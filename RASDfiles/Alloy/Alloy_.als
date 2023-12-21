/*SIGNATURES*/

abstract sig Boolean{}
one sig TRUE extends Boolean{}
one sig FALSE extends Boolean{}

sig Username{}
sig Password{}
sig EmailAddress{}

sig CodeKataBattle{
	tournament_available: some Tournament,
}

sig Student{
	username: one Username, 
	password: one Password,
 	email: one EmailAddress,
	personal_score: one Score,
	visualize_badge: set Badge,
}

sig Educator{
	username: one Username, 
	password: one Password,
 	email: one EmailAddress,
	assignScore: some Score,
	assignBadge: some Badge,
}

sig Tournament{
	tournamentId: one Int,
	battles_available: set Battles,
	participants: set Student,
	educator: some Educator,
	setted_by_more: one Boolean,
	registrationDeadline: one DateTime,
	startTime: one DateTime,
 	endTime: one DateTime,
	Openstatus: one Boolean,
	Closedstatus: one Boolean,
}{
	tournamentId > 0 and 
	startTime.timestamp < endTime.timestamp
   	startTime.timestamp >=0 and Openstatus != Closedstatus and 
	startTime.timestamp > registrationDeadline.timestamp and  startTime.timestamp < endTime.timestamp
}


sig Battles{
	battle_Id: one Int,
	teams_in_battle: some Team,
	battle_rule: one BattleRules,
	link_repo: one GitHubRepo,
	test_for_battle: one TestCase,
	Startstatus: one Boolean,
	EndStatus: one Boolean,
	deadlineRegistration: one DateTime,
  	startTimeBattle: one DateTime,
  	endTimeBattle: one DateTime
}{
	battle_Id > 0 and EndStatus != Startstatus 
	and startTimeBattle != endTimeBattle
	
}

sig Team{
	teamId: one Int,
	student_in_team: some Student,
	team_score: one Score,
	minParticipant: one Int,
	maxParticipant: one Int,
}{
	minParticipant < maxParticipant and
	minParticipant > 0 and teamId>0
}

sig Score{
	score: one Int
}{
 score >= 0 /*and score <= 100*/
}

sig TestCase{
  test: "test for the battle",
  testStatus: one Boolean,
}

sig Badge{
	variables: some Variables
}

sig Variables{
	constraint: "String Rules for the badge",
	setted_by: one Educator
}

sig BattleRules{
 	rule: "String rules for the battle",
 	setted_by: one Educator,
}

sig Notification {
    receiver: set Student,
    content:"news"
}

sig DateTime{
 	timestamp: one Int
}{
 	timestamp > 0
}

sig GitHubRepo{
 link: "String link"
}





/*FACTS OF THE PERSONAL DATA*/
fact noDuplicatedEmailStudent{
 all s1, s2: Student | s1 != s2 implies s1.email != s2.email
}

fact nosameEmailandUsername{
all s: Student, e: Educator|s.email !=e.email and s.username!= e.username
}

fact noDuplicatedUsernameStudent{
 all s1,  s2: Student | s1 != s2 implies s1.username != s2.username
}

fact noDuplicatedEmailEducator{
 all e1, e2: Educator | e1 != e2 implies e1.email != e2.email
}

fact noDuplicatedUsernameEducator{
 all e1,  e2: Educator | e1 != e2 implies e1.username != e2.username
}

//All the teams in the same battle mustn’t have the same students in it
fact NoCommonStudentsInSameBattle {
  all b: Battles, t1, t2: Team |
    t1 in b.teams_in_battle and t2 in b.teams_in_battle and t1 != t2 implies no s: Student 
    | s in t1.student_in_team and s in t2.student_in_team
}



//The number of the students in the platform must be greater or equal than the number of the tournament participants
fact RegisteredStudentsGreaterOrEqualParticipants {
    all t: Tournament | #t.participants <= # Student
}


/*CONSTRAINT OF THE BATTLE*/
/*name of the Battle must be unique*/
fact UniqueBattleName{
 all b1,b2:Battles | (b1!=b2)implies b1.battle_Id != b2.battle_Id
}

//The start time of the battle has to happen after the deadline of the registration in the tournament
fact TimestampBattle{
 all b: Battles |
	b.deadlineRegistration.timestamp < b.startTimeBattle.timestamp and
	b.startTimeBattle.timestamp >= 0 
}

//One battle has to be connected only to one tournamert
fact BattlesConnectedToTournament {
  all b: Battles | one t: Tournament | b in t.battles_available
}

fact TeamsConnectedToOneBattle{
  all t: Team | one b: Battles | t in b.teams_in_battle
}




/*CONSTRAINT OF THE TOURNAMENT*/
fact UniqueTournamentName{
 all t1,t2: Tournament | (t1!=t2) implies t1.tournamentId != t2.tournamentId
}

fact TournamentsConnectedToCodeKataBattle {
  all t: Tournament, cb: CodeKataBattle | t in  cb.tournament_available
}

fact UniqueTeamId{
	all t1,t2: Team | t1!=t2 implies t1.teamId != t2.teamId
}

fact UniqueLinkGitHubRepo{
	all b1,b2: Battles | b1!=b2 implies b1.link_repo != b2.link_repo
}
 
fact endstatus{
all t:Tournament, b:Battles|(t.Closedstatus = TRUE ) implies b.EndStatus = TRUE  }

fact startstatus{
all t:Tournament, b:Battles| (t.Openstatus = TRUE ) implies b.Startstatus = TRUE}

fact TeamHasAtLeastOneStudent{
	all t:Team | #t.student_in_team > t.minParticipant and t.maxParticipant > #t.student_in_team
}
//The test cases for one battle are unique, based on the battle goal
fact testcaseinBattle{
	some  t1,t2: TestCase| all b: Battles|(t1 in b.test_for_battle and t2 in b.test_for_battle) implies t1!= t2
}

//The start time of the Tournament must happen before the start time of the Battle
fact FirstTournamentThenBattle{
  all t:Tournament, b:Battles | (b in t.battles_available and b.Startstatus=TRUE) 
  implies  t.startTime.timestamp<b.startTimeBattle.timestamp
}

//students can registrate in the tournament until the registration deadline
fact SubscriptionDeadline {
  all t: Tournament, s: Student , d: DateTime |
    s in t.participants implies d.timestamp <= t.registrationDeadline.timestamp
}

//The end time of the battle must happen before the end time of the tournament
fact FirstBattleThenTournament{
  all t:Tournament, b:Battles | (b in t.battles_available and b.EndStatus = TRUE) 
  implies  t.endTime.timestamp > b.endTimeBattle.timestamp
}

fact TestCaseRequiresBattle {
  all t: TestCase | some b: Battles | t in b.test_for_battle
}

/*CONSTRAINT FOR THE BADGE*/
//the same badge can be assigned to the same student only once
fact UniqueBadgeAssignment {
  all s: Student, b1, b2: Badge | (b1 in s.visualize_badge and b2 in s.visualize_badge) implies (b1 != b2) 
}

fact BadgeVisibleAfterTournament {
  all t: Tournament, s: Student, b: Badge |
    (s in t.participants and b in s.visualize_badge) implies t.Closedstatus = TRUE
}


/* badges are assigned only when the battle is over*/
fact BadgeAssignmentAfterBattleCompletion {
  all s: Student, b: Badge, battle: Battles | 
    (b in s.visualize_badge) implies
      battle.EndStatus = TRUE and battle.Startstatus=FALSE
}

fact oneBattleRulesForABattle{
	all br: BattleRules | one b: Battles | br in b.battle_rule
}

fact PersonalScoreVisibleAfterTournament {
  all t: Tournament, s: Student, sc: Score |
    (sc in s.personal_score) implies  t.Closedstatus = TRUE
}

fact BadgeVisibleAfterTournament {
  all t: Tournament, s: Student, b: Badge |
    (b in s.visualize_badge) implies t.Closedstatus = TRUE
}

//If one flag is TRUE, more educator can create new battles in the same tournament
fact moreEducatorforOneTournament{
 all e1,e2:Educator, t:Tournament |(e1!=e2 and t.setted_by_more = TRUE and e1 in t.educator) implies e2 in t.educator
}
//Since the tournament is created, the user receives a notification 
fact NotifyStudentsAfterBattleCreation {
  all t: Tournament, b: Battles, s: Student |
    b in t.battles_available and b.EndStatus=FALSE and s in t.participants implies
    some n: Notification |
      n.receiver = s 
}

//ASSERT

// Check if the badge are uniquely assigned to each student
assert UniqueBadgeAssignment {
  all s: Student, b1, b2: Badge | (b1 in s.visualize_badge and b2 in s.visualize_badge) implies (b1 != b2)
}

// Check if the github repo link is unique for each battle	
assert UniqueGitHubRepoLink {
  all b1, b2: Battles | (b1 != b2) implies b1.link_repo != b2.link_repo
}

// Check if the badge is visible only after the end of the torunament
assert BadgeVisibleAfterTournament {
  all t: Tournament, s: Student, b: Badge |
    (s in t.participants and b in s.visualize_badge) implies t.Closedstatus = TRUE
}

// Check if the personal score il visible after the Tournament is closed
assert PersonalScoreVisibleAfterTournament {
  all t: Tournament, s: Student, sc: Score |
    (sc in s.personal_score) implies t.Closedstatus = TRUE
}

fun CalculateScore[s : Student]: one Int{
 let 
	teams = {t : Team | s in t.student_in_team},
	team_score = teams.team_score,
	personalScore = team_score.score|
	sum personalScore
}



check UniqueBadgeAssignment for 5
check UniqueGitHubRepoLink for 5
check BadgeVisibleAfterTournament for 5
check PersonalScoreVisibleAfterTournament for 5

pred show{
	#CodeKataBattle = 1
	#Tournament > 0
	#Student>0
	#Educator > 0

}
run show
