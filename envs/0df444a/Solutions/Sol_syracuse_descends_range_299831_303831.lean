-- Prove2me | solution 1 for syracuse_descends_range_299831_303831
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:44:20.005256+00:00
-- url     : https://prove2.me/submissions/e692f027-e60e-49b0-8358-f7fe56032841

import Mathlib
import Definitions.Def_syracuseStep

set_option maxHeartbeats 1000000

open Nat

/-- Half of all odd numbers descend in a single Syracuse step, uniformly. -/
theorem step_lt_of_one_mod_four (m : ℕ) (h1 : 1 < m) (h4 : m % 4 = 1) : syracuseStep m < m := by
  have hne : 3 * m + 1 ≠ 0 := by omega
  have hdvd : (2:ℕ) ^ 2 ∣ 3 * m + 1 := by
    have : (4:ℕ) ∣ 3 * m + 1 := by omega
    simpa using this
  have hle : 2 ≤ (3 * m + 1).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp hdvd
  have hpow : (2:ℕ) ^ 2 ≤ 2 ^ ((3 * m + 1).factorization 2) :=
    Nat.pow_le_pow_right (by norm_num) hle
  have h1' : syracuseStep m ≤ (3 * m + 1) / 2 ^ 2 := by
    show ordCompl[2] (3 * m + 1) ≤ _
    exact Nat.div_le_div_left hpow (by positivity)
  have h2' : (3 * m + 1) / 2 ^ 2 < m := by
    apply Nat.div_lt_of_lt_mul
    omega
  omega

/-- `Blo L x` : some Syracuse iterate of `x` drops below `L`. -/
abbrev Blo (L x : ℕ) : Prop := ∃ t : ℕ, syracuseStep^[t] x < L

theorem bbase {L x y : ℕ} (h : syracuseStep x = y) (hy : y < L) : Blo L x :=
  ⟨1, by rw [Function.iterate_one, h]; exact hy⟩

theorem bstep {L x y : ℕ} (h : syracuseStep x = y) (hy : Blo L y) : Blo L x := by
  obtain ⟨t, ht⟩ := hy
  exact ⟨t + 1, by rw [Function.iterate_add_apply, Function.iterate_one, h]; exact ht⟩

theorem se (a : ℕ) {y z : ℕ} (h : 3 * y + 1 = 2 ^ a * z) (hz : Odd z) :
    syracuseStep y = z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp [Nat.odd_iff] at hz
  have hfac : (3 * y + 1).factorization 2 = a := by
    rw [h, Nat.factorization_mul (by positivity) hz0]
    simp [Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by rwa [Nat.two_dvd_ne_zero, ← Nat.odd_iff])]
  show ordCompl[2] (3 * y + 1) = z
  rw [hfac, h, Nat.mul_div_cancel_left _ (by positivity)]


theorem B983125 : Blo 299831 983125 := bbase (se 8 (by rfl) ⟨5760, by rfl⟩ : syracuseStep 983125 = 11521) (by norm_num)
theorem B622733 : Blo 299831 622733 := bbase (se 3 (by rfl) ⟨116762, by rfl⟩ : syracuseStep 622733 = 233525) (by norm_num)
theorem B524485 : Blo 299831 524485 := bbase (se 4 (by rfl) ⟨49170, by rfl⟩ : syracuseStep 524485 = 98341) (by norm_num)
theorem B1016117 : Blo 299831 1016117 := bbase (se 5 (by rfl) ⟨47630, by rfl⟩ : syracuseStep 1016117 = 95261) (by norm_num)
theorem B688445 : Blo 299831 688445 := bbase (se 3 (by rfl) ⟨129083, by rfl⟩ : syracuseStep 688445 = 258167) (by norm_num)
theorem B1081669 : Blo 299831 1081669 := bbase (se 4 (by rfl) ⟨101406, by rfl⟩ : syracuseStep 1081669 = 202813) (by norm_num)
theorem B21955157 : Blo 299831 21955157 := bbase (se 8 (by rfl) ⟨128643, by rfl⟩ : syracuseStep 21955157 = 257287) (by norm_num)
theorem B1016549 : Blo 299831 1016549 := bbase (se 4 (by rfl) ⟨95301, by rfl⟩ : syracuseStep 1016549 = 190603) (by norm_num)
theorem B1442549 : Blo 299831 1442549 := bbase (se 5 (by rfl) ⟨67619, by rfl⟩ : syracuseStep 1442549 = 135239) (by norm_num)
theorem B459541 : Blo 299831 459541 := bbase (se 6 (by rfl) ⟨10770, by rfl⟩ : syracuseStep 459541 = 21541) (by norm_num)
theorem B2327413 : Blo 299831 2327413 := bbase (se 5 (by rfl) ⟨109097, by rfl⟩ : syracuseStep 2327413 = 218195) (by norm_num)
theorem B721813 : Blo 299831 721813 := bbase (se 6 (by rfl) ⟨16917, by rfl⟩ : syracuseStep 721813 = 33835) (by norm_num)
theorem B426989 : Blo 299831 426989 := bbase (se 3 (by rfl) ⟨80060, by rfl⟩ : syracuseStep 426989 = 160121) (by norm_num)
theorem B427069 : Blo 299831 427069 := bbase (se 3 (by rfl) ⟨80075, by rfl⟩ : syracuseStep 427069 = 160151) (by norm_num)
theorem B1016981 : Blo 299831 1016981 := bbase (se 6 (by rfl) ⟨23835, by rfl⟩ : syracuseStep 1016981 = 47671) (by norm_num)
theorem B1148053 : Blo 299831 1148053 := bbase (se 6 (by rfl) ⟨26907, by rfl⟩ : syracuseStep 1148053 = 53815) (by norm_num)
theorem B427189 : Blo 299831 427189 := bbase (se 5 (by rfl) ⟨20024, by rfl⟩ : syracuseStep 427189 = 40049) (by norm_num)
theorem B722189 : Blo 299831 722189 := bbase (se 3 (by rfl) ⟨135410, by rfl⟩ : syracuseStep 722189 = 270821) (by norm_num)
theorem B427285 : Blo 299831 427285 := bbase (se 6 (by rfl) ⟨10014, by rfl⟩ : syracuseStep 427285 = 20029) (by norm_num)
theorem B361829 : Blo 299831 361829 := bbase (se 4 (by rfl) ⟨33921, by rfl⟩ : syracuseStep 361829 = 67843) (by norm_num)
theorem B1148357 : Blo 299831 1148357 := bbase (se 4 (by rfl) ⟨107658, by rfl⟩ : syracuseStep 1148357 = 215317) (by norm_num)
theorem B361945 : Blo 299831 361945 := bbase (se 2 (by rfl) ⟨135729, by rfl⟩ : syracuseStep 361945 = 271459) (by norm_num)
theorem B362017 : Blo 299831 362017 := bbase (se 2 (by rfl) ⟨135756, by rfl⟩ : syracuseStep 362017 = 271513) (by norm_num)
theorem B460325 : Blo 299831 460325 := bbase (se 4 (by rfl) ⟨43155, by rfl⟩ : syracuseStep 460325 = 86311) (by norm_num)
theorem B1017413 : Blo 299831 1017413 := bbase (se 4 (by rfl) ⟨95382, by rfl⟩ : syracuseStep 1017413 = 190765) (by norm_num)
theorem B362137 : Blo 299831 362137 := bbase (se 2 (by rfl) ⟨135801, by rfl⟩ : syracuseStep 362137 = 271603) (by norm_num)
theorem B722621 : Blo 299831 722621 := bbase (se 3 (by rfl) ⟨135491, by rfl⟩ : syracuseStep 722621 = 270983) (by norm_num)
theorem B427781 : Blo 299831 427781 := bbase (se 4 (by rfl) ⟨40104, by rfl⟩ : syracuseStep 427781 = 80209) (by norm_num)
theorem B657293 : Blo 299831 657293 := bbase (se 3 (by rfl) ⟨123242, by rfl⟩ : syracuseStep 657293 = 246485) (by norm_num)
theorem B1640341 : Blo 299831 1640341 := bbase (se 6 (by rfl) ⟨38445, by rfl⟩ : syracuseStep 1640341 = 76891) (by norm_num)
theorem B1017845 : Blo 299831 1017845 := bbase (se 5 (by rfl) ⟨47711, by rfl⟩ : syracuseStep 1017845 = 95423) (by norm_num)
theorem B362521 : Blo 299831 362521 := bbase (se 2 (by rfl) ⟨135945, by rfl⟩ : syracuseStep 362521 = 271891) (by norm_num)
theorem B7702613 : Blo 299831 7702613 := bbase (se 8 (by rfl) ⟨45132, by rfl⟩ : syracuseStep 7702613 = 90265) (by norm_num)
theorem B1378421 : Blo 299831 1378421 := bbase (se 5 (by rfl) ⟨64613, by rfl⟩ : syracuseStep 1378421 = 129227) (by norm_num)
theorem B460933 : Blo 299831 460933 := bbase (se 4 (by rfl) ⟨43212, by rfl⟩ : syracuseStep 460933 = 86425) (by norm_num)
theorem B1083557 : Blo 299831 1083557 := bbase (se 4 (by rfl) ⟨101583, by rfl⟩ : syracuseStep 1083557 = 203167) (by norm_num)
theorem B723197 : Blo 299831 723197 := bbase (se 3 (by rfl) ⟨135599, by rfl⟩ : syracuseStep 723197 = 271199) (by norm_num)
theorem B428333 : Blo 299831 428333 := bbase (se 3 (by rfl) ⟨80312, by rfl⟩ : syracuseStep 428333 = 160625) (by norm_num)
theorem B657709 : Blo 299831 657709 := bbase (se 3 (by rfl) ⟨123320, by rfl⟩ : syracuseStep 657709 = 246641) (by norm_num)
theorem B1935701 : Blo 299831 1935701 := bbase (se 10 (by rfl) ⟨2835, by rfl⟩ : syracuseStep 1935701 = 5671) (by norm_num)
theorem B3082645 : Blo 299831 3082645 := bbase (se 6 (by rfl) ⟨72249, by rfl⟩ : syracuseStep 3082645 = 144499) (by norm_num)
theorem B1018277 : Blo 299831 1018277 := bbase (se 4 (by rfl) ⟨95463, by rfl⟩ : syracuseStep 1018277 = 190927) (by norm_num)
theorem B2886293 : Blo 299831 2886293 := bbase (se 6 (by rfl) ⟨67647, by rfl⟩ : syracuseStep 2886293 = 135295) (by norm_num)
theorem B920261 : Blo 299831 920261 := bbase (se 4 (by rfl) ⟨86274, by rfl⟩ : syracuseStep 920261 = 172549) (by norm_num)
theorem B363209 : Blo 299831 363209 := bbase (se 2 (by rfl) ⟨136203, by rfl⟩ : syracuseStep 363209 = 272407) (by norm_num)
theorem B1018709 : Blo 299831 1018709 := bbase (se 9 (by rfl) ⟨2984, by rfl⟩ : syracuseStep 1018709 = 5969) (by norm_num)
theorem B854981 : Blo 299831 854981 := bbase (se 4 (by rfl) ⟨80154, by rfl⟩ : syracuseStep 854981 = 160309) (by norm_num)
theorem B429085 : Blo 299831 429085 := bbase (se 3 (by rfl) ⟨80453, by rfl⟩ : syracuseStep 429085 = 160907) (by norm_num)
theorem B2919509 : Blo 299831 2919509 := bbase (se 8 (by rfl) ⟨17106, by rfl⟩ : syracuseStep 2919509 = 34213) (by norm_num)
theorem B1084565 : Blo 299831 1084565 := bbase (se 6 (by rfl) ⟨25419, by rfl⟩ : syracuseStep 1084565 = 50839) (by norm_num)
theorem B1019141 : Blo 299831 1019141 := bbase (se 4 (by rfl) ⟨95544, by rfl⟩ : syracuseStep 1019141 = 191089) (by norm_num)
theorem B363809 : Blo 299831 363809 := bbase (se 2 (by rfl) ⟨136428, by rfl⟩ : syracuseStep 363809 = 272857) (by norm_num)
theorem B920933 : Blo 299831 920933 := bbase (se 4 (by rfl) ⟨86337, by rfl⟩ : syracuseStep 920933 = 172675) (by norm_num)
theorem B1150469 : Blo 299831 1150469 := bbase (se 4 (by rfl) ⟨107856, by rfl⟩ : syracuseStep 1150469 = 215713) (by norm_num)
theorem B364117 : Blo 299831 364117 := bbase (se 8 (by rfl) ⟨2133, by rfl⟩ : syracuseStep 364117 = 4267) (by norm_num)
theorem B1019573 : Blo 299831 1019573 := bbase (se 5 (by rfl) ⟨47792, by rfl⟩ : syracuseStep 1019573 = 95585) (by norm_num)
theorem B364213 : Blo 299831 364213 := bbase (se 5 (by rfl) ⟨17072, by rfl⟩ : syracuseStep 364213 = 34145) (by norm_num)
theorem B364261 : Blo 299831 364261 := bbase (se 4 (by rfl) ⟨34149, by rfl⟩ : syracuseStep 364261 = 68299) (by norm_num)
theorem B1150757 : Blo 299831 1150757 := bbase (se 4 (by rfl) ⟨107883, by rfl⟩ : syracuseStep 1150757 = 215767) (by norm_num)
theorem B429877 : Blo 299831 429877 := bbase (se 5 (by rfl) ⟨20150, by rfl⟩ : syracuseStep 429877 = 40301) (by norm_num)
theorem B397153 : Blo 299831 397153 := bbase (se 2 (by rfl) ⟨148932, by rfl⟩ : syracuseStep 397153 = 297865) (by norm_num)
theorem B2166709 : Blo 299831 2166709 := bbase (se 5 (by rfl) ⟨101564, by rfl⟩ : syracuseStep 2166709 = 203129) (by norm_num)
theorem B856165 : Blo 299831 856165 := bbase (se 4 (by rfl) ⟨80265, by rfl⟩ : syracuseStep 856165 = 160531) (by norm_num)
theorem B1020005 : Blo 299831 1020005 := bbase (se 4 (by rfl) ⟨95625, by rfl⟩ : syracuseStep 1020005 = 191251) (by norm_num)
theorem B430213 : Blo 299831 430213 := bbase (se 4 (by rfl) ⟨40332, by rfl⟩ : syracuseStep 430213 = 80665) (by norm_num)
theorem B856325 : Blo 299831 856325 := bbase (se 4 (by rfl) ⟨80280, by rfl⟩ : syracuseStep 856325 = 160561) (by norm_num)
theorem B430429 : Blo 299831 430429 := bbase (se 3 (by rfl) ⟨80705, by rfl⟩ : syracuseStep 430429 = 161411) (by norm_num)
theorem B2298293 : Blo 299831 2298293 := bbase (se 5 (by rfl) ⟨107732, by rfl⟩ : syracuseStep 2298293 = 215465) (by norm_num)
theorem B856565 : Blo 299831 856565 := bbase (se 5 (by rfl) ⟨40151, by rfl⟩ : syracuseStep 856565 = 80303) (by norm_num)
theorem B692749 : Blo 299831 692749 := bbase (se 3 (by rfl) ⟨129890, by rfl⟩ : syracuseStep 692749 = 259781) (by norm_num)
theorem B1020437 : Blo 299831 1020437 := bbase (se 6 (by rfl) ⟨23916, by rfl⟩ : syracuseStep 1020437 = 47833) (by norm_num)
theorem B1282661 : Blo 299831 1282661 := bbase (se 4 (by rfl) ⟨120249, by rfl⟩ : syracuseStep 1282661 = 240499) (by norm_num)
theorem B856757 : Blo 299831 856757 := bbase (se 5 (by rfl) ⟨40160, by rfl⟩ : syracuseStep 856757 = 80321) (by norm_num)
theorem B430805 : Blo 299831 430805 := bbase (se 7 (by rfl) ⟨5048, by rfl⟩ : syracuseStep 430805 = 10097) (by norm_num)
theorem B725773 : Blo 299831 725773 := bbase (se 3 (by rfl) ⟨136082, by rfl⟩ : syracuseStep 725773 = 272165) (by norm_num)
theorem B1282949 : Blo 299831 1282949 := bbase (se 4 (by rfl) ⟨120276, by rfl⟩ : syracuseStep 1282949 = 240553) (by norm_num)
theorem B1020869 : Blo 299831 1020869 := bbase (se 4 (by rfl) ⟨95706, by rfl⟩ : syracuseStep 1020869 = 191413) (by norm_num)
theorem B1151941 : Blo 299831 1151941 := bbase (se 4 (by rfl) ⟨107994, by rfl⟩ : syracuseStep 1151941 = 215989) (by norm_num)
theorem B1152245 : Blo 299831 1152245 := bbase (se 5 (by rfl) ⟨54011, by rfl⟩ : syracuseStep 1152245 = 108023) (by norm_num)
theorem B1021301 : Blo 299831 1021301 := bbase (se 5 (by rfl) ⟨47873, by rfl⟩ : syracuseStep 1021301 = 95747) (by norm_num)
theorem B759253 : Blo 299831 759253 := bbase (se 7 (by rfl) ⟨8897, by rfl⟩ : syracuseStep 759253 = 17795) (by norm_num)
theorem B759365 : Blo 299831 759365 := bbase (se 4 (by rfl) ⟨71190, by rfl⟩ : syracuseStep 759365 = 142381) (by norm_num)
theorem B1283701 : Blo 299831 1283701 := bbase (se 5 (by rfl) ⟨60173, by rfl⟩ : syracuseStep 1283701 = 120347) (by norm_num)
theorem B857749 : Blo 299831 857749 := bbase (se 6 (by rfl) ⟨20103, by rfl⟩ : syracuseStep 857749 = 40207) (by norm_num)
theorem B5183189 : Blo 299831 5183189 := bbase (se 7 (by rfl) ⟨60740, by rfl⟩ : syracuseStep 5183189 = 121481) (by norm_num)
theorem B759557 : Blo 299831 759557 := bbase (se 4 (by rfl) ⟨71208, by rfl⟩ : syracuseStep 759557 = 142417) (by norm_num)
theorem B1021733 : Blo 299831 1021733 := bbase (se 4 (by rfl) ⟨95787, by rfl⟩ : syracuseStep 1021733 = 191575) (by norm_num)
theorem B726965 : Blo 299831 726965 := bbase (se 5 (by rfl) ⟨34076, by rfl⟩ : syracuseStep 726965 = 68153) (by norm_num)
theorem B759901 : Blo 299831 759901 := bbase (se 3 (by rfl) ⟨142481, by rfl⟩ : syracuseStep 759901 = 284963) (by norm_num)
theorem B432229 : Blo 299831 432229 := bbase (se 4 (by rfl) ⟨40521, by rfl⟩ : syracuseStep 432229 = 81043) (by norm_num)
theorem B727157 : Blo 299831 727157 := bbase (se 5 (by rfl) ⟨34085, by rfl⟩ : syracuseStep 727157 = 68171) (by norm_num)
theorem B760013 : Blo 299831 760013 := bbase (se 3 (by rfl) ⟨142502, by rfl⟩ : syracuseStep 760013 = 285005) (by norm_num)
theorem B1022165 : Blo 299831 1022165 := bbase (se 7 (by rfl) ⟨11978, by rfl⟩ : syracuseStep 1022165 = 23957) (by norm_num)
theorem B1284437 : Blo 299831 1284437 := bbase (se 10 (by rfl) ⟨1881, by rfl⟩ : syracuseStep 1284437 = 3763) (by norm_num)
theorem B760205 : Blo 299831 760205 := bbase (se 3 (by rfl) ⟨142538, by rfl⟩ : syracuseStep 760205 = 285077) (by norm_num)
theorem B1022597 : Blo 299831 1022597 := bbase (se 4 (by rfl) ⟨95868, by rfl⟩ : syracuseStep 1022597 = 191737) (by norm_num)
theorem B760549 : Blo 299831 760549 := bbase (se 4 (by rfl) ⟨71301, by rfl⟩ : syracuseStep 760549 = 142603) (by norm_num)
theorem B858853 : Blo 299831 858853 := bbase (se 4 (by rfl) ⟨80517, by rfl⟩ : syracuseStep 858853 = 161035) (by norm_num)
theorem B760661 : Blo 299831 760661 := bbase (se 9 (by rfl) ⟨2228, by rfl⟩ : syracuseStep 760661 = 4457) (by norm_num)
theorem B2923381 : Blo 299831 2923381 := bbase (se 5 (by rfl) ⟨137033, by rfl⟩ : syracuseStep 2923381 = 274067) (by norm_num)
theorem B760853 : Blo 299831 760853 := bbase (se 6 (by rfl) ⟨17832, by rfl⟩ : syracuseStep 760853 = 35665) (by norm_num)
theorem B1023029 : Blo 299831 1023029 := bbase (se 5 (by rfl) ⟨47954, by rfl⟩ : syracuseStep 1023029 = 95909) (by norm_num)
theorem B761197 : Blo 299831 761197 := bbase (se 3 (by rfl) ⟨142724, by rfl⟩ : syracuseStep 761197 = 285449) (by norm_num)
theorem B761309 : Blo 299831 761309 := bbase (se 3 (by rfl) ⟨142745, by rfl⟩ : syracuseStep 761309 = 285491) (by norm_num)
theorem B1023461 : Blo 299831 1023461 := bbase (se 4 (by rfl) ⟨95949, by rfl⟩ : syracuseStep 1023461 = 191899) (by norm_num)
theorem B1121861 : Blo 299831 1121861 := bbase (se 4 (by rfl) ⟨105174, by rfl⟩ : syracuseStep 1121861 = 210349) (by norm_num)
theorem B761501 : Blo 299831 761501 := bbase (se 3 (by rfl) ⟨142781, by rfl⟩ : syracuseStep 761501 = 285563) (by norm_num)
theorem B1449701 : Blo 299831 1449701 := bbase (se 4 (by rfl) ⟨135909, by rfl⟩ : syracuseStep 1449701 = 271819) (by norm_num)
theorem B2072309 : Blo 299831 2072309 := bbase (se 5 (by rfl) ⟨97139, by rfl⟩ : syracuseStep 2072309 = 194279) (by norm_num)
theorem B1154837 : Blo 299831 1154837 := bbase (se 6 (by rfl) ⟨27066, by rfl⟩ : syracuseStep 1154837 = 54133) (by norm_num)
theorem B1023893 : Blo 299831 1023893 := bbase (se 6 (by rfl) ⟨23997, by rfl⟩ : syracuseStep 1023893 = 47995) (by norm_num)
theorem B335825 : Blo 299831 335825 := bbase (se 2 (by rfl) ⟨125934, by rfl⟩ : syracuseStep 335825 = 251869) (by norm_num)
theorem B761845 : Blo 299831 761845 := bbase (se 5 (by rfl) ⟨35711, by rfl⟩ : syracuseStep 761845 = 71423) (by norm_num)
theorem B761957 : Blo 299831 761957 := bbase (se 4 (by rfl) ⟨71433, by rfl⟩ : syracuseStep 761957 = 142867) (by norm_num)
theorem B860357 : Blo 299831 860357 := bbase (se 4 (by rfl) ⟨80658, by rfl⟩ : syracuseStep 860357 = 161317) (by norm_num)
theorem B762149 : Blo 299831 762149 := bbase (se 4 (by rfl) ⟨71451, by rfl⟩ : syracuseStep 762149 = 142903) (by norm_num)
theorem B1024325 : Blo 299831 1024325 := bbase (se 4 (by rfl) ⟨96030, by rfl⟩ : syracuseStep 1024325 = 192061) (by norm_num)
theorem B729445 : Blo 299831 729445 := bbase (se 4 (by rfl) ⟨68385, by rfl⟩ : syracuseStep 729445 = 136771) (by norm_num)
theorem B762493 : Blo 299831 762493 := bbase (se 3 (by rfl) ⟨142967, by rfl⟩ : syracuseStep 762493 = 285935) (by norm_num)
theorem B762605 : Blo 299831 762605 := bbase (se 3 (by rfl) ⟨142988, by rfl⟩ : syracuseStep 762605 = 285977) (by norm_num)
theorem B1024757 : Blo 299831 1024757 := bbase (se 5 (by rfl) ⟨48035, by rfl⟩ : syracuseStep 1024757 = 96071) (by norm_num)
theorem B369505 : Blo 299831 369505 := bbase (se 2 (by rfl) ⟨138564, by rfl⟩ : syracuseStep 369505 = 277129) (by norm_num)
theorem B762797 : Blo 299831 762797 := bbase (se 3 (by rfl) ⟨143024, by rfl⟩ : syracuseStep 762797 = 286049) (by norm_num)
theorem B1025189 : Blo 299831 1025189 := bbase (se 4 (by rfl) ⟨96111, by rfl⟩ : syracuseStep 1025189 = 192223) (by norm_num)
theorem B763141 : Blo 299831 763141 := bbase (se 4 (by rfl) ⟨71544, by rfl⟩ : syracuseStep 763141 = 143089) (by norm_num)
theorem B763253 : Blo 299831 763253 := bbase (se 5 (by rfl) ⟨35777, by rfl⟩ : syracuseStep 763253 = 71555) (by norm_num)
theorem B337333 : Blo 299831 337333 := bbase (se 5 (by rfl) ⟨15812, by rfl⟩ : syracuseStep 337333 = 31625) (by norm_num)
theorem B304597 : Blo 299831 304597 := bbase (se 7 (by rfl) ⟨3569, by rfl⟩ : syracuseStep 304597 = 7139) (by norm_num)
theorem B337369 : Blo 299831 337369 := bbase (se 2 (by rfl) ⟨126513, by rfl⟩ : syracuseStep 337369 = 253027) (by norm_num)
theorem B337405 : Blo 299831 337405 := bbase (se 3 (by rfl) ⟨63263, by rfl⟩ : syracuseStep 337405 = 126527) (by norm_num)
theorem B337441 : Blo 299831 337441 := bbase (se 2 (by rfl) ⟨126540, by rfl⟩ : syracuseStep 337441 = 253081) (by norm_num)
theorem B1287733 : Blo 299831 1287733 := bbase (se 5 (by rfl) ⟨60362, by rfl⟩ : syracuseStep 1287733 = 120725) (by norm_num)
theorem B763445 : Blo 299831 763445 := bbase (se 5 (by rfl) ⟨35786, by rfl⟩ : syracuseStep 763445 = 71573) (by norm_num)
theorem B2336309 : Blo 299831 2336309 := bbase (se 5 (by rfl) ⟨109514, by rfl⟩ : syracuseStep 2336309 = 219029) (by norm_num)
theorem B337477 : Blo 299831 337477 := bbase (se 4 (by rfl) ⟨31638, by rfl⟩ : syracuseStep 337477 = 63277) (by norm_num)
theorem B337513 : Blo 299831 337513 := bbase (se 2 (by rfl) ⟨126567, by rfl⟩ : syracuseStep 337513 = 253135) (by norm_num)
theorem B337549 : Blo 299831 337549 := bbase (se 3 (by rfl) ⟨63290, by rfl⟩ : syracuseStep 337549 = 126581) (by norm_num)
theorem B337585 : Blo 299831 337585 := bbase (se 2 (by rfl) ⟨126594, by rfl⟩ : syracuseStep 337585 = 253189) (by norm_num)
theorem B337621 : Blo 299831 337621 := bbase (se 7 (by rfl) ⟨3956, by rfl⟩ : syracuseStep 337621 = 7913) (by norm_num)
theorem B861941 : Blo 299831 861941 := bbase (se 5 (by rfl) ⟨40403, by rfl⟩ : syracuseStep 861941 = 80807) (by norm_num)
theorem B337657 : Blo 299831 337657 := bbase (se 2 (by rfl) ⟨126621, by rfl⟩ : syracuseStep 337657 = 253243) (by norm_num)
theorem B337693 : Blo 299831 337693 := bbase (se 3 (by rfl) ⟨63317, by rfl⟩ : syracuseStep 337693 = 126635) (by norm_num)
theorem B337729 : Blo 299831 337729 := bbase (se 2 (by rfl) ⟨126648, by rfl⟩ : syracuseStep 337729 = 253297) (by norm_num)
theorem B337765 : Blo 299831 337765 := bbase (se 4 (by rfl) ⟨31665, by rfl⟩ : syracuseStep 337765 = 63331) (by norm_num)
theorem B337801 : Blo 299831 337801 := bbase (se 2 (by rfl) ⟨126675, by rfl⟩ : syracuseStep 337801 = 253351) (by norm_num)
theorem B763789 : Blo 299831 763789 := bbase (se 3 (by rfl) ⟨143210, by rfl⟩ : syracuseStep 763789 = 286421) (by norm_num)
theorem B337837 : Blo 299831 337837 := bbase (se 3 (by rfl) ⟨63344, by rfl⟩ : syracuseStep 337837 = 126689) (by norm_num)
theorem B337873 : Blo 299831 337873 := bbase (se 2 (by rfl) ⟨126702, by rfl⟩ : syracuseStep 337873 = 253405) (by norm_num)
theorem B337909 : Blo 299831 337909 := bbase (se 5 (by rfl) ⟨15839, by rfl⟩ : syracuseStep 337909 = 31679) (by norm_num)
theorem B763901 : Blo 299831 763901 := bbase (se 3 (by rfl) ⟨143231, by rfl⟩ : syracuseStep 763901 = 286463) (by norm_num)
theorem B337945 : Blo 299831 337945 := bbase (se 2 (by rfl) ⟨126729, by rfl⟩ : syracuseStep 337945 = 253459) (by norm_num)
theorem B337981 : Blo 299831 337981 := bbase (se 3 (by rfl) ⟨63371, by rfl⟩ : syracuseStep 337981 = 126743) (by norm_num)
theorem B305213 : Blo 299831 305213 := bbase (se 3 (by rfl) ⟨57227, by rfl⟩ : syracuseStep 305213 = 114455) (by norm_num)
theorem B338017 : Blo 299831 338017 := bbase (se 2 (by rfl) ⟨126756, by rfl⟩ : syracuseStep 338017 = 253513) (by norm_num)
theorem B338053 : Blo 299831 338053 := bbase (se 4 (by rfl) ⟨31692, by rfl⟩ : syracuseStep 338053 = 63385) (by norm_num)
theorem B1091717 : Blo 299831 1091717 := bbase (se 4 (by rfl) ⟨102348, by rfl⟩ : syracuseStep 1091717 = 204697) (by norm_num)
theorem B338089 : Blo 299831 338089 := bbase (se 2 (by rfl) ⟨126783, by rfl⟩ : syracuseStep 338089 = 253567) (by norm_num)
theorem B764093 : Blo 299831 764093 := bbase (se 3 (by rfl) ⟨143267, by rfl⟩ : syracuseStep 764093 = 286535) (by norm_num)
theorem B338125 : Blo 299831 338125 := bbase (se 3 (by rfl) ⟨63398, by rfl⟩ : syracuseStep 338125 = 126797) (by norm_num)
theorem B338161 : Blo 299831 338161 := bbase (se 2 (by rfl) ⟨126810, by rfl⟩ : syracuseStep 338161 = 253621) (by norm_num)
theorem B338197 : Blo 299831 338197 := bbase (se 6 (by rfl) ⟨7926, by rfl⟩ : syracuseStep 338197 = 15853) (by norm_num)
theorem B698653 : Blo 299831 698653 := bbase (se 3 (by rfl) ⟨130997, by rfl⟩ : syracuseStep 698653 = 261995) (by norm_num)
theorem B338233 : Blo 299831 338233 := bbase (se 2 (by rfl) ⟨126837, by rfl⟩ : syracuseStep 338233 = 253675) (by norm_num)
theorem B1714517 : Blo 299831 1714517 := bbase (se 10 (by rfl) ⟨2511, by rfl⟩ : syracuseStep 1714517 = 5023) (by norm_num)
theorem B338269 : Blo 299831 338269 := bbase (se 3 (by rfl) ⟨63425, by rfl⟩ : syracuseStep 338269 = 126851) (by norm_num)
theorem B338305 : Blo 299831 338305 := bbase (se 2 (by rfl) ⟨126864, by rfl⟩ : syracuseStep 338305 = 253729) (by norm_num)
theorem B862613 : Blo 299831 862613 := bbase (se 6 (by rfl) ⟨20217, by rfl⟩ : syracuseStep 862613 = 40435) (by norm_num)
theorem B338341 : Blo 299831 338341 := bbase (se 4 (by rfl) ⟨31719, by rfl⟩ : syracuseStep 338341 = 63439) (by norm_num)
theorem B338377 : Blo 299831 338377 := bbase (se 2 (by rfl) ⟨126891, by rfl⟩ : syracuseStep 338377 = 253783) (by norm_num)
theorem B731605 : Blo 299831 731605 := bbase (se 7 (by rfl) ⟨8573, by rfl⟩ : syracuseStep 731605 = 17147) (by norm_num)
theorem B338413 : Blo 299831 338413 := bbase (se 3 (by rfl) ⟨63452, by rfl⟩ : syracuseStep 338413 = 126905) (by norm_num)
theorem B338449 : Blo 299831 338449 := bbase (se 2 (by rfl) ⟨126918, by rfl⟩ : syracuseStep 338449 = 253837) (by norm_num)
theorem B1518101 : Blo 299831 1518101 := bbase (se 6 (by rfl) ⟨35580, by rfl⟩ : syracuseStep 1518101 = 71161) (by norm_num)
theorem B764437 : Blo 299831 764437 := bbase (se 6 (by rfl) ⟨17916, by rfl⟩ : syracuseStep 764437 = 35833) (by norm_num)
theorem B338485 : Blo 299831 338485 := bbase (se 5 (by rfl) ⟨15866, by rfl⟩ : syracuseStep 338485 = 31733) (by norm_num)
theorem B338521 : Blo 299831 338521 := bbase (se 2 (by rfl) ⟨126945, by rfl⟩ : syracuseStep 338521 = 253891) (by norm_num)
theorem B338557 : Blo 299831 338557 := bbase (se 3 (by rfl) ⟨63479, by rfl⟩ : syracuseStep 338557 = 126959) (by norm_num)
theorem B764549 : Blo 299831 764549 := bbase (se 4 (by rfl) ⟨71676, by rfl⟩ : syracuseStep 764549 = 143353) (by norm_num)
theorem B338593 : Blo 299831 338593 := bbase (se 2 (by rfl) ⟨126972, by rfl⟩ : syracuseStep 338593 = 253945) (by norm_num)
theorem B338629 : Blo 299831 338629 := bbase (se 4 (by rfl) ⟨31746, by rfl⟩ : syracuseStep 338629 = 63493) (by norm_num)
theorem B1223365 : Blo 299831 1223365 := bbase (se 4 (by rfl) ⟨114690, by rfl⟩ : syracuseStep 1223365 = 229381) (by norm_num)
theorem B338665 : Blo 299831 338665 := bbase (se 2 (by rfl) ⟨126999, by rfl⟩ : syracuseStep 338665 = 253999) (by norm_num)
theorem B338701 : Blo 299831 338701 := bbase (se 3 (by rfl) ⟨63506, by rfl⟩ : syracuseStep 338701 = 127013) (by norm_num)
theorem B338737 : Blo 299831 338737 := bbase (se 2 (by rfl) ⟨127026, by rfl⟩ : syracuseStep 338737 = 254053) (by norm_num)
theorem B764741 : Blo 299831 764741 := bbase (se 4 (by rfl) ⟨71694, by rfl⟩ : syracuseStep 764741 = 143389) (by norm_num)
theorem B863045 : Blo 299831 863045 := bbase (se 4 (by rfl) ⟨80910, by rfl⟩ : syracuseStep 863045 = 161821) (by norm_num)
theorem B338773 : Blo 299831 338773 := bbase (se 9 (by rfl) ⟨992, by rfl⟩ : syracuseStep 338773 = 1985) (by norm_num)
theorem B338809 : Blo 299831 338809 := bbase (se 2 (by rfl) ⟨127053, by rfl⟩ : syracuseStep 338809 = 254107) (by norm_num)
theorem B338845 : Blo 299831 338845 := bbase (se 3 (by rfl) ⟨63533, by rfl⟩ : syracuseStep 338845 = 127067) (by norm_num)
theorem B338881 : Blo 299831 338881 := bbase (se 2 (by rfl) ⟨127080, by rfl⟩ : syracuseStep 338881 = 254161) (by norm_num)
theorem B1158085 : Blo 299831 1158085 := bbase (se 4 (by rfl) ⟨108570, by rfl⟩ : syracuseStep 1158085 = 217141) (by norm_num)
theorem B306137 : Blo 299831 306137 := bbase (se 2 (by rfl) ⟨114801, by rfl⟩ : syracuseStep 306137 = 229603) (by norm_num)
theorem B338917 : Blo 299831 338917 := bbase (se 4 (by rfl) ⟨31773, by rfl⟩ : syracuseStep 338917 = 63547) (by norm_num)
theorem B338953 : Blo 299831 338953 := bbase (se 2 (by rfl) ⟨127107, by rfl⟩ : syracuseStep 338953 = 254215) (by norm_num)
theorem B338989 : Blo 299831 338989 := bbase (se 3 (by rfl) ⟨63560, by rfl⟩ : syracuseStep 338989 = 127121) (by norm_num)
theorem B339025 : Blo 299831 339025 := bbase (se 2 (by rfl) ⟨127134, by rfl⟩ : syracuseStep 339025 = 254269) (by norm_num)
theorem B339061 : Blo 299831 339061 := bbase (se 5 (by rfl) ⟨15893, by rfl⟩ : syracuseStep 339061 = 31787) (by norm_num)
theorem B339097 : Blo 299831 339097 := bbase (se 2 (by rfl) ⟨127161, by rfl⟩ : syracuseStep 339097 = 254323) (by norm_num)
theorem B765085 : Blo 299831 765085 := bbase (se 3 (by rfl) ⟨143453, by rfl⟩ : syracuseStep 765085 = 286907) (by norm_num)
theorem B339133 : Blo 299831 339133 := bbase (se 3 (by rfl) ⟨63587, by rfl⟩ : syracuseStep 339133 = 127175) (by norm_num)
theorem B339169 : Blo 299831 339169 := bbase (se 2 (by rfl) ⟨127188, by rfl⟩ : syracuseStep 339169 = 254377) (by norm_num)
theorem B928997 : Blo 299831 928997 := bbase (se 4 (by rfl) ⟨87093, by rfl⟩ : syracuseStep 928997 = 174187) (by norm_num)
theorem B339205 : Blo 299831 339205 := bbase (se 4 (by rfl) ⟨31800, by rfl⟩ : syracuseStep 339205 = 63601) (by norm_num)
theorem B1092869 : Blo 299831 1092869 := bbase (se 4 (by rfl) ⟨102456, by rfl⟩ : syracuseStep 1092869 = 204913) (by norm_num)
theorem B765197 : Blo 299831 765197 := bbase (se 3 (by rfl) ⟨143474, by rfl⟩ : syracuseStep 765197 = 286949) (by norm_num)
theorem B339241 : Blo 299831 339241 := bbase (se 2 (by rfl) ⟨127215, by rfl⟩ : syracuseStep 339241 = 254431) (by norm_num)
theorem B339277 : Blo 299831 339277 := bbase (se 3 (by rfl) ⟨63614, by rfl⟩ : syracuseStep 339277 = 127229) (by norm_num)
theorem B5680469 : Blo 299831 5680469 := bbase (se 11 (by rfl) ⟨4160, by rfl⟩ : syracuseStep 5680469 = 8321) (by norm_num)
theorem B339313 : Blo 299831 339313 := bbase (se 2 (by rfl) ⟨127242, by rfl⟩ : syracuseStep 339313 = 254485) (by norm_num)
theorem B339349 : Blo 299831 339349 := bbase (se 6 (by rfl) ⟨7953, by rfl⟩ : syracuseStep 339349 = 15907) (by norm_num)
theorem B339385 : Blo 299831 339385 := bbase (se 2 (by rfl) ⟨127269, by rfl⟩ : syracuseStep 339385 = 254539) (by norm_num)
theorem B765389 : Blo 299831 765389 := bbase (se 3 (by rfl) ⟨143510, by rfl⟩ : syracuseStep 765389 = 287021) (by norm_num)
theorem B339421 : Blo 299831 339421 := bbase (se 3 (by rfl) ⟨63641, by rfl⟩ : syracuseStep 339421 = 127283) (by norm_num)
theorem B1715701 : Blo 299831 1715701 := bbase (se 5 (by rfl) ⟨80423, by rfl⟩ : syracuseStep 1715701 = 160847) (by norm_num)
theorem B339457 : Blo 299831 339457 := bbase (se 2 (by rfl) ⟨127296, by rfl⟩ : syracuseStep 339457 = 254593) (by norm_num)
theorem B339493 : Blo 299831 339493 := bbase (se 4 (by rfl) ⟨31827, by rfl⟩ : syracuseStep 339493 = 63655) (by norm_num)
theorem B470573 : Blo 299831 470573 := bbase (se 3 (by rfl) ⟨88232, by rfl⟩ : syracuseStep 470573 = 176465) (by norm_num)
theorem B1453621 : Blo 299831 1453621 := bbase (se 5 (by rfl) ⟨68138, by rfl⟩ : syracuseStep 1453621 = 136277) (by norm_num)
theorem B863797 : Blo 299831 863797 := bbase (se 5 (by rfl) ⟨40490, by rfl⟩ : syracuseStep 863797 = 80981) (by norm_num)
theorem B339529 : Blo 299831 339529 := bbase (se 2 (by rfl) ⟨127323, by rfl⟩ : syracuseStep 339529 = 254647) (by norm_num)
theorem B339565 : Blo 299831 339565 := bbase (se 3 (by rfl) ⟨63668, by rfl⟩ : syracuseStep 339565 = 127337) (by norm_num)
theorem B339601 : Blo 299831 339601 := bbase (se 2 (by rfl) ⟨127350, by rfl⟩ : syracuseStep 339601 = 254701) (by norm_num)
theorem B339637 : Blo 299831 339637 := bbase (se 5 (by rfl) ⟨15920, by rfl⟩ : syracuseStep 339637 = 31841) (by norm_num)
theorem B339673 : Blo 299831 339673 := bbase (se 2 (by rfl) ⟨127377, by rfl⟩ : syracuseStep 339673 = 254755) (by norm_num)
theorem B339709 : Blo 299831 339709 := bbase (se 3 (by rfl) ⟨63695, by rfl⟩ : syracuseStep 339709 = 127391) (by norm_num)
theorem B405253 : Blo 299831 405253 := bbase (se 4 (by rfl) ⟨37992, by rfl⟩ : syracuseStep 405253 = 75985) (by norm_num)
theorem B339745 : Blo 299831 339745 := bbase (se 2 (by rfl) ⟨127404, by rfl⟩ : syracuseStep 339745 = 254809) (by norm_num)
theorem B1519397 : Blo 299831 1519397 := bbase (se 4 (by rfl) ⟨142443, by rfl⟩ : syracuseStep 1519397 = 284887) (by norm_num)
theorem B765733 : Blo 299831 765733 := bbase (se 4 (by rfl) ⟨71787, by rfl⟩ : syracuseStep 765733 = 143575) (by norm_num)
theorem B438053 : Blo 299831 438053 := bbase (se 4 (by rfl) ⟨41067, by rfl⟩ : syracuseStep 438053 = 82135) (by norm_num)
theorem B339781 : Blo 299831 339781 := bbase (se 4 (by rfl) ⟨31854, by rfl⟩ : syracuseStep 339781 = 63709) (by norm_num)
theorem B339817 : Blo 299831 339817 := bbase (se 2 (by rfl) ⟨127431, by rfl⟩ : syracuseStep 339817 = 254863) (by norm_num)
theorem B1027957 : Blo 299831 1027957 := bbase (se 5 (by rfl) ⟨48185, by rfl⟩ : syracuseStep 1027957 = 96371) (by norm_num)
theorem B339853 : Blo 299831 339853 := bbase (se 3 (by rfl) ⟨63722, by rfl⟩ : syracuseStep 339853 = 127445) (by norm_num)
theorem B765845 : Blo 299831 765845 := bbase (se 6 (by rfl) ⟨17949, by rfl⟩ : syracuseStep 765845 = 35899) (by norm_num)
theorem B339889 : Blo 299831 339889 := bbase (se 2 (by rfl) ⟨127458, by rfl⟩ : syracuseStep 339889 = 254917) (by norm_num)
theorem B339925 : Blo 299831 339925 := bbase (se 7 (by rfl) ⟨3983, by rfl⟩ : syracuseStep 339925 = 7967) (by norm_num)
theorem B339961 : Blo 299831 339961 := bbase (se 2 (by rfl) ⟨127485, by rfl⟩ : syracuseStep 339961 = 254971) (by norm_num)
theorem B2306069 : Blo 299831 2306069 := bbase (se 6 (by rfl) ⟨54048, by rfl⟩ : syracuseStep 2306069 = 108097) (by norm_num)
theorem B339997 : Blo 299831 339997 := bbase (se 3 (by rfl) ⟨63749, by rfl⟩ : syracuseStep 339997 = 127499) (by norm_num)
theorem B340033 : Blo 299831 340033 := bbase (se 2 (by rfl) ⟨127512, by rfl⟩ : syracuseStep 340033 = 255025) (by norm_num)
theorem B766037 : Blo 299831 766037 := bbase (se 8 (by rfl) ⟨4488, by rfl⟩ : syracuseStep 766037 = 8977) (by norm_num)
theorem B340069 : Blo 299831 340069 := bbase (se 4 (by rfl) ⟨31881, by rfl⟩ : syracuseStep 340069 = 63763) (by norm_num)
theorem B340105 : Blo 299831 340105 := bbase (se 2 (by rfl) ⟨127539, by rfl⟩ : syracuseStep 340105 = 255079) (by norm_num)
theorem B569501 : Blo 299831 569501 := bbase (se 3 (by rfl) ⟨106781, by rfl⟩ : syracuseStep 569501 = 213563) (by norm_num)
theorem B962725 : Blo 299831 962725 := bbase (se 4 (by rfl) ⟨90255, by rfl⟩ : syracuseStep 962725 = 180511) (by norm_num)
theorem B340141 : Blo 299831 340141 := bbase (se 3 (by rfl) ⟨63776, by rfl⟩ : syracuseStep 340141 = 127553) (by norm_num)
theorem B340177 : Blo 299831 340177 := bbase (se 2 (by rfl) ⟨127566, by rfl⟩ : syracuseStep 340177 = 255133) (by norm_num)
theorem B340213 : Blo 299831 340213 := bbase (se 5 (by rfl) ⟨15947, by rfl⟩ : syracuseStep 340213 = 31895) (by norm_num)
theorem B340249 : Blo 299831 340249 := bbase (se 2 (by rfl) ⟨127593, by rfl⟩ : syracuseStep 340249 = 255187) (by norm_num)
theorem B405805 : Blo 299831 405805 := bbase (se 3 (by rfl) ⟨76088, by rfl⟩ : syracuseStep 405805 = 152177) (by norm_num)
theorem B340285 : Blo 299831 340285 := bbase (se 3 (by rfl) ⟨63803, by rfl⟩ : syracuseStep 340285 = 127607) (by norm_num)
theorem B340321 : Blo 299831 340321 := bbase (se 2 (by rfl) ⟨127620, by rfl⟩ : syracuseStep 340321 = 255241) (by norm_num)
theorem B340357 : Blo 299831 340357 := bbase (se 4 (by rfl) ⟨31908, by rfl⟩ : syracuseStep 340357 = 63817) (by norm_num)
theorem B340393 : Blo 299831 340393 := bbase (se 2 (by rfl) ⟨127647, by rfl⟩ : syracuseStep 340393 = 255295) (by norm_num)
theorem B766381 : Blo 299831 766381 := bbase (se 3 (by rfl) ⟨143696, by rfl⟩ : syracuseStep 766381 = 287393) (by norm_num)
theorem B340429 : Blo 299831 340429 := bbase (se 3 (by rfl) ⟨63830, by rfl⟩ : syracuseStep 340429 = 127661) (by norm_num)
theorem B1290725 : Blo 299831 1290725 := bbase (se 4 (by rfl) ⟨121005, by rfl⟩ : syracuseStep 1290725 = 242011) (by norm_num)
theorem B340465 : Blo 299831 340465 := bbase (se 2 (by rfl) ⟨127674, by rfl⟩ : syracuseStep 340465 = 255349) (by norm_num)
theorem B340501 : Blo 299831 340501 := bbase (se 6 (by rfl) ⟨7980, by rfl⟩ : syracuseStep 340501 = 15961) (by norm_num)
theorem B766493 : Blo 299831 766493 := bbase (se 3 (by rfl) ⟨143717, by rfl⟩ : syracuseStep 766493 = 287435) (by norm_num)
theorem B340537 : Blo 299831 340537 := bbase (se 2 (by rfl) ⟨127701, by rfl⟩ : syracuseStep 340537 = 255403) (by norm_num)
theorem B340573 : Blo 299831 340573 := bbase (se 3 (by rfl) ⟨63857, by rfl⟩ : syracuseStep 340573 = 127715) (by norm_num)
theorem B340609 : Blo 299831 340609 := bbase (se 2 (by rfl) ⟨127728, by rfl⟩ : syracuseStep 340609 = 255457) (by norm_num)
theorem B340645 : Blo 299831 340645 := bbase (se 4 (by rfl) ⟨31935, by rfl⟩ : syracuseStep 340645 = 63871) (by norm_num)
theorem B340681 : Blo 299831 340681 := bbase (se 2 (by rfl) ⟨127755, by rfl⟩ : syracuseStep 340681 = 255511) (by norm_num)
theorem B406237 : Blo 299831 406237 := bbase (se 3 (by rfl) ⟨76169, by rfl⟩ : syracuseStep 406237 = 152339) (by norm_num)
theorem B766685 : Blo 299831 766685 := bbase (se 3 (by rfl) ⟨143753, by rfl⟩ : syracuseStep 766685 = 287507) (by norm_num)
theorem B340717 : Blo 299831 340717 := bbase (se 3 (by rfl) ⟨63884, by rfl⟩ : syracuseStep 340717 = 127769) (by norm_num)
theorem B340753 : Blo 299831 340753 := bbase (se 2 (by rfl) ⟨127782, by rfl⟩ : syracuseStep 340753 = 255565) (by norm_num)
theorem B340789 : Blo 299831 340789 := bbase (se 5 (by rfl) ⟨15974, by rfl⟩ : syracuseStep 340789 = 31949) (by norm_num)
theorem B340825 : Blo 299831 340825 := bbase (se 2 (by rfl) ⟨127809, by rfl⟩ : syracuseStep 340825 = 255619) (by norm_num)
theorem B340861 : Blo 299831 340861 := bbase (se 3 (by rfl) ⟨63911, by rfl⟩ : syracuseStep 340861 = 127823) (by norm_num)
theorem B570253 : Blo 299831 570253 := bbase (se 3 (by rfl) ⟨106922, by rfl⟩ : syracuseStep 570253 = 213845) (by norm_num)
theorem B340897 : Blo 299831 340897 := bbase (se 2 (by rfl) ⟨127836, by rfl⟩ : syracuseStep 340897 = 255673) (by norm_num)
theorem B406453 : Blo 299831 406453 := bbase (se 5 (by rfl) ⟨19052, by rfl⟩ : syracuseStep 406453 = 38105) (by norm_num)
theorem B340933 : Blo 299831 340933 := bbase (se 4 (by rfl) ⟨31962, by rfl⟩ : syracuseStep 340933 = 63925) (by norm_num)
theorem B340969 : Blo 299831 340969 := bbase (se 2 (by rfl) ⟨127863, by rfl⟩ : syracuseStep 340969 = 255727) (by norm_num)
theorem B341005 : Blo 299831 341005 := bbase (se 3 (by rfl) ⟨63938, by rfl⟩ : syracuseStep 341005 = 127877) (by norm_num)
theorem B570397 : Blo 299831 570397 := bbase (se 3 (by rfl) ⟨106949, by rfl⟩ : syracuseStep 570397 = 213899) (by norm_num)
theorem B341041 : Blo 299831 341041 := bbase (se 2 (by rfl) ⟨127890, by rfl⟩ : syracuseStep 341041 = 255781) (by norm_num)
theorem B1520693 : Blo 299831 1520693 := bbase (se 5 (by rfl) ⟨71282, by rfl⟩ : syracuseStep 1520693 = 142565) (by norm_num)
theorem B767029 : Blo 299831 767029 := bbase (se 5 (by rfl) ⟨35954, by rfl⟩ : syracuseStep 767029 = 71909) (by norm_num)
theorem B341077 : Blo 299831 341077 := bbase (se 8 (by rfl) ⟨1998, by rfl⟩ : syracuseStep 341077 = 3997) (by norm_num)
theorem B341113 : Blo 299831 341113 := bbase (se 2 (by rfl) ⟨127917, by rfl⟩ : syracuseStep 341113 = 255835) (by norm_num)
theorem B341149 : Blo 299831 341149 := bbase (se 3 (by rfl) ⟨63965, by rfl⟩ : syracuseStep 341149 = 127931) (by norm_num)
theorem B767141 : Blo 299831 767141 := bbase (se 4 (by rfl) ⟨71919, by rfl⟩ : syracuseStep 767141 = 143839) (by norm_num)
theorem B570557 : Blo 299831 570557 := bbase (se 3 (by rfl) ⟨106979, by rfl⟩ : syracuseStep 570557 = 213959) (by norm_num)
theorem B341185 : Blo 299831 341185 := bbase (se 2 (by rfl) ⟨127944, by rfl⟩ : syracuseStep 341185 = 255889) (by norm_num)
theorem B341221 : Blo 299831 341221 := bbase (se 4 (by rfl) ⟨31989, by rfl⟩ : syracuseStep 341221 = 63979) (by norm_num)
theorem B341257 : Blo 299831 341257 := bbase (se 2 (by rfl) ⟨127971, by rfl⟩ : syracuseStep 341257 = 255943) (by norm_num)
theorem B341293 : Blo 299831 341293 := bbase (se 3 (by rfl) ⟨63992, by rfl⟩ : syracuseStep 341293 = 127985) (by norm_num)
theorem B570701 : Blo 299831 570701 := bbase (se 3 (by rfl) ⟨107006, by rfl⟩ : syracuseStep 570701 = 214013) (by norm_num)
theorem B341329 : Blo 299831 341329 := bbase (se 2 (by rfl) ⟨127998, by rfl⟩ : syracuseStep 341329 = 255997) (by norm_num)
theorem B767333 : Blo 299831 767333 := bbase (se 4 (by rfl) ⟨71937, by rfl⟩ : syracuseStep 767333 = 143875) (by norm_num)
theorem B2569589 : Blo 299831 2569589 := bbase (se 5 (by rfl) ⟨120449, by rfl⟩ : syracuseStep 2569589 = 240899) (by norm_num)
theorem B341365 : Blo 299831 341365 := bbase (se 5 (by rfl) ⟨16001, by rfl⟩ : syracuseStep 341365 = 32003) (by norm_num)
theorem B341401 : Blo 299831 341401 := bbase (se 2 (by rfl) ⟨128025, by rfl⟩ : syracuseStep 341401 = 256051) (by norm_num)
theorem B1717685 : Blo 299831 1717685 := bbase (se 5 (by rfl) ⟨80516, by rfl⟩ : syracuseStep 1717685 = 161033) (by norm_num)
theorem B341437 : Blo 299831 341437 := bbase (se 3 (by rfl) ⟨64019, by rfl⟩ : syracuseStep 341437 = 128039) (by norm_num)
theorem B1291733 : Blo 299831 1291733 := bbase (se 7 (by rfl) ⟨15137, by rfl⟩ : syracuseStep 1291733 = 30275) (by norm_num)
theorem B341473 : Blo 299831 341473 := bbase (se 2 (by rfl) ⟨128052, by rfl⟩ : syracuseStep 341473 = 256105) (by norm_num)
theorem B341509 : Blo 299831 341509 := bbase (se 4 (by rfl) ⟨32016, by rfl⟩ : syracuseStep 341509 = 64033) (by norm_num)
theorem B341545 : Blo 299831 341545 := bbase (se 2 (by rfl) ⟨128079, by rfl⟩ : syracuseStep 341545 = 256159) (by norm_num)
theorem B341581 : Blo 299831 341581 := bbase (se 3 (by rfl) ⟨64046, by rfl⟩ : syracuseStep 341581 = 128093) (by norm_num)
theorem B570989 : Blo 299831 570989 := bbase (se 3 (by rfl) ⟨107060, by rfl⟩ : syracuseStep 570989 = 214121) (by norm_num)
theorem B341617 : Blo 299831 341617 := bbase (se 2 (by rfl) ⟨128106, by rfl⟩ : syracuseStep 341617 = 256213) (by norm_num)
theorem B341653 : Blo 299831 341653 := bbase (se 6 (by rfl) ⟨8007, by rfl⟩ : syracuseStep 341653 = 16015) (by norm_num)
theorem B341689 : Blo 299831 341689 := bbase (se 2 (by rfl) ⟨128133, by rfl⟩ : syracuseStep 341689 = 256267) (by norm_num)
theorem B767677 : Blo 299831 767677 := bbase (se 3 (by rfl) ⟨143939, by rfl⟩ : syracuseStep 767677 = 287879) (by norm_num)
theorem B341725 : Blo 299831 341725 := bbase (se 3 (by rfl) ⟨64073, by rfl⟩ : syracuseStep 341725 = 128147) (by norm_num)
theorem B341761 : Blo 299831 341761 := bbase (se 2 (by rfl) ⟨128160, by rfl⟩ : syracuseStep 341761 = 256321) (by norm_num)
theorem B571141 : Blo 299831 571141 := bbase (se 4 (by rfl) ⟨53544, by rfl⟩ : syracuseStep 571141 = 107089) (by norm_num)
theorem B341797 : Blo 299831 341797 := bbase (se 4 (by rfl) ⟨32043, by rfl⟩ : syracuseStep 341797 = 64087) (by norm_num)
theorem B767789 : Blo 299831 767789 := bbase (se 3 (by rfl) ⟨143960, by rfl⟩ : syracuseStep 767789 = 287921) (by norm_num)
theorem B767981 : Blo 299831 767981 := bbase (se 3 (by rfl) ⟨143996, by rfl⟩ : syracuseStep 767981 = 287993) (by norm_num)
theorem B571445 : Blo 299831 571445 := bbase (se 5 (by rfl) ⟨26786, by rfl⟩ : syracuseStep 571445 = 53573) (by norm_num)
theorem B505973 : Blo 299831 505973 := bbase (se 5 (by rfl) ⟨23717, by rfl⟩ : syracuseStep 505973 = 47435) (by norm_num)
theorem B1554565 : Blo 299831 1554565 := bbase (se 4 (by rfl) ⟨145740, by rfl⟩ : syracuseStep 1554565 = 291481) (by norm_num)
theorem B506101 : Blo 299831 506101 := bbase (se 5 (by rfl) ⟨23723, by rfl⟩ : syracuseStep 506101 = 47447) (by norm_num)
theorem B1521989 : Blo 299831 1521989 := bbase (se 4 (by rfl) ⟨142686, by rfl⟩ : syracuseStep 1521989 = 285373) (by norm_num)
theorem B768325 : Blo 299831 768325 := bbase (se 4 (by rfl) ⟨72030, by rfl⟩ : syracuseStep 768325 = 144061) (by norm_num)
theorem B506189 : Blo 299831 506189 := bbase (se 3 (by rfl) ⟨94910, by rfl⟩ : syracuseStep 506189 = 189821) (by norm_num)
theorem B768437 : Blo 299831 768437 := bbase (se 5 (by rfl) ⟨36020, by rfl⟩ : syracuseStep 768437 = 72041) (by norm_num)
theorem B506317 : Blo 299831 506317 := bbase (se 3 (by rfl) ⟨94934, by rfl⟩ : syracuseStep 506317 = 189869) (by norm_num)
theorem B1161733 : Blo 299831 1161733 := bbase (se 4 (by rfl) ⟨108912, by rfl⟩ : syracuseStep 1161733 = 217825) (by norm_num)
theorem B506405 : Blo 299831 506405 := bbase (se 4 (by rfl) ⟨47475, by rfl⟩ : syracuseStep 506405 = 94951) (by norm_num)
theorem B2964053 : Blo 299831 2964053 := bbase (se 8 (by rfl) ⟨17367, by rfl⟩ : syracuseStep 2964053 = 34735) (by norm_num)
theorem B768629 : Blo 299831 768629 := bbase (se 5 (by rfl) ⟨36029, by rfl⟩ : syracuseStep 768629 = 72059) (by norm_num)
theorem B506533 : Blo 299831 506533 := bbase (se 4 (by rfl) ⟨47487, by rfl⟩ : syracuseStep 506533 = 94975) (by norm_num)
theorem B506621 : Blo 299831 506621 := bbase (se 3 (by rfl) ⟨94991, by rfl⟩ : syracuseStep 506621 = 189983) (by norm_num)
theorem B572197 : Blo 299831 572197 := bbase (se 4 (by rfl) ⟨53643, by rfl⟩ : syracuseStep 572197 = 107287) (by norm_num)
theorem B506749 : Blo 299831 506749 := bbase (se 3 (by rfl) ⟨95015, by rfl⟩ : syracuseStep 506749 = 190031) (by norm_num)
theorem B408485 : Blo 299831 408485 := bbase (se 4 (by rfl) ⟨38295, by rfl⟩ : syracuseStep 408485 = 76591) (by norm_num)
theorem B572341 : Blo 299831 572341 := bbase (se 5 (by rfl) ⟨26828, by rfl⟩ : syracuseStep 572341 = 53657) (by norm_num)
theorem B768973 : Blo 299831 768973 := bbase (se 3 (by rfl) ⟨144182, by rfl⟩ : syracuseStep 768973 = 288365) (by norm_num)
theorem B506837 : Blo 299831 506837 := bbase (se 7 (by rfl) ⟨5939, by rfl⟩ : syracuseStep 506837 = 11879) (by norm_num)
theorem B965621 : Blo 299831 965621 := bbase (se 5 (by rfl) ⟨45263, by rfl⟩ : syracuseStep 965621 = 90527) (by norm_num)
theorem B506965 : Blo 299831 506965 := bbase (se 8 (by rfl) ⟨2970, by rfl⟩ : syracuseStep 506965 = 5941) (by norm_num)
theorem B572501 : Blo 299831 572501 := bbase (se 8 (by rfl) ⟨3354, by rfl⟩ : syracuseStep 572501 = 6709) (by norm_num)
theorem B507053 : Blo 299831 507053 := bbase (se 3 (by rfl) ⟨95072, by rfl⟩ : syracuseStep 507053 = 190145) (by norm_num)
theorem B1293509 : Blo 299831 1293509 := bbase (se 4 (by rfl) ⟨121266, by rfl⟩ : syracuseStep 1293509 = 242533) (by norm_num)
theorem B572645 : Blo 299831 572645 := bbase (se 4 (by rfl) ⟨53685, by rfl⟩ : syracuseStep 572645 = 107371) (by norm_num)
theorem B507181 : Blo 299831 507181 := bbase (se 3 (by rfl) ⟨95096, by rfl⟩ : syracuseStep 507181 = 190193) (by norm_num)
theorem B507269 : Blo 299831 507269 := bbase (se 4 (by rfl) ⟨47556, by rfl⟩ : syracuseStep 507269 = 95113) (by norm_num)
theorem B1457621 : Blo 299831 1457621 := bbase (se 7 (by rfl) ⟨17081, by rfl⟩ : syracuseStep 1457621 = 34163) (by norm_num)
theorem B507397 : Blo 299831 507397 := bbase (se 4 (by rfl) ⟨47568, by rfl⟩ : syracuseStep 507397 = 95137) (by norm_num)
theorem B572933 : Blo 299831 572933 := bbase (se 4 (by rfl) ⟨53712, by rfl⟩ : syracuseStep 572933 = 107425) (by norm_num)
theorem B1523285 : Blo 299831 1523285 := bbase (se 8 (by rfl) ⟨8925, by rfl⟩ : syracuseStep 1523285 = 17851) (by norm_num)
theorem B1719893 : Blo 299831 1719893 := bbase (se 8 (by rfl) ⟨10077, by rfl⟩ : syracuseStep 1719893 = 20155) (by norm_num)
theorem B507485 : Blo 299831 507485 := bbase (se 3 (by rfl) ⟨95153, by rfl⟩ : syracuseStep 507485 = 190307) (by norm_num)
theorem B867989 : Blo 299831 867989 := bbase (se 6 (by rfl) ⟨20343, by rfl⟩ : syracuseStep 867989 = 40687) (by norm_num)
theorem B573085 : Blo 299831 573085 := bbase (se 3 (by rfl) ⟨107453, by rfl⟩ : syracuseStep 573085 = 214907) (by norm_num)
theorem B507613 : Blo 299831 507613 := bbase (se 3 (by rfl) ⟨95177, by rfl⟩ : syracuseStep 507613 = 190355) (by norm_num)
theorem B1457909 : Blo 299831 1457909 := bbase (se 5 (by rfl) ⟨68339, by rfl⟩ : syracuseStep 1457909 = 136679) (by norm_num)
theorem B540437 : Blo 299831 540437 := bbase (se 6 (by rfl) ⟨12666, by rfl⟩ : syracuseStep 540437 = 25333) (by norm_num)
theorem B507701 : Blo 299831 507701 := bbase (se 5 (by rfl) ⟨23798, by rfl⟩ : syracuseStep 507701 = 47597) (by norm_num)
theorem B3358549 : Blo 299831 3358549 := bbase (se 9 (by rfl) ⟨9839, by rfl⟩ : syracuseStep 3358549 = 19679) (by norm_num)
theorem B3456917 : Blo 299831 3456917 := bbase (se 6 (by rfl) ⟨81021, by rfl⟩ : syracuseStep 3456917 = 162043) (by norm_num)
theorem B507829 : Blo 299831 507829 := bbase (se 5 (by rfl) ⟨23804, by rfl⟩ : syracuseStep 507829 = 47609) (by norm_num)
theorem B573389 : Blo 299831 573389 := bbase (se 3 (by rfl) ⟨107510, by rfl⟩ : syracuseStep 573389 = 215021) (by norm_num)
theorem B507917 : Blo 299831 507917 := bbase (se 3 (by rfl) ⟨95234, by rfl⟩ : syracuseStep 507917 = 190469) (by norm_num)
theorem B508045 : Blo 299831 508045 := bbase (se 3 (by rfl) ⟨95258, by rfl⟩ : syracuseStep 508045 = 190517) (by norm_num)
theorem B508133 : Blo 299831 508133 := bbase (se 4 (by rfl) ⟨47637, by rfl⟩ : syracuseStep 508133 = 95275) (by norm_num)
theorem B966917 : Blo 299831 966917 := bbase (se 4 (by rfl) ⟨90648, by rfl⟩ : syracuseStep 966917 = 181297) (by norm_num)
theorem B508261 : Blo 299831 508261 := bbase (se 4 (by rfl) ⟨47649, by rfl⟩ : syracuseStep 508261 = 95299) (by norm_num)
theorem B508349 : Blo 299831 508349 := bbase (se 3 (by rfl) ⟨95315, by rfl⟩ : syracuseStep 508349 = 190631) (by norm_num)
theorem B508477 : Blo 299831 508477 := bbase (se 3 (by rfl) ⟨95339, by rfl⟩ : syracuseStep 508477 = 190679) (by norm_num)
theorem B344669 : Blo 299831 344669 := bbase (se 3 (by rfl) ⟨64625, by rfl⟩ : syracuseStep 344669 = 129251) (by norm_num)
theorem B1229413 : Blo 299831 1229413 := bbase (se 4 (by rfl) ⟨115257, by rfl⟩ : syracuseStep 1229413 = 230515) (by norm_num)
theorem B508565 : Blo 299831 508565 := bbase (se 6 (by rfl) ⟨11919, by rfl⟩ : syracuseStep 508565 = 23839) (by norm_num)
theorem B574141 : Blo 299831 574141 := bbase (se 3 (by rfl) ⟨107651, by rfl⟩ : syracuseStep 574141 = 215303) (by norm_num)
theorem B508693 : Blo 299831 508693 := bbase (se 6 (by rfl) ⟨11922, by rfl⟩ : syracuseStep 508693 = 23845) (by norm_num)
theorem B574285 : Blo 299831 574285 := bbase (se 3 (by rfl) ⟨107678, by rfl⟩ : syracuseStep 574285 = 215357) (by norm_num)
theorem B1524581 : Blo 299831 1524581 := bbase (se 4 (by rfl) ⟨142929, by rfl⟩ : syracuseStep 1524581 = 285859) (by norm_num)
theorem B508781 : Blo 299831 508781 := bbase (se 3 (by rfl) ⟨95396, by rfl⟩ : syracuseStep 508781 = 190793) (by norm_num)
theorem B345061 : Blo 299831 345061 := bbase (se 4 (by rfl) ⟨32349, by rfl⟩ : syracuseStep 345061 = 64699) (by norm_num)
theorem B508909 : Blo 299831 508909 := bbase (se 3 (by rfl) ⟨95420, by rfl⟩ : syracuseStep 508909 = 190841) (by norm_num)
theorem B574445 : Blo 299831 574445 := bbase (se 3 (by rfl) ⟨107708, by rfl⟩ : syracuseStep 574445 = 215417) (by norm_num)
theorem B508997 : Blo 299831 508997 := bbase (se 4 (by rfl) ⟨47718, by rfl⟩ : syracuseStep 508997 = 95437) (by norm_num)
theorem B574589 : Blo 299831 574589 := bbase (se 3 (by rfl) ⟨107735, by rfl⟩ : syracuseStep 574589 = 215471) (by norm_num)
theorem B509125 : Blo 299831 509125 := bbase (se 4 (by rfl) ⟨47730, by rfl⟩ : syracuseStep 509125 = 95461) (by norm_num)
theorem B1557701 : Blo 299831 1557701 := bbase (se 4 (by rfl) ⟨146034, by rfl⟩ : syracuseStep 1557701 = 292069) (by norm_num)
theorem B509213 : Blo 299831 509213 := bbase (se 3 (by rfl) ⟨95477, by rfl⟩ : syracuseStep 509213 = 190955) (by norm_num)
theorem B640381 : Blo 299831 640381 := bbase (se 3 (by rfl) ⟨120071, by rfl⟩ : syracuseStep 640381 = 240143) (by norm_num)
theorem B771461 : Blo 299831 771461 := bbase (se 4 (by rfl) ⟨72324, by rfl⟩ : syracuseStep 771461 = 144649) (by norm_num)
theorem B509341 : Blo 299831 509341 := bbase (se 3 (by rfl) ⟨95501, by rfl⟩ : syracuseStep 509341 = 191003) (by norm_num)
theorem B574877 : Blo 299831 574877 := bbase (se 3 (by rfl) ⟨107789, by rfl⟩ : syracuseStep 574877 = 215579) (by norm_num)
theorem B509429 : Blo 299831 509429 := bbase (se 5 (by rfl) ⟨23879, by rfl⟩ : syracuseStep 509429 = 47759) (by norm_num)
theorem B575029 : Blo 299831 575029 := bbase (se 5 (by rfl) ⟨26954, by rfl⟩ : syracuseStep 575029 = 53909) (by norm_num)
theorem B345677 : Blo 299831 345677 := bbase (se 3 (by rfl) ⟨64814, by rfl⟩ : syracuseStep 345677 = 129629) (by norm_num)
theorem B509557 : Blo 299831 509557 := bbase (se 5 (by rfl) ⟨23885, by rfl⟩ : syracuseStep 509557 = 47771) (by norm_num)
theorem B509645 : Blo 299831 509645 := bbase (se 3 (by rfl) ⟨95558, by rfl⟩ : syracuseStep 509645 = 191117) (by norm_num)
theorem B640757 : Blo 299831 640757 := bbase (se 5 (by rfl) ⟨30035, by rfl⟩ : syracuseStep 640757 = 60071) (by norm_num)
theorem B509773 : Blo 299831 509773 := bbase (se 3 (by rfl) ⟨95582, by rfl⟩ : syracuseStep 509773 = 191165) (by norm_num)
theorem B575333 : Blo 299831 575333 := bbase (se 4 (by rfl) ⟨53937, by rfl⟩ : syracuseStep 575333 = 107875) (by norm_num)
theorem B542629 : Blo 299831 542629 := bbase (se 4 (by rfl) ⟨50871, by rfl⟩ : syracuseStep 542629 = 101743) (by norm_num)
theorem B509861 : Blo 299831 509861 := bbase (se 4 (by rfl) ⟨47799, by rfl⟩ : syracuseStep 509861 = 95599) (by norm_num)
theorem B542701 : Blo 299831 542701 := bbase (se 3 (by rfl) ⟨101756, by rfl⟩ : syracuseStep 542701 = 203513) (by norm_num)
theorem B870389 : Blo 299831 870389 := bbase (se 5 (by rfl) ⟨40799, by rfl⟩ : syracuseStep 870389 = 81599) (by norm_num)
theorem B509989 : Blo 299831 509989 := bbase (se 4 (by rfl) ⟨47811, by rfl⟩ : syracuseStep 509989 = 95623) (by norm_num)
theorem B968773 : Blo 299831 968773 := bbase (se 4 (by rfl) ⟨90822, by rfl⟩ : syracuseStep 968773 = 181645) (by norm_num)
theorem B641125 : Blo 299831 641125 := bbase (se 4 (by rfl) ⟨60105, by rfl⟩ : syracuseStep 641125 = 120211) (by norm_num)
theorem B1525877 : Blo 299831 1525877 := bbase (se 5 (by rfl) ⟨71525, by rfl⟩ : syracuseStep 1525877 = 143051) (by norm_num)
theorem B510077 : Blo 299831 510077 := bbase (se 3 (by rfl) ⟨95639, by rfl⟩ : syracuseStep 510077 = 191279) (by norm_num)
theorem B510205 : Blo 299831 510205 := bbase (se 3 (by rfl) ⟨95663, by rfl⟩ : syracuseStep 510205 = 191327) (by norm_num)
theorem B510293 : Blo 299831 510293 := bbase (se 10 (by rfl) ⟨747, by rfl⟩ : syracuseStep 510293 = 1495) (by norm_num)
theorem B510421 : Blo 299831 510421 := bbase (se 7 (by rfl) ⟨5981, by rfl⟩ : syracuseStep 510421 = 11963) (by norm_num)
theorem B510509 : Blo 299831 510509 := bbase (se 3 (by rfl) ⟨95720, by rfl⟩ : syracuseStep 510509 = 191441) (by norm_num)
theorem B576085 : Blo 299831 576085 := bbase (se 8 (by rfl) ⟨3375, by rfl⟩ : syracuseStep 576085 = 6751) (by norm_num)
theorem B379505 : Blo 299831 379505 := bbase (se 2 (by rfl) ⟨142314, by rfl⟩ : syracuseStep 379505 = 284629) (by norm_num)
theorem B3263125 : Blo 299831 3263125 := bbase (se 6 (by rfl) ⟨76479, by rfl⟩ : syracuseStep 3263125 = 152959) (by norm_num)
theorem B379561 : Blo 299831 379561 := bbase (se 2 (by rfl) ⟨142335, by rfl⟩ : syracuseStep 379561 = 284671) (by norm_num)
theorem B510637 : Blo 299831 510637 := bbase (se 3 (by rfl) ⟨95744, by rfl⟩ : syracuseStep 510637 = 191489) (by norm_num)
theorem B576229 : Blo 299831 576229 := bbase (se 4 (by rfl) ⟨54021, by rfl⟩ : syracuseStep 576229 = 108043) (by norm_num)
theorem B510725 : Blo 299831 510725 := bbase (se 4 (by rfl) ⟨47880, by rfl⟩ : syracuseStep 510725 = 95761) (by norm_num)
theorem B379657 : Blo 299831 379657 := bbase (se 2 (by rfl) ⟨142371, by rfl⟩ : syracuseStep 379657 = 284743) (by norm_num)
theorem B674621 : Blo 299831 674621 := bbase (se 3 (by rfl) ⟨126491, by rfl⟩ : syracuseStep 674621 = 252983) (by norm_num)
theorem B1231685 : Blo 299831 1231685 := bbase (se 4 (by rfl) ⟨115470, by rfl⟩ : syracuseStep 1231685 = 230941) (by norm_num)
theorem B674693 : Blo 299831 674693 := bbase (se 4 (by rfl) ⟨63252, by rfl⟩ : syracuseStep 674693 = 126505) (by norm_num)
theorem B510853 : Blo 299831 510853 := bbase (se 4 (by rfl) ⟨47892, by rfl⟩ : syracuseStep 510853 = 95785) (by norm_num)
theorem B576389 : Blo 299831 576389 := bbase (se 4 (by rfl) ⟨54036, by rfl⟩ : syracuseStep 576389 = 108073) (by norm_num)
theorem B3263381 : Blo 299831 3263381 := bbase (se 6 (by rfl) ⟨76485, by rfl⟩ : syracuseStep 3263381 = 152971) (by norm_num)
theorem B379829 : Blo 299831 379829 := bbase (se 5 (by rfl) ⟨17804, by rfl⟩ : syracuseStep 379829 = 35609) (by norm_num)
theorem B674765 : Blo 299831 674765 := bbase (se 3 (by rfl) ⟨126518, by rfl⟩ : syracuseStep 674765 = 253037) (by norm_num)
theorem B510941 : Blo 299831 510941 := bbase (se 3 (by rfl) ⟨95801, by rfl⟩ : syracuseStep 510941 = 191603) (by norm_num)
theorem B379885 : Blo 299831 379885 := bbase (se 3 (by rfl) ⟨71228, by rfl⟩ : syracuseStep 379885 = 142457) (by norm_num)
theorem B674837 : Blo 299831 674837 := bbase (se 6 (by rfl) ⟨15816, by rfl⟩ : syracuseStep 674837 = 31633) (by norm_num)
theorem B576533 : Blo 299831 576533 := bbase (se 6 (by rfl) ⟨13512, by rfl⟩ : syracuseStep 576533 = 27025) (by norm_num)
theorem B379981 : Blo 299831 379981 := bbase (se 3 (by rfl) ⟨71246, by rfl⟩ : syracuseStep 379981 = 142493) (by norm_num)
theorem B674909 : Blo 299831 674909 := bbase (se 3 (by rfl) ⟨126545, by rfl⟩ : syracuseStep 674909 = 253091) (by norm_num)
theorem B511069 : Blo 299831 511069 := bbase (se 3 (by rfl) ⟨95825, by rfl⟩ : syracuseStep 511069 = 191651) (by norm_num)
theorem B674981 : Blo 299831 674981 := bbase (se 4 (by rfl) ⟨63279, by rfl⟩ : syracuseStep 674981 = 126559) (by norm_num)
theorem B511157 : Blo 299831 511157 := bbase (se 5 (by rfl) ⟨23960, by rfl⟩ : syracuseStep 511157 = 47921) (by norm_num)
theorem B675053 : Blo 299831 675053 := bbase (se 3 (by rfl) ⟨126572, by rfl⟩ : syracuseStep 675053 = 253145) (by norm_num)
theorem B380153 : Blo 299831 380153 := bbase (se 2 (by rfl) ⟨142557, by rfl⟩ : syracuseStep 380153 = 285115) (by norm_num)
theorem B544013 : Blo 299831 544013 := bbase (se 3 (by rfl) ⟨102002, by rfl⟩ : syracuseStep 544013 = 204005) (by norm_num)
theorem B380209 : Blo 299831 380209 := bbase (se 2 (by rfl) ⟨142578, by rfl⟩ : syracuseStep 380209 = 285157) (by norm_num)
theorem B675125 : Blo 299831 675125 := bbase (se 5 (by rfl) ⟨31646, by rfl⟩ : syracuseStep 675125 = 63293) (by norm_num)
theorem B511285 : Blo 299831 511285 := bbase (se 5 (by rfl) ⟨23966, by rfl⟩ : syracuseStep 511285 = 47933) (by norm_num)
theorem B544085 : Blo 299831 544085 := bbase (se 11 (by rfl) ⟨398, by rfl⟩ : syracuseStep 544085 = 797) (by norm_num)
theorem B1297781 : Blo 299831 1297781 := bbase (se 5 (by rfl) ⟨60833, by rfl⟩ : syracuseStep 1297781 = 121667) (by norm_num)
theorem B675197 : Blo 299831 675197 := bbase (se 3 (by rfl) ⟨126599, by rfl⟩ : syracuseStep 675197 = 253199) (by norm_num)
theorem B1527173 : Blo 299831 1527173 := bbase (se 4 (by rfl) ⟨143172, by rfl⟩ : syracuseStep 1527173 = 286345) (by norm_num)
theorem B511373 : Blo 299831 511373 := bbase (se 3 (by rfl) ⟨95882, by rfl⟩ : syracuseStep 511373 = 191765) (by norm_num)
theorem B380305 : Blo 299831 380305 := bbase (se 2 (by rfl) ⟨142614, by rfl⟩ : syracuseStep 380305 = 285229) (by norm_num)
theorem B675269 : Blo 299831 675269 := bbase (se 4 (by rfl) ⟨63306, by rfl⟩ : syracuseStep 675269 = 126613) (by norm_num)
theorem B675341 : Blo 299831 675341 := bbase (se 3 (by rfl) ⟨126626, by rfl⟩ : syracuseStep 675341 = 253253) (by norm_num)
theorem B511501 : Blo 299831 511501 := bbase (se 3 (by rfl) ⟨95906, by rfl⟩ : syracuseStep 511501 = 191813) (by norm_num)
theorem B380477 : Blo 299831 380477 := bbase (se 3 (by rfl) ⟨71339, by rfl⟩ : syracuseStep 380477 = 142679) (by norm_num)
theorem B642629 : Blo 299831 642629 := bbase (se 4 (by rfl) ⟨60246, by rfl⟩ : syracuseStep 642629 = 120493) (by norm_num)
theorem B675413 : Blo 299831 675413 := bbase (se 8 (by rfl) ⟨3957, by rfl⟩ : syracuseStep 675413 = 7915) (by norm_num)
theorem B511589 : Blo 299831 511589 := bbase (se 4 (by rfl) ⟨47961, by rfl⟩ : syracuseStep 511589 = 95923) (by norm_num)
theorem B380533 : Blo 299831 380533 := bbase (se 5 (by rfl) ⟨17837, by rfl⟩ : syracuseStep 380533 = 35675) (by norm_num)
theorem B675485 : Blo 299831 675485 := bbase (se 3 (by rfl) ⟨126653, by rfl⟩ : syracuseStep 675485 = 253307) (by norm_num)
theorem B380629 : Blo 299831 380629 := bbase (se 7 (by rfl) ⟨4460, by rfl⟩ : syracuseStep 380629 = 8921) (by norm_num)
theorem B642773 : Blo 299831 642773 := bbase (se 7 (by rfl) ⟨7532, by rfl⟩ : syracuseStep 642773 = 15065) (by norm_num)
theorem B675557 : Blo 299831 675557 := bbase (se 4 (by rfl) ⟨63333, by rfl⟩ : syracuseStep 675557 = 126667) (by norm_num)
theorem B511717 : Blo 299831 511717 := bbase (se 4 (by rfl) ⟨47973, by rfl⟩ : syracuseStep 511717 = 95947) (by norm_num)
theorem B675629 : Blo 299831 675629 := bbase (se 3 (by rfl) ⟨126680, by rfl⟩ : syracuseStep 675629 = 253361) (by norm_num)
theorem B1953589 : Blo 299831 1953589 := bbase (se 5 (by rfl) ⟨91574, by rfl⟩ : syracuseStep 1953589 = 183149) (by norm_num)
theorem B511805 : Blo 299831 511805 := bbase (se 3 (by rfl) ⟨95963, by rfl⟩ : syracuseStep 511805 = 191927) (by norm_num)
theorem B675701 : Blo 299831 675701 := bbase (se 5 (by rfl) ⟨31673, by rfl⟩ : syracuseStep 675701 = 63347) (by norm_num)
theorem B380801 : Blo 299831 380801 := bbase (se 2 (by rfl) ⟨142800, by rfl⟩ : syracuseStep 380801 = 285601) (by norm_num)
theorem B380857 : Blo 299831 380857 := bbase (se 2 (by rfl) ⟨142821, by rfl⟩ : syracuseStep 380857 = 285643) (by norm_num)
theorem B675773 : Blo 299831 675773 := bbase (se 3 (by rfl) ⟨126707, by rfl⟩ : syracuseStep 675773 = 253415) (by norm_num)
theorem B511933 : Blo 299831 511933 := bbase (se 3 (by rfl) ⟨95987, by rfl⟩ : syracuseStep 511933 = 191975) (by norm_num)
theorem B675845 : Blo 299831 675845 := bbase (se 4 (by rfl) ⟨63360, by rfl⟩ : syracuseStep 675845 = 126721) (by norm_num)
theorem B512021 : Blo 299831 512021 := bbase (se 6 (by rfl) ⟨12000, by rfl⟩ : syracuseStep 512021 = 24001) (by norm_num)
theorem B380953 : Blo 299831 380953 := bbase (se 2 (by rfl) ⟨142857, by rfl⟩ : syracuseStep 380953 = 285715) (by norm_num)
theorem B577565 : Blo 299831 577565 := bbase (se 3 (by rfl) ⟨108293, by rfl⟩ : syracuseStep 577565 = 216587) (by norm_num)
theorem B643133 : Blo 299831 643133 := bbase (se 3 (by rfl) ⟨120587, by rfl⟩ : syracuseStep 643133 = 241175) (by norm_num)
theorem B675917 : Blo 299831 675917 := bbase (se 3 (by rfl) ⟨126734, by rfl⟩ : syracuseStep 675917 = 253469) (by norm_num)
theorem B3887189 : Blo 299831 3887189 := bbase (se 8 (by rfl) ⟨22776, by rfl⟩ : syracuseStep 3887189 = 45553) (by norm_num)
theorem B413797 : Blo 299831 413797 := bbase (se 4 (by rfl) ⟨38793, by rfl⟩ : syracuseStep 413797 = 77587) (by norm_num)
theorem B675989 : Blo 299831 675989 := bbase (se 6 (by rfl) ⟨15843, by rfl⟩ : syracuseStep 675989 = 31687) (by norm_num)
theorem B512149 : Blo 299831 512149 := bbase (se 6 (by rfl) ⟨12003, by rfl⟩ : syracuseStep 512149 = 24007) (by norm_num)
theorem B2904245 : Blo 299831 2904245 := bbase (se 5 (by rfl) ⟨136136, by rfl⟩ : syracuseStep 2904245 = 272273) (by norm_num)
theorem B381125 : Blo 299831 381125 := bbase (se 4 (by rfl) ⟨35730, by rfl⟩ : syracuseStep 381125 = 71461) (by norm_num)
theorem B676061 : Blo 299831 676061 := bbase (se 3 (by rfl) ⟨126761, by rfl⟩ : syracuseStep 676061 = 253523) (by norm_num)
theorem B512237 : Blo 299831 512237 := bbase (se 3 (by rfl) ⟨96044, by rfl⟩ : syracuseStep 512237 = 192089) (by norm_num)
theorem B381181 : Blo 299831 381181 := bbase (se 3 (by rfl) ⟨71471, by rfl⟩ : syracuseStep 381181 = 142943) (by norm_num)
theorem B577813 : Blo 299831 577813 := bbase (se 6 (by rfl) ⟨13542, by rfl⟩ : syracuseStep 577813 = 27085) (by norm_num)
theorem B676133 : Blo 299831 676133 := bbase (se 4 (by rfl) ⟨63387, by rfl⟩ : syracuseStep 676133 = 126775) (by norm_num)
theorem B381277 : Blo 299831 381277 := bbase (se 3 (by rfl) ⟨71489, by rfl⟩ : syracuseStep 381277 = 142979) (by norm_num)
theorem B676205 : Blo 299831 676205 := bbase (se 3 (by rfl) ⟨126788, by rfl⟩ : syracuseStep 676205 = 253577) (by norm_num)
theorem B610669 : Blo 299831 610669 := bbase (se 3 (by rfl) ⟨114500, by rfl⟩ : syracuseStep 610669 = 229001) (by norm_num)
theorem B512365 : Blo 299831 512365 := bbase (se 3 (by rfl) ⟨96068, by rfl⟩ : syracuseStep 512365 = 192137) (by norm_num)
theorem B676277 : Blo 299831 676277 := bbase (se 5 (by rfl) ⟨31700, by rfl⟩ : syracuseStep 676277 = 63401) (by norm_num)
theorem B512453 : Blo 299831 512453 := bbase (se 4 (by rfl) ⟨48042, by rfl⟩ : syracuseStep 512453 = 96085) (by norm_num)
theorem B676349 : Blo 299831 676349 := bbase (se 3 (by rfl) ⟨126815, by rfl⟩ : syracuseStep 676349 = 253631) (by norm_num)
theorem B381449 : Blo 299831 381449 := bbase (se 2 (by rfl) ⟨143043, by rfl⟩ : syracuseStep 381449 = 286087) (by norm_num)
theorem B381505 : Blo 299831 381505 := bbase (se 2 (by rfl) ⟨143064, by rfl⟩ : syracuseStep 381505 = 286129) (by norm_num)
theorem B676421 : Blo 299831 676421 := bbase (se 4 (by rfl) ⟨63414, by rfl⟩ : syracuseStep 676421 = 126829) (by norm_num)
theorem B512581 : Blo 299831 512581 := bbase (se 4 (by rfl) ⟨48054, by rfl⟩ : syracuseStep 512581 = 96109) (by norm_num)
theorem B676493 : Blo 299831 676493 := bbase (se 3 (by rfl) ⟨126842, by rfl⟩ : syracuseStep 676493 = 253685) (by norm_num)
theorem B1528469 : Blo 299831 1528469 := bbase (se 6 (by rfl) ⟨35823, by rfl⟩ : syracuseStep 1528469 = 71647) (by norm_num)
theorem B512669 : Blo 299831 512669 := bbase (se 3 (by rfl) ⟨96125, by rfl⟩ : syracuseStep 512669 = 192251) (by norm_num)
theorem B381601 : Blo 299831 381601 := bbase (se 2 (by rfl) ⟨143100, by rfl⟩ : syracuseStep 381601 = 286201) (by norm_num)
theorem B676565 : Blo 299831 676565 := bbase (se 7 (by rfl) ⟨7928, by rfl⟩ : syracuseStep 676565 = 15857) (by norm_num)
theorem B1037045 : Blo 299831 1037045 := bbase (se 5 (by rfl) ⟨48611, by rfl⟩ : syracuseStep 1037045 = 97223) (by norm_num)
theorem B676637 : Blo 299831 676637 := bbase (se 3 (by rfl) ⟨126869, by rfl⟩ : syracuseStep 676637 = 253739) (by norm_num)
theorem B381773 : Blo 299831 381773 := bbase (se 3 (by rfl) ⟨71582, by rfl⟩ : syracuseStep 381773 = 143165) (by norm_num)
theorem B611165 : Blo 299831 611165 := bbase (se 3 (by rfl) ⟨114593, by rfl⟩ : syracuseStep 611165 = 229187) (by norm_num)
theorem B676709 : Blo 299831 676709 := bbase (se 4 (by rfl) ⟨63441, by rfl⟩ : syracuseStep 676709 = 126883) (by norm_num)
theorem B381829 : Blo 299831 381829 := bbase (se 4 (by rfl) ⟨35796, by rfl⟩ : syracuseStep 381829 = 71593) (by norm_num)
theorem B676781 : Blo 299831 676781 := bbase (se 3 (by rfl) ⟨126896, by rfl⟩ : syracuseStep 676781 = 253793) (by norm_num)
theorem B644021 : Blo 299831 644021 := bbase (se 5 (by rfl) ⟨30188, by rfl⟩ : syracuseStep 644021 = 60377) (by norm_num)
theorem B381925 : Blo 299831 381925 := bbase (se 4 (by rfl) ⟨35805, by rfl⟩ : syracuseStep 381925 = 71611) (by norm_num)
theorem B676853 : Blo 299831 676853 := bbase (se 5 (by rfl) ⟨31727, by rfl⟩ : syracuseStep 676853 = 63455) (by norm_num)
theorem B349177 : Blo 299831 349177 := bbase (se 2 (by rfl) ⟨130941, by rfl⟩ : syracuseStep 349177 = 261883) (by norm_num)
theorem B611365 : Blo 299831 611365 := bbase (se 4 (by rfl) ⟨57315, by rfl⟩ : syracuseStep 611365 = 114631) (by norm_num)
theorem B676925 : Blo 299831 676925 := bbase (se 3 (by rfl) ⟨126923, by rfl⟩ : syracuseStep 676925 = 253847) (by norm_num)
theorem B676997 : Blo 299831 676997 := bbase (se 4 (by rfl) ⟨63468, by rfl⟩ : syracuseStep 676997 = 126937) (by norm_num)
theorem B382097 : Blo 299831 382097 := bbase (se 2 (by rfl) ⟨143286, by rfl⟩ : syracuseStep 382097 = 286573) (by norm_num)
theorem B644269 : Blo 299831 644269 := bbase (se 3 (by rfl) ⟨120800, by rfl⟩ : syracuseStep 644269 = 241601) (by norm_num)
theorem B382153 : Blo 299831 382153 := bbase (se 2 (by rfl) ⟨143307, by rfl⟩ : syracuseStep 382153 = 286615) (by norm_num)
theorem B677069 : Blo 299831 677069 := bbase (se 3 (by rfl) ⟨126950, by rfl⟩ : syracuseStep 677069 = 253901) (by norm_num)
theorem B2282741 : Blo 299831 2282741 := bbase (se 5 (by rfl) ⟨107003, by rfl⟩ : syracuseStep 2282741 = 214007) (by norm_num)
theorem B2577653 : Blo 299831 2577653 := bbase (se 5 (by rfl) ⟨120827, by rfl⟩ : syracuseStep 2577653 = 241655) (by norm_num)
theorem B677141 : Blo 299831 677141 := bbase (se 6 (by rfl) ⟨15870, by rfl⟩ : syracuseStep 677141 = 31741) (by norm_num)
theorem B382249 : Blo 299831 382249 := bbase (se 2 (by rfl) ⟨143343, by rfl⟩ : syracuseStep 382249 = 286687) (by norm_num)
theorem B677213 : Blo 299831 677213 := bbase (se 3 (by rfl) ⟨126977, by rfl⟩ : syracuseStep 677213 = 253955) (by norm_num)
theorem B677285 : Blo 299831 677285 := bbase (se 4 (by rfl) ⟨63495, by rfl⟩ : syracuseStep 677285 = 126991) (by norm_num)
theorem B382421 : Blo 299831 382421 := bbase (se 7 (by rfl) ⟨4481, by rfl⟩ : syracuseStep 382421 = 8963) (by norm_num)
theorem B677357 : Blo 299831 677357 := bbase (se 3 (by rfl) ⟨127004, by rfl⟩ : syracuseStep 677357 = 254009) (by norm_num)
theorem B480773 : Blo 299831 480773 := bbase (se 4 (by rfl) ⟨45072, by rfl⟩ : syracuseStep 480773 = 90145) (by norm_num)
theorem B382477 : Blo 299831 382477 := bbase (se 3 (by rfl) ⟨71714, by rfl⟩ : syracuseStep 382477 = 143429) (by norm_num)
theorem B677429 : Blo 299831 677429 := bbase (se 5 (by rfl) ⟨31754, by rfl⟩ : syracuseStep 677429 = 63509) (by norm_num)
theorem B874037 : Blo 299831 874037 := bbase (se 5 (by rfl) ⟨40970, by rfl⟩ : syracuseStep 874037 = 81941) (by norm_num)
theorem B382573 : Blo 299831 382573 := bbase (se 3 (by rfl) ⟨71732, by rfl⟩ : syracuseStep 382573 = 143465) (by norm_num)
theorem B677501 : Blo 299831 677501 := bbase (se 3 (by rfl) ⟨127031, by rfl⟩ : syracuseStep 677501 = 254063) (by norm_num)
theorem B480901 : Blo 299831 480901 := bbase (se 4 (by rfl) ⟨45084, by rfl⟩ : syracuseStep 480901 = 90169) (by norm_num)
theorem B644773 : Blo 299831 644773 := bbase (se 4 (by rfl) ⟨60447, by rfl⟩ : syracuseStep 644773 = 120895) (by norm_num)
theorem B677573 : Blo 299831 677573 := bbase (se 4 (by rfl) ⟨63522, by rfl⟩ : syracuseStep 677573 = 127045) (by norm_num)
theorem B677645 : Blo 299831 677645 := bbase (se 3 (by rfl) ⟨127058, by rfl⟩ : syracuseStep 677645 = 254117) (by norm_num)
theorem B382745 : Blo 299831 382745 := bbase (se 2 (by rfl) ⟨143529, by rfl⟩ : syracuseStep 382745 = 287059) (by norm_num)
theorem B382801 : Blo 299831 382801 := bbase (se 2 (by rfl) ⟨143550, by rfl⟩ : syracuseStep 382801 = 287101) (by norm_num)
theorem B677717 : Blo 299831 677717 := bbase (se 9 (by rfl) ⟨1985, by rfl⟩ : syracuseStep 677717 = 3971) (by norm_num)
theorem B677789 : Blo 299831 677789 := bbase (se 3 (by rfl) ⟨127085, by rfl⟩ : syracuseStep 677789 = 254171) (by norm_num)
theorem B1529765 : Blo 299831 1529765 := bbase (se 4 (by rfl) ⟨143415, by rfl⟩ : syracuseStep 1529765 = 286831) (by norm_num)
theorem B382897 : Blo 299831 382897 := bbase (se 2 (by rfl) ⟨143586, by rfl⟩ : syracuseStep 382897 = 287173) (by norm_num)
theorem B1103813 : Blo 299831 1103813 := bbase (se 4 (by rfl) ⟨103482, by rfl⟩ : syracuseStep 1103813 = 206965) (by norm_num)
theorem B677861 : Blo 299831 677861 := bbase (se 4 (by rfl) ⟨63549, by rfl⟩ : syracuseStep 677861 = 127099) (by norm_num)
theorem B546853 : Blo 299831 546853 := bbase (se 4 (by rfl) ⟨51267, by rfl⟩ : syracuseStep 546853 = 102535) (by norm_num)
theorem B677933 : Blo 299831 677933 := bbase (se 3 (by rfl) ⟨127112, by rfl⟩ : syracuseStep 677933 = 254225) (by norm_num)
theorem B383069 : Blo 299831 383069 := bbase (se 3 (by rfl) ⟨71825, by rfl⟩ : syracuseStep 383069 = 143651) (by norm_num)
theorem B612461 : Blo 299831 612461 := bbase (se 3 (by rfl) ⟨114836, by rfl⟩ : syracuseStep 612461 = 229673) (by norm_num)
theorem B678005 : Blo 299831 678005 := bbase (se 5 (by rfl) ⟨31781, by rfl⟩ : syracuseStep 678005 = 63563) (by norm_num)
theorem B383125 : Blo 299831 383125 := bbase (se 6 (by rfl) ⟨8979, by rfl⟩ : syracuseStep 383125 = 17959) (by norm_num)
theorem B972965 : Blo 299831 972965 := bbase (se 4 (by rfl) ⟨91215, by rfl⟩ : syracuseStep 972965 = 182431) (by norm_num)
theorem B678077 : Blo 299831 678077 := bbase (se 3 (by rfl) ⟨127139, by rfl⟩ : syracuseStep 678077 = 254279) (by norm_num)
theorem B383221 : Blo 299831 383221 := bbase (se 5 (by rfl) ⟨17963, by rfl⟩ : syracuseStep 383221 = 35927) (by norm_num)
theorem B547069 : Blo 299831 547069 := bbase (se 3 (by rfl) ⟨102575, by rfl⟩ : syracuseStep 547069 = 205151) (by norm_num)
theorem B678149 : Blo 299831 678149 := bbase (se 4 (by rfl) ⟨63576, by rfl⟩ : syracuseStep 678149 = 127153) (by norm_num)
theorem B776461 : Blo 299831 776461 := bbase (se 3 (by rfl) ⟨145586, by rfl⟩ : syracuseStep 776461 = 291173) (by norm_num)
theorem B678221 : Blo 299831 678221 := bbase (se 3 (by rfl) ⟨127166, by rfl⟩ : syracuseStep 678221 = 254333) (by norm_num)
theorem B678293 : Blo 299831 678293 := bbase (se 6 (by rfl) ⟨15897, by rfl⟩ : syracuseStep 678293 = 31795) (by norm_num)
theorem B383393 : Blo 299831 383393 := bbase (se 2 (by rfl) ⟨143772, by rfl⟩ : syracuseStep 383393 = 287545) (by norm_num)
theorem B383449 : Blo 299831 383449 := bbase (se 2 (by rfl) ⟨143793, by rfl⟩ : syracuseStep 383449 = 287587) (by norm_num)
theorem B678365 : Blo 299831 678365 := bbase (se 3 (by rfl) ⟨127193, by rfl⟩ : syracuseStep 678365 = 254387) (by norm_num)
theorem B645661 : Blo 299831 645661 := bbase (se 3 (by rfl) ⟨121061, by rfl⟩ : syracuseStep 645661 = 242123) (by norm_num)
theorem B678437 : Blo 299831 678437 := bbase (se 4 (by rfl) ⟨63603, by rfl⟩ : syracuseStep 678437 = 127207) (by norm_num)
theorem B383545 : Blo 299831 383545 := bbase (se 2 (by rfl) ⟨143829, by rfl⟩ : syracuseStep 383545 = 287659) (by norm_num)
theorem B678509 : Blo 299831 678509 := bbase (se 3 (by rfl) ⟨127220, by rfl⟩ : syracuseStep 678509 = 254441) (by norm_num)
theorem B875125 : Blo 299831 875125 := bbase (se 5 (by rfl) ⟨41021, by rfl⟩ : syracuseStep 875125 = 82043) (by norm_num)
theorem B613021 : Blo 299831 613021 := bbase (se 3 (by rfl) ⟨114941, by rfl⟩ : syracuseStep 613021 = 229883) (by norm_num)
theorem B678581 : Blo 299831 678581 := bbase (se 5 (by rfl) ⟨31808, by rfl⟩ : syracuseStep 678581 = 63617) (by norm_num)
theorem B383717 : Blo 299831 383717 := bbase (se 4 (by rfl) ⟨35973, by rfl⟩ : syracuseStep 383717 = 71947) (by norm_num)
theorem B678653 : Blo 299831 678653 := bbase (se 3 (by rfl) ⟨127247, by rfl⟩ : syracuseStep 678653 = 254495) (by norm_num)
theorem B383773 : Blo 299831 383773 := bbase (se 3 (by rfl) ⟨71957, by rfl⟩ : syracuseStep 383773 = 143915) (by norm_num)
theorem B678725 : Blo 299831 678725 := bbase (se 4 (by rfl) ⟨63630, by rfl⟩ : syracuseStep 678725 = 127261) (by norm_num)
theorem B383869 : Blo 299831 383869 := bbase (se 3 (by rfl) ⟨71975, by rfl⟩ : syracuseStep 383869 = 143951) (by norm_num)
theorem B678797 : Blo 299831 678797 := bbase (se 3 (by rfl) ⟨127274, by rfl⟩ : syracuseStep 678797 = 254549) (by norm_num)
theorem B678869 : Blo 299831 678869 := bbase (se 7 (by rfl) ⟨7955, by rfl⟩ : syracuseStep 678869 = 15911) (by norm_num)
theorem B482285 : Blo 299831 482285 := bbase (se 3 (by rfl) ⟨90428, by rfl⟩ : syracuseStep 482285 = 180857) (by norm_num)
theorem B646157 : Blo 299831 646157 := bbase (se 3 (by rfl) ⟨121154, by rfl⟩ : syracuseStep 646157 = 242309) (by norm_num)
theorem B678941 : Blo 299831 678941 := bbase (se 3 (by rfl) ⟨127301, by rfl⟩ : syracuseStep 678941 = 254603) (by norm_num)
theorem B580645 : Blo 299831 580645 := bbase (se 4 (by rfl) ⟨54435, by rfl⟩ : syracuseStep 580645 = 108871) (by norm_num)
theorem B384041 : Blo 299831 384041 := bbase (se 2 (by rfl) ⟨144015, by rfl⟩ : syracuseStep 384041 = 288031) (by norm_num)
theorem B1956917 : Blo 299831 1956917 := bbase (se 5 (by rfl) ⟨91730, by rfl⟩ : syracuseStep 1956917 = 183461) (by norm_num)
theorem B384097 : Blo 299831 384097 := bbase (se 2 (by rfl) ⟨144036, by rfl⟩ : syracuseStep 384097 = 288073) (by norm_num)
theorem B679013 : Blo 299831 679013 := bbase (se 4 (by rfl) ⟨63657, by rfl⟩ : syracuseStep 679013 = 127315) (by norm_num)
theorem B679085 : Blo 299831 679085 := bbase (se 3 (by rfl) ⟨127328, by rfl⟩ : syracuseStep 679085 = 254657) (by norm_num)
theorem B1531061 : Blo 299831 1531061 := bbase (se 5 (by rfl) ⟨71768, by rfl⟩ : syracuseStep 1531061 = 143537) (by norm_num)
theorem B384193 : Blo 299831 384193 := bbase (se 2 (by rfl) ⟨144072, by rfl⟩ : syracuseStep 384193 = 288145) (by norm_num)
theorem B449765 : Blo 299831 449765 := bbase (se 4 (by rfl) ⟨42165, by rfl⟩ : syracuseStep 449765 = 84331) (by norm_num)
theorem B679157 : Blo 299831 679157 := bbase (se 5 (by rfl) ⟨31835, by rfl⟩ : syracuseStep 679157 = 63671) (by norm_num)
theorem B449789 : Blo 299831 449789 := bbase (se 3 (by rfl) ⟨84335, by rfl⟩ : syracuseStep 449789 = 168671) (by norm_num)
theorem B449813 : Blo 299831 449813 := bbase (se 6 (by rfl) ⟨10542, by rfl⟩ : syracuseStep 449813 = 21085) (by norm_num)
theorem B449837 : Blo 299831 449837 := bbase (se 3 (by rfl) ⟨84344, by rfl⟩ : syracuseStep 449837 = 168689) (by norm_num)
theorem B679229 : Blo 299831 679229 := bbase (se 3 (by rfl) ⟨127355, by rfl⟩ : syracuseStep 679229 = 254711) (by norm_num)
theorem B449861 : Blo 299831 449861 := bbase (se 4 (by rfl) ⟨42174, by rfl⟩ : syracuseStep 449861 = 84349) (by norm_num)
theorem B449885 : Blo 299831 449885 := bbase (se 3 (by rfl) ⟨84353, by rfl⟩ : syracuseStep 449885 = 168707) (by norm_num)
theorem B384365 : Blo 299831 384365 := bbase (se 3 (by rfl) ⟨72068, by rfl⟩ : syracuseStep 384365 = 144137) (by norm_num)
theorem B449909 : Blo 299831 449909 := bbase (se 5 (by rfl) ⟨21089, by rfl⟩ : syracuseStep 449909 = 42179) (by norm_num)
theorem B679301 : Blo 299831 679301 := bbase (se 4 (by rfl) ⟨63684, by rfl⟩ : syracuseStep 679301 = 127369) (by norm_num)
theorem B449933 : Blo 299831 449933 := bbase (se 3 (by rfl) ⟨84362, by rfl⟩ : syracuseStep 449933 = 168725) (by norm_num)
theorem B449957 : Blo 299831 449957 := bbase (se 4 (by rfl) ⟨42183, by rfl⟩ : syracuseStep 449957 = 84367) (by norm_num)
theorem B384421 : Blo 299831 384421 := bbase (se 4 (by rfl) ⟨36039, by rfl⟩ : syracuseStep 384421 = 72079) (by norm_num)
theorem B449981 : Blo 299831 449981 := bbase (se 3 (by rfl) ⟨84371, by rfl⟩ : syracuseStep 449981 = 168743) (by norm_num)
theorem B679373 : Blo 299831 679373 := bbase (se 3 (by rfl) ⟨127382, by rfl⟩ : syracuseStep 679373 = 254765) (by norm_num)
theorem B450005 : Blo 299831 450005 := bbase (se 7 (by rfl) ⟨5273, by rfl⟩ : syracuseStep 450005 = 10547) (by norm_num)
theorem B450029 : Blo 299831 450029 := bbase (se 3 (by rfl) ⟨84380, by rfl⟩ : syracuseStep 450029 = 168761) (by norm_num)
theorem B450053 : Blo 299831 450053 := bbase (se 4 (by rfl) ⟨42192, by rfl⟩ : syracuseStep 450053 = 84385) (by norm_num)
theorem B384517 : Blo 299831 384517 := bbase (se 4 (by rfl) ⟨36048, by rfl⟩ : syracuseStep 384517 = 72097) (by norm_num)
theorem B679445 : Blo 299831 679445 := bbase (se 6 (by rfl) ⟨15924, by rfl⟩ : syracuseStep 679445 = 31849) (by norm_num)
theorem B450077 : Blo 299831 450077 := bbase (se 3 (by rfl) ⟨84389, by rfl⟩ : syracuseStep 450077 = 168779) (by norm_num)
theorem B450101 : Blo 299831 450101 := bbase (se 5 (by rfl) ⟨21098, by rfl⟩ : syracuseStep 450101 = 42197) (by norm_num)
theorem B450125 : Blo 299831 450125 := bbase (se 3 (by rfl) ⟨84398, by rfl⟩ : syracuseStep 450125 = 168797) (by norm_num)
theorem B679517 : Blo 299831 679517 := bbase (se 3 (by rfl) ⟨127409, by rfl⟩ : syracuseStep 679517 = 254819) (by norm_num)
theorem B450149 : Blo 299831 450149 := bbase (se 4 (by rfl) ⟨42201, by rfl⟩ : syracuseStep 450149 = 84403) (by norm_num)
theorem B2252405 : Blo 299831 2252405 := bbase (se 5 (by rfl) ⟨105581, by rfl⟩ : syracuseStep 2252405 = 211163) (by norm_num)
theorem B450173 : Blo 299831 450173 := bbase (se 3 (by rfl) ⟨84407, by rfl⟩ : syracuseStep 450173 = 168815) (by norm_num)
theorem B450197 : Blo 299831 450197 := bbase (se 6 (by rfl) ⟨10551, by rfl⟩ : syracuseStep 450197 = 21103) (by norm_num)
theorem B679589 : Blo 299831 679589 := bbase (se 4 (by rfl) ⟨63711, by rfl⟩ : syracuseStep 679589 = 127423) (by norm_num)
theorem B450221 : Blo 299831 450221 := bbase (se 3 (by rfl) ⟨84416, by rfl⟩ : syracuseStep 450221 = 168833) (by norm_num)
theorem B450245 : Blo 299831 450245 := bbase (se 4 (by rfl) ⟨42210, by rfl⟩ : syracuseStep 450245 = 84421) (by norm_num)
theorem B450269 : Blo 299831 450269 := bbase (se 3 (by rfl) ⟨84425, by rfl⟩ : syracuseStep 450269 = 168851) (by norm_num)
theorem B515813 : Blo 299831 515813 := bbase (se 4 (by rfl) ⟨48357, by rfl⟩ : syracuseStep 515813 = 96715) (by norm_num)
theorem B679661 : Blo 299831 679661 := bbase (se 3 (by rfl) ⟨127436, by rfl⟩ : syracuseStep 679661 = 254873) (by norm_num)
theorem B450293 : Blo 299831 450293 := bbase (se 5 (by rfl) ⟨21107, by rfl⟩ : syracuseStep 450293 = 42215) (by norm_num)
theorem B450317 : Blo 299831 450317 := bbase (se 3 (by rfl) ⟨84434, by rfl⟩ : syracuseStep 450317 = 168869) (by norm_num)
theorem B450341 : Blo 299831 450341 := bbase (se 4 (by rfl) ⟨42219, by rfl⟩ : syracuseStep 450341 = 84439) (by norm_num)
theorem B679733 : Blo 299831 679733 := bbase (se 5 (by rfl) ⟨31862, by rfl⟩ : syracuseStep 679733 = 63725) (by norm_num)
theorem B450365 : Blo 299831 450365 := bbase (se 3 (by rfl) ⟨84443, by rfl⟩ : syracuseStep 450365 = 168887) (by norm_num)
theorem B450389 : Blo 299831 450389 := bbase (se 9 (by rfl) ⟨1319, by rfl⟩ : syracuseStep 450389 = 2639) (by norm_num)
theorem B450413 : Blo 299831 450413 := bbase (se 3 (by rfl) ⟨84452, by rfl⟩ : syracuseStep 450413 = 168905) (by norm_num)
theorem B679805 : Blo 299831 679805 := bbase (se 3 (by rfl) ⟨127463, by rfl⟩ : syracuseStep 679805 = 254927) (by norm_num)
theorem B450437 : Blo 299831 450437 := bbase (se 4 (by rfl) ⟨42228, by rfl⟩ : syracuseStep 450437 = 84457) (by norm_num)
theorem B647045 : Blo 299831 647045 := bbase (se 4 (by rfl) ⟨60660, by rfl⟩ : syracuseStep 647045 = 121321) (by norm_num)
theorem B483221 : Blo 299831 483221 := bbase (se 6 (by rfl) ⟨11325, by rfl⟩ : syracuseStep 483221 = 22651) (by norm_num)
theorem B778133 : Blo 299831 778133 := bbase (se 6 (by rfl) ⟨18237, by rfl⟩ : syracuseStep 778133 = 36475) (by norm_num)
theorem B450461 : Blo 299831 450461 := bbase (se 3 (by rfl) ⟨84461, by rfl⟩ : syracuseStep 450461 = 168923) (by norm_num)
theorem B810917 : Blo 299831 810917 := bbase (se 4 (by rfl) ⟨76023, by rfl⟩ : syracuseStep 810917 = 152047) (by norm_num)
theorem B450485 : Blo 299831 450485 := bbase (se 5 (by rfl) ⟨21116, by rfl⟩ : syracuseStep 450485 = 42233) (by norm_num)
theorem B679877 : Blo 299831 679877 := bbase (se 4 (by rfl) ⟨63738, by rfl⟩ : syracuseStep 679877 = 127477) (by norm_num)
theorem B450509 : Blo 299831 450509 := bbase (se 3 (by rfl) ⟨84470, by rfl⟩ : syracuseStep 450509 = 168941) (by norm_num)
theorem B450533 : Blo 299831 450533 := bbase (se 4 (by rfl) ⟨42237, by rfl⟩ : syracuseStep 450533 = 84475) (by norm_num)
theorem B647165 : Blo 299831 647165 := bbase (se 3 (by rfl) ⟨121343, by rfl⟩ : syracuseStep 647165 = 242687) (by norm_num)
theorem B450557 : Blo 299831 450557 := bbase (se 3 (by rfl) ⟨84479, by rfl⟩ : syracuseStep 450557 = 168959) (by norm_num)
theorem B679949 : Blo 299831 679949 := bbase (se 3 (by rfl) ⟨127490, by rfl⟩ : syracuseStep 679949 = 254981) (by norm_num)
theorem B450581 : Blo 299831 450581 := bbase (se 6 (by rfl) ⟨10560, by rfl⟩ : syracuseStep 450581 = 21121) (by norm_num)
theorem B450605 : Blo 299831 450605 := bbase (se 3 (by rfl) ⟨84488, by rfl⟩ : syracuseStep 450605 = 168977) (by norm_num)
theorem B450629 : Blo 299831 450629 := bbase (se 4 (by rfl) ⟨42246, by rfl⟩ : syracuseStep 450629 = 84493) (by norm_num)
theorem B680021 : Blo 299831 680021 := bbase (se 8 (by rfl) ⟨3984, by rfl⟩ : syracuseStep 680021 = 7969) (by norm_num)
theorem B450653 : Blo 299831 450653 := bbase (se 3 (by rfl) ⟨84497, by rfl⟩ : syracuseStep 450653 = 168995) (by norm_num)
theorem B778349 : Blo 299831 778349 := bbase (se 3 (by rfl) ⟨145940, by rfl⟩ : syracuseStep 778349 = 291881) (by norm_num)
theorem B1138805 : Blo 299831 1138805 := bbase (se 5 (by rfl) ⟨53381, by rfl⟩ : syracuseStep 1138805 = 106763) (by norm_num)
theorem B450677 : Blo 299831 450677 := bbase (se 5 (by rfl) ⟨21125, by rfl⟩ : syracuseStep 450677 = 42251) (by norm_num)
theorem B450701 : Blo 299831 450701 := bbase (se 3 (by rfl) ⟨84506, by rfl⟩ : syracuseStep 450701 = 169013) (by norm_num)
theorem B680093 : Blo 299831 680093 := bbase (se 3 (by rfl) ⟨127517, by rfl⟩ : syracuseStep 680093 = 255035) (by norm_num)
theorem B450725 : Blo 299831 450725 := bbase (se 4 (by rfl) ⟨42255, by rfl⟩ : syracuseStep 450725 = 84511) (by norm_num)
theorem B450749 : Blo 299831 450749 := bbase (se 3 (by rfl) ⟨84515, by rfl⟩ : syracuseStep 450749 = 169031) (by norm_num)
theorem B385217 : Blo 299831 385217 := bbase (se 2 (by rfl) ⟨144456, by rfl⟩ : syracuseStep 385217 = 288913) (by norm_num)
theorem B450773 : Blo 299831 450773 := bbase (se 7 (by rfl) ⟨5282, by rfl⟩ : syracuseStep 450773 = 10565) (by norm_num)
theorem B680165 : Blo 299831 680165 := bbase (se 4 (by rfl) ⟨63765, by rfl⟩ : syracuseStep 680165 = 127531) (by norm_num)
theorem B450797 : Blo 299831 450797 := bbase (se 3 (by rfl) ⟨84524, by rfl⟩ : syracuseStep 450797 = 169049) (by norm_num)
theorem B450821 : Blo 299831 450821 := bbase (se 4 (by rfl) ⟨42264, by rfl⟩ : syracuseStep 450821 = 84529) (by norm_num)
theorem B450845 : Blo 299831 450845 := bbase (se 3 (by rfl) ⟨84533, by rfl⟩ : syracuseStep 450845 = 169067) (by norm_num)
theorem B680237 : Blo 299831 680237 := bbase (se 3 (by rfl) ⟨127544, by rfl⟩ : syracuseStep 680237 = 255089) (by norm_num)
theorem B450869 : Blo 299831 450869 := bbase (se 5 (by rfl) ⟨21134, by rfl⟩ : syracuseStep 450869 = 42269) (by norm_num)
theorem B450893 : Blo 299831 450893 := bbase (se 3 (by rfl) ⟨84542, by rfl⟩ : syracuseStep 450893 = 169085) (by norm_num)
theorem B450917 : Blo 299831 450917 := bbase (se 4 (by rfl) ⟨42273, by rfl⟩ : syracuseStep 450917 = 84547) (by norm_num)
theorem B680309 : Blo 299831 680309 := bbase (se 5 (by rfl) ⟨31889, by rfl⟩ : syracuseStep 680309 = 63779) (by norm_num)
theorem B450941 : Blo 299831 450941 := bbase (se 3 (by rfl) ⟨84551, by rfl⟩ : syracuseStep 450941 = 169103) (by norm_num)
theorem B1139093 : Blo 299831 1139093 := bbase (se 6 (by rfl) ⟨26697, by rfl⟩ : syracuseStep 1139093 = 53395) (by norm_num)
theorem B450965 : Blo 299831 450965 := bbase (se 6 (by rfl) ⟨10569, by rfl⟩ : syracuseStep 450965 = 21139) (by norm_num)
theorem B450989 : Blo 299831 450989 := bbase (se 3 (by rfl) ⟨84560, by rfl⟩ : syracuseStep 450989 = 169121) (by norm_num)
theorem B680381 : Blo 299831 680381 := bbase (se 3 (by rfl) ⟨127571, by rfl⟩ : syracuseStep 680381 = 255143) (by norm_num)
theorem B451013 : Blo 299831 451013 := bbase (se 4 (by rfl) ⟨42282, by rfl⟩ : syracuseStep 451013 = 84565) (by norm_num)
theorem B1532357 : Blo 299831 1532357 := bbase (se 4 (by rfl) ⟨143658, by rfl⟩ : syracuseStep 1532357 = 287317) (by norm_num)
theorem B451037 : Blo 299831 451037 := bbase (se 3 (by rfl) ⟨84569, by rfl⟩ : syracuseStep 451037 = 169139) (by norm_num)
theorem B451061 : Blo 299831 451061 := bbase (se 5 (by rfl) ⟨21143, by rfl⟩ : syracuseStep 451061 = 42287) (by norm_num)
theorem B680453 : Blo 299831 680453 := bbase (se 4 (by rfl) ⟨63792, by rfl⟩ : syracuseStep 680453 = 127585) (by norm_num)
theorem B451085 : Blo 299831 451085 := bbase (se 3 (by rfl) ⟨84578, by rfl⟩ : syracuseStep 451085 = 169157) (by norm_num)
theorem B483869 : Blo 299831 483869 := bbase (se 3 (by rfl) ⟨90725, by rfl⟩ : syracuseStep 483869 = 181451) (by norm_num)
theorem B451109 : Blo 299831 451109 := bbase (se 4 (by rfl) ⟨42291, by rfl⟩ : syracuseStep 451109 = 84583) (by norm_num)
theorem B451133 : Blo 299831 451133 := bbase (se 3 (by rfl) ⟨84587, by rfl⟩ : syracuseStep 451133 = 169175) (by norm_num)
theorem B680525 : Blo 299831 680525 := bbase (se 3 (by rfl) ⟨127598, by rfl⟩ : syracuseStep 680525 = 255197) (by norm_num)
theorem B451157 : Blo 299831 451157 := bbase (se 8 (by rfl) ⟨2643, by rfl⟩ : syracuseStep 451157 = 5287) (by norm_num)
theorem B451181 : Blo 299831 451181 := bbase (se 3 (by rfl) ⟨84596, by rfl⟩ : syracuseStep 451181 = 169193) (by norm_num)
theorem B647797 : Blo 299831 647797 := bbase (se 5 (by rfl) ⟨30365, by rfl⟩ : syracuseStep 647797 = 60731) (by norm_num)
theorem B451205 : Blo 299831 451205 := bbase (se 4 (by rfl) ⟨42300, by rfl⟩ : syracuseStep 451205 = 84601) (by norm_num)
theorem B680597 : Blo 299831 680597 := bbase (se 6 (by rfl) ⟨15951, by rfl⟩ : syracuseStep 680597 = 31903) (by norm_num)
theorem B451229 : Blo 299831 451229 := bbase (se 3 (by rfl) ⟨84605, by rfl⟩ : syracuseStep 451229 = 169211) (by norm_num)
theorem B451253 : Blo 299831 451253 := bbase (se 5 (by rfl) ⟨21152, by rfl⟩ : syracuseStep 451253 = 42305) (by norm_num)
theorem B451277 : Blo 299831 451277 := bbase (se 3 (by rfl) ⟨84614, by rfl⟩ : syracuseStep 451277 = 169229) (by norm_num)
theorem B320221 : Blo 299831 320221 := bbase (se 3 (by rfl) ⟨60041, by rfl⟩ : syracuseStep 320221 = 120083) (by norm_num)
theorem B680669 : Blo 299831 680669 := bbase (se 3 (by rfl) ⟨127625, by rfl⟩ : syracuseStep 680669 = 255251) (by norm_num)
theorem B451301 : Blo 299831 451301 := bbase (se 4 (by rfl) ⟨42309, by rfl⟩ : syracuseStep 451301 = 84619) (by norm_num)
theorem B451325 : Blo 299831 451325 := bbase (se 3 (by rfl) ⟨84623, by rfl⟩ : syracuseStep 451325 = 169247) (by norm_num)
theorem B451349 : Blo 299831 451349 := bbase (se 6 (by rfl) ⟨10578, by rfl⟩ : syracuseStep 451349 = 21157) (by norm_num)
theorem B320293 : Blo 299831 320293 := bbase (se 4 (by rfl) ⟨30027, by rfl⟩ : syracuseStep 320293 = 60055) (by norm_num)
theorem B680741 : Blo 299831 680741 := bbase (se 4 (by rfl) ⟨63819, by rfl⟩ : syracuseStep 680741 = 127639) (by norm_num)
theorem B451373 : Blo 299831 451373 := bbase (se 3 (by rfl) ⟨84632, by rfl⟩ : syracuseStep 451373 = 169265) (by norm_num)
theorem B451397 : Blo 299831 451397 := bbase (se 4 (by rfl) ⟨42318, by rfl⟩ : syracuseStep 451397 = 84637) (by norm_num)
theorem B451421 : Blo 299831 451421 := bbase (se 3 (by rfl) ⟨84641, by rfl⟩ : syracuseStep 451421 = 169283) (by norm_num)
theorem B680813 : Blo 299831 680813 := bbase (se 3 (by rfl) ⟨127652, by rfl⟩ : syracuseStep 680813 = 255305) (by norm_num)
theorem B451445 : Blo 299831 451445 := bbase (se 5 (by rfl) ⟨21161, by rfl⟩ : syracuseStep 451445 = 42323) (by norm_num)
theorem B549757 : Blo 299831 549757 := bbase (se 3 (by rfl) ⟨103079, by rfl⟩ : syracuseStep 549757 = 206159) (by norm_num)
theorem B451469 : Blo 299831 451469 := bbase (se 3 (by rfl) ⟨84650, by rfl⟩ : syracuseStep 451469 = 169301) (by norm_num)
theorem B451493 : Blo 299831 451493 := bbase (se 4 (by rfl) ⟨42327, by rfl⟩ : syracuseStep 451493 = 84655) (by norm_num)
theorem B517045 : Blo 299831 517045 := bbase (se 5 (by rfl) ⟨24236, by rfl⟩ : syracuseStep 517045 = 48473) (by norm_num)
theorem B680885 : Blo 299831 680885 := bbase (se 5 (by rfl) ⟨31916, by rfl⟩ : syracuseStep 680885 = 63833) (by norm_num)
theorem B451517 : Blo 299831 451517 := bbase (se 3 (by rfl) ⟨84659, by rfl⟩ : syracuseStep 451517 = 169319) (by norm_num)
theorem B451541 : Blo 299831 451541 := bbase (se 7 (by rfl) ⟨5291, by rfl⟩ : syracuseStep 451541 = 10583) (by norm_num)
theorem B320473 : Blo 299831 320473 := bbase (se 2 (by rfl) ⟨120177, by rfl⟩ : syracuseStep 320473 = 240355) (by norm_num)
theorem B451565 : Blo 299831 451565 := bbase (se 3 (by rfl) ⟨84668, by rfl⟩ : syracuseStep 451565 = 169337) (by norm_num)
theorem B680957 : Blo 299831 680957 := bbase (se 3 (by rfl) ⟨127679, by rfl⟩ : syracuseStep 680957 = 255359) (by norm_num)
theorem B451589 : Blo 299831 451589 := bbase (se 4 (by rfl) ⟨42336, by rfl⟩ : syracuseStep 451589 = 84673) (by norm_num)
theorem B582661 : Blo 299831 582661 := bbase (se 4 (by rfl) ⟨54624, by rfl⟩ : syracuseStep 582661 = 109249) (by norm_num)
theorem B451613 : Blo 299831 451613 := bbase (se 3 (by rfl) ⟨84677, by rfl⟩ : syracuseStep 451613 = 169355) (by norm_num)
theorem B451637 : Blo 299831 451637 := bbase (se 5 (by rfl) ⟨21170, by rfl⟩ : syracuseStep 451637 = 42341) (by norm_num)
theorem B615485 : Blo 299831 615485 := bbase (se 3 (by rfl) ⟨115403, by rfl⟩ : syracuseStep 615485 = 230807) (by norm_num)
theorem B681029 : Blo 299831 681029 := bbase (se 4 (by rfl) ⟨63846, by rfl⟩ : syracuseStep 681029 = 127693) (by norm_num)
theorem B451661 : Blo 299831 451661 := bbase (se 3 (by rfl) ⟨84686, by rfl⟩ : syracuseStep 451661 = 169373) (by norm_num)
theorem B451685 : Blo 299831 451685 := bbase (se 4 (by rfl) ⟨42345, by rfl⟩ : syracuseStep 451685 = 84691) (by norm_num)
theorem B451709 : Blo 299831 451709 := bbase (se 3 (by rfl) ⟨84695, by rfl⟩ : syracuseStep 451709 = 169391) (by norm_num)
theorem B681101 : Blo 299831 681101 := bbase (se 3 (by rfl) ⟨127706, by rfl⟩ : syracuseStep 681101 = 255413) (by norm_num)
theorem B451733 : Blo 299831 451733 := bbase (se 6 (by rfl) ⟨10587, by rfl⟩ : syracuseStep 451733 = 21175) (by norm_num)
theorem B451757 : Blo 299831 451757 := bbase (se 3 (by rfl) ⟨84704, by rfl⟩ : syracuseStep 451757 = 169409) (by norm_num)
theorem B451781 : Blo 299831 451781 := bbase (se 4 (by rfl) ⟨42354, by rfl⟩ : syracuseStep 451781 = 84709) (by norm_num)
theorem B681173 : Blo 299831 681173 := bbase (se 7 (by rfl) ⟨7982, by rfl⟩ : syracuseStep 681173 = 15965) (by norm_num)
theorem B451805 : Blo 299831 451805 := bbase (se 3 (by rfl) ⟨84713, by rfl⟩ : syracuseStep 451805 = 169427) (by norm_num)
theorem B451829 : Blo 299831 451829 := bbase (se 5 (by rfl) ⟨21179, by rfl⟩ : syracuseStep 451829 = 42359) (by norm_num)
theorem B1729781 : Blo 299831 1729781 := bbase (se 5 (by rfl) ⟨81083, by rfl⟩ : syracuseStep 1729781 = 162167) (by norm_num)
theorem B451853 : Blo 299831 451853 := bbase (se 3 (by rfl) ⟨84722, by rfl⟩ : syracuseStep 451853 = 169445) (by norm_num)
theorem B681245 : Blo 299831 681245 := bbase (se 3 (by rfl) ⟨127733, by rfl⟩ : syracuseStep 681245 = 255467) (by norm_num)
theorem B451877 : Blo 299831 451877 := bbase (se 4 (by rfl) ⟨42363, by rfl⟩ : syracuseStep 451877 = 84727) (by norm_num)
theorem B451901 : Blo 299831 451901 := bbase (se 3 (by rfl) ⟨84731, by rfl⟩ : syracuseStep 451901 = 169463) (by norm_num)
theorem B1402181 : Blo 299831 1402181 := bbase (se 4 (by rfl) ⟨131454, by rfl⟩ : syracuseStep 1402181 = 262909) (by norm_num)
theorem B451925 : Blo 299831 451925 := bbase (se 12 (by rfl) ⟨165, by rfl⟩ : syracuseStep 451925 = 331) (by norm_num)
theorem B681317 : Blo 299831 681317 := bbase (se 4 (by rfl) ⟨63873, by rfl⟩ : syracuseStep 681317 = 127747) (by norm_num)
theorem B451949 : Blo 299831 451949 := bbase (se 3 (by rfl) ⟨84740, by rfl⟩ : syracuseStep 451949 = 169481) (by norm_num)
theorem B1631605 : Blo 299831 1631605 := bbase (se 5 (by rfl) ⟨76481, by rfl⟩ : syracuseStep 1631605 = 152963) (by norm_num)
theorem B451973 : Blo 299831 451973 := bbase (se 4 (by rfl) ⟨42372, by rfl⟩ : syracuseStep 451973 = 84745) (by norm_num)
theorem B320917 : Blo 299831 320917 := bbase (se 6 (by rfl) ⟨7521, by rfl⟩ : syracuseStep 320917 = 15043) (by norm_num)
theorem B451997 : Blo 299831 451997 := bbase (se 3 (by rfl) ⟨84749, by rfl⟩ : syracuseStep 451997 = 169499) (by norm_num)
theorem B681389 : Blo 299831 681389 := bbase (se 3 (by rfl) ⟨127760, by rfl⟩ : syracuseStep 681389 = 255521) (by norm_num)
theorem B452021 : Blo 299831 452021 := bbase (se 5 (by rfl) ⟨21188, by rfl⟩ : syracuseStep 452021 = 42377) (by norm_num)
theorem B517565 : Blo 299831 517565 := bbase (se 3 (by rfl) ⟨97043, by rfl⟩ : syracuseStep 517565 = 194087) (by norm_num)
theorem B452045 : Blo 299831 452045 := bbase (se 3 (by rfl) ⟨84758, by rfl⟩ : syracuseStep 452045 = 169517) (by norm_num)
theorem B452069 : Blo 299831 452069 := bbase (se 4 (by rfl) ⟨42381, by rfl⟩ : syracuseStep 452069 = 84763) (by norm_num)
theorem B648685 : Blo 299831 648685 := bbase (se 3 (by rfl) ⟨121628, by rfl⟩ : syracuseStep 648685 = 243257) (by norm_num)
theorem B681461 : Blo 299831 681461 := bbase (se 5 (by rfl) ⟨31943, by rfl⟩ : syracuseStep 681461 = 63887) (by norm_num)
theorem B452093 : Blo 299831 452093 := bbase (se 3 (by rfl) ⟨84767, by rfl⟩ : syracuseStep 452093 = 169535) (by norm_num)
theorem B484861 : Blo 299831 484861 := bbase (se 3 (by rfl) ⟨90911, by rfl⟩ : syracuseStep 484861 = 181823) (by norm_num)
theorem B321041 : Blo 299831 321041 := bbase (se 2 (by rfl) ⟨120390, by rfl⟩ : syracuseStep 321041 = 240781) (by norm_num)
theorem B452117 : Blo 299831 452117 := bbase (se 6 (by rfl) ⟨10596, by rfl⟩ : syracuseStep 452117 = 21193) (by norm_num)
theorem B452141 : Blo 299831 452141 := bbase (se 3 (by rfl) ⟨84776, by rfl⟩ : syracuseStep 452141 = 169553) (by norm_num)
theorem B1140277 : Blo 299831 1140277 := bbase (se 5 (by rfl) ⟨53450, by rfl⟩ : syracuseStep 1140277 = 106901) (by norm_num)
theorem B2188853 : Blo 299831 2188853 := bbase (se 5 (by rfl) ⟨102602, by rfl⟩ : syracuseStep 2188853 = 205205) (by norm_num)
theorem B681533 : Blo 299831 681533 := bbase (se 3 (by rfl) ⟨127787, by rfl⟩ : syracuseStep 681533 = 255575) (by norm_num)
theorem B452165 : Blo 299831 452165 := bbase (se 4 (by rfl) ⟨42390, by rfl⟩ : syracuseStep 452165 = 84781) (by norm_num)
theorem B452189 : Blo 299831 452189 := bbase (se 3 (by rfl) ⟨84785, by rfl⟩ : syracuseStep 452189 = 169571) (by norm_num)
theorem B648805 : Blo 299831 648805 := bbase (se 4 (by rfl) ⟨60825, by rfl⟩ : syracuseStep 648805 = 121651) (by norm_num)
theorem B452213 : Blo 299831 452213 := bbase (se 5 (by rfl) ⟨21197, by rfl⟩ : syracuseStep 452213 = 42395) (by norm_num)
theorem B681605 : Blo 299831 681605 := bbase (se 4 (by rfl) ⟨63900, by rfl⟩ : syracuseStep 681605 = 127801) (by norm_num)
theorem B452237 : Blo 299831 452237 := bbase (se 3 (by rfl) ⟨84794, by rfl⟩ : syracuseStep 452237 = 169589) (by norm_num)
theorem B452261 : Blo 299831 452261 := bbase (se 4 (by rfl) ⟨42399, by rfl⟩ : syracuseStep 452261 = 84799) (by norm_num)
theorem B452285 : Blo 299831 452285 := bbase (se 3 (by rfl) ⟨84803, by rfl⟩ : syracuseStep 452285 = 169607) (by norm_num)
theorem B681677 : Blo 299831 681677 := bbase (se 3 (by rfl) ⟨127814, by rfl⟩ : syracuseStep 681677 = 255629) (by norm_num)
theorem B452309 : Blo 299831 452309 := bbase (se 7 (by rfl) ⟨5300, by rfl⟩ : syracuseStep 452309 = 10601) (by norm_num)
theorem B1533653 : Blo 299831 1533653 := bbase (se 7 (by rfl) ⟨17972, by rfl⟩ : syracuseStep 1533653 = 35945) (by norm_num)
theorem B452333 : Blo 299831 452333 := bbase (se 3 (by rfl) ⟨84812, by rfl⟩ : syracuseStep 452333 = 169625) (by norm_num)
theorem B452357 : Blo 299831 452357 := bbase (se 4 (by rfl) ⟨42408, by rfl⟩ : syracuseStep 452357 = 84817) (by norm_num)
theorem B321293 : Blo 299831 321293 := bbase (se 3 (by rfl) ⟨60242, by rfl⟩ : syracuseStep 321293 = 120485) (by norm_num)
theorem B681749 : Blo 299831 681749 := bbase (se 6 (by rfl) ⟨15978, by rfl⟩ : syracuseStep 681749 = 31957) (by norm_num)
theorem B452381 : Blo 299831 452381 := bbase (se 3 (by rfl) ⟨84821, by rfl⟩ : syracuseStep 452381 = 169643) (by norm_num)
theorem B452405 : Blo 299831 452405 := bbase (se 5 (by rfl) ⟨21206, by rfl⟩ : syracuseStep 452405 = 42413) (by norm_num)
theorem B452429 : Blo 299831 452429 := bbase (se 3 (by rfl) ⟨84830, by rfl⟩ : syracuseStep 452429 = 169661) (by norm_num)
theorem B681821 : Blo 299831 681821 := bbase (se 3 (by rfl) ⟨127841, by rfl⟩ : syracuseStep 681821 = 255683) (by norm_num)
theorem B1140581 : Blo 299831 1140581 := bbase (se 4 (by rfl) ⟨106929, by rfl⟩ : syracuseStep 1140581 = 213859) (by norm_num)
theorem B452453 : Blo 299831 452453 := bbase (se 4 (by rfl) ⟨42417, by rfl⟩ : syracuseStep 452453 = 84835) (by norm_num)
theorem B452477 : Blo 299831 452477 := bbase (se 3 (by rfl) ⟨84839, by rfl⟩ : syracuseStep 452477 = 169679) (by norm_num)
theorem B452501 : Blo 299831 452501 := bbase (se 6 (by rfl) ⟨10605, by rfl⟩ : syracuseStep 452501 = 21211) (by norm_num)
theorem B681893 : Blo 299831 681893 := bbase (se 4 (by rfl) ⟨63927, by rfl⟩ : syracuseStep 681893 = 127855) (by norm_num)
theorem B452525 : Blo 299831 452525 := bbase (se 3 (by rfl) ⟨84848, by rfl⟩ : syracuseStep 452525 = 169697) (by norm_num)
theorem B485309 : Blo 299831 485309 := bbase (se 3 (by rfl) ⟨90995, by rfl⟩ : syracuseStep 485309 = 181991) (by norm_num)
theorem B452549 : Blo 299831 452549 := bbase (se 4 (by rfl) ⟨42426, by rfl⟩ : syracuseStep 452549 = 84853) (by norm_num)
theorem B452573 : Blo 299831 452573 := bbase (se 3 (by rfl) ⟨84857, by rfl⟩ : syracuseStep 452573 = 169715) (by norm_num)
theorem B681965 : Blo 299831 681965 := bbase (se 3 (by rfl) ⟨127868, by rfl⟩ : syracuseStep 681965 = 255737) (by norm_num)
theorem B452597 : Blo 299831 452597 := bbase (se 5 (by rfl) ⟨21215, by rfl⟩ : syracuseStep 452597 = 42431) (by norm_num)
theorem B452621 : Blo 299831 452621 := bbase (se 3 (by rfl) ⟨84866, by rfl⟩ : syracuseStep 452621 = 169733) (by norm_num)
theorem B1304597 : Blo 299831 1304597 := bbase (se 6 (by rfl) ⟨30576, by rfl⟩ : syracuseStep 1304597 = 61153) (by norm_num)
theorem B452645 : Blo 299831 452645 := bbase (se 4 (by rfl) ⟨42435, by rfl⟩ : syracuseStep 452645 = 84871) (by norm_num)
theorem B682037 : Blo 299831 682037 := bbase (se 5 (by rfl) ⟨31970, by rfl⟩ : syracuseStep 682037 = 63941) (by norm_num)
theorem B452669 : Blo 299831 452669 := bbase (se 3 (by rfl) ⟨84875, by rfl⟩ : syracuseStep 452669 = 169751) (by norm_num)
theorem B452693 : Blo 299831 452693 := bbase (se 8 (by rfl) ⟨2652, by rfl⟩ : syracuseStep 452693 = 5305) (by norm_num)
theorem B452717 : Blo 299831 452717 := bbase (se 3 (by rfl) ⟨84884, by rfl⟩ : syracuseStep 452717 = 169769) (by norm_num)
theorem B682109 : Blo 299831 682109 := bbase (se 3 (by rfl) ⟨127895, by rfl⟩ : syracuseStep 682109 = 255791) (by norm_num)
theorem B452741 : Blo 299831 452741 := bbase (se 4 (by rfl) ⟨42444, by rfl⟩ : syracuseStep 452741 = 84889) (by norm_num)
theorem B485509 : Blo 299831 485509 := bbase (se 4 (by rfl) ⟨45516, by rfl⟩ : syracuseStep 485509 = 91033) (by norm_num)
theorem B452765 : Blo 299831 452765 := bbase (se 3 (by rfl) ⟨84893, by rfl⟩ : syracuseStep 452765 = 169787) (by norm_num)
theorem B649397 : Blo 299831 649397 := bbase (se 5 (by rfl) ⟨30440, by rfl⟩ : syracuseStep 649397 = 60881) (by norm_num)
theorem B452789 : Blo 299831 452789 := bbase (se 5 (by rfl) ⟨21224, by rfl⟩ : syracuseStep 452789 = 42449) (by norm_num)
theorem B682181 : Blo 299831 682181 := bbase (se 4 (by rfl) ⟨63954, by rfl⟩ : syracuseStep 682181 = 127909) (by norm_num)
theorem B321737 : Blo 299831 321737 := bbase (se 2 (by rfl) ⟨120651, by rfl⟩ : syracuseStep 321737 = 241303) (by norm_num)
theorem B452813 : Blo 299831 452813 := bbase (se 3 (by rfl) ⟨84902, by rfl⟩ : syracuseStep 452813 = 169805) (by norm_num)
theorem B452837 : Blo 299831 452837 := bbase (se 4 (by rfl) ⟨42453, by rfl⟩ : syracuseStep 452837 = 84907) (by norm_num)
theorem B452861 : Blo 299831 452861 := bbase (se 3 (by rfl) ⟨84911, by rfl⟩ : syracuseStep 452861 = 169823) (by norm_num)
theorem B682253 : Blo 299831 682253 := bbase (se 3 (by rfl) ⟨127922, by rfl⟩ : syracuseStep 682253 = 255845) (by norm_num)
theorem B452885 : Blo 299831 452885 := bbase (se 6 (by rfl) ⟨10614, by rfl⟩ : syracuseStep 452885 = 21229) (by norm_num)
theorem B452909 : Blo 299831 452909 := bbase (se 3 (by rfl) ⟨84920, by rfl⟩ : syracuseStep 452909 = 169841) (by norm_num)
theorem B452933 : Blo 299831 452933 := bbase (se 4 (by rfl) ⟨42462, by rfl⟩ : syracuseStep 452933 = 84925) (by norm_num)
theorem B4811093 : Blo 299831 4811093 := bbase (se 10 (by rfl) ⟨7047, by rfl⟩ : syracuseStep 4811093 = 14095) (by norm_num)
theorem B682325 : Blo 299831 682325 := bbase (se 10 (by rfl) ⟨999, by rfl⟩ : syracuseStep 682325 = 1999) (by norm_num)
theorem B452957 : Blo 299831 452957 := bbase (se 3 (by rfl) ⟨84929, by rfl⟩ : syracuseStep 452957 = 169859) (by norm_num)
theorem B452981 : Blo 299831 452981 := bbase (se 5 (by rfl) ⟨21233, by rfl⟩ : syracuseStep 452981 = 42467) (by norm_num)
theorem B485765 : Blo 299831 485765 := bbase (se 4 (by rfl) ⟨45540, by rfl⟩ : syracuseStep 485765 = 91081) (by norm_num)
theorem B453005 : Blo 299831 453005 := bbase (se 3 (by rfl) ⟨84938, by rfl⟩ : syracuseStep 453005 = 169877) (by norm_num)
theorem B682397 : Blo 299831 682397 := bbase (se 3 (by rfl) ⟨127949, by rfl⟩ : syracuseStep 682397 = 255899) (by norm_num)
theorem B453029 : Blo 299831 453029 := bbase (se 4 (by rfl) ⟨42471, by rfl⟩ : syracuseStep 453029 = 84943) (by norm_num)
theorem B453053 : Blo 299831 453053 := bbase (se 3 (by rfl) ⟨84947, by rfl⟩ : syracuseStep 453053 = 169895) (by norm_num)
theorem B321985 : Blo 299831 321985 := bbase (se 2 (by rfl) ⟨120744, by rfl⟩ : syracuseStep 321985 = 241489) (by norm_num)
theorem B453077 : Blo 299831 453077 := bbase (se 7 (by rfl) ⟨5309, by rfl⟩ : syracuseStep 453077 = 10619) (by norm_num)
theorem B682469 : Blo 299831 682469 := bbase (se 4 (by rfl) ⟨63981, by rfl⟩ : syracuseStep 682469 = 127963) (by norm_num)
theorem B453101 : Blo 299831 453101 := bbase (se 3 (by rfl) ⟨84956, by rfl⟩ : syracuseStep 453101 = 169913) (by norm_num)
theorem B453125 : Blo 299831 453125 := bbase (se 4 (by rfl) ⟨42480, by rfl⟩ : syracuseStep 453125 = 84961) (by norm_num)
theorem B453149 : Blo 299831 453149 := bbase (se 3 (by rfl) ⟨84965, by rfl⟩ : syracuseStep 453149 = 169931) (by norm_num)
theorem B682541 : Blo 299831 682541 := bbase (se 3 (by rfl) ⟨127976, by rfl⟩ : syracuseStep 682541 = 255953) (by norm_num)
theorem B453173 : Blo 299831 453173 := bbase (se 5 (by rfl) ⟨21242, by rfl⟩ : syracuseStep 453173 = 42485) (by norm_num)
theorem B453197 : Blo 299831 453197 := bbase (se 3 (by rfl) ⟨84974, by rfl⟩ : syracuseStep 453197 = 169949) (by norm_num)
theorem B453221 : Blo 299831 453221 := bbase (se 4 (by rfl) ⟨42489, by rfl⟩ : syracuseStep 453221 = 84979) (by norm_num)
theorem B813685 : Blo 299831 813685 := bbase (se 5 (by rfl) ⟨38141, by rfl⟩ : syracuseStep 813685 = 76283) (by norm_num)
theorem B682613 : Blo 299831 682613 := bbase (se 5 (by rfl) ⟨31997, by rfl⟩ : syracuseStep 682613 = 63995) (by norm_num)
theorem B453245 : Blo 299831 453245 := bbase (se 3 (by rfl) ⟨84983, by rfl⟩ : syracuseStep 453245 = 169967) (by norm_num)
theorem B453269 : Blo 299831 453269 := bbase (se 6 (by rfl) ⟨10623, by rfl⟩ : syracuseStep 453269 = 21247) (by norm_num)
theorem B453293 : Blo 299831 453293 := bbase (se 3 (by rfl) ⟨84992, by rfl⟩ : syracuseStep 453293 = 169985) (by norm_num)
theorem B682685 : Blo 299831 682685 := bbase (se 3 (by rfl) ⟨128003, by rfl⟩ : syracuseStep 682685 = 256007) (by norm_num)
theorem B453317 : Blo 299831 453317 := bbase (se 4 (by rfl) ⟨42498, by rfl⟩ : syracuseStep 453317 = 84997) (by norm_num)
theorem B453341 : Blo 299831 453341 := bbase (se 3 (by rfl) ⟨85001, by rfl⟩ : syracuseStep 453341 = 170003) (by norm_num)
theorem B453365 : Blo 299831 453365 := bbase (se 5 (by rfl) ⟨21251, by rfl⟩ : syracuseStep 453365 = 42503) (by norm_num)
theorem B682757 : Blo 299831 682757 := bbase (se 4 (by rfl) ⟨64008, by rfl⟩ : syracuseStep 682757 = 128017) (by norm_num)
theorem B453389 : Blo 299831 453389 := bbase (se 3 (by rfl) ⟨85010, by rfl⟩ : syracuseStep 453389 = 170021) (by norm_num)
theorem B453413 : Blo 299831 453413 := bbase (se 4 (by rfl) ⟨42507, by rfl⟩ : syracuseStep 453413 = 85015) (by norm_num)
theorem B453437 : Blo 299831 453437 := bbase (se 3 (by rfl) ⟨85019, by rfl⟩ : syracuseStep 453437 = 170039) (by norm_num)
theorem B682829 : Blo 299831 682829 := bbase (se 3 (by rfl) ⟨128030, by rfl⟩ : syracuseStep 682829 = 256061) (by norm_num)
theorem B453461 : Blo 299831 453461 := bbase (se 9 (by rfl) ⟨1328, by rfl⟩ : syracuseStep 453461 = 2657) (by norm_num)
theorem B453485 : Blo 299831 453485 := bbase (se 3 (by rfl) ⟨85028, by rfl⟩ : syracuseStep 453485 = 170057) (by norm_num)
theorem B322429 : Blo 299831 322429 := bbase (se 3 (by rfl) ⟨60455, by rfl⟩ : syracuseStep 322429 = 120911) (by norm_num)
theorem B453509 : Blo 299831 453509 := bbase (se 4 (by rfl) ⟨42516, by rfl⟩ : syracuseStep 453509 = 85033) (by norm_num)
theorem B682901 : Blo 299831 682901 := bbase (se 6 (by rfl) ⟨16005, by rfl⟩ : syracuseStep 682901 = 32011) (by norm_num)
theorem B453533 : Blo 299831 453533 := bbase (se 3 (by rfl) ⟨85037, by rfl⟩ : syracuseStep 453533 = 170075) (by norm_num)
theorem B2747317 : Blo 299831 2747317 := bbase (se 5 (by rfl) ⟨128780, by rfl⟩ : syracuseStep 2747317 = 257561) (by norm_num)
theorem B453557 : Blo 299831 453557 := bbase (se 5 (by rfl) ⟨21260, by rfl⟩ : syracuseStep 453557 = 42521) (by norm_num)
theorem B322489 : Blo 299831 322489 := bbase (se 2 (by rfl) ⟨120933, by rfl⟩ : syracuseStep 322489 = 241867) (by norm_num)
theorem B453581 : Blo 299831 453581 := bbase (se 3 (by rfl) ⟨85046, by rfl⟩ : syracuseStep 453581 = 170093) (by norm_num)
theorem B682973 : Blo 299831 682973 := bbase (se 3 (by rfl) ⟨128057, by rfl⟩ : syracuseStep 682973 = 256115) (by norm_num)
theorem B453605 : Blo 299831 453605 := bbase (se 4 (by rfl) ⟨42525, by rfl⟩ : syracuseStep 453605 = 85051) (by norm_num)
theorem B1534949 : Blo 299831 1534949 := bbase (se 4 (by rfl) ⟨143901, by rfl⟩ : syracuseStep 1534949 = 287803) (by norm_num)
theorem B453629 : Blo 299831 453629 := bbase (se 3 (by rfl) ⟨85055, by rfl⟩ : syracuseStep 453629 = 170111) (by norm_num)
theorem B453653 : Blo 299831 453653 := bbase (se 6 (by rfl) ⟨10632, by rfl⟩ : syracuseStep 453653 = 21265) (by norm_num)
theorem B683045 : Blo 299831 683045 := bbase (se 4 (by rfl) ⟨64035, by rfl⟩ : syracuseStep 683045 = 128071) (by norm_num)
theorem B453677 : Blo 299831 453677 := bbase (se 3 (by rfl) ⟨85064, by rfl⟩ : syracuseStep 453677 = 170129) (by norm_num)
theorem B453701 : Blo 299831 453701 := bbase (se 4 (by rfl) ⟨42534, by rfl⟩ : syracuseStep 453701 = 85069) (by norm_num)
theorem B453725 : Blo 299831 453725 := bbase (se 3 (by rfl) ⟨85073, by rfl⟩ : syracuseStep 453725 = 170147) (by norm_num)
theorem B683117 : Blo 299831 683117 := bbase (se 3 (by rfl) ⟨128084, by rfl⟩ : syracuseStep 683117 = 256169) (by norm_num)
theorem B453749 : Blo 299831 453749 := bbase (se 5 (by rfl) ⟨21269, by rfl⟩ : syracuseStep 453749 = 42539) (by norm_num)
theorem B453773 : Blo 299831 453773 := bbase (se 3 (by rfl) ⟨85082, by rfl⟩ : syracuseStep 453773 = 170165) (by norm_num)
theorem B453797 : Blo 299831 453797 := bbase (se 4 (by rfl) ⟨42543, by rfl⟩ : syracuseStep 453797 = 85087) (by norm_num)
theorem B683189 : Blo 299831 683189 := bbase (se 5 (by rfl) ⟨32024, by rfl⟩ : syracuseStep 683189 = 64049) (by norm_num)
theorem B453821 : Blo 299831 453821 := bbase (se 3 (by rfl) ⟨85091, by rfl⟩ : syracuseStep 453821 = 170183) (by norm_num)
theorem B453845 : Blo 299831 453845 := bbase (se 7 (by rfl) ⟨5318, by rfl⟩ : syracuseStep 453845 = 10637) (by norm_num)
theorem B453869 : Blo 299831 453869 := bbase (se 3 (by rfl) ⟨85100, by rfl⟩ : syracuseStep 453869 = 170201) (by norm_num)
theorem B322805 : Blo 299831 322805 := bbase (se 5 (by rfl) ⟨15131, by rfl⟩ : syracuseStep 322805 = 30263) (by norm_num)
theorem B683261 : Blo 299831 683261 := bbase (se 3 (by rfl) ⟨128111, by rfl⟩ : syracuseStep 683261 = 256223) (by norm_num)
theorem B453893 : Blo 299831 453893 := bbase (se 4 (by rfl) ⟨42552, by rfl⟩ : syracuseStep 453893 = 85105) (by norm_num)
theorem B453917 : Blo 299831 453917 := bbase (se 3 (by rfl) ⟨85109, by rfl⟩ : syracuseStep 453917 = 170219) (by norm_num)
theorem B453941 : Blo 299831 453941 := bbase (se 5 (by rfl) ⟨21278, by rfl⟩ : syracuseStep 453941 = 42557) (by norm_num)
theorem B683333 : Blo 299831 683333 := bbase (se 4 (by rfl) ⟨64062, by rfl⟩ : syracuseStep 683333 = 128125) (by norm_num)
theorem B453965 : Blo 299831 453965 := bbase (se 3 (by rfl) ⟨85118, by rfl⟩ : syracuseStep 453965 = 170237) (by norm_num)
theorem B453989 : Blo 299831 453989 := bbase (se 4 (by rfl) ⟨42561, by rfl⟩ : syracuseStep 453989 = 85123) (by norm_num)
theorem B454013 : Blo 299831 454013 := bbase (se 3 (by rfl) ⟨85127, by rfl⟩ : syracuseStep 454013 = 170255) (by norm_num)
theorem B683405 : Blo 299831 683405 := bbase (se 3 (by rfl) ⟨128138, by rfl⟩ : syracuseStep 683405 = 256277) (by norm_num)
theorem B454037 : Blo 299831 454037 := bbase (se 6 (by rfl) ⟨10641, by rfl⟩ : syracuseStep 454037 = 21283) (by norm_num)
theorem B454061 : Blo 299831 454061 := bbase (se 3 (by rfl) ⟨85136, by rfl⟩ : syracuseStep 454061 = 170273) (by norm_num)
theorem B454085 : Blo 299831 454085 := bbase (se 4 (by rfl) ⟨42570, by rfl⟩ : syracuseStep 454085 = 85141) (by norm_num)
theorem B683477 : Blo 299831 683477 := bbase (se 7 (by rfl) ⟨8009, by rfl⟩ : syracuseStep 683477 = 16019) (by norm_num)
theorem B454109 : Blo 299831 454109 := bbase (se 3 (by rfl) ⟨85145, by rfl⟩ : syracuseStep 454109 = 170291) (by norm_num)
theorem B454133 : Blo 299831 454133 := bbase (se 5 (by rfl) ⟨21287, by rfl⟩ : syracuseStep 454133 = 42575) (by norm_num)
theorem B454157 : Blo 299831 454157 := bbase (se 3 (by rfl) ⟨85154, by rfl⟩ : syracuseStep 454157 = 170309) (by norm_num)
theorem B683549 : Blo 299831 683549 := bbase (se 3 (by rfl) ⟨128165, by rfl⟩ : syracuseStep 683549 = 256331) (by norm_num)
theorem B454181 : Blo 299831 454181 := bbase (se 4 (by rfl) ⟨42579, by rfl⟩ : syracuseStep 454181 = 85159) (by norm_num)
theorem B454205 : Blo 299831 454205 := bbase (se 3 (by rfl) ⟨85163, by rfl⟩ : syracuseStep 454205 = 170327) (by norm_num)
theorem B454229 : Blo 299831 454229 := bbase (se 8 (by rfl) ⟨2661, by rfl⟩ : syracuseStep 454229 = 5323) (by norm_num)
theorem B683621 : Blo 299831 683621 := bbase (se 4 (by rfl) ⟨64089, by rfl⟩ : syracuseStep 683621 = 128179) (by norm_num)
theorem B454253 : Blo 299831 454253 := bbase (se 3 (by rfl) ⟨85172, by rfl⟩ : syracuseStep 454253 = 170345) (by norm_num)
theorem B454277 : Blo 299831 454277 := bbase (se 4 (by rfl) ⟨42588, by rfl⟩ : syracuseStep 454277 = 85177) (by norm_num)
theorem B454301 : Blo 299831 454301 := bbase (se 3 (by rfl) ⟨85181, by rfl⟩ : syracuseStep 454301 = 170363) (by norm_num)
theorem B323249 : Blo 299831 323249 := bbase (se 2 (by rfl) ⟨121218, by rfl⟩ : syracuseStep 323249 = 242437) (by norm_num)
theorem B454325 : Blo 299831 454325 := bbase (se 5 (by rfl) ⟨21296, by rfl⟩ : syracuseStep 454325 = 42593) (by norm_num)
theorem B454349 : Blo 299831 454349 := bbase (se 3 (by rfl) ⟨85190, by rfl⟩ : syracuseStep 454349 = 170381) (by norm_num)
theorem B454373 : Blo 299831 454373 := bbase (se 4 (by rfl) ⟨42597, by rfl⟩ : syracuseStep 454373 = 85195) (by norm_num)
theorem B323309 : Blo 299831 323309 := bbase (se 3 (by rfl) ⟨60620, by rfl⟩ : syracuseStep 323309 = 121241) (by norm_num)
theorem B454397 : Blo 299831 454397 := bbase (se 3 (by rfl) ⟨85199, by rfl⟩ : syracuseStep 454397 = 170399) (by norm_num)
theorem B913157 : Blo 299831 913157 := bbase (se 4 (by rfl) ⟨85608, by rfl⟩ : syracuseStep 913157 = 171217) (by norm_num)
theorem B454421 : Blo 299831 454421 := bbase (se 6 (by rfl) ⟨10650, by rfl⟩ : syracuseStep 454421 = 21301) (by norm_num)
theorem B454445 : Blo 299831 454445 := bbase (se 3 (by rfl) ⟨85208, by rfl⟩ : syracuseStep 454445 = 170417) (by norm_num)
theorem B454469 : Blo 299831 454469 := bbase (se 4 (by rfl) ⟨42606, by rfl⟩ : syracuseStep 454469 = 85213) (by norm_num)
theorem B454493 : Blo 299831 454493 := bbase (se 3 (by rfl) ⟨85217, by rfl⟩ : syracuseStep 454493 = 170435) (by norm_num)
theorem B388969 : Blo 299831 388969 := bbase (se 2 (by rfl) ⟨145863, by rfl⟩ : syracuseStep 388969 = 291727) (by norm_num)
theorem B323437 : Blo 299831 323437 := bbase (se 3 (by rfl) ⟨60644, by rfl⟩ : syracuseStep 323437 = 121289) (by norm_num)
theorem B454517 : Blo 299831 454517 := bbase (se 5 (by rfl) ⟨21305, by rfl⟩ : syracuseStep 454517 = 42611) (by norm_num)
theorem B651149 : Blo 299831 651149 := bbase (se 3 (by rfl) ⟨122090, by rfl⟩ : syracuseStep 651149 = 244181) (by norm_num)
theorem B454541 : Blo 299831 454541 := bbase (se 3 (by rfl) ⟨85226, by rfl⟩ : syracuseStep 454541 = 170453) (by norm_num)
theorem B1142693 : Blo 299831 1142693 := bbase (se 4 (by rfl) ⟨107127, by rfl⟩ : syracuseStep 1142693 = 214255) (by norm_num)
theorem B454565 : Blo 299831 454565 := bbase (se 4 (by rfl) ⟨42615, by rfl⟩ : syracuseStep 454565 = 85231) (by norm_num)
theorem B454589 : Blo 299831 454589 := bbase (se 3 (by rfl) ⟨85235, by rfl⟩ : syracuseStep 454589 = 170471) (by norm_num)
theorem B454613 : Blo 299831 454613 := bbase (se 7 (by rfl) ⟨5327, by rfl⟩ : syracuseStep 454613 = 10655) (by norm_num)
theorem B454637 : Blo 299831 454637 := bbase (se 3 (by rfl) ⟨85244, by rfl⟩ : syracuseStep 454637 = 170489) (by norm_num)
theorem B454661 : Blo 299831 454661 := bbase (se 4 (by rfl) ⟨42624, by rfl⟩ : syracuseStep 454661 = 85249) (by norm_num)
theorem B454685 : Blo 299831 454685 := bbase (se 3 (by rfl) ⟨85253, by rfl⟩ : syracuseStep 454685 = 170507) (by norm_num)
theorem B454709 : Blo 299831 454709 := bbase (se 5 (by rfl) ⟨21314, by rfl⟩ : syracuseStep 454709 = 42629) (by norm_num)
theorem B454733 : Blo 299831 454733 := bbase (se 3 (by rfl) ⟨85262, by rfl⟩ : syracuseStep 454733 = 170525) (by norm_num)
theorem B454757 : Blo 299831 454757 := bbase (se 4 (by rfl) ⟨42633, by rfl⟩ : syracuseStep 454757 = 85267) (by norm_num)
theorem B454781 : Blo 299831 454781 := bbase (se 3 (by rfl) ⟨85271, by rfl⟩ : syracuseStep 454781 = 170543) (by norm_num)
theorem B454805 : Blo 299831 454805 := bbase (se 6 (by rfl) ⟨10659, by rfl⟩ : syracuseStep 454805 = 21319) (by norm_num)
theorem B454829 : Blo 299831 454829 := bbase (se 3 (by rfl) ⟨85280, by rfl⟩ : syracuseStep 454829 = 170561) (by norm_num)
theorem B815285 : Blo 299831 815285 := bbase (se 5 (by rfl) ⟨38216, by rfl⟩ : syracuseStep 815285 = 76433) (by norm_num)
theorem B1142981 : Blo 299831 1142981 := bbase (se 4 (by rfl) ⟨107154, by rfl⟩ : syracuseStep 1142981 = 214309) (by norm_num)
theorem B454853 : Blo 299831 454853 := bbase (se 4 (by rfl) ⟨42642, by rfl⟩ : syracuseStep 454853 = 85285) (by norm_num)
theorem B454877 : Blo 299831 454877 := bbase (se 3 (by rfl) ⟨85289, by rfl⟩ : syracuseStep 454877 = 170579) (by norm_num)
theorem B553189 : Blo 299831 553189 := bbase (se 4 (by rfl) ⟨51861, by rfl⟩ : syracuseStep 553189 = 103723) (by norm_num)
theorem B1831157 : Blo 299831 1831157 := bbase (se 5 (by rfl) ⟨85835, by rfl⟩ : syracuseStep 1831157 = 171671) (by norm_num)
theorem B454901 : Blo 299831 454901 := bbase (se 5 (by rfl) ⟨21323, by rfl⟩ : syracuseStep 454901 = 42647) (by norm_num)
theorem B1536245 : Blo 299831 1536245 := bbase (se 5 (by rfl) ⟨72011, by rfl⟩ : syracuseStep 1536245 = 144023) (by norm_num)
theorem B454925 : Blo 299831 454925 := bbase (se 3 (by rfl) ⟨85298, by rfl⟩ : syracuseStep 454925 = 170597) (by norm_num)
theorem B454949 : Blo 299831 454949 := bbase (se 4 (by rfl) ⟨42651, by rfl⟩ : syracuseStep 454949 = 85303) (by norm_num)
theorem B323881 : Blo 299831 323881 := bbase (se 2 (by rfl) ⟨121455, by rfl⟩ : syracuseStep 323881 = 242911) (by norm_num)
theorem B454973 : Blo 299831 454973 := bbase (se 3 (by rfl) ⟨85307, by rfl⟩ : syracuseStep 454973 = 170615) (by norm_num)
theorem B454997 : Blo 299831 454997 := bbase (se 10 (by rfl) ⟨666, by rfl⟩ : syracuseStep 454997 = 1333) (by norm_num)
theorem B455021 : Blo 299831 455021 := bbase (se 3 (by rfl) ⟨85316, by rfl⟩ : syracuseStep 455021 = 170633) (by norm_num)
theorem B455045 : Blo 299831 455045 := bbase (se 4 (by rfl) ⟨42660, by rfl⟩ : syracuseStep 455045 = 85321) (by norm_num)
theorem B455069 : Blo 299831 455069 := bbase (se 3 (by rfl) ⟨85325, by rfl⟩ : syracuseStep 455069 = 170651) (by norm_num)
theorem B324001 : Blo 299831 324001 := bbase (se 2 (by rfl) ⟨121500, by rfl⟩ : syracuseStep 324001 = 243001) (by norm_num)
theorem B1929653 : Blo 299831 1929653 := bbase (se 5 (by rfl) ⟨90452, by rfl⟩ : syracuseStep 1929653 = 180905) (by norm_num)
theorem B455093 : Blo 299831 455093 := bbase (se 5 (by rfl) ⟨21332, by rfl⟩ : syracuseStep 455093 = 42665) (by norm_num)
theorem B455117 : Blo 299831 455117 := bbase (se 3 (by rfl) ⟨85334, by rfl⟩ : syracuseStep 455117 = 170669) (by norm_num)
theorem B455141 : Blo 299831 455141 := bbase (se 4 (by rfl) ⟨42669, by rfl⟩ : syracuseStep 455141 = 85339) (by norm_num)
theorem B455165 : Blo 299831 455165 := bbase (se 3 (by rfl) ⟨85343, by rfl⟩ : syracuseStep 455165 = 170687) (by norm_num)
theorem B1012229 : Blo 299831 1012229 := bbase (se 4 (by rfl) ⟨94896, by rfl⟩ : syracuseStep 1012229 = 189793) (by norm_num)
theorem B455189 : Blo 299831 455189 := bbase (se 6 (by rfl) ⟨10668, by rfl⟩ : syracuseStep 455189 = 21337) (by norm_num)
theorem B455213 : Blo 299831 455213 := bbase (se 3 (by rfl) ⟨85352, by rfl⟩ : syracuseStep 455213 = 170705) (by norm_num)
theorem B455237 : Blo 299831 455237 := bbase (se 4 (by rfl) ⟨42678, by rfl⟩ : syracuseStep 455237 = 85357) (by norm_num)
theorem B455261 : Blo 299831 455261 := bbase (se 3 (by rfl) ⟨85361, by rfl⟩ : syracuseStep 455261 = 170723) (by norm_num)
theorem B815717 : Blo 299831 815717 := bbase (se 4 (by rfl) ⟨76473, by rfl⟩ : syracuseStep 815717 = 152947) (by norm_num)
theorem B455285 : Blo 299831 455285 := bbase (se 5 (by rfl) ⟨21341, by rfl⟩ : syracuseStep 455285 = 42683) (by norm_num)
theorem B455309 : Blo 299831 455309 := bbase (se 3 (by rfl) ⟨85370, by rfl⟩ : syracuseStep 455309 = 170741) (by norm_num)
theorem B324253 : Blo 299831 324253 := bbase (se 3 (by rfl) ⟨60797, by rfl⟩ : syracuseStep 324253 = 121595) (by norm_num)
theorem B324257 : Blo 299831 324257 := bbase (se 2 (by rfl) ⟨121596, by rfl⟩ : syracuseStep 324257 = 243193) (by norm_num)
theorem B455333 : Blo 299831 455333 := bbase (se 4 (by rfl) ⟨42687, by rfl⟩ : syracuseStep 455333 = 85375) (by norm_num)
theorem B455357 : Blo 299831 455357 := bbase (se 3 (by rfl) ⟨85379, by rfl⟩ : syracuseStep 455357 = 170759) (by norm_num)
theorem B455381 : Blo 299831 455381 := bbase (se 7 (by rfl) ⟨5336, by rfl⟩ : syracuseStep 455381 = 10673) (by norm_num)
theorem B455405 : Blo 299831 455405 := bbase (se 3 (by rfl) ⟨85388, by rfl⟩ : syracuseStep 455405 = 170777) (by norm_num)
theorem B455429 : Blo 299831 455429 := bbase (se 4 (by rfl) ⟨42696, by rfl⟩ : syracuseStep 455429 = 85393) (by norm_num)
theorem B455453 : Blo 299831 455453 := bbase (se 3 (by rfl) ⟨85397, by rfl⟩ : syracuseStep 455453 = 170795) (by norm_num)
theorem B455477 : Blo 299831 455477 := bbase (se 5 (by rfl) ⟨21350, by rfl⟩ : syracuseStep 455477 = 42701) (by norm_num)
theorem B455501 : Blo 299831 455501 := bbase (se 3 (by rfl) ⟨85406, by rfl⟩ : syracuseStep 455501 = 170813) (by norm_num)
theorem B2290517 : Blo 299831 2290517 := bbase (se 9 (by rfl) ⟨6710, by rfl⟩ : syracuseStep 2290517 = 13421) (by norm_num)
theorem B455525 : Blo 299831 455525 := bbase (se 4 (by rfl) ⟨42705, by rfl⟩ : syracuseStep 455525 = 85411) (by norm_num)
theorem B455549 : Blo 299831 455549 := bbase (se 3 (by rfl) ⟨85415, by rfl⟩ : syracuseStep 455549 = 170831) (by norm_num)
theorem B455573 : Blo 299831 455573 := bbase (se 6 (by rfl) ⟨10677, by rfl⟩ : syracuseStep 455573 = 21355) (by norm_num)
theorem B652205 : Blo 299831 652205 := bbase (se 3 (by rfl) ⟨122288, by rfl⟩ : syracuseStep 652205 = 244577) (by norm_num)
theorem B455597 : Blo 299831 455597 := bbase (se 3 (by rfl) ⟨85424, by rfl⟩ : syracuseStep 455597 = 170849) (by norm_num)
theorem B1012661 : Blo 299831 1012661 := bbase (se 5 (by rfl) ⟨47468, by rfl⟩ : syracuseStep 1012661 = 94937) (by norm_num)
theorem B455621 : Blo 299831 455621 := bbase (se 4 (by rfl) ⟨42714, by rfl⟩ : syracuseStep 455621 = 85429) (by norm_num)
theorem B455645 : Blo 299831 455645 := bbase (se 3 (by rfl) ⟨85433, by rfl⟩ : syracuseStep 455645 = 170867) (by norm_num)
theorem B455669 : Blo 299831 455669 := bbase (se 5 (by rfl) ⟨21359, by rfl⟩ : syracuseStep 455669 = 42719) (by norm_num)
theorem B455693 : Blo 299831 455693 := bbase (se 3 (by rfl) ⟨85442, by rfl⟩ : syracuseStep 455693 = 170885) (by norm_num)
theorem B455717 : Blo 299831 455717 := bbase (se 4 (by rfl) ⟨42723, by rfl⟩ : syracuseStep 455717 = 85447) (by norm_num)
theorem B1373237 : Blo 299831 1373237 := bbase (se 5 (by rfl) ⟨64370, by rfl⟩ : syracuseStep 1373237 = 128741) (by norm_num)
theorem B455741 : Blo 299831 455741 := bbase (se 3 (by rfl) ⟨85451, by rfl⟩ : syracuseStep 455741 = 170903) (by norm_num)
theorem B652445 : Blo 299831 652445 := bbase (se 3 (by rfl) ⟨122333, by rfl⟩ : syracuseStep 652445 = 244667) (by norm_num)
theorem B1013093 : Blo 299831 1013093 := bbase (se 4 (by rfl) ⟨94977, by rfl⟩ : syracuseStep 1013093 = 189955) (by norm_num)
theorem B1144165 : Blo 299831 1144165 := bbase (se 4 (by rfl) ⟨107265, by rfl⟩ : syracuseStep 1144165 = 214531) (by norm_num)
theorem B1537541 : Blo 299831 1537541 := bbase (se 4 (by rfl) ⟨144144, by rfl⟩ : syracuseStep 1537541 = 288289) (by norm_num)
theorem B1144469 : Blo 299831 1144469 := bbase (se 6 (by rfl) ⟨26823, by rfl⟩ : syracuseStep 1144469 = 53647) (by norm_num)
theorem B456445 : Blo 299831 456445 := bbase (se 3 (by rfl) ⟨85583, by rfl⟩ : syracuseStep 456445 = 171167) (by norm_num)
theorem B1013525 : Blo 299831 1013525 := bbase (se 6 (by rfl) ⟨23754, by rfl⟩ : syracuseStep 1013525 = 47509) (by norm_num)
theorem B554813 : Blo 299831 554813 := bbase (se 3 (by rfl) ⟨104027, by rfl⟩ : syracuseStep 554813 = 208055) (by norm_num)
theorem B456653 : Blo 299831 456653 := bbase (se 3 (by rfl) ⟨85622, by rfl⟩ : syracuseStep 456653 = 171245) (by norm_num)
theorem B325721 : Blo 299831 325721 := bbase (se 2 (by rfl) ⟨122145, by rfl⟩ : syracuseStep 325721 = 244291) (by norm_num)
theorem B456821 : Blo 299831 456821 := bbase (se 5 (by rfl) ⟨21413, by rfl⟩ : syracuseStep 456821 = 42827) (by norm_num)
theorem B1013957 : Blo 299831 1013957 := bbase (se 4 (by rfl) ⟨95058, by rfl⟩ : syracuseStep 1013957 = 190117) (by norm_num)
theorem B1964245 : Blo 299831 1964245 := bbase (se 7 (by rfl) ⟨23018, by rfl⟩ : syracuseStep 1964245 = 46037) (by norm_num)
theorem B1964405 : Blo 299831 1964405 := bbase (se 5 (by rfl) ⟨92081, by rfl⟩ : syracuseStep 1964405 = 184163) (by norm_num)
theorem B2882101 : Blo 299831 2882101 := bbase (se 5 (by rfl) ⟨135098, by rfl⟩ : syracuseStep 2882101 = 270197) (by norm_num)
theorem B1014389 : Blo 299831 1014389 := bbase (se 5 (by rfl) ⟨47549, by rfl⟩ : syracuseStep 1014389 = 95099) (by norm_num)
theorem B7076821 : Blo 299831 7076821 := bbase (se 7 (by rfl) ⟨82931, by rfl⟩ : syracuseStep 7076821 = 165863) (by norm_num)
theorem B457741 : Blo 299831 457741 := bbase (se 3 (by rfl) ⟨85826, by rfl⟩ : syracuseStep 457741 = 171653) (by norm_num)
theorem B1014821 : Blo 299831 1014821 := bbase (se 4 (by rfl) ⟨95139, by rfl⟩ : syracuseStep 1014821 = 190279) (by norm_num)
theorem B916853 : Blo 299831 916853 := bbase (se 5 (by rfl) ⟨42977, by rfl⟩ : syracuseStep 916853 = 85955) (by norm_num)
theorem B1015253 : Blo 299831 1015253 := bbase (se 7 (by rfl) ⟨11897, by rfl⟩ : syracuseStep 1015253 = 23795) (by norm_num)
theorem B3866069 : Blo 299831 3866069 := bbase (se 7 (by rfl) ⟨45305, by rfl⟩ : syracuseStep 3866069 = 90611) (by norm_num)
theorem B1146581 : Blo 299831 1146581 := bbase (se 7 (by rfl) ⟨13436, by rfl⟩ : syracuseStep 1146581 = 26873) (by norm_num)
theorem B327469 : Blo 299831 327469 := bbase (se 3 (by rfl) ⟨61400, by rfl⟩ : syracuseStep 327469 = 122801) (by norm_num)
theorem B1015685 : Blo 299831 1015685 := bbase (se 4 (by rfl) ⟨95220, by rfl⟩ : syracuseStep 1015685 = 190441) (by norm_num)
theorem B1146869 : Blo 299831 1146869 := bbase (se 5 (by rfl) ⟨53759, by rfl⟩ : syracuseStep 1146869 = 107519) (by norm_num)
theorem B327677 : Blo 299831 327677 := bbase (se 3 (by rfl) ⟨61439, by rfl⟩ : syracuseStep 327677 = 122879) (by norm_num)
theorem B1310833 : Blo 299831 1310833 := bstep (se 2 (by rfl) ⟨491562, by rfl⟩ : syracuseStep 1310833 = 983125) B983125
theorem B1933445 : Blo 299831 1933445 := bstep (se 4 (by rfl) ⟨181260, by rfl⟩ : syracuseStep 1933445 = 362521) B362521
theorem B458963 : Blo 299831 458963 := bstep (se 1 (by rfl) ⟨344222, by rfl⟩ : syracuseStep 458963 = 688445) B688445
theorem B1442225 : Blo 299831 1442225 := bstep (se 2 (by rfl) ⟨540834, by rfl⟩ : syracuseStep 1442225 = 1081669) B1081669
theorem B1016333 : Blo 299831 1016333 := bstep (se 3 (by rfl) ⟨190562, by rfl⟩ : syracuseStep 1016333 = 381125) B381125
theorem B1016387 : Blo 299831 1016387 := bstep (se 1 (by rfl) ⟨762290, by rfl⟩ : syracuseStep 1016387 = 1524581) B1524581
theorem B2458309 : Blo 299831 2458309 := bstep (se 4 (by rfl) ⟨230466, by rfl⟩ : syracuseStep 2458309 = 460933) B460933
theorem B1639217 : Blo 299831 1639217 := bstep (se 2 (by rfl) ⟨614706, by rfl⟩ : syracuseStep 1639217 = 1229413) B1229413
theorem B1016657 : Blo 299831 1016657 := bstep (se 2 (by rfl) ⟨381246, by rfl⟩ : syracuseStep 1016657 = 762493) B762493
theorem B426961 : Blo 299831 426961 := bstep (se 2 (by rfl) ⟨160110, by rfl⟩ : syracuseStep 426961 = 320221) B320221
theorem B689393 : Blo 299831 689393 := bstep (se 2 (by rfl) ⟨258522, by rfl⟩ : syracuseStep 689393 = 517045) B517045
theorem B427297 : Blo 299831 427297 := bstep (se 2 (by rfl) ⟨160236, by rfl⟩ : syracuseStep 427297 = 320473) B320473
theorem B460081 : Blo 299831 460081 := bstep (se 2 (by rfl) ⟨172530, by rfl⟩ : syracuseStep 460081 = 345061) B345061
theorem B1017197 : Blo 299831 1017197 := bstep (se 3 (by rfl) ⟨190724, by rfl⟩ : syracuseStep 1017197 = 381449) B381449
theorem B1017251 : Blo 299831 1017251 := bstep (se 1 (by rfl) ⟨762938, by rfl⟩ : syracuseStep 1017251 = 1525877) B1525877
theorem B918947 : Blo 299831 918947 := bstep (se 1 (by rfl) ⟨689210, by rfl⟩ : syracuseStep 918947 = 1378421) B1378421
theorem B722371 : Blo 299831 722371 := bstep (se 1 (by rfl) ⟨541778, by rfl⟩ : syracuseStep 722371 = 1083557) B1083557
theorem B3507781 : Blo 299831 3507781 := bstep (se 4 (by rfl) ⟨328854, by rfl⟩ : syracuseStep 3507781 = 657709) B657709
theorem B919117 : Blo 299831 919117 := bstep (se 3 (by rfl) ⟨172334, by rfl⟩ : syracuseStep 919117 = 344669) B344669
theorem B1017521 : Blo 299831 1017521 := bstep (se 2 (by rfl) ⟨381570, by rfl⟩ : syracuseStep 1017521 = 763141) B763141
theorem B853841 : Blo 299831 853841 := bstep (se 2 (by rfl) ⟨320190, by rfl⟩ : syracuseStep 853841 = 640381) B640381
theorem B427889 : Blo 299831 427889 := bstep (se 2 (by rfl) ⟨160458, by rfl⟩ : syracuseStep 427889 = 320917) B320917
theorem B821123 : Blo 299831 821123 := bstep (se 1 (by rfl) ⟨615842, by rfl⟩ : syracuseStep 821123 = 1231685) B1231685
theorem B1148813 : Blo 299831 1148813 := bstep (se 3 (by rfl) ⟨215402, by rfl⟩ : syracuseStep 1148813 = 430805) B430805
theorem B723043 : Blo 299831 723043 := bstep (se 1 (by rfl) ⟨542282, by rfl⟩ : syracuseStep 723043 = 1084565) B1084565
theorem B362675 : Blo 299831 362675 := bstep (se 1 (by rfl) ⟨272006, by rfl⟩ : syracuseStep 362675 = 544013) B544013
theorem B1018061 : Blo 299831 1018061 := bstep (se 3 (by rfl) ⟨190886, by rfl⟩ : syracuseStep 1018061 = 381773) B381773
theorem B362723 : Blo 299831 362723 := bstep (se 1 (by rfl) ⟨272042, by rfl⟩ : syracuseStep 362723 = 544085) B544085
theorem B1018115 : Blo 299831 1018115 := bstep (se 1 (by rfl) ⟨763586, by rfl⟩ : syracuseStep 1018115 = 1527173) B1527173
theorem B428419 : Blo 299831 428419 := bstep (se 1 (by rfl) ⟨321314, by rfl⟩ : syracuseStep 428419 = 642629) B642629
theorem B1018385 : Blo 299831 1018385 := bstep (se 2 (by rfl) ⟨381894, by rfl⟩ : syracuseStep 1018385 = 763789) B763789
theorem B723505 : Blo 299831 723505 := bstep (se 2 (by rfl) ⟨271314, by rfl⟩ : syracuseStep 723505 = 542629) B542629
theorem B723601 : Blo 299831 723601 := bstep (se 2 (by rfl) ⟨271350, by rfl⟩ : syracuseStep 723601 = 542701) B542701
theorem B428755 : Blo 299831 428755 := bstep (se 1 (by rfl) ⟨321566, by rfl⟩ : syracuseStep 428755 = 643133) B643133
theorem B2591459 : Blo 299831 2591459 := bstep (se 1 (by rfl) ⟨1943594, by rfl⟩ : syracuseStep 2591459 = 3887189) B3887189
theorem B1936163 : Blo 299831 1936163 := bstep (se 1 (by rfl) ⟨1452122, by rfl⟩ : syracuseStep 1936163 = 2904245) B2904245
theorem B854833 : Blo 299831 854833 := bstep (se 2 (by rfl) ⟨320562, by rfl⟩ : syracuseStep 854833 = 641125) B641125
theorem B1641293 : Blo 299831 1641293 := bstep (se 3 (by rfl) ⟨307742, by rfl⟩ : syracuseStep 1641293 = 615485) B615485
theorem B1018925 : Blo 299831 1018925 := bstep (se 3 (by rfl) ⟨191048, by rfl⟩ : syracuseStep 1018925 = 382097) B382097
theorem B855107 : Blo 299831 855107 := bstep (se 1 (by rfl) ⟨641330, by rfl⟩ : syracuseStep 855107 = 1282661) B1282661
theorem B1018979 : Blo 299831 1018979 := bstep (se 1 (by rfl) ⟨764234, by rfl⟩ : syracuseStep 1018979 = 1528469) B1528469
theorem B691363 : Blo 299831 691363 := bstep (se 1 (by rfl) ⟨518522, by rfl⟩ : syracuseStep 691363 = 1037045) B1037045
theorem B429313 : Blo 299831 429313 := bstep (se 2 (by rfl) ⟨160992, by rfl⟩ : syracuseStep 429313 = 321985) B321985
theorem B855299 : Blo 299831 855299 := bstep (se 1 (by rfl) ⟨641474, by rfl⟩ : syracuseStep 855299 = 1282949) B1282949
theorem B429347 : Blo 299831 429347 := bstep (se 1 (by rfl) ⟨322010, by rfl⟩ : syracuseStep 429347 = 644021) B644021
theorem B1019249 : Blo 299831 1019249 := bstep (se 2 (by rfl) ⟨382218, by rfl⟩ : syracuseStep 1019249 = 764437) B764437
theorem B1084913 : Blo 299831 1084913 := bstep (se 2 (by rfl) ⟨406842, by rfl⟩ : syracuseStep 1084913 = 813685) B813685
theorem B429905 : Blo 299831 429905 := bstep (se 2 (by rfl) ⟨161214, by rfl⟩ : syracuseStep 429905 = 322429) B322429
theorem B1019789 : Blo 299831 1019789 := bstep (se 3 (by rfl) ⟨191210, by rfl⟩ : syracuseStep 1019789 = 382421) B382421
theorem B429985 : Blo 299831 429985 := bstep (se 2 (by rfl) ⟨161244, by rfl⟩ : syracuseStep 429985 = 322489) B322489
theorem B1544113 : Blo 299831 1544113 := bstep (se 2 (by rfl) ⟨579042, by rfl⟩ : syracuseStep 1544113 = 1158085) B1158085
theorem B1019843 : Blo 299831 1019843 := bstep (se 1 (by rfl) ⟨764882, by rfl⟩ : syracuseStep 1019843 = 1529765) B1529765
theorem B1282061 : Blo 299831 1282061 := bstep (se 3 (by rfl) ⟨240386, by rfl⟩ : syracuseStep 1282061 = 480773) B480773
theorem B856109 : Blo 299831 856109 := bstep (se 3 (by rfl) ⟨160520, by rfl⟩ : syracuseStep 856109 = 321041) B321041
theorem B2330765 : Blo 299831 2330765 := bstep (se 3 (by rfl) ⟨437018, by rfl⟩ : syracuseStep 2330765 = 874037) B874037
theorem B1708229 : Blo 299831 1708229 := bstep (se 4 (by rfl) ⟨160146, by rfl⟩ : syracuseStep 1708229 = 320293) B320293
theorem B1020113 : Blo 299831 1020113 := bstep (se 2 (by rfl) ⟨382542, by rfl⟩ : syracuseStep 1020113 = 765085) B765085
theorem B856291 : Blo 299831 856291 := bstep (se 1 (by rfl) ⟨642218, by rfl⟩ : syracuseStep 856291 = 1284437) B1284437
theorem B1970693 : Blo 299831 1970693 := bstep (se 4 (by rfl) ⟨184752, by rfl⟩ : syracuseStep 1970693 = 369505) B369505
theorem B1708685 : Blo 299831 1708685 := bstep (se 3 (by rfl) ⟨320378, by rfl⟩ : syracuseStep 1708685 = 640757) B640757
theorem B430771 : Blo 299831 430771 := bstep (se 1 (by rfl) ⟨323078, by rfl⟩ : syracuseStep 430771 = 646157) B646157
theorem B856781 : Blo 299831 856781 := bstep (se 3 (by rfl) ⟨160646, by rfl⟩ : syracuseStep 856781 = 321293) B321293
theorem B1020653 : Blo 299831 1020653 := bstep (se 3 (by rfl) ⟨191372, by rfl⟩ : syracuseStep 1020653 = 382745) B382745
theorem B1938161 : Blo 299831 1938161 := bstep (se 2 (by rfl) ⟨726810, by rfl⟩ : syracuseStep 1938161 = 1453621) B1453621
theorem B1151729 : Blo 299831 1151729 := bstep (se 2 (by rfl) ⟨431898, by rfl⟩ : syracuseStep 1151729 = 863797) B863797
theorem B1020707 : Blo 299831 1020707 := bstep (se 1 (by rfl) ⟨765530, by rfl⟩ : syracuseStep 1020707 = 1531061) B1531061
theorem B299843 : Blo 299831 299843 := bstep (se 1 (by rfl) ⟨224882, by rfl⟩ : syracuseStep 299843 = 449765) B449765
theorem B299859 : Blo 299831 299859 := bstep (se 1 (by rfl) ⟨224894, by rfl⟩ : syracuseStep 299859 = 449789) B449789
theorem B299875 : Blo 299831 299875 := bstep (se 1 (by rfl) ⟨224906, by rfl⟩ : syracuseStep 299875 = 449813) B449813
theorem B299891 : Blo 299831 299891 := bstep (se 1 (by rfl) ⟨224918, by rfl⟩ : syracuseStep 299891 = 449837) B449837
theorem B299907 : Blo 299831 299907 := bstep (se 1 (by rfl) ⟨224930, by rfl⟩ : syracuseStep 299907 = 449861) B449861
theorem B299923 : Blo 299831 299923 := bstep (se 1 (by rfl) ⟨224942, by rfl⟩ : syracuseStep 299923 = 449885) B449885
theorem B299939 : Blo 299831 299939 := bstep (se 1 (by rfl) ⟨224954, by rfl⟩ : syracuseStep 299939 = 449909) B449909
theorem B299955 : Blo 299831 299955 := bstep (se 1 (by rfl) ⟨224966, by rfl⟩ : syracuseStep 299955 = 449933) B449933
theorem B299971 : Blo 299831 299971 := bstep (se 1 (by rfl) ⟨224978, by rfl⟩ : syracuseStep 299971 = 449957) B449957
theorem B299987 : Blo 299831 299987 := bstep (se 1 (by rfl) ⟨224990, by rfl⟩ : syracuseStep 299987 = 449981) B449981
theorem B300003 : Blo 299831 300003 := bstep (se 1 (by rfl) ⟨225002, by rfl⟩ : syracuseStep 300003 = 450005) B450005
theorem B300019 : Blo 299831 300019 := bstep (se 1 (by rfl) ⟨225014, by rfl⟩ : syracuseStep 300019 = 450029) B450029
theorem B300035 : Blo 299831 300035 := bstep (se 1 (by rfl) ⟨225026, by rfl⟩ : syracuseStep 300035 = 450053) B450053
theorem B300051 : Blo 299831 300051 := bstep (se 1 (by rfl) ⟨225038, by rfl⟩ : syracuseStep 300051 = 450077) B450077
theorem B300067 : Blo 299831 300067 := bstep (se 1 (by rfl) ⟨225050, by rfl⟩ : syracuseStep 300067 = 450101) B450101
theorem B1020977 : Blo 299831 1020977 := bstep (se 2 (by rfl) ⟨382866, by rfl⟩ : syracuseStep 1020977 = 765733) B765733
theorem B300083 : Blo 299831 300083 := bstep (se 1 (by rfl) ⟨225062, by rfl⟩ : syracuseStep 300083 = 450125) B450125
theorem B300099 : Blo 299831 300099 := bstep (se 1 (by rfl) ⟨225074, by rfl⟩ : syracuseStep 300099 = 450149) B450149
theorem B300115 : Blo 299831 300115 := bstep (se 1 (by rfl) ⟨225086, by rfl⟩ : syracuseStep 300115 = 450173) B450173
theorem B300131 : Blo 299831 300131 := bstep (se 1 (by rfl) ⟨225098, by rfl⟩ : syracuseStep 300131 = 450197) B450197
theorem B300147 : Blo 299831 300147 := bstep (se 1 (by rfl) ⟨225110, by rfl⟩ : syracuseStep 300147 = 450221) B450221
theorem B300163 : Blo 299831 300163 := bstep (se 1 (by rfl) ⟨225122, by rfl⟩ : syracuseStep 300163 = 450245) B450245
theorem B431249 : Blo 299831 431249 := bstep (se 2 (by rfl) ⟨161718, by rfl⟩ : syracuseStep 431249 = 323437) B323437
theorem B300179 : Blo 299831 300179 := bstep (se 1 (by rfl) ⟨225134, by rfl⟩ : syracuseStep 300179 = 450269) B450269
theorem B300195 : Blo 299831 300195 := bstep (se 1 (by rfl) ⟨225146, by rfl⟩ : syracuseStep 300195 = 450293) B450293
theorem B300211 : Blo 299831 300211 := bstep (se 1 (by rfl) ⟨225158, by rfl⟩ : syracuseStep 300211 = 450317) B450317
theorem B300227 : Blo 299831 300227 := bstep (se 1 (by rfl) ⟨225170, by rfl⟩ : syracuseStep 300227 = 450341) B450341
theorem B300243 : Blo 299831 300243 := bstep (se 1 (by rfl) ⟨225182, by rfl⟩ : syracuseStep 300243 = 450365) B450365
theorem B300259 : Blo 299831 300259 := bstep (se 1 (by rfl) ⟨225194, by rfl⟩ : syracuseStep 300259 = 450389) B450389
theorem B2888945 : Blo 299831 2888945 := bstep (se 2 (by rfl) ⟨1083354, by rfl⟩ : syracuseStep 2888945 = 2166709) B2166709
theorem B300275 : Blo 299831 300275 := bstep (se 1 (by rfl) ⟨225206, by rfl⟩ : syracuseStep 300275 = 450413) B450413
theorem B300291 : Blo 299831 300291 := bstep (se 1 (by rfl) ⟨225218, by rfl⟩ : syracuseStep 300291 = 450437) B450437
theorem B431363 : Blo 299831 431363 := bstep (se 1 (by rfl) ⟨323522, by rfl⟩ : syracuseStep 431363 = 647045) B647045
theorem B300307 : Blo 299831 300307 := bstep (se 1 (by rfl) ⟨225230, by rfl⟩ : syracuseStep 300307 = 450461) B450461
theorem B300323 : Blo 299831 300323 := bstep (se 1 (by rfl) ⟨225242, by rfl⟩ : syracuseStep 300323 = 450485) B450485
theorem B300339 : Blo 299831 300339 := bstep (se 1 (by rfl) ⟨225254, by rfl⟩ : syracuseStep 300339 = 450509) B450509
theorem B300355 : Blo 299831 300355 := bstep (se 1 (by rfl) ⟨225266, by rfl⟩ : syracuseStep 300355 = 450533) B450533
theorem B300371 : Blo 299831 300371 := bstep (se 1 (by rfl) ⟨225278, by rfl⟩ : syracuseStep 300371 = 450557) B450557
theorem B431443 : Blo 299831 431443 := bstep (se 1 (by rfl) ⟨323582, by rfl⟩ : syracuseStep 431443 = 647165) B647165
theorem B300387 : Blo 299831 300387 := bstep (se 1 (by rfl) ⟨225290, by rfl⟩ : syracuseStep 300387 = 450581) B450581
theorem B300403 : Blo 299831 300403 := bstep (se 1 (by rfl) ⟨225302, by rfl⟩ : syracuseStep 300403 = 450605) B450605
theorem B300419 : Blo 299831 300419 := bstep (se 1 (by rfl) ⟨225314, by rfl⟩ : syracuseStep 300419 = 450629) B450629
theorem B3478925 : Blo 299831 3478925 := bstep (se 3 (by rfl) ⟨652298, by rfl⟩ : syracuseStep 3478925 = 1304597) B1304597
theorem B300435 : Blo 299831 300435 := bstep (se 1 (by rfl) ⟨225326, by rfl⟩ : syracuseStep 300435 = 450653) B450653
theorem B759203 : Blo 299831 759203 := bstep (se 1 (by rfl) ⟨569402, by rfl⟩ : syracuseStep 759203 = 1138805) B1138805
theorem B300451 : Blo 299831 300451 := bstep (se 1 (by rfl) ⟨225338, by rfl⟩ : syracuseStep 300451 = 450677) B450677
theorem B300467 : Blo 299831 300467 := bstep (se 1 (by rfl) ⟨225350, by rfl⟩ : syracuseStep 300467 = 450701) B450701
theorem B300483 : Blo 299831 300483 := bstep (se 1 (by rfl) ⟨225362, by rfl⟩ : syracuseStep 300483 = 450725) B450725
theorem B300499 : Blo 299831 300499 := bstep (se 1 (by rfl) ⟨225374, by rfl⟩ : syracuseStep 300499 = 450749) B450749
theorem B300515 : Blo 299831 300515 := bstep (se 1 (by rfl) ⟨225386, by rfl⟩ : syracuseStep 300515 = 450773) B450773
theorem B300531 : Blo 299831 300531 := bstep (se 1 (by rfl) ⟨225398, by rfl⟩ : syracuseStep 300531 = 450797) B450797
theorem B300547 : Blo 299831 300547 := bstep (se 1 (by rfl) ⟨225410, by rfl⟩ : syracuseStep 300547 = 450821) B450821
theorem B300563 : Blo 299831 300563 := bstep (se 1 (by rfl) ⟨225422, by rfl⟩ : syracuseStep 300563 = 450845) B450845
theorem B300579 : Blo 299831 300579 := bstep (se 1 (by rfl) ⟨225434, by rfl⟩ : syracuseStep 300579 = 450869) B450869
theorem B1283633 : Blo 299831 1283633 := bstep (se 2 (by rfl) ⟨481362, by rfl⟩ : syracuseStep 1283633 = 962725) B962725
theorem B300595 : Blo 299831 300595 := bstep (se 1 (by rfl) ⟨225446, by rfl⟩ : syracuseStep 300595 = 450893) B450893
theorem B300611 : Blo 299831 300611 := bstep (se 1 (by rfl) ⟨225458, by rfl⟩ : syracuseStep 300611 = 450917) B450917
theorem B1021517 : Blo 299831 1021517 := bstep (se 3 (by rfl) ⟨191534, by rfl⟩ : syracuseStep 1021517 = 383069) B383069
theorem B300627 : Blo 299831 300627 := bstep (se 1 (by rfl) ⟨225470, by rfl⟩ : syracuseStep 300627 = 450941) B450941
theorem B759395 : Blo 299831 759395 := bstep (se 1 (by rfl) ⟨569546, by rfl⟩ : syracuseStep 759395 = 1139093) B1139093
theorem B300643 : Blo 299831 300643 := bstep (se 1 (by rfl) ⟨225482, by rfl⟩ : syracuseStep 300643 = 450965) B450965
theorem B300659 : Blo 299831 300659 := bstep (se 1 (by rfl) ⟨225494, by rfl⟩ : syracuseStep 300659 = 450989) B450989
theorem B300675 : Blo 299831 300675 := bstep (se 1 (by rfl) ⟨225506, by rfl⟩ : syracuseStep 300675 = 451013) B451013
theorem B1021571 : Blo 299831 1021571 := bstep (se 1 (by rfl) ⟨766178, by rfl⟩ : syracuseStep 1021571 = 1532357) B1532357
theorem B1939085 : Blo 299831 1939085 := bstep (se 3 (by rfl) ⟨363578, by rfl⟩ : syracuseStep 1939085 = 727157) B727157
theorem B300691 : Blo 299831 300691 := bstep (se 1 (by rfl) ⟨225518, by rfl⟩ : syracuseStep 300691 = 451037) B451037
theorem B300707 : Blo 299831 300707 := bstep (se 1 (by rfl) ⟨225530, by rfl⟩ : syracuseStep 300707 = 451061) B451061
theorem B300723 : Blo 299831 300723 := bstep (se 1 (by rfl) ⟨225542, by rfl⟩ : syracuseStep 300723 = 451085) B451085
theorem B300739 : Blo 299831 300739 := bstep (se 1 (by rfl) ⟨225554, by rfl⟩ : syracuseStep 300739 = 451109) B451109
theorem B300755 : Blo 299831 300755 := bstep (se 1 (by rfl) ⟨225566, by rfl⟩ : syracuseStep 300755 = 451133) B451133
theorem B300771 : Blo 299831 300771 := bstep (se 1 (by rfl) ⟨225578, by rfl⟩ : syracuseStep 300771 = 451157) B451157
theorem B300787 : Blo 299831 300787 := bstep (se 1 (by rfl) ⟨225590, by rfl⟩ : syracuseStep 300787 = 451181) B451181
theorem B300803 : Blo 299831 300803 := bstep (se 1 (by rfl) ⟨225602, by rfl⟩ : syracuseStep 300803 = 451205) B451205
theorem B300819 : Blo 299831 300819 := bstep (se 1 (by rfl) ⟨225614, by rfl⟩ : syracuseStep 300819 = 451229) B451229
theorem B300835 : Blo 299831 300835 := bstep (se 1 (by rfl) ⟨225626, by rfl⟩ : syracuseStep 300835 = 451253) B451253
theorem B300851 : Blo 299831 300851 := bstep (se 1 (by rfl) ⟨225638, by rfl⟩ : syracuseStep 300851 = 451277) B451277
theorem B300867 : Blo 299831 300867 := bstep (se 1 (by rfl) ⟨225650, by rfl⟩ : syracuseStep 300867 = 451301) B451301
theorem B300883 : Blo 299831 300883 := bstep (se 1 (by rfl) ⟨225662, by rfl⟩ : syracuseStep 300883 = 451325) B451325
theorem B300899 : Blo 299831 300899 := bstep (se 1 (by rfl) ⟨225674, by rfl⟩ : syracuseStep 300899 = 451349) B451349
theorem B857965 : Blo 299831 857965 := bstep (se 3 (by rfl) ⟨160868, by rfl⟩ : syracuseStep 857965 = 321737) B321737
theorem B300915 : Blo 299831 300915 := bstep (se 1 (by rfl) ⟨225686, by rfl⟩ : syracuseStep 300915 = 451373) B451373
theorem B432001 : Blo 299831 432001 := bstep (se 2 (by rfl) ⟨162000, by rfl⟩ : syracuseStep 432001 = 324001) B324001
theorem B300931 : Blo 299831 300931 := bstep (se 1 (by rfl) ⟨225698, by rfl⟩ : syracuseStep 300931 = 451397) B451397
theorem B1021841 : Blo 299831 1021841 := bstep (se 2 (by rfl) ⟨383190, by rfl⟩ : syracuseStep 1021841 = 766381) B766381
theorem B300947 : Blo 299831 300947 := bstep (se 1 (by rfl) ⟨225710, by rfl⟩ : syracuseStep 300947 = 451421) B451421
theorem B300963 : Blo 299831 300963 := bstep (se 1 (by rfl) ⟨225722, by rfl⟩ : syracuseStep 300963 = 451445) B451445
theorem B300979 : Blo 299831 300979 := bstep (se 1 (by rfl) ⟨225734, by rfl⟩ : syracuseStep 300979 = 451469) B451469
theorem B300995 : Blo 299831 300995 := bstep (se 1 (by rfl) ⟨225746, by rfl⟩ : syracuseStep 300995 = 451493) B451493
theorem B301011 : Blo 299831 301011 := bstep (se 1 (by rfl) ⟨225758, by rfl⟩ : syracuseStep 301011 = 451517) B451517
theorem B301027 : Blo 299831 301027 := bstep (se 1 (by rfl) ⟨225770, by rfl⟩ : syracuseStep 301027 = 451541) B451541
theorem B301043 : Blo 299831 301043 := bstep (se 1 (by rfl) ⟨225782, by rfl⟩ : syracuseStep 301043 = 451565) B451565
theorem B301059 : Blo 299831 301059 := bstep (se 1 (by rfl) ⟨225794, by rfl⟩ : syracuseStep 301059 = 451589) B451589
theorem B923665 : Blo 299831 923665 := bstep (se 2 (by rfl) ⟨346374, by rfl⟩ : syracuseStep 923665 = 692749) B692749
theorem B301075 : Blo 299831 301075 := bstep (se 1 (by rfl) ⟨225806, by rfl⟩ : syracuseStep 301075 = 451613) B451613
theorem B301091 : Blo 299831 301091 := bstep (se 1 (by rfl) ⟨225818, by rfl⟩ : syracuseStep 301091 = 451637) B451637
theorem B301107 : Blo 299831 301107 := bstep (se 1 (by rfl) ⟨225830, by rfl⟩ : syracuseStep 301107 = 451661) B451661
theorem B301123 : Blo 299831 301123 := bstep (se 1 (by rfl) ⟨225842, by rfl⟩ : syracuseStep 301123 = 451685) B451685
theorem B301139 : Blo 299831 301139 := bstep (se 1 (by rfl) ⟨225854, by rfl⟩ : syracuseStep 301139 = 451709) B451709
theorem B301155 : Blo 299831 301155 := bstep (se 1 (by rfl) ⟨225866, by rfl⟩ : syracuseStep 301155 = 451733) B451733
theorem B301171 : Blo 299831 301171 := bstep (se 1 (by rfl) ⟨225878, by rfl⟩ : syracuseStep 301171 = 451757) B451757
theorem B301187 : Blo 299831 301187 := bstep (se 1 (by rfl) ⟨225890, by rfl⟩ : syracuseStep 301187 = 451781) B451781
theorem B301203 : Blo 299831 301203 := bstep (se 1 (by rfl) ⟨225902, by rfl⟩ : syracuseStep 301203 = 451805) B451805
theorem B301219 : Blo 299831 301219 := bstep (se 1 (by rfl) ⟨225914, by rfl⟩ : syracuseStep 301219 = 451829) B451829
theorem B1153187 : Blo 299831 1153187 := bstep (se 1 (by rfl) ⟨864890, by rfl⟩ : syracuseStep 1153187 = 1729781) B1729781
theorem B301235 : Blo 299831 301235 := bstep (se 1 (by rfl) ⟨225926, by rfl⟩ : syracuseStep 301235 = 451853) B451853
theorem B301251 : Blo 299831 301251 := bstep (se 1 (by rfl) ⟨225938, by rfl⟩ : syracuseStep 301251 = 451877) B451877
theorem B301267 : Blo 299831 301267 := bstep (se 1 (by rfl) ⟨225950, by rfl⟩ : syracuseStep 301267 = 451901) B451901
theorem B301283 : Blo 299831 301283 := bstep (se 1 (by rfl) ⟨225962, by rfl⟩ : syracuseStep 301283 = 451925) B451925
theorem B301299 : Blo 299831 301299 := bstep (se 1 (by rfl) ⟨225974, by rfl⟩ : syracuseStep 301299 = 451949) B451949
theorem B301315 : Blo 299831 301315 := bstep (se 1 (by rfl) ⟨225986, by rfl⟩ : syracuseStep 301315 = 451973) B451973
theorem B301331 : Blo 299831 301331 := bstep (se 1 (by rfl) ⟨225998, by rfl⟩ : syracuseStep 301331 = 451997) B451997
theorem B301347 : Blo 299831 301347 := bstep (se 1 (by rfl) ⟨226010, by rfl⟩ : syracuseStep 301347 = 452021) B452021
theorem B301363 : Blo 299831 301363 := bstep (se 1 (by rfl) ⟨226022, by rfl⟩ : syracuseStep 301363 = 452045) B452045
theorem B301379 : Blo 299831 301379 := bstep (se 1 (by rfl) ⟨226034, by rfl⟩ : syracuseStep 301379 = 452069) B452069
theorem B301395 : Blo 299831 301395 := bstep (se 1 (by rfl) ⟨226046, by rfl⟩ : syracuseStep 301395 = 452093) B452093
theorem B301411 : Blo 299831 301411 := bstep (se 1 (by rfl) ⟨226058, by rfl⟩ : syracuseStep 301411 = 452117) B452117
theorem B301427 : Blo 299831 301427 := bstep (se 1 (by rfl) ⟨226070, by rfl⟩ : syracuseStep 301427 = 452141) B452141
theorem B301443 : Blo 299831 301443 := bstep (se 1 (by rfl) ⟨226082, by rfl⟩ : syracuseStep 301443 = 452165) B452165
theorem B301459 : Blo 299831 301459 := bstep (se 1 (by rfl) ⟨226094, by rfl⟩ : syracuseStep 301459 = 452189) B452189
theorem B301475 : Blo 299831 301475 := bstep (se 1 (by rfl) ⟨226106, by rfl⟩ : syracuseStep 301475 = 452213) B452213
theorem B1022381 : Blo 299831 1022381 := bstep (se 3 (by rfl) ⟨191696, by rfl⟩ : syracuseStep 1022381 = 383393) B383393
theorem B301491 : Blo 299831 301491 := bstep (se 1 (by rfl) ⟨226118, by rfl⟩ : syracuseStep 301491 = 452237) B452237
theorem B301507 : Blo 299831 301507 := bstep (se 1 (by rfl) ⟨226130, by rfl⟩ : syracuseStep 301507 = 452261) B452261
theorem B301523 : Blo 299831 301523 := bstep (se 1 (by rfl) ⟨226142, by rfl⟩ : syracuseStep 301523 = 452285) B452285
theorem B301539 : Blo 299831 301539 := bstep (se 1 (by rfl) ⟨226154, by rfl⟩ : syracuseStep 301539 = 452309) B452309
theorem B1022435 : Blo 299831 1022435 := bstep (se 1 (by rfl) ⟨766826, by rfl⟩ : syracuseStep 1022435 = 1533653) B1533653
theorem B301555 : Blo 299831 301555 := bstep (se 1 (by rfl) ⟨226166, by rfl⟩ : syracuseStep 301555 = 452333) B452333
theorem B301571 : Blo 299831 301571 := bstep (se 1 (by rfl) ⟨226178, by rfl⟩ : syracuseStep 301571 = 452357) B452357
theorem B760337 : Blo 299831 760337 := bstep (se 2 (by rfl) ⟨285126, by rfl⟩ : syracuseStep 760337 = 570253) B570253
theorem B301587 : Blo 299831 301587 := bstep (se 1 (by rfl) ⟨226190, by rfl⟩ : syracuseStep 301587 = 452381) B452381
theorem B301603 : Blo 299831 301603 := bstep (se 1 (by rfl) ⟨226202, by rfl⟩ : syracuseStep 301603 = 452405) B452405
theorem B301619 : Blo 299831 301619 := bstep (se 1 (by rfl) ⟨226214, by rfl⟩ : syracuseStep 301619 = 452429) B452429
theorem B760387 : Blo 299831 760387 := bstep (se 1 (by rfl) ⟨570290, by rfl⟩ : syracuseStep 760387 = 1140581) B1140581
theorem B301635 : Blo 299831 301635 := bstep (se 1 (by rfl) ⟨226226, by rfl⟩ : syracuseStep 301635 = 452453) B452453
theorem B301651 : Blo 299831 301651 := bstep (se 1 (by rfl) ⟨226238, by rfl⟩ : syracuseStep 301651 = 452477) B452477
theorem B301667 : Blo 299831 301667 := bstep (se 1 (by rfl) ⟨226250, by rfl⟩ : syracuseStep 301667 = 452501) B452501
theorem B301683 : Blo 299831 301683 := bstep (se 1 (by rfl) ⟨226262, by rfl⟩ : syracuseStep 301683 = 452525) B452525
theorem B301699 : Blo 299831 301699 := bstep (se 1 (by rfl) ⟨226274, by rfl⟩ : syracuseStep 301699 = 452549) B452549
theorem B301715 : Blo 299831 301715 := bstep (se 1 (by rfl) ⟨226286, by rfl⟩ : syracuseStep 301715 = 452573) B452573
theorem B465569 : Blo 299831 465569 := bstep (se 2 (by rfl) ⟨174588, by rfl⟩ : syracuseStep 465569 = 349177) B349177
theorem B301731 : Blo 299831 301731 := bstep (se 1 (by rfl) ⟨226298, by rfl⟩ : syracuseStep 301731 = 452597) B452597
theorem B301747 : Blo 299831 301747 := bstep (se 1 (by rfl) ⟨226310, by rfl⟩ : syracuseStep 301747 = 452621) B452621
theorem B301763 : Blo 299831 301763 := bstep (se 1 (by rfl) ⟨226322, by rfl⟩ : syracuseStep 301763 = 452645) B452645
theorem B760529 : Blo 299831 760529 := bstep (se 2 (by rfl) ⟨285198, by rfl⟩ : syracuseStep 760529 = 570397) B570397
theorem B301779 : Blo 299831 301779 := bstep (se 1 (by rfl) ⟨226334, by rfl⟩ : syracuseStep 301779 = 452669) B452669
theorem B301795 : Blo 299831 301795 := bstep (se 1 (by rfl) ⟨226346, by rfl⟩ : syracuseStep 301795 = 452693) B452693
theorem B1022705 : Blo 299831 1022705 := bstep (se 2 (by rfl) ⟨383514, by rfl⟩ : syracuseStep 1022705 = 767029) B767029
theorem B301811 : Blo 299831 301811 := bstep (se 1 (by rfl) ⟨226358, by rfl⟩ : syracuseStep 301811 = 452717) B452717
theorem B301827 : Blo 299831 301827 := bstep (se 1 (by rfl) ⟨226370, by rfl⟩ : syracuseStep 301827 = 452741) B452741
theorem B727811 : Blo 299831 727811 := bstep (se 1 (by rfl) ⟨545858, by rfl⟩ : syracuseStep 727811 = 1091717) B1091717
theorem B301843 : Blo 299831 301843 := bstep (se 1 (by rfl) ⟨226382, by rfl⟩ : syracuseStep 301843 = 452765) B452765
theorem B301859 : Blo 299831 301859 := bstep (se 1 (by rfl) ⟨226394, by rfl⟩ : syracuseStep 301859 = 452789) B452789
theorem B301875 : Blo 299831 301875 := bstep (se 1 (by rfl) ⟨226406, by rfl⟩ : syracuseStep 301875 = 452813) B452813
theorem B301891 : Blo 299831 301891 := bstep (se 1 (by rfl) ⟨226418, by rfl⟩ : syracuseStep 301891 = 452837) B452837
theorem B301907 : Blo 299831 301907 := bstep (se 1 (by rfl) ⟨226430, by rfl⟩ : syracuseStep 301907 = 452861) B452861
theorem B301923 : Blo 299831 301923 := bstep (se 1 (by rfl) ⟨226442, by rfl⟩ : syracuseStep 301923 = 452885) B452885
theorem B301939 : Blo 299831 301939 := bstep (se 1 (by rfl) ⟨226454, by rfl⟩ : syracuseStep 301939 = 452909) B452909
theorem B301955 : Blo 299831 301955 := bstep (se 1 (by rfl) ⟨226466, by rfl⟩ : syracuseStep 301955 = 452933) B452933
theorem B859025 : Blo 299831 859025 := bstep (se 2 (by rfl) ⟨322134, by rfl⟩ : syracuseStep 859025 = 644269) B644269
theorem B301971 : Blo 299831 301971 := bstep (se 1 (by rfl) ⟨226478, by rfl⟩ : syracuseStep 301971 = 452957) B452957
theorem B301987 : Blo 299831 301987 := bstep (se 1 (by rfl) ⟨226490, by rfl⟩ : syracuseStep 301987 = 452981) B452981
theorem B302003 : Blo 299831 302003 := bstep (se 1 (by rfl) ⟨226502, by rfl⟩ : syracuseStep 302003 = 453005) B453005
theorem B302019 : Blo 299831 302019 := bstep (se 1 (by rfl) ⟨226514, by rfl⟩ : syracuseStep 302019 = 453029) B453029
theorem B302035 : Blo 299831 302035 := bstep (se 1 (by rfl) ⟨226526, by rfl⟩ : syracuseStep 302035 = 453053) B453053
theorem B302051 : Blo 299831 302051 := bstep (se 1 (by rfl) ⟨226538, by rfl⟩ : syracuseStep 302051 = 453077) B453077
theorem B302067 : Blo 299831 302067 := bstep (se 1 (by rfl) ⟨226550, by rfl⟩ : syracuseStep 302067 = 453101) B453101
theorem B302083 : Blo 299831 302083 := bstep (se 1 (by rfl) ⟨226562, by rfl⟩ : syracuseStep 302083 = 453125) B453125
theorem B302099 : Blo 299831 302099 := bstep (se 1 (by rfl) ⟨226574, by rfl⟩ : syracuseStep 302099 = 453149) B453149
theorem B302115 : Blo 299831 302115 := bstep (se 1 (by rfl) ⟨226586, by rfl⟩ : syracuseStep 302115 = 453173) B453173
theorem B302131 : Blo 299831 302131 := bstep (se 1 (by rfl) ⟨226598, by rfl⟩ : syracuseStep 302131 = 453197) B453197
theorem B302147 : Blo 299831 302147 := bstep (se 1 (by rfl) ⟨226610, by rfl⟩ : syracuseStep 302147 = 453221) B453221
theorem B302163 : Blo 299831 302163 := bstep (se 1 (by rfl) ⟨226622, by rfl⟩ : syracuseStep 302163 = 453245) B453245
theorem B302179 : Blo 299831 302179 := bstep (se 1 (by rfl) ⟨226634, by rfl⟩ : syracuseStep 302179 = 453269) B453269
theorem B302195 : Blo 299831 302195 := bstep (se 1 (by rfl) ⟨226646, by rfl⟩ : syracuseStep 302195 = 453293) B453293
theorem B302211 : Blo 299831 302211 := bstep (se 1 (by rfl) ⟨226658, by rfl⟩ : syracuseStep 302211 = 453317) B453317
theorem B302227 : Blo 299831 302227 := bstep (se 1 (by rfl) ⟨226670, by rfl⟩ : syracuseStep 302227 = 453341) B453341
theorem B302243 : Blo 299831 302243 := bstep (se 1 (by rfl) ⟨226682, by rfl⟩ : syracuseStep 302243 = 453365) B453365
theorem B302259 : Blo 299831 302259 := bstep (se 1 (by rfl) ⟨226694, by rfl⟩ : syracuseStep 302259 = 453389) B453389
theorem B302275 : Blo 299831 302275 := bstep (se 1 (by rfl) ⟨226706, by rfl⟩ : syracuseStep 302275 = 453413) B453413
theorem B302291 : Blo 299831 302291 := bstep (se 1 (by rfl) ⟨226718, by rfl⟩ : syracuseStep 302291 = 453437) B453437
theorem B302307 : Blo 299831 302307 := bstep (se 1 (by rfl) ⟨226730, by rfl⟩ : syracuseStep 302307 = 453461) B453461
theorem B302323 : Blo 299831 302323 := bstep (se 1 (by rfl) ⟨226742, by rfl⟩ : syracuseStep 302323 = 453485) B453485
theorem B302339 : Blo 299831 302339 := bstep (se 1 (by rfl) ⟨226754, by rfl⟩ : syracuseStep 302339 = 453509) B453509
theorem B1023245 : Blo 299831 1023245 := bstep (se 3 (by rfl) ⟨191858, by rfl⟩ : syracuseStep 1023245 = 383717) B383717
theorem B302355 : Blo 299831 302355 := bstep (se 1 (by rfl) ⟨226766, by rfl⟩ : syracuseStep 302355 = 453533) B453533
theorem B302371 : Blo 299831 302371 := bstep (se 1 (by rfl) ⟨226778, by rfl⟩ : syracuseStep 302371 = 453557) B453557
theorem B302387 : Blo 299831 302387 := bstep (se 1 (by rfl) ⟨226790, by rfl⟩ : syracuseStep 302387 = 453581) B453581
theorem B302403 : Blo 299831 302403 := bstep (se 1 (by rfl) ⟨226802, by rfl⟩ : syracuseStep 302403 = 453605) B453605
theorem B1023299 : Blo 299831 1023299 := bstep (se 1 (by rfl) ⟨767474, by rfl⟩ : syracuseStep 1023299 = 1534949) B1534949
theorem B302419 : Blo 299831 302419 := bstep (se 1 (by rfl) ⟨226814, by rfl⟩ : syracuseStep 302419 = 453629) B453629
theorem B302435 : Blo 299831 302435 := bstep (se 1 (by rfl) ⟨226826, by rfl⟩ : syracuseStep 302435 = 453653) B453653
theorem B302451 : Blo 299831 302451 := bstep (se 1 (by rfl) ⟨226838, by rfl⟩ : syracuseStep 302451 = 453677) B453677
theorem B302467 : Blo 299831 302467 := bstep (se 1 (by rfl) ⟨226850, by rfl⟩ : syracuseStep 302467 = 453701) B453701
theorem B302483 : Blo 299831 302483 := bstep (se 1 (by rfl) ⟨226862, by rfl⟩ : syracuseStep 302483 = 453725) B453725
theorem B302499 : Blo 299831 302499 := bstep (se 1 (by rfl) ⟨226874, by rfl⟩ : syracuseStep 302499 = 453749) B453749
theorem B302515 : Blo 299831 302515 := bstep (se 1 (by rfl) ⟨226886, by rfl⟩ : syracuseStep 302515 = 453773) B453773
theorem B302531 : Blo 299831 302531 := bstep (se 1 (by rfl) ⟨226898, by rfl⟩ : syracuseStep 302531 = 453797) B453797
theorem B302547 : Blo 299831 302547 := bstep (se 1 (by rfl) ⟨226910, by rfl⟩ : syracuseStep 302547 = 453821) B453821
theorem B302563 : Blo 299831 302563 := bstep (se 1 (by rfl) ⟨226922, by rfl⟩ : syracuseStep 302563 = 453845) B453845
theorem B1711601 : Blo 299831 1711601 := bstep (se 2 (by rfl) ⟨641850, by rfl⟩ : syracuseStep 1711601 = 1283701) B1283701
theorem B302579 : Blo 299831 302579 := bstep (se 1 (by rfl) ⟨226934, by rfl⟩ : syracuseStep 302579 = 453869) B453869
theorem B302595 : Blo 299831 302595 := bstep (se 1 (by rfl) ⟨226946, by rfl⟩ : syracuseStep 302595 = 453893) B453893
theorem B728579 : Blo 299831 728579 := bstep (se 1 (by rfl) ⟨546434, by rfl⟩ : syracuseStep 728579 = 1092869) B1092869
theorem B302611 : Blo 299831 302611 := bstep (se 1 (by rfl) ⟨226958, by rfl⟩ : syracuseStep 302611 = 453917) B453917
theorem B302627 : Blo 299831 302627 := bstep (se 1 (by rfl) ⟨226970, by rfl⟩ : syracuseStep 302627 = 453941) B453941
theorem B859697 : Blo 299831 859697 := bstep (se 2 (by rfl) ⟨322386, by rfl⟩ : syracuseStep 859697 = 644773) B644773
theorem B302643 : Blo 299831 302643 := bstep (se 1 (by rfl) ⟨226982, by rfl⟩ : syracuseStep 302643 = 453965) B453965
theorem B302659 : Blo 299831 302659 := bstep (se 1 (by rfl) ⟨226994, by rfl⟩ : syracuseStep 302659 = 453989) B453989
theorem B1023569 : Blo 299831 1023569 := bstep (se 2 (by rfl) ⟨383838, by rfl⟩ : syracuseStep 1023569 = 767677) B767677
theorem B302675 : Blo 299831 302675 := bstep (se 1 (by rfl) ⟨227006, by rfl⟩ : syracuseStep 302675 = 454013) B454013
theorem B302691 : Blo 299831 302691 := bstep (se 1 (by rfl) ⟨227018, by rfl⟩ : syracuseStep 302691 = 454037) B454037
theorem B302707 : Blo 299831 302707 := bstep (se 1 (by rfl) ⟨227030, by rfl⟩ : syracuseStep 302707 = 454061) B454061
theorem B302723 : Blo 299831 302723 := bstep (se 1 (by rfl) ⟨227042, by rfl⟩ : syracuseStep 302723 = 454085) B454085
theorem B302739 : Blo 299831 302739 := bstep (se 1 (by rfl) ⟨227054, by rfl⟩ : syracuseStep 302739 = 454109) B454109
theorem B302755 : Blo 299831 302755 := bstep (se 1 (by rfl) ⟨227066, by rfl⟩ : syracuseStep 302755 = 454133) B454133
theorem B761521 : Blo 299831 761521 := bstep (se 2 (by rfl) ⟨285570, by rfl⟩ : syracuseStep 761521 = 571141) B571141
theorem B302771 : Blo 299831 302771 := bstep (se 1 (by rfl) ⟨227078, by rfl⟩ : syracuseStep 302771 = 454157) B454157
theorem B302787 : Blo 299831 302787 := bstep (se 1 (by rfl) ⟨227090, by rfl⟩ : syracuseStep 302787 = 454181) B454181
theorem B302803 : Blo 299831 302803 := bstep (se 1 (by rfl) ⟨227102, by rfl⟩ : syracuseStep 302803 = 454205) B454205
theorem B302819 : Blo 299831 302819 := bstep (se 1 (by rfl) ⟨227114, by rfl⟩ : syracuseStep 302819 = 454229) B454229
theorem B302835 : Blo 299831 302835 := bstep (se 1 (by rfl) ⟨227126, by rfl⟩ : syracuseStep 302835 = 454253) B454253
theorem B302851 : Blo 299831 302851 := bstep (se 1 (by rfl) ⟨227138, by rfl⟩ : syracuseStep 302851 = 454277) B454277
theorem B1089293 : Blo 299831 1089293 := bstep (se 3 (by rfl) ⟨204242, by rfl⟩ : syracuseStep 1089293 = 408485) B408485
theorem B302867 : Blo 299831 302867 := bstep (se 1 (by rfl) ⟨227150, by rfl⟩ : syracuseStep 302867 = 454301) B454301
theorem B302883 : Blo 299831 302883 := bstep (se 1 (by rfl) ⟨227162, by rfl⟩ : syracuseStep 302883 = 454325) B454325
theorem B302899 : Blo 299831 302899 := bstep (se 1 (by rfl) ⟨227174, by rfl⟩ : syracuseStep 302899 = 454349) B454349
theorem B302915 : Blo 299831 302915 := bstep (se 1 (by rfl) ⟨227186, by rfl⟩ : syracuseStep 302915 = 454373) B454373
theorem B302931 : Blo 299831 302931 := bstep (se 1 (by rfl) ⟨227198, by rfl⟩ : syracuseStep 302931 = 454397) B454397
theorem B302947 : Blo 299831 302947 := bstep (se 1 (by rfl) ⟨227210, by rfl⟩ : syracuseStep 302947 = 454421) B454421
theorem B302963 : Blo 299831 302963 := bstep (se 1 (by rfl) ⟨227222, by rfl⟩ : syracuseStep 302963 = 454445) B454445
theorem B302979 : Blo 299831 302979 := bstep (se 1 (by rfl) ⟨227234, by rfl⟩ : syracuseStep 302979 = 454469) B454469
theorem B302995 : Blo 299831 302995 := bstep (se 1 (by rfl) ⟨227246, by rfl⟩ : syracuseStep 302995 = 454493) B454493
theorem B303011 : Blo 299831 303011 := bstep (se 1 (by rfl) ⟨227258, by rfl⟩ : syracuseStep 303011 = 454517) B454517
theorem B434099 : Blo 299831 434099 := bstep (se 1 (by rfl) ⟨325574, by rfl⟩ : syracuseStep 434099 = 651149) B651149
theorem B303027 : Blo 299831 303027 := bstep (se 1 (by rfl) ⟨227270, by rfl⟩ : syracuseStep 303027 = 454541) B454541
theorem B761795 : Blo 299831 761795 := bstep (se 1 (by rfl) ⟨571346, by rfl⟩ : syracuseStep 761795 = 1142693) B1142693
theorem B303043 : Blo 299831 303043 := bstep (se 1 (by rfl) ⟨227282, by rfl⟩ : syracuseStep 303043 = 454565) B454565
theorem B1286093 : Blo 299831 1286093 := bstep (se 3 (by rfl) ⟨241142, by rfl⟩ : syracuseStep 1286093 = 482285) B482285
theorem B303059 : Blo 299831 303059 := bstep (se 1 (by rfl) ⟨227294, by rfl⟩ : syracuseStep 303059 = 454589) B454589
theorem B303075 : Blo 299831 303075 := bstep (se 1 (by rfl) ⟨227306, by rfl⟩ : syracuseStep 303075 = 454613) B454613
theorem B303091 : Blo 299831 303091 := bstep (se 1 (by rfl) ⟨227318, by rfl⟩ : syracuseStep 303091 = 454637) B454637
theorem B303107 : Blo 299831 303107 := bstep (se 1 (by rfl) ⟨227330, by rfl⟩ : syracuseStep 303107 = 454661) B454661
theorem B303123 : Blo 299831 303123 := bstep (se 1 (by rfl) ⟨227342, by rfl⟩ : syracuseStep 303123 = 454685) B454685
theorem B303139 : Blo 299831 303139 := bstep (se 1 (by rfl) ⟨227354, by rfl⟩ : syracuseStep 303139 = 454709) B454709
theorem B729137 : Blo 299831 729137 := bstep (se 2 (by rfl) ⟨273426, by rfl⟩ : syracuseStep 729137 = 546853) B546853
theorem B303155 : Blo 299831 303155 := bstep (se 1 (by rfl) ⟨227366, by rfl⟩ : syracuseStep 303155 = 454733) B454733
theorem B303171 : Blo 299831 303171 := bstep (se 1 (by rfl) ⟨227378, by rfl⟩ : syracuseStep 303171 = 454757) B454757
theorem B303187 : Blo 299831 303187 := bstep (se 1 (by rfl) ⟨227390, by rfl⟩ : syracuseStep 303187 = 454781) B454781
theorem B303203 : Blo 299831 303203 := bstep (se 1 (by rfl) ⟨227402, by rfl⟩ : syracuseStep 303203 = 454805) B454805
theorem B1024109 : Blo 299831 1024109 := bstep (se 3 (by rfl) ⟨192020, by rfl⟩ : syracuseStep 1024109 = 384041) B384041
theorem B303219 : Blo 299831 303219 := bstep (se 1 (by rfl) ⟨227414, by rfl⟩ : syracuseStep 303219 = 454829) B454829
theorem B761987 : Blo 299831 761987 := bstep (se 1 (by rfl) ⟨571490, by rfl⟩ : syracuseStep 761987 = 1142981) B1142981
theorem B303235 : Blo 299831 303235 := bstep (se 1 (by rfl) ⟨227426, by rfl⟩ : syracuseStep 303235 = 454853) B454853
theorem B5218445 : Blo 299831 5218445 := bstep (se 3 (by rfl) ⟨978458, by rfl⟩ : syracuseStep 5218445 = 1956917) B1956917
theorem B303251 : Blo 299831 303251 := bstep (se 1 (by rfl) ⟨227438, by rfl⟩ : syracuseStep 303251 = 454877) B454877
theorem B1220771 : Blo 299831 1220771 := bstep (se 1 (by rfl) ⟨915578, by rfl⟩ : syracuseStep 1220771 = 1831157) B1831157
theorem B303267 : Blo 299831 303267 := bstep (se 1 (by rfl) ⟨227450, by rfl⟩ : syracuseStep 303267 = 454901) B454901
theorem B1024163 : Blo 299831 1024163 := bstep (se 1 (by rfl) ⟨768122, by rfl⟩ : syracuseStep 1024163 = 1536245) B1536245
theorem B2072753 : Blo 299831 2072753 := bstep (se 2 (by rfl) ⟨777282, by rfl⟩ : syracuseStep 2072753 = 1554565) B1554565
theorem B303283 : Blo 299831 303283 := bstep (se 1 (by rfl) ⟨227462, by rfl⟩ : syracuseStep 303283 = 454925) B454925
theorem B303299 : Blo 299831 303299 := bstep (se 1 (by rfl) ⟨227474, by rfl⟩ : syracuseStep 303299 = 454949) B454949
theorem B303315 : Blo 299831 303315 := bstep (se 1 (by rfl) ⟨227486, by rfl⟩ : syracuseStep 303315 = 454973) B454973
theorem B303331 : Blo 299831 303331 := bstep (se 1 (by rfl) ⟨227498, by rfl⟩ : syracuseStep 303331 = 454997) B454997
theorem B303347 : Blo 299831 303347 := bstep (se 1 (by rfl) ⟨227510, by rfl⟩ : syracuseStep 303347 = 455021) B455021
theorem B303363 : Blo 299831 303363 := bstep (se 1 (by rfl) ⟨227522, by rfl⟩ : syracuseStep 303363 = 455045) B455045
theorem B303379 : Blo 299831 303379 := bstep (se 1 (by rfl) ⟨227534, by rfl⟩ : syracuseStep 303379 = 455069) B455069
theorem B1286435 : Blo 299831 1286435 := bstep (se 1 (by rfl) ⟨964826, by rfl⟩ : syracuseStep 1286435 = 1929653) B1929653
theorem B303395 : Blo 299831 303395 := bstep (se 1 (by rfl) ⟨227546, by rfl⟩ : syracuseStep 303395 = 455093) B455093
theorem B303411 : Blo 299831 303411 := bstep (se 1 (by rfl) ⟨227558, by rfl⟩ : syracuseStep 303411 = 455117) B455117
theorem B860483 : Blo 299831 860483 := bstep (se 1 (by rfl) ⟨645362, by rfl⟩ : syracuseStep 860483 = 1290725) B1290725
theorem B303427 : Blo 299831 303427 := bstep (se 1 (by rfl) ⟨227570, by rfl⟩ : syracuseStep 303427 = 455141) B455141
theorem B729425 : Blo 299831 729425 := bstep (se 2 (by rfl) ⟨273534, by rfl⟩ : syracuseStep 729425 = 547069) B547069
theorem B303443 : Blo 299831 303443 := bstep (se 1 (by rfl) ⟨227582, by rfl⟩ : syracuseStep 303443 = 455165) B455165
theorem B303459 : Blo 299831 303459 := bstep (se 1 (by rfl) ⟨227594, by rfl⟩ : syracuseStep 303459 = 455189) B455189
theorem B303475 : Blo 299831 303475 := bstep (se 1 (by rfl) ⟨227606, by rfl⟩ : syracuseStep 303475 = 455213) B455213
theorem B303491 : Blo 299831 303491 := bstep (se 1 (by rfl) ⟨227618, by rfl⟩ : syracuseStep 303491 = 455237) B455237
theorem B303507 : Blo 299831 303507 := bstep (se 1 (by rfl) ⟨227630, by rfl⟩ : syracuseStep 303507 = 455261) B455261
theorem B303523 : Blo 299831 303523 := bstep (se 1 (by rfl) ⟨227642, by rfl⟩ : syracuseStep 303523 = 455285) B455285
theorem B1024433 : Blo 299831 1024433 := bstep (se 2 (by rfl) ⟨384162, by rfl⟩ : syracuseStep 1024433 = 768325) B768325
theorem B303539 : Blo 299831 303539 := bstep (se 1 (by rfl) ⟨227654, by rfl⟩ : syracuseStep 303539 = 455309) B455309
theorem B303555 : Blo 299831 303555 := bstep (se 1 (by rfl) ⟨227666, by rfl⟩ : syracuseStep 303555 = 455333) B455333
theorem B303571 : Blo 299831 303571 := bstep (se 1 (by rfl) ⟨227678, by rfl⟩ : syracuseStep 303571 = 455357) B455357
theorem B303587 : Blo 299831 303587 := bstep (se 1 (by rfl) ⟨227690, by rfl⟩ : syracuseStep 303587 = 455381) B455381
theorem B303603 : Blo 299831 303603 := bstep (se 1 (by rfl) ⟨227702, by rfl⟩ : syracuseStep 303603 = 455405) B455405
theorem B303619 : Blo 299831 303619 := bstep (se 1 (by rfl) ⟨227714, by rfl⟩ : syracuseStep 303619 = 455429) B455429
theorem B303635 : Blo 299831 303635 := bstep (se 1 (by rfl) ⟨227726, by rfl⟩ : syracuseStep 303635 = 455453) B455453
theorem B303651 : Blo 299831 303651 := bstep (se 1 (by rfl) ⟨227738, by rfl⟩ : syracuseStep 303651 = 455477) B455477
theorem B303667 : Blo 299831 303667 := bstep (se 1 (by rfl) ⟨227750, by rfl⟩ : syracuseStep 303667 = 455501) B455501
theorem B303683 : Blo 299831 303683 := bstep (se 1 (by rfl) ⟨227762, by rfl⟩ : syracuseStep 303683 = 455525) B455525
theorem B303699 : Blo 299831 303699 := bstep (se 1 (by rfl) ⟨227774, by rfl⟩ : syracuseStep 303699 = 455549) B455549
theorem B303715 : Blo 299831 303715 := bstep (se 1 (by rfl) ⟨227786, by rfl⟩ : syracuseStep 303715 = 455573) B455573
theorem B434803 : Blo 299831 434803 := bstep (se 1 (by rfl) ⟨326102, by rfl⟩ : syracuseStep 434803 = 652205) B652205
theorem B303731 : Blo 299831 303731 := bstep (se 1 (by rfl) ⟨227798, by rfl⟩ : syracuseStep 303731 = 455597) B455597
theorem B303747 : Blo 299831 303747 := bstep (se 1 (by rfl) ⟨227810, by rfl⟩ : syracuseStep 303747 = 455621) B455621
theorem B860813 : Blo 299831 860813 := bstep (se 3 (by rfl) ⟨161402, by rfl⟩ : syracuseStep 860813 = 322805) B322805
theorem B303763 : Blo 299831 303763 := bstep (se 1 (by rfl) ⟨227822, by rfl⟩ : syracuseStep 303763 = 455645) B455645
theorem B303779 : Blo 299831 303779 := bstep (se 1 (by rfl) ⟨227834, by rfl⟩ : syracuseStep 303779 = 455669) B455669
theorem B1548977 : Blo 299831 1548977 := bstep (se 2 (by rfl) ⟨580866, by rfl⟩ : syracuseStep 1548977 = 1161733) B1161733
theorem B303795 : Blo 299831 303795 := bstep (se 1 (by rfl) ⟨227846, by rfl⟩ : syracuseStep 303795 = 455693) B455693
theorem B303811 : Blo 299831 303811 := bstep (se 1 (by rfl) ⟨227858, by rfl⟩ : syracuseStep 303811 = 455717) B455717
theorem B860881 : Blo 299831 860881 := bstep (se 2 (by rfl) ⟨322830, by rfl⟩ : syracuseStep 860881 = 645661) B645661
theorem B303827 : Blo 299831 303827 := bstep (se 1 (by rfl) ⟨227870, by rfl⟩ : syracuseStep 303827 = 455741) B455741
theorem B3842801 : Blo 299831 3842801 := bstep (se 2 (by rfl) ⟨1441050, by rfl⟩ : syracuseStep 3842801 = 2882101) B2882101
theorem B434963 : Blo 299831 434963 := bstep (se 1 (by rfl) ⟨326222, by rfl⟩ : syracuseStep 434963 = 652445) B652445
theorem B1713059 : Blo 299831 1713059 := bstep (se 1 (by rfl) ⟨1284794, by rfl⟩ : syracuseStep 1713059 = 2569589) B2569589
theorem B1024973 : Blo 299831 1024973 := bstep (se 3 (by rfl) ⟨192182, by rfl⟩ : syracuseStep 1024973 = 384365) B384365
theorem B861155 : Blo 299831 861155 := bstep (se 1 (by rfl) ⟨645866, by rfl⟩ : syracuseStep 861155 = 1291733) B1291733
theorem B1025027 : Blo 299831 1025027 := bstep (se 1 (by rfl) ⟨768770, by rfl⟩ : syracuseStep 1025027 = 1537541) B1537541
theorem B762929 : Blo 299831 762929 := bstep (se 2 (by rfl) ⟨286098, by rfl⟩ : syracuseStep 762929 = 572197) B572197
theorem B762979 : Blo 299831 762979 := bstep (se 1 (by rfl) ⟨572234, by rfl⟩ : syracuseStep 762979 = 1144469) B1144469
theorem B763121 : Blo 299831 763121 := bstep (se 2 (by rfl) ⟨286170, by rfl⟩ : syracuseStep 763121 = 572341) B572341
theorem B1025297 : Blo 299831 1025297 := bstep (se 2 (by rfl) ⟨384486, by rfl⟩ : syracuseStep 1025297 = 768973) B768973
theorem B304435 : Blo 299831 304435 := bstep (se 1 (by rfl) ⟨228326, by rfl⟩ : syracuseStep 304435 = 456653) B456653
theorem B2434373 : Blo 299831 2434373 := bstep (se 4 (by rfl) ⟨228222, by rfl⟩ : syracuseStep 2434373 = 456445) B456445
theorem B337315 : Blo 299831 337315 := bstep (se 1 (by rfl) ⟨252986, by rfl⟩ : syracuseStep 337315 = 505973) B505973
theorem B2991629 : Blo 299831 2991629 := bstep (se 3 (by rfl) ⟨560930, by rfl⟩ : syracuseStep 2991629 = 1121861) B1121861
theorem B337459 : Blo 299831 337459 := bstep (se 1 (by rfl) ⟨253094, by rfl⟩ : syracuseStep 337459 = 506189) B506189
theorem B6006413 : Blo 299831 6006413 := bstep (se 3 (by rfl) ⟨1126202, by rfl⟩ : syracuseStep 6006413 = 2252405) B2252405
theorem B337603 : Blo 299831 337603 := bstep (se 1 (by rfl) ⟨253202, by rfl⟩ : syracuseStep 337603 = 506405) B506405
theorem B1976035 : Blo 299831 1976035 := bstep (se 1 (by rfl) ⟨1482026, by rfl⟩ : syracuseStep 1976035 = 2964053) B2964053
theorem B861997 : Blo 299831 861997 := bstep (se 3 (by rfl) ⟨161624, by rfl⟩ : syracuseStep 861997 = 323249) B323249
theorem B337747 : Blo 299831 337747 := bstep (se 1 (by rfl) ⟨253310, by rfl⟩ : syracuseStep 337747 = 506621) B506621
theorem B2074501 : Blo 299831 2074501 := bstep (se 4 (by rfl) ⟨194484, by rfl⟩ : syracuseStep 2074501 = 388969) B388969
theorem B1714061 : Blo 299831 1714061 := bstep (se 3 (by rfl) ⟨321386, by rfl⟩ : syracuseStep 1714061 = 642773) B642773
theorem B862157 : Blo 299831 862157 := bstep (se 3 (by rfl) ⟨161654, by rfl⟩ : syracuseStep 862157 = 323309) B323309
theorem B337891 : Blo 299831 337891 := bstep (se 1 (by rfl) ⟨253418, by rfl⟩ : syracuseStep 337891 = 506837) B506837
theorem B338035 : Blo 299831 338035 := bstep (se 1 (by rfl) ⟨253526, by rfl⟩ : syracuseStep 338035 = 507053) B507053
theorem B862339 : Blo 299831 862339 := bstep (se 1 (by rfl) ⟨646754, by rfl⟩ : syracuseStep 862339 = 1293509) B1293509
theorem B3582133 : Blo 299831 3582133 := bstep (se 5 (by rfl) ⟨167912, by rfl⟩ : syracuseStep 3582133 = 335825) B335825
theorem B764113 : Blo 299831 764113 := bstep (se 2 (by rfl) ⟨286542, by rfl⟩ : syracuseStep 764113 = 573085) B573085
theorem B338179 : Blo 299831 338179 := bstep (se 1 (by rfl) ⟨253634, by rfl⟩ : syracuseStep 338179 = 507269) B507269
theorem B436625 : Blo 299831 436625 := bstep (se 2 (by rfl) ⟨163734, by rfl⟩ : syracuseStep 436625 = 327469) B327469
theorem B338323 : Blo 299831 338323 := bstep (se 1 (by rfl) ⟨253742, by rfl⟩ : syracuseStep 338323 = 507485) B507485
theorem B764387 : Blo 299831 764387 := bstep (se 1 (by rfl) ⟨573290, by rfl⟩ : syracuseStep 764387 = 1146581) B1146581
theorem B338467 : Blo 299831 338467 := bstep (se 1 (by rfl) ⟨253850, by rfl⟩ : syracuseStep 338467 = 507701) B507701
theorem B2304611 : Blo 299831 2304611 := bstep (se 1 (by rfl) ⟨1728458, by rfl⟩ : syracuseStep 2304611 = 3456917) B3456917
theorem B764579 : Blo 299831 764579 := bstep (se 1 (by rfl) ⟨573434, by rfl⟩ : syracuseStep 764579 = 1146869) B1146869
theorem B338611 : Blo 299831 338611 := bstep (se 1 (by rfl) ⟨253958, by rfl⟩ : syracuseStep 338611 = 507917) B507917
theorem B338755 : Blo 299831 338755 := bstep (se 1 (by rfl) ⟨254066, by rfl⟩ : syracuseStep 338755 = 508133) B508133
theorem B699313 : Blo 299831 699313 := bstep (se 2 (by rfl) ⟨262242, by rfl⟩ : syracuseStep 699313 = 524485) B524485
theorem B2075597 : Blo 299831 2075597 := bstep (se 3 (by rfl) ⟨389174, by rfl⟩ : syracuseStep 2075597 = 778349) B778349
theorem B338899 : Blo 299831 338899 := bstep (se 1 (by rfl) ⟨254174, by rfl⟩ : syracuseStep 338899 = 508349) B508349
theorem B339043 : Blo 299831 339043 := bstep (se 1 (by rfl) ⟨254282, by rfl⟩ : syracuseStep 339043 = 508565) B508565
theorem B339187 : Blo 299831 339187 := bstep (se 1 (by rfl) ⟨254390, by rfl⟩ : syracuseStep 339187 = 508781) B508781
theorem B339331 : Blo 299831 339331 := bstep (se 1 (by rfl) ⟨254498, by rfl⟩ : syracuseStep 339331 = 508997) B508997
theorem B863729 : Blo 299831 863729 := bstep (se 2 (by rfl) ⟨323898, by rfl⟩ : syracuseStep 863729 = 647797) B647797
theorem B339475 : Blo 299831 339475 := bstep (se 1 (by rfl) ⟨254606, by rfl⟩ : syracuseStep 339475 = 509213) B509213
theorem B765521 : Blo 299831 765521 := bstep (se 2 (by rfl) ⟨287070, by rfl⟩ : syracuseStep 765521 = 574141) B574141
theorem B765571 : Blo 299831 765571 := bstep (se 1 (by rfl) ⟨574178, by rfl⟩ : syracuseStep 765571 = 1148357) B1148357
theorem B339619 : Blo 299831 339619 := bstep (se 1 (by rfl) ⟨254714, by rfl⟩ : syracuseStep 339619 = 509429) B509429
theorem B306883 : Blo 299831 306883 := bstep (se 1 (by rfl) ⟨230162, by rfl⟩ : syracuseStep 306883 = 460325) B460325
theorem B765713 : Blo 299831 765713 := bstep (se 2 (by rfl) ⟨287142, by rfl⟩ : syracuseStep 765713 = 574285) B574285
theorem B339763 : Blo 299831 339763 := bstep (se 1 (by rfl) ⟨254822, by rfl⟩ : syracuseStep 339763 = 509645) B509645
theorem B962417 : Blo 299831 962417 := bstep (se 2 (by rfl) ⟨360906, by rfl⟩ : syracuseStep 962417 = 721813) B721813
theorem B339907 : Blo 299831 339907 := bstep (se 1 (by rfl) ⟨254930, by rfl⟩ : syracuseStep 339907 = 509861) B509861
theorem B569425 : Blo 299831 569425 := bstep (se 2 (by rfl) ⟨213534, by rfl⟩ : syracuseStep 569425 = 427069) B427069
theorem B340051 : Blo 299831 340051 := bstep (se 1 (by rfl) ⟨255038, by rfl⟩ : syracuseStep 340051 = 510077) B510077
theorem B1290467 : Blo 299831 1290467 := bstep (se 1 (by rfl) ⟨967850, by rfl⟩ : syracuseStep 1290467 = 1935701) B1935701
theorem B340195 : Blo 299831 340195 := bstep (se 1 (by rfl) ⟨255146, by rfl⟩ : syracuseStep 340195 = 510293) B510293
theorem B569585 : Blo 299831 569585 := bstep (se 2 (by rfl) ⟨213594, by rfl⟩ : syracuseStep 569585 = 427189) B427189
theorem B2175245 : Blo 299831 2175245 := bstep (se 3 (by rfl) ⟨407858, by rfl⟩ : syracuseStep 2175245 = 815717) B815717
theorem B340339 : Blo 299831 340339 := bstep (se 1 (by rfl) ⟨255254, by rfl⟩ : syracuseStep 340339 = 510509) B510509
theorem B864685 : Blo 299831 864685 := bstep (se 3 (by rfl) ⟨162128, by rfl⟩ : syracuseStep 864685 = 324257) B324257
theorem B2175473 : Blo 299831 2175473 := bstep (se 2 (by rfl) ⟨815802, by rfl⟩ : syracuseStep 2175473 = 1631605) B1631605
theorem B340483 : Blo 299831 340483 := bstep (se 1 (by rfl) ⟨255362, by rfl⟩ : syracuseStep 340483 = 510725) B510725
theorem B2175587 : Blo 299831 2175587 := bstep (se 1 (by rfl) ⟨1631690, by rfl⟩ : syracuseStep 2175587 = 3263381) B3263381
theorem B406129 : Blo 299831 406129 := bstep (se 2 (by rfl) ⟨152298, by rfl⟩ : syracuseStep 406129 = 304597) B304597
theorem B569987 : Blo 299831 569987 := bstep (se 1 (by rfl) ⟨427490, by rfl⟩ : syracuseStep 569987 = 854981) B854981
theorem B3846797 : Blo 299831 3846797 := bstep (se 3 (by rfl) ⟨721274, by rfl⟩ : syracuseStep 3846797 = 1442549) B1442549
theorem B864913 : Blo 299831 864913 := bstep (se 2 (by rfl) ⟨324342, by rfl⟩ : syracuseStep 864913 = 648685) B648685
theorem B340627 : Blo 299831 340627 := bstep (se 1 (by rfl) ⟨255470, by rfl⟩ : syracuseStep 340627 = 510941) B510941
theorem B4108981 : Blo 299831 4108981 := bstep (se 5 (by rfl) ⟨192608, by rfl⟩ : syracuseStep 4108981 = 385217) B385217
theorem B1946339 : Blo 299831 1946339 := bstep (se 1 (by rfl) ⟨1459754, by rfl⟩ : syracuseStep 1946339 = 2919509) B2919509
theorem B1520369 : Blo 299831 1520369 := bstep (se 2 (by rfl) ⟨570138, by rfl⟩ : syracuseStep 1520369 = 1140277) B1140277
theorem B1716977 : Blo 299831 1716977 := bstep (se 2 (by rfl) ⟨643866, by rfl⟩ : syracuseStep 1716977 = 1287733) B1287733
theorem B766705 : Blo 299831 766705 := bstep (se 2 (by rfl) ⟨287514, by rfl⟩ : syracuseStep 766705 = 575029) B575029
theorem B340771 : Blo 299831 340771 := bstep (se 1 (by rfl) ⟨255578, by rfl⟩ : syracuseStep 340771 = 511157) B511157
theorem B865073 : Blo 299831 865073 := bstep (se 2 (by rfl) ⟨324402, by rfl⟩ : syracuseStep 865073 = 648805) B648805
theorem B865187 : Blo 299831 865187 := bstep (se 1 (by rfl) ⟨648890, by rfl⟩ : syracuseStep 865187 = 1297781) B1297781
theorem B340915 : Blo 299831 340915 := bstep (se 1 (by rfl) ⟨255686, by rfl⟩ : syracuseStep 340915 = 511373) B511373
theorem B766979 : Blo 299831 766979 := bstep (se 1 (by rfl) ⟨575234, by rfl⟩ : syracuseStep 766979 = 1150469) B1150469
theorem B341059 : Blo 299831 341059 := bstep (se 1 (by rfl) ⟨255794, by rfl⟩ : syracuseStep 341059 = 511589) B511589
theorem B767171 : Blo 299831 767171 := bstep (se 1 (by rfl) ⟨575378, by rfl⟩ : syracuseStep 767171 = 1150757) B1150757
theorem B341203 : Blo 299831 341203 := bstep (se 1 (by rfl) ⟨255902, by rfl⟩ : syracuseStep 341203 = 511805) B511805
theorem B341347 : Blo 299831 341347 := bstep (se 1 (by rfl) ⟨256010, by rfl⟩ : syracuseStep 341347 = 512021) B512021
theorem B1291697 : Blo 299831 1291697 := bstep (se 2 (by rfl) ⟨484386, by rfl⟩ : syracuseStep 1291697 = 968773) B968773
theorem B341491 : Blo 299831 341491 := bstep (se 1 (by rfl) ⟨256118, by rfl⟩ : syracuseStep 341491 = 512237) B512237
theorem B570883 : Blo 299831 570883 := bstep (se 1 (by rfl) ⟨428162, by rfl⟩ : syracuseStep 570883 = 856325) B856325
theorem B341635 : Blo 299831 341635 := bstep (se 1 (by rfl) ⟨256226, by rfl⟩ : syracuseStep 341635 = 512453) B512453
theorem B571043 : Blo 299831 571043 := bstep (se 1 (by rfl) ⟨428282, by rfl⟩ : syracuseStep 571043 = 856565) B856565
theorem B931537 : Blo 299831 931537 := bstep (se 2 (by rfl) ⟨349326, by rfl⟩ : syracuseStep 931537 = 698653) B698653
theorem B341779 : Blo 299831 341779 := bstep (se 1 (by rfl) ⟨256334, by rfl⟩ : syracuseStep 341779 = 512669) B512669
theorem B4110193 : Blo 299831 4110193 := bstep (se 2 (by rfl) ⟨1541322, by rfl⟩ : syracuseStep 4110193 = 3082645) B3082645
theorem B407443 : Blo 299831 407443 := bstep (se 1 (by rfl) ⟨305582, by rfl⟩ : syracuseStep 407443 = 611165) B611165
theorem B14956597 : Blo 299831 14956597 := bstep (se 5 (by rfl) ⟨701090, by rfl⟩ : syracuseStep 14956597 = 1402181) B1402181
theorem B768113 : Blo 299831 768113 := bstep (se 2 (by rfl) ⟨288042, by rfl⟩ : syracuseStep 768113 = 576085) B576085
theorem B1521827 : Blo 299831 1521827 := bstep (se 1 (by rfl) ⟨1141370, by rfl⟩ : syracuseStep 1521827 = 2282741) B2282741
theorem B1718435 : Blo 299831 1718435 := bstep (se 1 (by rfl) ⟨1288826, by rfl⟩ : syracuseStep 1718435 = 2577653) B2577653
theorem B768163 : Blo 299831 768163 := bstep (se 1 (by rfl) ⟨576122, by rfl⟩ : syracuseStep 768163 = 1152245) B1152245
theorem B506081 : Blo 299831 506081 := bstep (se 2 (by rfl) ⟨189780, by rfl⟩ : syracuseStep 506081 = 379561) B379561
theorem B964877 : Blo 299831 964877 := bstep (se 3 (by rfl) ⟨180914, by rfl⟩ : syracuseStep 964877 = 361829) B361829
theorem B768305 : Blo 299831 768305 := bstep (se 2 (by rfl) ⟨288114, by rfl⟩ : syracuseStep 768305 = 576229) B576229
theorem B506209 : Blo 299831 506209 := bstep (se 2 (by rfl) ⟨189828, by rfl⟩ : syracuseStep 506209 = 379657) B379657
theorem B506243 : Blo 299831 506243 := bstep (se 1 (by rfl) ⟨379682, by rfl⟩ : syracuseStep 506243 = 759365) B759365
theorem B3455459 : Blo 299831 3455459 := bstep (se 1 (by rfl) ⟨2591594, by rfl⟩ : syracuseStep 3455459 = 5183189) B5183189
theorem B506371 : Blo 299831 506371 := bstep (se 1 (by rfl) ⟨379778, by rfl⟩ : syracuseStep 506371 = 759557) B759557
theorem B735875 : Blo 299831 735875 := bstep (se 1 (by rfl) ⟨551906, by rfl⟩ : syracuseStep 735875 = 1103813) B1103813
theorem B506513 : Blo 299831 506513 := bstep (se 2 (by rfl) ⟨189942, by rfl⟩ : syracuseStep 506513 = 379885) B379885
theorem B572113 : Blo 299831 572113 := bstep (se 2 (by rfl) ⟨214542, by rfl⟩ : syracuseStep 572113 = 429085) B429085
theorem B506641 : Blo 299831 506641 := bstep (se 2 (by rfl) ⟨189990, by rfl⟩ : syracuseStep 506641 = 379981) B379981
theorem B506675 : Blo 299831 506675 := bstep (se 1 (by rfl) ⟨380006, by rfl⟩ : syracuseStep 506675 = 760013) B760013
theorem B506803 : Blo 299831 506803 := bstep (se 1 (by rfl) ⟨380102, by rfl⟩ : syracuseStep 506803 = 760205) B760205
theorem B1522637 : Blo 299831 1522637 := bstep (se 3 (by rfl) ⟨285494, by rfl⟩ : syracuseStep 1522637 = 570989) B570989
theorem B506945 : Blo 299831 506945 := bstep (se 2 (by rfl) ⟨190104, by rfl⟩ : syracuseStep 506945 = 380209) B380209
theorem B507073 : Blo 299831 507073 := bstep (se 2 (by rfl) ⟨190152, by rfl⟩ : syracuseStep 507073 = 380305) B380305
theorem B507107 : Blo 299831 507107 := bstep (se 1 (by rfl) ⟨380330, by rfl⟩ : syracuseStep 507107 = 760661) B760661
theorem B2932037 : Blo 299831 2932037 := bstep (se 4 (by rfl) ⟨274878, by rfl⟩ : syracuseStep 2932037 = 549757) B549757
theorem B507235 : Blo 299831 507235 := bstep (se 1 (by rfl) ⟨380426, by rfl⟩ : syracuseStep 507235 = 760853) B760853
theorem B507377 : Blo 299831 507377 := bstep (se 2 (by rfl) ⟨190266, by rfl⟩ : syracuseStep 507377 = 380533) B380533
theorem B507505 : Blo 299831 507505 := bstep (se 2 (by rfl) ⟨190314, by rfl⟩ : syracuseStep 507505 = 380629) B380629
theorem B507539 : Blo 299831 507539 := bstep (se 1 (by rfl) ⟨380654, by rfl⟩ : syracuseStep 507539 = 761309) B761309
theorem B1752781 : Blo 299831 1752781 := bstep (se 3 (by rfl) ⟨328646, by rfl⟩ : syracuseStep 1752781 = 657293) B657293
theorem B573169 : Blo 299831 573169 := bstep (se 2 (by rfl) ⟨214938, by rfl⟩ : syracuseStep 573169 = 429877) B429877
theorem B507667 : Blo 299831 507667 := bstep (se 1 (by rfl) ⟨380750, by rfl⟩ : syracuseStep 507667 = 761501) B761501
theorem B966467 : Blo 299831 966467 := bstep (se 1 (by rfl) ⟨724850, by rfl⟩ : syracuseStep 966467 = 1449701) B1449701
theorem B1294157 : Blo 299831 1294157 := bstep (se 3 (by rfl) ⟨242654, by rfl⟩ : syracuseStep 1294157 = 485309) B485309
theorem B507809 : Blo 299831 507809 := bstep (se 2 (by rfl) ⟨190428, by rfl⟩ : syracuseStep 507809 = 380857) B380857
theorem B540611 : Blo 299831 540611 := bstep (se 1 (by rfl) ⟨405458, by rfl⟩ : syracuseStep 540611 = 810917) B810917
theorem B507937 : Blo 299831 507937 := bstep (se 2 (by rfl) ⟨190476, by rfl⟩ : syracuseStep 507937 = 380953) B380953
theorem B507971 : Blo 299831 507971 := bstep (se 1 (by rfl) ⟨380978, by rfl⟩ : syracuseStep 507971 = 761957) B761957
theorem B2441285 : Blo 299831 2441285 := bstep (se 4 (by rfl) ⟨228870, by rfl⟩ : syracuseStep 2441285 = 457741) B457741
theorem B573571 : Blo 299831 573571 := bstep (se 1 (by rfl) ⟨430178, by rfl⟩ : syracuseStep 573571 = 860357) B860357
theorem B573617 : Blo 299831 573617 := bstep (se 2 (by rfl) ⟨215106, by rfl⟩ : syracuseStep 573617 = 430213) B430213
theorem B508099 : Blo 299831 508099 := bstep (se 1 (by rfl) ⟨381074, by rfl⟩ : syracuseStep 508099 = 762149) B762149
theorem B868589 : Blo 299831 868589 := bstep (se 3 (by rfl) ⟨162860, by rfl⟩ : syracuseStep 868589 = 325721) B325721
theorem B737585 : Blo 299831 737585 := bstep (se 2 (by rfl) ⟨276594, by rfl⟩ : syracuseStep 737585 = 553189) B553189
theorem B508241 : Blo 299831 508241 := bstep (se 2 (by rfl) ⟨190590, by rfl⟩ : syracuseStep 508241 = 381181) B381181
theorem B770417 : Blo 299831 770417 := bstep (se 2 (by rfl) ⟨288906, by rfl⟩ : syracuseStep 770417 = 577813) B577813
theorem B541073 : Blo 299831 541073 := bstep (se 2 (by rfl) ⟨202902, by rfl⟩ : syracuseStep 541073 = 405805) B405805
theorem B508369 : Blo 299831 508369 := bstep (se 2 (by rfl) ⟨190638, by rfl⟩ : syracuseStep 508369 = 381277) B381277
theorem B573905 : Blo 299831 573905 := bstep (se 2 (by rfl) ⟨215214, by rfl⟩ : syracuseStep 573905 = 430429) B430429
theorem B508403 : Blo 299831 508403 := bstep (se 1 (by rfl) ⟨381302, by rfl⟩ : syracuseStep 508403 = 762605) B762605
theorem B508531 : Blo 299831 508531 := bstep (se 1 (by rfl) ⟨381398, by rfl⟩ : syracuseStep 508531 = 762797) B762797
theorem B508673 : Blo 299831 508673 := bstep (se 2 (by rfl) ⟨190752, by rfl⟩ : syracuseStep 508673 = 381505) B381505
theorem B3687221 : Blo 299831 3687221 := bstep (se 5 (by rfl) ⟨172838, by rfl⟩ : syracuseStep 3687221 = 345677) B345677
theorem B508801 : Blo 299831 508801 := bstep (se 2 (by rfl) ⟨190800, by rfl⟩ : syracuseStep 508801 = 381601) B381601
theorem B508835 : Blo 299831 508835 := bstep (se 1 (by rfl) ⟨381626, by rfl⟩ : syracuseStep 508835 = 763253) B763253
theorem B541649 : Blo 299831 541649 := bstep (se 2 (by rfl) ⟨203118, by rfl⟩ : syracuseStep 541649 = 406237) B406237
theorem B345043 : Blo 299831 345043 := bstep (se 1 (by rfl) ⟨258782, by rfl⟩ : syracuseStep 345043 = 517565) B517565
theorem B967697 : Blo 299831 967697 := bstep (se 2 (by rfl) ⟨362886, by rfl⟩ : syracuseStep 967697 = 725773) B725773
theorem B508963 : Blo 299831 508963 := bstep (se 1 (by rfl) ⟨381722, by rfl⟩ : syracuseStep 508963 = 763445) B763445
theorem B1557539 : Blo 299831 1557539 := bstep (se 1 (by rfl) ⟨1168154, by rfl⟩ : syracuseStep 1557539 = 2336309) B2336309
theorem B1459235 : Blo 299831 1459235 := bstep (se 1 (by rfl) ⟨1094426, by rfl⟩ : syracuseStep 1459235 = 2188853) B2188853
theorem B574627 : Blo 299831 574627 := bstep (se 1 (by rfl) ⟨430970, by rfl⟩ : syracuseStep 574627 = 861941) B861941
theorem B509105 : Blo 299831 509105 := bstep (se 2 (by rfl) ⟨190914, by rfl⟩ : syracuseStep 509105 = 381829) B381829
theorem B541937 : Blo 299831 541937 := bstep (se 2 (by rfl) ⟨203226, by rfl⟩ : syracuseStep 541937 = 406453) B406453
theorem B509233 : Blo 299831 509233 := bstep (se 2 (by rfl) ⟨190962, by rfl⟩ : syracuseStep 509233 = 381925) B381925
theorem B509267 : Blo 299831 509267 := bstep (se 1 (by rfl) ⟨381950, by rfl⟩ : syracuseStep 509267 = 763901) B763901
theorem B2278853 : Blo 299831 2278853 := bstep (se 4 (by rfl) ⟨213642, by rfl⟩ : syracuseStep 2278853 = 427285) B427285
theorem B509395 : Blo 299831 509395 := bstep (se 1 (by rfl) ⟨382046, by rfl⟩ : syracuseStep 509395 = 764093) B764093
theorem B509537 : Blo 299831 509537 := bstep (se 2 (by rfl) ⟨191076, by rfl⟩ : syracuseStep 509537 = 382153) B382153
theorem B575075 : Blo 299831 575075 := bstep (se 1 (by rfl) ⟨431306, by rfl⟩ : syracuseStep 575075 = 862613) B862613
theorem B509665 : Blo 299831 509665 := bstep (se 2 (by rfl) ⟨191124, by rfl⟩ : syracuseStep 509665 = 382249) B382249
theorem B509699 : Blo 299831 509699 := bstep (se 1 (by rfl) ⟨382274, by rfl⟩ : syracuseStep 509699 = 764549) B764549
theorem B1525553 : Blo 299831 1525553 := bstep (se 2 (by rfl) ⟨572082, by rfl⟩ : syracuseStep 1525553 = 1144165) B1144165
theorem B968557 : Blo 299831 968557 := bstep (se 3 (by rfl) ⟨181604, by rfl⟩ : syracuseStep 968557 = 363209) B363209
theorem B509827 : Blo 299831 509827 := bstep (se 1 (by rfl) ⟨382370, by rfl⟩ : syracuseStep 509827 = 764741) B764741
theorem B575363 : Blo 299831 575363 := bstep (se 1 (by rfl) ⟨431522, by rfl⟩ : syracuseStep 575363 = 863045) B863045
theorem B509969 : Blo 299831 509969 := bstep (se 2 (by rfl) ⟨191238, by rfl⟩ : syracuseStep 509969 = 382477) B382477
theorem B510097 : Blo 299831 510097 := bstep (se 2 (by rfl) ⟨191286, by rfl⟩ : syracuseStep 510097 = 382573) B382573
theorem B641201 : Blo 299831 641201 := bstep (se 2 (by rfl) ⟨240450, by rfl⟩ : syracuseStep 641201 = 480901) B480901
theorem B510131 : Blo 299831 510131 := bstep (se 1 (by rfl) ⟨382598, by rfl⟩ : syracuseStep 510131 = 765197) B765197
theorem B3786979 : Blo 299831 3786979 := bstep (se 1 (by rfl) ⟨2840234, by rfl⟩ : syracuseStep 3786979 = 5680469) B5680469
theorem B510259 : Blo 299831 510259 := bstep (se 1 (by rfl) ⟨382694, by rfl⟩ : syracuseStep 510259 = 765389) B765389
theorem B313715 : Blo 299831 313715 := bstep (se 1 (by rfl) ⟨235286, by rfl⟩ : syracuseStep 313715 = 470573) B470573
theorem B510401 : Blo 299831 510401 := bstep (se 2 (by rfl) ⟨191400, by rfl⟩ : syracuseStep 510401 = 382801) B382801
theorem B608771 : Blo 299831 608771 := bstep (se 1 (by rfl) ⟨456578, by rfl⟩ : syracuseStep 608771 = 913157) B913157
theorem B510529 : Blo 299831 510529 := bstep (se 2 (by rfl) ⟨191448, by rfl⟩ : syracuseStep 510529 = 382897) B382897
theorem B510563 : Blo 299831 510563 := bstep (se 1 (by rfl) ⟨382922, by rfl⟩ : syracuseStep 510563 = 765845) B765845
theorem B2574989 : Blo 299831 2574989 := bstep (se 3 (by rfl) ⟨482810, by rfl⟩ : syracuseStep 2574989 = 965621) B965621
theorem B510691 : Blo 299831 510691 := bstep (se 1 (by rfl) ⟨383018, by rfl⟩ : syracuseStep 510691 = 766037) B766037
theorem B379667 : Blo 299831 379667 := bstep (se 1 (by rfl) ⟨284750, by rfl⟩ : syracuseStep 379667 = 569501) B569501
theorem B543523 : Blo 299831 543523 := bstep (se 1 (by rfl) ⟨407642, by rfl⟩ : syracuseStep 543523 = 815285) B815285
theorem B576305 : Blo 299831 576305 := bstep (se 2 (by rfl) ⟨216114, by rfl⟩ : syracuseStep 576305 = 432229) B432229
theorem B510833 : Blo 299831 510833 := bstep (se 2 (by rfl) ⟨191562, by rfl⟩ : syracuseStep 510833 = 383125) B383125
theorem B674801 : Blo 299831 674801 := bstep (se 2 (by rfl) ⟨253050, by rfl⟩ : syracuseStep 674801 = 506101) B506101
theorem B510961 : Blo 299831 510961 := bstep (se 2 (by rfl) ⟨191610, by rfl⟩ : syracuseStep 510961 = 383221) B383221
theorem B674819 : Blo 299831 674819 := bstep (se 1 (by rfl) ⟨506114, by rfl⟩ : syracuseStep 674819 = 1012229) B1012229
theorem B1035281 : Blo 299831 1035281 := bstep (se 2 (by rfl) ⟨388230, by rfl⟩ : syracuseStep 1035281 = 776461) B776461
theorem B510995 : Blo 299831 510995 := bstep (se 1 (by rfl) ⟨383246, by rfl⟩ : syracuseStep 510995 = 766493) B766493
theorem B511123 : Blo 299831 511123 := bstep (se 1 (by rfl) ⟨383342, by rfl⟩ : syracuseStep 511123 = 766685) B766685
theorem B1527011 : Blo 299831 1527011 := bstep (se 1 (by rfl) ⟨1145258, by rfl⟩ : syracuseStep 1527011 = 2290517) B2290517
theorem B675089 : Blo 299831 675089 := bstep (se 2 (by rfl) ⟨253158, by rfl⟩ : syracuseStep 675089 = 506317) B506317
theorem B511265 : Blo 299831 511265 := bstep (se 2 (by rfl) ⟨191724, by rfl⟩ : syracuseStep 511265 = 383449) B383449
theorem B675107 : Blo 299831 675107 := bstep (se 1 (by rfl) ⟨506330, by rfl⟩ : syracuseStep 675107 = 1012661) B1012661
theorem B5918005 : Blo 299831 5918005 := bstep (se 5 (by rfl) ⟨277406, by rfl⟩ : syracuseStep 5918005 = 554813) B554813
theorem B511393 : Blo 299831 511393 := bstep (se 2 (by rfl) ⟨191772, by rfl⟩ : syracuseStep 511393 = 383545) B383545
theorem B970157 : Blo 299831 970157 := bstep (se 3 (by rfl) ⟨181904, by rfl⟩ : syracuseStep 970157 = 363809) B363809
theorem B511427 : Blo 299831 511427 := bstep (se 1 (by rfl) ⟨383570, by rfl⟩ : syracuseStep 511427 = 767141) B767141
theorem B380371 : Blo 299831 380371 := bstep (se 1 (by rfl) ⟨285278, by rfl⟩ : syracuseStep 380371 = 570557) B570557
theorem B1166833 : Blo 299831 1166833 := bstep (se 2 (by rfl) ⟨437562, by rfl⟩ : syracuseStep 1166833 = 875125) B875125
theorem B675377 : Blo 299831 675377 := bstep (se 2 (by rfl) ⟨253266, by rfl⟩ : syracuseStep 675377 = 506533) B506533
theorem B380467 : Blo 299831 380467 := bstep (se 1 (by rfl) ⟨285350, by rfl⟩ : syracuseStep 380467 = 570701) B570701
theorem B675395 : Blo 299831 675395 := bstep (se 1 (by rfl) ⟨506546, by rfl⟩ : syracuseStep 675395 = 1013093) B1013093
theorem B511555 : Blo 299831 511555 := bstep (se 1 (by rfl) ⟨383666, by rfl⟩ : syracuseStep 511555 = 767333) B767333
theorem B2444941 : Blo 299831 2444941 := bstep (se 3 (by rfl) ⟨458426, by rfl⟩ : syracuseStep 2444941 = 916853) B916853
theorem B511697 : Blo 299831 511697 := bstep (se 2 (by rfl) ⟨191886, by rfl⟩ : syracuseStep 511697 = 383773) B383773
theorem B675665 : Blo 299831 675665 := bstep (se 2 (by rfl) ⟨253374, by rfl⟩ : syracuseStep 675665 = 506749) B506749
theorem B511825 : Blo 299831 511825 := bstep (se 2 (by rfl) ⟨191934, by rfl⟩ : syracuseStep 511825 = 383869) B383869
theorem B675683 : Blo 299831 675683 := bstep (se 1 (by rfl) ⟨506762, by rfl⟩ : syracuseStep 675683 = 1013525) B1013525
theorem B511859 : Blo 299831 511859 := bstep (se 1 (by rfl) ⟨383894, by rfl⟩ : syracuseStep 511859 = 767789) B767789
theorem B511987 : Blo 299831 511987 := bstep (se 1 (by rfl) ⟨383990, by rfl⟩ : syracuseStep 511987 = 767981) B767981
theorem B1527821 : Blo 299831 1527821 := bstep (se 3 (by rfl) ⟨286466, by rfl⟩ : syracuseStep 1527821 = 572933) B572933
theorem B380963 : Blo 299831 380963 := bstep (se 1 (by rfl) ⟨285722, by rfl⟩ : syracuseStep 380963 = 571445) B571445
theorem B774193 : Blo 299831 774193 := bstep (se 2 (by rfl) ⟨290322, by rfl⟩ : syracuseStep 774193 = 580645) B580645
theorem B675953 : Blo 299831 675953 := bstep (se 2 (by rfl) ⟨253482, by rfl⟩ : syracuseStep 675953 = 506965) B506965
theorem B512129 : Blo 299831 512129 := bstep (se 2 (by rfl) ⟨192048, by rfl⟩ : syracuseStep 512129 = 384097) B384097
theorem B675971 : Blo 299831 675971 := bstep (se 1 (by rfl) ⟨506978, by rfl⟩ : syracuseStep 675971 = 1013957) B1013957
theorem B512257 : Blo 299831 512257 := bstep (se 2 (by rfl) ⟨192096, by rfl⟩ : syracuseStep 512257 = 384193) B384193
theorem B512291 : Blo 299831 512291 := bstep (se 1 (by rfl) ⟨384218, by rfl⟩ : syracuseStep 512291 = 768437) B768437
theorem B676241 : Blo 299831 676241 := bstep (se 2 (by rfl) ⟨253590, by rfl⟩ : syracuseStep 676241 = 507181) B507181
theorem B676259 : Blo 299831 676259 := bstep (se 1 (by rfl) ⟨507194, by rfl⟩ : syracuseStep 676259 = 1014389) B1014389
theorem B512419 : Blo 299831 512419 := bstep (se 1 (by rfl) ⟨384314, by rfl⟩ : syracuseStep 512419 = 768629) B768629
theorem B17912261 : Blo 299831 17912261 := bstep (se 4 (by rfl) ⟨1679274, by rfl⟩ : syracuseStep 17912261 = 3358549) B3358549
theorem B2118149 : Blo 299831 2118149 := bstep (se 4 (by rfl) ⟨198576, by rfl⟩ : syracuseStep 2118149 = 397153) B397153
theorem B512561 : Blo 299831 512561 := bstep (se 2 (by rfl) ⟨192210, by rfl⟩ : syracuseStep 512561 = 384421) B384421
theorem B5526157 : Blo 299831 5526157 := bstep (se 3 (by rfl) ⟨1036154, by rfl⟩ : syracuseStep 5526157 = 2072309) B2072309
theorem B676529 : Blo 299831 676529 := bstep (se 2 (by rfl) ⟨253698, by rfl⟩ : syracuseStep 676529 = 507397) B507397
theorem B512689 : Blo 299831 512689 := bstep (se 2 (by rfl) ⟨192258, by rfl⟩ : syracuseStep 512689 = 384517) B384517
theorem B676547 : Blo 299831 676547 := bstep (se 1 (by rfl) ⟨507410, by rfl⟩ : syracuseStep 676547 = 1014821) B1014821
theorem B381667 : Blo 299831 381667 := bstep (se 1 (by rfl) ⟨286250, by rfl⟩ : syracuseStep 381667 = 572501) B572501
theorem B1168141 : Blo 299831 1168141 := bstep (se 3 (by rfl) ⟨219026, by rfl⟩ : syracuseStep 1168141 = 438053) B438053
theorem B381763 : Blo 299831 381763 := bstep (se 1 (by rfl) ⟨286322, by rfl⟩ : syracuseStep 381763 = 572645) B572645
theorem B676817 : Blo 299831 676817 := bstep (se 2 (by rfl) ⟨253806, by rfl⟩ : syracuseStep 676817 = 507613) B507613
theorem B676835 : Blo 299831 676835 := bstep (se 1 (by rfl) ⟨507626, by rfl⟩ : syracuseStep 676835 = 1015253) B1015253
theorem B2577379 : Blo 299831 2577379 := bstep (se 1 (by rfl) ⟨1933034, by rfl⟩ : syracuseStep 2577379 = 3866069) B3866069
theorem B971747 : Blo 299831 971747 := bstep (se 1 (by rfl) ⟨728810, by rfl⟩ : syracuseStep 971747 = 1457621) B1457621
theorem B578659 : Blo 299831 578659 := bstep (se 1 (by rfl) ⟨433994, by rfl⟩ : syracuseStep 578659 = 867989) B867989
theorem B971939 : Blo 299831 971939 := bstep (se 1 (by rfl) ⟨728954, by rfl⟩ : syracuseStep 971939 = 1457909) B1457909
theorem B677105 : Blo 299831 677105 := bstep (se 2 (by rfl) ⟨253914, by rfl⟩ : syracuseStep 677105 = 507829) B507829
theorem B677123 : Blo 299831 677123 := bstep (se 1 (by rfl) ⟨507842, by rfl⟩ : syracuseStep 677123 = 1015685) B1015685
theorem B382259 : Blo 299831 382259 := bstep (se 1 (by rfl) ⟨286694, by rfl⟩ : syracuseStep 382259 = 573389) B573389
theorem B3495221 : Blo 299831 3495221 := bstep (se 5 (by rfl) ⟨163838, by rfl⟩ : syracuseStep 3495221 = 327677) B327677
theorem B644611 : Blo 299831 644611 := bstep (se 1 (by rfl) ⟨483458, by rfl⟩ : syracuseStep 644611 = 966917) B966917
theorem B677393 : Blo 299831 677393 := bstep (se 2 (by rfl) ⟨254022, by rfl⟩ : syracuseStep 677393 = 508045) B508045
theorem B677411 : Blo 299831 677411 := bstep (se 1 (by rfl) ⟨508058, by rfl⟩ : syracuseStep 677411 = 1016117) B1016117
theorem B1660621 : Blo 299831 1660621 := bstep (se 3 (by rfl) ⟨311366, by rfl⟩ : syracuseStep 1660621 = 622733) B622733
theorem B14636771 : Blo 299831 14636771 := bstep (se 1 (by rfl) ⟨10977578, by rfl⟩ : syracuseStep 14636771 = 21955157) B21955157
theorem B677681 : Blo 299831 677681 := bstep (se 2 (by rfl) ⟨254130, by rfl⟩ : syracuseStep 677681 = 508261) B508261
theorem B972593 : Blo 299831 972593 := bstep (se 2 (by rfl) ⟨364722, by rfl⟩ : syracuseStep 972593 = 729445) B729445
theorem B677699 : Blo 299831 677699 := bstep (se 1 (by rfl) ⟨508274, by rfl⟩ : syracuseStep 677699 = 1016549) B1016549
theorem B382963 : Blo 299831 382963 := bstep (se 1 (by rfl) ⟨287222, by rfl⟩ : syracuseStep 382963 = 574445) B574445
theorem B677969 : Blo 299831 677969 := bstep (se 2 (by rfl) ⟨254238, by rfl⟩ : syracuseStep 677969 = 508477) B508477
theorem B383059 : Blo 299831 383059 := bstep (se 1 (by rfl) ⟨287294, by rfl⟩ : syracuseStep 383059 = 574589) B574589
theorem B677987 : Blo 299831 677987 := bstep (se 1 (by rfl) ⟨508490, by rfl⟩ : syracuseStep 677987 = 1016981) B1016981
theorem B1038467 : Blo 299831 1038467 := bstep (se 1 (by rfl) ⟨778850, by rfl⟩ : syracuseStep 1038467 = 1557701) B1557701
theorem B481459 : Blo 299831 481459 := bstep (se 1 (by rfl) ⟨361094, by rfl⟩ : syracuseStep 481459 = 722189) B722189
theorem B514307 : Blo 299831 514307 := bstep (se 1 (by rfl) ⟨385730, by rfl⟩ : syracuseStep 514307 = 771461) B771461
theorem B678257 : Blo 299831 678257 := bstep (se 2 (by rfl) ⟨254346, by rfl⟩ : syracuseStep 678257 = 508693) B508693
theorem B612721 : Blo 299831 612721 := bstep (se 2 (by rfl) ⟨229770, by rfl⟩ : syracuseStep 612721 = 459541) B459541
theorem B678275 : Blo 299831 678275 := bstep (se 1 (by rfl) ⟨508706, by rfl⟩ : syracuseStep 678275 = 1017413) B1017413
theorem B3103217 : Blo 299831 3103217 := bstep (se 2 (by rfl) ⟨1163706, by rfl⟩ : syracuseStep 3103217 = 2327413) B2327413
theorem B4872757 : Blo 299831 4872757 := bstep (se 5 (by rfl) ⟨228410, by rfl⟩ : syracuseStep 4872757 = 456821) B456821
theorem B383555 : Blo 299831 383555 := bstep (se 1 (by rfl) ⟨287666, by rfl⟩ : syracuseStep 383555 = 575333) B575333
theorem B678545 : Blo 299831 678545 := bstep (se 2 (by rfl) ⟨254454, by rfl⟩ : syracuseStep 678545 = 508909) B508909
theorem B580259 : Blo 299831 580259 := bstep (se 1 (by rfl) ⟨435194, by rfl⟩ : syracuseStep 580259 = 870389) B870389
theorem B678563 : Blo 299831 678563 := bstep (se 1 (by rfl) ⟨508922, by rfl⟩ : syracuseStep 678563 = 1017845) B1017845
theorem B776881 : Blo 299831 776881 := bstep (se 2 (by rfl) ⟨291330, by rfl⟩ : syracuseStep 776881 = 582661) B582661
theorem B5135075 : Blo 299831 5135075 := bstep (se 1 (by rfl) ⟨3851306, by rfl⟩ : syracuseStep 5135075 = 7702613) B7702613
theorem B482131 : Blo 299831 482131 := bstep (se 1 (by rfl) ⟨361598, by rfl⟩ : syracuseStep 482131 = 723197) B723197
theorem B1530737 : Blo 299831 1530737 := bstep (se 2 (by rfl) ⟨574026, by rfl⟩ : syracuseStep 1530737 = 1148053) B1148053
theorem B1727365 : Blo 299831 1727365 := bstep (se 4 (by rfl) ⟨161940, by rfl⟩ : syracuseStep 1727365 = 323881) B323881
theorem B678833 : Blo 299831 678833 := bstep (se 2 (by rfl) ⟨254562, by rfl⟩ : syracuseStep 678833 = 509125) B509125
theorem B678851 : Blo 299831 678851 := bstep (se 1 (by rfl) ⟨509138, by rfl⟩ : syracuseStep 678851 = 1018277) B1018277
theorem B1924195 : Blo 299831 1924195 := bstep (se 1 (by rfl) ⟨1443146, by rfl⟩ : syracuseStep 1924195 = 2886293) B2886293
theorem B613507 : Blo 299831 613507 := bstep (se 1 (by rfl) ⟨460130, by rfl⟩ : syracuseStep 613507 = 920261) B920261
theorem B2284685 : Blo 299831 2284685 := bstep (se 3 (by rfl) ⟨428378, by rfl⟩ : syracuseStep 2284685 = 856757) B856757
theorem B679121 : Blo 299831 679121 := bstep (se 2 (by rfl) ⟨254670, by rfl⟩ : syracuseStep 679121 = 509341) B509341
theorem B449747 : Blo 299831 449747 := bstep (se 1 (by rfl) ⟨337310, by rfl⟩ : syracuseStep 449747 = 674621) B674621
theorem B679139 : Blo 299831 679139 := bstep (se 1 (by rfl) ⟨509354, by rfl⟩ : syracuseStep 679139 = 1018709) B1018709
theorem B449777 : Blo 299831 449777 := bstep (se 2 (by rfl) ⟨168666, by rfl⟩ : syracuseStep 449777 = 337333) B337333
theorem B449795 : Blo 299831 449795 := bstep (se 1 (by rfl) ⟨337346, by rfl⟩ : syracuseStep 449795 = 674693) B674693
theorem B384259 : Blo 299831 384259 := bstep (se 1 (by rfl) ⟨288194, by rfl⟩ : syracuseStep 384259 = 576389) B576389
theorem B449825 : Blo 299831 449825 := bstep (se 2 (by rfl) ⟨168684, by rfl⟩ : syracuseStep 449825 = 337369) B337369
theorem B482593 : Blo 299831 482593 := bstep (se 2 (by rfl) ⟨180972, by rfl⟩ : syracuseStep 482593 = 361945) B361945
theorem B449843 : Blo 299831 449843 := bstep (se 1 (by rfl) ⟨337382, by rfl⟩ : syracuseStep 449843 = 674765) B674765
theorem B449873 : Blo 299831 449873 := bstep (se 2 (by rfl) ⟨168702, by rfl⟩ : syracuseStep 449873 = 337405) B337405
theorem B646481 : Blo 299831 646481 := bstep (se 2 (by rfl) ⟨242430, by rfl⟩ : syracuseStep 646481 = 484861) B484861
theorem B449891 : Blo 299831 449891 := bstep (se 1 (by rfl) ⟨337418, by rfl⟩ : syracuseStep 449891 = 674837) B674837
theorem B384355 : Blo 299831 384355 := bstep (se 1 (by rfl) ⟨288266, by rfl⟩ : syracuseStep 384355 = 576533) B576533
theorem B449921 : Blo 299831 449921 := bstep (se 2 (by rfl) ⟨168720, by rfl⟩ : syracuseStep 449921 = 337441) B337441
theorem B482689 : Blo 299831 482689 := bstep (se 2 (by rfl) ⟨181008, by rfl⟩ : syracuseStep 482689 = 362017) B362017
theorem B449939 : Blo 299831 449939 := bstep (se 1 (by rfl) ⟨337454, by rfl⟩ : syracuseStep 449939 = 674909) B674909
theorem B449969 : Blo 299831 449969 := bstep (se 2 (by rfl) ⟨168738, by rfl⟩ : syracuseStep 449969 = 337477) B337477
theorem B449987 : Blo 299831 449987 := bstep (se 1 (by rfl) ⟨337490, by rfl⟩ : syracuseStep 449987 = 674981) B674981
theorem B450017 : Blo 299831 450017 := bstep (se 2 (by rfl) ⟨168756, by rfl⟩ : syracuseStep 450017 = 337513) B337513
theorem B679409 : Blo 299831 679409 := bstep (se 2 (by rfl) ⟨254778, by rfl⟩ : syracuseStep 679409 = 509557) B509557
theorem B450035 : Blo 299831 450035 := bstep (se 1 (by rfl) ⟨337526, by rfl⟩ : syracuseStep 450035 = 675053) B675053
theorem B679427 : Blo 299831 679427 := bstep (se 1 (by rfl) ⟨509570, by rfl⟩ : syracuseStep 679427 = 1019141) B1019141
theorem B450065 : Blo 299831 450065 := bstep (se 2 (by rfl) ⟨168774, by rfl⟩ : syracuseStep 450065 = 337549) B337549
theorem B482849 : Blo 299831 482849 := bstep (se 2 (by rfl) ⟨181068, by rfl⟩ : syracuseStep 482849 = 362137) B362137
theorem B450083 : Blo 299831 450083 := bstep (se 1 (by rfl) ⟨337562, by rfl⟩ : syracuseStep 450083 = 675125) B675125
theorem B450113 : Blo 299831 450113 := bstep (se 2 (by rfl) ⟨168792, by rfl⟩ : syracuseStep 450113 = 337585) B337585
theorem B613955 : Blo 299831 613955 := bstep (se 1 (by rfl) ⟨460466, by rfl⟩ : syracuseStep 613955 = 920933) B920933
theorem B450131 : Blo 299831 450131 := bstep (se 1 (by rfl) ⟨337598, by rfl⟩ : syracuseStep 450131 = 675197) B675197
theorem B450161 : Blo 299831 450161 := bstep (se 2 (by rfl) ⟨168810, by rfl⟩ : syracuseStep 450161 = 337621) B337621
theorem B450179 : Blo 299831 450179 := bstep (se 1 (by rfl) ⟨337634, by rfl⟩ : syracuseStep 450179 = 675269) B675269
theorem B450209 : Blo 299831 450209 := bstep (se 2 (by rfl) ⟨168828, by rfl⟩ : syracuseStep 450209 = 337657) B337657
theorem B450227 : Blo 299831 450227 := bstep (se 1 (by rfl) ⟨337670, by rfl⟩ : syracuseStep 450227 = 675341) B675341
theorem B450257 : Blo 299831 450257 := bstep (se 2 (by rfl) ⟨168846, by rfl⟩ : syracuseStep 450257 = 337693) B337693
theorem B450275 : Blo 299831 450275 := bstep (se 1 (by rfl) ⟨337706, by rfl⟩ : syracuseStep 450275 = 675413) B675413
theorem B450305 : Blo 299831 450305 := bstep (se 2 (by rfl) ⟨168864, by rfl⟩ : syracuseStep 450305 = 337729) B337729
theorem B679697 : Blo 299831 679697 := bstep (se 2 (by rfl) ⟨254886, by rfl⟩ : syracuseStep 679697 = 509773) B509773
theorem B450323 : Blo 299831 450323 := bstep (se 1 (by rfl) ⟨337742, by rfl⟩ : syracuseStep 450323 = 675485) B675485
theorem B679715 : Blo 299831 679715 := bstep (se 1 (by rfl) ⟨509786, by rfl⟩ : syracuseStep 679715 = 1019573) B1019573
theorem B450353 : Blo 299831 450353 := bstep (se 2 (by rfl) ⟨168882, by rfl⟩ : syracuseStep 450353 = 337765) B337765
theorem B450371 : Blo 299831 450371 := bstep (se 1 (by rfl) ⟨337778, by rfl⟩ : syracuseStep 450371 = 675557) B675557
theorem B450401 : Blo 299831 450401 := bstep (se 2 (by rfl) ⟨168900, by rfl⟩ : syracuseStep 450401 = 337801) B337801
theorem B2187121 : Blo 299831 2187121 := bstep (se 2 (by rfl) ⟨820170, by rfl⟩ : syracuseStep 2187121 = 1640341) B1640341
theorem B450419 : Blo 299831 450419 := bstep (se 1 (by rfl) ⟨337814, by rfl⟩ : syracuseStep 450419 = 675629) B675629
theorem B450449 : Blo 299831 450449 := bstep (se 2 (by rfl) ⟨168918, by rfl⟩ : syracuseStep 450449 = 337837) B337837
theorem B450467 : Blo 299831 450467 := bstep (se 1 (by rfl) ⟨337850, by rfl⟩ : syracuseStep 450467 = 675701) B675701
theorem B450497 : Blo 299831 450497 := bstep (se 2 (by rfl) ⟨168936, by rfl⟩ : syracuseStep 450497 = 337873) B337873
theorem B1138637 : Blo 299831 1138637 := bstep (se 3 (by rfl) ⟨213494, by rfl⟩ : syracuseStep 1138637 = 426989) B426989
theorem B450515 : Blo 299831 450515 := bstep (se 1 (by rfl) ⟨337886, by rfl⟩ : syracuseStep 450515 = 675773) B675773
theorem B450545 : Blo 299831 450545 := bstep (se 2 (by rfl) ⟨168954, by rfl⟩ : syracuseStep 450545 = 337909) B337909
theorem B450563 : Blo 299831 450563 := bstep (se 1 (by rfl) ⟨337922, by rfl⟩ : syracuseStep 450563 = 675845) B675845
theorem B385043 : Blo 299831 385043 := bstep (se 1 (by rfl) ⟨288782, by rfl⟩ : syracuseStep 385043 = 577565) B577565
theorem B450593 : Blo 299831 450593 := bstep (se 2 (by rfl) ⟨168972, by rfl⟩ : syracuseStep 450593 = 337945) B337945
theorem B679985 : Blo 299831 679985 := bstep (se 2 (by rfl) ⟨254994, by rfl⟩ : syracuseStep 679985 = 509989) B509989
theorem B450611 : Blo 299831 450611 := bstep (se 1 (by rfl) ⟨337958, by rfl⟩ : syracuseStep 450611 = 675917) B675917
theorem B680003 : Blo 299831 680003 := bstep (se 1 (by rfl) ⟨510002, by rfl⟩ : syracuseStep 680003 = 1020005) B1020005
theorem B450641 : Blo 299831 450641 := bstep (se 2 (by rfl) ⟨168990, by rfl⟩ : syracuseStep 450641 = 337981) B337981
theorem B450659 : Blo 299831 450659 := bstep (se 1 (by rfl) ⟨337994, by rfl⟩ : syracuseStep 450659 = 675989) B675989
theorem B450689 : Blo 299831 450689 := bstep (se 2 (by rfl) ⟨169008, by rfl⟩ : syracuseStep 450689 = 338017) B338017
theorem B450707 : Blo 299831 450707 := bstep (se 1 (by rfl) ⟨338030, by rfl⟩ : syracuseStep 450707 = 676061) B676061
theorem B450737 : Blo 299831 450737 := bstep (se 2 (by rfl) ⟨169026, by rfl⟩ : syracuseStep 450737 = 338053) B338053
theorem B647345 : Blo 299831 647345 := bstep (se 2 (by rfl) ⟨242754, by rfl⟩ : syracuseStep 647345 = 485509) B485509
theorem B450755 : Blo 299831 450755 := bstep (se 1 (by rfl) ⟨338066, by rfl⟩ : syracuseStep 450755 = 676133) B676133
theorem B450785 : Blo 299831 450785 := bstep (se 2 (by rfl) ⟨169044, by rfl⟩ : syracuseStep 450785 = 338089) B338089
theorem B450803 : Blo 299831 450803 := bstep (se 1 (by rfl) ⟨338102, by rfl⟩ : syracuseStep 450803 = 676205) B676205
theorem B450833 : Blo 299831 450833 := bstep (se 2 (by rfl) ⟨169062, by rfl⟩ : syracuseStep 450833 = 338125) B338125
theorem B450851 : Blo 299831 450851 := bstep (se 1 (by rfl) ⟨338138, by rfl⟩ : syracuseStep 450851 = 676277) B676277
theorem B1532195 : Blo 299831 1532195 := bstep (se 1 (by rfl) ⟨1149146, by rfl⟩ : syracuseStep 1532195 = 2298293) B2298293
theorem B450881 : Blo 299831 450881 := bstep (se 2 (by rfl) ⟨169080, by rfl⟩ : syracuseStep 450881 = 338161) B338161
theorem B680273 : Blo 299831 680273 := bstep (se 2 (by rfl) ⟨255102, by rfl⟩ : syracuseStep 680273 = 510205) B510205
theorem B450899 : Blo 299831 450899 := bstep (se 1 (by rfl) ⟨338174, by rfl⟩ : syracuseStep 450899 = 676349) B676349
theorem B680291 : Blo 299831 680291 := bstep (se 1 (by rfl) ⟨510218, by rfl⟩ : syracuseStep 680291 = 1020437) B1020437
theorem B450929 : Blo 299831 450929 := bstep (se 2 (by rfl) ⟨169098, by rfl⟩ : syracuseStep 450929 = 338197) B338197
theorem B450947 : Blo 299831 450947 := bstep (se 1 (by rfl) ⟨338210, by rfl⟩ : syracuseStep 450947 = 676421) B676421
theorem B450977 : Blo 299831 450977 := bstep (se 2 (by rfl) ⟨169116, by rfl⟩ : syracuseStep 450977 = 338233) B338233
theorem B450995 : Blo 299831 450995 := bstep (se 1 (by rfl) ⟨338246, by rfl⟩ : syracuseStep 450995 = 676493) B676493
theorem B451025 : Blo 299831 451025 := bstep (se 2 (by rfl) ⟨169134, by rfl⟩ : syracuseStep 451025 = 338269) B338269
theorem B451043 : Blo 299831 451043 := bstep (se 1 (by rfl) ⟨338282, by rfl⟩ : syracuseStep 451043 = 676565) B676565
theorem B451073 : Blo 299831 451073 := bstep (se 2 (by rfl) ⟨169152, by rfl⟩ : syracuseStep 451073 = 338305) B338305
theorem B451091 : Blo 299831 451091 := bstep (se 1 (by rfl) ⟨338318, by rfl⟩ : syracuseStep 451091 = 676637) B676637
theorem B451121 : Blo 299831 451121 := bstep (se 2 (by rfl) ⟨169170, by rfl⟩ : syracuseStep 451121 = 338341) B338341
theorem B451139 : Blo 299831 451139 := bstep (se 1 (by rfl) ⟨338354, by rfl⟩ : syracuseStep 451139 = 676709) B676709
theorem B451169 : Blo 299831 451169 := bstep (se 2 (by rfl) ⟨169188, by rfl⟩ : syracuseStep 451169 = 338377) B338377
theorem B975473 : Blo 299831 975473 := bstep (se 2 (by rfl) ⟨365802, by rfl⟩ : syracuseStep 975473 = 731605) B731605
theorem B680561 : Blo 299831 680561 := bstep (se 2 (by rfl) ⟨255210, by rfl⟩ : syracuseStep 680561 = 510421) B510421
theorem B451187 : Blo 299831 451187 := bstep (se 1 (by rfl) ⟨338390, by rfl⟩ : syracuseStep 451187 = 676781) B676781
theorem B680579 : Blo 299831 680579 := bstep (se 1 (by rfl) ⟨510434, by rfl⟩ : syracuseStep 680579 = 1020869) B1020869
theorem B451217 : Blo 299831 451217 := bstep (se 2 (by rfl) ⟨169206, by rfl⟩ : syracuseStep 451217 = 338413) B338413
theorem B451235 : Blo 299831 451235 := bstep (se 1 (by rfl) ⟨338426, by rfl⟩ : syracuseStep 451235 = 676853) B676853
theorem B451265 : Blo 299831 451265 := bstep (se 2 (by rfl) ⟨169224, by rfl⟩ : syracuseStep 451265 = 338449) B338449
theorem B451283 : Blo 299831 451283 := bstep (se 1 (by rfl) ⟨338462, by rfl⟩ : syracuseStep 451283 = 676925) B676925
theorem B451313 : Blo 299831 451313 := bstep (se 2 (by rfl) ⟨169242, by rfl⟩ : syracuseStep 451313 = 338485) B338485
theorem B451331 : Blo 299831 451331 := bstep (se 1 (by rfl) ⟨338498, by rfl⟩ : syracuseStep 451331 = 676997) B676997
theorem B451361 : Blo 299831 451361 := bstep (se 2 (by rfl) ⟨169260, by rfl⟩ : syracuseStep 451361 = 338521) B338521
theorem B451379 : Blo 299831 451379 := bstep (se 1 (by rfl) ⟨338534, by rfl⟩ : syracuseStep 451379 = 677069) B677069
theorem B1729349 : Blo 299831 1729349 := bstep (se 4 (by rfl) ⟨162126, by rfl⟩ : syracuseStep 1729349 = 324253) B324253
theorem B451409 : Blo 299831 451409 := bstep (se 2 (by rfl) ⟨169278, by rfl⟩ : syracuseStep 451409 = 338557) B338557
theorem B451427 : Blo 299831 451427 := bstep (se 1 (by rfl) ⟨338570, by rfl⟩ : syracuseStep 451427 = 677141) B677141
theorem B4350833 : Blo 299831 4350833 := bstep (se 2 (by rfl) ⟨1631562, by rfl⟩ : syracuseStep 4350833 = 3263125) B3263125
theorem B451457 : Blo 299831 451457 := bstep (se 2 (by rfl) ⟨169296, by rfl⟩ : syracuseStep 451457 = 338593) B338593
theorem B680849 : Blo 299831 680849 := bstep (se 2 (by rfl) ⟨255318, by rfl⟩ : syracuseStep 680849 = 510637) B510637
theorem B451475 : Blo 299831 451475 := bstep (se 1 (by rfl) ⟨338606, by rfl⟩ : syracuseStep 451475 = 677213) B677213
theorem B680867 : Blo 299831 680867 := bstep (se 1 (by rfl) ⟨510650, by rfl⟩ : syracuseStep 680867 = 1021301) B1021301
theorem B451505 : Blo 299831 451505 := bstep (se 2 (by rfl) ⟨169314, by rfl⟩ : syracuseStep 451505 = 338629) B338629
theorem B1631153 : Blo 299831 1631153 := bstep (se 2 (by rfl) ⟨611682, by rfl⟩ : syracuseStep 1631153 = 1223365) B1223365
theorem B451523 : Blo 299831 451523 := bstep (se 1 (by rfl) ⟨338642, by rfl⟩ : syracuseStep 451523 = 677285) B677285
theorem B451553 : Blo 299831 451553 := bstep (se 2 (by rfl) ⟨169332, by rfl⟩ : syracuseStep 451553 = 338665) B338665
theorem B451571 : Blo 299831 451571 := bstep (se 1 (by rfl) ⟨338678, by rfl⟩ : syracuseStep 451571 = 677357) B677357
theorem B451601 : Blo 299831 451601 := bstep (se 2 (by rfl) ⟨169350, by rfl⟩ : syracuseStep 451601 = 338701) B338701
theorem B451619 : Blo 299831 451619 := bstep (se 1 (by rfl) ⟨338714, by rfl⟩ : syracuseStep 451619 = 677429) B677429
theorem B451649 : Blo 299831 451649 := bstep (se 2 (by rfl) ⟨169368, by rfl⟩ : syracuseStep 451649 = 338737) B338737
theorem B1533005 : Blo 299831 1533005 := bstep (se 3 (by rfl) ⟨287438, by rfl⟩ : syracuseStep 1533005 = 574877) B574877
theorem B451667 : Blo 299831 451667 := bstep (se 1 (by rfl) ⟨338750, by rfl⟩ : syracuseStep 451667 = 677501) B677501
theorem B451697 : Blo 299831 451697 := bstep (se 2 (by rfl) ⟨169386, by rfl⟩ : syracuseStep 451697 = 338773) B338773
theorem B451715 : Blo 299831 451715 := bstep (se 1 (by rfl) ⟨338786, by rfl⟩ : syracuseStep 451715 = 677573) B677573
theorem B451745 : Blo 299831 451745 := bstep (se 2 (by rfl) ⟨169404, by rfl⟩ : syracuseStep 451745 = 338809) B338809
theorem B681137 : Blo 299831 681137 := bstep (se 2 (by rfl) ⟨255426, by rfl⟩ : syracuseStep 681137 = 510853) B510853
theorem B451763 : Blo 299831 451763 := bstep (se 1 (by rfl) ⟨338822, by rfl⟩ : syracuseStep 451763 = 677645) B677645
theorem B681155 : Blo 299831 681155 := bstep (se 1 (by rfl) ⟨510866, by rfl⟩ : syracuseStep 681155 = 1021733) B1021733
theorem B451793 : Blo 299831 451793 := bstep (se 2 (by rfl) ⟨169422, by rfl⟩ : syracuseStep 451793 = 338845) B338845
theorem B451811 : Blo 299831 451811 := bstep (se 1 (by rfl) ⟨338858, by rfl⟩ : syracuseStep 451811 = 677717) B677717
theorem B3663089 : Blo 299831 3663089 := bstep (se 2 (by rfl) ⟨1373658, by rfl⟩ : syracuseStep 3663089 = 2747317) B2747317
theorem B451841 : Blo 299831 451841 := bstep (se 2 (by rfl) ⟨169440, by rfl⟩ : syracuseStep 451841 = 338881) B338881
theorem B451859 : Blo 299831 451859 := bstep (se 1 (by rfl) ⟨338894, by rfl⟩ : syracuseStep 451859 = 677789) B677789
theorem B484643 : Blo 299831 484643 := bstep (se 1 (by rfl) ⟨363482, by rfl⟩ : syracuseStep 484643 = 726965) B726965
theorem B451889 : Blo 299831 451889 := bstep (se 2 (by rfl) ⟨169458, by rfl⟩ : syracuseStep 451889 = 338917) B338917
theorem B451907 : Blo 299831 451907 := bstep (se 1 (by rfl) ⟨338930, by rfl⟩ : syracuseStep 451907 = 677861) B677861
theorem B451937 : Blo 299831 451937 := bstep (se 2 (by rfl) ⟨169476, by rfl⟩ : syracuseStep 451937 = 338953) B338953
theorem B451955 : Blo 299831 451955 := bstep (se 1 (by rfl) ⟨338966, by rfl⟩ : syracuseStep 451955 = 677933) B677933
theorem B451985 : Blo 299831 451985 := bstep (se 2 (by rfl) ⟨169494, by rfl⟩ : syracuseStep 451985 = 338989) B338989
theorem B452003 : Blo 299831 452003 := bstep (se 1 (by rfl) ⟨339002, by rfl⟩ : syracuseStep 452003 = 678005) B678005
theorem B452033 : Blo 299831 452033 := bstep (se 2 (by rfl) ⟨169512, by rfl⟩ : syracuseStep 452033 = 339025) B339025
theorem B648643 : Blo 299831 648643 := bstep (se 1 (by rfl) ⟨486482, by rfl⟩ : syracuseStep 648643 = 972965) B972965
theorem B681425 : Blo 299831 681425 := bstep (se 2 (by rfl) ⟨255534, by rfl⟩ : syracuseStep 681425 = 511069) B511069
theorem B452051 : Blo 299831 452051 := bstep (se 1 (by rfl) ⟨339038, by rfl⟩ : syracuseStep 452051 = 678077) B678077
theorem B681443 : Blo 299831 681443 := bstep (se 1 (by rfl) ⟨511082, by rfl⟩ : syracuseStep 681443 = 1022165) B1022165
theorem B452081 : Blo 299831 452081 := bstep (se 2 (by rfl) ⟨169530, by rfl⟩ : syracuseStep 452081 = 339061) B339061
theorem B452099 : Blo 299831 452099 := bstep (se 1 (by rfl) ⟨339074, by rfl⟩ : syracuseStep 452099 = 678149) B678149
theorem B452129 : Blo 299831 452129 := bstep (se 2 (by rfl) ⟨169548, by rfl⟩ : syracuseStep 452129 = 339097) B339097
theorem B452147 : Blo 299831 452147 := bstep (se 1 (by rfl) ⟨339110, by rfl⟩ : syracuseStep 452147 = 678221) B678221
theorem B452177 : Blo 299831 452177 := bstep (se 2 (by rfl) ⟨169566, by rfl⟩ : syracuseStep 452177 = 339133) B339133
theorem B452195 : Blo 299831 452195 := bstep (se 1 (by rfl) ⟨339146, by rfl⟩ : syracuseStep 452195 = 678293) B678293
theorem B452225 : Blo 299831 452225 := bstep (se 2 (by rfl) ⟨169584, by rfl⟩ : syracuseStep 452225 = 339169) B339169
theorem B452243 : Blo 299831 452243 := bstep (se 1 (by rfl) ⟨339182, by rfl⟩ : syracuseStep 452243 = 678365) B678365
theorem B452273 : Blo 299831 452273 := bstep (se 2 (by rfl) ⟨169602, by rfl⟩ : syracuseStep 452273 = 339205) B339205
theorem B452291 : Blo 299831 452291 := bstep (se 1 (by rfl) ⟨339218, by rfl⟩ : syracuseStep 452291 = 678437) B678437
theorem B452321 : Blo 299831 452321 := bstep (se 2 (by rfl) ⟨169620, by rfl⟩ : syracuseStep 452321 = 339241) B339241
theorem B681713 : Blo 299831 681713 := bstep (se 2 (by rfl) ⟨255642, by rfl⟩ : syracuseStep 681713 = 511285) B511285
theorem B452339 : Blo 299831 452339 := bstep (se 1 (by rfl) ⟨339254, by rfl⟩ : syracuseStep 452339 = 678509) B678509
theorem B681731 : Blo 299831 681731 := bstep (se 1 (by rfl) ⟨511298, by rfl⟩ : syracuseStep 681731 = 1022597) B1022597
theorem B452369 : Blo 299831 452369 := bstep (se 2 (by rfl) ⟨169638, by rfl⟩ : syracuseStep 452369 = 339277) B339277
theorem B452387 : Blo 299831 452387 := bstep (se 1 (by rfl) ⟨339290, by rfl⟩ : syracuseStep 452387 = 678581) B678581
theorem B452417 : Blo 299831 452417 := bstep (se 2 (by rfl) ⟨169656, by rfl⟩ : syracuseStep 452417 = 339313) B339313
theorem B1926989 : Blo 299831 1926989 := bstep (se 3 (by rfl) ⟨361310, by rfl⟩ : syracuseStep 1926989 = 722621) B722621
theorem B452435 : Blo 299831 452435 := bstep (se 1 (by rfl) ⟨339326, by rfl⟩ : syracuseStep 452435 = 678653) B678653
theorem B452465 : Blo 299831 452465 := bstep (se 2 (by rfl) ⟨169674, by rfl⟩ : syracuseStep 452465 = 339349) B339349
theorem B452483 : Blo 299831 452483 := bstep (se 1 (by rfl) ⟨339362, by rfl⟩ : syracuseStep 452483 = 678725) B678725
theorem B452513 : Blo 299831 452513 := bstep (se 2 (by rfl) ⟨169692, by rfl⟩ : syracuseStep 452513 = 339385) B339385
theorem B452531 : Blo 299831 452531 := bstep (se 1 (by rfl) ⟨339398, by rfl⟩ : syracuseStep 452531 = 678797) B678797
theorem B15591365 : Blo 299831 15591365 := bstep (se 4 (by rfl) ⟨1461690, by rfl⟩ : syracuseStep 15591365 = 2923381) B2923381
theorem B452561 : Blo 299831 452561 := bstep (se 2 (by rfl) ⟨169710, by rfl⟩ : syracuseStep 452561 = 339421) B339421
theorem B452579 : Blo 299831 452579 := bstep (se 1 (by rfl) ⟨339434, by rfl⟩ : syracuseStep 452579 = 678869) B678869
theorem B2287601 : Blo 299831 2287601 := bstep (se 2 (by rfl) ⟨857850, by rfl⟩ : syracuseStep 2287601 = 1715701) B1715701
theorem B452609 : Blo 299831 452609 := bstep (se 2 (by rfl) ⟨169728, by rfl⟩ : syracuseStep 452609 = 339457) B339457
theorem B1140749 : Blo 299831 1140749 := bstep (se 3 (by rfl) ⟨213890, by rfl⟩ : syracuseStep 1140749 = 427781) B427781
theorem B682001 : Blo 299831 682001 := bstep (se 2 (by rfl) ⟨255750, by rfl⟩ : syracuseStep 682001 = 511501) B511501
theorem B452627 : Blo 299831 452627 := bstep (se 1 (by rfl) ⟨339470, by rfl⟩ : syracuseStep 452627 = 678941) B678941
theorem B682019 : Blo 299831 682019 := bstep (se 1 (by rfl) ⟨511514, by rfl⟩ : syracuseStep 682019 = 1023029) B1023029
theorem B452657 : Blo 299831 452657 := bstep (se 2 (by rfl) ⟨169746, by rfl⟩ : syracuseStep 452657 = 339493) B339493
theorem B452675 : Blo 299831 452675 := bstep (se 1 (by rfl) ⟨339506, by rfl⟩ : syracuseStep 452675 = 679013) B679013
theorem B452705 : Blo 299831 452705 := bstep (se 2 (by rfl) ⟨169764, by rfl⟩ : syracuseStep 452705 = 339529) B339529
theorem B485489 : Blo 299831 485489 := bstep (se 2 (by rfl) ⟨182058, by rfl⟩ : syracuseStep 485489 = 364117) B364117
theorem B452723 : Blo 299831 452723 := bstep (se 1 (by rfl) ⟨339542, by rfl⟩ : syracuseStep 452723 = 679085) B679085
theorem B452753 : Blo 299831 452753 := bstep (se 2 (by rfl) ⟨169782, by rfl⟩ : syracuseStep 452753 = 339565) B339565
theorem B452771 : Blo 299831 452771 := bstep (se 1 (by rfl) ⟨339578, by rfl⟩ : syracuseStep 452771 = 679157) B679157
theorem B452801 : Blo 299831 452801 := bstep (se 2 (by rfl) ⟨169800, by rfl⟩ : syracuseStep 452801 = 339601) B339601
theorem B452819 : Blo 299831 452819 := bstep (se 1 (by rfl) ⟨339614, by rfl⟩ : syracuseStep 452819 = 679229) B679229
theorem B452849 : Blo 299831 452849 := bstep (se 2 (by rfl) ⟨169818, by rfl⟩ : syracuseStep 452849 = 339637) B339637
theorem B485617 : Blo 299831 485617 := bstep (se 2 (by rfl) ⟨182106, by rfl⟩ : syracuseStep 485617 = 364213) B364213
theorem B452867 : Blo 299831 452867 := bstep (se 1 (by rfl) ⟨339650, by rfl⟩ : syracuseStep 452867 = 679301) B679301
theorem B452897 : Blo 299831 452897 := bstep (se 2 (by rfl) ⟨169836, by rfl⟩ : syracuseStep 452897 = 339673) B339673
theorem B485681 : Blo 299831 485681 := bstep (se 2 (by rfl) ⟨182130, by rfl⟩ : syracuseStep 485681 = 364261) B364261
theorem B682289 : Blo 299831 682289 := bstep (se 2 (by rfl) ⟨255858, by rfl⟩ : syracuseStep 682289 = 511717) B511717
theorem B452915 : Blo 299831 452915 := bstep (se 1 (by rfl) ⟨339686, by rfl⟩ : syracuseStep 452915 = 679373) B679373
theorem B682307 : Blo 299831 682307 := bstep (se 1 (by rfl) ⟨511730, by rfl⟩ : syracuseStep 682307 = 1023461) B1023461
theorem B452945 : Blo 299831 452945 := bstep (se 2 (by rfl) ⟨169854, by rfl⟩ : syracuseStep 452945 = 339709) B339709
theorem B452963 : Blo 299831 452963 := bstep (se 1 (by rfl) ⟨339722, by rfl⟩ : syracuseStep 452963 = 679445) B679445
theorem B452993 : Blo 299831 452993 := bstep (se 2 (by rfl) ⟨169872, by rfl⟩ : syracuseStep 452993 = 339745) B339745
theorem B453011 : Blo 299831 453011 := bstep (se 1 (by rfl) ⟨339758, by rfl⟩ : syracuseStep 453011 = 679517) B679517
theorem B453041 : Blo 299831 453041 := bstep (se 2 (by rfl) ⟨169890, by rfl⟩ : syracuseStep 453041 = 339781) B339781
theorem B453059 : Blo 299831 453059 := bstep (se 1 (by rfl) ⟨339794, by rfl⟩ : syracuseStep 453059 = 679589) B679589
theorem B453089 : Blo 299831 453089 := bstep (se 2 (by rfl) ⟨169908, by rfl⟩ : syracuseStep 453089 = 339817) B339817
theorem B1370609 : Blo 299831 1370609 := bstep (se 2 (by rfl) ⟨513978, by rfl⟩ : syracuseStep 1370609 = 1027957) B1027957
theorem B453107 : Blo 299831 453107 := bstep (se 1 (by rfl) ⟨339830, by rfl⟩ : syracuseStep 453107 = 679661) B679661
theorem B453137 : Blo 299831 453137 := bstep (se 2 (by rfl) ⟨169926, by rfl⟩ : syracuseStep 453137 = 339853) B339853
theorem B453155 : Blo 299831 453155 := bstep (se 1 (by rfl) ⟨339866, by rfl⟩ : syracuseStep 453155 = 679733) B679733
theorem B453185 : Blo 299831 453185 := bstep (se 2 (by rfl) ⟨169944, by rfl⟩ : syracuseStep 453185 = 339889) B339889
theorem B682577 : Blo 299831 682577 := bstep (se 2 (by rfl) ⟨255966, by rfl⟩ : syracuseStep 682577 = 511933) B511933
theorem B453203 : Blo 299831 453203 := bstep (se 1 (by rfl) ⟨339902, by rfl⟩ : syracuseStep 453203 = 679805) B679805
theorem B322147 : Blo 299831 322147 := bstep (se 1 (by rfl) ⟨241610, by rfl⟩ : syracuseStep 322147 = 483221) B483221
theorem B518755 : Blo 299831 518755 := bstep (se 1 (by rfl) ⟨389066, by rfl⟩ : syracuseStep 518755 = 778133) B778133
theorem B682595 : Blo 299831 682595 := bstep (se 1 (by rfl) ⟨511946, by rfl⟩ : syracuseStep 682595 = 1023893) B1023893
theorem B453233 : Blo 299831 453233 := bstep (se 2 (by rfl) ⟨169962, by rfl⟩ : syracuseStep 453233 = 339925) B339925
theorem B453251 : Blo 299831 453251 := bstep (se 1 (by rfl) ⟨339938, by rfl⟩ : syracuseStep 453251 = 679877) B679877
theorem B453281 : Blo 299831 453281 := bstep (se 2 (by rfl) ⟨169980, by rfl⟩ : syracuseStep 453281 = 339961) B339961
theorem B453299 : Blo 299831 453299 := bstep (se 1 (by rfl) ⟨339974, by rfl⟩ : syracuseStep 453299 = 679949) B679949
theorem B453329 : Blo 299831 453329 := bstep (se 2 (by rfl) ⟨169998, by rfl⟩ : syracuseStep 453329 = 339997) B339997
theorem B453347 : Blo 299831 453347 := bstep (se 1 (by rfl) ⟨340010, by rfl⟩ : syracuseStep 453347 = 680021) B680021
theorem B453377 : Blo 299831 453377 := bstep (se 2 (by rfl) ⟨170016, by rfl⟩ : syracuseStep 453377 = 340033) B340033
theorem B453395 : Blo 299831 453395 := bstep (se 1 (by rfl) ⟨340046, by rfl⟩ : syracuseStep 453395 = 680093) B680093
theorem B1141553 : Blo 299831 1141553 := bstep (se 2 (by rfl) ⟨428082, by rfl⟩ : syracuseStep 1141553 = 856165) B856165
theorem B551729 : Blo 299831 551729 := bstep (se 2 (by rfl) ⟨206898, by rfl⟩ : syracuseStep 551729 = 413797) B413797
theorem B453425 : Blo 299831 453425 := bstep (se 2 (by rfl) ⟨170034, by rfl⟩ : syracuseStep 453425 = 340069) B340069
theorem B453443 : Blo 299831 453443 := bstep (se 1 (by rfl) ⟨340082, by rfl⟩ : syracuseStep 453443 = 680165) B680165
theorem B813901 : Blo 299831 813901 := bstep (se 3 (by rfl) ⟨152606, by rfl⟩ : syracuseStep 813901 = 305213) B305213
theorem B453473 : Blo 299831 453473 := bstep (se 2 (by rfl) ⟨170052, by rfl⟩ : syracuseStep 453473 = 340105) B340105
theorem B682865 : Blo 299831 682865 := bstep (se 2 (by rfl) ⟨256074, by rfl⟩ : syracuseStep 682865 = 512149) B512149
theorem B453491 : Blo 299831 453491 := bstep (se 1 (by rfl) ⟨340118, by rfl⟩ : syracuseStep 453491 = 680237) B680237
theorem B682883 : Blo 299831 682883 := bstep (se 1 (by rfl) ⟨512162, by rfl⟩ : syracuseStep 682883 = 1024325) B1024325
theorem B453521 : Blo 299831 453521 := bstep (se 2 (by rfl) ⟨170070, by rfl⟩ : syracuseStep 453521 = 340141) B340141
theorem B453539 : Blo 299831 453539 := bstep (se 1 (by rfl) ⟨340154, by rfl⟩ : syracuseStep 453539 = 680309) B680309
theorem B453569 : Blo 299831 453569 := bstep (se 2 (by rfl) ⟨170088, by rfl⟩ : syracuseStep 453569 = 340177) B340177
theorem B1633229 : Blo 299831 1633229 := bstep (se 3 (by rfl) ⟨306230, by rfl⟩ : syracuseStep 1633229 = 612461) B612461
theorem B453587 : Blo 299831 453587 := bstep (se 1 (by rfl) ⟨340190, by rfl⟩ : syracuseStep 453587 = 680381) B680381
theorem B453617 : Blo 299831 453617 := bstep (se 2 (by rfl) ⟨170106, by rfl⟩ : syracuseStep 453617 = 340213) B340213
theorem B453635 : Blo 299831 453635 := bstep (se 1 (by rfl) ⟨340226, by rfl⟩ : syracuseStep 453635 = 680453) B680453
theorem B322579 : Blo 299831 322579 := bstep (se 1 (by rfl) ⟨241934, by rfl⟩ : syracuseStep 322579 = 483869) B483869
theorem B453665 : Blo 299831 453665 := bstep (se 2 (by rfl) ⟨170124, by rfl⟩ : syracuseStep 453665 = 340249) B340249
theorem B453683 : Blo 299831 453683 := bstep (se 1 (by rfl) ⟨340262, by rfl⟩ : syracuseStep 453683 = 680525) B680525
theorem B453713 : Blo 299831 453713 := bstep (se 2 (by rfl) ⟨170142, by rfl⟩ : syracuseStep 453713 = 340285) B340285
theorem B453731 : Blo 299831 453731 := bstep (se 1 (by rfl) ⟨340298, by rfl⟩ : syracuseStep 453731 = 680597) B680597
theorem B453761 : Blo 299831 453761 := bstep (se 2 (by rfl) ⟨170160, by rfl⟩ : syracuseStep 453761 = 340321) B340321
theorem B1731725 : Blo 299831 1731725 := bstep (se 3 (by rfl) ⟨324698, by rfl⟩ : syracuseStep 1731725 = 649397) B649397
theorem B814225 : Blo 299831 814225 := bstep (se 2 (by rfl) ⟨305334, by rfl⟩ : syracuseStep 814225 = 610669) B610669
theorem B683153 : Blo 299831 683153 := bstep (se 2 (by rfl) ⟨256182, by rfl⟩ : syracuseStep 683153 = 512365) B512365
theorem B453779 : Blo 299831 453779 := bstep (se 1 (by rfl) ⟨340334, by rfl⟩ : syracuseStep 453779 = 680669) B680669
theorem B683171 : Blo 299831 683171 := bstep (se 1 (by rfl) ⟨512378, by rfl⟩ : syracuseStep 683171 = 1024757) B1024757
theorem B453809 : Blo 299831 453809 := bstep (se 2 (by rfl) ⟨170178, by rfl⟩ : syracuseStep 453809 = 340357) B340357
theorem B453827 : Blo 299831 453827 := bstep (se 1 (by rfl) ⟨340370, by rfl⟩ : syracuseStep 453827 = 680741) B680741
theorem B453857 : Blo 299831 453857 := bstep (se 2 (by rfl) ⟨170196, by rfl⟩ : syracuseStep 453857 = 340393) B340393
theorem B453875 : Blo 299831 453875 := bstep (se 1 (by rfl) ⟨340406, by rfl⟩ : syracuseStep 453875 = 680813) B680813
theorem B453905 : Blo 299831 453905 := bstep (se 2 (by rfl) ⟨170214, by rfl⟩ : syracuseStep 453905 = 340429) B340429
theorem B453923 : Blo 299831 453923 := bstep (se 1 (by rfl) ⟨340442, by rfl⟩ : syracuseStep 453923 = 680885) B680885
theorem B453953 : Blo 299831 453953 := bstep (se 2 (by rfl) ⟨170232, by rfl⟩ : syracuseStep 453953 = 340465) B340465
theorem B453971 : Blo 299831 453971 := bstep (se 1 (by rfl) ⟨340478, by rfl⟩ : syracuseStep 453971 = 680957) B680957
theorem B454001 : Blo 299831 454001 := bstep (se 2 (by rfl) ⟨170250, by rfl⟩ : syracuseStep 454001 = 340501) B340501
theorem B454019 : Blo 299831 454019 := bstep (se 1 (by rfl) ⟨340514, by rfl⟩ : syracuseStep 454019 = 681029) B681029
theorem B454049 : Blo 299831 454049 := bstep (se 2 (by rfl) ⟨170268, by rfl⟩ : syracuseStep 454049 = 340537) B340537
theorem B683441 : Blo 299831 683441 := bstep (se 2 (by rfl) ⟨256290, by rfl⟩ : syracuseStep 683441 = 512581) B512581
theorem B454067 : Blo 299831 454067 := bstep (se 1 (by rfl) ⟨340550, by rfl⟩ : syracuseStep 454067 = 681101) B681101
theorem B683459 : Blo 299831 683459 := bstep (se 1 (by rfl) ⟨512594, by rfl⟩ : syracuseStep 683459 = 1025189) B1025189
theorem B1142221 : Blo 299831 1142221 := bstep (se 3 (by rfl) ⟨214166, by rfl⟩ : syracuseStep 1142221 = 428333) B428333
theorem B454097 : Blo 299831 454097 := bstep (se 2 (by rfl) ⟨170286, by rfl⟩ : syracuseStep 454097 = 340573) B340573
theorem B454115 : Blo 299831 454115 := bstep (se 1 (by rfl) ⟨340586, by rfl⟩ : syracuseStep 454115 = 681173) B681173
theorem B454145 : Blo 299831 454145 := bstep (se 2 (by rfl) ⟨170304, by rfl⟩ : syracuseStep 454145 = 340609) B340609
theorem B454163 : Blo 299831 454163 := bstep (se 1 (by rfl) ⟨340622, by rfl⟩ : syracuseStep 454163 = 681245) B681245
theorem B454193 : Blo 299831 454193 := bstep (se 2 (by rfl) ⟨170322, by rfl⟩ : syracuseStep 454193 = 340645) B340645
theorem B454211 : Blo 299831 454211 := bstep (se 1 (by rfl) ⟨340658, by rfl⟩ : syracuseStep 454211 = 681317) B681317
theorem B454241 : Blo 299831 454241 := bstep (se 2 (by rfl) ⟨170340, by rfl⟩ : syracuseStep 454241 = 340681) B340681
theorem B454259 : Blo 299831 454259 := bstep (se 1 (by rfl) ⟨340694, by rfl⟩ : syracuseStep 454259 = 681389) B681389
theorem B454289 : Blo 299831 454289 := bstep (se 2 (by rfl) ⟨170358, by rfl⟩ : syracuseStep 454289 = 340717) B340717
theorem B454307 : Blo 299831 454307 := bstep (se 1 (by rfl) ⟨340730, by rfl⟩ : syracuseStep 454307 = 681461) B681461
theorem B454337 : Blo 299831 454337 := bstep (se 2 (by rfl) ⟨170376, by rfl⟩ : syracuseStep 454337 = 340753) B340753
theorem B454355 : Blo 299831 454355 := bstep (se 1 (by rfl) ⟨340766, by rfl⟩ : syracuseStep 454355 = 681533) B681533
theorem B454385 : Blo 299831 454385 := bstep (se 2 (by rfl) ⟨170394, by rfl⟩ : syracuseStep 454385 = 340789) B340789
theorem B454403 : Blo 299831 454403 := bstep (se 1 (by rfl) ⟨340802, by rfl⟩ : syracuseStep 454403 = 681605) B681605
theorem B41676565 : Blo 299831 41676565 := bstep (se 6 (by rfl) ⟨976794, by rfl⟩ : syracuseStep 41676565 = 1953589) B1953589
theorem B454433 : Blo 299831 454433 := bstep (se 2 (by rfl) ⟨170412, by rfl⟩ : syracuseStep 454433 = 340825) B340825
theorem B454451 : Blo 299831 454451 := bstep (se 1 (by rfl) ⟨340838, by rfl⟩ : syracuseStep 454451 = 681677) B681677
theorem B454481 : Blo 299831 454481 := bstep (se 2 (by rfl) ⟨170430, by rfl⟩ : syracuseStep 454481 = 340861) B340861
theorem B454499 : Blo 299831 454499 := bstep (se 1 (by rfl) ⟨340874, by rfl⟩ : syracuseStep 454499 = 681749) B681749
theorem B454529 : Blo 299831 454529 := bstep (se 2 (by rfl) ⟨170448, by rfl⟩ : syracuseStep 454529 = 340897) B340897
theorem B454547 : Blo 299831 454547 := bstep (se 1 (by rfl) ⟨340910, by rfl⟩ : syracuseStep 454547 = 681821) B681821
theorem B454577 : Blo 299831 454577 := bstep (se 2 (by rfl) ⟨170466, by rfl⟩ : syracuseStep 454577 = 340933) B340933
theorem B1535921 : Blo 299831 1535921 := bstep (se 2 (by rfl) ⟨575970, by rfl⟩ : syracuseStep 1535921 = 1151941) B1151941
theorem B454595 : Blo 299831 454595 := bstep (se 1 (by rfl) ⟨340946, by rfl⟩ : syracuseStep 454595 = 681893) B681893
theorem B454625 : Blo 299831 454625 := bstep (se 2 (by rfl) ⟨170484, by rfl⟩ : syracuseStep 454625 = 340969) B340969
theorem B454643 : Blo 299831 454643 := bstep (se 1 (by rfl) ⟨340982, by rfl⟩ : syracuseStep 454643 = 681965) B681965
theorem B454673 : Blo 299831 454673 := bstep (se 2 (by rfl) ⟨170502, by rfl⟩ : syracuseStep 454673 = 341005) B341005
theorem B454691 : Blo 299831 454691 := bstep (se 1 (by rfl) ⟨341018, by rfl⟩ : syracuseStep 454691 = 682037) B682037
theorem B815153 : Blo 299831 815153 := bstep (se 2 (by rfl) ⟨305682, by rfl⟩ : syracuseStep 815153 = 611365) B611365
theorem B454721 : Blo 299831 454721 := bstep (se 2 (by rfl) ⟨170520, by rfl⟩ : syracuseStep 454721 = 341041) B341041
theorem B454739 : Blo 299831 454739 := bstep (se 1 (by rfl) ⟨341054, by rfl⟩ : syracuseStep 454739 = 682109) B682109
theorem B454769 : Blo 299831 454769 := bstep (se 2 (by rfl) ⟨170538, by rfl⟩ : syracuseStep 454769 = 341077) B341077
theorem B454787 : Blo 299831 454787 := bstep (se 1 (by rfl) ⟨341090, by rfl⟩ : syracuseStep 454787 = 682181) B682181
theorem B454817 : Blo 299831 454817 := bstep (se 2 (by rfl) ⟨170556, by rfl⟩ : syracuseStep 454817 = 341113) B341113
theorem B454835 : Blo 299831 454835 := bstep (se 1 (by rfl) ⟨341126, by rfl⟩ : syracuseStep 454835 = 682253) B682253
theorem B454865 : Blo 299831 454865 := bstep (se 2 (by rfl) ⟨170574, by rfl⟩ : syracuseStep 454865 = 341149) B341149
theorem B3207395 : Blo 299831 3207395 := bstep (se 1 (by rfl) ⟨2405546, by rfl⟩ : syracuseStep 3207395 = 4811093) B4811093
theorem B1143011 : Blo 299831 1143011 := bstep (se 1 (by rfl) ⟨857258, by rfl⟩ : syracuseStep 1143011 = 1714517) B1714517
theorem B454883 : Blo 299831 454883 := bstep (se 1 (by rfl) ⟨341162, by rfl⟩ : syracuseStep 454883 = 682325) B682325
theorem B454913 : Blo 299831 454913 := bstep (se 2 (by rfl) ⟨170592, by rfl⟩ : syracuseStep 454913 = 341185) B341185
theorem B323843 : Blo 299831 323843 := bstep (se 1 (by rfl) ⟨242882, by rfl⟩ : syracuseStep 323843 = 485765) B485765
theorem B454931 : Blo 299831 454931 := bstep (se 1 (by rfl) ⟨341198, by rfl⟩ : syracuseStep 454931 = 682397) B682397
theorem B1012013 : Blo 299831 1012013 := bstep (se 3 (by rfl) ⟨189752, by rfl⟩ : syracuseStep 1012013 = 379505) B379505
theorem B454961 : Blo 299831 454961 := bstep (se 2 (by rfl) ⟨170610, by rfl⟩ : syracuseStep 454961 = 341221) B341221
theorem B454979 : Blo 299831 454979 := bstep (se 1 (by rfl) ⟨341234, by rfl⟩ : syracuseStep 454979 = 682469) B682469
theorem B455009 : Blo 299831 455009 := bstep (se 2 (by rfl) ⟨170628, by rfl⟩ : syracuseStep 455009 = 341257) B341257
theorem B1012067 : Blo 299831 1012067 := bstep (se 1 (by rfl) ⟨759050, by rfl⟩ : syracuseStep 1012067 = 1518101) B1518101
theorem B455027 : Blo 299831 455027 := bstep (se 1 (by rfl) ⟨341270, by rfl⟩ : syracuseStep 455027 = 682541) B682541
theorem B455057 : Blo 299831 455057 := bstep (se 2 (by rfl) ⟨170646, by rfl⟩ : syracuseStep 455057 = 341293) B341293
theorem B455075 : Blo 299831 455075 := bstep (se 1 (by rfl) ⟨341306, by rfl⟩ : syracuseStep 455075 = 682613) B682613
theorem B455105 : Blo 299831 455105 := bstep (se 2 (by rfl) ⟨170664, by rfl⟩ : syracuseStep 455105 = 341329) B341329
theorem B455123 : Blo 299831 455123 := bstep (se 1 (by rfl) ⟨341342, by rfl⟩ : syracuseStep 455123 = 682685) B682685
theorem B455153 : Blo 299831 455153 := bstep (se 2 (by rfl) ⟨170682, by rfl⟩ : syracuseStep 455153 = 341365) B341365
theorem B455171 : Blo 299831 455171 := bstep (se 1 (by rfl) ⟨341378, by rfl⟩ : syracuseStep 455171 = 682757) B682757
theorem B455201 : Blo 299831 455201 := bstep (se 2 (by rfl) ⟨170700, by rfl⟩ : syracuseStep 455201 = 341401) B341401
theorem B455219 : Blo 299831 455219 := bstep (se 1 (by rfl) ⟨341414, by rfl⟩ : syracuseStep 455219 = 682829) B682829
theorem B455249 : Blo 299831 455249 := bstep (se 2 (by rfl) ⟨170718, by rfl⟩ : syracuseStep 455249 = 341437) B341437
theorem B455267 : Blo 299831 455267 := bstep (se 1 (by rfl) ⟨341450, by rfl⟩ : syracuseStep 455267 = 682901) B682901
theorem B1012337 : Blo 299831 1012337 := bstep (se 2 (by rfl) ⟨379626, by rfl⟩ : syracuseStep 1012337 = 759253) B759253
theorem B455297 : Blo 299831 455297 := bstep (se 2 (by rfl) ⟨170736, by rfl⟩ : syracuseStep 455297 = 341473) B341473
theorem B455315 : Blo 299831 455315 := bstep (se 1 (by rfl) ⟨341486, by rfl⟩ : syracuseStep 455315 = 682973) B682973
theorem B455345 : Blo 299831 455345 := bstep (se 2 (by rfl) ⟨170754, by rfl⟩ : syracuseStep 455345 = 341509) B341509
theorem B455363 : Blo 299831 455363 := bstep (se 1 (by rfl) ⟨341522, by rfl⟩ : syracuseStep 455363 = 683045) B683045
theorem B455393 : Blo 299831 455393 := bstep (se 2 (by rfl) ⟨170772, by rfl⟩ : syracuseStep 455393 = 341545) B341545
theorem B455411 : Blo 299831 455411 := bstep (se 1 (by rfl) ⟨341558, by rfl⟩ : syracuseStep 455411 = 683117) B683117
theorem B455441 : Blo 299831 455441 := bstep (se 2 (by rfl) ⟨170790, by rfl⟩ : syracuseStep 455441 = 341581) B341581
theorem B455459 : Blo 299831 455459 := bstep (se 1 (by rfl) ⟨341594, by rfl⟩ : syracuseStep 455459 = 683189) B683189
theorem B455489 : Blo 299831 455489 := bstep (se 2 (by rfl) ⟨170808, by rfl⟩ : syracuseStep 455489 = 341617) B341617
theorem B619331 : Blo 299831 619331 := bstep (se 1 (by rfl) ⟨464498, by rfl⟩ : syracuseStep 619331 = 928997) B928997
theorem B455507 : Blo 299831 455507 := bstep (se 1 (by rfl) ⟨341630, by rfl⟩ : syracuseStep 455507 = 683261) B683261
theorem B1143665 : Blo 299831 1143665 := bstep (se 2 (by rfl) ⟨428874, by rfl⟩ : syracuseStep 1143665 = 857749) B857749
theorem B455537 : Blo 299831 455537 := bstep (se 2 (by rfl) ⟨170826, by rfl⟩ : syracuseStep 455537 = 341653) B341653
theorem B455555 : Blo 299831 455555 := bstep (se 1 (by rfl) ⟨341666, by rfl⟩ : syracuseStep 455555 = 683333) B683333
theorem B455585 : Blo 299831 455585 := bstep (se 2 (by rfl) ⟨170844, by rfl⟩ : syracuseStep 455585 = 341689) B341689
theorem B455603 : Blo 299831 455603 := bstep (se 1 (by rfl) ⟨341702, by rfl⟩ : syracuseStep 455603 = 683405) B683405
theorem B455633 : Blo 299831 455633 := bstep (se 2 (by rfl) ⟨170862, by rfl⟩ : syracuseStep 455633 = 341725) B341725
theorem B455651 : Blo 299831 455651 := bstep (se 1 (by rfl) ⟨341738, by rfl⟩ : syracuseStep 455651 = 683477) B683477
theorem B455681 : Blo 299831 455681 := bstep (se 2 (by rfl) ⟨170880, by rfl⟩ : syracuseStep 455681 = 341761) B341761
theorem B455699 : Blo 299831 455699 := bstep (se 1 (by rfl) ⟨341774, by rfl⟩ : syracuseStep 455699 = 683549) B683549
theorem B455729 : Blo 299831 455729 := bstep (se 2 (by rfl) ⟨170898, by rfl⟩ : syracuseStep 455729 = 341797) B341797
theorem B455747 : Blo 299831 455747 := bstep (se 1 (by rfl) ⟨341810, by rfl⟩ : syracuseStep 455747 = 683621) B683621
theorem B1012877 : Blo 299831 1012877 := bstep (se 3 (by rfl) ⟨189914, by rfl⟩ : syracuseStep 1012877 = 379829) B379829
theorem B1012931 : Blo 299831 1012931 := bstep (se 1 (by rfl) ⟨759698, by rfl⟩ : syracuseStep 1012931 = 1519397) B1519397
theorem B816365 : Blo 299831 816365 := bstep (se 3 (by rfl) ⟨153068, by rfl⟩ : syracuseStep 816365 = 306137) B306137
theorem B1537379 : Blo 299831 1537379 := bstep (se 1 (by rfl) ⟨1153034, by rfl⟩ : syracuseStep 1537379 = 2306069) B2306069
theorem B1013201 : Blo 299831 1013201 := bstep (se 2 (by rfl) ⟨379950, by rfl⟩ : syracuseStep 1013201 = 759901) B759901
theorem B2618993 : Blo 299831 2618993 := bstep (se 2 (by rfl) ⟨982122, by rfl⟩ : syracuseStep 2618993 = 1964245) B1964245
theorem B1013741 : Blo 299831 1013741 := bstep (se 3 (by rfl) ⟨190076, by rfl⟩ : syracuseStep 1013741 = 380153) B380153
theorem B1013795 : Blo 299831 1013795 := bstep (se 1 (by rfl) ⟨760346, by rfl⟩ : syracuseStep 1013795 = 1520693) B1520693
theorem B915491 : Blo 299831 915491 := bstep (se 1 (by rfl) ⟨686618, by rfl⟩ : syracuseStep 915491 = 1373237) B1373237
theorem B817361 : Blo 299831 817361 := bstep (se 2 (by rfl) ⟨306510, by rfl⟩ : syracuseStep 817361 = 613021) B613021
theorem B1145123 : Blo 299831 1145123 := bstep (se 1 (by rfl) ⟨858842, by rfl⟩ : syracuseStep 1145123 = 1717685) B1717685
theorem B1014065 : Blo 299831 1014065 := bstep (se 2 (by rfl) ⟨380274, by rfl⟩ : syracuseStep 1014065 = 760549) B760549
theorem B1145137 : Blo 299831 1145137 := bstep (se 2 (by rfl) ⟨429426, by rfl⟩ : syracuseStep 1145137 = 858853) B858853
theorem B9435761 : Blo 299831 9435761 := bstep (se 2 (by rfl) ⟨3538410, by rfl⟩ : syracuseStep 9435761 = 7076821) B7076821
theorem B2161349 : Blo 299831 2161349 := bstep (se 4 (by rfl) ⟨202626, by rfl⟩ : syracuseStep 2161349 = 405253) B405253
theorem B1014605 : Blo 299831 1014605 := bstep (se 3 (by rfl) ⟨190238, by rfl⟩ : syracuseStep 1014605 = 380477) B380477
theorem B1014659 : Blo 299831 1014659 := bstep (se 1 (by rfl) ⟨760994, by rfl⟩ : syracuseStep 1014659 = 1521989) B1521989
theorem B1309603 : Blo 299831 1309603 := bstep (se 1 (by rfl) ⟨982202, by rfl⟩ : syracuseStep 1309603 = 1964405) B1964405
theorem B1014929 : Blo 299831 1014929 := bstep (se 2 (by rfl) ⟨380598, by rfl⟩ : syracuseStep 1014929 = 761197) B761197
theorem B1375501 : Blo 299831 1375501 := bstep (se 3 (by rfl) ⟨257906, by rfl⟩ : syracuseStep 1375501 = 515813) B515813
theorem B1441165 : Blo 299831 1441165 := bstep (se 3 (by rfl) ⟨270218, by rfl⟩ : syracuseStep 1441165 = 540437) B540437
theorem B3079565 : Blo 299831 3079565 := bstep (se 3 (by rfl) ⟨577418, by rfl⟩ : syracuseStep 3079565 = 1154837) B1154837
theorem B1015469 : Blo 299831 1015469 := bstep (se 3 (by rfl) ⟨190400, by rfl⟩ : syracuseStep 1015469 = 380801) B380801
theorem B1015523 : Blo 299831 1015523 := bstep (se 1 (by rfl) ⟨761642, by rfl⟩ : syracuseStep 1015523 = 1523285) B1523285
theorem B1146595 : Blo 299831 1146595 := bstep (se 1 (by rfl) ⟨859946, by rfl⟩ : syracuseStep 1146595 = 1719893) B1719893
theorem B1015793 : Blo 299831 1015793 := bstep (se 2 (by rfl) ⟨380922, by rfl⟩ : syracuseStep 1015793 = 761845) B761845
theorem B1015901 : Blo 299831 1015901 := bstep (se 3 (by rfl) ⟨190481, by rfl⟩ : syracuseStep 1015901 = 380963) B380963
theorem B491723 : Blo 299831 491723 := bstep (se 1 (by rfl) ⟨368792, by rfl⟩ : syracuseStep 491723 = 737585) B737585
theorem B360715 : Blo 299831 360715 := bstep (se 1 (by rfl) ⟨270536, by rfl⟩ : syracuseStep 360715 = 541073) B541073
theorem B2458147 : Blo 299831 2458147 := bstep (se 1 (by rfl) ⟨1843610, by rfl⟩ : syracuseStep 2458147 = 3687221) B3687221
theorem B8553053 : Blo 299831 8553053 := bstep (se 3 (by rfl) ⟨1603697, by rfl⟩ : syracuseStep 8553053 = 3207395) B3207395
theorem B361099 : Blo 299831 361099 := bstep (se 1 (by rfl) ⟨270824, by rfl⟩ : syracuseStep 361099 = 541649) B541649
theorem B361291 : Blo 299831 361291 := bstep (se 1 (by rfl) ⟨270968, by rfl⟩ : syracuseStep 361291 = 541937) B541937
theorem B459595 : Blo 299831 459595 := bstep (se 1 (by rfl) ⟨344696, by rfl⟩ : syracuseStep 459595 = 689393) B689393
theorem B3277745 : Blo 299831 3277745 := bstep (se 2 (by rfl) ⟨1229154, by rfl⟩ : syracuseStep 3277745 = 2458309) B2458309
theorem B1147841 : Blo 299831 1147841 := bstep (se 2 (by rfl) ⟨430440, by rfl⟩ : syracuseStep 1147841 = 860881) B860881
theorem B19104709 : Blo 299831 19104709 := bstep (se 4 (by rfl) ⟨1791066, by rfl⟩ : syracuseStep 19104709 = 3582133) B3582133
theorem B1017035 : Blo 299831 1017035 := bstep (se 1 (by rfl) ⟨762776, by rfl⟩ : syracuseStep 1017035 = 1525553) B1525553
theorem B1017305 : Blo 299831 1017305 := bstep (se 2 (by rfl) ⟨381489, by rfl⟩ : syracuseStep 1017305 = 762979) B762979
theorem B4130605 : Blo 299831 4130605 := bstep (se 3 (by rfl) ⟨774488, by rfl⟩ : syracuseStep 4130605 = 1548977) B1548977
theorem B690187 : Blo 299831 690187 := bstep (se 1 (by rfl) ⟨517640, by rfl⟩ : syracuseStep 690187 = 1035281) B1035281
theorem B1018007 : Blo 299831 1018007 := bstep (se 1 (by rfl) ⟨763505, by rfl⟩ : syracuseStep 1018007 = 1527011) B1527011
theorem B723275 : Blo 299831 723275 := bstep (se 1 (by rfl) ⟨542456, by rfl⟩ : syracuseStep 723275 = 1084913) B1084913
theorem B3869045 : Blo 299831 3869045 := bstep (se 5 (by rfl) ⟨181361, by rfl⟩ : syracuseStep 3869045 = 362723) B362723
theorem B1149329 : Blo 299831 1149329 := bstep (se 2 (by rfl) ⟨430998, by rfl⟩ : syracuseStep 1149329 = 861997) B861997
theorem B854707 : Blo 299831 854707 := bstep (se 1 (by rfl) ⟨641030, by rfl⟩ : syracuseStep 854707 = 1282061) B1282061
theorem B1018547 : Blo 299831 1018547 := bstep (se 1 (by rfl) ⟨763910, by rfl⟩ : syracuseStep 1018547 = 1527821) B1527821
theorem B1149785 : Blo 299831 1149785 := bstep (se 2 (by rfl) ⟨431169, by rfl⟩ : syracuseStep 1149785 = 862339) B862339
theorem B1018817 : Blo 299831 1018817 := bstep (se 2 (by rfl) ⟨382056, by rfl⟩ : syracuseStep 1018817 = 764113) B764113
theorem B5049305 : Blo 299831 5049305 := bstep (se 2 (by rfl) ⟨1893489, by rfl⟩ : syracuseStep 5049305 = 3786979) B3786979
theorem B1412099 : Blo 299831 1412099 := bstep (se 1 (by rfl) ⟨1059074, by rfl⟩ : syracuseStep 1412099 = 2118149) B2118149
theorem B1313795 : Blo 299831 1313795 := bstep (se 1 (by rfl) ⟨985346, by rfl⟩ : syracuseStep 1313795 = 1970693) B1970693
theorem B1149997 : Blo 299831 1149997 := bstep (se 3 (by rfl) ⟨215624, by rfl⟩ : syracuseStep 1149997 = 431249) B431249
theorem B2591837 : Blo 299831 2591837 := bstep (se 3 (by rfl) ⟨485969, by rfl⟩ : syracuseStep 2591837 = 971939) B971939
theorem B1150301 : Blo 299831 1150301 := bstep (se 3 (by rfl) ⟨215681, by rfl⟩ : syracuseStep 1150301 = 431363) B431363
theorem B691673 : Blo 299831 691673 := bstep (se 2 (by rfl) ⟨259377, by rfl⟩ : syracuseStep 691673 = 518755) B518755
theorem B1019357 : Blo 299831 1019357 := bstep (se 3 (by rfl) ⟨191129, by rfl⟩ : syracuseStep 1019357 = 382259) B382259
theorem B2330147 : Blo 299831 2330147 := bstep (se 1 (by rfl) ⟨1747610, by rfl⟩ : syracuseStep 2330147 = 3495221) B3495221
theorem B855755 : Blo 299831 855755 := bstep (se 1 (by rfl) ⟨641816, by rfl⟩ : syracuseStep 855755 = 1283633) B1283633
theorem B724697 : Blo 299831 724697 := bstep (se 2 (by rfl) ⟨271761, by rfl⟩ : syracuseStep 724697 = 543523) B543523
theorem B1085201 : Blo 299831 1085201 := bstep (se 2 (by rfl) ⟨406950, by rfl⟩ : syracuseStep 1085201 = 813901) B813901
theorem B430105 : Blo 299831 430105 := bstep (se 2 (by rfl) ⟨161289, by rfl⟩ : syracuseStep 430105 = 322579) B322579
theorem B692311 : Blo 299831 692311 := bstep (se 1 (by rfl) ⟨519233, by rfl⟩ : syracuseStep 692311 = 1038467) B1038467
theorem B4657333 : Blo 299831 4657333 := bstep (se 5 (by rfl) ⟨218312, by rfl⟩ : syracuseStep 4657333 = 436625) B436625
theorem B1085633 : Blo 299831 1085633 := bstep (se 2 (by rfl) ⟨407112, by rfl⟩ : syracuseStep 1085633 = 814225) B814225
theorem B921817 : Blo 299831 921817 := bstep (se 2 (by rfl) ⟨345681, by rfl⟩ : syracuseStep 921817 = 691363) B691363
theorem B6983981 : Blo 299831 6983981 := bstep (se 3 (by rfl) ⟨1309496, by rfl⟩ : syracuseStep 6983981 = 2618993) B2618993
theorem B2068811 : Blo 299831 2068811 := bstep (se 1 (by rfl) ⟨1551608, by rfl⟩ : syracuseStep 2068811 = 3103217) B3103217
theorem B1020491 : Blo 299831 1020491 := bstep (se 1 (by rfl) ⟨765368, by rfl⟩ : syracuseStep 1020491 = 1530737) B1530737
theorem B299831 : Blo 299831 299831 := bstep (se 1 (by rfl) ⟨224873, by rfl⟩ : syracuseStep 299831 = 449747) B449747
theorem B299851 : Blo 299831 299851 := bstep (se 1 (by rfl) ⟨224888, by rfl⟩ : syracuseStep 299851 = 449777) B449777
theorem B299863 : Blo 299831 299863 := bstep (se 1 (by rfl) ⟨224897, by rfl⟩ : syracuseStep 299863 = 449795) B449795
theorem B1020761 : Blo 299831 1020761 := bstep (se 2 (by rfl) ⟨382785, by rfl⟩ : syracuseStep 1020761 = 765571) B765571
theorem B299883 : Blo 299831 299883 := bstep (se 1 (by rfl) ⟨224912, by rfl⟩ : syracuseStep 299883 = 449825) B449825
theorem B299895 : Blo 299831 299895 := bstep (se 1 (by rfl) ⟨224921, by rfl⟩ : syracuseStep 299895 = 449843) B449843
theorem B299915 : Blo 299831 299915 := bstep (se 1 (by rfl) ⟨224936, by rfl⟩ : syracuseStep 299915 = 449873) B449873
theorem B299927 : Blo 299831 299927 := bstep (se 1 (by rfl) ⟨224945, by rfl⟩ : syracuseStep 299927 = 449891) B449891
theorem B299947 : Blo 299831 299947 := bstep (se 1 (by rfl) ⟨224960, by rfl⟩ : syracuseStep 299947 = 449921) B449921
theorem B299959 : Blo 299831 299959 := bstep (se 1 (by rfl) ⟨224969, by rfl⟩ : syracuseStep 299959 = 449939) B449939
theorem B299979 : Blo 299831 299979 := bstep (se 1 (by rfl) ⟨224984, by rfl⟩ : syracuseStep 299979 = 449969) B449969
theorem B299991 : Blo 299831 299991 := bstep (se 1 (by rfl) ⟨224993, by rfl⟩ : syracuseStep 299991 = 449987) B449987
theorem B300011 : Blo 299831 300011 := bstep (se 1 (by rfl) ⟨225008, by rfl⟩ : syracuseStep 300011 = 450017) B450017
theorem B300023 : Blo 299831 300023 := bstep (se 1 (by rfl) ⟨225017, by rfl⟩ : syracuseStep 300023 = 450035) B450035
theorem B300043 : Blo 299831 300043 := bstep (se 1 (by rfl) ⟨225032, by rfl⟩ : syracuseStep 300043 = 450065) B450065
theorem B300055 : Blo 299831 300055 := bstep (se 1 (by rfl) ⟨225041, by rfl⟩ : syracuseStep 300055 = 450083) B450083
theorem B300075 : Blo 299831 300075 := bstep (se 1 (by rfl) ⟨225056, by rfl⟩ : syracuseStep 300075 = 450113) B450113
theorem B300087 : Blo 299831 300087 := bstep (se 1 (by rfl) ⟨225065, by rfl⟩ : syracuseStep 300087 = 450131) B450131
theorem B300107 : Blo 299831 300107 := bstep (se 1 (by rfl) ⟨225080, by rfl⟩ : syracuseStep 300107 = 450161) B450161
theorem B300119 : Blo 299831 300119 := bstep (se 1 (by rfl) ⟨225089, by rfl⟩ : syracuseStep 300119 = 450179) B450179
theorem B1840229 : Blo 299831 1840229 := bstep (se 4 (by rfl) ⟨172521, by rfl⟩ : syracuseStep 1840229 = 345043) B345043
theorem B300139 : Blo 299831 300139 := bstep (se 1 (by rfl) ⟨225104, by rfl⟩ : syracuseStep 300139 = 450209) B450209
theorem B300151 : Blo 299831 300151 := bstep (se 1 (by rfl) ⟨225113, by rfl⟩ : syracuseStep 300151 = 450227) B450227
theorem B300171 : Blo 299831 300171 := bstep (se 1 (by rfl) ⟨225128, by rfl⟩ : syracuseStep 300171 = 450257) B450257
theorem B300183 : Blo 299831 300183 := bstep (se 1 (by rfl) ⟨225137, by rfl⟩ : syracuseStep 300183 = 450275) B450275
theorem B300203 : Blo 299831 300203 := bstep (se 1 (by rfl) ⟨225152, by rfl⟩ : syracuseStep 300203 = 450305) B450305
theorem B300215 : Blo 299831 300215 := bstep (se 1 (by rfl) ⟨225161, by rfl⟩ : syracuseStep 300215 = 450323) B450323
theorem B300235 : Blo 299831 300235 := bstep (se 1 (by rfl) ⟨225176, by rfl⟩ : syracuseStep 300235 = 450353) B450353
theorem B300247 : Blo 299831 300247 := bstep (se 1 (by rfl) ⟨225185, by rfl⟩ : syracuseStep 300247 = 450371) B450371
theorem B300267 : Blo 299831 300267 := bstep (se 1 (by rfl) ⟨225200, by rfl⟩ : syracuseStep 300267 = 450401) B450401
theorem B300279 : Blo 299831 300279 := bstep (se 1 (by rfl) ⟨225209, by rfl⟩ : syracuseStep 300279 = 450419) B450419
theorem B300299 : Blo 299831 300299 := bstep (se 1 (by rfl) ⟨225224, by rfl⟩ : syracuseStep 300299 = 450449) B450449
theorem B300311 : Blo 299831 300311 := bstep (se 1 (by rfl) ⟨225233, by rfl⟩ : syracuseStep 300311 = 450467) B450467
theorem B300331 : Blo 299831 300331 := bstep (se 1 (by rfl) ⟨225248, by rfl⟩ : syracuseStep 300331 = 450497) B450497
theorem B759091 : Blo 299831 759091 := bstep (se 1 (by rfl) ⟨569318, by rfl⟩ : syracuseStep 759091 = 1138637) B1138637
theorem B857395 : Blo 299831 857395 := bstep (se 1 (by rfl) ⟨643046, by rfl⟩ : syracuseStep 857395 = 1286093) B1286093
theorem B300343 : Blo 299831 300343 := bstep (se 1 (by rfl) ⟨225257, by rfl⟩ : syracuseStep 300343 = 450515) B450515
theorem B300363 : Blo 299831 300363 := bstep (se 1 (by rfl) ⟨225272, by rfl⟩ : syracuseStep 300363 = 450545) B450545
theorem B300375 : Blo 299831 300375 := bstep (se 1 (by rfl) ⟨225281, by rfl⟩ : syracuseStep 300375 = 450563) B450563
theorem B300395 : Blo 299831 300395 := bstep (se 1 (by rfl) ⟨225296, by rfl⟩ : syracuseStep 300395 = 450593) B450593
theorem B300407 : Blo 299831 300407 := bstep (se 1 (by rfl) ⟨225305, by rfl⟩ : syracuseStep 300407 = 450611) B450611
theorem B300427 : Blo 299831 300427 := bstep (se 1 (by rfl) ⟨225320, by rfl⟩ : syracuseStep 300427 = 450641) B450641
theorem B300439 : Blo 299831 300439 := bstep (se 1 (by rfl) ⟨225329, by rfl⟩ : syracuseStep 300439 = 450659) B450659
theorem B300459 : Blo 299831 300459 := bstep (se 1 (by rfl) ⟨225344, by rfl⟩ : syracuseStep 300459 = 450689) B450689
theorem B3478963 : Blo 299831 3478963 := bstep (se 1 (by rfl) ⟨2609222, by rfl⟩ : syracuseStep 3478963 = 5218445) B5218445
theorem B300471 : Blo 299831 300471 := bstep (se 1 (by rfl) ⟨225353, by rfl⟩ : syracuseStep 300471 = 450707) B450707
theorem B759233 : Blo 299831 759233 := bstep (se 2 (by rfl) ⟨284712, by rfl⟩ : syracuseStep 759233 = 569425) B569425
theorem B300491 : Blo 299831 300491 := bstep (se 1 (by rfl) ⟨225368, by rfl⟩ : syracuseStep 300491 = 450737) B450737
theorem B1381835 : Blo 299831 1381835 := bstep (se 1 (by rfl) ⟨1036376, by rfl⟩ : syracuseStep 1381835 = 2072753) B2072753
theorem B431563 : Blo 299831 431563 := bstep (se 1 (by rfl) ⟨323672, by rfl⟩ : syracuseStep 431563 = 647345) B647345
theorem B300503 : Blo 299831 300503 := bstep (se 1 (by rfl) ⟨225377, by rfl⟩ : syracuseStep 300503 = 450755) B450755
theorem B300523 : Blo 299831 300523 := bstep (se 1 (by rfl) ⟨225392, by rfl⟩ : syracuseStep 300523 = 450785) B450785
theorem B300535 : Blo 299831 300535 := bstep (se 1 (by rfl) ⟨225401, by rfl⟩ : syracuseStep 300535 = 450803) B450803
theorem B300555 : Blo 299831 300555 := bstep (se 1 (by rfl) ⟨225416, by rfl⟩ : syracuseStep 300555 = 450833) B450833
theorem B300567 : Blo 299831 300567 := bstep (se 1 (by rfl) ⟨225425, by rfl⟩ : syracuseStep 300567 = 450851) B450851
theorem B857623 : Blo 299831 857623 := bstep (se 1 (by rfl) ⟨643217, by rfl⟩ : syracuseStep 857623 = 1286435) B1286435
theorem B1021463 : Blo 299831 1021463 := bstep (se 1 (by rfl) ⟨766097, by rfl⟩ : syracuseStep 1021463 = 1532195) B1532195
theorem B300587 : Blo 299831 300587 := bstep (se 1 (by rfl) ⟨225440, by rfl⟩ : syracuseStep 300587 = 450881) B450881
theorem B300599 : Blo 299831 300599 := bstep (se 1 (by rfl) ⟨225449, by rfl⟩ : syracuseStep 300599 = 450899) B450899
theorem B300619 : Blo 299831 300619 := bstep (se 1 (by rfl) ⟨225464, by rfl⟩ : syracuseStep 300619 = 450929) B450929
theorem B300631 : Blo 299831 300631 := bstep (se 1 (by rfl) ⟨225473, by rfl⟩ : syracuseStep 300631 = 450947) B450947
theorem B300651 : Blo 299831 300651 := bstep (se 1 (by rfl) ⟨225488, by rfl⟩ : syracuseStep 300651 = 450977) B450977
theorem B300663 : Blo 299831 300663 := bstep (se 1 (by rfl) ⟨225497, by rfl⟩ : syracuseStep 300663 = 450995) B450995
theorem B300683 : Blo 299831 300683 := bstep (se 1 (by rfl) ⟨225512, by rfl⟩ : syracuseStep 300683 = 451025) B451025
theorem B300695 : Blo 299831 300695 := bstep (se 1 (by rfl) ⟨225521, by rfl⟩ : syracuseStep 300695 = 451043) B451043
theorem B300715 : Blo 299831 300715 := bstep (se 1 (by rfl) ⟨225536, by rfl⟩ : syracuseStep 300715 = 451073) B451073
theorem B300727 : Blo 299831 300727 := bstep (se 1 (by rfl) ⟨225545, by rfl⟩ : syracuseStep 300727 = 451091) B451091
theorem B300747 : Blo 299831 300747 := bstep (se 1 (by rfl) ⟨225560, by rfl⟩ : syracuseStep 300747 = 451121) B451121
theorem B300759 : Blo 299831 300759 := bstep (se 1 (by rfl) ⟨225569, by rfl⟩ : syracuseStep 300759 = 451139) B451139
theorem B300779 : Blo 299831 300779 := bstep (se 1 (by rfl) ⟨225584, by rfl⟩ : syracuseStep 300779 = 451169) B451169
theorem B300791 : Blo 299831 300791 := bstep (se 1 (by rfl) ⟨225593, by rfl⟩ : syracuseStep 300791 = 451187) B451187
theorem B300811 : Blo 299831 300811 := bstep (se 1 (by rfl) ⟨225608, by rfl⟩ : syracuseStep 300811 = 451217) B451217
theorem B300823 : Blo 299831 300823 := bstep (se 1 (by rfl) ⟨225617, by rfl⟩ : syracuseStep 300823 = 451235) B451235
theorem B300843 : Blo 299831 300843 := bstep (se 1 (by rfl) ⟨225632, by rfl⟩ : syracuseStep 300843 = 451265) B451265
theorem B1709869 : Blo 299831 1709869 := bstep (se 3 (by rfl) ⟨320600, by rfl⟩ : syracuseStep 1709869 = 641201) B641201
theorem B300855 : Blo 299831 300855 := bstep (se 1 (by rfl) ⟨225641, by rfl⟩ : syracuseStep 300855 = 451283) B451283
theorem B2561867 : Blo 299831 2561867 := bstep (se 1 (by rfl) ⟨1921400, by rfl⟩ : syracuseStep 2561867 = 3842801) B3842801
theorem B300875 : Blo 299831 300875 := bstep (se 1 (by rfl) ⟨225656, by rfl⟩ : syracuseStep 300875 = 451313) B451313
theorem B300887 : Blo 299831 300887 := bstep (se 1 (by rfl) ⟨225665, by rfl⟩ : syracuseStep 300887 = 451331) B451331
theorem B300907 : Blo 299831 300907 := bstep (se 1 (by rfl) ⟨225680, by rfl⟩ : syracuseStep 300907 = 451361) B451361
theorem B300919 : Blo 299831 300919 := bstep (se 1 (by rfl) ⟨225689, by rfl⟩ : syracuseStep 300919 = 451379) B451379
theorem B1152899 : Blo 299831 1152899 := bstep (se 1 (by rfl) ⟨864674, by rfl⟩ : syracuseStep 1152899 = 1729349) B1729349
theorem B300939 : Blo 299831 300939 := bstep (se 1 (by rfl) ⟨225704, by rfl⟩ : syracuseStep 300939 = 451409) B451409
theorem B1152913 : Blo 299831 1152913 := bstep (se 2 (by rfl) ⟨432342, by rfl⟩ : syracuseStep 1152913 = 864685) B864685
theorem B300951 : Blo 299831 300951 := bstep (se 1 (by rfl) ⟨225713, by rfl⟩ : syracuseStep 300951 = 451427) B451427
theorem B300971 : Blo 299831 300971 := bstep (se 1 (by rfl) ⟨225728, by rfl⟩ : syracuseStep 300971 = 451457) B451457
theorem B300983 : Blo 299831 300983 := bstep (se 1 (by rfl) ⟨225737, by rfl⟩ : syracuseStep 300983 = 451475) B451475
theorem B301003 : Blo 299831 301003 := bstep (se 1 (by rfl) ⟨225752, by rfl⟩ : syracuseStep 301003 = 451505) B451505
theorem B1087435 : Blo 299831 1087435 := bstep (se 1 (by rfl) ⟨815576, by rfl⟩ : syracuseStep 1087435 = 1631153) B1631153
theorem B301015 : Blo 299831 301015 := bstep (se 1 (by rfl) ⟨225761, by rfl⟩ : syracuseStep 301015 = 451523) B451523
theorem B301035 : Blo 299831 301035 := bstep (se 1 (by rfl) ⟨225776, by rfl⟩ : syracuseStep 301035 = 451553) B451553
theorem B301047 : Blo 299831 301047 := bstep (se 1 (by rfl) ⟨225785, by rfl⟩ : syracuseStep 301047 = 451571) B451571
theorem B301067 : Blo 299831 301067 := bstep (se 1 (by rfl) ⟨225800, by rfl⟩ : syracuseStep 301067 = 451601) B451601
theorem B301079 : Blo 299831 301079 := bstep (se 1 (by rfl) ⟨225809, by rfl⟩ : syracuseStep 301079 = 451619) B451619
theorem B301099 : Blo 299831 301099 := bstep (se 1 (by rfl) ⟨225824, by rfl⟩ : syracuseStep 301099 = 451649) B451649
theorem B1022003 : Blo 299831 1022003 := bstep (se 1 (by rfl) ⟨766502, by rfl⟩ : syracuseStep 1022003 = 1533005) B1533005
theorem B301111 : Blo 299831 301111 := bstep (se 1 (by rfl) ⟨225833, by rfl⟩ : syracuseStep 301111 = 451667) B451667
theorem B301131 : Blo 299831 301131 := bstep (se 1 (by rfl) ⟨225848, by rfl⟩ : syracuseStep 301131 = 451697) B451697
theorem B301143 : Blo 299831 301143 := bstep (se 1 (by rfl) ⟨225857, by rfl⟩ : syracuseStep 301143 = 451715) B451715
theorem B301163 : Blo 299831 301163 := bstep (se 1 (by rfl) ⟨225872, by rfl⟩ : syracuseStep 301163 = 451745) B451745
theorem B301175 : Blo 299831 301175 := bstep (se 1 (by rfl) ⟨225881, by rfl⟩ : syracuseStep 301175 = 451763) B451763
theorem B301195 : Blo 299831 301195 := bstep (se 1 (by rfl) ⟨225896, by rfl⟩ : syracuseStep 301195 = 451793) B451793
theorem B301207 : Blo 299831 301207 := bstep (se 1 (by rfl) ⟨225905, by rfl⟩ : syracuseStep 301207 = 451811) B451811
theorem B301227 : Blo 299831 301227 := bstep (se 1 (by rfl) ⟨225920, by rfl⟩ : syracuseStep 301227 = 451841) B451841
theorem B301239 : Blo 299831 301239 := bstep (se 1 (by rfl) ⟨225929, by rfl⟩ : syracuseStep 301239 = 451859) B451859
theorem B1153217 : Blo 299831 1153217 := bstep (se 2 (by rfl) ⟨432456, by rfl⟩ : syracuseStep 1153217 = 864913) B864913
theorem B301259 : Blo 299831 301259 := bstep (se 1 (by rfl) ⟨225944, by rfl⟩ : syracuseStep 301259 = 451889) B451889
theorem B301271 : Blo 299831 301271 := bstep (se 1 (by rfl) ⟨225953, by rfl⟩ : syracuseStep 301271 = 451907) B451907
theorem B301291 : Blo 299831 301291 := bstep (se 1 (by rfl) ⟨225968, by rfl⟩ : syracuseStep 301291 = 451937) B451937
theorem B5478641 : Blo 299831 5478641 := bstep (se 2 (by rfl) ⟨2054490, by rfl⟩ : syracuseStep 5478641 = 4108981) B4108981
theorem B301303 : Blo 299831 301303 := bstep (se 1 (by rfl) ⟨225977, by rfl⟩ : syracuseStep 301303 = 451955) B451955
theorem B301323 : Blo 299831 301323 := bstep (se 1 (by rfl) ⟨225992, by rfl⟩ : syracuseStep 301323 = 451985) B451985
theorem B301335 : Blo 299831 301335 := bstep (se 1 (by rfl) ⟨226001, by rfl⟩ : syracuseStep 301335 = 452003) B452003
theorem B301355 : Blo 299831 301355 := bstep (se 1 (by rfl) ⟨226016, by rfl⟩ : syracuseStep 301355 = 452033) B452033
theorem B301367 : Blo 299831 301367 := bstep (se 1 (by rfl) ⟨226025, by rfl⟩ : syracuseStep 301367 = 452051) B452051
theorem B1022273 : Blo 299831 1022273 := bstep (se 2 (by rfl) ⟨383352, by rfl⟩ : syracuseStep 1022273 = 766705) B766705
theorem B301387 : Blo 299831 301387 := bstep (se 1 (by rfl) ⟨226040, by rfl⟩ : syracuseStep 301387 = 452081) B452081
theorem B301399 : Blo 299831 301399 := bstep (se 1 (by rfl) ⟨226049, by rfl⟩ : syracuseStep 301399 = 452099) B452099
theorem B301419 : Blo 299831 301419 := bstep (se 1 (by rfl) ⟨226064, by rfl⟩ : syracuseStep 301419 = 452129) B452129
theorem B301431 : Blo 299831 301431 := bstep (se 1 (by rfl) ⟨226073, by rfl⟩ : syracuseStep 301431 = 452147) B452147
theorem B301451 : Blo 299831 301451 := bstep (se 1 (by rfl) ⟨226088, by rfl⟩ : syracuseStep 301451 = 452177) B452177
theorem B301463 : Blo 299831 301463 := bstep (se 1 (by rfl) ⟨226097, by rfl⟩ : syracuseStep 301463 = 452195) B452195
theorem B301483 : Blo 299831 301483 := bstep (se 1 (by rfl) ⟨226112, by rfl⟩ : syracuseStep 301483 = 452225) B452225
theorem B4004275 : Blo 299831 4004275 := bstep (se 1 (by rfl) ⟨3003206, by rfl⟩ : syracuseStep 4004275 = 6006413) B6006413
theorem B301495 : Blo 299831 301495 := bstep (se 1 (by rfl) ⟨226121, by rfl⟩ : syracuseStep 301495 = 452243) B452243
theorem B301515 : Blo 299831 301515 := bstep (se 1 (by rfl) ⟨226136, by rfl⟩ : syracuseStep 301515 = 452273) B452273
theorem B301527 : Blo 299831 301527 := bstep (se 1 (by rfl) ⟨226145, by rfl⟩ : syracuseStep 301527 = 452291) B452291
theorem B301547 : Blo 299831 301547 := bstep (se 1 (by rfl) ⟨226160, by rfl⟩ : syracuseStep 301547 = 452321) B452321
theorem B301559 : Blo 299831 301559 := bstep (se 1 (by rfl) ⟨226169, by rfl⟩ : syracuseStep 301559 = 452339) B452339
theorem B301579 : Blo 299831 301579 := bstep (se 1 (by rfl) ⟨226184, by rfl⟩ : syracuseStep 301579 = 452369) B452369
theorem B301591 : Blo 299831 301591 := bstep (se 1 (by rfl) ⟨226193, by rfl⟩ : syracuseStep 301591 = 452387) B452387
theorem B301611 : Blo 299831 301611 := bstep (se 1 (by rfl) ⟨226208, by rfl⟩ : syracuseStep 301611 = 452417) B452417
theorem B1284659 : Blo 299831 1284659 := bstep (se 1 (by rfl) ⟨963494, by rfl⟩ : syracuseStep 1284659 = 1926989) B1926989
theorem B301623 : Blo 299831 301623 := bstep (se 1 (by rfl) ⟨226217, by rfl⟩ : syracuseStep 301623 = 452435) B452435
theorem B301643 : Blo 299831 301643 := bstep (se 1 (by rfl) ⟨226232, by rfl⟩ : syracuseStep 301643 = 452465) B452465
theorem B301655 : Blo 299831 301655 := bstep (se 1 (by rfl) ⟨226241, by rfl⟩ : syracuseStep 301655 = 452483) B452483
theorem B301675 : Blo 299831 301675 := bstep (se 1 (by rfl) ⟨226256, by rfl⟩ : syracuseStep 301675 = 452513) B452513
theorem B301687 : Blo 299831 301687 := bstep (se 1 (by rfl) ⟨226265, by rfl⟩ : syracuseStep 301687 = 452531) B452531
theorem B10394243 : Blo 299831 10394243 := bstep (se 1 (by rfl) ⟨7795682, by rfl⟩ : syracuseStep 10394243 = 15591365) B15591365
theorem B301707 : Blo 299831 301707 := bstep (se 1 (by rfl) ⟨226280, by rfl⟩ : syracuseStep 301707 = 452561) B452561
theorem B301719 : Blo 299831 301719 := bstep (se 1 (by rfl) ⟨226289, by rfl⟩ : syracuseStep 301719 = 452579) B452579
theorem B301739 : Blo 299831 301739 := bstep (se 1 (by rfl) ⟨226304, by rfl⟩ : syracuseStep 301739 = 452609) B452609
theorem B760499 : Blo 299831 760499 := bstep (se 1 (by rfl) ⟨570374, by rfl⟩ : syracuseStep 760499 = 1140749) B1140749
theorem B301751 : Blo 299831 301751 := bstep (se 1 (by rfl) ⟨226313, by rfl⟩ : syracuseStep 301751 = 452627) B452627
theorem B301771 : Blo 299831 301771 := bstep (se 1 (by rfl) ⟨226328, by rfl⟩ : syracuseStep 301771 = 452657) B452657
theorem B301783 : Blo 299831 301783 := bstep (se 1 (by rfl) ⟨226337, by rfl⟩ : syracuseStep 301783 = 452675) B452675
theorem B301803 : Blo 299831 301803 := bstep (se 1 (by rfl) ⟨226352, by rfl⟩ : syracuseStep 301803 = 452705) B452705
theorem B301815 : Blo 299831 301815 := bstep (se 1 (by rfl) ⟨226361, by rfl⟩ : syracuseStep 301815 = 452723) B452723
theorem B301835 : Blo 299831 301835 := bstep (se 1 (by rfl) ⟨226376, by rfl⟩ : syracuseStep 301835 = 452753) B452753
theorem B301847 : Blo 299831 301847 := bstep (se 1 (by rfl) ⟨226385, by rfl⟩ : syracuseStep 301847 = 452771) B452771
theorem B301867 : Blo 299831 301867 := bstep (se 1 (by rfl) ⟨226400, by rfl⟩ : syracuseStep 301867 = 452801) B452801
theorem B301879 : Blo 299831 301879 := bstep (se 1 (by rfl) ⟨226409, by rfl⟩ : syracuseStep 301879 = 452819) B452819
theorem B301899 : Blo 299831 301899 := bstep (se 1 (by rfl) ⟨226424, by rfl⟩ : syracuseStep 301899 = 452849) B452849
theorem B301911 : Blo 299831 301911 := bstep (se 1 (by rfl) ⟨226433, by rfl⟩ : syracuseStep 301911 = 452867) B452867
theorem B1022813 : Blo 299831 1022813 := bstep (se 3 (by rfl) ⟨191777, by rfl⟩ : syracuseStep 1022813 = 383555) B383555
theorem B301931 : Blo 299831 301931 := bstep (se 1 (by rfl) ⟨226448, by rfl⟩ : syracuseStep 301931 = 452897) B452897
theorem B301943 : Blo 299831 301943 := bstep (se 1 (by rfl) ⟨226457, by rfl⟩ : syracuseStep 301943 = 452915) B452915
theorem B301963 : Blo 299831 301963 := bstep (se 1 (by rfl) ⟨226472, by rfl⟩ : syracuseStep 301963 = 452945) B452945
theorem B301975 : Blo 299831 301975 := bstep (se 1 (by rfl) ⟨226481, by rfl⟩ : syracuseStep 301975 = 452963) B452963
theorem B301995 : Blo 299831 301995 := bstep (se 1 (by rfl) ⟨226496, by rfl⟩ : syracuseStep 301995 = 452993) B452993
theorem B302007 : Blo 299831 302007 := bstep (se 1 (by rfl) ⟨226505, by rfl⟩ : syracuseStep 302007 = 453011) B453011
theorem B31562693 : Blo 299831 31562693 := bstep (se 4 (by rfl) ⟨2959002, by rfl⟩ : syracuseStep 31562693 = 5918005) B5918005
theorem B302027 : Blo 299831 302027 := bstep (se 1 (by rfl) ⟨226520, by rfl⟩ : syracuseStep 302027 = 453041) B453041
theorem B302039 : Blo 299831 302039 := bstep (se 1 (by rfl) ⟨226529, by rfl⟩ : syracuseStep 302039 = 453059) B453059
theorem B302059 : Blo 299831 302059 := bstep (se 1 (by rfl) ⟨226544, by rfl⟩ : syracuseStep 302059 = 453089) B453089
theorem B302071 : Blo 299831 302071 := bstep (se 1 (by rfl) ⟨226553, by rfl⟩ : syracuseStep 302071 = 453107) B453107
theorem B302091 : Blo 299831 302091 := bstep (se 1 (by rfl) ⟨226568, by rfl⟩ : syracuseStep 302091 = 453137) B453137
theorem B302103 : Blo 299831 302103 := bstep (se 1 (by rfl) ⟨226577, by rfl⟩ : syracuseStep 302103 = 453155) B453155
theorem B302123 : Blo 299831 302123 := bstep (se 1 (by rfl) ⟨226592, by rfl⟩ : syracuseStep 302123 = 453185) B453185
theorem B302135 : Blo 299831 302135 := bstep (se 1 (by rfl) ⟨226601, by rfl⟩ : syracuseStep 302135 = 453203) B453203
theorem B302155 : Blo 299831 302155 := bstep (se 1 (by rfl) ⟨226616, by rfl⟩ : syracuseStep 302155 = 453233) B453233
theorem B302167 : Blo 299831 302167 := bstep (se 1 (by rfl) ⟨226625, by rfl⟩ : syracuseStep 302167 = 453251) B453251
theorem B302187 : Blo 299831 302187 := bstep (se 1 (by rfl) ⟨226640, by rfl⟩ : syracuseStep 302187 = 453281) B453281
theorem B302199 : Blo 299831 302199 := bstep (se 1 (by rfl) ⟨226649, by rfl⟩ : syracuseStep 302199 = 453299) B453299
theorem B302219 : Blo 299831 302219 := bstep (se 1 (by rfl) ⟨226664, by rfl⟩ : syracuseStep 302219 = 453329) B453329
theorem B302231 : Blo 299831 302231 := bstep (se 1 (by rfl) ⟨226673, by rfl⟩ : syracuseStep 302231 = 453347) B453347
theorem B302251 : Blo 299831 302251 := bstep (se 1 (by rfl) ⟨226688, by rfl⟩ : syracuseStep 302251 = 453377) B453377
theorem B302263 : Blo 299831 302263 := bstep (se 1 (by rfl) ⟨226697, by rfl⟩ : syracuseStep 302263 = 453395) B453395
theorem B761035 : Blo 299831 761035 := bstep (se 1 (by rfl) ⟨570776, by rfl⟩ : syracuseStep 761035 = 1141553) B1141553
theorem B302283 : Blo 299831 302283 := bstep (se 1 (by rfl) ⟨226712, by rfl⟩ : syracuseStep 302283 = 453425) B453425
theorem B302295 : Blo 299831 302295 := bstep (se 1 (by rfl) ⟨226721, by rfl⟩ : syracuseStep 302295 = 453443) B453443
theorem B302315 : Blo 299831 302315 := bstep (se 1 (by rfl) ⟨226736, by rfl⟩ : syracuseStep 302315 = 453473) B453473
theorem B302327 : Blo 299831 302327 := bstep (se 1 (by rfl) ⟨226745, by rfl⟩ : syracuseStep 302327 = 453491) B453491
theorem B302347 : Blo 299831 302347 := bstep (se 1 (by rfl) ⟨226760, by rfl⟩ : syracuseStep 302347 = 453521) B453521
theorem B302359 : Blo 299831 302359 := bstep (se 1 (by rfl) ⟨226769, by rfl⟩ : syracuseStep 302359 = 453539) B453539
theorem B302379 : Blo 299831 302379 := bstep (se 1 (by rfl) ⟨226784, by rfl⟩ : syracuseStep 302379 = 453569) B453569
theorem B1088819 : Blo 299831 1088819 := bstep (se 1 (by rfl) ⟨816614, by rfl⟩ : syracuseStep 1088819 = 1633229) B1633229
theorem B1383731 : Blo 299831 1383731 := bstep (se 1 (by rfl) ⟨1037798, by rfl⟩ : syracuseStep 1383731 = 2075597) B2075597
theorem B302391 : Blo 299831 302391 := bstep (se 1 (by rfl) ⟨226793, by rfl⟩ : syracuseStep 302391 = 453587) B453587
theorem B302411 : Blo 299831 302411 := bstep (se 1 (by rfl) ⟨226808, by rfl⟩ : syracuseStep 302411 = 453617) B453617
theorem B302423 : Blo 299831 302423 := bstep (se 1 (by rfl) ⟨226817, by rfl⟩ : syracuseStep 302423 = 453635) B453635
theorem B761177 : Blo 299831 761177 := bstep (se 2 (by rfl) ⟨285441, by rfl⟩ : syracuseStep 761177 = 570883) B570883
theorem B859481 : Blo 299831 859481 := bstep (se 2 (by rfl) ⟨322305, by rfl⟩ : syracuseStep 859481 = 644611) B644611
theorem B302443 : Blo 299831 302443 := bstep (se 1 (by rfl) ⟨226832, by rfl⟩ : syracuseStep 302443 = 453665) B453665
theorem B302455 : Blo 299831 302455 := bstep (se 1 (by rfl) ⟨226841, by rfl⟩ : syracuseStep 302455 = 453683) B453683
theorem B302475 : Blo 299831 302475 := bstep (se 1 (by rfl) ⟨226856, by rfl⟩ : syracuseStep 302475 = 453713) B453713
theorem B302487 : Blo 299831 302487 := bstep (se 1 (by rfl) ⟨226865, by rfl⟩ : syracuseStep 302487 = 453731) B453731
theorem B302507 : Blo 299831 302507 := bstep (se 1 (by rfl) ⟨226880, by rfl⟩ : syracuseStep 302507 = 453761) B453761
theorem B1154483 : Blo 299831 1154483 := bstep (se 1 (by rfl) ⟨865862, by rfl⟩ : syracuseStep 1154483 = 1731725) B1731725
theorem B302519 : Blo 299831 302519 := bstep (se 1 (by rfl) ⟨226889, by rfl⟩ : syracuseStep 302519 = 453779) B453779
theorem B302539 : Blo 299831 302539 := bstep (se 1 (by rfl) ⟨226904, by rfl⟩ : syracuseStep 302539 = 453809) B453809
theorem B302551 : Blo 299831 302551 := bstep (se 1 (by rfl) ⟨226913, by rfl⟩ : syracuseStep 302551 = 453827) B453827
theorem B302571 : Blo 299831 302571 := bstep (se 1 (by rfl) ⟨226928, by rfl⟩ : syracuseStep 302571 = 453857) B453857
theorem B302583 : Blo 299831 302583 := bstep (se 1 (by rfl) ⟨226937, by rfl⟩ : syracuseStep 302583 = 453875) B453875
theorem B302603 : Blo 299831 302603 := bstep (se 1 (by rfl) ⟨226952, by rfl⟩ : syracuseStep 302603 = 453905) B453905
theorem B302615 : Blo 299831 302615 := bstep (se 1 (by rfl) ⟨226961, by rfl⟩ : syracuseStep 302615 = 453923) B453923
theorem B302635 : Blo 299831 302635 := bstep (se 1 (by rfl) ⟨226976, by rfl⟩ : syracuseStep 302635 = 453953) B453953
theorem B302647 : Blo 299831 302647 := bstep (se 1 (by rfl) ⟨226985, by rfl⟩ : syracuseStep 302647 = 453971) B453971
theorem B302667 : Blo 299831 302667 := bstep (se 1 (by rfl) ⟨227000, by rfl⟩ : syracuseStep 302667 = 454001) B454001
theorem B302679 : Blo 299831 302679 := bstep (se 1 (by rfl) ⟨227009, by rfl⟩ : syracuseStep 302679 = 454019) B454019
theorem B302699 : Blo 299831 302699 := bstep (se 1 (by rfl) ⟨227024, by rfl⟩ : syracuseStep 302699 = 454049) B454049
theorem B302711 : Blo 299831 302711 := bstep (se 1 (by rfl) ⟨227033, by rfl⟩ : syracuseStep 302711 = 454067) B454067
theorem B302731 : Blo 299831 302731 := bstep (se 1 (by rfl) ⟨227048, by rfl⟩ : syracuseStep 302731 = 454097) B454097
theorem B302743 : Blo 299831 302743 := bstep (se 1 (by rfl) ⟨227057, by rfl⟩ : syracuseStep 302743 = 454115) B454115
theorem B302763 : Blo 299831 302763 := bstep (se 1 (by rfl) ⟨227072, by rfl⟩ : syracuseStep 302763 = 454145) B454145
theorem B302775 : Blo 299831 302775 := bstep (se 1 (by rfl) ⟨227081, by rfl⟩ : syracuseStep 302775 = 454163) B454163
theorem B302795 : Blo 299831 302795 := bstep (se 1 (by rfl) ⟨227096, by rfl⟩ : syracuseStep 302795 = 454193) B454193
theorem B302807 : Blo 299831 302807 := bstep (se 1 (by rfl) ⟨227105, by rfl⟩ : syracuseStep 302807 = 454211) B454211
theorem B302827 : Blo 299831 302827 := bstep (se 1 (by rfl) ⟨227120, by rfl⟩ : syracuseStep 302827 = 454241) B454241
theorem B302839 : Blo 299831 302839 := bstep (se 1 (by rfl) ⟨227129, by rfl⟩ : syracuseStep 302839 = 454259) B454259
theorem B302859 : Blo 299831 302859 := bstep (se 1 (by rfl) ⟨227144, by rfl⟩ : syracuseStep 302859 = 454289) B454289
theorem B302871 : Blo 299831 302871 := bstep (se 1 (by rfl) ⟨227153, by rfl⟩ : syracuseStep 302871 = 454307) B454307
theorem B302891 : Blo 299831 302891 := bstep (se 1 (by rfl) ⟨227168, by rfl⟩ : syracuseStep 302891 = 454337) B454337
theorem B302903 : Blo 299831 302903 := bstep (se 1 (by rfl) ⟨227177, by rfl⟩ : syracuseStep 302903 = 454355) B454355
theorem B5480257 : Blo 299831 5480257 := bstep (se 2 (by rfl) ⟨2055096, by rfl⟩ : syracuseStep 5480257 = 4110193) B4110193
theorem B302923 : Blo 299831 302923 := bstep (se 1 (by rfl) ⟨227192, by rfl⟩ : syracuseStep 302923 = 454385) B454385
theorem B302935 : Blo 299831 302935 := bstep (se 1 (by rfl) ⟨227201, by rfl⟩ : syracuseStep 302935 = 454403) B454403
theorem B302955 : Blo 299831 302955 := bstep (se 1 (by rfl) ⟨227216, by rfl⟩ : syracuseStep 302955 = 454433) B454433
theorem B302967 : Blo 299831 302967 := bstep (se 1 (by rfl) ⟨227225, by rfl⟩ : syracuseStep 302967 = 454451) B454451
theorem B302987 : Blo 299831 302987 := bstep (se 1 (by rfl) ⟨227240, by rfl⟩ : syracuseStep 302987 = 454481) B454481
theorem B302999 : Blo 299831 302999 := bstep (se 1 (by rfl) ⟨227249, by rfl⟩ : syracuseStep 302999 = 454499) B454499
theorem B303019 : Blo 299831 303019 := bstep (se 1 (by rfl) ⟨227264, by rfl⟩ : syracuseStep 303019 = 454529) B454529
theorem B303031 : Blo 299831 303031 := bstep (se 1 (by rfl) ⟨227273, by rfl⟩ : syracuseStep 303031 = 454547) B454547
theorem B303051 : Blo 299831 303051 := bstep (se 1 (by rfl) ⟨227288, by rfl⟩ : syracuseStep 303051 = 454577) B454577
theorem B1023947 : Blo 299831 1023947 := bstep (se 1 (by rfl) ⟨767960, by rfl⟩ : syracuseStep 1023947 = 1535921) B1535921
theorem B303063 : Blo 299831 303063 := bstep (se 1 (by rfl) ⟨227297, by rfl⟩ : syracuseStep 303063 = 454595) B454595
theorem B303083 : Blo 299831 303083 := bstep (se 1 (by rfl) ⟨227312, by rfl⟩ : syracuseStep 303083 = 454625) B454625
theorem B303095 : Blo 299831 303095 := bstep (se 1 (by rfl) ⟨227321, by rfl⟩ : syracuseStep 303095 = 454643) B454643
theorem B303115 : Blo 299831 303115 := bstep (se 1 (by rfl) ⟨227336, by rfl⟩ : syracuseStep 303115 = 454673) B454673
theorem B303127 : Blo 299831 303127 := bstep (se 1 (by rfl) ⟨227345, by rfl⟩ : syracuseStep 303127 = 454691) B454691
theorem B303147 : Blo 299831 303147 := bstep (se 1 (by rfl) ⟨227360, by rfl⟩ : syracuseStep 303147 = 454721) B454721
theorem B303159 : Blo 299831 303159 := bstep (se 1 (by rfl) ⟨227369, by rfl⟩ : syracuseStep 303159 = 454739) B454739
theorem B303179 : Blo 299831 303179 := bstep (se 1 (by rfl) ⟨227384, by rfl⟩ : syracuseStep 303179 = 454769) B454769
theorem B303191 : Blo 299831 303191 := bstep (se 1 (by rfl) ⟨227393, by rfl⟩ : syracuseStep 303191 = 454787) B454787
theorem B303211 : Blo 299831 303211 := bstep (se 1 (by rfl) ⟨227408, by rfl⟩ : syracuseStep 303211 = 454817) B454817
theorem B303223 : Blo 299831 303223 := bstep (se 1 (by rfl) ⟨227417, by rfl⟩ : syracuseStep 303223 = 454835) B454835
theorem B303243 : Blo 299831 303243 := bstep (se 1 (by rfl) ⟨227432, by rfl⟩ : syracuseStep 303243 = 454865) B454865
theorem B762007 : Blo 299831 762007 := bstep (se 1 (by rfl) ⟨571505, by rfl⟩ : syracuseStep 762007 = 1143011) B1143011
theorem B860311 : Blo 299831 860311 := bstep (se 1 (by rfl) ⟨645233, by rfl⟩ : syracuseStep 860311 = 1290467) B1290467
theorem B303255 : Blo 299831 303255 := bstep (se 1 (by rfl) ⟨227441, by rfl⟩ : syracuseStep 303255 = 454883) B454883
theorem B303275 : Blo 299831 303275 := bstep (se 1 (by rfl) ⟨227456, by rfl⟩ : syracuseStep 303275 = 454913) B454913
theorem B1450163 : Blo 299831 1450163 := bstep (se 1 (by rfl) ⟨1087622, by rfl⟩ : syracuseStep 1450163 = 2175245) B2175245
theorem B303287 : Blo 299831 303287 := bstep (se 1 (by rfl) ⟨227465, by rfl⟩ : syracuseStep 303287 = 454931) B454931
theorem B303307 : Blo 299831 303307 := bstep (se 1 (by rfl) ⟨227480, by rfl⟩ : syracuseStep 303307 = 454961) B454961
theorem B303319 : Blo 299831 303319 := bstep (se 1 (by rfl) ⟨227489, by rfl⟩ : syracuseStep 303319 = 454979) B454979
theorem B1024217 : Blo 299831 1024217 := bstep (se 2 (by rfl) ⟨384081, by rfl⟩ : syracuseStep 1024217 = 768163) B768163
theorem B303339 : Blo 299831 303339 := bstep (se 1 (by rfl) ⟨227504, by rfl⟩ : syracuseStep 303339 = 455009) B455009
theorem B303351 : Blo 299831 303351 := bstep (se 1 (by rfl) ⟨227513, by rfl⟩ : syracuseStep 303351 = 455027) B455027
theorem B303371 : Blo 299831 303371 := bstep (se 1 (by rfl) ⟨227528, by rfl⟩ : syracuseStep 303371 = 455057) B455057
theorem B303383 : Blo 299831 303383 := bstep (se 1 (by rfl) ⟨227537, by rfl⟩ : syracuseStep 303383 = 455075) B455075
theorem B303403 : Blo 299831 303403 := bstep (se 1 (by rfl) ⟨227552, by rfl⟩ : syracuseStep 303403 = 455105) B455105
theorem B303415 : Blo 299831 303415 := bstep (se 1 (by rfl) ⟨227561, by rfl⟩ : syracuseStep 303415 = 455123) B455123
theorem B1450315 : Blo 299831 1450315 := bstep (se 1 (by rfl) ⟨1087736, by rfl⟩ : syracuseStep 1450315 = 2175473) B2175473
theorem B303435 : Blo 299831 303435 := bstep (se 1 (by rfl) ⟨227576, by rfl⟩ : syracuseStep 303435 = 455153) B455153
theorem B303447 : Blo 299831 303447 := bstep (se 1 (by rfl) ⟨227585, by rfl⟩ : syracuseStep 303447 = 455171) B455171
theorem B303467 : Blo 299831 303467 := bstep (se 1 (by rfl) ⟨227600, by rfl⟩ : syracuseStep 303467 = 455201) B455201
theorem B303479 : Blo 299831 303479 := bstep (se 1 (by rfl) ⟨227609, by rfl⟩ : syracuseStep 303479 = 455219) B455219
theorem B303499 : Blo 299831 303499 := bstep (se 1 (by rfl) ⟨227624, by rfl⟩ : syracuseStep 303499 = 455249) B455249
theorem B1450391 : Blo 299831 1450391 := bstep (se 1 (by rfl) ⟨1087793, by rfl⟩ : syracuseStep 1450391 = 2175587) B2175587
theorem B303511 : Blo 299831 303511 := bstep (se 1 (by rfl) ⟨227633, by rfl⟩ : syracuseStep 303511 = 455267) B455267
theorem B303531 : Blo 299831 303531 := bstep (se 1 (by rfl) ⟨227648, by rfl⟩ : syracuseStep 303531 = 455297) B455297
theorem B2564531 : Blo 299831 2564531 := bstep (se 1 (by rfl) ⟨1923398, by rfl⟩ : syracuseStep 2564531 = 3846797) B3846797
theorem B303543 : Blo 299831 303543 := bstep (se 1 (by rfl) ⟨227657, by rfl⟩ : syracuseStep 303543 = 455315) B455315
theorem B303563 : Blo 299831 303563 := bstep (se 1 (by rfl) ⟨227672, by rfl⟩ : syracuseStep 303563 = 455345) B455345
theorem B303575 : Blo 299831 303575 := bstep (se 1 (by rfl) ⟨227681, by rfl⟩ : syracuseStep 303575 = 455363) B455363
theorem B303595 : Blo 299831 303595 := bstep (se 1 (by rfl) ⟨227696, by rfl⟩ : syracuseStep 303595 = 455393) B455393
theorem B303607 : Blo 299831 303607 := bstep (se 1 (by rfl) ⟨227705, by rfl⟩ : syracuseStep 303607 = 455411) B455411
theorem B303627 : Blo 299831 303627 := bstep (se 1 (by rfl) ⟨227720, by rfl⟩ : syracuseStep 303627 = 455441) B455441
theorem B303639 : Blo 299831 303639 := bstep (se 1 (by rfl) ⟨227729, by rfl⟩ : syracuseStep 303639 = 455459) B455459
theorem B303659 : Blo 299831 303659 := bstep (se 1 (by rfl) ⟨227744, by rfl⟩ : syracuseStep 303659 = 455489) B455489
theorem B303671 : Blo 299831 303671 := bstep (se 1 (by rfl) ⟨227753, by rfl⟩ : syracuseStep 303671 = 455507) B455507
theorem B762443 : Blo 299831 762443 := bstep (se 1 (by rfl) ⟨571832, by rfl⟩ : syracuseStep 762443 = 1143665) B1143665
theorem B303691 : Blo 299831 303691 := bstep (se 1 (by rfl) ⟨227768, by rfl⟩ : syracuseStep 303691 = 455537) B455537
theorem B303703 : Blo 299831 303703 := bstep (se 1 (by rfl) ⟨227777, by rfl⟩ : syracuseStep 303703 = 455555) B455555
theorem B303723 : Blo 299831 303723 := bstep (se 1 (by rfl) ⟨227792, by rfl⟩ : syracuseStep 303723 = 455585) B455585
theorem B303735 : Blo 299831 303735 := bstep (se 1 (by rfl) ⟨227801, by rfl⟩ : syracuseStep 303735 = 455603) B455603
theorem B303755 : Blo 299831 303755 := bstep (se 1 (by rfl) ⟨227816, by rfl⟩ : syracuseStep 303755 = 455633) B455633
theorem B303767 : Blo 299831 303767 := bstep (se 1 (by rfl) ⟨227825, by rfl⟩ : syracuseStep 303767 = 455651) B455651
theorem B303787 : Blo 299831 303787 := bstep (se 1 (by rfl) ⟨227840, by rfl⟩ : syracuseStep 303787 = 455681) B455681
theorem B303799 : Blo 299831 303799 := bstep (se 1 (by rfl) ⟨227849, by rfl⟩ : syracuseStep 303799 = 455699) B455699
theorem B303819 : Blo 299831 303819 := bstep (se 1 (by rfl) ⟨227864, by rfl⟩ : syracuseStep 303819 = 455729) B455729
theorem B303831 : Blo 299831 303831 := bstep (se 1 (by rfl) ⟨227873, by rfl⟩ : syracuseStep 303831 = 455747) B455747
theorem B6497009 : Blo 299831 6497009 := bstep (se 2 (by rfl) ⟨2436378, by rfl⟩ : syracuseStep 6497009 = 4872757) B4872757
theorem B1024919 : Blo 299831 1024919 := bstep (se 1 (by rfl) ⟨768689, by rfl⟩ : syracuseStep 1024919 = 1537379) B1537379
theorem B762817 : Blo 299831 762817 := bstep (se 2 (by rfl) ⟨286056, by rfl⟩ : syracuseStep 762817 = 572113) B572113
theorem B861131 : Blo 299831 861131 := bstep (se 1 (by rfl) ⟨645848, by rfl⟩ : syracuseStep 861131 = 1291697) B1291697
theorem B2303153 : Blo 299831 2303153 := bstep (se 2 (by rfl) ⟨863682, by rfl⟩ : syracuseStep 2303153 = 1727365) B1727365
theorem B1746137 : Blo 299831 1746137 := bstep (se 2 (by rfl) ⟨654801, by rfl⟩ : syracuseStep 1746137 = 1309603) B1309603
theorem B2565593 : Blo 299831 2565593 := bstep (se 2 (by rfl) ⟨962097, by rfl⟩ : syracuseStep 2565593 = 1924195) B1924195
theorem B337387 : Blo 299831 337387 := bstep (se 1 (by rfl) ⟨253040, by rfl⟩ : syracuseStep 337387 = 506081) B506081
theorem B763415 : Blo 299831 763415 := bstep (se 1 (by rfl) ⟨572561, by rfl⟩ : syracuseStep 763415 = 1145123) B1145123
theorem B337495 : Blo 299831 337495 := bstep (se 1 (by rfl) ⟨253121, by rfl⟩ : syracuseStep 337495 = 506243) B506243
theorem B2303639 : Blo 299831 2303639 := bstep (se 1 (by rfl) ⟨1727729, by rfl⟩ : syracuseStep 2303639 = 3455459) B3455459
theorem B337675 : Blo 299831 337675 := bstep (se 1 (by rfl) ⟨253256, by rfl⟩ : syracuseStep 337675 = 506513) B506513
theorem B337783 : Blo 299831 337783 := bstep (se 1 (by rfl) ⟨253337, by rfl⟩ : syracuseStep 337783 = 506675) B506675
theorem B337963 : Blo 299831 337963 := bstep (se 1 (by rfl) ⟨253472, by rfl⟩ : syracuseStep 337963 = 506945) B506945
theorem B338071 : Blo 299831 338071 := bstep (se 1 (by rfl) ⟨253553, by rfl⟩ : syracuseStep 338071 = 507107) B507107
theorem B3451085 : Blo 299831 3451085 := bstep (se 3 (by rfl) ⟨647078, by rfl⟩ : syracuseStep 3451085 = 1294157) B1294157
theorem B2337041 : Blo 299831 2337041 := bstep (se 2 (by rfl) ⟨876390, by rfl⟩ : syracuseStep 2337041 = 1752781) B1752781
theorem B764225 : Blo 299831 764225 := bstep (se 2 (by rfl) ⟨286584, by rfl⟩ : syracuseStep 764225 = 573169) B573169
theorem B338251 : Blo 299831 338251 := bstep (se 1 (by rfl) ⟨253688, by rfl⟩ : syracuseStep 338251 = 507377) B507377
theorem B338359 : Blo 299831 338359 := bstep (se 1 (by rfl) ⟨253769, by rfl⟩ : syracuseStep 338359 = 507539) B507539
theorem B1157597 : Blo 299831 1157597 := bstep (se 3 (by rfl) ⟨217049, by rfl⟩ : syracuseStep 1157597 = 434099) B434099
theorem B338539 : Blo 299831 338539 := bstep (se 1 (by rfl) ⟨253904, by rfl⟩ : syracuseStep 338539 = 507809) B507809
theorem B338647 : Blo 299831 338647 := bstep (se 1 (by rfl) ⟨253985, by rfl⟩ : syracuseStep 338647 = 507971) B507971
theorem B1288963 : Blo 299831 1288963 := bstep (se 1 (by rfl) ⟨966722, by rfl⟩ : syracuseStep 1288963 = 1933445) B1933445
theorem B305975 : Blo 299831 305975 := bstep (se 1 (by rfl) ⟨229481, by rfl⟩ : syracuseStep 305975 = 458963) B458963
theorem B764761 : Blo 299831 764761 := bstep (se 2 (by rfl) ⟨286785, by rfl⟩ : syracuseStep 764761 = 573571) B573571
theorem B4107125 : Blo 299831 4107125 := bstep (se 5 (by rfl) ⟨192521, by rfl⟩ : syracuseStep 4107125 = 385043) B385043
theorem B338827 : Blo 299831 338827 := bstep (se 1 (by rfl) ⟨254120, by rfl⟩ : syracuseStep 338827 = 508241) B508241
theorem B961483 : Blo 299831 961483 := bstep (se 1 (by rfl) ⟨721112, by rfl⟩ : syracuseStep 961483 = 1442225) B1442225
theorem B338935 : Blo 299831 338935 := bstep (se 1 (by rfl) ⟨254201, by rfl⟩ : syracuseStep 338935 = 508403) B508403
theorem B339115 : Blo 299831 339115 := bstep (se 1 (by rfl) ⟨254336, by rfl⟩ : syracuseStep 339115 = 508673) B508673
theorem B8694965 : Blo 299831 8694965 := bstep (se 5 (by rfl) ⟨407576, by rfl⟩ : syracuseStep 8694965 = 815153) B815153
theorem B6991109 : Blo 299831 6991109 := bstep (se 4 (by rfl) ⟨655416, by rfl⟩ : syracuseStep 6991109 = 1310833) B1310833
theorem B339223 : Blo 299831 339223 := bstep (se 1 (by rfl) ⟨254417, by rfl⟩ : syracuseStep 339223 = 508835) B508835
theorem B863581 : Blo 299831 863581 := bstep (se 3 (by rfl) ⟨161921, by rfl⟩ : syracuseStep 863581 = 323843) B323843
theorem B339403 : Blo 299831 339403 := bstep (se 1 (by rfl) ⟨254552, by rfl⟩ : syracuseStep 339403 = 509105) B509105
theorem B1945133 : Blo 299831 1945133 := bstep (se 3 (by rfl) ⟨364712, by rfl⟩ : syracuseStep 1945133 = 729425) B729425
theorem B339511 : Blo 299831 339511 := bstep (se 1 (by rfl) ⟨254633, by rfl⟩ : syracuseStep 339511 = 509267) B509267
theorem B1519235 : Blo 299831 1519235 := bstep (se 1 (by rfl) ⟨1139426, by rfl⟩ : syracuseStep 1519235 = 2278853) B2278853
theorem B339691 : Blo 299831 339691 := bstep (se 1 (by rfl) ⟨254768, by rfl⟩ : syracuseStep 339691 = 509537) B509537
theorem B339799 : Blo 299831 339799 := bstep (se 1 (by rfl) ⟨254849, by rfl⟩ : syracuseStep 339799 = 509699) B509699
theorem B765875 : Blo 299831 765875 := bstep (se 1 (by rfl) ⟨574406, by rfl⟩ : syracuseStep 765875 = 1148813) B1148813
theorem B569281 : Blo 299831 569281 := bstep (se 2 (by rfl) ⟨213480, by rfl⟩ : syracuseStep 569281 = 426961) B426961
theorem B339979 : Blo 299831 339979 := bstep (se 1 (by rfl) ⟨254984, by rfl⟩ : syracuseStep 339979 = 509969) B509969
theorem B340087 : Blo 299831 340087 := bstep (se 1 (by rfl) ⟨255065, by rfl⟩ : syracuseStep 340087 = 510131) B510131
theorem B766169 : Blo 299831 766169 := bstep (se 2 (by rfl) ⟨287313, by rfl⟩ : syracuseStep 766169 = 574627) B574627
theorem B340267 : Blo 299831 340267 := bstep (se 1 (by rfl) ⟨255200, by rfl⟩ : syracuseStep 340267 = 510401) B510401
theorem B405847 : Blo 299831 405847 := bstep (se 1 (by rfl) ⟨304385, by rfl⟩ : syracuseStep 405847 = 608771) B608771
theorem B569729 : Blo 299831 569729 := bstep (se 2 (by rfl) ⟨213648, by rfl⟩ : syracuseStep 569729 = 427297) B427297
theorem B340375 : Blo 299831 340375 := bstep (se 1 (by rfl) ⟨255281, by rfl⟩ : syracuseStep 340375 = 510563) B510563
theorem B405913 : Blo 299831 405913 := bstep (se 2 (by rfl) ⟨152217, by rfl⟩ : syracuseStep 405913 = 304435) B304435
theorem B1716659 : Blo 299831 1716659 := bstep (se 1 (by rfl) ⟨1287494, by rfl⟩ : syracuseStep 1716659 = 2574989) B2574989
theorem B1290775 : Blo 299831 1290775 := bstep (se 1 (by rfl) ⟨968081, by rfl⟩ : syracuseStep 1290775 = 1936163) B1936163
theorem B1094195 : Blo 299831 1094195 := bstep (se 1 (by rfl) ⟨820646, by rfl⟩ : syracuseStep 1094195 = 1641293) B1641293
theorem B340555 : Blo 299831 340555 := bstep (se 1 (by rfl) ⟨255416, by rfl⟩ : syracuseStep 340555 = 510833) B510833
theorem B963161 : Blo 299831 963161 := bstep (se 2 (by rfl) ⟨361185, by rfl⟩ : syracuseStep 963161 = 722371) B722371
theorem B864857 : Blo 299831 864857 := bstep (se 2 (by rfl) ⟨324321, by rfl⟩ : syracuseStep 864857 = 648643) B648643
theorem B340663 : Blo 299831 340663 := bstep (se 1 (by rfl) ⟨255497, by rfl⟩ : syracuseStep 340663 = 510995) B510995
theorem B570071 : Blo 299831 570071 := bstep (se 1 (by rfl) ⟨427553, by rfl⟩ : syracuseStep 570071 = 855107) B855107
theorem B1159901 : Blo 299831 1159901 := bstep (se 3 (by rfl) ⟨217481, by rfl⟩ : syracuseStep 1159901 = 434963) B434963
theorem B4371245 : Blo 299831 4371245 := bstep (se 3 (by rfl) ⟨819608, by rfl⟩ : syracuseStep 4371245 = 1639217) B1639217
theorem B1651549 : Blo 299831 1651549 := bstep (se 3 (by rfl) ⟨309665, by rfl⟩ : syracuseStep 1651549 = 619331) B619331
theorem B340843 : Blo 299831 340843 := bstep (se 1 (by rfl) ⟨255632, by rfl⟩ : syracuseStep 340843 = 511265) B511265
theorem B340951 : Blo 299831 340951 := bstep (se 1 (by rfl) ⟨255713, by rfl⟩ : syracuseStep 340951 = 511427) B511427
theorem B2634713 : Blo 299831 2634713 := bstep (se 2 (by rfl) ⟨988017, by rfl⟩ : syracuseStep 2634713 = 1976035) B1976035
theorem B341131 : Blo 299831 341131 := bstep (se 1 (by rfl) ⟨255848, by rfl⟩ : syracuseStep 341131 = 511697) B511697
theorem B1291409 : Blo 299831 1291409 := bstep (se 2 (by rfl) ⟨484278, by rfl⟩ : syracuseStep 1291409 = 968557) B968557
theorem B2766001 : Blo 299831 2766001 := bstep (se 2 (by rfl) ⟨1037250, by rfl⟩ : syracuseStep 2766001 = 2074501) B2074501
theorem B341239 : Blo 299831 341239 := bstep (se 1 (by rfl) ⟨255929, by rfl⟩ : syracuseStep 341239 = 511859) B511859
theorem B570739 : Blo 299831 570739 := bstep (se 1 (by rfl) ⟨428054, by rfl⟩ : syracuseStep 570739 = 856109) B856109
theorem B341419 : Blo 299831 341419 := bstep (se 1 (by rfl) ⟨256064, by rfl⟩ : syracuseStep 341419 = 512129) B512129
theorem B1553843 : Blo 299831 1553843 := bstep (se 1 (by rfl) ⟨1165382, by rfl⟩ : syracuseStep 1553843 = 2330765) B2330765
theorem B964057 : Blo 299831 964057 := bstep (se 2 (by rfl) ⟨361521, by rfl⟩ : syracuseStep 964057 = 723043) B723043
theorem B341527 : Blo 299831 341527 := bstep (se 1 (by rfl) ⟨256145, by rfl⟩ : syracuseStep 341527 = 512291) B512291
theorem B11941507 : Blo 299831 11941507 := bstep (se 1 (by rfl) ⟨8956130, by rfl⟩ : syracuseStep 11941507 = 17912261) B17912261
theorem B341707 : Blo 299831 341707 := bstep (se 1 (by rfl) ⟨256280, by rfl⟩ : syracuseStep 341707 = 512561) B512561
theorem B571187 : Blo 299831 571187 := bstep (se 1 (by rfl) ⟨428390, by rfl⟩ : syracuseStep 571187 = 856781) B856781
theorem B1292107 : Blo 299831 1292107 := bstep (se 1 (by rfl) ⟨969080, by rfl⟩ : syracuseStep 1292107 = 1938161) B1938161
theorem B767819 : Blo 299831 767819 := bstep (se 1 (by rfl) ⟨575864, by rfl⟩ : syracuseStep 767819 = 1151729) B1151729
theorem B571225 : Blo 299831 571225 := bstep (se 2 (by rfl) ⟨214209, by rfl⟩ : syracuseStep 571225 = 428419) B428419
theorem B1718117 : Blo 299831 1718117 := bstep (se 4 (by rfl) ⟨161073, by rfl⟩ : syracuseStep 1718117 = 322147) B322147
theorem B964673 : Blo 299831 964673 := bstep (se 2 (by rfl) ⟨361752, by rfl⟩ : syracuseStep 964673 = 723505) B723505
theorem B1292381 : Blo 299831 1292381 := bstep (se 3 (by rfl) ⟨242321, by rfl⟩ : syracuseStep 1292381 = 484643) B484643
theorem B964801 : Blo 299831 964801 := bstep (se 2 (by rfl) ⟨361800, by rfl⟩ : syracuseStep 964801 = 723601) B723601
theorem B506135 : Blo 299831 506135 := bstep (se 1 (by rfl) ⟨379601, by rfl⟩ : syracuseStep 506135 = 759203) B759203
theorem B571673 : Blo 299831 571673 := bstep (se 2 (by rfl) ⟨214377, by rfl⟩ : syracuseStep 571673 = 428755) B428755
theorem B506263 : Blo 299831 506263 := bstep (se 1 (by rfl) ⟨379697, by rfl⟩ : syracuseStep 506263 = 759395) B759395
theorem B1292723 : Blo 299831 1292723 := bstep (se 1 (by rfl) ⟨969542, by rfl⟩ : syracuseStep 1292723 = 1939085) B1939085
theorem B932417 : Blo 299831 932417 := bstep (se 2 (by rfl) ⟨349656, by rfl⟩ : syracuseStep 932417 = 699313) B699313
theorem B768791 : Blo 299831 768791 := bstep (se 1 (by rfl) ⟨576593, by rfl⟩ : syracuseStep 768791 = 1153187) B1153187
theorem B572417 : Blo 299831 572417 := bstep (se 2 (by rfl) ⟨214656, by rfl⟩ : syracuseStep 572417 = 429313) B429313
theorem B506891 : Blo 299831 506891 := bstep (se 1 (by rfl) ⟨380168, by rfl⟩ : syracuseStep 506891 = 760337) B760337
theorem B2571365 : Blo 299831 2571365 := bstep (se 4 (by rfl) ⟨241065, by rfl⟩ : syracuseStep 2571365 = 482131) B482131
theorem B507019 : Blo 299831 507019 := bstep (se 1 (by rfl) ⟨380264, by rfl⟩ : syracuseStep 507019 = 760529) B760529
theorem B3423383 : Blo 299831 3423383 := bstep (se 1 (by rfl) ⟨2567537, by rfl⟩ : syracuseStep 3423383 = 5135075) B5135075
theorem B572683 : Blo 299831 572683 := bstep (se 1 (by rfl) ⟨429512, by rfl⟩ : syracuseStep 572683 = 859025) B859025
theorem B1522961 : Blo 299831 1522961 := bstep (se 2 (by rfl) ⟨571110, by rfl⟩ : syracuseStep 1522961 = 1142221) B1142221
theorem B507161 : Blo 299831 507161 := bstep (se 2 (by rfl) ⟨190185, by rfl⟩ : syracuseStep 507161 = 380371) B380371
theorem B1555777 : Blo 299831 1555777 := bstep (se 2 (by rfl) ⟨583416, by rfl⟩ : syracuseStep 1555777 = 1166833) B1166833
theorem B507289 : Blo 299831 507289 := bstep (se 2 (by rfl) ⟨190233, by rfl⟩ : syracuseStep 507289 = 380467) B380467
theorem B1523123 : Blo 299831 1523123 := bstep (se 1 (by rfl) ⟨1142342, by rfl⟩ : syracuseStep 1523123 = 2284685) B2284685
theorem B3259921 : Blo 299831 3259921 := bstep (se 2 (by rfl) ⟨1222470, by rfl⟩ : syracuseStep 3259921 = 2444941) B2444941
theorem B2276909 : Blo 299831 2276909 := bstep (se 3 (by rfl) ⟨426920, by rfl⟩ : syracuseStep 2276909 = 853841) B853841
theorem B409177 : Blo 299831 409177 := bstep (se 2 (by rfl) ⟨153441, by rfl⟩ : syracuseStep 409177 = 306883) B306883
theorem B573131 : Blo 299831 573131 := bstep (se 1 (by rfl) ⟨429848, by rfl⟩ : syracuseStep 573131 = 859697) B859697
theorem B409303 : Blo 299831 409303 := bstep (se 1 (by rfl) ⟨306977, by rfl⟩ : syracuseStep 409303 = 613955) B613955
theorem B573313 : Blo 299831 573313 := bstep (se 2 (by rfl) ⟨214992, by rfl⟩ : syracuseStep 573313 = 429985) B429985
theorem B507863 : Blo 299831 507863 := bstep (se 1 (by rfl) ⟨380897, by rfl⟩ : syracuseStep 507863 = 761795) B761795
theorem B1032257 : Blo 299831 1032257 := bstep (se 2 (by rfl) ⟨387096, by rfl⟩ : syracuseStep 1032257 = 774193) B774193
theorem B507991 : Blo 299831 507991 := bstep (se 1 (by rfl) ⟨380993, by rfl⟩ : syracuseStep 507991 = 761987) B761987
theorem B573655 : Blo 299831 573655 := bstep (se 1 (by rfl) ⟨430241, by rfl⟩ : syracuseStep 573655 = 860483) B860483
theorem B573875 : Blo 299831 573875 := bstep (se 1 (by rfl) ⟨430406, by rfl⟩ : syracuseStep 573875 = 860813) B860813
theorem B967133 : Blo 299831 967133 := bstep (se 3 (by rfl) ⟨181337, by rfl⟩ : syracuseStep 967133 = 362675) B362675
theorem B2900555 : Blo 299831 2900555 := bstep (se 1 (by rfl) ⟨2175416, by rfl⟩ : syracuseStep 2900555 = 4350833) B4350833
theorem B574103 : Blo 299831 574103 := bstep (se 1 (by rfl) ⟨430577, by rfl⟩ : syracuseStep 574103 = 861155) B861155
theorem B508619 : Blo 299831 508619 := bstep (se 1 (by rfl) ⟨381464, by rfl⟩ : syracuseStep 508619 = 762929) B762929
theorem B2573005 : Blo 299831 2573005 := bstep (se 3 (by rfl) ⟨482438, by rfl⟩ : syracuseStep 2573005 = 964877) B964877
theorem B1295149 : Blo 299831 1295149 := bstep (se 3 (by rfl) ⟨242840, by rfl⟩ : syracuseStep 1295149 = 485681) B485681
theorem B541505 : Blo 299831 541505 := bstep (se 2 (by rfl) ⟨203064, by rfl⟩ : syracuseStep 541505 = 406129) B406129
theorem B2442059 : Blo 299831 2442059 := bstep (se 1 (by rfl) ⟨1831544, by rfl⟩ : syracuseStep 2442059 = 3663089) B3663089
theorem B508747 : Blo 299831 508747 := bstep (se 1 (by rfl) ⟨381560, by rfl⟩ : syracuseStep 508747 = 763121) B763121
theorem B1622915 : Blo 299831 1622915 := bstep (se 1 (by rfl) ⟨1217186, by rfl⟩ : syracuseStep 1622915 = 2434373) B2434373
theorem B574361 : Blo 299831 574361 := bstep (se 2 (by rfl) ⟨215385, by rfl⟩ : syracuseStep 574361 = 430771) B430771
theorem B508889 : Blo 299831 508889 := bstep (se 2 (by rfl) ⟨190833, by rfl⟩ : syracuseStep 508889 = 381667) B381667
theorem B836573 : Blo 299831 836573 := bstep (se 3 (by rfl) ⟨156857, by rfl⟩ : syracuseStep 836573 = 313715) B313715
theorem B1557521 : Blo 299831 1557521 := bstep (se 2 (by rfl) ⟨584070, by rfl⟩ : syracuseStep 1557521 = 1168141) B1168141
theorem B509017 : Blo 299831 509017 := bstep (se 2 (by rfl) ⟨190881, by rfl⟩ : syracuseStep 509017 = 381763) B381763
theorem B574771 : Blo 299831 574771 := bstep (se 1 (by rfl) ⟨431078, by rfl⟩ : syracuseStep 574771 = 862157) B862157
theorem B1525067 : Blo 299831 1525067 := bstep (se 1 (by rfl) ⟨1143800, by rfl⟩ : syracuseStep 1525067 = 2287601) B2287601
theorem B771545 : Blo 299831 771545 := bstep (se 2 (by rfl) ⟨289329, by rfl⟩ : syracuseStep 771545 = 578659) B578659
theorem B509591 : Blo 299831 509591 := bstep (se 1 (by rfl) ⟨382193, by rfl⟩ : syracuseStep 509591 = 764387) B764387
theorem B4966069 : Blo 299831 4966069 := bstep (se 5 (by rfl) ⟨232784, by rfl⟩ : syracuseStep 4966069 = 465569) B465569
theorem B509719 : Blo 299831 509719 := bstep (se 1 (by rfl) ⟨382289, by rfl⟩ : syracuseStep 509719 = 764579) B764579
theorem B575257 : Blo 299831 575257 := bstep (se 2 (by rfl) ⟨215721, by rfl⟩ : syracuseStep 575257 = 431443) B431443
theorem B2574341 : Blo 299831 2574341 := bstep (se 4 (by rfl) ⟨241344, by rfl⟩ : syracuseStep 2574341 = 482689) B482689
theorem B2214161 : Blo 299831 2214161 := bstep (se 2 (by rfl) ⟨830310, by rfl⟩ : syracuseStep 2214161 = 1660621) B1660621
theorem B575819 : Blo 299831 575819 := bstep (se 1 (by rfl) ⟨431864, by rfl⟩ : syracuseStep 575819 = 863729) B863729
theorem B510347 : Blo 299831 510347 := bstep (se 1 (by rfl) ⟨382760, by rfl⟩ : syracuseStep 510347 = 765521) B765521
theorem B576001 : Blo 299831 576001 := bstep (se 2 (by rfl) ⟨216000, by rfl⟩ : syracuseStep 576001 = 432001) B432001
theorem B510475 : Blo 299831 510475 := bstep (se 1 (by rfl) ⟨382856, by rfl⟩ : syracuseStep 510475 = 765713) B765713
theorem B543257 : Blo 299831 543257 := bstep (se 2 (by rfl) ⟨203721, by rfl⟩ : syracuseStep 543257 = 407443) B407443
theorem B641611 : Blo 299831 641611 := bstep (se 1 (by rfl) ⟨481208, by rfl⟩ : syracuseStep 641611 = 962417) B962417
theorem B510617 : Blo 299831 510617 := bstep (se 2 (by rfl) ⟨191481, by rfl⟩ : syracuseStep 510617 = 382963) B382963
theorem B1231553 : Blo 299831 1231553 := bstep (se 2 (by rfl) ⟨461832, by rfl⟩ : syracuseStep 1231553 = 923665) B923665
theorem B19942129 : Blo 299831 19942129 := bstep (se 2 (by rfl) ⟨7478298, by rfl⟩ : syracuseStep 19942129 = 14956597) B14956597
theorem B510745 : Blo 299831 510745 := bstep (se 2 (by rfl) ⟨191529, by rfl⟩ : syracuseStep 510745 = 383059) B383059
theorem B379723 : Blo 299831 379723 := bstep (se 1 (by rfl) ⟨284792, by rfl⟩ : syracuseStep 379723 = 569585) B569585
theorem B674675 : Blo 299831 674675 := bstep (se 1 (by rfl) ⟨506006, by rfl⟩ : syracuseStep 674675 = 1012013) B1012013
theorem B674711 : Blo 299831 674711 := bstep (se 1 (by rfl) ⟨506033, by rfl⟩ : syracuseStep 674711 = 1012067) B1012067
theorem B641945 : Blo 299831 641945 := bstep (se 2 (by rfl) ⟨240729, by rfl⟩ : syracuseStep 641945 = 481459) B481459
theorem B1526849 : Blo 299831 1526849 := bstep (se 2 (by rfl) ⟨572568, by rfl⟩ : syracuseStep 1526849 = 1145137) B1145137
theorem B4901957 : Blo 299831 4901957 := bstep (se 4 (by rfl) ⟨459558, by rfl⟩ : syracuseStep 4901957 = 919117) B919117
theorem B674891 : Blo 299831 674891 := bstep (se 1 (by rfl) ⟨506168, by rfl⟩ : syracuseStep 674891 = 1012337) B1012337
theorem B379991 : Blo 299831 379991 := bstep (se 1 (by rfl) ⟨284993, by rfl⟩ : syracuseStep 379991 = 569987) B569987
theorem B674945 : Blo 299831 674945 := bstep (se 2 (by rfl) ⟨253104, by rfl⟩ : syracuseStep 674945 = 506209) B506209
theorem B1297559 : Blo 299831 1297559 := bstep (se 1 (by rfl) ⟨973169, by rfl⟩ : syracuseStep 1297559 = 1946339) B1946339
theorem B576715 : Blo 299831 576715 := bstep (se 1 (by rfl) ⟨432536, by rfl⟩ : syracuseStep 576715 = 865073) B865073
theorem B576791 : Blo 299831 576791 := bstep (se 1 (by rfl) ⟨432593, by rfl⟩ : syracuseStep 576791 = 865187) B865187
theorem B511319 : Blo 299831 511319 := bstep (se 1 (by rfl) ⟨383489, by rfl⟩ : syracuseStep 511319 = 766979) B766979
theorem B675161 : Blo 299831 675161 := bstep (se 2 (by rfl) ⟨253185, by rfl⟩ : syracuseStep 675161 = 506371) B506371
theorem B2280797 : Blo 299831 2280797 := bstep (se 3 (by rfl) ⟨427649, by rfl⟩ : syracuseStep 2280797 = 855299) B855299
theorem B675251 : Blo 299831 675251 := bstep (se 1 (by rfl) ⟨506438, by rfl⟩ : syracuseStep 675251 = 1012877) B1012877
theorem B675287 : Blo 299831 675287 := bstep (se 1 (by rfl) ⟨506465, by rfl⟩ : syracuseStep 675287 = 1012931) B1012931
theorem B511447 : Blo 299831 511447 := bstep (se 1 (by rfl) ⟨383585, by rfl⟩ : syracuseStep 511447 = 767171) B767171
theorem B544243 : Blo 299831 544243 := bstep (se 1 (by rfl) ⟨408182, by rfl⟩ : syracuseStep 544243 = 816365) B816365
theorem B1723949 : Blo 299831 1723949 := bstep (se 3 (by rfl) ⟨323240, by rfl⟩ : syracuseStep 1723949 = 646481) B646481
theorem B1035841 : Blo 299831 1035841 := bstep (se 2 (by rfl) ⟨388440, by rfl⟩ : syracuseStep 1035841 = 776881) B776881
theorem B675467 : Blo 299831 675467 := bstep (se 1 (by rfl) ⟨506600, by rfl⟩ : syracuseStep 675467 = 1013201) B1013201
theorem B675521 : Blo 299831 675521 := bstep (se 2 (by rfl) ⟨253320, by rfl⟩ : syracuseStep 675521 = 506641) B506641
theorem B380695 : Blo 299831 380695 := bstep (se 1 (by rfl) ⟨285521, by rfl⟩ : syracuseStep 380695 = 571043) B571043
theorem B675737 : Blo 299831 675737 := bstep (se 2 (by rfl) ⟨253401, by rfl⟩ : syracuseStep 675737 = 506803) B506803
theorem B675827 : Blo 299831 675827 := bstep (se 1 (by rfl) ⟨506870, by rfl⟩ : syracuseStep 675827 = 1013741) B1013741
theorem B675863 : Blo 299831 675863 := bstep (se 1 (by rfl) ⟨506897, by rfl⟩ : syracuseStep 675863 = 1013795) B1013795
theorem B610327 : Blo 299831 610327 := bstep (se 1 (by rfl) ⟨457745, by rfl⟩ : syracuseStep 610327 = 915491) B915491
theorem B512075 : Blo 299831 512075 := bstep (se 1 (by rfl) ⟨384056, by rfl⟩ : syracuseStep 512075 = 768113) B768113
theorem B544907 : Blo 299831 544907 := bstep (se 1 (by rfl) ⟨408680, by rfl⟩ : syracuseStep 544907 = 817361) B817361
theorem B676043 : Blo 299831 676043 := bstep (se 1 (by rfl) ⟨507032, by rfl⟩ : syracuseStep 676043 = 1014065) B1014065
theorem B512203 : Blo 299831 512203 := bstep (se 1 (by rfl) ⟨384152, by rfl⟩ : syracuseStep 512203 = 768305) B768305
theorem B676097 : Blo 299831 676097 := bstep (se 2 (by rfl) ⟨253536, by rfl⟩ : syracuseStep 676097 = 507073) B507073
theorem B512345 : Blo 299831 512345 := bstep (se 2 (by rfl) ⟨192129, by rfl⟩ : syracuseStep 512345 = 384259) B384259
theorem B643457 : Blo 299831 643457 := bstep (se 2 (by rfl) ⟨241296, by rfl⟩ : syracuseStep 643457 = 482593) B482593
theorem B676313 : Blo 299831 676313 := bstep (se 2 (by rfl) ⟨253617, by rfl⟩ : syracuseStep 676313 = 507235) B507235
theorem B512473 : Blo 299831 512473 := bstep (se 2 (by rfl) ⟨192177, by rfl⟩ : syracuseStep 512473 = 384355) B384355
theorem B1921553 : Blo 299831 1921553 := bstep (se 2 (by rfl) ⟨720582, by rfl⟩ : syracuseStep 1921553 = 1441165) B1441165
theorem B676403 : Blo 299831 676403 := bstep (se 1 (by rfl) ⟨507302, by rfl⟩ : syracuseStep 676403 = 1014605) B1014605
theorem B676439 : Blo 299831 676439 := bstep (se 1 (by rfl) ⟨507329, by rfl⟩ : syracuseStep 676439 = 1014659) B1014659
theorem B2904781 : Blo 299831 2904781 := bstep (se 3 (by rfl) ⟨544646, by rfl⟩ : syracuseStep 2904781 = 1089293) B1089293
theorem B676619 : Blo 299831 676619 := bstep (se 1 (by rfl) ⟨507464, by rfl⟩ : syracuseStep 676619 = 1014929) B1014929
theorem B676673 : Blo 299831 676673 := bstep (se 2 (by rfl) ⟨253752, by rfl⟩ : syracuseStep 676673 = 507505) B507505
theorem B1954691 : Blo 299831 1954691 := bstep (se 1 (by rfl) ⟨1466018, by rfl⟩ : syracuseStep 1954691 = 2932037) B2932037
theorem B2053043 : Blo 299831 2053043 := bstep (se 1 (by rfl) ⟨1539782, by rfl⟩ : syracuseStep 2053043 = 3079565) B3079565
theorem B1528793 : Blo 299831 1528793 := bstep (se 2 (by rfl) ⟨573297, by rfl⟩ : syracuseStep 1528793 = 1146595) B1146595
theorem B676889 : Blo 299831 676889 := bstep (se 2 (by rfl) ⟨253833, by rfl⟩ : syracuseStep 676889 = 507667) B507667
theorem B676979 : Blo 299831 676979 := bstep (se 1 (by rfl) ⟨507734, by rfl⟩ : syracuseStep 676979 = 1015469) B1015469
theorem B677015 : Blo 299831 677015 := bstep (se 1 (by rfl) ⟨507761, by rfl⟩ : syracuseStep 677015 = 1015523) B1015523
theorem B644311 : Blo 299831 644311 := bstep (se 1 (by rfl) ⟨483233, by rfl⟩ : syracuseStep 644311 = 966467) B966467
theorem B677195 : Blo 299831 677195 := bstep (se 1 (by rfl) ⟨507896, by rfl⟩ : syracuseStep 677195 = 1015793) B1015793
theorem B677249 : Blo 299831 677249 := bstep (se 2 (by rfl) ⟨253968, by rfl⟩ : syracuseStep 677249 = 507937) B507937
theorem B1627523 : Blo 299831 1627523 := bstep (se 1 (by rfl) ⟨1220642, by rfl⟩ : syracuseStep 1627523 = 2441285) B2441285
theorem B382411 : Blo 299831 382411 := bstep (se 1 (by rfl) ⟨286808, by rfl⟩ : syracuseStep 382411 = 573617) B573617
theorem B579059 : Blo 299831 579059 := bstep (se 1 (by rfl) ⟨434294, by rfl⟩ : syracuseStep 579059 = 868589) B868589
theorem B513611 : Blo 299831 513611 := bstep (se 1 (by rfl) ⟨385208, by rfl⟩ : syracuseStep 513611 = 770417) B770417
theorem B677465 : Blo 299831 677465 := bstep (se 2 (by rfl) ⟨254049, by rfl⟩ : syracuseStep 677465 = 508099) B508099
theorem B677555 : Blo 299831 677555 := bstep (se 1 (by rfl) ⟨508166, by rfl⟩ : syracuseStep 677555 = 1016333) B1016333
theorem B677591 : Blo 299831 677591 := bstep (se 1 (by rfl) ⟨508193, by rfl⟩ : syracuseStep 677591 = 1016387) B1016387
theorem B677771 : Blo 299831 677771 := bstep (se 1 (by rfl) ⟨508328, by rfl⟩ : syracuseStep 677771 = 1016657) B1016657
theorem B677825 : Blo 299831 677825 := bstep (se 2 (by rfl) ⟨254184, by rfl⟩ : syracuseStep 677825 = 508369) B508369
theorem B645131 : Blo 299831 645131 := bstep (se 1 (by rfl) ⟨483848, by rfl⟩ : syracuseStep 645131 = 967697) B967697
theorem B1038359 : Blo 299831 1038359 := bstep (se 1 (by rfl) ⟨778769, by rfl⟩ : syracuseStep 1038359 = 1557539) B1557539
theorem B972823 : Blo 299831 972823 := bstep (se 1 (by rfl) ⟨729617, by rfl⟩ : syracuseStep 972823 = 1459235) B1459235
theorem B579737 : Blo 299831 579737 := bstep (se 2 (by rfl) ⟨217401, by rfl⟩ : syracuseStep 579737 = 434803) B434803
theorem B678041 : Blo 299831 678041 := bstep (se 2 (by rfl) ⟨254265, by rfl⟩ : syracuseStep 678041 = 508531) B508531
theorem B678131 : Blo 299831 678131 := bstep (se 1 (by rfl) ⟨508598, by rfl⟩ : syracuseStep 678131 = 1017197) B1017197
theorem B678167 : Blo 299831 678167 := bstep (se 1 (by rfl) ⟨508625, by rfl⟩ : syracuseStep 678167 = 1017251) B1017251
theorem B612631 : Blo 299831 612631 := bstep (se 1 (by rfl) ⟨459473, by rfl⟩ : syracuseStep 612631 = 918947) B918947
theorem B383383 : Blo 299831 383383 := bstep (se 1 (by rfl) ⟨287537, by rfl⟩ : syracuseStep 383383 = 575075) B575075
theorem B678347 : Blo 299831 678347 := bstep (se 1 (by rfl) ⟨508760, by rfl⟩ : syracuseStep 678347 = 1017521) B1017521
theorem B678401 : Blo 299831 678401 := bstep (se 2 (by rfl) ⟨254400, by rfl⟩ : syracuseStep 678401 = 508801) B508801
theorem B1530413 : Blo 299831 1530413 := bstep (se 3 (by rfl) ⟨286952, by rfl⟩ : syracuseStep 1530413 = 573905) B573905
theorem B547415 : Blo 299831 547415 := bstep (se 1 (by rfl) ⟨410561, by rfl⟩ : syracuseStep 547415 = 821123) B821123
theorem B678617 : Blo 299831 678617 := bstep (se 2 (by rfl) ⟨254481, by rfl⟩ : syracuseStep 678617 = 508963) B508963
theorem B678707 : Blo 299831 678707 := bstep (se 1 (by rfl) ⟨509030, by rfl⟩ : syracuseStep 678707 = 1018061) B1018061
theorem B678743 : Blo 299831 678743 := bstep (se 1 (by rfl) ⟨509057, by rfl⟩ : syracuseStep 678743 = 1018115) B1018115
theorem B678923 : Blo 299831 678923 := bstep (se 1 (by rfl) ⟨509192, by rfl⟩ : syracuseStep 678923 = 1018385) B1018385
theorem B678977 : Blo 299831 678977 := bstep (se 2 (by rfl) ⟨254616, by rfl⟩ : syracuseStep 678977 = 509233) B509233
theorem B613441 : Blo 299831 613441 := bstep (se 2 (by rfl) ⟨230040, by rfl⟩ : syracuseStep 613441 = 460081) B460081
theorem B1727639 : Blo 299831 1727639 := bstep (se 1 (by rfl) ⟨1295729, by rfl⟩ : syracuseStep 1727639 = 2591459) B2591459
theorem B384203 : Blo 299831 384203 := bstep (se 1 (by rfl) ⟨288152, by rfl⟩ : syracuseStep 384203 = 576305) B576305
theorem B449753 : Blo 299831 449753 := bstep (se 2 (by rfl) ⟨168657, by rfl⟩ : syracuseStep 449753 = 337315) B337315
theorem B679193 : Blo 299831 679193 := bstep (se 2 (by rfl) ⟨254697, by rfl⟩ : syracuseStep 679193 = 509395) B509395
theorem B449867 : Blo 299831 449867 := bstep (se 1 (by rfl) ⟨337400, by rfl⟩ : syracuseStep 449867 = 674801) B674801
theorem B449879 : Blo 299831 449879 := bstep (se 1 (by rfl) ⟨337409, by rfl⟩ : syracuseStep 449879 = 674819) B674819
theorem B679283 : Blo 299831 679283 := bstep (se 1 (by rfl) ⟨509462, by rfl⟩ : syracuseStep 679283 = 1018925) B1018925
theorem B679319 : Blo 299831 679319 := bstep (se 1 (by rfl) ⟨509489, by rfl⟩ : syracuseStep 679319 = 1018979) B1018979
theorem B449945 : Blo 299831 449945 := bstep (se 2 (by rfl) ⟨168729, by rfl⟩ : syracuseStep 449945 = 337459) B337459
theorem B4677041 : Blo 299831 4677041 := bstep (se 2 (by rfl) ⟨1753890, by rfl⟩ : syracuseStep 4677041 = 3507781) B3507781
theorem B450059 : Blo 299831 450059 := bstep (se 1 (by rfl) ⟨337544, by rfl⟩ : syracuseStep 450059 = 675089) B675089
theorem B450071 : Blo 299831 450071 := bstep (se 1 (by rfl) ⟨337553, by rfl⟩ : syracuseStep 450071 = 675107) B675107
theorem B679499 : Blo 299831 679499 := bstep (se 1 (by rfl) ⟨509624, by rfl⟩ : syracuseStep 679499 = 1019249) B1019249
theorem B450137 : Blo 299831 450137 := bstep (se 2 (by rfl) ⟨168801, by rfl⟩ : syracuseStep 450137 = 337603) B337603
theorem B679553 : Blo 299831 679553 := bstep (se 2 (by rfl) ⟨254832, by rfl⟩ : syracuseStep 679553 = 509665) B509665
theorem B450251 : Blo 299831 450251 := bstep (se 1 (by rfl) ⟨337688, by rfl⟩ : syracuseStep 450251 = 675377) B675377
theorem B450263 : Blo 299831 450263 := bstep (se 1 (by rfl) ⟨337697, by rfl⟩ : syracuseStep 450263 = 675395) B675395
theorem B450329 : Blo 299831 450329 := bstep (se 2 (by rfl) ⟨168873, by rfl⟩ : syracuseStep 450329 = 337747) B337747
theorem B679769 : Blo 299831 679769 := bstep (se 2 (by rfl) ⟨254913, by rfl⟩ : syracuseStep 679769 = 509827) B509827
theorem B450443 : Blo 299831 450443 := bstep (se 1 (by rfl) ⟨337832, by rfl⟩ : syracuseStep 450443 = 675665) B675665
theorem B450455 : Blo 299831 450455 := bstep (se 1 (by rfl) ⟨337841, by rfl⟩ : syracuseStep 450455 = 675683) B675683
theorem B679859 : Blo 299831 679859 := bstep (se 1 (by rfl) ⟨509894, by rfl⟩ : syracuseStep 679859 = 1019789) B1019789
theorem B679895 : Blo 299831 679895 := bstep (se 1 (by rfl) ⟨509921, by rfl⟩ : syracuseStep 679895 = 1019843) B1019843
theorem B450521 : Blo 299831 450521 := bstep (se 2 (by rfl) ⟨168945, by rfl⟩ : syracuseStep 450521 = 337891) B337891
theorem B450635 : Blo 299831 450635 := bstep (se 1 (by rfl) ⟨337976, by rfl⟩ : syracuseStep 450635 = 675953) B675953
theorem B450647 : Blo 299831 450647 := bstep (se 1 (by rfl) ⟨337985, by rfl⟩ : syracuseStep 450647 = 675971) B675971
theorem B1138819 : Blo 299831 1138819 := bstep (se 1 (by rfl) ⟨854114, by rfl⟩ : syracuseStep 1138819 = 1708229) B1708229
theorem B680075 : Blo 299831 680075 := bstep (se 1 (by rfl) ⟨510056, by rfl⟩ : syracuseStep 680075 = 1020113) B1020113
theorem B450713 : Blo 299831 450713 := bstep (se 2 (by rfl) ⟨169017, by rfl⟩ : syracuseStep 450713 = 338035) B338035
theorem B680129 : Blo 299831 680129 := bstep (se 2 (by rfl) ⟨255048, by rfl⟩ : syracuseStep 680129 = 510097) B510097
theorem B450827 : Blo 299831 450827 := bstep (se 1 (by rfl) ⟨338120, by rfl⟩ : syracuseStep 450827 = 676241) B676241
theorem B450839 : Blo 299831 450839 := bstep (se 1 (by rfl) ⟨338129, by rfl⟩ : syracuseStep 450839 = 676259) B676259
theorem B647489 : Blo 299831 647489 := bstep (se 2 (by rfl) ⟨242808, by rfl⟩ : syracuseStep 647489 = 485617) B485617
theorem B450905 : Blo 299831 450905 := bstep (se 2 (by rfl) ⟨169089, by rfl⟩ : syracuseStep 450905 = 338179) B338179
theorem B680345 : Blo 299831 680345 := bstep (se 2 (by rfl) ⟨255129, by rfl⟩ : syracuseStep 680345 = 510259) B510259
theorem B1139123 : Blo 299831 1139123 := bstep (se 1 (by rfl) ⟨854342, by rfl⟩ : syracuseStep 1139123 = 1708685) B1708685
theorem B451019 : Blo 299831 451019 := bstep (se 1 (by rfl) ⟨338264, by rfl⟩ : syracuseStep 451019 = 676529) B676529
theorem B451031 : Blo 299831 451031 := bstep (se 1 (by rfl) ⟨338273, by rfl⟩ : syracuseStep 451031 = 676547) B676547
theorem B680435 : Blo 299831 680435 := bstep (se 1 (by rfl) ⟨510326, by rfl⟩ : syracuseStep 680435 = 1020653) B1020653
theorem B680471 : Blo 299831 680471 := bstep (se 1 (by rfl) ⟨510353, by rfl⟩ : syracuseStep 680471 = 1020707) B1020707
theorem B451097 : Blo 299831 451097 := bstep (se 2 (by rfl) ⟨169161, by rfl⟩ : syracuseStep 451097 = 338323) B338323
theorem B451211 : Blo 299831 451211 := bstep (se 1 (by rfl) ⟨338408, by rfl⟩ : syracuseStep 451211 = 676817) B676817
theorem B451223 : Blo 299831 451223 := bstep (se 1 (by rfl) ⟨338417, by rfl⟩ : syracuseStep 451223 = 676835) B676835
theorem B647831 : Blo 299831 647831 := bstep (se 1 (by rfl) ⟨485873, by rfl⟩ : syracuseStep 647831 = 971747) B971747
theorem B680651 : Blo 299831 680651 := bstep (se 1 (by rfl) ⟨510488, by rfl⟩ : syracuseStep 680651 = 1020977) B1020977
theorem B451289 : Blo 299831 451289 := bstep (se 2 (by rfl) ⟨169233, by rfl⟩ : syracuseStep 451289 = 338467) B338467
theorem B680705 : Blo 299831 680705 := bstep (se 2 (by rfl) ⟨255264, by rfl⟩ : syracuseStep 680705 = 510529) B510529
theorem B1925963 : Blo 299831 1925963 := bstep (se 1 (by rfl) ⟨1444472, by rfl⟩ : syracuseStep 1925963 = 2888945) B2888945
theorem B451403 : Blo 299831 451403 := bstep (se 1 (by rfl) ⟨338552, by rfl⟩ : syracuseStep 451403 = 677105) B677105
theorem B451415 : Blo 299831 451415 := bstep (se 1 (by rfl) ⟨338561, by rfl⟩ : syracuseStep 451415 = 677123) B677123
theorem B451481 : Blo 299831 451481 := bstep (se 2 (by rfl) ⟨169305, by rfl⟩ : syracuseStep 451481 = 338611) B338611
theorem B2319283 : Blo 299831 2319283 := bstep (se 1 (by rfl) ⟨1739462, by rfl⟩ : syracuseStep 2319283 = 3478925) B3478925
theorem B680921 : Blo 299831 680921 := bstep (se 2 (by rfl) ⟨255345, by rfl⟩ : syracuseStep 680921 = 510691) B510691
theorem B451595 : Blo 299831 451595 := bstep (se 1 (by rfl) ⟨338696, by rfl⟩ : syracuseStep 451595 = 677393) B677393
theorem B451607 : Blo 299831 451607 := bstep (se 1 (by rfl) ⟨338705, by rfl⟩ : syracuseStep 451607 = 677411) B677411
theorem B681011 : Blo 299831 681011 := bstep (se 1 (by rfl) ⟨510758, by rfl⟩ : syracuseStep 681011 = 1021517) B1021517
theorem B1139777 : Blo 299831 1139777 := bstep (se 2 (by rfl) ⟨427416, by rfl⟩ : syracuseStep 1139777 = 854833) B854833
theorem B681047 : Blo 299831 681047 := bstep (se 1 (by rfl) ⟨510785, by rfl⟩ : syracuseStep 681047 = 1021571) B1021571
theorem B451673 : Blo 299831 451673 := bstep (se 2 (by rfl) ⟨169377, by rfl⟩ : syracuseStep 451673 = 338755) B338755
theorem B9757847 : Blo 299831 9757847 := bstep (se 1 (by rfl) ⟨7318385, by rfl⟩ : syracuseStep 9757847 = 14636771) B14636771
theorem B451787 : Blo 299831 451787 := bstep (se 1 (by rfl) ⟨338840, by rfl⟩ : syracuseStep 451787 = 677681) B677681
theorem B648395 : Blo 299831 648395 := bstep (se 1 (by rfl) ⟨486296, by rfl⟩ : syracuseStep 648395 = 972593) B972593
theorem B451799 : Blo 299831 451799 := bstep (se 1 (by rfl) ⟨338849, by rfl⟩ : syracuseStep 451799 = 677699) B677699
theorem B681227 : Blo 299831 681227 := bstep (se 1 (by rfl) ⟨510920, by rfl⟩ : syracuseStep 681227 = 1021841) B1021841
theorem B451865 : Blo 299831 451865 := bstep (se 2 (by rfl) ⟨169449, by rfl⟩ : syracuseStep 451865 = 338899) B338899
theorem B681281 : Blo 299831 681281 := bstep (se 2 (by rfl) ⟨255480, by rfl⟩ : syracuseStep 681281 = 510961) B510961
theorem B451979 : Blo 299831 451979 := bstep (se 1 (by rfl) ⟨338984, by rfl⟩ : syracuseStep 451979 = 677969) B677969
theorem B451991 : Blo 299831 451991 := bstep (se 1 (by rfl) ⟨338993, by rfl⟩ : syracuseStep 451991 = 677987) B677987
theorem B452057 : Blo 299831 452057 := bstep (se 2 (by rfl) ⟨169521, by rfl⟩ : syracuseStep 452057 = 339043) B339043
theorem B681497 : Blo 299831 681497 := bstep (se 2 (by rfl) ⟨255561, by rfl⟩ : syracuseStep 681497 = 511123) B511123
theorem B452171 : Blo 299831 452171 := bstep (se 1 (by rfl) ⟨339128, by rfl⟩ : syracuseStep 452171 = 678257) B678257
theorem B452183 : Blo 299831 452183 := bstep (se 1 (by rfl) ⟨339137, by rfl⟩ : syracuseStep 452183 = 678275) B678275
theorem B681587 : Blo 299831 681587 := bstep (se 1 (by rfl) ⟨511190, by rfl⟩ : syracuseStep 681587 = 1022381) B1022381
theorem B681623 : Blo 299831 681623 := bstep (se 1 (by rfl) ⟨511217, by rfl⟩ : syracuseStep 681623 = 1022435) B1022435
theorem B452249 : Blo 299831 452249 := bstep (se 2 (by rfl) ⟨169593, by rfl⟩ : syracuseStep 452249 = 339187) B339187
theorem B452363 : Blo 299831 452363 := bstep (se 1 (by rfl) ⟨339272, by rfl⟩ : syracuseStep 452363 = 678545) B678545
theorem B386839 : Blo 299831 386839 := bstep (se 1 (by rfl) ⟨290129, by rfl⟩ : syracuseStep 386839 = 580259) B580259
theorem B452375 : Blo 299831 452375 := bstep (se 1 (by rfl) ⟨339281, by rfl⟩ : syracuseStep 452375 = 678563) B678563
theorem B681803 : Blo 299831 681803 := bstep (se 1 (by rfl) ⟨511352, by rfl⟩ : syracuseStep 681803 = 1022705) B1022705
theorem B485207 : Blo 299831 485207 := bstep (se 1 (by rfl) ⟨363905, by rfl⟩ : syracuseStep 485207 = 727811) B727811
theorem B452441 : Blo 299831 452441 := bstep (se 2 (by rfl) ⟨169665, by rfl⟩ : syracuseStep 452441 = 339331) B339331
theorem B681857 : Blo 299831 681857 := bstep (se 2 (by rfl) ⟨255696, by rfl⟩ : syracuseStep 681857 = 511393) B511393
theorem B452555 : Blo 299831 452555 := bstep (se 1 (by rfl) ⟨339416, by rfl⟩ : syracuseStep 452555 = 678833) B678833
theorem B452567 : Blo 299831 452567 := bstep (se 1 (by rfl) ⟨339425, by rfl⟩ : syracuseStep 452567 = 678851) B678851
theorem B452633 : Blo 299831 452633 := bstep (se 2 (by rfl) ⟨169737, by rfl⟩ : syracuseStep 452633 = 339475) B339475
theorem B682073 : Blo 299831 682073 := bstep (se 2 (by rfl) ⟨255777, by rfl⟩ : syracuseStep 682073 = 511555) B511555
theorem B452747 : Blo 299831 452747 := bstep (se 1 (by rfl) ⟨339560, by rfl⟩ : syracuseStep 452747 = 679121) B679121
theorem B452759 : Blo 299831 452759 := bstep (se 1 (by rfl) ⟨339569, by rfl⟩ : syracuseStep 452759 = 679139) B679139
theorem B682163 : Blo 299831 682163 := bstep (se 1 (by rfl) ⟨511622, by rfl⟩ : syracuseStep 682163 = 1023245) B1023245
theorem B682199 : Blo 299831 682199 := bstep (se 1 (by rfl) ⟨511649, by rfl⟩ : syracuseStep 682199 = 1023299) B1023299
theorem B452825 : Blo 299831 452825 := bstep (se 2 (by rfl) ⟨169809, by rfl⟩ : syracuseStep 452825 = 339619) B339619
theorem B1141037 : Blo 299831 1141037 := bstep (se 3 (by rfl) ⟨213944, by rfl⟩ : syracuseStep 1141037 = 427889) B427889
theorem B1141067 : Blo 299831 1141067 := bstep (se 1 (by rfl) ⟨855800, by rfl⟩ : syracuseStep 1141067 = 1711601) B1711601
theorem B452939 : Blo 299831 452939 := bstep (se 1 (by rfl) ⟨339704, by rfl⟩ : syracuseStep 452939 = 679409) B679409
theorem B452951 : Blo 299831 452951 := bstep (se 1 (by rfl) ⟨339713, by rfl⟩ : syracuseStep 452951 = 679427) B679427
theorem B485719 : Blo 299831 485719 := bstep (se 1 (by rfl) ⟨364289, by rfl⟩ : syracuseStep 485719 = 728579) B728579
theorem B1534301 : Blo 299831 1534301 := bstep (se 3 (by rfl) ⟨287681, by rfl⟩ : syracuseStep 1534301 = 575363) B575363
theorem B321899 : Blo 299831 321899 := bstep (se 1 (by rfl) ⟨241424, by rfl⟩ : syracuseStep 321899 = 482849) B482849
theorem B55568753 : Blo 299831 55568753 := bstep (se 2 (by rfl) ⟨20838282, by rfl⟩ : syracuseStep 55568753 = 41676565) B41676565
theorem B682379 : Blo 299831 682379 := bstep (se 1 (by rfl) ⟨511784, by rfl⟩ : syracuseStep 682379 = 1023569) B1023569
theorem B453017 : Blo 299831 453017 := bstep (se 2 (by rfl) ⟨169881, by rfl⟩ : syracuseStep 453017 = 339763) B339763
theorem B682433 : Blo 299831 682433 := bstep (se 2 (by rfl) ⟨255912, by rfl⟩ : syracuseStep 682433 = 511825) B511825
theorem B453131 : Blo 299831 453131 := bstep (se 1 (by rfl) ⟨339848, by rfl⟩ : syracuseStep 453131 = 679697) B679697
theorem B453143 : Blo 299831 453143 := bstep (se 1 (by rfl) ⟨339857, by rfl⟩ : syracuseStep 453143 = 679715) B679715
theorem B2058817 : Blo 299831 2058817 := bstep (se 2 (by rfl) ⟨772056, by rfl⟩ : syracuseStep 2058817 = 1544113) B1544113
theorem B453209 : Blo 299831 453209 := bstep (se 2 (by rfl) ⟨169953, by rfl⟩ : syracuseStep 453209 = 339907) B339907
theorem B682649 : Blo 299831 682649 := bstep (se 2 (by rfl) ⟨255993, by rfl⟩ : syracuseStep 682649 = 511987) B511987
theorem B453323 : Blo 299831 453323 := bstep (se 1 (by rfl) ⟨339992, by rfl⟩ : syracuseStep 453323 = 679985) B679985
theorem B486091 : Blo 299831 486091 := bstep (se 1 (by rfl) ⟨364568, by rfl⟩ : syracuseStep 486091 = 729137) B729137
theorem B453335 : Blo 299831 453335 := bstep (se 1 (by rfl) ⟨340001, by rfl⟩ : syracuseStep 453335 = 680003) B680003
theorem B682739 : Blo 299831 682739 := bstep (se 1 (by rfl) ⟨512054, by rfl⟩ : syracuseStep 682739 = 1024109) B1024109
theorem B813847 : Blo 299831 813847 := bstep (se 1 (by rfl) ⟨610385, by rfl⟩ : syracuseStep 813847 = 1220771) B1220771
theorem B682775 : Blo 299831 682775 := bstep (se 1 (by rfl) ⟨512081, by rfl⟩ : syracuseStep 682775 = 1024163) B1024163
theorem B453401 : Blo 299831 453401 := bstep (se 2 (by rfl) ⟨170025, by rfl⟩ : syracuseStep 453401 = 340051) B340051
theorem B453515 : Blo 299831 453515 := bstep (se 1 (by rfl) ⟨340136, by rfl⟩ : syracuseStep 453515 = 680273) B680273
theorem B453527 : Blo 299831 453527 := bstep (se 1 (by rfl) ⟨340145, by rfl⟩ : syracuseStep 453527 = 680291) B680291
theorem B682955 : Blo 299831 682955 := bstep (se 1 (by rfl) ⟨512216, by rfl⟩ : syracuseStep 682955 = 1024433) B1024433
theorem B1141721 : Blo 299831 1141721 := bstep (se 2 (by rfl) ⟨428145, by rfl⟩ : syracuseStep 1141721 = 856291) B856291
theorem B453593 : Blo 299831 453593 := bstep (se 2 (by rfl) ⟨170097, by rfl⟩ : syracuseStep 453593 = 340195) B340195
theorem B683009 : Blo 299831 683009 := bstep (se 2 (by rfl) ⟨256128, by rfl⟩ : syracuseStep 683009 = 512257) B512257
theorem B650315 : Blo 299831 650315 := bstep (se 1 (by rfl) ⟨487736, by rfl⟩ : syracuseStep 650315 = 975473) B975473
theorem B453707 : Blo 299831 453707 := bstep (se 1 (by rfl) ⟨340280, by rfl⟩ : syracuseStep 453707 = 680561) B680561
theorem B453719 : Blo 299831 453719 := bstep (se 1 (by rfl) ⟨340289, by rfl⟩ : syracuseStep 453719 = 680579) B680579
theorem B453785 : Blo 299831 453785 := bstep (se 2 (by rfl) ⟨170169, by rfl⟩ : syracuseStep 453785 = 340339) B340339
theorem B683225 : Blo 299831 683225 := bstep (se 2 (by rfl) ⟨256209, by rfl⟩ : syracuseStep 683225 = 512419) B512419
theorem B453899 : Blo 299831 453899 := bstep (se 1 (by rfl) ⟨340424, by rfl⟩ : syracuseStep 453899 = 680849) B680849
theorem B1142039 : Blo 299831 1142039 := bstep (se 1 (by rfl) ⟨856529, by rfl⟩ : syracuseStep 1142039 = 1713059) B1713059
theorem B453911 : Blo 299831 453911 := bstep (se 1 (by rfl) ⟨340433, by rfl⟩ : syracuseStep 453911 = 680867) B680867
theorem B683315 : Blo 299831 683315 := bstep (se 1 (by rfl) ⟨512486, by rfl⟩ : syracuseStep 683315 = 1024973) B1024973
theorem B683351 : Blo 299831 683351 := bstep (se 1 (by rfl) ⟨512513, by rfl⟩ : syracuseStep 683351 = 1025027) B1025027
theorem B453977 : Blo 299831 453977 := bstep (se 2 (by rfl) ⟨170241, by rfl⟩ : syracuseStep 453977 = 340483) B340483
theorem B1371485 : Blo 299831 1371485 := bstep (se 3 (by rfl) ⟨257153, by rfl⟩ : syracuseStep 1371485 = 514307) B514307
theorem B454091 : Blo 299831 454091 := bstep (se 1 (by rfl) ⟨340568, by rfl⟩ : syracuseStep 454091 = 681137) B681137
theorem B454103 : Blo 299831 454103 := bstep (se 1 (by rfl) ⟨340577, by rfl⟩ : syracuseStep 454103 = 681155) B681155
theorem B683531 : Blo 299831 683531 := bstep (se 1 (by rfl) ⟨512648, by rfl⟩ : syracuseStep 683531 = 1025297) B1025297
theorem B7368209 : Blo 299831 7368209 := bstep (se 2 (by rfl) ⟨2763078, by rfl⟩ : syracuseStep 7368209 = 5526157) B5526157
theorem B454169 : Blo 299831 454169 := bstep (se 2 (by rfl) ⟨170313, by rfl⟩ : syracuseStep 454169 = 340627) B340627
theorem B683585 : Blo 299831 683585 := bstep (se 2 (by rfl) ⟨256344, by rfl⟩ : syracuseStep 683585 = 512689) B512689
theorem B454283 : Blo 299831 454283 := bstep (se 1 (by rfl) ⟨340712, by rfl⟩ : syracuseStep 454283 = 681425) B681425
theorem B454295 : Blo 299831 454295 := bstep (se 1 (by rfl) ⟨340721, by rfl⟩ : syracuseStep 454295 = 681443) B681443
theorem B1994419 : Blo 299831 1994419 := bstep (se 1 (by rfl) ⟨1495814, by rfl⟩ : syracuseStep 1994419 = 2991629) B2991629
theorem B454361 : Blo 299831 454361 := bstep (se 2 (by rfl) ⟨170385, by rfl⟩ : syracuseStep 454361 = 340771) B340771
theorem B454475 : Blo 299831 454475 := bstep (se 1 (by rfl) ⟨340856, by rfl⟩ : syracuseStep 454475 = 681713) B681713
theorem B454487 : Blo 299831 454487 := bstep (se 1 (by rfl) ⟨340865, by rfl⟩ : syracuseStep 454487 = 681731) B681731
theorem B454553 : Blo 299831 454553 := bstep (se 2 (by rfl) ⟨170457, by rfl⟩ : syracuseStep 454553 = 340915) B340915
theorem B1142707 : Blo 299831 1142707 := bstep (se 1 (by rfl) ⟨857030, by rfl⟩ : syracuseStep 1142707 = 1714061) B1714061
theorem B3436505 : Blo 299831 3436505 := bstep (se 2 (by rfl) ⟨1288689, by rfl⟩ : syracuseStep 3436505 = 2577379) B2577379
theorem B454667 : Blo 299831 454667 := bstep (se 1 (by rfl) ⟨341000, by rfl⟩ : syracuseStep 454667 = 682001) B682001
theorem B454679 : Blo 299831 454679 := bstep (se 1 (by rfl) ⟨341009, by rfl⟩ : syracuseStep 454679 = 682019) B682019
theorem B323659 : Blo 299831 323659 := bstep (se 1 (by rfl) ⟨242744, by rfl⟩ : syracuseStep 323659 = 485489) B485489
theorem B454745 : Blo 299831 454745 := bstep (se 2 (by rfl) ⟨170529, by rfl⟩ : syracuseStep 454745 = 341059) B341059
theorem B454859 : Blo 299831 454859 := bstep (se 1 (by rfl) ⟨341144, by rfl⟩ : syracuseStep 454859 = 682289) B682289
theorem B454871 : Blo 299831 454871 := bstep (se 1 (by rfl) ⟨341153, by rfl⟩ : syracuseStep 454871 = 682307) B682307
theorem B454937 : Blo 299831 454937 := bstep (se 2 (by rfl) ⟨170601, by rfl⟩ : syracuseStep 454937 = 341203) B341203
theorem B913739 : Blo 299831 913739 := bstep (se 1 (by rfl) ⟨685304, by rfl⟩ : syracuseStep 913739 = 1370609) B1370609
theorem B455051 : Blo 299831 455051 := bstep (se 1 (by rfl) ⟨341288, by rfl⟩ : syracuseStep 455051 = 682577) B682577
theorem B455063 : Blo 299831 455063 := bstep (se 1 (by rfl) ⟨341297, by rfl⟩ : syracuseStep 455063 = 682595) B682595
theorem B1536407 : Blo 299831 1536407 := bstep (se 1 (by rfl) ⟨1152305, by rfl⟩ : syracuseStep 1536407 = 2304611) B2304611
theorem B455129 : Blo 299831 455129 := bstep (se 2 (by rfl) ⟨170673, by rfl⟩ : syracuseStep 455129 = 341347) B341347
theorem B455243 : Blo 299831 455243 := bstep (se 1 (by rfl) ⟨341432, by rfl⟩ : syracuseStep 455243 = 682865) B682865
theorem B455255 : Blo 299831 455255 := bstep (se 1 (by rfl) ⟨341441, by rfl⟩ : syracuseStep 455255 = 682883) B682883
theorem B455321 : Blo 299831 455321 := bstep (se 2 (by rfl) ⟨170745, by rfl⟩ : syracuseStep 455321 = 341491) B341491
theorem B1012445 : Blo 299831 1012445 := bstep (se 3 (by rfl) ⟨189833, by rfl⟩ : syracuseStep 1012445 = 379667) B379667
theorem B455435 : Blo 299831 455435 := bstep (se 1 (by rfl) ⟨341576, by rfl⟩ : syracuseStep 455435 = 683153) B683153
theorem B455447 : Blo 299831 455447 := bstep (se 1 (by rfl) ⟨341585, by rfl⟩ : syracuseStep 455447 = 683171) B683171
theorem B1471277 : Blo 299831 1471277 := bstep (se 3 (by rfl) ⟨275864, by rfl⟩ : syracuseStep 1471277 = 551729) B551729
theorem B455513 : Blo 299831 455513 := bstep (se 2 (by rfl) ⟨170817, by rfl⟩ : syracuseStep 455513 = 341635) B341635
theorem B1242049 : Blo 299831 1242049 := bstep (se 2 (by rfl) ⟨465768, by rfl⟩ : syracuseStep 1242049 = 931537) B931537
theorem B455627 : Blo 299831 455627 := bstep (se 1 (by rfl) ⟨341720, by rfl⟩ : syracuseStep 455627 = 683441) B683441
theorem B455639 : Blo 299831 455639 := bstep (se 1 (by rfl) ⟨341729, by rfl⟩ : syracuseStep 455639 = 683459) B683459
theorem B455705 : Blo 299831 455705 := bstep (se 2 (by rfl) ⟨170889, by rfl⟩ : syracuseStep 455705 = 341779) B341779
theorem B1143953 : Blo 299831 1143953 := bstep (se 2 (by rfl) ⟨428982, by rfl⟩ : syracuseStep 1143953 = 857965) B857965
theorem B816961 : Blo 299831 816961 := bstep (se 2 (by rfl) ⟨306360, by rfl⟩ : syracuseStep 816961 = 612721) B612721
theorem B1013579 : Blo 299831 1013579 := bstep (se 1 (by rfl) ⟨760184, by rfl⟩ : syracuseStep 1013579 = 1520369) B1520369
theorem B1144651 : Blo 299831 1144651 := bstep (se 1 (by rfl) ⟨858488, by rfl⟩ : syracuseStep 1144651 = 1716977) B1716977
theorem B1013849 : Blo 299831 1013849 := bstep (se 2 (by rfl) ⟨380193, by rfl⟩ : syracuseStep 1013849 = 760387) B760387
theorem B1144925 : Blo 299831 1144925 := bstep (se 3 (by rfl) ⟨214673, by rfl⟩ : syracuseStep 1144925 = 429347) B429347
theorem B2587085 : Blo 299831 2587085 := bstep (se 3 (by rfl) ⟨485078, by rfl⟩ : syracuseStep 2587085 = 970157) B970157
theorem B1014551 : Blo 299831 1014551 := bstep (se 1 (by rfl) ⟨760913, by rfl⟩ : syracuseStep 1014551 = 1521827) B1521827
theorem B1145623 : Blo 299831 1145623 := bstep (se 1 (by rfl) ⟨859217, by rfl⟩ : syracuseStep 1145623 = 1718435) B1718435
theorem B818009 : Blo 299831 818009 := bstep (se 2 (by rfl) ⟨306753, by rfl⟩ : syracuseStep 818009 = 613507) B613507
theorem B1834001 : Blo 299831 1834001 := bstep (se 2 (by rfl) ⟨687750, by rfl⟩ : syracuseStep 1834001 = 1375501) B1375501
theorem B6290507 : Blo 299831 6290507 := bstep (se 1 (by rfl) ⟨4717880, by rfl⟩ : syracuseStep 6290507 = 9435761) B9435761
theorem B490583 : Blo 299831 490583 := bstep (se 1 (by rfl) ⟨367937, by rfl⟩ : syracuseStep 490583 = 735875) B735875
theorem B1440899 : Blo 299831 1440899 := bstep (se 1 (by rfl) ⟨1080674, by rfl⟩ : syracuseStep 1440899 = 2161349) B2161349
theorem B1015091 : Blo 299831 1015091 := bstep (se 1 (by rfl) ⟨761318, by rfl⟩ : syracuseStep 1015091 = 1522637) B1522637
theorem B1146413 : Blo 299831 1146413 := bstep (se 3 (by rfl) ⟨214952, by rfl⟩ : syracuseStep 1146413 = 429905) B429905
theorem B1015361 : Blo 299831 1015361 := bstep (se 2 (by rfl) ⟨380760, by rfl⟩ : syracuseStep 1015361 = 761521) B761521
theorem B2916161 : Blo 299831 2916161 := bstep (se 2 (by rfl) ⟨1093560, by rfl⟩ : syracuseStep 2916161 = 2187121) B2187121
theorem B360407 : Blo 299831 360407 := bstep (se 1 (by rfl) ⟨270305, by rfl⟩ : syracuseStep 360407 = 540611) B540611
theorem B688171 : Blo 299831 688171 := bstep (se 1 (by rfl) ⟨516128, by rfl⟩ : syracuseStep 688171 = 1032257) B1032257
theorem B327815 : Blo 299831 327815 := bstep (se 1 (by rfl) ⟨245861, by rfl⟩ : syracuseStep 327815 = 491723) B491723
theorem B1016009 : Blo 299831 1016009 := bstep (se 2 (by rfl) ⟨381003, by rfl⟩ : syracuseStep 1016009 = 762007) B762007
theorem B1147081 : Blo 299831 1147081 := bstep (se 2 (by rfl) ⟨430155, by rfl⟩ : syracuseStep 1147081 = 860311) B860311
theorem B1933703 : Blo 299831 1933703 := bstep (se 1 (by rfl) ⟨1450277, by rfl⟩ : syracuseStep 1933703 = 2900555) B2900555
theorem B1933753 : Blo 299831 1933753 := bstep (se 2 (by rfl) ⟨725157, by rfl⟩ : syracuseStep 1933753 = 1450315) B1450315
theorem B1081943 : Blo 299831 1081943 := bstep (se 1 (by rfl) ⟨811457, by rfl⟩ : syracuseStep 1081943 = 1622915) B1622915
theorem B3277529 : Blo 299831 3277529 := bstep (se 2 (by rfl) ⟨1229073, by rfl⟩ : syracuseStep 3277529 = 2458147) B2458147
theorem B1016711 : Blo 299831 1016711 := bstep (se 1 (by rfl) ⟨762533, by rfl⟩ : syracuseStep 1016711 = 1525067) B1525067
theorem B3867709 : Blo 299831 3867709 := bstep (se 3 (by rfl) ⟨725195, by rfl⟩ : syracuseStep 3867709 = 1450391) B1450391
theorem B1017089 : Blo 299831 1017089 := bstep (se 2 (by rfl) ⟨381408, by rfl⟩ : syracuseStep 1017089 = 762817) B762817
theorem B2917853 : Blo 299831 2917853 := bstep (se 3 (by rfl) ⟨547097, by rfl⟩ : syracuseStep 2917853 = 1094195) B1094195
theorem B1476107 : Blo 299831 1476107 := bstep (se 1 (by rfl) ⟨1107080, by rfl⟩ : syracuseStep 1476107 = 2214161) B2214161
theorem B22808141 : Blo 299831 22808141 := bstep (se 3 (by rfl) ⟨4276526, by rfl⟩ : syracuseStep 22808141 = 8553053) B8553053
theorem B362171 : Blo 299831 362171 := bstep (se 1 (by rfl) ⟨271628, by rfl⟩ : syracuseStep 362171 = 543257) B543257
theorem B2590501 : Blo 299831 2590501 := bstep (se 4 (by rfl) ⟨242859, by rfl⟩ : syracuseStep 2590501 = 485719) B485719
theorem B821035 : Blo 299831 821035 := bstep (se 1 (by rfl) ⟨615776, by rfl⟩ : syracuseStep 821035 = 1231553) B1231553
theorem B1017899 : Blo 299831 1017899 := bstep (se 1 (by rfl) ⟨763424, by rfl⟩ : syracuseStep 1017899 = 1526849) B1526849
theorem B1444013 : Blo 299831 1444013 := bstep (se 3 (by rfl) ⟨270752, by rfl⟩ : syracuseStep 1444013 = 541505) B541505
theorem B6621425 : Blo 299831 6621425 := bstep (se 2 (by rfl) ⟨2483034, by rfl⟩ : syracuseStep 6621425 = 4966069) B4966069
theorem B1149299 : Blo 299831 1149299 := bstep (se 1 (by rfl) ⟨861974, by rfl⟩ : syracuseStep 1149299 = 1723949) B1723949
theorem B723467 : Blo 299831 723467 := bstep (se 1 (by rfl) ⟨542600, by rfl⟩ : syracuseStep 723467 = 1085201) B1085201
theorem B2296349 : Blo 299831 2296349 := bstep (se 3 (by rfl) ⟨430565, by rfl⟩ : syracuseStep 2296349 = 861131) B861131
theorem B2230861 : Blo 299831 2230861 := bstep (se 3 (by rfl) ⟨418286, by rfl⟩ : syracuseStep 2230861 = 836573) B836573
theorem B920249 : Blo 299831 920249 := bstep (se 2 (by rfl) ⟨345093, by rfl⟩ : syracuseStep 920249 = 690187) B690187
theorem B723755 : Blo 299831 723755 := bstep (se 1 (by rfl) ⟨542816, by rfl⟩ : syracuseStep 723755 = 1085633) B1085633
theorem B4655987 : Blo 299831 4655987 := bstep (se 1 (by rfl) ⟨3491990, by rfl⟩ : syracuseStep 4655987 = 6983981) B6983981
theorem B1379207 : Blo 299831 1379207 := bstep (se 1 (by rfl) ⟨1034405, by rfl⟩ : syracuseStep 1379207 = 2068811) B2068811
theorem B428971 : Blo 299831 428971 := bstep (se 1 (by rfl) ⟨321728, by rfl⟩ : syracuseStep 428971 = 643457) B643457
theorem B1281035 : Blo 299831 1281035 := bstep (se 1 (by rfl) ⟨960776, by rfl⟩ : syracuseStep 1281035 = 1921553) B1921553
theorem B4656365 : Blo 299831 4656365 := bstep (se 3 (by rfl) ⟨873068, by rfl⟩ : syracuseStep 4656365 = 1746137) B1746137
theorem B1019195 : Blo 299831 1019195 := bstep (se 1 (by rfl) ⟨764396, by rfl⟩ : syracuseStep 1019195 = 1528793) B1528793
theorem B1085015 : Blo 299831 1085015 := bstep (se 1 (by rfl) ⟨813761, by rfl⟩ : syracuseStep 1085015 = 1627523) B1627523
theorem B921223 : Blo 299831 921223 := bstep (se 1 (by rfl) ⟨690917, by rfl⟩ : syracuseStep 921223 = 1381835) B1381835
theorem B1085129 : Blo 299831 1085129 := bstep (se 2 (by rfl) ⟨406923, by rfl⟩ : syracuseStep 1085129 = 813847) B813847
theorem B2592485 : Blo 299831 2592485 := bstep (se 4 (by rfl) ⟨243045, by rfl⟩ : syracuseStep 2592485 = 486091) B486091
theorem B1019681 : Blo 299831 1019681 := bstep (se 2 (by rfl) ⟨382380, by rfl⟩ : syracuseStep 1019681 = 764761) B764761
theorem B1707911 : Blo 299831 1707911 := bstep (se 1 (by rfl) ⟨1280933, by rfl⟩ : syracuseStep 1707911 = 2561867) B2561867
theorem B1281977 : Blo 299831 1281977 := bstep (se 2 (by rfl) ⟨480741, by rfl⟩ : syracuseStep 1281977 = 961483) B961483
theorem B692239 : Blo 299831 692239 := bstep (se 1 (by rfl) ⟨519179, by rfl⟩ : syracuseStep 692239 = 1038359) B1038359
theorem B1020275 : Blo 299831 1020275 := bstep (se 1 (by rfl) ⟨765206, by rfl⟩ : syracuseStep 1020275 = 1530413) B1530413
theorem B856439 : Blo 299831 856439 := bstep (se 1 (by rfl) ⟨642329, by rfl⟩ : syracuseStep 856439 = 1284659) B1284659
theorem B364943 : Blo 299831 364943 := bstep (se 1 (by rfl) ⟨273707, by rfl⟩ : syracuseStep 364943 = 547415) B547415
theorem B1151441 : Blo 299831 1151441 := bstep (se 2 (by rfl) ⟨431790, by rfl⟩ : syracuseStep 1151441 = 863581) B863581
theorem B21041795 : Blo 299831 21041795 := bstep (se 1 (by rfl) ⟨15781346, by rfl⟩ : syracuseStep 21041795 = 31562693) B31562693
theorem B725657 : Blo 299831 725657 := bstep (se 2 (by rfl) ⟨272121, by rfl⟩ : syracuseStep 725657 = 544243) B544243
theorem B1381121 : Blo 299831 1381121 := bstep (se 2 (by rfl) ⟨517920, by rfl⟩ : syracuseStep 1381121 = 1035841) B1035841
theorem B1151759 : Blo 299831 1151759 := bstep (se 1 (by rfl) ⟨863819, by rfl⟩ : syracuseStep 1151759 = 1727639) B1727639
theorem B299835 : Blo 299831 299835 := bstep (se 1 (by rfl) ⟨224876, by rfl⟩ : syracuseStep 299835 = 449753) B449753
theorem B725879 : Blo 299831 725879 := bstep (se 1 (by rfl) ⟨544409, by rfl⟩ : syracuseStep 725879 = 1088819) B1088819
theorem B922487 : Blo 299831 922487 := bstep (se 1 (by rfl) ⟨691865, by rfl⟩ : syracuseStep 922487 = 1383731) B1383731
theorem B299911 : Blo 299831 299911 := bstep (se 1 (by rfl) ⟨224933, by rfl⟩ : syracuseStep 299911 = 449867) B449867
theorem B299919 : Blo 299831 299919 := bstep (se 1 (by rfl) ⟨224939, by rfl⟩ : syracuseStep 299919 = 449879) B449879
theorem B2659225 : Blo 299831 2659225 := bstep (se 2 (by rfl) ⟨997209, by rfl⟩ : syracuseStep 2659225 = 1994419) B1994419
theorem B299963 : Blo 299831 299963 := bstep (se 1 (by rfl) ⟨224972, by rfl⟩ : syracuseStep 299963 = 449945) B449945
theorem B3118027 : Blo 299831 3118027 := bstep (se 1 (by rfl) ⟨2338520, by rfl⟩ : syracuseStep 3118027 = 4677041) B4677041
theorem B300039 : Blo 299831 300039 := bstep (se 1 (by rfl) ⟨225029, by rfl⟩ : syracuseStep 300039 = 450059) B450059
theorem B300047 : Blo 299831 300047 := bstep (se 1 (by rfl) ⟨225035, by rfl⟩ : syracuseStep 300047 = 450071) B450071
theorem B300091 : Blo 299831 300091 := bstep (se 1 (by rfl) ⟨225068, by rfl⟩ : syracuseStep 300091 = 450137) B450137
theorem B300167 : Blo 299831 300167 := bstep (se 1 (by rfl) ⟨225125, by rfl⟩ : syracuseStep 300167 = 450251) B450251
theorem B300175 : Blo 299831 300175 := bstep (se 1 (by rfl) ⟨225131, by rfl⟩ : syracuseStep 300175 = 450263) B450263
theorem B300219 : Blo 299831 300219 := bstep (se 1 (by rfl) ⟨225164, by rfl⟩ : syracuseStep 300219 = 450329) B450329
theorem B759041 : Blo 299831 759041 := bstep (se 2 (by rfl) ⟨284640, by rfl⟩ : syracuseStep 759041 = 569281) B569281
theorem B300295 : Blo 299831 300295 := bstep (se 1 (by rfl) ⟨225221, by rfl⟩ : syracuseStep 300295 = 450443) B450443
theorem B300303 : Blo 299831 300303 := bstep (se 1 (by rfl) ⟨225227, by rfl⟩ : syracuseStep 300303 = 450455) B450455
theorem B300347 : Blo 299831 300347 := bstep (se 1 (by rfl) ⟨225260, by rfl⟩ : syracuseStep 300347 = 450521) B450521
theorem B300423 : Blo 299831 300423 := bstep (se 1 (by rfl) ⟨225317, by rfl⟩ : syracuseStep 300423 = 450635) B450635
theorem B300431 : Blo 299831 300431 := bstep (se 1 (by rfl) ⟨225323, by rfl⟩ : syracuseStep 300431 = 450647) B450647
theorem B300475 : Blo 299831 300475 := bstep (se 1 (by rfl) ⟨225356, by rfl⟩ : syracuseStep 300475 = 450713) B450713
theorem B923081 : Blo 299831 923081 := bstep (se 2 (by rfl) ⟨346155, by rfl⟩ : syracuseStep 923081 = 692311) B692311
theorem B300551 : Blo 299831 300551 := bstep (se 1 (by rfl) ⟨225413, by rfl⟩ : syracuseStep 300551 = 450827) B450827
theorem B300559 : Blo 299831 300559 := bstep (se 1 (by rfl) ⟨225419, by rfl⟩ : syracuseStep 300559 = 450839) B450839
theorem B431659 : Blo 299831 431659 := bstep (se 1 (by rfl) ⟨323744, by rfl⟩ : syracuseStep 431659 = 647489) B647489
theorem B300603 : Blo 299831 300603 := bstep (se 1 (by rfl) ⟨225452, by rfl⟩ : syracuseStep 300603 = 450905) B450905
theorem B759415 : Blo 299831 759415 := bstep (se 1 (by rfl) ⟨569561, by rfl⟩ : syracuseStep 759415 = 1139123) B1139123
theorem B1709687 : Blo 299831 1709687 := bstep (se 1 (by rfl) ⟨1282265, by rfl⟩ : syracuseStep 1709687 = 2564531) B2564531
theorem B300679 : Blo 299831 300679 := bstep (se 1 (by rfl) ⟨225509, by rfl⟩ : syracuseStep 300679 = 451019) B451019
theorem B300687 : Blo 299831 300687 := bstep (se 1 (by rfl) ⟨225515, by rfl⟩ : syracuseStep 300687 = 451031) B451031
theorem B300731 : Blo 299831 300731 := bstep (se 1 (by rfl) ⟨225548, by rfl⟩ : syracuseStep 300731 = 451097) B451097
theorem B1545965 : Blo 299831 1545965 := bstep (se 3 (by rfl) ⟨289868, by rfl⟩ : syracuseStep 1545965 = 579737) B579737
theorem B300807 : Blo 299831 300807 := bstep (se 1 (by rfl) ⟨225605, by rfl⟩ : syracuseStep 300807 = 451211) B451211
theorem B300815 : Blo 299831 300815 := bstep (se 1 (by rfl) ⟨225611, by rfl⟩ : syracuseStep 300815 = 451223) B451223
theorem B431887 : Blo 299831 431887 := bstep (se 1 (by rfl) ⟨323915, by rfl⟩ : syracuseStep 431887 = 647831) B647831
theorem B300859 : Blo 299831 300859 := bstep (se 1 (by rfl) ⟨225644, by rfl⟩ : syracuseStep 300859 = 451289) B451289
theorem B4331339 : Blo 299831 4331339 := bstep (se 1 (by rfl) ⟨3248504, by rfl⟩ : syracuseStep 4331339 = 6497009) B6497009
theorem B1283975 : Blo 299831 1283975 := bstep (se 1 (by rfl) ⟨962981, by rfl⟩ : syracuseStep 1283975 = 1925963) B1925963
theorem B300935 : Blo 299831 300935 := bstep (se 1 (by rfl) ⟨225701, by rfl⟩ : syracuseStep 300935 = 451403) B451403
theorem B300943 : Blo 299831 300943 := bstep (se 1 (by rfl) ⟨225707, by rfl⟩ : syracuseStep 300943 = 451415) B451415
theorem B300987 : Blo 299831 300987 := bstep (se 1 (by rfl) ⟨225740, by rfl⟩ : syracuseStep 300987 = 451481) B451481
theorem B301063 : Blo 299831 301063 := bstep (se 1 (by rfl) ⟨225797, by rfl⟩ : syracuseStep 301063 = 451595) B451595
theorem B301071 : Blo 299831 301071 := bstep (se 1 (by rfl) ⟨225803, by rfl⟩ : syracuseStep 301071 = 451607) B451607
theorem B759851 : Blo 299831 759851 := bstep (se 1 (by rfl) ⟨569888, by rfl⟩ : syracuseStep 759851 = 1139777) B1139777
theorem B301115 : Blo 299831 301115 := bstep (se 1 (by rfl) ⟨225836, by rfl⟩ : syracuseStep 301115 = 451673) B451673
theorem B301191 : Blo 299831 301191 := bstep (se 1 (by rfl) ⟨225893, by rfl⟩ : syracuseStep 301191 = 451787) B451787
theorem B432263 : Blo 299831 432263 := bstep (se 1 (by rfl) ⟨324197, by rfl⟩ : syracuseStep 432263 = 648395) B648395
theorem B301199 : Blo 299831 301199 := bstep (se 1 (by rfl) ⟨225899, by rfl⟩ : syracuseStep 301199 = 451799) B451799
theorem B301243 : Blo 299831 301243 := bstep (se 1 (by rfl) ⟨225932, by rfl⟩ : syracuseStep 301243 = 451865) B451865
theorem B301319 : Blo 299831 301319 := bstep (se 1 (by rfl) ⟨225989, by rfl⟩ : syracuseStep 301319 = 451979) B451979
theorem B301327 : Blo 299831 301327 := bstep (se 1 (by rfl) ⟨225995, by rfl⟩ : syracuseStep 301327 = 451991) B451991
theorem B3873041 : Blo 299831 3873041 := bstep (se 2 (by rfl) ⟨1452390, by rfl⟩ : syracuseStep 3873041 = 2904781) B2904781
theorem B1710395 : Blo 299831 1710395 := bstep (se 1 (by rfl) ⟨1282796, by rfl⟩ : syracuseStep 1710395 = 2565593) B2565593
theorem B301371 : Blo 299831 301371 := bstep (se 1 (by rfl) ⟨226028, by rfl⟩ : syracuseStep 301371 = 452057) B452057
theorem B301447 : Blo 299831 301447 := bstep (se 1 (by rfl) ⟨226085, by rfl⟩ : syracuseStep 301447 = 452171) B452171
theorem B301455 : Blo 299831 301455 := bstep (se 1 (by rfl) ⟨226091, by rfl⟩ : syracuseStep 301455 = 452183) B452183
theorem B301499 : Blo 299831 301499 := bstep (se 1 (by rfl) ⟨226124, by rfl⟩ : syracuseStep 301499 = 452249) B452249
theorem B2202065 : Blo 299831 2202065 := bstep (se 2 (by rfl) ⟨825774, by rfl⟩ : syracuseStep 2202065 = 1651549) B1651549
theorem B301575 : Blo 299831 301575 := bstep (se 1 (by rfl) ⟨226181, by rfl⟩ : syracuseStep 301575 = 452363) B452363
theorem B301583 : Blo 299831 301583 := bstep (se 1 (by rfl) ⟨226187, by rfl⟩ : syracuseStep 301583 = 452375) B452375
theorem B301627 : Blo 299831 301627 := bstep (se 1 (by rfl) ⟨226220, by rfl⟩ : syracuseStep 301627 = 452441) B452441
theorem B301703 : Blo 299831 301703 := bstep (se 1 (by rfl) ⟨226277, by rfl⟩ : syracuseStep 301703 = 452555) B452555
theorem B301711 : Blo 299831 301711 := bstep (se 1 (by rfl) ⟨226283, by rfl⟩ : syracuseStep 301711 = 452567) B452567
theorem B301755 : Blo 299831 301755 := bstep (se 1 (by rfl) ⟨226316, by rfl⟩ : syracuseStep 301755 = 452633) B452633
theorem B301831 : Blo 299831 301831 := bstep (se 1 (by rfl) ⟨226373, by rfl⟩ : syracuseStep 301831 = 452747) B452747
theorem B301839 : Blo 299831 301839 := bstep (se 1 (by rfl) ⟨226379, by rfl⟩ : syracuseStep 301839 = 452759) B452759
theorem B2300723 : Blo 299831 2300723 := bstep (se 1 (by rfl) ⟨1725542, by rfl⟩ : syracuseStep 2300723 = 3451085) B3451085
theorem B301883 : Blo 299831 301883 := bstep (se 1 (by rfl) ⟨226412, by rfl⟩ : syracuseStep 301883 = 452825) B452825
theorem B760691 : Blo 299831 760691 := bstep (se 1 (by rfl) ⟨570518, by rfl⟩ : syracuseStep 760691 = 1141037) B1141037
theorem B760711 : Blo 299831 760711 := bstep (se 1 (by rfl) ⟨570533, by rfl⟩ : syracuseStep 760711 = 1141067) B1141067
theorem B301959 : Blo 299831 301959 := bstep (se 1 (by rfl) ⟨226469, by rfl⟩ : syracuseStep 301959 = 452939) B452939
theorem B301967 : Blo 299831 301967 := bstep (se 1 (by rfl) ⟨226475, by rfl⟩ : syracuseStep 301967 = 452951) B452951
theorem B1022867 : Blo 299831 1022867 := bstep (se 1 (by rfl) ⟨767150, by rfl⟩ : syracuseStep 1022867 = 1534301) B1534301
theorem B302011 : Blo 299831 302011 := bstep (se 1 (by rfl) ⟨226508, by rfl⟩ : syracuseStep 302011 = 453017) B453017
theorem B859081 : Blo 299831 859081 := bstep (se 2 (by rfl) ⟨322155, by rfl⟩ : syracuseStep 859081 = 644311) B644311
theorem B302087 : Blo 299831 302087 := bstep (se 1 (by rfl) ⟨226565, by rfl⟩ : syracuseStep 302087 = 453131) B453131
theorem B302095 : Blo 299831 302095 := bstep (se 1 (by rfl) ⟨226571, by rfl⟩ : syracuseStep 302095 = 453143) B453143
theorem B302139 : Blo 299831 302139 := bstep (se 1 (by rfl) ⟨226604, by rfl⟩ : syracuseStep 302139 = 453209) B453209
theorem B302215 : Blo 299831 302215 := bstep (se 1 (by rfl) ⟨226661, by rfl⟩ : syracuseStep 302215 = 453323) B453323
theorem B302223 : Blo 299831 302223 := bstep (se 1 (by rfl) ⟨226667, by rfl⟩ : syracuseStep 302223 = 453335) B453335
theorem B760985 : Blo 299831 760985 := bstep (se 2 (by rfl) ⟨285369, by rfl⟩ : syracuseStep 760985 = 570739) B570739
theorem B302267 : Blo 299831 302267 := bstep (se 1 (by rfl) ⟨226700, by rfl⟩ : syracuseStep 302267 = 453401) B453401
theorem B302343 : Blo 299831 302343 := bstep (se 1 (by rfl) ⟨226757, by rfl⟩ : syracuseStep 302343 = 453515) B453515
theorem B302351 : Blo 299831 302351 := bstep (se 1 (by rfl) ⟨226763, by rfl⟩ : syracuseStep 302351 = 453527) B453527
theorem B1285409 : Blo 299831 1285409 := bstep (se 2 (by rfl) ⟨482028, by rfl⟩ : syracuseStep 1285409 = 964057) B964057
theorem B761147 : Blo 299831 761147 := bstep (se 1 (by rfl) ⟨570860, by rfl⟩ : syracuseStep 761147 = 1141721) B1141721
theorem B302395 : Blo 299831 302395 := bstep (se 1 (by rfl) ⟨226796, by rfl⟩ : syracuseStep 302395 = 453593) B453593
theorem B302471 : Blo 299831 302471 := bstep (se 1 (by rfl) ⟨226853, by rfl⟩ : syracuseStep 302471 = 453707) B453707
theorem B302479 : Blo 299831 302479 := bstep (se 1 (by rfl) ⟨226859, by rfl⟩ : syracuseStep 302479 = 453719) B453719
theorem B302523 : Blo 299831 302523 := bstep (se 1 (by rfl) ⟨226892, by rfl⟩ : syracuseStep 302523 = 453785) B453785
theorem B4660739 : Blo 299831 4660739 := bstep (se 1 (by rfl) ⟨3495554, by rfl⟩ : syracuseStep 4660739 = 6991109) B6991109
theorem B302599 : Blo 299831 302599 := bstep (se 1 (by rfl) ⟨226949, by rfl⟩ : syracuseStep 302599 = 453899) B453899
theorem B761359 : Blo 299831 761359 := bstep (se 1 (by rfl) ⟨571019, by rfl⟩ : syracuseStep 761359 = 1142039) B1142039
theorem B302607 : Blo 299831 302607 := bstep (se 1 (by rfl) ⟨226955, by rfl⟩ : syracuseStep 302607 = 453911) B453911
theorem B302651 : Blo 299831 302651 := bstep (se 1 (by rfl) ⟨226988, by rfl⟩ : syracuseStep 302651 = 453977) B453977
theorem B302727 : Blo 299831 302727 := bstep (se 1 (by rfl) ⟨227045, by rfl⟩ : syracuseStep 302727 = 454091) B454091
theorem B302735 : Blo 299831 302735 := bstep (se 1 (by rfl) ⟨227051, by rfl⟩ : syracuseStep 302735 = 454103) B454103
theorem B302779 : Blo 299831 302779 := bstep (se 1 (by rfl) ⟨227084, by rfl⟩ : syracuseStep 302779 = 454169) B454169
theorem B1711853 : Blo 299831 1711853 := bstep (se 3 (by rfl) ⟨320972, by rfl⟩ : syracuseStep 1711853 = 641945) B641945
theorem B1089281 : Blo 299831 1089281 := bstep (se 2 (by rfl) ⟨408480, by rfl⟩ : syracuseStep 1089281 = 816961) B816961
theorem B302855 : Blo 299831 302855 := bstep (se 1 (by rfl) ⟨227141, by rfl⟩ : syracuseStep 302855 = 454283) B454283
theorem B302863 : Blo 299831 302863 := bstep (se 1 (by rfl) ⟨227147, by rfl⟩ : syracuseStep 302863 = 454295) B454295
theorem B761633 : Blo 299831 761633 := bstep (se 2 (by rfl) ⟨285612, by rfl⟩ : syracuseStep 761633 = 571225) B571225
theorem B302907 : Blo 299831 302907 := bstep (se 1 (by rfl) ⟨227180, by rfl⟩ : syracuseStep 302907 = 454361) B454361
theorem B302983 : Blo 299831 302983 := bstep (se 1 (by rfl) ⟨227237, by rfl⟩ : syracuseStep 302983 = 454475) B454475
theorem B302991 : Blo 299831 302991 := bstep (se 1 (by rfl) ⟨227243, by rfl⟩ : syracuseStep 302991 = 454487) B454487
theorem B1449913 : Blo 299831 1449913 := bstep (se 2 (by rfl) ⟨543717, by rfl⟩ : syracuseStep 1449913 = 1087435) B1087435
theorem B303035 : Blo 299831 303035 := bstep (se 1 (by rfl) ⟨227276, by rfl⟩ : syracuseStep 303035 = 454553) B454553
theorem B303111 : Blo 299831 303111 := bstep (se 1 (by rfl) ⟨227333, by rfl⟩ : syracuseStep 303111 = 454667) B454667
theorem B303119 : Blo 299831 303119 := bstep (se 1 (by rfl) ⟨227339, by rfl⟩ : syracuseStep 303119 = 454679) B454679
theorem B303163 : Blo 299831 303163 := bstep (se 1 (by rfl) ⟨227372, by rfl⟩ : syracuseStep 303163 = 454745) B454745
theorem B303239 : Blo 299831 303239 := bstep (se 1 (by rfl) ⟨227429, by rfl⟩ : syracuseStep 303239 = 454859) B454859
theorem B303247 : Blo 299831 303247 := bstep (se 1 (by rfl) ⟨227435, by rfl⟩ : syracuseStep 303247 = 454871) B454871
theorem B303291 : Blo 299831 303291 := bstep (se 1 (by rfl) ⟨227468, by rfl⟩ : syracuseStep 303291 = 454937) B454937
theorem B1286401 : Blo 299831 1286401 := bstep (se 2 (by rfl) ⟨482400, by rfl⟩ : syracuseStep 1286401 = 964801) B964801
theorem B303367 : Blo 299831 303367 := bstep (se 1 (by rfl) ⟨227525, by rfl⟩ : syracuseStep 303367 = 455051) B455051
theorem B303375 : Blo 299831 303375 := bstep (se 1 (by rfl) ⟨227531, by rfl⟩ : syracuseStep 303375 = 455063) B455063
theorem B1024271 : Blo 299831 1024271 := bstep (se 1 (by rfl) ⟨768203, by rfl⟩ : syracuseStep 1024271 = 1536407) B1536407
theorem B303419 : Blo 299831 303419 := bstep (se 1 (by rfl) ⟨227564, by rfl⟩ : syracuseStep 303419 = 455129) B455129
theorem B303495 : Blo 299831 303495 := bstep (se 1 (by rfl) ⟨227621, by rfl⟩ : syracuseStep 303495 = 455243) B455243
theorem B303503 : Blo 299831 303503 := bstep (se 1 (by rfl) ⟨227627, by rfl⟩ : syracuseStep 303503 = 455255) B455255
theorem B303547 : Blo 299831 303547 := bstep (se 1 (by rfl) ⟨227660, by rfl⟩ : syracuseStep 303547 = 455321) B455321
theorem B303623 : Blo 299831 303623 := bstep (se 1 (by rfl) ⟨227717, by rfl⟩ : syracuseStep 303623 = 455435) B455435
theorem B303631 : Blo 299831 303631 := bstep (se 1 (by rfl) ⟨227723, by rfl⟩ : syracuseStep 303631 = 455447) B455447
theorem B1024541 : Blo 299831 1024541 := bstep (se 3 (by rfl) ⟨192101, by rfl⟩ : syracuseStep 1024541 = 384203) B384203
theorem B303675 : Blo 299831 303675 := bstep (se 1 (by rfl) ⟨227756, by rfl⟩ : syracuseStep 303675 = 455513) B455513
theorem B303751 : Blo 299831 303751 := bstep (se 1 (by rfl) ⟨227813, by rfl⟩ : syracuseStep 303751 = 455627) B455627
theorem B303759 : Blo 299831 303759 := bstep (se 1 (by rfl) ⟨227819, by rfl⟩ : syracuseStep 303759 = 455639) B455639
theorem B303803 : Blo 299831 303803 := bstep (se 1 (by rfl) ⟨227852, by rfl⟩ : syracuseStep 303803 = 455705) B455705
theorem B762635 : Blo 299831 762635 := bstep (se 1 (by rfl) ⟨571976, by rfl⟩ : syracuseStep 762635 = 1143953) B1143953
theorem B860939 : Blo 299831 860939 := bstep (se 1 (by rfl) ⟨645704, by rfl⟩ : syracuseStep 860939 = 1291409) B1291409
theorem B1844461 : Blo 299831 1844461 := bstep (se 3 (by rfl) ⟨345836, by rfl⟩ : syracuseStep 1844461 = 691673) B691673
theorem B763283 : Blo 299831 763283 := bstep (se 1 (by rfl) ⟨572462, by rfl⟩ : syracuseStep 763283 = 1144925) B1144925
theorem B861587 : Blo 299831 861587 := bstep (se 1 (by rfl) ⟨646190, by rfl⟩ : syracuseStep 861587 = 1292381) B1292381
theorem B337423 : Blo 299831 337423 := bstep (se 1 (by rfl) ⟨253067, by rfl⟩ : syracuseStep 337423 = 506135) B506135
theorem B22029893 : Blo 299831 22029893 := bstep (se 4 (by rfl) ⟨2065302, by rfl⟩ : syracuseStep 22029893 = 4130605) B4130605
theorem B861815 : Blo 299831 861815 := bstep (se 1 (by rfl) ⟨646361, by rfl⟩ : syracuseStep 861815 = 1292723) B1292723
theorem B763577 : Blo 299831 763577 := bstep (se 2 (by rfl) ⟨286341, by rfl⟩ : syracuseStep 763577 = 572683) B572683
theorem B2074369 : Blo 299831 2074369 := bstep (se 2 (by rfl) ⟨777888, by rfl⟩ : syracuseStep 2074369 = 1555777) B1555777
theorem B337927 : Blo 299831 337927 := bstep (se 1 (by rfl) ⟨253445, by rfl⟩ : syracuseStep 337927 = 506891) B506891
theorem B1222667 : Blo 299831 1222667 := bstep (se 1 (by rfl) ⟨917000, by rfl⟩ : syracuseStep 1222667 = 1834001) B1834001
theorem B1714243 : Blo 299831 1714243 := bstep (se 1 (by rfl) ⟨1285682, by rfl⟩ : syracuseStep 1714243 = 2571365) B2571365
theorem B960599 : Blo 299831 960599 := bstep (se 1 (by rfl) ⟨720449, by rfl⟩ : syracuseStep 960599 = 1440899) B1440899
theorem B338107 : Blo 299831 338107 := bstep (se 1 (by rfl) ⟨253580, by rfl⟩ : syracuseStep 338107 = 507161) B507161
theorem B1517939 : Blo 299831 1517939 := bstep (se 1 (by rfl) ⟨1138454, by rfl⟩ : syracuseStep 1517939 = 2276909) B2276909
theorem B764275 : Blo 299831 764275 := bstep (se 1 (by rfl) ⟨573206, by rfl⟩ : syracuseStep 764275 = 1146413) B1146413
theorem B764417 : Blo 299831 764417 := bstep (se 2 (by rfl) ⟨286656, by rfl⟩ : syracuseStep 764417 = 573313) B573313
theorem B1944107 : Blo 299831 1944107 := bstep (se 1 (by rfl) ⟨1458080, by rfl⟩ : syracuseStep 1944107 = 2916161) B2916161
theorem B961085 : Blo 299831 961085 := bstep (se 3 (by rfl) ⟨180203, by rfl⟩ : syracuseStep 961085 = 360407) B360407
theorem B338575 : Blo 299831 338575 := bstep (se 1 (by rfl) ⟨253931, by rfl⟩ : syracuseStep 338575 = 507863) B507863
theorem B1518425 : Blo 299831 1518425 := bstep (se 2 (by rfl) ⟨569409, by rfl⟩ : syracuseStep 1518425 = 1138819) B1138819
theorem B764873 : Blo 299831 764873 := bstep (se 2 (by rfl) ⟨286827, by rfl⟩ : syracuseStep 764873 = 573655) B573655
theorem B1453085 : Blo 299831 1453085 := bstep (se 3 (by rfl) ⟨272453, by rfl⟩ : syracuseStep 1453085 = 544907) B544907
theorem B339079 : Blo 299831 339079 := bstep (se 1 (by rfl) ⟨254309, by rfl⟩ : syracuseStep 339079 = 508619) B508619
theorem B765227 : Blo 299831 765227 := bstep (se 1 (by rfl) ⟨573920, by rfl⟩ : syracuseStep 765227 = 1147841) B1147841
theorem B339259 : Blo 299831 339259 := bstep (se 1 (by rfl) ⟨254444, by rfl⟩ : syracuseStep 339259 = 508889) B508889
theorem B2436637 : Blo 299831 2436637 := bstep (se 3 (by rfl) ⟨456869, by rfl⟩ : syracuseStep 2436637 = 913739) B913739
theorem B339727 : Blo 299831 339727 := bstep (se 1 (by rfl) ⟨254795, by rfl⟩ : syracuseStep 339727 = 509591) B509591
theorem B3092377 : Blo 299831 3092377 := bstep (se 2 (by rfl) ⟨1159641, by rfl⟩ : syracuseStep 3092377 = 2319283) B2319283
theorem B25472945 : Blo 299831 25472945 := bstep (se 2 (by rfl) ⟨9552354, by rfl⟩ : syracuseStep 25472945 = 19104709) B19104709
theorem B1716227 : Blo 299831 1716227 := bstep (se 1 (by rfl) ⟨1287170, by rfl⟩ : syracuseStep 1716227 = 2574341) B2574341
theorem B340231 : Blo 299831 340231 := bstep (se 1 (by rfl) ⟨255173, by rfl⟩ : syracuseStep 340231 = 510347) B510347
theorem B766219 : Blo 299831 766219 := bstep (se 1 (by rfl) ⟨574664, by rfl⟩ : syracuseStep 766219 = 1149329) B1149329
theorem B766361 : Blo 299831 766361 := bstep (se 2 (by rfl) ⟨287385, by rfl⟩ : syracuseStep 766361 = 574771) B574771
theorem B340411 : Blo 299831 340411 := bstep (se 1 (by rfl) ⟨255308, by rfl⟩ : syracuseStep 340411 = 510617) B510617
theorem B766523 : Blo 299831 766523 := bstep (se 1 (by rfl) ⟨574892, by rfl⟩ : syracuseStep 766523 = 1149785) B1149785
theorem B865039 : Blo 299831 865039 := bstep (se 1 (by rfl) ⟨648779, by rfl⟩ : syracuseStep 865039 = 1297559) B1297559
theorem B340879 : Blo 299831 340879 := bstep (se 1 (by rfl) ⟨255659, by rfl⟩ : syracuseStep 340879 = 511319) B511319
theorem B1520531 : Blo 299831 1520531 := bstep (se 1 (by rfl) ⟨1140398, by rfl⟩ : syracuseStep 1520531 = 2280797) B2280797
theorem B766867 : Blo 299831 766867 := bstep (se 1 (by rfl) ⟨575150, by rfl⟩ : syracuseStep 766867 = 1150301) B1150301
theorem B1553431 : Blo 299831 1553431 := bstep (se 1 (by rfl) ⟨1165073, by rfl⟩ : syracuseStep 1553431 = 2330147) B2330147
theorem B767009 : Blo 299831 767009 := bstep (se 2 (by rfl) ⟨287628, by rfl⟩ : syracuseStep 767009 = 575257) B575257
theorem B570503 : Blo 299831 570503 := bstep (se 1 (by rfl) ⟨427877, by rfl⟩ : syracuseStep 570503 = 855755) B855755
theorem B341383 : Blo 299831 341383 := bstep (se 1 (by rfl) ⟨256037, by rfl⟩ : syracuseStep 341383 = 512075) B512075
theorem B341563 : Blo 299831 341563 := bstep (se 1 (by rfl) ⟨256172, by rfl⟩ : syracuseStep 341563 = 512345) B512345
theorem B3421925 : Blo 299831 3421925 := bstep (se 4 (by rfl) ⟨320805, by rfl⟩ : syracuseStep 3421925 = 641611) B641611
theorem B768001 : Blo 299831 768001 := bstep (se 2 (by rfl) ⟨288000, by rfl⟩ : syracuseStep 768001 = 576001) B576001
theorem B1226819 : Blo 299831 1226819 := bstep (se 1 (by rfl) ⟨920114, by rfl⟩ : syracuseStep 1226819 = 1840229) B1840229
theorem B506155 : Blo 299831 506155 := bstep (se 1 (by rfl) ⟨379616, by rfl⟩ : syracuseStep 506155 = 759233) B759233
theorem B26589505 : Blo 299831 26589505 := bstep (se 2 (by rfl) ⟨9971064, by rfl⟩ : syracuseStep 26589505 = 19942129) B19942129
theorem B1718617 : Blo 299831 1718617 := bstep (se 2 (by rfl) ⟨644481, by rfl⟩ : syracuseStep 1718617 = 1288963) B1288963
theorem B342407 : Blo 299831 342407 := bstep (se 1 (by rfl) ⟨256805, by rfl⟩ : syracuseStep 342407 = 513611) B513611
theorem B506297 : Blo 299831 506297 := bstep (se 2 (by rfl) ⟨189861, by rfl⟩ : syracuseStep 506297 = 379723) B379723
theorem B4143581 : Blo 299831 4143581 := bstep (se 3 (by rfl) ⟨776921, by rfl⟩ : syracuseStep 4143581 = 1553843) B1553843
theorem B768599 : Blo 299831 768599 := bstep (se 1 (by rfl) ⟨576449, by rfl⟩ : syracuseStep 768599 = 1152899) B1152899
theorem B768811 : Blo 299831 768811 := bstep (se 1 (by rfl) ⟨576608, by rfl⟩ : syracuseStep 768811 = 1153217) B1153217
theorem B3652427 : Blo 299831 3652427 := bstep (se 1 (by rfl) ⟨2739320, by rfl⟩ : syracuseStep 3652427 = 5478641) B5478641
theorem B768953 : Blo 299831 768953 := bstep (se 2 (by rfl) ⟨288357, by rfl⟩ : syracuseStep 768953 = 576715) B576715
theorem B6929495 : Blo 299831 6929495 := bstep (se 1 (by rfl) ⟨5197121, by rfl⟩ : syracuseStep 6929495 = 10394243) B10394243
theorem B506999 : Blo 299831 506999 := bstep (se 1 (by rfl) ⟨380249, by rfl⟩ : syracuseStep 506999 = 760499) B760499
theorem B507451 : Blo 299831 507451 := bstep (se 1 (by rfl) ⟨380588, by rfl⟩ : syracuseStep 507451 = 761177) B761177
theorem B572987 : Blo 299831 572987 := bstep (se 1 (by rfl) ⟨429740, by rfl⟩ : syracuseStep 572987 = 859481) B859481
theorem B769655 : Blo 299831 769655 := bstep (se 1 (by rfl) ⟨577241, by rfl⟩ : syracuseStep 769655 = 1154483) B1154483
theorem B507593 : Blo 299831 507593 := bstep (se 2 (by rfl) ⟨190347, by rfl⟩ : syracuseStep 507593 = 380695) B380695
theorem B1523609 : Blo 299831 1523609 := bstep (se 2 (by rfl) ⟨571353, by rfl⟩ : syracuseStep 1523609 = 1142707) B1142707
theorem B1720349 : Blo 299831 1720349 := bstep (se 3 (by rfl) ⟨322565, by rfl⟩ : syracuseStep 1720349 = 645131) B645131
theorem B573473 : Blo 299831 573473 := bstep (se 2 (by rfl) ⟨215052, by rfl⟩ : syracuseStep 573473 = 430105) B430105
theorem B966775 : Blo 299831 966775 := bstep (se 1 (by rfl) ⟨725081, by rfl⟩ : syracuseStep 966775 = 1450163) B1450163
theorem B6209777 : Blo 299831 6209777 := bstep (se 2 (by rfl) ⟨2328666, by rfl⟩ : syracuseStep 6209777 = 4657333) B4657333
theorem B1229089 : Blo 299831 1229089 := bstep (se 2 (by rfl) ⟨460908, by rfl⟩ : syracuseStep 1229089 = 921817) B921817
theorem B508295 : Blo 299831 508295 := bstep (se 1 (by rfl) ⟨381221, by rfl⟩ : syracuseStep 508295 = 762443) B762443
theorem B541129 : Blo 299831 541129 := bstep (se 2 (by rfl) ⟨202923, by rfl⟩ : syracuseStep 541129 = 405847) B405847
theorem B541217 : Blo 299831 541217 := bstep (se 2 (by rfl) ⟨202956, by rfl⟩ : syracuseStep 541217 = 405913) B405913
theorem B1721033 : Blo 299831 1721033 := bstep (se 2 (by rfl) ⟨645387, by rfl⟩ : syracuseStep 1721033 = 1290775) B1290775
theorem B6505231 : Blo 299831 6505231 := bstep (se 1 (by rfl) ⟨4878923, by rfl⟩ : syracuseStep 6505231 = 9757847) B9757847
theorem B508943 : Blo 299831 508943 := bstep (se 1 (by rfl) ⟨381707, by rfl⟩ : syracuseStep 508943 = 763415) B763415
theorem B1656065 : Blo 299831 1656065 := bstep (se 2 (by rfl) ⟨621024, by rfl⟩ : syracuseStep 1656065 = 1242049) B1242049
theorem B1558027 : Blo 299831 1558027 := bstep (se 1 (by rfl) ⟨1168520, by rfl⟩ : syracuseStep 1558027 = 2337041) B2337041
theorem B509483 : Blo 299831 509483 := bstep (se 1 (by rfl) ⟨382112, by rfl⟩ : syracuseStep 509483 = 764225) B764225
theorem B3688001 : Blo 299831 3688001 := bstep (se 2 (by rfl) ⟨1383000, by rfl⟩ : syracuseStep 3688001 = 2766001) B2766001
theorem B37045835 : Blo 299831 37045835 := bstep (se 1 (by rfl) ⟨27784376, by rfl⟩ : syracuseStep 37045835 = 55568753) B55568753
theorem B771731 : Blo 299831 771731 := bstep (se 1 (by rfl) ⟨578798, by rfl⟩ : syracuseStep 771731 = 1157597) B1157597
theorem B4638617 : Blo 299831 4638617 := bstep (se 2 (by rfl) ⟨1739481, by rfl⟩ : syracuseStep 4638617 = 3478963) B3478963
theorem B2738083 : Blo 299831 2738083 := bstep (se 1 (by rfl) ⟨2053562, by rfl⟩ : syracuseStep 2738083 = 4107125) B4107125
theorem B509881 : Blo 299831 509881 := bstep (se 2 (by rfl) ⟨191205, by rfl⟩ : syracuseStep 509881 = 382411) B382411
theorem B575417 : Blo 299831 575417 := bstep (se 2 (by rfl) ⟨215781, by rfl⟩ : syracuseStep 575417 = 431563) B431563
theorem B1296755 : Blo 299831 1296755 := bstep (se 1 (by rfl) ⟨972566, by rfl⟩ : syracuseStep 1296755 = 1945133) B1945133
theorem B2279825 : Blo 299831 2279825 := bstep (se 2 (by rfl) ⟨854934, by rfl⟩ : syracuseStep 2279825 = 1709869) B1709869
theorem B1526201 : Blo 299831 1526201 := bstep (se 2 (by rfl) ⟨572325, by rfl⟩ : syracuseStep 1526201 = 1144651) B1144651
theorem B1722809 : Blo 299831 1722809 := bstep (se 2 (by rfl) ⟨646053, by rfl⟩ : syracuseStep 1722809 = 1292107) B1292107
theorem B510583 : Blo 299831 510583 := bstep (se 1 (by rfl) ⟨382937, by rfl⟩ : syracuseStep 510583 = 765875) B765875
theorem B1297097 : Blo 299831 1297097 := bstep (se 2 (by rfl) ⟨486411, by rfl⟩ : syracuseStep 1297097 = 972823) B972823
theorem B510779 : Blo 299831 510779 := bstep (se 1 (by rfl) ⟨383084, by rfl⟩ : syracuseStep 510779 = 766169) B766169
theorem B379819 : Blo 299831 379819 := bstep (se 1 (by rfl) ⟨284864, by rfl⟩ : syracuseStep 379819 = 569729) B569729
theorem B642107 : Blo 299831 642107 := bstep (se 1 (by rfl) ⟨481580, by rfl⟩ : syracuseStep 642107 = 963161) B963161
theorem B576571 : Blo 299831 576571 := bstep (se 1 (by rfl) ⟨432428, by rfl⟩ : syracuseStep 576571 = 864857) B864857
theorem B2182277 : Blo 299831 2182277 := bstep (se 4 (by rfl) ⟨204588, by rfl⟩ : syracuseStep 2182277 = 409177) B409177
theorem B380047 : Blo 299831 380047 := bstep (se 1 (by rfl) ⟨285035, by rfl⟩ : syracuseStep 380047 = 570071) B570071
theorem B674963 : Blo 299831 674963 := bstep (se 1 (by rfl) ⟨506222, by rfl⟩ : syracuseStep 674963 = 1012445) B1012445
theorem B773267 : Blo 299831 773267 := bstep (se 1 (by rfl) ⟨579950, by rfl⟩ : syracuseStep 773267 = 1159901) B1159901
theorem B675017 : Blo 299831 675017 := bstep (se 2 (by rfl) ⟨253131, by rfl⟩ : syracuseStep 675017 = 506263) B506263
theorem B511177 : Blo 299831 511177 := bstep (se 2 (by rfl) ⟨191691, by rfl⟩ : syracuseStep 511177 = 383383) B383383
theorem B1756475 : Blo 299831 1756475 := bstep (se 1 (by rfl) ⟨1317356, by rfl⟩ : syracuseStep 1756475 = 2634713) B2634713
theorem B63688037 : Blo 299831 63688037 := bstep (se 4 (by rfl) ⟨5970753, by rfl⟩ : syracuseStep 63688037 = 11941507) B11941507
theorem B1527497 : Blo 299831 1527497 := bstep (se 2 (by rfl) ⟨572811, by rfl⟩ : syracuseStep 1527497 = 1145623) B1145623
theorem B380791 : Blo 299831 380791 := bstep (se 1 (by rfl) ⟨285593, by rfl⟩ : syracuseStep 380791 = 571187) B571187
theorem B675719 : Blo 299831 675719 := bstep (se 1 (by rfl) ⟨506789, by rfl⟩ : syracuseStep 675719 = 1013579) B1013579
theorem B511879 : Blo 299831 511879 := bstep (se 1 (by rfl) ⟨383909, by rfl⟩ : syracuseStep 511879 = 767819) B767819
theorem B643115 : Blo 299831 643115 := bstep (se 1 (by rfl) ⟨482336, by rfl⟩ : syracuseStep 643115 = 964673) B964673
theorem B675899 : Blo 299831 675899 := bstep (se 1 (by rfl) ⟨506924, by rfl⟩ : syracuseStep 675899 = 1013849) B1013849
theorem B676025 : Blo 299831 676025 := bstep (se 2 (by rfl) ⟨253509, by rfl⟩ : syracuseStep 676025 = 507019) B507019
theorem B381115 : Blo 299831 381115 := bstep (se 1 (by rfl) ⟨285836, by rfl⟩ : syracuseStep 381115 = 571673) B571673
theorem B1724723 : Blo 299831 1724723 := bstep (se 1 (by rfl) ⟨1293542, by rfl⟩ : syracuseStep 1724723 = 2587085) B2587085
theorem B676367 : Blo 299831 676367 := bstep (se 1 (by rfl) ⟨507275, by rfl⟩ : syracuseStep 676367 = 1014551) B1014551
theorem B512527 : Blo 299831 512527 := bstep (se 1 (by rfl) ⟨384395, by rfl⟩ : syracuseStep 512527 = 768791) B768791
theorem B676385 : Blo 299831 676385 := bstep (se 2 (by rfl) ⟨253644, by rfl⟩ : syracuseStep 676385 = 507289) B507289
theorem B545339 : Blo 299831 545339 := bstep (se 1 (by rfl) ⟨409004, by rfl⟩ : syracuseStep 545339 = 818009) B818009
theorem B381611 : Blo 299831 381611 := bstep (se 1 (by rfl) ⟨286208, by rfl⟩ : syracuseStep 381611 = 572417) B572417
theorem B4346561 : Blo 299831 4346561 := bstep (se 2 (by rfl) ⟨1629960, by rfl⟩ : syracuseStep 4346561 = 3259921) B3259921
theorem B2282255 : Blo 299831 2282255 := bstep (se 1 (by rfl) ⟨1711691, by rfl⟩ : syracuseStep 2282255 = 3423383) B3423383
theorem B676727 : Blo 299831 676727 := bstep (se 1 (by rfl) ⟨507545, by rfl⟩ : syracuseStep 676727 = 1015091) B1015091
theorem B545737 : Blo 299831 545737 := bstep (se 2 (by rfl) ⟨204651, by rfl⟩ : syracuseStep 545737 = 409303) B409303
theorem B676907 : Blo 299831 676907 := bstep (se 1 (by rfl) ⟨507680, by rfl⟩ : syracuseStep 676907 = 1015361) B1015361
theorem B382087 : Blo 299831 382087 := bstep (se 1 (by rfl) ⟨286565, by rfl⟩ : syracuseStep 382087 = 573131) B573131
theorem B677267 : Blo 299831 677267 := bstep (se 1 (by rfl) ⟨507950, by rfl⟩ : syracuseStep 677267 = 1015901) B1015901
theorem B677321 : Blo 299831 677321 := bstep (se 2 (by rfl) ⟨253995, by rfl⟩ : syracuseStep 677321 = 507991) B507991
theorem B382583 : Blo 299831 382583 := bstep (se 1 (by rfl) ⟨286937, by rfl⟩ : syracuseStep 382583 = 573875) B573875
theorem B644755 : Blo 299831 644755 := bstep (se 1 (by rfl) ⟨483566, by rfl⟩ : syracuseStep 644755 = 967133) B967133
theorem B480953 : Blo 299831 480953 := bstep (se 2 (by rfl) ⟨180357, by rfl⟩ : syracuseStep 480953 = 360715) B360715
theorem B1726181 : Blo 299831 1726181 := bstep (se 4 (by rfl) ⟨161829, by rfl⟩ : syracuseStep 1726181 = 323659) B323659
theorem B382735 : Blo 299831 382735 := bstep (se 1 (by rfl) ⟨287051, by rfl⟩ : syracuseStep 382735 = 574103) B574103
theorem B1628039 : Blo 299831 1628039 := bstep (se 1 (by rfl) ⟨1221029, by rfl⟩ : syracuseStep 1628039 = 2442059) B2442059
theorem B382907 : Blo 299831 382907 := bstep (se 1 (by rfl) ⟨287180, by rfl⟩ : syracuseStep 382907 = 574361) B574361
theorem B2185163 : Blo 299831 2185163 := bstep (se 1 (by rfl) ⟨1638872, by rfl⟩ : syracuseStep 2185163 = 3277745) B3277745
theorem B1038347 : Blo 299831 1038347 := bstep (se 1 (by rfl) ⟨778760, by rfl⟩ : syracuseStep 1038347 = 1557521) B1557521
theorem B678023 : Blo 299831 678023 := bstep (se 1 (by rfl) ⟨508517, by rfl⟩ : syracuseStep 678023 = 1017035) B1017035
theorem B481465 : Blo 299831 481465 := bstep (se 2 (by rfl) ⟨180549, by rfl⟩ : syracuseStep 481465 = 361099) B361099
theorem B3430673 : Blo 299831 3430673 := bstep (se 2 (by rfl) ⟨1286502, by rfl⟩ : syracuseStep 3430673 = 2573005) B2573005
theorem B514363 : Blo 299831 514363 := bstep (se 1 (by rfl) ⟨385772, by rfl⟩ : syracuseStep 514363 = 771545) B771545
theorem B678203 : Blo 299831 678203 := bstep (se 1 (by rfl) ⟨508652, by rfl⟩ : syracuseStep 678203 = 1017305) B1017305
theorem B1726865 : Blo 299831 1726865 := bstep (se 2 (by rfl) ⟨647574, by rfl⟩ : syracuseStep 1726865 = 1295149) B1295149
theorem B481721 : Blo 299831 481721 := bstep (se 2 (by rfl) ⟨180645, by rfl⟩ : syracuseStep 481721 = 361291) B361291
theorem B678329 : Blo 299831 678329 := bstep (se 2 (by rfl) ⟨254373, by rfl⟩ : syracuseStep 678329 = 508747) B508747
theorem B612793 : Blo 299831 612793 := bstep (se 2 (by rfl) ⟨229797, by rfl⟩ : syracuseStep 612793 = 459595) B459595
theorem B678671 : Blo 299831 678671 := bstep (se 1 (by rfl) ⟨509003, by rfl⟩ : syracuseStep 678671 = 1018007) B1018007
theorem B678689 : Blo 299831 678689 := bstep (se 2 (by rfl) ⟨254508, by rfl⟩ : syracuseStep 678689 = 509017) B509017
theorem B482183 : Blo 299831 482183 := bstep (se 1 (by rfl) ⟨361637, by rfl⟩ : syracuseStep 482183 = 723275) B723275
theorem B383879 : Blo 299831 383879 := bstep (se 1 (by rfl) ⟨287909, by rfl⟩ : syracuseStep 383879 = 575819) B575819
theorem B2579363 : Blo 299831 2579363 := bstep (se 1 (by rfl) ⟨1934522, by rfl⟩ : syracuseStep 2579363 = 3869045) B3869045
theorem B679031 : Blo 299831 679031 := bstep (se 1 (by rfl) ⟨509273, by rfl⟩ : syracuseStep 679031 = 1018547) B1018547
theorem B449783 : Blo 299831 449783 := bstep (se 1 (by rfl) ⟨337337, by rfl⟩ : syracuseStep 449783 = 674675) B674675
theorem B449807 : Blo 299831 449807 := bstep (se 1 (by rfl) ⟨337355, by rfl⟩ : syracuseStep 449807 = 674711) B674711
theorem B679211 : Blo 299831 679211 := bstep (se 1 (by rfl) ⟨509408, by rfl⟩ : syracuseStep 679211 = 1018817) B1018817
theorem B449849 : Blo 299831 449849 := bstep (se 2 (by rfl) ⟨168693, by rfl⟩ : syracuseStep 449849 = 337387) B337387
theorem B3366203 : Blo 299831 3366203 := bstep (se 1 (by rfl) ⟨2524652, by rfl⟩ : syracuseStep 3366203 = 5049305) B5049305
theorem B941399 : Blo 299831 941399 := bstep (se 1 (by rfl) ⟨706049, by rfl⟩ : syracuseStep 941399 = 1412099) B1412099
theorem B875863 : Blo 299831 875863 := bstep (se 1 (by rfl) ⟨656897, by rfl⟩ : syracuseStep 875863 = 1313795) B1313795
theorem B3267971 : Blo 299831 3267971 := bstep (se 1 (by rfl) ⟨2450978, by rfl⟩ : syracuseStep 3267971 = 4901957) B4901957
theorem B449927 : Blo 299831 449927 := bstep (se 1 (by rfl) ⟨337445, by rfl⟩ : syracuseStep 449927 = 674891) B674891
theorem B1727891 : Blo 299831 1727891 := bstep (se 1 (by rfl) ⟨1295918, by rfl⟩ : syracuseStep 1727891 = 2591837) B2591837
theorem B449963 : Blo 299831 449963 := bstep (se 1 (by rfl) ⟨337472, by rfl⟩ : syracuseStep 449963 = 674945) B674945
theorem B449993 : Blo 299831 449993 := bstep (se 2 (by rfl) ⟨168747, by rfl⟩ : syracuseStep 449993 = 337495) B337495
theorem B384527 : Blo 299831 384527 := bstep (se 1 (by rfl) ⟨288395, by rfl⟩ : syracuseStep 384527 = 576791) B576791
theorem B450107 : Blo 299831 450107 := bstep (se 1 (by rfl) ⟨337580, by rfl⟩ : syracuseStep 450107 = 675161) B675161
theorem B450167 : Blo 299831 450167 := bstep (se 1 (by rfl) ⟨337625, by rfl⟩ : syracuseStep 450167 = 675251) B675251
theorem B450191 : Blo 299831 450191 := bstep (se 1 (by rfl) ⟨337643, by rfl⟩ : syracuseStep 450191 = 675287) B675287
theorem B679571 : Blo 299831 679571 := bstep (se 1 (by rfl) ⟨509678, by rfl⟩ : syracuseStep 679571 = 1019357) B1019357
theorem B450233 : Blo 299831 450233 := bstep (se 2 (by rfl) ⟨168837, by rfl⟩ : syracuseStep 450233 = 337675) B337675
theorem B679625 : Blo 299831 679625 := bstep (se 2 (by rfl) ⟨254859, by rfl⟩ : syracuseStep 679625 = 509719) B509719
theorem B450311 : Blo 299831 450311 := bstep (se 1 (by rfl) ⟨337733, by rfl⟩ : syracuseStep 450311 = 675467) B675467
theorem B450347 : Blo 299831 450347 := bstep (se 1 (by rfl) ⟨337760, by rfl⟩ : syracuseStep 450347 = 675521) B675521
theorem B483131 : Blo 299831 483131 := bstep (se 1 (by rfl) ⟨362348, by rfl⟩ : syracuseStep 483131 = 724697) B724697
theorem B450377 : Blo 299831 450377 := bstep (se 2 (by rfl) ⟨168891, by rfl⟩ : syracuseStep 450377 = 337783) B337783
theorem B450491 : Blo 299831 450491 := bstep (se 1 (by rfl) ⟨337868, by rfl⟩ : syracuseStep 450491 = 675737) B675737
theorem B450551 : Blo 299831 450551 := bstep (se 1 (by rfl) ⟨337913, by rfl⟩ : syracuseStep 450551 = 675827) B675827
theorem B450575 : Blo 299831 450575 := bstep (se 1 (by rfl) ⟨337931, by rfl⟩ : syracuseStep 450575 = 675863) B675863
theorem B450617 : Blo 299831 450617 := bstep (se 2 (by rfl) ⟨168981, by rfl⟩ : syracuseStep 450617 = 337963) B337963
theorem B450695 : Blo 299831 450695 := bstep (se 1 (by rfl) ⟨338021, by rfl⟩ : syracuseStep 450695 = 676043) B676043
theorem B450731 : Blo 299831 450731 := bstep (se 1 (by rfl) ⟨338048, by rfl⟩ : syracuseStep 450731 = 676097) B676097
theorem B450761 : Blo 299831 450761 := bstep (se 2 (by rfl) ⟨169035, by rfl⟩ : syracuseStep 450761 = 338071) B338071
theorem B450875 : Blo 299831 450875 := bstep (se 1 (by rfl) ⟨338156, by rfl⟩ : syracuseStep 450875 = 676313) B676313
theorem B450935 : Blo 299831 450935 := bstep (se 1 (by rfl) ⟨338201, by rfl⟩ : syracuseStep 450935 = 676403) B676403
theorem B680327 : Blo 299831 680327 := bstep (se 1 (by rfl) ⟨510245, by rfl⟩ : syracuseStep 680327 = 1020491) B1020491
theorem B450959 : Blo 299831 450959 := bstep (se 1 (by rfl) ⟨338219, by rfl⟩ : syracuseStep 450959 = 676439) B676439
theorem B451001 : Blo 299831 451001 := bstep (se 2 (by rfl) ⟨169125, by rfl⟩ : syracuseStep 451001 = 338251) B338251
theorem B451079 : Blo 299831 451079 := bstep (se 1 (by rfl) ⟨338309, by rfl⟩ : syracuseStep 451079 = 676619) B676619
theorem B451115 : Blo 299831 451115 := bstep (se 1 (by rfl) ⟨338336, by rfl⟩ : syracuseStep 451115 = 676673) B676673
theorem B680507 : Blo 299831 680507 := bstep (se 1 (by rfl) ⟨510380, by rfl⟩ : syracuseStep 680507 = 1020761) B1020761
theorem B451145 : Blo 299831 451145 := bstep (se 2 (by rfl) ⟨169179, by rfl⟩ : syracuseStep 451145 = 338359) B338359
theorem B1303127 : Blo 299831 1303127 := bstep (se 1 (by rfl) ⟨977345, by rfl⟩ : syracuseStep 1303127 = 1954691) B1954691
theorem B1368695 : Blo 299831 1368695 := bstep (se 1 (by rfl) ⟨1026521, by rfl⟩ : syracuseStep 1368695 = 2053043) B2053043
theorem B680633 : Blo 299831 680633 := bstep (se 2 (by rfl) ⟨255237, by rfl⟩ : syracuseStep 680633 = 510475) B510475
theorem B451259 : Blo 299831 451259 := bstep (se 1 (by rfl) ⟨338444, by rfl⟩ : syracuseStep 451259 = 676889) B676889
theorem B451319 : Blo 299831 451319 := bstep (se 1 (by rfl) ⟨338489, by rfl⟩ : syracuseStep 451319 = 676979) B676979
theorem B2745089 : Blo 299831 2745089 := bstep (se 2 (by rfl) ⟨1029408, by rfl⟩ : syracuseStep 2745089 = 2058817) B2058817
theorem B451343 : Blo 299831 451343 := bstep (se 1 (by rfl) ⟨338507, by rfl⟩ : syracuseStep 451343 = 677015) B677015
theorem B451385 : Blo 299831 451385 := bstep (se 2 (by rfl) ⟨169269, by rfl⟩ : syracuseStep 451385 = 338539) B338539
theorem B451463 : Blo 299831 451463 := bstep (se 1 (by rfl) ⟨338597, by rfl⟩ : syracuseStep 451463 = 677195) B677195
theorem B1139609 : Blo 299831 1139609 := bstep (se 2 (by rfl) ⟨427353, by rfl⟩ : syracuseStep 1139609 = 854707) B854707
theorem B451499 : Blo 299831 451499 := bstep (se 1 (by rfl) ⟨338624, by rfl⟩ : syracuseStep 451499 = 677249) B677249
theorem B451529 : Blo 299831 451529 := bstep (se 2 (by rfl) ⟨169323, by rfl⟩ : syracuseStep 451529 = 338647) B338647
theorem B386039 : Blo 299831 386039 := bstep (se 1 (by rfl) ⟨289529, by rfl⟩ : syracuseStep 386039 = 579059) B579059
theorem B680975 : Blo 299831 680975 := bstep (se 1 (by rfl) ⟨510731, by rfl⟩ : syracuseStep 680975 = 1021463) B1021463
theorem B680993 : Blo 299831 680993 := bstep (se 2 (by rfl) ⟨255372, by rfl⟩ : syracuseStep 680993 = 510745) B510745
theorem B451643 : Blo 299831 451643 := bstep (se 1 (by rfl) ⟨338732, by rfl⟩ : syracuseStep 451643 = 677465) B677465
theorem B3433589 : Blo 299831 3433589 := bstep (se 5 (by rfl) ⟨160949, by rfl⟩ : syracuseStep 3433589 = 321899) B321899
theorem B451703 : Blo 299831 451703 := bstep (se 1 (by rfl) ⟨338777, by rfl⟩ : syracuseStep 451703 = 677555) B677555
theorem B451727 : Blo 299831 451727 := bstep (se 1 (by rfl) ⟨338795, by rfl⟩ : syracuseStep 451727 = 677591) B677591
theorem B451769 : Blo 299831 451769 := bstep (se 2 (by rfl) ⟨169413, by rfl⟩ : syracuseStep 451769 = 338827) B338827
theorem B451847 : Blo 299831 451847 := bstep (se 1 (by rfl) ⟨338885, by rfl⟩ : syracuseStep 451847 = 677771) B677771
theorem B451883 : Blo 299831 451883 := bstep (se 1 (by rfl) ⟨338912, by rfl⟩ : syracuseStep 451883 = 677825) B677825
theorem B451913 : Blo 299831 451913 := bstep (se 2 (by rfl) ⟨169467, by rfl⟩ : syracuseStep 451913 = 338935) B338935
theorem B681335 : Blo 299831 681335 := bstep (se 1 (by rfl) ⟨511001, by rfl⟩ : syracuseStep 681335 = 1022003) B1022003
theorem B1533329 : Blo 299831 1533329 := bstep (se 2 (by rfl) ⟨574998, by rfl⟩ : syracuseStep 1533329 = 1149997) B1149997
theorem B452027 : Blo 299831 452027 := bstep (se 1 (by rfl) ⟨339020, by rfl⟩ : syracuseStep 452027 = 678041) B678041
theorem B452087 : Blo 299831 452087 := bstep (se 1 (by rfl) ⟨339065, by rfl⟩ : syracuseStep 452087 = 678131) B678131
theorem B452111 : Blo 299831 452111 := bstep (se 1 (by rfl) ⟨339083, by rfl⟩ : syracuseStep 452111 = 678167) B678167
theorem B681515 : Blo 299831 681515 := bstep (se 1 (by rfl) ⟨511136, by rfl⟩ : syracuseStep 681515 = 1022273) B1022273
theorem B452153 : Blo 299831 452153 := bstep (se 2 (by rfl) ⟨169557, by rfl⟩ : syracuseStep 452153 = 339115) B339115
theorem B452231 : Blo 299831 452231 := bstep (se 1 (by rfl) ⟨339173, by rfl⟩ : syracuseStep 452231 = 678347) B678347
theorem B452267 : Blo 299831 452267 := bstep (se 1 (by rfl) ⟨339200, by rfl⟩ : syracuseStep 452267 = 678401) B678401
theorem B452297 : Blo 299831 452297 := bstep (se 2 (by rfl) ⟨169611, by rfl⟩ : syracuseStep 452297 = 339223) B339223
theorem B452411 : Blo 299831 452411 := bstep (se 1 (by rfl) ⟨339308, by rfl⟩ : syracuseStep 452411 = 678617) B678617
theorem B452471 : Blo 299831 452471 := bstep (se 1 (by rfl) ⟨339353, by rfl⟩ : syracuseStep 452471 = 678707) B678707
theorem B452495 : Blo 299831 452495 := bstep (se 1 (by rfl) ⟨339371, by rfl⟩ : syracuseStep 452495 = 678743) B678743
theorem B681875 : Blo 299831 681875 := bstep (se 1 (by rfl) ⟨511406, by rfl⟩ : syracuseStep 681875 = 1022813) B1022813
theorem B452537 : Blo 299831 452537 := bstep (se 2 (by rfl) ⟨169701, by rfl⟩ : syracuseStep 452537 = 339403) B339403
theorem B681929 : Blo 299831 681929 := bstep (se 2 (by rfl) ⟨255723, by rfl⟩ : syracuseStep 681929 = 511447) B511447
theorem B452615 : Blo 299831 452615 := bstep (se 1 (by rfl) ⟨339461, by rfl⟩ : syracuseStep 452615 = 678923) B678923
theorem B452651 : Blo 299831 452651 := bstep (se 1 (by rfl) ⟨339488, by rfl⟩ : syracuseStep 452651 = 678977) B678977
theorem B452681 : Blo 299831 452681 := bstep (se 2 (by rfl) ⟨169755, by rfl⟩ : syracuseStep 452681 = 339511) B339511
theorem B452795 : Blo 299831 452795 := bstep (se 1 (by rfl) ⟨339596, by rfl⟩ : syracuseStep 452795 = 679193) B679193
theorem B452855 : Blo 299831 452855 := bstep (se 1 (by rfl) ⟨339641, by rfl⟩ : syracuseStep 452855 = 679283) B679283
theorem B452879 : Blo 299831 452879 := bstep (se 1 (by rfl) ⟨339659, by rfl⟩ : syracuseStep 452879 = 679319) B679319
theorem B452921 : Blo 299831 452921 := bstep (se 2 (by rfl) ⟨169845, by rfl⟩ : syracuseStep 452921 = 339691) B339691
theorem B452999 : Blo 299831 452999 := bstep (se 1 (by rfl) ⟨339749, by rfl⟩ : syracuseStep 452999 = 679499) B679499
theorem B453035 : Blo 299831 453035 := bstep (se 1 (by rfl) ⟨339776, by rfl⟩ : syracuseStep 453035 = 679553) B679553
theorem B453065 : Blo 299831 453065 := bstep (se 2 (by rfl) ⟨169899, by rfl⟩ : syracuseStep 453065 = 339799) B339799
theorem B453179 : Blo 299831 453179 := bstep (se 1 (by rfl) ⟨339884, by rfl⟩ : syracuseStep 453179 = 679769) B679769
theorem B453239 : Blo 299831 453239 := bstep (se 1 (by rfl) ⟨339929, by rfl⟩ : syracuseStep 453239 = 679859) B679859
theorem B682631 : Blo 299831 682631 := bstep (se 1 (by rfl) ⟨511973, by rfl⟩ : syracuseStep 682631 = 1023947) B1023947
theorem B453263 : Blo 299831 453263 := bstep (se 1 (by rfl) ⟨339947, by rfl⟩ : syracuseStep 453263 = 679895) B679895
theorem B453305 : Blo 299831 453305 := bstep (se 2 (by rfl) ⟨169989, by rfl⟩ : syracuseStep 453305 = 339979) B339979
theorem B813769 : Blo 299831 813769 := bstep (se 2 (by rfl) ⟨305163, by rfl⟩ : syracuseStep 813769 = 610327) B610327
theorem B453383 : Blo 299831 453383 := bstep (se 1 (by rfl) ⟨340037, by rfl⟩ : syracuseStep 453383 = 680075) B680075
theorem B453419 : Blo 299831 453419 := bstep (se 1 (by rfl) ⟨340064, by rfl⟩ : syracuseStep 453419 = 680129) B680129
theorem B682811 : Blo 299831 682811 := bstep (se 1 (by rfl) ⟨512108, by rfl⟩ : syracuseStep 682811 = 1024217) B1024217
theorem B453449 : Blo 299831 453449 := bstep (se 2 (by rfl) ⟨170043, by rfl⟩ : syracuseStep 453449 = 340087) B340087
theorem B682937 : Blo 299831 682937 := bstep (se 2 (by rfl) ⟨256101, by rfl⟩ : syracuseStep 682937 = 512203) B512203
theorem B453563 : Blo 299831 453563 := bstep (se 1 (by rfl) ⟨340172, by rfl⟩ : syracuseStep 453563 = 680345) B680345
theorem B453623 : Blo 299831 453623 := bstep (se 1 (by rfl) ⟨340217, by rfl⟩ : syracuseStep 453623 = 680435) B680435
theorem B453647 : Blo 299831 453647 := bstep (se 1 (by rfl) ⟨340235, by rfl⟩ : syracuseStep 453647 = 680471) B680471
theorem B453689 : Blo 299831 453689 := bstep (se 2 (by rfl) ⟨170133, by rfl⟩ : syracuseStep 453689 = 340267) B340267
theorem B453767 : Blo 299831 453767 := bstep (se 1 (by rfl) ⟨340325, by rfl⟩ : syracuseStep 453767 = 680651) B680651
theorem B453803 : Blo 299831 453803 := bstep (se 1 (by rfl) ⟨340352, by rfl⟩ : syracuseStep 453803 = 680705) B680705
theorem B453833 : Blo 299831 453833 := bstep (se 2 (by rfl) ⟨170187, by rfl⟩ : syracuseStep 453833 = 340375) B340375
theorem B683279 : Blo 299831 683279 := bstep (se 1 (by rfl) ⟨512459, by rfl⟩ : syracuseStep 683279 = 1024919) B1024919
theorem B683297 : Blo 299831 683297 := bstep (se 2 (by rfl) ⟨256236, by rfl⟩ : syracuseStep 683297 = 512473) B512473
theorem B453947 : Blo 299831 453947 := bstep (se 1 (by rfl) ⟨340460, by rfl⟩ : syracuseStep 453947 = 680921) B680921
theorem B454007 : Blo 299831 454007 := bstep (se 1 (by rfl) ⟨340505, by rfl⟩ : syracuseStep 454007 = 681011) B681011
theorem B454031 : Blo 299831 454031 := bstep (se 1 (by rfl) ⟨340523, by rfl⟩ : syracuseStep 454031 = 681047) B681047
theorem B454073 : Blo 299831 454073 := bstep (se 2 (by rfl) ⟨170277, by rfl⟩ : syracuseStep 454073 = 340555) B340555
theorem B1535435 : Blo 299831 1535435 := bstep (se 1 (by rfl) ⟨1151576, by rfl⟩ : syracuseStep 1535435 = 2303153) B2303153
theorem B454151 : Blo 299831 454151 := bstep (se 1 (by rfl) ⟨340613, by rfl⟩ : syracuseStep 454151 = 681227) B681227
theorem B454187 : Blo 299831 454187 := bstep (se 1 (by rfl) ⟨340640, by rfl⟩ : syracuseStep 454187 = 681281) B681281
theorem B454217 : Blo 299831 454217 := bstep (se 2 (by rfl) ⟨170331, by rfl⟩ : syracuseStep 454217 = 340663) B340663
theorem B454331 : Blo 299831 454331 := bstep (se 1 (by rfl) ⟨340748, by rfl⟩ : syracuseStep 454331 = 681497) B681497
theorem B454391 : Blo 299831 454391 := bstep (se 1 (by rfl) ⟨340793, by rfl⟩ : syracuseStep 454391 = 681587) B681587
theorem B454415 : Blo 299831 454415 := bstep (se 1 (by rfl) ⟨340811, by rfl⟩ : syracuseStep 454415 = 681623) B681623
theorem B1535759 : Blo 299831 1535759 := bstep (se 1 (by rfl) ⟨1151819, by rfl⟩ : syracuseStep 1535759 = 2303639) B2303639
theorem B454457 : Blo 299831 454457 := bstep (se 2 (by rfl) ⟨170421, by rfl⟩ : syracuseStep 454457 = 340843) B340843
theorem B454535 : Blo 299831 454535 := bstep (se 1 (by rfl) ⟨340901, by rfl⟩ : syracuseStep 454535 = 681803) B681803
theorem B323471 : Blo 299831 323471 := bstep (se 1 (by rfl) ⟨242603, by rfl⟩ : syracuseStep 323471 = 485207) B485207
theorem B454571 : Blo 299831 454571 := bstep (se 1 (by rfl) ⟨340928, by rfl⟩ : syracuseStep 454571 = 681857) B681857
theorem B454601 : Blo 299831 454601 := bstep (se 2 (by rfl) ⟨170475, by rfl⟩ : syracuseStep 454601 = 340951) B340951
theorem B454715 : Blo 299831 454715 := bstep (se 1 (by rfl) ⟨341036, by rfl⟩ : syracuseStep 454715 = 682073) B682073
theorem B454775 : Blo 299831 454775 := bstep (se 1 (by rfl) ⟨341081, by rfl⟩ : syracuseStep 454775 = 682163) B682163
theorem B454799 : Blo 299831 454799 := bstep (se 1 (by rfl) ⟨341099, by rfl⟩ : syracuseStep 454799 = 682199) B682199
theorem B454841 : Blo 299831 454841 := bstep (se 2 (by rfl) ⟨170565, by rfl⟩ : syracuseStep 454841 = 341131) B341131
theorem B454919 : Blo 299831 454919 := bstep (se 1 (by rfl) ⟨341189, by rfl⟩ : syracuseStep 454919 = 682379) B682379
theorem B454955 : Blo 299831 454955 := bstep (se 1 (by rfl) ⟨341216, by rfl⟩ : syracuseStep 454955 = 682433) B682433
theorem B454985 : Blo 299831 454985 := bstep (se 2 (by rfl) ⟨170619, by rfl⟩ : syracuseStep 454985 = 341239) B341239
theorem B1012121 : Blo 299831 1012121 := bstep (se 2 (by rfl) ⟨379545, by rfl⟩ : syracuseStep 1012121 = 759091) B759091
theorem B1143193 : Blo 299831 1143193 := bstep (se 2 (by rfl) ⟨428697, by rfl⟩ : syracuseStep 1143193 = 857395) B857395
theorem B455099 : Blo 299831 455099 := bstep (se 1 (by rfl) ⟨341324, by rfl⟩ : syracuseStep 455099 = 682649) B682649
theorem B455159 : Blo 299831 455159 := bstep (se 1 (by rfl) ⟨341369, by rfl⟩ : syracuseStep 455159 = 682739) B682739
theorem B455183 : Blo 299831 455183 := bstep (se 1 (by rfl) ⟨341387, by rfl⟩ : syracuseStep 455183 = 682775) B682775
theorem B455225 : Blo 299831 455225 := bstep (se 2 (by rfl) ⟨170709, by rfl⟩ : syracuseStep 455225 = 341419) B341419
theorem B455303 : Blo 299831 455303 := bstep (se 1 (by rfl) ⟨341477, by rfl⟩ : syracuseStep 455303 = 682955) B682955
theorem B455339 : Blo 299831 455339 := bstep (se 1 (by rfl) ⟨341504, by rfl⟩ : syracuseStep 455339 = 683009) B683009
theorem B1143497 : Blo 299831 1143497 := bstep (se 2 (by rfl) ⟨428811, by rfl⟩ : syracuseStep 1143497 = 857623) B857623
theorem B455369 : Blo 299831 455369 := bstep (se 2 (by rfl) ⟨170763, by rfl⟩ : syracuseStep 455369 = 341527) B341527
theorem B5796643 : Blo 299831 5796643 := bstep (se 1 (by rfl) ⟨4347482, by rfl⟩ : syracuseStep 5796643 = 8694965) B8694965
theorem B455483 : Blo 299831 455483 := bstep (se 1 (by rfl) ⟨341612, by rfl⟩ : syracuseStep 455483 = 683225) B683225
theorem B815933 : Blo 299831 815933 := bstep (se 3 (by rfl) ⟨152987, by rfl⟩ : syracuseStep 815933 = 305975) B305975
theorem B455543 : Blo 299831 455543 := bstep (se 1 (by rfl) ⟨341657, by rfl⟩ : syracuseStep 455543 = 683315) B683315
theorem B455567 : Blo 299831 455567 := bstep (se 1 (by rfl) ⟨341675, by rfl⟩ : syracuseStep 455567 = 683351) B683351
theorem B914323 : Blo 299831 914323 := bstep (se 1 (by rfl) ⟨685742, by rfl⟩ : syracuseStep 914323 = 1371485) B1371485
theorem B455609 : Blo 299831 455609 := bstep (se 2 (by rfl) ⟨170853, by rfl⟩ : syracuseStep 455609 = 341707) B341707
theorem B455687 : Blo 299831 455687 := bstep (se 1 (by rfl) ⟨341765, by rfl⟩ : syracuseStep 455687 = 683531) B683531
theorem B4912139 : Blo 299831 4912139 := bstep (se 1 (by rfl) ⟨3684104, by rfl⟩ : syracuseStep 4912139 = 7368209) B7368209
theorem B455723 : Blo 299831 455723 := bstep (se 1 (by rfl) ⟨341792, by rfl⟩ : syracuseStep 455723 = 683585) B683585
theorem B1012823 : Blo 299831 1012823 := bstep (se 1 (by rfl) ⟨759617, by rfl⟩ : syracuseStep 1012823 = 1519235) B1519235
theorem B1537217 : Blo 299831 1537217 := bstep (se 2 (by rfl) ⟨576456, by rfl⟩ : syracuseStep 1537217 = 1152913) B1152913
theorem B2291003 : Blo 299831 2291003 := bstep (se 1 (by rfl) ⟨1718252, by rfl⟩ : syracuseStep 2291003 = 3436505) B3436505
theorem B1734173 : Blo 299831 1734173 := bstep (se 3 (by rfl) ⟨325157, by rfl⟩ : syracuseStep 1734173 = 650315) B650315
theorem B16774685 : Blo 299831 16774685 := bstep (se 3 (by rfl) ⟨3145253, by rfl⟩ : syracuseStep 16774685 = 6290507) B6290507
theorem B1013309 : Blo 299831 1013309 := bstep (se 3 (by rfl) ⟨189995, by rfl⟩ : syracuseStep 1013309 = 379991) B379991
theorem B1308221 : Blo 299831 1308221 := bstep (se 3 (by rfl) ⟨245291, by rfl⟩ : syracuseStep 1308221 = 490583) B490583
theorem B1144439 : Blo 299831 1144439 := bstep (se 1 (by rfl) ⟨858329, by rfl⟩ : syracuseStep 1144439 = 1716659) B1716659
theorem B816841 : Blo 299831 816841 := bstep (se 2 (by rfl) ⟨306315, by rfl⟩ : syracuseStep 816841 = 612631) B612631
theorem B980851 : Blo 299831 980851 := bstep (se 1 (by rfl) ⟨735638, by rfl⟩ : syracuseStep 980851 = 1471277) B1471277
theorem B2914163 : Blo 299831 2914163 := bstep (se 1 (by rfl) ⟨2185622, by rfl⟩ : syracuseStep 2914163 = 4371245) B4371245
theorem B5339033 : Blo 299831 5339033 := bstep (se 2 (by rfl) ⟨2002137, by rfl⟩ : syracuseStep 5339033 = 4004275) B4004275
theorem B1145411 : Blo 299831 1145411 := bstep (se 1 (by rfl) ⟨859058, by rfl⟩ : syracuseStep 1145411 = 1718117) B1718117
theorem B817921 : Blo 299831 817921 := bstep (se 2 (by rfl) ⟨306720, by rfl⟩ : syracuseStep 817921 = 613441) B613441
theorem B2063141 : Blo 299831 2063141 := bstep (se 4 (by rfl) ⟨193419, by rfl⟩ : syracuseStep 2063141 = 386839) B386839
theorem B1014713 : Blo 299831 1014713 := bstep (se 2 (by rfl) ⟨380517, by rfl⟩ : syracuseStep 1014713 = 761035) B761035
theorem B621611 : Blo 299831 621611 := bstep (se 1 (by rfl) ⟨466208, by rfl⟩ : syracuseStep 621611 = 932417) B932417
theorem B1015307 : Blo 299831 1015307 := bstep (se 1 (by rfl) ⟨761480, by rfl⟩ : syracuseStep 1015307 = 1522961) B1522961
theorem B1015415 : Blo 299831 1015415 := bstep (se 1 (by rfl) ⟨761561, by rfl⟩ : syracuseStep 1015415 = 1523123) B1523123
theorem B7307009 : Blo 299831 7307009 := bstep (se 2 (by rfl) ⟨2740128, by rfl⟩ : syracuseStep 7307009 = 5480257) B5480257
theorem B1146899 : Blo 299831 1146899 := bstep (se 1 (by rfl) ⟨860174, by rfl⟩ : syracuseStep 1146899 = 1720349) B1720349
theorem B917561 : Blo 299831 917561 := bstep (se 2 (by rfl) ⟨344085, by rfl⟩ : syracuseStep 917561 = 688171) B688171
theorem B360811 : Blo 299831 360811 := bstep (se 1 (by rfl) ⟨270608, by rfl⟩ : syracuseStep 360811 = 541217) B541217
theorem B1638785 : Blo 299831 1638785 := bstep (se 2 (by rfl) ⟨614544, by rfl⟩ : syracuseStep 1638785 = 1229089) B1229089
theorem B721295 : Blo 299831 721295 := bstep (se 1 (by rfl) ⟨540971, by rfl⟩ : syracuseStep 721295 = 1081943) B1081943
theorem B1147355 : Blo 299831 1147355 := bstep (se 1 (by rfl) ⟨860516, by rfl⟩ : syracuseStep 1147355 = 1721033) B1721033
theorem B721505 : Blo 299831 721505 := bstep (se 2 (by rfl) ⟨270564, by rfl⟩ : syracuseStep 721505 = 541129) B541129
theorem B984071 : Blo 299831 984071 := bstep (se 1 (by rfl) ⟨738053, by rfl⟩ : syracuseStep 984071 = 1476107) B1476107
theorem B2458667 : Blo 299831 2458667 := bstep (se 1 (by rfl) ⟨1844000, by rfl⟩ : syracuseStep 2458667 = 3688001) B3688001
theorem B15205427 : Blo 299831 15205427 := bstep (se 1 (by rfl) ⟨11404070, by rfl⟩ : syracuseStep 15205427 = 22808141) B22808141
theorem B1017467 : Blo 299831 1017467 := bstep (se 1 (by rfl) ⟨763100, by rfl⟩ : syracuseStep 1017467 = 1526201) B1526201
theorem B1148539 : Blo 299831 1148539 := bstep (se 1 (by rfl) ⟨861404, by rfl⟩ : syracuseStep 1148539 = 1722809) B1722809
theorem B1935085 : Blo 299831 1935085 := bstep (se 3 (by rfl) ⟨362828, by rfl⟩ : syracuseStep 1935085 = 725657) B725657
theorem B1017629 : Blo 299831 1017629 := bstep (se 3 (by rfl) ⟨190805, by rfl⟩ : syracuseStep 1017629 = 381611) B381611
theorem B919471 : Blo 299831 919471 := bstep (se 1 (by rfl) ⟨689603, by rfl⟩ : syracuseStep 919471 = 1379207) B1379207
theorem B1935677 : Blo 299831 1935677 := bstep (se 3 (by rfl) ⟨362939, by rfl⟩ : syracuseStep 1935677 = 725879) B725879
theorem B2459965 : Blo 299831 2459965 := bstep (se 3 (by rfl) ⟨461243, by rfl⟩ : syracuseStep 2459965 = 922487) B922487
theorem B723343 : Blo 299831 723343 := bstep (se 1 (by rfl) ⟨542507, by rfl⟩ : syracuseStep 723343 = 1085015) B1085015
theorem B723419 : Blo 299831 723419 := bstep (se 1 (by rfl) ⟨542564, by rfl⟩ : syracuseStep 723419 = 1085129) B1085129
theorem B1018331 : Blo 299831 1018331 := bstep (se 1 (by rfl) ⟨763748, by rfl⟩ : syracuseStep 1018331 = 1527497) B1527497
theorem B854651 : Blo 299831 854651 := bstep (se 1 (by rfl) ⟨640988, by rfl⟩ : syracuseStep 854651 = 1281977) B1281977
theorem B428743 : Blo 299831 428743 := bstep (se 1 (by rfl) ⟨321557, by rfl⟩ : syracuseStep 428743 = 643115) B643115
theorem B1149815 : Blo 299831 1149815 := bstep (se 1 (by rfl) ⟨862361, by rfl⟩ : syracuseStep 1149815 = 1724723) B1724723
theorem B14027863 : Blo 299831 14027863 := bstep (se 1 (by rfl) ⟨10520897, by rfl⟩ : syracuseStep 14027863 = 21041795) B21041795
theorem B1019033 : Blo 299831 1019033 := bstep (se 2 (by rfl) ⟨382137, by rfl⟩ : syracuseStep 1019033 = 764275) B764275
theorem B920747 : Blo 299831 920747 := bstep (se 1 (by rfl) ⟨690560, by rfl⟩ : syracuseStep 920747 = 1381121) B1381121
theorem B1150787 : Blo 299831 1150787 := bstep (se 1 (by rfl) ⟨863090, by rfl⟩ : syracuseStep 1150787 = 1726181) B1726181
theorem B2461549 : Blo 299831 2461549 := bstep (se 3 (by rfl) ⟨461540, by rfl⟩ : syracuseStep 2461549 = 923081) B923081
theorem B2887559 : Blo 299831 2887559 := bstep (se 1 (by rfl) ⟨2165669, by rfl⟩ : syracuseStep 2887559 = 4331339) B4331339
theorem B855983 : Blo 299831 855983 := bstep (se 1 (by rfl) ⟨641987, by rfl⟩ : syracuseStep 855983 = 1283975) B1283975
theorem B4362245 : Blo 299831 4362245 := bstep (se 4 (by rfl) ⟨408960, by rfl⟩ : syracuseStep 4362245 = 817921) B817921
theorem B692231 : Blo 299831 692231 := bstep (se 1 (by rfl) ⟨519173, by rfl⟩ : syracuseStep 692231 = 1038347) B1038347
theorem B1151243 : Blo 299831 1151243 := bstep (se 1 (by rfl) ⟨863432, by rfl⟩ : syracuseStep 1151243 = 1726865) B1726865
theorem B1020221 : Blo 299831 1020221 := bstep (se 3 (by rfl) ⟨191291, by rfl⟩ : syracuseStep 1020221 = 382583) B382583
theorem B3248849 : Blo 299831 3248849 := bstep (se 2 (by rfl) ⟨1218318, by rfl⟩ : syracuseStep 3248849 = 2436637) B2436637
theorem B299855 : Blo 299831 299855 := bstep (se 1 (by rfl) ⟨224891, by rfl⟩ : syracuseStep 299855 = 449783) B449783
theorem B299871 : Blo 299831 299871 := bstep (se 1 (by rfl) ⟨224903, by rfl⟩ : syracuseStep 299871 = 449807) B449807
theorem B299899 : Blo 299831 299899 := bstep (se 1 (by rfl) ⟨224924, by rfl⟩ : syracuseStep 299899 = 449849) B449849
theorem B627599 : Blo 299831 627599 := bstep (se 1 (by rfl) ⟨470699, by rfl⟩ : syracuseStep 627599 = 941399) B941399
theorem B299951 : Blo 299831 299951 := bstep (se 1 (by rfl) ⟨224963, by rfl⟩ : syracuseStep 299951 = 449927) B449927
theorem B1151927 : Blo 299831 1151927 := bstep (se 1 (by rfl) ⟨863945, by rfl⟩ : syracuseStep 1151927 = 1727891) B1727891
theorem B299975 : Blo 299831 299975 := bstep (se 1 (by rfl) ⟨224981, by rfl⟩ : syracuseStep 299975 = 449963) B449963
theorem B299995 : Blo 299831 299995 := bstep (se 1 (by rfl) ⟨224996, by rfl⟩ : syracuseStep 299995 = 449993) B449993
theorem B300071 : Blo 299831 300071 := bstep (se 1 (by rfl) ⟨225053, by rfl⟩ : syracuseStep 300071 = 450107) B450107
theorem B300111 : Blo 299831 300111 := bstep (se 1 (by rfl) ⟨225083, by rfl⟩ : syracuseStep 300111 = 450167) B450167
theorem B300127 : Blo 299831 300127 := bstep (se 1 (by rfl) ⟨225095, by rfl⟩ : syracuseStep 300127 = 450191) B450191
theorem B300155 : Blo 299831 300155 := bstep (se 1 (by rfl) ⟨225116, by rfl⟩ : syracuseStep 300155 = 450233) B450233
theorem B1021085 : Blo 299831 1021085 := bstep (se 3 (by rfl) ⟨191453, by rfl⟩ : syracuseStep 1021085 = 382907) B382907
theorem B726187 : Blo 299831 726187 := bstep (se 1 (by rfl) ⟨544640, by rfl⟩ : syracuseStep 726187 = 1089281) B1089281
theorem B300207 : Blo 299831 300207 := bstep (se 1 (by rfl) ⟨225155, by rfl⟩ : syracuseStep 300207 = 450311) B450311
theorem B300231 : Blo 299831 300231 := bstep (se 1 (by rfl) ⟨225173, by rfl⟩ : syracuseStep 300231 = 450347) B450347
theorem B300251 : Blo 299831 300251 := bstep (se 1 (by rfl) ⟨225188, by rfl⟩ : syracuseStep 300251 = 450377) B450377
theorem B300327 : Blo 299831 300327 := bstep (se 1 (by rfl) ⟨225245, by rfl⟩ : syracuseStep 300327 = 450491) B450491
theorem B300367 : Blo 299831 300367 := bstep (se 1 (by rfl) ⟨225275, by rfl⟩ : syracuseStep 300367 = 450551) B450551
theorem B300383 : Blo 299831 300383 := bstep (se 1 (by rfl) ⟨225287, by rfl⟩ : syracuseStep 300383 = 450575) B450575
theorem B922985 : Blo 299831 922985 := bstep (se 2 (by rfl) ⟨346119, by rfl⟩ : syracuseStep 922985 = 692239) B692239
theorem B300411 : Blo 299831 300411 := bstep (se 1 (by rfl) ⟨225308, by rfl⟩ : syracuseStep 300411 = 450617) B450617
theorem B300463 : Blo 299831 300463 := bstep (se 1 (by rfl) ⟨225347, by rfl⟩ : syracuseStep 300463 = 450695) B450695
theorem B300487 : Blo 299831 300487 := bstep (se 1 (by rfl) ⟨225365, by rfl⟩ : syracuseStep 300487 = 450731) B450731
theorem B300507 : Blo 299831 300507 := bstep (se 1 (by rfl) ⟨225380, by rfl⟩ : syracuseStep 300507 = 450761) B450761
theorem B300583 : Blo 299831 300583 := bstep (se 1 (by rfl) ⟨225437, by rfl⟩ : syracuseStep 300583 = 450875) B450875
theorem B300623 : Blo 299831 300623 := bstep (se 1 (by rfl) ⟨225467, by rfl⟩ : syracuseStep 300623 = 450935) B450935
theorem B300639 : Blo 299831 300639 := bstep (se 1 (by rfl) ⟨225479, by rfl⟩ : syracuseStep 300639 = 450959) B450959
theorem B300667 : Blo 299831 300667 := bstep (se 1 (by rfl) ⟨225500, by rfl⟩ : syracuseStep 300667 = 451001) B451001
theorem B300719 : Blo 299831 300719 := bstep (se 1 (by rfl) ⟨225539, by rfl⟩ : syracuseStep 300719 = 451079) B451079
theorem B1021625 : Blo 299831 1021625 := bstep (se 2 (by rfl) ⟨383109, by rfl⟩ : syracuseStep 1021625 = 766219) B766219
theorem B1152701 : Blo 299831 1152701 := bstep (se 3 (by rfl) ⟨216131, by rfl⟩ : syracuseStep 1152701 = 432263) B432263
theorem B300743 : Blo 299831 300743 := bstep (se 1 (by rfl) ⟨225557, by rfl⟩ : syracuseStep 300743 = 451115) B451115
theorem B300763 : Blo 299831 300763 := bstep (se 1 (by rfl) ⟨225572, by rfl⟩ : syracuseStep 300763 = 451145) B451145
theorem B300839 : Blo 299831 300839 := bstep (se 1 (by rfl) ⟨225629, by rfl⟩ : syracuseStep 300839 = 451259) B451259
theorem B300879 : Blo 299831 300879 := bstep (se 1 (by rfl) ⟨225659, by rfl⟩ : syracuseStep 300879 = 451319) B451319
theorem B300895 : Blo 299831 300895 := bstep (se 1 (by rfl) ⟨225671, by rfl⟩ : syracuseStep 300895 = 451343) B451343
theorem B300923 : Blo 299831 300923 := bstep (se 1 (by rfl) ⟨225692, by rfl⟩ : syracuseStep 300923 = 451385) B451385
theorem B300975 : Blo 299831 300975 := bstep (se 1 (by rfl) ⟨225731, by rfl⟩ : syracuseStep 300975 = 451463) B451463
theorem B759739 : Blo 299831 759739 := bstep (se 1 (by rfl) ⟨569804, by rfl⟩ : syracuseStep 759739 = 1139609) B1139609
theorem B300999 : Blo 299831 300999 := bstep (se 1 (by rfl) ⟨225749, by rfl⟩ : syracuseStep 300999 = 451499) B451499
theorem B301019 : Blo 299831 301019 := bstep (se 1 (by rfl) ⟨225764, by rfl⟩ : syracuseStep 301019 = 451529) B451529
theorem B301095 : Blo 299831 301095 := bstep (se 1 (by rfl) ⟨225821, by rfl⟩ : syracuseStep 301095 = 451643) B451643
theorem B301135 : Blo 299831 301135 := bstep (se 1 (by rfl) ⟨225851, by rfl⟩ : syracuseStep 301135 = 451703) B451703
theorem B301151 : Blo 299831 301151 := bstep (se 1 (by rfl) ⟨225863, by rfl⟩ : syracuseStep 301151 = 451727) B451727
theorem B301179 : Blo 299831 301179 := bstep (se 1 (by rfl) ⟨225884, by rfl⟩ : syracuseStep 301179 = 451769) B451769
theorem B301231 : Blo 299831 301231 := bstep (se 1 (by rfl) ⟨225923, by rfl⟩ : syracuseStep 301231 = 451847) B451847
theorem B301255 : Blo 299831 301255 := bstep (se 1 (by rfl) ⟨225941, by rfl⟩ : syracuseStep 301255 = 451883) B451883
theorem B301275 : Blo 299831 301275 := bstep (se 1 (by rfl) ⟨225956, by rfl⟩ : syracuseStep 301275 = 451913) B451913
theorem B1022219 : Blo 299831 1022219 := bstep (se 1 (by rfl) ⟨766664, by rfl⟩ : syracuseStep 1022219 = 1533329) B1533329
theorem B301351 : Blo 299831 301351 := bstep (se 1 (by rfl) ⟨226013, by rfl⟩ : syracuseStep 301351 = 452027) B452027
theorem B301391 : Blo 299831 301391 := bstep (se 1 (by rfl) ⟨226043, by rfl⟩ : syracuseStep 301391 = 452087) B452087
theorem B301407 : Blo 299831 301407 := bstep (se 1 (by rfl) ⟨226055, by rfl⟩ : syracuseStep 301407 = 452111) B452111
theorem B1153385 : Blo 299831 1153385 := bstep (se 2 (by rfl) ⟨432519, by rfl⟩ : syracuseStep 1153385 = 865039) B865039
theorem B301435 : Blo 299831 301435 := bstep (se 1 (by rfl) ⟨226076, by rfl⟩ : syracuseStep 301435 = 452153) B452153
theorem B14686595 : Blo 299831 14686595 := bstep (se 1 (by rfl) ⟨11014946, by rfl⟩ : syracuseStep 14686595 = 22029893) B22029893
theorem B301487 : Blo 299831 301487 := bstep (se 1 (by rfl) ⟨226115, by rfl⟩ : syracuseStep 301487 = 452231) B452231
theorem B301511 : Blo 299831 301511 := bstep (se 1 (by rfl) ⟨226133, by rfl⟩ : syracuseStep 301511 = 452267) B452267
theorem B301531 : Blo 299831 301531 := bstep (se 1 (by rfl) ⟨226148, by rfl⟩ : syracuseStep 301531 = 452297) B452297
theorem B1284589 : Blo 299831 1284589 := bstep (se 3 (by rfl) ⟨240860, by rfl⟩ : syracuseStep 1284589 = 481721) B481721
theorem B1219097 : Blo 299831 1219097 := bstep (se 2 (by rfl) ⟨457161, by rfl⟩ : syracuseStep 1219097 = 914323) B914323
theorem B1022489 : Blo 299831 1022489 := bstep (se 2 (by rfl) ⟨383433, by rfl⟩ : syracuseStep 1022489 = 766867) B766867
theorem B3545633 : Blo 299831 3545633 := bstep (se 2 (by rfl) ⟨1329612, by rfl⟩ : syracuseStep 3545633 = 2659225) B2659225
theorem B301607 : Blo 299831 301607 := bstep (se 1 (by rfl) ⟨226205, by rfl⟩ : syracuseStep 301607 = 452411) B452411
theorem B9837125 : Blo 299831 9837125 := bstep (se 4 (by rfl) ⟨922230, by rfl⟩ : syracuseStep 9837125 = 1844461) B1844461
theorem B301647 : Blo 299831 301647 := bstep (se 1 (by rfl) ⟨226235, by rfl⟩ : syracuseStep 301647 = 452471) B452471
theorem B301663 : Blo 299831 301663 := bstep (se 1 (by rfl) ⟨226247, by rfl⟩ : syracuseStep 301663 = 452495) B452495
theorem B727649 : Blo 299831 727649 := bstep (se 2 (by rfl) ⟨272868, by rfl⟩ : syracuseStep 727649 = 545737) B545737
theorem B301691 : Blo 299831 301691 := bstep (se 1 (by rfl) ⟨226268, by rfl⟩ : syracuseStep 301691 = 452537) B452537
theorem B301743 : Blo 299831 301743 := bstep (se 1 (by rfl) ⟨226307, by rfl⟩ : syracuseStep 301743 = 452615) B452615
theorem B301767 : Blo 299831 301767 := bstep (se 1 (by rfl) ⟨226325, by rfl⟩ : syracuseStep 301767 = 452651) B452651
theorem B2071241 : Blo 299831 2071241 := bstep (se 2 (by rfl) ⟨776715, by rfl⟩ : syracuseStep 2071241 = 1553431) B1553431
theorem B301787 : Blo 299831 301787 := bstep (se 1 (by rfl) ⟨226340, by rfl⟩ : syracuseStep 301787 = 452681) B452681
theorem B301863 : Blo 299831 301863 := bstep (se 1 (by rfl) ⟨226397, by rfl⟩ : syracuseStep 301863 = 452795) B452795
theorem B301903 : Blo 299831 301903 := bstep (se 1 (by rfl) ⟨226427, by rfl⟩ : syracuseStep 301903 = 452855) B452855
theorem B301919 : Blo 299831 301919 := bstep (se 1 (by rfl) ⟨226439, by rfl⟩ : syracuseStep 301919 = 452879) B452879
theorem B301947 : Blo 299831 301947 := bstep (se 1 (by rfl) ⟨226460, by rfl⟩ : syracuseStep 301947 = 452921) B452921
theorem B301999 : Blo 299831 301999 := bstep (se 1 (by rfl) ⟨226499, by rfl⟩ : syracuseStep 301999 = 452999) B452999
theorem B302023 : Blo 299831 302023 := bstep (se 1 (by rfl) ⟨226517, by rfl⟩ : syracuseStep 302023 = 453035) B453035
theorem B302043 : Blo 299831 302043 := bstep (se 1 (by rfl) ⟨226532, by rfl⟩ : syracuseStep 302043 = 453065) B453065
theorem B302119 : Blo 299831 302119 := bstep (se 1 (by rfl) ⟨226589, by rfl⟩ : syracuseStep 302119 = 453179) B453179
theorem B302159 : Blo 299831 302159 := bstep (se 1 (by rfl) ⟨226619, by rfl⟩ : syracuseStep 302159 = 453239) B453239
theorem B302175 : Blo 299831 302175 := bstep (se 1 (by rfl) ⟨226631, by rfl⟩ : syracuseStep 302175 = 453263) B453263
theorem B302203 : Blo 299831 302203 := bstep (se 1 (by rfl) ⟨226652, by rfl⟩ : syracuseStep 302203 = 453305) B453305
theorem B302255 : Blo 299831 302255 := bstep (se 1 (by rfl) ⟨226691, by rfl⟩ : syracuseStep 302255 = 453383) B453383
theorem B302279 : Blo 299831 302279 := bstep (se 1 (by rfl) ⟨226709, by rfl⟩ : syracuseStep 302279 = 453419) B453419
theorem B302299 : Blo 299831 302299 := bstep (se 1 (by rfl) ⟨226724, by rfl⟩ : syracuseStep 302299 = 453449) B453449
theorem B302375 : Blo 299831 302375 := bstep (se 1 (by rfl) ⟨226781, by rfl⟩ : syracuseStep 302375 = 453563) B453563
theorem B302415 : Blo 299831 302415 := bstep (se 1 (by rfl) ⟨226811, by rfl⟩ : syracuseStep 302415 = 453623) B453623
theorem B302431 : Blo 299831 302431 := bstep (se 1 (by rfl) ⟨226823, by rfl⟩ : syracuseStep 302431 = 453647) B453647
theorem B302459 : Blo 299831 302459 := bstep (se 1 (by rfl) ⟨226844, by rfl⟩ : syracuseStep 302459 = 453689) B453689
theorem B302511 : Blo 299831 302511 := bstep (se 1 (by rfl) ⟨226883, by rfl⟩ : syracuseStep 302511 = 453767) B453767
theorem B302535 : Blo 299831 302535 := bstep (se 1 (by rfl) ⟨226901, by rfl⟩ : syracuseStep 302535 = 453803) B453803
theorem B302555 : Blo 299831 302555 := bstep (se 1 (by rfl) ⟨226916, by rfl⟩ : syracuseStep 302555 = 453833) B453833
theorem B859673 : Blo 299831 859673 := bstep (se 2 (by rfl) ⟨322377, by rfl⟩ : syracuseStep 859673 = 644755) B644755
theorem B302631 : Blo 299831 302631 := bstep (se 1 (by rfl) ⟨226973, by rfl⟩ : syracuseStep 302631 = 453947) B453947
theorem B302671 : Blo 299831 302671 := bstep (se 1 (by rfl) ⟨227003, by rfl⟩ : syracuseStep 302671 = 454007) B454007
theorem B302687 : Blo 299831 302687 := bstep (se 1 (by rfl) ⟨227015, by rfl⟩ : syracuseStep 302687 = 454031) B454031
theorem B1089121 : Blo 299831 1089121 := bstep (se 2 (by rfl) ⟨408420, by rfl⟩ : syracuseStep 1089121 = 816841) B816841
theorem B302715 : Blo 299831 302715 := bstep (se 1 (by rfl) ⟨227036, by rfl⟩ : syracuseStep 302715 = 454073) B454073
theorem B1023623 : Blo 299831 1023623 := bstep (se 1 (by rfl) ⟨767717, by rfl⟩ : syracuseStep 1023623 = 1535435) B1535435
theorem B302767 : Blo 299831 302767 := bstep (se 1 (by rfl) ⟨227075, by rfl⟩ : syracuseStep 302767 = 454151) B454151
theorem B1023677 : Blo 299831 1023677 := bstep (se 3 (by rfl) ⟨191939, by rfl⟩ : syracuseStep 1023677 = 383879) B383879
theorem B302791 : Blo 299831 302791 := bstep (se 1 (by rfl) ⟨227093, by rfl⟩ : syracuseStep 302791 = 454187) B454187
theorem B302811 : Blo 299831 302811 := bstep (se 1 (by rfl) ⟨227108, by rfl⟩ : syracuseStep 302811 = 454217) B454217
theorem B302887 : Blo 299831 302887 := bstep (se 1 (by rfl) ⟨227165, by rfl⟩ : syracuseStep 302887 = 454331) B454331
theorem B302927 : Blo 299831 302927 := bstep (se 1 (by rfl) ⟨227195, by rfl⟩ : syracuseStep 302927 = 454391) B454391
theorem B302943 : Blo 299831 302943 := bstep (se 1 (by rfl) ⟨227207, by rfl⟩ : syracuseStep 302943 = 454415) B454415
theorem B1023839 : Blo 299831 1023839 := bstep (se 1 (by rfl) ⟨767879, by rfl⟩ : syracuseStep 1023839 = 1535759) B1535759
theorem B302971 : Blo 299831 302971 := bstep (se 1 (by rfl) ⟨227228, by rfl⟩ : syracuseStep 302971 = 454457) B454457
theorem B303023 : Blo 299831 303023 := bstep (se 1 (by rfl) ⟨227267, by rfl⟩ : syracuseStep 303023 = 454535) B454535
theorem B303047 : Blo 299831 303047 := bstep (se 1 (by rfl) ⟨227285, by rfl⟩ : syracuseStep 303047 = 454571) B454571
theorem B303067 : Blo 299831 303067 := bstep (se 1 (by rfl) ⟨227300, by rfl⟩ : syracuseStep 303067 = 454601) B454601
theorem B1024001 : Blo 299831 1024001 := bstep (se 2 (by rfl) ⟨384000, by rfl⟩ : syracuseStep 1024001 = 768001) B768001
theorem B3416093 : Blo 299831 3416093 := bstep (se 3 (by rfl) ⟨640517, by rfl⟩ : syracuseStep 3416093 = 1281035) B1281035
theorem B303143 : Blo 299831 303143 := bstep (se 1 (by rfl) ⟨227357, by rfl⟩ : syracuseStep 303143 = 454715) B454715
theorem B303183 : Blo 299831 303183 := bstep (se 1 (by rfl) ⟨227387, by rfl⟩ : syracuseStep 303183 = 454775) B454775
theorem B303199 : Blo 299831 303199 := bstep (se 1 (by rfl) ⟨227399, by rfl⟩ : syracuseStep 303199 = 454799) B454799
theorem B303227 : Blo 299831 303227 := bstep (se 1 (by rfl) ⟨227420, by rfl⟩ : syracuseStep 303227 = 454841) B454841
theorem B1712285 : Blo 299831 1712285 := bstep (se 3 (by rfl) ⟨321053, by rfl⟩ : syracuseStep 1712285 = 642107) B642107
theorem B303279 : Blo 299831 303279 := bstep (se 1 (by rfl) ⟨227459, by rfl⟩ : syracuseStep 303279 = 454919) B454919
theorem B303303 : Blo 299831 303303 := bstep (se 1 (by rfl) ⟨227477, by rfl⟩ : syracuseStep 303303 = 454955) B454955
theorem B303323 : Blo 299831 303323 := bstep (se 1 (by rfl) ⟨227492, by rfl⟩ : syracuseStep 303323 = 454985) B454985
theorem B2302181 : Blo 299831 2302181 := bstep (se 4 (by rfl) ⟨215829, by rfl⟩ : syracuseStep 2302181 = 431659) B431659
theorem B303399 : Blo 299831 303399 := bstep (se 1 (by rfl) ⟨227549, by rfl⟩ : syracuseStep 303399 = 455099) B455099
theorem B303439 : Blo 299831 303439 := bstep (se 1 (by rfl) ⟨227579, by rfl⟩ : syracuseStep 303439 = 455159) B455159
theorem B303455 : Blo 299831 303455 := bstep (se 1 (by rfl) ⟨227591, by rfl⟩ : syracuseStep 303455 = 455183) B455183
theorem B303483 : Blo 299831 303483 := bstep (se 1 (by rfl) ⟨227612, by rfl⟩ : syracuseStep 303483 = 455225) B455225
theorem B303535 : Blo 299831 303535 := bstep (se 1 (by rfl) ⟨227651, by rfl⟩ : syracuseStep 303535 = 455303) B455303
theorem B303559 : Blo 299831 303559 := bstep (se 1 (by rfl) ⟨227669, by rfl⟩ : syracuseStep 303559 = 455339) B455339
theorem B762331 : Blo 299831 762331 := bstep (se 1 (by rfl) ⟨571748, by rfl⟩ : syracuseStep 762331 = 1143497) B1143497
theorem B303579 : Blo 299831 303579 := bstep (se 1 (by rfl) ⟨227684, by rfl⟩ : syracuseStep 303579 = 455369) B455369
theorem B303655 : Blo 299831 303655 := bstep (se 1 (by rfl) ⟨227741, by rfl⟩ : syracuseStep 303655 = 455483) B455483
theorem B303695 : Blo 299831 303695 := bstep (se 1 (by rfl) ⟨227771, by rfl⟩ : syracuseStep 303695 = 455543) B455543
theorem B303711 : Blo 299831 303711 := bstep (se 1 (by rfl) ⟨227783, by rfl⟩ : syracuseStep 303711 = 455567) B455567
theorem B303739 : Blo 299831 303739 := bstep (se 1 (by rfl) ⟨227804, by rfl⟩ : syracuseStep 303739 = 455609) B455609
theorem B303791 : Blo 299831 303791 := bstep (se 1 (by rfl) ⟨227843, by rfl⟩ : syracuseStep 303791 = 455687) B455687
theorem B303815 : Blo 299831 303815 := bstep (se 1 (by rfl) ⟨227861, by rfl⟩ : syracuseStep 303815 = 455723) B455723
theorem B1024811 : Blo 299831 1024811 := bstep (se 1 (by rfl) ⟨768608, by rfl⟩ : syracuseStep 1024811 = 1537217) B1537217
theorem B1156115 : Blo 299831 1156115 := bstep (se 1 (by rfl) ⟨867086, by rfl⟩ : syracuseStep 1156115 = 1734173) B1734173
theorem B11183123 : Blo 299831 11183123 := bstep (se 1 (by rfl) ⟨8387342, by rfl⟩ : syracuseStep 11183123 = 16774685) B16774685
theorem B1025081 : Blo 299831 1025081 := bstep (se 2 (by rfl) ⟨384405, by rfl⟩ : syracuseStep 1025081 = 768811) B768811
theorem B762959 : Blo 299831 762959 := bstep (se 1 (by rfl) ⟨572219, by rfl⟩ : syracuseStep 762959 = 1144439) B1144439
theorem B1942775 : Blo 299831 1942775 := bstep (se 1 (by rfl) ⟨1457081, by rfl⟩ : syracuseStep 1942775 = 2914163) B2914163
theorem B1025405 : Blo 299831 1025405 := bstep (se 3 (by rfl) ⟨192263, by rfl⟩ : syracuseStep 1025405 = 384527) B384527
theorem B337531 : Blo 299831 337531 := bstep (se 1 (by rfl) ⟨253148, by rfl⟩ : syracuseStep 337531 = 506297) B506297
theorem B2762387 : Blo 299831 2762387 := bstep (se 1 (by rfl) ⟨2071790, by rfl⟩ : syracuseStep 2762387 = 4143581) B4143581
theorem B763607 : Blo 299831 763607 := bstep (se 1 (by rfl) ⟨572705, by rfl⟩ : syracuseStep 763607 = 1145411) B1145411
theorem B2434951 : Blo 299831 2434951 := bstep (se 1 (by rfl) ⟨1826213, by rfl⟩ : syracuseStep 2434951 = 3652427) B3652427
theorem B337999 : Blo 299831 337999 := bstep (se 1 (by rfl) ⟨253499, by rfl⟩ : syracuseStep 337999 = 506999) B506999
theorem B1288349 : Blo 299831 1288349 := bstep (se 3 (by rfl) ⟨241565, by rfl⟩ : syracuseStep 1288349 = 483131) B483131
theorem B862589 : Blo 299831 862589 := bstep (se 3 (by rfl) ⟨161735, by rfl⟩ : syracuseStep 862589 = 323471) B323471
theorem B338395 : Blo 299831 338395 := bstep (se 1 (by rfl) ⟨253796, by rfl⟩ : syracuseStep 338395 = 507593) B507593
theorem B1289033 : Blo 299831 1289033 := bstep (se 2 (by rfl) ⟨483387, by rfl⟩ : syracuseStep 1289033 = 966775) B966775
theorem B4139851 : Blo 299831 4139851 := bstep (se 1 (by rfl) ⟨3104888, by rfl⟩ : syracuseStep 4139851 = 6209777) B6209777
theorem B338863 : Blo 299831 338863 := bstep (se 1 (by rfl) ⟨254147, by rfl⟩ : syracuseStep 338863 = 508295) B508295
theorem B1289135 : Blo 299831 1289135 := bstep (se 1 (by rfl) ⟨966851, by rfl⟩ : syracuseStep 1289135 = 1933703) B1933703
theorem B1715201 : Blo 299831 1715201 := bstep (se 2 (by rfl) ⟨643200, by rfl⟩ : syracuseStep 1715201 = 1286401) B1286401
theorem B339295 : Blo 299831 339295 := bstep (se 1 (by rfl) ⟨254471, by rfl⟩ : syracuseStep 339295 = 508943) B508943
theorem B1945235 : Blo 299831 1945235 := bstep (se 1 (by rfl) ⟨1458926, by rfl⟩ : syracuseStep 1945235 = 2917853) B2917853
theorem B339655 : Blo 299831 339655 := bstep (se 1 (by rfl) ⟨254741, by rfl⟩ : syracuseStep 339655 = 509483) B509483
theorem B3092411 : Blo 299831 3092411 := bstep (se 1 (by rfl) ⟨2319308, by rfl⟩ : syracuseStep 3092411 = 4638617) B4638617
theorem B5156945 : Blo 299831 5156945 := bstep (se 2 (by rfl) ⟨1933854, by rfl⟩ : syracuseStep 5156945 = 3867709) B3867709
theorem B962675 : Blo 299831 962675 := bstep (se 1 (by rfl) ⟨722006, by rfl⟩ : syracuseStep 962675 = 1444013) B1444013
theorem B1454237 : Blo 299831 1454237 := bstep (se 3 (by rfl) ⟨272669, by rfl⟩ : syracuseStep 1454237 = 545339) B545339
theorem B766199 : Blo 299831 766199 := bstep (se 1 (by rfl) ⟨574649, by rfl⟩ : syracuseStep 766199 = 1149299) B1149299
theorem B864503 : Blo 299831 864503 := bstep (se 1 (by rfl) ⟨648377, by rfl⟩ : syracuseStep 864503 = 1296755) B1296755
theorem B1519883 : Blo 299831 1519883 := bstep (se 1 (by rfl) ⟨1139912, by rfl⟩ : syracuseStep 1519883 = 2279825) B2279825
theorem B3649853 : Blo 299831 3649853 := bstep (se 3 (by rfl) ⟨684347, by rfl⟩ : syracuseStep 3649853 = 1368695) B1368695
theorem B864731 : Blo 299831 864731 := bstep (se 1 (by rfl) ⟨648548, by rfl⟩ : syracuseStep 864731 = 1297097) B1297097
theorem B340519 : Blo 299831 340519 := bstep (se 1 (by rfl) ⟨255389, by rfl⟩ : syracuseStep 340519 = 510779) B510779
theorem B2077369 : Blo 299831 2077369 := bstep (se 2 (by rfl) ⟨779013, by rfl⟩ : syracuseStep 2077369 = 1558027) B1558027
theorem B1454851 : Blo 299831 1454851 := bstep (se 1 (by rfl) ⟨1091138, by rfl⟩ : syracuseStep 1454851 = 2182277) B2182277
theorem B2175821 : Blo 299831 2175821 := bstep (se 3 (by rfl) ⟨407966, by rfl⟩ : syracuseStep 2175821 = 815933) B815933
theorem B2765825 : Blo 299831 2765825 := bstep (se 2 (by rfl) ⟨1037184, by rfl⟩ : syracuseStep 2765825 = 2074369) B2074369
theorem B3454001 : Blo 299831 3454001 := bstep (se 2 (by rfl) ⟨1295250, by rfl⟩ : syracuseStep 3454001 = 2590501) B2590501
theorem B3650777 : Blo 299831 3650777 := bstep (se 2 (by rfl) ⟨1369041, by rfl⟩ : syracuseStep 3650777 = 2738083) B2738083
theorem B1029437 : Blo 299831 1029437 := bstep (se 3 (by rfl) ⟨193019, by rfl⟩ : syracuseStep 1029437 = 386039) B386039
theorem B570959 : Blo 299831 570959 := bstep (se 1 (by rfl) ⟨428219, by rfl⟩ : syracuseStep 570959 = 856439) B856439
theorem B767627 : Blo 299831 767627 := bstep (se 1 (by rfl) ⟨575720, by rfl⟩ : syracuseStep 767627 = 1151441) B1151441
theorem B1521341 : Blo 299831 1521341 := bstep (se 3 (by rfl) ⟨285251, by rfl⟩ : syracuseStep 1521341 = 570503) B570503
theorem B2897707 : Blo 299831 2897707 := bstep (se 1 (by rfl) ⟨2173280, by rfl⟩ : syracuseStep 2897707 = 4346561) B4346561
theorem B1521503 : Blo 299831 1521503 := bstep (se 1 (by rfl) ⟨1141127, by rfl⟩ : syracuseStep 1521503 = 2282255) B2282255
theorem B767839 : Blo 299831 767839 := bstep (se 1 (by rfl) ⟨575879, by rfl⟩ : syracuseStep 767839 = 1151759) B1151759
theorem B506027 : Blo 299831 506027 := bstep (se 1 (by rfl) ⟨379520, by rfl⟩ : syracuseStep 506027 = 759041) B759041
theorem B1030643 : Blo 299831 1030643 := bstep (se 1 (by rfl) ⟨772982, by rfl⟩ : syracuseStep 1030643 = 1545965) B1545965
theorem B506425 : Blo 299831 506425 := bstep (se 2 (by rfl) ⟨189909, by rfl⟩ : syracuseStep 506425 = 379819) B379819
theorem B571961 : Blo 299831 571961 := bstep (se 2 (by rfl) ⟨214485, by rfl⟩ : syracuseStep 571961 = 428971) B428971
theorem B1456775 : Blo 299831 1456775 := bstep (se 1 (by rfl) ⟨1092581, by rfl⟩ : syracuseStep 1456775 = 2185163) B2185163
theorem B506567 : Blo 299831 506567 := bstep (se 1 (by rfl) ⟨379925, by rfl⟩ : syracuseStep 506567 = 759851) B759851
theorem B768761 : Blo 299831 768761 := bstep (se 2 (by rfl) ⟨288285, by rfl⟩ : syracuseStep 768761 = 576571) B576571
theorem B506729 : Blo 299831 506729 := bstep (se 2 (by rfl) ⟨190023, by rfl⟩ : syracuseStep 506729 = 380047) B380047
theorem B965789 : Blo 299831 965789 := bstep (se 3 (by rfl) ⟨181085, by rfl⟩ : syracuseStep 965789 = 362171) B362171
theorem B507127 : Blo 299831 507127 := bstep (se 1 (by rfl) ⟨380345, by rfl⟩ : syracuseStep 507127 = 760691) B760691
theorem B1719575 : Blo 299831 1719575 := bstep (se 1 (by rfl) ⟨1289681, by rfl⟩ : syracuseStep 1719575 = 2579363) B2579363
theorem B507323 : Blo 299831 507323 := bstep (se 1 (by rfl) ⟨380492, by rfl⟩ : syracuseStep 507323 = 760985) B760985
theorem B1228297 : Blo 299831 1228297 := bstep (se 2 (by rfl) ⟨460611, by rfl⟩ : syracuseStep 1228297 = 921223) B921223
theorem B507431 : Blo 299831 507431 := bstep (se 1 (by rfl) ⟨380573, by rfl⟩ : syracuseStep 507431 = 761147) B761147
theorem B2178647 : Blo 299831 2178647 := bstep (se 1 (by rfl) ⟨1633985, by rfl⟩ : syracuseStep 2178647 = 3267971) B3267971
theorem B4341437 : Blo 299831 4341437 := bstep (se 3 (by rfl) ⟨814019, by rfl⟩ : syracuseStep 4341437 = 1628039) B1628039
theorem B507721 : Blo 299831 507721 := bstep (se 2 (by rfl) ⟨190395, by rfl⟩ : syracuseStep 507721 = 380791) B380791
theorem B507755 : Blo 299831 507755 := bstep (se 1 (by rfl) ⟨380816, by rfl⟩ : syracuseStep 507755 = 761633) B761633
theorem B508153 : Blo 299831 508153 := bstep (se 2 (by rfl) ⟨190557, by rfl⟩ : syracuseStep 508153 = 381115) B381115
theorem B868751 : Blo 299831 868751 := bstep (se 1 (by rfl) ⟨651563, by rfl⟩ : syracuseStep 868751 = 1303127) B1303127
theorem B508423 : Blo 299831 508423 := bstep (se 1 (by rfl) ⟨381317, by rfl⟩ : syracuseStep 508423 = 762635) B762635
theorem B573959 : Blo 299831 573959 := bstep (se 1 (by rfl) ⟨430469, by rfl⟩ : syracuseStep 573959 = 860939) B860939
theorem B1524257 : Blo 299831 1524257 := bstep (se 2 (by rfl) ⟨571596, by rfl⟩ : syracuseStep 1524257 = 1143193) B1143193
theorem B508855 : Blo 299831 508855 := bstep (se 1 (by rfl) ⟨381641, by rfl⟩ : syracuseStep 508855 = 763283) B763283
theorem B574391 : Blo 299831 574391 := bstep (se 1 (by rfl) ⟨430793, by rfl⟩ : syracuseStep 574391 = 861587) B861587
theorem B574543 : Blo 299831 574543 := bstep (se 1 (by rfl) ⟨430907, by rfl⟩ : syracuseStep 574543 = 861815) B861815
theorem B509051 : Blo 299831 509051 := bstep (se 1 (by rfl) ⟨381788, by rfl⟩ : syracuseStep 509051 = 763577) B763577
theorem B640399 : Blo 299831 640399 := bstep (se 1 (by rfl) ⟨480299, by rfl⟩ : syracuseStep 640399 = 960599) B960599
theorem B509449 : Blo 299831 509449 := bstep (se 2 (by rfl) ⟨191043, by rfl⟩ : syracuseStep 509449 = 382087) B382087
theorem B509611 : Blo 299831 509611 := bstep (se 1 (by rfl) ⟨382208, by rfl⟩ : syracuseStep 509611 = 764417) B764417
theorem B1296071 : Blo 299831 1296071 := bstep (se 1 (by rfl) ⟨972053, by rfl⟩ : syracuseStep 1296071 = 1944107) B1944107
theorem B640723 : Blo 299831 640723 := bstep (se 1 (by rfl) ⟨480542, by rfl⟩ : syracuseStep 640723 = 961085) B961085
theorem B509915 : Blo 299831 509915 := bstep (se 1 (by rfl) ⟨382436, by rfl⟩ : syracuseStep 509915 = 764873) B764873
theorem B968723 : Blo 299831 968723 := bstep (se 1 (by rfl) ⟨726542, by rfl⟩ : syracuseStep 968723 = 1453085) B1453085
theorem B510151 : Blo 299831 510151 := bstep (se 1 (by rfl) ⟨382613, by rfl⟩ : syracuseStep 510151 = 765227) B765227
theorem B510313 : Blo 299831 510313 := bstep (se 2 (by rfl) ⟨191367, by rfl⟩ : syracuseStep 510313 = 382735) B382735
theorem B575849 : Blo 299831 575849 := bstep (se 2 (by rfl) ⟨215943, by rfl⟩ : syracuseStep 575849 = 431887) B431887
theorem B641953 : Blo 299831 641953 := bstep (se 2 (by rfl) ⟨240732, by rfl⟩ : syracuseStep 641953 = 481465) B481465
theorem B674747 : Blo 299831 674747 := bstep (se 1 (by rfl) ⟨506060, by rfl⟩ : syracuseStep 674747 = 1012121) B1012121
theorem B510907 : Blo 299831 510907 := bstep (se 1 (by rfl) ⟨383180, by rfl⟩ : syracuseStep 510907 = 766361) B766361
theorem B511015 : Blo 299831 511015 := bstep (se 1 (by rfl) ⟨383261, by rfl⟩ : syracuseStep 511015 = 766523) B766523
theorem B674873 : Blo 299831 674873 := bstep (se 2 (by rfl) ⟨253077, by rfl⟩ : syracuseStep 674873 = 506155) B506155
theorem B511339 : Blo 299831 511339 := bstep (se 1 (by rfl) ⟨383504, by rfl⟩ : syracuseStep 511339 = 767009) B767009
theorem B675215 : Blo 299831 675215 := bstep (se 1 (by rfl) ⟨506411, by rfl⟩ : syracuseStep 675215 = 1012823) B1012823
theorem B3427757 : Blo 299831 3427757 := bstep (se 3 (by rfl) ⟨642704, by rfl⟩ : syracuseStep 3427757 = 1285409) B1285409
theorem B1527335 : Blo 299831 1527335 := bstep (se 1 (by rfl) ⟨1145501, by rfl⟩ : syracuseStep 1527335 = 2291003) B2291003
theorem B675539 : Blo 299831 675539 := bstep (se 1 (by rfl) ⟨506654, by rfl⟩ : syracuseStep 675539 = 1013309) B1013309
theorem B872147 : Blo 299831 872147 := bstep (se 1 (by rfl) ⟨654110, by rfl⟩ : syracuseStep 872147 = 1308221) B1308221
theorem B2281283 : Blo 299831 2281283 := bstep (se 1 (by rfl) ⟨1710962, by rfl⟩ : syracuseStep 2281283 = 3421925) B3421925
theorem B3559355 : Blo 299831 3559355 := bstep (se 1 (by rfl) ⟨2669516, by rfl⟩ : syracuseStep 3559355 = 5339033) B5339033
theorem B4378853 : Blo 299831 4378853 := bstep (se 4 (by rfl) ⟨410517, by rfl⟩ : syracuseStep 4378853 = 821035) B821035
theorem B512399 : Blo 299831 512399 := bstep (se 1 (by rfl) ⟨384299, by rfl⟩ : syracuseStep 512399 = 768599) B768599
theorem B1167817 : Blo 299831 1167817 := bstep (se 2 (by rfl) ⟨437931, by rfl⟩ : syracuseStep 1167817 = 875863) B875863
theorem B676475 : Blo 299831 676475 := bstep (se 1 (by rfl) ⟨507356, by rfl⟩ : syracuseStep 676475 = 1014713) B1014713
theorem B512635 : Blo 299831 512635 := bstep (se 1 (by rfl) ⟨384476, by rfl⟩ : syracuseStep 512635 = 768953) B768953
theorem B414407 : Blo 299831 414407 := bstep (se 1 (by rfl) ⟨310805, by rfl⟩ : syracuseStep 414407 = 621611) B621611
theorem B676601 : Blo 299831 676601 := bstep (se 2 (by rfl) ⟨253725, by rfl⟩ : syracuseStep 676601 = 507451) B507451
theorem B676871 : Blo 299831 676871 := bstep (se 1 (by rfl) ⟨507653, by rfl⟩ : syracuseStep 676871 = 1015307) B1015307
theorem B381991 : Blo 299831 381991 := bstep (se 1 (by rfl) ⟨286493, by rfl⟩ : syracuseStep 381991 = 572987) B572987
theorem B513103 : Blo 299831 513103 := bstep (se 1 (by rfl) ⟨384827, by rfl⟩ : syracuseStep 513103 = 769655) B769655
theorem B676943 : Blo 299831 676943 := bstep (se 1 (by rfl) ⟨507707, by rfl⟩ : syracuseStep 676943 = 1015415) B1015415
theorem B4871339 : Blo 299831 4871339 := bstep (se 1 (by rfl) ⟨3653504, by rfl⟩ : syracuseStep 4871339 = 7307009) B7307009
theorem B382315 : Blo 299831 382315 := bstep (se 1 (by rfl) ⟨286736, by rfl⟩ : syracuseStep 382315 = 573473) B573473
theorem B677339 : Blo 299831 677339 := bstep (se 1 (by rfl) ⟨508004, by rfl⟩ : syracuseStep 677339 = 1016009) B1016009
theorem B1529441 : Blo 299831 1529441 := bstep (se 2 (by rfl) ⟨573540, by rfl⟩ : syracuseStep 1529441 = 1147081) B1147081
theorem B2185019 : Blo 299831 2185019 := bstep (se 1 (by rfl) ⟨1638764, by rfl⟩ : syracuseStep 2185019 = 3277529) B3277529
theorem B2578337 : Blo 299831 2578337 := bstep (se 2 (by rfl) ⟨966876, by rfl⟩ : syracuseStep 2578337 = 1933753) B1933753
theorem B677807 : Blo 299831 677807 := bstep (se 1 (by rfl) ⟨508355, by rfl⟩ : syracuseStep 677807 = 1016711) B1016711
theorem B678059 : Blo 299831 678059 := bstep (se 1 (by rfl) ⟨508544, by rfl⟩ : syracuseStep 678059 = 1017089) B1017089
theorem B1104043 : Blo 299831 1104043 := bstep (se 1 (by rfl) ⟨828032, by rfl⟩ : syracuseStep 1104043 = 1656065) B1656065
theorem B8673641 : Blo 299831 8673641 := bstep (se 2 (by rfl) ⟨3252615, by rfl⟩ : syracuseStep 8673641 = 6505231) B6505231
theorem B973181 : Blo 299831 973181 := bstep (se 3 (by rfl) ⟨182471, by rfl⟩ : syracuseStep 973181 = 364943) B364943
theorem B24697223 : Blo 299831 24697223 := bstep (se 1 (by rfl) ⟨18522917, by rfl⟩ : syracuseStep 24697223 = 37045835) B37045835
theorem B514487 : Blo 299831 514487 := bstep (se 1 (by rfl) ⟨385865, by rfl⟩ : syracuseStep 514487 = 771731) B771731
theorem B383611 : Blo 299831 383611 := bstep (se 1 (by rfl) ⟨287708, by rfl⟩ : syracuseStep 383611 = 575417) B575417
theorem B678599 : Blo 299831 678599 := bstep (se 1 (by rfl) ⟨508949, by rfl⟩ : syracuseStep 678599 = 1017899) B1017899
theorem B3496693 : Blo 299831 3496693 := bstep (se 5 (by rfl) ⟨163907, by rfl⟩ : syracuseStep 3496693 = 327815) B327815
theorem B4414283 : Blo 299831 4414283 := bstep (se 1 (by rfl) ⟨3310712, by rfl⟩ : syracuseStep 4414283 = 6621425) B6621425
theorem B482311 : Blo 299831 482311 := bstep (se 1 (by rfl) ⟨361733, by rfl⟩ : syracuseStep 482311 = 723467) B723467
theorem B1530899 : Blo 299831 1530899 := bstep (se 1 (by rfl) ⟨1148174, by rfl⟩ : syracuseStep 1530899 = 2296349) B2296349
theorem B613499 : Blo 299831 613499 := bstep (se 1 (by rfl) ⟨460124, by rfl⟩ : syracuseStep 613499 = 920249) B920249
theorem B3103991 : Blo 299831 3103991 := bstep (se 1 (by rfl) ⟨2327993, by rfl⟩ : syracuseStep 3103991 = 4655987) B4655987
theorem B449897 : Blo 299831 449897 := bstep (se 2 (by rfl) ⟨168711, by rfl⟩ : syracuseStep 449897 = 337423) B337423
theorem B449975 : Blo 299831 449975 := bstep (se 1 (by rfl) ⟨337481, by rfl⟩ : syracuseStep 449975 = 674963) B674963
theorem B450011 : Blo 299831 450011 := bstep (se 1 (by rfl) ⟨337508, by rfl⟩ : syracuseStep 450011 = 675017) B675017
theorem B3104243 : Blo 299831 3104243 := bstep (se 1 (by rfl) ⟨2328182, by rfl⟩ : syracuseStep 3104243 = 4656365) B4656365
theorem B1170983 : Blo 299831 1170983 := bstep (se 1 (by rfl) ⟨878237, by rfl⟩ : syracuseStep 1170983 = 1756475) B1756475
theorem B679463 : Blo 299831 679463 := bstep (se 1 (by rfl) ⟨509597, by rfl⟩ : syracuseStep 679463 = 1019195) B1019195
theorem B1728323 : Blo 299831 1728323 := bstep (se 1 (by rfl) ⟨1296242, by rfl⟩ : syracuseStep 1728323 = 2592485) B2592485
theorem B679787 : Blo 299831 679787 := bstep (se 1 (by rfl) ⟨509840, by rfl⟩ : syracuseStep 679787 = 1019681) B1019681
theorem B679841 : Blo 299831 679841 := bstep (se 2 (by rfl) ⟨254940, by rfl⟩ : syracuseStep 679841 = 509881) B509881
theorem B1138607 : Blo 299831 1138607 := bstep (se 1 (by rfl) ⟨853955, by rfl⟩ : syracuseStep 1138607 = 1707911) B1707911
theorem B450479 : Blo 299831 450479 := bstep (se 1 (by rfl) ⟨337859, by rfl⟩ : syracuseStep 450479 = 675719) B675719
theorem B450569 : Blo 299831 450569 := bstep (se 2 (by rfl) ⟨168963, by rfl⟩ : syracuseStep 450569 = 337927) B337927
theorem B450599 : Blo 299831 450599 := bstep (se 1 (by rfl) ⟨337949, by rfl⟩ : syracuseStep 450599 = 675899) B675899
theorem B2285657 : Blo 299831 2285657 := bstep (se 2 (by rfl) ⟨857121, by rfl⟩ : syracuseStep 2285657 = 1714243) B1714243
theorem B450683 : Blo 299831 450683 := bstep (se 1 (by rfl) ⟨338012, by rfl⟩ : syracuseStep 450683 = 676025) B676025
theorem B680183 : Blo 299831 680183 := bstep (se 1 (by rfl) ⟨510137, by rfl⟩ : syracuseStep 680183 = 1020275) B1020275
theorem B450809 : Blo 299831 450809 := bstep (se 2 (by rfl) ⟨169053, by rfl⟩ : syracuseStep 450809 = 338107) B338107
theorem B450911 : Blo 299831 450911 := bstep (se 1 (by rfl) ⟨338183, by rfl⟩ : syracuseStep 450911 = 676367) B676367
theorem B450923 : Blo 299831 450923 := bstep (se 1 (by rfl) ⟨338192, by rfl⟩ : syracuseStep 450923 = 676385) B676385
theorem B451151 : Blo 299831 451151 := bstep (se 1 (by rfl) ⟨338363, by rfl⟩ : syracuseStep 451151 = 676727) B676727
theorem B451271 : Blo 299831 451271 := bstep (se 1 (by rfl) ⟨338453, by rfl⟩ : syracuseStep 451271 = 676907) B676907
theorem B2974481 : Blo 299831 2974481 := bstep (se 2 (by rfl) ⟨1115430, by rfl⟩ : syracuseStep 2974481 = 2230861) B2230861
theorem B680777 : Blo 299831 680777 := bstep (se 2 (by rfl) ⟨255291, by rfl⟩ : syracuseStep 680777 = 510583) B510583
theorem B451433 : Blo 299831 451433 := bstep (se 2 (by rfl) ⟨169287, by rfl⟩ : syracuseStep 451433 = 338575) B338575
theorem B451511 : Blo 299831 451511 := bstep (se 1 (by rfl) ⟨338633, by rfl⟩ : syracuseStep 451511 = 677267) B677267
theorem B451547 : Blo 299831 451547 := bstep (se 1 (by rfl) ⟨338660, by rfl⟩ : syracuseStep 451547 = 677321) B677321
theorem B1139791 : Blo 299831 1139791 := bstep (se 1 (by rfl) ⟨854843, by rfl⟩ : syracuseStep 1139791 = 1709687) B1709687
theorem B320635 : Blo 299831 320635 := bstep (se 1 (by rfl) ⟨240476, by rfl⟩ : syracuseStep 320635 = 480953) B480953
theorem B452015 : Blo 299831 452015 := bstep (se 1 (by rfl) ⟨339011, by rfl⟩ : syracuseStep 452015 = 678023) B678023
theorem B452105 : Blo 299831 452105 := bstep (se 2 (by rfl) ⟨169539, by rfl⟩ : syracuseStep 452105 = 339079) B339079
theorem B2287115 : Blo 299831 2287115 := bstep (se 1 (by rfl) ⟨1715336, by rfl⟩ : syracuseStep 2287115 = 3430673) B3430673
theorem B2582027 : Blo 299831 2582027 := bstep (se 1 (by rfl) ⟨1936520, by rfl⟩ : syracuseStep 2582027 = 3873041) B3873041
theorem B17360405 : Blo 299831 17360405 := bstep (se 6 (by rfl) ⟨406884, by rfl⟩ : syracuseStep 17360405 = 813769) B813769
theorem B1140263 : Blo 299831 1140263 := bstep (se 1 (by rfl) ⟨855197, by rfl⟩ : syracuseStep 1140263 = 1710395) B1710395
theorem B452135 : Blo 299831 452135 := bstep (se 1 (by rfl) ⟨339101, by rfl⟩ : syracuseStep 452135 = 678203) B678203
theorem B681569 : Blo 299831 681569 := bstep (se 2 (by rfl) ⟨255588, by rfl⟩ : syracuseStep 681569 = 511177) B511177
theorem B452219 : Blo 299831 452219 := bstep (se 1 (by rfl) ⟨339164, by rfl⟩ : syracuseStep 452219 = 678329) B678329
theorem B1468043 : Blo 299831 1468043 := bstep (se 1 (by rfl) ⟨1101032, by rfl⟩ : syracuseStep 1468043 = 2202065) B2202065
theorem B452345 : Blo 299831 452345 := bstep (se 2 (by rfl) ⟨169629, by rfl⟩ : syracuseStep 452345 = 339259) B339259
theorem B452447 : Blo 299831 452447 := bstep (se 1 (by rfl) ⟨339335, by rfl⟩ : syracuseStep 452447 = 678671) B678671
theorem B452459 : Blo 299831 452459 := bstep (se 1 (by rfl) ⟨339344, by rfl⟩ : syracuseStep 452459 = 678689) B678689
theorem B1533815 : Blo 299831 1533815 := bstep (se 1 (by rfl) ⟨1150361, by rfl⟩ : syracuseStep 1533815 = 2300723) B2300723
theorem B321455 : Blo 299831 321455 := bstep (se 1 (by rfl) ⟨241091, by rfl⟩ : syracuseStep 321455 = 482183) B482183
theorem B681911 : Blo 299831 681911 := bstep (se 1 (by rfl) ⟨511433, by rfl⟩ : syracuseStep 681911 = 1022867) B1022867
theorem B452687 : Blo 299831 452687 := bstep (se 1 (by rfl) ⟨339515, by rfl⟩ : syracuseStep 452687 = 679031) B679031
theorem B452807 : Blo 299831 452807 := bstep (se 1 (by rfl) ⟨339605, by rfl⟩ : syracuseStep 452807 = 679211) B679211
theorem B3107159 : Blo 299831 3107159 := bstep (se 1 (by rfl) ⟨2330369, by rfl⟩ : syracuseStep 3107159 = 4660739) B4660739
theorem B452969 : Blo 299831 452969 := bstep (se 2 (by rfl) ⟨169863, by rfl⟩ : syracuseStep 452969 = 339727) B339727
theorem B453047 : Blo 299831 453047 := bstep (se 1 (by rfl) ⟨339785, by rfl⟩ : syracuseStep 453047 = 679571) B679571
theorem B453083 : Blo 299831 453083 := bstep (se 1 (by rfl) ⟨339812, by rfl⟩ : syracuseStep 453083 = 679625) B679625
theorem B1141235 : Blo 299831 1141235 := bstep (se 1 (by rfl) ⟨855926, by rfl⟩ : syracuseStep 1141235 = 1711853) B1711853
theorem B682505 : Blo 299831 682505 := bstep (se 2 (by rfl) ⟨255939, by rfl⟩ : syracuseStep 682505 = 511879) B511879
theorem B4123169 : Blo 299831 4123169 := bstep (se 2 (by rfl) ⟨1546188, by rfl⟩ : syracuseStep 4123169 = 3092377) B3092377
theorem B682847 : Blo 299831 682847 := bstep (se 1 (by rfl) ⟨512135, by rfl⟩ : syracuseStep 682847 = 1024271) B1024271
theorem B453551 : Blo 299831 453551 := bstep (se 1 (by rfl) ⟨340163, by rfl⟩ : syracuseStep 453551 = 680327) B680327
theorem B453641 : Blo 299831 453641 := bstep (se 2 (by rfl) ⟨170115, by rfl⟩ : syracuseStep 453641 = 340231) B340231
theorem B683027 : Blo 299831 683027 := bstep (se 1 (by rfl) ⟨512270, by rfl⟩ : syracuseStep 683027 = 1024541) B1024541
theorem B453671 : Blo 299831 453671 := bstep (se 1 (by rfl) ⟨340253, by rfl⟩ : syracuseStep 453671 = 680507) B680507
theorem B453755 : Blo 299831 453755 := bstep (se 1 (by rfl) ⟨340316, by rfl⟩ : syracuseStep 453755 = 680633) B680633
theorem B1830059 : Blo 299831 1830059 := bstep (se 1 (by rfl) ⟨1372544, by rfl⟩ : syracuseStep 1830059 = 2745089) B2745089
theorem B453881 : Blo 299831 453881 := bstep (se 2 (by rfl) ⟨170205, by rfl⟩ : syracuseStep 453881 = 340411) B340411
theorem B453983 : Blo 299831 453983 := bstep (se 1 (by rfl) ⟨340487, by rfl⟩ : syracuseStep 453983 = 680975) B680975
theorem B683369 : Blo 299831 683369 := bstep (se 2 (by rfl) ⟨256263, by rfl⟩ : syracuseStep 683369 = 512527) B512527
theorem B453995 : Blo 299831 453995 := bstep (se 1 (by rfl) ⟨340496, by rfl⟩ : syracuseStep 453995 = 680993) B680993
theorem B2289059 : Blo 299831 2289059 := bstep (se 1 (by rfl) ⟨1716794, by rfl⟩ : syracuseStep 2289059 = 3433589) B3433589
theorem B454223 : Blo 299831 454223 := bstep (se 1 (by rfl) ⟨340667, by rfl⟩ : syracuseStep 454223 = 681335) B681335
theorem B913085 : Blo 299831 913085 := bstep (se 3 (by rfl) ⟨171203, by rfl⟩ : syracuseStep 913085 = 342407) B342407
theorem B454343 : Blo 299831 454343 := bstep (se 1 (by rfl) ⟨340757, by rfl⟩ : syracuseStep 454343 = 681515) B681515
theorem B7728857 : Blo 299831 7728857 := bstep (se 2 (by rfl) ⟨2898321, by rfl⟩ : syracuseStep 7728857 = 5796643) B5796643
theorem B454505 : Blo 299831 454505 := bstep (se 2 (by rfl) ⟨170439, by rfl⟩ : syracuseStep 454505 = 340879) B340879
theorem B454583 : Blo 299831 454583 := bstep (se 1 (by rfl) ⟨340937, by rfl⟩ : syracuseStep 454583 = 681875) B681875
theorem B4157369 : Blo 299831 4157369 := bstep (se 2 (by rfl) ⟨1559013, by rfl⟩ : syracuseStep 4157369 = 3118027) B3118027
theorem B454619 : Blo 299831 454619 := bstep (se 1 (by rfl) ⟨340964, by rfl⟩ : syracuseStep 454619 = 681929) B681929
theorem B815111 : Blo 299831 815111 := bstep (se 1 (by rfl) ⟨611333, by rfl⟩ : syracuseStep 815111 = 1222667) B1222667
theorem B1011959 : Blo 299831 1011959 := bstep (se 1 (by rfl) ⟨758969, by rfl⟩ : syracuseStep 1011959 = 1517939) B1517939
theorem B455087 : Blo 299831 455087 := bstep (se 1 (by rfl) ⟨341315, by rfl⟩ : syracuseStep 455087 = 682631) B682631
theorem B455177 : Blo 299831 455177 := bstep (se 2 (by rfl) ⟨170691, by rfl⟩ : syracuseStep 455177 = 341383) B341383
theorem B455207 : Blo 299831 455207 := bstep (se 1 (by rfl) ⟨341405, by rfl⟩ : syracuseStep 455207 = 682811) B682811
theorem B1012283 : Blo 299831 1012283 := bstep (se 1 (by rfl) ⟨759212, by rfl⟩ : syracuseStep 1012283 = 1518425) B1518425
theorem B455291 : Blo 299831 455291 := bstep (se 1 (by rfl) ⟨341468, by rfl⟩ : syracuseStep 455291 = 682937) B682937
theorem B455417 : Blo 299831 455417 := bstep (se 2 (by rfl) ⟨170781, by rfl⟩ : syracuseStep 455417 = 341563) B341563
theorem B1930013 : Blo 299831 1930013 := bstep (se 3 (by rfl) ⟨361877, by rfl⟩ : syracuseStep 1930013 = 723755) B723755
theorem B1012553 : Blo 299831 1012553 := bstep (se 2 (by rfl) ⟨379707, by rfl⟩ : syracuseStep 1012553 = 759415) B759415
theorem B455519 : Blo 299831 455519 := bstep (se 1 (by rfl) ⟨341639, by rfl⟩ : syracuseStep 455519 = 683279) B683279
theorem B455531 : Blo 299831 455531 := bstep (se 1 (by rfl) ⟨341648, by rfl⟩ : syracuseStep 455531 = 683297) B683297
theorem B1307801 : Blo 299831 1307801 := bstep (se 2 (by rfl) ⟨490425, by rfl⟩ : syracuseStep 1307801 = 980851) B980851
theorem B1144151 : Blo 299831 1144151 := bstep (se 1 (by rfl) ⟨858113, by rfl⟩ : syracuseStep 1144151 = 1716227) B1716227
theorem B2062045 : Blo 299831 2062045 := bstep (se 3 (by rfl) ⟨386633, by rfl⟩ : syracuseStep 2062045 = 773267) B773267
theorem B685817 : Blo 299831 685817 := bstep (se 2 (by rfl) ⟨257181, by rfl⟩ : syracuseStep 685817 = 514363) B514363
theorem B35452673 : Blo 299831 35452673 := bstep (se 2 (by rfl) ⟨13294752, by rfl⟩ : syracuseStep 35452673 = 26589505) B26589505
theorem B2291489 : Blo 299831 2291489 := bstep (se 2 (by rfl) ⟨859308, by rfl⟩ : syracuseStep 2291489 = 1718617) B1718617
theorem B817057 : Blo 299831 817057 := bstep (se 2 (by rfl) ⟨306396, by rfl⟩ : syracuseStep 817057 = 612793) B612793
theorem B1013687 : Blo 299831 1013687 := bstep (se 1 (by rfl) ⟨760265, by rfl⟩ : syracuseStep 1013687 = 1520531) B1520531
theorem B3274759 : Blo 299831 3274759 := bstep (se 1 (by rfl) ⟨2456069, by rfl⟩ : syracuseStep 3274759 = 4912139) B4912139
theorem B8976541 : Blo 299831 8976541 := bstep (se 3 (by rfl) ⟨1683101, by rfl⟩ : syracuseStep 8976541 = 3366203) B3366203
theorem B169834765 : Blo 299831 169834765 := bstep (se 3 (by rfl) ⟨31844018, by rfl⟩ : syracuseStep 169834765 = 63688037) B63688037
theorem B1014281 : Blo 299831 1014281 := bstep (se 2 (by rfl) ⟨380355, by rfl⟩ : syracuseStep 1014281 = 760711) B760711
theorem B1145441 : Blo 299831 1145441 := bstep (se 2 (by rfl) ⟨429540, by rfl⟩ : syracuseStep 1145441 = 859081) B859081
theorem B817879 : Blo 299831 817879 := bstep (se 1 (by rfl) ⟨613409, by rfl⟩ : syracuseStep 817879 = 1226819) B1226819
theorem B1375427 : Blo 299831 1375427 := bstep (se 1 (by rfl) ⟨1031570, by rfl⟩ : syracuseStep 1375427 = 2063141) B2063141
theorem B1015145 : Blo 299831 1015145 := bstep (se 2 (by rfl) ⟨380679, by rfl⟩ : syracuseStep 1015145 = 761359) B761359
theorem B4619663 : Blo 299831 4619663 := bstep (se 1 (by rfl) ⟨3464747, by rfl⟩ : syracuseStep 4619663 = 6929495) B6929495
theorem B67927853 : Blo 299831 67927853 := bstep (se 3 (by rfl) ⟨12736472, by rfl⟩ : syracuseStep 67927853 = 25472945) B25472945
theorem B1933217 : Blo 299831 1933217 := bstep (se 2 (by rfl) ⟨724956, by rfl⟩ : syracuseStep 1933217 = 1449913) B1449913
theorem B1015739 : Blo 299831 1015739 := bstep (se 1 (by rfl) ⟨761804, by rfl⟩ : syracuseStep 1015739 = 1523609) B1523609
theorem B1016171 : Blo 299831 1016171 := bstep (se 1 (by rfl) ⟨762128, by rfl⟩ : syracuseStep 1016171 = 1524257) B1524257
theorem B1016441 : Blo 299831 1016441 := bstep (se 2 (by rfl) ⟨381165, by rfl⟩ : syracuseStep 1016441 = 762331) B762331
theorem B656047 : Blo 299831 656047 := bstep (se 1 (by rfl) ⟨492035, by rfl⟩ : syracuseStep 656047 = 984071) B984071
theorem B1639111 : Blo 299831 1639111 := bstep (se 1 (by rfl) ⟨1229333, by rfl⟩ : syracuseStep 1639111 = 2458667) B2458667
theorem B427513 : Blo 299831 427513 := bstep (se 2 (by rfl) ⟨160317, by rfl⟩ : syracuseStep 427513 = 320635) B320635
theorem B853865 : Blo 299831 853865 := bstep (se 2 (by rfl) ⟨320199, by rfl⟩ : syracuseStep 853865 = 640399) B640399
theorem B854297 : Blo 299831 854297 := bstep (se 2 (by rfl) ⟨320361, by rfl⟩ : syracuseStep 854297 = 640723) B640723
theorem B1018223 : Blo 299831 1018223 := bstep (se 1 (by rfl) ⟨763667, by rfl⟩ : syracuseStep 1018223 = 1527335) B1527335
theorem B1673597 : Blo 299831 1673597 := bstep (se 3 (by rfl) ⟨313799, by rfl⟩ : syracuseStep 1673597 = 627599) B627599
theorem B2919235 : Blo 299831 2919235 := bstep (se 1 (by rfl) ⟨2189426, by rfl⟩ : syracuseStep 2919235 = 4378853) B4378853
theorem B3279953 : Blo 299831 3279953 := bstep (se 2 (by rfl) ⟨1229982, by rfl⟩ : syracuseStep 3279953 = 2459965) B2459965
theorem B3247559 : Blo 299831 3247559 := bstep (se 1 (by rfl) ⟨2435669, by rfl⟩ : syracuseStep 3247559 = 4871339) B4871339
theorem B11079301 : Blo 299831 11079301 := bstep (se 4 (by rfl) ⟨1038684, by rfl⟩ : syracuseStep 11079301 = 2077369) B2077369
theorem B1019627 : Blo 299831 1019627 := bstep (se 1 (by rfl) ⟨764720, by rfl⟩ : syracuseStep 1019627 = 1529441) B1529441
theorem B855937 : Blo 299831 855937 := bstep (se 2 (by rfl) ⟨320976, by rfl⟩ : syracuseStep 855937 = 641953) B641953
theorem B2363755 : Blo 299831 2363755 := bstep (se 1 (by rfl) ⟨1772816, by rfl⟩ : syracuseStep 2363755 = 3545633) B3545633
theorem B6558083 : Blo 299831 6558083 := bstep (se 1 (by rfl) ⟨4918562, by rfl⟩ : syracuseStep 6558083 = 9837125) B9837125
theorem B1380827 : Blo 299831 1380827 := bstep (se 1 (by rfl) ⟨1035620, by rfl⟩ : syracuseStep 1380827 = 2071241) B2071241
theorem B1020599 : Blo 299831 1020599 := bstep (se 1 (by rfl) ⟨765449, by rfl⟩ : syracuseStep 1020599 = 1530899) B1530899
theorem B2069327 : Blo 299831 2069327 := bstep (se 1 (by rfl) ⟨1551995, by rfl⟩ : syracuseStep 2069327 = 3103991) B3103991
theorem B299931 : Blo 299831 299931 := bstep (se 1 (by rfl) ⟨224948, by rfl⟩ : syracuseStep 299931 = 449897) B449897
theorem B299983 : Blo 299831 299983 := bstep (se 1 (by rfl) ⟨224987, by rfl⟩ : syracuseStep 299983 = 449975) B449975
theorem B300007 : Blo 299831 300007 := bstep (se 1 (by rfl) ⟨225005, by rfl⟩ : syracuseStep 300007 = 450011) B450011
theorem B2069495 : Blo 299831 2069495 := bstep (se 1 (by rfl) ⟨1552121, by rfl⟩ : syracuseStep 2069495 = 3104243) B3104243
theorem B857213 : Blo 299831 857213 := bstep (se 3 (by rfl) ⟨160727, by rfl⟩ : syracuseStep 857213 = 321455) B321455
theorem B3282065 : Blo 299831 3282065 := bstep (se 2 (by rfl) ⟨1230774, by rfl⟩ : syracuseStep 3282065 = 2461549) B2461549
theorem B1152215 : Blo 299831 1152215 := bstep (se 1 (by rfl) ⟨864161, by rfl⟩ : syracuseStep 1152215 = 1728323) B1728323
theorem B759071 : Blo 299831 759071 := bstep (se 1 (by rfl) ⟨569303, by rfl⟩ : syracuseStep 759071 = 1138607) B1138607
theorem B300319 : Blo 299831 300319 := bstep (se 1 (by rfl) ⟨225239, by rfl⟩ : syracuseStep 300319 = 450479) B450479
theorem B300379 : Blo 299831 300379 := bstep (se 1 (by rfl) ⟨225284, by rfl⟩ : syracuseStep 300379 = 450569) B450569
theorem B300399 : Blo 299831 300399 := bstep (se 1 (by rfl) ⟨225299, by rfl⟩ : syracuseStep 300399 = 450599) B450599
theorem B300455 : Blo 299831 300455 := bstep (se 1 (by rfl) ⟨225341, by rfl⟩ : syracuseStep 300455 = 450683) B450683
theorem B300539 : Blo 299831 300539 := bstep (se 1 (by rfl) ⟨225404, by rfl⟩ : syracuseStep 300539 = 450809) B450809
theorem B300607 : Blo 299831 300607 := bstep (se 1 (by rfl) ⟨225455, by rfl⟩ : syracuseStep 300607 = 450911) B450911
theorem B300615 : Blo 299831 300615 := bstep (se 1 (by rfl) ⟨225461, by rfl⟩ : syracuseStep 300615 = 450923) B450923
theorem B300767 : Blo 299831 300767 := bstep (se 1 (by rfl) ⟨225575, by rfl⟩ : syracuseStep 300767 = 451151) B451151
theorem B300847 : Blo 299831 300847 := bstep (se 1 (by rfl) ⟨225635, by rfl⟩ : syracuseStep 300847 = 451271) B451271
theorem B300955 : Blo 299831 300955 := bstep (se 1 (by rfl) ⟨225716, by rfl⟩ : syracuseStep 300955 = 451433) B451433
theorem B301007 : Blo 299831 301007 := bstep (se 1 (by rfl) ⟨225755, by rfl⟩ : syracuseStep 301007 = 451511) B451511
theorem B301031 : Blo 299831 301031 := bstep (se 1 (by rfl) ⟨225773, by rfl⟩ : syracuseStep 301031 = 451547) B451547
theorem B301343 : Blo 299831 301343 := bstep (se 1 (by rfl) ⟨226007, by rfl⟩ : syracuseStep 301343 = 452015) B452015
theorem B2300237 : Blo 299831 2300237 := bstep (se 3 (by rfl) ⟨431294, by rfl⟩ : syracuseStep 2300237 = 862589) B862589
theorem B2595149 : Blo 299831 2595149 := bstep (se 3 (by rfl) ⟨486590, by rfl⟩ : syracuseStep 2595149 = 973181) B973181
theorem B1939801 : Blo 299831 1939801 := bstep (se 2 (by rfl) ⟨727425, by rfl⟩ : syracuseStep 1939801 = 1454851) B1454851
theorem B301403 : Blo 299831 301403 := bstep (se 1 (by rfl) ⟨226052, by rfl⟩ : syracuseStep 301403 = 452105) B452105
theorem B11573603 : Blo 299831 11573603 := bstep (se 1 (by rfl) ⟨8680202, by rfl⟩ : syracuseStep 11573603 = 17360405) B17360405
theorem B760175 : Blo 299831 760175 := bstep (se 1 (by rfl) ⟨570131, by rfl⟩ : syracuseStep 760175 = 1140263) B1140263
theorem B301423 : Blo 299831 301423 := bstep (se 1 (by rfl) ⟨226067, by rfl⟩ : syracuseStep 301423 = 452135) B452135
theorem B301479 : Blo 299831 301479 := bstep (se 1 (by rfl) ⟨226109, by rfl⟩ : syracuseStep 301479 = 452219) B452219
theorem B1841591 : Blo 299831 1841591 := bstep (se 1 (by rfl) ⟨1381193, by rfl⟩ : syracuseStep 1841591 = 2762387) B2762387
theorem B301563 : Blo 299831 301563 := bstep (se 1 (by rfl) ⟨226172, by rfl⟩ : syracuseStep 301563 = 452345) B452345
theorem B301631 : Blo 299831 301631 := bstep (se 1 (by rfl) ⟨226223, by rfl⟩ : syracuseStep 301631 = 452447) B452447
theorem B301639 : Blo 299831 301639 := bstep (se 1 (by rfl) ⟨226229, by rfl⟩ : syracuseStep 301639 = 452459) B452459
theorem B1022543 : Blo 299831 1022543 := bstep (se 1 (by rfl) ⟨766907, by rfl⟩ : syracuseStep 1022543 = 1533815) B1533815
theorem B301791 : Blo 299831 301791 := bstep (se 1 (by rfl) ⟨226343, by rfl⟩ : syracuseStep 301791 = 452687) B452687
theorem B3250925 : Blo 299831 3250925 := bstep (se 3 (by rfl) ⟨609548, by rfl⟩ : syracuseStep 3250925 = 1219097) B1219097
theorem B858899 : Blo 299831 858899 := bstep (se 1 (by rfl) ⟨644174, by rfl⟩ : syracuseStep 858899 = 1288349) B1288349
theorem B301871 : Blo 299831 301871 := bstep (se 1 (by rfl) ⟨226403, by rfl⟩ : syracuseStep 301871 = 452807) B452807
theorem B2071439 : Blo 299831 2071439 := bstep (se 1 (by rfl) ⟨1553579, by rfl⟩ : syracuseStep 2071439 = 3107159) B3107159
theorem B301979 : Blo 299831 301979 := bstep (se 1 (by rfl) ⟨226484, by rfl⟩ : syracuseStep 301979 = 452969) B452969
theorem B302031 : Blo 299831 302031 := bstep (se 1 (by rfl) ⟨226523, by rfl⟩ : syracuseStep 302031 = 453047) B453047
theorem B302055 : Blo 299831 302055 := bstep (se 1 (by rfl) ⟨226541, by rfl⟩ : syracuseStep 302055 = 453083) B453083
theorem B760823 : Blo 299831 760823 := bstep (se 1 (by rfl) ⟨570617, by rfl⟩ : syracuseStep 760823 = 1141235) B1141235
theorem B859355 : Blo 299831 859355 := bstep (se 1 (by rfl) ⟨644516, by rfl⟩ : syracuseStep 859355 = 1289033) B1289033
theorem B859423 : Blo 299831 859423 := bstep (se 1 (by rfl) ⟨644567, by rfl⟩ : syracuseStep 859423 = 1289135) B1289135
theorem B302367 : Blo 299831 302367 := bstep (se 1 (by rfl) ⟨226775, by rfl⟩ : syracuseStep 302367 = 453551) B453551
theorem B302427 : Blo 299831 302427 := bstep (se 1 (by rfl) ⟨226820, by rfl⟩ : syracuseStep 302427 = 453641) B453641
theorem B302447 : Blo 299831 302447 := bstep (se 1 (by rfl) ⟨226835, by rfl⟩ : syracuseStep 302447 = 453671) B453671
theorem B302503 : Blo 299831 302503 := bstep (se 1 (by rfl) ⟨226877, by rfl⟩ : syracuseStep 302503 = 453755) B453755
theorem B1220039 : Blo 299831 1220039 := bstep (se 1 (by rfl) ⟨915029, by rfl⟩ : syracuseStep 1220039 = 1830059) B1830059
theorem B302587 : Blo 299831 302587 := bstep (se 1 (by rfl) ⟨226940, by rfl⟩ : syracuseStep 302587 = 453881) B453881
theorem B302655 : Blo 299831 302655 := bstep (se 1 (by rfl) ⟨226991, by rfl⟩ : syracuseStep 302655 = 453983) B453983
theorem B302663 : Blo 299831 302663 := bstep (se 1 (by rfl) ⟨226997, by rfl⟩ : syracuseStep 302663 = 453995) B453995
theorem B302815 : Blo 299831 302815 := bstep (se 1 (by rfl) ⟨227111, by rfl⟩ : syracuseStep 302815 = 454223) B454223
theorem B1023785 : Blo 299831 1023785 := bstep (se 2 (by rfl) ⟨383919, by rfl⟩ : syracuseStep 1023785 = 767839) B767839
theorem B302895 : Blo 299831 302895 := bstep (se 1 (by rfl) ⟨227171, by rfl⟩ : syracuseStep 302895 = 454343) B454343
theorem B5152571 : Blo 299831 5152571 := bstep (se 1 (by rfl) ⟨3864428, by rfl⟩ : syracuseStep 5152571 = 7728857) B7728857
theorem B1089409 : Blo 299831 1089409 := bstep (se 2 (by rfl) ⟨408528, by rfl⟩ : syracuseStep 1089409 = 817057) B817057
theorem B303003 : Blo 299831 303003 := bstep (se 1 (by rfl) ⟨227252, by rfl⟩ : syracuseStep 303003 = 454505) B454505
theorem B303055 : Blo 299831 303055 := bstep (se 1 (by rfl) ⟨227291, by rfl⟩ : syracuseStep 303055 = 454583) B454583
theorem B303079 : Blo 299831 303079 := bstep (se 1 (by rfl) ⟨227309, by rfl⟩ : syracuseStep 303079 = 454619) B454619
theorem B4366345 : Blo 299831 4366345 := bstep (se 2 (by rfl) ⟨1637379, by rfl⟩ : syracuseStep 4366345 = 3274759) B3274759
theorem B11968721 : Blo 299831 11968721 := bstep (se 2 (by rfl) ⟨4488270, by rfl⟩ : syracuseStep 11968721 = 8976541) B8976541
theorem B2433235 : Blo 299831 2433235 := bstep (se 1 (by rfl) ⟨1824926, by rfl⟩ : syracuseStep 2433235 = 3649853) B3649853
theorem B303391 : Blo 299831 303391 := bstep (se 1 (by rfl) ⟨227543, by rfl⟩ : syracuseStep 303391 = 455087) B455087
theorem B303451 : Blo 299831 303451 := bstep (se 1 (by rfl) ⟨227588, by rfl⟩ : syracuseStep 303451 = 455177) B455177
theorem B303471 : Blo 299831 303471 := bstep (se 1 (by rfl) ⟨227603, by rfl⟩ : syracuseStep 303471 = 455207) B455207
theorem B303527 : Blo 299831 303527 := bstep (se 1 (by rfl) ⟨227645, by rfl⟩ : syracuseStep 303527 = 455291) B455291
theorem B303611 : Blo 299831 303611 := bstep (se 1 (by rfl) ⟨227708, by rfl⟩ : syracuseStep 303611 = 455417) B455417
theorem B1286675 : Blo 299831 1286675 := bstep (se 1 (by rfl) ⟨965006, by rfl⟩ : syracuseStep 1286675 = 1930013) B1930013
theorem B1450547 : Blo 299831 1450547 := bstep (se 1 (by rfl) ⟨1087910, by rfl⟩ : syracuseStep 1450547 = 2175821) B2175821
theorem B303679 : Blo 299831 303679 := bstep (se 1 (by rfl) ⟨227759, by rfl⟩ : syracuseStep 303679 = 455519) B455519
theorem B303687 : Blo 299831 303687 := bstep (se 1 (by rfl) ⟨227765, by rfl⟩ : syracuseStep 303687 = 455531) B455531
theorem B1712785 : Blo 299831 1712785 := bstep (se 2 (by rfl) ⟨642294, by rfl⟩ : syracuseStep 1712785 = 1284589) B1284589
theorem B1843883 : Blo 299831 1843883 := bstep (se 1 (by rfl) ⟨1382912, by rfl⟩ : syracuseStep 1843883 = 2765825) B2765825
theorem B2302667 : Blo 299831 2302667 := bstep (se 1 (by rfl) ⟨1727000, by rfl⟩ : syracuseStep 2302667 = 3454001) B3454001
theorem B2433851 : Blo 299831 2433851 := bstep (se 1 (by rfl) ⟨1825388, by rfl⟩ : syracuseStep 2433851 = 3650777) B3650777
theorem B762767 : Blo 299831 762767 := bstep (se 1 (by rfl) ⟨572075, by rfl⟩ : syracuseStep 762767 = 1144151) B1144151
theorem B1090505 : Blo 299831 1090505 := bstep (se 2 (by rfl) ⟨408939, by rfl⟩ : syracuseStep 1090505 = 817879) B817879
theorem B4662257 : Blo 299831 4662257 := bstep (se 2 (by rfl) ⟨1748346, by rfl⟩ : syracuseStep 4662257 = 3496693) B3496693
theorem B23635115 : Blo 299831 23635115 := bstep (se 1 (by rfl) ⟨17726336, by rfl⟩ : syracuseStep 23635115 = 35452673) B35452673
theorem B3122621 : Blo 299831 3122621 := bstep (se 3 (by rfl) ⟨585491, by rfl⟩ : syracuseStep 3122621 = 1170983) B1170983
theorem B337351 : Blo 299831 337351 := bstep (se 1 (by rfl) ⟨253013, by rfl⟩ : syracuseStep 337351 = 506027) B506027
theorem B763627 : Blo 299831 763627 := bstep (se 1 (by rfl) ⟨572720, by rfl⟩ : syracuseStep 763627 = 1145441) B1145441
theorem B337711 : Blo 299831 337711 := bstep (se 1 (by rfl) ⟨253283, by rfl⟩ : syracuseStep 337711 = 506567) B506567
theorem B337819 : Blo 299831 337819 := bstep (se 1 (by rfl) ⟨253364, by rfl⟩ : syracuseStep 337819 = 506729) B506729
theorem B12986405 : Blo 299831 12986405 := bstep (se 4 (by rfl) ⟨1217475, by rfl⟩ : syracuseStep 12986405 = 2434951) B2434951
theorem B1452161 : Blo 299831 1452161 := bstep (se 2 (by rfl) ⟨544560, by rfl⟩ : syracuseStep 1452161 = 1089121) B1089121
theorem B338215 : Blo 299831 338215 := bstep (se 1 (by rfl) ⟨253661, by rfl⟩ : syracuseStep 338215 = 507323) B507323
theorem B338287 : Blo 299831 338287 := bstep (se 1 (by rfl) ⟨253715, by rfl⟩ : syracuseStep 338287 = 507431) B507431
theorem B1452431 : Blo 299831 1452431 := bstep (se 1 (by rfl) ⟨1089323, by rfl⟩ : syracuseStep 1452431 = 2178647) B2178647
theorem B2894291 : Blo 299831 2894291 := bstep (se 1 (by rfl) ⟨2170718, by rfl⟩ : syracuseStep 2894291 = 4341437) B4341437
theorem B338503 : Blo 299831 338503 := bstep (se 1 (by rfl) ⟨253877, by rfl⟩ : syracuseStep 338503 = 507755) B507755
theorem B1288811 : Blo 299831 1288811 := bstep (se 1 (by rfl) ⟨966608, by rfl⟩ : syracuseStep 1288811 = 1933217) B1933217
theorem B764599 : Blo 299831 764599 := bstep (se 1 (by rfl) ⟨573449, by rfl⟩ : syracuseStep 764599 = 1146899) B1146899
theorem B1845949 : Blo 299831 1845949 := bstep (se 3 (by rfl) ⟨346115, by rfl⟩ : syracuseStep 1845949 = 692231) B692231
theorem B1092523 : Blo 299831 1092523 := bstep (se 1 (by rfl) ⟨819392, by rfl⟩ : syracuseStep 1092523 = 1638785) B1638785
theorem B764903 : Blo 299831 764903 := bstep (se 1 (by rfl) ⟨573677, by rfl⟩ : syracuseStep 764903 = 1147355) B1147355
theorem B10136951 : Blo 299831 10136951 := bstep (se 1 (by rfl) ⟨7602713, by rfl⟩ : syracuseStep 10136951 = 15205427) B15205427
theorem B339367 : Blo 299831 339367 := bstep (se 1 (by rfl) ⟨254525, by rfl⟩ : syracuseStep 339367 = 509051) B509051
theorem B864047 : Blo 299831 864047 := bstep (se 1 (by rfl) ⟨648035, by rfl⟩ : syracuseStep 864047 = 1296071) B1296071
theorem B339943 : Blo 299831 339943 := bstep (se 1 (by rfl) ⟨254957, by rfl⟩ : syracuseStep 339943 = 509915) B509915
theorem B1519721 : Blo 299831 1519721 := bstep (se 2 (by rfl) ⟨569895, by rfl⟩ : syracuseStep 1519721 = 1139791) B1139791
theorem B766057 : Blo 299831 766057 := bstep (se 2 (by rfl) ⟨287271, by rfl⟩ : syracuseStep 766057 = 574543) B574543
theorem B1290451 : Blo 299831 1290451 := bstep (se 1 (by rfl) ⟨967838, by rfl⟩ : syracuseStep 1290451 = 1935677) B1935677
theorem B569767 : Blo 299831 569767 := bstep (se 1 (by rfl) ⟨427325, by rfl⟩ : syracuseStep 569767 = 854651) B854651
theorem B8663597 : Blo 299831 8663597 := bstep (se 3 (by rfl) ⟨1624424, by rfl⟩ : syracuseStep 8663597 = 3248849) B3248849
theorem B766543 : Blo 299831 766543 := bstep (se 1 (by rfl) ⟨574907, by rfl⟩ : syracuseStep 766543 = 1149815) B1149815
theorem B1520855 : Blo 299831 1520855 := bstep (se 1 (by rfl) ⟨1140641, by rfl⟩ : syracuseStep 1520855 = 2281283) B2281283
theorem B767191 : Blo 299831 767191 := bstep (se 1 (by rfl) ⟨575393, by rfl⟩ : syracuseStep 767191 = 1150787) B1150787
theorem B1225961 : Blo 299831 1225961 := bstep (se 2 (by rfl) ⟨459735, by rfl⟩ : syracuseStep 1225961 = 919471) B919471
theorem B570655 : Blo 299831 570655 := bstep (se 1 (by rfl) ⟨427991, by rfl⟩ : syracuseStep 570655 = 855983) B855983
theorem B2372903 : Blo 299831 2372903 := bstep (se 1 (by rfl) ⟨1779677, by rfl⟩ : syracuseStep 2372903 = 3559355) B3559355
theorem B767495 : Blo 299831 767495 := bstep (se 1 (by rfl) ⟨575621, by rfl⟩ : syracuseStep 767495 = 1151243) B1151243
theorem B341599 : Blo 299831 341599 := bstep (se 1 (by rfl) ⟨256199, by rfl⟩ : syracuseStep 341599 = 512399) B512399
theorem B964457 : Blo 299831 964457 := bstep (se 2 (by rfl) ⟨361671, by rfl⟩ : syracuseStep 964457 = 723343) B723343
theorem B767951 : Blo 299831 767951 := bstep (se 1 (by rfl) ⟨575963, by rfl⟩ : syracuseStep 767951 = 1151927) B1151927
theorem B5519801 : Blo 299831 5519801 := bstep (se 2 (by rfl) ⟨2069925, by rfl⟩ : syracuseStep 5519801 = 4139851) B4139851
theorem B768467 : Blo 299831 768467 := bstep (se 1 (by rfl) ⟨576350, by rfl⟩ : syracuseStep 768467 = 1152701) B1152701
theorem B1456679 : Blo 299831 1456679 := bstep (se 1 (by rfl) ⟨1092509, by rfl⟩ : syracuseStep 1456679 = 2185019) B2185019
theorem B1718891 : Blo 299831 1718891 := bstep (se 1 (by rfl) ⟨1289168, by rfl⟩ : syracuseStep 1718891 = 2578337) B2578337
theorem B5782427 : Blo 299831 5782427 := bstep (se 1 (by rfl) ⟨4336820, by rfl⟩ : syracuseStep 5782427 = 8673641) B8673641
theorem B768923 : Blo 299831 768923 := bstep (se 1 (by rfl) ⟨576692, by rfl⟩ : syracuseStep 768923 = 1153385) B1153385
theorem B16464815 : Blo 299831 16464815 := bstep (se 1 (by rfl) ⟨12348611, by rfl⟩ : syracuseStep 16464815 = 24697223) B24697223
theorem B342991 : Blo 299831 342991 := bstep (se 1 (by rfl) ⟨257243, by rfl⟩ : syracuseStep 342991 = 514487) B514487
theorem B2277395 : Blo 299831 2277395 := bstep (se 1 (by rfl) ⟨1708046, by rfl⟩ : syracuseStep 2277395 = 3416093) B3416093
theorem B1523771 : Blo 299831 1523771 := bstep (se 1 (by rfl) ⟨1142828, by rfl⟩ : syracuseStep 1523771 = 2285657) B2285657
theorem B1982987 : Blo 299831 1982987 := bstep (se 1 (by rfl) ⟨1487240, by rfl⟩ : syracuseStep 1982987 = 2974481) B2974481
theorem B1557089 : Blo 299831 1557089 := bstep (se 2 (by rfl) ⟨583908, by rfl⟩ : syracuseStep 1557089 = 1167817) B1167817
theorem B770743 : Blo 299831 770743 := bstep (se 1 (by rfl) ⟨578057, by rfl⟩ : syracuseStep 770743 = 1156115) B1156115
theorem B7455415 : Blo 299831 7455415 := bstep (se 1 (by rfl) ⟨5591561, by rfl⟩ : syracuseStep 7455415 = 11183123) B11183123
theorem B508639 : Blo 299831 508639 := bstep (se 1 (by rfl) ⟨381479, by rfl⟩ : syracuseStep 508639 = 762959) B762959
theorem B1295183 : Blo 299831 1295183 := bstep (se 1 (by rfl) ⟨971387, by rfl⟩ : syracuseStep 1295183 = 1942775) B1942775
theorem B1524743 : Blo 299831 1524743 := bstep (se 1 (by rfl) ⟨1143557, by rfl⟩ : syracuseStep 1524743 = 2287115) B2287115
theorem B1721351 : Blo 299831 1721351 := bstep (se 1 (by rfl) ⟨1291013, by rfl⟩ : syracuseStep 1721351 = 2582027) B2582027
theorem B509071 : Blo 299831 509071 := bstep (se 1 (by rfl) ⟨381803, by rfl⟩ : syracuseStep 509071 = 763607) B763607
theorem B509321 : Blo 299831 509321 := bstep (se 2 (by rfl) ⟨190995, by rfl⟩ : syracuseStep 509321 = 381991) B381991
theorem B1525229 : Blo 299831 1525229 := bstep (se 3 (by rfl) ⟨285980, by rfl⟩ : syracuseStep 1525229 = 571961) B571961
theorem B968249 : Blo 299831 968249 := bstep (se 2 (by rfl) ⟨363093, by rfl⟩ : syracuseStep 968249 = 726187) B726187
theorem B509753 : Blo 299831 509753 := bstep (se 2 (by rfl) ⟨191157, by rfl⟩ : syracuseStep 509753 = 382315) B382315
theorem B1526039 : Blo 299831 1526039 := bstep (se 1 (by rfl) ⟨1144529, by rfl⟩ : syracuseStep 1526039 = 2289059) B2289059
theorem B1296823 : Blo 299831 1296823 := bstep (se 1 (by rfl) ⟨972617, by rfl⟩ : syracuseStep 1296823 = 1945235) B1945235
theorem B608723 : Blo 299831 608723 := bstep (se 1 (by rfl) ⟨456542, by rfl⟩ : syracuseStep 608723 = 913085) B913085
theorem B2771579 : Blo 299831 2771579 := bstep (se 1 (by rfl) ⟨2078684, by rfl⟩ : syracuseStep 2771579 = 4157369) B4157369
theorem B543407 : Blo 299831 543407 := bstep (se 1 (by rfl) ⟨407555, by rfl⟩ : syracuseStep 543407 = 815111) B815111
theorem B641783 : Blo 299831 641783 := bstep (se 1 (by rfl) ⟨481337, by rfl⟩ : syracuseStep 641783 = 962675) B962675
theorem B969491 : Blo 299831 969491 := bstep (se 1 (by rfl) ⟨727118, by rfl⟩ : syracuseStep 969491 = 1454237) B1454237
theorem B674639 : Blo 299831 674639 := bstep (se 1 (by rfl) ⟨505979, by rfl⟩ : syracuseStep 674639 = 1011959) B1011959
theorem B510799 : Blo 299831 510799 := bstep (se 1 (by rfl) ⟨383099, by rfl⟩ : syracuseStep 510799 = 766199) B766199
theorem B576335 : Blo 299831 576335 := bstep (se 1 (by rfl) ⟨432251, by rfl⟩ : syracuseStep 576335 = 864503) B864503
theorem B576487 : Blo 299831 576487 := bstep (se 1 (by rfl) ⟨432365, by rfl⟩ : syracuseStep 576487 = 864731) B864731
theorem B226446353 : Blo 299831 226446353 := bstep (se 2 (by rfl) ⟨84917382, by rfl⟩ : syracuseStep 226446353 = 169834765) B169834765
theorem B674855 : Blo 299831 674855 := bstep (se 1 (by rfl) ⟨506141, by rfl⟩ : syracuseStep 674855 = 1012283) B1012283
theorem B675035 : Blo 299831 675035 := bstep (se 1 (by rfl) ⟨506276, by rfl⟩ : syracuseStep 675035 = 1012553) B1012553
theorem B675233 : Blo 299831 675233 := bstep (se 2 (by rfl) ⟨253212, by rfl⟩ : syracuseStep 675233 = 506425) B506425
theorem B871867 : Blo 299831 871867 := bstep (se 1 (by rfl) ⟨653900, by rfl⟩ : syracuseStep 871867 = 1307801) B1307801
theorem B511481 : Blo 299831 511481 := bstep (se 2 (by rfl) ⟨191805, by rfl⟩ : syracuseStep 511481 = 383611) B383611
theorem B380639 : Blo 299831 380639 := bstep (se 1 (by rfl) ⟨285479, by rfl⟩ : syracuseStep 380639 = 570959) B570959
theorem B511751 : Blo 299831 511751 := bstep (se 1 (by rfl) ⟨383813, by rfl⟩ : syracuseStep 511751 = 767627) B767627
theorem B1527659 : Blo 299831 1527659 := bstep (se 1 (by rfl) ⟨1145744, by rfl⟩ : syracuseStep 1527659 = 2291489) B2291489
theorem B675791 : Blo 299831 675791 := bstep (se 1 (by rfl) ⟨506843, by rfl⟩ : syracuseStep 675791 = 1013687) B1013687
theorem B643081 : Blo 299831 643081 := bstep (se 2 (by rfl) ⟨241155, by rfl⟩ : syracuseStep 643081 = 482311) B482311
theorem B676169 : Blo 299831 676169 := bstep (se 2 (by rfl) ⟨253563, by rfl⟩ : syracuseStep 676169 = 507127) B507127
theorem B676187 : Blo 299831 676187 := bstep (se 1 (by rfl) ⟨507140, by rfl⟩ : syracuseStep 676187 = 1014281) B1014281
theorem B971183 : Blo 299831 971183 := bstep (se 1 (by rfl) ⟨728387, by rfl⟩ : syracuseStep 971183 = 1456775) B1456775
theorem B512507 : Blo 299831 512507 := bstep (se 1 (by rfl) ⟨384380, by rfl⟩ : syracuseStep 512507 = 768761) B768761
theorem B643859 : Blo 299831 643859 := bstep (se 1 (by rfl) ⟨482894, by rfl⟩ : syracuseStep 643859 = 965789) B965789
theorem B676763 : Blo 299831 676763 := bstep (se 1 (by rfl) ⟨507572, by rfl⟩ : syracuseStep 676763 = 1015145) B1015145
theorem B676961 : Blo 299831 676961 := bstep (se 2 (by rfl) ⟨253860, by rfl⟩ : syracuseStep 676961 = 507721) B507721
theorem B677159 : Blo 299831 677159 := bstep (se 1 (by rfl) ⟨507869, by rfl⟩ : syracuseStep 677159 = 1015739) B1015739
theorem B611707 : Blo 299831 611707 := bstep (se 1 (by rfl) ⟨458780, by rfl⟩ : syracuseStep 611707 = 917561) B917561
theorem B480863 : Blo 299831 480863 := bstep (se 1 (by rfl) ⟨360647, by rfl⟩ : syracuseStep 480863 = 721295) B721295
theorem B579167 : Blo 299831 579167 := bstep (se 1 (by rfl) ⟨434375, by rfl⟩ : syracuseStep 579167 = 868751) B868751
theorem B677537 : Blo 299831 677537 := bstep (se 2 (by rfl) ⟨254076, by rfl⟩ : syracuseStep 677537 = 508153) B508153
theorem B382639 : Blo 299831 382639 := bstep (se 1 (by rfl) ⟨286979, by rfl⟩ : syracuseStep 382639 = 573959) B573959
theorem B481081 : Blo 299831 481081 := bstep (se 2 (by rfl) ⟨180405, by rfl⟩ : syracuseStep 481081 = 360811) B360811
theorem B677897 : Blo 299831 677897 := bstep (se 2 (by rfl) ⟨254211, by rfl⟩ : syracuseStep 677897 = 508423) B508423
theorem B678311 : Blo 299831 678311 := bstep (se 1 (by rfl) ⟨508733, by rfl⟩ : syracuseStep 678311 = 1017467) B1017467
theorem B678419 : Blo 299831 678419 := bstep (se 1 (by rfl) ⟨508814, by rfl⟩ : syracuseStep 678419 = 1017629) B1017629
theorem B678473 : Blo 299831 678473 := bstep (se 2 (by rfl) ⟨254427, by rfl⟩ : syracuseStep 678473 = 508855) B508855
theorem B645815 : Blo 299831 645815 := bstep (se 1 (by rfl) ⟨484361, by rfl⟩ : syracuseStep 645815 = 968723) B968723
theorem B1924013 : Blo 299831 1924013 := bstep (se 3 (by rfl) ⟨360752, by rfl⟩ : syracuseStep 1924013 = 721505) B721505
theorem B482279 : Blo 299831 482279 := bstep (se 1 (by rfl) ⟨361709, by rfl⟩ : syracuseStep 482279 = 723419) B723419
theorem B678887 : Blo 299831 678887 := bstep (se 1 (by rfl) ⟨509165, by rfl⟩ : syracuseStep 678887 = 1018331) B1018331
theorem B1105085 : Blo 299831 1105085 := bstep (se 3 (by rfl) ⟨207203, by rfl⟩ : syracuseStep 1105085 = 414407) B414407
theorem B449831 : Blo 299831 449831 := bstep (se 1 (by rfl) ⟨337373, by rfl⟩ : syracuseStep 449831 = 674747) B674747
theorem B679265 : Blo 299831 679265 := bstep (se 2 (by rfl) ⟨254724, by rfl⟩ : syracuseStep 679265 = 509449) B509449
theorem B449915 : Blo 299831 449915 := bstep (se 1 (by rfl) ⟨337436, by rfl⟩ : syracuseStep 449915 = 674873) B674873
theorem B679355 : Blo 299831 679355 := bstep (se 1 (by rfl) ⟨509516, by rfl⟩ : syracuseStep 679355 = 1019033) B1019033
theorem B613831 : Blo 299831 613831 := bstep (se 1 (by rfl) ⟨460373, by rfl⟩ : syracuseStep 613831 = 920747) B920747
theorem B450041 : Blo 299831 450041 := bstep (se 2 (by rfl) ⟨168765, by rfl⟩ : syracuseStep 450041 = 337531) B337531
theorem B1531385 : Blo 299831 1531385 := bstep (se 2 (by rfl) ⟨574269, by rfl⟩ : syracuseStep 1531385 = 1148539) B1148539
theorem B679481 : Blo 299831 679481 := bstep (se 2 (by rfl) ⟨254805, by rfl⟩ : syracuseStep 679481 = 509611) B509611
theorem B450143 : Blo 299831 450143 := bstep (se 1 (by rfl) ⟨337607, by rfl⟩ : syracuseStep 450143 = 675215) B675215
theorem B2285171 : Blo 299831 2285171 := bstep (se 1 (by rfl) ⟨1713878, by rfl⟩ : syracuseStep 2285171 = 3427757) B3427757
theorem B2580113 : Blo 299831 2580113 := bstep (se 2 (by rfl) ⟨967542, by rfl⟩ : syracuseStep 2580113 = 1935085) B1935085
theorem B450359 : Blo 299831 450359 := bstep (se 1 (by rfl) ⟨337769, by rfl⟩ : syracuseStep 450359 = 675539) B675539
theorem B581431 : Blo 299831 581431 := bstep (se 1 (by rfl) ⟨436073, by rfl⟩ : syracuseStep 581431 = 872147) B872147
theorem B1531709 : Blo 299831 1531709 := bstep (se 3 (by rfl) ⟨287195, by rfl⟩ : syracuseStep 1531709 = 574391) B574391
theorem B1925039 : Blo 299831 1925039 := bstep (se 1 (by rfl) ⟨1443779, by rfl⟩ : syracuseStep 1925039 = 2887559) B2887559
theorem B2908163 : Blo 299831 2908163 := bstep (se 1 (by rfl) ⟨2181122, by rfl⟩ : syracuseStep 2908163 = 4362245) B4362245
theorem B450665 : Blo 299831 450665 := bstep (se 2 (by rfl) ⟨168999, by rfl⟩ : syracuseStep 450665 = 337999) B337999
theorem B680147 : Blo 299831 680147 := bstep (se 1 (by rfl) ⟨510110, by rfl⟩ : syracuseStep 680147 = 1020221) B1020221
theorem B680201 : Blo 299831 680201 := bstep (se 2 (by rfl) ⟨255075, by rfl⟩ : syracuseStep 680201 = 510151) B510151
theorem B450983 : Blo 299831 450983 := bstep (se 1 (by rfl) ⟨338237, by rfl⟩ : syracuseStep 450983 = 676475) B676475
theorem B680417 : Blo 299831 680417 := bstep (se 2 (by rfl) ⟨255156, by rfl⟩ : syracuseStep 680417 = 510313) B510313
theorem B451067 : Blo 299831 451067 := bstep (se 1 (by rfl) ⟨338300, by rfl⟩ : syracuseStep 451067 = 676601) B676601
theorem B451193 : Blo 299831 451193 := bstep (se 2 (by rfl) ⟨169197, by rfl⟩ : syracuseStep 451193 = 338395) B338395
theorem B451247 : Blo 299831 451247 := bstep (se 1 (by rfl) ⟨338435, by rfl⟩ : syracuseStep 451247 = 676871) B676871
theorem B451295 : Blo 299831 451295 := bstep (se 1 (by rfl) ⟨338471, by rfl⟩ : syracuseStep 451295 = 676943) B676943
theorem B680723 : Blo 299831 680723 := bstep (se 1 (by rfl) ⟨510542, by rfl⟩ : syracuseStep 680723 = 1021085) B1021085
theorem B615323 : Blo 299831 615323 := bstep (se 1 (by rfl) ⟨461492, by rfl⟩ : syracuseStep 615323 = 922985) B922985
theorem B451559 : Blo 299831 451559 := bstep (se 1 (by rfl) ⟨338669, by rfl⟩ : syracuseStep 451559 = 677339) B677339
theorem B2286629 : Blo 299831 2286629 := bstep (se 4 (by rfl) ⟨214371, by rfl⟩ : syracuseStep 2286629 = 428743) B428743
theorem B681083 : Blo 299831 681083 := bstep (se 1 (by rfl) ⟨510812, by rfl⟩ : syracuseStep 681083 = 1021625) B1021625
theorem B451817 : Blo 299831 451817 := bstep (se 2 (by rfl) ⟨169431, by rfl⟩ : syracuseStep 451817 = 338863) B338863
theorem B681209 : Blo 299831 681209 := bstep (se 2 (by rfl) ⟨255453, by rfl⟩ : syracuseStep 681209 = 510907) B510907
theorem B451871 : Blo 299831 451871 := bstep (se 1 (by rfl) ⟨338903, by rfl⟩ : syracuseStep 451871 = 677807) B677807
theorem B681353 : Blo 299831 681353 := bstep (se 2 (by rfl) ⟨255507, by rfl⟩ : syracuseStep 681353 = 511015) B511015
theorem B452039 : Blo 299831 452039 := bstep (se 1 (by rfl) ⟨339029, by rfl⟩ : syracuseStep 452039 = 678059) B678059
theorem B18703817 : Blo 299831 18703817 := bstep (se 2 (by rfl) ⟨7013931, by rfl⟩ : syracuseStep 18703817 = 14027863) B14027863
theorem B681479 : Blo 299831 681479 := bstep (se 1 (by rfl) ⟨511109, by rfl⟩ : syracuseStep 681479 = 1022219) B1022219
theorem B9791063 : Blo 299831 9791063 := bstep (se 1 (by rfl) ⟨7343297, by rfl⟩ : syracuseStep 9791063 = 14686595) B14686595
theorem B681659 : Blo 299831 681659 := bstep (se 1 (by rfl) ⟨511244, by rfl⟩ : syracuseStep 681659 = 1022489) B1022489
theorem B485099 : Blo 299831 485099 := bstep (se 1 (by rfl) ⟨363824, by rfl⟩ : syracuseStep 485099 = 727649) B727649
theorem B452393 : Blo 299831 452393 := bstep (se 2 (by rfl) ⟨169647, by rfl⟩ : syracuseStep 452393 = 339295) B339295
theorem B452399 : Blo 299831 452399 := bstep (se 1 (by rfl) ⟨339299, by rfl⟩ : syracuseStep 452399 = 678599) B678599
theorem B681785 : Blo 299831 681785 := bstep (se 2 (by rfl) ⟨255669, by rfl⟩ : syracuseStep 681785 = 511339) B511339
theorem B2942855 : Blo 299831 2942855 := bstep (se 1 (by rfl) ⟨2207141, by rfl⟩ : syracuseStep 2942855 = 4414283) B4414283
theorem B452873 : Blo 299831 452873 := bstep (se 2 (by rfl) ⟨169827, by rfl⟩ : syracuseStep 452873 = 339655) B339655
theorem B452975 : Blo 299831 452975 := bstep (se 1 (by rfl) ⟨339731, by rfl⟩ : syracuseStep 452975 = 679463) B679463
theorem B682415 : Blo 299831 682415 := bstep (se 1 (by rfl) ⟨511811, by rfl⟩ : syracuseStep 682415 = 1023623) B1023623
theorem B682451 : Blo 299831 682451 := bstep (se 1 (by rfl) ⟨511838, by rfl⟩ : syracuseStep 682451 = 1023677) B1023677
theorem B682559 : Blo 299831 682559 := bstep (se 1 (by rfl) ⟨511919, by rfl⟩ : syracuseStep 682559 = 1023839) B1023839
theorem B453191 : Blo 299831 453191 := bstep (se 1 (by rfl) ⟨339893, by rfl⟩ : syracuseStep 453191 = 679787) B679787
theorem B453227 : Blo 299831 453227 := bstep (se 1 (by rfl) ⟨339920, by rfl⟩ : syracuseStep 453227 = 679841) B679841
theorem B682667 : Blo 299831 682667 := bstep (se 1 (by rfl) ⟨512000, by rfl⟩ : syracuseStep 682667 = 1024001) B1024001
theorem B1141523 : Blo 299831 1141523 := bstep (se 1 (by rfl) ⟨856142, by rfl⟩ : syracuseStep 1141523 = 1712285) B1712285
theorem B1534787 : Blo 299831 1534787 := bstep (se 1 (by rfl) ⟨1151090, by rfl⟩ : syracuseStep 1534787 = 2302181) B2302181
theorem B453455 : Blo 299831 453455 := bstep (se 1 (by rfl) ⟨340091, by rfl⟩ : syracuseStep 453455 = 680183) B680183
theorem B683207 : Blo 299831 683207 := bstep (se 1 (by rfl) ⟨512405, by rfl⟩ : syracuseStep 683207 = 1024811) B1024811
theorem B453851 : Blo 299831 453851 := bstep (se 1 (by rfl) ⟨340388, by rfl⟩ : syracuseStep 453851 = 680777) B680777
theorem B683387 : Blo 299831 683387 := bstep (se 1 (by rfl) ⟨512540, by rfl⟩ : syracuseStep 683387 = 1025081) B1025081
theorem B454025 : Blo 299831 454025 := bstep (se 2 (by rfl) ⟨170259, by rfl⟩ : syracuseStep 454025 = 340519) B340519
theorem B683513 : Blo 299831 683513 := bstep (se 2 (by rfl) ⟨256317, by rfl⟩ : syracuseStep 683513 = 512635) B512635
theorem B683603 : Blo 299831 683603 := bstep (se 1 (by rfl) ⟨512702, by rfl⟩ : syracuseStep 683603 = 1025405) B1025405
theorem B1535597 : Blo 299831 1535597 := bstep (se 3 (by rfl) ⟨287924, by rfl⟩ : syracuseStep 1535597 = 575849) B575849
theorem B454379 : Blo 299831 454379 := bstep (se 1 (by rfl) ⟨340784, by rfl⟩ : syracuseStep 454379 = 681569) B681569
theorem B978695 : Blo 299831 978695 := bstep (se 1 (by rfl) ⟨734021, by rfl⟩ : syracuseStep 978695 = 1468043) B1468043
theorem B454607 : Blo 299831 454607 := bstep (se 1 (by rfl) ⟨340955, by rfl⟩ : syracuseStep 454607 = 681911) B681911
theorem B684137 : Blo 299831 684137 := bstep (se 2 (by rfl) ⟨256551, by rfl⟩ : syracuseStep 684137 = 513103) B513103
theorem B455003 : Blo 299831 455003 := bstep (se 1 (by rfl) ⟨341252, by rfl⟩ : syracuseStep 455003 = 682505) B682505
theorem B2748779 : Blo 299831 2748779 := bstep (se 1 (by rfl) ⟨2061584, by rfl⟩ : syracuseStep 2748779 = 4123169) B4123169
theorem B455231 : Blo 299831 455231 := bstep (se 1 (by rfl) ⟨341423, by rfl⟩ : syracuseStep 455231 = 682847) B682847
theorem B1143467 : Blo 299831 1143467 := bstep (se 1 (by rfl) ⟨857600, by rfl⟩ : syracuseStep 1143467 = 1715201) B1715201
theorem B455351 : Blo 299831 455351 := bstep (se 1 (by rfl) ⟨341513, by rfl⟩ : syracuseStep 455351 = 683027) B683027
theorem B455579 : Blo 299831 455579 := bstep (se 1 (by rfl) ⟨341684, by rfl⟩ : syracuseStep 455579 = 683369) B683369
theorem B2749393 : Blo 299831 2749393 := bstep (se 2 (by rfl) ⟨1031022, by rfl⟩ : syracuseStep 2749393 = 2062045) B2062045
theorem B3863609 : Blo 299831 3863609 := bstep (se 2 (by rfl) ⟨1448853, by rfl⟩ : syracuseStep 3863609 = 2897707) B2897707
theorem B1012985 : Blo 299831 1012985 := bstep (se 2 (by rfl) ⟨379869, by rfl⟩ : syracuseStep 1012985 = 759739) B759739
theorem B2061607 : Blo 299831 2061607 := bstep (se 1 (by rfl) ⟨1546205, by rfl⟩ : syracuseStep 2061607 = 3092411) B3092411
theorem B3437963 : Blo 299831 3437963 := bstep (se 1 (by rfl) ⟨2578472, by rfl⟩ : syracuseStep 3437963 = 5156945) B5156945
theorem B1013255 : Blo 299831 1013255 := bstep (se 1 (by rfl) ⟨759941, by rfl⟩ : syracuseStep 1013255 = 1519883) B1519883
theorem B1472057 : Blo 299831 1472057 := bstep (se 2 (by rfl) ⟨552021, by rfl⟩ : syracuseStep 1472057 = 1104043) B1104043
theorem B1635997 : Blo 299831 1635997 := bstep (se 3 (by rfl) ⟨306749, by rfl⟩ : syracuseStep 1635997 = 613499) B613499
theorem B3667805 : Blo 299831 3667805 := bstep (se 3 (by rfl) ⟨687713, by rfl⟩ : syracuseStep 3667805 = 1375427) B1375427
theorem B686291 : Blo 299831 686291 := bstep (se 1 (by rfl) ⟨514718, by rfl⟩ : syracuseStep 686291 = 1029437) B1029437
theorem B1014227 : Blo 299831 1014227 := bstep (se 1 (by rfl) ⟨760670, by rfl⟩ : syracuseStep 1014227 = 1521341) B1521341
theorem B457211 : Blo 299831 457211 := bstep (se 1 (by rfl) ⟨342908, by rfl⟩ : syracuseStep 457211 = 685817) B685817
theorem B1014335 : Blo 299831 1014335 := bstep (se 1 (by rfl) ⟨760751, by rfl⟩ : syracuseStep 1014335 = 1521503) B1521503
theorem B2292461 : Blo 299831 2292461 := bstep (se 3 (by rfl) ⟨429836, by rfl⟩ : syracuseStep 2292461 = 859673) B859673
theorem B687095 : Blo 299831 687095 := bstep (se 1 (by rfl) ⟨515321, by rfl⟩ : syracuseStep 687095 = 1030643) B1030643
theorem B1637729 : Blo 299831 1637729 := bstep (se 2 (by rfl) ⟨614148, by rfl⟩ : syracuseStep 1637729 = 1228297) B1228297
theorem B181140941 : Blo 299831 181140941 := bstep (se 3 (by rfl) ⟨33963926, by rfl⟩ : syracuseStep 181140941 = 67927853) B67927853
theorem B1146383 : Blo 299831 1146383 := bstep (se 1 (by rfl) ⟨859787, by rfl⟩ : syracuseStep 1146383 = 1719575) B1719575
theorem B3079775 : Blo 299831 3079775 := bstep (se 1 (by rfl) ⟨2309831, by rfl⟩ : syracuseStep 3079775 = 4619663) B4619663
theorem B1015847 : Blo 299831 1015847 := bstep (se 1 (by rfl) ⟨761885, by rfl⟩ : syracuseStep 1015847 = 1523771) B1523771
theorem B3244313 : Blo 299831 3244313 := bstep (se 2 (by rfl) ⟨1216617, by rfl⟩ : syracuseStep 3244313 = 2433235) B2433235
theorem B1016495 : Blo 299831 1016495 := bstep (se 1 (by rfl) ⟨762371, by rfl⟩ : syracuseStep 1016495 = 1524743) B1524743
theorem B1147567 : Blo 299831 1147567 := bstep (se 1 (by rfl) ⟨860675, by rfl⟩ : syracuseStep 1147567 = 1721351) B1721351
theorem B1016819 : Blo 299831 1016819 := bstep (se 1 (by rfl) ⟨762614, by rfl⟩ : syracuseStep 1016819 = 1525229) B1525229
theorem B1017359 : Blo 299831 1017359 := bstep (se 1 (by rfl) ⟨763019, by rfl⟩ : syracuseStep 1017359 = 1526039) B1526039
theorem B1115731 : Blo 299831 1115731 := bstep (se 1 (by rfl) ⟨836798, by rfl⟩ : syracuseStep 1115731 = 1673597) B1673597
theorem B427855 : Blo 299831 427855 := bstep (se 1 (by rfl) ⟨320891, by rfl⟩ : syracuseStep 427855 = 641783) B641783
theorem B150964235 : Blo 299831 150964235 := bstep (se 1 (by rfl) ⟨113223176, by rfl⟩ : syracuseStep 150964235 = 226446353) B226446353
theorem B2165039 : Blo 299831 2165039 := bstep (se 1 (by rfl) ⟨1623779, by rfl⟩ : syracuseStep 2165039 = 3247559) B3247559
theorem B1018169 : Blo 299831 1018169 := bstep (se 2 (by rfl) ⟨381813, by rfl⟩ : syracuseStep 1018169 = 763627) B763627
theorem B1640861 : Blo 299831 1640861 := bstep (se 3 (by rfl) ⟨307661, by rfl⟩ : syracuseStep 1640861 = 615323) B615323
theorem B1018439 : Blo 299831 1018439 := bstep (se 1 (by rfl) ⟨763829, by rfl⟩ : syracuseStep 1018439 = 1527659) B1527659
theorem B920551 : Blo 299831 920551 := bstep (se 1 (by rfl) ⟨690413, by rfl⟩ : syracuseStep 920551 = 1380827) B1380827
theorem B429239 : Blo 299831 429239 := bstep (se 1 (by rfl) ⟨321929, by rfl⟩ : syracuseStep 429239 = 643859) B643859
theorem B1379551 : Blo 299831 1379551 := bstep (se 1 (by rfl) ⟨1034663, by rfl⟩ : syracuseStep 1379551 = 2069327) B2069327
theorem B1379663 : Blo 299831 1379663 := bstep (se 1 (by rfl) ⟨1034747, by rfl⟩ : syracuseStep 1379663 = 2069495) B2069495
theorem B1019465 : Blo 299831 1019465 := bstep (se 2 (by rfl) ⟨382299, by rfl⟩ : syracuseStep 1019465 = 764599) B764599
theorem B2461265 : Blo 299831 2461265 := bstep (se 2 (by rfl) ⟨922974, by rfl⟩ : syracuseStep 2461265 = 1845949) B1845949
theorem B1282301 : Blo 299831 1282301 := bstep (se 3 (by rfl) ⟨240431, by rfl⟩ : syracuseStep 1282301 = 480863) B480863
theorem B430543 : Blo 299831 430543 := bstep (se 1 (by rfl) ⟨322907, by rfl⟩ : syracuseStep 430543 = 645815) B645815
theorem B2167283 : Blo 299831 2167283 := bstep (se 1 (by rfl) ⟨1625462, by rfl⟩ : syracuseStep 2167283 = 3250925) B3250925
theorem B1380959 : Blo 299831 1380959 := bstep (se 1 (by rfl) ⟨1035719, by rfl⟩ : syracuseStep 1380959 = 2071439) B2071439
theorem B299887 : Blo 299831 299887 := bstep (se 1 (by rfl) ⟨224915, by rfl⟩ : syracuseStep 299887 = 449831) B449831
theorem B299943 : Blo 299831 299943 := bstep (se 1 (by rfl) ⟨224957, by rfl⟩ : syracuseStep 299943 = 449915) B449915
theorem B300027 : Blo 299831 300027 := bstep (se 1 (by rfl) ⟨225020, by rfl⟩ : syracuseStep 300027 = 450041) B450041
theorem B1020923 : Blo 299831 1020923 := bstep (se 1 (by rfl) ⟨765692, by rfl⟩ : syracuseStep 1020923 = 1531385) B1531385
theorem B300095 : Blo 299831 300095 := bstep (se 1 (by rfl) ⟨225071, by rfl⟩ : syracuseStep 300095 = 450143) B450143
theorem B300239 : Blo 299831 300239 := bstep (se 1 (by rfl) ⟨225179, by rfl⟩ : syracuseStep 300239 = 450359) B450359
theorem B1021139 : Blo 299831 1021139 := bstep (se 1 (by rfl) ⟨765854, by rfl⟩ : syracuseStep 1021139 = 1531709) B1531709
theorem B1283359 : Blo 299831 1283359 := bstep (se 1 (by rfl) ⟨962519, by rfl⟩ : syracuseStep 1283359 = 1925039) B1925039
theorem B857441 : Blo 299831 857441 := bstep (se 2 (by rfl) ⟨321540, by rfl⟩ : syracuseStep 857441 = 643081) B643081
theorem B300443 : Blo 299831 300443 := bstep (se 1 (by rfl) ⟨225332, by rfl⟩ : syracuseStep 300443 = 450665) B450665
theorem B1021409 : Blo 299831 1021409 := bstep (se 2 (by rfl) ⟨383028, by rfl⟩ : syracuseStep 1021409 = 766057) B766057
theorem B300655 : Blo 299831 300655 := bstep (se 1 (by rfl) ⟨225491, by rfl⟩ : syracuseStep 300655 = 450983) B450983
theorem B300711 : Blo 299831 300711 := bstep (se 1 (by rfl) ⟨225533, by rfl⟩ : syracuseStep 300711 = 451067) B451067
theorem B857783 : Blo 299831 857783 := bstep (se 1 (by rfl) ⟨643337, by rfl⟩ : syracuseStep 857783 = 1286675) B1286675
theorem B300795 : Blo 299831 300795 := bstep (se 1 (by rfl) ⟨225596, by rfl⟩ : syracuseStep 300795 = 451193) B451193
theorem B300831 : Blo 299831 300831 := bstep (se 1 (by rfl) ⟨225623, by rfl⟩ : syracuseStep 300831 = 451247) B451247
theorem B3151673 : Blo 299831 3151673 := bstep (se 2 (by rfl) ⟨1181877, by rfl⟩ : syracuseStep 3151673 = 2363755) B2363755
theorem B300863 : Blo 299831 300863 := bstep (se 1 (by rfl) ⟨225647, by rfl⟩ : syracuseStep 300863 = 451295) B451295
theorem B759689 : Blo 299831 759689 := bstep (se 2 (by rfl) ⟨284883, by rfl⟩ : syracuseStep 759689 = 569767) B569767
theorem B727003 : Blo 299831 727003 := bstep (se 1 (by rfl) ⟨545252, by rfl⟩ : syracuseStep 727003 = 1090505) B1090505
theorem B301039 : Blo 299831 301039 := bstep (se 1 (by rfl) ⟨225779, by rfl⟩ : syracuseStep 301039 = 451559) B451559
theorem B1022057 : Blo 299831 1022057 := bstep (se 2 (by rfl) ⟨383271, by rfl⟩ : syracuseStep 1022057 = 766543) B766543
theorem B301211 : Blo 299831 301211 := bstep (se 1 (by rfl) ⟨225908, by rfl⟩ : syracuseStep 301211 = 451817) B451817
theorem B301247 : Blo 299831 301247 := bstep (se 1 (by rfl) ⟨225935, by rfl⟩ : syracuseStep 301247 = 451871) B451871
theorem B301359 : Blo 299831 301359 := bstep (se 1 (by rfl) ⟨226019, by rfl⟩ : syracuseStep 301359 = 452039) B452039
theorem B6527375 : Blo 299831 6527375 := bstep (se 1 (by rfl) ⟨4895531, by rfl⟩ : syracuseStep 6527375 = 9791063) B9791063
theorem B301595 : Blo 299831 301595 := bstep (se 1 (by rfl) ⟨226196, by rfl⟩ : syracuseStep 301595 = 452393) B452393
theorem B301599 : Blo 299831 301599 := bstep (se 1 (by rfl) ⟨226199, by rfl⟩ : syracuseStep 301599 = 452399) B452399
theorem B8657603 : Blo 299831 8657603 := bstep (se 1 (by rfl) ⟨6493202, by rfl⟩ : syracuseStep 8657603 = 12986405) B12986405
theorem B301915 : Blo 299831 301915 := bstep (se 1 (by rfl) ⟨226436, by rfl⟩ : syracuseStep 301915 = 452873) B452873
theorem B301983 : Blo 299831 301983 := bstep (se 1 (by rfl) ⟨226487, by rfl⟩ : syracuseStep 301983 = 452975) B452975
theorem B1022921 : Blo 299831 1022921 := bstep (se 2 (by rfl) ⟨383595, by rfl⟩ : syracuseStep 1022921 = 767191) B767191
theorem B760873 : Blo 299831 760873 := bstep (se 2 (by rfl) ⟨285327, by rfl⟩ : syracuseStep 760873 = 570655) B570655
theorem B302127 : Blo 299831 302127 := bstep (se 1 (by rfl) ⟨226595, by rfl⟩ : syracuseStep 302127 = 453191) B453191
theorem B859207 : Blo 299831 859207 := bstep (se 1 (by rfl) ⟨644405, by rfl⟩ : syracuseStep 859207 = 1288811) B1288811
theorem B302151 : Blo 299831 302151 := bstep (se 1 (by rfl) ⟨226613, by rfl⟩ : syracuseStep 302151 = 453227) B453227
theorem B1449085 : Blo 299831 1449085 := bstep (se 3 (by rfl) ⟨271703, by rfl⟩ : syracuseStep 1449085 = 543407) B543407
theorem B761015 : Blo 299831 761015 := bstep (se 1 (by rfl) ⟨570761, by rfl⟩ : syracuseStep 761015 = 1141523) B1141523
theorem B1023191 : Blo 299831 1023191 := bstep (se 1 (by rfl) ⟨767393, by rfl⟩ : syracuseStep 1023191 = 1534787) B1534787
theorem B302303 : Blo 299831 302303 := bstep (se 1 (by rfl) ⟨226727, by rfl⟩ : syracuseStep 302303 = 453455) B453455
theorem B302567 : Blo 299831 302567 := bstep (se 1 (by rfl) ⟨226925, by rfl⟩ : syracuseStep 302567 = 453851) B453851
theorem B6757967 : Blo 299831 6757967 := bstep (se 1 (by rfl) ⟨5068475, by rfl⟩ : syracuseStep 6757967 = 10136951) B10136951
theorem B302683 : Blo 299831 302683 := bstep (se 1 (by rfl) ⟨227012, by rfl⟩ : syracuseStep 302683 = 454025) B454025
theorem B1023731 : Blo 299831 1023731 := bstep (se 1 (by rfl) ⟨767798, by rfl⟩ : syracuseStep 1023731 = 1535597) B1535597
theorem B302919 : Blo 299831 302919 := bstep (se 1 (by rfl) ⟨227189, by rfl⟩ : syracuseStep 302919 = 454379) B454379
theorem B1286077 : Blo 299831 1286077 := bstep (se 3 (by rfl) ⟨241139, by rfl⟩ : syracuseStep 1286077 = 482279) B482279
theorem B303071 : Blo 299831 303071 := bstep (se 1 (by rfl) ⟨227303, by rfl⟩ : syracuseStep 303071 = 454607) B454607
theorem B303335 : Blo 299831 303335 := bstep (se 1 (by rfl) ⟨227501, by rfl⟩ : syracuseStep 303335 = 455003) B455003
theorem B5775731 : Blo 299831 5775731 := bstep (se 1 (by rfl) ⟨4331798, by rfl⟩ : syracuseStep 5775731 = 8663597) B8663597
theorem B303487 : Blo 299831 303487 := bstep (se 1 (by rfl) ⟨227615, by rfl⟩ : syracuseStep 303487 = 455231) B455231
theorem B762311 : Blo 299831 762311 := bstep (se 1 (by rfl) ⟨571733, by rfl⟩ : syracuseStep 762311 = 1143467) B1143467
theorem B303567 : Blo 299831 303567 := bstep (se 1 (by rfl) ⟨227675, by rfl⟩ : syracuseStep 303567 = 455351) B455351
theorem B303719 : Blo 299831 303719 := bstep (se 1 (by rfl) ⟨227789, by rfl⟩ : syracuseStep 303719 = 455579) B455579
theorem B1581935 : Blo 299831 1581935 := bstep (se 1 (by rfl) ⟨1186451, by rfl⟩ : syracuseStep 1581935 = 2372903) B2372903
theorem B3679867 : Blo 299831 3679867 := bstep (se 1 (by rfl) ⟨2759900, by rfl⟩ : syracuseStep 3679867 = 5519801) B5519801
theorem B304807 : Blo 299831 304807 := bstep (se 1 (by rfl) ⟨228605, by rfl⟩ : syracuseStep 304807 = 457211) B457211
theorem B2304125 : Blo 299831 2304125 := bstep (se 3 (by rfl) ⟨432023, by rfl⟩ : syracuseStep 2304125 = 864047) B864047
theorem B1091819 : Blo 299831 1091819 := bstep (se 1 (by rfl) ⟨818864, by rfl⟩ : syracuseStep 1091819 = 1637729) B1637729
theorem B120760627 : Blo 299831 120760627 := bstep (se 1 (by rfl) ⟨90570470, by rfl⟩ : syracuseStep 120760627 = 181140941) B181140941
theorem B764255 : Blo 299831 764255 := bstep (se 1 (by rfl) ⟨573191, by rfl⟩ : syracuseStep 764255 = 1146383) B1146383
theorem B1452545 : Blo 299831 1452545 := bstep (se 2 (by rfl) ⟨544704, by rfl⟩ : syracuseStep 1452545 = 1089409) B1089409
theorem B1518263 : Blo 299831 1518263 := bstep (se 1 (by rfl) ⟨1138697, by rfl⟩ : syracuseStep 1518263 = 2277395) B2277395
theorem B1321991 : Blo 299831 1321991 := bstep (se 1 (by rfl) ⟨991493, by rfl⟩ : syracuseStep 1321991 = 1982987) B1982987
theorem B863455 : Blo 299831 863455 := bstep (se 1 (by rfl) ⟨647591, by rfl⟩ : syracuseStep 863455 = 1295183) B1295183
theorem B1027657 : Blo 299831 1027657 := bstep (se 2 (by rfl) ⟨385371, by rfl⟩ : syracuseStep 1027657 = 770743) B770743
theorem B9940553 : Blo 299831 9940553 := bstep (se 2 (by rfl) ⟨3727707, by rfl⟩ : syracuseStep 9940553 = 7455415) B7455415
theorem B339547 : Blo 299831 339547 := bstep (se 1 (by rfl) ⟨254660, by rfl⟩ : syracuseStep 339547 = 509321) B509321
theorem B339835 : Blo 299831 339835 := bstep (se 1 (by rfl) ⟨254876, by rfl⟩ : syracuseStep 339835 = 509753) B509753
theorem B569243 : Blo 299831 569243 := bstep (se 1 (by rfl) ⟨426932, by rfl⟩ : syracuseStep 569243 = 853865) B853865
theorem B569531 : Blo 299831 569531 := bstep (se 1 (by rfl) ⟨427148, by rfl⟩ : syracuseStep 569531 = 854297) B854297
theorem B405815 : Blo 299831 405815 := bstep (se 1 (by rfl) ⟨304361, by rfl⟩ : syracuseStep 405815 = 608723) B608723
theorem B1847719 : Blo 299831 1847719 := bstep (se 1 (by rfl) ⟨1385789, by rfl⟩ : syracuseStep 1847719 = 2771579) B2771579
theorem B570017 : Blo 299831 570017 := bstep (se 2 (by rfl) ⟨213756, by rfl⟩ : syracuseStep 570017 = 427513) B427513
theorem B340987 : Blo 299831 340987 := bstep (se 1 (by rfl) ⟨255740, by rfl⟩ : syracuseStep 340987 = 511481) B511481
theorem B341167 : Blo 299831 341167 := bstep (se 1 (by rfl) ⟨255875, by rfl⟩ : syracuseStep 341167 = 511751) B511751
theorem B12432685 : Blo 299831 12432685 := bstep (se 3 (by rfl) ⟨2331128, by rfl⟩ : syracuseStep 12432685 = 4662257) B4662257
theorem B4372055 : Blo 299831 4372055 := bstep (se 1 (by rfl) ⟨3279041, by rfl⟩ : syracuseStep 4372055 = 6558083) B6558083
theorem B341671 : Blo 299831 341671 := bstep (se 1 (by rfl) ⟨256253, by rfl⟩ : syracuseStep 341671 = 512507) B512507
theorem B571475 : Blo 299831 571475 := bstep (se 1 (by rfl) ⟨428606, by rfl⟩ : syracuseStep 571475 = 857213) B857213
theorem B768143 : Blo 299831 768143 := bstep (se 1 (by rfl) ⟨576107, by rfl⟩ : syracuseStep 768143 = 1152215) B1152215
theorem B506047 : Blo 299831 506047 := bstep (se 1 (by rfl) ⟨379535, by rfl⟩ : syracuseStep 506047 = 759071) B759071
theorem B1456697 : Blo 299831 1456697 := bstep (se 2 (by rfl) ⟨546261, by rfl⟩ : syracuseStep 1456697 = 1092523) B1092523
theorem B768649 : Blo 299831 768649 := bstep (se 2 (by rfl) ⟨288243, by rfl⟩ : syracuseStep 768649 = 576487) B576487
theorem B7715735 : Blo 299831 7715735 := bstep (se 1 (by rfl) ⟨5786801, by rfl⟩ : syracuseStep 7715735 = 11573603) B11573603
theorem B506783 : Blo 299831 506783 := bstep (se 1 (by rfl) ⟨380087, by rfl⟩ : syracuseStep 506783 = 760175) B760175
theorem B1227727 : Blo 299831 1227727 := bstep (se 1 (by rfl) ⟨920795, by rfl⟩ : syracuseStep 1227727 = 1841591) B1841591
theorem B572599 : Blo 299831 572599 := bstep (se 1 (by rfl) ⟨429449, by rfl⟩ : syracuseStep 572599 = 858899) B858899
theorem B507215 : Blo 299831 507215 := bstep (se 1 (by rfl) ⟨380411, by rfl⟩ : syracuseStep 507215 = 760823) B760823
theorem B736723 : Blo 299831 736723 := bstep (se 1 (by rfl) ⟨552542, by rfl⟩ : syracuseStep 736723 = 1105085) B1105085
theorem B572903 : Blo 299831 572903 := bstep (se 1 (by rfl) ⟨429677, by rfl⟩ : syracuseStep 572903 = 859355) B859355
theorem B1523447 : Blo 299831 1523447 := bstep (se 1 (by rfl) ⟨1142585, by rfl⟩ : syracuseStep 1523447 = 2285171) B2285171
theorem B1720075 : Blo 299831 1720075 := bstep (se 1 (by rfl) ⟨1290056, by rfl⟩ : syracuseStep 1720075 = 2580113) B2580113
theorem B7979147 : Blo 299831 7979147 := bstep (se 1 (by rfl) ⟨5984360, by rfl⟩ : syracuseStep 7979147 = 11968721) B11968721
theorem B1720601 : Blo 299831 1720601 := bstep (se 2 (by rfl) ⟨645225, by rfl⟩ : syracuseStep 1720601 = 1290451) B1290451
theorem B967031 : Blo 299831 967031 := bstep (se 1 (by rfl) ⟨725273, by rfl⟩ : syracuseStep 967031 = 1450547) B1450547
theorem B1229255 : Blo 299831 1229255 := bstep (se 1 (by rfl) ⟨921941, by rfl⟩ : syracuseStep 1229255 = 1843883) B1843883
theorem B1622567 : Blo 299831 1622567 := bstep (se 1 (by rfl) ⟨1216925, by rfl⟩ : syracuseStep 1622567 = 2433851) B2433851
theorem B508511 : Blo 299831 508511 := bstep (se 1 (by rfl) ⟨381383, by rfl⟩ : syracuseStep 508511 = 762767) B762767
theorem B1524419 : Blo 299831 1524419 := bstep (se 1 (by rfl) ⟨1143314, by rfl⟩ : syracuseStep 1524419 = 2286629) B2286629
theorem B2081747 : Blo 299831 2081747 := bstep (se 1 (by rfl) ⟨1561310, by rfl⟩ : syracuseStep 2081747 = 3122621) B3122621
theorem B12469211 : Blo 299831 12469211 := bstep (se 1 (by rfl) ⟨9351908, by rfl⟩ : syracuseStep 12469211 = 18703817) B18703817
theorem B968107 : Blo 299831 968107 := bstep (se 1 (by rfl) ⟨726080, by rfl⟩ : syracuseStep 968107 = 1452161) B1452161
theorem B968287 : Blo 299831 968287 := bstep (se 1 (by rfl) ⟨726215, by rfl⟩ : syracuseStep 968287 = 1452431) B1452431
theorem B509935 : Blo 299831 509935 := bstep (se 1 (by rfl) ⟨382451, by rfl⟩ : syracuseStep 509935 = 764903) B764903
theorem B2181329 : Blo 299831 2181329 := bstep (se 2 (by rfl) ⟨817998, by rfl⟩ : syracuseStep 2181329 = 1635997) B1635997
theorem B510185 : Blo 299831 510185 := bstep (se 2 (by rfl) ⟨191319, by rfl⟩ : syracuseStep 510185 = 382639) B382639
theorem B641441 : Blo 299831 641441 := bstep (se 2 (by rfl) ⟨240540, by rfl⟩ : syracuseStep 641441 = 481081) B481081
theorem B5130701 : Blo 299831 5130701 := bstep (se 3 (by rfl) ⟨962006, by rfl⟩ : syracuseStep 5130701 = 1924013) B1924013
theorem B2575739 : Blo 299831 2575739 := bstep (se 1 (by rfl) ⟨1931804, by rfl⟩ : syracuseStep 2575739 = 3863609) B3863609
theorem B675323 : Blo 299831 675323 := bstep (se 1 (by rfl) ⟨506492, by rfl⟩ : syracuseStep 675323 = 1012985) B1012985
theorem B675503 : Blo 299831 675503 := bstep (se 1 (by rfl) ⟨506627, by rfl⟩ : syracuseStep 675503 = 1013255) B1013255
theorem B511663 : Blo 299831 511663 := bstep (se 1 (by rfl) ⟨383747, by rfl⟩ : syracuseStep 511663 = 767495) B767495
theorem B2445203 : Blo 299831 2445203 := bstep (se 1 (by rfl) ⟨1833902, by rfl⟩ : syracuseStep 2445203 = 3667805) B3667805
theorem B642971 : Blo 299831 642971 := bstep (se 1 (by rfl) ⟨482228, by rfl⟩ : syracuseStep 642971 = 964457) B964457
theorem B511967 : Blo 299831 511967 := bstep (se 1 (by rfl) ⟨383975, by rfl⟩ : syracuseStep 511967 = 767951) B767951
theorem B676151 : Blo 299831 676151 := bstep (se 1 (by rfl) ⟨507113, by rfl⟩ : syracuseStep 676151 = 1014227) B1014227
theorem B512311 : Blo 299831 512311 := bstep (se 1 (by rfl) ⟨384233, by rfl⟩ : syracuseStep 512311 = 768467) B768467
theorem B971119 : Blo 299831 971119 := bstep (se 1 (by rfl) ⟨728339, by rfl⟩ : syracuseStep 971119 = 1456679) B1456679
theorem B676223 : Blo 299831 676223 := bstep (se 1 (by rfl) ⟨507167, by rfl⟩ : syracuseStep 676223 = 1014335) B1014335
theorem B1528307 : Blo 299831 1528307 := bstep (se 1 (by rfl) ⟨1146230, by rfl⟩ : syracuseStep 1528307 = 2292461) B2292461
theorem B3854951 : Blo 299831 3854951 := bstep (se 1 (by rfl) ⟨2891213, by rfl⟩ : syracuseStep 3854951 = 5782427) B5782427
theorem B512615 : Blo 299831 512615 := bstep (se 1 (by rfl) ⟨384461, by rfl⟩ : syracuseStep 512615 = 768923) B768923
theorem B2053183 : Blo 299831 2053183 := bstep (se 1 (by rfl) ⟨1539887, by rfl⟩ : syracuseStep 2053183 = 3079775) B3079775
theorem B775241 : Blo 299831 775241 := bstep (se 2 (by rfl) ⟨290715, by rfl⟩ : syracuseStep 775241 = 581431) B581431
theorem B7755101 : Blo 299831 7755101 := bstep (se 3 (by rfl) ⟨1454081, by rfl⟩ : syracuseStep 7755101 = 2908163) B2908163
theorem B5821793 : Blo 299831 5821793 := bstep (se 2 (by rfl) ⟨2183172, by rfl⟩ : syracuseStep 5821793 = 4366345) B4366345
theorem B677447 : Blo 299831 677447 := bstep (se 1 (by rfl) ⟨508085, by rfl⟩ : syracuseStep 677447 = 1016171) B1016171
theorem B1824365 : Blo 299831 1824365 := bstep (se 3 (by rfl) ⟨342068, by rfl⟩ : syracuseStep 1824365 = 684137) B684137
theorem B1038059 : Blo 299831 1038059 := bstep (se 1 (by rfl) ⟨778544, by rfl⟩ : syracuseStep 1038059 = 1557089) B1557089
theorem B677627 : Blo 299831 677627 := bstep (se 1 (by rfl) ⟨508220, by rfl⟩ : syracuseStep 677627 = 1016441) B1016441
theorem B2283713 : Blo 299831 2283713 := bstep (se 2 (by rfl) ⟨856392, by rfl⟩ : syracuseStep 2283713 = 1712785) B1712785
theorem B874729 : Blo 299831 874729 := bstep (se 2 (by rfl) ⟨328023, by rfl⟩ : syracuseStep 874729 = 656047) B656047
theorem B2185481 : Blo 299831 2185481 := bstep (se 2 (by rfl) ⟨819555, by rfl⟩ : syracuseStep 2185481 = 1639111) B1639111
theorem B678185 : Blo 299831 678185 := bstep (se 2 (by rfl) ⟨254319, by rfl⟩ : syracuseStep 678185 = 508639) B508639
theorem B645499 : Blo 299831 645499 := bstep (se 1 (by rfl) ⟨484124, by rfl⟩ : syracuseStep 645499 = 968249) B968249
theorem B678761 : Blo 299831 678761 := bstep (se 2 (by rfl) ⟨254535, by rfl⟩ : syracuseStep 678761 = 509071) B509071
theorem B678815 : Blo 299831 678815 := bstep (se 1 (by rfl) ⟨509111, by rfl⟩ : syracuseStep 678815 = 1018223) B1018223
theorem B646327 : Blo 299831 646327 := bstep (se 1 (by rfl) ⟨484745, by rfl⟩ : syracuseStep 646327 = 969491) B969491
theorem B449759 : Blo 299831 449759 := bstep (se 1 (by rfl) ⟨337319, by rfl⟩ : syracuseStep 449759 = 674639) B674639
theorem B449801 : Blo 299831 449801 := bstep (se 2 (by rfl) ⟨168675, by rfl⟩ : syracuseStep 449801 = 337351) B337351
theorem B449903 : Blo 299831 449903 := bstep (se 1 (by rfl) ⟨337427, by rfl⟩ : syracuseStep 449903 = 674855) B674855
theorem B2186635 : Blo 299831 2186635 := bstep (se 1 (by rfl) ⟨1639976, by rfl⟩ : syracuseStep 2186635 = 3279953) B3279953
theorem B450023 : Blo 299831 450023 := bstep (se 1 (by rfl) ⟨337517, by rfl⟩ : syracuseStep 450023 = 675035) B675035
theorem B450155 : Blo 299831 450155 := bstep (se 1 (by rfl) ⟨337616, by rfl⟩ : syracuseStep 450155 = 675233) B675233
theorem B450281 : Blo 299831 450281 := bstep (se 2 (by rfl) ⟨168855, by rfl⟩ : syracuseStep 450281 = 337711) B337711
theorem B679751 : Blo 299831 679751 := bstep (se 1 (by rfl) ⟨509813, by rfl⟩ : syracuseStep 679751 = 1019627) B1019627
theorem B450425 : Blo 299831 450425 := bstep (se 2 (by rfl) ⟨168909, by rfl⟩ : syracuseStep 450425 = 337819) B337819
theorem B450527 : Blo 299831 450527 := bstep (se 1 (by rfl) ⟨337895, by rfl⟩ : syracuseStep 450527 = 675791) B675791
theorem B450779 : Blo 299831 450779 := bstep (se 1 (by rfl) ⟨338084, by rfl⟩ : syracuseStep 450779 = 676169) B676169
theorem B450791 : Blo 299831 450791 := bstep (se 1 (by rfl) ⟨338093, by rfl⟩ : syracuseStep 450791 = 676187) B676187
theorem B647455 : Blo 299831 647455 := bstep (se 1 (by rfl) ⟨485591, by rfl⟩ : syracuseStep 647455 = 971183) B971183
theorem B450953 : Blo 299831 450953 := bstep (se 2 (by rfl) ⟨169107, by rfl⟩ : syracuseStep 450953 = 338215) B338215
theorem B680399 : Blo 299831 680399 := bstep (se 1 (by rfl) ⟨510299, by rfl⟩ : syracuseStep 680399 = 1020599) B1020599
theorem B451049 : Blo 299831 451049 := bstep (se 2 (by rfl) ⟨169143, by rfl⟩ : syracuseStep 451049 = 338287) B338287
theorem B1729097 : Blo 299831 1729097 := bstep (se 2 (by rfl) ⟨648411, by rfl⟩ : syracuseStep 1729097 = 1296823) B1296823
theorem B451175 : Blo 299831 451175 := bstep (se 1 (by rfl) ⟨338381, by rfl⟩ : syracuseStep 451175 = 676763) B676763
theorem B451307 : Blo 299831 451307 := bstep (se 1 (by rfl) ⟨338480, by rfl⟩ : syracuseStep 451307 = 676961) B676961
theorem B451337 : Blo 299831 451337 := bstep (se 2 (by rfl) ⟨169251, by rfl⟩ : syracuseStep 451337 = 338503) B338503
theorem B2188043 : Blo 299831 2188043 := bstep (se 1 (by rfl) ⟨1641032, by rfl⟩ : syracuseStep 2188043 = 3282065) B3282065
theorem B451439 : Blo 299831 451439 := bstep (se 1 (by rfl) ⟨338579, by rfl⟩ : syracuseStep 451439 = 677159) B677159
theorem B386111 : Blo 299831 386111 := bstep (se 1 (by rfl) ⟨289583, by rfl⟩ : syracuseStep 386111 = 579167) B579167
theorem B3892313 : Blo 299831 3892313 := bstep (se 2 (by rfl) ⟨1459617, by rfl⟩ : syracuseStep 3892313 = 2919235) B2919235
theorem B681065 : Blo 299831 681065 := bstep (se 2 (by rfl) ⟨255399, by rfl⟩ : syracuseStep 681065 = 510799) B510799
theorem B451691 : Blo 299831 451691 := bstep (se 1 (by rfl) ⟨338768, by rfl⟩ : syracuseStep 451691 = 677537) B677537
theorem B451931 : Blo 299831 451931 := bstep (se 1 (by rfl) ⟨338948, by rfl⟩ : syracuseStep 451931 = 677897) B677897
theorem B1533491 : Blo 299831 1533491 := bstep (se 1 (by rfl) ⟨1150118, by rfl⟩ : syracuseStep 1533491 = 2300237) B2300237
theorem B1730099 : Blo 299831 1730099 := bstep (se 1 (by rfl) ⟨1297574, by rfl⟩ : syracuseStep 1730099 = 2595149) B2595149
theorem B452207 : Blo 299831 452207 := bstep (se 1 (by rfl) ⟨339155, by rfl⟩ : syracuseStep 452207 = 678311) B678311
theorem B452279 : Blo 299831 452279 := bstep (se 1 (by rfl) ⟨339209, by rfl⟩ : syracuseStep 452279 = 678419) B678419
theorem B452315 : Blo 299831 452315 := bstep (se 1 (by rfl) ⟨339236, by rfl⟩ : syracuseStep 452315 = 678473) B678473
theorem B681695 : Blo 299831 681695 := bstep (se 1 (by rfl) ⟨511271, by rfl⟩ : syracuseStep 681695 = 1022543) B1022543
theorem B452489 : Blo 299831 452489 := bstep (se 2 (by rfl) ⟨169683, by rfl⟩ : syracuseStep 452489 = 339367) B339367
theorem B452591 : Blo 299831 452591 := bstep (se 1 (by rfl) ⟨339443, by rfl⟩ : syracuseStep 452591 = 678887) B678887
theorem B14772401 : Blo 299831 14772401 := bstep (se 2 (by rfl) ⟨5539650, by rfl⟩ : syracuseStep 14772401 = 11079301) B11079301
theorem B452843 : Blo 299831 452843 := bstep (se 1 (by rfl) ⟨339632, by rfl⟩ : syracuseStep 452843 = 679265) B679265
theorem B452903 : Blo 299831 452903 := bstep (se 1 (by rfl) ⟨339677, by rfl⟩ : syracuseStep 452903 = 679355) B679355
theorem B813359 : Blo 299831 813359 := bstep (se 1 (by rfl) ⟨610019, by rfl⟩ : syracuseStep 813359 = 1220039) B1220039
theorem B452987 : Blo 299831 452987 := bstep (se 1 (by rfl) ⟨339740, by rfl⟩ : syracuseStep 452987 = 679481) B679481
theorem B1141249 : Blo 299831 1141249 := bstep (se 2 (by rfl) ⟨427968, by rfl⟩ : syracuseStep 1141249 = 855937) B855937
theorem B682523 : Blo 299831 682523 := bstep (se 1 (by rfl) ⟨511892, by rfl⟩ : syracuseStep 682523 = 1023785) B1023785
theorem B3435047 : Blo 299831 3435047 := bstep (se 1 (by rfl) ⟨2576285, by rfl⟩ : syracuseStep 3435047 = 5152571) B5152571
theorem B453257 : Blo 299831 453257 := bstep (se 2 (by rfl) ⟨169971, by rfl⟩ : syracuseStep 453257 = 339943) B339943
theorem B453431 : Blo 299831 453431 := bstep (se 1 (by rfl) ⟨340073, by rfl⟩ : syracuseStep 453431 = 680147) B680147
theorem B453467 : Blo 299831 453467 := bstep (se 1 (by rfl) ⟨340100, by rfl⟩ : syracuseStep 453467 = 680201) B680201
theorem B453611 : Blo 299831 453611 := bstep (se 1 (by rfl) ⟨340208, by rfl⟩ : syracuseStep 453611 = 680417) B680417
theorem B1535111 : Blo 299831 1535111 := bstep (se 1 (by rfl) ⟨1151333, by rfl⟩ : syracuseStep 1535111 = 2302667) B2302667
theorem B453815 : Blo 299831 453815 := bstep (se 1 (by rfl) ⟨340361, by rfl⟩ : syracuseStep 453815 = 680723) B680723
theorem B1830109 : Blo 299831 1830109 := bstep (se 3 (by rfl) ⟨343145, by rfl⟩ : syracuseStep 1830109 = 686291) B686291
theorem B454055 : Blo 299831 454055 := bstep (se 1 (by rfl) ⟨340541, by rfl⟩ : syracuseStep 454055 = 681083) B681083
theorem B15756743 : Blo 299831 15756743 := bstep (se 1 (by rfl) ⟨11817557, by rfl⟩ : syracuseStep 15756743 = 23635115) B23635115
theorem B454139 : Blo 299831 454139 := bstep (se 1 (by rfl) ⟨340604, by rfl⟩ : syracuseStep 454139 = 681209) B681209
theorem B454235 : Blo 299831 454235 := bstep (se 1 (by rfl) ⟨340676, by rfl⟩ : syracuseStep 454235 = 681353) B681353
theorem B454319 : Blo 299831 454319 := bstep (se 1 (by rfl) ⟨340739, by rfl⟩ : syracuseStep 454319 = 681479) B681479
theorem B454439 : Blo 299831 454439 := bstep (se 1 (by rfl) ⟨340829, by rfl⟩ : syracuseStep 454439 = 681659) B681659
theorem B323399 : Blo 299831 323399 := bstep (se 1 (by rfl) ⟨242549, by rfl⟩ : syracuseStep 323399 = 485099) B485099
theorem B454523 : Blo 299831 454523 := bstep (se 1 (by rfl) ⟨340892, by rfl⟩ : syracuseStep 454523 = 681785) B681785
theorem B1961903 : Blo 299831 1961903 := bstep (se 1 (by rfl) ⟨1471427, by rfl⟩ : syracuseStep 1961903 = 2942855) B2942855
theorem B3665857 : Blo 299831 3665857 := bstep (se 2 (by rfl) ⟨1374696, by rfl⟩ : syracuseStep 3665857 = 2749393) B2749393
theorem B454943 : Blo 299831 454943 := bstep (se 1 (by rfl) ⟨341207, by rfl⟩ : syracuseStep 454943 = 682415) B682415
theorem B1929527 : Blo 299831 1929527 := bstep (se 1 (by rfl) ⟨1447145, by rfl⟩ : syracuseStep 1929527 = 2894291) B2894291
theorem B454967 : Blo 299831 454967 := bstep (se 1 (by rfl) ⟨341225, by rfl⟩ : syracuseStep 454967 = 682451) B682451
theorem B455039 : Blo 299831 455039 := bstep (se 1 (by rfl) ⟨341279, by rfl⟩ : syracuseStep 455039 = 682559) B682559
theorem B2748809 : Blo 299831 2748809 := bstep (se 2 (by rfl) ⟨1030803, by rfl⟩ : syracuseStep 2748809 = 2061607) B2061607
theorem B455111 : Blo 299831 455111 := bstep (se 1 (by rfl) ⟨341333, by rfl⟩ : syracuseStep 455111 = 682667) B682667
theorem B815609 : Blo 299831 815609 := bstep (se 2 (by rfl) ⟨305853, by rfl⟩ : syracuseStep 815609 = 611707) B611707
theorem B455465 : Blo 299831 455465 := bstep (se 2 (by rfl) ⟨170799, by rfl⟩ : syracuseStep 455465 = 341599) B341599
theorem B455471 : Blo 299831 455471 := bstep (se 1 (by rfl) ⟨341603, by rfl⟩ : syracuseStep 455471 = 683207) B683207
theorem B1536893 : Blo 299831 1536893 := bstep (se 3 (by rfl) ⟨288167, by rfl⟩ : syracuseStep 1536893 = 576335) B576335
theorem B455591 : Blo 299831 455591 := bstep (se 1 (by rfl) ⟨341693, by rfl⟩ : syracuseStep 455591 = 683387) B683387
theorem B4649957 : Blo 299831 4649957 := bstep (se 4 (by rfl) ⟨435933, by rfl⟩ : syracuseStep 4649957 = 871867) B871867
theorem B455675 : Blo 299831 455675 := bstep (se 1 (by rfl) ⟨341756, by rfl⟩ : syracuseStep 455675 = 683513) B683513
theorem B455735 : Blo 299831 455735 := bstep (se 1 (by rfl) ⟨341801, by rfl⟩ : syracuseStep 455735 = 683603) B683603
theorem B652463 : Blo 299831 652463 := bstep (se 1 (by rfl) ⟨489347, by rfl⟩ : syracuseStep 652463 = 978695) B978695
theorem B1013147 : Blo 299831 1013147 := bstep (se 1 (by rfl) ⟨759860, by rfl⟩ : syracuseStep 1013147 = 1519721) B1519721
theorem B1832519 : Blo 299831 1832519 := bstep (se 1 (by rfl) ⟨1374389, by rfl⟩ : syracuseStep 1832519 = 2748779) B2748779
theorem B2586401 : Blo 299831 2586401 := bstep (se 2 (by rfl) ⟨969900, by rfl⟩ : syracuseStep 2586401 = 1939801) B1939801
theorem B1013903 : Blo 299831 1013903 := bstep (se 1 (by rfl) ⟨760427, by rfl⟩ : syracuseStep 1013903 = 1520855) B1520855
theorem B817307 : Blo 299831 817307 := bstep (se 1 (by rfl) ⟨612980, by rfl⟩ : syracuseStep 817307 = 1225961) B1225961
theorem B2291975 : Blo 299831 2291975 := bstep (se 1 (by rfl) ⟨1718981, by rfl⟩ : syracuseStep 2291975 = 3437963) B3437963
theorem B981371 : Blo 299831 981371 := bstep (se 1 (by rfl) ⟨736028, by rfl⟩ : syracuseStep 981371 = 1472057) B1472057
theorem B457321 : Blo 299831 457321 := bstep (se 2 (by rfl) ⟨171495, by rfl⟩ : syracuseStep 457321 = 342991) B342991
theorem B1145897 : Blo 299831 1145897 := bstep (se 2 (by rfl) ⟨429711, by rfl⟩ : syracuseStep 1145897 = 859423) B859423
theorem B1145927 : Blo 299831 1145927 := bstep (se 1 (by rfl) ⟨859445, by rfl⟩ : syracuseStep 1145927 = 1718891) B1718891
theorem B1015037 : Blo 299831 1015037 := bstep (se 3 (by rfl) ⟨190319, by rfl⟩ : syracuseStep 1015037 = 380639) B380639
theorem B818441 : Blo 299831 818441 := bstep (se 2 (by rfl) ⟨306915, by rfl⟩ : syracuseStep 818441 = 613831) B613831
theorem B10976543 : Blo 299831 10976543 := bstep (se 1 (by rfl) ⟨8232407, by rfl⟩ : syracuseStep 10976543 = 16464815) B16464815
theorem B458063 : Blo 299831 458063 := bstep (se 1 (by rfl) ⟨343547, by rfl⟩ : syracuseStep 458063 = 687095) B687095
theorem B2162875 : Blo 299831 2162875 := bstep (se 1 (by rfl) ⟨1622156, by rfl⟩ : syracuseStep 2162875 = 3244313) B3244313
theorem B1147067 : Blo 299831 1147067 := bstep (se 1 (by rfl) ⟨860300, by rfl⟩ : syracuseStep 1147067 = 1720601) B1720601
theorem B819503 : Blo 299831 819503 := bstep (se 1 (by rfl) ⟨614627, by rfl⟩ : syracuseStep 819503 = 1229255) B1229255
theorem B1081711 : Blo 299831 1081711 := bstep (se 1 (by rfl) ⟨811283, by rfl⟩ : syracuseStep 1081711 = 1622567) B1622567
theorem B1016279 : Blo 299831 1016279 := bstep (se 1 (by rfl) ⟨762209, by rfl⟩ : syracuseStep 1016279 = 1524419) B1524419
theorem B1082173 : Blo 299831 1082173 := bstep (se 3 (by rfl) ⟨202907, by rfl⟩ : syracuseStep 1082173 = 405815) B405815
theorem B1443359 : Blo 299831 1443359 := bstep (se 1 (by rfl) ⟨1082519, by rfl⟩ : syracuseStep 1443359 = 2165039) B2165039
theorem B427627 : Blo 299831 427627 := bstep (se 1 (by rfl) ⟨320720, by rfl⟩ : syracuseStep 427627 = 641441) B641441
theorem B919775 : Blo 299831 919775 := bstep (se 1 (by rfl) ⟨689831, by rfl⟩ : syracuseStep 919775 = 1379663) B1379663
theorem B1640843 : Blo 299831 1640843 := bstep (se 1 (by rfl) ⟨1230632, by rfl⟩ : syracuseStep 1640843 = 2461265) B2461265
theorem B428647 : Blo 299831 428647 := bstep (se 1 (by rfl) ⟨321485, by rfl⟩ : syracuseStep 428647 = 642971) B642971
theorem B854867 : Blo 299831 854867 := bstep (se 1 (by rfl) ⟨641150, by rfl⟩ : syracuseStep 854867 = 1282301) B1282301
theorem B1018871 : Blo 299831 1018871 := bstep (se 1 (by rfl) ⟨764153, by rfl⟩ : syracuseStep 1018871 = 1528307) B1528307
theorem B920639 : Blo 299831 920639 := bstep (se 1 (by rfl) ⟨690479, by rfl⟩ : syracuseStep 920639 = 1380959) B1380959
theorem B1216243 : Blo 299831 1216243 := bstep (se 1 (by rfl) ⟨912182, by rfl⟩ : syracuseStep 1216243 = 1824365) B1824365
theorem B692039 : Blo 299831 692039 := bstep (se 1 (by rfl) ⟨519029, by rfl⟩ : syracuseStep 692039 = 1038059) B1038059
theorem B2101115 : Blo 299831 2101115 := bstep (se 1 (by rfl) ⟨1575836, by rfl⟩ : syracuseStep 2101115 = 3151673) B3151673
theorem B1839401 : Blo 299831 1839401 := bstep (se 2 (by rfl) ⟨689775, by rfl⟩ : syracuseStep 1839401 = 1379551) B1379551
theorem B1151273 : Blo 299831 1151273 := bstep (se 2 (by rfl) ⟨431727, by rfl⟩ : syracuseStep 1151273 = 863455) B863455
theorem B5771735 : Blo 299831 5771735 := bstep (se 1 (by rfl) ⟨4328801, by rfl⟩ : syracuseStep 5771735 = 8657603) B8657603
theorem B299839 : Blo 299831 299839 := bstep (se 1 (by rfl) ⟨224879, by rfl⟩ : syracuseStep 299839 = 449759) B449759
theorem B299867 : Blo 299831 299867 := bstep (se 1 (by rfl) ⟨224900, by rfl⟩ : syracuseStep 299867 = 449801) B449801
theorem B299935 : Blo 299831 299935 := bstep (se 1 (by rfl) ⟨224951, by rfl⟩ : syracuseStep 299935 = 449903) B449903
theorem B300015 : Blo 299831 300015 := bstep (se 1 (by rfl) ⟨225011, by rfl⟩ : syracuseStep 300015 = 450023) B450023
theorem B300103 : Blo 299831 300103 := bstep (se 1 (by rfl) ⟨225077, by rfl⟩ : syracuseStep 300103 = 450155) B450155
theorem B300187 : Blo 299831 300187 := bstep (se 1 (by rfl) ⟨225140, by rfl⟩ : syracuseStep 300187 = 450281) B450281
theorem B300283 : Blo 299831 300283 := bstep (se 1 (by rfl) ⟨225212, by rfl⟩ : syracuseStep 300283 = 450425) B450425
theorem B4887809 : Blo 299831 4887809 := bstep (se 2 (by rfl) ⟨1832928, by rfl⟩ : syracuseStep 4887809 = 3665857) B3665857
theorem B300351 : Blo 299831 300351 := bstep (se 1 (by rfl) ⟨225263, by rfl⟩ : syracuseStep 300351 = 450527) B450527
theorem B300519 : Blo 299831 300519 := bstep (se 1 (by rfl) ⟨225389, by rfl⟩ : syracuseStep 300519 = 450779) B450779
theorem B300527 : Blo 299831 300527 := bstep (se 1 (by rfl) ⟨225395, by rfl⟩ : syracuseStep 300527 = 450791) B450791
theorem B300635 : Blo 299831 300635 := bstep (se 1 (by rfl) ⟨225476, by rfl⟩ : syracuseStep 300635 = 450953) B450953
theorem B300699 : Blo 299831 300699 := bstep (se 1 (by rfl) ⟨225524, by rfl⟩ : syracuseStep 300699 = 451049) B451049
theorem B1152731 : Blo 299831 1152731 := bstep (se 1 (by rfl) ⟨864548, by rfl⟩ : syracuseStep 1152731 = 1729097) B1729097
theorem B300783 : Blo 299831 300783 := bstep (se 1 (by rfl) ⟨225587, by rfl⟩ : syracuseStep 300783 = 451175) B451175
theorem B300871 : Blo 299831 300871 := bstep (se 1 (by rfl) ⟨225653, by rfl⟩ : syracuseStep 300871 = 451307) B451307
theorem B300891 : Blo 299831 300891 := bstep (se 1 (by rfl) ⟨225668, by rfl⟩ : syracuseStep 300891 = 451337) B451337
theorem B2463625 : Blo 299831 2463625 := bstep (se 2 (by rfl) ⟨923859, by rfl⟩ : syracuseStep 2463625 = 1847719) B1847719
theorem B300959 : Blo 299831 300959 := bstep (se 1 (by rfl) ⟨225719, by rfl⟩ : syracuseStep 300959 = 451439) B451439
theorem B2594875 : Blo 299831 2594875 := bstep (se 1 (by rfl) ⟨1946156, by rfl⟩ : syracuseStep 2594875 = 3892313) B3892313
theorem B301127 : Blo 299831 301127 := bstep (se 1 (by rfl) ⟨225845, by rfl⟩ : syracuseStep 301127 = 451691) B451691
theorem B2168957 : Blo 299831 2168957 := bstep (se 3 (by rfl) ⟨406679, by rfl⟩ : syracuseStep 2168957 = 813359) B813359
theorem B301287 : Blo 299831 301287 := bstep (se 1 (by rfl) ⟨225965, by rfl⟩ : syracuseStep 301287 = 451931) B451931
theorem B1022327 : Blo 299831 1022327 := bstep (se 1 (by rfl) ⟨766745, by rfl⟩ : syracuseStep 1022327 = 1533491) B1533491
theorem B1153399 : Blo 299831 1153399 := bstep (se 1 (by rfl) ⟨865049, by rfl⟩ : syracuseStep 1153399 = 1730099) B1730099
theorem B301471 : Blo 299831 301471 := bstep (se 1 (by rfl) ⟨226103, by rfl⟩ : syracuseStep 301471 = 452207) B452207
theorem B301519 : Blo 299831 301519 := bstep (se 1 (by rfl) ⟨226139, by rfl⟩ : syracuseStep 301519 = 452279) B452279
theorem B301543 : Blo 299831 301543 := bstep (se 1 (by rfl) ⟨226157, by rfl⟩ : syracuseStep 301543 = 452315) B452315
theorem B301659 : Blo 299831 301659 := bstep (se 1 (by rfl) ⟨226244, by rfl⟩ : syracuseStep 301659 = 452489) B452489
theorem B301727 : Blo 299831 301727 := bstep (se 1 (by rfl) ⟨226295, by rfl⟩ : syracuseStep 301727 = 452591) B452591
theorem B301895 : Blo 299831 301895 := bstep (se 1 (by rfl) ⟨226421, by rfl⟩ : syracuseStep 301895 = 452843) B452843
theorem B727879 : Blo 299831 727879 := bstep (se 1 (by rfl) ⟨545909, by rfl⟩ : syracuseStep 727879 = 1091819) B1091819
theorem B301935 : Blo 299831 301935 := bstep (se 1 (by rfl) ⟨226451, by rfl⟩ : syracuseStep 301935 = 452903) B452903
theorem B301991 : Blo 299831 301991 := bstep (se 1 (by rfl) ⟨226493, by rfl⟩ : syracuseStep 301991 = 452987) B452987
theorem B1711145 : Blo 299831 1711145 := bstep (se 2 (by rfl) ⟨641679, by rfl⟩ : syracuseStep 1711145 = 1283359) B1283359
theorem B302171 : Blo 299831 302171 := bstep (se 1 (by rfl) ⟨226628, by rfl⟩ : syracuseStep 302171 = 453257) B453257
theorem B302287 : Blo 299831 302287 := bstep (se 1 (by rfl) ⟨226715, by rfl⟩ : syracuseStep 302287 = 453431) B453431
theorem B302311 : Blo 299831 302311 := bstep (se 1 (by rfl) ⟨226733, by rfl⟩ : syracuseStep 302311 = 453467) B453467
theorem B302407 : Blo 299831 302407 := bstep (se 1 (by rfl) ⟨226805, by rfl⟩ : syracuseStep 302407 = 453611) B453611
theorem B1023407 : Blo 299831 1023407 := bstep (se 1 (by rfl) ⟨767555, by rfl⟩ : syracuseStep 1023407 = 1535111) B1535111
theorem B302543 : Blo 299831 302543 := bstep (se 1 (by rfl) ⟨226907, by rfl⟩ : syracuseStep 302543 = 453815) B453815
theorem B302703 : Blo 299831 302703 := bstep (se 1 (by rfl) ⟨227027, by rfl⟩ : syracuseStep 302703 = 454055) B454055
theorem B302759 : Blo 299831 302759 := bstep (se 1 (by rfl) ⟨227069, by rfl⟩ : syracuseStep 302759 = 454139) B454139
theorem B6627035 : Blo 299831 6627035 := bstep (se 1 (by rfl) ⟨4970276, by rfl⟩ : syracuseStep 6627035 = 9940553) B9940553
theorem B302823 : Blo 299831 302823 := bstep (se 1 (by rfl) ⟨227117, by rfl⟩ : syracuseStep 302823 = 454235) B454235
theorem B302879 : Blo 299831 302879 := bstep (se 1 (by rfl) ⟨227159, by rfl⟩ : syracuseStep 302879 = 454319) B454319
theorem B302959 : Blo 299831 302959 := bstep (se 1 (by rfl) ⟨227219, by rfl⟩ : syracuseStep 302959 = 454439) B454439
theorem B303015 : Blo 299831 303015 := bstep (se 1 (by rfl) ⟨227261, by rfl⟩ : syracuseStep 303015 = 454523) B454523
theorem B303295 : Blo 299831 303295 := bstep (se 1 (by rfl) ⟨227471, by rfl⟩ : syracuseStep 303295 = 454943) B454943
theorem B1286351 : Blo 299831 1286351 := bstep (se 1 (by rfl) ⟨964763, by rfl⟩ : syracuseStep 1286351 = 1929527) B1929527
theorem B303311 : Blo 299831 303311 := bstep (se 1 (by rfl) ⟨227483, by rfl⟩ : syracuseStep 303311 = 454967) B454967
theorem B303359 : Blo 299831 303359 := bstep (se 1 (by rfl) ⟨227519, by rfl⟩ : syracuseStep 303359 = 455039) B455039
theorem B303407 : Blo 299831 303407 := bstep (se 1 (by rfl) ⟨227555, by rfl⟩ : syracuseStep 303407 = 455111) B455111
theorem B860665 : Blo 299831 860665 := bstep (se 2 (by rfl) ⟨322749, by rfl⟩ : syracuseStep 860665 = 645499) B645499
theorem B303643 : Blo 299831 303643 := bstep (se 1 (by rfl) ⟨227732, by rfl⟩ : syracuseStep 303643 = 455465) B455465
theorem B303647 : Blo 299831 303647 := bstep (se 1 (by rfl) ⟨227735, by rfl⟩ : syracuseStep 303647 = 455471) B455471
theorem B1024595 : Blo 299831 1024595 := bstep (se 1 (by rfl) ⟨768446, by rfl⟩ : syracuseStep 1024595 = 1536893) B1536893
theorem B303727 : Blo 299831 303727 := bstep (se 1 (by rfl) ⟨227795, by rfl⟩ : syracuseStep 303727 = 455591) B455591
theorem B303783 : Blo 299831 303783 := bstep (se 1 (by rfl) ⟨227837, by rfl⟩ : syracuseStep 303783 = 455675) B455675
theorem B303823 : Blo 299831 303823 := bstep (se 1 (by rfl) ⟨227867, by rfl⟩ : syracuseStep 303823 = 455735) B455735
theorem B434975 : Blo 299831 434975 := bstep (se 1 (by rfl) ⟨326231, by rfl⟩ : syracuseStep 434975 = 652463) B652463
theorem B1024865 : Blo 299831 1024865 := bstep (se 2 (by rfl) ⟨384324, by rfl⟩ : syracuseStep 1024865 = 768649) B768649
theorem B1221679 : Blo 299831 1221679 := bstep (se 1 (by rfl) ⟨916259, by rfl⟩ : syracuseStep 1221679 = 1832519) B1832519
theorem B763465 : Blo 299831 763465 := bstep (se 2 (by rfl) ⟨286299, by rfl⟩ : syracuseStep 763465 = 572599) B572599
theorem B861769 : Blo 299831 861769 := bstep (se 2 (by rfl) ⟨323163, by rfl⟩ : syracuseStep 861769 = 646327) B646327
theorem B337855 : Blo 299831 337855 := bstep (se 1 (by rfl) ⟨253391, by rfl⟩ : syracuseStep 337855 = 506783) B506783
theorem B763931 : Blo 299831 763931 := bstep (se 1 (by rfl) ⟨572948, by rfl⟩ : syracuseStep 763931 = 1145897) B1145897
theorem B763951 : Blo 299831 763951 := bstep (se 1 (by rfl) ⟨572963, by rfl⟩ : syracuseStep 763951 = 1145927) B1145927
theorem B862397 : Blo 299831 862397 := bstep (se 3 (by rfl) ⟨161699, by rfl⟩ : syracuseStep 862397 = 323399) B323399
theorem B7317695 : Blo 299831 7317695 := bstep (se 1 (by rfl) ⟨5488271, by rfl⟩ : syracuseStep 7317695 = 10976543) B10976543
theorem B338143 : Blo 299831 338143 := bstep (se 1 (by rfl) ⟨253607, by rfl⟩ : syracuseStep 338143 = 507215) B507215
theorem B305375 : Blo 299831 305375 := bstep (se 1 (by rfl) ⟨229031, by rfl⟩ : syracuseStep 305375 = 458063) B458063
theorem B1714769 : Blo 299831 1714769 := bstep (se 2 (by rfl) ⟨643038, by rfl⟩ : syracuseStep 1714769 = 1286077) B1286077
theorem B5319431 : Blo 299831 5319431 := bstep (se 1 (by rfl) ⟨3989573, by rfl⟩ : syracuseStep 5319431 = 7979147) B7979147
theorem B863273 : Blo 299831 863273 := bstep (se 2 (by rfl) ⟨323727, by rfl⟩ : syracuseStep 863273 = 647455) B647455
theorem B339007 : Blo 299831 339007 := bstep (se 1 (by rfl) ⟨254255, by rfl⟩ : syracuseStep 339007 = 508511) B508511
theorem B1518749 : Blo 299831 1518749 := bstep (se 3 (by rfl) ⟨284765, by rfl⟩ : syracuseStep 1518749 = 569531) B569531
theorem B4665221 : Blo 299831 4665221 := bstep (se 4 (by rfl) ⟨437364, by rfl⟩ : syracuseStep 4665221 = 874729) B874729
theorem B5779421 : Blo 299831 5779421 := bstep (se 3 (by rfl) ⟨1083641, by rfl⟩ : syracuseStep 5779421 = 2167283) B2167283
theorem B2174957 : Blo 299831 2174957 := bstep (se 3 (by rfl) ⟨407804, by rfl⟩ : syracuseStep 2174957 = 815609) B815609
theorem B100642823 : Blo 299831 100642823 := bstep (se 1 (by rfl) ⟨75482117, by rfl⟩ : syracuseStep 100642823 = 150964235) B150964235
theorem B1454219 : Blo 299831 1454219 := bstep (se 1 (by rfl) ⟨1090664, by rfl⟩ : syracuseStep 1454219 = 2181329) B2181329
theorem B340123 : Blo 299831 340123 := bstep (se 1 (by rfl) ⟨255092, by rfl⟩ : syracuseStep 340123 = 510185) B510185
theorem B1093907 : Blo 299831 1093907 := bstep (se 1 (by rfl) ⟨820430, by rfl⟩ : syracuseStep 1093907 = 1640861) B1640861
theorem B3420467 : Blo 299831 3420467 := bstep (se 1 (by rfl) ⟨2565350, by rfl⟩ : syracuseStep 3420467 = 5130701) B5130701
theorem B1520045 : Blo 299831 1520045 := bstep (se 3 (by rfl) ⟨285008, by rfl⟩ : syracuseStep 1520045 = 570017) B570017
theorem B1290809 : Blo 299831 1290809 := bstep (se 2 (by rfl) ⟨484053, by rfl⟩ : syracuseStep 1290809 = 968107) B968107
theorem B1487641 : Blo 299831 1487641 := bstep (se 2 (by rfl) ⟨557865, by rfl⟩ : syracuseStep 1487641 = 1115731) B1115731
theorem B1291049 : Blo 299831 1291049 := bstep (se 2 (by rfl) ⟨484143, by rfl⟩ : syracuseStep 1291049 = 968287) B968287
theorem B406409 : Blo 299831 406409 := bstep (se 2 (by rfl) ⟨152403, by rfl⟩ : syracuseStep 406409 = 304807) B304807
theorem B1717159 : Blo 299831 1717159 := bstep (se 1 (by rfl) ⟨1287869, by rfl⟩ : syracuseStep 1717159 = 2575739) B2575739
theorem B570473 : Blo 299831 570473 := bstep (se 2 (by rfl) ⟨213927, by rfl⟩ : syracuseStep 570473 = 427855) B427855
theorem B5551325 : Blo 299831 5551325 := bstep (se 3 (by rfl) ⟨1040873, by rfl⟩ : syracuseStep 5551325 = 2081747) B2081747
theorem B341311 : Blo 299831 341311 := bstep (se 1 (by rfl) ⟨255983, by rfl⟩ : syracuseStep 341311 = 511967) B511967
theorem B1029629 : Blo 299831 1029629 := bstep (se 3 (by rfl) ⟨193055, by rfl⟩ : syracuseStep 1029629 = 386111) B386111
theorem B2569967 : Blo 299831 2569967 := bstep (se 1 (by rfl) ⟨1927475, by rfl⟩ : syracuseStep 2569967 = 3854951) B3854951
theorem B341743 : Blo 299831 341743 := bstep (se 1 (by rfl) ⟨256307, by rfl⟩ : syracuseStep 341743 = 512615) B512615
theorem B1521665 : Blo 299831 1521665 := bstep (se 2 (by rfl) ⟨570624, by rfl⟩ : syracuseStep 1521665 = 1141249) B1141249
theorem B571627 : Blo 299831 571627 := bstep (se 1 (by rfl) ⟨428720, by rfl⟩ : syracuseStep 571627 = 857441) B857441
theorem B3881195 : Blo 299831 3881195 := bstep (se 1 (by rfl) ⟨2910896, by rfl⟩ : syracuseStep 3881195 = 5821793) B5821793
theorem B571855 : Blo 299831 571855 := bstep (se 1 (by rfl) ⟨428891, by rfl⟩ : syracuseStep 571855 = 857783) B857783
theorem B506459 : Blo 299831 506459 := bstep (se 1 (by rfl) ⟨379844, by rfl⟩ : syracuseStep 506459 = 759689) B759689
theorem B1227401 : Blo 299831 1227401 := bstep (se 2 (by rfl) ⟨460275, by rfl⟩ : syracuseStep 1227401 = 920551) B920551
theorem B1522475 : Blo 299831 1522475 := bstep (se 1 (by rfl) ⟨1141856, by rfl⟩ : syracuseStep 1522475 = 2283713) B2283713
theorem B1456987 : Blo 299831 1456987 := bstep (se 1 (by rfl) ⟨1092740, by rfl⟩ : syracuseStep 1456987 = 2185481) B2185481
theorem B2440145 : Blo 299831 2440145 := bstep (se 2 (by rfl) ⟨915054, by rfl⟩ : syracuseStep 2440145 = 1830109) B1830109
theorem B507343 : Blo 299831 507343 := bstep (se 1 (by rfl) ⟨380507, by rfl⟩ : syracuseStep 507343 = 761015) B761015
theorem B4505311 : Blo 299831 4505311 := bstep (se 1 (by rfl) ⟨3378983, by rfl⟩ : syracuseStep 4505311 = 6757967) B6757967
theorem B1523933 : Blo 299831 1523933 := bstep (se 3 (by rfl) ⟨285737, by rfl⟩ : syracuseStep 1523933 = 571475) B571475
theorem B3850487 : Blo 299831 3850487 := bstep (se 1 (by rfl) ⟨2887865, by rfl⟩ : syracuseStep 3850487 = 5775731) B5775731
theorem B508207 : Blo 299831 508207 := bstep (se 1 (by rfl) ⟨381155, by rfl⟩ : syracuseStep 508207 = 762311) B762311
theorem B1294825 : Blo 299831 1294825 := bstep (se 2 (by rfl) ⟨485559, by rfl⟩ : syracuseStep 1294825 = 971119) B971119
theorem B1458695 : Blo 299831 1458695 := bstep (se 1 (by rfl) ⟨1094021, by rfl⟩ : syracuseStep 1458695 = 2188043) B2188043
theorem B574057 : Blo 299831 574057 := bstep (se 2 (by rfl) ⟨215271, by rfl⟩ : syracuseStep 574057 = 430543) B430543
theorem B2737577 : Blo 299831 2737577 := bstep (se 2 (by rfl) ⟨1026591, by rfl⟩ : syracuseStep 2737577 = 2053183) B2053183
theorem B9848267 : Blo 299831 9848267 := bstep (se 1 (by rfl) ⟨7386200, by rfl⟩ : syracuseStep 9848267 = 14772401) B14772401
theorem B509503 : Blo 299831 509503 := bstep (se 1 (by rfl) ⟨382127, by rfl⟩ : syracuseStep 509503 = 764255) B764255
theorem B968363 : Blo 299831 968363 := bstep (se 1 (by rfl) ⟨726272, by rfl⟩ : syracuseStep 968363 = 1452545) B1452545
theorem B10504495 : Blo 299831 10504495 := bstep (se 1 (by rfl) ⟨7878371, by rfl⟩ : syracuseStep 10504495 = 15756743) B15756743
theorem B379495 : Blo 299831 379495 := bstep (se 1 (by rfl) ⟨284621, by rfl⟩ : syracuseStep 379495 = 569243) B569243
theorem B969337 : Blo 299831 969337 := bstep (se 2 (by rfl) ⟨363501, by rfl⟩ : syracuseStep 969337 = 727003) B727003
theorem B674729 : Blo 299831 674729 := bstep (se 2 (by rfl) ⟨253023, by rfl⟩ : syracuseStep 674729 = 506047) B506047
theorem B3099971 : Blo 299831 3099971 := bstep (se 1 (by rfl) ⟨2324978, by rfl⟩ : syracuseStep 3099971 = 4649957) B4649957
theorem B609761 : Blo 299831 609761 := bstep (se 2 (by rfl) ⟨228660, by rfl⟩ : syracuseStep 609761 = 457321) B457321
theorem B675431 : Blo 299831 675431 := bstep (se 1 (by rfl) ⟨506573, by rfl⟩ : syracuseStep 675431 = 1013147) B1013147
theorem B1724267 : Blo 299831 1724267 := bstep (se 1 (by rfl) ⟨1293200, by rfl⟩ : syracuseStep 1724267 = 2586401) B2586401
theorem B675935 : Blo 299831 675935 := bstep (se 1 (by rfl) ⟨506951, by rfl⟩ : syracuseStep 675935 = 1013903) B1013903
theorem B512095 : Blo 299831 512095 := bstep (se 1 (by rfl) ⟨384071, by rfl⟩ : syracuseStep 512095 = 768143) B768143
theorem B544871 : Blo 299831 544871 := bstep (se 1 (by rfl) ⟨408653, by rfl⟩ : syracuseStep 544871 = 817307) B817307
theorem B1527983 : Blo 299831 1527983 := bstep (se 1 (by rfl) ⟨1145987, by rfl⟩ : syracuseStep 1527983 = 2291975) B2291975
theorem B971131 : Blo 299831 971131 := bstep (se 1 (by rfl) ⟨728348, by rfl⟩ : syracuseStep 971131 = 1456697) B1456697
theorem B676691 : Blo 299831 676691 := bstep (se 1 (by rfl) ⟨507518, by rfl⟩ : syracuseStep 676691 = 1015037) B1015037
theorem B545627 : Blo 299831 545627 := bstep (se 1 (by rfl) ⟨409220, by rfl⟩ : syracuseStep 545627 = 818441) B818441
theorem B381935 : Blo 299831 381935 := bstep (se 1 (by rfl) ⟨286451, by rfl⟩ : syracuseStep 381935 = 572903) B572903
theorem B677231 : Blo 299831 677231 := bstep (se 1 (by rfl) ⟨507923, by rfl⟩ : syracuseStep 677231 = 1015847) B1015847
theorem B644687 : Blo 299831 644687 := bstep (se 1 (by rfl) ⟨483515, by rfl⟩ : syracuseStep 644687 = 967031) B967031
theorem B677663 : Blo 299831 677663 := bstep (se 1 (by rfl) ⟨508247, by rfl⟩ : syracuseStep 677663 = 1016495) B1016495
theorem B8312807 : Blo 299831 8312807 := bstep (se 1 (by rfl) ⟨6234605, by rfl⟩ : syracuseStep 8312807 = 12469211) B12469211
theorem B677879 : Blo 299831 677879 := bstep (se 1 (by rfl) ⟨508409, by rfl⟩ : syracuseStep 677879 = 1016819) B1016819
theorem B1530089 : Blo 299831 1530089 := bstep (se 2 (by rfl) ⟨573783, by rfl⟩ : syracuseStep 1530089 = 1147567) B1147567
theorem B678239 : Blo 299831 678239 := bstep (se 1 (by rfl) ⟨508679, by rfl⟩ : syracuseStep 678239 = 1017359) B1017359
theorem B678779 : Blo 299831 678779 := bstep (se 1 (by rfl) ⟨509084, by rfl⟩ : syracuseStep 678779 = 1018169) B1018169
theorem B678959 : Blo 299831 678959 := bstep (se 1 (by rfl) ⟨509219, by rfl⟩ : syracuseStep 678959 = 1018439) B1018439
theorem B4906489 : Blo 299831 4906489 := bstep (se 2 (by rfl) ⟨1839933, by rfl⟩ : syracuseStep 4906489 = 3679867) B3679867
theorem B4218493 : Blo 299831 4218493 := bstep (se 3 (by rfl) ⟨790967, by rfl⟩ : syracuseStep 4218493 = 1581935) B1581935
theorem B450215 : Blo 299831 450215 := bstep (se 1 (by rfl) ⟨337661, by rfl⟩ : syracuseStep 450215 = 675323) B675323
theorem B679643 : Blo 299831 679643 := bstep (se 1 (by rfl) ⟨509732, by rfl⟩ : syracuseStep 679643 = 1019465) B1019465
theorem B450335 : Blo 299831 450335 := bstep (se 1 (by rfl) ⟨337751, by rfl⟩ : syracuseStep 450335 = 675503) B675503
theorem B1630135 : Blo 299831 1630135 := bstep (se 1 (by rfl) ⟨1222601, by rfl⟩ : syracuseStep 1630135 = 2445203) B2445203
theorem B679913 : Blo 299831 679913 := bstep (se 2 (by rfl) ⟨254967, by rfl⟩ : syracuseStep 679913 = 509935) B509935
theorem B450767 : Blo 299831 450767 := bstep (se 1 (by rfl) ⟨338075, by rfl⟩ : syracuseStep 450767 = 676151) B676151
theorem B450815 : Blo 299831 450815 := bstep (se 1 (by rfl) ⟨338111, by rfl⟩ : syracuseStep 450815 = 676223) B676223
theorem B161014169 : Blo 299831 161014169 := bstep (se 2 (by rfl) ⟨60380313, by rfl⟩ : syracuseStep 161014169 = 120760627) B120760627
theorem B680615 : Blo 299831 680615 := bstep (se 1 (by rfl) ⟨510461, by rfl⟩ : syracuseStep 680615 = 1020923) B1020923
theorem B516827 : Blo 299831 516827 := bstep (se 1 (by rfl) ⟨387620, by rfl⟩ : syracuseStep 516827 = 775241) B775241
theorem B680759 : Blo 299831 680759 := bstep (se 1 (by rfl) ⟨510569, by rfl⟩ : syracuseStep 680759 = 1021139) B1021139
theorem B5170067 : Blo 299831 5170067 := bstep (se 1 (by rfl) ⟨3877550, by rfl⟩ : syracuseStep 5170067 = 7755101) B7755101
theorem B680939 : Blo 299831 680939 := bstep (se 1 (by rfl) ⟨510704, by rfl⟩ : syracuseStep 680939 = 1021409) B1021409
theorem B451631 : Blo 299831 451631 := bstep (se 1 (by rfl) ⟨338723, by rfl⟩ : syracuseStep 451631 = 677447) B677447
theorem B451751 : Blo 299831 451751 := bstep (se 1 (by rfl) ⟨338813, by rfl⟩ : syracuseStep 451751 = 677627) B677627
theorem B681371 : Blo 299831 681371 := bstep (se 1 (by rfl) ⟨511028, by rfl⟩ : syracuseStep 681371 = 1022057) B1022057
theorem B452123 : Blo 299831 452123 := bstep (se 1 (by rfl) ⟨339092, by rfl⟩ : syracuseStep 452123 = 678185) B678185
theorem B4351583 : Blo 299831 4351583 := bstep (se 1 (by rfl) ⟨3263687, by rfl⟩ : syracuseStep 4351583 = 6527375) B6527375
theorem B452507 : Blo 299831 452507 := bstep (se 1 (by rfl) ⟨339380, by rfl⟩ : syracuseStep 452507 = 678761) B678761
theorem B452543 : Blo 299831 452543 := bstep (se 1 (by rfl) ⟨339407, by rfl⟩ : syracuseStep 452543 = 678815) B678815
theorem B681947 : Blo 299831 681947 := bstep (se 1 (by rfl) ⟨511460, by rfl⟩ : syracuseStep 681947 = 1022921) B1022921
theorem B1370209 : Blo 299831 1370209 := bstep (se 2 (by rfl) ⟨513828, by rfl⟩ : syracuseStep 1370209 = 1027657) B1027657
theorem B452729 : Blo 299831 452729 := bstep (se 2 (by rfl) ⟨169773, by rfl⟩ : syracuseStep 452729 = 339547) B339547
theorem B682127 : Blo 299831 682127 := bstep (se 1 (by rfl) ⟨511595, by rfl⟩ : syracuseStep 682127 = 1023191) B1023191
theorem B682217 : Blo 299831 682217 := bstep (se 2 (by rfl) ⟨255831, by rfl⟩ : syracuseStep 682217 = 511663) B511663
theorem B6547877 : Blo 299831 6547877 := bstep (se 4 (by rfl) ⟨613863, by rfl⟩ : syracuseStep 6547877 = 1227727) B1227727
theorem B682487 : Blo 299831 682487 := bstep (se 1 (by rfl) ⟨511865, by rfl⟩ : syracuseStep 682487 = 1023731) B1023731
theorem B453113 : Blo 299831 453113 := bstep (se 2 (by rfl) ⟨169917, by rfl⟩ : syracuseStep 453113 = 339835) B339835
theorem B453167 : Blo 299831 453167 := bstep (se 1 (by rfl) ⟨339875, by rfl⟩ : syracuseStep 453167 = 679751) B679751
theorem B453599 : Blo 299831 453599 := bstep (se 1 (by rfl) ⟨340199, by rfl⟩ : syracuseStep 453599 = 680399) B680399
theorem B683081 : Blo 299831 683081 := bstep (se 2 (by rfl) ⟨256155, by rfl⟩ : syracuseStep 683081 = 512311) B512311
theorem B454043 : Blo 299831 454043 := bstep (se 1 (by rfl) ⟨340532, by rfl⟩ : syracuseStep 454043 = 681065) B681065
theorem B454463 : Blo 299831 454463 := bstep (se 1 (by rfl) ⟨340847, by rfl⟩ : syracuseStep 454463 = 681695) B681695
theorem B454649 : Blo 299831 454649 := bstep (se 2 (by rfl) ⟨170493, by rfl⟩ : syracuseStep 454649 = 340987) B340987
theorem B1536083 : Blo 299831 1536083 := bstep (se 1 (by rfl) ⟨1152062, by rfl⟩ : syracuseStep 1536083 = 2304125) B2304125
theorem B454889 : Blo 299831 454889 := bstep (se 2 (by rfl) ⟨170583, by rfl⟩ : syracuseStep 454889 = 341167) B341167
theorem B455015 : Blo 299831 455015 := bstep (se 1 (by rfl) ⟨341261, by rfl⟩ : syracuseStep 455015 = 682523) B682523
theorem B2290031 : Blo 299831 2290031 := bstep (se 1 (by rfl) ⟨1717523, by rfl⟩ : syracuseStep 2290031 = 3435047) B3435047
theorem B16576913 : Blo 299831 16576913 := bstep (se 2 (by rfl) ⟨6216342, by rfl⟩ : syracuseStep 16576913 = 12432685) B12432685
theorem B1012175 : Blo 299831 1012175 := bstep (se 1 (by rfl) ⟨759131, by rfl⟩ : syracuseStep 1012175 = 1518263) B1518263
theorem B881327 : Blo 299831 881327 := bstep (se 1 (by rfl) ⟨660995, by rfl⟩ : syracuseStep 881327 = 1321991) B1321991
theorem B455561 : Blo 299831 455561 := bstep (se 2 (by rfl) ⟨170835, by rfl⟩ : syracuseStep 455561 = 341671) B341671
theorem B1307935 : Blo 299831 1307935 := bstep (se 1 (by rfl) ⟨980951, by rfl⟩ : syracuseStep 1307935 = 1961903) B1961903
theorem B1832539 : Blo 299831 1832539 := bstep (se 1 (by rfl) ⟨1374404, by rfl⟩ : syracuseStep 1832539 = 2748809) B2748809
theorem B1144637 : Blo 299831 1144637 := bstep (se 3 (by rfl) ⟨214619, by rfl⟩ : syracuseStep 1144637 = 429239) B429239
theorem B2914703 : Blo 299831 2914703 := bstep (se 1 (by rfl) ⟨2186027, by rfl⟩ : syracuseStep 2914703 = 4372055) B4372055
theorem B1014497 : Blo 299831 1014497 := bstep (se 2 (by rfl) ⟨380436, by rfl⟩ : syracuseStep 1014497 = 760873) B760873
theorem B1145609 : Blo 299831 1145609 := bstep (se 2 (by rfl) ⟨429603, by rfl⟩ : syracuseStep 1145609 = 859207) B859207
theorem B1932113 : Blo 299831 1932113 := bstep (se 2 (by rfl) ⟨724542, by rfl⟩ : syracuseStep 1932113 = 1449085) B1449085
theorem B654247 : Blo 299831 654247 := bstep (se 1 (by rfl) ⟨490685, by rfl⟩ : syracuseStep 654247 = 981371) B981371
theorem B2915513 : Blo 299831 2915513 := bstep (se 2 (by rfl) ⟨1093317, by rfl⟩ : syracuseStep 2915513 = 2186635) B2186635
theorem B5143823 : Blo 299831 5143823 := bstep (se 1 (by rfl) ⟨3857867, by rfl⟩ : syracuseStep 5143823 = 7715735) B7715735
theorem B982297 : Blo 299831 982297 := bstep (se 2 (by rfl) ⟨368361, by rfl⟩ : syracuseStep 982297 = 736723) B736723
theorem B2293433 : Blo 299831 2293433 := bstep (se 2 (by rfl) ⟨860037, by rfl⟩ : syracuseStep 2293433 = 1720075) B1720075
theorem B1015631 : Blo 299831 1015631 := bstep (se 1 (by rfl) ⟨761723, by rfl⟩ : syracuseStep 1015631 = 1523447) B1523447
theorem B1015955 : Blo 299831 1015955 := bstep (se 1 (by rfl) ⟨761966, by rfl⟩ : syracuseStep 1015955 = 1523933) B1523933
theorem B2883833 : Blo 299831 2883833 := bstep (se 2 (by rfl) ⟨1081437, by rfl⟩ : syracuseStep 2883833 = 2162875) B2162875
theorem B1442281 : Blo 299831 1442281 := bstep (se 2 (by rfl) ⟨540855, by rfl⟩ : syracuseStep 1442281 = 1081711) B1081711
theorem B1147553 : Blo 299831 1147553 := bstep (se 2 (by rfl) ⟨430332, by rfl⟩ : syracuseStep 1147553 = 860665) B860665
theorem B44205101 : Blo 299831 44205101 := bstep (se 3 (by rfl) ⟨8288456, by rfl⟩ : syracuseStep 44205101 = 16576913) B16576913
theorem B1442897 : Blo 299831 1442897 := bstep (se 2 (by rfl) ⟨541086, by rfl⟩ : syracuseStep 1442897 = 1082173) B1082173
theorem B1378205 : Blo 299831 1378205 := bstep (se 3 (by rfl) ⟨258413, by rfl⟩ : syracuseStep 1378205 = 516827) B516827
theorem B1017953 : Blo 299831 1017953 := bstep (se 2 (by rfl) ⟨381732, by rfl⟩ : syracuseStep 1017953 = 763465) B763465
theorem B1149025 : Blo 299831 1149025 := bstep (se 2 (by rfl) ⟨430884, by rfl⟩ : syracuseStep 1149025 = 861769) B861769
theorem B2066647 : Blo 299831 2066647 := bstep (se 1 (by rfl) ⟨1549985, by rfl⟩ : syracuseStep 2066647 = 3099971) B3099971
theorem B461359 : Blo 299831 461359 := bstep (se 1 (by rfl) ⟨346019, by rfl⟩ : syracuseStep 461359 = 692039) B692039
theorem B1149511 : Blo 299831 1149511 := bstep (se 1 (by rfl) ⟨862133, by rfl⟩ : syracuseStep 1149511 = 1724267) B1724267
theorem B1018493 : Blo 299831 1018493 := bstep (se 3 (by rfl) ⟨190967, by rfl⟩ : syracuseStep 1018493 = 381935) B381935
theorem B1018601 : Blo 299831 1018601 := bstep (se 2 (by rfl) ⟨381975, by rfl⟩ : syracuseStep 1018601 = 763951) B763951
theorem B363247 : Blo 299831 363247 := bstep (se 1 (by rfl) ⟨272435, by rfl⟩ : syracuseStep 363247 = 544871) B544871
theorem B1018655 : Blo 299831 1018655 := bstep (se 1 (by rfl) ⟨763991, by rfl⟩ : syracuseStep 1018655 = 1527983) B1527983
theorem B429791 : Blo 299831 429791 := bstep (se 1 (by rfl) ⟨322343, by rfl⟩ : syracuseStep 429791 = 644687) B644687
theorem B5541871 : Blo 299831 5541871 := bstep (se 1 (by rfl) ⟨4156403, by rfl⟩ : syracuseStep 5541871 = 8312807) B8312807
theorem B1020059 : Blo 299831 1020059 := bstep (se 1 (by rfl) ⟨765044, by rfl⟩ : syracuseStep 1020059 = 1530089) B1530089
theorem B300143 : Blo 299831 300143 := bstep (se 1 (by rfl) ⟨225107, by rfl⟩ : syracuseStep 300143 = 450215) B450215
theorem B300223 : Blo 299831 300223 := bstep (se 1 (by rfl) ⟨225167, by rfl⟩ : syracuseStep 300223 = 450335) B450335
theorem B300511 : Blo 299831 300511 := bstep (se 1 (by rfl) ⟨225383, by rfl⟩ : syracuseStep 300511 = 450767) B450767
theorem B857567 : Blo 299831 857567 := bstep (se 1 (by rfl) ⟨643175, by rfl⟩ : syracuseStep 857567 = 1286351) B1286351
theorem B300543 : Blo 299831 300543 := bstep (se 1 (by rfl) ⟨225407, by rfl⟩ : syracuseStep 300543 = 450815) B450815
theorem B3446711 : Blo 299831 3446711 := bstep (se 1 (by rfl) ⟨2585033, by rfl⟩ : syracuseStep 3446711 = 5170067) B5170067
theorem B301087 : Blo 299831 301087 := bstep (se 1 (by rfl) ⟨225815, by rfl⟩ : syracuseStep 301087 = 451631) B451631
theorem B301167 : Blo 299831 301167 := bstep (se 1 (by rfl) ⟨225875, by rfl⟩ : syracuseStep 301167 = 451751) B451751
theorem B301415 : Blo 299831 301415 := bstep (se 1 (by rfl) ⟨226061, by rfl⟩ : syracuseStep 301415 = 452123) B452123
theorem B301671 : Blo 299831 301671 := bstep (se 1 (by rfl) ⟨226253, by rfl⟩ : syracuseStep 301671 = 452507) B452507
theorem B301695 : Blo 299831 301695 := bstep (se 1 (by rfl) ⟨226271, by rfl⟩ : syracuseStep 301695 = 452543) B452543
theorem B301819 : Blo 299831 301819 := bstep (se 1 (by rfl) ⟨226364, by rfl⟩ : syracuseStep 301819 = 452729) B452729
theorem B4365251 : Blo 299831 4365251 := bstep (se 1 (by rfl) ⟨3273938, by rfl⟩ : syracuseStep 4365251 = 6547877) B6547877
theorem B302075 : Blo 299831 302075 := bstep (se 1 (by rfl) ⟨226556, by rfl⟩ : syracuseStep 302075 = 453113) B453113
theorem B302111 : Blo 299831 302111 := bstep (se 1 (by rfl) ⟨226583, by rfl⟩ : syracuseStep 302111 = 453167) B453167
theorem B1743913 : Blo 299831 1743913 := bstep (se 2 (by rfl) ⟨653967, by rfl⟩ : syracuseStep 1743913 = 1307935) B1307935
theorem B3546287 : Blo 299831 3546287 := bstep (se 1 (by rfl) ⟨2659715, by rfl⟩ : syracuseStep 3546287 = 5319431) B5319431
theorem B302399 : Blo 299831 302399 := bstep (se 1 (by rfl) ⟨226799, by rfl⟩ : syracuseStep 302399 = 453599) B453599
theorem B302695 : Blo 299831 302695 := bstep (se 1 (by rfl) ⟨227021, by rfl⟩ : syracuseStep 302695 = 454043) B454043
theorem B3284833 : Blo 299831 3284833 := bstep (se 2 (by rfl) ⟨1231812, by rfl⟩ : syracuseStep 3284833 = 2463625) B2463625
theorem B302975 : Blo 299831 302975 := bstep (se 1 (by rfl) ⟨227231, by rfl⟩ : syracuseStep 302975 = 454463) B454463
theorem B1449971 : Blo 299831 1449971 := bstep (se 1 (by rfl) ⟨1087478, by rfl⟩ : syracuseStep 1449971 = 2174957) B2174957
theorem B303099 : Blo 299831 303099 := bstep (se 1 (by rfl) ⟨227324, by rfl⟩ : syracuseStep 303099 = 454649) B454649
theorem B1024055 : Blo 299831 1024055 := bstep (se 1 (by rfl) ⟨768041, by rfl⟩ : syracuseStep 1024055 = 1536083) B1536083
theorem B303259 : Blo 299831 303259 := bstep (se 1 (by rfl) ⟨227444, by rfl⟩ : syracuseStep 303259 = 454889) B454889
theorem B729271 : Blo 299831 729271 := bstep (se 1 (by rfl) ⟨546953, by rfl⟩ : syracuseStep 729271 = 1093907) B1093907
theorem B303343 : Blo 299831 303343 := bstep (se 1 (by rfl) ⟨227507, by rfl⟩ : syracuseStep 303343 = 455015) B455015
theorem B762169 : Blo 299831 762169 := bstep (se 2 (by rfl) ⟨285813, by rfl⟩ : syracuseStep 762169 = 571627) B571627
theorem B860539 : Blo 299831 860539 := bstep (se 1 (by rfl) ⟨645404, by rfl⟩ : syracuseStep 860539 = 1290809) B1290809
theorem B860699 : Blo 299831 860699 := bstep (se 1 (by rfl) ⟨645524, by rfl⟩ : syracuseStep 860699 = 1291049) B1291049
theorem B303707 : Blo 299831 303707 := bstep (se 1 (by rfl) ⟨227780, by rfl⟩ : syracuseStep 303707 = 455561) B455561
theorem B762473 : Blo 299831 762473 := bstep (se 2 (by rfl) ⟨285927, by rfl⟩ : syracuseStep 762473 = 571855) B571855
theorem B1942649 : Blo 299831 1942649 := bstep (se 2 (by rfl) ⟨728493, by rfl⟩ : syracuseStep 1942649 = 1456987) B1456987
theorem B1713311 : Blo 299831 1713311 := bstep (se 1 (by rfl) ⟨1284983, by rfl⟩ : syracuseStep 1713311 = 2569967) B2569967
theorem B763091 : Blo 299831 763091 := bstep (se 1 (by rfl) ⟨572318, by rfl⟩ : syracuseStep 763091 = 1144637) B1144637
theorem B4335029 : Blo 299831 4335029 := bstep (se 5 (by rfl) ⟨203204, by rfl⟩ : syracuseStep 4335029 = 406409) B406409
theorem B1943135 : Blo 299831 1943135 := bstep (se 1 (by rfl) ⟨1457351, by rfl⟩ : syracuseStep 1943135 = 2914703) B2914703
theorem B337639 : Blo 299831 337639 := bstep (se 1 (by rfl) ⟨253229, by rfl⟩ : syracuseStep 337639 = 506459) B506459
theorem B763739 : Blo 299831 763739 := bstep (se 1 (by rfl) ⟨572804, by rfl⟩ : syracuseStep 763739 = 1145609) B1145609
theorem B1288075 : Blo 299831 1288075 := bstep (se 1 (by rfl) ⟨966056, by rfl⟩ : syracuseStep 1288075 = 1932113) B1932113
theorem B1943675 : Blo 299831 1943675 := bstep (se 1 (by rfl) ⟨1457756, by rfl⟩ : syracuseStep 1943675 = 2915513) B2915513
theorem B6007081 : Blo 299831 6007081 := bstep (se 2 (by rfl) ⟨2252655, by rfl⟩ : syracuseStep 6007081 = 4505311) B4505311
theorem B2173513 : Blo 299831 2173513 := bstep (se 2 (by rfl) ⟨815067, by rfl⟩ : syracuseStep 2173513 = 1630135) B1630135
theorem B764711 : Blo 299831 764711 := bstep (se 1 (by rfl) ⟨573533, by rfl⟩ : syracuseStep 764711 = 1147067) B1147067
theorem B2566991 : Blo 299831 2566991 := bstep (se 1 (by rfl) ⟨1925243, by rfl⟩ : syracuseStep 2566991 = 3850487) B3850487
theorem B765409 : Blo 299831 765409 := bstep (se 2 (by rfl) ⟨287028, by rfl⟩ : syracuseStep 765409 = 574057) B574057
theorem B6565511 : Blo 299831 6565511 := bstep (se 1 (by rfl) ⟨4924133, by rfl⟩ : syracuseStep 6565511 = 9848267) B9848267
theorem B962239 : Blo 299831 962239 := bstep (se 1 (by rfl) ⟨721679, by rfl⟩ : syracuseStep 962239 = 1443359) B1443359
theorem B1093895 : Blo 299831 1093895 := bstep (se 1 (by rfl) ⟨820421, by rfl⟩ : syracuseStep 1093895 = 1640843) B1640843
theorem B569911 : Blo 299831 569911 := bstep (se 1 (by rfl) ⟨427433, by rfl⟩ : syracuseStep 569911 = 854867) B854867
theorem B1159933 : Blo 299831 1159933 := bstep (se 3 (by rfl) ⟨217487, by rfl⟩ : syracuseStep 1159933 = 434975) B434975
theorem B570169 : Blo 299831 570169 := bstep (se 2 (by rfl) ⟨213813, by rfl⟩ : syracuseStep 570169 = 427627) B427627
theorem B1455005 : Blo 299831 1455005 := bstep (se 3 (by rfl) ⟨272813, by rfl⟩ : syracuseStep 1455005 = 545627) B545627
theorem B406507 : Blo 299831 406507 := bstep (se 1 (by rfl) ⟨304880, by rfl⟩ : syracuseStep 406507 = 609761) B609761
theorem B3257333 : Blo 299831 3257333 := bstep (se 5 (by rfl) ⟨152687, by rfl⟩ : syracuseStep 3257333 = 305375) B305375
theorem B1226267 : Blo 299831 1226267 := bstep (se 1 (by rfl) ⟨919700, by rfl⟩ : syracuseStep 1226267 = 1839401) B1839401
theorem B767515 : Blo 299831 767515 := bstep (se 1 (by rfl) ⟨575636, by rfl⟩ : syracuseStep 767515 = 1151273) B1151273
theorem B3847823 : Blo 299831 3847823 := bstep (se 1 (by rfl) ⟨2885867, by rfl⟩ : syracuseStep 3847823 = 5771735) B5771735
theorem B14005993 : Blo 299831 14005993 := bstep (se 2 (by rfl) ⟨5252247, by rfl⟩ : syracuseStep 14005993 = 10504495) B10504495
theorem B505993 : Blo 299831 505993 := bstep (se 2 (by rfl) ⟨189747, by rfl⟩ : syracuseStep 505993 = 379495) B379495
theorem B571529 : Blo 299831 571529 := bstep (se 2 (by rfl) ⟨214323, by rfl⟩ : syracuseStep 571529 = 428647) B428647
theorem B1292449 : Blo 299831 1292449 := bstep (se 2 (by rfl) ⟨484668, by rfl⟩ : syracuseStep 1292449 = 969337) B969337
theorem B3258539 : Blo 299831 3258539 := bstep (se 1 (by rfl) ⟨2443904, by rfl⟩ : syracuseStep 3258539 = 4887809) B4887809
theorem B768487 : Blo 299831 768487 := bstep (se 1 (by rfl) ⟨576365, by rfl⟩ : syracuseStep 768487 = 1152731) B1152731
theorem B1621657 : Blo 299831 1621657 := bstep (se 2 (by rfl) ⟨608121, by rfl⟩ : syracuseStep 1621657 = 1216243) B1216243
theorem B5783885 : Blo 299831 5783885 := bstep (se 3 (by rfl) ⟨1084478, by rfl⟩ : syracuseStep 5783885 = 2168957) B2168957
theorem B1294841 : Blo 299831 1294841 := bstep (se 2 (by rfl) ⟨485565, by rfl⟩ : syracuseStep 1294841 = 971131) B971131
theorem B1983521 : Blo 299831 1983521 := bstep (se 2 (by rfl) ⟨743820, by rfl⟩ : syracuseStep 1983521 = 1487641) B1487641
theorem B2901055 : Blo 299831 2901055 := bstep (se 1 (by rfl) ⟨2175791, by rfl⟩ : syracuseStep 2901055 = 4351583) B4351583
theorem B509287 : Blo 299831 509287 := bstep (se 1 (by rfl) ⟨381965, by rfl⟩ : syracuseStep 509287 = 763931) B763931
theorem B574931 : Blo 299831 574931 := bstep (se 1 (by rfl) ⟨431198, by rfl⟩ : syracuseStep 574931 = 862397) B862397
theorem B575515 : Blo 299831 575515 := bstep (se 1 (by rfl) ⟨431636, by rfl⟩ : syracuseStep 575515 = 863273) B863273
theorem B2443385 : Blo 299831 2443385 := bstep (se 2 (by rfl) ⟨916269, by rfl⟩ : syracuseStep 2443385 = 1832539) B1832539
theorem B3852947 : Blo 299831 3852947 := bstep (se 1 (by rfl) ⟨2889710, by rfl⟩ : syracuseStep 3852947 = 5779421) B5779421
theorem B67095215 : Blo 299831 67095215 := bstep (se 1 (by rfl) ⟨50321411, by rfl⟩ : syracuseStep 67095215 = 100642823) B100642823
theorem B3459833 : Blo 299831 3459833 := bstep (se 2 (by rfl) ⟨1297437, by rfl⟩ : syracuseStep 3459833 = 2594875) B2594875
theorem B969479 : Blo 299831 969479 := bstep (se 1 (by rfl) ⟨727109, by rfl⟩ : syracuseStep 969479 = 1454219) B1454219
theorem B2280311 : Blo 299831 2280311 := bstep (se 1 (by rfl) ⟨1710233, by rfl⟩ : syracuseStep 2280311 = 3420467) B3420467
theorem B1526687 : Blo 299831 1526687 := bstep (se 1 (by rfl) ⟨1145015, by rfl⟩ : syracuseStep 1526687 = 2290031) B2290031
theorem B674783 : Blo 299831 674783 := bstep (se 1 (by rfl) ⟨506087, by rfl⟩ : syracuseStep 674783 = 1012175) B1012175
theorem B380315 : Blo 299831 380315 := bstep (se 1 (by rfl) ⟨285236, by rfl⟩ : syracuseStep 380315 = 570473) B570473
theorem B970505 : Blo 299831 970505 := bstep (se 2 (by rfl) ⟨363939, by rfl⟩ : syracuseStep 970505 = 727879) B727879
theorem B872329 : Blo 299831 872329 := bstep (se 2 (by rfl) ⟨327123, by rfl⟩ : syracuseStep 872329 = 654247) B654247
theorem B676331 : Blo 299831 676331 := bstep (se 1 (by rfl) ⟨507248, by rfl⟩ : syracuseStep 676331 = 1014497) B1014497
theorem B676457 : Blo 299831 676457 := bstep (se 2 (by rfl) ⟨253671, by rfl⟩ : syracuseStep 676457 = 507343) B507343
theorem B1626763 : Blo 299831 1626763 := bstep (se 1 (by rfl) ⟨1220072, by rfl⟩ : syracuseStep 1626763 = 2440145) B2440145
theorem B6541985 : Blo 299831 6541985 := bstep (se 2 (by rfl) ⟨2453244, by rfl⟩ : syracuseStep 6541985 = 4906489) B4906489
theorem B5624657 : Blo 299831 5624657 := bstep (se 2 (by rfl) ⟨2109246, by rfl⟩ : syracuseStep 5624657 = 4218493) B4218493
theorem B3429215 : Blo 299831 3429215 := bstep (se 1 (by rfl) ⟨2571911, by rfl⟩ : syracuseStep 3429215 = 5143823) B5143823
theorem B1528955 : Blo 299831 1528955 := bstep (se 1 (by rfl) ⟨1146716, by rfl⟩ : syracuseStep 1528955 = 2293433) B2293433
theorem B677087 : Blo 299831 677087 := bstep (se 1 (by rfl) ⟨507815, by rfl⟩ : syracuseStep 677087 = 1015631) B1015631
theorem B546335 : Blo 299831 546335 := bstep (se 1 (by rfl) ⟨409751, by rfl⟩ : syracuseStep 546335 = 819503) B819503
theorem B677519 : Blo 299831 677519 := bstep (se 1 (by rfl) ⟨508139, by rfl⟩ : syracuseStep 677519 = 1016279) B1016279
theorem B677609 : Blo 299831 677609 := bstep (se 2 (by rfl) ⟨254103, by rfl⟩ : syracuseStep 677609 = 508207) B508207
theorem B1726433 : Blo 299831 1726433 := bstep (se 2 (by rfl) ⟨647412, by rfl⟩ : syracuseStep 1726433 = 1294825) B1294825
theorem B1825051 : Blo 299831 1825051 := bstep (se 1 (by rfl) ⟨1368788, by rfl⟩ : syracuseStep 1825051 = 2737577) B2737577
theorem B645575 : Blo 299831 645575 := bstep (se 1 (by rfl) ⟨484181, by rfl⟩ : syracuseStep 645575 = 968363) B968363
theorem B3889853 : Blo 299831 3889853 := bstep (se 3 (by rfl) ⟨729347, by rfl⟩ : syracuseStep 3889853 = 1458695) B1458695
theorem B1628905 : Blo 299831 1628905 := bstep (se 2 (by rfl) ⟨610839, by rfl⟩ : syracuseStep 1628905 = 1221679) B1221679
theorem B613183 : Blo 299831 613183 := bstep (se 1 (by rfl) ⟨459887, by rfl⟩ : syracuseStep 613183 = 919775) B919775
theorem B2350205 : Blo 299831 2350205 := bstep (se 3 (by rfl) ⟨440663, by rfl⟩ : syracuseStep 2350205 = 881327) B881327
theorem B449819 : Blo 299831 449819 := bstep (se 1 (by rfl) ⟨337364, by rfl⟩ : syracuseStep 449819 = 674729) B674729
theorem B679247 : Blo 299831 679247 := bstep (se 1 (by rfl) ⟨509435, by rfl⟩ : syracuseStep 679247 = 1018871) B1018871
theorem B613759 : Blo 299831 613759 := bstep (se 1 (by rfl) ⟨460319, by rfl⟩ : syracuseStep 613759 = 920639) B920639
theorem B679337 : Blo 299831 679337 := bstep (se 2 (by rfl) ⟨254751, by rfl⟩ : syracuseStep 679337 = 509503) B509503
theorem B450287 : Blo 299831 450287 := bstep (se 1 (by rfl) ⟨337715, by rfl⟩ : syracuseStep 450287 = 675431) B675431
theorem B1400743 : Blo 299831 1400743 := bstep (se 1 (by rfl) ⟨1050557, by rfl⟩ : syracuseStep 1400743 = 2101115) B2101115
theorem B450473 : Blo 299831 450473 := bstep (se 2 (by rfl) ⟨168927, by rfl⟩ : syracuseStep 450473 = 337855) B337855
theorem B450623 : Blo 299831 450623 := bstep (se 1 (by rfl) ⟨337967, by rfl⟩ : syracuseStep 450623 = 675935) B675935
theorem B1826945 : Blo 299831 1826945 := bstep (se 2 (by rfl) ⟨685104, by rfl⟩ : syracuseStep 1826945 = 1370209) B1370209
theorem B450857 : Blo 299831 450857 := bstep (se 2 (by rfl) ⟨169071, by rfl⟩ : syracuseStep 450857 = 338143) B338143
theorem B451127 : Blo 299831 451127 := bstep (se 1 (by rfl) ⟨338345, by rfl⟩ : syracuseStep 451127 = 676691) B676691
theorem B451487 : Blo 299831 451487 := bstep (se 1 (by rfl) ⟨338615, by rfl⟩ : syracuseStep 451487 = 677231) B677231
theorem B451775 : Blo 299831 451775 := bstep (se 1 (by rfl) ⟨338831, by rfl⟩ : syracuseStep 451775 = 677663) B677663
theorem B2745677 : Blo 299831 2745677 := bstep (se 3 (by rfl) ⟨514814, by rfl⟩ : syracuseStep 2745677 = 1029629) B1029629
theorem B451919 : Blo 299831 451919 := bstep (se 1 (by rfl) ⟨338939, by rfl⟩ : syracuseStep 451919 = 677879) B677879
theorem B452009 : Blo 299831 452009 := bstep (se 2 (by rfl) ⟨169503, by rfl⟩ : syracuseStep 452009 = 339007) B339007
theorem B452159 : Blo 299831 452159 := bstep (se 1 (by rfl) ⟨339119, by rfl⟩ : syracuseStep 452159 = 678239) B678239
theorem B681551 : Blo 299831 681551 := bstep (se 1 (by rfl) ⟨511163, by rfl⟩ : syracuseStep 681551 = 1022327) B1022327
theorem B452519 : Blo 299831 452519 := bstep (se 1 (by rfl) ⟨339389, by rfl⟩ : syracuseStep 452519 = 678779) B678779
theorem B1140763 : Blo 299831 1140763 := bstep (se 1 (by rfl) ⟨855572, by rfl⟩ : syracuseStep 1140763 = 1711145) B1711145
theorem B452639 : Blo 299831 452639 := bstep (se 1 (by rfl) ⟨339479, by rfl⟩ : syracuseStep 452639 = 678959) B678959
theorem B682271 : Blo 299831 682271 := bstep (se 1 (by rfl) ⟨511703, by rfl⟩ : syracuseStep 682271 = 1023407) B1023407
theorem B453095 : Blo 299831 453095 := bstep (se 1 (by rfl) ⟨339821, by rfl⟩ : syracuseStep 453095 = 679643) B679643
theorem B4418023 : Blo 299831 4418023 := bstep (se 1 (by rfl) ⟨3313517, by rfl⟩ : syracuseStep 4418023 = 6627035) B6627035
theorem B453275 : Blo 299831 453275 := bstep (se 1 (by rfl) ⟨339956, by rfl⟩ : syracuseStep 453275 = 679913) B679913
theorem B682793 : Blo 299831 682793 := bstep (se 2 (by rfl) ⟨256047, by rfl⟩ : syracuseStep 682793 = 512095) B512095
theorem B453497 : Blo 299831 453497 := bstep (se 2 (by rfl) ⟨170061, by rfl⟩ : syracuseStep 453497 = 340123) B340123
theorem B107342779 : Blo 299831 107342779 := bstep (se 1 (by rfl) ⟨80507084, by rfl⟩ : syracuseStep 107342779 = 161014169) B161014169
theorem B683063 : Blo 299831 683063 := bstep (se 1 (by rfl) ⟨512297, by rfl⟩ : syracuseStep 683063 = 1024595) B1024595
theorem B453743 : Blo 299831 453743 := bstep (se 1 (by rfl) ⟨340307, by rfl⟩ : syracuseStep 453743 = 680615) B680615
theorem B453839 : Blo 299831 453839 := bstep (se 1 (by rfl) ⟨340379, by rfl⟩ : syracuseStep 453839 = 680759) B680759
theorem B683243 : Blo 299831 683243 := bstep (se 1 (by rfl) ⟨512432, by rfl⟩ : syracuseStep 683243 = 1024865) B1024865
theorem B453959 : Blo 299831 453959 := bstep (se 1 (by rfl) ⟨340469, by rfl⟩ : syracuseStep 453959 = 680939) B680939
theorem B454247 : Blo 299831 454247 := bstep (se 1 (by rfl) ⟨340685, by rfl⟩ : syracuseStep 454247 = 681371) B681371
theorem B2289545 : Blo 299831 2289545 := bstep (se 2 (by rfl) ⟨858579, by rfl⟩ : syracuseStep 2289545 = 1717159) B1717159
theorem B454631 : Blo 299831 454631 := bstep (se 1 (by rfl) ⟨340973, by rfl⟩ : syracuseStep 454631 = 681947) B681947
theorem B454751 : Blo 299831 454751 := bstep (se 1 (by rfl) ⟨341063, by rfl⟩ : syracuseStep 454751 = 682127) B682127
theorem B4878463 : Blo 299831 4878463 := bstep (se 1 (by rfl) ⟨3658847, by rfl⟩ : syracuseStep 4878463 = 7317695) B7317695
theorem B454811 : Blo 299831 454811 := bstep (se 1 (by rfl) ⟨341108, by rfl⟩ : syracuseStep 454811 = 682217) B682217
theorem B454991 : Blo 299831 454991 := bstep (se 1 (by rfl) ⟨341243, by rfl⟩ : syracuseStep 454991 = 682487) B682487
theorem B1143179 : Blo 299831 1143179 := bstep (se 1 (by rfl) ⟨857384, by rfl⟩ : syracuseStep 1143179 = 1714769) B1714769
theorem B455081 : Blo 299831 455081 := bstep (se 2 (by rfl) ⟨170655, by rfl⟩ : syracuseStep 455081 = 341311) B341311
theorem B455387 : Blo 299831 455387 := bstep (se 1 (by rfl) ⟨341540, by rfl⟩ : syracuseStep 455387 = 683081) B683081
theorem B1012499 : Blo 299831 1012499 := bstep (se 1 (by rfl) ⟨759374, by rfl⟩ : syracuseStep 1012499 = 1518749) B1518749
theorem B455657 : Blo 299831 455657 := bstep (se 2 (by rfl) ⟨170871, by rfl⟩ : syracuseStep 455657 = 341743) B341743
theorem B3110147 : Blo 299831 3110147 := bstep (se 1 (by rfl) ⟨2332610, by rfl⟩ : syracuseStep 3110147 = 4665221) B4665221
theorem B1013363 : Blo 299831 1013363 := bstep (se 1 (by rfl) ⟨760022, by rfl⟩ : syracuseStep 1013363 = 1520045) B1520045
theorem B1537865 : Blo 299831 1537865 := bstep (se 2 (by rfl) ⟨576699, by rfl⟩ : syracuseStep 1537865 = 1153399) B1153399
theorem B3700883 : Blo 299831 3700883 := bstep (se 1 (by rfl) ⟨2775662, by rfl⟩ : syracuseStep 3700883 = 5551325) B5551325
theorem B1014443 : Blo 299831 1014443 := bstep (se 1 (by rfl) ⟨760832, by rfl⟩ : syracuseStep 1014443 = 1521665) B1521665
theorem B2587463 : Blo 299831 2587463 := bstep (se 1 (by rfl) ⟨1940597, by rfl⟩ : syracuseStep 2587463 = 3881195) B3881195
theorem B1309729 : Blo 299831 1309729 := bstep (se 2 (by rfl) ⟨491148, by rfl⟩ : syracuseStep 1309729 = 982297) B982297
theorem B818267 : Blo 299831 818267 := bstep (se 1 (by rfl) ⟨613700, by rfl⟩ : syracuseStep 818267 = 1227401) B1227401
theorem B1014983 : Blo 299831 1014983 := bstep (se 1 (by rfl) ⟨761237, by rfl⟩ : syracuseStep 1014983 = 1522475) B1522475
theorem B1016225 : Blo 299831 1016225 := bstep (se 2 (by rfl) ⟨381084, by rfl⟩ : syracuseStep 1016225 = 762169) B762169
theorem B1147385 : Blo 299831 1147385 := bstep (se 2 (by rfl) ⟨430269, by rfl⟩ : syracuseStep 1147385 = 860539) B860539
theorem B918803 : Blo 299831 918803 := bstep (se 1 (by rfl) ⟨689102, by rfl⟩ : syracuseStep 918803 = 1378205) B1378205
theorem B3868073 : Blo 299831 3868073 := bstep (se 2 (by rfl) ⟨1450527, by rfl⟩ : syracuseStep 3868073 = 2901055) B2901055
theorem B44730143 : Blo 299831 44730143 := bstep (se 1 (by rfl) ⟨33547607, by rfl⟩ : syracuseStep 44730143 = 67095215) B67095215
theorem B1017791 : Blo 299831 1017791 := bstep (se 1 (by rfl) ⟨763343, by rfl⟩ : syracuseStep 1017791 = 1526687) B1526687
theorem B2460581 : Blo 299831 2460581 := bstep (se 4 (by rfl) ⟨230679, by rfl⟩ : syracuseStep 2460581 = 461359) B461359
theorem B2755529 : Blo 299831 2755529 := bstep (se 2 (by rfl) ⟨1033323, by rfl⟩ : syracuseStep 2755529 = 2066647) B2066647
theorem B4361323 : Blo 299831 4361323 := bstep (se 1 (by rfl) ⟨3270992, by rfl⟩ : syracuseStep 4361323 = 6541985) B6541985
theorem B1019303 : Blo 299831 1019303 := bstep (se 1 (by rfl) ⟨764477, by rfl⟩ : syracuseStep 1019303 = 1528955) B1528955
theorem B364223 : Blo 299831 364223 := bstep (se 1 (by rfl) ⟨273167, by rfl⟩ : syracuseStep 364223 = 546335) B546335
theorem B1937317 : Blo 299831 1937317 := bstep (se 4 (by rfl) ⟨181623, by rfl⟩ : syracuseStep 1937317 = 363247) B363247
theorem B2297807 : Blo 299831 2297807 := bstep (se 1 (by rfl) ⟨1723355, by rfl⟩ : syracuseStep 2297807 = 3446711) B3446711
theorem B1150955 : Blo 299831 1150955 := bstep (se 1 (by rfl) ⟨863216, by rfl⟩ : syracuseStep 1150955 = 1726433) B1726433
theorem B2593235 : Blo 299831 2593235 := bstep (se 1 (by rfl) ⟨1944926, by rfl⟩ : syracuseStep 2593235 = 3889853) B3889853
theorem B1020545 : Blo 299831 1020545 := bstep (se 2 (by rfl) ⟨382704, by rfl⟩ : syracuseStep 1020545 = 765409) B765409
theorem B2364191 : Blo 299831 2364191 := bstep (se 1 (by rfl) ⟨1773143, by rfl⟩ : syracuseStep 2364191 = 3546287) B3546287
theorem B299879 : Blo 299831 299879 := bstep (se 1 (by rfl) ⟨224909, by rfl⟩ : syracuseStep 299879 = 449819) B449819
theorem B1282985 : Blo 299831 1282985 := bstep (se 2 (by rfl) ⟨481119, by rfl⟩ : syracuseStep 1282985 = 962239) B962239
theorem B300191 : Blo 299831 300191 := bstep (se 1 (by rfl) ⟨225143, by rfl⟩ : syracuseStep 300191 = 450287) B450287
theorem B300315 : Blo 299831 300315 := bstep (se 1 (by rfl) ⟨225236, by rfl⟩ : syracuseStep 300315 = 450473) B450473
theorem B300415 : Blo 299831 300415 := bstep (se 1 (by rfl) ⟨225311, by rfl⟩ : syracuseStep 300415 = 450623) B450623
theorem B1217963 : Blo 299831 1217963 := bstep (se 1 (by rfl) ⟨913472, by rfl⟩ : syracuseStep 1217963 = 1826945) B1826945
theorem B300571 : Blo 299831 300571 := bstep (se 1 (by rfl) ⟨225428, by rfl⟩ : syracuseStep 300571 = 450857) B450857
theorem B300751 : Blo 299831 300751 := bstep (se 1 (by rfl) ⟨225563, by rfl⟩ : syracuseStep 300751 = 451127) B451127
theorem B300991 : Blo 299831 300991 := bstep (se 1 (by rfl) ⟨225743, by rfl⟩ : syracuseStep 300991 = 451487) B451487
theorem B759881 : Blo 299831 759881 := bstep (se 2 (by rfl) ⟨284955, by rfl⟩ : syracuseStep 759881 = 569911) B569911
theorem B301183 : Blo 299831 301183 := bstep (se 1 (by rfl) ⟨225887, by rfl⟩ : syracuseStep 301183 = 451775) B451775
theorem B2169017 : Blo 299831 2169017 := bstep (se 2 (by rfl) ⟨813381, by rfl⟩ : syracuseStep 2169017 = 1626763) B1626763
theorem B301279 : Blo 299831 301279 := bstep (se 1 (by rfl) ⟨225959, by rfl⟩ : syracuseStep 301279 = 451919) B451919
theorem B301339 : Blo 299831 301339 := bstep (se 1 (by rfl) ⟨226004, by rfl⟩ : syracuseStep 301339 = 452009) B452009
theorem B2890019 : Blo 299831 2890019 := bstep (se 1 (by rfl) ⟨2167514, by rfl⟩ : syracuseStep 2890019 = 4335029) B4335029
theorem B1546577 : Blo 299831 1546577 := bstep (se 2 (by rfl) ⟨579966, by rfl⟩ : syracuseStep 1546577 = 1159933) B1159933
theorem B301439 : Blo 299831 301439 := bstep (se 1 (by rfl) ⟨226079, by rfl⟩ : syracuseStep 301439 = 452159) B452159
theorem B760225 : Blo 299831 760225 := bstep (se 2 (by rfl) ⟨285084, by rfl⟩ : syracuseStep 760225 = 570169) B570169
theorem B301679 : Blo 299831 301679 := bstep (se 1 (by rfl) ⟨226259, by rfl⟩ : syracuseStep 301679 = 452519) B452519
theorem B301759 : Blo 299831 301759 := bstep (se 1 (by rfl) ⟨226319, by rfl⟩ : syracuseStep 301759 = 452639) B452639
theorem B302063 : Blo 299831 302063 := bstep (se 1 (by rfl) ⟨226547, by rfl⟩ : syracuseStep 302063 = 453095) B453095
theorem B302183 : Blo 299831 302183 := bstep (se 1 (by rfl) ⟨226637, by rfl⟩ : syracuseStep 302183 = 453275) B453275
theorem B1711327 : Blo 299831 1711327 := bstep (se 1 (by rfl) ⟨1283495, by rfl⟩ : syracuseStep 1711327 = 2566991) B2566991
theorem B302331 : Blo 299831 302331 := bstep (se 1 (by rfl) ⟨226748, by rfl⟩ : syracuseStep 302331 = 453497) B453497
theorem B1023353 : Blo 299831 1023353 := bstep (se 2 (by rfl) ⟨383757, by rfl⟩ : syracuseStep 1023353 = 767515) B767515
theorem B302495 : Blo 299831 302495 := bstep (se 1 (by rfl) ⟨226871, by rfl⟩ : syracuseStep 302495 = 453743) B453743
theorem B302559 : Blo 299831 302559 := bstep (se 1 (by rfl) ⟨226919, by rfl⟩ : syracuseStep 302559 = 453839) B453839
theorem B302639 : Blo 299831 302639 := bstep (se 1 (by rfl) ⟨226979, by rfl⟩ : syracuseStep 302639 = 453959) B453959
theorem B302831 : Blo 299831 302831 := bstep (se 1 (by rfl) ⟨227123, by rfl⟩ : syracuseStep 302831 = 454247) B454247
theorem B303087 : Blo 299831 303087 := bstep (se 1 (by rfl) ⟨227315, by rfl⟩ : syracuseStep 303087 = 454631) B454631
theorem B303167 : Blo 299831 303167 := bstep (se 1 (by rfl) ⟨227375, by rfl⟩ : syracuseStep 303167 = 454751) B454751
theorem B303207 : Blo 299831 303207 := bstep (se 1 (by rfl) ⟨227405, by rfl⟩ : syracuseStep 303207 = 454811) B454811
theorem B729263 : Blo 299831 729263 := bstep (se 1 (by rfl) ⟨546947, by rfl⟩ : syracuseStep 729263 = 1093895) B1093895
theorem B303327 : Blo 299831 303327 := bstep (se 1 (by rfl) ⟨227495, by rfl⟩ : syracuseStep 303327 = 454991) B454991
theorem B762119 : Blo 299831 762119 := bstep (se 1 (by rfl) ⟨571589, by rfl⟩ : syracuseStep 762119 = 1143179) B1143179
theorem B303387 : Blo 299831 303387 := bstep (se 1 (by rfl) ⟨227540, by rfl⟩ : syracuseStep 303387 = 455081) B455081
theorem B2433401 : Blo 299831 2433401 := bstep (se 2 (by rfl) ⟨912525, by rfl⟩ : syracuseStep 2433401 = 1825051) B1825051
theorem B303591 : Blo 299831 303591 := bstep (se 1 (by rfl) ⟨227693, by rfl⟩ : syracuseStep 303591 = 455387) B455387
theorem B1024649 : Blo 299831 1024649 := bstep (se 2 (by rfl) ⟨384243, by rfl⟩ : syracuseStep 1024649 = 768487) B768487
theorem B303771 : Blo 299831 303771 := bstep (se 1 (by rfl) ⟨227828, by rfl⟩ : syracuseStep 303771 = 455657) B455657
theorem B2171555 : Blo 299831 2171555 := bstep (se 1 (by rfl) ⟨1628666, by rfl⟩ : syracuseStep 2171555 = 3257333) B3257333
theorem B2073431 : Blo 299831 2073431 := bstep (se 1 (by rfl) ⟨1555073, by rfl⟩ : syracuseStep 2073431 = 3110147) B3110147
theorem B2171873 : Blo 299831 2171873 := bstep (se 2 (by rfl) ⟨814452, by rfl⟩ : syracuseStep 2171873 = 1628905) B1628905
theorem B2565215 : Blo 299831 2565215 := bstep (se 1 (by rfl) ⟨1923911, by rfl⟩ : syracuseStep 2565215 = 3847823) B3847823
theorem B1025243 : Blo 299831 1025243 := bstep (se 1 (by rfl) ⟨768932, by rfl⟩ : syracuseStep 1025243 = 1537865) B1537865
theorem B1746305 : Blo 299831 1746305 := bstep (se 2 (by rfl) ⟨654864, by rfl⟩ : syracuseStep 1746305 = 1309729) B1309729
theorem B2467255 : Blo 299831 2467255 := bstep (se 1 (by rfl) ⟨1850441, by rfl⟩ : syracuseStep 2467255 = 3700883) B3700883
theorem B2172359 : Blo 299831 2172359 := bstep (se 1 (by rfl) ⟨1629269, by rfl⟩ : syracuseStep 2172359 = 3258539) B3258539
theorem B863227 : Blo 299831 863227 := bstep (se 1 (by rfl) ⟨647420, by rfl⟩ : syracuseStep 863227 = 1294841) B1294841
theorem B765035 : Blo 299831 765035 := bstep (se 1 (by rfl) ⟨573776, by rfl⟩ : syracuseStep 765035 = 1147553) B1147553
theorem B1322347 : Blo 299831 1322347 := bstep (se 1 (by rfl) ⟨991760, by rfl⟩ : syracuseStep 1322347 = 1983521) B1983521
theorem B29470067 : Blo 299831 29470067 := bstep (se 1 (by rfl) ⟨22102550, by rfl⟩ : syracuseStep 29470067 = 44205101) B44205101
theorem B961931 : Blo 299831 961931 := bstep (se 1 (by rfl) ⟨721448, by rfl⟩ : syracuseStep 961931 = 1442897) B1442897
theorem B8728181 : Blo 299831 8728181 := bstep (se 5 (by rfl) ⟨409133, by rfl⟩ : syracuseStep 8728181 = 818267) B818267
theorem B2568631 : Blo 299831 2568631 := bstep (se 1 (by rfl) ⟨1926473, by rfl⟩ : syracuseStep 2568631 = 3852947) B3852947
theorem B2306555 : Blo 299831 2306555 := bstep (se 1 (by rfl) ⟨1729916, by rfl⟩ : syracuseStep 2306555 = 3459833) B3459833
theorem B1520207 : Blo 299831 1520207 := bstep (se 1 (by rfl) ⟨1140155, by rfl⟩ : syracuseStep 1520207 = 2280311) B2280311
theorem B1717433 : Blo 299831 1717433 := bstep (se 2 (by rfl) ⟨644037, by rfl⟩ : syracuseStep 1717433 = 1288075) B1288075
theorem B1521017 : Blo 299831 1521017 := bstep (se 2 (by rfl) ⟨570381, by rfl⟩ : syracuseStep 1521017 = 1140763) B1140763
theorem B767353 : Blo 299831 767353 := bstep (se 2 (by rfl) ⟨287757, by rfl⟩ : syracuseStep 767353 = 575515) B575515
theorem B8009441 : Blo 299831 8009441 := bstep (se 2 (by rfl) ⟨3003540, by rfl⟩ : syracuseStep 8009441 = 6007081) B6007081
theorem B3749771 : Blo 299831 3749771 := bstep (se 1 (by rfl) ⟨2812328, by rfl⟩ : syracuseStep 3749771 = 5624657) B5624657
theorem B2898017 : Blo 299831 2898017 := bstep (se 2 (by rfl) ⟨1086756, by rfl⟩ : syracuseStep 2898017 = 2173513) B2173513
theorem B571711 : Blo 299831 571711 := bstep (se 1 (by rfl) ⟨428783, by rfl⟩ : syracuseStep 571711 = 857567) B857567
theorem B1163105 : Blo 299831 1163105 := bstep (se 2 (by rfl) ⟨436164, by rfl⟩ : syracuseStep 1163105 = 872329) B872329
theorem B7389161 : Blo 299831 7389161 := bstep (se 2 (by rfl) ⟨2770935, by rfl⟩ : syracuseStep 7389161 = 5541871) B5541871
theorem B966647 : Blo 299831 966647 := bstep (se 1 (by rfl) ⟨724985, by rfl⟩ : syracuseStep 966647 = 1449971) B1449971
theorem B6504617 : Blo 299831 6504617 := bstep (se 2 (by rfl) ⟨2439231, by rfl⟩ : syracuseStep 6504617 = 4878463) B4878463
theorem B573799 : Blo 299831 573799 := bstep (se 1 (by rfl) ⟨430349, by rfl⟩ : syracuseStep 573799 = 860699) B860699
theorem B508315 : Blo 299831 508315 := bstep (se 1 (by rfl) ⟨381236, by rfl⟩ : syracuseStep 508315 = 762473) B762473
theorem B1295099 : Blo 299831 1295099 := bstep (se 1 (by rfl) ⟨971324, by rfl⟩ : syracuseStep 1295099 = 1942649) B1942649
theorem B508727 : Blo 299831 508727 := bstep (se 1 (by rfl) ⟨381545, by rfl⟩ : syracuseStep 508727 = 763091) B763091
theorem B1295423 : Blo 299831 1295423 := bstep (se 1 (by rfl) ⟨971567, by rfl⟩ : syracuseStep 1295423 = 1943135) B1943135
theorem B1721533 : Blo 299831 1721533 := bstep (se 3 (by rfl) ⟨322787, by rfl⟩ : syracuseStep 1721533 = 645575) B645575
theorem B509159 : Blo 299831 509159 := bstep (se 1 (by rfl) ⟨381869, by rfl⟩ : syracuseStep 509159 = 763739) B763739
theorem B542009 : Blo 299831 542009 := bstep (se 2 (by rfl) ⟨203253, by rfl⟩ : syracuseStep 542009 = 406507) B406507
theorem B1295783 : Blo 299831 1295783 := bstep (se 1 (by rfl) ⟨971837, by rfl⟩ : syracuseStep 1295783 = 1943675) B1943675
theorem B509807 : Blo 299831 509807 := bstep (se 1 (by rfl) ⟨382355, by rfl⟩ : syracuseStep 509807 = 764711) B764711
theorem B4377007 : Blo 299831 4377007 := bstep (se 1 (by rfl) ⟨3282755, by rfl⟩ : syracuseStep 4377007 = 6565511) B6565511
theorem B1526363 : Blo 299831 1526363 := bstep (se 1 (by rfl) ⟨1144772, by rfl⟩ : syracuseStep 1526363 = 2289545) B2289545
theorem B674657 : Blo 299831 674657 := bstep (se 2 (by rfl) ⟨252996, by rfl⟩ : syracuseStep 674657 = 505993) B505993
theorem B1723265 : Blo 299831 1723265 := bstep (se 2 (by rfl) ⟨646224, by rfl⟩ : syracuseStep 1723265 = 1292449) B1292449
theorem B674999 : Blo 299831 674999 := bstep (se 1 (by rfl) ⟨506249, by rfl⟩ : syracuseStep 674999 = 1012499) B1012499
theorem B970003 : Blo 299831 970003 := bstep (se 1 (by rfl) ⟨727502, by rfl⟩ : syracuseStep 970003 = 1455005) B1455005
theorem B675575 : Blo 299831 675575 := bstep (se 1 (by rfl) ⟨506681, by rfl⟩ : syracuseStep 675575 = 1013363) B1013363
theorem B381019 : Blo 299831 381019 := bstep (se 1 (by rfl) ⟨285764, by rfl⟩ : syracuseStep 381019 = 571529) B571529
theorem B676295 : Blo 299831 676295 := bstep (se 1 (by rfl) ⟨507221, by rfl⟩ : syracuseStep 676295 = 1014443) B1014443
theorem B1724975 : Blo 299831 1724975 := bstep (se 1 (by rfl) ⟨1293731, by rfl⟩ : syracuseStep 1724975 = 2587463) B2587463
theorem B676655 : Blo 299831 676655 := bstep (se 1 (by rfl) ⟨507491, by rfl⟩ : syracuseStep 676655 = 1014983) B1014983
theorem B4379777 : Blo 299831 4379777 := bstep (se 2 (by rfl) ⟨1642416, by rfl⟩ : syracuseStep 4379777 = 3284833) B3284833
theorem B677303 : Blo 299831 677303 := bstep (se 1 (by rfl) ⟨507977, by rfl⟩ : syracuseStep 677303 = 1015955) B1015955
theorem B1922555 : Blo 299831 1922555 := bstep (se 1 (by rfl) ⟨1441916, by rfl⟩ : syracuseStep 1922555 = 2883833) B2883833
theorem B3855923 : Blo 299831 3855923 := bstep (se 1 (by rfl) ⟨2891942, by rfl⟩ : syracuseStep 3855923 = 5783885) B5783885
theorem B972361 : Blo 299831 972361 := bstep (se 2 (by rfl) ⟨364635, by rfl⟩ : syracuseStep 972361 = 729271) B729271
theorem B1923041 : Blo 299831 1923041 := bstep (se 2 (by rfl) ⟨721140, by rfl⟩ : syracuseStep 1923041 = 1442281) B1442281
theorem B383287 : Blo 299831 383287 := bstep (se 1 (by rfl) ⟨287465, by rfl⟩ : syracuseStep 383287 = 574931) B574931
theorem B678635 : Blo 299831 678635 := bstep (se 1 (by rfl) ⟨508976, by rfl⟩ : syracuseStep 678635 = 1017953) B1017953
theorem B1628923 : Blo 299831 1628923 := bstep (se 1 (by rfl) ⟨1221692, by rfl⟩ : syracuseStep 1628923 = 2443385) B2443385
theorem B678995 : Blo 299831 678995 := bstep (se 1 (by rfl) ⟨509246, by rfl⟩ : syracuseStep 678995 = 1018493) B1018493
theorem B679049 : Blo 299831 679049 := bstep (se 2 (by rfl) ⟨254643, by rfl⟩ : syracuseStep 679049 = 509287) B509287
theorem B679067 : Blo 299831 679067 := bstep (se 1 (by rfl) ⟨509300, by rfl⟩ : syracuseStep 679067 = 1018601) B1018601
theorem B646319 : Blo 299831 646319 := bstep (se 1 (by rfl) ⟨484739, by rfl⟩ : syracuseStep 646319 = 969479) B969479
theorem B679103 : Blo 299831 679103 := bstep (se 1 (by rfl) ⟨509327, by rfl⟩ : syracuseStep 679103 = 1018655) B1018655
theorem B449855 : Blo 299831 449855 := bstep (se 1 (by rfl) ⟨337391, by rfl⟩ : syracuseStep 449855 = 674783) B674783
theorem B450185 : Blo 299831 450185 := bstep (se 2 (by rfl) ⟨168819, by rfl⟩ : syracuseStep 450185 = 337639) B337639
theorem B647003 : Blo 299831 647003 := bstep (se 1 (by rfl) ⟨485252, by rfl⟩ : syracuseStep 647003 = 970505) B970505
theorem B680039 : Blo 299831 680039 := bstep (se 1 (by rfl) ⟨510029, by rfl⟩ : syracuseStep 680039 = 1020059) B1020059
theorem B1532033 : Blo 299831 1532033 := bstep (se 2 (by rfl) ⟨574512, by rfl⟩ : syracuseStep 1532033 = 1149025) B1149025
theorem B450887 : Blo 299831 450887 := bstep (se 1 (by rfl) ⟨338165, by rfl⟩ : syracuseStep 450887 = 676331) B676331
theorem B450971 : Blo 299831 450971 := bstep (se 1 (by rfl) ⟨338228, by rfl⟩ : syracuseStep 450971 = 676457) B676457
theorem B2286143 : Blo 299831 2286143 := bstep (se 1 (by rfl) ⟨1714607, by rfl⟩ : syracuseStep 2286143 = 3429215) B3429215
theorem B5890697 : Blo 299831 5890697 := bstep (se 2 (by rfl) ⟨2209011, by rfl⟩ : syracuseStep 5890697 = 4418023) B4418023
theorem B1532681 : Blo 299831 1532681 := bstep (se 2 (by rfl) ⟨574755, by rfl⟩ : syracuseStep 1532681 = 1149511) B1149511
theorem B451391 : Blo 299831 451391 := bstep (se 1 (by rfl) ⟨338543, by rfl⟩ : syracuseStep 451391 = 677087) B677087
theorem B451679 : Blo 299831 451679 := bstep (se 1 (by rfl) ⟨338759, by rfl⟩ : syracuseStep 451679 = 677519) B677519
theorem B451739 : Blo 299831 451739 := bstep (se 1 (by rfl) ⟨338804, by rfl⟩ : syracuseStep 451739 = 677609) B677609
theorem B143123705 : Blo 299831 143123705 := bstep (se 2 (by rfl) ⟨53671389, by rfl⟩ : syracuseStep 143123705 = 107342779) B107342779
theorem B2910167 : Blo 299831 2910167 := bstep (se 1 (by rfl) ⟨2182625, by rfl⟩ : syracuseStep 2910167 = 4365251) B4365251
theorem B1566803 : Blo 299831 1566803 := bstep (se 1 (by rfl) ⟨1175102, by rfl⟩ : syracuseStep 1566803 = 2350205) B2350205
theorem B452831 : Blo 299831 452831 := bstep (se 1 (by rfl) ⟨339623, by rfl⟩ : syracuseStep 452831 = 679247) B679247
theorem B452891 : Blo 299831 452891 := bstep (se 1 (by rfl) ⟨339668, by rfl⟩ : syracuseStep 452891 = 679337) B679337
theorem B682703 : Blo 299831 682703 := bstep (se 1 (by rfl) ⟨512027, by rfl⟩ : syracuseStep 682703 = 1024055) B1024055
theorem B1142207 : Blo 299831 1142207 := bstep (se 1 (by rfl) ⟨856655, by rfl⟩ : syracuseStep 1142207 = 1713311) B1713311
theorem B1830451 : Blo 299831 1830451 := bstep (se 1 (by rfl) ⟨1372838, by rfl⟩ : syracuseStep 1830451 = 2745677) B2745677
theorem B454367 : Blo 299831 454367 := bstep (se 1 (by rfl) ⟨340775, by rfl⟩ : syracuseStep 454367 = 681551) B681551
theorem B454847 : Blo 299831 454847 := bstep (se 1 (by rfl) ⟨341135, by rfl⟩ : syracuseStep 454847 = 682271) B682271
theorem B455195 : Blo 299831 455195 := bstep (se 1 (by rfl) ⟨341396, by rfl⟩ : syracuseStep 455195 = 682793) B682793
theorem B455375 : Blo 299831 455375 := bstep (se 1 (by rfl) ⟨341531, by rfl⟩ : syracuseStep 455375 = 683063) B683063
theorem B455495 : Blo 299831 455495 := bstep (se 1 (by rfl) ⟨341621, by rfl⟩ : syracuseStep 455495 = 683243) B683243
theorem B18674657 : Blo 299831 18674657 := bstep (se 2 (by rfl) ⟨7002996, by rfl⟩ : syracuseStep 18674657 = 14005993) B14005993
theorem B817511 : Blo 299831 817511 := bstep (se 1 (by rfl) ⟨613133, by rfl⟩ : syracuseStep 817511 = 1226267) B1226267
theorem B1014173 : Blo 299831 1014173 := bstep (se 3 (by rfl) ⟨190157, by rfl⟩ : syracuseStep 1014173 = 380315) B380315
theorem B817577 : Blo 299831 817577 := bstep (se 2 (by rfl) ⟨306591, by rfl⟩ : syracuseStep 817577 = 613183) B613183
theorem B2325217 : Blo 299831 2325217 := bstep (se 2 (by rfl) ⟨871956, by rfl⟩ : syracuseStep 2325217 = 1743913) B1743913
theorem B818345 : Blo 299831 818345 := bstep (se 2 (by rfl) ⟨306879, by rfl⟩ : syracuseStep 818345 = 613759) B613759
theorem B1146109 : Blo 299831 1146109 := bstep (se 3 (by rfl) ⟨214895, by rfl⟩ : syracuseStep 1146109 = 429791) B429791
theorem B2162209 : Blo 299831 2162209 := bstep (se 2 (by rfl) ⟨810828, by rfl⟩ : syracuseStep 2162209 = 1621657) B1621657
theorem B1867657 : Blo 299831 1867657 := bstep (se 2 (by rfl) ⟨700371, by rfl⟩ : syracuseStep 1867657 = 1400743) B1400743
theorem B29820095 : Blo 299831 29820095 := bstep (se 1 (by rfl) ⟨22365071, by rfl⟩ : syracuseStep 29820095 = 44730143) B44730143
theorem B2295377 : Blo 299831 2295377 := bstep (se 2 (by rfl) ⟨860766, by rfl⟩ : syracuseStep 2295377 = 1721533) B1721533
theorem B1017575 : Blo 299831 1017575 := bstep (se 1 (by rfl) ⟨763181, by rfl⟩ : syracuseStep 1017575 = 1526363) B1526363
theorem B1148843 : Blo 299831 1148843 := bstep (se 1 (by rfl) ⟨861632, by rfl⟩ : syracuseStep 1148843 = 1723265) B1723265
theorem B1640387 : Blo 299831 1640387 := bstep (se 1 (by rfl) ⟨1230290, by rfl⟩ : syracuseStep 1640387 = 2460581) B2460581
theorem B1837019 : Blo 299831 1837019 := bstep (se 1 (by rfl) ⟨1377764, by rfl⟩ : syracuseStep 1837019 = 2755529) B2755529
theorem B1149983 : Blo 299831 1149983 := bstep (se 1 (by rfl) ⟨862487, by rfl⟩ : syracuseStep 1149983 = 1724975) B1724975
theorem B1576127 : Blo 299831 1576127 := bstep (se 1 (by rfl) ⟨1182095, by rfl⟩ : syracuseStep 1576127 = 2364191) B2364191
theorem B5836009 : Blo 299831 5836009 := bstep (se 2 (by rfl) ⟨2188503, by rfl⟩ : syracuseStep 5836009 = 4377007) B4377007
theorem B855323 : Blo 299831 855323 := bstep (se 1 (by rfl) ⟨641492, by rfl⟩ : syracuseStep 855323 = 1282985) B1282985
theorem B2919851 : Blo 299831 2919851 := bstep (se 1 (by rfl) ⟨2189888, by rfl⟩ : syracuseStep 2919851 = 4379777) B4379777
theorem B1445357 : Blo 299831 1445357 := bstep (se 3 (by rfl) ⟨271004, by rfl⟩ : syracuseStep 1445357 = 542009) B542009
theorem B1281703 : Blo 299831 1281703 := bstep (se 1 (by rfl) ⟨961277, by rfl⟩ : syracuseStep 1281703 = 1922555) B1922555
theorem B3247901 : Blo 299831 3247901 := bstep (se 3 (by rfl) ⟨608981, by rfl⟩ : syracuseStep 3247901 = 1217963) B1217963
theorem B1282027 : Blo 299831 1282027 := bstep (se 1 (by rfl) ⟨961520, by rfl⟩ : syracuseStep 1282027 = 1923041) B1923041
theorem B1150969 : Blo 299831 1150969 := bstep (se 2 (by rfl) ⟨431613, by rfl⟩ : syracuseStep 1150969 = 863227) B863227
theorem B1446011 : Blo 299831 1446011 := bstep (se 1 (by rfl) ⟨1084508, by rfl⟩ : syracuseStep 1446011 = 2169017) B2169017
theorem B299903 : Blo 299831 299903 := bstep (se 1 (by rfl) ⟨224927, by rfl⟩ : syracuseStep 299903 = 449855) B449855
theorem B9999389 : Blo 299831 9999389 := bstep (se 3 (by rfl) ⟨1874885, by rfl⟩ : syracuseStep 9999389 = 3749771) B3749771
theorem B300123 : Blo 299831 300123 := bstep (se 1 (by rfl) ⟨225092, by rfl⟩ : syracuseStep 300123 = 450185) B450185
theorem B431335 : Blo 299831 431335 := bstep (se 1 (by rfl) ⟨323501, by rfl⟩ : syracuseStep 431335 = 647003) B647003
theorem B1021355 : Blo 299831 1021355 := bstep (se 1 (by rfl) ⟨766016, by rfl⟩ : syracuseStep 1021355 = 1532033) B1532033
theorem B300591 : Blo 299831 300591 := bstep (se 1 (by rfl) ⟨225443, by rfl⟩ : syracuseStep 300591 = 450887) B450887
theorem B300647 : Blo 299831 300647 := bstep (se 1 (by rfl) ⟨225485, by rfl⟩ : syracuseStep 300647 = 450971) B450971
theorem B1447703 : Blo 299831 1447703 := bstep (se 1 (by rfl) ⟨1085777, by rfl⟩ : syracuseStep 1447703 = 2171555) B2171555
theorem B1021787 : Blo 299831 1021787 := bstep (se 1 (by rfl) ⟨766340, by rfl⟩ : syracuseStep 1021787 = 1532681) B1532681
theorem B300927 : Blo 299831 300927 := bstep (se 1 (by rfl) ⟨225695, by rfl⟩ : syracuseStep 300927 = 451391) B451391
theorem B1382287 : Blo 299831 1382287 := bstep (se 1 (by rfl) ⟨1036715, by rfl⟩ : syracuseStep 1382287 = 2073431) B2073431
theorem B1447915 : Blo 299831 1447915 := bstep (se 1 (by rfl) ⟨1085936, by rfl⟩ : syracuseStep 1447915 = 2171873) B2171873
theorem B1710143 : Blo 299831 1710143 := bstep (se 1 (by rfl) ⟨1282607, by rfl⟩ : syracuseStep 1710143 = 2565215) B2565215
theorem B301119 : Blo 299831 301119 := bstep (se 1 (by rfl) ⟨225839, by rfl⟩ : syracuseStep 301119 = 451679) B451679
theorem B301159 : Blo 299831 301159 := bstep (se 1 (by rfl) ⟨225869, by rfl⟩ : syracuseStep 301159 = 451739) B451739
theorem B1448239 : Blo 299831 1448239 := bstep (se 1 (by rfl) ⟨1086179, by rfl⟩ : syracuseStep 1448239 = 2172359) B2172359
theorem B1940111 : Blo 299831 1940111 := bstep (se 1 (by rfl) ⟨1455083, by rfl⟩ : syracuseStep 1940111 = 2910167) B2910167
theorem B301887 : Blo 299831 301887 := bstep (se 1 (by rfl) ⟨226415, by rfl⟩ : syracuseStep 301887 = 452831) B452831
theorem B301927 : Blo 299831 301927 := bstep (se 1 (by rfl) ⟨226445, by rfl⟩ : syracuseStep 301927 = 452891) B452891
theorem B1023137 : Blo 299831 1023137 := bstep (se 2 (by rfl) ⟨383676, by rfl⟩ : syracuseStep 1023137 = 767353) B767353
theorem B761471 : Blo 299831 761471 := bstep (se 1 (by rfl) ⟨571103, by rfl⟩ : syracuseStep 761471 = 1142207) B1142207
theorem B302911 : Blo 299831 302911 := bstep (se 1 (by rfl) ⟨227183, by rfl⟩ : syracuseStep 302911 = 454367) B454367
theorem B303231 : Blo 299831 303231 := bstep (se 1 (by rfl) ⟨227423, by rfl⟩ : syracuseStep 303231 = 454847) B454847
theorem B303463 : Blo 299831 303463 := bstep (se 1 (by rfl) ⟨227597, by rfl⟩ : syracuseStep 303463 = 455195) B455195
theorem B762281 : Blo 299831 762281 := bstep (se 2 (by rfl) ⟨285855, by rfl⟩ : syracuseStep 762281 = 571711) B571711
theorem B303583 : Blo 299831 303583 := bstep (se 1 (by rfl) ⟨227687, by rfl⟩ : syracuseStep 303583 = 455375) B455375
theorem B303663 : Blo 299831 303663 := bstep (se 1 (by rfl) ⟨227747, by rfl⟩ : syracuseStep 303663 = 455495) B455495
theorem B2171897 : Blo 299831 2171897 := bstep (se 2 (by rfl) ⟨814461, by rfl⟩ : syracuseStep 2171897 = 1628923) B1628923
theorem B4926107 : Blo 299831 4926107 := bstep (se 1 (by rfl) ⟨3694580, by rfl⟩ : syracuseStep 4926107 = 7389161) B7389161
theorem B4336411 : Blo 299831 4336411 := bstep (se 1 (by rfl) ⟨3252308, by rfl⟩ : syracuseStep 4336411 = 6504617) B6504617
theorem B764923 : Blo 299831 764923 := bstep (se 1 (by rfl) ⟨573692, by rfl⟩ : syracuseStep 764923 = 1147385) B1147385
theorem B765065 : Blo 299831 765065 := bstep (se 2 (by rfl) ⟨286899, by rfl⟩ : syracuseStep 765065 = 573799) B573799
theorem B863399 : Blo 299831 863399 := bstep (se 1 (by rfl) ⟨647549, by rfl⟩ : syracuseStep 863399 = 1295099) B1295099
theorem B339151 : Blo 299831 339151 := bstep (se 1 (by rfl) ⟨254363, by rfl⟩ : syracuseStep 339151 = 508727) B508727
theorem B863615 : Blo 299831 863615 := bstep (se 1 (by rfl) ⟨647711, by rfl⟩ : syracuseStep 863615 = 1295423) B1295423
theorem B339439 : Blo 299831 339439 := bstep (se 1 (by rfl) ⟨254579, by rfl⟩ : syracuseStep 339439 = 509159) B509159
theorem B863855 : Blo 299831 863855 := bstep (se 1 (by rfl) ⟨647891, by rfl⟩ : syracuseStep 863855 = 1295783) B1295783
theorem B339871 : Blo 299831 339871 := bstep (se 1 (by rfl) ⟨254903, by rfl⟩ : syracuseStep 339871 = 509807) B509807
theorem B3289673 : Blo 299831 3289673 := bstep (se 2 (by rfl) ⟨1233627, by rfl⟩ : syracuseStep 3289673 = 2467255) B2467255
theorem B767303 : Blo 299831 767303 := bstep (se 1 (by rfl) ⟨575477, by rfl⟩ : syracuseStep 767303 = 1150955) B1150955
theorem B2570615 : Blo 299831 2570615 := bstep (se 1 (by rfl) ⟨1927961, by rfl⟩ : syracuseStep 2570615 = 3855923) B3855923
theorem B506587 : Blo 299831 506587 := bstep (se 1 (by rfl) ⟨379940, by rfl⟩ : syracuseStep 506587 = 759881) B759881
theorem B5815097 : Blo 299831 5815097 := bstep (se 2 (by rfl) ⟨2180661, by rfl⟩ : syracuseStep 5815097 = 4361323) B4361323
theorem B1031051 : Blo 299831 1031051 := bstep (se 1 (by rfl) ⟨773288, by rfl⟩ : syracuseStep 1031051 = 1546577) B1546577
theorem B1293337 : Blo 299831 1293337 := bstep (se 2 (by rfl) ⟨485001, by rfl⟩ : syracuseStep 1293337 = 970003) B970003
theorem B2440601 : Blo 299831 2440601 := bstep (se 2 (by rfl) ⟨915225, by rfl⟩ : syracuseStep 2440601 = 1830451) B1830451
theorem B508025 : Blo 299831 508025 := bstep (se 2 (by rfl) ⟨190509, by rfl⟩ : syracuseStep 508025 = 381019) B381019
theorem B508079 : Blo 299831 508079 := bstep (se 1 (by rfl) ⟨381059, by rfl⟩ : syracuseStep 508079 = 762119) B762119
theorem B1622267 : Blo 299831 1622267 := bstep (se 1 (by rfl) ⟨1216700, by rfl⟩ : syracuseStep 1622267 = 2433401) B2433401
theorem B1524095 : Blo 299831 1524095 := bstep (se 1 (by rfl) ⟨1143071, by rfl⟩ : syracuseStep 1524095 = 2286143) B2286143
theorem B3424841 : Blo 299831 3424841 := bstep (se 2 (by rfl) ⟨1284315, by rfl⟩ : syracuseStep 3424841 = 2568631) B2568631
theorem B1164203 : Blo 299831 1164203 := bstep (se 1 (by rfl) ⟨873152, by rfl⟩ : syracuseStep 1164203 = 1746305) B1746305
theorem B2180029 : Blo 299831 2180029 := bstep (se 3 (by rfl) ⟨408755, by rfl⟩ : syracuseStep 2180029 = 817511) B817511
theorem B510023 : Blo 299831 510023 := bstep (se 1 (by rfl) ⟨382517, by rfl⟩ : syracuseStep 510023 = 765035) B765035
theorem B1296481 : Blo 299831 1296481 := bstep (se 2 (by rfl) ⟨486180, by rfl⟩ : syracuseStep 1296481 = 972361) B972361
theorem B19646711 : Blo 299831 19646711 := bstep (se 1 (by rfl) ⟨14735033, by rfl⟩ : syracuseStep 19646711 = 29470067) B29470067
theorem B641287 : Blo 299831 641287 := bstep (se 1 (by rfl) ⟨480965, by rfl⟩ : syracuseStep 641287 = 961931) B961931
theorem B5818787 : Blo 299831 5818787 := bstep (se 1 (by rfl) ⟨4364090, by rfl⟩ : syracuseStep 5818787 = 8728181) B8728181
theorem B511049 : Blo 299831 511049 := bstep (se 2 (by rfl) ⟨191643, by rfl⟩ : syracuseStep 511049 = 383287) B383287
theorem B1723517 : Blo 299831 1723517 := bstep (se 3 (by rfl) ⟨323159, by rfl⟩ : syracuseStep 1723517 = 646319) B646319
theorem B3100289 : Blo 299831 3100289 := bstep (se 2 (by rfl) ⟨1162608, by rfl⟩ : syracuseStep 3100289 = 2325217) B2325217
theorem B676115 : Blo 299831 676115 := bstep (se 1 (by rfl) ⟨507086, by rfl⟩ : syracuseStep 676115 = 1014173) B1014173
theorem B545051 : Blo 299831 545051 := bstep (se 1 (by rfl) ⟨408788, by rfl⟩ : syracuseStep 545051 = 817577) B817577
theorem B2281769 : Blo 299831 2281769 := bstep (se 2 (by rfl) ⟨855663, by rfl⟩ : syracuseStep 2281769 = 1711327) B1711327
theorem B1528145 : Blo 299831 1528145 := bstep (se 2 (by rfl) ⟨573054, by rfl⟩ : syracuseStep 1528145 = 1146109) B1146109
theorem B971261 : Blo 299831 971261 := bstep (se 3 (by rfl) ⟨182111, by rfl⟩ : syracuseStep 971261 = 364223) B364223
theorem B545563 : Blo 299831 545563 := bstep (se 1 (by rfl) ⟨409172, by rfl⟩ : syracuseStep 545563 = 818345) B818345
theorem B775403 : Blo 299831 775403 := bstep (se 1 (by rfl) ⟨581552, by rfl⟩ : syracuseStep 775403 = 1163105) B1163105
theorem B644431 : Blo 299831 644431 := bstep (se 1 (by rfl) ⟨483323, by rfl⟩ : syracuseStep 644431 = 966647) B966647
theorem B677483 : Blo 299831 677483 := bstep (se 1 (by rfl) ⟨508112, by rfl⟩ : syracuseStep 677483 = 1016225) B1016225
theorem B677753 : Blo 299831 677753 := bstep (se 2 (by rfl) ⟨254157, by rfl⟩ : syracuseStep 677753 = 508315) B508315
theorem B612535 : Blo 299831 612535 := bstep (se 1 (by rfl) ⟨459401, by rfl⟩ : syracuseStep 612535 = 918803) B918803
theorem B2578715 : Blo 299831 2578715 := bstep (se 1 (by rfl) ⟨1934036, by rfl⟩ : syracuseStep 2578715 = 3868073) B3868073
theorem B678527 : Blo 299831 678527 := bstep (se 1 (by rfl) ⟨508895, by rfl⟩ : syracuseStep 678527 = 1017791) B1017791
theorem B449771 : Blo 299831 449771 := bstep (se 1 (by rfl) ⟨337328, by rfl⟩ : syracuseStep 449771 = 674657) B674657
theorem B449999 : Blo 299831 449999 := bstep (se 1 (by rfl) ⟨337499, by rfl⟩ : syracuseStep 449999 = 674999) B674999
theorem B679535 : Blo 299831 679535 := bstep (se 1 (by rfl) ⟨509651, by rfl⟩ : syracuseStep 679535 = 1019303) B1019303
theorem B450383 : Blo 299831 450383 := bstep (se 1 (by rfl) ⟨337787, by rfl⟩ : syracuseStep 450383 = 675575) B675575
theorem B1531871 : Blo 299831 1531871 := bstep (se 1 (by rfl) ⟨1148903, by rfl⟩ : syracuseStep 1531871 = 2297807) B2297807
theorem B450863 : Blo 299831 450863 := bstep (se 1 (by rfl) ⟨338147, by rfl⟩ : syracuseStep 450863 = 676295) B676295
theorem B1728823 : Blo 299831 1728823 := bstep (se 1 (by rfl) ⟨1296617, by rfl⟩ : syracuseStep 1728823 = 2593235) B2593235
theorem B680363 : Blo 299831 680363 := bstep (se 1 (by rfl) ⟨510272, by rfl⟩ : syracuseStep 680363 = 1020545) B1020545
theorem B451103 : Blo 299831 451103 := bstep (se 1 (by rfl) ⟨338327, by rfl⟩ : syracuseStep 451103 = 676655) B676655
theorem B451535 : Blo 299831 451535 := bstep (se 1 (by rfl) ⟨338651, by rfl⟩ : syracuseStep 451535 = 677303) B677303
theorem B1926679 : Blo 299831 1926679 := bstep (se 1 (by rfl) ⟨1445009, by rfl⟩ : syracuseStep 1926679 = 2890019) B2890019
theorem B1763129 : Blo 299831 1763129 := bstep (se 2 (by rfl) ⟨661173, by rfl⟩ : syracuseStep 1763129 = 1322347) B1322347
theorem B452423 : Blo 299831 452423 := bstep (se 1 (by rfl) ⟨339317, by rfl⟩ : syracuseStep 452423 = 678635) B678635
theorem B452663 : Blo 299831 452663 := bstep (se 1 (by rfl) ⟨339497, by rfl⟩ : syracuseStep 452663 = 678995) B678995
theorem B452699 : Blo 299831 452699 := bstep (se 1 (by rfl) ⟨339524, by rfl⟩ : syracuseStep 452699 = 679049) B679049
theorem B452711 : Blo 299831 452711 := bstep (se 1 (by rfl) ⟨339533, by rfl⟩ : syracuseStep 452711 = 679067) B679067
theorem B452735 : Blo 299831 452735 := bstep (se 1 (by rfl) ⟨339551, by rfl⟩ : syracuseStep 452735 = 679103) B679103
theorem B682235 : Blo 299831 682235 := bstep (se 1 (by rfl) ⟨511676, by rfl⟩ : syracuseStep 682235 = 1023353) B1023353
theorem B2583089 : Blo 299831 2583089 := bstep (se 2 (by rfl) ⟨968658, by rfl⟩ : syracuseStep 2583089 = 1937317) B1937317
theorem B453359 : Blo 299831 453359 := bstep (se 1 (by rfl) ⟨340019, by rfl⟩ : syracuseStep 453359 = 680039) B680039
theorem B486175 : Blo 299831 486175 := bstep (se 1 (by rfl) ⟨364631, by rfl⟩ : syracuseStep 486175 = 729263) B729263
theorem B3927131 : Blo 299831 3927131 := bstep (se 1 (by rfl) ⟨2945348, by rfl⟩ : syracuseStep 3927131 = 5890697) B5890697
theorem B683099 : Blo 299831 683099 := bstep (se 1 (by rfl) ⟨512324, by rfl⟩ : syracuseStep 683099 = 1024649) B1024649
theorem B683495 : Blo 299831 683495 := bstep (se 1 (by rfl) ⟨512621, by rfl⟩ : syracuseStep 683495 = 1025243) B1025243
theorem B95415803 : Blo 299831 95415803 := bstep (se 1 (by rfl) ⟨71561852, by rfl⟩ : syracuseStep 95415803 = 143123705) B143123705
theorem B1044535 : Blo 299831 1044535 := bstep (se 1 (by rfl) ⟨783401, by rfl⟩ : syracuseStep 1044535 = 1566803) B1566803
theorem B455135 : Blo 299831 455135 := bstep (se 1 (by rfl) ⟨341351, by rfl⟩ : syracuseStep 455135 = 682703) B682703
theorem B1537703 : Blo 299831 1537703 := bstep (se 1 (by rfl) ⟨1153277, by rfl⟩ : syracuseStep 1537703 = 2306555) B2306555
theorem B1013471 : Blo 299831 1013471 := bstep (se 1 (by rfl) ⟨760103, by rfl⟩ : syracuseStep 1013471 = 1520207) B1520207
theorem B1013633 : Blo 299831 1013633 := bstep (se 2 (by rfl) ⟨380112, by rfl⟩ : syracuseStep 1013633 = 760225) B760225
theorem B12449771 : Blo 299831 12449771 := bstep (se 1 (by rfl) ⟨9337328, by rfl⟩ : syracuseStep 12449771 = 18674657) B18674657
theorem B1144955 : Blo 299831 1144955 := bstep (se 1 (by rfl) ⟨858716, by rfl⟩ : syracuseStep 1144955 = 1717433) B1717433
theorem B1014011 : Blo 299831 1014011 := bstep (se 1 (by rfl) ⟨760508, by rfl⟩ : syracuseStep 1014011 = 1521017) B1521017
theorem B5339627 : Blo 299831 5339627 := bstep (se 1 (by rfl) ⟨4004720, by rfl⟩ : syracuseStep 5339627 = 8009441) B8009441
theorem B1932011 : Blo 299831 1932011 := bstep (se 1 (by rfl) ⟨1449008, by rfl⟩ : syracuseStep 1932011 = 2898017) B2898017
theorem B2882945 : Blo 299831 2882945 := bstep (se 2 (by rfl) ⟨1081104, by rfl⟩ : syracuseStep 2882945 = 2162209) B2162209
theorem B2490209 : Blo 299831 2490209 := bstep (se 2 (by rfl) ⟨933828, by rfl⟩ : syracuseStep 2490209 = 1867657) B1867657
theorem B1081511 : Blo 299831 1081511 := bstep (se 1 (by rfl) ⟨811133, by rfl⟩ : syracuseStep 1081511 = 1622267) B1622267
theorem B1016063 : Blo 299831 1016063 := bstep (se 1 (by rfl) ⟨762047, by rfl⟩ : syracuseStep 1016063 = 1524095) B1524095
theorem B1149011 : Blo 299831 1149011 := bstep (se 1 (by rfl) ⟨861758, by rfl⟩ : syracuseStep 1149011 = 1723517) B1723517
theorem B1050751 : Blo 299831 1050751 := bstep (se 1 (by rfl) ⟨788063, by rfl⟩ : syracuseStep 1050751 = 1576127) B1576127
theorem B2165267 : Blo 299831 2165267 := bstep (se 1 (by rfl) ⟨1623950, by rfl⟩ : syracuseStep 2165267 = 3247901) B3247901
theorem B363367 : Blo 299831 363367 := bstep (se 1 (by rfl) ⟨272525, by rfl⟩ : syracuseStep 363367 = 545051) B545051
theorem B1018763 : Blo 299831 1018763 := bstep (se 1 (by rfl) ⟨764072, by rfl⟩ : syracuseStep 1018763 = 1528145) B1528145
theorem B855049 : Blo 299831 855049 := bstep (se 2 (by rfl) ⟨320643, by rfl⟩ : syracuseStep 855049 = 641287) B641287
theorem B1019897 : Blo 299831 1019897 := bstep (se 2 (by rfl) ⟨382461, by rfl⟩ : syracuseStep 1019897 = 764923) B764923
theorem B299847 : Blo 299831 299847 := bstep (se 1 (by rfl) ⟨224885, by rfl⟩ : syracuseStep 299847 = 449771) B449771
theorem B1708937 : Blo 299831 1708937 := bstep (se 2 (by rfl) ⟨640851, by rfl⟩ : syracuseStep 1708937 = 1281703) B1281703
theorem B299999 : Blo 299831 299999 := bstep (se 1 (by rfl) ⟨224999, by rfl⟩ : syracuseStep 299999 = 449999) B449999
theorem B300255 : Blo 299831 300255 := bstep (se 1 (by rfl) ⟨225191, by rfl⟩ : syracuseStep 300255 = 450383) B450383
theorem B1709369 : Blo 299831 1709369 := bstep (se 2 (by rfl) ⟨641013, by rfl⟩ : syracuseStep 1709369 = 1282027) B1282027
theorem B1021247 : Blo 299831 1021247 := bstep (se 1 (by rfl) ⟨765935, by rfl⟩ : syracuseStep 1021247 = 1531871) B1531871
theorem B300575 : Blo 299831 300575 := bstep (se 1 (by rfl) ⟨225431, by rfl⟩ : syracuseStep 300575 = 450863) B450863
theorem B300735 : Blo 299831 300735 := bstep (se 1 (by rfl) ⟨225551, by rfl⟩ : syracuseStep 300735 = 451103) B451103
theorem B301023 : Blo 299831 301023 := bstep (se 1 (by rfl) ⟨225767, by rfl⟩ : syracuseStep 301023 = 451535) B451535
theorem B1447931 : Blo 299831 1447931 := bstep (se 1 (by rfl) ⟨1085948, by rfl⟩ : syracuseStep 1447931 = 2171897) B2171897
theorem B727417 : Blo 299831 727417 := bstep (se 2 (by rfl) ⟨272781, by rfl⟩ : syracuseStep 727417 = 545563) B545563
theorem B301615 : Blo 299831 301615 := bstep (se 1 (by rfl) ⟨226211, by rfl⟩ : syracuseStep 301615 = 452423) B452423
theorem B301775 : Blo 299831 301775 := bstep (se 1 (by rfl) ⟨226331, by rfl⟩ : syracuseStep 301775 = 452663) B452663
theorem B301799 : Blo 299831 301799 := bstep (se 1 (by rfl) ⟨226349, by rfl⟩ : syracuseStep 301799 = 452699) B452699
theorem B301807 : Blo 299831 301807 := bstep (se 1 (by rfl) ⟨226355, by rfl⟩ : syracuseStep 301807 = 452711) B452711
theorem B301823 : Blo 299831 301823 := bstep (se 1 (by rfl) ⟨226367, by rfl⟩ : syracuseStep 301823 = 452735) B452735
theorem B3284071 : Blo 299831 3284071 := bstep (se 1 (by rfl) ⟨2463053, by rfl⟩ : syracuseStep 3284071 = 4926107) B4926107
theorem B859241 : Blo 299831 859241 := bstep (se 2 (by rfl) ⟨322215, by rfl⟩ : syracuseStep 859241 = 644431) B644431
theorem B302239 : Blo 299831 302239 := bstep (se 1 (by rfl) ⟨226679, by rfl⟩ : syracuseStep 302239 = 453359) B453359
theorem B63610535 : Blo 299831 63610535 := bstep (se 1 (by rfl) ⟨47707901, by rfl⟩ : syracuseStep 63610535 = 95415803) B95415803
theorem B1843049 : Blo 299831 1843049 := bstep (se 2 (by rfl) ⟨691143, by rfl⟩ : syracuseStep 1843049 = 1382287) B1382287
theorem B303423 : Blo 299831 303423 := bstep (se 1 (by rfl) ⟨227567, by rfl⟩ : syracuseStep 303423 = 455135) B455135
theorem B1025135 : Blo 299831 1025135 := bstep (se 1 (by rfl) ⟨768851, by rfl⟩ : syracuseStep 1025135 = 1537703) B1537703
theorem B8299847 : Blo 299831 8299847 := bstep (se 1 (by rfl) ⟨6224885, by rfl⟩ : syracuseStep 8299847 = 12449771) B12449771
theorem B763303 : Blo 299831 763303 := bstep (se 1 (by rfl) ⟨572477, by rfl⟩ : syracuseStep 763303 = 1144955) B1144955
theorem B1713743 : Blo 299831 1713743 := bstep (se 1 (by rfl) ⟨1285307, by rfl⟩ : syracuseStep 1713743 = 2570615) B2570615
theorem B8267437 : Blo 299831 8267437 := bstep (se 3 (by rfl) ⟨1550144, by rfl⟩ : syracuseStep 8267437 = 3100289) B3100289
theorem B1288007 : Blo 299831 1288007 := bstep (se 1 (by rfl) ⟨966005, by rfl⟩ : syracuseStep 1288007 = 1932011) B1932011
theorem B3876731 : Blo 299831 3876731 := bstep (se 1 (by rfl) ⟨2907548, by rfl⟩ : syracuseStep 3876731 = 5815097) B5815097
theorem B338683 : Blo 299831 338683 := bstep (se 1 (by rfl) ⟨254012, by rfl⟩ : syracuseStep 338683 = 508025) B508025
theorem B338719 : Blo 299831 338719 := bstep (se 1 (by rfl) ⟨254039, by rfl⟩ : syracuseStep 338719 = 508079) B508079
theorem B2305097 : Blo 299831 2305097 := bstep (se 2 (by rfl) ⟨864411, by rfl⟩ : syracuseStep 2305097 = 1728823) B1728823
theorem B765895 : Blo 299831 765895 := bstep (se 1 (by rfl) ⟨574421, by rfl⟩ : syracuseStep 765895 = 1148843) B1148843
theorem B1093591 : Blo 299831 1093591 := bstep (se 1 (by rfl) ⟨820193, by rfl⟩ : syracuseStep 1093591 = 1640387) B1640387
theorem B1224679 : Blo 299831 1224679 := bstep (se 1 (by rfl) ⟨918509, by rfl⟩ : syracuseStep 1224679 = 1837019) B1837019
theorem B340015 : Blo 299831 340015 := bstep (se 1 (by rfl) ⟨255011, by rfl⟩ : syracuseStep 340015 = 510023) B510023
theorem B3879191 : Blo 299831 3879191 := bstep (se 1 (by rfl) ⟨2909393, by rfl⟩ : syracuseStep 3879191 = 5818787) B5818787
theorem B766655 : Blo 299831 766655 := bstep (se 1 (by rfl) ⟨574991, by rfl⟩ : syracuseStep 766655 = 1149983) B1149983
theorem B2568905 : Blo 299831 2568905 := bstep (se 2 (by rfl) ⟨963339, by rfl⟩ : syracuseStep 2568905 = 1926679) B1926679
theorem B340699 : Blo 299831 340699 := bstep (se 1 (by rfl) ⟨255524, by rfl⟩ : syracuseStep 340699 = 511049) B511049
theorem B570215 : Blo 299831 570215 := bstep (se 1 (by rfl) ⟨427661, by rfl⟩ : syracuseStep 570215 = 855323) B855323
theorem B1946567 : Blo 299831 1946567 := bstep (se 1 (by rfl) ⟨1459925, by rfl⟩ : syracuseStep 1946567 = 2919851) B2919851
theorem B963571 : Blo 299831 963571 := bstep (se 1 (by rfl) ⟨722678, by rfl⟩ : syracuseStep 963571 = 1445357) B1445357
theorem B964007 : Blo 299831 964007 := bstep (se 1 (by rfl) ⟨723005, by rfl⟩ : syracuseStep 964007 = 1446011) B1446011
theorem B1521179 : Blo 299831 1521179 := bstep (se 1 (by rfl) ⟨1140884, by rfl⟩ : syracuseStep 1521179 = 2281769) B2281769
theorem B6666259 : Blo 299831 6666259 := bstep (se 1 (by rfl) ⟨4999694, by rfl⟩ : syracuseStep 6666259 = 9999389) B9999389
theorem B5781881 : Blo 299831 5781881 := bstep (se 2 (by rfl) ⟨2168205, by rfl⟩ : syracuseStep 5781881 = 4336411) B4336411
theorem B965135 : Blo 299831 965135 := bstep (se 1 (by rfl) ⟨723851, by rfl⟩ : syracuseStep 965135 = 1447703) B1447703
theorem B1719143 : Blo 299831 1719143 := bstep (se 1 (by rfl) ⟨1289357, by rfl⟩ : syracuseStep 1719143 = 2578715) B2578715
theorem B7781345 : Blo 299831 7781345 := bstep (se 2 (by rfl) ⟨2918004, by rfl⟩ : syracuseStep 7781345 = 5836009) B5836009
theorem B1293407 : Blo 299831 1293407 := bstep (se 1 (by rfl) ⟨970055, by rfl⟩ : syracuseStep 1293407 = 1940111) B1940111
theorem B507647 : Blo 299831 507647 := bstep (se 1 (by rfl) ⟨380735, by rfl⟩ : syracuseStep 507647 = 761471) B761471
theorem B1392713 : Blo 299831 1392713 := bstep (se 2 (by rfl) ⟨522267, by rfl⟩ : syracuseStep 1392713 = 1044535) B1044535
theorem B508187 : Blo 299831 508187 := bstep (se 1 (by rfl) ⟨381140, by rfl⟩ : syracuseStep 508187 = 762281) B762281
theorem B575113 : Blo 299831 575113 := bstep (se 2 (by rfl) ⟨215667, by rfl⟩ : syracuseStep 575113 = 431335) B431335
theorem B1722059 : Blo 299831 1722059 := bstep (se 1 (by rfl) ⟨1291544, by rfl⟩ : syracuseStep 1722059 = 2583089) B2583089
theorem B510043 : Blo 299831 510043 := bstep (se 1 (by rfl) ⟨382532, by rfl⟩ : syracuseStep 510043 = 765065) B765065
theorem B575599 : Blo 299831 575599 := bstep (se 1 (by rfl) ⟨431699, by rfl⟩ : syracuseStep 575599 = 863399) B863399
theorem B575743 : Blo 299831 575743 := bstep (se 1 (by rfl) ⟨431807, by rfl⟩ : syracuseStep 575743 = 863615) B863615
theorem B575903 : Blo 299831 575903 := bstep (se 1 (by rfl) ⟨431927, by rfl⟩ : syracuseStep 575903 = 863855) B863855
theorem B511535 : Blo 299831 511535 := bstep (se 1 (by rfl) ⟨383651, by rfl⟩ : syracuseStep 511535 = 767303) B767303
theorem B675449 : Blo 299831 675449 := bstep (se 2 (by rfl) ⟨253293, by rfl⟩ : syracuseStep 675449 = 506587) B506587
theorem B675647 : Blo 299831 675647 := bstep (se 1 (by rfl) ⟨506735, by rfl⟩ : syracuseStep 675647 = 1013471) B1013471
theorem B675755 : Blo 299831 675755 := bstep (se 1 (by rfl) ⟨506816, by rfl⟩ : syracuseStep 675755 = 1013633) B1013633
theorem B1724449 : Blo 299831 1724449 := bstep (se 2 (by rfl) ⟨646668, by rfl⟩ : syracuseStep 1724449 = 1293337) B1293337
theorem B676007 : Blo 299831 676007 := bstep (se 1 (by rfl) ⟨507005, by rfl⟩ : syracuseStep 676007 = 1014011) B1014011
theorem B3559751 : Blo 299831 3559751 := bstep (se 1 (by rfl) ⟨2669813, by rfl⟩ : syracuseStep 3559751 = 5339627) B5339627
theorem B1921963 : Blo 299831 1921963 := bstep (se 1 (by rfl) ⟨1441472, by rfl⟩ : syracuseStep 1921963 = 2882945) B2882945
theorem B1627067 : Blo 299831 1627067 := bstep (se 1 (by rfl) ⟨1220300, by rfl⟩ : syracuseStep 1627067 = 2440601) B2440601
theorem B1660139 : Blo 299831 1660139 := bstep (se 1 (by rfl) ⟨1245104, by rfl⟩ : syracuseStep 1660139 = 2490209) B2490209
theorem B2283227 : Blo 299831 2283227 := bstep (se 1 (by rfl) ⟨1712420, by rfl⟩ : syracuseStep 2283227 = 3424841) B3424841
theorem B776135 : Blo 299831 776135 := bstep (se 1 (by rfl) ⟨582101, by rfl⟩ : syracuseStep 776135 = 1164203) B1164203
theorem B19880063 : Blo 299831 19880063 := bstep (se 1 (by rfl) ⟨14910047, by rfl⟩ : syracuseStep 19880063 = 29820095) B29820095
theorem B1530251 : Blo 299831 1530251 := bstep (se 1 (by rfl) ⟨1147688, by rfl⟩ : syracuseStep 1530251 = 2295377) B2295377
theorem B678383 : Blo 299831 678383 := bstep (se 1 (by rfl) ⟨508787, by rfl⟩ : syracuseStep 678383 = 1017575) B1017575
theorem B2906705 : Blo 299831 2906705 := bstep (se 2 (by rfl) ⟨1090014, by rfl⟩ : syracuseStep 2906705 = 2180029) B2180029
theorem B13097807 : Blo 299831 13097807 := bstep (se 1 (by rfl) ⟨9823355, by rfl⟩ : syracuseStep 13097807 = 19646711) B19646711
theorem B1728641 : Blo 299831 1728641 := bstep (se 2 (by rfl) ⟨648240, by rfl⟩ : syracuseStep 1728641 = 1296481) B1296481
theorem B450743 : Blo 299831 450743 := bstep (se 1 (by rfl) ⟨338057, by rfl⟩ : syracuseStep 450743 = 676115) B676115
theorem B647507 : Blo 299831 647507 := bstep (se 1 (by rfl) ⟨485630, by rfl⟩ : syracuseStep 647507 = 971261) B971261
theorem B516935 : Blo 299831 516935 := bstep (se 1 (by rfl) ⟨387701, by rfl⟩ : syracuseStep 516935 = 775403) B775403
theorem B680903 : Blo 299831 680903 := bstep (se 1 (by rfl) ⟨510677, by rfl⟩ : syracuseStep 680903 = 1021355) B1021355
theorem B648233 : Blo 299831 648233 := bstep (se 2 (by rfl) ⟨243087, by rfl⟩ : syracuseStep 648233 = 486175) B486175
theorem B451655 : Blo 299831 451655 := bstep (se 1 (by rfl) ⟨338741, by rfl⟩ : syracuseStep 451655 = 677483) B677483
theorem B681191 : Blo 299831 681191 := bstep (se 1 (by rfl) ⟨510893, by rfl⟩ : syracuseStep 681191 = 1021787) B1021787
theorem B451835 : Blo 299831 451835 := bstep (se 1 (by rfl) ⟨338876, by rfl⟩ : syracuseStep 451835 = 677753) B677753
theorem B1140095 : Blo 299831 1140095 := bstep (se 1 (by rfl) ⟨855071, by rfl⟩ : syracuseStep 1140095 = 1710143) B1710143
theorem B452201 : Blo 299831 452201 := bstep (se 2 (by rfl) ⟨169575, by rfl⟩ : syracuseStep 452201 = 339151) B339151
theorem B452351 : Blo 299831 452351 := bstep (se 1 (by rfl) ⟨339263, by rfl⟩ : syracuseStep 452351 = 678527) B678527
theorem B452585 : Blo 299831 452585 := bstep (se 2 (by rfl) ⟨169719, by rfl⟩ : syracuseStep 452585 = 339439) B339439
theorem B682091 : Blo 299831 682091 := bstep (se 1 (by rfl) ⟨511568, by rfl⟩ : syracuseStep 682091 = 1023137) B1023137
theorem B453023 : Blo 299831 453023 := bstep (se 1 (by rfl) ⟨339767, by rfl⟩ : syracuseStep 453023 = 679535) B679535
theorem B453161 : Blo 299831 453161 := bstep (se 2 (by rfl) ⟨169935, by rfl⟩ : syracuseStep 453161 = 339871) B339871
theorem B1534625 : Blo 299831 1534625 := bstep (se 2 (by rfl) ⟨575484, by rfl⟩ : syracuseStep 1534625 = 1150969) B1150969
theorem B453575 : Blo 299831 453575 := bstep (se 1 (by rfl) ⟨340181, by rfl⟩ : syracuseStep 453575 = 680363) B680363
theorem B1175419 : Blo 299831 1175419 := bstep (se 1 (by rfl) ⟨881564, by rfl⟩ : syracuseStep 1175419 = 1763129) B1763129
theorem B454823 : Blo 299831 454823 := bstep (se 1 (by rfl) ⟨341117, by rfl⟩ : syracuseStep 454823 = 682235) B682235
theorem B2618087 : Blo 299831 2618087 := bstep (se 1 (by rfl) ⟨1963565, by rfl⟩ : syracuseStep 2618087 = 3927131) B3927131
theorem B455399 : Blo 299831 455399 := bstep (se 1 (by rfl) ⟨341549, by rfl⟩ : syracuseStep 455399 = 683099) B683099
theorem B455663 : Blo 299831 455663 := bstep (se 1 (by rfl) ⟨341747, by rfl⟩ : syracuseStep 455663 = 683495) B683495
theorem B2749469 : Blo 299831 2749469 := bstep (se 3 (by rfl) ⟨515525, by rfl⟩ : syracuseStep 2749469 = 1031051) B1031051
theorem B1930553 : Blo 299831 1930553 := bstep (se 2 (by rfl) ⟨723957, by rfl⟩ : syracuseStep 1930553 = 1447915) B1447915
theorem B816713 : Blo 299831 816713 := bstep (se 2 (by rfl) ⟨306267, by rfl⟩ : syracuseStep 816713 = 612535) B612535
theorem B2193115 : Blo 299831 2193115 := bstep (se 1 (by rfl) ⟨1644836, by rfl⟩ : syracuseStep 2193115 = 3289673) B3289673
theorem B1930985 : Blo 299831 1930985 := bstep (se 2 (by rfl) ⟨724119, by rfl⟩ : syracuseStep 1930985 = 1448239) B1448239
theorem B721007 : Blo 299831 721007 := bstep (se 1 (by rfl) ⟨540755, by rfl⟩ : syracuseStep 721007 = 1081511) B1081511
theorem B1148039 : Blo 299831 1148039 := bstep (se 1 (by rfl) ⟨861029, by rfl⟩ : syracuseStep 1148039 = 1722059) B1722059
theorem B1443511 : Blo 299831 1443511 := bstep (se 1 (by rfl) ⟨1082633, by rfl⟩ : syracuseStep 1443511 = 2165267) B2165267
theorem B1017737 : Blo 299831 1017737 := bstep (se 2 (by rfl) ⟨381651, by rfl⟩ : syracuseStep 1017737 = 763303) B763303
theorem B6981565 : Blo 299831 6981565 := bstep (se 3 (by rfl) ⟨1309043, by rfl⟩ : syracuseStep 6981565 = 2618087) B2618087
theorem B1084711 : Blo 299831 1084711 := bstep (se 1 (by rfl) ⟨813533, by rfl⟩ : syracuseStep 1084711 = 1627067) B1627067
theorem B1020167 : Blo 299831 1020167 := bstep (se 1 (by rfl) ⟨765125, by rfl⟩ : syracuseStep 1020167 = 1530251) B1530251
theorem B1937803 : Blo 299831 1937803 := bstep (se 1 (by rfl) ⟨1453352, by rfl⟩ : syracuseStep 1937803 = 2906705) B2906705
theorem B42407023 : Blo 299831 42407023 := bstep (se 1 (by rfl) ⟨31805267, by rfl⟩ : syracuseStep 42407023 = 63610535) B63610535
theorem B1021193 : Blo 299831 1021193 := bstep (se 2 (by rfl) ⟨382947, by rfl⟩ : syracuseStep 1021193 = 765895) B765895
theorem B2299265 : Blo 299831 2299265 := bstep (se 2 (by rfl) ⟨862224, by rfl⟩ : syracuseStep 2299265 = 1724449) B1724449
theorem B1152427 : Blo 299831 1152427 := bstep (se 1 (by rfl) ⟨864320, by rfl⟩ : syracuseStep 1152427 = 1728641) B1728641
theorem B300495 : Blo 299831 300495 := bstep (se 1 (by rfl) ⟨225371, by rfl⟩ : syracuseStep 300495 = 450743) B450743
theorem B431671 : Blo 299831 431671 := bstep (se 1 (by rfl) ⟨323753, by rfl⟩ : syracuseStep 431671 = 647507) B647507
theorem B432155 : Blo 299831 432155 := bstep (se 1 (by rfl) ⟨324116, by rfl⟩ : syracuseStep 432155 = 648233) B648233
theorem B301103 : Blo 299831 301103 := bstep (se 1 (by rfl) ⟨225827, by rfl⟩ : syracuseStep 301103 = 451655) B451655
theorem B301223 : Blo 299831 301223 := bstep (se 1 (by rfl) ⟨225917, by rfl⟩ : syracuseStep 301223 = 451835) B451835
theorem B760063 : Blo 299831 760063 := bstep (se 1 (by rfl) ⟨570047, by rfl⟩ : syracuseStep 760063 = 1140095) B1140095
theorem B301467 : Blo 299831 301467 := bstep (se 1 (by rfl) ⟨226100, by rfl⟩ : syracuseStep 301467 = 452201) B452201
theorem B301567 : Blo 299831 301567 := bstep (se 1 (by rfl) ⟨226175, by rfl⟩ : syracuseStep 301567 = 452351) B452351
theorem B858671 : Blo 299831 858671 := bstep (se 1 (by rfl) ⟨644003, by rfl⟩ : syracuseStep 858671 = 1288007) B1288007
theorem B2562617 : Blo 299831 2562617 := bstep (se 2 (by rfl) ⟨960981, by rfl⟩ : syracuseStep 2562617 = 1921963) B1921963
theorem B1284761 : Blo 299831 1284761 := bstep (se 2 (by rfl) ⟨481785, by rfl⟩ : syracuseStep 1284761 = 963571) B963571
theorem B301723 : Blo 299831 301723 := bstep (se 1 (by rfl) ⟨226292, by rfl⟩ : syracuseStep 301723 = 452585) B452585
theorem B302015 : Blo 299831 302015 := bstep (se 1 (by rfl) ⟨226511, by rfl⟩ : syracuseStep 302015 = 453023) B453023
theorem B302107 : Blo 299831 302107 := bstep (se 1 (by rfl) ⟨226580, by rfl⟩ : syracuseStep 302107 = 453161) B453161
theorem B1023083 : Blo 299831 1023083 := bstep (se 1 (by rfl) ⟨767312, by rfl⟩ : syracuseStep 1023083 = 1534625) B1534625
theorem B302383 : Blo 299831 302383 := bstep (se 1 (by rfl) ⟨226787, by rfl⟩ : syracuseStep 302383 = 453575) B453575
theorem B2924153 : Blo 299831 2924153 := bstep (se 2 (by rfl) ⟨1096557, by rfl⟩ : syracuseStep 2924153 = 2193115) B2193115
theorem B8888345 : Blo 299831 8888345 := bstep (se 2 (by rfl) ⟨3333129, by rfl⟩ : syracuseStep 8888345 = 6666259) B6666259
theorem B303215 : Blo 299831 303215 := bstep (se 1 (by rfl) ⟨227411, by rfl⟩ : syracuseStep 303215 = 454823) B454823
theorem B1712603 : Blo 299831 1712603 := bstep (se 1 (by rfl) ⟨1284452, by rfl⟩ : syracuseStep 1712603 = 2568905) B2568905
theorem B303599 : Blo 299831 303599 := bstep (se 1 (by rfl) ⟨227699, by rfl⟩ : syracuseStep 303599 = 455399) B455399
theorem B303775 : Blo 299831 303775 := bstep (se 1 (by rfl) ⟨227831, by rfl⟩ : syracuseStep 303775 = 455663) B455663
theorem B1287035 : Blo 299831 1287035 := bstep (se 1 (by rfl) ⟨965276, by rfl⟩ : syracuseStep 1287035 = 1930553) B1930553
theorem B1287323 : Blo 299831 1287323 := bstep (se 1 (by rfl) ⟨965492, by rfl⟩ : syracuseStep 1287323 = 1930985) B1930985
theorem B5187563 : Blo 299831 5187563 := bstep (se 1 (by rfl) ⟨3890672, by rfl⟩ : syracuseStep 5187563 = 7781345) B7781345
theorem B862271 : Blo 299831 862271 := bstep (se 1 (by rfl) ⟨646703, by rfl⟩ : syracuseStep 862271 = 1293407) B1293407
theorem B338431 : Blo 299831 338431 := bstep (se 1 (by rfl) ⟨253823, by rfl⟩ : syracuseStep 338431 = 507647) B507647
theorem B928475 : Blo 299831 928475 := bstep (se 1 (by rfl) ⟨696356, by rfl⟩ : syracuseStep 928475 = 1392713) B1392713
theorem B338791 : Blo 299831 338791 := bstep (se 1 (by rfl) ⟨254093, by rfl⟩ : syracuseStep 338791 = 508187) B508187
theorem B766007 : Blo 299831 766007 := bstep (se 1 (by rfl) ⟨574505, by rfl⟩ : syracuseStep 766007 = 1149011) B1149011
theorem B766817 : Blo 299831 766817 := bstep (se 2 (by rfl) ⟨287556, by rfl⟩ : syracuseStep 766817 = 575113) B575113
theorem B341023 : Blo 299831 341023 := bstep (se 1 (by rfl) ⟨255767, by rfl⟩ : syracuseStep 341023 = 511535) B511535
theorem B767465 : Blo 299831 767465 := bstep (se 2 (by rfl) ⟨287799, by rfl⟩ : syracuseStep 767465 = 575599) B575599
theorem B2373167 : Blo 299831 2373167 := bstep (se 1 (by rfl) ⟨1779875, by rfl⟩ : syracuseStep 2373167 = 3559751) B3559751
theorem B767657 : Blo 299831 767657 := bstep (se 2 (by rfl) ⟨287871, by rfl⟩ : syracuseStep 767657 = 575743) B575743
theorem B1522151 : Blo 299831 1522151 := bstep (se 1 (by rfl) ⟨1141613, by rfl⟩ : syracuseStep 1522151 = 2283227) B2283227
theorem B965287 : Blo 299831 965287 := bstep (se 1 (by rfl) ⟨723965, by rfl⟩ : syracuseStep 965287 = 1447931) B1447931
theorem B13253375 : Blo 299831 13253375 := bstep (se 1 (by rfl) ⟨9940031, by rfl⟩ : syracuseStep 13253375 = 19880063) B19880063
theorem B8731871 : Blo 299831 8731871 := bstep (se 1 (by rfl) ⟨6548903, by rfl⟩ : syracuseStep 8731871 = 13097807) B13097807
theorem B572827 : Blo 299831 572827 := bstep (se 1 (by rfl) ⟨429620, by rfl⟩ : syracuseStep 572827 = 859241) B859241
theorem B1228699 : Blo 299831 1228699 := bstep (se 1 (by rfl) ⟨921524, by rfl⟩ : syracuseStep 1228699 = 1843049) B1843049
theorem B1458121 : Blo 299831 1458121 := bstep (se 2 (by rfl) ⟨546795, by rfl⟩ : syracuseStep 1458121 = 1093591) B1093591
theorem B17515045 : Blo 299831 17515045 := bstep (se 4 (by rfl) ⟨1642035, by rfl⟩ : syracuseStep 17515045 = 3284071) B3284071
theorem B344623 : Blo 299831 344623 := bstep (se 1 (by rfl) ⟨258467, by rfl⟩ : syracuseStep 344623 = 516935) B516935
theorem B511103 : Blo 299831 511103 := bstep (se 1 (by rfl) ⟨383327, by rfl⟩ : syracuseStep 511103 = 766655) B766655
theorem B969889 : Blo 299831 969889 := bstep (se 2 (by rfl) ⟨363708, by rfl⟩ : syracuseStep 969889 = 727417) B727417
theorem B380143 : Blo 299831 380143 := bstep (se 1 (by rfl) ⟨285107, by rfl⟩ : syracuseStep 380143 = 570215) B570215
theorem B1297711 : Blo 299831 1297711 := bstep (se 1 (by rfl) ⟨973283, by rfl⟩ : syracuseStep 1297711 = 1946567) B1946567
theorem B44092997 : Blo 299831 44092997 := bstep (se 4 (by rfl) ⟨4133718, by rfl⟩ : syracuseStep 44092997 = 8267437) B8267437
theorem B642671 : Blo 299831 642671 := bstep (se 1 (by rfl) ⟨482003, by rfl⟩ : syracuseStep 642671 = 964007) B964007
theorem B544475 : Blo 299831 544475 := bstep (se 1 (by rfl) ⟨408356, by rfl⟩ : syracuseStep 544475 = 816713) B816713
theorem B3854587 : Blo 299831 3854587 := bstep (se 1 (by rfl) ⟨2890940, by rfl⟩ : syracuseStep 3854587 = 5781881) B5781881
theorem B643423 : Blo 299831 643423 := bstep (se 1 (by rfl) ⟨482567, by rfl⟩ : syracuseStep 643423 = 965135) B965135
theorem B677375 : Blo 299831 677375 := bstep (se 1 (by rfl) ⟨508031, by rfl⟩ : syracuseStep 677375 = 1016063) B1016063
theorem B383935 : Blo 299831 383935 := bstep (se 1 (by rfl) ⟨287951, by rfl⟩ : syracuseStep 383935 = 575903) B575903
theorem B679175 : Blo 299831 679175 := bstep (se 1 (by rfl) ⟨509381, by rfl⟩ : syracuseStep 679175 = 1018763) B1018763
theorem B450299 : Blo 299831 450299 := bstep (se 1 (by rfl) ⟨337724, by rfl⟩ : syracuseStep 450299 = 675449) B675449
theorem B450431 : Blo 299831 450431 := bstep (se 1 (by rfl) ⟨337823, by rfl⟩ : syracuseStep 450431 = 675647) B675647
theorem B450503 : Blo 299831 450503 := bstep (se 1 (by rfl) ⟨337877, by rfl⟩ : syracuseStep 450503 = 675755) B675755
theorem B679931 : Blo 299831 679931 := bstep (se 1 (by rfl) ⟨509948, by rfl⟩ : syracuseStep 679931 = 1019897) B1019897
theorem B7331917 : Blo 299831 7331917 := bstep (se 3 (by rfl) ⟨1374734, by rfl⟩ : syracuseStep 7331917 = 2749469) B2749469
theorem B450671 : Blo 299831 450671 := bstep (se 1 (by rfl) ⟨338003, by rfl⟩ : syracuseStep 450671 = 676007) B676007
theorem B680057 : Blo 299831 680057 := bstep (se 2 (by rfl) ⟨255021, by rfl⟩ : syracuseStep 680057 = 510043) B510043
theorem B1401001 : Blo 299831 1401001 := bstep (se 2 (by rfl) ⟨525375, by rfl⟩ : syracuseStep 1401001 = 1050751) B1050751
theorem B1139291 : Blo 299831 1139291 := bstep (se 1 (by rfl) ⟨854468, by rfl⟩ : syracuseStep 1139291 = 1708937) B1708937
theorem B1106759 : Blo 299831 1106759 := bstep (se 1 (by rfl) ⟨830069, by rfl⟩ : syracuseStep 1106759 = 1660139) B1660139
theorem B1139579 : Blo 299831 1139579 := bstep (se 1 (by rfl) ⟨854684, by rfl⟩ : syracuseStep 1139579 = 1709369) B1709369
theorem B680831 : Blo 299831 680831 := bstep (se 1 (by rfl) ⟨510623, by rfl⟩ : syracuseStep 680831 = 1021247) B1021247
theorem B451577 : Blo 299831 451577 := bstep (se 2 (by rfl) ⟨169341, by rfl⟩ : syracuseStep 451577 = 338683) B338683
theorem B451625 : Blo 299831 451625 := bstep (se 2 (by rfl) ⟨169359, by rfl⟩ : syracuseStep 451625 = 338719) B338719
theorem B484489 : Blo 299831 484489 := bstep (se 2 (by rfl) ⟨181683, by rfl⟩ : syracuseStep 484489 = 363367) B363367
theorem B517423 : Blo 299831 517423 := bstep (se 1 (by rfl) ⟨388067, by rfl⟩ : syracuseStep 517423 = 776135) B776135
theorem B1140065 : Blo 299831 1140065 := bstep (se 2 (by rfl) ⟨427524, by rfl⟩ : syracuseStep 1140065 = 855049) B855049
theorem B452255 : Blo 299831 452255 := bstep (se 1 (by rfl) ⟨339191, by rfl⟩ : syracuseStep 452255 = 678383) B678383
theorem B1567225 : Blo 299831 1567225 := bstep (se 2 (by rfl) ⟨587709, by rfl⟩ : syracuseStep 1567225 = 1175419) B1175419
theorem B1632905 : Blo 299831 1632905 := bstep (se 2 (by rfl) ⟨612339, by rfl⟩ : syracuseStep 1632905 = 1224679) B1224679
theorem B453353 : Blo 299831 453353 := bstep (se 2 (by rfl) ⟨170007, by rfl⟩ : syracuseStep 453353 = 340015) B340015
theorem B453935 : Blo 299831 453935 := bstep (se 1 (by rfl) ⟨340451, by rfl⟩ : syracuseStep 453935 = 680903) B680903
theorem B683423 : Blo 299831 683423 := bstep (se 1 (by rfl) ⟨512567, by rfl⟩ : syracuseStep 683423 = 1025135) B1025135
theorem B454127 : Blo 299831 454127 := bstep (se 1 (by rfl) ⟨340595, by rfl⟩ : syracuseStep 454127 = 681191) B681191
theorem B5533231 : Blo 299831 5533231 := bstep (se 1 (by rfl) ⟨4149923, by rfl⟩ : syracuseStep 5533231 = 8299847) B8299847
theorem B454265 : Blo 299831 454265 := bstep (se 2 (by rfl) ⟨170349, by rfl⟩ : syracuseStep 454265 = 340699) B340699
theorem B1142495 : Blo 299831 1142495 := bstep (se 1 (by rfl) ⟨856871, by rfl⟩ : syracuseStep 1142495 = 1713743) B1713743
theorem B2584487 : Blo 299831 2584487 := bstep (se 1 (by rfl) ⟨1938365, by rfl⟩ : syracuseStep 2584487 = 3876731) B3876731
theorem B454727 : Blo 299831 454727 := bstep (se 1 (by rfl) ⟨341045, by rfl⟩ : syracuseStep 454727 = 682091) B682091
theorem B1536731 : Blo 299831 1536731 := bstep (se 1 (by rfl) ⟨1152548, by rfl⟩ : syracuseStep 1536731 = 2305097) B2305097
theorem B2586127 : Blo 299831 2586127 := bstep (se 1 (by rfl) ⟨1939595, by rfl⟩ : syracuseStep 2586127 = 3879191) B3879191
theorem B1014119 : Blo 299831 1014119 := bstep (se 1 (by rfl) ⟨760589, by rfl⟩ : syracuseStep 1014119 = 1521179) B1521179
theorem B1146095 : Blo 299831 1146095 := bstep (se 1 (by rfl) ⟨859571, by rfl⟩ : syracuseStep 1146095 = 1719143) B1719143
theorem B459497 : Blo 299831 459497 := bstep (se 2 (by rfl) ⟨172311, by rfl⟩ : syracuseStep 459497 = 344623) B344623
theorem B689897 : Blo 299831 689897 := bstep (se 2 (by rfl) ⟨258711, by rfl⟩ : syracuseStep 689897 = 517423) B517423
theorem B29395331 : Blo 299831 29395331 := bstep (se 1 (by rfl) ⟨22046498, by rfl⟩ : syracuseStep 29395331 = 44092997) B44092997
theorem B428447 : Blo 299831 428447 := bstep (se 1 (by rfl) ⟨321335, by rfl⟩ : syracuseStep 428447 = 642671) B642671
theorem B362983 : Blo 299831 362983 := bstep (se 1 (by rfl) ⟨272237, by rfl⟩ : syracuseStep 362983 = 544475) B544475
theorem B9308753 : Blo 299831 9308753 := bstep (se 2 (by rfl) ⟨3490782, by rfl⟩ : syracuseStep 9308753 = 6981565) B6981565
theorem B29888021 : Blo 299831 29888021 := bstep (se 6 (by rfl) ⟨700500, by rfl⟩ : syracuseStep 29888021 = 1401001) B1401001
theorem B5148197 : Blo 299831 5148197 := bstep (se 4 (by rfl) ⟨482643, by rfl⟩ : syracuseStep 5148197 = 965287) B965287
theorem B1708411 : Blo 299831 1708411 := bstep (se 1 (by rfl) ⟨1281308, by rfl⟩ : syracuseStep 1708411 = 2562617) B2562617
theorem B1446281 : Blo 299831 1446281 := bstep (se 2 (by rfl) ⟨542355, by rfl⟩ : syracuseStep 1446281 = 1084711) B1084711
theorem B856507 : Blo 299831 856507 := bstep (se 1 (by rfl) ⟨642380, by rfl⟩ : syracuseStep 856507 = 1284761) B1284761
theorem B7377641 : Blo 299831 7377641 := bstep (se 2 (by rfl) ⟨2766615, by rfl⟩ : syracuseStep 7377641 = 5533231) B5533231
theorem B300199 : Blo 299831 300199 := bstep (se 1 (by rfl) ⟨225149, by rfl⟩ : syracuseStep 300199 = 450299) B450299
theorem B300287 : Blo 299831 300287 := bstep (se 1 (by rfl) ⟨225215, by rfl⟩ : syracuseStep 300287 = 450431) B450431
theorem B300335 : Blo 299831 300335 := bstep (se 1 (by rfl) ⟨225251, by rfl⟩ : syracuseStep 300335 = 450503) B450503
theorem B1152413 : Blo 299831 1152413 := bstep (se 3 (by rfl) ⟨216077, by rfl⟩ : syracuseStep 1152413 = 432155) B432155
theorem B300447 : Blo 299831 300447 := bstep (se 1 (by rfl) ⟨225335, by rfl⟩ : syracuseStep 300447 = 450671) B450671
theorem B759527 : Blo 299831 759527 := bstep (se 1 (by rfl) ⟨569645, by rfl⟩ : syracuseStep 759527 = 1139291) B1139291
theorem B857897 : Blo 299831 857897 := bstep (se 2 (by rfl) ⟨321711, by rfl⟩ : syracuseStep 857897 = 643423) B643423
theorem B759719 : Blo 299831 759719 := bstep (se 1 (by rfl) ⟨569789, by rfl⟩ : syracuseStep 759719 = 1139579) B1139579
theorem B858023 : Blo 299831 858023 := bstep (se 1 (by rfl) ⟨643517, by rfl⟩ : syracuseStep 858023 = 1287035) B1287035
theorem B301051 : Blo 299831 301051 := bstep (se 1 (by rfl) ⟨225788, by rfl⟩ : syracuseStep 301051 = 451577) B451577
theorem B301083 : Blo 299831 301083 := bstep (se 1 (by rfl) ⟨225812, by rfl⟩ : syracuseStep 301083 = 451625) B451625
theorem B858215 : Blo 299831 858215 := bstep (se 1 (by rfl) ⟨643661, by rfl⟩ : syracuseStep 858215 = 1287323) B1287323
theorem B760043 : Blo 299831 760043 := bstep (se 1 (by rfl) ⟨570032, by rfl⟩ : syracuseStep 760043 = 1140065) B1140065
theorem B301503 : Blo 299831 301503 := bstep (se 1 (by rfl) ⟨226127, by rfl⟩ : syracuseStep 301503 = 452255) B452255
theorem B1088603 : Blo 299831 1088603 := bstep (se 1 (by rfl) ⟨816452, by rfl⟩ : syracuseStep 1088603 = 1632905) B1632905
theorem B302235 : Blo 299831 302235 := bstep (se 1 (by rfl) ⟨226676, by rfl⟩ : syracuseStep 302235 = 453353) B453353
theorem B3448169 : Blo 299831 3448169 := bstep (se 2 (by rfl) ⟨1293063, by rfl⟩ : syracuseStep 3448169 = 2586127) B2586127
theorem B302623 : Blo 299831 302623 := bstep (se 1 (by rfl) ⟨226967, by rfl⟩ : syracuseStep 302623 = 453935) B453935
theorem B302751 : Blo 299831 302751 := bstep (se 1 (by rfl) ⟨227063, by rfl⟩ : syracuseStep 302751 = 454127) B454127
theorem B302843 : Blo 299831 302843 := bstep (se 1 (by rfl) ⟨227132, by rfl⟩ : syracuseStep 302843 = 454265) B454265
theorem B761663 : Blo 299831 761663 := bstep (se 1 (by rfl) ⟨571247, by rfl⟩ : syracuseStep 761663 = 1142495) B1142495
theorem B303151 : Blo 299831 303151 := bstep (se 1 (by rfl) ⟨227363, by rfl⟩ : syracuseStep 303151 = 454727) B454727
theorem B1024487 : Blo 299831 1024487 := bstep (se 1 (by rfl) ⟨768365, by rfl⟩ : syracuseStep 1024487 = 1536731) B1536731
theorem B1582111 : Blo 299831 1582111 := bstep (se 1 (by rfl) ⟨1186583, by rfl⟩ : syracuseStep 1582111 = 2373167) B2373167
theorem B763769 : Blo 299831 763769 := bstep (se 2 (by rfl) ⟨286413, by rfl⟩ : syracuseStep 763769 = 572827) B572827
theorem B764063 : Blo 299831 764063 := bstep (se 1 (by rfl) ⟨573047, by rfl⟩ : syracuseStep 764063 = 1146095) B1146095
theorem B1944161 : Blo 299831 1944161 := bstep (se 2 (by rfl) ⟨729060, by rfl⟩ : syracuseStep 1944161 = 1458121) B1458121
theorem B9775889 : Blo 299831 9775889 := bstep (se 2 (by rfl) ⟨3665958, by rfl⟩ : syracuseStep 9775889 = 7331917) B7331917
theorem B765359 : Blo 299831 765359 := bstep (se 1 (by rfl) ⟨574019, by rfl⟩ : syracuseStep 765359 = 1148039) B1148039
theorem B340735 : Blo 299831 340735 := bstep (se 1 (by rfl) ⟨255551, by rfl⟩ : syracuseStep 340735 = 511103) B511103
theorem B1293185 : Blo 299831 1293185 := bstep (se 2 (by rfl) ⟨484944, by rfl⟩ : syracuseStep 1293185 = 969889) B969889
theorem B506857 : Blo 299831 506857 := bstep (se 2 (by rfl) ⟨190071, by rfl⟩ : syracuseStep 506857 = 380143) B380143
theorem B572447 : Blo 299831 572447 := bstep (se 1 (by rfl) ⟨429335, by rfl⟩ : syracuseStep 572447 = 858671) B858671
theorem B1949435 : Blo 299831 1949435 := bstep (se 1 (by rfl) ⟨1462076, by rfl⟩ : syracuseStep 1949435 = 2924153) B2924153
theorem B737839 : Blo 299831 737839 := bstep (se 1 (by rfl) ⟨553379, by rfl⟩ : syracuseStep 737839 = 1106759) B1106759
theorem B3458375 : Blo 299831 3458375 := bstep (se 1 (by rfl) ⟨2593781, by rfl⟩ : syracuseStep 3458375 = 5187563) B5187563
theorem B574847 : Blo 299831 574847 := bstep (se 1 (by rfl) ⟨431135, by rfl⟩ : syracuseStep 574847 = 862271) B862271
theorem B56542697 : Blo 299831 56542697 := bstep (se 2 (by rfl) ⟨21203511, by rfl⟩ : syracuseStep 56542697 = 42407023) B42407023
theorem B575561 : Blo 299831 575561 := bstep (se 2 (by rfl) ⟨215835, by rfl⟩ : syracuseStep 575561 = 431671) B431671
theorem B1722991 : Blo 299831 1722991 := bstep (se 1 (by rfl) ⟨1292243, by rfl⟩ : syracuseStep 1722991 = 2584487) B2584487
theorem B510671 : Blo 299831 510671 := bstep (se 1 (by rfl) ⟨383003, by rfl⟩ : syracuseStep 510671 = 766007) B766007
theorem B511211 : Blo 299831 511211 := bstep (se 1 (by rfl) ⟨383408, by rfl⟩ : syracuseStep 511211 = 766817) B766817
theorem B511643 : Blo 299831 511643 := bstep (se 1 (by rfl) ⟨383732, by rfl⟩ : syracuseStep 511643 = 767465) B767465
theorem B511771 : Blo 299831 511771 := bstep (se 1 (by rfl) ⟨383828, by rfl⟩ : syracuseStep 511771 = 767657) B767657
theorem B511913 : Blo 299831 511913 := bstep (se 2 (by rfl) ⟨191967, by rfl⟩ : syracuseStep 511913 = 383935) B383935
theorem B676079 : Blo 299831 676079 := bstep (se 1 (by rfl) ⟨507059, by rfl⟩ : syracuseStep 676079 = 1014119) B1014119
theorem B8835583 : Blo 299831 8835583 := bstep (se 1 (by rfl) ⟨6626687, by rfl⟩ : syracuseStep 8835583 = 13253375) B13253375
theorem B5821247 : Blo 299831 5821247 := bstep (se 1 (by rfl) ⟨4365935, by rfl⟩ : syracuseStep 5821247 = 8731871) B8731871
theorem B480671 : Blo 299831 480671 := bstep (se 1 (by rfl) ⟨360503, by rfl⟩ : syracuseStep 480671 = 721007) B721007
theorem B678491 : Blo 299831 678491 := bstep (se 1 (by rfl) ⟨508868, by rfl⟩ : syracuseStep 678491 = 1017737) B1017737
theorem B645985 : Blo 299831 645985 := bstep (se 2 (by rfl) ⟨242244, by rfl⟩ : syracuseStep 645985 = 484489) B484489
theorem B1924681 : Blo 299831 1924681 := bstep (se 2 (by rfl) ⟨721755, by rfl⟩ : syracuseStep 1924681 = 1443511) B1443511
theorem B680111 : Blo 299831 680111 := bstep (se 1 (by rfl) ⟨510083, by rfl⟩ : syracuseStep 680111 = 1020167) B1020167
theorem B93413573 : Blo 299831 93413573 := bstep (se 4 (by rfl) ⟨8757522, by rfl⟩ : syracuseStep 93413573 = 17515045) B17515045
theorem B2089633 : Blo 299831 2089633 := bstep (se 2 (by rfl) ⟨783612, by rfl⟩ : syracuseStep 2089633 = 1567225) B1567225
theorem B451241 : Blo 299831 451241 := bstep (se 2 (by rfl) ⟨169215, by rfl⟩ : syracuseStep 451241 = 338431) B338431
theorem B680795 : Blo 299831 680795 := bstep (se 1 (by rfl) ⟨510596, by rfl⟩ : syracuseStep 680795 = 1021193) B1021193
theorem B1532843 : Blo 299831 1532843 := bstep (se 1 (by rfl) ⟨1149632, by rfl⟩ : syracuseStep 1532843 = 2299265) B2299265
theorem B451583 : Blo 299831 451583 := bstep (se 1 (by rfl) ⟨338687, by rfl⟩ : syracuseStep 451583 = 677375) B677375
theorem B451721 : Blo 299831 451721 := bstep (se 2 (by rfl) ⟨169395, by rfl⟩ : syracuseStep 451721 = 338791) B338791
theorem B1730281 : Blo 299831 1730281 := bstep (se 2 (by rfl) ⟨648855, by rfl⟩ : syracuseStep 1730281 = 1297711) B1297711
theorem B682055 : Blo 299831 682055 := bstep (se 1 (by rfl) ⟨511541, by rfl⟩ : syracuseStep 682055 = 1023083) B1023083
theorem B452783 : Blo 299831 452783 := bstep (se 1 (by rfl) ⟨339587, by rfl⟩ : syracuseStep 452783 = 679175) B679175
theorem B453287 : Blo 299831 453287 := bstep (se 1 (by rfl) ⟨339965, by rfl⟩ : syracuseStep 453287 = 679931) B679931
theorem B5925563 : Blo 299831 5925563 := bstep (se 1 (by rfl) ⟨4444172, by rfl⟩ : syracuseStep 5925563 = 8888345) B8888345
theorem B453371 : Blo 299831 453371 := bstep (se 1 (by rfl) ⟨340028, by rfl⟩ : syracuseStep 453371 = 680057) B680057
theorem B1141735 : Blo 299831 1141735 := bstep (se 1 (by rfl) ⟨856301, by rfl⟩ : syracuseStep 1141735 = 1712603) B1712603
theorem B5139449 : Blo 299831 5139449 := bstep (se 2 (by rfl) ⟨1927293, by rfl⟩ : syracuseStep 5139449 = 3854587) B3854587
theorem B2583737 : Blo 299831 2583737 := bstep (se 2 (by rfl) ⟨968901, by rfl⟩ : syracuseStep 2583737 = 1937803) B1937803
theorem B453887 : Blo 299831 453887 := bstep (se 1 (by rfl) ⟨340415, by rfl⟩ : syracuseStep 453887 = 680831) B680831
theorem B454697 : Blo 299831 454697 := bstep (se 2 (by rfl) ⟨170511, by rfl⟩ : syracuseStep 454697 = 341023) B341023
theorem B618983 : Blo 299831 618983 := bstep (se 1 (by rfl) ⟨464237, by rfl⟩ : syracuseStep 618983 = 928475) B928475
theorem B1536569 : Blo 299831 1536569 := bstep (se 2 (by rfl) ⟨576213, by rfl⟩ : syracuseStep 1536569 = 1152427) B1152427
theorem B455615 : Blo 299831 455615 := bstep (se 1 (by rfl) ⟨341711, by rfl⟩ : syracuseStep 455615 = 683423) B683423
theorem B1013417 : Blo 299831 1013417 := bstep (se 2 (by rfl) ⟨380031, by rfl⟩ : syracuseStep 1013417 = 760063) B760063
theorem B1014767 : Blo 299831 1014767 := bstep (se 1 (by rfl) ⟨761075, by rfl⟩ : syracuseStep 1014767 = 1522151) B1522151
theorem B1638265 : Blo 299831 1638265 := bstep (se 2 (by rfl) ⟨614349, by rfl⟩ : syracuseStep 1638265 = 1228699) B1228699
theorem B2786177 : Blo 299831 2786177 := bstep (se 2 (by rfl) ⟨1044816, by rfl⟩ : syracuseStep 2786177 = 2089633) B2089633
theorem B459931 : Blo 299831 459931 := bstep (se 1 (by rfl) ⟨344948, by rfl⟩ : syracuseStep 459931 = 689897) B689897
theorem B19596887 : Blo 299831 19596887 := bstep (se 1 (by rfl) ⟨14697665, by rfl⟩ : syracuseStep 19596887 = 29395331) B29395331
theorem B19925347 : Blo 299831 19925347 := bstep (se 1 (by rfl) ⟨14944010, by rfl⟩ : syracuseStep 19925347 = 29888021) B29888021
theorem B3935141 : Blo 299831 3935141 := bstep (se 4 (by rfl) ⟨368919, by rfl⟩ : syracuseStep 3935141 = 737839) B737839
theorem B4918427 : Blo 299831 4918427 := bstep (se 1 (by rfl) ⟨3688820, by rfl⟩ : syracuseStep 4918427 = 7377641) B7377641
theorem B2297321 : Blo 299831 2297321 := bstep (se 2 (by rfl) ⟨861495, by rfl⟩ : syracuseStep 2297321 = 1722991) B1722991
theorem B3445253 : Blo 299831 3445253 := bstep (se 4 (by rfl) ⟨322992, by rfl⟩ : syracuseStep 3445253 = 645985) B645985
theorem B725735 : Blo 299831 725735 := bstep (se 1 (by rfl) ⟨544301, by rfl⟩ : syracuseStep 725735 = 1088603) B1088603
theorem B2298779 : Blo 299831 2298779 := bstep (se 1 (by rfl) ⟨1724084, by rfl⟩ : syracuseStep 2298779 = 3448169) B3448169
theorem B300827 : Blo 299831 300827 := bstep (se 1 (by rfl) ⟨225620, by rfl⟩ : syracuseStep 300827 = 451241) B451241
theorem B1021895 : Blo 299831 1021895 := bstep (se 1 (by rfl) ⟨766421, by rfl⟩ : syracuseStep 1021895 = 1532843) B1532843
theorem B301055 : Blo 299831 301055 := bstep (se 1 (by rfl) ⟨225791, by rfl⟩ : syracuseStep 301055 = 451583) B451583
theorem B301147 : Blo 299831 301147 := bstep (se 1 (by rfl) ⟨225860, by rfl⟩ : syracuseStep 301147 = 451721) B451721
theorem B301855 : Blo 299831 301855 := bstep (se 1 (by rfl) ⟨226391, by rfl⟩ : syracuseStep 301855 = 452783) B452783
theorem B302191 : Blo 299831 302191 := bstep (se 1 (by rfl) ⟨226643, by rfl⟩ : syracuseStep 302191 = 453287) B453287
theorem B302247 : Blo 299831 302247 := bstep (se 1 (by rfl) ⟨226685, by rfl⟩ : syracuseStep 302247 = 453371) B453371
theorem B302591 : Blo 299831 302591 := bstep (se 1 (by rfl) ⟨226943, by rfl⟩ : syracuseStep 302591 = 453887) B453887
theorem B303131 : Blo 299831 303131 := bstep (se 1 (by rfl) ⟨227348, by rfl⟩ : syracuseStep 303131 = 454697) B454697
theorem B1024379 : Blo 299831 1024379 := bstep (se 1 (by rfl) ⟨768284, by rfl⟩ : syracuseStep 1024379 = 1536569) B1536569
theorem B303743 : Blo 299831 303743 := bstep (se 1 (by rfl) ⟨227807, by rfl⟩ : syracuseStep 303743 = 455615) B455615
theorem B862123 : Blo 299831 862123 := bstep (se 1 (by rfl) ⟨646592, by rfl⟩ : syracuseStep 862123 = 1293185) B1293185
theorem B2566241 : Blo 299831 2566241 := bstep (se 2 (by rfl) ⟨962340, by rfl⟩ : syracuseStep 2566241 = 1924681) B1924681
theorem B2305583 : Blo 299831 2305583 := bstep (se 1 (by rfl) ⟨1729187, by rfl⟩ : syracuseStep 2305583 = 3458375) B3458375
theorem B37695131 : Blo 299831 37695131 := bstep (se 1 (by rfl) ⟨28271348, by rfl⟩ : syracuseStep 37695131 = 56542697) B56542697
theorem B6205835 : Blo 299831 6205835 := bstep (se 1 (by rfl) ⟨4654376, by rfl⟩ : syracuseStep 6205835 = 9308753) B9308753
theorem B340447 : Blo 299831 340447 := bstep (se 1 (by rfl) ⟨255335, by rfl⟩ : syracuseStep 340447 = 510671) B510671
theorem B1225325 : Blo 299831 1225325 := bstep (se 3 (by rfl) ⟨229748, by rfl⟩ : syracuseStep 1225325 = 459497) B459497
theorem B340807 : Blo 299831 340807 := bstep (se 1 (by rfl) ⟨255605, by rfl⟩ : syracuseStep 340807 = 511211) B511211
theorem B2307041 : Blo 299831 2307041 := bstep (se 2 (by rfl) ⟨865140, by rfl⟩ : syracuseStep 2307041 = 1730281) B1730281
theorem B341095 : Blo 299831 341095 := bstep (se 1 (by rfl) ⟨255821, by rfl⟩ : syracuseStep 341095 = 511643) B511643
theorem B341275 : Blo 299831 341275 := bstep (se 1 (by rfl) ⟨255956, by rfl⟩ : syracuseStep 341275 = 511913) B511913
theorem B964187 : Blo 299831 964187 := bstep (se 1 (by rfl) ⟨723140, by rfl⟩ : syracuseStep 964187 = 1446281) B1446281
theorem B3880831 : Blo 299831 3880831 := bstep (se 1 (by rfl) ⟨2910623, by rfl⟩ : syracuseStep 3880831 = 5821247) B5821247
theorem B768275 : Blo 299831 768275 := bstep (se 1 (by rfl) ⟨576206, by rfl⟩ : syracuseStep 768275 = 1152413) B1152413
theorem B506351 : Blo 299831 506351 := bstep (se 1 (by rfl) ⟨379763, by rfl⟩ : syracuseStep 506351 = 759527) B759527
theorem B571931 : Blo 299831 571931 := bstep (se 1 (by rfl) ⟨428948, by rfl⟩ : syracuseStep 571931 = 857897) B857897
theorem B506479 : Blo 299831 506479 := bstep (se 1 (by rfl) ⟨379859, by rfl⟩ : syracuseStep 506479 = 759719) B759719
theorem B572015 : Blo 299831 572015 := bstep (se 1 (by rfl) ⟨429011, by rfl⟩ : syracuseStep 572015 = 858023) B858023
theorem B1522313 : Blo 299831 1522313 := bstep (se 2 (by rfl) ⟨570867, by rfl⟩ : syracuseStep 1522313 = 1141735) B1141735
theorem B506695 : Blo 299831 506695 := bstep (se 1 (by rfl) ⟨380021, by rfl⟩ : syracuseStep 506695 = 760043) B760043
theorem B6602485 : Blo 299831 6602485 := bstep (se 5 (by rfl) ⟨309491, by rfl⟩ : syracuseStep 6602485 = 618983) B618983
theorem B507775 : Blo 299831 507775 := bstep (se 1 (by rfl) ⟨380831, by rfl⟩ : syracuseStep 507775 = 761663) B761663
theorem B62275715 : Blo 299831 62275715 := bstep (se 1 (by rfl) ⟨46706786, by rfl⟩ : syracuseStep 62275715 = 93413573) B93413573
theorem B8437925 : Blo 299831 8437925 := bstep (se 4 (by rfl) ⟨791055, by rfl⟩ : syracuseStep 8437925 = 1582111) B1582111
theorem B2277881 : Blo 299831 2277881 := bstep (se 2 (by rfl) ⟨854205, by rfl⟩ : syracuseStep 2277881 = 1708411) B1708411
theorem B11780777 : Blo 299831 11780777 := bstep (se 2 (by rfl) ⟨4417791, by rfl⟩ : syracuseStep 11780777 = 8835583) B8835583
theorem B509179 : Blo 299831 509179 := bstep (se 1 (by rfl) ⟨381884, by rfl⟩ : syracuseStep 509179 = 763769) B763769
theorem B509375 : Blo 299831 509375 := bstep (se 1 (by rfl) ⟨382031, by rfl⟩ : syracuseStep 509375 = 764063) B764063
theorem B1296107 : Blo 299831 1296107 := bstep (se 1 (by rfl) ⟨972080, by rfl⟩ : syracuseStep 1296107 = 1944161) B1944161
theorem B3950375 : Blo 299831 3950375 := bstep (se 1 (by rfl) ⟨2962781, by rfl⟩ : syracuseStep 3950375 = 5925563) B5925563
theorem B3426299 : Blo 299831 3426299 := bstep (se 1 (by rfl) ⟨2569724, by rfl⟩ : syracuseStep 3426299 = 5139449) B5139449
theorem B1722491 : Blo 299831 1722491 := bstep (se 1 (by rfl) ⟨1291868, by rfl⟩ : syracuseStep 1722491 = 2583737) B2583737
theorem B510239 : Blo 299831 510239 := bstep (se 1 (by rfl) ⟨382679, by rfl⟩ : syracuseStep 510239 = 765359) B765359
theorem B1526525 : Blo 299831 1526525 := bstep (se 3 (by rfl) ⟨286223, by rfl⟩ : syracuseStep 1526525 = 572447) B572447
theorem B675611 : Blo 299831 675611 := bstep (se 1 (by rfl) ⟨506708, by rfl⟩ : syracuseStep 675611 = 1013417) B1013417
theorem B675809 : Blo 299831 675809 := bstep (se 2 (by rfl) ⟨253428, by rfl⟩ : syracuseStep 675809 = 506857) B506857
theorem B676511 : Blo 299831 676511 := bstep (se 1 (by rfl) ⟨507383, by rfl⟩ : syracuseStep 676511 = 1014767) B1014767
theorem B2184353 : Blo 299831 2184353 := bstep (se 2 (by rfl) ⟨819132, by rfl⟩ : syracuseStep 2184353 = 1638265) B1638265
theorem B1299623 : Blo 299831 1299623 := bstep (se 1 (by rfl) ⟨974717, by rfl⟩ : syracuseStep 1299623 = 1949435) B1949435
theorem B383231 : Blo 299831 383231 := bstep (se 1 (by rfl) ⟨287423, by rfl⟩ : syracuseStep 383231 = 574847) B574847
theorem B383707 : Blo 299831 383707 := bstep (se 1 (by rfl) ⟨287780, by rfl⟩ : syracuseStep 383707 = 575561) B575561
theorem B3432131 : Blo 299831 3432131 := bstep (se 1 (by rfl) ⟨2574098, by rfl⟩ : syracuseStep 3432131 = 5148197) B5148197
theorem B450719 : Blo 299831 450719 := bstep (se 1 (by rfl) ⟨338039, by rfl⟩ : syracuseStep 450719 = 676079) B676079
theorem B483977 : Blo 299831 483977 := bstep (se 2 (by rfl) ⟨181491, by rfl⟩ : syracuseStep 483977 = 362983) B362983
theorem B320447 : Blo 299831 320447 := bstep (se 1 (by rfl) ⟨240335, by rfl⟩ : syracuseStep 320447 = 480671) B480671
theorem B452327 : Blo 299831 452327 := bstep (se 1 (by rfl) ⟨339245, by rfl⟩ : syracuseStep 452327 = 678491) B678491
theorem B682361 : Blo 299831 682361 := bstep (se 2 (by rfl) ⟨255885, by rfl⟩ : syracuseStep 682361 = 511771) B511771
theorem B453407 : Blo 299831 453407 := bstep (se 1 (by rfl) ⟨340055, by rfl⟩ : syracuseStep 453407 = 680111) B680111
theorem B2288573 : Blo 299831 2288573 := bstep (se 3 (by rfl) ⟨429107, by rfl⟩ : syracuseStep 2288573 = 858215) B858215
theorem B682991 : Blo 299831 682991 := bstep (se 1 (by rfl) ⟨512243, by rfl⟩ : syracuseStep 682991 = 1024487) B1024487
theorem B453863 : Blo 299831 453863 := bstep (se 1 (by rfl) ⟨340397, by rfl⟩ : syracuseStep 453863 = 680795) B680795
theorem B1142009 : Blo 299831 1142009 := bstep (se 2 (by rfl) ⟨428253, by rfl⟩ : syracuseStep 1142009 = 856507) B856507
theorem B454313 : Blo 299831 454313 := bstep (se 2 (by rfl) ⟨170367, by rfl⟩ : syracuseStep 454313 = 340735) B340735
theorem B1142525 : Blo 299831 1142525 := bstep (se 3 (by rfl) ⟨214223, by rfl⟩ : syracuseStep 1142525 = 428447) B428447
theorem B454703 : Blo 299831 454703 := bstep (se 1 (by rfl) ⟨341027, by rfl⟩ : syracuseStep 454703 = 682055) B682055
theorem B6517259 : Blo 299831 6517259 := bstep (se 1 (by rfl) ⟨4887944, by rfl⟩ : syracuseStep 6517259 = 9775889) B9775889
theorem B41517143 : Blo 299831 41517143 := bstep (se 1 (by rfl) ⟨31137857, by rfl⟩ : syracuseStep 41517143 = 62275715) B62275715
theorem B16548893 : Blo 299831 16548893 := bstep (se 3 (by rfl) ⟨3102917, by rfl⟩ : syracuseStep 16548893 = 6205835) B6205835
theorem B1148327 : Blo 299831 1148327 := bstep (se 1 (by rfl) ⟨861245, by rfl⟩ : syracuseStep 1148327 = 1722491) B1722491
theorem B1017683 : Blo 299831 1017683 := bstep (se 1 (by rfl) ⟨763262, by rfl⟩ : syracuseStep 1017683 = 1526525) B1526525
theorem B2623427 : Blo 299831 2623427 := bstep (se 1 (by rfl) ⟨1967570, by rfl⟩ : syracuseStep 2623427 = 3935141) B3935141
theorem B3278951 : Blo 299831 3278951 := bstep (se 1 (by rfl) ⟨2459213, by rfl⟩ : syracuseStep 3278951 = 4918427) B4918427
theorem B854525 : Blo 299831 854525 := bstep (se 3 (by rfl) ⟨160223, by rfl⟩ : syracuseStep 854525 = 320447) B320447
theorem B1149497 : Blo 299831 1149497 := bstep (se 2 (by rfl) ⟨431061, by rfl⟩ : syracuseStep 1149497 = 862123) B862123
theorem B2296835 : Blo 299831 2296835 := bstep (se 1 (by rfl) ⟨1722626, by rfl⟩ : syracuseStep 2296835 = 3445253) B3445253
theorem B300479 : Blo 299831 300479 := bstep (se 1 (by rfl) ⟨225359, by rfl⟩ : syracuseStep 300479 = 450719) B450719
theorem B1021949 : Blo 299831 1021949 := bstep (se 3 (by rfl) ⟨191615, by rfl⟩ : syracuseStep 1021949 = 383231) B383231
theorem B301551 : Blo 299831 301551 := bstep (se 1 (by rfl) ⟨226163, by rfl⟩ : syracuseStep 301551 = 452327) B452327
theorem B1710827 : Blo 299831 1710827 := bstep (se 1 (by rfl) ⟨1283120, by rfl⟩ : syracuseStep 1710827 = 2566241) B2566241
theorem B302271 : Blo 299831 302271 := bstep (se 1 (by rfl) ⟨226703, by rfl⟩ : syracuseStep 302271 = 453407) B453407
theorem B302575 : Blo 299831 302575 := bstep (se 1 (by rfl) ⟨226931, by rfl⟩ : syracuseStep 302575 = 453863) B453863
theorem B761339 : Blo 299831 761339 := bstep (se 1 (by rfl) ⟨571004, by rfl⟩ : syracuseStep 761339 = 1142009) B1142009
theorem B302875 : Blo 299831 302875 := bstep (se 1 (by rfl) ⟨227156, by rfl⟩ : syracuseStep 302875 = 454313) B454313
theorem B761683 : Blo 299831 761683 := bstep (se 1 (by rfl) ⟨571262, by rfl⟩ : syracuseStep 761683 = 1142525) B1142525
theorem B303135 : Blo 299831 303135 := bstep (se 1 (by rfl) ⟨227351, by rfl⟩ : syracuseStep 303135 = 454703) B454703
theorem B337567 : Blo 299831 337567 := bstep (se 1 (by rfl) ⟨253175, by rfl⟩ : syracuseStep 337567 = 506351) B506351
theorem B1518587 : Blo 299831 1518587 := bstep (se 1 (by rfl) ⟨1138940, by rfl⟩ : syracuseStep 1518587 = 2277881) B2277881
theorem B339583 : Blo 299831 339583 := bstep (se 1 (by rfl) ⟨254687, by rfl⟩ : syracuseStep 339583 = 509375) B509375
theorem B864071 : Blo 299831 864071 := bstep (se 1 (by rfl) ⟨648053, by rfl⟩ : syracuseStep 864071 = 1296107) B1296107
theorem B340159 : Blo 299831 340159 := bstep (se 1 (by rfl) ⟨255119, by rfl⟩ : syracuseStep 340159 = 510239) B510239
theorem B1456235 : Blo 299831 1456235 := bstep (se 1 (by rfl) ⟨1092176, by rfl⟩ : syracuseStep 1456235 = 2184353) B2184353
theorem B1525715 : Blo 299831 1525715 := bstep (se 1 (by rfl) ⟨1144286, by rfl⟩ : syracuseStep 1525715 = 2288573) B2288573
theorem B4344839 : Blo 299831 4344839 := bstep (se 1 (by rfl) ⟨3258629, by rfl⟩ : syracuseStep 4344839 = 6517259) B6517259
theorem B675305 : Blo 299831 675305 := bstep (se 2 (by rfl) ⟨253239, by rfl⟩ : syracuseStep 675305 = 506479) B506479
theorem B511609 : Blo 299831 511609 := bstep (se 2 (by rfl) ⟨191853, by rfl⟩ : syracuseStep 511609 = 383707) B383707
theorem B642791 : Blo 299831 642791 := bstep (se 1 (by rfl) ⟨482093, by rfl⟩ : syracuseStep 642791 = 964187) B964187
theorem B675593 : Blo 299831 675593 := bstep (se 2 (by rfl) ⟨253347, by rfl⟩ : syracuseStep 675593 = 506695) B506695
theorem B512183 : Blo 299831 512183 := bstep (se 1 (by rfl) ⟨384137, by rfl⟩ : syracuseStep 512183 = 768275) B768275
theorem B381287 : Blo 299831 381287 := bstep (se 1 (by rfl) ⟨285965, by rfl⟩ : syracuseStep 381287 = 571931) B571931
theorem B381343 : Blo 299831 381343 := bstep (se 1 (by rfl) ⟨286007, by rfl⟩ : syracuseStep 381343 = 572015) B572015
theorem B8803313 : Blo 299831 8803313 := bstep (se 2 (by rfl) ⟨3301242, by rfl⟩ : syracuseStep 8803313 = 6602485) B6602485
theorem B677033 : Blo 299831 677033 := bstep (se 2 (by rfl) ⟨253887, by rfl⟩ : syracuseStep 677033 = 507775) B507775
theorem B5625283 : Blo 299831 5625283 := bstep (se 1 (by rfl) ⟨4218962, by rfl⟩ : syracuseStep 5625283 = 8437925) B8437925
theorem B7853851 : Blo 299831 7853851 := bstep (se 1 (by rfl) ⟨5890388, by rfl⟩ : syracuseStep 7853851 = 11780777) B11780777
theorem B1857451 : Blo 299831 1857451 := bstep (se 1 (by rfl) ⟨1393088, by rfl⟩ : syracuseStep 1857451 = 2786177) B2786177
theorem B13064591 : Blo 299831 13064591 := bstep (se 1 (by rfl) ⟨9798443, by rfl⟩ : syracuseStep 13064591 = 19596887) B19596887
theorem B2284199 : Blo 299831 2284199 := bstep (se 1 (by rfl) ⟨1713149, by rfl⟩ : syracuseStep 2284199 = 3426299) B3426299
theorem B613241 : Blo 299831 613241 := bstep (se 2 (by rfl) ⟨229965, by rfl⟩ : syracuseStep 613241 = 459931) B459931
theorem B3267533 : Blo 299831 3267533 := bstep (se 3 (by rfl) ⟨612662, by rfl⟩ : syracuseStep 3267533 = 1225325) B1225325
theorem B678905 : Blo 299831 678905 := bstep (se 2 (by rfl) ⟨254589, by rfl⟩ : syracuseStep 678905 = 509179) B509179
theorem B1531547 : Blo 299831 1531547 := bstep (se 1 (by rfl) ⟨1148660, by rfl⟩ : syracuseStep 1531547 = 2297321) B2297321
theorem B450407 : Blo 299831 450407 := bstep (se 1 (by rfl) ⟨337805, by rfl⟩ : syracuseStep 450407 = 675611) B675611
theorem B450539 : Blo 299831 450539 := bstep (se 1 (by rfl) ⟨337904, by rfl⟩ : syracuseStep 450539 = 675809) B675809
theorem B3465661 : Blo 299831 3465661 := bstep (se 3 (by rfl) ⟨649811, by rfl⟩ : syracuseStep 3465661 = 1299623) B1299623
theorem B451007 : Blo 299831 451007 := bstep (se 1 (by rfl) ⟨338255, by rfl⟩ : syracuseStep 451007 = 676511) B676511
theorem B26567129 : Blo 299831 26567129 := bstep (se 2 (by rfl) ⟨9962673, by rfl⟩ : syracuseStep 26567129 = 19925347) B19925347
theorem B483823 : Blo 299831 483823 := bstep (se 1 (by rfl) ⟨362867, by rfl⟩ : syracuseStep 483823 = 725735) B725735
theorem B1532519 : Blo 299831 1532519 := bstep (se 1 (by rfl) ⟨1149389, by rfl⟩ : syracuseStep 1532519 = 2298779) B2298779
theorem B681263 : Blo 299831 681263 := bstep (se 1 (by rfl) ⟨510947, by rfl⟩ : syracuseStep 681263 = 1021895) B1021895
theorem B2288087 : Blo 299831 2288087 := bstep (se 1 (by rfl) ⟨1716065, by rfl⟩ : syracuseStep 2288087 = 3432131) B3432131
theorem B682919 : Blo 299831 682919 := bstep (se 1 (by rfl) ⟨512189, by rfl⟩ : syracuseStep 682919 = 1024379) B1024379
theorem B322651 : Blo 299831 322651 := bstep (se 1 (by rfl) ⟨241988, by rfl⟩ : syracuseStep 322651 = 483977) B483977
theorem B453929 : Blo 299831 453929 := bstep (se 2 (by rfl) ⟨170223, by rfl⟩ : syracuseStep 453929 = 340447) B340447
theorem B454409 : Blo 299831 454409 := bstep (se 2 (by rfl) ⟨170403, by rfl⟩ : syracuseStep 454409 = 340807) B340807
theorem B454793 : Blo 299831 454793 := bstep (se 2 (by rfl) ⟨170547, by rfl⟩ : syracuseStep 454793 = 341095) B341095
theorem B454907 : Blo 299831 454907 := bstep (se 1 (by rfl) ⟨341180, by rfl⟩ : syracuseStep 454907 = 682361) B682361
theorem B455033 : Blo 299831 455033 := bstep (se 2 (by rfl) ⟨170637, by rfl⟩ : syracuseStep 455033 = 341275) B341275
theorem B455327 : Blo 299831 455327 := bstep (se 1 (by rfl) ⟨341495, by rfl⟩ : syracuseStep 455327 = 682991) B682991
theorem B1537055 : Blo 299831 1537055 := bstep (se 1 (by rfl) ⟨1152791, by rfl⟩ : syracuseStep 1537055 = 2305583) B2305583
theorem B25130087 : Blo 299831 25130087 := bstep (se 1 (by rfl) ⟨18847565, by rfl⟩ : syracuseStep 25130087 = 37695131) B37695131
theorem B5174441 : Blo 299831 5174441 := bstep (se 2 (by rfl) ⟨1940415, by rfl⟩ : syracuseStep 5174441 = 3880831) B3880831
theorem B42137333 : Blo 299831 42137333 := bstep (se 5 (by rfl) ⟨1975187, by rfl⟩ : syracuseStep 42137333 = 3950375) B3950375
theorem B1538027 : Blo 299831 1538027 := bstep (se 1 (by rfl) ⟨1153520, by rfl⟩ : syracuseStep 1538027 = 2307041) B2307041
theorem B1014875 : Blo 299831 1014875 := bstep (se 1 (by rfl) ⟨761156, by rfl⟩ : syracuseStep 1014875 = 1522313) B1522313
theorem B4620881 : Blo 299831 4620881 := bstep (se 2 (by rfl) ⟨1732830, by rfl⟩ : syracuseStep 4620881 = 3465661) B3465661
theorem B1016765 : Blo 299831 1016765 := bstep (se 3 (by rfl) ⟨190643, by rfl⟩ : syracuseStep 1016765 = 381287) B381287
theorem B1017143 : Blo 299831 1017143 := bstep (se 1 (by rfl) ⟨762857, by rfl⟩ : syracuseStep 1017143 = 1525715) B1525715
theorem B428527 : Blo 299831 428527 := bstep (se 1 (by rfl) ⟨321395, by rfl⟩ : syracuseStep 428527 = 642791) B642791
theorem B5868875 : Blo 299831 5868875 := bstep (se 1 (by rfl) ⟨4401656, by rfl⟩ : syracuseStep 5868875 = 8803313) B8803313
theorem B430201 : Blo 299831 430201 := bstep (se 2 (by rfl) ⟨161325, by rfl⟩ : syracuseStep 430201 = 322651) B322651
theorem B1021031 : Blo 299831 1021031 := bstep (se 1 (by rfl) ⟨765773, by rfl⟩ : syracuseStep 1021031 = 1531547) B1531547
theorem B300271 : Blo 299831 300271 := bstep (se 1 (by rfl) ⟨225203, by rfl⟩ : syracuseStep 300271 = 450407) B450407
theorem B300359 : Blo 299831 300359 := bstep (se 1 (by rfl) ⟨225269, by rfl⟩ : syracuseStep 300359 = 450539) B450539
theorem B300671 : Blo 299831 300671 := bstep (se 1 (by rfl) ⟨225503, by rfl⟩ : syracuseStep 300671 = 451007) B451007
theorem B1021679 : Blo 299831 1021679 := bstep (se 1 (by rfl) ⟨766259, by rfl⟩ : syracuseStep 1021679 = 1532519) B1532519
theorem B302619 : Blo 299831 302619 := bstep (se 1 (by rfl) ⟨226964, by rfl⟩ : syracuseStep 302619 = 453929) B453929
theorem B302939 : Blo 299831 302939 := bstep (se 1 (by rfl) ⟨227204, by rfl⟩ : syracuseStep 302939 = 454409) B454409
theorem B303195 : Blo 299831 303195 := bstep (se 1 (by rfl) ⟨227396, by rfl⟩ : syracuseStep 303195 = 454793) B454793
theorem B303271 : Blo 299831 303271 := bstep (se 1 (by rfl) ⟨227453, by rfl⟩ : syracuseStep 303271 = 454907) B454907
theorem B303355 : Blo 299831 303355 := bstep (se 1 (by rfl) ⟨227516, by rfl⟩ : syracuseStep 303355 = 455033) B455033
theorem B303551 : Blo 299831 303551 := bstep (se 1 (by rfl) ⟨227663, by rfl⟩ : syracuseStep 303551 = 455327) B455327
theorem B1024703 : Blo 299831 1024703 := bstep (se 1 (by rfl) ⟨768527, by rfl⟩ : syracuseStep 1024703 = 1537055) B1537055
theorem B16753391 : Blo 299831 16753391 := bstep (se 1 (by rfl) ⟨12565043, by rfl⟩ : syracuseStep 16753391 = 25130087) B25130087
theorem B3449627 : Blo 299831 3449627 := bstep (se 1 (by rfl) ⟨2587220, by rfl⟩ : syracuseStep 3449627 = 5174441) B5174441
theorem B28091555 : Blo 299831 28091555 := bstep (se 1 (by rfl) ⟨21068666, by rfl⟩ : syracuseStep 28091555 = 42137333) B42137333
theorem B1025351 : Blo 299831 1025351 := bstep (se 1 (by rfl) ⟨769013, by rfl⟩ : syracuseStep 1025351 = 1538027) B1538027
theorem B765551 : Blo 299831 765551 := bstep (se 1 (by rfl) ⟨574163, by rfl⟩ : syracuseStep 765551 = 1148327) B1148327
theorem B1748951 : Blo 299831 1748951 := bstep (se 1 (by rfl) ⟨1311713, by rfl⟩ : syracuseStep 1748951 = 2623427) B2623427
theorem B569683 : Blo 299831 569683 := bstep (se 1 (by rfl) ⟨427262, by rfl⟩ : syracuseStep 569683 = 854525) B854525
theorem B766331 : Blo 299831 766331 := bstep (se 1 (by rfl) ⟨574748, by rfl⟩ : syracuseStep 766331 = 1149497) B1149497
theorem B2896559 : Blo 299831 2896559 := bstep (se 1 (by rfl) ⟨2172419, by rfl⟩ : syracuseStep 2896559 = 4344839) B4344839
theorem B341455 : Blo 299831 341455 := bstep (se 1 (by rfl) ⟨256091, by rfl⟩ : syracuseStep 341455 = 512183) B512183
theorem B1522799 : Blo 299831 1522799 := bstep (se 1 (by rfl) ⟨1142099, by rfl⟩ : syracuseStep 1522799 = 2284199) B2284199
theorem B408827 : Blo 299831 408827 := bstep (se 1 (by rfl) ⟨306620, by rfl⟩ : syracuseStep 408827 = 613241) B613241
theorem B2178355 : Blo 299831 2178355 := bstep (se 1 (by rfl) ⟨1633766, by rfl⟩ : syracuseStep 2178355 = 3267533) B3267533
theorem B507559 : Blo 299831 507559 := bstep (se 1 (by rfl) ⟨380669, by rfl⟩ : syracuseStep 507559 = 761339) B761339
theorem B17711419 : Blo 299831 17711419 := bstep (se 1 (by rfl) ⟨13283564, by rfl⟩ : syracuseStep 17711419 = 26567129) B26567129
theorem B508457 : Blo 299831 508457 := bstep (se 2 (by rfl) ⟨190671, by rfl⟩ : syracuseStep 508457 = 381343) B381343
theorem B1525391 : Blo 299831 1525391 := bstep (se 1 (by rfl) ⟨1144043, by rfl⟩ : syracuseStep 1525391 = 2288087) B2288087
theorem B10471801 : Blo 299831 10471801 := bstep (se 2 (by rfl) ⟨3926925, by rfl⟩ : syracuseStep 10471801 = 7853851) B7853851
theorem B576047 : Blo 299831 576047 := bstep (se 1 (by rfl) ⟨432035, by rfl⟩ : syracuseStep 576047 = 864071) B864071
theorem B2476601 : Blo 299831 2476601 := bstep (se 2 (by rfl) ⟨928725, by rfl⟩ : syracuseStep 2476601 = 1857451) B1857451
theorem B970823 : Blo 299831 970823 := bstep (se 1 (by rfl) ⟨728117, by rfl⟩ : syracuseStep 970823 = 1456235) B1456235
theorem B676583 : Blo 299831 676583 := bstep (se 1 (by rfl) ⟨507437, by rfl⟩ : syracuseStep 676583 = 1014875) B1014875
theorem B27678095 : Blo 299831 27678095 := bstep (se 1 (by rfl) ⟨20758571, by rfl⟩ : syracuseStep 27678095 = 41517143) B41517143
theorem B645097 : Blo 299831 645097 := bstep (se 2 (by rfl) ⟨241911, by rfl⟩ : syracuseStep 645097 = 483823) B483823
theorem B11032595 : Blo 299831 11032595 := bstep (se 1 (by rfl) ⟨8274446, by rfl⟩ : syracuseStep 11032595 = 16548893) B16548893
theorem B678455 : Blo 299831 678455 := bstep (se 1 (by rfl) ⟨508841, by rfl⟩ : syracuseStep 678455 = 1017683) B1017683
theorem B2185967 : Blo 299831 2185967 := bstep (se 1 (by rfl) ⟨1639475, by rfl⟩ : syracuseStep 2185967 = 3278951) B3278951
theorem B1531223 : Blo 299831 1531223 := bstep (se 1 (by rfl) ⟨1148417, by rfl⟩ : syracuseStep 1531223 = 2296835) B2296835
theorem B450089 : Blo 299831 450089 := bstep (se 2 (by rfl) ⟨168783, by rfl⟩ : syracuseStep 450089 = 337567) B337567
theorem B450203 : Blo 299831 450203 := bstep (se 1 (by rfl) ⟨337652, by rfl⟩ : syracuseStep 450203 = 675305) B675305
theorem B450395 : Blo 299831 450395 := bstep (se 1 (by rfl) ⟨337796, by rfl⟩ : syracuseStep 450395 = 675593) B675593
theorem B451355 : Blo 299831 451355 := bstep (se 1 (by rfl) ⟨338516, by rfl⟩ : syracuseStep 451355 = 677033) B677033
theorem B681299 : Blo 299831 681299 := bstep (se 1 (by rfl) ⟨510974, by rfl⟩ : syracuseStep 681299 = 1021949) B1021949
theorem B8709727 : Blo 299831 8709727 := bstep (se 1 (by rfl) ⟨6532295, by rfl⟩ : syracuseStep 8709727 = 13064591) B13064591
theorem B1140551 : Blo 299831 1140551 := bstep (se 1 (by rfl) ⟨855413, by rfl⟩ : syracuseStep 1140551 = 1710827) B1710827
theorem B452603 : Blo 299831 452603 := bstep (se 1 (by rfl) ⟨339452, by rfl⟩ : syracuseStep 452603 = 678905) B678905
theorem B682145 : Blo 299831 682145 := bstep (se 2 (by rfl) ⟨255804, by rfl⟩ : syracuseStep 682145 = 511609) B511609
theorem B452777 : Blo 299831 452777 := bstep (se 2 (by rfl) ⟨169791, by rfl⟩ : syracuseStep 452777 = 339583) B339583
theorem B453545 : Blo 299831 453545 := bstep (se 2 (by rfl) ⟨170079, by rfl⟩ : syracuseStep 453545 = 340159) B340159
theorem B454175 : Blo 299831 454175 := bstep (se 1 (by rfl) ⟨340631, by rfl⟩ : syracuseStep 454175 = 681263) B681263
theorem B7500377 : Blo 299831 7500377 := bstep (se 2 (by rfl) ⟨2812641, by rfl⟩ : syracuseStep 7500377 = 5625283) B5625283
theorem B455279 : Blo 299831 455279 := bstep (se 1 (by rfl) ⟨341459, by rfl⟩ : syracuseStep 455279 = 682919) B682919
theorem B1012391 : Blo 299831 1012391 := bstep (se 1 (by rfl) ⟨759293, by rfl⟩ : syracuseStep 1012391 = 1518587) B1518587
theorem B1015577 : Blo 299831 1015577 := bstep (se 2 (by rfl) ⟨380841, by rfl⟩ : syracuseStep 1015577 = 761683) B761683
theorem B2588861 : Blo 299831 2588861 := bstep (se 3 (by rfl) ⟨485411, by rfl⟩ : syracuseStep 2588861 = 970823) B970823
theorem B3080587 : Blo 299831 3080587 := bstep (se 1 (by rfl) ⟨2310440, by rfl⟩ : syracuseStep 3080587 = 4620881) B4620881
theorem B2294405 : Blo 299831 2294405 := bstep (se 4 (by rfl) ⟨215100, by rfl⟩ : syracuseStep 2294405 = 430201) B430201
theorem B1016927 : Blo 299831 1016927 := bstep (se 1 (by rfl) ⟨762695, by rfl⟩ : syracuseStep 1016927 = 1525391) B1525391
theorem B13962401 : Blo 299831 13962401 := bstep (se 2 (by rfl) ⟨5235900, by rfl⟩ : syracuseStep 13962401 = 10471801) B10471801
theorem B18452063 : Blo 299831 18452063 := bstep (se 1 (by rfl) ⟨13839047, by rfl⟩ : syracuseStep 18452063 = 27678095) B27678095
theorem B1020815 : Blo 299831 1020815 := bstep (se 1 (by rfl) ⟨765611, by rfl⟩ : syracuseStep 1020815 = 1531223) B1531223
theorem B300059 : Blo 299831 300059 := bstep (se 1 (by rfl) ⟨225044, by rfl⟩ : syracuseStep 300059 = 450089) B450089
theorem B300135 : Blo 299831 300135 := bstep (se 1 (by rfl) ⟨225101, by rfl⟩ : syracuseStep 300135 = 450203) B450203
theorem B300263 : Blo 299831 300263 := bstep (se 1 (by rfl) ⟨225197, by rfl⟩ : syracuseStep 300263 = 450395) B450395
theorem B759577 : Blo 299831 759577 := bstep (se 2 (by rfl) ⟨284841, by rfl⟩ : syracuseStep 759577 = 569683) B569683
theorem B300903 : Blo 299831 300903 := bstep (se 1 (by rfl) ⟨225677, by rfl⟩ : syracuseStep 300903 = 451355) B451355
theorem B2299751 : Blo 299831 2299751 := bstep (se 1 (by rfl) ⟨1724813, by rfl⟩ : syracuseStep 2299751 = 3449627) B3449627
theorem B760367 : Blo 299831 760367 := bstep (se 1 (by rfl) ⟨570275, by rfl⟩ : syracuseStep 760367 = 1140551) B1140551
theorem B301735 : Blo 299831 301735 := bstep (se 1 (by rfl) ⟨226301, by rfl⟩ : syracuseStep 301735 = 452603) B452603
theorem B301851 : Blo 299831 301851 := bstep (se 1 (by rfl) ⟨226388, by rfl⟩ : syracuseStep 301851 = 452777) B452777
theorem B302363 : Blo 299831 302363 := bstep (se 1 (by rfl) ⟨226772, by rfl⟩ : syracuseStep 302363 = 453545) B453545
theorem B302783 : Blo 299831 302783 := bstep (se 1 (by rfl) ⟨227087, by rfl⟩ : syracuseStep 302783 = 454175) B454175
theorem B860129 : Blo 299831 860129 := bstep (se 2 (by rfl) ⟨322548, by rfl⟩ : syracuseStep 860129 = 645097) B645097
theorem B303519 : Blo 299831 303519 := bstep (se 1 (by rfl) ⟨227639, by rfl⟩ : syracuseStep 303519 = 455279) B455279
theorem B1090205 : Blo 299831 1090205 := bstep (se 3 (by rfl) ⟨204413, by rfl⟩ : syracuseStep 1090205 = 408827) B408827
theorem B338971 : Blo 299831 338971 := bstep (se 1 (by rfl) ⟨254228, by rfl⟩ : syracuseStep 338971 = 508457) B508457
theorem B20001005 : Blo 299831 20001005 := bstep (se 3 (by rfl) ⟨3750188, by rfl⟩ : syracuseStep 20001005 = 7500377) B7500377
theorem B1651067 : Blo 299831 1651067 := bstep (se 1 (by rfl) ⟨1238300, by rfl⟩ : syracuseStep 1651067 = 2476601) B2476601
theorem B11612969 : Blo 299831 11612969 := bstep (se 2 (by rfl) ⟨4354863, by rfl⟩ : syracuseStep 11612969 = 8709727) B8709727
theorem B571369 : Blo 299831 571369 := bstep (se 2 (by rfl) ⟨214263, by rfl⟩ : syracuseStep 571369 = 428527) B428527
theorem B7355063 : Blo 299831 7355063 := bstep (se 1 (by rfl) ⟨5516297, by rfl⟩ : syracuseStep 7355063 = 11032595) B11032595
theorem B18727703 : Blo 299831 18727703 := bstep (se 1 (by rfl) ⟨14045777, by rfl⟩ : syracuseStep 18727703 = 28091555) B28091555
theorem B510367 : Blo 299831 510367 := bstep (se 1 (by rfl) ⟨382775, by rfl⟩ : syracuseStep 510367 = 765551) B765551
theorem B1165967 : Blo 299831 1165967 := bstep (se 1 (by rfl) ⟨874475, by rfl⟩ : syracuseStep 1165967 = 1748951) B1748951
theorem B510887 : Blo 299831 510887 := bstep (se 1 (by rfl) ⟨383165, by rfl⟩ : syracuseStep 510887 = 766331) B766331
theorem B674927 : Blo 299831 674927 := bstep (se 1 (by rfl) ⟨506195, by rfl⟩ : syracuseStep 674927 = 1012391) B1012391
theorem B15650333 : Blo 299831 15650333 := bstep (se 3 (by rfl) ⟨2934437, by rfl⟩ : syracuseStep 15650333 = 5868875) B5868875
theorem B2904473 : Blo 299831 2904473 := bstep (se 2 (by rfl) ⟨1089177, by rfl⟩ : syracuseStep 2904473 = 2178355) B2178355
theorem B676745 : Blo 299831 676745 := bstep (se 2 (by rfl) ⟨253779, by rfl⟩ : syracuseStep 676745 = 507559) B507559
theorem B677051 : Blo 299831 677051 := bstep (se 1 (by rfl) ⟨507788, by rfl⟩ : syracuseStep 677051 = 1015577) B1015577
theorem B23615225 : Blo 299831 23615225 := bstep (se 2 (by rfl) ⟨8855709, by rfl⟩ : syracuseStep 23615225 = 17711419) B17711419
theorem B677843 : Blo 299831 677843 := bstep (se 1 (by rfl) ⟨508382, by rfl⟩ : syracuseStep 677843 = 1016765) B1016765
theorem B678095 : Blo 299831 678095 := bstep (se 1 (by rfl) ⟨508571, by rfl⟩ : syracuseStep 678095 = 1017143) B1017143
theorem B384031 : Blo 299831 384031 := bstep (se 1 (by rfl) ⟨288023, by rfl⟩ : syracuseStep 384031 = 576047) B576047
theorem B451055 : Blo 299831 451055 := bstep (se 1 (by rfl) ⟨338291, by rfl⟩ : syracuseStep 451055 = 676583) B676583
theorem B680687 : Blo 299831 680687 := bstep (se 1 (by rfl) ⟨510515, by rfl⟩ : syracuseStep 680687 = 1021031) B1021031
theorem B681119 : Blo 299831 681119 := bstep (se 1 (by rfl) ⟨510839, by rfl⟩ : syracuseStep 681119 = 1021679) B1021679
theorem B452303 : Blo 299831 452303 := bstep (se 1 (by rfl) ⟨339227, by rfl⟩ : syracuseStep 452303 = 678455) B678455
theorem B683135 : Blo 299831 683135 := bstep (se 1 (by rfl) ⟨512351, by rfl⟩ : syracuseStep 683135 = 1024703) B1024703
theorem B11168927 : Blo 299831 11168927 := bstep (se 1 (by rfl) ⟨8376695, by rfl⟩ : syracuseStep 11168927 = 16753391) B16753391
theorem B683567 : Blo 299831 683567 := bstep (se 1 (by rfl) ⟨512675, by rfl⟩ : syracuseStep 683567 = 1025351) B1025351
theorem B454199 : Blo 299831 454199 := bstep (se 1 (by rfl) ⟨340649, by rfl⟩ : syracuseStep 454199 = 681299) B681299
theorem B454763 : Blo 299831 454763 := bstep (se 1 (by rfl) ⟨341072, by rfl⟩ : syracuseStep 454763 = 682145) B682145
theorem B455273 : Blo 299831 455273 := bstep (se 2 (by rfl) ⟨170727, by rfl⟩ : syracuseStep 455273 = 341455) B341455
theorem B5829245 : Blo 299831 5829245 := bstep (se 3 (by rfl) ⟨1092983, by rfl⟩ : syracuseStep 5829245 = 2185967) B2185967
theorem B1931039 : Blo 299831 1931039 := bstep (se 1 (by rfl) ⟨1448279, by rfl⟩ : syracuseStep 1931039 = 2896559) B2896559
theorem B1015199 : Blo 299831 1015199 := bstep (se 1 (by rfl) ⟨761399, by rfl⟩ : syracuseStep 1015199 = 1522799) B1522799
theorem B12485135 : Blo 299831 12485135 := bstep (se 1 (by rfl) ⟨9363851, by rfl⟩ : syracuseStep 12485135 = 18727703) B18727703
theorem B9308267 : Blo 299831 9308267 := bstep (se 1 (by rfl) ⟨6981200, by rfl⟩ : syracuseStep 9308267 = 13962401) B13962401
theorem B1936315 : Blo 299831 1936315 := bstep (se 1 (by rfl) ⟨1452236, by rfl⟩ : syracuseStep 1936315 = 2904473) B2904473
theorem B300703 : Blo 299831 300703 := bstep (se 1 (by rfl) ⟨225527, by rfl⟩ : syracuseStep 300703 = 451055) B451055
theorem B726803 : Blo 299831 726803 := bstep (se 1 (by rfl) ⟨545102, by rfl⟩ : syracuseStep 726803 = 1090205) B1090205
theorem B301535 : Blo 299831 301535 := bstep (se 1 (by rfl) ⟨226151, by rfl⟩ : syracuseStep 301535 = 452303) B452303
theorem B7445951 : Blo 299831 7445951 := bstep (se 1 (by rfl) ⟨5584463, by rfl⟩ : syracuseStep 7445951 = 11168927) B11168927
theorem B302799 : Blo 299831 302799 := bstep (se 1 (by rfl) ⟨227099, by rfl⟩ : syracuseStep 302799 = 454199) B454199
theorem B761825 : Blo 299831 761825 := bstep (se 2 (by rfl) ⟨285684, by rfl⟩ : syracuseStep 761825 = 571369) B571369
theorem B303175 : Blo 299831 303175 := bstep (se 1 (by rfl) ⟨227381, by rfl⟩ : syracuseStep 303175 = 454763) B454763
theorem B303515 : Blo 299831 303515 := bstep (se 1 (by rfl) ⟨227636, by rfl⟩ : syracuseStep 303515 = 455273) B455273
theorem B7741979 : Blo 299831 7741979 := bstep (se 1 (by rfl) ⟨5806484, by rfl⟩ : syracuseStep 7741979 = 11612969) B11612969
theorem B1287359 : Blo 299831 1287359 := bstep (se 1 (by rfl) ⟨965519, by rfl⟩ : syracuseStep 1287359 = 1931039) B1931039
theorem B4107449 : Blo 299831 4107449 := bstep (se 2 (by rfl) ⟨1540293, by rfl⟩ : syracuseStep 4107449 = 3080587) B3080587
theorem B340591 : Blo 299831 340591 := bstep (se 1 (by rfl) ⟨255443, by rfl⟩ : syracuseStep 340591 = 510887) B510887
theorem B10433555 : Blo 299831 10433555 := bstep (se 1 (by rfl) ⟨7825166, by rfl⟩ : syracuseStep 10433555 = 15650333) B15650333
theorem B12301375 : Blo 299831 12301375 := bstep (se 1 (by rfl) ⟨9226031, by rfl⟩ : syracuseStep 12301375 = 18452063) B18452063
theorem B15743483 : Blo 299831 15743483 := bstep (se 1 (by rfl) ⟨11807612, by rfl⟩ : syracuseStep 15743483 = 23615225) B23615225
theorem B506911 : Blo 299831 506911 := bstep (se 1 (by rfl) ⟨380183, by rfl⟩ : syracuseStep 506911 = 760367) B760367
theorem B573419 : Blo 299831 573419 := bstep (se 1 (by rfl) ⟨430064, by rfl⟩ : syracuseStep 573419 = 860129) B860129
theorem B1100711 : Blo 299831 1100711 := bstep (se 1 (by rfl) ⟨825533, by rfl⟩ : syracuseStep 1100711 = 1651067) B1651067
theorem B3886163 : Blo 299831 3886163 := bstep (se 1 (by rfl) ⟨2914622, by rfl⟩ : syracuseStep 3886163 = 5829245) B5829245
theorem B512041 : Blo 299831 512041 := bstep (se 2 (by rfl) ⟨192015, by rfl⟩ : syracuseStep 512041 = 384031) B384031
theorem B4903375 : Blo 299831 4903375 := bstep (se 1 (by rfl) ⟨3677531, by rfl⟩ : syracuseStep 4903375 = 7355063) B7355063
theorem B676799 : Blo 299831 676799 := bstep (se 1 (by rfl) ⟨507599, by rfl⟩ : syracuseStep 676799 = 1015199) B1015199
theorem B1725907 : Blo 299831 1725907 := bstep (se 1 (by rfl) ⟨1294430, by rfl⟩ : syracuseStep 1725907 = 2588861) B2588861
theorem B1529603 : Blo 299831 1529603 := bstep (se 1 (by rfl) ⟨1147202, by rfl⟩ : syracuseStep 1529603 = 2294405) B2294405
theorem B677951 : Blo 299831 677951 := bstep (se 1 (by rfl) ⟨508463, by rfl⟩ : syracuseStep 677951 = 1016927) B1016927
theorem B777311 : Blo 299831 777311 := bstep (se 1 (by rfl) ⟨582983, by rfl⟩ : syracuseStep 777311 = 1165967) B1165967
theorem B449951 : Blo 299831 449951 := bstep (se 1 (by rfl) ⟨337463, by rfl⟩ : syracuseStep 449951 = 674927) B674927
theorem B680489 : Blo 299831 680489 := bstep (se 2 (by rfl) ⟨255183, by rfl⟩ : syracuseStep 680489 = 510367) B510367
theorem B451163 : Blo 299831 451163 := bstep (se 1 (by rfl) ⟨338372, by rfl⟩ : syracuseStep 451163 = 676745) B676745
theorem B680543 : Blo 299831 680543 := bstep (se 1 (by rfl) ⟨510407, by rfl⟩ : syracuseStep 680543 = 1020815) B1020815
theorem B451367 : Blo 299831 451367 := bstep (se 1 (by rfl) ⟨338525, by rfl⟩ : syracuseStep 451367 = 677051) B677051
theorem B1533167 : Blo 299831 1533167 := bstep (se 1 (by rfl) ⟨1149875, by rfl⟩ : syracuseStep 1533167 = 2299751) B2299751
theorem B451895 : Blo 299831 451895 := bstep (se 1 (by rfl) ⟨338921, by rfl⟩ : syracuseStep 451895 = 677843) B677843
theorem B451961 : Blo 299831 451961 := bstep (se 2 (by rfl) ⟨169485, by rfl⟩ : syracuseStep 451961 = 338971) B338971
theorem B452063 : Blo 299831 452063 := bstep (se 1 (by rfl) ⟨339047, by rfl⟩ : syracuseStep 452063 = 678095) B678095
theorem B453791 : Blo 299831 453791 := bstep (se 1 (by rfl) ⟨340343, by rfl⟩ : syracuseStep 453791 = 680687) B680687
theorem B454079 : Blo 299831 454079 := bstep (se 1 (by rfl) ⟨340559, by rfl⟩ : syracuseStep 454079 = 681119) B681119
theorem B455423 : Blo 299831 455423 := bstep (se 1 (by rfl) ⟨341567, by rfl⟩ : syracuseStep 455423 = 683135) B683135
theorem B455711 : Blo 299831 455711 := bstep (se 1 (by rfl) ⟨341783, by rfl⟩ : syracuseStep 455711 = 683567) B683567
theorem B1012769 : Blo 299831 1012769 := bstep (se 2 (by rfl) ⟨379788, by rfl⟩ : syracuseStep 1012769 = 759577) B759577
theorem B13334003 : Blo 299831 13334003 := bstep (se 1 (by rfl) ⟨10000502, by rfl⟩ : syracuseStep 13334003 = 20001005) B20001005
theorem B33293693 : Blo 299831 33293693 := bstep (se 3 (by rfl) ⟨6242567, by rfl⟩ : syracuseStep 33293693 = 12485135) B12485135
theorem B2590775 : Blo 299831 2590775 := bstep (se 1 (by rfl) ⟨1943081, by rfl⟩ : syracuseStep 2590775 = 3886163) B3886163
theorem B1019735 : Blo 299831 1019735 := bstep (se 1 (by rfl) ⟨764801, by rfl⟩ : syracuseStep 1019735 = 1529603) B1529603
theorem B299967 : Blo 299831 299967 := bstep (se 1 (by rfl) ⟨224975, by rfl⟩ : syracuseStep 299967 = 449951) B449951
theorem B300775 : Blo 299831 300775 := bstep (se 1 (by rfl) ⟨225581, by rfl⟩ : syracuseStep 300775 = 451163) B451163
theorem B300911 : Blo 299831 300911 := bstep (se 1 (by rfl) ⟨225683, by rfl⟩ : syracuseStep 300911 = 451367) B451367
theorem B858239 : Blo 299831 858239 := bstep (se 1 (by rfl) ⟨643679, by rfl⟩ : syracuseStep 858239 = 1287359) B1287359
theorem B1022111 : Blo 299831 1022111 := bstep (se 1 (by rfl) ⟨766583, by rfl⟩ : syracuseStep 1022111 = 1533167) B1533167
theorem B301263 : Blo 299831 301263 := bstep (se 1 (by rfl) ⟨225947, by rfl⟩ : syracuseStep 301263 = 451895) B451895
theorem B301307 : Blo 299831 301307 := bstep (se 1 (by rfl) ⟨225980, by rfl⟩ : syracuseStep 301307 = 451961) B451961
theorem B301375 : Blo 299831 301375 := bstep (se 1 (by rfl) ⟨226031, by rfl⟩ : syracuseStep 301375 = 452063) B452063
theorem B2301209 : Blo 299831 2301209 := bstep (se 2 (by rfl) ⟨862953, by rfl⟩ : syracuseStep 2301209 = 1725907) B1725907
theorem B302527 : Blo 299831 302527 := bstep (se 1 (by rfl) ⟨226895, by rfl⟩ : syracuseStep 302527 = 453791) B453791
theorem B302719 : Blo 299831 302719 := bstep (se 1 (by rfl) ⟨227039, by rfl⟩ : syracuseStep 302719 = 454079) B454079
theorem B303615 : Blo 299831 303615 := bstep (se 1 (by rfl) ⟨227711, by rfl⟩ : syracuseStep 303615 = 455423) B455423
theorem B6955703 : Blo 299831 6955703 := bstep (se 1 (by rfl) ⟨5216777, by rfl⟩ : syracuseStep 6955703 = 10433555) B10433555
theorem B303807 : Blo 299831 303807 := bstep (se 1 (by rfl) ⟨227855, by rfl⟩ : syracuseStep 303807 = 455711) B455711
theorem B8889335 : Blo 299831 8889335 := bstep (se 1 (by rfl) ⟨6667001, by rfl⟩ : syracuseStep 8889335 = 13334003) B13334003
theorem B10495655 : Blo 299831 10495655 := bstep (se 1 (by rfl) ⟨7871741, by rfl⟩ : syracuseStep 10495655 = 15743483) B15743483
theorem B6205511 : Blo 299831 6205511 := bstep (se 1 (by rfl) ⟨4654133, by rfl⟩ : syracuseStep 6205511 = 9308267) B9308267
theorem B733807 : Blo 299831 733807 := bstep (se 1 (by rfl) ⟨550355, by rfl⟩ : syracuseStep 733807 = 1100711) B1100711
theorem B4963967 : Blo 299831 4963967 := bstep (se 1 (by rfl) ⟨3722975, by rfl⟩ : syracuseStep 4963967 = 7445951) B7445951
theorem B507883 : Blo 299831 507883 := bstep (se 1 (by rfl) ⟨380912, by rfl⟩ : syracuseStep 507883 = 761825) B761825
theorem B5161319 : Blo 299831 5161319 := bstep (se 1 (by rfl) ⟨3870989, by rfl⟩ : syracuseStep 5161319 = 7741979) B7741979
theorem B6537833 : Blo 299831 6537833 := bstep (se 2 (by rfl) ⟨2451687, by rfl⟩ : syracuseStep 6537833 = 4903375) B4903375
theorem B16401833 : Blo 299831 16401833 := bstep (se 2 (by rfl) ⟨6150687, by rfl⟩ : syracuseStep 16401833 = 12301375) B12301375
theorem B2738299 : Blo 299831 2738299 := bstep (se 1 (by rfl) ⟨2053724, by rfl⟩ : syracuseStep 2738299 = 4107449) B4107449
theorem B675179 : Blo 299831 675179 := bstep (se 1 (by rfl) ⟨506384, by rfl⟩ : syracuseStep 675179 = 1012769) B1012769
theorem B675881 : Blo 299831 675881 := bstep (se 2 (by rfl) ⟨253455, by rfl⟩ : syracuseStep 675881 = 506911) B506911
theorem B1529117 : Blo 299831 1529117 := bstep (se 3 (by rfl) ⟨286709, by rfl⟩ : syracuseStep 1529117 = 573419) B573419
theorem B451199 : Blo 299831 451199 := bstep (se 1 (by rfl) ⟨338399, by rfl⟩ : syracuseStep 451199 = 676799) B676799
theorem B484535 : Blo 299831 484535 := bstep (se 1 (by rfl) ⟨363401, by rfl⟩ : syracuseStep 484535 = 726803) B726803
theorem B2581753 : Blo 299831 2581753 := bstep (se 2 (by rfl) ⟨968157, by rfl⟩ : syracuseStep 2581753 = 1936315) B1936315
theorem B451967 : Blo 299831 451967 := bstep (se 1 (by rfl) ⟨338975, by rfl⟩ : syracuseStep 451967 = 677951) B677951
theorem B518207 : Blo 299831 518207 := bstep (se 1 (by rfl) ⟨388655, by rfl⟩ : syracuseStep 518207 = 777311) B777311
theorem B682721 : Blo 299831 682721 := bstep (se 2 (by rfl) ⟨256020, by rfl⟩ : syracuseStep 682721 = 512041) B512041
theorem B453659 : Blo 299831 453659 := bstep (se 1 (by rfl) ⟨340244, by rfl⟩ : syracuseStep 453659 = 680489) B680489
theorem B453695 : Blo 299831 453695 := bstep (se 1 (by rfl) ⟨340271, by rfl⟩ : syracuseStep 453695 = 680543) B680543
theorem B454121 : Blo 299831 454121 := bstep (se 2 (by rfl) ⟨170295, by rfl⟩ : syracuseStep 454121 = 340591) B340591
theorem B3440879 : Blo 299831 3440879 := bstep (se 1 (by rfl) ⟨2580659, by rfl⟩ : syracuseStep 3440879 = 5161319) B5161319
theorem B4358555 : Blo 299831 4358555 := bstep (se 1 (by rfl) ⟨3268916, by rfl⟩ : syracuseStep 4358555 = 6537833) B6537833
theorem B3442337 : Blo 299831 3442337 := bstep (se 2 (by rfl) ⟨1290876, by rfl⟩ : syracuseStep 3442337 = 2581753) B2581753
theorem B1019411 : Blo 299831 1019411 := bstep (se 1 (by rfl) ⟨764558, by rfl⟩ : syracuseStep 1019411 = 1529117) B1529117
theorem B174952885 : Blo 299831 174952885 := bstep (se 5 (by rfl) ⟨8200916, by rfl⟩ : syracuseStep 174952885 = 16401833) B16401833
theorem B300799 : Blo 299831 300799 := bstep (se 1 (by rfl) ⟨225599, by rfl⟩ : syracuseStep 300799 = 451199) B451199
theorem B301311 : Blo 299831 301311 := bstep (se 1 (by rfl) ⟨225983, by rfl⟩ : syracuseStep 301311 = 451967) B451967
theorem B302439 : Blo 299831 302439 := bstep (se 1 (by rfl) ⟨226829, by rfl⟩ : syracuseStep 302439 = 453659) B453659
theorem B302463 : Blo 299831 302463 := bstep (se 1 (by rfl) ⟨226847, by rfl⟩ : syracuseStep 302463 = 453695) B453695
theorem B302747 : Blo 299831 302747 := bstep (se 1 (by rfl) ⟨227060, by rfl⟩ : syracuseStep 302747 = 454121) B454121
theorem B4137007 : Blo 299831 4137007 := bstep (se 1 (by rfl) ⟨3102755, by rfl⟩ : syracuseStep 4137007 = 6205511) B6205511
theorem B22195795 : Blo 299831 22195795 := bstep (se 1 (by rfl) ⟨16646846, by rfl⟩ : syracuseStep 22195795 = 33293693) B33293693
theorem B3651065 : Blo 299831 3651065 := bstep (se 2 (by rfl) ⟨1369149, by rfl⟩ : syracuseStep 3651065 = 2738299) B2738299
theorem B572159 : Blo 299831 572159 := bstep (se 1 (by rfl) ⟨429119, by rfl⟩ : syracuseStep 572159 = 858239) B858239
theorem B4637135 : Blo 299831 4637135 := bstep (se 1 (by rfl) ⟨3477851, by rfl⟩ : syracuseStep 4637135 = 6955703) B6955703
theorem B6997103 : Blo 299831 6997103 := bstep (se 1 (by rfl) ⟨5247827, by rfl⟩ : syracuseStep 6997103 = 10495655) B10495655
theorem B677177 : Blo 299831 677177 := bstep (se 2 (by rfl) ⟨253941, by rfl⟩ : syracuseStep 677177 = 507883) B507883
theorem B5527541 : Blo 299831 5527541 := bstep (se 5 (by rfl) ⟨259103, by rfl⟩ : syracuseStep 5527541 = 518207) B518207
theorem B1727183 : Blo 299831 1727183 := bstep (se 1 (by rfl) ⟨1295387, by rfl⟩ : syracuseStep 1727183 = 2590775) B2590775
theorem B450119 : Blo 299831 450119 := bstep (se 1 (by rfl) ⟨337589, by rfl⟩ : syracuseStep 450119 = 675179) B675179
theorem B679823 : Blo 299831 679823 := bstep (se 1 (by rfl) ⟨509867, by rfl⟩ : syracuseStep 679823 = 1019735) B1019735
theorem B450587 : Blo 299831 450587 := bstep (se 1 (by rfl) ⟨337940, by rfl⟩ : syracuseStep 450587 = 675881) B675881
theorem B681407 : Blo 299831 681407 := bstep (se 1 (by rfl) ⟨511055, by rfl⟩ : syracuseStep 681407 = 1022111) B1022111
theorem B1534139 : Blo 299831 1534139 := bstep (se 1 (by rfl) ⟨1150604, by rfl⟩ : syracuseStep 1534139 = 2301209) B2301209
theorem B5926223 : Blo 299831 5926223 := bstep (se 1 (by rfl) ⟨4444667, by rfl⟩ : syracuseStep 5926223 = 8889335) B8889335
theorem B323023 : Blo 299831 323023 := bstep (se 1 (by rfl) ⟨242267, by rfl⟩ : syracuseStep 323023 = 484535) B484535
theorem B978409 : Blo 299831 978409 := bstep (se 2 (by rfl) ⟨366903, by rfl⟩ : syracuseStep 978409 = 733807) B733807
theorem B455147 : Blo 299831 455147 := bstep (se 1 (by rfl) ⟨341360, by rfl⟩ : syracuseStep 455147 = 682721) B682721
theorem B3309311 : Blo 299831 3309311 := bstep (se 1 (by rfl) ⟨2481983, by rfl⟩ : syracuseStep 3309311 = 4963967) B4963967
theorem B2293919 : Blo 299831 2293919 := bstep (se 1 (by rfl) ⟨1720439, by rfl⟩ : syracuseStep 2293919 = 3440879) B3440879
theorem B2294891 : Blo 299831 2294891 := bstep (se 1 (by rfl) ⟨1721168, by rfl⟩ : syracuseStep 2294891 = 3442337) B3442337
theorem B1151455 : Blo 299831 1151455 := bstep (se 1 (by rfl) ⟨863591, by rfl⟩ : syracuseStep 1151455 = 1727183) B1727183
theorem B430697 : Blo 299831 430697 := bstep (se 2 (by rfl) ⟨161511, by rfl⟩ : syracuseStep 430697 = 323023) B323023
theorem B29594393 : Blo 299831 29594393 := bstep (se 2 (by rfl) ⟨11097897, by rfl⟩ : syracuseStep 29594393 = 22195795) B22195795
theorem B300079 : Blo 299831 300079 := bstep (se 1 (by rfl) ⟨225059, by rfl⟩ : syracuseStep 300079 = 450119) B450119
theorem B300391 : Blo 299831 300391 := bstep (se 1 (by rfl) ⟨225293, by rfl⟩ : syracuseStep 300391 = 450587) B450587
theorem B1022759 : Blo 299831 1022759 := bstep (se 1 (by rfl) ⟨767069, by rfl⟩ : syracuseStep 1022759 = 1534139) B1534139
theorem B5218181 : Blo 299831 5218181 := bstep (se 4 (by rfl) ⟨489204, by rfl⟩ : syracuseStep 5218181 = 978409) B978409
theorem B303431 : Blo 299831 303431 := bstep (se 1 (by rfl) ⟨227573, by rfl⟩ : syracuseStep 303431 = 455147) B455147
theorem B2434043 : Blo 299831 2434043 := bstep (se 1 (by rfl) ⟨1825532, by rfl⟩ : syracuseStep 2434043 = 3651065) B3651065
theorem B2206207 : Blo 299831 2206207 := bstep (se 1 (by rfl) ⟨1654655, by rfl⟩ : syracuseStep 2206207 = 3309311) B3309311
theorem B5516009 : Blo 299831 5516009 := bstep (se 2 (by rfl) ⟨2068503, by rfl⟩ : syracuseStep 5516009 = 4137007) B4137007
theorem B4664735 : Blo 299831 4664735 := bstep (se 1 (by rfl) ⟨3498551, by rfl⟩ : syracuseStep 4664735 = 6997103) B6997103
theorem B12365693 : Blo 299831 12365693 := bstep (se 3 (by rfl) ⟨2318567, by rfl⟩ : syracuseStep 12365693 = 4637135) B4637135
theorem B3685027 : Blo 299831 3685027 := bstep (se 1 (by rfl) ⟨2763770, by rfl⟩ : syracuseStep 3685027 = 5527541) B5527541
theorem B3950815 : Blo 299831 3950815 := bstep (se 1 (by rfl) ⟨2963111, by rfl⟩ : syracuseStep 3950815 = 5926223) B5926223
theorem B381439 : Blo 299831 381439 := bstep (se 1 (by rfl) ⟨286079, by rfl⟩ : syracuseStep 381439 = 572159) B572159
theorem B2905703 : Blo 299831 2905703 := bstep (se 1 (by rfl) ⟨2179277, by rfl⟩ : syracuseStep 2905703 = 4358555) B4358555
theorem B679607 : Blo 299831 679607 := bstep (se 1 (by rfl) ⟨509705, by rfl⟩ : syracuseStep 679607 = 1019411) B1019411
theorem B451451 : Blo 299831 451451 := bstep (se 1 (by rfl) ⟨338588, by rfl⟩ : syracuseStep 451451 = 677177) B677177
theorem B453215 : Blo 299831 453215 := bstep (se 1 (by rfl) ⟨339911, by rfl⟩ : syracuseStep 453215 = 679823) B679823
theorem B233270513 : Blo 299831 233270513 := bstep (se 2 (by rfl) ⟨87476442, by rfl⟩ : syracuseStep 233270513 = 174952885) B174952885
theorem B454271 : Blo 299831 454271 := bstep (se 1 (by rfl) ⟨340703, by rfl⟩ : syracuseStep 454271 = 681407) B681407
theorem B1148525 : Blo 299831 1148525 := bstep (se 3 (by rfl) ⟨215348, by rfl⟩ : syracuseStep 1148525 = 430697) B430697
theorem B11766437 : Blo 299831 11766437 := bstep (se 4 (by rfl) ⟨1103103, by rfl⟩ : syracuseStep 11766437 = 2206207) B2206207
theorem B19729595 : Blo 299831 19729595 := bstep (se 1 (by rfl) ⟨14797196, by rfl⟩ : syracuseStep 19729595 = 29594393) B29594393
theorem B1937135 : Blo 299831 1937135 := bstep (se 1 (by rfl) ⟨1452851, by rfl⟩ : syracuseStep 1937135 = 2905703) B2905703
theorem B3478787 : Blo 299831 3478787 := bstep (se 1 (by rfl) ⟨2609090, by rfl⟩ : syracuseStep 3478787 = 5218181) B5218181
theorem B300967 : Blo 299831 300967 := bstep (se 1 (by rfl) ⟨225725, by rfl⟩ : syracuseStep 300967 = 451451) B451451
theorem B302143 : Blo 299831 302143 := bstep (se 1 (by rfl) ⟨226607, by rfl⟩ : syracuseStep 302143 = 453215) B453215
theorem B3677339 : Blo 299831 3677339 := bstep (se 1 (by rfl) ⟨2758004, by rfl⟩ : syracuseStep 3677339 = 5516009) B5516009
theorem B302847 : Blo 299831 302847 := bstep (se 1 (by rfl) ⟨227135, by rfl⟩ : syracuseStep 302847 = 454271) B454271
theorem B1622695 : Blo 299831 1622695 := bstep (se 1 (by rfl) ⟨1217021, by rfl⟩ : syracuseStep 1622695 = 2434043) B2434043
theorem B508585 : Blo 299831 508585 := bstep (se 2 (by rfl) ⟨190719, by rfl⟩ : syracuseStep 508585 = 381439) B381439
theorem B8243795 : Blo 299831 8243795 := bstep (se 1 (by rfl) ⟨6182846, by rfl⟩ : syracuseStep 8243795 = 12365693) B12365693
theorem B1529279 : Blo 299831 1529279 := bstep (se 1 (by rfl) ⟨1146959, by rfl⟩ : syracuseStep 1529279 = 2293919) B2293919
theorem B1529927 : Blo 299831 1529927 := bstep (se 1 (by rfl) ⟨1147445, by rfl⟩ : syracuseStep 1529927 = 2294891) B2294891
theorem B5267753 : Blo 299831 5267753 := bstep (se 2 (by rfl) ⟨1975407, by rfl⟩ : syracuseStep 5267753 = 3950815) B3950815
theorem B681839 : Blo 299831 681839 := bstep (se 1 (by rfl) ⟨511379, by rfl⟩ : syracuseStep 681839 = 1022759) B1022759
theorem B453071 : Blo 299831 453071 := bstep (se 1 (by rfl) ⟨339803, by rfl⟩ : syracuseStep 453071 = 679607) B679607
theorem B1535273 : Blo 299831 1535273 := bstep (se 2 (by rfl) ⟨575727, by rfl⟩ : syracuseStep 1535273 = 1151455) B1151455
theorem B155513675 : Blo 299831 155513675 := bstep (se 1 (by rfl) ⟨116635256, by rfl⟩ : syracuseStep 155513675 = 233270513) B233270513
theorem B3109823 : Blo 299831 3109823 := bstep (se 1 (by rfl) ⟨2332367, by rfl⟩ : syracuseStep 3109823 = 4664735) B4664735
theorem B4913369 : Blo 299831 4913369 := bstep (se 2 (by rfl) ⟨1842513, by rfl⟩ : syracuseStep 4913369 = 3685027) B3685027
theorem B2163593 : Blo 299831 2163593 := bstep (se 2 (by rfl) ⟨811347, by rfl⟩ : syracuseStep 2163593 = 1622695) B1622695
theorem B1019519 : Blo 299831 1019519 := bstep (se 1 (by rfl) ⟨764639, by rfl⟩ : syracuseStep 1019519 = 1529279) B1529279
theorem B1019951 : Blo 299831 1019951 := bstep (se 1 (by rfl) ⟨764963, by rfl⟩ : syracuseStep 1019951 = 1529927) B1529927
theorem B3511835 : Blo 299831 3511835 := bstep (se 1 (by rfl) ⟨2633876, by rfl⟩ : syracuseStep 3511835 = 5267753) B5267753
theorem B302047 : Blo 299831 302047 := bstep (se 1 (by rfl) ⟨226535, by rfl⟩ : syracuseStep 302047 = 453071) B453071
theorem B1023515 : Blo 299831 1023515 := bstep (se 1 (by rfl) ⟨767636, by rfl⟩ : syracuseStep 1023515 = 1535273) B1535273
theorem B2073215 : Blo 299831 2073215 := bstep (se 1 (by rfl) ⟨1554911, by rfl⟩ : syracuseStep 2073215 = 3109823) B3109823
theorem B765683 : Blo 299831 765683 := bstep (se 1 (by rfl) ⟨574262, by rfl⟩ : syracuseStep 765683 = 1148525) B1148525
theorem B7844291 : Blo 299831 7844291 := bstep (se 1 (by rfl) ⟨5883218, by rfl⟩ : syracuseStep 7844291 = 11766437) B11766437
theorem B13153063 : Blo 299831 13153063 := bstep (se 1 (by rfl) ⟨9864797, by rfl⟩ : syracuseStep 13153063 = 19729595) B19729595
theorem B5165693 : Blo 299831 5165693 := bstep (se 3 (by rfl) ⟨968567, by rfl⟩ : syracuseStep 5165693 = 1937135) B1937135
theorem B678113 : Blo 299831 678113 := bstep (se 2 (by rfl) ⟨254292, by rfl⟩ : syracuseStep 678113 = 508585) B508585
theorem B5495863 : Blo 299831 5495863 := bstep (se 1 (by rfl) ⟨4121897, by rfl⟩ : syracuseStep 5495863 = 8243795) B8243795
theorem B2319191 : Blo 299831 2319191 := bstep (se 1 (by rfl) ⟨1739393, by rfl⟩ : syracuseStep 2319191 = 3478787) B3478787
theorem B2451559 : Blo 299831 2451559 := bstep (se 1 (by rfl) ⟨1838669, by rfl⟩ : syracuseStep 2451559 = 3677339) B3677339
theorem B454559 : Blo 299831 454559 := bstep (se 1 (by rfl) ⟨340919, by rfl⟩ : syracuseStep 454559 = 681839) B681839
theorem B103675783 : Blo 299831 103675783 := bstep (se 1 (by rfl) ⟨77756837, by rfl⟩ : syracuseStep 103675783 = 155513675) B155513675
theorem B3275579 : Blo 299831 3275579 := bstep (se 1 (by rfl) ⟨2456684, by rfl⟩ : syracuseStep 3275579 = 4913369) B4913369
theorem B1442395 : Blo 299831 1442395 := bstep (se 1 (by rfl) ⟨1081796, by rfl⟩ : syracuseStep 1442395 = 2163593) B2163593
theorem B3443795 : Blo 299831 3443795 := bstep (se 1 (by rfl) ⟨2582846, by rfl⟩ : syracuseStep 3443795 = 5165693) B5165693
theorem B1382143 : Blo 299831 1382143 := bstep (se 1 (by rfl) ⟨1036607, by rfl⟩ : syracuseStep 1382143 = 2073215) B2073215
theorem B1546127 : Blo 299831 1546127 := bstep (se 1 (by rfl) ⟨1159595, by rfl⟩ : syracuseStep 1546127 = 2319191) B2319191
theorem B17537417 : Blo 299831 17537417 := bstep (se 2 (by rfl) ⟨6576531, by rfl⟩ : syracuseStep 17537417 = 13153063) B13153063
theorem B303039 : Blo 299831 303039 := bstep (se 1 (by rfl) ⟨227279, by rfl⟩ : syracuseStep 303039 = 454559) B454559
theorem B2341223 : Blo 299831 2341223 := bstep (se 1 (by rfl) ⟨1755917, by rfl⟩ : syracuseStep 2341223 = 3511835) B3511835
theorem B8734877 : Blo 299831 8734877 := bstep (se 3 (by rfl) ⟨1637789, by rfl⟩ : syracuseStep 8734877 = 3275579) B3275579
theorem B510455 : Blo 299831 510455 := bstep (se 1 (by rfl) ⟨382841, by rfl⟩ : syracuseStep 510455 = 765683) B765683
theorem B138234377 : Blo 299831 138234377 := bstep (se 2 (by rfl) ⟨51837891, by rfl⟩ : syracuseStep 138234377 = 103675783) B103675783
theorem B5229527 : Blo 299831 5229527 := bstep (se 1 (by rfl) ⟨3922145, by rfl⟩ : syracuseStep 5229527 = 7844291) B7844291
theorem B7327817 : Blo 299831 7327817 := bstep (se 2 (by rfl) ⟨2747931, by rfl⟩ : syracuseStep 7327817 = 5495863) B5495863
theorem B679679 : Blo 299831 679679 := bstep (se 1 (by rfl) ⟨509759, by rfl⟩ : syracuseStep 679679 = 1019519) B1019519
theorem B679967 : Blo 299831 679967 := bstep (se 1 (by rfl) ⟨509975, by rfl⟩ : syracuseStep 679967 = 1019951) B1019951
theorem B3268745 : Blo 299831 3268745 := bstep (se 2 (by rfl) ⟨1225779, by rfl⟩ : syracuseStep 3268745 = 2451559) B2451559
theorem B452075 : Blo 299831 452075 := bstep (se 1 (by rfl) ⟨339056, by rfl⟩ : syracuseStep 452075 = 678113) B678113
theorem B682343 : Blo 299831 682343 := bstep (se 1 (by rfl) ⟨511757, by rfl⟩ : syracuseStep 682343 = 1023515) B1023515
theorem B2295863 : Blo 299831 2295863 := bstep (se 1 (by rfl) ⟨1721897, by rfl⟩ : syracuseStep 2295863 = 3443795) B3443795
theorem B4885211 : Blo 299831 4885211 := bstep (se 1 (by rfl) ⟨3663908, by rfl⟩ : syracuseStep 4885211 = 7327817) B7327817
theorem B301383 : Blo 299831 301383 := bstep (se 1 (by rfl) ⟨226037, by rfl⟩ : syracuseStep 301383 = 452075) B452075
theorem B1842857 : Blo 299831 1842857 := bstep (se 2 (by rfl) ⟨691071, by rfl⟩ : syracuseStep 1842857 = 1382143) B1382143
theorem B340303 : Blo 299831 340303 := bstep (se 1 (by rfl) ⟨255227, by rfl⟩ : syracuseStep 340303 = 510455) B510455
theorem B92156251 : Blo 299831 92156251 := bstep (se 1 (by rfl) ⟨69117188, by rfl⟩ : syracuseStep 92156251 = 138234377) B138234377
theorem B1030751 : Blo 299831 1030751 := bstep (se 1 (by rfl) ⟨773063, by rfl⟩ : syracuseStep 1030751 = 1546127) B1546127
theorem B2179163 : Blo 299831 2179163 := bstep (se 1 (by rfl) ⟨1634372, by rfl⟩ : syracuseStep 2179163 = 3268745) B3268745
theorem B13945405 : Blo 299831 13945405 := bstep (se 3 (by rfl) ⟨2614763, by rfl⟩ : syracuseStep 13945405 = 5229527) B5229527
theorem B1560815 : Blo 299831 1560815 := bstep (se 1 (by rfl) ⟨1170611, by rfl⟩ : syracuseStep 1560815 = 2341223) B2341223
theorem B1923193 : Blo 299831 1923193 := bstep (se 2 (by rfl) ⟨721197, by rfl⟩ : syracuseStep 1923193 = 1442395) B1442395
theorem B5823251 : Blo 299831 5823251 := bstep (se 1 (by rfl) ⟨4367438, by rfl⟩ : syracuseStep 5823251 = 8734877) B8734877
theorem B11691611 : Blo 299831 11691611 := bstep (se 1 (by rfl) ⟨8768708, by rfl⟩ : syracuseStep 11691611 = 17537417) B17537417
theorem B453119 : Blo 299831 453119 := bstep (se 1 (by rfl) ⟨339839, by rfl⟩ : syracuseStep 453119 = 679679) B679679
theorem B453311 : Blo 299831 453311 := bstep (se 1 (by rfl) ⟨339983, by rfl⟩ : syracuseStep 453311 = 679967) B679967
theorem B454895 : Blo 299831 454895 := bstep (se 1 (by rfl) ⟨341171, by rfl⟩ : syracuseStep 454895 = 682343) B682343
theorem B302079 : Blo 299831 302079 := bstep (se 1 (by rfl) ⟨226559, by rfl⟩ : syracuseStep 302079 = 453119) B453119
theorem B302207 : Blo 299831 302207 := bstep (se 1 (by rfl) ⟨226655, by rfl⟩ : syracuseStep 302207 = 453311) B453311
theorem B303263 : Blo 299831 303263 := bstep (se 1 (by rfl) ⟨227447, by rfl⟩ : syracuseStep 303263 = 454895) B454895
theorem B2564257 : Blo 299831 2564257 := bstep (se 2 (by rfl) ⟨961596, by rfl⟩ : syracuseStep 2564257 = 1923193) B1923193
theorem B5811101 : Blo 299831 5811101 := bstep (se 3 (by rfl) ⟨1089581, by rfl⟩ : syracuseStep 5811101 = 2179163) B2179163
theorem B18593873 : Blo 299831 18593873 := bstep (se 2 (by rfl) ⟨6972702, by rfl⟩ : syracuseStep 18593873 = 13945405) B13945405
theorem B3882167 : Blo 299831 3882167 := bstep (se 1 (by rfl) ⟨2911625, by rfl⟩ : syracuseStep 3882167 = 5823251) B5823251
theorem B1228571 : Blo 299831 1228571 := bstep (se 1 (by rfl) ⟨921428, by rfl⟩ : syracuseStep 1228571 = 1842857) B1842857
theorem B13027229 : Blo 299831 13027229 := bstep (se 3 (by rfl) ⟨2442605, by rfl⟩ : syracuseStep 13027229 = 4885211) B4885211
theorem B1530575 : Blo 299831 1530575 := bstep (se 1 (by rfl) ⟨1147931, by rfl⟩ : syracuseStep 1530575 = 2295863) B2295863
theorem B1040543 : Blo 299831 1040543 := bstep (se 1 (by rfl) ⟨780407, by rfl⟩ : syracuseStep 1040543 = 1560815) B1560815
theorem B453737 : Blo 299831 453737 := bstep (se 2 (by rfl) ⟨170151, by rfl⟩ : syracuseStep 453737 = 340303) B340303
theorem B122875001 : Blo 299831 122875001 := bstep (se 2 (by rfl) ⟨46078125, by rfl⟩ : syracuseStep 122875001 = 92156251) B92156251
theorem B7794407 : Blo 299831 7794407 := bstep (se 1 (by rfl) ⟨5845805, by rfl⟩ : syracuseStep 7794407 = 11691611) B11691611
theorem B687167 : Blo 299831 687167 := bstep (se 1 (by rfl) ⟨515375, by rfl⟩ : syracuseStep 687167 = 1030751) B1030751
theorem B8684819 : Blo 299831 8684819 := bstep (se 1 (by rfl) ⟨6513614, by rfl⟩ : syracuseStep 8684819 = 13027229) B13027229
theorem B1020383 : Blo 299831 1020383 := bstep (se 1 (by rfl) ⟨765287, by rfl⟩ : syracuseStep 1020383 = 1530575) B1530575
theorem B693695 : Blo 299831 693695 := bstep (se 1 (by rfl) ⟨520271, by rfl⟩ : syracuseStep 693695 = 1040543) B1040543
theorem B3874067 : Blo 299831 3874067 := bstep (se 1 (by rfl) ⟨2905550, by rfl⟩ : syracuseStep 3874067 = 5811101) B5811101
theorem B302491 : Blo 299831 302491 := bstep (se 1 (by rfl) ⟨226868, by rfl⟩ : syracuseStep 302491 = 453737) B453737
theorem B12395915 : Blo 299831 12395915 := bstep (se 1 (by rfl) ⟨9296936, by rfl⟩ : syracuseStep 12395915 = 18593873) B18593873
theorem B3419009 : Blo 299831 3419009 := bstep (se 2 (by rfl) ⟨1282128, by rfl⟩ : syracuseStep 3419009 = 2564257) B2564257
theorem B5196271 : Blo 299831 5196271 := bstep (se 1 (by rfl) ⟨3897203, by rfl⟩ : syracuseStep 5196271 = 7794407) B7794407
theorem B81916667 : Blo 299831 81916667 := bstep (se 1 (by rfl) ⟨61437500, by rfl⟩ : syracuseStep 81916667 = 122875001) B122875001
theorem B458111 : Blo 299831 458111 := bstep (se 1 (by rfl) ⟨343583, by rfl⟩ : syracuseStep 458111 = 687167) B687167
theorem B2588111 : Blo 299831 2588111 := bstep (se 1 (by rfl) ⟨1941083, by rfl⟩ : syracuseStep 2588111 = 3882167) B3882167
theorem B819047 : Blo 299831 819047 := bstep (se 1 (by rfl) ⟨614285, by rfl⟩ : syracuseStep 819047 = 1228571) B1228571
theorem B8263943 : Blo 299831 8263943 := bstep (se 1 (by rfl) ⟨6197957, by rfl⟩ : syracuseStep 8263943 = 12395915) B12395915
theorem B305407 : Blo 299831 305407 := bstep (se 1 (by rfl) ⟨229055, by rfl⟩ : syracuseStep 305407 = 458111) B458111
theorem B6928361 : Blo 299831 6928361 := bstep (se 2 (by rfl) ⟨2598135, by rfl⟩ : syracuseStep 6928361 = 5196271) B5196271
theorem B1849853 : Blo 299831 1849853 := bstep (se 3 (by rfl) ⟨346847, by rfl⟩ : syracuseStep 1849853 = 693695) B693695
theorem B2279339 : Blo 299831 2279339 := bstep (se 1 (by rfl) ⟨1709504, by rfl⟩ : syracuseStep 2279339 = 3419009) B3419009
theorem B54611111 : Blo 299831 54611111 := bstep (se 1 (by rfl) ⟨40958333, by rfl⟩ : syracuseStep 54611111 = 81916667) B81916667
theorem B1725407 : Blo 299831 1725407 := bstep (se 1 (by rfl) ⟨1294055, by rfl⟩ : syracuseStep 1725407 = 2588111) B2588111
theorem B546031 : Blo 299831 546031 := bstep (se 1 (by rfl) ⟨409523, by rfl⟩ : syracuseStep 546031 = 819047) B819047
theorem B5789879 : Blo 299831 5789879 := bstep (se 1 (by rfl) ⟨4342409, by rfl⟩ : syracuseStep 5789879 = 8684819) B8684819
theorem B680255 : Blo 299831 680255 := bstep (se 1 (by rfl) ⟨510191, by rfl⟩ : syracuseStep 680255 = 1020383) B1020383
theorem B2582711 : Blo 299831 2582711 := bstep (se 1 (by rfl) ⟨1937033, by rfl⟩ : syracuseStep 2582711 = 3874067) B3874067
theorem B36407407 : Blo 299831 36407407 := bstep (se 1 (by rfl) ⟨27305555, by rfl⟩ : syracuseStep 36407407 = 54611111) B54611111
theorem B1150271 : Blo 299831 1150271 := bstep (se 1 (by rfl) ⟨862703, by rfl⟩ : syracuseStep 1150271 = 1725407) B1725407
theorem B5509295 : Blo 299831 5509295 := bstep (se 1 (by rfl) ⟨4131971, by rfl⟩ : syracuseStep 5509295 = 8263943) B8263943
theorem B728041 : Blo 299831 728041 := bstep (se 2 (by rfl) ⟨273015, by rfl⟩ : syracuseStep 728041 = 546031) B546031
theorem B1519559 : Blo 299831 1519559 := bstep (se 1 (by rfl) ⟨1139669, by rfl⟩ : syracuseStep 1519559 = 2279339) B2279339
theorem B1721807 : Blo 299831 1721807 := bstep (se 1 (by rfl) ⟨1291355, by rfl⟩ : syracuseStep 1721807 = 2582711) B2582711
theorem B1233235 : Blo 299831 1233235 := bstep (se 1 (by rfl) ⟨924926, by rfl⟩ : syracuseStep 1233235 = 1849853) B1849853
theorem B1628837 : Blo 299831 1628837 := bstep (se 4 (by rfl) ⟨152703, by rfl⟩ : syracuseStep 1628837 = 305407) B305407
theorem B3859919 : Blo 299831 3859919 := bstep (se 1 (by rfl) ⟨2894939, by rfl⟩ : syracuseStep 3859919 = 5789879) B5789879
theorem B453503 : Blo 299831 453503 := bstep (se 1 (by rfl) ⟨340127, by rfl⟩ : syracuseStep 453503 = 680255) B680255
theorem B4618907 : Blo 299831 4618907 := bstep (se 1 (by rfl) ⟨3464180, by rfl⟩ : syracuseStep 4618907 = 6928361) B6928361
theorem B1147871 : Blo 299831 1147871 := bstep (se 1 (by rfl) ⟨860903, by rfl⟩ : syracuseStep 1147871 = 1721807) B1721807
theorem B3672863 : Blo 299831 3672863 := bstep (se 1 (by rfl) ⟨2754647, by rfl⟩ : syracuseStep 3672863 = 5509295) B5509295
theorem B1085891 : Blo 299831 1085891 := bstep (se 1 (by rfl) ⟨814418, by rfl⟩ : syracuseStep 1085891 = 1628837) B1628837
theorem B1644313 : Blo 299831 1644313 := bstep (se 2 (by rfl) ⟨616617, by rfl⟩ : syracuseStep 1644313 = 1233235) B1233235
theorem B302335 : Blo 299831 302335 := bstep (se 1 (by rfl) ⟨226751, by rfl⟩ : syracuseStep 302335 = 453503) B453503
theorem B766847 : Blo 299831 766847 := bstep (se 1 (by rfl) ⟨575135, by rfl⟩ : syracuseStep 766847 = 1150271) B1150271
theorem B48543209 : Blo 299831 48543209 := bstep (se 2 (by rfl) ⟨18203703, by rfl⟩ : syracuseStep 48543209 = 36407407) B36407407
theorem B2573279 : Blo 299831 2573279 := bstep (se 1 (by rfl) ⟨1929959, by rfl⟩ : syracuseStep 2573279 = 3859919) B3859919
theorem B970721 : Blo 299831 970721 := bstep (se 2 (by rfl) ⟨364020, by rfl⟩ : syracuseStep 970721 = 728041) B728041
theorem B1013039 : Blo 299831 1013039 := bstep (se 1 (by rfl) ⟨759779, by rfl⟩ : syracuseStep 1013039 = 1519559) B1519559
theorem B3079271 : Blo 299831 3079271 := bstep (se 1 (by rfl) ⟨2309453, by rfl⟩ : syracuseStep 3079271 = 4618907) B4618907
theorem B1715519 : Blo 299831 1715519 := bstep (se 1 (by rfl) ⟨1286639, by rfl⟩ : syracuseStep 1715519 = 2573279) B2573279
theorem B765247 : Blo 299831 765247 := bstep (se 1 (by rfl) ⟨573935, by rfl⟩ : syracuseStep 765247 = 1147871) B1147871
theorem B2895709 : Blo 299831 2895709 := bstep (se 3 (by rfl) ⟨542945, by rfl⟩ : syracuseStep 2895709 = 1085891) B1085891
theorem B511231 : Blo 299831 511231 := bstep (se 1 (by rfl) ⟨383423, by rfl⟩ : syracuseStep 511231 = 766847) B766847
theorem B675359 : Blo 299831 675359 := bstep (se 1 (by rfl) ⟨506519, by rfl⟩ : syracuseStep 675359 = 1013039) B1013039
theorem B32362139 : Blo 299831 32362139 := bstep (se 1 (by rfl) ⟨24271604, by rfl⟩ : syracuseStep 32362139 = 48543209) B48543209
theorem B2052847 : Blo 299831 2052847 := bstep (se 1 (by rfl) ⟨1539635, by rfl⟩ : syracuseStep 2052847 = 3079271) B3079271
theorem B2448575 : Blo 299831 2448575 := bstep (se 1 (by rfl) ⟨1836431, by rfl⟩ : syracuseStep 2448575 = 3672863) B3672863
theorem B647147 : Blo 299831 647147 := bstep (se 1 (by rfl) ⟨485360, by rfl⟩ : syracuseStep 647147 = 970721) B970721
theorem B2192417 : Blo 299831 2192417 := bstep (se 2 (by rfl) ⟨822156, by rfl⟩ : syracuseStep 2192417 = 1644313) B1644313
theorem B10948517 : Blo 299831 10948517 := bstep (se 4 (by rfl) ⟨1026423, by rfl⟩ : syracuseStep 10948517 = 2052847) B2052847
theorem B1020329 : Blo 299831 1020329 := bstep (se 2 (by rfl) ⟨382623, by rfl⟩ : syracuseStep 1020329 = 765247) B765247
theorem B21574759 : Blo 299831 21574759 := bstep (se 1 (by rfl) ⟨16181069, by rfl⟩ : syracuseStep 21574759 = 32362139) B32362139
theorem B1461611 : Blo 299831 1461611 := bstep (se 1 (by rfl) ⟨1096208, by rfl⟩ : syracuseStep 1461611 = 2192417) B2192417
theorem B1725725 : Blo 299831 1725725 := bstep (se 3 (by rfl) ⟨323573, by rfl⟩ : syracuseStep 1725725 = 647147) B647147
theorem B450239 : Blo 299831 450239 := bstep (se 1 (by rfl) ⟨337679, by rfl⟩ : syracuseStep 450239 = 675359) B675359
theorem B681641 : Blo 299831 681641 := bstep (se 2 (by rfl) ⟨255615, by rfl⟩ : syracuseStep 681641 = 511231) B511231
theorem B1632383 : Blo 299831 1632383 := bstep (se 1 (by rfl) ⟨1224287, by rfl⟩ : syracuseStep 1632383 = 2448575) B2448575
theorem B3860945 : Blo 299831 3860945 := bstep (se 2 (by rfl) ⟨1447854, by rfl⟩ : syracuseStep 3860945 = 2895709) B2895709
theorem B1143679 : Blo 299831 1143679 := bstep (se 1 (by rfl) ⟨857759, by rfl⟩ : syracuseStep 1143679 = 1715519) B1715519
theorem B1150483 : Blo 299831 1150483 := bstep (se 1 (by rfl) ⟨862862, by rfl⟩ : syracuseStep 1150483 = 1725725) B1725725
theorem B300159 : Blo 299831 300159 := bstep (se 1 (by rfl) ⟨225119, by rfl⟩ : syracuseStep 300159 = 450239) B450239
theorem B1088255 : Blo 299831 1088255 := bstep (se 1 (by rfl) ⟨816191, by rfl⟩ : syracuseStep 1088255 = 1632383) B1632383
theorem B1524905 : Blo 299831 1524905 := bstep (se 2 (by rfl) ⟨571839, by rfl⟩ : syracuseStep 1524905 = 1143679) B1143679
theorem B2573963 : Blo 299831 2573963 := bstep (se 1 (by rfl) ⟨1930472, by rfl⟩ : syracuseStep 2573963 = 3860945) B3860945
theorem B7299011 : Blo 299831 7299011 := bstep (se 1 (by rfl) ⟨5474258, by rfl⟩ : syracuseStep 7299011 = 10948517) B10948517
theorem B680219 : Blo 299831 680219 := bstep (se 1 (by rfl) ⟨510164, by rfl⟩ : syracuseStep 680219 = 1020329) B1020329
theorem B454427 : Blo 299831 454427 := bstep (se 1 (by rfl) ⟨340820, by rfl⟩ : syracuseStep 454427 = 681641) B681641
theorem B28766345 : Blo 299831 28766345 := bstep (se 2 (by rfl) ⟨10787379, by rfl⟩ : syracuseStep 28766345 = 21574759) B21574759
theorem B3897629 : Blo 299831 3897629 := bstep (se 3 (by rfl) ⟨730805, by rfl⟩ : syracuseStep 3897629 = 1461611) B1461611
theorem B76710253 : Blo 299831 76710253 := bstep (se 3 (by rfl) ⟨14383172, by rfl⟩ : syracuseStep 76710253 = 28766345) B28766345
theorem B1016603 : Blo 299831 1016603 := bstep (se 1 (by rfl) ⟨762452, by rfl⟩ : syracuseStep 1016603 = 1524905) B1524905
theorem B302951 : Blo 299831 302951 := bstep (se 1 (by rfl) ⟨227213, by rfl⟩ : syracuseStep 302951 = 454427) B454427
theorem B2598419 : Blo 299831 2598419 := bstep (se 1 (by rfl) ⟨1948814, by rfl⟩ : syracuseStep 2598419 = 3897629) B3897629
theorem B1715975 : Blo 299831 1715975 := bstep (se 1 (by rfl) ⟨1286981, by rfl⟩ : syracuseStep 1715975 = 2573963) B2573963
theorem B4866007 : Blo 299831 4866007 := bstep (se 1 (by rfl) ⟨3649505, by rfl⟩ : syracuseStep 4866007 = 7299011) B7299011
theorem B2902013 : Blo 299831 2902013 := bstep (se 3 (by rfl) ⟨544127, by rfl⟩ : syracuseStep 2902013 = 1088255) B1088255
theorem B1533977 : Blo 299831 1533977 := bstep (se 2 (by rfl) ⟨575241, by rfl⟩ : syracuseStep 1533977 = 1150483) B1150483
theorem B453479 : Blo 299831 453479 := bstep (se 1 (by rfl) ⟨340109, by rfl⟩ : syracuseStep 453479 = 680219) B680219
theorem B1934675 : Blo 299831 1934675 := bstep (se 1 (by rfl) ⟨1451006, by rfl⟩ : syracuseStep 1934675 = 2902013) B2902013
theorem B1022651 : Blo 299831 1022651 := bstep (se 1 (by rfl) ⟨766988, by rfl⟩ : syracuseStep 1022651 = 1533977) B1533977
theorem B302319 : Blo 299831 302319 := bstep (se 1 (by rfl) ⟨226739, by rfl⟩ : syracuseStep 302319 = 453479) B453479
theorem B102280337 : Blo 299831 102280337 := bstep (se 2 (by rfl) ⟨38355126, by rfl⟩ : syracuseStep 102280337 = 76710253) B76710253
theorem B677735 : Blo 299831 677735 := bstep (se 1 (by rfl) ⟨508301, by rfl⟩ : syracuseStep 677735 = 1016603) B1016603
theorem B1732279 : Blo 299831 1732279 := bstep (se 1 (by rfl) ⟨1299209, by rfl⟩ : syracuseStep 1732279 = 2598419) B2598419
theorem B1143983 : Blo 299831 1143983 := bstep (se 1 (by rfl) ⟨857987, by rfl⟩ : syracuseStep 1143983 = 1715975) B1715975
theorem B6488009 : Blo 299831 6488009 := bstep (se 2 (by rfl) ⟨2433003, by rfl⟩ : syracuseStep 6488009 = 4866007) B4866007
theorem B762655 : Blo 299831 762655 := bstep (se 1 (by rfl) ⟨571991, by rfl⟩ : syracuseStep 762655 = 1143983) B1143983
theorem B1289783 : Blo 299831 1289783 := bstep (se 1 (by rfl) ⟨967337, by rfl⟩ : syracuseStep 1289783 = 1934675) B1934675
theorem B2309705 : Blo 299831 2309705 := bstep (se 2 (by rfl) ⟨866139, by rfl⟩ : syracuseStep 2309705 = 1732279) B1732279
theorem B451823 : Blo 299831 451823 := bstep (se 1 (by rfl) ⟨338867, by rfl⟩ : syracuseStep 451823 = 677735) B677735
theorem B681767 : Blo 299831 681767 := bstep (se 1 (by rfl) ⟨511325, by rfl⟩ : syracuseStep 681767 = 1022651) B1022651
theorem B68186891 : Blo 299831 68186891 := bstep (se 1 (by rfl) ⟨51140168, by rfl⟩ : syracuseStep 68186891 = 102280337) B102280337
theorem B4325339 : Blo 299831 4325339 := bstep (se 1 (by rfl) ⟨3244004, by rfl⟩ : syracuseStep 4325339 = 6488009) B6488009
theorem B1016873 : Blo 299831 1016873 := bstep (se 2 (by rfl) ⟨381327, by rfl⟩ : syracuseStep 1016873 = 762655) B762655
theorem B181831709 : Blo 299831 181831709 := bstep (se 3 (by rfl) ⟨34093445, by rfl⟩ : syracuseStep 181831709 = 68186891) B68186891
theorem B301215 : Blo 299831 301215 := bstep (se 1 (by rfl) ⟨225911, by rfl⟩ : syracuseStep 301215 = 451823) B451823
theorem B454511 : Blo 299831 454511 := bstep (se 1 (by rfl) ⟨340883, by rfl⟩ : syracuseStep 454511 = 681767) B681767
theorem B3439421 : Blo 299831 3439421 := bstep (se 3 (by rfl) ⟨644891, by rfl⟩ : syracuseStep 3439421 = 1289783) B1289783
theorem B1539803 : Blo 299831 1539803 := bstep (se 1 (by rfl) ⟨1154852, by rfl⟩ : syracuseStep 1539803 = 2309705) B2309705
theorem B11534237 : Blo 299831 11534237 := bstep (se 3 (by rfl) ⟨2162669, by rfl⟩ : syracuseStep 11534237 = 4325339) B4325339
theorem B303007 : Blo 299831 303007 := bstep (se 1 (by rfl) ⟨227255, by rfl⟩ : syracuseStep 303007 = 454511) B454511
theorem B1026535 : Blo 299831 1026535 := bstep (se 1 (by rfl) ⟨769901, by rfl⟩ : syracuseStep 1026535 = 1539803) B1539803
theorem B121221139 : Blo 299831 121221139 := bstep (se 1 (by rfl) ⟨90915854, by rfl⟩ : syracuseStep 121221139 = 181831709) B181831709
theorem B7689491 : Blo 299831 7689491 := bstep (se 1 (by rfl) ⟨5767118, by rfl⟩ : syracuseStep 7689491 = 11534237) B11534237
theorem B677915 : Blo 299831 677915 := bstep (se 1 (by rfl) ⟨508436, by rfl⟩ : syracuseStep 677915 = 1016873) B1016873
theorem B2292947 : Blo 299831 2292947 := bstep (se 1 (by rfl) ⟨1719710, by rfl⟩ : syracuseStep 2292947 = 3439421) B3439421
theorem B5126327 : Blo 299831 5126327 := bstep (se 1 (by rfl) ⟨3844745, by rfl⟩ : syracuseStep 5126327 = 7689491) B7689491
theorem B161628185 : Blo 299831 161628185 := bstep (se 2 (by rfl) ⟨60610569, by rfl⟩ : syracuseStep 161628185 = 121221139) B121221139
theorem B1528631 : Blo 299831 1528631 := bstep (se 1 (by rfl) ⟨1146473, by rfl⟩ : syracuseStep 1528631 = 2292947) B2292947
theorem B1368713 : Blo 299831 1368713 := bstep (se 2 (by rfl) ⟨513267, by rfl⟩ : syracuseStep 1368713 = 1026535) B1026535
theorem B451943 : Blo 299831 451943 := bstep (se 1 (by rfl) ⟨338957, by rfl⟩ : syracuseStep 451943 = 677915) B677915
theorem B1019087 : Blo 299831 1019087 := bstep (se 1 (by rfl) ⟨764315, by rfl⟩ : syracuseStep 1019087 = 1528631) B1528631
theorem B301295 : Blo 299831 301295 := bstep (se 1 (by rfl) ⟨225971, by rfl⟩ : syracuseStep 301295 = 451943) B451943
theorem B3417551 : Blo 299831 3417551 := bstep (se 1 (by rfl) ⟨2563163, by rfl⟩ : syracuseStep 3417551 = 5126327) B5126327
theorem B107752123 : Blo 299831 107752123 := bstep (se 1 (by rfl) ⟨80814092, by rfl⟩ : syracuseStep 107752123 = 161628185) B161628185
theorem B912475 : Blo 299831 912475 := bstep (se 1 (by rfl) ⟨684356, by rfl⟩ : syracuseStep 912475 = 1368713) B1368713
theorem B1216633 : Blo 299831 1216633 := bstep (se 2 (by rfl) ⟨456237, by rfl⟩ : syracuseStep 1216633 = 912475) B912475
theorem B143669497 : Blo 299831 143669497 := bstep (se 2 (by rfl) ⟨53876061, by rfl⟩ : syracuseStep 143669497 = 107752123) B107752123
theorem B2278367 : Blo 299831 2278367 := bstep (se 1 (by rfl) ⟨1708775, by rfl⟩ : syracuseStep 2278367 = 3417551) B3417551
theorem B679391 : Blo 299831 679391 := bstep (se 1 (by rfl) ⟨509543, by rfl⟩ : syracuseStep 679391 = 1019087) B1019087
theorem B1518911 : Blo 299831 1518911 := bstep (se 1 (by rfl) ⟨1139183, by rfl⟩ : syracuseStep 1518911 = 2278367) B2278367
theorem B1622177 : Blo 299831 1622177 := bstep (se 2 (by rfl) ⟨608316, by rfl⟩ : syracuseStep 1622177 = 1216633) B1216633
theorem B452927 : Blo 299831 452927 := bstep (se 1 (by rfl) ⟨339695, by rfl⟩ : syracuseStep 452927 = 679391) B679391
theorem B191559329 : Blo 299831 191559329 := bstep (se 2 (by rfl) ⟨71834748, by rfl⟩ : syracuseStep 191559329 = 143669497) B143669497
theorem B1081451 : Blo 299831 1081451 := bstep (se 1 (by rfl) ⟨811088, by rfl⟩ : syracuseStep 1081451 = 1622177) B1622177
theorem B301951 : Blo 299831 301951 := bstep (se 1 (by rfl) ⟨226463, by rfl⟩ : syracuseStep 301951 = 452927) B452927
theorem B127706219 : Blo 299831 127706219 := bstep (se 1 (by rfl) ⟨95779664, by rfl⟩ : syracuseStep 127706219 = 191559329) B191559329
theorem B1012607 : Blo 299831 1012607 := bstep (se 1 (by rfl) ⟨759455, by rfl⟩ : syracuseStep 1012607 = 1518911) B1518911
theorem B2883869 : Blo 299831 2883869 := bstep (se 3 (by rfl) ⟨540725, by rfl⟩ : syracuseStep 2883869 = 1081451) B1081451
theorem B85137479 : Blo 299831 85137479 := bstep (se 1 (by rfl) ⟨63853109, by rfl⟩ : syracuseStep 85137479 = 127706219) B127706219
theorem B675071 : Blo 299831 675071 := bstep (se 1 (by rfl) ⟨506303, by rfl⟩ : syracuseStep 675071 = 1012607) B1012607
theorem B56758319 : Blo 299831 56758319 := bstep (se 1 (by rfl) ⟨42568739, by rfl⟩ : syracuseStep 56758319 = 85137479) B85137479
theorem B1922579 : Blo 299831 1922579 := bstep (se 1 (by rfl) ⟨1441934, by rfl⟩ : syracuseStep 1922579 = 2883869) B2883869
theorem B450047 : Blo 299831 450047 := bstep (se 1 (by rfl) ⟨337535, by rfl⟩ : syracuseStep 450047 = 675071) B675071
theorem B1281719 : Blo 299831 1281719 := bstep (se 1 (by rfl) ⟨961289, by rfl⟩ : syracuseStep 1281719 = 1922579) B1922579
theorem B300031 : Blo 299831 300031 := bstep (se 1 (by rfl) ⟨225023, by rfl⟩ : syracuseStep 300031 = 450047) B450047
theorem B37838879 : Blo 299831 37838879 := bstep (se 1 (by rfl) ⟨28379159, by rfl⟩ : syracuseStep 37838879 = 56758319) B56758319
theorem B854479 : Blo 299831 854479 := bstep (se 1 (by rfl) ⟨640859, by rfl⟩ : syracuseStep 854479 = 1281719) B1281719
theorem B25225919 : Blo 299831 25225919 := bstep (se 1 (by rfl) ⟨18919439, by rfl⟩ : syracuseStep 25225919 = 37838879) B37838879
theorem B16817279 : Blo 299831 16817279 := bstep (se 1 (by rfl) ⟨12612959, by rfl⟩ : syracuseStep 16817279 = 25225919) B25225919
theorem B1139305 : Blo 299831 1139305 := bstep (se 2 (by rfl) ⟨427239, by rfl⟩ : syracuseStep 1139305 = 854479) B854479
theorem B1519073 : Blo 299831 1519073 := bstep (se 2 (by rfl) ⟨569652, by rfl⟩ : syracuseStep 1519073 = 1139305) B1139305
theorem B44846077 : Blo 299831 44846077 := bstep (se 3 (by rfl) ⟨8408639, by rfl⟩ : syracuseStep 44846077 = 16817279) B16817279
theorem B59794769 : Blo 299831 59794769 := bstep (se 2 (by rfl) ⟨22423038, by rfl⟩ : syracuseStep 59794769 = 44846077) B44846077
theorem B1012715 : Blo 299831 1012715 := bstep (se 1 (by rfl) ⟨759536, by rfl⟩ : syracuseStep 1012715 = 1519073) B1519073
theorem B39863179 : Blo 299831 39863179 := bstep (se 1 (by rfl) ⟨29897384, by rfl⟩ : syracuseStep 39863179 = 59794769) B59794769
theorem B675143 : Blo 299831 675143 := bstep (se 1 (by rfl) ⟨506357, by rfl⟩ : syracuseStep 675143 = 1012715) B1012715
theorem B53150905 : Blo 299831 53150905 := bstep (se 2 (by rfl) ⟨19931589, by rfl⟩ : syracuseStep 53150905 = 39863179) B39863179
theorem B450095 : Blo 299831 450095 := bstep (se 1 (by rfl) ⟨337571, by rfl⟩ : syracuseStep 450095 = 675143) B675143
theorem B300063 : Blo 299831 300063 := bstep (se 1 (by rfl) ⟨225047, by rfl⟩ : syracuseStep 300063 = 450095) B450095
theorem B70867873 : Blo 299831 70867873 := bstep (se 2 (by rfl) ⟨26575452, by rfl⟩ : syracuseStep 70867873 = 53150905) B53150905
theorem B94490497 : Blo 299831 94490497 := bstep (se 2 (by rfl) ⟨35433936, by rfl⟩ : syracuseStep 94490497 = 70867873) B70867873
theorem B125987329 : Blo 299831 125987329 := bstep (se 2 (by rfl) ⟨47245248, by rfl⟩ : syracuseStep 125987329 = 94490497) B94490497
theorem B167983105 : Blo 299831 167983105 := bstep (se 2 (by rfl) ⟨62993664, by rfl⟩ : syracuseStep 167983105 = 125987329) B125987329
theorem B223977473 : Blo 299831 223977473 := bstep (se 2 (by rfl) ⟨83991552, by rfl⟩ : syracuseStep 223977473 = 167983105) B167983105
theorem B149318315 : Blo 299831 149318315 := bstep (se 1 (by rfl) ⟨111988736, by rfl⟩ : syracuseStep 149318315 = 223977473) B223977473
theorem B99545543 : Blo 299831 99545543 := bstep (se 1 (by rfl) ⟨74659157, by rfl⟩ : syracuseStep 99545543 = 149318315) B149318315
theorem B66363695 : Blo 299831 66363695 := bstep (se 1 (by rfl) ⟨49772771, by rfl⟩ : syracuseStep 66363695 = 99545543) B99545543
theorem B44242463 : Blo 299831 44242463 := bstep (se 1 (by rfl) ⟨33181847, by rfl⟩ : syracuseStep 44242463 = 66363695) B66363695
theorem B29494975 : Blo 299831 29494975 := bstep (se 1 (by rfl) ⟨22121231, by rfl⟩ : syracuseStep 29494975 = 44242463) B44242463
theorem B39326633 : Blo 299831 39326633 := bstep (se 2 (by rfl) ⟨14747487, by rfl⟩ : syracuseStep 39326633 = 29494975) B29494975
theorem B26217755 : Blo 299831 26217755 := bstep (se 1 (by rfl) ⟨19663316, by rfl⟩ : syracuseStep 26217755 = 39326633) B39326633
theorem B17478503 : Blo 299831 17478503 := bstep (se 1 (by rfl) ⟨13108877, by rfl⟩ : syracuseStep 17478503 = 26217755) B26217755
theorem B11652335 : Blo 299831 11652335 := bstep (se 1 (by rfl) ⟨8739251, by rfl⟩ : syracuseStep 11652335 = 17478503) B17478503
theorem B7768223 : Blo 299831 7768223 := bstep (se 1 (by rfl) ⟨5826167, by rfl⟩ : syracuseStep 7768223 = 11652335) B11652335
theorem B5178815 : Blo 299831 5178815 := bstep (se 1 (by rfl) ⟨3884111, by rfl⟩ : syracuseStep 5178815 = 7768223) B7768223
theorem B3452543 : Blo 299831 3452543 := bstep (se 1 (by rfl) ⟨2589407, by rfl⟩ : syracuseStep 3452543 = 5178815) B5178815
theorem B2301695 : Blo 299831 2301695 := bstep (se 1 (by rfl) ⟨1726271, by rfl⟩ : syracuseStep 2301695 = 3452543) B3452543
theorem B1534463 : Blo 299831 1534463 := bstep (se 1 (by rfl) ⟨1150847, by rfl⟩ : syracuseStep 1534463 = 2301695) B2301695
theorem B1022975 : Blo 299831 1022975 := bstep (se 1 (by rfl) ⟨767231, by rfl⟩ : syracuseStep 1022975 = 1534463) B1534463
theorem B681983 : Blo 299831 681983 := bstep (se 1 (by rfl) ⟨511487, by rfl⟩ : syracuseStep 681983 = 1022975) B1022975
theorem B454655 : Blo 299831 454655 := bstep (se 1 (by rfl) ⟨340991, by rfl⟩ : syracuseStep 454655 = 681983) B681983
theorem B303103 : Blo 299831 303103 := bstep (se 1 (by rfl) ⟨227327, by rfl⟩ : syracuseStep 303103 = 454655) B454655

theorem C0 (j : ℕ) (h1 : 74957 ≤ j) (h2 : j ≤ 75656) : Blo 299831 (4 * j + 3) := by
  interval_cases j
  · exact B299831
  · exact B299835
  · exact B299839
  · exact B299843
  · exact B299847
  · exact B299851
  · exact B299855
  · exact B299859
  · exact B299863
  · exact B299867
  · exact B299871
  · exact B299875
  · exact B299879
  · exact B299883
  · exact B299887
  · exact B299891
  · exact B299895
  · exact B299899
  · exact B299903
  · exact B299907
  · exact B299911
  · exact B299915
  · exact B299919
  · exact B299923
  · exact B299927
  · exact B299931
  · exact B299935
  · exact B299939
  · exact B299943
  · exact B299947
  · exact B299951
  · exact B299955
  · exact B299959
  · exact B299963
  · exact B299967
  · exact B299971
  · exact B299975
  · exact B299979
  · exact B299983
  · exact B299987
  · exact B299991
  · exact B299995
  · exact B299999
  · exact B300003
  · exact B300007
  · exact B300011
  · exact B300015
  · exact B300019
  · exact B300023
  · exact B300027
  · exact B300031
  · exact B300035
  · exact B300039
  · exact B300043
  · exact B300047
  · exact B300051
  · exact B300055
  · exact B300059
  · exact B300063
  · exact B300067
  · exact B300071
  · exact B300075
  · exact B300079
  · exact B300083
  · exact B300087
  · exact B300091
  · exact B300095
  · exact B300099
  · exact B300103
  · exact B300107
  · exact B300111
  · exact B300115
  · exact B300119
  · exact B300123
  · exact B300127
  · exact B300131
  · exact B300135
  · exact B300139
  · exact B300143
  · exact B300147
  · exact B300151
  · exact B300155
  · exact B300159
  · exact B300163
  · exact B300167
  · exact B300171
  · exact B300175
  · exact B300179
  · exact B300183
  · exact B300187
  · exact B300191
  · exact B300195
  · exact B300199
  · exact B300203
  · exact B300207
  · exact B300211
  · exact B300215
  · exact B300219
  · exact B300223
  · exact B300227
  · exact B300231
  · exact B300235
  · exact B300239
  · exact B300243
  · exact B300247
  · exact B300251
  · exact B300255
  · exact B300259
  · exact B300263
  · exact B300267
  · exact B300271
  · exact B300275
  · exact B300279
  · exact B300283
  · exact B300287
  · exact B300291
  · exact B300295
  · exact B300299
  · exact B300303
  · exact B300307
  · exact B300311
  · exact B300315
  · exact B300319
  · exact B300323
  · exact B300327
  · exact B300331
  · exact B300335
  · exact B300339
  · exact B300343
  · exact B300347
  · exact B300351
  · exact B300355
  · exact B300359
  · exact B300363
  · exact B300367
  · exact B300371
  · exact B300375
  · exact B300379
  · exact B300383
  · exact B300387
  · exact B300391
  · exact B300395
  · exact B300399
  · exact B300403
  · exact B300407
  · exact B300411
  · exact B300415
  · exact B300419
  · exact B300423
  · exact B300427
  · exact B300431
  · exact B300435
  · exact B300439
  · exact B300443
  · exact B300447
  · exact B300451
  · exact B300455
  · exact B300459
  · exact B300463
  · exact B300467
  · exact B300471
  · exact B300475
  · exact B300479
  · exact B300483
  · exact B300487
  · exact B300491
  · exact B300495
  · exact B300499
  · exact B300503
  · exact B300507
  · exact B300511
  · exact B300515
  · exact B300519
  · exact B300523
  · exact B300527
  · exact B300531
  · exact B300535
  · exact B300539
  · exact B300543
  · exact B300547
  · exact B300551
  · exact B300555
  · exact B300559
  · exact B300563
  · exact B300567
  · exact B300571
  · exact B300575
  · exact B300579
  · exact B300583
  · exact B300587
  · exact B300591
  · exact B300595
  · exact B300599
  · exact B300603
  · exact B300607
  · exact B300611
  · exact B300615
  · exact B300619
  · exact B300623
  · exact B300627
  · exact B300631
  · exact B300635
  · exact B300639
  · exact B300643
  · exact B300647
  · exact B300651
  · exact B300655
  · exact B300659
  · exact B300663
  · exact B300667
  · exact B300671
  · exact B300675
  · exact B300679
  · exact B300683
  · exact B300687
  · exact B300691
  · exact B300695
  · exact B300699
  · exact B300703
  · exact B300707
  · exact B300711
  · exact B300715
  · exact B300719
  · exact B300723
  · exact B300727
  · exact B300731
  · exact B300735
  · exact B300739
  · exact B300743
  · exact B300747
  · exact B300751
  · exact B300755
  · exact B300759
  · exact B300763
  · exact B300767
  · exact B300771
  · exact B300775
  · exact B300779
  · exact B300783
  · exact B300787
  · exact B300791
  · exact B300795
  · exact B300799
  · exact B300803
  · exact B300807
  · exact B300811
  · exact B300815
  · exact B300819
  · exact B300823
  · exact B300827
  · exact B300831
  · exact B300835
  · exact B300839
  · exact B300843
  · exact B300847
  · exact B300851
  · exact B300855
  · exact B300859
  · exact B300863
  · exact B300867
  · exact B300871
  · exact B300875
  · exact B300879
  · exact B300883
  · exact B300887
  · exact B300891
  · exact B300895
  · exact B300899
  · exact B300903
  · exact B300907
  · exact B300911
  · exact B300915
  · exact B300919
  · exact B300923
  · exact B300927
  · exact B300931
  · exact B300935
  · exact B300939
  · exact B300943
  · exact B300947
  · exact B300951
  · exact B300955
  · exact B300959
  · exact B300963
  · exact B300967
  · exact B300971
  · exact B300975
  · exact B300979
  · exact B300983
  · exact B300987
  · exact B300991
  · exact B300995
  · exact B300999
  · exact B301003
  · exact B301007
  · exact B301011
  · exact B301015
  · exact B301019
  · exact B301023
  · exact B301027
  · exact B301031
  · exact B301035
  · exact B301039
  · exact B301043
  · exact B301047
  · exact B301051
  · exact B301055
  · exact B301059
  · exact B301063
  · exact B301067
  · exact B301071
  · exact B301075
  · exact B301079
  · exact B301083
  · exact B301087
  · exact B301091
  · exact B301095
  · exact B301099
  · exact B301103
  · exact B301107
  · exact B301111
  · exact B301115
  · exact B301119
  · exact B301123
  · exact B301127
  · exact B301131
  · exact B301135
  · exact B301139
  · exact B301143
  · exact B301147
  · exact B301151
  · exact B301155
  · exact B301159
  · exact B301163
  · exact B301167
  · exact B301171
  · exact B301175
  · exact B301179
  · exact B301183
  · exact B301187
  · exact B301191
  · exact B301195
  · exact B301199
  · exact B301203
  · exact B301207
  · exact B301211
  · exact B301215
  · exact B301219
  · exact B301223
  · exact B301227
  · exact B301231
  · exact B301235
  · exact B301239
  · exact B301243
  · exact B301247
  · exact B301251
  · exact B301255
  · exact B301259
  · exact B301263
  · exact B301267
  · exact B301271
  · exact B301275
  · exact B301279
  · exact B301283
  · exact B301287
  · exact B301291
  · exact B301295
  · exact B301299
  · exact B301303
  · exact B301307
  · exact B301311
  · exact B301315
  · exact B301319
  · exact B301323
  · exact B301327
  · exact B301331
  · exact B301335
  · exact B301339
  · exact B301343
  · exact B301347
  · exact B301351
  · exact B301355
  · exact B301359
  · exact B301363
  · exact B301367
  · exact B301371
  · exact B301375
  · exact B301379
  · exact B301383
  · exact B301387
  · exact B301391
  · exact B301395
  · exact B301399
  · exact B301403
  · exact B301407
  · exact B301411
  · exact B301415
  · exact B301419
  · exact B301423
  · exact B301427
  · exact B301431
  · exact B301435
  · exact B301439
  · exact B301443
  · exact B301447
  · exact B301451
  · exact B301455
  · exact B301459
  · exact B301463
  · exact B301467
  · exact B301471
  · exact B301475
  · exact B301479
  · exact B301483
  · exact B301487
  · exact B301491
  · exact B301495
  · exact B301499
  · exact B301503
  · exact B301507
  · exact B301511
  · exact B301515
  · exact B301519
  · exact B301523
  · exact B301527
  · exact B301531
  · exact B301535
  · exact B301539
  · exact B301543
  · exact B301547
  · exact B301551
  · exact B301555
  · exact B301559
  · exact B301563
  · exact B301567
  · exact B301571
  · exact B301575
  · exact B301579
  · exact B301583
  · exact B301587
  · exact B301591
  · exact B301595
  · exact B301599
  · exact B301603
  · exact B301607
  · exact B301611
  · exact B301615
  · exact B301619
  · exact B301623
  · exact B301627
  · exact B301631
  · exact B301635
  · exact B301639
  · exact B301643
  · exact B301647
  · exact B301651
  · exact B301655
  · exact B301659
  · exact B301663
  · exact B301667
  · exact B301671
  · exact B301675
  · exact B301679
  · exact B301683
  · exact B301687
  · exact B301691
  · exact B301695
  · exact B301699
  · exact B301703
  · exact B301707
  · exact B301711
  · exact B301715
  · exact B301719
  · exact B301723
  · exact B301727
  · exact B301731
  · exact B301735
  · exact B301739
  · exact B301743
  · exact B301747
  · exact B301751
  · exact B301755
  · exact B301759
  · exact B301763
  · exact B301767
  · exact B301771
  · exact B301775
  · exact B301779
  · exact B301783
  · exact B301787
  · exact B301791
  · exact B301795
  · exact B301799
  · exact B301803
  · exact B301807
  · exact B301811
  · exact B301815
  · exact B301819
  · exact B301823
  · exact B301827
  · exact B301831
  · exact B301835
  · exact B301839
  · exact B301843
  · exact B301847
  · exact B301851
  · exact B301855
  · exact B301859
  · exact B301863
  · exact B301867
  · exact B301871
  · exact B301875
  · exact B301879
  · exact B301883
  · exact B301887
  · exact B301891
  · exact B301895
  · exact B301899
  · exact B301903
  · exact B301907
  · exact B301911
  · exact B301915
  · exact B301919
  · exact B301923
  · exact B301927
  · exact B301931
  · exact B301935
  · exact B301939
  · exact B301943
  · exact B301947
  · exact B301951
  · exact B301955
  · exact B301959
  · exact B301963
  · exact B301967
  · exact B301971
  · exact B301975
  · exact B301979
  · exact B301983
  · exact B301987
  · exact B301991
  · exact B301995
  · exact B301999
  · exact B302003
  · exact B302007
  · exact B302011
  · exact B302015
  · exact B302019
  · exact B302023
  · exact B302027
  · exact B302031
  · exact B302035
  · exact B302039
  · exact B302043
  · exact B302047
  · exact B302051
  · exact B302055
  · exact B302059
  · exact B302063
  · exact B302067
  · exact B302071
  · exact B302075
  · exact B302079
  · exact B302083
  · exact B302087
  · exact B302091
  · exact B302095
  · exact B302099
  · exact B302103
  · exact B302107
  · exact B302111
  · exact B302115
  · exact B302119
  · exact B302123
  · exact B302127
  · exact B302131
  · exact B302135
  · exact B302139
  · exact B302143
  · exact B302147
  · exact B302151
  · exact B302155
  · exact B302159
  · exact B302163
  · exact B302167
  · exact B302171
  · exact B302175
  · exact B302179
  · exact B302183
  · exact B302187
  · exact B302191
  · exact B302195
  · exact B302199
  · exact B302203
  · exact B302207
  · exact B302211
  · exact B302215
  · exact B302219
  · exact B302223
  · exact B302227
  · exact B302231
  · exact B302235
  · exact B302239
  · exact B302243
  · exact B302247
  · exact B302251
  · exact B302255
  · exact B302259
  · exact B302263
  · exact B302267
  · exact B302271
  · exact B302275
  · exact B302279
  · exact B302283
  · exact B302287
  · exact B302291
  · exact B302295
  · exact B302299
  · exact B302303
  · exact B302307
  · exact B302311
  · exact B302315
  · exact B302319
  · exact B302323
  · exact B302327
  · exact B302331
  · exact B302335
  · exact B302339
  · exact B302343
  · exact B302347
  · exact B302351
  · exact B302355
  · exact B302359
  · exact B302363
  · exact B302367
  · exact B302371
  · exact B302375
  · exact B302379
  · exact B302383
  · exact B302387
  · exact B302391
  · exact B302395
  · exact B302399
  · exact B302403
  · exact B302407
  · exact B302411
  · exact B302415
  · exact B302419
  · exact B302423
  · exact B302427
  · exact B302431
  · exact B302435
  · exact B302439
  · exact B302443
  · exact B302447
  · exact B302451
  · exact B302455
  · exact B302459
  · exact B302463
  · exact B302467
  · exact B302471
  · exact B302475
  · exact B302479
  · exact B302483
  · exact B302487
  · exact B302491
  · exact B302495
  · exact B302499
  · exact B302503
  · exact B302507
  · exact B302511
  · exact B302515
  · exact B302519
  · exact B302523
  · exact B302527
  · exact B302531
  · exact B302535
  · exact B302539
  · exact B302543
  · exact B302547
  · exact B302551
  · exact B302555
  · exact B302559
  · exact B302563
  · exact B302567
  · exact B302571
  · exact B302575
  · exact B302579
  · exact B302583
  · exact B302587
  · exact B302591
  · exact B302595
  · exact B302599
  · exact B302603
  · exact B302607
  · exact B302611
  · exact B302615
  · exact B302619
  · exact B302623
  · exact B302627

theorem C1 (j : ℕ) (h1 : 75657 ≤ j) (h2 : j ≤ 75957) : Blo 299831 (4 * j + 3) := by
  interval_cases j
  · exact B302631
  · exact B302635
  · exact B302639
  · exact B302643
  · exact B302647
  · exact B302651
  · exact B302655
  · exact B302659
  · exact B302663
  · exact B302667
  · exact B302671
  · exact B302675
  · exact B302679
  · exact B302683
  · exact B302687
  · exact B302691
  · exact B302695
  · exact B302699
  · exact B302703
  · exact B302707
  · exact B302711
  · exact B302715
  · exact B302719
  · exact B302723
  · exact B302727
  · exact B302731
  · exact B302735
  · exact B302739
  · exact B302743
  · exact B302747
  · exact B302751
  · exact B302755
  · exact B302759
  · exact B302763
  · exact B302767
  · exact B302771
  · exact B302775
  · exact B302779
  · exact B302783
  · exact B302787
  · exact B302791
  · exact B302795
  · exact B302799
  · exact B302803
  · exact B302807
  · exact B302811
  · exact B302815
  · exact B302819
  · exact B302823
  · exact B302827
  · exact B302831
  · exact B302835
  · exact B302839
  · exact B302843
  · exact B302847
  · exact B302851
  · exact B302855
  · exact B302859
  · exact B302863
  · exact B302867
  · exact B302871
  · exact B302875
  · exact B302879
  · exact B302883
  · exact B302887
  · exact B302891
  · exact B302895
  · exact B302899
  · exact B302903
  · exact B302907
  · exact B302911
  · exact B302915
  · exact B302919
  · exact B302923
  · exact B302927
  · exact B302931
  · exact B302935
  · exact B302939
  · exact B302943
  · exact B302947
  · exact B302951
  · exact B302955
  · exact B302959
  · exact B302963
  · exact B302967
  · exact B302971
  · exact B302975
  · exact B302979
  · exact B302983
  · exact B302987
  · exact B302991
  · exact B302995
  · exact B302999
  · exact B303003
  · exact B303007
  · exact B303011
  · exact B303015
  · exact B303019
  · exact B303023
  · exact B303027
  · exact B303031
  · exact B303035
  · exact B303039
  · exact B303043
  · exact B303047
  · exact B303051
  · exact B303055
  · exact B303059
  · exact B303063
  · exact B303067
  · exact B303071
  · exact B303075
  · exact B303079
  · exact B303083
  · exact B303087
  · exact B303091
  · exact B303095
  · exact B303099
  · exact B303103
  · exact B303107
  · exact B303111
  · exact B303115
  · exact B303119
  · exact B303123
  · exact B303127
  · exact B303131
  · exact B303135
  · exact B303139
  · exact B303143
  · exact B303147
  · exact B303151
  · exact B303155
  · exact B303159
  · exact B303163
  · exact B303167
  · exact B303171
  · exact B303175
  · exact B303179
  · exact B303183
  · exact B303187
  · exact B303191
  · exact B303195
  · exact B303199
  · exact B303203
  · exact B303207
  · exact B303211
  · exact B303215
  · exact B303219
  · exact B303223
  · exact B303227
  · exact B303231
  · exact B303235
  · exact B303239
  · exact B303243
  · exact B303247
  · exact B303251
  · exact B303255
  · exact B303259
  · exact B303263
  · exact B303267
  · exact B303271
  · exact B303275
  · exact B303279
  · exact B303283
  · exact B303287
  · exact B303291
  · exact B303295
  · exact B303299
  · exact B303303
  · exact B303307
  · exact B303311
  · exact B303315
  · exact B303319
  · exact B303323
  · exact B303327
  · exact B303331
  · exact B303335
  · exact B303339
  · exact B303343
  · exact B303347
  · exact B303351
  · exact B303355
  · exact B303359
  · exact B303363
  · exact B303367
  · exact B303371
  · exact B303375
  · exact B303379
  · exact B303383
  · exact B303387
  · exact B303391
  · exact B303395
  · exact B303399
  · exact B303403
  · exact B303407
  · exact B303411
  · exact B303415
  · exact B303419
  · exact B303423
  · exact B303427
  · exact B303431
  · exact B303435
  · exact B303439
  · exact B303443
  · exact B303447
  · exact B303451
  · exact B303455
  · exact B303459
  · exact B303463
  · exact B303467
  · exact B303471
  · exact B303475
  · exact B303479
  · exact B303483
  · exact B303487
  · exact B303491
  · exact B303495
  · exact B303499
  · exact B303503
  · exact B303507
  · exact B303511
  · exact B303515
  · exact B303519
  · exact B303523
  · exact B303527
  · exact B303531
  · exact B303535
  · exact B303539
  · exact B303543
  · exact B303547
  · exact B303551
  · exact B303555
  · exact B303559
  · exact B303563
  · exact B303567
  · exact B303571
  · exact B303575
  · exact B303579
  · exact B303583
  · exact B303587
  · exact B303591
  · exact B303595
  · exact B303599
  · exact B303603
  · exact B303607
  · exact B303611
  · exact B303615
  · exact B303619
  · exact B303623
  · exact B303627
  · exact B303631
  · exact B303635
  · exact B303639
  · exact B303643
  · exact B303647
  · exact B303651
  · exact B303655
  · exact B303659
  · exact B303663
  · exact B303667
  · exact B303671
  · exact B303675
  · exact B303679
  · exact B303683
  · exact B303687
  · exact B303691
  · exact B303695
  · exact B303699
  · exact B303703
  · exact B303707
  · exact B303711
  · exact B303715
  · exact B303719
  · exact B303723
  · exact B303727
  · exact B303731
  · exact B303735
  · exact B303739
  · exact B303743
  · exact B303747
  · exact B303751
  · exact B303755
  · exact B303759
  · exact B303763
  · exact B303767
  · exact B303771
  · exact B303775
  · exact B303779
  · exact B303783
  · exact B303787
  · exact B303791
  · exact B303795
  · exact B303799
  · exact B303803
  · exact B303807
  · exact B303811
  · exact B303815
  · exact B303819
  · exact B303823
  · exact B303827
  · exact B303831

theorem solution (m : ℕ) (hlo : 299831 ≤ m) (hhi : m ≤ 303831) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 74957 ≤ j := by omega
    have hj2 : j ≤ 75957 := by omega
    have hb : Blo 299831 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 75657 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
