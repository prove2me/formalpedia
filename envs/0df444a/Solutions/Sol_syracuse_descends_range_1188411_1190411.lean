-- Prove2me | solution 1 for syracuse_descends_range_1188411_1190411
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:10:37.328178+00:00
-- url     : https://prove2.me/submissions/97ad52f3-743b-4fc7-bb2b-82ef22710f6b

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


theorem B1269793 : Blo 1188411 1269793 := bbase (se 2 (by rfl) ⟨476172, by rfl⟩ : syracuseStep 1269793 = 952345) (by norm_num)
theorem B2007085 : Blo 1188411 2007085 := bbase (se 3 (by rfl) ⟨376328, by rfl⟩ : syracuseStep 2007085 = 752657) (by norm_num)
theorem B4513877 : Blo 1188411 4513877 := bbase (se 8 (by rfl) ⟨26448, by rfl⟩ : syracuseStep 4513877 = 52897) (by norm_num)
theorem B4014197 : Blo 1188411 4014197 := bbase (se 5 (by rfl) ⟨188165, by rfl⟩ : syracuseStep 4014197 = 376331) (by norm_num)
theorem B2007173 : Blo 1188411 2007173 := bbase (se 4 (by rfl) ⟨188172, by rfl⟩ : syracuseStep 2007173 = 376345) (by norm_num)
theorem B2539757 : Blo 1188411 2539757 := bbase (se 3 (by rfl) ⟨476204, by rfl⟩ : syracuseStep 2539757 = 952409) (by norm_num)
theorem B2007301 : Blo 1188411 2007301 := bbase (se 4 (by rfl) ⟨188184, by rfl⟩ : syracuseStep 2007301 = 376369) (by norm_num)
theorem B7627061 : Blo 1188411 7627061 := bbase (se 5 (by rfl) ⟨357518, by rfl⟩ : syracuseStep 7627061 = 715037) (by norm_num)
theorem B2007389 : Blo 1188411 2007389 := bbase (se 3 (by rfl) ⟨376385, by rfl⟩ : syracuseStep 2007389 = 752771) (by norm_num)
theorem B2007517 : Blo 1188411 2007517 := bbase (se 3 (by rfl) ⟨376409, by rfl⟩ : syracuseStep 2007517 = 752819) (by norm_num)
theorem B4014629 : Blo 1188411 4014629 := bbase (se 4 (by rfl) ⟨376371, by rfl⟩ : syracuseStep 4014629 = 752743) (by norm_num)
theorem B2007605 : Blo 1188411 2007605 := bbase (se 5 (by rfl) ⟨94106, by rfl⟩ : syracuseStep 2007605 = 188213) (by norm_num)
theorem B6021701 : Blo 1188411 6021701 := bbase (se 4 (by rfl) ⟨564534, by rfl⟩ : syracuseStep 6021701 = 1129069) (by norm_num)
theorem B2007733 : Blo 1188411 2007733 := bbase (se 5 (by rfl) ⟨94112, by rfl⟩ : syracuseStep 2007733 = 188225) (by norm_num)
theorem B2859725 : Blo 1188411 2859725 := bbase (se 3 (by rfl) ⟨536198, by rfl⟩ : syracuseStep 2859725 = 1072397) (by norm_num)
theorem B2540261 : Blo 1188411 2540261 := bbase (se 4 (by rfl) ⟨238149, by rfl⟩ : syracuseStep 2540261 = 476299) (by norm_num)
theorem B2540269 : Blo 1188411 2540269 := bbase (se 3 (by rfl) ⟨476300, by rfl⟩ : syracuseStep 2540269 = 952601) (by norm_num)
theorem B2171653 : Blo 1188411 2171653 := bbase (se 4 (by rfl) ⟨203592, by rfl⟩ : syracuseStep 2171653 = 407185) (by norm_num)
theorem B2007821 : Blo 1188411 2007821 := bbase (se 3 (by rfl) ⟨376466, by rfl⟩ : syracuseStep 2007821 = 752933) (by norm_num)
theorem B4285205 : Blo 1188411 4285205 := bbase (se 6 (by rfl) ⟨100434, by rfl⟩ : syracuseStep 4285205 = 200869) (by norm_num)
theorem B1606429 : Blo 1188411 1606429 := bbase (se 3 (by rfl) ⟨301205, by rfl⟩ : syracuseStep 1606429 = 602411) (by norm_num)
theorem B1270613 : Blo 1188411 1270613 := bbase (se 9 (by rfl) ⟨3722, by rfl⟩ : syracuseStep 1270613 = 7445) (by norm_num)
theorem B3810149 : Blo 1188411 3810149 := bbase (se 4 (by rfl) ⟨357201, by rfl⟩ : syracuseStep 3810149 = 714403) (by norm_num)
theorem B2007949 : Blo 1188411 2007949 := bbase (se 3 (by rfl) ⟨376490, by rfl⟩ : syracuseStep 2007949 = 752981) (by norm_num)
theorem B4015061 : Blo 1188411 4015061 := bbase (se 7 (by rfl) ⟨47051, by rfl⟩ : syracuseStep 4015061 = 94103) (by norm_num)
theorem B2008037 : Blo 1188411 2008037 := bbase (se 4 (by rfl) ⟨188253, by rfl⟩ : syracuseStep 2008037 = 376507) (by norm_num)
theorem B2008165 : Blo 1188411 2008165 := bbase (se 4 (by rfl) ⟨188265, by rfl⟩ : syracuseStep 2008165 = 376531) (by norm_num)
theorem B2008253 : Blo 1188411 2008253 := bbase (se 3 (by rfl) ⟨376547, by rfl⟩ : syracuseStep 2008253 = 753095) (by norm_num)
theorem B4515061 : Blo 1188411 4515061 := bbase (se 5 (by rfl) ⟨211643, by rfl⟩ : syracuseStep 4515061 = 423287) (by norm_num)
theorem B1271057 : Blo 1188411 1271057 := bbase (se 2 (by rfl) ⟨476646, by rfl⟩ : syracuseStep 1271057 = 953293) (by norm_num)
theorem B3212597 : Blo 1188411 3212597 := bbase (se 5 (by rfl) ⟨150590, by rfl⟩ : syracuseStep 3212597 = 301181) (by norm_num)
theorem B10167605 : Blo 1188411 10167605 := bbase (se 5 (by rfl) ⟨476606, by rfl⟩ : syracuseStep 10167605 = 953213) (by norm_num)
theorem B2008381 : Blo 1188411 2008381 := bbase (se 3 (by rfl) ⟨376571, by rfl⟩ : syracuseStep 2008381 = 753143) (by norm_num)
theorem B2409797 : Blo 1188411 2409797 := bbase (se 4 (by rfl) ⟨225918, by rfl⟩ : syracuseStep 2409797 = 451837) (by norm_num)
theorem B4015493 : Blo 1188411 4015493 := bbase (se 4 (by rfl) ⟨376452, by rfl⟩ : syracuseStep 4015493 = 752905) (by norm_num)
theorem B2008469 : Blo 1188411 2008469 := bbase (se 6 (by rfl) ⟨47073, by rfl⟩ : syracuseStep 2008469 = 94147) (by norm_num)
theorem B1607125 : Blo 1188411 1607125 := bbase (se 7 (by rfl) ⟨18833, by rfl⟩ : syracuseStep 1607125 = 37667) (by norm_num)
theorem B2008597 : Blo 1188411 2008597 := bbase (se 6 (by rfl) ⟨47076, by rfl⟩ : syracuseStep 2008597 = 94153) (by norm_num)
theorem B4515365 : Blo 1188411 4515365 := bbase (se 4 (by rfl) ⟨423315, by rfl⟩ : syracuseStep 4515365 = 846631) (by norm_num)
theorem B2008685 : Blo 1188411 2008685 := bbase (se 3 (by rfl) ⟨376628, by rfl⟩ : syracuseStep 2008685 = 753257) (by norm_num)
theorem B1336981 : Blo 1188411 1336981 := bbase (se 6 (by rfl) ⟨31335, by rfl⟩ : syracuseStep 1336981 = 62671) (by norm_num)
theorem B1337017 : Blo 1188411 1337017 := bbase (se 2 (by rfl) ⟨501381, by rfl⟩ : syracuseStep 1337017 = 1002763) (by norm_num)
theorem B1205977 : Blo 1188411 1205977 := bbase (se 2 (by rfl) ⟨452241, by rfl⟩ : syracuseStep 1205977 = 904483) (by norm_num)
theorem B1337053 : Blo 1188411 1337053 := bbase (se 3 (by rfl) ⟨250697, by rfl⟩ : syracuseStep 1337053 = 501395) (by norm_num)
theorem B3811045 : Blo 1188411 3811045 := bbase (se 4 (by rfl) ⟨357285, by rfl⟩ : syracuseStep 3811045 = 714571) (by norm_num)
theorem B2008813 : Blo 1188411 2008813 := bbase (se 3 (by rfl) ⟨376652, by rfl⟩ : syracuseStep 2008813 = 753305) (by norm_num)
theorem B1337089 : Blo 1188411 1337089 := bbase (se 2 (by rfl) ⟨501408, by rfl⟩ : syracuseStep 1337089 = 1002817) (by norm_num)
theorem B1337125 : Blo 1188411 1337125 := bbase (se 4 (by rfl) ⟨125355, by rfl⟩ : syracuseStep 1337125 = 250711) (by norm_num)
theorem B4015925 : Blo 1188411 4015925 := bbase (se 5 (by rfl) ⟨188246, by rfl⟩ : syracuseStep 4015925 = 376493) (by norm_num)
theorem B1337161 : Blo 1188411 1337161 := bbase (se 2 (by rfl) ⟨501435, by rfl⟩ : syracuseStep 1337161 = 1002871) (by norm_num)
theorem B6022997 : Blo 1188411 6022997 := bbase (se 9 (by rfl) ⟨17645, by rfl⟩ : syracuseStep 6022997 = 35291) (by norm_num)
theorem B2541397 : Blo 1188411 2541397 := bbase (se 9 (by rfl) ⟨7445, by rfl⟩ : syracuseStep 2541397 = 14891) (by norm_num)
theorem B1337197 : Blo 1188411 1337197 := bbase (se 3 (by rfl) ⟨250724, by rfl⟩ : syracuseStep 1337197 = 501449) (by norm_num)
theorem B2410357 : Blo 1188411 2410357 := bbase (se 5 (by rfl) ⟨112985, by rfl⟩ : syracuseStep 2410357 = 225971) (by norm_num)
theorem B6776693 : Blo 1188411 6776693 := bbase (se 5 (by rfl) ⟨317657, by rfl⟩ : syracuseStep 6776693 = 635315) (by norm_num)
theorem B1337233 : Blo 1188411 1337233 := bbase (se 2 (by rfl) ⟨501462, by rfl⟩ : syracuseStep 1337233 = 1002925) (by norm_num)
theorem B5146517 : Blo 1188411 5146517 := bbase (se 6 (by rfl) ⟨120621, by rfl⟩ : syracuseStep 5146517 = 241243) (by norm_num)
theorem B1337269 : Blo 1188411 1337269 := bbase (se 5 (by rfl) ⟨62684, by rfl⟩ : syracuseStep 1337269 = 125369) (by norm_num)
theorem B3008461 : Blo 1188411 3008461 := bbase (se 3 (by rfl) ⟨564086, by rfl⟩ : syracuseStep 3008461 = 1128173) (by norm_num)
theorem B1337305 : Blo 1188411 1337305 := bbase (se 2 (by rfl) ⟨501489, by rfl⟩ : syracuseStep 1337305 = 1002979) (by norm_num)
theorem B6768629 : Blo 1188411 6768629 := bbase (se 5 (by rfl) ⟨317279, by rfl⟩ : syracuseStep 6768629 = 634559) (by norm_num)
theorem B1337341 : Blo 1188411 1337341 := bbase (se 3 (by rfl) ⟨250751, by rfl⟩ : syracuseStep 1337341 = 501503) (by norm_num)
theorem B1206293 : Blo 1188411 1206293 := bbase (se 6 (by rfl) ⟨28272, by rfl⟩ : syracuseStep 1206293 = 56545) (by norm_num)
theorem B1337377 : Blo 1188411 1337377 := bbase (se 2 (by rfl) ⟨501516, by rfl⟩ : syracuseStep 1337377 = 1003033) (by norm_num)
theorem B3008573 : Blo 1188411 3008573 := bbase (se 3 (by rfl) ⟨564107, by rfl⟩ : syracuseStep 3008573 = 1128215) (by norm_num)
theorem B1337413 : Blo 1188411 1337413 := bbase (se 4 (by rfl) ⟨125382, by rfl⟩ : syracuseStep 1337413 = 250765) (by norm_num)
theorem B20088917 : Blo 1188411 20088917 := bbase (se 8 (by rfl) ⟨117708, by rfl⟩ : syracuseStep 20088917 = 235417) (by norm_num)
theorem B1337449 : Blo 1188411 1337449 := bbase (se 2 (by rfl) ⟨501543, by rfl⟩ : syracuseStep 1337449 = 1003087) (by norm_num)
theorem B6514805 : Blo 1188411 6514805 := bbase (se 5 (by rfl) ⟨305381, by rfl⟩ : syracuseStep 6514805 = 610763) (by norm_num)
theorem B7940213 : Blo 1188411 7940213 := bbase (se 5 (by rfl) ⟨372197, by rfl⟩ : syracuseStep 7940213 = 744395) (by norm_num)
theorem B5081221 : Blo 1188411 5081221 := bbase (se 4 (by rfl) ⟨476364, by rfl⟩ : syracuseStep 5081221 = 952729) (by norm_num)
theorem B1337485 : Blo 1188411 1337485 := bbase (se 3 (by rfl) ⟨250778, by rfl⟩ : syracuseStep 1337485 = 501557) (by norm_num)
theorem B1337521 : Blo 1188411 1337521 := bbase (se 2 (by rfl) ⟨501570, by rfl⟩ : syracuseStep 1337521 = 1003141) (by norm_num)
theorem B2541773 : Blo 1188411 2541773 := bbase (se 3 (by rfl) ⟨476582, by rfl⟩ : syracuseStep 2541773 = 953165) (by norm_num)
theorem B1337557 : Blo 1188411 1337557 := bbase (se 7 (by rfl) ⟨15674, by rfl⟩ : syracuseStep 1337557 = 31349) (by norm_num)
theorem B4016357 : Blo 1188411 4016357 := bbase (se 4 (by rfl) ⟨376533, by rfl⟩ : syracuseStep 4016357 = 753067) (by norm_num)
theorem B1337593 : Blo 1188411 1337593 := bbase (se 2 (by rfl) ⟨501597, by rfl⟩ : syracuseStep 1337593 = 1003195) (by norm_num)
theorem B3008765 : Blo 1188411 3008765 := bbase (se 3 (by rfl) ⟨564143, by rfl⟩ : syracuseStep 3008765 = 1128287) (by norm_num)
theorem B1337629 : Blo 1188411 1337629 := bbase (se 3 (by rfl) ⟨250805, by rfl⟩ : syracuseStep 1337629 = 501611) (by norm_num)
theorem B1222949 : Blo 1188411 1222949 := bbase (se 4 (by rfl) ⟨114651, by rfl⟩ : syracuseStep 1222949 = 229303) (by norm_num)
theorem B1337665 : Blo 1188411 1337665 := bbase (se 2 (by rfl) ⟨501624, by rfl⟩ : syracuseStep 1337665 = 1003249) (by norm_num)
theorem B2034013 : Blo 1188411 2034013 := bbase (se 3 (by rfl) ⟨381377, by rfl⟩ : syracuseStep 2034013 = 762755) (by norm_num)
theorem B1337701 : Blo 1188411 1337701 := bbase (se 4 (by rfl) ⟨125409, by rfl⟩ : syracuseStep 1337701 = 250819) (by norm_num)
theorem B1427825 : Blo 1188411 1427825 := bbase (se 2 (by rfl) ⟨535434, by rfl⟩ : syracuseStep 1427825 = 1070869) (by norm_num)
theorem B1337737 : Blo 1188411 1337737 := bbase (se 2 (by rfl) ⟨501651, by rfl⟩ : syracuseStep 1337737 = 1003303) (by norm_num)
theorem B5794213 : Blo 1188411 5794213 := bbase (se 4 (by rfl) ⟨543207, by rfl⟩ : syracuseStep 5794213 = 1086415) (by norm_num)
theorem B1337773 : Blo 1188411 1337773 := bbase (se 3 (by rfl) ⟨250832, by rfl⟩ : syracuseStep 1337773 = 501665) (by norm_num)
theorem B1337809 : Blo 1188411 1337809 := bbase (se 2 (by rfl) ⟨501678, by rfl⟩ : syracuseStep 1337809 = 1003357) (by norm_num)
theorem B36628949 : Blo 1188411 36628949 := bbase (se 7 (by rfl) ⟨429245, by rfl⟩ : syracuseStep 36628949 = 858491) (by norm_num)
theorem B1337845 : Blo 1188411 1337845 := bbase (se 5 (by rfl) ⟨62711, by rfl⟩ : syracuseStep 1337845 = 125423) (by norm_num)
theorem B4286965 : Blo 1188411 4286965 := bbase (se 5 (by rfl) ⟨200951, by rfl⟩ : syracuseStep 4286965 = 401903) (by norm_num)
theorem B1337881 : Blo 1188411 1337881 := bbase (se 2 (by rfl) ⟨501705, by rfl⟩ : syracuseStep 1337881 = 1003411) (by norm_num)
theorem B2714141 : Blo 1188411 2714141 := bbase (se 3 (by rfl) ⟨508901, by rfl⟩ : syracuseStep 2714141 = 1017803) (by norm_num)
theorem B1337917 : Blo 1188411 1337917 := bbase (se 3 (by rfl) ⟨250859, by rfl⟩ : syracuseStep 1337917 = 501719) (by norm_num)
theorem B3009109 : Blo 1188411 3009109 := bbase (se 8 (by rfl) ⟨17631, by rfl⟩ : syracuseStep 3009109 = 35263) (by norm_num)
theorem B1337953 : Blo 1188411 1337953 := bbase (se 2 (by rfl) ⟨501732, by rfl⟩ : syracuseStep 1337953 = 1003465) (by norm_num)
theorem B1337989 : Blo 1188411 1337989 := bbase (se 4 (by rfl) ⟨125436, by rfl⟩ : syracuseStep 1337989 = 250873) (by norm_num)
theorem B4016789 : Blo 1188411 4016789 := bbase (se 6 (by rfl) ⟨94143, by rfl⟩ : syracuseStep 4016789 = 188287) (by norm_num)
theorem B1428133 : Blo 1188411 1428133 := bbase (se 4 (by rfl) ⟨133887, by rfl⟩ : syracuseStep 1428133 = 267775) (by norm_num)
theorem B1338025 : Blo 1188411 1338025 := bbase (se 2 (by rfl) ⟨501759, by rfl⟩ : syracuseStep 1338025 = 1003519) (by norm_num)
theorem B3009221 : Blo 1188411 3009221 := bbase (se 4 (by rfl) ⟨282114, by rfl⟩ : syracuseStep 3009221 = 564229) (by norm_num)
theorem B1338061 : Blo 1188411 1338061 := bbase (se 3 (by rfl) ⟨250886, by rfl⟩ : syracuseStep 1338061 = 501773) (by norm_num)
theorem B3386069 : Blo 1188411 3386069 := bbase (se 7 (by rfl) ⟨39680, by rfl⟩ : syracuseStep 3386069 = 79361) (by norm_num)
theorem B1338097 : Blo 1188411 1338097 := bbase (se 2 (by rfl) ⟨501786, by rfl⟩ : syracuseStep 1338097 = 1003573) (by norm_num)
theorem B1608445 : Blo 1188411 1608445 := bbase (se 3 (by rfl) ⟨301583, by rfl⟩ : syracuseStep 1608445 = 603167) (by norm_num)
theorem B1428229 : Blo 1188411 1428229 := bbase (se 4 (by rfl) ⟨133896, by rfl⟩ : syracuseStep 1428229 = 267793) (by norm_num)
theorem B11578133 : Blo 1188411 11578133 := bbase (se 6 (by rfl) ⟨271362, by rfl⟩ : syracuseStep 11578133 = 542725) (by norm_num)
theorem B1338133 : Blo 1188411 1338133 := bbase (se 6 (by rfl) ⟨31362, by rfl⟩ : syracuseStep 1338133 = 62725) (by norm_num)
theorem B3435317 : Blo 1188411 3435317 := bbase (se 5 (by rfl) ⟨161030, by rfl⟩ : syracuseStep 3435317 = 322061) (by norm_num)
theorem B9161525 : Blo 1188411 9161525 := bbase (se 5 (by rfl) ⟨429446, by rfl⟩ : syracuseStep 9161525 = 858893) (by norm_num)
theorem B1338169 : Blo 1188411 1338169 := bbase (se 2 (by rfl) ⟨501813, by rfl⟩ : syracuseStep 1338169 = 1003627) (by norm_num)
theorem B1608509 : Blo 1188411 1608509 := bbase (se 3 (by rfl) ⟨301595, by rfl⟩ : syracuseStep 1608509 = 603191) (by norm_num)
theorem B1526593 : Blo 1188411 1526593 := bbase (se 2 (by rfl) ⟨572472, by rfl⟩ : syracuseStep 1526593 = 1144945) (by norm_num)
theorem B1338205 : Blo 1188411 1338205 := bbase (se 3 (by rfl) ⟨250913, by rfl⟩ : syracuseStep 1338205 = 501827) (by norm_num)
theorem B1338241 : Blo 1188411 1338241 := bbase (se 2 (by rfl) ⟨501840, by rfl⟩ : syracuseStep 1338241 = 1003681) (by norm_num)
theorem B3009413 : Blo 1188411 3009413 := bbase (se 4 (by rfl) ⟨282132, by rfl⟩ : syracuseStep 3009413 = 564265) (by norm_num)
theorem B1428373 : Blo 1188411 1428373 := bbase (se 6 (by rfl) ⟨33477, by rfl⟩ : syracuseStep 1428373 = 66955) (by norm_num)
theorem B1338277 : Blo 1188411 1338277 := bbase (se 4 (by rfl) ⟨125463, by rfl⟩ : syracuseStep 1338277 = 250927) (by norm_num)
theorem B1338313 : Blo 1188411 1338313 := bbase (se 2 (by rfl) ⟨501867, by rfl⟩ : syracuseStep 1338313 = 1003735) (by norm_num)
theorem B3050453 : Blo 1188411 3050453 := bbase (se 7 (by rfl) ⟨35747, by rfl⟩ : syracuseStep 3050453 = 71495) (by norm_num)
theorem B1338349 : Blo 1188411 1338349 := bbase (se 3 (by rfl) ⟨250940, by rfl⟩ : syracuseStep 1338349 = 501881) (by norm_num)
theorem B2411525 : Blo 1188411 2411525 := bbase (se 4 (by rfl) ⟨226080, by rfl⟩ : syracuseStep 2411525 = 452161) (by norm_num)
theorem B1338385 : Blo 1188411 1338385 := bbase (se 2 (by rfl) ⟨501894, by rfl⟩ : syracuseStep 1338385 = 1003789) (by norm_num)
theorem B6777877 : Blo 1188411 6777877 := bbase (se 6 (by rfl) ⟨158856, by rfl⟩ : syracuseStep 6777877 = 317713) (by norm_num)
theorem B1338421 : Blo 1188411 1338421 := bbase (se 5 (by rfl) ⟨62738, by rfl⟩ : syracuseStep 1338421 = 125477) (by norm_num)
theorem B4017221 : Blo 1188411 4017221 := bbase (se 4 (by rfl) ⟨376614, by rfl⟩ : syracuseStep 4017221 = 753229) (by norm_num)
theorem B1338457 : Blo 1188411 1338457 := bbase (se 2 (by rfl) ⟨501921, by rfl⟩ : syracuseStep 1338457 = 1003843) (by norm_num)
theorem B2714717 : Blo 1188411 2714717 := bbase (se 3 (by rfl) ⟨509009, by rfl⟩ : syracuseStep 2714717 = 1018019) (by norm_num)
theorem B6024293 : Blo 1188411 6024293 := bbase (se 4 (by rfl) ⟨564777, by rfl⟩ : syracuseStep 6024293 = 1129555) (by norm_num)
theorem B1338493 : Blo 1188411 1338493 := bbase (se 3 (by rfl) ⟨250967, by rfl⟩ : syracuseStep 1338493 = 501935) (by norm_num)
theorem B1338529 : Blo 1188411 1338529 := bbase (se 2 (by rfl) ⟨501948, by rfl⟩ : syracuseStep 1338529 = 1003897) (by norm_num)
theorem B2714797 : Blo 1188411 2714797 := bbase (se 3 (by rfl) ⟨509024, by rfl⟩ : syracuseStep 2714797 = 1018049) (by norm_num)
theorem B1338565 : Blo 1188411 1338565 := bbase (se 4 (by rfl) ⟨125490, by rfl⟩ : syracuseStep 1338565 = 250981) (by norm_num)
theorem B3009757 : Blo 1188411 3009757 := bbase (se 3 (by rfl) ⟨564329, by rfl⟩ : syracuseStep 3009757 = 1128659) (by norm_num)
theorem B1338601 : Blo 1188411 1338601 := bbase (se 2 (by rfl) ⟨501975, by rfl⟩ : syracuseStep 1338601 = 1003951) (by norm_num)
theorem B1338637 : Blo 1188411 1338637 := bbase (se 3 (by rfl) ⟨250994, by rfl⟩ : syracuseStep 1338637 = 501989) (by norm_num)
theorem B2256149 : Blo 1188411 2256149 := bbase (se 6 (by rfl) ⟨52878, by rfl⟩ : syracuseStep 2256149 = 105757) (by norm_num)
theorem B1338673 : Blo 1188411 1338673 := bbase (se 2 (by rfl) ⟨502002, by rfl⟩ : syracuseStep 1338673 = 1004005) (by norm_num)
theorem B2673989 : Blo 1188411 2673989 := bbase (se 4 (by rfl) ⟨250686, by rfl⟩ : syracuseStep 2673989 = 501373) (by norm_num)
theorem B3009869 : Blo 1188411 3009869 := bbase (se 3 (by rfl) ⟨564350, by rfl⟩ : syracuseStep 3009869 = 1128701) (by norm_num)
theorem B1338709 : Blo 1188411 1338709 := bbase (se 11 (by rfl) ⟨980, by rfl⟩ : syracuseStep 1338709 = 1961) (by norm_num)
theorem B1338745 : Blo 1188411 1338745 := bbase (se 2 (by rfl) ⟨502029, by rfl⟩ : syracuseStep 1338745 = 1004059) (by norm_num)
theorem B2674061 : Blo 1188411 2674061 := bbase (se 3 (by rfl) ⟨501386, by rfl⟩ : syracuseStep 2674061 = 1002773) (by norm_num)
theorem B1338781 : Blo 1188411 1338781 := bbase (se 3 (by rfl) ⟨251021, by rfl⟩ : syracuseStep 1338781 = 502043) (by norm_num)
theorem B2936237 : Blo 1188411 2936237 := bbase (se 3 (by rfl) ⟨550544, by rfl⟩ : syracuseStep 2936237 = 1101089) (by norm_num)
theorem B1338817 : Blo 1188411 1338817 := bbase (se 2 (by rfl) ⟨502056, by rfl⟩ : syracuseStep 1338817 = 1004113) (by norm_num)
theorem B1904069 : Blo 1188411 1904069 := bbase (se 4 (by rfl) ⟨178506, by rfl⟩ : syracuseStep 1904069 = 357013) (by norm_num)
theorem B2674133 : Blo 1188411 2674133 := bbase (se 7 (by rfl) ⟨31337, by rfl⟩ : syracuseStep 2674133 = 62675) (by norm_num)
theorem B4287973 : Blo 1188411 4287973 := bbase (se 4 (by rfl) ⟨401997, by rfl⟩ : syracuseStep 4287973 = 803995) (by norm_num)
theorem B1338853 : Blo 1188411 1338853 := bbase (se 4 (by rfl) ⟨125517, by rfl⟩ : syracuseStep 1338853 = 251035) (by norm_num)
theorem B6016517 : Blo 1188411 6016517 := bbase (se 4 (by rfl) ⟨564048, by rfl⟩ : syracuseStep 6016517 = 1128097) (by norm_num)
theorem B1338889 : Blo 1188411 1338889 := bbase (se 2 (by rfl) ⟨502083, by rfl⟩ : syracuseStep 1338889 = 1004167) (by norm_num)
theorem B3010061 : Blo 1188411 3010061 := bbase (se 3 (by rfl) ⟨564386, by rfl⟩ : syracuseStep 3010061 = 1128773) (by norm_num)
theorem B2674205 : Blo 1188411 2674205 := bbase (se 3 (by rfl) ⟨501413, by rfl⟩ : syracuseStep 2674205 = 1002827) (by norm_num)
theorem B1338925 : Blo 1188411 1338925 := bbase (se 3 (by rfl) ⟨251048, by rfl⟩ : syracuseStep 1338925 = 502097) (by norm_num)
theorem B2256437 : Blo 1188411 2256437 := bbase (se 5 (by rfl) ⟨105770, by rfl⟩ : syracuseStep 2256437 = 211541) (by norm_num)
theorem B1338961 : Blo 1188411 1338961 := bbase (se 2 (by rfl) ⟨502110, by rfl⟩ : syracuseStep 1338961 = 1004221) (by norm_num)
theorem B4951637 : Blo 1188411 4951637 := bbase (se 8 (by rfl) ⟨29013, by rfl⟩ : syracuseStep 4951637 = 58027) (by norm_num)
theorem B5082709 : Blo 1188411 5082709 := bbase (se 8 (by rfl) ⟨29781, by rfl⟩ : syracuseStep 5082709 = 59563) (by norm_num)
theorem B2674277 : Blo 1188411 2674277 := bbase (se 4 (by rfl) ⟨250713, by rfl⟩ : syracuseStep 2674277 = 501427) (by norm_num)
theorem B4517477 : Blo 1188411 4517477 := bbase (se 4 (by rfl) ⟨423513, by rfl⟩ : syracuseStep 4517477 = 847027) (by norm_num)
theorem B5082725 : Blo 1188411 5082725 := bbase (se 4 (by rfl) ⟨476505, by rfl⟩ : syracuseStep 5082725 = 953011) (by norm_num)
theorem B1338997 : Blo 1188411 1338997 := bbase (se 5 (by rfl) ⟨62765, by rfl⟩ : syracuseStep 1338997 = 125531) (by norm_num)
theorem B1339033 : Blo 1188411 1339033 := bbase (se 2 (by rfl) ⟨502137, by rfl⟩ : syracuseStep 1339033 = 1004275) (by norm_num)
theorem B2674349 : Blo 1188411 2674349 := bbase (se 3 (by rfl) ⟨501440, by rfl⟩ : syracuseStep 2674349 = 1002881) (by norm_num)
theorem B1339069 : Blo 1188411 1339069 := bbase (se 3 (by rfl) ⟨251075, by rfl⟩ : syracuseStep 1339069 = 502151) (by norm_num)
theorem B2256589 : Blo 1188411 2256589 := bbase (se 3 (by rfl) ⟨423110, by rfl⟩ : syracuseStep 2256589 = 846221) (by norm_num)
theorem B1339105 : Blo 1188411 1339105 := bbase (se 2 (by rfl) ⟨502164, by rfl⟩ : syracuseStep 1339105 = 1004329) (by norm_num)
theorem B2674421 : Blo 1188411 2674421 := bbase (se 5 (by rfl) ⟨125363, by rfl⟩ : syracuseStep 2674421 = 250727) (by norm_num)
theorem B1339141 : Blo 1188411 1339141 := bbase (se 4 (by rfl) ⟨125544, by rfl⟩ : syracuseStep 1339141 = 251089) (by norm_num)
theorem B1339177 : Blo 1188411 1339177 := bbase (se 2 (by rfl) ⟨502191, by rfl⟩ : syracuseStep 1339177 = 1004383) (by norm_num)
theorem B2674493 : Blo 1188411 2674493 := bbase (se 3 (by rfl) ⟨501467, by rfl⟩ : syracuseStep 2674493 = 1002935) (by norm_num)
theorem B1339213 : Blo 1188411 1339213 := bbase (se 3 (by rfl) ⟨251102, by rfl⟩ : syracuseStep 1339213 = 502205) (by norm_num)
theorem B3010405 : Blo 1188411 3010405 := bbase (se 4 (by rfl) ⟨282225, by rfl⟩ : syracuseStep 3010405 = 564451) (by norm_num)
theorem B3387253 : Blo 1188411 3387253 := bbase (se 5 (by rfl) ⟨158777, by rfl⟩ : syracuseStep 3387253 = 317555) (by norm_num)
theorem B1429373 : Blo 1188411 1429373 := bbase (se 3 (by rfl) ⟨268007, by rfl⟩ : syracuseStep 1429373 = 536015) (by norm_num)
theorem B2674565 : Blo 1188411 2674565 := bbase (se 4 (by rfl) ⟨250740, by rfl⟩ : syracuseStep 2674565 = 501481) (by norm_num)
theorem B4517765 : Blo 1188411 4517765 := bbase (se 4 (by rfl) ⟨423540, by rfl⟩ : syracuseStep 4517765 = 847081) (by norm_num)
theorem B1904581 : Blo 1188411 1904581 := bbase (se 4 (by rfl) ⟨178554, by rfl⟩ : syracuseStep 1904581 = 357109) (by norm_num)
theorem B2674637 : Blo 1188411 2674637 := bbase (se 3 (by rfl) ⟨501494, by rfl⟩ : syracuseStep 2674637 = 1002989) (by norm_num)
theorem B3010517 : Blo 1188411 3010517 := bbase (se 7 (by rfl) ⟨35279, by rfl⟩ : syracuseStep 3010517 = 70559) (by norm_num)
theorem B2256893 : Blo 1188411 2256893 := bbase (se 3 (by rfl) ⟨423167, by rfl⟩ : syracuseStep 2256893 = 846335) (by norm_num)
theorem B2674709 : Blo 1188411 2674709 := bbase (se 6 (by rfl) ⟨62688, by rfl⟩ : syracuseStep 2674709 = 125377) (by norm_num)
theorem B8572949 : Blo 1188411 8572949 := bbase (se 6 (by rfl) ⟨200928, by rfl⟩ : syracuseStep 8572949 = 401857) (by norm_num)
theorem B3387413 : Blo 1188411 3387413 := bbase (se 6 (by rfl) ⟨79392, by rfl⟩ : syracuseStep 3387413 = 158785) (by norm_num)
theorem B7721045 : Blo 1188411 7721045 := bbase (se 8 (by rfl) ⟨45240, by rfl⟩ : syracuseStep 7721045 = 90481) (by norm_num)
theorem B2674781 : Blo 1188411 2674781 := bbase (se 3 (by rfl) ⟨501521, by rfl⟩ : syracuseStep 2674781 = 1003043) (by norm_num)
theorem B3010709 : Blo 1188411 3010709 := bbase (se 6 (by rfl) ⟨70563, by rfl⟩ : syracuseStep 3010709 = 141127) (by norm_num)
theorem B2674853 : Blo 1188411 2674853 := bbase (se 4 (by rfl) ⟨250767, by rfl⟩ : syracuseStep 2674853 = 501535) (by norm_num)
theorem B2412757 : Blo 1188411 2412757 := bbase (se 7 (by rfl) ⟨28274, by rfl⟩ : syracuseStep 2412757 = 56549) (by norm_num)
theorem B2674925 : Blo 1188411 2674925 := bbase (se 3 (by rfl) ⟨501548, by rfl⟩ : syracuseStep 2674925 = 1003097) (by norm_num)
theorem B3387653 : Blo 1188411 3387653 := bbase (se 4 (by rfl) ⟨317592, by rfl⟩ : syracuseStep 3387653 = 635185) (by norm_num)
theorem B2674997 : Blo 1188411 2674997 := bbase (se 5 (by rfl) ⟨125390, by rfl⟩ : syracuseStep 2674997 = 250781) (by norm_num)
theorem B6025589 : Blo 1188411 6025589 := bbase (se 5 (by rfl) ⟨282449, by rfl⟩ : syracuseStep 6025589 = 564899) (by norm_num)
theorem B2675069 : Blo 1188411 2675069 := bbase (se 3 (by rfl) ⟨501575, by rfl⟩ : syracuseStep 2675069 = 1003151) (by norm_num)
theorem B2675141 : Blo 1188411 2675141 := bbase (se 4 (by rfl) ⟨250794, by rfl⟩ : syracuseStep 2675141 = 501589) (by norm_num)
theorem B3387845 : Blo 1188411 3387845 := bbase (se 4 (by rfl) ⟨317610, by rfl⟩ : syracuseStep 3387845 = 635221) (by norm_num)
theorem B1905125 : Blo 1188411 1905125 := bbase (se 4 (by rfl) ⟨178605, by rfl⟩ : syracuseStep 1905125 = 357211) (by norm_num)
theorem B3011053 : Blo 1188411 3011053 := bbase (se 3 (by rfl) ⟨564572, by rfl⟩ : syracuseStep 3011053 = 1129145) (by norm_num)
theorem B2675213 : Blo 1188411 2675213 := bbase (se 3 (by rfl) ⟨501602, by rfl⟩ : syracuseStep 2675213 = 1003205) (by norm_num)
theorem B1430065 : Blo 1188411 1430065 := bbase (se 2 (by rfl) ⟨536274, by rfl⟩ : syracuseStep 1430065 = 1072549) (by norm_num)
theorem B10850869 : Blo 1188411 10850869 := bbase (se 5 (by rfl) ⟨508634, by rfl⟩ : syracuseStep 10850869 = 1017269) (by norm_num)
theorem B2675285 : Blo 1188411 2675285 := bbase (se 8 (by rfl) ⟨15675, by rfl⟩ : syracuseStep 2675285 = 31351) (by norm_num)
theorem B3011165 : Blo 1188411 3011165 := bbase (se 3 (by rfl) ⟨564593, by rfl⟩ : syracuseStep 3011165 = 1129187) (by norm_num)
theorem B4067957 : Blo 1188411 4067957 := bbase (se 5 (by rfl) ⟨190685, by rfl⟩ : syracuseStep 4067957 = 381371) (by norm_num)
theorem B9032309 : Blo 1188411 9032309 := bbase (se 5 (by rfl) ⟨423389, by rfl⟩ : syracuseStep 9032309 = 846779) (by norm_num)
theorem B2675357 : Blo 1188411 2675357 := bbase (se 3 (by rfl) ⟨501629, by rfl⟩ : syracuseStep 2675357 = 1003259) (by norm_num)
theorem B2675429 : Blo 1188411 2675429 := bbase (se 4 (by rfl) ⟨250821, by rfl⟩ : syracuseStep 2675429 = 501643) (by norm_num)
theorem B2142949 : Blo 1188411 2142949 := bbase (se 4 (by rfl) ⟨200901, by rfl⟩ : syracuseStep 2142949 = 401803) (by norm_num)
theorem B2257645 : Blo 1188411 2257645 := bbase (se 3 (by rfl) ⟨423308, by rfl⟩ : syracuseStep 2257645 = 846617) (by norm_num)
theorem B6017813 : Blo 1188411 6017813 := bbase (se 6 (by rfl) ⟨141042, by rfl⟩ : syracuseStep 6017813 = 282085) (by norm_num)
theorem B3011357 : Blo 1188411 3011357 := bbase (se 3 (by rfl) ⟨564629, by rfl⟩ : syracuseStep 3011357 = 1129259) (by norm_num)
theorem B2675501 : Blo 1188411 2675501 := bbase (se 3 (by rfl) ⟨501656, by rfl⟩ : syracuseStep 2675501 = 1003313) (by norm_num)
theorem B2143021 : Blo 1188411 2143021 := bbase (se 3 (by rfl) ⟨401816, by rfl⟩ : syracuseStep 2143021 = 803633) (by norm_num)
theorem B9646901 : Blo 1188411 9646901 := bbase (se 5 (by rfl) ⟨452198, by rfl⟩ : syracuseStep 9646901 = 904397) (by norm_num)
theorem B1782629 : Blo 1188411 1782629 := bbase (se 4 (by rfl) ⟨167121, by rfl⟩ : syracuseStep 1782629 = 334243) (by norm_num)
theorem B1504109 : Blo 1188411 1504109 := bbase (se 3 (by rfl) ⟨282020, by rfl⟩ : syracuseStep 1504109 = 564041) (by norm_num)
theorem B1692533 : Blo 1188411 1692533 := bbase (se 5 (by rfl) ⟨79337, by rfl⟩ : syracuseStep 1692533 = 158675) (by norm_num)
theorem B2675573 : Blo 1188411 2675573 := bbase (se 5 (by rfl) ⟨125417, by rfl⟩ : syracuseStep 2675573 = 250835) (by norm_num)
theorem B1782653 : Blo 1188411 1782653 := bbase (se 3 (by rfl) ⟨334247, by rfl⟩ : syracuseStep 1782653 = 668495) (by norm_num)
theorem B2257789 : Blo 1188411 2257789 := bbase (se 3 (by rfl) ⟨423335, by rfl⟩ : syracuseStep 2257789 = 846671) (by norm_num)
theorem B1807237 : Blo 1188411 1807237 := bbase (se 4 (by rfl) ⟨169428, by rfl⟩ : syracuseStep 1807237 = 338857) (by norm_num)
theorem B1782677 : Blo 1188411 1782677 := bbase (se 6 (by rfl) ⟨41781, by rfl⟩ : syracuseStep 1782677 = 83563) (by norm_num)
theorem B5714837 : Blo 1188411 5714837 := bbase (se 6 (by rfl) ⟨133941, by rfl⟩ : syracuseStep 5714837 = 267883) (by norm_num)
theorem B1504165 : Blo 1188411 1504165 := bbase (se 4 (by rfl) ⟨141015, by rfl⟩ : syracuseStep 1504165 = 282031) (by norm_num)
theorem B1782701 : Blo 1188411 1782701 := bbase (se 3 (by rfl) ⟨334256, by rfl⟩ : syracuseStep 1782701 = 668513) (by norm_num)
theorem B2675645 : Blo 1188411 2675645 := bbase (se 3 (by rfl) ⟨501683, by rfl⟩ : syracuseStep 2675645 = 1003367) (by norm_num)
theorem B1487809 : Blo 1188411 1487809 := bbase (se 2 (by rfl) ⟨557928, by rfl⟩ : syracuseStep 1487809 = 1115857) (by norm_num)
theorem B1782725 : Blo 1188411 1782725 := bbase (se 4 (by rfl) ⟨167130, by rfl⟩ : syracuseStep 1782725 = 334261) (by norm_num)
theorem B1692613 : Blo 1188411 1692613 := bbase (se 4 (by rfl) ⟨158682, by rfl⟩ : syracuseStep 1692613 = 317365) (by norm_num)
theorem B1782749 : Blo 1188411 1782749 := bbase (se 3 (by rfl) ⟨334265, by rfl⟩ : syracuseStep 1782749 = 668531) (by norm_num)
theorem B1782773 : Blo 1188411 1782773 := bbase (se 5 (by rfl) ⟨83567, by rfl⟩ : syracuseStep 1782773 = 167135) (by norm_num)
theorem B1504261 : Blo 1188411 1504261 := bbase (se 4 (by rfl) ⟨141024, by rfl⟩ : syracuseStep 1504261 = 282049) (by norm_num)
theorem B2675717 : Blo 1188411 2675717 := bbase (se 4 (by rfl) ⟨250848, by rfl⟩ : syracuseStep 2675717 = 501697) (by norm_num)
theorem B1782797 : Blo 1188411 1782797 := bbase (se 3 (by rfl) ⟨334274, by rfl⟩ : syracuseStep 1782797 = 668549) (by norm_num)
theorem B1905677 : Blo 1188411 1905677 := bbase (se 3 (by rfl) ⟨357314, by rfl⟩ : syracuseStep 1905677 = 714629) (by norm_num)
theorem B9024533 : Blo 1188411 9024533 := bbase (se 6 (by rfl) ⟨211512, by rfl⟩ : syracuseStep 9024533 = 423025) (by norm_num)
theorem B2143253 : Blo 1188411 2143253 := bbase (se 6 (by rfl) ⟨50232, by rfl⟩ : syracuseStep 2143253 = 100465) (by norm_num)
theorem B2257949 : Blo 1188411 2257949 := bbase (se 3 (by rfl) ⟨423365, by rfl⟩ : syracuseStep 2257949 = 846731) (by norm_num)
theorem B1782821 : Blo 1188411 1782821 := bbase (se 4 (by rfl) ⟨167139, by rfl⟩ : syracuseStep 1782821 = 334279) (by norm_num)
theorem B4518949 : Blo 1188411 4518949 := bbase (se 4 (by rfl) ⟨423651, by rfl⟩ : syracuseStep 4518949 = 847303) (by norm_num)
theorem B1905709 : Blo 1188411 1905709 := bbase (se 3 (by rfl) ⟨357320, by rfl⟩ : syracuseStep 1905709 = 714641) (by norm_num)
theorem B2290733 : Blo 1188411 2290733 := bbase (se 3 (by rfl) ⟨429512, by rfl⟩ : syracuseStep 2290733 = 859025) (by norm_num)
theorem B1782845 : Blo 1188411 1782845 := bbase (se 3 (by rfl) ⟨334283, by rfl⟩ : syracuseStep 1782845 = 668567) (by norm_num)
theorem B1692733 : Blo 1188411 1692733 := bbase (se 3 (by rfl) ⟨317387, by rfl⟩ : syracuseStep 1692733 = 634775) (by norm_num)
theorem B2675789 : Blo 1188411 2675789 := bbase (se 3 (by rfl) ⟨501710, by rfl⟩ : syracuseStep 2675789 = 1003421) (by norm_num)
theorem B1782869 : Blo 1188411 1782869 := bbase (se 8 (by rfl) ⟨10446, by rfl⟩ : syracuseStep 1782869 = 20893) (by norm_num)
theorem B1782893 : Blo 1188411 1782893 := bbase (se 3 (by rfl) ⟨334292, by rfl⟩ : syracuseStep 1782893 = 668585) (by norm_num)
theorem B3011701 : Blo 1188411 3011701 := bbase (se 5 (by rfl) ⟨141173, by rfl⟩ : syracuseStep 3011701 = 282347) (by norm_num)
theorem B1782917 : Blo 1188411 1782917 := bbase (se 4 (by rfl) ⟨167148, by rfl⟩ : syracuseStep 1782917 = 334297) (by norm_num)
theorem B2675861 : Blo 1188411 2675861 := bbase (se 6 (by rfl) ⟨62715, by rfl⟩ : syracuseStep 2675861 = 125431) (by norm_num)
theorem B3093653 : Blo 1188411 3093653 := bbase (se 6 (by rfl) ⟨72507, by rfl⟩ : syracuseStep 3093653 = 145015) (by norm_num)
theorem B1782941 : Blo 1188411 1782941 := bbase (se 3 (by rfl) ⟨334301, by rfl⟩ : syracuseStep 1782941 = 668603) (by norm_num)
theorem B1692829 : Blo 1188411 1692829 := bbase (se 3 (by rfl) ⟨317405, by rfl⟩ : syracuseStep 1692829 = 634811) (by norm_num)
theorem B4011173 : Blo 1188411 4011173 := bbase (se 4 (by rfl) ⟨376047, by rfl⟩ : syracuseStep 4011173 = 752095) (by norm_num)
theorem B2258093 : Blo 1188411 2258093 := bbase (se 3 (by rfl) ⟨423392, by rfl⟩ : syracuseStep 2258093 = 846785) (by norm_num)
theorem B1504433 : Blo 1188411 1504433 := bbase (se 2 (by rfl) ⟨564162, by rfl⟩ : syracuseStep 1504433 = 1128325) (by norm_num)
theorem B1782965 : Blo 1188411 1782965 := bbase (se 5 (by rfl) ⟨83576, by rfl⟩ : syracuseStep 1782965 = 167153) (by norm_num)
theorem B1782989 : Blo 1188411 1782989 := bbase (se 3 (by rfl) ⟨334310, by rfl⟩ : syracuseStep 1782989 = 668621) (by norm_num)
theorem B2675933 : Blo 1188411 2675933 := bbase (se 3 (by rfl) ⟨501737, by rfl⟩ : syracuseStep 2675933 = 1003475) (by norm_num)
theorem B1783013 : Blo 1188411 1783013 := bbase (se 4 (by rfl) ⟨167157, by rfl⟩ : syracuseStep 1783013 = 334315) (by norm_num)
theorem B3011813 : Blo 1188411 3011813 := bbase (se 4 (by rfl) ⟨282357, by rfl⟩ : syracuseStep 3011813 = 564715) (by norm_num)
theorem B1504489 : Blo 1188411 1504489 := bbase (se 2 (by rfl) ⟨564183, by rfl⟩ : syracuseStep 1504489 = 1128367) (by norm_num)
theorem B3216629 : Blo 1188411 3216629 := bbase (se 5 (by rfl) ⟨150779, by rfl⟩ : syracuseStep 3216629 = 301559) (by norm_num)
theorem B1783037 : Blo 1188411 1783037 := bbase (se 3 (by rfl) ⟨334319, by rfl⟩ : syracuseStep 1783037 = 668639) (by norm_num)
theorem B3257605 : Blo 1188411 3257605 := bbase (se 4 (by rfl) ⟨305400, by rfl⟩ : syracuseStep 3257605 = 610801) (by norm_num)
theorem B1783061 : Blo 1188411 1783061 := bbase (se 6 (by rfl) ⟨41790, by rfl⟩ : syracuseStep 1783061 = 83581) (by norm_num)
theorem B2676005 : Blo 1188411 2676005 := bbase (se 4 (by rfl) ⟨250875, by rfl⟩ : syracuseStep 2676005 = 501751) (by norm_num)
theorem B1783085 : Blo 1188411 1783085 := bbase (se 3 (by rfl) ⟨334328, by rfl⟩ : syracuseStep 1783085 = 668657) (by norm_num)
theorem B1783109 : Blo 1188411 1783109 := bbase (se 4 (by rfl) ⟨167166, by rfl⟩ : syracuseStep 1783109 = 334333) (by norm_num)
theorem B1504585 : Blo 1188411 1504585 := bbase (se 2 (by rfl) ⟨564219, by rfl⟩ : syracuseStep 1504585 = 1128439) (by norm_num)
theorem B4519253 : Blo 1188411 4519253 := bbase (se 13 (by rfl) ⟨827, by rfl⟩ : syracuseStep 4519253 = 1655) (by norm_num)
theorem B1783133 : Blo 1188411 1783133 := bbase (se 3 (by rfl) ⟨334337, by rfl⟩ : syracuseStep 1783133 = 668675) (by norm_num)
theorem B2676077 : Blo 1188411 2676077 := bbase (se 3 (by rfl) ⟨501764, by rfl⟩ : syracuseStep 2676077 = 1003529) (by norm_num)
theorem B1783157 : Blo 1188411 1783157 := bbase (se 5 (by rfl) ⟨83585, by rfl⟩ : syracuseStep 1783157 = 167171) (by norm_num)
theorem B5428613 : Blo 1188411 5428613 := bbase (se 4 (by rfl) ⟨508932, by rfl⟩ : syracuseStep 5428613 = 1017865) (by norm_num)
theorem B1783181 : Blo 1188411 1783181 := bbase (se 3 (by rfl) ⟨334346, by rfl⟩ : syracuseStep 1783181 = 668693) (by norm_num)
theorem B1783205 : Blo 1188411 1783205 := bbase (se 4 (by rfl) ⟨167175, by rfl⟩ : syracuseStep 1783205 = 334351) (by norm_num)
theorem B3012005 : Blo 1188411 3012005 := bbase (se 4 (by rfl) ⟨282375, by rfl⟩ : syracuseStep 3012005 = 564751) (by norm_num)
theorem B3388837 : Blo 1188411 3388837 := bbase (se 4 (by rfl) ⟨317703, by rfl⟩ : syracuseStep 3388837 = 635407) (by norm_num)
theorem B1447345 : Blo 1188411 1447345 := bbase (se 2 (by rfl) ⟨542754, by rfl⟩ : syracuseStep 1447345 = 1085509) (by norm_num)
theorem B2676149 : Blo 1188411 2676149 := bbase (se 5 (by rfl) ⟨125444, by rfl⟩ : syracuseStep 2676149 = 250889) (by norm_num)
theorem B1783229 : Blo 1188411 1783229 := bbase (se 3 (by rfl) ⟨334355, by rfl⟩ : syracuseStep 1783229 = 668711) (by norm_num)
theorem B2258381 : Blo 1188411 2258381 := bbase (se 3 (by rfl) ⟨423446, by rfl⟩ : syracuseStep 2258381 = 846893) (by norm_num)
theorem B1783253 : Blo 1188411 1783253 := bbase (se 7 (by rfl) ⟨20897, by rfl⟩ : syracuseStep 1783253 = 41795) (by norm_num)
theorem B14464469 : Blo 1188411 14464469 := bbase (se 7 (by rfl) ⟨169505, by rfl⟩ : syracuseStep 14464469 = 339011) (by norm_num)
theorem B1783277 : Blo 1188411 1783277 := bbase (se 3 (by rfl) ⟨334364, by rfl⟩ : syracuseStep 1783277 = 668729) (by norm_num)
theorem B1504757 : Blo 1188411 1504757 := bbase (se 5 (by rfl) ⟨70535, by rfl⟩ : syracuseStep 1504757 = 141071) (by norm_num)
theorem B2676221 : Blo 1188411 2676221 := bbase (se 3 (by rfl) ⟨501791, by rfl⟩ : syracuseStep 2676221 = 1003583) (by norm_num)
theorem B1783301 : Blo 1188411 1783301 := bbase (se 4 (by rfl) ⟨167184, by rfl⟩ : syracuseStep 1783301 = 334369) (by norm_num)
theorem B1783325 : Blo 1188411 1783325 := bbase (se 3 (by rfl) ⟨334373, by rfl⟩ : syracuseStep 1783325 = 668747) (by norm_num)
theorem B1504813 : Blo 1188411 1504813 := bbase (se 3 (by rfl) ⟨282152, by rfl⟩ : syracuseStep 1504813 = 564305) (by norm_num)
theorem B1783349 : Blo 1188411 1783349 := bbase (se 5 (by rfl) ⟨83594, by rfl⟩ : syracuseStep 1783349 = 167189) (by norm_num)
theorem B2676293 : Blo 1188411 2676293 := bbase (se 4 (by rfl) ⟨250902, by rfl⟩ : syracuseStep 2676293 = 501805) (by norm_num)
theorem B1783373 : Blo 1188411 1783373 := bbase (se 3 (by rfl) ⟨334382, by rfl⟩ : syracuseStep 1783373 = 668765) (by norm_num)
theorem B4011605 : Blo 1188411 4011605 := bbase (se 8 (by rfl) ⟨23505, by rfl⟩ : syracuseStep 4011605 = 47011) (by norm_num)
theorem B1783397 : Blo 1188411 1783397 := bbase (se 4 (by rfl) ⟨167193, by rfl⟩ : syracuseStep 1783397 = 334387) (by norm_num)
theorem B2258533 : Blo 1188411 2258533 := bbase (se 4 (by rfl) ⟨211737, by rfl⟩ : syracuseStep 2258533 = 423475) (by norm_num)
theorem B1783421 : Blo 1188411 1783421 := bbase (se 3 (by rfl) ⟨334391, by rfl⟩ : syracuseStep 1783421 = 668783) (by norm_num)
theorem B1504909 : Blo 1188411 1504909 := bbase (se 3 (by rfl) ⟨282170, by rfl⟩ : syracuseStep 1504909 = 564341) (by norm_num)
theorem B1693325 : Blo 1188411 1693325 := bbase (se 3 (by rfl) ⟨317498, by rfl⟩ : syracuseStep 1693325 = 634997) (by norm_num)
theorem B2676365 : Blo 1188411 2676365 := bbase (se 3 (by rfl) ⟨501818, by rfl⟩ : syracuseStep 2676365 = 1003637) (by norm_num)
theorem B1783445 : Blo 1188411 1783445 := bbase (se 6 (by rfl) ⟨41799, by rfl⟩ : syracuseStep 1783445 = 83599) (by norm_num)
theorem B1783469 : Blo 1188411 1783469 := bbase (se 3 (by rfl) ⟨334400, by rfl⟩ : syracuseStep 1783469 = 668801) (by norm_num)
theorem B1783493 : Blo 1188411 1783493 := bbase (se 4 (by rfl) ⟨167202, by rfl⟩ : syracuseStep 1783493 = 334405) (by norm_num)
theorem B2676437 : Blo 1188411 2676437 := bbase (se 7 (by rfl) ⟨31364, by rfl⟩ : syracuseStep 2676437 = 62729) (by norm_num)
theorem B1783517 : Blo 1188411 1783517 := bbase (se 3 (by rfl) ⟨334409, by rfl⟩ : syracuseStep 1783517 = 668819) (by norm_num)
theorem B1783541 : Blo 1188411 1783541 := bbase (se 5 (by rfl) ⟨83603, by rfl⟩ : syracuseStep 1783541 = 167207) (by norm_num)
theorem B3012349 : Blo 1188411 3012349 := bbase (se 3 (by rfl) ⟨564815, by rfl⟩ : syracuseStep 3012349 = 1129631) (by norm_num)
theorem B1783565 : Blo 1188411 1783565 := bbase (se 3 (by rfl) ⟨334418, by rfl⟩ : syracuseStep 1783565 = 668837) (by norm_num)
theorem B2676509 : Blo 1188411 2676509 := bbase (se 3 (by rfl) ⟨501845, by rfl⟩ : syracuseStep 2676509 = 1003691) (by norm_num)
theorem B1783589 : Blo 1188411 1783589 := bbase (se 4 (by rfl) ⟨167211, by rfl⟩ : syracuseStep 1783589 = 334423) (by norm_num)
theorem B2144045 : Blo 1188411 2144045 := bbase (se 3 (by rfl) ⟨402008, by rfl⟩ : syracuseStep 2144045 = 804017) (by norm_num)
theorem B8132405 : Blo 1188411 8132405 := bbase (se 5 (by rfl) ⟨381206, by rfl⟩ : syracuseStep 8132405 = 762413) (by norm_num)
theorem B1505081 : Blo 1188411 1505081 := bbase (se 2 (by rfl) ⟨564405, by rfl⟩ : syracuseStep 1505081 = 1128811) (by norm_num)
theorem B1783613 : Blo 1188411 1783613 := bbase (se 3 (by rfl) ⟨334427, by rfl⟩ : syracuseStep 1783613 = 668855) (by norm_num)
theorem B1783637 : Blo 1188411 1783637 := bbase (se 9 (by rfl) ⟨5225, by rfl⟩ : syracuseStep 1783637 = 10451) (by norm_num)
theorem B2676581 : Blo 1188411 2676581 := bbase (se 4 (by rfl) ⟨250929, by rfl⟩ : syracuseStep 2676581 = 501859) (by norm_num)
theorem B1783661 : Blo 1188411 1783661 := bbase (se 3 (by rfl) ⟨334436, by rfl⟩ : syracuseStep 1783661 = 668873) (by norm_num)
theorem B3012461 : Blo 1188411 3012461 := bbase (se 3 (by rfl) ⟨564836, by rfl⟩ : syracuseStep 3012461 = 1129673) (by norm_num)
theorem B1505137 : Blo 1188411 1505137 := bbase (se 2 (by rfl) ⟨564426, by rfl⟩ : syracuseStep 1505137 = 1128853) (by norm_num)
theorem B1783685 : Blo 1188411 1783685 := bbase (se 4 (by rfl) ⟨167220, by rfl⟩ : syracuseStep 1783685 = 334441) (by norm_num)
theorem B2258837 : Blo 1188411 2258837 := bbase (se 6 (by rfl) ⟨52941, by rfl⟩ : syracuseStep 2258837 = 105883) (by norm_num)
theorem B1783709 : Blo 1188411 1783709 := bbase (se 3 (by rfl) ⟨334445, by rfl⟩ : syracuseStep 1783709 = 668891) (by norm_num)
theorem B2676653 : Blo 1188411 2676653 := bbase (se 3 (by rfl) ⟨501872, by rfl⟩ : syracuseStep 2676653 = 1003745) (by norm_num)
theorem B5076917 : Blo 1188411 5076917 := bbase (se 5 (by rfl) ⟨237980, by rfl⟩ : syracuseStep 5076917 = 475961) (by norm_num)
theorem B1783733 : Blo 1188411 1783733 := bbase (se 5 (by rfl) ⟨83612, by rfl⟩ : syracuseStep 1783733 = 167225) (by norm_num)
theorem B1783757 : Blo 1188411 1783757 := bbase (se 3 (by rfl) ⟨334454, by rfl⟩ : syracuseStep 1783757 = 668909) (by norm_num)
theorem B1906637 : Blo 1188411 1906637 := bbase (se 3 (by rfl) ⟨357494, by rfl⟩ : syracuseStep 1906637 = 714989) (by norm_num)
theorem B1505233 : Blo 1188411 1505233 := bbase (se 2 (by rfl) ⟨564462, by rfl⟩ : syracuseStep 1505233 = 1128925) (by norm_num)
theorem B1783781 : Blo 1188411 1783781 := bbase (se 4 (by rfl) ⟨167229, by rfl⟩ : syracuseStep 1783781 = 334459) (by norm_num)
theorem B7616501 : Blo 1188411 7616501 := bbase (se 5 (by rfl) ⟨357023, by rfl⟩ : syracuseStep 7616501 = 714047) (by norm_num)
theorem B2676725 : Blo 1188411 2676725 := bbase (se 5 (by rfl) ⟨125471, by rfl⟩ : syracuseStep 2676725 = 250943) (by norm_num)
theorem B1783805 : Blo 1188411 1783805 := bbase (se 3 (by rfl) ⟨334463, by rfl⟩ : syracuseStep 1783805 = 668927) (by norm_num)
theorem B4012037 : Blo 1188411 4012037 := bbase (se 4 (by rfl) ⟨376128, by rfl⟩ : syracuseStep 4012037 = 752257) (by norm_num)
theorem B1783829 : Blo 1188411 1783829 := bbase (se 6 (by rfl) ⟨41808, by rfl⟩ : syracuseStep 1783829 = 83617) (by norm_num)
theorem B6019109 : Blo 1188411 6019109 := bbase (se 4 (by rfl) ⟨564291, by rfl⟩ : syracuseStep 6019109 = 1128583) (by norm_num)
theorem B1783853 : Blo 1188411 1783853 := bbase (se 3 (by rfl) ⟨334472, by rfl⟩ : syracuseStep 1783853 = 668945) (by norm_num)
theorem B3012653 : Blo 1188411 3012653 := bbase (se 3 (by rfl) ⟨564872, by rfl⟩ : syracuseStep 3012653 = 1129745) (by norm_num)
theorem B2676797 : Blo 1188411 2676797 := bbase (se 3 (by rfl) ⟨501899, by rfl⟩ : syracuseStep 2676797 = 1003799) (by norm_num)
theorem B1783877 : Blo 1188411 1783877 := bbase (se 4 (by rfl) ⟨167238, by rfl⟩ : syracuseStep 1783877 = 334477) (by norm_num)
theorem B2144333 : Blo 1188411 2144333 := bbase (se 3 (by rfl) ⟨402062, by rfl⟩ : syracuseStep 2144333 = 804125) (by norm_num)
theorem B3807317 : Blo 1188411 3807317 := bbase (se 8 (by rfl) ⟨22308, by rfl⟩ : syracuseStep 3807317 = 44617) (by norm_num)
theorem B1783901 : Blo 1188411 1783901 := bbase (se 3 (by rfl) ⟨334481, by rfl⟩ : syracuseStep 1783901 = 668963) (by norm_num)
theorem B1783925 : Blo 1188411 1783925 := bbase (se 5 (by rfl) ⟨83621, by rfl⟩ : syracuseStep 1783925 = 167243) (by norm_num)
theorem B1505405 : Blo 1188411 1505405 := bbase (se 3 (by rfl) ⟨282263, by rfl⟩ : syracuseStep 1505405 = 564527) (by norm_num)
theorem B2676869 : Blo 1188411 2676869 := bbase (se 4 (by rfl) ⟨250956, by rfl⟩ : syracuseStep 2676869 = 501913) (by norm_num)
theorem B1783949 : Blo 1188411 1783949 := bbase (se 3 (by rfl) ⟨334490, by rfl⟩ : syracuseStep 1783949 = 668981) (by norm_num)
theorem B2144405 : Blo 1188411 2144405 := bbase (se 6 (by rfl) ⟨50259, by rfl⟩ : syracuseStep 2144405 = 100519) (by norm_num)
theorem B1783973 : Blo 1188411 1783973 := bbase (se 4 (by rfl) ⟨167247, by rfl⟩ : syracuseStep 1783973 = 334495) (by norm_num)
theorem B1505461 : Blo 1188411 1505461 := bbase (se 5 (by rfl) ⟨70568, by rfl⟩ : syracuseStep 1505461 = 141137) (by norm_num)
theorem B1693877 : Blo 1188411 1693877 := bbase (se 5 (by rfl) ⟨79400, by rfl⟩ : syracuseStep 1693877 = 158801) (by norm_num)
theorem B1783997 : Blo 1188411 1783997 := bbase (se 3 (by rfl) ⟨334499, by rfl⟩ : syracuseStep 1783997 = 668999) (by norm_num)
theorem B2676941 : Blo 1188411 2676941 := bbase (se 3 (by rfl) ⟨501926, by rfl⟩ : syracuseStep 2676941 = 1003853) (by norm_num)
theorem B1784021 : Blo 1188411 1784021 := bbase (se 7 (by rfl) ⟨20906, by rfl⟩ : syracuseStep 1784021 = 41813) (by norm_num)
theorem B1784045 : Blo 1188411 1784045 := bbase (se 3 (by rfl) ⟨334508, by rfl⟩ : syracuseStep 1784045 = 669017) (by norm_num)
theorem B1784069 : Blo 1188411 1784069 := bbase (se 4 (by rfl) ⟨167256, by rfl⟩ : syracuseStep 1784069 = 334513) (by norm_num)
theorem B1505557 : Blo 1188411 1505557 := bbase (se 6 (by rfl) ⟨35286, by rfl⟩ : syracuseStep 1505557 = 70573) (by norm_num)
theorem B2677013 : Blo 1188411 2677013 := bbase (se 6 (by rfl) ⟨62742, by rfl⟩ : syracuseStep 2677013 = 125485) (by norm_num)
theorem B1784093 : Blo 1188411 1784093 := bbase (se 3 (by rfl) ⟨334517, by rfl⟩ : syracuseStep 1784093 = 669035) (by norm_num)
theorem B1784117 : Blo 1188411 1784117 := bbase (se 5 (by rfl) ⟨83630, by rfl⟩ : syracuseStep 1784117 = 167261) (by norm_num)
theorem B2857285 : Blo 1188411 2857285 := bbase (se 4 (by rfl) ⟨267870, by rfl⟩ : syracuseStep 2857285 = 535741) (by norm_num)
theorem B1784141 : Blo 1188411 1784141 := bbase (se 3 (by rfl) ⟨334526, by rfl⟩ : syracuseStep 1784141 = 669053) (by norm_num)
theorem B2677085 : Blo 1188411 2677085 := bbase (se 3 (by rfl) ⟨501953, by rfl⟩ : syracuseStep 2677085 = 1003907) (by norm_num)
theorem B1784165 : Blo 1188411 1784165 := bbase (se 4 (by rfl) ⟨167265, by rfl⟩ : syracuseStep 1784165 = 334531) (by norm_num)
theorem B1784189 : Blo 1188411 1784189 := bbase (se 3 (by rfl) ⟨334535, by rfl⟩ : syracuseStep 1784189 = 669071) (by norm_num)
theorem B3012997 : Blo 1188411 3012997 := bbase (se 4 (by rfl) ⟨282468, by rfl⟩ : syracuseStep 3012997 = 564937) (by norm_num)
theorem B1784213 : Blo 1188411 1784213 := bbase (se 6 (by rfl) ⟨41817, by rfl⟩ : syracuseStep 1784213 = 83635) (by norm_num)
theorem B10164629 : Blo 1188411 10164629 := bbase (se 6 (by rfl) ⟨238233, by rfl⟩ : syracuseStep 10164629 = 476467) (by norm_num)
theorem B2677157 : Blo 1188411 2677157 := bbase (se 4 (by rfl) ⟨250983, by rfl⟩ : syracuseStep 2677157 = 501967) (by norm_num)
theorem B1784237 : Blo 1188411 1784237 := bbase (se 3 (by rfl) ⟨334544, by rfl⟩ : syracuseStep 1784237 = 669089) (by norm_num)
theorem B4012469 : Blo 1188411 4012469 := bbase (se 5 (by rfl) ⟨188084, by rfl⟩ : syracuseStep 4012469 = 376169) (by norm_num)
theorem B1505729 : Blo 1188411 1505729 := bbase (se 2 (by rfl) ⟨564648, by rfl⟩ : syracuseStep 1505729 = 1129297) (by norm_num)
theorem B2005445 : Blo 1188411 2005445 := bbase (se 4 (by rfl) ⟨188010, by rfl⟩ : syracuseStep 2005445 = 376021) (by norm_num)
theorem B1784261 : Blo 1188411 1784261 := bbase (se 4 (by rfl) ⟨167274, by rfl⟩ : syracuseStep 1784261 = 334549) (by norm_num)
theorem B1784285 : Blo 1188411 1784285 := bbase (se 3 (by rfl) ⟨334553, by rfl⟩ : syracuseStep 1784285 = 669107) (by norm_num)
theorem B5716453 : Blo 1188411 5716453 := bbase (se 4 (by rfl) ⟨535917, by rfl⟩ : syracuseStep 5716453 = 1071835) (by norm_num)
theorem B2677229 : Blo 1188411 2677229 := bbase (se 3 (by rfl) ⟨501980, by rfl⟩ : syracuseStep 2677229 = 1003961) (by norm_num)
theorem B1784309 : Blo 1188411 1784309 := bbase (se 5 (by rfl) ⟨83639, by rfl⟩ : syracuseStep 1784309 = 167279) (by norm_num)
theorem B3013109 : Blo 1188411 3013109 := bbase (se 5 (by rfl) ⟨141239, by rfl⟩ : syracuseStep 3013109 = 282479) (by norm_num)
theorem B1505785 : Blo 1188411 1505785 := bbase (se 2 (by rfl) ⟨564669, by rfl⟩ : syracuseStep 1505785 = 1129339) (by norm_num)
theorem B1784333 : Blo 1188411 1784333 := bbase (se 3 (by rfl) ⟨334562, by rfl⟩ : syracuseStep 1784333 = 669125) (by norm_num)
theorem B1784357 : Blo 1188411 1784357 := bbase (se 4 (by rfl) ⟨167283, by rfl⟩ : syracuseStep 1784357 = 334567) (by norm_num)
theorem B2677301 : Blo 1188411 2677301 := bbase (se 5 (by rfl) ⟨125498, by rfl⟩ : syracuseStep 2677301 = 250997) (by norm_num)
theorem B1784381 : Blo 1188411 1784381 := bbase (se 3 (by rfl) ⟨334571, by rfl⟩ : syracuseStep 1784381 = 669143) (by norm_num)
theorem B2005573 : Blo 1188411 2005573 := bbase (se 4 (by rfl) ⟨188022, by rfl⟩ : syracuseStep 2005573 = 376045) (by norm_num)
theorem B1784405 : Blo 1188411 1784405 := bbase (se 8 (by rfl) ⟨10455, by rfl⟩ : syracuseStep 1784405 = 20911) (by norm_num)
theorem B26434133 : Blo 1188411 26434133 := bbase (se 8 (by rfl) ⟨154887, by rfl⟩ : syracuseStep 26434133 = 309775) (by norm_num)
theorem B1505881 : Blo 1188411 1505881 := bbase (se 2 (by rfl) ⟨564705, by rfl⟩ : syracuseStep 1505881 = 1129411) (by norm_num)
theorem B1784429 : Blo 1188411 1784429 := bbase (se 3 (by rfl) ⟨334580, by rfl⟩ : syracuseStep 1784429 = 669161) (by norm_num)
theorem B2677373 : Blo 1188411 2677373 := bbase (se 3 (by rfl) ⟨502007, by rfl⟩ : syracuseStep 2677373 = 1004015) (by norm_num)
theorem B1784453 : Blo 1188411 1784453 := bbase (se 4 (by rfl) ⟨167292, by rfl⟩ : syracuseStep 1784453 = 334585) (by norm_num)
theorem B2259589 : Blo 1188411 2259589 := bbase (se 4 (by rfl) ⟨211836, by rfl⟩ : syracuseStep 2259589 = 423673) (by norm_num)
theorem B3054229 : Blo 1188411 3054229 := bbase (se 6 (by rfl) ⟨71583, by rfl⟩ : syracuseStep 3054229 = 143167) (by norm_num)
theorem B2005661 : Blo 1188411 2005661 := bbase (se 3 (by rfl) ⟨376061, by rfl⟩ : syracuseStep 2005661 = 752123) (by norm_num)
theorem B1784477 : Blo 1188411 1784477 := bbase (se 3 (by rfl) ⟨334589, by rfl⟩ : syracuseStep 1784477 = 669179) (by norm_num)
theorem B6429365 : Blo 1188411 6429365 := bbase (se 5 (by rfl) ⟨301376, by rfl⟩ : syracuseStep 6429365 = 602753) (by norm_num)
theorem B1784501 : Blo 1188411 1784501 := bbase (se 5 (by rfl) ⟨83648, by rfl⟩ : syracuseStep 1784501 = 167297) (by norm_num)
theorem B6273733 : Blo 1188411 6273733 := bbase (se 4 (by rfl) ⟨588162, by rfl⟩ : syracuseStep 6273733 = 1176325) (by norm_num)
theorem B2677445 : Blo 1188411 2677445 := bbase (se 4 (by rfl) ⟨251010, by rfl⟩ : syracuseStep 2677445 = 502021) (by norm_num)
theorem B1784525 : Blo 1188411 1784525 := bbase (se 3 (by rfl) ⟨334598, by rfl⟩ : syracuseStep 1784525 = 669197) (by norm_num)
theorem B1784549 : Blo 1188411 1784549 := bbase (se 4 (by rfl) ⟨167301, by rfl⟩ : syracuseStep 1784549 = 334603) (by norm_num)
theorem B1784573 : Blo 1188411 1784573 := bbase (se 3 (by rfl) ⟨334607, by rfl⟩ : syracuseStep 1784573 = 669215) (by norm_num)
theorem B1506053 : Blo 1188411 1506053 := bbase (se 4 (by rfl) ⟨141192, by rfl⟩ : syracuseStep 1506053 = 282385) (by norm_num)
theorem B2538253 : Blo 1188411 2538253 := bbase (se 3 (by rfl) ⟨475922, by rfl⟩ : syracuseStep 2538253 = 951845) (by norm_num)
theorem B2677517 : Blo 1188411 2677517 := bbase (se 3 (by rfl) ⟨502034, by rfl⟩ : syracuseStep 2677517 = 1004069) (by norm_num)
theorem B1784597 : Blo 1188411 1784597 := bbase (se 6 (by rfl) ⟨41826, by rfl⟩ : syracuseStep 1784597 = 83653) (by norm_num)
theorem B2259733 : Blo 1188411 2259733 := bbase (se 6 (by rfl) ⟨52962, by rfl⟩ : syracuseStep 2259733 = 105925) (by norm_num)
theorem B2005789 : Blo 1188411 2005789 := bbase (se 3 (by rfl) ⟨376085, by rfl⟩ : syracuseStep 2005789 = 752171) (by norm_num)
theorem B1784621 : Blo 1188411 1784621 := bbase (se 3 (by rfl) ⟨334616, by rfl⟩ : syracuseStep 1784621 = 669233) (by norm_num)
theorem B1506109 : Blo 1188411 1506109 := bbase (se 3 (by rfl) ⟨282395, by rfl⟩ : syracuseStep 1506109 = 564791) (by norm_num)
theorem B1784645 : Blo 1188411 1784645 := bbase (se 4 (by rfl) ⟨167310, by rfl⟩ : syracuseStep 1784645 = 334621) (by norm_num)
theorem B2677589 : Blo 1188411 2677589 := bbase (se 9 (by rfl) ⟨7844, by rfl⟩ : syracuseStep 2677589 = 15689) (by norm_num)
theorem B1784669 : Blo 1188411 1784669 := bbase (se 3 (by rfl) ⟨334625, by rfl⟩ : syracuseStep 1784669 = 669251) (by norm_num)
theorem B4012901 : Blo 1188411 4012901 := bbase (se 4 (by rfl) ⟨376209, by rfl⟩ : syracuseStep 4012901 = 752419) (by norm_num)
theorem B2005877 : Blo 1188411 2005877 := bbase (se 5 (by rfl) ⟨94025, by rfl⟩ : syracuseStep 2005877 = 188051) (by norm_num)
theorem B1784693 : Blo 1188411 1784693 := bbase (se 5 (by rfl) ⟨83657, by rfl⟩ : syracuseStep 1784693 = 167315) (by norm_num)
theorem B2538373 : Blo 1188411 2538373 := bbase (se 4 (by rfl) ⟨237972, by rfl⟩ : syracuseStep 2538373 = 475945) (by norm_num)
theorem B1784717 : Blo 1188411 1784717 := bbase (se 3 (by rfl) ⟨334634, by rfl⟩ : syracuseStep 1784717 = 669269) (by norm_num)
theorem B2063261 : Blo 1188411 2063261 := bbase (se 3 (by rfl) ⟨386861, by rfl⟩ : syracuseStep 2063261 = 773723) (by norm_num)
theorem B2677661 : Blo 1188411 2677661 := bbase (se 3 (by rfl) ⟨502061, by rfl⟩ : syracuseStep 2677661 = 1004123) (by norm_num)
theorem B1506205 : Blo 1188411 1506205 := bbase (se 3 (by rfl) ⟨282413, by rfl⟩ : syracuseStep 1506205 = 564827) (by norm_num)
theorem B5790629 : Blo 1188411 5790629 := bbase (se 4 (by rfl) ⟨542871, by rfl⟩ : syracuseStep 5790629 = 1085743) (by norm_num)
theorem B1784741 : Blo 1188411 1784741 := bbase (se 4 (by rfl) ⟨167319, by rfl⟩ : syracuseStep 1784741 = 334639) (by norm_num)
theorem B1694629 : Blo 1188411 1694629 := bbase (se 4 (by rfl) ⟨158871, by rfl⟩ : syracuseStep 1694629 = 317743) (by norm_num)
theorem B2259893 : Blo 1188411 2259893 := bbase (se 5 (by rfl) ⟨105932, by rfl⟩ : syracuseStep 2259893 = 211865) (by norm_num)
theorem B1784765 : Blo 1188411 1784765 := bbase (se 3 (by rfl) ⟨334643, by rfl⟩ : syracuseStep 1784765 = 669287) (by norm_num)
theorem B1784789 : Blo 1188411 1784789 := bbase (se 7 (by rfl) ⟨20915, by rfl⟩ : syracuseStep 1784789 = 41831) (by norm_num)
theorem B2857949 : Blo 1188411 2857949 := bbase (se 3 (by rfl) ⟨535865, by rfl⟩ : syracuseStep 2857949 = 1071731) (by norm_num)
theorem B2677733 : Blo 1188411 2677733 := bbase (se 4 (by rfl) ⟨251037, by rfl⟩ : syracuseStep 2677733 = 502075) (by norm_num)
theorem B1784813 : Blo 1188411 1784813 := bbase (se 3 (by rfl) ⟨334652, by rfl⟩ : syracuseStep 1784813 = 669305) (by norm_num)
theorem B2006005 : Blo 1188411 2006005 := bbase (se 5 (by rfl) ⟨94031, by rfl⟩ : syracuseStep 2006005 = 188063) (by norm_num)
theorem B1784837 : Blo 1188411 1784837 := bbase (se 4 (by rfl) ⟨167328, by rfl⟩ : syracuseStep 1784837 = 334657) (by norm_num)
theorem B1784861 : Blo 1188411 1784861 := bbase (se 3 (by rfl) ⟨334661, by rfl⟩ : syracuseStep 1784861 = 669323) (by norm_num)
theorem B2677805 : Blo 1188411 2677805 := bbase (se 3 (by rfl) ⟨502088, by rfl⟩ : syracuseStep 2677805 = 1004177) (by norm_num)
theorem B1784885 : Blo 1188411 1784885 := bbase (se 5 (by rfl) ⟨83666, by rfl⟩ : syracuseStep 1784885 = 167333) (by norm_num)
theorem B1506377 : Blo 1188411 1506377 := bbase (se 2 (by rfl) ⟨564891, by rfl⟩ : syracuseStep 1506377 = 1129783) (by norm_num)
theorem B2006093 : Blo 1188411 2006093 := bbase (se 3 (by rfl) ⟨376142, by rfl⟩ : syracuseStep 2006093 = 752285) (by norm_num)
theorem B1784909 : Blo 1188411 1784909 := bbase (se 3 (by rfl) ⟨334670, by rfl⟩ : syracuseStep 1784909 = 669341) (by norm_num)
theorem B1784933 : Blo 1188411 1784933 := bbase (se 4 (by rfl) ⟨167337, by rfl⟩ : syracuseStep 1784933 = 334675) (by norm_num)
theorem B2677877 : Blo 1188411 2677877 := bbase (se 5 (by rfl) ⟨125525, by rfl⟩ : syracuseStep 2677877 = 251051) (by norm_num)
theorem B1784957 : Blo 1188411 1784957 := bbase (se 3 (by rfl) ⟨334679, by rfl⟩ : syracuseStep 1784957 = 669359) (by norm_num)
theorem B1506433 : Blo 1188411 1506433 := bbase (se 2 (by rfl) ⟨564912, by rfl⟩ : syracuseStep 1506433 = 1129825) (by norm_num)
theorem B2538629 : Blo 1188411 2538629 := bbase (se 4 (by rfl) ⟨237996, by rfl⟩ : syracuseStep 2538629 = 475993) (by norm_num)
theorem B1784981 : Blo 1188411 1784981 := bbase (se 6 (by rfl) ⟨41835, by rfl⟩ : syracuseStep 1784981 = 83671) (by norm_num)
theorem B1785005 : Blo 1188411 1785005 := bbase (se 3 (by rfl) ⟨334688, by rfl⟩ : syracuseStep 1785005 = 669377) (by norm_num)
theorem B2677949 : Blo 1188411 2677949 := bbase (se 3 (by rfl) ⟨502115, by rfl⟩ : syracuseStep 2677949 = 1004231) (by norm_num)
theorem B1785029 : Blo 1188411 1785029 := bbase (se 4 (by rfl) ⟨167346, by rfl⟩ : syracuseStep 1785029 = 334693) (by norm_num)
theorem B2006221 : Blo 1188411 2006221 := bbase (se 3 (by rfl) ⟨376166, by rfl⟩ : syracuseStep 2006221 = 752333) (by norm_num)
theorem B1785053 : Blo 1188411 1785053 := bbase (se 3 (by rfl) ⟨334697, by rfl⟩ : syracuseStep 1785053 = 669395) (by norm_num)
theorem B1506529 : Blo 1188411 1506529 := bbase (se 2 (by rfl) ⟨564948, by rfl⟩ : syracuseStep 1506529 = 1129897) (by norm_num)
theorem B1785077 : Blo 1188411 1785077 := bbase (se 5 (by rfl) ⟨83675, by rfl⟩ : syracuseStep 1785077 = 167351) (by norm_num)
theorem B2678021 : Blo 1188411 2678021 := bbase (se 4 (by rfl) ⟨251064, by rfl⟩ : syracuseStep 2678021 = 502129) (by norm_num)
theorem B1785101 : Blo 1188411 1785101 := bbase (se 3 (by rfl) ⟨334706, by rfl⟩ : syracuseStep 1785101 = 669413) (by norm_num)
theorem B4013333 : Blo 1188411 4013333 := bbase (se 6 (by rfl) ⟨94062, by rfl⟩ : syracuseStep 4013333 = 188125) (by norm_num)
theorem B2006309 : Blo 1188411 2006309 := bbase (se 4 (by rfl) ⟨188091, by rfl⟩ : syracuseStep 2006309 = 376183) (by norm_num)
theorem B1785125 : Blo 1188411 1785125 := bbase (se 4 (by rfl) ⟨167355, by rfl⟩ : syracuseStep 1785125 = 334711) (by norm_num)
theorem B6020405 : Blo 1188411 6020405 := bbase (se 5 (by rfl) ⟨282206, by rfl⟩ : syracuseStep 6020405 = 564413) (by norm_num)
theorem B1785149 : Blo 1188411 1785149 := bbase (se 3 (by rfl) ⟨334715, by rfl⟩ : syracuseStep 1785149 = 669431) (by norm_num)
theorem B2678093 : Blo 1188411 2678093 := bbase (se 3 (by rfl) ⟨502142, by rfl⟩ : syracuseStep 2678093 = 1004285) (by norm_num)
theorem B1785173 : Blo 1188411 1785173 := bbase (se 11 (by rfl) ⟨1307, by rfl⟩ : syracuseStep 1785173 = 2615) (by norm_num)
theorem B1785197 : Blo 1188411 1785197 := bbase (se 3 (by rfl) ⟨334724, by rfl⟩ : syracuseStep 1785197 = 669449) (by norm_num)
theorem B1785221 : Blo 1188411 1785221 := bbase (se 4 (by rfl) ⟨167364, by rfl⟩ : syracuseStep 1785221 = 334729) (by norm_num)
theorem B2751877 : Blo 1188411 2751877 := bbase (se 4 (by rfl) ⟨257988, by rfl⟩ : syracuseStep 2751877 = 515977) (by norm_num)
theorem B2678165 : Blo 1188411 2678165 := bbase (se 6 (by rfl) ⟨62769, by rfl⟩ : syracuseStep 2678165 = 125539) (by norm_num)
theorem B1785245 : Blo 1188411 1785245 := bbase (se 3 (by rfl) ⟨334733, by rfl⟩ : syracuseStep 1785245 = 669467) (by norm_num)
theorem B2006437 : Blo 1188411 2006437 := bbase (se 4 (by rfl) ⟨188103, by rfl⟩ : syracuseStep 2006437 = 376207) (by norm_num)
theorem B1785269 : Blo 1188411 1785269 := bbase (se 5 (by rfl) ⟨83684, by rfl⟩ : syracuseStep 1785269 = 167369) (by norm_num)
theorem B1785293 : Blo 1188411 1785293 := bbase (se 3 (by rfl) ⟨334742, by rfl⟩ : syracuseStep 1785293 = 669485) (by norm_num)
theorem B2678237 : Blo 1188411 2678237 := bbase (se 3 (by rfl) ⟨502169, by rfl⟩ : syracuseStep 2678237 = 1004339) (by norm_num)
theorem B1785317 : Blo 1188411 1785317 := bbase (se 4 (by rfl) ⟨167373, by rfl⟩ : syracuseStep 1785317 = 334747) (by norm_num)
theorem B2006525 : Blo 1188411 2006525 := bbase (se 3 (by rfl) ⟨376223, by rfl⟩ : syracuseStep 2006525 = 752447) (by norm_num)
theorem B1785341 : Blo 1188411 1785341 := bbase (se 3 (by rfl) ⟨334751, by rfl⟩ : syracuseStep 1785341 = 669503) (by norm_num)
theorem B1785365 : Blo 1188411 1785365 := bbase (se 6 (by rfl) ⟨41844, by rfl⟩ : syracuseStep 1785365 = 83689) (by norm_num)
theorem B1629733 : Blo 1188411 1629733 := bbase (se 4 (by rfl) ⟨152787, by rfl⟩ : syracuseStep 1629733 = 305575) (by norm_num)
theorem B2678309 : Blo 1188411 2678309 := bbase (se 4 (by rfl) ⟨251091, by rfl⟩ : syracuseStep 2678309 = 502183) (by norm_num)
theorem B1785389 : Blo 1188411 1785389 := bbase (se 3 (by rfl) ⟨334760, by rfl⟩ : syracuseStep 1785389 = 669521) (by norm_num)
theorem B1785413 : Blo 1188411 1785413 := bbase (se 4 (by rfl) ⟨167382, by rfl⟩ : syracuseStep 1785413 = 334765) (by norm_num)
theorem B15236693 : Blo 1188411 15236693 := bbase (se 8 (by rfl) ⟨89277, by rfl⟩ : syracuseStep 15236693 = 178555) (by norm_num)
theorem B1785437 : Blo 1188411 1785437 := bbase (se 3 (by rfl) ⟨334769, by rfl⟩ : syracuseStep 1785437 = 669539) (by norm_num)
theorem B2678381 : Blo 1188411 2678381 := bbase (se 3 (by rfl) ⟨502196, by rfl⟩ : syracuseStep 2678381 = 1004393) (by norm_num)
theorem B1785461 : Blo 1188411 1785461 := bbase (se 5 (by rfl) ⟨83693, by rfl⟩ : syracuseStep 1785461 = 167387) (by norm_num)
theorem B2006653 : Blo 1188411 2006653 := bbase (se 3 (by rfl) ⟨376247, by rfl⟩ : syracuseStep 2006653 = 752495) (by norm_num)
theorem B1785485 : Blo 1188411 1785485 := bbase (se 3 (by rfl) ⟨334778, by rfl⟩ : syracuseStep 1785485 = 669557) (by norm_num)
theorem B4284053 : Blo 1188411 4284053 := bbase (se 6 (by rfl) ⟨100407, by rfl⟩ : syracuseStep 4284053 = 200815) (by norm_num)
theorem B5078693 : Blo 1188411 5078693 := bbase (se 4 (by rfl) ⟨476127, by rfl⟩ : syracuseStep 5078693 = 952255) (by norm_num)
theorem B1785509 : Blo 1188411 1785509 := bbase (se 4 (by rfl) ⟨167391, by rfl⟩ : syracuseStep 1785509 = 334783) (by norm_num)
theorem B1785533 : Blo 1188411 1785533 := bbase (se 3 (by rfl) ⟨334787, by rfl⟩ : syracuseStep 1785533 = 669575) (by norm_num)
theorem B4013765 : Blo 1188411 4013765 := bbase (se 4 (by rfl) ⟨376290, by rfl⟩ : syracuseStep 4013765 = 752581) (by norm_num)
theorem B2006741 : Blo 1188411 2006741 := bbase (se 7 (by rfl) ⟨23516, by rfl⟩ : syracuseStep 2006741 = 47033) (by norm_num)
theorem B1785557 : Blo 1188411 1785557 := bbase (se 7 (by rfl) ⟨20924, by rfl⟩ : syracuseStep 1785557 = 41849) (by norm_num)
theorem B1785581 : Blo 1188411 1785581 := bbase (se 3 (by rfl) ⟨334796, by rfl⟩ : syracuseStep 1785581 = 669593) (by norm_num)
theorem B1785605 : Blo 1188411 1785605 := bbase (se 4 (by rfl) ⟨167400, by rfl⟩ : syracuseStep 1785605 = 334801) (by norm_num)
theorem B4513589 : Blo 1188411 4513589 := bbase (se 5 (by rfl) ⟨211574, by rfl⟩ : syracuseStep 4513589 = 423149) (by norm_num)
theorem B75210581 : Blo 1188411 75210581 := bbase (se 9 (by rfl) ⟨220343, by rfl⟩ : syracuseStep 75210581 = 440687) (by norm_num)
theorem B2006869 : Blo 1188411 2006869 := bbase (se 9 (by rfl) ⟨5879, by rfl⟩ : syracuseStep 2006869 = 11759) (by norm_num)
theorem B1269605 : Blo 1188411 1269605 := bbase (se 4 (by rfl) ⟨119025, by rfl⟩ : syracuseStep 1269605 = 238051) (by norm_num)
theorem B5078933 : Blo 1188411 5078933 := bbase (se 6 (by rfl) ⟨119037, by rfl⟩ : syracuseStep 5078933 = 238075) (by norm_num)
theorem B2006957 : Blo 1188411 2006957 := bbase (se 3 (by rfl) ⟨376304, by rfl⟩ : syracuseStep 2006957 = 752609) (by norm_num)
theorem B10878965 : Blo 1188411 10878965 := bbase (se 5 (by rfl) ⟨509951, by rfl⟩ : syracuseStep 10878965 = 1019903) (by norm_num)
theorem B2539517 : Blo 1188411 2539517 := bbase (se 3 (by rfl) ⟨476159, by rfl⟩ : syracuseStep 2539517 = 952319) (by norm_num)
theorem B2007139 : Blo 1188411 2007139 := bstep (se 1 (by rfl) ⟨1505354, by rfl⟩ : syracuseStep 2007139 = 3010709) B3010709
theorem B6774961 : Blo 1188411 6774961 := bstep (se 2 (by rfl) ⟨2540610, by rfl⟩ : syracuseStep 6774961 = 5081221) B5081221
theorem B13557941 : Blo 1188411 13557941 := bstep (se 5 (by rfl) ⟨635528, by rfl⟩ : syracuseStep 13557941 = 1271057) B1271057
theorem B5718221 : Blo 1188411 5718221 := bstep (se 3 (by rfl) ⟨1072166, by rfl⟩ : syracuseStep 5718221 = 2144333) B2144333
theorem B2007281 : Blo 1188411 2007281 := bstep (se 2 (by rfl) ⟨752730, by rfl⟩ : syracuseStep 2007281 = 1505461) B1505461
theorem B4014413 : Blo 1188411 4014413 := bstep (se 3 (by rfl) ⟨752702, by rfl⟩ : syracuseStep 4014413 = 1505405) B1505405
theorem B2007409 : Blo 1188411 2007409 := bstep (se 2 (by rfl) ⟨752778, by rfl⟩ : syracuseStep 2007409 = 1505557) B1505557
theorem B4014467 : Blo 1188411 4014467 := bstep (se 1 (by rfl) ⟨3010850, by rfl⟩ : syracuseStep 4014467 = 6021701) B6021701
theorem B8249741 : Blo 1188411 8249741 := bstep (se 3 (by rfl) ⟨1546826, by rfl⟩ : syracuseStep 8249741 = 3093653) B3093653
theorem B5718413 : Blo 1188411 5718413 := bstep (se 3 (by rfl) ⟨1072202, by rfl⟩ : syracuseStep 5718413 = 2144405) B2144405
theorem B2007443 : Blo 1188411 2007443 := bstep (se 1 (by rfl) ⟨1505582, by rfl⟩ : syracuseStep 2007443 = 3011165) B3011165
theorem B2711971 : Blo 1188411 2711971 := bstep (se 1 (by rfl) ⟨2033978, by rfl⟩ : syracuseStep 2711971 = 4067957) B4067957
theorem B6021539 : Blo 1188411 6021539 := bstep (se 1 (by rfl) ⟨4516154, by rfl⟩ : syracuseStep 6021539 = 9032309) B9032309
theorem B3809713 : Blo 1188411 3809713 := bstep (se 2 (by rfl) ⟨1428642, by rfl⟩ : syracuseStep 3809713 = 2857285) B2857285
theorem B2712017 : Blo 1188411 2712017 := bstep (se 2 (by rfl) ⟨1017006, by rfl⟩ : syracuseStep 2712017 = 2034013) B2034013
theorem B2007571 : Blo 1188411 2007571 := bstep (se 1 (by rfl) ⟨1505678, by rfl⟩ : syracuseStep 2007571 = 3011357) B3011357
theorem B6431267 : Blo 1188411 6431267 := bstep (se 1 (by rfl) ⟨4823450, by rfl⟩ : syracuseStep 6431267 = 9646901) B9646901
theorem B7725617 : Blo 1188411 7725617 := bstep (se 2 (by rfl) ⟨2897106, by rfl⟩ : syracuseStep 7725617 = 5794213) B5794213
theorem B1188419 : Blo 1188411 1188419 := bstep (se 1 (by rfl) ⟨891314, by rfl⟩ : syracuseStep 1188419 = 1782629) B1782629
theorem B2540099 : Blo 1188411 2540099 := bstep (se 1 (by rfl) ⟨1905074, by rfl⟩ : syracuseStep 2540099 = 3810149) B3810149
theorem B1188435 : Blo 1188411 1188435 := bstep (se 1 (by rfl) ⟨891326, by rfl⟩ : syracuseStep 1188435 = 1782653) B1782653
theorem B1188451 : Blo 1188411 1188451 := bstep (se 1 (by rfl) ⟨891338, by rfl⟩ : syracuseStep 1188451 = 1782677) B1782677
theorem B3809891 : Blo 1188411 3809891 := bstep (se 1 (by rfl) ⟨2857418, by rfl⟩ : syracuseStep 3809891 = 5714837) B5714837
theorem B1188467 : Blo 1188411 1188467 := bstep (se 1 (by rfl) ⟨891350, by rfl⟩ : syracuseStep 1188467 = 1782701) B1782701
theorem B1188483 : Blo 1188411 1188483 := bstep (se 1 (by rfl) ⟨891362, by rfl⟩ : syracuseStep 1188483 = 1782725) B1782725
theorem B8577677 : Blo 1188411 8577677 := bstep (se 3 (by rfl) ⟨1608314, by rfl⟩ : syracuseStep 8577677 = 3216629) B3216629
theorem B4014737 : Blo 1188411 4014737 := bstep (se 2 (by rfl) ⟨1505526, by rfl⟩ : syracuseStep 4014737 = 3011053) B3011053
theorem B1188499 : Blo 1188411 1188499 := bstep (se 1 (by rfl) ⟨891374, by rfl⟩ : syracuseStep 1188499 = 1782749) B1782749
theorem B2007713 : Blo 1188411 2007713 := bstep (se 2 (by rfl) ⟨752892, by rfl⟩ : syracuseStep 2007713 = 1505785) B1505785
theorem B1188515 : Blo 1188411 1188515 := bstep (se 1 (by rfl) ⟨891386, by rfl⟩ : syracuseStep 1188515 = 1782773) B1782773
theorem B1188531 : Blo 1188411 1188531 := bstep (se 1 (by rfl) ⟨891398, by rfl⟩ : syracuseStep 1188531 = 1782797) B1782797
theorem B1270451 : Blo 1188411 1270451 := bstep (se 1 (by rfl) ⟨952838, by rfl⟩ : syracuseStep 1270451 = 1905677) B1905677
theorem B1188547 : Blo 1188411 1188547 := bstep (se 1 (by rfl) ⟨891410, by rfl⟩ : syracuseStep 1188547 = 1782821) B1782821
theorem B1188563 : Blo 1188411 1188563 := bstep (se 1 (by rfl) ⟨891422, by rfl⟩ : syracuseStep 1188563 = 1782845) B1782845
theorem B1188579 : Blo 1188411 1188579 := bstep (se 1 (by rfl) ⟨891434, by rfl⟩ : syracuseStep 1188579 = 1782869) B1782869
theorem B14467825 : Blo 1188411 14467825 := bstep (se 2 (by rfl) ⟨5425434, by rfl⟩ : syracuseStep 14467825 = 10850869) B10850869
theorem B1188595 : Blo 1188411 1188595 := bstep (se 1 (by rfl) ⟨891446, by rfl⟩ : syracuseStep 1188595 = 1782893) B1782893
theorem B1188611 : Blo 1188411 1188611 := bstep (se 1 (by rfl) ⟨891458, by rfl⟩ : syracuseStep 1188611 = 1782917) B1782917
theorem B3261197 : Blo 1188411 3261197 := bstep (se 3 (by rfl) ⟨611474, by rfl⟩ : syracuseStep 3261197 = 1222949) B1222949
theorem B1188627 : Blo 1188411 1188627 := bstep (se 1 (by rfl) ⟨891470, by rfl⟩ : syracuseStep 1188627 = 1782941) B1782941
theorem B2007841 : Blo 1188411 2007841 := bstep (se 2 (by rfl) ⟨752940, by rfl⟩ : syracuseStep 2007841 = 1505881) B1505881
theorem B1188643 : Blo 1188411 1188643 := bstep (se 1 (by rfl) ⟨891482, by rfl⟩ : syracuseStep 1188643 = 1782965) B1782965
theorem B1188659 : Blo 1188411 1188659 := bstep (se 1 (by rfl) ⟨891494, by rfl⟩ : syracuseStep 1188659 = 1782989) B1782989
theorem B1188675 : Blo 1188411 1188675 := bstep (se 1 (by rfl) ⟨891506, by rfl⟩ : syracuseStep 1188675 = 1783013) B1783013
theorem B2007875 : Blo 1188411 2007875 := bstep (se 1 (by rfl) ⟨1505906, by rfl⟩ : syracuseStep 2007875 = 3011813) B3011813
theorem B9028421 : Blo 1188411 9028421 := bstep (se 4 (by rfl) ⟨846414, by rfl⟩ : syracuseStep 9028421 = 1692829) B1692829
theorem B1188691 : Blo 1188411 1188691 := bstep (se 1 (by rfl) ⟨891518, by rfl⟩ : syracuseStep 1188691 = 1783037) B1783037
theorem B1188707 : Blo 1188411 1188707 := bstep (se 1 (by rfl) ⟨891530, by rfl⟩ : syracuseStep 1188707 = 1783061) B1783061
theorem B1188723 : Blo 1188411 1188723 := bstep (se 1 (by rfl) ⟨891542, by rfl⟩ : syracuseStep 1188723 = 1783085) B1783085
theorem B1188739 : Blo 1188411 1188739 := bstep (se 1 (by rfl) ⟨891554, by rfl⟩ : syracuseStep 1188739 = 1783109) B1783109
theorem B1188755 : Blo 1188411 1188755 := bstep (se 1 (by rfl) ⟨891566, by rfl⟩ : syracuseStep 1188755 = 1783133) B1783133
theorem B1188771 : Blo 1188411 1188771 := bstep (se 1 (by rfl) ⟨891578, by rfl⟩ : syracuseStep 1188771 = 1783157) B1783157
theorem B8364977 : Blo 1188411 8364977 := bstep (se 2 (by rfl) ⟨3136866, by rfl⟩ : syracuseStep 8364977 = 6273733) B6273733
theorem B1188787 : Blo 1188411 1188787 := bstep (se 1 (by rfl) ⟨891590, by rfl⟩ : syracuseStep 1188787 = 1783181) B1783181
theorem B1188803 : Blo 1188411 1188803 := bstep (se 1 (by rfl) ⟨891602, by rfl⟩ : syracuseStep 1188803 = 1783205) B1783205
theorem B2008003 : Blo 1188411 2008003 := bstep (se 1 (by rfl) ⟨1506002, by rfl⟩ : syracuseStep 2008003 = 3012005) B3012005
theorem B1188819 : Blo 1188411 1188819 := bstep (se 1 (by rfl) ⟨891614, by rfl⟩ : syracuseStep 1188819 = 1783229) B1783229
theorem B1188835 : Blo 1188411 1188835 := bstep (se 1 (by rfl) ⟨891626, by rfl⟩ : syracuseStep 1188835 = 1783253) B1783253
theorem B9642979 : Blo 1188411 9642979 := bstep (se 1 (by rfl) ⟨7232234, by rfl⟩ : syracuseStep 9642979 = 14464469) B14464469
theorem B1188851 : Blo 1188411 1188851 := bstep (se 1 (by rfl) ⟨891638, by rfl⟩ : syracuseStep 1188851 = 1783277) B1783277
theorem B1188867 : Blo 1188411 1188867 := bstep (se 1 (by rfl) ⟨891650, by rfl⟩ : syracuseStep 1188867 = 1783301) B1783301
theorem B3384337 : Blo 1188411 3384337 := bstep (se 2 (by rfl) ⟨1269126, by rfl⟩ : syracuseStep 3384337 = 2538253) B2538253
theorem B1188883 : Blo 1188411 1188883 := bstep (se 1 (by rfl) ⟨891662, by rfl⟩ : syracuseStep 1188883 = 1783325) B1783325
theorem B1188899 : Blo 1188411 1188899 := bstep (se 1 (by rfl) ⟨891674, by rfl⟩ : syracuseStep 1188899 = 1783349) B1783349
theorem B1188915 : Blo 1188411 1188915 := bstep (se 1 (by rfl) ⟨891686, by rfl⟩ : syracuseStep 1188915 = 1783373) B1783373
theorem B1188931 : Blo 1188411 1188931 := bstep (se 1 (by rfl) ⟨891698, by rfl⟩ : syracuseStep 1188931 = 1783397) B1783397
theorem B2008145 : Blo 1188411 2008145 := bstep (se 2 (by rfl) ⟨753054, by rfl⟩ : syracuseStep 2008145 = 1506109) B1506109
theorem B1188947 : Blo 1188411 1188947 := bstep (se 1 (by rfl) ⟨891710, by rfl⟩ : syracuseStep 1188947 = 1783421) B1783421
theorem B1188963 : Blo 1188411 1188963 := bstep (se 1 (by rfl) ⟨891722, by rfl⟩ : syracuseStep 1188963 = 1783445) B1783445
theorem B1188979 : Blo 1188411 1188979 := bstep (se 1 (by rfl) ⟨891734, by rfl⟩ : syracuseStep 1188979 = 1783469) B1783469
theorem B1188995 : Blo 1188411 1188995 := bstep (se 1 (by rfl) ⟨891746, by rfl⟩ : syracuseStep 1188995 = 1783493) B1783493
theorem B1189011 : Blo 1188411 1189011 := bstep (se 1 (by rfl) ⟨891758, by rfl⟩ : syracuseStep 1189011 = 1783517) B1783517
theorem B1189027 : Blo 1188411 1189027 := bstep (se 1 (by rfl) ⟨891770, by rfl⟩ : syracuseStep 1189027 = 1783541) B1783541
theorem B4015277 : Blo 1188411 4015277 := bstep (se 3 (by rfl) ⟨752864, by rfl⟩ : syracuseStep 4015277 = 1505729) B1505729
theorem B3384497 : Blo 1188411 3384497 := bstep (se 2 (by rfl) ⟨1269186, by rfl⟩ : syracuseStep 3384497 = 2538373) B2538373
theorem B1189043 : Blo 1188411 1189043 := bstep (se 1 (by rfl) ⟨891782, by rfl⟩ : syracuseStep 1189043 = 1783565) B1783565
theorem B1189059 : Blo 1188411 1189059 := bstep (se 1 (by rfl) ⟨891794, by rfl⟩ : syracuseStep 1189059 = 1783589) B1783589
theorem B6022349 : Blo 1188411 6022349 := bstep (se 3 (by rfl) ⟨1129190, by rfl⟩ : syracuseStep 6022349 = 2258381) B2258381
theorem B2008273 : Blo 1188411 2008273 := bstep (se 2 (by rfl) ⟨753102, by rfl⟩ : syracuseStep 2008273 = 1506205) B1506205
theorem B1189075 : Blo 1188411 1189075 := bstep (se 1 (by rfl) ⟨891806, by rfl⟩ : syracuseStep 1189075 = 1783613) B1783613
theorem B1189091 : Blo 1188411 1189091 := bstep (se 1 (by rfl) ⟨891818, by rfl⟩ : syracuseStep 1189091 = 1783637) B1783637
theorem B4015331 : Blo 1188411 4015331 := bstep (se 1 (by rfl) ⟨3011498, by rfl⟩ : syracuseStep 4015331 = 6022997) B6022997
theorem B1189107 : Blo 1188411 1189107 := bstep (se 1 (by rfl) ⟨891830, by rfl⟩ : syracuseStep 1189107 = 1783661) B1783661
theorem B2008307 : Blo 1188411 2008307 := bstep (se 1 (by rfl) ⟨1506230, by rfl⟩ : syracuseStep 2008307 = 3012461) B3012461
theorem B1983745 : Blo 1188411 1983745 := bstep (se 2 (by rfl) ⟨743904, by rfl⟩ : syracuseStep 1983745 = 1487809) B1487809
theorem B1189123 : Blo 1188411 1189123 := bstep (se 1 (by rfl) ⟨891842, by rfl⟩ : syracuseStep 1189123 = 1783685) B1783685
theorem B5080333 : Blo 1188411 5080333 := bstep (se 3 (by rfl) ⟨952562, by rfl⟩ : syracuseStep 5080333 = 1905125) B1905125
theorem B1189139 : Blo 1188411 1189139 := bstep (se 1 (by rfl) ⟨891854, by rfl⟩ : syracuseStep 1189139 = 1783709) B1783709
theorem B3384611 : Blo 1188411 3384611 := bstep (se 1 (by rfl) ⟨2538458, by rfl⟩ : syracuseStep 3384611 = 5076917) B5076917
theorem B1189155 : Blo 1188411 1189155 := bstep (se 1 (by rfl) ⟨891866, by rfl⟩ : syracuseStep 1189155 = 1783733) B1783733
theorem B1189171 : Blo 1188411 1189171 := bstep (se 1 (by rfl) ⟨891878, by rfl⟩ : syracuseStep 1189171 = 1783757) B1783757
theorem B1189187 : Blo 1188411 1189187 := bstep (se 1 (by rfl) ⟨891890, by rfl⟩ : syracuseStep 1189187 = 1783781) B1783781
theorem B1189203 : Blo 1188411 1189203 := bstep (se 1 (by rfl) ⟨891902, by rfl⟩ : syracuseStep 1189203 = 1783805) B1783805
theorem B1189219 : Blo 1188411 1189219 := bstep (se 1 (by rfl) ⟨891914, by rfl⟩ : syracuseStep 1189219 = 1783829) B1783829
theorem B9037169 : Blo 1188411 9037169 := bstep (se 2 (by rfl) ⟨3388938, by rfl⟩ : syracuseStep 9037169 = 6777877) B6777877
theorem B1189235 : Blo 1188411 1189235 := bstep (se 1 (by rfl) ⟨891926, by rfl⟩ : syracuseStep 1189235 = 1783853) B1783853
theorem B2008435 : Blo 1188411 2008435 := bstep (se 1 (by rfl) ⟨1506326, by rfl⟩ : syracuseStep 2008435 = 3012653) B3012653
theorem B1189251 : Blo 1188411 1189251 := bstep (se 1 (by rfl) ⟨891938, by rfl⟩ : syracuseStep 1189251 = 1783877) B1783877
theorem B2540945 : Blo 1188411 2540945 := bstep (se 2 (by rfl) ⟨952854, by rfl⟩ : syracuseStep 2540945 = 1905709) B1905709
theorem B1189267 : Blo 1188411 1189267 := bstep (se 1 (by rfl) ⟨891950, by rfl⟩ : syracuseStep 1189267 = 1783901) B1783901
theorem B4343203 : Blo 1188411 4343203 := bstep (se 1 (by rfl) ⟨3257402, by rfl⟩ : syracuseStep 4343203 = 6514805) B6514805
theorem B1189283 : Blo 1188411 1189283 := bstep (se 1 (by rfl) ⟨891962, by rfl⟩ : syracuseStep 1189283 = 1783925) B1783925
theorem B5293475 : Blo 1188411 5293475 := bstep (se 1 (by rfl) ⟨3970106, by rfl⟩ : syracuseStep 5293475 = 7940213) B7940213
theorem B1189299 : Blo 1188411 1189299 := bstep (se 1 (by rfl) ⟨891974, by rfl⟩ : syracuseStep 1189299 = 1783949) B1783949
theorem B1189315 : Blo 1188411 1189315 := bstep (se 1 (by rfl) ⟨891986, by rfl⟩ : syracuseStep 1189315 = 1783973) B1783973
theorem B1189331 : Blo 1188411 1189331 := bstep (se 1 (by rfl) ⟨891998, by rfl⟩ : syracuseStep 1189331 = 1783997) B1783997
theorem B1189347 : Blo 1188411 1189347 := bstep (se 1 (by rfl) ⟨892010, by rfl⟩ : syracuseStep 1189347 = 1784021) B1784021
theorem B4015601 : Blo 1188411 4015601 := bstep (se 2 (by rfl) ⟨1505850, by rfl⟩ : syracuseStep 4015601 = 3011701) B3011701
theorem B1189363 : Blo 1188411 1189363 := bstep (se 1 (by rfl) ⟨892022, by rfl⟩ : syracuseStep 1189363 = 1784045) B1784045
theorem B2008577 : Blo 1188411 2008577 := bstep (se 2 (by rfl) ⟨753216, by rfl⟩ : syracuseStep 2008577 = 1506433) B1506433
theorem B1189379 : Blo 1188411 1189379 := bstep (se 1 (by rfl) ⟨892034, by rfl⟩ : syracuseStep 1189379 = 1784069) B1784069
theorem B1189395 : Blo 1188411 1189395 := bstep (se 1 (by rfl) ⟨892046, by rfl⟩ : syracuseStep 1189395 = 1784093) B1784093
theorem B1189411 : Blo 1188411 1189411 := bstep (se 1 (by rfl) ⟨892058, by rfl⟩ : syracuseStep 1189411 = 1784117) B1784117
theorem B1189427 : Blo 1188411 1189427 := bstep (se 1 (by rfl) ⟨892070, by rfl⟩ : syracuseStep 1189427 = 1784141) B1784141
theorem B1189443 : Blo 1188411 1189443 := bstep (se 1 (by rfl) ⟨892082, by rfl⟩ : syracuseStep 1189443 = 1784165) B1784165
theorem B1189459 : Blo 1188411 1189459 := bstep (se 1 (by rfl) ⟨892094, by rfl⟩ : syracuseStep 1189459 = 1784189) B1784189
theorem B1189475 : Blo 1188411 1189475 := bstep (se 1 (by rfl) ⟨892106, by rfl⟩ : syracuseStep 1189475 = 1784213) B1784213
theorem B6776419 : Blo 1188411 6776419 := bstep (se 1 (by rfl) ⟨5082314, by rfl⟩ : syracuseStep 6776419 = 10164629) B10164629
theorem B1189491 : Blo 1188411 1189491 := bstep (se 1 (by rfl) ⟨892118, by rfl⟩ : syracuseStep 1189491 = 1784237) B1784237
theorem B2008705 : Blo 1188411 2008705 := bstep (se 2 (by rfl) ⟨753264, by rfl⟩ : syracuseStep 2008705 = 1506529) B1506529
theorem B1336963 : Blo 1188411 1336963 := bstep (se 1 (by rfl) ⟨1002722, by rfl⟩ : syracuseStep 1336963 = 2005445) B2005445
theorem B1189507 : Blo 1188411 1189507 := bstep (se 1 (by rfl) ⟨892130, by rfl⟩ : syracuseStep 1189507 = 1784261) B1784261
theorem B1189523 : Blo 1188411 1189523 := bstep (se 1 (by rfl) ⟨892142, by rfl⟩ : syracuseStep 1189523 = 1784285) B1784285
theorem B1189539 : Blo 1188411 1189539 := bstep (se 1 (by rfl) ⟨892154, by rfl⟩ : syracuseStep 1189539 = 1784309) B1784309
theorem B2008739 : Blo 1188411 2008739 := bstep (se 1 (by rfl) ⟨1506554, by rfl⟩ : syracuseStep 2008739 = 3013109) B3013109
theorem B4343473 : Blo 1188411 4343473 := bstep (se 2 (by rfl) ⟨1628802, by rfl⟩ : syracuseStep 4343473 = 3257605) B3257605
theorem B1189555 : Blo 1188411 1189555 := bstep (se 1 (by rfl) ⟨892166, by rfl⟩ : syracuseStep 1189555 = 1784333) B1784333
theorem B1189571 : Blo 1188411 1189571 := bstep (se 1 (by rfl) ⟨892178, by rfl⟩ : syracuseStep 1189571 = 1784357) B1784357
theorem B4515533 : Blo 1188411 4515533 := bstep (se 3 (by rfl) ⟨846662, by rfl⟩ : syracuseStep 4515533 = 1693325) B1693325
theorem B1189587 : Blo 1188411 1189587 := bstep (se 1 (by rfl) ⟨892190, by rfl⟩ : syracuseStep 1189587 = 1784381) B1784381
theorem B1189603 : Blo 1188411 1189603 := bstep (se 1 (by rfl) ⟨892202, by rfl⟩ : syracuseStep 1189603 = 1784405) B1784405
theorem B17622755 : Blo 1188411 17622755 := bstep (se 1 (by rfl) ⟨13217066, by rfl⟩ : syracuseStep 17622755 = 26434133) B26434133
theorem B1189619 : Blo 1188411 1189619 := bstep (se 1 (by rfl) ⟨892214, by rfl⟩ : syracuseStep 1189619 = 1784429) B1784429
theorem B1189635 : Blo 1188411 1189635 := bstep (se 1 (by rfl) ⟨892226, by rfl⟩ : syracuseStep 1189635 = 1784453) B1784453
theorem B1337107 : Blo 1188411 1337107 := bstep (se 1 (by rfl) ⟨1002830, by rfl⟩ : syracuseStep 1337107 = 2005661) B2005661
theorem B1189651 : Blo 1188411 1189651 := bstep (se 1 (by rfl) ⟨892238, by rfl⟩ : syracuseStep 1189651 = 1784477) B1784477
theorem B4286243 : Blo 1188411 4286243 := bstep (se 1 (by rfl) ⟨3214682, by rfl⟩ : syracuseStep 4286243 = 6429365) B6429365
theorem B1189667 : Blo 1188411 1189667 := bstep (se 1 (by rfl) ⟨892250, by rfl⟩ : syracuseStep 1189667 = 1784501) B1784501
theorem B1189683 : Blo 1188411 1189683 := bstep (se 1 (by rfl) ⟨892262, by rfl⟩ : syracuseStep 1189683 = 1784525) B1784525
theorem B1189699 : Blo 1188411 1189699 := bstep (se 1 (by rfl) ⟨892274, by rfl⟩ : syracuseStep 1189699 = 1784549) B1784549
theorem B1189715 : Blo 1188411 1189715 := bstep (se 1 (by rfl) ⟨892286, by rfl⟩ : syracuseStep 1189715 = 1784573) B1784573
theorem B7718755 : Blo 1188411 7718755 := bstep (se 1 (by rfl) ⟨5789066, by rfl⟩ : syracuseStep 7718755 = 11578133) B11578133
theorem B1189731 : Blo 1188411 1189731 := bstep (se 1 (by rfl) ⟨892298, by rfl⟩ : syracuseStep 1189731 = 1784597) B1784597
theorem B1189747 : Blo 1188411 1189747 := bstep (se 1 (by rfl) ⟨892310, by rfl⟩ : syracuseStep 1189747 = 1784621) B1784621
theorem B1189763 : Blo 1188411 1189763 := bstep (se 1 (by rfl) ⟨892322, by rfl⟩ : syracuseStep 1189763 = 1784645) B1784645
theorem B1189779 : Blo 1188411 1189779 := bstep (se 1 (by rfl) ⟨892334, by rfl⟩ : syracuseStep 1189779 = 1784669) B1784669
theorem B1337251 : Blo 1188411 1337251 := bstep (se 1 (by rfl) ⟨1002938, by rfl⟩ : syracuseStep 1337251 = 2005877) B2005877
theorem B1189795 : Blo 1188411 1189795 := bstep (se 1 (by rfl) ⟨892346, by rfl⟩ : syracuseStep 1189795 = 1784693) B1784693
theorem B1189811 : Blo 1188411 1189811 := bstep (se 1 (by rfl) ⟨892358, by rfl⟩ : syracuseStep 1189811 = 1784717) B1784717
theorem B1189827 : Blo 1188411 1189827 := bstep (se 1 (by rfl) ⟨892370, by rfl⟩ : syracuseStep 1189827 = 1784741) B1784741
theorem B1189843 : Blo 1188411 1189843 := bstep (se 1 (by rfl) ⟨892382, by rfl⟩ : syracuseStep 1189843 = 1784765) B1784765
theorem B2033635 : Blo 1188411 2033635 := bstep (se 1 (by rfl) ⟨1525226, by rfl⟩ : syracuseStep 2033635 = 3050453) B3050453
theorem B1189859 : Blo 1188411 1189859 := bstep (se 1 (by rfl) ⟨892394, by rfl⟩ : syracuseStep 1189859 = 1784789) B1784789
theorem B1189875 : Blo 1188411 1189875 := bstep (se 1 (by rfl) ⟨892406, by rfl⟩ : syracuseStep 1189875 = 1784813) B1784813
theorem B1607683 : Blo 1188411 1607683 := bstep (se 1 (by rfl) ⟨1205762, by rfl⟩ : syracuseStep 1607683 = 2411525) B2411525
theorem B1189891 : Blo 1188411 1189891 := bstep (se 1 (by rfl) ⟨892418, by rfl⟩ : syracuseStep 1189891 = 1784837) B1784837
theorem B4016141 : Blo 1188411 4016141 := bstep (se 3 (by rfl) ⟨753026, by rfl⟩ : syracuseStep 4016141 = 1506053) B1506053
theorem B1189907 : Blo 1188411 1189907 := bstep (se 1 (by rfl) ⟨892430, by rfl⟩ : syracuseStep 1189907 = 1784861) B1784861
theorem B1189923 : Blo 1188411 1189923 := bstep (se 1 (by rfl) ⟨892442, by rfl⟩ : syracuseStep 1189923 = 1784885) B1784885
theorem B2172977 : Blo 1188411 2172977 := bstep (se 2 (by rfl) ⟨814866, by rfl⟩ : syracuseStep 2172977 = 1629733) B1629733
theorem B1337395 : Blo 1188411 1337395 := bstep (se 1 (by rfl) ⟨1003046, by rfl⟩ : syracuseStep 1337395 = 2006093) B2006093
theorem B1189939 : Blo 1188411 1189939 := bstep (se 1 (by rfl) ⟨892454, by rfl⟩ : syracuseStep 1189939 = 1784909) B1784909
theorem B1189955 : Blo 1188411 1189955 := bstep (se 1 (by rfl) ⟨892466, by rfl⟩ : syracuseStep 1189955 = 1784933) B1784933
theorem B4016195 : Blo 1188411 4016195 := bstep (se 1 (by rfl) ⟨3012146, by rfl⟩ : syracuseStep 4016195 = 6024293) B6024293
theorem B1189971 : Blo 1188411 1189971 := bstep (se 1 (by rfl) ⟨892478, by rfl⟩ : syracuseStep 1189971 = 1784957) B1784957
theorem B1189987 : Blo 1188411 1189987 := bstep (se 1 (by rfl) ⟨892490, by rfl⟩ : syracuseStep 1189987 = 1784981) B1784981
theorem B6776945 : Blo 1188411 6776945 := bstep (se 2 (by rfl) ⟨2541354, by rfl⟩ : syracuseStep 6776945 = 5082709) B5082709
theorem B1190003 : Blo 1188411 1190003 := bstep (se 1 (by rfl) ⟨892502, by rfl⟩ : syracuseStep 1190003 = 1785005) B1785005
theorem B1190019 : Blo 1188411 1190019 := bstep (se 1 (by rfl) ⟨892514, by rfl⟩ : syracuseStep 1190019 = 1785029) B1785029
theorem B21686413 : Blo 1188411 21686413 := bstep (se 3 (by rfl) ⟨4066202, by rfl⟩ : syracuseStep 21686413 = 8132405) B8132405
theorem B1190035 : Blo 1188411 1190035 := bstep (se 1 (by rfl) ⟨892526, by rfl⟩ : syracuseStep 1190035 = 1785053) B1785053
theorem B1190051 : Blo 1188411 1190051 := bstep (se 1 (by rfl) ⟨892538, by rfl⟩ : syracuseStep 1190051 = 1785077) B1785077
theorem B1190067 : Blo 1188411 1190067 := bstep (se 1 (by rfl) ⟨892550, by rfl⟩ : syracuseStep 1190067 = 1785101) B1785101
theorem B1337539 : Blo 1188411 1337539 := bstep (se 1 (by rfl) ⟨1003154, by rfl⟩ : syracuseStep 1337539 = 2006309) B2006309
theorem B1190083 : Blo 1188411 1190083 := bstep (se 1 (by rfl) ⟨892562, by rfl⟩ : syracuseStep 1190083 = 1785125) B1785125
theorem B1190099 : Blo 1188411 1190099 := bstep (se 1 (by rfl) ⟨892574, by rfl⟩ : syracuseStep 1190099 = 1785149) B1785149
theorem B1190115 : Blo 1188411 1190115 := bstep (se 1 (by rfl) ⟨892586, by rfl⟩ : syracuseStep 1190115 = 1785173) B1785173
theorem B1190131 : Blo 1188411 1190131 := bstep (se 1 (by rfl) ⟨892598, by rfl⟩ : syracuseStep 1190131 = 1785197) B1785197
theorem B1190147 : Blo 1188411 1190147 := bstep (se 1 (by rfl) ⟨892610, by rfl⟩ : syracuseStep 1190147 = 1785221) B1785221
theorem B3385613 : Blo 1188411 3385613 := bstep (se 3 (by rfl) ⟨634802, by rfl⟩ : syracuseStep 3385613 = 1269605) B1269605
theorem B3008785 : Blo 1188411 3008785 := bstep (se 2 (by rfl) ⟨1128294, by rfl⟩ : syracuseStep 3008785 = 2256589) B2256589
theorem B1190163 : Blo 1188411 1190163 := bstep (se 1 (by rfl) ⟨892622, by rfl⟩ : syracuseStep 1190163 = 1785245) B1785245
theorem B1607969 : Blo 1188411 1607969 := bstep (se 2 (by rfl) ⟨602988, by rfl⟩ : syracuseStep 1607969 = 1205977) B1205977
theorem B1190179 : Blo 1188411 1190179 := bstep (se 1 (by rfl) ⟨892634, by rfl⟩ : syracuseStep 1190179 = 1785269) B1785269
theorem B5081393 : Blo 1188411 5081393 := bstep (se 2 (by rfl) ⟨1905522, by rfl⟩ : syracuseStep 5081393 = 3811045) B3811045
theorem B1190195 : Blo 1188411 1190195 := bstep (se 1 (by rfl) ⟨892646, by rfl⟩ : syracuseStep 1190195 = 1785293) B1785293
theorem B1190211 : Blo 1188411 1190211 := bstep (se 1 (by rfl) ⟨892658, by rfl⟩ : syracuseStep 1190211 = 1785317) B1785317
theorem B3811661 : Blo 1188411 3811661 := bstep (se 3 (by rfl) ⟨714686, by rfl⟩ : syracuseStep 3811661 = 1429373) B1429373
theorem B4016465 : Blo 1188411 4016465 := bstep (se 2 (by rfl) ⟨1506174, by rfl⟩ : syracuseStep 4016465 = 3012349) B3012349
theorem B1337683 : Blo 1188411 1337683 := bstep (se 1 (by rfl) ⟨1003262, by rfl⟩ : syracuseStep 1337683 = 2006525) B2006525
theorem B1190227 : Blo 1188411 1190227 := bstep (se 1 (by rfl) ⟨892670, by rfl⟩ : syracuseStep 1190227 = 1785341) B1785341
theorem B1190243 : Blo 1188411 1190243 := bstep (se 1 (by rfl) ⟨892682, by rfl⟩ : syracuseStep 1190243 = 1785365) B1785365
theorem B1190259 : Blo 1188411 1190259 := bstep (se 1 (by rfl) ⟨892694, by rfl⟩ : syracuseStep 1190259 = 1785389) B1785389
theorem B1190275 : Blo 1188411 1190275 := bstep (se 1 (by rfl) ⟨892706, by rfl⟩ : syracuseStep 1190275 = 1785413) B1785413
theorem B1190291 : Blo 1188411 1190291 := bstep (se 1 (by rfl) ⟨892718, by rfl⟩ : syracuseStep 1190291 = 1785437) B1785437
theorem B1190307 : Blo 1188411 1190307 := bstep (se 1 (by rfl) ⟨892730, by rfl⟩ : syracuseStep 1190307 = 1785461) B1785461
theorem B1190323 : Blo 1188411 1190323 := bstep (se 1 (by rfl) ⟨892742, by rfl⟩ : syracuseStep 1190323 = 1785485) B1785485
theorem B3385795 : Blo 1188411 3385795 := bstep (se 1 (by rfl) ⟨2539346, by rfl⟩ : syracuseStep 3385795 = 5078693) B5078693
theorem B1190339 : Blo 1188411 1190339 := bstep (se 1 (by rfl) ⟨892754, by rfl⟩ : syracuseStep 1190339 = 1785509) B1785509
theorem B1190355 : Blo 1188411 1190355 := bstep (se 1 (by rfl) ⟨892766, by rfl⟩ : syracuseStep 1190355 = 1785533) B1785533
theorem B1337827 : Blo 1188411 1337827 := bstep (se 1 (by rfl) ⟨1003370, by rfl⟩ : syracuseStep 1337827 = 2006741) B2006741
theorem B1190371 : Blo 1188411 1190371 := bstep (se 1 (by rfl) ⟨892778, by rfl⟩ : syracuseStep 1190371 = 1785557) B1785557
theorem B3213809 : Blo 1188411 3213809 := bstep (se 2 (by rfl) ⟨1205178, by rfl⟩ : syracuseStep 3213809 = 2410357) B2410357
theorem B4516337 : Blo 1188411 4516337 := bstep (se 2 (by rfl) ⟨1693626, by rfl⟩ : syracuseStep 4516337 = 3387253) B3387253
theorem B1190387 : Blo 1188411 1190387 := bstep (se 1 (by rfl) ⟨892790, by rfl⟩ : syracuseStep 1190387 = 1785581) B1785581
theorem B1190403 : Blo 1188411 1190403 := bstep (se 1 (by rfl) ⟨892802, by rfl⟩ : syracuseStep 1190403 = 1785605) B1785605
theorem B3009059 : Blo 1188411 3009059 := bstep (se 1 (by rfl) ⟨2256794, by rfl⟩ : syracuseStep 3009059 = 4513589) B4513589
theorem B3385955 : Blo 1188411 3385955 := bstep (se 1 (by rfl) ⟨2539466, by rfl⟩ : syracuseStep 3385955 = 5078933) B5078933
theorem B1337971 : Blo 1188411 1337971 := bstep (se 1 (by rfl) ⟨1003478, by rfl⟩ : syracuseStep 1337971 = 2006957) B2006957
theorem B7252643 : Blo 1188411 7252643 := bstep (se 1 (by rfl) ⟨5439482, by rfl⟩ : syracuseStep 7252643 = 10878965) B10878965
theorem B5147363 : Blo 1188411 5147363 := bstep (se 1 (by rfl) ⟨3860522, by rfl⟩ : syracuseStep 5147363 = 7721045) B7721045
theorem B3009251 : Blo 1188411 3009251 := bstep (se 1 (by rfl) ⟨2256938, by rfl⟩ : syracuseStep 3009251 = 4513877) B4513877
theorem B1338115 : Blo 1188411 1338115 := bstep (se 1 (by rfl) ⟨1003586, by rfl⟩ : syracuseStep 1338115 = 2007173) B2007173
theorem B46328597 : Blo 1188411 46328597 := bstep (se 6 (by rfl) ⟨1085826, by rfl⟩ : syracuseStep 46328597 = 2171653) B2171653
theorem B4017005 : Blo 1188411 4017005 := bstep (se 3 (by rfl) ⟨753188, by rfl⟩ : syracuseStep 4017005 = 1506377) B1506377
theorem B1338259 : Blo 1188411 1338259 := bstep (se 1 (by rfl) ⟨1003694, by rfl⟩ : syracuseStep 1338259 = 2007389) B2007389
theorem B4017059 : Blo 1188411 4017059 := bstep (se 1 (by rfl) ⟨3012794, by rfl⟩ : syracuseStep 4017059 = 6025589) B6025589
theorem B1338403 : Blo 1188411 1338403 := bstep (se 1 (by rfl) ⟨1003802, by rfl⟩ : syracuseStep 1338403 = 2007605) B2007605
theorem B4517005 : Blo 1188411 4517005 := bstep (se 3 (by rfl) ⟨846938, by rfl⟩ : syracuseStep 4517005 = 1693877) B1693877
theorem B4017329 : Blo 1188411 4017329 := bstep (se 2 (by rfl) ⟨1506498, by rfl⟩ : syracuseStep 4017329 = 3012997) B3012997
theorem B1338547 : Blo 1188411 1338547 := bstep (se 1 (by rfl) ⟨1003910, by rfl⟩ : syracuseStep 1338547 = 2007821) B2007821
theorem B7621937 : Blo 1188411 7621937 := bstep (se 2 (by rfl) ⟨2858226, by rfl⟩ : syracuseStep 7621937 = 5716453) B5716453
theorem B1338691 : Blo 1188411 1338691 := bstep (se 1 (by rfl) ⟨1004018, by rfl⟩ : syracuseStep 1338691 = 2008037) B2008037
theorem B6016355 : Blo 1188411 6016355 := bstep (se 1 (by rfl) ⟨4512266, by rfl⟩ : syracuseStep 6016355 = 9024533) B9024533
theorem B1428835 : Blo 1188411 1428835 := bstep (se 1 (by rfl) ⟨1071626, by rfl⟩ : syracuseStep 1428835 = 2143253) B2143253
theorem B1527155 : Blo 1188411 1527155 := bstep (se 1 (by rfl) ⟨1145366, by rfl⟩ : syracuseStep 1527155 = 2290733) B2290733
theorem B2674097 : Blo 1188411 2674097 := bstep (se 2 (by rfl) ⟨1002786, by rfl⟩ : syracuseStep 2674097 = 2005573) B2005573
theorem B2674115 : Blo 1188411 2674115 := bstep (se 1 (by rfl) ⟨2005586, by rfl⟩ : syracuseStep 2674115 = 4011173) B4011173
theorem B16289221 : Blo 1188411 16289221 := bstep (se 4 (by rfl) ⟨1527114, by rfl⟩ : syracuseStep 16289221 = 3054229) B3054229
theorem B1338835 : Blo 1188411 1338835 := bstep (se 1 (by rfl) ⟨1004126, by rfl⟩ : syracuseStep 1338835 = 2008253) B2008253
theorem B6426125 : Blo 1188411 6426125 := bstep (se 3 (by rfl) ⟨1204898, by rfl⟩ : syracuseStep 6426125 = 2409797) B2409797
theorem B2141731 : Blo 1188411 2141731 := bstep (se 1 (by rfl) ⟨1606298, by rfl⟩ : syracuseStep 2141731 = 3212597) B3212597
theorem B6778403 : Blo 1188411 6778403 := bstep (se 1 (by rfl) ⟨5083802, by rfl⟩ : syracuseStep 6778403 = 10167605) B10167605
theorem B1904177 : Blo 1188411 1904177 := bstep (se 2 (by rfl) ⟨714066, by rfl⟩ : syracuseStep 1904177 = 1428133) B1428133
theorem B1338979 : Blo 1188411 1338979 := bstep (se 1 (by rfl) ⟨1004234, by rfl⟩ : syracuseStep 1338979 = 2008469) B2008469
theorem B3010193 : Blo 1188411 3010193 := bstep (se 2 (by rfl) ⟨1128822, by rfl⟩ : syracuseStep 3010193 = 2257645) B2257645
theorem B3387025 : Blo 1188411 3387025 := bstep (se 2 (by rfl) ⟨1270134, by rfl⟩ : syracuseStep 3387025 = 2540269) B2540269
theorem B1904305 : Blo 1188411 1904305 := bstep (se 2 (by rfl) ⟨714114, by rfl⟩ : syracuseStep 1904305 = 1428229) B1428229
theorem B3010243 : Blo 1188411 3010243 := bstep (se 1 (by rfl) ⟨2257682, by rfl⟩ : syracuseStep 3010243 = 4515365) B4515365
theorem B2141905 : Blo 1188411 2141905 := bstep (se 2 (by rfl) ⟨803214, by rfl⟩ : syracuseStep 2141905 = 1606429) B1606429
theorem B2674385 : Blo 1188411 2674385 := bstep (se 2 (by rfl) ⟨1002894, by rfl⟩ : syracuseStep 2674385 = 2005789) B2005789
theorem B2674403 : Blo 1188411 2674403 := bstep (se 1 (by rfl) ⟨2005802, by rfl⟩ : syracuseStep 2674403 = 4011605) B4011605
theorem B1339123 : Blo 1188411 1339123 := bstep (se 1 (by rfl) ⟨1004342, by rfl⟩ : syracuseStep 1339123 = 2008685) B2008685
theorem B2035457 : Blo 1188411 2035457 := bstep (se 2 (by rfl) ⟨763296, by rfl⟩ : syracuseStep 2035457 = 1526593) B1526593
theorem B3010385 : Blo 1188411 3010385 := bstep (se 2 (by rfl) ⟨1128894, by rfl⟩ : syracuseStep 3010385 = 2257789) B2257789
theorem B1429363 : Blo 1188411 1429363 := bstep (se 1 (by rfl) ⟨1072022, by rfl⟩ : syracuseStep 1429363 = 2144045) B2144045
theorem B97677197 : Blo 1188411 97677197 := bstep (se 3 (by rfl) ⟨18314474, by rfl⟩ : syracuseStep 97677197 = 36628949) B36628949
theorem B4517795 : Blo 1188411 4517795 := bstep (se 1 (by rfl) ⟨3388346, by rfl⟩ : syracuseStep 4517795 = 6776693) B6776693
theorem B2256817 : Blo 1188411 2256817 := bstep (se 2 (by rfl) ⟨846306, by rfl⟩ : syracuseStep 2256817 = 1692613) B1692613
theorem B2674673 : Blo 1188411 2674673 := bstep (se 2 (by rfl) ⟨1003002, by rfl⟩ : syracuseStep 2674673 = 2006005) B2006005
theorem B2674691 : Blo 1188411 2674691 := bstep (se 1 (by rfl) ⟨2006018, by rfl⟩ : syracuseStep 2674691 = 4012037) B4012037
theorem B6025265 : Blo 1188411 6025265 := bstep (se 2 (by rfl) ⟨2259474, by rfl⟩ : syracuseStep 6025265 = 4518949) B4518949
theorem B2256977 : Blo 1188411 2256977 := bstep (se 2 (by rfl) ⟨846366, by rfl⟩ : syracuseStep 2256977 = 1692733) B1692733
theorem B6017165 : Blo 1188411 6017165 := bstep (se 3 (by rfl) ⟨1128218, by rfl⟩ : syracuseStep 6017165 = 2256437) B2256437
theorem B2674961 : Blo 1188411 2674961 := bstep (se 2 (by rfl) ⟨1003110, by rfl⟩ : syracuseStep 2674961 = 2006221) B2006221
theorem B2674979 : Blo 1188411 2674979 := bstep (se 1 (by rfl) ⟨2006234, by rfl⟩ : syracuseStep 2674979 = 4012469) B4012469
theorem B2257379 : Blo 1188411 2257379 := bstep (se 1 (by rfl) ⟨1693034, by rfl⟩ : syracuseStep 2257379 = 3386069) B3386069
theorem B2290211 : Blo 1188411 2290211 := bstep (se 1 (by rfl) ⟨1717658, by rfl⟩ : syracuseStep 2290211 = 3435317) B3435317
theorem B6107683 : Blo 1188411 6107683 := bstep (se 1 (by rfl) ⟨4580762, by rfl⟩ : syracuseStep 6107683 = 9161525) B9161525
theorem B2675249 : Blo 1188411 2675249 := bstep (se 2 (by rfl) ⟨1003218, by rfl⟩ : syracuseStep 2675249 = 2006437) B2006437
theorem B4518449 : Blo 1188411 4518449 := bstep (se 2 (by rfl) ⟨1694418, by rfl⟩ : syracuseStep 4518449 = 3388837) B3388837
theorem B1929793 : Blo 1188411 1929793 := bstep (se 2 (by rfl) ⟨723672, by rfl⟩ : syracuseStep 1929793 = 1447345) B1447345
theorem B2675267 : Blo 1188411 2675267 := bstep (se 1 (by rfl) ⟨2006450, by rfl⟩ : syracuseStep 2675267 = 4012901) B4012901
theorem B2142833 : Blo 1188411 2142833 := bstep (se 2 (by rfl) ⟨803562, by rfl⟩ : syracuseStep 2142833 = 1607125) B1607125
theorem B1905299 : Blo 1188411 1905299 := bstep (se 1 (by rfl) ⟨1428974, by rfl⟩ : syracuseStep 1905299 = 2857949) B2857949
theorem B9638597 : Blo 1188411 9638597 := bstep (se 4 (by rfl) ⟨903618, by rfl⟩ : syracuseStep 9638597 = 1807237) B1807237
theorem B14676677 : Blo 1188411 14676677 := bstep (se 4 (by rfl) ⟨1375938, by rfl⟩ : syracuseStep 14676677 = 2751877) B2751877
theorem B1692419 : Blo 1188411 1692419 := bstep (se 1 (by rfl) ⟨1269314, by rfl⟩ : syracuseStep 1692419 = 2538629) B2538629
theorem B3011377 : Blo 1188411 3011377 := bstep (se 2 (by rfl) ⟨1129266, by rfl⟩ : syracuseStep 3011377 = 2258533) B2258533
theorem B4289357 : Blo 1188411 4289357 := bstep (se 3 (by rfl) ⟨804254, by rfl⟩ : syracuseStep 4289357 = 1608509) B1608509
theorem B2675537 : Blo 1188411 2675537 := bstep (se 2 (by rfl) ⟨1003326, by rfl⟩ : syracuseStep 2675537 = 2006653) B2006653
theorem B1504099 : Blo 1188411 1504099 := bstep (se 1 (by rfl) ⟨1128074, by rfl⟩ : syracuseStep 1504099 = 2256149) B2256149
theorem B2675555 : Blo 1188411 2675555 := bstep (se 1 (by rfl) ⟨2006666, by rfl⟩ : syracuseStep 2675555 = 4013333) B4013333
theorem B1782641 : Blo 1188411 1782641 := bstep (se 2 (by rfl) ⟨668490, by rfl⟩ : syracuseStep 1782641 = 1336981) B1336981
theorem B1782659 : Blo 1188411 1782659 := bstep (se 1 (by rfl) ⟨1336994, by rfl⟩ : syracuseStep 1782659 = 2673989) B2673989
theorem B3388301 : Blo 1188411 3388301 := bstep (se 3 (by rfl) ⟨635306, by rfl⟩ : syracuseStep 3388301 = 1270613) B1270613
theorem B1782689 : Blo 1188411 1782689 := bstep (se 2 (by rfl) ⟨668508, by rfl⟩ : syracuseStep 1782689 = 1337017) B1337017
theorem B1782707 : Blo 1188411 1782707 := bstep (se 1 (by rfl) ⟨1337030, by rfl⟩ : syracuseStep 1782707 = 2674061) B2674061
theorem B4010957 : Blo 1188411 4010957 := bstep (se 3 (by rfl) ⟨752054, by rfl⟩ : syracuseStep 4010957 = 1504109) B1504109
theorem B1782737 : Blo 1188411 1782737 := bstep (se 2 (by rfl) ⟨668526, by rfl⟩ : syracuseStep 1782737 = 1337053) B1337053
theorem B1782755 : Blo 1188411 1782755 := bstep (se 1 (by rfl) ⟨1337066, by rfl⟩ : syracuseStep 1782755 = 2674133) B2674133
theorem B1782785 : Blo 1188411 1782785 := bstep (se 2 (by rfl) ⟨668544, by rfl⟩ : syracuseStep 1782785 = 1337089) B1337089
theorem B4011011 : Blo 1188411 4011011 := bstep (se 1 (by rfl) ⟨3008258, by rfl⟩ : syracuseStep 4011011 = 6016517) B6016517
theorem B1782803 : Blo 1188411 1782803 := bstep (se 1 (by rfl) ⟨1337102, by rfl⟩ : syracuseStep 1782803 = 2674205) B2674205
theorem B1782833 : Blo 1188411 1782833 := bstep (se 2 (by rfl) ⟨668562, by rfl⟩ : syracuseStep 1782833 = 1337125) B1337125
theorem B1782851 : Blo 1188411 1782851 := bstep (se 1 (by rfl) ⟨1337138, by rfl⟩ : syracuseStep 1782851 = 2674277) B2674277
theorem B3011651 : Blo 1188411 3011651 := bstep (se 1 (by rfl) ⟨2258738, by rfl⟩ : syracuseStep 3011651 = 4517477) B4517477
theorem B3388483 : Blo 1188411 3388483 := bstep (se 1 (by rfl) ⟨2541362, by rfl⟩ : syracuseStep 3388483 = 5082725) B5082725
theorem B1782881 : Blo 1188411 1782881 := bstep (se 2 (by rfl) ⟨668580, by rfl⟩ : syracuseStep 1782881 = 1337161) B1337161
theorem B2856035 : Blo 1188411 2856035 := bstep (se 1 (by rfl) ⟨2142026, by rfl⟩ : syracuseStep 2856035 = 4284053) B4284053
theorem B2675825 : Blo 1188411 2675825 := bstep (se 2 (by rfl) ⟨1003434, by rfl⟩ : syracuseStep 2675825 = 2006869) B2006869
theorem B3388529 : Blo 1188411 3388529 := bstep (se 2 (by rfl) ⟨1270698, by rfl⟩ : syracuseStep 3388529 = 2541397) B2541397
theorem B1782899 : Blo 1188411 1782899 := bstep (se 1 (by rfl) ⟨1337174, by rfl⟩ : syracuseStep 1782899 = 2674349) B2674349
theorem B2675843 : Blo 1188411 2675843 := bstep (se 1 (by rfl) ⟨2006882, by rfl⟩ : syracuseStep 2675843 = 4013765) B4013765
theorem B1782929 : Blo 1188411 1782929 := bstep (se 2 (by rfl) ⟨668598, by rfl⟩ : syracuseStep 1782929 = 1337197) B1337197
theorem B1782947 : Blo 1188411 1782947 := bstep (se 1 (by rfl) ⟨1337210, by rfl⟩ : syracuseStep 1782947 = 2674421) B2674421
theorem B1782977 : Blo 1188411 1782977 := bstep (se 2 (by rfl) ⟨668616, by rfl⟩ : syracuseStep 1782977 = 1337233) B1337233
theorem B5084365 : Blo 1188411 5084365 := bstep (se 3 (by rfl) ⟨953318, by rfl⟩ : syracuseStep 5084365 = 1906637) B1906637
theorem B1782995 : Blo 1188411 1782995 := bstep (se 1 (by rfl) ⟨1337246, by rfl⟩ : syracuseStep 1782995 = 2674493) B2674493
theorem B50140387 : Blo 1188411 50140387 := bstep (se 1 (by rfl) ⟨37605290, by rfl⟩ : syracuseStep 50140387 = 75210581) B75210581
theorem B1783025 : Blo 1188411 1783025 := bstep (se 2 (by rfl) ⟨668634, by rfl⟩ : syracuseStep 1783025 = 1337269) B1337269
theorem B1783043 : Blo 1188411 1783043 := bstep (se 1 (by rfl) ⟨1337282, by rfl⟩ : syracuseStep 1783043 = 2674565) B2674565
theorem B3011843 : Blo 1188411 3011843 := bstep (se 1 (by rfl) ⟨2258882, by rfl⟩ : syracuseStep 3011843 = 4517765) B4517765
theorem B4011281 : Blo 1188411 4011281 := bstep (se 2 (by rfl) ⟨1504230, by rfl⟩ : syracuseStep 4011281 = 3008461) B3008461
theorem B1783073 : Blo 1188411 1783073 := bstep (se 2 (by rfl) ⟨668652, by rfl⟩ : syracuseStep 1783073 = 1337305) B1337305
theorem B1783091 : Blo 1188411 1783091 := bstep (se 1 (by rfl) ⟨1337318, by rfl⟩ : syracuseStep 1783091 = 2674637) B2674637
theorem B6772045 : Blo 1188411 6772045 := bstep (se 3 (by rfl) ⟨1269758, by rfl⟩ : syracuseStep 6772045 = 2539517) B2539517
theorem B1783121 : Blo 1188411 1783121 := bstep (se 2 (by rfl) ⟨668670, by rfl⟩ : syracuseStep 1783121 = 1337341) B1337341
theorem B1504595 : Blo 1188411 1504595 := bstep (se 1 (by rfl) ⟨1128446, by rfl⟩ : syracuseStep 1504595 = 2256893) B2256893
theorem B1783139 : Blo 1188411 1783139 := bstep (se 1 (by rfl) ⟨1337354, by rfl⟩ : syracuseStep 1783139 = 2674709) B2674709
theorem B5715299 : Blo 1188411 5715299 := bstep (se 1 (by rfl) ⟨4286474, by rfl⟩ : syracuseStep 5715299 = 8572949) B8572949
theorem B2258275 : Blo 1188411 2258275 := bstep (se 1 (by rfl) ⟨1693706, by rfl⟩ : syracuseStep 2258275 = 3387413) B3387413
theorem B1783169 : Blo 1188411 1783169 := bstep (se 2 (by rfl) ⟨668688, by rfl⟩ : syracuseStep 1783169 = 1337377) B1337377
theorem B1693057 : Blo 1188411 1693057 := bstep (se 2 (by rfl) ⟨634896, by rfl⟩ : syracuseStep 1693057 = 1269793) B1269793
theorem B3216781 : Blo 1188411 3216781 := bstep (se 3 (by rfl) ⟨603146, by rfl⟩ : syracuseStep 3216781 = 1206293) B1206293
theorem B2676113 : Blo 1188411 2676113 := bstep (se 2 (by rfl) ⟨1003542, by rfl⟩ : syracuseStep 2676113 = 2007085) B2007085
theorem B1783187 : Blo 1188411 1783187 := bstep (se 1 (by rfl) ⟨1337390, by rfl⟩ : syracuseStep 1783187 = 2674781) B2674781
theorem B2676131 : Blo 1188411 2676131 := bstep (se 1 (by rfl) ⟨2007098, by rfl⟩ : syracuseStep 2676131 = 4014197) B4014197
theorem B1783217 : Blo 1188411 1783217 := bstep (se 2 (by rfl) ⟨668706, by rfl⟩ : syracuseStep 1783217 = 1337413) B1337413
theorem B1783235 : Blo 1188411 1783235 := bstep (se 1 (by rfl) ⟨1337426, by rfl⟩ : syracuseStep 1783235 = 2674853) B2674853
theorem B1783265 : Blo 1188411 1783265 := bstep (se 2 (by rfl) ⟨668724, by rfl⟩ : syracuseStep 1783265 = 1337449) B1337449
theorem B1783283 : Blo 1188411 1783283 := bstep (se 1 (by rfl) ⟨1337462, by rfl⟩ : syracuseStep 1783283 = 2674925) B2674925
theorem B1693171 : Blo 1188411 1693171 := bstep (se 1 (by rfl) ⟨1269878, by rfl⟩ : syracuseStep 1693171 = 2539757) B2539757
theorem B2258435 : Blo 1188411 2258435 := bstep (se 1 (by rfl) ⟨1693826, by rfl⟩ : syracuseStep 2258435 = 3387653) B3387653
theorem B1783313 : Blo 1188411 1783313 := bstep (se 2 (by rfl) ⟨668742, by rfl⟩ : syracuseStep 1783313 = 1337485) B1337485
theorem B1783331 : Blo 1188411 1783331 := bstep (se 1 (by rfl) ⟨1337498, by rfl⟩ : syracuseStep 1783331 = 2674997) B2674997
theorem B5084707 : Blo 1188411 5084707 := bstep (se 1 (by rfl) ⟨3813530, by rfl⟩ : syracuseStep 5084707 = 7627061) B7627061
theorem B1783361 : Blo 1188411 1783361 := bstep (se 2 (by rfl) ⟨668760, by rfl⟩ : syracuseStep 1783361 = 1337521) B1337521
theorem B1783379 : Blo 1188411 1783379 := bstep (se 1 (by rfl) ⟨1337534, by rfl⟩ : syracuseStep 1783379 = 2675069) B2675069
theorem B1783409 : Blo 1188411 1783409 := bstep (se 2 (by rfl) ⟨668778, by rfl⟩ : syracuseStep 1783409 = 1337557) B1337557
theorem B3217009 : Blo 1188411 3217009 := bstep (se 2 (by rfl) ⟨1206378, by rfl⟩ : syracuseStep 3217009 = 2412757) B2412757
theorem B1783427 : Blo 1188411 1783427 := bstep (se 1 (by rfl) ⟨1337570, by rfl⟩ : syracuseStep 1783427 = 2675141) B2675141
theorem B1783457 : Blo 1188411 1783457 := bstep (se 2 (by rfl) ⟨668796, by rfl⟩ : syracuseStep 1783457 = 1337593) B1337593
theorem B2676401 : Blo 1188411 2676401 := bstep (se 2 (by rfl) ⟨1003650, by rfl⟩ : syracuseStep 2676401 = 2007301) B2007301
theorem B1783475 : Blo 1188411 1783475 := bstep (se 1 (by rfl) ⟨1337606, by rfl⟩ : syracuseStep 1783475 = 2675213) B2675213
theorem B2676419 : Blo 1188411 2676419 := bstep (se 1 (by rfl) ⟨2007314, by rfl⟩ : syracuseStep 2676419 = 4014629) B4014629
theorem B1783505 : Blo 1188411 1783505 := bstep (se 2 (by rfl) ⟨668814, by rfl⟩ : syracuseStep 1783505 = 1337629) B1337629
theorem B1783523 : Blo 1188411 1783523 := bstep (se 1 (by rfl) ⟨1337642, by rfl⟩ : syracuseStep 1783523 = 2675285) B2675285
theorem B1783553 : Blo 1188411 1783553 := bstep (se 2 (by rfl) ⟨668832, by rfl⟩ : syracuseStep 1783553 = 1337665) B1337665
theorem B1783571 : Blo 1188411 1783571 := bstep (se 1 (by rfl) ⟨1337678, by rfl⟩ : syracuseStep 1783571 = 2675357) B2675357
theorem B4011821 : Blo 1188411 4011821 := bstep (se 3 (by rfl) ⟨752216, by rfl⟩ : syracuseStep 4011821 = 1504433) B1504433
theorem B1783601 : Blo 1188411 1783601 := bstep (se 2 (by rfl) ⟨668850, by rfl⟩ : syracuseStep 1783601 = 1337701) B1337701
theorem B1783619 : Blo 1188411 1783619 := bstep (se 1 (by rfl) ⟨1337714, by rfl⟩ : syracuseStep 1783619 = 2675429) B2675429
theorem B1783649 : Blo 1188411 1783649 := bstep (se 2 (by rfl) ⟨668868, by rfl⟩ : syracuseStep 1783649 = 1337737) B1337737
theorem B4011875 : Blo 1188411 4011875 := bstep (se 1 (by rfl) ⟨3008906, by rfl⟩ : syracuseStep 4011875 = 6017813) B6017813
theorem B2856803 : Blo 1188411 2856803 := bstep (se 1 (by rfl) ⟨2142602, by rfl⟩ : syracuseStep 2856803 = 4285205) B4285205
theorem B1783667 : Blo 1188411 1783667 := bstep (se 1 (by rfl) ⟨1337750, by rfl⟩ : syracuseStep 1783667 = 2675501) B2675501
theorem B1783697 : Blo 1188411 1783697 := bstep (se 2 (by rfl) ⟨668886, by rfl⟩ : syracuseStep 1783697 = 1337773) B1337773
theorem B1783715 : Blo 1188411 1783715 := bstep (se 1 (by rfl) ⟨1337786, by rfl⟩ : syracuseStep 1783715 = 2675573) B2675573
theorem B1783745 : Blo 1188411 1783745 := bstep (se 2 (by rfl) ⟨668904, by rfl⟩ : syracuseStep 1783745 = 1337809) B1337809
theorem B2676689 : Blo 1188411 2676689 := bstep (se 2 (by rfl) ⟨1003758, by rfl⟩ : syracuseStep 2676689 = 2007517) B2007517
theorem B1783763 : Blo 1188411 1783763 := bstep (se 1 (by rfl) ⟨1337822, by rfl⟩ : syracuseStep 1783763 = 2675645) B2675645
theorem B2676707 : Blo 1188411 2676707 := bstep (se 1 (by rfl) ⟨2007530, by rfl⟩ : syracuseStep 2676707 = 4015061) B4015061
theorem B1783793 : Blo 1188411 1783793 := bstep (se 2 (by rfl) ⟨668922, by rfl⟩ : syracuseStep 1783793 = 1337845) B1337845
theorem B5715953 : Blo 1188411 5715953 := bstep (se 2 (by rfl) ⟨2143482, by rfl⟩ : syracuseStep 5715953 = 4286965) B4286965
theorem B1783811 : Blo 1188411 1783811 := bstep (se 1 (by rfl) ⟨1337858, by rfl⟩ : syracuseStep 1783811 = 2675717) B2675717
theorem B1505299 : Blo 1188411 1505299 := bstep (se 1 (by rfl) ⟨1128974, by rfl⟩ : syracuseStep 1505299 = 2257949) B2257949
theorem B1783841 : Blo 1188411 1783841 := bstep (se 2 (by rfl) ⟨668940, by rfl⟩ : syracuseStep 1783841 = 1337881) B1337881
theorem B1783859 : Blo 1188411 1783859 := bstep (se 1 (by rfl) ⟨1337894, by rfl⟩ : syracuseStep 1783859 = 2675789) B2675789
theorem B1906753 : Blo 1188411 1906753 := bstep (se 2 (by rfl) ⟨715032, by rfl⟩ : syracuseStep 1906753 = 1430065) B1430065
theorem B1783889 : Blo 1188411 1783889 := bstep (se 2 (by rfl) ⟨668958, by rfl⟩ : syracuseStep 1783889 = 1337917) B1337917
theorem B1783907 : Blo 1188411 1783907 := bstep (se 1 (by rfl) ⟨1337930, by rfl⟩ : syracuseStep 1783907 = 2675861) B2675861
theorem B4012145 : Blo 1188411 4012145 := bstep (se 2 (by rfl) ⟨1504554, by rfl⟩ : syracuseStep 4012145 = 3009109) B3009109
theorem B1505395 : Blo 1188411 1505395 := bstep (se 1 (by rfl) ⟨1129046, by rfl⟩ : syracuseStep 1505395 = 2258093) B2258093
theorem B1783937 : Blo 1188411 1783937 := bstep (se 2 (by rfl) ⟨668976, by rfl⟩ : syracuseStep 1783937 = 1337953) B1337953
theorem B1783955 : Blo 1188411 1783955 := bstep (se 1 (by rfl) ⟨1337966, by rfl⟩ : syracuseStep 1783955 = 2675933) B2675933
theorem B1783985 : Blo 1188411 1783985 := bstep (se 2 (by rfl) ⟨668994, by rfl⟩ : syracuseStep 1783985 = 1337989) B1337989
theorem B3012785 : Blo 1188411 3012785 := bstep (se 2 (by rfl) ⟨1129794, by rfl⟩ : syracuseStep 3012785 = 2259589) B2259589
theorem B1784003 : Blo 1188411 1784003 := bstep (se 1 (by rfl) ⟨1338002, by rfl⟩ : syracuseStep 1784003 = 2676005) B2676005
theorem B1784033 : Blo 1188411 1784033 := bstep (se 2 (by rfl) ⟨669012, by rfl⟩ : syracuseStep 1784033 = 1338025) B1338025
theorem B3012835 : Blo 1188411 3012835 := bstep (se 1 (by rfl) ⟨2259626, by rfl⟩ : syracuseStep 3012835 = 4519253) B4519253
theorem B2676977 : Blo 1188411 2676977 := bstep (se 2 (by rfl) ⟨1003866, by rfl⟩ : syracuseStep 2676977 = 2007733) B2007733
theorem B1784051 : Blo 1188411 1784051 := bstep (se 1 (by rfl) ⟨1338038, by rfl⟩ : syracuseStep 1784051 = 2676077) B2676077
theorem B2676995 : Blo 1188411 2676995 := bstep (se 1 (by rfl) ⟨2007746, by rfl⟩ : syracuseStep 2676995 = 4015493) B4015493
theorem B3619075 : Blo 1188411 3619075 := bstep (se 1 (by rfl) ⟨2714306, by rfl⟩ : syracuseStep 3619075 = 5428613) B5428613
theorem B1784081 : Blo 1188411 1784081 := bstep (se 2 (by rfl) ⟨669030, by rfl⟩ : syracuseStep 1784081 = 1338061) B1338061
theorem B1784099 : Blo 1188411 1784099 := bstep (se 1 (by rfl) ⟨1338074, by rfl⟩ : syracuseStep 1784099 = 2676149) B2676149
theorem B3807533 : Blo 1188411 3807533 := bstep (se 3 (by rfl) ⟨713912, by rfl⟩ : syracuseStep 3807533 = 1427825) B1427825
theorem B2857265 : Blo 1188411 2857265 := bstep (se 2 (by rfl) ⟨1071474, by rfl⟩ : syracuseStep 2857265 = 2142949) B2142949
theorem B1784129 : Blo 1188411 1784129 := bstep (se 2 (by rfl) ⟨669048, by rfl⟩ : syracuseStep 1784129 = 1338097) B1338097
theorem B2144593 : Blo 1188411 2144593 := bstep (se 2 (by rfl) ⟨804222, by rfl⟩ : syracuseStep 2144593 = 1608445) B1608445
theorem B1784147 : Blo 1188411 1784147 := bstep (se 1 (by rfl) ⟨1338110, by rfl⟩ : syracuseStep 1784147 = 2676221) B2676221
theorem B1784177 : Blo 1188411 1784177 := bstep (se 2 (by rfl) ⟨669066, by rfl⟩ : syracuseStep 1784177 = 1338133) B1338133
theorem B3012977 : Blo 1188411 3012977 := bstep (se 2 (by rfl) ⟨1129866, by rfl⟩ : syracuseStep 3012977 = 2259733) B2259733
theorem B1784195 : Blo 1188411 1784195 := bstep (se 1 (by rfl) ⟨1338146, by rfl⟩ : syracuseStep 1784195 = 2676293) B2676293
theorem B2857361 : Blo 1188411 2857361 := bstep (se 2 (by rfl) ⟨1071510, by rfl⟩ : syracuseStep 2857361 = 2143021) B2143021
theorem B1784225 : Blo 1188411 1784225 := bstep (se 2 (by rfl) ⟨669084, by rfl⟩ : syracuseStep 1784225 = 1338169) B1338169
theorem B1784243 : Blo 1188411 1784243 := bstep (se 1 (by rfl) ⟨1338182, by rfl⟩ : syracuseStep 1784243 = 2676365) B2676365
theorem B7829965 : Blo 1188411 7829965 := bstep (se 3 (by rfl) ⟨1468118, by rfl⟩ : syracuseStep 7829965 = 2936237) B2936237
theorem B1784273 : Blo 1188411 1784273 := bstep (se 2 (by rfl) ⟨669102, by rfl⟩ : syracuseStep 1784273 = 1338205) B1338205
theorem B1784291 : Blo 1188411 1784291 := bstep (se 1 (by rfl) ⟨1338218, by rfl⟩ : syracuseStep 1784291 = 2676437) B2676437
theorem B1784321 : Blo 1188411 1784321 := bstep (se 2 (by rfl) ⟨669120, by rfl⟩ : syracuseStep 1784321 = 1338241) B1338241
theorem B9034253 : Blo 1188411 9034253 := bstep (se 3 (by rfl) ⟨1693922, by rfl⟩ : syracuseStep 9034253 = 3387845) B3387845
theorem B2677265 : Blo 1188411 2677265 := bstep (se 2 (by rfl) ⟨1003974, by rfl⟩ : syracuseStep 2677265 = 2007949) B2007949
theorem B1784339 : Blo 1188411 1784339 := bstep (se 1 (by rfl) ⟨1338254, by rfl⟩ : syracuseStep 1784339 = 2676509) B2676509
theorem B2677283 : Blo 1188411 2677283 := bstep (se 1 (by rfl) ⟨2007962, by rfl⟩ : syracuseStep 2677283 = 4015925) B4015925
theorem B2005553 : Blo 1188411 2005553 := bstep (se 2 (by rfl) ⟨752082, by rfl⟩ : syracuseStep 2005553 = 1504165) B1504165
theorem B1784369 : Blo 1188411 1784369 := bstep (se 2 (by rfl) ⟨669138, by rfl⟩ : syracuseStep 1784369 = 1338277) B1338277
theorem B2259505 : Blo 1188411 2259505 := bstep (se 2 (by rfl) ⟨847314, by rfl⟩ : syracuseStep 2259505 = 1694629) B1694629
theorem B1784387 : Blo 1188411 1784387 := bstep (se 1 (by rfl) ⟨1338290, by rfl⟩ : syracuseStep 1784387 = 2676581) B2676581
theorem B1784417 : Blo 1188411 1784417 := bstep (se 2 (by rfl) ⟨669156, by rfl⟩ : syracuseStep 1784417 = 1338313) B1338313
theorem B3431011 : Blo 1188411 3431011 := bstep (se 1 (by rfl) ⟨2573258, by rfl⟩ : syracuseStep 3431011 = 5146517) B5146517
theorem B1505891 : Blo 1188411 1505891 := bstep (se 1 (by rfl) ⟨1129418, by rfl⟩ : syracuseStep 1505891 = 2258837) B2258837
theorem B1784435 : Blo 1188411 1784435 := bstep (se 1 (by rfl) ⟨1338326, by rfl⟩ : syracuseStep 1784435 = 2676653) B2676653
theorem B4012685 : Blo 1188411 4012685 := bstep (se 3 (by rfl) ⟨752378, by rfl⟩ : syracuseStep 4012685 = 1504757) B1504757
theorem B1784465 : Blo 1188411 1784465 := bstep (se 2 (by rfl) ⟨669174, by rfl⟩ : syracuseStep 1784465 = 1338349) B1338349
theorem B4512419 : Blo 1188411 4512419 := bstep (se 1 (by rfl) ⟨3384314, by rfl⟩ : syracuseStep 4512419 = 6768629) B6768629
theorem B5077667 : Blo 1188411 5077667 := bstep (se 1 (by rfl) ⟨3808250, by rfl⟩ : syracuseStep 5077667 = 7616501) B7616501
theorem B1784483 : Blo 1188411 1784483 := bstep (se 1 (by rfl) ⟨1338362, by rfl⟩ : syracuseStep 1784483 = 2676725) B2676725
theorem B2005681 : Blo 1188411 2005681 := bstep (se 2 (by rfl) ⟨752130, by rfl⟩ : syracuseStep 2005681 = 1504261) B1504261
theorem B1784513 : Blo 1188411 1784513 := bstep (se 2 (by rfl) ⟨669192, by rfl⟩ : syracuseStep 1784513 = 1338385) B1338385
theorem B4012739 : Blo 1188411 4012739 := bstep (se 1 (by rfl) ⟨3009554, by rfl⟩ : syracuseStep 4012739 = 6019109) B6019109
theorem B2005715 : Blo 1188411 2005715 := bstep (se 1 (by rfl) ⟨1504286, by rfl⟩ : syracuseStep 2005715 = 3008573) B3008573
theorem B1784531 : Blo 1188411 1784531 := bstep (se 1 (by rfl) ⟨1338398, by rfl⟩ : syracuseStep 1784531 = 2676797) B2676797
theorem B2538211 : Blo 1188411 2538211 := bstep (se 1 (by rfl) ⟨1903658, by rfl⟩ : syracuseStep 2538211 = 3807317) B3807317
theorem B13392611 : Blo 1188411 13392611 := bstep (se 1 (by rfl) ⟨10044458, by rfl⟩ : syracuseStep 13392611 = 20088917) B20088917
theorem B1784561 : Blo 1188411 1784561 := bstep (se 2 (by rfl) ⟨669210, by rfl⟩ : syracuseStep 1784561 = 1338421) B1338421
theorem B1784579 : Blo 1188411 1784579 := bstep (se 1 (by rfl) ⟨1338434, by rfl⟩ : syracuseStep 1784579 = 2676869) B2676869
theorem B1784609 : Blo 1188411 1784609 := bstep (se 2 (by rfl) ⟨669228, by rfl⟩ : syracuseStep 1784609 = 1338457) B1338457
theorem B2677553 : Blo 1188411 2677553 := bstep (se 2 (by rfl) ⟨1004082, by rfl⟩ : syracuseStep 2677553 = 2008165) B2008165
theorem B1784627 : Blo 1188411 1784627 := bstep (se 1 (by rfl) ⟨1338470, by rfl⟩ : syracuseStep 1784627 = 2676941) B2676941
theorem B1694515 : Blo 1188411 1694515 := bstep (se 1 (by rfl) ⟨1270886, by rfl⟩ : syracuseStep 1694515 = 2541773) B2541773
theorem B2677571 : Blo 1188411 2677571 := bstep (se 1 (by rfl) ⟨2008178, by rfl⟩ : syracuseStep 2677571 = 4016357) B4016357
theorem B1784657 : Blo 1188411 1784657 := bstep (se 2 (by rfl) ⟨669246, by rfl⟩ : syracuseStep 1784657 = 1338493) B1338493
theorem B2005843 : Blo 1188411 2005843 := bstep (se 1 (by rfl) ⟨1504382, by rfl⟩ : syracuseStep 2005843 = 3008765) B3008765
theorem B1784675 : Blo 1188411 1784675 := bstep (se 1 (by rfl) ⟨1338506, by rfl⟩ : syracuseStep 1784675 = 2677013) B2677013
theorem B1784705 : Blo 1188411 1784705 := bstep (se 2 (by rfl) ⟨669264, by rfl⟩ : syracuseStep 1784705 = 1338529) B1338529
theorem B3619729 : Blo 1188411 3619729 := bstep (se 2 (by rfl) ⟨1357398, by rfl⟩ : syracuseStep 3619729 = 2714797) B2714797
theorem B1784723 : Blo 1188411 1784723 := bstep (se 1 (by rfl) ⟨1338542, by rfl⟩ : syracuseStep 1784723 = 2677085) B2677085
theorem B1784753 : Blo 1188411 1784753 := bstep (se 2 (by rfl) ⟨669282, by rfl⟩ : syracuseStep 1784753 = 1338565) B1338565
theorem B1784771 : Blo 1188411 1784771 := bstep (se 1 (by rfl) ⟨1338578, by rfl⟩ : syracuseStep 1784771 = 2677157) B2677157
theorem B4013009 : Blo 1188411 4013009 := bstep (se 2 (by rfl) ⟨1504878, by rfl⟩ : syracuseStep 4013009 = 3009757) B3009757
theorem B2005985 : Blo 1188411 2005985 := bstep (se 2 (by rfl) ⟨752244, by rfl⟩ : syracuseStep 2005985 = 1504489) B1504489
theorem B1784801 : Blo 1188411 1784801 := bstep (se 2 (by rfl) ⟨669300, by rfl⟩ : syracuseStep 1784801 = 1338601) B1338601
theorem B6020081 : Blo 1188411 6020081 := bstep (se 2 (by rfl) ⟨2257530, by rfl⟩ : syracuseStep 6020081 = 4515061) B4515061
theorem B1784819 : Blo 1188411 1784819 := bstep (se 1 (by rfl) ⟨1338614, by rfl⟩ : syracuseStep 1784819 = 2677229) B2677229
theorem B1784849 : Blo 1188411 1784849 := bstep (se 2 (by rfl) ⟨669318, by rfl⟩ : syracuseStep 1784849 = 1338637) B1338637
theorem B1809427 : Blo 1188411 1809427 := bstep (se 1 (by rfl) ⟨1357070, by rfl⟩ : syracuseStep 1809427 = 2714141) B2714141
theorem B1784867 : Blo 1188411 1784867 := bstep (se 1 (by rfl) ⟨1338650, by rfl⟩ : syracuseStep 1784867 = 2677301) B2677301
theorem B1784897 : Blo 1188411 1784897 := bstep (se 2 (by rfl) ⟨669336, by rfl⟩ : syracuseStep 1784897 = 1338673) B1338673
theorem B2677841 : Blo 1188411 2677841 := bstep (se 2 (by rfl) ⟨1004190, by rfl⟩ : syracuseStep 2677841 = 2008381) B2008381
theorem B1784915 : Blo 1188411 1784915 := bstep (se 1 (by rfl) ⟨1338686, by rfl⟩ : syracuseStep 1784915 = 2677373) B2677373
theorem B2006113 : Blo 1188411 2006113 := bstep (se 2 (by rfl) ⟨752292, by rfl⟩ : syracuseStep 2006113 = 1504585) B1504585
theorem B2677859 : Blo 1188411 2677859 := bstep (se 1 (by rfl) ⟨2008394, by rfl⟩ : syracuseStep 2677859 = 4016789) B4016789
theorem B1784945 : Blo 1188411 1784945 := bstep (se 2 (by rfl) ⟨669354, by rfl⟩ : syracuseStep 1784945 = 1338709) B1338709
theorem B2006147 : Blo 1188411 2006147 := bstep (se 1 (by rfl) ⟨1504610, by rfl⟩ : syracuseStep 2006147 = 3009221) B3009221
theorem B1784963 : Blo 1188411 1784963 := bstep (se 1 (by rfl) ⟨1338722, by rfl⟩ : syracuseStep 1784963 = 2677445) B2677445
theorem B1784993 : Blo 1188411 1784993 := bstep (se 2 (by rfl) ⟨669372, by rfl⟩ : syracuseStep 1784993 = 1338745) B1338745
theorem B1785011 : Blo 1188411 1785011 := bstep (se 1 (by rfl) ⟨1338758, by rfl⟩ : syracuseStep 1785011 = 2677517) B2677517
theorem B7625933 : Blo 1188411 7625933 := bstep (se 3 (by rfl) ⟨1429862, by rfl⟩ : syracuseStep 7625933 = 2859725) B2859725
theorem B1785041 : Blo 1188411 1785041 := bstep (se 2 (by rfl) ⟨669390, by rfl⟩ : syracuseStep 1785041 = 1338781) B1338781
theorem B1785059 : Blo 1188411 1785059 := bstep (se 1 (by rfl) ⟨1338794, by rfl⟩ : syracuseStep 1785059 = 2677589) B2677589
theorem B1785089 : Blo 1188411 1785089 := bstep (se 2 (by rfl) ⟨669408, by rfl⟩ : syracuseStep 1785089 = 1338817) B1338817
theorem B2006275 : Blo 1188411 2006275 := bstep (se 1 (by rfl) ⟨1504706, by rfl⟩ : syracuseStep 2006275 = 3009413) B3009413
theorem B6774029 : Blo 1188411 6774029 := bstep (se 3 (by rfl) ⟨1270130, by rfl⟩ : syracuseStep 6774029 = 2540261) B2540261
theorem B1375507 : Blo 1188411 1375507 := bstep (se 1 (by rfl) ⟨1031630, by rfl⟩ : syracuseStep 1375507 = 2063261) B2063261
theorem B1785107 : Blo 1188411 1785107 := bstep (se 1 (by rfl) ⟨1338830, by rfl⟩ : syracuseStep 1785107 = 2677661) B2677661
theorem B1506595 : Blo 1188411 1506595 := bstep (se 1 (by rfl) ⟨1129946, by rfl⟩ : syracuseStep 1506595 = 2259893) B2259893
theorem B5717297 : Blo 1188411 5717297 := bstep (se 2 (by rfl) ⟨2143986, by rfl⟩ : syracuseStep 5717297 = 4287973) B4287973
theorem B1785137 : Blo 1188411 1785137 := bstep (se 2 (by rfl) ⟨669426, by rfl⟩ : syracuseStep 1785137 = 1338853) B1338853
theorem B1785155 : Blo 1188411 1785155 := bstep (se 1 (by rfl) ⟨1338866, by rfl⟩ : syracuseStep 1785155 = 2677733) B2677733
theorem B1785185 : Blo 1188411 1785185 := bstep (se 2 (by rfl) ⟨669444, by rfl⟩ : syracuseStep 1785185 = 1338889) B1338889
theorem B2678129 : Blo 1188411 2678129 := bstep (se 2 (by rfl) ⟨1004298, by rfl⟩ : syracuseStep 2678129 = 2008597) B2008597
theorem B1785203 : Blo 1188411 1785203 := bstep (se 1 (by rfl) ⟨1338902, by rfl⟩ : syracuseStep 1785203 = 2677805) B2677805
theorem B2678147 : Blo 1188411 2678147 := bstep (se 1 (by rfl) ⟨2008610, by rfl⟩ : syracuseStep 2678147 = 4017221) B4017221
theorem B2006417 : Blo 1188411 2006417 := bstep (se 2 (by rfl) ⟨752406, by rfl⟩ : syracuseStep 2006417 = 1504813) B1504813
theorem B1785233 : Blo 1188411 1785233 := bstep (se 2 (by rfl) ⟨669462, by rfl⟩ : syracuseStep 1785233 = 1338925) B1338925
theorem B1809811 : Blo 1188411 1809811 := bstep (se 1 (by rfl) ⟨1357358, by rfl⟩ : syracuseStep 1809811 = 2714717) B2714717
theorem B1785251 : Blo 1188411 1785251 := bstep (se 1 (by rfl) ⟨1338938, by rfl⟩ : syracuseStep 1785251 = 2677877) B2677877
theorem B1785281 : Blo 1188411 1785281 := bstep (se 2 (by rfl) ⟨669480, by rfl⟩ : syracuseStep 1785281 = 1338961) B1338961
theorem B7617989 : Blo 1188411 7617989 := bstep (se 4 (by rfl) ⟨714186, by rfl⟩ : syracuseStep 7617989 = 1428373) B1428373
theorem B1785299 : Blo 1188411 1785299 := bstep (se 1 (by rfl) ⟨1338974, by rfl⟩ : syracuseStep 1785299 = 2677949) B2677949
theorem B4013549 : Blo 1188411 4013549 := bstep (se 3 (by rfl) ⟨752540, by rfl⟩ : syracuseStep 4013549 = 1505081) B1505081
theorem B1785329 : Blo 1188411 1785329 := bstep (se 2 (by rfl) ⟨669498, by rfl⟩ : syracuseStep 1785329 = 1338997) B1338997
theorem B1785347 : Blo 1188411 1785347 := bstep (se 1 (by rfl) ⟨1339010, by rfl⟩ : syracuseStep 1785347 = 2678021) B2678021
theorem B2006545 : Blo 1188411 2006545 := bstep (se 2 (by rfl) ⟨752454, by rfl⟩ : syracuseStep 2006545 = 1504909) B1504909
theorem B4013603 : Blo 1188411 4013603 := bstep (se 1 (by rfl) ⟨3010202, by rfl⟩ : syracuseStep 4013603 = 6020405) B6020405
theorem B1785377 : Blo 1188411 1785377 := bstep (se 2 (by rfl) ⟨669516, by rfl⟩ : syracuseStep 1785377 = 1339033) B1339033
theorem B2006579 : Blo 1188411 2006579 := bstep (se 1 (by rfl) ⟨1504934, by rfl⟩ : syracuseStep 2006579 = 3009869) B3009869
theorem B1785395 : Blo 1188411 1785395 := bstep (se 1 (by rfl) ⟨1339046, by rfl⟩ : syracuseStep 1785395 = 2678093) B2678093
theorem B1785425 : Blo 1188411 1785425 := bstep (se 2 (by rfl) ⟨669534, by rfl⟩ : syracuseStep 1785425 = 1339069) B1339069
theorem B1785443 : Blo 1188411 1785443 := bstep (se 1 (by rfl) ⟨1339082, by rfl⟩ : syracuseStep 1785443 = 2678165) B2678165
theorem B1785473 : Blo 1188411 1785473 := bstep (se 2 (by rfl) ⟨669552, by rfl⟩ : syracuseStep 1785473 = 1339105) B1339105
theorem B1269379 : Blo 1188411 1269379 := bstep (se 1 (by rfl) ⟨952034, by rfl⟩ : syracuseStep 1269379 = 1904069) B1904069
theorem B4513421 : Blo 1188411 4513421 := bstep (se 3 (by rfl) ⟨846266, by rfl⟩ : syracuseStep 4513421 = 1692533) B1692533
theorem B2678417 : Blo 1188411 2678417 := bstep (se 2 (by rfl) ⟨1004406, by rfl⟩ : syracuseStep 2678417 = 2008813) B2008813
theorem B1785491 : Blo 1188411 1785491 := bstep (se 1 (by rfl) ⟨1339118, by rfl⟩ : syracuseStep 1785491 = 2678237) B2678237
theorem B1785521 : Blo 1188411 1785521 := bstep (se 2 (by rfl) ⟨669570, by rfl⟩ : syracuseStep 1785521 = 1339141) B1339141
theorem B2006707 : Blo 1188411 2006707 := bstep (se 1 (by rfl) ⟨1505030, by rfl⟩ : syracuseStep 2006707 = 3010061) B3010061
theorem B1785539 : Blo 1188411 1785539 := bstep (se 1 (by rfl) ⟨1339154, by rfl⟩ : syracuseStep 1785539 = 2678309) B2678309
theorem B1785569 : Blo 1188411 1785569 := bstep (se 2 (by rfl) ⟨669588, by rfl⟩ : syracuseStep 1785569 = 1339177) B1339177
theorem B3301091 : Blo 1188411 3301091 := bstep (se 1 (by rfl) ⟨2475818, by rfl⟩ : syracuseStep 3301091 = 4951637) B4951637
theorem B10157795 : Blo 1188411 10157795 := bstep (se 1 (by rfl) ⟨7618346, by rfl⟩ : syracuseStep 10157795 = 15236693) B15236693
theorem B1785587 : Blo 1188411 1785587 := bstep (se 1 (by rfl) ⟨1339190, by rfl⟩ : syracuseStep 1785587 = 2678381) B2678381
theorem B15441677 : Blo 1188411 15441677 := bstep (se 3 (by rfl) ⟨2895314, by rfl⟩ : syracuseStep 15441677 = 5790629) B5790629
theorem B1785617 : Blo 1188411 1785617 := bstep (se 2 (by rfl) ⟨669606, by rfl⟩ : syracuseStep 1785617 = 1339213) B1339213
theorem B4013873 : Blo 1188411 4013873 := bstep (se 2 (by rfl) ⟨1505202, by rfl⟩ : syracuseStep 4013873 = 3010405) B3010405
theorem B2006849 : Blo 1188411 2006849 := bstep (se 2 (by rfl) ⟨752568, by rfl⟩ : syracuseStep 2006849 = 1505137) B1505137
theorem B2539441 : Blo 1188411 2539441 := bstep (se 2 (by rfl) ⟨952290, by rfl⟩ : syracuseStep 2539441 = 1904581) B1904581
theorem B2006977 : Blo 1188411 2006977 := bstep (se 2 (by rfl) ⟨752616, by rfl⟩ : syracuseStep 2006977 = 1505233) B1505233
theorem B2007011 : Blo 1188411 2007011 := bstep (se 1 (by rfl) ⟨1505258, by rfl⟩ : syracuseStep 2007011 = 3010517) B3010517
theorem B2007065 : Blo 1188411 2007065 := bstep (se 2 (by rfl) ⟨752649, by rfl⟩ : syracuseStep 2007065 = 1505299) B1505299
theorem B2007193 : Blo 1188411 2007193 := bstep (se 2 (by rfl) ⟨752697, by rfl⟩ : syracuseStep 2007193 = 1505395) B1505395
theorem B4014359 : Blo 1188411 4014359 := bstep (se 1 (by rfl) ⟨3010769, by rfl⟩ : syracuseStep 4014359 = 6021539) B6021539
theorem B4825433 : Blo 1188411 4825433 := bstep (se 2 (by rfl) ⟨1809537, by rfl⟩ : syracuseStep 4825433 = 3619075) B3619075
theorem B2539927 : Blo 1188411 2539927 := bstep (se 1 (by rfl) ⟨1904945, by rfl⟩ : syracuseStep 2539927 = 3809891) B3809891
theorem B5718451 : Blo 1188411 5718451 := bstep (se 1 (by rfl) ⟨4288838, by rfl⟩ : syracuseStep 5718451 = 8577677) B8577677
theorem B1270199 : Blo 1188411 1270199 := bstep (se 1 (by rfl) ⟨952649, by rfl⟩ : syracuseStep 1270199 = 1905299) B1905299
theorem B2859457 : Blo 1188411 2859457 := bstep (se 2 (by rfl) ⟨1072296, by rfl⟩ : syracuseStep 2859457 = 2144593) B2144593
theorem B2859571 : Blo 1188411 2859571 := bstep (se 1 (by rfl) ⟨2144678, by rfl⟩ : syracuseStep 2859571 = 4289357) B4289357
theorem B5079617 : Blo 1188411 5079617 := bstep (se 2 (by rfl) ⟨1904856, by rfl⟩ : syracuseStep 5079617 = 3809713) B3809713
theorem B1188427 : Blo 1188411 1188427 := bstep (se 1 (by rfl) ⟨891320, by rfl⟩ : syracuseStep 1188427 = 1782641) B1782641
theorem B1188439 : Blo 1188411 1188439 := bstep (se 1 (by rfl) ⟨891329, by rfl⟩ : syracuseStep 1188439 = 1782659) B1782659
theorem B4514393 : Blo 1188411 4514393 := bstep (se 2 (by rfl) ⟨1692897, by rfl⟩ : syracuseStep 4514393 = 3385795) B3385795
theorem B1188459 : Blo 1188411 1188459 := bstep (se 1 (by rfl) ⟨891344, by rfl⟩ : syracuseStep 1188459 = 1782689) B1782689
theorem B1188471 : Blo 1188411 1188471 := bstep (se 1 (by rfl) ⟨891353, by rfl⟩ : syracuseStep 1188471 = 1782707) B1782707
theorem B1188491 : Blo 1188411 1188491 := bstep (se 1 (by rfl) ⟨891368, by rfl⟩ : syracuseStep 1188491 = 1782737) B1782737
theorem B1188503 : Blo 1188411 1188503 := bstep (se 1 (by rfl) ⟨891377, by rfl⟩ : syracuseStep 1188503 = 1782755) B1782755
theorem B1188523 : Blo 1188411 1188523 := bstep (se 1 (by rfl) ⟨891392, by rfl⟩ : syracuseStep 1188523 = 1782785) B1782785
theorem B1188535 : Blo 1188411 1188535 := bstep (se 1 (by rfl) ⟨891401, by rfl⟩ : syracuseStep 1188535 = 1782803) B1782803
theorem B1188555 : Blo 1188411 1188555 := bstep (se 1 (by rfl) ⟨891416, by rfl⟩ : syracuseStep 1188555 = 1782833) B1782833
theorem B1188567 : Blo 1188411 1188567 := bstep (se 1 (by rfl) ⟨891425, by rfl⟩ : syracuseStep 1188567 = 1782851) B1782851
theorem B2007767 : Blo 1188411 2007767 := bstep (se 1 (by rfl) ⟨1505825, by rfl⟩ : syracuseStep 2007767 = 3011651) B3011651
theorem B8143577 : Blo 1188411 8143577 := bstep (se 2 (by rfl) ⟨3053841, by rfl⟩ : syracuseStep 8143577 = 6107683) B6107683
theorem B1188587 : Blo 1188411 1188587 := bstep (se 1 (by rfl) ⟨891440, by rfl⟩ : syracuseStep 1188587 = 1782881) B1782881
theorem B1188599 : Blo 1188411 1188599 := bstep (se 1 (by rfl) ⟨891449, by rfl⟩ : syracuseStep 1188599 = 1782899) B1782899
theorem B2573057 : Blo 1188411 2573057 := bstep (se 2 (by rfl) ⟨964896, by rfl⟩ : syracuseStep 2573057 = 1929793) B1929793
theorem B1188619 : Blo 1188411 1188619 := bstep (se 1 (by rfl) ⟨891464, by rfl⟩ : syracuseStep 1188619 = 1782929) B1782929
theorem B1188631 : Blo 1188411 1188631 := bstep (se 1 (by rfl) ⟨891473, by rfl⟩ : syracuseStep 1188631 = 1782947) B1782947
theorem B1188651 : Blo 1188411 1188651 := bstep (se 1 (by rfl) ⟨891488, by rfl⟩ : syracuseStep 1188651 = 1782977) B1782977
theorem B4014899 : Blo 1188411 4014899 := bstep (se 1 (by rfl) ⟨3011174, by rfl⟩ : syracuseStep 4014899 = 6022349) B6022349
theorem B1188663 : Blo 1188411 1188663 := bstep (se 1 (by rfl) ⟨891497, by rfl⟩ : syracuseStep 1188663 = 1782995) B1782995
theorem B1188683 : Blo 1188411 1188683 := bstep (se 1 (by rfl) ⟨891512, by rfl⟩ : syracuseStep 1188683 = 1783025) B1783025
theorem B1188695 : Blo 1188411 1188695 := bstep (se 1 (by rfl) ⟨891521, by rfl⟩ : syracuseStep 1188695 = 1783043) B1783043
theorem B2007895 : Blo 1188411 2007895 := bstep (se 1 (by rfl) ⟨1505921, by rfl⟩ : syracuseStep 2007895 = 3011843) B3011843
theorem B1188715 : Blo 1188411 1188715 := bstep (se 1 (by rfl) ⟨891536, by rfl⟩ : syracuseStep 1188715 = 1783073) B1783073
theorem B1188727 : Blo 1188411 1188727 := bstep (se 1 (by rfl) ⟨891545, by rfl⟩ : syracuseStep 1188727 = 1783091) B1783091
theorem B1188747 : Blo 1188411 1188747 := bstep (se 1 (by rfl) ⟨891560, by rfl⟩ : syracuseStep 1188747 = 1783121) B1783121
theorem B1188759 : Blo 1188411 1188759 := bstep (se 1 (by rfl) ⟨891569, by rfl⟩ : syracuseStep 1188759 = 1783139) B1783139
theorem B3810199 : Blo 1188411 3810199 := bstep (se 1 (by rfl) ⟨2857649, by rfl⟩ : syracuseStep 3810199 = 5715299) B5715299
theorem B1188779 : Blo 1188411 1188779 := bstep (se 1 (by rfl) ⟨891584, by rfl⟩ : syracuseStep 1188779 = 1783169) B1783169
theorem B1188791 : Blo 1188411 1188791 := bstep (se 1 (by rfl) ⟨891593, by rfl⟩ : syracuseStep 1188791 = 1783187) B1783187
theorem B1188811 : Blo 1188411 1188811 := bstep (se 1 (by rfl) ⟨891608, by rfl⟩ : syracuseStep 1188811 = 1783217) B1783217
theorem B1188823 : Blo 1188411 1188823 := bstep (se 1 (by rfl) ⟨891617, by rfl⟩ : syracuseStep 1188823 = 1783235) B1783235
theorem B3384281 : Blo 1188411 3384281 := bstep (se 2 (by rfl) ⟨1269105, by rfl⟩ : syracuseStep 3384281 = 2538211) B2538211
theorem B1188843 : Blo 1188411 1188843 := bstep (se 1 (by rfl) ⟨891632, by rfl⟩ : syracuseStep 1188843 = 1783265) B1783265
theorem B1188855 : Blo 1188411 1188855 := bstep (se 1 (by rfl) ⟨891641, by rfl⟩ : syracuseStep 1188855 = 1783283) B1783283
theorem B1188875 : Blo 1188411 1188875 := bstep (se 1 (by rfl) ⟨891656, by rfl⟩ : syracuseStep 1188875 = 1783313) B1783313
theorem B1188887 : Blo 1188411 1188887 := bstep (se 1 (by rfl) ⟨891665, by rfl⟩ : syracuseStep 1188887 = 1783331) B1783331
theorem B1188907 : Blo 1188411 1188907 := bstep (se 1 (by rfl) ⟨891680, by rfl⟩ : syracuseStep 1188907 = 1783361) B1783361
theorem B7619629 : Blo 1188411 7619629 := bstep (se 3 (by rfl) ⟨1428680, by rfl⟩ : syracuseStep 7619629 = 2857361) B2857361
theorem B1188919 : Blo 1188411 1188919 := bstep (se 1 (by rfl) ⟨891689, by rfl⟩ : syracuseStep 1188919 = 1783379) B1783379
theorem B4015169 : Blo 1188411 4015169 := bstep (se 2 (by rfl) ⟨1505688, by rfl⟩ : syracuseStep 4015169 = 3011377) B3011377
theorem B1188939 : Blo 1188411 1188939 := bstep (se 1 (by rfl) ⟨891704, by rfl⟩ : syracuseStep 1188939 = 1783409) B1783409
theorem B1188951 : Blo 1188411 1188951 := bstep (se 1 (by rfl) ⟨891713, by rfl⟩ : syracuseStep 1188951 = 1783427) B1783427
theorem B1188971 : Blo 1188411 1188971 := bstep (se 1 (by rfl) ⟨891728, by rfl⟩ : syracuseStep 1188971 = 1783457) B1783457
theorem B1188983 : Blo 1188411 1188983 := bstep (se 1 (by rfl) ⟨891737, by rfl⟩ : syracuseStep 1188983 = 1783475) B1783475
theorem B1189003 : Blo 1188411 1189003 := bstep (se 1 (by rfl) ⟨891752, by rfl⟩ : syracuseStep 1189003 = 1783505) B1783505
theorem B1189015 : Blo 1188411 1189015 := bstep (se 1 (by rfl) ⟨891761, by rfl⟩ : syracuseStep 1189015 = 1783523) B1783523
theorem B11748503 : Blo 1188411 11748503 := bstep (se 1 (by rfl) ⟨8811377, by rfl⟩ : syracuseStep 11748503 = 17622755) B17622755
theorem B1189035 : Blo 1188411 1189035 := bstep (se 1 (by rfl) ⟨891776, by rfl⟩ : syracuseStep 1189035 = 1783553) B1783553
theorem B1189047 : Blo 1188411 1189047 := bstep (se 1 (by rfl) ⟨891785, by rfl⟩ : syracuseStep 1189047 = 1783571) B1783571
theorem B4826305 : Blo 1188411 4826305 := bstep (se 2 (by rfl) ⟨1809864, by rfl⟩ : syracuseStep 4826305 = 3619729) B3619729
theorem B1189067 : Blo 1188411 1189067 := bstep (se 1 (by rfl) ⟨891800, by rfl⟩ : syracuseStep 1189067 = 1783601) B1783601
theorem B1189079 : Blo 1188411 1189079 := bstep (se 1 (by rfl) ⟨891809, by rfl⟩ : syracuseStep 1189079 = 1783619) B1783619
theorem B1189099 : Blo 1188411 1189099 := bstep (se 1 (by rfl) ⟨891824, by rfl⟩ : syracuseStep 1189099 = 1783649) B1783649
theorem B1189111 : Blo 1188411 1189111 := bstep (se 1 (by rfl) ⟨891833, by rfl⟩ : syracuseStep 1189111 = 1783667) B1783667
theorem B1189131 : Blo 1188411 1189131 := bstep (se 1 (by rfl) ⟨891848, by rfl⟩ : syracuseStep 1189131 = 1783697) B1783697
theorem B1189143 : Blo 1188411 1189143 := bstep (se 1 (by rfl) ⟨891857, by rfl⟩ : syracuseStep 1189143 = 1783715) B1783715
theorem B1189163 : Blo 1188411 1189163 := bstep (se 1 (by rfl) ⟨891872, by rfl⟩ : syracuseStep 1189163 = 1783745) B1783745
theorem B1189175 : Blo 1188411 1189175 := bstep (se 1 (by rfl) ⟨891881, by rfl⟩ : syracuseStep 1189175 = 1783763) B1783763
theorem B1189195 : Blo 1188411 1189195 := bstep (se 1 (by rfl) ⟨891896, by rfl⟩ : syracuseStep 1189195 = 1783793) B1783793
theorem B3810635 : Blo 1188411 3810635 := bstep (se 1 (by rfl) ⟨2857976, by rfl⟩ : syracuseStep 3810635 = 5715953) B5715953
theorem B1189207 : Blo 1188411 1189207 := bstep (se 1 (by rfl) ⟨891905, by rfl⟩ : syracuseStep 1189207 = 1783811) B1783811
theorem B1189227 : Blo 1188411 1189227 := bstep (se 1 (by rfl) ⟨891920, by rfl⟩ : syracuseStep 1189227 = 1783841) B1783841
theorem B1189239 : Blo 1188411 1189239 := bstep (se 1 (by rfl) ⟨891929, by rfl⟩ : syracuseStep 1189239 = 1783859) B1783859
theorem B1189259 : Blo 1188411 1189259 := bstep (se 1 (by rfl) ⟨891944, by rfl⟩ : syracuseStep 1189259 = 1783889) B1783889
theorem B1189271 : Blo 1188411 1189271 := bstep (se 1 (by rfl) ⟨891953, by rfl⟩ : syracuseStep 1189271 = 1783907) B1783907
theorem B1189291 : Blo 1188411 1189291 := bstep (se 1 (by rfl) ⟨891968, by rfl⟩ : syracuseStep 1189291 = 1783937) B1783937
theorem B1189303 : Blo 1188411 1189303 := bstep (se 1 (by rfl) ⟨891977, by rfl⟩ : syracuseStep 1189303 = 1783955) B1783955
theorem B1189323 : Blo 1188411 1189323 := bstep (se 1 (by rfl) ⟨891992, by rfl⟩ : syracuseStep 1189323 = 1783985) B1783985
theorem B2008523 : Blo 1188411 2008523 := bstep (se 1 (by rfl) ⟨1506392, by rfl⟩ : syracuseStep 2008523 = 3012785) B3012785
theorem B1189335 : Blo 1188411 1189335 := bstep (se 1 (by rfl) ⟨892001, by rfl⟩ : syracuseStep 1189335 = 1784003) B1784003
theorem B1189355 : Blo 1188411 1189355 := bstep (se 1 (by rfl) ⟨892016, by rfl⟩ : syracuseStep 1189355 = 1784033) B1784033
theorem B1189367 : Blo 1188411 1189367 := bstep (se 1 (by rfl) ⟨892025, by rfl⟩ : syracuseStep 1189367 = 1784051) B1784051
theorem B1189387 : Blo 1188411 1189387 := bstep (se 1 (by rfl) ⟨892040, by rfl⟩ : syracuseStep 1189387 = 1784081) B1784081
theorem B6022673 : Blo 1188411 6022673 := bstep (se 2 (by rfl) ⟨2258502, by rfl⟩ : syracuseStep 6022673 = 4517005) B4517005
theorem B1189399 : Blo 1188411 1189399 := bstep (se 1 (by rfl) ⟨892049, by rfl⟩ : syracuseStep 1189399 = 1784099) B1784099
theorem B1189419 : Blo 1188411 1189419 := bstep (se 1 (by rfl) ⟨892064, by rfl⟩ : syracuseStep 1189419 = 1784129) B1784129
theorem B2541107 : Blo 1188411 2541107 := bstep (se 1 (by rfl) ⟨1905830, by rfl⟩ : syracuseStep 2541107 = 3811661) B3811661
theorem B1189431 : Blo 1188411 1189431 := bstep (se 1 (by rfl) ⟨892073, by rfl⟩ : syracuseStep 1189431 = 1784147) B1784147
theorem B1189451 : Blo 1188411 1189451 := bstep (se 1 (by rfl) ⟨892088, by rfl⟩ : syracuseStep 1189451 = 1784177) B1784177
theorem B2008651 : Blo 1188411 2008651 := bstep (se 1 (by rfl) ⟨1506488, by rfl⟩ : syracuseStep 2008651 = 3012977) B3012977
theorem B1189463 : Blo 1188411 1189463 := bstep (se 1 (by rfl) ⟨892097, by rfl⟩ : syracuseStep 1189463 = 1784195) B1784195
theorem B4015709 : Blo 1188411 4015709 := bstep (se 3 (by rfl) ⟨752945, by rfl⟩ : syracuseStep 4015709 = 1505891) B1505891
theorem B1189483 : Blo 1188411 1189483 := bstep (se 1 (by rfl) ⟨892112, by rfl⟩ : syracuseStep 1189483 = 1784225) B1784225
theorem B1189495 : Blo 1188411 1189495 := bstep (se 1 (by rfl) ⟨892121, by rfl⟩ : syracuseStep 1189495 = 1784243) B1784243
theorem B1189515 : Blo 1188411 1189515 := bstep (se 1 (by rfl) ⟨892136, by rfl⟩ : syracuseStep 1189515 = 1784273) B1784273
theorem B1189527 : Blo 1188411 1189527 := bstep (se 1 (by rfl) ⟨892145, by rfl⟩ : syracuseStep 1189527 = 1784291) B1784291
theorem B1189547 : Blo 1188411 1189547 := bstep (se 1 (by rfl) ⟨892160, by rfl⟩ : syracuseStep 1189547 = 1784321) B1784321
theorem B6022835 : Blo 1188411 6022835 := bstep (se 1 (by rfl) ⟨4517126, by rfl⟩ : syracuseStep 6022835 = 9034253) B9034253
theorem B1189559 : Blo 1188411 1189559 := bstep (se 1 (by rfl) ⟨892169, by rfl⟩ : syracuseStep 1189559 = 1784339) B1784339
theorem B1337035 : Blo 1188411 1337035 := bstep (se 1 (by rfl) ⟨1002776, by rfl⟩ : syracuseStep 1337035 = 2005553) B2005553
theorem B1189579 : Blo 1188411 1189579 := bstep (se 1 (by rfl) ⟨892184, by rfl⟩ : syracuseStep 1189579 = 1784369) B1784369
theorem B1189591 : Blo 1188411 1189591 := bstep (se 1 (by rfl) ⟨892193, by rfl⟩ : syracuseStep 1189591 = 1784387) B1784387
theorem B2008793 : Blo 1188411 2008793 := bstep (se 2 (by rfl) ⟨753297, by rfl⟩ : syracuseStep 2008793 = 1506595) B1506595
theorem B1189611 : Blo 1188411 1189611 := bstep (se 1 (by rfl) ⟨892208, by rfl⟩ : syracuseStep 1189611 = 1784417) B1784417
theorem B1189623 : Blo 1188411 1189623 := bstep (se 1 (by rfl) ⟨892217, by rfl⟩ : syracuseStep 1189623 = 1784435) B1784435
theorem B1189643 : Blo 1188411 1189643 := bstep (se 1 (by rfl) ⟨892232, by rfl⟩ : syracuseStep 1189643 = 1784465) B1784465
theorem B9029393 : Blo 1188411 9029393 := bstep (se 2 (by rfl) ⟨3386022, by rfl⟩ : syracuseStep 9029393 = 6772045) B6772045
theorem B3008279 : Blo 1188411 3008279 := bstep (se 1 (by rfl) ⟨2256209, by rfl⟩ : syracuseStep 3008279 = 4512419) B4512419
theorem B1189655 : Blo 1188411 1189655 := bstep (se 1 (by rfl) ⟨892241, by rfl⟩ : syracuseStep 1189655 = 1784483) B1784483
theorem B4835095 : Blo 1188411 4835095 := bstep (se 1 (by rfl) ⟨3626321, by rfl⟩ : syracuseStep 4835095 = 7252643) B7252643
theorem B1189675 : Blo 1188411 1189675 := bstep (se 1 (by rfl) ⟨892256, by rfl⟩ : syracuseStep 1189675 = 1784513) B1784513
theorem B1337143 : Blo 1188411 1337143 := bstep (se 1 (by rfl) ⟨1002857, by rfl⟩ : syracuseStep 1337143 = 2005715) B2005715
theorem B1189687 : Blo 1188411 1189687 := bstep (se 1 (by rfl) ⟨892265, by rfl⟩ : syracuseStep 1189687 = 1784531) B1784531
theorem B1189707 : Blo 1188411 1189707 := bstep (se 1 (by rfl) ⟨892280, by rfl⟩ : syracuseStep 1189707 = 1784561) B1784561
theorem B1189719 : Blo 1188411 1189719 := bstep (se 1 (by rfl) ⟨892289, by rfl⟩ : syracuseStep 1189719 = 1784579) B1784579
theorem B30885731 : Blo 1188411 30885731 := bstep (se 1 (by rfl) ⟨23164298, by rfl⟩ : syracuseStep 30885731 = 46328597) B46328597
theorem B1189739 : Blo 1188411 1189739 := bstep (se 1 (by rfl) ⟨892304, by rfl⟩ : syracuseStep 1189739 = 1784609) B1784609
theorem B1189751 : Blo 1188411 1189751 := bstep (se 1 (by rfl) ⟨892313, by rfl⟩ : syracuseStep 1189751 = 1784627) B1784627
theorem B1189771 : Blo 1188411 1189771 := bstep (se 1 (by rfl) ⟨892328, by rfl⟩ : syracuseStep 1189771 = 1784657) B1784657
theorem B1189783 : Blo 1188411 1189783 := bstep (se 1 (by rfl) ⟨892337, by rfl⟩ : syracuseStep 1189783 = 1784675) B1784675
theorem B1189803 : Blo 1188411 1189803 := bstep (se 1 (by rfl) ⟨892352, by rfl⟩ : syracuseStep 1189803 = 1784705) B1784705
theorem B21718961 : Blo 1188411 21718961 := bstep (se 2 (by rfl) ⟨8144610, by rfl⟩ : syracuseStep 21718961 = 16289221) B16289221
theorem B1189815 : Blo 1188411 1189815 := bstep (se 1 (by rfl) ⟨892361, by rfl⟩ : syracuseStep 1189815 = 1784723) B1784723
theorem B1189835 : Blo 1188411 1189835 := bstep (se 1 (by rfl) ⟨892376, by rfl⟩ : syracuseStep 1189835 = 1784753) B1784753
theorem B1189847 : Blo 1188411 1189847 := bstep (se 1 (by rfl) ⟨892385, by rfl⟩ : syracuseStep 1189847 = 1784771) B1784771
theorem B1337323 : Blo 1188411 1337323 := bstep (se 1 (by rfl) ⟨1002992, by rfl⟩ : syracuseStep 1337323 = 2005985) B2005985
theorem B1189867 : Blo 1188411 1189867 := bstep (se 1 (by rfl) ⟨892400, by rfl⟩ : syracuseStep 1189867 = 1784801) B1784801
theorem B1189879 : Blo 1188411 1189879 := bstep (se 1 (by rfl) ⟨892409, by rfl⟩ : syracuseStep 1189879 = 1784819) B1784819
theorem B1189899 : Blo 1188411 1189899 := bstep (se 1 (by rfl) ⟨892424, by rfl⟩ : syracuseStep 1189899 = 1784849) B1784849
theorem B1189911 : Blo 1188411 1189911 := bstep (se 1 (by rfl) ⟨892433, by rfl⟩ : syracuseStep 1189911 = 1784867) B1784867
theorem B1189931 : Blo 1188411 1189931 := bstep (se 1 (by rfl) ⟨892448, by rfl⟩ : syracuseStep 1189931 = 1784897) B1784897
theorem B1189943 : Blo 1188411 1189943 := bstep (se 1 (by rfl) ⟨892457, by rfl⟩ : syracuseStep 1189943 = 1784915) B1784915
theorem B1189963 : Blo 1188411 1189963 := bstep (se 1 (by rfl) ⟨892472, by rfl⟩ : syracuseStep 1189963 = 1784945) B1784945
theorem B1337431 : Blo 1188411 1337431 := bstep (se 1 (by rfl) ⟨1003073, by rfl⟩ : syracuseStep 1337431 = 2006147) B2006147
theorem B1189975 : Blo 1188411 1189975 := bstep (se 1 (by rfl) ⟨892481, by rfl⟩ : syracuseStep 1189975 = 1784963) B1784963
theorem B11429981 : Blo 1188411 11429981 := bstep (se 3 (by rfl) ⟨2143121, by rfl⟩ : syracuseStep 11429981 = 4286243) B4286243
theorem B1189995 : Blo 1188411 1189995 := bstep (se 1 (by rfl) ⟨892496, by rfl⟩ : syracuseStep 1189995 = 1784993) B1784993
theorem B1190007 : Blo 1188411 1190007 := bstep (se 1 (by rfl) ⟨892505, by rfl⟩ : syracuseStep 1190007 = 1785011) B1785011
theorem B1190027 : Blo 1188411 1190027 := bstep (se 1 (by rfl) ⟨892520, by rfl⟩ : syracuseStep 1190027 = 1785041) B1785041
theorem B1190039 : Blo 1188411 1190039 := bstep (se 1 (by rfl) ⟨892529, by rfl⟩ : syracuseStep 1190039 = 1785059) B1785059
theorem B1190059 : Blo 1188411 1190059 := bstep (se 1 (by rfl) ⟨892544, by rfl⟩ : syracuseStep 1190059 = 1785089) B1785089
theorem B4516019 : Blo 1188411 4516019 := bstep (se 1 (by rfl) ⟨3387014, by rfl⟩ : syracuseStep 4516019 = 6774029) B6774029
theorem B1190071 : Blo 1188411 1190071 := bstep (se 1 (by rfl) ⟨892553, by rfl⟩ : syracuseStep 1190071 = 1785107) B1785107
theorem B4516033 : Blo 1188411 4516033 := bstep (se 2 (by rfl) ⟨1693512, by rfl⟩ : syracuseStep 4516033 = 3387025) B3387025
theorem B5081291 : Blo 1188411 5081291 := bstep (se 1 (by rfl) ⟨3810968, by rfl⟩ : syracuseStep 5081291 = 7621937) B7621937
theorem B3811531 : Blo 1188411 3811531 := bstep (se 1 (by rfl) ⟨2858648, by rfl⟩ : syracuseStep 3811531 = 5717297) B5717297
theorem B1190091 : Blo 1188411 1190091 := bstep (se 1 (by rfl) ⟨892568, by rfl⟩ : syracuseStep 1190091 = 1785137) B1785137
theorem B1190103 : Blo 1188411 1190103 := bstep (se 1 (by rfl) ⟨892577, by rfl⟩ : syracuseStep 1190103 = 1785155) B1785155
theorem B1190123 : Blo 1188411 1190123 := bstep (se 1 (by rfl) ⟨892592, by rfl⟩ : syracuseStep 1190123 = 1785185) B1785185
theorem B1190135 : Blo 1188411 1190135 := bstep (se 1 (by rfl) ⟨892601, by rfl⟩ : syracuseStep 1190135 = 1785203) B1785203
theorem B1337611 : Blo 1188411 1337611 := bstep (se 1 (by rfl) ⟨1003208, by rfl⟩ : syracuseStep 1337611 = 2006417) B2006417
theorem B1190155 : Blo 1188411 1190155 := bstep (se 1 (by rfl) ⟨892616, by rfl⟩ : syracuseStep 1190155 = 1785233) B1785233
theorem B1190167 : Blo 1188411 1190167 := bstep (se 1 (by rfl) ⟨892625, by rfl⟩ : syracuseStep 1190167 = 1785251) B1785251
theorem B1190187 : Blo 1188411 1190187 := bstep (se 1 (by rfl) ⟨892640, by rfl⟩ : syracuseStep 1190187 = 1785281) B1785281
theorem B1190199 : Blo 1188411 1190199 := bstep (se 1 (by rfl) ⟨892649, by rfl⟩ : syracuseStep 1190199 = 1785299) B1785299
theorem B1190219 : Blo 1188411 1190219 := bstep (se 1 (by rfl) ⟨892664, by rfl⟩ : syracuseStep 1190219 = 1785329) B1785329
theorem B1190231 : Blo 1188411 1190231 := bstep (se 1 (by rfl) ⟨892673, by rfl⟩ : syracuseStep 1190231 = 1785347) B1785347
theorem B1190251 : Blo 1188411 1190251 := bstep (se 1 (by rfl) ⟨892688, by rfl⟩ : syracuseStep 1190251 = 1785377) B1785377
theorem B1337719 : Blo 1188411 1337719 := bstep (se 1 (by rfl) ⟨1003289, by rfl⟩ : syracuseStep 1337719 = 2006579) B2006579
theorem B1190263 : Blo 1188411 1190263 := bstep (se 1 (by rfl) ⟨892697, by rfl⟩ : syracuseStep 1190263 = 1785395) B1785395
theorem B1190283 : Blo 1188411 1190283 := bstep (se 1 (by rfl) ⟨892712, by rfl⟩ : syracuseStep 1190283 = 1785425) B1785425
theorem B1190295 : Blo 1188411 1190295 := bstep (se 1 (by rfl) ⟨892721, by rfl⟩ : syracuseStep 1190295 = 1785443) B1785443
theorem B1190315 : Blo 1188411 1190315 := bstep (se 1 (by rfl) ⟨892736, by rfl⟩ : syracuseStep 1190315 = 1785473) B1785473
theorem B3008947 : Blo 1188411 3008947 := bstep (se 1 (by rfl) ⟨2256710, by rfl⟩ : syracuseStep 3008947 = 4513421) B4513421
theorem B1190327 : Blo 1188411 1190327 := bstep (se 1 (by rfl) ⟨892745, by rfl⟩ : syracuseStep 1190327 = 1785491) B1785491
theorem B1190347 : Blo 1188411 1190347 := bstep (se 1 (by rfl) ⟨892760, by rfl⟩ : syracuseStep 1190347 = 1785521) B1785521
theorem B1190359 : Blo 1188411 1190359 := bstep (se 1 (by rfl) ⟨892769, by rfl⟩ : syracuseStep 1190359 = 1785539) B1785539
theorem B10291673 : Blo 1188411 10291673 := bstep (se 2 (by rfl) ⟨3859377, by rfl⟩ : syracuseStep 10291673 = 7718755) B7718755
theorem B1190379 : Blo 1188411 1190379 := bstep (se 1 (by rfl) ⟨892784, by rfl⟩ : syracuseStep 1190379 = 1785569) B1785569
theorem B1190391 : Blo 1188411 1190391 := bstep (se 1 (by rfl) ⟨892793, by rfl⟩ : syracuseStep 1190391 = 1785587) B1785587
theorem B1190411 : Blo 1188411 1190411 := bstep (se 1 (by rfl) ⟨892808, by rfl⟩ : syracuseStep 1190411 = 1785617) B1785617
theorem B1337899 : Blo 1188411 1337899 := bstep (se 1 (by rfl) ⟨1003424, by rfl⟩ : syracuseStep 1337899 = 2006849) B2006849
theorem B3009089 : Blo 1188411 3009089 := bstep (se 2 (by rfl) ⟨1128408, by rfl⟩ : syracuseStep 3009089 = 2256817) B2256817
theorem B3385921 : Blo 1188411 3385921 := bstep (se 2 (by rfl) ⟨1269720, by rfl⟩ : syracuseStep 3385921 = 2539441) B2539441
theorem B1338007 : Blo 1188411 1338007 := bstep (se 1 (by rfl) ⟨1003505, by rfl⟩ : syracuseStep 1338007 = 2007011) B2007011
theorem B4016843 : Blo 1188411 4016843 := bstep (se 1 (by rfl) ⟨3012632, by rfl⟩ : syracuseStep 4016843 = 6025265) B6025265
theorem B2542337 : Blo 1188411 2542337 := bstep (se 2 (by rfl) ⟨953376, by rfl⟩ : syracuseStep 2542337 = 1906753) B1906753
theorem B9038627 : Blo 1188411 9038627 := bstep (se 1 (by rfl) ⟨6778970, by rfl⟩ : syracuseStep 9038627 = 13557941) B13557941
theorem B3812147 : Blo 1188411 3812147 := bstep (se 1 (by rfl) ⟨2859110, by rfl⟩ : syracuseStep 3812147 = 5718221) B5718221
theorem B1338187 : Blo 1188411 1338187 := bstep (se 1 (by rfl) ⟨1003640, by rfl⟩ : syracuseStep 1338187 = 2007281) B2007281
theorem B11422565 : Blo 1188411 11422565 := bstep (se 4 (by rfl) ⟨1070865, by rfl⟩ : syracuseStep 11422565 = 2141731) B2141731
theorem B5499827 : Blo 1188411 5499827 := bstep (se 1 (by rfl) ⟨4124870, by rfl⟩ : syracuseStep 5499827 = 8249741) B8249741
theorem B3812275 : Blo 1188411 3812275 := bstep (se 1 (by rfl) ⟨2859206, by rfl⟩ : syracuseStep 3812275 = 5718413) B5718413
theorem B1338295 : Blo 1188411 1338295 := bstep (se 1 (by rfl) ⟨1003721, by rfl⟩ : syracuseStep 1338295 = 2007443) B2007443
theorem B4017113 : Blo 1188411 4017113 := bstep (se 2 (by rfl) ⟨1506417, by rfl⟩ : syracuseStep 4017113 = 3012835) B3012835
theorem B4287511 : Blo 1188411 4287511 := bstep (se 1 (by rfl) ⟨3215633, by rfl⟩ : syracuseStep 4287511 = 6431267) B6431267
theorem B1526807 : Blo 1188411 1526807 := bstep (se 1 (by rfl) ⟨1145105, by rfl⟩ : syracuseStep 1526807 = 2290211) B2290211
theorem B1338475 : Blo 1188411 1338475 := bstep (se 1 (by rfl) ⟨1003856, by rfl⟩ : syracuseStep 1338475 = 2007713) B2007713
theorem B6425731 : Blo 1188411 6425731 := bstep (se 1 (by rfl) ⟨4819298, by rfl⟩ : syracuseStep 6425731 = 9638597) B9638597
theorem B9784451 : Blo 1188411 9784451 := bstep (se 1 (by rfl) ⟨7338338, by rfl⟩ : syracuseStep 9784451 = 14676677) B14676677
theorem B2174131 : Blo 1188411 2174131 := bstep (se 1 (by rfl) ⟨1630598, by rfl⟩ : syracuseStep 2174131 = 3261197) B3261197
theorem B1338583 : Blo 1188411 1338583 := bstep (se 1 (by rfl) ⟨1003937, by rfl⟩ : syracuseStep 1338583 = 2007875) B2007875
theorem B3615961 : Blo 1188411 3615961 := bstep (se 2 (by rfl) ⟨1355985, by rfl⟩ : syracuseStep 3615961 = 2711971) B2711971
theorem B2673971 : Blo 1188411 2673971 := bstep (se 1 (by rfl) ⟨2005478, by rfl⟩ : syracuseStep 2673971 = 4010957) B4010957
theorem B2674007 : Blo 1188411 2674007 := bstep (se 1 (by rfl) ⟨2005505, by rfl⟩ : syracuseStep 2674007 = 4011011) B4011011
theorem B1338763 : Blo 1188411 1338763 := bstep (se 1 (by rfl) ⟨1004072, by rfl⟩ : syracuseStep 1338763 = 2008145) B2008145
theorem B1904023 : Blo 1188411 1904023 := bstep (se 1 (by rfl) ⟨1428017, by rfl⟩ : syracuseStep 1904023 = 2856035) B2856035
theorem B4287917 : Blo 1188411 4287917 := bstep (se 3 (by rfl) ⟨803984, by rfl⟩ : syracuseStep 4287917 = 1607969) B1607969
theorem B2256331 : Blo 1188411 2256331 := bstep (se 1 (by rfl) ⟨1692248, by rfl⟩ : syracuseStep 2256331 = 3384497) B3384497
theorem B10153421 : Blo 1188411 10153421 := bstep (se 3 (by rfl) ⟨1903766, by rfl⟩ : syracuseStep 10153421 = 3807533) B3807533
theorem B4574681 : Blo 1188411 4574681 := bstep (se 2 (by rfl) ⟨1715505, by rfl⟩ : syracuseStep 4574681 = 3431011) B3431011
theorem B1338871 : Blo 1188411 1338871 := bstep (se 1 (by rfl) ⟨1004153, by rfl⟩ : syracuseStep 1338871 = 2008307) B2008307
theorem B2674187 : Blo 1188411 2674187 := bstep (se 1 (by rfl) ⟨2005640, by rfl⟩ : syracuseStep 2674187 = 4011281) B4011281
theorem B2256407 : Blo 1188411 2256407 := bstep (se 1 (by rfl) ⟨1692305, by rfl⟩ : syracuseStep 2256407 = 3384611) B3384611
theorem B2674241 : Blo 1188411 2674241 := bstep (se 2 (by rfl) ⟨1002840, by rfl⟩ : syracuseStep 2674241 = 2005681) B2005681
theorem B6024779 : Blo 1188411 6024779 := bstep (se 1 (by rfl) ⟨4518584, by rfl⟩ : syracuseStep 6024779 = 9037169) B9037169
theorem B1339051 : Blo 1188411 1339051 := bstep (se 1 (by rfl) ⟨1004288, by rfl⟩ : syracuseStep 1339051 = 2008577) B2008577
theorem B1339159 : Blo 1188411 1339159 := bstep (se 1 (by rfl) ⟨1004369, by rfl⟩ : syracuseStep 1339159 = 2008739) B2008739
theorem B2674457 : Blo 1188411 2674457 := bstep (se 2 (by rfl) ⟨1002921, by rfl⟩ : syracuseStep 2674457 = 2005843) B2005843
theorem B3010355 : Blo 1188411 3010355 := bstep (se 1 (by rfl) ⟨2257766, by rfl⟩ : syracuseStep 3010355 = 4515533) B4515533
theorem B2674547 : Blo 1188411 2674547 := bstep (se 1 (by rfl) ⟨2005910, by rfl⟩ : syracuseStep 2674547 = 4011821) B4011821
theorem B2674583 : Blo 1188411 2674583 := bstep (se 1 (by rfl) ⟨2005937, by rfl⟩ : syracuseStep 2674583 = 4011875) B4011875
theorem B12857305 : Blo 1188411 12857305 := bstep (se 2 (by rfl) ⟨4821489, by rfl⟩ : syracuseStep 12857305 = 9642979) B9642979
theorem B2412569 : Blo 1188411 2412569 := bstep (se 2 (by rfl) ⟨904713, by rfl⟩ : syracuseStep 2412569 = 1809427) B1809427
theorem B2674763 : Blo 1188411 2674763 := bstep (se 1 (by rfl) ⟨2006072, by rfl⟩ : syracuseStep 2674763 = 4012145) B4012145
theorem B4517963 : Blo 1188411 4517963 := bstep (se 1 (by rfl) ⟨3388472, by rfl⟩ : syracuseStep 4517963 = 6776945) B6776945
theorem B4517977 : Blo 1188411 4517977 := bstep (se 2 (by rfl) ⟨1694241, by rfl⟩ : syracuseStep 4517977 = 3388483) B3388483
theorem B7336037 : Blo 1188411 7336037 := bstep (se 4 (by rfl) ⟨687753, by rfl⟩ : syracuseStep 7336037 = 1375507) B1375507
theorem B2674817 : Blo 1188411 2674817 := bstep (se 2 (by rfl) ⟨1003056, by rfl⟩ : syracuseStep 2674817 = 2006113) B2006113
theorem B2257075 : Blo 1188411 2257075 := bstep (se 1 (by rfl) ⟨1692806, by rfl⟩ : syracuseStep 2257075 = 3385613) B3385613
theorem B1904843 : Blo 1188411 1904843 := bstep (se 1 (by rfl) ⟨1428632, by rfl⟩ : syracuseStep 1904843 = 2857265) B2857265
theorem B3387595 : Blo 1188411 3387595 := bstep (se 1 (by rfl) ⟨2540696, by rfl⟩ : syracuseStep 3387595 = 5081393) B5081393
theorem B6779153 : Blo 1188411 6779153 := bstep (se 2 (by rfl) ⟨2542182, by rfl⟩ : syracuseStep 6779153 = 5084365) B5084365
theorem B5714221 : Blo 1188411 5714221 := bstep (se 3 (by rfl) ⟨1071416, by rfl⟩ : syracuseStep 5714221 = 2142833) B2142833
theorem B2142539 : Blo 1188411 2142539 := bstep (se 1 (by rfl) ⟨1606904, by rfl⟩ : syracuseStep 2142539 = 3213809) B3213809
theorem B3010891 : Blo 1188411 3010891 := bstep (se 1 (by rfl) ⟨2258168, by rfl⟩ : syracuseStep 3010891 = 4516337) B4516337
theorem B2675033 : Blo 1188411 2675033 := bstep (se 2 (by rfl) ⟨1003137, by rfl⟩ : syracuseStep 2675033 = 2006275) B2006275
theorem B2257303 : Blo 1188411 2257303 := bstep (se 1 (by rfl) ⟨1692977, by rfl⟩ : syracuseStep 2257303 = 3385955) B3385955
theorem B2675123 : Blo 1188411 2675123 := bstep (se 1 (by rfl) ⟨2006342, by rfl⟩ : syracuseStep 2675123 = 4012685) B4012685
theorem B2675159 : Blo 1188411 2675159 := bstep (se 1 (by rfl) ⟨2006369, by rfl⟩ : syracuseStep 2675159 = 4012739) B4012739
theorem B1905113 : Blo 1188411 1905113 := bstep (se 2 (by rfl) ⟨714417, by rfl⟩ : syracuseStep 1905113 = 1428835) B1428835
theorem B3011033 : Blo 1188411 3011033 := bstep (se 2 (by rfl) ⟨1129137, by rfl⟩ : syracuseStep 3011033 = 2258275) B2258275
theorem B3387869 : Blo 1188411 3387869 := bstep (se 3 (by rfl) ⟨635225, by rfl⟩ : syracuseStep 3387869 = 1270451) B1270451
theorem B2257409 : Blo 1188411 2257409 := bstep (se 2 (by rfl) ⟨846528, by rfl⟩ : syracuseStep 2257409 = 1693057) B1693057
theorem B4289041 : Blo 1188411 4289041 := bstep (se 2 (by rfl) ⟨1608390, by rfl⟩ : syracuseStep 4289041 = 3216781) B3216781
theorem B2413081 : Blo 1188411 2413081 := bstep (se 2 (by rfl) ⟨904905, by rfl⟩ : syracuseStep 2413081 = 1809811) B1809811
theorem B2675339 : Blo 1188411 2675339 := bstep (se 1 (by rfl) ⟨2006504, by rfl⟩ : syracuseStep 2675339 = 4013009) B4013009
theorem B2257561 : Blo 1188411 2257561 := bstep (se 2 (by rfl) ⟨846585, by rfl⟩ : syracuseStep 2257561 = 1693171) B1693171
theorem B2675393 : Blo 1188411 2675393 := bstep (se 2 (by rfl) ⟨1003272, by rfl⟩ : syracuseStep 2675393 = 2006545) B2006545
theorem B6779609 : Blo 1188411 6779609 := bstep (se 2 (by rfl) ⟨2542353, by rfl⟩ : syracuseStep 6779609 = 5084707) B5084707
theorem B5083955 : Blo 1188411 5083955 := bstep (se 1 (by rfl) ⟨3812966, by rfl⟩ : syracuseStep 5083955 = 7625933) B7625933
theorem B4289345 : Blo 1188411 4289345 := bstep (se 2 (by rfl) ⟨1608504, by rfl⟩ : syracuseStep 4289345 = 3217009) B3217009
theorem B1782617 : Blo 1188411 1782617 := bstep (se 2 (by rfl) ⟨668481, by rfl⟩ : syracuseStep 1782617 = 1336963) B1336963
theorem B1692505 : Blo 1188411 1692505 := bstep (se 2 (by rfl) ⟨634689, by rfl⟩ : syracuseStep 1692505 = 1269379) B1269379
theorem B4010903 : Blo 1188411 4010903 := bstep (se 1 (by rfl) ⟨3008177, by rfl⟩ : syracuseStep 4010903 = 6016355) B6016355
theorem B2675609 : Blo 1188411 2675609 := bstep (se 2 (by rfl) ⟨1003353, by rfl⟩ : syracuseStep 2675609 = 2006707) B2006707
theorem B2855873 : Blo 1188411 2855873 := bstep (se 2 (by rfl) ⟨1070952, by rfl⟩ : syracuseStep 2855873 = 2141905) B2141905
theorem B1782731 : Blo 1188411 1782731 := bstep (se 1 (by rfl) ⟨1337048, by rfl⟩ : syracuseStep 1782731 = 2674097) B2674097
theorem B1782743 : Blo 1188411 1782743 := bstep (se 1 (by rfl) ⟨1337057, by rfl⟩ : syracuseStep 1782743 = 2674115) B2674115
theorem B2675699 : Blo 1188411 2675699 := bstep (se 1 (by rfl) ⟨2006774, by rfl⟩ : syracuseStep 2675699 = 4013549) B4013549
theorem B2675735 : Blo 1188411 2675735 := bstep (se 1 (by rfl) ⟨2006801, by rfl⟩ : syracuseStep 2675735 = 4013603) B4013603
theorem B4518935 : Blo 1188411 4518935 := bstep (se 1 (by rfl) ⟨3389201, by rfl⟩ : syracuseStep 4518935 = 6778403) B6778403
theorem B1782809 : Blo 1188411 1782809 := bstep (se 2 (by rfl) ⟨668553, by rfl⟩ : syracuseStep 1782809 = 1337107) B1337107
theorem B41759813 : Blo 1188411 41759813 := bstep (se 4 (by rfl) ⟨3914982, by rfl⟩ : syracuseStep 41759813 = 7829965) B7829965
theorem B1782923 : Blo 1188411 1782923 := bstep (se 1 (by rfl) ⟨1337192, by rfl⟩ : syracuseStep 1782923 = 2674385) B2674385
theorem B2200727 : Blo 1188411 2200727 := bstep (se 1 (by rfl) ⟨1650545, by rfl⟩ : syracuseStep 2200727 = 3301091) B3301091
theorem B1782935 : Blo 1188411 1782935 := bstep (se 1 (by rfl) ⟨1337201, by rfl⟩ : syracuseStep 1782935 = 2674403) B2674403
theorem B6771863 : Blo 1188411 6771863 := bstep (se 1 (by rfl) ⟨5078897, by rfl⟩ : syracuseStep 6771863 = 10157795) B10157795
theorem B1905817 : Blo 1188411 1905817 := bstep (se 2 (by rfl) ⟨714681, by rfl⟩ : syracuseStep 1905817 = 1429363) B1429363
theorem B1356971 : Blo 1188411 1356971 := bstep (se 1 (by rfl) ⟨1017728, by rfl⟩ : syracuseStep 1356971 = 2035457) B2035457
theorem B10294451 : Blo 1188411 10294451 := bstep (se 1 (by rfl) ⟨7720838, by rfl⟩ : syracuseStep 10294451 = 15441677) B15441677
theorem B2675915 : Blo 1188411 2675915 := bstep (se 1 (by rfl) ⟨2006936, by rfl⟩ : syracuseStep 2675915 = 4013873) B4013873
theorem B1783001 : Blo 1188411 1783001 := bstep (se 2 (by rfl) ⟨668625, by rfl⟩ : syracuseStep 1783001 = 1337251) B1337251
theorem B2675969 : Blo 1188411 2675969 := bstep (se 2 (by rfl) ⟨1003488, by rfl⟩ : syracuseStep 2675969 = 2006977) B2006977
theorem B3011863 : Blo 1188411 3011863 := bstep (se 1 (by rfl) ⟨2258897, by rfl⟩ : syracuseStep 3011863 = 4517795) B4517795
theorem B1783115 : Blo 1188411 1783115 := bstep (se 1 (by rfl) ⟨1337336, by rfl⟩ : syracuseStep 1783115 = 2674673) B2674673
theorem B1783127 : Blo 1188411 1783127 := bstep (se 1 (by rfl) ⟨1337345, by rfl⟩ : syracuseStep 1783127 = 2674691) B2674691
theorem B2143577 : Blo 1188411 2143577 := bstep (se 2 (by rfl) ⟨803841, by rfl⟩ : syracuseStep 2143577 = 1607683) B1607683
theorem B1504651 : Blo 1188411 1504651 := bstep (se 1 (by rfl) ⟨1128488, by rfl⟩ : syracuseStep 1504651 = 2256977) B2256977
theorem B1783193 : Blo 1188411 1783193 := bstep (se 2 (by rfl) ⟨668697, by rfl⟩ : syracuseStep 1783193 = 1337395) B1337395
theorem B4011443 : Blo 1188411 4011443 := bstep (se 1 (by rfl) ⟨3008582, by rfl⟩ : syracuseStep 4011443 = 6017165) B6017165
theorem B2676185 : Blo 1188411 2676185 := bstep (se 2 (by rfl) ⟨1003569, by rfl⟩ : syracuseStep 2676185 = 2007139) B2007139
theorem B1783307 : Blo 1188411 1783307 := bstep (se 1 (by rfl) ⟨1337480, by rfl⟩ : syracuseStep 1783307 = 2674961) B2674961
theorem B28915217 : Blo 1188411 28915217 := bstep (se 2 (by rfl) ⟨10843206, by rfl⟩ : syracuseStep 28915217 = 21686413) B21686413
theorem B1783319 : Blo 1188411 1783319 := bstep (se 1 (by rfl) ⟨1337489, by rfl⟩ : syracuseStep 1783319 = 2674979) B2674979
theorem B2676275 : Blo 1188411 2676275 := bstep (se 1 (by rfl) ⟨2007206, by rfl⟩ : syracuseStep 2676275 = 4014413) B4014413
theorem B9033281 : Blo 1188411 9033281 := bstep (se 2 (by rfl) ⟨3387480, by rfl⟩ : syracuseStep 9033281 = 6774961) B6774961
theorem B2676311 : Blo 1188411 2676311 := bstep (se 1 (by rfl) ⟨2007233, by rfl⟩ : syracuseStep 2676311 = 4014467) B4014467
theorem B1783385 : Blo 1188411 1783385 := bstep (se 2 (by rfl) ⟨668769, by rfl⟩ : syracuseStep 1783385 = 1337539) B1337539
theorem B1808011 : Blo 1188411 1808011 := bstep (se 1 (by rfl) ⟨1356008, by rfl⟩ : syracuseStep 1808011 = 2712017) B2712017
theorem B1504919 : Blo 1188411 1504919 := bstep (se 1 (by rfl) ⟨1128689, by rfl⟩ : syracuseStep 1504919 = 2257379) B2257379
theorem B4011713 : Blo 1188411 4011713 := bstep (se 2 (by rfl) ⟨1504392, by rfl⟩ : syracuseStep 4011713 = 3008785) B3008785
theorem B1783499 : Blo 1188411 1783499 := bstep (se 1 (by rfl) ⟨1337624, by rfl⟩ : syracuseStep 1783499 = 2675249) B2675249
theorem B5150411 : Blo 1188411 5150411 := bstep (se 1 (by rfl) ⟨3862808, by rfl⟩ : syracuseStep 5150411 = 7725617) B7725617
theorem B3012299 : Blo 1188411 3012299 := bstep (se 1 (by rfl) ⟨2259224, by rfl⟩ : syracuseStep 3012299 = 4518449) B4518449
theorem B1783511 : Blo 1188411 1783511 := bstep (se 1 (by rfl) ⟨1337633, by rfl⟩ : syracuseStep 1783511 = 2675267) B2675267
theorem B1693399 : Blo 1188411 1693399 := bstep (se 1 (by rfl) ⟨1270049, by rfl⟩ : syracuseStep 1693399 = 2540099) B2540099
theorem B2676491 : Blo 1188411 2676491 := bstep (se 1 (by rfl) ⟨2007368, by rfl⟩ : syracuseStep 2676491 = 4014737) B4014737
theorem B1783577 : Blo 1188411 1783577 := bstep (se 2 (by rfl) ⟨668841, by rfl⟩ : syracuseStep 1783577 = 1337683) B1337683
theorem B2676545 : Blo 1188411 2676545 := bstep (se 2 (by rfl) ⟨1003704, by rfl⟩ : syracuseStep 2676545 = 2007409) B2007409
theorem B6018947 : Blo 1188411 6018947 := bstep (se 1 (by rfl) ⟨4514210, by rfl⟩ : syracuseStep 6018947 = 9028421) B9028421
theorem B1783691 : Blo 1188411 1783691 := bstep (se 1 (by rfl) ⟨1337768, by rfl⟩ : syracuseStep 1783691 = 2675537) B2675537
theorem B1783703 : Blo 1188411 1783703 := bstep (se 1 (by rfl) ⟨1337777, by rfl⟩ : syracuseStep 1783703 = 2675555) B2675555
theorem B2258867 : Blo 1188411 2258867 := bstep (se 1 (by rfl) ⟨1694150, by rfl⟩ : syracuseStep 2258867 = 3388301) B3388301
theorem B5576651 : Blo 1188411 5576651 := bstep (se 1 (by rfl) ⟨4182488, by rfl⟩ : syracuseStep 5576651 = 8364977) B8364977
theorem B1783769 : Blo 1188411 1783769 := bstep (se 2 (by rfl) ⟨668913, by rfl⟩ : syracuseStep 1783769 = 1337827) B1337827
theorem B2676761 : Blo 1188411 2676761 := bstep (se 2 (by rfl) ⟨1003785, by rfl⟩ : syracuseStep 2676761 = 2007571) B2007571
theorem B3012673 : Blo 1188411 3012673 := bstep (se 2 (by rfl) ⟨1129752, by rfl⟩ : syracuseStep 3012673 = 2259505) B2259505
theorem B1783883 : Blo 1188411 1783883 := bstep (se 1 (by rfl) ⟨1337912, by rfl⟩ : syracuseStep 1783883 = 2675825) B2675825
theorem B2259019 : Blo 1188411 2259019 := bstep (se 1 (by rfl) ⟨1694264, by rfl⟩ : syracuseStep 2259019 = 3388529) B3388529
theorem B1783895 : Blo 1188411 1783895 := bstep (se 1 (by rfl) ⟨1337921, by rfl⟩ : syracuseStep 1783895 = 2675843) B2675843
theorem B2676851 : Blo 1188411 2676851 := bstep (se 1 (by rfl) ⟨2007638, by rfl⟩ : syracuseStep 2676851 = 4015277) B4015277
theorem B2676887 : Blo 1188411 2676887 := bstep (se 1 (by rfl) ⟨2007665, by rfl⟩ : syracuseStep 2676887 = 4015331) B4015331
theorem B1783961 : Blo 1188411 1783961 := bstep (se 2 (by rfl) ⟨668985, by rfl⟩ : syracuseStep 1783961 = 1337971) B1337971
theorem B4012253 : Blo 1188411 4012253 := bstep (se 3 (by rfl) ⟨752297, by rfl⟩ : syracuseStep 4012253 = 1504595) B1504595
theorem B1784075 : Blo 1188411 1784075 := bstep (se 1 (by rfl) ⟨1338056, by rfl⟩ : syracuseStep 1784075 = 2676113) B2676113
theorem B1693963 : Blo 1188411 1693963 := bstep (se 1 (by rfl) ⟨1270472, by rfl⟩ : syracuseStep 1693963 = 2540945) B2540945
theorem B1784087 : Blo 1188411 1784087 := bstep (se 1 (by rfl) ⟨1338065, by rfl⟩ : syracuseStep 1784087 = 2676131) B2676131
theorem B3528983 : Blo 1188411 3528983 := bstep (se 1 (by rfl) ⟨2646737, by rfl⟩ : syracuseStep 3528983 = 5293475) B5293475
theorem B19290433 : Blo 1188411 19290433 := bstep (se 2 (by rfl) ⟨7233912, by rfl⟩ : syracuseStep 19290433 = 14467825) B14467825
theorem B2677067 : Blo 1188411 2677067 := bstep (se 1 (by rfl) ⟨2007800, by rfl⟩ : syracuseStep 2677067 = 4015601) B4015601
theorem B1505623 : Blo 1188411 1505623 := bstep (se 1 (by rfl) ⟨1129217, by rfl⟩ : syracuseStep 1505623 = 2258435) B2258435
theorem B1784153 : Blo 1188411 1784153 := bstep (se 2 (by rfl) ⟨669057, by rfl⟩ : syracuseStep 1784153 = 1338115) B1338115
theorem B2677121 : Blo 1188411 2677121 := bstep (se 2 (by rfl) ⟨1003920, by rfl⟩ : syracuseStep 2677121 = 2007841) B2007841
theorem B2259353 : Blo 1188411 2259353 := bstep (se 2 (by rfl) ⟨847257, by rfl⟩ : syracuseStep 2259353 = 1694515) B1694515
theorem B1784267 : Blo 1188411 1784267 := bstep (se 1 (by rfl) ⟨1338200, by rfl⟩ : syracuseStep 1784267 = 2676401) B2676401
theorem B1784279 : Blo 1188411 1784279 := bstep (se 1 (by rfl) ⟨1338209, by rfl⟩ : syracuseStep 1784279 = 2676419) B2676419
theorem B2005465 : Blo 1188411 2005465 := bstep (se 2 (by rfl) ⟨752049, by rfl⟩ : syracuseStep 2005465 = 1504099) B1504099
theorem B1784345 : Blo 1188411 1784345 := bstep (se 2 (by rfl) ⟨669129, by rfl⟩ : syracuseStep 1784345 = 1338259) B1338259
theorem B2677337 : Blo 1188411 2677337 := bstep (se 2 (by rfl) ⟨1004001, by rfl⟩ : syracuseStep 2677337 = 2008003) B2008003
theorem B1784459 : Blo 1188411 1784459 := bstep (se 1 (by rfl) ⟨1338344, by rfl⟩ : syracuseStep 1784459 = 2676689) B2676689
theorem B1784471 : Blo 1188411 1784471 := bstep (se 1 (by rfl) ⟨1338353, by rfl⟩ : syracuseStep 1784471 = 2676707) B2676707
theorem B2677427 : Blo 1188411 2677427 := bstep (se 1 (by rfl) ⟨2008070, by rfl⟩ : syracuseStep 2677427 = 4016141) B4016141
theorem B4512449 : Blo 1188411 4512449 := bstep (se 2 (by rfl) ⟨1692168, by rfl⟩ : syracuseStep 4512449 = 3384337) B3384337
theorem B1448651 : Blo 1188411 1448651 := bstep (se 1 (by rfl) ⟨1086488, by rfl⟩ : syracuseStep 1448651 = 2172977) B2172977
theorem B2677463 : Blo 1188411 2677463 := bstep (se 1 (by rfl) ⟨2008097, by rfl⟩ : syracuseStep 2677463 = 4016195) B4016195
theorem B1784537 : Blo 1188411 1784537 := bstep (se 2 (by rfl) ⟨669201, by rfl⟩ : syracuseStep 1784537 = 1338403) B1338403
theorem B1784651 : Blo 1188411 1784651 := bstep (se 1 (by rfl) ⟨1338488, by rfl⟩ : syracuseStep 1784651 = 2676977) B2676977
theorem B1784663 : Blo 1188411 1784663 := bstep (se 1 (by rfl) ⟨1338497, by rfl⟩ : syracuseStep 1784663 = 2676995) B2676995
theorem B2677643 : Blo 1188411 2677643 := bstep (se 1 (by rfl) ⟨2008232, by rfl⟩ : syracuseStep 2677643 = 4016465) B4016465
theorem B1784729 : Blo 1188411 1784729 := bstep (se 2 (by rfl) ⟨669273, by rfl⟩ : syracuseStep 1784729 = 1338547) B1338547
theorem B2677697 : Blo 1188411 2677697 := bstep (se 2 (by rfl) ⟨1004136, by rfl⟩ : syracuseStep 2677697 = 2008273) B2008273
theorem B66853849 : Blo 1188411 66853849 := bstep (se 2 (by rfl) ⟨25070193, by rfl⟩ : syracuseStep 66853849 = 50140387) B50140387
theorem B2644993 : Blo 1188411 2644993 := bstep (se 2 (by rfl) ⟨991872, by rfl⟩ : syracuseStep 2644993 = 1983745) B1983745
theorem B1784843 : Blo 1188411 1784843 := bstep (se 1 (by rfl) ⟨1338632, by rfl⟩ : syracuseStep 1784843 = 2677265) B2677265
theorem B6773777 : Blo 1188411 6773777 := bstep (se 2 (by rfl) ⟨2540166, by rfl⟩ : syracuseStep 6773777 = 5080333) B5080333
theorem B2006039 : Blo 1188411 2006039 := bstep (se 1 (by rfl) ⟨1504529, by rfl⟩ : syracuseStep 2006039 = 3009059) B3009059
theorem B1784855 : Blo 1188411 1784855 := bstep (se 1 (by rfl) ⟨1338641, by rfl⟩ : syracuseStep 1784855 = 2677283) B2677283
theorem B1784921 : Blo 1188411 1784921 := bstep (se 2 (by rfl) ⟨669345, by rfl⟩ : syracuseStep 1784921 = 1338691) B1338691
theorem B13540445 : Blo 1188411 13540445 := bstep (se 3 (by rfl) ⟨2538833, by rfl⟩ : syracuseStep 13540445 = 5077667) B5077667
theorem B3431575 : Blo 1188411 3431575 := bstep (se 1 (by rfl) ⟨2573681, by rfl⟩ : syracuseStep 3431575 = 5147363) B5147363
theorem B2006167 : Blo 1188411 2006167 := bstep (se 1 (by rfl) ⟨1504625, by rfl⟩ : syracuseStep 2006167 = 3009251) B3009251
theorem B8928407 : Blo 1188411 8928407 := bstep (se 1 (by rfl) ⟨6696305, by rfl⟩ : syracuseStep 8928407 = 13392611) B13392611
theorem B2677913 : Blo 1188411 2677913 := bstep (se 2 (by rfl) ⟨1004217, by rfl⟩ : syracuseStep 2677913 = 2008435) B2008435
theorem B1785035 : Blo 1188411 1785035 := bstep (se 1 (by rfl) ⟨1338776, by rfl⟩ : syracuseStep 1785035 = 2677553) B2677553
theorem B1785047 : Blo 1188411 1785047 := bstep (se 1 (by rfl) ⟨1338785, by rfl⟩ : syracuseStep 1785047 = 2677571) B2677571
theorem B5790937 : Blo 1188411 5790937 := bstep (se 2 (by rfl) ⟨2171601, by rfl⟩ : syracuseStep 5790937 = 4343203) B4343203
theorem B2678003 : Blo 1188411 2678003 := bstep (se 1 (by rfl) ⟨2008502, by rfl⟩ : syracuseStep 2678003 = 4017005) B4017005
theorem B2678039 : Blo 1188411 2678039 := bstep (se 1 (by rfl) ⟨2008529, by rfl⟩ : syracuseStep 2678039 = 4017059) B4017059
theorem B1785113 : Blo 1188411 1785113 := bstep (se 2 (by rfl) ⟨669417, by rfl⟩ : syracuseStep 1785113 = 1338835) B1338835
theorem B4013387 : Blo 1188411 4013387 := bstep (se 1 (by rfl) ⟨3010040, by rfl⟩ : syracuseStep 4013387 = 6020081) B6020081
theorem B4513117 : Blo 1188411 4513117 := bstep (se 3 (by rfl) ⟨846209, by rfl⟩ : syracuseStep 4513117 = 1692419) B1692419
theorem B1785227 : Blo 1188411 1785227 := bstep (se 1 (by rfl) ⟨1338920, by rfl⟩ : syracuseStep 1785227 = 2677841) B2677841
theorem B1785239 : Blo 1188411 1785239 := bstep (se 1 (by rfl) ⟨1338929, by rfl⟩ : syracuseStep 1785239 = 2677859) B2677859
theorem B2678219 : Blo 1188411 2678219 := bstep (se 1 (by rfl) ⟨2008664, by rfl⟩ : syracuseStep 2678219 = 4017329) B4017329
theorem B65158613 : Blo 1188411 65158613 := bstep (se 7 (by rfl) ⟨763577, by rfl⟩ : syracuseStep 65158613 = 1527155) B1527155
theorem B9035225 : Blo 1188411 9035225 := bstep (se 2 (by rfl) ⟨3388209, by rfl⟩ : syracuseStep 9035225 = 6776419) B6776419
theorem B1785305 : Blo 1188411 1785305 := bstep (se 2 (by rfl) ⟨669489, by rfl⟩ : syracuseStep 1785305 = 1338979) B1338979
theorem B2678273 : Blo 1188411 2678273 := bstep (se 2 (by rfl) ⟨1004352, by rfl⟩ : syracuseStep 2678273 = 2008705) B2008705
theorem B2539073 : Blo 1188411 2539073 := bstep (se 2 (by rfl) ⟨952152, by rfl⟩ : syracuseStep 2539073 = 1904305) B1904305
theorem B5791297 : Blo 1188411 5791297 := bstep (se 2 (by rfl) ⟨2171736, by rfl⟩ : syracuseStep 5791297 = 4343473) B4343473
theorem B1785419 : Blo 1188411 1785419 := bstep (se 1 (by rfl) ⟨1339064, by rfl⟩ : syracuseStep 1785419 = 2678129) B2678129
theorem B1785431 : Blo 1188411 1785431 := bstep (se 1 (by rfl) ⟨1339073, by rfl⟩ : syracuseStep 1785431 = 2678147) B2678147
theorem B4013657 : Blo 1188411 4013657 := bstep (se 2 (by rfl) ⟨1505121, by rfl⟩ : syracuseStep 4013657 = 3010243) B3010243
theorem B7618141 : Blo 1188411 7618141 := bstep (se 3 (by rfl) ⟨1428401, by rfl⟩ : syracuseStep 7618141 = 2856803) B2856803
theorem B5078659 : Blo 1188411 5078659 := bstep (se 1 (by rfl) ⟨3808994, by rfl⟩ : syracuseStep 5078659 = 7617989) B7617989
theorem B1785497 : Blo 1188411 1785497 := bstep (se 2 (by rfl) ⟨669561, by rfl⟩ : syracuseStep 1785497 = 1339123) B1339123
theorem B4284083 : Blo 1188411 4284083 := bstep (se 1 (by rfl) ⟨3213062, by rfl⟩ : syracuseStep 4284083 = 6426125) B6426125
theorem B1269451 : Blo 1188411 1269451 := bstep (se 1 (by rfl) ⟨952088, by rfl⟩ : syracuseStep 1269451 = 1904177) B1904177
theorem B2006795 : Blo 1188411 2006795 := bstep (se 1 (by rfl) ⟨1505096, by rfl⟩ : syracuseStep 2006795 = 3010193) B3010193
theorem B1785611 : Blo 1188411 1785611 := bstep (se 1 (by rfl) ⟨1339208, by rfl⟩ : syracuseStep 1785611 = 2678417) B2678417
theorem B2006923 : Blo 1188411 2006923 := bstep (se 1 (by rfl) ⟨1505192, by rfl⟩ : syracuseStep 2006923 = 3010385) B3010385
theorem B65118131 : Blo 1188411 65118131 := bstep (se 1 (by rfl) ⟨48838598, by rfl⟩ : syracuseStep 65118131 = 97677197) B97677197
theorem B2711513 : Blo 1188411 2711513 := bstep (se 2 (by rfl) ⟨1016817, by rfl⟩ : syracuseStep 2711513 = 2033635) B2033635
theorem B14106629 : Blo 1188411 14106629 := bstep (se 4 (by rfl) ⟨1322496, by rfl⟩ : syracuseStep 14106629 = 2644993) B2644993
theorem B4071485 : Blo 1188411 4071485 := bstep (se 3 (by rfl) ⟨763403, by rfl⟩ : syracuseStep 4071485 = 1526807) B1526807
theorem B4890691 : Blo 1188411 4890691 := bstep (se 1 (by rfl) ⟨3668018, by rfl⟩ : syracuseStep 4890691 = 7336037) B7336037
theorem B12869765 : Blo 1188411 12869765 := bstep (se 4 (by rfl) ⟨1206540, by rfl⟩ : syracuseStep 12869765 = 2413081) B2413081
theorem B6021377 : Blo 1188411 6021377 := bstep (se 2 (by rfl) ⟨2258016, by rfl⟩ : syracuseStep 6021377 = 4516033) B4516033
theorem B1270075 : Blo 1188411 1270075 := bstep (se 1 (by rfl) ⟨952556, by rfl⟩ : syracuseStep 1270075 = 1905113) B1905113
theorem B2007355 : Blo 1188411 2007355 := bstep (se 1 (by rfl) ⟨1505516, by rfl⟩ : syracuseStep 2007355 = 3011033) B3011033
theorem B7618961 : Blo 1188411 7618961 := bstep (se 2 (by rfl) ⟨2857110, by rfl⟩ : syracuseStep 7618961 = 5714221) B5714221
theorem B4014521 : Blo 1188411 4014521 := bstep (se 2 (by rfl) ⟨1505445, by rfl⟩ : syracuseStep 4014521 = 3010891) B3010891
theorem B2007497 : Blo 1188411 2007497 := bstep (se 2 (by rfl) ⟨752811, by rfl⟩ : syracuseStep 2007497 = 1505623) B1505623
theorem B5079581 : Blo 1188411 5079581 := bstep (se 3 (by rfl) ⟨952421, by rfl⟩ : syracuseStep 5079581 = 1904843) B1904843
theorem B2859563 : Blo 1188411 2859563 := bstep (se 1 (by rfl) ⟨2144672, by rfl⟩ : syracuseStep 2859563 = 4289345) B4289345
theorem B1188411 : Blo 1188411 1188411 := bstep (se 1 (by rfl) ⟨891308, by rfl⟩ : syracuseStep 1188411 = 1782617) B1782617
theorem B1188487 : Blo 1188411 1188487 := bstep (se 1 (by rfl) ⟨891365, by rfl⟩ : syracuseStep 1188487 = 1782731) B1782731
theorem B1188495 : Blo 1188411 1188495 := bstep (se 1 (by rfl) ⟨891371, by rfl⟩ : syracuseStep 1188495 = 1782743) B1782743
theorem B1188539 : Blo 1188411 1188539 := bstep (se 1 (by rfl) ⟨891404, by rfl⟩ : syracuseStep 1188539 = 1782809) B1782809
theorem B5718721 : Blo 1188411 5718721 := bstep (se 2 (by rfl) ⟨2144520, by rfl⟩ : syracuseStep 5718721 = 4289041) B4289041
theorem B9642725 : Blo 1188411 9642725 := bstep (se 4 (by rfl) ⟨904005, by rfl⟩ : syracuseStep 9642725 = 1808011) B1808011
theorem B4514561 : Blo 1188411 4514561 := bstep (se 2 (by rfl) ⟨1692960, by rfl⟩ : syracuseStep 4514561 = 3385921) B3385921
theorem B1188615 : Blo 1188411 1188615 := bstep (se 1 (by rfl) ⟨891461, by rfl⟩ : syracuseStep 1188615 = 1782923) B1782923
theorem B1188623 : Blo 1188411 1188623 := bstep (se 1 (by rfl) ⟨891467, by rfl⟩ : syracuseStep 1188623 = 1782935) B1782935
theorem B4514575 : Blo 1188411 4514575 := bstep (se 1 (by rfl) ⟨3385931, by rfl⟩ : syracuseStep 4514575 = 6771863) B6771863
theorem B18301733 : Blo 1188411 18301733 := bstep (se 4 (by rfl) ⟨1715787, by rfl⟩ : syracuseStep 18301733 = 3431575) B3431575
theorem B1188667 : Blo 1188411 1188667 := bstep (se 1 (by rfl) ⟨891500, by rfl⟩ : syracuseStep 1188667 = 1783001) B1783001
theorem B1188743 : Blo 1188411 1188743 := bstep (se 1 (by rfl) ⟨891557, by rfl⟩ : syracuseStep 1188743 = 1783115) B1783115
theorem B2540423 : Blo 1188411 2540423 := bstep (se 1 (by rfl) ⟨1905317, by rfl⟩ : syracuseStep 2540423 = 3810635) B3810635
theorem B1188751 : Blo 1188411 1188751 := bstep (se 1 (by rfl) ⟨891563, by rfl⟩ : syracuseStep 1188751 = 1783127) B1783127
theorem B1188795 : Blo 1188411 1188795 := bstep (se 1 (by rfl) ⟨891596, by rfl⟩ : syracuseStep 1188795 = 1783193) B1783193
theorem B1188871 : Blo 1188411 1188871 := bstep (se 1 (by rfl) ⟨891653, by rfl⟩ : syracuseStep 1188871 = 1783307) B1783307
theorem B19276811 : Blo 1188411 19276811 := bstep (se 1 (by rfl) ⟨14457608, by rfl⟩ : syracuseStep 19276811 = 28915217) B28915217
theorem B4015115 : Blo 1188411 4015115 := bstep (se 1 (by rfl) ⟨3011336, by rfl⟩ : syracuseStep 4015115 = 6022673) B6022673
theorem B1188879 : Blo 1188411 1188879 := bstep (se 1 (by rfl) ⟨891659, by rfl⟩ : syracuseStep 1188879 = 1783319) B1783319
theorem B6022187 : Blo 1188411 6022187 := bstep (se 1 (by rfl) ⟨4516640, by rfl⟩ : syracuseStep 6022187 = 9033281) B9033281
theorem B1188923 : Blo 1188411 1188923 := bstep (se 1 (by rfl) ⟨891692, by rfl⟩ : syracuseStep 1188923 = 1783385) B1783385
theorem B4015223 : Blo 1188411 4015223 := bstep (se 1 (by rfl) ⟨3011417, by rfl⟩ : syracuseStep 4015223 = 6022835) B6022835
theorem B1188999 : Blo 1188411 1188999 := bstep (se 1 (by rfl) ⟨891749, by rfl⟩ : syracuseStep 1188999 = 1783499) B1783499
theorem B3433607 : Blo 1188411 3433607 := bstep (se 1 (by rfl) ⟨2575205, by rfl⟩ : syracuseStep 3433607 = 5150411) B5150411
theorem B2008199 : Blo 1188411 2008199 := bstep (se 1 (by rfl) ⟨1506149, by rfl⟩ : syracuseStep 2008199 = 3012299) B3012299
theorem B1189007 : Blo 1188411 1189007 := bstep (se 1 (by rfl) ⟨891755, by rfl⟩ : syracuseStep 1189007 = 1783511) B1783511
theorem B1189051 : Blo 1188411 1189051 := bstep (se 1 (by rfl) ⟨891788, by rfl⟩ : syracuseStep 1189051 = 1783577) B1783577
theorem B5080265 : Blo 1188411 5080265 := bstep (se 2 (by rfl) ⟨1905099, by rfl⟩ : syracuseStep 5080265 = 3810199) B3810199
theorem B1189127 : Blo 1188411 1189127 := bstep (se 1 (by rfl) ⟨891845, by rfl⟩ : syracuseStep 1189127 = 1783691) B1783691
theorem B1189135 : Blo 1188411 1189135 := bstep (se 1 (by rfl) ⟨891851, by rfl⟩ : syracuseStep 1189135 = 1783703) B1783703
theorem B89138465 : Blo 1188411 89138465 := bstep (se 2 (by rfl) ⟨33426924, by rfl⟩ : syracuseStep 89138465 = 66853849) B66853849
theorem B1189179 : Blo 1188411 1189179 := bstep (se 1 (by rfl) ⟨891884, by rfl⟩ : syracuseStep 1189179 = 1783769) B1783769
theorem B1189255 : Blo 1188411 1189255 := bstep (se 1 (by rfl) ⟨891941, by rfl⟩ : syracuseStep 1189255 = 1783883) B1783883
theorem B1189263 : Blo 1188411 1189263 := bstep (se 1 (by rfl) ⟨891947, by rfl⟩ : syracuseStep 1189263 = 1783895) B1783895
theorem B10159505 : Blo 1188411 10159505 := bstep (se 2 (by rfl) ⟨3809814, by rfl⟩ : syracuseStep 10159505 = 7619629) B7619629
theorem B7619987 : Blo 1188411 7619987 := bstep (se 1 (by rfl) ⟨5714990, by rfl⟩ : syracuseStep 7619987 = 11429981) B11429981
theorem B1189307 : Blo 1188411 1189307 := bstep (se 1 (by rfl) ⟨891980, by rfl⟩ : syracuseStep 1189307 = 1783961) B1783961
theorem B1189383 : Blo 1188411 1189383 := bstep (se 1 (by rfl) ⟨892037, by rfl⟩ : syracuseStep 1189383 = 1784075) B1784075
theorem B1189391 : Blo 1188411 1189391 := bstep (se 1 (by rfl) ⟨892043, by rfl⟩ : syracuseStep 1189391 = 1784087) B1784087
theorem B2352655 : Blo 1188411 2352655 := bstep (se 1 (by rfl) ⟨1764491, by rfl⟩ : syracuseStep 2352655 = 3528983) B3528983
theorem B2541089 : Blo 1188411 2541089 := bstep (se 2 (by rfl) ⟨952908, by rfl⟩ : syracuseStep 2541089 = 1905817) B1905817
theorem B1189435 : Blo 1188411 1189435 := bstep (se 1 (by rfl) ⟨892076, by rfl⟩ : syracuseStep 1189435 = 1784153) B1784153
theorem B1189511 : Blo 1188411 1189511 := bstep (se 1 (by rfl) ⟨892133, by rfl⟩ : syracuseStep 1189511 = 1784267) B1784267
theorem B1189519 : Blo 1188411 1189519 := bstep (se 1 (by rfl) ⟨892139, by rfl⟩ : syracuseStep 1189519 = 1784279) B1784279
theorem B1189563 : Blo 1188411 1189563 := bstep (se 1 (by rfl) ⟨892172, by rfl⟩ : syracuseStep 1189563 = 1784345) B1784345
theorem B4015817 : Blo 1188411 4015817 := bstep (se 2 (by rfl) ⟨1505931, by rfl⟩ : syracuseStep 4015817 = 3011863) B3011863
theorem B1189639 : Blo 1188411 1189639 := bstep (se 1 (by rfl) ⟨892229, by rfl⟩ : syracuseStep 1189639 = 1784459) B1784459
theorem B1189647 : Blo 1188411 1189647 := bstep (se 1 (by rfl) ⟨892235, by rfl⟩ : syracuseStep 1189647 = 1784471) B1784471
theorem B3008299 : Blo 1188411 3008299 := bstep (se 1 (by rfl) ⟨2256224, by rfl⟩ : syracuseStep 3008299 = 4512449) B4512449
theorem B1189691 : Blo 1188411 1189691 := bstep (se 1 (by rfl) ⟨892268, by rfl⟩ : syracuseStep 1189691 = 1784537) B1784537
theorem B2541431 : Blo 1188411 2541431 := bstep (se 1 (by rfl) ⟨1906073, by rfl⟩ : syracuseStep 2541431 = 3812147) B3812147
theorem B1189767 : Blo 1188411 1189767 := bstep (se 1 (by rfl) ⟨892325, by rfl⟩ : syracuseStep 1189767 = 1784651) B1784651
theorem B1189775 : Blo 1188411 1189775 := bstep (se 1 (by rfl) ⟨892331, by rfl⟩ : syracuseStep 1189775 = 1784663) B1784663
theorem B3008441 : Blo 1188411 3008441 := bstep (se 2 (by rfl) ⟨1128165, by rfl⟩ : syracuseStep 3008441 = 2256331) B2256331
theorem B1189819 : Blo 1188411 1189819 := bstep (se 1 (by rfl) ⟨892364, by rfl⟩ : syracuseStep 1189819 = 1784729) B1784729
theorem B1189895 : Blo 1188411 1189895 := bstep (se 1 (by rfl) ⟨892421, by rfl⟩ : syracuseStep 1189895 = 1784843) B1784843
theorem B4515851 : Blo 1188411 4515851 := bstep (se 1 (by rfl) ⟨3386888, by rfl⟩ : syracuseStep 4515851 = 6773777) B6773777
theorem B1337359 : Blo 1188411 1337359 := bstep (se 1 (by rfl) ⟨1003019, by rfl⟩ : syracuseStep 1337359 = 2006039) B2006039
theorem B1189903 : Blo 1188411 1189903 := bstep (se 1 (by rfl) ⟨892427, by rfl⟩ : syracuseStep 1189903 = 1784855) B1784855
theorem B1189947 : Blo 1188411 1189947 := bstep (se 1 (by rfl) ⟨892460, by rfl⟩ : syracuseStep 1189947 = 1784921) B1784921
theorem B6522967 : Blo 1188411 6522967 := bstep (se 1 (by rfl) ⟨4892225, by rfl⟩ : syracuseStep 6522967 = 9784451) B9784451
theorem B1190023 : Blo 1188411 1190023 := bstep (se 1 (by rfl) ⟨892517, by rfl⟩ : syracuseStep 1190023 = 1785035) B1785035
theorem B1190031 : Blo 1188411 1190031 := bstep (se 1 (by rfl) ⟨892523, by rfl⟩ : syracuseStep 1190031 = 1785047) B1785047
theorem B1190075 : Blo 1188411 1190075 := bstep (se 1 (by rfl) ⟨892556, by rfl⟩ : syracuseStep 1190075 = 1785113) B1785113
theorem B1190151 : Blo 1188411 1190151 := bstep (se 1 (by rfl) ⟨892613, by rfl⟩ : syracuseStep 1190151 = 1785227) B1785227
theorem B1190159 : Blo 1188411 1190159 := bstep (se 1 (by rfl) ⟨892619, by rfl⟩ : syracuseStep 1190159 = 1785239) B1785239
theorem B6768947 : Blo 1188411 6768947 := bstep (se 1 (by rfl) ⟨5076710, by rfl⟩ : syracuseStep 6768947 = 10153421) B10153421
theorem B3049787 : Blo 1188411 3049787 := bstep (se 1 (by rfl) ⟨2287340, by rfl⟩ : syracuseStep 3049787 = 4574681) B4574681
theorem B6023483 : Blo 1188411 6023483 := bstep (se 1 (by rfl) ⟨4517612, by rfl⟩ : syracuseStep 6023483 = 9035225) B9035225
theorem B1190203 : Blo 1188411 1190203 := bstep (se 1 (by rfl) ⟨892652, by rfl⟩ : syracuseStep 1190203 = 1785305) B1785305
theorem B4016519 : Blo 1188411 4016519 := bstep (se 1 (by rfl) ⟨3012389, by rfl⟩ : syracuseStep 4016519 = 6024779) B6024779
theorem B1190279 : Blo 1188411 1190279 := bstep (se 1 (by rfl) ⟨892709, by rfl⟩ : syracuseStep 1190279 = 1785419) B1785419
theorem B1190287 : Blo 1188411 1190287 := bstep (se 1 (by rfl) ⟨892715, by rfl⟩ : syracuseStep 1190287 = 1785431) B1785431
theorem B1190331 : Blo 1188411 1190331 := bstep (se 1 (by rfl) ⟨892748, by rfl⟩ : syracuseStep 1190331 = 1785497) B1785497
theorem B6023645 : Blo 1188411 6023645 := bstep (se 3 (by rfl) ⟨1129433, by rfl⟩ : syracuseStep 6023645 = 2258867) B2258867
theorem B1337863 : Blo 1188411 1337863 := bstep (se 1 (by rfl) ⟨1003397, by rfl⟩ : syracuseStep 1337863 = 2006795) B2006795
theorem B1190407 : Blo 1188411 1190407 := bstep (se 1 (by rfl) ⟨892805, by rfl⟩ : syracuseStep 1190407 = 1785611) B1785611
theorem B43412087 : Blo 1188411 43412087 := bstep (se 1 (by rfl) ⟨32559065, by rfl⟩ : syracuseStep 43412087 = 65118131) B65118131
theorem B1338043 : Blo 1188411 1338043 := bstep (se 1 (by rfl) ⟨1003532, by rfl⟩ : syracuseStep 1338043 = 2007065) B2007065
theorem B1608379 : Blo 1188411 1608379 := bstep (se 1 (by rfl) ⟨1206284, by rfl⟩ : syracuseStep 1608379 = 2412569) B2412569
theorem B4016897 : Blo 1188411 4016897 := bstep (se 2 (by rfl) ⟨1506336, by rfl⟩ : syracuseStep 4016897 = 3012673) B3012673
theorem B6023969 : Blo 1188411 6023969 := bstep (se 2 (by rfl) ⟨2258988, by rfl⟩ : syracuseStep 6023969 = 4517977) B4517977
theorem B22866725 : Blo 1188411 22866725 := bstep (se 4 (by rfl) ⟨2143755, by rfl⟩ : syracuseStep 22866725 = 4287511) B4287511
theorem B1428359 : Blo 1188411 1428359 := bstep (se 1 (by rfl) ⟨1071269, by rfl⟩ : syracuseStep 1428359 = 2142539) B2142539
theorem B3009433 : Blo 1188411 3009433 := bstep (se 2 (by rfl) ⟨1128537, by rfl⟩ : syracuseStep 3009433 = 2257075) B2257075
theorem B4516793 : Blo 1188411 4516793 := bstep (se 2 (by rfl) ⟨1693797, by rfl⟩ : syracuseStep 4516793 = 3387595) B3387595
theorem B5082041 : Blo 1188411 5082041 := bstep (se 2 (by rfl) ⟨1905765, by rfl⟩ : syracuseStep 5082041 = 3811531) B3811531
theorem B3386411 : Blo 1188411 3386411 := bstep (se 1 (by rfl) ⟨2539808, by rfl⟩ : syracuseStep 3386411 = 5079617) B5079617
theorem B3009595 : Blo 1188411 3009595 := bstep (se 1 (by rfl) ⟨2257196, by rfl⟩ : syracuseStep 3009595 = 4514393) B4514393
theorem B5868605 : Blo 1188411 5868605 := bstep (se 3 (by rfl) ⟨1100363, by rfl⟩ : syracuseStep 5868605 = 2200727) B2200727
theorem B31329341 : Blo 1188411 31329341 := bstep (se 3 (by rfl) ⟨5874251, by rfl⟩ : syracuseStep 31329341 = 11748503) B11748503
theorem B1338511 : Blo 1188411 1338511 := bstep (se 1 (by rfl) ⟨1003883, by rfl⟩ : syracuseStep 1338511 = 2007767) B2007767
theorem B3009737 : Blo 1188411 3009737 := bstep (se 2 (by rfl) ⟨1128651, by rfl⟩ : syracuseStep 3009737 = 2257303) B2257303
theorem B3812609 : Blo 1188411 3812609 := bstep (se 2 (by rfl) ⟨1429728, by rfl⟩ : syracuseStep 3812609 = 2859457) B2859457
theorem B2673935 : Blo 1188411 2673935 := bstep (se 1 (by rfl) ⟨2005451, by rfl⟩ : syracuseStep 2673935 = 4010903) B4010903
theorem B2673953 : Blo 1188411 2673953 := bstep (se 2 (by rfl) ⟨1002732, by rfl⟩ : syracuseStep 2673953 = 2005465) B2005465
theorem B1903915 : Blo 1188411 1903915 := bstep (se 1 (by rfl) ⟨1427936, by rfl⟩ : syracuseStep 1903915 = 2855873) B2855873
theorem B2256187 : Blo 1188411 2256187 := bstep (se 1 (by rfl) ⟨1692140, by rfl⟩ : syracuseStep 2256187 = 3384281) B3384281
theorem B27839875 : Blo 1188411 27839875 := bstep (se 1 (by rfl) ⟨20879906, by rfl⟩ : syracuseStep 27839875 = 41759813) B41759813
theorem B3812761 : Blo 1188411 3812761 := bstep (se 2 (by rfl) ⟨1429785, by rfl⟩ : syracuseStep 3812761 = 2859571) B2859571
theorem B3010081 : Blo 1188411 3010081 := bstep (se 2 (by rfl) ⟨1128780, by rfl⟩ : syracuseStep 3010081 = 2257561) B2257561
theorem B1429051 : Blo 1188411 1429051 := bstep (se 1 (by rfl) ⟨1071788, by rfl⟩ : syracuseStep 1429051 = 2143577) B2143577
theorem B2674295 : Blo 1188411 2674295 := bstep (se 1 (by rfl) ⟨2005721, by rfl⟩ : syracuseStep 2674295 = 4011443) B4011443
theorem B1339015 : Blo 1188411 1339015 := bstep (se 1 (by rfl) ⟨1004261, by rfl⟩ : syracuseStep 1339015 = 2008523) B2008523
theorem B6770405 : Blo 1188411 6770405 := bstep (se 4 (by rfl) ⟨634725, by rfl⟩ : syracuseStep 6770405 = 1269451) B1269451
theorem B6024941 : Blo 1188411 6024941 := bstep (se 3 (by rfl) ⟨1129676, by rfl⟩ : syracuseStep 6024941 = 2259353) B2259353
theorem B2256673 : Blo 1188411 2256673 := bstep (se 2 (by rfl) ⟨846252, by rfl⟩ : syracuseStep 2256673 = 1692505) B1692505
theorem B2674475 : Blo 1188411 2674475 := bstep (se 1 (by rfl) ⟨2005856, by rfl⟩ : syracuseStep 2674475 = 4011713) B4011713
theorem B1339195 : Blo 1188411 1339195 := bstep (se 1 (by rfl) ⟨1004396, by rfl⟩ : syracuseStep 1339195 = 2008793) B2008793
theorem B3387197 : Blo 1188411 3387197 := bstep (se 3 (by rfl) ⟨635099, by rfl⟩ : syracuseStep 3387197 = 1270199) B1270199
theorem B20590487 : Blo 1188411 20590487 := bstep (se 1 (by rfl) ⟨15442865, by rfl⟩ : syracuseStep 20590487 = 30885731) B30885731
theorem B5083033 : Blo 1188411 5083033 := bstep (se 2 (by rfl) ⟨1906137, by rfl⟩ : syracuseStep 5083033 = 3812275) B3812275
theorem B14479307 : Blo 1188411 14479307 := bstep (se 1 (by rfl) ⟨10859480, by rfl⟩ : syracuseStep 14479307 = 21718961) B21718961
theorem B3010679 : Blo 1188411 3010679 := bstep (se 1 (by rfl) ⟨2258009, by rfl⟩ : syracuseStep 3010679 = 4516019) B4516019
theorem B3387527 : Blo 1188411 3387527 := bstep (se 1 (by rfl) ⟨2540645, by rfl⟩ : syracuseStep 3387527 = 5081291) B5081291
theorem B2674835 : Blo 1188411 2674835 := bstep (se 1 (by rfl) ⟨2006126, by rfl⟩ : syracuseStep 2674835 = 4012253) B4012253
theorem B6770861 : Blo 1188411 6770861 := bstep (se 3 (by rfl) ⟨1269536, by rfl⟩ : syracuseStep 6770861 = 2539073) B2539073
theorem B2674889 : Blo 1188411 2674889 := bstep (se 2 (by rfl) ⟨1003083, by rfl⟩ : syracuseStep 2674889 = 2006167) B2006167
theorem B6435073 : Blo 1188411 6435073 := bstep (se 2 (by rfl) ⟨2413152, by rfl⟩ : syracuseStep 6435073 = 4826305) B4826305
theorem B7721249 : Blo 1188411 7721249 := bstep (se 2 (by rfl) ⟨2895468, by rfl⟩ : syracuseStep 7721249 = 5790937) B5790937
theorem B4821281 : Blo 1188411 4821281 := bstep (se 2 (by rfl) ⟨1807980, by rfl⟩ : syracuseStep 4821281 = 3615961) B3615961
theorem B6861115 : Blo 1188411 6861115 := bstep (se 1 (by rfl) ⟨5145836, by rfl⟩ : syracuseStep 6861115 = 10291673) B10291673
theorem B6017489 : Blo 1188411 6017489 := bstep (se 2 (by rfl) ⟨2256558, by rfl⟩ : syracuseStep 6017489 = 4513117) B4513117
theorem B6025751 : Blo 1188411 6025751 := bstep (se 1 (by rfl) ⟨4519313, by rfl⟩ : syracuseStep 6025751 = 9038627) B9038627
theorem B3863069 : Blo 1188411 3863069 := bstep (se 3 (by rfl) ⟨724325, by rfl⟩ : syracuseStep 3863069 = 1448651) B1448651
theorem B7615043 : Blo 1188411 7615043 := bstep (se 1 (by rfl) ⟨5711282, by rfl⟩ : syracuseStep 7615043 = 11422565) B11422565
theorem B3666551 : Blo 1188411 3666551 := bstep (se 1 (by rfl) ⟨2749913, by rfl⟩ : syracuseStep 3666551 = 5499827) B5499827
theorem B6861485 : Blo 1188411 6861485 := bstep (se 3 (by rfl) ⟨1286528, by rfl⟩ : syracuseStep 6861485 = 2573057) B2573057
theorem B7721729 : Blo 1188411 7721729 := bstep (se 2 (by rfl) ⟨2895648, by rfl⟩ : syracuseStep 7721729 = 5791297) B5791297
theorem B5952271 : Blo 1188411 5952271 := bstep (se 1 (by rfl) ⟨4464203, by rfl⟩ : syracuseStep 5952271 = 8928407) B8928407
theorem B13546277 : Blo 1188411 13546277 := bstep (se 4 (by rfl) ⟨1269963, by rfl⟩ : syracuseStep 13546277 = 2539927) B2539927
theorem B6771545 : Blo 1188411 6771545 := bstep (se 2 (by rfl) ⟨2539329, by rfl⟩ : syracuseStep 6771545 = 5078659) B5078659
theorem B1782647 : Blo 1188411 1782647 := bstep (se 1 (by rfl) ⟨1336985, by rfl⟩ : syracuseStep 1782647 = 2673971) B2673971
theorem B2675591 : Blo 1188411 2675591 := bstep (se 1 (by rfl) ⟨2006693, by rfl⟩ : syracuseStep 2675591 = 4013387) B4013387
theorem B1782671 : Blo 1188411 1782671 := bstep (se 1 (by rfl) ⟨1337003, by rfl⟩ : syracuseStep 1782671 = 2674007) B2674007
theorem B1782713 : Blo 1188411 1782713 := bstep (se 2 (by rfl) ⟨668517, by rfl⟩ : syracuseStep 1782713 = 1337035) B1337035
theorem B2257865 : Blo 1188411 2257865 := bstep (se 2 (by rfl) ⟨846699, by rfl⟩ : syracuseStep 2257865 = 1693399) B1693399
theorem B43439075 : Blo 1188411 43439075 := bstep (se 1 (by rfl) ⟨32579306, by rfl⟩ : syracuseStep 43439075 = 65158613) B65158613
theorem B1782791 : Blo 1188411 1782791 := bstep (se 1 (by rfl) ⟨1337093, by rfl⟩ : syracuseStep 1782791 = 2674187) B2674187
theorem B1504271 : Blo 1188411 1504271 := bstep (se 1 (by rfl) ⟨1128203, by rfl⟩ : syracuseStep 1504271 = 2256407) B2256407
theorem B1782827 : Blo 1188411 1782827 := bstep (se 1 (by rfl) ⟨1337120, by rfl⟩ : syracuseStep 1782827 = 2674241) B2674241
theorem B2675771 : Blo 1188411 2675771 := bstep (se 1 (by rfl) ⟨2006828, by rfl⟩ : syracuseStep 2675771 = 4013657) B4013657
theorem B1782857 : Blo 1188411 1782857 := bstep (se 2 (by rfl) ⟨668571, by rfl⟩ : syracuseStep 1782857 = 1337143) B1337143
theorem B2856055 : Blo 1188411 2856055 := bstep (se 1 (by rfl) ⟨2142041, by rfl⟩ : syracuseStep 2856055 = 4284083) B4284083
theorem B2675897 : Blo 1188411 2675897 := bstep (se 2 (by rfl) ⟨1003461, by rfl⟩ : syracuseStep 2675897 = 2006923) B2006923
theorem B1782971 : Blo 1188411 1782971 := bstep (se 1 (by rfl) ⟨1337228, by rfl⟩ : syracuseStep 1782971 = 2674457) B2674457
theorem B7230701 : Blo 1188411 7230701 := bstep (se 3 (by rfl) ⟨1355756, by rfl⟩ : syracuseStep 7230701 = 2711513) B2711513
theorem B1783031 : Blo 1188411 1783031 := bstep (se 1 (by rfl) ⟨1337273, by rfl⟩ : syracuseStep 1783031 = 2674547) B2674547
theorem B1783055 : Blo 1188411 1783055 := bstep (se 1 (by rfl) ⟨1337291, by rfl⟩ : syracuseStep 1783055 = 2674583) B2674583
theorem B17143073 : Blo 1188411 17143073 := bstep (se 2 (by rfl) ⟨6428652, by rfl⟩ : syracuseStep 17143073 = 12857305) B12857305
theorem B1783097 : Blo 1188411 1783097 := bstep (se 2 (by rfl) ⟨668661, by rfl⟩ : syracuseStep 1783097 = 1337323) B1337323
theorem B1783175 : Blo 1188411 1783175 := bstep (se 1 (by rfl) ⟨1337381, by rfl⟩ : syracuseStep 1783175 = 2674763) B2674763
theorem B3011975 : Blo 1188411 3011975 := bstep (se 1 (by rfl) ⟨2258981, by rfl⟩ : syracuseStep 3011975 = 4517963) B4517963
theorem B1783211 : Blo 1188411 1783211 := bstep (se 1 (by rfl) ⟨1337408, by rfl⟩ : syracuseStep 1783211 = 2674817) B2674817
theorem B3012025 : Blo 1188411 3012025 := bstep (se 2 (by rfl) ⟨1129509, by rfl⟩ : syracuseStep 3012025 = 2259019) B2259019
theorem B1783241 : Blo 1188411 1783241 := bstep (se 2 (by rfl) ⟨668715, by rfl⟩ : syracuseStep 1783241 = 1337431) B1337431
theorem B4519435 : Blo 1188411 4519435 := bstep (se 1 (by rfl) ⟨3389576, by rfl⟩ : syracuseStep 4519435 = 6779153) B6779153
theorem B2676239 : Blo 1188411 2676239 := bstep (se 1 (by rfl) ⟨2007179, by rfl⟩ : syracuseStep 2676239 = 4014359) B4014359
theorem B2676257 : Blo 1188411 2676257 := bstep (se 2 (by rfl) ⟨1003596, by rfl⟩ : syracuseStep 2676257 = 2007193) B2007193
theorem B1783355 : Blo 1188411 1783355 := bstep (se 1 (by rfl) ⟨1337516, by rfl⟩ : syracuseStep 1783355 = 2675033) B2675033
theorem B3216955 : Blo 1188411 3216955 := bstep (se 1 (by rfl) ⟨2412716, by rfl⟩ : syracuseStep 3216955 = 4825433) B4825433
theorem B1783415 : Blo 1188411 1783415 := bstep (se 1 (by rfl) ⟨1337561, by rfl⟩ : syracuseStep 1783415 = 2675123) B2675123
theorem B1783439 : Blo 1188411 1783439 := bstep (se 1 (by rfl) ⟨1337579, by rfl⟩ : syracuseStep 1783439 = 2675159) B2675159
theorem B2258579 : Blo 1188411 2258579 := bstep (se 1 (by rfl) ⟨1693934, by rfl⟩ : syracuseStep 2258579 = 3387869) B3387869
theorem B1783481 : Blo 1188411 1783481 := bstep (se 2 (by rfl) ⟨668805, by rfl⟩ : syracuseStep 1783481 = 1337611) B1337611
theorem B2258617 : Blo 1188411 2258617 := bstep (se 2 (by rfl) ⟨846981, by rfl⟩ : syracuseStep 2258617 = 1693963) B1693963
theorem B25720577 : Blo 1188411 25720577 := bstep (se 2 (by rfl) ⟨9645216, by rfl⟩ : syracuseStep 25720577 = 19290433) B19290433
theorem B1783559 : Blo 1188411 1783559 := bstep (se 1 (by rfl) ⟨1337669, by rfl⟩ : syracuseStep 1783559 = 2675339) B2675339
theorem B3618589 : Blo 1188411 3618589 := bstep (se 3 (by rfl) ⟨678485, by rfl⟩ : syracuseStep 3618589 = 1356971) B1356971
theorem B1783595 : Blo 1188411 1783595 := bstep (se 1 (by rfl) ⟨1337696, by rfl⟩ : syracuseStep 1783595 = 2675393) B2675393
theorem B5429051 : Blo 1188411 5429051 := bstep (se 1 (by rfl) ⟨4071788, by rfl⟩ : syracuseStep 5429051 = 8143577) B8143577
theorem B4519739 : Blo 1188411 4519739 := bstep (se 1 (by rfl) ⟨3389804, by rfl⟩ : syracuseStep 4519739 = 6779609) B6779609
theorem B1783625 : Blo 1188411 1783625 := bstep (se 2 (by rfl) ⟨668859, by rfl⟩ : syracuseStep 1783625 = 1337719) B1337719
theorem B2676599 : Blo 1188411 2676599 := bstep (se 1 (by rfl) ⟨2007449, by rfl⟩ : syracuseStep 2676599 = 4014899) B4014899
theorem B3389303 : Blo 1188411 3389303 := bstep (se 1 (by rfl) ⟨2541977, by rfl⟩ : syracuseStep 3389303 = 5083955) B5083955
theorem B4011929 : Blo 1188411 4011929 := bstep (se 2 (by rfl) ⟨1504473, by rfl⟩ : syracuseStep 4011929 = 3008947) B3008947
theorem B7624601 : Blo 1188411 7624601 := bstep (se 2 (by rfl) ⟨2859225, by rfl⟩ : syracuseStep 7624601 = 5718451) B5718451
theorem B1783739 : Blo 1188411 1783739 := bstep (se 1 (by rfl) ⟨1337804, by rfl⟩ : syracuseStep 1783739 = 2675609) B2675609
theorem B1783799 : Blo 1188411 1783799 := bstep (se 1 (by rfl) ⟨1337849, by rfl⟩ : syracuseStep 1783799 = 2675699) B2675699
theorem B1783823 : Blo 1188411 1783823 := bstep (se 1 (by rfl) ⟨1337867, by rfl⟩ : syracuseStep 1783823 = 2675735) B2675735
theorem B3012623 : Blo 1188411 3012623 := bstep (se 1 (by rfl) ⟨2259467, by rfl⟩ : syracuseStep 3012623 = 4518935) B4518935
theorem B2676779 : Blo 1188411 2676779 := bstep (se 1 (by rfl) ⟨2007584, by rfl⟩ : syracuseStep 2676779 = 4015169) B4015169
theorem B1783865 : Blo 1188411 1783865 := bstep (se 2 (by rfl) ⟨668949, by rfl⟩ : syracuseStep 1783865 = 1337899) B1337899
theorem B6862967 : Blo 1188411 6862967 := bstep (se 1 (by rfl) ⟨5147225, by rfl⟩ : syracuseStep 6862967 = 10294451) B10294451
theorem B1783943 : Blo 1188411 1783943 := bstep (se 1 (by rfl) ⟨1337957, by rfl⟩ : syracuseStep 1783943 = 2675915) B2675915
theorem B1783979 : Blo 1188411 1783979 := bstep (se 1 (by rfl) ⟨1337984, by rfl⟩ : syracuseStep 1783979 = 2675969) B2675969
theorem B1784009 : Blo 1188411 1784009 := bstep (se 2 (by rfl) ⟨669003, by rfl⟩ : syracuseStep 1784009 = 1338007) B1338007
theorem B1784123 : Blo 1188411 1784123 := bstep (se 1 (by rfl) ⟨1338092, by rfl⟩ : syracuseStep 1784123 = 2676185) B2676185
theorem B1784183 : Blo 1188411 1784183 := bstep (se 1 (by rfl) ⟨1338137, by rfl⟩ : syracuseStep 1784183 = 2676275) B2676275
theorem B1694071 : Blo 1188411 1694071 := bstep (se 1 (by rfl) ⟨1270553, by rfl⟩ : syracuseStep 1694071 = 2541107) B2541107
theorem B1784207 : Blo 1188411 1784207 := bstep (se 1 (by rfl) ⟨1338155, by rfl⟩ : syracuseStep 1784207 = 2676311) B2676311
theorem B2677139 : Blo 1188411 2677139 := bstep (se 1 (by rfl) ⟨2007854, by rfl⟩ : syracuseStep 2677139 = 4015709) B4015709
theorem B1784249 : Blo 1188411 1784249 := bstep (se 2 (by rfl) ⟨669093, by rfl⟩ : syracuseStep 1784249 = 1338187) B1338187
theorem B2677193 : Blo 1188411 2677193 := bstep (se 2 (by rfl) ⟨1003947, by rfl⟩ : syracuseStep 2677193 = 2007895) B2007895
theorem B1784327 : Blo 1188411 1784327 := bstep (se 1 (by rfl) ⟨1338245, by rfl⟩ : syracuseStep 1784327 = 2676491) B2676491
theorem B6019595 : Blo 1188411 6019595 := bstep (se 1 (by rfl) ⟨4514696, by rfl⟩ : syracuseStep 6019595 = 9029393) B9029393
theorem B2005519 : Blo 1188411 2005519 := bstep (se 1 (by rfl) ⟨1504139, by rfl⟩ : syracuseStep 2005519 = 3008279) B3008279
theorem B1784363 : Blo 1188411 1784363 := bstep (se 1 (by rfl) ⟨1338272, by rfl⟩ : syracuseStep 1784363 = 2676545) B2676545
theorem B1784393 : Blo 1188411 1784393 := bstep (se 2 (by rfl) ⟨669147, by rfl⟩ : syracuseStep 1784393 = 1338295) B1338295
theorem B4012631 : Blo 1188411 4012631 := bstep (se 1 (by rfl) ⟨3009473, by rfl⟩ : syracuseStep 4012631 = 6018947) B6018947
theorem B3717767 : Blo 1188411 3717767 := bstep (se 1 (by rfl) ⟨2788325, by rfl⟩ : syracuseStep 3717767 = 5576651) B5576651
theorem B6019757 : Blo 1188411 6019757 := bstep (se 3 (by rfl) ⟨1128704, by rfl⟩ : syracuseStep 6019757 = 2257409) B2257409
theorem B1784507 : Blo 1188411 1784507 := bstep (se 1 (by rfl) ⟨1338380, by rfl⟩ : syracuseStep 1784507 = 2676761) B2676761
theorem B1784567 : Blo 1188411 1784567 := bstep (se 1 (by rfl) ⟨1338425, by rfl⟩ : syracuseStep 1784567 = 2676851) B2676851
theorem B1784591 : Blo 1188411 1784591 := bstep (se 1 (by rfl) ⟨1338443, by rfl⟩ : syracuseStep 1784591 = 2676887) B2676887
theorem B25787173 : Blo 1188411 25787173 := bstep (se 4 (by rfl) ⟨2417547, by rfl⟩ : syracuseStep 25787173 = 4835095) B4835095
theorem B1784633 : Blo 1188411 1784633 := bstep (se 2 (by rfl) ⟨669237, by rfl⟩ : syracuseStep 1784633 = 1338475) B1338475
theorem B8567641 : Blo 1188411 8567641 := bstep (se 2 (by rfl) ⟨3212865, by rfl⟩ : syracuseStep 8567641 = 6425731) B6425731
theorem B1784711 : Blo 1188411 1784711 := bstep (se 1 (by rfl) ⟨1338533, by rfl⟩ : syracuseStep 1784711 = 2677067) B2677067
theorem B2898841 : Blo 1188411 2898841 := bstep (se 2 (by rfl) ⟨1087065, by rfl⟩ : syracuseStep 2898841 = 2174131) B2174131
theorem B1784747 : Blo 1188411 1784747 := bstep (se 1 (by rfl) ⟨1338560, by rfl⟩ : syracuseStep 1784747 = 2677121) B2677121
theorem B1784777 : Blo 1188411 1784777 := bstep (se 2 (by rfl) ⟨669291, by rfl⟩ : syracuseStep 1784777 = 1338583) B1338583
theorem B2006059 : Blo 1188411 2006059 := bstep (se 1 (by rfl) ⟨1504544, by rfl⟩ : syracuseStep 2006059 = 3009089) B3009089
theorem B1784891 : Blo 1188411 1784891 := bstep (se 1 (by rfl) ⟨1338668, by rfl⟩ : syracuseStep 1784891 = 2677337) B2677337
theorem B4013117 : Blo 1188411 4013117 := bstep (se 3 (by rfl) ⟨752459, by rfl⟩ : syracuseStep 4013117 = 1504919) B1504919
theorem B1784951 : Blo 1188411 1784951 := bstep (se 1 (by rfl) ⟨1338713, by rfl⟩ : syracuseStep 1784951 = 2677427) B2677427
theorem B2677895 : Blo 1188411 2677895 := bstep (se 1 (by rfl) ⟨2008421, by rfl⟩ : syracuseStep 2677895 = 4016843) B4016843
theorem B1784975 : Blo 1188411 1784975 := bstep (se 1 (by rfl) ⟨1338731, by rfl⟩ : syracuseStep 1784975 = 2677463) B2677463
theorem B1694891 : Blo 1188411 1694891 := bstep (se 1 (by rfl) ⟨1271168, by rfl⟩ : syracuseStep 1694891 = 2542337) B2542337
theorem B2006201 : Blo 1188411 2006201 := bstep (se 2 (by rfl) ⟨752325, by rfl⟩ : syracuseStep 2006201 = 1504651) B1504651
theorem B1785017 : Blo 1188411 1785017 := bstep (se 2 (by rfl) ⟨669381, by rfl⟩ : syracuseStep 1785017 = 1338763) B1338763
theorem B2538697 : Blo 1188411 2538697 := bstep (se 2 (by rfl) ⟨952011, by rfl⟩ : syracuseStep 2538697 = 1904023) B1904023
theorem B1785095 : Blo 1188411 1785095 := bstep (se 1 (by rfl) ⟨1338821, by rfl⟩ : syracuseStep 1785095 = 2677643) B2677643
theorem B1785131 : Blo 1188411 1785131 := bstep (se 1 (by rfl) ⟨1338848, by rfl⟩ : syracuseStep 1785131 = 2677697) B2677697
theorem B2678075 : Blo 1188411 2678075 := bstep (se 1 (by rfl) ⟨2008556, by rfl⟩ : syracuseStep 2678075 = 4017113) B4017113
theorem B1785161 : Blo 1188411 1785161 := bstep (se 2 (by rfl) ⟨669435, by rfl⟩ : syracuseStep 1785161 = 1338871) B1338871
theorem B9026963 : Blo 1188411 9026963 := bstep (se 1 (by rfl) ⟨6770222, by rfl⟩ : syracuseStep 9026963 = 13540445) B13540445
theorem B2678201 : Blo 1188411 2678201 := bstep (se 2 (by rfl) ⟨1004325, by rfl⟩ : syracuseStep 2678201 = 2008651) B2008651
theorem B1785275 : Blo 1188411 1785275 := bstep (se 1 (by rfl) ⟨1338956, by rfl⟩ : syracuseStep 1785275 = 2677913) B2677913
theorem B10157521 : Blo 1188411 10157521 := bstep (se 2 (by rfl) ⟨3809070, by rfl⟩ : syracuseStep 10157521 = 7618141) B7618141
theorem B1785335 : Blo 1188411 1785335 := bstep (se 1 (by rfl) ⟨1339001, by rfl⟩ : syracuseStep 1785335 = 2678003) B2678003
theorem B1785359 : Blo 1188411 1785359 := bstep (se 1 (by rfl) ⟨1339019, by rfl⟩ : syracuseStep 1785359 = 2678039) B2678039
theorem B1785401 : Blo 1188411 1785401 := bstep (se 2 (by rfl) ⟨669525, by rfl⟩ : syracuseStep 1785401 = 1339051) B1339051
theorem B2858611 : Blo 1188411 2858611 := bstep (se 1 (by rfl) ⟨2143958, by rfl⟩ : syracuseStep 2858611 = 4287917) B4287917
theorem B1785479 : Blo 1188411 1785479 := bstep (se 1 (by rfl) ⟨1339109, by rfl⟩ : syracuseStep 1785479 = 2678219) B2678219
theorem B1785515 : Blo 1188411 1785515 := bstep (se 1 (by rfl) ⟨1339136, by rfl⟩ : syracuseStep 1785515 = 2678273) B2678273
theorem B1785545 : Blo 1188411 1785545 := bstep (se 2 (by rfl) ⟨669579, by rfl⟩ : syracuseStep 1785545 = 1339159) B1339159
theorem B2006903 : Blo 1188411 2006903 := bstep (se 1 (by rfl) ⟨1505177, by rfl⟩ : syracuseStep 2006903 = 3010355) B3010355
theorem B9404419 : Blo 1188411 9404419 := bstep (se 1 (by rfl) ⟨7053314, by rfl⟩ : syracuseStep 9404419 = 14106629) B14106629
theorem B2007119 : Blo 1188411 2007119 := bstep (se 1 (by rfl) ⟨1505339, by rfl⟩ : syracuseStep 2007119 = 3010679) B3010679
theorem B4513907 : Blo 1188411 4513907 := bstep (se 1 (by rfl) ⟨3385430, by rfl⟩ : syracuseStep 4513907 = 6770861) B6770861
theorem B4014251 : Blo 1188411 4014251 := bstep (se 1 (by rfl) ⟨3010688, by rfl⟩ : syracuseStep 4014251 = 6021377) B6021377
theorem B26083685 : Blo 1188411 26083685 := bstep (se 4 (by rfl) ⟨2445345, by rfl⟩ : syracuseStep 26083685 = 4890691) B4890691
theorem B4514363 : Blo 1188411 4514363 := bstep (se 1 (by rfl) ⟨3385772, by rfl⟩ : syracuseStep 4514363 = 6771545) B6771545
theorem B1188431 : Blo 1188411 1188431 := bstep (se 1 (by rfl) ⟨891323, by rfl⟩ : syracuseStep 1188431 = 1782647) B1782647
theorem B1188447 : Blo 1188411 1188447 := bstep (se 1 (by rfl) ⟨891335, by rfl⟩ : syracuseStep 1188447 = 1782671) B1782671
theorem B1188475 : Blo 1188411 1188475 := bstep (se 1 (by rfl) ⟨891356, by rfl⟩ : syracuseStep 1188475 = 1782713) B1782713
theorem B28959383 : Blo 1188411 28959383 := bstep (se 1 (by rfl) ⟨21719537, by rfl⟩ : syracuseStep 28959383 = 43439075) B43439075
theorem B1188527 : Blo 1188411 1188527 := bstep (se 1 (by rfl) ⟨891395, by rfl⟩ : syracuseStep 1188527 = 1782791) B1782791
theorem B1188551 : Blo 1188411 1188551 := bstep (se 1 (by rfl) ⟨891413, by rfl⟩ : syracuseStep 1188551 = 1782827) B1782827
theorem B4014791 : Blo 1188411 4014791 := bstep (se 1 (by rfl) ⟨3011093, by rfl⟩ : syracuseStep 4014791 = 6022187) B6022187
theorem B1188571 : Blo 1188411 1188571 := bstep (se 1 (by rfl) ⟨891428, by rfl⟩ : syracuseStep 1188571 = 1782857) B1782857
theorem B1188647 : Blo 1188411 1188647 := bstep (se 1 (by rfl) ⟨891485, by rfl⟩ : syracuseStep 1188647 = 1782971) B1782971
theorem B1188687 : Blo 1188411 1188687 := bstep (se 1 (by rfl) ⟨891515, by rfl⟩ : syracuseStep 1188687 = 1783031) B1783031
theorem B1188703 : Blo 1188411 1188703 := bstep (se 1 (by rfl) ⟨891527, by rfl⟩ : syracuseStep 1188703 = 1783055) B1783055
theorem B59425643 : Blo 1188411 59425643 := bstep (se 1 (by rfl) ⟨44569232, by rfl⟩ : syracuseStep 59425643 = 89138465) B89138465
theorem B11428715 : Blo 1188411 11428715 := bstep (se 1 (by rfl) ⟨8571536, by rfl⟩ : syracuseStep 11428715 = 17143073) B17143073
theorem B1188731 : Blo 1188411 1188731 := bstep (se 1 (by rfl) ⟨891548, by rfl⟩ : syracuseStep 1188731 = 1783097) B1783097
theorem B1188783 : Blo 1188411 1188783 := bstep (se 1 (by rfl) ⟨891587, by rfl⟩ : syracuseStep 1188783 = 1783175) B1783175
theorem B2007983 : Blo 1188411 2007983 := bstep (se 1 (by rfl) ⟨1505987, by rfl⟩ : syracuseStep 2007983 = 3011975) B3011975
theorem B5079991 : Blo 1188411 5079991 := bstep (se 1 (by rfl) ⟨3809993, by rfl⟩ : syracuseStep 5079991 = 7619987) B7619987
theorem B1188807 : Blo 1188411 1188807 := bstep (se 1 (by rfl) ⟨891605, by rfl⟩ : syracuseStep 1188807 = 1783211) B1783211
theorem B1188827 : Blo 1188411 1188827 := bstep (se 1 (by rfl) ⟨891620, by rfl⟩ : syracuseStep 1188827 = 1783241) B1783241
theorem B1188903 : Blo 1188411 1188903 := bstep (se 1 (by rfl) ⟨891677, by rfl⟩ : syracuseStep 1188903 = 1783355) B1783355
theorem B20317229 : Blo 1188411 20317229 := bstep (se 3 (by rfl) ⟨3809480, by rfl⟩ : syracuseStep 20317229 = 7618961) B7618961
theorem B34382897 : Blo 1188411 34382897 := bstep (se 2 (by rfl) ⟨12893586, by rfl⟩ : syracuseStep 34382897 = 25787173) B25787173
theorem B1188943 : Blo 1188411 1188943 := bstep (se 1 (by rfl) ⟨891707, by rfl⟩ : syracuseStep 1188943 = 1783415) B1783415
theorem B1188959 : Blo 1188411 1188959 := bstep (se 1 (by rfl) ⟨891719, by rfl⟩ : syracuseStep 1188959 = 1783439) B1783439
theorem B1188987 : Blo 1188411 1188987 := bstep (se 1 (by rfl) ⟨891740, by rfl⟩ : syracuseStep 1188987 = 1783481) B1783481
theorem B17147051 : Blo 1188411 17147051 := bstep (se 1 (by rfl) ⟨12860288, by rfl⟩ : syracuseStep 17147051 = 25720577) B25720577
theorem B1189039 : Blo 1188411 1189039 := bstep (se 1 (by rfl) ⟨891779, by rfl⟩ : syracuseStep 1189039 = 1783559) B1783559
theorem B1189063 : Blo 1188411 1189063 := bstep (se 1 (by rfl) ⟨891797, by rfl⟩ : syracuseStep 1189063 = 1783595) B1783595
theorem B1189083 : Blo 1188411 1189083 := bstep (se 1 (by rfl) ⟨891812, by rfl⟩ : syracuseStep 1189083 = 1783625) B1783625
theorem B1189159 : Blo 1188411 1189159 := bstep (se 1 (by rfl) ⟨891869, by rfl⟩ : syracuseStep 1189159 = 1783739) B1783739
theorem B1189199 : Blo 1188411 1189199 := bstep (se 1 (by rfl) ⟨891899, by rfl⟩ : syracuseStep 1189199 = 1783799) B1783799
theorem B1189215 : Blo 1188411 1189215 := bstep (se 1 (by rfl) ⟨891911, by rfl⟩ : syracuseStep 1189215 = 1783823) B1783823
theorem B2008415 : Blo 1188411 2008415 := bstep (se 1 (by rfl) ⟨1506311, by rfl⟩ : syracuseStep 2008415 = 3012623) B3012623
theorem B1189243 : Blo 1188411 1189243 := bstep (se 1 (by rfl) ⟨891932, by rfl⟩ : syracuseStep 1189243 = 1783865) B1783865
theorem B6776237 : Blo 1188411 6776237 := bstep (se 3 (by rfl) ⟨1270544, by rfl⟩ : syracuseStep 6776237 = 2541089) B2541089
theorem B1189295 : Blo 1188411 1189295 := bstep (se 1 (by rfl) ⟨891971, by rfl⟩ : syracuseStep 1189295 = 1783943) B1783943
theorem B1189319 : Blo 1188411 1189319 := bstep (se 1 (by rfl) ⟨891989, by rfl⟩ : syracuseStep 1189319 = 1783979) B1783979
theorem B1189339 : Blo 1188411 1189339 := bstep (se 1 (by rfl) ⟨892004, by rfl⟩ : syracuseStep 1189339 = 1784009) B1784009
theorem B2033191 : Blo 1188411 2033191 := bstep (se 1 (by rfl) ⟨1524893, by rfl⟩ : syracuseStep 2033191 = 3049787) B3049787
theorem B1189415 : Blo 1188411 1189415 := bstep (se 1 (by rfl) ⟨892061, by rfl⟩ : syracuseStep 1189415 = 1784123) B1784123
theorem B4015655 : Blo 1188411 4015655 := bstep (se 1 (by rfl) ⟨3011741, by rfl⟩ : syracuseStep 4015655 = 6023483) B6023483
theorem B1189455 : Blo 1188411 1189455 := bstep (se 1 (by rfl) ⟨892091, by rfl⟩ : syracuseStep 1189455 = 1784183) B1784183
theorem B1189471 : Blo 1188411 1189471 := bstep (se 1 (by rfl) ⟨892103, by rfl⟩ : syracuseStep 1189471 = 1784207) B1784207
theorem B3384929 : Blo 1188411 3384929 := bstep (se 2 (by rfl) ⟨1269348, by rfl⟩ : syracuseStep 3384929 = 2538697) B2538697
theorem B1189499 : Blo 1188411 1189499 := bstep (se 1 (by rfl) ⟨892124, by rfl⟩ : syracuseStep 1189499 = 1784249) B1784249
theorem B4015763 : Blo 1188411 4015763 := bstep (se 1 (by rfl) ⟨3011822, by rfl⟩ : syracuseStep 4015763 = 6023645) B6023645
theorem B1189551 : Blo 1188411 1189551 := bstep (se 1 (by rfl) ⟨892163, by rfl⟩ : syracuseStep 1189551 = 1784327) B1784327
theorem B1189575 : Blo 1188411 1189575 := bstep (se 1 (by rfl) ⟨892181, by rfl⟩ : syracuseStep 1189575 = 1784363) B1784363
theorem B1189595 : Blo 1188411 1189595 := bstep (se 1 (by rfl) ⟨892196, by rfl⟩ : syracuseStep 1189595 = 1784393) B1784393
theorem B3008249 : Blo 1188411 3008249 := bstep (se 2 (by rfl) ⟨1128093, by rfl⟩ : syracuseStep 3008249 = 2256187) B2256187
theorem B1189671 : Blo 1188411 1189671 := bstep (se 1 (by rfl) ⟨892253, by rfl⟩ : syracuseStep 1189671 = 1784507) B1784507
theorem B1189711 : Blo 1188411 1189711 := bstep (se 1 (by rfl) ⟨892283, by rfl⟩ : syracuseStep 1189711 = 1784567) B1784567
theorem B37119833 : Blo 1188411 37119833 := bstep (se 2 (by rfl) ⟨13919937, by rfl⟩ : syracuseStep 37119833 = 27839875) B27839875
theorem B1189727 : Blo 1188411 1189727 := bstep (se 1 (by rfl) ⟨892295, by rfl⟩ : syracuseStep 1189727 = 1784591) B1784591
theorem B4015979 : Blo 1188411 4015979 := bstep (se 1 (by rfl) ⟨3011984, by rfl⟩ : syracuseStep 4015979 = 6023969) B6023969
theorem B1189755 : Blo 1188411 1189755 := bstep (se 1 (by rfl) ⟨892316, by rfl⟩ : syracuseStep 1189755 = 1784633) B1784633
theorem B4016033 : Blo 1188411 4016033 := bstep (se 2 (by rfl) ⟨1506012, by rfl⟩ : syracuseStep 4016033 = 3012025) B3012025
theorem B1189807 : Blo 1188411 1189807 := bstep (se 1 (by rfl) ⟨892355, by rfl⟩ : syracuseStep 1189807 = 1784711) B1784711
theorem B13543361 : Blo 1188411 13543361 := bstep (se 2 (by rfl) ⟨5078760, by rfl⟩ : syracuseStep 13543361 = 10157521) B10157521
theorem B1189831 : Blo 1188411 1189831 := bstep (se 1 (by rfl) ⟨892373, by rfl⟩ : syracuseStep 1189831 = 1784747) B1784747
theorem B1189851 : Blo 1188411 1189851 := bstep (se 1 (by rfl) ⟨892388, by rfl⟩ : syracuseStep 1189851 = 1784777) B1784777
theorem B1189927 : Blo 1188411 1189927 := bstep (se 1 (by rfl) ⟨892445, by rfl⟩ : syracuseStep 1189927 = 1784891) B1784891
theorem B1189967 : Blo 1188411 1189967 := bstep (se 1 (by rfl) ⟨892475, by rfl⟩ : syracuseStep 1189967 = 1784951) B1784951
theorem B1189983 : Blo 1188411 1189983 := bstep (se 1 (by rfl) ⟨892487, by rfl⟩ : syracuseStep 1189983 = 1784975) B1784975
theorem B1337467 : Blo 1188411 1337467 := bstep (se 1 (by rfl) ⟨1003100, by rfl⟩ : syracuseStep 1337467 = 2006201) B2006201
theorem B1190011 : Blo 1188411 1190011 := bstep (se 1 (by rfl) ⟨892508, by rfl⟩ : syracuseStep 1190011 = 1785017) B1785017
theorem B20334725 : Blo 1188411 20334725 := bstep (se 4 (by rfl) ⟨1906380, by rfl⟩ : syracuseStep 20334725 = 3812761) B3812761
theorem B3811481 : Blo 1188411 3811481 := bstep (se 2 (by rfl) ⟨1429305, by rfl⟩ : syracuseStep 3811481 = 2858611) B2858611
theorem B2541739 : Blo 1188411 2541739 := bstep (se 1 (by rfl) ⟨1906304, by rfl⟩ : syracuseStep 2541739 = 3812609) B3812609
theorem B1190063 : Blo 1188411 1190063 := bstep (se 1 (by rfl) ⟨892547, by rfl⟩ : syracuseStep 1190063 = 1785095) B1785095
theorem B1190087 : Blo 1188411 1190087 := bstep (se 1 (by rfl) ⟨892565, by rfl⟩ : syracuseStep 1190087 = 1785131) B1785131
theorem B1190107 : Blo 1188411 1190107 := bstep (se 1 (by rfl) ⟨892580, by rfl⟩ : syracuseStep 1190107 = 1785161) B1785161
theorem B1190183 : Blo 1188411 1190183 := bstep (se 1 (by rfl) ⟨892637, by rfl⟩ : syracuseStep 1190183 = 1785275) B1785275
theorem B9038141 : Blo 1188411 9038141 := bstep (se 3 (by rfl) ⟨1694651, by rfl⟩ : syracuseStep 9038141 = 3389303) B3389303
theorem B1190223 : Blo 1188411 1190223 := bstep (se 1 (by rfl) ⟨892667, by rfl⟩ : syracuseStep 1190223 = 1785335) B1785335
theorem B1190239 : Blo 1188411 1190239 := bstep (se 1 (by rfl) ⟨892679, by rfl⟩ : syracuseStep 1190239 = 1785359) B1785359
theorem B1190267 : Blo 1188411 1190267 := bstep (se 1 (by rfl) ⟨892700, by rfl⟩ : syracuseStep 1190267 = 1785401) B1785401
theorem B3008897 : Blo 1188411 3008897 := bstep (se 2 (by rfl) ⟨1128336, by rfl⟩ : syracuseStep 3008897 = 2256673) B2256673
theorem B1190319 : Blo 1188411 1190319 := bstep (se 1 (by rfl) ⟨892739, by rfl⟩ : syracuseStep 1190319 = 1785479) B1785479
theorem B1190343 : Blo 1188411 1190343 := bstep (se 1 (by rfl) ⟨892757, by rfl⟩ : syracuseStep 1190343 = 1785515) B1785515
theorem B1190363 : Blo 1188411 1190363 := bstep (se 1 (by rfl) ⟨892772, by rfl⟩ : syracuseStep 1190363 = 1785545) B1785545
theorem B13552109 : Blo 1188411 13552109 := bstep (se 3 (by rfl) ⟨2541020, by rfl⟩ : syracuseStep 13552109 = 5082041) B5082041
theorem B4016627 : Blo 1188411 4016627 := bstep (se 1 (by rfl) ⟨3012470, by rfl⟩ : syracuseStep 4016627 = 6024941) B6024941
theorem B6777377 : Blo 1188411 6777377 := bstep (se 2 (by rfl) ⟨2541516, by rfl⟩ : syracuseStep 6777377 = 5083033) B5083033
theorem B1337935 : Blo 1188411 1337935 := bstep (se 1 (by rfl) ⟨1003451, by rfl⟩ : syracuseStep 1337935 = 2006903) B2006903
theorem B9652871 : Blo 1188411 9652871 := bstep (se 1 (by rfl) ⟨7239653, by rfl⟩ : syracuseStep 9652871 = 14479307) B14479307
theorem B2714323 : Blo 1188411 2714323 := bstep (se 1 (by rfl) ⟨2035742, by rfl⟩ : syracuseStep 2714323 = 4071485) B4071485
theorem B8579843 : Blo 1188411 8579843 := bstep (se 1 (by rfl) ⟨6434882, by rfl⟩ : syracuseStep 8579843 = 12869765) B12869765
theorem B3214187 : Blo 1188411 3214187 := bstep (se 1 (by rfl) ⟨2410640, by rfl⟩ : syracuseStep 3214187 = 4821281) B4821281
theorem B1338331 : Blo 1188411 1338331 := bstep (se 1 (by rfl) ⟨1003748, by rfl⟩ : syracuseStep 1338331 = 2007497) B2007497
theorem B8580097 : Blo 1188411 8580097 := bstep (se 2 (by rfl) ⟨3217536, by rfl⟩ : syracuseStep 8580097 = 6435073) B6435073
theorem B4017167 : Blo 1188411 4017167 := bstep (se 1 (by rfl) ⟨3012875, by rfl⟩ : syracuseStep 4017167 = 6025751) B6025751
theorem B3386387 : Blo 1188411 3386387 := bstep (se 1 (by rfl) ⟨2539790, by rfl⟩ : syracuseStep 3386387 = 5079581) B5079581
theorem B2575379 : Blo 1188411 2575379 := bstep (se 1 (by rfl) ⟨1931534, by rfl⟩ : syracuseStep 2575379 = 3863069) B3863069
theorem B4574323 : Blo 1188411 4574323 := bstep (se 1 (by rfl) ⟨3430742, by rfl⟩ : syracuseStep 4574323 = 6861485) B6861485
theorem B5147819 : Blo 1188411 5147819 := bstep (se 1 (by rfl) ⟨3860864, by rfl⟩ : syracuseStep 5147819 = 7721729) B7721729
theorem B3009707 : Blo 1188411 3009707 := bstep (se 1 (by rfl) ⟨2257280, by rfl⟩ : syracuseStep 3009707 = 4514561) B4514561
theorem B12201155 : Blo 1188411 12201155 := bstep (se 1 (by rfl) ⟨9150866, by rfl⟩ : syracuseStep 12201155 = 18301733) B18301733
theorem B9030851 : Blo 1188411 9030851 := bstep (se 1 (by rfl) ⟨6773138, by rfl⟩ : syracuseStep 9030851 = 13546277) B13546277
theorem B2674025 : Blo 1188411 2674025 := bstep (se 2 (by rfl) ⟨1002759, by rfl⟩ : syracuseStep 2674025 = 2005519) B2005519
theorem B20589997 : Blo 1188411 20589997 := bstep (se 3 (by rfl) ⟨3860624, by rfl⟩ : syracuseStep 20589997 = 7721249) B7721249
theorem B2289071 : Blo 1188411 2289071 := bstep (se 1 (by rfl) ⟨1716803, by rfl⟩ : syracuseStep 2289071 = 3433607) B3433607
theorem B1338799 : Blo 1188411 1338799 := bstep (se 1 (by rfl) ⟨1004099, by rfl⟩ : syracuseStep 1338799 = 2008199) B2008199
theorem B3386843 : Blo 1188411 3386843 := bstep (se 1 (by rfl) ⟨2540132, by rfl⟩ : syracuseStep 3386843 = 5080265) B5080265
theorem B4820467 : Blo 1188411 4820467 := bstep (se 1 (by rfl) ⟨3615350, by rfl⟩ : syracuseStep 4820467 = 7230701) B7230701
theorem B11423521 : Blo 1188411 11423521 := bstep (se 2 (by rfl) ⟨4283820, by rfl⟩ : syracuseStep 11423521 = 8567641) B8567641
theorem B34312085 : Blo 1188411 34312085 := bstep (se 6 (by rfl) ⟨804189, by rfl⟩ : syracuseStep 34312085 = 1608379) B1608379
theorem B2674619 : Blo 1188411 2674619 := bstep (se 1 (by rfl) ⟨2005964, by rfl⟩ : syracuseStep 2674619 = 4011929) B4011929
theorem B5083067 : Blo 1188411 5083067 := bstep (se 1 (by rfl) ⟨3812300, by rfl⟩ : syracuseStep 5083067 = 7624601) B7624601
theorem B3010567 : Blo 1188411 3010567 := bstep (se 1 (by rfl) ⟨2257925, by rfl⟩ : syracuseStep 3010567 = 4515851) B4515851
theorem B2674745 : Blo 1188411 2674745 := bstep (se 2 (by rfl) ⟨1003029, by rfl⟩ : syracuseStep 2674745 = 2006059) B2006059
theorem B4575311 : Blo 1188411 4575311 := bstep (se 1 (by rfl) ⟨3431483, by rfl⟩ : syracuseStep 4575311 = 6862967) B6862967
theorem B9777469 : Blo 1188411 9777469 := bstep (se 3 (by rfl) ⟨1833275, by rfl⟩ : syracuseStep 9777469 = 3666551) B3666551
theorem B2675087 : Blo 1188411 2675087 := bstep (se 1 (by rfl) ⟨2006315, by rfl⟩ : syracuseStep 2675087 = 4012631) B4012631
theorem B2478511 : Blo 1188411 2478511 := bstep (se 1 (by rfl) ⟨1858883, by rfl⟩ : syracuseStep 2478511 = 3717767) B3717767
theorem B3011195 : Blo 1188411 3011195 := bstep (se 1 (by rfl) ⟨2258396, by rfl⟩ : syracuseStep 3011195 = 4516793) B4516793
theorem B6025913 : Blo 1188411 6025913 := bstep (se 2 (by rfl) ⟨2259717, by rfl⟩ : syracuseStep 6025913 = 4519435) B4519435
theorem B2257607 : Blo 1188411 2257607 := bstep (se 1 (by rfl) ⟨1693205, by rfl⟩ : syracuseStep 2257607 = 3386411) B3386411
theorem B3912403 : Blo 1188411 3912403 := bstep (se 1 (by rfl) ⟨2934302, by rfl⟩ : syracuseStep 3912403 = 5868605) B5868605
theorem B2675411 : Blo 1188411 2675411 := bstep (se 1 (by rfl) ⟨2006558, by rfl⟩ : syracuseStep 2675411 = 4013117) B4013117
theorem B20886227 : Blo 1188411 20886227 := bstep (se 1 (by rfl) ⟨15664670, by rfl⟩ : syracuseStep 20886227 = 31329341) B31329341
theorem B1905401 : Blo 1188411 1905401 := bstep (se 2 (by rfl) ⟨714525, by rfl⟩ : syracuseStep 1905401 = 1429051) B1429051
theorem B4289273 : Blo 1188411 4289273 := bstep (se 2 (by rfl) ⟨1608477, by rfl⟩ : syracuseStep 4289273 = 3216955) B3216955
theorem B1782623 : Blo 1188411 1782623 := bstep (se 1 (by rfl) ⟨1336967, by rfl⟩ : syracuseStep 1782623 = 2673935) B2673935
theorem B1782635 : Blo 1188411 1782635 := bstep (se 1 (by rfl) ⟨1336976, by rfl⟩ : syracuseStep 1782635 = 2673953) B2673953
theorem B3011489 : Blo 1188411 3011489 := bstep (se 2 (by rfl) ⟨1129308, by rfl⟩ : syracuseStep 3011489 = 2258617) B2258617
theorem B6017975 : Blo 1188411 6017975 := bstep (se 1 (by rfl) ⟨4513481, by rfl⟩ : syracuseStep 6017975 = 9026963) B9026963
theorem B4011065 : Blo 1188411 4011065 := bstep (se 2 (by rfl) ⟨1504149, by rfl⟩ : syracuseStep 4011065 = 3008299) B3008299
theorem B1782863 : Blo 1188411 1782863 := bstep (se 1 (by rfl) ⟨1337147, by rfl⟩ : syracuseStep 1782863 = 2674295) B2674295
theorem B1782983 : Blo 1188411 1782983 := bstep (se 1 (by rfl) ⟨1337237, by rfl⟩ : syracuseStep 1782983 = 2674475) B2674475
theorem B2258131 : Blo 1188411 2258131 := bstep (se 1 (by rfl) ⟨1693598, by rfl⟩ : syracuseStep 2258131 = 3387197) B3387197
theorem B13726991 : Blo 1188411 13726991 := bstep (se 1 (by rfl) ⟨10295243, by rfl⟩ : syracuseStep 13726991 = 20590487) B20590487
theorem B1783145 : Blo 1188411 1783145 := bstep (se 2 (by rfl) ⟨668679, by rfl⟩ : syracuseStep 1783145 = 1337359) B1337359
theorem B4011389 : Blo 1188411 4011389 := bstep (se 3 (by rfl) ⟨752135, by rfl⟩ : syracuseStep 4011389 = 1504271) B1504271
theorem B12547493 : Blo 1188411 12547493 := bstep (se 4 (by rfl) ⟨1176327, by rfl⟩ : syracuseStep 12547493 = 2352655) B2352655
theorem B2258351 : Blo 1188411 2258351 := bstep (se 1 (by rfl) ⟨1693763, by rfl⟩ : syracuseStep 2258351 = 3387527) B3387527
theorem B1783223 : Blo 1188411 1783223 := bstep (se 1 (by rfl) ⟨1337417, by rfl⟩ : syracuseStep 1783223 = 2674835) B2674835
theorem B8697289 : Blo 1188411 8697289 := bstep (se 2 (by rfl) ⟨3261483, by rfl⟩ : syracuseStep 8697289 = 6522967) B6522967
theorem B1783259 : Blo 1188411 1783259 := bstep (se 1 (by rfl) ⟨1337444, by rfl⟩ : syracuseStep 1783259 = 2674889) B2674889
theorem B2676347 : Blo 1188411 2676347 := bstep (se 1 (by rfl) ⟨2007260, by rfl⟩ : syracuseStep 2676347 = 4014521) B4014521
theorem B4011659 : Blo 1188411 4011659 := bstep (se 1 (by rfl) ⟨3008744, by rfl⟩ : syracuseStep 4011659 = 6017489) B6017489
theorem B5076695 : Blo 1188411 5076695 := bstep (se 1 (by rfl) ⟨3807521, by rfl⟩ : syracuseStep 5076695 = 7615043) B7615043
theorem B9148153 : Blo 1188411 9148153 := bstep (se 2 (by rfl) ⟨3430557, by rfl⟩ : syracuseStep 9148153 = 6861115) B6861115
theorem B1693433 : Blo 1188411 1693433 := bstep (se 2 (by rfl) ⟨635037, by rfl⟩ : syracuseStep 1693433 = 1270075) B1270075
theorem B2676473 : Blo 1188411 2676473 := bstep (se 2 (by rfl) ⟨1003677, by rfl⟩ : syracuseStep 2676473 = 2007355) B2007355
theorem B4519709 : Blo 1188411 4519709 := bstep (se 3 (by rfl) ⟨847445, by rfl⟩ : syracuseStep 4519709 = 1694891) B1694891
theorem B6428483 : Blo 1188411 6428483 := bstep (se 1 (by rfl) ⟨4821362, by rfl⟩ : syracuseStep 6428483 = 9642725) B9642725
theorem B2258761 : Blo 1188411 2258761 := bstep (se 2 (by rfl) ⟨847035, by rfl⟩ : syracuseStep 2258761 = 1694071) B1694071
theorem B1783727 : Blo 1188411 1783727 := bstep (se 1 (by rfl) ⟨1337795, by rfl⟩ : syracuseStep 1783727 = 2675591) B2675591
theorem B1505243 : Blo 1188411 1505243 := bstep (se 1 (by rfl) ⟨1128932, by rfl⟩ : syracuseStep 1505243 = 2257865) B2257865
theorem B12851207 : Blo 1188411 12851207 := bstep (se 1 (by rfl) ⟨9638405, by rfl⟩ : syracuseStep 12851207 = 19276811) B19276811
theorem B2676743 : Blo 1188411 2676743 := bstep (se 1 (by rfl) ⟨2007557, by rfl⟩ : syracuseStep 2676743 = 4015115) B4015115
theorem B1783817 : Blo 1188411 1783817 := bstep (se 2 (by rfl) ⟨668931, by rfl⟩ : syracuseStep 1783817 = 1337863) B1337863
theorem B1783847 : Blo 1188411 1783847 := bstep (se 1 (by rfl) ⟨1337885, by rfl⟩ : syracuseStep 1783847 = 2675771) B2675771
theorem B2676815 : Blo 1188411 2676815 := bstep (se 1 (by rfl) ⟨2007611, by rfl⟩ : syracuseStep 2676815 = 4015223) B4015223
theorem B1783931 : Blo 1188411 1783931 := bstep (se 1 (by rfl) ⟨1337948, by rfl⟩ : syracuseStep 1783931 = 2675897) B2675897
theorem B1784057 : Blo 1188411 1784057 := bstep (se 2 (by rfl) ⟨669021, by rfl⟩ : syracuseStep 1784057 = 1338043) B1338043
theorem B7624961 : Blo 1188411 7624961 := bstep (se 2 (by rfl) ⟨2859360, by rfl⟩ : syracuseStep 7624961 = 5718721) B5718721
theorem B6773003 : Blo 1188411 6773003 := bstep (se 1 (by rfl) ⟨5079752, by rfl⟩ : syracuseStep 6773003 = 10159505) B10159505
theorem B1784159 : Blo 1188411 1784159 := bstep (se 1 (by rfl) ⟨1338119, by rfl⟩ : syracuseStep 1784159 = 2676239) B2676239
theorem B6019433 : Blo 1188411 6019433 := bstep (se 2 (by rfl) ⟨2257287, by rfl⟩ : syracuseStep 6019433 = 4514575) B4514575
theorem B7936361 : Blo 1188411 7936361 := bstep (se 2 (by rfl) ⟨2976135, by rfl⟩ : syracuseStep 7936361 = 5952271) B5952271
theorem B1784171 : Blo 1188411 1784171 := bstep (se 1 (by rfl) ⟨1338128, by rfl⟩ : syracuseStep 1784171 = 2676257) B2676257
theorem B1505719 : Blo 1188411 1505719 := bstep (se 1 (by rfl) ⟨1129289, by rfl⟩ : syracuseStep 1505719 = 2258579) B2258579
theorem B2677211 : Blo 1188411 2677211 := bstep (se 1 (by rfl) ⟨2007908, by rfl⟩ : syracuseStep 2677211 = 4015817) B4015817
theorem B4012577 : Blo 1188411 4012577 := bstep (se 2 (by rfl) ⟨1504716, by rfl⟩ : syracuseStep 4012577 = 3009433) B3009433
theorem B3865121 : Blo 1188411 3865121 := bstep (se 2 (by rfl) ⟨1449420, by rfl⟩ : syracuseStep 3865121 = 2898841) B2898841
theorem B3619367 : Blo 1188411 3619367 := bstep (se 1 (by rfl) ⟨2714525, by rfl⟩ : syracuseStep 3619367 = 5429051) B5429051
theorem B3013159 : Blo 1188411 3013159 := bstep (se 1 (by rfl) ⟨2259869, by rfl⟩ : syracuseStep 3013159 = 4519739) B4519739
theorem B1784399 : Blo 1188411 1784399 := bstep (se 1 (by rfl) ⟨1338299, by rfl⟩ : syracuseStep 1784399 = 2676599) B2676599
theorem B1694287 : Blo 1188411 1694287 := bstep (se 1 (by rfl) ⟨1270715, by rfl⟩ : syracuseStep 1694287 = 2541431) B2541431
theorem B2005627 : Blo 1188411 2005627 := bstep (se 1 (by rfl) ⟨1504220, by rfl⟩ : syracuseStep 2005627 = 3008441) B3008441
theorem B1784519 : Blo 1188411 1784519 := bstep (se 1 (by rfl) ⟨1338389, by rfl⟩ : syracuseStep 1784519 = 2676779) B2676779
theorem B4012793 : Blo 1188411 4012793 := bstep (se 2 (by rfl) ⟨1504797, by rfl⟩ : syracuseStep 4012793 = 3009595) B3009595
theorem B7625501 : Blo 1188411 7625501 := bstep (se 3 (by rfl) ⟨1429781, by rfl⟩ : syracuseStep 7625501 = 2859563) B2859563
theorem B3808073 : Blo 1188411 3808073 := bstep (se 2 (by rfl) ⟨1428027, by rfl⟩ : syracuseStep 3808073 = 2856055) B2856055
theorem B1784681 : Blo 1188411 1784681 := bstep (se 2 (by rfl) ⟨669255, by rfl⟩ : syracuseStep 1784681 = 1338511) B1338511
theorem B4512631 : Blo 1188411 4512631 := bstep (se 1 (by rfl) ⟨3384473, by rfl⟩ : syracuseStep 4512631 = 6768947) B6768947
theorem B2677679 : Blo 1188411 2677679 := bstep (se 1 (by rfl) ⟨2008259, by rfl⟩ : syracuseStep 2677679 = 4016519) B4016519
theorem B1784759 : Blo 1188411 1784759 := bstep (se 1 (by rfl) ⟨1338569, by rfl⟩ : syracuseStep 1784759 = 2677139) B2677139
theorem B1784795 : Blo 1188411 1784795 := bstep (se 1 (by rfl) ⟨1338596, by rfl⟩ : syracuseStep 1784795 = 2677193) B2677193
theorem B4013063 : Blo 1188411 4013063 := bstep (se 1 (by rfl) ⟨3009797, by rfl⟩ : syracuseStep 4013063 = 6019595) B6019595
theorem B2538553 : Blo 1188411 2538553 := bstep (se 2 (by rfl) ⟨951957, by rfl⟩ : syracuseStep 2538553 = 1903915) B1903915
theorem B28941391 : Blo 1188411 28941391 := bstep (se 1 (by rfl) ⟨21706043, by rfl⟩ : syracuseStep 28941391 = 43412087) B43412087
theorem B4013171 : Blo 1188411 4013171 := bstep (se 1 (by rfl) ⟨3009878, by rfl⟩ : syracuseStep 4013171 = 6019757) B6019757
theorem B2677931 : Blo 1188411 2677931 := bstep (se 1 (by rfl) ⟨2008448, by rfl⟩ : syracuseStep 2677931 = 4016897) B4016897
theorem B15244483 : Blo 1188411 15244483 := bstep (se 1 (by rfl) ⟨11433362, by rfl⟩ : syracuseStep 15244483 = 22866725) B22866725
theorem B4013441 : Blo 1188411 4013441 := bstep (se 2 (by rfl) ⟨1505040, by rfl⟩ : syracuseStep 4013441 = 3010081) B3010081
theorem B1785263 : Blo 1188411 1785263 := bstep (se 1 (by rfl) ⟨1338947, by rfl⟩ : syracuseStep 1785263 = 2677895) B2677895
theorem B2006491 : Blo 1188411 2006491 := bstep (se 1 (by rfl) ⟨1504868, by rfl⟩ : syracuseStep 2006491 = 3009737) B3009737
theorem B1785353 : Blo 1188411 1785353 := bstep (se 2 (by rfl) ⟨669507, by rfl⟩ : syracuseStep 1785353 = 1339015) B1339015
theorem B1785383 : Blo 1188411 1785383 := bstep (se 1 (by rfl) ⟨1339037, by rfl⟩ : syracuseStep 1785383 = 2678075) B2678075
theorem B1785467 : Blo 1188411 1785467 := bstep (se 1 (by rfl) ⟨1339100, by rfl⟩ : syracuseStep 1785467 = 2678201) B2678201
theorem B3808957 : Blo 1188411 3808957 := bstep (se 3 (by rfl) ⟨714179, by rfl⟩ : syracuseStep 3808957 = 1428359) B1428359
theorem B6774461 : Blo 1188411 6774461 := bstep (se 3 (by rfl) ⟨1270211, by rfl⟩ : syracuseStep 6774461 = 2540423) B2540423
theorem B4824785 : Blo 1188411 4824785 := bstep (se 2 (by rfl) ⟨1809294, by rfl⟩ : syracuseStep 4824785 = 3618589) B3618589
theorem B1785593 : Blo 1188411 1785593 := bstep (se 2 (by rfl) ⟨669597, by rfl⟩ : syracuseStep 1785593 = 1339195) B1339195
theorem B4513603 : Blo 1188411 4513603 := bstep (se 1 (by rfl) ⟨3385202, by rfl⟩ : syracuseStep 4513603 = 6770405) B6770405
theorem B4014089 : Blo 1188411 4014089 := bstep (se 2 (by rfl) ⟨1505283, by rfl⟩ : syracuseStep 4014089 = 3010567) B3010567
theorem B9036197 : Blo 1188411 9036197 := bstep (se 4 (by rfl) ⟨847143, by rfl⟩ : syracuseStep 9036197 = 1694287) B1694287
theorem B2007463 : Blo 1188411 2007463 := bstep (se 1 (by rfl) ⟨1505597, by rfl⟩ : syracuseStep 2007463 = 3011195) B3011195
theorem B2859515 : Blo 1188411 2859515 := bstep (se 1 (by rfl) ⟨2144636, by rfl⟩ : syracuseStep 2859515 = 4289273) B4289273
theorem B1188415 : Blo 1188411 1188415 := bstep (se 1 (by rfl) ⟨891311, by rfl⟩ : syracuseStep 1188415 = 1782623) B1782623
theorem B1188423 : Blo 1188411 1188423 := bstep (se 1 (by rfl) ⟨891317, by rfl⟩ : syracuseStep 1188423 = 1782635) B1782635
theorem B39617095 : Blo 1188411 39617095 := bstep (se 1 (by rfl) ⟨29712821, by rfl⟩ : syracuseStep 39617095 = 59425643) B59425643
theorem B7619143 : Blo 1188411 7619143 := bstep (se 1 (by rfl) ⟨5714357, by rfl⟩ : syracuseStep 7619143 = 11428715) B11428715
theorem B2007625 : Blo 1188411 2007625 := bstep (se 2 (by rfl) ⟨752859, by rfl⟩ : syracuseStep 2007625 = 1505719) B1505719
theorem B24396389 : Blo 1188411 24396389 := bstep (se 4 (by rfl) ⟨2287161, by rfl⟩ : syracuseStep 24396389 = 4574323) B4574323
theorem B2007659 : Blo 1188411 2007659 := bstep (se 1 (by rfl) ⟨1505744, by rfl⟩ : syracuseStep 2007659 = 3011489) B3011489
theorem B22921931 : Blo 1188411 22921931 := bstep (se 1 (by rfl) ⟨17191448, by rfl⟩ : syracuseStep 22921931 = 34382897) B34382897
theorem B1188575 : Blo 1188411 1188575 := bstep (se 1 (by rfl) ⟨891431, by rfl⟩ : syracuseStep 1188575 = 1782863) B1782863
theorem B1188655 : Blo 1188411 1188655 := bstep (se 1 (by rfl) ⟨891491, by rfl⟩ : syracuseStep 1188655 = 1782983) B1782983
theorem B9151327 : Blo 1188411 9151327 := bstep (se 1 (by rfl) ⟨6863495, by rfl⟩ : syracuseStep 9151327 = 13726991) B13726991
theorem B1188763 : Blo 1188411 1188763 := bstep (se 1 (by rfl) ⟨891572, by rfl⟩ : syracuseStep 1188763 = 1783145) B1783145
theorem B8364995 : Blo 1188411 8364995 := bstep (se 1 (by rfl) ⟨6273746, by rfl⟩ : syracuseStep 8364995 = 12547493) B12547493
theorem B1188815 : Blo 1188411 1188815 := bstep (se 1 (by rfl) ⟨891611, by rfl⟩ : syracuseStep 1188815 = 1783223) B1783223
theorem B1188839 : Blo 1188411 1188839 := bstep (se 1 (by rfl) ⟨891629, by rfl⟩ : syracuseStep 1188839 = 1783259) B1783259
theorem B3384463 : Blo 1188411 3384463 := bstep (se 1 (by rfl) ⟨2538347, by rfl⟩ : syracuseStep 3384463 = 5076695) B5076695
theorem B4285655 : Blo 1188411 4285655 := bstep (se 1 (by rfl) ⟨3214241, by rfl⟩ : syracuseStep 4285655 = 6428483) B6428483
theorem B1189151 : Blo 1188411 1189151 := bstep (se 1 (by rfl) ⟨891863, by rfl⟩ : syracuseStep 1189151 = 1783727) B1783727
theorem B9028907 : Blo 1188411 9028907 := bstep (se 1 (by rfl) ⟨6771680, by rfl⟩ : syracuseStep 9028907 = 13543361) B13543361
theorem B1189211 : Blo 1188411 1189211 := bstep (se 1 (by rfl) ⟨891908, by rfl⟩ : syracuseStep 1189211 = 1783817) B1783817
theorem B1189231 : Blo 1188411 1189231 := bstep (se 1 (by rfl) ⟨891923, by rfl⟩ : syracuseStep 1189231 = 1783847) B1783847
theorem B3384737 : Blo 1188411 3384737 := bstep (se 2 (by rfl) ⟨1269276, by rfl⟩ : syracuseStep 3384737 = 2538553) B2538553
theorem B1189287 : Blo 1188411 1189287 := bstep (se 1 (by rfl) ⟨891965, by rfl⟩ : syracuseStep 1189287 = 1783931) B1783931
theorem B2540987 : Blo 1188411 2540987 := bstep (se 1 (by rfl) ⟨1905740, by rfl⟩ : syracuseStep 2540987 = 3811481) B3811481
theorem B1189371 : Blo 1188411 1189371 := bstep (se 1 (by rfl) ⟨892028, by rfl⟩ : syracuseStep 1189371 = 1784057) B1784057
theorem B4515335 : Blo 1188411 4515335 := bstep (se 1 (by rfl) ⟨3386501, by rfl⟩ : syracuseStep 4515335 = 6773003) B6773003
theorem B1189439 : Blo 1188411 1189439 := bstep (se 1 (by rfl) ⟨892079, by rfl⟩ : syracuseStep 1189439 = 1784159) B1784159
theorem B1189447 : Blo 1188411 1189447 := bstep (se 1 (by rfl) ⟨892085, by rfl⟩ : syracuseStep 1189447 = 1784171) B1784171
theorem B20325977 : Blo 1188411 20325977 := bstep (se 2 (by rfl) ⟨7622241, by rfl⟩ : syracuseStep 20325977 = 15244483) B15244483
theorem B25740989 : Blo 1188411 25740989 := bstep (se 3 (by rfl) ⟨4826435, by rfl⟩ : syracuseStep 25740989 = 9652871) B9652871
theorem B1189599 : Blo 1188411 1189599 := bstep (se 1 (by rfl) ⟨892199, by rfl⟩ : syracuseStep 1189599 = 1784399) B1784399
theorem B1189679 : Blo 1188411 1189679 := bstep (se 1 (by rfl) ⟨892259, by rfl⟩ : syracuseStep 1189679 = 1784519) B1784519
theorem B5719895 : Blo 1188411 5719895 := bstep (se 1 (by rfl) ⟨4289921, by rfl⟩ : syracuseStep 5719895 = 8579843) B8579843
theorem B27453329 : Blo 1188411 27453329 := bstep (se 2 (by rfl) ⟨10294998, by rfl⟩ : syracuseStep 27453329 = 20589997) B20589997
theorem B1189787 : Blo 1188411 1189787 := bstep (se 1 (by rfl) ⟨892340, by rfl⟩ : syracuseStep 1189787 = 1784681) B1784681
theorem B1189839 : Blo 1188411 1189839 := bstep (se 1 (by rfl) ⟨892379, by rfl⟩ : syracuseStep 1189839 = 1784759) B1784759
theorem B1189863 : Blo 1188411 1189863 := bstep (se 1 (by rfl) ⟨892397, by rfl⟩ : syracuseStep 1189863 = 1784795) B1784795
theorem B4515821 : Blo 1188411 4515821 := bstep (se 3 (by rfl) ⟨846716, by rfl⟩ : syracuseStep 4515821 = 1693433) B1693433
theorem B5081069 : Blo 1188411 5081069 := bstep (se 3 (by rfl) ⟨952700, by rfl⟩ : syracuseStep 5081069 = 1905401) B1905401
theorem B1526047 : Blo 1188411 1526047 := bstep (se 1 (by rfl) ⟨1144535, by rfl⟩ : syracuseStep 1526047 = 2289071) B2289071
theorem B1190175 : Blo 1188411 1190175 := bstep (se 1 (by rfl) ⟨892631, by rfl⟩ : syracuseStep 1190175 = 1785263) B1785263
theorem B1190235 : Blo 1188411 1190235 := bstep (se 1 (by rfl) ⟨892676, by rfl⟩ : syracuseStep 1190235 = 1785353) B1785353
theorem B1190255 : Blo 1188411 1190255 := bstep (se 1 (by rfl) ⟨892691, by rfl⟩ : syracuseStep 1190255 = 1785383) B1785383
theorem B15231361 : Blo 1188411 15231361 := bstep (se 2 (by rfl) ⟨5711760, by rfl⟩ : syracuseStep 15231361 = 11423521) B11423521
theorem B1190311 : Blo 1188411 1190311 := bstep (se 1 (by rfl) ⟨892733, by rfl⟩ : syracuseStep 1190311 = 1785467) B1785467
theorem B4516307 : Blo 1188411 4516307 := bstep (se 1 (by rfl) ⟨3387230, by rfl⟩ : syracuseStep 4516307 = 6774461) B6774461
theorem B1190395 : Blo 1188411 1190395 := bstep (se 1 (by rfl) ⟨892796, by rfl⟩ : syracuseStep 1190395 = 1785593) B1785593
theorem B22874723 : Blo 1188411 22874723 := bstep (se 1 (by rfl) ⟨17156042, by rfl⟩ : syracuseStep 22874723 = 34312085) B34312085
theorem B9030365 : Blo 1188411 9030365 := bstep (se 3 (by rfl) ⟨1693193, by rfl⟩ : syracuseStep 9030365 = 3386387) B3386387
theorem B3050207 : Blo 1188411 3050207 := bstep (se 1 (by rfl) ⟨2287655, by rfl⟩ : syracuseStep 3050207 = 4575311) B4575311
theorem B1338079 : Blo 1188411 1338079 := bstep (se 1 (by rfl) ⟨1003559, by rfl⟩ : syracuseStep 1338079 = 2007119) B2007119
theorem B3009271 : Blo 1188411 3009271 := bstep (se 1 (by rfl) ⟨2256953, by rfl⟩ : syracuseStep 3009271 = 4513907) B4513907
theorem B3009575 : Blo 1188411 3009575 := bstep (se 1 (by rfl) ⟨2257181, by rfl⟩ : syracuseStep 3009575 = 4514363) B4514363
theorem B13036625 : Blo 1188411 13036625 := bstep (se 2 (by rfl) ⟨4888734, by rfl⟩ : syracuseStep 13036625 = 9777469) B9777469
theorem B4017275 : Blo 1188411 4017275 := bstep (se 1 (by rfl) ⟨3012956, by rfl⟩ : syracuseStep 4017275 = 6025913) B6025913
theorem B3304681 : Blo 1188411 3304681 := bstep (se 2 (by rfl) ⟨1239255, by rfl⟩ : syracuseStep 3304681 = 2478511) B2478511
theorem B1338655 : Blo 1188411 1338655 := bstep (se 1 (by rfl) ⟨1003991, by rfl⟩ : syracuseStep 1338655 = 2007983) B2007983
theorem B13544819 : Blo 1188411 13544819 := bstep (se 1 (by rfl) ⟨10158614, by rfl⟩ : syracuseStep 13544819 = 20317229) B20317229
theorem B2674043 : Blo 1188411 2674043 := bstep (se 1 (by rfl) ⟨2005532, by rfl⟩ : syracuseStep 2674043 = 4011065) B4011065
theorem B4017545 : Blo 1188411 4017545 := bstep (se 2 (by rfl) ⟨1506579, by rfl⟩ : syracuseStep 4017545 = 3013159) B3013159
theorem B11431367 : Blo 1188411 11431367 := bstep (se 1 (by rfl) ⟨8573525, by rfl⟩ : syracuseStep 11431367 = 17147051) B17147051
theorem B2674169 : Blo 1188411 2674169 := bstep (se 2 (by rfl) ⟨1002813, by rfl⟩ : syracuseStep 2674169 = 2005627) B2005627
theorem B1338943 : Blo 1188411 1338943 := bstep (se 1 (by rfl) ⟨1004207, by rfl⟩ : syracuseStep 1338943 = 2008415) B2008415
theorem B2674259 : Blo 1188411 2674259 := bstep (se 1 (by rfl) ⟨2005694, by rfl⟩ : syracuseStep 2674259 = 4011389) B4011389
theorem B4517491 : Blo 1188411 4517491 := bstep (se 1 (by rfl) ⟨3388118, by rfl⟩ : syracuseStep 4517491 = 6776237) B6776237
theorem B2674439 : Blo 1188411 2674439 := bstep (se 1 (by rfl) ⟨2005829, by rfl⟩ : syracuseStep 2674439 = 4011659) B4011659
theorem B6016841 : Blo 1188411 6016841 := bstep (se 2 (by rfl) ⟨2256315, by rfl⟩ : syracuseStep 6016841 = 4512631) B4512631
theorem B11440129 : Blo 1188411 11440129 := bstep (se 2 (by rfl) ⟨4290048, by rfl⟩ : syracuseStep 11440129 = 8580097) B8580097
theorem B38588521 : Blo 1188411 38588521 := bstep (se 2 (by rfl) ⟨14470695, by rfl⟩ : syracuseStep 38588521 = 28941391) B28941391
theorem B5083307 : Blo 1188411 5083307 := bstep (se 1 (by rfl) ⟨3812480, by rfl⟩ : syracuseStep 5083307 = 7624961) B7624961
theorem B6025427 : Blo 1188411 6025427 := bstep (se 1 (by rfl) ⟨4519070, by rfl⟩ : syracuseStep 6025427 = 9038141) B9038141
theorem B3010841 : Blo 1188411 3010841 := bstep (se 2 (by rfl) ⟨1129065, by rfl⟩ : syracuseStep 3010841 = 2258131) B2258131
theorem B2675051 : Blo 1188411 2675051 := bstep (se 1 (by rfl) ⟨2006288, by rfl⟩ : syracuseStep 2675051 = 4012577) B4012577
theorem B4518251 : Blo 1188411 4518251 := bstep (se 1 (by rfl) ⟨3388688, by rfl⟩ : syracuseStep 4518251 = 6777377) B6777377
theorem B2576747 : Blo 1188411 2576747 := bstep (se 1 (by rfl) ⟨1932560, by rfl⟩ : syracuseStep 2576747 = 3865121) B3865121
theorem B2412911 : Blo 1188411 2412911 := bstep (se 1 (by rfl) ⟨1809683, by rfl⟩ : syracuseStep 2412911 = 3619367) B3619367
theorem B2675195 : Blo 1188411 2675195 := bstep (se 1 (by rfl) ⟨2006396, by rfl⟩ : syracuseStep 2675195 = 4012793) B4012793
theorem B5083667 : Blo 1188411 5083667 := bstep (se 1 (by rfl) ⟨3812750, by rfl⟩ : syracuseStep 5083667 = 7625501) B7625501
theorem B2142791 : Blo 1188411 2142791 := bstep (se 1 (by rfl) ⟨1607093, by rfl⟩ : syracuseStep 2142791 = 3214187) B3214187
theorem B11596385 : Blo 1188411 11596385 := bstep (se 2 (by rfl) ⟨4348644, by rfl⟩ : syracuseStep 11596385 = 8697289) B8697289
theorem B2675321 : Blo 1188411 2675321 := bstep (se 2 (by rfl) ⟨1003245, by rfl⟩ : syracuseStep 2675321 = 2006491) B2006491
theorem B6427289 : Blo 1188411 6427289 := bstep (se 2 (by rfl) ⟨2410233, by rfl⟩ : syracuseStep 6427289 = 4820467) B4820467
theorem B2675375 : Blo 1188411 2675375 := bstep (se 1 (by rfl) ⟨2006531, by rfl⟩ : syracuseStep 2675375 = 4013063) B4013063
theorem B1716919 : Blo 1188411 1716919 := bstep (se 1 (by rfl) ⟨1287689, by rfl⟩ : syracuseStep 1716919 = 2575379) B2575379
theorem B2675447 : Blo 1188411 2675447 := bstep (se 1 (by rfl) ⟨2006585, by rfl⟩ : syracuseStep 2675447 = 4013171) B4013171
theorem B1782683 : Blo 1188411 1782683 := bstep (se 1 (by rfl) ⟨1337012, by rfl⟩ : syracuseStep 1782683 = 2674025) B2674025
theorem B2675627 : Blo 1188411 2675627 := bstep (se 1 (by rfl) ⟨2006720, by rfl⟩ : syracuseStep 2675627 = 4013441) B4013441
theorem B2257895 : Blo 1188411 2257895 := bstep (se 1 (by rfl) ⟨1693421, by rfl⟩ : syracuseStep 2257895 = 3386843) B3386843
theorem B6018137 : Blo 1188411 6018137 := bstep (se 2 (by rfl) ⟨2256801, by rfl⟩ : syracuseStep 6018137 = 4513603) B4513603
theorem B3011681 : Blo 1188411 3011681 := bstep (se 2 (by rfl) ⟨1129380, by rfl⟩ : syracuseStep 3011681 = 2258761) B2258761
theorem B3216523 : Blo 1188411 3216523 := bstep (se 1 (by rfl) ⟨2412392, by rfl⟩ : syracuseStep 3216523 = 4824785) B4824785
theorem B1783079 : Blo 1188411 1783079 := bstep (se 1 (by rfl) ⟨1337309, by rfl⟩ : syracuseStep 1783079 = 2674619) B2674619
theorem B3388711 : Blo 1188411 3388711 := bstep (se 1 (by rfl) ⟨2541533, by rfl⟩ : syracuseStep 3388711 = 5083067) B5083067
theorem B12539225 : Blo 1188411 12539225 := bstep (se 2 (by rfl) ⟨4702209, by rfl⟩ : syracuseStep 12539225 = 9404419) B9404419
theorem B1783163 : Blo 1188411 1783163 := bstep (se 1 (by rfl) ⟨1337372, by rfl⟩ : syracuseStep 1783163 = 2674745) B2674745
theorem B2676167 : Blo 1188411 2676167 := bstep (se 1 (by rfl) ⟨2007125, by rfl⟩ : syracuseStep 2676167 = 4014251) B4014251
theorem B1783289 : Blo 1188411 1783289 := bstep (se 2 (by rfl) ⟨668733, by rfl⟩ : syracuseStep 1783289 = 1337467) B1337467
theorem B3388985 : Blo 1188411 3388985 := bstep (se 2 (by rfl) ⟨1270869, by rfl⟩ : syracuseStep 3388985 = 2541739) B2541739
theorem B1783391 : Blo 1188411 1783391 := bstep (se 1 (by rfl) ⟨1337543, by rfl⟩ : syracuseStep 1783391 = 2675087) B2675087
theorem B1505071 : Blo 1188411 1505071 := bstep (se 1 (by rfl) ⟨1128803, by rfl⟩ : syracuseStep 1505071 = 2257607) B2257607
theorem B2676527 : Blo 1188411 2676527 := bstep (se 1 (by rfl) ⟨2007395, by rfl⟩ : syracuseStep 2676527 = 4014791) B4014791
theorem B1783607 : Blo 1188411 1783607 := bstep (se 1 (by rfl) ⟨1337705, by rfl⟩ : syracuseStep 1783607 = 2675411) B2675411
theorem B13924151 : Blo 1188411 13924151 := bstep (se 1 (by rfl) ⟨10443113, by rfl⟩ : syracuseStep 13924151 = 20886227) B20886227
theorem B4011983 : Blo 1188411 4011983 := bstep (se 1 (by rfl) ⟨3008987, by rfl⟩ : syracuseStep 4011983 = 6017975) B6017975
theorem B1783913 : Blo 1188411 1783913 := bstep (se 2 (by rfl) ⟨668967, by rfl⟩ : syracuseStep 1783913 = 1337935) B1337935
theorem B69556493 : Blo 1188411 69556493 := bstep (se 3 (by rfl) ⟨13041842, by rfl⟩ : syracuseStep 69556493 = 26083685) B26083685
theorem B5216537 : Blo 1188411 5216537 := bstep (se 2 (by rfl) ⟨1956201, by rfl⟩ : syracuseStep 5216537 = 3912403) B3912403
theorem B3619097 : Blo 1188411 3619097 := bstep (se 2 (by rfl) ⟨1357161, by rfl⟩ : syracuseStep 3619097 = 2714323) B2714323
theorem B1505567 : Blo 1188411 1505567 := bstep (se 1 (by rfl) ⟨1129175, by rfl⟩ : syracuseStep 1505567 = 2258351) B2258351
theorem B2677103 : Blo 1188411 2677103 := bstep (se 1 (by rfl) ⟨2007827, by rfl⟩ : syracuseStep 2677103 = 4015655) B4015655
theorem B1784231 : Blo 1188411 1784231 := bstep (se 1 (by rfl) ⟨1338173, by rfl⟩ : syracuseStep 1784231 = 2676347) B2676347
theorem B84654517 : Blo 1188411 84654517 := bstep (se 5 (by rfl) ⟨3968180, by rfl⟩ : syracuseStep 84654517 = 7936361) B7936361
theorem B2677175 : Blo 1188411 2677175 := bstep (se 1 (by rfl) ⟨2007881, by rfl⟩ : syracuseStep 2677175 = 4015763) B4015763
theorem B2005499 : Blo 1188411 2005499 := bstep (se 1 (by rfl) ⟨1504124, by rfl⟩ : syracuseStep 2005499 = 3008249) B3008249
theorem B1784315 : Blo 1188411 1784315 := bstep (se 1 (by rfl) ⟨1338236, by rfl⟩ : syracuseStep 1784315 = 2676473) B2676473
theorem B3013139 : Blo 1188411 3013139 := bstep (se 1 (by rfl) ⟨2259854, by rfl⟩ : syracuseStep 3013139 = 4519709) B4519709
theorem B24746555 : Blo 1188411 24746555 := bstep (se 1 (by rfl) ⟨18559916, by rfl⟩ : syracuseStep 24746555 = 37119833) B37119833
theorem B2677319 : Blo 1188411 2677319 := bstep (se 1 (by rfl) ⟨2007989, by rfl⟩ : syracuseStep 2677319 = 4015979) B4015979
theorem B6773321 : Blo 1188411 6773321 := bstep (se 2 (by rfl) ⟨2539995, by rfl⟩ : syracuseStep 6773321 = 5079991) B5079991
theorem B2677355 : Blo 1188411 2677355 := bstep (se 1 (by rfl) ⟨2008016, by rfl⟩ : syracuseStep 2677355 = 4016033) B4016033
theorem B1784441 : Blo 1188411 1784441 := bstep (se 2 (by rfl) ⟨669165, by rfl⟩ : syracuseStep 1784441 = 1338331) B1338331
theorem B8567471 : Blo 1188411 8567471 := bstep (se 1 (by rfl) ⟨6425603, by rfl⟩ : syracuseStep 8567471 = 12851207) B12851207
theorem B1784495 : Blo 1188411 1784495 := bstep (se 1 (by rfl) ⟨1338371, by rfl⟩ : syracuseStep 1784495 = 2676743) B2676743
theorem B1784543 : Blo 1188411 1784543 := bstep (se 1 (by rfl) ⟨1338407, by rfl⟩ : syracuseStep 1784543 = 2676815) B2676815
theorem B13556483 : Blo 1188411 13556483 := bstep (se 1 (by rfl) ⟨10167362, by rfl⟩ : syracuseStep 13556483 = 20334725) B20334725
theorem B4012955 : Blo 1188411 4012955 := bstep (se 1 (by rfl) ⟨3009716, by rfl⟩ : syracuseStep 4012955 = 6019433) B6019433
theorem B2005931 : Blo 1188411 2005931 := bstep (se 1 (by rfl) ⟨1504448, by rfl⟩ : syracuseStep 2005931 = 3008897) B3008897
theorem B9026477 : Blo 1188411 9026477 := bstep (se 3 (by rfl) ⟨1692464, by rfl⟩ : syracuseStep 9026477 = 3384929) B3384929
theorem B1784807 : Blo 1188411 1784807 := bstep (se 1 (by rfl) ⟨1338605, by rfl⟩ : syracuseStep 1784807 = 2677211) B2677211
theorem B9034739 : Blo 1188411 9034739 := bstep (se 1 (by rfl) ⟨6776054, by rfl⟩ : syracuseStep 9034739 = 13552109) B13552109
theorem B2677751 : Blo 1188411 2677751 := bstep (se 1 (by rfl) ⟨2008313, by rfl⟩ : syracuseStep 2677751 = 4016627) B4016627
theorem B77225021 : Blo 1188411 77225021 := bstep (se 3 (by rfl) ⟨14479691, by rfl⟩ : syracuseStep 77225021 = 28959383) B28959383
theorem B2538715 : Blo 1188411 2538715 := bstep (se 1 (by rfl) ⟨1904036, by rfl⟩ : syracuseStep 2538715 = 3808073) B3808073
theorem B1785065 : Blo 1188411 1785065 := bstep (se 2 (by rfl) ⟨669399, by rfl⟩ : syracuseStep 1785065 = 1338799) B1338799
theorem B1785119 : Blo 1188411 1785119 := bstep (se 1 (by rfl) ⟨1338839, by rfl⟩ : syracuseStep 1785119 = 2677679) B2677679
theorem B2678111 : Blo 1188411 2678111 := bstep (se 1 (by rfl) ⟨2008583, by rfl⟩ : syracuseStep 2678111 = 4017167) B4017167
theorem B2710921 : Blo 1188411 2710921 := bstep (se 2 (by rfl) ⟨1016595, by rfl⟩ : syracuseStep 2710921 = 2033191) B2033191
theorem B3431879 : Blo 1188411 3431879 := bstep (se 1 (by rfl) ⟨2573909, by rfl⟩ : syracuseStep 3431879 = 5147819) B5147819
theorem B2006471 : Blo 1188411 2006471 := bstep (se 1 (by rfl) ⟨1504853, by rfl⟩ : syracuseStep 2006471 = 3009707) B3009707
theorem B1785287 : Blo 1188411 1785287 := bstep (se 1 (by rfl) ⟨1338965, by rfl⟩ : syracuseStep 1785287 = 2677931) B2677931
theorem B8134103 : Blo 1188411 8134103 := bstep (se 1 (by rfl) ⟨6100577, by rfl⟩ : syracuseStep 8134103 = 12201155) B12201155
theorem B6020567 : Blo 1188411 6020567 := bstep (se 1 (by rfl) ⟨4515425, by rfl⟩ : syracuseStep 6020567 = 9030851) B9030851
theorem B5078609 : Blo 1188411 5078609 := bstep (se 2 (by rfl) ⟨1904478, by rfl⟩ : syracuseStep 5078609 = 3808957) B3808957
theorem B12197537 : Blo 1188411 12197537 := bstep (se 2 (by rfl) ⟨4574076, by rfl⟩ : syracuseStep 12197537 = 9148153) B9148153
theorem B4013981 : Blo 1188411 4013981 := bstep (se 3 (by rfl) ⟨752621, by rfl⟩ : syracuseStep 4013981 = 1505243) B1505243
theorem B15253505 : Blo 1188411 15253505 := bstep (se 2 (by rfl) ⟨5720064, by rfl⟩ : syracuseStep 15253505 = 11440129) B11440129
theorem B2007227 : Blo 1188411 2007227 := bstep (se 1 (by rfl) ⟨1505420, by rfl⟩ : syracuseStep 2007227 = 3010841) B3010841
theorem B20308481 : Blo 1188411 20308481 := bstep (se 2 (by rfl) ⟨7615680, by rfl⟩ : syracuseStep 20308481 = 15231361) B15231361
theorem B1188455 : Blo 1188411 1188455 := bstep (se 1 (by rfl) ⟨891341, by rfl⟩ : syracuseStep 1188455 = 1782683) B1782683
theorem B185483981 : Blo 1188411 185483981 := bstep (se 3 (by rfl) ⟨34778246, by rfl⟩ : syracuseStep 185483981 = 69556493) B69556493
theorem B2007787 : Blo 1188411 2007787 := bstep (se 1 (by rfl) ⟨1505840, by rfl⟩ : syracuseStep 2007787 = 3011681) B3011681
theorem B4014845 : Blo 1188411 4014845 := bstep (se 3 (by rfl) ⟨752783, by rfl⟩ : syracuseStep 4014845 = 1505567) B1505567
theorem B52822793 : Blo 1188411 52822793 := bstep (se 2 (by rfl) ⟨19808547, by rfl⟩ : syracuseStep 52822793 = 39617095) B39617095
theorem B10158857 : Blo 1188411 10158857 := bstep (se 2 (by rfl) ⟨3809571, by rfl⟩ : syracuseStep 10158857 = 7619143) B7619143
theorem B1188719 : Blo 1188411 1188719 := bstep (se 1 (by rfl) ⟨891539, by rfl⟩ : syracuseStep 1188719 = 1783079) B1783079
theorem B1188775 : Blo 1188411 1188775 := bstep (se 1 (by rfl) ⟨891581, by rfl⟩ : syracuseStep 1188775 = 1783163) B1783163
theorem B1188859 : Blo 1188411 1188859 := bstep (se 1 (by rfl) ⟨891644, by rfl⟩ : syracuseStep 1188859 = 1783289) B1783289
theorem B13550651 : Blo 1188411 13550651 := bstep (se 1 (by rfl) ⟨10162988, by rfl⟩ : syracuseStep 13550651 = 20325977) B20325977
theorem B1188927 : Blo 1188411 1188927 := bstep (se 1 (by rfl) ⟨891695, by rfl⟩ : syracuseStep 1188927 = 1783391) B1783391
theorem B1189071 : Blo 1188411 1189071 := bstep (se 1 (by rfl) ⟨891803, by rfl⟩ : syracuseStep 1189071 = 1783607) B1783607
theorem B9282767 : Blo 1188411 9282767 := bstep (se 1 (by rfl) ⟨6962075, by rfl⟩ : syracuseStep 9282767 = 13924151) B13924151
theorem B18302219 : Blo 1188411 18302219 := bstep (se 1 (by rfl) ⟨13726664, by rfl⟩ : syracuseStep 18302219 = 27453329) B27453329
theorem B1189275 : Blo 1188411 1189275 := bstep (se 1 (by rfl) ⟨891956, by rfl⟩ : syracuseStep 1189275 = 1783913) B1783913
theorem B1189487 : Blo 1188411 1189487 := bstep (se 1 (by rfl) ⟨892115, by rfl⟩ : syracuseStep 1189487 = 1784231) B1784231
theorem B3384953 : Blo 1188411 3384953 := bstep (se 2 (by rfl) ⟨1269357, by rfl⟩ : syracuseStep 3384953 = 2538715) B2538715
theorem B1336999 : Blo 1188411 1336999 := bstep (se 1 (by rfl) ⟨1002749, by rfl⟩ : syracuseStep 1336999 = 2005499) B2005499
theorem B1189543 : Blo 1188411 1189543 := bstep (se 1 (by rfl) ⟨892157, by rfl⟩ : syracuseStep 1189543 = 1784315) B1784315
theorem B2008759 : Blo 1188411 2008759 := bstep (se 1 (by rfl) ⟨1506569, by rfl⟩ : syracuseStep 2008759 = 3013139) B3013139
theorem B4515547 : Blo 1188411 4515547 := bstep (se 1 (by rfl) ⟨3386660, by rfl⟩ : syracuseStep 4515547 = 6773321) B6773321
theorem B17139437 : Blo 1188411 17139437 := bstep (se 3 (by rfl) ⟨3213644, by rfl⟩ : syracuseStep 17139437 = 6427289) B6427289
theorem B1189627 : Blo 1188411 1189627 := bstep (se 1 (by rfl) ⟨892220, by rfl⟩ : syracuseStep 1189627 = 1784441) B1784441
theorem B5711647 : Blo 1188411 5711647 := bstep (se 1 (by rfl) ⟨4283735, by rfl⟩ : syracuseStep 5711647 = 8567471) B8567471
theorem B1189663 : Blo 1188411 1189663 := bstep (se 1 (by rfl) ⟨892247, by rfl⟩ : syracuseStep 1189663 = 1784495) B1784495
theorem B2033471 : Blo 1188411 2033471 := bstep (se 1 (by rfl) ⟨1525103, by rfl⟩ : syracuseStep 2033471 = 3050207) B3050207
theorem B1189695 : Blo 1188411 1189695 := bstep (se 1 (by rfl) ⟨892271, by rfl⟩ : syracuseStep 1189695 = 1784543) B1784543
theorem B9037655 : Blo 1188411 9037655 := bstep (se 1 (by rfl) ⟨6778241, by rfl⟩ : syracuseStep 9037655 = 13556483) B13556483
theorem B3614561 : Blo 1188411 3614561 := bstep (se 2 (by rfl) ⟨1355460, by rfl⟩ : syracuseStep 3614561 = 2710921) B2710921
theorem B1337287 : Blo 1188411 1337287 := bstep (se 1 (by rfl) ⟨1002965, by rfl⟩ : syracuseStep 1337287 = 2005931) B2005931
theorem B1189871 : Blo 1188411 1189871 := bstep (se 1 (by rfl) ⟨892403, by rfl⟩ : syracuseStep 1189871 = 1784807) B1784807
theorem B6023159 : Blo 1188411 6023159 := bstep (se 1 (by rfl) ⟨4517369, by rfl⟩ : syracuseStep 6023159 = 9034739) B9034739
theorem B6023321 : Blo 1188411 6023321 := bstep (se 2 (by rfl) ⟨2258745, by rfl⟩ : syracuseStep 6023321 = 4517491) B4517491
theorem B1190043 : Blo 1188411 1190043 := bstep (se 1 (by rfl) ⟨892532, by rfl⟩ : syracuseStep 1190043 = 1785065) B1785065
theorem B1190079 : Blo 1188411 1190079 := bstep (se 1 (by rfl) ⟨892559, by rfl⟩ : syracuseStep 1190079 = 1785119) B1785119
theorem B9029879 : Blo 1188411 9029879 := bstep (se 1 (by rfl) ⟨6772409, by rfl⟩ : syracuseStep 9029879 = 13544819) B13544819
theorem B2287919 : Blo 1188411 2287919 := bstep (se 1 (by rfl) ⟨1715939, by rfl⟩ : syracuseStep 2287919 = 3431879) B3431879
theorem B1337647 : Blo 1188411 1337647 := bstep (se 1 (by rfl) ⟨1003235, by rfl⟩ : syracuseStep 1337647 = 2006471) B2006471
theorem B7620911 : Blo 1188411 7620911 := bstep (se 1 (by rfl) ⟨5715683, by rfl⟩ : syracuseStep 7620911 = 11431367) B11431367
theorem B1190191 : Blo 1188411 1190191 := bstep (se 1 (by rfl) ⟨892643, by rfl⟩ : syracuseStep 1190191 = 1785287) B1785287
theorem B3385739 : Blo 1188411 3385739 := bstep (se 1 (by rfl) ⟨2539304, by rfl⟩ : syracuseStep 3385739 = 5078609) B5078609
theorem B4016951 : Blo 1188411 4016951 := bstep (se 1 (by rfl) ⟨3012713, by rfl⟩ : syracuseStep 4016951 = 6025427) B6025427
theorem B1608607 : Blo 1188411 1608607 := bstep (se 1 (by rfl) ⟨1206455, by rfl⟩ : syracuseStep 1608607 = 2412911) B2412911
theorem B6024131 : Blo 1188411 6024131 := bstep (se 1 (by rfl) ⟨4518098, by rfl⟩ : syracuseStep 6024131 = 9036197) B9036197
theorem B1428527 : Blo 1188411 1428527 := bstep (se 1 (by rfl) ⟨1071395, by rfl⟩ : syracuseStep 1428527 = 2142791) B2142791
theorem B16264259 : Blo 1188411 16264259 := bstep (se 1 (by rfl) ⟨12198194, by rfl⟩ : syracuseStep 16264259 = 24396389) B24396389
theorem B1338439 : Blo 1188411 1338439 := bstep (se 1 (by rfl) ⟨1003829, by rfl⟩ : syracuseStep 1338439 = 2007659) B2007659
theorem B15281287 : Blo 1188411 15281287 := bstep (se 1 (by rfl) ⟨11460965, by rfl⟩ : syracuseStep 15281287 = 22921931) B22921931
theorem B112872689 : Blo 1188411 112872689 := bstep (se 2 (by rfl) ⟨42327258, by rfl⟩ : syracuseStep 112872689 = 84654517) B84654517
theorem B2256491 : Blo 1188411 2256491 := bstep (se 1 (by rfl) ⟨1692368, by rfl⟩ : syracuseStep 2256491 = 3384737) B3384737
theorem B3010223 : Blo 1188411 3010223 := bstep (se 1 (by rfl) ⟨2257667, by rfl⟩ : syracuseStep 3010223 = 4515335) B4515335
theorem B12201769 : Blo 1188411 12201769 := bstep (se 2 (by rfl) ⟨4575663, by rfl⟩ : syracuseStep 12201769 = 9151327) B9151327
theorem B17624965 : Blo 1188411 17624965 := bstep (se 4 (by rfl) ⟨1652340, by rfl⟩ : syracuseStep 17624965 = 3304681) B3304681
theorem B3813263 : Blo 1188411 3813263 := bstep (se 1 (by rfl) ⟨2859947, by rfl⟩ : syracuseStep 3813263 = 5719895) B5719895
theorem B2674655 : Blo 1188411 2674655 := bstep (se 1 (by rfl) ⟨2005991, by rfl⟩ : syracuseStep 2674655 = 4011983) B4011983
theorem B3010547 : Blo 1188411 3010547 := bstep (se 1 (by rfl) ⟨2257910, by rfl⟩ : syracuseStep 3010547 = 4515821) B4515821
theorem B3387379 : Blo 1188411 3387379 := bstep (se 1 (by rfl) ⟨2540534, by rfl⟩ : syracuseStep 3387379 = 5081069) B5081069
theorem B8138917 : Blo 1188411 8138917 := bstep (se 4 (by rfl) ⟨763023, by rfl⟩ : syracuseStep 8138917 = 1526047) B1526047
theorem B4288697 : Blo 1188411 4288697 := bstep (se 2 (by rfl) ⟨1608261, by rfl⟩ : syracuseStep 4288697 = 3216523) B3216523
theorem B3477691 : Blo 1188411 3477691 := bstep (se 1 (by rfl) ⟨2608268, by rfl⟩ : syracuseStep 3477691 = 5216537) B5216537
theorem B2412731 : Blo 1188411 2412731 := bstep (se 1 (by rfl) ⟨1809548, by rfl⟩ : syracuseStep 2412731 = 3619097) B3619097
theorem B3010871 : Blo 1188411 3010871 := bstep (se 1 (by rfl) ⟨2258153, by rfl⟩ : syracuseStep 3010871 = 4516307) B4516307
theorem B4518281 : Blo 1188411 4518281 := bstep (se 2 (by rfl) ⟨1694355, by rfl⟩ : syracuseStep 4518281 = 3388711) B3388711
theorem B15249815 : Blo 1188411 15249815 := bstep (se 1 (by rfl) ⟨11437361, by rfl⟩ : syracuseStep 15249815 = 22874723) B22874723
theorem B2675303 : Blo 1188411 2675303 := bstep (se 1 (by rfl) ⟨2006477, by rfl⟩ : syracuseStep 2675303 = 4012955) B4012955
theorem B6017651 : Blo 1188411 6017651 := bstep (se 1 (by rfl) ⟨4513238, by rfl⟩ : syracuseStep 6017651 = 9026477) B9026477
theorem B51483347 : Blo 1188411 51483347 := bstep (se 1 (by rfl) ⟨38612510, by rfl⟩ : syracuseStep 51483347 = 77225021) B77225021
theorem B1782695 : Blo 1188411 1782695 := bstep (se 1 (by rfl) ⟨1337021, by rfl⟩ : syracuseStep 1782695 = 2674043) B2674043
theorem B1782779 : Blo 1188411 1782779 := bstep (se 1 (by rfl) ⟨1337084, by rfl⟩ : syracuseStep 1782779 = 2674169) B2674169
theorem B1782839 : Blo 1188411 1782839 := bstep (se 1 (by rfl) ⟨1337129, by rfl⟩ : syracuseStep 1782839 = 2674259) B2674259
theorem B8131691 : Blo 1188411 8131691 := bstep (se 1 (by rfl) ⟨6098768, by rfl⟩ : syracuseStep 8131691 = 12197537) B12197537
theorem B1782959 : Blo 1188411 1782959 := bstep (se 1 (by rfl) ⟨1337219, by rfl⟩ : syracuseStep 1782959 = 2674439) B2674439
theorem B4011227 : Blo 1188411 4011227 := bstep (se 1 (by rfl) ⟨3008420, by rfl⟩ : syracuseStep 4011227 = 6016841) B6016841
theorem B2675987 : Blo 1188411 2675987 := bstep (se 1 (by rfl) ⟨2006990, by rfl⟩ : syracuseStep 2675987 = 4013981) B4013981
theorem B2676059 : Blo 1188411 2676059 := bstep (se 1 (by rfl) ⟨2007044, by rfl⟩ : syracuseStep 2676059 = 4014089) B4014089
theorem B3388871 : Blo 1188411 3388871 := bstep (se 1 (by rfl) ⟨2541653, by rfl⟩ : syracuseStep 3388871 = 5083307) B5083307
theorem B51451361 : Blo 1188411 51451361 := bstep (se 2 (by rfl) ⟨19294260, by rfl⟩ : syracuseStep 51451361 = 38588521) B38588521
theorem B1783367 : Blo 1188411 1783367 := bstep (se 1 (by rfl) ⟨1337525, by rfl⟩ : syracuseStep 1783367 = 2675051) B2675051
theorem B3012167 : Blo 1188411 3012167 := bstep (se 1 (by rfl) ⟨2259125, by rfl⟩ : syracuseStep 3012167 = 4518251) B4518251
theorem B1717831 : Blo 1188411 1717831 := bstep (se 1 (by rfl) ⟨1288373, by rfl⟩ : syracuseStep 1717831 = 2576747) B2576747
theorem B1783463 : Blo 1188411 1783463 := bstep (se 1 (by rfl) ⟨1337597, by rfl⟩ : syracuseStep 1783463 = 2675195) B2675195
theorem B1906343 : Blo 1188411 1906343 := bstep (se 1 (by rfl) ⟨1429757, by rfl⟩ : syracuseStep 1906343 = 2859515) B2859515
theorem B3389111 : Blo 1188411 3389111 := bstep (se 1 (by rfl) ⟨2541833, by rfl⟩ : syracuseStep 3389111 = 5083667) B5083667
theorem B7730923 : Blo 1188411 7730923 := bstep (se 1 (by rfl) ⟨5798192, by rfl⟩ : syracuseStep 7730923 = 11596385) B11596385
theorem B1783547 : Blo 1188411 1783547 := bstep (se 1 (by rfl) ⟨1337660, by rfl⟩ : syracuseStep 1783547 = 2675321) B2675321
theorem B1783583 : Blo 1188411 1783583 := bstep (se 1 (by rfl) ⟨1337687, by rfl⟩ : syracuseStep 1783583 = 2675375) B2675375
theorem B1783631 : Blo 1188411 1783631 := bstep (se 1 (by rfl) ⟨1337723, by rfl⟩ : syracuseStep 1783631 = 2675447) B2675447
theorem B2676617 : Blo 1188411 2676617 := bstep (se 2 (by rfl) ⟨1003731, by rfl⟩ : syracuseStep 2676617 = 2007463) B2007463
theorem B1783751 : Blo 1188411 1783751 := bstep (se 1 (by rfl) ⟨1337813, by rfl⟩ : syracuseStep 1783751 = 2675627) B2675627
theorem B5576663 : Blo 1188411 5576663 := bstep (se 1 (by rfl) ⟨4182497, by rfl⟩ : syracuseStep 5576663 = 8364995) B8364995
theorem B4012091 : Blo 1188411 4012091 := bstep (se 1 (by rfl) ⟨3009068, by rfl⟩ : syracuseStep 4012091 = 6018137) B6018137
theorem B2676833 : Blo 1188411 2676833 := bstep (se 2 (by rfl) ⟨1003812, by rfl⟩ : syracuseStep 2676833 = 2007625) B2007625
theorem B2857103 : Blo 1188411 2857103 := bstep (se 1 (by rfl) ⟨2142827, by rfl⟩ : syracuseStep 2857103 = 4285655) B4285655
theorem B6019271 : Blo 1188411 6019271 := bstep (se 1 (by rfl) ⟨4514453, by rfl⟩ : syracuseStep 6019271 = 9028907) B9028907
theorem B33437933 : Blo 1188411 33437933 := bstep (se 3 (by rfl) ⟨6269612, by rfl⟩ : syracuseStep 33437933 = 12539225) B12539225
theorem B9156901 : Blo 1188411 9156901 := bstep (se 4 (by rfl) ⟨858459, by rfl⟩ : syracuseStep 9156901 = 1716919) B1716919
theorem B1693991 : Blo 1188411 1693991 := bstep (se 1 (by rfl) ⟨1270493, by rfl⟩ : syracuseStep 1693991 = 2540987) B2540987
theorem B1784105 : Blo 1188411 1784105 := bstep (se 2 (by rfl) ⟨669039, by rfl⟩ : syracuseStep 1784105 = 1338079) B1338079
theorem B1784111 : Blo 1188411 1784111 := bstep (se 1 (by rfl) ⟨1338083, by rfl⟩ : syracuseStep 1784111 = 2676167) B2676167
theorem B4012361 : Blo 1188411 4012361 := bstep (se 2 (by rfl) ⟨1504635, by rfl⟩ : syracuseStep 4012361 = 3009271) B3009271
theorem B2259323 : Blo 1188411 2259323 := bstep (se 1 (by rfl) ⟨1694492, by rfl⟩ : syracuseStep 2259323 = 3388985) B3388985
theorem B17160659 : Blo 1188411 17160659 := bstep (se 1 (by rfl) ⟨12870494, by rfl⟩ : syracuseStep 17160659 = 25740989) B25740989
theorem B1784351 : Blo 1188411 1784351 := bstep (se 1 (by rfl) ⟨1338263, by rfl⟩ : syracuseStep 1784351 = 2676527) B2676527
theorem B4512617 : Blo 1188411 4512617 := bstep (se 2 (by rfl) ⟨1692231, by rfl⟩ : syracuseStep 4512617 = 3384463) B3384463
theorem B1784735 : Blo 1188411 1784735 := bstep (se 1 (by rfl) ⟨1338551, by rfl⟩ : syracuseStep 1784735 = 2677103) B2677103
theorem B1784783 : Blo 1188411 1784783 := bstep (se 1 (by rfl) ⟨1338587, by rfl⟩ : syracuseStep 1784783 = 2677175) B2677175
theorem B16497703 : Blo 1188411 16497703 := bstep (se 1 (by rfl) ⟨12373277, by rfl⟩ : syracuseStep 16497703 = 24746555) B24746555
theorem B1784873 : Blo 1188411 1784873 := bstep (se 2 (by rfl) ⟨669327, by rfl⟩ : syracuseStep 1784873 = 1338655) B1338655
theorem B1784879 : Blo 1188411 1784879 := bstep (se 1 (by rfl) ⟨1338659, by rfl⟩ : syracuseStep 1784879 = 2677319) B2677319
theorem B1784903 : Blo 1188411 1784903 := bstep (se 1 (by rfl) ⟨1338677, by rfl⟩ : syracuseStep 1784903 = 2677355) B2677355
theorem B6020243 : Blo 1188411 6020243 := bstep (se 1 (by rfl) ⟨4515182, by rfl⟩ : syracuseStep 6020243 = 9030365) B9030365
theorem B1785167 : Blo 1188411 1785167 := bstep (se 1 (by rfl) ⟨1338875, by rfl⟩ : syracuseStep 1785167 = 2677751) B2677751
theorem B2006383 : Blo 1188411 2006383 := bstep (se 1 (by rfl) ⟨1504787, by rfl⟩ : syracuseStep 2006383 = 3009575) B3009575
theorem B8691083 : Blo 1188411 8691083 := bstep (se 1 (by rfl) ⟨6518312, by rfl⟩ : syracuseStep 8691083 = 13036625) B13036625
theorem B2678183 : Blo 1188411 2678183 := bstep (se 1 (by rfl) ⟨2008637, by rfl⟩ : syracuseStep 2678183 = 4017275) B4017275
theorem B1785257 : Blo 1188411 1785257 := bstep (se 2 (by rfl) ⟨669471, by rfl⟩ : syracuseStep 1785257 = 1338943) B1338943
theorem B1785407 : Blo 1188411 1785407 := bstep (se 1 (by rfl) ⟨1339055, by rfl⟩ : syracuseStep 1785407 = 2678111) B2678111
theorem B2678363 : Blo 1188411 2678363 := bstep (se 1 (by rfl) ⟨2008772, by rfl⟩ : syracuseStep 2678363 = 4017545) B4017545
theorem B5422735 : Blo 1188411 5422735 := bstep (se 1 (by rfl) ⟨4067051, by rfl⟩ : syracuseStep 5422735 = 8134103) B8134103
theorem B4013711 : Blo 1188411 4013711 := bstep (se 1 (by rfl) ⟨3010283, by rfl⟩ : syracuseStep 4013711 = 6020567) B6020567
theorem B2006761 : Blo 1188411 2006761 := bstep (se 2 (by rfl) ⟨752535, by rfl⟩ : syracuseStep 2006761 = 1505071) B1505071
theorem B6021053 : Blo 1188411 6021053 := bstep (se 3 (by rfl) ⟨1128947, by rfl⟩ : syracuseStep 6021053 = 2257895) B2257895
theorem B2859131 : Blo 1188411 2859131 := bstep (se 1 (by rfl) ⟨2144348, by rfl⟩ : syracuseStep 2859131 = 4288697) B4288697
theorem B3809405 : Blo 1188411 3809405 := bstep (se 3 (by rfl) ⟨714263, by rfl⟩ : syracuseStep 3809405 = 1428527) B1428527
theorem B2007247 : Blo 1188411 2007247 := bstep (se 1 (by rfl) ⟨1505435, by rfl⟩ : syracuseStep 2007247 = 3010871) B3010871
theorem B4636921 : Blo 1188411 4636921 := bstep (se 2 (by rfl) ⟨1738845, by rfl⟩ : syracuseStep 4636921 = 3477691) B3477691
theorem B10166543 : Blo 1188411 10166543 := bstep (se 1 (by rfl) ⟨7624907, by rfl⟩ : syracuseStep 10166543 = 15249815) B15249815
theorem B21684509 : Blo 1188411 21684509 := bstep (se 3 (by rfl) ⟨4065845, by rfl⟩ : syracuseStep 21684509 = 8131691) B8131691
theorem B1188463 : Blo 1188411 1188463 := bstep (se 1 (by rfl) ⟨891347, by rfl⟩ : syracuseStep 1188463 = 1782695) B1782695
theorem B1188519 : Blo 1188411 1188519 := bstep (se 1 (by rfl) ⟨891389, by rfl⟩ : syracuseStep 1188519 = 1782779) B1782779
theorem B1188559 : Blo 1188411 1188559 := bstep (se 1 (by rfl) ⟨891419, by rfl⟩ : syracuseStep 1188559 = 1782839) B1782839
theorem B1188639 : Blo 1188411 1188639 := bstep (se 1 (by rfl) ⟨891479, by rfl⟩ : syracuseStep 1188639 = 1782959) B1782959
theorem B34300907 : Blo 1188411 34300907 := bstep (se 1 (by rfl) ⟨25725680, by rfl⟩ : syracuseStep 34300907 = 51451361) B51451361
theorem B1188911 : Blo 1188411 1188911 := bstep (se 1 (by rfl) ⟨891683, by rfl⟩ : syracuseStep 1188911 = 1783367) B1783367
theorem B2008111 : Blo 1188411 2008111 := bstep (se 1 (by rfl) ⟨1506083, by rfl⟩ : syracuseStep 2008111 = 3012167) B3012167
theorem B1188975 : Blo 1188411 1188975 := bstep (se 1 (by rfl) ⟨891731, by rfl⟩ : syracuseStep 1188975 = 1783463) B1783463
theorem B1270895 : Blo 1188411 1270895 := bstep (se 1 (by rfl) ⟨953171, by rfl⟩ : syracuseStep 1270895 = 1906343) B1906343
theorem B1189031 : Blo 1188411 1189031 := bstep (se 1 (by rfl) ⟨891773, by rfl⟩ : syracuseStep 1189031 = 1783547) B1783547
theorem B1189055 : Blo 1188411 1189055 := bstep (se 1 (by rfl) ⟨891791, by rfl⟩ : syracuseStep 1189055 = 1783583) B1783583
theorem B1189087 : Blo 1188411 1189087 := bstep (se 1 (by rfl) ⟨891815, by rfl⟩ : syracuseStep 1189087 = 1783631) B1783631
theorem B2409707 : Blo 1188411 2409707 := bstep (se 1 (by rfl) ⟨1807280, by rfl⟩ : syracuseStep 2409707 = 3614561) B3614561
theorem B1189167 : Blo 1188411 1189167 := bstep (se 1 (by rfl) ⟨891875, by rfl⟩ : syracuseStep 1189167 = 1783751) B1783751
theorem B4015439 : Blo 1188411 4015439 := bstep (se 1 (by rfl) ⟨3011579, by rfl⟩ : syracuseStep 4015439 = 6023159) B6023159
theorem B21996937 : Blo 1188411 21996937 := bstep (se 2 (by rfl) ⟨8248851, by rfl⟩ : syracuseStep 21996937 = 16497703) B16497703
theorem B4015547 : Blo 1188411 4015547 := bstep (se 1 (by rfl) ⟨3011660, by rfl⟩ : syracuseStep 4015547 = 6023321) B6023321
theorem B22291955 : Blo 1188411 22291955 := bstep (se 1 (by rfl) ⟨16718966, by rfl⟩ : syracuseStep 22291955 = 33437933) B33437933
theorem B1189403 : Blo 1188411 1189403 := bstep (se 1 (by rfl) ⟨892052, by rfl⟩ : syracuseStep 1189403 = 1784105) B1784105
theorem B1525279 : Blo 1188411 1525279 := bstep (se 1 (by rfl) ⟨1143959, by rfl⟩ : syracuseStep 1525279 = 2287919) B2287919
theorem B1189407 : Blo 1188411 1189407 := bstep (se 1 (by rfl) ⟨892055, by rfl⟩ : syracuseStep 1189407 = 1784111) B1784111
theorem B5080607 : Blo 1188411 5080607 := bstep (se 1 (by rfl) ⟨3810455, by rfl⟩ : syracuseStep 5080607 = 7620911) B7620911
theorem B1189567 : Blo 1188411 1189567 := bstep (se 1 (by rfl) ⟨892175, by rfl⟩ : syracuseStep 1189567 = 1784351) B1784351
theorem B3008411 : Blo 1188411 3008411 := bstep (se 1 (by rfl) ⟨2256308, by rfl⟩ : syracuseStep 3008411 = 4512617) B4512617
theorem B1189823 : Blo 1188411 1189823 := bstep (se 1 (by rfl) ⟨892367, by rfl⟩ : syracuseStep 1189823 = 1784735) B1784735
theorem B4016087 : Blo 1188411 4016087 := bstep (se 1 (by rfl) ⟨3012065, by rfl⟩ : syracuseStep 4016087 = 6024131) B6024131
theorem B1189855 : Blo 1188411 1189855 := bstep (se 1 (by rfl) ⟨892391, by rfl⟩ : syracuseStep 1189855 = 1784783) B1784783
theorem B1189915 : Blo 1188411 1189915 := bstep (se 1 (by rfl) ⟨892436, by rfl⟩ : syracuseStep 1189915 = 1784873) B1784873
theorem B1189919 : Blo 1188411 1189919 := bstep (se 1 (by rfl) ⟨892439, by rfl⟩ : syracuseStep 1189919 = 1784879) B1784879
theorem B1189935 : Blo 1188411 1189935 := bstep (se 1 (by rfl) ⟨892451, by rfl⟩ : syracuseStep 1189935 = 1784903) B1784903
theorem B1190111 : Blo 1188411 1190111 := bstep (se 1 (by rfl) ⟨892583, by rfl⟩ : syracuseStep 1190111 = 1785167) B1785167
theorem B5794055 : Blo 1188411 5794055 := bstep (se 1 (by rfl) ⟨4345541, by rfl⟩ : syracuseStep 5794055 = 8691083) B8691083
theorem B1190171 : Blo 1188411 1190171 := bstep (se 1 (by rfl) ⟨892628, by rfl⟩ : syracuseStep 1190171 = 1785257) B1785257
theorem B10307897 : Blo 1188411 10307897 := bstep (se 2 (by rfl) ⟨3865461, by rfl⟩ : syracuseStep 10307897 = 7730923) B7730923
theorem B1190271 : Blo 1188411 1190271 := bstep (se 1 (by rfl) ⟨892703, by rfl⟩ : syracuseStep 1190271 = 1785407) B1785407
theorem B2542175 : Blo 1188411 2542175 := bstep (se 1 (by rfl) ⟨1906631, by rfl⟩ : syracuseStep 2542175 = 3813263) B3813263
theorem B4516505 : Blo 1188411 4516505 := bstep (se 2 (by rfl) ⟨1693689, by rfl⟩ : syracuseStep 4516505 = 3387379) B3387379
theorem B10169003 : Blo 1188411 10169003 := bstep (se 1 (by rfl) ⟨7626752, by rfl⟩ : syracuseStep 10169003 = 15253505) B15253505
theorem B1338151 : Blo 1188411 1338151 := bstep (se 1 (by rfl) ⟨1003613, by rfl⟩ : syracuseStep 1338151 = 2007227) B2007227
theorem B9161765 : Blo 1188411 9161765 := bstep (se 4 (by rfl) ⟨858915, by rfl⟩ : syracuseStep 9161765 = 1717831) B1717831
theorem B12209201 : Blo 1188411 12209201 := bstep (se 2 (by rfl) ⟨4578450, by rfl⟩ : syracuseStep 12209201 = 9156901) B9156901
theorem B6433949 : Blo 1188411 6433949 := bstep (se 3 (by rfl) ⟨1206365, by rfl⟩ : syracuseStep 6433949 = 2412731) B2412731
theorem B4517309 : Blo 1188411 4517309 := bstep (se 3 (by rfl) ⟨846995, by rfl⟩ : syracuseStep 4517309 = 1693991) B1693991
theorem B2674151 : Blo 1188411 2674151 := bstep (se 1 (by rfl) ⟨2005613, by rfl⟩ : syracuseStep 2674151 = 4011227) B4011227
theorem B12201479 : Blo 1188411 12201479 := bstep (se 1 (by rfl) ⟨9151109, by rfl⟩ : syracuseStep 12201479 = 18302219) B18302219
theorem B2256635 : Blo 1188411 2256635 := bstep (se 1 (by rfl) ⟨1692476, by rfl⟩ : syracuseStep 2256635 = 3384953) B3384953
theorem B1355647 : Blo 1188411 1355647 := bstep (se 1 (by rfl) ⟨1016735, by rfl⟩ : syracuseStep 1355647 = 2033471) B2033471
theorem B6025103 : Blo 1188411 6025103 := bstep (se 1 (by rfl) ⟨4518827, by rfl⟩ : syracuseStep 6025103 = 9037655) B9037655
theorem B2674727 : Blo 1188411 2674727 := bstep (se 1 (by rfl) ⟨2006045, by rfl⟩ : syracuseStep 2674727 = 4012091) B4012091
theorem B1904735 : Blo 1188411 1904735 := bstep (se 1 (by rfl) ⟨1428551, by rfl⟩ : syracuseStep 1904735 = 2857103) B2857103
theorem B2674907 : Blo 1188411 2674907 := bstep (se 1 (by rfl) ⟨2006180, by rfl⟩ : syracuseStep 2674907 = 4012361) B4012361
theorem B2257159 : Blo 1188411 2257159 := bstep (se 1 (by rfl) ⟨1692869, by rfl⟩ : syracuseStep 2257159 = 3385739) B3385739
theorem B11440439 : Blo 1188411 11440439 := bstep (se 1 (by rfl) ⟨8580329, by rfl⟩ : syracuseStep 11440439 = 17160659) B17160659
theorem B2675177 : Blo 1188411 2675177 := bstep (se 2 (by rfl) ⟨1003191, by rfl⟩ : syracuseStep 2675177 = 2006383) B2006383
theorem B10842839 : Blo 1188411 10842839 := bstep (se 1 (by rfl) ⟨8132129, by rfl⟩ : syracuseStep 10842839 = 16264259) B16264259
theorem B75248459 : Blo 1188411 75248459 := bstep (se 1 (by rfl) ⟨56436344, by rfl⟩ : syracuseStep 75248459 = 112872689) B112872689
theorem B7230313 : Blo 1188411 7230313 := bstep (se 2 (by rfl) ⟨2711367, by rfl⟩ : syracuseStep 7230313 = 5422735) B5422735
theorem B1782665 : Blo 1188411 1782665 := bstep (se 2 (by rfl) ⟨668499, by rfl⟩ : syracuseStep 1782665 = 1336999) B1336999
theorem B2675681 : Blo 1188411 2675681 := bstep (se 2 (by rfl) ⟨1003380, by rfl⟩ : syracuseStep 2675681 = 2006761) B2006761
theorem B7615529 : Blo 1188411 7615529 := bstep (se 2 (by rfl) ⟨2855823, by rfl⟩ : syracuseStep 7615529 = 5711647) B5711647
theorem B1504327 : Blo 1188411 1504327 := bstep (se 1 (by rfl) ⟨1128245, by rfl⟩ : syracuseStep 1504327 = 2256491) B2256491
theorem B2675807 : Blo 1188411 2675807 := bstep (se 1 (by rfl) ⟨2006855, by rfl⟩ : syracuseStep 2675807 = 4013711) B4013711
theorem B23499953 : Blo 1188411 23499953 := bstep (se 2 (by rfl) ⟨8812482, by rfl⟩ : syracuseStep 23499953 = 17624965) B17624965
theorem B1783049 : Blo 1188411 1783049 := bstep (se 2 (by rfl) ⟨668643, by rfl⟩ : syracuseStep 1783049 = 1337287) B1337287
theorem B1783103 : Blo 1188411 1783103 := bstep (se 1 (by rfl) ⟨1337327, by rfl⟩ : syracuseStep 1783103 = 2674655) B2674655
theorem B10851889 : Blo 1188411 10851889 := bstep (se 2 (by rfl) ⟨4069458, by rfl⟩ : syracuseStep 10851889 = 8138917) B8138917
theorem B3012187 : Blo 1188411 3012187 := bstep (se 1 (by rfl) ⟨2259140, by rfl⟩ : syracuseStep 3012187 = 4518281) B4518281
theorem B13538987 : Blo 1188411 13538987 := bstep (se 1 (by rfl) ⟨10154240, by rfl⟩ : syracuseStep 13538987 = 20308481) B20308481
theorem B1783529 : Blo 1188411 1783529 := bstep (se 2 (by rfl) ⟨668823, by rfl⟩ : syracuseStep 1783529 = 1337647) B1337647
theorem B1783535 : Blo 1188411 1783535 := bstep (se 1 (by rfl) ⟨1337651, by rfl⟩ : syracuseStep 1783535 = 2675303) B2675303
theorem B4011767 : Blo 1188411 4011767 := bstep (se 1 (by rfl) ⟨3008825, by rfl⟩ : syracuseStep 4011767 = 6017651) B6017651
theorem B123655987 : Blo 1188411 123655987 := bstep (se 1 (by rfl) ⟨92741990, by rfl⟩ : syracuseStep 123655987 = 185483981) B185483981
theorem B34322231 : Blo 1188411 34322231 := bstep (se 1 (by rfl) ⟨25741673, by rfl⟩ : syracuseStep 34322231 = 51483347) B51483347
theorem B2676563 : Blo 1188411 2676563 := bstep (se 1 (by rfl) ⟨2007422, by rfl⟩ : syracuseStep 2676563 = 4014845) B4014845
theorem B35215195 : Blo 1188411 35215195 := bstep (se 1 (by rfl) ⟨26411396, by rfl⟩ : syracuseStep 35215195 = 52822793) B52822793
theorem B6772571 : Blo 1188411 6772571 := bstep (se 1 (by rfl) ⟨5079428, by rfl⟩ : syracuseStep 6772571 = 10158857) B10158857
theorem B81500197 : Blo 1188411 81500197 := bstep (se 4 (by rfl) ⟨7640643, by rfl⟩ : syracuseStep 81500197 = 15281287) B15281287
theorem B9033767 : Blo 1188411 9033767 := bstep (se 1 (by rfl) ⟨6775325, by rfl⟩ : syracuseStep 9033767 = 13550651) B13550651
theorem B1783991 : Blo 1188411 1783991 := bstep (se 1 (by rfl) ⟨1337993, by rfl⟩ : syracuseStep 1783991 = 2675987) B2675987
theorem B1784039 : Blo 1188411 1784039 := bstep (se 1 (by rfl) ⟨1338029, by rfl⟩ : syracuseStep 1784039 = 2676059) B2676059
theorem B2259247 : Blo 1188411 2259247 := bstep (se 1 (by rfl) ⟨1694435, by rfl⟩ : syracuseStep 2259247 = 3388871) B3388871
theorem B2677049 : Blo 1188411 2677049 := bstep (se 2 (by rfl) ⟨1003893, by rfl⟩ : syracuseStep 2677049 = 2007787) B2007787
theorem B2259407 : Blo 1188411 2259407 := bstep (se 1 (by rfl) ⟨1694555, by rfl⟩ : syracuseStep 2259407 = 3389111) B3389111
theorem B11426291 : Blo 1188411 11426291 := bstep (se 1 (by rfl) ⟨8569718, by rfl⟩ : syracuseStep 11426291 = 17139437) B17139437
theorem B2144809 : Blo 1188411 2144809 := bstep (se 2 (by rfl) ⟨804303, by rfl⟩ : syracuseStep 2144809 = 1608607) B1608607
theorem B1784411 : Blo 1188411 1784411 := bstep (se 1 (by rfl) ⟨1338308, by rfl⟩ : syracuseStep 1784411 = 2676617) B2676617
theorem B3717775 : Blo 1188411 3717775 := bstep (se 1 (by rfl) ⟨2788331, by rfl⟩ : syracuseStep 3717775 = 5576663) B5576663
theorem B1784555 : Blo 1188411 1784555 := bstep (se 1 (by rfl) ⟨1338416, by rfl⟩ : syracuseStep 1784555 = 2676833) B2676833
theorem B1784585 : Blo 1188411 1784585 := bstep (se 2 (by rfl) ⟨669219, by rfl⟩ : syracuseStep 1784585 = 1338439) B1338439
theorem B4012847 : Blo 1188411 4012847 := bstep (se 1 (by rfl) ⟨3009635, by rfl⟩ : syracuseStep 4012847 = 6019271) B6019271
theorem B6019919 : Blo 1188411 6019919 := bstep (se 1 (by rfl) ⟨4514939, by rfl⟩ : syracuseStep 6019919 = 9029879) B9029879
theorem B1506215 : Blo 1188411 1506215 := bstep (se 1 (by rfl) ⟨1129661, by rfl⟩ : syracuseStep 1506215 = 2259323) B2259323
theorem B2677967 : Blo 1188411 2677967 := bstep (se 1 (by rfl) ⟨2008475, by rfl⟩ : syracuseStep 2677967 = 4016951) B4016951
theorem B4013495 : Blo 1188411 4013495 := bstep (se 1 (by rfl) ⟨3010121, by rfl⟩ : syracuseStep 4013495 = 6020243) B6020243
theorem B99016181 : Blo 1188411 99016181 := bstep (se 5 (by rfl) ⟨4641383, by rfl⟩ : syracuseStep 99016181 = 9282767) B9282767
theorem B2678345 : Blo 1188411 2678345 := bstep (se 2 (by rfl) ⟨1004379, by rfl⟩ : syracuseStep 2678345 = 2008759) B2008759
theorem B1785455 : Blo 1188411 1785455 := bstep (se 1 (by rfl) ⟨1339091, by rfl⟩ : syracuseStep 1785455 = 2678183) B2678183
theorem B6020729 : Blo 1188411 6020729 := bstep (se 2 (by rfl) ⟨2257773, by rfl⟩ : syracuseStep 6020729 = 4515547) B4515547
theorem B16269025 : Blo 1188411 16269025 := bstep (se 2 (by rfl) ⟨6100884, by rfl⟩ : syracuseStep 16269025 = 12201769) B12201769
theorem B1785575 : Blo 1188411 1785575 := bstep (se 1 (by rfl) ⟨1339181, by rfl⟩ : syracuseStep 1785575 = 2678363) B2678363
theorem B2006815 : Blo 1188411 2006815 := bstep (se 1 (by rfl) ⟨1505111, by rfl⟩ : syracuseStep 2006815 = 3010223) B3010223
theorem B4014035 : Blo 1188411 4014035 := bstep (se 1 (by rfl) ⟨3010526, by rfl⟩ : syracuseStep 4014035 = 6021053) B6021053
theorem B2007031 : Blo 1188411 2007031 := bstep (se 1 (by rfl) ⟨1505273, by rfl⟩ : syracuseStep 2007031 = 3010547) B3010547
theorem B108666929 : Blo 1188411 108666929 := bstep (se 2 (by rfl) ⟨40750098, by rfl⟩ : syracuseStep 108666929 = 81500197) B81500197
theorem B2539603 : Blo 1188411 2539603 := bstep (se 1 (by rfl) ⟨1904702, by rfl⟩ : syracuseStep 2539603 = 3809405) B3809405
theorem B7626959 : Blo 1188411 7626959 := bstep (se 1 (by rfl) ⟨5720219, by rfl⟩ : syracuseStep 7626959 = 11440439) B11440439
theorem B5079293 : Blo 1188411 5079293 := bstep (se 3 (by rfl) ⟨952367, by rfl⟩ : syracuseStep 5079293 = 1904735) B1904735
theorem B1188443 : Blo 1188411 1188443 := bstep (se 1 (by rfl) ⟨891332, by rfl⟩ : syracuseStep 1188443 = 1782665) B1782665
theorem B1188699 : Blo 1188411 1188699 := bstep (se 1 (by rfl) ⟨891524, by rfl⟩ : syracuseStep 1188699 = 1783049) B1783049
theorem B4957033 : Blo 1188411 4957033 := bstep (se 2 (by rfl) ⟨1858887, by rfl⟩ : syracuseStep 4957033 = 3717775) B3717775
theorem B1188735 : Blo 1188411 1188735 := bstep (se 1 (by rfl) ⟨891551, by rfl⟩ : syracuseStep 1188735 = 1783103) B1783103
theorem B14861303 : Blo 1188411 14861303 := bstep (se 1 (by rfl) ⟨11145977, by rfl⟩ : syracuseStep 14861303 = 22291955) B22291955
theorem B1189019 : Blo 1188411 1189019 := bstep (se 1 (by rfl) ⟨891764, by rfl⟩ : syracuseStep 1189019 = 1783529) B1783529
theorem B1189023 : Blo 1188411 1189023 := bstep (se 1 (by rfl) ⟨891767, by rfl⟩ : syracuseStep 1189023 = 1783535) B1783535
theorem B22881487 : Blo 1188411 22881487 := bstep (se 1 (by rfl) ⟨17161115, by rfl⟩ : syracuseStep 22881487 = 34322231) B34322231
theorem B4515047 : Blo 1188411 4515047 := bstep (se 1 (by rfl) ⟨3386285, by rfl⟩ : syracuseStep 4515047 = 6772571) B6772571
theorem B6022511 : Blo 1188411 6022511 := bstep (se 1 (by rfl) ⟨4516883, by rfl⟩ : syracuseStep 6022511 = 9033767) B9033767
theorem B1189327 : Blo 1188411 1189327 := bstep (se 1 (by rfl) ⟨891995, by rfl⟩ : syracuseStep 1189327 = 1783991) B1783991
theorem B1189359 : Blo 1188411 1189359 := bstep (se 1 (by rfl) ⟨892019, by rfl⟩ : syracuseStep 1189359 = 1784039) B1784039
theorem B1189607 : Blo 1188411 1189607 := bstep (se 1 (by rfl) ⟨892205, by rfl⟩ : syracuseStep 1189607 = 1784411) B1784411
theorem B1189703 : Blo 1188411 1189703 := bstep (se 1 (by rfl) ⟨892277, by rfl⟩ : syracuseStep 1189703 = 1784555) B1784555
theorem B1189723 : Blo 1188411 1189723 := bstep (se 1 (by rfl) ⟨892292, by rfl⟩ : syracuseStep 1189723 = 1784585) B1784585
theorem B29329249 : Blo 1188411 29329249 := bstep (se 2 (by rfl) ⟨10998468, by rfl⟩ : syracuseStep 29329249 = 21996937) B21996937
theorem B2033705 : Blo 1188411 2033705 := bstep (se 2 (by rfl) ⟨762639, by rfl⟩ : syracuseStep 2033705 = 1525279) B1525279
theorem B14469185 : Blo 1188411 14469185 := bstep (se 2 (by rfl) ⟨5425944, by rfl⟩ : syracuseStep 14469185 = 10851889) B10851889
theorem B4016249 : Blo 1188411 4016249 := bstep (se 2 (by rfl) ⟨1506093, by rfl⟩ : syracuseStep 4016249 = 3012187) B3012187
theorem B164874649 : Blo 1188411 164874649 := bstep (se 2 (by rfl) ⟨61827993, by rfl⟩ : syracuseStep 164874649 = 123655987) B123655987
theorem B1190303 : Blo 1188411 1190303 := bstep (se 1 (by rfl) ⟨892727, by rfl⟩ : syracuseStep 1190303 = 1785455) B1785455
theorem B4016573 : Blo 1188411 4016573 := bstep (se 3 (by rfl) ⟨753107, by rfl⟩ : syracuseStep 4016573 = 1506215) B1506215
theorem B1190383 : Blo 1188411 1190383 := bstep (se 1 (by rfl) ⟨892787, by rfl⟩ : syracuseStep 1190383 = 1785575) B1785575
theorem B4016735 : Blo 1188411 4016735 := bstep (se 1 (by rfl) ⟨3012551, by rfl⟩ : syracuseStep 4016735 = 6025103) B6025103
theorem B6777695 : Blo 1188411 6777695 := bstep (se 1 (by rfl) ⟨5083271, by rfl⟩ : syracuseStep 6777695 = 10166543) B10166543
theorem B11438981 : Blo 1188411 11438981 := bstep (se 4 (by rfl) ⟨1072404, by rfl⟩ : syracuseStep 11438981 = 2144809) B2144809
theorem B3009545 : Blo 1188411 3009545 := bstep (se 2 (by rfl) ⟨1128579, by rfl⟩ : syracuseStep 3009545 = 2257159) B2257159
theorem B17157197 : Blo 1188411 17157197 := bstep (se 3 (by rfl) ⟨3216974, by rfl⟩ : syracuseStep 17157197 = 6433949) B6433949
theorem B7228559 : Blo 1188411 7228559 := bstep (se 1 (by rfl) ⟨5421419, by rfl⟩ : syracuseStep 7228559 = 10842839) B10842839
theorem B6425885 : Blo 1188411 6425885 := bstep (se 3 (by rfl) ⟨1204853, by rfl⟩ : syracuseStep 6425885 = 2409707) B2409707
theorem B22867271 : Blo 1188411 22867271 := bstep (se 1 (by rfl) ⟨17150453, by rfl⟩ : syracuseStep 22867271 = 34300907) B34300907
theorem B15666635 : Blo 1188411 15666635 := bstep (se 1 (by rfl) ⟨11749976, by rfl⟩ : syracuseStep 15666635 = 23499953) B23499953
theorem B3387071 : Blo 1188411 3387071 := bstep (se 1 (by rfl) ⟨2540303, by rfl⟩ : syracuseStep 3387071 = 5080607) B5080607
theorem B2674511 : Blo 1188411 2674511 := bstep (se 1 (by rfl) ⟨2005883, by rfl⟩ : syracuseStep 2674511 = 4011767) B4011767
theorem B3862703 : Blo 1188411 3862703 := bstep (se 1 (by rfl) ⟨2897027, by rfl⟩ : syracuseStep 3862703 = 5794055) B5794055
theorem B3011003 : Blo 1188411 3011003 := bstep (se 1 (by rfl) ⟨2258252, by rfl⟩ : syracuseStep 3011003 = 4516505) B4516505
theorem B6779335 : Blo 1188411 6779335 := bstep (se 1 (by rfl) ⟨5084501, by rfl⟩ : syracuseStep 6779335 = 10169003) B10169003
theorem B2675231 : Blo 1188411 2675231 := bstep (se 1 (by rfl) ⟨2006423, by rfl⟩ : syracuseStep 2675231 = 4012847) B4012847
theorem B6107843 : Blo 1188411 6107843 := bstep (se 1 (by rfl) ⟨4580882, by rfl⟩ : syracuseStep 6107843 = 9161765) B9161765
theorem B8139467 : Blo 1188411 8139467 := bstep (se 1 (by rfl) ⟨6104600, by rfl⟩ : syracuseStep 8139467 = 12209201) B12209201
theorem B2675663 : Blo 1188411 2675663 := bstep (se 1 (by rfl) ⟨2006747, by rfl⟩ : syracuseStep 2675663 = 4013495) B4013495
theorem B3011539 : Blo 1188411 3011539 := bstep (se 1 (by rfl) ⟨2258654, by rfl⟩ : syracuseStep 3011539 = 4517309) B4517309
theorem B1782767 : Blo 1188411 1782767 := bstep (se 1 (by rfl) ⟨1337075, by rfl⟩ : syracuseStep 1782767 = 2674151) B2674151
theorem B2675753 : Blo 1188411 2675753 := bstep (se 2 (by rfl) ⟨1003407, by rfl⟩ : syracuseStep 2675753 = 2006815) B2006815
theorem B46953593 : Blo 1188411 46953593 := bstep (se 2 (by rfl) ⟨17607597, by rfl⟩ : syracuseStep 46953593 = 35215195) B35215195
theorem B1504423 : Blo 1188411 1504423 := bstep (se 1 (by rfl) ⟨1128317, by rfl⟩ : syracuseStep 1504423 = 2256635) B2256635
theorem B1807529 : Blo 1188411 1807529 := bstep (se 2 (by rfl) ⟨677823, by rfl⟩ : syracuseStep 1807529 = 1355647) B1355647
theorem B2676023 : Blo 1188411 2676023 := bstep (se 1 (by rfl) ⟨2007017, by rfl⟩ : syracuseStep 2676023 = 4014035) B4014035
theorem B2676041 : Blo 1188411 2676041 := bstep (se 2 (by rfl) ⟨1003515, by rfl⟩ : syracuseStep 2676041 = 2007031) B2007031
theorem B1783151 : Blo 1188411 1783151 := bstep (se 1 (by rfl) ⟨1337363, by rfl⟩ : syracuseStep 1783151 = 2674727) B2674727
theorem B1906087 : Blo 1188411 1906087 := bstep (se 1 (by rfl) ⟨1429565, by rfl⟩ : syracuseStep 1906087 = 2859131) B2859131
theorem B1783271 : Blo 1188411 1783271 := bstep (se 1 (by rfl) ⟨1337453, by rfl⟩ : syracuseStep 1783271 = 2674907) B2674907
theorem B14456339 : Blo 1188411 14456339 := bstep (se 1 (by rfl) ⟨10842254, by rfl⟩ : syracuseStep 14456339 = 21684509) B21684509
theorem B2676329 : Blo 1188411 2676329 := bstep (se 2 (by rfl) ⟨1003623, by rfl⟩ : syracuseStep 2676329 = 2007247) B2007247
theorem B3389053 : Blo 1188411 3389053 := bstep (se 3 (by rfl) ⟨635447, by rfl⟩ : syracuseStep 3389053 = 1270895) B1270895
theorem B1783451 : Blo 1188411 1783451 := bstep (se 1 (by rfl) ⟨1337588, by rfl⟩ : syracuseStep 1783451 = 2675177) B2675177
theorem B6182561 : Blo 1188411 6182561 := bstep (se 2 (by rfl) ⟨2318460, by rfl⟩ : syracuseStep 6182561 = 4636921) B4636921
theorem B3012329 : Blo 1188411 3012329 := bstep (se 2 (by rfl) ⟨1129623, by rfl⟩ : syracuseStep 3012329 = 2259247) B2259247
theorem B50165639 : Blo 1188411 50165639 := bstep (se 1 (by rfl) ⟨37624229, by rfl⟩ : syracuseStep 50165639 = 75248459) B75248459
theorem B1783787 : Blo 1188411 1783787 := bstep (se 1 (by rfl) ⟨1337840, by rfl⟩ : syracuseStep 1783787 = 2675681) B2675681
theorem B5077019 : Blo 1188411 5077019 := bstep (se 1 (by rfl) ⟨3807764, by rfl⟩ : syracuseStep 5077019 = 7615529) B7615529
theorem B1783871 : Blo 1188411 1783871 := bstep (se 1 (by rfl) ⟨1337903, by rfl⟩ : syracuseStep 1783871 = 2675807) B2675807
theorem B2676959 : Blo 1188411 2676959 := bstep (se 1 (by rfl) ⟨2007719, by rfl⟩ : syracuseStep 2676959 = 4015439) B4015439
theorem B2677031 : Blo 1188411 2677031 := bstep (se 1 (by rfl) ⟨2007773, by rfl⟩ : syracuseStep 2677031 = 4015547) B4015547
theorem B1784201 : Blo 1188411 1784201 := bstep (se 2 (by rfl) ⟨669075, by rfl⟩ : syracuseStep 1784201 = 1338151) B1338151
theorem B9025991 : Blo 1188411 9025991 := bstep (se 1 (by rfl) ⟨6769493, by rfl⟩ : syracuseStep 9025991 = 13538987) B13538987
theorem B9640417 : Blo 1188411 9640417 := bstep (se 2 (by rfl) ⟨3615156, by rfl⟩ : syracuseStep 9640417 = 7230313) B7230313
theorem B1784375 : Blo 1188411 1784375 := bstep (se 1 (by rfl) ⟨1338281, by rfl⟩ : syracuseStep 1784375 = 2676563) B2676563
theorem B2005607 : Blo 1188411 2005607 := bstep (se 1 (by rfl) ⟨1504205, by rfl⟩ : syracuseStep 2005607 = 3008411) B3008411
theorem B2677391 : Blo 1188411 2677391 := bstep (se 1 (by rfl) ⟨2008043, by rfl⟩ : syracuseStep 2677391 = 4016087) B4016087
theorem B2677481 : Blo 1188411 2677481 := bstep (se 2 (by rfl) ⟨1004055, by rfl⟩ : syracuseStep 2677481 = 2008111) B2008111
theorem B2005769 : Blo 1188411 2005769 := bstep (se 2 (by rfl) ⟨752163, by rfl⟩ : syracuseStep 2005769 = 1504327) B1504327
theorem B1784699 : Blo 1188411 1784699 := bstep (se 1 (by rfl) ⟨1338524, by rfl⟩ : syracuseStep 1784699 = 2677049) B2677049
theorem B6871931 : Blo 1188411 6871931 := bstep (se 1 (by rfl) ⟨5153948, by rfl⟩ : syracuseStep 6871931 = 10307897) B10307897
theorem B1506271 : Blo 1188411 1506271 := bstep (se 1 (by rfl) ⟨1129703, by rfl⟩ : syracuseStep 1506271 = 2259407) B2259407
theorem B7617527 : Blo 1188411 7617527 := bstep (se 1 (by rfl) ⟨5713145, by rfl⟩ : syracuseStep 7617527 = 11426291) B11426291
theorem B1694783 : Blo 1188411 1694783 := bstep (se 1 (by rfl) ⟨1271087, by rfl⟩ : syracuseStep 1694783 = 2542175) B2542175
theorem B4013279 : Blo 1188411 4013279 := bstep (se 1 (by rfl) ⟨3009959, by rfl⟩ : syracuseStep 4013279 = 6019919) B6019919
theorem B1785311 : Blo 1188411 1785311 := bstep (se 1 (by rfl) ⟨1338983, by rfl⟩ : syracuseStep 1785311 = 2677967) B2677967
theorem B21692033 : Blo 1188411 21692033 := bstep (se 2 (by rfl) ⟨8134512, by rfl⟩ : syracuseStep 21692033 = 16269025) B16269025
theorem B66010787 : Blo 1188411 66010787 := bstep (se 1 (by rfl) ⟨49508090, by rfl⟩ : syracuseStep 66010787 = 99016181) B99016181
theorem B8134319 : Blo 1188411 8134319 := bstep (se 1 (by rfl) ⟨6100739, by rfl⟩ : syracuseStep 8134319 = 12201479) B12201479
theorem B1785563 : Blo 1188411 1785563 := bstep (se 1 (by rfl) ⟨1339172, by rfl⟩ : syracuseStep 1785563 = 2678345) B2678345
theorem B4013819 : Blo 1188411 4013819 := bstep (se 1 (by rfl) ⟨3010364, by rfl⟩ : syracuseStep 4013819 = 6020729) B6020729
theorem B5423213 : Blo 1188411 5423213 := bstep (se 3 (by rfl) ⟨1016852, by rfl⟩ : syracuseStep 5423213 = 2033705) B2033705
theorem B2007335 : Blo 1188411 2007335 := bstep (se 1 (by rfl) ⟨1505501, by rfl⟩ : syracuseStep 2007335 = 3011003) B3011003
theorem B19276157 : Blo 1188411 19276157 := bstep (se 3 (by rfl) ⟨3614279, by rfl⟩ : syracuseStep 19276157 = 7228559) B7228559
theorem B219832865 : Blo 1188411 219832865 := bstep (se 2 (by rfl) ⟨82437324, by rfl⟩ : syracuseStep 219832865 = 164874649) B164874649
theorem B12853889 : Blo 1188411 12853889 := bstep (se 2 (by rfl) ⟨4820208, by rfl⟩ : syracuseStep 12853889 = 9640417) B9640417
theorem B1188511 : Blo 1188411 1188511 := bstep (se 1 (by rfl) ⟨891383, by rfl⟩ : syracuseStep 1188511 = 1782767) B1782767
theorem B31302395 : Blo 1188411 31302395 := bstep (se 1 (by rfl) ⟨23476796, by rfl⟩ : syracuseStep 31302395 = 46953593) B46953593
theorem B1188767 : Blo 1188411 1188767 := bstep (se 1 (by rfl) ⟨891575, by rfl⟩ : syracuseStep 1188767 = 1783151) B1783151
theorem B4015007 : Blo 1188411 4015007 := bstep (se 1 (by rfl) ⟨3011255, by rfl⟩ : syracuseStep 4015007 = 6022511) B6022511
theorem B1188847 : Blo 1188411 1188847 := bstep (se 1 (by rfl) ⟨891635, by rfl⟩ : syracuseStep 1188847 = 1783271) B1783271
theorem B1188967 : Blo 1188411 1188967 := bstep (se 1 (by rfl) ⟨891725, by rfl⟩ : syracuseStep 1188967 = 1783451) B1783451
theorem B4121707 : Blo 1188411 4121707 := bstep (se 1 (by rfl) ⟨3091280, by rfl⟩ : syracuseStep 4121707 = 6182561) B6182561
theorem B2008219 : Blo 1188411 2008219 := bstep (se 1 (by rfl) ⟨1506164, by rfl⟩ : syracuseStep 2008219 = 3012329) B3012329
theorem B4015385 : Blo 1188411 4015385 := bstep (se 2 (by rfl) ⟨1505769, by rfl⟩ : syracuseStep 4015385 = 3011539) B3011539
theorem B2008361 : Blo 1188411 2008361 := bstep (se 2 (by rfl) ⟨753135, by rfl⟩ : syracuseStep 2008361 = 1506271) B1506271
theorem B1189191 : Blo 1188411 1189191 := bstep (se 1 (by rfl) ⟨891893, by rfl⟩ : syracuseStep 1189191 = 1783787) B1783787
theorem B3384679 : Blo 1188411 3384679 := bstep (se 1 (by rfl) ⟨2538509, by rfl⟩ : syracuseStep 3384679 = 5077019) B5077019
theorem B1189247 : Blo 1188411 1189247 := bstep (se 1 (by rfl) ⟨891935, by rfl⟩ : syracuseStep 1189247 = 1783871) B1783871
theorem B1189467 : Blo 1188411 1189467 := bstep (se 1 (by rfl) ⟨892100, by rfl⟩ : syracuseStep 1189467 = 1784201) B1784201
theorem B30508649 : Blo 1188411 30508649 := bstep (se 2 (by rfl) ⟨11440743, by rfl⟩ : syracuseStep 30508649 = 22881487) B22881487
theorem B1189583 : Blo 1188411 1189583 := bstep (se 1 (by rfl) ⟨892187, by rfl⟩ : syracuseStep 1189583 = 1784375) B1784375
theorem B1337071 : Blo 1188411 1337071 := bstep (se 1 (by rfl) ⟨1002803, by rfl⟩ : syracuseStep 1337071 = 2005607) B2005607
theorem B1337179 : Blo 1188411 1337179 := bstep (se 1 (by rfl) ⟨1002884, by rfl⟩ : syracuseStep 1337179 = 2005769) B2005769
theorem B16287581 : Blo 1188411 16287581 := bstep (se 3 (by rfl) ⟨3053921, by rfl⟩ : syracuseStep 16287581 = 6107843) B6107843
theorem B2541449 : Blo 1188411 2541449 := bstep (se 2 (by rfl) ⟨953043, by rfl⟩ : syracuseStep 2541449 = 1906087) B1906087
theorem B1189799 : Blo 1188411 1189799 := bstep (se 1 (by rfl) ⟨892349, by rfl⟩ : syracuseStep 1189799 = 1784699) B1784699
theorem B4581287 : Blo 1188411 4581287 := bstep (se 1 (by rfl) ⟨3435965, by rfl⟩ : syracuseStep 4581287 = 6871931) B6871931
theorem B11438131 : Blo 1188411 11438131 := bstep (se 1 (by rfl) ⟨8578598, by rfl⟩ : syracuseStep 11438131 = 17157197) B17157197
theorem B1190207 : Blo 1188411 1190207 := bstep (se 1 (by rfl) ⟨892655, by rfl⟩ : syracuseStep 1190207 = 1785311) B1785311
theorem B14461355 : Blo 1188411 14461355 := bstep (se 1 (by rfl) ⟨10846016, by rfl⟩ : syracuseStep 14461355 = 21692033) B21692033
theorem B1190375 : Blo 1188411 1190375 := bstep (se 1 (by rfl) ⟨892781, by rfl⟩ : syracuseStep 1190375 = 1785563) B1785563
theorem B72444619 : Blo 1188411 72444619 := bstep (se 1 (by rfl) ⟨54333464, by rfl⟩ : syracuseStep 72444619 = 108666929) B108666929
theorem B3386137 : Blo 1188411 3386137 := bstep (se 2 (by rfl) ⟨1269801, by rfl⟩ : syracuseStep 3386137 = 2539603) B2539603
theorem B2575135 : Blo 1188411 2575135 := bstep (se 1 (by rfl) ⟨1931351, by rfl⟩ : syracuseStep 2575135 = 3862703) B3862703
theorem B3386195 : Blo 1188411 3386195 := bstep (se 1 (by rfl) ⟨2539646, by rfl⟩ : syracuseStep 3386195 = 5079293) B5079293
theorem B4820077 : Blo 1188411 4820077 := bstep (se 3 (by rfl) ⟨903764, by rfl⟩ : syracuseStep 4820077 = 1807529) B1807529
theorem B9039113 : Blo 1188411 9039113 := bstep (se 2 (by rfl) ⟨3389667, by rfl⟩ : syracuseStep 9039113 = 6779335) B6779335
theorem B9907535 : Blo 1188411 9907535 := bstep (se 1 (by rfl) ⟨7430651, by rfl⟩ : syracuseStep 9907535 = 14861303) B14861303
theorem B3010031 : Blo 1188411 3010031 := bstep (se 1 (by rfl) ⟨2257523, by rfl⟩ : syracuseStep 3010031 = 4515047) B4515047
theorem B9637559 : Blo 1188411 9637559 := bstep (se 1 (by rfl) ⟨7228169, by rfl⟩ : syracuseStep 9637559 = 14456339) B14456339
theorem B33443759 : Blo 1188411 33443759 := bstep (se 1 (by rfl) ⟨25082819, by rfl⟩ : syracuseStep 33443759 = 50165639) B50165639
theorem B9646123 : Blo 1188411 9646123 := bstep (se 1 (by rfl) ⟨7234592, by rfl⟩ : syracuseStep 9646123 = 14469185) B14469185
theorem B6017327 : Blo 1188411 6017327 := bstep (se 1 (by rfl) ⟨4512995, by rfl⟩ : syracuseStep 6017327 = 9025991) B9025991
theorem B21705245 : Blo 1188411 21705245 := bstep (se 3 (by rfl) ⟨4069733, by rfl⟩ : syracuseStep 21705245 = 8139467) B8139467
theorem B4518463 : Blo 1188411 4518463 := bstep (se 1 (by rfl) ⟨3388847, by rfl⟩ : syracuseStep 4518463 = 6777695) B6777695
theorem B2675519 : Blo 1188411 2675519 := bstep (se 1 (by rfl) ⟨2006639, by rfl⟩ : syracuseStep 2675519 = 4013279) B4013279
theorem B4518737 : Blo 1188411 4518737 := bstep (se 2 (by rfl) ⟨1694526, by rfl⟩ : syracuseStep 4518737 = 3389053) B3389053
theorem B2258047 : Blo 1188411 2258047 := bstep (se 1 (by rfl) ⟨1693535, by rfl⟩ : syracuseStep 2258047 = 3387071) B3387071
theorem B39105665 : Blo 1188411 39105665 := bstep (se 2 (by rfl) ⟨14664624, by rfl⟩ : syracuseStep 39105665 = 29329249) B29329249
theorem B2675879 : Blo 1188411 2675879 := bstep (se 1 (by rfl) ⟨2006909, by rfl⟩ : syracuseStep 2675879 = 4013819) B4013819
theorem B1783007 : Blo 1188411 1783007 := bstep (se 1 (by rfl) ⟨1337255, by rfl⟩ : syracuseStep 1783007 = 2674511) B2674511
theorem B5084639 : Blo 1188411 5084639 := bstep (se 1 (by rfl) ⟨3813479, by rfl⟩ : syracuseStep 5084639 = 7626959) B7626959
theorem B4519421 : Blo 1188411 4519421 := bstep (se 3 (by rfl) ⟨847391, by rfl⟩ : syracuseStep 4519421 = 1694783) B1694783
theorem B1783487 : Blo 1188411 1783487 := bstep (se 1 (by rfl) ⟨1337615, by rfl⟩ : syracuseStep 1783487 = 2675231) B2675231
theorem B1783775 : Blo 1188411 1783775 := bstep (se 1 (by rfl) ⟨1337831, by rfl⟩ : syracuseStep 1783775 = 2675663) B2675663
theorem B1783835 : Blo 1188411 1783835 := bstep (se 1 (by rfl) ⟨1337876, by rfl⟩ : syracuseStep 1783835 = 2675753) B2675753
theorem B1784015 : Blo 1188411 1784015 := bstep (se 1 (by rfl) ⟨1338011, by rfl⟩ : syracuseStep 1784015 = 2676023) B2676023
theorem B1784027 : Blo 1188411 1784027 := bstep (se 1 (by rfl) ⟨1338020, by rfl⟩ : syracuseStep 1784027 = 2676041) B2676041
theorem B1784219 : Blo 1188411 1784219 := bstep (se 1 (by rfl) ⟨1338164, by rfl⟩ : syracuseStep 1784219 = 2676329) B2676329
theorem B6609377 : Blo 1188411 6609377 := bstep (se 2 (by rfl) ⟨2478516, by rfl⟩ : syracuseStep 6609377 = 4957033) B4957033
theorem B41777693 : Blo 1188411 41777693 := bstep (se 3 (by rfl) ⟨7833317, by rfl⟩ : syracuseStep 41777693 = 15666635) B15666635
theorem B2677499 : Blo 1188411 2677499 := bstep (se 1 (by rfl) ⟨2008124, by rfl⟩ : syracuseStep 2677499 = 4016249) B4016249
theorem B1784639 : Blo 1188411 1784639 := bstep (se 1 (by rfl) ⟨1338479, by rfl⟩ : syracuseStep 1784639 = 2676959) B2676959
theorem B1784687 : Blo 1188411 1784687 := bstep (se 1 (by rfl) ⟨1338515, by rfl⟩ : syracuseStep 1784687 = 2677031) B2677031
theorem B2005897 : Blo 1188411 2005897 := bstep (se 2 (by rfl) ⟨752211, by rfl⟩ : syracuseStep 2005897 = 1504423) B1504423
theorem B2677715 : Blo 1188411 2677715 := bstep (se 1 (by rfl) ⟨2008286, by rfl⟩ : syracuseStep 2677715 = 4016573) B4016573
theorem B2677823 : Blo 1188411 2677823 := bstep (se 1 (by rfl) ⟨2008367, by rfl⟩ : syracuseStep 2677823 = 4016735) B4016735
theorem B1784927 : Blo 1188411 1784927 := bstep (se 1 (by rfl) ⟨1338695, by rfl⟩ : syracuseStep 1784927 = 2677391) B2677391
theorem B1784987 : Blo 1188411 1784987 := bstep (se 1 (by rfl) ⟨1338740, by rfl⟩ : syracuseStep 1784987 = 2677481) B2677481
theorem B7625987 : Blo 1188411 7625987 := bstep (se 1 (by rfl) ⟨5719490, by rfl⟩ : syracuseStep 7625987 = 11438981) B11438981
theorem B5078351 : Blo 1188411 5078351 := bstep (se 1 (by rfl) ⟨3808763, by rfl⟩ : syracuseStep 5078351 = 7617527) B7617527
theorem B2006363 : Blo 1188411 2006363 := bstep (se 1 (by rfl) ⟨1504772, by rfl⟩ : syracuseStep 2006363 = 3009545) B3009545
theorem B4283923 : Blo 1188411 4283923 := bstep (se 1 (by rfl) ⟨3212942, by rfl⟩ : syracuseStep 4283923 = 6425885) B6425885
theorem B15244847 : Blo 1188411 15244847 := bstep (se 1 (by rfl) ⟨11433635, by rfl⟩ : syracuseStep 15244847 = 22867271) B22867271
theorem B44007191 : Blo 1188411 44007191 := bstep (se 1 (by rfl) ⟨33005393, by rfl⟩ : syracuseStep 44007191 = 66010787) B66010787
theorem B5422879 : Blo 1188411 5422879 := bstep (se 1 (by rfl) ⟨4067159, by rfl⟩ : syracuseStep 5422879 = 8134319) B8134319
theorem B12861497 : Blo 1188411 12861497 := bstep (se 2 (by rfl) ⟨4823061, by rfl⟩ : syracuseStep 12861497 = 9646123) B9646123
theorem B146555243 : Blo 1188411 146555243 := bstep (se 1 (by rfl) ⟨109916432, by rfl⟩ : syracuseStep 146555243 = 219832865) B219832865
theorem B8569259 : Blo 1188411 8569259 := bstep (se 1 (by rfl) ⟨6426944, by rfl⟩ : syracuseStep 8569259 = 12853889) B12853889
theorem B25707077 : Blo 1188411 25707077 := bstep (se 4 (by rfl) ⟨2410038, by rfl⟩ : syracuseStep 25707077 = 4820077) B4820077
theorem B1188671 : Blo 1188411 1188671 := bstep (se 1 (by rfl) ⟨891503, by rfl⟩ : syracuseStep 1188671 = 1783007) B1783007
theorem B26420093 : Blo 1188411 26420093 := bstep (se 3 (by rfl) ⟨4953767, by rfl⟩ : syracuseStep 26420093 = 9907535) B9907535
theorem B96592825 : Blo 1188411 96592825 := bstep (se 2 (by rfl) ⟨36222309, by rfl⟩ : syracuseStep 96592825 = 72444619) B72444619
theorem B4514849 : Blo 1188411 4514849 := bstep (se 2 (by rfl) ⟨1693068, by rfl⟩ : syracuseStep 4514849 = 3386137) B3386137
theorem B3433513 : Blo 1188411 3433513 := bstep (se 2 (by rfl) ⟨1287567, by rfl⟩ : syracuseStep 3433513 = 2575135) B2575135
theorem B1188991 : Blo 1188411 1188991 := bstep (se 1 (by rfl) ⟨891743, by rfl⟩ : syracuseStep 1188991 = 1783487) B1783487
theorem B1189183 : Blo 1188411 1189183 := bstep (se 1 (by rfl) ⟨891887, by rfl⟩ : syracuseStep 1189183 = 1783775) B1783775
theorem B1189223 : Blo 1188411 1189223 := bstep (se 1 (by rfl) ⟨891917, by rfl⟩ : syracuseStep 1189223 = 1783835) B1783835
theorem B1189343 : Blo 1188411 1189343 := bstep (se 1 (by rfl) ⟨892007, by rfl⟩ : syracuseStep 1189343 = 1784015) B1784015
theorem B1189351 : Blo 1188411 1189351 := bstep (se 1 (by rfl) ⟨892013, by rfl⟩ : syracuseStep 1189351 = 1784027) B1784027
theorem B1189479 : Blo 1188411 1189479 := bstep (se 1 (by rfl) ⟨892109, by rfl⟩ : syracuseStep 1189479 = 1784219) B1784219
theorem B1189759 : Blo 1188411 1189759 := bstep (se 1 (by rfl) ⟨892319, by rfl⟩ : syracuseStep 1189759 = 1784639) B1784639
theorem B1189791 : Blo 1188411 1189791 := bstep (se 1 (by rfl) ⟨892343, by rfl⟩ : syracuseStep 1189791 = 1784687) B1784687
theorem B5711897 : Blo 1188411 5711897 := bstep (se 2 (by rfl) ⟨2141961, by rfl⟩ : syracuseStep 5711897 = 4283923) B4283923
theorem B1189951 : Blo 1188411 1189951 := bstep (se 1 (by rfl) ⟨892463, by rfl⟩ : syracuseStep 1189951 = 1784927) B1784927
theorem B1189991 : Blo 1188411 1189991 := bstep (se 1 (by rfl) ⟨892493, by rfl⟩ : syracuseStep 1189991 = 1784987) B1784987
theorem B3385567 : Blo 1188411 3385567 := bstep (se 1 (by rfl) ⟨2539175, by rfl⟩ : syracuseStep 3385567 = 5078351) B5078351
theorem B1337575 : Blo 1188411 1337575 := bstep (se 1 (by rfl) ⟨1003181, by rfl⟩ : syracuseStep 1337575 = 2006363) B2006363
theorem B6425039 : Blo 1188411 6425039 := bstep (se 1 (by rfl) ⟨4818779, by rfl⟩ : syracuseStep 6425039 = 9637559) B9637559
theorem B29338127 : Blo 1188411 29338127 := bstep (se 1 (by rfl) ⟨22003595, by rfl⟩ : syracuseStep 29338127 = 44007191) B44007191
theorem B1338223 : Blo 1188411 1338223 := bstep (se 1 (by rfl) ⟨1003667, by rfl⟩ : syracuseStep 1338223 = 2007335) B2007335
theorem B14461901 : Blo 1188411 14461901 := bstep (se 3 (by rfl) ⟨2711606, by rfl⟩ : syracuseStep 14461901 = 5423213) B5423213
theorem B14470163 : Blo 1188411 14470163 := bstep (se 1 (by rfl) ⟨10852622, by rfl⟩ : syracuseStep 14470163 = 21705245) B21705245
theorem B20868263 : Blo 1188411 20868263 := bstep (se 1 (by rfl) ⟨15651197, by rfl⟩ : syracuseStep 20868263 = 31302395) B31302395
theorem B6024617 : Blo 1188411 6024617 := bstep (se 2 (by rfl) ⟨2259231, by rfl⟩ : syracuseStep 6024617 = 4518463) B4518463
theorem B26070443 : Blo 1188411 26070443 := bstep (se 1 (by rfl) ⟨19552832, by rfl⟩ : syracuseStep 26070443 = 39105665) B39105665
theorem B1338907 : Blo 1188411 1338907 := bstep (se 1 (by rfl) ⟨1004180, by rfl⟩ : syracuseStep 1338907 = 2008361) B2008361
theorem B38563613 : Blo 1188411 38563613 := bstep (se 3 (by rfl) ⟨7230677, by rfl⟩ : syracuseStep 38563613 = 14461355) B14461355
theorem B2674529 : Blo 1188411 2674529 := bstep (se 2 (by rfl) ⟨1002948, by rfl⟩ : syracuseStep 2674529 = 2005897) B2005897
theorem B10858387 : Blo 1188411 10858387 := bstep (se 1 (by rfl) ⟨8143790, by rfl⟩ : syracuseStep 10858387 = 16287581) B16287581
theorem B3010729 : Blo 1188411 3010729 := bstep (se 2 (by rfl) ⟨1129023, by rfl⟩ : syracuseStep 3010729 = 2258047) B2258047
theorem B2257463 : Blo 1188411 2257463 := bstep (se 1 (by rfl) ⟨1693097, by rfl⟩ : syracuseStep 2257463 = 3386195) B3386195
theorem B5083991 : Blo 1188411 5083991 := bstep (se 1 (by rfl) ⟨3812993, by rfl⟩ : syracuseStep 5083991 = 7625987) B7625987
theorem B6026075 : Blo 1188411 6026075 := bstep (se 1 (by rfl) ⟨4519556, by rfl⟩ : syracuseStep 6026075 = 9039113) B9039113
theorem B1782761 : Blo 1188411 1782761 := bstep (se 2 (by rfl) ⟨668535, by rfl⟩ : syracuseStep 1782761 = 1337071) B1337071
theorem B10163231 : Blo 1188411 10163231 := bstep (se 1 (by rfl) ⟨7622423, by rfl⟩ : syracuseStep 10163231 = 15244847) B15244847
theorem B7230505 : Blo 1188411 7230505 := bstep (se 2 (by rfl) ⟨2711439, by rfl⟩ : syracuseStep 7230505 = 5422879) B5422879
theorem B1782905 : Blo 1188411 1782905 := bstep (se 2 (by rfl) ⟨668589, by rfl⟩ : syracuseStep 1782905 = 1337179) B1337179
theorem B22295839 : Blo 1188411 22295839 := bstep (se 1 (by rfl) ⟨16721879, by rfl⟩ : syracuseStep 22295839 = 33443759) B33443759
theorem B15250841 : Blo 1188411 15250841 := bstep (se 2 (by rfl) ⟨5719065, by rfl⟩ : syracuseStep 15250841 = 11438131) B11438131
theorem B4011551 : Blo 1188411 4011551 := bstep (se 1 (by rfl) ⟨3008663, by rfl⟩ : syracuseStep 4011551 = 6017327) B6017327
theorem B12850771 : Blo 1188411 12850771 := bstep (se 1 (by rfl) ⟨9638078, by rfl⟩ : syracuseStep 12850771 = 19276157) B19276157
theorem B1783679 : Blo 1188411 1783679 := bstep (se 1 (by rfl) ⟨1337759, by rfl⟩ : syracuseStep 1783679 = 2675519) B2675519
theorem B3012491 : Blo 1188411 3012491 := bstep (se 1 (by rfl) ⟨2259368, by rfl⟩ : syracuseStep 3012491 = 4518737) B4518737
theorem B2676671 : Blo 1188411 2676671 := bstep (se 1 (by rfl) ⟨2007503, by rfl⟩ : syracuseStep 2676671 = 4015007) B4015007
theorem B1783919 : Blo 1188411 1783919 := bstep (se 1 (by rfl) ⟨1337939, by rfl⟩ : syracuseStep 1783919 = 2675879) B2675879
theorem B2676923 : Blo 1188411 2676923 := bstep (se 1 (by rfl) ⟨2007692, by rfl⟩ : syracuseStep 2676923 = 4015385) B4015385
theorem B3389759 : Blo 1188411 3389759 := bstep (se 1 (by rfl) ⟨2542319, by rfl⟩ : syracuseStep 3389759 = 5084639) B5084639
theorem B3012947 : Blo 1188411 3012947 := bstep (se 1 (by rfl) ⟨2259710, by rfl⟩ : syracuseStep 3012947 = 4519421) B4519421
theorem B20339099 : Blo 1188411 20339099 := bstep (se 1 (by rfl) ⟨15254324, by rfl⟩ : syracuseStep 20339099 = 30508649) B30508649
theorem B1694299 : Blo 1188411 1694299 := bstep (se 1 (by rfl) ⟨1270724, by rfl⟩ : syracuseStep 1694299 = 2541449) B2541449
theorem B3054191 : Blo 1188411 3054191 := bstep (se 1 (by rfl) ⟨2290643, by rfl⟩ : syracuseStep 3054191 = 4581287) B4581287
theorem B5495609 : Blo 1188411 5495609 := bstep (se 2 (by rfl) ⟨2060853, by rfl⟩ : syracuseStep 5495609 = 4121707) B4121707
theorem B2677625 : Blo 1188411 2677625 := bstep (se 2 (by rfl) ⟨1004109, by rfl⟩ : syracuseStep 2677625 = 2008219) B2008219
theorem B4406251 : Blo 1188411 4406251 := bstep (se 1 (by rfl) ⟨3304688, by rfl⟩ : syracuseStep 4406251 = 6609377) B6609377
theorem B27851795 : Blo 1188411 27851795 := bstep (se 1 (by rfl) ⟨20888846, by rfl⟩ : syracuseStep 27851795 = 41777693) B41777693
theorem B4512905 : Blo 1188411 4512905 := bstep (se 2 (by rfl) ⟨1692339, by rfl⟩ : syracuseStep 4512905 = 3384679) B3384679
theorem B1784999 : Blo 1188411 1784999 := bstep (se 1 (by rfl) ⟨1338749, by rfl⟩ : syracuseStep 1784999 = 2677499) B2677499
theorem B1785143 : Blo 1188411 1785143 := bstep (se 1 (by rfl) ⟨1338857, by rfl⟩ : syracuseStep 1785143 = 2677715) B2677715
theorem B1785215 : Blo 1188411 1785215 := bstep (se 1 (by rfl) ⟨1338911, by rfl⟩ : syracuseStep 1785215 = 2677823) B2677823
theorem B2006687 : Blo 1188411 2006687 := bstep (se 1 (by rfl) ⟨1505015, by rfl⟩ : syracuseStep 2006687 = 3010031) B3010031
theorem B4014305 : Blo 1188411 4014305 := bstep (se 2 (by rfl) ⟨1505364, by rfl⟩ : syracuseStep 4014305 = 3010729) B3010729
theorem B4514089 : Blo 1188411 4514089 := bstep (se 2 (by rfl) ⟨1692783, by rfl⟩ : syracuseStep 4514089 = 3385567) B3385567
theorem B17138051 : Blo 1188411 17138051 := bstep (se 1 (by rfl) ⟨12853538, by rfl⟩ : syracuseStep 17138051 = 25707077) B25707077
theorem B17613395 : Blo 1188411 17613395 := bstep (se 1 (by rfl) ⟨13210046, by rfl⟩ : syracuseStep 17613395 = 26420093) B26420093
theorem B1188507 : Blo 1188411 1188507 := bstep (se 1 (by rfl) ⟨891380, by rfl⟩ : syracuseStep 1188507 = 1782761) B1782761
theorem B6775487 : Blo 1188411 6775487 := bstep (se 1 (by rfl) ⟨5081615, by rfl⟩ : syracuseStep 6775487 = 10163231) B10163231
theorem B1188603 : Blo 1188411 1188603 := bstep (se 1 (by rfl) ⟨891452, by rfl⟩ : syracuseStep 1188603 = 1782905) B1782905
theorem B10167227 : Blo 1188411 10167227 := bstep (se 1 (by rfl) ⟨7625420, by rfl⟩ : syracuseStep 10167227 = 15250841) B15250841
theorem B1189119 : Blo 1188411 1189119 := bstep (se 1 (by rfl) ⟨891839, by rfl⟩ : syracuseStep 1189119 = 1783679) B1783679
theorem B2008327 : Blo 1188411 2008327 := bstep (se 1 (by rfl) ⟨1506245, by rfl⟩ : syracuseStep 2008327 = 3012491) B3012491
theorem B5875001 : Blo 1188411 5875001 := bstep (se 2 (by rfl) ⟨2203125, by rfl⟩ : syracuseStep 5875001 = 4406251) B4406251
theorem B1189279 : Blo 1188411 1189279 := bstep (se 1 (by rfl) ⟨891959, by rfl⟩ : syracuseStep 1189279 = 1783919) B1783919
theorem B2008631 : Blo 1188411 2008631 := bstep (se 1 (by rfl) ⟨1506473, by rfl⟩ : syracuseStep 2008631 = 3012947) B3012947
theorem B13559399 : Blo 1188411 13559399 := bstep (se 1 (by rfl) ⟨10169549, by rfl⟩ : syracuseStep 13559399 = 20339099) B20339099
theorem B8144509 : Blo 1188411 8144509 := bstep (se 3 (by rfl) ⟨1527095, by rfl⟩ : syracuseStep 8144509 = 3054191) B3054191
theorem B3663739 : Blo 1188411 3663739 := bstep (se 1 (by rfl) ⟨2747804, by rfl⟩ : syracuseStep 3663739 = 5495609) B5495609
theorem B3008603 : Blo 1188411 3008603 := bstep (se 1 (by rfl) ⟨2256452, by rfl⟩ : syracuseStep 3008603 = 4512905) B4512905
theorem B13912175 : Blo 1188411 13912175 := bstep (se 1 (by rfl) ⟨10434131, by rfl⟩ : syracuseStep 13912175 = 20868263) B20868263
theorem B1189999 : Blo 1188411 1189999 := bstep (se 1 (by rfl) ⟨892499, by rfl⟩ : syracuseStep 1189999 = 1784999) B1784999
theorem B1190095 : Blo 1188411 1190095 := bstep (se 1 (by rfl) ⟨892571, by rfl⟩ : syracuseStep 1190095 = 1785143) B1785143
theorem B1190143 : Blo 1188411 1190143 := bstep (se 1 (by rfl) ⟨892607, by rfl⟩ : syracuseStep 1190143 = 1785215) B1785215
theorem B4016411 : Blo 1188411 4016411 := bstep (se 1 (by rfl) ⟨3012308, by rfl⟩ : syracuseStep 4016411 = 6024617) B6024617
theorem B1337791 : Blo 1188411 1337791 := bstep (se 1 (by rfl) ⟨1003343, by rfl⟩ : syracuseStep 1337791 = 2006687) B2006687
theorem B25709075 : Blo 1188411 25709075 := bstep (se 1 (by rfl) ⟨19281806, by rfl⟩ : syracuseStep 25709075 = 38563613) B38563613
theorem B14477849 : Blo 1188411 14477849 := bstep (se 2 (by rfl) ⟨5429193, by rfl⟩ : syracuseStep 14477849 = 10858387) B10858387
theorem B15231725 : Blo 1188411 15231725 := bstep (se 3 (by rfl) ⟨2855948, by rfl⟩ : syracuseStep 15231725 = 5711897) B5711897
theorem B5712839 : Blo 1188411 5712839 := bstep (se 1 (by rfl) ⟨4284629, by rfl⟩ : syracuseStep 5712839 = 8569259) B8569259
theorem B4017383 : Blo 1188411 4017383 := bstep (se 1 (by rfl) ⟨3013037, by rfl⟩ : syracuseStep 4017383 = 6026075) B6026075
theorem B3009899 : Blo 1188411 3009899 := bstep (se 1 (by rfl) ⟨2257424, by rfl⟩ : syracuseStep 3009899 = 4514849) B4514849
theorem B2674367 : Blo 1188411 2674367 := bstep (se 1 (by rfl) ⟨2005775, by rfl⟩ : syracuseStep 2674367 = 4011551) B4011551
theorem B17133437 : Blo 1188411 17133437 := bstep (se 3 (by rfl) ⟨3212519, by rfl⟩ : syracuseStep 17133437 = 6425039) B6425039
theorem B128790433 : Blo 1188411 128790433 := bstep (se 2 (by rfl) ⟨48296412, by rfl⟩ : syracuseStep 128790433 = 96592825) B96592825
theorem B19558751 : Blo 1188411 19558751 := bstep (se 1 (by rfl) ⟨14669063, by rfl⟩ : syracuseStep 19558751 = 29338127) B29338127
theorem B9646775 : Blo 1188411 9646775 := bstep (se 1 (by rfl) ⟨7235081, by rfl⟩ : syracuseStep 9646775 = 14470163) B14470163
theorem B18567863 : Blo 1188411 18567863 := bstep (se 1 (by rfl) ⟨13925897, by rfl⟩ : syracuseStep 18567863 = 27851795) B27851795
theorem B17134361 : Blo 1188411 17134361 := bstep (se 2 (by rfl) ⟨6425385, by rfl⟩ : syracuseStep 17134361 = 12850771) B12850771
theorem B17380295 : Blo 1188411 17380295 := bstep (se 1 (by rfl) ⟨13035221, by rfl⟩ : syracuseStep 17380295 = 26070443) B26070443
theorem B1783019 : Blo 1188411 1783019 := bstep (se 1 (by rfl) ⟨1337264, by rfl⟩ : syracuseStep 1783019 = 2674529) B2674529
theorem B8574331 : Blo 1188411 8574331 := bstep (se 1 (by rfl) ⟨6430748, by rfl⟩ : syracuseStep 8574331 = 12861497) B12861497
theorem B97703495 : Blo 1188411 97703495 := bstep (se 1 (by rfl) ⟨73277621, by rfl⟩ : syracuseStep 97703495 = 146555243) B146555243
theorem B1783433 : Blo 1188411 1783433 := bstep (se 2 (by rfl) ⟨668787, by rfl⟩ : syracuseStep 1783433 = 1337575) B1337575
theorem B1504975 : Blo 1188411 1504975 := bstep (se 1 (by rfl) ⟨1128731, by rfl⟩ : syracuseStep 1504975 = 2257463) B2257463
theorem B3389327 : Blo 1188411 3389327 := bstep (se 1 (by rfl) ⟨2541995, by rfl⟩ : syracuseStep 3389327 = 5083991) B5083991
theorem B2259065 : Blo 1188411 2259065 := bstep (se 2 (by rfl) ⟨847149, by rfl⟩ : syracuseStep 2259065 = 1694299) B1694299
theorem B1784297 : Blo 1188411 1784297 := bstep (se 2 (by rfl) ⟨669111, by rfl⟩ : syracuseStep 1784297 = 1338223) B1338223
theorem B1784447 : Blo 1188411 1784447 := bstep (se 1 (by rfl) ⟨1338335, by rfl⟩ : syracuseStep 1784447 = 2676671) B2676671
theorem B9640673 : Blo 1188411 9640673 := bstep (se 2 (by rfl) ⟨3615252, by rfl⟩ : syracuseStep 9640673 = 7230505) B7230505
theorem B4578017 : Blo 1188411 4578017 := bstep (se 2 (by rfl) ⟨1716756, by rfl⟩ : syracuseStep 4578017 = 3433513) B3433513
theorem B1784615 : Blo 1188411 1784615 := bstep (se 1 (by rfl) ⟨1338461, by rfl⟩ : syracuseStep 1784615 = 2676923) B2676923
theorem B2259839 : Blo 1188411 2259839 := bstep (se 1 (by rfl) ⟨1694879, by rfl⟩ : syracuseStep 2259839 = 3389759) B3389759
theorem B29727785 : Blo 1188411 29727785 := bstep (se 2 (by rfl) ⟨11147919, by rfl⟩ : syracuseStep 29727785 = 22295839) B22295839
theorem B1785083 : Blo 1188411 1785083 := bstep (se 1 (by rfl) ⟨1338812, by rfl⟩ : syracuseStep 1785083 = 2677625) B2677625
theorem B9641267 : Blo 1188411 9641267 := bstep (se 1 (by rfl) ⟨7230950, by rfl⟩ : syracuseStep 9641267 = 14461901) B14461901
theorem B1785209 : Blo 1188411 1785209 := bstep (se 2 (by rfl) ⟨669453, by rfl⟩ : syracuseStep 1785209 = 1338907) B1338907
theorem B6431183 : Blo 1188411 6431183 := bstep (se 1 (by rfl) ⟨4823387, by rfl⟩ : syracuseStep 6431183 = 9646775) B9646775
theorem B12378575 : Blo 1188411 12378575 := bstep (se 1 (by rfl) ⟨9283931, by rfl⟩ : syracuseStep 12378575 = 18567863) B18567863
theorem B1188679 : Blo 1188411 1188679 := bstep (se 1 (by rfl) ⟨891509, by rfl⟩ : syracuseStep 1188679 = 1783019) B1783019
theorem B3916667 : Blo 1188411 3916667 := bstep (se 1 (by rfl) ⟨2937500, by rfl⟩ : syracuseStep 3916667 = 5875001) B5875001
theorem B65135663 : Blo 1188411 65135663 := bstep (se 1 (by rfl) ⟨48851747, by rfl⟩ : syracuseStep 65135663 = 97703495) B97703495
theorem B1188955 : Blo 1188411 1188955 := bstep (se 1 (by rfl) ⟨891716, by rfl⟩ : syracuseStep 1188955 = 1783433) B1783433
theorem B9274783 : Blo 1188411 9274783 := bstep (se 1 (by rfl) ⟨6956087, by rfl⟩ : syracuseStep 9274783 = 13912175) B13912175
theorem B1189531 : Blo 1188411 1189531 := bstep (se 1 (by rfl) ⟨892148, by rfl⟩ : syracuseStep 1189531 = 1784297) B1784297
theorem B17139383 : Blo 1188411 17139383 := bstep (se 1 (by rfl) ⟨12854537, by rfl⟩ : syracuseStep 17139383 = 25709075) B25709075
theorem B9651899 : Blo 1188411 9651899 := bstep (se 1 (by rfl) ⟨7238924, by rfl⟩ : syracuseStep 9651899 = 14477849) B14477849
theorem B1189631 : Blo 1188411 1189631 := bstep (se 1 (by rfl) ⟨892223, by rfl⟩ : syracuseStep 1189631 = 1784447) B1784447
theorem B1189743 : Blo 1188411 1189743 := bstep (se 1 (by rfl) ⟨892307, by rfl⟩ : syracuseStep 1189743 = 1784615) B1784615
theorem B12208045 : Blo 1188411 12208045 := bstep (se 3 (by rfl) ⟨2289008, by rfl⟩ : syracuseStep 12208045 = 4578017) B4578017
theorem B19818523 : Blo 1188411 19818523 := bstep (se 1 (by rfl) ⟨14863892, by rfl⟩ : syracuseStep 19818523 = 29727785) B29727785
theorem B1190055 : Blo 1188411 1190055 := bstep (se 1 (by rfl) ⟨892541, by rfl⟩ : syracuseStep 1190055 = 1785083) B1785083
theorem B1190139 : Blo 1188411 1190139 := bstep (se 1 (by rfl) ⟨892604, by rfl⟩ : syracuseStep 1190139 = 1785209) B1785209
theorem B4884985 : Blo 1188411 4884985 := bstep (se 2 (by rfl) ⟨1831869, by rfl⟩ : syracuseStep 4884985 = 3663739) B3663739
theorem B11422291 : Blo 1188411 11422291 := bstep (se 1 (by rfl) ⟨8566718, by rfl⟩ : syracuseStep 11422291 = 17133437) B17133437
theorem B11742263 : Blo 1188411 11742263 := bstep (se 1 (by rfl) ⟨8806697, by rfl⟩ : syracuseStep 11742263 = 17613395) B17613395
theorem B4516991 : Blo 1188411 4516991 := bstep (se 1 (by rfl) ⟨3387743, by rfl⟩ : syracuseStep 4516991 = 6775487) B6775487
theorem B11422907 : Blo 1188411 11422907 := bstep (se 1 (by rfl) ⟨8567180, by rfl⟩ : syracuseStep 11422907 = 17134361) B17134361
theorem B6778151 : Blo 1188411 6778151 := bstep (se 1 (by rfl) ⟨5083613, by rfl⟩ : syracuseStep 6778151 = 10167227) B10167227
theorem B11586863 : Blo 1188411 11586863 := bstep (se 1 (by rfl) ⟨8690147, by rfl⟩ : syracuseStep 11586863 = 17380295) B17380295
theorem B1339087 : Blo 1188411 1339087 := bstep (se 1 (by rfl) ⟨1004315, by rfl⟩ : syracuseStep 1339087 = 2008631) B2008631
theorem B9039599 : Blo 1188411 9039599 := bstep (se 1 (by rfl) ⟨6779699, by rfl⟩ : syracuseStep 9039599 = 13559399) B13559399
theorem B6427115 : Blo 1188411 6427115 := bstep (se 1 (by rfl) ⟨4820336, by rfl⟩ : syracuseStep 6427115 = 9640673) B9640673
theorem B10154483 : Blo 1188411 10154483 := bstep (se 1 (by rfl) ⟨7615862, by rfl⟩ : syracuseStep 10154483 = 15231725) B15231725
theorem B11432441 : Blo 1188411 11432441 := bstep (se 2 (by rfl) ⟨4287165, by rfl⟩ : syracuseStep 11432441 = 8574331) B8574331
theorem B10859345 : Blo 1188411 10859345 := bstep (se 2 (by rfl) ⟨4072254, by rfl⟩ : syracuseStep 10859345 = 8144509) B8144509
theorem B6427511 : Blo 1188411 6427511 := bstep (se 1 (by rfl) ⟨4820633, by rfl⟩ : syracuseStep 6427511 = 9641267) B9641267
theorem B6026237 : Blo 1188411 6026237 := bstep (se 3 (by rfl) ⟨1129919, by rfl⟩ : syracuseStep 6026237 = 2259839) B2259839
theorem B1782911 : Blo 1188411 1782911 := bstep (se 1 (by rfl) ⟨1337183, by rfl⟩ : syracuseStep 1782911 = 2674367) B2674367
theorem B2676203 : Blo 1188411 2676203 := bstep (se 1 (by rfl) ⟨2007152, by rfl⟩ : syracuseStep 2676203 = 4014305) B4014305
theorem B11425367 : Blo 1188411 11425367 := bstep (se 1 (by rfl) ⟨8569025, by rfl⟩ : syracuseStep 11425367 = 17138051) B17138051
theorem B6018785 : Blo 1188411 6018785 := bstep (se 2 (by rfl) ⟨2257044, by rfl⟩ : syracuseStep 6018785 = 4514089) B4514089
theorem B1783721 : Blo 1188411 1783721 := bstep (se 2 (by rfl) ⟨668895, by rfl⟩ : syracuseStep 1783721 = 1337791) B1337791
theorem B52156669 : Blo 1188411 52156669 := bstep (se 3 (by rfl) ⟨9779375, by rfl⟩ : syracuseStep 52156669 = 19558751) B19558751
theorem B2259551 : Blo 1188411 2259551 := bstep (se 1 (by rfl) ⟨1694663, by rfl⟩ : syracuseStep 2259551 = 3389327) B3389327
theorem B2005735 : Blo 1188411 2005735 := bstep (se 1 (by rfl) ⟨1504301, by rfl⟩ : syracuseStep 2005735 = 3008603) B3008603
theorem B1506043 : Blo 1188411 1506043 := bstep (se 1 (by rfl) ⟨1129532, by rfl⟩ : syracuseStep 1506043 = 2259065) B2259065
theorem B2677607 : Blo 1188411 2677607 := bstep (se 1 (by rfl) ⟨2008205, by rfl⟩ : syracuseStep 2677607 = 4016411) B4016411
theorem B2677769 : Blo 1188411 2677769 := bstep (se 2 (by rfl) ⟨1004163, by rfl⟩ : syracuseStep 2677769 = 2008327) B2008327
theorem B3808559 : Blo 1188411 3808559 := bstep (se 1 (by rfl) ⟨2856419, by rfl⟩ : syracuseStep 3808559 = 5712839) B5712839
theorem B2678255 : Blo 1188411 2678255 := bstep (se 1 (by rfl) ⟨2008691, by rfl⟩ : syracuseStep 2678255 = 4017383) B4017383
theorem B2006599 : Blo 1188411 2006599 := bstep (se 1 (by rfl) ⟨1504949, by rfl⟩ : syracuseStep 2006599 = 3009899) B3009899
theorem B2006633 : Blo 1188411 2006633 := bstep (se 2 (by rfl) ⟨752487, by rfl⟩ : syracuseStep 2006633 = 1504975) B1504975
theorem B171720577 : Blo 1188411 171720577 := bstep (se 2 (by rfl) ⟨64395216, by rfl⟩ : syracuseStep 171720577 = 128790433) B128790433
theorem B4284743 : Blo 1188411 4284743 := bstep (se 1 (by rfl) ⟨3213557, by rfl⟩ : syracuseStep 4284743 = 6427115) B6427115
theorem B69542225 : Blo 1188411 69542225 := bstep (se 2 (by rfl) ⟨26078334, by rfl⟩ : syracuseStep 69542225 = 52156669) B52156669
theorem B4285007 : Blo 1188411 4285007 := bstep (se 1 (by rfl) ⟨3213755, by rfl⟩ : syracuseStep 4285007 = 6427511) B6427511
theorem B1188607 : Blo 1188411 1188607 := bstep (se 1 (by rfl) ⟨891455, by rfl⟩ : syracuseStep 1188607 = 1782911) B1782911
theorem B15229721 : Blo 1188411 15229721 := bstep (se 2 (by rfl) ⟨5711145, by rfl⟩ : syracuseStep 15229721 = 11422291) B11422291
theorem B2008057 : Blo 1188411 2008057 := bstep (se 2 (by rfl) ⟨753021, by rfl⟩ : syracuseStep 2008057 = 1506043) B1506043
theorem B1189147 : Blo 1188411 1189147 := bstep (se 1 (by rfl) ⟨891860, by rfl⟩ : syracuseStep 1189147 = 1783721) B1783721
theorem B1337755 : Blo 1188411 1337755 := bstep (se 1 (by rfl) ⟨1003316, by rfl⟩ : syracuseStep 1337755 = 2006633) B2006633
theorem B228960769 : Blo 1188411 228960769 := bstep (se 2 (by rfl) ⟨85860288, by rfl⟩ : syracuseStep 228960769 = 171720577) B171720577
theorem B26053253 : Blo 1188411 26053253 := bstep (se 4 (by rfl) ⟨2442492, by rfl⟩ : syracuseStep 26053253 = 4884985) B4884985
theorem B4287455 : Blo 1188411 4287455 := bstep (se 1 (by rfl) ⟨3215591, by rfl⟩ : syracuseStep 4287455 = 6431183) B6431183
theorem B8252383 : Blo 1188411 8252383 := bstep (se 1 (by rfl) ⟨6189287, by rfl⟩ : syracuseStep 8252383 = 12378575) B12378575
theorem B6769655 : Blo 1188411 6769655 := bstep (se 1 (by rfl) ⟨5077241, by rfl⟩ : syracuseStep 6769655 = 10154483) B10154483
theorem B7621627 : Blo 1188411 7621627 := bstep (se 1 (by rfl) ⟨5716220, by rfl⟩ : syracuseStep 7621627 = 11432441) B11432441
theorem B4017491 : Blo 1188411 4017491 := bstep (se 1 (by rfl) ⟨3013118, by rfl⟩ : syracuseStep 4017491 = 6026237) B6026237
theorem B2674313 : Blo 1188411 2674313 := bstep (se 2 (by rfl) ⟨1002867, by rfl⟩ : syracuseStep 2674313 = 2005735) B2005735
theorem B6434599 : Blo 1188411 6434599 := bstep (se 1 (by rfl) ⟨4825949, by rfl⟩ : syracuseStep 6434599 = 9651899) B9651899
theorem B12366377 : Blo 1188411 12366377 := bstep (se 2 (by rfl) ⟨4637391, by rfl⟩ : syracuseStep 12366377 = 9274783) B9274783
theorem B7828175 : Blo 1188411 7828175 := bstep (se 1 (by rfl) ⟨5871131, by rfl⟩ : syracuseStep 7828175 = 11742263) B11742263
theorem B3011327 : Blo 1188411 3011327 := bstep (se 1 (by rfl) ⟨2258495, by rfl⟩ : syracuseStep 3011327 = 4516991) B4516991
theorem B2675465 : Blo 1188411 2675465 := bstep (se 2 (by rfl) ⟨1003299, by rfl⟩ : syracuseStep 2675465 = 2006599) B2006599
theorem B7615271 : Blo 1188411 7615271 := bstep (se 1 (by rfl) ⟨5711453, by rfl⟩ : syracuseStep 7615271 = 11422907) B11422907
theorem B4518767 : Blo 1188411 4518767 := bstep (se 1 (by rfl) ⟨3389075, by rfl⟩ : syracuseStep 4518767 = 6778151) B6778151
theorem B6026399 : Blo 1188411 6026399 := bstep (se 1 (by rfl) ⟨4519799, by rfl⟩ : syracuseStep 6026399 = 9039599) B9039599
theorem B105698789 : Blo 1188411 105698789 := bstep (se 4 (by rfl) ⟨9909261, by rfl⟩ : syracuseStep 105698789 = 19818523) B19818523
theorem B7239563 : Blo 1188411 7239563 := bstep (se 1 (by rfl) ⟨5429672, by rfl⟩ : syracuseStep 7239563 = 10859345) B10859345
theorem B2611111 : Blo 1188411 2611111 := bstep (se 1 (by rfl) ⟨1958333, by rfl⟩ : syracuseStep 2611111 = 3916667) B3916667
theorem B43423775 : Blo 1188411 43423775 := bstep (se 1 (by rfl) ⟨32567831, by rfl⟩ : syracuseStep 43423775 = 65135663) B65135663
theorem B1784135 : Blo 1188411 1784135 := bstep (se 1 (by rfl) ⟨1338101, by rfl⟩ : syracuseStep 1784135 = 2676203) B2676203
theorem B7616911 : Blo 1188411 7616911 := bstep (se 1 (by rfl) ⟨5712683, by rfl⟩ : syracuseStep 7616911 = 11425367) B11425367
theorem B11426255 : Blo 1188411 11426255 := bstep (se 1 (by rfl) ⟨8569691, by rfl⟩ : syracuseStep 11426255 = 17139383) B17139383
theorem B4012523 : Blo 1188411 4012523 := bstep (se 1 (by rfl) ⟨3009392, by rfl⟩ : syracuseStep 4012523 = 6018785) B6018785
theorem B1506367 : Blo 1188411 1506367 := bstep (se 1 (by rfl) ⟨1129775, by rfl⟩ : syracuseStep 1506367 = 2259551) B2259551
theorem B1785071 : Blo 1188411 1785071 := bstep (se 1 (by rfl) ⟨1338803, by rfl⟩ : syracuseStep 1785071 = 2677607) B2677607
theorem B1785179 : Blo 1188411 1785179 := bstep (se 1 (by rfl) ⟨1338884, by rfl⟩ : syracuseStep 1785179 = 2677769) B2677769
theorem B2539039 : Blo 1188411 2539039 := bstep (se 1 (by rfl) ⟨1904279, by rfl⟩ : syracuseStep 2539039 = 3808559) B3808559
theorem B7724575 : Blo 1188411 7724575 := bstep (se 1 (by rfl) ⟨5793431, by rfl⟩ : syracuseStep 7724575 = 11586863) B11586863
theorem B1785449 : Blo 1188411 1785449 := bstep (se 2 (by rfl) ⟨669543, by rfl⟩ : syracuseStep 1785449 = 1339087) B1339087
theorem B1785503 : Blo 1188411 1785503 := bstep (se 1 (by rfl) ⟨1339127, by rfl⟩ : syracuseStep 1785503 = 2678255) B2678255
theorem B16277393 : Blo 1188411 16277393 := bstep (se 2 (by rfl) ⟨6104022, by rfl⟩ : syracuseStep 16277393 = 12208045) B12208045
theorem B2007551 : Blo 1188411 2007551 := bstep (se 1 (by rfl) ⟨1505663, by rfl⟩ : syracuseStep 2007551 = 3011327) B3011327
theorem B45703925 : Blo 1188411 45703925 := bstep (se 5 (by rfl) ⟨2142371, by rfl⟩ : syracuseStep 45703925 = 4284743) B4284743
theorem B4826375 : Blo 1188411 4826375 := bstep (se 1 (by rfl) ⟨3619781, by rfl⟩ : syracuseStep 4826375 = 7239563) B7239563
theorem B11003177 : Blo 1188411 11003177 := bstep (se 2 (by rfl) ⟨4126191, by rfl⟩ : syracuseStep 11003177 = 8252383) B8252383
theorem B2008489 : Blo 1188411 2008489 := bstep (se 2 (by rfl) ⟨753183, by rfl⟩ : syracuseStep 2008489 = 1506367) B1506367
theorem B1189423 : Blo 1188411 1189423 := bstep (se 1 (by rfl) ⟨892067, by rfl⟩ : syracuseStep 1189423 = 1784135) B1784135
theorem B17368835 : Blo 1188411 17368835 := bstep (se 1 (by rfl) ⟨13026626, by rfl⟩ : syracuseStep 17368835 = 26053253) B26053253
theorem B20875133 : Blo 1188411 20875133 := bstep (se 3 (by rfl) ⟨3914087, by rfl⟩ : syracuseStep 20875133 = 7828175) B7828175
theorem B3385385 : Blo 1188411 3385385 := bstep (se 2 (by rfl) ⟨1269519, by rfl⟩ : syracuseStep 3385385 = 2539039) B2539039
theorem B10299433 : Blo 1188411 10299433 := bstep (se 2 (by rfl) ⟨3862287, by rfl⟩ : syracuseStep 10299433 = 7724575) B7724575
theorem B1190047 : Blo 1188411 1190047 := bstep (se 1 (by rfl) ⟨892535, by rfl⟩ : syracuseStep 1190047 = 1785071) B1785071
theorem B1190119 : Blo 1188411 1190119 := bstep (se 1 (by rfl) ⟨892589, by rfl⟩ : syracuseStep 1190119 = 1785179) B1785179
theorem B8579465 : Blo 1188411 8579465 := bstep (se 2 (by rfl) ⟨3217299, by rfl⟩ : syracuseStep 8579465 = 6434599) B6434599
theorem B1190299 : Blo 1188411 1190299 := bstep (se 1 (by rfl) ⟨892724, by rfl⟩ : syracuseStep 1190299 = 1785449) B1785449
theorem B1190335 : Blo 1188411 1190335 := bstep (se 1 (by rfl) ⟨892751, by rfl⟩ : syracuseStep 1190335 = 1785503) B1785503
theorem B46361483 : Blo 1188411 46361483 := bstep (se 1 (by rfl) ⟨34771112, by rfl⟩ : syracuseStep 46361483 = 69542225) B69542225
theorem B8244251 : Blo 1188411 8244251 := bstep (se 1 (by rfl) ⟨6183188, by rfl⟩ : syracuseStep 8244251 = 12366377) B12366377
theorem B10153147 : Blo 1188411 10153147 := bstep (se 1 (by rfl) ⟨7614860, by rfl⟩ : syracuseStep 10153147 = 15229721) B15229721
theorem B4017599 : Blo 1188411 4017599 := bstep (se 1 (by rfl) ⟨3013199, by rfl⟩ : syracuseStep 4017599 = 6026399) B6026399
theorem B10162169 : Blo 1188411 10162169 := bstep (se 2 (by rfl) ⟨3810813, by rfl⟩ : syracuseStep 10162169 = 7621627) B7621627
theorem B2675015 : Blo 1188411 2675015 := bstep (se 1 (by rfl) ⟨2006261, by rfl⟩ : syracuseStep 2675015 = 4012523) B4012523
theorem B43406381 : Blo 1188411 43406381 := bstep (se 3 (by rfl) ⟨8138696, by rfl⟩ : syracuseStep 43406381 = 16277393) B16277393
theorem B1782875 : Blo 1188411 1782875 := bstep (se 1 (by rfl) ⟨1337156, by rfl⟩ : syracuseStep 1782875 = 2674313) B2674313
theorem B2856671 : Blo 1188411 2856671 := bstep (se 1 (by rfl) ⟨2142503, by rfl⟩ : syracuseStep 2856671 = 4285007) B4285007
theorem B1783643 : Blo 1188411 1783643 := bstep (se 1 (by rfl) ⟨1337732, by rfl⟩ : syracuseStep 1783643 = 2675465) B2675465
theorem B10155881 : Blo 1188411 10155881 := bstep (se 2 (by rfl) ⟨3808455, by rfl⟩ : syracuseStep 10155881 = 7616911) B7616911
theorem B5076847 : Blo 1188411 5076847 := bstep (se 1 (by rfl) ⟨3807635, by rfl⟩ : syracuseStep 5076847 = 7615271) B7615271
theorem B1783673 : Blo 1188411 1783673 := bstep (se 2 (by rfl) ⟨668877, by rfl⟩ : syracuseStep 1783673 = 1337755) B1337755
theorem B3012511 : Blo 1188411 3012511 := bstep (se 1 (by rfl) ⟨2259383, by rfl⟩ : syracuseStep 3012511 = 4518767) B4518767
theorem B305281025 : Blo 1188411 305281025 := bstep (se 2 (by rfl) ⟨114480384, by rfl⟩ : syracuseStep 305281025 = 228960769) B228960769
theorem B70465859 : Blo 1188411 70465859 := bstep (se 1 (by rfl) ⟨52849394, by rfl⟩ : syracuseStep 70465859 = 105698789) B105698789
theorem B2677409 : Blo 1188411 2677409 := bstep (se 2 (by rfl) ⟨1004028, by rfl⟩ : syracuseStep 2677409 = 2008057) B2008057
theorem B28949183 : Blo 1188411 28949183 := bstep (se 1 (by rfl) ⟨21711887, by rfl⟩ : syracuseStep 28949183 = 43423775) B43423775
theorem B7617503 : Blo 1188411 7617503 := bstep (se 1 (by rfl) ⟨5713127, by rfl⟩ : syracuseStep 7617503 = 11426255) B11426255
theorem B2858303 : Blo 1188411 2858303 := bstep (se 1 (by rfl) ⟨2143727, by rfl⟩ : syracuseStep 2858303 = 4287455) B4287455
theorem B4513103 : Blo 1188411 4513103 := bstep (se 1 (by rfl) ⟨3384827, by rfl⟩ : syracuseStep 4513103 = 6769655) B6769655
theorem B2678327 : Blo 1188411 2678327 := bstep (se 1 (by rfl) ⟨2008745, by rfl⟩ : syracuseStep 2678327 = 4017491) B4017491
theorem B3481481 : Blo 1188411 3481481 := bstep (se 2 (by rfl) ⟨1305555, by rfl⟩ : syracuseStep 3481481 = 2611111) B2611111
theorem B1188583 : Blo 1188411 1188583 := bstep (se 1 (by rfl) ⟨891437, by rfl⟩ : syracuseStep 1188583 = 1782875) B1782875
theorem B1189095 : Blo 1188411 1189095 := bstep (se 1 (by rfl) ⟨891821, by rfl⟩ : syracuseStep 1189095 = 1783643) B1783643
theorem B1189115 : Blo 1188411 1189115 := bstep (se 1 (by rfl) ⟨891836, by rfl⟩ : syracuseStep 1189115 = 1783673) B1783673
theorem B5719643 : Blo 1188411 5719643 := bstep (se 1 (by rfl) ⟨4289732, by rfl⟩ : syracuseStep 5719643 = 8579465) B8579465
theorem B3008735 : Blo 1188411 3008735 := bstep (se 1 (by rfl) ⟨2256551, by rfl⟩ : syracuseStep 3008735 = 4513103) B4513103
theorem B9283949 : Blo 1188411 9283949 := bstep (se 3 (by rfl) ⟨1740740, by rfl⟩ : syracuseStep 9283949 = 3481481) B3481481
theorem B6769129 : Blo 1188411 6769129 := bstep (se 2 (by rfl) ⟨2538423, by rfl⟩ : syracuseStep 6769129 = 5076847) B5076847
theorem B4016681 : Blo 1188411 4016681 := bstep (se 2 (by rfl) ⟨1506255, by rfl⟩ : syracuseStep 4016681 = 3012511) B3012511
theorem B13732577 : Blo 1188411 13732577 := bstep (se 2 (by rfl) ⟨5149716, by rfl⟩ : syracuseStep 13732577 = 10299433) B10299433
theorem B1338367 : Blo 1188411 1338367 := bstep (se 1 (by rfl) ⟨1003775, by rfl⟩ : syracuseStep 1338367 = 2007551) B2007551
theorem B30469283 : Blo 1188411 30469283 := bstep (se 1 (by rfl) ⟨22851962, by rfl⟩ : syracuseStep 30469283 = 45703925) B45703925
theorem B28937587 : Blo 1188411 28937587 := bstep (se 1 (by rfl) ⟨21703190, by rfl⟩ : syracuseStep 28937587 = 43406381) B43406381
theorem B7335451 : Blo 1188411 7335451 := bstep (se 1 (by rfl) ⟨5501588, by rfl⟩ : syracuseStep 7335451 = 11003177) B11003177
theorem B1904447 : Blo 1188411 1904447 := bstep (se 1 (by rfl) ⟨1428335, by rfl⟩ : syracuseStep 1904447 = 2856671) B2856671
theorem B6770587 : Blo 1188411 6770587 := bstep (se 1 (by rfl) ⟨5077940, by rfl⟩ : syracuseStep 6770587 = 10155881) B10155881
theorem B2256923 : Blo 1188411 2256923 := bstep (se 1 (by rfl) ⟨1692692, by rfl⟩ : syracuseStep 2256923 = 3385385) B3385385
theorem B46977239 : Blo 1188411 46977239 := bstep (se 1 (by rfl) ⟨35232929, by rfl⟩ : syracuseStep 46977239 = 70465859) B70465859
theorem B13537529 : Blo 1188411 13537529 := bstep (se 2 (by rfl) ⟨5076573, by rfl⟩ : syracuseStep 13537529 = 10153147) B10153147
theorem B1905535 : Blo 1188411 1905535 := bstep (se 1 (by rfl) ⟨1429151, by rfl⟩ : syracuseStep 1905535 = 2858303) B2858303
theorem B185267573 : Blo 1188411 185267573 := bstep (se 5 (by rfl) ⟨8684417, by rfl⟩ : syracuseStep 185267573 = 17368835) B17368835
theorem B1783343 : Blo 1188411 1783343 := bstep (se 1 (by rfl) ⟨1337507, by rfl⟩ : syracuseStep 1783343 = 2675015) B2675015
theorem B3217583 : Blo 1188411 3217583 := bstep (se 1 (by rfl) ⟨2413187, by rfl⟩ : syracuseStep 3217583 = 4826375) B4826375
theorem B13916755 : Blo 1188411 13916755 := bstep (se 1 (by rfl) ⟨10437566, by rfl⟩ : syracuseStep 13916755 = 20875133) B20875133
theorem B203520683 : Blo 1188411 203520683 := bstep (se 1 (by rfl) ⟨152640512, by rfl⟩ : syracuseStep 203520683 = 305281025) B305281025
theorem B1784939 : Blo 1188411 1784939 := bstep (se 1 (by rfl) ⟨1338704, by rfl⟩ : syracuseStep 1784939 = 2677409) B2677409
theorem B19299455 : Blo 1188411 19299455 := bstep (se 1 (by rfl) ⟨14474591, by rfl⟩ : syracuseStep 19299455 = 28949183) B28949183
theorem B2677985 : Blo 1188411 2677985 := bstep (se 2 (by rfl) ⟨1004244, by rfl⟩ : syracuseStep 2677985 = 2008489) B2008489
theorem B30907655 : Blo 1188411 30907655 := bstep (se 1 (by rfl) ⟨23180741, by rfl⟩ : syracuseStep 30907655 = 46361483) B46361483
theorem B5078335 : Blo 1188411 5078335 := bstep (se 1 (by rfl) ⟨3808751, by rfl⟩ : syracuseStep 5078335 = 7617503) B7617503
theorem B5496167 : Blo 1188411 5496167 := bstep (se 1 (by rfl) ⟨4122125, by rfl⟩ : syracuseStep 5496167 = 8244251) B8244251
theorem B2678399 : Blo 1188411 2678399 := bstep (se 1 (by rfl) ⟨2008799, by rfl⟩ : syracuseStep 2678399 = 4017599) B4017599
theorem B1785551 : Blo 1188411 1785551 := bstep (se 1 (by rfl) ⟨1339163, by rfl⟩ : syracuseStep 1785551 = 2678327) B2678327
theorem B6774779 : Blo 1188411 6774779 := bstep (se 1 (by rfl) ⟨5081084, by rfl⟩ : syracuseStep 6774779 = 10162169) B10162169
theorem B31318159 : Blo 1188411 31318159 := bstep (se 1 (by rfl) ⟨23488619, by rfl⟩ : syracuseStep 31318159 = 46977239) B46977239
theorem B18555673 : Blo 1188411 18555673 := bstep (se 2 (by rfl) ⟨6958377, by rfl⟩ : syracuseStep 18555673 = 13916755) B13916755
theorem B123511715 : Blo 1188411 123511715 := bstep (se 1 (by rfl) ⟨92633786, by rfl⟩ : syracuseStep 123511715 = 185267573) B185267573
theorem B1188895 : Blo 1188411 1188895 := bstep (se 1 (by rfl) ⟨891671, by rfl⟩ : syracuseStep 1188895 = 1783343) B1783343
theorem B1189959 : Blo 1188411 1189959 := bstep (se 1 (by rfl) ⟨892469, by rfl⟩ : syracuseStep 1189959 = 1784939) B1784939
theorem B20605103 : Blo 1188411 20605103 := bstep (se 1 (by rfl) ⟨15453827, by rfl⟩ : syracuseStep 20605103 = 30907655) B30907655
theorem B3664111 : Blo 1188411 3664111 := bstep (se 1 (by rfl) ⟨2748083, by rfl⟩ : syracuseStep 3664111 = 5496167) B5496167
theorem B1190367 : Blo 1188411 1190367 := bstep (se 1 (by rfl) ⟨892775, by rfl⟩ : syracuseStep 1190367 = 1785551) B1785551
theorem B4516519 : Blo 1188411 4516519 := bstep (se 1 (by rfl) ⟨3387389, by rfl⟩ : syracuseStep 4516519 = 6774779) B6774779
theorem B3813095 : Blo 1188411 3813095 := bstep (se 1 (by rfl) ⟨2859821, by rfl⟩ : syracuseStep 3813095 = 5719643) B5719643
theorem B6189299 : Blo 1188411 6189299 := bstep (se 1 (by rfl) ⟨4641974, by rfl⟩ : syracuseStep 6189299 = 9283949) B9283949
theorem B6771113 : Blo 1188411 6771113 := bstep (se 2 (by rfl) ⟨2539167, by rfl⟩ : syracuseStep 6771113 = 5078335) B5078335
theorem B135680455 : Blo 1188411 135680455 := bstep (se 1 (by rfl) ⟨101760341, by rfl⟩ : syracuseStep 135680455 = 203520683) B203520683
theorem B9155051 : Blo 1188411 9155051 := bstep (se 1 (by rfl) ⟨6866288, by rfl⟩ : syracuseStep 9155051 = 13732577) B13732577
theorem B10162853 : Blo 1188411 10162853 := bstep (se 4 (by rfl) ⟨952767, by rfl⟩ : syracuseStep 10162853 = 1905535) B1905535
theorem B12866303 : Blo 1188411 12866303 := bstep (se 1 (by rfl) ⟨9649727, by rfl⟩ : syracuseStep 12866303 = 19299455) B19299455
theorem B20312855 : Blo 1188411 20312855 := bstep (se 1 (by rfl) ⟨15234641, by rfl⟩ : syracuseStep 20312855 = 30469283) B30469283
theorem B6018461 : Blo 1188411 6018461 := bstep (se 3 (by rfl) ⟨1128461, by rfl⟩ : syracuseStep 6018461 = 2256923) B2256923
theorem B9025019 : Blo 1188411 9025019 := bstep (se 1 (by rfl) ⟨6768764, by rfl⟩ : syracuseStep 9025019 = 13537529) B13537529
theorem B9025505 : Blo 1188411 9025505 := bstep (se 2 (by rfl) ⟨3384564, by rfl⟩ : syracuseStep 9025505 = 6769129) B6769129
theorem B1784489 : Blo 1188411 1784489 := bstep (se 2 (by rfl) ⟨669183, by rfl⟩ : syracuseStep 1784489 = 1338367) B1338367
theorem B2145055 : Blo 1188411 2145055 := bstep (se 1 (by rfl) ⟨1608791, by rfl⟩ : syracuseStep 2145055 = 3217583) B3217583
theorem B2005823 : Blo 1188411 2005823 := bstep (se 1 (by rfl) ⟨1504367, by rfl⟩ : syracuseStep 2005823 = 3008735) B3008735
theorem B2677787 : Blo 1188411 2677787 := bstep (se 1 (by rfl) ⟨2008340, by rfl⟩ : syracuseStep 2677787 = 4016681) B4016681
theorem B38583449 : Blo 1188411 38583449 := bstep (se 2 (by rfl) ⟨14468793, by rfl⟩ : syracuseStep 38583449 = 28937587) B28937587
theorem B9780601 : Blo 1188411 9780601 := bstep (se 2 (by rfl) ⟨3667725, by rfl⟩ : syracuseStep 9780601 = 7335451) B7335451
theorem B1785323 : Blo 1188411 1785323 := bstep (se 1 (by rfl) ⟨1338992, by rfl⟩ : syracuseStep 1785323 = 2677985) B2677985
theorem B1785599 : Blo 1188411 1785599 := bstep (se 1 (by rfl) ⟨1339199, by rfl⟩ : syracuseStep 1785599 = 2678399) B2678399
theorem B9027449 : Blo 1188411 9027449 := bstep (se 2 (by rfl) ⟨3385293, by rfl⟩ : syracuseStep 9027449 = 6770587) B6770587
theorem B1269631 : Blo 1188411 1269631 := bstep (se 1 (by rfl) ⟨952223, by rfl⟩ : syracuseStep 1269631 = 1904447) B1904447
theorem B4514075 : Blo 1188411 4514075 := bstep (se 1 (by rfl) ⟨3385556, by rfl⟩ : syracuseStep 4514075 = 6771113) B6771113
theorem B6103367 : Blo 1188411 6103367 := bstep (se 1 (by rfl) ⟨4577525, by rfl⟩ : syracuseStep 6103367 = 9155051) B9155051
theorem B6775235 : Blo 1188411 6775235 := bstep (se 1 (by rfl) ⟨5081426, by rfl⟩ : syracuseStep 6775235 = 10162853) B10162853
theorem B8577535 : Blo 1188411 8577535 := bstep (se 1 (by rfl) ⟨6433151, by rfl⟩ : syracuseStep 8577535 = 12866303) B12866303
theorem B13541903 : Blo 1188411 13541903 := bstep (se 1 (by rfl) ⟨10156427, by rfl⟩ : syracuseStep 13541903 = 20312855) B20312855
theorem B6022025 : Blo 1188411 6022025 := bstep (se 2 (by rfl) ⟨2258259, by rfl⟩ : syracuseStep 6022025 = 4516519) B4516519
theorem B24740897 : Blo 1188411 24740897 := bstep (se 2 (by rfl) ⟨9277836, by rfl⟩ : syracuseStep 24740897 = 18555673) B18555673
theorem B2860073 : Blo 1188411 2860073 := bstep (se 2 (by rfl) ⟨1072527, by rfl⟩ : syracuseStep 2860073 = 2145055) B2145055
theorem B1189659 : Blo 1188411 1189659 := bstep (se 1 (by rfl) ⟨892244, by rfl⟩ : syracuseStep 1189659 = 1784489) B1784489
theorem B1337215 : Blo 1188411 1337215 := bstep (se 1 (by rfl) ⟨1002911, by rfl⟩ : syracuseStep 1337215 = 2005823) B2005823
theorem B10168253 : Blo 1188411 10168253 := bstep (se 3 (by rfl) ⟨1906547, by rfl⟩ : syracuseStep 10168253 = 3813095) B3813095
theorem B1190215 : Blo 1188411 1190215 := bstep (se 1 (by rfl) ⟨892661, by rfl⟩ : syracuseStep 1190215 = 1785323) B1785323
theorem B1190399 : Blo 1188411 1190399 := bstep (se 1 (by rfl) ⟨892799, by rfl⟩ : syracuseStep 1190399 = 1785599) B1785599
theorem B41757545 : Blo 1188411 41757545 := bstep (se 2 (by rfl) ⟨15659079, by rfl⟩ : syracuseStep 41757545 = 31318159) B31318159
theorem B4885481 : Blo 1188411 4885481 := bstep (se 2 (by rfl) ⟨1832055, by rfl⟩ : syracuseStep 4885481 = 3664111) B3664111
theorem B180907273 : Blo 1188411 180907273 := bstep (se 2 (by rfl) ⟨67840227, by rfl⟩ : syracuseStep 180907273 = 135680455) B135680455
theorem B82341143 : Blo 1188411 82341143 := bstep (se 1 (by rfl) ⟨61755857, by rfl⟩ : syracuseStep 82341143 = 123511715) B123511715
theorem B6016679 : Blo 1188411 6016679 := bstep (se 1 (by rfl) ⟨4512509, by rfl⟩ : syracuseStep 6016679 = 9025019) B9025019
theorem B6017003 : Blo 1188411 6017003 := bstep (se 1 (by rfl) ⟨4512752, by rfl⟩ : syracuseStep 6017003 = 9025505) B9025505
theorem B1692841 : Blo 1188411 1692841 := bstep (se 2 (by rfl) ⟨634815, by rfl⟩ : syracuseStep 1692841 = 1269631) B1269631
theorem B6018299 : Blo 1188411 6018299 := bstep (se 1 (by rfl) ⟨4513724, by rfl⟩ : syracuseStep 6018299 = 9027449) B9027449
theorem B4126199 : Blo 1188411 4126199 := bstep (se 1 (by rfl) ⟨3094649, by rfl⟩ : syracuseStep 4126199 = 6189299) B6189299
theorem B4012307 : Blo 1188411 4012307 := bstep (se 1 (by rfl) ⟨3009230, by rfl⟩ : syracuseStep 4012307 = 6018461) B6018461
theorem B13736735 : Blo 1188411 13736735 := bstep (se 1 (by rfl) ⟨10302551, by rfl⟩ : syracuseStep 13736735 = 20605103) B20605103
theorem B13040801 : Blo 1188411 13040801 := bstep (se 2 (by rfl) ⟨4890300, by rfl⟩ : syracuseStep 13040801 = 9780601) B9780601
theorem B1785191 : Blo 1188411 1785191 := bstep (se 1 (by rfl) ⟨1338893, by rfl⟩ : syracuseStep 1785191 = 2677787) B2677787
theorem B25722299 : Blo 1188411 25722299 := bstep (se 1 (by rfl) ⟨19291724, by rfl⟩ : syracuseStep 25722299 = 38583449) B38583449
theorem B9027935 : Blo 1188411 9027935 := bstep (se 1 (by rfl) ⟨6770951, by rfl⟩ : syracuseStep 9027935 = 13541903) B13541903
theorem B4014683 : Blo 1188411 4014683 := bstep (se 1 (by rfl) ⟨3011012, by rfl⟩ : syracuseStep 4014683 = 6022025) B6022025
theorem B11436713 : Blo 1188411 11436713 := bstep (se 2 (by rfl) ⟨4288767, by rfl⟩ : syracuseStep 11436713 = 8577535) B8577535
theorem B8693867 : Blo 1188411 8693867 := bstep (se 1 (by rfl) ⟨6520400, by rfl⟩ : syracuseStep 8693867 = 13040801) B13040801
theorem B1190127 : Blo 1188411 1190127 := bstep (se 1 (by rfl) ⟨892595, by rfl⟩ : syracuseStep 1190127 = 1785191) B1785191
theorem B17148199 : Blo 1188411 17148199 := bstep (se 1 (by rfl) ⟨12861149, by rfl⟩ : syracuseStep 17148199 = 25722299) B25722299
theorem B13027949 : Blo 1188411 13027949 := bstep (se 3 (by rfl) ⟨2442740, by rfl⟩ : syracuseStep 13027949 = 4885481) B4885481
theorem B3009383 : Blo 1188411 3009383 := bstep (se 1 (by rfl) ⟨2257037, by rfl⟩ : syracuseStep 3009383 = 4514075) B4514075
theorem B4516823 : Blo 1188411 4516823 := bstep (se 1 (by rfl) ⟨3387617, by rfl⟩ : syracuseStep 4516823 = 6775235) B6775235
theorem B6778835 : Blo 1188411 6778835 := bstep (se 1 (by rfl) ⟨5084126, by rfl⟩ : syracuseStep 6778835 = 10168253) B10168253
theorem B2674871 : Blo 1188411 2674871 := bstep (se 1 (by rfl) ⟨2006153, by rfl⟩ : syracuseStep 2674871 = 4012307) B4012307
theorem B2257121 : Blo 1188411 2257121 := bstep (se 2 (by rfl) ⟨846420, by rfl⟩ : syracuseStep 2257121 = 1692841) B1692841
theorem B241209697 : Blo 1188411 241209697 := bstep (se 2 (by rfl) ⟨90453636, by rfl⟩ : syracuseStep 241209697 = 180907273) B180907273
theorem B4011119 : Blo 1188411 4011119 := bstep (se 1 (by rfl) ⟨3008339, by rfl⟩ : syracuseStep 4011119 = 6016679) B6016679
theorem B1782953 : Blo 1188411 1782953 := bstep (se 2 (by rfl) ⟨668607, by rfl⟩ : syracuseStep 1782953 = 1337215) B1337215
theorem B44012789 : Blo 1188411 44012789 := bstep (se 5 (by rfl) ⟨2063099, by rfl⟩ : syracuseStep 44012789 = 4126199) B4126199
theorem B4011335 : Blo 1188411 4011335 := bstep (se 1 (by rfl) ⟨3008501, by rfl⟩ : syracuseStep 4011335 = 6017003) B6017003
theorem B65975725 : Blo 1188411 65975725 := bstep (se 3 (by rfl) ⟨12370448, by rfl⟩ : syracuseStep 65975725 = 24740897) B24740897
theorem B4068911 : Blo 1188411 4068911 := bstep (se 1 (by rfl) ⟨3051683, by rfl⟩ : syracuseStep 4068911 = 6103367) B6103367
theorem B1906715 : Blo 1188411 1906715 := bstep (se 1 (by rfl) ⟨1430036, by rfl⟩ : syracuseStep 1906715 = 2860073) B2860073
theorem B4012199 : Blo 1188411 4012199 := bstep (se 1 (by rfl) ⟨3009149, by rfl⟩ : syracuseStep 4012199 = 6018299) B6018299
theorem B9157823 : Blo 1188411 9157823 := bstep (se 1 (by rfl) ⟨6868367, by rfl⟩ : syracuseStep 9157823 = 13736735) B13736735
theorem B54894095 : Blo 1188411 54894095 := bstep (se 1 (by rfl) ⟨41170571, by rfl⟩ : syracuseStep 54894095 = 82341143) B82341143
theorem B111353453 : Blo 1188411 111353453 := bstep (se 3 (by rfl) ⟨20878772, by rfl⟩ : syracuseStep 111353453 = 41757545) B41757545
theorem B22864265 : Blo 1188411 22864265 := bstep (se 2 (by rfl) ⟨8574099, by rfl⟩ : syracuseStep 22864265 = 17148199) B17148199
theorem B1188635 : Blo 1188411 1188635 := bstep (se 1 (by rfl) ⟨891476, by rfl⟩ : syracuseStep 1188635 = 1782953) B1782953
theorem B1271143 : Blo 1188411 1271143 := bstep (se 1 (by rfl) ⟨953357, by rfl⟩ : syracuseStep 1271143 = 1906715) B1906715
theorem B8685299 : Blo 1188411 8685299 := bstep (se 1 (by rfl) ⟨6513974, by rfl⟩ : syracuseStep 8685299 = 13027949) B13027949
theorem B87967633 : Blo 1188411 87967633 := bstep (se 2 (by rfl) ⟨32987862, by rfl⟩ : syracuseStep 87967633 = 65975725) B65975725
theorem B6105215 : Blo 1188411 6105215 := bstep (se 1 (by rfl) ⟨4578911, by rfl⟩ : syracuseStep 6105215 = 9157823) B9157823
theorem B36596063 : Blo 1188411 36596063 := bstep (se 1 (by rfl) ⟨27447047, by rfl⟩ : syracuseStep 36596063 = 54894095) B54894095
theorem B321612929 : Blo 1188411 321612929 := bstep (se 2 (by rfl) ⟨120604848, by rfl⟩ : syracuseStep 321612929 = 241209697) B241209697
theorem B2674079 : Blo 1188411 2674079 := bstep (se 1 (by rfl) ⟨2005559, by rfl⟩ : syracuseStep 2674079 = 4011119) B4011119
theorem B2674223 : Blo 1188411 2674223 := bstep (se 1 (by rfl) ⟨2005667, by rfl⟩ : syracuseStep 2674223 = 4011335) B4011335
theorem B5795911 : Blo 1188411 5795911 := bstep (se 1 (by rfl) ⟨4346933, by rfl⟩ : syracuseStep 5795911 = 8693867) B8693867
theorem B2674799 : Blo 1188411 2674799 := bstep (se 1 (by rfl) ⟨2006099, by rfl⟩ : syracuseStep 2674799 = 4012199) B4012199
theorem B10850429 : Blo 1188411 10850429 := bstep (se 3 (by rfl) ⟨2034455, by rfl⟩ : syracuseStep 10850429 = 4068911) B4068911
theorem B3011215 : Blo 1188411 3011215 := bstep (se 1 (by rfl) ⟨2258411, by rfl⟩ : syracuseStep 3011215 = 4516823) B4516823
theorem B4519223 : Blo 1188411 4519223 := bstep (se 1 (by rfl) ⟨3389417, by rfl⟩ : syracuseStep 4519223 = 6778835) B6778835
theorem B1783247 : Blo 1188411 1783247 := bstep (se 1 (by rfl) ⟨1337435, by rfl⟩ : syracuseStep 1783247 = 2674871) B2674871
theorem B1504747 : Blo 1188411 1504747 := bstep (se 1 (by rfl) ⟨1128560, by rfl⟩ : syracuseStep 1504747 = 2257121) B2257121
theorem B6018623 : Blo 1188411 6018623 := bstep (se 1 (by rfl) ⟨4513967, by rfl⟩ : syracuseStep 6018623 = 9027935) B9027935
theorem B2676455 : Blo 1188411 2676455 := bstep (se 1 (by rfl) ⟨2007341, by rfl⟩ : syracuseStep 2676455 = 4014683) B4014683
theorem B7624475 : Blo 1188411 7624475 := bstep (se 1 (by rfl) ⟨5718356, by rfl⟩ : syracuseStep 7624475 = 11436713) B11436713
theorem B29341859 : Blo 1188411 29341859 := bstep (se 1 (by rfl) ⟨22006394, by rfl⟩ : syracuseStep 29341859 = 44012789) B44012789
theorem B2006255 : Blo 1188411 2006255 := bstep (se 1 (by rfl) ⟨1504691, by rfl⟩ : syracuseStep 2006255 = 3009383) B3009383
theorem B74235635 : Blo 1188411 74235635 := bstep (se 1 (by rfl) ⟨55676726, by rfl⟩ : syracuseStep 74235635 = 111353453) B111353453
theorem B7233619 : Blo 1188411 7233619 := bstep (se 1 (by rfl) ⟨5425214, by rfl⟩ : syracuseStep 7233619 = 10850429) B10850429
theorem B4014953 : Blo 1188411 4014953 := bstep (se 2 (by rfl) ⟨1505607, by rfl⟩ : syracuseStep 4014953 = 3011215) B3011215
theorem B1188831 : Blo 1188411 1188831 := bstep (se 1 (by rfl) ⟨891623, by rfl⟩ : syracuseStep 1188831 = 1783247) B1783247
theorem B24397375 : Blo 1188411 24397375 := bstep (se 1 (by rfl) ⟨18298031, by rfl⟩ : syracuseStep 24397375 = 36596063) B36596063
theorem B1337503 : Blo 1188411 1337503 := bstep (se 1 (by rfl) ⟨1003127, by rfl⟩ : syracuseStep 1337503 = 2006255) B2006255
theorem B49490423 : Blo 1188411 49490423 := bstep (se 1 (by rfl) ⟨37117817, by rfl⟩ : syracuseStep 49490423 = 74235635) B74235635
theorem B7727881 : Blo 1188411 7727881 := bstep (se 2 (by rfl) ⟨2897955, by rfl⟩ : syracuseStep 7727881 = 5795911) B5795911
theorem B78244957 : Blo 1188411 78244957 := bstep (se 3 (by rfl) ⟨14670929, by rfl⟩ : syracuseStep 78244957 = 29341859) B29341859
theorem B5082983 : Blo 1188411 5082983 := bstep (se 1 (by rfl) ⟨3812237, by rfl⟩ : syracuseStep 5082983 = 7624475) B7624475
theorem B1782719 : Blo 1188411 1782719 := bstep (se 1 (by rfl) ⟨1337039, by rfl⟩ : syracuseStep 1782719 = 2674079) B2674079
theorem B1782815 : Blo 1188411 1782815 := bstep (se 1 (by rfl) ⟨1337111, by rfl⟩ : syracuseStep 1782815 = 2674223) B2674223
theorem B117290177 : Blo 1188411 117290177 := bstep (se 2 (by rfl) ⟨43983816, by rfl⟩ : syracuseStep 117290177 = 87967633) B87967633
theorem B1783199 : Blo 1188411 1783199 := bstep (se 1 (by rfl) ⟨1337399, by rfl⟩ : syracuseStep 1783199 = 2674799) B2674799
theorem B15242843 : Blo 1188411 15242843 := bstep (se 1 (by rfl) ⟨11432132, by rfl⟩ : syracuseStep 15242843 = 22864265) B22864265
theorem B3012815 : Blo 1188411 3012815 := bstep (se 1 (by rfl) ⟨2259611, by rfl⟩ : syracuseStep 3012815 = 4519223) B4519223
theorem B4012415 : Blo 1188411 4012415 := bstep (se 1 (by rfl) ⟨3009311, by rfl⟩ : syracuseStep 4012415 = 6018623) B6018623
theorem B1784303 : Blo 1188411 1784303 := bstep (se 1 (by rfl) ⟨1338227, by rfl⟩ : syracuseStep 1784303 = 2676455) B2676455
theorem B5790199 : Blo 1188411 5790199 := bstep (se 1 (by rfl) ⟨4342649, by rfl⟩ : syracuseStep 5790199 = 8685299) B8685299
theorem B4070143 : Blo 1188411 4070143 := bstep (se 1 (by rfl) ⟨3052607, by rfl⟩ : syracuseStep 4070143 = 6105215) B6105215
theorem B1694857 : Blo 1188411 1694857 := bstep (se 2 (by rfl) ⟨635571, by rfl⟩ : syracuseStep 1694857 = 1271143) B1271143
theorem B2006329 : Blo 1188411 2006329 := bstep (se 2 (by rfl) ⟨752373, by rfl⟩ : syracuseStep 2006329 = 1504747) B1504747
theorem B214408619 : Blo 1188411 214408619 := bstep (se 1 (by rfl) ⟨160806464, by rfl⟩ : syracuseStep 214408619 = 321612929) B321612929
theorem B1188479 : Blo 1188411 1188479 := bstep (se 1 (by rfl) ⟨891359, by rfl⟩ : syracuseStep 1188479 = 1782719) B1782719
theorem B1188543 : Blo 1188411 1188543 := bstep (se 1 (by rfl) ⟨891407, by rfl⟩ : syracuseStep 1188543 = 1782815) B1782815
theorem B78193451 : Blo 1188411 78193451 := bstep (se 1 (by rfl) ⟨58645088, by rfl⟩ : syracuseStep 78193451 = 117290177) B117290177
theorem B1188799 : Blo 1188411 1188799 := bstep (se 1 (by rfl) ⟨891599, by rfl⟩ : syracuseStep 1188799 = 1783199) B1783199
theorem B2008543 : Blo 1188411 2008543 := bstep (se 1 (by rfl) ⟨1506407, by rfl⟩ : syracuseStep 2008543 = 3012815) B3012815
theorem B1189535 : Blo 1188411 1189535 := bstep (se 1 (by rfl) ⟨892151, by rfl⟩ : syracuseStep 1189535 = 1784303) B1784303
theorem B9644825 : Blo 1188411 9644825 := bstep (se 2 (by rfl) ⟨3616809, by rfl⟩ : syracuseStep 9644825 = 7233619) B7233619
theorem B7720265 : Blo 1188411 7720265 := bstep (se 2 (by rfl) ⟨2895099, by rfl⟩ : syracuseStep 7720265 = 5790199) B5790199
theorem B5426857 : Blo 1188411 5426857 := bstep (se 2 (by rfl) ⟨2035071, by rfl⟩ : syracuseStep 5426857 = 4070143) B4070143
theorem B10161895 : Blo 1188411 10161895 := bstep (se 1 (by rfl) ⟨7621421, by rfl⟩ : syracuseStep 10161895 = 15242843) B15242843
theorem B2674943 : Blo 1188411 2674943 := bstep (se 1 (by rfl) ⟨2006207, by rfl⟩ : syracuseStep 2674943 = 4012415) B4012415
theorem B32993615 : Blo 1188411 32993615 := bstep (se 1 (by rfl) ⟨24745211, by rfl⟩ : syracuseStep 32993615 = 49490423) B49490423
theorem B2675105 : Blo 1188411 2675105 := bstep (se 2 (by rfl) ⟨1003164, by rfl⟩ : syracuseStep 2675105 = 2006329) B2006329
theorem B142939079 : Blo 1188411 142939079 := bstep (se 1 (by rfl) ⟨107204309, by rfl⟩ : syracuseStep 142939079 = 214408619) B214408619
theorem B3388655 : Blo 1188411 3388655 := bstep (se 1 (by rfl) ⟨2541491, by rfl⟩ : syracuseStep 3388655 = 5082983) B5082983
theorem B1783337 : Blo 1188411 1783337 := bstep (se 2 (by rfl) ⟨668751, by rfl⟩ : syracuseStep 1783337 = 1337503) B1337503
theorem B417306437 : Blo 1188411 417306437 := bstep (se 4 (by rfl) ⟨39122478, by rfl⟩ : syracuseStep 417306437 = 78244957) B78244957
theorem B2676635 : Blo 1188411 2676635 := bstep (se 1 (by rfl) ⟨2007476, by rfl⟩ : syracuseStep 2676635 = 4014953) B4014953
theorem B10303841 : Blo 1188411 10303841 := bstep (se 2 (by rfl) ⟨3863940, by rfl⟩ : syracuseStep 10303841 = 7727881) B7727881
theorem B2259809 : Blo 1188411 2259809 := bstep (se 2 (by rfl) ⟨847428, by rfl⟩ : syracuseStep 2259809 = 1694857) B1694857
theorem B32529833 : Blo 1188411 32529833 := bstep (se 2 (by rfl) ⟨12198687, by rfl⟩ : syracuseStep 32529833 = 24397375) B24397375
theorem B87982973 : Blo 1188411 87982973 := bstep (se 3 (by rfl) ⟨16496807, by rfl⟩ : syracuseStep 87982973 = 32993615) B32993615
theorem B28943237 : Blo 1188411 28943237 := bstep (se 4 (by rfl) ⟨2713428, by rfl⟩ : syracuseStep 28943237 = 5426857) B5426857
theorem B1188891 : Blo 1188411 1188891 := bstep (se 1 (by rfl) ⟨891668, by rfl⟩ : syracuseStep 1188891 = 1783337) B1783337
theorem B5146843 : Blo 1188411 5146843 := bstep (se 1 (by rfl) ⟨3860132, by rfl⟩ : syracuseStep 5146843 = 7720265) B7720265
theorem B21686555 : Blo 1188411 21686555 := bstep (se 1 (by rfl) ⟨16264916, by rfl⟩ : syracuseStep 21686555 = 32529833) B32529833
theorem B52128967 : Blo 1188411 52128967 := bstep (se 1 (by rfl) ⟨39096725, by rfl⟩ : syracuseStep 52128967 = 78193451) B78193451
theorem B95292719 : Blo 1188411 95292719 := bstep (se 1 (by rfl) ⟨71469539, by rfl⟩ : syracuseStep 95292719 = 142939079) B142939079
theorem B278204291 : Blo 1188411 278204291 := bstep (se 1 (by rfl) ⟨208653218, by rfl⟩ : syracuseStep 278204291 = 417306437) B417306437
theorem B6869227 : Blo 1188411 6869227 := bstep (se 1 (by rfl) ⟨5151920, by rfl⟩ : syracuseStep 6869227 = 10303841) B10303841
theorem B1783295 : Blo 1188411 1783295 := bstep (se 1 (by rfl) ⟨1337471, by rfl⟩ : syracuseStep 1783295 = 2674943) B2674943
theorem B1783403 : Blo 1188411 1783403 := bstep (se 1 (by rfl) ⟨1337552, by rfl⟩ : syracuseStep 1783403 = 2675105) B2675105
theorem B2259103 : Blo 1188411 2259103 := bstep (se 1 (by rfl) ⟨1694327, by rfl⟩ : syracuseStep 2259103 = 3388655) B3388655
theorem B1784423 : Blo 1188411 1784423 := bstep (se 1 (by rfl) ⟨1338317, by rfl⟩ : syracuseStep 1784423 = 2676635) B2676635
theorem B6429883 : Blo 1188411 6429883 := bstep (se 1 (by rfl) ⟨4822412, by rfl⟩ : syracuseStep 6429883 = 9644825) B9644825
theorem B1506539 : Blo 1188411 1506539 := bstep (se 1 (by rfl) ⟨1129904, by rfl⟩ : syracuseStep 1506539 = 2259809) B2259809
theorem B2678057 : Blo 1188411 2678057 := bstep (se 2 (by rfl) ⟨1004271, by rfl⟩ : syracuseStep 2678057 = 2008543) B2008543
theorem B13549193 : Blo 1188411 13549193 := bstep (se 2 (by rfl) ⟨5080947, by rfl⟩ : syracuseStep 13549193 = 10161895) B10161895
theorem B9158969 : Blo 1188411 9158969 := bstep (se 2 (by rfl) ⟨3434613, by rfl⟩ : syracuseStep 9158969 = 6869227) B6869227
theorem B58655315 : Blo 1188411 58655315 := bstep (se 1 (by rfl) ⟨43991486, by rfl⟩ : syracuseStep 58655315 = 87982973) B87982973
theorem B1188863 : Blo 1188411 1188863 := bstep (se 1 (by rfl) ⟨891647, by rfl⟩ : syracuseStep 1188863 = 1783295) B1783295
theorem B1188935 : Blo 1188411 1188935 := bstep (se 1 (by rfl) ⟨891701, by rfl⟩ : syracuseStep 1188935 = 1783403) B1783403
theorem B1189615 : Blo 1188411 1189615 := bstep (se 1 (by rfl) ⟨892211, by rfl⟩ : syracuseStep 1189615 = 1784423) B1784423
theorem B185469527 : Blo 1188411 185469527 := bstep (se 1 (by rfl) ⟨139102145, by rfl⟩ : syracuseStep 185469527 = 278204291) B278204291
theorem B19295491 : Blo 1188411 19295491 := bstep (se 1 (by rfl) ⟨14471618, by rfl⟩ : syracuseStep 19295491 = 28943237) B28943237
theorem B4017437 : Blo 1188411 4017437 := bstep (se 3 (by rfl) ⟨753269, by rfl⟩ : syracuseStep 4017437 = 1506539) B1506539
theorem B8573177 : Blo 1188411 8573177 := bstep (se 2 (by rfl) ⟨3214941, by rfl⟩ : syracuseStep 8573177 = 6429883) B6429883
theorem B69505289 : Blo 1188411 69505289 := bstep (se 2 (by rfl) ⟨26064483, by rfl⟩ : syracuseStep 69505289 = 52128967) B52128967
theorem B9032795 : Blo 1188411 9032795 := bstep (se 1 (by rfl) ⟨6774596, by rfl⟩ : syracuseStep 9032795 = 13549193) B13549193
theorem B3012137 : Blo 1188411 3012137 := bstep (se 2 (by rfl) ⟨1129551, by rfl⟩ : syracuseStep 3012137 = 2259103) B2259103
theorem B6862457 : Blo 1188411 6862457 := bstep (se 2 (by rfl) ⟨2573421, by rfl⟩ : syracuseStep 6862457 = 5146843) B5146843
theorem B14457703 : Blo 1188411 14457703 := bstep (se 1 (by rfl) ⟨10843277, by rfl⟩ : syracuseStep 14457703 = 21686555) B21686555
theorem B1785371 : Blo 1188411 1785371 := bstep (se 1 (by rfl) ⟨1339028, by rfl⟩ : syracuseStep 1785371 = 2678057) B2678057
theorem B63528479 : Blo 1188411 63528479 := bstep (se 1 (by rfl) ⟨47646359, by rfl⟩ : syracuseStep 63528479 = 95292719) B95292719
theorem B6021863 : Blo 1188411 6021863 := bstep (se 1 (by rfl) ⟨4516397, by rfl⟩ : syracuseStep 6021863 = 9032795) B9032795
theorem B2008091 : Blo 1188411 2008091 := bstep (se 1 (by rfl) ⟨1506068, by rfl⟩ : syracuseStep 2008091 = 3012137) B3012137
theorem B19276937 : Blo 1188411 19276937 := bstep (se 2 (by rfl) ⟨7228851, by rfl⟩ : syracuseStep 19276937 = 14457703) B14457703
theorem B1190247 : Blo 1188411 1190247 := bstep (se 1 (by rfl) ⟨892685, by rfl⟩ : syracuseStep 1190247 = 1785371) B1785371
theorem B46336859 : Blo 1188411 46336859 := bstep (se 1 (by rfl) ⟨34752644, by rfl⟩ : syracuseStep 46336859 = 69505289) B69505289
theorem B6105979 : Blo 1188411 6105979 := bstep (se 1 (by rfl) ⟨4579484, by rfl⟩ : syracuseStep 6105979 = 9158969) B9158969
theorem B39103543 : Blo 1188411 39103543 := bstep (se 1 (by rfl) ⟨29327657, by rfl⟩ : syracuseStep 39103543 = 58655315) B58655315
theorem B4574971 : Blo 1188411 4574971 := bstep (se 1 (by rfl) ⟨3431228, by rfl⟩ : syracuseStep 4574971 = 6862457) B6862457
theorem B25727321 : Blo 1188411 25727321 := bstep (se 2 (by rfl) ⟨9647745, by rfl⟩ : syracuseStep 25727321 = 19295491) B19295491
theorem B123646351 : Blo 1188411 123646351 := bstep (se 1 (by rfl) ⟨92734763, by rfl⟩ : syracuseStep 123646351 = 185469527) B185469527
theorem B5715451 : Blo 1188411 5715451 := bstep (se 1 (by rfl) ⟨4286588, by rfl⟩ : syracuseStep 5715451 = 8573177) B8573177
theorem B2678291 : Blo 1188411 2678291 := bstep (se 1 (by rfl) ⟨2008718, by rfl⟩ : syracuseStep 2678291 = 4017437) B4017437
theorem B42352319 : Blo 1188411 42352319 := bstep (se 1 (by rfl) ⟨31764239, by rfl⟩ : syracuseStep 42352319 = 63528479) B63528479
theorem B208552229 : Blo 1188411 208552229 := bstep (se 4 (by rfl) ⟨19551771, by rfl⟩ : syracuseStep 208552229 = 39103543) B39103543
theorem B4014575 : Blo 1188411 4014575 := bstep (se 1 (by rfl) ⟨3010931, by rfl⟩ : syracuseStep 4014575 = 6021863) B6021863
theorem B1338727 : Blo 1188411 1338727 := bstep (se 1 (by rfl) ⟨1004045, by rfl⟩ : syracuseStep 1338727 = 2008091) B2008091
theorem B112939517 : Blo 1188411 112939517 := bstep (se 3 (by rfl) ⟨21176159, by rfl⟩ : syracuseStep 112939517 = 42352319) B42352319
theorem B6099961 : Blo 1188411 6099961 := bstep (se 2 (by rfl) ⟨2287485, by rfl⟩ : syracuseStep 6099961 = 4574971) B4574971
theorem B17151547 : Blo 1188411 17151547 := bstep (se 1 (by rfl) ⟨12863660, by rfl⟩ : syracuseStep 17151547 = 25727321) B25727321
theorem B164861801 : Blo 1188411 164861801 := bstep (se 2 (by rfl) ⟨61823175, by rfl⟩ : syracuseStep 164861801 = 123646351) B123646351
theorem B12851291 : Blo 1188411 12851291 := bstep (se 1 (by rfl) ⟨9638468, by rfl⟩ : syracuseStep 12851291 = 19276937) B19276937
theorem B8141305 : Blo 1188411 8141305 := bstep (se 2 (by rfl) ⟨3052989, by rfl⟩ : syracuseStep 8141305 = 6105979) B6105979
theorem B30891239 : Blo 1188411 30891239 := bstep (se 1 (by rfl) ⟨23168429, by rfl⟩ : syracuseStep 30891239 = 46336859) B46336859
theorem B1785527 : Blo 1188411 1785527 := bstep (se 1 (by rfl) ⟨1339145, by rfl⟩ : syracuseStep 1785527 = 2678291) B2678291
theorem B30482405 : Blo 1188411 30482405 := bstep (se 4 (by rfl) ⟨2857725, by rfl⟩ : syracuseStep 30482405 = 5715451) B5715451
theorem B139034819 : Blo 1188411 139034819 := bstep (se 1 (by rfl) ⟨104276114, by rfl⟩ : syracuseStep 139034819 = 208552229) B208552229
theorem B75293011 : Blo 1188411 75293011 := bstep (se 1 (by rfl) ⟨56469758, by rfl⟩ : syracuseStep 75293011 = 112939517) B112939517
theorem B10855073 : Blo 1188411 10855073 := bstep (se 2 (by rfl) ⟨4070652, by rfl⟩ : syracuseStep 10855073 = 8141305) B8141305
theorem B1190351 : Blo 1188411 1190351 := bstep (se 1 (by rfl) ⟨892763, by rfl⟩ : syracuseStep 1190351 = 1785527) B1785527
theorem B109907867 : Blo 1188411 109907867 := bstep (se 1 (by rfl) ⟨82430900, by rfl⟩ : syracuseStep 109907867 = 164861801) B164861801
theorem B22868729 : Blo 1188411 22868729 := bstep (se 2 (by rfl) ⟨8575773, by rfl⟩ : syracuseStep 22868729 = 17151547) B17151547
theorem B20321603 : Blo 1188411 20321603 := bstep (se 1 (by rfl) ⟨15241202, by rfl⟩ : syracuseStep 20321603 = 30482405) B30482405
theorem B2676383 : Blo 1188411 2676383 := bstep (se 1 (by rfl) ⟨2007287, by rfl⟩ : syracuseStep 2676383 = 4014575) B4014575
theorem B8133281 : Blo 1188411 8133281 := bstep (se 2 (by rfl) ⟨3049980, by rfl⟩ : syracuseStep 8133281 = 6099961) B6099961
theorem B8567527 : Blo 1188411 8567527 := bstep (se 1 (by rfl) ⟨6425645, by rfl⟩ : syracuseStep 8567527 = 12851291) B12851291
theorem B1784969 : Blo 1188411 1784969 := bstep (se 2 (by rfl) ⟨669363, by rfl⟩ : syracuseStep 1784969 = 1338727) B1338727
theorem B20594159 : Blo 1188411 20594159 := bstep (se 1 (by rfl) ⟨15445619, by rfl⟩ : syracuseStep 20594159 = 30891239) B30891239
theorem B15245819 : Blo 1188411 15245819 := bstep (se 1 (by rfl) ⟨11434364, by rfl⟩ : syracuseStep 15245819 = 22868729) B22868729
theorem B1189979 : Blo 1188411 1189979 := bstep (se 1 (by rfl) ⟨892484, by rfl⟩ : syracuseStep 1189979 = 1784969) B1784969
theorem B73271911 : Blo 1188411 73271911 := bstep (se 1 (by rfl) ⟨54953933, by rfl⟩ : syracuseStep 73271911 = 109907867) B109907867
theorem B7236715 : Blo 1188411 7236715 := bstep (se 1 (by rfl) ⟨5427536, by rfl⟩ : syracuseStep 7236715 = 10855073) B10855073
theorem B11423369 : Blo 1188411 11423369 := bstep (se 2 (by rfl) ⟨4283763, by rfl⟩ : syracuseStep 11423369 = 8567527) B8567527
theorem B92689879 : Blo 1188411 92689879 := bstep (se 1 (by rfl) ⟨69517409, by rfl⟩ : syracuseStep 92689879 = 139034819) B139034819
theorem B100390681 : Blo 1188411 100390681 := bstep (se 2 (by rfl) ⟨37646505, by rfl⟩ : syracuseStep 100390681 = 75293011) B75293011
theorem B13547735 : Blo 1188411 13547735 := bstep (se 1 (by rfl) ⟨10160801, by rfl⟩ : syracuseStep 13547735 = 20321603) B20321603
theorem B1784255 : Blo 1188411 1784255 := bstep (se 1 (by rfl) ⟨1338191, by rfl⟩ : syracuseStep 1784255 = 2676383) B2676383
theorem B5422187 : Blo 1188411 5422187 := bstep (se 1 (by rfl) ⟨4066640, by rfl⟩ : syracuseStep 5422187 = 8133281) B8133281
theorem B13729439 : Blo 1188411 13729439 := bstep (se 1 (by rfl) ⟨10297079, by rfl⟩ : syracuseStep 13729439 = 20594159) B20594159
theorem B1189503 : Blo 1188411 1189503 := bstep (se 1 (by rfl) ⟨892127, by rfl⟩ : syracuseStep 1189503 = 1784255) B1784255
theorem B123586505 : Blo 1188411 123586505 := bstep (se 2 (by rfl) ⟨46344939, by rfl⟩ : syracuseStep 123586505 = 92689879) B92689879
theorem B3614791 : Blo 1188411 3614791 := bstep (se 1 (by rfl) ⟨2711093, by rfl⟩ : syracuseStep 3614791 = 5422187) B5422187
theorem B9152959 : Blo 1188411 9152959 := bstep (se 1 (by rfl) ⟨6864719, by rfl⟩ : syracuseStep 9152959 = 13729439) B13729439
theorem B9031823 : Blo 1188411 9031823 := bstep (se 1 (by rfl) ⟨6773867, by rfl⟩ : syracuseStep 9031823 = 13547735) B13547735
theorem B133854241 : Blo 1188411 133854241 := bstep (se 2 (by rfl) ⟨50195340, by rfl⟩ : syracuseStep 133854241 = 100390681) B100390681
theorem B7615579 : Blo 1188411 7615579 := bstep (se 1 (by rfl) ⟨5711684, by rfl⟩ : syracuseStep 7615579 = 11423369) B11423369
theorem B10163879 : Blo 1188411 10163879 := bstep (se 1 (by rfl) ⟨7622909, by rfl⟩ : syracuseStep 10163879 = 15245819) B15245819
theorem B97695881 : Blo 1188411 97695881 := bstep (se 2 (by rfl) ⟨36635955, by rfl⟩ : syracuseStep 97695881 = 73271911) B73271911
theorem B9648953 : Blo 1188411 9648953 := bstep (se 2 (by rfl) ⟨3618357, by rfl⟩ : syracuseStep 9648953 = 7236715) B7236715
theorem B6021215 : Blo 1188411 6021215 := bstep (se 1 (by rfl) ⟨4515911, by rfl⟩ : syracuseStep 6021215 = 9031823) B9031823
theorem B6775919 : Blo 1188411 6775919 := bstep (se 1 (by rfl) ⟨5081939, by rfl⟩ : syracuseStep 6775919 = 10163879) B10163879
theorem B178472321 : Blo 1188411 178472321 := bstep (se 2 (by rfl) ⟨66927120, by rfl⟩ : syracuseStep 178472321 = 133854241) B133854241
theorem B6432635 : Blo 1188411 6432635 := bstep (se 1 (by rfl) ⟨4824476, by rfl⟩ : syracuseStep 6432635 = 9648953) B9648953
theorem B4819721 : Blo 1188411 4819721 := bstep (se 2 (by rfl) ⟨1807395, by rfl⟩ : syracuseStep 4819721 = 3614791) B3614791
theorem B82391003 : Blo 1188411 82391003 := bstep (se 1 (by rfl) ⟨61793252, by rfl⟩ : syracuseStep 82391003 = 123586505) B123586505
theorem B65130587 : Blo 1188411 65130587 := bstep (se 1 (by rfl) ⟨48847940, by rfl⟩ : syracuseStep 65130587 = 97695881) B97695881
theorem B10154105 : Blo 1188411 10154105 := bstep (se 2 (by rfl) ⟨3807789, by rfl⟩ : syracuseStep 10154105 = 7615579) B7615579
theorem B12203945 : Blo 1188411 12203945 := bstep (se 2 (by rfl) ⟨4576479, by rfl⟩ : syracuseStep 12203945 = 9152959) B9152959
theorem B4014143 : Blo 1188411 4014143 := bstep (se 1 (by rfl) ⟨3010607, by rfl⟩ : syracuseStep 4014143 = 6021215) B6021215
theorem B118981547 : Blo 1188411 118981547 := bstep (se 1 (by rfl) ⟨89236160, by rfl⟩ : syracuseStep 118981547 = 178472321) B178472321
theorem B8135963 : Blo 1188411 8135963 := bstep (se 1 (by rfl) ⟨6101972, by rfl⟩ : syracuseStep 8135963 = 12203945) B12203945
theorem B43420391 : Blo 1188411 43420391 := bstep (se 1 (by rfl) ⟨32565293, by rfl⟩ : syracuseStep 43420391 = 65130587) B65130587
theorem B6769403 : Blo 1188411 6769403 := bstep (se 1 (by rfl) ⟨5077052, by rfl⟩ : syracuseStep 6769403 = 10154105) B10154105
theorem B4517279 : Blo 1188411 4517279 := bstep (se 1 (by rfl) ⟨3387959, by rfl⟩ : syracuseStep 4517279 = 6775919) B6775919
theorem B4288423 : Blo 1188411 4288423 := bstep (se 1 (by rfl) ⟨3216317, by rfl⟩ : syracuseStep 4288423 = 6432635) B6432635
theorem B12852589 : Blo 1188411 12852589 := bstep (se 3 (by rfl) ⟨2409860, by rfl⟩ : syracuseStep 12852589 = 4819721) B4819721
theorem B54927335 : Blo 1188411 54927335 := bstep (se 1 (by rfl) ⟨41195501, by rfl⟩ : syracuseStep 54927335 = 82391003) B82391003
theorem B5423975 : Blo 1188411 5423975 := bstep (se 1 (by rfl) ⟨4067981, by rfl⟩ : syracuseStep 5423975 = 8135963) B8135963
theorem B28946927 : Blo 1188411 28946927 := bstep (se 1 (by rfl) ⟨21710195, by rfl⟩ : syracuseStep 28946927 = 43420391) B43420391
theorem B3011519 : Blo 1188411 3011519 := bstep (se 1 (by rfl) ⟨2258639, by rfl⟩ : syracuseStep 3011519 = 4517279) B4517279
theorem B2676095 : Blo 1188411 2676095 := bstep (se 1 (by rfl) ⟨2007071, by rfl⟩ : syracuseStep 2676095 = 4014143) B4014143
theorem B79321031 : Blo 1188411 79321031 := bstep (se 1 (by rfl) ⟨59490773, by rfl⟩ : syracuseStep 79321031 = 118981547) B118981547
theorem B17136785 : Blo 1188411 17136785 := bstep (se 2 (by rfl) ⟨6426294, by rfl⟩ : syracuseStep 17136785 = 12852589) B12852589
theorem B4512935 : Blo 1188411 4512935 := bstep (se 1 (by rfl) ⟨3384701, by rfl⟩ : syracuseStep 4512935 = 6769403) B6769403
theorem B5717897 : Blo 1188411 5717897 := bstep (se 2 (by rfl) ⟨2144211, by rfl⟩ : syracuseStep 5717897 = 4288423) B4288423
theorem B36618223 : Blo 1188411 36618223 := bstep (se 1 (by rfl) ⟨27463667, by rfl⟩ : syracuseStep 36618223 = 54927335) B54927335
theorem B2007679 : Blo 1188411 2007679 := bstep (se 1 (by rfl) ⟨1505759, by rfl⟩ : syracuseStep 2007679 = 3011519) B3011519
theorem B52880687 : Blo 1188411 52880687 := bstep (se 1 (by rfl) ⟨39660515, by rfl⟩ : syracuseStep 52880687 = 79321031) B79321031
theorem B3008623 : Blo 1188411 3008623 := bstep (se 1 (by rfl) ⟨2256467, by rfl⟩ : syracuseStep 3008623 = 4512935) B4512935
theorem B3811931 : Blo 1188411 3811931 := bstep (se 1 (by rfl) ⟨2858948, by rfl⟩ : syracuseStep 3811931 = 5717897) B5717897
theorem B3615983 : Blo 1188411 3615983 := bstep (se 1 (by rfl) ⟨2711987, by rfl⟩ : syracuseStep 3615983 = 5423975) B5423975
theorem B11424523 : Blo 1188411 11424523 := bstep (se 1 (by rfl) ⟨8568392, by rfl⟩ : syracuseStep 11424523 = 17136785) B17136785
theorem B1784063 : Blo 1188411 1784063 := bstep (se 1 (by rfl) ⟨1338047, by rfl⟩ : syracuseStep 1784063 = 2676095) B2676095
theorem B77191805 : Blo 1188411 77191805 := bstep (se 3 (by rfl) ⟨14473463, by rfl⟩ : syracuseStep 77191805 = 28946927) B28946927
theorem B48824297 : Blo 1188411 48824297 := bstep (se 2 (by rfl) ⟨18309111, by rfl⟩ : syracuseStep 48824297 = 36618223) B36618223
theorem B1189375 : Blo 1188411 1189375 := bstep (se 1 (by rfl) ⟨892031, by rfl⟩ : syracuseStep 1189375 = 1784063) B1784063
theorem B2541287 : Blo 1188411 2541287 := bstep (se 1 (by rfl) ⟨1905965, by rfl⟩ : syracuseStep 2541287 = 3811931) B3811931
theorem B2410655 : Blo 1188411 2410655 := bstep (se 1 (by rfl) ⟨1807991, by rfl⟩ : syracuseStep 2410655 = 3615983) B3615983
theorem B32549531 : Blo 1188411 32549531 := bstep (se 1 (by rfl) ⟨24412148, by rfl⟩ : syracuseStep 32549531 = 48824297) B48824297
theorem B35253791 : Blo 1188411 35253791 := bstep (se 1 (by rfl) ⟨26440343, by rfl⟩ : syracuseStep 35253791 = 52880687) B52880687
theorem B15232697 : Blo 1188411 15232697 := bstep (se 2 (by rfl) ⟨5712261, by rfl⟩ : syracuseStep 15232697 = 11424523) B11424523
theorem B4011497 : Blo 1188411 4011497 := bstep (se 2 (by rfl) ⟨1504311, by rfl⟩ : syracuseStep 4011497 = 3008623) B3008623
theorem B2676905 : Blo 1188411 2676905 := bstep (se 2 (by rfl) ⟨1003839, by rfl⟩ : syracuseStep 2676905 = 2007679) B2007679
theorem B51461203 : Blo 1188411 51461203 := bstep (se 1 (by rfl) ⟨38595902, by rfl⟩ : syracuseStep 51461203 = 77191805) B77191805
theorem B2674331 : Blo 1188411 2674331 := bstep (se 1 (by rfl) ⟨2005748, by rfl⟩ : syracuseStep 2674331 = 4011497) B4011497
theorem B86798749 : Blo 1188411 86798749 := bstep (se 3 (by rfl) ⟨16274765, by rfl⟩ : syracuseStep 86798749 = 32549531) B32549531
theorem B10155131 : Blo 1188411 10155131 := bstep (se 1 (by rfl) ⟨7616348, by rfl⟩ : syracuseStep 10155131 = 15232697) B15232697
theorem B6428413 : Blo 1188411 6428413 := bstep (se 3 (by rfl) ⟨1205327, by rfl⟩ : syracuseStep 6428413 = 2410655) B2410655
theorem B1694191 : Blo 1188411 1694191 := bstep (se 1 (by rfl) ⟨1270643, by rfl⟩ : syracuseStep 1694191 = 2541287) B2541287
theorem B68614937 : Blo 1188411 68614937 := bstep (se 2 (by rfl) ⟨25730601, by rfl⟩ : syracuseStep 68614937 = 51461203) B51461203
theorem B1784603 : Blo 1188411 1784603 := bstep (se 1 (by rfl) ⟨1338452, by rfl⟩ : syracuseStep 1784603 = 2676905) B2676905
theorem B23502527 : Blo 1188411 23502527 := bstep (se 1 (by rfl) ⟨17626895, by rfl⟩ : syracuseStep 23502527 = 35253791) B35253791
theorem B34284869 : Blo 1188411 34284869 := bstep (se 4 (by rfl) ⟨3214206, by rfl⟩ : syracuseStep 34284869 = 6428413) B6428413
theorem B1189735 : Blo 1188411 1189735 := bstep (se 1 (by rfl) ⟨892301, by rfl⟩ : syracuseStep 1189735 = 1784603) B1784603
theorem B115731665 : Blo 1188411 115731665 := bstep (se 2 (by rfl) ⟨43399374, by rfl⟩ : syracuseStep 115731665 = 86798749) B86798749
theorem B6770087 : Blo 1188411 6770087 := bstep (se 1 (by rfl) ⟨5077565, by rfl⟩ : syracuseStep 6770087 = 10155131) B10155131
theorem B1782887 : Blo 1188411 1782887 := bstep (se 1 (by rfl) ⟨1337165, by rfl⟩ : syracuseStep 1782887 = 2674331) B2674331
theorem B15668351 : Blo 1188411 15668351 := bstep (se 1 (by rfl) ⟨11751263, by rfl⟩ : syracuseStep 15668351 = 23502527) B23502527
theorem B2258921 : Blo 1188411 2258921 := bstep (se 2 (by rfl) ⟨847095, by rfl⟩ : syracuseStep 2258921 = 1694191) B1694191
theorem B45743291 : Blo 1188411 45743291 := bstep (se 1 (by rfl) ⟨34307468, by rfl⟩ : syracuseStep 45743291 = 68614937) B68614937
theorem B1188591 : Blo 1188411 1188591 := bstep (se 1 (by rfl) ⟨891443, by rfl⟩ : syracuseStep 1188591 = 1782887) B1782887
theorem B10445567 : Blo 1188411 10445567 := bstep (se 1 (by rfl) ⟨7834175, by rfl⟩ : syracuseStep 10445567 = 15668351) B15668351
theorem B22856579 : Blo 1188411 22856579 := bstep (se 1 (by rfl) ⟨17142434, by rfl⟩ : syracuseStep 22856579 = 34284869) B34284869
theorem B77154443 : Blo 1188411 77154443 := bstep (se 1 (by rfl) ⟨57865832, by rfl⟩ : syracuseStep 77154443 = 115731665) B115731665
theorem B30495527 : Blo 1188411 30495527 := bstep (se 1 (by rfl) ⟨22871645, by rfl⟩ : syracuseStep 30495527 = 45743291) B45743291
theorem B1505947 : Blo 1188411 1505947 := bstep (se 1 (by rfl) ⟨1129460, by rfl⟩ : syracuseStep 1505947 = 2258921) B2258921
theorem B4513391 : Blo 1188411 4513391 := bstep (se 1 (by rfl) ⟨3385043, by rfl⟩ : syracuseStep 4513391 = 6770087) B6770087
theorem B15237719 : Blo 1188411 15237719 := bstep (se 1 (by rfl) ⟨11428289, by rfl⟩ : syracuseStep 15237719 = 22856579) B22856579
theorem B2007929 : Blo 1188411 2007929 := bstep (se 2 (by rfl) ⟨752973, by rfl⟩ : syracuseStep 2007929 = 1505947) B1505947
theorem B3008927 : Blo 1188411 3008927 := bstep (se 1 (by rfl) ⟨2256695, by rfl⟩ : syracuseStep 3008927 = 4513391) B4513391
theorem B20330351 : Blo 1188411 20330351 := bstep (se 1 (by rfl) ⟨15247763, by rfl⟩ : syracuseStep 20330351 = 30495527) B30495527
theorem B51436295 : Blo 1188411 51436295 := bstep (se 1 (by rfl) ⟨38577221, by rfl⟩ : syracuseStep 51436295 = 77154443) B77154443
theorem B111419381 : Blo 1188411 111419381 := bstep (se 5 (by rfl) ⟨5222783, by rfl⟩ : syracuseStep 111419381 = 10445567) B10445567
theorem B10158479 : Blo 1188411 10158479 := bstep (se 1 (by rfl) ⟨7618859, by rfl⟩ : syracuseStep 10158479 = 15237719) B15237719
theorem B74279587 : Blo 1188411 74279587 := bstep (se 1 (by rfl) ⟨55709690, by rfl⟩ : syracuseStep 74279587 = 111419381) B111419381
theorem B1338619 : Blo 1188411 1338619 := bstep (se 1 (by rfl) ⟨1003964, by rfl⟩ : syracuseStep 1338619 = 2007929) B2007929
theorem B13553567 : Blo 1188411 13553567 := bstep (se 1 (by rfl) ⟨10165175, by rfl⟩ : syracuseStep 13553567 = 20330351) B20330351
theorem B2005951 : Blo 1188411 2005951 := bstep (se 1 (by rfl) ⟨1504463, by rfl⟩ : syracuseStep 2005951 = 3008927) B3008927
theorem B34290863 : Blo 1188411 34290863 := bstep (se 1 (by rfl) ⟨25718147, by rfl⟩ : syracuseStep 34290863 = 51436295) B51436295
theorem B2674601 : Blo 1188411 2674601 := bstep (se 2 (by rfl) ⟨1002975, by rfl⟩ : syracuseStep 2674601 = 2005951) B2005951
theorem B22860575 : Blo 1188411 22860575 := bstep (se 1 (by rfl) ⟨17145431, by rfl⟩ : syracuseStep 22860575 = 34290863) B34290863
theorem B6772319 : Blo 1188411 6772319 := bstep (se 1 (by rfl) ⟨5079239, by rfl⟩ : syracuseStep 6772319 = 10158479) B10158479
theorem B99039449 : Blo 1188411 99039449 := bstep (se 2 (by rfl) ⟨37139793, by rfl⟩ : syracuseStep 99039449 = 74279587) B74279587
theorem B1784825 : Blo 1188411 1784825 := bstep (se 2 (by rfl) ⟨669309, by rfl⟩ : syracuseStep 1784825 = 1338619) B1338619
theorem B9035711 : Blo 1188411 9035711 := bstep (se 1 (by rfl) ⟨6776783, by rfl⟩ : syracuseStep 9035711 = 13553567) B13553567
theorem B4514879 : Blo 1188411 4514879 := bstep (se 1 (by rfl) ⟨3386159, by rfl⟩ : syracuseStep 4514879 = 6772319) B6772319
theorem B1189883 : Blo 1188411 1189883 := bstep (se 1 (by rfl) ⟨892412, by rfl⟩ : syracuseStep 1189883 = 1784825) B1784825
theorem B6023807 : Blo 1188411 6023807 := bstep (se 1 (by rfl) ⟨4517855, by rfl⟩ : syracuseStep 6023807 = 9035711) B9035711
theorem B15240383 : Blo 1188411 15240383 := bstep (se 1 (by rfl) ⟨11430287, by rfl⟩ : syracuseStep 15240383 = 22860575) B22860575
theorem B264105197 : Blo 1188411 264105197 := bstep (se 3 (by rfl) ⟨49519724, by rfl⟩ : syracuseStep 264105197 = 99039449) B99039449
theorem B1783067 : Blo 1188411 1783067 := bstep (se 1 (by rfl) ⟨1337300, by rfl⟩ : syracuseStep 1783067 = 2674601) B2674601
theorem B1188711 : Blo 1188411 1188711 := bstep (se 1 (by rfl) ⟨891533, by rfl⟩ : syracuseStep 1188711 = 1783067) B1783067
theorem B4015871 : Blo 1188411 4015871 := bstep (se 1 (by rfl) ⟨3011903, by rfl⟩ : syracuseStep 4015871 = 6023807) B6023807
theorem B10160255 : Blo 1188411 10160255 := bstep (se 1 (by rfl) ⟨7620191, by rfl⟩ : syracuseStep 10160255 = 15240383) B15240383
theorem B3009919 : Blo 1188411 3009919 := bstep (se 1 (by rfl) ⟨2257439, by rfl⟩ : syracuseStep 3009919 = 4514879) B4514879
theorem B176070131 : Blo 1188411 176070131 := bstep (se 1 (by rfl) ⟨132052598, by rfl⟩ : syracuseStep 176070131 = 264105197) B264105197
theorem B117380087 : Blo 1188411 117380087 := bstep (se 1 (by rfl) ⟨88035065, by rfl⟩ : syracuseStep 117380087 = 176070131) B176070131
theorem B2677247 : Blo 1188411 2677247 := bstep (se 1 (by rfl) ⟨2007935, by rfl⟩ : syracuseStep 2677247 = 4015871) B4015871
theorem B6773503 : Blo 1188411 6773503 := bstep (se 1 (by rfl) ⟨5080127, by rfl⟩ : syracuseStep 6773503 = 10160255) B10160255
theorem B4013225 : Blo 1188411 4013225 := bstep (se 2 (by rfl) ⟨1504959, by rfl⟩ : syracuseStep 4013225 = 3009919) B3009919
theorem B78253391 : Blo 1188411 78253391 := bstep (se 1 (by rfl) ⟨58690043, by rfl⟩ : syracuseStep 78253391 = 117380087) B117380087
theorem B9031337 : Blo 1188411 9031337 := bstep (se 2 (by rfl) ⟨3386751, by rfl⟩ : syracuseStep 9031337 = 6773503) B6773503
theorem B2675483 : Blo 1188411 2675483 := bstep (se 1 (by rfl) ⟨2006612, by rfl⟩ : syracuseStep 2675483 = 4013225) B4013225
theorem B1784831 : Blo 1188411 1784831 := bstep (se 1 (by rfl) ⟨1338623, by rfl⟩ : syracuseStep 1784831 = 2677247) B2677247
theorem B208675709 : Blo 1188411 208675709 := bstep (se 3 (by rfl) ⟨39126695, by rfl⟩ : syracuseStep 208675709 = 78253391) B78253391
theorem B1189887 : Blo 1188411 1189887 := bstep (se 1 (by rfl) ⟨892415, by rfl⟩ : syracuseStep 1189887 = 1784831) B1784831
theorem B1783655 : Blo 1188411 1783655 := bstep (se 1 (by rfl) ⟨1337741, by rfl⟩ : syracuseStep 1783655 = 2675483) B2675483
theorem B6020891 : Blo 1188411 6020891 := bstep (se 1 (by rfl) ⟨4515668, by rfl⟩ : syracuseStep 6020891 = 9031337) B9031337
theorem B139117139 : Blo 1188411 139117139 := bstep (se 1 (by rfl) ⟨104337854, by rfl⟩ : syracuseStep 139117139 = 208675709) B208675709
theorem B1189103 : Blo 1188411 1189103 := bstep (se 1 (by rfl) ⟨891827, by rfl⟩ : syracuseStep 1189103 = 1783655) B1783655
theorem B4013927 : Blo 1188411 4013927 := bstep (se 1 (by rfl) ⟨3010445, by rfl⟩ : syracuseStep 4013927 = 6020891) B6020891
theorem B92744759 : Blo 1188411 92744759 := bstep (se 1 (by rfl) ⟨69558569, by rfl⟩ : syracuseStep 92744759 = 139117139) B139117139
theorem B2675951 : Blo 1188411 2675951 := bstep (se 1 (by rfl) ⟨2006963, by rfl⟩ : syracuseStep 2675951 = 4013927) B4013927
theorem B61829839 : Blo 1188411 61829839 := bstep (se 1 (by rfl) ⟨46372379, by rfl⟩ : syracuseStep 61829839 = 92744759) B92744759
theorem B1783967 : Blo 1188411 1783967 := bstep (se 1 (by rfl) ⟨1337975, by rfl⟩ : syracuseStep 1783967 = 2675951) B2675951
theorem B1189311 : Blo 1188411 1189311 := bstep (se 1 (by rfl) ⟨891983, by rfl⟩ : syracuseStep 1189311 = 1783967) B1783967
theorem B82439785 : Blo 1188411 82439785 := bstep (se 2 (by rfl) ⟨30914919, by rfl⟩ : syracuseStep 82439785 = 61829839) B61829839
theorem B109919713 : Blo 1188411 109919713 := bstep (se 2 (by rfl) ⟨41219892, by rfl⟩ : syracuseStep 109919713 = 82439785) B82439785
theorem B146559617 : Blo 1188411 146559617 := bstep (se 2 (by rfl) ⟨54959856, by rfl⟩ : syracuseStep 146559617 = 109919713) B109919713
theorem B97706411 : Blo 1188411 97706411 := bstep (se 1 (by rfl) ⟨73279808, by rfl⟩ : syracuseStep 97706411 = 146559617) B146559617
theorem B65137607 : Blo 1188411 65137607 := bstep (se 1 (by rfl) ⟨48853205, by rfl⟩ : syracuseStep 65137607 = 97706411) B97706411
theorem B43425071 : Blo 1188411 43425071 := bstep (se 1 (by rfl) ⟨32568803, by rfl⟩ : syracuseStep 43425071 = 65137607) B65137607
theorem B28950047 : Blo 1188411 28950047 := bstep (se 1 (by rfl) ⟨21712535, by rfl⟩ : syracuseStep 28950047 = 43425071) B43425071
theorem B19300031 : Blo 1188411 19300031 := bstep (se 1 (by rfl) ⟨14475023, by rfl⟩ : syracuseStep 19300031 = 28950047) B28950047
theorem B12866687 : Blo 1188411 12866687 := bstep (se 1 (by rfl) ⟨9650015, by rfl⟩ : syracuseStep 12866687 = 19300031) B19300031
theorem B8577791 : Blo 1188411 8577791 := bstep (se 1 (by rfl) ⟨6433343, by rfl⟩ : syracuseStep 8577791 = 12866687) B12866687
theorem B5718527 : Blo 1188411 5718527 := bstep (se 1 (by rfl) ⟨4288895, by rfl⟩ : syracuseStep 5718527 = 8577791) B8577791
theorem B3812351 : Blo 1188411 3812351 := bstep (se 1 (by rfl) ⟨2859263, by rfl⟩ : syracuseStep 3812351 = 5718527) B5718527
theorem B10166269 : Blo 1188411 10166269 := bstep (se 3 (by rfl) ⟨1906175, by rfl⟩ : syracuseStep 10166269 = 3812351) B3812351
theorem B13555025 : Blo 1188411 13555025 := bstep (se 2 (by rfl) ⟨5083134, by rfl⟩ : syracuseStep 13555025 = 10166269) B10166269
theorem B9036683 : Blo 1188411 9036683 := bstep (se 1 (by rfl) ⟨6777512, by rfl⟩ : syracuseStep 9036683 = 13555025) B13555025
theorem B6024455 : Blo 1188411 6024455 := bstep (se 1 (by rfl) ⟨4518341, by rfl⟩ : syracuseStep 6024455 = 9036683) B9036683
theorem B4016303 : Blo 1188411 4016303 := bstep (se 1 (by rfl) ⟨3012227, by rfl⟩ : syracuseStep 4016303 = 6024455) B6024455
theorem B2677535 : Blo 1188411 2677535 := bstep (se 1 (by rfl) ⟨2008151, by rfl⟩ : syracuseStep 2677535 = 4016303) B4016303
theorem B1785023 : Blo 1188411 1785023 := bstep (se 1 (by rfl) ⟨1338767, by rfl⟩ : syracuseStep 1785023 = 2677535) B2677535
theorem B1190015 : Blo 1188411 1190015 := bstep (se 1 (by rfl) ⟨892511, by rfl⟩ : syracuseStep 1190015 = 1785023) B1785023

theorem C0 (j : ℕ) (h1 : 297102 ≤ j) (h2 : j ≤ 297602) : Blo 1188411 (4 * j + 3) := by
  interval_cases j
  · exact B1188411
  · exact B1188415
  · exact B1188419
  · exact B1188423
  · exact B1188427
  · exact B1188431
  · exact B1188435
  · exact B1188439
  · exact B1188443
  · exact B1188447
  · exact B1188451
  · exact B1188455
  · exact B1188459
  · exact B1188463
  · exact B1188467
  · exact B1188471
  · exact B1188475
  · exact B1188479
  · exact B1188483
  · exact B1188487
  · exact B1188491
  · exact B1188495
  · exact B1188499
  · exact B1188503
  · exact B1188507
  · exact B1188511
  · exact B1188515
  · exact B1188519
  · exact B1188523
  · exact B1188527
  · exact B1188531
  · exact B1188535
  · exact B1188539
  · exact B1188543
  · exact B1188547
  · exact B1188551
  · exact B1188555
  · exact B1188559
  · exact B1188563
  · exact B1188567
  · exact B1188571
  · exact B1188575
  · exact B1188579
  · exact B1188583
  · exact B1188587
  · exact B1188591
  · exact B1188595
  · exact B1188599
  · exact B1188603
  · exact B1188607
  · exact B1188611
  · exact B1188615
  · exact B1188619
  · exact B1188623
  · exact B1188627
  · exact B1188631
  · exact B1188635
  · exact B1188639
  · exact B1188643
  · exact B1188647
  · exact B1188651
  · exact B1188655
  · exact B1188659
  · exact B1188663
  · exact B1188667
  · exact B1188671
  · exact B1188675
  · exact B1188679
  · exact B1188683
  · exact B1188687
  · exact B1188691
  · exact B1188695
  · exact B1188699
  · exact B1188703
  · exact B1188707
  · exact B1188711
  · exact B1188715
  · exact B1188719
  · exact B1188723
  · exact B1188727
  · exact B1188731
  · exact B1188735
  · exact B1188739
  · exact B1188743
  · exact B1188747
  · exact B1188751
  · exact B1188755
  · exact B1188759
  · exact B1188763
  · exact B1188767
  · exact B1188771
  · exact B1188775
  · exact B1188779
  · exact B1188783
  · exact B1188787
  · exact B1188791
  · exact B1188795
  · exact B1188799
  · exact B1188803
  · exact B1188807
  · exact B1188811
  · exact B1188815
  · exact B1188819
  · exact B1188823
  · exact B1188827
  · exact B1188831
  · exact B1188835
  · exact B1188839
  · exact B1188843
  · exact B1188847
  · exact B1188851
  · exact B1188855
  · exact B1188859
  · exact B1188863
  · exact B1188867
  · exact B1188871
  · exact B1188875
  · exact B1188879
  · exact B1188883
  · exact B1188887
  · exact B1188891
  · exact B1188895
  · exact B1188899
  · exact B1188903
  · exact B1188907
  · exact B1188911
  · exact B1188915
  · exact B1188919
  · exact B1188923
  · exact B1188927
  · exact B1188931
  · exact B1188935
  · exact B1188939
  · exact B1188943
  · exact B1188947
  · exact B1188951
  · exact B1188955
  · exact B1188959
  · exact B1188963
  · exact B1188967
  · exact B1188971
  · exact B1188975
  · exact B1188979
  · exact B1188983
  · exact B1188987
  · exact B1188991
  · exact B1188995
  · exact B1188999
  · exact B1189003
  · exact B1189007
  · exact B1189011
  · exact B1189015
  · exact B1189019
  · exact B1189023
  · exact B1189027
  · exact B1189031
  · exact B1189035
  · exact B1189039
  · exact B1189043
  · exact B1189047
  · exact B1189051
  · exact B1189055
  · exact B1189059
  · exact B1189063
  · exact B1189067
  · exact B1189071
  · exact B1189075
  · exact B1189079
  · exact B1189083
  · exact B1189087
  · exact B1189091
  · exact B1189095
  · exact B1189099
  · exact B1189103
  · exact B1189107
  · exact B1189111
  · exact B1189115
  · exact B1189119
  · exact B1189123
  · exact B1189127
  · exact B1189131
  · exact B1189135
  · exact B1189139
  · exact B1189143
  · exact B1189147
  · exact B1189151
  · exact B1189155
  · exact B1189159
  · exact B1189163
  · exact B1189167
  · exact B1189171
  · exact B1189175
  · exact B1189179
  · exact B1189183
  · exact B1189187
  · exact B1189191
  · exact B1189195
  · exact B1189199
  · exact B1189203
  · exact B1189207
  · exact B1189211
  · exact B1189215
  · exact B1189219
  · exact B1189223
  · exact B1189227
  · exact B1189231
  · exact B1189235
  · exact B1189239
  · exact B1189243
  · exact B1189247
  · exact B1189251
  · exact B1189255
  · exact B1189259
  · exact B1189263
  · exact B1189267
  · exact B1189271
  · exact B1189275
  · exact B1189279
  · exact B1189283
  · exact B1189287
  · exact B1189291
  · exact B1189295
  · exact B1189299
  · exact B1189303
  · exact B1189307
  · exact B1189311
  · exact B1189315
  · exact B1189319
  · exact B1189323
  · exact B1189327
  · exact B1189331
  · exact B1189335
  · exact B1189339
  · exact B1189343
  · exact B1189347
  · exact B1189351
  · exact B1189355
  · exact B1189359
  · exact B1189363
  · exact B1189367
  · exact B1189371
  · exact B1189375
  · exact B1189379
  · exact B1189383
  · exact B1189387
  · exact B1189391
  · exact B1189395
  · exact B1189399
  · exact B1189403
  · exact B1189407
  · exact B1189411
  · exact B1189415
  · exact B1189419
  · exact B1189423
  · exact B1189427
  · exact B1189431
  · exact B1189435
  · exact B1189439
  · exact B1189443
  · exact B1189447
  · exact B1189451
  · exact B1189455
  · exact B1189459
  · exact B1189463
  · exact B1189467
  · exact B1189471
  · exact B1189475
  · exact B1189479
  · exact B1189483
  · exact B1189487
  · exact B1189491
  · exact B1189495
  · exact B1189499
  · exact B1189503
  · exact B1189507
  · exact B1189511
  · exact B1189515
  · exact B1189519
  · exact B1189523
  · exact B1189527
  · exact B1189531
  · exact B1189535
  · exact B1189539
  · exact B1189543
  · exact B1189547
  · exact B1189551
  · exact B1189555
  · exact B1189559
  · exact B1189563
  · exact B1189567
  · exact B1189571
  · exact B1189575
  · exact B1189579
  · exact B1189583
  · exact B1189587
  · exact B1189591
  · exact B1189595
  · exact B1189599
  · exact B1189603
  · exact B1189607
  · exact B1189611
  · exact B1189615
  · exact B1189619
  · exact B1189623
  · exact B1189627
  · exact B1189631
  · exact B1189635
  · exact B1189639
  · exact B1189643
  · exact B1189647
  · exact B1189651
  · exact B1189655
  · exact B1189659
  · exact B1189663
  · exact B1189667
  · exact B1189671
  · exact B1189675
  · exact B1189679
  · exact B1189683
  · exact B1189687
  · exact B1189691
  · exact B1189695
  · exact B1189699
  · exact B1189703
  · exact B1189707
  · exact B1189711
  · exact B1189715
  · exact B1189719
  · exact B1189723
  · exact B1189727
  · exact B1189731
  · exact B1189735
  · exact B1189739
  · exact B1189743
  · exact B1189747
  · exact B1189751
  · exact B1189755
  · exact B1189759
  · exact B1189763
  · exact B1189767
  · exact B1189771
  · exact B1189775
  · exact B1189779
  · exact B1189783
  · exact B1189787
  · exact B1189791
  · exact B1189795
  · exact B1189799
  · exact B1189803
  · exact B1189807
  · exact B1189811
  · exact B1189815
  · exact B1189819
  · exact B1189823
  · exact B1189827
  · exact B1189831
  · exact B1189835
  · exact B1189839
  · exact B1189843
  · exact B1189847
  · exact B1189851
  · exact B1189855
  · exact B1189859
  · exact B1189863
  · exact B1189867
  · exact B1189871
  · exact B1189875
  · exact B1189879
  · exact B1189883
  · exact B1189887
  · exact B1189891
  · exact B1189895
  · exact B1189899
  · exact B1189903
  · exact B1189907
  · exact B1189911
  · exact B1189915
  · exact B1189919
  · exact B1189923
  · exact B1189927
  · exact B1189931
  · exact B1189935
  · exact B1189939
  · exact B1189943
  · exact B1189947
  · exact B1189951
  · exact B1189955
  · exact B1189959
  · exact B1189963
  · exact B1189967
  · exact B1189971
  · exact B1189975
  · exact B1189979
  · exact B1189983
  · exact B1189987
  · exact B1189991
  · exact B1189995
  · exact B1189999
  · exact B1190003
  · exact B1190007
  · exact B1190011
  · exact B1190015
  · exact B1190019
  · exact B1190023
  · exact B1190027
  · exact B1190031
  · exact B1190035
  · exact B1190039
  · exact B1190043
  · exact B1190047
  · exact B1190051
  · exact B1190055
  · exact B1190059
  · exact B1190063
  · exact B1190067
  · exact B1190071
  · exact B1190075
  · exact B1190079
  · exact B1190083
  · exact B1190087
  · exact B1190091
  · exact B1190095
  · exact B1190099
  · exact B1190103
  · exact B1190107
  · exact B1190111
  · exact B1190115
  · exact B1190119
  · exact B1190123
  · exact B1190127
  · exact B1190131
  · exact B1190135
  · exact B1190139
  · exact B1190143
  · exact B1190147
  · exact B1190151
  · exact B1190155
  · exact B1190159
  · exact B1190163
  · exact B1190167
  · exact B1190171
  · exact B1190175
  · exact B1190179
  · exact B1190183
  · exact B1190187
  · exact B1190191
  · exact B1190195
  · exact B1190199
  · exact B1190203
  · exact B1190207
  · exact B1190211
  · exact B1190215
  · exact B1190219
  · exact B1190223
  · exact B1190227
  · exact B1190231
  · exact B1190235
  · exact B1190239
  · exact B1190243
  · exact B1190247
  · exact B1190251
  · exact B1190255
  · exact B1190259
  · exact B1190263
  · exact B1190267
  · exact B1190271
  · exact B1190275
  · exact B1190279
  · exact B1190283
  · exact B1190287
  · exact B1190291
  · exact B1190295
  · exact B1190299
  · exact B1190303
  · exact B1190307
  · exact B1190311
  · exact B1190315
  · exact B1190319
  · exact B1190323
  · exact B1190327
  · exact B1190331
  · exact B1190335
  · exact B1190339
  · exact B1190343
  · exact B1190347
  · exact B1190351
  · exact B1190355
  · exact B1190359
  · exact B1190363
  · exact B1190367
  · exact B1190371
  · exact B1190375
  · exact B1190379
  · exact B1190383
  · exact B1190387
  · exact B1190391
  · exact B1190395
  · exact B1190399
  · exact B1190403
  · exact B1190407
  · exact B1190411

theorem solution (m : ℕ) (hlo : 1188411 ≤ m) (hhi : m ≤ 1190411) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 297102 ≤ j := by omega
    have hj2 : j ≤ 297602 := by omega
    have hb : Blo 1188411 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
