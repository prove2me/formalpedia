-- Prove2me | solution 1 for syracuse_descends_range_1719060_1721060
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:29:21.419404+00:00
-- url     : https://prove2.me/submissions/69497b8d-231c-498d-bf5a-592f722a953f

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


theorem B2580485 : Blo 1719060 2580485 := bbase (se 4 (by rfl) ⟨241920, by rfl⟩ : syracuseStep 2580485 = 483841) (by norm_num)
theorem B6529045 : Blo 1719060 6529045 := bbase (se 6 (by rfl) ⟨153024, by rfl⟩ : syracuseStep 6529045 = 306049) (by norm_num)
theorem B15687701 : Blo 1719060 15687701 := bbase (se 6 (by rfl) ⟨367680, by rfl⟩ : syracuseStep 15687701 = 735361) (by norm_num)
theorem B2981909 : Blo 1719060 2981909 := bbase (se 6 (by rfl) ⟨69888, by rfl⟩ : syracuseStep 2981909 = 139777) (by norm_num)
theorem B2580509 : Blo 1719060 2580509 := bbase (se 3 (by rfl) ⟨483845, by rfl⟩ : syracuseStep 2580509 = 967691) (by norm_num)
theorem B8822837 : Blo 1719060 8822837 := bbase (se 5 (by rfl) ⟨413570, by rfl⟩ : syracuseStep 8822837 = 827141) (by norm_num)
theorem B2580533 : Blo 1719060 2580533 := bbase (se 5 (by rfl) ⟨120962, by rfl⟩ : syracuseStep 2580533 = 241925) (by norm_num)
theorem B2580557 : Blo 1719060 2580557 := bbase (se 3 (by rfl) ⟨483854, by rfl⟩ : syracuseStep 2580557 = 967709) (by norm_num)
theorem B2580581 : Blo 1719060 2580581 := bbase (se 4 (by rfl) ⟨241929, by rfl⟩ : syracuseStep 2580581 = 483859) (by norm_num)
theorem B2580605 : Blo 1719060 2580605 := bbase (se 3 (by rfl) ⟨483863, by rfl⟩ : syracuseStep 2580605 = 967727) (by norm_num)
theorem B2580629 : Blo 1719060 2580629 := bbase (se 6 (by rfl) ⟨60483, by rfl⟩ : syracuseStep 2580629 = 120967) (by norm_num)
theorem B5808293 : Blo 1719060 5808293 := bbase (se 4 (by rfl) ⟨544527, by rfl⟩ : syracuseStep 5808293 = 1089055) (by norm_num)
theorem B2580653 : Blo 1719060 2580653 := bbase (se 3 (by rfl) ⟨483872, by rfl⟩ : syracuseStep 2580653 = 967745) (by norm_num)
theorem B2580677 : Blo 1719060 2580677 := bbase (se 4 (by rfl) ⟨241938, by rfl⟩ : syracuseStep 2580677 = 483877) (by norm_num)
theorem B8708309 : Blo 1719060 8708309 := bbase (se 7 (by rfl) ⟨102050, by rfl⟩ : syracuseStep 8708309 = 204101) (by norm_num)
theorem B2580701 : Blo 1719060 2580701 := bbase (se 3 (by rfl) ⟨483881, by rfl⟩ : syracuseStep 2580701 = 967763) (by norm_num)
theorem B2580725 : Blo 1719060 2580725 := bbase (se 5 (by rfl) ⟨120971, by rfl⟩ : syracuseStep 2580725 = 241943) (by norm_num)
theorem B2580749 : Blo 1719060 2580749 := bbase (se 3 (by rfl) ⟨483890, by rfl⟩ : syracuseStep 2580749 = 967781) (by norm_num)
theorem B5882149 : Blo 1719060 5882149 := bbase (se 4 (by rfl) ⟨551451, by rfl⟩ : syracuseStep 5882149 = 1102903) (by norm_num)
theorem B2580773 : Blo 1719060 2580773 := bbase (se 4 (by rfl) ⟨241947, by rfl⟩ : syracuseStep 2580773 = 483895) (by norm_num)
theorem B2580797 : Blo 1719060 2580797 := bbase (se 3 (by rfl) ⟨483899, by rfl⟩ : syracuseStep 2580797 = 967799) (by norm_num)
theorem B6529349 : Blo 1719060 6529349 := bbase (se 4 (by rfl) ⟨612126, by rfl⟩ : syracuseStep 6529349 = 1224253) (by norm_num)
theorem B2580821 : Blo 1719060 2580821 := bbase (se 10 (by rfl) ⟨3780, by rfl⟩ : syracuseStep 2580821 = 7561) (by norm_num)
theorem B2580845 : Blo 1719060 2580845 := bbase (se 3 (by rfl) ⟨483908, by rfl⟩ : syracuseStep 2580845 = 967817) (by norm_num)
theorem B2580869 : Blo 1719060 2580869 := bbase (se 4 (by rfl) ⟨241956, by rfl⟩ : syracuseStep 2580869 = 483913) (by norm_num)
theorem B2580893 : Blo 1719060 2580893 := bbase (se 3 (by rfl) ⟨483917, by rfl⟩ : syracuseStep 2580893 = 967835) (by norm_num)
theorem B2580917 : Blo 1719060 2580917 := bbase (se 5 (by rfl) ⟨120980, by rfl⟩ : syracuseStep 2580917 = 241961) (by norm_num)
theorem B2580941 : Blo 1719060 2580941 := bbase (se 3 (by rfl) ⟨483926, by rfl⟩ : syracuseStep 2580941 = 967853) (by norm_num)
theorem B2580965 : Blo 1719060 2580965 := bbase (se 4 (by rfl) ⟨241965, by rfl⟩ : syracuseStep 2580965 = 483931) (by norm_num)
theorem B2580989 : Blo 1719060 2580989 := bbase (se 3 (by rfl) ⟨483935, by rfl⟩ : syracuseStep 2580989 = 967871) (by norm_num)
theorem B2581013 : Blo 1719060 2581013 := bbase (se 6 (by rfl) ⟨60492, by rfl⟩ : syracuseStep 2581013 = 120985) (by norm_num)
theorem B2581037 : Blo 1719060 2581037 := bbase (se 3 (by rfl) ⟨483944, by rfl⟩ : syracuseStep 2581037 = 967889) (by norm_num)
theorem B2581061 : Blo 1719060 2581061 := bbase (se 4 (by rfl) ⟨241974, by rfl⟩ : syracuseStep 2581061 = 483949) (by norm_num)
theorem B2581085 : Blo 1719060 2581085 := bbase (se 3 (by rfl) ⟨483953, by rfl⟩ : syracuseStep 2581085 = 967907) (by norm_num)
theorem B2581109 : Blo 1719060 2581109 := bbase (se 5 (by rfl) ⟨120989, by rfl⟩ : syracuseStep 2581109 = 241979) (by norm_num)
theorem B2581133 : Blo 1719060 2581133 := bbase (se 3 (by rfl) ⟨483962, by rfl⟩ : syracuseStep 2581133 = 967925) (by norm_num)
theorem B1933969 : Blo 1719060 1933969 := bbase (se 2 (by rfl) ⟨725238, by rfl⟩ : syracuseStep 1933969 = 1450477) (by norm_num)
theorem B2581157 : Blo 1719060 2581157 := bbase (se 4 (by rfl) ⟨241983, by rfl⟩ : syracuseStep 2581157 = 483967) (by norm_num)
theorem B1934005 : Blo 1719060 1934005 := bbase (se 5 (by rfl) ⟨90656, by rfl⟩ : syracuseStep 1934005 = 181313) (by norm_num)
theorem B2450101 : Blo 1719060 2450101 := bbase (se 5 (by rfl) ⟨114848, by rfl⟩ : syracuseStep 2450101 = 229697) (by norm_num)
theorem B2581181 : Blo 1719060 2581181 := bbase (se 3 (by rfl) ⟨483971, by rfl⟩ : syracuseStep 2581181 = 967943) (by norm_num)
theorem B8823509 : Blo 1719060 8823509 := bbase (se 7 (by rfl) ⟨103400, by rfl⟩ : syracuseStep 8823509 = 206801) (by norm_num)
theorem B4899541 : Blo 1719060 4899541 := bbase (se 7 (by rfl) ⟨57416, by rfl⟩ : syracuseStep 4899541 = 114833) (by norm_num)
theorem B2581205 : Blo 1719060 2581205 := bbase (se 7 (by rfl) ⟨30248, by rfl⟩ : syracuseStep 2581205 = 60497) (by norm_num)
theorem B1934041 : Blo 1719060 1934041 := bbase (se 2 (by rfl) ⟨725265, by rfl⟩ : syracuseStep 1934041 = 1450531) (by norm_num)
theorem B2581229 : Blo 1719060 2581229 := bbase (se 3 (by rfl) ⟨483980, by rfl⟩ : syracuseStep 2581229 = 967961) (by norm_num)
theorem B1934077 : Blo 1719060 1934077 := bbase (se 3 (by rfl) ⟨362639, by rfl⟩ : syracuseStep 1934077 = 725279) (by norm_num)
theorem B2581253 : Blo 1719060 2581253 := bbase (se 4 (by rfl) ⟨241992, by rfl⟩ : syracuseStep 2581253 = 483985) (by norm_num)
theorem B2581277 : Blo 1719060 2581277 := bbase (se 3 (by rfl) ⟨483989, by rfl⟩ : syracuseStep 2581277 = 967979) (by norm_num)
theorem B1934113 : Blo 1719060 1934113 := bbase (se 2 (by rfl) ⟨725292, by rfl⟩ : syracuseStep 1934113 = 1450585) (by norm_num)
theorem B2581301 : Blo 1719060 2581301 := bbase (se 5 (by rfl) ⟨120998, by rfl⟩ : syracuseStep 2581301 = 241997) (by norm_num)
theorem B6202165 : Blo 1719060 6202165 := bbase (se 5 (by rfl) ⟨290726, by rfl⟩ : syracuseStep 6202165 = 581453) (by norm_num)
theorem B1835833 : Blo 1719060 1835833 := bbase (se 2 (by rfl) ⟨688437, by rfl⟩ : syracuseStep 1835833 = 1376875) (by norm_num)
theorem B1934149 : Blo 1719060 1934149 := bbase (se 4 (by rfl) ⟨181326, by rfl⟩ : syracuseStep 1934149 = 362653) (by norm_num)
theorem B2581325 : Blo 1719060 2581325 := bbase (se 3 (by rfl) ⟨483998, by rfl⟩ : syracuseStep 2581325 = 967997) (by norm_num)
theorem B2581349 : Blo 1719060 2581349 := bbase (se 4 (by rfl) ⟨242001, by rfl⟩ : syracuseStep 2581349 = 484003) (by norm_num)
theorem B1934185 : Blo 1719060 1934185 := bbase (se 2 (by rfl) ⟨725319, by rfl⟩ : syracuseStep 1934185 = 1450639) (by norm_num)
theorem B1835893 : Blo 1719060 1835893 := bbase (se 5 (by rfl) ⟨86057, by rfl⟩ : syracuseStep 1835893 = 172115) (by norm_num)
theorem B2581373 : Blo 1719060 2581373 := bbase (se 3 (by rfl) ⟨484007, by rfl⟩ : syracuseStep 2581373 = 968015) (by norm_num)
theorem B1934221 : Blo 1719060 1934221 := bbase (se 3 (by rfl) ⟨362666, by rfl⟩ : syracuseStep 1934221 = 725333) (by norm_num)
theorem B2581397 : Blo 1719060 2581397 := bbase (se 6 (by rfl) ⟨60501, by rfl⟩ : syracuseStep 2581397 = 121003) (by norm_num)
theorem B2581421 : Blo 1719060 2581421 := bbase (se 3 (by rfl) ⟨484016, by rfl⟩ : syracuseStep 2581421 = 968033) (by norm_num)
theorem B1934257 : Blo 1719060 1934257 := bbase (se 2 (by rfl) ⟨725346, by rfl⟩ : syracuseStep 1934257 = 1450693) (by norm_num)
theorem B2581445 : Blo 1719060 2581445 := bbase (se 4 (by rfl) ⟨242010, by rfl⟩ : syracuseStep 2581445 = 484021) (by norm_num)
theorem B1934293 : Blo 1719060 1934293 := bbase (se 7 (by rfl) ⟨22667, by rfl⟩ : syracuseStep 1934293 = 45335) (by norm_num)
theorem B6202325 : Blo 1719060 6202325 := bbase (se 7 (by rfl) ⟨72683, by rfl⟩ : syracuseStep 6202325 = 145367) (by norm_num)
theorem B2581469 : Blo 1719060 2581469 := bbase (se 3 (by rfl) ⟨484025, by rfl⟩ : syracuseStep 2581469 = 968051) (by norm_num)
theorem B2900981 : Blo 1719060 2900981 := bbase (se 5 (by rfl) ⟨135983, by rfl⟩ : syracuseStep 2900981 = 271967) (by norm_num)
theorem B2581493 : Blo 1719060 2581493 := bbase (se 5 (by rfl) ⟨121007, by rfl⟩ : syracuseStep 2581493 = 242015) (by norm_num)
theorem B1934329 : Blo 1719060 1934329 := bbase (se 2 (by rfl) ⟨725373, by rfl⟩ : syracuseStep 1934329 = 1450747) (by norm_num)
theorem B2581517 : Blo 1719060 2581517 := bbase (se 3 (by rfl) ⟨484034, by rfl⟩ : syracuseStep 2581517 = 968069) (by norm_num)
theorem B1934365 : Blo 1719060 1934365 := bbase (se 3 (by rfl) ⟨362693, by rfl⟩ : syracuseStep 1934365 = 725387) (by norm_num)
theorem B2581541 : Blo 1719060 2581541 := bbase (se 4 (by rfl) ⟨242019, by rfl⟩ : syracuseStep 2581541 = 484039) (by norm_num)
theorem B2581565 : Blo 1719060 2581565 := bbase (se 3 (by rfl) ⟨484043, by rfl⟩ : syracuseStep 2581565 = 968087) (by norm_num)
theorem B1934401 : Blo 1719060 1934401 := bbase (se 2 (by rfl) ⟨725400, by rfl⟩ : syracuseStep 1934401 = 1450801) (by norm_num)
theorem B2581589 : Blo 1719060 2581589 := bbase (se 8 (by rfl) ⟨15126, by rfl⟩ : syracuseStep 2581589 = 30253) (by norm_num)
theorem B1934437 : Blo 1719060 1934437 := bbase (se 4 (by rfl) ⟨181353, by rfl⟩ : syracuseStep 1934437 = 362707) (by norm_num)
theorem B2901109 : Blo 1719060 2901109 := bbase (se 5 (by rfl) ⟨135989, by rfl⟩ : syracuseStep 2901109 = 271979) (by norm_num)
theorem B1934473 : Blo 1719060 1934473 := bbase (se 2 (by rfl) ⟨725427, by rfl⟩ : syracuseStep 1934473 = 1450855) (by norm_num)
theorem B1934509 : Blo 1719060 1934509 := bbase (se 3 (by rfl) ⟨362720, by rfl⟩ : syracuseStep 1934509 = 725441) (by norm_num)
theorem B1836209 : Blo 1719060 1836209 := bbase (se 2 (by rfl) ⟨688578, by rfl⟩ : syracuseStep 1836209 = 1377157) (by norm_num)
theorem B2901197 : Blo 1719060 2901197 := bbase (se 3 (by rfl) ⟨543974, by rfl⟩ : syracuseStep 2901197 = 1087949) (by norm_num)
theorem B1934545 : Blo 1719060 1934545 := bbase (se 2 (by rfl) ⟨725454, by rfl⟩ : syracuseStep 1934545 = 1450909) (by norm_num)
theorem B11019509 : Blo 1719060 11019509 := bbase (se 5 (by rfl) ⟨516539, by rfl⟩ : syracuseStep 11019509 = 1033079) (by norm_num)
theorem B3867893 : Blo 1719060 3867893 := bbase (se 5 (by rfl) ⟨181307, by rfl⟩ : syracuseStep 3867893 = 362615) (by norm_num)
theorem B1934581 : Blo 1719060 1934581 := bbase (se 5 (by rfl) ⟨90683, by rfl⟩ : syracuseStep 1934581 = 181367) (by norm_num)
theorem B8266997 : Blo 1719060 8266997 := bbase (se 5 (by rfl) ⟨387515, by rfl⟩ : syracuseStep 8266997 = 775031) (by norm_num)
theorem B2065673 : Blo 1719060 2065673 := bbase (se 2 (by rfl) ⟨774627, by rfl⟩ : syracuseStep 2065673 = 1549255) (by norm_num)
theorem B1934617 : Blo 1719060 1934617 := bbase (se 2 (by rfl) ⟨725481, by rfl⟩ : syracuseStep 1934617 = 1450963) (by norm_num)
theorem B3867965 : Blo 1719060 3867965 := bbase (se 3 (by rfl) ⟨725243, by rfl⟩ : syracuseStep 3867965 = 1450487) (by norm_num)
theorem B1934653 : Blo 1719060 1934653 := bbase (se 3 (by rfl) ⟨362747, by rfl⟩ : syracuseStep 1934653 = 725495) (by norm_num)
theorem B2901325 : Blo 1719060 2901325 := bbase (se 3 (by rfl) ⟨543998, by rfl⟩ : syracuseStep 2901325 = 1087997) (by norm_num)
theorem B8267093 : Blo 1719060 8267093 := bbase (se 12 (by rfl) ⟨3027, by rfl⟩ : syracuseStep 8267093 = 6055) (by norm_num)
theorem B1934689 : Blo 1719060 1934689 := bbase (se 2 (by rfl) ⟨725508, by rfl⟩ : syracuseStep 1934689 = 1451017) (by norm_num)
theorem B3868037 : Blo 1719060 3868037 := bbase (se 4 (by rfl) ⟨362628, by rfl⟩ : syracuseStep 3868037 = 725257) (by norm_num)
theorem B1934725 : Blo 1719060 1934725 := bbase (se 4 (by rfl) ⟨181380, by rfl⟩ : syracuseStep 1934725 = 362761) (by norm_num)
theorem B2901413 : Blo 1719060 2901413 := bbase (se 4 (by rfl) ⟨272007, by rfl⟩ : syracuseStep 2901413 = 544015) (by norm_num)
theorem B1934761 : Blo 1719060 1934761 := bbase (se 2 (by rfl) ⟨725535, by rfl⟩ : syracuseStep 1934761 = 1451071) (by norm_num)
theorem B4351421 : Blo 1719060 4351421 := bbase (se 3 (by rfl) ⟨815891, by rfl⟩ : syracuseStep 4351421 = 1631783) (by norm_num)
theorem B3868109 : Blo 1719060 3868109 := bbase (se 3 (by rfl) ⟨725270, by rfl⟩ : syracuseStep 3868109 = 1450541) (by norm_num)
theorem B1934797 : Blo 1719060 1934797 := bbase (se 3 (by rfl) ⟨362774, by rfl⟩ : syracuseStep 1934797 = 725549) (by norm_num)
theorem B8709605 : Blo 1719060 8709605 := bbase (se 4 (by rfl) ⟨816525, by rfl⟩ : syracuseStep 8709605 = 1633051) (by norm_num)
theorem B1934833 : Blo 1719060 1934833 := bbase (se 2 (by rfl) ⟨725562, by rfl⟩ : syracuseStep 1934833 = 1451125) (by norm_num)
theorem B3868181 : Blo 1719060 3868181 := bbase (se 6 (by rfl) ⟨90660, by rfl⟩ : syracuseStep 3868181 = 181321) (by norm_num)
theorem B1934869 : Blo 1719060 1934869 := bbase (se 6 (by rfl) ⟨45348, by rfl⟩ : syracuseStep 1934869 = 90697) (by norm_num)
theorem B3671581 : Blo 1719060 3671581 := bbase (se 3 (by rfl) ⟨688421, by rfl⟩ : syracuseStep 3671581 = 1376843) (by norm_num)
theorem B2901541 : Blo 1719060 2901541 := bbase (se 4 (by rfl) ⟨272019, by rfl⟩ : syracuseStep 2901541 = 544039) (by norm_num)
theorem B1934905 : Blo 1719060 1934905 := bbase (se 2 (by rfl) ⟨725589, by rfl⟩ : syracuseStep 1934905 = 1451179) (by norm_num)
theorem B2065981 : Blo 1719060 2065981 := bbase (se 3 (by rfl) ⟨387371, by rfl⟩ : syracuseStep 2065981 = 774743) (by norm_num)
theorem B3868253 : Blo 1719060 3868253 := bbase (se 3 (by rfl) ⟨725297, by rfl⟩ : syracuseStep 3868253 = 1450595) (by norm_num)
theorem B1934941 : Blo 1719060 1934941 := bbase (se 3 (by rfl) ⟨362801, by rfl⟩ : syracuseStep 1934941 = 725603) (by norm_num)
theorem B1836653 : Blo 1719060 1836653 := bbase (se 3 (by rfl) ⟨344372, by rfl⟩ : syracuseStep 1836653 = 688745) (by norm_num)
theorem B2901629 : Blo 1719060 2901629 := bbase (se 3 (by rfl) ⟨544055, by rfl⟩ : syracuseStep 2901629 = 1088111) (by norm_num)
theorem B1934977 : Blo 1719060 1934977 := bbase (se 2 (by rfl) ⟨725616, by rfl⟩ : syracuseStep 1934977 = 1451233) (by norm_num)
theorem B5228165 : Blo 1719060 5228165 := bbase (se 4 (by rfl) ⟨490140, by rfl⟩ : syracuseStep 5228165 = 980281) (by norm_num)
theorem B2066081 : Blo 1719060 2066081 := bbase (se 2 (by rfl) ⟨774780, by rfl⟩ : syracuseStep 2066081 = 1549561) (by norm_num)
theorem B3868325 : Blo 1719060 3868325 := bbase (se 4 (by rfl) ⟨362655, by rfl⟩ : syracuseStep 3868325 = 725311) (by norm_num)
theorem B1935013 : Blo 1719060 1935013 := bbase (se 4 (by rfl) ⟨181407, by rfl⟩ : syracuseStep 1935013 = 362815) (by norm_num)
theorem B1836713 : Blo 1719060 1836713 := bbase (se 2 (by rfl) ⟨688767, by rfl⟩ : syracuseStep 1836713 = 1377535) (by norm_num)
theorem B1935049 : Blo 1719060 1935049 := bbase (se 2 (by rfl) ⟨725643, by rfl⟩ : syracuseStep 1935049 = 1451287) (by norm_num)
theorem B4130509 : Blo 1719060 4130509 := bbase (se 3 (by rfl) ⟨774470, by rfl⟩ : syracuseStep 4130509 = 1548941) (by norm_num)
theorem B11929301 : Blo 1719060 11929301 := bbase (se 7 (by rfl) ⟨139796, by rfl⟩ : syracuseStep 11929301 = 279593) (by norm_num)
theorem B3868397 : Blo 1719060 3868397 := bbase (se 3 (by rfl) ⟨725324, by rfl⟩ : syracuseStep 3868397 = 1450649) (by norm_num)
theorem B1935085 : Blo 1719060 1935085 := bbase (se 3 (by rfl) ⟨362828, by rfl⟩ : syracuseStep 1935085 = 725657) (by norm_num)
theorem B2901757 : Blo 1719060 2901757 := bbase (se 3 (by rfl) ⟨544079, by rfl⟩ : syracuseStep 2901757 = 1088159) (by norm_num)
theorem B1935121 : Blo 1719060 1935121 := bbase (se 2 (by rfl) ⟨725670, by rfl⟩ : syracuseStep 1935121 = 1451341) (by norm_num)
theorem B4351765 : Blo 1719060 4351765 := bbase (se 6 (by rfl) ⟨101994, by rfl⟩ : syracuseStep 4351765 = 203989) (by norm_num)
theorem B13068053 : Blo 1719060 13068053 := bbase (se 6 (by rfl) ⟨306282, by rfl⟩ : syracuseStep 13068053 = 612565) (by norm_num)
theorem B1836841 : Blo 1719060 1836841 := bbase (se 2 (by rfl) ⟨688815, by rfl⟩ : syracuseStep 1836841 = 1377631) (by norm_num)
theorem B4130605 : Blo 1719060 4130605 := bbase (se 3 (by rfl) ⟨774488, by rfl⟩ : syracuseStep 4130605 = 1548977) (by norm_num)
theorem B3868469 : Blo 1719060 3868469 := bbase (se 5 (by rfl) ⟨181334, by rfl⟩ : syracuseStep 3868469 = 362669) (by norm_num)
theorem B16525109 : Blo 1719060 16525109 := bbase (se 5 (by rfl) ⟨774614, by rfl⟩ : syracuseStep 16525109 = 1549229) (by norm_num)
theorem B1935157 : Blo 1719060 1935157 := bbase (se 5 (by rfl) ⟨90710, by rfl⟩ : syracuseStep 1935157 = 181421) (by norm_num)
theorem B2901845 : Blo 1719060 2901845 := bbase (se 9 (by rfl) ⟨8501, by rfl⟩ : syracuseStep 2901845 = 17003) (by norm_num)
theorem B1935193 : Blo 1719060 1935193 := bbase (se 2 (by rfl) ⟨725697, by rfl⟩ : syracuseStep 1935193 = 1451395) (by norm_num)
theorem B3868541 : Blo 1719060 3868541 := bbase (se 3 (by rfl) ⟨725351, by rfl⟩ : syracuseStep 3868541 = 1450703) (by norm_num)
theorem B1935229 : Blo 1719060 1935229 := bbase (se 3 (by rfl) ⟨362855, by rfl⟩ : syracuseStep 1935229 = 725711) (by norm_num)
theorem B4351877 : Blo 1719060 4351877 := bbase (se 4 (by rfl) ⟨407988, by rfl⟩ : syracuseStep 4351877 = 815977) (by norm_num)
theorem B9791381 : Blo 1719060 9791381 := bbase (se 6 (by rfl) ⟨229485, by rfl⟩ : syracuseStep 9791381 = 458971) (by norm_num)
theorem B1935265 : Blo 1719060 1935265 := bbase (se 2 (by rfl) ⟨725724, by rfl⟩ : syracuseStep 1935265 = 1451449) (by norm_num)
theorem B3868613 : Blo 1719060 3868613 := bbase (se 4 (by rfl) ⟨362682, by rfl⟩ : syracuseStep 3868613 = 725365) (by norm_num)
theorem B1935301 : Blo 1719060 1935301 := bbase (se 4 (by rfl) ⟨181434, by rfl⟩ : syracuseStep 1935301 = 362869) (by norm_num)
theorem B2901973 : Blo 1719060 2901973 := bbase (se 7 (by rfl) ⟨34007, by rfl⟩ : syracuseStep 2901973 = 68015) (by norm_num)
theorem B1935337 : Blo 1719060 1935337 := bbase (se 2 (by rfl) ⟨725751, by rfl⟩ : syracuseStep 1935337 = 1451503) (by norm_num)
theorem B3868685 : Blo 1719060 3868685 := bbase (se 3 (by rfl) ⟨725378, by rfl⟩ : syracuseStep 3868685 = 1450757) (by norm_num)
theorem B1935373 : Blo 1719060 1935373 := bbase (se 3 (by rfl) ⟨362882, by rfl⟩ : syracuseStep 1935373 = 725765) (by norm_num)
theorem B2902061 : Blo 1719060 2902061 := bbase (se 3 (by rfl) ⟨544136, by rfl⟩ : syracuseStep 2902061 = 1088273) (by norm_num)
theorem B1935409 : Blo 1719060 1935409 := bbase (se 2 (by rfl) ⟨725778, by rfl⟩ : syracuseStep 1935409 = 1451557) (by norm_num)
theorem B2066485 : Blo 1719060 2066485 := bbase (se 5 (by rfl) ⟨96866, by rfl⟩ : syracuseStep 2066485 = 193733) (by norm_num)
theorem B4352069 : Blo 1719060 4352069 := bbase (se 4 (by rfl) ⟨408006, by rfl⟩ : syracuseStep 4352069 = 816013) (by norm_num)
theorem B3868757 : Blo 1719060 3868757 := bbase (se 8 (by rfl) ⟨22668, by rfl⟩ : syracuseStep 3868757 = 45337) (by norm_num)
theorem B1935445 : Blo 1719060 1935445 := bbase (se 8 (by rfl) ⟨11340, by rfl⟩ : syracuseStep 1935445 = 22681) (by norm_num)
theorem B1935481 : Blo 1719060 1935481 := bbase (se 2 (by rfl) ⟨725805, by rfl⟩ : syracuseStep 1935481 = 1451611) (by norm_num)
theorem B3868829 : Blo 1719060 3868829 := bbase (se 3 (by rfl) ⟨725405, by rfl⟩ : syracuseStep 3868829 = 1450811) (by norm_num)
theorem B1935517 : Blo 1719060 1935517 := bbase (se 3 (by rfl) ⟨362909, by rfl⟩ : syracuseStep 1935517 = 725819) (by norm_num)
theorem B2902189 : Blo 1719060 2902189 := bbase (se 3 (by rfl) ⟨544160, by rfl⟩ : syracuseStep 2902189 = 1088321) (by norm_num)
theorem B3582133 : Blo 1719060 3582133 := bbase (se 5 (by rfl) ⟨167912, by rfl⟩ : syracuseStep 3582133 = 335825) (by norm_num)
theorem B13060277 : Blo 1719060 13060277 := bbase (se 5 (by rfl) ⟨612200, by rfl⟩ : syracuseStep 13060277 = 1224401) (by norm_num)
theorem B2754749 : Blo 1719060 2754749 := bbase (se 3 (by rfl) ⟨516515, by rfl⟩ : syracuseStep 2754749 = 1033031) (by norm_num)
theorem B1935553 : Blo 1719060 1935553 := bbase (se 2 (by rfl) ⟨725832, by rfl⟩ : syracuseStep 1935553 = 1451665) (by norm_num)
theorem B3868901 : Blo 1719060 3868901 := bbase (se 4 (by rfl) ⟨362709, by rfl⟩ : syracuseStep 3868901 = 725419) (by norm_num)
theorem B1837285 : Blo 1719060 1837285 := bbase (se 4 (by rfl) ⟨172245, by rfl⟩ : syracuseStep 1837285 = 344491) (by norm_num)
theorem B1935589 : Blo 1719060 1935589 := bbase (se 4 (by rfl) ⟨181461, by rfl⟩ : syracuseStep 1935589 = 362923) (by norm_num)
theorem B5802245 : Blo 1719060 5802245 := bbase (se 4 (by rfl) ⟨543960, by rfl⟩ : syracuseStep 5802245 = 1087921) (by norm_num)
theorem B2902277 : Blo 1719060 2902277 := bbase (se 4 (by rfl) ⟨272088, by rfl⟩ : syracuseStep 2902277 = 544177) (by norm_num)
theorem B1935625 : Blo 1719060 1935625 := bbase (se 2 (by rfl) ⟨725859, by rfl⟩ : syracuseStep 1935625 = 1451719) (by norm_num)
theorem B3868973 : Blo 1719060 3868973 := bbase (se 3 (by rfl) ⟨725432, by rfl⟩ : syracuseStep 3868973 = 1450865) (by norm_num)
theorem B1935661 : Blo 1719060 1935661 := bbase (se 3 (by rfl) ⟨362936, by rfl⟩ : syracuseStep 1935661 = 725873) (by norm_num)
theorem B2206001 : Blo 1719060 2206001 := bbase (se 2 (by rfl) ⟨827250, by rfl⟩ : syracuseStep 2206001 = 1654501) (by norm_num)
theorem B4131125 : Blo 1719060 4131125 := bbase (se 5 (by rfl) ⟨193646, by rfl⟩ : syracuseStep 4131125 = 387293) (by norm_num)
theorem B1935697 : Blo 1719060 1935697 := bbase (se 2 (by rfl) ⟨725886, by rfl⟩ : syracuseStep 1935697 = 1451773) (by norm_num)
theorem B1837405 : Blo 1719060 1837405 := bbase (se 3 (by rfl) ⟨344513, by rfl⟩ : syracuseStep 1837405 = 689027) (by norm_num)
theorem B3869045 : Blo 1719060 3869045 := bbase (se 5 (by rfl) ⟨181361, by rfl⟩ : syracuseStep 3869045 = 362723) (by norm_num)
theorem B1935733 : Blo 1719060 1935733 := bbase (se 5 (by rfl) ⟨90737, by rfl⟩ : syracuseStep 1935733 = 181475) (by norm_num)
theorem B12405109 : Blo 1719060 12405109 := bbase (se 5 (by rfl) ⟨581489, by rfl⟩ : syracuseStep 12405109 = 1162979) (by norm_num)
theorem B2902405 : Blo 1719060 2902405 := bbase (se 4 (by rfl) ⟨272100, by rfl⟩ : syracuseStep 2902405 = 544201) (by norm_num)
theorem B6531461 : Blo 1719060 6531461 := bbase (se 4 (by rfl) ⟨612324, by rfl⟩ : syracuseStep 6531461 = 1224649) (by norm_num)
theorem B3672469 : Blo 1719060 3672469 := bbase (se 6 (by rfl) ⟨86073, by rfl⟩ : syracuseStep 3672469 = 172147) (by norm_num)
theorem B1935769 : Blo 1719060 1935769 := bbase (se 2 (by rfl) ⟨725913, by rfl⟩ : syracuseStep 1935769 = 1451827) (by norm_num)
theorem B4352413 : Blo 1719060 4352413 := bbase (se 3 (by rfl) ⟨816077, by rfl⟩ : syracuseStep 4352413 = 1632155) (by norm_num)
theorem B2066869 : Blo 1719060 2066869 := bbase (se 5 (by rfl) ⟨96884, by rfl⟩ : syracuseStep 2066869 = 193769) (by norm_num)
theorem B3869117 : Blo 1719060 3869117 := bbase (se 3 (by rfl) ⟨725459, by rfl⟩ : syracuseStep 3869117 = 1450919) (by norm_num)
theorem B1935805 : Blo 1719060 1935805 := bbase (se 3 (by rfl) ⟨362963, by rfl⟩ : syracuseStep 1935805 = 725927) (by norm_num)
theorem B5302741 : Blo 1719060 5302741 := bbase (se 7 (by rfl) ⟨62141, by rfl⟩ : syracuseStep 5302741 = 124283) (by norm_num)
theorem B10463701 : Blo 1719060 10463701 := bbase (se 7 (by rfl) ⟨122621, by rfl⟩ : syracuseStep 10463701 = 245243) (by norm_num)
theorem B2902493 : Blo 1719060 2902493 := bbase (se 3 (by rfl) ⟨544217, by rfl⟩ : syracuseStep 2902493 = 1088435) (by norm_num)
theorem B1935841 : Blo 1719060 1935841 := bbase (se 2 (by rfl) ⟨725940, by rfl⟩ : syracuseStep 1935841 = 1451881) (by norm_num)
theorem B5229029 : Blo 1719060 5229029 := bbase (se 4 (by rfl) ⟨490221, by rfl⟩ : syracuseStep 5229029 = 980443) (by norm_num)
theorem B3869189 : Blo 1719060 3869189 := bbase (se 4 (by rfl) ⟨362736, by rfl⟩ : syracuseStep 3869189 = 725473) (by norm_num)
theorem B1935877 : Blo 1719060 1935877 := bbase (se 4 (by rfl) ⟨181488, by rfl⟩ : syracuseStep 1935877 = 362977) (by norm_num)
theorem B4352525 : Blo 1719060 4352525 := bbase (se 3 (by rfl) ⟨816098, by rfl⟩ : syracuseStep 4352525 = 1632197) (by norm_num)
theorem B1935913 : Blo 1719060 1935913 := bbase (se 2 (by rfl) ⟨725967, by rfl⟩ : syracuseStep 1935913 = 1451935) (by norm_num)
theorem B3869261 : Blo 1719060 3869261 := bbase (se 3 (by rfl) ⟨725486, by rfl⟩ : syracuseStep 3869261 = 1450973) (by norm_num)
theorem B1935949 : Blo 1719060 1935949 := bbase (se 3 (by rfl) ⟨362990, by rfl⟩ : syracuseStep 1935949 = 725981) (by norm_num)
theorem B1837657 : Blo 1719060 1837657 := bbase (se 2 (by rfl) ⟨689121, by rfl⟩ : syracuseStep 1837657 = 1378243) (by norm_num)
theorem B2902621 : Blo 1719060 2902621 := bbase (se 3 (by rfl) ⟨544241, by rfl⟩ : syracuseStep 2902621 = 1088483) (by norm_num)
theorem B1837661 : Blo 1719060 1837661 := bbase (se 3 (by rfl) ⟨344561, by rfl⟩ : syracuseStep 1837661 = 689123) (by norm_num)
theorem B1935985 : Blo 1719060 1935985 := bbase (se 2 (by rfl) ⟨725994, by rfl⟩ : syracuseStep 1935985 = 1451989) (by norm_num)
theorem B2755205 : Blo 1719060 2755205 := bbase (se 4 (by rfl) ⟨258300, by rfl⟩ : syracuseStep 2755205 = 516601) (by norm_num)
theorem B1960597 : Blo 1719060 1960597 := bbase (se 6 (by rfl) ⟨45951, by rfl⟩ : syracuseStep 1960597 = 91903) (by norm_num)
theorem B3869333 : Blo 1719060 3869333 := bbase (se 6 (by rfl) ⟨90687, by rfl⟩ : syracuseStep 3869333 = 181375) (by norm_num)
theorem B1936021 : Blo 1719060 1936021 := bbase (se 6 (by rfl) ⟨45375, by rfl⟩ : syracuseStep 1936021 = 90751) (by norm_num)
theorem B6531749 : Blo 1719060 6531749 := bbase (se 4 (by rfl) ⟨612351, by rfl⟩ : syracuseStep 6531749 = 1224703) (by norm_num)
theorem B5802677 : Blo 1719060 5802677 := bbase (se 5 (by rfl) ⟨272000, by rfl⟩ : syracuseStep 5802677 = 544001) (by norm_num)
theorem B2902709 : Blo 1719060 2902709 := bbase (se 5 (by rfl) ⟨136064, by rfl⟩ : syracuseStep 2902709 = 272129) (by norm_num)
theorem B1936057 : Blo 1719060 1936057 := bbase (se 2 (by rfl) ⟨726021, by rfl⟩ : syracuseStep 1936057 = 1452043) (by norm_num)
theorem B4352717 : Blo 1719060 4352717 := bbase (se 3 (by rfl) ⟨816134, by rfl⟩ : syracuseStep 4352717 = 1632269) (by norm_num)
theorem B3869405 : Blo 1719060 3869405 := bbase (se 3 (by rfl) ⟨725513, by rfl⟩ : syracuseStep 3869405 = 1451027) (by norm_num)
theorem B1936093 : Blo 1719060 1936093 := bbase (se 3 (by rfl) ⟨363017, by rfl⟩ : syracuseStep 1936093 = 726035) (by norm_num)
theorem B5966581 : Blo 1719060 5966581 := bbase (se 5 (by rfl) ⟨279683, by rfl⟩ : syracuseStep 5966581 = 559367) (by norm_num)
theorem B8710901 : Blo 1719060 8710901 := bbase (se 5 (by rfl) ⟨408323, by rfl⟩ : syracuseStep 8710901 = 816647) (by norm_num)
theorem B1936129 : Blo 1719060 1936129 := bbase (se 2 (by rfl) ⟨726048, by rfl⟩ : syracuseStep 1936129 = 1452097) (by norm_num)
theorem B3869477 : Blo 1719060 3869477 := bbase (se 4 (by rfl) ⟨362763, by rfl⟩ : syracuseStep 3869477 = 725527) (by norm_num)
theorem B1936165 : Blo 1719060 1936165 := bbase (se 4 (by rfl) ⟨181515, by rfl⟩ : syracuseStep 1936165 = 363031) (by norm_num)
theorem B2902837 : Blo 1719060 2902837 := bbase (se 5 (by rfl) ⟨136070, by rfl⟩ : syracuseStep 2902837 = 272141) (by norm_num)
theorem B5507909 : Blo 1719060 5507909 := bbase (se 4 (by rfl) ⟨516366, by rfl⟩ : syracuseStep 5507909 = 1032733) (by norm_num)
theorem B4131653 : Blo 1719060 4131653 := bbase (se 4 (by rfl) ⟨387342, by rfl⟩ : syracuseStep 4131653 = 774685) (by norm_num)
theorem B3869549 : Blo 1719060 3869549 := bbase (se 3 (by rfl) ⟨725540, by rfl⟩ : syracuseStep 3869549 = 1451081) (by norm_num)
theorem B4647797 : Blo 1719060 4647797 := bbase (se 5 (by rfl) ⟨217865, by rfl⟩ : syracuseStep 4647797 = 435731) (by norm_num)
theorem B3672965 : Blo 1719060 3672965 := bbase (se 4 (by rfl) ⟨344340, by rfl⟩ : syracuseStep 3672965 = 688681) (by norm_num)
theorem B2206597 : Blo 1719060 2206597 := bbase (se 4 (by rfl) ⟨206868, by rfl⟩ : syracuseStep 2206597 = 413737) (by norm_num)
theorem B2902925 : Blo 1719060 2902925 := bbase (se 3 (by rfl) ⟨544298, by rfl⟩ : syracuseStep 2902925 = 1088597) (by norm_num)
theorem B3869621 : Blo 1719060 3869621 := bbase (se 5 (by rfl) ⟨181388, by rfl⟩ : syracuseStep 3869621 = 362777) (by norm_num)
theorem B3869693 : Blo 1719060 3869693 := bbase (se 3 (by rfl) ⟨725567, by rfl⟩ : syracuseStep 3869693 = 1451135) (by norm_num)
theorem B2903053 : Blo 1719060 2903053 := bbase (se 3 (by rfl) ⟨544322, by rfl⟩ : syracuseStep 2903053 = 1088645) (by norm_num)
theorem B4353061 : Blo 1719060 4353061 := bbase (se 4 (by rfl) ⟨408099, by rfl⟩ : syracuseStep 4353061 = 816199) (by norm_num)
theorem B4131893 : Blo 1719060 4131893 := bbase (se 5 (by rfl) ⟨193682, by rfl⟩ : syracuseStep 4131893 = 387365) (by norm_num)
theorem B3869765 : Blo 1719060 3869765 := bbase (se 4 (by rfl) ⟨362790, by rfl⟩ : syracuseStep 3869765 = 725581) (by norm_num)
theorem B7842901 : Blo 1719060 7842901 := bbase (se 8 (by rfl) ⟨45954, by rfl⟩ : syracuseStep 7842901 = 91909) (by norm_num)
theorem B3263581 : Blo 1719060 3263581 := bbase (se 3 (by rfl) ⟨611921, by rfl⟩ : syracuseStep 3263581 = 1223843) (by norm_num)
theorem B5803109 : Blo 1719060 5803109 := bbase (se 4 (by rfl) ⟨544041, by rfl⟩ : syracuseStep 5803109 = 1088083) (by norm_num)
theorem B2903141 : Blo 1719060 2903141 := bbase (se 4 (by rfl) ⟨272169, by rfl⟩ : syracuseStep 2903141 = 544339) (by norm_num)
theorem B7351397 : Blo 1719060 7351397 := bbase (se 4 (by rfl) ⟨689193, by rfl⟩ : syracuseStep 7351397 = 1378387) (by norm_num)
theorem B3869837 : Blo 1719060 3869837 := bbase (se 3 (by rfl) ⟨725594, by rfl⟩ : syracuseStep 3869837 = 1451189) (by norm_num)
theorem B8703125 : Blo 1719060 8703125 := bbase (se 6 (by rfl) ⟨203979, by rfl⟩ : syracuseStep 8703125 = 407959) (by norm_num)
theorem B4353173 : Blo 1719060 4353173 := bbase (se 6 (by rfl) ⟨102027, by rfl⟩ : syracuseStep 4353173 = 204055) (by norm_num)
theorem B5885077 : Blo 1719060 5885077 := bbase (se 6 (by rfl) ⟨137931, by rfl⟩ : syracuseStep 5885077 = 275863) (by norm_num)
theorem B24792277 : Blo 1719060 24792277 := bbase (se 7 (by rfl) ⟨290534, by rfl⟩ : syracuseStep 24792277 = 581069) (by norm_num)
theorem B3869909 : Blo 1719060 3869909 := bbase (se 7 (by rfl) ⟨45350, by rfl⟩ : syracuseStep 3869909 = 90701) (by norm_num)
theorem B8269013 : Blo 1719060 8269013 := bbase (se 7 (by rfl) ⟨96902, by rfl⟩ : syracuseStep 8269013 = 193805) (by norm_num)
theorem B2903269 : Blo 1719060 2903269 := bbase (se 4 (by rfl) ⟨272181, by rfl⟩ : syracuseStep 2903269 = 544363) (by norm_num)
theorem B3869981 : Blo 1719060 3869981 := bbase (se 3 (by rfl) ⟨725621, by rfl⟩ : syracuseStep 3869981 = 1451243) (by norm_num)
theorem B2903357 : Blo 1719060 2903357 := bbase (se 3 (by rfl) ⟨544379, by rfl⟩ : syracuseStep 2903357 = 1088759) (by norm_num)
theorem B4353365 : Blo 1719060 4353365 := bbase (se 11 (by rfl) ⟨3188, by rfl⟩ : syracuseStep 4353365 = 6377) (by norm_num)
theorem B3870053 : Blo 1719060 3870053 := bbase (se 4 (by rfl) ⟨362817, by rfl⟩ : syracuseStep 3870053 = 725635) (by norm_num)
theorem B3485053 : Blo 1719060 3485053 := bbase (se 3 (by rfl) ⟨653447, by rfl⟩ : syracuseStep 3485053 = 1306895) (by norm_num)
theorem B3263885 : Blo 1719060 3263885 := bbase (se 3 (by rfl) ⟨611978, by rfl⟩ : syracuseStep 3263885 = 1223957) (by norm_num)
theorem B3100045 : Blo 1719060 3100045 := bbase (se 3 (by rfl) ⟨581258, by rfl⟩ : syracuseStep 3100045 = 1162517) (by norm_num)
theorem B3870125 : Blo 1719060 3870125 := bbase (se 3 (by rfl) ⟨725648, by rfl⟩ : syracuseStep 3870125 = 1451297) (by norm_num)
theorem B2903485 : Blo 1719060 2903485 := bbase (se 3 (by rfl) ⟨544403, by rfl⟩ : syracuseStep 2903485 = 1088807) (by norm_num)
theorem B3870197 : Blo 1719060 3870197 := bbase (se 5 (by rfl) ⟨181415, by rfl⟩ : syracuseStep 3870197 = 362831) (by norm_num)
theorem B1961473 : Blo 1719060 1961473 := bbase (se 2 (by rfl) ⟨735552, by rfl⟩ : syracuseStep 1961473 = 1471105) (by norm_num)
theorem B5803541 : Blo 1719060 5803541 := bbase (se 6 (by rfl) ⟨136020, by rfl⟩ : syracuseStep 5803541 = 272041) (by norm_num)
theorem B2903573 : Blo 1719060 2903573 := bbase (se 6 (by rfl) ⟨68052, by rfl⟩ : syracuseStep 2903573 = 136105) (by norm_num)
theorem B3100189 : Blo 1719060 3100189 := bbase (se 3 (by rfl) ⟨581285, by rfl⟩ : syracuseStep 3100189 = 1162571) (by norm_num)
theorem B9801269 : Blo 1719060 9801269 := bbase (se 5 (by rfl) ⟨459434, by rfl⟩ : syracuseStep 9801269 = 918869) (by norm_num)
theorem B3870269 : Blo 1719060 3870269 := bbase (se 3 (by rfl) ⟨725675, by rfl⟩ : syracuseStep 3870269 = 1451351) (by norm_num)
theorem B3100261 : Blo 1719060 3100261 := bbase (se 4 (by rfl) ⟨290649, by rfl⟩ : syracuseStep 3100261 = 581299) (by norm_num)
theorem B2756197 : Blo 1719060 2756197 := bbase (se 4 (by rfl) ⟨258393, by rfl⟩ : syracuseStep 2756197 = 516787) (by norm_num)
theorem B3870341 : Blo 1719060 3870341 := bbase (se 4 (by rfl) ⟨362844, by rfl⟩ : syracuseStep 3870341 = 725689) (by norm_num)
theorem B2903701 : Blo 1719060 2903701 := bbase (se 6 (by rfl) ⟨68055, by rfl⟩ : syracuseStep 2903701 = 136111) (by norm_num)
theorem B4353709 : Blo 1719060 4353709 := bbase (se 3 (by rfl) ⟨816320, by rfl⟩ : syracuseStep 4353709 = 1632641) (by norm_num)
theorem B3534509 : Blo 1719060 3534509 := bbase (se 3 (by rfl) ⟨662720, by rfl⟩ : syracuseStep 3534509 = 1325441) (by norm_num)
theorem B3870413 : Blo 1719060 3870413 := bbase (se 3 (by rfl) ⟨725702, by rfl⟩ : syracuseStep 3870413 = 1451405) (by norm_num)
theorem B2903789 : Blo 1719060 2903789 := bbase (se 3 (by rfl) ⟨544460, by rfl⟩ : syracuseStep 2903789 = 1088921) (by norm_num)
theorem B3673853 : Blo 1719060 3673853 := bbase (se 3 (by rfl) ⟨688847, by rfl⟩ : syracuseStep 3673853 = 1377695) (by norm_num)
theorem B3870485 : Blo 1719060 3870485 := bbase (se 6 (by rfl) ⟨90714, by rfl⟩ : syracuseStep 3870485 = 181429) (by norm_num)
theorem B4353821 : Blo 1719060 4353821 := bbase (se 3 (by rfl) ⟨816341, by rfl⟩ : syracuseStep 4353821 = 1632683) (by norm_num)
theorem B3485501 : Blo 1719060 3485501 := bbase (se 3 (by rfl) ⟨653531, by rfl⟩ : syracuseStep 3485501 = 1307063) (by norm_num)
theorem B6532933 : Blo 1719060 6532933 := bbase (se 4 (by rfl) ⟨612462, by rfl⟩ : syracuseStep 6532933 = 1224925) (by norm_num)
theorem B8376149 : Blo 1719060 8376149 := bbase (se 9 (by rfl) ⟨24539, by rfl⟩ : syracuseStep 8376149 = 49079) (by norm_num)
theorem B3870557 : Blo 1719060 3870557 := bbase (se 3 (by rfl) ⟨725729, by rfl⟩ : syracuseStep 3870557 = 1451459) (by norm_num)
theorem B2903917 : Blo 1719060 2903917 := bbase (se 3 (by rfl) ⟨544484, by rfl⟩ : syracuseStep 2903917 = 1088969) (by norm_num)
theorem B3673973 : Blo 1719060 3673973 := bbase (se 5 (by rfl) ⟨172217, by rfl⟩ : syracuseStep 3673973 = 344435) (by norm_num)
theorem B3870629 : Blo 1719060 3870629 := bbase (se 4 (by rfl) ⟨362871, by rfl⟩ : syracuseStep 3870629 = 725743) (by norm_num)
theorem B1961893 : Blo 1719060 1961893 := bbase (se 4 (by rfl) ⟨183927, by rfl⟩ : syracuseStep 1961893 = 367855) (by norm_num)
theorem B5803973 : Blo 1719060 5803973 := bbase (se 4 (by rfl) ⟨544122, by rfl⟩ : syracuseStep 5803973 = 1088245) (by norm_num)
theorem B2904005 : Blo 1719060 2904005 := bbase (se 4 (by rfl) ⟨272250, by rfl⟩ : syracuseStep 2904005 = 544501) (by norm_num)
theorem B4354013 : Blo 1719060 4354013 := bbase (se 3 (by rfl) ⟨816377, by rfl⟩ : syracuseStep 4354013 = 1632755) (by norm_num)
theorem B1961957 : Blo 1719060 1961957 := bbase (se 4 (by rfl) ⟨183933, by rfl⟩ : syracuseStep 1961957 = 367867) (by norm_num)
theorem B3870701 : Blo 1719060 3870701 := bbase (se 3 (by rfl) ⟨725756, by rfl⟩ : syracuseStep 3870701 = 1451513) (by norm_num)
theorem B8712197 : Blo 1719060 8712197 := bbase (se 4 (by rfl) ⟨816768, by rfl⟩ : syracuseStep 8712197 = 1633537) (by norm_num)
theorem B3870773 : Blo 1719060 3870773 := bbase (se 5 (by rfl) ⟨181442, by rfl⟩ : syracuseStep 3870773 = 362885) (by norm_num)
theorem B2904133 : Blo 1719060 2904133 := bbase (se 4 (by rfl) ⟨272262, by rfl⟩ : syracuseStep 2904133 = 544525) (by norm_num)
theorem B6533237 : Blo 1719060 6533237 := bbase (se 5 (by rfl) ⟨306245, by rfl⟩ : syracuseStep 6533237 = 612491) (by norm_num)
theorem B3264637 : Blo 1719060 3264637 := bbase (se 3 (by rfl) ⟨612119, by rfl⟩ : syracuseStep 3264637 = 1224239) (by norm_num)
theorem B3870845 : Blo 1719060 3870845 := bbase (se 3 (by rfl) ⟨725783, by rfl⟩ : syracuseStep 3870845 = 1451567) (by norm_num)
theorem B2904221 : Blo 1719060 2904221 := bbase (se 3 (by rfl) ⟨544541, by rfl⟩ : syracuseStep 2904221 = 1089083) (by norm_num)
theorem B3870917 : Blo 1719060 3870917 := bbase (se 4 (by rfl) ⟨362898, by rfl⟩ : syracuseStep 3870917 = 725797) (by norm_num)
theorem B7344341 : Blo 1719060 7344341 := bbase (se 7 (by rfl) ⟨86066, by rfl⟩ : syracuseStep 7344341 = 172133) (by norm_num)
theorem B3264781 : Blo 1719060 3264781 := bbase (se 3 (by rfl) ⟨612146, by rfl⟩ : syracuseStep 3264781 = 1224293) (by norm_num)
theorem B3870989 : Blo 1719060 3870989 := bbase (se 3 (by rfl) ⟨725810, by rfl⟩ : syracuseStep 3870989 = 1451621) (by norm_num)
theorem B4354357 : Blo 1719060 4354357 := bbase (se 5 (by rfl) ⟨204110, by rfl⟩ : syracuseStep 4354357 = 408221) (by norm_num)
theorem B3871061 : Blo 1719060 3871061 := bbase (se 10 (by rfl) ⟨5670, by rfl⟩ : syracuseStep 3871061 = 11341) (by norm_num)
theorem B5804405 : Blo 1719060 5804405 := bbase (se 5 (by rfl) ⟨272081, by rfl⟩ : syracuseStep 5804405 = 544163) (by norm_num)
theorem B3871133 : Blo 1719060 3871133 := bbase (se 3 (by rfl) ⟨725837, by rfl⟩ : syracuseStep 3871133 = 1451675) (by norm_num)
theorem B8704421 : Blo 1719060 8704421 := bbase (se 4 (by rfl) ⟨816039, by rfl⟩ : syracuseStep 8704421 = 1632079) (by norm_num)
theorem B4354469 : Blo 1719060 4354469 := bbase (se 4 (by rfl) ⟨408231, by rfl⟩ : syracuseStep 4354469 = 816463) (by norm_num)
theorem B3264941 : Blo 1719060 3264941 := bbase (se 3 (by rfl) ⟨612176, by rfl⟩ : syracuseStep 3264941 = 1224353) (by norm_num)
theorem B4411837 : Blo 1719060 4411837 := bbase (se 3 (by rfl) ⟨827219, by rfl⟩ : syracuseStep 4411837 = 1654439) (by norm_num)
theorem B3871205 : Blo 1719060 3871205 := bbase (se 4 (by rfl) ⟨362925, by rfl⟩ : syracuseStep 3871205 = 725851) (by norm_num)
theorem B3674605 : Blo 1719060 3674605 := bbase (se 3 (by rfl) ⟨688988, by rfl⟩ : syracuseStep 3674605 = 1377977) (by norm_num)
theorem B19599893 : Blo 1719060 19599893 := bbase (se 6 (by rfl) ⟨459372, by rfl⟩ : syracuseStep 19599893 = 918745) (by norm_num)
theorem B3871277 : Blo 1719060 3871277 := bbase (se 3 (by rfl) ⟨725864, by rfl⟩ : syracuseStep 3871277 = 1451729) (by norm_num)
theorem B3265085 : Blo 1719060 3265085 := bbase (se 3 (by rfl) ⟨612203, by rfl⟩ : syracuseStep 3265085 = 1224407) (by norm_num)
theorem B16536149 : Blo 1719060 16536149 := bbase (se 8 (by rfl) ⟨96891, by rfl⟩ : syracuseStep 16536149 = 193783) (by norm_num)
theorem B4354661 : Blo 1719060 4354661 := bbase (se 4 (by rfl) ⟨408249, by rfl⟩ : syracuseStep 4354661 = 816499) (by norm_num)
theorem B3871349 : Blo 1719060 3871349 := bbase (se 5 (by rfl) ⟨181469, by rfl⟩ : syracuseStep 3871349 = 362939) (by norm_num)
theorem B29397653 : Blo 1719060 29397653 := bbase (se 6 (by rfl) ⟨689007, by rfl⟩ : syracuseStep 29397653 = 1378015) (by norm_num)
theorem B3871421 : Blo 1719060 3871421 := bbase (se 3 (by rfl) ⟨725891, by rfl⟩ : syracuseStep 3871421 = 1451783) (by norm_num)
theorem B4649669 : Blo 1719060 4649669 := bbase (se 4 (by rfl) ⟨435906, by rfl⟩ : syracuseStep 4649669 = 871813) (by norm_num)
theorem B4133605 : Blo 1719060 4133605 := bbase (se 4 (by rfl) ⟨387525, by rfl⟩ : syracuseStep 4133605 = 775051) (by norm_num)
theorem B3871493 : Blo 1719060 3871493 := bbase (se 4 (by rfl) ⟨362952, by rfl⟩ : syracuseStep 3871493 = 725905) (by norm_num)
theorem B2175761 : Blo 1719060 2175761 := bbase (se 2 (by rfl) ⟨815910, by rfl⟩ : syracuseStep 2175761 = 1631821) (by norm_num)
theorem B5804837 : Blo 1719060 5804837 := bbase (se 4 (by rfl) ⟨544203, by rfl⟩ : syracuseStep 5804837 = 1088407) (by norm_num)
theorem B2175817 : Blo 1719060 2175817 := bbase (se 2 (by rfl) ⟨815931, by rfl⟩ : syracuseStep 2175817 = 1631863) (by norm_num)
theorem B3871565 : Blo 1719060 3871565 := bbase (se 3 (by rfl) ⟨725918, by rfl⟩ : syracuseStep 3871565 = 1451837) (by norm_num)
theorem B25146197 : Blo 1719060 25146197 := bbase (se 9 (by rfl) ⟨73670, by rfl⟩ : syracuseStep 25146197 = 147341) (by norm_num)
theorem B3265373 : Blo 1719060 3265373 := bbase (se 3 (by rfl) ⟨612257, by rfl⟩ : syracuseStep 3265373 = 1224515) (by norm_num)
theorem B4412269 : Blo 1719060 4412269 := bbase (se 3 (by rfl) ⟨827300, by rfl⟩ : syracuseStep 4412269 = 1654601) (by norm_num)
theorem B3871637 : Blo 1719060 3871637 := bbase (se 6 (by rfl) ⟨90741, by rfl⟩ : syracuseStep 3871637 = 181483) (by norm_num)
theorem B2175913 : Blo 1719060 2175913 := bbase (se 2 (by rfl) ⟨815967, by rfl⟩ : syracuseStep 2175913 = 1631935) (by norm_num)
theorem B4355005 : Blo 1719060 4355005 := bbase (se 3 (by rfl) ⟨816563, by rfl⟩ : syracuseStep 4355005 = 1633127) (by norm_num)
theorem B5510101 : Blo 1719060 5510101 := bbase (se 7 (by rfl) ⟨64571, by rfl⟩ : syracuseStep 5510101 = 129143) (by norm_num)
theorem B3871709 : Blo 1719060 3871709 := bbase (se 3 (by rfl) ⟨725945, by rfl⟩ : syracuseStep 3871709 = 1451891) (by norm_num)
theorem B3265525 : Blo 1719060 3265525 := bbase (se 5 (by rfl) ⟨153071, by rfl⟩ : syracuseStep 3265525 = 306143) (by norm_num)
theorem B3871781 : Blo 1719060 3871781 := bbase (se 4 (by rfl) ⟨362979, by rfl⟩ : syracuseStep 3871781 = 725959) (by norm_num)
theorem B4355117 : Blo 1719060 4355117 := bbase (se 3 (by rfl) ⟨816584, by rfl⟩ : syracuseStep 4355117 = 1633169) (by norm_num)
theorem B2176085 : Blo 1719060 2176085 := bbase (se 8 (by rfl) ⟨12750, by rfl⟩ : syracuseStep 2176085 = 25501) (by norm_num)
theorem B3871853 : Blo 1719060 3871853 := bbase (se 3 (by rfl) ⟨725972, by rfl⟩ : syracuseStep 3871853 = 1451945) (by norm_num)
theorem B2176141 : Blo 1719060 2176141 := bbase (se 3 (by rfl) ⟨408026, by rfl⟩ : syracuseStep 2176141 = 816053) (by norm_num)
theorem B3486869 : Blo 1719060 3486869 := bbase (se 6 (by rfl) ⟨81723, by rfl⟩ : syracuseStep 3486869 = 163447) (by norm_num)
theorem B3871925 : Blo 1719060 3871925 := bbase (se 5 (by rfl) ⟨181496, by rfl⟩ : syracuseStep 3871925 = 362993) (by norm_num)
theorem B7345349 : Blo 1719060 7345349 := bbase (se 4 (by rfl) ⟨688626, by rfl⟩ : syracuseStep 7345349 = 1377253) (by norm_num)
theorem B5805269 : Blo 1719060 5805269 := bbase (se 7 (by rfl) ⟨68030, by rfl⟩ : syracuseStep 5805269 = 136061) (by norm_num)
theorem B2176237 : Blo 1719060 2176237 := bbase (se 3 (by rfl) ⟨408044, by rfl⟩ : syracuseStep 2176237 = 816089) (by norm_num)
theorem B4355309 : Blo 1719060 4355309 := bbase (se 3 (by rfl) ⟨816620, by rfl⟩ : syracuseStep 4355309 = 1633241) (by norm_num)
theorem B5231861 : Blo 1719060 5231861 := bbase (se 5 (by rfl) ⟨245243, by rfl⟩ : syracuseStep 5231861 = 490487) (by norm_num)
theorem B3871997 : Blo 1719060 3871997 := bbase (se 3 (by rfl) ⟨725999, by rfl⟩ : syracuseStep 3871997 = 1451999) (by norm_num)
theorem B3265829 : Blo 1719060 3265829 := bbase (se 4 (by rfl) ⟨306171, by rfl⟩ : syracuseStep 3265829 = 612343) (by norm_num)
theorem B3872069 : Blo 1719060 3872069 := bbase (se 4 (by rfl) ⟨363006, by rfl⟩ : syracuseStep 3872069 = 726013) (by norm_num)
theorem B11015509 : Blo 1719060 11015509 := bbase (se 14 (by rfl) ⟨1008, by rfl⟩ : syracuseStep 11015509 = 2017) (by norm_num)
theorem B6976853 : Blo 1719060 6976853 := bbase (se 13 (by rfl) ⟨1277, by rfl⟩ : syracuseStep 6976853 = 2555) (by norm_num)
theorem B4896101 : Blo 1719060 4896101 := bbase (se 4 (by rfl) ⟨459009, by rfl⟩ : syracuseStep 4896101 = 918019) (by norm_num)
theorem B3675493 : Blo 1719060 3675493 := bbase (se 4 (by rfl) ⟨344577, by rfl⟩ : syracuseStep 3675493 = 689155) (by norm_num)
theorem B2094445 : Blo 1719060 2094445 := bbase (se 3 (by rfl) ⟨392708, by rfl⟩ : syracuseStep 2094445 = 785417) (by norm_num)
theorem B3872141 : Blo 1719060 3872141 := bbase (se 3 (by rfl) ⟨726026, by rfl⟩ : syracuseStep 3872141 = 1452053) (by norm_num)
theorem B6198677 : Blo 1719060 6198677 := bbase (se 6 (by rfl) ⟨145281, by rfl⟩ : syracuseStep 6198677 = 290563) (by norm_num)
theorem B2176409 : Blo 1719060 2176409 := bbase (se 2 (by rfl) ⟨816153, by rfl⟩ : syracuseStep 2176409 = 1632307) (by norm_num)
theorem B2176465 : Blo 1719060 2176465 := bbase (se 2 (by rfl) ⟨816174, by rfl⟩ : syracuseStep 2176465 = 1632349) (by norm_num)
theorem B3872213 : Blo 1719060 3872213 := bbase (se 7 (by rfl) ⟨45377, by rfl⟩ : syracuseStep 3872213 = 90755) (by norm_num)
theorem B3675613 : Blo 1719060 3675613 := bbase (se 3 (by rfl) ⟨689177, by rfl⟩ : syracuseStep 3675613 = 1378355) (by norm_num)
theorem B3872285 : Blo 1719060 3872285 := bbase (se 3 (by rfl) ⟨726053, by rfl⟩ : syracuseStep 3872285 = 1452107) (by norm_num)
theorem B2176561 : Blo 1719060 2176561 := bbase (se 2 (by rfl) ⟨816210, by rfl⟩ : syracuseStep 2176561 = 1632421) (by norm_num)
theorem B4355653 : Blo 1719060 4355653 := bbase (se 4 (by rfl) ⟨408342, by rfl⟩ : syracuseStep 4355653 = 816685) (by norm_num)
theorem B3872357 : Blo 1719060 3872357 := bbase (se 4 (by rfl) ⟨363033, by rfl⟩ : syracuseStep 3872357 = 726067) (by norm_num)
theorem B5805701 : Blo 1719060 5805701 := bbase (se 4 (by rfl) ⟨544284, by rfl⟩ : syracuseStep 5805701 = 1088569) (by norm_num)
theorem B8705717 : Blo 1719060 8705717 := bbase (se 5 (by rfl) ⟨408080, by rfl⟩ : syracuseStep 8705717 = 816161) (by norm_num)
theorem B4355765 : Blo 1719060 4355765 := bbase (se 5 (by rfl) ⟨204176, by rfl⟩ : syracuseStep 4355765 = 408353) (by norm_num)
theorem B33052373 : Blo 1719060 33052373 := bbase (se 7 (by rfl) ⟨387332, by rfl⟩ : syracuseStep 33052373 = 774665) (by norm_num)
theorem B2176733 : Blo 1719060 2176733 := bbase (se 3 (by rfl) ⟨408137, by rfl⟩ : syracuseStep 2176733 = 816275) (by norm_num)
theorem B2651869 : Blo 1719060 2651869 := bbase (se 3 (by rfl) ⟨497225, by rfl⟩ : syracuseStep 2651869 = 994451) (by norm_num)
theorem B2176789 : Blo 1719060 2176789 := bbase (se 6 (by rfl) ⟨51018, by rfl⟩ : syracuseStep 2176789 = 102037) (by norm_num)
theorem B5510933 : Blo 1719060 5510933 := bbase (se 6 (by rfl) ⟨129162, by rfl⟩ : syracuseStep 5510933 = 258325) (by norm_num)
theorem B2094913 : Blo 1719060 2094913 := bbase (se 2 (by rfl) ⟨785592, by rfl⟩ : syracuseStep 2094913 = 1571185) (by norm_num)
theorem B2176885 : Blo 1719060 2176885 := bbase (se 5 (by rfl) ⟨102041, by rfl⟩ : syracuseStep 2176885 = 204083) (by norm_num)
theorem B4355957 : Blo 1719060 4355957 := bbase (se 5 (by rfl) ⟨204185, by rfl⟩ : syracuseStep 4355957 = 408371) (by norm_num)
theorem B2095025 : Blo 1719060 2095025 := bbase (se 2 (by rfl) ⟨785634, by rfl⟩ : syracuseStep 2095025 = 1571269) (by norm_num)
theorem B3266581 : Blo 1719060 3266581 := bbase (se 6 (by rfl) ⟨76560, by rfl⟩ : syracuseStep 3266581 = 153121) (by norm_num)
theorem B2177057 : Blo 1719060 2177057 := bbase (se 2 (by rfl) ⟨816396, by rfl⟩ : syracuseStep 2177057 = 1632793) (by norm_num)
theorem B6617141 : Blo 1719060 6617141 := bbase (se 5 (by rfl) ⟨310178, by rfl⟩ : syracuseStep 6617141 = 620357) (by norm_num)
theorem B5806133 : Blo 1719060 5806133 := bbase (se 5 (by rfl) ⟨272162, by rfl⟩ : syracuseStep 5806133 = 544325) (by norm_num)
theorem B2177113 : Blo 1719060 2177113 := bbase (se 2 (by rfl) ⟨816417, by rfl⟩ : syracuseStep 2177113 = 1632835) (by norm_num)
theorem B7846021 : Blo 1719060 7846021 := bbase (se 4 (by rfl) ⟨735564, by rfl⟩ : syracuseStep 7846021 = 1471129) (by norm_num)
theorem B4135045 : Blo 1719060 4135045 := bbase (se 4 (by rfl) ⟨387660, by rfl⟩ : syracuseStep 4135045 = 775321) (by norm_num)
theorem B3266725 : Blo 1719060 3266725 := bbase (se 4 (by rfl) ⟨306255, by rfl⟩ : syracuseStep 3266725 = 612511) (by norm_num)
theorem B2578613 : Blo 1719060 2578613 := bbase (se 5 (by rfl) ⟨120872, by rfl⟩ : syracuseStep 2578613 = 241745) (by norm_num)
theorem B2177209 : Blo 1719060 2177209 := bbase (se 2 (by rfl) ⟨816453, by rfl⟩ : syracuseStep 2177209 = 1632907) (by norm_num)
theorem B2578637 : Blo 1719060 2578637 := bbase (se 3 (by rfl) ⟨483494, by rfl⟩ : syracuseStep 2578637 = 966989) (by norm_num)
theorem B4356301 : Blo 1719060 4356301 := bbase (se 3 (by rfl) ⟨816806, by rfl⟩ : syracuseStep 4356301 = 1633613) (by norm_num)
theorem B2578661 : Blo 1719060 2578661 := bbase (se 4 (by rfl) ⟨241749, by rfl⟩ : syracuseStep 2578661 = 483499) (by norm_num)
theorem B2578685 : Blo 1719060 2578685 := bbase (se 3 (by rfl) ⟨483503, by rfl⟩ : syracuseStep 2578685 = 967007) (by norm_num)
theorem B2578709 : Blo 1719060 2578709 := bbase (se 6 (by rfl) ⟨60438, by rfl⟩ : syracuseStep 2578709 = 120877) (by norm_num)
theorem B2578733 : Blo 1719060 2578733 := bbase (se 3 (by rfl) ⟨483512, by rfl⟩ : syracuseStep 2578733 = 967025) (by norm_num)
theorem B4356413 : Blo 1719060 4356413 := bbase (se 3 (by rfl) ⟨816827, by rfl⟩ : syracuseStep 4356413 = 1633655) (by norm_num)
theorem B2578757 : Blo 1719060 2578757 := bbase (se 4 (by rfl) ⟨241758, by rfl⟩ : syracuseStep 2578757 = 483517) (by norm_num)
theorem B3488069 : Blo 1719060 3488069 := bbase (se 4 (by rfl) ⟨327006, by rfl⟩ : syracuseStep 3488069 = 654013) (by norm_num)
theorem B3266885 : Blo 1719060 3266885 := bbase (se 4 (by rfl) ⟨306270, by rfl⟩ : syracuseStep 3266885 = 612541) (by norm_num)
theorem B2578781 : Blo 1719060 2578781 := bbase (se 3 (by rfl) ⟨483521, by rfl⟩ : syracuseStep 2578781 = 967043) (by norm_num)
theorem B2177381 : Blo 1719060 2177381 := bbase (se 4 (by rfl) ⟨204129, by rfl⟩ : syracuseStep 2177381 = 408259) (by norm_num)
theorem B2578805 : Blo 1719060 2578805 := bbase (se 5 (by rfl) ⟨120881, by rfl⟩ : syracuseStep 2578805 = 241763) (by norm_num)
theorem B2447749 : Blo 1719060 2447749 := bbase (se 4 (by rfl) ⟨229476, by rfl⟩ : syracuseStep 2447749 = 458953) (by norm_num)
theorem B6199685 : Blo 1719060 6199685 := bbase (se 4 (by rfl) ⟨581220, by rfl⟩ : syracuseStep 6199685 = 1162441) (by norm_num)
theorem B2578829 : Blo 1719060 2578829 := bbase (se 3 (by rfl) ⟨483530, by rfl⟩ : syracuseStep 2578829 = 967061) (by norm_num)
theorem B2357653 : Blo 1719060 2357653 := bbase (se 6 (by rfl) ⟨55257, by rfl⟩ : syracuseStep 2357653 = 110515) (by norm_num)
theorem B2177437 : Blo 1719060 2177437 := bbase (se 3 (by rfl) ⟨408269, by rfl⟩ : syracuseStep 2177437 = 816539) (by norm_num)
theorem B2578853 : Blo 1719060 2578853 := bbase (se 4 (by rfl) ⟨241767, by rfl⟩ : syracuseStep 2578853 = 483535) (by norm_num)
theorem B2578877 : Blo 1719060 2578877 := bbase (se 3 (by rfl) ⟨483539, by rfl⟩ : syracuseStep 2578877 = 967079) (by norm_num)
theorem B1743301 : Blo 1719060 1743301 := bbase (se 4 (by rfl) ⟨163434, by rfl⟩ : syracuseStep 1743301 = 326869) (by norm_num)
theorem B2578901 : Blo 1719060 2578901 := bbase (se 7 (by rfl) ⟨30221, by rfl⟩ : syracuseStep 2578901 = 60443) (by norm_num)
theorem B3267029 : Blo 1719060 3267029 := bbase (se 7 (by rfl) ⟨38285, by rfl⟩ : syracuseStep 3267029 = 76571) (by norm_num)
theorem B5806565 : Blo 1719060 5806565 := bbase (se 4 (by rfl) ⟨544365, by rfl⟩ : syracuseStep 5806565 = 1088731) (by norm_num)
theorem B2578925 : Blo 1719060 2578925 := bbase (se 3 (by rfl) ⟨483548, by rfl⟩ : syracuseStep 2578925 = 967097) (by norm_num)
theorem B2357741 : Blo 1719060 2357741 := bbase (se 3 (by rfl) ⟨442076, by rfl⟩ : syracuseStep 2357741 = 884153) (by norm_num)
theorem B2177533 : Blo 1719060 2177533 := bbase (se 3 (by rfl) ⟨408287, by rfl⟩ : syracuseStep 2177533 = 816575) (by norm_num)
theorem B2578949 : Blo 1719060 2578949 := bbase (se 4 (by rfl) ⟨241776, by rfl⟩ : syracuseStep 2578949 = 483553) (by norm_num)
theorem B2578973 : Blo 1719060 2578973 := bbase (se 3 (by rfl) ⟨483557, by rfl⟩ : syracuseStep 2578973 = 967115) (by norm_num)
theorem B2578997 : Blo 1719060 2578997 := bbase (se 5 (by rfl) ⟨120890, by rfl⟩ : syracuseStep 2578997 = 241781) (by norm_num)
theorem B2579021 : Blo 1719060 2579021 := bbase (se 3 (by rfl) ⟨483566, by rfl⟩ : syracuseStep 2579021 = 967133) (by norm_num)
theorem B6527573 : Blo 1719060 6527573 := bbase (se 8 (by rfl) ⟨38247, by rfl⟩ : syracuseStep 6527573 = 76495) (by norm_num)
theorem B2579045 : Blo 1719060 2579045 := bbase (se 4 (by rfl) ⟨241785, by rfl⟩ : syracuseStep 2579045 = 483571) (by norm_num)
theorem B2579069 : Blo 1719060 2579069 := bbase (se 3 (by rfl) ⟨483575, by rfl⟩ : syracuseStep 2579069 = 967151) (by norm_num)
theorem B2579093 : Blo 1719060 2579093 := bbase (se 6 (by rfl) ⟨60447, by rfl⟩ : syracuseStep 2579093 = 120895) (by norm_num)
theorem B2177705 : Blo 1719060 2177705 := bbase (se 2 (by rfl) ⟨816639, by rfl⟩ : syracuseStep 2177705 = 1633279) (by norm_num)
theorem B2579117 : Blo 1719060 2579117 := bbase (se 3 (by rfl) ⟨483584, by rfl⟩ : syracuseStep 2579117 = 967169) (by norm_num)
theorem B10459829 : Blo 1719060 10459829 := bbase (se 5 (by rfl) ⟨490304, by rfl⟩ : syracuseStep 10459829 = 980609) (by norm_num)
theorem B2579141 : Blo 1719060 2579141 := bbase (se 4 (by rfl) ⟨241794, by rfl⟩ : syracuseStep 2579141 = 483589) (by norm_num)
theorem B2448085 : Blo 1719060 2448085 := bbase (se 7 (by rfl) ⟨28688, by rfl⟩ : syracuseStep 2448085 = 57377) (by norm_num)
theorem B2579165 : Blo 1719060 2579165 := bbase (se 3 (by rfl) ⟨483593, by rfl⟩ : syracuseStep 2579165 = 967187) (by norm_num)
theorem B2177761 : Blo 1719060 2177761 := bbase (se 2 (by rfl) ⟨816660, by rfl⟩ : syracuseStep 2177761 = 1633321) (by norm_num)
theorem B2579189 : Blo 1719060 2579189 := bbase (se 5 (by rfl) ⟨120899, by rfl⟩ : syracuseStep 2579189 = 241799) (by norm_num)
theorem B3267317 : Blo 1719060 3267317 := bbase (se 5 (by rfl) ⟨153155, by rfl⟩ : syracuseStep 3267317 = 306311) (by norm_num)
theorem B2579213 : Blo 1719060 2579213 := bbase (se 3 (by rfl) ⟨483602, by rfl⟩ : syracuseStep 2579213 = 967205) (by norm_num)
theorem B1743637 : Blo 1719060 1743637 := bbase (se 6 (by rfl) ⟨40866, by rfl⟩ : syracuseStep 1743637 = 81733) (by norm_num)
theorem B2579237 : Blo 1719060 2579237 := bbase (se 4 (by rfl) ⟨241803, by rfl⟩ : syracuseStep 2579237 = 483607) (by norm_num)
theorem B2579261 : Blo 1719060 2579261 := bbase (se 3 (by rfl) ⟨483611, by rfl⟩ : syracuseStep 2579261 = 967223) (by norm_num)
theorem B2177857 : Blo 1719060 2177857 := bbase (se 2 (by rfl) ⟨816696, by rfl⟩ : syracuseStep 2177857 = 1633393) (by norm_num)
theorem B2579285 : Blo 1719060 2579285 := bbase (se 9 (by rfl) ⟨7556, by rfl⟩ : syracuseStep 2579285 = 15113) (by norm_num)
theorem B2579309 : Blo 1719060 2579309 := bbase (se 3 (by rfl) ⟨483620, by rfl⟩ : syracuseStep 2579309 = 967241) (by norm_num)
theorem B6527861 : Blo 1719060 6527861 := bbase (se 5 (by rfl) ⟨305993, by rfl⟩ : syracuseStep 6527861 = 611987) (by norm_num)
theorem B2579333 : Blo 1719060 2579333 := bbase (se 4 (by rfl) ⟨241812, by rfl⟩ : syracuseStep 2579333 = 483625) (by norm_num)
theorem B4897685 : Blo 1719060 4897685 := bbase (se 6 (by rfl) ⟨114789, by rfl⟩ : syracuseStep 4897685 = 229579) (by norm_num)
theorem B5806997 : Blo 1719060 5806997 := bbase (se 6 (by rfl) ⟨136101, by rfl⟩ : syracuseStep 5806997 = 272203) (by norm_num)
theorem B2579357 : Blo 1719060 2579357 := bbase (se 3 (by rfl) ⟨483629, by rfl⟩ : syracuseStep 2579357 = 967259) (by norm_num)
theorem B2448301 : Blo 1719060 2448301 := bbase (se 3 (by rfl) ⟨459056, by rfl⟩ : syracuseStep 2448301 = 918113) (by norm_num)
theorem B2579381 : Blo 1719060 2579381 := bbase (se 5 (by rfl) ⟨120908, by rfl⟩ : syracuseStep 2579381 = 241817) (by norm_num)
theorem B7347125 : Blo 1719060 7347125 := bbase (se 5 (by rfl) ⟨344396, by rfl⟩ : syracuseStep 7347125 = 688793) (by norm_num)
theorem B8707013 : Blo 1719060 8707013 := bbase (se 4 (by rfl) ⟨816282, by rfl⟩ : syracuseStep 8707013 = 1632565) (by norm_num)
theorem B2579405 : Blo 1719060 2579405 := bbase (se 3 (by rfl) ⟨483638, by rfl⟩ : syracuseStep 2579405 = 967277) (by norm_num)
theorem B2579429 : Blo 1719060 2579429 := bbase (se 4 (by rfl) ⟨241821, by rfl⟩ : syracuseStep 2579429 = 483643) (by norm_num)
theorem B2178029 : Blo 1719060 2178029 := bbase (se 3 (by rfl) ⟨408380, by rfl⟩ : syracuseStep 2178029 = 816761) (by norm_num)
theorem B2579453 : Blo 1719060 2579453 := bbase (se 3 (by rfl) ⟨483647, by rfl⟩ : syracuseStep 2579453 = 967295) (by norm_num)
theorem B2579477 : Blo 1719060 2579477 := bbase (se 6 (by rfl) ⟨60456, by rfl⟩ : syracuseStep 2579477 = 120913) (by norm_num)
theorem B2178085 : Blo 1719060 2178085 := bbase (se 4 (by rfl) ⟨204195, by rfl⟩ : syracuseStep 2178085 = 408391) (by norm_num)
theorem B2481197 : Blo 1719060 2481197 := bbase (se 3 (by rfl) ⟨465224, by rfl⟩ : syracuseStep 2481197 = 930449) (by norm_num)
theorem B2579501 : Blo 1719060 2579501 := bbase (se 3 (by rfl) ⟨483656, by rfl⟩ : syracuseStep 2579501 = 967313) (by norm_num)
theorem B2579525 : Blo 1719060 2579525 := bbase (se 4 (by rfl) ⟨241830, by rfl⟩ : syracuseStep 2579525 = 483661) (by norm_num)
theorem B2579549 : Blo 1719060 2579549 := bbase (se 3 (by rfl) ⟨483665, by rfl⟩ : syracuseStep 2579549 = 967331) (by norm_num)
theorem B2325613 : Blo 1719060 2325613 := bbase (se 3 (by rfl) ⟨436052, by rfl⟩ : syracuseStep 2325613 = 872105) (by norm_num)
theorem B2579573 : Blo 1719060 2579573 := bbase (se 5 (by rfl) ⟨120917, by rfl⟩ : syracuseStep 2579573 = 241835) (by norm_num)
theorem B2178181 : Blo 1719060 2178181 := bbase (se 4 (by rfl) ⟨204204, by rfl⟩ : syracuseStep 2178181 = 408409) (by norm_num)
theorem B2579597 : Blo 1719060 2579597 := bbase (se 3 (by rfl) ⟨483674, by rfl⟩ : syracuseStep 2579597 = 967349) (by norm_num)
theorem B11025557 : Blo 1719060 11025557 := bbase (se 6 (by rfl) ⟨258411, by rfl⟩ : syracuseStep 11025557 = 516823) (by norm_num)
theorem B2579621 : Blo 1719060 2579621 := bbase (se 4 (by rfl) ⟨241839, by rfl⟩ : syracuseStep 2579621 = 483679) (by norm_num)
theorem B5881013 : Blo 1719060 5881013 := bbase (se 5 (by rfl) ⟨275672, by rfl⟩ : syracuseStep 5881013 = 551345) (by norm_num)
theorem B2579645 : Blo 1719060 2579645 := bbase (se 3 (by rfl) ⟨483683, by rfl⟩ : syracuseStep 2579645 = 967367) (by norm_num)
theorem B2579669 : Blo 1719060 2579669 := bbase (se 7 (by rfl) ⟨30230, by rfl⟩ : syracuseStep 2579669 = 60461) (by norm_num)
theorem B2579693 : Blo 1719060 2579693 := bbase (se 3 (by rfl) ⟨483692, by rfl⟩ : syracuseStep 2579693 = 967385) (by norm_num)
theorem B12401909 : Blo 1719060 12401909 := bbase (se 5 (by rfl) ⟨581339, by rfl⟩ : syracuseStep 12401909 = 1162679) (by norm_num)
theorem B2579717 : Blo 1719060 2579717 := bbase (se 4 (by rfl) ⟨241848, by rfl⟩ : syracuseStep 2579717 = 483697) (by norm_num)
theorem B2579741 : Blo 1719060 2579741 := bbase (se 3 (by rfl) ⟨483701, by rfl⟩ : syracuseStep 2579741 = 967403) (by norm_num)
theorem B2448677 : Blo 1719060 2448677 := bbase (se 4 (by rfl) ⟨229563, by rfl⟩ : syracuseStep 2448677 = 459127) (by norm_num)
theorem B2579765 : Blo 1719060 2579765 := bbase (se 5 (by rfl) ⟨120926, by rfl⟩ : syracuseStep 2579765 = 241853) (by norm_num)
theorem B5807429 : Blo 1719060 5807429 := bbase (se 4 (by rfl) ⟨544446, by rfl⟩ : syracuseStep 5807429 = 1088893) (by norm_num)
theorem B2579789 : Blo 1719060 2579789 := bbase (se 3 (by rfl) ⟨483710, by rfl⟩ : syracuseStep 2579789 = 967421) (by norm_num)
theorem B2579813 : Blo 1719060 2579813 := bbase (se 4 (by rfl) ⟨241857, by rfl⟩ : syracuseStep 2579813 = 483715) (by norm_num)
theorem B2579837 : Blo 1719060 2579837 := bbase (se 3 (by rfl) ⟨483719, by rfl⟩ : syracuseStep 2579837 = 967439) (by norm_num)
theorem B2579861 : Blo 1719060 2579861 := bbase (se 6 (by rfl) ⟨60465, by rfl⟩ : syracuseStep 2579861 = 120931) (by norm_num)
theorem B2579885 : Blo 1719060 2579885 := bbase (se 3 (by rfl) ⟨483728, by rfl⟩ : syracuseStep 2579885 = 967457) (by norm_num)
theorem B2579909 : Blo 1719060 2579909 := bbase (se 4 (by rfl) ⟨241866, by rfl⟩ : syracuseStep 2579909 = 483733) (by norm_num)
theorem B2579933 : Blo 1719060 2579933 := bbase (se 3 (by rfl) ⟨483737, by rfl⟩ : syracuseStep 2579933 = 967475) (by norm_num)
theorem B2579957 : Blo 1719060 2579957 := bbase (se 5 (by rfl) ⟨120935, by rfl⟩ : syracuseStep 2579957 = 241871) (by norm_num)
theorem B2579981 : Blo 1719060 2579981 := bbase (se 3 (by rfl) ⟨483746, by rfl⟩ : syracuseStep 2579981 = 967493) (by norm_num)
theorem B2580005 : Blo 1719060 2580005 := bbase (se 4 (by rfl) ⟨241875, by rfl⟩ : syracuseStep 2580005 = 483751) (by norm_num)
theorem B4898357 : Blo 1719060 4898357 := bbase (se 5 (by rfl) ⟨229610, by rfl⟩ : syracuseStep 4898357 = 459221) (by norm_num)
theorem B2580029 : Blo 1719060 2580029 := bbase (se 3 (by rfl) ⟨483755, by rfl⟩ : syracuseStep 2580029 = 967511) (by norm_num)
theorem B2580053 : Blo 1719060 2580053 := bbase (se 8 (by rfl) ⟨15117, by rfl⟩ : syracuseStep 2580053 = 30235) (by norm_num)
theorem B5512805 : Blo 1719060 5512805 := bbase (se 4 (by rfl) ⟨516825, by rfl⟩ : syracuseStep 5512805 = 1033651) (by norm_num)
theorem B2580077 : Blo 1719060 2580077 := bbase (se 3 (by rfl) ⟨483764, by rfl⟩ : syracuseStep 2580077 = 967529) (by norm_num)
theorem B2580101 : Blo 1719060 2580101 := bbase (se 4 (by rfl) ⟨241884, by rfl⟩ : syracuseStep 2580101 = 483769) (by norm_num)
theorem B2580125 : Blo 1719060 2580125 := bbase (se 3 (by rfl) ⟨483773, by rfl⟩ : syracuseStep 2580125 = 967547) (by norm_num)
theorem B2580149 : Blo 1719060 2580149 := bbase (se 5 (by rfl) ⟨120944, by rfl⟩ : syracuseStep 2580149 = 241889) (by norm_num)
theorem B2580173 : Blo 1719060 2580173 := bbase (se 3 (by rfl) ⟨483782, by rfl⟩ : syracuseStep 2580173 = 967565) (by norm_num)
theorem B2580197 : Blo 1719060 2580197 := bbase (se 4 (by rfl) ⟨241893, by rfl⟩ : syracuseStep 2580197 = 483787) (by norm_num)
theorem B5807861 : Blo 1719060 5807861 := bbase (se 5 (by rfl) ⟨272243, by rfl⟩ : syracuseStep 5807861 = 544487) (by norm_num)
theorem B2580221 : Blo 1719060 2580221 := bbase (se 3 (by rfl) ⟨483791, by rfl⟩ : syracuseStep 2580221 = 967583) (by norm_num)
theorem B2580245 : Blo 1719060 2580245 := bbase (se 6 (by rfl) ⟨60474, by rfl⟩ : syracuseStep 2580245 = 120949) (by norm_num)
theorem B2580269 : Blo 1719060 2580269 := bbase (se 3 (by rfl) ⟨483800, by rfl⟩ : syracuseStep 2580269 = 967601) (by norm_num)
theorem B2793269 : Blo 1719060 2793269 := bbase (se 5 (by rfl) ⟨130934, by rfl⟩ : syracuseStep 2793269 = 261869) (by norm_num)
theorem B4415285 : Blo 1719060 4415285 := bbase (se 5 (by rfl) ⟨206966, by rfl⟩ : syracuseStep 4415285 = 413933) (by norm_num)
theorem B2580293 : Blo 1719060 2580293 := bbase (se 4 (by rfl) ⟨241902, by rfl⟩ : syracuseStep 2580293 = 483805) (by norm_num)
theorem B2580317 : Blo 1719060 2580317 := bbase (se 3 (by rfl) ⟨483809, by rfl⟩ : syracuseStep 2580317 = 967619) (by norm_num)
theorem B2580341 : Blo 1719060 2580341 := bbase (se 5 (by rfl) ⟨120953, by rfl⟩ : syracuseStep 2580341 = 241907) (by norm_num)
theorem B2580365 : Blo 1719060 2580365 := bbase (se 3 (by rfl) ⟨483818, by rfl⟩ : syracuseStep 2580365 = 967637) (by norm_num)
theorem B2580389 : Blo 1719060 2580389 := bbase (se 4 (by rfl) ⟨241911, by rfl⟩ : syracuseStep 2580389 = 483823) (by norm_num)
theorem B2580413 : Blo 1719060 2580413 := bbase (se 3 (by rfl) ⟨483827, by rfl⟩ : syracuseStep 2580413 = 967655) (by norm_num)
theorem B2580437 : Blo 1719060 2580437 := bbase (se 7 (by rfl) ⟨30239, by rfl⟩ : syracuseStep 2580437 = 60479) (by norm_num)
theorem B18603989 : Blo 1719060 18603989 := bbase (se 7 (by rfl) ⟨218015, by rfl⟩ : syracuseStep 18603989 = 436031) (by norm_num)
theorem B4898789 : Blo 1719060 4898789 := bbase (se 4 (by rfl) ⟨459261, by rfl⟩ : syracuseStep 4898789 = 918523) (by norm_num)
theorem B2580461 : Blo 1719060 2580461 := bbase (se 3 (by rfl) ⟨483836, by rfl⟩ : syracuseStep 2580461 = 967673) (by norm_num)
theorem B1720323 : Blo 1719060 1720323 := bstep (se 1 (by rfl) ⟨1290242, by rfl⟩ : syracuseStep 1720323 = 2580485) B2580485
theorem B5808131 : Blo 1719060 5808131 := bstep (se 1 (by rfl) ⟨4356098, by rfl⟩ : syracuseStep 5808131 = 8712197) B8712197
theorem B2580497 : Blo 1719060 2580497 := bstep (se 2 (by rfl) ⟨967686, by rfl⟩ : syracuseStep 2580497 = 1935373) B1935373
theorem B1720339 : Blo 1719060 1720339 := bstep (se 1 (by rfl) ⟨1290254, by rfl⟩ : syracuseStep 1720339 = 2580509) B2580509
theorem B5881891 : Blo 1719060 5881891 := bstep (se 1 (by rfl) ⟨4411418, by rfl⟩ : syracuseStep 5881891 = 8822837) B8822837
theorem B2580515 : Blo 1719060 2580515 := bstep (se 1 (by rfl) ⟨1935386, by rfl⟩ : syracuseStep 2580515 = 3870773) B3870773
theorem B1720355 : Blo 1719060 1720355 := bstep (se 1 (by rfl) ⟨1290266, by rfl⟩ : syracuseStep 1720355 = 2580533) B2580533
theorem B1720371 : Blo 1719060 1720371 := bstep (se 1 (by rfl) ⟨1290278, by rfl⟩ : syracuseStep 1720371 = 2580557) B2580557
theorem B2580545 : Blo 1719060 2580545 := bstep (se 2 (by rfl) ⟨967704, by rfl⟩ : syracuseStep 2580545 = 1935409) B1935409
theorem B1720387 : Blo 1719060 1720387 := bstep (se 1 (by rfl) ⟨1290290, by rfl⟩ : syracuseStep 1720387 = 2580581) B2580581
theorem B2580563 : Blo 1719060 2580563 := bstep (se 1 (by rfl) ⟨1935422, by rfl⟩ : syracuseStep 2580563 = 3870845) B3870845
theorem B1720403 : Blo 1719060 1720403 := bstep (se 1 (by rfl) ⟨1290302, by rfl⟩ : syracuseStep 1720403 = 2580605) B2580605
theorem B1720419 : Blo 1719060 1720419 := bstep (se 1 (by rfl) ⟨1290314, by rfl⟩ : syracuseStep 1720419 = 2580629) B2580629
theorem B2580593 : Blo 1719060 2580593 := bstep (se 2 (by rfl) ⟨967722, by rfl⟩ : syracuseStep 2580593 = 1935445) B1935445
theorem B1720435 : Blo 1719060 1720435 := bstep (se 1 (by rfl) ⟨1290326, by rfl⟩ : syracuseStep 1720435 = 2580653) B2580653
theorem B2580611 : Blo 1719060 2580611 := bstep (se 1 (by rfl) ⟨1935458, by rfl⟩ : syracuseStep 2580611 = 3870917) B3870917
theorem B1720451 : Blo 1719060 1720451 := bstep (se 1 (by rfl) ⟨1290338, by rfl⟩ : syracuseStep 1720451 = 2580677) B2580677
theorem B1720467 : Blo 1719060 1720467 := bstep (se 1 (by rfl) ⟨1290350, by rfl⟩ : syracuseStep 1720467 = 2580701) B2580701
theorem B2580641 : Blo 1719060 2580641 := bstep (se 2 (by rfl) ⟨967740, by rfl⟩ : syracuseStep 2580641 = 1935481) B1935481
theorem B1720483 : Blo 1719060 1720483 := bstep (se 1 (by rfl) ⟨1290362, by rfl⟩ : syracuseStep 1720483 = 2580725) B2580725
theorem B10461361 : Blo 1719060 10461361 := bstep (se 2 (by rfl) ⟨3923010, by rfl⟩ : syracuseStep 10461361 = 7846021) B7846021
theorem B5513393 : Blo 1719060 5513393 := bstep (se 2 (by rfl) ⟨2067522, by rfl⟩ : syracuseStep 5513393 = 4135045) B4135045
theorem B2580659 : Blo 1719060 2580659 := bstep (se 1 (by rfl) ⟨1935494, by rfl⟩ : syracuseStep 2580659 = 3870989) B3870989
theorem B1720499 : Blo 1719060 1720499 := bstep (se 1 (by rfl) ⟨1290374, by rfl⟩ : syracuseStep 1720499 = 2580749) B2580749
theorem B1720515 : Blo 1719060 1720515 := bstep (se 1 (by rfl) ⟨1290386, by rfl⟩ : syracuseStep 1720515 = 2580773) B2580773
theorem B2580689 : Blo 1719060 2580689 := bstep (se 2 (by rfl) ⟨967758, by rfl⟩ : syracuseStep 2580689 = 1935517) B1935517
theorem B1720531 : Blo 1719060 1720531 := bstep (se 1 (by rfl) ⟨1290398, by rfl⟩ : syracuseStep 1720531 = 2580797) B2580797
theorem B2580707 : Blo 1719060 2580707 := bstep (se 1 (by rfl) ⟨1935530, by rfl⟩ : syracuseStep 2580707 = 3871061) B3871061
theorem B1720547 : Blo 1719060 1720547 := bstep (se 1 (by rfl) ⟨1290410, by rfl⟩ : syracuseStep 1720547 = 2580821) B2580821
theorem B1720563 : Blo 1719060 1720563 := bstep (se 1 (by rfl) ⟨1290422, by rfl⟩ : syracuseStep 1720563 = 2580845) B2580845
theorem B2580737 : Blo 1719060 2580737 := bstep (se 2 (by rfl) ⟨967776, by rfl⟩ : syracuseStep 2580737 = 1935553) B1935553
theorem B1720579 : Blo 1719060 1720579 := bstep (se 1 (by rfl) ⟨1290434, by rfl⟩ : syracuseStep 1720579 = 2580869) B2580869
theorem B5808401 : Blo 1719060 5808401 := bstep (se 2 (by rfl) ⟨2178150, by rfl⟩ : syracuseStep 5808401 = 4356301) B4356301
theorem B2580755 : Blo 1719060 2580755 := bstep (se 1 (by rfl) ⟨1935566, by rfl⟩ : syracuseStep 2580755 = 3871133) B3871133
theorem B1720595 : Blo 1719060 1720595 := bstep (se 1 (by rfl) ⟨1290446, by rfl⟩ : syracuseStep 1720595 = 2580893) B2580893
theorem B1720611 : Blo 1719060 1720611 := bstep (se 1 (by rfl) ⟨1290458, by rfl⟩ : syracuseStep 1720611 = 2580917) B2580917
theorem B2580785 : Blo 1719060 2580785 := bstep (se 2 (by rfl) ⟨967794, by rfl⟩ : syracuseStep 2580785 = 1935589) B1935589
theorem B1720627 : Blo 1719060 1720627 := bstep (se 1 (by rfl) ⟨1290470, by rfl⟩ : syracuseStep 1720627 = 2580941) B2580941
theorem B2580803 : Blo 1719060 2580803 := bstep (se 1 (by rfl) ⟨1935602, by rfl⟩ : syracuseStep 2580803 = 3871205) B3871205
theorem B1720643 : Blo 1719060 1720643 := bstep (se 1 (by rfl) ⟨1290482, by rfl⟩ : syracuseStep 1720643 = 2580965) B2580965
theorem B1720659 : Blo 1719060 1720659 := bstep (se 1 (by rfl) ⟨1290494, by rfl⟩ : syracuseStep 1720659 = 2580989) B2580989
theorem B2580833 : Blo 1719060 2580833 := bstep (se 2 (by rfl) ⟨967812, by rfl⟩ : syracuseStep 2580833 = 1935625) B1935625
theorem B1720675 : Blo 1719060 1720675 := bstep (se 1 (by rfl) ⟨1290506, by rfl⟩ : syracuseStep 1720675 = 2581013) B2581013
theorem B13066595 : Blo 1719060 13066595 := bstep (se 1 (by rfl) ⟨9799946, by rfl⟩ : syracuseStep 13066595 = 19599893) B19599893
theorem B2580851 : Blo 1719060 2580851 := bstep (se 1 (by rfl) ⟨1935638, by rfl⟩ : syracuseStep 2580851 = 3871277) B3871277
theorem B1720691 : Blo 1719060 1720691 := bstep (se 1 (by rfl) ⟨1290518, by rfl⟩ : syracuseStep 1720691 = 2581037) B2581037
theorem B1720707 : Blo 1719060 1720707 := bstep (se 1 (by rfl) ⟨1290530, by rfl⟩ : syracuseStep 1720707 = 2581061) B2581061
theorem B2580881 : Blo 1719060 2580881 := bstep (se 2 (by rfl) ⟨967830, by rfl⟩ : syracuseStep 2580881 = 1935661) B1935661
theorem B1720723 : Blo 1719060 1720723 := bstep (se 1 (by rfl) ⟨1290542, by rfl⟩ : syracuseStep 1720723 = 2581085) B2581085
theorem B2580899 : Blo 1719060 2580899 := bstep (se 1 (by rfl) ⟨1935674, by rfl⟩ : syracuseStep 2580899 = 3871349) B3871349
theorem B1720739 : Blo 1719060 1720739 := bstep (se 1 (by rfl) ⟨1290554, by rfl⟩ : syracuseStep 1720739 = 2581109) B2581109
theorem B1720755 : Blo 1719060 1720755 := bstep (se 1 (by rfl) ⟨1290566, by rfl⟩ : syracuseStep 1720755 = 2581133) B2581133
theorem B2580929 : Blo 1719060 2580929 := bstep (se 2 (by rfl) ⟨967848, by rfl⟩ : syracuseStep 2580929 = 1935697) B1935697
theorem B1720771 : Blo 1719060 1720771 := bstep (se 1 (by rfl) ⟨1290578, by rfl⟩ : syracuseStep 1720771 = 2581157) B2581157
theorem B2449873 : Blo 1719060 2449873 := bstep (se 2 (by rfl) ⟨918702, by rfl⟩ : syracuseStep 2449873 = 1837405) B1837405
theorem B2580947 : Blo 1719060 2580947 := bstep (se 1 (by rfl) ⟨1935710, by rfl⟩ : syracuseStep 2580947 = 3871421) B3871421
theorem B1720787 : Blo 1719060 1720787 := bstep (se 1 (by rfl) ⟨1290590, by rfl⟩ : syracuseStep 1720787 = 2581181) B2581181
theorem B5882339 : Blo 1719060 5882339 := bstep (se 1 (by rfl) ⟨4411754, by rfl⟩ : syracuseStep 5882339 = 8823509) B8823509
theorem B1720803 : Blo 1719060 1720803 := bstep (se 1 (by rfl) ⟨1290602, by rfl⟩ : syracuseStep 1720803 = 2581205) B2581205
theorem B2580977 : Blo 1719060 2580977 := bstep (se 2 (by rfl) ⟨967866, by rfl⟩ : syracuseStep 2580977 = 1935733) B1935733
theorem B16540145 : Blo 1719060 16540145 := bstep (se 2 (by rfl) ⟨6202554, by rfl⟩ : syracuseStep 16540145 = 12405109) B12405109
theorem B1720819 : Blo 1719060 1720819 := bstep (se 1 (by rfl) ⟨1290614, by rfl⟩ : syracuseStep 1720819 = 2581229) B2581229
theorem B2580995 : Blo 1719060 2580995 := bstep (se 1 (by rfl) ⟨1935746, by rfl⟩ : syracuseStep 2580995 = 3871493) B3871493
theorem B1720835 : Blo 1719060 1720835 := bstep (se 1 (by rfl) ⟨1290626, by rfl⟩ : syracuseStep 1720835 = 2581253) B2581253
theorem B1720851 : Blo 1719060 1720851 := bstep (se 1 (by rfl) ⟨1290638, by rfl⟩ : syracuseStep 1720851 = 2581277) B2581277
theorem B2581025 : Blo 1719060 2581025 := bstep (se 2 (by rfl) ⟨967884, by rfl⟩ : syracuseStep 2581025 = 1935769) B1935769
theorem B1720867 : Blo 1719060 1720867 := bstep (se 1 (by rfl) ⟨1290650, by rfl⟩ : syracuseStep 1720867 = 2581301) B2581301
theorem B2581043 : Blo 1719060 2581043 := bstep (se 1 (by rfl) ⟨1935782, by rfl⟩ : syracuseStep 2581043 = 3871565) B3871565
theorem B1720883 : Blo 1719060 1720883 := bstep (se 1 (by rfl) ⟨1290662, by rfl⟩ : syracuseStep 1720883 = 2581325) B2581325
theorem B1720899 : Blo 1719060 1720899 := bstep (se 1 (by rfl) ⟨1290674, by rfl⟩ : syracuseStep 1720899 = 2581349) B2581349
theorem B2581073 : Blo 1719060 2581073 := bstep (se 2 (by rfl) ⟨967902, by rfl⟩ : syracuseStep 2581073 = 1935805) B1935805
theorem B1720915 : Blo 1719060 1720915 := bstep (se 1 (by rfl) ⟨1290686, by rfl⟩ : syracuseStep 1720915 = 2581373) B2581373
theorem B2581091 : Blo 1719060 2581091 := bstep (se 1 (by rfl) ⟨1935818, by rfl⟩ : syracuseStep 2581091 = 3871637) B3871637
theorem B1720931 : Blo 1719060 1720931 := bstep (se 1 (by rfl) ⟨1290698, by rfl⟩ : syracuseStep 1720931 = 2581397) B2581397
theorem B7070321 : Blo 1719060 7070321 := bstep (se 2 (by rfl) ⟨2651370, by rfl⟩ : syracuseStep 7070321 = 5302741) B5302741
theorem B13951601 : Blo 1719060 13951601 := bstep (se 2 (by rfl) ⟨5231850, by rfl⟩ : syracuseStep 13951601 = 10463701) B10463701
theorem B1720947 : Blo 1719060 1720947 := bstep (se 1 (by rfl) ⟨1290710, by rfl⟩ : syracuseStep 1720947 = 2581421) B2581421
theorem B2581121 : Blo 1719060 2581121 := bstep (se 2 (by rfl) ⟨967920, by rfl⟩ : syracuseStep 2581121 = 1935841) B1935841
theorem B1720963 : Blo 1719060 1720963 := bstep (se 1 (by rfl) ⟨1290722, by rfl⟩ : syracuseStep 1720963 = 2581445) B2581445
theorem B4899473 : Blo 1719060 4899473 := bstep (se 2 (by rfl) ⟨1837302, by rfl⟩ : syracuseStep 4899473 = 3674605) B3674605
theorem B2581139 : Blo 1719060 2581139 := bstep (se 1 (by rfl) ⟨1935854, by rfl⟩ : syracuseStep 2581139 = 3871709) B3871709
theorem B1720979 : Blo 1719060 1720979 := bstep (se 1 (by rfl) ⟨1290734, by rfl⟩ : syracuseStep 1720979 = 2581469) B2581469
theorem B1933987 : Blo 1719060 1933987 := bstep (se 1 (by rfl) ⟨1450490, by rfl⟩ : syracuseStep 1933987 = 2900981) B2900981
theorem B1720995 : Blo 1719060 1720995 := bstep (se 1 (by rfl) ⟨1290746, by rfl⟩ : syracuseStep 1720995 = 2581493) B2581493
theorem B2581169 : Blo 1719060 2581169 := bstep (se 2 (by rfl) ⟨967938, by rfl⟩ : syracuseStep 2581169 = 1935877) B1935877
theorem B1721011 : Blo 1719060 1721011 := bstep (se 1 (by rfl) ⟨1290758, by rfl⟩ : syracuseStep 1721011 = 2581517) B2581517
theorem B2581187 : Blo 1719060 2581187 := bstep (se 1 (by rfl) ⟨1935890, by rfl⟩ : syracuseStep 2581187 = 3871781) B3871781
theorem B1721027 : Blo 1719060 1721027 := bstep (se 1 (by rfl) ⟨1290770, by rfl⟩ : syracuseStep 1721027 = 2581541) B2581541
theorem B1721043 : Blo 1719060 1721043 := bstep (se 1 (by rfl) ⟨1290782, by rfl⟩ : syracuseStep 1721043 = 2581565) B2581565
theorem B2581217 : Blo 1719060 2581217 := bstep (se 2 (by rfl) ⟨967956, by rfl⟩ : syracuseStep 2581217 = 1935913) B1935913
theorem B1721059 : Blo 1719060 1721059 := bstep (se 1 (by rfl) ⟨1290794, by rfl⟩ : syracuseStep 1721059 = 2581589) B2581589
theorem B2581235 : Blo 1719060 2581235 := bstep (se 1 (by rfl) ⟨1935926, by rfl⟩ : syracuseStep 2581235 = 3871853) B3871853
theorem B6529805 : Blo 1719060 6529805 := bstep (se 3 (by rfl) ⟨1224338, by rfl⟩ : syracuseStep 6529805 = 2448677) B2448677
theorem B2581265 : Blo 1719060 2581265 := bstep (se 2 (by rfl) ⟨967974, by rfl⟩ : syracuseStep 2581265 = 1935949) B1935949
theorem B2581283 : Blo 1719060 2581283 := bstep (se 1 (by rfl) ⟨1935962, by rfl⟩ : syracuseStep 2581283 = 3871925) B3871925
theorem B5882669 : Blo 1719060 5882669 := bstep (se 3 (by rfl) ⟨1103000, by rfl⟩ : syracuseStep 5882669 = 2206001) B2206001
theorem B1934131 : Blo 1719060 1934131 := bstep (se 1 (by rfl) ⟨1450598, by rfl⟩ : syracuseStep 1934131 = 2901197) B2901197
theorem B2581313 : Blo 1719060 2581313 := bstep (se 2 (by rfl) ⟨967992, by rfl⟩ : syracuseStep 2581313 = 1935985) B1935985
theorem B2581331 : Blo 1719060 2581331 := bstep (se 1 (by rfl) ⟨1935998, by rfl⟩ : syracuseStep 2581331 = 3871997) B3871997
theorem B2581361 : Blo 1719060 2581361 := bstep (se 2 (by rfl) ⟨968010, by rfl⟩ : syracuseStep 2581361 = 1936021) B1936021
theorem B2581379 : Blo 1719060 2581379 := bstep (se 1 (by rfl) ⟨1936034, by rfl⟩ : syracuseStep 2581379 = 3872069) B3872069
theorem B2581409 : Blo 1719060 2581409 := bstep (se 2 (by rfl) ⟨968028, by rfl⟩ : syracuseStep 2581409 = 1936057) B1936057
theorem B2581427 : Blo 1719060 2581427 := bstep (se 1 (by rfl) ⟨1936070, by rfl⟩ : syracuseStep 2581427 = 3872141) B3872141
theorem B1934275 : Blo 1719060 1934275 := bstep (se 1 (by rfl) ⟨1450706, by rfl⟩ : syracuseStep 1934275 = 2901413) B2901413
theorem B19104709 : Blo 1719060 19104709 := bstep (se 4 (by rfl) ⟨1791066, by rfl⟩ : syracuseStep 19104709 = 3582133) B3582133
theorem B2581457 : Blo 1719060 2581457 := bstep (se 2 (by rfl) ⟨968046, by rfl⟩ : syracuseStep 2581457 = 1936093) B1936093
theorem B2900947 : Blo 1719060 2900947 := bstep (se 1 (by rfl) ⟨2175710, by rfl⟩ : syracuseStep 2900947 = 4351421) B4351421
theorem B2581475 : Blo 1719060 2581475 := bstep (se 1 (by rfl) ⟨1936106, by rfl⟩ : syracuseStep 2581475 = 3872213) B3872213
theorem B7955441 : Blo 1719060 7955441 := bstep (se 2 (by rfl) ⟨2983290, by rfl⟩ : syracuseStep 7955441 = 5966581) B5966581
theorem B2581505 : Blo 1719060 2581505 := bstep (se 2 (by rfl) ⟨968064, by rfl⟩ : syracuseStep 2581505 = 1936129) B1936129
theorem B2581523 : Blo 1719060 2581523 := bstep (se 1 (by rfl) ⟨1936142, by rfl⟩ : syracuseStep 2581523 = 3872285) B3872285
theorem B2581553 : Blo 1719060 2581553 := bstep (se 2 (by rfl) ⟨968082, by rfl⟩ : syracuseStep 2581553 = 1936165) B1936165
theorem B2581571 : Blo 1719060 2581571 := bstep (se 1 (by rfl) ⟨1936178, by rfl⟩ : syracuseStep 2581571 = 3872357) B3872357
theorem B1934419 : Blo 1719060 1934419 := bstep (se 1 (by rfl) ⟨1450814, by rfl⟩ : syracuseStep 1934419 = 2901629) B2901629
theorem B2901089 : Blo 1719060 2901089 := bstep (se 2 (by rfl) ⟨1087908, by rfl⟩ : syracuseStep 2901089 = 2175817) B2175817
theorem B5883025 : Blo 1719060 5883025 := bstep (se 2 (by rfl) ⟨2206134, by rfl⟩ : syracuseStep 5883025 = 4412269) B4412269
theorem B2942129 : Blo 1719060 2942129 := bstep (se 2 (by rfl) ⟨1103298, by rfl⟩ : syracuseStep 2942129 = 2206597) B2206597
theorem B9798853 : Blo 1719060 9798853 := bstep (se 4 (by rfl) ⟨918642, by rfl⟩ : syracuseStep 9798853 = 1837285) B1837285
theorem B2901217 : Blo 1719060 2901217 := bstep (se 2 (by rfl) ⟨1087956, by rfl⟩ : syracuseStep 2901217 = 2175913) B2175913
theorem B1934563 : Blo 1719060 1934563 := bstep (se 1 (by rfl) ⟨1450922, by rfl⟩ : syracuseStep 1934563 = 2901845) B2901845
theorem B2901251 : Blo 1719060 2901251 := bstep (se 1 (by rfl) ⟨2175938, by rfl⟩ : syracuseStep 2901251 = 4351877) B4351877
theorem B1934707 : Blo 1719060 1934707 := bstep (se 1 (by rfl) ⟨1451030, by rfl⟩ : syracuseStep 1934707 = 2902061) B2902061
theorem B2901379 : Blo 1719060 2901379 := bstep (se 1 (by rfl) ⟨2176034, by rfl⟩ : syracuseStep 2901379 = 4352069) B4352069
theorem B4351441 : Blo 1719060 4351441 := bstep (se 2 (by rfl) ⟨1631790, by rfl⟩ : syracuseStep 4351441 = 3263581) B3263581
theorem B3868145 : Blo 1719060 3868145 := bstep (se 2 (by rfl) ⟨1450554, by rfl⟩ : syracuseStep 3868145 = 2901109) B2901109
theorem B3868163 : Blo 1719060 3868163 := bstep (se 1 (by rfl) ⟨2901122, by rfl⟩ : syracuseStep 3868163 = 5802245) B5802245
theorem B1934851 : Blo 1719060 1934851 := bstep (se 1 (by rfl) ⟨1451138, by rfl⟩ : syracuseStep 1934851 = 2902277) B2902277
theorem B2901521 : Blo 1719060 2901521 := bstep (se 2 (by rfl) ⟨1088070, by rfl⟩ : syracuseStep 2901521 = 2176141) B2176141
theorem B2754083 : Blo 1719060 2754083 := bstep (se 1 (by rfl) ⟨2065562, by rfl⟩ : syracuseStep 2754083 = 4131125) B4131125
theorem B22029893 : Blo 1719060 22029893 := bstep (se 4 (by rfl) ⟨2065302, by rfl⟩ : syracuseStep 22029893 = 4130605) B4130605
theorem B4900429 : Blo 1719060 4900429 := bstep (se 3 (by rfl) ⟨918830, by rfl⟩ : syracuseStep 4900429 = 1837661) B1837661
theorem B33056369 : Blo 1719060 33056369 := bstep (se 2 (by rfl) ⟨12396138, by rfl⟩ : syracuseStep 33056369 = 24792277) B24792277
theorem B2901649 : Blo 1719060 2901649 := bstep (se 2 (by rfl) ⟨1088118, by rfl⟩ : syracuseStep 2901649 = 2176237) B2176237
theorem B1934995 : Blo 1719060 1934995 := bstep (se 1 (by rfl) ⟨1451246, by rfl⟩ : syracuseStep 1934995 = 2902493) B2902493
theorem B2901683 : Blo 1719060 2901683 := bstep (se 1 (by rfl) ⟨2176262, by rfl⟩ : syracuseStep 2901683 = 4352525) B4352525
theorem B4351715 : Blo 1719060 4351715 := bstep (se 1 (by rfl) ⟨3263786, by rfl⟩ : syracuseStep 4351715 = 6527573) B6527573
theorem B1836803 : Blo 1719060 1836803 := bstep (se 1 (by rfl) ⟨1377602, by rfl⟩ : syracuseStep 1836803 = 2755205) B2755205
theorem B3868433 : Blo 1719060 3868433 := bstep (se 2 (by rfl) ⟨1450662, by rfl⟩ : syracuseStep 3868433 = 2901325) B2901325
theorem B3868451 : Blo 1719060 3868451 := bstep (se 1 (by rfl) ⟨2901338, by rfl⟩ : syracuseStep 3868451 = 5802677) B5802677
theorem B6973219 : Blo 1719060 6973219 := bstep (se 1 (by rfl) ⟨5229914, by rfl⟩ : syracuseStep 6973219 = 10459829) B10459829
theorem B1935139 : Blo 1719060 1935139 := bstep (se 1 (by rfl) ⟨1451354, by rfl⟩ : syracuseStep 1935139 = 2902709) B2902709
theorem B4900657 : Blo 1719060 4900657 := bstep (se 2 (by rfl) ⟨1837746, by rfl⟩ : syracuseStep 4900657 = 3675493) B3675493
theorem B2901811 : Blo 1719060 2901811 := bstep (se 1 (by rfl) ⟨2176358, by rfl⟩ : syracuseStep 2901811 = 4352717) B4352717
theorem B4646737 : Blo 1719060 4646737 := bstep (se 2 (by rfl) ⟨1742526, by rfl⟩ : syracuseStep 4646737 = 3485053) B3485053
theorem B3671939 : Blo 1719060 3671939 := bstep (se 1 (by rfl) ⟨2753954, by rfl⟩ : syracuseStep 3671939 = 5507909) B5507909
theorem B4351907 : Blo 1719060 4351907 := bstep (se 1 (by rfl) ⟨3263930, by rfl⟩ : syracuseStep 4351907 = 6527861) B6527861
theorem B3098531 : Blo 1719060 3098531 := bstep (se 1 (by rfl) ⟨2323898, by rfl⟩ : syracuseStep 3098531 = 4647797) B4647797
theorem B1935283 : Blo 1719060 1935283 := bstep (se 1 (by rfl) ⟨1451462, by rfl⟩ : syracuseStep 1935283 = 2902925) B2902925
theorem B2901953 : Blo 1719060 2901953 := bstep (se 2 (by rfl) ⟨1088232, by rfl⟩ : syracuseStep 2901953 = 2176465) B2176465
theorem B4900817 : Blo 1719060 4900817 := bstep (se 2 (by rfl) ⟨1837806, by rfl⟩ : syracuseStep 4900817 = 3675613) B3675613
theorem B2615297 : Blo 1719060 2615297 := bstep (se 2 (by rfl) ⟨980736, by rfl⟩ : syracuseStep 2615297 = 1961473) B1961473
theorem B2754595 : Blo 1719060 2754595 := bstep (se 1 (by rfl) ⟨2065946, by rfl⟩ : syracuseStep 2754595 = 4131893) B4131893
theorem B5802029 : Blo 1719060 5802029 := bstep (se 3 (by rfl) ⟨1087880, by rfl⟩ : syracuseStep 5802029 = 2175761) B2175761
theorem B3868721 : Blo 1719060 3868721 := bstep (se 2 (by rfl) ⟨1450770, by rfl⟩ : syracuseStep 3868721 = 2901541) B2901541
theorem B2902081 : Blo 1719060 2902081 := bstep (se 2 (by rfl) ⟨1088280, by rfl⟩ : syracuseStep 2902081 = 2176561) B2176561
theorem B3868739 : Blo 1719060 3868739 := bstep (se 1 (by rfl) ⟨2901554, by rfl⟩ : syracuseStep 3868739 = 5803109) B5803109
theorem B1935427 : Blo 1719060 1935427 := bstep (se 1 (by rfl) ⟨1451570, by rfl⟩ : syracuseStep 1935427 = 2903141) B2903141
theorem B4900931 : Blo 1719060 4900931 := bstep (se 1 (by rfl) ⟨3675698, by rfl⟩ : syracuseStep 4900931 = 7351397) B7351397
theorem B2754641 : Blo 1719060 2754641 := bstep (se 2 (by rfl) ⟨1032990, by rfl⟩ : syracuseStep 2754641 = 2065981) B2065981
theorem B5802083 : Blo 1719060 5802083 := bstep (se 1 (by rfl) ⟨4351562, by rfl⟩ : syracuseStep 5802083 = 8703125) B8703125
theorem B2902115 : Blo 1719060 2902115 := bstep (se 1 (by rfl) ⟨2176586, by rfl⟩ : syracuseStep 2902115 = 4353173) B4353173
theorem B7350371 : Blo 1719060 7350371 := bstep (se 1 (by rfl) ⟨5512778, by rfl⟩ : syracuseStep 7350371 = 11025557) B11025557
theorem B7448717 : Blo 1719060 7448717 := bstep (se 3 (by rfl) ⟨1396634, by rfl⟩ : syracuseStep 7448717 = 2793269) B2793269
theorem B8267939 : Blo 1719060 8267939 := bstep (se 1 (by rfl) ⟨6200954, by rfl⟩ : syracuseStep 8267939 = 12401909) B12401909
theorem B1935571 : Blo 1719060 1935571 := bstep (se 1 (by rfl) ⟨1451678, by rfl⟩ : syracuseStep 1935571 = 2903357) B2903357
theorem B2902243 : Blo 1719060 2902243 := bstep (se 1 (by rfl) ⟨2176682, by rfl⟩ : syracuseStep 2902243 = 4353365) B4353365
theorem B5507345 : Blo 1719060 5507345 := bstep (se 2 (by rfl) ⟨2065254, by rfl⟩ : syracuseStep 5507345 = 4130509) B4130509
theorem B23529797 : Blo 1719060 23529797 := bstep (se 4 (by rfl) ⟨2205918, by rfl⟩ : syracuseStep 23529797 = 4411837) B4411837
theorem B3869009 : Blo 1719060 3869009 := bstep (se 2 (by rfl) ⟨1450878, by rfl⟩ : syracuseStep 3869009 = 2901757) B2901757
theorem B3869027 : Blo 1719060 3869027 := bstep (se 1 (by rfl) ⟨2901770, by rfl⟩ : syracuseStep 3869027 = 5803541) B5803541
theorem B1935715 : Blo 1719060 1935715 := bstep (se 1 (by rfl) ⟨1451786, by rfl⟩ : syracuseStep 1935715 = 2903573) B2903573
theorem B5802353 : Blo 1719060 5802353 := bstep (se 2 (by rfl) ⟨2175882, by rfl⟩ : syracuseStep 5802353 = 4351765) B4351765
theorem B2902385 : Blo 1719060 2902385 := bstep (se 2 (by rfl) ⟨1088394, by rfl⟩ : syracuseStep 2902385 = 2176789) B2176789
theorem B8710577 : Blo 1719060 8710577 := bstep (se 2 (by rfl) ⟨3266466, by rfl⟩ : syracuseStep 8710577 = 6532933) B6532933
theorem B2902513 : Blo 1719060 2902513 := bstep (se 2 (by rfl) ⟨1088442, by rfl⟩ : syracuseStep 2902513 = 2176885) B2176885
theorem B1935859 : Blo 1719060 1935859 := bstep (se 1 (by rfl) ⟨1451894, by rfl⟩ : syracuseStep 1935859 = 2903789) B2903789
theorem B2902547 : Blo 1719060 2902547 := bstep (se 1 (by rfl) ⟨2176910, by rfl⟩ : syracuseStep 2902547 = 4353821) B4353821
theorem B2943523 : Blo 1719060 2943523 := bstep (se 1 (by rfl) ⟨2207642, by rfl⟩ : syracuseStep 2943523 = 4415285) B4415285
theorem B2615857 : Blo 1719060 2615857 := bstep (se 2 (by rfl) ⟨980946, by rfl⟩ : syracuseStep 2615857 = 1961893) B1961893
theorem B3869297 : Blo 1719060 3869297 := bstep (se 2 (by rfl) ⟨1450986, by rfl⟩ : syracuseStep 3869297 = 2901973) B2901973
theorem B3869315 : Blo 1719060 3869315 := bstep (se 1 (by rfl) ⟨2901986, by rfl⟩ : syracuseStep 3869315 = 5803973) B5803973
theorem B1936003 : Blo 1719060 1936003 := bstep (se 1 (by rfl) ⟨1452002, by rfl⟩ : syracuseStep 1936003 = 2904005) B2904005
theorem B2902675 : Blo 1719060 2902675 := bstep (se 1 (by rfl) ⟨2177006, by rfl⟩ : syracuseStep 2902675 = 4354013) B4354013
theorem B2755313 : Blo 1719060 2755313 := bstep (se 2 (by rfl) ⟨1033242, by rfl⟩ : syracuseStep 2755313 = 2066485) B2066485
theorem B1936147 : Blo 1719060 1936147 := bstep (se 1 (by rfl) ⟨1452110, by rfl⟩ : syracuseStep 1936147 = 2904221) B2904221
theorem B2902817 : Blo 1719060 2902817 := bstep (se 2 (by rfl) ⟨1088556, by rfl⟩ : syracuseStep 2902817 = 2177113) B2177113
theorem B4352849 : Blo 1719060 4352849 := bstep (se 2 (by rfl) ⟨1632318, by rfl⟩ : syracuseStep 4352849 = 3264637) B3264637
theorem B4352899 : Blo 1719060 4352899 := bstep (se 1 (by rfl) ⟨3264674, by rfl⟩ : syracuseStep 4352899 = 6529349) B6529349
theorem B5802893 : Blo 1719060 5802893 := bstep (se 3 (by rfl) ⟨1088042, by rfl⟩ : syracuseStep 5802893 = 2176085) B2176085
theorem B3869585 : Blo 1719060 3869585 := bstep (se 2 (by rfl) ⟨1451094, by rfl⟩ : syracuseStep 3869585 = 2902189) B2902189
theorem B2902945 : Blo 1719060 2902945 := bstep (se 2 (by rfl) ⟨1088604, by rfl⟩ : syracuseStep 2902945 = 2177209) B2177209
theorem B3869603 : Blo 1719060 3869603 := bstep (se 1 (by rfl) ⟨2902202, by rfl⟩ : syracuseStep 3869603 = 5804405) B5804405
theorem B5802947 : Blo 1719060 5802947 := bstep (se 1 (by rfl) ⟨4352210, by rfl⟩ : syracuseStep 5802947 = 8704421) B8704421
theorem B2902979 : Blo 1719060 2902979 := bstep (se 1 (by rfl) ⟨2177234, by rfl⟩ : syracuseStep 2902979 = 4354469) B4354469
theorem B4353041 : Blo 1719060 4353041 := bstep (se 2 (by rfl) ⟨1632390, by rfl⟩ : syracuseStep 4353041 = 3264781) B3264781
theorem B7842865 : Blo 1719060 7842865 := bstep (se 2 (by rfl) ⟨2941074, by rfl⟩ : syracuseStep 7842865 = 5882149) B5882149
theorem B2903107 : Blo 1719060 2903107 := bstep (se 1 (by rfl) ⟨2177330, by rfl⟩ : syracuseStep 2903107 = 4354661) B4354661
theorem B19598435 : Blo 1719060 19598435 := bstep (se 1 (by rfl) ⟨14698826, by rfl⟩ : syracuseStep 19598435 = 29397653) B29397653
theorem B3099779 : Blo 1719060 3099779 := bstep (se 1 (by rfl) ⟨2324834, by rfl⟩ : syracuseStep 3099779 = 4649669) B4649669
theorem B9800837 : Blo 1719060 9800837 := bstep (se 4 (by rfl) ⟨918828, by rfl⟩ : syracuseStep 9800837 = 1837657) B1837657
theorem B3263665 : Blo 1719060 3263665 := bstep (se 2 (by rfl) ⟨1223874, by rfl⟩ : syracuseStep 3263665 = 2447749) B2447749
theorem B3869873 : Blo 1719060 3869873 := bstep (se 2 (by rfl) ⟨1451202, by rfl⟩ : syracuseStep 3869873 = 2902405) B2902405
theorem B3869891 : Blo 1719060 3869891 := bstep (se 1 (by rfl) ⟨2902418, by rfl⟩ : syracuseStep 3869891 = 5804837) B5804837
theorem B14699717 : Blo 1719060 14699717 := bstep (se 4 (by rfl) ⟨1378098, by rfl⟩ : syracuseStep 14699717 = 2756197) B2756197
theorem B5803217 : Blo 1719060 5803217 := bstep (se 2 (by rfl) ⟨2176206, by rfl⟩ : syracuseStep 5803217 = 4352413) B4352413
theorem B2903249 : Blo 1719060 2903249 := bstep (se 2 (by rfl) ⟨1088718, by rfl⟩ : syracuseStep 2903249 = 2177437) B2177437
theorem B16764131 : Blo 1719060 16764131 := bstep (se 1 (by rfl) ⟨12573098, by rfl⟩ : syracuseStep 16764131 = 25146197) B25146197
theorem B2755825 : Blo 1719060 2755825 := bstep (se 2 (by rfl) ⟨1033434, by rfl⟩ : syracuseStep 2755825 = 2066869) B2066869
theorem B2903377 : Blo 1719060 2903377 := bstep (se 2 (by rfl) ⟨1088766, by rfl⟩ : syracuseStep 2903377 = 2177533) B2177533
theorem B5508461 : Blo 1719060 5508461 := bstep (se 3 (by rfl) ⟨1032836, by rfl⟩ : syracuseStep 5508461 = 2065673) B2065673
theorem B2903411 : Blo 1719060 2903411 := bstep (se 1 (by rfl) ⟨2177558, by rfl⟩ : syracuseStep 2903411 = 4355117) B4355117
theorem B10456517 : Blo 1719060 10456517 := bstep (se 4 (by rfl) ⟨980298, by rfl⟩ : syracuseStep 10456517 = 1960597) B1960597
theorem B3870161 : Blo 1719060 3870161 := bstep (se 2 (by rfl) ⟨1451310, by rfl⟩ : syracuseStep 3870161 = 2902621) B2902621
theorem B3870179 : Blo 1719060 3870179 := bstep (se 1 (by rfl) ⟨2902634, by rfl⟩ : syracuseStep 3870179 = 5805269) B5805269
theorem B2903539 : Blo 1719060 2903539 := bstep (se 1 (by rfl) ⟨2177654, by rfl⟩ : syracuseStep 2903539 = 4355309) B4355309
theorem B9301517 : Blo 1719060 9301517 := bstep (se 3 (by rfl) ⟨1744034, by rfl⟩ : syracuseStep 9301517 = 3488069) B3488069
theorem B3264067 : Blo 1719060 3264067 := bstep (se 1 (by rfl) ⟨2448050, by rfl⟩ : syracuseStep 3264067 = 4896101) B4896101
theorem B4132451 : Blo 1719060 4132451 := bstep (se 1 (by rfl) ⟨3099338, by rfl⟩ : syracuseStep 4132451 = 6198677) B6198677
theorem B3264113 : Blo 1719060 3264113 := bstep (se 2 (by rfl) ⟨1224042, by rfl⟩ : syracuseStep 3264113 = 2448085) B2448085
theorem B6532721 : Blo 1719060 6532721 := bstep (se 2 (by rfl) ⟨2449770, by rfl⟩ : syracuseStep 6532721 = 4899541) B4899541
theorem B2903681 : Blo 1719060 2903681 := bstep (se 2 (by rfl) ⟨1088880, by rfl⟩ : syracuseStep 2903681 = 2177761) B2177761
theorem B5803757 : Blo 1719060 5803757 := bstep (se 3 (by rfl) ⟨1088204, by rfl⟩ : syracuseStep 5803757 = 2176409) B2176409
theorem B3870449 : Blo 1719060 3870449 := bstep (se 2 (by rfl) ⟨1451418, by rfl⟩ : syracuseStep 3870449 = 2902837) B2902837
theorem B8269553 : Blo 1719060 8269553 := bstep (se 2 (by rfl) ⟨3101082, by rfl⟩ : syracuseStep 8269553 = 6202165) B6202165
theorem B2903809 : Blo 1719060 2903809 := bstep (se 2 (by rfl) ⟨1088928, by rfl⟩ : syracuseStep 2903809 = 2177857) B2177857
theorem B3485443 : Blo 1719060 3485443 := bstep (se 1 (by rfl) ⟨2614082, by rfl⟩ : syracuseStep 3485443 = 5228165) B5228165
theorem B3870467 : Blo 1719060 3870467 := bstep (se 1 (by rfl) ⟨2902850, by rfl⟩ : syracuseStep 3870467 = 5805701) B5805701
theorem B5803811 : Blo 1719060 5803811 := bstep (se 1 (by rfl) ⟨4352858, by rfl⟩ : syracuseStep 5803811 = 8705717) B8705717
theorem B2903843 : Blo 1719060 2903843 := bstep (se 1 (by rfl) ⟨2177882, by rfl⟩ : syracuseStep 2903843 = 4355765) B4355765
theorem B3673955 : Blo 1719060 3673955 := bstep (se 1 (by rfl) ⟨2755466, by rfl⟩ : syracuseStep 3673955 = 5510933) B5510933
theorem B8712035 : Blo 1719060 8712035 := bstep (se 1 (by rfl) ⟨6534026, by rfl⟩ : syracuseStep 8712035 = 13068053) B13068053
theorem B3264401 : Blo 1719060 3264401 := bstep (se 2 (by rfl) ⟨1224150, by rfl⟩ : syracuseStep 3264401 = 2448301) B2448301
theorem B2903971 : Blo 1719060 2903971 := bstep (se 1 (by rfl) ⟨2177978, by rfl⟩ : syracuseStep 2903971 = 4355957) B4355957
theorem B6287309 : Blo 1719060 6287309 := bstep (se 3 (by rfl) ⟨1178870, by rfl⟩ : syracuseStep 6287309 = 2357741) B2357741
theorem B4354033 : Blo 1719060 4354033 := bstep (se 2 (by rfl) ⟨1632762, by rfl⟩ : syracuseStep 4354033 = 3265525) B3265525
theorem B3870737 : Blo 1719060 3870737 := bstep (se 2 (by rfl) ⟨1451526, by rfl⟩ : syracuseStep 3870737 = 2903053) B2903053
theorem B4411427 : Blo 1719060 4411427 := bstep (se 1 (by rfl) ⟨3308570, by rfl⟩ : syracuseStep 4411427 = 6617141) B6617141
theorem B3870755 : Blo 1719060 3870755 := bstep (se 1 (by rfl) ⟨2903066, by rfl⟩ : syracuseStep 3870755 = 5806133) B5806133
theorem B5804081 : Blo 1719060 5804081 := bstep (se 2 (by rfl) ⟨2176530, by rfl⟩ : syracuseStep 5804081 = 4353061) B4353061
theorem B2904113 : Blo 1719060 2904113 := bstep (se 2 (by rfl) ⟨1089042, by rfl⟩ : syracuseStep 2904113 = 2178085) B2178085
theorem B10457201 : Blo 1719060 10457201 := bstep (se 2 (by rfl) ⟨3921450, by rfl⟩ : syracuseStep 10457201 = 7842901) B7842901
theorem B3100817 : Blo 1719060 3100817 := bstep (se 2 (by rfl) ⟨1162806, by rfl⟩ : syracuseStep 3100817 = 2325613) B2325613
theorem B2904241 : Blo 1719060 2904241 := bstep (se 2 (by rfl) ⟨1089090, by rfl⟩ : syracuseStep 2904241 = 2178181) B2178181
theorem B2904275 : Blo 1719060 2904275 := bstep (se 1 (by rfl) ⟨2178206, by rfl⟩ : syracuseStep 2904275 = 4356413) B4356413
theorem B4133123 : Blo 1719060 4133123 := bstep (se 1 (by rfl) ⟨3099842, by rfl⟩ : syracuseStep 4133123 = 6199685) B6199685
theorem B4354307 : Blo 1719060 4354307 := bstep (se 1 (by rfl) ⟨3265730, by rfl⟩ : syracuseStep 4354307 = 6531461) B6531461
theorem B3871025 : Blo 1719060 3871025 := bstep (se 2 (by rfl) ⟨1451634, by rfl⟩ : syracuseStep 3871025 = 2903269) B2903269
theorem B3486019 : Blo 1719060 3486019 := bstep (se 1 (by rfl) ⟨2614514, by rfl⟩ : syracuseStep 3486019 = 5229029) B5229029
theorem B3871043 : Blo 1719060 3871043 := bstep (se 1 (by rfl) ⟨2903282, by rfl⟩ : syracuseStep 3871043 = 5806565) B5806565
theorem B5509549 : Blo 1719060 5509549 := bstep (se 3 (by rfl) ⟨1033040, by rfl⟩ : syracuseStep 5509549 = 2066081) B2066081
theorem B4354499 : Blo 1719060 4354499 := bstep (se 1 (by rfl) ⟨3265874, by rfl⟩ : syracuseStep 4354499 = 6531749) B6531749
theorem B4133393 : Blo 1719060 4133393 := bstep (se 2 (by rfl) ⟨1550022, by rfl⟩ : syracuseStep 4133393 = 3100045) B3100045
theorem B5804621 : Blo 1719060 5804621 := bstep (se 3 (by rfl) ⟨1088366, by rfl⟩ : syracuseStep 5804621 = 2176733) B2176733
theorem B3871313 : Blo 1719060 3871313 := bstep (se 2 (by rfl) ⟨1451742, by rfl⟩ : syracuseStep 3871313 = 2903485) B2903485
theorem B3265123 : Blo 1719060 3265123 := bstep (se 1 (by rfl) ⟨2448842, by rfl⟩ : syracuseStep 3265123 = 4897685) B4897685
theorem B3871331 : Blo 1719060 3871331 := bstep (se 1 (by rfl) ⟨2903498, by rfl⟩ : syracuseStep 3871331 = 5806997) B5806997
theorem B5804675 : Blo 1719060 5804675 := bstep (se 1 (by rfl) ⟨4353506, by rfl⟩ : syracuseStep 5804675 = 8707013) B8707013
theorem B8712845 : Blo 1719060 8712845 := bstep (se 3 (by rfl) ⟨1633658, by rfl⟩ : syracuseStep 8712845 = 3267317) B3267317
theorem B4895441 : Blo 1719060 4895441 := bstep (se 2 (by rfl) ⟨1835790, by rfl⟩ : syracuseStep 4895441 = 3671581) B3671581
theorem B4133585 : Blo 1719060 4133585 := bstep (se 2 (by rfl) ⟨1550094, by rfl⟩ : syracuseStep 4133585 = 3100189) B3100189
theorem B3920675 : Blo 1719060 3920675 := bstep (se 1 (by rfl) ⟨2940506, by rfl⟩ : syracuseStep 3920675 = 5881013) B5881013
theorem B4133681 : Blo 1719060 4133681 := bstep (se 2 (by rfl) ⟨1550130, by rfl⟩ : syracuseStep 4133681 = 3100261) B3100261
theorem B3871601 : Blo 1719060 3871601 := bstep (se 2 (by rfl) ⟨1451850, by rfl⟩ : syracuseStep 3871601 = 2903701) B2903701
theorem B3871619 : Blo 1719060 3871619 := bstep (se 1 (by rfl) ⟨2903714, by rfl⟩ : syracuseStep 3871619 = 5807429) B5807429
theorem B5804945 : Blo 1719060 5804945 := bstep (se 2 (by rfl) ⟨2176854, by rfl⟩ : syracuseStep 5804945 = 4353709) B4353709
theorem B2175923 : Blo 1719060 2175923 := bstep (se 1 (by rfl) ⟨1631942, by rfl⟩ : syracuseStep 2175923 = 3263885) B3263885
theorem B3535825 : Blo 1719060 3535825 := bstep (se 2 (by rfl) ⟨1325934, by rfl⟩ : syracuseStep 3535825 = 2651869) B2651869
theorem B3265571 : Blo 1719060 3265571 := bstep (se 1 (by rfl) ⟨2449178, by rfl⟩ : syracuseStep 3265571 = 4898357) B4898357
theorem B6534179 : Blo 1719060 6534179 := bstep (se 1 (by rfl) ⟨4900634, by rfl⟩ : syracuseStep 6534179 = 9801269) B9801269
theorem B3675203 : Blo 1719060 3675203 := bstep (se 1 (by rfl) ⟨2756402, by rfl⟩ : syracuseStep 3675203 = 5512805) B5512805
theorem B2356339 : Blo 1719060 2356339 := bstep (se 1 (by rfl) ⟨1767254, by rfl⟩ : syracuseStep 2356339 = 3534509) B3534509
theorem B3871889 : Blo 1719060 3871889 := bstep (se 2 (by rfl) ⟨1451958, by rfl⟩ : syracuseStep 3871889 = 2903917) B2903917
theorem B3871907 : Blo 1719060 3871907 := bstep (se 1 (by rfl) ⟨2903930, by rfl⟩ : syracuseStep 3871907 = 5807861) B5807861
theorem B2323667 : Blo 1719060 2323667 := bstep (se 1 (by rfl) ⟨1742750, by rfl⟩ : syracuseStep 2323667 = 3485501) B3485501
theorem B5584099 : Blo 1719060 5584099 := bstep (se 1 (by rfl) ⟨4188074, by rfl⟩ : syracuseStep 5584099 = 8376149) B8376149
theorem B5231885 : Blo 1719060 5231885 := bstep (se 3 (by rfl) ⟨980978, by rfl⟩ : syracuseStep 5231885 = 1961957) B1961957
theorem B3265859 : Blo 1719060 3265859 := bstep (se 1 (by rfl) ⟨2449394, by rfl⟩ : syracuseStep 3265859 = 4898789) B4898789
theorem B10458467 : Blo 1719060 10458467 := bstep (se 1 (by rfl) ⟨7843850, by rfl⟩ : syracuseStep 10458467 = 15687701) B15687701
theorem B1987939 : Blo 1719060 1987939 := bstep (se 1 (by rfl) ⟨1490954, by rfl⟩ : syracuseStep 1987939 = 2981909) B2981909
theorem B8705393 : Blo 1719060 8705393 := bstep (se 2 (by rfl) ⟨3264522, by rfl⟩ : syracuseStep 8705393 = 6529045) B6529045
theorem B4355441 : Blo 1719060 4355441 := bstep (se 2 (by rfl) ⟨1633290, by rfl⟩ : syracuseStep 4355441 = 3266581) B3266581
theorem B4355491 : Blo 1719060 4355491 := bstep (se 1 (by rfl) ⟨3266618, by rfl⟩ : syracuseStep 4355491 = 6533237) B6533237
theorem B5805485 : Blo 1719060 5805485 := bstep (se 3 (by rfl) ⟨1088528, by rfl⟩ : syracuseStep 5805485 = 2177057) B2177057
theorem B3872177 : Blo 1719060 3872177 := bstep (se 2 (by rfl) ⟨1452066, by rfl⟩ : syracuseStep 3872177 = 2904133) B2904133
theorem B3872195 : Blo 1719060 3872195 := bstep (se 1 (by rfl) ⟨2904146, by rfl⟩ : syracuseStep 3872195 = 5808293) B5808293
theorem B6616525 : Blo 1719060 6616525 := bstep (se 3 (by rfl) ⟨1240598, by rfl⟩ : syracuseStep 6616525 = 2481197) B2481197
theorem B4896227 : Blo 1719060 4896227 := bstep (se 1 (by rfl) ⟨3672170, by rfl⟩ : syracuseStep 4896227 = 7344341) B7344341
theorem B5805539 : Blo 1719060 5805539 := bstep (se 1 (by rfl) ⟨4354154, by rfl⟩ : syracuseStep 5805539 = 8708309) B8708309
theorem B4355633 : Blo 1719060 4355633 := bstep (se 2 (by rfl) ⟨1633362, by rfl⟩ : syracuseStep 4355633 = 3266725) B3266725
theorem B2176627 : Blo 1719060 2176627 := bstep (se 1 (by rfl) ⟨1632470, by rfl⟩ : syracuseStep 2176627 = 3264941) B3264941
theorem B2176723 : Blo 1719060 2176723 := bstep (se 1 (by rfl) ⟨1632542, by rfl⟩ : syracuseStep 2176723 = 3265085) B3265085
theorem B11024099 : Blo 1719060 11024099 := bstep (se 1 (by rfl) ⟨8268074, by rfl⟩ : syracuseStep 11024099 = 16536149) B16536149
theorem B5805809 : Blo 1719060 5805809 := bstep (se 2 (by rfl) ⟨2177178, by rfl⟩ : syracuseStep 5805809 = 4354357) B4354357
theorem B37197589 : Blo 1719060 37197589 := bstep (se 6 (by rfl) ⟨871818, by rfl⟩ : syracuseStep 37197589 = 1743637) B1743637
theorem B4896557 : Blo 1719060 4896557 := bstep (se 3 (by rfl) ⟨918104, by rfl⟩ : syracuseStep 4896557 = 1836209) B1836209
theorem B7345997 : Blo 1719060 7345997 := bstep (se 3 (by rfl) ⟨1377374, by rfl⟩ : syracuseStep 7345997 = 2754749) B2754749
theorem B4896625 : Blo 1719060 4896625 := bstep (se 2 (by rfl) ⟨1836234, by rfl⟩ : syracuseStep 4896625 = 3672469) B3672469
theorem B3143537 : Blo 1719060 3143537 := bstep (se 2 (by rfl) ⟨1178826, by rfl⟩ : syracuseStep 3143537 = 2357653) B2357653
theorem B22050701 : Blo 1719060 22050701 := bstep (se 3 (by rfl) ⟨4134506, by rfl⟩ : syracuseStep 22050701 = 8269013) B8269013
theorem B4134883 : Blo 1719060 4134883 := bstep (se 1 (by rfl) ⟨3101162, by rfl⟩ : syracuseStep 4134883 = 6202325) B6202325
theorem B2324579 : Blo 1719060 2324579 := bstep (se 1 (by rfl) ⟨1743434, by rfl⟩ : syracuseStep 2324579 = 3486869) B3486869
theorem B4896899 : Blo 1719060 4896899 := bstep (se 1 (by rfl) ⟨3672674, by rfl⟩ : syracuseStep 4896899 = 7345349) B7345349
theorem B2578595 : Blo 1719060 2578595 := bstep (se 1 (by rfl) ⟨1933946, by rfl⟩ : syracuseStep 2578595 = 3867893) B3867893
theorem B7346339 : Blo 1719060 7346339 := bstep (se 1 (by rfl) ⟨5509754, by rfl⟩ : syracuseStep 7346339 = 11019509) B11019509
theorem B5511331 : Blo 1719060 5511331 := bstep (se 1 (by rfl) ⟨4133498, by rfl⟩ : syracuseStep 5511331 = 8266997) B8266997
theorem B3487907 : Blo 1719060 3487907 := bstep (se 1 (by rfl) ⟨2615930, by rfl⟩ : syracuseStep 3487907 = 5231861) B5231861
theorem B2578625 : Blo 1719060 2578625 := bstep (se 2 (by rfl) ⟨966984, by rfl⟩ : syracuseStep 2578625 = 1933969) B1933969
theorem B2177219 : Blo 1719060 2177219 := bstep (se 1 (by rfl) ⟨1632914, by rfl⟩ : syracuseStep 2177219 = 3265829) B3265829
theorem B2578643 : Blo 1719060 2578643 := bstep (se 1 (by rfl) ⟨1933982, by rfl⟩ : syracuseStep 2578643 = 3867965) B3867965
theorem B5511395 : Blo 1719060 5511395 := bstep (se 1 (by rfl) ⟨4133546, by rfl⟩ : syracuseStep 5511395 = 8267093) B8267093
theorem B4651235 : Blo 1719060 4651235 := bstep (se 1 (by rfl) ⟨3488426, by rfl⟩ : syracuseStep 4651235 = 6976853) B6976853
theorem B2578673 : Blo 1719060 2578673 := bstep (se 2 (by rfl) ⟨967002, by rfl⟩ : syracuseStep 2578673 = 1934005) B1934005
theorem B3266801 : Blo 1719060 3266801 := bstep (se 2 (by rfl) ⟨1225050, by rfl⟩ : syracuseStep 3266801 = 2450101) B2450101
theorem B2578691 : Blo 1719060 2578691 := bstep (se 1 (by rfl) ⟨1934018, by rfl⟩ : syracuseStep 2578691 = 3868037) B3868037
theorem B5806349 : Blo 1719060 5806349 := bstep (se 3 (by rfl) ⟨1088690, by rfl⟩ : syracuseStep 5806349 = 2177381) B2177381
theorem B2578721 : Blo 1719060 2578721 := bstep (se 2 (by rfl) ⟨967020, by rfl⟩ : syracuseStep 2578721 = 1934041) B1934041
theorem B5511473 : Blo 1719060 5511473 := bstep (se 2 (by rfl) ⟨2066802, by rfl⟩ : syracuseStep 5511473 = 4133605) B4133605
theorem B2578739 : Blo 1719060 2578739 := bstep (se 1 (by rfl) ⟨1934054, by rfl⟩ : syracuseStep 2578739 = 3868109) B3868109
theorem B5806403 : Blo 1719060 5806403 := bstep (se 1 (by rfl) ⟨4354802, by rfl⟩ : syracuseStep 5806403 = 8709605) B8709605
theorem B2578769 : Blo 1719060 2578769 := bstep (se 2 (by rfl) ⟨967038, by rfl⟩ : syracuseStep 2578769 = 1934077) B1934077
theorem B2578787 : Blo 1719060 2578787 := bstep (se 1 (by rfl) ⟨1934090, by rfl⟩ : syracuseStep 2578787 = 3868181) B3868181
theorem B2578817 : Blo 1719060 2578817 := bstep (se 2 (by rfl) ⟨967056, by rfl⟩ : syracuseStep 2578817 = 1934113) B1934113
theorem B2578835 : Blo 1719060 2578835 := bstep (se 1 (by rfl) ⟨1934126, by rfl⟩ : syracuseStep 2578835 = 3868253) B3868253
theorem B2447777 : Blo 1719060 2447777 := bstep (se 2 (by rfl) ⟨917916, by rfl⟩ : syracuseStep 2447777 = 1835833) B1835833
theorem B2578865 : Blo 1719060 2578865 := bstep (se 2 (by rfl) ⟨967074, by rfl⟩ : syracuseStep 2578865 = 1934149) B1934149
theorem B2578883 : Blo 1719060 2578883 := bstep (se 1 (by rfl) ⟨1934162, by rfl⟩ : syracuseStep 2578883 = 3868325) B3868325
theorem B2578913 : Blo 1719060 2578913 := bstep (se 2 (by rfl) ⟨967092, by rfl⟩ : syracuseStep 2578913 = 1934185) B1934185
theorem B22034915 : Blo 1719060 22034915 := bstep (se 1 (by rfl) ⟨16526186, by rfl⟩ : syracuseStep 22034915 = 33052373) B33052373
theorem B7952867 : Blo 1719060 7952867 := bstep (se 1 (by rfl) ⟨5964650, by rfl⟩ : syracuseStep 7952867 = 11929301) B11929301
theorem B2447857 : Blo 1719060 2447857 := bstep (se 2 (by rfl) ⟨917946, by rfl⟩ : syracuseStep 2447857 = 1835893) B1835893
theorem B2578931 : Blo 1719060 2578931 := bstep (se 1 (by rfl) ⟨1934198, by rfl⟩ : syracuseStep 2578931 = 3868397) B3868397
theorem B2578961 : Blo 1719060 2578961 := bstep (se 2 (by rfl) ⟨967110, by rfl⟩ : syracuseStep 2578961 = 1934221) B1934221
theorem B2578979 : Blo 1719060 2578979 := bstep (se 1 (by rfl) ⟨1934234, by rfl⟩ : syracuseStep 2578979 = 3868469) B3868469
theorem B11016739 : Blo 1719060 11016739 := bstep (se 1 (by rfl) ⟨8262554, by rfl⟩ : syracuseStep 11016739 = 16525109) B16525109
theorem B2579009 : Blo 1719060 2579009 := bstep (se 2 (by rfl) ⟨967128, by rfl⟩ : syracuseStep 2579009 = 1934257) B1934257
theorem B5806673 : Blo 1719060 5806673 := bstep (se 2 (by rfl) ⟨2177502, by rfl⟩ : syracuseStep 5806673 = 4355005) B4355005
theorem B2579027 : Blo 1719060 2579027 := bstep (se 1 (by rfl) ⟨1934270, by rfl⟩ : syracuseStep 2579027 = 3868541) B3868541
theorem B6527587 : Blo 1719060 6527587 := bstep (se 1 (by rfl) ⟨4895690, by rfl⟩ : syracuseStep 6527587 = 9791381) B9791381
theorem B2579057 : Blo 1719060 2579057 := bstep (se 2 (by rfl) ⟨967146, by rfl⟩ : syracuseStep 2579057 = 1934293) B1934293
theorem B7346801 : Blo 1719060 7346801 := bstep (se 2 (by rfl) ⟨2755050, by rfl⟩ : syracuseStep 7346801 = 5510101) B5510101
theorem B2579075 : Blo 1719060 2579075 := bstep (se 1 (by rfl) ⟨1934306, by rfl⟩ : syracuseStep 2579075 = 3868613) B3868613
theorem B2579105 : Blo 1719060 2579105 := bstep (se 2 (by rfl) ⟨967164, by rfl⟩ : syracuseStep 2579105 = 1934329) B1934329
theorem B2579123 : Blo 1719060 2579123 := bstep (se 1 (by rfl) ⟨1934342, by rfl⟩ : syracuseStep 2579123 = 3868685) B3868685
theorem B2579153 : Blo 1719060 2579153 := bstep (se 2 (by rfl) ⟨967182, by rfl⟩ : syracuseStep 2579153 = 1934365) B1934365
theorem B2579171 : Blo 1719060 2579171 := bstep (se 1 (by rfl) ⟨1934378, by rfl⟩ : syracuseStep 2579171 = 3868757) B3868757
theorem B2579201 : Blo 1719060 2579201 := bstep (se 2 (by rfl) ⟨967200, by rfl⟩ : syracuseStep 2579201 = 1934401) B1934401
theorem B2579219 : Blo 1719060 2579219 := bstep (se 1 (by rfl) ⟨1934414, by rfl⟩ : syracuseStep 2579219 = 3868829) B3868829
theorem B1719075 : Blo 1719060 1719075 := bstep (se 1 (by rfl) ⟨1289306, by rfl⟩ : syracuseStep 1719075 = 2578613) B2578613
theorem B8706851 : Blo 1719060 8706851 := bstep (se 1 (by rfl) ⟨6530138, by rfl⟩ : syracuseStep 8706851 = 13060277) B13060277
theorem B2579249 : Blo 1719060 2579249 := bstep (se 2 (by rfl) ⟨967218, by rfl⟩ : syracuseStep 2579249 = 1934437) B1934437
theorem B1719091 : Blo 1719060 1719091 := bstep (se 1 (by rfl) ⟨1289318, by rfl⟩ : syracuseStep 1719091 = 2578637) B2578637
theorem B1719107 : Blo 1719060 1719107 := bstep (se 1 (by rfl) ⟨1289330, by rfl⟩ : syracuseStep 1719107 = 2578661) B2578661
theorem B2579267 : Blo 1719060 2579267 := bstep (se 1 (by rfl) ⟨1934450, by rfl⟩ : syracuseStep 2579267 = 3868901) B3868901
theorem B1719123 : Blo 1719060 1719123 := bstep (se 1 (by rfl) ⟨1289342, by rfl⟩ : syracuseStep 1719123 = 2578685) B2578685
theorem B2579297 : Blo 1719060 2579297 := bstep (se 2 (by rfl) ⟨967236, by rfl⟩ : syracuseStep 2579297 = 1934473) B1934473
theorem B1719139 : Blo 1719060 1719139 := bstep (se 1 (by rfl) ⟨1289354, by rfl⟩ : syracuseStep 1719139 = 2578709) B2578709
theorem B7846769 : Blo 1719060 7846769 := bstep (se 2 (by rfl) ⟨2942538, by rfl⟩ : syracuseStep 7846769 = 5885077) B5885077
theorem B1719155 : Blo 1719060 1719155 := bstep (se 1 (by rfl) ⟨1289366, by rfl⟩ : syracuseStep 1719155 = 2578733) B2578733
theorem B2579315 : Blo 1719060 2579315 := bstep (se 1 (by rfl) ⟨1934486, by rfl⟩ : syracuseStep 2579315 = 3868973) B3868973
theorem B1719171 : Blo 1719060 1719171 := bstep (se 1 (by rfl) ⟨1289378, by rfl⟩ : syracuseStep 1719171 = 2578757) B2578757
theorem B2177923 : Blo 1719060 2177923 := bstep (se 1 (by rfl) ⟨1633442, by rfl⟩ : syracuseStep 2177923 = 3266885) B3266885
theorem B2579345 : Blo 1719060 2579345 := bstep (se 2 (by rfl) ⟨967254, by rfl⟩ : syracuseStep 2579345 = 1934509) B1934509
theorem B1719187 : Blo 1719060 1719187 := bstep (se 1 (by rfl) ⟨1289390, by rfl⟩ : syracuseStep 1719187 = 2578781) B2578781
theorem B1719203 : Blo 1719060 1719203 := bstep (se 1 (by rfl) ⟨1289402, by rfl⟩ : syracuseStep 1719203 = 2578805) B2578805
theorem B2579363 : Blo 1719060 2579363 := bstep (se 1 (by rfl) ⟨1934522, by rfl⟩ : syracuseStep 2579363 = 3869045) B3869045
theorem B1719219 : Blo 1719060 1719219 := bstep (se 1 (by rfl) ⟨1289414, by rfl⟩ : syracuseStep 1719219 = 2578829) B2578829
theorem B2579393 : Blo 1719060 2579393 := bstep (se 2 (by rfl) ⟨967272, by rfl⟩ : syracuseStep 2579393 = 1934545) B1934545
theorem B1719235 : Blo 1719060 1719235 := bstep (se 1 (by rfl) ⟨1289426, by rfl⟩ : syracuseStep 1719235 = 2578853) B2578853
theorem B4897741 : Blo 1719060 4897741 := bstep (se 3 (by rfl) ⟨918326, by rfl⟩ : syracuseStep 4897741 = 1836653) B1836653
theorem B1719251 : Blo 1719060 1719251 := bstep (se 1 (by rfl) ⟨1289438, by rfl⟩ : syracuseStep 1719251 = 2578877) B2578877
theorem B2579411 : Blo 1719060 2579411 := bstep (se 1 (by rfl) ⟨1934558, by rfl⟩ : syracuseStep 2579411 = 3869117) B3869117
theorem B1719267 : Blo 1719060 1719267 := bstep (se 1 (by rfl) ⟨1289450, by rfl⟩ : syracuseStep 1719267 = 2578901) B2578901
theorem B2178019 : Blo 1719060 2178019 := bstep (se 1 (by rfl) ⟨1633514, by rfl⟩ : syracuseStep 2178019 = 3267029) B3267029
theorem B2579441 : Blo 1719060 2579441 := bstep (se 2 (by rfl) ⟨967290, by rfl⟩ : syracuseStep 2579441 = 1934581) B1934581
theorem B1719283 : Blo 1719060 1719283 := bstep (se 1 (by rfl) ⟨1289462, by rfl⟩ : syracuseStep 1719283 = 2578925) B2578925
theorem B1719299 : Blo 1719060 1719299 := bstep (se 1 (by rfl) ⟨1289474, by rfl⟩ : syracuseStep 1719299 = 2578949) B2578949
theorem B2579459 : Blo 1719060 2579459 := bstep (se 1 (by rfl) ⟨1934594, by rfl⟩ : syracuseStep 2579459 = 3869189) B3869189
theorem B1719315 : Blo 1719060 1719315 := bstep (se 1 (by rfl) ⟨1289486, by rfl⟩ : syracuseStep 1719315 = 2578973) B2578973
theorem B2579489 : Blo 1719060 2579489 := bstep (se 2 (by rfl) ⟨967308, by rfl⟩ : syracuseStep 2579489 = 1934617) B1934617
theorem B1719331 : Blo 1719060 1719331 := bstep (se 1 (by rfl) ⟨1289498, by rfl⟩ : syracuseStep 1719331 = 2578997) B2578997
theorem B1719347 : Blo 1719060 1719347 := bstep (se 1 (by rfl) ⟨1289510, by rfl⟩ : syracuseStep 1719347 = 2579021) B2579021
theorem B2579507 : Blo 1719060 2579507 := bstep (se 1 (by rfl) ⟨1934630, by rfl⟩ : syracuseStep 2579507 = 3869261) B3869261
theorem B1719363 : Blo 1719060 1719363 := bstep (se 1 (by rfl) ⟨1289522, by rfl⟩ : syracuseStep 1719363 = 2579045) B2579045
theorem B2579537 : Blo 1719060 2579537 := bstep (se 2 (by rfl) ⟨967326, by rfl⟩ : syracuseStep 2579537 = 1934653) B1934653
theorem B1719379 : Blo 1719060 1719379 := bstep (se 1 (by rfl) ⟨1289534, by rfl⟩ : syracuseStep 1719379 = 2579069) B2579069
theorem B1719395 : Blo 1719060 1719395 := bstep (se 1 (by rfl) ⟨1289546, by rfl⟩ : syracuseStep 1719395 = 2579093) B2579093
theorem B2579555 : Blo 1719060 2579555 := bstep (se 1 (by rfl) ⟨1934666, by rfl⟩ : syracuseStep 2579555 = 3869333) B3869333
theorem B4897901 : Blo 1719060 4897901 := bstep (se 3 (by rfl) ⟨918356, by rfl⟩ : syracuseStep 4897901 = 1836713) B1836713
theorem B5807213 : Blo 1719060 5807213 := bstep (se 3 (by rfl) ⟨1088852, by rfl⟩ : syracuseStep 5807213 = 2177705) B2177705
theorem B14687345 : Blo 1719060 14687345 := bstep (se 2 (by rfl) ⟨5507754, by rfl⟩ : syracuseStep 14687345 = 11015509) B11015509
theorem B1719411 : Blo 1719060 1719411 := bstep (se 1 (by rfl) ⟨1289558, by rfl⟩ : syracuseStep 1719411 = 2579117) B2579117
theorem B2579585 : Blo 1719060 2579585 := bstep (se 2 (by rfl) ⟨967344, by rfl⟩ : syracuseStep 2579585 = 1934689) B1934689
theorem B1719427 : Blo 1719060 1719427 := bstep (se 1 (by rfl) ⟨1289570, by rfl⟩ : syracuseStep 1719427 = 2579141) B2579141
theorem B2792593 : Blo 1719060 2792593 := bstep (se 2 (by rfl) ⟨1047222, by rfl⟩ : syracuseStep 2792593 = 2094445) B2094445
theorem B1719443 : Blo 1719060 1719443 := bstep (se 1 (by rfl) ⟨1289582, by rfl⟩ : syracuseStep 1719443 = 2579165) B2579165
theorem B2579603 : Blo 1719060 2579603 := bstep (se 1 (by rfl) ⟨1934702, by rfl⟩ : syracuseStep 2579603 = 3869405) B3869405
theorem B1719459 : Blo 1719060 1719459 := bstep (se 1 (by rfl) ⟨1289594, by rfl⟩ : syracuseStep 1719459 = 2579189) B2579189
theorem B5807267 : Blo 1719060 5807267 := bstep (se 1 (by rfl) ⟨4355450, by rfl⟩ : syracuseStep 5807267 = 8710901) B8710901
theorem B2579633 : Blo 1719060 2579633 := bstep (se 2 (by rfl) ⟨967362, by rfl⟩ : syracuseStep 2579633 = 1934725) B1934725
theorem B1719475 : Blo 1719060 1719475 := bstep (se 1 (by rfl) ⟨1289606, by rfl⟩ : syracuseStep 1719475 = 2579213) B2579213
theorem B22346933 : Blo 1719060 22346933 := bstep (se 5 (by rfl) ⟨1047512, by rfl⟩ : syracuseStep 22346933 = 2095025) B2095025
theorem B1719491 : Blo 1719060 1719491 := bstep (se 1 (by rfl) ⟨1289618, by rfl⟩ : syracuseStep 1719491 = 2579237) B2579237
theorem B2579651 : Blo 1719060 2579651 := bstep (se 1 (by rfl) ⟨1934738, by rfl⟩ : syracuseStep 2579651 = 3869477) B3869477
theorem B1719507 : Blo 1719060 1719507 := bstep (se 1 (by rfl) ⟨1289630, by rfl⟩ : syracuseStep 1719507 = 2579261) B2579261
theorem B2579681 : Blo 1719060 2579681 := bstep (se 2 (by rfl) ⟨967380, by rfl⟩ : syracuseStep 2579681 = 1934761) B1934761
theorem B1719523 : Blo 1719060 1719523 := bstep (se 1 (by rfl) ⟨1289642, by rfl⟩ : syracuseStep 1719523 = 2579285) B2579285
theorem B1719539 : Blo 1719060 1719539 := bstep (se 1 (by rfl) ⟨1289654, by rfl⟩ : syracuseStep 1719539 = 2579309) B2579309
theorem B2579699 : Blo 1719060 2579699 := bstep (se 1 (by rfl) ⟨1934774, by rfl⟩ : syracuseStep 2579699 = 3869549) B3869549
theorem B1719555 : Blo 1719060 1719555 := bstep (se 1 (by rfl) ⟨1289666, by rfl⟩ : syracuseStep 1719555 = 2579333) B2579333
theorem B2448643 : Blo 1719060 2448643 := bstep (se 1 (by rfl) ⟨1836482, by rfl⟩ : syracuseStep 2448643 = 3672965) B3672965
theorem B2579729 : Blo 1719060 2579729 := bstep (se 2 (by rfl) ⟨967398, by rfl⟩ : syracuseStep 2579729 = 1934797) B1934797
theorem B1719571 : Blo 1719060 1719571 := bstep (se 1 (by rfl) ⟨1289678, by rfl⟩ : syracuseStep 1719571 = 2579357) B2579357
theorem B1719587 : Blo 1719060 1719587 := bstep (se 1 (by rfl) ⟨1289690, by rfl⟩ : syracuseStep 1719587 = 2579381) B2579381
theorem B2579747 : Blo 1719060 2579747 := bstep (se 1 (by rfl) ⟨1934810, by rfl⟩ : syracuseStep 2579747 = 3869621) B3869621
theorem B4898083 : Blo 1719060 4898083 := bstep (se 1 (by rfl) ⟨3673562, by rfl⟩ : syracuseStep 4898083 = 7347125) B7347125
theorem B1719603 : Blo 1719060 1719603 := bstep (se 1 (by rfl) ⟨1289702, by rfl⟩ : syracuseStep 1719603 = 2579405) B2579405
theorem B2579777 : Blo 1719060 2579777 := bstep (se 2 (by rfl) ⟨967416, by rfl⟩ : syracuseStep 2579777 = 1934833) B1934833
theorem B1719619 : Blo 1719060 1719619 := bstep (se 1 (by rfl) ⟨1289714, by rfl⟩ : syracuseStep 1719619 = 2579429) B2579429
theorem B1719635 : Blo 1719060 1719635 := bstep (se 1 (by rfl) ⟨1289726, by rfl⟩ : syracuseStep 1719635 = 2579453) B2579453
theorem B2579795 : Blo 1719060 2579795 := bstep (se 1 (by rfl) ⟨1934846, by rfl⟩ : syracuseStep 2579795 = 3869693) B3869693
theorem B1719651 : Blo 1719060 1719651 := bstep (se 1 (by rfl) ⟨1289738, by rfl⟩ : syracuseStep 1719651 = 2579477) B2579477
theorem B2579825 : Blo 1719060 2579825 := bstep (se 2 (by rfl) ⟨967434, by rfl⟩ : syracuseStep 2579825 = 1934869) B1934869
theorem B1719667 : Blo 1719060 1719667 := bstep (se 1 (by rfl) ⟨1289750, by rfl⟩ : syracuseStep 1719667 = 2579501) B2579501
theorem B1719683 : Blo 1719060 1719683 := bstep (se 1 (by rfl) ⟨1289762, by rfl⟩ : syracuseStep 1719683 = 2579525) B2579525
theorem B2579843 : Blo 1719060 2579843 := bstep (se 1 (by rfl) ⟨1934882, by rfl⟩ : syracuseStep 2579843 = 3869765) B3869765
theorem B1719699 : Blo 1719060 1719699 := bstep (se 1 (by rfl) ⟨1289774, by rfl⟩ : syracuseStep 1719699 = 2579549) B2579549
theorem B2579873 : Blo 1719060 2579873 := bstep (se 2 (by rfl) ⟨967452, by rfl⟩ : syracuseStep 2579873 = 1934905) B1934905
theorem B1719715 : Blo 1719060 1719715 := bstep (se 1 (by rfl) ⟨1289786, by rfl⟩ : syracuseStep 1719715 = 2579573) B2579573
theorem B5807537 : Blo 1719060 5807537 := bstep (se 2 (by rfl) ⟨2177826, by rfl⟩ : syracuseStep 5807537 = 4355653) B4355653
theorem B1719731 : Blo 1719060 1719731 := bstep (se 1 (by rfl) ⟨1289798, by rfl⟩ : syracuseStep 1719731 = 2579597) B2579597
theorem B2579891 : Blo 1719060 2579891 := bstep (se 1 (by rfl) ⟨1934918, by rfl⟩ : syracuseStep 2579891 = 3869837) B3869837
theorem B1719747 : Blo 1719060 1719747 := bstep (se 1 (by rfl) ⟨1289810, by rfl⟩ : syracuseStep 1719747 = 2579621) B2579621
theorem B2579921 : Blo 1719060 2579921 := bstep (se 2 (by rfl) ⟨967470, by rfl⟩ : syracuseStep 2579921 = 1934941) B1934941
theorem B1719763 : Blo 1719060 1719763 := bstep (se 1 (by rfl) ⟨1289822, by rfl⟩ : syracuseStep 1719763 = 2579645) B2579645
theorem B1719779 : Blo 1719060 1719779 := bstep (se 1 (by rfl) ⟨1289834, by rfl⟩ : syracuseStep 1719779 = 2579669) B2579669
theorem B2579939 : Blo 1719060 2579939 := bstep (se 1 (by rfl) ⟨1934954, by rfl⟩ : syracuseStep 2579939 = 3869909) B3869909
theorem B1719795 : Blo 1719060 1719795 := bstep (se 1 (by rfl) ⟨1289846, by rfl⟩ : syracuseStep 1719795 = 2579693) B2579693
theorem B2579969 : Blo 1719060 2579969 := bstep (se 2 (by rfl) ⟨967488, by rfl⟩ : syracuseStep 2579969 = 1934977) B1934977
theorem B1719811 : Blo 1719060 1719811 := bstep (se 1 (by rfl) ⟨1289858, by rfl⟩ : syracuseStep 1719811 = 2579717) B2579717
theorem B11017741 : Blo 1719060 11017741 := bstep (se 3 (by rfl) ⟨2065826, by rfl⟩ : syracuseStep 11017741 = 4131653) B4131653
theorem B1719827 : Blo 1719060 1719827 := bstep (se 1 (by rfl) ⟨1289870, by rfl⟩ : syracuseStep 1719827 = 2579741) B2579741
theorem B2579987 : Blo 1719060 2579987 := bstep (se 1 (by rfl) ⟨1934990, by rfl⟩ : syracuseStep 2579987 = 3869981) B3869981
theorem B1719843 : Blo 1719060 1719843 := bstep (se 1 (by rfl) ⟨1289882, by rfl⟩ : syracuseStep 1719843 = 2579765) B2579765
theorem B2580017 : Blo 1719060 2580017 := bstep (se 2 (by rfl) ⟨967506, by rfl⟩ : syracuseStep 2580017 = 1935013) B1935013
theorem B1719859 : Blo 1719060 1719859 := bstep (se 1 (by rfl) ⟨1289894, by rfl⟩ : syracuseStep 1719859 = 2579789) B2579789
theorem B1719875 : Blo 1719060 1719875 := bstep (se 1 (by rfl) ⟨1289906, by rfl⟩ : syracuseStep 1719875 = 2579813) B2579813
theorem B2580035 : Blo 1719060 2580035 := bstep (se 1 (by rfl) ⟨1935026, by rfl⟩ : syracuseStep 2580035 = 3870053) B3870053
theorem B8707661 : Blo 1719060 8707661 := bstep (se 3 (by rfl) ⟨1632686, by rfl⟩ : syracuseStep 8707661 = 3265373) B3265373
theorem B1719891 : Blo 1719060 1719891 := bstep (se 1 (by rfl) ⟨1289918, by rfl⟩ : syracuseStep 1719891 = 2579837) B2579837
theorem B2580065 : Blo 1719060 2580065 := bstep (se 2 (by rfl) ⟨967524, by rfl⟩ : syracuseStep 2580065 = 1935049) B1935049
theorem B1719907 : Blo 1719060 1719907 := bstep (se 1 (by rfl) ⟨1289930, by rfl⟩ : syracuseStep 1719907 = 2579861) B2579861
theorem B1719923 : Blo 1719060 1719923 := bstep (se 1 (by rfl) ⟨1289942, by rfl⟩ : syracuseStep 1719923 = 2579885) B2579885
theorem B2580083 : Blo 1719060 2580083 := bstep (se 1 (by rfl) ⟨1935062, by rfl⟩ : syracuseStep 2580083 = 3870125) B3870125
theorem B1719939 : Blo 1719060 1719939 := bstep (se 1 (by rfl) ⟨1289954, by rfl⟩ : syracuseStep 1719939 = 2579909) B2579909
theorem B2580113 : Blo 1719060 2580113 := bstep (se 2 (by rfl) ⟨967542, by rfl⟩ : syracuseStep 2580113 = 1935085) B1935085
theorem B1719955 : Blo 1719060 1719955 := bstep (se 1 (by rfl) ⟨1289966, by rfl⟩ : syracuseStep 1719955 = 2579933) B2579933
theorem B1719971 : Blo 1719060 1719971 := bstep (se 1 (by rfl) ⟨1289978, by rfl⟩ : syracuseStep 1719971 = 2579957) B2579957
theorem B2580131 : Blo 1719060 2580131 := bstep (se 1 (by rfl) ⟨1935098, by rfl⟩ : syracuseStep 2580131 = 3870197) B3870197
theorem B1719987 : Blo 1719060 1719987 := bstep (se 1 (by rfl) ⟨1289990, by rfl⟩ : syracuseStep 1719987 = 2579981) B2579981
theorem B2580161 : Blo 1719060 2580161 := bstep (se 2 (by rfl) ⟨967560, by rfl⟩ : syracuseStep 2580161 = 1935121) B1935121
theorem B1720003 : Blo 1719060 1720003 := bstep (se 1 (by rfl) ⟨1290002, by rfl⟩ : syracuseStep 1720003 = 2580005) B2580005
theorem B9297605 : Blo 1719060 9297605 := bstep (se 4 (by rfl) ⟨871650, by rfl⟩ : syracuseStep 9297605 = 1743301) B1743301
theorem B1720019 : Blo 1719060 1720019 := bstep (se 1 (by rfl) ⟨1290014, by rfl⟩ : syracuseStep 1720019 = 2580029) B2580029
theorem B2580179 : Blo 1719060 2580179 := bstep (se 1 (by rfl) ⟨1935134, by rfl⟩ : syracuseStep 2580179 = 3870269) B3870269
theorem B2449121 : Blo 1719060 2449121 := bstep (se 2 (by rfl) ⟨918420, by rfl⟩ : syracuseStep 2449121 = 1836841) B1836841
theorem B1720035 : Blo 1719060 1720035 := bstep (se 1 (by rfl) ⟨1290026, by rfl⟩ : syracuseStep 1720035 = 2580053) B2580053
theorem B2580209 : Blo 1719060 2580209 := bstep (se 2 (by rfl) ⟨967578, by rfl⟩ : syracuseStep 2580209 = 1935157) B1935157
theorem B1720051 : Blo 1719060 1720051 := bstep (se 1 (by rfl) ⟨1290038, by rfl⟩ : syracuseStep 1720051 = 2580077) B2580077
theorem B2793217 : Blo 1719060 2793217 := bstep (se 2 (by rfl) ⟨1047456, by rfl⟩ : syracuseStep 2793217 = 2094913) B2094913
theorem B1720067 : Blo 1719060 1720067 := bstep (se 1 (by rfl) ⟨1290050, by rfl⟩ : syracuseStep 1720067 = 2580101) B2580101
theorem B2580227 : Blo 1719060 2580227 := bstep (se 1 (by rfl) ⟨1935170, by rfl⟩ : syracuseStep 2580227 = 3870341) B3870341
theorem B1720083 : Blo 1719060 1720083 := bstep (se 1 (by rfl) ⟨1290062, by rfl⟩ : syracuseStep 1720083 = 2580125) B2580125
theorem B2580257 : Blo 1719060 2580257 := bstep (se 2 (by rfl) ⟨967596, by rfl⟩ : syracuseStep 2580257 = 1935193) B1935193
theorem B1720099 : Blo 1719060 1720099 := bstep (se 1 (by rfl) ⟨1290074, by rfl⟩ : syracuseStep 1720099 = 2580149) B2580149
theorem B1720115 : Blo 1719060 1720115 := bstep (se 1 (by rfl) ⟨1290086, by rfl⟩ : syracuseStep 1720115 = 2580173) B2580173
theorem B2580275 : Blo 1719060 2580275 := bstep (se 1 (by rfl) ⟨1935206, by rfl⟩ : syracuseStep 2580275 = 3870413) B3870413
theorem B1720131 : Blo 1719060 1720131 := bstep (se 1 (by rfl) ⟨1290098, by rfl⟩ : syracuseStep 1720131 = 2580197) B2580197
theorem B2580305 : Blo 1719060 2580305 := bstep (se 2 (by rfl) ⟨967614, by rfl⟩ : syracuseStep 2580305 = 1935229) B1935229
theorem B1720147 : Blo 1719060 1720147 := bstep (se 1 (by rfl) ⟨1290110, by rfl⟩ : syracuseStep 1720147 = 2580221) B2580221
theorem B2449235 : Blo 1719060 2449235 := bstep (se 1 (by rfl) ⟨1836926, by rfl⟩ : syracuseStep 2449235 = 3673853) B3673853
theorem B1720163 : Blo 1719060 1720163 := bstep (se 1 (by rfl) ⟨1290122, by rfl⟩ : syracuseStep 1720163 = 2580245) B2580245
theorem B2580323 : Blo 1719060 2580323 := bstep (se 1 (by rfl) ⟨1935242, by rfl⟩ : syracuseStep 2580323 = 3870485) B3870485
theorem B1720179 : Blo 1719060 1720179 := bstep (se 1 (by rfl) ⟨1290134, by rfl⟩ : syracuseStep 1720179 = 2580269) B2580269
theorem B2580353 : Blo 1719060 2580353 := bstep (se 2 (by rfl) ⟨967632, by rfl⟩ : syracuseStep 2580353 = 1935265) B1935265
theorem B1720195 : Blo 1719060 1720195 := bstep (se 1 (by rfl) ⟨1290146, by rfl⟩ : syracuseStep 1720195 = 2580293) B2580293
theorem B1720211 : Blo 1719060 1720211 := bstep (se 1 (by rfl) ⟨1290158, by rfl⟩ : syracuseStep 1720211 = 2580317) B2580317
theorem B2580371 : Blo 1719060 2580371 := bstep (se 1 (by rfl) ⟨1935278, by rfl⟩ : syracuseStep 2580371 = 3870557) B3870557
theorem B1720227 : Blo 1719060 1720227 := bstep (se 1 (by rfl) ⟨1290170, by rfl⟩ : syracuseStep 1720227 = 2580341) B2580341
theorem B2449315 : Blo 1719060 2449315 := bstep (se 1 (by rfl) ⟨1836986, by rfl⟩ : syracuseStep 2449315 = 3673973) B3673973
theorem B2580401 : Blo 1719060 2580401 := bstep (se 2 (by rfl) ⟨967650, by rfl⟩ : syracuseStep 2580401 = 1935301) B1935301
theorem B1720243 : Blo 1719060 1720243 := bstep (se 1 (by rfl) ⟨1290182, by rfl⟩ : syracuseStep 1720243 = 2580365) B2580365
theorem B1720259 : Blo 1719060 1720259 := bstep (se 1 (by rfl) ⟨1290194, by rfl⟩ : syracuseStep 1720259 = 2580389) B2580389
theorem B2580419 : Blo 1719060 2580419 := bstep (se 1 (by rfl) ⟨1935314, by rfl⟩ : syracuseStep 2580419 = 3870629) B3870629
theorem B5808077 : Blo 1719060 5808077 := bstep (se 3 (by rfl) ⟨1089014, by rfl⟩ : syracuseStep 5808077 = 2178029) B2178029
theorem B1720275 : Blo 1719060 1720275 := bstep (se 1 (by rfl) ⟨1290206, by rfl⟩ : syracuseStep 1720275 = 2580413) B2580413
theorem B2580449 : Blo 1719060 2580449 := bstep (se 2 (by rfl) ⟨967668, by rfl⟩ : syracuseStep 2580449 = 1935337) B1935337
theorem B1720291 : Blo 1719060 1720291 := bstep (se 1 (by rfl) ⟨1290218, by rfl⟩ : syracuseStep 1720291 = 2580437) B2580437
theorem B12402659 : Blo 1719060 12402659 := bstep (se 1 (by rfl) ⟨9301994, by rfl⟩ : syracuseStep 12402659 = 18603989) B18603989
theorem B1720307 : Blo 1719060 1720307 := bstep (se 1 (by rfl) ⟨1290230, by rfl⟩ : syracuseStep 1720307 = 2580461) B2580461
theorem B2580467 : Blo 1719060 2580467 := bstep (se 1 (by rfl) ⟨1935350, by rfl⟩ : syracuseStep 2580467 = 3870701) B3870701
theorem B2580491 : Blo 1719060 2580491 := bstep (se 1 (by rfl) ⟨1935368, by rfl⟩ : syracuseStep 2580491 = 3870737) B3870737
theorem B1720331 : Blo 1719060 1720331 := bstep (se 1 (by rfl) ⟨1290248, by rfl⟩ : syracuseStep 1720331 = 2580497) B2580497
theorem B2580503 : Blo 1719060 2580503 := bstep (se 1 (by rfl) ⟨1935377, by rfl⟩ : syracuseStep 2580503 = 3870755) B3870755
theorem B1720343 : Blo 1719060 1720343 := bstep (se 1 (by rfl) ⟨1290257, by rfl⟩ : syracuseStep 1720343 = 2580515) B2580515
theorem B1720363 : Blo 1719060 1720363 := bstep (se 1 (by rfl) ⟨1290272, by rfl⟩ : syracuseStep 1720363 = 2580545) B2580545
theorem B1720375 : Blo 1719060 1720375 := bstep (se 1 (by rfl) ⟨1290281, by rfl⟩ : syracuseStep 1720375 = 2580563) B2580563
theorem B1720395 : Blo 1719060 1720395 := bstep (se 1 (by rfl) ⟨1290296, by rfl⟩ : syracuseStep 1720395 = 2580593) B2580593
theorem B1720407 : Blo 1719060 1720407 := bstep (se 1 (by rfl) ⟨1290305, by rfl⟩ : syracuseStep 1720407 = 2580611) B2580611
theorem B2580569 : Blo 1719060 2580569 := bstep (se 2 (by rfl) ⟨967713, by rfl⟩ : syracuseStep 2580569 = 1935427) B1935427
theorem B11763805 : Blo 1719060 11763805 := bstep (se 3 (by rfl) ⟨2205713, by rfl⟩ : syracuseStep 11763805 = 4411427) B4411427
theorem B1720427 : Blo 1719060 1720427 := bstep (se 1 (by rfl) ⟨1290320, by rfl⟩ : syracuseStep 1720427 = 2580641) B2580641
theorem B1720439 : Blo 1719060 1720439 := bstep (se 1 (by rfl) ⟨1290329, by rfl⟩ : syracuseStep 1720439 = 2580659) B2580659
theorem B1720459 : Blo 1719060 1720459 := bstep (se 1 (by rfl) ⟨1290344, by rfl⟩ : syracuseStep 1720459 = 2580689) B2580689
theorem B1720471 : Blo 1719060 1720471 := bstep (se 1 (by rfl) ⟨1290353, by rfl⟩ : syracuseStep 1720471 = 2580707) B2580707
theorem B1720491 : Blo 1719060 1720491 := bstep (se 1 (by rfl) ⟨1290368, by rfl⟩ : syracuseStep 1720491 = 2580737) B2580737
theorem B1720503 : Blo 1719060 1720503 := bstep (se 1 (by rfl) ⟨1290377, by rfl⟩ : syracuseStep 1720503 = 2580755) B2580755
theorem B2580683 : Blo 1719060 2580683 := bstep (se 1 (by rfl) ⟨1935512, by rfl⟩ : syracuseStep 2580683 = 3871025) B3871025
theorem B1720523 : Blo 1719060 1720523 := bstep (se 1 (by rfl) ⟨1290392, by rfl⟩ : syracuseStep 1720523 = 2580785) B2580785
theorem B2580695 : Blo 1719060 2580695 := bstep (se 1 (by rfl) ⟨1935521, by rfl⟩ : syracuseStep 2580695 = 3871043) B3871043
theorem B1720535 : Blo 1719060 1720535 := bstep (se 1 (by rfl) ⟨1290401, by rfl⟩ : syracuseStep 1720535 = 2580803) B2580803
theorem B7348441 : Blo 1719060 7348441 := bstep (se 2 (by rfl) ⟨2755665, by rfl⟩ : syracuseStep 7348441 = 5511331) B5511331
theorem B1720555 : Blo 1719060 1720555 := bstep (se 1 (by rfl) ⟨1290416, by rfl⟩ : syracuseStep 1720555 = 2580833) B2580833
theorem B1720567 : Blo 1719060 1720567 := bstep (se 1 (by rfl) ⟨1290425, by rfl⟩ : syracuseStep 1720567 = 2580851) B2580851
theorem B1720587 : Blo 1719060 1720587 := bstep (se 1 (by rfl) ⟨1290440, by rfl⟩ : syracuseStep 1720587 = 2580881) B2580881
theorem B1720599 : Blo 1719060 1720599 := bstep (se 1 (by rfl) ⟨1290449, by rfl⟩ : syracuseStep 1720599 = 2580899) B2580899
theorem B2580761 : Blo 1719060 2580761 := bstep (se 2 (by rfl) ⟨967785, by rfl⟩ : syracuseStep 2580761 = 1935571) B1935571
theorem B1720619 : Blo 1719060 1720619 := bstep (se 1 (by rfl) ⟨1290464, by rfl⟩ : syracuseStep 1720619 = 2580929) B2580929
theorem B27885869 : Blo 1719060 27885869 := bstep (se 3 (by rfl) ⟨5228600, by rfl⟩ : syracuseStep 27885869 = 10457201) B10457201
theorem B1720631 : Blo 1719060 1720631 := bstep (se 1 (by rfl) ⟨1290473, by rfl⟩ : syracuseStep 1720631 = 2580947) B2580947
theorem B1720651 : Blo 1719060 1720651 := bstep (se 1 (by rfl) ⟨1290488, by rfl⟩ : syracuseStep 1720651 = 2580977) B2580977
theorem B11026763 : Blo 1719060 11026763 := bstep (se 1 (by rfl) ⟨8270072, by rfl⟩ : syracuseStep 11026763 = 16540145) B16540145
theorem B1720663 : Blo 1719060 1720663 := bstep (se 1 (by rfl) ⟨1290497, by rfl⟩ : syracuseStep 1720663 = 2580995) B2580995
theorem B1720683 : Blo 1719060 1720683 := bstep (se 1 (by rfl) ⟨1290512, by rfl⟩ : syracuseStep 1720683 = 2581025) B2581025
theorem B41820533 : Blo 1719060 41820533 := bstep (se 5 (by rfl) ⟨1960337, by rfl⟩ : syracuseStep 41820533 = 3920675) B3920675
theorem B1720695 : Blo 1719060 1720695 := bstep (se 1 (by rfl) ⟨1290521, by rfl⟩ : syracuseStep 1720695 = 2581043) B2581043
theorem B2580875 : Blo 1719060 2580875 := bstep (se 1 (by rfl) ⟨1935656, by rfl⟩ : syracuseStep 2580875 = 3871313) B3871313
theorem B1720715 : Blo 1719060 1720715 := bstep (se 1 (by rfl) ⟨1290536, by rfl⟩ : syracuseStep 1720715 = 2581073) B2581073
theorem B2580887 : Blo 1719060 2580887 := bstep (se 1 (by rfl) ⟨1935665, by rfl⟩ : syracuseStep 2580887 = 3871331) B3871331
theorem B1720727 : Blo 1719060 1720727 := bstep (se 1 (by rfl) ⟨1290545, by rfl⟩ : syracuseStep 1720727 = 2581091) B2581091
theorem B1720747 : Blo 1719060 1720747 := bstep (se 1 (by rfl) ⟨1290560, by rfl⟩ : syracuseStep 1720747 = 2581121) B2581121
theorem B5808563 : Blo 1719060 5808563 := bstep (se 1 (by rfl) ⟨4356422, by rfl⟩ : syracuseStep 5808563 = 8712845) B8712845
theorem B1720759 : Blo 1719060 1720759 := bstep (se 1 (by rfl) ⟨1290569, by rfl⟩ : syracuseStep 1720759 = 2581139) B2581139
theorem B1720779 : Blo 1719060 1720779 := bstep (se 1 (by rfl) ⟨1290584, by rfl⟩ : syracuseStep 1720779 = 2581169) B2581169
theorem B1720791 : Blo 1719060 1720791 := bstep (se 1 (by rfl) ⟨1290593, by rfl⟩ : syracuseStep 1720791 = 2581187) B2581187
theorem B2580953 : Blo 1719060 2580953 := bstep (se 2 (by rfl) ⟨967857, by rfl⟩ : syracuseStep 2580953 = 1935715) B1935715
theorem B1720811 : Blo 1719060 1720811 := bstep (se 1 (by rfl) ⟨1290608, by rfl⟩ : syracuseStep 1720811 = 2581217) B2581217
theorem B1720823 : Blo 1719060 1720823 := bstep (se 1 (by rfl) ⟨1290617, by rfl⟩ : syracuseStep 1720823 = 2581235) B2581235
theorem B1720843 : Blo 1719060 1720843 := bstep (se 1 (by rfl) ⟨1290632, by rfl⟩ : syracuseStep 1720843 = 2581265) B2581265
theorem B1720855 : Blo 1719060 1720855 := bstep (se 1 (by rfl) ⟨1290641, by rfl⟩ : syracuseStep 1720855 = 2581283) B2581283
theorem B1720875 : Blo 1719060 1720875 := bstep (se 1 (by rfl) ⟨1290656, by rfl⟩ : syracuseStep 1720875 = 2581313) B2581313
theorem B1720887 : Blo 1719060 1720887 := bstep (se 1 (by rfl) ⟨1290665, by rfl⟩ : syracuseStep 1720887 = 2581331) B2581331
theorem B2581067 : Blo 1719060 2581067 := bstep (se 1 (by rfl) ⟨1935800, by rfl⟩ : syracuseStep 2581067 = 3871601) B3871601
theorem B1720907 : Blo 1719060 1720907 := bstep (se 1 (by rfl) ⟨1290680, by rfl⟩ : syracuseStep 1720907 = 2581361) B2581361
theorem B2581079 : Blo 1719060 2581079 := bstep (se 1 (by rfl) ⟨1935809, by rfl⟩ : syracuseStep 2581079 = 3871619) B3871619
theorem B1720919 : Blo 1719060 1720919 := bstep (se 1 (by rfl) ⟨1290689, by rfl⟩ : syracuseStep 1720919 = 2581379) B2581379
theorem B44704349 : Blo 1719060 44704349 := bstep (se 3 (by rfl) ⟨8382065, by rfl⟩ : syracuseStep 44704349 = 16764131) B16764131
theorem B1720939 : Blo 1719060 1720939 := bstep (se 1 (by rfl) ⟨1290704, by rfl⟩ : syracuseStep 1720939 = 2581409) B2581409
theorem B1720951 : Blo 1719060 1720951 := bstep (se 1 (by rfl) ⟨1290713, by rfl⟩ : syracuseStep 1720951 = 2581427) B2581427
theorem B1720971 : Blo 1719060 1720971 := bstep (se 1 (by rfl) ⟨1290728, by rfl⟩ : syracuseStep 1720971 = 2581457) B2581457
theorem B1720983 : Blo 1719060 1720983 := bstep (se 1 (by rfl) ⟨1290737, by rfl⟩ : syracuseStep 1720983 = 2581475) B2581475
theorem B2581145 : Blo 1719060 2581145 := bstep (se 2 (by rfl) ⟨967929, by rfl⟩ : syracuseStep 2581145 = 1935859) B1935859
theorem B1721003 : Blo 1719060 1721003 := bstep (se 1 (by rfl) ⟨1290752, by rfl⟩ : syracuseStep 1721003 = 2581505) B2581505
theorem B1721015 : Blo 1719060 1721015 := bstep (se 1 (by rfl) ⟨1290761, by rfl⟩ : syracuseStep 1721015 = 2581523) B2581523
theorem B1721035 : Blo 1719060 1721035 := bstep (se 1 (by rfl) ⟨1290776, by rfl⟩ : syracuseStep 1721035 = 2581553) B2581553
theorem B13951693 : Blo 1719060 13951693 := bstep (se 3 (by rfl) ⟨2615942, by rfl⟩ : syracuseStep 13951693 = 5231885) B5231885
theorem B2450135 : Blo 1719060 2450135 := bstep (se 1 (by rfl) ⟨1837601, by rfl⟩ : syracuseStep 2450135 = 3675203) B3675203
theorem B14688985 : Blo 1719060 14688985 := bstep (se 2 (by rfl) ⟨5508369, by rfl⟩ : syracuseStep 14688985 = 11016739) B11016739
theorem B1721047 : Blo 1719060 1721047 := bstep (se 1 (by rfl) ⟨1290785, by rfl⟩ : syracuseStep 1721047 = 2581571) B2581571
theorem B1934059 : Blo 1719060 1934059 := bstep (se 1 (by rfl) ⟨1450544, by rfl⟩ : syracuseStep 1934059 = 2901089) B2901089
theorem B2581259 : Blo 1719060 2581259 := bstep (se 1 (by rfl) ⟨1935944, by rfl⟩ : syracuseStep 2581259 = 3871889) B3871889
theorem B2581271 : Blo 1719060 2581271 := bstep (se 1 (by rfl) ⟨1935953, by rfl⟩ : syracuseStep 2581271 = 3871907) B3871907
theorem B1934167 : Blo 1719060 1934167 := bstep (se 1 (by rfl) ⟨1450625, by rfl⟩ : syracuseStep 1934167 = 2901251) B2901251
theorem B2581337 : Blo 1719060 2581337 := bstep (se 2 (by rfl) ⟨968001, by rfl⟩ : syracuseStep 2581337 = 1936003) B1936003
theorem B8708957 : Blo 1719060 8708957 := bstep (se 3 (by rfl) ⟨1632929, by rfl⟩ : syracuseStep 8708957 = 3265859) B3265859
theorem B6972311 : Blo 1719060 6972311 := bstep (se 1 (by rfl) ⟨5229233, by rfl⟩ : syracuseStep 6972311 = 10458467) B10458467
theorem B2581451 : Blo 1719060 2581451 := bstep (se 1 (by rfl) ⟨1936088, by rfl⟩ : syracuseStep 2581451 = 3872177) B3872177
theorem B2581463 : Blo 1719060 2581463 := bstep (se 1 (by rfl) ⟨1936097, by rfl⟩ : syracuseStep 2581463 = 3872195) B3872195
theorem B1934347 : Blo 1719060 1934347 := bstep (se 1 (by rfl) ⟨1450760, by rfl⟩ : syracuseStep 1934347 = 2901521) B2901521
theorem B55804949 : Blo 1719060 55804949 := bstep (se 6 (by rfl) ⟨1307928, by rfl⟩ : syracuseStep 55804949 = 2615857) B2615857
theorem B1836055 : Blo 1719060 1836055 := bstep (se 1 (by rfl) ⟨1377041, by rfl⟩ : syracuseStep 1836055 = 2754083) B2754083
theorem B2581529 : Blo 1719060 2581529 := bstep (se 2 (by rfl) ⟨968073, by rfl⟩ : syracuseStep 2581529 = 1936147) B1936147
theorem B22037579 : Blo 1719060 22037579 := bstep (se 1 (by rfl) ⟨16528184, by rfl⟩ : syracuseStep 22037579 = 33056369) B33056369
theorem B1934455 : Blo 1719060 1934455 := bstep (se 1 (by rfl) ⟨1450841, by rfl⟩ : syracuseStep 1934455 = 2901683) B2901683
theorem B2901143 : Blo 1719060 2901143 := bstep (se 1 (by rfl) ⟨2175857, by rfl⟩ : syracuseStep 2901143 = 4351715) B4351715
theorem B7349399 : Blo 1719060 7349399 := bstep (se 1 (by rfl) ⟨5512049, by rfl⟩ : syracuseStep 7349399 = 11024099) B11024099
theorem B14697733 : Blo 1719060 14697733 := bstep (se 4 (by rfl) ⟨1377912, by rfl⟩ : syracuseStep 14697733 = 2755825) B2755825
theorem B6530321 : Blo 1719060 6530321 := bstep (se 2 (by rfl) ⟨2448870, by rfl⟩ : syracuseStep 6530321 = 4897741) B4897741
theorem B2901271 : Blo 1719060 2901271 := bstep (se 1 (by rfl) ⟨2175953, by rfl⟩ : syracuseStep 2901271 = 4351907) B4351907
theorem B3867929 : Blo 1719060 3867929 := bstep (se 2 (by rfl) ⟨1450473, by rfl⟩ : syracuseStep 3867929 = 2900947) B2900947
theorem B1934635 : Blo 1719060 1934635 := bstep (se 1 (by rfl) ⟨1450976, by rfl⟩ : syracuseStep 1934635 = 2901953) B2901953
theorem B3868019 : Blo 1719060 3868019 := bstep (se 1 (by rfl) ⟨2901014, by rfl⟩ : syracuseStep 3868019 = 5802029) B5802029
theorem B1836427 : Blo 1719060 1836427 := bstep (se 1 (by rfl) ⟨1377320, by rfl⟩ : syracuseStep 1836427 = 2754641) B2754641
theorem B3868055 : Blo 1719060 3868055 := bstep (se 1 (by rfl) ⟨2901041, by rfl⟩ : syracuseStep 3868055 = 5802083) B5802083
theorem B1934743 : Blo 1719060 1934743 := bstep (se 1 (by rfl) ⟨1451057, by rfl⟩ : syracuseStep 1934743 = 2902115) B2902115
theorem B4900247 : Blo 1719060 4900247 := bstep (se 1 (by rfl) ⟨3675185, by rfl⟩ : syracuseStep 4900247 = 7350371) B7350371
theorem B3671563 : Blo 1719060 3671563 := bstep (se 1 (by rfl) ⟨2753672, by rfl⟩ : syracuseStep 3671563 = 5507345) B5507345
theorem B4351553 : Blo 1719060 4351553 := bstep (se 2 (by rfl) ⟨1631832, by rfl⟩ : syracuseStep 4351553 = 3263665) B3263665
theorem B3868235 : Blo 1719060 3868235 := bstep (se 1 (by rfl) ⟨2901176, by rfl⟩ : syracuseStep 3868235 = 5802353) B5802353
theorem B1934923 : Blo 1719060 1934923 := bstep (se 1 (by rfl) ⟨1451192, by rfl⟩ : syracuseStep 1934923 = 2902385) B2902385
theorem B3868289 : Blo 1719060 3868289 := bstep (se 2 (by rfl) ⟨1450608, by rfl⟩ : syracuseStep 3868289 = 2901217) B2901217
theorem B14689943 : Blo 1719060 14689943 := bstep (se 1 (by rfl) ⟨11017457, by rfl⟩ : syracuseStep 14689943 = 22034915) B22034915
theorem B5301911 : Blo 1719060 5301911 := bstep (se 1 (by rfl) ⟨3976433, by rfl⟩ : syracuseStep 5301911 = 7952867) B7952867
theorem B1935031 : Blo 1719060 1935031 := bstep (se 1 (by rfl) ⟨1451273, by rfl⟩ : syracuseStep 1935031 = 2902547) B2902547
theorem B6530777 : Blo 1719060 6530777 := bstep (se 2 (by rfl) ⟨2449041, by rfl⟩ : syracuseStep 6530777 = 4898083) B4898083
theorem B1836875 : Blo 1719060 1836875 := bstep (se 1 (by rfl) ⟨1377656, by rfl⟩ : syracuseStep 1836875 = 2755313) B2755313
theorem B3868505 : Blo 1719060 3868505 := bstep (se 2 (by rfl) ⟨1450689, by rfl⟩ : syracuseStep 3868505 = 2901379) B2901379
theorem B1935211 : Blo 1719060 1935211 := bstep (se 1 (by rfl) ⟨1451408, by rfl⟩ : syracuseStep 1935211 = 2902817) B2902817
theorem B2901899 : Blo 1719060 2901899 := bstep (se 1 (by rfl) ⟨2176424, by rfl⟩ : syracuseStep 2901899 = 4352849) B4352849
theorem B6530989 : Blo 1719060 6530989 := bstep (se 3 (by rfl) ⟨1224560, by rfl⟩ : syracuseStep 6530989 = 2449121) B2449121
theorem B3868595 : Blo 1719060 3868595 := bstep (se 1 (by rfl) ⟨2901446, by rfl⟩ : syracuseStep 3868595 = 5802893) B5802893
theorem B5801921 : Blo 1719060 5801921 := bstep (se 2 (by rfl) ⟨2175720, by rfl⟩ : syracuseStep 5801921 = 4351441) B4351441
theorem B3868631 : Blo 1719060 3868631 := bstep (se 1 (by rfl) ⟨2901473, by rfl⟩ : syracuseStep 3868631 = 5802947) B5802947
theorem B1935319 : Blo 1719060 1935319 := bstep (se 1 (by rfl) ⟨1451489, by rfl⟩ : syracuseStep 1935319 = 2902979) B2902979
theorem B2902027 : Blo 1719060 2902027 := bstep (se 1 (by rfl) ⟨2176520, by rfl⟩ : syracuseStep 2902027 = 4353041) B4353041
theorem B14690321 : Blo 1719060 14690321 := bstep (se 2 (by rfl) ⟨5508870, by rfl⟩ : syracuseStep 14690321 = 11017741) B11017741
theorem B9791563 : Blo 1719060 9791563 := bstep (se 1 (by rfl) ⟨7343672, by rfl⟩ : syracuseStep 9791563 = 14687345) B14687345
theorem B2066519 : Blo 1719060 2066519 := bstep (se 1 (by rfl) ⟨1549889, by rfl⟩ : syracuseStep 2066519 = 3099779) B3099779
theorem B4352089 : Blo 1719060 4352089 := bstep (se 2 (by rfl) ⟨1632033, by rfl⟩ : syracuseStep 4352089 = 3264067) B3264067
theorem B9799811 : Blo 1719060 9799811 := bstep (se 1 (by rfl) ⟨7349858, by rfl⟩ : syracuseStep 9799811 = 14699717) B14699717
theorem B3868811 : Blo 1719060 3868811 := bstep (se 1 (by rfl) ⟨2901608, by rfl⟩ : syracuseStep 3868811 = 5803217) B5803217
theorem B1935499 : Blo 1719060 1935499 := bstep (se 1 (by rfl) ⟨1451624, by rfl⟩ : syracuseStep 1935499 = 2903249) B2903249
theorem B2902169 : Blo 1719060 2902169 := bstep (se 2 (by rfl) ⟨1088313, by rfl⟩ : syracuseStep 2902169 = 2176627) B2176627
theorem B3868865 : Blo 1719060 3868865 := bstep (se 2 (by rfl) ⟨1450824, by rfl⟩ : syracuseStep 3868865 = 2901649) B2901649
theorem B6531293 : Blo 1719060 6531293 := bstep (se 3 (by rfl) ⟨1224617, by rfl⟩ : syracuseStep 6531293 = 2449235) B2449235
theorem B3672307 : Blo 1719060 3672307 := bstep (se 1 (by rfl) ⟨2754230, by rfl⟩ : syracuseStep 3672307 = 5508461) B5508461
theorem B1935607 : Blo 1719060 1935607 := bstep (se 1 (by rfl) ⟨1451705, by rfl⟩ : syracuseStep 1935607 = 2903411) B2903411
theorem B2902297 : Blo 1719060 2902297 := bstep (se 2 (by rfl) ⟨1088361, by rfl⟩ : syracuseStep 2902297 = 2176723) B2176723
theorem B4647257 : Blo 1719060 4647257 := bstep (se 2 (by rfl) ⟨1742721, by rfl⟩ : syracuseStep 4647257 = 3485443) B3485443
theorem B9791837 : Blo 1719060 9791837 := bstep (se 3 (by rfl) ⟨1835969, by rfl⟩ : syracuseStep 9791837 = 3671939) B3671939
theorem B49596785 : Blo 1719060 49596785 := bstep (se 2 (by rfl) ⟨18598794, by rfl⟩ : syracuseStep 49596785 = 37197589) B37197589
theorem B2754967 : Blo 1719060 2754967 := bstep (se 1 (by rfl) ⟨2066225, by rfl⟩ : syracuseStep 2754967 = 4132451) B4132451
theorem B3869081 : Blo 1719060 3869081 := bstep (se 2 (by rfl) ⟨1450905, by rfl⟩ : syracuseStep 3869081 = 2901811) B2901811
theorem B1935787 : Blo 1719060 1935787 := bstep (se 1 (by rfl) ⟨1451840, by rfl⟩ : syracuseStep 1935787 = 2903681) B2903681
theorem B6195649 : Blo 1719060 6195649 := bstep (se 2 (by rfl) ⟨2323368, by rfl⟩ : syracuseStep 6195649 = 4646737) B4646737
theorem B5802461 : Blo 1719060 5802461 := bstep (se 3 (by rfl) ⟨1087961, by rfl⟩ : syracuseStep 5802461 = 2175923) B2175923
theorem B3869171 : Blo 1719060 3869171 := bstep (se 1 (by rfl) ⟨2901878, by rfl⟩ : syracuseStep 3869171 = 5803757) B5803757
theorem B3869207 : Blo 1719060 3869207 := bstep (se 1 (by rfl) ⟨2901905, by rfl⟩ : syracuseStep 3869207 = 5803811) B5803811
theorem B1935895 : Blo 1719060 1935895 := bstep (se 1 (by rfl) ⟨1451921, by rfl⟩ : syracuseStep 1935895 = 2903843) B2903843
theorem B8268439 : Blo 1719060 8268439 := bstep (se 1 (by rfl) ⟨6201329, by rfl⟩ : syracuseStep 8268439 = 12402659) B12402659
theorem B27896501 : Blo 1719060 27896501 := bstep (se 5 (by rfl) ⟨1307648, by rfl⟩ : syracuseStep 27896501 = 2615297) B2615297
theorem B3869387 : Blo 1719060 3869387 := bstep (se 1 (by rfl) ⟨2902040, by rfl⟩ : syracuseStep 3869387 = 5804081) B5804081
theorem B1936075 : Blo 1719060 1936075 := bstep (se 1 (by rfl) ⟨1452056, by rfl⟩ : syracuseStep 1936075 = 2904113) B2904113
theorem B7842521 : Blo 1719060 7842521 := bstep (se 2 (by rfl) ⟨2940945, by rfl⟩ : syracuseStep 7842521 = 5881891) B5881891
theorem B3672793 : Blo 1719060 3672793 := bstep (se 2 (by rfl) ⟨1377297, by rfl⟩ : syracuseStep 3672793 = 2754595) B2754595
theorem B3869441 : Blo 1719060 3869441 := bstep (se 2 (by rfl) ⟨1451040, by rfl⟩ : syracuseStep 3869441 = 2902081) B2902081
theorem B2067211 : Blo 1719060 2067211 := bstep (se 1 (by rfl) ⟨1550408, by rfl⟩ : syracuseStep 2067211 = 3100817) B3100817
theorem B1936183 : Blo 1719060 1936183 := bstep (se 1 (by rfl) ⟨1452137, by rfl⟩ : syracuseStep 1936183 = 2904275) B2904275
theorem B2755415 : Blo 1719060 2755415 := bstep (se 1 (by rfl) ⟨2066561, by rfl⟩ : syracuseStep 2755415 = 4133123) B4133123
theorem B2902871 : Blo 1719060 2902871 := bstep (se 1 (by rfl) ⟨2177153, by rfl⟩ : syracuseStep 2902871 = 4354307) B4354307
theorem B15698789 : Blo 1719060 15698789 := bstep (se 4 (by rfl) ⟨1471761, by rfl⟩ : syracuseStep 15698789 = 2943523) B2943523
theorem B8711063 : Blo 1719060 8711063 := bstep (se 1 (by rfl) ⟨6533297, by rfl⟩ : syracuseStep 8711063 = 13066595) B13066595
theorem B2902999 : Blo 1719060 2902999 := bstep (se 1 (by rfl) ⟨2177249, by rfl⟩ : syracuseStep 2902999 = 4354499) B4354499
theorem B3869657 : Blo 1719060 3869657 := bstep (se 2 (by rfl) ⟨1451121, by rfl⟩ : syracuseStep 3869657 = 2902243) B2902243
theorem B2755595 : Blo 1719060 2755595 := bstep (se 1 (by rfl) ⟨2066696, by rfl⟩ : syracuseStep 2755595 = 4133393) B4133393
theorem B3869747 : Blo 1719060 3869747 := bstep (se 1 (by rfl) ⟨2902310, by rfl⟩ : syracuseStep 3869747 = 5804621) B5804621
theorem B4713547 : Blo 1719060 4713547 := bstep (se 1 (by rfl) ⟨3535160, by rfl⟩ : syracuseStep 4713547 = 7070321) B7070321
theorem B9301067 : Blo 1719060 9301067 := bstep (se 1 (by rfl) ⟨6975800, by rfl⟩ : syracuseStep 9301067 = 13951601) B13951601
theorem B3869783 : Blo 1719060 3869783 := bstep (se 1 (by rfl) ⟨2902337, by rfl⟩ : syracuseStep 3869783 = 5804675) B5804675
theorem B4648025 : Blo 1719060 4648025 := bstep (se 2 (by rfl) ⟨1743009, by rfl⟩ : syracuseStep 4648025 = 3486019) B3486019
theorem B3263627 : Blo 1719060 3263627 := bstep (se 1 (by rfl) ⟨2447720, by rfl⟩ : syracuseStep 3263627 = 4895441) B4895441
theorem B2755723 : Blo 1719060 2755723 := bstep (se 1 (by rfl) ⟨2066792, by rfl⟩ : syracuseStep 2755723 = 4133585) B4133585
theorem B59591821 : Blo 1719060 59591821 := bstep (se 3 (by rfl) ⟨11173466, by rfl⟩ : syracuseStep 59591821 = 22346933) B22346933
theorem B4353203 : Blo 1719060 4353203 := bstep (se 1 (by rfl) ⟨3264902, by rfl⟩ : syracuseStep 4353203 = 6529805) B6529805
theorem B2755787 : Blo 1719060 2755787 := bstep (se 1 (by rfl) ⟨2066840, by rfl⟩ : syracuseStep 2755787 = 4133681) B4133681
theorem B6196445 : Blo 1719060 6196445 := bstep (se 3 (by rfl) ⟨1161833, by rfl⟩ : syracuseStep 6196445 = 2323667) B2323667
theorem B3869963 : Blo 1719060 3869963 := bstep (se 1 (by rfl) ⟨2902472, by rfl⟩ : syracuseStep 3869963 = 5804945) B5804945
theorem B3263809 : Blo 1719060 3263809 := bstep (se 2 (by rfl) ⟨1223928, by rfl⟩ : syracuseStep 3263809 = 2447857) B2447857
theorem B3870017 : Blo 1719060 3870017 := bstep (se 2 (by rfl) ⟨1451256, by rfl⟩ : syracuseStep 3870017 = 2902513) B2902513
theorem B5303627 : Blo 1719060 5303627 := bstep (se 1 (by rfl) ⟨3977720, by rfl⟩ : syracuseStep 5303627 = 7955441) B7955441
theorem B1961419 : Blo 1719060 1961419 := bstep (se 1 (by rfl) ⟨1471064, by rfl⟩ : syracuseStep 1961419 = 2942129) B2942129
theorem B8703449 : Blo 1719060 8703449 := bstep (se 2 (by rfl) ⟨3263793, by rfl⟩ : syracuseStep 8703449 = 6527587) B6527587
theorem B4353497 : Blo 1719060 4353497 := bstep (se 2 (by rfl) ⟨1632561, by rfl⟩ : syracuseStep 4353497 = 3265123) B3265123
theorem B3870233 : Blo 1719060 3870233 := bstep (se 2 (by rfl) ⟨1451337, by rfl⟩ : syracuseStep 3870233 = 2902675) B2902675
theorem B5803595 : Blo 1719060 5803595 := bstep (se 1 (by rfl) ⟨4352696, by rfl⟩ : syracuseStep 5803595 = 8705393) B8705393
theorem B2903627 : Blo 1719060 2903627 := bstep (se 1 (by rfl) ⟨2177720, by rfl⟩ : syracuseStep 2903627 = 4355441) B4355441
theorem B3870323 : Blo 1719060 3870323 := bstep (se 1 (by rfl) ⟨2902742, by rfl⟩ : syracuseStep 3870323 = 5805485) B5805485
theorem B3264151 : Blo 1719060 3264151 := bstep (se 1 (by rfl) ⟨2448113, by rfl⟩ : syracuseStep 3264151 = 4896227) B4896227
theorem B3870359 : Blo 1719060 3870359 := bstep (se 1 (by rfl) ⟨2902769, by rfl⟩ : syracuseStep 3870359 = 5805539) B5805539
theorem B2903755 : Blo 1719060 2903755 := bstep (se 1 (by rfl) ⟨2177816, by rfl⟩ : syracuseStep 2903755 = 4355633) B4355633
theorem B3870539 : Blo 1719060 3870539 := bstep (se 1 (by rfl) ⟨2902904, by rfl⟩ : syracuseStep 3870539 = 5805809) B5805809
theorem B5803865 : Blo 1719060 5803865 := bstep (se 2 (by rfl) ⟨2176449, by rfl⟩ : syracuseStep 5803865 = 4352899) B4352899
theorem B2903897 : Blo 1719060 2903897 := bstep (se 2 (by rfl) ⟨1088961, by rfl⟩ : syracuseStep 2903897 = 2177923) B2177923
theorem B3264371 : Blo 1719060 3264371 := bstep (se 1 (by rfl) ⟨2448278, by rfl⟩ : syracuseStep 3264371 = 4896557) B4896557
theorem B3870593 : Blo 1719060 3870593 := bstep (se 2 (by rfl) ⟨1451472, by rfl⟩ : syracuseStep 3870593 = 2902945) B2902945
theorem B25472945 : Blo 1719060 25472945 := bstep (se 2 (by rfl) ⟨9552354, by rfl⟩ : syracuseStep 25472945 = 19104709) B19104709
theorem B14700467 : Blo 1719060 14700467 := bstep (se 1 (by rfl) ⟨11025350, by rfl⟩ : syracuseStep 14700467 = 22050701) B22050701
theorem B4714433 : Blo 1719060 4714433 := bstep (se 2 (by rfl) ⟨1767912, by rfl⟩ : syracuseStep 4714433 = 3535825) B3535825
theorem B2904025 : Blo 1719060 2904025 := bstep (se 2 (by rfl) ⟨1089009, by rfl⟩ : syracuseStep 2904025 = 2178019) B2178019
theorem B10457153 : Blo 1719060 10457153 := bstep (se 2 (by rfl) ⟨3921432, by rfl⟩ : syracuseStep 10457153 = 7842865) B7842865
theorem B3264599 : Blo 1719060 3264599 := bstep (se 1 (by rfl) ⟨2448449, by rfl⟩ : syracuseStep 3264599 = 4896899) B4896899
theorem B3870809 : Blo 1719060 3870809 := bstep (se 2 (by rfl) ⟨1451553, by rfl⟩ : syracuseStep 3870809 = 2903107) B2903107
theorem B3674263 : Blo 1719060 3674263 := bstep (se 1 (by rfl) ⟨2755697, by rfl⟩ : syracuseStep 3674263 = 5511395) B5511395
theorem B3100823 : Blo 1719060 3100823 := bstep (se 1 (by rfl) ⟨2325617, by rfl⟩ : syracuseStep 3100823 = 4651235) B4651235
theorem B3141785 : Blo 1719060 3141785 := bstep (se 2 (by rfl) ⟨1178169, by rfl⟩ : syracuseStep 3141785 = 2356339) B2356339
theorem B3870899 : Blo 1719060 3870899 := bstep (se 1 (by rfl) ⟨2903174, by rfl⟩ : syracuseStep 3870899 = 5806349) B5806349
theorem B7844033 : Blo 1719060 7844033 := bstep (se 2 (by rfl) ⟨2941512, by rfl⟩ : syracuseStep 7844033 = 5883025) B5883025
theorem B3723457 : Blo 1719060 3723457 := bstep (se 2 (by rfl) ⟨1396296, by rfl⟩ : syracuseStep 3723457 = 2792593) B2792593
theorem B3674315 : Blo 1719060 3674315 := bstep (se 1 (by rfl) ⟨2755736, by rfl⟩ : syracuseStep 3674315 = 5511473) B5511473
theorem B3870935 : Blo 1719060 3870935 := bstep (se 1 (by rfl) ⟨2903201, by rfl⟩ : syracuseStep 3870935 = 5806403) B5806403
theorem B3264857 : Blo 1719060 3264857 := bstep (se 2 (by rfl) ⟨1224321, by rfl⟩ : syracuseStep 3264857 = 2448643) B2448643
theorem B3871115 : Blo 1719060 3871115 := bstep (se 1 (by rfl) ⟨2903336, by rfl⟩ : syracuseStep 3871115 = 5806673) B5806673
theorem B3871169 : Blo 1719060 3871169 := bstep (se 2 (by rfl) ⟨1451688, by rfl⟩ : syracuseStep 3871169 = 2903377) B2903377
theorem B2650585 : Blo 1719060 2650585 := bstep (se 2 (by rfl) ⟨993969, by rfl⟩ : syracuseStep 2650585 = 1987939) B1987939
theorem B5804567 : Blo 1719060 5804567 := bstep (se 1 (by rfl) ⟨4353425, by rfl⟩ : syracuseStep 5804567 = 8706851) B8706851
theorem B5231179 : Blo 1719060 5231179 := bstep (se 1 (by rfl) ⟨3923384, by rfl⟩ : syracuseStep 5231179 = 7846769) B7846769
theorem B3871385 : Blo 1719060 3871385 := bstep (se 2 (by rfl) ⟨1451769, by rfl⟩ : syracuseStep 3871385 = 2903539) B2903539
theorem B134124245 : Blo 1719060 134124245 := bstep (se 7 (by rfl) ⟨1571768, by rfl⟩ : syracuseStep 134124245 = 3143537) B3143537
theorem B3265267 : Blo 1719060 3265267 := bstep (se 1 (by rfl) ⟨2448950, by rfl⟩ : syracuseStep 3265267 = 4897901) B4897901
theorem B3871475 : Blo 1719060 3871475 := bstep (se 1 (by rfl) ⟨2903606, by rfl⟩ : syracuseStep 3871475 = 5807213) B5807213
theorem B6533891 : Blo 1719060 6533891 := bstep (se 1 (by rfl) ⟨4900418, by rfl⟩ : syracuseStep 6533891 = 9800837) B9800837
theorem B6533905 : Blo 1719060 6533905 := bstep (se 2 (by rfl) ⟨2450214, by rfl⟩ : syracuseStep 6533905 = 4900429) B4900429
theorem B3871511 : Blo 1719060 3871511 := bstep (se 1 (by rfl) ⟨2903633, by rfl⟩ : syracuseStep 3871511 = 5807267) B5807267
theorem B3871691 : Blo 1719060 3871691 := bstep (se 1 (by rfl) ⟨2903768, by rfl⟩ : syracuseStep 3871691 = 5807537) B5807537
theorem B3724289 : Blo 1719060 3724289 := bstep (se 2 (by rfl) ⟨1396608, by rfl⟩ : syracuseStep 3724289 = 2793217) B2793217
theorem B3871745 : Blo 1719060 3871745 := bstep (se 2 (by rfl) ⟨1451904, by rfl⟩ : syracuseStep 3871745 = 2903809) B2903809
theorem B8705069 : Blo 1719060 8705069 := bstep (se 3 (by rfl) ⟨1632200, by rfl⟩ : syracuseStep 8705069 = 3264401) B3264401
theorem B5805107 : Blo 1719060 5805107 := bstep (se 1 (by rfl) ⟨4353830, by rfl⟩ : syracuseStep 5805107 = 8707661) B8707661
theorem B6534209 : Blo 1719060 6534209 := bstep (se 2 (by rfl) ⟨2450328, by rfl⟩ : syracuseStep 6534209 = 4900657) B4900657
theorem B2176075 : Blo 1719060 2176075 := bstep (se 1 (by rfl) ⟨1632056, by rfl⟩ : syracuseStep 2176075 = 3264113) B3264113
theorem B4355147 : Blo 1719060 4355147 := bstep (se 1 (by rfl) ⟨3266360, by rfl⟩ : syracuseStep 4355147 = 6532721) B6532721
theorem B8262749 : Blo 1719060 8262749 := bstep (se 3 (by rfl) ⟨1549265, by rfl⟩ : syracuseStep 8262749 = 3098531) B3098531
theorem B6198403 : Blo 1719060 6198403 := bstep (se 1 (by rfl) ⟨4648802, by rfl⟩ : syracuseStep 6198403 = 9297605) B9297605
theorem B3265753 : Blo 1719060 3265753 := bstep (se 2 (by rfl) ⟨1224657, by rfl⟩ : syracuseStep 3265753 = 2449315) B2449315
theorem B3871961 : Blo 1719060 3871961 := bstep (se 2 (by rfl) ⟨1451985, by rfl⟩ : syracuseStep 3871961 = 2903971) B2903971
theorem B3872051 : Blo 1719060 3872051 := bstep (se 1 (by rfl) ⟨2904038, by rfl⟩ : syracuseStep 3872051 = 5808077) B5808077
theorem B4191539 : Blo 1719060 4191539 := bstep (se 1 (by rfl) ⟨3143654, by rfl⟩ : syracuseStep 4191539 = 6287309) B6287309
theorem B5805377 : Blo 1719060 5805377 := bstep (se 2 (by rfl) ⟨2177016, by rfl⟩ : syracuseStep 5805377 = 4354033) B4354033
theorem B3872087 : Blo 1719060 3872087 := bstep (se 1 (by rfl) ⟨2904065, by rfl⟩ : syracuseStep 3872087 = 5808131) B5808131
theorem B3872267 : Blo 1719060 3872267 := bstep (se 1 (by rfl) ⟨2904200, by rfl⟩ : syracuseStep 3872267 = 5808401) B5808401
theorem B13948481 : Blo 1719060 13948481 := bstep (se 2 (by rfl) ⟨5230680, by rfl⟩ : syracuseStep 13948481 = 10461361) B10461361
theorem B3872321 : Blo 1719060 3872321 := bstep (se 2 (by rfl) ⟨1452120, by rfl⟩ : syracuseStep 3872321 = 2904241) B2904241
theorem B6198877 : Blo 1719060 6198877 := bstep (se 3 (by rfl) ⟨1162289, by rfl⟩ : syracuseStep 6198877 = 2324579) B2324579
theorem B19863245 : Blo 1719060 19863245 := bstep (se 3 (by rfl) ⟨3724358, by rfl⟩ : syracuseStep 19863245 = 7448717) B7448717
theorem B3266315 : Blo 1719060 3266315 := bstep (se 1 (by rfl) ⟨2449736, by rfl⟩ : syracuseStep 3266315 = 4899473) B4899473
theorem B14702381 : Blo 1719060 14702381 := bstep (se 3 (by rfl) ⟨2756696, by rfl⟩ : syracuseStep 14702381 = 5513393) B5513393
theorem B5805917 : Blo 1719060 5805917 := bstep (se 3 (by rfl) ⟨1088609, by rfl⟩ : syracuseStep 5805917 = 2177219) B2177219
theorem B3921779 : Blo 1719060 3921779 := bstep (se 1 (by rfl) ⟨2941334, by rfl⟩ : syracuseStep 3921779 = 5882669) B5882669
theorem B7346065 : Blo 1719060 7346065 := bstep (se 2 (by rfl) ⟨2754774, by rfl⟩ : syracuseStep 7346065 = 5509549) B5509549
theorem B3266497 : Blo 1719060 3266497 := bstep (se 2 (by rfl) ⟨1224936, by rfl⟩ : syracuseStep 3266497 = 2449873) B2449873
theorem B2177047 : Blo 1719060 2177047 := bstep (se 1 (by rfl) ⟨1632785, by rfl⟩ : syracuseStep 2177047 = 3265571) B3265571
theorem B4356119 : Blo 1719060 4356119 := bstep (se 1 (by rfl) ⟨3267089, by rfl⟩ : syracuseStep 4356119 = 6534179) B6534179
theorem B2578649 : Blo 1719060 2578649 := bstep (se 2 (by rfl) ⟨966993, by rfl⟩ : syracuseStep 2578649 = 1933987) B1933987
theorem B2578763 : Blo 1719060 2578763 := bstep (se 1 (by rfl) ⟨1934072, by rfl⟩ : syracuseStep 2578763 = 3868145) B3868145
theorem B2578775 : Blo 1719060 2578775 := bstep (se 1 (by rfl) ⟨1934081, by rfl⟩ : syracuseStep 2578775 = 3868163) B3868163
theorem B14686595 : Blo 1719060 14686595 := bstep (se 1 (by rfl) ⟨11014946, by rfl⟩ : syracuseStep 14686595 = 22029893) B22029893
theorem B2578841 : Blo 1719060 2578841 := bstep (se 2 (by rfl) ⟨967065, by rfl⟩ : syracuseStep 2578841 = 1934131) B1934131
theorem B6527405 : Blo 1719060 6527405 := bstep (se 3 (by rfl) ⟨1223888, by rfl⟩ : syracuseStep 6527405 = 2447777) B2447777
theorem B2578955 : Blo 1719060 2578955 := bstep (se 1 (by rfl) ⟨1934216, by rfl⟩ : syracuseStep 2578955 = 3868433) B3868433
theorem B27884045 : Blo 1719060 27884045 := bstep (se 3 (by rfl) ⟨5228258, by rfl⟩ : syracuseStep 27884045 = 10456517) B10456517
theorem B2578967 : Blo 1719060 2578967 := bstep (se 1 (by rfl) ⟨1934225, by rfl⟩ : syracuseStep 2578967 = 3868451) B3868451
theorem B4897331 : Blo 1719060 4897331 := bstep (se 1 (by rfl) ⟨3672998, by rfl⟩ : syracuseStep 4897331 = 7345997) B7345997
theorem B2579033 : Blo 1719060 2579033 := bstep (se 2 (by rfl) ⟨967137, by rfl⟩ : syracuseStep 2579033 = 1934275) B1934275
theorem B15686237 : Blo 1719060 15686237 := bstep (se 3 (by rfl) ⟨2941169, by rfl⟩ : syracuseStep 15686237 = 5882339) B5882339
theorem B3267211 : Blo 1719060 3267211 := bstep (se 1 (by rfl) ⟨2450408, by rfl⟩ : syracuseStep 3267211 = 4900817) B4900817
theorem B2579147 : Blo 1719060 2579147 := bstep (se 1 (by rfl) ⟨1934360, by rfl⟩ : syracuseStep 2579147 = 3868721) B3868721
theorem B2579159 : Blo 1719060 2579159 := bstep (se 1 (by rfl) ⟨1934369, by rfl⟩ : syracuseStep 2579159 = 3868739) B3868739
theorem B3267287 : Blo 1719060 3267287 := bstep (se 1 (by rfl) ⟨2450465, by rfl⟩ : syracuseStep 3267287 = 4900931) B4900931
theorem B1719063 : Blo 1719060 1719063 := bstep (se 1 (by rfl) ⟨1289297, by rfl⟩ : syracuseStep 1719063 = 2578595) B2578595
theorem B4897559 : Blo 1719060 4897559 := bstep (se 1 (by rfl) ⟨3673169, by rfl⟩ : syracuseStep 4897559 = 7346339) B7346339
theorem B2579225 : Blo 1719060 2579225 := bstep (se 2 (by rfl) ⟨967209, by rfl⟩ : syracuseStep 2579225 = 1934419) B1934419
theorem B2325271 : Blo 1719060 2325271 := bstep (se 1 (by rfl) ⟨1743953, by rfl⟩ : syracuseStep 2325271 = 3487907) B3487907
theorem B5511959 : Blo 1719060 5511959 := bstep (se 1 (by rfl) ⟨4133969, by rfl⟩ : syracuseStep 5511959 = 8267939) B8267939
theorem B1719083 : Blo 1719060 1719083 := bstep (se 1 (by rfl) ⟨1289312, by rfl⟩ : syracuseStep 1719083 = 2578625) B2578625
theorem B1719095 : Blo 1719060 1719095 := bstep (se 1 (by rfl) ⟨1289321, by rfl⟩ : syracuseStep 1719095 = 2578643) B2578643
theorem B1719115 : Blo 1719060 1719115 := bstep (se 1 (by rfl) ⟨1289336, by rfl⟩ : syracuseStep 1719115 = 2578673) B2578673
theorem B2177867 : Blo 1719060 2177867 := bstep (se 1 (by rfl) ⟨1633400, by rfl⟩ : syracuseStep 2177867 = 3266801) B3266801
theorem B1719127 : Blo 1719060 1719127 := bstep (se 1 (by rfl) ⟨1289345, by rfl⟩ : syracuseStep 1719127 = 2578691) B2578691
theorem B1719147 : Blo 1719060 1719147 := bstep (se 1 (by rfl) ⟨1289360, by rfl⟩ : syracuseStep 1719147 = 2578721) B2578721
theorem B1719159 : Blo 1719060 1719159 := bstep (se 1 (by rfl) ⟨1289369, by rfl⟩ : syracuseStep 1719159 = 2578739) B2578739
theorem B15686531 : Blo 1719060 15686531 := bstep (se 1 (by rfl) ⟨11764898, by rfl⟩ : syracuseStep 15686531 = 23529797) B23529797
theorem B1719179 : Blo 1719060 1719179 := bstep (se 1 (by rfl) ⟨1289384, by rfl⟩ : syracuseStep 1719179 = 2578769) B2578769
theorem B2579339 : Blo 1719060 2579339 := bstep (se 1 (by rfl) ⟨1934504, by rfl⟩ : syracuseStep 2579339 = 3869009) B3869009
theorem B1719191 : Blo 1719060 1719191 := bstep (se 1 (by rfl) ⟨1289393, by rfl⟩ : syracuseStep 1719191 = 2578787) B2578787
theorem B2579351 : Blo 1719060 2579351 := bstep (se 1 (by rfl) ⟨1934513, by rfl⟩ : syracuseStep 2579351 = 3869027) B3869027
theorem B1719211 : Blo 1719060 1719211 := bstep (se 1 (by rfl) ⟨1289408, by rfl⟩ : syracuseStep 1719211 = 2578817) B2578817
theorem B13065137 : Blo 1719060 13065137 := bstep (se 2 (by rfl) ⟨4899426, by rfl⟩ : syracuseStep 13065137 = 9798853) B9798853
theorem B1719223 : Blo 1719060 1719223 := bstep (se 1 (by rfl) ⟨1289417, by rfl⟩ : syracuseStep 1719223 = 2578835) B2578835
theorem B1719243 : Blo 1719060 1719243 := bstep (se 1 (by rfl) ⟨1289432, by rfl⟩ : syracuseStep 1719243 = 2578865) B2578865
theorem B5807051 : Blo 1719060 5807051 := bstep (se 1 (by rfl) ⟨4355288, by rfl⟩ : syracuseStep 5807051 = 8710577) B8710577
theorem B1719255 : Blo 1719060 1719255 := bstep (se 1 (by rfl) ⟨1289441, by rfl⟩ : syracuseStep 1719255 = 2578883) B2578883
theorem B7445465 : Blo 1719060 7445465 := bstep (se 2 (by rfl) ⟨2792049, by rfl⟩ : syracuseStep 7445465 = 5584099) B5584099
theorem B2579417 : Blo 1719060 2579417 := bstep (se 2 (by rfl) ⟨967281, by rfl⟩ : syracuseStep 2579417 = 1934563) B1934563
theorem B1719275 : Blo 1719060 1719275 := bstep (se 1 (by rfl) ⟨1289456, by rfl⟩ : syracuseStep 1719275 = 2578913) B2578913
theorem B1719287 : Blo 1719060 1719287 := bstep (se 1 (by rfl) ⟨1289465, by rfl⟩ : syracuseStep 1719287 = 2578931) B2578931
theorem B1719307 : Blo 1719060 1719307 := bstep (se 1 (by rfl) ⟨1289480, by rfl⟩ : syracuseStep 1719307 = 2578961) B2578961
theorem B1719319 : Blo 1719060 1719319 := bstep (se 1 (by rfl) ⟨1289489, by rfl⟩ : syracuseStep 1719319 = 2578979) B2578979
theorem B1719339 : Blo 1719060 1719339 := bstep (se 1 (by rfl) ⟨1289504, by rfl⟩ : syracuseStep 1719339 = 2579009) B2579009
theorem B1719351 : Blo 1719060 1719351 := bstep (se 1 (by rfl) ⟨1289513, by rfl⟩ : syracuseStep 1719351 = 2579027) B2579027
theorem B1719371 : Blo 1719060 1719371 := bstep (se 1 (by rfl) ⟨1289528, by rfl⟩ : syracuseStep 1719371 = 2579057) B2579057
theorem B2579531 : Blo 1719060 2579531 := bstep (se 1 (by rfl) ⟨1934648, by rfl⟩ : syracuseStep 2579531 = 3869297) B3869297
theorem B4897867 : Blo 1719060 4897867 := bstep (se 1 (by rfl) ⟨3673400, by rfl⟩ : syracuseStep 4897867 = 7346801) B7346801
theorem B1719383 : Blo 1719060 1719383 := bstep (se 1 (by rfl) ⟨1289537, by rfl⟩ : syracuseStep 1719383 = 2579075) B2579075
theorem B2579543 : Blo 1719060 2579543 := bstep (se 1 (by rfl) ⟨1934657, by rfl⟩ : syracuseStep 2579543 = 3869315) B3869315
theorem B1719403 : Blo 1719060 1719403 := bstep (se 1 (by rfl) ⟨1289552, by rfl⟩ : syracuseStep 1719403 = 2579105) B2579105
theorem B1719415 : Blo 1719060 1719415 := bstep (se 1 (by rfl) ⟨1289561, by rfl⟩ : syracuseStep 1719415 = 2579123) B2579123
theorem B1719435 : Blo 1719060 1719435 := bstep (se 1 (by rfl) ⟨1289576, by rfl⟩ : syracuseStep 1719435 = 2579153) B2579153
theorem B1719447 : Blo 1719060 1719447 := bstep (se 1 (by rfl) ⟨1289585, by rfl⟩ : syracuseStep 1719447 = 2579171) B2579171
theorem B2579609 : Blo 1719060 2579609 := bstep (se 2 (by rfl) ⟨967353, by rfl⟩ : syracuseStep 2579609 = 1934707) B1934707
theorem B1719467 : Blo 1719060 1719467 := bstep (se 1 (by rfl) ⟨1289600, by rfl⟩ : syracuseStep 1719467 = 2579201) B2579201
theorem B1719479 : Blo 1719060 1719479 := bstep (se 1 (by rfl) ⟨1289609, by rfl⟩ : syracuseStep 1719479 = 2579219) B2579219
theorem B1719499 : Blo 1719060 1719499 := bstep (se 1 (by rfl) ⟨1289624, by rfl⟩ : syracuseStep 1719499 = 2579249) B2579249
theorem B1719511 : Blo 1719060 1719511 := bstep (se 1 (by rfl) ⟨1289633, by rfl⟩ : syracuseStep 1719511 = 2579267) B2579267
theorem B5807321 : Blo 1719060 5807321 := bstep (se 2 (by rfl) ⟨2177745, by rfl⟩ : syracuseStep 5807321 = 4355491) B4355491
theorem B1719531 : Blo 1719060 1719531 := bstep (se 1 (by rfl) ⟨1289648, by rfl⟩ : syracuseStep 1719531 = 2579297) B2579297
theorem B1719543 : Blo 1719060 1719543 := bstep (se 1 (by rfl) ⟨1289657, by rfl⟩ : syracuseStep 1719543 = 2579315) B2579315
theorem B1719563 : Blo 1719060 1719563 := bstep (se 1 (by rfl) ⟨1289672, by rfl⟩ : syracuseStep 1719563 = 2579345) B2579345
theorem B2579723 : Blo 1719060 2579723 := bstep (se 1 (by rfl) ⟨1934792, by rfl⟩ : syracuseStep 2579723 = 3869585) B3869585
theorem B8822033 : Blo 1719060 8822033 := bstep (se 2 (by rfl) ⟨3308262, by rfl⟩ : syracuseStep 8822033 = 6616525) B6616525
theorem B1719575 : Blo 1719060 1719575 := bstep (se 1 (by rfl) ⟨1289681, by rfl⟩ : syracuseStep 1719575 = 2579363) B2579363
theorem B2579735 : Blo 1719060 2579735 := bstep (se 1 (by rfl) ⟨1934801, by rfl⟩ : syracuseStep 2579735 = 3869603) B3869603
theorem B1719595 : Blo 1719060 1719595 := bstep (se 1 (by rfl) ⟨1289696, by rfl⟩ : syracuseStep 1719595 = 2579393) B2579393
theorem B1719607 : Blo 1719060 1719607 := bstep (se 1 (by rfl) ⟨1289705, by rfl⟩ : syracuseStep 1719607 = 2579411) B2579411
theorem B1719627 : Blo 1719060 1719627 := bstep (se 1 (by rfl) ⟨1289720, by rfl⟩ : syracuseStep 1719627 = 2579441) B2579441
theorem B1719639 : Blo 1719060 1719639 := bstep (se 1 (by rfl) ⟨1289729, by rfl⟩ : syracuseStep 1719639 = 2579459) B2579459
theorem B2579801 : Blo 1719060 2579801 := bstep (se 2 (by rfl) ⟨967425, by rfl⟩ : syracuseStep 2579801 = 1934851) B1934851
theorem B4898141 : Blo 1719060 4898141 := bstep (se 3 (by rfl) ⟨918401, by rfl⟩ : syracuseStep 4898141 = 1836803) B1836803
theorem B1719659 : Blo 1719060 1719659 := bstep (se 1 (by rfl) ⟨1289744, by rfl⟩ : syracuseStep 1719659 = 2579489) B2579489
theorem B1719671 : Blo 1719060 1719671 := bstep (se 1 (by rfl) ⟨1289753, by rfl⟩ : syracuseStep 1719671 = 2579507) B2579507
theorem B1719691 : Blo 1719060 1719691 := bstep (se 1 (by rfl) ⟨1289768, by rfl⟩ : syracuseStep 1719691 = 2579537) B2579537
theorem B1719703 : Blo 1719060 1719703 := bstep (se 1 (by rfl) ⟨1289777, by rfl⟩ : syracuseStep 1719703 = 2579555) B2579555
theorem B13065623 : Blo 1719060 13065623 := bstep (se 1 (by rfl) ⟨9799217, by rfl⟩ : syracuseStep 13065623 = 19598435) B19598435
theorem B1719723 : Blo 1719060 1719723 := bstep (se 1 (by rfl) ⟨1289792, by rfl⟩ : syracuseStep 1719723 = 2579585) B2579585
theorem B1719735 : Blo 1719060 1719735 := bstep (se 1 (by rfl) ⟨1289801, by rfl⟩ : syracuseStep 1719735 = 2579603) B2579603
theorem B1719755 : Blo 1719060 1719755 := bstep (se 1 (by rfl) ⟨1289816, by rfl⟩ : syracuseStep 1719755 = 2579633) B2579633
theorem B2579915 : Blo 1719060 2579915 := bstep (se 1 (by rfl) ⟨1934936, by rfl⟩ : syracuseStep 2579915 = 3869873) B3869873
theorem B1719767 : Blo 1719060 1719767 := bstep (se 1 (by rfl) ⟨1289825, by rfl⟩ : syracuseStep 1719767 = 2579651) B2579651
theorem B2579927 : Blo 1719060 2579927 := bstep (se 1 (by rfl) ⟨1934945, by rfl⟩ : syracuseStep 2579927 = 3869891) B3869891
theorem B1719787 : Blo 1719060 1719787 := bstep (se 1 (by rfl) ⟨1289840, by rfl⟩ : syracuseStep 1719787 = 2579681) B2579681
theorem B1719799 : Blo 1719060 1719799 := bstep (se 1 (by rfl) ⟨1289849, by rfl⟩ : syracuseStep 1719799 = 2579699) B2579699
theorem B1719819 : Blo 1719060 1719819 := bstep (se 1 (by rfl) ⟨1289864, by rfl⟩ : syracuseStep 1719819 = 2579729) B2579729
theorem B1719831 : Blo 1719060 1719831 := bstep (se 1 (by rfl) ⟨1289873, by rfl⟩ : syracuseStep 1719831 = 2579747) B2579747
theorem B2579993 : Blo 1719060 2579993 := bstep (se 2 (by rfl) ⟨967497, by rfl⟩ : syracuseStep 2579993 = 1934995) B1934995
theorem B1719851 : Blo 1719060 1719851 := bstep (se 1 (by rfl) ⟨1289888, by rfl⟩ : syracuseStep 1719851 = 2579777) B2579777
theorem B1719863 : Blo 1719060 1719863 := bstep (se 1 (by rfl) ⟨1289897, by rfl⟩ : syracuseStep 1719863 = 2579795) B2579795
theorem B1719883 : Blo 1719060 1719883 := bstep (se 1 (by rfl) ⟨1289912, by rfl⟩ : syracuseStep 1719883 = 2579825) B2579825
theorem B1719895 : Blo 1719060 1719895 := bstep (se 1 (by rfl) ⟨1289921, by rfl⟩ : syracuseStep 1719895 = 2579843) B2579843
theorem B9797213 : Blo 1719060 9797213 := bstep (se 3 (by rfl) ⟨1836977, by rfl⟩ : syracuseStep 9797213 = 3673955) B3673955
theorem B1719915 : Blo 1719060 1719915 := bstep (se 1 (by rfl) ⟨1289936, by rfl⟩ : syracuseStep 1719915 = 2579873) B2579873
theorem B1719927 : Blo 1719060 1719927 := bstep (se 1 (by rfl) ⟨1289945, by rfl⟩ : syracuseStep 1719927 = 2579891) B2579891
theorem B1719947 : Blo 1719060 1719947 := bstep (se 1 (by rfl) ⟨1289960, by rfl⟩ : syracuseStep 1719947 = 2579921) B2579921
theorem B2580107 : Blo 1719060 2580107 := bstep (se 1 (by rfl) ⟨1935080, by rfl⟩ : syracuseStep 2580107 = 3870161) B3870161
theorem B1719959 : Blo 1719060 1719959 := bstep (se 1 (by rfl) ⟨1289969, by rfl⟩ : syracuseStep 1719959 = 2579939) B2579939
theorem B2580119 : Blo 1719060 2580119 := bstep (se 1 (by rfl) ⟨1935089, by rfl⟩ : syracuseStep 2580119 = 3870179) B3870179
theorem B1719979 : Blo 1719060 1719979 := bstep (se 1 (by rfl) ⟨1289984, by rfl⟩ : syracuseStep 1719979 = 2579969) B2579969
theorem B6201011 : Blo 1719060 6201011 := bstep (se 1 (by rfl) ⟨4650758, by rfl⟩ : syracuseStep 6201011 = 9301517) B9301517
theorem B1719991 : Blo 1719060 1719991 := bstep (se 1 (by rfl) ⟨1289993, by rfl⟩ : syracuseStep 1719991 = 2579987) B2579987
theorem B1720011 : Blo 1719060 1720011 := bstep (se 1 (by rfl) ⟨1290008, by rfl⟩ : syracuseStep 1720011 = 2580017) B2580017
theorem B1720023 : Blo 1719060 1720023 := bstep (se 1 (by rfl) ⟨1290017, by rfl⟩ : syracuseStep 1720023 = 2580035) B2580035
theorem B9297625 : Blo 1719060 9297625 := bstep (se 2 (by rfl) ⟨3486609, by rfl⟩ : syracuseStep 9297625 = 6973219) B6973219
theorem B2580185 : Blo 1719060 2580185 := bstep (se 2 (by rfl) ⟨967569, by rfl⟩ : syracuseStep 2580185 = 1935139) B1935139
theorem B1720043 : Blo 1719060 1720043 := bstep (se 1 (by rfl) ⟨1290032, by rfl⟩ : syracuseStep 1720043 = 2580065) B2580065
theorem B1720055 : Blo 1719060 1720055 := bstep (se 1 (by rfl) ⟨1290041, by rfl⟩ : syracuseStep 1720055 = 2580083) B2580083
theorem B1720075 : Blo 1719060 1720075 := bstep (se 1 (by rfl) ⟨1290056, by rfl⟩ : syracuseStep 1720075 = 2580113) B2580113
theorem B1720087 : Blo 1719060 1720087 := bstep (se 1 (by rfl) ⟨1290065, by rfl⟩ : syracuseStep 1720087 = 2580131) B2580131
theorem B1720107 : Blo 1719060 1720107 := bstep (se 1 (by rfl) ⟨1290080, by rfl⟩ : syracuseStep 1720107 = 2580161) B2580161
theorem B1720119 : Blo 1719060 1720119 := bstep (se 1 (by rfl) ⟨1290089, by rfl⟩ : syracuseStep 1720119 = 2580179) B2580179
theorem B6528833 : Blo 1719060 6528833 := bstep (se 2 (by rfl) ⟨2448312, by rfl⟩ : syracuseStep 6528833 = 4896625) B4896625
theorem B1720139 : Blo 1719060 1720139 := bstep (se 1 (by rfl) ⟨1290104, by rfl⟩ : syracuseStep 1720139 = 2580209) B2580209
theorem B2580299 : Blo 1719060 2580299 := bstep (se 1 (by rfl) ⟨1935224, by rfl⟩ : syracuseStep 2580299 = 3870449) B3870449
theorem B5513035 : Blo 1719060 5513035 := bstep (se 1 (by rfl) ⟨4134776, by rfl⟩ : syracuseStep 5513035 = 8269553) B8269553
theorem B1720151 : Blo 1719060 1720151 := bstep (se 1 (by rfl) ⟨1290113, by rfl⟩ : syracuseStep 1720151 = 2580227) B2580227
theorem B2580311 : Blo 1719060 2580311 := bstep (se 1 (by rfl) ⟨1935233, by rfl⟩ : syracuseStep 2580311 = 3870467) B3870467
theorem B1720171 : Blo 1719060 1720171 := bstep (se 1 (by rfl) ⟨1290128, by rfl⟩ : syracuseStep 1720171 = 2580257) B2580257
theorem B1720183 : Blo 1719060 1720183 := bstep (se 1 (by rfl) ⟨1290137, by rfl⟩ : syracuseStep 1720183 = 2580275) B2580275
theorem B1720203 : Blo 1719060 1720203 := bstep (se 1 (by rfl) ⟨1290152, by rfl⟩ : syracuseStep 1720203 = 2580305) B2580305
theorem B1720215 : Blo 1719060 1720215 := bstep (se 1 (by rfl) ⟨1290161, by rfl⟩ : syracuseStep 1720215 = 2580323) B2580323
theorem B5808023 : Blo 1719060 5808023 := bstep (se 1 (by rfl) ⟨4356017, by rfl⟩ : syracuseStep 5808023 = 8712035) B8712035
theorem B2580377 : Blo 1719060 2580377 := bstep (se 2 (by rfl) ⟨967641, by rfl⟩ : syracuseStep 2580377 = 1935283) B1935283
theorem B1720235 : Blo 1719060 1720235 := bstep (se 1 (by rfl) ⟨1290176, by rfl⟩ : syracuseStep 1720235 = 2580353) B2580353
theorem B1720247 : Blo 1719060 1720247 := bstep (se 1 (by rfl) ⟨1290185, by rfl⟩ : syracuseStep 1720247 = 2580371) B2580371
theorem B1720267 : Blo 1719060 1720267 := bstep (se 1 (by rfl) ⟨1290200, by rfl⟩ : syracuseStep 1720267 = 2580401) B2580401
theorem B1720279 : Blo 1719060 1720279 := bstep (se 1 (by rfl) ⟨1290209, by rfl⟩ : syracuseStep 1720279 = 2580419) B2580419
theorem B5513177 : Blo 1719060 5513177 := bstep (se 2 (by rfl) ⟨2067441, by rfl⟩ : syracuseStep 5513177 = 4134883) B4134883
theorem B1720299 : Blo 1719060 1720299 := bstep (se 1 (by rfl) ⟨1290224, by rfl⟩ : syracuseStep 1720299 = 2580449) B2580449
theorem B1720311 : Blo 1719060 1720311 := bstep (se 1 (by rfl) ⟨1290233, by rfl⟩ : syracuseStep 1720311 = 2580467) B2580467
theorem B1720327 : Blo 1719060 1720327 := bstep (se 1 (by rfl) ⟨1290245, by rfl⟩ : syracuseStep 1720327 = 2580491) B2580491
theorem B1720335 : Blo 1719060 1720335 := bstep (se 1 (by rfl) ⟨1290251, by rfl⟩ : syracuseStep 1720335 = 2580503) B2580503
theorem B6971435 : Blo 1719060 6971435 := bstep (se 1 (by rfl) ⟨5228576, by rfl⟩ : syracuseStep 6971435 = 10457153) B10457153
theorem B2580539 : Blo 1719060 2580539 := bstep (se 1 (by rfl) ⟨1935404, by rfl⟩ : syracuseStep 2580539 = 3870809) B3870809
theorem B1720379 : Blo 1719060 1720379 := bstep (se 1 (by rfl) ⟨1290284, by rfl⟩ : syracuseStep 1720379 = 2580569) B2580569
theorem B2580599 : Blo 1719060 2580599 := bstep (se 1 (by rfl) ⟨1935449, by rfl⟩ : syracuseStep 2580599 = 3870899) B3870899
theorem B2449543 : Blo 1719060 2449543 := bstep (se 1 (by rfl) ⟨1837157, by rfl⟩ : syracuseStep 2449543 = 3674315) B3674315
theorem B1720455 : Blo 1719060 1720455 := bstep (se 1 (by rfl) ⟨1290341, by rfl⟩ : syracuseStep 1720455 = 2580683) B2580683
theorem B2580623 : Blo 1719060 2580623 := bstep (se 1 (by rfl) ⟨1935467, by rfl⟩ : syracuseStep 2580623 = 3870935) B3870935
theorem B1720463 : Blo 1719060 1720463 := bstep (se 1 (by rfl) ⟨1290347, by rfl⟩ : syracuseStep 1720463 = 2580695) B2580695
theorem B2580665 : Blo 1719060 2580665 := bstep (se 2 (by rfl) ⟨967749, by rfl⟩ : syracuseStep 2580665 = 1935499) B1935499
theorem B1720507 : Blo 1719060 1720507 := bstep (se 1 (by rfl) ⟨1290380, by rfl⟩ : syracuseStep 1720507 = 2580761) B2580761
theorem B4899017 : Blo 1719060 4899017 := bstep (se 2 (by rfl) ⟨1837131, by rfl⟩ : syracuseStep 4899017 = 3674263) B3674263
theorem B4964609 : Blo 1719060 4964609 := bstep (se 2 (by rfl) ⟨1861728, by rfl⟩ : syracuseStep 4964609 = 3723457) B3723457
theorem B2580743 : Blo 1719060 2580743 := bstep (se 1 (by rfl) ⟨1935557, by rfl⟩ : syracuseStep 2580743 = 3871115) B3871115
theorem B1720583 : Blo 1719060 1720583 := bstep (se 1 (by rfl) ⟨1290437, by rfl⟩ : syracuseStep 1720583 = 2580875) B2580875
theorem B1720591 : Blo 1719060 1720591 := bstep (se 1 (by rfl) ⟨1290443, by rfl⟩ : syracuseStep 1720591 = 2580887) B2580887
theorem B9797921 : Blo 1719060 9797921 := bstep (se 2 (by rfl) ⟨3674220, by rfl⟩ : syracuseStep 9797921 = 7348441) B7348441
theorem B2580779 : Blo 1719060 2580779 := bstep (se 1 (by rfl) ⟨1935584, by rfl⟩ : syracuseStep 2580779 = 3871169) B3871169
theorem B1720635 : Blo 1719060 1720635 := bstep (se 1 (by rfl) ⟨1290476, by rfl⟩ : syracuseStep 1720635 = 2580953) B2580953
theorem B2580809 : Blo 1719060 2580809 := bstep (se 2 (by rfl) ⟨967803, by rfl⟩ : syracuseStep 2580809 = 1935607) B1935607
theorem B1720711 : Blo 1719060 1720711 := bstep (se 1 (by rfl) ⟨1290533, by rfl⟩ : syracuseStep 1720711 = 2581067) B2581067
theorem B1720719 : Blo 1719060 1720719 := bstep (se 1 (by rfl) ⟨1290539, by rfl⟩ : syracuseStep 1720719 = 2581079) B2581079
theorem B29802899 : Blo 1719060 29802899 := bstep (se 1 (by rfl) ⟨22352174, by rfl⟩ : syracuseStep 29802899 = 44704349) B44704349
theorem B2580923 : Blo 1719060 2580923 := bstep (se 1 (by rfl) ⟨1935692, by rfl⟩ : syracuseStep 2580923 = 3871385) B3871385
theorem B1720763 : Blo 1719060 1720763 := bstep (se 1 (by rfl) ⟨1290572, by rfl⟩ : syracuseStep 1720763 = 2581145) B2581145
theorem B89416163 : Blo 1719060 89416163 := bstep (se 1 (by rfl) ⟨67062122, by rfl⟩ : syracuseStep 89416163 = 134124245) B134124245
theorem B2580983 : Blo 1719060 2580983 := bstep (se 1 (by rfl) ⟨1935737, by rfl⟩ : syracuseStep 2580983 = 3871475) B3871475
theorem B1720839 : Blo 1719060 1720839 := bstep (se 1 (by rfl) ⟨1290629, by rfl⟩ : syracuseStep 1720839 = 2581259) B2581259
theorem B2581007 : Blo 1719060 2581007 := bstep (se 1 (by rfl) ⟨1935755, by rfl⟩ : syracuseStep 2581007 = 3871511) B3871511
theorem B1720847 : Blo 1719060 1720847 := bstep (se 1 (by rfl) ⟨1290635, by rfl⟩ : syracuseStep 1720847 = 2581271) B2581271
theorem B7348765 : Blo 1719060 7348765 := bstep (se 3 (by rfl) ⟨1377893, by rfl⟩ : syracuseStep 7348765 = 2755787) B2755787
theorem B2581049 : Blo 1719060 2581049 := bstep (se 2 (by rfl) ⟨967893, by rfl⟩ : syracuseStep 2581049 = 1935787) B1935787
theorem B1720891 : Blo 1719060 1720891 := bstep (se 1 (by rfl) ⟨1290668, by rfl⟩ : syracuseStep 1720891 = 2581337) B2581337
theorem B2581127 : Blo 1719060 2581127 := bstep (se 1 (by rfl) ⟨1935845, by rfl⟩ : syracuseStep 2581127 = 3871691) B3871691
theorem B1720967 : Blo 1719060 1720967 := bstep (se 1 (by rfl) ⟨1290725, by rfl⟩ : syracuseStep 1720967 = 2581451) B2581451
theorem B1720975 : Blo 1719060 1720975 := bstep (se 1 (by rfl) ⟨1290731, by rfl⟩ : syracuseStep 1720975 = 2581463) B2581463
theorem B2482859 : Blo 1719060 2482859 := bstep (se 1 (by rfl) ⟨1862144, by rfl⟩ : syracuseStep 2482859 = 3724289) B3724289
theorem B2581163 : Blo 1719060 2581163 := bstep (se 1 (by rfl) ⟨1935872, by rfl⟩ : syracuseStep 2581163 = 3871745) B3871745
theorem B1721019 : Blo 1719060 1721019 := bstep (se 1 (by rfl) ⟨1290764, by rfl⟩ : syracuseStep 1721019 = 2581529) B2581529
theorem B2581193 : Blo 1719060 2581193 := bstep (se 2 (by rfl) ⟨967947, by rfl⟩ : syracuseStep 2581193 = 1935895) B1935895
theorem B1934095 : Blo 1719060 1934095 := bstep (se 1 (by rfl) ⟨1450571, by rfl⟩ : syracuseStep 1934095 = 2901143) B2901143
theorem B4899599 : Blo 1719060 4899599 := bstep (se 1 (by rfl) ⟨3674699, by rfl⟩ : syracuseStep 4899599 = 7349399) B7349399
theorem B2581307 : Blo 1719060 2581307 := bstep (se 1 (by rfl) ⟨1935980, by rfl⟩ : syracuseStep 2581307 = 3871961) B3871961
theorem B2581367 : Blo 1719060 2581367 := bstep (se 1 (by rfl) ⟨1936025, by rfl⟩ : syracuseStep 2581367 = 3872051) B3872051
theorem B2581391 : Blo 1719060 2581391 := bstep (se 1 (by rfl) ⟨1936043, by rfl⟩ : syracuseStep 2581391 = 3872087) B3872087
theorem B2581433 : Blo 1719060 2581433 := bstep (se 2 (by rfl) ⟨968037, by rfl⟩ : syracuseStep 2581433 = 1936075) B1936075
theorem B2581511 : Blo 1719060 2581511 := bstep (se 1 (by rfl) ⟨1936133, by rfl⟩ : syracuseStep 2581511 = 3872267) B3872267
theorem B2901035 : Blo 1719060 2901035 := bstep (se 1 (by rfl) ⟨2175776, by rfl⟩ : syracuseStep 2901035 = 4351553) B4351553
theorem B2581547 : Blo 1719060 2581547 := bstep (se 1 (by rfl) ⟨1936160, by rfl⟩ : syracuseStep 2581547 = 3872321) B3872321
theorem B2581577 : Blo 1719060 2581577 := bstep (se 2 (by rfl) ⟨968091, by rfl⟩ : syracuseStep 2581577 = 1936183) B1936183
theorem B19588229 : Blo 1719060 19588229 := bstep (se 4 (by rfl) ⟨1836396, by rfl⟩ : syracuseStep 19588229 = 3672793) B3672793
theorem B2614519 : Blo 1719060 2614519 := bstep (se 1 (by rfl) ⟨1960889, by rfl⟩ : syracuseStep 2614519 = 3921779) B3921779
theorem B1934599 : Blo 1719060 1934599 := bstep (se 1 (by rfl) ⟨1450949, by rfl⟩ : syracuseStep 1934599 = 2901899) B2901899
theorem B3867947 : Blo 1719060 3867947 := bstep (se 1 (by rfl) ⟨2900960, by rfl⟩ : syracuseStep 3867947 = 5801921) B5801921
theorem B2901433 : Blo 1719060 2901433 := bstep (se 2 (by rfl) ⟨1088037, by rfl⟩ : syracuseStep 2901433 = 2176075) B2176075
theorem B6530489 : Blo 1719060 6530489 := bstep (se 2 (by rfl) ⟨2448933, by rfl⟩ : syracuseStep 6530489 = 4897867) B4897867
theorem B1934779 : Blo 1719060 1934779 := bstep (se 1 (by rfl) ⟨1451084, by rfl⟩ : syracuseStep 1934779 = 2902169) B2902169
theorem B6284729 : Blo 1719060 6284729 := bstep (se 2 (by rfl) ⟨2356773, by rfl⟩ : syracuseStep 6284729 = 4713547) B4713547
theorem B79455761 : Blo 1719060 79455761 := bstep (se 2 (by rfl) ⟨29795910, by rfl⟩ : syracuseStep 79455761 = 59591821) B59591821
theorem B3098171 : Blo 1719060 3098171 := bstep (se 1 (by rfl) ⟨2323628, by rfl⟩ : syracuseStep 3098171 = 4647257) B4647257
theorem B41829965 : Blo 1719060 41829965 := bstep (se 3 (by rfl) ⟨7843118, by rfl⟩ : syracuseStep 41829965 = 15686237) B15686237
theorem B33064523 : Blo 1719060 33064523 := bstep (se 1 (by rfl) ⟨24798392, by rfl⟩ : syracuseStep 33064523 = 49596785) B49596785
theorem B9791063 : Blo 1719060 9791063 := bstep (se 1 (by rfl) ⟨7343297, by rfl⟩ : syracuseStep 9791063 = 14686595) B14686595
theorem B4351603 : Blo 1719060 4351603 := bstep (se 1 (by rfl) ⟨3263702, by rfl⟩ : syracuseStep 4351603 = 6527405) B6527405
theorem B3868307 : Blo 1719060 3868307 := bstep (se 1 (by rfl) ⟨2901230, by rfl⟩ : syracuseStep 3868307 = 5802461) B5802461
theorem B19596977 : Blo 1719060 19596977 := bstep (se 2 (by rfl) ⟨7348866, by rfl⟩ : syracuseStep 19596977 = 14697733) B14697733
theorem B3868361 : Blo 1719060 3868361 := bstep (se 2 (by rfl) ⟨1450635, by rfl⟩ : syracuseStep 3868361 = 2901271) B2901271
theorem B4351745 : Blo 1719060 4351745 := bstep (se 2 (by rfl) ⟨1631904, by rfl⟩ : syracuseStep 4351745 = 3263809) B3263809
theorem B5228347 : Blo 1719060 5228347 := bstep (se 1 (by rfl) ⟨3921260, by rfl⟩ : syracuseStep 5228347 = 7842521) B7842521
theorem B1935247 : Blo 1719060 1935247 := bstep (se 1 (by rfl) ⟨1451435, by rfl⟩ : syracuseStep 1935247 = 2902871) B2902871
theorem B2615225 : Blo 1719060 2615225 := bstep (se 2 (by rfl) ⟨980709, by rfl⟩ : syracuseStep 2615225 = 1961419) B1961419
theorem B8710091 : Blo 1719060 8710091 := bstep (se 1 (by rfl) ⟨6532568, by rfl⟩ : syracuseStep 8710091 = 13065137) B13065137
theorem B1837063 : Blo 1719060 1837063 := bstep (se 1 (by rfl) ⟨1377797, by rfl⟩ : syracuseStep 1837063 = 2755595) B2755595
theorem B3098683 : Blo 1719060 3098683 := bstep (se 1 (by rfl) ⟨2324012, by rfl⟩ : syracuseStep 3098683 = 4648025) B4648025
theorem B2902135 : Blo 1719060 2902135 := bstep (se 1 (by rfl) ⟨2176601, by rfl⟩ : syracuseStep 2902135 = 4353203) B4353203
theorem B4130963 : Blo 1719060 4130963 := bstep (se 1 (by rfl) ⟨3098222, by rfl⟩ : syracuseStep 4130963 = 6196445) B6196445
theorem B4352201 : Blo 1719060 4352201 := bstep (se 2 (by rfl) ⟨1632075, by rfl⟩ : syracuseStep 4352201 = 3264151) B3264151
theorem B8710415 : Blo 1719060 8710415 := bstep (se 1 (by rfl) ⟨6532811, by rfl⟩ : syracuseStep 8710415 = 13065623) B13065623
theorem B12396833 : Blo 1719060 12396833 := bstep (se 2 (by rfl) ⟨4648812, by rfl⟩ : syracuseStep 12396833 = 9297625) B9297625
theorem B5802299 : Blo 1719060 5802299 := bstep (se 1 (by rfl) ⟨4351724, by rfl⟩ : syracuseStep 5802299 = 8703449) B8703449
theorem B2902331 : Blo 1719060 2902331 := bstep (se 1 (by rfl) ⟨2176748, by rfl⟩ : syracuseStep 2902331 = 4353497) B4353497
theorem B3869063 : Blo 1719060 3869063 := bstep (se 1 (by rfl) ⟨2901797, by rfl⟩ : syracuseStep 3869063 = 5803595) B5803595
theorem B1935751 : Blo 1719060 1935751 := bstep (se 1 (by rfl) ⟨1451813, by rfl⟩ : syracuseStep 1935751 = 2903627) B2903627
theorem B6531475 : Blo 1719060 6531475 := bstep (se 1 (by rfl) ⟨4898606, by rfl⟩ : syracuseStep 6531475 = 9797213) B9797213
theorem B7350713 : Blo 1719060 7350713 := bstep (se 2 (by rfl) ⟨2756517, by rfl⟩ : syracuseStep 7350713 = 5513035) B5513035
theorem B4352555 : Blo 1719060 4352555 := bstep (se 1 (by rfl) ⟨3264416, by rfl⟩ : syracuseStep 4352555 = 6528833) B6528833
theorem B3869243 : Blo 1719060 3869243 := bstep (se 1 (by rfl) ⟨2901932, by rfl⟩ : syracuseStep 3869243 = 5803865) B5803865
theorem B1935931 : Blo 1719060 1935931 := bstep (se 1 (by rfl) ⟨1451948, by rfl⟩ : syracuseStep 1935931 = 2903897) B2903897
theorem B9800311 : Blo 1719060 9800311 := bstep (se 1 (by rfl) ⟨7350233, by rfl⟩ : syracuseStep 9800311 = 14700467) B14700467
theorem B3869369 : Blo 1719060 3869369 := bstep (se 2 (by rfl) ⟨1451013, by rfl⟩ : syracuseStep 3869369 = 2902027) B2902027
theorem B2902729 : Blo 1719060 2902729 := bstep (se 2 (by rfl) ⟨1088523, by rfl⟩ : syracuseStep 2902729 = 2177047) B2177047
theorem B2067215 : Blo 1719060 2067215 := bstep (se 1 (by rfl) ⟨1550411, by rfl⟩ : syracuseStep 2067215 = 3100823) B3100823
theorem B5802785 : Blo 1719060 5802785 := bstep (se 2 (by rfl) ⟨2176044, by rfl⟩ : syracuseStep 5802785 = 4352089) B4352089
theorem B5229355 : Blo 1719060 5229355 := bstep (se 1 (by rfl) ⟨3922016, by rfl⟩ : syracuseStep 5229355 = 7844033) B7844033
theorem B18590579 : Blo 1719060 18590579 := bstep (se 1 (by rfl) ⟨13942934, by rfl⟩ : syracuseStep 18590579 = 27885869) B27885869
theorem B7351175 : Blo 1719060 7351175 := bstep (se 1 (by rfl) ⟨5513381, by rfl⟩ : syracuseStep 7351175 = 11026763) B11026763
theorem B27880355 : Blo 1719060 27880355 := bstep (se 1 (by rfl) ⟨20910266, by rfl⟩ : syracuseStep 27880355 = 41820533) B41820533
theorem B3869711 : Blo 1719060 3869711 := bstep (se 1 (by rfl) ⟨2902283, by rfl⟩ : syracuseStep 3869711 = 5804567) B5804567
theorem B3869729 : Blo 1719060 3869729 := bstep (se 2 (by rfl) ⟨1451148, by rfl⟩ : syracuseStep 3869729 = 2902297) B2902297
theorem B3673289 : Blo 1719060 3673289 := bstep (se 2 (by rfl) ⟨1377483, by rfl⟩ : syracuseStep 3673289 = 2754967) B2754967
theorem B8260865 : Blo 1719060 8260865 := bstep (se 2 (by rfl) ⟨3097824, by rfl⟩ : syracuseStep 8260865 = 6195649) B6195649
theorem B4648207 : Blo 1719060 4648207 := bstep (se 1 (by rfl) ⟨3486155, by rfl⟩ : syracuseStep 4648207 = 6972311) B6972311
theorem B3534113 : Blo 1719060 3534113 := bstep (se 2 (by rfl) ⟨1325292, by rfl⟩ : syracuseStep 3534113 = 2650585) B2650585
theorem B37203299 : Blo 1719060 37203299 := bstep (se 1 (by rfl) ⟨27902474, by rfl⟩ : syracuseStep 37203299 = 55804949) B55804949
theorem B5803379 : Blo 1719060 5803379 := bstep (se 1 (by rfl) ⟨4352534, by rfl⟩ : syracuseStep 5803379 = 8705069) B8705069
theorem B3870071 : Blo 1719060 3870071 := bstep (se 1 (by rfl) ⟨2902553, by rfl⟩ : syracuseStep 3870071 = 5805107) B5805107
theorem B14691719 : Blo 1719060 14691719 := bstep (se 1 (by rfl) ⟨11018789, by rfl⟩ : syracuseStep 14691719 = 22037579) B22037579
theorem B2903431 : Blo 1719060 2903431 := bstep (se 1 (by rfl) ⟨2177573, by rfl⟩ : syracuseStep 2903431 = 4355147) B4355147
theorem B5508499 : Blo 1719060 5508499 := bstep (se 1 (by rfl) ⟨4131374, by rfl⟩ : syracuseStep 5508499 = 8262749) B8262749
theorem B6974905 : Blo 1719060 6974905 := bstep (se 2 (by rfl) ⟨2615589, by rfl⟩ : syracuseStep 6974905 = 5231179) B5231179
theorem B11177437 : Blo 1719060 11177437 := bstep (se 3 (by rfl) ⟨2095769, by rfl⟩ : syracuseStep 11177437 = 4191539) B4191539
theorem B4353547 : Blo 1719060 4353547 := bstep (se 1 (by rfl) ⟨3265160, by rfl⟩ : syracuseStep 4353547 = 6530321) B6530321
theorem B3870251 : Blo 1719060 3870251 := bstep (se 1 (by rfl) ⟨2902688, by rfl⟩ : syracuseStep 3870251 = 5805377) B5805377
theorem B4353689 : Blo 1719060 4353689 := bstep (se 2 (by rfl) ⟨1632633, by rfl⟩ : syracuseStep 4353689 = 3265267) B3265267
theorem B2756281 : Blo 1719060 2756281 := bstep (se 2 (by rfl) ⟨1033605, by rfl⟩ : syracuseStep 2756281 = 2067211) B2067211
theorem B8711873 : Blo 1719060 8711873 := bstep (se 2 (by rfl) ⟨3266952, by rfl⟩ : syracuseStep 8711873 = 6533905) B6533905
theorem B3100361 : Blo 1719060 3100361 := bstep (se 2 (by rfl) ⟨1162635, by rfl⟩ : syracuseStep 3100361 = 2325271) B2325271
theorem B9793295 : Blo 1719060 9793295 := bstep (se 1 (by rfl) ⟨7344971, by rfl⟩ : syracuseStep 9793295 = 14689943) B14689943
theorem B3534607 : Blo 1719060 3534607 := bstep (se 1 (by rfl) ⟨2650955, by rfl⟩ : syracuseStep 3534607 = 5301911) B5301911
theorem B13242163 : Blo 1719060 13242163 := bstep (se 1 (by rfl) ⟨9931622, by rfl⟩ : syracuseStep 13242163 = 19863245) B19863245
theorem B4353851 : Blo 1719060 4353851 := bstep (se 1 (by rfl) ⟨3265388, by rfl⟩ : syracuseStep 4353851 = 6530777) B6530777
theorem B9801587 : Blo 1719060 9801587 := bstep (se 1 (by rfl) ⟨7351190, by rfl⟩ : syracuseStep 9801587 = 14702381) B14702381
theorem B3870611 : Blo 1719060 3870611 := bstep (se 1 (by rfl) ⟨2902958, by rfl⟩ : syracuseStep 3870611 = 5805917) B5805917
theorem B3870665 : Blo 1719060 3870665 := bstep (se 2 (by rfl) ⟨1451499, by rfl⟩ : syracuseStep 3870665 = 2902999) B2902999
theorem B9793547 : Blo 1719060 9793547 := bstep (se 1 (by rfl) ⟨7345160, by rfl⟩ : syracuseStep 9793547 = 14690321) B14690321
theorem B2904079 : Blo 1719060 2904079 := bstep (se 1 (by rfl) ⟨2178059, by rfl⟩ : syracuseStep 2904079 = 4356119) B4356119
theorem B6533207 : Blo 1719060 6533207 := bstep (se 1 (by rfl) ⟨4899905, by rfl⟩ : syracuseStep 6533207 = 9799811) B9799811
theorem B4354195 : Blo 1719060 4354195 := bstep (se 1 (by rfl) ⟨3265646, by rfl⟩ : syracuseStep 4354195 = 6531293) B6531293
theorem B37195949 : Blo 1719060 37195949 := bstep (se 3 (by rfl) ⟨6974240, by rfl⟩ : syracuseStep 37195949 = 13948481) B13948481
theorem B3674297 : Blo 1719060 3674297 := bstep (se 2 (by rfl) ⟨1377861, by rfl⟩ : syracuseStep 3674297 = 2755723) B2755723
theorem B4354337 : Blo 1719060 4354337 := bstep (se 2 (by rfl) ⟨1632876, by rfl⟩ : syracuseStep 4354337 = 3265753) B3265753
theorem B3264887 : Blo 1719060 3264887 := bstep (se 1 (by rfl) ⟨2448665, by rfl⟩ : syracuseStep 3264887 = 4897331) B4897331
theorem B3265039 : Blo 1719060 3265039 := bstep (se 1 (by rfl) ⟨2448779, by rfl⟩ : syracuseStep 3265039 = 4897559) B4897559
theorem B3674639 : Blo 1719060 3674639 := bstep (se 1 (by rfl) ⟨2755979, by rfl⟩ : syracuseStep 3674639 = 5511959) B5511959
theorem B6533693 : Blo 1719060 6533693 := bstep (se 3 (by rfl) ⟨1225067, by rfl⟩ : syracuseStep 6533693 = 2450135) B2450135
theorem B10465859 : Blo 1719060 10465859 := bstep (se 1 (by rfl) ⟨7849394, by rfl⟩ : syracuseStep 10465859 = 15698789) B15698789
theorem B10457687 : Blo 1719060 10457687 := bstep (se 1 (by rfl) ⟨7843265, by rfl⟩ : syracuseStep 10457687 = 15686531) B15686531
theorem B3871367 : Blo 1719060 3871367 := bstep (se 1 (by rfl) ⟨2903525, by rfl⟩ : syracuseStep 3871367 = 5807051) B5807051
theorem B4895417 : Blo 1719060 4895417 := bstep (se 2 (by rfl) ⟨1835781, by rfl⟩ : syracuseStep 4895417 = 3671563) B3671563
theorem B2175751 : Blo 1719060 2175751 := bstep (se 1 (by rfl) ⟨1631813, by rfl⟩ : syracuseStep 2175751 = 3263627) B3263627
theorem B3871547 : Blo 1719060 3871547 := bstep (se 1 (by rfl) ⟨2903660, by rfl⟩ : syracuseStep 3871547 = 5807321) B5807321
theorem B3535751 : Blo 1719060 3535751 := bstep (se 1 (by rfl) ⟨2651813, by rfl⟩ : syracuseStep 3535751 = 5303627) B5303627
theorem B3265427 : Blo 1719060 3265427 := bstep (se 1 (by rfl) ⟨2449070, by rfl⟩ : syracuseStep 3265427 = 4898141) B4898141
theorem B3871673 : Blo 1719060 3871673 := bstep (se 2 (by rfl) ⟨1451877, by rfl⟩ : syracuseStep 3871673 = 2903755) B2903755
theorem B4134007 : Blo 1719060 4134007 := bstep (se 1 (by rfl) ⟨3100505, by rfl⟩ : syracuseStep 4134007 = 6201011) B6201011
theorem B9794753 : Blo 1719060 9794753 := bstep (se 2 (by rfl) ⟨3673032, by rfl⟩ : syracuseStep 9794753 = 7346065) B7346065
theorem B2176247 : Blo 1719060 2176247 := bstep (se 1 (by rfl) ⟨1632185, by rfl⟩ : syracuseStep 2176247 = 3264371) B3264371
theorem B4355329 : Blo 1719060 4355329 := bstep (se 2 (by rfl) ⟨1633248, by rfl⟩ : syracuseStep 4355329 = 3266497) B3266497
theorem B3872015 : Blo 1719060 3872015 := bstep (se 1 (by rfl) ⟨2904011, by rfl⟩ : syracuseStep 3872015 = 5808023) B5808023
theorem B3872033 : Blo 1719060 3872033 := bstep (se 2 (by rfl) ⟨1452012, by rfl⟩ : syracuseStep 3872033 = 2904025) B2904025
theorem B3142955 : Blo 1719060 3142955 := bstep (se 1 (by rfl) ⟨2357216, by rfl⟩ : syracuseStep 3142955 = 4714433) B4714433
theorem B3675451 : Blo 1719060 3675451 := bstep (se 1 (by rfl) ⟨2756588, by rfl⟩ : syracuseStep 3675451 = 5513177) B5513177
theorem B2176399 : Blo 1719060 2176399 := bstep (se 1 (by rfl) ⟨1632299, by rfl⟩ : syracuseStep 2176399 = 3264599) B3264599
theorem B13055417 : Blo 1719060 13055417 := bstep (se 2 (by rfl) ⟨4895781, by rfl⟩ : syracuseStep 13055417 = 9791563) B9791563
theorem B15685073 : Blo 1719060 15685073 := bstep (se 2 (by rfl) ⟨5881902, by rfl⟩ : syracuseStep 15685073 = 11763805) B11763805
theorem B2176571 : Blo 1719060 2176571 := bstep (se 1 (by rfl) ⟨1632428, by rfl⟩ : syracuseStep 2176571 = 3264857) B3264857
theorem B5510717 : Blo 1719060 5510717 := bstep (se 3 (by rfl) ⟨1033259, by rfl⟩ : syracuseStep 5510717 = 2066519) B2066519
theorem B3872375 : Blo 1719060 3872375 := bstep (se 1 (by rfl) ⟨2904281, by rfl⟩ : syracuseStep 3872375 = 5808563) B5808563
theorem B4896409 : Blo 1719060 4896409 := bstep (se 2 (by rfl) ⟨1836153, by rfl⟩ : syracuseStep 4896409 = 3672307) B3672307
theorem B8378093 : Blo 1719060 8378093 := bstep (se 3 (by rfl) ⟨1570892, by rfl⟩ : syracuseStep 8378093 = 3141785) B3141785
theorem B4355927 : Blo 1719060 4355927 := bstep (se 1 (by rfl) ⟨3266945, by rfl⟩ : syracuseStep 4355927 = 6533891) B6533891
theorem B5805971 : Blo 1719060 5805971 := bstep (se 1 (by rfl) ⟨4354478, by rfl⟩ : syracuseStep 5805971 = 8708957) B8708957
theorem B4356139 : Blo 1719060 4356139 := bstep (se 1 (by rfl) ⟨3267104, by rfl⟩ : syracuseStep 4356139 = 6534209) B6534209
theorem B4356281 : Blo 1719060 4356281 := bstep (se 2 (by rfl) ⟨1633605, by rfl⟩ : syracuseStep 4356281 = 3267211) B3267211
theorem B2578619 : Blo 1719060 2578619 := bstep (se 1 (by rfl) ⟨1933964, by rfl⟩ : syracuseStep 2578619 = 3867929) B3867929
theorem B11024585 : Blo 1719060 11024585 := bstep (se 2 (by rfl) ⟨4134219, by rfl⟩ : syracuseStep 11024585 = 8268439) B8268439
theorem B2578679 : Blo 1719060 2578679 := bstep (se 1 (by rfl) ⟨1934009, by rfl⟩ : syracuseStep 2578679 = 3868019) B3868019
theorem B2578703 : Blo 1719060 2578703 := bstep (se 1 (by rfl) ⟨1934027, by rfl⟩ : syracuseStep 2578703 = 3868055) B3868055
theorem B3266831 : Blo 1719060 3266831 := bstep (se 1 (by rfl) ⟨2450123, by rfl⟩ : syracuseStep 3266831 = 4900247) B4900247
theorem B18602257 : Blo 1719060 18602257 := bstep (se 2 (by rfl) ⟨6975846, by rfl⟩ : syracuseStep 18602257 = 13951693) B13951693
theorem B19585313 : Blo 1719060 19585313 := bstep (se 2 (by rfl) ⟨7344492, by rfl⟩ : syracuseStep 19585313 = 14688985) B14688985
theorem B2578745 : Blo 1719060 2578745 := bstep (se 2 (by rfl) ⟨967029, by rfl⟩ : syracuseStep 2578745 = 1934059) B1934059
theorem B2578823 : Blo 1719060 2578823 := bstep (se 1 (by rfl) ⟨1934117, by rfl⟩ : syracuseStep 2578823 = 3868235) B3868235
theorem B2578859 : Blo 1719060 2578859 := bstep (se 1 (by rfl) ⟨1934144, by rfl⟩ : syracuseStep 2578859 = 3868289) B3868289
theorem B2578889 : Blo 1719060 2578889 := bstep (se 2 (by rfl) ⟨967083, by rfl⟩ : syracuseStep 2578889 = 1934167) B1934167
theorem B2177543 : Blo 1719060 2177543 := bstep (se 1 (by rfl) ⟨1633157, by rfl⟩ : syracuseStep 2177543 = 3266315) B3266315
theorem B2579003 : Blo 1719060 2579003 := bstep (se 1 (by rfl) ⟨1934252, by rfl⟩ : syracuseStep 2579003 = 3868505) B3868505
theorem B2579063 : Blo 1719060 2579063 := bstep (se 1 (by rfl) ⟨1934297, by rfl⟩ : syracuseStep 2579063 = 3868595) B3868595
theorem B2579087 : Blo 1719060 2579087 := bstep (se 1 (by rfl) ⟨1934315, by rfl⟩ : syracuseStep 2579087 = 3868631) B3868631
theorem B2579129 : Blo 1719060 2579129 := bstep (se 2 (by rfl) ⟨967173, by rfl⟩ : syracuseStep 2579129 = 1934347) B1934347
theorem B2448073 : Blo 1719060 2448073 := bstep (se 2 (by rfl) ⟨918027, by rfl⟩ : syracuseStep 2448073 = 1836055) B1836055
theorem B74357453 : Blo 1719060 74357453 := bstep (se 3 (by rfl) ⟨13942022, by rfl⟩ : syracuseStep 74357453 = 27884045) B27884045
theorem B2579207 : Blo 1719060 2579207 := bstep (se 1 (by rfl) ⟨1934405, by rfl⟩ : syracuseStep 2579207 = 3868811) B3868811
theorem B2579243 : Blo 1719060 2579243 := bstep (se 1 (by rfl) ⟨1934432, by rfl⟩ : syracuseStep 2579243 = 3868865) B3868865
theorem B1719099 : Blo 1719060 1719099 := bstep (se 1 (by rfl) ⟨1289324, by rfl⟩ : syracuseStep 1719099 = 2578649) B2578649
theorem B2579273 : Blo 1719060 2579273 := bstep (se 2 (by rfl) ⟨967227, by rfl⟩ : syracuseStep 2579273 = 1934455) B1934455
theorem B8264537 : Blo 1719060 8264537 := bstep (se 2 (by rfl) ⟨3099201, by rfl⟩ : syracuseStep 8264537 = 6198403) B6198403
theorem B1719175 : Blo 1719060 1719175 := bstep (se 1 (by rfl) ⟨1289381, by rfl⟩ : syracuseStep 1719175 = 2578763) B2578763
theorem B1719183 : Blo 1719060 1719183 := bstep (se 1 (by rfl) ⟨1289387, by rfl⟩ : syracuseStep 1719183 = 2578775) B2578775
theorem B6527891 : Blo 1719060 6527891 := bstep (se 1 (by rfl) ⟨4895918, by rfl⟩ : syracuseStep 6527891 = 9791837) B9791837
theorem B1719227 : Blo 1719060 1719227 := bstep (se 1 (by rfl) ⟨1289420, by rfl⟩ : syracuseStep 1719227 = 2578841) B2578841
theorem B2579387 : Blo 1719060 2579387 := bstep (se 1 (by rfl) ⟨1934540, by rfl⟩ : syracuseStep 2579387 = 3869081) B3869081
theorem B2579447 : Blo 1719060 2579447 := bstep (se 1 (by rfl) ⟨1934585, by rfl⟩ : syracuseStep 2579447 = 3869171) B3869171
theorem B1719303 : Blo 1719060 1719303 := bstep (se 1 (by rfl) ⟨1289477, by rfl⟩ : syracuseStep 1719303 = 2578955) B2578955
theorem B1719311 : Blo 1719060 1719311 := bstep (se 1 (by rfl) ⟨1289483, by rfl⟩ : syracuseStep 1719311 = 2578967) B2578967
theorem B2579471 : Blo 1719060 2579471 := bstep (se 1 (by rfl) ⟨1934603, by rfl⟩ : syracuseStep 2579471 = 3869207) B3869207
theorem B2579513 : Blo 1719060 2579513 := bstep (se 2 (by rfl) ⟨967317, by rfl⟩ : syracuseStep 2579513 = 1934635) B1934635
theorem B1719355 : Blo 1719060 1719355 := bstep (se 1 (by rfl) ⟨1289516, by rfl⟩ : syracuseStep 1719355 = 2579033) B2579033
theorem B1719431 : Blo 1719060 1719431 := bstep (se 1 (by rfl) ⟨1289573, by rfl⟩ : syracuseStep 1719431 = 2579147) B2579147
theorem B2579591 : Blo 1719060 2579591 := bstep (se 1 (by rfl) ⟨1934693, by rfl⟩ : syracuseStep 2579591 = 3869387) B3869387
theorem B74390669 : Blo 1719060 74390669 := bstep (se 3 (by rfl) ⟨13948250, by rfl⟩ : syracuseStep 74390669 = 27896501) B27896501
theorem B1719439 : Blo 1719060 1719439 := bstep (se 1 (by rfl) ⟨1289579, by rfl⟩ : syracuseStep 1719439 = 2579159) B2579159
theorem B2178191 : Blo 1719060 2178191 := bstep (se 1 (by rfl) ⟨1633643, by rfl⟩ : syracuseStep 2178191 = 3267287) B3267287
theorem B2579627 : Blo 1719060 2579627 := bstep (se 1 (by rfl) ⟨1934720, by rfl⟩ : syracuseStep 2579627 = 3869441) B3869441
theorem B2448569 : Blo 1719060 2448569 := bstep (se 2 (by rfl) ⟨918213, by rfl⟩ : syracuseStep 2448569 = 1836427) B1836427
theorem B1719483 : Blo 1719060 1719483 := bstep (se 1 (by rfl) ⟨1289612, by rfl⟩ : syracuseStep 1719483 = 2579225) B2579225
theorem B2579657 : Blo 1719060 2579657 := bstep (se 2 (by rfl) ⟨967371, by rfl⟩ : syracuseStep 2579657 = 1934743) B1934743
theorem B1719559 : Blo 1719060 1719559 := bstep (se 1 (by rfl) ⟨1289669, by rfl⟩ : syracuseStep 1719559 = 2579339) B2579339
theorem B1719567 : Blo 1719060 1719567 := bstep (se 1 (by rfl) ⟨1289675, by rfl⟩ : syracuseStep 1719567 = 2579351) B2579351
theorem B5807375 : Blo 1719060 5807375 := bstep (se 1 (by rfl) ⟨4355531, by rfl⟩ : syracuseStep 5807375 = 8711063) B8711063
theorem B4963643 : Blo 1719060 4963643 := bstep (se 1 (by rfl) ⟨3722732, by rfl⟩ : syracuseStep 4963643 = 7445465) B7445465
theorem B1719611 : Blo 1719060 1719611 := bstep (se 1 (by rfl) ⟨1289708, by rfl⟩ : syracuseStep 1719611 = 2579417) B2579417
theorem B2579771 : Blo 1719060 2579771 := bstep (se 1 (by rfl) ⟨1934828, by rfl⟩ : syracuseStep 2579771 = 3869657) B3869657
theorem B2579831 : Blo 1719060 2579831 := bstep (se 1 (by rfl) ⟨1934873, by rfl⟩ : syracuseStep 2579831 = 3869747) B3869747
theorem B1719687 : Blo 1719060 1719687 := bstep (se 1 (by rfl) ⟨1289765, by rfl⟩ : syracuseStep 1719687 = 2579531) B2579531
theorem B6200711 : Blo 1719060 6200711 := bstep (se 1 (by rfl) ⟨4650533, by rfl⟩ : syracuseStep 6200711 = 9301067) B9301067
theorem B1719695 : Blo 1719060 1719695 := bstep (se 1 (by rfl) ⟨1289771, by rfl⟩ : syracuseStep 1719695 = 2579543) B2579543
theorem B2579855 : Blo 1719060 2579855 := bstep (se 1 (by rfl) ⟨1934891, by rfl⟩ : syracuseStep 2579855 = 3869783) B3869783
theorem B2579897 : Blo 1719060 2579897 := bstep (se 2 (by rfl) ⟨967461, by rfl⟩ : syracuseStep 2579897 = 1934923) B1934923
theorem B1719739 : Blo 1719060 1719739 := bstep (se 1 (by rfl) ⟨1289804, by rfl⟩ : syracuseStep 1719739 = 2579609) B2579609
theorem B8265169 : Blo 1719060 8265169 := bstep (se 2 (by rfl) ⟨3099438, by rfl⟩ : syracuseStep 8265169 = 6198877) B6198877
theorem B1719815 : Blo 1719060 1719815 := bstep (se 1 (by rfl) ⟨1289861, by rfl⟩ : syracuseStep 1719815 = 2579723) B2579723
theorem B2579975 : Blo 1719060 2579975 := bstep (se 1 (by rfl) ⟨1934981, by rfl⟩ : syracuseStep 2579975 = 3869963) B3869963
theorem B5881355 : Blo 1719060 5881355 := bstep (se 1 (by rfl) ⟨4411016, by rfl⟩ : syracuseStep 5881355 = 8822033) B8822033
theorem B1719823 : Blo 1719060 1719823 := bstep (se 1 (by rfl) ⟨1289867, by rfl⟩ : syracuseStep 1719823 = 2579735) B2579735
theorem B4898333 : Blo 1719060 4898333 := bstep (se 3 (by rfl) ⟨918437, by rfl⟩ : syracuseStep 4898333 = 1836875) B1836875
theorem B5807645 : Blo 1719060 5807645 := bstep (se 3 (by rfl) ⟨1088933, by rfl⟩ : syracuseStep 5807645 = 2177867) B2177867
theorem B2580011 : Blo 1719060 2580011 := bstep (se 1 (by rfl) ⟨1935008, by rfl⟩ : syracuseStep 2580011 = 3870017) B3870017
theorem B1719867 : Blo 1719060 1719867 := bstep (se 1 (by rfl) ⟨1289900, by rfl⟩ : syracuseStep 1719867 = 2579801) B2579801
theorem B7347773 : Blo 1719060 7347773 := bstep (se 3 (by rfl) ⟨1377707, by rfl⟩ : syracuseStep 7347773 = 2755415) B2755415
theorem B2580041 : Blo 1719060 2580041 := bstep (se 2 (by rfl) ⟨967515, by rfl⟩ : syracuseStep 2580041 = 1935031) B1935031
theorem B1719943 : Blo 1719060 1719943 := bstep (se 1 (by rfl) ⟨1289957, by rfl⟩ : syracuseStep 1719943 = 2579915) B2579915
theorem B1719951 : Blo 1719060 1719951 := bstep (se 1 (by rfl) ⟨1289963, by rfl⟩ : syracuseStep 1719951 = 2579927) B2579927
theorem B1719995 : Blo 1719060 1719995 := bstep (se 1 (by rfl) ⟨1289996, by rfl⟩ : syracuseStep 1719995 = 2579993) B2579993
theorem B2580155 : Blo 1719060 2580155 := bstep (se 1 (by rfl) ⟨1935116, by rfl⟩ : syracuseStep 2580155 = 3870233) B3870233
theorem B2580215 : Blo 1719060 2580215 := bstep (se 1 (by rfl) ⟨1935161, by rfl⟩ : syracuseStep 2580215 = 3870323) B3870323
theorem B1720071 : Blo 1719060 1720071 := bstep (se 1 (by rfl) ⟨1290053, by rfl⟩ : syracuseStep 1720071 = 2580107) B2580107
theorem B1720079 : Blo 1719060 1720079 := bstep (se 1 (by rfl) ⟨1290059, by rfl⟩ : syracuseStep 1720079 = 2580119) B2580119
theorem B2580239 : Blo 1719060 2580239 := bstep (se 1 (by rfl) ⟨1935179, by rfl⟩ : syracuseStep 2580239 = 3870359) B3870359
theorem B67927853 : Blo 1719060 67927853 := bstep (se 3 (by rfl) ⟨12736472, by rfl⟩ : syracuseStep 67927853 = 25472945) B25472945
theorem B1720123 : Blo 1719060 1720123 := bstep (se 1 (by rfl) ⟨1290092, by rfl⟩ : syracuseStep 1720123 = 2580185) B2580185
theorem B2580281 : Blo 1719060 2580281 := bstep (se 2 (by rfl) ⟨967605, by rfl⟩ : syracuseStep 2580281 = 1935211) B1935211
theorem B1720199 : Blo 1719060 1720199 := bstep (se 1 (by rfl) ⟨1290149, by rfl⟩ : syracuseStep 1720199 = 2580299) B2580299
theorem B2580359 : Blo 1719060 2580359 := bstep (se 1 (by rfl) ⟨1935269, by rfl⟩ : syracuseStep 2580359 = 3870539) B3870539
theorem B1720207 : Blo 1719060 1720207 := bstep (se 1 (by rfl) ⟨1290155, by rfl⟩ : syracuseStep 1720207 = 2580311) B2580311
theorem B8707985 : Blo 1719060 8707985 := bstep (se 2 (by rfl) ⟨3265494, by rfl⟩ : syracuseStep 8707985 = 6530989) B6530989
theorem B2580395 : Blo 1719060 2580395 := bstep (se 1 (by rfl) ⟨1935296, by rfl⟩ : syracuseStep 2580395 = 3870593) B3870593
theorem B1720251 : Blo 1719060 1720251 := bstep (se 1 (by rfl) ⟨1290188, by rfl⟩ : syracuseStep 1720251 = 2580377) B2580377
theorem B2580425 : Blo 1719060 2580425 := bstep (se 2 (by rfl) ⟨967659, by rfl⟩ : syracuseStep 2580425 = 1935319) B1935319
theorem B6529031 : Blo 1719060 6529031 := bstep (se 1 (by rfl) ⟨4896773, by rfl⟩ : syracuseStep 6529031 = 9793547) B9793547
theorem B9797669 : Blo 1719060 9797669 := bstep (se 4 (by rfl) ⟨918531, by rfl⟩ : syracuseStep 9797669 = 1837063) B1837063
theorem B1720359 : Blo 1719060 1720359 := bstep (se 1 (by rfl) ⟨1290269, by rfl⟩ : syracuseStep 1720359 = 2580539) B2580539
theorem B5808185 : Blo 1719060 5808185 := bstep (se 2 (by rfl) ⟨2178069, by rfl⟩ : syracuseStep 5808185 = 4356139) B4356139
theorem B1720399 : Blo 1719060 1720399 := bstep (se 1 (by rfl) ⟨1290299, by rfl⟩ : syracuseStep 1720399 = 2580599) B2580599
theorem B1720415 : Blo 1719060 1720415 := bstep (se 1 (by rfl) ⟨1290311, by rfl⟩ : syracuseStep 1720415 = 2580623) B2580623
theorem B24797299 : Blo 1719060 24797299 := bstep (se 1 (by rfl) ⟨18597974, by rfl⟩ : syracuseStep 24797299 = 37195949) B37195949
theorem B2449531 : Blo 1719060 2449531 := bstep (se 1 (by rfl) ⟨1837148, by rfl⟩ : syracuseStep 2449531 = 3674297) B3674297
theorem B1720443 : Blo 1719060 1720443 := bstep (se 1 (by rfl) ⟨1290332, by rfl⟩ : syracuseStep 1720443 = 2580665) B2580665
theorem B1720495 : Blo 1719060 1720495 := bstep (se 1 (by rfl) ⟨1290371, by rfl⟩ : syracuseStep 1720495 = 2580743) B2580743
theorem B1720519 : Blo 1719060 1720519 := bstep (se 1 (by rfl) ⟨1290389, by rfl⟩ : syracuseStep 1720519 = 2580779) B2580779
theorem B1720539 : Blo 1719060 1720539 := bstep (se 1 (by rfl) ⟨1290404, by rfl⟩ : syracuseStep 1720539 = 2580809) B2580809
theorem B1720615 : Blo 1719060 1720615 := bstep (se 1 (by rfl) ⟨1290461, by rfl⟩ : syracuseStep 1720615 = 2580923) B2580923
theorem B1720655 : Blo 1719060 1720655 := bstep (se 1 (by rfl) ⟨1290491, by rfl⟩ : syracuseStep 1720655 = 2580983) B2580983
theorem B2449759 : Blo 1719060 2449759 := bstep (se 1 (by rfl) ⟨1837319, by rfl⟩ : syracuseStep 2449759 = 3674639) B3674639
theorem B1720671 : Blo 1719060 1720671 := bstep (se 1 (by rfl) ⟨1290503, by rfl⟩ : syracuseStep 1720671 = 2581007) B2581007
theorem B1720699 : Blo 1719060 1720699 := bstep (se 1 (by rfl) ⟨1290524, by rfl⟩ : syracuseStep 1720699 = 2581049) B2581049
theorem B5808509 : Blo 1719060 5808509 := bstep (se 3 (by rfl) ⟨1089095, by rfl⟩ : syracuseStep 5808509 = 2178191) B2178191
theorem B2580911 : Blo 1719060 2580911 := bstep (se 1 (by rfl) ⟨1935683, by rfl⟩ : syracuseStep 2580911 = 3871367) B3871367
theorem B1720751 : Blo 1719060 1720751 := bstep (se 1 (by rfl) ⟨1290563, by rfl⟩ : syracuseStep 1720751 = 2581127) B2581127
theorem B1720775 : Blo 1719060 1720775 := bstep (se 1 (by rfl) ⟨1290581, by rfl⟩ : syracuseStep 1720775 = 2581163) B2581163
theorem B1720795 : Blo 1719060 1720795 := bstep (se 1 (by rfl) ⟨1290596, by rfl⟩ : syracuseStep 1720795 = 2581193) B2581193
theorem B6529517 : Blo 1719060 6529517 := bstep (se 3 (by rfl) ⟨1224284, by rfl⟩ : syracuseStep 6529517 = 2448569) B2448569
theorem B2581001 : Blo 1719060 2581001 := bstep (se 2 (by rfl) ⟨967875, by rfl⟩ : syracuseStep 2581001 = 1935751) B1935751
theorem B8708633 : Blo 1719060 8708633 := bstep (se 2 (by rfl) ⟨3265737, by rfl⟩ : syracuseStep 8708633 = 6531475) B6531475
theorem B2581031 : Blo 1719060 2581031 := bstep (se 1 (by rfl) ⟨1935773, by rfl⟩ : syracuseStep 2581031 = 3871547) B3871547
theorem B1720871 : Blo 1719060 1720871 := bstep (se 1 (by rfl) ⟨1290653, by rfl⟩ : syracuseStep 1720871 = 2581307) B2581307
theorem B1720911 : Blo 1719060 1720911 := bstep (se 1 (by rfl) ⟨1290683, by rfl⟩ : syracuseStep 1720911 = 2581367) B2581367
theorem B1720927 : Blo 1719060 1720927 := bstep (se 1 (by rfl) ⟨1290695, by rfl⟩ : syracuseStep 1720927 = 2581391) B2581391
theorem B2581115 : Blo 1719060 2581115 := bstep (se 1 (by rfl) ⟨1935836, by rfl⟩ : syracuseStep 2581115 = 3871673) B3871673
theorem B1720955 : Blo 1719060 1720955 := bstep (se 1 (by rfl) ⟨1290716, by rfl⟩ : syracuseStep 1720955 = 2581433) B2581433
theorem B13238957 : Blo 1719060 13238957 := bstep (se 3 (by rfl) ⟨2482304, by rfl⟩ : syracuseStep 13238957 = 4964609) B4964609
theorem B1721007 : Blo 1719060 1721007 := bstep (se 1 (by rfl) ⟨1290755, by rfl⟩ : syracuseStep 1721007 = 2581511) B2581511
theorem B1934023 : Blo 1719060 1934023 := bstep (se 1 (by rfl) ⟨1450517, by rfl⟩ : syracuseStep 1934023 = 2901035) B2901035
theorem B1721031 : Blo 1719060 1721031 := bstep (se 1 (by rfl) ⟨1290773, by rfl⟩ : syracuseStep 1721031 = 2581547) B2581547
theorem B9798353 : Blo 1719060 9798353 := bstep (se 2 (by rfl) ⟨3674382, by rfl⟩ : syracuseStep 9798353 = 7348765) B7348765
theorem B1721051 : Blo 1719060 1721051 := bstep (se 1 (by rfl) ⟨1290788, by rfl⟩ : syracuseStep 1721051 = 2581577) B2581577
theorem B2581241 : Blo 1719060 2581241 := bstep (se 2 (by rfl) ⟨967965, by rfl⟩ : syracuseStep 2581241 = 1935931) B1935931
theorem B13058819 : Blo 1719060 13058819 := bstep (se 1 (by rfl) ⟨9794114, by rfl⟩ : syracuseStep 13058819 = 19588229) B19588229
theorem B6529835 : Blo 1719060 6529835 := bstep (se 1 (by rfl) ⟨4897376, by rfl⟩ : syracuseStep 6529835 = 9794753) B9794753
theorem B13067081 : Blo 1719060 13067081 := bstep (se 2 (by rfl) ⟨4900155, by rfl⟩ : syracuseStep 13067081 = 9800311) B9800311
theorem B2581343 : Blo 1719060 2581343 := bstep (se 1 (by rfl) ⟨1936007, by rfl⟩ : syracuseStep 2581343 = 3872015) B3872015
theorem B2581355 : Blo 1719060 2581355 := bstep (se 1 (by rfl) ⟨1936016, by rfl⟩ : syracuseStep 2581355 = 3872033) B3872033
theorem B2901001 : Blo 1719060 2901001 := bstep (se 2 (by rfl) ⟨1087875, by rfl⟩ : syracuseStep 2901001 = 2175751) B2175751
theorem B52970507 : Blo 1719060 52970507 := bstep (se 1 (by rfl) ⟨39727880, by rfl⟩ : syracuseStep 52970507 = 79455761) B79455761
theorem B2065447 : Blo 1719060 2065447 := bstep (se 1 (by rfl) ⟨1549085, by rfl⟩ : syracuseStep 2065447 = 3098171) B3098171
theorem B27886643 : Blo 1719060 27886643 := bstep (se 1 (by rfl) ⟨20914982, by rfl⟩ : syracuseStep 27886643 = 41829965) B41829965
theorem B6972473 : Blo 1719060 6972473 := bstep (se 2 (by rfl) ⟨2614677, by rfl⟩ : syracuseStep 6972473 = 5229355) B5229355
theorem B2581583 : Blo 1719060 2581583 := bstep (se 1 (by rfl) ⟨1936187, by rfl⟩ : syracuseStep 2581583 = 3872375) B3872375
theorem B2901163 : Blo 1719060 2901163 := bstep (se 1 (by rfl) ⟨2175872, by rfl⟩ : syracuseStep 2901163 = 4351745) B4351745
theorem B18851237 : Blo 1719060 18851237 := bstep (se 4 (by rfl) ⟨1767303, by rfl⟩ : syracuseStep 18851237 = 3534607) B3534607
theorem B2753975 : Blo 1719060 2753975 := bstep (se 1 (by rfl) ⟨2065481, by rfl⟩ : syracuseStep 2753975 = 4130963) B4130963
theorem B2901467 : Blo 1719060 2901467 := bstep (se 1 (by rfl) ⟨2176100, by rfl⟩ : syracuseStep 2901467 = 4352201) B4352201
theorem B7349723 : Blo 1719060 7349723 := bstep (se 1 (by rfl) ⟨5512292, by rfl⟩ : syracuseStep 7349723 = 11024585) B11024585
theorem B3868199 : Blo 1719060 3868199 := bstep (se 1 (by rfl) ⟨2901149, by rfl⟩ : syracuseStep 3868199 = 5802299) B5802299
theorem B1934887 : Blo 1719060 1934887 := bstep (se 1 (by rfl) ⟨1451165, by rfl⟩ : syracuseStep 1934887 = 2902331) B2902331
theorem B27887165 : Blo 1719060 27887165 := bstep (se 3 (by rfl) ⟨5228843, by rfl⟩ : syracuseStep 27887165 = 10457687) B10457687
theorem B4900475 : Blo 1719060 4900475 := bstep (se 1 (by rfl) ⟨3675356, by rfl⟩ : syracuseStep 4900475 = 7350713) B7350713
theorem B2901703 : Blo 1719060 2901703 := bstep (se 1 (by rfl) ⟨2176277, by rfl⟩ : syracuseStep 2901703 = 4352555) B4352555
theorem B4900601 : Blo 1719060 4900601 := bstep (se 2 (by rfl) ⟨1837725, by rfl⟩ : syracuseStep 4900601 = 3675451) B3675451
theorem B6620957 : Blo 1719060 6620957 := bstep (se 3 (by rfl) ⟨1241429, by rfl⟩ : syracuseStep 6620957 = 2482859) B2482859
theorem B49571635 : Blo 1719060 49571635 := bstep (se 1 (by rfl) ⟨37178726, by rfl⟩ : syracuseStep 49571635 = 74357453) B74357453
theorem B2901865 : Blo 1719060 2901865 := bstep (se 2 (by rfl) ⟨1088199, by rfl⟩ : syracuseStep 2901865 = 2176399) B2176399
theorem B3868523 : Blo 1719060 3868523 := bstep (se 1 (by rfl) ⟨2901392, by rfl⟩ : syracuseStep 3868523 = 5802785) B5802785
theorem B3868577 : Blo 1719060 3868577 := bstep (se 2 (by rfl) ⟨1450716, by rfl⟩ : syracuseStep 3868577 = 2901433) B2901433
theorem B9299873 : Blo 1719060 9299873 := bstep (se 2 (by rfl) ⟨3487452, by rfl⟩ : syracuseStep 9299873 = 6974905) B6974905
theorem B4900783 : Blo 1719060 4900783 := bstep (se 1 (by rfl) ⟨3675587, by rfl⟩ : syracuseStep 4900783 = 7351175) B7351175
theorem B4351927 : Blo 1719060 4351927 := bstep (se 1 (by rfl) ⟨3263945, by rfl⟩ : syracuseStep 4351927 = 6527891) B6527891
theorem B11020225 : Blo 1719060 11020225 := bstep (se 2 (by rfl) ⟨4132584, by rfl⟩ : syracuseStep 11020225 = 8265169) B8265169
theorem B22341581 : Blo 1719060 22341581 := bstep (se 3 (by rfl) ⟨4189046, by rfl⟩ : syracuseStep 22341581 = 8378093) B8378093
theorem B14903249 : Blo 1719060 14903249 := bstep (se 2 (by rfl) ⟨5588718, by rfl⟩ : syracuseStep 14903249 = 11177437) B11177437
theorem B5802137 : Blo 1719060 5802137 := bstep (se 2 (by rfl) ⟨2175801, by rfl⟩ : syracuseStep 5802137 = 4351603) B4351603
theorem B5507243 : Blo 1719060 5507243 := bstep (se 1 (by rfl) ⟨4130432, by rfl⟩ : syracuseStep 5507243 = 8260865) B8260865
theorem B3868919 : Blo 1719060 3868919 := bstep (se 1 (by rfl) ⟨2901689, by rfl⟩ : syracuseStep 3868919 = 5803379) B5803379
theorem B17656217 : Blo 1719060 17656217 := bstep (se 2 (by rfl) ⟨6621081, by rfl⟩ : syracuseStep 17656217 = 13242163) B13242163
theorem B2902459 : Blo 1719060 2902459 := bstep (se 1 (by rfl) ⟨2176844, by rfl⟩ : syracuseStep 2902459 = 4353689) B4353689
theorem B6973933 : Blo 1719060 6973933 := bstep (se 3 (by rfl) ⟨1307612, by rfl⟩ : syracuseStep 6973933 = 2615225) B2615225
theorem B2902567 : Blo 1719060 2902567 := bstep (se 1 (by rfl) ⟨2176925, by rfl⟩ : syracuseStep 2902567 = 4353851) B4353851
theorem B4647623 : Blo 1719060 4647623 := bstep (se 1 (by rfl) ⟨3485717, by rfl⟩ : syracuseStep 4647623 = 6971435) B6971435
theorem B4131577 : Blo 1719060 4131577 := bstep (se 2 (by rfl) ⟨1549341, by rfl⟩ : syracuseStep 4131577 = 3098683) B3098683
theorem B3869513 : Blo 1719060 3869513 := bstep (se 2 (by rfl) ⟨1451067, by rfl⟩ : syracuseStep 3869513 = 2902135) B2902135
theorem B2902891 : Blo 1719060 2902891 := bstep (se 1 (by rfl) ⟨2177168, by rfl⟩ : syracuseStep 2902891 = 4354337) B4354337
theorem B6531947 : Blo 1719060 6531947 := bstep (se 1 (by rfl) ⟨4898960, by rfl⟩ : syracuseStep 6531947 = 9797921) B9797921
theorem B19868599 : Blo 1719060 19868599 := bstep (se 1 (by rfl) ⟨14901449, by rfl⟩ : syracuseStep 19868599 = 29802899) B29802899
theorem B22048037 : Blo 1719060 22048037 := bstep (se 4 (by rfl) ⟨2067003, by rfl⟩ : syracuseStep 22048037 = 4134007) B4134007
theorem B5803325 : Blo 1719060 5803325 := bstep (se 3 (by rfl) ⟨1088123, by rfl⟩ : syracuseStep 5803325 = 2176247) B2176247
theorem B4353385 : Blo 1719060 4353385 := bstep (se 2 (by rfl) ⟨1632519, by rfl⟩ : syracuseStep 4353385 = 3265039) B3265039
theorem B8711549 : Blo 1719060 8711549 := bstep (se 3 (by rfl) ⟨1633415, by rfl⟩ : syracuseStep 8711549 = 3266831) B3266831
theorem B3870305 : Blo 1719060 3870305 := bstep (se 2 (by rfl) ⟨1451364, by rfl⟩ : syracuseStep 3870305 = 2902729) B2902729
theorem B8703611 : Blo 1719060 8703611 := bstep (se 1 (by rfl) ⟨6527708, by rfl⟩ : syracuseStep 8703611 = 13055417) B13055417
theorem B4353659 : Blo 1719060 4353659 := bstep (se 1 (by rfl) ⟨3265244, by rfl⟩ : syracuseStep 4353659 = 6530489) B6530489
theorem B4189819 : Blo 1719060 4189819 := bstep (se 1 (by rfl) ⟨3142364, by rfl⟩ : syracuseStep 4189819 = 6284729) B6284729
theorem B10456715 : Blo 1719060 10456715 := bstep (se 1 (by rfl) ⟨7842536, by rfl⟩ : syracuseStep 10456715 = 15685073) B15685073
theorem B3673811 : Blo 1719060 3673811 := bstep (se 1 (by rfl) ⟨2755358, by rfl⟩ : syracuseStep 3673811 = 5510717) B5510717
theorem B2903951 : Blo 1719060 2903951 := bstep (se 1 (by rfl) ⟨2177963, by rfl⟩ : syracuseStep 2903951 = 4355927) B4355927
theorem B3870647 : Blo 1719060 3870647 := bstep (se 1 (by rfl) ⟨2902985, by rfl⟩ : syracuseStep 3870647 = 5805971) B5805971
theorem B13062221 : Blo 1719060 13062221 := bstep (se 3 (by rfl) ⟨2449166, by rfl⟩ : syracuseStep 13062221 = 4898333) B4898333
theorem B2904187 : Blo 1719060 2904187 := bstep (se 1 (by rfl) ⟨2178140, by rfl⟩ : syracuseStep 2904187 = 4356281) B4356281
theorem B5804189 : Blo 1719060 5804189 := bstep (se 3 (by rfl) ⟨1088285, by rfl⟩ : syracuseStep 5804189 = 2176571) B2176571
theorem B3486025 : Blo 1719060 3486025 := bstep (se 2 (by rfl) ⟨1307259, by rfl⟩ : syracuseStep 3486025 = 2614519) B2614519
theorem B6197609 : Blo 1719060 6197609 := bstep (se 2 (by rfl) ⟨2324103, by rfl⟩ : syracuseStep 6197609 = 4648207) B4648207
theorem B13054445 : Blo 1719060 13054445 := bstep (se 3 (by rfl) ⟨2447708, by rfl⟩ : syracuseStep 13054445 = 4895417) B4895417
theorem B3871241 : Blo 1719060 3871241 := bstep (se 2 (by rfl) ⟨1451715, by rfl⟩ : syracuseStep 3871241 = 2903431) B2903431
theorem B7344665 : Blo 1719060 7344665 := bstep (se 2 (by rfl) ⟨2754249, by rfl⟩ : syracuseStep 7344665 = 5508499) B5508499
theorem B5509691 : Blo 1719060 5509691 := bstep (se 1 (by rfl) ⟨4132268, by rfl⟩ : syracuseStep 5509691 = 8264537) B8264537
theorem B5804729 : Blo 1719060 5804729 := bstep (se 2 (by rfl) ⟨2176773, by rfl⟩ : syracuseStep 5804729 = 4353547) B4353547
theorem B3871583 : Blo 1719060 3871583 := bstep (se 1 (by rfl) ⟨2903687, by rfl⟩ : syracuseStep 3871583 = 5807375) B5807375
theorem B2356075 : Blo 1719060 2356075 := bstep (se 1 (by rfl) ⟨1767056, by rfl⟩ : syracuseStep 2356075 = 3534113) B3534113
theorem B24802199 : Blo 1719060 24802199 := bstep (se 1 (by rfl) ⟨18601649, by rfl⟩ : syracuseStep 24802199 = 37203299) B37203299
theorem B3675041 : Blo 1719060 3675041 := bstep (se 2 (by rfl) ⟨1378140, by rfl⟩ : syracuseStep 3675041 = 2756281) B2756281
theorem B9794479 : Blo 1719060 9794479 := bstep (se 1 (by rfl) ⟨7345859, by rfl⟩ : syracuseStep 9794479 = 14691719) B14691719
theorem B4133807 : Blo 1719060 4133807 := bstep (se 1 (by rfl) ⟨3100355, by rfl⟩ : syracuseStep 4133807 = 6200711) B6200711
theorem B3920903 : Blo 1719060 3920903 := bstep (se 1 (by rfl) ⟨2940677, by rfl⟩ : syracuseStep 3920903 = 5881355) B5881355
theorem B3871763 : Blo 1719060 3871763 := bstep (se 1 (by rfl) ⟨2903822, by rfl⟩ : syracuseStep 3871763 = 5807645) B5807645
theorem B6534391 : Blo 1719060 6534391 := bstep (se 1 (by rfl) ⟨4900793, by rfl⟩ : syracuseStep 6534391 = 9801587) B9801587
theorem B5805323 : Blo 1719060 5805323 := bstep (se 1 (by rfl) ⟨4353992, by rfl⟩ : syracuseStep 5805323 = 8707985) B8707985
theorem B3872105 : Blo 1719060 3872105 := bstep (se 2 (by rfl) ⟨1452039, by rfl⟩ : syracuseStep 3872105 = 2904079) B2904079
theorem B4355471 : Blo 1719060 4355471 := bstep (se 1 (by rfl) ⟨3266603, by rfl⟩ : syracuseStep 4355471 = 6533207) B6533207
theorem B3266011 : Blo 1719060 3266011 := bstep (se 1 (by rfl) ⟨2449508, by rfl⟩ : syracuseStep 3266011 = 4899017) B4899017
theorem B3266057 : Blo 1719060 3266057 := bstep (se 2 (by rfl) ⟨1224771, by rfl⟩ : syracuseStep 3266057 = 2449543) B2449543
theorem B5805593 : Blo 1719060 5805593 := bstep (se 2 (by rfl) ⟨2177097, by rfl⟩ : syracuseStep 5805593 = 4354195) B4354195
theorem B59610775 : Blo 1719060 59610775 := bstep (se 1 (by rfl) ⟨44708081, by rfl⟩ : syracuseStep 59610775 = 89416163) B89416163
theorem B24803009 : Blo 1719060 24803009 := bstep (se 2 (by rfl) ⟨9301128, by rfl⟩ : syracuseStep 24803009 = 18602257) B18602257
theorem B4355795 : Blo 1719060 4355795 := bstep (se 1 (by rfl) ⟨3266846, by rfl⟩ : syracuseStep 4355795 = 6533693) B6533693
theorem B3266399 : Blo 1719060 3266399 := bstep (se 1 (by rfl) ⟨2449799, by rfl⟩ : syracuseStep 3266399 = 4899599) B4899599
theorem B9795437 : Blo 1719060 9795437 := bstep (se 3 (by rfl) ⟨1836644, by rfl⟩ : syracuseStep 9795437 = 3673289) B3673289
theorem B2176951 : Blo 1719060 2176951 := bstep (se 1 (by rfl) ⟨1632713, by rfl⟩ : syracuseStep 2176951 = 3265427) B3265427
theorem B2578631 : Blo 1719060 2578631 := bstep (se 1 (by rfl) ⟨1933973, by rfl⟩ : syracuseStep 2578631 = 3867947) B3867947
theorem B2095303 : Blo 1719060 2095303 := bstep (se 1 (by rfl) ⟨1571477, by rfl⟩ : syracuseStep 2095303 = 3142955) B3142955
theorem B8706365 : Blo 1719060 8706365 := bstep (se 3 (by rfl) ⟨1632443, by rfl⟩ : syracuseStep 8706365 = 3264887) B3264887
theorem B2578793 : Blo 1719060 2578793 := bstep (se 2 (by rfl) ⟨967047, by rfl⟩ : syracuseStep 2578793 = 1934095) B1934095
theorem B13056389 : Blo 1719060 13056389 := bstep (se 4 (by rfl) ⟨1224036, by rfl⟩ : syracuseStep 13056389 = 2448073) B2448073
theorem B22043015 : Blo 1719060 22043015 := bstep (se 1 (by rfl) ⟨16532261, by rfl⟩ : syracuseStep 22043015 = 33064523) B33064523
theorem B6527375 : Blo 1719060 6527375 := bstep (se 1 (by rfl) ⟨4895531, by rfl⟩ : syracuseStep 6527375 = 9791063) B9791063
theorem B2578871 : Blo 1719060 2578871 := bstep (se 1 (by rfl) ⟨1934153, by rfl⟩ : syracuseStep 2578871 = 3868307) B3868307
theorem B13064651 : Blo 1719060 13064651 := bstep (se 1 (by rfl) ⟨9798488, by rfl⟩ : syracuseStep 13064651 = 19596977) B19596977
theorem B2578907 : Blo 1719060 2578907 := bstep (se 1 (by rfl) ⟨1934180, by rfl⟩ : syracuseStep 2578907 = 3868361) B3868361
theorem B5806727 : Blo 1719060 5806727 := bstep (se 1 (by rfl) ⟨4355045, by rfl⟩ : syracuseStep 5806727 = 8710091) B8710091
theorem B5806781 : Blo 1719060 5806781 := bstep (se 3 (by rfl) ⟨1088771, by rfl⟩ : syracuseStep 5806781 = 2177543) B2177543
theorem B1719079 : Blo 1719060 1719079 := bstep (se 1 (by rfl) ⟨1289309, by rfl⟩ : syracuseStep 1719079 = 2578619) B2578619
theorem B19594061 : Blo 1719060 19594061 := bstep (se 3 (by rfl) ⟨3673886, by rfl⟩ : syracuseStep 19594061 = 7347773) B7347773
theorem B1719119 : Blo 1719060 1719119 := bstep (se 1 (by rfl) ⟨1289339, by rfl⟩ : syracuseStep 1719119 = 2578679) B2578679
theorem B27908957 : Blo 1719060 27908957 := bstep (se 3 (by rfl) ⟨5232929, by rfl⟩ : syracuseStep 27908957 = 10465859) B10465859
theorem B1719135 : Blo 1719060 1719135 := bstep (se 1 (by rfl) ⟨1289351, by rfl⟩ : syracuseStep 1719135 = 2578703) B2578703
theorem B5806943 : Blo 1719060 5806943 := bstep (se 1 (by rfl) ⟨4355207, by rfl⟩ : syracuseStep 5806943 = 8710415) B8710415
theorem B8264555 : Blo 1719060 8264555 := bstep (se 1 (by rfl) ⟨6198416, by rfl⟩ : syracuseStep 8264555 = 12396833) B12396833
theorem B13056875 : Blo 1719060 13056875 := bstep (se 1 (by rfl) ⟨9792656, by rfl⟩ : syracuseStep 13056875 = 19585313) B19585313
theorem B1719163 : Blo 1719060 1719163 := bstep (se 1 (by rfl) ⟨1289372, by rfl⟩ : syracuseStep 1719163 = 2578745) B2578745
theorem B1719215 : Blo 1719060 1719215 := bstep (se 1 (by rfl) ⟨1289411, by rfl⟩ : syracuseStep 1719215 = 2578823) B2578823
theorem B2579375 : Blo 1719060 2579375 := bstep (se 1 (by rfl) ⟨1934531, by rfl⟩ : syracuseStep 2579375 = 3869063) B3869063
theorem B1719239 : Blo 1719060 1719239 := bstep (se 1 (by rfl) ⟨1289429, by rfl⟩ : syracuseStep 1719239 = 2578859) B2578859
theorem B1719259 : Blo 1719060 1719259 := bstep (se 1 (by rfl) ⟨1289444, by rfl⟩ : syracuseStep 1719259 = 2578889) B2578889
theorem B5807105 : Blo 1719060 5807105 := bstep (se 2 (by rfl) ⟨2177664, by rfl⟩ : syracuseStep 5807105 = 4355329) B4355329
theorem B2579465 : Blo 1719060 2579465 := bstep (se 2 (by rfl) ⟨967299, by rfl⟩ : syracuseStep 2579465 = 1934599) B1934599
theorem B1719335 : Blo 1719060 1719335 := bstep (se 1 (by rfl) ⟨1289501, by rfl⟩ : syracuseStep 1719335 = 2579003) B2579003
theorem B2579495 : Blo 1719060 2579495 := bstep (se 1 (by rfl) ⟨1934621, by rfl⟩ : syracuseStep 2579495 = 3869243) B3869243
theorem B1719375 : Blo 1719060 1719375 := bstep (se 1 (by rfl) ⟨1289531, by rfl⟩ : syracuseStep 1719375 = 2579063) B2579063
theorem B1719391 : Blo 1719060 1719391 := bstep (se 1 (by rfl) ⟨1289543, by rfl⟩ : syracuseStep 1719391 = 2579087) B2579087
theorem B1719419 : Blo 1719060 1719419 := bstep (se 1 (by rfl) ⟨1289564, by rfl⟩ : syracuseStep 1719419 = 2579129) B2579129
theorem B2579579 : Blo 1719060 2579579 := bstep (se 1 (by rfl) ⟨1934684, by rfl⟩ : syracuseStep 2579579 = 3869369) B3869369
theorem B1719471 : Blo 1719060 1719471 := bstep (se 1 (by rfl) ⟨1289603, by rfl⟩ : syracuseStep 1719471 = 2579207) B2579207
theorem B1719495 : Blo 1719060 1719495 := bstep (se 1 (by rfl) ⟨1289621, by rfl⟩ : syracuseStep 1719495 = 2579243) B2579243
theorem B1719515 : Blo 1719060 1719515 := bstep (se 1 (by rfl) ⟨1289636, by rfl⟩ : syracuseStep 1719515 = 2579273) B2579273
theorem B12393719 : Blo 1719060 12393719 := bstep (se 1 (by rfl) ⟨9295289, by rfl⟩ : syracuseStep 12393719 = 18590579) B18590579
theorem B2579705 : Blo 1719060 2579705 := bstep (se 2 (by rfl) ⟨967389, by rfl⟩ : syracuseStep 2579705 = 1934779) B1934779
theorem B18586903 : Blo 1719060 18586903 := bstep (se 1 (by rfl) ⟨13940177, by rfl⟩ : syracuseStep 18586903 = 27880355) B27880355
theorem B1719591 : Blo 1719060 1719591 := bstep (se 1 (by rfl) ⟨1289693, by rfl⟩ : syracuseStep 1719591 = 2579387) B2579387
theorem B1719631 : Blo 1719060 1719631 := bstep (se 1 (by rfl) ⟨1289723, by rfl⟩ : syracuseStep 1719631 = 2579447) B2579447
theorem B1719647 : Blo 1719060 1719647 := bstep (se 1 (by rfl) ⟨1289735, by rfl⟩ : syracuseStep 1719647 = 2579471) B2579471
theorem B2579807 : Blo 1719060 2579807 := bstep (se 1 (by rfl) ⟨1934855, by rfl⟩ : syracuseStep 2579807 = 3869711) B3869711
theorem B2579819 : Blo 1719060 2579819 := bstep (se 1 (by rfl) ⟨1934864, by rfl⟩ : syracuseStep 2579819 = 3869729) B3869729
theorem B1719675 : Blo 1719060 1719675 := bstep (se 1 (by rfl) ⟨1289756, by rfl⟩ : syracuseStep 1719675 = 2579513) B2579513
theorem B5512573 : Blo 1719060 5512573 := bstep (se 3 (by rfl) ⟨1033607, by rfl⟩ : syracuseStep 5512573 = 2067215) B2067215
theorem B1719727 : Blo 1719060 1719727 := bstep (se 1 (by rfl) ⟨1289795, by rfl⟩ : syracuseStep 1719727 = 2579591) B2579591
theorem B49593779 : Blo 1719060 49593779 := bstep (se 1 (by rfl) ⟨37195334, by rfl⟩ : syracuseStep 49593779 = 74390669) B74390669
theorem B33070517 : Blo 1719060 33070517 := bstep (se 5 (by rfl) ⟨1550180, by rfl⟩ : syracuseStep 33070517 = 3100361) B3100361
theorem B1719751 : Blo 1719060 1719751 := bstep (se 1 (by rfl) ⟨1289813, by rfl⟩ : syracuseStep 1719751 = 2579627) B2579627
theorem B181140941 : Blo 1719060 181140941 := bstep (se 3 (by rfl) ⟨33963926, by rfl⟩ : syracuseStep 181140941 = 67927853) B67927853
theorem B1719771 : Blo 1719060 1719771 := bstep (se 1 (by rfl) ⟨1289828, by rfl⟩ : syracuseStep 1719771 = 2579657) B2579657
theorem B6528545 : Blo 1719060 6528545 := bstep (se 2 (by rfl) ⟨2448204, by rfl⟩ : syracuseStep 6528545 = 4896409) B4896409
theorem B3309095 : Blo 1719060 3309095 := bstep (se 1 (by rfl) ⟨2481821, by rfl⟩ : syracuseStep 3309095 = 4963643) B4963643
theorem B1719847 : Blo 1719060 1719847 := bstep (se 1 (by rfl) ⟨1289885, by rfl⟩ : syracuseStep 1719847 = 2579771) B2579771
theorem B1719887 : Blo 1719060 1719887 := bstep (se 1 (by rfl) ⟨1289915, by rfl⟩ : syracuseStep 1719887 = 2579831) B2579831
theorem B2580047 : Blo 1719060 2580047 := bstep (se 1 (by rfl) ⟨1935035, by rfl⟩ : syracuseStep 2580047 = 3870071) B3870071
theorem B1719903 : Blo 1719060 1719903 := bstep (se 1 (by rfl) ⟨1289927, by rfl⟩ : syracuseStep 1719903 = 2579855) B2579855
theorem B1719931 : Blo 1719060 1719931 := bstep (se 1 (by rfl) ⟨1289948, by rfl⟩ : syracuseStep 1719931 = 2579897) B2579897
theorem B1719983 : Blo 1719060 1719983 := bstep (se 1 (by rfl) ⟨1289987, by rfl⟩ : syracuseStep 1719983 = 2579975) B2579975
theorem B9428669 : Blo 1719060 9428669 := bstep (se 3 (by rfl) ⟨1767875, by rfl⟩ : syracuseStep 9428669 = 3535751) B3535751
theorem B1720007 : Blo 1719060 1720007 := bstep (se 1 (by rfl) ⟨1290005, by rfl⟩ : syracuseStep 1720007 = 2580011) B2580011
theorem B2580167 : Blo 1719060 2580167 := bstep (se 1 (by rfl) ⟨1935125, by rfl⟩ : syracuseStep 2580167 = 3870251) B3870251
theorem B1720027 : Blo 1719060 1720027 := bstep (se 1 (by rfl) ⟨1290020, by rfl⟩ : syracuseStep 1720027 = 2580041) B2580041
theorem B6971129 : Blo 1719060 6971129 := bstep (se 2 (by rfl) ⟨2614173, by rfl⟩ : syracuseStep 6971129 = 5228347) B5228347
theorem B1720103 : Blo 1719060 1720103 := bstep (se 1 (by rfl) ⟨1290077, by rfl⟩ : syracuseStep 1720103 = 2580155) B2580155
theorem B5807915 : Blo 1719060 5807915 := bstep (se 1 (by rfl) ⟨4355936, by rfl⟩ : syracuseStep 5807915 = 8711873) B8711873
theorem B1720143 : Blo 1719060 1720143 := bstep (se 1 (by rfl) ⟨1290107, by rfl⟩ : syracuseStep 1720143 = 2580215) B2580215
theorem B6528863 : Blo 1719060 6528863 := bstep (se 1 (by rfl) ⟨4896647, by rfl⟩ : syracuseStep 6528863 = 9793295) B9793295
theorem B1720159 : Blo 1719060 1720159 := bstep (se 1 (by rfl) ⟨1290119, by rfl⟩ : syracuseStep 1720159 = 2580239) B2580239
theorem B2580329 : Blo 1719060 2580329 := bstep (se 2 (by rfl) ⟨967623, by rfl⟩ : syracuseStep 2580329 = 1935247) B1935247
theorem B1720187 : Blo 1719060 1720187 := bstep (se 1 (by rfl) ⟨1290140, by rfl⟩ : syracuseStep 1720187 = 2580281) B2580281
theorem B1720239 : Blo 1719060 1720239 := bstep (se 1 (by rfl) ⟨1290179, by rfl⟩ : syracuseStep 1720239 = 2580359) B2580359
theorem B2580407 : Blo 1719060 2580407 := bstep (se 1 (by rfl) ⟨1935305, by rfl⟩ : syracuseStep 2580407 = 3870611) B3870611
theorem B1720263 : Blo 1719060 1720263 := bstep (se 1 (by rfl) ⟨1290197, by rfl⟩ : syracuseStep 1720263 = 2580395) B2580395
theorem B1720283 : Blo 1719060 1720283 := bstep (se 1 (by rfl) ⟨1290212, by rfl⟩ : syracuseStep 1720283 = 2580425) B2580425
theorem B2580443 : Blo 1719060 2580443 := bstep (se 1 (by rfl) ⟨1935332, by rfl⟩ : syracuseStep 2580443 = 3870665) B3870665
theorem B8708147 : Blo 1719060 8708147 := bstep (se 1 (by rfl) ⟨6531110, by rfl⟩ : syracuseStep 8708147 = 13062221) B13062221
theorem B33063065 : Blo 1719060 33063065 := bstep (se 2 (by rfl) ⟨12398649, by rfl⟩ : syracuseStep 33063065 = 24797299) B24797299
theorem B2793737 : Blo 1719060 2793737 := bstep (se 2 (by rfl) ⟨1047651, by rfl⟩ : syracuseStep 2793737 = 2095303) B2095303
theorem B1720607 : Blo 1719060 1720607 := bstep (se 1 (by rfl) ⟨1290455, by rfl⟩ : syracuseStep 1720607 = 2580911) B2580911
theorem B2580827 : Blo 1719060 2580827 := bstep (se 1 (by rfl) ⟨1935620, by rfl⟩ : syracuseStep 2580827 = 3871241) B3871241
theorem B1720667 : Blo 1719060 1720667 := bstep (se 1 (by rfl) ⟨1290500, by rfl⟩ : syracuseStep 1720667 = 2581001) B2581001
theorem B1720687 : Blo 1719060 1720687 := bstep (se 1 (by rfl) ⟨1290515, by rfl⟩ : syracuseStep 1720687 = 2581031) B2581031
theorem B1720743 : Blo 1719060 1720743 := bstep (se 1 (by rfl) ⟨1290557, by rfl⟩ : syracuseStep 1720743 = 2581115) B2581115
theorem B1720827 : Blo 1719060 1720827 := bstep (se 1 (by rfl) ⟨1290620, by rfl⟩ : syracuseStep 1720827 = 2581241) B2581241
theorem B2581055 : Blo 1719060 2581055 := bstep (se 1 (by rfl) ⟨1935791, by rfl⟩ : syracuseStep 2581055 = 3871583) B3871583
theorem B1720895 : Blo 1719060 1720895 := bstep (se 1 (by rfl) ⟨1290671, by rfl⟩ : syracuseStep 1720895 = 2581343) B2581343
theorem B1720903 : Blo 1719060 1720903 := bstep (se 1 (by rfl) ⟨1290677, by rfl⟩ : syracuseStep 1720903 = 2581355) B2581355
theorem B2450027 : Blo 1719060 2450027 := bstep (se 1 (by rfl) ⟨1837520, by rfl⟩ : syracuseStep 2450027 = 3675041) B3675041
theorem B9298577 : Blo 1719060 9298577 := bstep (se 2 (by rfl) ⟨3486966, by rfl⟩ : syracuseStep 9298577 = 6973933) B6973933
theorem B2613935 : Blo 1719060 2613935 := bstep (se 1 (by rfl) ⟨1960451, by rfl⟩ : syracuseStep 2613935 = 3920903) B3920903
theorem B2581175 : Blo 1719060 2581175 := bstep (se 1 (by rfl) ⟨1935881, by rfl⟩ : syracuseStep 2581175 = 3871763) B3871763
theorem B1721055 : Blo 1719060 1721055 := bstep (se 1 (by rfl) ⟨1290791, by rfl⟩ : syracuseStep 1721055 = 2581583) B2581583
theorem B2581403 : Blo 1719060 2581403 := bstep (se 1 (by rfl) ⟨1936052, by rfl⟩ : syracuseStep 2581403 = 3872105) B3872105
theorem B12567491 : Blo 1719060 12567491 := bstep (se 1 (by rfl) ⟨9425618, by rfl⟩ : syracuseStep 12567491 = 18851237) B18851237
theorem B1835983 : Blo 1719060 1835983 := bstep (se 1 (by rfl) ⟨1376987, by rfl⟩ : syracuseStep 1835983 = 2753975) B2753975
theorem B1934311 : Blo 1719060 1934311 := bstep (se 1 (by rfl) ⟨1450733, by rfl⟩ : syracuseStep 1934311 = 2901467) B2901467
theorem B4899815 : Blo 1719060 4899815 := bstep (se 1 (by rfl) ⟨3674861, by rfl⟩ : syracuseStep 4899815 = 7349723) B7349723
theorem B13059305 : Blo 1719060 13059305 := bstep (se 2 (by rfl) ⟨4897239, by rfl⟩ : syracuseStep 13059305 = 9794479) B9794479
theorem B6530291 : Blo 1719060 6530291 := bstep (se 1 (by rfl) ⟨4897718, by rfl⟩ : syracuseStep 6530291 = 9795437) B9795437
theorem B14894387 : Blo 1719060 14894387 := bstep (se 1 (by rfl) ⟨11170790, by rfl⟩ : syracuseStep 14894387 = 22341581) B22341581
theorem B3868001 : Blo 1719060 3868001 := bstep (se 2 (by rfl) ⟨1450500, by rfl⟩ : syracuseStep 3868001 = 2901001) B2901001
theorem B2753929 : Blo 1719060 2753929 := bstep (se 2 (by rfl) ⟨1032723, by rfl⟩ : syracuseStep 2753929 = 2065447) B2065447
theorem B3868091 : Blo 1719060 3868091 := bstep (se 1 (by rfl) ⟨2901068, by rfl⟩ : syracuseStep 3868091 = 5802137) B5802137
theorem B3671495 : Blo 1719060 3671495 := bstep (se 1 (by rfl) ⟨2753621, by rfl⟩ : syracuseStep 3671495 = 5507243) B5507243
theorem B3868217 : Blo 1719060 3868217 := bstep (se 2 (by rfl) ⟨1450581, by rfl⟩ : syracuseStep 3868217 = 2901163) B2901163
theorem B4351583 : Blo 1719060 4351583 := bstep (se 1 (by rfl) ⟨3263687, by rfl⟩ : syracuseStep 4351583 = 6527375) B6527375
theorem B8709767 : Blo 1719060 8709767 := bstep (se 1 (by rfl) ⟨6532325, by rfl⟩ : syracuseStep 8709767 = 13064651) B13064651
theorem B24782537 : Blo 1719060 24782537 := bstep (se 2 (by rfl) ⟨9293451, by rfl⟩ : syracuseStep 24782537 = 18586903) B18586903
theorem B7350097 : Blo 1719060 7350097 := bstep (se 2 (by rfl) ⟨2756286, by rfl⟩ : syracuseStep 7350097 = 5512573) B5512573
theorem B18605971 : Blo 1719060 18605971 := bstep (se 1 (by rfl) ⟨13954478, by rfl⟩ : syracuseStep 18605971 = 27908957) B27908957
theorem B14698691 : Blo 1719060 14698691 := bstep (se 1 (by rfl) ⟨11024018, by rfl⟩ : syracuseStep 14698691 = 22048037) B22048037
theorem B79481033 : Blo 1719060 79481033 := bstep (se 2 (by rfl) ⟨29805387, by rfl⟩ : syracuseStep 79481033 = 59610775) B59610775
theorem B3868883 : Blo 1719060 3868883 := bstep (se 1 (by rfl) ⟨2901662, by rfl⟩ : syracuseStep 3868883 = 5803325) B5803325
theorem B3868937 : Blo 1719060 3868937 := bstep (se 2 (by rfl) ⟨1450851, by rfl⟩ : syracuseStep 3868937 = 2901703) B2901703
theorem B22047011 : Blo 1719060 22047011 := bstep (se 1 (by rfl) ⟨16535258, by rfl⟩ : syracuseStep 22047011 = 33070517) B33070517
theorem B120760627 : Blo 1719060 120760627 := bstep (se 1 (by rfl) ⟨90570470, by rfl⟩ : syracuseStep 120760627 = 181140941) B181140941
theorem B4352363 : Blo 1719060 4352363 := bstep (se 1 (by rfl) ⟨3264272, by rfl⟩ : syracuseStep 4352363 = 6528545) B6528545
theorem B2206063 : Blo 1719060 2206063 := bstep (se 1 (by rfl) ⟨1654547, by rfl⟩ : syracuseStep 2206063 = 3309095) B3309095
theorem B66095513 : Blo 1719060 66095513 := bstep (se 2 (by rfl) ⟨24785817, by rfl⟩ : syracuseStep 66095513 = 49571635) B49571635
theorem B5802407 : Blo 1719060 5802407 := bstep (se 1 (by rfl) ⟨4351805, by rfl⟩ : syracuseStep 5802407 = 8703611) B8703611
theorem B2902439 : Blo 1719060 2902439 := bstep (se 1 (by rfl) ⟨2176829, by rfl⟩ : syracuseStep 2902439 = 4353659) B4353659
theorem B6285779 : Blo 1719060 6285779 := bstep (se 1 (by rfl) ⟨4714334, by rfl⟩ : syracuseStep 6285779 = 9428669) B9428669
theorem B3869153 : Blo 1719060 3869153 := bstep (se 2 (by rfl) ⟨1450932, by rfl⟩ : syracuseStep 3869153 = 2901865) B2901865
theorem B4647419 : Blo 1719060 4647419 := bstep (se 1 (by rfl) ⟨3485564, by rfl⟩ : syracuseStep 4647419 = 6971129) B6971129
theorem B39741997 : Blo 1719060 39741997 := bstep (se 3 (by rfl) ⟨7451624, by rfl⟩ : syracuseStep 39741997 = 14903249) B14903249
theorem B4352575 : Blo 1719060 4352575 := bstep (se 1 (by rfl) ⟨3264431, by rfl⟩ : syracuseStep 4352575 = 6528863) B6528863
theorem B5802569 : Blo 1719060 5802569 := bstep (se 2 (by rfl) ⟨2175963, by rfl⟩ : syracuseStep 5802569 = 4351927) B4351927
theorem B2902601 : Blo 1719060 2902601 := bstep (se 2 (by rfl) ⟨1088475, by rfl⟩ : syracuseStep 2902601 = 2176951) B2176951
theorem B1935967 : Blo 1719060 1935967 := bstep (se 1 (by rfl) ⟨1451975, by rfl⟩ : syracuseStep 1935967 = 2903951) B2903951
theorem B4352687 : Blo 1719060 4352687 := bstep (se 1 (by rfl) ⟨3264515, by rfl⟩ : syracuseStep 4352687 = 6529031) B6529031
theorem B6531779 : Blo 1719060 6531779 := bstep (se 1 (by rfl) ⟨4898834, by rfl⟩ : syracuseStep 6531779 = 9797669) B9797669
theorem B3869459 : Blo 1719060 3869459 := bstep (se 1 (by rfl) ⟨2902094, by rfl⟩ : syracuseStep 3869459 = 5804189) B5804189
theorem B4131739 : Blo 1719060 4131739 := bstep (se 1 (by rfl) ⟨3098804, by rfl⟩ : syracuseStep 4131739 = 6197609) B6197609
theorem B8702963 : Blo 1719060 8702963 := bstep (se 1 (by rfl) ⟨6527222, by rfl⟩ : syracuseStep 8702963 = 13054445) B13054445
theorem B4353011 : Blo 1719060 4353011 := bstep (se 1 (by rfl) ⟨3264758, by rfl⟩ : syracuseStep 4353011 = 6529517) B6529517
theorem B3673127 : Blo 1719060 3673127 := bstep (se 1 (by rfl) ⟨2754845, by rfl⟩ : syracuseStep 3673127 = 5509691) B5509691
theorem B4648033 : Blo 1719060 4648033 := bstep (se 2 (by rfl) ⟨1743012, by rfl⟩ : syracuseStep 4648033 = 3486025) B3486025
theorem B8825971 : Blo 1719060 8825971 := bstep (se 1 (by rfl) ⟨6619478, by rfl⟩ : syracuseStep 8825971 = 13238957) B13238957
theorem B3869819 : Blo 1719060 3869819 := bstep (se 1 (by rfl) ⟨2902364, by rfl⟩ : syracuseStep 3869819 = 5804729) B5804729
theorem B6532235 : Blo 1719060 6532235 := bstep (se 1 (by rfl) ⟨4899176, by rfl⟩ : syracuseStep 6532235 = 9798353) B9798353
theorem B4353223 : Blo 1719060 4353223 := bstep (se 1 (by rfl) ⟨3264917, by rfl⟩ : syracuseStep 4353223 = 6529835) B6529835
theorem B8711387 : Blo 1719060 8711387 := bstep (se 1 (by rfl) ⟨6533540, by rfl⟩ : syracuseStep 8711387 = 13067081) B13067081
theorem B3869945 : Blo 1719060 3869945 := bstep (se 2 (by rfl) ⟨1451229, by rfl⟩ : syracuseStep 3869945 = 2902459) B2902459
theorem B16534799 : Blo 1719060 16534799 := bstep (se 1 (by rfl) ⟨12401099, by rfl⟩ : syracuseStep 16534799 = 24802199) B24802199
theorem B2755871 : Blo 1719060 2755871 := bstep (se 1 (by rfl) ⟨2066903, by rfl⟩ : syracuseStep 2755871 = 4133807) B4133807
theorem B18591095 : Blo 1719060 18591095 := bstep (se 1 (by rfl) ⟨13943321, by rfl⟩ : syracuseStep 18591095 = 27886643) B27886643
theorem B4648315 : Blo 1719060 4648315 := bstep (se 1 (by rfl) ⟨3486236, by rfl⟩ : syracuseStep 4648315 = 6972473) B6972473
theorem B3870089 : Blo 1719060 3870089 := bstep (se 2 (by rfl) ⟨1451283, by rfl⟩ : syracuseStep 3870089 = 2902567) B2902567
theorem B3870215 : Blo 1719060 3870215 := bstep (se 1 (by rfl) ⟨2902661, by rfl⟩ : syracuseStep 3870215 = 5805323) B5805323
theorem B2903647 : Blo 1719060 2903647 := bstep (se 1 (by rfl) ⟨2177735, by rfl⟩ : syracuseStep 2903647 = 4355471) B4355471
theorem B5508769 : Blo 1719060 5508769 := bstep (se 2 (by rfl) ⟨2065788, by rfl⟩ : syracuseStep 5508769 = 4131577) B4131577
theorem B3870395 : Blo 1719060 3870395 := bstep (se 1 (by rfl) ⟨2902796, by rfl⟩ : syracuseStep 3870395 = 5805593) B5805593
theorem B18591443 : Blo 1719060 18591443 := bstep (se 1 (by rfl) ⟨13943582, by rfl⟩ : syracuseStep 18591443 = 27887165) B27887165
theorem B16535339 : Blo 1719060 16535339 := bstep (se 1 (by rfl) ⟨12401504, by rfl⟩ : syracuseStep 16535339 = 24803009) B24803009
theorem B2903863 : Blo 1719060 2903863 := bstep (se 1 (by rfl) ⟨2177897, by rfl⟩ : syracuseStep 2903863 = 4355795) B4355795
theorem B3141433 : Blo 1719060 3141433 := bstep (se 2 (by rfl) ⟨1178037, by rfl⟩ : syracuseStep 3141433 = 2356075) B2356075
theorem B3870521 : Blo 1719060 3870521 := bstep (se 2 (by rfl) ⟨1451445, by rfl⟩ : syracuseStep 3870521 = 2902891) B2902891
theorem B5804243 : Blo 1719060 5804243 := bstep (se 1 (by rfl) ⟨4353182, by rfl⟩ : syracuseStep 5804243 = 8706365) B8706365
theorem B8704259 : Blo 1719060 8704259 := bstep (se 1 (by rfl) ⟨6528194, by rfl⟩ : syracuseStep 8704259 = 13056389) B13056389
theorem B8712521 : Blo 1719060 8712521 := bstep (se 2 (by rfl) ⟨3267195, by rfl⟩ : syracuseStep 8712521 = 6534391) B6534391
theorem B3871151 : Blo 1719060 3871151 := bstep (se 1 (by rfl) ⟨2903363, by rfl⟩ : syracuseStep 3871151 = 5806727) B5806727
theorem B3871187 : Blo 1719060 3871187 := bstep (se 1 (by rfl) ⟨2903390, by rfl⟩ : syracuseStep 3871187 = 5806781) B5806781
theorem B5804513 : Blo 1719060 5804513 := bstep (se 2 (by rfl) ⟨2176692, by rfl⟩ : syracuseStep 5804513 = 4353385) B4353385
theorem B13062707 : Blo 1719060 13062707 := bstep (se 1 (by rfl) ⟨9797030, by rfl⟩ : syracuseStep 13062707 = 19594061) B19594061
theorem B3871295 : Blo 1719060 3871295 := bstep (se 1 (by rfl) ⟨2903471, by rfl⟩ : syracuseStep 3871295 = 5806943) B5806943
theorem B8704583 : Blo 1719060 8704583 := bstep (se 1 (by rfl) ⟨6528437, by rfl⟩ : syracuseStep 8704583 = 13056875) B13056875
theorem B5509703 : Blo 1719060 5509703 := bstep (se 1 (by rfl) ⟨4132277, by rfl⟩ : syracuseStep 5509703 = 8264555) B8264555
theorem B4354631 : Blo 1719060 4354631 := bstep (se 1 (by rfl) ⟨3265973, by rfl⟩ : syracuseStep 4354631 = 6531947) B6531947
theorem B4354681 : Blo 1719060 4354681 := bstep (se 2 (by rfl) ⟨1633005, by rfl⟩ : syracuseStep 4354681 = 3266011) B3266011
theorem B3871403 : Blo 1719060 3871403 := bstep (se 1 (by rfl) ⟨2903552, by rfl⟩ : syracuseStep 3871403 = 5807105) B5807105
theorem B8262479 : Blo 1719060 8262479 := bstep (se 1 (by rfl) ⟨6196859, by rfl⟩ : syracuseStep 8262479 = 12393719) B12393719
theorem B3871943 : Blo 1719060 3871943 := bstep (se 1 (by rfl) ⟨2903957, by rfl⟩ : syracuseStep 3871943 = 5807915) B5807915
theorem B6534377 : Blo 1719060 6534377 := bstep (se 2 (by rfl) ⟨2450391, by rfl⟩ : syracuseStep 6534377 = 4900783) B4900783
theorem B14693633 : Blo 1719060 14693633 := bstep (se 2 (by rfl) ⟨5510112, by rfl⟩ : syracuseStep 14693633 = 11020225) B11020225
theorem B3872123 : Blo 1719060 3872123 := bstep (se 1 (by rfl) ⟨2904092, by rfl⟩ : syracuseStep 3872123 = 5808185) B5808185
theorem B3872249 : Blo 1719060 3872249 := bstep (se 2 (by rfl) ⟨1452093, by rfl⟩ : syracuseStep 3872249 = 2904187) B2904187
theorem B3872339 : Blo 1719060 3872339 := bstep (se 1 (by rfl) ⟨2904254, by rfl⟩ : syracuseStep 3872339 = 5808509) B5808509
theorem B4896443 : Blo 1719060 4896443 := bstep (se 1 (by rfl) ⟨3672332, by rfl⟩ : syracuseStep 4896443 = 7344665) B7344665
theorem B5805755 : Blo 1719060 5805755 := bstep (se 1 (by rfl) ⟨4354316, by rfl⟩ : syracuseStep 5805755 = 8708633) B8708633
theorem B3266345 : Blo 1719060 3266345 := bstep (se 2 (by rfl) ⟨1224879, by rfl⟩ : syracuseStep 3266345 = 2449759) B2449759
theorem B8705879 : Blo 1719060 8705879 := bstep (se 1 (by rfl) ⟨6529409, by rfl⟩ : syracuseStep 8705879 = 13058819) B13058819
theorem B13064165 : Blo 1719060 13064165 := bstep (se 4 (by rfl) ⟨1224765, by rfl⟩ : syracuseStep 13064165 = 2449531) B2449531
theorem B35313671 : Blo 1719060 35313671 := bstep (se 1 (by rfl) ⟨26485253, by rfl⟩ : syracuseStep 35313671 = 52970507) B52970507
theorem B2578697 : Blo 1719060 2578697 := bstep (se 2 (by rfl) ⟨967011, by rfl⟩ : syracuseStep 2578697 = 1934023) B1934023
theorem B2177371 : Blo 1719060 2177371 := bstep (se 1 (by rfl) ⟨1633028, by rfl⟩ : syracuseStep 2177371 = 3266057) B3266057
theorem B2578799 : Blo 1719060 2578799 := bstep (se 1 (by rfl) ⟨1934099, by rfl⟩ : syracuseStep 2578799 = 3868199) B3868199
theorem B3266983 : Blo 1719060 3266983 := bstep (se 1 (by rfl) ⟨2450237, by rfl⟩ : syracuseStep 3266983 = 4900475) B4900475
theorem B3267067 : Blo 1719060 3267067 := bstep (se 1 (by rfl) ⟨2450300, by rfl⟩ : syracuseStep 3267067 = 4900601) B4900601
theorem B4413971 : Blo 1719060 4413971 := bstep (se 1 (by rfl) ⟨3310478, by rfl⟩ : syracuseStep 4413971 = 6620957) B6620957
theorem B2177599 : Blo 1719060 2177599 := bstep (se 1 (by rfl) ⟨1633199, by rfl⟩ : syracuseStep 2177599 = 3266399) B3266399
theorem B2579015 : Blo 1719060 2579015 := bstep (se 1 (by rfl) ⟨1934261, by rfl⟩ : syracuseStep 2579015 = 3868523) B3868523
theorem B26491465 : Blo 1719060 26491465 := bstep (se 2 (by rfl) ⟨9934299, by rfl⟩ : syracuseStep 26491465 = 19868599) B19868599
theorem B2579051 : Blo 1719060 2579051 := bstep (se 1 (by rfl) ⟨1934288, by rfl⟩ : syracuseStep 2579051 = 3868577) B3868577
theorem B6199915 : Blo 1719060 6199915 := bstep (se 1 (by rfl) ⟨4649936, by rfl⟩ : syracuseStep 6199915 = 9299873) B9299873
theorem B1719087 : Blo 1719060 1719087 := bstep (se 1 (by rfl) ⟨1289315, by rfl⟩ : syracuseStep 1719087 = 2578631) B2578631
theorem B2579279 : Blo 1719060 2579279 := bstep (se 1 (by rfl) ⟨1934459, by rfl⟩ : syracuseStep 2579279 = 3868919) B3868919
theorem B1719195 : Blo 1719060 1719195 := bstep (se 1 (by rfl) ⟨1289396, by rfl⟩ : syracuseStep 1719195 = 2578793) B2578793
theorem B14695343 : Blo 1719060 14695343 := bstep (se 1 (by rfl) ⟨11021507, by rfl⟩ : syracuseStep 14695343 = 22043015) B22043015
theorem B11770811 : Blo 1719060 11770811 := bstep (se 1 (by rfl) ⟨8828108, by rfl⟩ : syracuseStep 11770811 = 17656217) B17656217
theorem B1719247 : Blo 1719060 1719247 := bstep (se 1 (by rfl) ⟨1289435, by rfl⟩ : syracuseStep 1719247 = 2578871) B2578871
theorem B1719271 : Blo 1719060 1719271 := bstep (se 1 (by rfl) ⟨1289453, by rfl⟩ : syracuseStep 1719271 = 2578907) B2578907
theorem B12393661 : Blo 1719060 12393661 := bstep (se 3 (by rfl) ⟨2323811, by rfl⟩ : syracuseStep 12393661 = 4647623) B4647623
theorem B2579675 : Blo 1719060 2579675 := bstep (se 1 (by rfl) ⟨1934756, by rfl⟩ : syracuseStep 2579675 = 3869513) B3869513
theorem B1719583 : Blo 1719060 1719583 := bstep (se 1 (by rfl) ⟨1289687, by rfl⟩ : syracuseStep 1719583 = 2579375) B2579375
theorem B1719643 : Blo 1719060 1719643 := bstep (se 1 (by rfl) ⟨1289732, by rfl⟩ : syracuseStep 1719643 = 2579465) B2579465
theorem B1719663 : Blo 1719060 1719663 := bstep (se 1 (by rfl) ⟨1289747, by rfl⟩ : syracuseStep 1719663 = 2579495) B2579495
theorem B2579849 : Blo 1719060 2579849 := bstep (se 2 (by rfl) ⟨967443, by rfl⟩ : syracuseStep 2579849 = 1934887) B1934887
theorem B1719719 : Blo 1719060 1719719 := bstep (se 1 (by rfl) ⟨1289789, by rfl⟩ : syracuseStep 1719719 = 2579579) B2579579
theorem B5586425 : Blo 1719060 5586425 := bstep (se 2 (by rfl) ⟨2094909, by rfl⟩ : syracuseStep 5586425 = 4189819) B4189819
theorem B1719803 : Blo 1719060 1719803 := bstep (se 1 (by rfl) ⟨1289852, by rfl⟩ : syracuseStep 1719803 = 2579705) B2579705
theorem B1719871 : Blo 1719060 1719871 := bstep (se 1 (by rfl) ⟨1289903, by rfl⟩ : syracuseStep 1719871 = 2579807) B2579807
theorem B1719879 : Blo 1719060 1719879 := bstep (se 1 (by rfl) ⟨1289909, by rfl⟩ : syracuseStep 1719879 = 2579819) B2579819
theorem B5807699 : Blo 1719060 5807699 := bstep (se 1 (by rfl) ⟨4355774, by rfl⟩ : syracuseStep 5807699 = 8711549) B8711549
theorem B33062519 : Blo 1719060 33062519 := bstep (se 1 (by rfl) ⟨24796889, by rfl⟩ : syracuseStep 33062519 = 49593779) B49593779
theorem B1720031 : Blo 1719060 1720031 := bstep (se 1 (by rfl) ⟨1290023, by rfl⟩ : syracuseStep 1720031 = 2580047) B2580047
theorem B2580203 : Blo 1719060 2580203 := bstep (se 1 (by rfl) ⟨1935152, by rfl⟩ : syracuseStep 2580203 = 3870305) B3870305
theorem B6971143 : Blo 1719060 6971143 := bstep (se 1 (by rfl) ⟨5228357, by rfl⟩ : syracuseStep 6971143 = 10456715) B10456715
theorem B1720111 : Blo 1719060 1720111 := bstep (se 1 (by rfl) ⟨1290083, by rfl⟩ : syracuseStep 1720111 = 2580167) B2580167
theorem B2449207 : Blo 1719060 2449207 := bstep (se 1 (by rfl) ⟨1836905, by rfl⟩ : syracuseStep 2449207 = 3673811) B3673811
theorem B1720219 : Blo 1719060 1720219 := bstep (se 1 (by rfl) ⟨1290164, by rfl⟩ : syracuseStep 1720219 = 2580329) B2580329
theorem B1720271 : Blo 1719060 1720271 := bstep (se 1 (by rfl) ⟨1290203, by rfl⟩ : syracuseStep 1720271 = 2580407) B2580407
theorem B2580431 : Blo 1719060 2580431 := bstep (se 1 (by rfl) ⟨1935323, by rfl⟩ : syracuseStep 2580431 = 3870647) B3870647
theorem B1720295 : Blo 1719060 1720295 := bstep (se 1 (by rfl) ⟨1290221, by rfl⟩ : syracuseStep 1720295 = 2580443) B2580443
theorem B5808347 : Blo 1719060 5808347 := bstep (se 1 (by rfl) ⟨4356260, by rfl⟩ : syracuseStep 5808347 = 8712521) B8712521
theorem B1720551 : Blo 1719060 1720551 := bstep (se 1 (by rfl) ⟨1290413, by rfl⟩ : syracuseStep 1720551 = 2580827) B2580827
theorem B2580767 : Blo 1719060 2580767 := bstep (se 1 (by rfl) ⟨1935575, by rfl⟩ : syracuseStep 2580767 = 3871151) B3871151
theorem B2580791 : Blo 1719060 2580791 := bstep (se 1 (by rfl) ⟨1935593, by rfl⟩ : syracuseStep 2580791 = 3871187) B3871187
theorem B8708471 : Blo 1719060 8708471 := bstep (se 1 (by rfl) ⟨6531353, by rfl⟩ : syracuseStep 8708471 = 13062707) B13062707
theorem B2580863 : Blo 1719060 2580863 := bstep (se 1 (by rfl) ⟨1935647, by rfl⟩ : syracuseStep 2580863 = 3871295) B3871295
theorem B1720703 : Blo 1719060 1720703 := bstep (se 1 (by rfl) ⟨1290527, by rfl⟩ : syracuseStep 1720703 = 2581055) B2581055
theorem B161014169 : Blo 1719060 161014169 := bstep (se 2 (by rfl) ⟨60380313, by rfl⟩ : syracuseStep 161014169 = 120760627) B120760627
theorem B2580935 : Blo 1719060 2580935 := bstep (se 1 (by rfl) ⟨1935701, by rfl⟩ : syracuseStep 2580935 = 3871403) B3871403
theorem B1720783 : Blo 1719060 1720783 := bstep (se 1 (by rfl) ⟨1290587, by rfl⟩ : syracuseStep 1720783 = 2581175) B2581175
theorem B2941417 : Blo 1719060 2941417 := bstep (se 2 (by rfl) ⟨1103031, by rfl⟩ : syracuseStep 2941417 = 2206063) B2206063
theorem B24789509 : Blo 1719060 24789509 := bstep (se 4 (by rfl) ⟨2324016, by rfl⟩ : syracuseStep 24789509 = 4648033) B4648033
theorem B1720935 : Blo 1719060 1720935 := bstep (se 1 (by rfl) ⟨1290701, by rfl⟩ : syracuseStep 1720935 = 2581403) B2581403
theorem B2581289 : Blo 1719060 2581289 := bstep (se 2 (by rfl) ⟨967983, by rfl⟩ : syracuseStep 2581289 = 1935967) B1935967
theorem B2581295 : Blo 1719060 2581295 := bstep (se 1 (by rfl) ⟨1935971, by rfl⟩ : syracuseStep 2581295 = 3871943) B3871943
theorem B8266553 : Blo 1719060 8266553 := bstep (se 2 (by rfl) ⟨3099957, by rfl⟩ : syracuseStep 8266553 = 6199915) B6199915
theorem B9929591 : Blo 1719060 9929591 := bstep (se 1 (by rfl) ⟨7447193, by rfl⟩ : syracuseStep 9929591 = 14894387) B14894387
theorem B2581415 : Blo 1719060 2581415 := bstep (se 1 (by rfl) ⟨1936061, by rfl⟩ : syracuseStep 2581415 = 3872123) B3872123
theorem B2581499 : Blo 1719060 2581499 := bstep (se 1 (by rfl) ⟨1936124, by rfl⟩ : syracuseStep 2581499 = 3872249) B3872249
theorem B2581559 : Blo 1719060 2581559 := bstep (se 1 (by rfl) ⟨1936169, by rfl⟩ : syracuseStep 2581559 = 3872339) B3872339
theorem B2901055 : Blo 1719060 2901055 := bstep (se 1 (by rfl) ⟨2175791, by rfl⟩ : syracuseStep 2901055 = 4351583) B4351583
theorem B8709443 : Blo 1719060 8709443 := bstep (se 1 (by rfl) ⟨6532082, by rfl⟩ : syracuseStep 8709443 = 13064165) B13064165
theorem B9799127 : Blo 1719060 9799127 := bstep (se 1 (by rfl) ⟨7349345, by rfl⟩ : syracuseStep 9799127 = 14698691) B14698691
theorem B52987355 : Blo 1719060 52987355 := bstep (se 1 (by rfl) ⟨39740516, by rfl⟩ : syracuseStep 52987355 = 79481033) B79481033
theorem B14698007 : Blo 1719060 14698007 := bstep (se 1 (by rfl) ⟨11023505, by rfl⟩ : syracuseStep 14698007 = 22047011) B22047011
theorem B2901575 : Blo 1719060 2901575 := bstep (se 1 (by rfl) ⟨2176181, by rfl⟩ : syracuseStep 2901575 = 4352363) B4352363
theorem B16524881 : Blo 1719060 16524881 := bstep (se 2 (by rfl) ⟨6196830, by rfl⟩ : syracuseStep 16524881 = 12393661) B12393661
theorem B3868271 : Blo 1719060 3868271 := bstep (se 1 (by rfl) ⟨2901203, by rfl⟩ : syracuseStep 3868271 = 5802407) B5802407
theorem B1934959 : Blo 1719060 1934959 := bstep (se 1 (by rfl) ⟨1451219, by rfl⟩ : syracuseStep 1934959 = 2902439) B2902439
theorem B3098279 : Blo 1719060 3098279 := bstep (se 1 (by rfl) ⟨2323709, by rfl⟩ : syracuseStep 3098279 = 4647419) B4647419
theorem B2942647 : Blo 1719060 2942647 := bstep (se 1 (by rfl) ⟨2206985, by rfl⟩ : syracuseStep 2942647 = 4413971) B4413971
theorem B3868379 : Blo 1719060 3868379 := bstep (se 1 (by rfl) ⟨2901284, by rfl⟩ : syracuseStep 3868379 = 5802569) B5802569
theorem B1935067 : Blo 1719060 1935067 := bstep (se 1 (by rfl) ⟨1451300, by rfl⟩ : syracuseStep 1935067 = 2902601) B2902601
theorem B2901791 : Blo 1719060 2901791 := bstep (se 1 (by rfl) ⟨2176343, by rfl⟩ : syracuseStep 2901791 = 4352687) B4352687
theorem B3671905 : Blo 1719060 3671905 := bstep (se 2 (by rfl) ⟨1376964, by rfl⟩ : syracuseStep 3671905 = 2753929) B2753929
theorem B2902007 : Blo 1719060 2902007 := bstep (se 1 (by rfl) ⟨2176505, by rfl⟩ : syracuseStep 2902007 = 4353011) B4353011
theorem B5801975 : Blo 1719060 5801975 := bstep (se 1 (by rfl) ⟨4351481, by rfl⟩ : syracuseStep 5801975 = 8702963) B8702963
theorem B8710253 : Blo 1719060 8710253 := bstep (se 3 (by rfl) ⟨1633172, by rfl⟩ : syracuseStep 8710253 = 3266345) B3266345
theorem B1837247 : Blo 1719060 1837247 := bstep (se 1 (by rfl) ⟨1377935, by rfl⟩ : syracuseStep 1837247 = 2755871) B2755871
theorem B4188577 : Blo 1719060 4188577 := bstep (se 2 (by rfl) ⟨1570716, by rfl⟩ : syracuseStep 4188577 = 3141433) B3141433
theorem B9800129 : Blo 1719060 9800129 := bstep (se 2 (by rfl) ⟨3675048, by rfl⟩ : syracuseStep 9800129 = 7350097) B7350097
theorem B24807961 : Blo 1719060 24807961 := bstep (se 2 (by rfl) ⟨9302985, by rfl⟩ : syracuseStep 24807961 = 18605971) B18605971
theorem B3869495 : Blo 1719060 3869495 := bstep (se 1 (by rfl) ⟨2902121, by rfl⟩ : syracuseStep 3869495 = 5804243) B5804243
theorem B5802839 : Blo 1719060 5802839 := bstep (se 1 (by rfl) ⟨4352129, by rfl⟩ : syracuseStep 5802839 = 8704259) B8704259
theorem B3869675 : Blo 1719060 3869675 := bstep (se 1 (by rfl) ⟨2902256, by rfl⟩ : syracuseStep 3869675 = 5804513) B5804513
theorem B5803055 : Blo 1719060 5803055 := bstep (se 1 (by rfl) ⟨4352291, by rfl⟩ : syracuseStep 5803055 = 8704583) B8704583
theorem B3673135 : Blo 1719060 3673135 := bstep (se 1 (by rfl) ⟨2754851, by rfl⟩ : syracuseStep 3673135 = 5509703) B5509703
theorem B2903087 : Blo 1719060 2903087 := bstep (se 1 (by rfl) ⟨2177315, by rfl⟩ : syracuseStep 2903087 = 4354631) B4354631
theorem B2903161 : Blo 1719060 2903161 := bstep (se 2 (by rfl) ⟨1088685, by rfl⟩ : syracuseStep 2903161 = 2177371) B2177371
theorem B5508319 : Blo 1719060 5508319 := bstep (se 1 (by rfl) ⟨4131239, by rfl⟩ : syracuseStep 5508319 = 8262479) B8262479
theorem B7449965 : Blo 1719060 7449965 := bstep (se 3 (by rfl) ⟨1396868, by rfl⟩ : syracuseStep 7449965 = 2793737) B2793737
theorem B52989329 : Blo 1719060 52989329 := bstep (se 2 (by rfl) ⟨19870998, by rfl⟩ : syracuseStep 52989329 = 39741997) B39741997
theorem B5803433 : Blo 1719060 5803433 := bstep (se 2 (by rfl) ⟨2176287, by rfl⟩ : syracuseStep 5803433 = 4352575) B4352575
theorem B2903465 : Blo 1719060 2903465 := bstep (se 2 (by rfl) ⟨1088799, by rfl⟩ : syracuseStep 2903465 = 2177599) B2177599
theorem B4353527 : Blo 1719060 4353527 := bstep (se 1 (by rfl) ⟨3265145, by rfl⟩ : syracuseStep 4353527 = 6530291) B6530291
theorem B3264295 : Blo 1719060 3264295 := bstep (se 1 (by rfl) ⟨2448221, by rfl⟩ : syracuseStep 3264295 = 4896443) B4896443
theorem B3870503 : Blo 1719060 3870503 := bstep (se 1 (by rfl) ⟨2902877, by rfl⟩ : syracuseStep 3870503 = 5805755) B5805755
theorem B5508985 : Blo 1719060 5508985 := bstep (se 2 (by rfl) ⟨2065869, by rfl⟩ : syracuseStep 5508985 = 4131739) B4131739
theorem B5803919 : Blo 1719060 5803919 := bstep (se 1 (by rfl) ⟨4352939, by rfl⟩ : syracuseStep 5803919 = 8705879) B8705879
theorem B11767961 : Blo 1719060 11767961 := bstep (se 2 (by rfl) ⟨4412985, by rfl⟩ : syracuseStep 11767961 = 8825971) B8825971
theorem B5804297 : Blo 1719060 5804297 := bstep (se 2 (by rfl) ⟨2176611, by rfl⟩ : syracuseStep 5804297 = 4353223) B4353223
theorem B6533405 : Blo 1719060 6533405 := bstep (se 3 (by rfl) ⟨1225013, by rfl⟩ : syracuseStep 6533405 = 2450027) B2450027
theorem B4190519 : Blo 1719060 4190519 := bstep (se 1 (by rfl) ⟨3142889, by rfl⟩ : syracuseStep 4190519 = 6285779) B6285779
theorem B4354519 : Blo 1719060 4354519 := bstep (se 1 (by rfl) ⟨3265889, by rfl⟩ : syracuseStep 4354519 = 6531779) B6531779
theorem B6197753 : Blo 1719060 6197753 := bstep (se 2 (by rfl) ⟨2324157, by rfl⟩ : syracuseStep 6197753 = 4648315) B4648315
theorem B4354823 : Blo 1719060 4354823 := bstep (se 1 (by rfl) ⟨3266117, by rfl⟩ : syracuseStep 4354823 = 6532235) B6532235
theorem B3871529 : Blo 1719060 3871529 := bstep (se 2 (by rfl) ⟨1451823, by rfl⟩ : syracuseStep 3871529 = 2903647) B2903647
theorem B11023199 : Blo 1719060 11023199 := bstep (se 1 (by rfl) ⟨8267399, by rfl⟩ : syracuseStep 11023199 = 16534799) B16534799
theorem B7345025 : Blo 1719060 7345025 := bstep (se 2 (by rfl) ⟨2754384, by rfl⟩ : syracuseStep 7345025 = 5508769) B5508769
theorem B3724283 : Blo 1719060 3724283 := bstep (se 1 (by rfl) ⟨2793212, by rfl⟩ : syracuseStep 3724283 = 5586425) B5586425
theorem B9294857 : Blo 1719060 9294857 := bstep (se 2 (by rfl) ⟨3485571, by rfl⟩ : syracuseStep 9294857 = 6971143) B6971143
theorem B3871799 : Blo 1719060 3871799 := bstep (se 1 (by rfl) ⟨2903849, by rfl⟩ : syracuseStep 3871799 = 5807699) B5807699
theorem B3265609 : Blo 1719060 3265609 := bstep (se 2 (by rfl) ⟨1224603, by rfl⟩ : syracuseStep 3265609 = 2449207) B2449207
theorem B3871817 : Blo 1719060 3871817 := bstep (se 2 (by rfl) ⟨1451931, by rfl⟩ : syracuseStep 3871817 = 2903863) B2903863
theorem B22041679 : Blo 1719060 22041679 := bstep (se 1 (by rfl) ⟨16531259, by rfl⟩ : syracuseStep 22041679 = 33062519) B33062519
theorem B11023559 : Blo 1719060 11023559 := bstep (se 1 (by rfl) ⟨8267669, by rfl⟩ : syracuseStep 11023559 = 16535339) B16535339
theorem B5805431 : Blo 1719060 5805431 := bstep (se 1 (by rfl) ⟨4354073, by rfl⟩ : syracuseStep 5805431 = 8708147) B8708147
theorem B22042043 : Blo 1719060 22042043 := bstep (se 1 (by rfl) ⟨16531532, by rfl⟩ : syracuseStep 22042043 = 33063065) B33063065
theorem B9795005 : Blo 1719060 9795005 := bstep (se 3 (by rfl) ⟨1836563, by rfl⟩ : syracuseStep 9795005 = 3673127) B3673127
theorem B4355977 : Blo 1719060 4355977 := bstep (se 2 (by rfl) ⟨1633491, by rfl⟩ : syracuseStep 4355977 = 3266983) B3266983
theorem B8378327 : Blo 1719060 8378327 := bstep (se 1 (by rfl) ⟨6283745, by rfl⟩ : syracuseStep 8378327 = 12567491) B12567491
theorem B3266543 : Blo 1719060 3266543 := bstep (se 1 (by rfl) ⟨2449907, by rfl⟩ : syracuseStep 3266543 = 4899815) B4899815
theorem B4356089 : Blo 1719060 4356089 := bstep (se 2 (by rfl) ⟨1633533, by rfl⟩ : syracuseStep 4356089 = 3267067) B3267067
theorem B35321953 : Blo 1719060 35321953 := bstep (se 2 (by rfl) ⟨13245732, by rfl⟩ : syracuseStep 35321953 = 26491465) B26491465
theorem B8706203 : Blo 1719060 8706203 := bstep (se 1 (by rfl) ⟨6529652, by rfl⟩ : syracuseStep 8706203 = 13059305) B13059305
theorem B4356251 : Blo 1719060 4356251 := bstep (se 1 (by rfl) ⟨3267188, by rfl⟩ : syracuseStep 4356251 = 6534377) B6534377
theorem B5806241 : Blo 1719060 5806241 := bstep (se 2 (by rfl) ⟨2177340, by rfl⟩ : syracuseStep 5806241 = 4354681) B4354681
theorem B9795755 : Blo 1719060 9795755 := bstep (se 1 (by rfl) ⟨7346816, by rfl⟩ : syracuseStep 9795755 = 14693633) B14693633
theorem B2578667 : Blo 1719060 2578667 := bstep (se 1 (by rfl) ⟨1934000, by rfl⟩ : syracuseStep 2578667 = 3868001) B3868001
theorem B2578727 : Blo 1719060 2578727 := bstep (se 1 (by rfl) ⟨1934045, by rfl⟩ : syracuseStep 2578727 = 3868091) B3868091
theorem B2447663 : Blo 1719060 2447663 := bstep (se 1 (by rfl) ⟨1835747, by rfl⟩ : syracuseStep 2447663 = 3671495) B3671495
theorem B2578811 : Blo 1719060 2578811 := bstep (se 1 (by rfl) ⟨1934108, by rfl⟩ : syracuseStep 2578811 = 3868217) B3868217
theorem B5806511 : Blo 1719060 5806511 := bstep (se 1 (by rfl) ⟨4354883, by rfl⟩ : syracuseStep 5806511 = 8709767) B8709767
theorem B16521691 : Blo 1719060 16521691 := bstep (se 1 (by rfl) ⟨12391268, by rfl⟩ : syracuseStep 16521691 = 24782537) B24782537
theorem B2447977 : Blo 1719060 2447977 := bstep (se 2 (by rfl) ⟨917991, by rfl⟩ : syracuseStep 2447977 = 1835983) B1835983
theorem B2579081 : Blo 1719060 2579081 := bstep (se 2 (by rfl) ⟨967155, by rfl⟩ : syracuseStep 2579081 = 1934311) B1934311
theorem B23542447 : Blo 1719060 23542447 := bstep (se 1 (by rfl) ⟨17656835, by rfl⟩ : syracuseStep 23542447 = 35313671) B35313671
theorem B2579255 : Blo 1719060 2579255 := bstep (se 1 (by rfl) ⟨1934441, by rfl⟩ : syracuseStep 2579255 = 3868883) B3868883
theorem B1719131 : Blo 1719060 1719131 := bstep (se 1 (by rfl) ⟨1289348, by rfl⟩ : syracuseStep 1719131 = 2578697) B2578697
theorem B2579291 : Blo 1719060 2579291 := bstep (se 1 (by rfl) ⟨1934468, by rfl⟩ : syracuseStep 2579291 = 3868937) B3868937
theorem B1719199 : Blo 1719060 1719199 := bstep (se 1 (by rfl) ⟨1289399, by rfl⟩ : syracuseStep 1719199 = 2578799) B2578799
theorem B44063675 : Blo 1719060 44063675 := bstep (se 1 (by rfl) ⟨33047756, by rfl⟩ : syracuseStep 44063675 = 66095513) B66095513
theorem B2579435 : Blo 1719060 2579435 := bstep (se 1 (by rfl) ⟨1934576, by rfl⟩ : syracuseStep 2579435 = 3869153) B3869153
theorem B1719343 : Blo 1719060 1719343 := bstep (se 1 (by rfl) ⟨1289507, by rfl⟩ : syracuseStep 1719343 = 2579015) B2579015
theorem B24796205 : Blo 1719060 24796205 := bstep (se 3 (by rfl) ⟨4649288, by rfl⟩ : syracuseStep 24796205 = 9298577) B9298577
theorem B1719367 : Blo 1719060 1719367 := bstep (se 1 (by rfl) ⟨1289525, by rfl⟩ : syracuseStep 1719367 = 2579051) B2579051
theorem B6970493 : Blo 1719060 6970493 := bstep (se 3 (by rfl) ⟨1306967, by rfl⟩ : syracuseStep 6970493 = 2613935) B2613935
theorem B2579639 : Blo 1719060 2579639 := bstep (se 1 (by rfl) ⟨1934729, by rfl⟩ : syracuseStep 2579639 = 3869459) B3869459
theorem B1719519 : Blo 1719060 1719519 := bstep (se 1 (by rfl) ⟨1289639, by rfl⟩ : syracuseStep 1719519 = 2579279) B2579279
theorem B9796895 : Blo 1719060 9796895 := bstep (se 1 (by rfl) ⟨7347671, by rfl⟩ : syracuseStep 9796895 = 14695343) B14695343
theorem B7847207 : Blo 1719060 7847207 := bstep (se 1 (by rfl) ⟨5885405, by rfl⟩ : syracuseStep 7847207 = 11770811) B11770811
theorem B2579879 : Blo 1719060 2579879 := bstep (se 1 (by rfl) ⟨1934909, by rfl⟩ : syracuseStep 2579879 = 3869819) B3869819
theorem B1719783 : Blo 1719060 1719783 := bstep (se 1 (by rfl) ⟨1289837, by rfl⟩ : syracuseStep 1719783 = 2579675) B2579675
theorem B5807591 : Blo 1719060 5807591 := bstep (se 1 (by rfl) ⟨4355693, by rfl⟩ : syracuseStep 5807591 = 8711387) B8711387
theorem B2579963 : Blo 1719060 2579963 := bstep (se 1 (by rfl) ⟨1934972, by rfl⟩ : syracuseStep 2579963 = 3869945) B3869945
theorem B12394063 : Blo 1719060 12394063 := bstep (se 1 (by rfl) ⟨9295547, by rfl⟩ : syracuseStep 12394063 = 18591095) B18591095
theorem B1719899 : Blo 1719060 1719899 := bstep (se 1 (by rfl) ⟨1289924, by rfl⟩ : syracuseStep 1719899 = 2579849) B2579849
theorem B2580059 : Blo 1719060 2580059 := bstep (se 1 (by rfl) ⟨1935044, by rfl⟩ : syracuseStep 2580059 = 3870089) B3870089
theorem B2580143 : Blo 1719060 2580143 := bstep (se 1 (by rfl) ⟨1935107, by rfl⟩ : syracuseStep 2580143 = 3870215) B3870215
theorem B2580263 : Blo 1719060 2580263 := bstep (se 1 (by rfl) ⟨1935197, by rfl⟩ : syracuseStep 2580263 = 3870395) B3870395
theorem B12394295 : Blo 1719060 12394295 := bstep (se 1 (by rfl) ⟨9295721, by rfl⟩ : syracuseStep 12394295 = 18591443) B18591443
theorem B1720135 : Blo 1719060 1720135 := bstep (se 1 (by rfl) ⟨1290101, by rfl⟩ : syracuseStep 1720135 = 2580203) B2580203
theorem B2580347 : Blo 1719060 2580347 := bstep (se 1 (by rfl) ⟨1935260, by rfl⟩ : syracuseStep 2580347 = 3870521) B3870521
theorem B1720287 : Blo 1719060 1720287 := bstep (se 1 (by rfl) ⟨1290215, by rfl⟩ : syracuseStep 1720287 = 2580431) B2580431
theorem B47095937 : Blo 1719060 47095937 := bstep (se 2 (by rfl) ⟨17660976, by rfl⟩ : syracuseStep 47095937 = 35321953) B35321953
theorem B1720511 : Blo 1719060 1720511 := bstep (se 1 (by rfl) ⟨1290383, by rfl⟩ : syracuseStep 1720511 = 2580767) B2580767
theorem B1720527 : Blo 1719060 1720527 := bstep (se 1 (by rfl) ⟨1290395, by rfl⟩ : syracuseStep 1720527 = 2580791) B2580791
theorem B2793679 : Blo 1719060 2793679 := bstep (se 1 (by rfl) ⟨2095259, by rfl⟩ : syracuseStep 2793679 = 4190519) B4190519
theorem B1720575 : Blo 1719060 1720575 := bstep (se 1 (by rfl) ⟨1290431, by rfl⟩ : syracuseStep 1720575 = 2580863) B2580863
theorem B1720623 : Blo 1719060 1720623 := bstep (se 1 (by rfl) ⟨1290467, by rfl⟩ : syracuseStep 1720623 = 2580935) B2580935
theorem B18587981 : Blo 1719060 18587981 := bstep (se 3 (by rfl) ⟨3485246, by rfl⟩ : syracuseStep 18587981 = 6970493) B6970493
theorem B4899325 : Blo 1719060 4899325 := bstep (se 3 (by rfl) ⟨918623, by rfl⟩ : syracuseStep 4899325 = 1837247) B1837247
theorem B2581019 : Blo 1719060 2581019 := bstep (se 1 (by rfl) ⟨1935764, by rfl⟩ : syracuseStep 2581019 = 3871529) B3871529
theorem B1720859 : Blo 1719060 1720859 := bstep (se 1 (by rfl) ⟨1290644, by rfl⟩ : syracuseStep 1720859 = 2581289) B2581289
theorem B1720863 : Blo 1719060 1720863 := bstep (se 1 (by rfl) ⟨1290647, by rfl⟩ : syracuseStep 1720863 = 2581295) B2581295
theorem B7348799 : Blo 1719060 7348799 := bstep (se 1 (by rfl) ⟨5511599, by rfl⟩ : syracuseStep 7348799 = 11023199) B11023199
theorem B6619727 : Blo 1719060 6619727 := bstep (se 1 (by rfl) ⟨4964795, by rfl⟩ : syracuseStep 6619727 = 9929591) B9929591
theorem B1720943 : Blo 1719060 1720943 := bstep (se 1 (by rfl) ⟨1290707, by rfl⟩ : syracuseStep 1720943 = 2581415) B2581415
theorem B22028921 : Blo 1719060 22028921 := bstep (se 2 (by rfl) ⟨8260845, by rfl⟩ : syracuseStep 22028921 = 16521691) B16521691
theorem B2482855 : Blo 1719060 2482855 := bstep (se 1 (by rfl) ⟨1862141, by rfl⟩ : syracuseStep 2482855 = 3724283) B3724283
theorem B1720999 : Blo 1719060 1720999 := bstep (se 1 (by rfl) ⟨1290749, by rfl⟩ : syracuseStep 1720999 = 2581499) B2581499
theorem B2581199 : Blo 1719060 2581199 := bstep (se 1 (by rfl) ⟨1935899, by rfl⟩ : syracuseStep 2581199 = 3871799) B3871799
theorem B1721039 : Blo 1719060 1721039 := bstep (se 1 (by rfl) ⟨1290779, by rfl⟩ : syracuseStep 1721039 = 2581559) B2581559
theorem B2581211 : Blo 1719060 2581211 := bstep (se 1 (by rfl) ⟨1935908, by rfl⟩ : syracuseStep 2581211 = 3871817) B3871817
theorem B7349039 : Blo 1719060 7349039 := bstep (se 1 (by rfl) ⟨5511779, by rfl⟩ : syracuseStep 7349039 = 11023559) B11023559
theorem B6530003 : Blo 1719060 6530003 := bstep (se 1 (by rfl) ⟨4897502, by rfl⟩ : syracuseStep 6530003 = 9795005) B9795005
theorem B35324903 : Blo 1719060 35324903 := bstep (se 1 (by rfl) ⟨26493677, by rfl⟩ : syracuseStep 35324903 = 52987355) B52987355
theorem B9798671 : Blo 1719060 9798671 := bstep (se 1 (by rfl) ⟨7349003, by rfl⟩ : syracuseStep 9798671 = 14698007) B14698007
theorem B1934383 : Blo 1719060 1934383 := bstep (se 1 (by rfl) ⟨1450787, by rfl⟩ : syracuseStep 1934383 = 2901575) B2901575
theorem B2065519 : Blo 1719060 2065519 := bstep (se 1 (by rfl) ⟨1549139, by rfl⟩ : syracuseStep 2065519 = 3098279) B3098279
theorem B1934527 : Blo 1719060 1934527 := bstep (se 1 (by rfl) ⟨1450895, by rfl⟩ : syracuseStep 1934527 = 2901791) B2901791
theorem B3867983 : Blo 1719060 3867983 := bstep (se 1 (by rfl) ⟨2900987, by rfl⟩ : syracuseStep 3867983 = 5801975) B5801975
theorem B1934671 : Blo 1719060 1934671 := bstep (se 1 (by rfl) ⟨1451003, by rfl⟩ : syracuseStep 1934671 = 2902007) B2902007
theorem B3868073 : Blo 1719060 3868073 := bstep (se 2 (by rfl) ⟨1450527, by rfl⟩ : syracuseStep 3868073 = 2901055) B2901055
theorem B6530503 : Blo 1719060 6530503 := bstep (se 1 (by rfl) ⟨4897877, by rfl⟩ : syracuseStep 6530503 = 9795755) B9795755
theorem B3868559 : Blo 1719060 3868559 := bstep (se 1 (by rfl) ⟨2901419, by rfl⟩ : syracuseStep 3868559 = 5802839) B5802839
theorem B3868703 : Blo 1719060 3868703 := bstep (se 1 (by rfl) ⟨2901527, by rfl⟩ : syracuseStep 3868703 = 5803055) B5803055
theorem B1935391 : Blo 1719060 1935391 := bstep (se 1 (by rfl) ⟨1451543, by rfl⟩ : syracuseStep 1935391 = 2903087) B2903087
theorem B16525417 : Blo 1719060 16525417 := bstep (se 2 (by rfl) ⟨6197031, by rfl⟩ : syracuseStep 16525417 = 12394063) B12394063
theorem B6531263 : Blo 1719060 6531263 := bstep (se 1 (by rfl) ⟨4898447, by rfl⟩ : syracuseStep 6531263 = 9796895) B9796895
theorem B4966643 : Blo 1719060 4966643 := bstep (se 1 (by rfl) ⟨3724982, by rfl⟩ : syracuseStep 4966643 = 7449965) B7449965
theorem B35326219 : Blo 1719060 35326219 := bstep (se 1 (by rfl) ⟨26494664, by rfl⟩ : syracuseStep 35326219 = 52989329) B52989329
theorem B3868955 : Blo 1719060 3868955 := bstep (se 1 (by rfl) ⟨2901716, by rfl⟩ : syracuseStep 3868955 = 5803433) B5803433
theorem B1935643 : Blo 1719060 1935643 := bstep (se 1 (by rfl) ⟨1451732, by rfl⟩ : syracuseStep 1935643 = 2903465) B2903465
theorem B2902351 : Blo 1719060 2902351 := bstep (se 1 (by rfl) ⟨2176763, by rfl⟩ : syracuseStep 2902351 = 4353527) B4353527
theorem B4352393 : Blo 1719060 4352393 := bstep (se 2 (by rfl) ⟨1632147, by rfl⟩ : syracuseStep 4352393 = 3264295) B3264295
theorem B22342205 : Blo 1719060 22342205 := bstep (se 3 (by rfl) ⟨4189163, by rfl⟩ : syracuseStep 22342205 = 8378327) B8378327
theorem B3869279 : Blo 1719060 3869279 := bstep (se 1 (by rfl) ⟨2901959, by rfl⟩ : syracuseStep 3869279 = 5803919) B5803919
theorem B3869531 : Blo 1719060 3869531 := bstep (se 1 (by rfl) ⟨2902148, by rfl⟩ : syracuseStep 3869531 = 5804297) B5804297
theorem B107342779 : Blo 1719060 107342779 := bstep (se 1 (by rfl) ⟨80507084, by rfl⟩ : syracuseStep 107342779 = 161014169) B161014169
theorem B16526339 : Blo 1719060 16526339 := bstep (se 1 (by rfl) ⟨12394754, by rfl⟩ : syracuseStep 16526339 = 24789509) B24789509
theorem B2903215 : Blo 1719060 2903215 := bstep (se 1 (by rfl) ⟨2177411, by rfl⟩ : syracuseStep 2903215 = 4354823) B4354823
theorem B6196571 : Blo 1719060 6196571 := bstep (se 1 (by rfl) ⟨4647428, by rfl⟩ : syracuseStep 6196571 = 9294857) B9294857
theorem B3263969 : Blo 1719060 3263969 := bstep (se 2 (by rfl) ⟨1223988, by rfl⟩ : syracuseStep 3263969 = 2447977) B2447977
theorem B3870287 : Blo 1719060 3870287 := bstep (se 1 (by rfl) ⟨2902715, by rfl⟩ : syracuseStep 3870287 = 5805431) B5805431
theorem B6532751 : Blo 1719060 6532751 := bstep (se 1 (by rfl) ⟨4899563, by rfl⟩ : syracuseStep 6532751 = 9799127) B9799127
theorem B16527341 : Blo 1719060 16527341 := bstep (se 3 (by rfl) ⟨3098876, by rfl⟩ : syracuseStep 16527341 = 6197753) B6197753
theorem B2904059 : Blo 1719060 2904059 := bstep (se 1 (by rfl) ⟨2178044, by rfl⟩ : syracuseStep 2904059 = 4356089) B4356089
theorem B4354145 : Blo 1719060 4354145 := bstep (se 2 (by rfl) ⟨1632804, by rfl⟩ : syracuseStep 4354145 = 3265609) B3265609
theorem B5804135 : Blo 1719060 5804135 := bstep (se 1 (by rfl) ⟨4353101, by rfl⟩ : syracuseStep 5804135 = 8706203) B8706203
theorem B2904167 : Blo 1719060 2904167 := bstep (se 1 (by rfl) ⟨2178125, by rfl⟩ : syracuseStep 2904167 = 4356251) B4356251
theorem B29388905 : Blo 1719060 29388905 := bstep (se 2 (by rfl) ⟨11020839, by rfl⟩ : syracuseStep 29388905 = 22041679) B22041679
theorem B3870827 : Blo 1719060 3870827 := bstep (se 1 (by rfl) ⟨2903120, by rfl⟩ : syracuseStep 3870827 = 5806241) B5806241
theorem B3870881 : Blo 1719060 3870881 := bstep (se 2 (by rfl) ⟨1451580, by rfl⟩ : syracuseStep 3870881 = 2903161) B2903161
theorem B3871007 : Blo 1719060 3871007 := bstep (se 1 (by rfl) ⟨2903255, by rfl⟩ : syracuseStep 3871007 = 5806511) B5806511
theorem B7344425 : Blo 1719060 7344425 := bstep (se 2 (by rfl) ⟨2754159, by rfl⟩ : syracuseStep 7344425 = 5508319) B5508319
theorem B6533419 : Blo 1719060 6533419 := bstep (se 1 (by rfl) ⟨4900064, by rfl⟩ : syracuseStep 6533419 = 9800129) B9800129
theorem B5231471 : Blo 1719060 5231471 := bstep (se 1 (by rfl) ⟨3923603, by rfl⟩ : syracuseStep 5231471 = 7847207) B7847207
theorem B3871727 : Blo 1719060 3871727 := bstep (se 1 (by rfl) ⟨2903795, by rfl⟩ : syracuseStep 3871727 = 5807591) B5807591
theorem B4895873 : Blo 1719060 4895873 := bstep (se 2 (by rfl) ⟨1835952, by rfl⟩ : syracuseStep 4895873 = 3671905) B3671905
theorem B7345313 : Blo 1719060 7345313 := bstep (se 2 (by rfl) ⟨2754492, by rfl⟩ : syracuseStep 7345313 = 5508985) B5508985
theorem B8262863 : Blo 1719060 8262863 := bstep (se 1 (by rfl) ⟨6197147, by rfl⟩ : syracuseStep 8262863 = 12394295) B12394295
theorem B3872231 : Blo 1719060 3872231 := bstep (se 1 (by rfl) ⟨2904173, by rfl⟩ : syracuseStep 3872231 = 5808347) B5808347
theorem B4355603 : Blo 1719060 4355603 := bstep (se 1 (by rfl) ⟨3266702, by rfl⟩ : syracuseStep 4355603 = 6533405) B6533405
theorem B5805647 : Blo 1719060 5805647 := bstep (se 1 (by rfl) ⟨4354235, by rfl⟩ : syracuseStep 5805647 = 8708471) B8708471
theorem B31381229 : Blo 1719060 31381229 := bstep (se 3 (by rfl) ⟨5883980, by rfl⟩ : syracuseStep 31381229 = 11767961) B11767961
theorem B5511035 : Blo 1719060 5511035 := bstep (se 1 (by rfl) ⟨4133276, by rfl⟩ : syracuseStep 5511035 = 8266553) B8266553
theorem B5584769 : Blo 1719060 5584769 := bstep (se 2 (by rfl) ⟨2094288, by rfl⟩ : syracuseStep 5584769 = 4188577) B4188577
theorem B4896683 : Blo 1719060 4896683 := bstep (se 1 (by rfl) ⟨3672512, by rfl⟩ : syracuseStep 4896683 = 7345025) B7345025
theorem B5806025 : Blo 1719060 5806025 := bstep (se 2 (by rfl) ⟨2177259, by rfl⟩ : syracuseStep 5806025 = 4354519) B4354519
theorem B33077281 : Blo 1719060 33077281 := bstep (se 2 (by rfl) ⟨12403980, by rfl⟩ : syracuseStep 33077281 = 24807961) B24807961
theorem B6527101 : Blo 1719060 6527101 := bstep (se 3 (by rfl) ⟨1223831, by rfl⟩ : syracuseStep 6527101 = 2447663) B2447663
theorem B5806295 : Blo 1719060 5806295 := bstep (se 1 (by rfl) ⟨4354721, by rfl⟩ : syracuseStep 5806295 = 8709443) B8709443
theorem B31389929 : Blo 1719060 31389929 := bstep (se 2 (by rfl) ⟨11771223, by rfl⟩ : syracuseStep 31389929 = 23542447) B23542447
theorem B15694117 : Blo 1719060 15694117 := bstep (se 4 (by rfl) ⟨1471323, by rfl⟩ : syracuseStep 15694117 = 2942647) B2942647
theorem B14694695 : Blo 1719060 14694695 := bstep (se 1 (by rfl) ⟨11021021, by rfl⟩ : syracuseStep 14694695 = 22042043) B22042043
theorem B11016587 : Blo 1719060 11016587 := bstep (se 1 (by rfl) ⟨8262440, by rfl⟩ : syracuseStep 11016587 = 16524881) B16524881
theorem B2578847 : Blo 1719060 2578847 := bstep (se 1 (by rfl) ⟨1934135, by rfl⟩ : syracuseStep 2578847 = 3868271) B3868271
theorem B2578919 : Blo 1719060 2578919 := bstep (se 1 (by rfl) ⟨1934189, by rfl⟩ : syracuseStep 2578919 = 3868379) B3868379
theorem B2177695 : Blo 1719060 2177695 := bstep (se 1 (by rfl) ⟨1633271, by rfl⟩ : syracuseStep 2177695 = 3266543) B3266543
theorem B4897513 : Blo 1719060 4897513 := bstep (se 2 (by rfl) ⟨1836567, by rfl⟩ : syracuseStep 4897513 = 3673135) B3673135
theorem B5806835 : Blo 1719060 5806835 := bstep (se 1 (by rfl) ⟨4355126, by rfl⟩ : syracuseStep 5806835 = 8710253) B8710253
theorem B1719111 : Blo 1719060 1719111 := bstep (se 1 (by rfl) ⟨1289333, by rfl⟩ : syracuseStep 1719111 = 2578667) B2578667
theorem B1719151 : Blo 1719060 1719151 := bstep (se 1 (by rfl) ⟨1289363, by rfl⟩ : syracuseStep 1719151 = 2578727) B2578727
theorem B1719207 : Blo 1719060 1719207 := bstep (se 1 (by rfl) ⟨1289405, by rfl⟩ : syracuseStep 1719207 = 2578811) B2578811
theorem B1719387 : Blo 1719060 1719387 := bstep (se 1 (by rfl) ⟨1289540, by rfl⟩ : syracuseStep 1719387 = 2579081) B2579081
theorem B1719503 : Blo 1719060 1719503 := bstep (se 1 (by rfl) ⟨1289627, by rfl⟩ : syracuseStep 1719503 = 2579255) B2579255
theorem B2579663 : Blo 1719060 2579663 := bstep (se 1 (by rfl) ⟨1934747, by rfl⟩ : syracuseStep 2579663 = 3869495) B3869495
theorem B1719527 : Blo 1719060 1719527 := bstep (se 1 (by rfl) ⟨1289645, by rfl⟩ : syracuseStep 1719527 = 2579291) B2579291
theorem B29375783 : Blo 1719060 29375783 := bstep (se 1 (by rfl) ⟨22031837, by rfl⟩ : syracuseStep 29375783 = 44063675) B44063675
theorem B1719623 : Blo 1719060 1719623 := bstep (se 1 (by rfl) ⟨1289717, by rfl⟩ : syracuseStep 1719623 = 2579435) B2579435
theorem B2579783 : Blo 1719060 2579783 := bstep (se 1 (by rfl) ⟨1934837, by rfl⟩ : syracuseStep 2579783 = 3869675) B3869675
theorem B16530803 : Blo 1719060 16530803 := bstep (se 1 (by rfl) ⟨12398102, by rfl⟩ : syracuseStep 16530803 = 24796205) B24796205
theorem B1719759 : Blo 1719060 1719759 := bstep (se 1 (by rfl) ⟨1289819, by rfl⟩ : syracuseStep 1719759 = 2579639) B2579639
theorem B2579945 : Blo 1719060 2579945 := bstep (se 2 (by rfl) ⟨967479, by rfl⟩ : syracuseStep 2579945 = 1934959) B1934959
theorem B1719919 : Blo 1719060 1719919 := bstep (se 1 (by rfl) ⟨1289939, by rfl⟩ : syracuseStep 1719919 = 2579879) B2579879
theorem B2580089 : Blo 1719060 2580089 := bstep (se 2 (by rfl) ⟨967533, by rfl⟩ : syracuseStep 2580089 = 1935067) B1935067
theorem B1719975 : Blo 1719060 1719975 := bstep (se 1 (by rfl) ⟨1289981, by rfl⟩ : syracuseStep 1719975 = 2579963) B2579963
theorem B1720039 : Blo 1719060 1720039 := bstep (se 1 (by rfl) ⟨1290029, by rfl⟩ : syracuseStep 1720039 = 2580059) B2580059
theorem B1720095 : Blo 1719060 1720095 := bstep (se 1 (by rfl) ⟨1290071, by rfl⟩ : syracuseStep 1720095 = 2580143) B2580143
theorem B5807969 : Blo 1719060 5807969 := bstep (se 2 (by rfl) ⟨2177988, by rfl⟩ : syracuseStep 5807969 = 4355977) B4355977
theorem B1720175 : Blo 1719060 1720175 := bstep (se 1 (by rfl) ⟨1290131, by rfl⟩ : syracuseStep 1720175 = 2580263) B2580263
theorem B2580335 : Blo 1719060 2580335 := bstep (se 1 (by rfl) ⟨1935251, by rfl⟩ : syracuseStep 2580335 = 3870503) B3870503
theorem B15687557 : Blo 1719060 15687557 := bstep (se 4 (by rfl) ⟨1470708, by rfl⟩ : syracuseStep 15687557 = 2941417) B2941417
theorem B1720231 : Blo 1719060 1720231 := bstep (se 1 (by rfl) ⟨1290173, by rfl⟩ : syracuseStep 1720231 = 2580347) B2580347
theorem B2580521 : Blo 1719060 2580521 := bstep (se 2 (by rfl) ⟨967695, by rfl⟩ : syracuseStep 2580521 = 1935391) B1935391
theorem B2580551 : Blo 1719060 2580551 := bstep (se 1 (by rfl) ⟨1935413, by rfl⟩ : syracuseStep 2580551 = 3870827) B3870827
theorem B2580587 : Blo 1719060 2580587 := bstep (se 1 (by rfl) ⟨1935440, by rfl⟩ : syracuseStep 2580587 = 3870881) B3870881
theorem B2580671 : Blo 1719060 2580671 := bstep (se 1 (by rfl) ⟨1935503, by rfl⟩ : syracuseStep 2580671 = 3871007) B3871007
theorem B1720679 : Blo 1719060 1720679 := bstep (se 1 (by rfl) ⟨1290509, by rfl⟩ : syracuseStep 1720679 = 2581019) B2581019
theorem B2580857 : Blo 1719060 2580857 := bstep (se 2 (by rfl) ⟨967821, by rfl⟩ : syracuseStep 2580857 = 1935643) B1935643
theorem B4899199 : Blo 1719060 4899199 := bstep (se 1 (by rfl) ⟨3674399, by rfl⟩ : syracuseStep 4899199 = 7348799) B7348799
theorem B1720799 : Blo 1719060 1720799 := bstep (se 1 (by rfl) ⟨1290599, by rfl⟩ : syracuseStep 1720799 = 2581199) B2581199
theorem B1720807 : Blo 1719060 1720807 := bstep (se 1 (by rfl) ⟨1290605, by rfl⟩ : syracuseStep 1720807 = 2581211) B2581211
theorem B4899359 : Blo 1719060 4899359 := bstep (se 1 (by rfl) ⟨3674519, by rfl⟩ : syracuseStep 4899359 = 7349039) B7349039
theorem B2581151 : Blo 1719060 2581151 := bstep (se 1 (by rfl) ⟨1935863, by rfl⟩ : syracuseStep 2581151 = 3871727) B3871727
theorem B334807829 : Blo 1719060 334807829 := bstep (se 6 (by rfl) ⟨7847058, by rfl⟩ : syracuseStep 334807829 = 15694117) B15694117
theorem B6530017 : Blo 1719060 6530017 := bstep (se 2 (by rfl) ⟨2448756, by rfl⟩ : syracuseStep 6530017 = 4897513) B4897513
theorem B2581487 : Blo 1719060 2581487 := bstep (se 1 (by rfl) ⟨1936115, by rfl⟩ : syracuseStep 2581487 = 3872231) B3872231
theorem B143123705 : Blo 1719060 143123705 := bstep (se 2 (by rfl) ⟨53671389, by rfl⟩ : syracuseStep 143123705 = 107342779) B107342779
theorem B2901595 : Blo 1719060 2901595 := bstep (se 1 (by rfl) ⟨2176196, by rfl⟩ : syracuseStep 2901595 = 4352393) B4352393
theorem B14894803 : Blo 1719060 14894803 := bstep (se 1 (by rfl) ⟨11171102, by rfl⟩ : syracuseStep 14894803 = 22342205) B22342205
theorem B83683277 : Blo 1719060 83683277 := bstep (se 3 (by rfl) ⟨15690614, by rfl⟩ : syracuseStep 83683277 = 31381229) B31381229
theorem B4131047 : Blo 1719060 4131047 := bstep (se 1 (by rfl) ⟨3098285, by rfl⟩ : syracuseStep 4131047 = 6196571) B6196571
theorem B11020535 : Blo 1719060 11020535 := bstep (se 1 (by rfl) ⟨8265401, by rfl⟩ : syracuseStep 11020535 = 16530803) B16530803
theorem B1936039 : Blo 1719060 1936039 := bstep (se 1 (by rfl) ⟨1452029, by rfl⟩ : syracuseStep 1936039 = 2904059) B2904059
theorem B238283477 : Blo 1719060 238283477 := bstep (se 7 (by rfl) ⟨2792384, by rfl⟩ : syracuseStep 238283477 = 5584769) B5584769
theorem B2902763 : Blo 1719060 2902763 := bstep (se 1 (by rfl) ⟨2177072, by rfl⟩ : syracuseStep 2902763 = 4354145) B4354145
theorem B3869423 : Blo 1719060 3869423 := bstep (se 1 (by rfl) ⟨2902067, by rfl⟩ : syracuseStep 3869423 = 5804135) B5804135
theorem B1936111 : Blo 1719060 1936111 := bstep (se 1 (by rfl) ⟨1452083, by rfl⟩ : syracuseStep 1936111 = 2904167) B2904167
theorem B8702801 : Blo 1719060 8702801 := bstep (se 2 (by rfl) ⟨3263550, by rfl⟩ : syracuseStep 8702801 = 6527101) B6527101
theorem B8711225 : Blo 1719060 8711225 := bstep (se 2 (by rfl) ⟨3266709, by rfl⟩ : syracuseStep 8711225 = 6533419) B6533419
theorem B3869801 : Blo 1719060 3869801 := bstep (se 2 (by rfl) ⟨1451175, by rfl⟩ : syracuseStep 3869801 = 2902351) B2902351
theorem B4353335 : Blo 1719060 4353335 := bstep (se 1 (by rfl) ⟨3265001, by rfl⟩ : syracuseStep 4353335 = 6530003) B6530003
theorem B6532433 : Blo 1719060 6532433 := bstep (se 2 (by rfl) ⟨2449662, by rfl⟩ : syracuseStep 6532433 = 4899325) B4899325
theorem B6532447 : Blo 1719060 6532447 := bstep (se 1 (by rfl) ⟨4899335, by rfl⟩ : syracuseStep 6532447 = 9798671) B9798671
theorem B3263915 : Blo 1719060 3263915 := bstep (se 1 (by rfl) ⟨2447936, by rfl⟩ : syracuseStep 3263915 = 4895873) B4895873
theorem B5508575 : Blo 1719060 5508575 := bstep (se 1 (by rfl) ⟨4131431, by rfl⟩ : syracuseStep 5508575 = 8262863) B8262863
theorem B13241893 : Blo 1719060 13241893 := bstep (se 4 (by rfl) ⟨1241427, by rfl⟩ : syracuseStep 13241893 = 2482855) B2482855
theorem B2903593 : Blo 1719060 2903593 := bstep (se 2 (by rfl) ⟨1088847, by rfl⟩ : syracuseStep 2903593 = 2177695) B2177695
theorem B2903735 : Blo 1719060 2903735 := bstep (se 1 (by rfl) ⟨2177801, by rfl⟩ : syracuseStep 2903735 = 4355603) B4355603
theorem B3870431 : Blo 1719060 3870431 := bstep (se 1 (by rfl) ⟨2902823, by rfl⟩ : syracuseStep 3870431 = 5805647) B5805647
theorem B3264455 : Blo 1719060 3264455 := bstep (se 1 (by rfl) ⟨2448341, by rfl⟩ : syracuseStep 3264455 = 4896683) B4896683
theorem B3870683 : Blo 1719060 3870683 := bstep (se 1 (by rfl) ⟨2903012, by rfl⟩ : syracuseStep 3870683 = 5806025) B5806025
theorem B4354175 : Blo 1719060 4354175 := bstep (se 1 (by rfl) ⟨3265631, by rfl⟩ : syracuseStep 4354175 = 6531263) B6531263
theorem B3870863 : Blo 1719060 3870863 := bstep (se 1 (by rfl) ⟨2903147, by rfl⟩ : syracuseStep 3870863 = 5806295) B5806295
theorem B20926619 : Blo 1719060 20926619 := bstep (se 1 (by rfl) ⟨15694964, by rfl⟩ : syracuseStep 20926619 = 31389929) B31389929
theorem B3870953 : Blo 1719060 3870953 := bstep (se 2 (by rfl) ⟨1451607, by rfl⟩ : syracuseStep 3870953 = 2903215) B2903215
theorem B7344391 : Blo 1719060 7344391 := bstep (se 1 (by rfl) ⟨5508293, by rfl⟩ : syracuseStep 7344391 = 11016587) B11016587
theorem B3871223 : Blo 1719060 3871223 := bstep (se 1 (by rfl) ⟨2903417, by rfl⟩ : syracuseStep 3871223 = 5806835) B5806835
theorem B19583855 : Blo 1719060 19583855 := bstep (se 1 (by rfl) ⟨14687891, by rfl⟩ : syracuseStep 19583855 = 29375783) B29375783
theorem B2175979 : Blo 1719060 2175979 := bstep (se 1 (by rfl) ⟨1631984, by rfl⟩ : syracuseStep 2175979 = 3263969) B3263969
theorem B4355167 : Blo 1719060 4355167 := bstep (se 1 (by rfl) ⟨3266375, by rfl⟩ : syracuseStep 4355167 = 6532751) B6532751
theorem B3871979 : Blo 1719060 3871979 := bstep (se 1 (by rfl) ⟨2903984, by rfl⟩ : syracuseStep 3871979 = 5807969) B5807969
theorem B10458371 : Blo 1719060 10458371 := bstep (se 1 (by rfl) ⟨7843778, by rfl⟩ : syracuseStep 10458371 = 15687557) B15687557
theorem B44103041 : Blo 1719060 44103041 := bstep (se 2 (by rfl) ⟨16538640, by rfl⟩ : syracuseStep 44103041 = 33077281) B33077281
theorem B19592603 : Blo 1719060 19592603 := bstep (se 1 (by rfl) ⟨14694452, by rfl⟩ : syracuseStep 19592603 = 29388905) B29388905
theorem B31397291 : Blo 1719060 31397291 := bstep (se 1 (by rfl) ⟨23547968, by rfl⟩ : syracuseStep 31397291 = 47095937) B47095937
theorem B22033889 : Blo 1719060 22033889 := bstep (se 2 (by rfl) ⟨8262708, by rfl⟩ : syracuseStep 22033889 = 16525417) B16525417
theorem B4896283 : Blo 1719060 4896283 := bstep (se 1 (by rfl) ⟨3672212, by rfl⟩ : syracuseStep 4896283 = 7344425) B7344425
theorem B12391987 : Blo 1719060 12391987 := bstep (se 1 (by rfl) ⟨9293990, by rfl⟩ : syracuseStep 12391987 = 18587981) B18587981
theorem B47101625 : Blo 1719060 47101625 := bstep (se 2 (by rfl) ⟨17663109, by rfl⟩ : syracuseStep 47101625 = 35326219) B35326219
theorem B4413151 : Blo 1719060 4413151 := bstep (se 1 (by rfl) ⟨3309863, by rfl⟩ : syracuseStep 4413151 = 6619727) B6619727
theorem B14685947 : Blo 1719060 14685947 := bstep (se 1 (by rfl) ⟨11014460, by rfl⟩ : syracuseStep 14685947 = 22028921) B22028921
theorem B11016101 : Blo 1719060 11016101 := bstep (se 4 (by rfl) ⟨1032759, by rfl⟩ : syracuseStep 11016101 = 2065519) B2065519
theorem B13244381 : Blo 1719060 13244381 := bstep (se 3 (by rfl) ⟨2483321, by rfl⟩ : syracuseStep 13244381 = 4966643) B4966643
theorem B23549935 : Blo 1719060 23549935 := bstep (se 1 (by rfl) ⟨17662451, by rfl⟩ : syracuseStep 23549935 = 35324903) B35324903
theorem B4896875 : Blo 1719060 4896875 := bstep (se 1 (by rfl) ⟨3672656, by rfl⟩ : syracuseStep 4896875 = 7345313) B7345313
theorem B2578655 : Blo 1719060 2578655 := bstep (se 1 (by rfl) ⟨1933991, by rfl⟩ : syracuseStep 2578655 = 3867983) B3867983
theorem B2578715 : Blo 1719060 2578715 := bstep (se 1 (by rfl) ⟨1934036, by rfl⟩ : syracuseStep 2578715 = 3868073) B3868073
theorem B14899621 : Blo 1719060 14899621 := bstep (se 4 (by rfl) ⟨1396839, by rfl⟩ : syracuseStep 14899621 = 2793679) B2793679
theorem B2579039 : Blo 1719060 2579039 := bstep (se 1 (by rfl) ⟨1934279, by rfl⟩ : syracuseStep 2579039 = 3868559) B3868559
theorem B2579135 : Blo 1719060 2579135 := bstep (se 1 (by rfl) ⟨1934351, by rfl⟩ : syracuseStep 2579135 = 3868703) B3868703
theorem B2579177 : Blo 1719060 2579177 := bstep (se 2 (by rfl) ⟨967191, by rfl⟩ : syracuseStep 2579177 = 1934383) B1934383
theorem B2579303 : Blo 1719060 2579303 := bstep (se 1 (by rfl) ⟨1934477, by rfl⟩ : syracuseStep 2579303 = 3868955) B3868955
theorem B9796463 : Blo 1719060 9796463 := bstep (se 1 (by rfl) ⟨7347347, by rfl⟩ : syracuseStep 9796463 = 14694695) B14694695
theorem B2579369 : Blo 1719060 2579369 := bstep (se 2 (by rfl) ⟨967263, by rfl⟩ : syracuseStep 2579369 = 1934527) B1934527
theorem B1719231 : Blo 1719060 1719231 := bstep (se 1 (by rfl) ⟨1289423, by rfl⟩ : syracuseStep 1719231 = 2578847) B2578847
theorem B1719279 : Blo 1719060 1719279 := bstep (se 1 (by rfl) ⟨1289459, by rfl⟩ : syracuseStep 1719279 = 2578919) B2578919
theorem B2579519 : Blo 1719060 2579519 := bstep (se 1 (by rfl) ⟨1934639, by rfl⟩ : syracuseStep 2579519 = 3869279) B3869279
theorem B2579561 : Blo 1719060 2579561 := bstep (se 2 (by rfl) ⟨967335, by rfl⟩ : syracuseStep 2579561 = 1934671) B1934671
theorem B2579687 : Blo 1719060 2579687 := bstep (se 1 (by rfl) ⟨1934765, by rfl⟩ : syracuseStep 2579687 = 3869531) B3869531
theorem B8707337 : Blo 1719060 8707337 := bstep (se 2 (by rfl) ⟨3265251, by rfl⟩ : syracuseStep 8707337 = 6530503) B6530503
theorem B11017559 : Blo 1719060 11017559 := bstep (se 1 (by rfl) ⟨8263169, by rfl⟩ : syracuseStep 11017559 = 16526339) B16526339
theorem B1719775 : Blo 1719060 1719775 := bstep (se 1 (by rfl) ⟨1289831, by rfl⟩ : syracuseStep 1719775 = 2579663) B2579663
theorem B1719855 : Blo 1719060 1719855 := bstep (se 1 (by rfl) ⟨1289891, by rfl⟩ : syracuseStep 1719855 = 2579783) B2579783
theorem B13950589 : Blo 1719060 13950589 := bstep (se 3 (by rfl) ⟨2615735, by rfl⟩ : syracuseStep 13950589 = 5231471) B5231471
theorem B1719963 : Blo 1719060 1719963 := bstep (se 1 (by rfl) ⟨1289972, by rfl⟩ : syracuseStep 1719963 = 2579945) B2579945
theorem B14696093 : Blo 1719060 14696093 := bstep (se 3 (by rfl) ⟨2755517, by rfl⟩ : syracuseStep 14696093 = 5511035) B5511035
theorem B2580191 : Blo 1719060 2580191 := bstep (se 1 (by rfl) ⟨1935143, by rfl⟩ : syracuseStep 2580191 = 3870287) B3870287
theorem B1720059 : Blo 1719060 1720059 := bstep (se 1 (by rfl) ⟨1290044, by rfl⟩ : syracuseStep 1720059 = 2580089) B2580089
theorem B1720223 : Blo 1719060 1720223 := bstep (se 1 (by rfl) ⟨1290167, by rfl⟩ : syracuseStep 1720223 = 2580335) B2580335
theorem B11018227 : Blo 1719060 11018227 := bstep (se 1 (by rfl) ⟨8263670, by rfl⟩ : syracuseStep 11018227 = 16527341) B16527341
theorem B1720347 : Blo 1719060 1720347 := bstep (se 1 (by rfl) ⟨1290260, by rfl⟩ : syracuseStep 1720347 = 2580521) B2580521
theorem B1720367 : Blo 1719060 1720367 := bstep (se 1 (by rfl) ⟨1290275, by rfl⟩ : syracuseStep 1720367 = 2580551) B2580551
theorem B1720391 : Blo 1719060 1720391 := bstep (se 1 (by rfl) ⟨1290293, by rfl⟩ : syracuseStep 1720391 = 2580587) B2580587
theorem B2580575 : Blo 1719060 2580575 := bstep (se 1 (by rfl) ⟨1935431, by rfl⟩ : syracuseStep 2580575 = 3870863) B3870863
theorem B13951079 : Blo 1719060 13951079 := bstep (se 1 (by rfl) ⟨10463309, by rfl⟩ : syracuseStep 13951079 = 20926619) B20926619
theorem B1720447 : Blo 1719060 1720447 := bstep (se 1 (by rfl) ⟨1290335, by rfl⟩ : syracuseStep 1720447 = 2580671) B2580671
theorem B2580635 : Blo 1719060 2580635 := bstep (se 1 (by rfl) ⟨1935476, by rfl⟩ : syracuseStep 2580635 = 3870953) B3870953
theorem B1720571 : Blo 1719060 1720571 := bstep (se 1 (by rfl) ⟨1290428, by rfl⟩ : syracuseStep 1720571 = 2580857) B2580857
theorem B13058333 : Blo 1719060 13058333 := bstep (se 3 (by rfl) ⟨2448437, by rfl⟩ : syracuseStep 13058333 = 4896875) B4896875
theorem B2580815 : Blo 1719060 2580815 := bstep (se 1 (by rfl) ⟨1935611, by rfl⟩ : syracuseStep 2580815 = 3871223) B3871223
theorem B1720767 : Blo 1719060 1720767 := bstep (se 1 (by rfl) ⟨1290575, by rfl⟩ : syracuseStep 1720767 = 2581151) B2581151
theorem B19866161 : Blo 1719060 19866161 := bstep (se 2 (by rfl) ⟨7449810, by rfl⟩ : syracuseStep 19866161 = 14899621) B14899621
theorem B1720991 : Blo 1719060 1720991 := bstep (se 1 (by rfl) ⟨1290743, by rfl⟩ : syracuseStep 1720991 = 2581487) B2581487
theorem B2581319 : Blo 1719060 2581319 := bstep (se 1 (by rfl) ⟨1935989, by rfl⟩ : syracuseStep 2581319 = 3871979) B3871979
theorem B6972247 : Blo 1719060 6972247 := bstep (se 1 (by rfl) ⟨5229185, by rfl⟩ : syracuseStep 6972247 = 10458371) B10458371
theorem B2581385 : Blo 1719060 2581385 := bstep (se 2 (by rfl) ⟨968019, by rfl⟩ : syracuseStep 2581385 = 1936039) B1936039
theorem B29402027 : Blo 1719060 29402027 := bstep (se 1 (by rfl) ⟨22051520, by rfl⟩ : syracuseStep 29402027 = 44103041) B44103041
theorem B20931527 : Blo 1719060 20931527 := bstep (se 1 (by rfl) ⟨15698645, by rfl⟩ : syracuseStep 20931527 = 31397291) B31397291
theorem B2581481 : Blo 1719060 2581481 := bstep (se 2 (by rfl) ⟨968055, by rfl⟩ : syracuseStep 2581481 = 1936111) B1936111
theorem B14689259 : Blo 1719060 14689259 := bstep (se 1 (by rfl) ⟨11016944, by rfl⟩ : syracuseStep 14689259 = 22033889) B22033889
theorem B31401083 : Blo 1719060 31401083 := bstep (se 1 (by rfl) ⟨23550812, by rfl⟩ : syracuseStep 31401083 = 47101625) B47101625
theorem B9790631 : Blo 1719060 9790631 := bstep (se 1 (by rfl) ⟨7342973, by rfl⟩ : syracuseStep 9790631 = 14685947) B14685947
theorem B55788851 : Blo 1719060 55788851 := bstep (se 1 (by rfl) ⟨41841638, by rfl⟩ : syracuseStep 55788851 = 83683277) B83683277
theorem B2901305 : Blo 1719060 2901305 := bstep (se 2 (by rfl) ⟨1087989, by rfl⟩ : syracuseStep 2901305 = 2175979) B2175979
theorem B8709929 : Blo 1719060 8709929 := bstep (se 2 (by rfl) ⟨3266223, by rfl⟩ : syracuseStep 8709929 = 6532447) B6532447
theorem B1935175 : Blo 1719060 1935175 := bstep (se 1 (by rfl) ⟨1451381, by rfl⟩ : syracuseStep 1935175 = 2902763) B2902763
theorem B5801867 : Blo 1719060 5801867 := bstep (se 1 (by rfl) ⟨4351400, by rfl⟩ : syracuseStep 5801867 = 8702801) B8702801
theorem B6530975 : Blo 1719060 6530975 := bstep (se 1 (by rfl) ⟨4898231, by rfl⟩ : syracuseStep 6530975 = 9796463) B9796463
theorem B17655857 : Blo 1719060 17655857 := bstep (se 2 (by rfl) ⟨6620946, by rfl⟩ : syracuseStep 17655857 = 13241893) B13241893
theorem B3868793 : Blo 1719060 3868793 := bstep (se 2 (by rfl) ⟨1450797, by rfl⟩ : syracuseStep 3868793 = 2901595) B2901595
theorem B2902223 : Blo 1719060 2902223 := bstep (se 1 (by rfl) ⟨2176667, by rfl⟩ : syracuseStep 2902223 = 4353335) B4353335
theorem B19859737 : Blo 1719060 19859737 := bstep (se 2 (by rfl) ⟨7447401, by rfl⟩ : syracuseStep 19859737 = 14894803) B14894803
theorem B5884201 : Blo 1719060 5884201 := bstep (se 2 (by rfl) ⟨2206575, by rfl⟩ : syracuseStep 5884201 = 4413151) B4413151
theorem B3672383 : Blo 1719060 3672383 := bstep (se 1 (by rfl) ⟨2754287, by rfl⟩ : syracuseStep 3672383 = 5508575) B5508575
theorem B1935823 : Blo 1719060 1935823 := bstep (se 1 (by rfl) ⟨1451867, by rfl⟩ : syracuseStep 1935823 = 2903735) B2903735
theorem B14690969 : Blo 1719060 14690969 := bstep (se 2 (by rfl) ⟨5509113, by rfl⟩ : syracuseStep 14690969 = 11018227) B11018227
theorem B2902783 : Blo 1719060 2902783 := bstep (se 1 (by rfl) ⟨2177087, by rfl⟩ : syracuseStep 2902783 = 4354175) B4354175
theorem B9792521 : Blo 1719060 9792521 := bstep (se 2 (by rfl) ⟨3672195, by rfl⟩ : syracuseStep 9792521 = 7344391) B7344391
theorem B6532265 : Blo 1719060 6532265 := bstep (se 2 (by rfl) ⟨2449599, by rfl⟩ : syracuseStep 6532265 = 4899199) B4899199
theorem B95415803 : Blo 1719060 95415803 := bstep (se 1 (by rfl) ⟨71561852, by rfl⟩ : syracuseStep 95415803 = 143123705) B143123705
theorem B29380157 : Blo 1719060 29380157 := bstep (se 3 (by rfl) ⟨5508779, by rfl⟩ : syracuseStep 29380157 = 11017559) B11017559
theorem B13061735 : Blo 1719060 13061735 := bstep (se 1 (by rfl) ⟨9796301, by rfl⟩ : syracuseStep 13061735 = 19592603) B19592603
theorem B8703773 : Blo 1719060 8703773 := bstep (se 3 (by rfl) ⟨1631957, by rfl⟩ : syracuseStep 8703773 = 3263915) B3263915
theorem B7344067 : Blo 1719060 7344067 := bstep (se 1 (by rfl) ⟨5508050, by rfl⟩ : syracuseStep 7344067 = 11016101) B11016101
theorem B158855651 : Blo 1719060 158855651 := bstep (se 1 (by rfl) ⟨119141738, by rfl⟩ : syracuseStep 158855651 = 238283477) B238283477
theorem B3871457 : Blo 1719060 3871457 := bstep (se 2 (by rfl) ⟨1451796, by rfl⟩ : syracuseStep 3871457 = 2903593) B2903593
theorem B18600785 : Blo 1719060 18600785 := bstep (se 2 (by rfl) ⟨6975294, by rfl⟩ : syracuseStep 18600785 = 13950589) B13950589
theorem B5804891 : Blo 1719060 5804891 := bstep (se 1 (by rfl) ⟨4353668, by rfl⟩ : syracuseStep 5804891 = 8707337) B8707337
theorem B4354955 : Blo 1719060 4354955 := bstep (se 1 (by rfl) ⟨3266216, by rfl⟩ : syracuseStep 4354955 = 6532433) B6532433
theorem B2176303 : Blo 1719060 2176303 := bstep (se 1 (by rfl) ⟨1632227, by rfl⟩ : syracuseStep 2176303 = 3264455) B3264455
theorem B3266239 : Blo 1719060 3266239 := bstep (se 1 (by rfl) ⟨2449679, by rfl⟩ : syracuseStep 3266239 = 4899359) B4899359
theorem B223205219 : Blo 1719060 223205219 := bstep (se 1 (by rfl) ⟨167403914, by rfl⟩ : syracuseStep 223205219 = 334807829) B334807829
theorem B13055903 : Blo 1719060 13055903 := bstep (se 1 (by rfl) ⟨9791927, by rfl⟩ : syracuseStep 13055903 = 19583855) B19583855
theorem B11016125 : Blo 1719060 11016125 := bstep (se 3 (by rfl) ⟨2065523, by rfl⟩ : syracuseStep 11016125 = 4131047) B4131047
theorem B8706689 : Blo 1719060 8706689 := bstep (se 2 (by rfl) ⟨3265008, by rfl⟩ : syracuseStep 8706689 = 6530017) B6530017
theorem B8829587 : Blo 1719060 8829587 := bstep (se 1 (by rfl) ⟨6622190, by rfl⟩ : syracuseStep 8829587 = 13244381) B13244381
theorem B5806889 : Blo 1719060 5806889 := bstep (se 2 (by rfl) ⟨2177583, by rfl⟩ : syracuseStep 5806889 = 4355167) B4355167
theorem B1719103 : Blo 1719060 1719103 := bstep (se 1 (by rfl) ⟨1289327, by rfl⟩ : syracuseStep 1719103 = 2578655) B2578655
theorem B7347023 : Blo 1719060 7347023 := bstep (se 1 (by rfl) ⟨5510267, by rfl⟩ : syracuseStep 7347023 = 11020535) B11020535
theorem B1719143 : Blo 1719060 1719143 := bstep (se 1 (by rfl) ⟨1289357, by rfl⟩ : syracuseStep 1719143 = 2578715) B2578715
theorem B1719359 : Blo 1719060 1719359 := bstep (se 1 (by rfl) ⟨1289519, by rfl⟩ : syracuseStep 1719359 = 2579039) B2579039
theorem B1719423 : Blo 1719060 1719423 := bstep (se 1 (by rfl) ⟨1289567, by rfl⟩ : syracuseStep 1719423 = 2579135) B2579135
theorem B1719451 : Blo 1719060 1719451 := bstep (se 1 (by rfl) ⟨1289588, by rfl⟩ : syracuseStep 1719451 = 2579177) B2579177
theorem B2579615 : Blo 1719060 2579615 := bstep (se 1 (by rfl) ⟨1934711, by rfl⟩ : syracuseStep 2579615 = 3869423) B3869423
theorem B1719535 : Blo 1719060 1719535 := bstep (se 1 (by rfl) ⟨1289651, by rfl⟩ : syracuseStep 1719535 = 2579303) B2579303
theorem B1719579 : Blo 1719060 1719579 := bstep (se 1 (by rfl) ⟨1289684, by rfl⟩ : syracuseStep 1719579 = 2579369) B2579369
theorem B6528377 : Blo 1719060 6528377 := bstep (se 2 (by rfl) ⟨2448141, by rfl⟩ : syracuseStep 6528377 = 4896283) B4896283
theorem B5807483 : Blo 1719060 5807483 := bstep (se 1 (by rfl) ⟨4355612, by rfl⟩ : syracuseStep 5807483 = 8711225) B8711225
theorem B1719679 : Blo 1719060 1719679 := bstep (se 1 (by rfl) ⟨1289759, by rfl⟩ : syracuseStep 1719679 = 2579519) B2579519
theorem B16522649 : Blo 1719060 16522649 := bstep (se 2 (by rfl) ⟨6195993, by rfl⟩ : syracuseStep 16522649 = 12391987) B12391987
theorem B1719707 : Blo 1719060 1719707 := bstep (se 1 (by rfl) ⟨1289780, by rfl⟩ : syracuseStep 1719707 = 2579561) B2579561
theorem B2579867 : Blo 1719060 2579867 := bstep (se 1 (by rfl) ⟨1934900, by rfl⟩ : syracuseStep 2579867 = 3869801) B3869801
theorem B1719791 : Blo 1719060 1719791 := bstep (se 1 (by rfl) ⟨1289843, by rfl⟩ : syracuseStep 1719791 = 2579687) B2579687
theorem B9797395 : Blo 1719060 9797395 := bstep (se 1 (by rfl) ⟨7348046, by rfl⟩ : syracuseStep 9797395 = 14696093) B14696093
theorem B1720127 : Blo 1719060 1720127 := bstep (se 1 (by rfl) ⟨1290095, by rfl⟩ : syracuseStep 1720127 = 2580191) B2580191
theorem B2580287 : Blo 1719060 2580287 := bstep (se 1 (by rfl) ⟨1935215, by rfl⟩ : syracuseStep 2580287 = 3870431) B3870431
theorem B2580455 : Blo 1719060 2580455 := bstep (se 1 (by rfl) ⟨1935341, by rfl⟩ : syracuseStep 2580455 = 3870683) B3870683
theorem B31399913 : Blo 1719060 31399913 := bstep (se 2 (by rfl) ⟨11774967, by rfl⟩ : syracuseStep 31399913 = 23549935) B23549935
theorem B1720383 : Blo 1719060 1720383 := bstep (se 1 (by rfl) ⟨1290287, by rfl⟩ : syracuseStep 1720383 = 2580575) B2580575
theorem B1720423 : Blo 1719060 1720423 := bstep (se 1 (by rfl) ⟨1290317, by rfl⟩ : syracuseStep 1720423 = 2580635) B2580635
theorem B1720543 : Blo 1719060 1720543 := bstep (se 1 (by rfl) ⟨1290407, by rfl⟩ : syracuseStep 1720543 = 2580815) B2580815
theorem B2580971 : Blo 1719060 2580971 := bstep (se 1 (by rfl) ⟨1935728, by rfl⟩ : syracuseStep 2580971 = 3871457) B3871457
theorem B1720879 : Blo 1719060 1720879 := bstep (se 1 (by rfl) ⟨1290659, by rfl⟩ : syracuseStep 1720879 = 2581319) B2581319
theorem B1720923 : Blo 1719060 1720923 := bstep (se 1 (by rfl) ⟨1290692, by rfl⟩ : syracuseStep 1720923 = 2581385) B2581385
theorem B2581097 : Blo 1719060 2581097 := bstep (se 2 (by rfl) ⟨967911, by rfl⟩ : syracuseStep 2581097 = 1935823) B1935823
theorem B1720987 : Blo 1719060 1720987 := bstep (se 1 (by rfl) ⟨1290740, by rfl⟩ : syracuseStep 1720987 = 2581481) B2581481
theorem B37192567 : Blo 1719060 37192567 := bstep (se 1 (by rfl) ⟨27894425, by rfl⟩ : syracuseStep 37192567 = 55788851) B55788851
theorem B1934203 : Blo 1719060 1934203 := bstep (se 1 (by rfl) ⟨1450652, by rfl⟩ : syracuseStep 1934203 = 2901305) B2901305
theorem B3867911 : Blo 1719060 3867911 := bstep (se 1 (by rfl) ⟨2900933, by rfl⟩ : syracuseStep 3867911 = 5801867) B5801867
theorem B1934815 : Blo 1719060 1934815 := bstep (se 1 (by rfl) ⟨1451111, by rfl⟩ : syracuseStep 1934815 = 2902223) B2902223
theorem B2901737 : Blo 1719060 2901737 := bstep (se 2 (by rfl) ⟨1088151, by rfl⟩ : syracuseStep 2901737 = 2176303) B2176303
theorem B4352251 : Blo 1719060 4352251 := bstep (se 1 (by rfl) ⟨3264188, by rfl⟩ : syracuseStep 4352251 = 6528377) B6528377
theorem B5802515 : Blo 1719060 5802515 := bstep (se 1 (by rfl) ⟨4351886, by rfl⟩ : syracuseStep 5802515 = 8703773) B8703773
theorem B9792089 : Blo 1719060 9792089 := bstep (se 2 (by rfl) ⟨3672033, by rfl⟩ : syracuseStep 9792089 = 7344067) B7344067
theorem B83733101 : Blo 1719060 83733101 := bstep (se 3 (by rfl) ⟨15699956, by rfl⟩ : syracuseStep 83733101 = 31399913) B31399913
theorem B9300719 : Blo 1719060 9300719 := bstep (se 1 (by rfl) ⟨6975539, by rfl⟩ : syracuseStep 9300719 = 13951079) B13951079
theorem B26479649 : Blo 1719060 26479649 := bstep (se 2 (by rfl) ⟨9929868, by rfl⟩ : syracuseStep 26479649 = 19859737) B19859737
theorem B3869927 : Blo 1719060 3869927 := bstep (se 1 (by rfl) ⟨2902445, by rfl⟩ : syracuseStep 3869927 = 5804891) B5804891
theorem B2903303 : Blo 1719060 2903303 := bstep (se 1 (by rfl) ⟨2177477, by rfl⟩ : syracuseStep 2903303 = 4354955) B4354955
theorem B13954351 : Blo 1719060 13954351 := bstep (se 1 (by rfl) ⟨10465763, by rfl⟩ : syracuseStep 13954351 = 20931527) B20931527
theorem B9792839 : Blo 1719060 9792839 := bstep (se 1 (by rfl) ⟨7344629, by rfl⟩ : syracuseStep 9792839 = 14689259) B14689259
theorem B20934055 : Blo 1719060 20934055 := bstep (se 1 (by rfl) ⟨15700541, by rfl⟩ : syracuseStep 20934055 = 31401083) B31401083
theorem B9793021 : Blo 1719060 9793021 := bstep (se 3 (by rfl) ⟨1836191, by rfl⟩ : syracuseStep 9793021 = 3672383) B3672383
theorem B3870377 : Blo 1719060 3870377 := bstep (se 2 (by rfl) ⟨1451391, by rfl⟩ : syracuseStep 3870377 = 2902783) B2902783
theorem B148803479 : Blo 1719060 148803479 := bstep (se 1 (by rfl) ⟨111602609, by rfl⟩ : syracuseStep 148803479 = 223205219) B223205219
theorem B8703935 : Blo 1719060 8703935 := bstep (se 1 (by rfl) ⟨6527951, by rfl⟩ : syracuseStep 8703935 = 13055903) B13055903
theorem B4353983 : Blo 1719060 4353983 := bstep (se 1 (by rfl) ⟨3265487, by rfl⟩ : syracuseStep 4353983 = 6530975) B6530975
theorem B7344083 : Blo 1719060 7344083 := bstep (se 1 (by rfl) ⟨5508062, by rfl⟩ : syracuseStep 7344083 = 11016125) B11016125
theorem B5804459 : Blo 1719060 5804459 := bstep (se 1 (by rfl) ⟨4353344, by rfl⟩ : syracuseStep 5804459 = 8706689) B8706689
theorem B5886391 : Blo 1719060 5886391 := bstep (se 1 (by rfl) ⟨4414793, by rfl⟩ : syracuseStep 5886391 = 8829587) B8829587
theorem B9793979 : Blo 1719060 9793979 := bstep (se 1 (by rfl) ⟨7345484, by rfl⟩ : syracuseStep 9793979 = 14690969) B14690969
theorem B3871259 : Blo 1719060 3871259 := bstep (se 1 (by rfl) ⟨2903444, by rfl⟩ : syracuseStep 3871259 = 5806889) B5806889
theorem B4354843 : Blo 1719060 4354843 := bstep (se 1 (by rfl) ⟨3266132, by rfl⟩ : syracuseStep 4354843 = 6532265) B6532265
theorem B3871655 : Blo 1719060 3871655 := bstep (se 1 (by rfl) ⟨2903741, by rfl⟩ : syracuseStep 3871655 = 5807483) B5807483
theorem B4354985 : Blo 1719060 4354985 := bstep (se 2 (by rfl) ⟨1633119, by rfl⟩ : syracuseStep 4354985 = 3266239) B3266239
theorem B11015099 : Blo 1719060 11015099 := bstep (se 1 (by rfl) ⟨8261324, by rfl⟩ : syracuseStep 11015099 = 16522649) B16522649
theorem B13063193 : Blo 1719060 13063193 := bstep (se 2 (by rfl) ⟨4898697, by rfl⟩ : syracuseStep 13063193 = 9797395) B9797395
theorem B8705555 : Blo 1719060 8705555 := bstep (se 1 (by rfl) ⟨6529166, by rfl⟩ : syracuseStep 8705555 = 13058333) B13058333
theorem B105903767 : Blo 1719060 105903767 := bstep (se 1 (by rfl) ⟨79427825, by rfl⟩ : syracuseStep 105903767 = 158855651) B158855651
theorem B13244107 : Blo 1719060 13244107 := bstep (se 1 (by rfl) ⟨9933080, by rfl⟩ : syracuseStep 13244107 = 19866161) B19866161
theorem B7845601 : Blo 1719060 7845601 := bstep (se 2 (by rfl) ⟨2942100, by rfl⟩ : syracuseStep 7845601 = 5884201) B5884201
theorem B12400523 : Blo 1719060 12400523 := bstep (se 1 (by rfl) ⟨9300392, by rfl⟩ : syracuseStep 12400523 = 18600785) B18600785
theorem B19601351 : Blo 1719060 19601351 := bstep (se 1 (by rfl) ⟨14701013, by rfl⟩ : syracuseStep 19601351 = 29402027) B29402027
theorem B6527087 : Blo 1719060 6527087 := bstep (se 1 (by rfl) ⟨4895315, by rfl⟩ : syracuseStep 6527087 = 9790631) B9790631
theorem B9296329 : Blo 1719060 9296329 := bstep (se 2 (by rfl) ⟨3486123, by rfl⟩ : syracuseStep 9296329 = 6972247) B6972247
theorem B5806619 : Blo 1719060 5806619 := bstep (se 1 (by rfl) ⟨4354964, by rfl⟩ : syracuseStep 5806619 = 8709929) B8709929
theorem B11770571 : Blo 1719060 11770571 := bstep (se 1 (by rfl) ⟨8827928, by rfl⟩ : syracuseStep 11770571 = 17655857) B17655857
theorem B2579195 : Blo 1719060 2579195 := bstep (se 1 (by rfl) ⟨1934396, by rfl⟩ : syracuseStep 2579195 = 3868793) B3868793
theorem B4898015 : Blo 1719060 4898015 := bstep (se 1 (by rfl) ⟨3673511, by rfl⟩ : syracuseStep 4898015 = 7347023) B7347023
theorem B6528347 : Blo 1719060 6528347 := bstep (se 1 (by rfl) ⟨4896260, by rfl⟩ : syracuseStep 6528347 = 9792521) B9792521
theorem B1719743 : Blo 1719060 1719743 := bstep (se 1 (by rfl) ⟨1289807, by rfl⟩ : syracuseStep 1719743 = 2579615) B2579615
theorem B1719911 : Blo 1719060 1719911 := bstep (se 1 (by rfl) ⟨1289933, by rfl⟩ : syracuseStep 1719911 = 2579867) B2579867
theorem B63610535 : Blo 1719060 63610535 := bstep (se 1 (by rfl) ⟨47707901, by rfl⟩ : syracuseStep 63610535 = 95415803) B95415803
theorem B19586771 : Blo 1719060 19586771 := bstep (se 1 (by rfl) ⟨14690078, by rfl⟩ : syracuseStep 19586771 = 29380157) B29380157
theorem B8707823 : Blo 1719060 8707823 := bstep (se 1 (by rfl) ⟨6530867, by rfl⟩ : syracuseStep 8707823 = 13061735) B13061735
theorem B2580233 : Blo 1719060 2580233 := bstep (se 2 (by rfl) ⟨967587, by rfl⟩ : syracuseStep 2580233 = 1935175) B1935175
theorem B1720191 : Blo 1719060 1720191 := bstep (se 1 (by rfl) ⟨1290143, by rfl⟩ : syracuseStep 1720191 = 2580287) B2580287
theorem B1720303 : Blo 1719060 1720303 := bstep (se 1 (by rfl) ⟨1290227, by rfl⟩ : syracuseStep 1720303 = 2580455) B2580455
theorem B6529319 : Blo 1719060 6529319 := bstep (se 1 (by rfl) ⟨4896989, by rfl⟩ : syracuseStep 6529319 = 9793979) B9793979
theorem B1720647 : Blo 1719060 1720647 := bstep (se 1 (by rfl) ⟨1290485, by rfl⟩ : syracuseStep 1720647 = 2580971) B2580971
theorem B2580839 : Blo 1719060 2580839 := bstep (se 1 (by rfl) ⟨1935629, by rfl⟩ : syracuseStep 2580839 = 3871259) B3871259
theorem B1720731 : Blo 1719060 1720731 := bstep (se 1 (by rfl) ⟨1290548, by rfl⟩ : syracuseStep 1720731 = 2581097) B2581097
theorem B7848521 : Blo 1719060 7848521 := bstep (se 2 (by rfl) ⟨2943195, by rfl⟩ : syracuseStep 7848521 = 5886391) B5886391
theorem B12395105 : Blo 1719060 12395105 := bstep (se 2 (by rfl) ⟨4648164, by rfl⟩ : syracuseStep 12395105 = 9296329) B9296329
theorem B2581103 : Blo 1719060 2581103 := bstep (se 1 (by rfl) ⟨1935827, by rfl⟩ : syracuseStep 2581103 = 3871655) B3871655
theorem B8708795 : Blo 1719060 8708795 := bstep (se 1 (by rfl) ⟨6531596, by rfl⟩ : syracuseStep 8708795 = 13063193) B13063193
theorem B1934491 : Blo 1719060 1934491 := bstep (se 1 (by rfl) ⟨1450868, by rfl⟩ : syracuseStep 1934491 = 2901737) B2901737
theorem B8267015 : Blo 1719060 8267015 := bstep (se 1 (by rfl) ⟨6200261, by rfl⟩ : syracuseStep 8267015 = 12400523) B12400523
theorem B13067567 : Blo 1719060 13067567 := bstep (se 1 (by rfl) ⟨9800675, by rfl⟩ : syracuseStep 13067567 = 19601351) B19601351
theorem B4351391 : Blo 1719060 4351391 := bstep (se 1 (by rfl) ⟨3263543, by rfl⟩ : syracuseStep 4351391 = 6527087) B6527087
theorem B3868343 : Blo 1719060 3868343 := bstep (se 1 (by rfl) ⟨2901257, by rfl⟩ : syracuseStep 3868343 = 5802515) B5802515
theorem B18605801 : Blo 1719060 18605801 := bstep (se 2 (by rfl) ⟨6977175, by rfl⟩ : syracuseStep 18605801 = 13954351) B13954351
theorem B55822067 : Blo 1719060 55822067 := bstep (se 1 (by rfl) ⟨41866550, by rfl⟩ : syracuseStep 55822067 = 83733101) B83733101
theorem B27912073 : Blo 1719060 27912073 := bstep (se 2 (by rfl) ⟨10467027, by rfl⟩ : syracuseStep 27912073 = 20934055) B20934055
theorem B1935535 : Blo 1719060 1935535 := bstep (se 1 (by rfl) ⟨1451651, by rfl⟩ : syracuseStep 1935535 = 2903303) B2903303
theorem B4352231 : Blo 1719060 4352231 := bstep (se 1 (by rfl) ⟨3264173, by rfl⟩ : syracuseStep 4352231 = 6528347) B6528347
theorem B5802623 : Blo 1719060 5802623 := bstep (se 1 (by rfl) ⟨4351967, by rfl⟩ : syracuseStep 5802623 = 8703935) B8703935
theorem B2902655 : Blo 1719060 2902655 := bstep (se 1 (by rfl) ⟨2176991, by rfl⟩ : syracuseStep 2902655 = 4353983) B4353983
theorem B3869639 : Blo 1719060 3869639 := bstep (se 1 (by rfl) ⟨2902229, by rfl⟩ : syracuseStep 3869639 = 5804459) B5804459
theorem B5803001 : Blo 1719060 5803001 := bstep (se 2 (by rfl) ⟨2176125, by rfl⟩ : syracuseStep 5803001 = 4352251) B4352251
theorem B2903323 : Blo 1719060 2903323 := bstep (se 1 (by rfl) ⟨2177492, by rfl⟩ : syracuseStep 2903323 = 4354985) B4354985
theorem B7343399 : Blo 1719060 7343399 := bstep (se 1 (by rfl) ⟨5507549, by rfl⟩ : syracuseStep 7343399 = 11015099) B11015099
theorem B5803703 : Blo 1719060 5803703 := bstep (se 1 (by rfl) ⟨4352777, by rfl⟩ : syracuseStep 5803703 = 8705555) B8705555
theorem B70602511 : Blo 1719060 70602511 := bstep (se 1 (by rfl) ⟨52951883, by rfl⟩ : syracuseStep 70602511 = 105903767) B105903767
theorem B49590089 : Blo 1719060 49590089 := bstep (se 2 (by rfl) ⟨18596283, by rfl⟩ : syracuseStep 49590089 = 37192567) B37192567
theorem B3871079 : Blo 1719060 3871079 := bstep (se 1 (by rfl) ⟨2903309, by rfl⟩ : syracuseStep 3871079 = 5806619) B5806619
theorem B3265343 : Blo 1719060 3265343 := bstep (se 1 (by rfl) ⟨2449007, by rfl⟩ : syracuseStep 3265343 = 4898015) B4898015
theorem B17658809 : Blo 1719060 17658809 := bstep (se 2 (by rfl) ⟨6622053, by rfl⟩ : syracuseStep 17658809 = 13244107) B13244107
theorem B42407023 : Blo 1719060 42407023 := bstep (se 1 (by rfl) ⟨31805267, by rfl⟩ : syracuseStep 42407023 = 63610535) B63610535
theorem B5805215 : Blo 1719060 5805215 := bstep (se 1 (by rfl) ⟨4353911, by rfl⟩ : syracuseStep 5805215 = 8707823) B8707823
theorem B99202319 : Blo 1719060 99202319 := bstep (se 1 (by rfl) ⟨74401739, by rfl⟩ : syracuseStep 99202319 = 148803479) B148803479
theorem B4896055 : Blo 1719060 4896055 := bstep (se 1 (by rfl) ⟨3672041, by rfl⟩ : syracuseStep 4896055 = 7344083) B7344083
theorem B2578607 : Blo 1719060 2578607 := bstep (se 1 (by rfl) ⟨1933955, by rfl⟩ : syracuseStep 2578607 = 3867911) B3867911
theorem B5806457 : Blo 1719060 5806457 := bstep (se 2 (by rfl) ⟨2177421, by rfl⟩ : syracuseStep 5806457 = 4354843) B4354843
theorem B2578937 : Blo 1719060 2578937 := bstep (se 2 (by rfl) ⟨967101, by rfl⟩ : syracuseStep 2578937 = 1934203) B1934203
theorem B6528059 : Blo 1719060 6528059 := bstep (se 1 (by rfl) ⟨4896044, by rfl⟩ : syracuseStep 6528059 = 9792089) B9792089
theorem B7847047 : Blo 1719060 7847047 := bstep (se 1 (by rfl) ⟨5885285, by rfl⟩ : syracuseStep 7847047 = 11770571) B11770571
theorem B6200479 : Blo 1719060 6200479 := bstep (se 1 (by rfl) ⟨4650359, by rfl⟩ : syracuseStep 6200479 = 9300719) B9300719
theorem B1719463 : Blo 1719060 1719463 := bstep (se 1 (by rfl) ⟨1289597, by rfl⟩ : syracuseStep 1719463 = 2579195) B2579195
theorem B2579753 : Blo 1719060 2579753 := bstep (se 2 (by rfl) ⟨967407, by rfl⟩ : syracuseStep 2579753 = 1934815) B1934815
theorem B13057361 : Blo 1719060 13057361 := bstep (se 2 (by rfl) ⟨4896510, by rfl⟩ : syracuseStep 13057361 = 9793021) B9793021
theorem B17653099 : Blo 1719060 17653099 := bstep (se 1 (by rfl) ⟨13239824, by rfl⟩ : syracuseStep 17653099 = 26479649) B26479649
theorem B2579951 : Blo 1719060 2579951 := bstep (se 1 (by rfl) ⟨1934963, by rfl⟩ : syracuseStep 2579951 = 3869927) B3869927
theorem B6528559 : Blo 1719060 6528559 := bstep (se 1 (by rfl) ⟨4896419, by rfl⟩ : syracuseStep 6528559 = 9792839) B9792839
theorem B10460801 : Blo 1719060 10460801 := bstep (se 2 (by rfl) ⟨3922800, by rfl⟩ : syracuseStep 10460801 = 7845601) B7845601
theorem B2580251 : Blo 1719060 2580251 := bstep (se 1 (by rfl) ⟨1935188, by rfl⟩ : syracuseStep 2580251 = 3870377) B3870377
theorem B13057847 : Blo 1719060 13057847 := bstep (se 1 (by rfl) ⟨9793385, by rfl⟩ : syracuseStep 13057847 = 19586771) B19586771
theorem B1720155 : Blo 1719060 1720155 := bstep (se 1 (by rfl) ⟨1290116, by rfl⟩ : syracuseStep 1720155 = 2580233) B2580233
theorem B2580713 : Blo 1719060 2580713 := bstep (se 2 (by rfl) ⟨967767, by rfl⟩ : syracuseStep 2580713 = 1935535) B1935535
theorem B2580719 : Blo 1719060 2580719 := bstep (se 1 (by rfl) ⟨1935539, by rfl⟩ : syracuseStep 2580719 = 3871079) B3871079
theorem B1720559 : Blo 1719060 1720559 := bstep (se 1 (by rfl) ⟨1290419, by rfl⟩ : syracuseStep 1720559 = 2580839) B2580839
theorem B1720735 : Blo 1719060 1720735 := bstep (se 1 (by rfl) ⟨1290551, by rfl⟩ : syracuseStep 1720735 = 2581103) B2581103
theorem B11772539 : Blo 1719060 11772539 := bstep (se 1 (by rfl) ⟨8829404, by rfl⟩ : syracuseStep 11772539 = 17658809) B17658809
theorem B66134879 : Blo 1719060 66134879 := bstep (se 1 (by rfl) ⟨49601159, by rfl⟩ : syracuseStep 66134879 = 99202319) B99202319
theorem B2900927 : Blo 1719060 2900927 := bstep (se 1 (by rfl) ⟨2175695, by rfl⟩ : syracuseStep 2900927 = 4351391) B4351391
theorem B12403867 : Blo 1719060 12403867 := bstep (se 1 (by rfl) ⟨9302900, by rfl⟩ : syracuseStep 12403867 = 18605801) B18605801
theorem B56542697 : Blo 1719060 56542697 := bstep (se 2 (by rfl) ⟨21203511, by rfl⟩ : syracuseStep 56542697 = 42407023) B42407023
theorem B2901487 : Blo 1719060 2901487 := bstep (se 1 (by rfl) ⟨2176115, by rfl⟩ : syracuseStep 2901487 = 4352231) B4352231
theorem B10462729 : Blo 1719060 10462729 := bstep (se 2 (by rfl) ⟨3923523, by rfl⟩ : syracuseStep 10462729 = 7847047) B7847047
theorem B8267305 : Blo 1719060 8267305 := bstep (se 2 (by rfl) ⟨3100239, by rfl⟩ : syracuseStep 8267305 = 6200479) B6200479
theorem B3868415 : Blo 1719060 3868415 := bstep (se 1 (by rfl) ⟨2901311, by rfl⟩ : syracuseStep 3868415 = 5802623) B5802623
theorem B1935103 : Blo 1719060 1935103 := bstep (se 1 (by rfl) ⟨1451327, by rfl⟩ : syracuseStep 1935103 = 2902655) B2902655
theorem B23537465 : Blo 1719060 23537465 := bstep (se 2 (by rfl) ⟨8826549, by rfl⟩ : syracuseStep 23537465 = 17653099) B17653099
theorem B3868667 : Blo 1719060 3868667 := bstep (se 1 (by rfl) ⟨2901500, by rfl⟩ : syracuseStep 3868667 = 5803001) B5803001
theorem B4352039 : Blo 1719060 4352039 := bstep (se 1 (by rfl) ⟨3264029, by rfl⟩ : syracuseStep 4352039 = 6528059) B6528059
theorem B94136681 : Blo 1719060 94136681 := bstep (se 2 (by rfl) ⟨35301255, by rfl⟩ : syracuseStep 94136681 = 70602511) B70602511
theorem B6973867 : Blo 1719060 6973867 := bstep (se 1 (by rfl) ⟨5230400, by rfl⟩ : syracuseStep 6973867 = 10460801) B10460801
theorem B3869135 : Blo 1719060 3869135 := bstep (se 1 (by rfl) ⟨2901851, by rfl⟩ : syracuseStep 3869135 = 5803703) B5803703
theorem B4352879 : Blo 1719060 4352879 := bstep (se 1 (by rfl) ⟨3264659, by rfl⟩ : syracuseStep 4352879 = 6529319) B6529319
theorem B19582397 : Blo 1719060 19582397 := bstep (se 3 (by rfl) ⟨3671699, by rfl⟩ : syracuseStep 19582397 = 7343399) B7343399
theorem B3870143 : Blo 1719060 3870143 := bstep (se 1 (by rfl) ⟨2902607, by rfl⟩ : syracuseStep 3870143 = 5805215) B5805215
theorem B8711711 : Blo 1719060 8711711 := bstep (se 1 (by rfl) ⟨6533783, by rfl⟩ : syracuseStep 8711711 = 13067567) B13067567
theorem B3870971 : Blo 1719060 3870971 := bstep (se 1 (by rfl) ⟨2903228, by rfl⟩ : syracuseStep 3870971 = 5806457) B5806457
theorem B3871097 : Blo 1719060 3871097 := bstep (se 2 (by rfl) ⟨1451661, by rfl⟩ : syracuseStep 3871097 = 2903323) B2903323
theorem B8704745 : Blo 1719060 8704745 := bstep (se 2 (by rfl) ⟨3264279, by rfl⟩ : syracuseStep 8704745 = 6528559) B6528559
theorem B8704907 : Blo 1719060 8704907 := bstep (se 1 (by rfl) ⟨6528680, by rfl⟩ : syracuseStep 8704907 = 13057361) B13057361
theorem B8705231 : Blo 1719060 8705231 := bstep (se 1 (by rfl) ⟨6528923, by rfl⟩ : syracuseStep 8705231 = 13057847) B13057847
theorem B33060059 : Blo 1719060 33060059 := bstep (se 1 (by rfl) ⟨24795044, by rfl⟩ : syracuseStep 33060059 = 49590089) B49590089
theorem B5232347 : Blo 1719060 5232347 := bstep (se 1 (by rfl) ⟨3924260, by rfl⟩ : syracuseStep 5232347 = 7848521) B7848521
theorem B8263403 : Blo 1719060 8263403 := bstep (se 1 (by rfl) ⟨6197552, by rfl⟩ : syracuseStep 8263403 = 12395105) B12395105
theorem B5805863 : Blo 1719060 5805863 := bstep (se 1 (by rfl) ⟨4354397, by rfl⟩ : syracuseStep 5805863 = 8708795) B8708795
theorem B2176895 : Blo 1719060 2176895 := bstep (se 1 (by rfl) ⟨1632671, by rfl⟩ : syracuseStep 2176895 = 3265343) B3265343
theorem B5511343 : Blo 1719060 5511343 := bstep (se 1 (by rfl) ⟨4133507, by rfl⟩ : syracuseStep 5511343 = 8267015) B8267015
theorem B2578895 : Blo 1719060 2578895 := bstep (se 1 (by rfl) ⟨1934171, by rfl⟩ : syracuseStep 2578895 = 3868343) B3868343
theorem B37214711 : Blo 1719060 37214711 := bstep (se 1 (by rfl) ⟨27911033, by rfl⟩ : syracuseStep 37214711 = 55822067) B55822067
theorem B1719071 : Blo 1719060 1719071 := bstep (se 1 (by rfl) ⟨1289303, by rfl⟩ : syracuseStep 1719071 = 2578607) B2578607
theorem B2579321 : Blo 1719060 2579321 := bstep (se 2 (by rfl) ⟨967245, by rfl⟩ : syracuseStep 2579321 = 1934491) B1934491
theorem B1719291 : Blo 1719060 1719291 := bstep (se 1 (by rfl) ⟨1289468, by rfl⟩ : syracuseStep 1719291 = 2578937) B2578937
theorem B6528073 : Blo 1719060 6528073 := bstep (se 2 (by rfl) ⟨2448027, by rfl⟩ : syracuseStep 6528073 = 4896055) B4896055
theorem B2579759 : Blo 1719060 2579759 := bstep (se 1 (by rfl) ⟨1934819, by rfl⟩ : syracuseStep 2579759 = 3869639) B3869639
theorem B1719835 : Blo 1719060 1719835 := bstep (se 1 (by rfl) ⟨1289876, by rfl⟩ : syracuseStep 1719835 = 2579753) B2579753
theorem B1719967 : Blo 1719060 1719967 := bstep (se 1 (by rfl) ⟨1289975, by rfl⟩ : syracuseStep 1719967 = 2579951) B2579951
theorem B37216097 : Blo 1719060 37216097 := bstep (se 2 (by rfl) ⟨13956036, by rfl⟩ : syracuseStep 37216097 = 27912073) B27912073
theorem B1720167 : Blo 1719060 1720167 := bstep (se 1 (by rfl) ⟨1290125, by rfl⟩ : syracuseStep 1720167 = 2580251) B2580251
theorem B1720475 : Blo 1719060 1720475 := bstep (se 1 (by rfl) ⟨1290356, by rfl⟩ : syracuseStep 1720475 = 2580713) B2580713
theorem B1720479 : Blo 1719060 1720479 := bstep (se 1 (by rfl) ⟨1290359, by rfl⟩ : syracuseStep 1720479 = 2580719) B2580719
theorem B2580647 : Blo 1719060 2580647 := bstep (se 1 (by rfl) ⟨1935485, by rfl⟩ : syracuseStep 2580647 = 3870971) B3870971
theorem B7348457 : Blo 1719060 7348457 := bstep (se 2 (by rfl) ⟨2755671, by rfl⟩ : syracuseStep 7348457 = 5511343) B5511343
theorem B2580731 : Blo 1719060 2580731 := bstep (se 1 (by rfl) ⟨1935548, by rfl⟩ : syracuseStep 2580731 = 3871097) B3871097
theorem B7848359 : Blo 1719060 7848359 := bstep (se 1 (by rfl) ⟨5886269, by rfl⟩ : syracuseStep 7848359 = 11772539) B11772539
theorem B9298489 : Blo 1719060 9298489 := bstep (se 2 (by rfl) ⟨3486933, by rfl⟩ : syracuseStep 9298489 = 6973867) B6973867
theorem B44089919 : Blo 1719060 44089919 := bstep (se 1 (by rfl) ⟨33067439, by rfl⟩ : syracuseStep 44089919 = 66134879) B66134879
theorem B1933951 : Blo 1719060 1933951 := bstep (se 1 (by rfl) ⟨1450463, by rfl⟩ : syracuseStep 1933951 = 2900927) B2900927
theorem B2901359 : Blo 1719060 2901359 := bstep (se 1 (by rfl) ⟨2176019, by rfl⟩ : syracuseStep 2901359 = 4352039) B4352039
theorem B2901919 : Blo 1719060 2901919 := bstep (se 1 (by rfl) ⟨2176439, by rfl⟩ : syracuseStep 2901919 = 4352879) B4352879
theorem B3868649 : Blo 1719060 3868649 := bstep (se 2 (by rfl) ⟨1450743, by rfl⟩ : syracuseStep 3868649 = 2901487) B2901487
theorem B5803163 : Blo 1719060 5803163 := bstep (se 1 (by rfl) ⟨4352372, by rfl⟩ : syracuseStep 5803163 = 8704745) B8704745
theorem B5803271 : Blo 1719060 5803271 := bstep (se 1 (by rfl) ⟨4352453, by rfl⟩ : syracuseStep 5803271 = 8704907) B8704907
theorem B5803487 : Blo 1719060 5803487 := bstep (se 1 (by rfl) ⟨4352615, by rfl⟩ : syracuseStep 5803487 = 8705231) B8705231
theorem B22040039 : Blo 1719060 22040039 := bstep (se 1 (by rfl) ⟨16530029, by rfl⟩ : syracuseStep 22040039 = 33060059) B33060059
theorem B37695131 : Blo 1719060 37695131 := bstep (se 1 (by rfl) ⟨28271348, by rfl⟩ : syracuseStep 37695131 = 56542697) B56542697
theorem B5508935 : Blo 1719060 5508935 := bstep (se 1 (by rfl) ⟨4131701, by rfl⟩ : syracuseStep 5508935 = 8263403) B8263403
theorem B3870575 : Blo 1719060 3870575 := bstep (se 1 (by rfl) ⟨2902931, by rfl⟩ : syracuseStep 3870575 = 5805863) B5805863
theorem B15691643 : Blo 1719060 15691643 := bstep (se 1 (by rfl) ⟨11768732, by rfl⟩ : syracuseStep 15691643 = 23537465) B23537465
theorem B8704097 : Blo 1719060 8704097 := bstep (se 2 (by rfl) ⟨3264036, by rfl⟩ : syracuseStep 8704097 = 6528073) B6528073
theorem B24809807 : Blo 1719060 24809807 := bstep (se 1 (by rfl) ⟨18607355, by rfl⟩ : syracuseStep 24809807 = 37214711) B37214711
theorem B11023073 : Blo 1719060 11023073 := bstep (se 2 (by rfl) ⟨4133652, by rfl⟩ : syracuseStep 11023073 = 8267305) B8267305
theorem B13054931 : Blo 1719060 13054931 := bstep (se 1 (by rfl) ⟨9791198, by rfl⟩ : syracuseStep 13054931 = 19582397) B19582397
theorem B5805053 : Blo 1719060 5805053 := bstep (se 3 (by rfl) ⟨1088447, by rfl⟩ : syracuseStep 5805053 = 2176895) B2176895
theorem B24810731 : Blo 1719060 24810731 := bstep (se 1 (by rfl) ⟨18608048, by rfl⟩ : syracuseStep 24810731 = 37216097) B37216097
theorem B3488231 : Blo 1719060 3488231 := bstep (se 1 (by rfl) ⟨2616173, by rfl⟩ : syracuseStep 3488231 = 5232347) B5232347
theorem B2578943 : Blo 1719060 2578943 := bstep (se 1 (by rfl) ⟨1934207, by rfl⟩ : syracuseStep 2578943 = 3868415) B3868415
theorem B2579111 : Blo 1719060 2579111 := bstep (se 1 (by rfl) ⟨1934333, by rfl⟩ : syracuseStep 2579111 = 3868667) B3868667
theorem B16538489 : Blo 1719060 16538489 := bstep (se 2 (by rfl) ⟨6201933, by rfl⟩ : syracuseStep 16538489 = 12403867) B12403867
theorem B62757787 : Blo 1719060 62757787 := bstep (se 1 (by rfl) ⟨47068340, by rfl⟩ : syracuseStep 62757787 = 94136681) B94136681
theorem B1719263 : Blo 1719060 1719263 := bstep (se 1 (by rfl) ⟨1289447, by rfl⟩ : syracuseStep 1719263 = 2578895) B2578895
theorem B2579423 : Blo 1719060 2579423 := bstep (se 1 (by rfl) ⟨1934567, by rfl⟩ : syracuseStep 2579423 = 3869135) B3869135
theorem B1719547 : Blo 1719060 1719547 := bstep (se 1 (by rfl) ⟨1289660, by rfl⟩ : syracuseStep 1719547 = 2579321) B2579321
theorem B13950305 : Blo 1719060 13950305 := bstep (se 2 (by rfl) ⟨5231364, by rfl⟩ : syracuseStep 13950305 = 10462729) B10462729
theorem B1719839 : Blo 1719060 1719839 := bstep (se 1 (by rfl) ⟨1289879, by rfl⟩ : syracuseStep 1719839 = 2579759) B2579759
theorem B2580095 : Blo 1719060 2580095 := bstep (se 1 (by rfl) ⟨1935071, by rfl⟩ : syracuseStep 2580095 = 3870143) B3870143
theorem B2580137 : Blo 1719060 2580137 := bstep (se 2 (by rfl) ⟨967551, by rfl⟩ : syracuseStep 2580137 = 1935103) B1935103
theorem B5807807 : Blo 1719060 5807807 := bstep (se 1 (by rfl) ⟨4355855, by rfl⟩ : syracuseStep 5807807 = 8711711) B8711711
theorem B1720431 : Blo 1719060 1720431 := bstep (se 1 (by rfl) ⟨1290323, by rfl⟩ : syracuseStep 1720431 = 2580647) B2580647
theorem B4898971 : Blo 1719060 4898971 := bstep (se 1 (by rfl) ⟨3674228, by rfl⟩ : syracuseStep 4898971 = 7348457) B7348457
theorem B1720487 : Blo 1719060 1720487 := bstep (se 1 (by rfl) ⟨1290365, by rfl⟩ : syracuseStep 1720487 = 2580731) B2580731
theorem B16539871 : Blo 1719060 16539871 := bstep (se 1 (by rfl) ⟨12404903, by rfl⟩ : syracuseStep 16539871 = 24809807) B24809807
theorem B29393279 : Blo 1719060 29393279 := bstep (se 1 (by rfl) ⟨22044959, by rfl⟩ : syracuseStep 29393279 = 44089919) B44089919
theorem B7348715 : Blo 1719060 7348715 := bstep (se 1 (by rfl) ⟨5511536, by rfl⟩ : syracuseStep 7348715 = 11023073) B11023073
theorem B16540487 : Blo 1719060 16540487 := bstep (se 1 (by rfl) ⟨12405365, by rfl⟩ : syracuseStep 16540487 = 24810731) B24810731
theorem B1934239 : Blo 1719060 1934239 := bstep (se 1 (by rfl) ⟨1450679, by rfl⟩ : syracuseStep 1934239 = 2901359) B2901359
theorem B3868775 : Blo 1719060 3868775 := bstep (se 1 (by rfl) ⟨2901581, by rfl⟩ : syracuseStep 3868775 = 5803163) B5803163
theorem B3868847 : Blo 1719060 3868847 := bstep (se 1 (by rfl) ⟨2901635, by rfl⟩ : syracuseStep 3868847 = 5803271) B5803271
theorem B9300203 : Blo 1719060 9300203 := bstep (se 1 (by rfl) ⟨6975152, by rfl⟩ : syracuseStep 9300203 = 13950305) B13950305
theorem B3868991 : Blo 1719060 3868991 := bstep (se 1 (by rfl) ⟨2901743, by rfl⟩ : syracuseStep 3868991 = 5803487) B5803487
theorem B3869225 : Blo 1719060 3869225 := bstep (se 2 (by rfl) ⟨1450959, by rfl⟩ : syracuseStep 3869225 = 2901919) B2901919
theorem B3672623 : Blo 1719060 3672623 := bstep (se 1 (by rfl) ⟨2754467, by rfl⟩ : syracuseStep 3672623 = 5508935) B5508935
theorem B5802731 : Blo 1719060 5802731 := bstep (se 1 (by rfl) ⟨4352048, by rfl⟩ : syracuseStep 5802731 = 8704097) B8704097
theorem B8703287 : Blo 1719060 8703287 := bstep (se 1 (by rfl) ⟨6527465, by rfl⟩ : syracuseStep 8703287 = 13054931) B13054931
theorem B3870035 : Blo 1719060 3870035 := bstep (se 1 (by rfl) ⟨2902526, by rfl⟩ : syracuseStep 3870035 = 5805053) B5805053
theorem B12397985 : Blo 1719060 12397985 := bstep (se 2 (by rfl) ⟨4649244, by rfl⟩ : syracuseStep 12397985 = 9298489) B9298489
theorem B83677049 : Blo 1719060 83677049 := bstep (se 2 (by rfl) ⟨31378893, by rfl⟩ : syracuseStep 83677049 = 62757787) B62757787
theorem B9301949 : Blo 1719060 9301949 := bstep (se 3 (by rfl) ⟨1744115, by rfl⟩ : syracuseStep 9301949 = 3488231) B3488231
theorem B14693359 : Blo 1719060 14693359 := bstep (se 1 (by rfl) ⟨11020019, by rfl⟩ : syracuseStep 14693359 = 22040039) B22040039
theorem B25130087 : Blo 1719060 25130087 := bstep (se 1 (by rfl) ⟨18847565, by rfl⟩ : syracuseStep 25130087 = 37695131) B37695131
theorem B3871871 : Blo 1719060 3871871 := bstep (se 1 (by rfl) ⟨2903903, by rfl⟩ : syracuseStep 3871871 = 5807807) B5807807
theorem B5232239 : Blo 1719060 5232239 := bstep (se 1 (by rfl) ⟨3924179, by rfl⟩ : syracuseStep 5232239 = 7848359) B7848359
theorem B2578601 : Blo 1719060 2578601 := bstep (se 2 (by rfl) ⟨966975, by rfl⟩ : syracuseStep 2578601 = 1933951) B1933951
theorem B2579099 : Blo 1719060 2579099 := bstep (se 1 (by rfl) ⟨1934324, by rfl⟩ : syracuseStep 2579099 = 3868649) B3868649
theorem B1719295 : Blo 1719060 1719295 := bstep (se 1 (by rfl) ⟨1289471, by rfl⟩ : syracuseStep 1719295 = 2578943) B2578943
theorem B1719407 : Blo 1719060 1719407 := bstep (se 1 (by rfl) ⟨1289555, by rfl⟩ : syracuseStep 1719407 = 2579111) B2579111
theorem B11025659 : Blo 1719060 11025659 := bstep (se 1 (by rfl) ⟨8269244, by rfl⟩ : syracuseStep 11025659 = 16538489) B16538489
theorem B1719615 : Blo 1719060 1719615 := bstep (se 1 (by rfl) ⟨1289711, by rfl⟩ : syracuseStep 1719615 = 2579423) B2579423
theorem B1720063 : Blo 1719060 1720063 := bstep (se 1 (by rfl) ⟨1290047, by rfl⟩ : syracuseStep 1720063 = 2580095) B2580095
theorem B1720091 : Blo 1719060 1720091 := bstep (se 1 (by rfl) ⟨1290068, by rfl⟩ : syracuseStep 1720091 = 2580137) B2580137
theorem B2580383 : Blo 1719060 2580383 := bstep (se 1 (by rfl) ⟨1935287, by rfl⟩ : syracuseStep 2580383 = 3870575) B3870575
theorem B10461095 : Blo 1719060 10461095 := bstep (se 1 (by rfl) ⟨7845821, by rfl⟩ : syracuseStep 10461095 = 15691643) B15691643
theorem B19595519 : Blo 1719060 19595519 := bstep (se 1 (by rfl) ⟨14696639, by rfl⟩ : syracuseStep 19595519 = 29393279) B29393279
theorem B22053161 : Blo 1719060 22053161 := bstep (se 2 (by rfl) ⟨8269935, by rfl⟩ : syracuseStep 22053161 = 16539871) B16539871
theorem B4899143 : Blo 1719060 4899143 := bstep (se 1 (by rfl) ⟨3674357, by rfl⟩ : syracuseStep 4899143 = 7348715) B7348715
theorem B11026991 : Blo 1719060 11026991 := bstep (se 1 (by rfl) ⟨8270243, by rfl⟩ : syracuseStep 11026991 = 16540487) B16540487
theorem B16753391 : Blo 1719060 16753391 := bstep (se 1 (by rfl) ⟨12565043, by rfl⟩ : syracuseStep 16753391 = 25130087) B25130087
theorem B2581247 : Blo 1719060 2581247 := bstep (se 1 (by rfl) ⟨1935935, by rfl⟩ : syracuseStep 2581247 = 3871871) B3871871
theorem B3868487 : Blo 1719060 3868487 := bstep (se 1 (by rfl) ⟨2901365, by rfl⟩ : syracuseStep 3868487 = 5802731) B5802731
theorem B7350439 : Blo 1719060 7350439 := bstep (se 1 (by rfl) ⟨5512829, by rfl⟩ : syracuseStep 7350439 = 11025659) B11025659
theorem B5802191 : Blo 1719060 5802191 := bstep (se 1 (by rfl) ⟨4351643, by rfl⟩ : syracuseStep 5802191 = 8703287) B8703287
theorem B6974063 : Blo 1719060 6974063 := bstep (se 1 (by rfl) ⟨5230547, by rfl⟩ : syracuseStep 6974063 = 10461095) B10461095
theorem B6531961 : Blo 1719060 6531961 := bstep (se 2 (by rfl) ⟨2449485, by rfl⟩ : syracuseStep 6531961 = 4898971) B4898971
theorem B19591145 : Blo 1719060 19591145 := bstep (se 2 (by rfl) ⟨7346679, by rfl⟩ : syracuseStep 19591145 = 14693359) B14693359
theorem B55784699 : Blo 1719060 55784699 := bstep (se 1 (by rfl) ⟨41838524, by rfl⟩ : syracuseStep 55784699 = 83677049) B83677049
theorem B3488159 : Blo 1719060 3488159 := bstep (se 1 (by rfl) ⟨2616119, by rfl⟩ : syracuseStep 3488159 = 5232239) B5232239
theorem B2578985 : Blo 1719060 2578985 := bstep (se 2 (by rfl) ⟨967119, by rfl⟩ : syracuseStep 2578985 = 1934239) B1934239
theorem B2579183 : Blo 1719060 2579183 := bstep (se 1 (by rfl) ⟨1934387, by rfl⟩ : syracuseStep 2579183 = 3868775) B3868775
theorem B1719067 : Blo 1719060 1719067 := bstep (se 1 (by rfl) ⟨1289300, by rfl⟩ : syracuseStep 1719067 = 2578601) B2578601
theorem B2579231 : Blo 1719060 2579231 := bstep (se 1 (by rfl) ⟨1934423, by rfl⟩ : syracuseStep 2579231 = 3868847) B3868847
theorem B6200135 : Blo 1719060 6200135 := bstep (se 1 (by rfl) ⟨4650101, by rfl⟩ : syracuseStep 6200135 = 9300203) B9300203
theorem B2579327 : Blo 1719060 2579327 := bstep (se 1 (by rfl) ⟨1934495, by rfl⟩ : syracuseStep 2579327 = 3868991) B3868991
theorem B2579483 : Blo 1719060 2579483 := bstep (se 1 (by rfl) ⟨1934612, by rfl⟩ : syracuseStep 2579483 = 3869225) B3869225
theorem B2448415 : Blo 1719060 2448415 := bstep (se 1 (by rfl) ⟨1836311, by rfl⟩ : syracuseStep 2448415 = 3672623) B3672623
theorem B1719399 : Blo 1719060 1719399 := bstep (se 1 (by rfl) ⟨1289549, by rfl⟩ : syracuseStep 1719399 = 2579099) B2579099
theorem B2580023 : Blo 1719060 2580023 := bstep (se 1 (by rfl) ⟨1935017, by rfl⟩ : syracuseStep 2580023 = 3870035) B3870035
theorem B8265323 : Blo 1719060 8265323 := bstep (se 1 (by rfl) ⟨6198992, by rfl⟩ : syracuseStep 8265323 = 12397985) B12397985
theorem B1720255 : Blo 1719060 1720255 := bstep (se 1 (by rfl) ⟨1290191, by rfl⟩ : syracuseStep 1720255 = 2580383) B2580383
theorem B6201299 : Blo 1719060 6201299 := bstep (se 1 (by rfl) ⟨4650974, by rfl⟩ : syracuseStep 6201299 = 9301949) B9301949
theorem B1720831 : Blo 1719060 1720831 := bstep (se 1 (by rfl) ⟨1290623, by rfl⟩ : syracuseStep 1720831 = 2581247) B2581247
theorem B8709281 : Blo 1719060 8709281 := bstep (se 2 (by rfl) ⟨3265980, by rfl⟩ : syracuseStep 8709281 = 6531961) B6531961
theorem B3868127 : Blo 1719060 3868127 := bstep (se 1 (by rfl) ⟨2901095, by rfl⟩ : syracuseStep 3868127 = 5802191) B5802191
theorem B13060763 : Blo 1719060 13060763 := bstep (se 1 (by rfl) ⟨9795572, by rfl⟩ : syracuseStep 13060763 = 19591145) B19591145
theorem B9800585 : Blo 1719060 9800585 := bstep (se 2 (by rfl) ⟨3675219, by rfl⟩ : syracuseStep 9800585 = 7350439) B7350439
theorem B7351327 : Blo 1719060 7351327 := bstep (se 1 (by rfl) ⟨5513495, by rfl⟩ : syracuseStep 7351327 = 11026991) B11026991
theorem B11168927 : Blo 1719060 11168927 := bstep (se 1 (by rfl) ⟨8376695, by rfl⟩ : syracuseStep 11168927 = 16753391) B16753391
theorem B3264553 : Blo 1719060 3264553 := bstep (se 2 (by rfl) ⟨1224207, by rfl⟩ : syracuseStep 3264553 = 2448415) B2448415
theorem B4649375 : Blo 1719060 4649375 := bstep (se 1 (by rfl) ⟨3487031, by rfl⟩ : syracuseStep 4649375 = 6974063) B6974063
theorem B4133423 : Blo 1719060 4133423 := bstep (se 1 (by rfl) ⟨3100067, by rfl⟩ : syracuseStep 4133423 = 6200135) B6200135
theorem B5510215 : Blo 1719060 5510215 := bstep (se 1 (by rfl) ⟨4132661, by rfl⟩ : syracuseStep 5510215 = 8265323) B8265323
theorem B16536797 : Blo 1719060 16536797 := bstep (se 3 (by rfl) ⟨3100649, by rfl⟩ : syracuseStep 16536797 = 6201299) B6201299
theorem B13063679 : Blo 1719060 13063679 := bstep (se 1 (by rfl) ⟨9797759, by rfl⟩ : syracuseStep 13063679 = 19595519) B19595519
theorem B14702107 : Blo 1719060 14702107 := bstep (se 1 (by rfl) ⟨11026580, by rfl⟩ : syracuseStep 14702107 = 22053161) B22053161
theorem B3266095 : Blo 1719060 3266095 := bstep (se 1 (by rfl) ⟨2449571, by rfl⟩ : syracuseStep 3266095 = 4899143) B4899143
theorem B37189799 : Blo 1719060 37189799 := bstep (se 1 (by rfl) ⟨27892349, by rfl⟩ : syracuseStep 37189799 = 55784699) B55784699
theorem B2578991 : Blo 1719060 2578991 := bstep (se 1 (by rfl) ⟨1934243, by rfl⟩ : syracuseStep 2578991 = 3868487) B3868487
theorem B2325439 : Blo 1719060 2325439 := bstep (se 1 (by rfl) ⟨1744079, by rfl⟩ : syracuseStep 2325439 = 3488159) B3488159
theorem B1719323 : Blo 1719060 1719323 := bstep (se 1 (by rfl) ⟨1289492, by rfl⟩ : syracuseStep 1719323 = 2578985) B2578985
theorem B1719455 : Blo 1719060 1719455 := bstep (se 1 (by rfl) ⟨1289591, by rfl⟩ : syracuseStep 1719455 = 2579183) B2579183
theorem B1719487 : Blo 1719060 1719487 := bstep (se 1 (by rfl) ⟨1289615, by rfl⟩ : syracuseStep 1719487 = 2579231) B2579231
theorem B1719551 : Blo 1719060 1719551 := bstep (se 1 (by rfl) ⟨1289663, by rfl⟩ : syracuseStep 1719551 = 2579327) B2579327
theorem B1719655 : Blo 1719060 1719655 := bstep (se 1 (by rfl) ⟨1289741, by rfl⟩ : syracuseStep 1719655 = 2579483) B2579483
theorem B1720015 : Blo 1719060 1720015 := bstep (se 1 (by rfl) ⟨1290011, by rfl⟩ : syracuseStep 1720015 = 2580023) B2580023
theorem B8709119 : Blo 1719060 8709119 := bstep (se 1 (by rfl) ⟨6531839, by rfl⟩ : syracuseStep 8709119 = 13063679) B13063679
theorem B4352737 : Blo 1719060 4352737 := bstep (se 2 (by rfl) ⟨1632276, by rfl⟩ : syracuseStep 4352737 = 3264553) B3264553
theorem B3099583 : Blo 1719060 3099583 := bstep (se 1 (by rfl) ⟨2324687, by rfl⟩ : syracuseStep 3099583 = 4649375) B4649375
theorem B2755615 : Blo 1719060 2755615 := bstep (se 1 (by rfl) ⟨2066711, by rfl⟩ : syracuseStep 2755615 = 4133423) B4133423
theorem B9801769 : Blo 1719060 9801769 := bstep (se 2 (by rfl) ⟨3675663, by rfl⟩ : syracuseStep 9801769 = 7351327) B7351327
theorem B24793199 : Blo 1719060 24793199 := bstep (se 1 (by rfl) ⟨18594899, by rfl⟩ : syracuseStep 24793199 = 37189799) B37189799
theorem B6533723 : Blo 1719060 6533723 := bstep (se 1 (by rfl) ⟨4900292, by rfl⟩ : syracuseStep 6533723 = 9800585) B9800585
theorem B4354793 : Blo 1719060 4354793 := bstep (se 2 (by rfl) ⟨1633047, by rfl⟩ : syracuseStep 4354793 = 3266095) B3266095
theorem B5806187 : Blo 1719060 5806187 := bstep (se 1 (by rfl) ⟨4354640, by rfl⟩ : syracuseStep 5806187 = 8709281) B8709281
theorem B11024531 : Blo 1719060 11024531 := bstep (se 1 (by rfl) ⟨8268398, by rfl⟩ : syracuseStep 11024531 = 16536797) B16536797
theorem B2578751 : Blo 1719060 2578751 := bstep (se 1 (by rfl) ⟨1934063, by rfl⟩ : syracuseStep 2578751 = 3868127) B3868127
theorem B7346953 : Blo 1719060 7346953 := bstep (se 2 (by rfl) ⟨2755107, by rfl⟩ : syracuseStep 7346953 = 5510215) B5510215
theorem B1719327 : Blo 1719060 1719327 := bstep (se 1 (by rfl) ⟨1289495, by rfl⟩ : syracuseStep 1719327 = 2578991) B2578991
theorem B8707175 : Blo 1719060 8707175 := bstep (se 1 (by rfl) ⟨6530381, by rfl⟩ : syracuseStep 8707175 = 13060763) B13060763
theorem B19602809 : Blo 1719060 19602809 := bstep (se 2 (by rfl) ⟨7351053, by rfl⟩ : syracuseStep 19602809 = 14702107) B14702107
theorem B7445951 : Blo 1719060 7445951 := bstep (se 1 (by rfl) ⟨5584463, by rfl⟩ : syracuseStep 7445951 = 11168927) B11168927
theorem B12402341 : Blo 1719060 12402341 := bstep (se 4 (by rfl) ⟨1162719, by rfl⟩ : syracuseStep 12402341 = 2325439) B2325439
theorem B7349687 : Blo 1719060 7349687 := bstep (se 1 (by rfl) ⟨5512265, by rfl⟩ : syracuseStep 7349687 = 11024531) B11024531
theorem B13068539 : Blo 1719060 13068539 := bstep (se 1 (by rfl) ⟨9801404, by rfl⟩ : syracuseStep 13068539 = 19602809) B19602809
theorem B8268227 : Blo 1719060 8268227 := bstep (se 1 (by rfl) ⟨6201170, by rfl⟩ : syracuseStep 8268227 = 12402341) B12402341
theorem B13069025 : Blo 1719060 13069025 := bstep (se 2 (by rfl) ⟨4900884, by rfl⟩ : syracuseStep 13069025 = 9801769) B9801769
theorem B2903195 : Blo 1719060 2903195 := bstep (se 1 (by rfl) ⟨2177396, by rfl⟩ : syracuseStep 2903195 = 4354793) B4354793
theorem B5803649 : Blo 1719060 5803649 := bstep (se 2 (by rfl) ⟨2176368, by rfl⟩ : syracuseStep 5803649 = 4352737) B4352737
theorem B4132777 : Blo 1719060 4132777 := bstep (se 2 (by rfl) ⟨1549791, by rfl⟩ : syracuseStep 4132777 = 3099583) B3099583
theorem B3674153 : Blo 1719060 3674153 := bstep (se 2 (by rfl) ⟨1377807, by rfl⟩ : syracuseStep 3674153 = 2755615) B2755615
theorem B3870791 : Blo 1719060 3870791 := bstep (se 1 (by rfl) ⟨2903093, by rfl⟩ : syracuseStep 3870791 = 5806187) B5806187
theorem B5804783 : Blo 1719060 5804783 := bstep (se 1 (by rfl) ⟨4353587, by rfl⟩ : syracuseStep 5804783 = 8707175) B8707175
theorem B16528799 : Blo 1719060 16528799 := bstep (se 1 (by rfl) ⟨12396599, by rfl⟩ : syracuseStep 16528799 = 24793199) B24793199
theorem B4355815 : Blo 1719060 4355815 := bstep (se 1 (by rfl) ⟨3266861, by rfl⟩ : syracuseStep 4355815 = 6533723) B6533723
theorem B5806079 : Blo 1719060 5806079 := bstep (se 1 (by rfl) ⟨4354559, by rfl⟩ : syracuseStep 5806079 = 8709119) B8709119
theorem B9795937 : Blo 1719060 9795937 := bstep (se 2 (by rfl) ⟨3673476, by rfl⟩ : syracuseStep 9795937 = 7346953) B7346953
theorem B1719167 : Blo 1719060 1719167 := bstep (se 1 (by rfl) ⟨1289375, by rfl⟩ : syracuseStep 1719167 = 2578751) B2578751
theorem B4963967 : Blo 1719060 4963967 := bstep (se 1 (by rfl) ⟨3722975, by rfl⟩ : syracuseStep 4963967 = 7445951) B7445951
theorem B2449435 : Blo 1719060 2449435 := bstep (se 1 (by rfl) ⟨1837076, by rfl⟩ : syracuseStep 2449435 = 3674153) B3674153
theorem B2580527 : Blo 1719060 2580527 := bstep (se 1 (by rfl) ⟨1935395, by rfl⟩ : syracuseStep 2580527 = 3870791) B3870791
theorem B4899791 : Blo 1719060 4899791 := bstep (se 1 (by rfl) ⟨3674843, by rfl⟩ : syracuseStep 4899791 = 7349687) B7349687
theorem B1935463 : Blo 1719060 1935463 := bstep (se 1 (by rfl) ⟨1451597, by rfl⟩ : syracuseStep 1935463 = 2903195) B2903195
theorem B3869099 : Blo 1719060 3869099 := bstep (se 1 (by rfl) ⟨2901824, by rfl⟩ : syracuseStep 3869099 = 5803649) B5803649
theorem B13061249 : Blo 1719060 13061249 := bstep (se 2 (by rfl) ⟨4897968, by rfl⟩ : syracuseStep 13061249 = 9795937) B9795937
theorem B3869855 : Blo 1719060 3869855 := bstep (se 1 (by rfl) ⟨2902391, by rfl⟩ : syracuseStep 3869855 = 5804783) B5804783
theorem B44076797 : Blo 1719060 44076797 := bstep (se 3 (by rfl) ⟨8264399, by rfl⟩ : syracuseStep 44076797 = 16528799) B16528799
theorem B3870719 : Blo 1719060 3870719 := bstep (se 1 (by rfl) ⟨2903039, by rfl⟩ : syracuseStep 3870719 = 5806079) B5806079
theorem B8712359 : Blo 1719060 8712359 := bstep (se 1 (by rfl) ⟨6534269, by rfl⟩ : syracuseStep 8712359 = 13068539) B13068539
theorem B8712683 : Blo 1719060 8712683 := bstep (se 1 (by rfl) ⟨6534512, by rfl⟩ : syracuseStep 8712683 = 13069025) B13069025
theorem B5510369 : Blo 1719060 5510369 := bstep (se 2 (by rfl) ⟨2066388, by rfl⟩ : syracuseStep 5510369 = 4132777) B4132777
theorem B5512151 : Blo 1719060 5512151 := bstep (se 1 (by rfl) ⟨4134113, by rfl⟩ : syracuseStep 5512151 = 8268227) B8268227
theorem B5807753 : Blo 1719060 5807753 := bstep (se 2 (by rfl) ⟨2177907, by rfl⟩ : syracuseStep 5807753 = 4355815) B4355815
theorem B3309311 : Blo 1719060 3309311 := bstep (se 1 (by rfl) ⟨2481983, by rfl⟩ : syracuseStep 3309311 = 4963967) B4963967
theorem B1720351 : Blo 1719060 1720351 := bstep (se 1 (by rfl) ⟨1290263, by rfl⟩ : syracuseStep 1720351 = 2580527) B2580527
theorem B5808239 : Blo 1719060 5808239 := bstep (se 1 (by rfl) ⟨4356179, by rfl⟩ : syracuseStep 5808239 = 8712359) B8712359
theorem B2580617 : Blo 1719060 2580617 := bstep (se 2 (by rfl) ⟨967731, by rfl⟩ : syracuseStep 2580617 = 1935463) B1935463
theorem B5808455 : Blo 1719060 5808455 := bstep (se 1 (by rfl) ⟨4356341, by rfl⟩ : syracuseStep 5808455 = 8712683) B8712683
theorem B2206207 : Blo 1719060 2206207 := bstep (se 1 (by rfl) ⟨1654655, by rfl⟩ : syracuseStep 2206207 = 3309311) B3309311
theorem B14699069 : Blo 1719060 14699069 := bstep (se 3 (by rfl) ⟨2756075, by rfl⟩ : syracuseStep 14699069 = 5512151) B5512151
theorem B3871835 : Blo 1719060 3871835 := bstep (se 1 (by rfl) ⟨2903876, by rfl⟩ : syracuseStep 3871835 = 5807753) B5807753
theorem B3265913 : Blo 1719060 3265913 := bstep (se 2 (by rfl) ⟨1224717, by rfl⟩ : syracuseStep 3265913 = 2449435) B2449435
theorem B14694317 : Blo 1719060 14694317 := bstep (se 3 (by rfl) ⟨2755184, by rfl⟩ : syracuseStep 14694317 = 5510369) B5510369
theorem B2580479 : Blo 1719060 2580479 := bstep (se 1 (by rfl) ⟨1935359, by rfl⟩ : syracuseStep 2580479 = 3870719) B3870719
theorem B2579399 : Blo 1719060 2579399 := bstep (se 1 (by rfl) ⟨1934549, by rfl⟩ : syracuseStep 2579399 = 3869099) B3869099
theorem B8707499 : Blo 1719060 8707499 := bstep (se 1 (by rfl) ⟨6530624, by rfl⟩ : syracuseStep 8707499 = 13061249) B13061249
theorem B2579903 : Blo 1719060 2579903 := bstep (se 1 (by rfl) ⟨1934927, by rfl⟩ : syracuseStep 2579903 = 3869855) B3869855
theorem B29384531 : Blo 1719060 29384531 := bstep (se 1 (by rfl) ⟨22038398, by rfl⟩ : syracuseStep 29384531 = 44076797) B44076797
theorem B13066109 : Blo 1719060 13066109 := bstep (se 3 (by rfl) ⟨2449895, by rfl⟩ : syracuseStep 13066109 = 4899791) B4899791
theorem B1720411 : Blo 1719060 1720411 := bstep (se 1 (by rfl) ⟨1290308, by rfl⟩ : syracuseStep 1720411 = 2580617) B2580617
theorem B2941609 : Blo 1719060 2941609 := bstep (se 2 (by rfl) ⟨1103103, by rfl⟩ : syracuseStep 2941609 = 2206207) B2206207
theorem B2581223 : Blo 1719060 2581223 := bstep (se 1 (by rfl) ⟨1935917, by rfl⟩ : syracuseStep 2581223 = 3871835) B3871835
theorem B9799379 : Blo 1719060 9799379 := bstep (se 1 (by rfl) ⟨7349534, by rfl⟩ : syracuseStep 9799379 = 14699069) B14699069
theorem B19589687 : Blo 1719060 19589687 := bstep (se 1 (by rfl) ⟨14692265, by rfl⟩ : syracuseStep 19589687 = 29384531) B29384531
theorem B8710739 : Blo 1719060 8710739 := bstep (se 1 (by rfl) ⟨6533054, by rfl⟩ : syracuseStep 8710739 = 13066109) B13066109
theorem B5804999 : Blo 1719060 5804999 := bstep (se 1 (by rfl) ⟨4353749, by rfl⟩ : syracuseStep 5804999 = 8707499) B8707499
theorem B3872159 : Blo 1719060 3872159 := bstep (se 1 (by rfl) ⟨2904119, by rfl⟩ : syracuseStep 3872159 = 5808239) B5808239
theorem B3872303 : Blo 1719060 3872303 := bstep (se 1 (by rfl) ⟨2904227, by rfl⟩ : syracuseStep 3872303 = 5808455) B5808455
theorem B2177275 : Blo 1719060 2177275 := bstep (se 1 (by rfl) ⟨1632956, by rfl⟩ : syracuseStep 2177275 = 3265913) B3265913
theorem B9796211 : Blo 1719060 9796211 := bstep (se 1 (by rfl) ⟨7347158, by rfl⟩ : syracuseStep 9796211 = 14694317) B14694317
theorem B1719599 : Blo 1719060 1719599 := bstep (se 1 (by rfl) ⟨1289699, by rfl⟩ : syracuseStep 1719599 = 2579399) B2579399
theorem B1719935 : Blo 1719060 1719935 := bstep (se 1 (by rfl) ⟨1289951, by rfl⟩ : syracuseStep 1719935 = 2579903) B2579903
theorem B1720319 : Blo 1719060 1720319 := bstep (se 1 (by rfl) ⟨1290239, by rfl⟩ : syracuseStep 1720319 = 2580479) B2580479
theorem B1720815 : Blo 1719060 1720815 := bstep (se 1 (by rfl) ⟨1290611, by rfl⟩ : syracuseStep 1720815 = 2581223) B2581223
theorem B2581439 : Blo 1719060 2581439 := bstep (se 1 (by rfl) ⟨1936079, by rfl⟩ : syracuseStep 2581439 = 3872159) B3872159
theorem B2581535 : Blo 1719060 2581535 := bstep (se 1 (by rfl) ⟨1936151, by rfl⟩ : syracuseStep 2581535 = 3872303) B3872303
theorem B13059791 : Blo 1719060 13059791 := bstep (se 1 (by rfl) ⟨9794843, by rfl⟩ : syracuseStep 13059791 = 19589687) B19589687
theorem B6530807 : Blo 1719060 6530807 := bstep (se 1 (by rfl) ⟨4898105, by rfl⟩ : syracuseStep 6530807 = 9796211) B9796211
theorem B2903033 : Blo 1719060 2903033 := bstep (se 2 (by rfl) ⟨1088637, by rfl⟩ : syracuseStep 2903033 = 2177275) B2177275
theorem B3869999 : Blo 1719060 3869999 := bstep (se 1 (by rfl) ⟨2902499, by rfl⟩ : syracuseStep 3869999 = 5804999) B5804999
theorem B6532919 : Blo 1719060 6532919 := bstep (se 1 (by rfl) ⟨4899689, by rfl⟩ : syracuseStep 6532919 = 9799379) B9799379
theorem B3922145 : Blo 1719060 3922145 := bstep (se 2 (by rfl) ⟨1470804, by rfl⟩ : syracuseStep 3922145 = 2941609) B2941609
theorem B5807159 : Blo 1719060 5807159 := bstep (se 1 (by rfl) ⟨4355369, by rfl⟩ : syracuseStep 5807159 = 8710739) B8710739
theorem B1720959 : Blo 1719060 1720959 := bstep (se 1 (by rfl) ⟨1290719, by rfl⟩ : syracuseStep 1720959 = 2581439) B2581439
theorem B1721023 : Blo 1719060 1721023 := bstep (se 1 (by rfl) ⟨1290767, by rfl⟩ : syracuseStep 1721023 = 2581535) B2581535
theorem B2614763 : Blo 1719060 2614763 := bstep (se 1 (by rfl) ⟨1961072, by rfl⟩ : syracuseStep 2614763 = 3922145) B3922145
theorem B1935355 : Blo 1719060 1935355 := bstep (se 1 (by rfl) ⟨1451516, by rfl⟩ : syracuseStep 1935355 = 2903033) B2903033
theorem B4353871 : Blo 1719060 4353871 := bstep (se 1 (by rfl) ⟨3265403, by rfl⟩ : syracuseStep 4353871 = 6530807) B6530807
theorem B3871439 : Blo 1719060 3871439 := bstep (se 1 (by rfl) ⟨2903579, by rfl⟩ : syracuseStep 3871439 = 5807159) B5807159
theorem B4355279 : Blo 1719060 4355279 := bstep (se 1 (by rfl) ⟨3266459, by rfl⟩ : syracuseStep 4355279 = 6532919) B6532919
theorem B8706527 : Blo 1719060 8706527 := bstep (se 1 (by rfl) ⟨6529895, by rfl⟩ : syracuseStep 8706527 = 13059791) B13059791
theorem B2579999 : Blo 1719060 2579999 := bstep (se 1 (by rfl) ⟨1934999, by rfl⟩ : syracuseStep 2579999 = 3869999) B3869999
theorem B2580959 : Blo 1719060 2580959 := bstep (se 1 (by rfl) ⟨1935719, by rfl⟩ : syracuseStep 2580959 = 3871439) B3871439
theorem B2903519 : Blo 1719060 2903519 := bstep (se 1 (by rfl) ⟨2177639, by rfl⟩ : syracuseStep 2903519 = 4355279) B4355279
theorem B5804351 : Blo 1719060 5804351 := bstep (se 1 (by rfl) ⟨4353263, by rfl⟩ : syracuseStep 5804351 = 8706527) B8706527
theorem B5805161 : Blo 1719060 5805161 := bstep (se 2 (by rfl) ⟨2176935, by rfl⟩ : syracuseStep 5805161 = 4353871) B4353871
theorem B1743175 : Blo 1719060 1743175 := bstep (se 1 (by rfl) ⟨1307381, by rfl⟩ : syracuseStep 1743175 = 2614763) B2614763
theorem B1719999 : Blo 1719060 1719999 := bstep (se 1 (by rfl) ⟨1289999, by rfl⟩ : syracuseStep 1719999 = 2579999) B2579999
theorem B2580473 : Blo 1719060 2580473 := bstep (se 2 (by rfl) ⟨967677, by rfl⟩ : syracuseStep 2580473 = 1935355) B1935355
theorem B1720639 : Blo 1719060 1720639 := bstep (se 1 (by rfl) ⟨1290479, by rfl⟩ : syracuseStep 1720639 = 2580959) B2580959
theorem B1935679 : Blo 1719060 1935679 := bstep (se 1 (by rfl) ⟨1451759, by rfl⟩ : syracuseStep 1935679 = 2903519) B2903519
theorem B3869567 : Blo 1719060 3869567 := bstep (se 1 (by rfl) ⟨2902175, by rfl⟩ : syracuseStep 3869567 = 5804351) B5804351
theorem B3870107 : Blo 1719060 3870107 := bstep (se 1 (by rfl) ⟨2902580, by rfl⟩ : syracuseStep 3870107 = 5805161) B5805161
theorem B2324233 : Blo 1719060 2324233 := bstep (se 2 (by rfl) ⟨871587, by rfl⟩ : syracuseStep 2324233 = 1743175) B1743175
theorem B1720315 : Blo 1719060 1720315 := bstep (se 1 (by rfl) ⟨1290236, by rfl⟩ : syracuseStep 1720315 = 2580473) B2580473
theorem B2580905 : Blo 1719060 2580905 := bstep (se 2 (by rfl) ⟨967839, by rfl⟩ : syracuseStep 2580905 = 1935679) B1935679
theorem B12395909 : Blo 1719060 12395909 := bstep (se 4 (by rfl) ⟨1162116, by rfl⟩ : syracuseStep 12395909 = 2324233) B2324233
theorem B2579711 : Blo 1719060 2579711 := bstep (se 1 (by rfl) ⟨1934783, by rfl⟩ : syracuseStep 2579711 = 3869567) B3869567
theorem B2580071 : Blo 1719060 2580071 := bstep (se 1 (by rfl) ⟨1935053, by rfl⟩ : syracuseStep 2580071 = 3870107) B3870107
theorem B1720603 : Blo 1719060 1720603 := bstep (se 1 (by rfl) ⟨1290452, by rfl⟩ : syracuseStep 1720603 = 2580905) B2580905
theorem B8263939 : Blo 1719060 8263939 := bstep (se 1 (by rfl) ⟨6197954, by rfl⟩ : syracuseStep 8263939 = 12395909) B12395909
theorem B1719807 : Blo 1719060 1719807 := bstep (se 1 (by rfl) ⟨1289855, by rfl⟩ : syracuseStep 1719807 = 2579711) B2579711
theorem B1720047 : Blo 1719060 1720047 := bstep (se 1 (by rfl) ⟨1290035, by rfl⟩ : syracuseStep 1720047 = 2580071) B2580071
theorem B11018585 : Blo 1719060 11018585 := bstep (se 2 (by rfl) ⟨4131969, by rfl⟩ : syracuseStep 11018585 = 8263939) B8263939
theorem B7345723 : Blo 1719060 7345723 := bstep (se 1 (by rfl) ⟨5509292, by rfl⟩ : syracuseStep 7345723 = 11018585) B11018585
theorem B9794297 : Blo 1719060 9794297 := bstep (se 2 (by rfl) ⟨3672861, by rfl⟩ : syracuseStep 9794297 = 7345723) B7345723
theorem B6529531 : Blo 1719060 6529531 := bstep (se 1 (by rfl) ⟨4897148, by rfl⟩ : syracuseStep 6529531 = 9794297) B9794297
theorem B8706041 : Blo 1719060 8706041 := bstep (se 2 (by rfl) ⟨3264765, by rfl⟩ : syracuseStep 8706041 = 6529531) B6529531
theorem B5804027 : Blo 1719060 5804027 := bstep (se 1 (by rfl) ⟨4353020, by rfl⟩ : syracuseStep 5804027 = 8706041) B8706041
theorem B3869351 : Blo 1719060 3869351 := bstep (se 1 (by rfl) ⟨2902013, by rfl⟩ : syracuseStep 3869351 = 5804027) B5804027
theorem B2579567 : Blo 1719060 2579567 := bstep (se 1 (by rfl) ⟨1934675, by rfl⟩ : syracuseStep 2579567 = 3869351) B3869351
theorem B1719711 : Blo 1719060 1719711 := bstep (se 1 (by rfl) ⟨1289783, by rfl⟩ : syracuseStep 1719711 = 2579567) B2579567

theorem C0 (j : ℕ) (h1 : 429765 ≤ j) (h2 : j ≤ 430264) : Blo 1719060 (4 * j + 3) := by
  interval_cases j
  · exact B1719063
  · exact B1719067
  · exact B1719071
  · exact B1719075
  · exact B1719079
  · exact B1719083
  · exact B1719087
  · exact B1719091
  · exact B1719095
  · exact B1719099
  · exact B1719103
  · exact B1719107
  · exact B1719111
  · exact B1719115
  · exact B1719119
  · exact B1719123
  · exact B1719127
  · exact B1719131
  · exact B1719135
  · exact B1719139
  · exact B1719143
  · exact B1719147
  · exact B1719151
  · exact B1719155
  · exact B1719159
  · exact B1719163
  · exact B1719167
  · exact B1719171
  · exact B1719175
  · exact B1719179
  · exact B1719183
  · exact B1719187
  · exact B1719191
  · exact B1719195
  · exact B1719199
  · exact B1719203
  · exact B1719207
  · exact B1719211
  · exact B1719215
  · exact B1719219
  · exact B1719223
  · exact B1719227
  · exact B1719231
  · exact B1719235
  · exact B1719239
  · exact B1719243
  · exact B1719247
  · exact B1719251
  · exact B1719255
  · exact B1719259
  · exact B1719263
  · exact B1719267
  · exact B1719271
  · exact B1719275
  · exact B1719279
  · exact B1719283
  · exact B1719287
  · exact B1719291
  · exact B1719295
  · exact B1719299
  · exact B1719303
  · exact B1719307
  · exact B1719311
  · exact B1719315
  · exact B1719319
  · exact B1719323
  · exact B1719327
  · exact B1719331
  · exact B1719335
  · exact B1719339
  · exact B1719343
  · exact B1719347
  · exact B1719351
  · exact B1719355
  · exact B1719359
  · exact B1719363
  · exact B1719367
  · exact B1719371
  · exact B1719375
  · exact B1719379
  · exact B1719383
  · exact B1719387
  · exact B1719391
  · exact B1719395
  · exact B1719399
  · exact B1719403
  · exact B1719407
  · exact B1719411
  · exact B1719415
  · exact B1719419
  · exact B1719423
  · exact B1719427
  · exact B1719431
  · exact B1719435
  · exact B1719439
  · exact B1719443
  · exact B1719447
  · exact B1719451
  · exact B1719455
  · exact B1719459
  · exact B1719463
  · exact B1719467
  · exact B1719471
  · exact B1719475
  · exact B1719479
  · exact B1719483
  · exact B1719487
  · exact B1719491
  · exact B1719495
  · exact B1719499
  · exact B1719503
  · exact B1719507
  · exact B1719511
  · exact B1719515
  · exact B1719519
  · exact B1719523
  · exact B1719527
  · exact B1719531
  · exact B1719535
  · exact B1719539
  · exact B1719543
  · exact B1719547
  · exact B1719551
  · exact B1719555
  · exact B1719559
  · exact B1719563
  · exact B1719567
  · exact B1719571
  · exact B1719575
  · exact B1719579
  · exact B1719583
  · exact B1719587
  · exact B1719591
  · exact B1719595
  · exact B1719599
  · exact B1719603
  · exact B1719607
  · exact B1719611
  · exact B1719615
  · exact B1719619
  · exact B1719623
  · exact B1719627
  · exact B1719631
  · exact B1719635
  · exact B1719639
  · exact B1719643
  · exact B1719647
  · exact B1719651
  · exact B1719655
  · exact B1719659
  · exact B1719663
  · exact B1719667
  · exact B1719671
  · exact B1719675
  · exact B1719679
  · exact B1719683
  · exact B1719687
  · exact B1719691
  · exact B1719695
  · exact B1719699
  · exact B1719703
  · exact B1719707
  · exact B1719711
  · exact B1719715
  · exact B1719719
  · exact B1719723
  · exact B1719727
  · exact B1719731
  · exact B1719735
  · exact B1719739
  · exact B1719743
  · exact B1719747
  · exact B1719751
  · exact B1719755
  · exact B1719759
  · exact B1719763
  · exact B1719767
  · exact B1719771
  · exact B1719775
  · exact B1719779
  · exact B1719783
  · exact B1719787
  · exact B1719791
  · exact B1719795
  · exact B1719799
  · exact B1719803
  · exact B1719807
  · exact B1719811
  · exact B1719815
  · exact B1719819
  · exact B1719823
  · exact B1719827
  · exact B1719831
  · exact B1719835
  · exact B1719839
  · exact B1719843
  · exact B1719847
  · exact B1719851
  · exact B1719855
  · exact B1719859
  · exact B1719863
  · exact B1719867
  · exact B1719871
  · exact B1719875
  · exact B1719879
  · exact B1719883
  · exact B1719887
  · exact B1719891
  · exact B1719895
  · exact B1719899
  · exact B1719903
  · exact B1719907
  · exact B1719911
  · exact B1719915
  · exact B1719919
  · exact B1719923
  · exact B1719927
  · exact B1719931
  · exact B1719935
  · exact B1719939
  · exact B1719943
  · exact B1719947
  · exact B1719951
  · exact B1719955
  · exact B1719959
  · exact B1719963
  · exact B1719967
  · exact B1719971
  · exact B1719975
  · exact B1719979
  · exact B1719983
  · exact B1719987
  · exact B1719991
  · exact B1719995
  · exact B1719999
  · exact B1720003
  · exact B1720007
  · exact B1720011
  · exact B1720015
  · exact B1720019
  · exact B1720023
  · exact B1720027
  · exact B1720031
  · exact B1720035
  · exact B1720039
  · exact B1720043
  · exact B1720047
  · exact B1720051
  · exact B1720055
  · exact B1720059
  · exact B1720063
  · exact B1720067
  · exact B1720071
  · exact B1720075
  · exact B1720079
  · exact B1720083
  · exact B1720087
  · exact B1720091
  · exact B1720095
  · exact B1720099
  · exact B1720103
  · exact B1720107
  · exact B1720111
  · exact B1720115
  · exact B1720119
  · exact B1720123
  · exact B1720127
  · exact B1720131
  · exact B1720135
  · exact B1720139
  · exact B1720143
  · exact B1720147
  · exact B1720151
  · exact B1720155
  · exact B1720159
  · exact B1720163
  · exact B1720167
  · exact B1720171
  · exact B1720175
  · exact B1720179
  · exact B1720183
  · exact B1720187
  · exact B1720191
  · exact B1720195
  · exact B1720199
  · exact B1720203
  · exact B1720207
  · exact B1720211
  · exact B1720215
  · exact B1720219
  · exact B1720223
  · exact B1720227
  · exact B1720231
  · exact B1720235
  · exact B1720239
  · exact B1720243
  · exact B1720247
  · exact B1720251
  · exact B1720255
  · exact B1720259
  · exact B1720263
  · exact B1720267
  · exact B1720271
  · exact B1720275
  · exact B1720279
  · exact B1720283
  · exact B1720287
  · exact B1720291
  · exact B1720295
  · exact B1720299
  · exact B1720303
  · exact B1720307
  · exact B1720311
  · exact B1720315
  · exact B1720319
  · exact B1720323
  · exact B1720327
  · exact B1720331
  · exact B1720335
  · exact B1720339
  · exact B1720343
  · exact B1720347
  · exact B1720351
  · exact B1720355
  · exact B1720359
  · exact B1720363
  · exact B1720367
  · exact B1720371
  · exact B1720375
  · exact B1720379
  · exact B1720383
  · exact B1720387
  · exact B1720391
  · exact B1720395
  · exact B1720399
  · exact B1720403
  · exact B1720407
  · exact B1720411
  · exact B1720415
  · exact B1720419
  · exact B1720423
  · exact B1720427
  · exact B1720431
  · exact B1720435
  · exact B1720439
  · exact B1720443
  · exact B1720447
  · exact B1720451
  · exact B1720455
  · exact B1720459
  · exact B1720463
  · exact B1720467
  · exact B1720471
  · exact B1720475
  · exact B1720479
  · exact B1720483
  · exact B1720487
  · exact B1720491
  · exact B1720495
  · exact B1720499
  · exact B1720503
  · exact B1720507
  · exact B1720511
  · exact B1720515
  · exact B1720519
  · exact B1720523
  · exact B1720527
  · exact B1720531
  · exact B1720535
  · exact B1720539
  · exact B1720543
  · exact B1720547
  · exact B1720551
  · exact B1720555
  · exact B1720559
  · exact B1720563
  · exact B1720567
  · exact B1720571
  · exact B1720575
  · exact B1720579
  · exact B1720583
  · exact B1720587
  · exact B1720591
  · exact B1720595
  · exact B1720599
  · exact B1720603
  · exact B1720607
  · exact B1720611
  · exact B1720615
  · exact B1720619
  · exact B1720623
  · exact B1720627
  · exact B1720631
  · exact B1720635
  · exact B1720639
  · exact B1720643
  · exact B1720647
  · exact B1720651
  · exact B1720655
  · exact B1720659
  · exact B1720663
  · exact B1720667
  · exact B1720671
  · exact B1720675
  · exact B1720679
  · exact B1720683
  · exact B1720687
  · exact B1720691
  · exact B1720695
  · exact B1720699
  · exact B1720703
  · exact B1720707
  · exact B1720711
  · exact B1720715
  · exact B1720719
  · exact B1720723
  · exact B1720727
  · exact B1720731
  · exact B1720735
  · exact B1720739
  · exact B1720743
  · exact B1720747
  · exact B1720751
  · exact B1720755
  · exact B1720759
  · exact B1720763
  · exact B1720767
  · exact B1720771
  · exact B1720775
  · exact B1720779
  · exact B1720783
  · exact B1720787
  · exact B1720791
  · exact B1720795
  · exact B1720799
  · exact B1720803
  · exact B1720807
  · exact B1720811
  · exact B1720815
  · exact B1720819
  · exact B1720823
  · exact B1720827
  · exact B1720831
  · exact B1720835
  · exact B1720839
  · exact B1720843
  · exact B1720847
  · exact B1720851
  · exact B1720855
  · exact B1720859
  · exact B1720863
  · exact B1720867
  · exact B1720871
  · exact B1720875
  · exact B1720879
  · exact B1720883
  · exact B1720887
  · exact B1720891
  · exact B1720895
  · exact B1720899
  · exact B1720903
  · exact B1720907
  · exact B1720911
  · exact B1720915
  · exact B1720919
  · exact B1720923
  · exact B1720927
  · exact B1720931
  · exact B1720935
  · exact B1720939
  · exact B1720943
  · exact B1720947
  · exact B1720951
  · exact B1720955
  · exact B1720959
  · exact B1720963
  · exact B1720967
  · exact B1720971
  · exact B1720975
  · exact B1720979
  · exact B1720983
  · exact B1720987
  · exact B1720991
  · exact B1720995
  · exact B1720999
  · exact B1721003
  · exact B1721007
  · exact B1721011
  · exact B1721015
  · exact B1721019
  · exact B1721023
  · exact B1721027
  · exact B1721031
  · exact B1721035
  · exact B1721039
  · exact B1721043
  · exact B1721047
  · exact B1721051
  · exact B1721055
  · exact B1721059

theorem solution (m : ℕ) (hlo : 1719060 ≤ m) (hhi : m ≤ 1721060) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 429765 ≤ j := by omega
    have hj2 : j ≤ 430264 := by omega
    have hb : Blo 1719060 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
