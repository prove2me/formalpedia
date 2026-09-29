-- Prove2me | solution 1 for syracuse_descends_range_287828_291828
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:44:14.461468+00:00
-- url     : https://prove2.me/submissions/b626130d-2f48-4921-a17f-10e9031d3811

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


theorem B327685 : Blo 287828 327685 := bbase (se 4 (by rfl) ⟨30720, by rfl⟩ : syracuseStep 327685 = 61441) (by norm_num)
theorem B655397 : Blo 287828 655397 := bbase (se 4 (by rfl) ⟨61443, by rfl⟩ : syracuseStep 655397 = 122887) (by norm_num)
theorem B327721 : Blo 287828 327721 := bbase (se 2 (by rfl) ⟨122895, by rfl⟩ : syracuseStep 327721 = 245791) (by norm_num)
theorem B327757 : Blo 287828 327757 := bbase (se 3 (by rfl) ⟨61454, by rfl⟩ : syracuseStep 327757 = 122909) (by norm_num)
theorem B655469 : Blo 287828 655469 := bbase (se 3 (by rfl) ⟨122900, by rfl⟩ : syracuseStep 655469 = 245801) (by norm_num)
theorem B491629 : Blo 287828 491629 := bbase (se 3 (by rfl) ⟨92180, by rfl⟩ : syracuseStep 491629 = 184361) (by norm_num)
theorem B327793 : Blo 287828 327793 := bbase (se 2 (by rfl) ⟨122922, by rfl⟩ : syracuseStep 327793 = 245845) (by norm_num)
theorem B393349 : Blo 287828 393349 := bbase (se 4 (by rfl) ⟨36876, by rfl⟩ : syracuseStep 393349 = 73753) (by norm_num)
theorem B327829 : Blo 287828 327829 := bbase (se 6 (by rfl) ⟨7683, by rfl⟩ : syracuseStep 327829 = 15367) (by norm_num)
theorem B622741 : Blo 287828 622741 := bbase (se 6 (by rfl) ⟨14595, by rfl⟩ : syracuseStep 622741 = 29191) (by norm_num)
theorem B295093 : Blo 287828 295093 := bbase (se 5 (by rfl) ⟨13832, by rfl⟩ : syracuseStep 295093 = 27665) (by norm_num)
theorem B655541 : Blo 287828 655541 := bbase (se 5 (by rfl) ⟨30728, by rfl⟩ : syracuseStep 655541 = 61457) (by norm_num)
theorem B327865 : Blo 287828 327865 := bbase (se 2 (by rfl) ⟨122949, by rfl⟩ : syracuseStep 327865 = 245899) (by norm_num)
theorem B491717 : Blo 287828 491717 := bbase (se 4 (by rfl) ⟨46098, by rfl⟩ : syracuseStep 491717 = 92197) (by norm_num)
theorem B327901 : Blo 287828 327901 := bbase (se 3 (by rfl) ⟨61481, by rfl⟩ : syracuseStep 327901 = 122963) (by norm_num)
theorem B983285 : Blo 287828 983285 := bbase (se 5 (by rfl) ⟨46091, by rfl⟩ : syracuseStep 983285 = 92183) (by norm_num)
theorem B655613 : Blo 287828 655613 := bbase (se 3 (by rfl) ⟨122927, by rfl⟩ : syracuseStep 655613 = 245855) (by norm_num)
theorem B327937 : Blo 287828 327937 := bbase (se 2 (by rfl) ⟨122976, by rfl⟩ : syracuseStep 327937 = 245953) (by norm_num)
theorem B524573 : Blo 287828 524573 := bbase (se 3 (by rfl) ⟨98357, by rfl⟩ : syracuseStep 524573 = 196715) (by norm_num)
theorem B327973 : Blo 287828 327973 := bbase (se 4 (by rfl) ⟨30747, by rfl⟩ : syracuseStep 327973 = 61495) (by norm_num)
theorem B622885 : Blo 287828 622885 := bbase (se 4 (by rfl) ⟨58395, by rfl⟩ : syracuseStep 622885 = 116791) (by norm_num)
theorem B655685 : Blo 287828 655685 := bbase (se 4 (by rfl) ⟨61470, by rfl⟩ : syracuseStep 655685 = 122941) (by norm_num)
theorem B491845 : Blo 287828 491845 := bbase (se 4 (by rfl) ⟨46110, by rfl⟩ : syracuseStep 491845 = 92221) (by norm_num)
theorem B328009 : Blo 287828 328009 := bbase (se 2 (by rfl) ⟨123003, by rfl⟩ : syracuseStep 328009 = 246007) (by norm_num)
theorem B2359637 : Blo 287828 2359637 := bbase (se 10 (by rfl) ⟨3456, by rfl⟩ : syracuseStep 2359637 = 6913) (by norm_num)
theorem B328045 : Blo 287828 328045 := bbase (se 3 (by rfl) ⟨61508, by rfl⟩ : syracuseStep 328045 = 123017) (by norm_num)
theorem B655757 : Blo 287828 655757 := bbase (se 3 (by rfl) ⟨122954, by rfl⟩ : syracuseStep 655757 = 245909) (by norm_num)
theorem B328081 : Blo 287828 328081 := bbase (se 2 (by rfl) ⟨123030, by rfl⟩ : syracuseStep 328081 = 246061) (by norm_num)
theorem B491933 : Blo 287828 491933 := bbase (se 3 (by rfl) ⟨92237, by rfl⟩ : syracuseStep 491933 = 184475) (by norm_num)
theorem B328117 : Blo 287828 328117 := bbase (se 5 (by rfl) ⟨15380, by rfl⟩ : syracuseStep 328117 = 30761) (by norm_num)
theorem B655829 : Blo 287828 655829 := bbase (se 7 (by rfl) ⟨7685, by rfl⟩ : syracuseStep 655829 = 15371) (by norm_num)
theorem B328153 : Blo 287828 328153 := bbase (se 2 (by rfl) ⟨123057, by rfl⟩ : syracuseStep 328153 = 246115) (by norm_num)
theorem B295417 : Blo 287828 295417 := bbase (se 2 (by rfl) ⟨110781, by rfl⟩ : syracuseStep 295417 = 221563) (by norm_num)
theorem B328189 : Blo 287828 328189 := bbase (se 3 (by rfl) ⟨61535, by rfl⟩ : syracuseStep 328189 = 123071) (by norm_num)
theorem B655901 : Blo 287828 655901 := bbase (se 3 (by rfl) ⟨122981, by rfl⟩ : syracuseStep 655901 = 245963) (by norm_num)
theorem B492061 : Blo 287828 492061 := bbase (se 3 (by rfl) ⟨92261, by rfl⟩ : syracuseStep 492061 = 184523) (by norm_num)
theorem B328225 : Blo 287828 328225 := bbase (se 2 (by rfl) ⟨123084, by rfl⟩ : syracuseStep 328225 = 246169) (by norm_num)
theorem B328261 : Blo 287828 328261 := bbase (se 4 (by rfl) ⟨30774, by rfl⟩ : syracuseStep 328261 = 61549) (by norm_num)
theorem B655973 : Blo 287828 655973 := bbase (se 4 (by rfl) ⟨61497, by rfl⟩ : syracuseStep 655973 = 122995) (by norm_num)
theorem B328297 : Blo 287828 328297 := bbase (se 2 (by rfl) ⟨123111, by rfl⟩ : syracuseStep 328297 = 246223) (by norm_num)
theorem B492149 : Blo 287828 492149 := bbase (se 5 (by rfl) ⟨23069, by rfl⟩ : syracuseStep 492149 = 46139) (by norm_num)
theorem B623261 : Blo 287828 623261 := bbase (se 3 (by rfl) ⟨116861, by rfl⟩ : syracuseStep 623261 = 233723) (by norm_num)
theorem B983717 : Blo 287828 983717 := bbase (se 4 (by rfl) ⟨92223, by rfl⟩ : syracuseStep 983717 = 184447) (by norm_num)
theorem B656045 : Blo 287828 656045 := bbase (se 3 (by rfl) ⟨123008, by rfl⟩ : syracuseStep 656045 = 246017) (by norm_num)
theorem B6292181 : Blo 287828 6292181 := bbase (se 7 (by rfl) ⟨73736, by rfl⟩ : syracuseStep 6292181 = 147473) (by norm_num)
theorem B328421 : Blo 287828 328421 := bbase (se 4 (by rfl) ⟨30789, by rfl⟩ : syracuseStep 328421 = 61579) (by norm_num)
theorem B656117 : Blo 287828 656117 := bbase (se 5 (by rfl) ⟨30755, by rfl⟩ : syracuseStep 656117 = 61511) (by norm_num)
theorem B492277 : Blo 287828 492277 := bbase (se 5 (by rfl) ⟨23075, by rfl⟩ : syracuseStep 492277 = 46151) (by norm_num)
theorem B1475333 : Blo 287828 1475333 := bbase (se 4 (by rfl) ⟨138312, by rfl⟩ : syracuseStep 1475333 = 276625) (by norm_num)
theorem B819989 : Blo 287828 819989 := bbase (se 6 (by rfl) ⟨19218, by rfl⟩ : syracuseStep 819989 = 38437) (by norm_num)
theorem B656189 : Blo 287828 656189 := bbase (se 3 (by rfl) ⟨123035, by rfl⟩ : syracuseStep 656189 = 246071) (by norm_num)
theorem B492365 : Blo 287828 492365 := bbase (se 3 (by rfl) ⟨92318, by rfl⟩ : syracuseStep 492365 = 184637) (by norm_num)
theorem B656261 : Blo 287828 656261 := bbase (se 4 (by rfl) ⟨61524, by rfl⟩ : syracuseStep 656261 = 123049) (by norm_num)
theorem B656333 : Blo 287828 656333 := bbase (se 3 (by rfl) ⟨123062, by rfl⟩ : syracuseStep 656333 = 246125) (by norm_num)
theorem B656405 : Blo 287828 656405 := bbase (se 6 (by rfl) ⟨15384, by rfl⟩ : syracuseStep 656405 = 30769) (by norm_num)
theorem B984149 : Blo 287828 984149 := bbase (se 8 (by rfl) ⟨5766, by rfl⟩ : syracuseStep 984149 = 11533) (by norm_num)
theorem B656477 : Blo 287828 656477 := bbase (se 3 (by rfl) ⟨123089, by rfl⟩ : syracuseStep 656477 = 246179) (by norm_num)
theorem B656549 : Blo 287828 656549 := bbase (se 4 (by rfl) ⟨61551, by rfl⟩ : syracuseStep 656549 = 123103) (by norm_num)
theorem B591077 : Blo 287828 591077 := bbase (se 4 (by rfl) ⟨55413, by rfl⟩ : syracuseStep 591077 = 110827) (by norm_num)
theorem B3736853 : Blo 287828 3736853 := bbase (se 6 (by rfl) ⟨87582, by rfl⟩ : syracuseStep 3736853 = 175165) (by norm_num)
theorem B918821 : Blo 287828 918821 := bbase (se 4 (by rfl) ⟨86139, by rfl⟩ : syracuseStep 918821 = 172279) (by norm_num)
theorem B1050085 : Blo 287828 1050085 := bbase (se 4 (by rfl) ⟨98445, by rfl⟩ : syracuseStep 1050085 = 196891) (by norm_num)
theorem B984581 : Blo 287828 984581 := bbase (se 4 (by rfl) ⟨92304, by rfl⟩ : syracuseStep 984581 = 184609) (by norm_num)
theorem B394813 : Blo 287828 394813 := bbase (se 3 (by rfl) ⟨74027, by rfl⟩ : syracuseStep 394813 = 148055) (by norm_num)
theorem B493229 : Blo 287828 493229 := bbase (se 3 (by rfl) ⟨92480, by rfl⟩ : syracuseStep 493229 = 184961) (by norm_num)
theorem B2197205 : Blo 287828 2197205 := bbase (se 7 (by rfl) ⟨25748, by rfl⟩ : syracuseStep 2197205 = 51497) (by norm_num)
theorem B821173 : Blo 287828 821173 := bbase (se 5 (by rfl) ⟨38492, by rfl⟩ : syracuseStep 821173 = 76985) (by norm_num)
theorem B1476629 : Blo 287828 1476629 := bbase (se 6 (by rfl) ⟨34608, by rfl⟩ : syracuseStep 1476629 = 69217) (by norm_num)
theorem B821333 : Blo 287828 821333 := bbase (se 8 (by rfl) ⟨4812, by rfl⟩ : syracuseStep 821333 = 9625) (by norm_num)
theorem B1181861 : Blo 287828 1181861 := bbase (se 4 (by rfl) ⟨110799, by rfl⟩ : syracuseStep 1181861 = 221599) (by norm_num)
theorem B1575125 : Blo 287828 1575125 := bbase (se 7 (by rfl) ⟨18458, by rfl⟩ : syracuseStep 1575125 = 36917) (by norm_num)
theorem B2787605 : Blo 287828 2787605 := bbase (se 6 (by rfl) ⟨65334, by rfl⟩ : syracuseStep 2787605 = 130669) (by norm_num)
theorem B788773 : Blo 287828 788773 := bbase (se 4 (by rfl) ⟨73947, by rfl⟩ : syracuseStep 788773 = 147895) (by norm_num)
theorem B821573 : Blo 287828 821573 := bbase (se 4 (by rfl) ⟨77022, by rfl⟩ : syracuseStep 821573 = 154045) (by norm_num)
theorem B559445 : Blo 287828 559445 := bbase (se 10 (by rfl) ⟨819, by rfl⟩ : syracuseStep 559445 = 1639) (by norm_num)
theorem B330205 : Blo 287828 330205 := bbase (se 3 (by rfl) ⟨61913, by rfl⟩ : syracuseStep 330205 = 123827) (by norm_num)
theorem B821765 : Blo 287828 821765 := bbase (se 4 (by rfl) ⟨77040, by rfl⟩ : syracuseStep 821765 = 154081) (by norm_num)
theorem B428885 : Blo 287828 428885 := bbase (se 9 (by rfl) ⟨1256, by rfl⟩ : syracuseStep 428885 = 2513) (by norm_num)
theorem B461693 : Blo 287828 461693 := bbase (se 3 (by rfl) ⟨86567, by rfl⟩ : syracuseStep 461693 = 173135) (by norm_num)
theorem B1313813 : Blo 287828 1313813 := bbase (se 6 (by rfl) ⟨30792, by rfl⟩ : syracuseStep 1313813 = 61585) (by norm_num)
theorem B461981 : Blo 287828 461981 := bbase (se 3 (by rfl) ⟨86621, by rfl⟩ : syracuseStep 461981 = 173243) (by norm_num)
theorem B331177 : Blo 287828 331177 := bbase (se 2 (by rfl) ⟨124191, by rfl⟩ : syracuseStep 331177 = 248383) (by norm_num)
theorem B822757 : Blo 287828 822757 := bbase (se 4 (by rfl) ⟨77133, by rfl⟩ : syracuseStep 822757 = 154267) (by norm_num)
theorem B462397 : Blo 287828 462397 := bbase (se 3 (by rfl) ⟨86699, by rfl⟩ : syracuseStep 462397 = 173399) (by norm_num)
theorem B2100853 : Blo 287828 2100853 := bbase (se 5 (by rfl) ⟨98477, by rfl⟩ : syracuseStep 2100853 = 196955) (by norm_num)
theorem B495253 : Blo 287828 495253 := bbase (se 6 (by rfl) ⟨11607, by rfl⟩ : syracuseStep 495253 = 23215) (by norm_num)
theorem B659141 : Blo 287828 659141 := bbase (se 4 (by rfl) ⟨61794, by rfl⟩ : syracuseStep 659141 = 123589) (by norm_num)
theorem B691973 : Blo 287828 691973 := bbase (se 4 (by rfl) ⟨64872, by rfl⟩ : syracuseStep 691973 = 129745) (by norm_num)
theorem B364333 : Blo 287828 364333 := bbase (se 3 (by rfl) ⟨68312, by rfl⟩ : syracuseStep 364333 = 136625) (by norm_num)
theorem B397181 : Blo 287828 397181 := bbase (se 3 (by rfl) ⟨74471, by rfl⟩ : syracuseStep 397181 = 148943) (by norm_num)
theorem B364429 : Blo 287828 364429 := bbase (se 3 (by rfl) ⟨68330, by rfl⟩ : syracuseStep 364429 = 136661) (by norm_num)
theorem B561077 : Blo 287828 561077 := bbase (se 5 (by rfl) ⟨26300, by rfl⟩ : syracuseStep 561077 = 52601) (by norm_num)
theorem B364601 : Blo 287828 364601 := bbase (se 2 (by rfl) ⟨136725, by rfl⟩ : syracuseStep 364601 = 273451) (by norm_num)
theorem B364657 : Blo 287828 364657 := bbase (se 2 (by rfl) ⟨136746, by rfl⟩ : syracuseStep 364657 = 273493) (by norm_num)
theorem B364753 : Blo 287828 364753 := bbase (se 2 (by rfl) ⟨136782, by rfl⟩ : syracuseStep 364753 = 273565) (by norm_num)
theorem B364925 : Blo 287828 364925 := bbase (se 3 (by rfl) ⟨68423, by rfl⟩ : syracuseStep 364925 = 136847) (by norm_num)
theorem B364981 : Blo 287828 364981 := bbase (se 5 (by rfl) ⟨17108, by rfl⟩ : syracuseStep 364981 = 34217) (by norm_num)
theorem B463333 : Blo 287828 463333 := bbase (se 4 (by rfl) ⟨43437, by rfl⟩ : syracuseStep 463333 = 86875) (by norm_num)
theorem B922117 : Blo 287828 922117 := bbase (se 4 (by rfl) ⟨86448, by rfl⟩ : syracuseStep 922117 = 172897) (by norm_num)
theorem B365077 : Blo 287828 365077 := bbase (se 6 (by rfl) ⟨8556, by rfl⟩ : syracuseStep 365077 = 17113) (by norm_num)
theorem B823861 : Blo 287828 823861 := bbase (se 5 (by rfl) ⟨38618, by rfl⟩ : syracuseStep 823861 = 77237) (by norm_num)
theorem B660053 : Blo 287828 660053 := bbase (se 8 (by rfl) ⟨3867, by rfl⟩ : syracuseStep 660053 = 7735) (by norm_num)
theorem B365249 : Blo 287828 365249 := bbase (se 2 (by rfl) ⟨136968, by rfl⟩ : syracuseStep 365249 = 273937) (by norm_num)
theorem B365305 : Blo 287828 365305 := bbase (se 2 (by rfl) ⟨136989, by rfl⟩ : syracuseStep 365305 = 273979) (by norm_num)
theorem B365401 : Blo 287828 365401 := bbase (se 2 (by rfl) ⟨137025, by rfl⟩ : syracuseStep 365401 = 274051) (by norm_num)
theorem B693173 : Blo 287828 693173 := bbase (se 5 (by rfl) ⟨32492, by rfl⟩ : syracuseStep 693173 = 64985) (by norm_num)
theorem B922565 : Blo 287828 922565 := bbase (se 4 (by rfl) ⟨86490, by rfl⟩ : syracuseStep 922565 = 172981) (by norm_num)
theorem B365573 : Blo 287828 365573 := bbase (se 4 (by rfl) ⟨34272, by rfl⟩ : syracuseStep 365573 = 68545) (by norm_num)
theorem B365629 : Blo 287828 365629 := bbase (se 3 (by rfl) ⟨68555, by rfl⟩ : syracuseStep 365629 = 137111) (by norm_num)
theorem B365725 : Blo 287828 365725 := bbase (se 3 (by rfl) ⟨68573, by rfl⟩ : syracuseStep 365725 = 137147) (by norm_num)
theorem B300217 : Blo 287828 300217 := bbase (se 2 (by rfl) ⟨112581, by rfl⟩ : syracuseStep 300217 = 225163) (by norm_num)
theorem B988469 : Blo 287828 988469 := bbase (se 5 (by rfl) ⟨46334, by rfl⟩ : syracuseStep 988469 = 92669) (by norm_num)
theorem B660797 : Blo 287828 660797 := bbase (se 3 (by rfl) ⟨123899, by rfl⟩ : syracuseStep 660797 = 247799) (by norm_num)
theorem B365897 : Blo 287828 365897 := bbase (se 2 (by rfl) ⟨137211, by rfl⟩ : syracuseStep 365897 = 274423) (by norm_num)
theorem B365953 : Blo 287828 365953 := bbase (se 2 (by rfl) ⟨137232, by rfl⟩ : syracuseStep 365953 = 274465) (by norm_num)
theorem B366049 : Blo 287828 366049 := bbase (se 2 (by rfl) ⟨137268, by rfl⟩ : syracuseStep 366049 = 274537) (by norm_num)
theorem B988757 : Blo 287828 988757 := bbase (se 8 (by rfl) ⟨5793, by rfl⟩ : syracuseStep 988757 = 11587) (by norm_num)
theorem B366221 : Blo 287828 366221 := bbase (se 3 (by rfl) ⟨68666, by rfl⟩ : syracuseStep 366221 = 137333) (by norm_num)
theorem B464525 : Blo 287828 464525 := bbase (se 3 (by rfl) ⟨87098, by rfl⟩ : syracuseStep 464525 = 174197) (by norm_num)
theorem B431765 : Blo 287828 431765 := bbase (se 6 (by rfl) ⟨10119, by rfl⟩ : syracuseStep 431765 = 20239) (by norm_num)
theorem B431789 : Blo 287828 431789 := bbase (se 3 (by rfl) ⟨80960, by rfl⟩ : syracuseStep 431789 = 161921) (by norm_num)
theorem B1316533 : Blo 287828 1316533 := bbase (se 5 (by rfl) ⟨61712, by rfl⟩ : syracuseStep 1316533 = 123425) (by norm_num)
theorem B431813 : Blo 287828 431813 := bbase (se 4 (by rfl) ⟨40482, by rfl⟩ : syracuseStep 431813 = 80965) (by norm_num)
theorem B366277 : Blo 287828 366277 := bbase (se 4 (by rfl) ⟨34338, by rfl⟩ : syracuseStep 366277 = 68677) (by norm_num)
theorem B431837 : Blo 287828 431837 := bbase (se 3 (by rfl) ⟨80969, by rfl⟩ : syracuseStep 431837 = 161939) (by norm_num)
theorem B431861 : Blo 287828 431861 := bbase (se 5 (by rfl) ⟨20243, by rfl⟩ : syracuseStep 431861 = 40487) (by norm_num)
theorem B431885 : Blo 287828 431885 := bbase (se 3 (by rfl) ⟨80978, by rfl⟩ : syracuseStep 431885 = 161957) (by norm_num)
theorem B431909 : Blo 287828 431909 := bbase (se 4 (by rfl) ⟨40491, by rfl⟩ : syracuseStep 431909 = 80983) (by norm_num)
theorem B366373 : Blo 287828 366373 := bbase (se 4 (by rfl) ⟨34347, by rfl⟩ : syracuseStep 366373 = 68695) (by norm_num)
theorem B431933 : Blo 287828 431933 := bbase (se 3 (by rfl) ⟨80987, by rfl⟩ : syracuseStep 431933 = 161975) (by norm_num)
theorem B464717 : Blo 287828 464717 := bbase (se 3 (by rfl) ⟨87134, by rfl⟩ : syracuseStep 464717 = 174269) (by norm_num)
theorem B431957 : Blo 287828 431957 := bbase (se 9 (by rfl) ⟨1265, by rfl⟩ : syracuseStep 431957 = 2531) (by norm_num)
theorem B431981 : Blo 287828 431981 := bbase (se 3 (by rfl) ⟨80996, by rfl⟩ : syracuseStep 431981 = 161993) (by norm_num)
theorem B432005 : Blo 287828 432005 := bbase (se 4 (by rfl) ⟨40500, by rfl⟩ : syracuseStep 432005 = 81001) (by norm_num)
theorem B432029 : Blo 287828 432029 := bbase (se 3 (by rfl) ⟨81005, by rfl⟩ : syracuseStep 432029 = 162011) (by norm_num)
theorem B432053 : Blo 287828 432053 := bbase (se 5 (by rfl) ⟨20252, by rfl⟩ : syracuseStep 432053 = 40505) (by norm_num)
theorem B432077 : Blo 287828 432077 := bbase (se 3 (by rfl) ⟨81014, by rfl⟩ : syracuseStep 432077 = 162029) (by norm_num)
theorem B366545 : Blo 287828 366545 := bbase (se 2 (by rfl) ⟨137454, by rfl⟩ : syracuseStep 366545 = 274909) (by norm_num)
theorem B432101 : Blo 287828 432101 := bbase (se 4 (by rfl) ⟨40509, by rfl⟩ : syracuseStep 432101 = 81019) (by norm_num)
theorem B1644533 : Blo 287828 1644533 := bbase (se 5 (by rfl) ⟨77087, by rfl⟩ : syracuseStep 1644533 = 154175) (by norm_num)
theorem B432125 : Blo 287828 432125 := bbase (se 3 (by rfl) ⟨81023, by rfl⟩ : syracuseStep 432125 = 162047) (by norm_num)
theorem B366601 : Blo 287828 366601 := bbase (se 2 (by rfl) ⟨137475, by rfl⟩ : syracuseStep 366601 = 274951) (by norm_num)
theorem B432149 : Blo 287828 432149 := bbase (se 6 (by rfl) ⟨10128, by rfl⟩ : syracuseStep 432149 = 20257) (by norm_num)
theorem B825365 : Blo 287828 825365 := bbase (se 6 (by rfl) ⟨19344, by rfl⟩ : syracuseStep 825365 = 38689) (by norm_num)
theorem B432173 : Blo 287828 432173 := bbase (se 3 (by rfl) ⟨81032, by rfl⟩ : syracuseStep 432173 = 162065) (by norm_num)
theorem B432197 : Blo 287828 432197 := bbase (se 4 (by rfl) ⟨40518, by rfl⟩ : syracuseStep 432197 = 81037) (by norm_num)
theorem B432221 : Blo 287828 432221 := bbase (se 3 (by rfl) ⟨81041, by rfl⟩ : syracuseStep 432221 = 162083) (by norm_num)
theorem B366697 : Blo 287828 366697 := bbase (se 2 (by rfl) ⟨137511, by rfl⟩ : syracuseStep 366697 = 275023) (by norm_num)
theorem B432245 : Blo 287828 432245 := bbase (se 5 (by rfl) ⟨20261, by rfl⟩ : syracuseStep 432245 = 40523) (by norm_num)
theorem B432269 : Blo 287828 432269 := bbase (se 3 (by rfl) ⟨81050, by rfl⟩ : syracuseStep 432269 = 162101) (by norm_num)
theorem B432293 : Blo 287828 432293 := bbase (se 4 (by rfl) ⟨40527, by rfl⟩ : syracuseStep 432293 = 81055) (by norm_num)
theorem B432317 : Blo 287828 432317 := bbase (se 3 (by rfl) ⟨81059, by rfl⟩ : syracuseStep 432317 = 162119) (by norm_num)
theorem B432341 : Blo 287828 432341 := bbase (se 7 (by rfl) ⟨5066, by rfl⟩ : syracuseStep 432341 = 10133) (by norm_num)
theorem B432365 : Blo 287828 432365 := bbase (se 3 (by rfl) ⟨81068, by rfl⟩ : syracuseStep 432365 = 162137) (by norm_num)
theorem B432389 : Blo 287828 432389 := bbase (se 4 (by rfl) ⟨40536, by rfl⟩ : syracuseStep 432389 = 81073) (by norm_num)
theorem B366869 : Blo 287828 366869 := bbase (se 6 (by rfl) ⟨8598, by rfl⟩ : syracuseStep 366869 = 17197) (by norm_num)
theorem B432413 : Blo 287828 432413 := bbase (se 3 (by rfl) ⟨81077, by rfl⟩ : syracuseStep 432413 = 162155) (by norm_num)
theorem B432437 : Blo 287828 432437 := bbase (se 5 (by rfl) ⟨20270, by rfl⟩ : syracuseStep 432437 = 40541) (by norm_num)
theorem B432461 : Blo 287828 432461 := bbase (se 3 (by rfl) ⟨81086, by rfl⟩ : syracuseStep 432461 = 162173) (by norm_num)
theorem B366925 : Blo 287828 366925 := bbase (se 3 (by rfl) ⟨68798, by rfl⟩ : syracuseStep 366925 = 137597) (by norm_num)
theorem B432485 : Blo 287828 432485 := bbase (se 4 (by rfl) ⟨40545, by rfl⟩ : syracuseStep 432485 = 81091) (by norm_num)
theorem B432509 : Blo 287828 432509 := bbase (se 3 (by rfl) ⟨81095, by rfl⟩ : syracuseStep 432509 = 162191) (by norm_num)
theorem B432533 : Blo 287828 432533 := bbase (se 6 (by rfl) ⟨10137, by rfl⟩ : syracuseStep 432533 = 20275) (by norm_num)
theorem B432557 : Blo 287828 432557 := bbase (se 3 (by rfl) ⟨81104, by rfl⟩ : syracuseStep 432557 = 162209) (by norm_num)
theorem B367021 : Blo 287828 367021 := bbase (se 3 (by rfl) ⟨68816, by rfl⟩ : syracuseStep 367021 = 137633) (by norm_num)
theorem B432581 : Blo 287828 432581 := bbase (se 4 (by rfl) ⟨40554, by rfl⟩ : syracuseStep 432581 = 81109) (by norm_num)
theorem B432605 : Blo 287828 432605 := bbase (se 3 (by rfl) ⟨81113, by rfl⟩ : syracuseStep 432605 = 162227) (by norm_num)
theorem B432629 : Blo 287828 432629 := bbase (se 5 (by rfl) ⟨20279, by rfl⟩ : syracuseStep 432629 = 40559) (by norm_num)
theorem B432653 : Blo 287828 432653 := bbase (se 3 (by rfl) ⟨81122, by rfl⟩ : syracuseStep 432653 = 162245) (by norm_num)
theorem B432677 : Blo 287828 432677 := bbase (se 4 (by rfl) ⟨40563, by rfl⟩ : syracuseStep 432677 = 81127) (by norm_num)
theorem B432701 : Blo 287828 432701 := bbase (se 3 (by rfl) ⟨81131, by rfl⟩ : syracuseStep 432701 = 162263) (by norm_num)
theorem B432725 : Blo 287828 432725 := bbase (se 8 (by rfl) ⟨2535, by rfl⟩ : syracuseStep 432725 = 5071) (by norm_num)
theorem B367193 : Blo 287828 367193 := bbase (se 2 (by rfl) ⟨137697, by rfl⟩ : syracuseStep 367193 = 275395) (by norm_num)
theorem B432749 : Blo 287828 432749 := bbase (se 3 (by rfl) ⟨81140, by rfl⟩ : syracuseStep 432749 = 162281) (by norm_num)
theorem B432773 : Blo 287828 432773 := bbase (se 4 (by rfl) ⟨40572, by rfl⟩ : syracuseStep 432773 = 81145) (by norm_num)
theorem B367249 : Blo 287828 367249 := bbase (se 2 (by rfl) ⟨137718, by rfl⟩ : syracuseStep 367249 = 275437) (by norm_num)
theorem B498325 : Blo 287828 498325 := bbase (se 6 (by rfl) ⟨11679, by rfl⟩ : syracuseStep 498325 = 23359) (by norm_num)
theorem B432797 : Blo 287828 432797 := bbase (se 3 (by rfl) ⟨81149, by rfl⟩ : syracuseStep 432797 = 162299) (by norm_num)
theorem B432821 : Blo 287828 432821 := bbase (se 5 (by rfl) ⟨20288, by rfl⟩ : syracuseStep 432821 = 40577) (by norm_num)
theorem B432845 : Blo 287828 432845 := bbase (se 3 (by rfl) ⟨81158, by rfl⟩ : syracuseStep 432845 = 162317) (by norm_num)
theorem B432869 : Blo 287828 432869 := bbase (se 4 (by rfl) ⟨40581, by rfl⟩ : syracuseStep 432869 = 81163) (by norm_num)
theorem B367345 : Blo 287828 367345 := bbase (se 2 (by rfl) ⟨137754, by rfl⟩ : syracuseStep 367345 = 275509) (by norm_num)
theorem B432893 : Blo 287828 432893 := bbase (se 3 (by rfl) ⟨81167, by rfl⟩ : syracuseStep 432893 = 162335) (by norm_num)
theorem B432917 : Blo 287828 432917 := bbase (se 6 (by rfl) ⟨10146, by rfl⟩ : syracuseStep 432917 = 20293) (by norm_num)
theorem B432941 : Blo 287828 432941 := bbase (se 3 (by rfl) ⟨81176, by rfl⟩ : syracuseStep 432941 = 162353) (by norm_num)
theorem B432965 : Blo 287828 432965 := bbase (se 4 (by rfl) ⟨40590, by rfl⟩ : syracuseStep 432965 = 81181) (by norm_num)
theorem B432989 : Blo 287828 432989 := bbase (se 3 (by rfl) ⟨81185, by rfl⟩ : syracuseStep 432989 = 162371) (by norm_num)
theorem B433013 : Blo 287828 433013 := bbase (se 5 (by rfl) ⟨20297, by rfl⟩ : syracuseStep 433013 = 40595) (by norm_num)
theorem B1121141 : Blo 287828 1121141 := bbase (se 5 (by rfl) ⟨52553, by rfl⟩ : syracuseStep 1121141 = 105107) (by norm_num)
theorem B433037 : Blo 287828 433037 := bbase (se 3 (by rfl) ⟨81194, by rfl⟩ : syracuseStep 433037 = 162389) (by norm_num)
theorem B367517 : Blo 287828 367517 := bbase (se 3 (by rfl) ⟨68909, by rfl⟩ : syracuseStep 367517 = 137819) (by norm_num)
theorem B433061 : Blo 287828 433061 := bbase (se 4 (by rfl) ⟨40599, by rfl⟩ : syracuseStep 433061 = 81199) (by norm_num)
theorem B433085 : Blo 287828 433085 := bbase (se 3 (by rfl) ⟨81203, by rfl⟩ : syracuseStep 433085 = 162407) (by norm_num)
theorem B433109 : Blo 287828 433109 := bbase (se 7 (by rfl) ⟨5075, by rfl⟩ : syracuseStep 433109 = 10151) (by norm_num)
theorem B367573 : Blo 287828 367573 := bbase (se 7 (by rfl) ⟨4307, by rfl⟩ : syracuseStep 367573 = 8615) (by norm_num)
theorem B498653 : Blo 287828 498653 := bbase (se 3 (by rfl) ⟨93497, by rfl⟩ : syracuseStep 498653 = 186995) (by norm_num)
theorem B433133 : Blo 287828 433133 := bbase (se 3 (by rfl) ⟨81212, by rfl⟩ : syracuseStep 433133 = 162425) (by norm_num)
theorem B629741 : Blo 287828 629741 := bbase (se 3 (by rfl) ⟨118076, by rfl⟩ : syracuseStep 629741 = 236153) (by norm_num)
theorem B433157 : Blo 287828 433157 := bbase (se 4 (by rfl) ⟨40608, by rfl⟩ : syracuseStep 433157 = 81217) (by norm_num)
theorem B433181 : Blo 287828 433181 := bbase (se 3 (by rfl) ⟨81221, by rfl⟩ : syracuseStep 433181 = 162443) (by norm_num)
theorem B662573 : Blo 287828 662573 := bbase (se 3 (by rfl) ⟨124232, by rfl⟩ : syracuseStep 662573 = 248465) (by norm_num)
theorem B433205 : Blo 287828 433205 := bbase (se 5 (by rfl) ⟨20306, by rfl⟩ : syracuseStep 433205 = 40613) (by norm_num)
theorem B367669 : Blo 287828 367669 := bbase (se 5 (by rfl) ⟨17234, by rfl⟩ : syracuseStep 367669 = 34469) (by norm_num)
theorem B433229 : Blo 287828 433229 := bbase (se 3 (by rfl) ⟨81230, by rfl⟩ : syracuseStep 433229 = 162461) (by norm_num)
theorem B433253 : Blo 287828 433253 := bbase (se 4 (by rfl) ⟨40617, by rfl⟩ : syracuseStep 433253 = 81235) (by norm_num)
theorem B433277 : Blo 287828 433277 := bbase (se 3 (by rfl) ⟨81239, by rfl⟩ : syracuseStep 433277 = 162479) (by norm_num)
theorem B924821 : Blo 287828 924821 := bbase (se 6 (by rfl) ⟨21675, by rfl⟩ : syracuseStep 924821 = 43351) (by norm_num)
theorem B433301 : Blo 287828 433301 := bbase (se 6 (by rfl) ⟨10155, by rfl⟩ : syracuseStep 433301 = 20311) (by norm_num)
theorem B1645717 : Blo 287828 1645717 := bbase (se 6 (by rfl) ⟨38571, by rfl⟩ : syracuseStep 1645717 = 77143) (by norm_num)
theorem B695461 : Blo 287828 695461 := bbase (se 4 (by rfl) ⟨65199, by rfl⟩ : syracuseStep 695461 = 130399) (by norm_num)
theorem B433325 : Blo 287828 433325 := bbase (se 3 (by rfl) ⟨81248, by rfl⟩ : syracuseStep 433325 = 162497) (by norm_num)
theorem B433349 : Blo 287828 433349 := bbase (se 4 (by rfl) ⟨40626, by rfl⟩ : syracuseStep 433349 = 81253) (by norm_num)
theorem B3316949 : Blo 287828 3316949 := bbase (se 7 (by rfl) ⟨38870, by rfl⟩ : syracuseStep 3316949 = 77741) (by norm_num)
theorem B433373 : Blo 287828 433373 := bbase (se 3 (by rfl) ⟨81257, by rfl⟩ : syracuseStep 433373 = 162515) (by norm_num)
theorem B367841 : Blo 287828 367841 := bbase (se 2 (by rfl) ⟨137940, by rfl⟩ : syracuseStep 367841 = 275881) (by norm_num)
theorem B433397 : Blo 287828 433397 := bbase (se 5 (by rfl) ⟨20315, by rfl⟩ : syracuseStep 433397 = 40631) (by norm_num)
theorem B466165 : Blo 287828 466165 := bbase (se 5 (by rfl) ⟨21851, by rfl⟩ : syracuseStep 466165 = 43703) (by norm_num)
theorem B695557 : Blo 287828 695557 := bbase (se 4 (by rfl) ⟨65208, by rfl⟩ : syracuseStep 695557 = 130417) (by norm_num)
theorem B433421 : Blo 287828 433421 := bbase (se 3 (by rfl) ⟨81266, by rfl⟩ : syracuseStep 433421 = 162533) (by norm_num)
theorem B367897 : Blo 287828 367897 := bbase (se 2 (by rfl) ⟨137961, by rfl⟩ : syracuseStep 367897 = 275923) (by norm_num)
theorem B433445 : Blo 287828 433445 := bbase (se 4 (by rfl) ⟨40635, by rfl⟩ : syracuseStep 433445 = 81271) (by norm_num)
theorem B433469 : Blo 287828 433469 := bbase (se 3 (by rfl) ⟨81275, by rfl⟩ : syracuseStep 433469 = 162551) (by norm_num)
theorem B433493 : Blo 287828 433493 := bbase (se 11 (by rfl) ⟨317, by rfl⟩ : syracuseStep 433493 = 635) (by norm_num)
theorem B433517 : Blo 287828 433517 := bbase (se 3 (by rfl) ⟨81284, by rfl⟩ : syracuseStep 433517 = 162569) (by norm_num)
theorem B367993 : Blo 287828 367993 := bbase (se 2 (by rfl) ⟨137997, by rfl⟩ : syracuseStep 367993 = 275995) (by norm_num)
theorem B433541 : Blo 287828 433541 := bbase (se 4 (by rfl) ⟨40644, by rfl⟩ : syracuseStep 433541 = 81289) (by norm_num)
theorem B433565 : Blo 287828 433565 := bbase (se 3 (by rfl) ⟨81293, by rfl⟩ : syracuseStep 433565 = 162587) (by norm_num)
theorem B433589 : Blo 287828 433589 := bbase (se 5 (by rfl) ⟨20324, by rfl⟩ : syracuseStep 433589 = 40649) (by norm_num)
theorem B695749 : Blo 287828 695749 := bbase (se 4 (by rfl) ⟨65226, by rfl⟩ : syracuseStep 695749 = 130453) (by norm_num)
theorem B433613 : Blo 287828 433613 := bbase (se 3 (by rfl) ⟨81302, by rfl⟩ : syracuseStep 433613 = 162605) (by norm_num)
theorem B433637 : Blo 287828 433637 := bbase (se 4 (by rfl) ⟨40653, by rfl⟩ : syracuseStep 433637 = 81307) (by norm_num)
theorem B433661 : Blo 287828 433661 := bbase (se 3 (by rfl) ⟨81311, by rfl⟩ : syracuseStep 433661 = 162623) (by norm_num)
theorem B433685 : Blo 287828 433685 := bbase (se 6 (by rfl) ⟨10164, by rfl⟩ : syracuseStep 433685 = 20329) (by norm_num)
theorem B368165 : Blo 287828 368165 := bbase (se 4 (by rfl) ⟨34515, by rfl⟩ : syracuseStep 368165 = 69031) (by norm_num)
theorem B433709 : Blo 287828 433709 := bbase (se 3 (by rfl) ⟨81320, by rfl⟩ : syracuseStep 433709 = 162641) (by norm_num)
theorem B433733 : Blo 287828 433733 := bbase (se 4 (by rfl) ⟨40662, by rfl⟩ : syracuseStep 433733 = 81325) (by norm_num)
theorem B826949 : Blo 287828 826949 := bbase (se 4 (by rfl) ⟨77526, by rfl⟩ : syracuseStep 826949 = 155053) (by norm_num)
theorem B433757 : Blo 287828 433757 := bbase (se 3 (by rfl) ⟨81329, by rfl⟩ : syracuseStep 433757 = 162659) (by norm_num)
theorem B368221 : Blo 287828 368221 := bbase (se 3 (by rfl) ⟨69041, by rfl⟩ : syracuseStep 368221 = 138083) (by norm_num)
theorem B433781 : Blo 287828 433781 := bbase (se 5 (by rfl) ⟨20333, by rfl⟩ : syracuseStep 433781 = 40667) (by norm_num)
theorem B433805 : Blo 287828 433805 := bbase (se 3 (by rfl) ⟨81338, by rfl⟩ : syracuseStep 433805 = 162677) (by norm_num)
theorem B433829 : Blo 287828 433829 := bbase (se 4 (by rfl) ⟨40671, by rfl⟩ : syracuseStep 433829 = 81343) (by norm_num)
theorem B433853 : Blo 287828 433853 := bbase (se 3 (by rfl) ⟨81347, by rfl⟩ : syracuseStep 433853 = 162695) (by norm_num)
theorem B368317 : Blo 287828 368317 := bbase (se 3 (by rfl) ⟨69059, by rfl⟩ : syracuseStep 368317 = 138119) (by norm_num)
theorem B5545685 : Blo 287828 5545685 := bbase (se 7 (by rfl) ⟨64988, by rfl⟩ : syracuseStep 5545685 = 129977) (by norm_num)
theorem B433877 : Blo 287828 433877 := bbase (se 7 (by rfl) ⟨5084, by rfl⟩ : syracuseStep 433877 = 10169) (by norm_num)
theorem B2989781 : Blo 287828 2989781 := bbase (se 7 (by rfl) ⟨35036, by rfl⟩ : syracuseStep 2989781 = 70073) (by norm_num)
theorem B728797 : Blo 287828 728797 := bbase (se 3 (by rfl) ⟨136649, by rfl⟩ : syracuseStep 728797 = 273299) (by norm_num)
theorem B433901 : Blo 287828 433901 := bbase (se 3 (by rfl) ⟨81356, by rfl⟩ : syracuseStep 433901 = 162713) (by norm_num)
theorem B433925 : Blo 287828 433925 := bbase (se 4 (by rfl) ⟨40680, by rfl⟩ : syracuseStep 433925 = 81361) (by norm_num)
theorem B696077 : Blo 287828 696077 := bbase (se 3 (by rfl) ⟨130514, by rfl⟩ : syracuseStep 696077 = 261029) (by norm_num)
theorem B433949 : Blo 287828 433949 := bbase (se 3 (by rfl) ⟨81365, by rfl⟩ : syracuseStep 433949 = 162731) (by norm_num)
theorem B433973 : Blo 287828 433973 := bbase (se 5 (by rfl) ⟨20342, by rfl⟩ : syracuseStep 433973 = 40685) (by norm_num)
theorem B728909 : Blo 287828 728909 := bbase (se 3 (by rfl) ⟨136670, by rfl⟩ : syracuseStep 728909 = 273341) (by norm_num)
theorem B433997 : Blo 287828 433997 := bbase (se 3 (by rfl) ⟨81374, by rfl⟩ : syracuseStep 433997 = 162749) (by norm_num)
theorem B434021 : Blo 287828 434021 := bbase (se 4 (by rfl) ⟨40689, by rfl⟩ : syracuseStep 434021 = 81379) (by norm_num)
theorem B368489 : Blo 287828 368489 := bbase (se 2 (by rfl) ⟨138183, by rfl⟩ : syracuseStep 368489 = 276367) (by norm_num)
theorem B434045 : Blo 287828 434045 := bbase (se 3 (by rfl) ⟨81383, by rfl⟩ : syracuseStep 434045 = 162767) (by norm_num)
theorem B434069 : Blo 287828 434069 := bbase (se 6 (by rfl) ⟨10173, by rfl⟩ : syracuseStep 434069 = 20347) (by norm_num)
theorem B368545 : Blo 287828 368545 := bbase (se 2 (by rfl) ⟨138204, by rfl⟩ : syracuseStep 368545 = 276409) (by norm_num)
theorem B434093 : Blo 287828 434093 := bbase (se 3 (by rfl) ⟨81392, by rfl⟩ : syracuseStep 434093 = 162785) (by norm_num)
theorem B434117 : Blo 287828 434117 := bbase (se 4 (by rfl) ⟨40698, by rfl⟩ : syracuseStep 434117 = 81397) (by norm_num)
theorem B434141 : Blo 287828 434141 := bbase (se 3 (by rfl) ⟨81401, by rfl⟩ : syracuseStep 434141 = 162803) (by norm_num)
theorem B434165 : Blo 287828 434165 := bbase (se 5 (by rfl) ⟨20351, by rfl⟩ : syracuseStep 434165 = 40703) (by norm_num)
theorem B368641 : Blo 287828 368641 := bbase (se 2 (by rfl) ⟨138240, by rfl⟩ : syracuseStep 368641 = 276481) (by norm_num)
theorem B729101 : Blo 287828 729101 := bbase (se 3 (by rfl) ⟨136706, by rfl⟩ : syracuseStep 729101 = 273413) (by norm_num)
theorem B434189 : Blo 287828 434189 := bbase (se 3 (by rfl) ⟨81410, by rfl⟩ : syracuseStep 434189 = 162821) (by norm_num)
theorem B434213 : Blo 287828 434213 := bbase (se 4 (by rfl) ⟨40707, by rfl⟩ : syracuseStep 434213 = 81415) (by norm_num)
theorem B1122341 : Blo 287828 1122341 := bbase (se 4 (by rfl) ⟨105219, by rfl⟩ : syracuseStep 1122341 = 210439) (by norm_num)
theorem B1450037 : Blo 287828 1450037 := bbase (se 5 (by rfl) ⟨67970, by rfl⟩ : syracuseStep 1450037 = 135941) (by norm_num)
theorem B434237 : Blo 287828 434237 := bbase (se 3 (by rfl) ⟨81419, by rfl⟩ : syracuseStep 434237 = 162839) (by norm_num)
theorem B434261 : Blo 287828 434261 := bbase (se 8 (by rfl) ⟨2544, by rfl⟩ : syracuseStep 434261 = 5089) (by norm_num)
theorem B434285 : Blo 287828 434285 := bbase (se 3 (by rfl) ⟨81428, by rfl⟩ : syracuseStep 434285 = 162857) (by norm_num)
theorem B434309 : Blo 287828 434309 := bbase (se 4 (by rfl) ⟨40716, by rfl⟩ : syracuseStep 434309 = 81433) (by norm_num)
theorem B5578901 : Blo 287828 5578901 := bbase (se 6 (by rfl) ⟨130755, by rfl⟩ : syracuseStep 5578901 = 261511) (by norm_num)
theorem B434333 : Blo 287828 434333 := bbase (se 3 (by rfl) ⟨81437, by rfl⟩ : syracuseStep 434333 = 162875) (by norm_num)
theorem B368813 : Blo 287828 368813 := bbase (se 3 (by rfl) ⟨69152, by rfl⟩ : syracuseStep 368813 = 138305) (by norm_num)
theorem B434357 : Blo 287828 434357 := bbase (se 5 (by rfl) ⟨20360, by rfl⟩ : syracuseStep 434357 = 40721) (by norm_num)
theorem B696509 : Blo 287828 696509 := bbase (se 3 (by rfl) ⟨130595, by rfl⟩ : syracuseStep 696509 = 261191) (by norm_num)
theorem B434381 : Blo 287828 434381 := bbase (se 3 (by rfl) ⟨81446, by rfl⟩ : syracuseStep 434381 = 162893) (by norm_num)
theorem B434405 : Blo 287828 434405 := bbase (se 4 (by rfl) ⟨40725, by rfl⟩ : syracuseStep 434405 = 81451) (by norm_num)
theorem B827621 : Blo 287828 827621 := bbase (se 4 (by rfl) ⟨77589, by rfl⟩ : syracuseStep 827621 = 155179) (by norm_num)
theorem B368869 : Blo 287828 368869 := bbase (se 4 (by rfl) ⟨34581, by rfl⟩ : syracuseStep 368869 = 69163) (by norm_num)
theorem B434429 : Blo 287828 434429 := bbase (se 3 (by rfl) ⟨81455, by rfl⟩ : syracuseStep 434429 = 162911) (by norm_num)
theorem B434453 : Blo 287828 434453 := bbase (se 6 (by rfl) ⟨10182, by rfl⟩ : syracuseStep 434453 = 20365) (by norm_num)
theorem B434477 : Blo 287828 434477 := bbase (se 3 (by rfl) ⟨81464, by rfl⟩ : syracuseStep 434477 = 162929) (by norm_num)
theorem B434501 : Blo 287828 434501 := bbase (se 4 (by rfl) ⟨40734, by rfl⟩ : syracuseStep 434501 = 81469) (by norm_num)
theorem B368965 : Blo 287828 368965 := bbase (se 4 (by rfl) ⟨34590, by rfl⟩ : syracuseStep 368965 = 69181) (by norm_num)
theorem B434525 : Blo 287828 434525 := bbase (se 3 (by rfl) ⟨81473, by rfl⟩ : syracuseStep 434525 = 162947) (by norm_num)
theorem B729445 : Blo 287828 729445 := bbase (se 4 (by rfl) ⟨68385, by rfl⟩ : syracuseStep 729445 = 136771) (by norm_num)
theorem B434549 : Blo 287828 434549 := bbase (se 5 (by rfl) ⟨20369, by rfl⟩ : syracuseStep 434549 = 40739) (by norm_num)
theorem B434573 : Blo 287828 434573 := bbase (se 3 (by rfl) ⟨81482, by rfl⟩ : syracuseStep 434573 = 162965) (by norm_num)
theorem B434597 : Blo 287828 434597 := bbase (se 4 (by rfl) ⟨40743, by rfl⟩ : syracuseStep 434597 = 81487) (by norm_num)
theorem B434621 : Blo 287828 434621 := bbase (se 3 (by rfl) ⟨81491, by rfl⟩ : syracuseStep 434621 = 162983) (by norm_num)
theorem B729557 : Blo 287828 729557 := bbase (se 7 (by rfl) ⟨8549, by rfl⟩ : syracuseStep 729557 = 17099) (by norm_num)
theorem B434645 : Blo 287828 434645 := bbase (se 7 (by rfl) ⟨5093, by rfl⟩ : syracuseStep 434645 = 10187) (by norm_num)
theorem B434669 : Blo 287828 434669 := bbase (se 3 (by rfl) ⟨81500, by rfl⟩ : syracuseStep 434669 = 163001) (by norm_num)
theorem B369137 : Blo 287828 369137 := bbase (se 2 (by rfl) ⟨138426, by rfl⟩ : syracuseStep 369137 = 276853) (by norm_num)
theorem B434693 : Blo 287828 434693 := bbase (se 4 (by rfl) ⟨40752, by rfl⟩ : syracuseStep 434693 = 81505) (by norm_num)
theorem B696845 : Blo 287828 696845 := bbase (se 3 (by rfl) ⟨130658, by rfl⟩ : syracuseStep 696845 = 261317) (by norm_num)
theorem B434717 : Blo 287828 434717 := bbase (se 3 (by rfl) ⟨81509, by rfl⟩ : syracuseStep 434717 = 163019) (by norm_num)
theorem B369193 : Blo 287828 369193 := bbase (se 2 (by rfl) ⟨138447, by rfl⟩ : syracuseStep 369193 = 276895) (by norm_num)
theorem B434741 : Blo 287828 434741 := bbase (se 5 (by rfl) ⟨20378, by rfl⟩ : syracuseStep 434741 = 40757) (by norm_num)
theorem B434765 : Blo 287828 434765 := bbase (se 3 (by rfl) ⟨81518, by rfl⟩ : syracuseStep 434765 = 163037) (by norm_num)
theorem B2466389 : Blo 287828 2466389 := bbase (se 8 (by rfl) ⟨14451, by rfl⟩ : syracuseStep 2466389 = 28903) (by norm_num)
theorem B434789 : Blo 287828 434789 := bbase (se 4 (by rfl) ⟨40761, by rfl⟩ : syracuseStep 434789 = 81523) (by norm_num)
theorem B631405 : Blo 287828 631405 := bbase (se 3 (by rfl) ⟨118388, by rfl⟩ : syracuseStep 631405 = 236777) (by norm_num)
theorem B434813 : Blo 287828 434813 := bbase (se 3 (by rfl) ⟨81527, by rfl⟩ : syracuseStep 434813 = 163055) (by norm_num)
theorem B369289 : Blo 287828 369289 := bbase (se 2 (by rfl) ⟨138483, by rfl⟩ : syracuseStep 369289 = 276967) (by norm_num)
theorem B729749 : Blo 287828 729749 := bbase (se 6 (by rfl) ⟨17103, by rfl⟩ : syracuseStep 729749 = 34207) (by norm_num)
theorem B434837 : Blo 287828 434837 := bbase (se 6 (by rfl) ⟨10191, by rfl⟩ : syracuseStep 434837 = 20383) (by norm_num)
theorem B828053 : Blo 287828 828053 := bbase (se 6 (by rfl) ⟨19407, by rfl⟩ : syracuseStep 828053 = 38815) (by norm_num)
theorem B434861 : Blo 287828 434861 := bbase (se 3 (by rfl) ⟨81536, by rfl⟩ : syracuseStep 434861 = 163073) (by norm_num)
theorem B434885 : Blo 287828 434885 := bbase (se 4 (by rfl) ⟨40770, by rfl⟩ : syracuseStep 434885 = 81541) (by norm_num)
theorem B434909 : Blo 287828 434909 := bbase (se 3 (by rfl) ⟨81545, by rfl⟩ : syracuseStep 434909 = 163091) (by norm_num)
theorem B434933 : Blo 287828 434933 := bbase (se 5 (by rfl) ⟨20387, by rfl⟩ : syracuseStep 434933 = 40775) (by norm_num)
theorem B434957 : Blo 287828 434957 := bbase (se 3 (by rfl) ⟨81554, by rfl⟩ : syracuseStep 434957 = 163109) (by norm_num)
theorem B434981 : Blo 287828 434981 := bbase (se 4 (by rfl) ⟨40779, by rfl⟩ : syracuseStep 434981 = 81559) (by norm_num)
theorem B435005 : Blo 287828 435005 := bbase (se 3 (by rfl) ⟨81563, by rfl⟩ : syracuseStep 435005 = 163127) (by norm_num)
theorem B435029 : Blo 287828 435029 := bbase (se 9 (by rfl) ⟨1274, by rfl⟩ : syracuseStep 435029 = 2549) (by norm_num)
theorem B435053 : Blo 287828 435053 := bbase (se 3 (by rfl) ⟨81572, by rfl⟩ : syracuseStep 435053 = 163145) (by norm_num)
theorem B435077 : Blo 287828 435077 := bbase (se 4 (by rfl) ⟨40788, by rfl⟩ : syracuseStep 435077 = 81577) (by norm_num)
theorem B435101 : Blo 287828 435101 := bbase (se 3 (by rfl) ⟨81581, by rfl⟩ : syracuseStep 435101 = 163163) (by norm_num)
theorem B435125 : Blo 287828 435125 := bbase (se 5 (by rfl) ⟨20396, by rfl⟩ : syracuseStep 435125 = 40793) (by norm_num)
theorem B435149 : Blo 287828 435149 := bbase (se 3 (by rfl) ⟨81590, by rfl⟩ : syracuseStep 435149 = 163181) (by norm_num)
theorem B435173 : Blo 287828 435173 := bbase (se 4 (by rfl) ⟨40797, by rfl⟩ : syracuseStep 435173 = 81595) (by norm_num)
theorem B730093 : Blo 287828 730093 := bbase (se 3 (by rfl) ⟨136892, by rfl⟩ : syracuseStep 730093 = 273785) (by norm_num)
theorem B435197 : Blo 287828 435197 := bbase (se 3 (by rfl) ⟨81599, by rfl⟩ : syracuseStep 435197 = 163199) (by norm_num)
theorem B435221 : Blo 287828 435221 := bbase (se 6 (by rfl) ⟨10200, by rfl⟩ : syracuseStep 435221 = 20401) (by norm_num)
theorem B435245 : Blo 287828 435245 := bbase (se 3 (by rfl) ⟨81608, by rfl⟩ : syracuseStep 435245 = 163217) (by norm_num)
theorem B435269 : Blo 287828 435269 := bbase (se 4 (by rfl) ⟨40806, by rfl⟩ : syracuseStep 435269 = 81613) (by norm_num)
theorem B1844309 : Blo 287828 1844309 := bbase (se 8 (by rfl) ⟨10806, by rfl⟩ : syracuseStep 1844309 = 21613) (by norm_num)
theorem B1647701 : Blo 287828 1647701 := bbase (se 8 (by rfl) ⟨9654, by rfl⟩ : syracuseStep 1647701 = 19309) (by norm_num)
theorem B730205 : Blo 287828 730205 := bbase (se 3 (by rfl) ⟨136913, by rfl⟩ : syracuseStep 730205 = 273827) (by norm_num)
theorem B435293 : Blo 287828 435293 := bbase (se 3 (by rfl) ⟨81617, by rfl⟩ : syracuseStep 435293 = 163235) (by norm_num)
theorem B435317 : Blo 287828 435317 := bbase (se 5 (by rfl) ⟨20405, by rfl⟩ : syracuseStep 435317 = 40811) (by norm_num)
theorem B435341 : Blo 287828 435341 := bbase (se 3 (by rfl) ⟨81626, by rfl⟩ : syracuseStep 435341 = 163253) (by norm_num)
theorem B435365 : Blo 287828 435365 := bbase (se 4 (by rfl) ⟨40815, by rfl⟩ : syracuseStep 435365 = 81631) (by norm_num)
theorem B435389 : Blo 287828 435389 := bbase (se 3 (by rfl) ⟨81635, by rfl⟩ : syracuseStep 435389 = 163271) (by norm_num)
theorem B795845 : Blo 287828 795845 := bbase (se 4 (by rfl) ⟨74610, by rfl⟩ : syracuseStep 795845 = 149221) (by norm_num)
theorem B435413 : Blo 287828 435413 := bbase (se 7 (by rfl) ⟨5102, by rfl⟩ : syracuseStep 435413 = 10205) (by norm_num)
theorem B664789 : Blo 287828 664789 := bbase (se 7 (by rfl) ⟨7790, by rfl⟩ : syracuseStep 664789 = 15581) (by norm_num)
theorem B435437 : Blo 287828 435437 := bbase (se 3 (by rfl) ⟨81644, by rfl⟩ : syracuseStep 435437 = 163289) (by norm_num)
theorem B435461 : Blo 287828 435461 := bbase (se 4 (by rfl) ⟨40824, by rfl⟩ : syracuseStep 435461 = 81649) (by norm_num)
theorem B369937 : Blo 287828 369937 := bbase (se 2 (by rfl) ⟨138726, by rfl⟩ : syracuseStep 369937 = 277453) (by norm_num)
theorem B730397 : Blo 287828 730397 := bbase (se 3 (by rfl) ⟨136949, by rfl⟩ : syracuseStep 730397 = 273899) (by norm_num)
theorem B435485 : Blo 287828 435485 := bbase (se 3 (by rfl) ⟨81653, by rfl⟩ : syracuseStep 435485 = 163307) (by norm_num)
theorem B435509 : Blo 287828 435509 := bbase (se 5 (by rfl) ⟨20414, by rfl⟩ : syracuseStep 435509 = 40829) (by norm_num)
theorem B2204981 : Blo 287828 2204981 := bbase (se 5 (by rfl) ⟨103358, by rfl⟩ : syracuseStep 2204981 = 206717) (by norm_num)
theorem B435533 : Blo 287828 435533 := bbase (se 3 (by rfl) ⟨81662, by rfl⟩ : syracuseStep 435533 = 163325) (by norm_num)
theorem B435557 : Blo 287828 435557 := bbase (se 4 (by rfl) ⟨40833, by rfl⟩ : syracuseStep 435557 = 81667) (by norm_num)
theorem B435581 : Blo 287828 435581 := bbase (se 3 (by rfl) ⟨81671, by rfl⟩ : syracuseStep 435581 = 163343) (by norm_num)
theorem B828805 : Blo 287828 828805 := bbase (se 4 (by rfl) ⟨77700, by rfl⟩ : syracuseStep 828805 = 155401) (by norm_num)
theorem B435605 : Blo 287828 435605 := bbase (se 6 (by rfl) ⟨10209, by rfl⟩ : syracuseStep 435605 = 20419) (by norm_num)
theorem B435629 : Blo 287828 435629 := bbase (se 3 (by rfl) ⟨81680, by rfl⟩ : syracuseStep 435629 = 163361) (by norm_num)
theorem B435653 : Blo 287828 435653 := bbase (se 4 (by rfl) ⟨40842, by rfl⟩ : syracuseStep 435653 = 81685) (by norm_num)
theorem B435677 : Blo 287828 435677 := bbase (se 3 (by rfl) ⟨81689, by rfl⟩ : syracuseStep 435677 = 163379) (by norm_num)
theorem B435701 : Blo 287828 435701 := bbase (se 5 (by rfl) ⟨20423, by rfl⟩ : syracuseStep 435701 = 40847) (by norm_num)
theorem B435725 : Blo 287828 435725 := bbase (se 3 (by rfl) ⟨81698, by rfl⟩ : syracuseStep 435725 = 163397) (by norm_num)
theorem B435749 : Blo 287828 435749 := bbase (se 4 (by rfl) ⟨40851, by rfl⟩ : syracuseStep 435749 = 81703) (by norm_num)
theorem B697901 : Blo 287828 697901 := bbase (se 3 (by rfl) ⟨130856, by rfl⟩ : syracuseStep 697901 = 261713) (by norm_num)
theorem B435773 : Blo 287828 435773 := bbase (se 3 (by rfl) ⟨81707, by rfl⟩ : syracuseStep 435773 = 163415) (by norm_num)
theorem B435797 : Blo 287828 435797 := bbase (se 8 (by rfl) ⟨2553, by rfl⟩ : syracuseStep 435797 = 5107) (by norm_num)
theorem B435821 : Blo 287828 435821 := bbase (se 3 (by rfl) ⟨81716, by rfl⟩ : syracuseStep 435821 = 163433) (by norm_num)
theorem B730741 : Blo 287828 730741 := bbase (se 5 (by rfl) ⟨34253, by rfl⟩ : syracuseStep 730741 = 68507) (by norm_num)
theorem B1320581 : Blo 287828 1320581 := bbase (se 4 (by rfl) ⟨123804, by rfl⟩ : syracuseStep 1320581 = 247609) (by norm_num)
theorem B435845 : Blo 287828 435845 := bbase (se 4 (by rfl) ⟨40860, by rfl⟩ : syracuseStep 435845 = 81721) (by norm_num)
theorem B435869 : Blo 287828 435869 := bbase (se 3 (by rfl) ⟨81725, by rfl⟩ : syracuseStep 435869 = 163451) (by norm_num)
theorem B435893 : Blo 287828 435893 := bbase (se 5 (by rfl) ⟨20432, by rfl⟩ : syracuseStep 435893 = 40865) (by norm_num)
theorem B435917 : Blo 287828 435917 := bbase (se 3 (by rfl) ⟨81734, by rfl⟩ : syracuseStep 435917 = 163469) (by norm_num)
theorem B730853 : Blo 287828 730853 := bbase (se 4 (by rfl) ⟨68517, by rfl⟩ : syracuseStep 730853 = 137035) (by norm_num)
theorem B435941 : Blo 287828 435941 := bbase (se 4 (by rfl) ⟨40869, by rfl⟩ : syracuseStep 435941 = 81739) (by norm_num)
theorem B435965 : Blo 287828 435965 := bbase (se 3 (by rfl) ⟨81743, by rfl⟩ : syracuseStep 435965 = 163487) (by norm_num)
theorem B435989 : Blo 287828 435989 := bbase (se 6 (by rfl) ⟨10218, by rfl⟩ : syracuseStep 435989 = 20437) (by norm_num)
theorem B436013 : Blo 287828 436013 := bbase (se 3 (by rfl) ⟨81752, by rfl⟩ : syracuseStep 436013 = 163505) (by norm_num)
theorem B436037 : Blo 287828 436037 := bbase (se 4 (by rfl) ⟨40878, by rfl⟩ : syracuseStep 436037 = 81757) (by norm_num)
theorem B436061 : Blo 287828 436061 := bbase (se 3 (by rfl) ⟨81761, by rfl⟩ : syracuseStep 436061 = 163523) (by norm_num)
theorem B436085 : Blo 287828 436085 := bbase (se 5 (by rfl) ⟨20441, by rfl⟩ : syracuseStep 436085 = 40883) (by norm_num)
theorem B436109 : Blo 287828 436109 := bbase (se 3 (by rfl) ⟨81770, by rfl⟩ : syracuseStep 436109 = 163541) (by norm_num)
theorem B731045 : Blo 287828 731045 := bbase (se 4 (by rfl) ⟨68535, by rfl⟩ : syracuseStep 731045 = 137071) (by norm_num)
theorem B436133 : Blo 287828 436133 := bbase (se 4 (by rfl) ⟨40887, by rfl⟩ : syracuseStep 436133 = 81775) (by norm_num)
theorem B436157 : Blo 287828 436157 := bbase (se 3 (by rfl) ⟨81779, by rfl⟩ : syracuseStep 436157 = 163559) (by norm_num)
theorem B436181 : Blo 287828 436181 := bbase (se 7 (by rfl) ⟨5111, by rfl⟩ : syracuseStep 436181 = 10223) (by norm_num)
theorem B436205 : Blo 287828 436205 := bbase (se 3 (by rfl) ⟨81788, by rfl⟩ : syracuseStep 436205 = 163577) (by norm_num)
theorem B436229 : Blo 287828 436229 := bbase (se 4 (by rfl) ⟨40896, by rfl⟩ : syracuseStep 436229 = 81793) (by norm_num)
theorem B436253 : Blo 287828 436253 := bbase (se 3 (by rfl) ⟨81797, by rfl⟩ : syracuseStep 436253 = 163595) (by norm_num)
theorem B436277 : Blo 287828 436277 := bbase (se 5 (by rfl) ⟨20450, by rfl⟩ : syracuseStep 436277 = 40901) (by norm_num)
theorem B436301 : Blo 287828 436301 := bbase (se 3 (by rfl) ⟨81806, by rfl⟩ : syracuseStep 436301 = 163613) (by norm_num)
theorem B436325 : Blo 287828 436325 := bbase (se 4 (by rfl) ⟨40905, by rfl⟩ : syracuseStep 436325 = 81811) (by norm_num)
theorem B436349 : Blo 287828 436349 := bbase (se 3 (by rfl) ⟨81815, by rfl⟩ : syracuseStep 436349 = 163631) (by norm_num)
theorem B436373 : Blo 287828 436373 := bbase (se 6 (by rfl) ⟨10227, by rfl⟩ : syracuseStep 436373 = 20455) (by norm_num)
theorem B436397 : Blo 287828 436397 := bbase (se 3 (by rfl) ⟨81824, by rfl⟩ : syracuseStep 436397 = 163649) (by norm_num)
theorem B436421 : Blo 287828 436421 := bbase (se 4 (by rfl) ⟨40914, by rfl⟩ : syracuseStep 436421 = 81829) (by norm_num)
theorem B436445 : Blo 287828 436445 := bbase (se 3 (by rfl) ⟨81833, by rfl⟩ : syracuseStep 436445 = 163667) (by norm_num)
theorem B436469 : Blo 287828 436469 := bbase (se 5 (by rfl) ⟨20459, by rfl⟩ : syracuseStep 436469 = 40919) (by norm_num)
theorem B731389 : Blo 287828 731389 := bbase (se 3 (by rfl) ⟨137135, by rfl⟩ : syracuseStep 731389 = 274271) (by norm_num)
theorem B436493 : Blo 287828 436493 := bbase (se 3 (by rfl) ⟨81842, by rfl⟩ : syracuseStep 436493 = 163685) (by norm_num)
theorem B436517 : Blo 287828 436517 := bbase (se 4 (by rfl) ⟨40923, by rfl⟩ : syracuseStep 436517 = 81847) (by norm_num)
theorem B436541 : Blo 287828 436541 := bbase (se 3 (by rfl) ⟨81851, by rfl⟩ : syracuseStep 436541 = 163703) (by norm_num)
theorem B9382229 : Blo 287828 9382229 := bbase (se 10 (by rfl) ⟨13743, by rfl⟩ : syracuseStep 9382229 = 27487) (by norm_num)
theorem B436565 : Blo 287828 436565 := bbase (se 10 (by rfl) ⟨639, by rfl⟩ : syracuseStep 436565 = 1279) (by norm_num)
theorem B731501 : Blo 287828 731501 := bbase (se 3 (by rfl) ⟨137156, by rfl⟩ : syracuseStep 731501 = 274313) (by norm_num)
theorem B436589 : Blo 287828 436589 := bbase (se 3 (by rfl) ⟨81860, by rfl⟩ : syracuseStep 436589 = 163721) (by norm_num)
theorem B436613 : Blo 287828 436613 := bbase (se 4 (by rfl) ⟨40932, by rfl⟩ : syracuseStep 436613 = 81865) (by norm_num)
theorem B436637 : Blo 287828 436637 := bbase (se 3 (by rfl) ⟨81869, by rfl⟩ : syracuseStep 436637 = 163739) (by norm_num)
theorem B436661 : Blo 287828 436661 := bbase (se 5 (by rfl) ⟨20468, by rfl⟩ : syracuseStep 436661 = 40937) (by norm_num)
theorem B436685 : Blo 287828 436685 := bbase (se 3 (by rfl) ⟨81878, by rfl⟩ : syracuseStep 436685 = 163757) (by norm_num)
theorem B436709 : Blo 287828 436709 := bbase (se 4 (by rfl) ⟨40941, by rfl⟩ : syracuseStep 436709 = 81883) (by norm_num)
theorem B436733 : Blo 287828 436733 := bbase (se 3 (by rfl) ⟨81887, by rfl⟩ : syracuseStep 436733 = 163775) (by norm_num)
theorem B436757 : Blo 287828 436757 := bbase (se 6 (by rfl) ⟨10236, by rfl⟩ : syracuseStep 436757 = 20473) (by norm_num)
theorem B731693 : Blo 287828 731693 := bbase (se 3 (by rfl) ⟨137192, by rfl⟩ : syracuseStep 731693 = 274385) (by norm_num)
theorem B436781 : Blo 287828 436781 := bbase (se 3 (by rfl) ⟨81896, by rfl⟩ : syracuseStep 436781 = 163793) (by norm_num)
theorem B436805 : Blo 287828 436805 := bbase (se 4 (by rfl) ⟨40950, by rfl⟩ : syracuseStep 436805 = 81901) (by norm_num)
theorem B436829 : Blo 287828 436829 := bbase (se 3 (by rfl) ⟨81905, by rfl⟩ : syracuseStep 436829 = 163811) (by norm_num)
theorem B436853 : Blo 287828 436853 := bbase (se 5 (by rfl) ⟨20477, by rfl⟩ : syracuseStep 436853 = 40955) (by norm_num)
theorem B436877 : Blo 287828 436877 := bbase (se 3 (by rfl) ⟨81914, by rfl⟩ : syracuseStep 436877 = 163829) (by norm_num)
theorem B993941 : Blo 287828 993941 := bbase (se 6 (by rfl) ⟨23295, by rfl⟩ : syracuseStep 993941 = 46591) (by norm_num)
theorem B436901 : Blo 287828 436901 := bbase (se 4 (by rfl) ⟨40959, by rfl⟩ : syracuseStep 436901 = 81919) (by norm_num)
theorem B469693 : Blo 287828 469693 := bbase (se 3 (by rfl) ⟨88067, by rfl⟩ : syracuseStep 469693 = 176135) (by norm_num)
theorem B436925 : Blo 287828 436925 := bbase (se 3 (by rfl) ⟨81923, by rfl⟩ : syracuseStep 436925 = 163847) (by norm_num)
theorem B436949 : Blo 287828 436949 := bbase (se 7 (by rfl) ⟨5120, by rfl⟩ : syracuseStep 436949 = 10241) (by norm_num)
theorem B436973 : Blo 287828 436973 := bbase (se 3 (by rfl) ⟨81932, by rfl⟩ : syracuseStep 436973 = 163865) (by norm_num)
theorem B436997 : Blo 287828 436997 := bbase (se 4 (by rfl) ⟨40968, by rfl⟩ : syracuseStep 436997 = 81937) (by norm_num)
theorem B437021 : Blo 287828 437021 := bbase (se 3 (by rfl) ⟨81941, by rfl⟩ : syracuseStep 437021 = 163883) (by norm_num)
theorem B437045 : Blo 287828 437045 := bbase (se 5 (by rfl) ⟨20486, by rfl⟩ : syracuseStep 437045 = 40973) (by norm_num)
theorem B994117 : Blo 287828 994117 := bbase (se 4 (by rfl) ⟨93198, by rfl⟩ : syracuseStep 994117 = 186397) (by norm_num)
theorem B437069 : Blo 287828 437069 := bbase (se 3 (by rfl) ⟨81950, by rfl⟩ : syracuseStep 437069 = 163901) (by norm_num)
theorem B437093 : Blo 287828 437093 := bbase (se 4 (by rfl) ⟨40977, by rfl⟩ : syracuseStep 437093 = 81955) (by norm_num)
theorem B437117 : Blo 287828 437117 := bbase (se 3 (by rfl) ⟨81959, by rfl⟩ : syracuseStep 437117 = 163919) (by norm_num)
theorem B732037 : Blo 287828 732037 := bbase (se 4 (by rfl) ⟨68628, by rfl⟩ : syracuseStep 732037 = 137257) (by norm_num)
theorem B437141 : Blo 287828 437141 := bbase (se 6 (by rfl) ⟨10245, by rfl⟩ : syracuseStep 437141 = 20491) (by norm_num)
theorem B437165 : Blo 287828 437165 := bbase (se 3 (by rfl) ⟨81968, by rfl⟩ : syracuseStep 437165 = 163937) (by norm_num)
theorem B437189 : Blo 287828 437189 := bbase (se 4 (by rfl) ⟨40986, by rfl⟩ : syracuseStep 437189 = 81973) (by norm_num)
theorem B437213 : Blo 287828 437213 := bbase (se 3 (by rfl) ⟨81977, by rfl⟩ : syracuseStep 437213 = 163955) (by norm_num)
theorem B928741 : Blo 287828 928741 := bbase (se 4 (by rfl) ⟨87069, by rfl⟩ : syracuseStep 928741 = 174139) (by norm_num)
theorem B732149 : Blo 287828 732149 := bbase (se 5 (by rfl) ⟨34319, by rfl⟩ : syracuseStep 732149 = 68639) (by norm_num)
theorem B437237 : Blo 287828 437237 := bbase (se 5 (by rfl) ⟨20495, by rfl⟩ : syracuseStep 437237 = 40991) (by norm_num)
theorem B437261 : Blo 287828 437261 := bbase (se 3 (by rfl) ⟨81986, by rfl⟩ : syracuseStep 437261 = 163973) (by norm_num)
theorem B437285 : Blo 287828 437285 := bbase (se 4 (by rfl) ⟨40995, by rfl⟩ : syracuseStep 437285 = 81991) (by norm_num)
theorem B437309 : Blo 287828 437309 := bbase (se 3 (by rfl) ⟨81995, by rfl⟩ : syracuseStep 437309 = 163991) (by norm_num)
theorem B437333 : Blo 287828 437333 := bbase (se 8 (by rfl) ⟨2562, by rfl⟩ : syracuseStep 437333 = 5125) (by norm_num)
theorem B502877 : Blo 287828 502877 := bbase (se 3 (by rfl) ⟨94289, by rfl⟩ : syracuseStep 502877 = 188579) (by norm_num)
theorem B437357 : Blo 287828 437357 := bbase (se 3 (by rfl) ⟨82004, by rfl⟩ : syracuseStep 437357 = 164009) (by norm_num)
theorem B1387637 : Blo 287828 1387637 := bbase (se 5 (by rfl) ⟨65045, by rfl⟩ : syracuseStep 1387637 = 130091) (by norm_num)
theorem B437381 : Blo 287828 437381 := bbase (se 4 (by rfl) ⟨41004, by rfl⟩ : syracuseStep 437381 = 82009) (by norm_num)
theorem B437405 : Blo 287828 437405 := bbase (se 3 (by rfl) ⟨82013, by rfl⟩ : syracuseStep 437405 = 164027) (by norm_num)
theorem B732341 : Blo 287828 732341 := bbase (se 5 (by rfl) ⟨34328, by rfl⟩ : syracuseStep 732341 = 68657) (by norm_num)
theorem B437429 : Blo 287828 437429 := bbase (se 5 (by rfl) ⟨20504, by rfl⟩ : syracuseStep 437429 = 41009) (by norm_num)
theorem B437453 : Blo 287828 437453 := bbase (se 3 (by rfl) ⟨82022, by rfl⟩ : syracuseStep 437453 = 164045) (by norm_num)
theorem B928997 : Blo 287828 928997 := bbase (se 4 (by rfl) ⟨87093, by rfl⟩ : syracuseStep 928997 = 174187) (by norm_num)
theorem B437477 : Blo 287828 437477 := bbase (se 4 (by rfl) ⟨41013, by rfl⟩ : syracuseStep 437477 = 82027) (by norm_num)
theorem B1649909 : Blo 287828 1649909 := bbase (se 5 (by rfl) ⟨77339, by rfl⟩ : syracuseStep 1649909 = 154679) (by norm_num)
theorem B437501 : Blo 287828 437501 := bbase (se 3 (by rfl) ⟨82031, by rfl⟩ : syracuseStep 437501 = 164063) (by norm_num)
theorem B437525 : Blo 287828 437525 := bbase (se 6 (by rfl) ⟨10254, by rfl⟩ : syracuseStep 437525 = 20509) (by norm_num)
theorem B437549 : Blo 287828 437549 := bbase (se 3 (by rfl) ⟨82040, by rfl⟩ : syracuseStep 437549 = 164081) (by norm_num)
theorem B437573 : Blo 287828 437573 := bbase (se 4 (by rfl) ⟨41022, by rfl⟩ : syracuseStep 437573 = 82045) (by norm_num)
theorem B437597 : Blo 287828 437597 := bbase (se 3 (by rfl) ⟨82049, by rfl⟩ : syracuseStep 437597 = 164099) (by norm_num)
theorem B437621 : Blo 287828 437621 := bbase (se 5 (by rfl) ⟨20513, by rfl⟩ : syracuseStep 437621 = 41027) (by norm_num)
theorem B372097 : Blo 287828 372097 := bbase (se 2 (by rfl) ⟨139536, by rfl⟩ : syracuseStep 372097 = 279073) (by norm_num)
theorem B437645 : Blo 287828 437645 := bbase (se 3 (by rfl) ⟨82058, by rfl⟩ : syracuseStep 437645 = 164117) (by norm_num)
theorem B437669 : Blo 287828 437669 := bbase (se 4 (by rfl) ⟨41031, by rfl⟩ : syracuseStep 437669 = 82063) (by norm_num)
theorem B437693 : Blo 287828 437693 := bbase (se 3 (by rfl) ⟨82067, by rfl⟩ : syracuseStep 437693 = 164135) (by norm_num)
theorem B437717 : Blo 287828 437717 := bbase (se 7 (by rfl) ⟨5129, by rfl⟩ : syracuseStep 437717 = 10259) (by norm_num)
theorem B437741 : Blo 287828 437741 := bbase (se 3 (by rfl) ⟨82076, by rfl⟩ : syracuseStep 437741 = 164153) (by norm_num)
theorem B2469365 : Blo 287828 2469365 := bbase (se 5 (by rfl) ⟨115751, by rfl⟩ : syracuseStep 2469365 = 231503) (by norm_num)
theorem B732685 : Blo 287828 732685 := bbase (se 3 (by rfl) ⟨137378, by rfl⟩ : syracuseStep 732685 = 274757) (by norm_num)
theorem B732797 : Blo 287828 732797 := bbase (se 3 (by rfl) ⟨137399, by rfl⟩ : syracuseStep 732797 = 274799) (by norm_num)
theorem B700093 : Blo 287828 700093 := bbase (se 3 (by rfl) ⟨131267, by rfl⟩ : syracuseStep 700093 = 262535) (by norm_num)
theorem B438005 : Blo 287828 438005 := bbase (se 5 (by rfl) ⟨20531, by rfl⟩ : syracuseStep 438005 = 41063) (by norm_num)
theorem B438053 : Blo 287828 438053 := bbase (se 4 (by rfl) ⟨41067, by rfl⟩ : syracuseStep 438053 = 82135) (by norm_num)
theorem B732989 : Blo 287828 732989 := bbase (se 3 (by rfl) ⟨137435, by rfl⟩ : syracuseStep 732989 = 274871) (by norm_num)
theorem B1093621 : Blo 287828 1093621 := bbase (se 5 (by rfl) ⟨51263, by rfl⟩ : syracuseStep 1093621 = 102527) (by norm_num)
theorem B339965 : Blo 287828 339965 := bbase (se 3 (by rfl) ⟨63743, by rfl⟩ : syracuseStep 339965 = 127487) (by norm_num)
theorem B733333 : Blo 287828 733333 := bbase (se 6 (by rfl) ⟨17187, by rfl⟩ : syracuseStep 733333 = 34375) (by norm_num)
theorem B733445 : Blo 287828 733445 := bbase (se 4 (by rfl) ⟨68760, by rfl⟩ : syracuseStep 733445 = 137521) (by norm_num)
theorem B1093925 : Blo 287828 1093925 := bbase (se 4 (by rfl) ⟨102555, by rfl⟩ : syracuseStep 1093925 = 205111) (by norm_num)
theorem B307513 : Blo 287828 307513 := bbase (se 2 (by rfl) ⟨115317, by rfl⟩ : syracuseStep 307513 = 230635) (by norm_num)
theorem B733637 : Blo 287828 733637 := bbase (se 4 (by rfl) ⟨68778, by rfl⟩ : syracuseStep 733637 = 137557) (by norm_num)
theorem B733981 : Blo 287828 733981 := bbase (se 3 (by rfl) ⟨137621, by rfl⟩ : syracuseStep 733981 = 275243) (by norm_num)
theorem B734093 : Blo 287828 734093 := bbase (se 3 (by rfl) ⟨137642, by rfl⟩ : syracuseStep 734093 = 275285) (by norm_num)
theorem B373781 : Blo 287828 373781 := bbase (se 6 (by rfl) ⟨8760, by rfl⟩ : syracuseStep 373781 = 17521) (by norm_num)
theorem B734285 : Blo 287828 734285 := bbase (se 3 (by rfl) ⟨137678, by rfl⟩ : syracuseStep 734285 = 275357) (by norm_num)
theorem B308333 : Blo 287828 308333 := bbase (se 3 (by rfl) ⟨57812, by rfl⟩ : syracuseStep 308333 = 115625) (by norm_num)
theorem B701581 : Blo 287828 701581 := bbase (se 3 (by rfl) ⟨131546, by rfl⟩ : syracuseStep 701581 = 263093) (by norm_num)
theorem B1881269 : Blo 287828 1881269 := bbase (se 5 (by rfl) ⟨88184, by rfl⟩ : syracuseStep 1881269 = 176369) (by norm_num)
theorem B734629 : Blo 287828 734629 := bbase (se 4 (by rfl) ⟨68871, by rfl⟩ : syracuseStep 734629 = 137743) (by norm_num)
theorem B734741 : Blo 287828 734741 := bbase (se 6 (by rfl) ⟨17220, by rfl⟩ : syracuseStep 734741 = 34441) (by norm_num)
theorem B308777 : Blo 287828 308777 := bbase (se 2 (by rfl) ⟨115791, by rfl⟩ : syracuseStep 308777 = 231583) (by norm_num)
theorem B996965 : Blo 287828 996965 := bbase (se 4 (by rfl) ⟨93465, by rfl⟩ : syracuseStep 996965 = 186931) (by norm_num)
theorem B734933 : Blo 287828 734933 := bbase (se 7 (by rfl) ⟨8612, by rfl⟩ : syracuseStep 734933 = 17225) (by norm_num)
theorem B3192533 : Blo 287828 3192533 := bbase (se 7 (by rfl) ⟨37412, by rfl⟩ : syracuseStep 3192533 = 74825) (by norm_num)
theorem B2635541 : Blo 287828 2635541 := bbase (se 6 (by rfl) ⟨61770, by rfl⟩ : syracuseStep 2635541 = 123541) (by norm_num)
theorem B3127061 : Blo 287828 3127061 := bbase (se 6 (by rfl) ⟨73290, by rfl⟩ : syracuseStep 3127061 = 146581) (by norm_num)
theorem B309025 : Blo 287828 309025 := bbase (se 2 (by rfl) ⟨115884, by rfl⟩ : syracuseStep 309025 = 231769) (by norm_num)
theorem B931765 : Blo 287828 931765 := bbase (se 5 (by rfl) ⟨43676, by rfl⟩ : syracuseStep 931765 = 87353) (by norm_num)
theorem B702437 : Blo 287828 702437 := bbase (se 4 (by rfl) ⟨65853, by rfl⟩ : syracuseStep 702437 = 131707) (by norm_num)
theorem B735277 : Blo 287828 735277 := bbase (se 3 (by rfl) ⟨137864, by rfl⟩ : syracuseStep 735277 = 275729) (by norm_num)
theorem B735389 : Blo 287828 735389 := bbase (se 3 (by rfl) ⟨137885, by rfl⟩ : syracuseStep 735389 = 275771) (by norm_num)
theorem B1816757 : Blo 287828 1816757 := bbase (se 5 (by rfl) ⟨85160, by rfl⟩ : syracuseStep 1816757 = 170321) (by norm_num)
theorem B309457 : Blo 287828 309457 := bbase (se 2 (by rfl) ⟨116046, by rfl⟩ : syracuseStep 309457 = 232093) (by norm_num)
theorem B309529 : Blo 287828 309529 := bbase (se 2 (by rfl) ⟨116073, by rfl⟩ : syracuseStep 309529 = 232147) (by norm_num)
theorem B735581 : Blo 287828 735581 := bbase (se 3 (by rfl) ⟨137921, by rfl⟩ : syracuseStep 735581 = 275843) (by norm_num)
theorem B1096037 : Blo 287828 1096037 := bbase (se 4 (by rfl) ⟨102753, by rfl⟩ : syracuseStep 1096037 = 205507) (by norm_num)
theorem B1096325 : Blo 287828 1096325 := bbase (se 4 (by rfl) ⟨102780, by rfl⟩ : syracuseStep 1096325 = 205561) (by norm_num)
theorem B309901 : Blo 287828 309901 := bbase (se 3 (by rfl) ⟨58106, by rfl⟩ : syracuseStep 309901 = 116213) (by norm_num)
theorem B735925 : Blo 287828 735925 := bbase (se 5 (by rfl) ⟨34496, by rfl⟩ : syracuseStep 735925 = 68993) (by norm_num)
theorem B736037 : Blo 287828 736037 := bbase (se 4 (by rfl) ⟨69003, by rfl⟩ : syracuseStep 736037 = 138007) (by norm_num)
theorem B736229 : Blo 287828 736229 := bbase (se 4 (by rfl) ⟨69021, by rfl⟩ : syracuseStep 736229 = 138043) (by norm_num)
theorem B310277 : Blo 287828 310277 := bbase (se 4 (by rfl) ⟨29088, by rfl⟩ : syracuseStep 310277 = 58177) (by norm_num)
theorem B1457189 : Blo 287828 1457189 := bbase (se 4 (by rfl) ⟨136611, by rfl⟩ : syracuseStep 1457189 = 273223) (by norm_num)
theorem B310349 : Blo 287828 310349 := bbase (se 3 (by rfl) ⟨58190, by rfl⟩ : syracuseStep 310349 = 116381) (by norm_num)
theorem B933125 : Blo 287828 933125 := bbase (se 4 (by rfl) ⟨87480, by rfl⟩ : syracuseStep 933125 = 174961) (by norm_num)
theorem B310537 : Blo 287828 310537 := bbase (se 2 (by rfl) ⟨116451, by rfl⟩ : syracuseStep 310537 = 232903) (by norm_num)
theorem B638237 : Blo 287828 638237 := bbase (se 3 (by rfl) ⟨119669, by rfl⟩ : syracuseStep 638237 = 239339) (by norm_num)
theorem B736573 : Blo 287828 736573 := bbase (se 3 (by rfl) ⟨138107, by rfl⟩ : syracuseStep 736573 = 276215) (by norm_num)
theorem B736685 : Blo 287828 736685 := bbase (se 3 (by rfl) ⟨138128, by rfl⟩ : syracuseStep 736685 = 276257) (by norm_num)
theorem B310721 : Blo 287828 310721 := bbase (se 2 (by rfl) ⟨116520, by rfl⟩ : syracuseStep 310721 = 233041) (by norm_num)
theorem B1261109 : Blo 287828 1261109 := bbase (se 5 (by rfl) ⟨59114, by rfl⟩ : syracuseStep 1261109 = 118229) (by norm_num)
theorem B736877 : Blo 287828 736877 := bbase (se 3 (by rfl) ⟨138164, by rfl⟩ : syracuseStep 736877 = 276329) (by norm_num)
theorem B1097509 : Blo 287828 1097509 := bbase (se 4 (by rfl) ⟨102891, by rfl⟩ : syracuseStep 1097509 = 205783) (by norm_num)
theorem B737221 : Blo 287828 737221 := bbase (se 4 (by rfl) ⟨69114, by rfl⟩ : syracuseStep 737221 = 138229) (by norm_num)
theorem B737333 : Blo 287828 737333 := bbase (se 5 (by rfl) ⟨34562, by rfl⟩ : syracuseStep 737333 = 69125) (by norm_num)
theorem B1392709 : Blo 287828 1392709 := bbase (se 4 (by rfl) ⟨130566, by rfl⟩ : syracuseStep 1392709 = 261133) (by norm_num)
theorem B1097813 : Blo 287828 1097813 := bbase (se 8 (by rfl) ⟨6432, by rfl⟩ : syracuseStep 1097813 = 12865) (by norm_num)
theorem B1491029 : Blo 287828 1491029 := bbase (se 8 (by rfl) ⟨8736, by rfl⟩ : syracuseStep 1491029 = 17473) (by norm_num)
theorem B442469 : Blo 287828 442469 := bbase (se 4 (by rfl) ⟨41481, by rfl⟩ : syracuseStep 442469 = 82963) (by norm_num)
theorem B409709 : Blo 287828 409709 := bbase (se 3 (by rfl) ⟨76820, by rfl⟩ : syracuseStep 409709 = 153641) (by norm_num)
theorem B442541 : Blo 287828 442541 := bbase (se 3 (by rfl) ⟨82976, by rfl⟩ : syracuseStep 442541 = 165953) (by norm_num)
theorem B311473 : Blo 287828 311473 := bbase (se 2 (by rfl) ⟨116802, by rfl⟩ : syracuseStep 311473 = 233605) (by norm_num)
theorem B737525 : Blo 287828 737525 := bbase (se 5 (by rfl) ⟨34571, by rfl⟩ : syracuseStep 737525 = 69143) (by norm_num)
theorem B311545 : Blo 287828 311545 := bbase (se 2 (by rfl) ⟨116829, by rfl⟩ : syracuseStep 311545 = 233659) (by norm_num)
theorem B1458485 : Blo 287828 1458485 := bbase (se 5 (by rfl) ⟨68366, by rfl⟩ : syracuseStep 1458485 = 136733) (by norm_num)
theorem B2769461 : Blo 287828 2769461 := bbase (se 5 (by rfl) ⟨129818, by rfl⟩ : syracuseStep 2769461 = 259637) (by norm_num)
theorem B737869 : Blo 287828 737869 := bbase (se 3 (by rfl) ⟨138350, by rfl⟩ : syracuseStep 737869 = 276701) (by norm_num)
theorem B410285 : Blo 287828 410285 := bbase (se 3 (by rfl) ⟨76928, by rfl⟩ : syracuseStep 410285 = 153857) (by norm_num)
theorem B737981 : Blo 287828 737981 := bbase (se 3 (by rfl) ⟨138371, by rfl⟩ : syracuseStep 737981 = 276743) (by norm_num)
theorem B1229573 : Blo 287828 1229573 := bbase (se 4 (by rfl) ⟨115272, by rfl⟩ : syracuseStep 1229573 = 230545) (by norm_num)
theorem B738173 : Blo 287828 738173 := bbase (se 3 (by rfl) ⟨138407, by rfl⟩ : syracuseStep 738173 = 276815) (by norm_num)
theorem B2212757 : Blo 287828 2212757 := bbase (se 6 (by rfl) ⟨51861, by rfl⟩ : syracuseStep 2212757 = 103723) (by norm_num)
theorem B1229813 : Blo 287828 1229813 := bbase (se 5 (by rfl) ⟨57647, by rfl⟩ : syracuseStep 1229813 = 115295) (by norm_num)
theorem B410837 : Blo 287828 410837 := bbase (se 7 (by rfl) ⟨4814, by rfl⟩ : syracuseStep 410837 = 9629) (by norm_num)
theorem B738517 : Blo 287828 738517 := bbase (se 7 (by rfl) ⟨8654, by rfl⟩ : syracuseStep 738517 = 17309) (by norm_num)
theorem B4179221 : Blo 287828 4179221 := bbase (se 6 (by rfl) ⟨97950, by rfl⟩ : syracuseStep 4179221 = 195901) (by norm_num)
theorem B738629 : Blo 287828 738629 := bbase (se 4 (by rfl) ⟨69246, by rfl⟩ : syracuseStep 738629 = 138493) (by norm_num)
theorem B1459781 : Blo 287828 1459781 := bbase (se 4 (by rfl) ⟨136854, by rfl⟩ : syracuseStep 1459781 = 273709) (by norm_num)
theorem B411589 : Blo 287828 411589 := bbase (se 4 (by rfl) ⟨38586, by rfl⟩ : syracuseStep 411589 = 77173) (by norm_num)
theorem B739277 : Blo 287828 739277 := bbase (se 3 (by rfl) ⟨138614, by rfl⟩ : syracuseStep 739277 = 277229) (by norm_num)
theorem B346241 : Blo 287828 346241 := bbase (se 2 (by rfl) ⟨129840, by rfl⟩ : syracuseStep 346241 = 259681) (by norm_num)
theorem B1099925 : Blo 287828 1099925 := bbase (se 6 (by rfl) ⟨25779, by rfl⟩ : syracuseStep 1099925 = 51559) (by norm_num)
theorem B1100213 : Blo 287828 1100213 := bbase (se 5 (by rfl) ⟨51572, by rfl⟩ : syracuseStep 1100213 = 103145) (by norm_num)
theorem B346577 : Blo 287828 346577 := bbase (se 2 (by rfl) ⟨129966, by rfl⟩ : syracuseStep 346577 = 259933) (by norm_num)
theorem B2804213 : Blo 287828 2804213 := bbase (se 5 (by rfl) ⟨131447, by rfl⟩ : syracuseStep 2804213 = 262895) (by norm_num)
theorem B346693 : Blo 287828 346693 := bbase (se 4 (by rfl) ⟨32502, by rfl⟩ : syracuseStep 346693 = 65005) (by norm_num)
theorem B346717 : Blo 287828 346717 := bbase (se 3 (by rfl) ⟨65009, by rfl⟩ : syracuseStep 346717 = 130019) (by norm_num)
theorem B412381 : Blo 287828 412381 := bbase (se 3 (by rfl) ⟨77321, by rfl⟩ : syracuseStep 412381 = 154643) (by norm_num)
theorem B740141 : Blo 287828 740141 := bbase (se 3 (by rfl) ⟨138776, by rfl⟩ : syracuseStep 740141 = 277553) (by norm_num)
theorem B1461077 : Blo 287828 1461077 := bbase (se 9 (by rfl) ⟨4280, by rfl⟩ : syracuseStep 1461077 = 8561) (by norm_num)
theorem B740333 : Blo 287828 740333 := bbase (se 3 (by rfl) ⟨138812, by rfl⟩ : syracuseStep 740333 = 277625) (by norm_num)
theorem B1854485 : Blo 287828 1854485 := bbase (se 6 (by rfl) ⟨43464, by rfl⟩ : syracuseStep 1854485 = 86929) (by norm_num)
theorem B412717 : Blo 287828 412717 := bbase (se 3 (by rfl) ⟨77384, by rfl⟩ : syracuseStep 412717 = 154769) (by norm_num)
theorem B1232101 : Blo 287828 1232101 := bbase (se 4 (by rfl) ⟨115509, by rfl⟩ : syracuseStep 1232101 = 231019) (by norm_num)
theorem B412933 : Blo 287828 412933 := bbase (se 4 (by rfl) ⟨38712, by rfl⟩ : syracuseStep 412933 = 77425) (by norm_num)
theorem B642325 : Blo 287828 642325 := bbase (se 6 (by rfl) ⟨15054, by rfl⟩ : syracuseStep 642325 = 30109) (by norm_num)
theorem B347413 : Blo 287828 347413 := bbase (se 6 (by rfl) ⟨8142, by rfl⟩ : syracuseStep 347413 = 16285) (by norm_num)
theorem B347509 : Blo 287828 347509 := bbase (se 5 (by rfl) ⟨16289, by rfl⟩ : syracuseStep 347509 = 32579) (by norm_num)
theorem B1101397 : Blo 287828 1101397 := bbase (se 8 (by rfl) ⟨6453, by rfl⟩ : syracuseStep 1101397 = 12907) (by norm_num)
theorem B413309 : Blo 287828 413309 := bbase (se 3 (by rfl) ⟨77495, by rfl⟩ : syracuseStep 413309 = 154991) (by norm_num)
theorem B380785 : Blo 287828 380785 := bbase (se 2 (by rfl) ⟨142794, by rfl⟩ : syracuseStep 380785 = 285589) (by norm_num)
theorem B1101701 : Blo 287828 1101701 := bbase (se 4 (by rfl) ⟨103284, by rfl⟩ : syracuseStep 1101701 = 206569) (by norm_num)
theorem B1167317 : Blo 287828 1167317 := bbase (se 7 (by rfl) ⟨13679, by rfl⟩ : syracuseStep 1167317 = 27359) (by norm_num)
theorem B1396709 : Blo 287828 1396709 := bbase (se 4 (by rfl) ⟨130941, by rfl⟩ : syracuseStep 1396709 = 261883) (by norm_num)
theorem B1462373 : Blo 287828 1462373 := bbase (se 4 (by rfl) ⟨137097, by rfl⟩ : syracuseStep 1462373 = 274195) (by norm_num)
theorem B1167653 : Blo 287828 1167653 := bbase (se 4 (by rfl) ⟨109467, by rfl⟩ : syracuseStep 1167653 = 218935) (by norm_num)
theorem B348509 : Blo 287828 348509 := bbase (se 3 (by rfl) ⟨65345, by rfl⟩ : syracuseStep 348509 = 130691) (by norm_num)
theorem B348797 : Blo 287828 348797 := bbase (se 3 (by rfl) ⟨65399, by rfl⟩ : syracuseStep 348797 = 130799) (by norm_num)
theorem B1233589 : Blo 287828 1233589 := bbase (se 5 (by rfl) ⟨57824, by rfl⟩ : syracuseStep 1233589 = 115649) (by norm_num)
theorem B1233605 : Blo 287828 1233605 := bbase (se 4 (by rfl) ⟨115650, by rfl⟩ : syracuseStep 1233605 = 231301) (by norm_num)
theorem B2249461 : Blo 287828 2249461 := bbase (se 5 (by rfl) ⟨105443, by rfl⟩ : syracuseStep 2249461 = 210887) (by norm_num)
theorem B348961 : Blo 287828 348961 := bbase (se 2 (by rfl) ⟨130860, by rfl⟩ : syracuseStep 348961 = 261721) (by norm_num)
theorem B348989 : Blo 287828 348989 := bbase (se 3 (by rfl) ⟨65435, by rfl⟩ : syracuseStep 348989 = 130871) (by norm_num)
theorem B4477781 : Blo 287828 4477781 := bbase (se 9 (by rfl) ⟨13118, by rfl⟩ : syracuseStep 4477781 = 26237) (by norm_num)
theorem B971621 : Blo 287828 971621 := bbase (se 4 (by rfl) ⟨91089, by rfl⟩ : syracuseStep 971621 = 182179) (by norm_num)
theorem B1659797 : Blo 287828 1659797 := bbase (se 6 (by rfl) ⟨38901, by rfl⟩ : syracuseStep 1659797 = 77803) (by norm_num)
theorem B349105 : Blo 287828 349105 := bbase (se 2 (by rfl) ⟨130914, by rfl⟩ : syracuseStep 349105 = 261829) (by norm_num)
theorem B414733 : Blo 287828 414733 := bbase (se 3 (by rfl) ⟨77762, by rfl⟩ : syracuseStep 414733 = 155525) (by norm_num)
theorem B349201 : Blo 287828 349201 := bbase (se 2 (by rfl) ⟨130950, by rfl⟩ : syracuseStep 349201 = 261901) (by norm_num)
theorem B972053 : Blo 287828 972053 := bbase (se 6 (by rfl) ⟨22782, by rfl⟩ : syracuseStep 972053 = 45565) (by norm_num)
theorem B1463669 : Blo 287828 1463669 := bbase (se 5 (by rfl) ⟨68609, by rfl⟩ : syracuseStep 1463669 = 137219) (by norm_num)
theorem B349681 : Blo 287828 349681 := bbase (se 2 (by rfl) ⟨131130, by rfl⟩ : syracuseStep 349681 = 262261) (by norm_num)
theorem B611869 : Blo 287828 611869 := bbase (se 3 (by rfl) ⟨114725, by rfl⟩ : syracuseStep 611869 = 229451) (by norm_num)
theorem B415325 : Blo 287828 415325 := bbase (se 3 (by rfl) ⟨77873, by rfl⟩ : syracuseStep 415325 = 155747) (by norm_num)
theorem B415405 : Blo 287828 415405 := bbase (se 3 (by rfl) ⟨77888, by rfl⟩ : syracuseStep 415405 = 155777) (by norm_num)
theorem B972485 : Blo 287828 972485 := bbase (se 4 (by rfl) ⟨91170, by rfl⟩ : syracuseStep 972485 = 182341) (by norm_num)
theorem B710405 : Blo 287828 710405 := bbase (se 4 (by rfl) ⟨66600, by rfl⟩ : syracuseStep 710405 = 133201) (by norm_num)
theorem B2119445 : Blo 287828 2119445 := bbase (se 6 (by rfl) ⟨49674, by rfl⟩ : syracuseStep 2119445 = 99349) (by norm_num)
theorem B1103813 : Blo 287828 1103813 := bbase (se 4 (by rfl) ⟨103482, by rfl⟩ : syracuseStep 1103813 = 206965) (by norm_num)
theorem B546925 : Blo 287828 546925 := bbase (se 3 (by rfl) ⟨102548, by rfl⟩ : syracuseStep 546925 = 205097) (by norm_num)
theorem B972917 : Blo 287828 972917 := bbase (se 5 (by rfl) ⟨45605, by rfl⟩ : syracuseStep 972917 = 91211) (by norm_num)
theorem B1104101 : Blo 287828 1104101 := bbase (se 4 (by rfl) ⟨103509, by rfl⟩ : syracuseStep 1104101 = 207019) (by norm_num)
theorem B547069 : Blo 287828 547069 := bbase (se 3 (by rfl) ⟨102575, by rfl⟩ : syracuseStep 547069 = 205151) (by norm_num)
theorem B547229 : Blo 287828 547229 := bbase (se 3 (by rfl) ⟨102605, by rfl⟩ : syracuseStep 547229 = 205211) (by norm_num)
theorem B973349 : Blo 287828 973349 := bbase (se 4 (by rfl) ⟨91251, by rfl⟩ : syracuseStep 973349 = 182503) (by norm_num)
theorem B547373 : Blo 287828 547373 := bbase (se 3 (by rfl) ⟨102632, by rfl⟩ : syracuseStep 547373 = 205265) (by norm_num)
theorem B2087477 : Blo 287828 2087477 := bbase (se 5 (by rfl) ⟨97850, by rfl⟩ : syracuseStep 2087477 = 195701) (by norm_num)
theorem B1464965 : Blo 287828 1464965 := bbase (se 4 (by rfl) ⟨137340, by rfl⟩ : syracuseStep 1464965 = 274681) (by norm_num)
theorem B1399493 : Blo 287828 1399493 := bbase (se 4 (by rfl) ⟨131202, by rfl⟩ : syracuseStep 1399493 = 262405) (by norm_num)
theorem B351005 : Blo 287828 351005 := bbase (se 3 (by rfl) ⟨65813, by rfl⟩ : syracuseStep 351005 = 131627) (by norm_num)
theorem B547661 : Blo 287828 547661 := bbase (se 3 (by rfl) ⟨102686, by rfl⟩ : syracuseStep 547661 = 205373) (by norm_num)
theorem B2087765 : Blo 287828 2087765 := bbase (se 9 (by rfl) ⟨6116, by rfl⟩ : syracuseStep 2087765 = 12233) (by norm_num)
theorem B1235861 : Blo 287828 1235861 := bbase (se 6 (by rfl) ⟨28965, by rfl⟩ : syracuseStep 1235861 = 57931) (by norm_num)
theorem B973781 : Blo 287828 973781 := bbase (se 7 (by rfl) ⟨11411, by rfl⟩ : syracuseStep 973781 = 22823) (by norm_num)
theorem B547813 : Blo 287828 547813 := bbase (se 4 (by rfl) ⟨51357, by rfl⟩ : syracuseStep 547813 = 102715) (by norm_num)
theorem B416917 : Blo 287828 416917 := bbase (se 6 (by rfl) ⟨9771, by rfl⟩ : syracuseStep 416917 = 19543) (by norm_num)
theorem B2645173 : Blo 287828 2645173 := bbase (se 5 (by rfl) ⟨123992, by rfl⟩ : syracuseStep 2645173 = 247985) (by norm_num)
theorem B318665 : Blo 287828 318665 := bbase (se 2 (by rfl) ⟨119499, by rfl⟩ : syracuseStep 318665 = 238999) (by norm_num)
theorem B548117 : Blo 287828 548117 := bbase (se 6 (by rfl) ⟨12846, by rfl⟩ : syracuseStep 548117 = 25693) (by norm_num)
theorem B974213 : Blo 287828 974213 := bbase (se 4 (by rfl) ⟨91332, by rfl⟩ : syracuseStep 974213 = 182665) (by norm_num)
theorem B1105285 : Blo 287828 1105285 := bbase (se 4 (by rfl) ⟨103620, by rfl⟩ : syracuseStep 1105285 = 207241) (by norm_num)
theorem B1171093 : Blo 287828 1171093 := bbase (se 6 (by rfl) ⟨27447, by rfl⟩ : syracuseStep 1171093 = 54895) (by norm_num)
theorem B1105589 : Blo 287828 1105589 := bbase (se 5 (by rfl) ⟨51824, by rfl⟩ : syracuseStep 1105589 = 103649) (by norm_num)
theorem B974645 : Blo 287828 974645 := bbase (se 5 (by rfl) ⟨45686, by rfl⟩ : syracuseStep 974645 = 91373) (by norm_num)
theorem B778133 : Blo 287828 778133 := bbase (se 6 (by rfl) ⟨18237, by rfl⟩ : syracuseStep 778133 = 36475) (by norm_num)
theorem B1466261 : Blo 287828 1466261 := bbase (se 6 (by rfl) ⟨34365, by rfl⟩ : syracuseStep 1466261 = 68731) (by norm_num)
theorem B548869 : Blo 287828 548869 := bbase (se 4 (by rfl) ⟨51456, by rfl⟩ : syracuseStep 548869 = 102913) (by norm_num)
theorem B549013 : Blo 287828 549013 := bbase (se 6 (by rfl) ⟨12867, by rfl⟩ : syracuseStep 549013 = 25735) (by norm_num)
theorem B1597589 : Blo 287828 1597589 := bbase (se 6 (by rfl) ⟨37443, by rfl⟩ : syracuseStep 1597589 = 74887) (by norm_num)
theorem B975077 : Blo 287828 975077 := bbase (se 4 (by rfl) ⟨91413, by rfl⟩ : syracuseStep 975077 = 182827) (by norm_num)
theorem B549173 : Blo 287828 549173 := bbase (se 5 (by rfl) ⟨25742, by rfl⟩ : syracuseStep 549173 = 51485) (by norm_num)
theorem B647621 : Blo 287828 647621 := bbase (se 4 (by rfl) ⟨60714, by rfl⟩ : syracuseStep 647621 = 121429) (by norm_num)
theorem B549317 : Blo 287828 549317 := bbase (se 4 (by rfl) ⟨51498, by rfl⟩ : syracuseStep 549317 = 102997) (by norm_num)
theorem B647693 : Blo 287828 647693 := bbase (se 3 (by rfl) ⟨121442, by rfl⟩ : syracuseStep 647693 = 242885) (by norm_num)
theorem B614957 : Blo 287828 614957 := bbase (se 3 (by rfl) ⟨115304, by rfl⟩ : syracuseStep 614957 = 230609) (by norm_num)
theorem B647765 : Blo 287828 647765 := bbase (se 8 (by rfl) ⟨3795, by rfl⟩ : syracuseStep 647765 = 7591) (by norm_num)
theorem B975509 : Blo 287828 975509 := bbase (se 6 (by rfl) ⟨22863, by rfl⟩ : syracuseStep 975509 = 45727) (by norm_num)
theorem B647837 : Blo 287828 647837 := bbase (se 3 (by rfl) ⟨121469, by rfl⟩ : syracuseStep 647837 = 242939) (by norm_num)
theorem B647909 : Blo 287828 647909 := bbase (se 4 (by rfl) ⟨60741, by rfl⟩ : syracuseStep 647909 = 121483) (by norm_num)
theorem B549605 : Blo 287828 549605 := bbase (se 4 (by rfl) ⟨51525, by rfl⟩ : syracuseStep 549605 = 103051) (by norm_num)
theorem B615197 : Blo 287828 615197 := bbase (se 3 (by rfl) ⟨115349, by rfl⟩ : syracuseStep 615197 = 230699) (by norm_num)
theorem B647981 : Blo 287828 647981 := bbase (se 3 (by rfl) ⟨121496, by rfl⟩ : syracuseStep 647981 = 242993) (by norm_num)
theorem B648053 : Blo 287828 648053 := bbase (se 5 (by rfl) ⟨30377, by rfl⟩ : syracuseStep 648053 = 60755) (by norm_num)
theorem B549757 : Blo 287828 549757 := bbase (se 3 (by rfl) ⟨103079, by rfl⟩ : syracuseStep 549757 = 206159) (by norm_num)
theorem B648125 : Blo 287828 648125 := bbase (se 3 (by rfl) ⟨121523, by rfl⟩ : syracuseStep 648125 = 243047) (by norm_num)
theorem B648197 : Blo 287828 648197 := bbase (se 4 (by rfl) ⟨60768, by rfl⟩ : syracuseStep 648197 = 121537) (by norm_num)
theorem B975941 : Blo 287828 975941 := bbase (se 4 (by rfl) ⟨91494, by rfl⟩ : syracuseStep 975941 = 182989) (by norm_num)
theorem B648269 : Blo 287828 648269 := bbase (se 3 (by rfl) ⟨121550, by rfl⟩ : syracuseStep 648269 = 243101) (by norm_num)
theorem B648341 : Blo 287828 648341 := bbase (se 6 (by rfl) ⟨15195, by rfl⟩ : syracuseStep 648341 = 30391) (by norm_num)
theorem B1467557 : Blo 287828 1467557 := bbase (se 4 (by rfl) ⟨137583, by rfl⟩ : syracuseStep 1467557 = 275167) (by norm_num)
theorem B550061 : Blo 287828 550061 := bbase (se 3 (by rfl) ⟨103136, by rfl⟩ : syracuseStep 550061 = 206273) (by norm_num)
theorem B648413 : Blo 287828 648413 := bbase (se 3 (by rfl) ⟨121577, by rfl⟩ : syracuseStep 648413 = 243155) (by norm_num)
theorem B615701 : Blo 287828 615701 := bbase (se 6 (by rfl) ⟨14430, by rfl⟩ : syracuseStep 615701 = 28861) (by norm_num)
theorem B615709 : Blo 287828 615709 := bbase (se 3 (by rfl) ⟨115445, by rfl⟩ : syracuseStep 615709 = 230891) (by norm_num)
theorem B648485 : Blo 287828 648485 := bbase (se 4 (by rfl) ⟨60795, by rfl⟩ : syracuseStep 648485 = 121591) (by norm_num)
theorem B648557 : Blo 287828 648557 := bbase (se 3 (by rfl) ⟨121604, by rfl⟩ : syracuseStep 648557 = 243209) (by norm_num)
theorem B648629 : Blo 287828 648629 := bbase (se 5 (by rfl) ⟨30404, by rfl⟩ : syracuseStep 648629 = 60809) (by norm_num)
theorem B1041893 : Blo 287828 1041893 := bbase (se 4 (by rfl) ⟨97677, by rfl⟩ : syracuseStep 1041893 = 195355) (by norm_num)
theorem B976373 : Blo 287828 976373 := bbase (se 5 (by rfl) ⟨45767, by rfl⟩ : syracuseStep 976373 = 91535) (by norm_num)
theorem B648701 : Blo 287828 648701 := bbase (se 3 (by rfl) ⟨121631, by rfl⟩ : syracuseStep 648701 = 243263) (by norm_num)
theorem B681485 : Blo 287828 681485 := bbase (se 3 (by rfl) ⟨127778, by rfl⟩ : syracuseStep 681485 = 255557) (by norm_num)
theorem B648773 : Blo 287828 648773 := bbase (se 4 (by rfl) ⟨60822, by rfl⟩ : syracuseStep 648773 = 121645) (by norm_num)
theorem B648845 : Blo 287828 648845 := bbase (se 3 (by rfl) ⟨121658, by rfl⟩ : syracuseStep 648845 = 243317) (by norm_num)
theorem B648917 : Blo 287828 648917 := bbase (se 7 (by rfl) ⟨7604, by rfl⟩ : syracuseStep 648917 = 15209) (by norm_num)
theorem B1107701 : Blo 287828 1107701 := bbase (se 5 (by rfl) ⟨51923, by rfl⟩ : syracuseStep 1107701 = 103847) (by norm_num)
theorem B648989 : Blo 287828 648989 := bbase (se 3 (by rfl) ⟨121685, by rfl⟩ : syracuseStep 648989 = 243371) (by norm_num)
theorem B649061 : Blo 287828 649061 := bbase (se 4 (by rfl) ⟨60849, by rfl⟩ : syracuseStep 649061 = 121699) (by norm_num)
theorem B1173365 : Blo 287828 1173365 := bbase (se 5 (by rfl) ⟨55001, by rfl⟩ : syracuseStep 1173365 = 110003) (by norm_num)
theorem B714629 : Blo 287828 714629 := bbase (se 4 (by rfl) ⟨66996, by rfl⟩ : syracuseStep 714629 = 133993) (by norm_num)
theorem B550813 : Blo 287828 550813 := bbase (se 3 (by rfl) ⟨103277, by rfl⟩ : syracuseStep 550813 = 206555) (by norm_num)
theorem B976805 : Blo 287828 976805 := bbase (se 4 (by rfl) ⟨91575, by rfl⟩ : syracuseStep 976805 = 183151) (by norm_num)
theorem B649133 : Blo 287828 649133 := bbase (se 3 (by rfl) ⟨121712, by rfl⟩ : syracuseStep 649133 = 243425) (by norm_num)
theorem B649205 : Blo 287828 649205 := bbase (se 5 (by rfl) ⟨30431, by rfl⟩ : syracuseStep 649205 = 60863) (by norm_num)
theorem B1107989 : Blo 287828 1107989 := bbase (se 6 (by rfl) ⟨25968, by rfl⟩ : syracuseStep 1107989 = 51937) (by norm_num)
theorem B550957 : Blo 287828 550957 := bbase (se 3 (by rfl) ⟨103304, by rfl⟩ : syracuseStep 550957 = 206609) (by norm_num)
theorem B649277 : Blo 287828 649277 := bbase (se 3 (by rfl) ⟨121739, by rfl⟩ : syracuseStep 649277 = 243479) (by norm_num)
theorem B2189429 : Blo 287828 2189429 := bbase (se 5 (by rfl) ⟨102629, by rfl⟩ : syracuseStep 2189429 = 205259) (by norm_num)
theorem B649349 : Blo 287828 649349 := bbase (se 4 (by rfl) ⟨60876, by rfl⟩ : syracuseStep 649349 = 121753) (by norm_num)
theorem B649421 : Blo 287828 649421 := bbase (se 3 (by rfl) ⟨121766, by rfl⟩ : syracuseStep 649421 = 243533) (by norm_num)
theorem B551117 : Blo 287828 551117 := bbase (se 3 (by rfl) ⟨103334, by rfl⟩ : syracuseStep 551117 = 206669) (by norm_num)
theorem B649493 : Blo 287828 649493 := bbase (se 6 (by rfl) ⟨15222, by rfl⟩ : syracuseStep 649493 = 30445) (by norm_num)
theorem B977237 : Blo 287828 977237 := bbase (se 10 (by rfl) ⟨1431, by rfl⟩ : syracuseStep 977237 = 2863) (by norm_num)
theorem B649565 : Blo 287828 649565 := bbase (se 3 (by rfl) ⟨121793, by rfl⟩ : syracuseStep 649565 = 243587) (by norm_num)
theorem B551261 : Blo 287828 551261 := bbase (se 3 (by rfl) ⟨103361, by rfl⟩ : syracuseStep 551261 = 206723) (by norm_num)
theorem B616837 : Blo 287828 616837 := bbase (se 4 (by rfl) ⟨57828, by rfl⟩ : syracuseStep 616837 = 115657) (by norm_num)
theorem B485797 : Blo 287828 485797 := bbase (se 4 (by rfl) ⟨45543, by rfl⟩ : syracuseStep 485797 = 91087) (by norm_num)
theorem B649637 : Blo 287828 649637 := bbase (se 4 (by rfl) ⟨60903, by rfl⟩ : syracuseStep 649637 = 121807) (by norm_num)
theorem B1468853 : Blo 287828 1468853 := bbase (se 5 (by rfl) ⟨68852, by rfl⟩ : syracuseStep 1468853 = 137705) (by norm_num)
theorem B649709 : Blo 287828 649709 := bbase (se 3 (by rfl) ⟨121820, by rfl⟩ : syracuseStep 649709 = 243641) (by norm_num)
theorem B485885 : Blo 287828 485885 := bbase (se 3 (by rfl) ⟨91103, by rfl⟩ : syracuseStep 485885 = 182207) (by norm_num)
theorem B649781 : Blo 287828 649781 := bbase (se 5 (by rfl) ⟨30458, by rfl⟩ : syracuseStep 649781 = 60917) (by norm_num)
theorem B486013 : Blo 287828 486013 := bbase (se 3 (by rfl) ⟨91127, by rfl⟩ : syracuseStep 486013 = 182255) (by norm_num)
theorem B649853 : Blo 287828 649853 := bbase (se 3 (by rfl) ⟨121847, by rfl⟩ : syracuseStep 649853 = 243695) (by norm_num)
theorem B551549 : Blo 287828 551549 := bbase (se 3 (by rfl) ⟨103415, by rfl⟩ : syracuseStep 551549 = 206831) (by norm_num)
theorem B518813 : Blo 287828 518813 := bbase (se 3 (by rfl) ⟨97277, by rfl⟩ : syracuseStep 518813 = 194555) (by norm_num)
theorem B649925 : Blo 287828 649925 := bbase (se 4 (by rfl) ⟨60930, by rfl⟩ : syracuseStep 649925 = 121861) (by norm_num)
theorem B486101 : Blo 287828 486101 := bbase (se 7 (by rfl) ⟨5696, by rfl⟩ : syracuseStep 486101 = 11393) (by norm_num)
theorem B617213 : Blo 287828 617213 := bbase (se 3 (by rfl) ⟨115727, by rfl⟩ : syracuseStep 617213 = 231455) (by norm_num)
theorem B977669 : Blo 287828 977669 := bbase (se 4 (by rfl) ⟨91656, by rfl⟩ : syracuseStep 977669 = 183313) (by norm_num)
theorem B649997 : Blo 287828 649997 := bbase (se 3 (by rfl) ⟨121874, by rfl⟩ : syracuseStep 649997 = 243749) (by norm_num)
theorem B551701 : Blo 287828 551701 := bbase (se 6 (by rfl) ⟨12930, by rfl⟩ : syracuseStep 551701 = 25861) (by norm_num)
theorem B486229 : Blo 287828 486229 := bbase (se 9 (by rfl) ⟨1424, by rfl⟩ : syracuseStep 486229 = 2849) (by norm_num)
theorem B650069 : Blo 287828 650069 := bbase (se 9 (by rfl) ⟨1904, by rfl⟩ : syracuseStep 650069 = 3809) (by norm_num)
theorem B846677 : Blo 287828 846677 := bbase (se 9 (by rfl) ⟨2480, by rfl⟩ : syracuseStep 846677 = 4961) (by norm_num)
theorem B1239893 : Blo 287828 1239893 := bbase (se 9 (by rfl) ⟨3632, by rfl⟩ : syracuseStep 1239893 = 7265) (by norm_num)
theorem B650141 : Blo 287828 650141 := bbase (se 3 (by rfl) ⟨121901, by rfl⟩ : syracuseStep 650141 = 243803) (by norm_num)
theorem B486317 : Blo 287828 486317 := bbase (se 3 (by rfl) ⟨91184, by rfl⟩ : syracuseStep 486317 = 182369) (by norm_num)
theorem B9989077 : Blo 287828 9989077 := bbase (se 7 (by rfl) ⟨117059, by rfl⟩ : syracuseStep 9989077 = 234119) (by norm_num)
theorem B650213 : Blo 287828 650213 := bbase (se 4 (by rfl) ⟨60957, by rfl⟩ : syracuseStep 650213 = 121915) (by norm_num)
theorem B486445 : Blo 287828 486445 := bbase (se 3 (by rfl) ⟨91208, by rfl⟩ : syracuseStep 486445 = 182417) (by norm_num)
theorem B650285 : Blo 287828 650285 := bbase (se 3 (by rfl) ⟨121928, by rfl⟩ : syracuseStep 650285 = 243857) (by norm_num)
theorem B552005 : Blo 287828 552005 := bbase (se 4 (by rfl) ⟨51750, by rfl⟩ : syracuseStep 552005 = 103501) (by norm_num)
theorem B650357 : Blo 287828 650357 := bbase (se 5 (by rfl) ⟨30485, by rfl⟩ : syracuseStep 650357 = 60971) (by norm_num)
theorem B486533 : Blo 287828 486533 := bbase (se 4 (by rfl) ⟨45612, by rfl⟩ : syracuseStep 486533 = 91225) (by norm_num)
theorem B978101 : Blo 287828 978101 := bbase (se 5 (by rfl) ⟨45848, by rfl⟩ : syracuseStep 978101 = 91697) (by norm_num)
theorem B650429 : Blo 287828 650429 := bbase (se 3 (by rfl) ⟨121955, by rfl⟩ : syracuseStep 650429 = 243911) (by norm_num)
theorem B486661 : Blo 287828 486661 := bbase (se 4 (by rfl) ⟨45624, by rfl⟩ : syracuseStep 486661 = 91249) (by norm_num)
theorem B650501 : Blo 287828 650501 := bbase (se 4 (by rfl) ⟨60984, by rfl⟩ : syracuseStep 650501 = 121969) (by norm_num)
theorem B945413 : Blo 287828 945413 := bbase (se 4 (by rfl) ⟨88632, by rfl⟩ : syracuseStep 945413 = 177265) (by norm_num)
theorem B3534101 : Blo 287828 3534101 := bbase (se 6 (by rfl) ⟨82830, by rfl⟩ : syracuseStep 3534101 = 165661) (by norm_num)
theorem B2485525 : Blo 287828 2485525 := bbase (se 6 (by rfl) ⟨58254, by rfl⟩ : syracuseStep 2485525 = 116509) (by norm_num)
theorem B1109285 : Blo 287828 1109285 := bbase (se 4 (by rfl) ⟨103995, by rfl⟩ : syracuseStep 1109285 = 207991) (by norm_num)
theorem B650573 : Blo 287828 650573 := bbase (se 3 (by rfl) ⟨121982, by rfl⟩ : syracuseStep 650573 = 243965) (by norm_num)
theorem B486749 : Blo 287828 486749 := bbase (se 3 (by rfl) ⟨91265, by rfl⟩ : syracuseStep 486749 = 182531) (by norm_num)
theorem B650645 : Blo 287828 650645 := bbase (se 6 (by rfl) ⟨15249, by rfl⟩ : syracuseStep 650645 = 30499) (by norm_num)
theorem B585157 : Blo 287828 585157 := bbase (se 4 (by rfl) ⟨54858, by rfl⟩ : syracuseStep 585157 = 109717) (by norm_num)
theorem B486877 : Blo 287828 486877 := bbase (se 3 (by rfl) ⟨91289, by rfl⟩ : syracuseStep 486877 = 182579) (by norm_num)
theorem B650717 : Blo 287828 650717 := bbase (se 3 (by rfl) ⟨122009, by rfl⟩ : syracuseStep 650717 = 244019) (by norm_num)
theorem B650789 : Blo 287828 650789 := bbase (se 4 (by rfl) ⟨61011, by rfl⟩ : syracuseStep 650789 = 122023) (by norm_num)
theorem B486965 : Blo 287828 486965 := bbase (se 5 (by rfl) ⟨22826, by rfl⟩ : syracuseStep 486965 = 45653) (by norm_num)
theorem B978533 : Blo 287828 978533 := bbase (se 4 (by rfl) ⟨91737, by rfl⟩ : syracuseStep 978533 = 183475) (by norm_num)
theorem B650861 : Blo 287828 650861 := bbase (se 3 (by rfl) ⟨122036, by rfl⟩ : syracuseStep 650861 = 244073) (by norm_num)
theorem B1502885 : Blo 287828 1502885 := bbase (se 4 (by rfl) ⟨140895, by rfl⟩ : syracuseStep 1502885 = 281791) (by norm_num)
theorem B487093 : Blo 287828 487093 := bbase (se 5 (by rfl) ⟨22832, by rfl⟩ : syracuseStep 487093 = 45665) (by norm_num)
theorem B650933 : Blo 287828 650933 := bbase (se 5 (by rfl) ⟨30512, by rfl⟩ : syracuseStep 650933 = 61025) (by norm_num)
theorem B1470149 : Blo 287828 1470149 := bbase (se 4 (by rfl) ⟨137826, by rfl⟩ : syracuseStep 1470149 = 275653) (by norm_num)
theorem B1994453 : Blo 287828 1994453 := bbase (se 7 (by rfl) ⟨23372, by rfl⟩ : syracuseStep 1994453 = 46745) (by norm_num)
theorem B651005 : Blo 287828 651005 := bbase (se 3 (by rfl) ⟨122063, by rfl⟩ : syracuseStep 651005 = 244127) (by norm_num)
theorem B487181 : Blo 287828 487181 := bbase (se 3 (by rfl) ⟨91346, by rfl⟩ : syracuseStep 487181 = 182693) (by norm_num)
theorem B552757 : Blo 287828 552757 := bbase (se 5 (by rfl) ⟨25910, by rfl⟩ : syracuseStep 552757 = 51821) (by norm_num)
theorem B651077 : Blo 287828 651077 := bbase (se 4 (by rfl) ⟨61038, by rfl⟩ : syracuseStep 651077 = 122077) (by norm_num)
theorem B487309 : Blo 287828 487309 := bbase (se 3 (by rfl) ⟨91370, by rfl⟩ : syracuseStep 487309 = 182741) (by norm_num)
theorem B651149 : Blo 287828 651149 := bbase (se 3 (by rfl) ⟨122090, by rfl⟩ : syracuseStep 651149 = 244181) (by norm_num)
theorem B1044373 : Blo 287828 1044373 := bbase (se 6 (by rfl) ⟨24477, by rfl⟩ : syracuseStep 1044373 = 48955) (by norm_num)
theorem B552901 : Blo 287828 552901 := bbase (se 4 (by rfl) ⟨51834, by rfl⟩ : syracuseStep 552901 = 103669) (by norm_num)
theorem B1142741 : Blo 287828 1142741 := bbase (se 7 (by rfl) ⟨13391, by rfl⟩ : syracuseStep 1142741 = 26783) (by norm_num)
theorem B651221 : Blo 287828 651221 := bbase (se 7 (by rfl) ⟨7631, by rfl⟩ : syracuseStep 651221 = 15263) (by norm_num)
theorem B487397 : Blo 287828 487397 := bbase (se 4 (by rfl) ⟨45693, by rfl⟩ : syracuseStep 487397 = 91387) (by norm_num)
theorem B978965 : Blo 287828 978965 := bbase (se 6 (by rfl) ⟨22944, by rfl⟩ : syracuseStep 978965 = 45889) (by norm_num)
theorem B651293 : Blo 287828 651293 := bbase (se 3 (by rfl) ⟨122117, by rfl⟩ : syracuseStep 651293 = 244235) (by norm_num)
theorem B487525 : Blo 287828 487525 := bbase (se 4 (by rfl) ⟨45705, by rfl⟩ : syracuseStep 487525 = 91411) (by norm_num)
theorem B651365 : Blo 287828 651365 := bbase (se 4 (by rfl) ⟨61065, by rfl⟩ : syracuseStep 651365 = 122131) (by norm_num)
theorem B553061 : Blo 287828 553061 := bbase (se 4 (by rfl) ⟨51849, by rfl⟩ : syracuseStep 553061 = 103699) (by norm_num)
theorem B651437 : Blo 287828 651437 := bbase (se 3 (by rfl) ⟨122144, by rfl⟩ : syracuseStep 651437 = 244289) (by norm_num)
theorem B487613 : Blo 287828 487613 := bbase (se 3 (by rfl) ⟨91427, by rfl⟩ : syracuseStep 487613 = 182855) (by norm_num)
theorem B651509 : Blo 287828 651509 := bbase (se 5 (by rfl) ⟨30539, by rfl⟩ : syracuseStep 651509 = 61079) (by norm_num)
theorem B553205 : Blo 287828 553205 := bbase (se 5 (by rfl) ⟨25931, by rfl⟩ : syracuseStep 553205 = 51863) (by norm_num)
theorem B323833 : Blo 287828 323833 := bbase (se 2 (by rfl) ⟨121437, by rfl⟩ : syracuseStep 323833 = 242875) (by norm_num)
theorem B323869 : Blo 287828 323869 := bbase (se 3 (by rfl) ⟨60725, by rfl⟩ : syracuseStep 323869 = 121451) (by norm_num)
theorem B520501 : Blo 287828 520501 := bbase (se 5 (by rfl) ⟨24398, by rfl⟩ : syracuseStep 520501 = 48797) (by norm_num)
theorem B487741 : Blo 287828 487741 := bbase (se 3 (by rfl) ⟨91451, by rfl⟩ : syracuseStep 487741 = 182903) (by norm_num)
theorem B651581 : Blo 287828 651581 := bbase (se 3 (by rfl) ⟨122171, by rfl⟩ : syracuseStep 651581 = 244343) (by norm_num)
theorem B323905 : Blo 287828 323905 := bbase (se 2 (by rfl) ⟨121464, by rfl⟩ : syracuseStep 323905 = 242929) (by norm_num)
theorem B323941 : Blo 287828 323941 := bbase (se 4 (by rfl) ⟨30369, by rfl⟩ : syracuseStep 323941 = 60739) (by norm_num)
theorem B618853 : Blo 287828 618853 := bbase (se 4 (by rfl) ⟨58017, by rfl⟩ : syracuseStep 618853 = 116035) (by norm_num)
theorem B651653 : Blo 287828 651653 := bbase (se 4 (by rfl) ⟨61092, by rfl⟩ : syracuseStep 651653 = 122185) (by norm_num)
theorem B323977 : Blo 287828 323977 := bbase (se 2 (by rfl) ⟨121491, by rfl⟩ : syracuseStep 323977 = 242983) (by norm_num)
theorem B487829 : Blo 287828 487829 := bbase (se 6 (by rfl) ⟨11433, by rfl⟩ : syracuseStep 487829 = 22867) (by norm_num)
theorem B324013 : Blo 287828 324013 := bbase (se 3 (by rfl) ⟨60752, by rfl⟩ : syracuseStep 324013 = 121505) (by norm_num)
theorem B979397 : Blo 287828 979397 := bbase (se 4 (by rfl) ⟨91818, by rfl⟩ : syracuseStep 979397 = 183637) (by norm_num)
theorem B651725 : Blo 287828 651725 := bbase (se 3 (by rfl) ⟨122198, by rfl⟩ : syracuseStep 651725 = 244397) (by norm_num)
theorem B324049 : Blo 287828 324049 := bbase (se 2 (by rfl) ⟨121518, by rfl⟩ : syracuseStep 324049 = 243037) (by norm_num)
theorem B324085 : Blo 287828 324085 := bbase (se 5 (by rfl) ⟨15191, by rfl⟩ : syracuseStep 324085 = 30383) (by norm_num)
theorem B586253 : Blo 287828 586253 := bbase (se 3 (by rfl) ⟨109922, by rfl⟩ : syracuseStep 586253 = 219845) (by norm_num)
theorem B487957 : Blo 287828 487957 := bbase (se 6 (by rfl) ⟨11436, by rfl⟩ : syracuseStep 487957 = 22873) (by norm_num)
theorem B651797 : Blo 287828 651797 := bbase (se 6 (by rfl) ⟨15276, by rfl⟩ : syracuseStep 651797 = 30553) (by norm_num)
theorem B553493 : Blo 287828 553493 := bbase (se 6 (by rfl) ⟨12972, by rfl⟩ : syracuseStep 553493 = 25945) (by norm_num)
theorem B324121 : Blo 287828 324121 := bbase (se 2 (by rfl) ⟨121545, by rfl⟩ : syracuseStep 324121 = 243091) (by norm_num)
theorem B324157 : Blo 287828 324157 := bbase (se 3 (by rfl) ⟨60779, by rfl⟩ : syracuseStep 324157 = 121559) (by norm_num)
theorem B1241669 : Blo 287828 1241669 := bbase (se 4 (by rfl) ⟨116406, by rfl⟩ : syracuseStep 1241669 = 232813) (by norm_num)
theorem B520789 : Blo 287828 520789 := bbase (se 8 (by rfl) ⟨3051, by rfl⟩ : syracuseStep 520789 = 6103) (by norm_num)
theorem B651869 : Blo 287828 651869 := bbase (se 3 (by rfl) ⟨122225, by rfl⟩ : syracuseStep 651869 = 244451) (by norm_num)
theorem B324193 : Blo 287828 324193 := bbase (se 2 (by rfl) ⟨121572, by rfl⟩ : syracuseStep 324193 = 243145) (by norm_num)
theorem B488045 : Blo 287828 488045 := bbase (se 3 (by rfl) ⟨91508, by rfl⟩ : syracuseStep 488045 = 183017) (by norm_num)
theorem B324229 : Blo 287828 324229 := bbase (se 4 (by rfl) ⟨30396, by rfl⟩ : syracuseStep 324229 = 60793) (by norm_num)
theorem B651941 : Blo 287828 651941 := bbase (se 4 (by rfl) ⟨61119, by rfl⟩ : syracuseStep 651941 = 122239) (by norm_num)
theorem B324265 : Blo 287828 324265 := bbase (se 2 (by rfl) ⟨121599, by rfl⟩ : syracuseStep 324265 = 243199) (by norm_num)
theorem B553645 : Blo 287828 553645 := bbase (se 3 (by rfl) ⟨103808, by rfl⟩ : syracuseStep 553645 = 207617) (by norm_num)
theorem B324301 : Blo 287828 324301 := bbase (se 3 (by rfl) ⟨60806, by rfl⟩ : syracuseStep 324301 = 121613) (by norm_num)
theorem B488173 : Blo 287828 488173 := bbase (se 3 (by rfl) ⟨91532, by rfl⟩ : syracuseStep 488173 = 183065) (by norm_num)
theorem B652013 : Blo 287828 652013 := bbase (se 3 (by rfl) ⟨122252, by rfl⟩ : syracuseStep 652013 = 244505) (by norm_num)
theorem B324337 : Blo 287828 324337 := bbase (se 2 (by rfl) ⟨121626, by rfl⟩ : syracuseStep 324337 = 243253) (by norm_num)
theorem B324373 : Blo 287828 324373 := bbase (se 6 (by rfl) ⟨7602, by rfl⟩ : syracuseStep 324373 = 15205) (by norm_num)
theorem B652085 : Blo 287828 652085 := bbase (se 5 (by rfl) ⟨30566, by rfl⟩ : syracuseStep 652085 = 61133) (by norm_num)
theorem B324409 : Blo 287828 324409 := bbase (se 2 (by rfl) ⟨121653, by rfl⟩ : syracuseStep 324409 = 243307) (by norm_num)
theorem B488261 : Blo 287828 488261 := bbase (se 4 (by rfl) ⟨45774, by rfl⟩ : syracuseStep 488261 = 91549) (by norm_num)
theorem B324445 : Blo 287828 324445 := bbase (se 3 (by rfl) ⟨60833, by rfl⟩ : syracuseStep 324445 = 121667) (by norm_num)
theorem B979829 : Blo 287828 979829 := bbase (se 5 (by rfl) ⟨45929, by rfl⟩ : syracuseStep 979829 = 91859) (by norm_num)
theorem B652157 : Blo 287828 652157 := bbase (se 3 (by rfl) ⟨122279, by rfl⟩ : syracuseStep 652157 = 244559) (by norm_num)
theorem B324481 : Blo 287828 324481 := bbase (se 2 (by rfl) ⟨121680, by rfl⟩ : syracuseStep 324481 = 243361) (by norm_num)
theorem B324517 : Blo 287828 324517 := bbase (se 4 (by rfl) ⟨30423, by rfl⟩ : syracuseStep 324517 = 60847) (by norm_num)
theorem B488389 : Blo 287828 488389 := bbase (se 4 (by rfl) ⟨45786, by rfl⟩ : syracuseStep 488389 = 91573) (by norm_num)
theorem B652229 : Blo 287828 652229 := bbase (se 4 (by rfl) ⟨61146, by rfl⟩ : syracuseStep 652229 = 122293) (by norm_num)
theorem B324553 : Blo 287828 324553 := bbase (se 2 (by rfl) ⟨121707, by rfl⟩ : syracuseStep 324553 = 243415) (by norm_num)
theorem B1471445 : Blo 287828 1471445 := bbase (se 7 (by rfl) ⟨17243, by rfl⟩ : syracuseStep 1471445 = 34487) (by norm_num)
theorem B553949 : Blo 287828 553949 := bbase (se 3 (by rfl) ⟨103865, by rfl⟩ : syracuseStep 553949 = 207731) (by norm_num)
theorem B324589 : Blo 287828 324589 := bbase (se 3 (by rfl) ⟨60860, by rfl⟩ : syracuseStep 324589 = 121721) (by norm_num)
theorem B652301 : Blo 287828 652301 := bbase (se 3 (by rfl) ⟨122306, by rfl⟩ : syracuseStep 652301 = 244613) (by norm_num)
theorem B324625 : Blo 287828 324625 := bbase (se 2 (by rfl) ⟨121734, by rfl⟩ : syracuseStep 324625 = 243469) (by norm_num)
theorem B488477 : Blo 287828 488477 := bbase (se 3 (by rfl) ⟨91589, by rfl⟩ : syracuseStep 488477 = 183179) (by norm_num)
theorem B324661 : Blo 287828 324661 := bbase (se 5 (by rfl) ⟨15218, by rfl⟩ : syracuseStep 324661 = 30437) (by norm_num)
theorem B652373 : Blo 287828 652373 := bbase (se 8 (by rfl) ⟨3822, by rfl⟩ : syracuseStep 652373 = 7645) (by norm_num)
theorem B947285 : Blo 287828 947285 := bbase (se 8 (by rfl) ⟨5550, by rfl⟩ : syracuseStep 947285 = 11101) (by norm_num)
theorem B324697 : Blo 287828 324697 := bbase (se 2 (by rfl) ⟨121761, by rfl⟩ : syracuseStep 324697 = 243523) (by norm_num)
theorem B324733 : Blo 287828 324733 := bbase (se 3 (by rfl) ⟨60887, by rfl⟩ : syracuseStep 324733 = 121775) (by norm_num)
theorem B488605 : Blo 287828 488605 := bbase (se 3 (by rfl) ⟨91613, by rfl⟩ : syracuseStep 488605 = 183227) (by norm_num)
theorem B652445 : Blo 287828 652445 := bbase (se 3 (by rfl) ⟨122333, by rfl⟩ : syracuseStep 652445 = 244667) (by norm_num)
theorem B324769 : Blo 287828 324769 := bbase (se 2 (by rfl) ⟨121788, by rfl⟩ : syracuseStep 324769 = 243577) (by norm_num)
theorem B324805 : Blo 287828 324805 := bbase (se 4 (by rfl) ⟨30450, by rfl⟩ : syracuseStep 324805 = 60901) (by norm_num)
theorem B2487509 : Blo 287828 2487509 := bbase (se 7 (by rfl) ⟨29150, by rfl⟩ : syracuseStep 2487509 = 58301) (by norm_num)
theorem B586973 : Blo 287828 586973 := bbase (se 3 (by rfl) ⟨110057, by rfl⟩ : syracuseStep 586973 = 220115) (by norm_num)
theorem B619741 : Blo 287828 619741 := bbase (se 3 (by rfl) ⟨116201, by rfl⟩ : syracuseStep 619741 = 232403) (by norm_num)
theorem B652517 : Blo 287828 652517 := bbase (se 4 (by rfl) ⟨61173, by rfl⟩ : syracuseStep 652517 = 122347) (by norm_num)
theorem B324841 : Blo 287828 324841 := bbase (se 2 (by rfl) ⟨121815, by rfl⟩ : syracuseStep 324841 = 243631) (by norm_num)
theorem B488693 : Blo 287828 488693 := bbase (se 5 (by rfl) ⟨22907, by rfl⟩ : syracuseStep 488693 = 45815) (by norm_num)
theorem B324877 : Blo 287828 324877 := bbase (se 3 (by rfl) ⟨60914, by rfl⟩ : syracuseStep 324877 = 121829) (by norm_num)
theorem B1176869 : Blo 287828 1176869 := bbase (se 4 (by rfl) ⟨110331, by rfl⟩ : syracuseStep 1176869 = 220663) (by norm_num)
theorem B980261 : Blo 287828 980261 := bbase (se 4 (by rfl) ⟨91899, by rfl⟩ : syracuseStep 980261 = 183799) (by norm_num)
theorem B652589 : Blo 287828 652589 := bbase (se 3 (by rfl) ⟨122360, by rfl⟩ : syracuseStep 652589 = 244721) (by norm_num)
theorem B324913 : Blo 287828 324913 := bbase (se 2 (by rfl) ⟨121842, by rfl⟩ : syracuseStep 324913 = 243685) (by norm_num)
theorem B324949 : Blo 287828 324949 := bbase (se 13 (by rfl) ⟨59, by rfl⟩ : syracuseStep 324949 = 119) (by norm_num)
theorem B521581 : Blo 287828 521581 := bbase (se 3 (by rfl) ⟨97796, by rfl⟩ : syracuseStep 521581 = 195593) (by norm_num)
theorem B488821 : Blo 287828 488821 := bbase (se 5 (by rfl) ⟨22913, by rfl⟩ : syracuseStep 488821 = 45827) (by norm_num)
theorem B652661 : Blo 287828 652661 := bbase (se 5 (by rfl) ⟨30593, by rfl⟩ : syracuseStep 652661 = 61187) (by norm_num)
theorem B324985 : Blo 287828 324985 := bbase (se 2 (by rfl) ⟨121869, by rfl⟩ : syracuseStep 324985 = 243739) (by norm_num)
theorem B325021 : Blo 287828 325021 := bbase (se 3 (by rfl) ⟨60941, by rfl⟩ : syracuseStep 325021 = 121883) (by norm_num)
theorem B652733 : Blo 287828 652733 := bbase (se 3 (by rfl) ⟨122387, by rfl⟩ : syracuseStep 652733 = 244775) (by norm_num)
theorem B325057 : Blo 287828 325057 := bbase (se 2 (by rfl) ⟨121896, by rfl⟩ : syracuseStep 325057 = 243793) (by norm_num)
theorem B488909 : Blo 287828 488909 := bbase (se 3 (by rfl) ⟨91670, by rfl⟩ : syracuseStep 488909 = 183341) (by norm_num)
theorem B325093 : Blo 287828 325093 := bbase (se 4 (by rfl) ⟨30477, by rfl⟩ : syracuseStep 325093 = 60955) (by norm_num)
theorem B521725 : Blo 287828 521725 := bbase (se 3 (by rfl) ⟨97823, by rfl⟩ : syracuseStep 521725 = 195647) (by norm_num)
theorem B652805 : Blo 287828 652805 := bbase (se 4 (by rfl) ⟨61200, by rfl⟩ : syracuseStep 652805 = 122401) (by norm_num)
theorem B325129 : Blo 287828 325129 := bbase (se 2 (by rfl) ⟨121923, by rfl⟩ : syracuseStep 325129 = 243847) (by norm_num)
theorem B1242661 : Blo 287828 1242661 := bbase (se 4 (by rfl) ⟨116499, by rfl⟩ : syracuseStep 1242661 = 232999) (by norm_num)
theorem B325165 : Blo 287828 325165 := bbase (se 3 (by rfl) ⟨60968, by rfl⟩ : syracuseStep 325165 = 121937) (by norm_num)
theorem B489037 : Blo 287828 489037 := bbase (se 3 (by rfl) ⟨91694, by rfl⟩ : syracuseStep 489037 = 183389) (by norm_num)
theorem B652877 : Blo 287828 652877 := bbase (se 3 (by rfl) ⟨122414, by rfl⟩ : syracuseStep 652877 = 244829) (by norm_num)
theorem B325201 : Blo 287828 325201 := bbase (se 2 (by rfl) ⟨121950, by rfl⟩ : syracuseStep 325201 = 243901) (by norm_num)
theorem B325237 : Blo 287828 325237 := bbase (se 5 (by rfl) ⟨15245, by rfl⟩ : syracuseStep 325237 = 30491) (by norm_num)
theorem B652949 : Blo 287828 652949 := bbase (se 6 (by rfl) ⟨15303, by rfl⟩ : syracuseStep 652949 = 30607) (by norm_num)
theorem B325273 : Blo 287828 325273 := bbase (se 2 (by rfl) ⟨121977, by rfl⟩ : syracuseStep 325273 = 243955) (by norm_num)
theorem B521885 : Blo 287828 521885 := bbase (se 3 (by rfl) ⟨97853, by rfl⟩ : syracuseStep 521885 = 195707) (by norm_num)
theorem B489125 : Blo 287828 489125 := bbase (se 4 (by rfl) ⟨45855, by rfl⟩ : syracuseStep 489125 = 91711) (by norm_num)
theorem B1111733 : Blo 287828 1111733 := bbase (se 5 (by rfl) ⟨52112, by rfl⟩ : syracuseStep 1111733 = 104225) (by norm_num)
theorem B2815669 : Blo 287828 2815669 := bbase (se 5 (by rfl) ⟨131984, by rfl⟩ : syracuseStep 2815669 = 263969) (by norm_num)
theorem B325309 : Blo 287828 325309 := bbase (se 3 (by rfl) ⟨60995, by rfl⟩ : syracuseStep 325309 = 121991) (by norm_num)
theorem B620237 : Blo 287828 620237 := bbase (se 3 (by rfl) ⟨116294, by rfl⟩ : syracuseStep 620237 = 232589) (by norm_num)
theorem B980693 : Blo 287828 980693 := bbase (se 7 (by rfl) ⟨11492, by rfl⟩ : syracuseStep 980693 = 22985) (by norm_num)
theorem B1865429 : Blo 287828 1865429 := bbase (se 7 (by rfl) ⟨21860, by rfl⟩ : syracuseStep 1865429 = 43721) (by norm_num)
theorem B653021 : Blo 287828 653021 := bbase (se 3 (by rfl) ⟨122441, by rfl⟩ : syracuseStep 653021 = 244883) (by norm_num)
theorem B325345 : Blo 287828 325345 := bbase (se 2 (by rfl) ⟨122004, by rfl⟩ : syracuseStep 325345 = 244009) (by norm_num)
theorem B521957 : Blo 287828 521957 := bbase (se 4 (by rfl) ⟨48933, by rfl⟩ : syracuseStep 521957 = 97867) (by norm_num)
theorem B325381 : Blo 287828 325381 := bbase (se 4 (by rfl) ⟨30504, by rfl⟩ : syracuseStep 325381 = 61009) (by norm_num)
theorem B587557 : Blo 287828 587557 := bbase (se 4 (by rfl) ⟨55083, by rfl⟩ : syracuseStep 587557 = 110167) (by norm_num)
theorem B489253 : Blo 287828 489253 := bbase (se 4 (by rfl) ⟨45867, by rfl⟩ : syracuseStep 489253 = 91735) (by norm_num)
theorem B653093 : Blo 287828 653093 := bbase (se 4 (by rfl) ⟨61227, by rfl⟩ : syracuseStep 653093 = 122455) (by norm_num)
theorem B325417 : Blo 287828 325417 := bbase (se 2 (by rfl) ⟨122031, by rfl⟩ : syracuseStep 325417 = 244063) (by norm_num)
theorem B325453 : Blo 287828 325453 := bbase (se 3 (by rfl) ⟨61022, by rfl⟩ : syracuseStep 325453 = 122045) (by norm_num)
theorem B653165 : Blo 287828 653165 := bbase (se 3 (by rfl) ⟨122468, by rfl⟩ : syracuseStep 653165 = 244937) (by norm_num)
theorem B325489 : Blo 287828 325489 := bbase (se 2 (by rfl) ⟨122058, by rfl⟩ : syracuseStep 325489 = 244117) (by norm_num)
theorem B489341 : Blo 287828 489341 := bbase (se 3 (by rfl) ⟨91751, by rfl⟩ : syracuseStep 489341 = 183503) (by norm_num)
theorem B325525 : Blo 287828 325525 := bbase (se 6 (by rfl) ⟨7629, by rfl⟩ : syracuseStep 325525 = 15259) (by norm_num)
theorem B653237 : Blo 287828 653237 := bbase (se 5 (by rfl) ⟨30620, by rfl⟩ : syracuseStep 653237 = 61241) (by norm_num)
theorem B325561 : Blo 287828 325561 := bbase (se 2 (by rfl) ⟨122085, by rfl⟩ : syracuseStep 325561 = 244171) (by norm_num)
theorem B325597 : Blo 287828 325597 := bbase (se 3 (by rfl) ⟨61049, by rfl⟩ : syracuseStep 325597 = 122099) (by norm_num)
theorem B653309 : Blo 287828 653309 := bbase (se 3 (by rfl) ⟨122495, by rfl⟩ : syracuseStep 653309 = 244991) (by norm_num)
theorem B489469 : Blo 287828 489469 := bbase (se 3 (by rfl) ⟨91775, by rfl⟩ : syracuseStep 489469 = 183551) (by norm_num)
theorem B325633 : Blo 287828 325633 := bbase (se 2 (by rfl) ⟨122112, by rfl⟩ : syracuseStep 325633 = 244225) (by norm_num)
theorem B325669 : Blo 287828 325669 := bbase (se 4 (by rfl) ⟨30531, by rfl⟩ : syracuseStep 325669 = 61063) (by norm_num)
theorem B653381 : Blo 287828 653381 := bbase (se 4 (by rfl) ⟨61254, by rfl⟩ : syracuseStep 653381 = 122509) (by norm_num)
theorem B325705 : Blo 287828 325705 := bbase (se 2 (by rfl) ⟨122139, by rfl⟩ : syracuseStep 325705 = 244279) (by norm_num)
theorem B489557 : Blo 287828 489557 := bbase (se 8 (by rfl) ⟨2868, by rfl⟩ : syracuseStep 489557 = 5737) (by norm_num)
theorem B325741 : Blo 287828 325741 := bbase (se 3 (by rfl) ⟨61076, by rfl⟩ : syracuseStep 325741 = 122153) (by norm_num)
theorem B981125 : Blo 287828 981125 := bbase (se 4 (by rfl) ⟨91980, by rfl⟩ : syracuseStep 981125 = 183961) (by norm_num)
theorem B653453 : Blo 287828 653453 := bbase (se 3 (by rfl) ⟨122522, by rfl⟩ : syracuseStep 653453 = 245045) (by norm_num)
theorem B325777 : Blo 287828 325777 := bbase (se 2 (by rfl) ⟨122166, by rfl⟩ : syracuseStep 325777 = 244333) (by norm_num)
theorem B293041 : Blo 287828 293041 := bbase (se 2 (by rfl) ⟨109890, by rfl⟩ : syracuseStep 293041 = 219781) (by norm_num)
theorem B325813 : Blo 287828 325813 := bbase (se 5 (by rfl) ⟨15272, by rfl⟩ : syracuseStep 325813 = 30545) (by norm_num)
theorem B489685 : Blo 287828 489685 := bbase (se 7 (by rfl) ⟨5738, by rfl⟩ : syracuseStep 489685 = 11477) (by norm_num)
theorem B653525 : Blo 287828 653525 := bbase (se 7 (by rfl) ⟨7658, by rfl⟩ : syracuseStep 653525 = 15317) (by norm_num)
theorem B325849 : Blo 287828 325849 := bbase (se 2 (by rfl) ⟨122193, by rfl⟩ : syracuseStep 325849 = 244387) (by norm_num)
theorem B1472741 : Blo 287828 1472741 := bbase (se 4 (by rfl) ⟨138069, by rfl⟩ : syracuseStep 1472741 = 276139) (by norm_num)
theorem B325885 : Blo 287828 325885 := bbase (se 3 (by rfl) ⟨61103, by rfl⟩ : syracuseStep 325885 = 122207) (by norm_num)
theorem B653597 : Blo 287828 653597 := bbase (se 3 (by rfl) ⟨122549, by rfl⟩ : syracuseStep 653597 = 245099) (by norm_num)
theorem B325921 : Blo 287828 325921 := bbase (se 2 (by rfl) ⟨122220, by rfl⟩ : syracuseStep 325921 = 244441) (by norm_num)
theorem B489773 : Blo 287828 489773 := bbase (se 3 (by rfl) ⟨91832, by rfl⟩ : syracuseStep 489773 = 183665) (by norm_num)
theorem B325957 : Blo 287828 325957 := bbase (se 4 (by rfl) ⟨30558, by rfl⟩ : syracuseStep 325957 = 61117) (by norm_num)
theorem B653669 : Blo 287828 653669 := bbase (se 4 (by rfl) ⟨61281, by rfl⟩ : syracuseStep 653669 = 122563) (by norm_num)
theorem B325993 : Blo 287828 325993 := bbase (se 2 (by rfl) ⟨122247, by rfl⟩ : syracuseStep 325993 = 244495) (by norm_num)
theorem B326029 : Blo 287828 326029 := bbase (se 3 (by rfl) ⟨61130, by rfl⟩ : syracuseStep 326029 = 122261) (by norm_num)
theorem B489901 : Blo 287828 489901 := bbase (se 3 (by rfl) ⟨91856, by rfl⟩ : syracuseStep 489901 = 183713) (by norm_num)
theorem B653741 : Blo 287828 653741 := bbase (se 3 (by rfl) ⟨122576, by rfl⟩ : syracuseStep 653741 = 245153) (by norm_num)
theorem B326065 : Blo 287828 326065 := bbase (se 2 (by rfl) ⟨122274, by rfl⟩ : syracuseStep 326065 = 244549) (by norm_num)
theorem B784837 : Blo 287828 784837 := bbase (se 4 (by rfl) ⟨73578, by rfl⟩ : syracuseStep 784837 = 147157) (by norm_num)
theorem B326101 : Blo 287828 326101 := bbase (se 7 (by rfl) ⟨3821, by rfl⟩ : syracuseStep 326101 = 7643) (by norm_num)
theorem B653813 : Blo 287828 653813 := bbase (se 5 (by rfl) ⟨30647, by rfl⟩ : syracuseStep 653813 = 61295) (by norm_num)
theorem B326137 : Blo 287828 326137 := bbase (se 2 (by rfl) ⟨122301, by rfl⟩ : syracuseStep 326137 = 244603) (by norm_num)
theorem B489989 : Blo 287828 489989 := bbase (se 4 (by rfl) ⟨45936, by rfl⟩ : syracuseStep 489989 = 91873) (by norm_num)
theorem B326173 : Blo 287828 326173 := bbase (se 3 (by rfl) ⟨61157, by rfl⟩ : syracuseStep 326173 = 122315) (by norm_num)
theorem B621101 : Blo 287828 621101 := bbase (se 3 (by rfl) ⟨116456, by rfl⟩ : syracuseStep 621101 = 232913) (by norm_num)
theorem B981557 : Blo 287828 981557 := bbase (se 5 (by rfl) ⟨46010, by rfl⟩ : syracuseStep 981557 = 92021) (by norm_num)
theorem B653885 : Blo 287828 653885 := bbase (se 3 (by rfl) ⟨122603, by rfl⟩ : syracuseStep 653885 = 245207) (by norm_num)
theorem B326209 : Blo 287828 326209 := bbase (se 2 (by rfl) ⟨122328, by rfl⟩ : syracuseStep 326209 = 244657) (by norm_num)
theorem B326245 : Blo 287828 326245 := bbase (se 4 (by rfl) ⟨30585, by rfl⟩ : syracuseStep 326245 = 61171) (by norm_num)
theorem B653957 : Blo 287828 653957 := bbase (se 4 (by rfl) ⟨61308, by rfl⟩ : syracuseStep 653957 = 122617) (by norm_num)
theorem B490117 : Blo 287828 490117 := bbase (se 4 (by rfl) ⟨45948, by rfl⟩ : syracuseStep 490117 = 91897) (by norm_num)
theorem B326281 : Blo 287828 326281 := bbase (se 2 (by rfl) ⟨122355, by rfl⟩ : syracuseStep 326281 = 244711) (by norm_num)
theorem B326317 : Blo 287828 326317 := bbase (se 3 (by rfl) ⟨61184, by rfl⟩ : syracuseStep 326317 = 122369) (by norm_num)
theorem B621245 : Blo 287828 621245 := bbase (se 3 (by rfl) ⟨116483, by rfl⟩ : syracuseStep 621245 = 232967) (by norm_num)
theorem B654029 : Blo 287828 654029 := bbase (se 3 (by rfl) ⟨122630, by rfl⟩ : syracuseStep 654029 = 245261) (by norm_num)
theorem B326353 : Blo 287828 326353 := bbase (se 2 (by rfl) ⟨122382, by rfl⟩ : syracuseStep 326353 = 244765) (by norm_num)
theorem B522965 : Blo 287828 522965 := bbase (se 7 (by rfl) ⟨6128, by rfl⟩ : syracuseStep 522965 = 12257) (by norm_num)
theorem B490205 : Blo 287828 490205 := bbase (se 3 (by rfl) ⟨91913, by rfl⟩ : syracuseStep 490205 = 183827) (by norm_num)
theorem B326389 : Blo 287828 326389 := bbase (se 5 (by rfl) ⟨15299, by rfl⟩ : syracuseStep 326389 = 30599) (by norm_num)
theorem B654101 : Blo 287828 654101 := bbase (se 6 (by rfl) ⟨15330, by rfl⟩ : syracuseStep 654101 = 30661) (by norm_num)
theorem B326425 : Blo 287828 326425 := bbase (se 2 (by rfl) ⟨122409, by rfl⟩ : syracuseStep 326425 = 244819) (by norm_num)
theorem B326461 : Blo 287828 326461 := bbase (se 3 (by rfl) ⟨61211, by rfl⟩ : syracuseStep 326461 = 122423) (by norm_num)
theorem B490333 : Blo 287828 490333 := bbase (se 3 (by rfl) ⟨91937, by rfl⟩ : syracuseStep 490333 = 183875) (by norm_num)
theorem B654173 : Blo 287828 654173 := bbase (se 3 (by rfl) ⟨122657, by rfl⟩ : syracuseStep 654173 = 245315) (by norm_num)
theorem B326497 : Blo 287828 326497 := bbase (se 2 (by rfl) ⟨122436, by rfl⟩ : syracuseStep 326497 = 244873) (by norm_num)
theorem B523109 : Blo 287828 523109 := bbase (se 4 (by rfl) ⟨49041, by rfl⟩ : syracuseStep 523109 = 98083) (by norm_num)
theorem B326533 : Blo 287828 326533 := bbase (se 4 (by rfl) ⟨30612, by rfl⟩ : syracuseStep 326533 = 61225) (by norm_num)
theorem B654245 : Blo 287828 654245 := bbase (se 4 (by rfl) ⟨61335, by rfl⟩ : syracuseStep 654245 = 122671) (by norm_num)
theorem B326569 : Blo 287828 326569 := bbase (se 2 (by rfl) ⟨122463, by rfl⟩ : syracuseStep 326569 = 244927) (by norm_num)
theorem B523189 : Blo 287828 523189 := bbase (se 5 (by rfl) ⟨24524, by rfl⟩ : syracuseStep 523189 = 49049) (by norm_num)
theorem B490421 : Blo 287828 490421 := bbase (se 5 (by rfl) ⟨22988, by rfl⟩ : syracuseStep 490421 = 45977) (by norm_num)
theorem B326605 : Blo 287828 326605 := bbase (se 3 (by rfl) ⟨61238, by rfl⟩ : syracuseStep 326605 = 122477) (by norm_num)
theorem B981989 : Blo 287828 981989 := bbase (se 4 (by rfl) ⟨92061, by rfl⟩ : syracuseStep 981989 = 184123) (by norm_num)
theorem B654317 : Blo 287828 654317 := bbase (se 3 (by rfl) ⟨122684, by rfl⟩ : syracuseStep 654317 = 245369) (by norm_num)
theorem B326641 : Blo 287828 326641 := bbase (se 2 (by rfl) ⟨122490, by rfl⟩ : syracuseStep 326641 = 244981) (by norm_num)
theorem B293905 : Blo 287828 293905 := bbase (se 2 (by rfl) ⟨110214, by rfl⟩ : syracuseStep 293905 = 220429) (by norm_num)
theorem B326677 : Blo 287828 326677 := bbase (se 6 (by rfl) ⟨7656, by rfl⟩ : syracuseStep 326677 = 15313) (by norm_num)
theorem B293917 : Blo 287828 293917 := bbase (se 3 (by rfl) ⟨55109, by rfl⟩ : syracuseStep 293917 = 110219) (by norm_num)
theorem B490549 : Blo 287828 490549 := bbase (se 5 (by rfl) ⟨22994, by rfl⟩ : syracuseStep 490549 = 45989) (by norm_num)
theorem B654389 : Blo 287828 654389 := bbase (se 5 (by rfl) ⟨30674, by rfl⟩ : syracuseStep 654389 = 61349) (by norm_num)
theorem B326713 : Blo 287828 326713 := bbase (se 2 (by rfl) ⟨122517, by rfl⟩ : syracuseStep 326713 = 245035) (by norm_num)
theorem B326749 : Blo 287828 326749 := bbase (se 3 (by rfl) ⟨61265, by rfl⟩ : syracuseStep 326749 = 122531) (by norm_num)
theorem B654461 : Blo 287828 654461 := bbase (se 3 (by rfl) ⟨122711, by rfl⟩ : syracuseStep 654461 = 245423) (by norm_num)
theorem B326785 : Blo 287828 326785 := bbase (se 2 (by rfl) ⟨122544, by rfl⟩ : syracuseStep 326785 = 245089) (by norm_num)
theorem B490637 : Blo 287828 490637 := bbase (se 3 (by rfl) ⟨91994, by rfl⟩ : syracuseStep 490637 = 183989) (by norm_num)
theorem B326821 : Blo 287828 326821 := bbase (se 4 (by rfl) ⟨30639, by rfl⟩ : syracuseStep 326821 = 61279) (by norm_num)
theorem B654533 : Blo 287828 654533 := bbase (se 4 (by rfl) ⟨61362, by rfl⟩ : syracuseStep 654533 = 122725) (by norm_num)
theorem B326857 : Blo 287828 326857 := bbase (se 2 (by rfl) ⟨122571, by rfl⟩ : syracuseStep 326857 = 245143) (by norm_num)
theorem B326893 : Blo 287828 326893 := bbase (se 3 (by rfl) ⟨61292, by rfl⟩ : syracuseStep 326893 = 122585) (by norm_num)
theorem B654605 : Blo 287828 654605 := bbase (se 3 (by rfl) ⟨122738, by rfl⟩ : syracuseStep 654605 = 245477) (by norm_num)
theorem B490765 : Blo 287828 490765 := bbase (se 3 (by rfl) ⟨92018, by rfl⟩ : syracuseStep 490765 = 184037) (by norm_num)
theorem B326929 : Blo 287828 326929 := bbase (se 2 (by rfl) ⟨122598, by rfl⟩ : syracuseStep 326929 = 245197) (by norm_num)
theorem B326965 : Blo 287828 326965 := bbase (se 5 (by rfl) ⟨15326, by rfl⟩ : syracuseStep 326965 = 30653) (by norm_num)
theorem B654677 : Blo 287828 654677 := bbase (se 11 (by rfl) ⟨479, by rfl⟩ : syracuseStep 654677 = 959) (by norm_num)
theorem B327001 : Blo 287828 327001 := bbase (se 2 (by rfl) ⟨122625, by rfl⟩ : syracuseStep 327001 = 245251) (by norm_num)
theorem B490853 : Blo 287828 490853 := bbase (se 4 (by rfl) ⟨46017, by rfl⟩ : syracuseStep 490853 = 92035) (by norm_num)
theorem B294265 : Blo 287828 294265 := bbase (se 2 (by rfl) ⟨110349, by rfl⟩ : syracuseStep 294265 = 220699) (by norm_num)
theorem B327037 : Blo 287828 327037 := bbase (se 3 (by rfl) ⟨61319, by rfl⟩ : syracuseStep 327037 = 122639) (by norm_num)
theorem B982421 : Blo 287828 982421 := bbase (se 6 (by rfl) ⟨23025, by rfl⟩ : syracuseStep 982421 = 46051) (by norm_num)
theorem B654749 : Blo 287828 654749 := bbase (se 3 (by rfl) ⟨122765, by rfl⟩ : syracuseStep 654749 = 245531) (by norm_num)
theorem B327073 : Blo 287828 327073 := bbase (se 2 (by rfl) ⟨122652, by rfl⟩ : syracuseStep 327073 = 245305) (by norm_num)
theorem B621989 : Blo 287828 621989 := bbase (se 4 (by rfl) ⟨58311, by rfl⟩ : syracuseStep 621989 = 116623) (by norm_num)
theorem B327109 : Blo 287828 327109 := bbase (se 4 (by rfl) ⟨30666, by rfl⟩ : syracuseStep 327109 = 61333) (by norm_num)
theorem B490981 : Blo 287828 490981 := bbase (se 4 (by rfl) ⟨46029, by rfl⟩ : syracuseStep 490981 = 92059) (by norm_num)
theorem B654821 : Blo 287828 654821 := bbase (se 4 (by rfl) ⟨61389, by rfl⟩ : syracuseStep 654821 = 122779) (by norm_num)
theorem B327145 : Blo 287828 327145 := bbase (se 2 (by rfl) ⟨122679, by rfl⟩ : syracuseStep 327145 = 245359) (by norm_num)
theorem B359921 : Blo 287828 359921 := bbase (se 2 (by rfl) ⟨134970, by rfl⟩ : syracuseStep 359921 = 269941) (by norm_num)
theorem B1474037 : Blo 287828 1474037 := bbase (se 5 (by rfl) ⟨69095, by rfl⟩ : syracuseStep 1474037 = 138191) (by norm_num)
theorem B327181 : Blo 287828 327181 := bbase (se 3 (by rfl) ⟨61346, by rfl⟩ : syracuseStep 327181 = 122693) (by norm_num)
theorem B654893 : Blo 287828 654893 := bbase (se 3 (by rfl) ⟨122792, by rfl⟩ : syracuseStep 654893 = 245585) (by norm_num)
theorem B327217 : Blo 287828 327217 := bbase (se 2 (by rfl) ⟨122706, by rfl⟩ : syracuseStep 327217 = 245413) (by norm_num)
theorem B491069 : Blo 287828 491069 := bbase (se 3 (by rfl) ⟨92075, by rfl⟩ : syracuseStep 491069 = 184151) (by norm_num)
theorem B327253 : Blo 287828 327253 := bbase (se 8 (by rfl) ⟨1917, by rfl⟩ : syracuseStep 327253 = 3835) (by norm_num)
theorem B654965 : Blo 287828 654965 := bbase (se 5 (by rfl) ⟨30701, by rfl⟩ : syracuseStep 654965 = 61403) (by norm_num)
theorem B327289 : Blo 287828 327289 := bbase (se 2 (by rfl) ⟨122733, by rfl⟩ : syracuseStep 327289 = 245467) (by norm_num)
theorem B327325 : Blo 287828 327325 := bbase (se 3 (by rfl) ⟨61373, by rfl⟩ : syracuseStep 327325 = 122747) (by norm_num)
theorem B491197 : Blo 287828 491197 := bbase (se 3 (by rfl) ⟨92099, by rfl⟩ : syracuseStep 491197 = 184199) (by norm_num)
theorem B655037 : Blo 287828 655037 := bbase (se 3 (by rfl) ⟨122819, by rfl⟩ : syracuseStep 655037 = 245639) (by norm_num)
theorem B327361 : Blo 287828 327361 := bbase (se 2 (by rfl) ⟨122760, by rfl⟩ : syracuseStep 327361 = 245521) (by norm_num)
theorem B327397 : Blo 287828 327397 := bbase (se 4 (by rfl) ⟨30693, by rfl⟩ : syracuseStep 327397 = 61387) (by norm_num)
theorem B655109 : Blo 287828 655109 := bbase (se 4 (by rfl) ⟨61416, by rfl⟩ : syracuseStep 655109 = 122833) (by norm_num)
theorem B327433 : Blo 287828 327433 := bbase (se 2 (by rfl) ⟨122787, by rfl⟩ : syracuseStep 327433 = 245575) (by norm_num)
theorem B491285 : Blo 287828 491285 := bbase (se 6 (by rfl) ⟨11514, by rfl⟩ : syracuseStep 491285 = 23029) (by norm_num)
theorem B327469 : Blo 287828 327469 := bbase (se 3 (by rfl) ⟨61400, by rfl⟩ : syracuseStep 327469 = 122801) (by norm_num)
theorem B982853 : Blo 287828 982853 := bbase (se 4 (by rfl) ⟨92142, by rfl⟩ : syracuseStep 982853 = 184285) (by norm_num)
theorem B655181 : Blo 287828 655181 := bbase (se 3 (by rfl) ⟨122846, by rfl⟩ : syracuseStep 655181 = 245693) (by norm_num)
theorem B327505 : Blo 287828 327505 := bbase (se 2 (by rfl) ⟨122814, by rfl⟩ : syracuseStep 327505 = 245629) (by norm_num)
theorem B1408853 : Blo 287828 1408853 := bbase (se 9 (by rfl) ⟨4127, by rfl⟩ : syracuseStep 1408853 = 8255) (by norm_num)
theorem B327541 : Blo 287828 327541 := bbase (se 5 (by rfl) ⟨15353, by rfl⟩ : syracuseStep 327541 = 30707) (by norm_num)
theorem B491413 : Blo 287828 491413 := bbase (se 6 (by rfl) ⟨11517, by rfl⟩ : syracuseStep 491413 = 23035) (by norm_num)
theorem B655253 : Blo 287828 655253 := bbase (se 6 (by rfl) ⟨15357, by rfl⟩ : syracuseStep 655253 = 30715) (by norm_num)
theorem B327577 : Blo 287828 327577 := bbase (se 2 (by rfl) ⟨122841, by rfl⟩ : syracuseStep 327577 = 245683) (by norm_num)
theorem B786341 : Blo 287828 786341 := bbase (se 4 (by rfl) ⟨73719, by rfl⟩ : syracuseStep 786341 = 147439) (by norm_num)
theorem B327613 : Blo 287828 327613 := bbase (se 3 (by rfl) ⟨61427, by rfl⟩ : syracuseStep 327613 = 122855) (by norm_num)
theorem B884693 : Blo 287828 884693 := bbase (se 7 (by rfl) ⟨10367, by rfl⟩ : syracuseStep 884693 = 20735) (by norm_num)
theorem B655325 : Blo 287828 655325 := bbase (se 3 (by rfl) ⟨122873, by rfl⟩ : syracuseStep 655325 = 245747) (by norm_num)
theorem B327649 : Blo 287828 327649 := bbase (se 2 (by rfl) ⟨122868, by rfl⟩ : syracuseStep 327649 = 245737) (by norm_num)
theorem B491501 : Blo 287828 491501 := bbase (se 3 (by rfl) ⟨92156, by rfl⟩ : syracuseStep 491501 = 184313) (by norm_num)
theorem B491521 : Blo 287828 491521 := bstep (se 2 (by rfl) ⟨184320, by rfl⟩ : syracuseStep 491521 = 368641) B368641
theorem B491555 : Blo 287828 491555 := bstep (se 1 (by rfl) ⟨368666, by rfl⟩ : syracuseStep 491555 = 737333) B737333
theorem B327811 : Blo 287828 327811 := bstep (se 1 (by rfl) ⟨245858, by rfl⟩ : syracuseStep 327811 = 491717) B491717
theorem B655505 : Blo 287828 655505 := bstep (se 2 (by rfl) ⟨245814, by rfl⟩ : syracuseStep 655505 = 491629) B491629
theorem B655523 : Blo 287828 655523 := bstep (se 1 (by rfl) ⟨491642, by rfl⟩ : syracuseStep 655523 = 983285) B983285
theorem B491683 : Blo 287828 491683 := bstep (se 1 (by rfl) ⟨368762, by rfl⟩ : syracuseStep 491683 = 737525) B737525
theorem B524465 : Blo 287828 524465 := bstep (se 2 (by rfl) ⟨196674, by rfl⟩ : syracuseStep 524465 = 393349) B393349
theorem B40337621 : Blo 287828 40337621 := bstep (se 7 (by rfl) ⟨472706, by rfl⟩ : syracuseStep 40337621 = 945413) B945413
theorem B1573091 : Blo 287828 1573091 := bstep (se 1 (by rfl) ⟨1179818, by rfl⟩ : syracuseStep 1573091 = 2359637) B2359637
theorem B1179917 : Blo 287828 1179917 := bstep (se 3 (by rfl) ⟨221234, by rfl⟩ : syracuseStep 1179917 = 442469) B442469
theorem B327955 : Blo 287828 327955 := bstep (se 1 (by rfl) ⟨245966, by rfl⟩ : syracuseStep 327955 = 491933) B491933
theorem B491825 : Blo 287828 491825 := bstep (se 2 (by rfl) ⟨184434, by rfl⟩ : syracuseStep 491825 = 368869) B368869
theorem B328099 : Blo 287828 328099 := bstep (se 1 (by rfl) ⟨246074, by rfl⟩ : syracuseStep 328099 = 492149) B492149
theorem B655793 : Blo 287828 655793 := bstep (se 2 (by rfl) ⟨245922, by rfl⟩ : syracuseStep 655793 = 491845) B491845
theorem B491953 : Blo 287828 491953 := bstep (se 2 (by rfl) ⟨184482, by rfl⟩ : syracuseStep 491953 = 368965) B368965
theorem B655811 : Blo 287828 655811 := bstep (se 1 (by rfl) ⟨491858, by rfl⟩ : syracuseStep 655811 = 983717) B983717
theorem B1180109 : Blo 287828 1180109 := bstep (se 3 (by rfl) ⟨221270, by rfl⟩ : syracuseStep 1180109 = 442541) B442541
theorem B983501 : Blo 287828 983501 := bstep (se 3 (by rfl) ⟨184406, by rfl⟩ : syracuseStep 983501 = 368813) B368813
theorem B491987 : Blo 287828 491987 := bstep (se 1 (by rfl) ⟨368990, by rfl⟩ : syracuseStep 491987 = 737981) B737981
theorem B4194787 : Blo 287828 4194787 := bstep (se 1 (by rfl) ⟨3146090, by rfl⟩ : syracuseStep 4194787 = 6292181) B6292181
theorem B819715 : Blo 287828 819715 := bstep (se 1 (by rfl) ⟨614786, by rfl⟩ : syracuseStep 819715 = 1229573) B1229573
theorem B983555 : Blo 287828 983555 := bstep (se 1 (by rfl) ⟨737666, by rfl⟩ : syracuseStep 983555 = 1475333) B1475333
theorem B328243 : Blo 287828 328243 := bstep (se 1 (by rfl) ⟨246182, by rfl⟩ : syracuseStep 328243 = 492365) B492365
theorem B492115 : Blo 287828 492115 := bstep (se 1 (by rfl) ⟨369086, by rfl⟩ : syracuseStep 492115 = 738173) B738173
theorem B1475171 : Blo 287828 1475171 := bstep (se 1 (by rfl) ⟨1106378, by rfl⟩ : syracuseStep 1475171 = 2212757) B2212757
theorem B819875 : Blo 287828 819875 := bstep (se 1 (by rfl) ⟨614906, by rfl⟩ : syracuseStep 819875 = 1229813) B1229813
theorem B656081 : Blo 287828 656081 := bstep (se 2 (by rfl) ⟨246030, by rfl⟩ : syracuseStep 656081 = 492061) B492061
theorem B492257 : Blo 287828 492257 := bstep (se 2 (by rfl) ⟨184596, by rfl⟩ : syracuseStep 492257 = 369193) B369193
theorem B656099 : Blo 287828 656099 := bstep (se 1 (by rfl) ⟨492074, by rfl⟩ : syracuseStep 656099 = 984149) B984149
theorem B3113741 : Blo 287828 3113741 := bstep (se 3 (by rfl) ⟨583826, by rfl⟩ : syracuseStep 3113741 = 1167653) B1167653
theorem B983825 : Blo 287828 983825 := bstep (se 2 (by rfl) ⟨368934, by rfl⟩ : syracuseStep 983825 = 737869) B737869
theorem B492385 : Blo 287828 492385 := bstep (se 2 (by rfl) ⟨184644, by rfl⟩ : syracuseStep 492385 = 369289) B369289
theorem B2786147 : Blo 287828 2786147 := bstep (se 1 (by rfl) ⟨2089610, by rfl⟩ : syracuseStep 2786147 = 4179221) B4179221
theorem B2491235 : Blo 287828 2491235 := bstep (se 1 (by rfl) ⟨1868426, by rfl⟩ : syracuseStep 2491235 = 3736853) B3736853
theorem B492419 : Blo 287828 492419 := bstep (se 1 (by rfl) ⟨369314, by rfl⟩ : syracuseStep 492419 = 738629) B738629
theorem B1573829 : Blo 287828 1573829 := bstep (se 4 (by rfl) ⟨147546, by rfl⟩ : syracuseStep 1573829 = 295093) B295093
theorem B656369 : Blo 287828 656369 := bstep (se 2 (by rfl) ⟨246138, by rfl⟩ : syracuseStep 656369 = 492277) B492277
theorem B656387 : Blo 287828 656387 := bstep (se 1 (by rfl) ⟨492290, by rfl⟩ : syracuseStep 656387 = 984581) B984581
theorem B984365 : Blo 287828 984365 := bstep (se 3 (by rfl) ⟨184568, by rfl⟩ : syracuseStep 984365 = 369137) B369137
theorem B492851 : Blo 287828 492851 := bstep (se 1 (by rfl) ⟨369638, by rfl⟩ : syracuseStep 492851 = 739277) B739277
theorem B984419 : Blo 287828 984419 := bstep (se 1 (by rfl) ⟨738314, by rfl⟩ : syracuseStep 984419 = 1476629) B1476629
theorem B1475981 : Blo 287828 1475981 := bstep (se 3 (by rfl) ⟨276746, by rfl⟩ : syracuseStep 1475981 = 553493) B553493
theorem B787907 : Blo 287828 787907 := bstep (se 1 (by rfl) ⟨590930, by rfl⟩ : syracuseStep 787907 = 1181861) B1181861
theorem B1639885 : Blo 287828 1639885 := bstep (se 3 (by rfl) ⟨307478, by rfl⟩ : syracuseStep 1639885 = 614957) B614957
theorem B1050083 : Blo 287828 1050083 := bstep (se 1 (by rfl) ⟨787562, by rfl⟩ : syracuseStep 1050083 = 1575125) B1575125
theorem B3311117 : Blo 287828 3311117 := bstep (se 3 (by rfl) ⟨620834, by rfl⟩ : syracuseStep 3311117 = 1241669) B1241669
theorem B886385 : Blo 287828 886385 := bstep (se 2 (by rfl) ⟨332394, by rfl⟩ : syracuseStep 886385 = 664789) B664789
theorem B984689 : Blo 287828 984689 := bstep (se 2 (by rfl) ⟨369258, by rfl⟩ : syracuseStep 984689 = 738517) B738517
theorem B1869475 : Blo 287828 1869475 := bstep (se 1 (by rfl) ⟨1402106, by rfl⟩ : syracuseStep 1869475 = 2804213) B2804213
theorem B493249 : Blo 287828 493249 := bstep (se 2 (by rfl) ⟨184968, by rfl⟩ : syracuseStep 493249 = 369937) B369937
theorem B820945 : Blo 287828 820945 := bstep (se 2 (by rfl) ⟨307854, by rfl⟩ : syracuseStep 820945 = 615709) B615709
theorem B493427 : Blo 287828 493427 := bstep (se 1 (by rfl) ⟨370070, by rfl⟩ : syracuseStep 493427 = 740141) B740141
theorem B526417 : Blo 287828 526417 := bstep (se 2 (by rfl) ⟨197406, by rfl⟩ : syracuseStep 526417 = 394813) B394813
theorem B461315 : Blo 287828 461315 := bstep (se 1 (by rfl) ⟨345986, by rfl⟩ : syracuseStep 461315 = 691973) B691973
theorem B1575557 : Blo 287828 1575557 := bstep (se 4 (by rfl) ⟨147708, by rfl⟩ : syracuseStep 1575557 = 295417) B295417
theorem B822221 : Blo 287828 822221 := bstep (se 3 (by rfl) ⟨154166, by rfl⟩ : syracuseStep 822221 = 308333) B308333
theorem B1051697 : Blo 287828 1051697 := bstep (se 2 (by rfl) ⟨394386, by rfl⟩ : syracuseStep 1051697 = 788773) B788773
theorem B822403 : Blo 287828 822403 := bstep (se 1 (by rfl) ⟨616802, by rfl⟩ : syracuseStep 822403 = 1233605) B1233605
theorem B822449 : Blo 287828 822449 := bstep (se 2 (by rfl) ⟨308418, by rfl⟩ : syracuseStep 822449 = 616837) B616837
theorem B2985187 : Blo 287828 2985187 := bstep (se 1 (by rfl) ⟨2238890, by rfl⟩ : syracuseStep 2985187 = 4477781) B4477781
theorem B1576205 : Blo 287828 1576205 := bstep (se 3 (by rfl) ⟨295538, by rfl⟩ : syracuseStep 1576205 = 591077) B591077
theorem B462115 : Blo 287828 462115 := bstep (se 1 (by rfl) ⟨346586, by rfl⟩ : syracuseStep 462115 = 693173) B693173
theorem B1641869 : Blo 287828 1641869 := bstep (se 3 (by rfl) ⟨307850, by rfl⟩ : syracuseStep 1641869 = 615701) B615701
theorem B462257 : Blo 287828 462257 := bstep (se 2 (by rfl) ⟨173346, by rfl⟩ : syracuseStep 462257 = 346693) B346693
theorem B462289 : Blo 287828 462289 := bstep (se 2 (by rfl) ⟨173358, by rfl⟩ : syracuseStep 462289 = 346717) B346717
theorem B658979 : Blo 287828 658979 := bstep (se 1 (by rfl) ⟨494234, by rfl⟩ : syracuseStep 658979 = 988469) B988469
theorem B626257 : Blo 287828 626257 := bstep (se 2 (by rfl) ⟨234846, by rfl⟩ : syracuseStep 626257 = 469693) B469693
theorem B659171 : Blo 287828 659171 := bstep (se 1 (by rfl) ⟨494378, by rfl⟩ : syracuseStep 659171 = 988757) B988757
theorem B1412963 : Blo 287828 1412963 := bstep (se 1 (by rfl) ⟨1059722, by rfl⟩ : syracuseStep 1412963 = 2119445) B2119445
theorem B364819 : Blo 287828 364819 := bstep (se 1 (by rfl) ⟨273614, by rfl⟩ : syracuseStep 364819 = 547229) B547229
theorem B1642801 : Blo 287828 1642801 := bstep (se 2 (by rfl) ⟨616050, by rfl⟩ : syracuseStep 1642801 = 1232101) B1232101
theorem B856433 : Blo 287828 856433 := bstep (se 2 (by rfl) ⟨321162, by rfl⟩ : syracuseStep 856433 = 642325) B642325
theorem B463217 : Blo 287828 463217 := bstep (se 2 (by rfl) ⟨173706, by rfl⟩ : syracuseStep 463217 = 347413) B347413
theorem B364915 : Blo 287828 364915 := bstep (se 1 (by rfl) ⟨273686, by rfl⟩ : syracuseStep 364915 = 547373) B547373
theorem B3314033 : Blo 287828 3314033 := bstep (se 2 (by rfl) ⟨1242762, by rfl⟩ : syracuseStep 3314033 = 2485525) B2485525
theorem B1315277 : Blo 287828 1315277 := bstep (se 3 (by rfl) ⟨246614, by rfl⟩ : syracuseStep 1315277 = 493229) B493229
theorem B496129 : Blo 287828 496129 := bstep (se 2 (by rfl) ⟨186048, by rfl⟩ : syracuseStep 496129 = 372097) B372097
theorem B823907 : Blo 287828 823907 := bstep (se 1 (by rfl) ⟨617930, by rfl⟩ : syracuseStep 823907 = 1235861) B1235861
theorem B332435 : Blo 287828 332435 := bstep (se 1 (by rfl) ⟨249326, by rfl⟩ : syracuseStep 332435 = 498653) B498653
theorem B365411 : Blo 287828 365411 := bstep (se 1 (by rfl) ⟨274058, by rfl⟩ : syracuseStep 365411 = 548117) B548117
theorem B1905677 : Blo 287828 1905677 := bstep (se 3 (by rfl) ⟨357314, by rfl⟩ : syracuseStep 1905677 = 714629) B714629
theorem B464051 : Blo 287828 464051 := bstep (se 1 (by rfl) ⟨348038, by rfl⟩ : syracuseStep 464051 = 696077) B696077
theorem B464339 : Blo 287828 464339 := bstep (se 1 (by rfl) ⟨348254, by rfl⟩ : syracuseStep 464339 = 696509) B696509
theorem B366115 : Blo 287828 366115 := bstep (se 1 (by rfl) ⟨274586, by rfl⟩ : syracuseStep 366115 = 549173) B549173
theorem B431747 : Blo 287828 431747 := bstep (se 1 (by rfl) ⟨323810, by rfl⟩ : syracuseStep 431747 = 647621) B647621
theorem B366211 : Blo 287828 366211 := bstep (se 1 (by rfl) ⟨274658, by rfl⟩ : syracuseStep 366211 = 549317) B549317
theorem B431777 : Blo 287828 431777 := bstep (se 2 (by rfl) ⟨161916, by rfl⟩ : syracuseStep 431777 = 323833) B323833
theorem B923309 : Blo 287828 923309 := bstep (se 3 (by rfl) ⟨173120, by rfl⟩ : syracuseStep 923309 = 346241) B346241
theorem B431795 : Blo 287828 431795 := bstep (se 1 (by rfl) ⟨323846, by rfl⟩ : syracuseStep 431795 = 647693) B647693
theorem B464563 : Blo 287828 464563 := bstep (se 1 (by rfl) ⟨348422, by rfl⟩ : syracuseStep 464563 = 696845) B696845
theorem B431825 : Blo 287828 431825 := bstep (se 2 (by rfl) ⟨161934, by rfl⟩ : syracuseStep 431825 = 323869) B323869
theorem B431843 : Blo 287828 431843 := bstep (se 1 (by rfl) ⟨323882, by rfl⟩ : syracuseStep 431843 = 647765) B647765
theorem B1644259 : Blo 287828 1644259 := bstep (se 1 (by rfl) ⟨1233194, by rfl⟩ : syracuseStep 1644259 = 2466389) B2466389
theorem B694001 : Blo 287828 694001 := bstep (se 2 (by rfl) ⟨260250, by rfl⟩ : syracuseStep 694001 = 520501) B520501
theorem B431873 : Blo 287828 431873 := bstep (se 2 (by rfl) ⟨161952, by rfl⟩ : syracuseStep 431873 = 323905) B323905
theorem B431891 : Blo 287828 431891 := bstep (se 1 (by rfl) ⟨323918, by rfl⟩ : syracuseStep 431891 = 647837) B647837
theorem B431921 : Blo 287828 431921 := bstep (se 2 (by rfl) ⟨161970, by rfl⟩ : syracuseStep 431921 = 323941) B323941
theorem B825137 : Blo 287828 825137 := bstep (se 2 (by rfl) ⟨309426, by rfl⟩ : syracuseStep 825137 = 618853) B618853
theorem B431939 : Blo 287828 431939 := bstep (se 1 (by rfl) ⟨323954, by rfl⟩ : syracuseStep 431939 = 647909) B647909
theorem B431969 : Blo 287828 431969 := bstep (se 2 (by rfl) ⟨161988, by rfl⟩ : syracuseStep 431969 = 323977) B323977
theorem B431987 : Blo 287828 431987 := bstep (se 1 (by rfl) ⟨323990, by rfl⟩ : syracuseStep 431987 = 647981) B647981
theorem B432017 : Blo 287828 432017 := bstep (se 2 (by rfl) ⟨162006, by rfl⟩ : syracuseStep 432017 = 324013) B324013
theorem B432035 : Blo 287828 432035 := bstep (se 1 (by rfl) ⟨324026, by rfl⟩ : syracuseStep 432035 = 648053) B648053
theorem B432065 : Blo 287828 432065 := bstep (se 2 (by rfl) ⟨162024, by rfl⟩ : syracuseStep 432065 = 324049) B324049
theorem B432083 : Blo 287828 432083 := bstep (se 1 (by rfl) ⟨324062, by rfl⟩ : syracuseStep 432083 = 648125) B648125
theorem B432113 : Blo 287828 432113 := bstep (se 2 (by rfl) ⟨162042, by rfl⟩ : syracuseStep 432113 = 324085) B324085
theorem B432131 : Blo 287828 432131 := bstep (se 1 (by rfl) ⟨324098, by rfl⟩ : syracuseStep 432131 = 648197) B648197
theorem B432161 : Blo 287828 432161 := bstep (se 2 (by rfl) ⟨162060, by rfl⟩ : syracuseStep 432161 = 324121) B324121
theorem B432179 : Blo 287828 432179 := bstep (se 1 (by rfl) ⟨324134, by rfl⟩ : syracuseStep 432179 = 648269) B648269
theorem B432209 : Blo 287828 432209 := bstep (se 2 (by rfl) ⟨162078, by rfl⟩ : syracuseStep 432209 = 324157) B324157
theorem B432227 : Blo 287828 432227 := bstep (se 1 (by rfl) ⟨324170, by rfl⟩ : syracuseStep 432227 = 648341) B648341
theorem B694385 : Blo 287828 694385 := bstep (se 2 (by rfl) ⟨260394, by rfl⟩ : syracuseStep 694385 = 520789) B520789
theorem B366707 : Blo 287828 366707 := bstep (se 1 (by rfl) ⟨275030, by rfl⟩ : syracuseStep 366707 = 550061) B550061
theorem B432257 : Blo 287828 432257 := bstep (se 2 (by rfl) ⟨162096, by rfl⟩ : syracuseStep 432257 = 324193) B324193
theorem B530563 : Blo 287828 530563 := bstep (se 1 (by rfl) ⟨397922, by rfl⟩ : syracuseStep 530563 = 795845) B795845
theorem B432275 : Blo 287828 432275 := bstep (se 1 (by rfl) ⟨324206, by rfl⟩ : syracuseStep 432275 = 648413) B648413
theorem B432305 : Blo 287828 432305 := bstep (se 2 (by rfl) ⟨162114, by rfl⟩ : syracuseStep 432305 = 324229) B324229
theorem B432323 : Blo 287828 432323 := bstep (se 1 (by rfl) ⟨324242, by rfl⟩ : syracuseStep 432323 = 648485) B648485
theorem B432353 : Blo 287828 432353 := bstep (se 2 (by rfl) ⟨162132, by rfl⟩ : syracuseStep 432353 = 324265) B324265
theorem B1644785 : Blo 287828 1644785 := bstep (se 2 (by rfl) ⟨616794, by rfl⟩ : syracuseStep 1644785 = 1233589) B1233589
theorem B432371 : Blo 287828 432371 := bstep (se 1 (by rfl) ⟨324278, by rfl⟩ : syracuseStep 432371 = 648557) B648557
theorem B432401 : Blo 287828 432401 := bstep (se 2 (by rfl) ⟨162150, by rfl⟩ : syracuseStep 432401 = 324301) B324301
theorem B432419 : Blo 287828 432419 := bstep (se 1 (by rfl) ⟨324314, by rfl⟩ : syracuseStep 432419 = 648629) B648629
theorem B432449 : Blo 287828 432449 := bstep (se 2 (by rfl) ⟨162168, by rfl⟩ : syracuseStep 432449 = 324337) B324337
theorem B694595 : Blo 287828 694595 := bstep (se 1 (by rfl) ⟨520946, by rfl⟩ : syracuseStep 694595 = 1041893) B1041893
theorem B432467 : Blo 287828 432467 := bstep (se 1 (by rfl) ⟨324350, by rfl⟩ : syracuseStep 432467 = 648701) B648701
theorem B432497 : Blo 287828 432497 := bstep (se 2 (by rfl) ⟨162186, by rfl⟩ : syracuseStep 432497 = 324373) B324373
theorem B465281 : Blo 287828 465281 := bstep (se 2 (by rfl) ⟨174480, by rfl⟩ : syracuseStep 465281 = 348961) B348961
theorem B432515 : Blo 287828 432515 := bstep (se 1 (by rfl) ⟨324386, by rfl⟩ : syracuseStep 432515 = 648773) B648773
theorem B432545 : Blo 287828 432545 := bstep (se 2 (by rfl) ⟨162204, by rfl⟩ : syracuseStep 432545 = 324409) B324409
theorem B432563 : Blo 287828 432563 := bstep (se 1 (by rfl) ⟨324422, by rfl⟩ : syracuseStep 432563 = 648845) B648845
theorem B432593 : Blo 287828 432593 := bstep (se 2 (by rfl) ⟨162222, by rfl⟩ : syracuseStep 432593 = 324445) B324445
theorem B432611 : Blo 287828 432611 := bstep (se 1 (by rfl) ⟨324458, by rfl⟩ : syracuseStep 432611 = 648917) B648917
theorem B432641 : Blo 287828 432641 := bstep (se 2 (by rfl) ⟨162240, by rfl⟩ : syracuseStep 432641 = 324481) B324481
theorem B432659 : Blo 287828 432659 := bstep (se 1 (by rfl) ⟨324494, by rfl⟩ : syracuseStep 432659 = 648989) B648989
theorem B924205 : Blo 287828 924205 := bstep (se 3 (by rfl) ⟨173288, by rfl⟩ : syracuseStep 924205 = 346577) B346577
theorem B432689 : Blo 287828 432689 := bstep (se 2 (by rfl) ⟨162258, by rfl⟩ : syracuseStep 432689 = 324517) B324517
theorem B465473 : Blo 287828 465473 := bstep (se 2 (by rfl) ⟨174552, by rfl⟩ : syracuseStep 465473 = 349105) B349105
theorem B432707 : Blo 287828 432707 := bstep (se 1 (by rfl) ⟨324530, by rfl⟩ : syracuseStep 432707 = 649061) B649061
theorem B432737 : Blo 287828 432737 := bstep (se 2 (by rfl) ⟨162276, by rfl⟩ : syracuseStep 432737 = 324553) B324553
theorem B432755 : Blo 287828 432755 := bstep (se 1 (by rfl) ⟨324566, by rfl⟩ : syracuseStep 432755 = 649133) B649133
theorem B432785 : Blo 287828 432785 := bstep (se 2 (by rfl) ⟨162294, by rfl⟩ : syracuseStep 432785 = 324589) B324589
theorem B432803 : Blo 287828 432803 := bstep (se 1 (by rfl) ⟨324602, by rfl⟩ : syracuseStep 432803 = 649205) B649205
theorem B432833 : Blo 287828 432833 := bstep (se 2 (by rfl) ⟨162312, by rfl⟩ : syracuseStep 432833 = 324625) B324625
theorem B465601 : Blo 287828 465601 := bstep (se 2 (by rfl) ⟨174600, by rfl⟩ : syracuseStep 465601 = 349201) B349201
theorem B432851 : Blo 287828 432851 := bstep (se 1 (by rfl) ⟨324638, by rfl⟩ : syracuseStep 432851 = 649277) B649277
theorem B432881 : Blo 287828 432881 := bstep (se 2 (by rfl) ⟨162330, by rfl⟩ : syracuseStep 432881 = 324661) B324661
theorem B432899 : Blo 287828 432899 := bstep (se 1 (by rfl) ⟨324674, by rfl⟩ : syracuseStep 432899 = 649349) B649349
theorem B432929 : Blo 287828 432929 := bstep (se 2 (by rfl) ⟨162348, by rfl⟩ : syracuseStep 432929 = 324697) B324697
theorem B432947 : Blo 287828 432947 := bstep (se 1 (by rfl) ⟨324710, by rfl⟩ : syracuseStep 432947 = 649421) B649421
theorem B367411 : Blo 287828 367411 := bstep (se 1 (by rfl) ⟨275558, by rfl⟩ : syracuseStep 367411 = 551117) B551117
theorem B432977 : Blo 287828 432977 := bstep (se 2 (by rfl) ⟨162366, by rfl⟩ : syracuseStep 432977 = 324733) B324733
theorem B432995 : Blo 287828 432995 := bstep (se 1 (by rfl) ⟨324746, by rfl⟩ : syracuseStep 432995 = 649493) B649493
theorem B433025 : Blo 287828 433025 := bstep (se 2 (by rfl) ⟨162384, by rfl⟩ : syracuseStep 433025 = 324769) B324769
theorem B433043 : Blo 287828 433043 := bstep (se 1 (by rfl) ⟨324782, by rfl⟩ : syracuseStep 433043 = 649565) B649565
theorem B367507 : Blo 287828 367507 := bstep (se 1 (by rfl) ⟨275630, by rfl⟩ : syracuseStep 367507 = 551261) B551261
theorem B433073 : Blo 287828 433073 := bstep (se 2 (by rfl) ⟨162402, by rfl⟩ : syracuseStep 433073 = 324805) B324805
theorem B433091 : Blo 287828 433091 := bstep (se 1 (by rfl) ⟨324818, by rfl⟩ : syracuseStep 433091 = 649637) B649637
theorem B433121 : Blo 287828 433121 := bstep (se 2 (by rfl) ⟨162420, by rfl⟩ : syracuseStep 433121 = 324841) B324841
theorem B433139 : Blo 287828 433139 := bstep (se 1 (by rfl) ⟨324854, by rfl⟩ : syracuseStep 433139 = 649709) B649709
theorem B433169 : Blo 287828 433169 := bstep (se 2 (by rfl) ⟨162438, by rfl⟩ : syracuseStep 433169 = 324877) B324877
theorem B433187 : Blo 287828 433187 := bstep (se 1 (by rfl) ⟨324890, by rfl⟩ : syracuseStep 433187 = 649781) B649781
theorem B433217 : Blo 287828 433217 := bstep (se 2 (by rfl) ⟨162456, by rfl⟩ : syracuseStep 433217 = 324913) B324913
theorem B433235 : Blo 287828 433235 := bstep (se 1 (by rfl) ⟨324926, by rfl⟩ : syracuseStep 433235 = 649853) B649853
theorem B662627 : Blo 287828 662627 := bstep (se 1 (by rfl) ⟨496970, by rfl⟩ : syracuseStep 662627 = 993941) B993941
theorem B433265 : Blo 287828 433265 := bstep (se 2 (by rfl) ⟨162474, by rfl⟩ : syracuseStep 433265 = 324949) B324949
theorem B433283 : Blo 287828 433283 := bstep (se 1 (by rfl) ⟨324962, by rfl⟩ : syracuseStep 433283 = 649925) B649925
theorem B695441 : Blo 287828 695441 := bstep (se 2 (by rfl) ⟨260790, by rfl⟩ : syracuseStep 695441 = 521581) B521581
theorem B433313 : Blo 287828 433313 := bstep (se 2 (by rfl) ⟨162492, by rfl⟩ : syracuseStep 433313 = 324985) B324985
theorem B433331 : Blo 287828 433331 := bstep (se 1 (by rfl) ⟨324998, by rfl⟩ : syracuseStep 433331 = 649997) B649997
theorem B433361 : Blo 287828 433361 := bstep (se 2 (by rfl) ⟨162510, by rfl⟩ : syracuseStep 433361 = 325021) B325021
theorem B433379 : Blo 287828 433379 := bstep (se 1 (by rfl) ⟨325034, by rfl⟩ : syracuseStep 433379 = 650069) B650069
theorem B564451 : Blo 287828 564451 := bstep (se 1 (by rfl) ⟨423338, by rfl⟩ : syracuseStep 564451 = 846677) B846677
theorem B826595 : Blo 287828 826595 := bstep (se 1 (by rfl) ⟨619946, by rfl⟩ : syracuseStep 826595 = 1239893) B1239893
theorem B433409 : Blo 287828 433409 := bstep (se 2 (by rfl) ⟨162528, by rfl⟩ : syracuseStep 433409 = 325057) B325057
theorem B433427 : Blo 287828 433427 := bstep (se 1 (by rfl) ⟨325070, by rfl⟩ : syracuseStep 433427 = 650141) B650141
theorem B433457 : Blo 287828 433457 := bstep (se 2 (by rfl) ⟨162546, by rfl⟩ : syracuseStep 433457 = 325093) B325093
theorem B466241 : Blo 287828 466241 := bstep (se 2 (by rfl) ⟨174840, by rfl⟩ : syracuseStep 466241 = 349681) B349681
theorem B433475 : Blo 287828 433475 := bstep (se 1 (by rfl) ⟨325106, by rfl⟩ : syracuseStep 433475 = 650213) B650213
theorem B695633 : Blo 287828 695633 := bstep (se 2 (by rfl) ⟨260862, by rfl⟩ : syracuseStep 695633 = 521725) B521725
theorem B433505 : Blo 287828 433505 := bstep (se 2 (by rfl) ⟨162564, by rfl⟩ : syracuseStep 433505 = 325129) B325129
theorem B433523 : Blo 287828 433523 := bstep (se 1 (by rfl) ⟨325142, by rfl⟩ : syracuseStep 433523 = 650285) B650285
theorem B368003 : Blo 287828 368003 := bstep (se 1 (by rfl) ⟨276002, by rfl⟩ : syracuseStep 368003 = 552005) B552005
theorem B433553 : Blo 287828 433553 := bstep (se 2 (by rfl) ⟨162582, by rfl⟩ : syracuseStep 433553 = 325165) B325165
theorem B335251 : Blo 287828 335251 := bstep (se 1 (by rfl) ⟨251438, by rfl⟩ : syracuseStep 335251 = 502877) B502877
theorem B925091 : Blo 287828 925091 := bstep (se 1 (by rfl) ⟨693818, by rfl⟩ : syracuseStep 925091 = 1387637) B1387637
theorem B433571 : Blo 287828 433571 := bstep (se 1 (by rfl) ⟨325178, by rfl⟩ : syracuseStep 433571 = 650357) B650357
theorem B433601 : Blo 287828 433601 := bstep (se 2 (by rfl) ⟨162600, by rfl⟩ : syracuseStep 433601 = 325201) B325201
theorem B433619 : Blo 287828 433619 := bstep (se 1 (by rfl) ⟨325214, by rfl⟩ : syracuseStep 433619 = 650429) B650429
theorem B433649 : Blo 287828 433649 := bstep (se 2 (by rfl) ⟨162618, by rfl⟩ : syracuseStep 433649 = 325237) B325237
theorem B433667 : Blo 287828 433667 := bstep (se 1 (by rfl) ⟨325250, by rfl⟩ : syracuseStep 433667 = 650501) B650501
theorem B433697 : Blo 287828 433697 := bstep (se 2 (by rfl) ⟨162636, by rfl⟩ : syracuseStep 433697 = 325273) B325273
theorem B433715 : Blo 287828 433715 := bstep (se 1 (by rfl) ⟨325286, by rfl⟩ : syracuseStep 433715 = 650573) B650573
theorem B433745 : Blo 287828 433745 := bstep (se 2 (by rfl) ⟨162654, by rfl⟩ : syracuseStep 433745 = 325309) B325309
theorem B433763 : Blo 287828 433763 := bstep (se 1 (by rfl) ⟨325322, by rfl⟩ : syracuseStep 433763 = 650645) B650645
theorem B433793 : Blo 287828 433793 := bstep (se 2 (by rfl) ⟨162672, by rfl⟩ : syracuseStep 433793 = 325345) B325345
theorem B433811 : Blo 287828 433811 := bstep (se 1 (by rfl) ⟨325358, by rfl⟩ : syracuseStep 433811 = 650717) B650717
theorem B1646243 : Blo 287828 1646243 := bstep (se 1 (by rfl) ⟨1234682, by rfl⟩ : syracuseStep 1646243 = 2469365) B2469365
theorem B433841 : Blo 287828 433841 := bstep (se 2 (by rfl) ⟨162690, by rfl⟩ : syracuseStep 433841 = 325381) B325381
theorem B433859 : Blo 287828 433859 := bstep (se 1 (by rfl) ⟨325394, by rfl⟩ : syracuseStep 433859 = 650789) B650789
theorem B433889 : Blo 287828 433889 := bstep (se 2 (by rfl) ⟨162708, by rfl⟩ : syracuseStep 433889 = 325417) B325417
theorem B433907 : Blo 287828 433907 := bstep (se 1 (by rfl) ⟨325430, by rfl⟩ : syracuseStep 433907 = 650861) B650861
theorem B433937 : Blo 287828 433937 := bstep (se 2 (by rfl) ⟨162726, by rfl⟩ : syracuseStep 433937 = 325453) B325453
theorem B433955 : Blo 287828 433955 := bstep (se 1 (by rfl) ⟨325466, by rfl⟩ : syracuseStep 433955 = 650933) B650933
theorem B433985 : Blo 287828 433985 := bstep (se 2 (by rfl) ⟨162744, by rfl⟩ : syracuseStep 433985 = 325489) B325489
theorem B434003 : Blo 287828 434003 := bstep (se 1 (by rfl) ⟨325502, by rfl⟩ : syracuseStep 434003 = 651005) B651005
theorem B434033 : Blo 287828 434033 := bstep (se 2 (by rfl) ⟨162762, by rfl⟩ : syracuseStep 434033 = 325525) B325525
theorem B434051 : Blo 287828 434051 := bstep (se 1 (by rfl) ⟨325538, by rfl⟩ : syracuseStep 434051 = 651077) B651077
theorem B434081 : Blo 287828 434081 := bstep (se 2 (by rfl) ⟨162780, by rfl⟩ : syracuseStep 434081 = 325561) B325561
theorem B434099 : Blo 287828 434099 := bstep (se 1 (by rfl) ⟨325574, by rfl⟩ : syracuseStep 434099 = 651149) B651149
theorem B1974221 : Blo 287828 1974221 := bstep (se 3 (by rfl) ⟨370166, by rfl⟩ : syracuseStep 1974221 = 740333) B740333
theorem B1679309 : Blo 287828 1679309 := bstep (se 3 (by rfl) ⟨314870, by rfl⟩ : syracuseStep 1679309 = 629741) B629741
theorem B434129 : Blo 287828 434129 := bstep (se 2 (by rfl) ⟨162798, by rfl⟩ : syracuseStep 434129 = 325597) B325597
theorem B761827 : Blo 287828 761827 := bstep (se 1 (by rfl) ⟨571370, by rfl⟩ : syracuseStep 761827 = 1142741) B1142741
theorem B434147 : Blo 287828 434147 := bstep (se 1 (by rfl) ⟨325610, by rfl⟩ : syracuseStep 434147 = 651221) B651221
theorem B434177 : Blo 287828 434177 := bstep (se 2 (by rfl) ⟨162816, by rfl⟩ : syracuseStep 434177 = 325633) B325633
theorem B827405 : Blo 287828 827405 := bstep (se 3 (by rfl) ⟨155138, by rfl⟩ : syracuseStep 827405 = 310277) B310277
theorem B434195 : Blo 287828 434195 := bstep (se 1 (by rfl) ⟨325646, by rfl⟩ : syracuseStep 434195 = 651293) B651293
theorem B434225 : Blo 287828 434225 := bstep (se 2 (by rfl) ⟨162834, by rfl⟩ : syracuseStep 434225 = 325669) B325669
theorem B434243 : Blo 287828 434243 := bstep (se 1 (by rfl) ⟨325682, by rfl⟩ : syracuseStep 434243 = 651365) B651365
theorem B368707 : Blo 287828 368707 := bstep (se 1 (by rfl) ⟨276530, by rfl⟩ : syracuseStep 368707 = 553061) B553061
theorem B434273 : Blo 287828 434273 := bstep (se 2 (by rfl) ⟨162852, by rfl⟩ : syracuseStep 434273 = 325705) B325705
theorem B434291 : Blo 287828 434291 := bstep (se 1 (by rfl) ⟨325718, by rfl⟩ : syracuseStep 434291 = 651437) B651437
theorem B729233 : Blo 287828 729233 := bstep (se 2 (by rfl) ⟨273462, by rfl⟩ : syracuseStep 729233 = 546925) B546925
theorem B434321 : Blo 287828 434321 := bstep (se 2 (by rfl) ⟨162870, by rfl⟩ : syracuseStep 434321 = 325741) B325741
theorem B434339 : Blo 287828 434339 := bstep (se 1 (by rfl) ⟨325754, by rfl⟩ : syracuseStep 434339 = 651509) B651509
theorem B368803 : Blo 287828 368803 := bstep (se 1 (by rfl) ⟨276602, by rfl⟩ : syracuseStep 368803 = 553205) B553205
theorem B434369 : Blo 287828 434369 := bstep (se 2 (by rfl) ⟨162888, by rfl⟩ : syracuseStep 434369 = 325777) B325777
theorem B729283 : Blo 287828 729283 := bstep (se 1 (by rfl) ⟨546962, by rfl⟩ : syracuseStep 729283 = 1093925) B1093925
theorem B827597 : Blo 287828 827597 := bstep (se 3 (by rfl) ⟨155174, by rfl⟩ : syracuseStep 827597 = 310349) B310349
theorem B434387 : Blo 287828 434387 := bstep (se 1 (by rfl) ⟨325790, by rfl⟩ : syracuseStep 434387 = 651581) B651581
theorem B434417 : Blo 287828 434417 := bstep (se 2 (by rfl) ⟨162906, by rfl⟩ : syracuseStep 434417 = 325813) B325813
theorem B434435 : Blo 287828 434435 := bstep (se 1 (by rfl) ⟨325826, by rfl⟩ : syracuseStep 434435 = 651653) B651653
theorem B434465 : Blo 287828 434465 := bstep (se 2 (by rfl) ⟨162924, by rfl⟩ : syracuseStep 434465 = 325849) B325849
theorem B434483 : Blo 287828 434483 := bstep (se 1 (by rfl) ⟨325862, by rfl⟩ : syracuseStep 434483 = 651725) B651725
theorem B3744053 : Blo 287828 3744053 := bstep (se 5 (by rfl) ⟨175502, by rfl⟩ : syracuseStep 3744053 = 351005) B351005
theorem B729425 : Blo 287828 729425 := bstep (se 2 (by rfl) ⟨273534, by rfl⟩ : syracuseStep 729425 = 547069) B547069
theorem B434513 : Blo 287828 434513 := bstep (se 2 (by rfl) ⟨162942, by rfl⟩ : syracuseStep 434513 = 325885) B325885
theorem B434531 : Blo 287828 434531 := bstep (se 1 (by rfl) ⟨325898, by rfl⟩ : syracuseStep 434531 = 651797) B651797
theorem B434561 : Blo 287828 434561 := bstep (se 2 (by rfl) ⟨162960, by rfl⟩ : syracuseStep 434561 = 325921) B325921
theorem B434579 : Blo 287828 434579 := bstep (se 1 (by rfl) ⟨325934, by rfl⟩ : syracuseStep 434579 = 651869) B651869
theorem B434609 : Blo 287828 434609 := bstep (se 2 (by rfl) ⟨162978, by rfl⟩ : syracuseStep 434609 = 325957) B325957
theorem B434627 : Blo 287828 434627 := bstep (se 1 (by rfl) ⟨325970, by rfl⟩ : syracuseStep 434627 = 651941) B651941
theorem B434657 : Blo 287828 434657 := bstep (se 2 (by rfl) ⟨162996, by rfl⟩ : syracuseStep 434657 = 325993) B325993
theorem B434675 : Blo 287828 434675 := bstep (se 1 (by rfl) ⟨326006, by rfl⟩ : syracuseStep 434675 = 652013) B652013
theorem B434705 : Blo 287828 434705 := bstep (se 2 (by rfl) ⟨163014, by rfl⟩ : syracuseStep 434705 = 326029) B326029
theorem B434723 : Blo 287828 434723 := bstep (se 1 (by rfl) ⟨326042, by rfl⟩ : syracuseStep 434723 = 652085) B652085
theorem B434753 : Blo 287828 434753 := bstep (se 2 (by rfl) ⟨163032, by rfl⟩ : syracuseStep 434753 = 326065) B326065
theorem B434771 : Blo 287828 434771 := bstep (se 1 (by rfl) ⟨326078, by rfl⟩ : syracuseStep 434771 = 652157) B652157
theorem B434801 : Blo 287828 434801 := bstep (se 2 (by rfl) ⟨163050, by rfl⟩ : syracuseStep 434801 = 326101) B326101
theorem B434819 : Blo 287828 434819 := bstep (se 1 (by rfl) ⟨326114, by rfl⟩ : syracuseStep 434819 = 652229) B652229
theorem B369299 : Blo 287828 369299 := bstep (se 1 (by rfl) ⟨276974, by rfl⟩ : syracuseStep 369299 = 553949) B553949
theorem B434849 : Blo 287828 434849 := bstep (se 2 (by rfl) ⟨163068, by rfl⟩ : syracuseStep 434849 = 326137) B326137
theorem B434867 : Blo 287828 434867 := bstep (se 1 (by rfl) ⟨326150, by rfl⟩ : syracuseStep 434867 = 652301) B652301
theorem B434897 : Blo 287828 434897 := bstep (se 2 (by rfl) ⟨163086, by rfl⟩ : syracuseStep 434897 = 326173) B326173
theorem B434915 : Blo 287828 434915 := bstep (se 1 (by rfl) ⟨326186, by rfl⟩ : syracuseStep 434915 = 652373) B652373
theorem B631523 : Blo 287828 631523 := bstep (se 1 (by rfl) ⟨473642, by rfl⟩ : syracuseStep 631523 = 947285) B947285
theorem B434945 : Blo 287828 434945 := bstep (se 2 (by rfl) ⟨163104, by rfl⟩ : syracuseStep 434945 = 326209) B326209
theorem B434963 : Blo 287828 434963 := bstep (se 1 (by rfl) ⟨326222, by rfl⟩ : syracuseStep 434963 = 652445) B652445
theorem B1254179 : Blo 287828 1254179 := bstep (se 1 (by rfl) ⟨940634, by rfl⟩ : syracuseStep 1254179 = 1881269) B1881269
theorem B434993 : Blo 287828 434993 := bstep (se 2 (by rfl) ⟨163122, by rfl⟩ : syracuseStep 434993 = 326245) B326245
theorem B435011 : Blo 287828 435011 := bstep (se 1 (by rfl) ⟨326258, by rfl⟩ : syracuseStep 435011 = 652517) B652517
theorem B435041 : Blo 287828 435041 := bstep (se 2 (by rfl) ⟨163140, by rfl⟩ : syracuseStep 435041 = 326281) B326281
theorem B664433 : Blo 287828 664433 := bstep (se 2 (by rfl) ⟨249162, by rfl⟩ : syracuseStep 664433 = 498325) B498325
theorem B435059 : Blo 287828 435059 := bstep (se 1 (by rfl) ⟨326294, by rfl⟩ : syracuseStep 435059 = 652589) B652589
theorem B435089 : Blo 287828 435089 := bstep (se 2 (by rfl) ⟨163158, by rfl⟩ : syracuseStep 435089 = 326317) B326317
theorem B435107 : Blo 287828 435107 := bstep (se 1 (by rfl) ⟨326330, by rfl⟩ : syracuseStep 435107 = 652661) B652661
theorem B435137 : Blo 287828 435137 := bstep (se 2 (by rfl) ⟨163176, by rfl⟩ : syracuseStep 435137 = 326353) B326353
theorem B435155 : Blo 287828 435155 := bstep (se 1 (by rfl) ⟨326366, by rfl⟩ : syracuseStep 435155 = 652733) B652733
theorem B435185 : Blo 287828 435185 := bstep (se 2 (by rfl) ⟨163194, by rfl⟩ : syracuseStep 435185 = 326389) B326389
theorem B435203 : Blo 287828 435203 := bstep (se 1 (by rfl) ⟨326402, by rfl⟩ : syracuseStep 435203 = 652805) B652805
theorem B435233 : Blo 287828 435233 := bstep (se 2 (by rfl) ⟨163212, by rfl⟩ : syracuseStep 435233 = 326425) B326425
theorem B435251 : Blo 287828 435251 := bstep (se 1 (by rfl) ⟨326438, by rfl⟩ : syracuseStep 435251 = 652877) B652877
theorem B664643 : Blo 287828 664643 := bstep (se 1 (by rfl) ⟨498482, by rfl⟩ : syracuseStep 664643 = 996965) B996965
theorem B435281 : Blo 287828 435281 := bstep (se 2 (by rfl) ⟨163230, by rfl⟩ : syracuseStep 435281 = 326461) B326461
theorem B435299 : Blo 287828 435299 := bstep (se 1 (by rfl) ⟨326474, by rfl⟩ : syracuseStep 435299 = 652949) B652949
theorem B435329 : Blo 287828 435329 := bstep (se 2 (by rfl) ⟨163248, by rfl⟩ : syracuseStep 435329 = 326497) B326497
theorem B435347 : Blo 287828 435347 := bstep (se 1 (by rfl) ⟨326510, by rfl⟩ : syracuseStep 435347 = 653021) B653021
theorem B828589 : Blo 287828 828589 := bstep (se 3 (by rfl) ⟨155360, by rfl⟩ : syracuseStep 828589 = 310721) B310721
theorem B435377 : Blo 287828 435377 := bstep (se 2 (by rfl) ⟨163266, by rfl⟩ : syracuseStep 435377 = 326533) B326533
theorem B435395 : Blo 287828 435395 := bstep (se 1 (by rfl) ⟨326546, by rfl⟩ : syracuseStep 435395 = 653093) B653093
theorem B435425 : Blo 287828 435425 := bstep (se 2 (by rfl) ⟨163284, by rfl⟩ : syracuseStep 435425 = 326569) B326569
theorem B697585 : Blo 287828 697585 := bstep (se 2 (by rfl) ⟨261594, by rfl⟩ : syracuseStep 697585 = 523189) B523189
theorem B435443 : Blo 287828 435443 := bstep (se 1 (by rfl) ⟨326582, by rfl⟩ : syracuseStep 435443 = 653165) B653165
theorem B435473 : Blo 287828 435473 := bstep (se 2 (by rfl) ⟨163302, by rfl⟩ : syracuseStep 435473 = 326605) B326605
theorem B435491 : Blo 287828 435491 := bstep (se 1 (by rfl) ⟨326618, by rfl⟩ : syracuseStep 435491 = 653237) B653237
theorem B959789 : Blo 287828 959789 := bstep (se 3 (by rfl) ⟨179960, by rfl⟩ : syracuseStep 959789 = 359921) B359921
theorem B730417 : Blo 287828 730417 := bstep (se 2 (by rfl) ⟨273906, by rfl⟩ : syracuseStep 730417 = 547813) B547813
theorem B435521 : Blo 287828 435521 := bstep (se 2 (by rfl) ⟨163320, by rfl⟩ : syracuseStep 435521 = 326641) B326641
theorem B435539 : Blo 287828 435539 := bstep (se 1 (by rfl) ⟨326654, by rfl⟩ : syracuseStep 435539 = 653309) B653309
theorem B435569 : Blo 287828 435569 := bstep (se 2 (by rfl) ⟨163338, by rfl⟩ : syracuseStep 435569 = 326677) B326677
theorem B435587 : Blo 287828 435587 := bstep (se 1 (by rfl) ⟨326690, by rfl⟩ : syracuseStep 435587 = 653381) B653381
theorem B435617 : Blo 287828 435617 := bstep (se 2 (by rfl) ⟨163356, by rfl⟩ : syracuseStep 435617 = 326713) B326713
theorem B435635 : Blo 287828 435635 := bstep (se 1 (by rfl) ⟨326726, by rfl⟩ : syracuseStep 435635 = 653453) B653453
theorem B435665 : Blo 287828 435665 := bstep (se 2 (by rfl) ⟨163374, by rfl⟩ : syracuseStep 435665 = 326749) B326749
theorem B435683 : Blo 287828 435683 := bstep (se 1 (by rfl) ⟨326762, by rfl⟩ : syracuseStep 435683 = 653525) B653525
theorem B435713 : Blo 287828 435713 := bstep (se 2 (by rfl) ⟨163392, by rfl⟩ : syracuseStep 435713 = 326785) B326785
theorem B1648133 : Blo 287828 1648133 := bstep (se 4 (by rfl) ⟨154512, by rfl⟩ : syracuseStep 1648133 = 309025) B309025
theorem B435731 : Blo 287828 435731 := bstep (se 1 (by rfl) ⟨326798, by rfl⟩ : syracuseStep 435731 = 653597) B653597
theorem B927281 : Blo 287828 927281 := bstep (se 2 (by rfl) ⟨347730, by rfl⟩ : syracuseStep 927281 = 695461) B695461
theorem B435761 : Blo 287828 435761 := bstep (se 2 (by rfl) ⟨163410, by rfl⟩ : syracuseStep 435761 = 326821) B326821
theorem B730691 : Blo 287828 730691 := bstep (se 1 (by rfl) ⟨548018, by rfl⟩ : syracuseStep 730691 = 1096037) B1096037
theorem B435779 : Blo 287828 435779 := bstep (se 1 (by rfl) ⟨326834, by rfl⟩ : syracuseStep 435779 = 653669) B653669
theorem B435809 : Blo 287828 435809 := bstep (se 2 (by rfl) ⟨163428, by rfl⟩ : syracuseStep 435809 = 326857) B326857
theorem B435827 : Blo 287828 435827 := bstep (se 1 (by rfl) ⟨326870, by rfl⟩ : syracuseStep 435827 = 653741) B653741
theorem B435857 : Blo 287828 435857 := bstep (se 2 (by rfl) ⟨163446, by rfl⟩ : syracuseStep 435857 = 326893) B326893
theorem B435875 : Blo 287828 435875 := bstep (se 1 (by rfl) ⟨326906, by rfl⟩ : syracuseStep 435875 = 653813) B653813
theorem B927409 : Blo 287828 927409 := bstep (se 2 (by rfl) ⟨347778, by rfl⟩ : syracuseStep 927409 = 695557) B695557
theorem B435905 : Blo 287828 435905 := bstep (se 2 (by rfl) ⟨163464, by rfl⟩ : syracuseStep 435905 = 326929) B326929
theorem B435923 : Blo 287828 435923 := bstep (se 1 (by rfl) ⟨326942, by rfl⟩ : syracuseStep 435923 = 653885) B653885
theorem B435953 : Blo 287828 435953 := bstep (se 2 (by rfl) ⟨163482, by rfl⟩ : syracuseStep 435953 = 326965) B326965
theorem B730883 : Blo 287828 730883 := bstep (se 1 (by rfl) ⟨548162, by rfl⟩ : syracuseStep 730883 = 1096325) B1096325
theorem B435971 : Blo 287828 435971 := bstep (se 1 (by rfl) ⟨326978, by rfl⟩ : syracuseStep 435971 = 653957) B653957
theorem B4007693 : Blo 287828 4007693 := bstep (se 3 (by rfl) ⟨751442, by rfl⟩ : syracuseStep 4007693 = 1502885) B1502885
theorem B436001 : Blo 287828 436001 := bstep (se 2 (by rfl) ⟨163500, by rfl⟩ : syracuseStep 436001 = 327001) B327001
theorem B436019 : Blo 287828 436019 := bstep (se 1 (by rfl) ⟨327014, by rfl⟩ : syracuseStep 436019 = 654029) B654029
theorem B436049 : Blo 287828 436049 := bstep (se 2 (by rfl) ⟨163518, by rfl⟩ : syracuseStep 436049 = 327037) B327037
theorem B436067 : Blo 287828 436067 := bstep (se 1 (by rfl) ⟨327050, by rfl⟩ : syracuseStep 436067 = 654101) B654101
theorem B436097 : Blo 287828 436097 := bstep (se 2 (by rfl) ⟨163536, by rfl⟩ : syracuseStep 436097 = 327073) B327073
theorem B436115 : Blo 287828 436115 := bstep (se 1 (by rfl) ⟨327086, by rfl⟩ : syracuseStep 436115 = 654173) B654173
theorem B927665 : Blo 287828 927665 := bstep (se 2 (by rfl) ⟨347874, by rfl⟩ : syracuseStep 927665 = 695749) B695749
theorem B436145 : Blo 287828 436145 := bstep (se 2 (by rfl) ⟨163554, by rfl⟩ : syracuseStep 436145 = 327109) B327109
theorem B436163 : Blo 287828 436163 := bstep (se 1 (by rfl) ⟨327122, by rfl⟩ : syracuseStep 436163 = 654245) B654245
theorem B436193 : Blo 287828 436193 := bstep (se 2 (by rfl) ⟨163572, by rfl⟩ : syracuseStep 436193 = 327145) B327145
theorem B436211 : Blo 287828 436211 := bstep (se 1 (by rfl) ⟨327158, by rfl⟩ : syracuseStep 436211 = 654317) B654317
theorem B436241 : Blo 287828 436241 := bstep (se 2 (by rfl) ⟨163590, by rfl⟩ : syracuseStep 436241 = 327181) B327181
theorem B436259 : Blo 287828 436259 := bstep (se 1 (by rfl) ⟨327194, by rfl⟩ : syracuseStep 436259 = 654389) B654389
theorem B436289 : Blo 287828 436289 := bstep (se 2 (by rfl) ⟨163608, by rfl⟩ : syracuseStep 436289 = 327217) B327217
theorem B436307 : Blo 287828 436307 := bstep (se 1 (by rfl) ⟨327230, by rfl⟩ : syracuseStep 436307 = 654461) B654461
theorem B436337 : Blo 287828 436337 := bstep (se 2 (by rfl) ⟨163626, by rfl⟩ : syracuseStep 436337 = 327253) B327253
theorem B436355 : Blo 287828 436355 := bstep (se 1 (by rfl) ⟨327266, by rfl⟩ : syracuseStep 436355 = 654533) B654533
theorem B436385 : Blo 287828 436385 := bstep (se 2 (by rfl) ⟨163644, by rfl⟩ : syracuseStep 436385 = 327289) B327289
theorem B436403 : Blo 287828 436403 := bstep (se 1 (by rfl) ⟨327302, by rfl⟩ : syracuseStep 436403 = 654605) B654605
theorem B436433 : Blo 287828 436433 := bstep (se 2 (by rfl) ⟨163662, by rfl⟩ : syracuseStep 436433 = 327325) B327325
theorem B436451 : Blo 287828 436451 := bstep (se 1 (by rfl) ⟨327338, by rfl⟩ : syracuseStep 436451 = 654677) B654677
theorem B436481 : Blo 287828 436481 := bstep (se 2 (by rfl) ⟨163680, by rfl⟩ : syracuseStep 436481 = 327361) B327361
theorem B436499 : Blo 287828 436499 := bstep (se 1 (by rfl) ⟨327374, by rfl⟩ : syracuseStep 436499 = 654749) B654749
theorem B436529 : Blo 287828 436529 := bstep (se 2 (by rfl) ⟨163698, by rfl⟩ : syracuseStep 436529 = 327397) B327397
theorem B436547 : Blo 287828 436547 := bstep (se 1 (by rfl) ⟨327410, by rfl⟩ : syracuseStep 436547 = 654821) B654821
theorem B1059149 : Blo 287828 1059149 := bstep (se 3 (by rfl) ⟨198590, by rfl⟩ : syracuseStep 1059149 = 397181) B397181
theorem B436577 : Blo 287828 436577 := bstep (se 2 (by rfl) ⟨163716, by rfl⟩ : syracuseStep 436577 = 327433) B327433
theorem B436595 : Blo 287828 436595 := bstep (se 1 (by rfl) ⟨327446, by rfl⟩ : syracuseStep 436595 = 654893) B654893
theorem B436625 : Blo 287828 436625 := bstep (se 2 (by rfl) ⟨163734, by rfl⟩ : syracuseStep 436625 = 327469) B327469
theorem B436643 : Blo 287828 436643 := bstep (se 1 (by rfl) ⟨327482, by rfl⟩ : syracuseStep 436643 = 654965) B654965
theorem B436673 : Blo 287828 436673 := bstep (se 2 (by rfl) ⟨163752, by rfl⟩ : syracuseStep 436673 = 327505) B327505
theorem B436691 : Blo 287828 436691 := bstep (se 1 (by rfl) ⟨327518, by rfl⟩ : syracuseStep 436691 = 655037) B655037
theorem B436721 : Blo 287828 436721 := bstep (se 2 (by rfl) ⟨163770, by rfl⟩ : syracuseStep 436721 = 327541) B327541
theorem B436739 : Blo 287828 436739 := bstep (se 1 (by rfl) ⟨327554, by rfl⟩ : syracuseStep 436739 = 655109) B655109
theorem B436769 : Blo 287828 436769 := bstep (se 2 (by rfl) ⟨163788, by rfl⟩ : syracuseStep 436769 = 327577) B327577
theorem B436787 : Blo 287828 436787 := bstep (se 1 (by rfl) ⟨327590, by rfl⟩ : syracuseStep 436787 = 655181) B655181
theorem B436817 : Blo 287828 436817 := bstep (se 2 (by rfl) ⟨163806, by rfl⟩ : syracuseStep 436817 = 327613) B327613
theorem B436835 : Blo 287828 436835 := bstep (se 1 (by rfl) ⟨327626, by rfl⟩ : syracuseStep 436835 = 655253) B655253
theorem B436865 : Blo 287828 436865 := bstep (se 2 (by rfl) ⟨163824, by rfl⟩ : syracuseStep 436865 = 327649) B327649
theorem B436883 : Blo 287828 436883 := bstep (se 1 (by rfl) ⟨327662, by rfl⟩ : syracuseStep 436883 = 655325) B655325
theorem B731825 : Blo 287828 731825 := bstep (se 2 (by rfl) ⟨274434, by rfl⟩ : syracuseStep 731825 = 548869) B548869
theorem B436913 : Blo 287828 436913 := bstep (se 2 (by rfl) ⟨163842, by rfl⟩ : syracuseStep 436913 = 327685) B327685
theorem B436931 : Blo 287828 436931 := bstep (se 1 (by rfl) ⟨327698, by rfl⟩ : syracuseStep 436931 = 655397) B655397
theorem B436961 : Blo 287828 436961 := bstep (se 2 (by rfl) ⟨163860, by rfl⟩ : syracuseStep 436961 = 327721) B327721
theorem B731875 : Blo 287828 731875 := bstep (se 1 (by rfl) ⟨548906, by rfl⟩ : syracuseStep 731875 = 1097813) B1097813
theorem B436979 : Blo 287828 436979 := bstep (se 1 (by rfl) ⟨327734, by rfl⟩ : syracuseStep 436979 = 655469) B655469
theorem B2992909 : Blo 287828 2992909 := bstep (se 3 (by rfl) ⟨561170, by rfl⟩ : syracuseStep 2992909 = 1122341) B1122341
theorem B437009 : Blo 287828 437009 := bstep (se 2 (by rfl) ⟨163878, by rfl⟩ : syracuseStep 437009 = 327757) B327757
theorem B437027 : Blo 287828 437027 := bstep (se 1 (by rfl) ⟨327770, by rfl⟩ : syracuseStep 437027 = 655541) B655541
theorem B437057 : Blo 287828 437057 := bstep (se 2 (by rfl) ⟨163896, by rfl⟩ : syracuseStep 437057 = 327793) B327793
theorem B437075 : Blo 287828 437075 := bstep (se 1 (by rfl) ⟨327806, by rfl⟩ : syracuseStep 437075 = 655613) B655613
theorem B732017 : Blo 287828 732017 := bstep (se 2 (by rfl) ⟨274506, by rfl⟩ : syracuseStep 732017 = 549013) B549013
theorem B437105 : Blo 287828 437105 := bstep (se 2 (by rfl) ⟨163914, by rfl⟩ : syracuseStep 437105 = 327829) B327829
theorem B830321 : Blo 287828 830321 := bstep (se 2 (by rfl) ⟨311370, by rfl⟩ : syracuseStep 830321 = 622741) B622741
theorem B437123 : Blo 287828 437123 := bstep (se 1 (by rfl) ⟨327842, by rfl⟩ : syracuseStep 437123 = 655685) B655685
theorem B437153 : Blo 287828 437153 := bstep (se 2 (by rfl) ⟨163932, by rfl⟩ : syracuseStep 437153 = 327865) B327865
theorem B437171 : Blo 287828 437171 := bstep (se 1 (by rfl) ⟨327878, by rfl⟩ : syracuseStep 437171 = 655757) B655757
theorem B1092557 : Blo 287828 1092557 := bstep (se 3 (by rfl) ⟨204854, by rfl⟩ : syracuseStep 1092557 = 409709) B409709
theorem B437201 : Blo 287828 437201 := bstep (se 2 (by rfl) ⟨163950, by rfl⟩ : syracuseStep 437201 = 327901) B327901
theorem B437219 : Blo 287828 437219 := bstep (se 1 (by rfl) ⟨327914, by rfl⟩ : syracuseStep 437219 = 655829) B655829
theorem B437249 : Blo 287828 437249 := bstep (se 2 (by rfl) ⟨163968, by rfl⟩ : syracuseStep 437249 = 327937) B327937
theorem B437267 : Blo 287828 437267 := bstep (se 1 (by rfl) ⟨327950, by rfl⟩ : syracuseStep 437267 = 655901) B655901
theorem B1846307 : Blo 287828 1846307 := bstep (se 1 (by rfl) ⟨1384730, by rfl⟩ : syracuseStep 1846307 = 2769461) B2769461
theorem B437297 : Blo 287828 437297 := bstep (se 2 (by rfl) ⟨163986, by rfl⟩ : syracuseStep 437297 = 327973) B327973
theorem B830513 : Blo 287828 830513 := bstep (se 2 (by rfl) ⟨311442, by rfl⟩ : syracuseStep 830513 = 622885) B622885
theorem B437315 : Blo 287828 437315 := bstep (se 1 (by rfl) ⟨327986, by rfl⟩ : syracuseStep 437315 = 655973) B655973
theorem B437345 : Blo 287828 437345 := bstep (se 2 (by rfl) ⟨164004, by rfl⟩ : syracuseStep 437345 = 328009) B328009
theorem B437363 : Blo 287828 437363 := bstep (se 1 (by rfl) ⟨328022, by rfl⟩ : syracuseStep 437363 = 656045) B656045
theorem B437393 : Blo 287828 437393 := bstep (se 2 (by rfl) ⟨164022, by rfl⟩ : syracuseStep 437393 = 328045) B328045
theorem B437411 : Blo 287828 437411 := bstep (se 1 (by rfl) ⟨328058, by rfl⟩ : syracuseStep 437411 = 656117) B656117
theorem B437441 : Blo 287828 437441 := bstep (se 2 (by rfl) ⟨164040, by rfl⟩ : syracuseStep 437441 = 328081) B328081
theorem B437459 : Blo 287828 437459 := bstep (se 1 (by rfl) ⟨328094, by rfl⟩ : syracuseStep 437459 = 656189) B656189
theorem B437489 : Blo 287828 437489 := bstep (se 2 (by rfl) ⟨164058, by rfl⟩ : syracuseStep 437489 = 328117) B328117
theorem B437507 : Blo 287828 437507 := bstep (se 1 (by rfl) ⟨328130, by rfl⟩ : syracuseStep 437507 = 656261) B656261
theorem B437537 : Blo 287828 437537 := bstep (se 2 (by rfl) ⟨164076, by rfl⟩ : syracuseStep 437537 = 328153) B328153
theorem B437555 : Blo 287828 437555 := bstep (se 1 (by rfl) ⟨328166, by rfl⟩ : syracuseStep 437555 = 656333) B656333
theorem B437585 : Blo 287828 437585 := bstep (se 2 (by rfl) ⟨164094, by rfl⟩ : syracuseStep 437585 = 328189) B328189
theorem B437603 : Blo 287828 437603 := bstep (se 1 (by rfl) ⟨328202, by rfl⟩ : syracuseStep 437603 = 656405) B656405
theorem B437633 : Blo 287828 437633 := bstep (se 2 (by rfl) ⟨164112, by rfl⟩ : syracuseStep 437633 = 328225) B328225
theorem B437651 : Blo 287828 437651 := bstep (se 1 (by rfl) ⟨328238, by rfl⟩ : syracuseStep 437651 = 656477) B656477
theorem B437681 : Blo 287828 437681 := bstep (se 2 (by rfl) ⟨164130, by rfl⟩ : syracuseStep 437681 = 328261) B328261
theorem B437699 : Blo 287828 437699 := bstep (se 1 (by rfl) ⟨328274, by rfl⟩ : syracuseStep 437699 = 656549) B656549
theorem B437729 : Blo 287828 437729 := bstep (se 2 (by rfl) ⟨164148, by rfl⟩ : syracuseStep 437729 = 328297) B328297
theorem B15904309 : Blo 287828 15904309 := bstep (se 5 (by rfl) ⟨745514, by rfl⟩ : syracuseStep 15904309 = 1491029) B1491029
theorem B929357 : Blo 287828 929357 := bstep (se 3 (by rfl) ⟨174254, by rfl⟩ : syracuseStep 929357 = 348509) B348509
theorem B733009 : Blo 287828 733009 := bstep (se 2 (by rfl) ⟨274878, by rfl⟩ : syracuseStep 733009 = 549757) B549757
theorem B733283 : Blo 287828 733283 := bstep (se 1 (by rfl) ⟨549962, by rfl⟩ : syracuseStep 733283 = 1099925) B1099925
theorem B733475 : Blo 287828 733475 := bstep (se 1 (by rfl) ⟨550106, by rfl⟩ : syracuseStep 733475 = 1100213) B1100213
theorem B930125 : Blo 287828 930125 := bstep (se 3 (by rfl) ⟨174398, by rfl⟩ : syracuseStep 930125 = 348797) B348797
theorem B1094093 : Blo 287828 1094093 := bstep (se 3 (by rfl) ⟨205142, by rfl⟩ : syracuseStep 1094093 = 410285) B410285
theorem B307795 : Blo 287828 307795 := bstep (se 1 (by rfl) ⟨230846, by rfl⟩ : syracuseStep 307795 = 461693) B461693
theorem B930637 : Blo 287828 930637 := bstep (se 3 (by rfl) ⟨174494, by rfl⟩ : syracuseStep 930637 = 348989) B348989
theorem B439427 : Blo 287828 439427 := bstep (se 1 (by rfl) ⟨329570, by rfl⟩ : syracuseStep 439427 = 659141) B659141
theorem B734417 : Blo 287828 734417 := bstep (se 2 (by rfl) ⟨275406, by rfl⟩ : syracuseStep 734417 = 550813) B550813
theorem B1094897 : Blo 287828 1094897 := bstep (se 2 (by rfl) ⟨410586, by rfl⟩ : syracuseStep 1094897 = 821173) B821173
theorem B734467 : Blo 287828 734467 := bstep (se 1 (by rfl) ⟨550850, by rfl⟩ : syracuseStep 734467 = 1101701) B1101701
theorem B374051 : Blo 287828 374051 := bstep (se 1 (by rfl) ⟨280538, by rfl⟩ : syracuseStep 374051 = 561077) B561077
theorem B931139 : Blo 287828 931139 := bstep (se 1 (by rfl) ⟨698354, by rfl⟩ : syracuseStep 931139 = 1396709) B1396709
theorem B996749 : Blo 287828 996749 := bstep (se 3 (by rfl) ⟨186890, by rfl⟩ : syracuseStep 996749 = 373781) B373781
theorem B734609 : Blo 287828 734609 := bstep (se 2 (by rfl) ⟨275478, by rfl⟩ : syracuseStep 734609 = 550957) B550957
theorem B440035 : Blo 287828 440035 := bstep (se 1 (by rfl) ⟨330026, by rfl⟩ : syracuseStep 440035 = 660053) B660053
theorem B1095565 : Blo 287828 1095565 := bstep (se 3 (by rfl) ⟨205418, by rfl⟩ : syracuseStep 1095565 = 410837) B410837
theorem B440273 : Blo 287828 440273 := bstep (se 2 (by rfl) ⟨165102, by rfl⟩ : syracuseStep 440273 = 330205) B330205
theorem B440531 : Blo 287828 440531 := bstep (se 1 (by rfl) ⟨330398, by rfl⟩ : syracuseStep 440531 = 660797) B660797
theorem B735601 : Blo 287828 735601 := bstep (se 2 (by rfl) ⟨275850, by rfl⟩ : syracuseStep 735601 = 551701) B551701
theorem B1325489 : Blo 287828 1325489 := bstep (se 2 (by rfl) ⟨497058, by rfl⟩ : syracuseStep 1325489 = 994117) B994117
theorem B309683 : Blo 287828 309683 := bstep (se 1 (by rfl) ⟨232262, by rfl⟩ : syracuseStep 309683 = 464525) B464525
theorem B473603 : Blo 287828 473603 := bstep (se 1 (by rfl) ⟨355202, by rfl⟩ : syracuseStep 473603 = 710405) B710405
theorem B6404629 : Blo 287828 6404629 := bstep (se 6 (by rfl) ⟨150108, by rfl⟩ : syracuseStep 6404629 = 300217) B300217
theorem B13318769 : Blo 287828 13318769 := bstep (se 2 (by rfl) ⟨4994538, by rfl⟩ : syracuseStep 13318769 = 9989077) B9989077
theorem B735875 : Blo 287828 735875 := bstep (se 1 (by rfl) ⟨551906, by rfl⟩ : syracuseStep 735875 = 1103813) B1103813
theorem B1096355 : Blo 287828 1096355 := bstep (se 1 (by rfl) ⟨822266, by rfl⟩ : syracuseStep 1096355 = 1644533) B1644533
theorem B736067 : Blo 287828 736067 := bstep (se 1 (by rfl) ⟨552050, by rfl⟩ : syracuseStep 736067 = 1104101) B1104101
theorem B3521549 : Blo 287828 3521549 := bstep (se 3 (by rfl) ⟨660290, by rfl⟩ : syracuseStep 3521549 = 1320581) B1320581
theorem B1391651 : Blo 287828 1391651 := bstep (se 1 (by rfl) ⟨1043738, by rfl⟩ : syracuseStep 1391651 = 2087477) B2087477
theorem B932995 : Blo 287828 932995 := bstep (se 1 (by rfl) ⟨699746, by rfl⟩ : syracuseStep 932995 = 1399493) B1399493
theorem B1653965 : Blo 287828 1653965 := bstep (se 3 (by rfl) ⟨310118, by rfl⟩ : syracuseStep 1653965 = 620237) B620237
theorem B441569 : Blo 287828 441569 := bstep (se 2 (by rfl) ⟨165588, by rfl⟩ : syracuseStep 441569 = 331177) B331177
theorem B1391843 : Blo 287828 1391843 := bstep (se 1 (by rfl) ⟨1043882, by rfl⟩ : syracuseStep 1391843 = 2087765) B2087765
theorem B1097009 : Blo 287828 1097009 := bstep (se 2 (by rfl) ⟨411378, by rfl⟩ : syracuseStep 1097009 = 822757) B822757
theorem B441715 : Blo 287828 441715 := bstep (se 1 (by rfl) ⟨331286, by rfl⟩ : syracuseStep 441715 = 662573) B662573
theorem B2211299 : Blo 287828 2211299 := bstep (se 1 (by rfl) ⟨1658474, by rfl⟩ : syracuseStep 2211299 = 3316949) B3316949
theorem B2801137 : Blo 287828 2801137 := bstep (se 2 (by rfl) ⟨1050426, by rfl⟩ : syracuseStep 2801137 = 2100853) B2100853
theorem B933457 : Blo 287828 933457 := bstep (se 2 (by rfl) ⟨350046, by rfl⟩ : syracuseStep 933457 = 700093) B700093
theorem B737009 : Blo 287828 737009 := bstep (se 2 (by rfl) ⟨276378, by rfl⟩ : syracuseStep 737009 = 552757) B552757
theorem B737059 : Blo 287828 737059 := bstep (se 1 (by rfl) ⟨552794, by rfl⟩ : syracuseStep 737059 = 1105589) B1105589
theorem B507713 : Blo 287828 507713 := bstep (se 2 (by rfl) ⟨190392, by rfl⟩ : syracuseStep 507713 = 380785) B380785
theorem B1392497 : Blo 287828 1392497 := bstep (se 2 (by rfl) ⟨522186, by rfl⟩ : syracuseStep 1392497 = 1044373) B1044373
theorem B737201 : Blo 287828 737201 := bstep (se 2 (by rfl) ⟨276450, by rfl⟩ : syracuseStep 737201 = 552901) B552901
theorem B1458161 : Blo 287828 1458161 := bstep (se 2 (by rfl) ⟨546810, by rfl⟩ : syracuseStep 1458161 = 1093621) B1093621
theorem B966691 : Blo 287828 966691 := bstep (se 1 (by rfl) ⟨725018, by rfl⟩ : syracuseStep 966691 = 1450037) B1450037
theorem B3719267 : Blo 287828 3719267 := bstep (se 1 (by rfl) ⟨2789450, by rfl⟩ : syracuseStep 3719267 = 5578901) B5578901
theorem B1065059 : Blo 287828 1065059 := bstep (se 1 (by rfl) ⟨798794, by rfl⟩ : syracuseStep 1065059 = 1597589) B1597589
theorem B410017 : Blo 287828 410017 := bstep (se 2 (by rfl) ⟨153756, by rfl⟩ : syracuseStep 410017 = 307513) B307513
theorem B3293621 : Blo 287828 3293621 := bstep (se 5 (by rfl) ⟨154388, by rfl⟩ : syracuseStep 3293621 = 308777) B308777
theorem B410131 : Blo 287828 410131 := bstep (se 1 (by rfl) ⟨307598, by rfl⟩ : syracuseStep 410131 = 615197) B615197
theorem B1229489 : Blo 287828 1229489 := bstep (se 2 (by rfl) ⟨461058, by rfl⟩ : syracuseStep 1229489 = 922117) B922117
theorem B1229539 : Blo 287828 1229539 := bstep (se 1 (by rfl) ⟨922154, by rfl⟩ : syracuseStep 1229539 = 1844309) B1844309
theorem B1098467 : Blo 287828 1098467 := bstep (se 1 (by rfl) ⟨823850, by rfl⟩ : syracuseStep 1098467 = 1647701) B1647701
theorem B1098481 : Blo 287828 1098481 := bstep (se 2 (by rfl) ⟨411930, by rfl⟩ : syracuseStep 1098481 = 823861) B823861
theorem B1491853 : Blo 287828 1491853 := bstep (se 3 (by rfl) ⟨279722, by rfl⟩ : syracuseStep 1491853 = 559445) B559445
theorem B738193 : Blo 287828 738193 := bstep (se 2 (by rfl) ⟨276822, by rfl⟩ : syracuseStep 738193 = 553645) B553645
theorem B2999281 : Blo 287828 2999281 := bstep (se 2 (by rfl) ⟨1124730, by rfl⟩ : syracuseStep 2999281 = 2249461) B2249461
theorem B738467 : Blo 287828 738467 := bstep (se 1 (by rfl) ⟨553850, by rfl⟩ : syracuseStep 738467 = 1107701) B1107701
theorem B738659 : Blo 287828 738659 := bstep (se 1 (by rfl) ⟨553994, by rfl⟩ : syracuseStep 738659 = 1107989) B1107989
theorem B1656197 : Blo 287828 1656197 := bstep (se 4 (by rfl) ⟨155268, by rfl⟩ : syracuseStep 1656197 = 310537) B310537
theorem B1459619 : Blo 287828 1459619 := bstep (se 1 (by rfl) ⟨1094714, by rfl⟩ : syracuseStep 1459619 = 2189429) B2189429
theorem B935441 : Blo 287828 935441 := bstep (se 2 (by rfl) ⟨350790, by rfl⟩ : syracuseStep 935441 = 701581) B701581
theorem B345875 : Blo 287828 345875 := bstep (se 1 (by rfl) ⟨259406, by rfl⟩ : syracuseStep 345875 = 518813) B518813
theorem B411475 : Blo 287828 411475 := bstep (se 1 (by rfl) ⟨308606, by rfl⟩ : syracuseStep 411475 = 617213) B617213
theorem B1853381 : Blo 287828 1853381 := bstep (se 4 (by rfl) ⟨173754, by rfl⟩ : syracuseStep 1853381 = 347509) B347509
theorem B1656881 : Blo 287828 1656881 := bstep (se 2 (by rfl) ⟨621330, by rfl⟩ : syracuseStep 1656881 = 1242661) B1242661
theorem B1099939 : Blo 287828 1099939 := bstep (se 1 (by rfl) ⟨824954, by rfl⟩ : syracuseStep 1099939 = 1649909) B1649909
theorem B739523 : Blo 287828 739523 := bstep (se 1 (by rfl) ⟨554642, by rfl⟩ : syracuseStep 739523 = 1109285) B1109285
theorem B1460429 : Blo 287828 1460429 := bstep (se 3 (by rfl) ⟨273830, by rfl⟩ : syracuseStep 1460429 = 547661) B547661
theorem B1755377 : Blo 287828 1755377 := bstep (se 2 (by rfl) ⟨658266, by rfl⟩ : syracuseStep 1755377 = 1316533) B1316533
theorem B3754225 : Blo 287828 3754225 := bstep (se 2 (by rfl) ⟨1407834, by rfl⟩ : syracuseStep 3754225 = 2815669) B2815669
theorem B1394957 : Blo 287828 1394957 := bstep (se 3 (by rfl) ⟨261554, by rfl⟩ : syracuseStep 1394957 = 523109) B523109
theorem B1329635 : Blo 287828 1329635 := bstep (se 1 (by rfl) ⟨997226, by rfl⟩ : syracuseStep 1329635 = 1994453) B1994453
theorem B412609 : Blo 287828 412609 := bstep (se 2 (by rfl) ⟨154728, by rfl⟩ : syracuseStep 412609 = 309457) B309457
theorem B412705 : Blo 287828 412705 := bstep (se 2 (by rfl) ⟨154764, by rfl⟩ : syracuseStep 412705 = 309529) B309529
theorem B1231949 : Blo 287828 1231949 := bstep (se 3 (by rfl) ⟨230990, by rfl⟩ : syracuseStep 1231949 = 461981) B461981
theorem B2641349 : Blo 287828 2641349 := bstep (se 4 (by rfl) ⟨247626, by rfl⟩ : syracuseStep 2641349 = 495253) B495253
theorem B1658339 : Blo 287828 1658339 := bstep (se 1 (by rfl) ⟨1243754, by rfl⟩ : syracuseStep 1658339 = 2487509) B2487509
theorem B413201 : Blo 287828 413201 := bstep (se 2 (by rfl) ⟨154950, by rfl⟩ : syracuseStep 413201 = 309901) B309901
theorem B4574773 : Blo 287828 4574773 := bstep (se 5 (by rfl) ⟨214442, by rfl⟩ : syracuseStep 4574773 = 428885) B428885
theorem B347923 : Blo 287828 347923 := bstep (se 1 (by rfl) ⟨260942, by rfl⟩ : syracuseStep 347923 = 521885) B521885
theorem B741155 : Blo 287828 741155 := bstep (se 1 (by rfl) ⟨555866, by rfl⟩ : syracuseStep 741155 = 1111733) B1111733
theorem B347971 : Blo 287828 347971 := bstep (se 1 (by rfl) ⟨260978, by rfl⟩ : syracuseStep 347971 = 521957) B521957
theorem B1757027 : Blo 287828 1757027 := bstep (se 1 (by rfl) ⟨1317770, by rfl⟩ : syracuseStep 1757027 = 2635541) B2635541
theorem B2084707 : Blo 287828 2084707 := bstep (se 1 (by rfl) ⟨1563530, by rfl⟩ : syracuseStep 2084707 = 3127061) B3127061
theorem B3133637 : Blo 287828 3133637 := bstep (se 4 (by rfl) ⟨293778, by rfl⟩ : syracuseStep 3133637 = 587557) B587557
theorem B3526897 : Blo 287828 3526897 := bstep (se 2 (by rfl) ⟨1322586, by rfl⟩ : syracuseStep 3526897 = 2645173) B2645173
theorem B1102157 : Blo 287828 1102157 := bstep (se 3 (by rfl) ⟨206654, by rfl⟩ : syracuseStep 1102157 = 413309) B413309
theorem B414067 : Blo 287828 414067 := bstep (se 1 (by rfl) ⟨310550, by rfl⟩ : syracuseStep 414067 = 621101) B621101
theorem B414163 : Blo 287828 414163 := bstep (se 1 (by rfl) ⟨310622, by rfl⟩ : syracuseStep 414163 = 621245) B621245
theorem B348643 : Blo 287828 348643 := bstep (se 1 (by rfl) ⟨261482, by rfl⟩ : syracuseStep 348643 = 522965) B522965
theorem B1168013 : Blo 287828 1168013 := bstep (se 3 (by rfl) ⟨219002, by rfl⟩ : syracuseStep 1168013 = 438005) B438005
theorem B971459 : Blo 287828 971459 := bstep (se 1 (by rfl) ⟨728594, by rfl⟩ : syracuseStep 971459 = 1457189) B1457189
theorem B1168141 : Blo 287828 1168141 := bstep (se 3 (by rfl) ⟨219026, by rfl⟩ : syracuseStep 1168141 = 438053) B438053
theorem B1561457 : Blo 287828 1561457 := bstep (se 2 (by rfl) ⟨585546, by rfl⟩ : syracuseStep 1561457 = 1171093) B1171093
theorem B414659 : Blo 287828 414659 := bstep (se 1 (by rfl) ⟨310994, by rfl⟩ : syracuseStep 414659 = 621989) B621989
theorem B971729 : Blo 287828 971729 := bstep (se 2 (by rfl) ⟨364398, by rfl⟩ : syracuseStep 971729 = 728797) B728797
theorem B840739 : Blo 287828 840739 := bstep (se 1 (by rfl) ⟨630554, by rfl⟩ : syracuseStep 840739 = 1261109) B1261109
theorem B1463345 : Blo 287828 1463345 := bstep (se 2 (by rfl) ⟨548754, by rfl⟩ : syracuseStep 1463345 = 1097509) B1097509
theorem B7492661 : Blo 287828 7492661 := bstep (se 5 (by rfl) ⟨351218, by rfl⟩ : syracuseStep 7492661 = 702437) B702437
theorem B939235 : Blo 287828 939235 := bstep (se 1 (by rfl) ⟨704426, by rfl⟩ : syracuseStep 939235 = 1408853) B1408853
theorem B3626293 : Blo 287828 3626293 := bstep (se 5 (by rfl) ⟨169982, by rfl⟩ : syracuseStep 3626293 = 339965) B339965
theorem B1856945 : Blo 287828 1856945 := bstep (se 2 (by rfl) ⟨696354, by rfl⟩ : syracuseStep 1856945 = 1392709) B1392709
theorem B972269 : Blo 287828 972269 := bstep (se 3 (by rfl) ⟨182300, by rfl⟩ : syracuseStep 972269 = 364601) B364601
theorem B349715 : Blo 287828 349715 := bstep (se 1 (by rfl) ⟨262286, by rfl⟩ : syracuseStep 349715 = 524573) B524573
theorem B972323 : Blo 287828 972323 := bstep (se 1 (by rfl) ⟨729242, by rfl⟩ : syracuseStep 972323 = 1458485) B1458485
theorem B415297 : Blo 287828 415297 := bstep (se 2 (by rfl) ⟨155736, by rfl⟩ : syracuseStep 415297 = 311473) B311473
theorem B972593 : Blo 287828 972593 := bstep (se 2 (by rfl) ⟨364722, by rfl⟩ : syracuseStep 972593 = 729445) B729445
theorem B546659 : Blo 287828 546659 := bstep (se 1 (by rfl) ⟨409994, by rfl⟩ : syracuseStep 546659 = 819989) B819989
theorem B841873 : Blo 287828 841873 := bstep (se 2 (by rfl) ⟨315702, by rfl⟩ : syracuseStep 841873 = 631405) B631405
theorem B1562885 : Blo 287828 1562885 := bstep (se 4 (by rfl) ⟨146520, by rfl⟩ : syracuseStep 1562885 = 293041) B293041
theorem B973133 : Blo 287828 973133 := bstep (se 3 (by rfl) ⟨182462, by rfl⟩ : syracuseStep 973133 = 364925) B364925
theorem B973187 : Blo 287828 973187 := bstep (se 1 (by rfl) ⟨729890, by rfl⟩ : syracuseStep 973187 = 1459781) B1459781
theorem B1464803 : Blo 287828 1464803 := bstep (se 1 (by rfl) ⟨1098602, by rfl⟩ : syracuseStep 1464803 = 2197205) B2197205
theorem B1661573 : Blo 287828 1661573 := bstep (se 4 (by rfl) ⟨155772, by rfl⟩ : syracuseStep 1661573 = 311545) B311545
theorem B973457 : Blo 287828 973457 := bstep (se 2 (by rfl) ⟨365046, by rfl⟩ : syracuseStep 973457 = 730093) B730093
theorem B547555 : Blo 287828 547555 := bstep (se 1 (by rfl) ⟨410666, by rfl⟩ : syracuseStep 547555 = 821333) B821333
theorem B1858403 : Blo 287828 1858403 := bstep (se 1 (by rfl) ⟨1393802, by rfl⟩ : syracuseStep 1858403 = 2787605) B2787605
theorem B547715 : Blo 287828 547715 := bstep (se 1 (by rfl) ⟨410786, by rfl⟩ : syracuseStep 547715 = 821573) B821573
theorem B1662029 : Blo 287828 1662029 := bstep (se 3 (by rfl) ⟨311630, by rfl⟩ : syracuseStep 1662029 = 623261) B623261
theorem B973997 : Blo 287828 973997 := bstep (se 3 (by rfl) ⟨182624, by rfl⟩ : syracuseStep 973997 = 365249) B365249
theorem B1105073 : Blo 287828 1105073 := bstep (se 2 (by rfl) ⟨414402, by rfl⟩ : syracuseStep 1105073 = 828805) B828805
theorem B974051 : Blo 287828 974051 := bstep (se 1 (by rfl) ⟨730538, by rfl⟩ : syracuseStep 974051 = 1461077) B1461077
theorem B875789 : Blo 287828 875789 := bstep (se 3 (by rfl) ⟨164210, by rfl⟩ : syracuseStep 875789 = 328421) B328421
theorem B1465613 : Blo 287828 1465613 := bstep (se 3 (by rfl) ⟨274802, by rfl⟩ : syracuseStep 1465613 = 549605) B549605
theorem B1400113 : Blo 287828 1400113 := bstep (se 2 (by rfl) ⟨525042, by rfl⟩ : syracuseStep 1400113 = 1050085) B1050085
theorem B875875 : Blo 287828 875875 := bstep (se 1 (by rfl) ⟨656906, by rfl⟩ : syracuseStep 875875 = 1313813) B1313813
theorem B1236323 : Blo 287828 1236323 := bstep (se 1 (by rfl) ⟨927242, by rfl⟩ : syracuseStep 1236323 = 1854485) B1854485
theorem B974321 : Blo 287828 974321 := bstep (se 2 (by rfl) ⟨365370, by rfl⟩ : syracuseStep 974321 = 730741) B730741
theorem B548785 : Blo 287828 548785 := bstep (se 2 (by rfl) ⟨205794, by rfl⟩ : syracuseStep 548785 = 411589) B411589
theorem B778211 : Blo 287828 778211 := bstep (se 1 (by rfl) ⟨583658, by rfl⟩ : syracuseStep 778211 = 1167317) B1167317
theorem B974861 : Blo 287828 974861 := bstep (se 3 (by rfl) ⟨182786, by rfl⟩ : syracuseStep 974861 = 365573) B365573
theorem B974915 : Blo 287828 974915 := bstep (se 1 (by rfl) ⟨731186, by rfl⟩ : syracuseStep 974915 = 1462373) B1462373
theorem B975185 : Blo 287828 975185 := bstep (se 2 (by rfl) ⟨365694, by rfl⟩ : syracuseStep 975185 = 731389) B731389
theorem B647729 : Blo 287828 647729 := bstep (se 2 (by rfl) ⟨242898, by rfl⟩ : syracuseStep 647729 = 485797) B485797
theorem B647747 : Blo 287828 647747 := bstep (se 1 (by rfl) ⟨485810, by rfl⟩ : syracuseStep 647747 = 971621) B971621
theorem B1565261 : Blo 287828 1565261 := bstep (se 3 (by rfl) ⟨293486, by rfl⟩ : syracuseStep 1565261 = 586973) B586973
theorem B1106531 : Blo 287828 1106531 := bstep (se 1 (by rfl) ⟨829898, by rfl⟩ : syracuseStep 1106531 = 1659797) B1659797
theorem B615043 : Blo 287828 615043 := bstep (se 1 (by rfl) ⟨461282, by rfl⟩ : syracuseStep 615043 = 922565) B922565
theorem B2450189 : Blo 287828 2450189 := bstep (se 3 (by rfl) ⟨459410, by rfl⟩ : syracuseStep 2450189 = 918821) B918821
theorem B648017 : Blo 287828 648017 := bstep (se 2 (by rfl) ⟨243006, by rfl⟩ : syracuseStep 648017 = 486013) B486013
theorem B648035 : Blo 287828 648035 := bstep (se 1 (by rfl) ⟨486026, by rfl⟩ : syracuseStep 648035 = 972053) B972053
theorem B975725 : Blo 287828 975725 := bstep (se 3 (by rfl) ⟨182948, by rfl⟩ : syracuseStep 975725 = 365897) B365897
theorem B975779 : Blo 287828 975779 := bstep (se 1 (by rfl) ⟨731834, by rfl⟩ : syracuseStep 975779 = 1463669) B1463669
theorem B549841 : Blo 287828 549841 := bstep (se 2 (by rfl) ⟨206190, by rfl⟩ : syracuseStep 549841 = 412381) B412381
theorem B287843 : Blo 287828 287843 := bstep (se 1 (by rfl) ⟨215882, by rfl⟩ : syracuseStep 287843 = 431765) B431765
theorem B648305 : Blo 287828 648305 := bstep (se 2 (by rfl) ⟨243114, by rfl⟩ : syracuseStep 648305 = 486229) B486229
theorem B287859 : Blo 287828 287859 := bstep (se 1 (by rfl) ⟨215894, by rfl⟩ : syracuseStep 287859 = 431789) B431789
theorem B287875 : Blo 287828 287875 := bstep (se 1 (by rfl) ⟨215906, by rfl⟩ : syracuseStep 287875 = 431813) B431813
theorem B648323 : Blo 287828 648323 := bstep (se 1 (by rfl) ⟨486242, by rfl⟩ : syracuseStep 648323 = 972485) B972485
theorem B287891 : Blo 287828 287891 := bstep (se 1 (by rfl) ⟨215918, by rfl⟩ : syracuseStep 287891 = 431837) B431837
theorem B287907 : Blo 287828 287907 := bstep (se 1 (by rfl) ⟨215930, by rfl⟩ : syracuseStep 287907 = 431861) B431861
theorem B976049 : Blo 287828 976049 := bstep (se 2 (by rfl) ⟨366018, by rfl⟩ : syracuseStep 976049 = 732037) B732037
theorem B287923 : Blo 287828 287923 := bstep (se 1 (by rfl) ⟨215942, by rfl⟩ : syracuseStep 287923 = 431885) B431885
theorem B287939 : Blo 287828 287939 := bstep (se 1 (by rfl) ⟨215954, by rfl⟩ : syracuseStep 287939 = 431909) B431909
theorem B287955 : Blo 287828 287955 := bstep (se 1 (by rfl) ⟨215966, by rfl⟩ : syracuseStep 287955 = 431933) B431933
theorem B287971 : Blo 287828 287971 := bstep (se 1 (by rfl) ⟨215978, by rfl⟩ : syracuseStep 287971 = 431957) B431957
theorem B287987 : Blo 287828 287987 := bstep (se 1 (by rfl) ⟨215990, by rfl⟩ : syracuseStep 287987 = 431981) B431981
theorem B288003 : Blo 287828 288003 := bstep (se 1 (by rfl) ⟨216002, by rfl⟩ : syracuseStep 288003 = 432005) B432005
theorem B288019 : Blo 287828 288019 := bstep (se 1 (by rfl) ⟨216014, by rfl⟩ : syracuseStep 288019 = 432029) B432029
theorem B288035 : Blo 287828 288035 := bstep (se 1 (by rfl) ⟨216026, by rfl⟩ : syracuseStep 288035 = 432053) B432053
theorem B1238321 : Blo 287828 1238321 := bstep (se 2 (by rfl) ⟨464370, by rfl⟩ : syracuseStep 1238321 = 928741) B928741
theorem B288051 : Blo 287828 288051 := bstep (se 1 (by rfl) ⟨216038, by rfl⟩ : syracuseStep 288051 = 432077) B432077
theorem B288067 : Blo 287828 288067 := bstep (se 1 (by rfl) ⟨216050, by rfl⟩ : syracuseStep 288067 = 432101) B432101
theorem B288083 : Blo 287828 288083 := bstep (se 1 (by rfl) ⟨216062, by rfl⟩ : syracuseStep 288083 = 432125) B432125
theorem B288099 : Blo 287828 288099 := bstep (se 1 (by rfl) ⟨216074, by rfl⟩ : syracuseStep 288099 = 432149) B432149
theorem B550243 : Blo 287828 550243 := bstep (se 1 (by rfl) ⟨412682, by rfl⟩ : syracuseStep 550243 = 825365) B825365
theorem B288115 : Blo 287828 288115 := bstep (se 1 (by rfl) ⟨216086, by rfl⟩ : syracuseStep 288115 = 432173) B432173
theorem B288131 : Blo 287828 288131 := bstep (se 1 (by rfl) ⟨216098, by rfl⟩ : syracuseStep 288131 = 432197) B432197
theorem B648593 : Blo 287828 648593 := bstep (se 2 (by rfl) ⟨243222, by rfl⟩ : syracuseStep 648593 = 486445) B486445
theorem B550289 : Blo 287828 550289 := bstep (se 2 (by rfl) ⟨206358, by rfl⟩ : syracuseStep 550289 = 412717) B412717
theorem B288147 : Blo 287828 288147 := bstep (se 1 (by rfl) ⟨216110, by rfl⟩ : syracuseStep 288147 = 432221) B432221
theorem B288163 : Blo 287828 288163 := bstep (se 1 (by rfl) ⟨216122, by rfl⟩ : syracuseStep 288163 = 432245) B432245
theorem B648611 : Blo 287828 648611 := bstep (se 1 (by rfl) ⟨486458, by rfl⟩ : syracuseStep 648611 = 972917) B972917
theorem B288179 : Blo 287828 288179 := bstep (se 1 (by rfl) ⟨216134, by rfl⟩ : syracuseStep 288179 = 432269) B432269
theorem B288195 : Blo 287828 288195 := bstep (se 1 (by rfl) ⟨216146, by rfl⟩ : syracuseStep 288195 = 432293) B432293
theorem B1861069 : Blo 287828 1861069 := bstep (se 3 (by rfl) ⟨348950, by rfl⟩ : syracuseStep 1861069 = 697901) B697901
theorem B288211 : Blo 287828 288211 := bstep (se 1 (by rfl) ⟨216158, by rfl⟩ : syracuseStep 288211 = 432317) B432317
theorem B288227 : Blo 287828 288227 := bstep (se 1 (by rfl) ⟨216170, by rfl⟩ : syracuseStep 288227 = 432341) B432341
theorem B288243 : Blo 287828 288243 := bstep (se 1 (by rfl) ⟨216182, by rfl⟩ : syracuseStep 288243 = 432365) B432365
theorem B288259 : Blo 287828 288259 := bstep (se 1 (by rfl) ⟨216194, by rfl⟩ : syracuseStep 288259 = 432389) B432389
theorem B288275 : Blo 287828 288275 := bstep (se 1 (by rfl) ⟨216206, by rfl⟩ : syracuseStep 288275 = 432413) B432413
theorem B288291 : Blo 287828 288291 := bstep (se 1 (by rfl) ⟨216218, by rfl⟩ : syracuseStep 288291 = 432437) B432437
theorem B288307 : Blo 287828 288307 := bstep (se 1 (by rfl) ⟨216230, by rfl⟩ : syracuseStep 288307 = 432461) B432461
theorem B288323 : Blo 287828 288323 := bstep (se 1 (by rfl) ⟨216242, by rfl⟩ : syracuseStep 288323 = 432485) B432485
theorem B1107533 : Blo 287828 1107533 := bstep (se 3 (by rfl) ⟨207662, by rfl⟩ : syracuseStep 1107533 = 415325) B415325
theorem B288339 : Blo 287828 288339 := bstep (se 1 (by rfl) ⟨216254, by rfl⟩ : syracuseStep 288339 = 432509) B432509
theorem B288355 : Blo 287828 288355 := bstep (se 1 (by rfl) ⟨216266, by rfl⟩ : syracuseStep 288355 = 432533) B432533
theorem B288371 : Blo 287828 288371 := bstep (se 1 (by rfl) ⟨216278, by rfl⟩ : syracuseStep 288371 = 432557) B432557
theorem B288387 : Blo 287828 288387 := bstep (se 1 (by rfl) ⟨216290, by rfl⟩ : syracuseStep 288387 = 432581) B432581
theorem B288403 : Blo 287828 288403 := bstep (se 1 (by rfl) ⟨216302, by rfl⟩ : syracuseStep 288403 = 432605) B432605
theorem B288419 : Blo 287828 288419 := bstep (se 1 (by rfl) ⟨216314, by rfl⟩ : syracuseStep 288419 = 432629) B432629
theorem B648881 : Blo 287828 648881 := bstep (se 2 (by rfl) ⟨243330, by rfl⟩ : syracuseStep 648881 = 486661) B486661
theorem B550577 : Blo 287828 550577 := bstep (se 2 (by rfl) ⟨206466, by rfl⟩ : syracuseStep 550577 = 412933) B412933
theorem B288435 : Blo 287828 288435 := bstep (se 1 (by rfl) ⟨216326, by rfl⟩ : syracuseStep 288435 = 432653) B432653
theorem B648899 : Blo 287828 648899 := bstep (se 1 (by rfl) ⟨486674, by rfl⟩ : syracuseStep 648899 = 973349) B973349
theorem B288451 : Blo 287828 288451 := bstep (se 1 (by rfl) ⟨216338, by rfl⟩ : syracuseStep 288451 = 432677) B432677
theorem B976589 : Blo 287828 976589 := bstep (se 3 (by rfl) ⟨183110, by rfl⟩ : syracuseStep 976589 = 366221) B366221
theorem B288467 : Blo 287828 288467 := bstep (se 1 (by rfl) ⟨216350, by rfl⟩ : syracuseStep 288467 = 432701) B432701
theorem B288483 : Blo 287828 288483 := bstep (se 1 (by rfl) ⟨216362, by rfl⟩ : syracuseStep 288483 = 432725) B432725
theorem B288499 : Blo 287828 288499 := bstep (se 1 (by rfl) ⟨216374, by rfl⟩ : syracuseStep 288499 = 432749) B432749
theorem B288515 : Blo 287828 288515 := bstep (se 1 (by rfl) ⟨216386, by rfl⟩ : syracuseStep 288515 = 432773) B432773
theorem B976643 : Blo 287828 976643 := bstep (se 1 (by rfl) ⟨732482, by rfl⟩ : syracuseStep 976643 = 1464965) B1464965
theorem B288531 : Blo 287828 288531 := bstep (se 1 (by rfl) ⟨216398, by rfl⟩ : syracuseStep 288531 = 432797) B432797
theorem B288547 : Blo 287828 288547 := bstep (se 1 (by rfl) ⟨216410, by rfl⟩ : syracuseStep 288547 = 432821) B432821
theorem B288563 : Blo 287828 288563 := bstep (se 1 (by rfl) ⟨216422, by rfl⟩ : syracuseStep 288563 = 432845) B432845
theorem B288579 : Blo 287828 288579 := bstep (se 1 (by rfl) ⟨216434, by rfl⟩ : syracuseStep 288579 = 432869) B432869
theorem B288595 : Blo 287828 288595 := bstep (se 1 (by rfl) ⟨216446, by rfl⟩ : syracuseStep 288595 = 432893) B432893
theorem B288611 : Blo 287828 288611 := bstep (se 1 (by rfl) ⟨216458, by rfl⟩ : syracuseStep 288611 = 432917) B432917
theorem B288627 : Blo 287828 288627 := bstep (se 1 (by rfl) ⟨216470, by rfl⟩ : syracuseStep 288627 = 432941) B432941
theorem B288643 : Blo 287828 288643 := bstep (se 1 (by rfl) ⟨216482, by rfl⟩ : syracuseStep 288643 = 432965) B432965
theorem B288659 : Blo 287828 288659 := bstep (se 1 (by rfl) ⟨216494, by rfl⟩ : syracuseStep 288659 = 432989) B432989
theorem B288675 : Blo 287828 288675 := bstep (se 1 (by rfl) ⟨216506, by rfl⟩ : syracuseStep 288675 = 433013) B433013
theorem B747427 : Blo 287828 747427 := bstep (se 1 (by rfl) ⟨560570, by rfl⟩ : syracuseStep 747427 = 1121141) B1121141
theorem B780209 : Blo 287828 780209 := bstep (se 2 (by rfl) ⟨292578, by rfl⟩ : syracuseStep 780209 = 585157) B585157
theorem B288691 : Blo 287828 288691 := bstep (se 1 (by rfl) ⟨216518, by rfl⟩ : syracuseStep 288691 = 433037) B433037
theorem B288707 : Blo 287828 288707 := bstep (se 1 (by rfl) ⟨216530, by rfl⟩ : syracuseStep 288707 = 433061) B433061
theorem B649169 : Blo 287828 649169 := bstep (se 2 (by rfl) ⟨243438, by rfl⟩ : syracuseStep 649169 = 486877) B486877
theorem B288723 : Blo 287828 288723 := bstep (se 1 (by rfl) ⟨216542, by rfl⟩ : syracuseStep 288723 = 433085) B433085
theorem B649187 : Blo 287828 649187 := bstep (se 1 (by rfl) ⟨486890, by rfl⟩ : syracuseStep 649187 = 973781) B973781
theorem B288739 : Blo 287828 288739 := bstep (se 1 (by rfl) ⟨216554, by rfl⟩ : syracuseStep 288739 = 433109) B433109
theorem B288755 : Blo 287828 288755 := bstep (se 1 (by rfl) ⟨216566, by rfl⟩ : syracuseStep 288755 = 433133) B433133
theorem B288771 : Blo 287828 288771 := bstep (se 1 (by rfl) ⟨216578, by rfl⟩ : syracuseStep 288771 = 433157) B433157
theorem B976913 : Blo 287828 976913 := bstep (se 2 (by rfl) ⟨366342, by rfl⟩ : syracuseStep 976913 = 732685) B732685
theorem B288787 : Blo 287828 288787 := bstep (se 1 (by rfl) ⟨216590, by rfl⟩ : syracuseStep 288787 = 433181) B433181
theorem B288803 : Blo 287828 288803 := bstep (se 1 (by rfl) ⟨216602, by rfl⟩ : syracuseStep 288803 = 433205) B433205
theorem B288819 : Blo 287828 288819 := bstep (se 1 (by rfl) ⟨216614, by rfl⟩ : syracuseStep 288819 = 433229) B433229
theorem B288835 : Blo 287828 288835 := bstep (se 1 (by rfl) ⟨216626, by rfl⟩ : syracuseStep 288835 = 433253) B433253
theorem B616529 : Blo 287828 616529 := bstep (se 2 (by rfl) ⟨231198, by rfl⟩ : syracuseStep 616529 = 462397) B462397
theorem B288851 : Blo 287828 288851 := bstep (se 1 (by rfl) ⟨216638, by rfl⟩ : syracuseStep 288851 = 433277) B433277
theorem B616547 : Blo 287828 616547 := bstep (se 1 (by rfl) ⟨462410, by rfl⟩ : syracuseStep 616547 = 924821) B924821
theorem B288867 : Blo 287828 288867 := bstep (se 1 (by rfl) ⟨216650, by rfl⟩ : syracuseStep 288867 = 433301) B433301
theorem B1468529 : Blo 287828 1468529 := bstep (se 2 (by rfl) ⟨550698, by rfl⟩ : syracuseStep 1468529 = 1101397) B1101397
theorem B288883 : Blo 287828 288883 := bstep (se 1 (by rfl) ⟨216662, by rfl⟩ : syracuseStep 288883 = 433325) B433325
theorem B288899 : Blo 287828 288899 := bstep (se 1 (by rfl) ⟨216674, by rfl⟩ : syracuseStep 288899 = 433349) B433349
theorem B288915 : Blo 287828 288915 := bstep (se 1 (by rfl) ⟨216686, by rfl⟩ : syracuseStep 288915 = 433373) B433373
theorem B288931 : Blo 287828 288931 := bstep (se 1 (by rfl) ⟨216698, by rfl⟩ : syracuseStep 288931 = 433397) B433397
theorem B288947 : Blo 287828 288947 := bstep (se 1 (by rfl) ⟨216710, by rfl⟩ : syracuseStep 288947 = 433421) B433421
theorem B288963 : Blo 287828 288963 := bstep (se 1 (by rfl) ⟨216722, by rfl⟩ : syracuseStep 288963 = 433445) B433445
theorem B1239245 : Blo 287828 1239245 := bstep (se 3 (by rfl) ⟨232358, by rfl⟩ : syracuseStep 1239245 = 464717) B464717
theorem B288979 : Blo 287828 288979 := bstep (se 1 (by rfl) ⟨216734, by rfl⟩ : syracuseStep 288979 = 433469) B433469
theorem B288995 : Blo 287828 288995 := bstep (se 1 (by rfl) ⟨216746, by rfl⟩ : syracuseStep 288995 = 433493) B433493
theorem B649457 : Blo 287828 649457 := bstep (se 2 (by rfl) ⟨243546, by rfl⟩ : syracuseStep 649457 = 487093) B487093
theorem B289011 : Blo 287828 289011 := bstep (se 1 (by rfl) ⟨216758, by rfl⟩ : syracuseStep 289011 = 433517) B433517
theorem B649475 : Blo 287828 649475 := bstep (se 1 (by rfl) ⟨487106, by rfl⟩ : syracuseStep 649475 = 974213) B974213
theorem B289027 : Blo 287828 289027 := bstep (se 1 (by rfl) ⟨216770, by rfl⟩ : syracuseStep 289027 = 433541) B433541
theorem B289043 : Blo 287828 289043 := bstep (se 1 (by rfl) ⟨216782, by rfl⟩ : syracuseStep 289043 = 433565) B433565
theorem B289059 : Blo 287828 289059 := bstep (se 1 (by rfl) ⟨216794, by rfl⟩ : syracuseStep 289059 = 433589) B433589
theorem B289075 : Blo 287828 289075 := bstep (se 1 (by rfl) ⟨216806, by rfl⟩ : syracuseStep 289075 = 433613) B433613
theorem B289091 : Blo 287828 289091 := bstep (se 1 (by rfl) ⟨216818, by rfl⟩ : syracuseStep 289091 = 433637) B433637
theorem B289107 : Blo 287828 289107 := bstep (se 1 (by rfl) ⟨216830, by rfl⟩ : syracuseStep 289107 = 433661) B433661
theorem B289123 : Blo 287828 289123 := bstep (se 1 (by rfl) ⟨216842, by rfl⟩ : syracuseStep 289123 = 433685) B433685
theorem B289139 : Blo 287828 289139 := bstep (se 1 (by rfl) ⟨216854, by rfl⟩ : syracuseStep 289139 = 433709) B433709
theorem B289155 : Blo 287828 289155 := bstep (se 1 (by rfl) ⟨216866, by rfl⟩ : syracuseStep 289155 = 433733) B433733
theorem B551299 : Blo 287828 551299 := bstep (se 1 (by rfl) ⟨413474, by rfl⟩ : syracuseStep 551299 = 826949) B826949
theorem B485777 : Blo 287828 485777 := bstep (se 2 (by rfl) ⟨182166, by rfl⟩ : syracuseStep 485777 = 364333) B364333
theorem B289171 : Blo 287828 289171 := bstep (se 1 (by rfl) ⟨216878, by rfl⟩ : syracuseStep 289171 = 433757) B433757
theorem B289187 : Blo 287828 289187 := bstep (se 1 (by rfl) ⟨216890, by rfl⟩ : syracuseStep 289187 = 433781) B433781
theorem B289203 : Blo 287828 289203 := bstep (se 1 (by rfl) ⟨216902, by rfl⟩ : syracuseStep 289203 = 433805) B433805
theorem B289219 : Blo 287828 289219 := bstep (se 1 (by rfl) ⟨216914, by rfl⟩ : syracuseStep 289219 = 433829) B433829
theorem B289235 : Blo 287828 289235 := bstep (se 1 (by rfl) ⟨216926, by rfl⟩ : syracuseStep 289235 = 433853) B433853
theorem B3697123 : Blo 287828 3697123 := bstep (se 1 (by rfl) ⟨2772842, by rfl⟩ : syracuseStep 3697123 = 5545685) B5545685
theorem B289251 : Blo 287828 289251 := bstep (se 1 (by rfl) ⟨216938, by rfl⟩ : syracuseStep 289251 = 433877) B433877
theorem B1993187 : Blo 287828 1993187 := bstep (se 1 (by rfl) ⟨1494890, by rfl⟩ : syracuseStep 1993187 = 2989781) B2989781
theorem B289267 : Blo 287828 289267 := bstep (se 1 (by rfl) ⟨216950, by rfl⟩ : syracuseStep 289267 = 433901) B433901
theorem B289283 : Blo 287828 289283 := bstep (se 1 (by rfl) ⟨216962, by rfl⟩ : syracuseStep 289283 = 433925) B433925
theorem B485905 : Blo 287828 485905 := bstep (se 2 (by rfl) ⟨182214, by rfl⟩ : syracuseStep 485905 = 364429) B364429
theorem B649745 : Blo 287828 649745 := bstep (se 2 (by rfl) ⟨243654, by rfl⟩ : syracuseStep 649745 = 487309) B487309
theorem B289299 : Blo 287828 289299 := bstep (se 1 (by rfl) ⟨216974, by rfl⟩ : syracuseStep 289299 = 433949) B433949
theorem B649763 : Blo 287828 649763 := bstep (se 1 (by rfl) ⟨487322, by rfl⟩ : syracuseStep 649763 = 974645) B974645
theorem B289315 : Blo 287828 289315 := bstep (se 1 (by rfl) ⟨216986, by rfl⟩ : syracuseStep 289315 = 433973) B433973
theorem B977453 : Blo 287828 977453 := bstep (se 3 (by rfl) ⟨183272, by rfl⟩ : syracuseStep 977453 = 366545) B366545
theorem B485939 : Blo 287828 485939 := bstep (se 1 (by rfl) ⟨364454, by rfl⟩ : syracuseStep 485939 = 728909) B728909
theorem B289331 : Blo 287828 289331 := bstep (se 1 (by rfl) ⟨216998, by rfl⟩ : syracuseStep 289331 = 433997) B433997
theorem B289347 : Blo 287828 289347 := bstep (se 1 (by rfl) ⟨217010, by rfl⟩ : syracuseStep 289347 = 434021) B434021
theorem B289363 : Blo 287828 289363 := bstep (se 1 (by rfl) ⟨217022, by rfl⟩ : syracuseStep 289363 = 434045) B434045
theorem B518755 : Blo 287828 518755 := bstep (se 1 (by rfl) ⟨389066, by rfl⟩ : syracuseStep 518755 = 778133) B778133
theorem B289379 : Blo 287828 289379 := bstep (se 1 (by rfl) ⟨217034, by rfl⟩ : syracuseStep 289379 = 434069) B434069
theorem B977507 : Blo 287828 977507 := bstep (se 1 (by rfl) ⟨733130, by rfl⟩ : syracuseStep 977507 = 1466261) B1466261
theorem B289395 : Blo 287828 289395 := bstep (se 1 (by rfl) ⟨217046, by rfl⟩ : syracuseStep 289395 = 434093) B434093
theorem B289411 : Blo 287828 289411 := bstep (se 1 (by rfl) ⟨217058, by rfl⟩ : syracuseStep 289411 = 434117) B434117
theorem B289427 : Blo 287828 289427 := bstep (se 1 (by rfl) ⟨217070, by rfl⟩ : syracuseStep 289427 = 434141) B434141
theorem B289443 : Blo 287828 289443 := bstep (se 1 (by rfl) ⟨217082, by rfl⟩ : syracuseStep 289443 = 434165) B434165
theorem B486067 : Blo 287828 486067 := bstep (se 1 (by rfl) ⟨364550, by rfl⟩ : syracuseStep 486067 = 729101) B729101
theorem B289459 : Blo 287828 289459 := bstep (se 1 (by rfl) ⟨217094, by rfl⟩ : syracuseStep 289459 = 434189) B434189
theorem B289475 : Blo 287828 289475 := bstep (se 1 (by rfl) ⟨217106, by rfl⟩ : syracuseStep 289475 = 434213) B434213
theorem B289491 : Blo 287828 289491 := bstep (se 1 (by rfl) ⟨217118, by rfl⟩ : syracuseStep 289491 = 434237) B434237
theorem B289507 : Blo 287828 289507 := bstep (se 1 (by rfl) ⟨217130, by rfl⟩ : syracuseStep 289507 = 434261) B434261
theorem B289523 : Blo 287828 289523 := bstep (se 1 (by rfl) ⟨217142, by rfl⟩ : syracuseStep 289523 = 434285) B434285
theorem B289539 : Blo 287828 289539 := bstep (se 1 (by rfl) ⟨217154, by rfl⟩ : syracuseStep 289539 = 434309) B434309
theorem B289555 : Blo 287828 289555 := bstep (se 1 (by rfl) ⟨217166, by rfl⟩ : syracuseStep 289555 = 434333) B434333
theorem B289571 : Blo 287828 289571 := bstep (se 1 (by rfl) ⟨217178, by rfl⟩ : syracuseStep 289571 = 434357) B434357
theorem B650033 : Blo 287828 650033 := bstep (se 2 (by rfl) ⟨243762, by rfl⟩ : syracuseStep 650033 = 487525) B487525
theorem B289587 : Blo 287828 289587 := bstep (se 1 (by rfl) ⟨217190, by rfl⟩ : syracuseStep 289587 = 434381) B434381
theorem B7269173 : Blo 287828 7269173 := bstep (se 5 (by rfl) ⟨340742, by rfl⟩ : syracuseStep 7269173 = 681485) B681485
theorem B486209 : Blo 287828 486209 := bstep (se 2 (by rfl) ⟨182328, by rfl⟩ : syracuseStep 486209 = 364657) B364657
theorem B650051 : Blo 287828 650051 := bstep (se 1 (by rfl) ⟨487538, by rfl⟩ : syracuseStep 650051 = 975077) B975077
theorem B289603 : Blo 287828 289603 := bstep (se 1 (by rfl) ⟨217202, by rfl⟩ : syracuseStep 289603 = 434405) B434405
theorem B551747 : Blo 287828 551747 := bstep (se 1 (by rfl) ⟨413810, by rfl⟩ : syracuseStep 551747 = 827621) B827621
theorem B289619 : Blo 287828 289619 := bstep (se 1 (by rfl) ⟨217214, by rfl⟩ : syracuseStep 289619 = 434429) B434429
theorem B289635 : Blo 287828 289635 := bstep (se 1 (by rfl) ⟨217226, by rfl⟩ : syracuseStep 289635 = 434453) B434453
theorem B977777 : Blo 287828 977777 := bstep (se 2 (by rfl) ⟨366666, by rfl⟩ : syracuseStep 977777 = 733333) B733333
theorem B289651 : Blo 287828 289651 := bstep (se 1 (by rfl) ⟨217238, by rfl⟩ : syracuseStep 289651 = 434477) B434477
theorem B289667 : Blo 287828 289667 := bstep (se 1 (by rfl) ⟨217250, by rfl⟩ : syracuseStep 289667 = 434501) B434501
theorem B289683 : Blo 287828 289683 := bstep (se 1 (by rfl) ⟨217262, by rfl⟩ : syracuseStep 289683 = 434525) B434525
theorem B289699 : Blo 287828 289699 := bstep (se 1 (by rfl) ⟨217274, by rfl⟩ : syracuseStep 289699 = 434549) B434549
theorem B289715 : Blo 287828 289715 := bstep (se 1 (by rfl) ⟨217286, by rfl⟩ : syracuseStep 289715 = 434573) B434573
theorem B486337 : Blo 287828 486337 := bstep (se 2 (by rfl) ⟨182376, by rfl⟩ : syracuseStep 486337 = 364753) B364753
theorem B289731 : Blo 287828 289731 := bstep (se 1 (by rfl) ⟨217298, by rfl⟩ : syracuseStep 289731 = 434597) B434597
theorem B289747 : Blo 287828 289747 := bstep (se 1 (by rfl) ⟨217310, by rfl⟩ : syracuseStep 289747 = 434621) B434621
theorem B486371 : Blo 287828 486371 := bstep (se 1 (by rfl) ⟨364778, by rfl⟩ : syracuseStep 486371 = 729557) B729557
theorem B289763 : Blo 287828 289763 := bstep (se 1 (by rfl) ⟨217322, by rfl⟩ : syracuseStep 289763 = 434645) B434645
theorem B289779 : Blo 287828 289779 := bstep (se 1 (by rfl) ⟨217334, by rfl⟩ : syracuseStep 289779 = 434669) B434669
theorem B289795 : Blo 287828 289795 := bstep (se 1 (by rfl) ⟨217346, by rfl⟩ : syracuseStep 289795 = 434693) B434693
theorem B289811 : Blo 287828 289811 := bstep (se 1 (by rfl) ⟨217358, by rfl⟩ : syracuseStep 289811 = 434717) B434717
theorem B289827 : Blo 287828 289827 := bstep (se 1 (by rfl) ⟨217370, by rfl⟩ : syracuseStep 289827 = 434741) B434741
theorem B289843 : Blo 287828 289843 := bstep (se 1 (by rfl) ⟨217382, by rfl⟩ : syracuseStep 289843 = 434765) B434765
theorem B289859 : Blo 287828 289859 := bstep (se 1 (by rfl) ⟨217394, by rfl⟩ : syracuseStep 289859 = 434789) B434789
theorem B650321 : Blo 287828 650321 := bstep (se 2 (by rfl) ⟨243870, by rfl⟩ : syracuseStep 650321 = 487741) B487741
theorem B289875 : Blo 287828 289875 := bstep (se 1 (by rfl) ⟨217406, by rfl⟩ : syracuseStep 289875 = 434813) B434813
theorem B486499 : Blo 287828 486499 := bstep (se 1 (by rfl) ⟨364874, by rfl⟩ : syracuseStep 486499 = 729749) B729749
theorem B650339 : Blo 287828 650339 := bstep (se 1 (by rfl) ⟨487754, by rfl⟩ : syracuseStep 650339 = 975509) B975509
theorem B289891 : Blo 287828 289891 := bstep (se 1 (by rfl) ⟨217418, by rfl⟩ : syracuseStep 289891 = 434837) B434837
theorem B552035 : Blo 287828 552035 := bstep (se 1 (by rfl) ⟨414026, by rfl⟩ : syracuseStep 552035 = 828053) B828053
theorem B289907 : Blo 287828 289907 := bstep (se 1 (by rfl) ⟨217430, by rfl⟩ : syracuseStep 289907 = 434861) B434861
theorem B289923 : Blo 287828 289923 := bstep (se 1 (by rfl) ⟨217442, by rfl⟩ : syracuseStep 289923 = 434885) B434885
theorem B289939 : Blo 287828 289939 := bstep (se 1 (by rfl) ⟨217454, by rfl⟩ : syracuseStep 289939 = 434909) B434909
theorem B289955 : Blo 287828 289955 := bstep (se 1 (by rfl) ⟨217466, by rfl⟩ : syracuseStep 289955 = 434933) B434933
theorem B289971 : Blo 287828 289971 := bstep (se 1 (by rfl) ⟨217478, by rfl⟩ : syracuseStep 289971 = 434957) B434957
theorem B289987 : Blo 287828 289987 := bstep (se 1 (by rfl) ⟨217490, by rfl⟩ : syracuseStep 289987 = 434981) B434981
theorem B290003 : Blo 287828 290003 := bstep (se 1 (by rfl) ⟨217502, by rfl⟩ : syracuseStep 290003 = 435005) B435005
theorem B290019 : Blo 287828 290019 := bstep (se 1 (by rfl) ⟨217514, by rfl⟩ : syracuseStep 290019 = 435029) B435029
theorem B486641 : Blo 287828 486641 := bstep (se 2 (by rfl) ⟨182490, by rfl⟩ : syracuseStep 486641 = 364981) B364981
theorem B290035 : Blo 287828 290035 := bstep (se 1 (by rfl) ⟨217526, by rfl⟩ : syracuseStep 290035 = 435053) B435053
theorem B290051 : Blo 287828 290051 := bstep (se 1 (by rfl) ⟨217538, by rfl⟩ : syracuseStep 290051 = 435077) B435077
theorem B290067 : Blo 287828 290067 := bstep (se 1 (by rfl) ⟨217550, by rfl⟩ : syracuseStep 290067 = 435101) B435101
theorem B290083 : Blo 287828 290083 := bstep (se 1 (by rfl) ⟨217562, by rfl⟩ : syracuseStep 290083 = 435125) B435125
theorem B617777 : Blo 287828 617777 := bstep (se 2 (by rfl) ⟨231666, by rfl⟩ : syracuseStep 617777 = 463333) B463333
theorem B290099 : Blo 287828 290099 := bstep (se 1 (by rfl) ⟨217574, by rfl⟩ : syracuseStep 290099 = 435149) B435149
theorem B290115 : Blo 287828 290115 := bstep (se 1 (by rfl) ⟨217586, by rfl⟩ : syracuseStep 290115 = 435173) B435173
theorem B290131 : Blo 287828 290131 := bstep (se 1 (by rfl) ⟨217598, by rfl⟩ : syracuseStep 290131 = 435197) B435197
theorem B290147 : Blo 287828 290147 := bstep (se 1 (by rfl) ⟨217610, by rfl⟩ : syracuseStep 290147 = 435221) B435221
theorem B486769 : Blo 287828 486769 := bstep (se 2 (by rfl) ⟨182538, by rfl⟩ : syracuseStep 486769 = 365077) B365077
theorem B650609 : Blo 287828 650609 := bstep (se 2 (by rfl) ⟨243978, by rfl⟩ : syracuseStep 650609 = 487957) B487957
theorem B290163 : Blo 287828 290163 := bstep (se 1 (by rfl) ⟨217622, by rfl⟩ : syracuseStep 290163 = 435245) B435245
theorem B650627 : Blo 287828 650627 := bstep (se 1 (by rfl) ⟨487970, by rfl⟩ : syracuseStep 650627 = 975941) B975941
theorem B290179 : Blo 287828 290179 := bstep (se 1 (by rfl) ⟨217634, by rfl⟩ : syracuseStep 290179 = 435269) B435269
theorem B978317 : Blo 287828 978317 := bstep (se 3 (by rfl) ⟨183434, by rfl⟩ : syracuseStep 978317 = 366869) B366869
theorem B486803 : Blo 287828 486803 := bstep (se 1 (by rfl) ⟨365102, by rfl⟩ : syracuseStep 486803 = 730205) B730205
theorem B290195 : Blo 287828 290195 := bstep (se 1 (by rfl) ⟨217646, by rfl⟩ : syracuseStep 290195 = 435293) B435293
theorem B290211 : Blo 287828 290211 := bstep (se 1 (by rfl) ⟨217658, by rfl⟩ : syracuseStep 290211 = 435317) B435317
theorem B290227 : Blo 287828 290227 := bstep (se 1 (by rfl) ⟨217670, by rfl⟩ : syracuseStep 290227 = 435341) B435341
theorem B978371 : Blo 287828 978371 := bstep (se 1 (by rfl) ⟨733778, by rfl⟩ : syracuseStep 978371 = 1467557) B1467557
theorem B290243 : Blo 287828 290243 := bstep (se 1 (by rfl) ⟨217682, by rfl⟩ : syracuseStep 290243 = 435365) B435365
theorem B2223557 : Blo 287828 2223557 := bstep (se 4 (by rfl) ⟨208458, by rfl⟩ : syracuseStep 2223557 = 416917) B416917
theorem B290259 : Blo 287828 290259 := bstep (se 1 (by rfl) ⟨217694, by rfl⟩ : syracuseStep 290259 = 435389) B435389
theorem B290275 : Blo 287828 290275 := bstep (se 1 (by rfl) ⟨217706, by rfl⟩ : syracuseStep 290275 = 435413) B435413
theorem B290291 : Blo 287828 290291 := bstep (se 1 (by rfl) ⟨217718, by rfl⟩ : syracuseStep 290291 = 435437) B435437
theorem B290307 : Blo 287828 290307 := bstep (se 1 (by rfl) ⟨217730, by rfl⟩ : syracuseStep 290307 = 435461) B435461
theorem B486931 : Blo 287828 486931 := bstep (se 1 (by rfl) ⟨365198, by rfl⟩ : syracuseStep 486931 = 730397) B730397
theorem B290323 : Blo 287828 290323 := bstep (se 1 (by rfl) ⟨217742, by rfl⟩ : syracuseStep 290323 = 435485) B435485
theorem B290339 : Blo 287828 290339 := bstep (se 1 (by rfl) ⟨217754, by rfl⟩ : syracuseStep 290339 = 435509) B435509
theorem B1469987 : Blo 287828 1469987 := bstep (se 1 (by rfl) ⟨1102490, by rfl⟩ : syracuseStep 1469987 = 2204981) B2204981
theorem B290355 : Blo 287828 290355 := bstep (se 1 (by rfl) ⟨217766, by rfl⟩ : syracuseStep 290355 = 435533) B435533
theorem B290371 : Blo 287828 290371 := bstep (se 1 (by rfl) ⟨217778, by rfl⟩ : syracuseStep 290371 = 435557) B435557
theorem B290387 : Blo 287828 290387 := bstep (se 1 (by rfl) ⟨217790, by rfl⟩ : syracuseStep 290387 = 435581) B435581
theorem B290403 : Blo 287828 290403 := bstep (se 1 (by rfl) ⟨217802, by rfl⟩ : syracuseStep 290403 = 435605) B435605
theorem B290419 : Blo 287828 290419 := bstep (se 1 (by rfl) ⟨217814, by rfl⟩ : syracuseStep 290419 = 435629) B435629
theorem B290435 : Blo 287828 290435 := bstep (se 1 (by rfl) ⟨217826, by rfl⟩ : syracuseStep 290435 = 435653) B435653
theorem B650897 : Blo 287828 650897 := bstep (se 2 (by rfl) ⟨244086, by rfl⟩ : syracuseStep 650897 = 488173) B488173
theorem B290451 : Blo 287828 290451 := bstep (se 1 (by rfl) ⟨217838, by rfl⟩ : syracuseStep 290451 = 435677) B435677
theorem B487073 : Blo 287828 487073 := bstep (se 2 (by rfl) ⟨182652, by rfl⟩ : syracuseStep 487073 = 365305) B365305
theorem B650915 : Blo 287828 650915 := bstep (se 1 (by rfl) ⟨488186, by rfl⟩ : syracuseStep 650915 = 976373) B976373
theorem B290467 : Blo 287828 290467 := bstep (se 1 (by rfl) ⟨217850, by rfl⟩ : syracuseStep 290467 = 435701) B435701
theorem B290483 : Blo 287828 290483 := bstep (se 1 (by rfl) ⟨217862, by rfl⟩ : syracuseStep 290483 = 435725) B435725
theorem B290499 : Blo 287828 290499 := bstep (se 1 (by rfl) ⟨217874, by rfl⟩ : syracuseStep 290499 = 435749) B435749
theorem B978641 : Blo 287828 978641 := bstep (se 2 (by rfl) ⟨366990, by rfl⟩ : syracuseStep 978641 = 733981) B733981
theorem B290515 : Blo 287828 290515 := bstep (se 1 (by rfl) ⟨217886, by rfl⟩ : syracuseStep 290515 = 435773) B435773
theorem B290531 : Blo 287828 290531 := bstep (se 1 (by rfl) ⟨217898, by rfl⟩ : syracuseStep 290531 = 435797) B435797
theorem B290547 : Blo 287828 290547 := bstep (se 1 (by rfl) ⟨217910, by rfl⟩ : syracuseStep 290547 = 435821) B435821
theorem B290563 : Blo 287828 290563 := bstep (se 1 (by rfl) ⟨217922, by rfl⟩ : syracuseStep 290563 = 435845) B435845
theorem B290579 : Blo 287828 290579 := bstep (se 1 (by rfl) ⟨217934, by rfl⟩ : syracuseStep 290579 = 435869) B435869
theorem B487201 : Blo 287828 487201 := bstep (se 2 (by rfl) ⟨182700, by rfl⟩ : syracuseStep 487201 = 365401) B365401
theorem B290595 : Blo 287828 290595 := bstep (se 1 (by rfl) ⟨217946, by rfl⟩ : syracuseStep 290595 = 435893) B435893
theorem B290611 : Blo 287828 290611 := bstep (se 1 (by rfl) ⟨217958, by rfl⟩ : syracuseStep 290611 = 435917) B435917
theorem B487235 : Blo 287828 487235 := bstep (se 1 (by rfl) ⟨365426, by rfl⟩ : syracuseStep 487235 = 730853) B730853
theorem B290627 : Blo 287828 290627 := bstep (se 1 (by rfl) ⟨217970, by rfl⟩ : syracuseStep 290627 = 435941) B435941
theorem B3305285 : Blo 287828 3305285 := bstep (se 4 (by rfl) ⟨309870, by rfl⟩ : syracuseStep 3305285 = 619741) B619741
theorem B290643 : Blo 287828 290643 := bstep (se 1 (by rfl) ⟨217982, by rfl⟩ : syracuseStep 290643 = 435965) B435965
theorem B290659 : Blo 287828 290659 := bstep (se 1 (by rfl) ⟨217994, by rfl⟩ : syracuseStep 290659 = 435989) B435989
theorem B290675 : Blo 287828 290675 := bstep (se 1 (by rfl) ⟨218006, by rfl⟩ : syracuseStep 290675 = 436013) B436013
theorem B290691 : Blo 287828 290691 := bstep (se 1 (by rfl) ⟨218018, by rfl⟩ : syracuseStep 290691 = 436037) B436037
theorem B290707 : Blo 287828 290707 := bstep (se 1 (by rfl) ⟨218030, by rfl⟩ : syracuseStep 290707 = 436061) B436061
theorem B782243 : Blo 287828 782243 := bstep (se 1 (by rfl) ⟨586682, by rfl⟩ : syracuseStep 782243 = 1173365) B1173365
theorem B290723 : Blo 287828 290723 := bstep (se 1 (by rfl) ⟨218042, by rfl⟩ : syracuseStep 290723 = 436085) B436085
theorem B651185 : Blo 287828 651185 := bstep (se 2 (by rfl) ⟨244194, by rfl⟩ : syracuseStep 651185 = 488389) B488389
theorem B290739 : Blo 287828 290739 := bstep (se 1 (by rfl) ⟨218054, by rfl⟩ : syracuseStep 290739 = 436109) B436109
theorem B487363 : Blo 287828 487363 := bstep (se 1 (by rfl) ⟨365522, by rfl⟩ : syracuseStep 487363 = 731045) B731045
theorem B651203 : Blo 287828 651203 := bstep (se 1 (by rfl) ⟨488402, by rfl⟩ : syracuseStep 651203 = 976805) B976805
theorem B290755 : Blo 287828 290755 := bstep (se 1 (by rfl) ⟨218066, by rfl⟩ : syracuseStep 290755 = 436133) B436133
theorem B290771 : Blo 287828 290771 := bstep (se 1 (by rfl) ⟨218078, by rfl⟩ : syracuseStep 290771 = 436157) B436157
theorem B290787 : Blo 287828 290787 := bstep (se 1 (by rfl) ⟨218090, by rfl⟩ : syracuseStep 290787 = 436181) B436181
theorem B290803 : Blo 287828 290803 := bstep (se 1 (by rfl) ⟨218102, by rfl⟩ : syracuseStep 290803 = 436205) B436205
theorem B290819 : Blo 287828 290819 := bstep (se 1 (by rfl) ⟨218114, by rfl⟩ : syracuseStep 290819 = 436229) B436229
theorem B2191373 : Blo 287828 2191373 := bstep (se 3 (by rfl) ⟨410882, by rfl⟩ : syracuseStep 2191373 = 821765) B821765
theorem B552977 : Blo 287828 552977 := bstep (se 2 (by rfl) ⟨207366, by rfl⟩ : syracuseStep 552977 = 414733) B414733
theorem B290835 : Blo 287828 290835 := bstep (se 1 (by rfl) ⟨218126, by rfl⟩ : syracuseStep 290835 = 436253) B436253
theorem B290851 : Blo 287828 290851 := bstep (se 1 (by rfl) ⟨218138, by rfl⟩ : syracuseStep 290851 = 436277) B436277
theorem B290867 : Blo 287828 290867 := bstep (se 1 (by rfl) ⟨218150, by rfl⟩ : syracuseStep 290867 = 436301) B436301
theorem B290883 : Blo 287828 290883 := bstep (se 1 (by rfl) ⟨218162, by rfl⟩ : syracuseStep 290883 = 436325) B436325
theorem B487505 : Blo 287828 487505 := bstep (se 2 (by rfl) ⟨182814, by rfl⟩ : syracuseStep 487505 = 365629) B365629
theorem B290899 : Blo 287828 290899 := bstep (se 1 (by rfl) ⟨218174, by rfl⟩ : syracuseStep 290899 = 436349) B436349
theorem B290915 : Blo 287828 290915 := bstep (se 1 (by rfl) ⟨218186, by rfl⟩ : syracuseStep 290915 = 436373) B436373
theorem B290931 : Blo 287828 290931 := bstep (se 1 (by rfl) ⟨218198, by rfl⟩ : syracuseStep 290931 = 436397) B436397
theorem B290947 : Blo 287828 290947 := bstep (se 1 (by rfl) ⟨218210, by rfl⟩ : syracuseStep 290947 = 436421) B436421
theorem B290963 : Blo 287828 290963 := bstep (se 1 (by rfl) ⟨218222, by rfl⟩ : syracuseStep 290963 = 436445) B436445
theorem B290979 : Blo 287828 290979 := bstep (se 1 (by rfl) ⟨218234, by rfl⟩ : syracuseStep 290979 = 436469) B436469
theorem B290995 : Blo 287828 290995 := bstep (se 1 (by rfl) ⟨218246, by rfl⟩ : syracuseStep 290995 = 436493) B436493
theorem B291011 : Blo 287828 291011 := bstep (se 1 (by rfl) ⟨218258, by rfl⟩ : syracuseStep 291011 = 436517) B436517
theorem B487633 : Blo 287828 487633 := bstep (se 2 (by rfl) ⟨182862, by rfl⟩ : syracuseStep 487633 = 365725) B365725
theorem B651473 : Blo 287828 651473 := bstep (se 2 (by rfl) ⟨244302, by rfl⟩ : syracuseStep 651473 = 488605) B488605
theorem B291027 : Blo 287828 291027 := bstep (se 1 (by rfl) ⟨218270, by rfl⟩ : syracuseStep 291027 = 436541) B436541
theorem B6254819 : Blo 287828 6254819 := bstep (se 1 (by rfl) ⟨4691114, by rfl⟩ : syracuseStep 6254819 = 9382229) B9382229
theorem B651491 : Blo 287828 651491 := bstep (se 1 (by rfl) ⟨488618, by rfl⟩ : syracuseStep 651491 = 977237) B977237
theorem B291043 : Blo 287828 291043 := bstep (se 1 (by rfl) ⟨218282, by rfl⟩ : syracuseStep 291043 = 436565) B436565
theorem B979181 : Blo 287828 979181 := bstep (se 3 (by rfl) ⟨183596, by rfl⟩ : syracuseStep 979181 = 367193) B367193
theorem B487667 : Blo 287828 487667 := bstep (se 1 (by rfl) ⟨365750, by rfl⟩ : syracuseStep 487667 = 731501) B731501
theorem B291059 : Blo 287828 291059 := bstep (se 1 (by rfl) ⟨218294, by rfl⟩ : syracuseStep 291059 = 436589) B436589
theorem B291075 : Blo 287828 291075 := bstep (se 1 (by rfl) ⟨218306, by rfl⟩ : syracuseStep 291075 = 436613) B436613
theorem B291091 : Blo 287828 291091 := bstep (se 1 (by rfl) ⟨218318, by rfl⟩ : syracuseStep 291091 = 436637) B436637
theorem B979235 : Blo 287828 979235 := bstep (se 1 (by rfl) ⟨734426, by rfl⟩ : syracuseStep 979235 = 1468853) B1468853
theorem B291107 : Blo 287828 291107 := bstep (se 1 (by rfl) ⟨218330, by rfl⟩ : syracuseStep 291107 = 436661) B436661
theorem B291123 : Blo 287828 291123 := bstep (se 1 (by rfl) ⟨218342, by rfl⟩ : syracuseStep 291123 = 436685) B436685
theorem B291139 : Blo 287828 291139 := bstep (se 1 (by rfl) ⟨218354, by rfl⟩ : syracuseStep 291139 = 436709) B436709
theorem B1470797 : Blo 287828 1470797 := bstep (se 3 (by rfl) ⟨275774, by rfl⟩ : syracuseStep 1470797 = 551549) B551549
theorem B323923 : Blo 287828 323923 := bstep (se 1 (by rfl) ⟨242942, by rfl⟩ : syracuseStep 323923 = 485885) B485885
theorem B291155 : Blo 287828 291155 := bstep (se 1 (by rfl) ⟨218366, by rfl⟩ : syracuseStep 291155 = 436733) B436733
theorem B291171 : Blo 287828 291171 := bstep (se 1 (by rfl) ⟨218378, by rfl⟩ : syracuseStep 291171 = 436757) B436757
theorem B487795 : Blo 287828 487795 := bstep (se 1 (by rfl) ⟨365846, by rfl⟩ : syracuseStep 487795 = 731693) B731693
theorem B291187 : Blo 287828 291187 := bstep (se 1 (by rfl) ⟨218390, by rfl⟩ : syracuseStep 291187 = 436781) B436781
theorem B291203 : Blo 287828 291203 := bstep (se 1 (by rfl) ⟨218402, by rfl⟩ : syracuseStep 291203 = 436805) B436805
theorem B291219 : Blo 287828 291219 := bstep (se 1 (by rfl) ⟨218414, by rfl⟩ : syracuseStep 291219 = 436829) B436829
theorem B291235 : Blo 287828 291235 := bstep (se 1 (by rfl) ⟨218426, by rfl⟩ : syracuseStep 291235 = 436853) B436853
theorem B291251 : Blo 287828 291251 := bstep (se 1 (by rfl) ⟨218438, by rfl⟩ : syracuseStep 291251 = 436877) B436877
theorem B291267 : Blo 287828 291267 := bstep (se 1 (by rfl) ⟨218450, by rfl⟩ : syracuseStep 291267 = 436901) B436901
theorem B291283 : Blo 287828 291283 := bstep (se 1 (by rfl) ⟨218462, by rfl⟩ : syracuseStep 291283 = 436925) B436925
theorem B324067 : Blo 287828 324067 := bstep (se 1 (by rfl) ⟨243050, by rfl⟩ : syracuseStep 324067 = 486101) B486101
theorem B291299 : Blo 287828 291299 := bstep (se 1 (by rfl) ⟨218474, by rfl⟩ : syracuseStep 291299 = 436949) B436949
theorem B651761 : Blo 287828 651761 := bstep (se 2 (by rfl) ⟨244410, by rfl⟩ : syracuseStep 651761 = 488821) B488821
theorem B291315 : Blo 287828 291315 := bstep (se 1 (by rfl) ⟨218486, by rfl⟩ : syracuseStep 291315 = 436973) B436973
theorem B487937 : Blo 287828 487937 := bstep (se 2 (by rfl) ⟨182976, by rfl⟩ : syracuseStep 487937 = 365953) B365953
theorem B651779 : Blo 287828 651779 := bstep (se 1 (by rfl) ⟨488834, by rfl⟩ : syracuseStep 651779 = 977669) B977669
theorem B291331 : Blo 287828 291331 := bstep (se 1 (by rfl) ⟨218498, by rfl⟩ : syracuseStep 291331 = 436997) B436997
theorem B291347 : Blo 287828 291347 := bstep (se 1 (by rfl) ⟨218510, by rfl⟩ : syracuseStep 291347 = 437021) B437021
theorem B291363 : Blo 287828 291363 := bstep (se 1 (by rfl) ⟨218522, by rfl⟩ : syracuseStep 291363 = 437045) B437045
theorem B979505 : Blo 287828 979505 := bstep (se 2 (by rfl) ⟨367314, by rfl⟩ : syracuseStep 979505 = 734629) B734629
theorem B291379 : Blo 287828 291379 := bstep (se 1 (by rfl) ⟨218534, by rfl⟩ : syracuseStep 291379 = 437069) B437069
theorem B291395 : Blo 287828 291395 := bstep (se 1 (by rfl) ⟨218546, by rfl⟩ : syracuseStep 291395 = 437093) B437093
theorem B291411 : Blo 287828 291411 := bstep (se 1 (by rfl) ⟨218558, by rfl⟩ : syracuseStep 291411 = 437117) B437117
theorem B291427 : Blo 287828 291427 := bstep (se 1 (by rfl) ⟨218570, by rfl⟩ : syracuseStep 291427 = 437141) B437141
theorem B324211 : Blo 287828 324211 := bstep (se 1 (by rfl) ⟨243158, by rfl⟩ : syracuseStep 324211 = 486317) B486317
theorem B291443 : Blo 287828 291443 := bstep (se 1 (by rfl) ⟨218582, by rfl⟩ : syracuseStep 291443 = 437165) B437165
theorem B488065 : Blo 287828 488065 := bstep (se 2 (by rfl) ⟨183024, by rfl⟩ : syracuseStep 488065 = 366049) B366049
theorem B291459 : Blo 287828 291459 := bstep (se 1 (by rfl) ⟨218594, by rfl⟩ : syracuseStep 291459 = 437189) B437189
theorem B291475 : Blo 287828 291475 := bstep (se 1 (by rfl) ⟨218606, by rfl⟩ : syracuseStep 291475 = 437213) B437213
theorem B488099 : Blo 287828 488099 := bstep (se 1 (by rfl) ⟨366074, by rfl⟩ : syracuseStep 488099 = 732149) B732149
theorem B291491 : Blo 287828 291491 := bstep (se 1 (by rfl) ⟨218618, by rfl⟩ : syracuseStep 291491 = 437237) B437237
theorem B291507 : Blo 287828 291507 := bstep (se 1 (by rfl) ⟨218630, by rfl⟩ : syracuseStep 291507 = 437261) B437261
theorem B291523 : Blo 287828 291523 := bstep (se 1 (by rfl) ⟨218642, by rfl⟩ : syracuseStep 291523 = 437285) B437285
theorem B815825 : Blo 287828 815825 := bstep (se 2 (by rfl) ⟨305934, by rfl⟩ : syracuseStep 815825 = 611869) B611869
theorem B291539 : Blo 287828 291539 := bstep (se 1 (by rfl) ⟨218654, by rfl⟩ : syracuseStep 291539 = 437309) B437309
theorem B291555 : Blo 287828 291555 := bstep (se 1 (by rfl) ⟨218666, by rfl⟩ : syracuseStep 291555 = 437333) B437333
theorem B291571 : Blo 287828 291571 := bstep (se 1 (by rfl) ⟨218678, by rfl⟩ : syracuseStep 291571 = 437357) B437357
theorem B324355 : Blo 287828 324355 := bstep (se 1 (by rfl) ⟨243266, by rfl⟩ : syracuseStep 324355 = 486533) B486533
theorem B291587 : Blo 287828 291587 := bstep (se 1 (by rfl) ⟨218690, by rfl⟩ : syracuseStep 291587 = 437381) B437381
theorem B652049 : Blo 287828 652049 := bstep (se 2 (by rfl) ⟨244518, by rfl⟩ : syracuseStep 652049 = 489037) B489037
theorem B291603 : Blo 287828 291603 := bstep (se 1 (by rfl) ⟨218702, by rfl⟩ : syracuseStep 291603 = 437405) B437405
theorem B488227 : Blo 287828 488227 := bstep (se 1 (by rfl) ⟨366170, by rfl⟩ : syracuseStep 488227 = 732341) B732341
theorem B652067 : Blo 287828 652067 := bstep (se 1 (by rfl) ⟨489050, by rfl⟩ : syracuseStep 652067 = 978101) B978101
theorem B291619 : Blo 287828 291619 := bstep (se 1 (by rfl) ⟨218714, by rfl⟩ : syracuseStep 291619 = 437429) B437429
theorem B291635 : Blo 287828 291635 := bstep (se 1 (by rfl) ⟨218726, by rfl⟩ : syracuseStep 291635 = 437453) B437453
theorem B619331 : Blo 287828 619331 := bstep (se 1 (by rfl) ⟨464498, by rfl⟩ : syracuseStep 619331 = 928997) B928997
theorem B291651 : Blo 287828 291651 := bstep (se 1 (by rfl) ⟨218738, by rfl⟩ : syracuseStep 291651 = 437477) B437477
theorem B291667 : Blo 287828 291667 := bstep (se 1 (by rfl) ⟨218750, by rfl⟩ : syracuseStep 291667 = 437501) B437501
theorem B2356067 : Blo 287828 2356067 := bstep (se 1 (by rfl) ⟨1767050, by rfl⟩ : syracuseStep 2356067 = 3534101) B3534101
theorem B291683 : Blo 287828 291683 := bstep (se 1 (by rfl) ⟨218762, by rfl⟩ : syracuseStep 291683 = 437525) B437525
theorem B291699 : Blo 287828 291699 := bstep (se 1 (by rfl) ⟨218774, by rfl⟩ : syracuseStep 291699 = 437549) B437549
theorem B291715 : Blo 287828 291715 := bstep (se 1 (by rfl) ⟨218786, by rfl⟩ : syracuseStep 291715 = 437573) B437573
theorem B553873 : Blo 287828 553873 := bstep (se 2 (by rfl) ⟨207702, by rfl⟩ : syracuseStep 553873 = 415405) B415405
theorem B324499 : Blo 287828 324499 := bstep (se 1 (by rfl) ⟨243374, by rfl⟩ : syracuseStep 324499 = 486749) B486749
theorem B291731 : Blo 287828 291731 := bstep (se 1 (by rfl) ⟨218798, by rfl⟩ : syracuseStep 291731 = 437597) B437597
theorem B291747 : Blo 287828 291747 := bstep (se 1 (by rfl) ⟨218810, by rfl⟩ : syracuseStep 291747 = 437621) B437621
theorem B488369 : Blo 287828 488369 := bstep (se 2 (by rfl) ⟨183138, by rfl⟩ : syracuseStep 488369 = 366277) B366277
theorem B291763 : Blo 287828 291763 := bstep (se 1 (by rfl) ⟨218822, by rfl⟩ : syracuseStep 291763 = 437645) B437645
theorem B291779 : Blo 287828 291779 := bstep (se 1 (by rfl) ⟨218834, by rfl⟩ : syracuseStep 291779 = 437669) B437669
theorem B291795 : Blo 287828 291795 := bstep (se 1 (by rfl) ⟨218846, by rfl⟩ : syracuseStep 291795 = 437693) B437693
theorem B291811 : Blo 287828 291811 := bstep (se 1 (by rfl) ⟨218858, by rfl⟩ : syracuseStep 291811 = 437717) B437717
theorem B291827 : Blo 287828 291827 := bstep (se 1 (by rfl) ⟨218870, by rfl⟩ : syracuseStep 291827 = 437741) B437741
theorem B324643 : Blo 287828 324643 := bstep (se 1 (by rfl) ⟨243482, by rfl⟩ : syracuseStep 324643 = 486965) B486965
theorem B488497 : Blo 287828 488497 := bstep (se 2 (by rfl) ⟨183186, by rfl⟩ : syracuseStep 488497 = 366373) B366373
theorem B652337 : Blo 287828 652337 := bstep (se 2 (by rfl) ⟨244626, by rfl⟩ : syracuseStep 652337 = 489253) B489253
theorem B652355 : Blo 287828 652355 := bstep (se 1 (by rfl) ⟨489266, by rfl⟩ : syracuseStep 652355 = 978533) B978533
theorem B980045 : Blo 287828 980045 := bstep (se 3 (by rfl) ⟨183758, by rfl⟩ : syracuseStep 980045 = 367517) B367517
theorem B488531 : Blo 287828 488531 := bstep (se 1 (by rfl) ⟨366398, by rfl⟩ : syracuseStep 488531 = 732797) B732797
theorem B980099 : Blo 287828 980099 := bstep (se 1 (by rfl) ⟨735074, by rfl⟩ : syracuseStep 980099 = 1470149) B1470149
theorem B324787 : Blo 287828 324787 := bstep (se 1 (by rfl) ⟨243590, by rfl⟩ : syracuseStep 324787 = 487181) B487181
theorem B488659 : Blo 287828 488659 := bstep (se 1 (by rfl) ⟨366494, by rfl⟩ : syracuseStep 488659 = 732989) B732989
theorem B1242353 : Blo 287828 1242353 := bstep (se 2 (by rfl) ⟨465882, by rfl⟩ : syracuseStep 1242353 = 931765) B931765
theorem B324931 : Blo 287828 324931 := bstep (se 1 (by rfl) ⟨243698, by rfl⟩ : syracuseStep 324931 = 487397) B487397
theorem B652625 : Blo 287828 652625 := bstep (se 2 (by rfl) ⟨244734, by rfl⟩ : syracuseStep 652625 = 489469) B489469
theorem B488801 : Blo 287828 488801 := bstep (se 2 (by rfl) ⟨183300, by rfl⟩ : syracuseStep 488801 = 366601) B366601
theorem B652643 : Blo 287828 652643 := bstep (se 1 (by rfl) ⟨489482, by rfl⟩ : syracuseStep 652643 = 978965) B978965
theorem B980369 : Blo 287828 980369 := bstep (se 2 (by rfl) ⟨367638, by rfl⟩ : syracuseStep 980369 = 735277) B735277
theorem B325075 : Blo 287828 325075 := bstep (se 1 (by rfl) ⟨243806, by rfl⟩ : syracuseStep 325075 = 487613) B487613
theorem B488929 : Blo 287828 488929 := bstep (se 2 (by rfl) ⟨183348, by rfl⟩ : syracuseStep 488929 = 366697) B366697
theorem B488963 : Blo 287828 488963 := bstep (se 1 (by rfl) ⟨366722, by rfl⟩ : syracuseStep 488963 = 733445) B733445
theorem B325219 : Blo 287828 325219 := bstep (se 1 (by rfl) ⟨243914, by rfl⟩ : syracuseStep 325219 = 487829) B487829
theorem B652913 : Blo 287828 652913 := bstep (se 2 (by rfl) ⟨244842, by rfl⟩ : syracuseStep 652913 = 489685) B489685
theorem B489091 : Blo 287828 489091 := bstep (se 1 (by rfl) ⟨366818, by rfl⟩ : syracuseStep 489091 = 733637) B733637
theorem B652931 : Blo 287828 652931 := bstep (se 1 (by rfl) ⟨489698, by rfl⟩ : syracuseStep 652931 = 979397) B979397
theorem B390835 : Blo 287828 390835 := bstep (se 1 (by rfl) ⟨293126, by rfl⟩ : syracuseStep 390835 = 586253) B586253
theorem B325363 : Blo 287828 325363 := bstep (se 1 (by rfl) ⟨244022, by rfl⟩ : syracuseStep 325363 = 488045) B488045
theorem B489233 : Blo 287828 489233 := bstep (se 2 (by rfl) ⟨183462, by rfl⟩ : syracuseStep 489233 = 366925) B366925
theorem B849773 : Blo 287828 849773 := bstep (se 3 (by rfl) ⟨159332, by rfl⟩ : syracuseStep 849773 = 318665) B318665
theorem B325507 : Blo 287828 325507 := bstep (se 1 (by rfl) ⟨244130, by rfl⟩ : syracuseStep 325507 = 488261) B488261
theorem B489361 : Blo 287828 489361 := bstep (se 2 (by rfl) ⟨183510, by rfl⟩ : syracuseStep 489361 = 367021) B367021
theorem B653201 : Blo 287828 653201 := bstep (se 2 (by rfl) ⟨244950, by rfl⟩ : syracuseStep 653201 = 489901) B489901
theorem B653219 : Blo 287828 653219 := bstep (se 1 (by rfl) ⟨489914, by rfl⟩ : syracuseStep 653219 = 979829) B979829
theorem B980909 : Blo 287828 980909 := bstep (se 3 (by rfl) ⟨183920, by rfl⟩ : syracuseStep 980909 = 367841) B367841
theorem B1046449 : Blo 287828 1046449 := bstep (se 2 (by rfl) ⟨392418, by rfl⟩ : syracuseStep 1046449 = 784837) B784837
theorem B489395 : Blo 287828 489395 := bstep (se 1 (by rfl) ⟨367046, by rfl⟩ : syracuseStep 489395 = 734093) B734093
theorem B980963 : Blo 287828 980963 := bstep (se 1 (by rfl) ⟨735722, by rfl⟩ : syracuseStep 980963 = 1471445) B1471445
theorem B2488333 : Blo 287828 2488333 := bstep (se 3 (by rfl) ⟨466562, by rfl⟩ : syracuseStep 2488333 = 933125) B933125
theorem B325651 : Blo 287828 325651 := bstep (se 1 (by rfl) ⟨244238, by rfl⟩ : syracuseStep 325651 = 488477) B488477
theorem B489523 : Blo 287828 489523 := bstep (se 1 (by rfl) ⟨367142, by rfl⟩ : syracuseStep 489523 = 734285) B734285
theorem B1701965 : Blo 287828 1701965 := bstep (se 3 (by rfl) ⟨319118, by rfl⟩ : syracuseStep 1701965 = 638237) B638237
theorem B325795 : Blo 287828 325795 := bstep (se 1 (by rfl) ⟨244346, by rfl⟩ : syracuseStep 325795 = 488693) B488693
theorem B653489 : Blo 287828 653489 := bstep (se 2 (by rfl) ⟨245058, by rfl⟩ : syracuseStep 653489 = 490117) B490117
theorem B489665 : Blo 287828 489665 := bstep (se 2 (by rfl) ⟨183624, by rfl⟩ : syracuseStep 489665 = 367249) B367249
theorem B784579 : Blo 287828 784579 := bstep (se 1 (by rfl) ⟨588434, by rfl⟩ : syracuseStep 784579 = 1176869) B1176869
theorem B653507 : Blo 287828 653507 := bstep (se 1 (by rfl) ⟨490130, by rfl⟩ : syracuseStep 653507 = 980261) B980261
theorem B981233 : Blo 287828 981233 := bstep (se 2 (by rfl) ⟨367962, by rfl⟩ : syracuseStep 981233 = 735925) B735925
theorem B325939 : Blo 287828 325939 := bstep (se 1 (by rfl) ⟨244454, by rfl⟩ : syracuseStep 325939 = 488909) B488909
theorem B489793 : Blo 287828 489793 := bstep (se 2 (by rfl) ⟨183672, by rfl⟩ : syracuseStep 489793 = 367345) B367345
theorem B489827 : Blo 287828 489827 := bstep (se 1 (by rfl) ⟨367370, by rfl⟩ : syracuseStep 489827 = 734741) B734741
theorem B326083 : Blo 287828 326083 := bstep (se 1 (by rfl) ⟨244562, by rfl⟩ : syracuseStep 326083 = 489125) B489125
theorem B653777 : Blo 287828 653777 := bstep (se 2 (by rfl) ⟨245166, by rfl⟩ : syracuseStep 653777 = 490333) B490333
theorem B489955 : Blo 287828 489955 := bstep (se 1 (by rfl) ⟨367466, by rfl⟩ : syracuseStep 489955 = 734933) B734933
theorem B653795 : Blo 287828 653795 := bstep (se 1 (by rfl) ⟨490346, by rfl⟩ : syracuseStep 653795 = 980693) B980693
theorem B1243619 : Blo 287828 1243619 := bstep (se 1 (by rfl) ⟨932714, by rfl⟩ : syracuseStep 1243619 = 1865429) B1865429
theorem B2128355 : Blo 287828 2128355 := bstep (se 1 (by rfl) ⟨1596266, by rfl⟩ : syracuseStep 2128355 = 3192533) B3192533
theorem B326227 : Blo 287828 326227 := bstep (se 1 (by rfl) ⟨244670, by rfl⟩ : syracuseStep 326227 = 489341) B489341
theorem B490097 : Blo 287828 490097 := bstep (se 2 (by rfl) ⟨183786, by rfl⟩ : syracuseStep 490097 = 367573) B367573
theorem B391873 : Blo 287828 391873 := bstep (se 2 (by rfl) ⟨146952, by rfl⟩ : syracuseStep 391873 = 293905) B293905
theorem B391889 : Blo 287828 391889 := bstep (se 2 (by rfl) ⟨146958, by rfl⟩ : syracuseStep 391889 = 293917) B293917
theorem B326371 : Blo 287828 326371 := bstep (se 1 (by rfl) ⟨244778, by rfl⟩ : syracuseStep 326371 = 489557) B489557
theorem B490225 : Blo 287828 490225 := bstep (se 2 (by rfl) ⟨183834, by rfl⟩ : syracuseStep 490225 = 367669) B367669
theorem B654065 : Blo 287828 654065 := bstep (se 2 (by rfl) ⟨245274, by rfl⟩ : syracuseStep 654065 = 490549) B490549
theorem B654083 : Blo 287828 654083 := bstep (se 1 (by rfl) ⟨490562, by rfl⟩ : syracuseStep 654083 = 981125) B981125
theorem B981773 : Blo 287828 981773 := bstep (se 3 (by rfl) ⟨184082, by rfl⟩ : syracuseStep 981773 = 368165) B368165
theorem B490259 : Blo 287828 490259 := bstep (se 1 (by rfl) ⟨367694, by rfl⟩ : syracuseStep 490259 = 735389) B735389
theorem B1211171 : Blo 287828 1211171 := bstep (se 1 (by rfl) ⟨908378, by rfl⟩ : syracuseStep 1211171 = 1816757) B1816757
theorem B981827 : Blo 287828 981827 := bstep (se 1 (by rfl) ⟨736370, by rfl⟩ : syracuseStep 981827 = 1472741) B1472741
theorem B2194289 : Blo 287828 2194289 := bstep (se 2 (by rfl) ⟨822858, by rfl⟩ : syracuseStep 2194289 = 1645717) B1645717
theorem B326515 : Blo 287828 326515 := bstep (se 1 (by rfl) ⟨244886, by rfl⟩ : syracuseStep 326515 = 489773) B489773
theorem B490387 : Blo 287828 490387 := bstep (se 1 (by rfl) ⟨367790, by rfl⟩ : syracuseStep 490387 = 735581) B735581
theorem B621553 : Blo 287828 621553 := bstep (se 2 (by rfl) ⟨233082, by rfl⟩ : syracuseStep 621553 = 466165) B466165
theorem B326659 : Blo 287828 326659 := bstep (se 1 (by rfl) ⟨244994, by rfl⟩ : syracuseStep 326659 = 489989) B489989
theorem B654353 : Blo 287828 654353 := bstep (se 2 (by rfl) ⟨245382, by rfl⟩ : syracuseStep 654353 = 490765) B490765
theorem B490529 : Blo 287828 490529 := bstep (se 2 (by rfl) ⟨183948, by rfl⟩ : syracuseStep 490529 = 367897) B367897
theorem B654371 : Blo 287828 654371 := bstep (se 1 (by rfl) ⟨490778, by rfl⟩ : syracuseStep 654371 = 981557) B981557
theorem B982097 : Blo 287828 982097 := bstep (se 2 (by rfl) ⟨368286, by rfl⟩ : syracuseStep 982097 = 736573) B736573
theorem B326803 : Blo 287828 326803 := bstep (se 1 (by rfl) ⟨245102, by rfl⟩ : syracuseStep 326803 = 490205) B490205
theorem B392353 : Blo 287828 392353 := bstep (se 2 (by rfl) ⟨147132, by rfl⟩ : syracuseStep 392353 = 294265) B294265
theorem B490657 : Blo 287828 490657 := bstep (se 2 (by rfl) ⟨183996, by rfl⟩ : syracuseStep 490657 = 367993) B367993
theorem B1473713 : Blo 287828 1473713 := bstep (se 2 (by rfl) ⟨552642, by rfl⟩ : syracuseStep 1473713 = 1105285) B1105285
theorem B490691 : Blo 287828 490691 := bstep (se 1 (by rfl) ⟨368018, by rfl⟩ : syracuseStep 490691 = 736037) B736037
theorem B326947 : Blo 287828 326947 := bstep (se 1 (by rfl) ⟨245210, by rfl⟩ : syracuseStep 326947 = 490421) B490421
theorem B654641 : Blo 287828 654641 := bstep (se 2 (by rfl) ⟨245490, by rfl⟩ : syracuseStep 654641 = 490981) B490981
theorem B490819 : Blo 287828 490819 := bstep (se 1 (by rfl) ⟨368114, by rfl⟩ : syracuseStep 490819 = 736229) B736229
theorem B654659 : Blo 287828 654659 := bstep (se 1 (by rfl) ⟨490994, by rfl⟩ : syracuseStep 654659 = 981989) B981989
theorem B327091 : Blo 287828 327091 := bstep (se 1 (by rfl) ⟨245318, by rfl⟩ : syracuseStep 327091 = 490637) B490637
theorem B490961 : Blo 287828 490961 := bstep (se 2 (by rfl) ⟨184110, by rfl⟩ : syracuseStep 490961 = 368221) B368221
theorem B327235 : Blo 287828 327235 := bstep (se 1 (by rfl) ⟨245426, by rfl⟩ : syracuseStep 327235 = 490853) B490853
theorem B491089 : Blo 287828 491089 := bstep (se 2 (by rfl) ⟨184158, by rfl⟩ : syracuseStep 491089 = 368317) B368317
theorem B654929 : Blo 287828 654929 := bstep (se 2 (by rfl) ⟨245598, by rfl⟩ : syracuseStep 654929 = 491197) B491197
theorem B654947 : Blo 287828 654947 := bstep (se 1 (by rfl) ⟨491210, by rfl⟩ : syracuseStep 654947 = 982421) B982421
theorem B982637 : Blo 287828 982637 := bstep (se 3 (by rfl) ⟨184244, by rfl⟩ : syracuseStep 982637 = 368489) B368489
theorem B491123 : Blo 287828 491123 := bstep (se 1 (by rfl) ⟨368342, by rfl⟩ : syracuseStep 491123 = 736685) B736685
theorem B982691 : Blo 287828 982691 := bstep (se 1 (by rfl) ⟨737018, by rfl⟩ : syracuseStep 982691 = 1474037) B1474037
theorem B327379 : Blo 287828 327379 := bstep (se 1 (by rfl) ⟨245534, by rfl⟩ : syracuseStep 327379 = 491069) B491069
theorem B491251 : Blo 287828 491251 := bstep (se 1 (by rfl) ⟨368438, by rfl⟩ : syracuseStep 491251 = 736877) B736877
theorem B327523 : Blo 287828 327523 := bstep (se 1 (by rfl) ⟨245642, by rfl⟩ : syracuseStep 327523 = 491285) B491285
theorem B655217 : Blo 287828 655217 := bstep (se 2 (by rfl) ⟨245706, by rfl⟩ : syracuseStep 655217 = 491413) B491413
theorem B491393 : Blo 287828 491393 := bstep (se 2 (by rfl) ⟨184272, by rfl⟩ : syracuseStep 491393 = 368545) B368545
theorem B655235 : Blo 287828 655235 := bstep (se 1 (by rfl) ⟨491426, by rfl⟩ : syracuseStep 655235 = 982853) B982853
theorem B2359181 : Blo 287828 2359181 := bstep (se 3 (by rfl) ⟨442346, by rfl⟩ : syracuseStep 2359181 = 884693) B884693
theorem B982961 : Blo 287828 982961 := bstep (se 2 (by rfl) ⟨368610, by rfl⟩ : syracuseStep 982961 = 737221) B737221
theorem B524227 : Blo 287828 524227 := bstep (se 1 (by rfl) ⟨393170, by rfl⟩ : syracuseStep 524227 = 786341) B786341
theorem B327667 : Blo 287828 327667 := bstep (se 1 (by rfl) ⟨245750, by rfl⟩ : syracuseStep 327667 = 491501) B491501
theorem B655361 : Blo 287828 655361 := bstep (se 2 (by rfl) ⟨245760, by rfl⟩ : syracuseStep 655361 = 491521) B491521
theorem B327703 : Blo 287828 327703 := bstep (se 1 (by rfl) ⟨245777, by rfl⟩ : syracuseStep 327703 = 491555) B491555
theorem B491609 : Blo 287828 491609 := bstep (se 2 (by rfl) ⟨184353, by rfl⟩ : syracuseStep 491609 = 368707) B368707
theorem B1048727 : Blo 287828 1048727 := bstep (se 1 (by rfl) ⟨786545, by rfl⟩ : syracuseStep 1048727 = 1573091) B1573091
theorem B786611 : Blo 287828 786611 := bstep (se 1 (by rfl) ⟨589958, by rfl⟩ : syracuseStep 786611 = 1179917) B1179917
theorem B327883 : Blo 287828 327883 := bstep (se 1 (by rfl) ⟨245912, by rfl⟩ : syracuseStep 327883 = 491825) B491825
theorem B655577 : Blo 287828 655577 := bstep (se 2 (by rfl) ⟨245841, by rfl⟩ : syracuseStep 655577 = 491683) B491683
theorem B491737 : Blo 287828 491737 := bstep (se 2 (by rfl) ⟨184401, by rfl⟩ : syracuseStep 491737 = 368803) B368803
theorem B2195747 : Blo 287828 2195747 := bstep (se 1 (by rfl) ⟨1646810, by rfl⟩ : syracuseStep 2195747 = 3293621) B3293621
theorem B655667 : Blo 287828 655667 := bstep (se 1 (by rfl) ⟨491750, by rfl⟩ : syracuseStep 655667 = 983501) B983501
theorem B327991 : Blo 287828 327991 := bstep (se 1 (by rfl) ⟨245993, by rfl⟩ : syracuseStep 327991 = 491987) B491987
theorem B655703 : Blo 287828 655703 := bstep (se 1 (by rfl) ⟨491777, by rfl⟩ : syracuseStep 655703 = 983555) B983555
theorem B983447 : Blo 287828 983447 := bstep (se 1 (by rfl) ⟨737585, by rfl⟩ : syracuseStep 983447 = 1475171) B1475171
theorem B819659 : Blo 287828 819659 := bstep (se 1 (by rfl) ⟨614744, by rfl⟩ : syracuseStep 819659 = 1229489) B1229489
theorem B328171 : Blo 287828 328171 := bstep (se 1 (by rfl) ⟨246128, by rfl⟩ : syracuseStep 328171 = 492257) B492257
theorem B655883 : Blo 287828 655883 := bstep (se 1 (by rfl) ⟨491912, by rfl⟩ : syracuseStep 655883 = 983825) B983825
theorem B655937 : Blo 287828 655937 := bstep (se 2 (by rfl) ⟨245976, by rfl⟩ : syracuseStep 655937 = 491953) B491953
theorem B328279 : Blo 287828 328279 := bstep (se 1 (by rfl) ⟨246209, by rfl⟩ : syracuseStep 328279 = 492419) B492419
theorem B1049219 : Blo 287828 1049219 := bstep (se 1 (by rfl) ⟨786914, by rfl⟩ : syracuseStep 1049219 = 1573829) B1573829
theorem B492311 : Blo 287828 492311 := bstep (se 1 (by rfl) ⟨369233, by rfl⟩ : syracuseStep 492311 = 738467) B738467
theorem B656153 : Blo 287828 656153 := bstep (se 2 (by rfl) ⟨246057, by rfl⟩ : syracuseStep 656153 = 492115) B492115
theorem B820057 : Blo 287828 820057 := bstep (se 2 (by rfl) ⟨307521, by rfl⟩ : syracuseStep 820057 = 615043) B615043
theorem B656243 : Blo 287828 656243 := bstep (se 1 (by rfl) ⟨492182, by rfl⟩ : syracuseStep 656243 = 984365) B984365
theorem B656279 : Blo 287828 656279 := bstep (se 1 (by rfl) ⟨492209, by rfl⟩ : syracuseStep 656279 = 984419) B984419
theorem B492439 : Blo 287828 492439 := bstep (se 1 (by rfl) ⟨369329, by rfl⟩ : syracuseStep 492439 = 738659) B738659
theorem B983987 : Blo 287828 983987 := bstep (se 1 (by rfl) ⟨737990, by rfl⟩ : syracuseStep 983987 = 1475981) B1475981
theorem B1639385 : Blo 287828 1639385 := bstep (se 2 (by rfl) ⟨614769, by rfl⟩ : syracuseStep 1639385 = 1229539) B1229539
theorem B623627 : Blo 287828 623627 := bstep (se 1 (by rfl) ⟨467720, by rfl⟩ : syracuseStep 623627 = 935441) B935441
theorem B590923 : Blo 287828 590923 := bstep (se 1 (by rfl) ⟨443192, by rfl⟩ : syracuseStep 590923 = 886385) B886385
theorem B656459 : Blo 287828 656459 := bstep (se 1 (by rfl) ⟨492344, by rfl⟩ : syracuseStep 656459 = 984689) B984689
theorem B656513 : Blo 287828 656513 := bstep (se 2 (by rfl) ⟨246192, by rfl⟩ : syracuseStep 656513 = 492385) B492385
theorem B984257 : Blo 287828 984257 := bstep (se 2 (by rfl) ⟨369096, by rfl⟩ : syracuseStep 984257 = 738193) B738193
theorem B3146957 : Blo 287828 3146957 := bstep (se 3 (by rfl) ⟨590054, by rfl⟩ : syracuseStep 3146957 = 1180109) B1180109
theorem B328951 : Blo 287828 328951 := bstep (se 1 (by rfl) ⟨246713, by rfl⟩ : syracuseStep 328951 = 493427) B493427
theorem B3999041 : Blo 287828 3999041 := bstep (se 2 (by rfl) ⟨1499640, by rfl⟩ : syracuseStep 3999041 = 2999281) B2999281
theorem B493015 : Blo 287828 493015 := bstep (se 1 (by rfl) ⟨369761, by rfl⟩ : syracuseStep 493015 = 739523) B739523
theorem B886423 : Blo 287828 886423 := bstep (se 1 (by rfl) ⟨664817, by rfl⟩ : syracuseStep 886423 = 1329635) B1329635
theorem B886493 : Blo 287828 886493 := bstep (se 3 (by rfl) ⟨166217, by rfl⟩ : syracuseStep 886493 = 332435) B332435
theorem B984797 : Blo 287828 984797 := bstep (se 3 (by rfl) ⟨184649, by rfl⟩ : syracuseStep 984797 = 369299) B369299
theorem B1050371 : Blo 287828 1050371 := bstep (se 1 (by rfl) ⟨787778, by rfl⟩ : syracuseStep 1050371 = 1575557) B1575557
theorem B821299 : Blo 287828 821299 := bstep (se 1 (by rfl) ⟨615974, by rfl⟩ : syracuseStep 821299 = 1231949) B1231949
theorem B1050803 : Blo 287828 1050803 := bstep (se 1 (by rfl) ⟨788102, by rfl⟩ : syracuseStep 1050803 = 1576205) B1576205
theorem B2492633 : Blo 287828 2492633 := bstep (se 2 (by rfl) ⟨934737, by rfl⟩ : syracuseStep 2492633 = 1869475) B1869475
theorem B657665 : Blo 287828 657665 := bstep (se 2 (by rfl) ⟨246624, by rfl⟩ : syracuseStep 657665 = 493249) B493249
theorem B1772381 : Blo 287828 1772381 := bstep (se 3 (by rfl) ⟨332321, by rfl⟩ : syracuseStep 1772381 = 664643) B664643
theorem B691673 : Blo 287828 691673 := bstep (se 2 (by rfl) ⟨259377, by rfl⟩ : syracuseStep 691673 = 518755) B518755
theorem B1314269 : Blo 287828 1314269 := bstep (se 3 (by rfl) ⟨246425, by rfl⟩ : syracuseStep 1314269 = 492851) B492851
theorem B462667 : Blo 287828 462667 := bstep (se 1 (by rfl) ⟨347000, by rfl⟩ : syracuseStep 462667 = 694001) B694001
theorem B2101085 : Blo 287828 2101085 := bstep (se 3 (by rfl) ⟨393953, by rfl⟩ : syracuseStep 2101085 = 787907) B787907
theorem B364439 : Blo 287828 364439 := bstep (se 1 (by rfl) ⟨273329, by rfl⟩ : syracuseStep 364439 = 546659) B546659
theorem B462923 : Blo 287828 462923 := bstep (se 1 (by rfl) ⟨347192, by rfl⟩ : syracuseStep 462923 = 694385) B694385
theorem B365143 : Blo 287828 365143 := bstep (se 1 (by rfl) ⟨273857, by rfl⟩ : syracuseStep 365143 = 547715) B547715
theorem B6099697 : Blo 287828 6099697 := bstep (se 2 (by rfl) ⟨2287386, by rfl⟩ : syracuseStep 6099697 = 4574773) B4574773
theorem B21205745 : Blo 287828 21205745 := bstep (se 2 (by rfl) ⟨7952154, by rfl⟩ : syracuseStep 21205745 = 15904309) B15904309
theorem B463627 : Blo 287828 463627 := bstep (se 1 (by rfl) ⟨347720, by rfl⟩ : syracuseStep 463627 = 695441) B695441
theorem B824215 : Blo 287828 824215 := bstep (se 1 (by rfl) ⟨618161, by rfl⟩ : syracuseStep 824215 = 1236323) B1236323
theorem B463897 : Blo 287828 463897 := bstep (se 2 (by rfl) ⟨173961, by rfl⟩ : syracuseStep 463897 = 347923) B347923
theorem B463961 : Blo 287828 463961 := bstep (se 2 (by rfl) ⟨173985, by rfl⟩ : syracuseStep 463961 = 347971) B347971
theorem B1316147 : Blo 287828 1316147 := bstep (se 1 (by rfl) ⟨987110, by rfl⟩ : syracuseStep 1316147 = 1974221) B1974221
theorem B1119539 : Blo 287828 1119539 := bstep (se 1 (by rfl) ⟨839654, by rfl⟩ : syracuseStep 1119539 = 1679309) B1679309
theorem B5051765 : Blo 287828 5051765 := bstep (se 5 (by rfl) ⟨236801, by rfl⟩ : syracuseStep 5051765 = 473603) B473603
theorem B2201093 : Blo 287828 2201093 := bstep (se 4 (by rfl) ⟨206352, by rfl⟩ : syracuseStep 2201093 = 412705) B412705
theorem B2496035 : Blo 287828 2496035 := bstep (se 1 (by rfl) ⟨1872026, by rfl⟩ : syracuseStep 2496035 = 3744053) B3744053
theorem B1644077 : Blo 287828 1644077 := bstep (se 3 (by rfl) ⟨308264, by rfl⟩ : syracuseStep 1644077 = 616529) B616529
theorem B431819 : Blo 287828 431819 := bstep (se 1 (by rfl) ⟨323864, by rfl⟩ : syracuseStep 431819 = 647729) B647729
theorem B431831 : Blo 287828 431831 := bstep (se 1 (by rfl) ⟨323873, by rfl⟩ : syracuseStep 431831 = 647747) B647747
theorem B431897 : Blo 287828 431897 := bstep (se 2 (by rfl) ⟨161961, by rfl⟩ : syracuseStep 431897 = 323923) B323923
theorem B432011 : Blo 287828 432011 := bstep (se 1 (by rfl) ⟨324008, by rfl⟩ : syracuseStep 432011 = 648017) B648017
theorem B432023 : Blo 287828 432023 := bstep (se 1 (by rfl) ⟨324017, by rfl⟩ : syracuseStep 432023 = 648035) B648035
theorem B432089 : Blo 287828 432089 := bstep (se 2 (by rfl) ⟨162033, by rfl⟩ : syracuseStep 432089 = 324067) B324067
theorem B661505 : Blo 287828 661505 := bstep (se 2 (by rfl) ⟨248064, by rfl⟩ : syracuseStep 661505 = 496129) B496129
theorem B432203 : Blo 287828 432203 := bstep (se 1 (by rfl) ⟨324152, by rfl⟩ : syracuseStep 432203 = 648305) B648305
theorem B432215 : Blo 287828 432215 := bstep (se 1 (by rfl) ⟨324161, by rfl⟩ : syracuseStep 432215 = 648323) B648323
theorem B432281 : Blo 287828 432281 := bstep (se 2 (by rfl) ⟨162105, by rfl⟩ : syracuseStep 432281 = 324211) B324211
theorem B825547 : Blo 287828 825547 := bstep (se 1 (by rfl) ⟨619160, by rfl⟩ : syracuseStep 825547 = 1238321) B1238321
theorem B432395 : Blo 287828 432395 := bstep (se 1 (by rfl) ⟨324296, by rfl⟩ : syracuseStep 432395 = 648593) B648593
theorem B366859 : Blo 287828 366859 := bstep (se 1 (by rfl) ⟨275144, by rfl⟩ : syracuseStep 366859 = 550289) B550289
theorem B432407 : Blo 287828 432407 := bstep (se 1 (by rfl) ⟨324305, by rfl⟩ : syracuseStep 432407 = 648611) B648611
theorem B432473 : Blo 287828 432473 := bstep (se 2 (by rfl) ⟨162177, by rfl⟩ : syracuseStep 432473 = 324355) B324355
theorem B432587 : Blo 287828 432587 := bstep (se 1 (by rfl) ⟨324440, by rfl⟩ : syracuseStep 432587 = 648881) B648881
theorem B432599 : Blo 287828 432599 := bstep (se 1 (by rfl) ⟨324449, by rfl⟩ : syracuseStep 432599 = 648899) B648899
theorem B825821 : Blo 287828 825821 := bstep (se 3 (by rfl) ⟨154841, by rfl⟩ : syracuseStep 825821 = 309683) B309683
theorem B432665 : Blo 287828 432665 := bstep (se 2 (by rfl) ⟨162249, by rfl⟩ : syracuseStep 432665 = 324499) B324499
theorem B432779 : Blo 287828 432779 := bstep (se 1 (by rfl) ⟨324584, by rfl⟩ : syracuseStep 432779 = 649169) B649169
theorem B432791 : Blo 287828 432791 := bstep (se 1 (by rfl) ⟨324593, by rfl⟩ : syracuseStep 432791 = 649187) B649187
theorem B432857 : Blo 287828 432857 := bstep (se 2 (by rfl) ⟨162321, by rfl⟩ : syracuseStep 432857 = 324643) B324643
theorem B1120985 : Blo 287828 1120985 := bstep (se 2 (by rfl) ⟨420369, by rfl⟩ : syracuseStep 1120985 = 840739) B840739
theorem B826163 : Blo 287828 826163 := bstep (se 1 (by rfl) ⟨619622, by rfl⟩ : syracuseStep 826163 = 1239245) B1239245
theorem B432971 : Blo 287828 432971 := bstep (se 1 (by rfl) ⟨324728, by rfl⟩ : syracuseStep 432971 = 649457) B649457
theorem B432983 : Blo 287828 432983 := bstep (se 1 (by rfl) ⟨324737, by rfl⟩ : syracuseStep 432983 = 649475) B649475
theorem B2464613 : Blo 287828 2464613 := bstep (se 4 (by rfl) ⟨231057, by rfl⟩ : syracuseStep 2464613 = 462115) B462115
theorem B433049 : Blo 287828 433049 := bstep (se 2 (by rfl) ⟨162393, by rfl⟩ : syracuseStep 433049 = 324787) B324787
theorem B1252313 : Blo 287828 1252313 := bstep (se 2 (by rfl) ⟨469617, by rfl⟩ : syracuseStep 1252313 = 939235) B939235
theorem B433163 : Blo 287828 433163 := bstep (se 1 (by rfl) ⟨324872, by rfl⟩ : syracuseStep 433163 = 649745) B649745
theorem B433175 : Blo 287828 433175 := bstep (se 1 (by rfl) ⟨324881, by rfl⟩ : syracuseStep 433175 = 649763) B649763
theorem B433241 : Blo 287828 433241 := bstep (se 2 (by rfl) ⟨162465, by rfl⟩ : syracuseStep 433241 = 324931) B324931
theorem B433355 : Blo 287828 433355 := bstep (se 1 (by rfl) ⟨325016, by rfl⟩ : syracuseStep 433355 = 650033) B650033
theorem B433367 : Blo 287828 433367 := bstep (se 1 (by rfl) ⟨325025, by rfl⟩ : syracuseStep 433367 = 650051) B650051
theorem B367831 : Blo 287828 367831 := bstep (se 1 (by rfl) ⟨275873, by rfl⟩ : syracuseStep 367831 = 551747) B551747
theorem B433433 : Blo 287828 433433 := bstep (se 2 (by rfl) ⟨162537, by rfl⟩ : syracuseStep 433433 = 325075) B325075
theorem B728371 : Blo 287828 728371 := bstep (se 1 (by rfl) ⟨546278, by rfl⟩ : syracuseStep 728371 = 1092557) B1092557
theorem B433547 : Blo 287828 433547 := bstep (se 1 (by rfl) ⟨325160, by rfl⟩ : syracuseStep 433547 = 650321) B650321
theorem B433559 : Blo 287828 433559 := bstep (se 1 (by rfl) ⟨325169, by rfl⟩ : syracuseStep 433559 = 650339) B650339
theorem B433625 : Blo 287828 433625 := bstep (se 2 (by rfl) ⟨162609, by rfl⟩ : syracuseStep 433625 = 325219) B325219
theorem B433739 : Blo 287828 433739 := bstep (se 1 (by rfl) ⟨325304, by rfl⟩ : syracuseStep 433739 = 650609) B650609
theorem B433751 : Blo 287828 433751 := bstep (se 1 (by rfl) ⟨325313, by rfl⟩ : syracuseStep 433751 = 650627) B650627
theorem B4955741 : Blo 287828 4955741 := bstep (se 3 (by rfl) ⟨929201, by rfl⟩ : syracuseStep 4955741 = 1858403) B1858403
theorem B1482371 : Blo 287828 1482371 := bstep (se 1 (by rfl) ⟨1111778, by rfl⟩ : syracuseStep 1482371 = 2223557) B2223557
theorem B433817 : Blo 287828 433817 := bstep (se 2 (by rfl) ⟨162681, by rfl⟩ : syracuseStep 433817 = 325363) B325363
theorem B433931 : Blo 287828 433931 := bstep (se 1 (by rfl) ⟨325448, by rfl⟩ : syracuseStep 433931 = 650897) B650897
theorem B433943 : Blo 287828 433943 := bstep (se 1 (by rfl) ⟨325457, by rfl⟩ : syracuseStep 433943 = 650915) B650915
theorem B434009 : Blo 287828 434009 := bstep (se 2 (by rfl) ⟨162753, by rfl⟩ : syracuseStep 434009 = 325507) B325507
theorem B2203523 : Blo 287828 2203523 := bstep (se 1 (by rfl) ⟨1652642, by rfl⟩ : syracuseStep 2203523 = 3305285) B3305285
theorem B434123 : Blo 287828 434123 := bstep (se 1 (by rfl) ⟨325592, by rfl⟩ : syracuseStep 434123 = 651185) B651185
theorem B434135 : Blo 287828 434135 := bstep (se 1 (by rfl) ⟨325601, by rfl⟩ : syracuseStep 434135 = 651203) B651203
theorem B368651 : Blo 287828 368651 := bstep (se 1 (by rfl) ⟨276488, by rfl⟩ : syracuseStep 368651 = 552977) B552977
theorem B3317777 : Blo 287828 3317777 := bstep (se 2 (by rfl) ⟨1244166, by rfl⟩ : syracuseStep 3317777 = 2488333) B2488333
theorem B434201 : Blo 287828 434201 := bstep (se 2 (by rfl) ⟨162825, by rfl⟩ : syracuseStep 434201 = 325651) B325651
theorem B434315 : Blo 287828 434315 := bstep (se 1 (by rfl) ⟨325736, by rfl⟩ : syracuseStep 434315 = 651473) B651473
theorem B4169879 : Blo 287828 4169879 := bstep (se 1 (by rfl) ⟨3127409, by rfl⟩ : syracuseStep 4169879 = 6254819) B6254819
theorem B434327 : Blo 287828 434327 := bstep (se 1 (by rfl) ⟨325745, by rfl⟩ : syracuseStep 434327 = 651491) B651491
theorem B1122497 : Blo 287828 1122497 := bstep (se 2 (by rfl) ⟨420936, by rfl⟩ : syracuseStep 1122497 = 841873) B841873
theorem B434393 : Blo 287828 434393 := bstep (se 2 (by rfl) ⟨162897, by rfl⟩ : syracuseStep 434393 = 325795) B325795
theorem B729395 : Blo 287828 729395 := bstep (se 1 (by rfl) ⟨547046, by rfl⟩ : syracuseStep 729395 = 1094093) B1094093
theorem B434507 : Blo 287828 434507 := bstep (se 1 (by rfl) ⟨325880, by rfl⟩ : syracuseStep 434507 = 651761) B651761
theorem B434519 : Blo 287828 434519 := bstep (se 1 (by rfl) ⟨325889, by rfl⟩ : syracuseStep 434519 = 651779) B651779
theorem B434585 : Blo 287828 434585 := bstep (se 2 (by rfl) ⟨162969, by rfl⟩ : syracuseStep 434585 = 325939) B325939
theorem B434699 : Blo 287828 434699 := bstep (se 1 (by rfl) ⟨326024, by rfl⟩ : syracuseStep 434699 = 652049) B652049
theorem B434711 : Blo 287828 434711 := bstep (se 1 (by rfl) ⟨326033, by rfl⟩ : syracuseStep 434711 = 652067) B652067
theorem B77537845 : Blo 287828 77537845 := bstep (se 5 (by rfl) ⟨3634586, by rfl⟩ : syracuseStep 77537845 = 7269173) B7269173
theorem B434777 : Blo 287828 434777 := bstep (se 2 (by rfl) ⟨163041, by rfl⟩ : syracuseStep 434777 = 326083) B326083
theorem B3711581 : Blo 287828 3711581 := bstep (se 3 (by rfl) ⟨695921, by rfl⟩ : syracuseStep 3711581 = 1391843) B1391843
theorem B5415605 : Blo 287828 5415605 := bstep (se 5 (by rfl) ⟨253856, by rfl⟩ : syracuseStep 5415605 = 507713) B507713
theorem B434891 : Blo 287828 434891 := bstep (se 1 (by rfl) ⟨326168, by rfl⟩ : syracuseStep 434891 = 652337) B652337
theorem B434903 : Blo 287828 434903 := bstep (se 1 (by rfl) ⟨326177, by rfl⟩ : syracuseStep 434903 = 652355) B652355
theorem B434969 : Blo 287828 434969 := bstep (se 2 (by rfl) ⟨163113, by rfl⟩ : syracuseStep 434969 = 326227) B326227
theorem B729931 : Blo 287828 729931 := bstep (se 1 (by rfl) ⟨547448, by rfl⟩ : syracuseStep 729931 = 1094897) B1094897
theorem B828235 : Blo 287828 828235 := bstep (se 1 (by rfl) ⟨621176, by rfl⟩ : syracuseStep 828235 = 1242353) B1242353
theorem B435083 : Blo 287828 435083 := bstep (se 1 (by rfl) ⟨326312, by rfl⟩ : syracuseStep 435083 = 652625) B652625
theorem B435095 : Blo 287828 435095 := bstep (se 1 (by rfl) ⟨326321, by rfl⟩ : syracuseStep 435095 = 652643) B652643
theorem B664499 : Blo 287828 664499 := bstep (se 1 (by rfl) ⟨498374, by rfl⟩ : syracuseStep 664499 = 996749) B996749
theorem B730073 : Blo 287828 730073 := bstep (se 2 (by rfl) ⟨273777, by rfl⟩ : syracuseStep 730073 = 547555) B547555
theorem B435161 : Blo 287828 435161 := bstep (se 2 (by rfl) ⟨163185, by rfl⟩ : syracuseStep 435161 = 326371) B326371
theorem B435275 : Blo 287828 435275 := bstep (se 1 (by rfl) ⟨326456, by rfl⟩ : syracuseStep 435275 = 652913) B652913
theorem B435287 : Blo 287828 435287 := bstep (se 1 (by rfl) ⟨326465, by rfl⟩ : syracuseStep 435287 = 652931) B652931
theorem B435353 : Blo 287828 435353 := bstep (se 2 (by rfl) ⟨163257, by rfl⟩ : syracuseStep 435353 = 326515) B326515
theorem B566515 : Blo 287828 566515 := bstep (se 1 (by rfl) ⟨424886, by rfl⟩ : syracuseStep 566515 = 849773) B849773
theorem B435467 : Blo 287828 435467 := bstep (se 1 (by rfl) ⟨326600, by rfl⟩ : syracuseStep 435467 = 653201) B653201
theorem B435479 : Blo 287828 435479 := bstep (se 1 (by rfl) ⟨326609, by rfl⟩ : syracuseStep 435479 = 653219) B653219
theorem B828737 : Blo 287828 828737 := bstep (se 2 (by rfl) ⟨310776, by rfl⟩ : syracuseStep 828737 = 621553) B621553
theorem B435545 : Blo 287828 435545 := bstep (se 2 (by rfl) ⟨163329, by rfl⟩ : syracuseStep 435545 = 326659) B326659
theorem B435659 : Blo 287828 435659 := bstep (se 1 (by rfl) ⟨326744, by rfl⟩ : syracuseStep 435659 = 653489) B653489
theorem B435671 : Blo 287828 435671 := bstep (se 1 (by rfl) ⟨326753, by rfl⟩ : syracuseStep 435671 = 653507) B653507
theorem B435737 : Blo 287828 435737 := bstep (se 2 (by rfl) ⟨163401, by rfl⟩ : syracuseStep 435737 = 326803) B326803
theorem B435851 : Blo 287828 435851 := bstep (se 1 (by rfl) ⟨326888, by rfl⟩ : syracuseStep 435851 = 653777) B653777
theorem B435863 : Blo 287828 435863 := bstep (se 1 (by rfl) ⟨326897, by rfl⟩ : syracuseStep 435863 = 653795) B653795
theorem B829079 : Blo 287828 829079 := bstep (se 1 (by rfl) ⟨621809, by rfl⟩ : syracuseStep 829079 = 1243619) B1243619
theorem B1418903 : Blo 287828 1418903 := bstep (se 1 (by rfl) ⟨1064177, by rfl⟩ : syracuseStep 1418903 = 2128355) B2128355
theorem B435929 : Blo 287828 435929 := bstep (se 2 (by rfl) ⟨163473, by rfl⟩ : syracuseStep 435929 = 326947) B326947
theorem B730903 : Blo 287828 730903 := bstep (se 1 (by rfl) ⟨548177, by rfl⟩ : syracuseStep 730903 = 1096355) B1096355
theorem B436043 : Blo 287828 436043 := bstep (se 1 (by rfl) ⟨327032, by rfl⟩ : syracuseStep 436043 = 654065) B654065
theorem B436055 : Blo 287828 436055 := bstep (se 1 (by rfl) ⟨327041, by rfl⟩ : syracuseStep 436055 = 654083) B654083
theorem B436121 : Blo 287828 436121 := bstep (se 2 (by rfl) ⟨163545, by rfl⟩ : syracuseStep 436121 = 327091) B327091
theorem B436235 : Blo 287828 436235 := bstep (se 1 (by rfl) ⟨327176, by rfl⟩ : syracuseStep 436235 = 654353) B654353
theorem B927767 : Blo 287828 927767 := bstep (se 1 (by rfl) ⟨695825, by rfl⟩ : syracuseStep 927767 = 1391651) B1391651
theorem B436247 : Blo 287828 436247 := bstep (se 1 (by rfl) ⟨327185, by rfl⟩ : syracuseStep 436247 = 654371) B654371
theorem B436313 : Blo 287828 436313 := bstep (se 2 (by rfl) ⟨163617, by rfl⟩ : syracuseStep 436313 = 327235) B327235
theorem B1976413 : Blo 287828 1976413 := bstep (se 3 (by rfl) ⟨370577, by rfl⟩ : syracuseStep 1976413 = 741155) B741155
theorem B436427 : Blo 287828 436427 := bstep (se 1 (by rfl) ⟨327320, by rfl⟩ : syracuseStep 436427 = 654641) B654641
theorem B731339 : Blo 287828 731339 := bstep (se 1 (by rfl) ⟨548504, by rfl⟩ : syracuseStep 731339 = 1097009) B1097009
theorem B436439 : Blo 287828 436439 := bstep (se 1 (by rfl) ⟨327329, by rfl⟩ : syracuseStep 436439 = 654659) B654659
theorem B436505 : Blo 287828 436505 := bstep (se 2 (by rfl) ⟨163689, by rfl⟩ : syracuseStep 436505 = 327379) B327379
theorem B436619 : Blo 287828 436619 := bstep (se 1 (by rfl) ⟨327464, by rfl⟩ : syracuseStep 436619 = 654929) B654929
theorem B436631 : Blo 287828 436631 := bstep (se 1 (by rfl) ⟨327473, by rfl⟩ : syracuseStep 436631 = 654947) B654947
theorem B436697 : Blo 287828 436697 := bstep (se 2 (by rfl) ⟨163761, by rfl⟩ : syracuseStep 436697 = 327523) B327523
theorem B731713 : Blo 287828 731713 := bstep (se 2 (by rfl) ⟨274392, by rfl⟩ : syracuseStep 731713 = 548785) B548785
theorem B928331 : Blo 287828 928331 := bstep (se 1 (by rfl) ⟨696248, by rfl⟩ : syracuseStep 928331 = 1392497) B1392497
theorem B436811 : Blo 287828 436811 := bstep (se 1 (by rfl) ⟨327608, by rfl⟩ : syracuseStep 436811 = 655217) B655217
theorem B436823 : Blo 287828 436823 := bstep (se 1 (by rfl) ⟨327617, by rfl⟩ : syracuseStep 436823 = 655235) B655235
theorem B698969 : Blo 287828 698969 := bstep (se 2 (by rfl) ⟨262113, by rfl⟩ : syracuseStep 698969 = 524227) B524227
theorem B436889 : Blo 287828 436889 := bstep (se 2 (by rfl) ⟨163833, by rfl⟩ : syracuseStep 436889 = 327667) B327667
theorem B1288921 : Blo 287828 1288921 := bstep (se 2 (by rfl) ⟨483345, by rfl⟩ : syracuseStep 1288921 = 966691) B966691
theorem B437003 : Blo 287828 437003 := bstep (se 1 (by rfl) ⟨327752, by rfl⟩ : syracuseStep 437003 = 655505) B655505
theorem B437015 : Blo 287828 437015 := bstep (se 1 (by rfl) ⟨327761, by rfl⟩ : syracuseStep 437015 = 655523) B655523
theorem B437081 : Blo 287828 437081 := bstep (se 2 (by rfl) ⟨163905, by rfl⟩ : syracuseStep 437081 = 327811) B327811
theorem B437195 : Blo 287828 437195 := bstep (se 1 (by rfl) ⟨327896, by rfl⟩ : syracuseStep 437195 = 655793) B655793
theorem B437207 : Blo 287828 437207 := bstep (se 1 (by rfl) ⟨327905, by rfl⟩ : syracuseStep 437207 = 655811) B655811
theorem B437273 : Blo 287828 437273 := bstep (se 2 (by rfl) ⟨163977, by rfl⟩ : syracuseStep 437273 = 327955) B327955
theorem B437387 : Blo 287828 437387 := bstep (se 1 (by rfl) ⟨328040, by rfl⟩ : syracuseStep 437387 = 656081) B656081
theorem B732311 : Blo 287828 732311 := bstep (se 1 (by rfl) ⟨549233, by rfl⟩ : syracuseStep 732311 = 1098467) B1098467
theorem B437399 : Blo 287828 437399 := bstep (se 1 (by rfl) ⟨328049, by rfl⟩ : syracuseStep 437399 = 656099) B656099
theorem B2206925 : Blo 287828 2206925 := bstep (se 3 (by rfl) ⟨413798, by rfl⟩ : syracuseStep 2206925 = 827597) B827597
theorem B437465 : Blo 287828 437465 := bstep (se 2 (by rfl) ⟨164049, by rfl⟩ : syracuseStep 437465 = 328099) B328099
theorem B437579 : Blo 287828 437579 := bstep (se 1 (by rfl) ⟨328184, by rfl⟩ : syracuseStep 437579 = 656369) B656369
theorem B437591 : Blo 287828 437591 := bstep (se 1 (by rfl) ⟨328193, by rfl⟩ : syracuseStep 437591 = 656387) B656387
theorem B1092953 : Blo 287828 1092953 := bstep (se 2 (by rfl) ⟨409857, by rfl⟩ : syracuseStep 1092953 = 819715) B819715
theorem B437657 : Blo 287828 437657 := bstep (se 2 (by rfl) ⟨164121, by rfl⟩ : syracuseStep 437657 = 328243) B328243
theorem B700055 : Blo 287828 700055 := bstep (se 1 (by rfl) ⟨525041, by rfl⟩ : syracuseStep 700055 = 1050083) B1050083
theorem B2207411 : Blo 287828 2207411 := bstep (se 1 (by rfl) ⟨1655558, by rfl⟩ : syracuseStep 2207411 = 3311117) B3311117
theorem B733121 : Blo 287828 733121 := bstep (se 2 (by rfl) ⟨274920, by rfl⟩ : syracuseStep 733121 = 549841) B549841
theorem B929971 : Blo 287828 929971 := bstep (se 1 (by rfl) ⟨697478, by rfl⟩ : syracuseStep 929971 = 1394957) B1394957
theorem B930113 : Blo 287828 930113 := bstep (se 2 (by rfl) ⟨348792, by rfl⟩ : syracuseStep 930113 = 697585) B697585
theorem B733657 : Blo 287828 733657 := bstep (se 2 (by rfl) ⟨275121, by rfl⟩ : syracuseStep 733657 = 550243) B550243
theorem B1684061 : Blo 287828 1684061 := bstep (se 3 (by rfl) ⟨315761, by rfl⟩ : syracuseStep 1684061 = 631523) B631523
theorem B701131 : Blo 287828 701131 := bstep (se 1 (by rfl) ⟨525848, by rfl⟩ : syracuseStep 701131 = 1051697) B1051697
theorem B8303309 : Blo 287828 8303309 := bstep (se 3 (by rfl) ⟨1556870, by rfl⟩ : syracuseStep 8303309 = 3113741) B3113741
theorem B1651549 : Blo 287828 1651549 := bstep (se 3 (by rfl) ⟨309665, by rfl⟩ : syracuseStep 1651549 = 619331) B619331
theorem B1094579 : Blo 287828 1094579 := bstep (se 1 (by rfl) ⟨820934, by rfl⟩ : syracuseStep 1094579 = 1641869) B1641869
theorem B1094593 : Blo 287828 1094593 := bstep (se 2 (by rfl) ⟨410472, by rfl⟩ : syracuseStep 1094593 = 820945) B820945
theorem B308171 : Blo 287828 308171 := bstep (se 1 (by rfl) ⟨231128, by rfl⟩ : syracuseStep 308171 = 462257) B462257
theorem B439319 : Blo 287828 439319 := bstep (se 1 (by rfl) ⟨329489, by rfl⟩ : syracuseStep 439319 = 658979) B658979
theorem B2208869 : Blo 287828 2208869 := bstep (se 4 (by rfl) ⟨207081, by rfl⟩ : syracuseStep 2208869 = 414163) B414163
theorem B439447 : Blo 287828 439447 := bstep (se 1 (by rfl) ⟨329585, by rfl⟩ : syracuseStep 439447 = 659171) B659171
theorem B996569 : Blo 287828 996569 := bstep (se 2 (by rfl) ⟨373713, by rfl⟩ : syracuseStep 996569 = 747427) B747427
theorem B734771 : Blo 287828 734771 := bstep (se 1 (by rfl) ⟨551078, by rfl⟩ : syracuseStep 734771 = 1102157) B1102157
theorem B2209355 : Blo 287828 2209355 := bstep (se 1 (by rfl) ⟨1657016, by rfl⟩ : syracuseStep 2209355 = 3314033) B3314033
theorem B735065 : Blo 287828 735065 := bstep (se 2 (by rfl) ⟨275649, by rfl⟩ : syracuseStep 735065 = 551299) B551299
theorem B4929497 : Blo 287828 4929497 := bstep (se 2 (by rfl) ⟨1848561, by rfl⟩ : syracuseStep 4929497 = 3697123) B3697123
theorem B4995107 : Blo 287828 4995107 := bstep (se 1 (by rfl) ⟨3746330, by rfl⟩ : syracuseStep 4995107 = 7492661) B7492661
theorem B997469 : Blo 287828 997469 := bstep (se 3 (by rfl) ⟨187025, by rfl⟩ : syracuseStep 997469 = 374051) B374051
theorem B309367 : Blo 287828 309367 := bstep (se 1 (by rfl) ⟨232025, by rfl⟩ : syracuseStep 309367 = 464051) B464051
theorem B932573 : Blo 287828 932573 := bstep (se 3 (by rfl) ⟨174857, by rfl⟩ : syracuseStep 932573 = 349715) B349715
theorem B1096523 : Blo 287828 1096523 := bstep (se 1 (by rfl) ⟨822392, by rfl⟩ : syracuseStep 1096523 = 1644785) B1644785
theorem B1096537 : Blo 287828 1096537 := bstep (se 2 (by rfl) ⟨411201, by rfl⟩ : syracuseStep 1096537 = 822403) B822403
theorem B310187 : Blo 287828 310187 := bstep (se 1 (by rfl) ⟨232640, by rfl⟩ : syracuseStep 310187 = 465281) B465281
theorem B3980249 : Blo 287828 3980249 := bstep (se 2 (by rfl) ⟨1492593, by rfl⟩ : syracuseStep 3980249 = 2985187) B2985187
theorem B310315 : Blo 287828 310315 := bstep (se 1 (by rfl) ⟨232736, by rfl⟩ : syracuseStep 310315 = 465473) B465473
theorem B12041621 : Blo 287828 12041621 := bstep (se 6 (by rfl) ⟨282225, by rfl⟩ : syracuseStep 12041621 = 564451) B564451
theorem B835009 : Blo 287828 835009 := bstep (se 2 (by rfl) ⟨313128, by rfl⟩ : syracuseStep 835009 = 626257) B626257
theorem B736715 : Blo 287828 736715 := bstep (se 1 (by rfl) ⟨552536, by rfl⟩ : syracuseStep 736715 = 1105073) B1105073
theorem B1097495 : Blo 287828 1097495 := bstep (se 1 (by rfl) ⟨823121, by rfl⟩ : syracuseStep 1097495 = 1646243) B1646243
theorem B4702529 : Blo 287828 4702529 := bstep (se 2 (by rfl) ⟨1763448, by rfl⟩ : syracuseStep 4702529 = 3526897) B3526897
theorem B737687 : Blo 287828 737687 := bstep (se 1 (by rfl) ⟨553265, by rfl⟩ : syracuseStep 737687 = 1106531) B1106531
theorem B836119 : Blo 287828 836119 := bstep (se 1 (by rfl) ⟨627089, by rfl⟩ : syracuseStep 836119 = 1254179) B1254179
theorem B442955 : Blo 287828 442955 := bstep (se 1 (by rfl) ⟨332216, by rfl⟩ : syracuseStep 442955 = 664433) B664433
theorem B410393 : Blo 287828 410393 := bstep (se 2 (by rfl) ⟨153897, by rfl⟩ : syracuseStep 410393 = 307795) B307795
theorem B1852253 : Blo 287828 1852253 := bstep (se 3 (by rfl) ⟨347297, by rfl⟩ : syracuseStep 1852253 = 694595) B694595
theorem B639859 : Blo 287828 639859 := bstep (se 1 (by rfl) ⟨479894, by rfl⟩ : syracuseStep 639859 = 959789) B959789
theorem B1098755 : Blo 287828 1098755 := bstep (se 1 (by rfl) ⟨824066, by rfl⟩ : syracuseStep 1098755 = 1648133) B1648133
theorem B1557521 : Blo 287828 1557521 := bstep (se 2 (by rfl) ⟨584070, by rfl⟩ : syracuseStep 1557521 = 1168141) B1168141
theorem B738355 : Blo 287828 738355 := bstep (se 1 (by rfl) ⟨553766, by rfl⟩ : syracuseStep 738355 = 1107533) B1107533
theorem B2671795 : Blo 287828 2671795 := bstep (se 1 (by rfl) ⟨2003846, by rfl⟩ : syracuseStep 2671795 = 4007693) B4007693
theorem B738497 : Blo 287828 738497 := bstep (se 2 (by rfl) ⟨276936, by rfl⟩ : syracuseStep 738497 = 553873) B553873
theorem B1230173 : Blo 287828 1230173 := bstep (se 3 (by rfl) ⟨230657, by rfl⟩ : syracuseStep 1230173 = 461315) B461315
theorem B411031 : Blo 287828 411031 := bstep (se 1 (by rfl) ⟨308273, by rfl⟩ : syracuseStep 411031 = 616547) B616547
theorem B706099 : Blo 287828 706099 := bstep (se 1 (by rfl) ⟨529574, by rfl⟩ : syracuseStep 706099 = 1059149) B1059149
theorem B1328791 : Blo 287828 1328791 := bstep (se 1 (by rfl) ⟨996593, by rfl⟩ : syracuseStep 1328791 = 1993187) B1993187
theorem B4835057 : Blo 287828 4835057 := bstep (se 2 (by rfl) ⟨1813146, by rfl⟩ : syracuseStep 4835057 = 3626293) B3626293
theorem B1230871 : Blo 287828 1230871 := bstep (se 1 (by rfl) ⟨923153, by rfl⟩ : syracuseStep 1230871 = 1846307) B1846307
theorem B3229789 : Blo 287828 3229789 := bstep (se 3 (by rfl) ⟨605585, by rfl⟩ : syracuseStep 3229789 = 1211171) B1211171
theorem B411851 : Blo 287828 411851 := bstep (se 1 (by rfl) ⟨308888, by rfl⟩ : syracuseStep 411851 = 617777) B617777
theorem B1460753 : Blo 287828 1460753 := bstep (se 2 (by rfl) ⟨547782, by rfl⟩ : syracuseStep 1460753 = 1095565) B1095565
theorem B1395265 : Blo 287828 1395265 := bstep (se 2 (by rfl) ⟨523224, by rfl⟩ : syracuseStep 1395265 = 1046449) B1046449
theorem B1460915 : Blo 287828 1460915 := bstep (se 1 (by rfl) ⟨1095686, by rfl⟩ : syracuseStep 1460915 = 2191373) B2191373
theorem B2214701 : Blo 287828 2214701 := bstep (se 3 (by rfl) ⟨415256, by rfl⟩ : syracuseStep 2214701 = 830513) B830513
theorem B707417 : Blo 287828 707417 := bstep (se 2 (by rfl) ⟨265281, by rfl⟩ : syracuseStep 707417 = 530563) B530563
theorem B3689333 : Blo 287828 3689333 := bstep (se 5 (by rfl) ⟨172937, by rfl⟩ : syracuseStep 3689333 = 345875) B345875
theorem B543883 : Blo 287828 543883 := bstep (se 1 (by rfl) ⟨407912, by rfl⟩ : syracuseStep 543883 = 815825) B815825
theorem B8539505 : Blo 287828 8539505 := bstep (se 2 (by rfl) ⟨3202314, by rfl⟩ : syracuseStep 8539505 = 6404629) B6404629
theorem B1232273 : Blo 287828 1232273 := bstep (se 2 (by rfl) ⟨462102, by rfl⟩ : syracuseStep 1232273 = 924205) B924205
theorem B1855021 : Blo 287828 1855021 := bstep (se 3 (by rfl) ⟨347816, by rfl⟩ : syracuseStep 1855021 = 695633) B695633
theorem B2084453 : Blo 287828 2084453 := bstep (se 4 (by rfl) ⟨195417, by rfl⟩ : syracuseStep 2084453 = 390835) B390835
theorem B2346853 : Blo 287828 2346853 := bstep (se 4 (by rfl) ⟨220017, by rfl⟩ : syracuseStep 2346853 = 440035) B440035
theorem B1101869 : Blo 287828 1101869 := bstep (se 3 (by rfl) ⟨206600, by rfl⟩ : syracuseStep 1101869 = 413201) B413201
theorem B1134643 : Blo 287828 1134643 := bstep (se 1 (by rfl) ⟨850982, by rfl⟩ : syracuseStep 1134643 = 1701965) B1701965
theorem B1167833 : Blo 287828 1167833 := bstep (se 2 (by rfl) ⟨437937, by rfl⟩ : syracuseStep 1167833 = 875875) B875875
theorem B447001 : Blo 287828 447001 := bstep (se 2 (by rfl) ⟨167625, by rfl⟩ : syracuseStep 447001 = 335251) B335251
theorem B1462859 : Blo 287828 1462859 := bstep (se 1 (by rfl) ⟨1097144, by rfl⟩ : syracuseStep 1462859 = 2194289) B2194289
theorem B2347699 : Blo 287828 2347699 := bstep (se 1 (by rfl) ⟨1760774, by rfl⟩ : syracuseStep 2347699 = 3521549) B3521549
theorem B1102643 : Blo 287828 1102643 := bstep (se 1 (by rfl) ⟨826982, by rfl⟩ : syracuseStep 1102643 = 1653965) B1653965
theorem B972107 : Blo 287828 972107 := bstep (se 1 (by rfl) ⟨729080, by rfl⟩ : syracuseStep 972107 = 1458161) B1458161
theorem B2479511 : Blo 287828 2479511 := bstep (se 1 (by rfl) ⟨1859633, by rfl⟩ : syracuseStep 2479511 = 3719267) B3719267
theorem B710039 : Blo 287828 710039 := bstep (se 1 (by rfl) ⟨532529, by rfl⟩ : syracuseStep 710039 = 1065059) B1065059
theorem B349643 : Blo 287828 349643 := bstep (se 1 (by rfl) ⟨262232, by rfl⟩ : syracuseStep 349643 = 524465) B524465
theorem B26891747 : Blo 287828 26891747 := bstep (se 1 (by rfl) ⟨20168810, by rfl⟩ : syracuseStep 26891747 = 40337621) B40337621
theorem B972377 : Blo 287828 972377 := bstep (se 2 (by rfl) ⟨364641, by rfl⟩ : syracuseStep 972377 = 729283) B729283
theorem B2807557 : Blo 287828 2807557 := bstep (se 4 (by rfl) ⟨263208, by rfl⟩ : syracuseStep 2807557 = 526417) B526417
theorem B546583 : Blo 287828 546583 := bstep (se 1 (by rfl) ⟨409937, by rfl⟩ : syracuseStep 546583 = 819875) B819875
theorem B546689 : Blo 287828 546689 := bstep (se 2 (by rfl) ⟨205008, by rfl⟩ : syracuseStep 546689 = 410017) B410017
theorem B1857431 : Blo 287828 1857431 := bstep (se 1 (by rfl) ⟨1393073, by rfl⟩ : syracuseStep 1857431 = 2786147) B2786147
theorem B1660823 : Blo 287828 1660823 := bstep (se 1 (by rfl) ⟨1245617, by rfl⟩ : syracuseStep 1660823 = 2491235) B2491235
theorem B5593049 : Blo 287828 5593049 := bstep (se 2 (by rfl) ⟨2097393, by rfl⟩ : syracuseStep 5593049 = 4194787) B4194787
theorem B546841 : Blo 287828 546841 := bstep (se 2 (by rfl) ⟨205065, by rfl⟩ : syracuseStep 546841 = 410131) B410131
theorem B1104131 : Blo 287828 1104131 := bstep (se 1 (by rfl) ⟨828098, by rfl⟩ : syracuseStep 1104131 = 1656197) B1656197
theorem B973079 : Blo 287828 973079 := bstep (se 1 (by rfl) ⟨729809, by rfl⟩ : syracuseStep 973079 = 1459619) B1459619
theorem B2283821 : Blo 287828 2283821 := bstep (se 3 (by rfl) ⟨428216, by rfl⟩ : syracuseStep 2283821 = 856433) B856433
theorem B1235245 : Blo 287828 1235245 := bstep (se 3 (by rfl) ⟨231608, by rfl⟩ : syracuseStep 1235245 = 463217) B463217
theorem B1464641 : Blo 287828 1464641 := bstep (se 2 (by rfl) ⟨549240, by rfl⟩ : syracuseStep 1464641 = 1098481) B1098481
theorem B1989137 : Blo 287828 1989137 := bstep (se 2 (by rfl) ⟨745926, by rfl⟩ : syracuseStep 1989137 = 1491853) B1491853
theorem B1235587 : Blo 287828 1235587 := bstep (se 1 (by rfl) ⟨926690, by rfl⟩ : syracuseStep 1235587 = 1853381) B1853381
theorem B1104587 : Blo 287828 1104587 := bstep (se 1 (by rfl) ⟨828440, by rfl⟩ : syracuseStep 1104587 = 1656881) B1656881
theorem B973619 : Blo 287828 973619 := bstep (se 1 (by rfl) ⟨730214, by rfl⟩ : syracuseStep 973619 = 1460429) B1460429
theorem B1170251 : Blo 287828 1170251 := bstep (se 1 (by rfl) ⟨877688, by rfl⟩ : syracuseStep 1170251 = 1755377) B1755377
theorem B1104785 : Blo 287828 1104785 := bstep (se 2 (by rfl) ⟨414294, by rfl⟩ : syracuseStep 1104785 = 828589) B828589
theorem B973889 : Blo 287828 973889 := bstep (se 2 (by rfl) ⟨365208, by rfl⟩ : syracuseStep 973889 = 730417) B730417
theorem B2186513 : Blo 287828 2186513 := bstep (se 2 (by rfl) ⟨819942, by rfl⟩ : syracuseStep 2186513 = 1639885) B1639885
theorem B2481425 : Blo 287828 2481425 := bstep (se 2 (by rfl) ⟨930534, by rfl⟩ : syracuseStep 2481425 = 1861069) B1861069
theorem B548147 : Blo 287828 548147 := bstep (se 1 (by rfl) ⟨411110, by rfl⟩ : syracuseStep 548147 = 822221) B822221
theorem B548299 : Blo 287828 548299 := bstep (se 1 (by rfl) ⟨411224, by rfl⟩ : syracuseStep 548299 = 822449) B822449
theorem B1236545 : Blo 287828 1236545 := bstep (se 2 (by rfl) ⟨463704, by rfl⟩ : syracuseStep 1236545 = 927409) B927409
theorem B974429 : Blo 287828 974429 := bstep (se 3 (by rfl) ⟨182705, by rfl⟩ : syracuseStep 974429 = 365411) B365411
theorem B1105559 : Blo 287828 1105559 := bstep (se 1 (by rfl) ⟨829169, by rfl⟩ : syracuseStep 1105559 = 1658339) B1658339
theorem B548633 : Blo 287828 548633 := bstep (se 2 (by rfl) ⟨205737, by rfl⟩ : syracuseStep 548633 = 411475) B411475
theorem B1105757 : Blo 287828 1105757 := bstep (se 3 (by rfl) ⟨207329, by rfl⟩ : syracuseStep 1105757 = 414659) B414659
theorem B1859429 : Blo 287828 1859429 := bstep (se 4 (by rfl) ⟨174321, by rfl⟩ : syracuseStep 1859429 = 348643) B348643
theorem B1171351 : Blo 287828 1171351 := bstep (se 1 (by rfl) ⟨878513, by rfl⟩ : syracuseStep 1171351 = 1757027) B1757027
theorem B941975 : Blo 287828 941975 := bstep (se 1 (by rfl) ⟨706481, by rfl⟩ : syracuseStep 941975 = 1412963) B1412963
theorem B2089091 : Blo 287828 2089091 := bstep (se 1 (by rfl) ⟨1566818, by rfl⟩ : syracuseStep 2089091 = 3133637) B3133637
theorem B1466585 : Blo 287828 1466585 := bstep (se 2 (by rfl) ⟨549969, by rfl⟩ : syracuseStep 1466585 = 1099939) B1099939
theorem B876851 : Blo 287828 876851 := bstep (se 1 (by rfl) ⟨657638, by rfl⟩ : syracuseStep 876851 = 1315277) B1315277
theorem B5005633 : Blo 287828 5005633 := bstep (se 2 (by rfl) ⟨1877112, by rfl⟩ : syracuseStep 5005633 = 3754225) B3754225
theorem B1171805 : Blo 287828 1171805 := bstep (se 3 (by rfl) ⟨219713, by rfl⟩ : syracuseStep 1171805 = 439427) B439427
theorem B549271 : Blo 287828 549271 := bstep (se 1 (by rfl) ⟨411953, by rfl⟩ : syracuseStep 549271 = 823907) B823907
theorem B778675 : Blo 287828 778675 := bstep (se 1 (by rfl) ⟨584006, by rfl⟩ : syracuseStep 778675 = 1168013) B1168013
theorem B647639 : Blo 287828 647639 := bstep (se 1 (by rfl) ⟨485729, by rfl⟩ : syracuseStep 647639 = 971459) B971459
theorem B1040971 : Blo 287828 1040971 := bstep (se 1 (by rfl) ⟨780728, by rfl⟩ : syracuseStep 1040971 = 1561457) B1561457
theorem B647819 : Blo 287828 647819 := bstep (se 1 (by rfl) ⟨485864, by rfl⟩ : syracuseStep 647819 = 971729) B971729
theorem B1270451 : Blo 287828 1270451 := bstep (se 1 (by rfl) ⟨952838, by rfl⟩ : syracuseStep 1270451 = 1905677) B1905677
theorem B4973237 : Blo 287828 4973237 := bstep (se 5 (by rfl) ⟨233120, by rfl⟩ : syracuseStep 4973237 = 466241) B466241
theorem B647873 : Blo 287828 647873 := bstep (se 2 (by rfl) ⟨242952, by rfl⟩ : syracuseStep 647873 = 485905) B485905
theorem B975563 : Blo 287828 975563 := bstep (se 1 (by rfl) ⟨731672, by rfl⟩ : syracuseStep 975563 = 1463345) B1463345
theorem B648089 : Blo 287828 648089 := bstep (se 2 (by rfl) ⟨243033, by rfl⟩ : syracuseStep 648089 = 486067) B486067
theorem B1237963 : Blo 287828 1237963 := bstep (se 1 (by rfl) ⟨928472, by rfl⟩ : syracuseStep 1237963 = 1856945) B1856945
theorem B975833 : Blo 287828 975833 := bstep (se 2 (by rfl) ⟨365937, by rfl⟩ : syracuseStep 975833 = 731875) B731875
theorem B648179 : Blo 287828 648179 := bstep (se 1 (by rfl) ⟨486134, by rfl⟩ : syracuseStep 648179 = 972269) B972269
theorem B3990545 : Blo 287828 3990545 := bstep (se 2 (by rfl) ⟨1496454, by rfl⟩ : syracuseStep 3990545 = 2992909) B2992909
theorem B648215 : Blo 287828 648215 := bstep (se 1 (by rfl) ⟨486161, by rfl⟩ : syracuseStep 648215 = 972323) B972323
theorem B287831 : Blo 287828 287831 := bstep (se 1 (by rfl) ⟨215873, by rfl⟩ : syracuseStep 287831 = 431747) B431747
theorem B287851 : Blo 287828 287851 := bstep (se 1 (by rfl) ⟨215888, by rfl⟩ : syracuseStep 287851 = 431777) B431777
theorem B615539 : Blo 287828 615539 := bstep (se 1 (by rfl) ⟨461654, by rfl⟩ : syracuseStep 615539 = 923309) B923309
theorem B287863 : Blo 287828 287863 := bstep (se 1 (by rfl) ⟨215897, by rfl⟩ : syracuseStep 287863 = 431795) B431795
theorem B287883 : Blo 287828 287883 := bstep (se 1 (by rfl) ⟨215912, by rfl⟩ : syracuseStep 287883 = 431825) B431825
theorem B287895 : Blo 287828 287895 := bstep (se 1 (by rfl) ⟨215921, by rfl⟩ : syracuseStep 287895 = 431843) B431843
theorem B287915 : Blo 287828 287915 := bstep (se 1 (by rfl) ⟨215936, by rfl⟩ : syracuseStep 287915 = 431873) B431873
theorem B287927 : Blo 287828 287927 := bstep (se 1 (by rfl) ⟨215945, by rfl⟩ : syracuseStep 287927 = 431891) B431891
theorem B287947 : Blo 287828 287947 := bstep (se 1 (by rfl) ⟨215960, by rfl⟩ : syracuseStep 287947 = 431921) B431921
theorem B648395 : Blo 287828 648395 := bstep (se 1 (by rfl) ⟨486296, by rfl⟩ : syracuseStep 648395 = 972593) B972593
theorem B550091 : Blo 287828 550091 := bstep (se 1 (by rfl) ⟨412568, by rfl⟩ : syracuseStep 550091 = 825137) B825137
theorem B287959 : Blo 287828 287959 := bstep (se 1 (by rfl) ⟨215969, by rfl⟩ : syracuseStep 287959 = 431939) B431939
theorem B1238237 : Blo 287828 1238237 := bstep (se 3 (by rfl) ⟨232169, by rfl⟩ : syracuseStep 1238237 = 464339) B464339
theorem B287979 : Blo 287828 287979 := bstep (se 1 (by rfl) ⟨215984, by rfl⟩ : syracuseStep 287979 = 431969) B431969
theorem B287991 : Blo 287828 287991 := bstep (se 1 (by rfl) ⟨215993, by rfl⟩ : syracuseStep 287991 = 431987) B431987
theorem B648449 : Blo 287828 648449 := bstep (se 2 (by rfl) ⟨243168, by rfl⟩ : syracuseStep 648449 = 486337) B486337
theorem B550145 : Blo 287828 550145 := bstep (se 2 (by rfl) ⟨206304, by rfl⟩ : syracuseStep 550145 = 412609) B412609
theorem B288011 : Blo 287828 288011 := bstep (se 1 (by rfl) ⟨216008, by rfl⟩ : syracuseStep 288011 = 432017) B432017
theorem B288023 : Blo 287828 288023 := bstep (se 1 (by rfl) ⟨216017, by rfl⟩ : syracuseStep 288023 = 432035) B432035
theorem B288043 : Blo 287828 288043 := bstep (se 1 (by rfl) ⟨216032, by rfl⟩ : syracuseStep 288043 = 432065) B432065
theorem B288055 : Blo 287828 288055 := bstep (se 1 (by rfl) ⟨216041, by rfl⟩ : syracuseStep 288055 = 432083) B432083
theorem B288075 : Blo 287828 288075 := bstep (se 1 (by rfl) ⟨216056, by rfl⟩ : syracuseStep 288075 = 432113) B432113
theorem B288087 : Blo 287828 288087 := bstep (se 1 (by rfl) ⟨216065, by rfl⟩ : syracuseStep 288087 = 432131) B432131
theorem B288107 : Blo 287828 288107 := bstep (se 1 (by rfl) ⟨216080, by rfl⟩ : syracuseStep 288107 = 432161) B432161
theorem B288119 : Blo 287828 288119 := bstep (se 1 (by rfl) ⟨216089, by rfl⟩ : syracuseStep 288119 = 432179) B432179
theorem B288139 : Blo 287828 288139 := bstep (se 1 (by rfl) ⟨216104, by rfl⟩ : syracuseStep 288139 = 432209) B432209
theorem B288151 : Blo 287828 288151 := bstep (se 1 (by rfl) ⟨216113, by rfl⟩ : syracuseStep 288151 = 432227) B432227
theorem B288171 : Blo 287828 288171 := bstep (se 1 (by rfl) ⟨216128, by rfl⟩ : syracuseStep 288171 = 432257) B432257
theorem B288183 : Blo 287828 288183 := bstep (se 1 (by rfl) ⟨216137, by rfl⟩ : syracuseStep 288183 = 432275) B432275
theorem B288203 : Blo 287828 288203 := bstep (se 1 (by rfl) ⟨216152, by rfl⟩ : syracuseStep 288203 = 432305) B432305
theorem B288215 : Blo 287828 288215 := bstep (se 1 (by rfl) ⟨216161, by rfl⟩ : syracuseStep 288215 = 432323) B432323
theorem B648665 : Blo 287828 648665 := bstep (se 2 (by rfl) ⟨243249, by rfl⟩ : syracuseStep 648665 = 486499) B486499
theorem B288235 : Blo 287828 288235 := bstep (se 1 (by rfl) ⟨216176, by rfl⟩ : syracuseStep 288235 = 432353) B432353
theorem B288247 : Blo 287828 288247 := bstep (se 1 (by rfl) ⟨216185, by rfl⟩ : syracuseStep 288247 = 432371) B432371
theorem B1041923 : Blo 287828 1041923 := bstep (se 1 (by rfl) ⟨781442, by rfl⟩ : syracuseStep 1041923 = 1562885) B1562885
theorem B288267 : Blo 287828 288267 := bstep (se 1 (by rfl) ⟨216200, by rfl⟩ : syracuseStep 288267 = 432401) B432401
theorem B288279 : Blo 287828 288279 := bstep (se 1 (by rfl) ⟨216209, by rfl⟩ : syracuseStep 288279 = 432419) B432419
theorem B288299 : Blo 287828 288299 := bstep (se 1 (by rfl) ⟨216224, by rfl⟩ : syracuseStep 288299 = 432449) B432449
theorem B648755 : Blo 287828 648755 := bstep (se 1 (by rfl) ⟨486566, by rfl⟩ : syracuseStep 648755 = 973133) B973133
theorem B288311 : Blo 287828 288311 := bstep (se 1 (by rfl) ⟨216233, by rfl⟩ : syracuseStep 288311 = 432467) B432467
theorem B288331 : Blo 287828 288331 := bstep (se 1 (by rfl) ⟨216248, by rfl⟩ : syracuseStep 288331 = 432497) B432497
theorem B288343 : Blo 287828 288343 := bstep (se 1 (by rfl) ⟨216257, by rfl⟩ : syracuseStep 288343 = 432515) B432515
theorem B648791 : Blo 287828 648791 := bstep (se 1 (by rfl) ⟨486593, by rfl⟩ : syracuseStep 648791 = 973187) B973187
theorem B288363 : Blo 287828 288363 := bstep (se 1 (by rfl) ⟨216272, by rfl⟩ : syracuseStep 288363 = 432545) B432545
theorem B288375 : Blo 287828 288375 := bstep (se 1 (by rfl) ⟨216281, by rfl⟩ : syracuseStep 288375 = 432563) B432563
theorem B288395 : Blo 287828 288395 := bstep (se 1 (by rfl) ⟨216296, by rfl⟩ : syracuseStep 288395 = 432593) B432593
theorem B288407 : Blo 287828 288407 := bstep (se 1 (by rfl) ⟨216305, by rfl⟩ : syracuseStep 288407 = 432611) B432611
theorem B976535 : Blo 287828 976535 := bstep (se 1 (by rfl) ⟨732401, by rfl⟩ : syracuseStep 976535 = 1464803) B1464803
theorem B288427 : Blo 287828 288427 := bstep (se 1 (by rfl) ⟨216320, by rfl⟩ : syracuseStep 288427 = 432641) B432641
theorem B288439 : Blo 287828 288439 := bstep (se 1 (by rfl) ⟨216329, by rfl⟩ : syracuseStep 288439 = 432659) B432659
theorem B288459 : Blo 287828 288459 := bstep (se 1 (by rfl) ⟨216344, by rfl⟩ : syracuseStep 288459 = 432689) B432689
theorem B288471 : Blo 287828 288471 := bstep (se 1 (by rfl) ⟨216353, by rfl⟩ : syracuseStep 288471 = 432707) B432707
theorem B288491 : Blo 287828 288491 := bstep (se 1 (by rfl) ⟨216368, by rfl⟩ : syracuseStep 288491 = 432737) B432737
theorem B288503 : Blo 287828 288503 := bstep (se 1 (by rfl) ⟨216377, by rfl⟩ : syracuseStep 288503 = 432755) B432755
theorem B1107715 : Blo 287828 1107715 := bstep (se 1 (by rfl) ⟨830786, by rfl⟩ : syracuseStep 1107715 = 1661573) B1661573
theorem B648971 : Blo 287828 648971 := bstep (se 1 (by rfl) ⟨486728, by rfl⟩ : syracuseStep 648971 = 973457) B973457
theorem B288523 : Blo 287828 288523 := bstep (se 1 (by rfl) ⟨216392, by rfl⟩ : syracuseStep 288523 = 432785) B432785
theorem B288535 : Blo 287828 288535 := bstep (se 1 (by rfl) ⟨216401, by rfl⟩ : syracuseStep 288535 = 432803) B432803
theorem B288555 : Blo 287828 288555 := bstep (se 1 (by rfl) ⟨216416, by rfl⟩ : syracuseStep 288555 = 432833) B432833
theorem B1468205 : Blo 287828 1468205 := bstep (se 3 (by rfl) ⟨275288, by rfl⟩ : syracuseStep 1468205 = 550577) B550577
theorem B288567 : Blo 287828 288567 := bstep (se 1 (by rfl) ⟨216425, by rfl⟩ : syracuseStep 288567 = 432851) B432851
theorem B649025 : Blo 287828 649025 := bstep (se 2 (by rfl) ⟨243384, by rfl⟩ : syracuseStep 649025 = 486769) B486769
theorem B288587 : Blo 287828 288587 := bstep (se 1 (by rfl) ⟨216440, by rfl⟩ : syracuseStep 288587 = 432881) B432881
theorem B288599 : Blo 287828 288599 := bstep (se 1 (by rfl) ⟨216449, by rfl⟩ : syracuseStep 288599 = 432899) B432899
theorem B288619 : Blo 287828 288619 := bstep (se 1 (by rfl) ⟨216464, by rfl⟩ : syracuseStep 288619 = 432929) B432929
theorem B288631 : Blo 287828 288631 := bstep (se 1 (by rfl) ⟨216473, by rfl⟩ : syracuseStep 288631 = 432947) B432947
theorem B288651 : Blo 287828 288651 := bstep (se 1 (by rfl) ⟨216488, by rfl⟩ : syracuseStep 288651 = 432977) B432977
theorem B288663 : Blo 287828 288663 := bstep (se 1 (by rfl) ⟨216497, by rfl⟩ : syracuseStep 288663 = 432995) B432995
theorem B288683 : Blo 287828 288683 := bstep (se 1 (by rfl) ⟨216512, by rfl⟩ : syracuseStep 288683 = 433025) B433025
theorem B288695 : Blo 287828 288695 := bstep (se 1 (by rfl) ⟨216521, by rfl⟩ : syracuseStep 288695 = 433043) B433043
theorem B616385 : Blo 287828 616385 := bstep (se 2 (by rfl) ⟨231144, by rfl⟩ : syracuseStep 616385 = 462289) B462289
theorem B288715 : Blo 287828 288715 := bstep (se 1 (by rfl) ⟨216536, by rfl⟩ : syracuseStep 288715 = 433073) B433073
theorem B288727 : Blo 287828 288727 := bstep (se 1 (by rfl) ⟨216545, by rfl⟩ : syracuseStep 288727 = 433091) B433091
theorem B288747 : Blo 287828 288747 := bstep (se 1 (by rfl) ⟨216560, by rfl⟩ : syracuseStep 288747 = 433121) B433121
theorem B288759 : Blo 287828 288759 := bstep (se 1 (by rfl) ⟨216569, by rfl⟩ : syracuseStep 288759 = 433139) B433139
theorem B288779 : Blo 287828 288779 := bstep (se 1 (by rfl) ⟨216584, by rfl⟩ : syracuseStep 288779 = 433169) B433169
theorem B288791 : Blo 287828 288791 := bstep (se 1 (by rfl) ⟨216593, by rfl⟩ : syracuseStep 288791 = 433187) B433187
theorem B649241 : Blo 287828 649241 := bstep (se 2 (by rfl) ⟨243465, by rfl⟩ : syracuseStep 649241 = 486931) B486931
theorem B288811 : Blo 287828 288811 := bstep (se 1 (by rfl) ⟨216608, by rfl⟩ : syracuseStep 288811 = 433217) B433217
theorem B1108019 : Blo 287828 1108019 := bstep (se 1 (by rfl) ⟨831014, by rfl⟩ : syracuseStep 1108019 = 1662029) B1662029
theorem B288823 : Blo 287828 288823 := bstep (se 1 (by rfl) ⟨216617, by rfl⟩ : syracuseStep 288823 = 433235) B433235
theorem B288843 : Blo 287828 288843 := bstep (se 1 (by rfl) ⟨216632, by rfl⟩ : syracuseStep 288843 = 433265) B433265
theorem B288855 : Blo 287828 288855 := bstep (se 1 (by rfl) ⟨216641, by rfl⟩ : syracuseStep 288855 = 433283) B433283
theorem B288875 : Blo 287828 288875 := bstep (se 1 (by rfl) ⟨216656, by rfl⟩ : syracuseStep 288875 = 433313) B433313
theorem B649331 : Blo 287828 649331 := bstep (se 1 (by rfl) ⟨486998, by rfl⟩ : syracuseStep 649331 = 973997) B973997
theorem B288887 : Blo 287828 288887 := bstep (se 1 (by rfl) ⟨216665, by rfl⟩ : syracuseStep 288887 = 433331) B433331
theorem B288907 : Blo 287828 288907 := bstep (se 1 (by rfl) ⟨216680, by rfl⟩ : syracuseStep 288907 = 433361) B433361
theorem B649367 : Blo 287828 649367 := bstep (se 1 (by rfl) ⟨487025, by rfl⟩ : syracuseStep 649367 = 974051) B974051
theorem B288919 : Blo 287828 288919 := bstep (se 1 (by rfl) ⟨216689, by rfl⟩ : syracuseStep 288919 = 433379) B433379
theorem B551063 : Blo 287828 551063 := bstep (se 1 (by rfl) ⟨413297, by rfl⟩ : syracuseStep 551063 = 826595) B826595
theorem B288939 : Blo 287828 288939 := bstep (se 1 (by rfl) ⟨216704, by rfl⟩ : syracuseStep 288939 = 433409) B433409
theorem B583859 : Blo 287828 583859 := bstep (se 1 (by rfl) ⟨437894, by rfl⟩ : syracuseStep 583859 = 875789) B875789
theorem B977075 : Blo 287828 977075 := bstep (se 1 (by rfl) ⟨732806, by rfl⟩ : syracuseStep 977075 = 1465613) B1465613
theorem B288951 : Blo 287828 288951 := bstep (se 1 (by rfl) ⟨216713, by rfl⟩ : syracuseStep 288951 = 433427) B433427
theorem B288971 : Blo 287828 288971 := bstep (se 1 (by rfl) ⟨216728, by rfl⟩ : syracuseStep 288971 = 433457) B433457
theorem B288983 : Blo 287828 288983 := bstep (se 1 (by rfl) ⟨216737, by rfl⟩ : syracuseStep 288983 = 433475) B433475
theorem B289003 : Blo 287828 289003 := bstep (se 1 (by rfl) ⟨216752, by rfl⟩ : syracuseStep 289003 = 433505) B433505
theorem B289015 : Blo 287828 289015 := bstep (se 1 (by rfl) ⟨216761, by rfl⟩ : syracuseStep 289015 = 433523) B433523
theorem B289035 : Blo 287828 289035 := bstep (se 1 (by rfl) ⟨216776, by rfl⟩ : syracuseStep 289035 = 433553) B433553
theorem B616727 : Blo 287828 616727 := bstep (se 1 (by rfl) ⟨462545, by rfl⟩ : syracuseStep 616727 = 925091) B925091
theorem B289047 : Blo 287828 289047 := bstep (se 1 (by rfl) ⟨216785, by rfl⟩ : syracuseStep 289047 = 433571) B433571
theorem B289067 : Blo 287828 289067 := bstep (se 1 (by rfl) ⟨216800, by rfl⟩ : syracuseStep 289067 = 433601) B433601
theorem B289079 : Blo 287828 289079 := bstep (se 1 (by rfl) ⟨216809, by rfl⟩ : syracuseStep 289079 = 433619) B433619
theorem B649547 : Blo 287828 649547 := bstep (se 1 (by rfl) ⟨487160, by rfl⟩ : syracuseStep 649547 = 974321) B974321
theorem B289099 : Blo 287828 289099 := bstep (se 1 (by rfl) ⟨216824, by rfl⟩ : syracuseStep 289099 = 433649) B433649
theorem B289111 : Blo 287828 289111 := bstep (se 1 (by rfl) ⟨216833, by rfl⟩ : syracuseStep 289111 = 433667) B433667
theorem B289131 : Blo 287828 289131 := bstep (se 1 (by rfl) ⟨216848, by rfl⟩ : syracuseStep 289131 = 433697) B433697
theorem B289143 : Blo 287828 289143 := bstep (se 1 (by rfl) ⟨216857, by rfl⟩ : syracuseStep 289143 = 433715) B433715
theorem B649601 : Blo 287828 649601 := bstep (se 2 (by rfl) ⟨243600, by rfl⟩ : syracuseStep 649601 = 487201) B487201
theorem B289163 : Blo 287828 289163 := bstep (se 1 (by rfl) ⟨216872, by rfl⟩ : syracuseStep 289163 = 433745) B433745
theorem B289175 : Blo 287828 289175 := bstep (se 1 (by rfl) ⟨216881, by rfl⟩ : syracuseStep 289175 = 433763) B433763
theorem B289195 : Blo 287828 289195 := bstep (se 1 (by rfl) ⟨216896, by rfl⟩ : syracuseStep 289195 = 433793) B433793
theorem B289207 : Blo 287828 289207 := bstep (se 1 (by rfl) ⟨216905, by rfl⟩ : syracuseStep 289207 = 433811) B433811
theorem B977345 : Blo 287828 977345 := bstep (se 2 (by rfl) ⟨366504, by rfl⟩ : syracuseStep 977345 = 733009) B733009
theorem B289227 : Blo 287828 289227 := bstep (se 1 (by rfl) ⟨216920, by rfl⟩ : syracuseStep 289227 = 433841) B433841
theorem B289239 : Blo 287828 289239 := bstep (se 1 (by rfl) ⟨216929, by rfl⟩ : syracuseStep 289239 = 433859) B433859
theorem B2779609 : Blo 287828 2779609 := bstep (se 2 (by rfl) ⟨1042353, by rfl⟩ : syracuseStep 2779609 = 2084707) B2084707
theorem B289259 : Blo 287828 289259 := bstep (se 1 (by rfl) ⟨216944, by rfl⟩ : syracuseStep 289259 = 433889) B433889
theorem B289271 : Blo 287828 289271 := bstep (se 1 (by rfl) ⟨216953, by rfl⟩ : syracuseStep 289271 = 433907) B433907
theorem B289291 : Blo 287828 289291 := bstep (se 1 (by rfl) ⟨216968, by rfl⟩ : syracuseStep 289291 = 433937) B433937
theorem B289303 : Blo 287828 289303 := bstep (se 1 (by rfl) ⟨216977, by rfl⟩ : syracuseStep 289303 = 433955) B433955
theorem B289323 : Blo 287828 289323 := bstep (se 1 (by rfl) ⟨216992, by rfl⟩ : syracuseStep 289323 = 433985) B433985
theorem B1174061 : Blo 287828 1174061 := bstep (se 3 (by rfl) ⟨220136, by rfl⟩ : syracuseStep 1174061 = 440273) B440273
theorem B289335 : Blo 287828 289335 := bstep (se 1 (by rfl) ⟨217001, by rfl⟩ : syracuseStep 289335 = 434003) B434003
theorem B289355 : Blo 287828 289355 := bstep (se 1 (by rfl) ⟨217016, by rfl⟩ : syracuseStep 289355 = 434033) B434033
theorem B289367 : Blo 287828 289367 := bstep (se 1 (by rfl) ⟨217025, by rfl⟩ : syracuseStep 289367 = 434051) B434051
theorem B649817 : Blo 287828 649817 := bstep (se 2 (by rfl) ⟨243681, by rfl⟩ : syracuseStep 649817 = 487363) B487363
theorem B289387 : Blo 287828 289387 := bstep (se 1 (by rfl) ⟨217040, by rfl⟩ : syracuseStep 289387 = 434081) B434081
theorem B289399 : Blo 287828 289399 := bstep (se 1 (by rfl) ⟨217049, by rfl⟩ : syracuseStep 289399 = 434099) B434099
theorem B289419 : Blo 287828 289419 := bstep (se 1 (by rfl) ⟨217064, by rfl⟩ : syracuseStep 289419 = 434129) B434129
theorem B518807 : Blo 287828 518807 := bstep (se 1 (by rfl) ⟨389105, by rfl⟩ : syracuseStep 518807 = 778211) B778211
theorem B289431 : Blo 287828 289431 := bstep (se 1 (by rfl) ⟨217073, by rfl⟩ : syracuseStep 289431 = 434147) B434147
theorem B289451 : Blo 287828 289451 := bstep (se 1 (by rfl) ⟨217088, by rfl⟩ : syracuseStep 289451 = 434177) B434177
theorem B649907 : Blo 287828 649907 := bstep (se 1 (by rfl) ⟨487430, by rfl⟩ : syracuseStep 649907 = 974861) B974861
theorem B551603 : Blo 287828 551603 := bstep (se 1 (by rfl) ⟨413702, by rfl⟩ : syracuseStep 551603 = 827405) B827405
theorem B289463 : Blo 287828 289463 := bstep (se 1 (by rfl) ⟨217097, by rfl⟩ : syracuseStep 289463 = 434195) B434195
theorem B289483 : Blo 287828 289483 := bstep (se 1 (by rfl) ⟨217112, by rfl⟩ : syracuseStep 289483 = 434225) B434225
theorem B649943 : Blo 287828 649943 := bstep (se 1 (by rfl) ⟨487457, by rfl⟩ : syracuseStep 649943 = 974915) B974915
theorem B289495 : Blo 287828 289495 := bstep (se 1 (by rfl) ⟨217121, by rfl⟩ : syracuseStep 289495 = 434243) B434243
theorem B289515 : Blo 287828 289515 := bstep (se 1 (by rfl) ⟨217136, by rfl⟩ : syracuseStep 289515 = 434273) B434273
theorem B289527 : Blo 287828 289527 := bstep (se 1 (by rfl) ⟨217145, by rfl⟩ : syracuseStep 289527 = 434291) B434291
theorem B486155 : Blo 287828 486155 := bstep (se 1 (by rfl) ⟨364616, by rfl⟩ : syracuseStep 486155 = 729233) B729233
theorem B289547 : Blo 287828 289547 := bstep (se 1 (by rfl) ⟨217160, by rfl⟩ : syracuseStep 289547 = 434321) B434321
theorem B289559 : Blo 287828 289559 := bstep (se 1 (by rfl) ⟨217169, by rfl⟩ : syracuseStep 289559 = 434339) B434339
theorem B289579 : Blo 287828 289579 := bstep (se 1 (by rfl) ⟨217184, by rfl⟩ : syracuseStep 289579 = 434369) B434369
theorem B289591 : Blo 287828 289591 := bstep (se 1 (by rfl) ⟨217193, by rfl⟩ : syracuseStep 289591 = 434387) B434387
theorem B289611 : Blo 287828 289611 := bstep (se 1 (by rfl) ⟨217208, by rfl⟩ : syracuseStep 289611 = 434417) B434417
theorem B289623 : Blo 287828 289623 := bstep (se 1 (by rfl) ⟨217217, by rfl⟩ : syracuseStep 289623 = 434435) B434435
theorem B289643 : Blo 287828 289643 := bstep (se 1 (by rfl) ⟨217232, by rfl⟩ : syracuseStep 289643 = 434465) B434465
theorem B289655 : Blo 287828 289655 := bstep (se 1 (by rfl) ⟨217241, by rfl⟩ : syracuseStep 289655 = 434483) B434483
theorem B486283 : Blo 287828 486283 := bstep (se 1 (by rfl) ⟨364712, by rfl⟩ : syracuseStep 486283 = 729425) B729425
theorem B650123 : Blo 287828 650123 := bstep (se 1 (by rfl) ⟨487592, by rfl⟩ : syracuseStep 650123 = 975185) B975185
theorem B289675 : Blo 287828 289675 := bstep (se 1 (by rfl) ⟨217256, by rfl⟩ : syracuseStep 289675 = 434513) B434513
theorem B289687 : Blo 287828 289687 := bstep (se 1 (by rfl) ⟨217265, by rfl⟩ : syracuseStep 289687 = 434531) B434531
theorem B289707 : Blo 287828 289707 := bstep (se 1 (by rfl) ⟨217280, by rfl⟩ : syracuseStep 289707 = 434561) B434561
theorem B289719 : Blo 287828 289719 := bstep (se 1 (by rfl) ⟨217289, by rfl⟩ : syracuseStep 289719 = 434579) B434579
theorem B650177 : Blo 287828 650177 := bstep (se 2 (by rfl) ⟨243816, by rfl⟩ : syracuseStep 650177 = 487633) B487633
theorem B289739 : Blo 287828 289739 := bstep (se 1 (by rfl) ⟨217304, by rfl⟩ : syracuseStep 289739 = 434609) B434609
theorem B289751 : Blo 287828 289751 := bstep (se 1 (by rfl) ⟨217313, by rfl⟩ : syracuseStep 289751 = 434627) B434627
theorem B977885 : Blo 287828 977885 := bstep (se 3 (by rfl) ⟨183353, by rfl⟩ : syracuseStep 977885 = 366707) B366707
theorem B289771 : Blo 287828 289771 := bstep (se 1 (by rfl) ⟨217328, by rfl⟩ : syracuseStep 289771 = 434657) B434657
theorem B289783 : Blo 287828 289783 := bstep (se 1 (by rfl) ⟨217337, by rfl⟩ : syracuseStep 289783 = 434675) B434675
theorem B289803 : Blo 287828 289803 := bstep (se 1 (by rfl) ⟨217352, by rfl⟩ : syracuseStep 289803 = 434705) B434705
theorem B289815 : Blo 287828 289815 := bstep (se 1 (by rfl) ⟨217361, by rfl⟩ : syracuseStep 289815 = 434723) B434723
theorem B486425 : Blo 287828 486425 := bstep (se 2 (by rfl) ⟨182409, by rfl⟩ : syracuseStep 486425 = 364819) B364819
theorem B289835 : Blo 287828 289835 := bstep (se 1 (by rfl) ⟨217376, by rfl⟩ : syracuseStep 289835 = 434753) B434753
theorem B1043507 : Blo 287828 1043507 := bstep (se 1 (by rfl) ⟨782630, by rfl⟩ : syracuseStep 1043507 = 1565261) B1565261
theorem B289847 : Blo 287828 289847 := bstep (se 1 (by rfl) ⟨217385, by rfl⟩ : syracuseStep 289847 = 434771) B434771
theorem B2190401 : Blo 287828 2190401 := bstep (se 2 (by rfl) ⟨821400, by rfl⟩ : syracuseStep 2190401 = 1642801) B1642801
theorem B289867 : Blo 287828 289867 := bstep (se 1 (by rfl) ⟨217400, by rfl⟩ : syracuseStep 289867 = 434801) B434801
theorem B289879 : Blo 287828 289879 := bstep (se 1 (by rfl) ⟨217409, by rfl⟩ : syracuseStep 289879 = 434819) B434819
theorem B289899 : Blo 287828 289899 := bstep (se 1 (by rfl) ⟨217424, by rfl⟩ : syracuseStep 289899 = 434849) B434849
theorem B289911 : Blo 287828 289911 := bstep (se 1 (by rfl) ⟨217433, by rfl⟩ : syracuseStep 289911 = 434867) B434867
theorem B289931 : Blo 287828 289931 := bstep (se 1 (by rfl) ⟨217448, by rfl⟩ : syracuseStep 289931 = 434897) B434897
theorem B289943 : Blo 287828 289943 := bstep (se 1 (by rfl) ⟨217457, by rfl⟩ : syracuseStep 289943 = 434915) B434915
theorem B486553 : Blo 287828 486553 := bstep (se 2 (by rfl) ⟨182457, by rfl⟩ : syracuseStep 486553 = 364915) B364915
theorem B650393 : Blo 287828 650393 := bstep (se 2 (by rfl) ⟨243897, by rfl⟩ : syracuseStep 650393 = 487795) B487795
theorem B552089 : Blo 287828 552089 := bstep (se 2 (by rfl) ⟨207033, by rfl⟩ : syracuseStep 552089 = 414067) B414067
theorem B289963 : Blo 287828 289963 := bstep (se 1 (by rfl) ⟨217472, by rfl⟩ : syracuseStep 289963 = 434945) B434945
theorem B1633459 : Blo 287828 1633459 := bstep (se 1 (by rfl) ⟨1225094, by rfl⟩ : syracuseStep 1633459 = 2450189) B2450189
theorem B289975 : Blo 287828 289975 := bstep (se 1 (by rfl) ⟨217481, by rfl⟩ : syracuseStep 289975 = 434963) B434963
theorem B289995 : Blo 287828 289995 := bstep (se 1 (by rfl) ⟨217496, by rfl⟩ : syracuseStep 289995 = 434993) B434993
theorem B290007 : Blo 287828 290007 := bstep (se 1 (by rfl) ⟨217505, by rfl⟩ : syracuseStep 290007 = 435011) B435011
theorem B290027 : Blo 287828 290027 := bstep (se 1 (by rfl) ⟨217520, by rfl⟩ : syracuseStep 290027 = 435041) B435041
theorem B650483 : Blo 287828 650483 := bstep (se 1 (by rfl) ⟨487862, by rfl⟩ : syracuseStep 650483 = 975725) B975725
theorem B290039 : Blo 287828 290039 := bstep (se 1 (by rfl) ⟨217529, by rfl⟩ : syracuseStep 290039 = 435059) B435059
theorem B290059 : Blo 287828 290059 := bstep (se 1 (by rfl) ⟨217544, by rfl⟩ : syracuseStep 290059 = 435089) B435089
theorem B650519 : Blo 287828 650519 := bstep (se 1 (by rfl) ⟨487889, by rfl⟩ : syracuseStep 650519 = 975779) B975779
theorem B290071 : Blo 287828 290071 := bstep (se 1 (by rfl) ⟨217553, by rfl⟩ : syracuseStep 290071 = 435107) B435107
theorem B290091 : Blo 287828 290091 := bstep (se 1 (by rfl) ⟨217568, by rfl⟩ : syracuseStep 290091 = 435137) B435137
theorem B290103 : Blo 287828 290103 := bstep (se 1 (by rfl) ⟨217577, by rfl⟩ : syracuseStep 290103 = 435155) B435155
theorem B290123 : Blo 287828 290123 := bstep (se 1 (by rfl) ⟨217592, by rfl⟩ : syracuseStep 290123 = 435185) B435185
theorem B290135 : Blo 287828 290135 := bstep (se 1 (by rfl) ⟨217601, by rfl⟩ : syracuseStep 290135 = 435203) B435203
theorem B290155 : Blo 287828 290155 := bstep (se 1 (by rfl) ⟨217616, by rfl⟩ : syracuseStep 290155 = 435233) B435233
theorem B290167 : Blo 287828 290167 := bstep (se 1 (by rfl) ⟨217625, by rfl⟩ : syracuseStep 290167 = 435251) B435251
theorem B290187 : Blo 287828 290187 := bstep (se 1 (by rfl) ⟨217640, by rfl⟩ : syracuseStep 290187 = 435281) B435281
theorem B290199 : Blo 287828 290199 := bstep (se 1 (by rfl) ⟨217649, by rfl⟩ : syracuseStep 290199 = 435299) B435299
theorem B290219 : Blo 287828 290219 := bstep (se 1 (by rfl) ⟨217664, by rfl⟩ : syracuseStep 290219 = 435329) B435329
theorem B290231 : Blo 287828 290231 := bstep (se 1 (by rfl) ⟨217673, by rfl⟩ : syracuseStep 290231 = 435347) B435347
theorem B650699 : Blo 287828 650699 := bstep (se 1 (by rfl) ⟨488024, by rfl⟩ : syracuseStep 650699 = 976049) B976049
theorem B290251 : Blo 287828 290251 := bstep (se 1 (by rfl) ⟨217688, by rfl⟩ : syracuseStep 290251 = 435377) B435377
theorem B290263 : Blo 287828 290263 := bstep (se 1 (by rfl) ⟨217697, by rfl⟩ : syracuseStep 290263 = 435395) B435395
theorem B290283 : Blo 287828 290283 := bstep (se 1 (by rfl) ⟨217712, by rfl⟩ : syracuseStep 290283 = 435425) B435425
theorem B290295 : Blo 287828 290295 := bstep (se 1 (by rfl) ⟨217721, by rfl⟩ : syracuseStep 290295 = 435443) B435443
theorem B650753 : Blo 287828 650753 := bstep (se 2 (by rfl) ⟨244032, by rfl⟩ : syracuseStep 650753 = 488065) B488065
theorem B2092549 : Blo 287828 2092549 := bstep (se 4 (by rfl) ⟨196176, by rfl⟩ : syracuseStep 2092549 = 392353) B392353
theorem B290315 : Blo 287828 290315 := bstep (se 1 (by rfl) ⟨217736, by rfl⟩ : syracuseStep 290315 = 435473) B435473
theorem B290327 : Blo 287828 290327 := bstep (se 1 (by rfl) ⟨217745, by rfl⟩ : syracuseStep 290327 = 435491) B435491
theorem B290347 : Blo 287828 290347 := bstep (se 1 (by rfl) ⟨217760, by rfl⟩ : syracuseStep 290347 = 435521) B435521
theorem B290359 : Blo 287828 290359 := bstep (se 1 (by rfl) ⟨217769, by rfl⟩ : syracuseStep 290359 = 435539) B435539
theorem B290379 : Blo 287828 290379 := bstep (se 1 (by rfl) ⟨217784, by rfl⟩ : syracuseStep 290379 = 435569) B435569
theorem B290391 : Blo 287828 290391 := bstep (se 1 (by rfl) ⟨217793, by rfl⟩ : syracuseStep 290391 = 435587) B435587
theorem B290411 : Blo 287828 290411 := bstep (se 1 (by rfl) ⟨217808, by rfl⟩ : syracuseStep 290411 = 435617) B435617
theorem B290423 : Blo 287828 290423 := bstep (se 1 (by rfl) ⟨217817, by rfl⟩ : syracuseStep 290423 = 435635) B435635
theorem B290443 : Blo 287828 290443 := bstep (se 1 (by rfl) ⟨217832, by rfl⟩ : syracuseStep 290443 = 435665) B435665
theorem B290455 : Blo 287828 290455 := bstep (se 1 (by rfl) ⟨217841, by rfl⟩ : syracuseStep 290455 = 435683) B435683
theorem B290475 : Blo 287828 290475 := bstep (se 1 (by rfl) ⟨217856, by rfl⟩ : syracuseStep 290475 = 435713) B435713
theorem B290487 : Blo 287828 290487 := bstep (se 1 (by rfl) ⟨217865, by rfl⟩ : syracuseStep 290487 = 435731) B435731
theorem B618187 : Blo 287828 618187 := bstep (se 1 (by rfl) ⟨463640, by rfl⟩ : syracuseStep 618187 = 927281) B927281
theorem B290507 : Blo 287828 290507 := bstep (se 1 (by rfl) ⟨217880, by rfl⟩ : syracuseStep 290507 = 435761) B435761
theorem B487127 : Blo 287828 487127 := bstep (se 1 (by rfl) ⟨365345, by rfl⟩ : syracuseStep 487127 = 730691) B730691
theorem B290519 : Blo 287828 290519 := bstep (se 1 (by rfl) ⟨217889, by rfl⟩ : syracuseStep 290519 = 435779) B435779
theorem B650969 : Blo 287828 650969 := bstep (se 2 (by rfl) ⟨244113, by rfl⟩ : syracuseStep 650969 = 488227) B488227
theorem B290539 : Blo 287828 290539 := bstep (se 1 (by rfl) ⟨217904, by rfl⟩ : syracuseStep 290539 = 435809) B435809
theorem B290551 : Blo 287828 290551 := bstep (se 1 (by rfl) ⟨217913, by rfl⟩ : syracuseStep 290551 = 435827) B435827
theorem B290571 : Blo 287828 290571 := bstep (se 1 (by rfl) ⟨217928, by rfl⟩ : syracuseStep 290571 = 435857) B435857
theorem B1240849 : Blo 287828 1240849 := bstep (se 2 (by rfl) ⟨465318, by rfl⟩ : syracuseStep 1240849 = 930637) B930637
theorem B290583 : Blo 287828 290583 := bstep (se 1 (by rfl) ⟨217937, by rfl⟩ : syracuseStep 290583 = 435875) B435875
theorem B290603 : Blo 287828 290603 := bstep (se 1 (by rfl) ⟨217952, by rfl⟩ : syracuseStep 290603 = 435905) B435905
theorem B3534637 : Blo 287828 3534637 := bstep (se 3 (by rfl) ⟨662744, by rfl⟩ : syracuseStep 3534637 = 1325489) B1325489
theorem B651059 : Blo 287828 651059 := bstep (se 1 (by rfl) ⟨488294, by rfl⟩ : syracuseStep 651059 = 976589) B976589
theorem B290615 : Blo 287828 290615 := bstep (se 1 (by rfl) ⟨217961, by rfl⟩ : syracuseStep 290615 = 435923) B435923
theorem B290635 : Blo 287828 290635 := bstep (se 1 (by rfl) ⟨217976, by rfl⟩ : syracuseStep 290635 = 435953) B435953
theorem B487255 : Blo 287828 487255 := bstep (se 1 (by rfl) ⟨365441, by rfl⟩ : syracuseStep 487255 = 730883) B730883
theorem B651095 : Blo 287828 651095 := bstep (se 1 (by rfl) ⟨488321, by rfl⟩ : syracuseStep 651095 = 976643) B976643
theorem B290647 : Blo 287828 290647 := bstep (se 1 (by rfl) ⟨217985, by rfl⟩ : syracuseStep 290647 = 435971) B435971
theorem B290667 : Blo 287828 290667 := bstep (se 1 (by rfl) ⟨218000, by rfl⟩ : syracuseStep 290667 = 436001) B436001
theorem B290679 : Blo 287828 290679 := bstep (se 1 (by rfl) ⟨218009, by rfl⟩ : syracuseStep 290679 = 436019) B436019
theorem B290699 : Blo 287828 290699 := bstep (se 1 (by rfl) ⟨218024, by rfl⟩ : syracuseStep 290699 = 436049) B436049
theorem B290711 : Blo 287828 290711 := bstep (se 1 (by rfl) ⟨218033, by rfl⟩ : syracuseStep 290711 = 436067) B436067
theorem B290731 : Blo 287828 290731 := bstep (se 1 (by rfl) ⟨218048, by rfl⟩ : syracuseStep 290731 = 436097) B436097
theorem B290743 : Blo 287828 290743 := bstep (se 1 (by rfl) ⟨218057, by rfl⟩ : syracuseStep 290743 = 436115) B436115
theorem B520139 : Blo 287828 520139 := bstep (se 1 (by rfl) ⟨390104, by rfl⟩ : syracuseStep 520139 = 780209) B780209
theorem B618443 : Blo 287828 618443 := bstep (se 1 (by rfl) ⟨463832, by rfl⟩ : syracuseStep 618443 = 927665) B927665
theorem B290763 : Blo 287828 290763 := bstep (se 1 (by rfl) ⟨218072, by rfl⟩ : syracuseStep 290763 = 436145) B436145
theorem B290775 : Blo 287828 290775 := bstep (se 1 (by rfl) ⟨218081, by rfl⟩ : syracuseStep 290775 = 436163) B436163
theorem B290795 : Blo 287828 290795 := bstep (se 1 (by rfl) ⟨218096, by rfl⟩ : syracuseStep 290795 = 436193) B436193
theorem B290807 : Blo 287828 290807 := bstep (se 1 (by rfl) ⟨218105, by rfl⟩ : syracuseStep 290807 = 436211) B436211
theorem B651275 : Blo 287828 651275 := bstep (se 1 (by rfl) ⟨488456, by rfl⟩ : syracuseStep 651275 = 976913) B976913
theorem B290827 : Blo 287828 290827 := bstep (se 1 (by rfl) ⟨218120, by rfl⟩ : syracuseStep 290827 = 436241) B436241
theorem B290839 : Blo 287828 290839 := bstep (se 1 (by rfl) ⟨218129, by rfl⟩ : syracuseStep 290839 = 436259) B436259
theorem B290859 : Blo 287828 290859 := bstep (se 1 (by rfl) ⟨218144, by rfl⟩ : syracuseStep 290859 = 436289) B436289
theorem B290871 : Blo 287828 290871 := bstep (se 1 (by rfl) ⟨218153, by rfl⟩ : syracuseStep 290871 = 436307) B436307
theorem B651329 : Blo 287828 651329 := bstep (se 2 (by rfl) ⟨244248, by rfl⟩ : syracuseStep 651329 = 488497) B488497
theorem B979019 : Blo 287828 979019 := bstep (se 1 (by rfl) ⟨734264, by rfl⟩ : syracuseStep 979019 = 1468529) B1468529
theorem B290891 : Blo 287828 290891 := bstep (se 1 (by rfl) ⟨218168, by rfl⟩ : syracuseStep 290891 = 436337) B436337
theorem B290903 : Blo 287828 290903 := bstep (se 1 (by rfl) ⟨218177, by rfl⟩ : syracuseStep 290903 = 436355) B436355
theorem B290923 : Blo 287828 290923 := bstep (se 1 (by rfl) ⟨218192, by rfl⟩ : syracuseStep 290923 = 436385) B436385
theorem B290935 : Blo 287828 290935 := bstep (se 1 (by rfl) ⟨218201, by rfl⟩ : syracuseStep 290935 = 436403) B436403
theorem B290955 : Blo 287828 290955 := bstep (se 1 (by rfl) ⟨218216, by rfl⟩ : syracuseStep 290955 = 436433) B436433
theorem B290967 : Blo 287828 290967 := bstep (se 1 (by rfl) ⟨218225, by rfl⟩ : syracuseStep 290967 = 436451) B436451
theorem B290987 : Blo 287828 290987 := bstep (se 1 (by rfl) ⟨218240, by rfl⟩ : syracuseStep 290987 = 436481) B436481
theorem B290999 : Blo 287828 290999 := bstep (se 1 (by rfl) ⟨218249, by rfl⟩ : syracuseStep 290999 = 436499) B436499
theorem B291019 : Blo 287828 291019 := bstep (se 1 (by rfl) ⟨218264, by rfl⟩ : syracuseStep 291019 = 436529) B436529
theorem B291031 : Blo 287828 291031 := bstep (se 1 (by rfl) ⟨218273, by rfl⟩ : syracuseStep 291031 = 436547) B436547
theorem B291051 : Blo 287828 291051 := bstep (se 1 (by rfl) ⟨218288, by rfl⟩ : syracuseStep 291051 = 436577) B436577
theorem B291063 : Blo 287828 291063 := bstep (se 1 (by rfl) ⟨218297, by rfl⟩ : syracuseStep 291063 = 436595) B436595
theorem B323851 : Blo 287828 323851 := bstep (se 1 (by rfl) ⟨242888, by rfl⟩ : syracuseStep 323851 = 485777) B485777
theorem B291083 : Blo 287828 291083 := bstep (se 1 (by rfl) ⟨218312, by rfl⟩ : syracuseStep 291083 = 436625) B436625
theorem B291095 : Blo 287828 291095 := bstep (se 1 (by rfl) ⟨218321, by rfl⟩ : syracuseStep 291095 = 436643) B436643
theorem B651545 : Blo 287828 651545 := bstep (se 2 (by rfl) ⟨244329, by rfl⟩ : syracuseStep 651545 = 488659) B488659
theorem B291115 : Blo 287828 291115 := bstep (se 1 (by rfl) ⟨218336, by rfl⟩ : syracuseStep 291115 = 436673) B436673
theorem B291127 : Blo 287828 291127 := bstep (se 1 (by rfl) ⟨218345, by rfl⟩ : syracuseStep 291127 = 436691) B436691
theorem B291147 : Blo 287828 291147 := bstep (se 1 (by rfl) ⟨218360, by rfl⟩ : syracuseStep 291147 = 436721) B436721
theorem B291159 : Blo 287828 291159 := bstep (se 1 (by rfl) ⟨218369, by rfl⟩ : syracuseStep 291159 = 436739) B436739
theorem B979289 : Blo 287828 979289 := bstep (se 2 (by rfl) ⟨367233, by rfl⟩ : syracuseStep 979289 = 734467) B734467
theorem B291179 : Blo 287828 291179 := bstep (se 1 (by rfl) ⟨218384, by rfl⟩ : syracuseStep 291179 = 436769) B436769
theorem B651635 : Blo 287828 651635 := bstep (se 1 (by rfl) ⟨488726, by rfl⟩ : syracuseStep 651635 = 977453) B977453
theorem B323959 : Blo 287828 323959 := bstep (se 1 (by rfl) ⟨242969, by rfl⟩ : syracuseStep 323959 = 485939) B485939
theorem B291191 : Blo 287828 291191 := bstep (se 1 (by rfl) ⟨218393, by rfl⟩ : syracuseStep 291191 = 436787) B436787
theorem B291211 : Blo 287828 291211 := bstep (se 1 (by rfl) ⟨218408, by rfl⟩ : syracuseStep 291211 = 436817) B436817
theorem B651671 : Blo 287828 651671 := bstep (se 1 (by rfl) ⟨488753, by rfl⟩ : syracuseStep 651671 = 977507) B977507
theorem B291223 : Blo 287828 291223 := bstep (se 1 (by rfl) ⟨218417, by rfl⟩ : syracuseStep 291223 = 436835) B436835
theorem B291243 : Blo 287828 291243 := bstep (se 1 (by rfl) ⟨218432, by rfl⟩ : syracuseStep 291243 = 436865) B436865
theorem B291255 : Blo 287828 291255 := bstep (se 1 (by rfl) ⟨218441, by rfl⟩ : syracuseStep 291255 = 436883) B436883
theorem B487883 : Blo 287828 487883 := bstep (se 1 (by rfl) ⟨365912, by rfl⟩ : syracuseStep 487883 = 731825) B731825
theorem B291275 : Blo 287828 291275 := bstep (se 1 (by rfl) ⟨218456, by rfl⟩ : syracuseStep 291275 = 436913) B436913
theorem B291287 : Blo 287828 291287 := bstep (se 1 (by rfl) ⟨218465, by rfl⟩ : syracuseStep 291287 = 436931) B436931
theorem B291307 : Blo 287828 291307 := bstep (se 1 (by rfl) ⟨218480, by rfl⟩ : syracuseStep 291307 = 436961) B436961
theorem B291319 : Blo 287828 291319 := bstep (se 1 (by rfl) ⟨218489, by rfl⟩ : syracuseStep 291319 = 436979) B436979
theorem B291339 : Blo 287828 291339 := bstep (se 1 (by rfl) ⟨218504, by rfl⟩ : syracuseStep 291339 = 437009) B437009
theorem B291351 : Blo 287828 291351 := bstep (se 1 (by rfl) ⟨218513, by rfl⟩ : syracuseStep 291351 = 437027) B437027
theorem B324139 : Blo 287828 324139 := bstep (se 1 (by rfl) ⟨243104, by rfl⟩ : syracuseStep 324139 = 486209) B486209
theorem B291371 : Blo 287828 291371 := bstep (se 1 (by rfl) ⟨218528, by rfl⟩ : syracuseStep 291371 = 437057) B437057
theorem B1045037 : Blo 287828 1045037 := bstep (se 3 (by rfl) ⟨195944, by rfl⟩ : syracuseStep 1045037 = 391889) B391889
theorem B291383 : Blo 287828 291383 := bstep (se 1 (by rfl) ⟨218537, by rfl⟩ : syracuseStep 291383 = 437075) B437075
theorem B488011 : Blo 287828 488011 := bstep (se 1 (by rfl) ⟨366008, by rfl⟩ : syracuseStep 488011 = 732017) B732017
theorem B651851 : Blo 287828 651851 := bstep (se 1 (by rfl) ⟨488888, by rfl⟩ : syracuseStep 651851 = 977777) B977777
theorem B291403 : Blo 287828 291403 := bstep (se 1 (by rfl) ⟨218552, by rfl⟩ : syracuseStep 291403 = 437105) B437105
theorem B553547 : Blo 287828 553547 := bstep (se 1 (by rfl) ⟨415160, by rfl⟩ : syracuseStep 553547 = 830321) B830321
theorem B291415 : Blo 287828 291415 := bstep (se 1 (by rfl) ⟨218561, by rfl⟩ : syracuseStep 291415 = 437123) B437123
theorem B291435 : Blo 287828 291435 := bstep (se 1 (by rfl) ⟨218576, by rfl⟩ : syracuseStep 291435 = 437153) B437153
theorem B291447 : Blo 287828 291447 := bstep (se 1 (by rfl) ⟨218585, by rfl⟩ : syracuseStep 291447 = 437171) B437171
theorem B651905 : Blo 287828 651905 := bstep (se 2 (by rfl) ⟨244464, by rfl⟩ : syracuseStep 651905 = 488929) B488929
theorem B291467 : Blo 287828 291467 := bstep (se 1 (by rfl) ⟨218600, by rfl⟩ : syracuseStep 291467 = 437201) B437201
theorem B324247 : Blo 287828 324247 := bstep (se 1 (by rfl) ⟨243185, by rfl⟩ : syracuseStep 324247 = 486371) B486371
theorem B291479 : Blo 287828 291479 := bstep (se 1 (by rfl) ⟨218609, by rfl⟩ : syracuseStep 291479 = 437219) B437219
theorem B291499 : Blo 287828 291499 := bstep (se 1 (by rfl) ⟨218624, by rfl⟩ : syracuseStep 291499 = 437249) B437249
theorem B291511 : Blo 287828 291511 := bstep (se 1 (by rfl) ⟨218633, by rfl⟩ : syracuseStep 291511 = 437267) B437267
theorem B291531 : Blo 287828 291531 := bstep (se 1 (by rfl) ⟨218648, by rfl⟩ : syracuseStep 291531 = 437297) B437297
theorem B291543 : Blo 287828 291543 := bstep (se 1 (by rfl) ⟨218657, by rfl⟩ : syracuseStep 291543 = 437315) B437315
theorem B488153 : Blo 287828 488153 := bstep (se 2 (by rfl) ⟨183057, by rfl⟩ : syracuseStep 488153 = 366115) B366115
theorem B291563 : Blo 287828 291563 := bstep (se 1 (by rfl) ⟨218672, by rfl⟩ : syracuseStep 291563 = 437345) B437345
theorem B291575 : Blo 287828 291575 := bstep (se 1 (by rfl) ⟨218681, by rfl⟩ : syracuseStep 291575 = 437363) B437363
theorem B553729 : Blo 287828 553729 := bstep (se 2 (by rfl) ⟨207648, by rfl⟩ : syracuseStep 553729 = 415297) B415297
theorem B291595 : Blo 287828 291595 := bstep (se 1 (by rfl) ⟨218696, by rfl⟩ : syracuseStep 291595 = 437393) B437393
theorem B291607 : Blo 287828 291607 := bstep (se 1 (by rfl) ⟨218705, by rfl⟩ : syracuseStep 291607 = 437411) B437411
theorem B291627 : Blo 287828 291627 := bstep (se 1 (by rfl) ⟨218720, by rfl⟩ : syracuseStep 291627 = 437441) B437441
theorem B291639 : Blo 287828 291639 := bstep (se 1 (by rfl) ⟨218729, by rfl⟩ : syracuseStep 291639 = 437459) B437459
theorem B324427 : Blo 287828 324427 := bstep (se 1 (by rfl) ⟨243320, by rfl⟩ : syracuseStep 324427 = 486641) B486641
theorem B291659 : Blo 287828 291659 := bstep (se 1 (by rfl) ⟨218744, by rfl⟩ : syracuseStep 291659 = 437489) B437489
theorem B291671 : Blo 287828 291671 := bstep (se 1 (by rfl) ⟨218753, by rfl⟩ : syracuseStep 291671 = 437507) B437507
theorem B488281 : Blo 287828 488281 := bstep (se 2 (by rfl) ⟨183105, by rfl⟩ : syracuseStep 488281 = 366211) B366211
theorem B652121 : Blo 287828 652121 := bstep (se 2 (by rfl) ⟨244545, by rfl⟩ : syracuseStep 652121 = 489091) B489091
theorem B291691 : Blo 287828 291691 := bstep (se 1 (by rfl) ⟨218768, by rfl⟩ : syracuseStep 291691 = 437537) B437537
theorem B291703 : Blo 287828 291703 := bstep (se 1 (by rfl) ⟨218777, by rfl⟩ : syracuseStep 291703 = 437555) B437555
theorem B291723 : Blo 287828 291723 := bstep (se 1 (by rfl) ⟨218792, by rfl⟩ : syracuseStep 291723 = 437585) B437585
theorem B291735 : Blo 287828 291735 := bstep (se 1 (by rfl) ⟨218801, by rfl⟩ : syracuseStep 291735 = 437603) B437603
theorem B619417 : Blo 287828 619417 := bstep (se 2 (by rfl) ⟨232281, by rfl⟩ : syracuseStep 619417 = 464563) B464563
theorem B291755 : Blo 287828 291755 := bstep (se 1 (by rfl) ⟨218816, by rfl⟩ : syracuseStep 291755 = 437633) B437633
theorem B652211 : Blo 287828 652211 := bstep (se 1 (by rfl) ⟨489158, by rfl⟩ : syracuseStep 652211 = 978317) B978317
theorem B324535 : Blo 287828 324535 := bstep (se 1 (by rfl) ⟨243401, by rfl⟩ : syracuseStep 324535 = 486803) B486803
theorem B291767 : Blo 287828 291767 := bstep (se 1 (by rfl) ⟨218825, by rfl⟩ : syracuseStep 291767 = 437651) B437651
theorem B291787 : Blo 287828 291787 := bstep (se 1 (by rfl) ⟨218840, by rfl⟩ : syracuseStep 291787 = 437681) B437681
theorem B652247 : Blo 287828 652247 := bstep (se 1 (by rfl) ⟨489185, by rfl⟩ : syracuseStep 652247 = 978371) B978371
theorem B291799 : Blo 287828 291799 := bstep (se 1 (by rfl) ⟨218849, by rfl⟩ : syracuseStep 291799 = 437699) B437699
theorem B2192345 : Blo 287828 2192345 := bstep (se 2 (by rfl) ⟨822129, by rfl⟩ : syracuseStep 2192345 = 1644259) B1644259
theorem B291819 : Blo 287828 291819 := bstep (se 1 (by rfl) ⟨218864, by rfl⟩ : syracuseStep 291819 = 437729) B437729
theorem B979991 : Blo 287828 979991 := bstep (se 1 (by rfl) ⟨734993, by rfl⟩ : syracuseStep 979991 = 1469987) B1469987
theorem B619571 : Blo 287828 619571 := bstep (se 1 (by rfl) ⟨464678, by rfl⟩ : syracuseStep 619571 = 929357) B929357
theorem B324715 : Blo 287828 324715 := bstep (se 1 (by rfl) ⟨243536, by rfl⟩ : syracuseStep 324715 = 487073) B487073
theorem B652427 : Blo 287828 652427 := bstep (se 1 (by rfl) ⟨489320, by rfl⟩ : syracuseStep 652427 = 978641) B978641
theorem B652481 : Blo 287828 652481 := bstep (se 2 (by rfl) ⟨244680, by rfl⟩ : syracuseStep 652481 = 489361) B489361
theorem B324823 : Blo 287828 324823 := bstep (se 1 (by rfl) ⟨243617, by rfl⟩ : syracuseStep 324823 = 487235) B487235
theorem B521495 : Blo 287828 521495 := bstep (se 1 (by rfl) ⟨391121, by rfl⟩ : syracuseStep 521495 = 782243) B782243
theorem B325003 : Blo 287828 325003 := bstep (se 1 (by rfl) ⟨243752, by rfl⟩ : syracuseStep 325003 = 487505) B487505
theorem B488855 : Blo 287828 488855 := bstep (se 1 (by rfl) ⟨366641, by rfl⟩ : syracuseStep 488855 = 733283) B733283
theorem B652697 : Blo 287828 652697 := bstep (se 2 (by rfl) ⟨244761, by rfl⟩ : syracuseStep 652697 = 489523) B489523
theorem B652787 : Blo 287828 652787 := bstep (se 1 (by rfl) ⟨489590, by rfl⟩ : syracuseStep 652787 = 979181) B979181
theorem B325111 : Blo 287828 325111 := bstep (se 1 (by rfl) ⟨243833, by rfl⟩ : syracuseStep 325111 = 487667) B487667
theorem B488983 : Blo 287828 488983 := bstep (se 1 (by rfl) ⟨366737, by rfl⟩ : syracuseStep 488983 = 733475) B733475
theorem B652823 : Blo 287828 652823 := bstep (se 1 (by rfl) ⟨489617, by rfl⟩ : syracuseStep 652823 = 979235) B979235
theorem B620083 : Blo 287828 620083 := bstep (se 1 (by rfl) ⟨465062, by rfl⟩ : syracuseStep 620083 = 930125) B930125
theorem B980531 : Blo 287828 980531 := bstep (se 1 (by rfl) ⟨735398, by rfl⟩ : syracuseStep 980531 = 1470797) B1470797
theorem B1046105 : Blo 287828 1046105 := bstep (se 2 (by rfl) ⟨392289, by rfl⟩ : syracuseStep 1046105 = 784579) B784579
theorem B1767005 : Blo 287828 1767005 := bstep (se 3 (by rfl) ⟨331313, by rfl⟩ : syracuseStep 1767005 = 662627) B662627
theorem B1472093 : Blo 287828 1472093 := bstep (se 3 (by rfl) ⟨276017, by rfl⟩ : syracuseStep 1472093 = 552035) B552035
theorem B325291 : Blo 287828 325291 := bstep (se 1 (by rfl) ⟨243968, by rfl⟩ : syracuseStep 325291 = 487937) B487937
theorem B653003 : Blo 287828 653003 := bstep (se 1 (by rfl) ⟨489752, by rfl⟩ : syracuseStep 653003 = 979505) B979505
theorem B653057 : Blo 287828 653057 := bstep (se 2 (by rfl) ⟨244896, by rfl⟩ : syracuseStep 653057 = 489793) B489793
theorem B325399 : Blo 287828 325399 := bstep (se 1 (by rfl) ⟨244049, by rfl⟩ : syracuseStep 325399 = 488099) B488099
theorem B980801 : Blo 287828 980801 := bstep (se 2 (by rfl) ⟨367800, by rfl⟩ : syracuseStep 980801 = 735601) B735601
theorem B1570711 : Blo 287828 1570711 := bstep (se 1 (by rfl) ⟨1178033, by rfl⟩ : syracuseStep 1570711 = 2356067) B2356067
theorem B1177517 : Blo 287828 1177517 := bstep (se 3 (by rfl) ⟨220784, by rfl⟩ : syracuseStep 1177517 = 441569) B441569
theorem B325579 : Blo 287828 325579 := bstep (se 1 (by rfl) ⟨244184, by rfl⟩ : syracuseStep 325579 = 488369) B488369
theorem B653273 : Blo 287828 653273 := bstep (se 2 (by rfl) ⟨244977, by rfl⟩ : syracuseStep 653273 = 489955) B489955
theorem B653363 : Blo 287828 653363 := bstep (se 1 (by rfl) ⟨490022, by rfl⟩ : syracuseStep 653363 = 980045) B980045
theorem B325687 : Blo 287828 325687 := bstep (se 1 (by rfl) ⟨244265, by rfl⟩ : syracuseStep 325687 = 488531) B488531
theorem B653399 : Blo 287828 653399 := bstep (se 1 (by rfl) ⟨490049, by rfl⟩ : syracuseStep 653399 = 980099) B980099
theorem B489611 : Blo 287828 489611 := bstep (se 1 (by rfl) ⟨367208, by rfl⟩ : syracuseStep 489611 = 734417) B734417
theorem B620759 : Blo 287828 620759 := bstep (se 1 (by rfl) ⟨465569, by rfl⟩ : syracuseStep 620759 = 931139) B931139
theorem B325867 : Blo 287828 325867 := bstep (se 1 (by rfl) ⟨244400, by rfl⟩ : syracuseStep 325867 = 488801) B488801
theorem B522497 : Blo 287828 522497 := bstep (se 2 (by rfl) ⟨195936, by rfl⟩ : syracuseStep 522497 = 391873) B391873
theorem B620801 : Blo 287828 620801 := bstep (se 2 (by rfl) ⟨232800, by rfl⟩ : syracuseStep 620801 = 465601) B465601
theorem B489739 : Blo 287828 489739 := bstep (se 1 (by rfl) ⟨367304, by rfl⟩ : syracuseStep 489739 = 734609) B734609
theorem B653579 : Blo 287828 653579 := bstep (se 1 (by rfl) ⟨490184, by rfl⟩ : syracuseStep 653579 = 980369) B980369
theorem B653633 : Blo 287828 653633 := bstep (se 2 (by rfl) ⟨245112, by rfl⟩ : syracuseStep 653633 = 490225) B490225
theorem B325975 : Blo 287828 325975 := bstep (se 1 (by rfl) ⟨244481, by rfl⟩ : syracuseStep 325975 = 488963) B488963
theorem B981341 : Blo 287828 981341 := bstep (se 3 (by rfl) ⟨184001, by rfl⟩ : syracuseStep 981341 = 368003) B368003
theorem B489881 : Blo 287828 489881 := bstep (se 2 (by rfl) ⟨183705, by rfl⟩ : syracuseStep 489881 = 367411) B367411
theorem B326155 : Blo 287828 326155 := bstep (se 1 (by rfl) ⟨244616, by rfl⟩ : syracuseStep 326155 = 489233) B489233
theorem B7043597 : Blo 287828 7043597 := bstep (se 3 (by rfl) ⟨1320674, by rfl⟩ : syracuseStep 7043597 = 2641349) B2641349
theorem B490009 : Blo 287828 490009 := bstep (se 2 (by rfl) ⟨183753, by rfl⟩ : syracuseStep 490009 = 367507) B367507
theorem B653849 : Blo 287828 653849 := bstep (se 2 (by rfl) ⟨245193, by rfl⟩ : syracuseStep 653849 = 490387) B490387
theorem B653939 : Blo 287828 653939 := bstep (se 1 (by rfl) ⟨490454, by rfl⟩ : syracuseStep 653939 = 980909) B980909
theorem B326263 : Blo 287828 326263 := bstep (se 1 (by rfl) ⟨244697, by rfl⟩ : syracuseStep 326263 = 489395) B489395
theorem B653975 : Blo 287828 653975 := bstep (se 1 (by rfl) ⟨490481, by rfl⟩ : syracuseStep 653975 = 980963) B980963
theorem B326443 : Blo 287828 326443 := bstep (se 1 (by rfl) ⟨244832, by rfl⟩ : syracuseStep 326443 = 489665) B489665
theorem B293687 : Blo 287828 293687 := bstep (se 1 (by rfl) ⟨220265, by rfl⟩ : syracuseStep 293687 = 440531) B440531
theorem B654155 : Blo 287828 654155 := bstep (se 1 (by rfl) ⟨490616, by rfl⟩ : syracuseStep 654155 = 981233) B981233
theorem B1243993 : Blo 287828 1243993 := bstep (se 2 (by rfl) ⟨466497, by rfl⟩ : syracuseStep 1243993 = 932995) B932995
theorem B654209 : Blo 287828 654209 := bstep (se 2 (by rfl) ⟨245328, by rfl⟩ : syracuseStep 654209 = 490657) B490657
theorem B326551 : Blo 287828 326551 := bstep (se 1 (by rfl) ⟨244913, by rfl⟩ : syracuseStep 326551 = 489827) B489827
theorem B1866817 : Blo 287828 1866817 := bstep (se 2 (by rfl) ⟨700056, by rfl⟩ : syracuseStep 1866817 = 1400113) B1400113
theorem B8879179 : Blo 287828 8879179 := bstep (se 1 (by rfl) ⟨6659384, by rfl⟩ : syracuseStep 8879179 = 13318769) B13318769
theorem B326731 : Blo 287828 326731 := bstep (se 1 (by rfl) ⟨245048, by rfl⟩ : syracuseStep 326731 = 490097) B490097
theorem B490583 : Blo 287828 490583 := bstep (se 1 (by rfl) ⟨367937, by rfl⟩ : syracuseStep 490583 = 735875) B735875
theorem B654425 : Blo 287828 654425 := bstep (se 2 (by rfl) ⟨245409, by rfl⟩ : syracuseStep 654425 = 490819) B490819
theorem B588953 : Blo 287828 588953 := bstep (se 2 (by rfl) ⟨220857, by rfl⟩ : syracuseStep 588953 = 441715) B441715
theorem B654515 : Blo 287828 654515 := bstep (se 1 (by rfl) ⟨490886, by rfl⟩ : syracuseStep 654515 = 981773) B981773
theorem B326839 : Blo 287828 326839 := bstep (se 1 (by rfl) ⟨245129, by rfl⟩ : syracuseStep 326839 = 490259) B490259
theorem B490711 : Blo 287828 490711 := bstep (se 1 (by rfl) ⟨368033, by rfl⟩ : syracuseStep 490711 = 736067) B736067
theorem B654551 : Blo 287828 654551 := bstep (se 1 (by rfl) ⟨490913, by rfl⟩ : syracuseStep 654551 = 981827) B981827
theorem B3734849 : Blo 287828 3734849 := bstep (se 2 (by rfl) ⟨1400568, by rfl⟩ : syracuseStep 3734849 = 2801137) B2801137
theorem B327019 : Blo 287828 327019 := bstep (se 1 (by rfl) ⟨245264, by rfl⟩ : syracuseStep 327019 = 490529) B490529
theorem B654731 : Blo 287828 654731 := bstep (se 1 (by rfl) ⟨491048, by rfl⟩ : syracuseStep 654731 = 982097) B982097
theorem B654785 : Blo 287828 654785 := bstep (se 2 (by rfl) ⟨245544, by rfl⟩ : syracuseStep 654785 = 491089) B491089
theorem B1244609 : Blo 287828 1244609 := bstep (se 2 (by rfl) ⟨466728, by rfl⟩ : syracuseStep 1244609 = 933457) B933457
theorem B982475 : Blo 287828 982475 := bstep (se 1 (by rfl) ⟨736856, by rfl⟩ : syracuseStep 982475 = 1473713) B1473713
theorem B327127 : Blo 287828 327127 := bstep (se 1 (by rfl) ⟨245345, by rfl⟩ : syracuseStep 327127 = 490691) B490691
theorem B327307 : Blo 287828 327307 := bstep (se 1 (by rfl) ⟨245480, by rfl⟩ : syracuseStep 327307 = 490961) B490961
theorem B1474199 : Blo 287828 1474199 := bstep (se 1 (by rfl) ⟨1105649, by rfl⟩ : syracuseStep 1474199 = 2211299) B2211299
theorem B655001 : Blo 287828 655001 := bstep (se 2 (by rfl) ⟨245625, by rfl⟩ : syracuseStep 655001 = 491251) B491251
theorem B982745 : Blo 287828 982745 := bstep (se 2 (by rfl) ⟨368529, by rfl⟩ : syracuseStep 982745 = 737059) B737059
theorem B655091 : Blo 287828 655091 := bstep (se 1 (by rfl) ⟨491318, by rfl⟩ : syracuseStep 655091 = 982637) B982637
theorem B327415 : Blo 287828 327415 := bstep (se 1 (by rfl) ⟨245561, by rfl⟩ : syracuseStep 327415 = 491123) B491123
theorem B655127 : Blo 287828 655127 := bstep (se 1 (by rfl) ⟨491345, by rfl⟩ : syracuseStep 655127 = 982691) B982691
theorem B491339 : Blo 287828 491339 := bstep (se 1 (by rfl) ⟨368504, by rfl⟩ : syracuseStep 491339 = 737009) B737009
theorem B327595 : Blo 287828 327595 := bstep (se 1 (by rfl) ⟨245696, by rfl⟩ : syracuseStep 327595 = 491393) B491393
theorem B1572787 : Blo 287828 1572787 := bstep (se 1 (by rfl) ⟨1179590, by rfl⟩ : syracuseStep 1572787 = 2359181) B2359181
theorem B491467 : Blo 287828 491467 := bstep (se 1 (by rfl) ⟨368600, by rfl⟩ : syracuseStep 491467 = 737201) B737201
theorem B655307 : Blo 287828 655307 := bstep (se 1 (by rfl) ⟨491480, by rfl⟩ : syracuseStep 655307 = 982961) B982961
theorem B1015769 : Blo 287828 1015769 := bstep (se 2 (by rfl) ⟨380913, by rfl⟩ : syracuseStep 1015769 = 761827) B761827
theorem B983069 : Blo 287828 983069 := bstep (se 3 (by rfl) ⟨184325, by rfl⟩ : syracuseStep 983069 = 368651) B368651
theorem B327739 : Blo 287828 327739 := bstep (se 1 (by rfl) ⟨245804, by rfl⟩ : syracuseStep 327739 = 491609) B491609
theorem B524407 : Blo 287828 524407 := bstep (se 1 (by rfl) ⟨393305, by rfl⟩ : syracuseStep 524407 = 786611) B786611
theorem B655631 : Blo 287828 655631 := bstep (se 1 (by rfl) ⟨491723, by rfl⟩ : syracuseStep 655631 = 983447) B983447
theorem B491791 : Blo 287828 491791 := bstep (se 1 (by rfl) ⟨368843, by rfl⟩ : syracuseStep 491791 = 737687) B737687
theorem B655649 : Blo 287828 655649 := bstep (se 2 (by rfl) ⟨245868, by rfl⟩ : syracuseStep 655649 = 491737) B491737
theorem B295303 : Blo 287828 295303 := bstep (se 1 (by rfl) ⟨221477, by rfl⟩ : syracuseStep 295303 = 442955) B442955
theorem B328207 : Blo 287828 328207 := bstep (se 1 (by rfl) ⟨246155, by rfl⟩ : syracuseStep 328207 = 492311) B492311
theorem B655991 : Blo 287828 655991 := bstep (se 1 (by rfl) ⟨491993, by rfl⟩ : syracuseStep 655991 = 983987) B983987
theorem B1114825 : Blo 287828 1114825 := bstep (se 2 (by rfl) ⟨418059, by rfl⟩ : syracuseStep 1114825 = 836119) B836119
theorem B103383793 : Blo 287828 103383793 := bstep (se 2 (by rfl) ⟨38768922, by rfl⟩ : syracuseStep 103383793 = 77537845) B77537845
theorem B656171 : Blo 287828 656171 := bstep (se 1 (by rfl) ⟨492128, by rfl⟩ : syracuseStep 656171 = 984257) B984257
theorem B492331 : Blo 287828 492331 := bstep (se 1 (by rfl) ⟨369248, by rfl⟩ : syracuseStep 492331 = 738497) B738497
theorem B2097971 : Blo 287828 2097971 := bstep (se 1 (by rfl) ⟨1573478, by rfl⟩ : syracuseStep 2097971 = 3146957) B3146957
theorem B820115 : Blo 287828 820115 := bstep (se 1 (by rfl) ⟨615086, by rfl⟩ : syracuseStep 820115 = 1230173) B1230173
theorem B590995 : Blo 287828 590995 := bstep (se 1 (by rfl) ⟨443246, by rfl⟩ : syracuseStep 590995 = 886493) B886493
theorem B656531 : Blo 287828 656531 := bstep (se 1 (by rfl) ⟨492398, by rfl⟩ : syracuseStep 656531 = 984797) B984797
theorem B853145 : Blo 287828 853145 := bstep (se 2 (by rfl) ⟨319929, by rfl⟩ : syracuseStep 853145 = 639859) B639859
theorem B656585 : Blo 287828 656585 := bstep (se 2 (by rfl) ⟨246219, by rfl⟩ : syracuseStep 656585 = 492439) B492439
theorem B984473 : Blo 287828 984473 := bstep (se 2 (by rfl) ⟨369177, by rfl⟩ : syracuseStep 984473 = 738355) B738355
theorem B787897 : Blo 287828 787897 := bstep (se 2 (by rfl) ⟨295461, by rfl⟩ : syracuseStep 787897 = 590923) B590923
theorem B755353 : Blo 287828 755353 := bstep (se 2 (by rfl) ⟨283257, by rfl⟩ : syracuseStep 755353 = 566515) B566515
theorem B1476467 : Blo 287828 1476467 := bstep (se 1 (by rfl) ⟨1107350, by rfl⟩ : syracuseStep 1476467 = 2214701) B2214701
theorem B2459555 : Blo 287828 2459555 := bstep (se 1 (by rfl) ⟨1844666, by rfl⟩ : syracuseStep 2459555 = 3689333) B3689333
theorem B657353 : Blo 287828 657353 := bstep (se 2 (by rfl) ⟨246507, by rfl⟩ : syracuseStep 657353 = 493015) B493015
theorem B1771721 : Blo 287828 1771721 := bstep (se 2 (by rfl) ⟨664395, by rfl⟩ : syracuseStep 1771721 = 1328791) B1328791
theorem B1181897 : Blo 287828 1181897 := bstep (se 2 (by rfl) ⟨443211, by rfl⟩ : syracuseStep 1181897 = 886423) B886423
theorem B821515 : Blo 287828 821515 := bstep (se 1 (by rfl) ⟨616136, by rfl⟩ : syracuseStep 821515 = 1232273) B1232273
theorem B1476953 : Blo 287828 1476953 := bstep (se 2 (by rfl) ⟨553857, by rfl⟩ : syracuseStep 1476953 = 1107715) B1107715
theorem B821789 : Blo 287828 821789 := bstep (se 3 (by rfl) ⟨154085, by rfl⟩ : syracuseStep 821789 = 308171) B308171
theorem B1641161 : Blo 287828 1641161 := bstep (se 2 (by rfl) ⟨615435, by rfl⟩ : syracuseStep 1641161 = 1230871) B1230871
theorem B3706145 : Blo 287828 3706145 := bstep (se 2 (by rfl) ⟨1389804, by rfl⟩ : syracuseStep 3706145 = 2779609) B2779609
theorem B3509725 : Blo 287828 3509725 := bstep (se 3 (by rfl) ⟨658073, by rfl⟩ : syracuseStep 3509725 = 1316147) B1316147
theorem B2985437 : Blo 287828 2985437 := bstep (se 3 (by rfl) ⟨559769, by rfl⟩ : syracuseStep 2985437 = 1119539) B1119539
theorem B13471373 : Blo 287828 13471373 := bstep (se 3 (by rfl) ⟨2525882, by rfl⟩ : syracuseStep 13471373 = 5051765) B5051765
theorem B17927831 : Blo 287828 17927831 := bstep (se 1 (by rfl) ⟨13445873, by rfl⟩ : syracuseStep 17927831 = 26891747) B26891747
theorem B725177 : Blo 287828 725177 := bstep (se 2 (by rfl) ⟨271941, by rfl⟩ : syracuseStep 725177 = 543883) B543883
theorem B1643075 : Blo 287828 1643075 := bstep (se 1 (by rfl) ⟨1232306, by rfl⟩ : syracuseStep 1643075 = 2464613) B2464613
theorem B2790065 : Blo 287828 2790065 := bstep (se 2 (by rfl) ⟨1046274, by rfl⟩ : syracuseStep 2790065 = 2092549) B2092549
theorem B824249 : Blo 287828 824249 := bstep (se 2 (by rfl) ⟨309093, by rfl⟩ : syracuseStep 824249 = 618187) B618187
theorem B824363 : Blo 287828 824363 := bstep (se 1 (by rfl) ⟨618272, by rfl⟩ : syracuseStep 824363 = 1236545) B1236545
theorem B988247 : Blo 287828 988247 := bstep (se 1 (by rfl) ⟨741185, by rfl⟩ : syracuseStep 988247 = 1482371) B1482371
theorem B627983 : Blo 287828 627983 := bstep (se 1 (by rfl) ⟨470987, by rfl⟩ : syracuseStep 627983 = 941975) B941975
theorem B1512857 : Blo 287828 1512857 := bstep (se 2 (by rfl) ⟨567321, by rfl⟩ : syracuseStep 1512857 = 1134643) B1134643
theorem B431759 : Blo 287828 431759 := bstep (se 1 (by rfl) ⟨323819, by rfl⟩ : syracuseStep 431759 = 647639) B647639
theorem B431801 : Blo 287828 431801 := bstep (se 2 (by rfl) ⟨161925, by rfl⟩ : syracuseStep 431801 = 323851) B323851
theorem B431879 : Blo 287828 431879 := bstep (se 1 (by rfl) ⟨323909, by rfl⟩ : syracuseStep 431879 = 647819) B647819
theorem B3610403 : Blo 287828 3610403 := bstep (se 1 (by rfl) ⟨2707802, by rfl⟩ : syracuseStep 3610403 = 5415605) B5415605
theorem B3315491 : Blo 287828 3315491 := bstep (se 1 (by rfl) ⟨2486618, by rfl⟩ : syracuseStep 3315491 = 4973237) B4973237
theorem B431915 : Blo 287828 431915 := bstep (se 1 (by rfl) ⟨323936, by rfl⟩ : syracuseStep 431915 = 647873) B647873
theorem B431945 : Blo 287828 431945 := bstep (se 2 (by rfl) ⟨161979, by rfl⟩ : syracuseStep 431945 = 323959) B323959
theorem B432059 : Blo 287828 432059 := bstep (se 1 (by rfl) ⟨324044, by rfl⟩ : syracuseStep 432059 = 648089) B648089
theorem B432119 : Blo 287828 432119 := bstep (se 1 (by rfl) ⟨324089, by rfl⟩ : syracuseStep 432119 = 648179) B648179
theorem B2660363 : Blo 287828 2660363 := bstep (se 1 (by rfl) ⟨1995272, by rfl⟩ : syracuseStep 2660363 = 3990545) B3990545
theorem B432143 : Blo 287828 432143 := bstep (se 1 (by rfl) ⟨324107, by rfl⟩ : syracuseStep 432143 = 648215) B648215
theorem B432185 : Blo 287828 432185 := bstep (se 2 (by rfl) ⟨162069, by rfl⟩ : syracuseStep 432185 = 324139) B324139
theorem B432263 : Blo 287828 432263 := bstep (se 1 (by rfl) ⟨324197, by rfl⟩ : syracuseStep 432263 = 648395) B648395
theorem B825491 : Blo 287828 825491 := bstep (se 1 (by rfl) ⟨619118, by rfl⟩ : syracuseStep 825491 = 1238237) B1238237
theorem B432299 : Blo 287828 432299 := bstep (se 1 (by rfl) ⟨324224, by rfl⟩ : syracuseStep 432299 = 648449) B648449
theorem B366763 : Blo 287828 366763 := bstep (se 1 (by rfl) ⟨275072, by rfl⟩ : syracuseStep 366763 = 550145) B550145
theorem B432329 : Blo 287828 432329 := bstep (se 2 (by rfl) ⟨162123, by rfl⟩ : syracuseStep 432329 = 324247) B324247
theorem B432443 : Blo 287828 432443 := bstep (se 1 (by rfl) ⟨324332, by rfl⟩ : syracuseStep 432443 = 648665) B648665
theorem B432503 : Blo 287828 432503 := bstep (se 1 (by rfl) ⟨324377, by rfl⟩ : syracuseStep 432503 = 648755) B648755
theorem B432527 : Blo 287828 432527 := bstep (se 1 (by rfl) ⟨324395, by rfl⟩ : syracuseStep 432527 = 648791) B648791
theorem B432569 : Blo 287828 432569 := bstep (se 2 (by rfl) ⟨162213, by rfl⟩ : syracuseStep 432569 = 324427) B324427
theorem B2202065 : Blo 287828 2202065 := bstep (se 2 (by rfl) ⟨825774, by rfl⟩ : syracuseStep 2202065 = 1651549) B1651549
theorem B432647 : Blo 287828 432647 := bstep (se 1 (by rfl) ⟨324485, by rfl⟩ : syracuseStep 432647 = 648971) B648971
theorem B825889 : Blo 287828 825889 := bstep (se 2 (by rfl) ⟨309708, by rfl⟩ : syracuseStep 825889 = 619417) B619417
theorem B432683 : Blo 287828 432683 := bstep (se 1 (by rfl) ⟨324512, by rfl⟩ : syracuseStep 432683 = 649025) B649025
theorem B432713 : Blo 287828 432713 := bstep (se 2 (by rfl) ⟨162267, by rfl⟩ : syracuseStep 432713 = 324535) B324535
theorem B432827 : Blo 287828 432827 := bstep (se 1 (by rfl) ⟨324620, by rfl⟩ : syracuseStep 432827 = 649241) B649241
theorem B432887 : Blo 287828 432887 := bstep (se 1 (by rfl) ⟨324665, by rfl⟩ : syracuseStep 432887 = 649331) B649331
theorem B432911 : Blo 287828 432911 := bstep (se 1 (by rfl) ⟨324683, by rfl⟩ : syracuseStep 432911 = 649367) B649367
theorem B432953 : Blo 287828 432953 := bstep (se 2 (by rfl) ⟨162357, by rfl⟩ : syracuseStep 432953 = 324715) B324715
theorem B433031 : Blo 287828 433031 := bstep (se 1 (by rfl) ⟨324773, by rfl⟩ : syracuseStep 433031 = 649547) B649547
theorem B433067 : Blo 287828 433067 := bstep (se 1 (by rfl) ⟨324800, by rfl⟩ : syracuseStep 433067 = 649601) B649601
theorem B433097 : Blo 287828 433097 := bstep (se 2 (by rfl) ⟨162411, by rfl⟩ : syracuseStep 433097 = 324823) B324823
theorem B433211 : Blo 287828 433211 := bstep (se 1 (by rfl) ⟨324908, by rfl⟩ : syracuseStep 433211 = 649817) B649817
theorem B433271 : Blo 287828 433271 := bstep (se 1 (by rfl) ⟨324953, by rfl⟩ : syracuseStep 433271 = 649907) B649907
theorem B367735 : Blo 287828 367735 := bstep (se 1 (by rfl) ⟨275801, by rfl⟩ : syracuseStep 367735 = 551603) B551603
theorem B433295 : Blo 287828 433295 := bstep (se 1 (by rfl) ⟨324971, by rfl⟩ : syracuseStep 433295 = 649943) B649943
theorem B433337 : Blo 287828 433337 := bstep (se 2 (by rfl) ⟨162501, by rfl⟩ : syracuseStep 433337 = 325003) B325003
theorem B433415 : Blo 287828 433415 := bstep (se 1 (by rfl) ⟨325061, by rfl⟩ : syracuseStep 433415 = 650123) B650123
theorem B433451 : Blo 287828 433451 := bstep (se 1 (by rfl) ⟨325088, by rfl⟩ : syracuseStep 433451 = 650177) B650177
theorem B433481 : Blo 287828 433481 := bstep (se 2 (by rfl) ⟨162555, by rfl⟩ : syracuseStep 433481 = 325111) B325111
theorem B695671 : Blo 287828 695671 := bstep (se 1 (by rfl) ⟨521753, by rfl⟩ : syracuseStep 695671 = 1043507) B1043507
theorem B826777 : Blo 287828 826777 := bstep (se 2 (by rfl) ⟨310041, by rfl⟩ : syracuseStep 826777 = 620083) B620083
theorem B433595 : Blo 287828 433595 := bstep (se 1 (by rfl) ⟨325196, by rfl⟩ : syracuseStep 433595 = 650393) B650393
theorem B368059 : Blo 287828 368059 := bstep (se 1 (by rfl) ⟨276044, by rfl⟩ : syracuseStep 368059 = 552089) B552089
theorem B433655 : Blo 287828 433655 := bstep (se 1 (by rfl) ⟨325241, by rfl⟩ : syracuseStep 433655 = 650483) B650483
theorem B433679 : Blo 287828 433679 := bstep (se 1 (by rfl) ⟨325259, by rfl⟩ : syracuseStep 433679 = 650519) B650519
theorem B433721 : Blo 287828 433721 := bstep (se 2 (by rfl) ⟨162645, by rfl⟩ : syracuseStep 433721 = 325291) B325291
theorem B728635 : Blo 287828 728635 := bstep (se 1 (by rfl) ⟨546476, by rfl⟩ : syracuseStep 728635 = 1092953) B1092953
theorem B4726349 : Blo 287828 4726349 := bstep (se 3 (by rfl) ⟨886190, by rfl⟩ : syracuseStep 4726349 = 1772381) B1772381
theorem B433799 : Blo 287828 433799 := bstep (se 1 (by rfl) ⟨325349, by rfl⟩ : syracuseStep 433799 = 650699) B650699
theorem B433835 : Blo 287828 433835 := bstep (se 1 (by rfl) ⟨325376, by rfl⟩ : syracuseStep 433835 = 650753) B650753
theorem B728777 : Blo 287828 728777 := bstep (se 2 (by rfl) ⟨273291, by rfl⟩ : syracuseStep 728777 = 546583) B546583
theorem B433865 : Blo 287828 433865 := bstep (se 2 (by rfl) ⟨162699, by rfl⟩ : syracuseStep 433865 = 325399) B325399
theorem B466703 : Blo 287828 466703 := bstep (se 1 (by rfl) ⟨350027, by rfl⟩ : syracuseStep 466703 = 700055) B700055
theorem B827165 : Blo 287828 827165 := bstep (se 3 (by rfl) ⟨155093, by rfl⟩ : syracuseStep 827165 = 310187) B310187
theorem B433979 : Blo 287828 433979 := bstep (se 1 (by rfl) ⟨325484, by rfl⟩ : syracuseStep 433979 = 650969) B650969
theorem B434039 : Blo 287828 434039 := bstep (se 1 (by rfl) ⟨325529, by rfl⟩ : syracuseStep 434039 = 651059) B651059
theorem B434063 : Blo 287828 434063 := bstep (se 1 (by rfl) ⟨325547, by rfl⟩ : syracuseStep 434063 = 651095) B651095
theorem B434105 : Blo 287828 434105 := bstep (se 2 (by rfl) ⟨162789, by rfl⟩ : syracuseStep 434105 = 325579) B325579
theorem B434183 : Blo 287828 434183 := bstep (se 1 (by rfl) ⟨325637, by rfl⟩ : syracuseStep 434183 = 651275) B651275
theorem B729121 : Blo 287828 729121 := bstep (se 2 (by rfl) ⟨273420, by rfl⟩ : syracuseStep 729121 = 546841) B546841
theorem B434219 : Blo 287828 434219 := bstep (se 1 (by rfl) ⟨325664, by rfl⟩ : syracuseStep 434219 = 651329) B651329
theorem B434249 : Blo 287828 434249 := bstep (se 2 (by rfl) ⟨162843, by rfl⟩ : syracuseStep 434249 = 325687) B325687
theorem B434363 : Blo 287828 434363 := bstep (se 1 (by rfl) ⟨325772, by rfl⟩ : syracuseStep 434363 = 651545) B651545
theorem B434423 : Blo 287828 434423 := bstep (se 1 (by rfl) ⟨325817, by rfl⟩ : syracuseStep 434423 = 651635) B651635
theorem B434447 : Blo 287828 434447 := bstep (se 1 (by rfl) ⟨325835, by rfl⟩ : syracuseStep 434447 = 651671) B651671
theorem B434489 : Blo 287828 434489 := bstep (se 2 (by rfl) ⟨162933, by rfl⟩ : syracuseStep 434489 = 325867) B325867
theorem B696691 : Blo 287828 696691 := bstep (se 1 (by rfl) ⟨522518, by rfl⟩ : syracuseStep 696691 = 1045037) B1045037
theorem B434567 : Blo 287828 434567 := bstep (se 1 (by rfl) ⟨325925, by rfl⟩ : syracuseStep 434567 = 651851) B651851
theorem B369031 : Blo 287828 369031 := bstep (se 1 (by rfl) ⟨276773, by rfl⟩ : syracuseStep 369031 = 553547) B553547
theorem B1646993 : Blo 287828 1646993 := bstep (se 2 (by rfl) ⟨617622, by rfl⟩ : syracuseStep 1646993 = 1235245) B1235245
theorem B1122707 : Blo 287828 1122707 := bstep (se 1 (by rfl) ⟨842030, by rfl⟩ : syracuseStep 1122707 = 1684061) B1684061
theorem B434603 : Blo 287828 434603 := bstep (se 1 (by rfl) ⟨325952, by rfl⟩ : syracuseStep 434603 = 651905) B651905
theorem B434633 : Blo 287828 434633 := bstep (se 2 (by rfl) ⟨162987, by rfl⟩ : syracuseStep 434633 = 325975) B325975
theorem B434747 : Blo 287828 434747 := bstep (se 1 (by rfl) ⟨326060, by rfl⟩ : syracuseStep 434747 = 652121) B652121
theorem B729719 : Blo 287828 729719 := bstep (se 1 (by rfl) ⟨547289, by rfl⟩ : syracuseStep 729719 = 1094579) B1094579
theorem B434807 : Blo 287828 434807 := bstep (se 1 (by rfl) ⟨326105, by rfl⟩ : syracuseStep 434807 = 652211) B652211
theorem B434831 : Blo 287828 434831 := bstep (se 1 (by rfl) ⟨326123, by rfl⟩ : syracuseStep 434831 = 652247) B652247
theorem B434873 : Blo 287828 434873 := bstep (se 2 (by rfl) ⟨163077, by rfl⟩ : syracuseStep 434873 = 326155) B326155
theorem B434951 : Blo 287828 434951 := bstep (se 1 (by rfl) ⟨326213, by rfl⟩ : syracuseStep 434951 = 652427) B652427
theorem B434987 : Blo 287828 434987 := bstep (se 1 (by rfl) ⟨326240, by rfl⟩ : syracuseStep 434987 = 652481) B652481
theorem B664379 : Blo 287828 664379 := bstep (se 1 (by rfl) ⟨498284, by rfl⟩ : syracuseStep 664379 = 996569) B996569
theorem B435017 : Blo 287828 435017 := bstep (se 2 (by rfl) ⟨163131, by rfl⟩ : syracuseStep 435017 = 326263) B326263
theorem B1647449 : Blo 287828 1647449 := bstep (se 2 (by rfl) ⟨617793, by rfl⟩ : syracuseStep 1647449 = 1235587) B1235587
theorem B435131 : Blo 287828 435131 := bstep (se 1 (by rfl) ⟨326348, by rfl⟩ : syracuseStep 435131 = 652697) B652697
theorem B435191 : Blo 287828 435191 := bstep (se 1 (by rfl) ⟨326393, by rfl⟩ : syracuseStep 435191 = 652787) B652787
theorem B435215 : Blo 287828 435215 := bstep (se 1 (by rfl) ⟨326411, by rfl⟩ : syracuseStep 435215 = 652823) B652823
theorem B435257 : Blo 287828 435257 := bstep (se 2 (by rfl) ⟨163221, by rfl⟩ : syracuseStep 435257 = 326443) B326443
theorem B697403 : Blo 287828 697403 := bstep (se 1 (by rfl) ⟨523052, by rfl⟩ : syracuseStep 697403 = 1046105) B1046105
theorem B435335 : Blo 287828 435335 := bstep (se 1 (by rfl) ⟨326501, by rfl⟩ : syracuseStep 435335 = 653003) B653003
theorem B435371 : Blo 287828 435371 := bstep (se 1 (by rfl) ⟨326528, by rfl⟩ : syracuseStep 435371 = 653057) B653057
theorem B435401 : Blo 287828 435401 := bstep (se 2 (by rfl) ⟨163275, by rfl⟩ : syracuseStep 435401 = 326551) B326551
theorem B1844461 : Blo 287828 1844461 := bstep (se 3 (by rfl) ⟨345836, by rfl⟩ : syracuseStep 1844461 = 691673) B691673
theorem B3286331 : Blo 287828 3286331 := bstep (se 1 (by rfl) ⟨2464748, by rfl⟩ : syracuseStep 3286331 = 4929497) B4929497
theorem B435515 : Blo 287828 435515 := bstep (se 1 (by rfl) ⟨326636, by rfl⟩ : syracuseStep 435515 = 653273) B653273
theorem B435575 : Blo 287828 435575 := bstep (se 1 (by rfl) ⟨326681, by rfl⟩ : syracuseStep 435575 = 653363) B653363
theorem B435599 : Blo 287828 435599 := bstep (se 1 (by rfl) ⟨326699, by rfl⟩ : syracuseStep 435599 = 653399) B653399
theorem B664979 : Blo 287828 664979 := bstep (se 1 (by rfl) ⟨498734, by rfl⟩ : syracuseStep 664979 = 997469) B997469
theorem B11838905 : Blo 287828 11838905 := bstep (se 2 (by rfl) ⟨4439589, by rfl⟩ : syracuseStep 11838905 = 8879179) B8879179
theorem B435641 : Blo 287828 435641 := bstep (se 2 (by rfl) ⟨163365, by rfl⟩ : syracuseStep 435641 = 326731) B326731
theorem B435719 : Blo 287828 435719 := bstep (se 1 (by rfl) ⟨326789, by rfl⟩ : syracuseStep 435719 = 653579) B653579
theorem B435755 : Blo 287828 435755 := bstep (se 1 (by rfl) ⟨326816, by rfl⟩ : syracuseStep 435755 = 653633) B653633
theorem B435785 : Blo 287828 435785 := bstep (se 2 (by rfl) ⟨163419, by rfl⟩ : syracuseStep 435785 = 326839) B326839
theorem B4695731 : Blo 287828 4695731 := bstep (se 1 (by rfl) ⟨3521798, by rfl⟩ : syracuseStep 4695731 = 7043597) B7043597
theorem B435899 : Blo 287828 435899 := bstep (se 1 (by rfl) ⟨326924, by rfl⟩ : syracuseStep 435899 = 653849) B653849
theorem B435959 : Blo 287828 435959 := bstep (se 1 (by rfl) ⟨326969, by rfl⟩ : syracuseStep 435959 = 653939) B653939
theorem B435983 : Blo 287828 435983 := bstep (se 1 (by rfl) ⟨326987, by rfl⟩ : syracuseStep 435983 = 653975) B653975
theorem B436025 : Blo 287828 436025 := bstep (se 2 (by rfl) ⟨163509, by rfl⟩ : syracuseStep 436025 = 327019) B327019
theorem B731015 : Blo 287828 731015 := bstep (se 1 (by rfl) ⟨548261, by rfl⟩ : syracuseStep 731015 = 1096523) B1096523
theorem B436103 : Blo 287828 436103 := bstep (se 1 (by rfl) ⟨327077, by rfl⟩ : syracuseStep 436103 = 654155) B654155
theorem B436139 : Blo 287828 436139 := bstep (se 1 (by rfl) ⟨327104, by rfl⟩ : syracuseStep 436139 = 654209) B654209
theorem B731065 : Blo 287828 731065 := bstep (se 2 (by rfl) ⟨274149, by rfl⟩ : syracuseStep 731065 = 548299) B548299
theorem B436169 : Blo 287828 436169 := bstep (se 2 (by rfl) ⟨163563, by rfl⟩ : syracuseStep 436169 = 327127) B327127
theorem B436283 : Blo 287828 436283 := bstep (se 1 (by rfl) ⟨327212, by rfl⟩ : syracuseStep 436283 = 654425) B654425
theorem B436343 : Blo 287828 436343 := bstep (se 1 (by rfl) ⟨327257, by rfl⟩ : syracuseStep 436343 = 654515) B654515
theorem B436367 : Blo 287828 436367 := bstep (se 1 (by rfl) ⟨327275, by rfl⟩ : syracuseStep 436367 = 654551) B654551
theorem B436409 : Blo 287828 436409 := bstep (se 2 (by rfl) ⟨163653, by rfl⟩ : syracuseStep 436409 = 327307) B327307
theorem B436487 : Blo 287828 436487 := bstep (se 1 (by rfl) ⟨327365, by rfl⟩ : syracuseStep 436487 = 654731) B654731
theorem B436523 : Blo 287828 436523 := bstep (se 1 (by rfl) ⟨327392, by rfl⟩ : syracuseStep 436523 = 654785) B654785
theorem B829739 : Blo 287828 829739 := bstep (se 1 (by rfl) ⟨622304, by rfl⟩ : syracuseStep 829739 = 1244609) B1244609
theorem B436553 : Blo 287828 436553 := bstep (se 2 (by rfl) ⟨163707, by rfl⟩ : syracuseStep 436553 = 327415) B327415
theorem B436667 : Blo 287828 436667 := bstep (se 1 (by rfl) ⟨327500, by rfl⟩ : syracuseStep 436667 = 655001) B655001
theorem B436727 : Blo 287828 436727 := bstep (se 1 (by rfl) ⟨327545, by rfl⟩ : syracuseStep 436727 = 655091) B655091
theorem B731663 : Blo 287828 731663 := bstep (se 1 (by rfl) ⟨548747, by rfl⟩ : syracuseStep 731663 = 1097495) B1097495
theorem B436751 : Blo 287828 436751 := bstep (se 1 (by rfl) ⟨327563, by rfl⟩ : syracuseStep 436751 = 655127) B655127
theorem B1387037 : Blo 287828 1387037 := bstep (se 3 (by rfl) ⟨260069, by rfl⟩ : syracuseStep 1387037 = 520139) B520139
theorem B436793 : Blo 287828 436793 := bstep (se 2 (by rfl) ⟨163797, by rfl⟩ : syracuseStep 436793 = 327595) B327595
theorem B436871 : Blo 287828 436871 := bstep (se 1 (by rfl) ⟨327653, by rfl⟩ : syracuseStep 436871 = 655307) B655307
theorem B436907 : Blo 287828 436907 := bstep (se 1 (by rfl) ⟨327680, by rfl⟩ : syracuseStep 436907 = 655361) B655361
theorem B436937 : Blo 287828 436937 := bstep (se 2 (by rfl) ⟨163851, by rfl⟩ : syracuseStep 436937 = 327703) B327703
theorem B437051 : Blo 287828 437051 := bstep (se 1 (by rfl) ⟨327788, by rfl⟩ : syracuseStep 437051 = 655577) B655577
theorem B437111 : Blo 287828 437111 := bstep (se 1 (by rfl) ⟨327833, by rfl⟩ : syracuseStep 437111 = 655667) B655667
theorem B437135 : Blo 287828 437135 := bstep (se 1 (by rfl) ⟨327851, by rfl⟩ : syracuseStep 437135 = 655703) B655703
theorem B437177 : Blo 287828 437177 := bstep (se 2 (by rfl) ⟨163941, by rfl⟩ : syracuseStep 437177 = 327883) B327883
theorem B437255 : Blo 287828 437255 := bstep (se 1 (by rfl) ⟨327941, by rfl⟩ : syracuseStep 437255 = 655883) B655883
theorem B437291 : Blo 287828 437291 := bstep (se 1 (by rfl) ⟨327968, by rfl⟩ : syracuseStep 437291 = 655937) B655937
theorem B2796605 : Blo 287828 2796605 := bstep (se 3 (by rfl) ⟨524363, by rfl⟩ : syracuseStep 2796605 = 1048727) B1048727
theorem B437321 : Blo 287828 437321 := bstep (se 2 (by rfl) ⟨163995, by rfl⟩ : syracuseStep 437321 = 327991) B327991
theorem B699479 : Blo 287828 699479 := bstep (se 1 (by rfl) ⟨524609, by rfl⟩ : syracuseStep 699479 = 1049219) B1049219
theorem B437435 : Blo 287828 437435 := bstep (se 1 (by rfl) ⟨328076, by rfl⟩ : syracuseStep 437435 = 656153) B656153
theorem B732361 : Blo 287828 732361 := bstep (se 2 (by rfl) ⟨274635, by rfl⟩ : syracuseStep 732361 = 549271) B549271
theorem B437495 : Blo 287828 437495 := bstep (se 1 (by rfl) ⟨328121, by rfl⟩ : syracuseStep 437495 = 656243) B656243
theorem B437519 : Blo 287828 437519 := bstep (se 1 (by rfl) ⟨328139, by rfl⟩ : syracuseStep 437519 = 656279) B656279
theorem B437561 : Blo 287828 437561 := bstep (se 2 (by rfl) ⟨164085, by rfl⟩ : syracuseStep 437561 = 328171) B328171
theorem B1092923 : Blo 287828 1092923 := bstep (se 1 (by rfl) ⟨819692, by rfl⟩ : syracuseStep 1092923 = 1639385) B1639385
theorem B732503 : Blo 287828 732503 := bstep (se 1 (by rfl) ⟨549377, by rfl⟩ : syracuseStep 732503 = 1098755) B1098755
theorem B437639 : Blo 287828 437639 := bstep (se 1 (by rfl) ⟨328229, by rfl⟩ : syracuseStep 437639 = 656459) B656459
theorem B437675 : Blo 287828 437675 := bstep (se 1 (by rfl) ⟨328256, by rfl⟩ : syracuseStep 437675 = 656513) B656513
theorem B1387961 : Blo 287828 1387961 := bstep (se 2 (by rfl) ⟨520485, by rfl⟩ : syracuseStep 1387961 = 1040971) B1040971
theorem B437705 : Blo 287828 437705 := bstep (se 2 (by rfl) ⟨164139, by rfl⟩ : syracuseStep 437705 = 328279) B328279
theorem B2666027 : Blo 287828 2666027 := bstep (se 1 (by rfl) ⟨1999520, by rfl⟩ : syracuseStep 2666027 = 3999041) B3999041
theorem B3124813 : Blo 287828 3124813 := bstep (se 3 (by rfl) ⟨585902, by rfl⟩ : syracuseStep 3124813 = 1171805) B1171805
theorem B1093409 : Blo 287828 1093409 := bstep (se 2 (by rfl) ⟨410028, by rfl⟩ : syracuseStep 1093409 = 820057) B820057
theorem B700247 : Blo 287828 700247 := bstep (se 1 (by rfl) ⟨525185, by rfl⟩ : syracuseStep 700247 = 1050371) B1050371
theorem B1650617 : Blo 287828 1650617 := bstep (se 2 (by rfl) ⟨618981, by rfl⟩ : syracuseStep 1650617 = 1237963) B1237963
theorem B700535 : Blo 287828 700535 := bstep (se 1 (by rfl) ⟨525401, by rfl⟩ : syracuseStep 700535 = 1050803) B1050803
theorem B438443 : Blo 287828 438443 := bstep (se 1 (by rfl) ⟨328832, by rfl⟩ : syracuseStep 438443 = 657665) B657665
theorem B438601 : Blo 287828 438601 := bstep (se 2 (by rfl) ⟨164475, by rfl⟩ : syracuseStep 438601 = 328951) B328951
theorem B3387869 : Blo 287828 3387869 := bstep (se 3 (by rfl) ⟨635225, by rfl⟩ : syracuseStep 3387869 = 1270451) B1270451
theorem B471611 : Blo 287828 471611 := bstep (se 1 (by rfl) ⟨353708, by rfl⟩ : syracuseStep 471611 = 707417) B707417
theorem B1094381 : Blo 287828 1094381 := bstep (se 3 (by rfl) ⟨205196, by rfl⟩ : syracuseStep 1094381 = 410393) B410393
theorem B12530645 : Blo 287828 12530645 := bstep (se 7 (by rfl) ⟨146843, by rfl⟩ : syracuseStep 12530645 = 293687) B293687
theorem B1389635 : Blo 287828 1389635 := bstep (se 1 (by rfl) ⟨1042226, by rfl⟩ : syracuseStep 1389635 = 2084453) B2084453
theorem B734579 : Blo 287828 734579 := bstep (se 1 (by rfl) ⟨550934, by rfl⟩ : syracuseStep 734579 = 1101869) B1101869
theorem B308615 : Blo 287828 308615 := bstep (se 1 (by rfl) ⟨231461, by rfl⟩ : syracuseStep 308615 = 462923) B462923
theorem B1095065 : Blo 287828 1095065 := bstep (se 2 (by rfl) ⟨410649, by rfl⟩ : syracuseStep 1095065 = 821299) B821299
theorem B2635217 : Blo 287828 2635217 := bstep (se 2 (by rfl) ⟨988206, by rfl⟩ : syracuseStep 2635217 = 1976413) B1976413
theorem B4306385 : Blo 287828 4306385 := bstep (se 2 (by rfl) ⟨1614894, by rfl⟩ : syracuseStep 4306385 = 3229789) B3229789
theorem B14137163 : Blo 287828 14137163 := bstep (se 1 (by rfl) ⟨10602872, by rfl⟩ : syracuseStep 14137163 = 21205745) B21205745
theorem B735095 : Blo 287828 735095 := bstep (se 1 (by rfl) ⟨551321, by rfl⟩ : syracuseStep 735095 = 1102643) B1102643
theorem B309307 : Blo 287828 309307 := bstep (se 1 (by rfl) ⟨231980, by rfl⟩ : syracuseStep 309307 = 463961) B463961
theorem B1653007 : Blo 287828 1653007 := bstep (se 1 (by rfl) ⟨1239755, by rfl⟩ : syracuseStep 1653007 = 2479511) B2479511
theorem B473359 : Blo 287828 473359 := bstep (se 1 (by rfl) ⟨355019, by rfl⟩ : syracuseStep 473359 = 710039) B710039
theorem B1718561 : Blo 287828 1718561 := bstep (se 2 (by rfl) ⟨644460, by rfl⟩ : syracuseStep 1718561 = 1288921) B1288921
theorem B1096051 : Blo 287828 1096051 := bstep (se 1 (by rfl) ⟨822038, by rfl⟩ : syracuseStep 1096051 = 1644077) B1644077
theorem B932381 : Blo 287828 932381 := bstep (se 3 (by rfl) ⟨174821, by rfl⟩ : syracuseStep 932381 = 349643) B349643
theorem B2472677 : Blo 287828 2472677 := bstep (se 4 (by rfl) ⟨231813, by rfl⟩ : syracuseStep 2472677 = 463627) B463627
theorem B736087 : Blo 287828 736087 := bstep (se 1 (by rfl) ⟨552065, by rfl⟩ : syracuseStep 736087 = 1104131) B1104131
theorem B1522547 : Blo 287828 1522547 := bstep (se 1 (by rfl) ⟨1141910, by rfl⟩ : syracuseStep 1522547 = 2283821) B2283821
theorem B2177945 : Blo 287828 2177945 := bstep (se 2 (by rfl) ⟨816729, by rfl⟩ : syracuseStep 2177945 = 1633459) B1633459
theorem B736391 : Blo 287828 736391 := bstep (se 1 (by rfl) ⟨552293, by rfl⟩ : syracuseStep 736391 = 1104587) B1104587
theorem B736523 : Blo 287828 736523 := bstep (se 1 (by rfl) ⟨552392, by rfl⟩ : syracuseStep 736523 = 1104785) B1104785
theorem B834875 : Blo 287828 834875 := bstep (se 1 (by rfl) ⟨626156, by rfl⟩ : syracuseStep 834875 = 1252313) B1252313
theorem B2473361 : Blo 287828 2473361 := bstep (se 2 (by rfl) ⟨927510, by rfl⟩ : syracuseStep 2473361 = 1855021) B1855021
theorem B1457675 : Blo 287828 1457675 := bstep (se 1 (by rfl) ⟨1093256, by rfl⟩ : syracuseStep 1457675 = 2186513) B2186513
theorem B1654283 : Blo 287828 1654283 := bstep (se 1 (by rfl) ⟨1240712, by rfl⟩ : syracuseStep 1654283 = 2481425) B2481425
theorem B1457837 : Blo 287828 1457837 := bstep (se 3 (by rfl) ⟨273344, by rfl⟩ : syracuseStep 1457837 = 546689) B546689
theorem B1654465 : Blo 287828 1654465 := bstep (se 2 (by rfl) ⟨620424, by rfl⟩ : syracuseStep 1654465 = 1240849) B1240849
theorem B737039 : Blo 287828 737039 := bstep (se 1 (by rfl) ⟨552779, by rfl⟩ : syracuseStep 737039 = 1105559) B1105559
theorem B3129137 : Blo 287828 3129137 := bstep (se 2 (by rfl) ⟨1173426, by rfl⟩ : syracuseStep 3129137 = 2346853) B2346853
theorem B737171 : Blo 287828 737171 := bstep (se 1 (by rfl) ⟨552878, by rfl⟩ : syracuseStep 737171 = 1105757) B1105757
theorem B2211851 : Blo 287828 2211851 := bstep (se 1 (by rfl) ⟨1658888, by rfl⟩ : syracuseStep 2211851 = 3317777) B3317777
theorem B1392727 : Blo 287828 1392727 := bstep (se 1 (by rfl) ⟨1044545, by rfl⟩ : syracuseStep 1392727 = 2089091) B2089091
theorem B2474387 : Blo 287828 2474387 := bstep (se 1 (by rfl) ⟨1855790, by rfl⟩ : syracuseStep 2474387 = 3711581) B3711581
theorem B1556957 : Blo 287828 1556957 := bstep (se 3 (by rfl) ⟨291929, by rfl⟩ : syracuseStep 1556957 = 583859) B583859
theorem B1098269 : Blo 287828 1098269 := bstep (se 3 (by rfl) ⟨205925, by rfl⟩ : syracuseStep 1098269 = 411851) B411851
theorem B442999 : Blo 287828 442999 := bstep (se 1 (by rfl) ⟨332249, by rfl⟩ : syracuseStep 442999 = 664499) B664499
theorem B1393325 : Blo 287828 1393325 := bstep (se 3 (by rfl) ⟨261248, by rfl⟩ : syracuseStep 1393325 = 522497) B522497
theorem B410359 : Blo 287828 410359 := bstep (se 1 (by rfl) ⟨307769, by rfl⟩ : syracuseStep 410359 = 615539) B615539
theorem B3130265 : Blo 287828 3130265 := bstep (se 2 (by rfl) ⟨1173849, by rfl⟩ : syracuseStep 3130265 = 2347699) B2347699
theorem B934841 : Blo 287828 934841 := bstep (se 2 (by rfl) ⟨350565, by rfl⟩ : syracuseStep 934841 = 701131) B701131
theorem B738305 : Blo 287828 738305 := bstep (se 2 (by rfl) ⟨276864, by rfl⟩ : syracuseStep 738305 = 553729) B553729
theorem B1098953 : Blo 287828 1098953 := bstep (se 2 (by rfl) ⟨412107, by rfl⟩ : syracuseStep 1098953 = 824215) B824215
theorem B1459457 : Blo 287828 1459457 := bstep (se 2 (by rfl) ⟨547296, by rfl⟩ : syracuseStep 1459457 = 1094593) B1094593
theorem B410923 : Blo 287828 410923 := bstep (se 1 (by rfl) ⟨308192, by rfl⟩ : syracuseStep 410923 = 616385) B616385
theorem B738679 : Blo 287828 738679 := bstep (se 1 (by rfl) ⟨554009, by rfl⟩ : syracuseStep 738679 = 1108019) B1108019
theorem B411151 : Blo 287828 411151 := bstep (se 1 (by rfl) ⟨308363, by rfl⟩ : syracuseStep 411151 = 616727) B616727
theorem B3884645 : Blo 287828 3884645 := bstep (se 4 (by rfl) ⟨364185, by rfl⟩ : syracuseStep 3884645 = 728371) B728371
theorem B345871 : Blo 287828 345871 := bstep (se 1 (by rfl) ⟨259403, by rfl⟩ : syracuseStep 345871 = 518807) B518807
theorem B1460267 : Blo 287828 1460267 := bstep (se 1 (by rfl) ⟨1095200, by rfl⟩ : syracuseStep 1460267 = 2190401) B2190401
theorem B412295 : Blo 287828 412295 := bstep (se 1 (by rfl) ⟨309221, by rfl⟩ : syracuseStep 412295 = 618443) B618443
theorem B412489 : Blo 287828 412489 := bstep (se 2 (by rfl) ⟨154683, by rfl⟩ : syracuseStep 412489 = 309367) B309367
theorem B1100729 : Blo 287828 1100729 := bstep (se 2 (by rfl) ⟨412773, by rfl⟩ : syracuseStep 1100729 = 825547) B825547
theorem B1461563 : Blo 287828 1461563 := bstep (se 1 (by rfl) ⟨1096172, by rfl⟩ : syracuseStep 1461563 = 2192345) B2192345
theorem B413047 : Blo 287828 413047 := bstep (se 1 (by rfl) ⟨309785, by rfl⟩ : syracuseStep 413047 = 619571) B619571
theorem B1461725 : Blo 287828 1461725 := bstep (se 3 (by rfl) ⟨274073, by rfl⟩ : syracuseStep 1461725 = 548147) B548147
theorem B347663 : Blo 287828 347663 := bstep (se 1 (by rfl) ⟨260747, by rfl⟩ : syracuseStep 347663 = 521495) B521495
theorem B1462049 : Blo 287828 1462049 := bstep (se 2 (by rfl) ⟨548268, by rfl⟩ : syracuseStep 1462049 = 1096537) B1096537
theorem B1658657 : Blo 287828 1658657 := bstep (se 2 (by rfl) ⟨621996, by rfl⟩ : syracuseStep 1658657 = 1243993) B1243993
theorem B17813525 : Blo 287828 17813525 := bstep (se 6 (by rfl) ⟨417504, by rfl⟩ : syracuseStep 17813525 = 835009) B835009
theorem B3330071 : Blo 287828 3330071 := bstep (se 1 (by rfl) ⟨2497553, by rfl⟩ : syracuseStep 3330071 = 4995107) B4995107
theorem B413753 : Blo 287828 413753 := bstep (se 2 (by rfl) ⟨155157, by rfl⟩ : syracuseStep 413753 = 310315) B310315
theorem B413839 : Blo 287828 413839 := bstep (se 1 (by rfl) ⟨310379, by rfl⟩ : syracuseStep 413839 = 620759) B620759
theorem B413867 : Blo 287828 413867 := bstep (se 1 (by rfl) ⟨310400, by rfl⟩ : syracuseStep 413867 = 620801) B620801
theorem B1463021 : Blo 287828 1463021 := bstep (se 3 (by rfl) ⟨274316, by rfl⟩ : syracuseStep 1463021 = 548633) B548633
theorem B971837 : Blo 287828 971837 := bstep (se 3 (by rfl) ⟨182219, by rfl⟩ : syracuseStep 971837 = 364439) B364439
theorem B1561801 : Blo 287828 1561801 := bstep (se 2 (by rfl) ⟨585675, by rfl⟩ : syracuseStep 1561801 = 1171351) B1171351
theorem B677179 : Blo 287828 677179 := bstep (se 1 (by rfl) ⟨507884, by rfl⟩ : syracuseStep 677179 = 1015769) B1015769
theorem B1463831 : Blo 287828 1463831 := bstep (se 1 (by rfl) ⟨1097873, by rfl⟩ : syracuseStep 1463831 = 2195747) B2195747
theorem B3135019 : Blo 287828 3135019 := bstep (se 1 (by rfl) ⟨2351264, by rfl⟩ : syracuseStep 3135019 = 4702529) B4702529
theorem B546439 : Blo 287828 546439 := bstep (se 1 (by rfl) ⟨409829, by rfl⟩ : syracuseStep 546439 = 819659) B819659
theorem B6674177 : Blo 287828 6674177 := bstep (se 2 (by rfl) ⟨2502816, by rfl⟩ : syracuseStep 6674177 = 5005633) B5005633
theorem B1234835 : Blo 287828 1234835 := bstep (se 1 (by rfl) ⟨926126, by rfl⟩ : syracuseStep 1234835 = 1852253) B1852253
theorem B1038233 : Blo 287828 1038233 := bstep (se 2 (by rfl) ⟨389337, by rfl⟩ : syracuseStep 1038233 = 778675) B778675
theorem B415751 : Blo 287828 415751 := bstep (se 1 (by rfl) ⟨311813, by rfl⟩ : syracuseStep 415751 = 623627) B623627
theorem B1038347 : Blo 287828 1038347 := bstep (se 1 (by rfl) ⟨778760, by rfl⟩ : syracuseStep 1038347 = 1557521) B1557521
theorem B973241 : Blo 287828 973241 := bstep (se 2 (by rfl) ⟨364965, by rfl⟩ : syracuseStep 973241 = 729931) B729931
theorem B1104313 : Blo 287828 1104313 := bstep (se 2 (by rfl) ⟨414117, by rfl⟩ : syracuseStep 1104313 = 828235) B828235
theorem B1661755 : Blo 287828 1661755 := bstep (se 1 (by rfl) ⟨1246316, by rfl⟩ : syracuseStep 1661755 = 2492633) B2492633
theorem B3562393 : Blo 287828 3562393 := bstep (se 2 (by rfl) ⟨1335897, by rfl⟩ : syracuseStep 3562393 = 2671795) B2671795
theorem B973835 : Blo 287828 973835 := bstep (se 1 (by rfl) ⟨730376, by rfl⟩ : syracuseStep 973835 = 1460753) B1460753
theorem B973943 : Blo 287828 973943 := bstep (se 1 (by rfl) ⟨730457, by rfl⟩ : syracuseStep 973943 = 1460915) B1460915
theorem B548041 : Blo 287828 548041 := bstep (se 2 (by rfl) ⟨205515, by rfl⟩ : syracuseStep 548041 = 411031) B411031
theorem B941465 : Blo 287828 941465 := bstep (se 2 (by rfl) ⟨353049, by rfl⟩ : syracuseStep 941465 = 706099) B706099
theorem B5693003 : Blo 287828 5693003 := bstep (se 1 (by rfl) ⟨4269752, by rfl⟩ : syracuseStep 5693003 = 8539505) B8539505
theorem B876179 : Blo 287828 876179 := bstep (se 1 (by rfl) ⟨657134, by rfl⟩ : syracuseStep 876179 = 1314269) B1314269
theorem B974537 : Blo 287828 974537 := bstep (se 2 (by rfl) ⟨365451, by rfl⟩ : syracuseStep 974537 = 730903) B730903
theorem B1400723 : Blo 287828 1400723 := bstep (se 1 (by rfl) ⟨1050542, by rfl⟩ : syracuseStep 1400723 = 2101085) B2101085
theorem B2384005 : Blo 287828 2384005 := bstep (se 4 (by rfl) ⟨223500, by rfl⟩ : syracuseStep 2384005 = 447001) B447001
theorem B778555 : Blo 287828 778555 := bstep (se 1 (by rfl) ⟨583916, by rfl⟩ : syracuseStep 778555 = 1167833) B1167833
theorem B975239 : Blo 287828 975239 := bstep (se 1 (by rfl) ⟨731429, by rfl⟩ : syracuseStep 975239 = 1462859) B1462859
theorem B1466909 : Blo 287828 1466909 := bstep (se 3 (by rfl) ⟨275045, by rfl⟩ : syracuseStep 1466909 = 550091) B550091
theorem B975617 : Blo 287828 975617 := bstep (se 2 (by rfl) ⟨365856, by rfl⟩ : syracuseStep 975617 = 731713) B731713
theorem B1860353 : Blo 287828 1860353 := bstep (se 2 (by rfl) ⟨697632, by rfl⟩ : syracuseStep 1860353 = 1395265) B1395265
theorem B648071 : Blo 287828 648071 := bstep (se 1 (by rfl) ⟨486053, by rfl⟩ : syracuseStep 648071 = 972107) B972107
theorem B1467395 : Blo 287828 1467395 := bstep (se 1 (by rfl) ⟨1100546, by rfl⟩ : syracuseStep 1467395 = 2201093) B2201093
theorem B1664023 : Blo 287828 1664023 := bstep (se 1 (by rfl) ⟨1248017, by rfl⟩ : syracuseStep 1664023 = 2496035) B2496035
theorem B648251 : Blo 287828 648251 := bstep (se 1 (by rfl) ⟨486188, by rfl⟩ : syracuseStep 648251 = 972377) B972377
theorem B287879 : Blo 287828 287879 := bstep (se 1 (by rfl) ⟨215909, by rfl⟩ : syracuseStep 287879 = 431819) B431819
theorem B287887 : Blo 287828 287887 := bstep (se 1 (by rfl) ⟨215915, by rfl⟩ : syracuseStep 287887 = 431831) B431831
theorem B648377 : Blo 287828 648377 := bstep (se 2 (by rfl) ⟨243141, by rfl⟩ : syracuseStep 648377 = 486283) B486283
theorem B287931 : Blo 287828 287931 := bstep (se 1 (by rfl) ⟨215948, by rfl⟩ : syracuseStep 287931 = 431897) B431897
theorem B32531717 : Blo 287828 32531717 := bstep (se 4 (by rfl) ⟨3049848, by rfl⟩ : syracuseStep 32531717 = 6099697) B6099697
theorem B288007 : Blo 287828 288007 := bstep (se 1 (by rfl) ⟨216005, by rfl⟩ : syracuseStep 288007 = 432011) B432011
theorem B288015 : Blo 287828 288015 := bstep (se 1 (by rfl) ⟨216011, by rfl⟩ : syracuseStep 288015 = 432023) B432023
theorem B1238287 : Blo 287828 1238287 := bstep (se 1 (by rfl) ⟨928715, by rfl⟩ : syracuseStep 1238287 = 1857431) B1857431
theorem B1107215 : Blo 287828 1107215 := bstep (se 1 (by rfl) ⟨830411, by rfl⟩ : syracuseStep 1107215 = 1660823) B1660823
theorem B288059 : Blo 287828 288059 := bstep (se 1 (by rfl) ⟨216044, by rfl⟩ : syracuseStep 288059 = 432089) B432089
theorem B3728699 : Blo 287828 3728699 := bstep (se 1 (by rfl) ⟨2796524, by rfl⟩ : syracuseStep 3728699 = 5593049) B5593049
theorem B2778461 : Blo 287828 2778461 := bstep (se 3 (by rfl) ⟨520961, by rfl⟩ : syracuseStep 2778461 = 1041923) B1041923
theorem B288135 : Blo 287828 288135 := bstep (se 1 (by rfl) ⟨216101, by rfl⟩ : syracuseStep 288135 = 432203) B432203
theorem B288143 : Blo 287828 288143 := bstep (se 1 (by rfl) ⟨216107, by rfl⟩ : syracuseStep 288143 = 432215) B432215
theorem B288187 : Blo 287828 288187 := bstep (se 1 (by rfl) ⟨216140, by rfl⟩ : syracuseStep 288187 = 432281) B432281
theorem B288263 : Blo 287828 288263 := bstep (se 1 (by rfl) ⟨216197, by rfl⟩ : syracuseStep 288263 = 432395) B432395
theorem B288271 : Blo 287828 288271 := bstep (se 1 (by rfl) ⟨216203, by rfl⟩ : syracuseStep 288271 = 432407) B432407
theorem B648719 : Blo 287828 648719 := bstep (se 1 (by rfl) ⟨486539, by rfl⟩ : syracuseStep 648719 = 973079) B973079
theorem B648737 : Blo 287828 648737 := bstep (se 2 (by rfl) ⟨243276, by rfl⟩ : syracuseStep 648737 = 486553) B486553
theorem B976427 : Blo 287828 976427 := bstep (se 1 (by rfl) ⟨732320, by rfl⟩ : syracuseStep 976427 = 1464641) B1464641
theorem B288315 : Blo 287828 288315 := bstep (se 1 (by rfl) ⟨216236, by rfl⟩ : syracuseStep 288315 = 432473) B432473
theorem B288391 : Blo 287828 288391 := bstep (se 1 (by rfl) ⟨216293, by rfl⟩ : syracuseStep 288391 = 432587) B432587
theorem B288399 : Blo 287828 288399 := bstep (se 1 (by rfl) ⟨216299, by rfl⟩ : syracuseStep 288399 = 432599) B432599
theorem B550547 : Blo 287828 550547 := bstep (se 1 (by rfl) ⟨412910, by rfl⟩ : syracuseStep 550547 = 825821) B825821
theorem B288443 : Blo 287828 288443 := bstep (se 1 (by rfl) ⟨216332, by rfl⟩ : syracuseStep 288443 = 432665) B432665
theorem B288519 : Blo 287828 288519 := bstep (se 1 (by rfl) ⟨216389, by rfl⟩ : syracuseStep 288519 = 432779) B432779
theorem B288527 : Blo 287828 288527 := bstep (se 1 (by rfl) ⟨216395, by rfl⟩ : syracuseStep 288527 = 432791) B432791
theorem B288571 : Blo 287828 288571 := bstep (se 1 (by rfl) ⟨216428, by rfl⟩ : syracuseStep 288571 = 432857) B432857
theorem B747323 : Blo 287828 747323 := bstep (se 1 (by rfl) ⟨560492, by rfl⟩ : syracuseStep 747323 = 1120985) B1120985
theorem B649079 : Blo 287828 649079 := bstep (se 1 (by rfl) ⟨486809, by rfl⟩ : syracuseStep 649079 = 973619) B973619
theorem B550775 : Blo 287828 550775 := bstep (se 1 (by rfl) ⟨413081, by rfl⟩ : syracuseStep 550775 = 826163) B826163
theorem B780167 : Blo 287828 780167 := bstep (se 1 (by rfl) ⟨585125, by rfl⟩ : syracuseStep 780167 = 1170251) B1170251
theorem B288647 : Blo 287828 288647 := bstep (se 1 (by rfl) ⟨216485, by rfl⟩ : syracuseStep 288647 = 432971) B432971
theorem B288655 : Blo 287828 288655 := bstep (se 1 (by rfl) ⟨216491, by rfl⟩ : syracuseStep 288655 = 432983) B432983
theorem B288699 : Blo 287828 288699 := bstep (se 1 (by rfl) ⟨216524, by rfl⟩ : syracuseStep 288699 = 433049) B433049
theorem B288775 : Blo 287828 288775 := bstep (se 1 (by rfl) ⟨216581, by rfl⟩ : syracuseStep 288775 = 433163) B433163
theorem B288783 : Blo 287828 288783 := bstep (se 1 (by rfl) ⟨216587, by rfl⟩ : syracuseStep 288783 = 433175) B433175
theorem B649259 : Blo 287828 649259 := bstep (se 1 (by rfl) ⟨486944, by rfl⟩ : syracuseStep 649259 = 973889) B973889
theorem B288827 : Blo 287828 288827 := bstep (se 1 (by rfl) ⟨216620, by rfl⟩ : syracuseStep 288827 = 433241) B433241
theorem B288903 : Blo 287828 288903 := bstep (se 1 (by rfl) ⟨216677, by rfl⟩ : syracuseStep 288903 = 433355) B433355
theorem B288911 : Blo 287828 288911 := bstep (se 1 (by rfl) ⟨216683, by rfl⟩ : syracuseStep 288911 = 433367) B433367
theorem B288955 : Blo 287828 288955 := bstep (se 1 (by rfl) ⟨216716, by rfl⟩ : syracuseStep 288955 = 433433) B433433
theorem B289031 : Blo 287828 289031 := bstep (se 1 (by rfl) ⟨216773, by rfl⟩ : syracuseStep 289031 = 433547) B433547
theorem B289039 : Blo 287828 289039 := bstep (se 1 (by rfl) ⟨216779, by rfl⟩ : syracuseStep 289039 = 433559) B433559
theorem B289083 : Blo 287828 289083 := bstep (se 1 (by rfl) ⟨216812, by rfl⟩ : syracuseStep 289083 = 433625) B433625
theorem B289159 : Blo 287828 289159 := bstep (se 1 (by rfl) ⟨216869, by rfl⟩ : syracuseStep 289159 = 433739) B433739
theorem B289167 : Blo 287828 289167 := bstep (se 1 (by rfl) ⟨216875, by rfl⟩ : syracuseStep 289167 = 433751) B433751
theorem B4712849 : Blo 287828 4712849 := bstep (se 2 (by rfl) ⟨1767318, by rfl⟩ : syracuseStep 4712849 = 3534637) B3534637
theorem B649619 : Blo 287828 649619 := bstep (se 1 (by rfl) ⟨487214, by rfl⟩ : syracuseStep 649619 = 974429) B974429
theorem B3303827 : Blo 287828 3303827 := bstep (se 1 (by rfl) ⟨2477870, by rfl⟩ : syracuseStep 3303827 = 4955741) B4955741
theorem B616889 : Blo 287828 616889 := bstep (se 2 (by rfl) ⟨231333, by rfl⟩ : syracuseStep 616889 = 462667) B462667
theorem B289211 : Blo 287828 289211 := bstep (se 1 (by rfl) ⟨216908, by rfl⟩ : syracuseStep 289211 = 433817) B433817
theorem B649673 : Blo 287828 649673 := bstep (se 2 (by rfl) ⟨243627, by rfl⟩ : syracuseStep 649673 = 487255) B487255
theorem B289287 : Blo 287828 289287 := bstep (se 1 (by rfl) ⟨216965, by rfl⟩ : syracuseStep 289287 = 433931) B433931
theorem B289295 : Blo 287828 289295 := bstep (se 1 (by rfl) ⟨216971, by rfl⟩ : syracuseStep 289295 = 433943) B433943
theorem B289339 : Blo 287828 289339 := bstep (se 1 (by rfl) ⟨217004, by rfl⟩ : syracuseStep 289339 = 434009) B434009
theorem B1239619 : Blo 287828 1239619 := bstep (se 1 (by rfl) ⟨929714, by rfl⟩ : syracuseStep 1239619 = 1859429) B1859429
theorem B1469015 : Blo 287828 1469015 := bstep (se 1 (by rfl) ⟨1101761, by rfl⟩ : syracuseStep 1469015 = 2203523) B2203523
theorem B289415 : Blo 287828 289415 := bstep (se 1 (by rfl) ⟨217061, by rfl⟩ : syracuseStep 289415 = 434123) B434123
theorem B289423 : Blo 287828 289423 := bstep (se 1 (by rfl) ⟨217067, by rfl⟩ : syracuseStep 289423 = 434135) B434135
theorem B1764013 : Blo 287828 1764013 := bstep (se 3 (by rfl) ⟨330752, by rfl⟩ : syracuseStep 1764013 = 661505) B661505
theorem B289467 : Blo 287828 289467 := bstep (se 1 (by rfl) ⟨217100, by rfl⟩ : syracuseStep 289467 = 434201) B434201
theorem B289543 : Blo 287828 289543 := bstep (se 1 (by rfl) ⟨217157, by rfl⟩ : syracuseStep 289543 = 434315) B434315
theorem B2779919 : Blo 287828 2779919 := bstep (se 1 (by rfl) ⟨2084939, by rfl⟩ : syracuseStep 2779919 = 4169879) B4169879
theorem B289551 : Blo 287828 289551 := bstep (se 1 (by rfl) ⟨217163, by rfl⟩ : syracuseStep 289551 = 434327) B434327
theorem B59894549 : Blo 287828 59894549 := bstep (se 6 (by rfl) ⟨1403778, by rfl⟩ : syracuseStep 59894549 = 2807557) B2807557
theorem B748331 : Blo 287828 748331 := bstep (se 1 (by rfl) ⟨561248, by rfl⟩ : syracuseStep 748331 = 1122497) B1122497
theorem B289595 : Blo 287828 289595 := bstep (se 1 (by rfl) ⟨217196, by rfl⟩ : syracuseStep 289595 = 434393) B434393
theorem B977723 : Blo 287828 977723 := bstep (se 1 (by rfl) ⟨733292, by rfl⟩ : syracuseStep 977723 = 1466585) B1466585
theorem B486263 : Blo 287828 486263 := bstep (se 1 (by rfl) ⟨364697, by rfl⟩ : syracuseStep 486263 = 729395) B729395
theorem B584567 : Blo 287828 584567 := bstep (se 1 (by rfl) ⟨438425, by rfl⟩ : syracuseStep 584567 = 876851) B876851
theorem B289671 : Blo 287828 289671 := bstep (se 1 (by rfl) ⟨217253, by rfl⟩ : syracuseStep 289671 = 434507) B434507
theorem B289679 : Blo 287828 289679 := bstep (se 1 (by rfl) ⟨217259, by rfl⟩ : syracuseStep 289679 = 434519) B434519
theorem B1239961 : Blo 287828 1239961 := bstep (se 2 (by rfl) ⟨464985, by rfl⟩ : syracuseStep 1239961 = 929971) B929971
theorem B289723 : Blo 287828 289723 := bstep (se 1 (by rfl) ⟨217292, by rfl⟩ : syracuseStep 289723 = 434585) B434585
theorem B9956357 : Blo 287828 9956357 := bstep (se 4 (by rfl) ⟨933408, by rfl⟩ : syracuseStep 9956357 = 1866817) B1866817
theorem B289799 : Blo 287828 289799 := bstep (se 1 (by rfl) ⟨217349, by rfl⟩ : syracuseStep 289799 = 434699) B434699
theorem B289807 : Blo 287828 289807 := bstep (se 1 (by rfl) ⟨217355, by rfl⟩ : syracuseStep 289807 = 434711) B434711
theorem B289851 : Blo 287828 289851 := bstep (se 1 (by rfl) ⟨217388, by rfl⟩ : syracuseStep 289851 = 434777) B434777
theorem B1469501 : Blo 287828 1469501 := bstep (se 3 (by rfl) ⟨275531, by rfl⟩ : syracuseStep 1469501 = 551063) B551063
theorem B650375 : Blo 287828 650375 := bstep (se 1 (by rfl) ⟨487781, by rfl⟩ : syracuseStep 650375 = 975563) B975563
theorem B289927 : Blo 287828 289927 := bstep (se 1 (by rfl) ⟨217445, by rfl⟩ : syracuseStep 289927 = 434891) B434891
theorem B289935 : Blo 287828 289935 := bstep (se 1 (by rfl) ⟨217451, by rfl⟩ : syracuseStep 289935 = 434903) B434903
theorem B289979 : Blo 287828 289979 := bstep (se 1 (by rfl) ⟨217484, by rfl⟩ : syracuseStep 289979 = 434969) B434969
theorem B290055 : Blo 287828 290055 := bstep (se 1 (by rfl) ⟨217541, by rfl⟩ : syracuseStep 290055 = 435083) B435083
theorem B290063 : Blo 287828 290063 := bstep (se 1 (by rfl) ⟨217547, by rfl⟩ : syracuseStep 290063 = 435095) B435095
theorem B978209 : Blo 287828 978209 := bstep (se 2 (by rfl) ⟨366828, by rfl⟩ : syracuseStep 978209 = 733657) B733657
theorem B486715 : Blo 287828 486715 := bstep (se 1 (by rfl) ⟨365036, by rfl⟩ : syracuseStep 486715 = 730073) B730073
theorem B650555 : Blo 287828 650555 := bstep (se 1 (by rfl) ⟨487916, by rfl⟩ : syracuseStep 650555 = 975833) B975833
theorem B290107 : Blo 287828 290107 := bstep (se 1 (by rfl) ⟨217580, by rfl⟩ : syracuseStep 290107 = 435161) B435161
theorem B290183 : Blo 287828 290183 := bstep (se 1 (by rfl) ⟨217637, by rfl⟩ : syracuseStep 290183 = 435275) B435275
theorem B290191 : Blo 287828 290191 := bstep (se 1 (by rfl) ⟨217643, by rfl⟩ : syracuseStep 290191 = 435287) B435287
theorem B650681 : Blo 287828 650681 := bstep (se 2 (by rfl) ⟨244005, by rfl⟩ : syracuseStep 650681 = 488011) B488011
theorem B290235 : Blo 287828 290235 := bstep (se 1 (by rfl) ⟨217676, by rfl⟩ : syracuseStep 290235 = 435353) B435353
theorem B486857 : Blo 287828 486857 := bstep (se 2 (by rfl) ⟨182571, by rfl⟩ : syracuseStep 486857 = 365143) B365143
theorem B290311 : Blo 287828 290311 := bstep (se 1 (by rfl) ⟨217733, by rfl⟩ : syracuseStep 290311 = 435467) B435467
theorem B290319 : Blo 287828 290319 := bstep (se 1 (by rfl) ⟨217739, by rfl⟩ : syracuseStep 290319 = 435479) B435479
theorem B552491 : Blo 287828 552491 := bstep (se 1 (by rfl) ⟨414368, by rfl⟩ : syracuseStep 552491 = 828737) B828737
theorem B290363 : Blo 287828 290363 := bstep (se 1 (by rfl) ⟨217772, by rfl⟩ : syracuseStep 290363 = 435545) B435545
theorem B290439 : Blo 287828 290439 := bstep (se 1 (by rfl) ⟨217829, by rfl⟩ : syracuseStep 290439 = 435659) B435659
theorem B290447 : Blo 287828 290447 := bstep (se 1 (by rfl) ⟨217835, by rfl⟩ : syracuseStep 290447 = 435671) B435671
theorem B290491 : Blo 287828 290491 := bstep (se 1 (by rfl) ⟨217868, by rfl⟩ : syracuseStep 290491 = 435737) B435737
theorem B290567 : Blo 287828 290567 := bstep (se 1 (by rfl) ⟨217925, by rfl⟩ : syracuseStep 290567 = 435851) B435851
theorem B651023 : Blo 287828 651023 := bstep (se 1 (by rfl) ⟨488267, by rfl⟩ : syracuseStep 651023 = 976535) B976535
theorem B290575 : Blo 287828 290575 := bstep (se 1 (by rfl) ⟨217931, by rfl⟩ : syracuseStep 290575 = 435863) B435863
theorem B552719 : Blo 287828 552719 := bstep (se 1 (by rfl) ⟨414539, by rfl⟩ : syracuseStep 552719 = 829079) B829079
theorem B945935 : Blo 287828 945935 := bstep (se 1 (by rfl) ⟨709451, by rfl⟩ : syracuseStep 945935 = 1418903) B1418903
theorem B651041 : Blo 287828 651041 := bstep (se 2 (by rfl) ⟨244140, by rfl⟩ : syracuseStep 651041 = 488281) B488281
theorem B290619 : Blo 287828 290619 := bstep (se 1 (by rfl) ⟨217964, by rfl⟩ : syracuseStep 290619 = 435929) B435929
theorem B978803 : Blo 287828 978803 := bstep (se 1 (by rfl) ⟨734102, by rfl⟩ : syracuseStep 978803 = 1468205) B1468205
theorem B290695 : Blo 287828 290695 := bstep (se 1 (by rfl) ⟨218021, by rfl⟩ : syracuseStep 290695 = 436043) B436043
theorem B290703 : Blo 287828 290703 := bstep (se 1 (by rfl) ⟨218027, by rfl⟩ : syracuseStep 290703 = 436055) B436055
theorem B290747 : Blo 287828 290747 := bstep (se 1 (by rfl) ⟨218060, by rfl⟩ : syracuseStep 290747 = 436121) B436121
theorem B290823 : Blo 287828 290823 := bstep (se 1 (by rfl) ⟨218117, by rfl⟩ : syracuseStep 290823 = 436235) B436235
theorem B618511 : Blo 287828 618511 := bstep (se 1 (by rfl) ⟨463883, by rfl⟩ : syracuseStep 618511 = 927767) B927767
theorem B290831 : Blo 287828 290831 := bstep (se 1 (by rfl) ⟨218123, by rfl⟩ : syracuseStep 290831 = 436247) B436247
theorem B618529 : Blo 287828 618529 := bstep (se 2 (by rfl) ⟨231948, by rfl⟩ : syracuseStep 618529 = 463897) B463897
theorem B5304365 : Blo 287828 5304365 := bstep (se 3 (by rfl) ⟨994568, by rfl⟩ : syracuseStep 5304365 = 1989137) B1989137
theorem B290875 : Blo 287828 290875 := bstep (se 1 (by rfl) ⟨218156, by rfl⟩ : syracuseStep 290875 = 436313) B436313
theorem B651383 : Blo 287828 651383 := bstep (se 1 (by rfl) ⟨488537, by rfl⟩ : syracuseStep 651383 = 977075) B977075
theorem B487559 : Blo 287828 487559 := bstep (se 1 (by rfl) ⟨365669, by rfl⟩ : syracuseStep 487559 = 731339) B731339
theorem B290951 : Blo 287828 290951 := bstep (se 1 (by rfl) ⟨218213, by rfl⟩ : syracuseStep 290951 = 436427) B436427
theorem B290959 : Blo 287828 290959 := bstep (se 1 (by rfl) ⟨218219, by rfl⟩ : syracuseStep 290959 = 436439) B436439
theorem B291003 : Blo 287828 291003 := bstep (se 1 (by rfl) ⟨218252, by rfl⟩ : syracuseStep 291003 = 436505) B436505
theorem B585929 : Blo 287828 585929 := bstep (se 2 (by rfl) ⟨219723, by rfl⟩ : syracuseStep 585929 = 439447) B439447
theorem B1863917 : Blo 287828 1863917 := bstep (se 3 (by rfl) ⟨349484, by rfl⟩ : syracuseStep 1863917 = 698969) B698969
theorem B291079 : Blo 287828 291079 := bstep (se 1 (by rfl) ⟨218309, by rfl⟩ : syracuseStep 291079 = 436619) B436619
theorem B291087 : Blo 287828 291087 := bstep (se 1 (by rfl) ⟨218315, by rfl⟩ : syracuseStep 291087 = 436631) B436631
theorem B651563 : Blo 287828 651563 := bstep (se 1 (by rfl) ⟨488672, by rfl⟩ : syracuseStep 651563 = 977345) B977345
theorem B291131 : Blo 287828 291131 := bstep (se 1 (by rfl) ⟨218348, by rfl⟩ : syracuseStep 291131 = 436697) B436697
theorem B782707 : Blo 287828 782707 := bstep (se 1 (by rfl) ⟨587030, by rfl⟩ : syracuseStep 782707 = 1174061) B1174061
theorem B618887 : Blo 287828 618887 := bstep (se 1 (by rfl) ⟨464165, by rfl⟩ : syracuseStep 618887 = 928331) B928331
theorem B291207 : Blo 287828 291207 := bstep (se 1 (by rfl) ⟨218405, by rfl⟩ : syracuseStep 291207 = 436811) B436811
theorem B291215 : Blo 287828 291215 := bstep (se 1 (by rfl) ⟨218411, by rfl⟩ : syracuseStep 291215 = 436823) B436823
theorem B291259 : Blo 287828 291259 := bstep (se 1 (by rfl) ⟨218444, by rfl⟩ : syracuseStep 291259 = 436889) B436889
theorem B324103 : Blo 287828 324103 := bstep (se 1 (by rfl) ⟨243077, by rfl⟩ : syracuseStep 324103 = 486155) B486155
theorem B291335 : Blo 287828 291335 := bstep (se 1 (by rfl) ⟨218501, by rfl⟩ : syracuseStep 291335 = 437003) B437003
theorem B291343 : Blo 287828 291343 := bstep (se 1 (by rfl) ⟨218507, by rfl⟩ : syracuseStep 291343 = 437015) B437015
theorem B291387 : Blo 287828 291387 := bstep (se 1 (by rfl) ⟨218540, by rfl⟩ : syracuseStep 291387 = 437081) B437081
theorem B2486861 : Blo 287828 2486861 := bstep (se 3 (by rfl) ⟨466286, by rfl⟩ : syracuseStep 2486861 = 932573) B932573
theorem B291463 : Blo 287828 291463 := bstep (se 1 (by rfl) ⟨218597, by rfl⟩ : syracuseStep 291463 = 437195) B437195
theorem B291471 : Blo 287828 291471 := bstep (se 1 (by rfl) ⟨218603, by rfl⟩ : syracuseStep 291471 = 437207) B437207
theorem B651923 : Blo 287828 651923 := bstep (se 1 (by rfl) ⟨488942, by rfl⟩ : syracuseStep 651923 = 977885) B977885
theorem B324283 : Blo 287828 324283 := bstep (se 1 (by rfl) ⟨243212, by rfl⟩ : syracuseStep 324283 = 486425) B486425
theorem B291515 : Blo 287828 291515 := bstep (se 1 (by rfl) ⟨218636, by rfl⟩ : syracuseStep 291515 = 437273) B437273
theorem B651977 : Blo 287828 651977 := bstep (se 2 (by rfl) ⟨244491, by rfl⟩ : syracuseStep 651977 = 488983) B488983
theorem B291591 : Blo 287828 291591 := bstep (se 1 (by rfl) ⟨218693, by rfl⟩ : syracuseStep 291591 = 437387) B437387
theorem B488207 : Blo 287828 488207 := bstep (se 1 (by rfl) ⟨366155, by rfl⟩ : syracuseStep 488207 = 732311) B732311
theorem B291599 : Blo 287828 291599 := bstep (se 1 (by rfl) ⟨218699, by rfl⟩ : syracuseStep 291599 = 437399) B437399
theorem B1471283 : Blo 287828 1471283 := bstep (se 1 (by rfl) ⟨1103462, by rfl⟩ : syracuseStep 1471283 = 2206925) B2206925
theorem B291643 : Blo 287828 291643 := bstep (se 1 (by rfl) ⟨218732, by rfl⟩ : syracuseStep 291643 = 437465) B437465
theorem B291719 : Blo 287828 291719 := bstep (se 1 (by rfl) ⟨218789, by rfl⟩ : syracuseStep 291719 = 437579) B437579
theorem B291727 : Blo 287828 291727 := bstep (se 1 (by rfl) ⟨218795, by rfl⟩ : syracuseStep 291727 = 437591) B437591
theorem B291771 : Blo 287828 291771 := bstep (se 1 (by rfl) ⟨218828, by rfl⟩ : syracuseStep 291771 = 437657) B437657
theorem B1471607 : Blo 287828 1471607 := bstep (se 1 (by rfl) ⟨1103705, by rfl⟩ : syracuseStep 1471607 = 2207411) B2207411
theorem B324751 : Blo 287828 324751 := bstep (se 1 (by rfl) ⟨243563, by rfl⟩ : syracuseStep 324751 = 487127) B487127
theorem B51573941 : Blo 287828 51573941 := bstep (se 5 (by rfl) ⟨2417528, by rfl⟩ : syracuseStep 51573941 = 4835057) B4835057
theorem B2094281 : Blo 287828 2094281 := bstep (se 2 (by rfl) ⟨785355, by rfl⟩ : syracuseStep 2094281 = 1570711) B1570711
theorem B488747 : Blo 287828 488747 := bstep (se 1 (by rfl) ⟨366560, by rfl⟩ : syracuseStep 488747 = 733121) B733121
theorem B652679 : Blo 287828 652679 := bstep (se 1 (by rfl) ⟨489509, by rfl⟩ : syracuseStep 652679 = 979019) B979019
theorem B620075 : Blo 287828 620075 := bstep (se 1 (by rfl) ⟨465056, by rfl⟩ : syracuseStep 620075 = 930113) B930113
theorem B652859 : Blo 287828 652859 := bstep (se 1 (by rfl) ⟨489644, by rfl⟩ : syracuseStep 652859 = 979289) B979289
theorem B325255 : Blo 287828 325255 := bstep (se 1 (by rfl) ⟨243941, by rfl⟩ : syracuseStep 325255 = 487883) B487883
theorem B489145 : Blo 287828 489145 := bstep (se 2 (by rfl) ⟨183429, by rfl⟩ : syracuseStep 489145 = 366859) B366859
theorem B652985 : Blo 287828 652985 := bstep (se 2 (by rfl) ⟨244869, by rfl⟩ : syracuseStep 652985 = 489739) B489739
theorem B5535539 : Blo 287828 5535539 := bstep (se 1 (by rfl) ⟨4151654, by rfl⟩ : syracuseStep 5535539 = 8303309) B8303309
theorem B325435 : Blo 287828 325435 := bstep (se 1 (by rfl) ⟨244076, by rfl⟩ : syracuseStep 325435 = 488153) B488153
theorem B292879 : Blo 287828 292879 := bstep (se 1 (by rfl) ⟨219659, by rfl⟩ : syracuseStep 292879 = 439319) B439319
theorem B653327 : Blo 287828 653327 := bstep (se 1 (by rfl) ⟨489995, by rfl⟩ : syracuseStep 653327 = 979991) B979991
theorem B653345 : Blo 287828 653345 := bstep (se 2 (by rfl) ⟨245004, by rfl⟩ : syracuseStep 653345 = 490009) B490009
theorem B1472579 : Blo 287828 1472579 := bstep (se 1 (by rfl) ⟨1104434, by rfl⟩ : syracuseStep 1472579 = 2208869) B2208869
theorem B325903 : Blo 287828 325903 := bstep (se 1 (by rfl) ⟨244427, by rfl⟩ : syracuseStep 325903 = 488855) B488855
theorem B489847 : Blo 287828 489847 := bstep (se 1 (by rfl) ⟨367385, by rfl⟩ : syracuseStep 489847 = 734771) B734771
theorem B653687 : Blo 287828 653687 := bstep (se 1 (by rfl) ⟨490265, by rfl⟩ : syracuseStep 653687 = 980531) B980531
theorem B1472903 : Blo 287828 1472903 := bstep (se 1 (by rfl) ⟨1104677, by rfl⟩ : syracuseStep 1472903 = 2209355) B2209355
theorem B1178003 : Blo 287828 1178003 := bstep (se 1 (by rfl) ⟨883502, by rfl⟩ : syracuseStep 1178003 = 1767005) B1767005
theorem B981395 : Blo 287828 981395 := bstep (se 1 (by rfl) ⟨736046, by rfl⟩ : syracuseStep 981395 = 1472093) B1472093
theorem B653867 : Blo 287828 653867 := bstep (se 1 (by rfl) ⟨490400, by rfl⟩ : syracuseStep 653867 = 980801) B980801
theorem B490043 : Blo 287828 490043 := bstep (se 1 (by rfl) ⟨367532, by rfl⟩ : syracuseStep 490043 = 735065) B735065
theorem B785011 : Blo 287828 785011 := bstep (se 1 (by rfl) ⟨588758, by rfl⟩ : syracuseStep 785011 = 1177517) B1177517
theorem B326407 : Blo 287828 326407 := bstep (se 1 (by rfl) ⟨244805, by rfl⟩ : syracuseStep 326407 = 489611) B489611
theorem B654227 : Blo 287828 654227 := bstep (se 1 (by rfl) ⟨490670, by rfl⟩ : syracuseStep 654227 = 981341) B981341
theorem B326587 : Blo 287828 326587 := bstep (se 1 (by rfl) ⟨244940, by rfl⟩ : syracuseStep 326587 = 489881) B489881
theorem B490441 : Blo 287828 490441 := bstep (se 2 (by rfl) ⟨183915, by rfl⟩ : syracuseStep 490441 = 367831) B367831
theorem B654281 : Blo 287828 654281 := bstep (se 2 (by rfl) ⟨245355, by rfl⟩ : syracuseStep 654281 = 490711) B490711
theorem B2653499 : Blo 287828 2653499 := bstep (se 1 (by rfl) ⟨1990124, by rfl⟩ : syracuseStep 2653499 = 3980249) B3980249
theorem B327055 : Blo 287828 327055 := bstep (se 1 (by rfl) ⟨245291, by rfl⟩ : syracuseStep 327055 = 490583) B490583
theorem B392635 : Blo 287828 392635 := bstep (se 1 (by rfl) ⟨294476, by rfl⟩ : syracuseStep 392635 = 588953) B588953
theorem B2489899 : Blo 287828 2489899 := bstep (se 1 (by rfl) ⟨1867424, by rfl⟩ : syracuseStep 2489899 = 3734849) B3734849
theorem B8027747 : Blo 287828 8027747 := bstep (se 1 (by rfl) ⟨6020810, by rfl⟩ : syracuseStep 8027747 = 12041621) B12041621
theorem B491143 : Blo 287828 491143 := bstep (se 1 (by rfl) ⟨368357, by rfl⟩ : syracuseStep 491143 = 736715) B736715
theorem B654983 : Blo 287828 654983 := bstep (se 1 (by rfl) ⟨491237, by rfl⟩ : syracuseStep 654983 = 982475) B982475
theorem B982799 : Blo 287828 982799 := bstep (se 1 (by rfl) ⟨737099, by rfl⟩ : syracuseStep 982799 = 1474199) B1474199
theorem B655163 : Blo 287828 655163 := bstep (se 1 (by rfl) ⟨491372, by rfl⟩ : syracuseStep 655163 = 982745) B982745
theorem B327559 : Blo 287828 327559 := bstep (se 1 (by rfl) ⟨245669, by rfl⟩ : syracuseStep 327559 = 491339) B491339
theorem B2097049 : Blo 287828 2097049 := bstep (se 2 (by rfl) ⟨786393, by rfl⟩ : syracuseStep 2097049 = 1572787) B1572787
theorem B655289 : Blo 287828 655289 := bstep (se 2 (by rfl) ⟨245733, by rfl⟩ : syracuseStep 655289 = 491467) B491467
theorem B655379 : Blo 287828 655379 := bstep (se 1 (by rfl) ⟨491534, by rfl⟩ : syracuseStep 655379 = 983069) B983069
theorem B5898269 : Blo 287828 5898269 := bstep (se 3 (by rfl) ⟨1105925, by rfl⟩ : syracuseStep 5898269 = 2211851) B2211851
theorem B3178673 : Blo 287828 3178673 := bstep (se 2 (by rfl) ⟨1192002, by rfl⟩ : syracuseStep 3178673 = 2384005) B2384005
theorem B1868093 : Blo 287828 1868093 := bstep (se 3 (by rfl) ⟨350267, by rfl⟩ : syracuseStep 1868093 = 700535) B700535
theorem B655721 : Blo 287828 655721 := bstep (se 2 (by rfl) ⟨245895, by rfl⟩ : syracuseStep 655721 = 491791) B491791
theorem B393737 : Blo 287828 393737 := bstep (se 2 (by rfl) ⟨147651, by rfl⟩ : syracuseStep 393737 = 295303) B295303
theorem B492041 : Blo 287828 492041 := bstep (se 2 (by rfl) ⟨184515, by rfl⟩ : syracuseStep 492041 = 369031) B369031
theorem B623227 : Blo 287828 623227 := bstep (se 1 (by rfl) ⟨467420, by rfl⟩ : syracuseStep 623227 = 934841) B934841
theorem B492203 : Blo 287828 492203 := bstep (se 1 (by rfl) ⟨369152, by rfl⟩ : syracuseStep 492203 = 738305) B738305
theorem B590665 : Blo 287828 590665 := bstep (se 2 (by rfl) ⟨221499, by rfl⟩ : syracuseStep 590665 = 442999) B442999
theorem B656315 : Blo 287828 656315 := bstep (se 1 (by rfl) ⟨492236, by rfl⟩ : syracuseStep 656315 = 984473) B984473
theorem B656441 : Blo 287828 656441 := bstep (se 2 (by rfl) ⟨246165, by rfl⟩ : syracuseStep 656441 = 492331) B492331
theorem B2589763 : Blo 287828 2589763 := bstep (se 1 (by rfl) ⟨1942322, by rfl⟩ : syracuseStep 2589763 = 3884645) B3884645
theorem B984311 : Blo 287828 984311 := bstep (se 1 (by rfl) ⟨738233, by rfl⟩ : syracuseStep 984311 = 1476467) B1476467
theorem B1639703 : Blo 287828 1639703 := bstep (se 1 (by rfl) ⟨1229777, by rfl⟩ : syracuseStep 1639703 = 2459555) B2459555
theorem B1181147 : Blo 287828 1181147 := bstep (se 1 (by rfl) ⟨885860, by rfl⟩ : syracuseStep 1181147 = 1771721) B1771721
theorem B787931 : Blo 287828 787931 := bstep (se 1 (by rfl) ⟨590948, by rfl⟩ : syracuseStep 787931 = 1181897) B1181897
theorem B984635 : Blo 287828 984635 := bstep (se 1 (by rfl) ⟨738476, by rfl⟩ : syracuseStep 984635 = 1476953) B1476953
theorem B2459281 : Blo 287828 2459281 := bstep (se 2 (by rfl) ⟨922230, by rfl⟩ : syracuseStep 2459281 = 1844461) B1844461
theorem B7440173 : Blo 287828 7440173 := bstep (se 3 (by rfl) ⟨1395032, by rfl⟩ : syracuseStep 7440173 = 2790065) B2790065
theorem B984905 : Blo 287828 984905 := bstep (se 2 (by rfl) ⟨369339, by rfl⟩ : syracuseStep 984905 = 738679) B738679
theorem B461161 : Blo 287828 461161 := bstep (se 2 (by rfl) ⟨172935, by rfl⟩ : syracuseStep 461161 = 345871) B345871
theorem B822973 : Blo 287828 822973 := bstep (se 3 (by rfl) ⟨154307, by rfl⟩ : syracuseStep 822973 = 308615) B308615
theorem B4034285 : Blo 287828 4034285 := bstep (se 3 (by rfl) ⟨756428, by rfl⟩ : syracuseStep 4034285 = 1512857) B1512857
theorem B823223 : Blo 287828 823223 := bstep (se 1 (by rfl) ⟨617417, by rfl⟩ : syracuseStep 823223 = 1234835) B1234835
theorem B692155 : Blo 287828 692155 := bstep (se 1 (by rfl) ⟨519116, by rfl⟩ : syracuseStep 692155 = 1038233) B1038233
theorem B692231 : Blo 287828 692231 := bstep (se 1 (by rfl) ⟨519173, by rfl⟩ : syracuseStep 692231 = 1038347) B1038347
theorem B1773575 : Blo 287828 1773575 := bstep (se 1 (by rfl) ⟨1330181, by rfl⟩ : syracuseStep 1773575 = 2660363) B2660363
theorem B4166417 : Blo 287828 4166417 := bstep (se 2 (by rfl) ⟨1562406, by rfl⟩ : syracuseStep 4166417 = 3124813) B3124813
theorem B627643 : Blo 287828 627643 := bstep (se 1 (by rfl) ⟨470732, by rfl⟩ : syracuseStep 627643 = 941465) B941465
theorem B3150899 : Blo 287828 3150899 := bstep (se 1 (by rfl) ⟨2363174, by rfl⟩ : syracuseStep 3150899 = 4726349) B4726349
theorem B824681 : Blo 287828 824681 := bstep (se 2 (by rfl) ⟨309255, by rfl⟩ : syracuseStep 824681 = 618511) B618511
theorem B824705 : Blo 287828 824705 := bstep (se 2 (by rfl) ⟨309264, by rfl⟩ : syracuseStep 824705 = 618529) B618529
theorem B432047 : Blo 287828 432047 := bstep (se 1 (by rfl) ⟨324035, by rfl⟩ : syracuseStep 432047 = 648071) B648071
theorem B432137 : Blo 287828 432137 := bstep (se 2 (by rfl) ⟨162051, by rfl⟩ : syracuseStep 432137 = 324103) B324103
theorem B432167 : Blo 287828 432167 := bstep (se 1 (by rfl) ⟨324125, by rfl⟩ : syracuseStep 432167 = 648251) B648251
theorem B464935 : Blo 287828 464935 := bstep (se 1 (by rfl) ⟨348701, by rfl⟩ : syracuseStep 464935 = 697403) B697403
theorem B3151973 : Blo 287828 3151973 := bstep (se 4 (by rfl) ⟨295497, by rfl⟩ : syracuseStep 3151973 = 590995) B590995
theorem B432251 : Blo 287828 432251 := bstep (se 1 (by rfl) ⟨324188, by rfl⟩ : syracuseStep 432251 = 648377) B648377
theorem B432377 : Blo 287828 432377 := bstep (se 2 (by rfl) ⟨162141, by rfl⟩ : syracuseStep 432377 = 324283) B324283
theorem B432479 : Blo 287828 432479 := bstep (se 1 (by rfl) ⟨324359, by rfl⟩ : syracuseStep 432479 = 648719) B648719
theorem B432491 : Blo 287828 432491 := bstep (se 1 (by rfl) ⟨324368, by rfl⟩ : syracuseStep 432491 = 648737) B648737
theorem B367031 : Blo 287828 367031 := bstep (se 1 (by rfl) ⟨275273, by rfl⟩ : syracuseStep 367031 = 550547) B550547
theorem B498215 : Blo 287828 498215 := bstep (se 1 (by rfl) ⟨373661, by rfl⟩ : syracuseStep 498215 = 747323) B747323
theorem B432719 : Blo 287828 432719 := bstep (se 1 (by rfl) ⟨324539, by rfl⟩ : syracuseStep 432719 = 649079) B649079
theorem B367183 : Blo 287828 367183 := bstep (se 1 (by rfl) ⟨275387, by rfl⟩ : syracuseStep 367183 = 550775) B550775
theorem B432839 : Blo 287828 432839 := bstep (se 1 (by rfl) ⟨324629, by rfl⟩ : syracuseStep 432839 = 649259) B649259
theorem B433001 : Blo 287828 433001 := bstep (se 2 (by rfl) ⟨162375, by rfl⟩ : syracuseStep 433001 = 324751) B324751
theorem B433079 : Blo 287828 433079 := bstep (se 1 (by rfl) ⟨324809, by rfl⟩ : syracuseStep 433079 = 649619) B649619
theorem B2202551 : Blo 287828 2202551 := bstep (se 1 (by rfl) ⟨1651913, by rfl⟩ : syracuseStep 2202551 = 3303827) B3303827
theorem B433115 : Blo 287828 433115 := bstep (se 1 (by rfl) ⟨324836, by rfl⟩ : syracuseStep 433115 = 649673) B649673
theorem B3611621 : Blo 287828 3611621 := bstep (se 4 (by rfl) ⟨338589, by rfl⟩ : syracuseStep 3611621 = 677179) B677179
theorem B924691 : Blo 287828 924691 := bstep (se 1 (by rfl) ⟨693518, by rfl⟩ : syracuseStep 924691 = 1387037) B1387037
theorem B498887 : Blo 287828 498887 := bstep (se 1 (by rfl) ⟨374165, by rfl⟩ : syracuseStep 498887 = 748331) B748331
theorem B3710245 : Blo 287828 3710245 := bstep (se 4 (by rfl) ⟨347835, by rfl⟩ : syracuseStep 3710245 = 695671) B695671
theorem B466319 : Blo 287828 466319 := bstep (se 1 (by rfl) ⟨349739, by rfl⟩ : syracuseStep 466319 = 699479) B699479
theorem B433583 : Blo 287828 433583 := bstep (se 1 (by rfl) ⟨325187, by rfl⟩ : syracuseStep 433583 = 650375) B650375
theorem B728585 : Blo 287828 728585 := bstep (se 2 (by rfl) ⟨273219, by rfl⟩ : syracuseStep 728585 = 546439) B546439
theorem B433673 : Blo 287828 433673 := bstep (se 2 (by rfl) ⟨162627, by rfl⟩ : syracuseStep 433673 = 325255) B325255
theorem B728615 : Blo 287828 728615 := bstep (se 1 (by rfl) ⟨546461, by rfl⟩ : syracuseStep 728615 = 1092923) B1092923
theorem B433703 : Blo 287828 433703 := bstep (se 1 (by rfl) ⟨325277, by rfl⟩ : syracuseStep 433703 = 650555) B650555
theorem B925307 : Blo 287828 925307 := bstep (se 1 (by rfl) ⟨693980, by rfl⟩ : syracuseStep 925307 = 1387961) B1387961
theorem B433787 : Blo 287828 433787 := bstep (se 1 (by rfl) ⟨325340, by rfl⟩ : syracuseStep 433787 = 650681) B650681
theorem B4202117 : Blo 287828 4202117 := bstep (se 4 (by rfl) ⟨393948, by rfl⟩ : syracuseStep 4202117 = 787897) B787897
theorem B1777351 : Blo 287828 1777351 := bstep (se 1 (by rfl) ⟨1333013, by rfl⟩ : syracuseStep 1777351 = 2666027) B2666027
theorem B368327 : Blo 287828 368327 := bstep (se 1 (by rfl) ⟨276245, by rfl⟩ : syracuseStep 368327 = 552491) B552491
theorem B433913 : Blo 287828 433913 := bstep (se 2 (by rfl) ⟨162717, by rfl⟩ : syracuseStep 433913 = 325435) B325435
theorem B434015 : Blo 287828 434015 := bstep (se 1 (by rfl) ⟨325511, by rfl⟩ : syracuseStep 434015 = 651023) B651023
theorem B368479 : Blo 287828 368479 := bstep (se 1 (by rfl) ⟨276359, by rfl⟩ : syracuseStep 368479 = 552719) B552719
theorem B630623 : Blo 287828 630623 := bstep (se 1 (by rfl) ⟨472967, by rfl⟩ : syracuseStep 630623 = 945935) B945935
theorem B728939 : Blo 287828 728939 := bstep (se 1 (by rfl) ⟨546704, by rfl⟩ : syracuseStep 728939 = 1093409) B1093409
theorem B434027 : Blo 287828 434027 := bstep (se 1 (by rfl) ⟨325520, by rfl⟩ : syracuseStep 434027 = 651041) B651041
theorem B466831 : Blo 287828 466831 := bstep (se 1 (by rfl) ⟨350123, by rfl⟩ : syracuseStep 466831 = 700247) B700247
theorem B434255 : Blo 287828 434255 := bstep (se 1 (by rfl) ⟨325691, by rfl⟩ : syracuseStep 434255 = 651383) B651383
theorem B434375 : Blo 287828 434375 := bstep (se 1 (by rfl) ⟨325781, by rfl⟩ : syracuseStep 434375 = 651563) B651563
theorem B434537 : Blo 287828 434537 := bstep (se 2 (by rfl) ⟨162951, by rfl⟩ : syracuseStep 434537 = 325903) B325903
theorem B2204009 : Blo 287828 2204009 := bstep (se 2 (by rfl) ⟨826503, by rfl⟩ : syracuseStep 2204009 = 1653007) B1653007
theorem B631145 : Blo 287828 631145 := bstep (se 2 (by rfl) ⟨236679, by rfl⟩ : syracuseStep 631145 = 473359) B473359
theorem B434615 : Blo 287828 434615 := bstep (se 1 (by rfl) ⟨325961, by rfl⟩ : syracuseStep 434615 = 651923) B651923
theorem B434651 : Blo 287828 434651 := bstep (se 1 (by rfl) ⟨325988, by rfl⟩ : syracuseStep 434651 = 651977) B651977
theorem B729587 : Blo 287828 729587 := bstep (se 1 (by rfl) ⟨547190, by rfl⟩ : syracuseStep 729587 = 1094381) B1094381
theorem B926423 : Blo 287828 926423 := bstep (se 1 (by rfl) ⟨694817, by rfl⟩ : syracuseStep 926423 = 1389635) B1389635
theorem B34382627 : Blo 287828 34382627 := bstep (se 1 (by rfl) ⟨25786970, by rfl⟩ : syracuseStep 34382627 = 51573941) B51573941
theorem B435119 : Blo 287828 435119 := bstep (se 1 (by rfl) ⟨326339, by rfl⟩ : syracuseStep 435119 = 652679) B652679
theorem B730043 : Blo 287828 730043 := bstep (se 1 (by rfl) ⟨547532, by rfl⟩ : syracuseStep 730043 = 1095065) B1095065
theorem B435209 : Blo 287828 435209 := bstep (se 2 (by rfl) ⟨163203, by rfl⟩ : syracuseStep 435209 = 326407) B326407
theorem B435239 : Blo 287828 435239 := bstep (se 1 (by rfl) ⟨326429, by rfl⟩ : syracuseStep 435239 = 652859) B652859
theorem B435323 : Blo 287828 435323 := bstep (se 1 (by rfl) ⟨326492, by rfl⟩ : syracuseStep 435323 = 652985) B652985
theorem B435449 : Blo 287828 435449 := bstep (se 2 (by rfl) ⟨163293, by rfl⟩ : syracuseStep 435449 = 326587) B326587
theorem B435551 : Blo 287828 435551 := bstep (se 1 (by rfl) ⟨326663, by rfl⟩ : syracuseStep 435551 = 653327) B653327
theorem B435563 : Blo 287828 435563 := bstep (se 1 (by rfl) ⟨326672, by rfl⟩ : syracuseStep 435563 = 653345) B653345
theorem B927101 : Blo 287828 927101 := bstep (se 3 (by rfl) ⟨173831, by rfl⟩ : syracuseStep 927101 = 347663) B347663
theorem B435791 : Blo 287828 435791 := bstep (se 1 (by rfl) ⟨326843, by rfl⟩ : syracuseStep 435791 = 653687) B653687
theorem B730721 : Blo 287828 730721 := bstep (se 2 (by rfl) ⟨274020, by rfl⟩ : syracuseStep 730721 = 548041) B548041
theorem B435911 : Blo 287828 435911 := bstep (se 1 (by rfl) ⟨326933, by rfl⟩ : syracuseStep 435911 = 653867) B653867
theorem B35923661 : Blo 287828 35923661 := bstep (se 3 (by rfl) ⟨6735686, by rfl⟩ : syracuseStep 35923661 = 13471373) B13471373
theorem B1648451 : Blo 287828 1648451 := bstep (se 1 (by rfl) ⟨1236338, by rfl⟩ : syracuseStep 1648451 = 2472677) B2472677
theorem B436073 : Blo 287828 436073 := bstep (se 2 (by rfl) ⟨163527, by rfl⟩ : syracuseStep 436073 = 327055) B327055
theorem B436151 : Blo 287828 436151 := bstep (se 1 (by rfl) ⟨327113, by rfl⟩ : syracuseStep 436151 = 654227) B654227
theorem B1451963 : Blo 287828 1451963 := bstep (se 1 (by rfl) ⟨1088972, by rfl⟩ : syracuseStep 1451963 = 2177945) B2177945
theorem B436187 : Blo 287828 436187 := bstep (se 1 (by rfl) ⟨327140, by rfl⟩ : syracuseStep 436187 = 654281) B654281
theorem B3319865 : Blo 287828 3319865 := bstep (se 2 (by rfl) ⟨1244949, by rfl⟩ : syracuseStep 3319865 = 2489899) B2489899
theorem B2205953 : Blo 287828 2205953 := bstep (se 2 (by rfl) ⟨827232, by rfl⟩ : syracuseStep 2205953 = 1654465) B1654465
theorem B1648907 : Blo 287828 1648907 := bstep (se 1 (by rfl) ⟨1236680, by rfl⟩ : syracuseStep 1648907 = 2473361) B2473361
theorem B5351831 : Blo 287828 5351831 := bstep (se 1 (by rfl) ⟨4013873, by rfl⟩ : syracuseStep 5351831 = 8027747) B8027747
theorem B436655 : Blo 287828 436655 := bstep (se 1 (by rfl) ⟨327491, by rfl⟩ : syracuseStep 436655 = 654983) B654983
theorem B436745 : Blo 287828 436745 := bstep (se 2 (by rfl) ⟨163779, by rfl⟩ : syracuseStep 436745 = 327559) B327559
theorem B2796065 : Blo 287828 2796065 := bstep (se 2 (by rfl) ⟨1048524, by rfl⟩ : syracuseStep 2796065 = 2097049) B2097049
theorem B436775 : Blo 287828 436775 := bstep (se 1 (by rfl) ⟨327581, by rfl⟩ : syracuseStep 436775 = 655163) B655163
theorem B436859 : Blo 287828 436859 := bstep (se 1 (by rfl) ⟨327644, by rfl⟩ : syracuseStep 436859 = 655289) B655289
theorem B436985 : Blo 287828 436985 := bstep (se 2 (by rfl) ⟨163869, by rfl⟩ : syracuseStep 436985 = 327739) B327739
theorem B699209 : Blo 287828 699209 := bstep (se 2 (by rfl) ⟨262203, by rfl⟩ : syracuseStep 699209 = 524407) B524407
theorem B437087 : Blo 287828 437087 := bstep (se 1 (by rfl) ⟨327815, by rfl⟩ : syracuseStep 437087 = 655631) B655631
theorem B437099 : Blo 287828 437099 := bstep (se 1 (by rfl) ⟨327824, by rfl⟩ : syracuseStep 437099 = 655649) B655649
theorem B1649591 : Blo 287828 1649591 := bstep (se 1 (by rfl) ⟨1237193, by rfl⟩ : syracuseStep 1649591 = 2474387) B2474387
theorem B732179 : Blo 287828 732179 := bstep (se 1 (by rfl) ⟨549134, by rfl⟩ : syracuseStep 732179 = 1098269) B1098269
theorem B437327 : Blo 287828 437327 := bstep (se 1 (by rfl) ⟨327995, by rfl⟩ : syracuseStep 437327 = 655991) B655991
theorem B928883 : Blo 287828 928883 := bstep (se 1 (by rfl) ⟨696662, by rfl⟩ : syracuseStep 928883 = 1393325) B1393325
theorem B928921 : Blo 287828 928921 := bstep (se 2 (by rfl) ⟨348345, by rfl⟩ : syracuseStep 928921 = 696691) B696691
theorem B437447 : Blo 287828 437447 := bstep (se 1 (by rfl) ⟨328085, by rfl⟩ : syracuseStep 437447 = 656171) B656171
theorem B437609 : Blo 287828 437609 := bstep (se 2 (by rfl) ⟨164103, by rfl⟩ : syracuseStep 437609 = 328207) B328207
theorem B437687 : Blo 287828 437687 := bstep (se 1 (by rfl) ⟨328265, by rfl⟩ : syracuseStep 437687 = 656531) B656531
theorem B568763 : Blo 287828 568763 := bstep (se 1 (by rfl) ⟨426572, by rfl⟩ : syracuseStep 568763 = 853145) B853145
theorem B732635 : Blo 287828 732635 := bstep (se 1 (by rfl) ⟨549476, by rfl⟩ : syracuseStep 732635 = 1098953) B1098953
theorem B437723 : Blo 287828 437723 := bstep (se 1 (by rfl) ⟨328292, by rfl⟩ : syracuseStep 437723 = 656585) B656585
theorem B1486433 : Blo 287828 1486433 := bstep (se 2 (by rfl) ⟨557412, by rfl⟩ : syracuseStep 1486433 = 1114825) B1114825
theorem B1650365 : Blo 287828 1650365 := bstep (se 3 (by rfl) ⟨309443, by rfl⟩ : syracuseStep 1650365 = 618887) B618887
theorem B2993885 : Blo 287828 2993885 := bstep (se 3 (by rfl) ⟨561353, by rfl⟩ : syracuseStep 2993885 = 1122707) B1122707
theorem B1651049 : Blo 287828 1651049 := bstep (se 2 (by rfl) ⟨619143, by rfl⟩ : syracuseStep 1651049 = 1238287) B1238287
theorem B1094107 : Blo 287828 1094107 := bstep (se 1 (by rfl) ⟨820580, by rfl⟩ : syracuseStep 1094107 = 1641161) B1641161
theorem B733819 : Blo 287828 733819 := bstep (se 1 (by rfl) ⟨550364, by rfl⟩ : syracuseStep 733819 = 1100729) B1100729
theorem B2470763 : Blo 287828 2470763 := bstep (se 1 (by rfl) ⟨1853072, by rfl⟩ : syracuseStep 2470763 = 3706145) B3706145
theorem B2635325 : Blo 287828 2635325 := bstep (se 3 (by rfl) ⟨494123, by rfl⟩ : syracuseStep 2635325 = 988247) B988247
theorem B1095353 : Blo 287828 1095353 := bstep (se 2 (by rfl) ⟨410757, by rfl⟩ : syracuseStep 1095353 = 821515) B821515
theorem B1095383 : Blo 287828 1095383 := bstep (se 1 (by rfl) ⟨821537, by rfl⟩ : syracuseStep 1095383 = 1643075) B1643075
theorem B86751245 : Blo 287828 86751245 := bstep (se 3 (by rfl) ⟨16265858, by rfl⟩ : syracuseStep 86751245 = 32531717) B32531717
theorem B1652825 : Blo 287828 1652825 := bstep (se 2 (by rfl) ⟨619809, by rfl⟩ : syracuseStep 1652825 = 1239619) B1239619
theorem B2406935 : Blo 287828 2406935 := bstep (se 1 (by rfl) ⟨1805201, by rfl⟩ : syracuseStep 2406935 = 3610403) B3610403
theorem B2210327 : Blo 287828 2210327 := bstep (se 1 (by rfl) ⟨1657745, by rfl⟩ : syracuseStep 2210327 = 3315491) B3315491
theorem B1653281 : Blo 287828 1653281 := bstep (se 2 (by rfl) ⟨619980, by rfl⟩ : syracuseStep 1653281 = 1239961) B1239961
theorem B1653533 : Blo 287828 1653533 := bstep (se 3 (by rfl) ⟨310037, by rfl⟩ : syracuseStep 1653533 = 620075) B620075
theorem B7093109 : Blo 287828 7093109 := bstep (se 5 (by rfl) ⟨332489, by rfl⟩ : syracuseStep 7093109 = 664979) B664979
theorem B311135 : Blo 287828 311135 := bstep (se 1 (by rfl) ⟨233351, by rfl⟩ : syracuseStep 311135 = 466703) B466703
theorem B1752941 : Blo 287828 1752941 := bstep (se 3 (by rfl) ⟨328676, by rfl⟩ : syracuseStep 1752941 = 657353) B657353
theorem B933815 : Blo 287828 933815 := bstep (se 1 (by rfl) ⟨700361, by rfl⟩ : syracuseStep 933815 = 1400723) B1400723
theorem B1097995 : Blo 287828 1097995 := bstep (se 1 (by rfl) ⟨823496, by rfl⟩ : syracuseStep 1097995 = 1646993) B1646993
theorem B442919 : Blo 287828 442919 := bstep (se 1 (by rfl) ⟨332189, by rfl⟩ : syracuseStep 442919 = 664379) B664379
theorem B1098299 : Blo 287828 1098299 := bstep (se 1 (by rfl) ⟨823724, by rfl⟩ : syracuseStep 1098299 = 1647449) B1647449
theorem B738143 : Blo 287828 738143 := bstep (se 1 (by rfl) ⟨553607, by rfl⟩ : syracuseStep 738143 = 1107215) B1107215
theorem B1852307 : Blo 287828 1852307 := bstep (se 1 (by rfl) ⟨1389230, by rfl⟩ : syracuseStep 1852307 = 2778461) B2778461
theorem B3130487 : Blo 287828 3130487 := bstep (se 1 (by rfl) ⟨2347865, by rfl⟩ : syracuseStep 3130487 = 4695731) B4695731
theorem B2082401 : Blo 287828 2082401 := bstep (se 2 (by rfl) ⟨780900, by rfl⟩ : syracuseStep 2082401 = 1561801) B1561801
theorem B411259 : Blo 287828 411259 := bstep (se 1 (by rfl) ⟨308444, by rfl⟩ : syracuseStep 411259 = 616889) B616889
theorem B1099453 : Blo 287828 1099453 := bstep (se 3 (by rfl) ⟨206147, by rfl⟩ : syracuseStep 1099453 = 412295) B412295
theorem B1853279 : Blo 287828 1853279 := bstep (se 1 (by rfl) ⟨1389959, by rfl⟩ : syracuseStep 1853279 = 2779919) B2779919
theorem B39929699 : Blo 287828 39929699 := bstep (se 1 (by rfl) ⟨29947274, by rfl⟩ : syracuseStep 39929699 = 59894549) B59894549
theorem B6637571 : Blo 287828 6637571 := bstep (se 1 (by rfl) ⟨4978178, by rfl⟩ : syracuseStep 6637571 = 9956357) B9956357
theorem B4180025 : Blo 287828 4180025 := bstep (se 2 (by rfl) ⟨1567509, by rfl⟩ : syracuseStep 4180025 = 3135019) B3135019
theorem B1100411 : Blo 287828 1100411 := bstep (se 1 (by rfl) ⟨825308, by rfl⟩ : syracuseStep 1100411 = 1650617) B1650617
theorem B412409 : Blo 287828 412409 := bstep (se 2 (by rfl) ⟨154653, by rfl⟩ : syracuseStep 412409 = 309307) B309307
theorem B314407 : Blo 287828 314407 := bstep (se 1 (by rfl) ⟨235805, by rfl⟩ : syracuseStep 314407 = 471611) B471611
theorem B1657907 : Blo 287828 1657907 := bstep (se 1 (by rfl) ⟨1243430, by rfl⟩ : syracuseStep 1657907 = 2486861) B2486861
theorem B1461401 : Blo 287828 1461401 := bstep (se 2 (by rfl) ⟨548025, by rfl⟩ : syracuseStep 1461401 = 1096051) B1096051
theorem B1101185 : Blo 287828 1101185 := bstep (se 2 (by rfl) ⟨412944, by rfl⟩ : syracuseStep 1101185 = 825889) B825889
theorem B1396187 : Blo 287828 1396187 := bstep (se 1 (by rfl) ⟨1047140, by rfl⟩ : syracuseStep 1396187 = 2094281) B2094281
theorem B1756811 : Blo 287828 1756811 := bstep (se 1 (by rfl) ⟨1317608, by rfl⟩ : syracuseStep 1756811 = 2635217) B2635217
theorem B2870923 : Blo 287828 2870923 := bstep (se 1 (by rfl) ⟨2153192, by rfl⟩ : syracuseStep 2870923 = 4306385) B4306385
theorem B2215673 : Blo 287828 2215673 := bstep (se 2 (by rfl) ⟨830877, by rfl⟩ : syracuseStep 2215673 = 1661755) B1661755
theorem B3690359 : Blo 287828 3690359 := bstep (se 1 (by rfl) ⟨2767769, by rfl⟩ : syracuseStep 3690359 = 5535539) B5535539
theorem B9424775 : Blo 287828 9424775 := bstep (se 1 (by rfl) ⟨7068581, by rfl⟩ : syracuseStep 9424775 = 14137163) B14137163
theorem B1102369 : Blo 287828 1102369 := bstep (se 2 (by rfl) ⟨413388, by rfl⟩ : syracuseStep 1102369 = 826777) B826777
theorem B971513 : Blo 287828 971513 := bstep (se 2 (by rfl) ⟨364317, by rfl⟩ : syracuseStep 971513 = 728635) B728635
theorem B971783 : Blo 287828 971783 := bstep (se 1 (by rfl) ⟨728837, by rfl⟩ : syracuseStep 971783 = 1457675) B1457675
theorem B1102855 : Blo 287828 1102855 := bstep (se 1 (by rfl) ⟨827141, by rfl⟩ : syracuseStep 1102855 = 1654283) B1654283
theorem B971891 : Blo 287828 971891 := bstep (se 1 (by rfl) ⟨728918, by rfl⟩ : syracuseStep 971891 = 1457837) B1457837
theorem B2086091 : Blo 287828 2086091 := bstep (se 1 (by rfl) ⟨1564568, by rfl⟩ : syracuseStep 2086091 = 3129137) B3129137
theorem B972161 : Blo 287828 972161 := bstep (se 2 (by rfl) ⟨364560, by rfl⟩ : syracuseStep 972161 = 729121) B729121
theorem B47502733 : Blo 287828 47502733 := bstep (se 3 (by rfl) ⟨8906762, by rfl⟩ : syracuseStep 47502733 = 17813525) B17813525
theorem B1856969 : Blo 287828 1856969 := bstep (se 2 (by rfl) ⟨696363, by rfl⟩ : syracuseStep 1856969 = 1392727) B1392727
theorem B1103341 : Blo 287828 1103341 := bstep (se 3 (by rfl) ⟨206876, by rfl⟩ : syracuseStep 1103341 = 413753) B413753
theorem B1037971 : Blo 287828 1037971 := bstep (se 1 (by rfl) ⟨778478, by rfl⟩ : syracuseStep 1037971 = 1556957) B1556957
theorem B1103645 : Blo 287828 1103645 := bstep (se 3 (by rfl) ⟨206933, by rfl⟩ : syracuseStep 1103645 = 413867) B413867
theorem B1398647 : Blo 287828 1398647 := bstep (se 1 (by rfl) ⟨1048985, by rfl⟩ : syracuseStep 1398647 = 2097971) B2097971
theorem B546743 : Blo 287828 546743 := bstep (se 1 (by rfl) ⟨410057, by rfl⟩ : syracuseStep 546743 = 820115) B820115
theorem B2086843 : Blo 287828 2086843 := bstep (se 1 (by rfl) ⟨1565132, by rfl⟩ : syracuseStep 2086843 = 3130265) B3130265
theorem B972971 : Blo 287828 972971 := bstep (se 1 (by rfl) ⟨729728, by rfl⟩ : syracuseStep 972971 = 1459457) B1459457
theorem B547145 : Blo 287828 547145 := bstep (se 2 (by rfl) ⟨205179, by rfl⟩ : syracuseStep 547145 = 410359) B410359
theorem B973511 : Blo 287828 973511 := bstep (se 1 (by rfl) ⟨730133, by rfl⟩ : syracuseStep 973511 = 1460267) B1460267
theorem B2218697 : Blo 287828 2218697 := bstep (se 2 (by rfl) ⟨832011, by rfl⟩ : syracuseStep 2218697 = 1664023) B1664023
theorem B4152293 : Blo 287828 4152293 := bstep (se 4 (by rfl) ⟨389277, by rfl⟩ : syracuseStep 4152293 = 778555) B778555
theorem B547859 : Blo 287828 547859 := bstep (se 1 (by rfl) ⟨410894, by rfl⟩ : syracuseStep 547859 = 821789) B821789
theorem B547897 : Blo 287828 547897 := bstep (se 2 (by rfl) ⟨205461, by rfl⟩ : syracuseStep 547897 = 410923) B410923
theorem B548201 : Blo 287828 548201 := bstep (se 2 (by rfl) ⟨205575, by rfl⟩ : syracuseStep 548201 = 411151) B411151
theorem B974375 : Blo 287828 974375 := bstep (se 1 (by rfl) ⟨730781, by rfl⟩ : syracuseStep 974375 = 1461563) B1461563
theorem B974483 : Blo 287828 974483 := bstep (se 1 (by rfl) ⟨730862, by rfl⟩ : syracuseStep 974483 = 1461725) B1461725
theorem B1990291 : Blo 287828 1990291 := bstep (se 1 (by rfl) ⟨1492718, by rfl⟩ : syracuseStep 1990291 = 2985437) B2985437
theorem B11951887 : Blo 287828 11951887 := bstep (se 1 (by rfl) ⟨8963915, by rfl⟩ : syracuseStep 11951887 = 17927831) B17927831
theorem B974699 : Blo 287828 974699 := bstep (se 1 (by rfl) ⟨731024, by rfl⟩ : syracuseStep 974699 = 1462049) B1462049
theorem B1105771 : Blo 287828 1105771 := bstep (se 1 (by rfl) ⟨829328, by rfl⟩ : syracuseStep 1105771 = 1658657) B1658657
theorem B974753 : Blo 287828 974753 := bstep (se 2 (by rfl) ⟨365532, by rfl⟩ : syracuseStep 974753 = 731065) B731065
theorem B2220047 : Blo 287828 2220047 := bstep (se 1 (by rfl) ⟨1665035, by rfl⟩ : syracuseStep 2220047 = 3330071) B3330071
theorem B483451 : Blo 287828 483451 := bstep (se 1 (by rfl) ⟨362588, by rfl⟩ : syracuseStep 483451 = 725177) B725177
theorem B975347 : Blo 287828 975347 := bstep (se 1 (by rfl) ⟨731510, by rfl⟩ : syracuseStep 975347 = 1463021) B1463021
theorem B549499 : Blo 287828 549499 := bstep (se 1 (by rfl) ⟨412124, by rfl⟩ : syracuseStep 549499 = 824249) B824249
theorem B549575 : Blo 287828 549575 := bstep (se 1 (by rfl) ⟨412181, by rfl⟩ : syracuseStep 549575 = 824363) B824363
theorem B647891 : Blo 287828 647891 := bstep (se 1 (by rfl) ⟨485918, by rfl⟩ : syracuseStep 647891 = 971837) B971837
theorem B418655 : Blo 287828 418655 := bstep (se 1 (by rfl) ⟨313991, by rfl⟩ : syracuseStep 418655 = 627983) B627983
theorem B2352017 : Blo 287828 2352017 := bstep (se 2 (by rfl) ⟨882006, by rfl⟩ : syracuseStep 2352017 = 1764013) B1764013
theorem B975887 : Blo 287828 975887 := bstep (se 1 (by rfl) ⟨731915, by rfl⟩ : syracuseStep 975887 = 1463831) B1463831
theorem B287839 : Blo 287828 287839 := bstep (se 1 (by rfl) ⟨215879, by rfl⟩ : syracuseStep 287839 = 431759) B431759
theorem B549985 : Blo 287828 549985 := bstep (se 2 (by rfl) ⟨206244, by rfl⟩ : syracuseStep 549985 = 412489) B412489
theorem B287867 : Blo 287828 287867 := bstep (se 1 (by rfl) ⟨215900, by rfl⟩ : syracuseStep 287867 = 431801) B431801
theorem B4449451 : Blo 287828 4449451 := bstep (se 1 (by rfl) ⟨3337088, by rfl⟩ : syracuseStep 4449451 = 6674177) B6674177
theorem B287919 : Blo 287828 287919 := bstep (se 1 (by rfl) ⟨215939, by rfl⟩ : syracuseStep 287919 = 431879) B431879
theorem B287943 : Blo 287828 287943 := bstep (se 1 (by rfl) ⟨215957, by rfl⟩ : syracuseStep 287943 = 431915) B431915
theorem B287963 : Blo 287828 287963 := bstep (se 1 (by rfl) ⟨215972, by rfl⟩ : syracuseStep 287963 = 431945) B431945
theorem B551380229 : Blo 287828 551380229 := bstep (se 4 (by rfl) ⟨51691896, by rfl⟩ : syracuseStep 551380229 = 103383793) B103383793
theorem B288039 : Blo 287828 288039 := bstep (se 1 (by rfl) ⟨216029, by rfl⟩ : syracuseStep 288039 = 432059) B432059
theorem B288079 : Blo 287828 288079 := bstep (se 1 (by rfl) ⟨216059, by rfl⟩ : syracuseStep 288079 = 432119) B432119
theorem B288095 : Blo 287828 288095 := bstep (se 1 (by rfl) ⟨216071, by rfl⟩ : syracuseStep 288095 = 432143) B432143
theorem B288123 : Blo 287828 288123 := bstep (se 1 (by rfl) ⟨216092, by rfl⟩ : syracuseStep 288123 = 432185) B432185
theorem B288175 : Blo 287828 288175 := bstep (se 1 (by rfl) ⟨216131, by rfl⟩ : syracuseStep 288175 = 432263) B432263
theorem B550327 : Blo 287828 550327 := bstep (se 1 (by rfl) ⟨412745, by rfl⟩ : syracuseStep 550327 = 825491) B825491
theorem B288199 : Blo 287828 288199 := bstep (se 1 (by rfl) ⟨216149, by rfl⟩ : syracuseStep 288199 = 432299) B432299
theorem B288219 : Blo 287828 288219 := bstep (se 1 (by rfl) ⟨216164, by rfl⟩ : syracuseStep 288219 = 432329) B432329
theorem B288295 : Blo 287828 288295 := bstep (se 1 (by rfl) ⟨216221, by rfl⟩ : syracuseStep 288295 = 432443) B432443
theorem B288335 : Blo 287828 288335 := bstep (se 1 (by rfl) ⟨216251, by rfl⟩ : syracuseStep 288335 = 432503) B432503
theorem B288351 : Blo 287828 288351 := bstep (se 1 (by rfl) ⟨216263, by rfl⟩ : syracuseStep 288351 = 432527) B432527
theorem B976481 : Blo 287828 976481 := bstep (se 2 (by rfl) ⟨366180, by rfl⟩ : syracuseStep 976481 = 732361) B732361
theorem B648827 : Blo 287828 648827 := bstep (se 1 (by rfl) ⟨486620, by rfl⟩ : syracuseStep 648827 = 973241) B973241
theorem B288379 : Blo 287828 288379 := bstep (se 1 (by rfl) ⟨216284, by rfl⟩ : syracuseStep 288379 = 432569) B432569
theorem B1468043 : Blo 287828 1468043 := bstep (se 1 (by rfl) ⟨1101032, by rfl⟩ : syracuseStep 1468043 = 2202065) B2202065
theorem B288431 : Blo 287828 288431 := bstep (se 1 (by rfl) ⟨216323, by rfl⟩ : syracuseStep 288431 = 432647) B432647
theorem B288455 : Blo 287828 288455 := bstep (se 1 (by rfl) ⟨216341, by rfl⟩ : syracuseStep 288455 = 432683) B432683
theorem B288475 : Blo 287828 288475 := bstep (se 1 (by rfl) ⟨216356, by rfl⟩ : syracuseStep 288475 = 432713) B432713
theorem B648953 : Blo 287828 648953 := bstep (se 2 (by rfl) ⟨243357, by rfl⟩ : syracuseStep 648953 = 486715) B486715
theorem B288551 : Blo 287828 288551 := bstep (se 1 (by rfl) ⟨216413, by rfl⟩ : syracuseStep 288551 = 432827) B432827
theorem B550729 : Blo 287828 550729 := bstep (se 2 (by rfl) ⟨206523, by rfl⟩ : syracuseStep 550729 = 413047) B413047
theorem B288591 : Blo 287828 288591 := bstep (se 1 (by rfl) ⟨216443, by rfl⟩ : syracuseStep 288591 = 432887) B432887
theorem B288607 : Blo 287828 288607 := bstep (se 1 (by rfl) ⟨216455, by rfl⟩ : syracuseStep 288607 = 432911) B432911
theorem B288635 : Blo 287828 288635 := bstep (se 1 (by rfl) ⟨216476, by rfl⟩ : syracuseStep 288635 = 432953) B432953
theorem B288687 : Blo 287828 288687 := bstep (se 1 (by rfl) ⟨216515, by rfl⟩ : syracuseStep 288687 = 433031) B433031
theorem B288711 : Blo 287828 288711 := bstep (se 1 (by rfl) ⟨216533, by rfl⟩ : syracuseStep 288711 = 433067) B433067
theorem B4679633 : Blo 287828 4679633 := bstep (se 2 (by rfl) ⟨1754862, by rfl⟩ : syracuseStep 4679633 = 3509725) B3509725
theorem B288731 : Blo 287828 288731 := bstep (se 1 (by rfl) ⟨216548, by rfl⟩ : syracuseStep 288731 = 433097) B433097
theorem B649223 : Blo 287828 649223 := bstep (se 1 (by rfl) ⟨486917, by rfl⟩ : syracuseStep 649223 = 973835) B973835
theorem B288807 : Blo 287828 288807 := bstep (se 1 (by rfl) ⟨216605, by rfl⟩ : syracuseStep 288807 = 433211) B433211
theorem B649295 : Blo 287828 649295 := bstep (se 1 (by rfl) ⟨486971, by rfl⟩ : syracuseStep 649295 = 973943) B973943
theorem B288847 : Blo 287828 288847 := bstep (se 1 (by rfl) ⟨216635, by rfl⟩ : syracuseStep 288847 = 433271) B433271
theorem B288863 : Blo 287828 288863 := bstep (se 1 (by rfl) ⟨216647, by rfl⟩ : syracuseStep 288863 = 433295) B433295
theorem B288891 : Blo 287828 288891 := bstep (se 1 (by rfl) ⟨216668, by rfl⟩ : syracuseStep 288891 = 433337) B433337
theorem B288943 : Blo 287828 288943 := bstep (se 1 (by rfl) ⟨216707, by rfl⟩ : syracuseStep 288943 = 433415) B433415
theorem B288967 : Blo 287828 288967 := bstep (se 1 (by rfl) ⟨216725, by rfl⟩ : syracuseStep 288967 = 433451) B433451
theorem B288987 : Blo 287828 288987 := bstep (se 1 (by rfl) ⟨216740, by rfl⟩ : syracuseStep 288987 = 433481) B433481
theorem B289063 : Blo 287828 289063 := bstep (se 1 (by rfl) ⟨216797, by rfl⟩ : syracuseStep 289063 = 433595) B433595
theorem B289103 : Blo 287828 289103 := bstep (se 1 (by rfl) ⟨216827, by rfl⟩ : syracuseStep 289103 = 433655) B433655
theorem B289119 : Blo 287828 289119 := bstep (se 1 (by rfl) ⟨216839, by rfl⟩ : syracuseStep 289119 = 433679) B433679
theorem B289147 : Blo 287828 289147 := bstep (se 1 (by rfl) ⟨216860, by rfl⟩ : syracuseStep 289147 = 433721) B433721
theorem B3795335 : Blo 287828 3795335 := bstep (se 1 (by rfl) ⟨2846501, by rfl⟩ : syracuseStep 3795335 = 5693003) B5693003
theorem B289199 : Blo 287828 289199 := bstep (se 1 (by rfl) ⟨216899, by rfl⟩ : syracuseStep 289199 = 433799) B433799
theorem B584119 : Blo 287828 584119 := bstep (se 1 (by rfl) ⟨438089, by rfl⟩ : syracuseStep 584119 = 876179) B876179
theorem B289223 : Blo 287828 289223 := bstep (se 1 (by rfl) ⟨216917, by rfl⟩ : syracuseStep 289223 = 433835) B433835
theorem B485851 : Blo 287828 485851 := bstep (se 1 (by rfl) ⟨364388, by rfl⟩ : syracuseStep 485851 = 728777) B728777
theorem B649691 : Blo 287828 649691 := bstep (se 1 (by rfl) ⟨487268, by rfl⟩ : syracuseStep 649691 = 974537) B974537
theorem B289243 : Blo 287828 289243 := bstep (se 1 (by rfl) ⟨216932, by rfl⟩ : syracuseStep 289243 = 433865) B433865
theorem B551443 : Blo 287828 551443 := bstep (se 1 (by rfl) ⟨413582, by rfl⟩ : syracuseStep 551443 = 827165) B827165
theorem B289319 : Blo 287828 289319 := bstep (se 1 (by rfl) ⟨216989, by rfl⟩ : syracuseStep 289319 = 433979) B433979
theorem B289359 : Blo 287828 289359 := bstep (se 1 (by rfl) ⟨217019, by rfl⟩ : syracuseStep 289359 = 434039) B434039
theorem B289375 : Blo 287828 289375 := bstep (se 1 (by rfl) ⟨217031, by rfl⟩ : syracuseStep 289375 = 434063) B434063
theorem B289403 : Blo 287828 289403 := bstep (se 1 (by rfl) ⟨217052, by rfl⟩ : syracuseStep 289403 = 434105) B434105
theorem B289455 : Blo 287828 289455 := bstep (se 1 (by rfl) ⟨217091, by rfl⟩ : syracuseStep 289455 = 434183) B434183
theorem B1108669 : Blo 287828 1108669 := bstep (se 3 (by rfl) ⟨207875, by rfl⟩ : syracuseStep 1108669 = 415751) B415751
theorem B289479 : Blo 287828 289479 := bstep (se 1 (by rfl) ⟨217109, by rfl⟩ : syracuseStep 289479 = 434219) B434219
theorem B289499 : Blo 287828 289499 := bstep (se 1 (by rfl) ⟨217124, by rfl⟩ : syracuseStep 289499 = 434249) B434249
theorem B289575 : Blo 287828 289575 := bstep (se 1 (by rfl) ⟨217181, by rfl⟩ : syracuseStep 289575 = 434363) B434363
theorem B289615 : Blo 287828 289615 := bstep (se 1 (by rfl) ⟨217211, by rfl⟩ : syracuseStep 289615 = 434423) B434423
theorem B289631 : Blo 287828 289631 := bstep (se 1 (by rfl) ⟨217223, by rfl⟩ : syracuseStep 289631 = 434447) B434447
theorem B551785 : Blo 287828 551785 := bstep (se 2 (by rfl) ⟨206919, by rfl⟩ : syracuseStep 551785 = 413839) B413839
theorem B289659 : Blo 287828 289659 := bstep (se 1 (by rfl) ⟨217244, by rfl⟩ : syracuseStep 289659 = 434489) B434489
theorem B650159 : Blo 287828 650159 := bstep (se 1 (by rfl) ⟨487619, by rfl⟩ : syracuseStep 650159 = 975239) B975239
theorem B289711 : Blo 287828 289711 := bstep (se 1 (by rfl) ⟨217283, by rfl⟩ : syracuseStep 289711 = 434567) B434567
theorem B289735 : Blo 287828 289735 := bstep (se 1 (by rfl) ⟨217301, by rfl⟩ : syracuseStep 289735 = 434603) B434603
theorem B289755 : Blo 287828 289755 := bstep (se 1 (by rfl) ⟨217316, by rfl⟩ : syracuseStep 289755 = 434633) B434633
theorem B977939 : Blo 287828 977939 := bstep (se 1 (by rfl) ⟨733454, by rfl⟩ : syracuseStep 977939 = 1466909) B1466909
theorem B289831 : Blo 287828 289831 := bstep (se 1 (by rfl) ⟨217373, by rfl⟩ : syracuseStep 289831 = 434747) B434747
theorem B486479 : Blo 287828 486479 := bstep (se 1 (by rfl) ⟨364859, by rfl⟩ : syracuseStep 486479 = 729719) B729719
theorem B289871 : Blo 287828 289871 := bstep (se 1 (by rfl) ⟨217403, by rfl⟩ : syracuseStep 289871 = 434807) B434807
theorem B289887 : Blo 287828 289887 := bstep (se 1 (by rfl) ⟨217415, by rfl⟩ : syracuseStep 289887 = 434831) B434831
theorem B584801 : Blo 287828 584801 := bstep (se 2 (by rfl) ⟨219300, by rfl⟩ : syracuseStep 584801 = 438601) B438601
theorem B289915 : Blo 287828 289915 := bstep (se 1 (by rfl) ⟨217436, by rfl⟩ : syracuseStep 289915 = 434873) B434873
theorem B1043609 : Blo 287828 1043609 := bstep (se 2 (by rfl) ⟨391353, by rfl⟩ : syracuseStep 1043609 = 782707) B782707
theorem B650411 : Blo 287828 650411 := bstep (se 1 (by rfl) ⟨487808, by rfl⟩ : syracuseStep 650411 = 975617) B975617
theorem B1240235 : Blo 287828 1240235 := bstep (se 1 (by rfl) ⟨930176, by rfl⟩ : syracuseStep 1240235 = 1860353) B1860353
theorem B289967 : Blo 287828 289967 := bstep (se 1 (by rfl) ⟨217475, by rfl⟩ : syracuseStep 289967 = 434951) B434951
theorem B289991 : Blo 287828 289991 := bstep (se 1 (by rfl) ⟨217493, by rfl⟩ : syracuseStep 289991 = 434987) B434987
theorem B290011 : Blo 287828 290011 := bstep (se 1 (by rfl) ⟨217508, by rfl⟩ : syracuseStep 290011 = 435017) B435017
theorem B290087 : Blo 287828 290087 := bstep (se 1 (by rfl) ⟨217565, by rfl⟩ : syracuseStep 290087 = 435131) B435131
theorem B290127 : Blo 287828 290127 := bstep (se 1 (by rfl) ⟨217595, by rfl⟩ : syracuseStep 290127 = 435191) B435191
theorem B978263 : Blo 287828 978263 := bstep (se 1 (by rfl) ⟨733697, by rfl⟩ : syracuseStep 978263 = 1467395) B1467395
theorem B290143 : Blo 287828 290143 := bstep (se 1 (by rfl) ⟨217607, by rfl⟩ : syracuseStep 290143 = 435215) B435215
theorem B290171 : Blo 287828 290171 := bstep (se 1 (by rfl) ⟨217628, by rfl⟩ : syracuseStep 290171 = 435257) B435257
theorem B290223 : Blo 287828 290223 := bstep (se 1 (by rfl) ⟨217667, by rfl⟩ : syracuseStep 290223 = 435335) B435335
theorem B290247 : Blo 287828 290247 := bstep (se 1 (by rfl) ⟨217685, by rfl⟩ : syracuseStep 290247 = 435371) B435371
theorem B290267 : Blo 287828 290267 := bstep (se 1 (by rfl) ⟨217700, by rfl⟩ : syracuseStep 290267 = 435401) B435401
theorem B2190887 : Blo 287828 2190887 := bstep (se 1 (by rfl) ⟨1643165, by rfl⟩ : syracuseStep 2190887 = 3286331) B3286331
theorem B290343 : Blo 287828 290343 := bstep (se 1 (by rfl) ⟨217757, by rfl⟩ : syracuseStep 290343 = 435515) B435515
theorem B2485799 : Blo 287828 2485799 := bstep (se 1 (by rfl) ⟨1864349, by rfl⟩ : syracuseStep 2485799 = 3728699) B3728699
theorem B290383 : Blo 287828 290383 := bstep (se 1 (by rfl) ⟨217787, by rfl⟩ : syracuseStep 290383 = 435575) B435575
theorem B290399 : Blo 287828 290399 := bstep (se 1 (by rfl) ⟨217799, by rfl⟩ : syracuseStep 290399 = 435599) B435599
theorem B7892603 : Blo 287828 7892603 := bstep (se 1 (by rfl) ⟨5919452, by rfl⟩ : syracuseStep 7892603 = 11838905) B11838905
theorem B290427 : Blo 287828 290427 := bstep (se 1 (by rfl) ⟨217820, by rfl⟩ : syracuseStep 290427 = 435641) B435641
theorem B290479 : Blo 287828 290479 := bstep (se 1 (by rfl) ⟨217859, by rfl⟩ : syracuseStep 290479 = 435719) B435719
theorem B650951 : Blo 287828 650951 := bstep (se 1 (by rfl) ⟨488213, by rfl⟩ : syracuseStep 650951 = 976427) B976427
theorem B290503 : Blo 287828 290503 := bstep (se 1 (by rfl) ⟨217877, by rfl⟩ : syracuseStep 290503 = 435755) B435755
theorem B290523 : Blo 287828 290523 := bstep (se 1 (by rfl) ⟨217892, by rfl⟩ : syracuseStep 290523 = 435785) B435785
theorem B290599 : Blo 287828 290599 := bstep (se 1 (by rfl) ⟨217949, by rfl⟩ : syracuseStep 290599 = 435899) B435899
theorem B290639 : Blo 287828 290639 := bstep (se 1 (by rfl) ⟨217979, by rfl⟩ : syracuseStep 290639 = 435959) B435959
theorem B290655 : Blo 287828 290655 := bstep (se 1 (by rfl) ⟨217991, by rfl⟩ : syracuseStep 290655 = 435983) B435983
theorem B290683 : Blo 287828 290683 := bstep (se 1 (by rfl) ⟨218012, by rfl⟩ : syracuseStep 290683 = 436025) B436025
theorem B520111 : Blo 287828 520111 := bstep (se 1 (by rfl) ⟨390083, by rfl⟩ : syracuseStep 520111 = 780167) B780167
theorem B487343 : Blo 287828 487343 := bstep (se 1 (by rfl) ⟨365507, by rfl⟩ : syracuseStep 487343 = 731015) B731015
theorem B290735 : Blo 287828 290735 := bstep (se 1 (by rfl) ⟨218051, by rfl⟩ : syracuseStep 290735 = 436103) B436103
theorem B290759 : Blo 287828 290759 := bstep (se 1 (by rfl) ⟨218069, by rfl⟩ : syracuseStep 290759 = 436139) B436139
theorem B290779 : Blo 287828 290779 := bstep (se 1 (by rfl) ⟨218084, by rfl⟩ : syracuseStep 290779 = 436169) B436169
theorem B290855 : Blo 287828 290855 := bstep (se 1 (by rfl) ⟨218141, by rfl⟩ : syracuseStep 290855 = 436283) B436283
theorem B290895 : Blo 287828 290895 := bstep (se 1 (by rfl) ⟨218171, by rfl⟩ : syracuseStep 290895 = 436343) B436343
theorem B290911 : Blo 287828 290911 := bstep (se 1 (by rfl) ⟨218183, by rfl⟩ : syracuseStep 290911 = 436367) B436367
theorem B290939 : Blo 287828 290939 := bstep (se 1 (by rfl) ⟨218204, by rfl⟩ : syracuseStep 290939 = 436409) B436409
theorem B290991 : Blo 287828 290991 := bstep (se 1 (by rfl) ⟨218243, by rfl⟩ : syracuseStep 290991 = 436487) B436487
theorem B291015 : Blo 287828 291015 := bstep (se 1 (by rfl) ⟨218261, by rfl⟩ : syracuseStep 291015 = 436523) B436523
theorem B553159 : Blo 287828 553159 := bstep (se 1 (by rfl) ⟨414869, by rfl⟩ : syracuseStep 553159 = 829739) B829739
theorem B291035 : Blo 287828 291035 := bstep (se 1 (by rfl) ⟨218276, by rfl⟩ : syracuseStep 291035 = 436553) B436553
theorem B3141899 : Blo 287828 3141899 := bstep (se 1 (by rfl) ⟨2356424, by rfl⟩ : syracuseStep 3141899 = 4712849) B4712849
theorem B291111 : Blo 287828 291111 := bstep (se 1 (by rfl) ⟨218333, by rfl⟩ : syracuseStep 291111 = 436667) B436667
theorem B291151 : Blo 287828 291151 := bstep (se 1 (by rfl) ⟨218363, by rfl⟩ : syracuseStep 291151 = 436727) B436727
theorem B487775 : Blo 287828 487775 := bstep (se 1 (by rfl) ⟨365831, by rfl⟩ : syracuseStep 487775 = 731663) B731663
theorem B291167 : Blo 287828 291167 := bstep (se 1 (by rfl) ⟨218375, by rfl⟩ : syracuseStep 291167 = 436751) B436751
theorem B291195 : Blo 287828 291195 := bstep (se 1 (by rfl) ⟨218396, by rfl⟩ : syracuseStep 291195 = 436793) B436793
theorem B979343 : Blo 287828 979343 := bstep (se 1 (by rfl) ⟨734507, by rfl⟩ : syracuseStep 979343 = 1469015) B1469015
theorem B291247 : Blo 287828 291247 := bstep (se 1 (by rfl) ⟨218435, by rfl⟩ : syracuseStep 291247 = 436871) B436871
theorem B291271 : Blo 287828 291271 := bstep (se 1 (by rfl) ⟨218453, by rfl⟩ : syracuseStep 291271 = 436907) B436907
theorem B291291 : Blo 287828 291291 := bstep (se 1 (by rfl) ⟨218468, by rfl⟩ : syracuseStep 291291 = 436937) B436937
theorem B651815 : Blo 287828 651815 := bstep (se 1 (by rfl) ⟨488861, by rfl⟩ : syracuseStep 651815 = 977723) B977723
theorem B291367 : Blo 287828 291367 := bstep (se 1 (by rfl) ⟨218525, by rfl⟩ : syracuseStep 291367 = 437051) B437051
theorem B324175 : Blo 287828 324175 := bstep (se 1 (by rfl) ⟨243131, by rfl⟩ : syracuseStep 324175 = 486263) B486263
theorem B389711 : Blo 287828 389711 := bstep (se 1 (by rfl) ⟨292283, by rfl⟩ : syracuseStep 389711 = 584567) B584567
theorem B291407 : Blo 287828 291407 := bstep (se 1 (by rfl) ⟨218555, by rfl⟩ : syracuseStep 291407 = 437111) B437111
theorem B291423 : Blo 287828 291423 := bstep (se 1 (by rfl) ⟨218567, by rfl⟩ : syracuseStep 291423 = 437135) B437135
theorem B291451 : Blo 287828 291451 := bstep (se 1 (by rfl) ⟨218588, by rfl⟩ : syracuseStep 291451 = 437177) B437177
theorem B291503 : Blo 287828 291503 := bstep (se 1 (by rfl) ⟨218627, by rfl⟩ : syracuseStep 291503 = 437255) B437255
theorem B291527 : Blo 287828 291527 := bstep (se 1 (by rfl) ⟨218645, by rfl⟩ : syracuseStep 291527 = 437291) B437291
theorem B979667 : Blo 287828 979667 := bstep (se 1 (by rfl) ⟨734750, by rfl⟩ : syracuseStep 979667 = 1469501) B1469501
theorem B1864403 : Blo 287828 1864403 := bstep (se 1 (by rfl) ⟨1398302, by rfl⟩ : syracuseStep 1864403 = 2796605) B2796605
theorem B291547 : Blo 287828 291547 := bstep (se 1 (by rfl) ⟨218660, by rfl⟩ : syracuseStep 291547 = 437321) B437321
theorem B291623 : Blo 287828 291623 := bstep (se 1 (by rfl) ⟨218717, by rfl⟩ : syracuseStep 291623 = 437435) B437435
theorem B291663 : Blo 287828 291663 := bstep (se 1 (by rfl) ⟨218747, by rfl⟩ : syracuseStep 291663 = 437495) B437495
theorem B291679 : Blo 287828 291679 := bstep (se 1 (by rfl) ⟨218759, by rfl⟩ : syracuseStep 291679 = 437519) B437519
theorem B652139 : Blo 287828 652139 := bstep (se 1 (by rfl) ⟨489104, by rfl⟩ : syracuseStep 652139 = 978209) B978209
theorem B291707 : Blo 287828 291707 := bstep (se 1 (by rfl) ⟨218780, by rfl⟩ : syracuseStep 291707 = 437561) B437561
theorem B488335 : Blo 287828 488335 := bstep (se 1 (by rfl) ⟨366251, by rfl⟩ : syracuseStep 488335 = 732503) B732503
theorem B652193 : Blo 287828 652193 := bstep (se 2 (by rfl) ⟨244572, by rfl⟩ : syracuseStep 652193 = 489145) B489145
theorem B291759 : Blo 287828 291759 := bstep (se 1 (by rfl) ⟨218819, by rfl⟩ : syracuseStep 291759 = 437639) B437639
theorem B291783 : Blo 287828 291783 := bstep (se 1 (by rfl) ⟨218837, by rfl⟩ : syracuseStep 291783 = 437675) B437675
theorem B324571 : Blo 287828 324571 := bstep (se 1 (by rfl) ⟨243428, by rfl⟩ : syracuseStep 324571 = 486857) B486857
theorem B291803 : Blo 287828 291803 := bstep (se 1 (by rfl) ⟨218852, by rfl⟩ : syracuseStep 291803 = 437705) B437705
theorem B652535 : Blo 287828 652535 := bstep (se 1 (by rfl) ⟨489401, by rfl⟩ : syracuseStep 652535 = 978803) B978803
theorem B390505 : Blo 287828 390505 := bstep (se 2 (by rfl) ⟨146439, by rfl⟩ : syracuseStep 390505 = 292879) B292879
theorem B3536243 : Blo 287828 3536243 := bstep (se 1 (by rfl) ⟨2652182, by rfl⟩ : syracuseStep 3536243 = 5304365) B5304365
theorem B325039 : Blo 287828 325039 := bstep (se 1 (by rfl) ⟨243779, by rfl⟩ : syracuseStep 325039 = 487559) B487559
theorem B292295 : Blo 287828 292295 := bstep (se 1 (by rfl) ⟨219221, by rfl⟩ : syracuseStep 292295 = 438443) B438443
theorem B390619 : Blo 287828 390619 := bstep (se 1 (by rfl) ⟨292964, by rfl⟩ : syracuseStep 390619 = 585929) B585929
theorem B1242611 : Blo 287828 1242611 := bstep (se 1 (by rfl) ⟨931958, by rfl⟩ : syracuseStep 1242611 = 1863917) B1863917
theorem B489017 : Blo 287828 489017 := bstep (se 2 (by rfl) ⟨183381, by rfl⟩ : syracuseStep 489017 = 366763) B366763
theorem B2258579 : Blo 287828 2258579 := bstep (se 1 (by rfl) ⟨1693934, by rfl⟩ : syracuseStep 2258579 = 3387869) B3387869
theorem B653129 : Blo 287828 653129 := bstep (se 2 (by rfl) ⟨244923, by rfl⟩ : syracuseStep 653129 = 489847) B489847
theorem B325471 : Blo 287828 325471 := bstep (se 1 (by rfl) ⟨244103, by rfl⟩ : syracuseStep 325471 = 488207) B488207
theorem B980855 : Blo 287828 980855 := bstep (se 1 (by rfl) ⟨735641, by rfl⟩ : syracuseStep 980855 = 1471283) B1471283
theorem B1472417 : Blo 287828 1472417 := bstep (se 2 (by rfl) ⟨552156, by rfl⟩ : syracuseStep 1472417 = 1104313) B1104313
theorem B8353763 : Blo 287828 8353763 := bstep (se 1 (by rfl) ⟨6265322, by rfl⟩ : syracuseStep 8353763 = 12530645) B12530645
theorem B981071 : Blo 287828 981071 := bstep (se 1 (by rfl) ⟨735803, by rfl⟩ : syracuseStep 981071 = 1471607) B1471607
theorem B4028549 : Blo 287828 4028549 := bstep (se 4 (by rfl) ⟨377676, by rfl⟩ : syracuseStep 4028549 = 755353) B755353
theorem B1046681 : Blo 287828 1046681 := bstep (se 2 (by rfl) ⟨392505, by rfl⟩ : syracuseStep 1046681 = 785011) B785011
theorem B325831 : Blo 287828 325831 := bstep (se 1 (by rfl) ⟨244373, by rfl⟩ : syracuseStep 325831 = 488747) B488747
theorem B489719 : Blo 287828 489719 := bstep (se 1 (by rfl) ⟨367289, by rfl⟩ : syracuseStep 489719 = 734579) B734579
theorem B981449 : Blo 287828 981449 := bstep (se 2 (by rfl) ⟨368043, by rfl⟩ : syracuseStep 981449 = 736087) B736087
theorem B4749857 : Blo 287828 4749857 := bstep (se 2 (by rfl) ⟨1781196, by rfl⟩ : syracuseStep 4749857 = 3562393) B3562393
theorem B490063 : Blo 287828 490063 := bstep (se 1 (by rfl) ⟨367547, by rfl⟩ : syracuseStep 490063 = 735095) B735095
theorem B653921 : Blo 287828 653921 := bstep (se 2 (by rfl) ⟨245220, by rfl⟩ : syracuseStep 653921 = 490441) B490441
theorem B981719 : Blo 287828 981719 := bstep (se 1 (by rfl) ⟨736289, by rfl⟩ : syracuseStep 981719 = 1472579) B1472579
theorem B490313 : Blo 287828 490313 := bstep (se 2 (by rfl) ⟨183867, by rfl⟩ : syracuseStep 490313 = 367735) B367735
theorem B1145707 : Blo 287828 1145707 := bstep (se 1 (by rfl) ⟨859280, by rfl⟩ : syracuseStep 1145707 = 1718561) B1718561
theorem B981935 : Blo 287828 981935 := bstep (se 1 (by rfl) ⟨736451, by rfl⟩ : syracuseStep 981935 = 1472903) B1472903
theorem B785335 : Blo 287828 785335 := bstep (se 1 (by rfl) ⟨589001, by rfl⟩ : syracuseStep 785335 = 1178003) B1178003
theorem B654263 : Blo 287828 654263 := bstep (se 1 (by rfl) ⟨490697, by rfl⟩ : syracuseStep 654263 = 981395) B981395
theorem B621587 : Blo 287828 621587 := bstep (se 1 (by rfl) ⟨466190, by rfl⟩ : syracuseStep 621587 = 932381) B932381
theorem B326695 : Blo 287828 326695 := bstep (se 1 (by rfl) ⟨245021, by rfl⟩ : syracuseStep 326695 = 490043) B490043
theorem B1015031 : Blo 287828 1015031 := bstep (se 1 (by rfl) ⟨761273, by rfl⟩ : syracuseStep 1015031 = 1522547) B1522547
theorem B523513 : Blo 287828 523513 := bstep (se 2 (by rfl) ⟨196317, by rfl⟩ : syracuseStep 523513 = 392635) B392635
theorem B490745 : Blo 287828 490745 := bstep (se 2 (by rfl) ⟨184029, by rfl⟩ : syracuseStep 490745 = 368059) B368059
theorem B490927 : Blo 287828 490927 := bstep (se 1 (by rfl) ⟨368195, by rfl⟩ : syracuseStep 490927 = 736391) B736391
theorem B491015 : Blo 287828 491015 := bstep (se 1 (by rfl) ⟨368261, by rfl⟩ : syracuseStep 491015 = 736523) B736523
theorem B654857 : Blo 287828 654857 := bstep (se 2 (by rfl) ⟨245571, by rfl⟩ : syracuseStep 654857 = 491143) B491143
theorem B1768999 : Blo 287828 1768999 := bstep (se 1 (by rfl) ⟨1326749, by rfl⟩ : syracuseStep 1768999 = 2653499) B2653499
theorem B556583 : Blo 287828 556583 := bstep (se 1 (by rfl) ⟨417437, by rfl⟩ : syracuseStep 556583 = 834875) B834875
theorem B491359 : Blo 287828 491359 := bstep (se 1 (by rfl) ⟨368519, by rfl⟩ : syracuseStep 491359 = 737039) B737039
theorem B655199 : Blo 287828 655199 := bstep (se 1 (by rfl) ⟨491399, by rfl⟩ : syracuseStep 655199 = 982799) B982799
theorem B491447 : Blo 287828 491447 := bstep (se 1 (by rfl) ⟨368585, by rfl⟩ : syracuseStep 491447 = 737171) B737171
theorem B15728717 : Blo 287828 15728717 := bstep (se 3 (by rfl) ⟨2949134, by rfl⟩ : syracuseStep 15728717 = 5898269) B5898269
theorem B1245395 : Blo 287828 1245395 := bstep (se 1 (by rfl) ⟨934046, by rfl⟩ : syracuseStep 1245395 = 1868093) B1868093
theorem B328027 : Blo 287828 328027 := bstep (se 1 (by rfl) ⟨246020, by rfl⟩ : syracuseStep 328027 = 492041) B492041
theorem B328135 : Blo 287828 328135 := bstep (se 1 (by rfl) ⟨246101, by rfl⟩ : syracuseStep 328135 = 492203) B492203
theorem B492095 : Blo 287828 492095 := bstep (se 1 (by rfl) ⟨369071, by rfl⟩ : syracuseStep 492095 = 738143) B738143
theorem B656207 : Blo 287828 656207 := bstep (se 1 (by rfl) ⟨492155, by rfl⟩ : syracuseStep 656207 = 984311) B984311
theorem B525287 : Blo 287828 525287 := bstep (se 1 (by rfl) ⟨393965, by rfl⟩ : syracuseStep 525287 = 787931) B787931
theorem B656423 : Blo 287828 656423 := bstep (se 1 (by rfl) ⟨492317, by rfl⟩ : syracuseStep 656423 = 984635) B984635
theorem B787553 : Blo 287828 787553 := bstep (se 2 (by rfl) ⟨295332, by rfl⟩ : syracuseStep 787553 = 590665) B590665
theorem B656603 : Blo 287828 656603 := bstep (se 1 (by rfl) ⟨492452, by rfl⟩ : syracuseStep 656603 = 984905) B984905
theorem B4425047 : Blo 287828 4425047 := bstep (se 1 (by rfl) ⟨3318785, by rfl⟩ : syracuseStep 4425047 = 6637571) B6637571
theorem B1049965 : Blo 287828 1049965 := bstep (se 3 (by rfl) ⟨196868, by rfl⟩ : syracuseStep 1049965 = 393737) B393737
theorem B2786683 : Blo 287828 2786683 := bstep (se 1 (by rfl) ⟨2090012, by rfl⟩ : syracuseStep 2786683 = 4180025) B4180025
theorem B55248277 : Blo 287828 55248277 := bstep (se 6 (by rfl) ⟨1294881, by rfl⟩ : syracuseStep 55248277 = 2589763) B2589763
theorem B1181117 : Blo 287828 1181117 := bstep (se 3 (by rfl) ⟨221459, by rfl⟩ : syracuseStep 1181117 = 442919) B442919
theorem B5932601 : Blo 287828 5932601 := bstep (se 2 (by rfl) ⟨2224725, by rfl⟩ : syracuseStep 5932601 = 4449451) B4449451
theorem B3279041 : Blo 287828 3279041 := bstep (se 2 (by rfl) ⟨1229640, by rfl⟩ : syracuseStep 3279041 = 2459281) B2459281
theorem B1116413 : Blo 287828 1116413 := bstep (se 3 (by rfl) ⟨209327, by rfl⟩ : syracuseStep 1116413 = 418655) B418655
theorem B2689523 : Blo 287828 2689523 := bstep (se 1 (by rfl) ⟨2017142, by rfl⟩ : syracuseStep 2689523 = 4034285) B4034285
theorem B1477115 : Blo 287828 1477115 := bstep (se 1 (by rfl) ⟨1107836, by rfl⟩ : syracuseStep 1477115 = 2215673) B2215673
theorem B2460239 : Blo 287828 2460239 := bstep (se 1 (by rfl) ⟨1845179, by rfl⟩ : syracuseStep 2460239 = 3690359) B3690359
theorem B1182383 : Blo 287828 1182383 := bstep (se 1 (by rfl) ⟨886787, by rfl⟩ : syracuseStep 1182383 = 1773575) B1773575
theorem B2100599 : Blo 287828 2100599 := bstep (se 1 (by rfl) ⟨1575449, by rfl⟩ : syracuseStep 2100599 = 3150899) B3150899
theorem B1478225 : Blo 287828 1478225 := bstep (se 2 (by rfl) ⟨554334, by rfl⟩ : syracuseStep 1478225 = 1108669) B1108669
theorem B2199149 : Blo 287828 2199149 := bstep (se 3 (by rfl) ⟨412340, by rfl⟩ : syracuseStep 2199149 = 824681) B824681
theorem B3149725 : Blo 287828 3149725 := bstep (se 3 (by rfl) ⟨590573, by rfl⟩ : syracuseStep 3149725 = 1181147) B1181147
theorem B364495 : Blo 287828 364495 := bstep (se 1 (by rfl) ⟨273371, by rfl⟩ : syracuseStep 364495 = 546743) B546743
theorem B2101315 : Blo 287828 2101315 := bstep (se 1 (by rfl) ⟨1575986, by rfl⟩ : syracuseStep 2101315 = 3151973) B3151973
theorem B364763 : Blo 287828 364763 := bstep (se 1 (by rfl) ⟨273572, by rfl⟩ : syracuseStep 364763 = 547145) B547145
theorem B332143 : Blo 287828 332143 := bstep (se 1 (by rfl) ⟨249107, by rfl⟩ : syracuseStep 332143 = 498215) B498215
theorem B1479131 : Blo 287828 1479131 := bstep (se 1 (by rfl) ⟨1109348, by rfl⟩ : syracuseStep 1479131 = 2218697) B2218697
theorem B365239 : Blo 287828 365239 := bstep (se 1 (by rfl) ⟨273929, by rfl⟩ : syracuseStep 365239 = 547859) B547859
theorem B332591 : Blo 287828 332591 := bstep (se 1 (by rfl) ⟨249443, by rfl⟩ : syracuseStep 332591 = 498887) B498887
theorem B365467 : Blo 287828 365467 := bstep (se 1 (by rfl) ⟨274100, by rfl⟩ : syracuseStep 365467 = 548201) B548201
theorem B3871901 : Blo 287828 3871901 := bstep (se 3 (by rfl) ⟨725981, by rfl⟩ : syracuseStep 3871901 = 1451963) B1451963
theorem B693481 : Blo 287828 693481 := bstep (se 2 (by rfl) ⟨260055, by rfl⟩ : syracuseStep 693481 = 520111) B520111
theorem B922873 : Blo 287828 922873 := bstep (se 2 (by rfl) ⟨346077, by rfl⟩ : syracuseStep 922873 = 692155) B692155
theorem B1480031 : Blo 287828 1480031 := bstep (se 1 (by rfl) ⟨1110023, by rfl⟩ : syracuseStep 1480031 = 2220047) B2220047
theorem B1676837 : Blo 287828 1676837 := bstep (se 4 (by rfl) ⟨157203, by rfl⟩ : syracuseStep 1676837 = 314407) B314407
theorem B5936885 : Blo 287828 5936885 := bstep (se 5 (by rfl) ⟨278291, by rfl⟩ : syracuseStep 5936885 = 556583) B556583
theorem B366383 : Blo 287828 366383 := bstep (se 1 (by rfl) ⟨274787, by rfl⟩ : syracuseStep 366383 = 549575) B549575
theorem B431927 : Blo 287828 431927 := bstep (se 1 (by rfl) ⟨323945, by rfl⟩ : syracuseStep 431927 = 647891) B647891
theorem B432233 : Blo 287828 432233 := bstep (se 2 (by rfl) ⟨162087, by rfl⟩ : syracuseStep 432233 = 324175) B324175
theorem B432551 : Blo 287828 432551 := bstep (se 1 (by rfl) ⟨324413, by rfl⟩ : syracuseStep 432551 = 648827) B648827
theorem B432635 : Blo 287828 432635 := bstep (se 1 (by rfl) ⟨324476, by rfl⟩ : syracuseStep 432635 = 648953) B648953
theorem B432761 : Blo 287828 432761 := bstep (se 2 (by rfl) ⟨162285, by rfl⟩ : syracuseStep 432761 = 324571) B324571
theorem B2792069 : Blo 287828 2792069 := bstep (se 4 (by rfl) ⟨261756, by rfl⟩ : syracuseStep 2792069 = 523513) B523513
theorem B432815 : Blo 287828 432815 := bstep (se 1 (by rfl) ⟨324611, by rfl⟩ : syracuseStep 432815 = 649223) B649223
theorem B432863 : Blo 287828 432863 := bstep (se 1 (by rfl) ⟨324647, by rfl⟩ : syracuseStep 432863 = 649295) B649295
theorem B2530223 : Blo 287828 2530223 := bstep (se 1 (by rfl) ⟨1897667, by rfl⟩ : syracuseStep 2530223 = 3795335) B3795335
theorem B433127 : Blo 287828 433127 := bstep (se 1 (by rfl) ⟨324845, by rfl⟩ : syracuseStep 433127 = 649691) B649691
theorem B466139 : Blo 287828 466139 := bstep (se 1 (by rfl) ⟨349604, by rfl⟩ : syracuseStep 466139 = 699209) B699209
theorem B433385 : Blo 287828 433385 := bstep (se 2 (by rfl) ⟨162519, by rfl⟩ : syracuseStep 433385 = 325039) B325039
theorem B433439 : Blo 287828 433439 := bstep (se 1 (by rfl) ⟨325079, by rfl⟩ : syracuseStep 433439 = 650159) B650159
theorem B433607 : Blo 287828 433607 := bstep (se 1 (by rfl) ⟨325205, by rfl⟩ : syracuseStep 433607 = 650411) B650411
theorem B826823 : Blo 287828 826823 := bstep (se 1 (by rfl) ⟨620117, by rfl⟩ : syracuseStep 826823 = 1240235) B1240235
theorem B1383961 : Blo 287828 1383961 := bstep (se 2 (by rfl) ⟨518985, by rfl⟩ : syracuseStep 1383961 = 1037971) B1037971
theorem B990955 : Blo 287828 990955 := bstep (se 1 (by rfl) ⟨743216, by rfl⟩ : syracuseStep 990955 = 1486433) B1486433
theorem B433961 : Blo 287828 433961 := bstep (se 2 (by rfl) ⟨162735, by rfl⟩ : syracuseStep 433961 = 325471) B325471
theorem B433967 : Blo 287828 433967 := bstep (se 1 (by rfl) ⟨325475, by rfl⟩ : syracuseStep 433967 = 650951) B650951
theorem B434441 : Blo 287828 434441 := bstep (se 2 (by rfl) ⟨162915, by rfl⟩ : syracuseStep 434441 = 325831) B325831
theorem B434543 : Blo 287828 434543 := bstep (se 1 (by rfl) ⟨325907, by rfl⟩ : syracuseStep 434543 = 651815) B651815
theorem B1647175 : Blo 287828 1647175 := bstep (se 1 (by rfl) ⟨1235381, by rfl⟩ : syracuseStep 1647175 = 2470763) B2470763
theorem B434759 : Blo 287828 434759 := bstep (se 1 (by rfl) ⟨326069, by rfl⟩ : syracuseStep 434759 = 652139) B652139
theorem B434795 : Blo 287828 434795 := bstep (se 1 (by rfl) ⟨326096, by rfl⟩ : syracuseStep 434795 = 652193) B652193
theorem B435023 : Blo 287828 435023 := bstep (se 1 (by rfl) ⟨326267, by rfl⟩ : syracuseStep 435023 = 652535) B652535
theorem B828407 : Blo 287828 828407 := bstep (se 1 (by rfl) ⟨621305, by rfl⟩ : syracuseStep 828407 = 1242611) B1242611
theorem B730235 : Blo 287828 730235 := bstep (se 1 (by rfl) ⟨547676, by rfl⟩ : syracuseStep 730235 = 1095353) B1095353
theorem B730255 : Blo 287828 730255 := bstep (se 1 (by rfl) ⟨547691, by rfl⟩ : syracuseStep 730255 = 1095383) B1095383
theorem B435419 : Blo 287828 435419 := bstep (se 1 (by rfl) ⟨326564, by rfl⟩ : syracuseStep 435419 = 653129) B653129
theorem B435593 : Blo 287828 435593 := bstep (se 2 (by rfl) ⟨163347, by rfl⟩ : syracuseStep 435593 = 326695) B326695
theorem B730529 : Blo 287828 730529 := bstep (se 2 (by rfl) ⟨273948, by rfl⟩ : syracuseStep 730529 = 547897) B547897
theorem B697787 : Blo 287828 697787 := bstep (se 1 (by rfl) ⟨523340, by rfl⟩ : syracuseStep 697787 = 1046681) B1046681
theorem B435947 : Blo 287828 435947 := bstep (se 1 (by rfl) ⟨326960, by rfl⟩ : syracuseStep 435947 = 653921) B653921
theorem B4728739 : Blo 287828 4728739 := bstep (se 1 (by rfl) ⟨3546554, by rfl⟩ : syracuseStep 4728739 = 7093109) B7093109
theorem B436175 : Blo 287828 436175 := bstep (se 1 (by rfl) ⟨327131, by rfl⟩ : syracuseStep 436175 = 654263) B654263
theorem B1681661 : Blo 287828 1681661 := bstep (se 3 (by rfl) ⟨315311, by rfl⟩ : syracuseStep 1681661 = 630623) B630623
theorem B829693 : Blo 287828 829693 := bstep (se 3 (by rfl) ⟨155567, by rfl⟩ : syracuseStep 829693 = 311135) B311135
theorem B2369801 : Blo 287828 2369801 := bstep (se 2 (by rfl) ⟨888675, by rfl⟩ : syracuseStep 2369801 = 1777351) B1777351
theorem B436571 : Blo 287828 436571 := bstep (se 1 (by rfl) ⟨327428, by rfl⟩ : syracuseStep 436571 = 654857) B654857
theorem B15935849 : Blo 287828 15935849 := bstep (se 2 (by rfl) ⟨5975943, by rfl⟩ : syracuseStep 15935849 = 11951887) B11951887
theorem B436799 : Blo 287828 436799 := bstep (se 1 (by rfl) ⟨327599, by rfl⟩ : syracuseStep 436799 = 655199) B655199
theorem B436919 : Blo 287828 436919 := bstep (se 1 (by rfl) ⟨327689, by rfl⟩ : syracuseStep 436919 = 655379) B655379
theorem B1845949 : Blo 287828 1845949 := bstep (se 3 (by rfl) ⟨346115, by rfl⟩ : syracuseStep 1845949 = 692231) B692231
theorem B437147 : Blo 287828 437147 := bstep (se 1 (by rfl) ⟨327860, by rfl⟩ : syracuseStep 437147 = 655721) B655721
theorem B732199 : Blo 287828 732199 := bstep (se 1 (by rfl) ⟨549149, by rfl⟩ : syracuseStep 732199 = 1098299) B1098299
theorem B437543 : Blo 287828 437543 := bstep (se 1 (by rfl) ⟨328157, by rfl⟩ : syracuseStep 437543 = 656315) B656315
theorem B437627 : Blo 287828 437627 := bstep (se 1 (by rfl) ⟨328220, by rfl⟩ : syracuseStep 437627 = 656441) B656441
theorem B732665 : Blo 287828 732665 := bstep (se 2 (by rfl) ⟨274749, by rfl⟩ : syracuseStep 732665 = 549499) B549499
theorem B830969 : Blo 287828 830969 := bstep (se 2 (by rfl) ⟨311613, by rfl⟩ : syracuseStep 830969 = 623227) B623227
theorem B1093135 : Blo 287828 1093135 := bstep (se 1 (by rfl) ⟨819851, by rfl⟩ : syracuseStep 1093135 = 1639703) B1639703
theorem B1388267 : Blo 287828 1388267 := bstep (se 1 (by rfl) ⟨1041200, by rfl⟩ : syracuseStep 1388267 = 2082401) B2082401
theorem B4960115 : Blo 287828 4960115 := bstep (se 1 (by rfl) ⟨3720086, by rfl⟩ : syracuseStep 4960115 = 7440173) B7440173
theorem B26619799 : Blo 287828 26619799 := bstep (se 1 (by rfl) ⟨19964849, by rfl⟩ : syracuseStep 26619799 = 39929699) B39929699
theorem B733313 : Blo 287828 733313 := bstep (se 2 (by rfl) ⟨274992, by rfl⟩ : syracuseStep 733313 = 549985) B549985
theorem B733607 : Blo 287828 733607 := bstep (se 1 (by rfl) ⟨550205, by rfl⟩ : syracuseStep 733607 = 1100411) B1100411
theorem B733769 : Blo 287828 733769 := bstep (se 2 (by rfl) ⟨275163, by rfl⟩ : syracuseStep 733769 = 550327) B550327
theorem B734123 : Blo 287828 734123 := bstep (se 1 (by rfl) ⟨550592, by rfl⟩ : syracuseStep 734123 = 1101185) B1101185
theorem B930791 : Blo 287828 930791 := bstep (se 1 (by rfl) ⟨698093, by rfl⟩ : syracuseStep 930791 = 1396187) B1396187
theorem B734305 : Blo 287828 734305 := bstep (se 2 (by rfl) ⟨275364, by rfl⟩ : syracuseStep 734305 = 550729) B550729
theorem B735257 : Blo 287828 735257 := bstep (se 2 (by rfl) ⟨275721, by rfl⟩ : syracuseStep 735257 = 551443) B551443
theorem B1390727 : Blo 287828 1390727 := bstep (se 1 (by rfl) ⟨1043045, by rfl⟩ : syracuseStep 1390727 = 2086091) B2086091
theorem B735713 : Blo 287828 735713 := bstep (se 2 (by rfl) ⟨275892, by rfl⟩ : syracuseStep 735713 = 551785) B551785
theorem B735763 : Blo 287828 735763 := bstep (se 1 (by rfl) ⟨551822, by rfl⟩ : syracuseStep 735763 = 1103645) B1103645
theorem B6110437 : Blo 287828 6110437 := bstep (se 4 (by rfl) ⟨572853, by rfl⟩ : syracuseStep 6110437 = 1145707) B1145707
theorem B2768195 : Blo 287828 2768195 := bstep (se 1 (by rfl) ⟨2076146, by rfl⟩ : syracuseStep 2768195 = 4152293) B4152293
theorem B2407747 : Blo 287828 2407747 := bstep (se 1 (by rfl) ⟨1805810, by rfl⟩ : syracuseStep 2407747 = 3611621) B3611621
theorem B1097297 : Blo 287828 1097297 := bstep (se 2 (by rfl) ⟨411486, by rfl⟩ : syracuseStep 1097297 = 822973) B822973
theorem B310879 : Blo 287828 310879 := bstep (se 1 (by rfl) ⟨233159, by rfl⟩ : syracuseStep 310879 = 466319) B466319
theorem B2801411 : Blo 287828 2801411 := bstep (se 1 (by rfl) ⟨2101058, by rfl⟩ : syracuseStep 2801411 = 4202117) B4202117
theorem B737545 : Blo 287828 737545 := bstep (se 2 (by rfl) ⟨276579, by rfl⟩ : syracuseStep 737545 = 553159) B553159
theorem B22921751 : Blo 287828 22921751 := bstep (se 1 (by rfl) ⟨17191313, by rfl⟩ : syracuseStep 22921751 = 34382627) B34382627
theorem B1458809 : Blo 287828 1458809 := bstep (se 2 (by rfl) ⟨547053, by rfl⟩ : syracuseStep 1458809 = 1094107) B1094107
theorem B1098967 : Blo 287828 1098967 := bstep (se 1 (by rfl) ⟨824225, by rfl⟩ : syracuseStep 1098967 = 1648451) B1648451
theorem B836857 : Blo 287828 836857 := bstep (se 2 (by rfl) ⟨313821, by rfl⟩ : syracuseStep 836857 = 627643) B627643
theorem B2213243 : Blo 287828 2213243 := bstep (se 1 (by rfl) ⟨1659932, by rfl⟩ : syracuseStep 2213243 = 3319865) B3319865
theorem B1099271 : Blo 287828 1099271 := bstep (se 1 (by rfl) ⟨824453, by rfl⟩ : syracuseStep 1099271 = 1648907) B1648907
theorem B1099727 : Blo 287828 1099727 := bstep (se 1 (by rfl) ⟨824795, by rfl⟩ : syracuseStep 1099727 = 1649591) B1649591
theorem B1099757 : Blo 287828 1099757 := bstep (se 3 (by rfl) ⟨206204, by rfl⟩ : syracuseStep 1099757 = 412409) B412409
theorem B379175 : Blo 287828 379175 := bstep (se 1 (by rfl) ⟨284381, by rfl⟩ : syracuseStep 379175 = 568763) B568763
theorem B1460591 : Blo 287828 1460591 := bstep (se 1 (by rfl) ⟨1095443, by rfl⟩ : syracuseStep 1460591 = 2190887) B2190887
theorem B1657199 : Blo 287828 1657199 := bstep (se 1 (by rfl) ⟨1242899, by rfl⟩ : syracuseStep 1657199 = 2485799) B2485799
theorem B5261735 : Blo 287828 5261735 := bstep (se 1 (by rfl) ⟨3946301, by rfl⟩ : syracuseStep 5261735 = 7892603) B7892603
theorem B1100243 : Blo 287828 1100243 := bstep (se 1 (by rfl) ⟨825182, by rfl⟩ : syracuseStep 1100243 = 1650365) B1650365
theorem B1100699 : Blo 287828 1100699 := bstep (se 1 (by rfl) ⟨825524, by rfl⟩ : syracuseStep 1100699 = 1651049) B1651049
theorem B1756883 : Blo 287828 1756883 := bstep (se 1 (by rfl) ⟨1317662, by rfl⟩ : syracuseStep 1756883 = 2635325) B2635325
theorem B1232921 : Blo 287828 1232921 := bstep (se 2 (by rfl) ⟨462345, by rfl⟩ : syracuseStep 1232921 = 924691) B924691
theorem B1101883 : Blo 287828 1101883 := bstep (se 1 (by rfl) ⟨826412, by rfl⟩ : syracuseStep 1101883 = 1652825) B1652825
theorem B3166571 : Blo 287828 3166571 := bstep (se 1 (by rfl) ⟨2374928, by rfl⟩ : syracuseStep 3166571 = 4749857) B4749857
theorem B1102187 : Blo 287828 1102187 := bstep (se 1 (by rfl) ⟨826640, by rfl⟩ : syracuseStep 1102187 = 1653281) B1653281
theorem B1102355 : Blo 287828 1102355 := bstep (se 1 (by rfl) ⟨826766, by rfl⟩ : syracuseStep 1102355 = 1653533) B1653533
theorem B414391 : Blo 287828 414391 := bstep (se 1 (by rfl) ⟨310793, by rfl⟩ : syracuseStep 414391 = 621587) B621587
theorem B676687 : Blo 287828 676687 := bstep (se 1 (by rfl) ⟨507515, by rfl⟩ : syracuseStep 676687 = 1015031) B1015031
theorem B4674509 : Blo 287828 4674509 := bstep (se 3 (by rfl) ⟨876470, by rfl⟩ : syracuseStep 4674509 = 1752941) B1752941
theorem B2119115 : Blo 287828 2119115 := bstep (se 1 (by rfl) ⟨1589336, by rfl⟩ : syracuseStep 2119115 = 3178673) B3178673
theorem B1463993 : Blo 287828 1463993 := bstep (se 2 (by rfl) ⟨548997, by rfl⟩ : syracuseStep 1463993 = 1097995) B1097995
theorem B1234871 : Blo 287828 1234871 := bstep (se 1 (by rfl) ⟨926153, by rfl⟩ : syracuseStep 1234871 = 1852307) B1852307
theorem B2578405 : Blo 287828 2578405 := bstep (se 4 (by rfl) ⟨241725, by rfl⟩ : syracuseStep 2578405 = 483451) B483451
theorem B2086991 : Blo 287828 2086991 := bstep (se 1 (by rfl) ⟨1565243, by rfl⟩ : syracuseStep 2086991 = 3130487) B3130487
theorem B1235519 : Blo 287828 1235519 := bstep (se 1 (by rfl) ⟨926639, by rfl⟩ : syracuseStep 1235519 = 1853279) B1853279
theorem B1039229 : Blo 287828 1039229 := bstep (se 3 (by rfl) ⟨194855, by rfl⟩ : syracuseStep 1039229 = 389711) B389711
theorem B1105271 : Blo 287828 1105271 := bstep (se 1 (by rfl) ⟨828953, by rfl⟩ : syracuseStep 1105271 = 1657907) B1657907
theorem B974267 : Blo 287828 974267 := bstep (se 1 (by rfl) ⟨730700, by rfl⟩ : syracuseStep 974267 = 1461401) B1461401
theorem B548345 : Blo 287828 548345 := bstep (se 2 (by rfl) ⟨205629, by rfl⟩ : syracuseStep 548345 = 411259) B411259
theorem B1465937 : Blo 287828 1465937 := bstep (se 2 (by rfl) ⟨549726, by rfl⟩ : syracuseStep 1465937 = 1099453) B1099453
theorem B1171207 : Blo 287828 1171207 := bstep (se 1 (by rfl) ⟨878405, by rfl⟩ : syracuseStep 1171207 = 1756811) B1756811
theorem B6283183 : Blo 287828 6283183 := bstep (se 1 (by rfl) ⟨4712387, by rfl⟩ : syracuseStep 6283183 = 9424775) B9424775
theorem B614881 : Blo 287828 614881 := bstep (se 2 (by rfl) ⟨230580, by rfl⟩ : syracuseStep 614881 = 461161) B461161
theorem B647675 : Blo 287828 647675 := bstep (se 1 (by rfl) ⟨485756, by rfl⟩ : syracuseStep 647675 = 971513) B971513
theorem B2777611 : Blo 287828 2777611 := bstep (se 1 (by rfl) ⟨2083208, by rfl⟩ : syracuseStep 2777611 = 4166417) B4166417
theorem B778825 : Blo 287828 778825 := bstep (se 2 (by rfl) ⟨292059, by rfl⟩ : syracuseStep 778825 = 584119) B584119
theorem B647801 : Blo 287828 647801 := bstep (se 2 (by rfl) ⟨242925, by rfl⟩ : syracuseStep 647801 = 485851) B485851
theorem B647855 : Blo 287828 647855 := bstep (se 1 (by rfl) ⟨485891, by rfl⟩ : syracuseStep 647855 = 971783) B971783
theorem B647927 : Blo 287828 647927 := bstep (se 1 (by rfl) ⟨485945, by rfl⟩ : syracuseStep 647927 = 971891) B971891
theorem B648107 : Blo 287828 648107 := bstep (se 1 (by rfl) ⟨486080, by rfl⟩ : syracuseStep 648107 = 972161) B972161
theorem B549803 : Blo 287828 549803 := bstep (se 1 (by rfl) ⟨412352, by rfl⟩ : syracuseStep 549803 = 824705) B824705
theorem B1237979 : Blo 287828 1237979 := bstep (se 1 (by rfl) ⟨928484, by rfl⟩ : syracuseStep 1237979 = 1856969) B1856969
theorem B779453 : Blo 287828 779453 := bstep (se 3 (by rfl) ⟨146147, by rfl⟩ : syracuseStep 779453 = 292295) B292295
theorem B288031 : Blo 287828 288031 := bstep (se 1 (by rfl) ⟨216023, by rfl⟩ : syracuseStep 288031 = 432047) B432047
theorem B288091 : Blo 287828 288091 := bstep (se 1 (by rfl) ⟨216068, by rfl⟩ : syracuseStep 288091 = 432137) B432137
theorem B288111 : Blo 287828 288111 := bstep (se 1 (by rfl) ⟨216083, by rfl⟩ : syracuseStep 288111 = 432167) B432167
theorem B288167 : Blo 287828 288167 := bstep (se 1 (by rfl) ⟨216125, by rfl⟩ : syracuseStep 288167 = 432251) B432251
theorem B648647 : Blo 287828 648647 := bstep (se 1 (by rfl) ⟨486485, by rfl⟩ : syracuseStep 648647 = 972971) B972971
theorem B288251 : Blo 287828 288251 := bstep (se 1 (by rfl) ⟨216188, by rfl⟩ : syracuseStep 288251 = 432377) B432377
theorem B1238561 : Blo 287828 1238561 := bstep (se 2 (by rfl) ⟨464460, by rfl⟩ : syracuseStep 1238561 = 928921) B928921
theorem B288319 : Blo 287828 288319 := bstep (se 1 (by rfl) ⟨216239, by rfl⟩ : syracuseStep 288319 = 432479) B432479
theorem B288327 : Blo 287828 288327 := bstep (se 1 (by rfl) ⟨216245, by rfl⟩ : syracuseStep 288327 = 432491) B432491
theorem B288479 : Blo 287828 288479 := bstep (se 1 (by rfl) ⟨216359, by rfl⟩ : syracuseStep 288479 = 432719) B432719
theorem B649007 : Blo 287828 649007 := bstep (se 1 (by rfl) ⟨486755, by rfl⟩ : syracuseStep 649007 = 973511) B973511
theorem B288559 : Blo 287828 288559 := bstep (se 1 (by rfl) ⟨216419, by rfl⟩ : syracuseStep 288559 = 432839) B432839
theorem B288667 : Blo 287828 288667 := bstep (se 1 (by rfl) ⟨216500, by rfl⟩ : syracuseStep 288667 = 433001) B433001
theorem B288719 : Blo 287828 288719 := bstep (se 1 (by rfl) ⟨216539, by rfl⟩ : syracuseStep 288719 = 433079) B433079
theorem B1468367 : Blo 287828 1468367 := bstep (se 1 (by rfl) ⟨1101275, by rfl⟩ : syracuseStep 1468367 = 2202551) B2202551
theorem B288743 : Blo 287828 288743 := bstep (se 1 (by rfl) ⟨216557, by rfl⟩ : syracuseStep 288743 = 433115) B433115
theorem B3827897 : Blo 287828 3827897 := bstep (se 2 (by rfl) ⟨1435461, by rfl⟩ : syracuseStep 3827897 = 2870923) B2870923
theorem B289055 : Blo 287828 289055 := bstep (se 1 (by rfl) ⟨216791, by rfl⟩ : syracuseStep 289055 = 433583) B433583
theorem B3729725 : Blo 287828 3729725 := bstep (se 3 (by rfl) ⟨699323, by rfl⟩ : syracuseStep 3729725 = 1398647) B1398647
theorem B485723 : Blo 287828 485723 := bstep (se 1 (by rfl) ⟨364292, by rfl⟩ : syracuseStep 485723 = 728585) B728585
theorem B289115 : Blo 287828 289115 := bstep (se 1 (by rfl) ⟨216836, by rfl⟩ : syracuseStep 289115 = 433673) B433673
theorem B485743 : Blo 287828 485743 := bstep (se 1 (by rfl) ⟨364307, by rfl⟩ : syracuseStep 485743 = 728615) B728615
theorem B649583 : Blo 287828 649583 := bstep (se 1 (by rfl) ⟨487187, by rfl⟩ : syracuseStep 649583 = 974375) B974375
theorem B289135 : Blo 287828 289135 := bstep (se 1 (by rfl) ⟨216851, by rfl⟩ : syracuseStep 289135 = 433703) B433703
theorem B616871 : Blo 287828 616871 := bstep (se 1 (by rfl) ⟨462653, by rfl⟩ : syracuseStep 616871 = 925307) B925307
theorem B289191 : Blo 287828 289191 := bstep (se 1 (by rfl) ⟨216893, by rfl⟩ : syracuseStep 289191 = 433787) B433787
theorem B649655 : Blo 287828 649655 := bstep (se 1 (by rfl) ⟨487241, by rfl⟩ : syracuseStep 649655 = 974483) B974483
theorem B289275 : Blo 287828 289275 := bstep (se 1 (by rfl) ⟨216956, by rfl⟩ : syracuseStep 289275 = 433913) B433913
theorem B12479021 : Blo 287828 12479021 := bstep (se 3 (by rfl) ⟨2339816, by rfl⟩ : syracuseStep 12479021 = 4679633) B4679633
theorem B289343 : Blo 287828 289343 := bstep (se 1 (by rfl) ⟨217007, by rfl⟩ : syracuseStep 289343 = 434015) B434015
theorem B485959 : Blo 287828 485959 := bstep (se 1 (by rfl) ⟨364469, by rfl⟩ : syracuseStep 485959 = 728939) B728939
theorem B649799 : Blo 287828 649799 := bstep (se 1 (by rfl) ⟨487349, by rfl⟩ : syracuseStep 649799 = 974699) B974699
theorem B289351 : Blo 287828 289351 := bstep (se 1 (by rfl) ⟨217013, by rfl⟩ : syracuseStep 289351 = 434027) B434027
theorem B649835 : Blo 287828 649835 := bstep (se 1 (by rfl) ⟨487376, by rfl⟩ : syracuseStep 649835 = 974753) B974753
theorem B289503 : Blo 287828 289503 := bstep (se 1 (by rfl) ⟨217127, by rfl⟩ : syracuseStep 289503 = 434255) B434255
theorem B289583 : Blo 287828 289583 := bstep (se 1 (by rfl) ⟨217187, by rfl⟩ : syracuseStep 289583 = 434375) B434375
theorem B289691 : Blo 287828 289691 := bstep (se 1 (by rfl) ⟨217268, by rfl⟩ : syracuseStep 289691 = 434537) B434537
theorem B1469339 : Blo 287828 1469339 := bstep (se 1 (by rfl) ⟨1102004, by rfl⟩ : syracuseStep 1469339 = 2204009) B2204009
theorem B420763 : Blo 287828 420763 := bstep (se 1 (by rfl) ⟨315572, by rfl⟩ : syracuseStep 420763 = 631145) B631145
theorem B289743 : Blo 287828 289743 := bstep (se 1 (by rfl) ⟨217307, by rfl⟩ : syracuseStep 289743 = 434615) B434615
theorem B289767 : Blo 287828 289767 := bstep (se 1 (by rfl) ⟨217325, by rfl⟩ : syracuseStep 289767 = 434651) B434651
theorem B486391 : Blo 287828 486391 := bstep (se 1 (by rfl) ⟨364793, by rfl⟩ : syracuseStep 486391 = 729587) B729587
theorem B650231 : Blo 287828 650231 := bstep (se 1 (by rfl) ⟨487673, by rfl⟩ : syracuseStep 650231 = 975347) B975347
theorem B10742797 : Blo 287828 10742797 := bstep (se 3 (by rfl) ⟨2014274, by rfl⟩ : syracuseStep 10742797 = 4028549) B4028549
theorem B617615 : Blo 287828 617615 := bstep (se 1 (by rfl) ⟨463211, by rfl⟩ : syracuseStep 617615 = 926423) B926423
theorem B1568011 : Blo 287828 1568011 := bstep (se 1 (by rfl) ⟨1176008, by rfl⟩ : syracuseStep 1568011 = 2352017) B2352017
theorem B290079 : Blo 287828 290079 := bstep (se 1 (by rfl) ⟨217559, by rfl⟩ : syracuseStep 290079 = 435119) B435119
theorem B486695 : Blo 287828 486695 := bstep (se 1 (by rfl) ⟨365021, by rfl⟩ : syracuseStep 486695 = 730043) B730043
theorem B290139 : Blo 287828 290139 := bstep (se 1 (by rfl) ⟨217604, by rfl⟩ : syracuseStep 290139 = 435209) B435209
theorem B650591 : Blo 287828 650591 := bstep (se 1 (by rfl) ⟨487943, by rfl⟩ : syracuseStep 650591 = 975887) B975887
theorem B290159 : Blo 287828 290159 := bstep (se 1 (by rfl) ⟨217619, by rfl⟩ : syracuseStep 290159 = 435239) B435239
theorem B1469825 : Blo 287828 1469825 := bstep (se 2 (by rfl) ⟨551184, by rfl⟩ : syracuseStep 1469825 = 1102369) B1102369
theorem B290215 : Blo 287828 290215 := bstep (se 1 (by rfl) ⟨217661, by rfl⟩ : syracuseStep 290215 = 435323) B435323
theorem B978425 : Blo 287828 978425 := bstep (se 2 (by rfl) ⟨366909, by rfl⟩ : syracuseStep 978425 = 733819) B733819
theorem B290299 : Blo 287828 290299 := bstep (se 1 (by rfl) ⟨217724, by rfl⟩ : syracuseStep 290299 = 435449) B435449
theorem B367586819 : Blo 287828 367586819 := bstep (se 1 (by rfl) ⟨275690114, by rfl⟩ : syracuseStep 367586819 = 551380229) B551380229
theorem B290367 : Blo 287828 290367 := bstep (se 1 (by rfl) ⟨217775, by rfl⟩ : syracuseStep 290367 = 435551) B435551
theorem B290375 : Blo 287828 290375 := bstep (se 1 (by rfl) ⟨217781, by rfl⟩ : syracuseStep 290375 = 435563) B435563
theorem B618067 : Blo 287828 618067 := bstep (se 1 (by rfl) ⟨463550, by rfl⟩ : syracuseStep 618067 = 927101) B927101
theorem B290527 : Blo 287828 290527 := bstep (se 1 (by rfl) ⟨217895, by rfl⟩ : syracuseStep 290527 = 435791) B435791
theorem B487147 : Blo 287828 487147 := bstep (se 1 (by rfl) ⟨365360, by rfl⟩ : syracuseStep 487147 = 730721) B730721
theorem B650987 : Blo 287828 650987 := bstep (se 1 (by rfl) ⟨488240, by rfl⟩ : syracuseStep 650987 = 976481) B976481
theorem B978695 : Blo 287828 978695 := bstep (se 1 (by rfl) ⟨734021, by rfl⟩ : syracuseStep 978695 = 1468043) B1468043
theorem B290607 : Blo 287828 290607 := bstep (se 1 (by rfl) ⟨217955, by rfl⟩ : syracuseStep 290607 = 435911) B435911
theorem B23949107 : Blo 287828 23949107 := bstep (se 1 (by rfl) ⟨17961830, by rfl⟩ : syracuseStep 23949107 = 35923661) B35923661
theorem B978749 : Blo 287828 978749 := bstep (se 3 (by rfl) ⟨183515, by rfl⟩ : syracuseStep 978749 = 367031) B367031
theorem B651113 : Blo 287828 651113 := bstep (se 2 (by rfl) ⟨244167, by rfl⟩ : syracuseStep 651113 = 488335) B488335
theorem B290715 : Blo 287828 290715 := bstep (se 1 (by rfl) ⟨218036, by rfl⟩ : syracuseStep 290715 = 436073) B436073
theorem B290767 : Blo 287828 290767 := bstep (se 1 (by rfl) ⟨218075, by rfl⟩ : syracuseStep 290767 = 436151) B436151
theorem B290791 : Blo 287828 290791 := bstep (se 1 (by rfl) ⟨218093, by rfl⟩ : syracuseStep 290791 = 436187) B436187
theorem B1470473 : Blo 287828 1470473 := bstep (se 2 (by rfl) ⟨551427, by rfl⟩ : syracuseStep 1470473 = 1102855) B1102855
theorem B1470635 : Blo 287828 1470635 := bstep (se 1 (by rfl) ⟨1102976, by rfl⟩ : syracuseStep 1470635 = 2205953) B2205953
theorem B3567887 : Blo 287828 3567887 := bstep (se 1 (by rfl) ⟨2675915, by rfl⟩ : syracuseStep 3567887 = 5351831) B5351831
theorem B291103 : Blo 287828 291103 := bstep (se 1 (by rfl) ⟨218327, by rfl⟩ : syracuseStep 291103 = 436655) B436655
theorem B291163 : Blo 287828 291163 := bstep (se 1 (by rfl) ⟨218372, by rfl⟩ : syracuseStep 291163 = 436745) B436745
theorem B1864043 : Blo 287828 1864043 := bstep (se 1 (by rfl) ⟨1398032, by rfl⟩ : syracuseStep 1864043 = 2796065) B2796065
theorem B291183 : Blo 287828 291183 := bstep (se 1 (by rfl) ⟨218387, by rfl⟩ : syracuseStep 291183 = 436775) B436775
theorem B291239 : Blo 287828 291239 := bstep (se 1 (by rfl) ⟨218429, by rfl⟩ : syracuseStep 291239 = 436859) B436859
theorem B520673 : Blo 287828 520673 := bstep (se 2 (by rfl) ⟨195252, by rfl⟩ : syracuseStep 520673 = 390505) B390505
theorem B291323 : Blo 287828 291323 := bstep (se 1 (by rfl) ⟨218492, by rfl⟩ : syracuseStep 291323 = 436985) B436985
theorem B63336977 : Blo 287828 63336977 := bstep (se 2 (by rfl) ⟨23751366, by rfl⟩ : syracuseStep 63336977 = 47502733) B47502733
theorem B291391 : Blo 287828 291391 := bstep (se 1 (by rfl) ⟨218543, by rfl⟩ : syracuseStep 291391 = 437087) B437087
theorem B291399 : Blo 287828 291399 := bstep (se 1 (by rfl) ⟨218549, by rfl⟩ : syracuseStep 291399 = 437099) B437099
theorem B520825 : Blo 287828 520825 := bstep (se 2 (by rfl) ⟨195309, by rfl⟩ : syracuseStep 520825 = 390619) B390619
theorem B1471121 : Blo 287828 1471121 := bstep (se 2 (by rfl) ⟨551670, by rfl⟩ : syracuseStep 1471121 = 1103341) B1103341
theorem B488119 : Blo 287828 488119 := bstep (se 1 (by rfl) ⟨366089, by rfl⟩ : syracuseStep 488119 = 732179) B732179
theorem B651959 : Blo 287828 651959 := bstep (se 1 (by rfl) ⟨488969, by rfl⟩ : syracuseStep 651959 = 977939) B977939
theorem B324319 : Blo 287828 324319 := bstep (se 1 (by rfl) ⟨243239, by rfl⟩ : syracuseStep 324319 = 486479) B486479
theorem B291551 : Blo 287828 291551 := bstep (se 1 (by rfl) ⟨218663, by rfl⟩ : syracuseStep 291551 = 437327) B437327
theorem B389867 : Blo 287828 389867 := bstep (se 1 (by rfl) ⟨292400, by rfl⟩ : syracuseStep 389867 = 584801) B584801
theorem B619255 : Blo 287828 619255 := bstep (se 1 (by rfl) ⟨464441, by rfl⟩ : syracuseStep 619255 = 928883) B928883
theorem B291631 : Blo 287828 291631 := bstep (se 1 (by rfl) ⟨218723, by rfl⟩ : syracuseStep 291631 = 437447) B437447
theorem B652175 : Blo 287828 652175 := bstep (se 1 (by rfl) ⟨489131, by rfl⟩ : syracuseStep 652175 = 978263) B978263
theorem B291739 : Blo 287828 291739 := bstep (se 1 (by rfl) ⟨218804, by rfl⟩ : syracuseStep 291739 = 437609) B437609
theorem B291791 : Blo 287828 291791 := bstep (se 1 (by rfl) ⟨218843, by rfl⟩ : syracuseStep 291791 = 437687) B437687
theorem B488423 : Blo 287828 488423 := bstep (se 1 (by rfl) ⟨366317, by rfl⟩ : syracuseStep 488423 = 732635) B732635
theorem B291815 : Blo 287828 291815 := bstep (se 1 (by rfl) ⟨218861, by rfl⟩ : syracuseStep 291815 = 437723) B437723
theorem B1995923 : Blo 287828 1995923 := bstep (se 1 (by rfl) ⟨1496942, by rfl⟩ : syracuseStep 1995923 = 2993885) B2993885
theorem B2782457 : Blo 287828 2782457 := bstep (se 2 (by rfl) ⟨1043421, by rfl⟩ : syracuseStep 2782457 = 2086843) B2086843
theorem B324895 : Blo 287828 324895 := bstep (se 1 (by rfl) ⟨243671, by rfl⟩ : syracuseStep 324895 = 487343) B487343
theorem B619913 : Blo 287828 619913 := bstep (se 2 (by rfl) ⟨232467, by rfl⟩ : syracuseStep 619913 = 464935) B464935
theorem B2094599 : Blo 287828 2094599 := bstep (se 1 (by rfl) ⟨1570949, by rfl⟩ : syracuseStep 2094599 = 3141899) B3141899
theorem B325183 : Blo 287828 325183 := bstep (se 1 (by rfl) ⟨243887, by rfl⟩ : syracuseStep 325183 = 487775) B487775
theorem B652895 : Blo 287828 652895 := bstep (se 1 (by rfl) ⟨489671, by rfl⟩ : syracuseStep 652895 = 979343) B979343
theorem B2782957 : Blo 287828 2782957 := bstep (se 3 (by rfl) ⟨521804, by rfl⟩ : syracuseStep 2782957 = 1043609) B1043609
theorem B653111 : Blo 287828 653111 := bstep (se 1 (by rfl) ⟨489833, by rfl⟩ : syracuseStep 653111 = 979667) B979667
theorem B1242935 : Blo 287828 1242935 := bstep (se 1 (by rfl) ⟨932201, by rfl⟩ : syracuseStep 1242935 = 1864403) B1864403
theorem B489577 : Blo 287828 489577 := bstep (se 2 (by rfl) ⟨183591, by rfl⟩ : syracuseStep 489577 = 367183) B367183
theorem B653417 : Blo 287828 653417 := bstep (se 2 (by rfl) ⟨245031, by rfl⟩ : syracuseStep 653417 = 490063) B490063
theorem B2357495 : Blo 287828 2357495 := bstep (se 1 (by rfl) ⟨1768121, by rfl⟩ : syracuseStep 2357495 = 3536243) B3536243
theorem B326011 : Blo 287828 326011 := bstep (se 1 (by rfl) ⟨244508, by rfl⟩ : syracuseStep 326011 = 489017) B489017
theorem B1505719 : Blo 287828 1505719 := bstep (se 1 (by rfl) ⟨1129289, by rfl⟩ : syracuseStep 1505719 = 2258579) B2258579
theorem B1047113 : Blo 287828 1047113 := bstep (se 2 (by rfl) ⟨392667, by rfl⟩ : syracuseStep 1047113 = 785335) B785335
theorem B653903 : Blo 287828 653903 := bstep (se 1 (by rfl) ⟨490427, by rfl⟩ : syracuseStep 653903 = 980855) B980855
theorem B981611 : Blo 287828 981611 := bstep (se 1 (by rfl) ⟨736208, by rfl⟩ : syracuseStep 981611 = 1472417) B1472417
theorem B5569175 : Blo 287828 5569175 := bstep (se 1 (by rfl) ⟨4176881, by rfl⟩ : syracuseStep 5569175 = 8353763) B8353763
theorem B57834163 : Blo 287828 57834163 := bstep (se 1 (by rfl) ⟨43375622, by rfl⟩ : syracuseStep 57834163 = 86751245) B86751245
theorem B654047 : Blo 287828 654047 := bstep (se 1 (by rfl) ⟨490535, by rfl⟩ : syracuseStep 654047 = 981071) B981071
theorem B326479 : Blo 287828 326479 := bstep (se 1 (by rfl) ⟨244859, by rfl⟩ : syracuseStep 326479 = 489719) B489719
theorem B654299 : Blo 287828 654299 := bstep (se 1 (by rfl) ⟨490724, by rfl⟩ : syracuseStep 654299 = 981449) B981449
theorem B1604623 : Blo 287828 1604623 := bstep (se 1 (by rfl) ⟨1203467, by rfl⟩ : syracuseStep 1604623 = 2406935) B2406935
theorem B1473551 : Blo 287828 1473551 := bstep (se 1 (by rfl) ⟨1105163, by rfl⟩ : syracuseStep 1473551 = 2210327) B2210327
theorem B4946993 : Blo 287828 4946993 := bstep (se 2 (by rfl) ⟨1855122, by rfl⟩ : syracuseStep 4946993 = 3710245) B3710245
theorem B654479 : Blo 287828 654479 := bstep (se 1 (by rfl) ⟨490859, by rfl⟩ : syracuseStep 654479 = 981719) B981719
theorem B982205 : Blo 287828 982205 := bstep (se 3 (by rfl) ⟨184163, by rfl⟩ : syracuseStep 982205 = 368327) B368327
theorem B326875 : Blo 287828 326875 := bstep (se 1 (by rfl) ⟨245156, by rfl⟩ : syracuseStep 326875 = 490313) B490313
theorem B654569 : Blo 287828 654569 := bstep (se 2 (by rfl) ⟨245463, by rfl⟩ : syracuseStep 654569 = 490927) B490927
theorem B654623 : Blo 287828 654623 := bstep (se 1 (by rfl) ⟨490967, by rfl⟩ : syracuseStep 654623 = 981935) B981935
theorem B2358665 : Blo 287828 2358665 := bstep (se 2 (by rfl) ⟨884499, by rfl⟩ : syracuseStep 2358665 = 1768999) B1768999
theorem B327163 : Blo 287828 327163 := bstep (se 1 (by rfl) ⟨245372, by rfl⟩ : syracuseStep 327163 = 490745) B490745
theorem B2653721 : Blo 287828 2653721 := bstep (se 2 (by rfl) ⟨995145, by rfl⟩ : syracuseStep 2653721 = 1990291) B1990291
theorem B327343 : Blo 287828 327343 := bstep (se 1 (by rfl) ⟨245507, by rfl⟩ : syracuseStep 327343 = 491015) B491015
theorem B491305 : Blo 287828 491305 := bstep (se 2 (by rfl) ⟨184239, by rfl⟩ : syracuseStep 491305 = 368479) B368479
theorem B655145 : Blo 287828 655145 := bstep (se 2 (by rfl) ⟨245679, by rfl⟩ : syracuseStep 655145 = 491359) B491359
theorem B1474361 : Blo 287828 1474361 := bstep (se 2 (by rfl) ⟨552885, by rfl⟩ : syracuseStep 1474361 = 1105771) B1105771
theorem B2195261 : Blo 287828 2195261 := bstep (se 3 (by rfl) ⟨411611, by rfl⟩ : syracuseStep 2195261 = 823223) B823223
theorem B2490173 : Blo 287828 2490173 := bstep (se 3 (by rfl) ⟨466907, by rfl⟩ : syracuseStep 2490173 = 933815) B933815
theorem B622441 : Blo 287828 622441 := bstep (se 2 (by rfl) ⟨233415, by rfl⟩ : syracuseStep 622441 = 466831) B466831
theorem B327631 : Blo 287828 327631 := bstep (se 1 (by rfl) ⟨245723, by rfl⟩ : syracuseStep 327631 = 491447) B491447
theorem B10485811 : Blo 287828 10485811 := bstep (se 1 (by rfl) ⟨7864358, by rfl⟩ : syracuseStep 10485811 = 15728717) B15728717
theorem B983393 : Blo 287828 983393 := bstep (se 2 (by rfl) ⟨368772, by rfl⟩ : syracuseStep 983393 = 737545) B737545
theorem B328063 : Blo 287828 328063 := bstep (se 1 (by rfl) ⟨246047, by rfl⟩ : syracuseStep 328063 = 492095) B492095
theorem B819841 : Blo 287828 819841 := bstep (se 2 (by rfl) ⟨307440, by rfl⟩ : syracuseStep 819841 = 614881) B614881
theorem B3703481 : Blo 287828 3703481 := bstep (se 2 (by rfl) ⟨1388805, by rfl⟩ : syracuseStep 3703481 = 2777611) B2777611
theorem B525035 : Blo 287828 525035 := bstep (se 1 (by rfl) ⟨393776, by rfl⟩ : syracuseStep 525035 = 787553) B787553
theorem B2196233 : Blo 287828 2196233 := bstep (se 2 (by rfl) ⟨823587, by rfl⟩ : syracuseStep 2196233 = 1647175) B1647175
theorem B2950031 : Blo 287828 2950031 := bstep (se 1 (by rfl) ⟨2212523, by rfl⟩ : syracuseStep 2950031 = 4425047) B4425047
theorem B1475495 : Blo 287828 1475495 := bstep (se 1 (by rfl) ⟨1106621, by rfl⟩ : syracuseStep 1475495 = 2213243) B2213243
theorem B787411 : Blo 287828 787411 := bstep (se 1 (by rfl) ⟨590558, by rfl⟩ : syracuseStep 787411 = 1181117) B1181117
theorem B3507823 : Blo 287828 3507823 := bstep (se 1 (by rfl) ⟨2630867, by rfl⟩ : syracuseStep 3507823 = 5261735) B5261735
theorem B984743 : Blo 287828 984743 := bstep (se 1 (by rfl) ⟨738557, by rfl⟩ : syracuseStep 984743 = 1477115) B1477115
theorem B1640159 : Blo 287828 1640159 := bstep (se 1 (by rfl) ⟨1230119, by rfl⟩ : syracuseStep 1640159 = 2460239) B2460239
theorem B788255 : Blo 287828 788255 := bstep (se 1 (by rfl) ⟨591191, by rfl⟩ : syracuseStep 788255 = 1182383) B1182383
theorem B73664369 : Blo 287828 73664369 := bstep (se 2 (by rfl) ⟨27624138, by rfl⟩ : syracuseStep 73664369 = 55248277) B55248277
theorem B1771429 : Blo 287828 1771429 := bstep (se 4 (by rfl) ⟨166071, by rfl⟩ : syracuseStep 1771429 = 332143) B332143
theorem B886909 : Blo 287828 886909 := bstep (se 3 (by rfl) ⟨166295, by rfl⟩ : syracuseStep 886909 = 332591) B332591
theorem B985483 : Blo 287828 985483 := bstep (se 1 (by rfl) ⟨739112, by rfl⟩ : syracuseStep 985483 = 1478225) B1478225
theorem B986087 : Blo 287828 986087 := bstep (se 1 (by rfl) ⟨739565, by rfl⟩ : syracuseStep 986087 = 1479131) B1479131
theorem B10325069 : Blo 287828 10325069 := bstep (se 3 (by rfl) ⟨1935950, by rfl⟩ : syracuseStep 10325069 = 3871901) B3871901
theorem B3116339 : Blo 287828 3116339 := bstep (se 1 (by rfl) ⟨2337254, by rfl⟩ : syracuseStep 3116339 = 4674509) B4674509
theorem B986687 : Blo 287828 986687 := bstep (se 1 (by rfl) ⟨740015, by rfl⟩ : syracuseStep 986687 = 1480031) B1480031
theorem B2461265 : Blo 287828 2461265 := bstep (se 2 (by rfl) ⟨922974, by rfl⟩ : syracuseStep 2461265 = 1845949) B1845949
theorem B1412743 : Blo 287828 1412743 := bstep (se 1 (by rfl) ⟨1059557, by rfl⟩ : syracuseStep 1412743 = 2119115) B2119115
theorem B1117891 : Blo 287828 1117891 := bstep (se 1 (by rfl) ⟨838418, by rfl⟩ : syracuseStep 1117891 = 1676837) B1676837
theorem B561017 : Blo 287828 561017 := bstep (se 2 (by rfl) ⟨210381, by rfl⟩ : syracuseStep 561017 = 420763) B420763
theorem B823247 : Blo 287828 823247 := bstep (se 1 (by rfl) ⟨617435, by rfl⟩ : syracuseStep 823247 = 1234871) B1234871
theorem B14323729 : Blo 287828 14323729 := bstep (se 2 (by rfl) ⟨5371398, by rfl⟩ : syracuseStep 14323729 = 10742797) B10742797
theorem B823679 : Blo 287828 823679 := bstep (se 1 (by rfl) ⟨617759, by rfl⟩ : syracuseStep 823679 = 1235519) B1235519
theorem B692819 : Blo 287828 692819 := bstep (se 1 (by rfl) ⟨519614, by rfl⟩ : syracuseStep 692819 = 1039229) B1039229
theorem B824089 : Blo 287828 824089 := bstep (se 2 (by rfl) ⟨309033, by rfl⟩ : syracuseStep 824089 = 618067) B618067
theorem B365563 : Blo 287828 365563 := bstep (se 1 (by rfl) ⟨274172, by rfl⟩ : syracuseStep 365563 = 548345) B548345
theorem B35493065 : Blo 287828 35493065 := bstep (se 2 (by rfl) ⟨13309899, by rfl⟩ : syracuseStep 35493065 = 26619799) B26619799
theorem B4199633 : Blo 287828 4199633 := bstep (se 2 (by rfl) ⟨1574862, by rfl⟩ : syracuseStep 4199633 = 3149725) B3149725
theorem B431783 : Blo 287828 431783 := bstep (se 1 (by rfl) ⟨323837, by rfl⟩ : syracuseStep 431783 = 647675) B647675
theorem B3708605 : Blo 287828 3708605 := bstep (se 3 (by rfl) ⟨695363, by rfl⟩ : syracuseStep 3708605 = 1390727) B1390727
theorem B431867 : Blo 287828 431867 := bstep (se 1 (by rfl) ⟨323900, by rfl⟩ : syracuseStep 431867 = 647801) B647801
theorem B431903 : Blo 287828 431903 := bstep (se 1 (by rfl) ⟨323927, by rfl⟩ : syracuseStep 431903 = 647855) B647855
theorem B431951 : Blo 287828 431951 := bstep (se 1 (by rfl) ⟨323963, by rfl⟩ : syracuseStep 431951 = 647927) B647927
theorem B432071 : Blo 287828 432071 := bstep (se 1 (by rfl) ⟨324053, by rfl⟩ : syracuseStep 432071 = 648107) B648107
theorem B366535 : Blo 287828 366535 := bstep (se 1 (by rfl) ⟨274901, by rfl⟩ : syracuseStep 366535 = 549803) B549803
theorem B825319 : Blo 287828 825319 := bstep (se 1 (by rfl) ⟨618989, by rfl⟩ : syracuseStep 825319 = 1237979) B1237979
theorem B694433 : Blo 287828 694433 := bstep (se 2 (by rfl) ⟨260412, by rfl⟩ : syracuseStep 694433 = 520825) B520825
theorem B465191 : Blo 287828 465191 := bstep (se 1 (by rfl) ⟨348893, by rfl⟩ : syracuseStep 465191 = 697787) B697787
theorem B432425 : Blo 287828 432425 := bstep (se 2 (by rfl) ⟨162159, by rfl⟩ : syracuseStep 432425 = 324319) B324319
theorem B432431 : Blo 287828 432431 := bstep (se 1 (by rfl) ⟨324323, by rfl⟩ : syracuseStep 432431 = 648647) B648647
theorem B825673 : Blo 287828 825673 := bstep (se 2 (by rfl) ⟨309627, by rfl⟩ : syracuseStep 825673 = 619255) B619255
theorem B825707 : Blo 287828 825707 := bstep (se 1 (by rfl) ⟨619280, by rfl⟩ : syracuseStep 825707 = 1238561) B1238561
theorem B432671 : Blo 287828 432671 := bstep (se 1 (by rfl) ⟨324503, by rfl⟩ : syracuseStep 432671 = 649007) B649007
theorem B4463237 : Blo 287828 4463237 := bstep (se 4 (by rfl) ⟨418428, by rfl⟩ : syracuseStep 4463237 = 836857) B836857
theorem B1579867 : Blo 287828 1579867 := bstep (se 1 (by rfl) ⟨1184900, by rfl⟩ : syracuseStep 1579867 = 2369801) B2369801
theorem B10623899 : Blo 287828 10623899 := bstep (se 1 (by rfl) ⟨7967924, by rfl⟩ : syracuseStep 10623899 = 15935849) B15935849
theorem B433055 : Blo 287828 433055 := bstep (se 1 (by rfl) ⟨324791, by rfl⟩ : syracuseStep 433055 = 649583) B649583
theorem B433103 : Blo 287828 433103 := bstep (se 1 (by rfl) ⟨324827, by rfl⟩ : syracuseStep 433103 = 649655) B649655
theorem B924641 : Blo 287828 924641 := bstep (se 2 (by rfl) ⟨346740, by rfl⟩ : syracuseStep 924641 = 693481) B693481
theorem B433193 : Blo 287828 433193 := bstep (se 2 (by rfl) ⟨162447, by rfl⟩ : syracuseStep 433193 = 324895) B324895
theorem B433199 : Blo 287828 433199 := bstep (se 1 (by rfl) ⟨324899, by rfl⟩ : syracuseStep 433199 = 649799) B649799
theorem B14851133 : Blo 287828 14851133 := bstep (se 3 (by rfl) ⟨2784587, by rfl⟩ : syracuseStep 14851133 = 5569175) B5569175
theorem B433223 : Blo 287828 433223 := bstep (se 1 (by rfl) ⟨324917, by rfl⟩ : syracuseStep 433223 = 649835) B649835
theorem B433487 : Blo 287828 433487 := bstep (se 1 (by rfl) ⟨325115, by rfl⟩ : syracuseStep 433487 = 650231) B650231
theorem B433577 : Blo 287828 433577 := bstep (se 2 (by rfl) ⟨162591, by rfl⟩ : syracuseStep 433577 = 325183) B325183
theorem B433727 : Blo 287828 433727 := bstep (se 1 (by rfl) ⟨325295, by rfl⟩ : syracuseStep 433727 = 650591) B650591
theorem B3710609 : Blo 287828 3710609 := bstep (se 2 (by rfl) ⟨1391478, by rfl⟩ : syracuseStep 3710609 = 2782957) B2782957
theorem B925511 : Blo 287828 925511 := bstep (se 1 (by rfl) ⟨694133, by rfl⟩ : syracuseStep 925511 = 1388267) B1388267
theorem B433991 : Blo 287828 433991 := bstep (se 1 (by rfl) ⟨325493, by rfl⟩ : syracuseStep 433991 = 650987) B650987
theorem B15966071 : Blo 287828 15966071 := bstep (se 1 (by rfl) ⟨11974553, by rfl⟩ : syracuseStep 15966071 = 23949107) B23949107
theorem B434075 : Blo 287828 434075 := bstep (se 1 (by rfl) ⟨325556, by rfl⟩ : syracuseStep 434075 = 651113) B651113
theorem B434639 : Blo 287828 434639 := bstep (se 1 (by rfl) ⟨325979, by rfl⟩ : syracuseStep 434639 = 651959) B651959
theorem B434681 : Blo 287828 434681 := bstep (se 2 (by rfl) ⟨163005, by rfl⟩ : syracuseStep 434681 = 326011) B326011
theorem B2007625 : Blo 287828 2007625 := bstep (se 2 (by rfl) ⟨752859, by rfl⟩ : syracuseStep 2007625 = 1505719) B1505719
theorem B434783 : Blo 287828 434783 := bstep (se 1 (by rfl) ⟨326087, by rfl⟩ : syracuseStep 434783 = 652175) B652175
theorem B77112217 : Blo 287828 77112217 := bstep (se 2 (by rfl) ⟨28917081, by rfl⟩ : syracuseStep 77112217 = 57834163) B57834163
theorem B435263 : Blo 287828 435263 := bstep (se 1 (by rfl) ⟨326447, by rfl⟩ : syracuseStep 435263 = 652895) B652895
theorem B435305 : Blo 287828 435305 := bstep (se 2 (by rfl) ⟨163239, by rfl⟩ : syracuseStep 435305 = 326479) B326479
theorem B435407 : Blo 287828 435407 := bstep (se 1 (by rfl) ⟨326555, by rfl⟩ : syracuseStep 435407 = 653111) B653111
theorem B828623 : Blo 287828 828623 := bstep (se 1 (by rfl) ⟨621467, by rfl⟩ : syracuseStep 828623 = 1242935) B1242935
theorem B2139497 : Blo 287828 2139497 := bstep (se 2 (by rfl) ⟨802311, by rfl⟩ : syracuseStep 2139497 = 1604623) B1604623
theorem B435611 : Blo 287828 435611 := bstep (se 1 (by rfl) ⟨326708, by rfl⟩ : syracuseStep 435611 = 653417) B653417
theorem B435833 : Blo 287828 435833 := bstep (se 2 (by rfl) ⟨163437, by rfl⟩ : syracuseStep 435833 = 326875) B326875
theorem B698075 : Blo 287828 698075 := bstep (se 1 (by rfl) ⟨523556, by rfl⟩ : syracuseStep 698075 = 1047113) B1047113
theorem B435935 : Blo 287828 435935 := bstep (se 1 (by rfl) ⟨326951, by rfl⟩ : syracuseStep 435935 = 653903) B653903
theorem B436031 : Blo 287828 436031 := bstep (se 1 (by rfl) ⟨327023, by rfl⟩ : syracuseStep 436031 = 654047) B654047
theorem B436199 : Blo 287828 436199 := bstep (se 1 (by rfl) ⟨327149, by rfl⟩ : syracuseStep 436199 = 654299) B654299
theorem B436217 : Blo 287828 436217 := bstep (se 2 (by rfl) ⟨163581, by rfl⟩ : syracuseStep 436217 = 327163) B327163
theorem B1845281 : Blo 287828 1845281 := bstep (se 2 (by rfl) ⟨691980, by rfl⟩ : syracuseStep 1845281 = 1383961) B1383961
theorem B436319 : Blo 287828 436319 := bstep (se 1 (by rfl) ⟨327239, by rfl⟩ : syracuseStep 436319 = 654479) B654479
theorem B436379 : Blo 287828 436379 := bstep (se 1 (by rfl) ⟨327284, by rfl⟩ : syracuseStep 436379 = 654569) B654569
theorem B436415 : Blo 287828 436415 := bstep (se 1 (by rfl) ⟨327311, by rfl⟩ : syracuseStep 436415 = 654623) B654623
theorem B1845463 : Blo 287828 1845463 := bstep (se 1 (by rfl) ⟨1384097, by rfl⟩ : syracuseStep 1845463 = 2768195) B2768195
theorem B436457 : Blo 287828 436457 := bstep (se 2 (by rfl) ⟨163671, by rfl⟩ : syracuseStep 436457 = 327343) B327343
theorem B1321273 : Blo 287828 1321273 := bstep (se 2 (by rfl) ⟨495477, by rfl⟩ : syracuseStep 1321273 = 990955) B990955
theorem B731531 : Blo 287828 731531 := bstep (se 1 (by rfl) ⟨548648, by rfl⟩ : syracuseStep 731531 = 1097297) B1097297
theorem B829921 : Blo 287828 829921 := bstep (se 2 (by rfl) ⟨311220, by rfl⟩ : syracuseStep 829921 = 622441) B622441
theorem B436763 : Blo 287828 436763 := bstep (se 1 (by rfl) ⟨327572, by rfl⟩ : syracuseStep 436763 = 655145) B655145
theorem B436841 : Blo 287828 436841 := bstep (se 2 (by rfl) ⟨163815, by rfl⟩ : syracuseStep 436841 = 327631) B327631
theorem B3287789 : Blo 287828 3287789 := bstep (se 3 (by rfl) ⟨616460, by rfl⟩ : syracuseStep 3287789 = 1232921) B1232921
theorem B830263 : Blo 287828 830263 := bstep (se 1 (by rfl) ⟨622697, by rfl⟩ : syracuseStep 830263 = 1245395) B1245395
theorem B15281167 : Blo 287828 15281167 := bstep (se 1 (by rfl) ⟨11460875, by rfl⟩ : syracuseStep 15281167 = 22921751) B22921751
theorem B437369 : Blo 287828 437369 := bstep (se 2 (by rfl) ⟨164013, by rfl⟩ : syracuseStep 437369 = 328027) B328027
theorem B437471 : Blo 287828 437471 := bstep (se 1 (by rfl) ⟨328103, by rfl⟩ : syracuseStep 437471 = 656207) B656207
theorem B437513 : Blo 287828 437513 := bstep (se 2 (by rfl) ⟨164067, by rfl⟩ : syracuseStep 437513 = 328135) B328135
theorem B437615 : Blo 287828 437615 := bstep (se 1 (by rfl) ⟨328211, by rfl⟩ : syracuseStep 437615 = 656423) B656423
theorem B437735 : Blo 287828 437735 := bstep (se 1 (by rfl) ⟨328301, by rfl⟩ : syracuseStep 437735 = 656603) B656603
theorem B732847 : Blo 287828 732847 := bstep (se 1 (by rfl) ⟨549635, by rfl⟩ : syracuseStep 732847 = 1099271) B1099271
theorem B1388461 : Blo 287828 1388461 := bstep (se 3 (by rfl) ⟨260336, by rfl⟩ : syracuseStep 1388461 = 520673) B520673
theorem B733151 : Blo 287828 733151 := bstep (se 1 (by rfl) ⟨549863, by rfl⟩ : syracuseStep 733151 = 1099727) B1099727
theorem B733171 : Blo 287828 733171 := bstep (se 1 (by rfl) ⟨549878, by rfl⟩ : syracuseStep 733171 = 1099757) B1099757
theorem B733495 : Blo 287828 733495 := bstep (se 1 (by rfl) ⟨550121, by rfl⟩ : syracuseStep 733495 = 1100243) B1100243
theorem B3715577 : Blo 287828 3715577 := bstep (se 2 (by rfl) ⟨1393341, by rfl⟩ : syracuseStep 3715577 = 2786683) B2786683
theorem B733799 : Blo 287828 733799 := bstep (se 1 (by rfl) ⟨550349, by rfl⟩ : syracuseStep 733799 = 1100699) B1100699
theorem B6304985 : Blo 287828 6304985 := bstep (se 2 (by rfl) ⟨2364369, by rfl⟩ : syracuseStep 6304985 = 4728739) B4728739
theorem B734791 : Blo 287828 734791 := bstep (se 1 (by rfl) ⟨551093, by rfl⟩ : syracuseStep 734791 = 1102187) B1102187
theorem B734903 : Blo 287828 734903 := bstep (se 1 (by rfl) ⟨551177, by rfl⟩ : syracuseStep 734903 = 1102355) B1102355
theorem B5585597 : Blo 287828 5585597 := bstep (se 3 (by rfl) ⟨1047299, by rfl⟩ : syracuseStep 5585597 = 2094599) B2094599
theorem B1391327 : Blo 287828 1391327 := bstep (se 1 (by rfl) ⟨1043495, by rfl⟩ : syracuseStep 1391327 = 2086991) B2086991
theorem B1686815 : Blo 287828 1686815 := bstep (se 1 (by rfl) ⟨1265111, by rfl⟩ : syracuseStep 1686815 = 2530223) B2530223
theorem B1457513 : Blo 287828 1457513 := bstep (se 2 (by rfl) ⟨546567, by rfl⟩ : syracuseStep 1457513 = 1093135) B1093135
theorem B310759 : Blo 287828 310759 := bstep (se 1 (by rfl) ⟨233069, by rfl⟩ : syracuseStep 310759 = 466139) B466139
theorem B736847 : Blo 287828 736847 := bstep (se 1 (by rfl) ⟨552635, by rfl⟩ : syracuseStep 736847 = 1105271) B1105271
theorem B2801753 : Blo 287828 2801753 := bstep (se 2 (by rfl) ⟨1050657, by rfl⟩ : syracuseStep 2801753 = 2101315) B2101315
theorem B902249 : Blo 287828 902249 := bstep (se 2 (by rfl) ⟨338343, by rfl⟩ : syracuseStep 902249 = 676687) B676687
theorem B411247 : Blo 287828 411247 := bstep (se 1 (by rfl) ⟨308435, by rfl⟩ : syracuseStep 411247 = 616871) B616871
theorem B1230497 : Blo 287828 1230497 := bstep (se 2 (by rfl) ⟨461436, by rfl⟩ : syracuseStep 1230497 = 922873) B922873
theorem B411743 : Blo 287828 411743 := bstep (se 1 (by rfl) ⟨308807, by rfl⟩ : syracuseStep 411743 = 617615) B617615
theorem B245057879 : Blo 287828 245057879 := bstep (se 1 (by rfl) ⟨183793409, by rfl⟩ : syracuseStep 245057879 = 367586819) B367586819
theorem B2378591 : Blo 287828 2378591 := bstep (se 1 (by rfl) ⟨1783943, by rfl⟩ : syracuseStep 2378591 = 3567887) B3567887
theorem B42224651 : Blo 287828 42224651 := bstep (se 1 (by rfl) ⟨31668488, by rfl⟩ : syracuseStep 42224651 = 63336977) B63336977
theorem B1330615 : Blo 287828 1330615 := bstep (se 1 (by rfl) ⟨997961, by rfl⟩ : syracuseStep 1330615 = 1995923) B1995923
theorem B1854971 : Blo 287828 1854971 := bstep (se 1 (by rfl) ⟨1391228, by rfl⟩ : syracuseStep 1854971 = 2782457) B2782457
theorem B413275 : Blo 287828 413275 := bstep (se 1 (by rfl) ⟨309956, by rfl⟩ : syracuseStep 413275 = 619913) B619913
theorem B8147249 : Blo 287828 8147249 := bstep (se 2 (by rfl) ⟨3055218, by rfl⟩ : syracuseStep 8147249 = 6110437) B6110437
theorem B3297995 : Blo 287828 3297995 := bstep (se 1 (by rfl) ⟨2473496, by rfl⟩ : syracuseStep 3297995 = 4946993) B4946993
theorem B414505 : Blo 287828 414505 := bstep (se 2 (by rfl) ⟨155439, by rfl⟩ : syracuseStep 414505 = 310879) B310879
theorem B1561609 : Blo 287828 1561609 := bstep (se 2 (by rfl) ⟨585603, by rfl⟩ : syracuseStep 1561609 = 1171207) B1171207
theorem B1463507 : Blo 287828 1463507 := bstep (se 1 (by rfl) ⟨1097630, by rfl⟩ : syracuseStep 1463507 = 2195261) B2195261
theorem B1660115 : Blo 287828 1660115 := bstep (se 1 (by rfl) ⟨1245086, by rfl⟩ : syracuseStep 1660115 = 2490173) B2490173
theorem B8377577 : Blo 287828 8377577 := bstep (se 2 (by rfl) ⟨3141591, by rfl⟩ : syracuseStep 8377577 = 6283183) B6283183
theorem B972539 : Blo 287828 972539 := bstep (se 1 (by rfl) ⟨729404, by rfl⟩ : syracuseStep 972539 = 1458809) B1458809
theorem B972701 : Blo 287828 972701 := bstep (se 3 (by rfl) ⟨182381, by rfl⟩ : syracuseStep 972701 = 364763) B364763
theorem B350191 : Blo 287828 350191 := bstep (se 1 (by rfl) ⟨262643, by rfl⟩ : syracuseStep 350191 = 525287) B525287
theorem B1038433 : Blo 287828 1038433 := bstep (se 2 (by rfl) ⟨389412, by rfl⟩ : syracuseStep 1038433 = 778825) B778825
theorem B8444189 : Blo 287828 8444189 := bstep (se 3 (by rfl) ⟨1583285, by rfl⟩ : syracuseStep 8444189 = 3166571) B3166571
theorem B3955067 : Blo 287828 3955067 := bstep (se 1 (by rfl) ⟨2966300, by rfl⟩ : syracuseStep 3955067 = 5932601) B5932601
theorem B2186027 : Blo 287828 2186027 := bstep (se 1 (by rfl) ⟨1639520, by rfl⟩ : syracuseStep 2186027 = 3279041) B3279041
theorem B744275 : Blo 287828 744275 := bstep (se 1 (by rfl) ⟨558206, by rfl⟩ : syracuseStep 744275 = 1116413) B1116413
theorem B973673 : Blo 287828 973673 := bstep (se 2 (by rfl) ⟨365127, by rfl⟩ : syracuseStep 973673 = 730255) B730255
theorem B973727 : Blo 287828 973727 := bstep (se 1 (by rfl) ⟨730295, by rfl⟩ : syracuseStep 973727 = 1460591) B1460591
theorem B1104799 : Blo 287828 1104799 := bstep (se 1 (by rfl) ⟨828599, by rfl⟩ : syracuseStep 1104799 = 1657199) B1657199
theorem B1465289 : Blo 287828 1465289 := bstep (se 2 (by rfl) ⟨549483, by rfl⟩ : syracuseStep 1465289 = 1098967) B1098967
theorem B1793015 : Blo 287828 1793015 := bstep (se 1 (by rfl) ⟨1344761, by rfl⟩ : syracuseStep 1793015 = 2689523) B2689523
theorem B1039645 : Blo 287828 1039645 := bstep (se 3 (by rfl) ⟨194933, by rfl⟩ : syracuseStep 1039645 = 389867) B389867
theorem B1400399 : Blo 287828 1400399 := bstep (se 1 (by rfl) ⟨1050299, by rfl⟩ : syracuseStep 1400399 = 2100599) B2100599
theorem B1466099 : Blo 287828 1466099 := bstep (se 1 (by rfl) ⟨1099574, by rfl⟩ : syracuseStep 1466099 = 2199149) B2199149
theorem B1171255 : Blo 287828 1171255 := bstep (se 1 (by rfl) ⟨878441, by rfl⟩ : syracuseStep 1171255 = 1756883) B1756883
theorem B2482109 : Blo 287828 2482109 := bstep (se 3 (by rfl) ⟨465395, by rfl⟩ : syracuseStep 2482109 = 930791) B930791
theorem B1106257 : Blo 287828 1106257 := bstep (se 2 (by rfl) ⟨414846, by rfl⟩ : syracuseStep 1106257 = 829693) B829693
theorem B647657 : Blo 287828 647657 := bstep (se 2 (by rfl) ⟨242871, by rfl⟩ : syracuseStep 647657 = 485743) B485743
theorem B647945 : Blo 287828 647945 := bstep (se 2 (by rfl) ⟨242979, by rfl⟩ : syracuseStep 647945 = 485959) B485959
theorem B975995 : Blo 287828 975995 := bstep (se 1 (by rfl) ⟨731996, by rfl⟩ : syracuseStep 975995 = 1463993) B1463993
theorem B3957923 : Blo 287828 3957923 := bstep (se 1 (by rfl) ⟨2968442, by rfl⟩ : syracuseStep 3957923 = 5936885) B5936885
theorem B287951 : Blo 287828 287951 := bstep (se 1 (by rfl) ⟨215963, by rfl⟩ : syracuseStep 287951 = 431927) B431927
theorem B648521 : Blo 287828 648521 := bstep (se 2 (by rfl) ⟨243195, by rfl⟩ : syracuseStep 648521 = 486391) B486391
theorem B976265 : Blo 287828 976265 := bstep (se 2 (by rfl) ⟨366099, by rfl⟩ : syracuseStep 976265 = 732199) B732199
theorem B288155 : Blo 287828 288155 := bstep (se 1 (by rfl) ⟨216116, by rfl⟩ : syracuseStep 288155 = 432233) B432233
theorem B288367 : Blo 287828 288367 := bstep (se 1 (by rfl) ⟨216275, by rfl⟩ : syracuseStep 288367 = 432551) B432551
theorem B288423 : Blo 287828 288423 := bstep (se 1 (by rfl) ⟨216317, by rfl⟩ : syracuseStep 288423 = 432635) B432635
theorem B2090681 : Blo 287828 2090681 := bstep (se 2 (by rfl) ⟨784005, by rfl⟩ : syracuseStep 2090681 = 1568011) B1568011
theorem B288507 : Blo 287828 288507 := bstep (se 1 (by rfl) ⟨216380, by rfl⟩ : syracuseStep 288507 = 432761) B432761
theorem B1861379 : Blo 287828 1861379 := bstep (se 1 (by rfl) ⟨1396034, by rfl⟩ : syracuseStep 1861379 = 2792069) B2792069
theorem B288543 : Blo 287828 288543 := bstep (se 1 (by rfl) ⟨216407, by rfl⟩ : syracuseStep 288543 = 432815) B432815
theorem B288575 : Blo 287828 288575 := bstep (se 1 (by rfl) ⟨216431, by rfl⟩ : syracuseStep 288575 = 432863) B432863
theorem B288751 : Blo 287828 288751 := bstep (se 1 (by rfl) ⟨216563, by rfl⟩ : syracuseStep 288751 = 433127) B433127
theorem B977021 : Blo 287828 977021 := bstep (se 3 (by rfl) ⟨183191, by rfl⟩ : syracuseStep 977021 = 366383) B366383
theorem B288923 : Blo 287828 288923 := bstep (se 1 (by rfl) ⟨216692, by rfl⟩ : syracuseStep 288923 = 433385) B433385
theorem B288959 : Blo 287828 288959 := bstep (se 1 (by rfl) ⟨216719, by rfl⟩ : syracuseStep 288959 = 433439) B433439
theorem B649511 : Blo 287828 649511 := bstep (se 1 (by rfl) ⟨487133, by rfl⟩ : syracuseStep 649511 = 974267) B974267
theorem B289071 : Blo 287828 289071 := bstep (se 1 (by rfl) ⟨216803, by rfl⟩ : syracuseStep 289071 = 433607) B433607
theorem B551215 : Blo 287828 551215 := bstep (se 1 (by rfl) ⟨413411, by rfl⟩ : syracuseStep 551215 = 826823) B826823
theorem B649529 : Blo 287828 649529 := bstep (se 2 (by rfl) ⟨243573, by rfl⟩ : syracuseStep 649529 = 487147) B487147
theorem B977291 : Blo 287828 977291 := bstep (se 1 (by rfl) ⟨732968, by rfl⟩ : syracuseStep 977291 = 1465937) B1465937
theorem B289307 : Blo 287828 289307 := bstep (se 1 (by rfl) ⟨216980, by rfl⟩ : syracuseStep 289307 = 433961) B433961
theorem B289311 : Blo 287828 289311 := bstep (se 1 (by rfl) ⟨216983, by rfl⟩ : syracuseStep 289311 = 433967) B433967
theorem B485993 : Blo 287828 485993 := bstep (se 2 (by rfl) ⟨182247, by rfl⟩ : syracuseStep 485993 = 364495) B364495
theorem B1469177 : Blo 287828 1469177 := bstep (se 2 (by rfl) ⟨550941, by rfl⟩ : syracuseStep 1469177 = 1101883) B1101883
theorem B289627 : Blo 287828 289627 := bstep (se 1 (by rfl) ⟨217220, by rfl⟩ : syracuseStep 289627 = 434441) B434441
theorem B289695 : Blo 287828 289695 := bstep (se 1 (by rfl) ⟨217271, by rfl⟩ : syracuseStep 289695 = 434543) B434543
theorem B289839 : Blo 287828 289839 := bstep (se 1 (by rfl) ⟨217379, by rfl⟩ : syracuseStep 289839 = 434759) B434759
theorem B289863 : Blo 287828 289863 := bstep (se 1 (by rfl) ⟨217397, by rfl⟩ : syracuseStep 289863 = 434795) B434795
theorem B290015 : Blo 287828 290015 := bstep (se 1 (by rfl) ⟨217511, by rfl⟩ : syracuseStep 290015 = 435023) B435023
theorem B4484429 : Blo 287828 4484429 := bstep (se 3 (by rfl) ⟨840830, by rfl⟩ : syracuseStep 4484429 = 1681661) B1681661
theorem B552271 : Blo 287828 552271 := bstep (se 1 (by rfl) ⟨414203, by rfl⟩ : syracuseStep 552271 = 828407) B828407
theorem B486823 : Blo 287828 486823 := bstep (se 1 (by rfl) ⟨365117, by rfl⟩ : syracuseStep 486823 = 730235) B730235
theorem B1011133 : Blo 287828 1011133 := bstep (se 3 (by rfl) ⟨189587, by rfl⟩ : syracuseStep 1011133 = 379175) B379175
theorem B519635 : Blo 287828 519635 := bstep (se 1 (by rfl) ⟨389726, by rfl⟩ : syracuseStep 519635 = 779453) B779453
theorem B290279 : Blo 287828 290279 := bstep (se 1 (by rfl) ⟨217709, by rfl⟩ : syracuseStep 290279 = 435419) B435419
theorem B486985 : Blo 287828 486985 := bstep (se 2 (by rfl) ⟨182619, by rfl⟩ : syracuseStep 486985 = 365239) B365239
theorem B650825 : Blo 287828 650825 := bstep (se 2 (by rfl) ⟨244059, by rfl⟩ : syracuseStep 650825 = 488119) B488119
theorem B552521 : Blo 287828 552521 := bstep (se 2 (by rfl) ⟨207195, by rfl⟩ : syracuseStep 552521 = 414391) B414391
theorem B290395 : Blo 287828 290395 := bstep (se 1 (by rfl) ⟨217796, by rfl⟩ : syracuseStep 290395 = 435593) B435593
theorem B487019 : Blo 287828 487019 := bstep (se 1 (by rfl) ⟨365264, by rfl⟩ : syracuseStep 487019 = 730529) B730529
theorem B290631 : Blo 287828 290631 := bstep (se 1 (by rfl) ⟨217973, by rfl⟩ : syracuseStep 290631 = 435947) B435947
theorem B487289 : Blo 287828 487289 := bstep (se 2 (by rfl) ⟨182733, by rfl⟩ : syracuseStep 487289 = 365467) B365467
theorem B978911 : Blo 287828 978911 := bstep (se 1 (by rfl) ⟨734183, by rfl⟩ : syracuseStep 978911 = 1468367) B1468367
theorem B290783 : Blo 287828 290783 := bstep (se 1 (by rfl) ⟨218087, by rfl⟩ : syracuseStep 290783 = 436175) B436175
theorem B2551931 : Blo 287828 2551931 := bstep (se 1 (by rfl) ⟨1913948, by rfl⟩ : syracuseStep 2551931 = 3827897) B3827897
theorem B979073 : Blo 287828 979073 := bstep (se 2 (by rfl) ⟨367152, by rfl⟩ : syracuseStep 979073 = 734305) B734305
theorem B2486483 : Blo 287828 2486483 := bstep (se 1 (by rfl) ⟨1864862, by rfl⟩ : syracuseStep 2486483 = 3729725) B3729725
theorem B323815 : Blo 287828 323815 := bstep (se 1 (by rfl) ⟨242861, by rfl⟩ : syracuseStep 323815 = 485723) B485723
theorem B291047 : Blo 287828 291047 := bstep (se 1 (by rfl) ⟨218285, by rfl⟩ : syracuseStep 291047 = 436571) B436571
theorem B8319347 : Blo 287828 8319347 := bstep (se 1 (by rfl) ⟨6239510, by rfl⟩ : syracuseStep 8319347 = 12479021) B12479021
theorem B291199 : Blo 287828 291199 := bstep (se 1 (by rfl) ⟨218399, by rfl⟩ : syracuseStep 291199 = 436799) B436799
theorem B291279 : Blo 287828 291279 := bstep (se 1 (by rfl) ⟨218459, by rfl⟩ : syracuseStep 291279 = 436919) B436919
theorem B5599813 : Blo 287828 5599813 := bstep (se 4 (by rfl) ⟨524982, by rfl⟩ : syracuseStep 5599813 = 1049965) B1049965
theorem B979559 : Blo 287828 979559 := bstep (se 1 (by rfl) ⟨734669, by rfl⟩ : syracuseStep 979559 = 1469339) B1469339
theorem B291431 : Blo 287828 291431 := bstep (se 1 (by rfl) ⟨218573, by rfl⟩ : syracuseStep 291431 = 437147) B437147
theorem B324463 : Blo 287828 324463 := bstep (se 1 (by rfl) ⟨243347, by rfl⟩ : syracuseStep 324463 = 486695) B486695
theorem B291695 : Blo 287828 291695 := bstep (se 1 (by rfl) ⟨218771, by rfl⟩ : syracuseStep 291695 = 437543) B437543
theorem B291751 : Blo 287828 291751 := bstep (se 1 (by rfl) ⟨218813, by rfl⟩ : syracuseStep 291751 = 437627) B437627
theorem B979883 : Blo 287828 979883 := bstep (se 1 (by rfl) ⟨734912, by rfl⟩ : syracuseStep 979883 = 1469825) B1469825
theorem B488443 : Blo 287828 488443 := bstep (se 1 (by rfl) ⟨366332, by rfl⟩ : syracuseStep 488443 = 732665) B732665
theorem B652283 : Blo 287828 652283 := bstep (se 1 (by rfl) ⟨489212, by rfl⟩ : syracuseStep 652283 = 978425) B978425
theorem B553979 : Blo 287828 553979 := bstep (se 1 (by rfl) ⟨415484, by rfl⟩ : syracuseStep 553979 = 830969) B830969
theorem B652463 : Blo 287828 652463 := bstep (se 1 (by rfl) ⟨489347, by rfl⟩ : syracuseStep 652463 = 978695) B978695
theorem B652499 : Blo 287828 652499 := bstep (se 1 (by rfl) ⟨489374, by rfl⟩ : syracuseStep 652499 = 978749) B978749
theorem B3306743 : Blo 287828 3306743 := bstep (se 1 (by rfl) ⟨2480057, by rfl⟩ : syracuseStep 3306743 = 4960115) B4960115
theorem B3437873 : Blo 287828 3437873 := bstep (se 2 (by rfl) ⟨1289202, by rfl⟩ : syracuseStep 3437873 = 2578405) B2578405
theorem B980315 : Blo 287828 980315 := bstep (se 1 (by rfl) ⟨735236, by rfl⟩ : syracuseStep 980315 = 1470473) B1470473
theorem B488875 : Blo 287828 488875 := bstep (se 1 (by rfl) ⟨366656, by rfl⟩ : syracuseStep 488875 = 733313) B733313
theorem B980423 : Blo 287828 980423 := bstep (se 1 (by rfl) ⟨735317, by rfl⟩ : syracuseStep 980423 = 1470635) B1470635
theorem B652769 : Blo 287828 652769 := bstep (se 2 (by rfl) ⟨244788, by rfl⟩ : syracuseStep 652769 = 489577) B489577
theorem B1242695 : Blo 287828 1242695 := bstep (se 1 (by rfl) ⟨932021, by rfl⟩ : syracuseStep 1242695 = 1864043) B1864043
theorem B489071 : Blo 287828 489071 := bstep (se 1 (by rfl) ⟨366803, by rfl⟩ : syracuseStep 489071 = 733607) B733607
theorem B489179 : Blo 287828 489179 := bstep (se 1 (by rfl) ⟨366884, by rfl⟩ : syracuseStep 489179 = 733769) B733769
theorem B980747 : Blo 287828 980747 := bstep (se 1 (by rfl) ⟨735560, by rfl⟩ : syracuseStep 980747 = 1471121) B1471121
theorem B489415 : Blo 287828 489415 := bstep (se 1 (by rfl) ⟨367061, by rfl⟩ : syracuseStep 489415 = 734123) B734123
theorem B325615 : Blo 287828 325615 := bstep (se 1 (by rfl) ⟨244211, by rfl⟩ : syracuseStep 325615 = 488423) B488423
theorem B981017 : Blo 287828 981017 := bstep (se 2 (by rfl) ⟨367881, by rfl⟩ : syracuseStep 981017 = 735763) B735763
theorem B490171 : Blo 287828 490171 := bstep (se 1 (by rfl) ⟨367628, by rfl⟩ : syracuseStep 490171 = 735257) B735257
theorem B1571663 : Blo 287828 1571663 := bstep (se 1 (by rfl) ⟨1178747, by rfl⟩ : syracuseStep 1571663 = 2357495) B2357495
theorem B490475 : Blo 287828 490475 := bstep (se 1 (by rfl) ⟨367856, by rfl⟩ : syracuseStep 490475 = 735713) B735713
theorem B654407 : Blo 287828 654407 := bstep (se 1 (by rfl) ⟨490805, by rfl⟩ : syracuseStep 654407 = 981611) B981611
theorem B3210329 : Blo 287828 3210329 := bstep (se 2 (by rfl) ⟨1203873, by rfl⟩ : syracuseStep 3210329 = 2407747) B2407747
theorem B982367 : Blo 287828 982367 := bstep (se 1 (by rfl) ⟨736775, by rfl⟩ : syracuseStep 982367 = 1473551) B1473551
theorem B654803 : Blo 287828 654803 := bstep (se 1 (by rfl) ⟨491102, by rfl⟩ : syracuseStep 654803 = 982205) B982205
theorem B1572443 : Blo 287828 1572443 := bstep (se 1 (by rfl) ⟨1179332, by rfl⟩ : syracuseStep 1572443 = 2358665) B2358665
theorem B1769147 : Blo 287828 1769147 := bstep (se 1 (by rfl) ⟨1326860, by rfl⟩ : syracuseStep 1769147 = 2653721) B2653721
theorem B655073 : Blo 287828 655073 := bstep (se 2 (by rfl) ⟨245652, by rfl⟩ : syracuseStep 655073 = 491305) B491305
theorem B1867607 : Blo 287828 1867607 := bstep (se 1 (by rfl) ⟨1400705, by rfl⟩ : syracuseStep 1867607 = 2801411) B2801411
theorem B982907 : Blo 287828 982907 := bstep (se 1 (by rfl) ⟨737180, by rfl⟩ : syracuseStep 982907 = 1474361) B1474361
theorem B1867835 : Blo 287828 1867835 := bstep (se 1 (by rfl) ⟨1400876, by rfl⟩ : syracuseStep 1867835 = 2801753) B2801753
theorem B655595 : Blo 287828 655595 := bstep (se 1 (by rfl) ⟨491696, by rfl⟩ : syracuseStep 655595 = 983393) B983393
theorem B1475009 : Blo 287828 1475009 := bstep (se 2 (by rfl) ⟨553128, by rfl⟩ : syracuseStep 1475009 = 1106257) B1106257
theorem B1966687 : Blo 287828 1966687 := bstep (se 1 (by rfl) ⟨1475015, by rfl⟩ : syracuseStep 1966687 = 2950031) B2950031
theorem B983663 : Blo 287828 983663 := bstep (se 1 (by rfl) ⟨737747, by rfl⟩ : syracuseStep 983663 = 1475495) B1475495
theorem B820331 : Blo 287828 820331 := bstep (se 1 (by rfl) ⟨615248, by rfl⟩ : syracuseStep 820331 = 1230497) B1230497
theorem B656495 : Blo 287828 656495 := bstep (se 1 (by rfl) ⟨492371, by rfl⟩ : syracuseStep 656495 = 984743) B984743
theorem B525503 : Blo 287828 525503 := bstep (se 1 (by rfl) ⟨394127, by rfl⟩ : syracuseStep 525503 = 788255) B788255
theorem B1049881 : Blo 287828 1049881 := bstep (se 2 (by rfl) ⟨393705, by rfl⟩ : syracuseStep 1049881 = 787411) B787411
theorem B657391 : Blo 287828 657391 := bstep (se 1 (by rfl) ⟨493043, by rfl⟩ : syracuseStep 657391 = 986087) B986087
theorem B28149767 : Blo 287828 28149767 := bstep (se 1 (by rfl) ⟨21112325, by rfl⟩ : syracuseStep 28149767 = 42224651) B42224651
theorem B6883379 : Blo 287828 6883379 := bstep (se 1 (by rfl) ⟨5162534, by rfl⟩ : syracuseStep 6883379 = 10325069) B10325069
theorem B657791 : Blo 287828 657791 := bstep (se 1 (by rfl) ⟨493343, by rfl⟩ : syracuseStep 657791 = 986687) B986687
theorem B1640843 : Blo 287828 1640843 := bstep (se 1 (by rfl) ⟨1230632, by rfl⟩ : syracuseStep 1640843 = 2461265) B2461265
theorem B2361905 : Blo 287828 2361905 := bstep (se 2 (by rfl) ⟨885714, by rfl⟩ : syracuseStep 2361905 = 1771429) B1771429
theorem B1477277 : Blo 287828 1477277 := bstep (se 3 (by rfl) ⟨276989, by rfl⟩ : syracuseStep 1477277 = 553979) B553979
theorem B1182545 : Blo 287828 1182545 := bstep (se 2 (by rfl) ⟨443454, by rfl⟩ : syracuseStep 1182545 = 886909) B886909
theorem B2460617 : Blo 287828 2460617 := bstep (se 2 (by rfl) ⟨922731, by rfl⟩ : syracuseStep 2460617 = 1845463) B1845463
theorem B461879 : Blo 287828 461879 := bstep (se 1 (by rfl) ⟨346409, by rfl⟩ : syracuseStep 461879 = 692819) B692819
theorem B2198663 : Blo 287828 2198663 := bstep (se 1 (by rfl) ⟨1648997, by rfl⟩ : syracuseStep 2198663 = 3297995) B3297995
theorem B1313977 : Blo 287828 1313977 := bstep (se 2 (by rfl) ⟨492741, by rfl⟩ : syracuseStep 1313977 = 985483) B985483
theorem B23662043 : Blo 287828 23662043 := bstep (se 1 (by rfl) ⟨17746532, by rfl⟩ : syracuseStep 23662043 = 35493065) B35493065
theorem B8425957 : Blo 287828 8425957 := bstep (se 4 (by rfl) ⟨789933, by rfl⟩ : syracuseStep 8425957 = 1579867) B1579867
theorem B1774153 : Blo 287828 1774153 := bstep (se 2 (by rfl) ⟨665307, by rfl⟩ : syracuseStep 1774153 = 1330615) B1330615
theorem B1348177 : Blo 287828 1348177 := bstep (se 2 (by rfl) ⟨505566, by rfl⟩ : syracuseStep 1348177 = 1011133) B1011133
theorem B7082599 : Blo 287828 7082599 := bstep (se 1 (by rfl) ⟨5311949, by rfl⟩ : syracuseStep 7082599 = 10623899) B10623899
theorem B9900755 : Blo 287828 9900755 := bstep (se 1 (by rfl) ⟨7425566, by rfl⟩ : syracuseStep 9900755 = 14851133) B14851133
theorem B4920749 : Blo 287828 4920749 := bstep (se 3 (by rfl) ⟨922640, by rfl⟩ : syracuseStep 4920749 = 1845281) B1845281
theorem B431753 : Blo 287828 431753 := bstep (se 2 (by rfl) ⟨161907, by rfl⟩ : syracuseStep 431753 = 323815) B323815
theorem B431771 : Blo 287828 431771 := bstep (se 1 (by rfl) ⟨323828, by rfl⟩ : syracuseStep 431771 = 647657) B647657
theorem B431963 : Blo 287828 431963 := bstep (se 1 (by rfl) ⟨323972, by rfl⟩ : syracuseStep 431963 = 647945) B647945
theorem B432347 : Blo 287828 432347 := bstep (se 1 (by rfl) ⟨324260, by rfl⟩ : syracuseStep 432347 = 648521) B648521
theorem B465383 : Blo 287828 465383 := bstep (se 1 (by rfl) ⟨349037, by rfl⟩ : syracuseStep 465383 = 698075) B698075
theorem B432617 : Blo 287828 432617 := bstep (se 2 (by rfl) ⟨162231, by rfl⟩ : syracuseStep 432617 = 324463) B324463
theorem B433007 : Blo 287828 433007 := bstep (se 1 (by rfl) ⟨324755, by rfl⟩ : syracuseStep 433007 = 649511) B649511
theorem B433019 : Blo 287828 433019 := bstep (se 1 (by rfl) ⟨324764, by rfl⟩ : syracuseStep 433019 = 649529) B649529
theorem B2989619 : Blo 287828 2989619 := bstep (se 1 (by rfl) ⟨2242214, by rfl⟩ : syracuseStep 2989619 = 4484429) B4484429
theorem B433883 : Blo 287828 433883 := bstep (se 1 (by rfl) ⟨325412, by rfl⟩ : syracuseStep 433883 = 650825) B650825
theorem B434153 : Blo 287828 434153 := bstep (se 2 (by rfl) ⟨162807, by rfl⟩ : syracuseStep 434153 = 325615) B325615
theorem B466921 : Blo 287828 466921 := bstep (se 2 (by rfl) ⟨175095, by rfl⟩ : syracuseStep 466921 = 350191) B350191
theorem B1384577 : Blo 287828 1384577 := bstep (se 2 (by rfl) ⟨519216, by rfl⟩ : syracuseStep 1384577 = 1038433) B1038433
theorem B5546231 : Blo 287828 5546231 := bstep (se 1 (by rfl) ⟨4159673, by rfl⟩ : syracuseStep 5546231 = 8319347) B8319347
theorem B434855 : Blo 287828 434855 := bstep (se 1 (by rfl) ⟨326141, by rfl⟩ : syracuseStep 434855 = 652283) B652283
theorem B434975 : Blo 287828 434975 := bstep (se 1 (by rfl) ⟨326231, by rfl⟩ : syracuseStep 434975 = 652463) B652463
theorem B434999 : Blo 287828 434999 := bstep (se 1 (by rfl) ⟨326249, by rfl⟩ : syracuseStep 434999 = 652499) B652499
theorem B4203323 : Blo 287828 4203323 := bstep (se 1 (by rfl) ⟨3152492, by rfl⟩ : syracuseStep 4203323 = 6304985) B6304985
theorem B2204495 : Blo 287828 2204495 := bstep (se 1 (by rfl) ⟨1653371, by rfl⟩ : syracuseStep 2204495 = 3306743) B3306743
theorem B435179 : Blo 287828 435179 := bstep (se 1 (by rfl) ⟨326384, by rfl⟩ : syracuseStep 435179 = 652769) B652769
theorem B828463 : Blo 287828 828463 := bstep (se 1 (by rfl) ⟨621347, by rfl⟩ : syracuseStep 828463 = 1242695) B1242695
theorem B1385693 : Blo 287828 1385693 := bstep (se 3 (by rfl) ⟨259817, by rfl⟩ : syracuseStep 1385693 = 519635) B519635
theorem B1386193 : Blo 287828 1386193 := bstep (se 2 (by rfl) ⟨519822, by rfl⟩ : syracuseStep 1386193 = 1039645) B1039645
theorem B927551 : Blo 287828 927551 := bstep (se 1 (by rfl) ⟨695663, by rfl⟩ : syracuseStep 927551 = 1391327) B1391327
theorem B436271 : Blo 287828 436271 := bstep (se 1 (by rfl) ⟨327203, by rfl⟩ : syracuseStep 436271 = 654407) B654407
theorem B2140219 : Blo 287828 2140219 := bstep (se 1 (by rfl) ⟨1605164, by rfl⟩ : syracuseStep 2140219 = 3210329) B3210329
theorem B2468029 : Blo 287828 2468029 := bstep (se 3 (by rfl) ⟨462755, by rfl⟩ : syracuseStep 2468029 = 925511) B925511
theorem B1124543 : Blo 287828 1124543 := bstep (se 1 (by rfl) ⟨843407, by rfl⟩ : syracuseStep 1124543 = 1686815) B1686815
theorem B436535 : Blo 287828 436535 := bstep (se 1 (by rfl) ⟨327401, by rfl⟩ : syracuseStep 436535 = 654803) B654803
theorem B436715 : Blo 287828 436715 := bstep (se 1 (by rfl) ⟨327536, by rfl⟩ : syracuseStep 436715 = 655073) B655073
theorem B2468987 : Blo 287828 2468987 := bstep (se 1 (by rfl) ⟨1851740, by rfl⟩ : syracuseStep 2468987 = 3703481) B3703481
theorem B437417 : Blo 287828 437417 := bstep (se 2 (by rfl) ⟨164031, by rfl⟩ : syracuseStep 437417 = 328063) B328063
theorem B601499 : Blo 287828 601499 := bstep (se 1 (by rfl) ⟨451124, by rfl⟩ : syracuseStep 601499 = 902249) B902249
theorem B1093121 : Blo 287828 1093121 := bstep (se 2 (by rfl) ⟨409920, by rfl⟩ : syracuseStep 1093121 = 819841) B819841
theorem B1093439 : Blo 287828 1093439 := bstep (se 1 (by rfl) ⟨820079, by rfl⟩ : syracuseStep 1093439 = 1640159) B1640159
theorem B1585727 : Blo 287828 1585727 := bstep (se 1 (by rfl) ⟨1189295, by rfl⟩ : syracuseStep 1585727 = 2378591) B2378591
theorem B2077559 : Blo 287828 2077559 := bstep (se 1 (by rfl) ⟨1558169, by rfl⟩ : syracuseStep 2077559 = 3116339) B3116339
theorem B734953 : Blo 287828 734953 := bstep (se 2 (by rfl) ⟨275607, by rfl⟩ : syracuseStep 734953 = 551215) B551215
theorem B2799755 : Blo 287828 2799755 := bstep (se 1 (by rfl) ⟨2099816, by rfl⟩ : syracuseStep 2799755 = 4199633) B4199633
theorem B5585051 : Blo 287828 5585051 := bstep (se 1 (by rfl) ⟨4188788, by rfl⟩ : syracuseStep 5585051 = 8377577) B8377577
theorem B2472403 : Blo 287828 2472403 := bstep (se 1 (by rfl) ⟨1854302, by rfl⟩ : syracuseStep 2472403 = 3708605) B3708605
theorem B310127 : Blo 287828 310127 := bstep (se 1 (by rfl) ⟨232595, by rfl⟩ : syracuseStep 310127 = 465191) B465191
theorem B2636711 : Blo 287828 2636711 := bstep (se 1 (by rfl) ⟨1977533, by rfl⟩ : syracuseStep 2636711 = 3955067) B3955067
theorem B736361 : Blo 287828 736361 := bstep (se 2 (by rfl) ⟨276135, by rfl⟩ : syracuseStep 736361 = 552271) B552271
theorem B1457351 : Blo 287828 1457351 := bstep (se 1 (by rfl) ⟨1093013, by rfl⟩ : syracuseStep 1457351 = 2186027) B2186027
theorem B1195343 : Blo 287828 1195343 := bstep (se 1 (by rfl) ⟨896507, by rfl⟩ : syracuseStep 1195343 = 1793015) B1793015
theorem B1883657 : Blo 287828 1883657 := bstep (se 2 (by rfl) ⟨706371, by rfl⟩ : syracuseStep 1883657 = 1412743) B1412743
theorem B1490521 : Blo 287828 1490521 := bstep (se 2 (by rfl) ⟨558945, by rfl⟩ : syracuseStep 1490521 = 1117891) B1117891
theorem B933599 : Blo 287828 933599 := bstep (se 1 (by rfl) ⟨700199, by rfl⟩ : syracuseStep 933599 = 1400399) B1400399
theorem B2473739 : Blo 287828 2473739 := bstep (se 1 (by rfl) ⟨1855304, by rfl⟩ : syracuseStep 2473739 = 3710609) B3710609
theorem B1851281 : Blo 287828 1851281 := bstep (se 2 (by rfl) ⟨694230, by rfl⟩ : syracuseStep 1851281 = 1388461) B1388461
theorem B1654739 : Blo 287828 1654739 := bstep (se 1 (by rfl) ⟨1241054, by rfl⟩ : syracuseStep 1654739 = 2482109) B2482109
theorem B1097981 : Blo 287828 1097981 := bstep (se 3 (by rfl) ⟨205871, by rfl⟩ : syracuseStep 1097981 = 411743) B411743
theorem B1851821 : Blo 287828 1851821 := bstep (se 3 (by rfl) ⟨347216, by rfl⟩ : syracuseStep 1851821 = 694433) B694433
theorem B2638615 : Blo 287828 2638615 := bstep (se 1 (by rfl) ⟨1978961, by rfl⟩ : syracuseStep 2638615 = 3957923) B3957923
theorem B1426331 : Blo 287828 1426331 := bstep (se 1 (by rfl) ⟨1069748, by rfl⟩ : syracuseStep 1426331 = 2139497) B2139497
theorem B1098785 : Blo 287828 1098785 := bstep (se 2 (by rfl) ⟨412044, by rfl⟩ : syracuseStep 1098785 = 824089) B824089
theorem B1393787 : Blo 287828 1393787 := bstep (se 1 (by rfl) ⟨1045340, by rfl⟩ : syracuseStep 1393787 = 2090681) B2090681
theorem B2082145 : Blo 287828 2082145 := bstep (se 2 (by rfl) ⟨780804, by rfl⟩ : syracuseStep 2082145 = 1561609) B1561609
theorem B1984733 : Blo 287828 1984733 := bstep (se 3 (by rfl) ⟨372137, by rfl⟩ : syracuseStep 1984733 = 744275) B744275
theorem B1657381 : Blo 287828 1657381 := bstep (se 4 (by rfl) ⟨155379, by rfl⟩ : syracuseStep 1657381 = 310759) B310759
theorem B1100425 : Blo 287828 1100425 := bstep (se 2 (by rfl) ⟨412659, by rfl⟩ : syracuseStep 1100425 = 825319) B825319
theorem B1657655 : Blo 287828 1657655 := bstep (se 1 (by rfl) ⟨1243241, by rfl⟩ : syracuseStep 1657655 = 2486483) B2486483
theorem B2477051 : Blo 287828 2477051 := bstep (se 1 (by rfl) ⟨1857788, by rfl⟩ : syracuseStep 2477051 = 3715577) B3715577
theorem B1100897 : Blo 287828 1100897 := bstep (se 2 (by rfl) ⟨412836, by rfl⟩ : syracuseStep 1100897 = 825673) B825673
theorem B3723731 : Blo 287828 3723731 := bstep (se 1 (by rfl) ⟨2792798, by rfl⟩ : syracuseStep 3723731 = 5585597) B5585597
theorem B971675 : Blo 287828 971675 := bstep (se 1 (by rfl) ⟨728756, by rfl⟩ : syracuseStep 971675 = 1457513) B1457513
theorem B1496045 : Blo 287828 1496045 := bstep (se 3 (by rfl) ⟨280508, by rfl⟩ : syracuseStep 1496045 = 561017) B561017
theorem B1561673 : Blo 287828 1561673 := bstep (se 2 (by rfl) ⟨585627, by rfl⟩ : syracuseStep 1561673 = 1171255) B1171255
theorem B13981081 : Blo 287828 13981081 := bstep (se 2 (by rfl) ⟨5242905, by rfl⟩ : syracuseStep 13981081 = 10485811) B10485811
theorem B325998229 : Blo 287828 325998229 := bstep (se 6 (by rfl) ⟨7640583, by rfl⟩ : syracuseStep 325998229 = 15281167) B15281167
theorem B350023 : Blo 287828 350023 := bstep (se 1 (by rfl) ⟨262517, by rfl⟩ : syracuseStep 350023 = 525035) B525035
theorem B1464155 : Blo 287828 1464155 := bstep (se 1 (by rfl) ⟨1098116, by rfl⟩ : syracuseStep 1464155 = 2196233) B2196233
theorem B2676833 : Blo 287828 2676833 := bstep (se 2 (by rfl) ⟨1003812, by rfl⟩ : syracuseStep 2676833 = 2007625) B2007625
theorem B102816289 : Blo 287828 102816289 := bstep (se 2 (by rfl) ⟨38556108, by rfl⟩ : syracuseStep 102816289 = 77112217) B77112217
theorem B49109579 : Blo 287828 49109579 := bstep (se 1 (by rfl) ⟨36832184, by rfl⟩ : syracuseStep 49109579 = 73664369) B73664369
theorem B163371919 : Blo 287828 163371919 := bstep (se 1 (by rfl) ⟨122528939, by rfl⟩ : syracuseStep 163371919 = 245057879) B245057879
theorem B4677097 : Blo 287828 4677097 := bstep (se 2 (by rfl) ⟨1753911, by rfl⟩ : syracuseStep 4677097 = 3507823) B3507823
theorem B1236647 : Blo 287828 1236647 := bstep (se 1 (by rfl) ⟨927485, by rfl⟩ : syracuseStep 1236647 = 1854971) B1854971
theorem B548831 : Blo 287828 548831 := bstep (se 1 (by rfl) ⟨411623, by rfl⟩ : syracuseStep 548831 = 823247) B823247
theorem B5431499 : Blo 287828 5431499 := bstep (se 1 (by rfl) ⟨4073624, by rfl⟩ : syracuseStep 5431499 = 8147249) B8147249
theorem B549119 : Blo 287828 549119 := bstep (se 1 (by rfl) ⟨411839, by rfl⟩ : syracuseStep 549119 = 823679) B823679
theorem B1761697 : Blo 287828 1761697 := bstep (se 2 (by rfl) ⟨660636, by rfl⟩ : syracuseStep 1761697 = 1321273) B1321273
theorem B1106561 : Blo 287828 1106561 := bstep (se 2 (by rfl) ⟨414960, by rfl⟩ : syracuseStep 1106561 = 829921) B829921
theorem B975671 : Blo 287828 975671 := bstep (se 1 (by rfl) ⟨731753, by rfl⟩ : syracuseStep 975671 = 1463507) B1463507
theorem B1106743 : Blo 287828 1106743 := bstep (se 1 (by rfl) ⟨830057, by rfl⟩ : syracuseStep 1106743 = 1660115) B1660115
theorem B1107017 : Blo 287828 1107017 := bstep (se 2 (by rfl) ⟨415131, by rfl⟩ : syracuseStep 1107017 = 830263) B830263
theorem B287855 : Blo 287828 287855 := bstep (se 1 (by rfl) ⟨215891, by rfl⟩ : syracuseStep 287855 = 431783) B431783
theorem B287911 : Blo 287828 287911 := bstep (se 1 (by rfl) ⟨215933, by rfl⟩ : syracuseStep 287911 = 431867) B431867
theorem B648359 : Blo 287828 648359 := bstep (se 1 (by rfl) ⟨486269, by rfl⟩ : syracuseStep 648359 = 972539) B972539
theorem B287935 : Blo 287828 287935 := bstep (se 1 (by rfl) ⟨215951, by rfl⟩ : syracuseStep 287935 = 431903) B431903
theorem B287967 : Blo 287828 287967 := bstep (se 1 (by rfl) ⟨215975, by rfl⟩ : syracuseStep 287967 = 431951) B431951
theorem B648467 : Blo 287828 648467 := bstep (se 1 (by rfl) ⟨486350, by rfl⟩ : syracuseStep 648467 = 972701) B972701
theorem B288047 : Blo 287828 288047 := bstep (se 1 (by rfl) ⟨216035, by rfl⟩ : syracuseStep 288047 = 432071) B432071
theorem B5629459 : Blo 287828 5629459 := bstep (se 1 (by rfl) ⟨4222094, by rfl⟩ : syracuseStep 5629459 = 8444189) B8444189
theorem B288283 : Blo 287828 288283 := bstep (se 1 (by rfl) ⟨216212, by rfl⟩ : syracuseStep 288283 = 432425) B432425
theorem B288287 : Blo 287828 288287 := bstep (se 1 (by rfl) ⟨216215, by rfl⟩ : syracuseStep 288287 = 432431) B432431
theorem B550471 : Blo 287828 550471 := bstep (se 1 (by rfl) ⟨412853, by rfl⟩ : syracuseStep 550471 = 825707) B825707
theorem B288447 : Blo 287828 288447 := bstep (se 1 (by rfl) ⟨216335, by rfl⟩ : syracuseStep 288447 = 432671) B432671
theorem B2975491 : Blo 287828 2975491 := bstep (se 1 (by rfl) ⟨2231618, by rfl⟩ : syracuseStep 2975491 = 4463237) B4463237
theorem B649097 : Blo 287828 649097 := bstep (se 2 (by rfl) ⟨243411, by rfl⟩ : syracuseStep 649097 = 486823) B486823
theorem B649115 : Blo 287828 649115 := bstep (se 1 (by rfl) ⟨486836, by rfl⟩ : syracuseStep 649115 = 973673) B973673
theorem B649151 : Blo 287828 649151 := bstep (se 1 (by rfl) ⟨486863, by rfl⟩ : syracuseStep 649151 = 973727) B973727
theorem B288703 : Blo 287828 288703 := bstep (se 1 (by rfl) ⟨216527, by rfl⟩ : syracuseStep 288703 = 433055) B433055
theorem B976859 : Blo 287828 976859 := bstep (se 1 (by rfl) ⟨732644, by rfl⟩ : syracuseStep 976859 = 1465289) B1465289
theorem B288735 : Blo 287828 288735 := bstep (se 1 (by rfl) ⟨216551, by rfl⟩ : syracuseStep 288735 = 433103) B433103
theorem B616427 : Blo 287828 616427 := bstep (se 1 (by rfl) ⟨462320, by rfl⟩ : syracuseStep 616427 = 924641) B924641
theorem B288795 : Blo 287828 288795 := bstep (se 1 (by rfl) ⟨216596, by rfl⟩ : syracuseStep 288795 = 433193) B433193
theorem B288799 : Blo 287828 288799 := bstep (se 1 (by rfl) ⟨216599, by rfl⟩ : syracuseStep 288799 = 433199) B433199
theorem B288815 : Blo 287828 288815 := bstep (se 1 (by rfl) ⟨216611, by rfl⟩ : syracuseStep 288815 = 433223) B433223
theorem B649313 : Blo 287828 649313 := bstep (se 2 (by rfl) ⟨243492, by rfl⟩ : syracuseStep 649313 = 486985) B486985
theorem B551033 : Blo 287828 551033 := bstep (se 2 (by rfl) ⟨206637, by rfl⟩ : syracuseStep 551033 = 413275) B413275
theorem B288991 : Blo 287828 288991 := bstep (se 1 (by rfl) ⟨216743, by rfl⟩ : syracuseStep 288991 = 433487) B433487
theorem B977129 : Blo 287828 977129 := bstep (se 2 (by rfl) ⟨366423, by rfl⟩ : syracuseStep 977129 = 732847) B732847
theorem B289051 : Blo 287828 289051 := bstep (se 1 (by rfl) ⟨216788, by rfl⟩ : syracuseStep 289051 = 433577) B433577
theorem B289151 : Blo 287828 289151 := bstep (se 1 (by rfl) ⟨216863, by rfl⟩ : syracuseStep 289151 = 433727) B433727
theorem B977399 : Blo 287828 977399 := bstep (se 1 (by rfl) ⟨733049, by rfl⟩ : syracuseStep 977399 = 1466099) B1466099
theorem B289327 : Blo 287828 289327 := bstep (se 1 (by rfl) ⟨216995, by rfl⟩ : syracuseStep 289327 = 433991) B433991
theorem B10644047 : Blo 287828 10644047 := bstep (se 1 (by rfl) ⟨7983035, by rfl⟩ : syracuseStep 10644047 = 15966071) B15966071
theorem B289383 : Blo 287828 289383 := bstep (se 1 (by rfl) ⟨217037, by rfl⟩ : syracuseStep 289383 = 434075) B434075
theorem B977561 : Blo 287828 977561 := bstep (se 2 (by rfl) ⟨366585, by rfl⟩ : syracuseStep 977561 = 733171) B733171
theorem B19098305 : Blo 287828 19098305 := bstep (se 2 (by rfl) ⟨7161864, by rfl⟩ : syracuseStep 19098305 = 14323729) B14323729
theorem B289759 : Blo 287828 289759 := bstep (se 1 (by rfl) ⟨217319, by rfl⟩ : syracuseStep 289759 = 434639) B434639
theorem B289787 : Blo 287828 289787 := bstep (se 1 (by rfl) ⟨217340, by rfl⟩ : syracuseStep 289787 = 434681) B434681
theorem B289855 : Blo 287828 289855 := bstep (se 1 (by rfl) ⟨217391, by rfl⟩ : syracuseStep 289855 = 434783) B434783
theorem B977993 : Blo 287828 977993 := bstep (se 2 (by rfl) ⟨366747, by rfl⟩ : syracuseStep 977993 = 733495) B733495
theorem B290175 : Blo 287828 290175 := bstep (se 1 (by rfl) ⟨217631, by rfl⟩ : syracuseStep 290175 = 435263) B435263
theorem B290203 : Blo 287828 290203 := bstep (se 1 (by rfl) ⟨217652, by rfl⟩ : syracuseStep 290203 = 435305) B435305
theorem B650663 : Blo 287828 650663 := bstep (se 1 (by rfl) ⟨487997, by rfl⟩ : syracuseStep 650663 = 975995) B975995
theorem B7466417 : Blo 287828 7466417 := bstep (se 2 (by rfl) ⟨2799906, by rfl⟩ : syracuseStep 7466417 = 5599813) B5599813
theorem B290271 : Blo 287828 290271 := bstep (se 1 (by rfl) ⟨217703, by rfl⟩ : syracuseStep 290271 = 435407) B435407
theorem B552415 : Blo 287828 552415 := bstep (se 1 (by rfl) ⟨414311, by rfl⟩ : syracuseStep 552415 = 828623) B828623
theorem B650843 : Blo 287828 650843 := bstep (se 1 (by rfl) ⟨488132, by rfl⟩ : syracuseStep 650843 = 976265) B976265
theorem B290407 : Blo 287828 290407 := bstep (se 1 (by rfl) ⟨217805, by rfl⟩ : syracuseStep 290407 = 435611) B435611
theorem B552673 : Blo 287828 552673 := bstep (se 2 (by rfl) ⟨207252, by rfl⟩ : syracuseStep 552673 = 414505) B414505
theorem B290555 : Blo 287828 290555 := bstep (se 1 (by rfl) ⟨217916, by rfl⟩ : syracuseStep 290555 = 435833) B435833
theorem B290623 : Blo 287828 290623 := bstep (se 1 (by rfl) ⟨217967, by rfl⟩ : syracuseStep 290623 = 435935) B435935
theorem B1240919 : Blo 287828 1240919 := bstep (se 1 (by rfl) ⟨930689, by rfl⟩ : syracuseStep 1240919 = 1861379) B1861379
theorem B290687 : Blo 287828 290687 := bstep (se 1 (by rfl) ⟨218015, by rfl⟩ : syracuseStep 290687 = 436031) B436031
theorem B290799 : Blo 287828 290799 := bstep (se 1 (by rfl) ⟨218099, by rfl⟩ : syracuseStep 290799 = 436199) B436199
theorem B487417 : Blo 287828 487417 := bstep (se 2 (by rfl) ⟨182781, by rfl⟩ : syracuseStep 487417 = 365563) B365563
theorem B651257 : Blo 287828 651257 := bstep (se 2 (by rfl) ⟨244221, by rfl⟩ : syracuseStep 651257 = 488443) B488443
theorem B290811 : Blo 287828 290811 := bstep (se 1 (by rfl) ⟨218108, by rfl⟩ : syracuseStep 290811 = 436217) B436217
theorem B290879 : Blo 287828 290879 := bstep (se 1 (by rfl) ⟨218159, by rfl⟩ : syracuseStep 290879 = 436319) B436319
theorem B651347 : Blo 287828 651347 := bstep (se 1 (by rfl) ⟨488510, by rfl⟩ : syracuseStep 651347 = 977021) B977021
theorem B290919 : Blo 287828 290919 := bstep (se 1 (by rfl) ⟨218189, by rfl⟩ : syracuseStep 290919 = 436379) B436379
theorem B290943 : Blo 287828 290943 := bstep (se 1 (by rfl) ⟨218207, by rfl⟩ : syracuseStep 290943 = 436415) B436415
theorem B290971 : Blo 287828 290971 := bstep (se 1 (by rfl) ⟨218228, by rfl⟩ : syracuseStep 290971 = 436457) B436457
theorem B487687 : Blo 287828 487687 := bstep (se 1 (by rfl) ⟨365765, by rfl⟩ : syracuseStep 487687 = 731531) B731531
theorem B651527 : Blo 287828 651527 := bstep (se 1 (by rfl) ⟨488645, by rfl⟩ : syracuseStep 651527 = 977291) B977291
theorem B291175 : Blo 287828 291175 := bstep (se 1 (by rfl) ⟨218381, by rfl⟩ : syracuseStep 291175 = 436763) B436763
theorem B323995 : Blo 287828 323995 := bstep (se 1 (by rfl) ⟨242996, by rfl⟩ : syracuseStep 323995 = 485993) B485993
theorem B291227 : Blo 287828 291227 := bstep (se 1 (by rfl) ⟨218420, by rfl⟩ : syracuseStep 291227 = 436841) B436841
theorem B2191859 : Blo 287828 2191859 := bstep (se 1 (by rfl) ⟨1643894, by rfl⟩ : syracuseStep 2191859 = 3287789) B3287789
theorem B979451 : Blo 287828 979451 := bstep (se 1 (by rfl) ⟨734588, by rfl⟩ : syracuseStep 979451 = 1469177) B1469177
theorem B651833 : Blo 287828 651833 := bstep (se 2 (by rfl) ⟨244437, by rfl⟩ : syracuseStep 651833 = 488875) B488875
theorem B291579 : Blo 287828 291579 := bstep (se 1 (by rfl) ⟨218684, by rfl⟩ : syracuseStep 291579 = 437369) B437369
theorem B979721 : Blo 287828 979721 := bstep (se 2 (by rfl) ⟨367395, by rfl⟩ : syracuseStep 979721 = 734791) B734791
theorem B291647 : Blo 287828 291647 := bstep (se 1 (by rfl) ⟨218735, by rfl⟩ : syracuseStep 291647 = 437471) B437471
theorem B291675 : Blo 287828 291675 := bstep (se 1 (by rfl) ⟨218756, by rfl⟩ : syracuseStep 291675 = 437513) B437513
theorem B291743 : Blo 287828 291743 := bstep (se 1 (by rfl) ⟨218807, by rfl⟩ : syracuseStep 291743 = 437615) B437615
theorem B291823 : Blo 287828 291823 := bstep (se 1 (by rfl) ⟨218867, by rfl⟩ : syracuseStep 291823 = 437735) B437735
theorem B324679 : Blo 287828 324679 := bstep (se 1 (by rfl) ⟨243509, by rfl⟩ : syracuseStep 324679 = 487019) B487019
theorem B324859 : Blo 287828 324859 := bstep (se 1 (by rfl) ⟨243644, by rfl⟩ : syracuseStep 324859 = 487289) B487289
theorem B488713 : Blo 287828 488713 := bstep (se 2 (by rfl) ⟨183267, by rfl⟩ : syracuseStep 488713 = 366535) B366535
theorem B652553 : Blo 287828 652553 := bstep (se 2 (by rfl) ⟨244707, by rfl⟩ : syracuseStep 652553 = 489415) B489415
theorem B488767 : Blo 287828 488767 := bstep (se 1 (by rfl) ⟨366575, by rfl⟩ : syracuseStep 488767 = 733151) B733151
theorem B652607 : Blo 287828 652607 := bstep (se 1 (by rfl) ⟨489455, by rfl⟩ : syracuseStep 652607 = 978911) B978911
theorem B1701287 : Blo 287828 1701287 := bstep (se 1 (by rfl) ⟨1275965, by rfl⟩ : syracuseStep 1701287 = 2551931) B2551931
theorem B652715 : Blo 287828 652715 := bstep (se 1 (by rfl) ⟨489536, by rfl⟩ : syracuseStep 652715 = 979073) B979073
theorem B489199 : Blo 287828 489199 := bstep (se 1 (by rfl) ⟨366899, by rfl⟩ : syracuseStep 489199 = 733799) B733799
theorem B653039 : Blo 287828 653039 := bstep (se 1 (by rfl) ⟨489779, by rfl⟩ : syracuseStep 653039 = 979559) B979559
theorem B2193317 : Blo 287828 2193317 := bstep (se 4 (by rfl) ⟨205623, by rfl⟩ : syracuseStep 2193317 = 411247) B411247
theorem B653255 : Blo 287828 653255 := bstep (se 1 (by rfl) ⟨489941, by rfl⟩ : syracuseStep 653255 = 979883) B979883
theorem B2291915 : Blo 287828 2291915 := bstep (se 1 (by rfl) ⟨1718936, by rfl⟩ : syracuseStep 2291915 = 3437873) B3437873
theorem B653543 : Blo 287828 653543 := bstep (se 1 (by rfl) ⟨490157, by rfl⟩ : syracuseStep 653543 = 980315) B980315
theorem B653561 : Blo 287828 653561 := bstep (se 2 (by rfl) ⟨245085, by rfl⟩ : syracuseStep 653561 = 490171) B490171
theorem B653615 : Blo 287828 653615 := bstep (se 1 (by rfl) ⟨490211, by rfl⟩ : syracuseStep 653615 = 980423) B980423
theorem B326047 : Blo 287828 326047 := bstep (se 1 (by rfl) ⟨244535, by rfl⟩ : syracuseStep 326047 = 489071) B489071
theorem B489935 : Blo 287828 489935 := bstep (se 1 (by rfl) ⟨367451, by rfl⟩ : syracuseStep 489935 = 734903) B734903
theorem B326119 : Blo 287828 326119 := bstep (se 1 (by rfl) ⟨244589, by rfl⟩ : syracuseStep 326119 = 489179) B489179
theorem B653831 : Blo 287828 653831 := bstep (se 1 (by rfl) ⟨490373, by rfl⟩ : syracuseStep 653831 = 980747) B980747
theorem B1473065 : Blo 287828 1473065 := bstep (se 2 (by rfl) ⟨552399, by rfl⟩ : syracuseStep 1473065 = 1104799) B1104799
theorem B654011 : Blo 287828 654011 := bstep (se 1 (by rfl) ⟨490508, by rfl⟩ : syracuseStep 654011 = 981017) B981017
theorem B1473389 : Blo 287828 1473389 := bstep (se 3 (by rfl) ⟨276260, by rfl⟩ : syracuseStep 1473389 = 552521) B552521
theorem B1047775 : Blo 287828 1047775 := bstep (se 1 (by rfl) ⟨785831, by rfl⟩ : syracuseStep 1047775 = 1571663) B1571663
theorem B326983 : Blo 287828 326983 := bstep (se 1 (by rfl) ⟨245237, by rfl⟩ : syracuseStep 326983 = 490475) B490475
theorem B654911 : Blo 287828 654911 := bstep (se 1 (by rfl) ⟨491183, by rfl⟩ : syracuseStep 654911 = 982367) B982367
theorem B491231 : Blo 287828 491231 := bstep (se 1 (by rfl) ⟨368423, by rfl⟩ : syracuseStep 491231 = 736847) B736847
theorem B1048295 : Blo 287828 1048295 := bstep (se 1 (by rfl) ⟨786221, by rfl⟩ : syracuseStep 1048295 = 1572443) B1572443
theorem B1179431 : Blo 287828 1179431 := bstep (se 1 (by rfl) ⟨884573, by rfl⟩ : syracuseStep 1179431 = 1769147) B1769147
theorem B1245071 : Blo 287828 1245071 := bstep (se 1 (by rfl) ⟨933803, by rfl⟩ : syracuseStep 1245071 = 1867607) B1867607
theorem B655271 : Blo 287828 655271 := bstep (se 1 (by rfl) ⟨491453, by rfl⟩ : syracuseStep 655271 = 982907) B982907
theorem B1245223 : Blo 287828 1245223 := bstep (se 1 (by rfl) ⟨933917, by rfl⟩ : syracuseStep 1245223 = 1867835) B1867835
theorem B983339 : Blo 287828 983339 := bstep (se 1 (by rfl) ⟨737504, by rfl⟩ : syracuseStep 983339 = 1475009) B1475009
theorem B655775 : Blo 287828 655775 := bstep (se 1 (by rfl) ⟨491831, by rfl⟩ : syracuseStep 655775 = 983663) B983663
theorem B950887 : Blo 287828 950887 := bstep (se 1 (by rfl) ⟨713165, by rfl⟩ : syracuseStep 950887 = 1426331) B1426331
theorem B1475657 : Blo 287828 1475657 := bstep (se 2 (by rfl) ⟨553371, by rfl⟩ : syracuseStep 1475657 = 1106743) B1106743
theorem B4588919 : Blo 287828 4588919 := bstep (se 1 (by rfl) ⟨3441689, by rfl⟩ : syracuseStep 4588919 = 6883379) B6883379
theorem B1574603 : Blo 287828 1574603 := bstep (se 1 (by rfl) ⟨1180952, by rfl⟩ : syracuseStep 1574603 = 2361905) B2361905
theorem B984851 : Blo 287828 984851 := bstep (se 1 (by rfl) ⟨738638, by rfl⟩ : syracuseStep 984851 = 1477277) B1477277
theorem B788363 : Blo 287828 788363 := bstep (se 1 (by rfl) ⟨591272, by rfl⟩ : syracuseStep 788363 = 1182545) B1182545
theorem B1640411 : Blo 287828 1640411 := bstep (se 1 (by rfl) ⟨1230308, by rfl⟩ : syracuseStep 1640411 = 2460617) B2460617
theorem B7505945 : Blo 287828 7505945 := bstep (se 2 (by rfl) ⟨2814729, by rfl⟩ : syracuseStep 7505945 = 5629459) B5629459
theorem B3967321 : Blo 287828 3967321 := bstep (se 2 (by rfl) ⟨1487745, by rfl⟩ : syracuseStep 3967321 = 2975491) B2975491
theorem B2853625 : Blo 287828 2853625 := bstep (se 2 (by rfl) ⟨1070109, by rfl⟩ : syracuseStep 2853625 = 2140219) B2140219
theorem B10488997 : Blo 287828 10488997 := bstep (se 4 (by rfl) ⟨983343, by rfl⟩ : syracuseStep 10488997 = 1966687) B1966687
theorem B3280499 : Blo 287828 3280499 := bstep (se 1 (by rfl) ⟨2460374, by rfl⟩ : syracuseStep 3280499 = 4920749) B4920749
theorem B32739719 : Blo 287828 32739719 := bstep (se 1 (by rfl) ⟨24554789, by rfl⟩ : syracuseStep 32739719 = 49109579) B49109579
theorem B824431 : Blo 287828 824431 := bstep (se 1 (by rfl) ⟨618323, by rfl⟩ : syracuseStep 824431 = 1236647) B1236647
theorem B365887 : Blo 287828 365887 := bstep (se 1 (by rfl) ⟨274415, by rfl⟩ : syracuseStep 365887 = 548831) B548831
theorem B923051 : Blo 287828 923051 := bstep (se 1 (by rfl) ⟨692288, by rfl⟩ : syracuseStep 923051 = 1384577) B1384577
theorem B431993 : Blo 287828 431993 := bstep (se 2 (by rfl) ⟨161997, by rfl⟩ : syracuseStep 431993 = 323995) B323995
theorem B2365537 : Blo 287828 2365537 := bstep (se 2 (by rfl) ⟨887076, by rfl⟩ : syracuseStep 2365537 = 1774153) B1774153
theorem B432239 : Blo 287828 432239 := bstep (se 1 (by rfl) ⟨324179, by rfl⟩ : syracuseStep 432239 = 648359) B648359
theorem B9443465 : Blo 287828 9443465 := bstep (se 2 (by rfl) ⟨3541299, by rfl⟩ : syracuseStep 9443465 = 7082599) B7082599
theorem B923795 : Blo 287828 923795 := bstep (se 1 (by rfl) ⟨692846, by rfl⟩ : syracuseStep 923795 = 1385693) B1385693
theorem B432311 : Blo 287828 432311 := bstep (se 1 (by rfl) ⟨324233, by rfl⟩ : syracuseStep 432311 = 648467) B648467
theorem B432731 : Blo 287828 432731 := bstep (se 1 (by rfl) ⟨324548, by rfl⟩ : syracuseStep 432731 = 649097) B649097
theorem B432743 : Blo 287828 432743 := bstep (se 1 (by rfl) ⟨324557, by rfl⟩ : syracuseStep 432743 = 649115) B649115
theorem B432767 : Blo 287828 432767 := bstep (se 1 (by rfl) ⟨324575, by rfl⟩ : syracuseStep 432767 = 649151) B649151
theorem B432875 : Blo 287828 432875 := bstep (se 1 (by rfl) ⟨324656, by rfl⟩ : syracuseStep 432875 = 649313) B649313
theorem B367355 : Blo 287828 367355 := bstep (se 1 (by rfl) ⟨275516, by rfl⟩ : syracuseStep 367355 = 551033) B551033
theorem B432905 : Blo 287828 432905 := bstep (se 2 (by rfl) ⟨162339, by rfl⟩ : syracuseStep 432905 = 324679) B324679
theorem B433145 : Blo 287828 433145 := bstep (se 2 (by rfl) ⟨162429, by rfl⟩ : syracuseStep 433145 = 324859) B324859
theorem B1645991 : Blo 287828 1645991 := bstep (se 1 (by rfl) ⟨1234493, by rfl⟩ : syracuseStep 1645991 = 2468987) B2468987
theorem B433775 : Blo 287828 433775 := bstep (se 1 (by rfl) ⟨325331, by rfl⟩ : syracuseStep 433775 = 650663) B650663
theorem B827005 : Blo 287828 827005 := bstep (se 3 (by rfl) ⟨155063, by rfl⟩ : syracuseStep 827005 = 310127) B310127
theorem B728747 : Blo 287828 728747 := bstep (se 1 (by rfl) ⟨546560, by rfl⟩ : syracuseStep 728747 = 1093121) B1093121
theorem B433895 : Blo 287828 433895 := bstep (se 1 (by rfl) ⟨325421, by rfl⟩ : syracuseStep 433895 = 650843) B650843
theorem B466697 : Blo 287828 466697 := bstep (se 2 (by rfl) ⟨175011, by rfl⟩ : syracuseStep 466697 = 350023) B350023
theorem B728959 : Blo 287828 728959 := bstep (se 1 (by rfl) ⟨546719, by rfl⟩ : syracuseStep 728959 = 1093439) B1093439
theorem B827279 : Blo 287828 827279 := bstep (se 1 (by rfl) ⟨620459, by rfl⟩ : syracuseStep 827279 = 1240919) B1240919
theorem B434171 : Blo 287828 434171 := bstep (se 1 (by rfl) ⟨325628, by rfl⟩ : syracuseStep 434171 = 651257) B651257
theorem B434231 : Blo 287828 434231 := bstep (se 1 (by rfl) ⟨325673, by rfl⟩ : syracuseStep 434231 = 651347) B651347
theorem B434351 : Blo 287828 434351 := bstep (se 1 (by rfl) ⟨325763, by rfl⟩ : syracuseStep 434351 = 651527) B651527
theorem B434555 : Blo 287828 434555 := bstep (se 1 (by rfl) ⟨325916, by rfl⟩ : syracuseStep 434555 = 651833) B651833
theorem B1057151 : Blo 287828 1057151 := bstep (se 1 (by rfl) ⟨792863, by rfl⟩ : syracuseStep 1057151 = 1585727) B1585727
theorem B434729 : Blo 287828 434729 := bstep (se 2 (by rfl) ⟨163023, by rfl⟩ : syracuseStep 434729 = 326047) B326047
theorem B1385039 : Blo 287828 1385039 := bstep (se 1 (by rfl) ⟨1038779, by rfl⟩ : syracuseStep 1385039 = 2077559) B2077559
theorem B434825 : Blo 287828 434825 := bstep (se 2 (by rfl) ⟨163059, by rfl⟩ : syracuseStep 434825 = 326119) B326119
theorem B435035 : Blo 287828 435035 := bstep (se 1 (by rfl) ⟨326276, by rfl⟩ : syracuseStep 435035 = 652553) B652553
theorem B435071 : Blo 287828 435071 := bstep (se 1 (by rfl) ⟨326303, by rfl⟩ : syracuseStep 435071 = 652607) B652607
theorem B435143 : Blo 287828 435143 := bstep (se 1 (by rfl) ⟨326357, by rfl⟩ : syracuseStep 435143 = 652715) B652715
theorem B435359 : Blo 287828 435359 := bstep (se 1 (by rfl) ⟨326519, by rfl⟩ : syracuseStep 435359 = 653039) B653039
theorem B435503 : Blo 287828 435503 := bstep (se 1 (by rfl) ⟨326627, by rfl⟩ : syracuseStep 435503 = 653255) B653255
theorem B435695 : Blo 287828 435695 := bstep (se 1 (by rfl) ⟨326771, by rfl⟩ : syracuseStep 435695 = 653543) B653543
theorem B435707 : Blo 287828 435707 := bstep (se 1 (by rfl) ⟨326780, by rfl⟩ : syracuseStep 435707 = 653561) B653561
theorem B435743 : Blo 287828 435743 := bstep (se 1 (by rfl) ⟨326807, by rfl⟩ : syracuseStep 435743 = 653615) B653615
theorem B435887 : Blo 287828 435887 := bstep (se 1 (by rfl) ⟨326915, by rfl⟩ : syracuseStep 435887 = 653831) B653831
theorem B435977 : Blo 287828 435977 := bstep (se 2 (by rfl) ⟨163491, by rfl⟩ : syracuseStep 435977 = 326983) B326983
theorem B436007 : Blo 287828 436007 := bstep (se 1 (by rfl) ⟨327005, by rfl⟩ : syracuseStep 436007 = 654011) B654011
theorem B6236129 : Blo 287828 6236129 := bstep (se 2 (by rfl) ⟨2338548, by rfl⟩ : syracuseStep 6236129 = 4677097) B4677097
theorem B796895 : Blo 287828 796895 := bstep (se 1 (by rfl) ⟨597671, by rfl⟩ : syracuseStep 796895 = 1195343) B1195343
theorem B1255771 : Blo 287828 1255771 := bstep (se 1 (by rfl) ⟨941828, by rfl⟩ : syracuseStep 1255771 = 1883657) B1883657
theorem B436607 : Blo 287828 436607 := bstep (se 1 (by rfl) ⟨327455, by rfl⟩ : syracuseStep 436607 = 654911) B654911
theorem B698863 : Blo 287828 698863 := bstep (se 1 (by rfl) ⟨524147, by rfl⟩ : syracuseStep 698863 = 1048295) B1048295
theorem B1649159 : Blo 287828 1649159 := bstep (se 1 (by rfl) ⟨1236869, by rfl⟩ : syracuseStep 1649159 = 2473739) B2473739
theorem B830047 : Blo 287828 830047 := bstep (se 1 (by rfl) ⟨622535, by rfl⟩ : syracuseStep 830047 = 1245071) B1245071
theorem B436847 : Blo 287828 436847 := bstep (se 1 (by rfl) ⟨327635, by rfl⟩ : syracuseStep 436847 = 655271) B655271
theorem B437063 : Blo 287828 437063 := bstep (se 1 (by rfl) ⟨327797, by rfl⟩ : syracuseStep 437063 = 655595) B655595
theorem B731987 : Blo 287828 731987 := bstep (se 1 (by rfl) ⟨548990, by rfl⟩ : syracuseStep 731987 = 1097981) B1097981
theorem B732523 : Blo 287828 732523 := bstep (se 1 (by rfl) ⟨549392, by rfl⟩ : syracuseStep 732523 = 1098785) B1098785
theorem B437663 : Blo 287828 437663 := bstep (se 1 (by rfl) ⟨328247, by rfl⟩ : syracuseStep 437663 = 656495) B656495
theorem B929191 : Blo 287828 929191 := bstep (se 1 (by rfl) ⟨696893, by rfl⟩ : syracuseStep 929191 = 1393787) B1393787
theorem B3518153 : Blo 287828 3518153 := bstep (se 2 (by rfl) ⟨1319307, by rfl⟩ : syracuseStep 3518153 = 2638615) B2638615
theorem B1323155 : Blo 287828 1323155 := bstep (se 1 (by rfl) ⟨992366, by rfl⟩ : syracuseStep 1323155 = 1984733) B1984733
theorem B438527 : Blo 287828 438527 := bstep (se 1 (by rfl) ⟨328895, by rfl⟩ : syracuseStep 438527 = 657791) B657791
theorem B1093895 : Blo 287828 1093895 := bstep (se 1 (by rfl) ⟨820421, by rfl⟩ : syracuseStep 1093895 = 1640843) B1640843
theorem B1651367 : Blo 287828 1651367 := bstep (se 1 (by rfl) ⟨1238525, by rfl⟩ : syracuseStep 1651367 = 2477051) B2477051
theorem B307919 : Blo 287828 307919 := bstep (se 1 (by rfl) ⟨230939, by rfl⟩ : syracuseStep 307919 = 461879) B461879
theorem B733931 : Blo 287828 733931 := bstep (se 1 (by rfl) ⟨550448, by rfl⟩ : syracuseStep 733931 = 1100897) B1100897
theorem B733961 : Blo 287828 733961 := bstep (se 2 (by rfl) ⟨275235, by rfl⟩ : syracuseStep 733961 = 550471) B550471
theorem B1848257 : Blo 287828 1848257 := bstep (se 2 (by rfl) ⟨693096, by rfl⟩ : syracuseStep 1848257 = 1386193) B1386193
theorem B15774695 : Blo 287828 15774695 := bstep (se 1 (by rfl) ⟨11831021, by rfl⟩ : syracuseStep 15774695 = 23662043) B23662043
theorem B3290705 : Blo 287828 3290705 := bstep (se 2 (by rfl) ⟨1234014, by rfl⟩ : syracuseStep 3290705 = 2468029) B2468029
theorem B6600503 : Blo 287828 6600503 := bstep (se 1 (by rfl) ⟨4950377, by rfl⟩ : syracuseStep 6600503 = 9900755) B9900755
theorem B997363 : Blo 287828 997363 := bstep (se 1 (by rfl) ⟨748022, by rfl⟩ : syracuseStep 997363 = 1496045) B1496045
theorem B2209841 : Blo 287828 2209841 := bstep (se 2 (by rfl) ⟨828690, by rfl⟩ : syracuseStep 2209841 = 1657381) B1657381
theorem B1784555 : Blo 287828 1784555 := bstep (se 1 (by rfl) ⟨1338416, by rfl⟩ : syracuseStep 1784555 = 2676833) B2676833
theorem B1751969 : Blo 287828 1751969 := bstep (se 2 (by rfl) ⟨656988, by rfl⟩ : syracuseStep 1751969 = 1313977) B1313977
theorem B736553 : Blo 287828 736553 := bstep (se 2 (by rfl) ⟨276207, by rfl⟩ : syracuseStep 736553 = 552415) B552415
theorem B736897 : Blo 287828 736897 := bstep (se 2 (by rfl) ⟨276336, by rfl⟩ : syracuseStep 736897 = 552673) B552673
theorem B3620999 : Blo 287828 3620999 := bstep (se 1 (by rfl) ⟨2715749, by rfl⟩ : syracuseStep 3620999 = 5431499) B5431499
theorem B737707 : Blo 287828 737707 := bstep (se 1 (by rfl) ⟨553280, by rfl⟩ : syracuseStep 737707 = 1106561) B1106561
theorem B2998781 : Blo 287828 2998781 := bstep (se 3 (by rfl) ⟨562271, by rfl⟩ : syracuseStep 2998781 = 1124543) B1124543
theorem B6111773 : Blo 287828 6111773 := bstep (se 3 (by rfl) ⟨1145957, by rfl⟩ : syracuseStep 6111773 = 2291915) B2291915
theorem B2802215 : Blo 287828 2802215 := bstep (se 1 (by rfl) ⟨2101661, by rfl⟩ : syracuseStep 2802215 = 4203323) B4203323
theorem B738011 : Blo 287828 738011 := bstep (se 1 (by rfl) ⟨553508, by rfl⟩ : syracuseStep 738011 = 1107017) B1107017
theorem B410951 : Blo 287828 410951 := bstep (se 1 (by rfl) ⟨308213, by rfl⟩ : syracuseStep 410951 = 616427) B616427
theorem B7096031 : Blo 287828 7096031 := bstep (se 1 (by rfl) ⟨5322023, by rfl⟩ : syracuseStep 7096031 = 10644047) B10644047
theorem B12732203 : Blo 287828 12732203 := bstep (se 1 (by rfl) ⟨9549152, by rfl⟩ : syracuseStep 12732203 = 19098305) B19098305
theorem B1461239 : Blo 287828 1461239 := bstep (se 1 (by rfl) ⟨1095929, by rfl⟩ : syracuseStep 1461239 = 2191859) B2191859
theorem B3296537 : Blo 287828 3296537 := bstep (se 2 (by rfl) ⟨1236201, by rfl⟩ : syracuseStep 3296537 = 2472403) B2472403
theorem B137088385 : Blo 287828 137088385 := bstep (se 2 (by rfl) ⟨51408144, by rfl⟩ : syracuseStep 137088385 = 102816289) B102816289
theorem B1134191 : Blo 287828 1134191 := bstep (se 1 (by rfl) ⟨850643, by rfl⟩ : syracuseStep 1134191 = 1701287) B1701287
theorem B217829225 : Blo 287828 217829225 := bstep (se 2 (by rfl) ⟨81685959, by rfl⟩ : syracuseStep 217829225 = 163371919) B163371919
theorem B1462211 : Blo 287828 1462211 := bstep (se 1 (by rfl) ⟨1096658, by rfl⟩ : syracuseStep 1462211 = 2193317) B2193317
theorem B3723367 : Blo 287828 3723367 := bstep (se 1 (by rfl) ⟨2792525, by rfl⟩ : syracuseStep 3723367 = 5585051) B5585051
theorem B1397033 : Blo 287828 1397033 := bstep (se 2 (by rfl) ⟨523887, by rfl⟩ : syracuseStep 1397033 = 1047775) B1047775
theorem B1757807 : Blo 287828 1757807 := bstep (se 1 (by rfl) ⟨1318355, by rfl⟩ : syracuseStep 1757807 = 2636711) B2636711
theorem B1987361 : Blo 287828 1987361 := bstep (se 2 (by rfl) ⟨745260, by rfl⟩ : syracuseStep 1987361 = 1490521) B1490521
theorem B971567 : Blo 287828 971567 := bstep (se 1 (by rfl) ⟨728675, by rfl⟩ : syracuseStep 971567 = 1457351) B1457351
theorem B1234187 : Blo 287828 1234187 := bstep (se 1 (by rfl) ⟨925640, by rfl⟩ : syracuseStep 1234187 = 1851281) B1851281
theorem B1103159 : Blo 287828 1103159 := bstep (se 1 (by rfl) ⟨827369, by rfl⟩ : syracuseStep 1103159 = 1654739) B1654739
theorem B1234547 : Blo 287828 1234547 := bstep (se 1 (by rfl) ⟨925910, by rfl⟩ : syracuseStep 1234547 = 1851821) B1851821
theorem B2348929 : Blo 287828 2348929 := bstep (se 2 (by rfl) ⟨880848, by rfl⟩ : syracuseStep 2348929 = 1761697) B1761697
theorem B1464317 : Blo 287828 1464317 := bstep (se 3 (by rfl) ⟨274559, by rfl⟩ : syracuseStep 1464317 = 549119) B549119
theorem B546887 : Blo 287828 546887 := bstep (se 1 (by rfl) ⟨410165, by rfl⟩ : syracuseStep 546887 = 820331) B820331
theorem B350335 : Blo 287828 350335 := bstep (se 1 (by rfl) ⟨262751, by rfl⟩ : syracuseStep 350335 = 525503) B525503
theorem B18766511 : Blo 287828 18766511 := bstep (se 1 (by rfl) ⟨14074883, by rfl⟩ : syracuseStep 18766511 = 28149767) B28149767
theorem B1104617 : Blo 287828 1104617 := bstep (se 2 (by rfl) ⟨414231, by rfl⟩ : syracuseStep 1104617 = 828463) B828463
theorem B1399841 : Blo 287828 1399841 := bstep (se 2 (by rfl) ⟨524940, by rfl⟩ : syracuseStep 1399841 = 1049881) B1049881
theorem B2776193 : Blo 287828 2776193 := bstep (se 2 (by rfl) ⟨1041072, by rfl⟩ : syracuseStep 2776193 = 2082145) B2082145
theorem B1105103 : Blo 287828 1105103 := bstep (se 1 (by rfl) ⟨828827, by rfl⟩ : syracuseStep 1105103 = 1657655) B1657655
theorem B1465775 : Blo 287828 1465775 := bstep (se 1 (by rfl) ⟨1099331, by rfl⟩ : syracuseStep 1465775 = 2198663) B2198663
theorem B876521 : Blo 287828 876521 := bstep (se 2 (by rfl) ⟨328695, by rfl⟩ : syracuseStep 876521 = 657391) B657391
theorem B2482487 : Blo 287828 2482487 := bstep (se 1 (by rfl) ⟨1861865, by rfl⟩ : syracuseStep 2482487 = 3723731) B3723731
theorem B647783 : Blo 287828 647783 := bstep (se 1 (by rfl) ⟨485837, by rfl⟩ : syracuseStep 647783 = 971675) B971675
theorem B1041115 : Blo 287828 1041115 := bstep (se 1 (by rfl) ⟨780836, by rfl⟩ : syracuseStep 1041115 = 1561673) B1561673
theorem B1467233 : Blo 287828 1467233 := bstep (se 2 (by rfl) ⟨550212, by rfl⟩ : syracuseStep 1467233 = 1100425) B1100425
theorem B287835 : Blo 287828 287835 := bstep (se 1 (by rfl) ⟨215876, by rfl⟩ : syracuseStep 287835 = 431753) B431753
theorem B287847 : Blo 287828 287847 := bstep (se 1 (by rfl) ⟨215885, by rfl⟩ : syracuseStep 287847 = 431771) B431771
theorem B287975 : Blo 287828 287975 := bstep (se 1 (by rfl) ⟨215981, by rfl⟩ : syracuseStep 287975 = 431963) B431963
theorem B976103 : Blo 287828 976103 := bstep (se 1 (by rfl) ⟨732077, by rfl⟩ : syracuseStep 976103 = 1464155) B1464155
theorem B288231 : Blo 287828 288231 := bstep (se 1 (by rfl) ⟨216173, by rfl⟩ : syracuseStep 288231 = 432347) B432347
theorem B288411 : Blo 287828 288411 := bstep (se 1 (by rfl) ⟨216308, by rfl⟩ : syracuseStep 288411 = 432617) B432617
theorem B288671 : Blo 287828 288671 := bstep (se 1 (by rfl) ⟨216503, by rfl⟩ : syracuseStep 288671 = 433007) B433007
theorem B288679 : Blo 287828 288679 := bstep (se 1 (by rfl) ⟨216509, by rfl⟩ : syracuseStep 288679 = 433019) B433019
theorem B1993079 : Blo 287828 1993079 := bstep (se 1 (by rfl) ⟨1494809, by rfl⟩ : syracuseStep 1993079 = 2989619) B2989619
theorem B289255 : Blo 287828 289255 := bstep (se 1 (by rfl) ⟨216941, by rfl⟩ : syracuseStep 289255 = 433883) B433883
theorem B289435 : Blo 287828 289435 := bstep (se 1 (by rfl) ⟨217076, by rfl⟩ : syracuseStep 289435 = 434153) B434153
theorem B649889 : Blo 287828 649889 := bstep (se 2 (by rfl) ⟨243708, by rfl⟩ : syracuseStep 649889 = 487417) B487417
theorem B3697487 : Blo 287828 3697487 := bstep (se 1 (by rfl) ⟨2773115, by rfl⟩ : syracuseStep 3697487 = 5546231) B5546231
theorem B650249 : Blo 287828 650249 := bstep (se 2 (by rfl) ⟨243843, by rfl⟩ : syracuseStep 650249 = 487687) B487687
theorem B289903 : Blo 287828 289903 := bstep (se 1 (by rfl) ⟨217427, by rfl⟩ : syracuseStep 289903 = 434855) B434855
theorem B289983 : Blo 287828 289983 := bstep (se 1 (by rfl) ⟨217487, by rfl⟩ : syracuseStep 289983 = 434975) B434975
theorem B650447 : Blo 287828 650447 := bstep (se 1 (by rfl) ⟨487835, by rfl⟩ : syracuseStep 650447 = 975671) B975671
theorem B289999 : Blo 287828 289999 := bstep (se 1 (by rfl) ⟨217499, by rfl⟩ : syracuseStep 289999 = 434999) B434999
theorem B1469663 : Blo 287828 1469663 := bstep (se 1 (by rfl) ⟨1102247, by rfl⟩ : syracuseStep 1469663 = 2204495) B2204495
theorem B11234609 : Blo 287828 11234609 := bstep (se 2 (by rfl) ⟨4212978, by rfl⟩ : syracuseStep 11234609 = 8425957) B8425957
theorem B290119 : Blo 287828 290119 := bstep (se 1 (by rfl) ⟨217589, by rfl⟩ : syracuseStep 290119 = 435179) B435179
theorem B1797569 : Blo 287828 1797569 := bstep (se 2 (by rfl) ⟨674088, by rfl⟩ : syracuseStep 1797569 = 1348177) B1348177
theorem B618367 : Blo 287828 618367 := bstep (se 1 (by rfl) ⟨463775, by rfl⟩ : syracuseStep 618367 = 927551) B927551
theorem B1241021 : Blo 287828 1241021 := bstep (se 3 (by rfl) ⟨232691, by rfl⟩ : syracuseStep 1241021 = 465383) B465383
theorem B651239 : Blo 287828 651239 := bstep (se 1 (by rfl) ⟨488429, by rfl⟩ : syracuseStep 651239 = 976859) B976859
theorem B290847 : Blo 287828 290847 := bstep (se 1 (by rfl) ⟨218135, by rfl⟩ : syracuseStep 290847 = 436271) B436271
theorem B651419 : Blo 287828 651419 := bstep (se 1 (by rfl) ⟨488564, by rfl⟩ : syracuseStep 651419 = 977129) B977129
theorem B291023 : Blo 287828 291023 := bstep (se 1 (by rfl) ⟨218267, by rfl⟩ : syracuseStep 291023 = 436535) B436535
theorem B291143 : Blo 287828 291143 := bstep (se 1 (by rfl) ⟨218357, by rfl⟩ : syracuseStep 291143 = 436715) B436715
theorem B651599 : Blo 287828 651599 := bstep (se 1 (by rfl) ⟨488699, by rfl⟩ : syracuseStep 651599 = 977399) B977399
theorem B651617 : Blo 287828 651617 := bstep (se 2 (by rfl) ⟨244356, by rfl⟩ : syracuseStep 651617 = 488713) B488713
theorem B651689 : Blo 287828 651689 := bstep (se 2 (by rfl) ⟨244383, by rfl⟩ : syracuseStep 651689 = 488767) B488767
theorem B651707 : Blo 287828 651707 := bstep (se 1 (by rfl) ⟨488780, by rfl⟩ : syracuseStep 651707 = 977561) B977561
theorem B18641441 : Blo 287828 18641441 := bstep (se 2 (by rfl) ⟨6990540, by rfl⟩ : syracuseStep 18641441 = 13981081) B13981081
theorem B651995 : Blo 287828 651995 := bstep (se 1 (by rfl) ⟨488996, by rfl⟩ : syracuseStep 651995 = 977993) B977993
theorem B291611 : Blo 287828 291611 := bstep (se 1 (by rfl) ⟨218708, by rfl⟩ : syracuseStep 291611 = 437417) B437417
theorem B434664305 : Blo 287828 434664305 := bstep (se 2 (by rfl) ⟨162999114, by rfl⟩ : syracuseStep 434664305 = 325998229) B325998229
theorem B4977611 : Blo 287828 4977611 := bstep (se 1 (by rfl) ⟨3733208, by rfl⟩ : syracuseStep 4977611 = 7466417) B7466417
theorem B979937 : Blo 287828 979937 := bstep (se 2 (by rfl) ⟨367476, by rfl⟩ : syracuseStep 979937 = 734953) B734953
theorem B652265 : Blo 287828 652265 := bstep (se 2 (by rfl) ⟨244599, by rfl⟩ : syracuseStep 652265 = 489199) B489199
theorem B652967 : Blo 287828 652967 := bstep (se 1 (by rfl) ⟨489725, by rfl⟩ : syracuseStep 652967 = 979451) B979451
theorem B653147 : Blo 287828 653147 := bstep (se 1 (by rfl) ⟨489860, by rfl⟩ : syracuseStep 653147 = 979721) B979721
theorem B1603997 : Blo 287828 1603997 := bstep (se 3 (by rfl) ⟨300749, by rfl⟩ : syracuseStep 1603997 = 601499) B601499
theorem B1866503 : Blo 287828 1866503 := bstep (se 1 (by rfl) ⟨1399877, by rfl⟩ : syracuseStep 1866503 = 2799755) B2799755
theorem B326623 : Blo 287828 326623 := bstep (se 1 (by rfl) ⟨244967, by rfl⟩ : syracuseStep 326623 = 489935) B489935
theorem B982043 : Blo 287828 982043 := bstep (se 1 (by rfl) ⟨736532, by rfl⟩ : syracuseStep 982043 = 1473065) B1473065
theorem B982259 : Blo 287828 982259 := bstep (se 1 (by rfl) ⟨736694, by rfl⟩ : syracuseStep 982259 = 1473389) B1473389
theorem B490907 : Blo 287828 490907 := bstep (se 1 (by rfl) ⟨368180, by rfl⟩ : syracuseStep 490907 = 736361) B736361
theorem B327487 : Blo 287828 327487 := bstep (se 1 (by rfl) ⟨245615, by rfl⟩ : syracuseStep 327487 = 491231) B491231
theorem B622399 : Blo 287828 622399 := bstep (se 1 (by rfl) ⟨466799, by rfl⟩ : syracuseStep 622399 = 933599) B933599
theorem B786287 : Blo 287828 786287 := bstep (se 1 (by rfl) ⟨589715, by rfl⟩ : syracuseStep 786287 = 1179431) B1179431
theorem B622561 : Blo 287828 622561 := bstep (se 2 (by rfl) ⟨233460, by rfl⟩ : syracuseStep 622561 = 466921) B466921
theorem B655559 : Blo 287828 655559 := bstep (se 1 (by rfl) ⟨491669, by rfl⟩ : syracuseStep 655559 = 983339) B983339
theorem B1999187 : Blo 287828 1999187 := bstep (se 1 (by rfl) ⟨1499390, by rfl⟩ : syracuseStep 1999187 = 2998781) B2998781
theorem B1868143 : Blo 287828 1868143 := bstep (se 1 (by rfl) ⟨1401107, by rfl⟩ : syracuseStep 1868143 = 2802215) B2802215
theorem B492007 : Blo 287828 492007 := bstep (se 1 (by rfl) ⟨369005, by rfl⟩ : syracuseStep 492007 = 738011) B738011
theorem B983609 : Blo 287828 983609 := bstep (se 2 (by rfl) ⟨368853, by rfl⟩ : syracuseStep 983609 = 737707) B737707
theorem B983771 : Blo 287828 983771 := bstep (se 1 (by rfl) ⟨737828, by rfl⟩ : syracuseStep 983771 = 1475657) B1475657
theorem B1049735 : Blo 287828 1049735 := bstep (se 1 (by rfl) ⟨787301, by rfl⟩ : syracuseStep 1049735 = 1574603) B1574603
theorem B656567 : Blo 287828 656567 := bstep (se 1 (by rfl) ⟨492425, by rfl⟩ : syracuseStep 656567 = 984851) B984851
theorem B525575 : Blo 287828 525575 := bstep (se 1 (by rfl) ⟨394181, by rfl⟩ : syracuseStep 525575 = 788363) B788363
theorem B821117 : Blo 287828 821117 := bstep (se 3 (by rfl) ⟨153959, by rfl⟩ : syracuseStep 821117 = 307919) B307919
theorem B2197691 : Blo 287828 2197691 := bstep (se 1 (by rfl) ⟨1648268, by rfl⟩ : syracuseStep 2197691 = 3296537) B3296537
theorem B756127 : Blo 287828 756127 := bstep (se 1 (by rfl) ⟨567095, by rfl⟩ : syracuseStep 756127 = 1134191) B1134191
theorem B1674361 : Blo 287828 1674361 := bstep (se 2 (by rfl) ⟨627885, by rfl⟩ : syracuseStep 1674361 = 1255771) B1255771
theorem B822791 : Blo 287828 822791 := bstep (se 1 (by rfl) ⟨617093, by rfl⟩ : syracuseStep 822791 = 1234187) B1234187
theorem B3804833 : Blo 287828 3804833 := bstep (se 2 (by rfl) ⟨1426812, by rfl⟩ : syracuseStep 3804833 = 2853625) B2853625
theorem B823031 : Blo 287828 823031 := bstep (se 1 (by rfl) ⟨617273, by rfl⟩ : syracuseStep 823031 = 1234547) B1234547
theorem B364591 : Blo 287828 364591 := bstep (se 1 (by rfl) ⟨273443, by rfl⟩ : syracuseStep 364591 = 546887) B546887
theorem B6295643 : Blo 287828 6295643 := bstep (se 1 (by rfl) ⟨4721732, by rfl⟩ : syracuseStep 6295643 = 9443465) B9443465
theorem B33952541 : Blo 287828 33952541 := bstep (se 3 (by rfl) ⟨6366101, by rfl⟩ : syracuseStep 33952541 = 12732203) B12732203
theorem B824489 : Blo 287828 824489 := bstep (se 2 (by rfl) ⟨309183, by rfl⟩ : syracuseStep 824489 = 618367) B618367
theorem B923359 : Blo 287828 923359 := bstep (se 1 (by rfl) ⟨692519, by rfl⟩ : syracuseStep 923359 = 1385039) B1385039
theorem B431855 : Blo 287828 431855 := bstep (se 1 (by rfl) ⟨323891, by rfl⟩ : syracuseStep 431855 = 647783) B647783
theorem B531263 : Blo 287828 531263 := bstep (se 1 (by rfl) ⟨398447, by rfl⟩ : syracuseStep 531263 = 796895) B796895
theorem B433259 : Blo 287828 433259 := bstep (se 1 (by rfl) ⟨324944, by rfl⟩ : syracuseStep 433259 = 649889) B649889
theorem B2464991 : Blo 287828 2464991 := bstep (se 1 (by rfl) ⟨1848743, by rfl⟩ : syracuseStep 2464991 = 3697487) B3697487
theorem B433499 : Blo 287828 433499 := bstep (se 1 (by rfl) ⟨325124, by rfl⟩ : syracuseStep 433499 = 650249) B650249
theorem B433631 : Blo 287828 433631 := bstep (se 1 (by rfl) ⟨325223, by rfl⟩ : syracuseStep 433631 = 650447) B650447
theorem B827347 : Blo 287828 827347 := bstep (se 1 (by rfl) ⟨620510, by rfl⟩ : syracuseStep 827347 = 1241021) B1241021
theorem B434159 : Blo 287828 434159 := bstep (se 1 (by rfl) ⟨325619, by rfl⟩ : syracuseStep 434159 = 651239) B651239
theorem B2924552213 : Blo 287828 2924552213 := bstep (se 6 (by rfl) ⟨68544192, by rfl⟩ : syracuseStep 2924552213 = 137088385) B137088385
theorem B434279 : Blo 287828 434279 := bstep (se 1 (by rfl) ⟨325709, by rfl⟩ : syracuseStep 434279 = 651419) B651419
theorem B3154049 : Blo 287828 3154049 := bstep (se 2 (by rfl) ⟨1182768, by rfl⟩ : syracuseStep 3154049 = 2365537) B2365537
theorem B467113 : Blo 287828 467113 := bstep (se 2 (by rfl) ⟨175167, by rfl⟩ : syracuseStep 467113 = 350335) B350335
theorem B729263 : Blo 287828 729263 := bstep (se 1 (by rfl) ⟨546947, by rfl⟩ : syracuseStep 729263 = 1093895) B1093895
theorem B434399 : Blo 287828 434399 := bstep (se 1 (by rfl) ⟨325799, by rfl⟩ : syracuseStep 434399 = 651599) B651599
theorem B434411 : Blo 287828 434411 := bstep (se 1 (by rfl) ⟨325808, by rfl⟩ : syracuseStep 434411 = 651617) B651617
theorem B434459 : Blo 287828 434459 := bstep (se 1 (by rfl) ⟨325844, by rfl⟩ : syracuseStep 434459 = 651689) B651689
theorem B434471 : Blo 287828 434471 := bstep (se 1 (by rfl) ⟨325853, by rfl⟩ : syracuseStep 434471 = 651707) B651707
theorem B12427627 : Blo 287828 12427627 := bstep (se 1 (by rfl) ⟨9320720, by rfl⟩ : syracuseStep 12427627 = 18641441) B18641441
theorem B434663 : Blo 287828 434663 := bstep (se 1 (by rfl) ⟨325997, by rfl⟩ : syracuseStep 434663 = 651995) B651995
theorem B289776203 : Blo 287828 289776203 := bstep (se 1 (by rfl) ⟨217332152, by rfl⟩ : syracuseStep 289776203 = 434664305) B434664305
theorem B3318407 : Blo 287828 3318407 := bstep (se 1 (by rfl) ⟨2488805, by rfl⟩ : syracuseStep 3318407 = 4977611) B4977611
theorem B434843 : Blo 287828 434843 := bstep (se 1 (by rfl) ⟨326132, by rfl⟩ : syracuseStep 434843 = 652265) B652265
theorem B435311 : Blo 287828 435311 := bstep (se 1 (by rfl) ⟨326483, by rfl⟩ : syracuseStep 435311 = 652967) B652967
theorem B4400335 : Blo 287828 4400335 := bstep (se 1 (by rfl) ⟨3300251, by rfl⟩ : syracuseStep 4400335 = 6600503) B6600503
theorem B435431 : Blo 287828 435431 := bstep (se 1 (by rfl) ⟨326573, by rfl⟩ : syracuseStep 435431 = 653147) B653147
theorem B435497 : Blo 287828 435497 := bstep (se 2 (by rfl) ⟨163311, by rfl⟩ : syracuseStep 435497 = 326623) B326623
theorem B1189703 : Blo 287828 1189703 := bstep (se 1 (by rfl) ⟨892277, by rfl⟩ : syracuseStep 1189703 = 1784555) B1784555
theorem B436649 : Blo 287828 436649 := bstep (se 2 (by rfl) ⟨163743, by rfl⟩ : syracuseStep 436649 = 327487) B327487
theorem B829865 : Blo 287828 829865 := bstep (se 2 (by rfl) ⟨311199, by rfl⟩ : syracuseStep 829865 = 622399) B622399
theorem B830081 : Blo 287828 830081 := bstep (se 2 (by rfl) ⟨311280, by rfl⟩ : syracuseStep 830081 = 622561) B622561
theorem B437183 : Blo 287828 437183 := bstep (se 1 (by rfl) ⟨327887, by rfl⟩ : syracuseStep 437183 = 655775) B655775
theorem B4074515 : Blo 287828 4074515 := bstep (se 1 (by rfl) ⟨3055886, by rfl⟩ : syracuseStep 4074515 = 6111773) B6111773
theorem B3059279 : Blo 287828 3059279 := bstep (se 1 (by rfl) ⟨2294459, by rfl⟩ : syracuseStep 3059279 = 4588919) B4588919
theorem B1388153 : Blo 287828 1388153 := bstep (se 2 (by rfl) ⟨520557, by rfl⟩ : syracuseStep 1388153 = 1041115) B1041115
theorem B4730687 : Blo 287828 4730687 := bstep (se 1 (by rfl) ⟨3548015, by rfl⟩ : syracuseStep 4730687 = 7096031) B7096031
theorem B1093607 : Blo 287828 1093607 := bstep (se 1 (by rfl) ⟨820205, by rfl⟩ : syracuseStep 1093607 = 1640411) B1640411
theorem B931355 : Blo 287828 931355 := bstep (se 1 (by rfl) ⟨698516, by rfl⟩ : syracuseStep 931355 = 1397033) B1397033
theorem B5289761 : Blo 287828 5289761 := bstep (se 2 (by rfl) ⟨1983660, by rfl⟩ : syracuseStep 5289761 = 3967321) B3967321
theorem B1324907 : Blo 287828 1324907 := bstep (se 1 (by rfl) ⟨993680, by rfl⟩ : syracuseStep 1324907 = 1987361) B1987361
theorem B931817 : Blo 287828 931817 := bstep (se 2 (by rfl) ⟨349431, by rfl⟩ : syracuseStep 931817 = 698863) B698863
theorem B1095869 : Blo 287828 1095869 := bstep (se 3 (by rfl) ⟨205475, by rfl⟩ : syracuseStep 1095869 = 410951) B410951
theorem B735439 : Blo 287828 735439 := bstep (se 1 (by rfl) ⟨551579, by rfl⟩ : syracuseStep 735439 = 1103159) B1103159
theorem B349223669 : Blo 287828 349223669 := bstep (se 5 (by rfl) ⟨16369859, by rfl⟩ : syracuseStep 349223669 = 32739719) B32739719
theorem B736411 : Blo 287828 736411 := bstep (se 1 (by rfl) ⟨552308, by rfl⟩ : syracuseStep 736411 = 1104617) B1104617
theorem B933227 : Blo 287828 933227 := bstep (se 1 (by rfl) ⟨699920, by rfl⟩ : syracuseStep 933227 = 1399841) B1399841
theorem B1850795 : Blo 287828 1850795 := bstep (se 1 (by rfl) ⟨1388096, by rfl⟩ : syracuseStep 1850795 = 2776193) B2776193
theorem B736735 : Blo 287828 736735 := bstep (se 1 (by rfl) ⟨552551, by rfl⟩ : syracuseStep 736735 = 1105103) B1105103
theorem B1097327 : Blo 287828 1097327 := bstep (se 1 (by rfl) ⟨822995, by rfl⟩ : syracuseStep 1097327 = 1645991) B1645991
theorem B311131 : Blo 287828 311131 := bstep (se 1 (by rfl) ⟨233348, by rfl⟩ : syracuseStep 311131 = 466697) B466697
theorem B4964489 : Blo 287828 4964489 := bstep (se 2 (by rfl) ⟨1861683, by rfl⟩ : syracuseStep 4964489 = 3723367) B3723367
theorem B1654991 : Blo 287828 1654991 := bstep (se 1 (by rfl) ⟨1241243, by rfl⟩ : syracuseStep 1654991 = 2482487) B2482487
theorem B704767 : Blo 287828 704767 := bstep (se 1 (by rfl) ⟨528575, by rfl⟩ : syracuseStep 704767 = 1057151) B1057151
theorem B1099241 : Blo 287828 1099241 := bstep (se 2 (by rfl) ⟨412215, by rfl⟩ : syracuseStep 1099241 = 824431) B824431
theorem B1328719 : Blo 287828 1328719 := bstep (se 1 (by rfl) ⟨996539, by rfl⟩ : syracuseStep 1328719 = 1993079) B1993079
theorem B1099439 : Blo 287828 1099439 := bstep (se 1 (by rfl) ⟨824579, by rfl⟩ : syracuseStep 1099439 = 1649159) B1649159
theorem B7489739 : Blo 287828 7489739 := bstep (se 1 (by rfl) ⟨5617304, by rfl⟩ : syracuseStep 7489739 = 11234609) B11234609
theorem B1198379 : Blo 287828 1198379 := bstep (se 1 (by rfl) ⟨898784, by rfl⟩ : syracuseStep 1198379 = 1797569) B1797569
theorem B2345435 : Blo 287828 2345435 := bstep (se 1 (by rfl) ⟨1759076, by rfl⟩ : syracuseStep 2345435 = 3518153) B3518153
theorem B3131905 : Blo 287828 3131905 := bstep (se 2 (by rfl) ⟨1174464, by rfl⟩ : syracuseStep 3131905 = 2348929) B2348929
theorem B1329817 : Blo 287828 1329817 := bstep (se 2 (by rfl) ⟨498681, by rfl⟩ : syracuseStep 1329817 = 997363) B997363
theorem B1100911 : Blo 287828 1100911 := bstep (se 1 (by rfl) ⟨825683, by rfl⟩ : syracuseStep 1100911 = 1651367) B1651367
theorem B1232171 : Blo 287828 1232171 := bstep (se 1 (by rfl) ⟨924128, by rfl⟩ : syracuseStep 1232171 = 1848257) B1848257
theorem B1069331 : Blo 287828 1069331 := bstep (se 1 (by rfl) ⟨801998, by rfl⟩ : syracuseStep 1069331 = 1603997) B1603997
theorem B1167979 : Blo 287828 1167979 := bstep (se 1 (by rfl) ⟨875984, by rfl⟩ : syracuseStep 1167979 = 1751969) B1751969
theorem B1102673 : Blo 287828 1102673 := bstep (se 2 (by rfl) ⟨413502, by rfl⟩ : syracuseStep 1102673 = 827005) B827005
theorem B971945 : Blo 287828 971945 := bstep (se 2 (by rfl) ⟨364479, by rfl⟩ : syracuseStep 971945 = 728959) B728959
theorem B1660297 : Blo 287828 1660297 := bstep (se 2 (by rfl) ⟨622611, by rfl⟩ : syracuseStep 1660297 = 1245223) B1245223
theorem B2413999 : Blo 287828 2413999 := bstep (se 1 (by rfl) ⟨1810499, by rfl⟩ : syracuseStep 2413999 = 3620999) B3620999
theorem B1169405 : Blo 287828 1169405 := bstep (se 3 (by rfl) ⟨219263, by rfl⟩ : syracuseStep 1169405 = 438527) B438527
theorem B1267849 : Blo 287828 1267849 := bstep (se 2 (by rfl) ⟨475443, by rfl⟩ : syracuseStep 1267849 = 950887) B950887
theorem B5003963 : Blo 287828 5003963 := bstep (se 1 (by rfl) ⟨3752972, by rfl⟩ : syracuseStep 5003963 = 7505945) B7505945
theorem B974159 : Blo 287828 974159 := bstep (se 1 (by rfl) ⟨730619, by rfl⟩ : syracuseStep 974159 = 1461239) B1461239
theorem B2186999 : Blo 287828 2186999 := bstep (se 1 (by rfl) ⟨1640249, by rfl⟩ : syracuseStep 2186999 = 3280499) B3280499
theorem B145219483 : Blo 287828 145219483 := bstep (se 1 (by rfl) ⟨108914612, by rfl⟩ : syracuseStep 145219483 = 217829225) B217829225
theorem B974807 : Blo 287828 974807 := bstep (se 1 (by rfl) ⟨731105, by rfl⟩ : syracuseStep 974807 = 1462211) B1462211
theorem B1171871 : Blo 287828 1171871 := bstep (se 1 (by rfl) ⟨878903, by rfl⟩ : syracuseStep 1171871 = 1757807) B1757807
theorem B647711 : Blo 287828 647711 := bstep (se 1 (by rfl) ⟨485783, by rfl⟩ : syracuseStep 647711 = 971567) B971567
theorem B1106729 : Blo 287828 1106729 := bstep (se 2 (by rfl) ⟨415023, by rfl⟩ : syracuseStep 1106729 = 830047) B830047
theorem B615367 : Blo 287828 615367 := bstep (se 1 (by rfl) ⟨461525, by rfl⟩ : syracuseStep 615367 = 923051) B923051
theorem B287995 : Blo 287828 287995 := bstep (se 1 (by rfl) ⟨215996, by rfl⟩ : syracuseStep 287995 = 431993) B431993
theorem B976211 : Blo 287828 976211 := bstep (se 1 (by rfl) ⟨732158, by rfl⟩ : syracuseStep 976211 = 1464317) B1464317
theorem B288159 : Blo 287828 288159 := bstep (se 1 (by rfl) ⟨216119, by rfl⟩ : syracuseStep 288159 = 432239) B432239
theorem B615863 : Blo 287828 615863 := bstep (se 1 (by rfl) ⟨461897, by rfl⟩ : syracuseStep 615863 = 923795) B923795
theorem B288207 : Blo 287828 288207 := bstep (se 1 (by rfl) ⟨216155, by rfl⟩ : syracuseStep 288207 = 432311) B432311
theorem B13985329 : Blo 287828 13985329 := bstep (se 2 (by rfl) ⟨5244498, by rfl⟩ : syracuseStep 13985329 = 10488997) B10488997
theorem B288487 : Blo 287828 288487 := bstep (se 1 (by rfl) ⟨216365, by rfl⟩ : syracuseStep 288487 = 432731) B432731
theorem B288495 : Blo 287828 288495 := bstep (se 1 (by rfl) ⟨216371, by rfl⟩ : syracuseStep 288495 = 432743) B432743
theorem B288511 : Blo 287828 288511 := bstep (se 1 (by rfl) ⟨216383, by rfl⟩ : syracuseStep 288511 = 432767) B432767
theorem B12511007 : Blo 287828 12511007 := bstep (se 1 (by rfl) ⟨9383255, by rfl⟩ : syracuseStep 12511007 = 18766511) B18766511
theorem B976697 : Blo 287828 976697 := bstep (se 2 (by rfl) ⟨366261, by rfl⟩ : syracuseStep 976697 = 732523) B732523
theorem B288583 : Blo 287828 288583 := bstep (se 1 (by rfl) ⟨216437, by rfl⟩ : syracuseStep 288583 = 432875) B432875
theorem B288603 : Blo 287828 288603 := bstep (se 1 (by rfl) ⟨216452, by rfl⟩ : syracuseStep 288603 = 432905) B432905
theorem B1238921 : Blo 287828 1238921 := bstep (se 2 (by rfl) ⟨464595, by rfl⟩ : syracuseStep 1238921 = 929191) B929191
theorem B288763 : Blo 287828 288763 := bstep (se 1 (by rfl) ⟨216572, by rfl⟩ : syracuseStep 288763 = 433145) B433145
theorem B977183 : Blo 287828 977183 := bstep (se 1 (by rfl) ⟨732887, by rfl⟩ : syracuseStep 977183 = 1465775) B1465775
theorem B289183 : Blo 287828 289183 := bstep (se 1 (by rfl) ⟨216887, by rfl⟩ : syracuseStep 289183 = 433775) B433775
theorem B485831 : Blo 287828 485831 := bstep (se 1 (by rfl) ⟨364373, by rfl⟩ : syracuseStep 485831 = 728747) B728747
theorem B289263 : Blo 287828 289263 := bstep (se 1 (by rfl) ⟨216947, by rfl⟩ : syracuseStep 289263 = 433895) B433895
theorem B551519 : Blo 287828 551519 := bstep (se 1 (by rfl) ⟨413639, by rfl⟩ : syracuseStep 551519 = 827279) B827279
theorem B584347 : Blo 287828 584347 := bstep (se 1 (by rfl) ⟨438260, by rfl⟩ : syracuseStep 584347 = 876521) B876521
theorem B289447 : Blo 287828 289447 := bstep (se 1 (by rfl) ⟨217085, by rfl⟩ : syracuseStep 289447 = 434171) B434171
theorem B289487 : Blo 287828 289487 := bstep (se 1 (by rfl) ⟨217115, by rfl⟩ : syracuseStep 289487 = 434231) B434231
theorem B289567 : Blo 287828 289567 := bstep (se 1 (by rfl) ⟨217175, by rfl⟩ : syracuseStep 289567 = 434351) B434351
theorem B289703 : Blo 287828 289703 := bstep (se 1 (by rfl) ⟨217277, by rfl⟩ : syracuseStep 289703 = 434555) B434555
theorem B289819 : Blo 287828 289819 := bstep (se 1 (by rfl) ⟨217364, by rfl⟩ : syracuseStep 289819 = 434729) B434729
theorem B289883 : Blo 287828 289883 := bstep (se 1 (by rfl) ⟨217412, by rfl⟩ : syracuseStep 289883 = 434825) B434825
theorem B290023 : Blo 287828 290023 := bstep (se 1 (by rfl) ⟨217517, by rfl⟩ : syracuseStep 290023 = 435035) B435035
theorem B978155 : Blo 287828 978155 := bstep (se 1 (by rfl) ⟨733616, by rfl⟩ : syracuseStep 978155 = 1467233) B1467233
theorem B290047 : Blo 287828 290047 := bstep (se 1 (by rfl) ⟨217535, by rfl⟩ : syracuseStep 290047 = 435071) B435071
theorem B290095 : Blo 287828 290095 := bstep (se 1 (by rfl) ⟨217571, by rfl⟩ : syracuseStep 290095 = 435143) B435143
theorem B290239 : Blo 287828 290239 := bstep (se 1 (by rfl) ⟨217679, by rfl⟩ : syracuseStep 290239 = 435359) B435359
theorem B650735 : Blo 287828 650735 := bstep (se 1 (by rfl) ⟨488051, by rfl⟩ : syracuseStep 650735 = 976103) B976103
theorem B290335 : Blo 287828 290335 := bstep (se 1 (by rfl) ⟨217751, by rfl⟩ : syracuseStep 290335 = 435503) B435503
theorem B290463 : Blo 287828 290463 := bstep (se 1 (by rfl) ⟨217847, by rfl⟩ : syracuseStep 290463 = 435695) B435695
theorem B290471 : Blo 287828 290471 := bstep (se 1 (by rfl) ⟨217853, by rfl⟩ : syracuseStep 290471 = 435707) B435707
theorem B290495 : Blo 287828 290495 := bstep (se 1 (by rfl) ⟨217871, by rfl⟩ : syracuseStep 290495 = 435743) B435743
theorem B290591 : Blo 287828 290591 := bstep (se 1 (by rfl) ⟨217943, by rfl⟩ : syracuseStep 290591 = 435887) B435887
theorem B290651 : Blo 287828 290651 := bstep (se 1 (by rfl) ⟨217988, by rfl⟩ : syracuseStep 290651 = 435977) B435977
theorem B290671 : Blo 287828 290671 := bstep (se 1 (by rfl) ⟨218003, by rfl⟩ : syracuseStep 290671 = 436007) B436007
theorem B4157419 : Blo 287828 4157419 := bstep (se 1 (by rfl) ⟨3118064, by rfl⟩ : syracuseStep 4157419 = 6236129) B6236129
theorem B291071 : Blo 287828 291071 := bstep (se 1 (by rfl) ⟨218303, by rfl⟩ : syracuseStep 291071 = 436607) B436607
theorem B291231 : Blo 287828 291231 := bstep (se 1 (by rfl) ⟨218423, by rfl⟩ : syracuseStep 291231 = 436847) B436847
theorem B487849 : Blo 287828 487849 := bstep (se 2 (by rfl) ⟨182943, by rfl⟩ : syracuseStep 487849 = 365887) B365887
theorem B291375 : Blo 287828 291375 := bstep (se 1 (by rfl) ⟨218531, by rfl⟩ : syracuseStep 291375 = 437063) B437063
theorem B487991 : Blo 287828 487991 := bstep (se 1 (by rfl) ⟨365993, by rfl⟩ : syracuseStep 487991 = 731987) B731987
theorem B979613 : Blo 287828 979613 := bstep (se 3 (by rfl) ⟨183677, by rfl⟩ : syracuseStep 979613 = 367355) B367355
theorem B979775 : Blo 287828 979775 := bstep (se 1 (by rfl) ⟨734831, by rfl⟩ : syracuseStep 979775 = 1469663) B1469663
theorem B291775 : Blo 287828 291775 := bstep (se 1 (by rfl) ⟨218831, by rfl⟩ : syracuseStep 291775 = 437663) B437663
theorem B882103 : Blo 287828 882103 := bstep (se 1 (by rfl) ⟨661577, by rfl⟩ : syracuseStep 882103 = 1323155) B1323155
theorem B489287 : Blo 287828 489287 := bstep (se 1 (by rfl) ⟨366965, by rfl⟩ : syracuseStep 489287 = 733931) B733931
theorem B489307 : Blo 287828 489307 := bstep (se 1 (by rfl) ⟨366980, by rfl⟩ : syracuseStep 489307 = 733961) B733961
theorem B653291 : Blo 287828 653291 := bstep (se 1 (by rfl) ⟨489968, by rfl⟩ : syracuseStep 653291 = 979937) B979937
theorem B10516463 : Blo 287828 10516463 := bstep (se 1 (by rfl) ⟨7887347, by rfl⟩ : syracuseStep 10516463 = 15774695) B15774695
theorem B2193803 : Blo 287828 2193803 := bstep (se 1 (by rfl) ⟨1645352, by rfl⟩ : syracuseStep 2193803 = 3290705) B3290705
theorem B1473227 : Blo 287828 1473227 := bstep (se 1 (by rfl) ⟨1104920, by rfl⟩ : syracuseStep 1473227 = 2209841) B2209841
theorem B1244335 : Blo 287828 1244335 := bstep (se 1 (by rfl) ⟨933251, by rfl⟩ : syracuseStep 1244335 = 1866503) B1866503
theorem B654695 : Blo 287828 654695 := bstep (se 1 (by rfl) ⟨491021, by rfl⟩ : syracuseStep 654695 = 982043) B982043
theorem B654839 : Blo 287828 654839 := bstep (se 1 (by rfl) ⟨491129, by rfl⟩ : syracuseStep 654839 = 982259) B982259
theorem B982529 : Blo 287828 982529 := bstep (se 2 (by rfl) ⟨368448, by rfl⟩ : syracuseStep 982529 = 736897) B736897
theorem B491035 : Blo 287828 491035 := bstep (se 1 (by rfl) ⟨368276, by rfl⟩ : syracuseStep 491035 = 736553) B736553
theorem B327271 : Blo 287828 327271 := bstep (se 1 (by rfl) ⟨245453, by rfl⟩ : syracuseStep 327271 = 490907) B490907
theorem B2096765 : Blo 287828 2096765 := bstep (se 3 (by rfl) ⟨393143, by rfl⟩ : syracuseStep 2096765 = 786287) B786287
theorem B3309659 : Blo 287828 3309659 := bstep (se 1 (by rfl) ⟨2482244, by rfl⟩ : syracuseStep 3309659 = 4964489) B4964489
theorem B622817 : Blo 287828 622817 := bstep (se 2 (by rfl) ⟨233556, by rfl⟩ : syracuseStep 622817 = 467113) B467113
theorem B655739 : Blo 287828 655739 := bstep (se 1 (by rfl) ⟨491804, by rfl⟩ : syracuseStep 655739 = 983609) B983609
theorem B655847 : Blo 287828 655847 := bstep (se 1 (by rfl) ⟨491885, by rfl⟩ : syracuseStep 655847 = 983771) B983771
theorem B2490857 : Blo 287828 2490857 := bstep (se 2 (by rfl) ⟨934071, by rfl⟩ : syracuseStep 2490857 = 1868143) B1868143
theorem B656009 : Blo 287828 656009 := bstep (se 2 (by rfl) ⟨246003, by rfl⟩ : syracuseStep 656009 = 492007) B492007
theorem B2851549 : Blo 287828 2851549 := bstep (se 3 (by rfl) ⟨534665, by rfl⟩ : syracuseStep 2851549 = 1069331) B1069331
theorem B5867113 : Blo 287828 5867113 := bstep (se 2 (by rfl) ⟨2200167, by rfl⟩ : syracuseStep 5867113 = 4400335) B4400335
theorem B18647105 : Blo 287828 18647105 := bstep (se 2 (by rfl) ⟨6992664, by rfl⟩ : syracuseStep 18647105 = 13985329) B13985329
theorem B90540109 : Blo 287828 90540109 := bstep (se 3 (by rfl) ⟨16976270, by rfl⟩ : syracuseStep 90540109 = 33952541) B33952541
theorem B1771625 : Blo 287828 1771625 := bstep (se 2 (by rfl) ⟨664359, by rfl⟩ : syracuseStep 1771625 = 1328719) B1328719
theorem B821447 : Blo 287828 821447 := bstep (se 1 (by rfl) ⟨616085, by rfl⟩ : syracuseStep 821447 = 1232171) B1232171
theorem B4197095 : Blo 287828 4197095 := bstep (se 1 (by rfl) ⟨3147821, by rfl⟩ : syracuseStep 4197095 = 6295643) B6295643
theorem B1773089 : Blo 287828 1773089 := bstep (se 2 (by rfl) ⟨664908, by rfl⟩ : syracuseStep 1773089 = 1329817) B1329817
theorem B1642301 : Blo 287828 1642301 := bstep (se 3 (by rfl) ⟨307931, by rfl⟩ : syracuseStep 1642301 = 615863) B615863
theorem B1643327 : Blo 287828 1643327 := bstep (se 1 (by rfl) ⟨1232495, by rfl⟩ : syracuseStep 1643327 = 2464991) B2464991
theorem B3281957 : Blo 287828 3281957 := bstep (se 4 (by rfl) ⟨307683, by rfl⟩ : syracuseStep 3281957 = 615367) B615367
theorem B5543225 : Blo 287828 5543225 := bstep (se 2 (by rfl) ⟨2078709, by rfl⟩ : syracuseStep 5543225 = 4157419) B4157419
theorem B1949701475 : Blo 287828 1949701475 := bstep (se 1 (by rfl) ⟨1462276106, by rfl⟩ : syracuseStep 1949701475 = 2924552213) B2924552213
theorem B2102699 : Blo 287828 2102699 := bstep (se 1 (by rfl) ⟨1577024, by rfl⟩ : syracuseStep 2102699 = 3154049) B3154049
theorem B431807 : Blo 287828 431807 := bstep (se 1 (by rfl) ⟨323855, by rfl⟩ : syracuseStep 431807 = 647711) B647711
theorem B793135 : Blo 287828 793135 := bstep (se 1 (by rfl) ⟨594851, by rfl⟩ : syracuseStep 793135 = 1189703) B1189703
theorem B825947 : Blo 287828 825947 := bstep (se 1 (by rfl) ⟨619460, by rfl⟩ : syracuseStep 825947 = 1238921) B1238921
theorem B367679 : Blo 287828 367679 := bstep (se 1 (by rfl) ⟨275759, by rfl⟩ : syracuseStep 367679 = 551519) B551519
theorem B3218665 : Blo 287828 3218665 := bstep (se 2 (by rfl) ⟨1206999, by rfl⟩ : syracuseStep 3218665 = 2413999) B2413999
theorem B1416701 : Blo 287828 1416701 := bstep (se 3 (by rfl) ⟨265631, by rfl⟩ : syracuseStep 1416701 = 531263) B531263
theorem B433823 : Blo 287828 433823 := bstep (se 1 (by rfl) ⟨325367, by rfl⟩ : syracuseStep 433823 = 650735) B650735
theorem B2039519 : Blo 287828 2039519 := bstep (se 1 (by rfl) ⟨1529639, by rfl⟩ : syracuseStep 2039519 = 3059279) B3059279
theorem B925435 : Blo 287828 925435 := bstep (se 1 (by rfl) ⟨694076, by rfl⟩ : syracuseStep 925435 = 1388153) B1388153
theorem B3153791 : Blo 287828 3153791 := bstep (se 1 (by rfl) ⟨2365343, by rfl⟩ : syracuseStep 3153791 = 4730687) B4730687
theorem B729071 : Blo 287828 729071 := bstep (se 1 (by rfl) ⟨546803, by rfl⟩ : syracuseStep 729071 = 1093607) B1093607
theorem B435527 : Blo 287828 435527 := bstep (se 1 (by rfl) ⟨326645, by rfl⟩ : syracuseStep 435527 = 653291) B653291
theorem B730579 : Blo 287828 730579 := bstep (se 1 (by rfl) ⟨547934, by rfl⟩ : syracuseStep 730579 = 1095869) B1095869
theorem B436361 : Blo 287828 436361 := bstep (se 2 (by rfl) ⟨163635, by rfl⟩ : syracuseStep 436361 = 327271) B327271
theorem B436463 : Blo 287828 436463 := bstep (se 1 (by rfl) ⟨327347, by rfl⟩ : syracuseStep 436463 = 654695) B654695
theorem B436559 : Blo 287828 436559 := bstep (se 1 (by rfl) ⟨327419, by rfl⟩ : syracuseStep 436559 = 654839) B654839
theorem B731551 : Blo 287828 731551 := bstep (se 1 (by rfl) ⟨548663, by rfl⟩ : syracuseStep 731551 = 1097327) B1097327
theorem B437039 : Blo 287828 437039 := bstep (se 1 (by rfl) ⟨327779, by rfl⟩ : syracuseStep 437039 = 655559) B655559
theorem B6761861 : Blo 287828 6761861 := bstep (se 4 (by rfl) ⟨633924, by rfl⟩ : syracuseStep 6761861 = 1267849) B1267849
theorem B699823 : Blo 287828 699823 := bstep (se 1 (by rfl) ⟨524867, by rfl⟩ : syracuseStep 699823 = 1049735) B1049735
theorem B437711 : Blo 287828 437711 := bstep (se 1 (by rfl) ⟨328283, by rfl⟩ : syracuseStep 437711 = 656567) B656567
theorem B732827 : Blo 287828 732827 := bstep (se 1 (by rfl) ⟨549620, by rfl⟩ : syracuseStep 732827 = 1099241) B1099241
theorem B732959 : Blo 287828 732959 := bstep (se 1 (by rfl) ⟨549719, by rfl⟩ : syracuseStep 732959 = 1099439) B1099439
theorem B4993159 : Blo 287828 4993159 := bstep (se 1 (by rfl) ⟨3744869, by rfl⟩ : syracuseStep 4993159 = 7489739) B7489739
theorem B2536555 : Blo 287828 2536555 := bstep (se 1 (by rfl) ⟨1902416, by rfl⟩ : syracuseStep 2536555 = 3804833) B3804833
theorem B735115 : Blo 287828 735115 := bstep (se 1 (by rfl) ⟨551336, by rfl⟩ : syracuseStep 735115 = 1102673) B1102673
theorem B4175873 : Blo 287828 4175873 := bstep (se 2 (by rfl) ⟨1565952, by rfl⟩ : syracuseStep 4175873 = 3131905) B3131905
theorem B1457999 : Blo 287828 1457999 := bstep (se 1 (by rfl) ⟨1093499, by rfl⟩ : syracuseStep 1457999 = 2186999) B2186999
theorem B193184135 : Blo 287828 193184135 := bstep (se 1 (by rfl) ⟨144888101, by rfl⟩ : syracuseStep 193184135 = 289776203) B289776203
theorem B2212271 : Blo 287828 2212271 := bstep (se 1 (by rfl) ⟨1659203, by rfl⟩ : syracuseStep 2212271 = 3318407) B3318407
theorem B737819 : Blo 287828 737819 := bstep (se 1 (by rfl) ⟨553364, by rfl⟩ : syracuseStep 737819 = 1106729) B1106729
theorem B8929925 : Blo 287828 8929925 := bstep (se 4 (by rfl) ⟨837180, by rfl⟩ : syracuseStep 8929925 = 1674361) B1674361
theorem B3195677 : Blo 287828 3195677 := bstep (se 3 (by rfl) ⟨599189, by rfl⟩ : syracuseStep 3195677 = 1198379) B1198379
theorem B1557305 : Blo 287828 1557305 := bstep (se 2 (by rfl) ⟨583989, by rfl⟩ : syracuseStep 1557305 = 1167979) B1167979
theorem B8340671 : Blo 287828 8340671 := bstep (se 1 (by rfl) ⟨6255503, by rfl⟩ : syracuseStep 8340671 = 12511007) B12511007
theorem B2213729 : Blo 287828 2213729 := bstep (se 2 (by rfl) ⟨830148, by rfl⟩ : syracuseStep 2213729 = 1660297) B1660297
theorem B1231145 : Blo 287828 1231145 := bstep (se 2 (by rfl) ⟨461679, by rfl⟩ : syracuseStep 1231145 = 923359) B923359
theorem B3526507 : Blo 287828 3526507 := bstep (se 1 (by rfl) ⟨2644880, by rfl⟩ : syracuseStep 3526507 = 5289761) B5289761
theorem B1659113 : Blo 287828 1659113 := bstep (se 2 (by rfl) ⟨622167, by rfl⟩ : syracuseStep 1659113 = 1244335) B1244335
theorem B1462535 : Blo 287828 1462535 := bstep (se 1 (by rfl) ⟨1096901, by rfl⟩ : syracuseStep 1462535 = 2193803) B2193803
theorem B1659365 : Blo 287828 1659365 := bstep (se 4 (by rfl) ⟨155565, by rfl⟩ : syracuseStep 1659365 = 311131) B311131
theorem B1233863 : Blo 287828 1233863 := bstep (se 1 (by rfl) ⟨925397, by rfl⟩ : syracuseStep 1233863 = 1850795) B1850795
theorem B1397843 : Blo 287828 1397843 := bstep (se 1 (by rfl) ⟨1048382, by rfl⟩ : syracuseStep 1397843 = 2096765) B2096765
theorem B1103129 : Blo 287828 1103129 := bstep (se 2 (by rfl) ⟨413673, by rfl⟩ : syracuseStep 1103129 = 827347) B827347
theorem B1103327 : Blo 287828 1103327 := bstep (se 1 (by rfl) ⟨827495, by rfl⟩ : syracuseStep 1103327 = 1654991) B1654991
theorem B1332791 : Blo 287828 1332791 := bstep (se 1 (by rfl) ⟨999593, by rfl⟩ : syracuseStep 1332791 = 1999187) B1999187
theorem B939689 : Blo 287828 939689 := bstep (se 2 (by rfl) ⟨352383, by rfl⟩ : syracuseStep 939689 = 704767) B704767
theorem B16570169 : Blo 287828 16570169 := bstep (se 2 (by rfl) ⟨6213813, by rfl⟩ : syracuseStep 16570169 = 12427627) B12427627
theorem B547411 : Blo 287828 547411 := bstep (se 1 (by rfl) ⟨410558, by rfl⟩ : syracuseStep 547411 = 821117) B821117
theorem B1465127 : Blo 287828 1465127 := bstep (se 1 (by rfl) ⟨1098845, by rfl⟩ : syracuseStep 1465127 = 2197691) B2197691
theorem B1563623 : Blo 287828 1563623 := bstep (se 1 (by rfl) ⟨1172717, by rfl⟩ : syracuseStep 1563623 = 2345435) B2345435
theorem B548527 : Blo 287828 548527 := bstep (se 1 (by rfl) ⟨411395, by rfl⟩ : syracuseStep 548527 = 822791) B822791
theorem B548687 : Blo 287828 548687 := bstep (se 1 (by rfl) ⟨411515, by rfl⟩ : syracuseStep 548687 = 823031) B823031
theorem B1008169 : Blo 287828 1008169 := bstep (se 2 (by rfl) ⟨378063, by rfl⟩ : syracuseStep 1008169 = 756127) B756127
theorem B1401533 : Blo 287828 1401533 := bstep (se 3 (by rfl) ⟨262787, by rfl⟩ : syracuseStep 1401533 = 525575) B525575
theorem B647963 : Blo 287828 647963 := bstep (se 1 (by rfl) ⟨485972, by rfl⟩ : syracuseStep 647963 = 971945) B971945
theorem B549659 : Blo 287828 549659 := bstep (se 1 (by rfl) ⟨412244, by rfl⟩ : syracuseStep 549659 = 824489) B824489
theorem B779129 : Blo 287828 779129 := bstep (se 2 (by rfl) ⟨292173, by rfl⟩ : syracuseStep 779129 = 584347) B584347
theorem B287903 : Blo 287828 287903 := bstep (se 1 (by rfl) ⟨215927, by rfl⟩ : syracuseStep 287903 = 431855) B431855
theorem B779603 : Blo 287828 779603 := bstep (se 1 (by rfl) ⟨584702, by rfl⟩ : syracuseStep 779603 = 1169405) B1169405
theorem B1467881 : Blo 287828 1467881 := bstep (se 2 (by rfl) ⟨550455, by rfl⟩ : syracuseStep 1467881 = 1100911) B1100911
theorem B3335975 : Blo 287828 3335975 := bstep (se 1 (by rfl) ⟨2501981, by rfl⟩ : syracuseStep 3335975 = 5003963) B5003963
theorem B288839 : Blo 287828 288839 := bstep (se 1 (by rfl) ⟨216629, by rfl⟩ : syracuseStep 288839 = 433259) B433259
theorem B649439 : Blo 287828 649439 := bstep (se 1 (by rfl) ⟨487079, by rfl⟩ : syracuseStep 649439 = 974159) B974159
theorem B288999 : Blo 287828 288999 := bstep (se 1 (by rfl) ⟨216749, by rfl⟩ : syracuseStep 288999 = 433499) B433499
theorem B289087 : Blo 287828 289087 := bstep (se 1 (by rfl) ⟨216815, by rfl⟩ : syracuseStep 289087 = 433631) B433631
theorem B649871 : Blo 287828 649871 := bstep (se 1 (by rfl) ⟨487403, by rfl⟩ : syracuseStep 649871 = 974807) B974807
theorem B289439 : Blo 287828 289439 := bstep (se 1 (by rfl) ⟨217079, by rfl⟩ : syracuseStep 289439 = 434159) B434159
theorem B486121 : Blo 287828 486121 := bstep (se 2 (by rfl) ⟨182295, by rfl⟩ : syracuseStep 486121 = 364591) B364591
theorem B289519 : Blo 287828 289519 := bstep (se 1 (by rfl) ⟨217139, by rfl⟩ : syracuseStep 289519 = 434279) B434279
theorem B486175 : Blo 287828 486175 := bstep (se 1 (by rfl) ⟨364631, by rfl⟩ : syracuseStep 486175 = 729263) B729263
theorem B289599 : Blo 287828 289599 := bstep (se 1 (by rfl) ⟨217199, by rfl⟩ : syracuseStep 289599 = 434399) B434399
theorem B289607 : Blo 287828 289607 := bstep (se 1 (by rfl) ⟨217205, by rfl⟩ : syracuseStep 289607 = 434411) B434411
theorem B289639 : Blo 287828 289639 := bstep (se 1 (by rfl) ⟨217229, by rfl⟩ : syracuseStep 289639 = 434459) B434459
theorem B289647 : Blo 287828 289647 := bstep (se 1 (by rfl) ⟨217235, by rfl⟩ : syracuseStep 289647 = 434471) B434471
theorem B781247 : Blo 287828 781247 := bstep (se 1 (by rfl) ⟨585935, by rfl⟩ : syracuseStep 781247 = 1171871) B1171871
theorem B289775 : Blo 287828 289775 := bstep (se 1 (by rfl) ⟨217331, by rfl⟩ : syracuseStep 289775 = 434663) B434663
theorem B289895 : Blo 287828 289895 := bstep (se 1 (by rfl) ⟨217421, by rfl⟩ : syracuseStep 289895 = 434843) B434843
theorem B650465 : Blo 287828 650465 := bstep (se 2 (by rfl) ⟨243924, by rfl⟩ : syracuseStep 650465 = 487849) B487849
theorem B290207 : Blo 287828 290207 := bstep (se 1 (by rfl) ⟨217655, by rfl⟩ : syracuseStep 290207 = 435311) B435311
theorem B290287 : Blo 287828 290287 := bstep (se 1 (by rfl) ⟨217715, by rfl⟩ : syracuseStep 290287 = 435431) B435431
theorem B290331 : Blo 287828 290331 := bstep (se 1 (by rfl) ⟨217748, by rfl⟩ : syracuseStep 290331 = 435497) B435497
theorem B650807 : Blo 287828 650807 := bstep (se 1 (by rfl) ⟨488105, by rfl⟩ : syracuseStep 650807 = 976211) B976211
theorem B651131 : Blo 287828 651131 := bstep (se 1 (by rfl) ⟨488348, by rfl⟩ : syracuseStep 651131 = 976697) B976697
theorem B651455 : Blo 287828 651455 := bstep (se 1 (by rfl) ⟨488591, by rfl⟩ : syracuseStep 651455 = 977183) B977183
theorem B291099 : Blo 287828 291099 := bstep (se 1 (by rfl) ⟨218324, by rfl⟩ : syracuseStep 291099 = 436649) B436649
theorem B553243 : Blo 287828 553243 := bstep (se 1 (by rfl) ⟨414932, by rfl⟩ : syracuseStep 553243 = 829865) B829865
theorem B323887 : Blo 287828 323887 := bstep (se 1 (by rfl) ⟨242915, by rfl⟩ : syracuseStep 323887 = 485831) B485831
theorem B553387 : Blo 287828 553387 := bstep (se 1 (by rfl) ⟨415040, by rfl⟩ : syracuseStep 553387 = 830081) B830081
theorem B1176137 : Blo 287828 1176137 := bstep (se 2 (by rfl) ⟨441051, by rfl⟩ : syracuseStep 1176137 = 882103) B882103
theorem B291455 : Blo 287828 291455 := bstep (se 1 (by rfl) ⟨218591, by rfl⟩ : syracuseStep 291455 = 437183) B437183
theorem B2716343 : Blo 287828 2716343 := bstep (se 1 (by rfl) ⟨2037257, by rfl⟩ : syracuseStep 2716343 = 4074515) B4074515
theorem B652103 : Blo 287828 652103 := bstep (se 1 (by rfl) ⟨489077, by rfl⟩ : syracuseStep 652103 = 978155) B978155
theorem B652409 : Blo 287828 652409 := bstep (se 2 (by rfl) ⟨244653, by rfl⟩ : syracuseStep 652409 = 489307) B489307
theorem B980585 : Blo 287828 980585 := bstep (se 2 (by rfl) ⟨367719, by rfl⟩ : syracuseStep 980585 = 735439) B735439
theorem B325327 : Blo 287828 325327 := bstep (se 1 (by rfl) ⟨243995, by rfl⟩ : syracuseStep 325327 = 487991) B487991
theorem B653075 : Blo 287828 653075 := bstep (se 1 (by rfl) ⟨489806, by rfl⟩ : syracuseStep 653075 = 979613) B979613
theorem B653183 : Blo 287828 653183 := bstep (se 1 (by rfl) ⟨489887, by rfl⟩ : syracuseStep 653183 = 979775) B979775
theorem B620903 : Blo 287828 620903 := bstep (se 1 (by rfl) ⟨465677, by rfl⟩ : syracuseStep 620903 = 931355) B931355
theorem B326191 : Blo 287828 326191 := bstep (se 1 (by rfl) ⟨244643, by rfl⟩ : syracuseStep 326191 = 489287) B489287
theorem B883271 : Blo 287828 883271 := bstep (se 1 (by rfl) ⟨662453, by rfl⟩ : syracuseStep 883271 = 1324907) B1324907
theorem B621211 : Blo 287828 621211 := bstep (se 1 (by rfl) ⟨465908, by rfl⟩ : syracuseStep 621211 = 931817) B931817
theorem B7010975 : Blo 287828 7010975 := bstep (se 1 (by rfl) ⟨5258231, by rfl⟩ : syracuseStep 7010975 = 10516463) B10516463
theorem B981881 : Blo 287828 981881 := bstep (se 2 (by rfl) ⟨368205, by rfl⟩ : syracuseStep 981881 = 736411) B736411
theorem B982151 : Blo 287828 982151 := bstep (se 1 (by rfl) ⟨736613, by rfl⟩ : syracuseStep 982151 = 1473227) B1473227
theorem B232815779 : Blo 287828 232815779 := bstep (se 1 (by rfl) ⟨174611834, by rfl⟩ : syracuseStep 232815779 = 349223669) B349223669
theorem B982313 : Blo 287828 982313 := bstep (se 2 (by rfl) ⟨368367, by rfl⟩ : syracuseStep 982313 = 736735) B736735
theorem B654713 : Blo 287828 654713 := bstep (se 2 (by rfl) ⟨245517, by rfl⟩ : syracuseStep 654713 = 491035) B491035
theorem B622151 : Blo 287828 622151 := bstep (se 1 (by rfl) ⟨466613, by rfl⟩ : syracuseStep 622151 = 933227) B933227
theorem B655019 : Blo 287828 655019 := bstep (se 1 (by rfl) ⟨491264, by rfl⟩ : syracuseStep 655019 = 982529) B982529
theorem B193625977 : Blo 287828 193625977 := bstep (se 2 (by rfl) ⟨72609741, by rfl⟩ : syracuseStep 193625977 = 145219483) B145219483
theorem B1474847 : Blo 287828 1474847 := bstep (se 1 (by rfl) ⟨1106135, by rfl⟩ : syracuseStep 1474847 = 2212271) B2212271
theorem B491879 : Blo 287828 491879 := bstep (se 1 (by rfl) ⟨368909, by rfl⟩ : syracuseStep 491879 = 737819) B737819
theorem B1475819 : Blo 287828 1475819 := bstep (se 1 (by rfl) ⟨1106864, by rfl⟩ : syracuseStep 1475819 = 2213729) B2213729
theorem B1181083 : Blo 287828 1181083 := bstep (se 1 (by rfl) ⟨885812, by rfl⟩ : syracuseStep 1181083 = 1771625) B1771625
theorem B820763 : Blo 287828 820763 := bstep (se 1 (by rfl) ⟨615572, by rfl⟩ : syracuseStep 820763 = 1231145) B1231145
theorem B8521805 : Blo 287828 8521805 := bstep (se 3 (by rfl) ⟨1597838, by rfl⟩ : syracuseStep 8521805 = 3195677) B3195677
theorem B1182059 : Blo 287828 1182059 := bstep (se 1 (by rfl) ⟨886544, by rfl⟩ : syracuseStep 1182059 = 1773089) B1773089
theorem B120720145 : Blo 287828 120720145 := bstep (se 2 (by rfl) ⟨45270054, by rfl⟩ : syracuseStep 120720145 = 90540109) B90540109
theorem B5376901 : Blo 287828 5376901 := bstep (se 4 (by rfl) ⟨504084, by rfl⟩ : syracuseStep 5376901 = 1008169) B1008169
theorem B4230053 : Blo 287828 4230053 := bstep (se 4 (by rfl) ⟨396567, by rfl⟩ : syracuseStep 4230053 = 793135) B793135
theorem B822575 : Blo 287828 822575 := bstep (se 1 (by rfl) ⟨616931, by rfl⟩ : syracuseStep 822575 = 1233863) B1233863
theorem B5199203933 : Blo 287828 5199203933 := bstep (se 3 (by rfl) ⟨974850737, by rfl⟩ : syracuseStep 5199203933 = 1949701475) B1949701475
theorem B888527 : Blo 287828 888527 := bstep (se 1 (by rfl) ⟨666395, by rfl⟩ : syracuseStep 888527 = 1332791) B1332791
theorem B626459 : Blo 287828 626459 := bstep (se 1 (by rfl) ⟨469844, by rfl⟩ : syracuseStep 626459 = 939689) B939689
theorem B11046779 : Blo 287828 11046779 := bstep (se 1 (by rfl) ⟨8285084, by rfl⟩ : syracuseStep 11046779 = 16570169) B16570169
theorem B365791 : Blo 287828 365791 := bstep (se 1 (by rfl) ⟨274343, by rfl⟩ : syracuseStep 365791 = 548687) B548687
theorem B2102527 : Blo 287828 2102527 := bstep (se 1 (by rfl) ⟨1576895, by rfl⟩ : syracuseStep 2102527 = 3153791) B3153791
theorem B6657545 : Blo 287828 6657545 := bstep (se 2 (by rfl) ⟨2496579, by rfl⟩ : syracuseStep 6657545 = 4993159) B4993159
theorem B431849 : Blo 287828 431849 := bstep (se 2 (by rfl) ⟨161943, by rfl⟩ : syracuseStep 431849 = 323887) B323887
theorem B431975 : Blo 287828 431975 := bstep (se 1 (by rfl) ⟨323981, by rfl⟩ : syracuseStep 431975 = 647963) B647963
theorem B366439 : Blo 287828 366439 := bstep (se 1 (by rfl) ⟨274829, by rfl⟩ : syracuseStep 366439 = 549659) B549659
theorem B3382073 : Blo 287828 3382073 := bstep (se 2 (by rfl) ⟨1268277, by rfl⟩ : syracuseStep 3382073 = 2536555) B2536555
theorem B432959 : Blo 287828 432959 := bstep (se 1 (by rfl) ⟨324719, by rfl⟩ : syracuseStep 432959 = 649439) B649439
theorem B433247 : Blo 287828 433247 := bstep (se 1 (by rfl) ⟨324935, by rfl⟩ : syracuseStep 433247 = 649871) B649871
theorem B433643 : Blo 287828 433643 := bstep (se 1 (by rfl) ⟨325232, by rfl⟩ : syracuseStep 433643 = 650465) B650465
theorem B433769 : Blo 287828 433769 := bstep (se 2 (by rfl) ⟨162663, by rfl⟩ : syracuseStep 433769 = 325327) B325327
theorem B433871 : Blo 287828 433871 := bstep (se 1 (by rfl) ⟨325403, by rfl⟩ : syracuseStep 433871 = 650807) B650807
theorem B434087 : Blo 287828 434087 := bstep (se 1 (by rfl) ⟨325565, by rfl⟩ : syracuseStep 434087 = 651131) B651131
theorem B434303 : Blo 287828 434303 := bstep (se 1 (by rfl) ⟨325727, by rfl⟩ : syracuseStep 434303 = 651455) B651455
theorem B1810895 : Blo 287828 1810895 := bstep (se 1 (by rfl) ⟨1358171, by rfl⟩ : syracuseStep 1810895 = 2716343) B2716343
theorem B434735 : Blo 287828 434735 := bstep (se 1 (by rfl) ⟨326051, by rfl⟩ : syracuseStep 434735 = 652103) B652103
theorem B434921 : Blo 287828 434921 := bstep (se 2 (by rfl) ⟨163095, by rfl⟩ : syracuseStep 434921 = 326191) B326191
theorem B434939 : Blo 287828 434939 := bstep (se 1 (by rfl) ⟨326204, by rfl⟩ : syracuseStep 434939 = 652409) B652409
theorem B729881 : Blo 287828 729881 := bstep (se 2 (by rfl) ⟨273705, by rfl⟩ : syracuseStep 729881 = 547411) B547411
theorem B828281 : Blo 287828 828281 := bstep (se 2 (by rfl) ⟨310605, by rfl⟩ : syracuseStep 828281 = 621211) B621211
theorem B435383 : Blo 287828 435383 := bstep (se 1 (by rfl) ⟨326537, by rfl⟩ : syracuseStep 435383 = 653075) B653075
theorem B435455 : Blo 287828 435455 := bstep (se 1 (by rfl) ⟨326591, by rfl⟩ : syracuseStep 435455 = 653183) B653183
theorem B731369 : Blo 287828 731369 := bstep (se 2 (by rfl) ⟨274263, by rfl⟩ : syracuseStep 731369 = 548527) B548527
theorem B436475 : Blo 287828 436475 := bstep (se 1 (by rfl) ⟨327356, by rfl⟩ : syracuseStep 436475 = 654713) B654713
theorem B436679 : Blo 287828 436679 := bstep (se 1 (by rfl) ⟨327509, by rfl⟩ : syracuseStep 436679 = 655019) B655019
theorem B2206439 : Blo 287828 2206439 := bstep (se 1 (by rfl) ⟨1654829, by rfl⟩ : syracuseStep 2206439 = 3309659) B3309659
theorem B437159 : Blo 287828 437159 := bstep (se 1 (by rfl) ⟨327869, by rfl⟩ : syracuseStep 437159 = 655739) B655739
theorem B128789423 : Blo 287828 128789423 := bstep (se 1 (by rfl) ⟨96592067, by rfl⟩ : syracuseStep 128789423 = 193184135) B193184135
theorem B437231 : Blo 287828 437231 := bstep (se 1 (by rfl) ⟨327923, by rfl⟩ : syracuseStep 437231 = 655847) B655847
theorem B437339 : Blo 287828 437339 := bstep (se 1 (by rfl) ⟨328004, by rfl⟩ : syracuseStep 437339 = 656009) B656009
theorem B2798063 : Blo 287828 2798063 := bstep (se 1 (by rfl) ⟨2098547, by rfl⟩ : syracuseStep 2798063 = 4197095) B4197095
theorem B1094867 : Blo 287828 1094867 := bstep (se 1 (by rfl) ⟨821150, by rfl⟩ : syracuseStep 1094867 = 1642301) B1642301
theorem B1095551 : Blo 287828 1095551 := bstep (se 1 (by rfl) ⟨821663, by rfl⟩ : syracuseStep 1095551 = 1643327) B1643327
theorem B931895 : Blo 287828 931895 := bstep (se 1 (by rfl) ⟨698921, by rfl⟩ : syracuseStep 931895 = 1397843) B1397843
theorem B735419 : Blo 287828 735419 := bstep (se 1 (by rfl) ⟨551564, by rfl⟩ : syracuseStep 735419 = 1103129) B1103129
theorem B2078941 : Blo 287828 2078941 := bstep (se 3 (by rfl) ⟨389801, by rfl⟩ : syracuseStep 2078941 = 779603) B779603
theorem B735551 : Blo 287828 735551 := bstep (se 1 (by rfl) ⟨551663, by rfl⟩ : syracuseStep 735551 = 1103327) B1103327
theorem B60833045 : Blo 287828 60833045 := bstep (se 6 (by rfl) ⟨1425774, by rfl⟩ : syracuseStep 60833045 = 2851549) B2851549
theorem B4702009 : Blo 287828 4702009 := bstep (se 2 (by rfl) ⟨1763253, by rfl⟩ : syracuseStep 4702009 = 3526507) B3526507
theorem B1359679 : Blo 287828 1359679 := bstep (se 1 (by rfl) ⟨1019759, by rfl⟩ : syracuseStep 1359679 = 2039519) B2039519
theorem B49725613 : Blo 287828 49725613 := bstep (se 3 (by rfl) ⟨9323552, by rfl⟩ : syracuseStep 49725613 = 18647105) B18647105
theorem B737657 : Blo 287828 737657 := bstep (se 2 (by rfl) ⟨276621, by rfl⟩ : syracuseStep 737657 = 553243) B553243
theorem B934355 : Blo 287828 934355 := bstep (se 1 (by rfl) ⟨700766, by rfl⟩ : syracuseStep 934355 = 1401533) B1401533
theorem B737849 : Blo 287828 737849 := bstep (se 2 (by rfl) ⟨276693, by rfl⟩ : syracuseStep 737849 = 553387) B553387
theorem B1655741 : Blo 287828 1655741 := bstep (se 3 (by rfl) ⟨310451, by rfl⟩ : syracuseStep 1655741 = 620903) B620903
theorem B18695933 : Blo 287828 18695933 := bstep (se 3 (by rfl) ⟨3505487, by rfl⟩ : syracuseStep 18695933 = 7010975) B7010975
theorem B4507907 : Blo 287828 4507907 := bstep (se 1 (by rfl) ⟨3380930, by rfl⟩ : syracuseStep 4507907 = 6761861) B6761861
theorem B155210519 : Blo 287828 155210519 := bstep (se 1 (by rfl) ⟨116407889, by rfl⟩ : syracuseStep 155210519 = 232815779) B232815779
theorem B1233913 : Blo 287828 1233913 := bstep (se 2 (by rfl) ⟨462717, by rfl⟩ : syracuseStep 1233913 = 925435) B925435
theorem B414767 : Blo 287828 414767 := bstep (se 1 (by rfl) ⟨311075, by rfl⟩ : syracuseStep 414767 = 622151) B622151
theorem B258167969 : Blo 287828 258167969 := bstep (se 2 (by rfl) ⟨96812988, by rfl⟩ : syracuseStep 258167969 = 193625977) B193625977
theorem B971999 : Blo 287828 971999 := bstep (se 1 (by rfl) ⟨728999, by rfl⟩ : syracuseStep 971999 = 1457999) B1457999
theorem B415211 : Blo 287828 415211 := bstep (se 1 (by rfl) ⟨311408, by rfl⟩ : syracuseStep 415211 = 622817) B622817
theorem B1660571 : Blo 287828 1660571 := bstep (se 1 (by rfl) ⟨1245428, by rfl⟩ : syracuseStep 1660571 = 2490857) B2490857
theorem B5953283 : Blo 287828 5953283 := bstep (se 1 (by rfl) ⟨4464962, by rfl⟩ : syracuseStep 5953283 = 8929925) B8929925
theorem B1038203 : Blo 287828 1038203 := bstep (se 1 (by rfl) ⟨778652, by rfl⟩ : syracuseStep 1038203 = 1557305) B1557305
theorem B5560447 : Blo 287828 5560447 := bstep (se 1 (by rfl) ⟨4170335, by rfl⟩ : syracuseStep 5560447 = 8340671) B8340671
theorem B547631 : Blo 287828 547631 := bstep (se 1 (by rfl) ⟨410723, by rfl⟩ : syracuseStep 547631 = 821447) B821447
theorem B974105 : Blo 287828 974105 := bstep (se 2 (by rfl) ⟨365289, by rfl⟩ : syracuseStep 974105 = 730579) B730579
theorem B7822817 : Blo 287828 7822817 := bstep (se 2 (by rfl) ⟨2933556, by rfl⟩ : syracuseStep 7822817 = 5867113) B5867113
theorem B1106075 : Blo 287828 1106075 := bstep (se 1 (by rfl) ⟨829556, by rfl⟩ : syracuseStep 1106075 = 1659113) B1659113
theorem B975023 : Blo 287828 975023 := bstep (se 1 (by rfl) ⟨731267, by rfl⟩ : syracuseStep 975023 = 1462535) B1462535
theorem B1106243 : Blo 287828 1106243 := bstep (se 1 (by rfl) ⟨829682, by rfl⟩ : syracuseStep 1106243 = 1659365) B1659365
theorem B975401 : Blo 287828 975401 := bstep (se 2 (by rfl) ⟨365775, by rfl⟩ : syracuseStep 975401 = 731551) B731551
theorem B2187971 : Blo 287828 2187971 := bstep (se 1 (by rfl) ⟨1640978, by rfl⟩ : syracuseStep 2187971 = 3281957) B3281957
theorem B3695483 : Blo 287828 3695483 := bstep (se 1 (by rfl) ⟨2771612, by rfl⟩ : syracuseStep 3695483 = 5543225) B5543225
theorem B1401799 : Blo 287828 1401799 := bstep (se 1 (by rfl) ⟨1051349, by rfl⟩ : syracuseStep 1401799 = 2102699) B2102699
theorem B648161 : Blo 287828 648161 := bstep (se 2 (by rfl) ⟨243060, by rfl⟩ : syracuseStep 648161 = 486121) B486121
theorem B648233 : Blo 287828 648233 := bstep (se 2 (by rfl) ⟨243087, by rfl⟩ : syracuseStep 648233 = 486175) B486175
theorem B287871 : Blo 287828 287871 := bstep (se 1 (by rfl) ⟨215903, by rfl⟩ : syracuseStep 287871 = 431807) B431807
theorem B550631 : Blo 287828 550631 := bstep (se 1 (by rfl) ⟨412973, by rfl⟩ : syracuseStep 550631 = 825947) B825947
theorem B976751 : Blo 287828 976751 := bstep (se 1 (by rfl) ⟨732563, by rfl⟩ : syracuseStep 976751 = 1465127) B1465127
theorem B1042415 : Blo 287828 1042415 := bstep (se 1 (by rfl) ⟨781811, by rfl⟩ : syracuseStep 1042415 = 1563623) B1563623
theorem B944467 : Blo 287828 944467 := bstep (se 1 (by rfl) ⟨708350, by rfl⟩ : syracuseStep 944467 = 1416701) B1416701
theorem B289215 : Blo 287828 289215 := bstep (se 1 (by rfl) ⟨216911, by rfl⟩ : syracuseStep 289215 = 433823) B433823
theorem B486047 : Blo 287828 486047 := bstep (se 1 (by rfl) ⟨364535, by rfl⟩ : syracuseStep 486047 = 729071) B729071
theorem B519419 : Blo 287828 519419 := bstep (se 1 (by rfl) ⟨389564, by rfl⟩ : syracuseStep 519419 = 779129) B779129
theorem B290351 : Blo 287828 290351 := bstep (se 1 (by rfl) ⟨217763, by rfl⟩ : syracuseStep 290351 = 435527) B435527
theorem B978587 : Blo 287828 978587 := bstep (se 1 (by rfl) ⟨733940, by rfl⟩ : syracuseStep 978587 = 1467881) B1467881
theorem B2223983 : Blo 287828 2223983 := bstep (se 1 (by rfl) ⟨1667987, by rfl⟩ : syracuseStep 2223983 = 3335975) B3335975
theorem B290907 : Blo 287828 290907 := bstep (se 1 (by rfl) ⟨218180, by rfl⟩ : syracuseStep 290907 = 436361) B436361
theorem B290975 : Blo 287828 290975 := bstep (se 1 (by rfl) ⟨218231, by rfl⟩ : syracuseStep 290975 = 436463) B436463
theorem B2355389 : Blo 287828 2355389 := bstep (se 3 (by rfl) ⟨441635, by rfl⟩ : syracuseStep 2355389 = 883271) B883271
theorem B291039 : Blo 287828 291039 := bstep (se 1 (by rfl) ⟨218279, by rfl⟩ : syracuseStep 291039 = 436559) B436559
theorem B291359 : Blo 287828 291359 := bstep (se 1 (by rfl) ⟨218519, by rfl⟩ : syracuseStep 291359 = 437039) B437039
theorem B520831 : Blo 287828 520831 := bstep (se 1 (by rfl) ⟨390623, by rfl⟩ : syracuseStep 520831 = 781247) B781247
theorem B3732389 : Blo 287828 3732389 := bstep (se 4 (by rfl) ⟨349911, by rfl⟩ : syracuseStep 3732389 = 699823) B699823
theorem B291807 : Blo 287828 291807 := bstep (se 1 (by rfl) ⟨218855, by rfl⟩ : syracuseStep 291807 = 437711) B437711
theorem B488551 : Blo 287828 488551 := bstep (se 1 (by rfl) ⟨366413, by rfl⟩ : syracuseStep 488551 = 732827) B732827
theorem B980153 : Blo 287828 980153 := bstep (se 2 (by rfl) ⟨367557, by rfl⟩ : syracuseStep 980153 = 735115) B735115
theorem B488639 : Blo 287828 488639 := bstep (se 1 (by rfl) ⟨366479, by rfl⟩ : syracuseStep 488639 = 732959) B732959
theorem B980477 : Blo 287828 980477 := bstep (se 3 (by rfl) ⟨183839, by rfl⟩ : syracuseStep 980477 = 367679) B367679
theorem B784091 : Blo 287828 784091 := bstep (se 1 (by rfl) ⟨588068, by rfl⟩ : syracuseStep 784091 = 1176137) B1176137
theorem B653723 : Blo 287828 653723 := bstep (se 1 (by rfl) ⟨490292, by rfl⟩ : syracuseStep 653723 = 980585) B980585
theorem B2783915 : Blo 287828 2783915 := bstep (se 1 (by rfl) ⟨2087936, by rfl⟩ : syracuseStep 2783915 = 4175873) B4175873
theorem B4291553 : Blo 287828 4291553 := bstep (se 2 (by rfl) ⟨1609332, by rfl⟩ : syracuseStep 4291553 = 3218665) B3218665
theorem B654587 : Blo 287828 654587 := bstep (se 1 (by rfl) ⟨490940, by rfl⟩ : syracuseStep 654587 = 981881) B981881
theorem B654767 : Blo 287828 654767 := bstep (se 1 (by rfl) ⟨491075, by rfl⟩ : syracuseStep 654767 = 982151) B982151
theorem B654875 : Blo 287828 654875 := bstep (se 1 (by rfl) ⟨491156, by rfl⟩ : syracuseStep 654875 = 982313) B982313
theorem B983231 : Blo 287828 983231 := bstep (se 1 (by rfl) ⟨737423, by rfl⟩ : syracuseStep 983231 = 1474847) B1474847
theorem B327919 : Blo 287828 327919 := bstep (se 1 (by rfl) ⟨245939, by rfl⟩ : syracuseStep 327919 = 491879) B491879
theorem B491771 : Blo 287828 491771 := bstep (se 1 (by rfl) ⟨368828, by rfl⟩ : syracuseStep 491771 = 737657) B737657
theorem B622903 : Blo 287828 622903 := bstep (se 1 (by rfl) ⟨467177, by rfl⟩ : syracuseStep 622903 = 934355) B934355
theorem B491899 : Blo 287828 491899 := bstep (se 1 (by rfl) ⟨368924, by rfl⟩ : syracuseStep 491899 = 737849) B737849
theorem B983879 : Blo 287828 983879 := bstep (se 1 (by rfl) ⟨737909, by rfl⟩ : syracuseStep 983879 = 1475819) B1475819
theorem B1869065 : Blo 287828 1869065 := bstep (se 2 (by rfl) ⟨700899, by rfl⟩ : syracuseStep 1869065 = 1401799) B1401799
theorem B788039 : Blo 287828 788039 := bstep (se 1 (by rfl) ⟨591029, by rfl⟩ : syracuseStep 788039 = 1182059) B1182059
theorem B1574777 : Blo 287828 1574777 := bstep (se 2 (by rfl) ⟨590541, by rfl⟩ : syracuseStep 1574777 = 1181083) B1181083
theorem B2820035 : Blo 287828 2820035 := bstep (se 1 (by rfl) ⟨2115026, by rfl⟩ : syracuseStep 2820035 = 4230053) B4230053
theorem B413894717 : Blo 287828 413894717 := bstep (se 3 (by rfl) ⟨77605259, by rfl⟩ : syracuseStep 413894717 = 155210519) B155210519
theorem B3466135955 : Blo 287828 3466135955 := bstep (se 1 (by rfl) ⟨2599601966, by rfl⟩ : syracuseStep 3466135955 = 5199203933) B5199203933
theorem B592351 : Blo 287828 592351 := bstep (se 1 (by rfl) ⟨444263, by rfl⟩ : syracuseStep 592351 = 888527) B888527
theorem B160960193 : Blo 287828 160960193 := bstep (se 2 (by rfl) ⟨60360072, by rfl⟩ : syracuseStep 160960193 = 120720145) B120720145
theorem B3968855 : Blo 287828 3968855 := bstep (se 1 (by rfl) ⟨2976641, by rfl⟩ : syracuseStep 3968855 = 5953283) B5953283
theorem B692135 : Blo 287828 692135 := bstep (se 1 (by rfl) ⟨519101, by rfl⟩ : syracuseStep 692135 = 1038203) B1038203
theorem B365087 : Blo 287828 365087 := bstep (se 1 (by rfl) ⟨273815, by rfl⟩ : syracuseStep 365087 = 547631) B547631
theorem B5215211 : Blo 287828 5215211 := bstep (se 1 (by rfl) ⟨3911408, by rfl⟩ : syracuseStep 5215211 = 7822817) B7822817
theorem B2463655 : Blo 287828 2463655 := bstep (se 1 (by rfl) ⟨1847741, by rfl⟩ : syracuseStep 2463655 = 3695483) B3695483
theorem B432107 : Blo 287828 432107 := bstep (se 1 (by rfl) ⟨324080, by rfl⟩ : syracuseStep 432107 = 648161) B648161
theorem B432155 : Blo 287828 432155 := bstep (se 1 (by rfl) ⟨324116, by rfl⟩ : syracuseStep 432155 = 648233) B648233
theorem B694441 : Blo 287828 694441 := bstep (se 2 (by rfl) ⟨260415, by rfl⟩ : syracuseStep 694441 = 520831) B520831
theorem B367087 : Blo 287828 367087 := bstep (se 1 (by rfl) ⟨275315, by rfl⟩ : syracuseStep 367087 = 550631) B550631
theorem B694943 : Blo 287828 694943 := bstep (se 1 (by rfl) ⟨521207, by rfl⟩ : syracuseStep 694943 = 1042415) B1042415
theorem B1645217 : Blo 287828 1645217 := bstep (se 2 (by rfl) ⟨616956, by rfl⟩ : syracuseStep 1645217 = 1233913) B1233913
theorem B85859615 : Blo 287828 85859615 := bstep (se 1 (by rfl) ⟨64394711, by rfl⟩ : syracuseStep 85859615 = 128789423) B128789423
theorem B11444141 : Blo 287828 11444141 := bstep (se 3 (by rfl) ⟨2145776, by rfl⟩ : syracuseStep 11444141 = 4291553) B4291553
theorem B7413929 : Blo 287828 7413929 := bstep (se 2 (by rfl) ⟨2780223, by rfl⟩ : syracuseStep 7413929 = 5560447) B5560447
theorem B729911 : Blo 287828 729911 := bstep (se 1 (by rfl) ⟨547433, by rfl⟩ : syracuseStep 729911 = 1094867) B1094867
theorem B730367 : Blo 287828 730367 := bstep (se 1 (by rfl) ⟨547775, by rfl⟩ : syracuseStep 730367 = 1095551) B1095551
theorem B435815 : Blo 287828 435815 := bstep (se 1 (by rfl) ⟨326861, by rfl⟩ : syracuseStep 435815 = 653723) B653723
theorem B436391 : Blo 287828 436391 := bstep (se 1 (by rfl) ⟨327293, by rfl⟩ : syracuseStep 436391 = 654587) B654587
theorem B436511 : Blo 287828 436511 := bstep (se 1 (by rfl) ⟨327383, by rfl⟩ : syracuseStep 436511 = 654767) B654767
theorem B436583 : Blo 287828 436583 := bstep (se 1 (by rfl) ⟨327437, by rfl⟩ : syracuseStep 436583 = 654875) B654875
theorem B6269345 : Blo 287828 6269345 := bstep (se 2 (by rfl) ⟨2351004, by rfl⟩ : syracuseStep 6269345 = 4702009) B4702009
theorem B1812905 : Blo 287828 1812905 := bstep (se 2 (by rfl) ⟨679839, by rfl⟩ : syracuseStep 1812905 = 1359679) B1359679
theorem B66300817 : Blo 287828 66300817 := bstep (se 2 (by rfl) ⟨24862806, by rfl⟩ : syracuseStep 66300817 = 49725613) B49725613
theorem B12463955 : Blo 287828 12463955 := bstep (se 1 (by rfl) ⟨9347966, by rfl⟩ : syracuseStep 12463955 = 18695933) B18695933
theorem B4829053 : Blo 287828 4829053 := bstep (se 3 (by rfl) ⟨905447, by rfl⟩ : syracuseStep 4829053 = 1810895) B1810895
theorem B172111979 : Blo 287828 172111979 := bstep (se 1 (by rfl) ⟨129083984, by rfl⟩ : syracuseStep 172111979 = 258167969) B258167969
theorem B4438363 : Blo 287828 4438363 := bstep (se 1 (by rfl) ⟨3328772, by rfl⟩ : syracuseStep 4438363 = 6657545) B6657545
theorem B737383 : Blo 287828 737383 := bstep (se 1 (by rfl) ⟨553037, by rfl⟩ : syracuseStep 737383 = 1106075) B1106075
theorem B22724813 : Blo 287828 22724813 := bstep (se 3 (by rfl) ⟨4260902, by rfl⟩ : syracuseStep 22724813 = 8521805) B8521805
theorem B737495 : Blo 287828 737495 := bstep (se 1 (by rfl) ⟨553121, by rfl⟩ : syracuseStep 737495 = 1106243) B1106243
theorem B1458647 : Blo 287828 1458647 := bstep (se 1 (by rfl) ⟨1093985, by rfl⟩ : syracuseStep 1458647 = 2187971) B2187971
theorem B2803369 : Blo 287828 2803369 := bstep (se 2 (by rfl) ⟨1051263, by rfl⟩ : syracuseStep 2803369 = 2102527) B2102527
theorem B346279 : Blo 287828 346279 := bstep (se 1 (by rfl) ⟨259709, by rfl⟩ : syracuseStep 346279 = 519419) B519419
theorem B2771921 : Blo 287828 2771921 := bstep (se 2 (by rfl) ⟨1039470, by rfl⟩ : syracuseStep 2771921 = 2078941) B2078941
theorem B1855943 : Blo 287828 1855943 := bstep (se 1 (by rfl) ⟨1391957, by rfl⟩ : syracuseStep 1855943 = 2783915) B2783915
theorem B40555363 : Blo 287828 40555363 := bstep (se 1 (by rfl) ⟨30416522, by rfl⟩ : syracuseStep 40555363 = 60833045) B60833045
theorem B1103827 : Blo 287828 1103827 := bstep (se 1 (by rfl) ⟨827870, by rfl⟩ : syracuseStep 1103827 = 1655741) B1655741
theorem B547175 : Blo 287828 547175 := bstep (se 1 (by rfl) ⟨410381, by rfl⟩ : syracuseStep 547175 = 820763) B820763
theorem B5037157 : Blo 287828 5037157 := bstep (se 4 (by rfl) ⟨472233, by rfl⟩ : syracuseStep 5037157 = 944467) B944467
theorem B548383 : Blo 287828 548383 := bstep (se 1 (by rfl) ⟨411287, by rfl⟩ : syracuseStep 548383 = 822575) B822575
theorem B7364519 : Blo 287828 7364519 := bstep (se 1 (by rfl) ⟨5523389, by rfl⟩ : syracuseStep 7364519 = 11046779) B11046779
theorem B1106045 : Blo 287828 1106045 := bstep (se 3 (by rfl) ⟨207383, by rfl⟩ : syracuseStep 1106045 = 414767) B414767
theorem B647999 : Blo 287828 647999 := bstep (se 1 (by rfl) ⟨485999, by rfl⟩ : syracuseStep 647999 = 971999) B971999
theorem B1107047 : Blo 287828 1107047 := bstep (se 1 (by rfl) ⟨830285, by rfl⟩ : syracuseStep 1107047 = 1660571) B1660571
theorem B287899 : Blo 287828 287899 := bstep (se 1 (by rfl) ⟨215924, by rfl⟩ : syracuseStep 287899 = 431849) B431849
theorem B7169201 : Blo 287828 7169201 := bstep (se 2 (by rfl) ⟨2688450, by rfl⟩ : syracuseStep 7169201 = 5376901) B5376901
theorem B287983 : Blo 287828 287983 := bstep (se 1 (by rfl) ⟨215987, by rfl⟩ : syracuseStep 287983 = 431975) B431975
theorem B1107229 : Blo 287828 1107229 := bstep (se 3 (by rfl) ⟨207605, by rfl⟩ : syracuseStep 1107229 = 415211) B415211
theorem B2254715 : Blo 287828 2254715 := bstep (se 1 (by rfl) ⟨1691036, by rfl⟩ : syracuseStep 2254715 = 3382073) B3382073
theorem B288639 : Blo 287828 288639 := bstep (se 1 (by rfl) ⟨216479, by rfl⟩ : syracuseStep 288639 = 432959) B432959
theorem B2090909 : Blo 287828 2090909 := bstep (se 3 (by rfl) ⟨392045, by rfl⟩ : syracuseStep 2090909 = 784091) B784091
theorem B288831 : Blo 287828 288831 := bstep (se 1 (by rfl) ⟨216623, by rfl⟩ : syracuseStep 288831 = 433247) B433247
theorem B649403 : Blo 287828 649403 := bstep (se 1 (by rfl) ⟨487052, by rfl⟩ : syracuseStep 649403 = 974105) B974105
theorem B289095 : Blo 287828 289095 := bstep (se 1 (by rfl) ⟨216821, by rfl⟩ : syracuseStep 289095 = 433643) B433643
theorem B289179 : Blo 287828 289179 := bstep (se 1 (by rfl) ⟨216884, by rfl⟩ : syracuseStep 289179 = 433769) B433769
theorem B289247 : Blo 287828 289247 := bstep (se 1 (by rfl) ⟨216935, by rfl⟩ : syracuseStep 289247 = 433871) B433871
theorem B289391 : Blo 287828 289391 := bstep (se 1 (by rfl) ⟨217043, by rfl⟩ : syracuseStep 289391 = 434087) B434087
theorem B289535 : Blo 287828 289535 := bstep (se 1 (by rfl) ⟨217151, by rfl⟩ : syracuseStep 289535 = 434303) B434303
theorem B650015 : Blo 287828 650015 := bstep (se 1 (by rfl) ⟨487511, by rfl⟩ : syracuseStep 650015 = 975023) B975023
theorem B650267 : Blo 287828 650267 := bstep (se 1 (by rfl) ⟨487700, by rfl⟩ : syracuseStep 650267 = 975401) B975401
theorem B289823 : Blo 287828 289823 := bstep (se 1 (by rfl) ⟨217367, by rfl⟩ : syracuseStep 289823 = 434735) B434735
theorem B289947 : Blo 287828 289947 := bstep (se 1 (by rfl) ⟨217460, by rfl⟩ : syracuseStep 289947 = 434921) B434921
theorem B289959 : Blo 287828 289959 := bstep (se 1 (by rfl) ⟨217469, by rfl⟩ : syracuseStep 289959 = 434939) B434939
theorem B486587 : Blo 287828 486587 := bstep (se 1 (by rfl) ⟨364940, by rfl⟩ : syracuseStep 486587 = 729881) B729881
theorem B552187 : Blo 287828 552187 := bstep (se 1 (by rfl) ⟨414140, by rfl⟩ : syracuseStep 552187 = 828281) B828281
theorem B12021085 : Blo 287828 12021085 := bstep (se 3 (by rfl) ⟨2253953, by rfl⟩ : syracuseStep 12021085 = 4507907) B4507907
theorem B290255 : Blo 287828 290255 := bstep (se 1 (by rfl) ⟨217691, by rfl⟩ : syracuseStep 290255 = 435383) B435383
theorem B290303 : Blo 287828 290303 := bstep (se 1 (by rfl) ⟨217727, by rfl⟩ : syracuseStep 290303 = 435455) B435455
theorem B651167 : Blo 287828 651167 := bstep (se 1 (by rfl) ⟨488375, by rfl⟩ : syracuseStep 651167 = 976751) B976751
theorem B651401 : Blo 287828 651401 := bstep (se 2 (by rfl) ⟨244275, by rfl⟩ : syracuseStep 651401 = 488551) B488551
theorem B487579 : Blo 287828 487579 := bstep (se 1 (by rfl) ⟨365684, by rfl⟩ : syracuseStep 487579 = 731369) B731369
theorem B290983 : Blo 287828 290983 := bstep (se 1 (by rfl) ⟨218237, by rfl⟩ : syracuseStep 290983 = 436475) B436475
theorem B487721 : Blo 287828 487721 := bstep (se 2 (by rfl) ⟨182895, by rfl⟩ : syracuseStep 487721 = 365791) B365791
theorem B291119 : Blo 287828 291119 := bstep (se 1 (by rfl) ⟨218339, by rfl⟩ : syracuseStep 291119 = 436679) B436679
theorem B324031 : Blo 287828 324031 := bstep (se 1 (by rfl) ⟨243023, by rfl⟩ : syracuseStep 324031 = 486047) B486047
theorem B1470959 : Blo 287828 1470959 := bstep (se 1 (by rfl) ⟨1103219, by rfl⟩ : syracuseStep 1470959 = 2206439) B2206439
theorem B291439 : Blo 287828 291439 := bstep (se 1 (by rfl) ⟨218579, by rfl⟩ : syracuseStep 291439 = 437159) B437159
theorem B291487 : Blo 287828 291487 := bstep (se 1 (by rfl) ⟨218615, by rfl⟩ : syracuseStep 291487 = 437231) B437231
theorem B291559 : Blo 287828 291559 := bstep (se 1 (by rfl) ⟨218669, by rfl⟩ : syracuseStep 291559 = 437339) B437339
theorem B652391 : Blo 287828 652391 := bstep (se 1 (by rfl) ⟨489293, by rfl⟩ : syracuseStep 652391 = 978587) B978587
theorem B488585 : Blo 287828 488585 := bstep (se 2 (by rfl) ⟨183219, by rfl⟩ : syracuseStep 488585 = 366439) B366439
theorem B1570259 : Blo 287828 1570259 := bstep (se 1 (by rfl) ⟨1177694, by rfl⟩ : syracuseStep 1570259 = 2355389) B2355389
theorem B1865375 : Blo 287828 1865375 := bstep (se 1 (by rfl) ⟨1399031, by rfl⟩ : syracuseStep 1865375 = 2798063) B2798063
theorem B2488259 : Blo 287828 2488259 := bstep (se 1 (by rfl) ⟨1866194, by rfl⟩ : syracuseStep 2488259 = 3732389) B3732389
theorem B653435 : Blo 287828 653435 := bstep (se 1 (by rfl) ⟨490076, by rfl⟩ : syracuseStep 653435 = 980153) B980153
theorem B325759 : Blo 287828 325759 := bstep (se 1 (by rfl) ⟨244319, by rfl⟩ : syracuseStep 325759 = 488639) B488639
theorem B653651 : Blo 287828 653651 := bstep (se 1 (by rfl) ⟨490238, by rfl⟩ : syracuseStep 653651 = 980477) B980477
theorem B621263 : Blo 287828 621263 := bstep (se 1 (by rfl) ⟨465947, by rfl⟩ : syracuseStep 621263 = 931895) B931895
theorem B490279 : Blo 287828 490279 := bstep (se 1 (by rfl) ⟨367709, by rfl⟩ : syracuseStep 490279 = 735419) B735419
theorem B490367 : Blo 287828 490367 := bstep (se 1 (by rfl) ⟨367775, by rfl⟩ : syracuseStep 490367 = 735551) B735551
theorem B1670557 : Blo 287828 1670557 := bstep (se 3 (by rfl) ⟨313229, by rfl⟩ : syracuseStep 1670557 = 626459) B626459
theorem B5930621 : Blo 287828 5930621 := bstep (se 3 (by rfl) ⟨1111991, by rfl⟩ : syracuseStep 5930621 = 2223983) B2223983
theorem B655487 : Blo 287828 655487 := bstep (se 1 (by rfl) ⟨491615, by rfl⟩ : syracuseStep 655487 = 983231) B983231
theorem B983177 : Blo 287828 983177 := bstep (se 2 (by rfl) ⟨368691, by rfl⟩ : syracuseStep 983177 = 737383) B737383
theorem B491663 : Blo 287828 491663 := bstep (se 1 (by rfl) ⟨368747, by rfl⟩ : syracuseStep 491663 = 737495) B737495
theorem B327847 : Blo 287828 327847 := bstep (se 1 (by rfl) ⟨245885, by rfl⟩ : syracuseStep 327847 = 491771) B491771
theorem B655865 : Blo 287828 655865 := bstep (se 2 (by rfl) ⟨245949, by rfl⟩ : syracuseStep 655865 = 491899) B491899
theorem B655919 : Blo 287828 655919 := bstep (se 1 (by rfl) ⟨491939, by rfl⟩ : syracuseStep 655919 = 983879) B983879
theorem B1246043 : Blo 287828 1246043 := bstep (se 1 (by rfl) ⟨934532, by rfl⟩ : syracuseStep 1246043 = 1869065) B1869065
theorem B525359 : Blo 287828 525359 := bstep (se 1 (by rfl) ⟨394019, by rfl⟩ : syracuseStep 525359 = 788039) B788039
theorem B1049851 : Blo 287828 1049851 := bstep (se 1 (by rfl) ⟨787388, by rfl⟩ : syracuseStep 1049851 = 1574777) B1574777
theorem B1476305 : Blo 287828 1476305 := bstep (se 2 (by rfl) ⟨553614, by rfl⟩ : syracuseStep 1476305 = 1107229) B1107229
theorem B3737825 : Blo 287828 3737825 := bstep (se 2 (by rfl) ⟨1401684, by rfl⟩ : syracuseStep 3737825 = 2803369) B2803369
theorem B461423 : Blo 287828 461423 := bstep (se 1 (by rfl) ⟨346067, by rfl⟩ : syracuseStep 461423 = 692135) B692135
theorem B461705 : Blo 287828 461705 := bstep (se 2 (by rfl) ⟨173139, by rfl⟩ : syracuseStep 461705 = 346279) B346279
theorem B3476807 : Blo 287828 3476807 := bstep (se 1 (by rfl) ⟨2607605, by rfl⟩ : syracuseStep 3476807 = 5215211) B5215211
theorem B463295 : Blo 287828 463295 := bstep (se 1 (by rfl) ⟨347471, by rfl⟩ : syracuseStep 463295 = 694943) B694943
theorem B16028113 : Blo 287828 16028113 := bstep (se 2 (by rfl) ⟨6010542, by rfl⟩ : syracuseStep 16028113 = 12021085) B12021085
theorem B431999 : Blo 287828 431999 := bstep (se 1 (by rfl) ⟨323999, by rfl⟩ : syracuseStep 431999 = 647999) B647999
theorem B432041 : Blo 287828 432041 := bstep (se 2 (by rfl) ⟨162015, by rfl⟩ : syracuseStep 432041 = 324031) B324031
theorem B54073817 : Blo 287828 54073817 := bstep (se 2 (by rfl) ⟨20277681, by rfl⟩ : syracuseStep 54073817 = 40555363) B40555363
theorem B432935 : Blo 287828 432935 := bstep (se 1 (by rfl) ⟨324701, by rfl⟩ : syracuseStep 432935 = 649403) B649403
theorem B433343 : Blo 287828 433343 := bstep (se 1 (by rfl) ⟨325007, by rfl⟩ : syracuseStep 433343 = 650015) B650015
theorem B433511 : Blo 287828 433511 := bstep (se 1 (by rfl) ⟨325133, by rfl⟩ : syracuseStep 433511 = 650267) B650267
theorem B3284873 : Blo 287828 3284873 := bstep (se 2 (by rfl) ⟨1231827, by rfl⟩ : syracuseStep 3284873 = 2463655) B2463655
theorem B434111 : Blo 287828 434111 := bstep (se 1 (by rfl) ⟨325583, by rfl⟩ : syracuseStep 434111 = 651167) B651167
theorem B434267 : Blo 287828 434267 := bstep (se 1 (by rfl) ⟨325700, by rfl⟩ : syracuseStep 434267 = 651401) B651401
theorem B434345 : Blo 287828 434345 := bstep (se 2 (by rfl) ⟨162879, by rfl⟩ : syracuseStep 434345 = 325759) B325759
theorem B925921 : Blo 287828 925921 := bstep (se 2 (by rfl) ⟨347220, by rfl⟩ : syracuseStep 925921 = 694441) B694441
theorem B434927 : Blo 287828 434927 := bstep (se 1 (by rfl) ⟨326195, by rfl⟩ : syracuseStep 434927 = 652391) B652391
theorem B435623 : Blo 287828 435623 := bstep (se 1 (by rfl) ⟨326717, by rfl⟩ : syracuseStep 435623 = 653435) B653435
theorem B435767 : Blo 287828 435767 := bstep (se 1 (by rfl) ⟨326825, by rfl⟩ : syracuseStep 435767 = 653651) B653651
theorem B731177 : Blo 287828 731177 := bstep (se 2 (by rfl) ⟨274191, by rfl⟩ : syracuseStep 731177 = 548383) B548383
theorem B437225 : Blo 287828 437225 := bstep (se 2 (by rfl) ⟨163959, by rfl⟩ : syracuseStep 437225 = 327919) B327919
theorem B830537 : Blo 287828 830537 := bstep (se 2 (by rfl) ⟨311451, by rfl⟩ : syracuseStep 830537 = 622903) B622903
theorem B60599501 : Blo 287828 60599501 := bstep (se 3 (by rfl) ⟨11362406, by rfl⟩ : syracuseStep 60599501 = 22724813) B22724813
theorem B1880023 : Blo 287828 1880023 := bstep (se 1 (by rfl) ⟨1410017, by rfl⟩ : syracuseStep 1880023 = 2820035) B2820035
theorem B1847947 : Blo 287828 1847947 := bstep (se 1 (by rfl) ⟨1385960, by rfl⟩ : syracuseStep 1847947 = 2771921) B2771921
theorem B3159205 : Blo 287828 3159205 := bstep (se 4 (by rfl) ⟨296175, by rfl⟩ : syracuseStep 3159205 = 592351) B592351
theorem B736249 : Blo 287828 736249 := bstep (se 2 (by rfl) ⟨276093, by rfl⟩ : syracuseStep 736249 = 552187) B552187
theorem B1096811 : Blo 287828 1096811 := bstep (se 1 (by rfl) ⟨822608, by rfl⟩ : syracuseStep 1096811 = 1645217) B1645217
theorem B6438737 : Blo 287828 6438737 := bstep (se 2 (by rfl) ⟨2414526, by rfl⟩ : syracuseStep 6438737 = 4829053) B4829053
theorem B737363 : Blo 287828 737363 := bstep (se 1 (by rfl) ⟨553022, by rfl⟩ : syracuseStep 737363 = 1106045) B1106045
theorem B458965277 : Blo 287828 458965277 := bstep (se 3 (by rfl) ⟨86055989, by rfl⟩ : syracuseStep 458965277 = 172111979) B172111979
theorem B738031 : Blo 287828 738031 := bstep (se 1 (by rfl) ⟨553523, by rfl⟩ : syracuseStep 738031 = 1107047) B1107047
theorem B1459133 : Blo 287828 1459133 := bstep (se 3 (by rfl) ⟨273587, by rfl⟩ : syracuseStep 1459133 = 547175) B547175
theorem B1393939 : Blo 287828 1393939 := bstep (se 1 (by rfl) ⟨1045454, by rfl⟩ : syracuseStep 1393939 = 2090909) B2090909
theorem B4179563 : Blo 287828 4179563 := bstep (se 1 (by rfl) ⟨3134672, by rfl⟩ : syracuseStep 4179563 = 6269345) B6269345
theorem B8309303 : Blo 287828 8309303 := bstep (se 1 (by rfl) ⟨6231977, by rfl⟩ : syracuseStep 8309303 = 12463955) B12463955
theorem B5917817 : Blo 287828 5917817 := bstep (se 2 (by rfl) ⟨2219181, by rfl⟩ : syracuseStep 5917817 = 4438363) B4438363
theorem B1658839 : Blo 287828 1658839 := bstep (se 1 (by rfl) ⟨1244129, by rfl⟩ : syracuseStep 1658839 = 2488259) B2488259
theorem B414175 : Blo 287828 414175 := bstep (se 1 (by rfl) ⟨310631, by rfl⟩ : syracuseStep 414175 = 621263) B621263
theorem B3953747 : Blo 287828 3953747 := bstep (se 1 (by rfl) ⟨2965310, by rfl⟩ : syracuseStep 3953747 = 5930621) B5930621
theorem B972431 : Blo 287828 972431 := bstep (se 1 (by rfl) ⟨729323, by rfl⟩ : syracuseStep 972431 = 1458647) B1458647
theorem B275929811 : Blo 287828 275929811 := bstep (se 1 (by rfl) ⟨206947358, by rfl⟩ : syracuseStep 275929811 = 413894717) B413894717
theorem B973565 : Blo 287828 973565 := bstep (se 3 (by rfl) ⟨182543, by rfl⟩ : syracuseStep 973565 = 365087) B365087
theorem B2310757303 : Blo 287828 2310757303 := bstep (se 1 (by rfl) ⟨1733067977, by rfl⟩ : syracuseStep 2310757303 = 3466135955) B3466135955
theorem B107306795 : Blo 287828 107306795 := bstep (se 1 (by rfl) ⟨80480096, by rfl⟩ : syracuseStep 107306795 = 160960193) B160960193
theorem B2645903 : Blo 287828 2645903 := bstep (se 1 (by rfl) ⟨1984427, by rfl⟩ : syracuseStep 2645903 = 3968855) B3968855
theorem B1237295 : Blo 287828 1237295 := bstep (se 1 (by rfl) ⟨927971, by rfl⟩ : syracuseStep 1237295 = 1855943) B1855943
theorem B88401089 : Blo 287828 88401089 := bstep (se 2 (by rfl) ⟨33150408, by rfl⟩ : syracuseStep 88401089 = 66300817) B66300817
theorem B288071 : Blo 287828 288071 := bstep (se 1 (by rfl) ⟨216053, by rfl⟩ : syracuseStep 288071 = 432107) B432107
theorem B288103 : Blo 287828 288103 := bstep (se 1 (by rfl) ⟨216077, by rfl⟩ : syracuseStep 288103 = 432155) B432155
theorem B57239743 : Blo 287828 57239743 := bstep (se 1 (by rfl) ⟨42929807, by rfl⟩ : syracuseStep 57239743 = 85859615) B85859615
theorem B4909679 : Blo 287828 4909679 := bstep (se 1 (by rfl) ⟨3682259, by rfl⟩ : syracuseStep 4909679 = 7364519) B7364519
theorem B7629427 : Blo 287828 7629427 := bstep (se 1 (by rfl) ⟨5722070, by rfl⟩ : syracuseStep 7629427 = 11444141) B11444141
theorem B4942619 : Blo 287828 4942619 := bstep (se 1 (by rfl) ⟨3706964, by rfl⟩ : syracuseStep 4942619 = 7413929) B7413929
theorem B650105 : Blo 287828 650105 := bstep (se 2 (by rfl) ⟨243789, by rfl⟩ : syracuseStep 650105 = 487579) B487579
theorem B486607 : Blo 287828 486607 := bstep (se 1 (by rfl) ⟨364955, by rfl⟩ : syracuseStep 486607 = 729911) B729911
theorem B4779467 : Blo 287828 4779467 := bstep (se 1 (by rfl) ⟨3584600, by rfl⟩ : syracuseStep 4779467 = 7169201) B7169201
theorem B486911 : Blo 287828 486911 := bstep (se 1 (by rfl) ⟨365183, by rfl⟩ : syracuseStep 486911 = 730367) B730367
theorem B290543 : Blo 287828 290543 := bstep (se 1 (by rfl) ⟨217907, by rfl⟩ : syracuseStep 290543 = 435815) B435815
theorem B1503143 : Blo 287828 1503143 := bstep (se 1 (by rfl) ⟨1127357, by rfl⟩ : syracuseStep 1503143 = 2254715) B2254715
theorem B290927 : Blo 287828 290927 := bstep (se 1 (by rfl) ⟨218195, by rfl⟩ : syracuseStep 290927 = 436391) B436391
theorem B291007 : Blo 287828 291007 := bstep (se 1 (by rfl) ⟨218255, by rfl⟩ : syracuseStep 291007 = 436511) B436511
theorem B291055 : Blo 287828 291055 := bstep (se 1 (by rfl) ⟨218291, by rfl⟩ : syracuseStep 291055 = 436583) B436583
theorem B1208603 : Blo 287828 1208603 := bstep (se 1 (by rfl) ⟨906452, by rfl⟩ : syracuseStep 1208603 = 1812905) B1812905
theorem B324391 : Blo 287828 324391 := bstep (se 1 (by rfl) ⟨243293, by rfl⟩ : syracuseStep 324391 = 486587) B486587
theorem B1471769 : Blo 287828 1471769 := bstep (se 2 (by rfl) ⟨551913, by rfl⟩ : syracuseStep 1471769 = 1103827) B1103827
theorem B325147 : Blo 287828 325147 := bstep (se 1 (by rfl) ⟨243860, by rfl⟩ : syracuseStep 325147 = 487721) B487721
theorem B980639 : Blo 287828 980639 := bstep (se 1 (by rfl) ⟨735479, by rfl⟩ : syracuseStep 980639 = 1470959) B1470959
theorem B489449 : Blo 287828 489449 := bstep (se 2 (by rfl) ⟨183543, by rfl⟩ : syracuseStep 489449 = 367087) B367087
theorem B325723 : Blo 287828 325723 := bstep (se 1 (by rfl) ⟨244292, by rfl⟩ : syracuseStep 325723 = 488585) B488585
theorem B1046839 : Blo 287828 1046839 := bstep (se 1 (by rfl) ⟨785129, by rfl⟩ : syracuseStep 1046839 = 1570259) B1570259
theorem B653705 : Blo 287828 653705 := bstep (se 2 (by rfl) ⟨245139, by rfl⟩ : syracuseStep 653705 = 490279) B490279
theorem B1243583 : Blo 287828 1243583 := bstep (se 1 (by rfl) ⟨932687, by rfl⟩ : syracuseStep 1243583 = 1865375) B1865375
theorem B6716209 : Blo 287828 6716209 := bstep (se 2 (by rfl) ⟨2518578, by rfl⟩ : syracuseStep 6716209 = 5037157) B5037157
theorem B2227409 : Blo 287828 2227409 := bstep (se 2 (by rfl) ⟨835278, by rfl⟩ : syracuseStep 2227409 = 1670557) B1670557
theorem B326911 : Blo 287828 326911 := bstep (se 1 (by rfl) ⟨245183, by rfl⟩ : syracuseStep 326911 = 490367) B490367
theorem B491575 : Blo 287828 491575 := bstep (se 1 (by rfl) ⟨368681, by rfl⟩ : syracuseStep 491575 = 737363) B737363
theorem B655451 : Blo 287828 655451 := bstep (se 1 (by rfl) ⟨491588, by rfl⟩ : syracuseStep 655451 = 983177) B983177
theorem B327775 : Blo 287828 327775 := bstep (se 1 (by rfl) ⟨245831, by rfl⟩ : syracuseStep 327775 = 491663) B491663
theorem B984041 : Blo 287828 984041 := bstep (se 2 (by rfl) ⟨369015, by rfl⟩ : syracuseStep 984041 = 738031) B738031
theorem B2786375 : Blo 287828 2786375 := bstep (se 1 (by rfl) ⟨2089781, by rfl⟩ : syracuseStep 2786375 = 4179563) B4179563
theorem B984203 : Blo 287828 984203 := bstep (se 1 (by rfl) ⟨738152, by rfl⟩ : syracuseStep 984203 = 1476305) B1476305
theorem B2491883 : Blo 287828 2491883 := bstep (se 1 (by rfl) ⟨1868912, by rfl⟩ : syracuseStep 2491883 = 3737825) B3737825
theorem B5539535 : Blo 287828 5539535 := bstep (se 1 (by rfl) ⟨4154651, by rfl⟩ : syracuseStep 5539535 = 8309303) B8309303
theorem B76319657 : Blo 287828 76319657 := bstep (se 2 (by rfl) ⟨28619871, by rfl⟩ : syracuseStep 76319657 = 57239743) B57239743
theorem B235736237 : Blo 287828 235736237 := bstep (se 3 (by rfl) ⟨44200544, by rfl⟩ : syracuseStep 235736237 = 88401089) B88401089
theorem B36049211 : Blo 287828 36049211 := bstep (se 1 (by rfl) ⟨27036908, by rfl⟩ : syracuseStep 36049211 = 54073817) B54073817
theorem B71537863 : Blo 287828 71537863 := bstep (se 1 (by rfl) ⟨53653397, by rfl⟩ : syracuseStep 71537863 = 107306795) B107306795
theorem B21370817 : Blo 287828 21370817 := bstep (se 2 (by rfl) ⟨8014056, by rfl⟩ : syracuseStep 21370817 = 16028113) B16028113
theorem B2463929 : Blo 287828 2463929 := bstep (se 2 (by rfl) ⟨923973, by rfl⟩ : syracuseStep 2463929 = 1847947) B1847947
theorem B16849093 : Blo 287828 16849093 := bstep (se 4 (by rfl) ⟨1579602, by rfl⟩ : syracuseStep 16849093 = 3159205) B3159205
theorem B432521 : Blo 287828 432521 := bstep (se 2 (by rfl) ⟨162195, by rfl⟩ : syracuseStep 432521 = 324391) B324391
theorem B433403 : Blo 287828 433403 := bstep (se 1 (by rfl) ⟨325052, by rfl⟩ : syracuseStep 433403 = 650105) B650105
theorem B433529 : Blo 287828 433529 := bstep (se 2 (by rfl) ⟨162573, by rfl⟩ : syracuseStep 433529 = 325147) B325147
theorem B3186311 : Blo 287828 3186311 := bstep (se 1 (by rfl) ⟨2389733, by rfl⟩ : syracuseStep 3186311 = 4779467) B4779467
theorem B434297 : Blo 287828 434297 := bstep (se 2 (by rfl) ⟨162861, by rfl⟩ : syracuseStep 434297 = 325723) B325723
theorem B8954945 : Blo 287828 8954945 := bstep (se 2 (by rfl) ⟨3358104, by rfl⟩ : syracuseStep 8954945 = 6716209) B6716209
theorem B435803 : Blo 287828 435803 := bstep (se 1 (by rfl) ⟨326852, by rfl⟩ : syracuseStep 435803 = 653705) B653705
theorem B829055 : Blo 287828 829055 := bstep (se 1 (by rfl) ⟨621791, by rfl⟩ : syracuseStep 829055 = 1243583) B1243583
theorem B435881 : Blo 287828 435881 := bstep (se 2 (by rfl) ⟨163455, by rfl⟩ : syracuseStep 435881 = 326911) B326911
theorem B731207 : Blo 287828 731207 := bstep (se 1 (by rfl) ⟨548405, by rfl⟩ : syracuseStep 731207 = 1096811) B1096811
theorem B1484939 : Blo 287828 1484939 := bstep (se 1 (by rfl) ⟨1113704, by rfl⟩ : syracuseStep 1484939 = 2227409) B2227409
theorem B7055741 : Blo 287828 7055741 := bstep (se 3 (by rfl) ⟨1322951, by rfl⟩ : syracuseStep 7055741 = 2645903) B2645903
theorem B436991 : Blo 287828 436991 := bstep (se 1 (by rfl) ⟨327743, by rfl⟩ : syracuseStep 436991 = 655487) B655487
theorem B437129 : Blo 287828 437129 := bstep (se 2 (by rfl) ⟨163923, by rfl⟩ : syracuseStep 437129 = 327847) B327847
theorem B437243 : Blo 287828 437243 := bstep (se 1 (by rfl) ⟨327932, by rfl⟩ : syracuseStep 437243 = 655865) B655865
theorem B437279 : Blo 287828 437279 := bstep (se 1 (by rfl) ⟨327959, by rfl⟩ : syracuseStep 437279 = 655919) B655919
theorem B3322781 : Blo 287828 3322781 := bstep (se 3 (by rfl) ⟨623021, by rfl⟩ : syracuseStep 3322781 = 1246043) B1246043
theorem B308863 : Blo 287828 308863 := bstep (se 1 (by rfl) ⟨231647, by rfl⟩ : syracuseStep 308863 = 463295) B463295
theorem B2635831 : Blo 287828 2635831 := bstep (se 1 (by rfl) ⟨1976873, by rfl⟩ : syracuseStep 2635831 = 3953747) B3953747
theorem B10172569 : Blo 287828 10172569 := bstep (se 2 (by rfl) ⟨3814713, by rfl⟩ : syracuseStep 10172569 = 7629427) B7629427
theorem B2506697 : Blo 287828 2506697 := bstep (se 2 (by rfl) ⟨940011, by rfl⟩ : syracuseStep 2506697 = 1880023) B1880023
theorem B2211785 : Blo 287828 2211785 := bstep (se 2 (by rfl) ⟨829419, by rfl⟩ : syracuseStep 2211785 = 1658839) B1658839
theorem B1230461 : Blo 287828 1230461 := bstep (se 3 (by rfl) ⟨230711, by rfl⟩ : syracuseStep 1230461 = 461423) B461423
theorem B3295079 : Blo 287828 3295079 := bstep (se 1 (by rfl) ⟨2471309, by rfl⟩ : syracuseStep 3295079 = 4942619) B4942619
theorem B1231213 : Blo 287828 1231213 := bstep (se 3 (by rfl) ⟨230852, by rfl⟩ : syracuseStep 1231213 = 461705) B461705
theorem B1002095 : Blo 287828 1002095 := bstep (se 1 (by rfl) ⟨751571, by rfl⟩ : syracuseStep 1002095 = 1503143) B1503143
theorem B805735 : Blo 287828 805735 := bstep (se 1 (by rfl) ⟨604301, by rfl⟩ : syracuseStep 805735 = 1208603) B1208603
theorem B15780845 : Blo 287828 15780845 := bstep (se 3 (by rfl) ⟨2958908, by rfl⟩ : syracuseStep 15780845 = 5917817) B5917817
theorem B1395785 : Blo 287828 1395785 := bstep (se 2 (by rfl) ⟨523419, by rfl⟩ : syracuseStep 1395785 = 1046839) B1046839
theorem B305976851 : Blo 287828 305976851 := bstep (se 1 (by rfl) ⟨229482638, by rfl⟩ : syracuseStep 305976851 = 458965277) B458965277
theorem B972755 : Blo 287828 972755 := bstep (se 1 (by rfl) ⟨729566, by rfl⟩ : syracuseStep 972755 = 1459133) B1459133
theorem B350239 : Blo 287828 350239 := bstep (se 1 (by rfl) ⟨262679, by rfl⟩ : syracuseStep 350239 = 525359) B525359
theorem B3299453 : Blo 287828 3299453 := bstep (se 3 (by rfl) ⟨618647, by rfl⟩ : syracuseStep 3299453 = 1237295) B1237295
theorem B4938245 : Blo 287828 4938245 := bstep (se 4 (by rfl) ⟨462960, by rfl⟩ : syracuseStep 4938245 = 925921) B925921
theorem B1399801 : Blo 287828 1399801 := bstep (se 2 (by rfl) ⟨524925, by rfl⟩ : syracuseStep 1399801 = 1049851) B1049851
theorem B1858585 : Blo 287828 1858585 := bstep (se 2 (by rfl) ⟨696969, by rfl⟩ : syracuseStep 1858585 = 1393939) B1393939
theorem B2317871 : Blo 287828 2317871 := bstep (se 1 (by rfl) ⟨1738403, by rfl⟩ : syracuseStep 2317871 = 3476807) B3476807
theorem B648287 : Blo 287828 648287 := bstep (se 1 (by rfl) ⟨486215, by rfl⟩ : syracuseStep 648287 = 972431) B972431
theorem B287999 : Blo 287828 287999 := bstep (se 1 (by rfl) ⟨215999, by rfl⟩ : syracuseStep 287999 = 431999) B431999
theorem B288027 : Blo 287828 288027 := bstep (se 1 (by rfl) ⟨216020, by rfl⟩ : syracuseStep 288027 = 432041) B432041
theorem B648809 : Blo 287828 648809 := bstep (se 2 (by rfl) ⟨243303, by rfl⟩ : syracuseStep 648809 = 486607) B486607
theorem B183953207 : Blo 287828 183953207 := bstep (se 1 (by rfl) ⟨137964905, by rfl⟩ : syracuseStep 183953207 = 275929811) B275929811
theorem B649043 : Blo 287828 649043 := bstep (se 1 (by rfl) ⟨486782, by rfl⟩ : syracuseStep 649043 = 973565) B973565
theorem B288623 : Blo 287828 288623 := bstep (se 1 (by rfl) ⟨216467, by rfl⟩ : syracuseStep 288623 = 432935) B432935
theorem B288895 : Blo 287828 288895 := bstep (se 1 (by rfl) ⟨216671, by rfl⟩ : syracuseStep 288895 = 433343) B433343
theorem B289007 : Blo 287828 289007 := bstep (se 1 (by rfl) ⟨216755, by rfl⟩ : syracuseStep 289007 = 433511) B433511
theorem B2189915 : Blo 287828 2189915 := bstep (se 1 (by rfl) ⟨1642436, by rfl⟩ : syracuseStep 2189915 = 3284873) B3284873
theorem B289407 : Blo 287828 289407 := bstep (se 1 (by rfl) ⟨217055, by rfl⟩ : syracuseStep 289407 = 434111) B434111
theorem B289511 : Blo 287828 289511 := bstep (se 1 (by rfl) ⟨217133, by rfl⟩ : syracuseStep 289511 = 434267) B434267
theorem B289563 : Blo 287828 289563 := bstep (se 1 (by rfl) ⟨217172, by rfl⟩ : syracuseStep 289563 = 434345) B434345
theorem B289951 : Blo 287828 289951 := bstep (se 1 (by rfl) ⟨217463, by rfl⟩ : syracuseStep 289951 = 434927) B434927
theorem B552233 : Blo 287828 552233 := bstep (se 2 (by rfl) ⟨207087, by rfl⟩ : syracuseStep 552233 = 414175) B414175
theorem B290415 : Blo 287828 290415 := bstep (se 1 (by rfl) ⟨217811, by rfl⟩ : syracuseStep 290415 = 435623) B435623
theorem B290511 : Blo 287828 290511 := bstep (se 1 (by rfl) ⟨217883, by rfl⟩ : syracuseStep 290511 = 435767) B435767
theorem B487451 : Blo 287828 487451 := bstep (se 1 (by rfl) ⟨365588, by rfl⟩ : syracuseStep 487451 = 731177) B731177
theorem B3273119 : Blo 287828 3273119 := bstep (se 1 (by rfl) ⟨2454839, by rfl⟩ : syracuseStep 3273119 = 4909679) B4909679
theorem B291483 : Blo 287828 291483 := bstep (se 1 (by rfl) ⟨218612, by rfl⟩ : syracuseStep 291483 = 437225) B437225
theorem B553691 : Blo 287828 553691 := bstep (se 1 (by rfl) ⟨415268, by rfl⟩ : syracuseStep 553691 = 830537) B830537
theorem B40399667 : Blo 287828 40399667 := bstep (se 1 (by rfl) ⟨30299750, by rfl⟩ : syracuseStep 40399667 = 60599501) B60599501
theorem B324607 : Blo 287828 324607 := bstep (se 1 (by rfl) ⟨243455, by rfl⟩ : syracuseStep 324607 = 486911) B486911
theorem B981179 : Blo 287828 981179 := bstep (se 1 (by rfl) ⟨735884, by rfl⟩ : syracuseStep 981179 = 1471769) B1471769
theorem B653759 : Blo 287828 653759 := bstep (se 1 (by rfl) ⟨490319, by rfl⟩ : syracuseStep 653759 = 980639) B980639
theorem B3081009737 : Blo 287828 3081009737 := bstep (se 2 (by rfl) ⟨1155378651, by rfl⟩ : syracuseStep 3081009737 = 2310757303) B2310757303
theorem B326299 : Blo 287828 326299 := bstep (se 1 (by rfl) ⟨244724, by rfl⟩ : syracuseStep 326299 = 489449) B489449
theorem B981665 : Blo 287828 981665 := bstep (se 2 (by rfl) ⟨368124, by rfl⟩ : syracuseStep 981665 = 736249) B736249
theorem B17169965 : Blo 287828 17169965 := bstep (se 3 (by rfl) ⟨3219368, by rfl⟩ : syracuseStep 17169965 = 6438737) B6438737
theorem B655433 : Blo 287828 655433 := bstep (se 2 (by rfl) ⟨245787, by rfl⟩ : syracuseStep 655433 = 491575) B491575
theorem B656027 : Blo 287828 656027 := bstep (se 1 (by rfl) ⟨492020, by rfl⟩ : syracuseStep 656027 = 984041) B984041
theorem B656135 : Blo 287828 656135 := bstep (se 1 (by rfl) ⟨492101, by rfl⟩ : syracuseStep 656135 = 984203) B984203
theorem B820307 : Blo 287828 820307 := bstep (se 1 (by rfl) ⟨615230, by rfl⟩ : syracuseStep 820307 = 1230461) B1230461
theorem B2196719 : Blo 287828 2196719 := bstep (se 1 (by rfl) ⟨1647539, by rfl⟩ : syracuseStep 2196719 = 3295079) B3295079
theorem B10520563 : Blo 287828 10520563 := bstep (se 1 (by rfl) ⟨7890422, by rfl⟩ : syracuseStep 10520563 = 15780845) B15780845
theorem B157157491 : Blo 287828 157157491 := bstep (se 1 (by rfl) ⟨117868118, by rfl⟩ : syracuseStep 157157491 = 235736237) B235736237
theorem B1641617 : Blo 287828 1641617 := bstep (se 2 (by rfl) ⟨615606, by rfl⟩ : syracuseStep 1641617 = 1231213) B1231213
theorem B203984567 : Blo 287828 203984567 := bstep (se 1 (by rfl) ⟨152988425, by rfl⟩ : syracuseStep 203984567 = 305976851) B305976851
theorem B2199635 : Blo 287828 2199635 := bstep (se 1 (by rfl) ⟨1649726, by rfl⟩ : syracuseStep 2199635 = 3299453) B3299453
theorem B1642619 : Blo 287828 1642619 := bstep (se 1 (by rfl) ⟨1231964, by rfl⟩ : syracuseStep 1642619 = 2463929) B2463929
theorem B1545247 : Blo 287828 1545247 := bstep (se 1 (by rfl) ⟨1158935, by rfl⟩ : syracuseStep 1545247 = 2317871) B2317871
theorem B56988845 : Blo 287828 56988845 := bstep (se 3 (by rfl) ⟨10685408, by rfl⟩ : syracuseStep 56988845 = 21370817) B21370817
theorem B5969963 : Blo 287828 5969963 := bstep (se 1 (by rfl) ⟨4477472, by rfl⟩ : syracuseStep 5969963 = 8954945) B8954945
theorem B432191 : Blo 287828 432191 := bstep (se 1 (by rfl) ⟨324143, by rfl⟩ : syracuseStep 432191 = 648287) B648287
theorem B432539 : Blo 287828 432539 := bstep (se 1 (by rfl) ⟨324404, by rfl⟩ : syracuseStep 432539 = 648809) B648809
theorem B432695 : Blo 287828 432695 := bstep (se 1 (by rfl) ⟨324521, by rfl⟩ : syracuseStep 432695 = 649043) B649043
theorem B432809 : Blo 287828 432809 := bstep (se 2 (by rfl) ⟨162303, by rfl⟩ : syracuseStep 432809 = 324607) B324607
theorem B8216025965 : Blo 287828 8216025965 := bstep (se 3 (by rfl) ⟨1540504868, by rfl⟩ : syracuseStep 8216025965 = 3081009737) B3081009737
theorem B368155 : Blo 287828 368155 := bstep (se 1 (by rfl) ⟨276116, by rfl⟩ : syracuseStep 368155 = 552233) B552233
theorem B466985 : Blo 287828 466985 := bstep (se 2 (by rfl) ⟨175119, by rfl⟩ : syracuseStep 466985 = 350239) B350239
theorem B3514441 : Blo 287828 3514441 := bstep (se 2 (by rfl) ⟨1317915, by rfl⟩ : syracuseStep 3514441 = 2635831) B2635831
theorem B369127 : Blo 287828 369127 := bstep (se 1 (by rfl) ⟨276845, by rfl⟩ : syracuseStep 369127 = 553691) B553691
theorem B435065 : Blo 287828 435065 := bstep (se 2 (by rfl) ⟨163149, by rfl⟩ : syracuseStep 435065 = 326299) B326299
theorem B435839 : Blo 287828 435839 := bstep (se 1 (by rfl) ⟨326879, by rfl⟩ : syracuseStep 435839 = 653759) B653759
theorem B8496829 : Blo 287828 8496829 := bstep (se 3 (by rfl) ⟨1593155, by rfl⟩ : syracuseStep 8496829 = 3186311) B3186311
theorem B11446643 : Blo 287828 11446643 := bstep (se 1 (by rfl) ⟨8584982, by rfl⟩ : syracuseStep 11446643 = 17169965) B17169965
theorem B436967 : Blo 287828 436967 := bstep (se 1 (by rfl) ⟨327725, by rfl⟩ : syracuseStep 436967 = 655451) B655451
theorem B437033 : Blo 287828 437033 := bstep (se 2 (by rfl) ⟨163887, by rfl⟩ : syracuseStep 437033 = 327775) B327775
theorem B668063 : Blo 287828 668063 := bstep (se 1 (by rfl) ⟨501047, by rfl⟩ : syracuseStep 668063 = 1002095) B1002095
theorem B930523 : Blo 287828 930523 := bstep (se 1 (by rfl) ⟨697892, by rfl⟩ : syracuseStep 930523 = 1395785) B1395785
theorem B24032807 : Blo 287828 24032807 := bstep (se 1 (by rfl) ⟨18024605, by rfl⟩ : syracuseStep 24032807 = 36049211) B36049211
theorem B2210813 : Blo 287828 2210813 := bstep (se 3 (by rfl) ⟨414527, by rfl⟩ : syracuseStep 2210813 = 829055) B829055
theorem B3292163 : Blo 287828 3292163 := bstep (se 1 (by rfl) ⟨2469122, by rfl⟩ : syracuseStep 3292163 = 4938245) B4938245
theorem B122635471 : Blo 287828 122635471 := bstep (se 1 (by rfl) ⟨91976603, by rfl⟩ : syracuseStep 122635471 = 183953207) B183953207
theorem B4703827 : Blo 287828 4703827 := bstep (se 1 (by rfl) ⟨3527870, by rfl⟩ : syracuseStep 4703827 = 7055741) B7055741
theorem B1459943 : Blo 287828 1459943 := bstep (se 1 (by rfl) ⟨1094957, by rfl⟩ : syracuseStep 1459943 = 2189915) B2189915
theorem B411817 : Blo 287828 411817 := bstep (se 2 (by rfl) ⟨154431, by rfl⟩ : syracuseStep 411817 = 308863) B308863
theorem B22465457 : Blo 287828 22465457 := bstep (se 2 (by rfl) ⟨8424546, by rfl⟩ : syracuseStep 22465457 = 16849093) B16849093
theorem B2182079 : Blo 287828 2182079 := bstep (se 1 (by rfl) ⟨1636559, by rfl⟩ : syracuseStep 2182079 = 3273119) B3273119
theorem B2215187 : Blo 287828 2215187 := bstep (se 1 (by rfl) ⟨1661390, by rfl⟩ : syracuseStep 2215187 = 3322781) B3322781
theorem B2478113 : Blo 287828 2478113 := bstep (se 2 (by rfl) ⟨929292, by rfl⟩ : syracuseStep 2478113 = 1858585) B1858585
theorem B1857583 : Blo 287828 1857583 := bstep (se 1 (by rfl) ⟨1393187, by rfl⟩ : syracuseStep 1857583 = 2786375) B2786375
theorem B1661255 : Blo 287828 1661255 := bstep (se 1 (by rfl) ⟨1245941, by rfl⟩ : syracuseStep 1661255 = 2491883) B2491883
theorem B3693023 : Blo 287828 3693023 := bstep (se 1 (by rfl) ⟨2769767, by rfl⟩ : syracuseStep 3693023 = 5539535) B5539535
theorem B50879771 : Blo 287828 50879771 := bstep (se 1 (by rfl) ⟨38159828, by rfl⟩ : syracuseStep 50879771 = 76319657) B76319657
theorem B1074313 : Blo 287828 1074313 := bstep (se 2 (by rfl) ⟨402867, by rfl⟩ : syracuseStep 1074313 = 805735) B805735
theorem B648503 : Blo 287828 648503 := bstep (se 1 (by rfl) ⟨486377, by rfl⟩ : syracuseStep 648503 = 972755) B972755
theorem B288347 : Blo 287828 288347 := bstep (se 1 (by rfl) ⟨216260, by rfl⟩ : syracuseStep 288347 = 432521) B432521
theorem B288935 : Blo 287828 288935 := bstep (se 1 (by rfl) ⟨216701, by rfl⟩ : syracuseStep 288935 = 433403) B433403
theorem B289019 : Blo 287828 289019 := bstep (se 1 (by rfl) ⟨216764, by rfl⟩ : syracuseStep 289019 = 433529) B433529
theorem B289531 : Blo 287828 289531 := bstep (se 1 (by rfl) ⟨217148, by rfl⟩ : syracuseStep 289531 = 434297) B434297
theorem B3959837 : Blo 287828 3959837 := bstep (se 3 (by rfl) ⟨742469, by rfl⟩ : syracuseStep 3959837 = 1484939) B1484939
theorem B290535 : Blo 287828 290535 := bstep (se 1 (by rfl) ⟨217901, by rfl⟩ : syracuseStep 290535 = 435803) B435803
theorem B290587 : Blo 287828 290587 := bstep (se 1 (by rfl) ⟨217940, by rfl⟩ : syracuseStep 290587 = 435881) B435881
theorem B487471 : Blo 287828 487471 := bstep (se 1 (by rfl) ⟨365603, by rfl⟩ : syracuseStep 487471 = 731207) B731207
theorem B95383817 : Blo 287828 95383817 := bstep (se 2 (by rfl) ⟨35768931, by rfl⟩ : syracuseStep 95383817 = 71537863) B71537863
theorem B291327 : Blo 287828 291327 := bstep (se 1 (by rfl) ⟨218495, by rfl⟩ : syracuseStep 291327 = 436991) B436991
theorem B291419 : Blo 287828 291419 := bstep (se 1 (by rfl) ⟨218564, by rfl⟩ : syracuseStep 291419 = 437129) B437129
theorem B291495 : Blo 287828 291495 := bstep (se 1 (by rfl) ⟨218621, by rfl⟩ : syracuseStep 291495 = 437243) B437243
theorem B291519 : Blo 287828 291519 := bstep (se 1 (by rfl) ⟨218639, by rfl⟩ : syracuseStep 291519 = 437279) B437279
theorem B324967 : Blo 287828 324967 := bstep (se 1 (by rfl) ⟨243725, by rfl⟩ : syracuseStep 324967 = 487451) B487451
theorem B13563425 : Blo 287828 13563425 := bstep (se 2 (by rfl) ⟨5086284, by rfl⟩ : syracuseStep 13563425 = 10172569) B10172569
theorem B26933111 : Blo 287828 26933111 := bstep (se 1 (by rfl) ⟨20199833, by rfl⟩ : syracuseStep 26933111 = 40399667) B40399667
theorem B1866401 : Blo 287828 1866401 := bstep (se 2 (by rfl) ⟨699900, by rfl⟩ : syracuseStep 1866401 = 1399801) B1399801
theorem B654119 : Blo 287828 654119 := bstep (se 1 (by rfl) ⟨490589, by rfl⟩ : syracuseStep 654119 = 981179) B981179
theorem B654443 : Blo 287828 654443 := bstep (se 1 (by rfl) ⟨490832, by rfl⟩ : syracuseStep 654443 = 981665) B981665
theorem B1671131 : Blo 287828 1671131 := bstep (se 1 (by rfl) ⟨1253348, by rfl⟩ : syracuseStep 1671131 = 2506697) B2506697
theorem B1474523 : Blo 287828 1474523 := bstep (se 1 (by rfl) ⟨1105892, by rfl⟩ : syracuseStep 1474523 = 2211785) B2211785
theorem B4685921 : Blo 287828 4685921 := bstep (se 2 (by rfl) ⟨1757220, by rfl⟩ : syracuseStep 4685921 = 3514441) B3514441
theorem B1245293 : Blo 287828 1245293 := bstep (se 3 (by rfl) ⟨233492, by rfl⟩ : syracuseStep 1245293 = 466985) B466985
theorem B492169 : Blo 287828 492169 := bstep (se 2 (by rfl) ⟨184563, by rfl⟩ : syracuseStep 492169 = 369127) B369127
theorem B163513961 : Blo 287828 163513961 := bstep (se 2 (by rfl) ⟨61317735, by rfl⟩ : syracuseStep 163513961 = 122635471) B122635471
theorem B14976971 : Blo 287828 14976971 := bstep (se 1 (by rfl) ⟨11232728, by rfl⟩ : syracuseStep 14976971 = 22465457) B22465457
theorem B1476791 : Blo 287828 1476791 := bstep (se 1 (by rfl) ⟨1107593, by rfl⟩ : syracuseStep 1476791 = 2215187) B2215187
theorem B135989711 : Blo 287828 135989711 := bstep (se 1 (by rfl) ⟨101992283, by rfl⟩ : syracuseStep 135989711 = 203984567) B203984567
theorem B14027417 : Blo 287828 14027417 := bstep (se 2 (by rfl) ⟨5260281, by rfl⟩ : syracuseStep 14027417 = 10520563) B10520563
theorem B2462015 : Blo 287828 2462015 := bstep (se 1 (by rfl) ⟨1846511, by rfl⟩ : syracuseStep 2462015 = 3693023) B3693023
theorem B33919847 : Blo 287828 33919847 := bstep (se 1 (by rfl) ⟨25439885, by rfl⟩ : syracuseStep 33919847 = 50879771) B50879771
theorem B432335 : Blo 287828 432335 := bstep (se 1 (by rfl) ⟨324251, by rfl⟩ : syracuseStep 432335 = 648503) B648503
theorem B433289 : Blo 287828 433289 := bstep (se 2 (by rfl) ⟨162483, by rfl⟩ : syracuseStep 433289 = 324967) B324967
theorem B436079 : Blo 287828 436079 := bstep (se 1 (by rfl) ⟨327059, by rfl⟩ : syracuseStep 436079 = 654119) B654119
theorem B436295 : Blo 287828 436295 := bstep (se 1 (by rfl) ⟨327221, by rfl⟩ : syracuseStep 436295 = 654443) B654443
theorem B436955 : Blo 287828 436955 := bstep (se 1 (by rfl) ⟨327716, by rfl⟩ : syracuseStep 436955 = 655433) B655433
theorem B437351 : Blo 287828 437351 := bstep (se 1 (by rfl) ⟨328013, by rfl⟩ : syracuseStep 437351 = 656027) B656027
theorem B437423 : Blo 287828 437423 := bstep (se 1 (by rfl) ⟨328067, by rfl⟩ : syracuseStep 437423 = 656135) B656135
theorem B1094411 : Blo 287828 1094411 := bstep (se 1 (by rfl) ⟨820808, by rfl⟩ : syracuseStep 1094411 = 1641617) B1641617
theorem B6271769 : Blo 287828 6271769 := bstep (se 2 (by rfl) ⟨2351913, by rfl⟩ : syracuseStep 6271769 = 4703827) B4703827
theorem B1652075 : Blo 287828 1652075 := bstep (se 1 (by rfl) ⟨1239056, by rfl⟩ : syracuseStep 1652075 = 2478113) B2478113
theorem B1095079 : Blo 287828 1095079 := bstep (se 1 (by rfl) ⟨821309, by rfl⟩ : syracuseStep 1095079 = 1642619) B1642619
theorem B37992563 : Blo 287828 37992563 := bstep (se 1 (by rfl) ⟨28494422, by rfl⟩ : syracuseStep 37992563 = 56988845) B56988845
theorem B3979975 : Blo 287828 3979975 := bstep (se 1 (by rfl) ⟨2984981, by rfl⟩ : syracuseStep 3979975 = 5969963) B5969963
theorem B5477350643 : Blo 287828 5477350643 := bstep (se 1 (by rfl) ⟨4108012982, by rfl⟩ : syracuseStep 5477350643 = 8216025965) B8216025965
theorem B30524381 : Blo 287828 30524381 := bstep (se 3 (by rfl) ⟨5723321, by rfl⟩ : syracuseStep 30524381 = 11446643) B11446643
theorem B2639891 : Blo 287828 2639891 := bstep (se 1 (by rfl) ⟨1979918, by rfl⟩ : syracuseStep 2639891 = 3959837) B3959837
theorem B5818877 : Blo 287828 5818877 := bstep (se 3 (by rfl) ⟨1091039, by rfl⟩ : syracuseStep 5818877 = 2182079) B2182079
theorem B2476777 : Blo 287828 2476777 := bstep (se 2 (by rfl) ⟨928791, by rfl⟩ : syracuseStep 2476777 = 1857583) B1857583
theorem B63589211 : Blo 287828 63589211 := bstep (se 1 (by rfl) ⟨47691908, by rfl⟩ : syracuseStep 63589211 = 95383817) B95383817
theorem B445375 : Blo 287828 445375 := bstep (se 1 (by rfl) ⟨334031, by rfl⟩ : syracuseStep 445375 = 668063) B668063
theorem B1464479 : Blo 287828 1464479 := bstep (se 1 (by rfl) ⟨1098359, by rfl⟩ : syracuseStep 1464479 = 2196719) B2196719
theorem B973295 : Blo 287828 973295 := bstep (se 1 (by rfl) ⟨729971, by rfl⟩ : syracuseStep 973295 = 1459943) B1459943
theorem B1432417 : Blo 287828 1432417 := bstep (se 2 (by rfl) ⟨537156, by rfl⟩ : syracuseStep 1432417 = 1074313) B1074313
theorem B11329105 : Blo 287828 11329105 := bstep (se 2 (by rfl) ⟨4248414, by rfl⟩ : syracuseStep 11329105 = 8496829) B8496829
theorem B1466423 : Blo 287828 1466423 := bstep (se 1 (by rfl) ⟨1099817, by rfl⟩ : syracuseStep 1466423 = 2199635) B2199635
theorem B209543321 : Blo 287828 209543321 := bstep (se 2 (by rfl) ⟨78578745, by rfl⟩ : syracuseStep 209543321 = 157157491) B157157491
theorem B2187485 : Blo 287828 2187485 := bstep (se 3 (by rfl) ⟨410153, by rfl⟩ : syracuseStep 2187485 = 820307) B820307
theorem B549089 : Blo 287828 549089 := bstep (se 2 (by rfl) ⟨205908, by rfl⟩ : syracuseStep 549089 = 411817) B411817
theorem B288127 : Blo 287828 288127 := bstep (se 1 (by rfl) ⟨216095, by rfl⟩ : syracuseStep 288127 = 432191) B432191
theorem B1107503 : Blo 287828 1107503 := bstep (se 1 (by rfl) ⟨830627, by rfl⟩ : syracuseStep 1107503 = 1661255) B1661255
theorem B288359 : Blo 287828 288359 := bstep (se 1 (by rfl) ⟨216269, by rfl⟩ : syracuseStep 288359 = 432539) B432539
theorem B288463 : Blo 287828 288463 := bstep (se 1 (by rfl) ⟨216347, by rfl⟩ : syracuseStep 288463 = 432695) B432695
theorem B288539 : Blo 287828 288539 := bstep (se 1 (by rfl) ⟨216404, by rfl⟩ : syracuseStep 288539 = 432809) B432809
theorem B649961 : Blo 287828 649961 := bstep (se 2 (by rfl) ⟨243735, by rfl⟩ : syracuseStep 649961 = 487471) B487471
theorem B290043 : Blo 287828 290043 := bstep (se 1 (by rfl) ⟨217532, by rfl⟩ : syracuseStep 290043 = 435065) B435065
theorem B1240697 : Blo 287828 1240697 := bstep (se 2 (by rfl) ⟨465261, by rfl⟩ : syracuseStep 1240697 = 930523) B930523
theorem B290559 : Blo 287828 290559 := bstep (se 1 (by rfl) ⟨217919, by rfl⟩ : syracuseStep 290559 = 435839) B435839
theorem B2060329 : Blo 287828 2060329 := bstep (se 2 (by rfl) ⟨772623, by rfl⟩ : syracuseStep 2060329 = 1545247) B1545247
theorem B291311 : Blo 287828 291311 := bstep (se 1 (by rfl) ⟨218483, by rfl⟩ : syracuseStep 291311 = 436967) B436967
theorem B291355 : Blo 287828 291355 := bstep (se 1 (by rfl) ⟨218516, by rfl⟩ : syracuseStep 291355 = 437033) B437033
theorem B9042283 : Blo 287828 9042283 := bstep (se 1 (by rfl) ⟨6781712, by rfl⟩ : syracuseStep 9042283 = 13563425) B13563425
theorem B16021871 : Blo 287828 16021871 := bstep (se 1 (by rfl) ⟨12016403, by rfl⟩ : syracuseStep 16021871 = 24032807) B24032807
theorem B17955407 : Blo 287828 17955407 := bstep (se 1 (by rfl) ⟨13466555, by rfl⟩ : syracuseStep 17955407 = 26933111) B26933111
theorem B1244267 : Blo 287828 1244267 := bstep (se 1 (by rfl) ⟨933200, by rfl⟩ : syracuseStep 1244267 = 1866401) B1866401
theorem B1473875 : Blo 287828 1473875 := bstep (se 1 (by rfl) ⟨1105406, by rfl⟩ : syracuseStep 1473875 = 2210813) B2210813
theorem B2194775 : Blo 287828 2194775 := bstep (se 1 (by rfl) ⟨1646081, by rfl⟩ : syracuseStep 2194775 = 3292163) B3292163
theorem B490873 : Blo 287828 490873 := bstep (se 2 (by rfl) ⟨184077, by rfl⟩ : syracuseStep 490873 = 368155) B368155
theorem B1114087 : Blo 287828 1114087 := bstep (se 1 (by rfl) ⟨835565, by rfl⟩ : syracuseStep 1114087 = 1671131) B1671131
theorem B983015 : Blo 287828 983015 := bstep (se 1 (by rfl) ⟨737261, by rfl⟩ : syracuseStep 983015 = 1474523) B1474523
theorem B20349587 : Blo 287828 20349587 := bstep (se 1 (by rfl) ⟨15262190, by rfl⟩ : syracuseStep 20349587 = 30524381) B30524381
theorem B656225 : Blo 287828 656225 := bstep (se 2 (by rfl) ⟨246084, by rfl⟩ : syracuseStep 656225 = 492169) B492169
theorem B984527 : Blo 287828 984527 := bstep (se 1 (by rfl) ⟨738395, by rfl⟩ : syracuseStep 984527 = 1476791) B1476791
theorem B1641343 : Blo 287828 1641343 := bstep (se 1 (by rfl) ⟨1231007, by rfl⟩ : syracuseStep 1641343 = 2462015) B2462015
theorem B22613231 : Blo 287828 22613231 := bstep (se 1 (by rfl) ⟨16959923, by rfl⟩ : syracuseStep 22613231 = 33919847) B33919847
theorem B139695547 : Blo 287828 139695547 := bstep (se 1 (by rfl) ⟨104771660, by rfl⟩ : syracuseStep 139695547 = 209543321) B209543321
theorem B366059 : Blo 287828 366059 := bstep (se 1 (by rfl) ⟨274544, by rfl⟩ : syracuseStep 366059 = 549089) B549089
theorem B433307 : Blo 287828 433307 := bstep (se 1 (by rfl) ⟨324980, by rfl⟩ : syracuseStep 433307 = 649961) B649961
theorem B827131 : Blo 287828 827131 := bstep (se 1 (by rfl) ⟨620348, by rfl⟩ : syracuseStep 827131 = 1240697) B1240697
theorem B729607 : Blo 287828 729607 := bstep (se 1 (by rfl) ⟨547205, by rfl⟩ : syracuseStep 729607 = 1094411) B1094411
theorem B1909889 : Blo 287828 1909889 := bstep (se 2 (by rfl) ⟨716208, by rfl⟩ : syracuseStep 1909889 = 1432417) B1432417
theorem B11970271 : Blo 287828 11970271 := bstep (se 1 (by rfl) ⟨8977703, by rfl⟩ : syracuseStep 11970271 = 17955407) B17955407
theorem B829511 : Blo 287828 829511 := bstep (se 1 (by rfl) ⟨622133, by rfl⟩ : syracuseStep 829511 = 1244267) B1244267
theorem B1485449 : Blo 287828 1485449 := bstep (se 2 (by rfl) ⟨557043, by rfl⟩ : syracuseStep 1485449 = 1114087) B1114087
theorem B3123947 : Blo 287828 3123947 := bstep (se 1 (by rfl) ⟨2342960, by rfl⟩ : syracuseStep 3123947 = 4685921) B4685921
theorem B830195 : Blo 287828 830195 := bstep (se 1 (by rfl) ⟨622646, by rfl⟩ : syracuseStep 830195 = 1245293) B1245293
theorem B3879251 : Blo 287828 3879251 := bstep (se 1 (by rfl) ⟨2909438, by rfl⟩ : syracuseStep 3879251 = 5818877) B5818877
theorem B9351611 : Blo 287828 9351611 := bstep (se 1 (by rfl) ⟨7013708, by rfl⟩ : syracuseStep 9351611 = 14027417) B14027417
theorem B2375333 : Blo 287828 2375333 := bstep (se 4 (by rfl) ⟨222687, by rfl⟩ : syracuseStep 2375333 = 445375) B445375
theorem B1458323 : Blo 287828 1458323 := bstep (se 1 (by rfl) ⟨1093742, by rfl⟩ : syracuseStep 1458323 = 2187485) B2187485
theorem B738335 : Blo 287828 738335 := bstep (se 1 (by rfl) ⟨553751, by rfl⟩ : syracuseStep 738335 = 1107503) B1107503
theorem B1460105 : Blo 287828 1460105 := bstep (se 2 (by rfl) ⟨547539, by rfl⟩ : syracuseStep 1460105 = 1095079) B1095079
theorem B4181179 : Blo 287828 4181179 := bstep (se 1 (by rfl) ⟨3135884, by rfl⟩ : syracuseStep 4181179 = 6271769) B6271769
theorem B1101383 : Blo 287828 1101383 := bstep (se 1 (by rfl) ⟨826037, by rfl⟩ : syracuseStep 1101383 = 1652075) B1652075
theorem B1463183 : Blo 287828 1463183 := bstep (se 1 (by rfl) ⟨1097387, by rfl⟩ : syracuseStep 1463183 = 2194775) B2194775
theorem B109009307 : Blo 287828 109009307 := bstep (se 1 (by rfl) ⟨81756980, by rfl⟩ : syracuseStep 109009307 = 163513961) B163513961
theorem B9984647 : Blo 287828 9984647 := bstep (se 1 (by rfl) ⟨7488485, by rfl⟩ : syracuseStep 9984647 = 14976971) B14976971
theorem B1759927 : Blo 287828 1759927 := bstep (se 1 (by rfl) ⟨1319945, by rfl⟩ : syracuseStep 1759927 = 2639891) B2639891
theorem B90659807 : Blo 287828 90659807 := bstep (se 1 (by rfl) ⟨67994855, by rfl⟩ : syracuseStep 90659807 = 135989711) B135989711
theorem B42392807 : Blo 287828 42392807 := bstep (se 1 (by rfl) ⟨31794605, by rfl⟩ : syracuseStep 42392807 = 63589211) B63589211
theorem B3302369 : Blo 287828 3302369 := bstep (se 2 (by rfl) ⟨1238388, by rfl⟩ : syracuseStep 3302369 = 2476777) B2476777
theorem B976319 : Blo 287828 976319 := bstep (se 1 (by rfl) ⟨732239, by rfl⟩ : syracuseStep 976319 = 1464479) B1464479
theorem B288223 : Blo 287828 288223 := bstep (se 1 (by rfl) ⟨216167, by rfl⟩ : syracuseStep 288223 = 432335) B432335
theorem B648863 : Blo 287828 648863 := bstep (se 1 (by rfl) ⟨486647, by rfl⟩ : syracuseStep 648863 = 973295) B973295
theorem B288859 : Blo 287828 288859 := bstep (se 1 (by rfl) ⟨216644, by rfl⟩ : syracuseStep 288859 = 433289) B433289
theorem B977615 : Blo 287828 977615 := bstep (se 1 (by rfl) ⟨733211, by rfl⟩ : syracuseStep 977615 = 1466423) B1466423
theorem B2747105 : Blo 287828 2747105 := bstep (se 2 (by rfl) ⟨1030164, by rfl⟩ : syracuseStep 2747105 = 2060329) B2060329
theorem B290719 : Blo 287828 290719 := bstep (se 1 (by rfl) ⟨218039, by rfl⟩ : syracuseStep 290719 = 436079) B436079
theorem B290863 : Blo 287828 290863 := bstep (se 1 (by rfl) ⟨218147, by rfl⟩ : syracuseStep 290863 = 436295) B436295
theorem B291303 : Blo 287828 291303 := bstep (se 1 (by rfl) ⟨218477, by rfl⟩ : syracuseStep 291303 = 436955) B436955
theorem B291567 : Blo 287828 291567 := bstep (se 1 (by rfl) ⟨218675, by rfl⟩ : syracuseStep 291567 = 437351) B437351
theorem B291615 : Blo 287828 291615 := bstep (se 1 (by rfl) ⟨218711, by rfl⟩ : syracuseStep 291615 = 437423) B437423
theorem B12056377 : Blo 287828 12056377 := bstep (se 2 (by rfl) ⟨4521141, by rfl⟩ : syracuseStep 12056377 = 9042283) B9042283
theorem B5306633 : Blo 287828 5306633 := bstep (se 2 (by rfl) ⟨1989987, by rfl⟩ : syracuseStep 5306633 = 3979975) B3979975
theorem B25328375 : Blo 287828 25328375 := bstep (se 1 (by rfl) ⟨18996281, by rfl⟩ : syracuseStep 25328375 = 37992563) B37992563
theorem B10681247 : Blo 287828 10681247 := bstep (se 1 (by rfl) ⟨8010935, by rfl⟩ : syracuseStep 10681247 = 16021871) B16021871
theorem B654497 : Blo 287828 654497 := bstep (se 2 (by rfl) ⟨245436, by rfl⟩ : syracuseStep 654497 = 490873) B490873
theorem B15105473 : Blo 287828 15105473 := bstep (se 2 (by rfl) ⟨5664552, by rfl⟩ : syracuseStep 15105473 = 11329105) B11329105
theorem B3651567095 : Blo 287828 3651567095 := bstep (se 1 (by rfl) ⟨2738675321, by rfl⟩ : syracuseStep 3651567095 = 5477350643) B5477350643
theorem B982583 : Blo 287828 982583 := bstep (se 1 (by rfl) ⟨736937, by rfl⟩ : syracuseStep 982583 = 1473875) B1473875
theorem B655343 : Blo 287828 655343 := bstep (se 1 (by rfl) ⟨491507, by rfl⟩ : syracuseStep 655343 = 983015) B983015
theorem B492223 : Blo 287828 492223 := bstep (se 1 (by rfl) ⟨369167, by rfl⟩ : syracuseStep 492223 = 738335) B738335
theorem B656351 : Blo 287828 656351 := bstep (se 1 (by rfl) ⟨492263, by rfl⟩ : syracuseStep 656351 = 984527) B984527
theorem B54265565 : Blo 287828 54265565 := bstep (se 3 (by rfl) ⟨10174793, by rfl⟩ : syracuseStep 54265565 = 20349587) B20349587
theorem B15075487 : Blo 287828 15075487 := bstep (se 1 (by rfl) ⟨11306615, by rfl⟩ : syracuseStep 15075487 = 22613231) B22613231
theorem B15960361 : Blo 287828 15960361 := bstep (se 2 (by rfl) ⟨5985135, by rfl⟩ : syracuseStep 15960361 = 11970271) B11970271
theorem B5574905 : Blo 287828 5574905 := bstep (se 2 (by rfl) ⟨2090589, by rfl⟩ : syracuseStep 5574905 = 4181179) B4181179
theorem B6656431 : Blo 287828 6656431 := bstep (se 1 (by rfl) ⟨4992323, by rfl⟩ : syracuseStep 6656431 = 9984647) B9984647
theorem B2201579 : Blo 287828 2201579 := bstep (se 1 (by rfl) ⟨1651184, by rfl⟩ : syracuseStep 2201579 = 3302369) B3302369
theorem B432575 : Blo 287828 432575 := bstep (se 1 (by rfl) ⟨324431, by rfl⟩ : syracuseStep 432575 = 648863) B648863
theorem B990299 : Blo 287828 990299 := bstep (se 1 (by rfl) ⟨742724, by rfl⟩ : syracuseStep 990299 = 1485449) B1485449
theorem B186260729 : Blo 287828 186260729 := bstep (se 2 (by rfl) ⟨69847773, by rfl⟩ : syracuseStep 186260729 = 139695547) B139695547
theorem B8330525 : Blo 287828 8330525 := bstep (se 3 (by rfl) ⟨1561973, by rfl⟩ : syracuseStep 8330525 = 3123947) B3123947
theorem B6234407 : Blo 287828 6234407 := bstep (se 1 (by rfl) ⟨4675805, by rfl⟩ : syracuseStep 6234407 = 9351611) B9351611
theorem B16885583 : Blo 287828 16885583 := bstep (se 1 (by rfl) ⟨12664187, by rfl⟩ : syracuseStep 16885583 = 25328375) B25328375
theorem B7120831 : Blo 287828 7120831 := bstep (se 1 (by rfl) ⟨5340623, by rfl⟩ : syracuseStep 7120831 = 10681247) B10681247
theorem B436331 : Blo 287828 436331 := bstep (se 1 (by rfl) ⟨327248, by rfl⟩ : syracuseStep 436331 = 654497) B654497
theorem B10070315 : Blo 287828 10070315 := bstep (se 1 (by rfl) ⟨7552736, by rfl⟩ : syracuseStep 10070315 = 15105473) B15105473
theorem B2434378063 : Blo 287828 2434378063 := bstep (se 1 (by rfl) ⟨1825783547, by rfl⟩ : syracuseStep 2434378063 = 3651567095) B3651567095
theorem B1583555 : Blo 287828 1583555 := bstep (se 1 (by rfl) ⟨1187666, by rfl⟩ : syracuseStep 1583555 = 2375333) B2375333
theorem B436895 : Blo 287828 436895 := bstep (se 1 (by rfl) ⟨327671, by rfl⟩ : syracuseStep 436895 = 655343) B655343
theorem B437483 : Blo 287828 437483 := bstep (se 1 (by rfl) ⟨328112, by rfl⟩ : syracuseStep 437483 = 656225) B656225
theorem B734255 : Blo 287828 734255 := bstep (se 1 (by rfl) ⟨550691, by rfl⟩ : syracuseStep 734255 = 1101383) B1101383
theorem B60439871 : Blo 287828 60439871 := bstep (se 1 (by rfl) ⟨45329903, by rfl⟩ : syracuseStep 60439871 = 90659807) B90659807
theorem B28261871 : Blo 287828 28261871 := bstep (se 1 (by rfl) ⟨21196403, by rfl⟩ : syracuseStep 28261871 = 42392807) B42392807
theorem B16075169 : Blo 287828 16075169 := bstep (se 2 (by rfl) ⟨6028188, by rfl⟩ : syracuseStep 16075169 = 12056377) B12056377
theorem B2346569 : Blo 287828 2346569 := bstep (se 2 (by rfl) ⟨879963, by rfl⟩ : syracuseStep 2346569 = 1759927) B1759927
theorem B1102841 : Blo 287828 1102841 := bstep (se 2 (by rfl) ⟨413565, by rfl⟩ : syracuseStep 1102841 = 827131) B827131
theorem B972215 : Blo 287828 972215 := bstep (se 1 (by rfl) ⟨729161, by rfl⟩ : syracuseStep 972215 = 1458323) B1458323
theorem B972809 : Blo 287828 972809 := bstep (se 2 (by rfl) ⟨364803, by rfl⟩ : syracuseStep 972809 = 729607) B729607
theorem B973403 : Blo 287828 973403 := bstep (se 1 (by rfl) ⟨730052, by rfl⟩ : syracuseStep 973403 = 1460105) B1460105
theorem B975455 : Blo 287828 975455 := bstep (se 1 (by rfl) ⟨731591, by rfl⟩ : syracuseStep 975455 = 1463183) B1463183
theorem B2188457 : Blo 287828 2188457 := bstep (se 2 (by rfl) ⟨820671, by rfl⟩ : syracuseStep 2188457 = 1641343) B1641343
theorem B976157 : Blo 287828 976157 := bstep (se 3 (by rfl) ⟨183029, by rfl⟩ : syracuseStep 976157 = 366059) B366059
theorem B72672871 : Blo 287828 72672871 := bstep (se 1 (by rfl) ⟨54504653, by rfl⟩ : syracuseStep 72672871 = 109009307) B109009307
theorem B288871 : Blo 287828 288871 := bstep (se 1 (by rfl) ⟨216653, by rfl⟩ : syracuseStep 288871 = 433307) B433307
theorem B1273259 : Blo 287828 1273259 := bstep (se 1 (by rfl) ⟨954944, by rfl⟩ : syracuseStep 1273259 = 1909889) B1909889
theorem B650879 : Blo 287828 650879 := bstep (se 1 (by rfl) ⟨488159, by rfl⟩ : syracuseStep 650879 = 976319) B976319
theorem B553007 : Blo 287828 553007 := bstep (se 1 (by rfl) ⟨414755, by rfl⟩ : syracuseStep 553007 = 829511) B829511
theorem B651743 : Blo 287828 651743 := bstep (se 1 (by rfl) ⟨488807, by rfl⟩ : syracuseStep 651743 = 977615) B977615
theorem B1831403 : Blo 287828 1831403 := bstep (se 1 (by rfl) ⟨1373552, by rfl⟩ : syracuseStep 1831403 = 2747105) B2747105
theorem B553463 : Blo 287828 553463 := bstep (se 1 (by rfl) ⟨415097, by rfl⟩ : syracuseStep 553463 = 830195) B830195
theorem B2586167 : Blo 287828 2586167 := bstep (se 1 (by rfl) ⟨1939625, by rfl⟩ : syracuseStep 2586167 = 3879251) B3879251
theorem B3537755 : Blo 287828 3537755 := bstep (se 1 (by rfl) ⟨2653316, by rfl⟩ : syracuseStep 3537755 = 5306633) B5306633
theorem B655055 : Blo 287828 655055 := bstep (se 1 (by rfl) ⟨491291, by rfl⟩ : syracuseStep 655055 = 982583) B982583
theorem B1474685 : Blo 287828 1474685 := bstep (se 3 (by rfl) ⟨276503, by rfl⟩ : syracuseStep 1474685 = 553007) B553007
theorem B656297 : Blo 287828 656297 := bstep (se 2 (by rfl) ⟨246111, by rfl⟩ : syracuseStep 656297 = 492223) B492223
theorem B36177043 : Blo 287828 36177043 := bstep (se 1 (by rfl) ⟨27132782, by rfl⟩ : syracuseStep 36177043 = 54265565) B54265565
theorem B10716779 : Blo 287828 10716779 := bstep (se 1 (by rfl) ⟨8037584, by rfl⟩ : syracuseStep 10716779 = 16075169) B16075169
theorem B96897161 : Blo 287828 96897161 := bstep (se 2 (by rfl) ⟨36336435, by rfl⟩ : syracuseStep 96897161 = 72672871) B72672871
theorem B3245837417 : Blo 287828 3245837417 := bstep (se 2 (by rfl) ⟨1217189031, by rfl⟩ : syracuseStep 3245837417 = 2434378063) B2434378063
theorem B660199 : Blo 287828 660199 := bstep (se 1 (by rfl) ⟨495149, by rfl⟩ : syracuseStep 660199 = 990299) B990299
theorem B433919 : Blo 287828 433919 := bstep (se 1 (by rfl) ⟨325439, by rfl⟩ : syracuseStep 433919 = 650879) B650879
theorem B434495 : Blo 287828 434495 := bstep (se 1 (by rfl) ⟨325871, by rfl⟩ : syracuseStep 434495 = 651743) B651743
theorem B1220935 : Blo 287828 1220935 := bstep (se 1 (by rfl) ⟨915701, by rfl⟩ : syracuseStep 1220935 = 1831403) B1831403
theorem B368975 : Blo 287828 368975 := bstep (se 1 (by rfl) ⟨276731, by rfl⟩ : syracuseStep 368975 = 553463) B553463
theorem B436703 : Blo 287828 436703 := bstep (se 1 (by rfl) ⟨327527, by rfl⟩ : syracuseStep 436703 = 655055) B655055
theorem B437567 : Blo 287828 437567 := bstep (se 1 (by rfl) ⟨328175, by rfl⟩ : syracuseStep 437567 = 656351) B656351
theorem B3716603 : Blo 287828 3716603 := bstep (se 1 (by rfl) ⟨2787452, by rfl⟩ : syracuseStep 3716603 = 5574905) B5574905
theorem B20100649 : Blo 287828 20100649 := bstep (se 2 (by rfl) ⟨7537743, by rfl⟩ : syracuseStep 20100649 = 15075487) B15075487
theorem B21280481 : Blo 287828 21280481 := bstep (se 2 (by rfl) ⟨7980180, by rfl⟩ : syracuseStep 21280481 = 15960361) B15960361
theorem B735227 : Blo 287828 735227 := bstep (se 1 (by rfl) ⟨551420, by rfl⟩ : syracuseStep 735227 = 1102841) B1102841
theorem B5553683 : Blo 287828 5553683 := bstep (se 1 (by rfl) ⟨4165262, by rfl⟩ : syracuseStep 5553683 = 8330525) B8330525
theorem B1458971 : Blo 287828 1458971 := bstep (se 1 (by rfl) ⟨1094228, by rfl⟩ : syracuseStep 1458971 = 2188457) B2188457
theorem B11257055 : Blo 287828 11257055 := bstep (se 1 (by rfl) ⟨8442791, by rfl⟩ : syracuseStep 11257055 = 16885583) B16885583
theorem B1724111 : Blo 287828 1724111 := bstep (se 1 (by rfl) ⟨1293083, by rfl⟩ : syracuseStep 1724111 = 2586167) B2586167
theorem B40293247 : Blo 287828 40293247 := bstep (se 1 (by rfl) ⟨30219935, by rfl⟩ : syracuseStep 40293247 = 60439871) B60439871
theorem B1564379 : Blo 287828 1564379 := bstep (se 1 (by rfl) ⟨1173284, by rfl⟩ : syracuseStep 1564379 = 2346569) B2346569
theorem B9494441 : Blo 287828 9494441 := bstep (se 2 (by rfl) ⟨3560415, by rfl⟩ : syracuseStep 9494441 = 7120831) B7120831
theorem B648143 : Blo 287828 648143 := bstep (se 1 (by rfl) ⟨486107, by rfl⟩ : syracuseStep 648143 = 972215) B972215
theorem B1467719 : Blo 287828 1467719 := bstep (se 1 (by rfl) ⟨1100789, by rfl⟩ : syracuseStep 1467719 = 2201579) B2201579
theorem B648539 : Blo 287828 648539 := bstep (se 1 (by rfl) ⟨486404, by rfl⟩ : syracuseStep 648539 = 972809) B972809
theorem B288383 : Blo 287828 288383 := bstep (se 1 (by rfl) ⟨216287, by rfl⟩ : syracuseStep 288383 = 432575) B432575
theorem B648935 : Blo 287828 648935 := bstep (se 1 (by rfl) ⟨486701, by rfl⟩ : syracuseStep 648935 = 973403) B973403
theorem B4156271 : Blo 287828 4156271 := bstep (se 1 (by rfl) ⟨3117203, by rfl⟩ : syracuseStep 4156271 = 6234407) B6234407
theorem B650303 : Blo 287828 650303 := bstep (se 1 (by rfl) ⟨487727, by rfl⟩ : syracuseStep 650303 = 975455) B975455
theorem B8875241 : Blo 287828 8875241 := bstep (se 2 (by rfl) ⟨3328215, by rfl⟩ : syracuseStep 8875241 = 6656431) B6656431
theorem B650771 : Blo 287828 650771 := bstep (se 1 (by rfl) ⟨488078, by rfl⟩ : syracuseStep 650771 = 976157) B976157
theorem B4222813 : Blo 287828 4222813 := bstep (se 3 (by rfl) ⟨791777, by rfl⟩ : syracuseStep 4222813 = 1583555) B1583555
theorem B290887 : Blo 287828 290887 := bstep (se 1 (by rfl) ⟨218165, by rfl⟩ : syracuseStep 290887 = 436331) B436331
theorem B6713543 : Blo 287828 6713543 := bstep (se 1 (by rfl) ⟨5035157, by rfl⟩ : syracuseStep 6713543 = 10070315) B10070315
theorem B291263 : Blo 287828 291263 := bstep (se 1 (by rfl) ⟨218447, by rfl⟩ : syracuseStep 291263 = 436895) B436895
theorem B291655 : Blo 287828 291655 := bstep (se 1 (by rfl) ⟨218741, by rfl⟩ : syracuseStep 291655 = 437483) B437483
theorem B848839 : Blo 287828 848839 := bstep (se 1 (by rfl) ⟨636629, by rfl⟩ : syracuseStep 848839 = 1273259) B1273259
theorem B496695277 : Blo 287828 496695277 := bstep (se 3 (by rfl) ⟨93130364, by rfl⟩ : syracuseStep 496695277 = 186260729) B186260729
theorem B489503 : Blo 287828 489503 := bstep (se 1 (by rfl) ⟨367127, by rfl⟩ : syracuseStep 489503 = 734255) B734255
theorem B2358503 : Blo 287828 2358503 := bstep (se 1 (by rfl) ⟨1768877, by rfl⟩ : syracuseStep 2358503 = 3537755) B3537755
theorem B18841247 : Blo 287828 18841247 := bstep (se 1 (by rfl) ⟨14130935, by rfl⟩ : syracuseStep 18841247 = 28261871) B28261871
theorem B983123 : Blo 287828 983123 := bstep (se 1 (by rfl) ⟨737342, by rfl⟩ : syracuseStep 983123 = 1474685) B1474685
theorem B7504703 : Blo 287828 7504703 := bstep (se 1 (by rfl) ⟨5628527, by rfl⟩ : syracuseStep 7504703 = 11257055) B11257055
theorem B983933 : Blo 287828 983933 := bstep (se 3 (by rfl) ⟨184487, by rfl⟩ : syracuseStep 983933 = 368975) B368975
theorem B7144519 : Blo 287828 7144519 := bstep (se 1 (by rfl) ⟨5358389, by rfl⟩ : syracuseStep 7144519 = 10716779) B10716779
theorem B48236057 : Blo 287828 48236057 := bstep (se 2 (by rfl) ⟨18088521, by rfl⟩ : syracuseStep 48236057 = 36177043) B36177043
theorem B1149407 : Blo 287828 1149407 := bstep (se 1 (by rfl) ⟨862055, by rfl⟩ : syracuseStep 1149407 = 1724111) B1724111
theorem B6329627 : Blo 287828 6329627 := bstep (se 1 (by rfl) ⟨4747220, by rfl⟩ : syracuseStep 6329627 = 9494441) B9494441
theorem B432095 : Blo 287828 432095 := bstep (se 1 (by rfl) ⟨324071, by rfl⟩ : syracuseStep 432095 = 648143) B648143
theorem B432359 : Blo 287828 432359 := bstep (se 1 (by rfl) ⟨324269, by rfl⟩ : syracuseStep 432359 = 648539) B648539
theorem B432623 : Blo 287828 432623 := bstep (se 1 (by rfl) ⟨324467, by rfl⟩ : syracuseStep 432623 = 648935) B648935
theorem B433535 : Blo 287828 433535 := bstep (se 1 (by rfl) ⟨325151, by rfl⟩ : syracuseStep 433535 = 650303) B650303
theorem B433847 : Blo 287828 433847 := bstep (se 1 (by rfl) ⟨325385, by rfl⟩ : syracuseStep 433847 = 650771) B650771
theorem B12560831 : Blo 287828 12560831 := bstep (se 1 (by rfl) ⟨9420623, by rfl⟩ : syracuseStep 12560831 = 18841247) B18841247
theorem B437531 : Blo 287828 437531 := bstep (se 1 (by rfl) ⟨328148, by rfl⟩ : syracuseStep 437531 = 656297) B656297
theorem B258392429 : Blo 287828 258392429 := bstep (se 3 (by rfl) ⟨48448580, by rfl⟩ : syracuseStep 258392429 = 96897161) B96897161
theorem B53724329 : Blo 287828 53724329 := bstep (se 2 (by rfl) ⟨20146623, by rfl⟩ : syracuseStep 53724329 = 40293247) B40293247
theorem B1131785 : Blo 287828 1131785 := bstep (se 2 (by rfl) ⟨424419, by rfl⟩ : syracuseStep 1131785 = 848839) B848839
theorem B2770847 : Blo 287828 2770847 := bstep (se 1 (by rfl) ⟨2078135, by rfl⟩ : syracuseStep 2770847 = 4156271) B4156271
theorem B5916827 : Blo 287828 5916827 := bstep (se 1 (by rfl) ⟨4437620, by rfl⟩ : syracuseStep 5916827 = 8875241) B8875241
theorem B662260369 : Blo 287828 662260369 := bstep (se 2 (by rfl) ⟨248347638, by rfl⟩ : syracuseStep 662260369 = 496695277) B496695277
theorem B4475695 : Blo 287828 4475695 := bstep (se 1 (by rfl) ⟨3356771, by rfl⟩ : syracuseStep 4475695 = 6713543) B6713543
theorem B2477735 : Blo 287828 2477735 := bstep (se 1 (by rfl) ⟨1858301, by rfl⟩ : syracuseStep 2477735 = 3716603) B3716603
theorem B1627913 : Blo 287828 1627913 := bstep (se 2 (by rfl) ⟨610467, by rfl⟩ : syracuseStep 1627913 = 1220935) B1220935
theorem B972647 : Blo 287828 972647 := bstep (se 1 (by rfl) ⟨729485, by rfl⟩ : syracuseStep 972647 = 1458971) B1458971
theorem B2163891611 : Blo 287828 2163891611 := bstep (se 1 (by rfl) ⟨1622918708, by rfl⟩ : syracuseStep 2163891611 = 3245837417) B3245837417
theorem B5630417 : Blo 287828 5630417 := bstep (se 2 (by rfl) ⟨2111406, by rfl⟩ : syracuseStep 5630417 = 4222813) B4222813
theorem B1042919 : Blo 287828 1042919 := bstep (se 1 (by rfl) ⟨782189, by rfl⟩ : syracuseStep 1042919 = 1564379) B1564379
theorem B289279 : Blo 287828 289279 := bstep (se 1 (by rfl) ⟨216959, by rfl⟩ : syracuseStep 289279 = 433919) B433919
theorem B289663 : Blo 287828 289663 := bstep (se 1 (by rfl) ⟨217247, by rfl⟩ : syracuseStep 289663 = 434495) B434495
theorem B978479 : Blo 287828 978479 := bstep (se 1 (by rfl) ⟨733859, by rfl⟩ : syracuseStep 978479 = 1467719) B1467719
theorem B880265 : Blo 287828 880265 := bstep (se 2 (by rfl) ⟨330099, by rfl⟩ : syracuseStep 880265 = 660199) B660199
theorem B291135 : Blo 287828 291135 := bstep (se 1 (by rfl) ⟨218351, by rfl⟩ : syracuseStep 291135 = 436703) B436703
theorem B26800865 : Blo 287828 26800865 := bstep (se 2 (by rfl) ⟨10050324, by rfl⟩ : syracuseStep 26800865 = 20100649) B20100649
theorem B291711 : Blo 287828 291711 := bstep (se 1 (by rfl) ⟨218783, by rfl⟩ : syracuseStep 291711 = 437567) B437567
theorem B14186987 : Blo 287828 14186987 := bstep (se 1 (by rfl) ⟨10640240, by rfl⟩ : syracuseStep 14186987 = 21280481) B21280481
theorem B490151 : Blo 287828 490151 := bstep (se 1 (by rfl) ⟨367613, by rfl⟩ : syracuseStep 490151 = 735227) B735227
theorem B326335 : Blo 287828 326335 := bstep (se 1 (by rfl) ⟨244751, by rfl⟩ : syracuseStep 326335 = 489503) B489503
theorem B1572335 : Blo 287828 1572335 := bstep (se 1 (by rfl) ⟨1179251, by rfl⟩ : syracuseStep 1572335 = 2358503) B2358503
theorem B3702455 : Blo 287828 3702455 := bstep (se 1 (by rfl) ⟨2776841, by rfl⟩ : syracuseStep 3702455 = 5553683) B5553683
theorem B655415 : Blo 287828 655415 := bstep (se 1 (by rfl) ⟨491561, by rfl⟩ : syracuseStep 655415 = 983123) B983123
theorem B172261619 : Blo 287828 172261619 := bstep (se 1 (by rfl) ⟨129196214, by rfl⟩ : syracuseStep 172261619 = 258392429) B258392429
theorem B655955 : Blo 287828 655955 := bstep (se 1 (by rfl) ⟨491966, by rfl⟩ : syracuseStep 655955 = 983933) B983933
theorem B35816219 : Blo 287828 35816219 := bstep (se 1 (by rfl) ⟨26862164, by rfl⟩ : syracuseStep 35816219 = 53724329) B53724329
theorem B754523 : Blo 287828 754523 := bstep (se 1 (by rfl) ⟨565892, by rfl⟩ : syracuseStep 754523 = 1131785) B1131785
theorem B5967593 : Blo 287828 5967593 := bstep (se 2 (by rfl) ⟨2237847, by rfl⟩ : syracuseStep 5967593 = 4475695) B4475695
theorem B1085275 : Blo 287828 1085275 := bstep (se 1 (by rfl) ⟨813956, by rfl⟩ : syracuseStep 1085275 = 1627913) B1627913
theorem B695279 : Blo 287828 695279 := bstep (se 1 (by rfl) ⟨521459, by rfl⟩ : syracuseStep 695279 = 1042919) B1042919
theorem B17867243 : Blo 287828 17867243 := bstep (se 1 (by rfl) ⟨13400432, by rfl⟩ : syracuseStep 17867243 = 26800865) B26800865
theorem B435113 : Blo 287828 435113 := bstep (se 2 (by rfl) ⟨163167, by rfl⟩ : syracuseStep 435113 = 326335) B326335
theorem B2468303 : Blo 287828 2468303 := bstep (se 1 (by rfl) ⟨1851227, by rfl⟩ : syracuseStep 2468303 = 3702455) B3702455
theorem B32157371 : Blo 287828 32157371 := bstep (se 1 (by rfl) ⟨24118028, by rfl⟩ : syracuseStep 32157371 = 48236057) B48236057
theorem B1847231 : Blo 287828 1847231 := bstep (se 1 (by rfl) ⟨1385423, by rfl⟩ : syracuseStep 1847231 = 2770847) B2770847
theorem B3944551 : Blo 287828 3944551 := bstep (se 1 (by rfl) ⟨2958413, by rfl⟩ : syracuseStep 3944551 = 5916827) B5916827
theorem B766271 : Blo 287828 766271 := bstep (se 1 (by rfl) ⟨574703, by rfl⟩ : syracuseStep 766271 = 1149407) B1149407
theorem B1651823 : Blo 287828 1651823 := bstep (se 1 (by rfl) ⟨1238867, by rfl⟩ : syracuseStep 1651823 = 2477735) B2477735
theorem B883013825 : Blo 287828 883013825 := bstep (se 2 (by rfl) ⟨331130184, by rfl⟩ : syracuseStep 883013825 = 662260369) B662260369
theorem B1442594407 : Blo 287828 1442594407 := bstep (se 1 (by rfl) ⟨1081945805, by rfl⟩ : syracuseStep 1442594407 = 2163891611) B2163891611
theorem B8373887 : Blo 287828 8373887 := bstep (se 1 (by rfl) ⟨6280415, by rfl⟩ : syracuseStep 8373887 = 12560831) B12560831
theorem B3753611 : Blo 287828 3753611 := bstep (se 1 (by rfl) ⟨2815208, by rfl⟩ : syracuseStep 3753611 = 5630417) B5630417
theorem B9457991 : Blo 287828 9457991 := bstep (se 1 (by rfl) ⟨7093493, by rfl⟩ : syracuseStep 9457991 = 14186987) B14186987
theorem B2347373 : Blo 287828 2347373 := bstep (se 3 (by rfl) ⟨440132, by rfl⟩ : syracuseStep 2347373 = 880265) B880265
theorem B5003135 : Blo 287828 5003135 := bstep (se 1 (by rfl) ⟨3752351, by rfl⟩ : syracuseStep 5003135 = 7504703) B7504703
theorem B9526025 : Blo 287828 9526025 := bstep (se 2 (by rfl) ⟨3572259, by rfl⟩ : syracuseStep 9526025 = 7144519) B7144519
theorem B4219751 : Blo 287828 4219751 := bstep (se 1 (by rfl) ⟨3164813, by rfl⟩ : syracuseStep 4219751 = 6329627) B6329627
theorem B648431 : Blo 287828 648431 := bstep (se 1 (by rfl) ⟨486323, by rfl⟩ : syracuseStep 648431 = 972647) B972647
theorem B288063 : Blo 287828 288063 := bstep (se 1 (by rfl) ⟨216047, by rfl⟩ : syracuseStep 288063 = 432095) B432095
theorem B288239 : Blo 287828 288239 := bstep (se 1 (by rfl) ⟨216179, by rfl⟩ : syracuseStep 288239 = 432359) B432359
theorem B288415 : Blo 287828 288415 := bstep (se 1 (by rfl) ⟨216311, by rfl⟩ : syracuseStep 288415 = 432623) B432623
theorem B289023 : Blo 287828 289023 := bstep (se 1 (by rfl) ⟨216767, by rfl⟩ : syracuseStep 289023 = 433535) B433535
theorem B289231 : Blo 287828 289231 := bstep (se 1 (by rfl) ⟨216923, by rfl⟩ : syracuseStep 289231 = 433847) B433847
theorem B291687 : Blo 287828 291687 := bstep (se 1 (by rfl) ⟨218765, by rfl⟩ : syracuseStep 291687 = 437531) B437531
theorem B652319 : Blo 287828 652319 := bstep (se 1 (by rfl) ⟨489239, by rfl⟩ : syracuseStep 652319 = 978479) B978479
theorem B326767 : Blo 287828 326767 := bstep (se 1 (by rfl) ⟨245075, by rfl⟩ : syracuseStep 326767 = 490151) B490151
theorem B1048223 : Blo 287828 1048223 := bstep (se 1 (by rfl) ⟨786167, by rfl⟩ : syracuseStep 1048223 = 1572335) B1572335
theorem B47645981 : Blo 287828 47645981 := bstep (se 3 (by rfl) ⟨8933621, by rfl⟩ : syracuseStep 47645981 = 17867243) B17867243
theorem B463519 : Blo 287828 463519 := bstep (se 1 (by rfl) ⟨347639, by rfl⟩ : syracuseStep 463519 = 695279) B695279
theorem B1447033 : Blo 287828 1447033 := bstep (se 2 (by rfl) ⟨542637, by rfl⟩ : syracuseStep 1447033 = 1085275) B1085275
theorem B432287 : Blo 287828 432287 := bstep (se 1 (by rfl) ⟨324215, by rfl⟩ : syracuseStep 432287 = 648431) B648431
theorem B1645535 : Blo 287828 1645535 := bstep (se 1 (by rfl) ⟨1234151, by rfl⟩ : syracuseStep 1645535 = 2468303) B2468303
theorem B434879 : Blo 287828 434879 := bstep (se 1 (by rfl) ⟨326159, by rfl⟩ : syracuseStep 434879 = 652319) B652319
theorem B435689 : Blo 287828 435689 := bstep (se 2 (by rfl) ⟨163383, by rfl⟩ : syracuseStep 435689 = 326767) B326767
theorem B1923459209 : Blo 287828 1923459209 := bstep (se 2 (by rfl) ⟨721297203, by rfl⟩ : syracuseStep 1923459209 = 1442594407) B1442594407
theorem B698815 : Blo 287828 698815 := bstep (se 1 (by rfl) ⟨524111, by rfl⟩ : syracuseStep 698815 = 1048223) B1048223
theorem B436943 : Blo 287828 436943 := bstep (se 1 (by rfl) ⟨327707, by rfl⟩ : syracuseStep 436943 = 655415) B655415
theorem B437303 : Blo 287828 437303 := bstep (se 1 (by rfl) ⟨327977, by rfl⟩ : syracuseStep 437303 = 655955) B655955
theorem B503015 : Blo 287828 503015 := bstep (se 1 (by rfl) ⟨377261, by rfl⟩ : syracuseStep 503015 = 754523) B754523
theorem B2043389 : Blo 287828 2043389 := bstep (se 3 (by rfl) ⟨383135, by rfl⟩ : syracuseStep 2043389 = 766271) B766271
theorem B5582591 : Blo 287828 5582591 := bstep (se 1 (by rfl) ⟨4186943, by rfl⟩ : syracuseStep 5582591 = 8373887) B8373887
theorem B2502407 : Blo 287828 2502407 := bstep (se 1 (by rfl) ⟨1876805, by rfl⟩ : syracuseStep 2502407 = 3753611) B3753611
theorem B3978395 : Blo 287828 3978395 := bstep (se 1 (by rfl) ⟨2983796, by rfl⟩ : syracuseStep 3978395 = 5967593) B5967593
theorem B6305327 : Blo 287828 6305327 := bstep (se 1 (by rfl) ⟨4728995, by rfl⟩ : syracuseStep 6305327 = 9457991) B9457991
theorem B180042709 : Blo 287828 180042709 := bstep (se 7 (by rfl) ⟨2109875, by rfl⟩ : syracuseStep 180042709 = 4219751) B4219751
theorem B5259401 : Blo 287828 5259401 := bstep (se 2 (by rfl) ⟨1972275, by rfl⟩ : syracuseStep 5259401 = 3944551) B3944551
theorem B1231487 : Blo 287828 1231487 := bstep (se 1 (by rfl) ⟨923615, by rfl⟩ : syracuseStep 1231487 = 1847231) B1847231
theorem B1101215 : Blo 287828 1101215 := bstep (se 1 (by rfl) ⟨825911, by rfl⟩ : syracuseStep 1101215 = 1651823) B1651823
theorem B114841079 : Blo 287828 114841079 := bstep (se 1 (by rfl) ⟨86130809, by rfl⟩ : syracuseStep 114841079 = 172261619) B172261619
theorem B23877479 : Blo 287828 23877479 := bstep (se 1 (by rfl) ⟨17908109, by rfl⟩ : syracuseStep 23877479 = 35816219) B35816219
theorem B1564915 : Blo 287828 1564915 := bstep (se 1 (by rfl) ⟨1173686, by rfl⟩ : syracuseStep 1564915 = 2347373) B2347373
theorem B3335423 : Blo 287828 3335423 := bstep (se 1 (by rfl) ⟨2501567, by rfl⟩ : syracuseStep 3335423 = 5003135) B5003135
theorem B6350683 : Blo 287828 6350683 := bstep (se 1 (by rfl) ⟨4763012, by rfl⟩ : syracuseStep 6350683 = 9526025) B9526025
theorem B290075 : Blo 287828 290075 := bstep (se 1 (by rfl) ⟨217556, by rfl⟩ : syracuseStep 290075 = 435113) B435113
theorem B588675883 : Blo 287828 588675883 := bstep (se 1 (by rfl) ⟨441506912, by rfl⟩ : syracuseStep 588675883 = 883013825) B883013825
theorem B85752989 : Blo 287828 85752989 := bstep (se 3 (by rfl) ⟨16078685, by rfl⟩ : syracuseStep 85752989 = 32157371) B32157371
theorem B3506267 : Blo 287828 3506267 := bstep (se 1 (by rfl) ⟨2629700, by rfl⟩ : syracuseStep 3506267 = 5259401) B5259401
theorem B820991 : Blo 287828 820991 := bstep (se 1 (by rfl) ⟨615743, by rfl⟩ : syracuseStep 820991 = 1231487) B1231487
theorem B4203551 : Blo 287828 4203551 := bstep (se 1 (by rfl) ⟨3152663, by rfl⟩ : syracuseStep 4203551 = 6305327) B6305327
theorem B784901177 : Blo 287828 784901177 := bstep (se 2 (by rfl) ⟨294337941, by rfl⟩ : syracuseStep 784901177 = 588675883) B588675883
theorem B5449037 : Blo 287828 5449037 := bstep (se 3 (by rfl) ⟨1021694, by rfl⟩ : syracuseStep 5449037 = 2043389) B2043389
theorem B31763987 : Blo 287828 31763987 := bstep (se 1 (by rfl) ⟨23822990, by rfl⟩ : syracuseStep 31763987 = 47645981) B47645981
theorem B734143 : Blo 287828 734143 := bstep (se 1 (by rfl) ⟨550607, by rfl⟩ : syracuseStep 734143 = 1101215) B1101215
theorem B8467577 : Blo 287828 8467577 := bstep (se 2 (by rfl) ⟨3175341, by rfl⟩ : syracuseStep 8467577 = 6350683) B6350683
theorem B931753 : Blo 287828 931753 := bstep (se 2 (by rfl) ⟨349407, by rfl⟩ : syracuseStep 931753 = 698815) B698815
theorem B8894461 : Blo 287828 8894461 := bstep (se 3 (by rfl) ⟨1667711, by rfl⟩ : syracuseStep 8894461 = 3335423) B3335423
theorem B76560719 : Blo 287828 76560719 := bstep (se 1 (by rfl) ⟨57420539, by rfl⟩ : syracuseStep 76560719 = 114841079) B114841079
theorem B1097023 : Blo 287828 1097023 := bstep (se 1 (by rfl) ⟨822767, by rfl⟩ : syracuseStep 1097023 = 1645535) B1645535
theorem B3721727 : Blo 287828 3721727 := bstep (se 1 (by rfl) ⟨2791295, by rfl⟩ : syracuseStep 3721727 = 5582591) B5582591
theorem B57168659 : Blo 287828 57168659 := bstep (se 1 (by rfl) ⟨42876494, by rfl⟩ : syracuseStep 57168659 = 85752989) B85752989
theorem B2086553 : Blo 287828 2086553 := bstep (se 2 (by rfl) ⟨782457, by rfl⟩ : syracuseStep 2086553 = 1564915) B1564915
theorem B15918319 : Blo 287828 15918319 := bstep (se 1 (by rfl) ⟨11938739, by rfl⟩ : syracuseStep 15918319 = 23877479) B23877479
theorem B288191 : Blo 287828 288191 := bstep (se 1 (by rfl) ⟨216143, by rfl⟩ : syracuseStep 288191 = 432287) B432287
theorem B289919 : Blo 287828 289919 := bstep (se 1 (by rfl) ⟨217439, by rfl⟩ : syracuseStep 289919 = 434879) B434879
theorem B618025 : Blo 287828 618025 := bstep (se 2 (by rfl) ⟨231759, by rfl⟩ : syracuseStep 618025 = 463519) B463519
theorem B290459 : Blo 287828 290459 := bstep (se 1 (by rfl) ⟨217844, by rfl⟩ : syracuseStep 290459 = 435689) B435689
theorem B1282306139 : Blo 287828 1282306139 := bstep (se 1 (by rfl) ⟨961729604, by rfl⟩ : syracuseStep 1282306139 = 1923459209) B1923459209
theorem B1929377 : Blo 287828 1929377 := bstep (se 2 (by rfl) ⟨723516, by rfl⟩ : syracuseStep 1929377 = 1447033) B1447033
theorem B291295 : Blo 287828 291295 := bstep (se 1 (by rfl) ⟨218471, by rfl⟩ : syracuseStep 291295 = 436943) B436943
theorem B291535 : Blo 287828 291535 := bstep (se 1 (by rfl) ⟨218651, by rfl⟩ : syracuseStep 291535 = 437303) B437303
theorem B1668271 : Blo 287828 1668271 := bstep (se 1 (by rfl) ⟨1251203, by rfl⟩ : syracuseStep 1668271 = 2502407) B2502407
theorem B1341373 : Blo 287828 1341373 := bstep (se 3 (by rfl) ⟨251507, by rfl⟩ : syracuseStep 1341373 = 503015) B503015
theorem B2652263 : Blo 287828 2652263 := bstep (se 1 (by rfl) ⟨1989197, by rfl⟩ : syracuseStep 2652263 = 3978395) B3978395
theorem B240056945 : Blo 287828 240056945 := bstep (se 2 (by rfl) ⟨90021354, by rfl⟩ : syracuseStep 240056945 = 180042709) B180042709
theorem B5145005 : Blo 287828 5145005 := bstep (se 3 (by rfl) ⟨964688, by rfl⟩ : syracuseStep 5145005 = 1929377) B1929377
theorem B38112439 : Blo 287828 38112439 := bstep (se 1 (by rfl) ⟨28584329, by rfl⟩ : syracuseStep 38112439 = 57168659) B57168659
theorem B824033 : Blo 287828 824033 := bstep (se 2 (by rfl) ⟨309012, by rfl⟩ : syracuseStep 824033 = 618025) B618025
theorem B21175991 : Blo 287828 21175991 := bstep (se 1 (by rfl) ⟨15881993, by rfl⟩ : syracuseStep 21175991 = 31763987) B31763987
theorem B5645051 : Blo 287828 5645051 := bstep (se 1 (by rfl) ⟨4233788, by rfl⟩ : syracuseStep 5645051 = 8467577) B8467577
theorem B2337511 : Blo 287828 2337511 := bstep (se 1 (by rfl) ⟨1753133, by rfl⟩ : syracuseStep 2337511 = 3506267) B3506267
theorem B14530765 : Blo 287828 14530765 := bstep (se 3 (by rfl) ⟨2724518, by rfl⟩ : syracuseStep 14530765 = 5449037) B5449037
theorem B1391035 : Blo 287828 1391035 := bstep (se 1 (by rfl) ⟨1043276, by rfl⟩ : syracuseStep 1391035 = 2086553) B2086553
theorem B2802367 : Blo 287828 2802367 := bstep (se 1 (by rfl) ⟨2101775, by rfl⟩ : syracuseStep 2802367 = 4203551) B4203551
theorem B204161917 : Blo 287828 204161917 := bstep (se 3 (by rfl) ⟨38280359, by rfl⟩ : syracuseStep 204161917 = 76560719) B76560719
theorem B1788497 : Blo 287828 1788497 := bstep (se 2 (by rfl) ⟨670686, by rfl⟩ : syracuseStep 1788497 = 1341373) B1341373
theorem B854870759 : Blo 287828 854870759 := bstep (se 1 (by rfl) ⟨641153069, by rfl⟩ : syracuseStep 854870759 = 1282306139) B1282306139
theorem B1462697 : Blo 287828 1462697 := bstep (se 2 (by rfl) ⟨548511, by rfl⟩ : syracuseStep 1462697 = 1097023) B1097023
theorem B547327 : Blo 287828 547327 := bstep (se 1 (by rfl) ⟨410495, by rfl⟩ : syracuseStep 547327 = 820991) B820991
theorem B21224425 : Blo 287828 21224425 := bstep (se 2 (by rfl) ⟨7959159, by rfl⟩ : syracuseStep 21224425 = 15918319) B15918319
theorem B2481151 : Blo 287828 2481151 := bstep (se 1 (by rfl) ⟨1860863, by rfl⟩ : syracuseStep 2481151 = 3721727) B3721727
theorem B523267451 : Blo 287828 523267451 := bstep (se 1 (by rfl) ⟨392450588, by rfl⟩ : syracuseStep 523267451 = 784901177) B784901177
theorem B978857 : Blo 287828 978857 := bstep (se 2 (by rfl) ⟨367071, by rfl⟩ : syracuseStep 978857 = 734143) B734143
theorem B2224361 : Blo 287828 2224361 := bstep (se 2 (by rfl) ⟨834135, by rfl⟩ : syracuseStep 2224361 = 1668271) B1668271
theorem B1242337 : Blo 287828 1242337 := bstep (se 2 (by rfl) ⟨465876, by rfl⟩ : syracuseStep 1242337 = 931753) B931753
theorem B11859281 : Blo 287828 11859281 := bstep (se 2 (by rfl) ⟨4447230, by rfl⟩ : syracuseStep 11859281 = 8894461) B8894461
theorem B1768175 : Blo 287828 1768175 := bstep (se 1 (by rfl) ⟨1326131, by rfl⟩ : syracuseStep 1768175 = 2652263) B2652263
theorem B160037963 : Blo 287828 160037963 := bstep (se 1 (by rfl) ⟨120028472, by rfl⟩ : syracuseStep 160037963 = 240056945) B240056945
theorem B3736489 : Blo 287828 3736489 := bstep (se 2 (by rfl) ⟨1401183, by rfl⟩ : syracuseStep 3736489 = 2802367) B2802367
theorem B3116681 : Blo 287828 3116681 := bstep (se 2 (by rfl) ⟨1168755, by rfl⟩ : syracuseStep 3116681 = 2337511) B2337511
theorem B1482907 : Blo 287828 1482907 := bstep (se 1 (by rfl) ⟨1112180, by rfl⟩ : syracuseStep 1482907 = 2224361) B2224361
theorem B19374353 : Blo 287828 19374353 := bstep (se 2 (by rfl) ⟨7265382, by rfl⟩ : syracuseStep 19374353 = 14530765) B14530765
theorem B729769 : Blo 287828 729769 := bstep (se 2 (by rfl) ⟨273663, by rfl⟩ : syracuseStep 729769 = 547327) B547327
theorem B7906187 : Blo 287828 7906187 := bstep (se 1 (by rfl) ⟨5929640, by rfl⟩ : syracuseStep 7906187 = 11859281) B11859281
theorem B272215889 : Blo 287828 272215889 := bstep (se 2 (by rfl) ⟨102080958, by rfl⟩ : syracuseStep 272215889 = 204161917) B204161917
theorem B1192331 : Blo 287828 1192331 := bstep (se 1 (by rfl) ⟨894248, by rfl⟩ : syracuseStep 1192331 = 1788497) B1788497
theorem B569913839 : Blo 287828 569913839 := bstep (se 1 (by rfl) ⟨427435379, by rfl⟩ : syracuseStep 569913839 = 854870759) B854870759
theorem B1656449 : Blo 287828 1656449 := bstep (se 2 (by rfl) ⟨621168, by rfl⟩ : syracuseStep 1656449 = 1242337) B1242337
theorem B1854713 : Blo 287828 1854713 := bstep (se 2 (by rfl) ⟨695517, by rfl⟩ : syracuseStep 1854713 = 1391035) B1391035
theorem B28299233 : Blo 287828 28299233 := bstep (se 2 (by rfl) ⟨10612212, by rfl⟩ : syracuseStep 28299233 = 21224425) B21224425
theorem B13720013 : Blo 287828 13720013 := bstep (se 3 (by rfl) ⟨2572502, by rfl⟩ : syracuseStep 13720013 = 5145005) B5145005
theorem B975131 : Blo 287828 975131 := bstep (se 1 (by rfl) ⟨731348, by rfl⟩ : syracuseStep 975131 = 1462697) B1462697
theorem B549355 : Blo 287828 549355 := bstep (se 1 (by rfl) ⟨412016, by rfl⟩ : syracuseStep 549355 = 824033) B824033
theorem B50816585 : Blo 287828 50816585 := bstep (se 2 (by rfl) ⟨19056219, by rfl⟩ : syracuseStep 50816585 = 38112439) B38112439
theorem B14117327 : Blo 287828 14117327 := bstep (se 1 (by rfl) ⟨10587995, by rfl⟩ : syracuseStep 14117327 = 21175991) B21175991
theorem B3763367 : Blo 287828 3763367 := bstep (se 1 (by rfl) ⟨2822525, by rfl⟩ : syracuseStep 3763367 = 5645051) B5645051
theorem B348844967 : Blo 287828 348844967 := bstep (se 1 (by rfl) ⟨261633725, by rfl⟩ : syracuseStep 348844967 = 523267451) B523267451
theorem B652571 : Blo 287828 652571 := bstep (se 1 (by rfl) ⟨489428, by rfl⟩ : syracuseStep 652571 = 978857) B978857
theorem B3308201 : Blo 287828 3308201 := bstep (se 2 (by rfl) ⟨1240575, by rfl⟩ : syracuseStep 3308201 = 2481151) B2481151
theorem B1178783 : Blo 287828 1178783 := bstep (se 1 (by rfl) ⟨884087, by rfl⟩ : syracuseStep 1178783 = 1768175) B1768175
theorem B106691975 : Blo 287828 106691975 := bstep (se 1 (by rfl) ⟨80018981, by rfl⟩ : syracuseStep 106691975 = 160037963) B160037963
theorem B4981985 : Blo 287828 4981985 := bstep (se 2 (by rfl) ⟨1868244, by rfl⟩ : syracuseStep 4981985 = 3736489) B3736489
theorem B9146675 : Blo 287828 9146675 := bstep (se 1 (by rfl) ⟨6860006, by rfl⟩ : syracuseStep 9146675 = 13720013) B13720013
theorem B12916235 : Blo 287828 12916235 := bstep (se 1 (by rfl) ⟨9687176, by rfl⟩ : syracuseStep 12916235 = 19374353) B19374353
theorem B9411551 : Blo 287828 9411551 := bstep (se 1 (by rfl) ⟨7058663, by rfl⟩ : syracuseStep 9411551 = 14117327) B14117327
theorem B181477259 : Blo 287828 181477259 := bstep (se 1 (by rfl) ⟨136107944, by rfl⟩ : syracuseStep 181477259 = 272215889) B272215889
theorem B794887 : Blo 287828 794887 := bstep (se 1 (by rfl) ⟨596165, by rfl⟩ : syracuseStep 794887 = 1192331) B1192331
theorem B232563311 : Blo 287828 232563311 := bstep (se 1 (by rfl) ⟨174422483, by rfl⟩ : syracuseStep 232563311 = 348844967) B348844967
theorem B435047 : Blo 287828 435047 := bstep (se 1 (by rfl) ⟨326285, by rfl⟩ : syracuseStep 435047 = 652571) B652571
theorem B2205467 : Blo 287828 2205467 := bstep (se 1 (by rfl) ⟨1654100, by rfl⟩ : syracuseStep 2205467 = 3308201) B3308201
theorem B1977209 : Blo 287828 1977209 := bstep (se 2 (by rfl) ⟨741453, by rfl⟩ : syracuseStep 1977209 = 1482907) B1482907
theorem B732473 : Blo 287828 732473 := bstep (se 2 (by rfl) ⟨274677, by rfl⟩ : syracuseStep 732473 = 549355) B549355
theorem B2077787 : Blo 287828 2077787 := bstep (se 1 (by rfl) ⟨1558340, by rfl⟩ : syracuseStep 2077787 = 3116681) B3116681
theorem B135510893 : Blo 287828 135510893 := bstep (se 3 (by rfl) ⟨25408292, by rfl⟩ : syracuseStep 135510893 = 50816585) B50816585
theorem B2508911 : Blo 287828 2508911 := bstep (se 1 (by rfl) ⟨1881683, by rfl⟩ : syracuseStep 2508911 = 3763367) B3763367
theorem B71127983 : Blo 287828 71127983 := bstep (se 1 (by rfl) ⟨53345987, by rfl⟩ : syracuseStep 71127983 = 106691975) B106691975
theorem B973025 : Blo 287828 973025 := bstep (se 2 (by rfl) ⟨364884, by rfl⟩ : syracuseStep 973025 = 729769) B729769
theorem B1104299 : Blo 287828 1104299 := bstep (se 1 (by rfl) ⟨828224, by rfl⟩ : syracuseStep 1104299 = 1656449) B1656449
theorem B1236475 : Blo 287828 1236475 := bstep (se 1 (by rfl) ⟨927356, by rfl⟩ : syracuseStep 1236475 = 1854713) B1854713
theorem B18866155 : Blo 287828 18866155 := bstep (se 1 (by rfl) ⟨14149616, by rfl⟩ : syracuseStep 18866155 = 28299233) B28299233
theorem B650087 : Blo 287828 650087 := bstep (se 1 (by rfl) ⟨487565, by rfl⟩ : syracuseStep 650087 = 975131) B975131
theorem B5270791 : Blo 287828 5270791 := bstep (se 1 (by rfl) ⟨3953093, by rfl⟩ : syracuseStep 5270791 = 7906187) B7906187
theorem B379942559 : Blo 287828 379942559 := bstep (se 1 (by rfl) ⟨284956919, by rfl⟩ : syracuseStep 379942559 = 569913839) B569913839
theorem B785855 : Blo 287828 785855 := bstep (se 1 (by rfl) ⟨589391, by rfl⟩ : syracuseStep 785855 = 1178783) B1178783
theorem B1672607 : Blo 287828 1672607 := bstep (se 1 (by rfl) ⟨1254455, by rfl⟩ : syracuseStep 1672607 = 2508911) B2508911
theorem B6097783 : Blo 287828 6097783 := bstep (se 1 (by rfl) ⟨4573337, by rfl⟩ : syracuseStep 6097783 = 9146675) B9146675
theorem B47418655 : Blo 287828 47418655 := bstep (se 1 (by rfl) ⟨35563991, by rfl⟩ : syracuseStep 47418655 = 71127983) B71127983
theorem B120984839 : Blo 287828 120984839 := bstep (se 1 (by rfl) ⟨90738629, by rfl⟩ : syracuseStep 120984839 = 181477259) B181477259
theorem B433391 : Blo 287828 433391 := bstep (se 1 (by rfl) ⟨325043, by rfl⟩ : syracuseStep 433391 = 650087) B650087
theorem B1318139 : Blo 287828 1318139 := bstep (se 1 (by rfl) ⟨988604, by rfl⟩ : syracuseStep 1318139 = 1977209) B1977209
theorem B1385191 : Blo 287828 1385191 := bstep (se 1 (by rfl) ⟨1038893, by rfl⟩ : syracuseStep 1385191 = 2077787) B2077787
theorem B1648633 : Blo 287828 1648633 := bstep (se 2 (by rfl) ⟨618237, by rfl⟩ : syracuseStep 1648633 = 1236475) B1236475
theorem B3321323 : Blo 287828 3321323 := bstep (se 1 (by rfl) ⟨2490992, by rfl⟩ : syracuseStep 3321323 = 4981985) B4981985
theorem B4239397 : Blo 287828 4239397 := bstep (se 4 (by rfl) ⟨397443, by rfl⟩ : syracuseStep 4239397 = 794887) B794887
theorem B736199 : Blo 287828 736199 := bstep (se 1 (by rfl) ⟨552149, by rfl⟩ : syracuseStep 736199 = 1104299) B1104299
theorem B7027721 : Blo 287828 7027721 := bstep (se 2 (by rfl) ⟨2635395, by rfl⟩ : syracuseStep 7027721 = 5270791) B5270791
theorem B6274367 : Blo 287828 6274367 := bstep (se 1 (by rfl) ⟨4705775, by rfl⟩ : syracuseStep 6274367 = 9411551) B9411551
theorem B155042207 : Blo 287828 155042207 := bstep (se 1 (by rfl) ⟨116281655, by rfl⟩ : syracuseStep 155042207 = 232563311) B232563311
theorem B25154873 : Blo 287828 25154873 := bstep (se 2 (by rfl) ⟨9433077, by rfl⟩ : syracuseStep 25154873 = 18866155) B18866155
theorem B8610823 : Blo 287828 8610823 := bstep (se 1 (by rfl) ⟨6458117, by rfl⟩ : syracuseStep 8610823 = 12916235) B12916235
theorem B648683 : Blo 287828 648683 := bstep (se 1 (by rfl) ⟨486512, by rfl⟩ : syracuseStep 648683 = 973025) B973025
theorem B290031 : Blo 287828 290031 := bstep (se 1 (by rfl) ⟨217523, by rfl⟩ : syracuseStep 290031 = 435047) B435047
theorem B1470311 : Blo 287828 1470311 := bstep (se 1 (by rfl) ⟨1102733, by rfl⟩ : syracuseStep 1470311 = 2205467) B2205467
theorem B488315 : Blo 287828 488315 := bstep (se 1 (by rfl) ⟨366236, by rfl⟩ : syracuseStep 488315 = 732473) B732473
theorem B253295039 : Blo 287828 253295039 := bstep (se 1 (by rfl) ⟨189971279, by rfl⟩ : syracuseStep 253295039 = 379942559) B379942559
theorem B90340595 : Blo 287828 90340595 := bstep (se 1 (by rfl) ⟨67755446, by rfl⟩ : syracuseStep 90340595 = 135510893) B135510893
theorem B523903 : Blo 287828 523903 := bstep (se 1 (by rfl) ⟨392927, by rfl⟩ : syracuseStep 523903 = 785855) B785855
theorem B22610117 : Blo 287828 22610117 := bstep (se 4 (by rfl) ⟨2119698, by rfl⟩ : syracuseStep 22610117 = 4239397) B4239397
theorem B2198177 : Blo 287828 2198177 := bstep (se 2 (by rfl) ⟨824316, by rfl⟩ : syracuseStep 2198177 = 1648633) B1648633
theorem B4460285 : Blo 287828 4460285 := bstep (se 3 (by rfl) ⟨836303, by rfl⟩ : syracuseStep 4460285 = 1672607) B1672607
theorem B8130377 : Blo 287828 8130377 := bstep (se 2 (by rfl) ⟨3048891, by rfl⟩ : syracuseStep 8130377 = 6097783) B6097783
theorem B432455 : Blo 287828 432455 := bstep (se 1 (by rfl) ⟨324341, by rfl⟩ : syracuseStep 432455 = 648683) B648683
theorem B168863359 : Blo 287828 168863359 := bstep (se 1 (by rfl) ⟨126647519, by rfl⟩ : syracuseStep 168863359 = 253295039) B253295039
theorem B698537 : Blo 287828 698537 := bstep (se 2 (by rfl) ⟨261951, by rfl⟩ : syracuseStep 698537 = 523903) B523903
theorem B103361471 : Blo 287828 103361471 := bstep (se 1 (by rfl) ⟨77521103, by rfl⟩ : syracuseStep 103361471 = 155042207) B155042207
theorem B11481097 : Blo 287828 11481097 := bstep (se 2 (by rfl) ⟨4305411, by rfl⟩ : syracuseStep 11481097 = 8610823) B8610823
theorem B80656559 : Blo 287828 80656559 := bstep (se 1 (by rfl) ⟨60492419, by rfl⟩ : syracuseStep 80656559 = 120984839) B120984839
theorem B7387685 : Blo 287828 7387685 := bstep (se 4 (by rfl) ⟨692595, by rfl⟩ : syracuseStep 7387685 = 1385191) B1385191
theorem B63224873 : Blo 287828 63224873 := bstep (se 2 (by rfl) ⟨23709327, by rfl⟩ : syracuseStep 63224873 = 47418655) B47418655
theorem B2214215 : Blo 287828 2214215 := bstep (se 1 (by rfl) ⟨1660661, by rfl⟩ : syracuseStep 2214215 = 3321323) B3321323
theorem B4182911 : Blo 287828 4182911 := bstep (se 1 (by rfl) ⟨3137183, by rfl⟩ : syracuseStep 4182911 = 6274367) B6274367
theorem B16769915 : Blo 287828 16769915 := bstep (se 1 (by rfl) ⟨12577436, by rfl⟩ : syracuseStep 16769915 = 25154873) B25154873
theorem B288927 : Blo 287828 288927 := bstep (se 1 (by rfl) ⟨216695, by rfl⟩ : syracuseStep 288927 = 433391) B433391
theorem B878759 : Blo 287828 878759 := bstep (se 1 (by rfl) ⟨659069, by rfl⟩ : syracuseStep 878759 = 1318139) B1318139
theorem B980207 : Blo 287828 980207 := bstep (se 1 (by rfl) ⟨735155, by rfl⟩ : syracuseStep 980207 = 1470311) B1470311
theorem B325543 : Blo 287828 325543 := bstep (se 1 (by rfl) ⟨244157, by rfl⟩ : syracuseStep 325543 = 488315) B488315
theorem B490799 : Blo 287828 490799 := bstep (se 1 (by rfl) ⟨368099, by rfl⟩ : syracuseStep 490799 = 736199) B736199
theorem B4685147 : Blo 287828 4685147 := bstep (se 1 (by rfl) ⟨3513860, by rfl⟩ : syracuseStep 4685147 = 7027721) B7027721
theorem B60227063 : Blo 287828 60227063 := bstep (se 1 (by rfl) ⟨45170297, by rfl⟩ : syracuseStep 60227063 = 90340595) B90340595
theorem B60293645 : Blo 287828 60293645 := bstep (se 3 (by rfl) ⟨11305058, by rfl⟩ : syracuseStep 60293645 = 22610117) B22610117
theorem B1476143 : Blo 287828 1476143 := bstep (se 1 (by rfl) ⟨1107107, by rfl⟩ : syracuseStep 1476143 = 2214215) B2214215
theorem B225151145 : Blo 287828 225151145 := bstep (se 2 (by rfl) ⟨84431679, by rfl⟩ : syracuseStep 225151145 = 168863359) B168863359
theorem B2788607 : Blo 287828 2788607 := bstep (se 1 (by rfl) ⟨2091455, by rfl⟩ : syracuseStep 2788607 = 4182911) B4182911
theorem B15308129 : Blo 287828 15308129 := bstep (se 2 (by rfl) ⟨5740548, by rfl⟩ : syracuseStep 15308129 = 11481097) B11481097
theorem B11179943 : Blo 287828 11179943 := bstep (se 1 (by rfl) ⟨8384957, by rfl⟩ : syracuseStep 11179943 = 16769915) B16769915
theorem B465691 : Blo 287828 465691 := bstep (se 1 (by rfl) ⟨349268, by rfl⟩ : syracuseStep 465691 = 698537) B698537
theorem B434057 : Blo 287828 434057 := bstep (se 2 (by rfl) ⟨162771, by rfl⟩ : syracuseStep 434057 = 325543) B325543
theorem B4925123 : Blo 287828 4925123 := bstep (se 1 (by rfl) ⟨3693842, by rfl⟩ : syracuseStep 4925123 = 7387685) B7387685
theorem B42149915 : Blo 287828 42149915 := bstep (se 1 (by rfl) ⟨31612436, by rfl⟩ : syracuseStep 42149915 = 63224873) B63224873
theorem B3123431 : Blo 287828 3123431 := bstep (se 1 (by rfl) ⟨2342573, by rfl⟩ : syracuseStep 3123431 = 4685147) B4685147
theorem B40151375 : Blo 287828 40151375 := bstep (se 1 (by rfl) ⟨30113531, by rfl⟩ : syracuseStep 40151375 = 60227063) B60227063
theorem B5420251 : Blo 287828 5420251 := bstep (se 1 (by rfl) ⟨4065188, by rfl⟩ : syracuseStep 5420251 = 8130377) B8130377
theorem B1465451 : Blo 287828 1465451 := bstep (se 1 (by rfl) ⟨1099088, by rfl⟩ : syracuseStep 1465451 = 2198177) B2198177
theorem B2973523 : Blo 287828 2973523 := bstep (se 1 (by rfl) ⟨2230142, by rfl⟩ : syracuseStep 2973523 = 4460285) B4460285
theorem B288303 : Blo 287828 288303 := bstep (se 1 (by rfl) ⟨216227, by rfl⟩ : syracuseStep 288303 = 432455) B432455
theorem B585839 : Blo 287828 585839 := bstep (se 1 (by rfl) ⟨439379, by rfl⟩ : syracuseStep 585839 = 878759) B878759
theorem B68907647 : Blo 287828 68907647 := bstep (se 1 (by rfl) ⟨51680735, by rfl⟩ : syracuseStep 68907647 = 103361471) B103361471
theorem B653471 : Blo 287828 653471 := bstep (se 1 (by rfl) ⟨490103, by rfl⟩ : syracuseStep 653471 = 980207) B980207
theorem B53771039 : Blo 287828 53771039 := bstep (se 1 (by rfl) ⟨40328279, by rfl⟩ : syracuseStep 53771039 = 80656559) B80656559
theorem B327199 : Blo 287828 327199 := bstep (se 1 (by rfl) ⟨245399, by rfl⟩ : syracuseStep 327199 = 490799) B490799
theorem B984095 : Blo 287828 984095 := bstep (se 1 (by rfl) ⟨738071, by rfl⟩ : syracuseStep 984095 = 1476143) B1476143
theorem B3283415 : Blo 287828 3283415 := bstep (se 1 (by rfl) ⟨2462561, by rfl⟩ : syracuseStep 3283415 = 4925123) B4925123
theorem B435647 : Blo 287828 435647 := bstep (se 1 (by rfl) ⟨326735, by rfl⟩ : syracuseStep 435647 = 653471) B653471
theorem B436265 : Blo 287828 436265 := bstep (se 2 (by rfl) ⟨163599, by rfl⟩ : syracuseStep 436265 = 327199) B327199
theorem B2401612213 : Blo 287828 2401612213 := bstep (se 5 (by rfl) ⟨112575572, by rfl⟩ : syracuseStep 2401612213 = 225151145) B225151145
theorem B7453295 : Blo 287828 7453295 := bstep (se 1 (by rfl) ⟨5589971, by rfl⟩ : syracuseStep 7453295 = 11179943) B11179943
theorem B28099943 : Blo 287828 28099943 := bstep (se 1 (by rfl) ⟨21074957, by rfl⟩ : syracuseStep 28099943 = 42149915) B42149915
theorem B2082287 : Blo 287828 2082287 := bstep (se 1 (by rfl) ⟨1561715, by rfl⟩ : syracuseStep 2082287 = 3123431) B3123431
theorem B7227001 : Blo 287828 7227001 := bstep (se 2 (by rfl) ⟨2710125, by rfl⟩ : syracuseStep 7227001 = 5420251) B5420251
theorem B1562237 : Blo 287828 1562237 := bstep (se 3 (by rfl) ⟨292919, by rfl⟩ : syracuseStep 1562237 = 585839) B585839
theorem B40195763 : Blo 287828 40195763 := bstep (se 1 (by rfl) ⟨30146822, by rfl⟩ : syracuseStep 40195763 = 60293645) B60293645
theorem B1859071 : Blo 287828 1859071 := bstep (se 1 (by rfl) ⟨1394303, by rfl⟩ : syracuseStep 1859071 = 2788607) B2788607
theorem B40821677 : Blo 287828 40821677 := bstep (se 3 (by rfl) ⟨7654064, by rfl⟩ : syracuseStep 40821677 = 15308129) B15308129
theorem B976967 : Blo 287828 976967 := bstep (se 1 (by rfl) ⟨732725, by rfl⟩ : syracuseStep 976967 = 1465451) B1465451
theorem B289371 : Blo 287828 289371 := bstep (se 1 (by rfl) ⟨217028, by rfl⟩ : syracuseStep 289371 = 434057) B434057
theorem B26767583 : Blo 287828 26767583 := bstep (se 1 (by rfl) ⟨20075687, by rfl⟩ : syracuseStep 26767583 = 40151375) B40151375
theorem B45938431 : Blo 287828 45938431 := bstep (se 1 (by rfl) ⟨34453823, by rfl⟩ : syracuseStep 45938431 = 68907647) B68907647
theorem B620921 : Blo 287828 620921 := bstep (se 2 (by rfl) ⟨232845, by rfl⟩ : syracuseStep 620921 = 465691) B465691
theorem B35847359 : Blo 287828 35847359 := bstep (se 1 (by rfl) ⟨26885519, by rfl⟩ : syracuseStep 35847359 = 53771039) B53771039
theorem B3964697 : Blo 287828 3964697 := bstep (se 2 (by rfl) ⟨1486761, by rfl⟩ : syracuseStep 3964697 = 2973523) B2973523
theorem B656063 : Blo 287828 656063 := bstep (se 1 (by rfl) ⟨492047, by rfl⟩ : syracuseStep 656063 = 984095) B984095
theorem B61251241 : Blo 287828 61251241 := bstep (se 2 (by rfl) ⟨22969215, by rfl⟩ : syracuseStep 61251241 = 45938431) B45938431
theorem B38544005 : Blo 287828 38544005 := bstep (se 4 (by rfl) ⟨3613500, by rfl⟩ : syracuseStep 38544005 = 7227001) B7227001
theorem B23898239 : Blo 287828 23898239 := bstep (se 1 (by rfl) ⟨17923679, by rfl⟩ : syracuseStep 23898239 = 35847359) B35847359
theorem B1388191 : Blo 287828 1388191 := bstep (se 1 (by rfl) ⟨1041143, by rfl⟩ : syracuseStep 1388191 = 2082287) B2082287
theorem B27214451 : Blo 287828 27214451 := bstep (se 1 (by rfl) ⟨20410838, by rfl⟩ : syracuseStep 27214451 = 40821677) B40821677
theorem B17845055 : Blo 287828 17845055 := bstep (se 1 (by rfl) ⟨13383791, by rfl⟩ : syracuseStep 17845055 = 26767583) B26767583
theorem B413947 : Blo 287828 413947 := bstep (se 1 (by rfl) ⟨310460, by rfl⟩ : syracuseStep 413947 = 620921) B620921
theorem B4968863 : Blo 287828 4968863 := bstep (se 1 (by rfl) ⟨3726647, by rfl⟩ : syracuseStep 4968863 = 7453295) B7453295
theorem B2478761 : Blo 287828 2478761 := bstep (se 2 (by rfl) ⟨929535, by rfl⟩ : syracuseStep 2478761 = 1859071) B1859071
theorem B2643131 : Blo 287828 2643131 := bstep (se 1 (by rfl) ⟨1982348, by rfl⟩ : syracuseStep 2643131 = 3964697) B3964697
theorem B18733295 : Blo 287828 18733295 := bstep (se 1 (by rfl) ⟨14049971, by rfl⟩ : syracuseStep 18733295 = 28099943) B28099943
theorem B1041491 : Blo 287828 1041491 := bstep (se 1 (by rfl) ⟨781118, by rfl⟩ : syracuseStep 1041491 = 1562237) B1562237
theorem B26797175 : Blo 287828 26797175 := bstep (se 1 (by rfl) ⟨20097881, by rfl⟩ : syracuseStep 26797175 = 40195763) B40195763
theorem B2188943 : Blo 287828 2188943 := bstep (se 1 (by rfl) ⟨1641707, by rfl⟩ : syracuseStep 2188943 = 3283415) B3283415
theorem B3202149617 : Blo 287828 3202149617 := bstep (se 2 (by rfl) ⟨1200806106, by rfl⟩ : syracuseStep 3202149617 = 2401612213) B2401612213
theorem B290431 : Blo 287828 290431 := bstep (se 1 (by rfl) ⟨217823, by rfl⟩ : syracuseStep 290431 = 435647) B435647
theorem B290843 : Blo 287828 290843 := bstep (se 1 (by rfl) ⟨218132, by rfl⟩ : syracuseStep 290843 = 436265) B436265
theorem B651311 : Blo 287828 651311 := bstep (se 1 (by rfl) ⟨488483, by rfl⟩ : syracuseStep 651311 = 976967) B976967
theorem B11896703 : Blo 287828 11896703 := bstep (se 1 (by rfl) ⟨8922527, by rfl⟩ : syracuseStep 11896703 = 17845055) B17845055
theorem B3312575 : Blo 287828 3312575 := bstep (se 1 (by rfl) ⟨2484431, by rfl⟩ : syracuseStep 3312575 = 4968863) B4968863
theorem B12488863 : Blo 287828 12488863 := bstep (se 1 (by rfl) ⟨9366647, by rfl⟩ : syracuseStep 12488863 = 18733295) B18733295
theorem B25696003 : Blo 287828 25696003 := bstep (se 1 (by rfl) ⟨19272002, by rfl⟩ : syracuseStep 25696003 = 38544005) B38544005
theorem B694327 : Blo 287828 694327 := bstep (se 1 (by rfl) ⟨520745, by rfl⟩ : syracuseStep 694327 = 1041491) B1041491
theorem B17864783 : Blo 287828 17864783 := bstep (se 1 (by rfl) ⟨13398587, by rfl⟩ : syracuseStep 17864783 = 26797175) B26797175
theorem B15932159 : Blo 287828 15932159 := bstep (se 1 (by rfl) ⟨11949119, by rfl⟩ : syracuseStep 15932159 = 23898239) B23898239
theorem B434207 : Blo 287828 434207 := bstep (se 1 (by rfl) ⟨325655, by rfl⟩ : syracuseStep 434207 = 651311) B651311
theorem B81668321 : Blo 287828 81668321 := bstep (se 2 (by rfl) ⟨30625620, by rfl⟩ : syracuseStep 81668321 = 61251241) B61251241
theorem B437375 : Blo 287828 437375 := bstep (se 1 (by rfl) ⟨328031, by rfl⟩ : syracuseStep 437375 = 656063) B656063
theorem B1652507 : Blo 287828 1652507 := bstep (se 1 (by rfl) ⟨1239380, by rfl⟩ : syracuseStep 1652507 = 2478761) B2478761
theorem B1850921 : Blo 287828 1850921 := bstep (se 2 (by rfl) ⟨694095, by rfl⟩ : syracuseStep 1850921 = 1388191) B1388191
theorem B1459295 : Blo 287828 1459295 := bstep (se 1 (by rfl) ⟨1094471, by rfl⟩ : syracuseStep 1459295 = 2188943) B2188943
theorem B18142967 : Blo 287828 18142967 := bstep (se 1 (by rfl) ⟨13607225, by rfl⟩ : syracuseStep 18142967 = 27214451) B27214451
theorem B1762087 : Blo 287828 1762087 := bstep (se 1 (by rfl) ⟨1321565, by rfl⟩ : syracuseStep 1762087 = 2643131) B2643131
theorem B551929 : Blo 287828 551929 := bstep (se 2 (by rfl) ⟨206973, by rfl⟩ : syracuseStep 551929 = 413947) B413947
theorem B2134766411 : Blo 287828 2134766411 := bstep (se 1 (by rfl) ⟨1601074808, by rfl⟩ : syracuseStep 2134766411 = 3202149617) B3202149617
theorem B7931135 : Blo 287828 7931135 := bstep (se 1 (by rfl) ⟨5948351, by rfl⟩ : syracuseStep 7931135 = 11896703) B11896703
theorem B10621439 : Blo 287828 10621439 := bstep (se 1 (by rfl) ⟨7966079, by rfl⟩ : syracuseStep 10621439 = 15932159) B15932159
theorem B16651817 : Blo 287828 16651817 := bstep (se 2 (by rfl) ⟨6244431, by rfl⟩ : syracuseStep 16651817 = 12488863) B12488863
theorem B925769 : Blo 287828 925769 := bstep (se 2 (by rfl) ⟨347163, by rfl⟩ : syracuseStep 925769 = 694327) B694327
theorem B2208383 : Blo 287828 2208383 := bstep (se 1 (by rfl) ⟨1656287, by rfl⟩ : syracuseStep 2208383 = 3312575) B3312575
theorem B735905 : Blo 287828 735905 := bstep (se 2 (by rfl) ⟨275964, by rfl⟩ : syracuseStep 735905 = 551929) B551929
theorem B11909855 : Blo 287828 11909855 := bstep (se 1 (by rfl) ⟨8932391, by rfl⟩ : syracuseStep 11909855 = 17864783) B17864783
theorem B48381245 : Blo 287828 48381245 := bstep (se 3 (by rfl) ⟨9071483, by rfl⟩ : syracuseStep 48381245 = 18142967) B18142967
theorem B54445547 : Blo 287828 54445547 := bstep (se 1 (by rfl) ⟨40834160, by rfl⟩ : syracuseStep 54445547 = 81668321) B81668321
theorem B34261337 : Blo 287828 34261337 := bstep (se 2 (by rfl) ⟨12848001, by rfl⟩ : syracuseStep 34261337 = 25696003) B25696003
theorem B1101671 : Blo 287828 1101671 := bstep (se 1 (by rfl) ⟨826253, by rfl⟩ : syracuseStep 1101671 = 1652507) B1652507
theorem B1233947 : Blo 287828 1233947 := bstep (se 1 (by rfl) ⟨925460, by rfl⟩ : syracuseStep 1233947 = 1850921) B1850921
theorem B972863 : Blo 287828 972863 := bstep (se 1 (by rfl) ⟨729647, by rfl⟩ : syracuseStep 972863 = 1459295) B1459295
theorem B2349449 : Blo 287828 2349449 := bstep (se 2 (by rfl) ⟨881043, by rfl⟩ : syracuseStep 2349449 = 1762087) B1762087
theorem B289471 : Blo 287828 289471 := bstep (se 1 (by rfl) ⟨217103, by rfl⟩ : syracuseStep 289471 = 434207) B434207
theorem B291583 : Blo 287828 291583 := bstep (se 1 (by rfl) ⟨218687, by rfl⟩ : syracuseStep 291583 = 437375) B437375
theorem B1423177607 : Blo 287828 1423177607 := bstep (se 1 (by rfl) ⟨1067383205, by rfl⟩ : syracuseStep 1423177607 = 2134766411) B2134766411
theorem B7080959 : Blo 287828 7080959 := bstep (se 1 (by rfl) ⟨5310719, by rfl⟩ : syracuseStep 7080959 = 10621439) B10621439
theorem B822631 : Blo 287828 822631 := bstep (se 1 (by rfl) ⟨616973, by rfl⟩ : syracuseStep 822631 = 1233947) B1233947
theorem B91363565 : Blo 287828 91363565 := bstep (se 3 (by rfl) ⟨17130668, by rfl⟩ : syracuseStep 91363565 = 34261337) B34261337
theorem B7939903 : Blo 287828 7939903 := bstep (se 1 (by rfl) ⟨5954927, by rfl⟩ : syracuseStep 7939903 = 11909855) B11909855
theorem B32254163 : Blo 287828 32254163 := bstep (se 1 (by rfl) ⟨24190622, by rfl⟩ : syracuseStep 32254163 = 48381245) B48381245
theorem B734447 : Blo 287828 734447 := bstep (se 1 (by rfl) ⟨550835, by rfl⟩ : syracuseStep 734447 = 1101671) B1101671
theorem B21149693 : Blo 287828 21149693 := bstep (se 3 (by rfl) ⟨3965567, by rfl⟩ : syracuseStep 21149693 = 7931135) B7931135
theorem B948785071 : Blo 287828 948785071 := bstep (se 1 (by rfl) ⟨711588803, by rfl⟩ : syracuseStep 948785071 = 1423177607) B1423177607
theorem B36297031 : Blo 287828 36297031 := bstep (se 1 (by rfl) ⟨27222773, by rfl⟩ : syracuseStep 36297031 = 54445547) B54445547
theorem B11101211 : Blo 287828 11101211 := bstep (se 1 (by rfl) ⟨8325908, by rfl⟩ : syracuseStep 11101211 = 16651817) B16651817
theorem B648575 : Blo 287828 648575 := bstep (se 1 (by rfl) ⟨486431, by rfl⟩ : syracuseStep 648575 = 972863) B972863
theorem B1566299 : Blo 287828 1566299 := bstep (se 1 (by rfl) ⟨1174724, by rfl⟩ : syracuseStep 1566299 = 2349449) B2349449
theorem B617179 : Blo 287828 617179 := bstep (se 1 (by rfl) ⟨462884, by rfl⟩ : syracuseStep 617179 = 925769) B925769
theorem B1472255 : Blo 287828 1472255 := bstep (se 1 (by rfl) ⟨1104191, by rfl⟩ : syracuseStep 1472255 = 2208383) B2208383
theorem B490603 : Blo 287828 490603 := bstep (se 1 (by rfl) ⟨367952, by rfl⟩ : syracuseStep 490603 = 735905) B735905
theorem B4720639 : Blo 287828 4720639 := bstep (se 1 (by rfl) ⟨3540479, by rfl⟩ : syracuseStep 4720639 = 7080959) B7080959
theorem B10586537 : Blo 287828 10586537 := bstep (se 2 (by rfl) ⟨3969951, by rfl⟩ : syracuseStep 10586537 = 7939903) B7939903
theorem B822905 : Blo 287828 822905 := bstep (se 2 (by rfl) ⟨308589, by rfl⟩ : syracuseStep 822905 = 617179) B617179
theorem B1265046761 : Blo 287828 1265046761 := bstep (se 2 (by rfl) ⟨474392535, by rfl⟩ : syracuseStep 1265046761 = 948785071) B948785071
theorem B432383 : Blo 287828 432383 := bstep (se 1 (by rfl) ⟨324287, by rfl⟩ : syracuseStep 432383 = 648575) B648575
theorem B21502775 : Blo 287828 21502775 := bstep (se 1 (by rfl) ⟨16127081, by rfl⟩ : syracuseStep 21502775 = 32254163) B32254163
theorem B14099795 : Blo 287828 14099795 := bstep (se 1 (by rfl) ⟨10574846, by rfl⟩ : syracuseStep 14099795 = 21149693) B21149693
theorem B1096841 : Blo 287828 1096841 := bstep (se 2 (by rfl) ⟨411315, by rfl⟩ : syracuseStep 1096841 = 822631) B822631
theorem B60909043 : Blo 287828 60909043 := bstep (se 1 (by rfl) ⟨45681782, by rfl⟩ : syracuseStep 60909043 = 91363565) B91363565
theorem B7400807 : Blo 287828 7400807 := bstep (se 1 (by rfl) ⟨5550605, by rfl⟩ : syracuseStep 7400807 = 11101211) B11101211
theorem B1044199 : Blo 287828 1044199 := bstep (se 1 (by rfl) ⟨783149, by rfl⟩ : syracuseStep 1044199 = 1566299) B1566299
theorem B48396041 : Blo 287828 48396041 := bstep (se 2 (by rfl) ⟨18148515, by rfl⟩ : syracuseStep 48396041 = 36297031) B36297031
theorem B489631 : Blo 287828 489631 := bstep (se 1 (by rfl) ⟨367223, by rfl⟩ : syracuseStep 489631 = 734447) B734447
theorem B981503 : Blo 287828 981503 := bstep (se 1 (by rfl) ⟨736127, by rfl⟩ : syracuseStep 981503 = 1472255) B1472255
theorem B654137 : Blo 287828 654137 := bstep (se 2 (by rfl) ⟨245301, by rfl⟩ : syracuseStep 654137 = 490603) B490603
theorem B6294185 : Blo 287828 6294185 := bstep (se 2 (by rfl) ⟨2360319, by rfl⟩ : syracuseStep 6294185 = 4720639) B4720639
theorem B436091 : Blo 287828 436091 := bstep (se 1 (by rfl) ⟨327068, by rfl⟩ : syracuseStep 436091 = 654137) B654137
theorem B731227 : Blo 287828 731227 := bstep (se 1 (by rfl) ⟨548420, by rfl⟩ : syracuseStep 731227 = 1096841) B1096841
theorem B7057691 : Blo 287828 7057691 := bstep (se 1 (by rfl) ⟨5293268, by rfl⟩ : syracuseStep 7057691 = 10586537) B10586537
theorem B81212057 : Blo 287828 81212057 := bstep (se 2 (by rfl) ⟨30454521, by rfl⟩ : syracuseStep 81212057 = 60909043) B60909043
theorem B843364507 : Blo 287828 843364507 := bstep (se 1 (by rfl) ⟨632523380, by rfl⟩ : syracuseStep 843364507 = 1265046761) B1265046761
theorem B14335183 : Blo 287828 14335183 := bstep (se 1 (by rfl) ⟨10751387, by rfl⟩ : syracuseStep 14335183 = 21502775) B21502775
theorem B1392265 : Blo 287828 1392265 := bstep (se 2 (by rfl) ⟨522099, by rfl⟩ : syracuseStep 1392265 = 1044199) B1044199
theorem B4933871 : Blo 287828 4933871 := bstep (se 1 (by rfl) ⟨3700403, by rfl⟩ : syracuseStep 4933871 = 7400807) B7400807
theorem B32264027 : Blo 287828 32264027 := bstep (se 1 (by rfl) ⟨24198020, by rfl⟩ : syracuseStep 32264027 = 48396041) B48396041
theorem B548603 : Blo 287828 548603 := bstep (se 1 (by rfl) ⟨411452, by rfl⟩ : syracuseStep 548603 = 822905) B822905
theorem B288255 : Blo 287828 288255 := bstep (se 1 (by rfl) ⟨216191, by rfl⟩ : syracuseStep 288255 = 432383) B432383
theorem B9399863 : Blo 287828 9399863 := bstep (se 1 (by rfl) ⟨7049897, by rfl⟩ : syracuseStep 9399863 = 14099795) B14099795
theorem B652841 : Blo 287828 652841 := bstep (se 2 (by rfl) ⟨244815, by rfl⟩ : syracuseStep 652841 = 489631) B489631
theorem B654335 : Blo 287828 654335 := bstep (se 1 (by rfl) ⟨490751, by rfl⟩ : syracuseStep 654335 = 981503) B981503
theorem B4196123 : Blo 287828 4196123 := bstep (se 1 (by rfl) ⟨3147092, by rfl⟩ : syracuseStep 4196123 = 6294185) B6294185
theorem B365735 : Blo 287828 365735 := bstep (se 1 (by rfl) ⟨274301, by rfl⟩ : syracuseStep 365735 = 548603) B548603
theorem B6266575 : Blo 287828 6266575 := bstep (se 1 (by rfl) ⟨4699931, by rfl⟩ : syracuseStep 6266575 = 9399863) B9399863
theorem B54141371 : Blo 287828 54141371 := bstep (se 1 (by rfl) ⟨40606028, by rfl⟩ : syracuseStep 54141371 = 81212057) B81212057
theorem B435227 : Blo 287828 435227 := bstep (se 1 (by rfl) ⟨326420, by rfl⟩ : syracuseStep 435227 = 652841) B652841
theorem B19113577 : Blo 287828 19113577 := bstep (se 2 (by rfl) ⟨7167591, by rfl⟩ : syracuseStep 19113577 = 14335183) B14335183
theorem B436223 : Blo 287828 436223 := bstep (se 1 (by rfl) ⟨327167, by rfl⟩ : syracuseStep 436223 = 654335) B654335
theorem B3289247 : Blo 287828 3289247 := bstep (se 1 (by rfl) ⟨2466935, by rfl⟩ : syracuseStep 3289247 = 4933871) B4933871
theorem B21509351 : Blo 287828 21509351 := bstep (se 1 (by rfl) ⟨16132013, by rfl⟩ : syracuseStep 21509351 = 32264027) B32264027
theorem B4705127 : Blo 287828 4705127 := bstep (se 1 (by rfl) ⟨3528845, by rfl⟩ : syracuseStep 4705127 = 7057691) B7057691
theorem B1124486009 : Blo 287828 1124486009 := bstep (se 2 (by rfl) ⟨421682253, by rfl⟩ : syracuseStep 1124486009 = 843364507) B843364507
theorem B1856353 : Blo 287828 1856353 := bstep (se 2 (by rfl) ⟨696132, by rfl⟩ : syracuseStep 1856353 = 1392265) B1392265
theorem B974969 : Blo 287828 974969 := bstep (se 2 (by rfl) ⟨365613, by rfl⟩ : syracuseStep 974969 = 731227) B731227
theorem B290727 : Blo 287828 290727 := bstep (se 1 (by rfl) ⟨218045, by rfl⟩ : syracuseStep 290727 = 436091) B436091
theorem B2797415 : Blo 287828 2797415 := bstep (se 1 (by rfl) ⟨2098061, by rfl⟩ : syracuseStep 2797415 = 4196123) B4196123
theorem B36094247 : Blo 287828 36094247 := bstep (se 1 (by rfl) ⟨27070685, by rfl⟩ : syracuseStep 36094247 = 54141371) B54141371
theorem B2475137 : Blo 287828 2475137 := bstep (se 2 (by rfl) ⟨928176, by rfl⟩ : syracuseStep 2475137 = 1856353) B1856353
theorem B14339567 : Blo 287828 14339567 := bstep (se 1 (by rfl) ⟨10754675, by rfl⟩ : syracuseStep 14339567 = 21509351) B21509351
theorem B3136751 : Blo 287828 3136751 := bstep (se 1 (by rfl) ⟨2352563, by rfl⟩ : syracuseStep 3136751 = 4705127) B4705127
theorem B749657339 : Blo 287828 749657339 := bstep (se 1 (by rfl) ⟨562243004, by rfl⟩ : syracuseStep 749657339 = 1124486009) B1124486009
theorem B975293 : Blo 287828 975293 := bstep (se 3 (by rfl) ⟨182867, by rfl⟩ : syracuseStep 975293 = 365735) B365735
theorem B649979 : Blo 287828 649979 := bstep (se 1 (by rfl) ⟨487484, by rfl⟩ : syracuseStep 649979 = 974969) B974969
theorem B290151 : Blo 287828 290151 := bstep (se 1 (by rfl) ⟨217613, by rfl⟩ : syracuseStep 290151 = 435227) B435227
theorem B290815 : Blo 287828 290815 := bstep (se 1 (by rfl) ⟨218111, by rfl⟩ : syracuseStep 290815 = 436223) B436223
theorem B2192831 : Blo 287828 2192831 := bstep (se 1 (by rfl) ⟨1644623, by rfl⟩ : syracuseStep 2192831 = 3289247) B3289247
theorem B101939077 : Blo 287828 101939077 := bstep (se 4 (by rfl) ⟨9556788, by rfl⟩ : syracuseStep 101939077 = 19113577) B19113577
theorem B8355433 : Blo 287828 8355433 := bstep (se 2 (by rfl) ⟨3133287, by rfl⟩ : syracuseStep 8355433 = 6266575) B6266575
theorem B433319 : Blo 287828 433319 := bstep (se 1 (by rfl) ⟨324989, by rfl⟩ : syracuseStep 433319 = 649979) B649979
theorem B24062831 : Blo 287828 24062831 := bstep (se 1 (by rfl) ⟨18047123, by rfl⟩ : syracuseStep 24062831 = 36094247) B36094247
theorem B1650091 : Blo 287828 1650091 := bstep (se 1 (by rfl) ⟨1237568, by rfl⟩ : syracuseStep 1650091 = 2475137) B2475137
theorem B1461887 : Blo 287828 1461887 := bstep (se 1 (by rfl) ⟨1096415, by rfl⟩ : syracuseStep 1461887 = 2192831) B2192831
theorem B9559711 : Blo 287828 9559711 := bstep (se 1 (by rfl) ⟨7169783, by rfl⟩ : syracuseStep 9559711 = 14339567) B14339567
theorem B2091167 : Blo 287828 2091167 := bstep (se 1 (by rfl) ⟨1568375, by rfl⟩ : syracuseStep 2091167 = 3136751) B3136751
theorem B499771559 : Blo 287828 499771559 := bstep (se 1 (by rfl) ⟨374828669, by rfl⟩ : syracuseStep 499771559 = 749657339) B749657339
theorem B650195 : Blo 287828 650195 := bstep (se 1 (by rfl) ⟨487646, by rfl⟩ : syracuseStep 650195 = 975293) B975293
theorem B135918769 : Blo 287828 135918769 := bstep (se 2 (by rfl) ⟨50969538, by rfl⟩ : syracuseStep 135918769 = 101939077) B101939077
theorem B1864943 : Blo 287828 1864943 := bstep (se 1 (by rfl) ⟨1398707, by rfl⟩ : syracuseStep 1864943 = 2797415) B2797415
theorem B11140577 : Blo 287828 11140577 := bstep (se 2 (by rfl) ⟨4177716, by rfl⟩ : syracuseStep 11140577 = 8355433) B8355433
theorem B2200121 : Blo 287828 2200121 := bstep (se 2 (by rfl) ⟨825045, by rfl⟩ : syracuseStep 2200121 = 1650091) B1650091
theorem B433463 : Blo 287828 433463 := bstep (se 1 (by rfl) ⟨325097, by rfl⟩ : syracuseStep 433463 = 650195) B650195
theorem B1394111 : Blo 287828 1394111 := bstep (se 1 (by rfl) ⟨1045583, by rfl⟩ : syracuseStep 1394111 = 2091167) B2091167
theorem B181225025 : Blo 287828 181225025 := bstep (se 2 (by rfl) ⟨67959384, by rfl⟩ : syracuseStep 181225025 = 135918769) B135918769
theorem B16041887 : Blo 287828 16041887 := bstep (se 1 (by rfl) ⟨12031415, by rfl⟩ : syracuseStep 16041887 = 24062831) B24062831
theorem B7427051 : Blo 287828 7427051 := bstep (se 1 (by rfl) ⟨5570288, by rfl⟩ : syracuseStep 7427051 = 11140577) B11140577
theorem B974591 : Blo 287828 974591 := bstep (se 1 (by rfl) ⟨730943, by rfl⟩ : syracuseStep 974591 = 1461887) B1461887
theorem B288879 : Blo 287828 288879 := bstep (se 1 (by rfl) ⟨216659, by rfl⟩ : syracuseStep 288879 = 433319) B433319
theorem B333181039 : Blo 287828 333181039 := bstep (se 1 (by rfl) ⟨249885779, by rfl⟩ : syracuseStep 333181039 = 499771559) B499771559
theorem B1243295 : Blo 287828 1243295 := bstep (se 1 (by rfl) ⟨932471, by rfl⟩ : syracuseStep 1243295 = 1864943) B1864943
theorem B12746281 : Blo 287828 12746281 := bstep (se 2 (by rfl) ⟨4779855, by rfl⟩ : syracuseStep 12746281 = 9559711) B9559711
theorem B120816683 : Blo 287828 120816683 := bstep (se 1 (by rfl) ⟨90612512, by rfl⟩ : syracuseStep 120816683 = 181225025) B181225025
theorem B4951367 : Blo 287828 4951367 := bstep (se 1 (by rfl) ⟨3713525, by rfl⟩ : syracuseStep 4951367 = 7427051) B7427051
theorem B444241385 : Blo 287828 444241385 := bstep (se 2 (by rfl) ⟨166590519, by rfl⟩ : syracuseStep 444241385 = 333181039) B333181039
theorem B828863 : Blo 287828 828863 := bstep (se 1 (by rfl) ⟨621647, by rfl⟩ : syracuseStep 828863 = 1243295) B1243295
theorem B929407 : Blo 287828 929407 := bstep (se 1 (by rfl) ⟨697055, by rfl⟩ : syracuseStep 929407 = 1394111) B1394111
theorem B10694591 : Blo 287828 10694591 := bstep (se 1 (by rfl) ⟨8020943, by rfl⟩ : syracuseStep 10694591 = 16041887) B16041887
theorem B16995041 : Blo 287828 16995041 := bstep (se 2 (by rfl) ⟨6373140, by rfl⟩ : syracuseStep 16995041 = 12746281) B12746281
theorem B1466747 : Blo 287828 1466747 := bstep (se 1 (by rfl) ⟨1100060, by rfl⟩ : syracuseStep 1466747 = 2200121) B2200121
theorem B288975 : Blo 287828 288975 := bstep (se 1 (by rfl) ⟨216731, by rfl⟩ : syracuseStep 288975 = 433463) B433463
theorem B649727 : Blo 287828 649727 := bstep (se 1 (by rfl) ⟨487295, by rfl⟩ : syracuseStep 649727 = 974591) B974591
theorem B80544455 : Blo 287828 80544455 := bstep (se 1 (by rfl) ⟨60408341, by rfl⟩ : syracuseStep 80544455 = 120816683) B120816683
theorem B296160923 : Blo 287828 296160923 := bstep (se 1 (by rfl) ⟨222120692, by rfl⟩ : syracuseStep 296160923 = 444241385) B444241385
theorem B433151 : Blo 287828 433151 := bstep (se 1 (by rfl) ⟨324863, by rfl⟩ : syracuseStep 433151 = 649727) B649727
theorem B7129727 : Blo 287828 7129727 := bstep (se 1 (by rfl) ⟨5347295, by rfl⟩ : syracuseStep 7129727 = 10694591) B10694591
theorem B3300911 : Blo 287828 3300911 := bstep (se 1 (by rfl) ⟨2475683, by rfl⟩ : syracuseStep 3300911 = 4951367) B4951367
theorem B11330027 : Blo 287828 11330027 := bstep (se 1 (by rfl) ⟨8497520, by rfl⟩ : syracuseStep 11330027 = 16995041) B16995041
theorem B1239209 : Blo 287828 1239209 := bstep (se 2 (by rfl) ⟨464703, by rfl⟩ : syracuseStep 1239209 = 929407) B929407
theorem B977831 : Blo 287828 977831 := bstep (se 1 (by rfl) ⟨733373, by rfl⟩ : syracuseStep 977831 = 1466747) B1466747
theorem B552575 : Blo 287828 552575 := bstep (se 1 (by rfl) ⟨414431, by rfl⟩ : syracuseStep 552575 = 828863) B828863
theorem B4753151 : Blo 287828 4753151 := bstep (se 1 (by rfl) ⟨3564863, by rfl⟩ : syracuseStep 4753151 = 7129727) B7129727
theorem B2200607 : Blo 287828 2200607 := bstep (se 1 (by rfl) ⟨1650455, by rfl⟩ : syracuseStep 2200607 = 3300911) B3300911
theorem B826139 : Blo 287828 826139 := bstep (se 1 (by rfl) ⟨619604, by rfl⟩ : syracuseStep 826139 = 1239209) B1239209
theorem B368383 : Blo 287828 368383 := bstep (se 1 (by rfl) ⟨276287, by rfl⟩ : syracuseStep 368383 = 552575) B552575
theorem B197440615 : Blo 287828 197440615 := bstep (se 1 (by rfl) ⟨148080461, by rfl⟩ : syracuseStep 197440615 = 296160923) B296160923
theorem B7553351 : Blo 287828 7553351 := bstep (se 1 (by rfl) ⟨5665013, by rfl⟩ : syracuseStep 7553351 = 11330027) B11330027
theorem B53696303 : Blo 287828 53696303 := bstep (se 1 (by rfl) ⟨40272227, by rfl⟩ : syracuseStep 53696303 = 80544455) B80544455
theorem B288767 : Blo 287828 288767 := bstep (se 1 (by rfl) ⟨216575, by rfl⟩ : syracuseStep 288767 = 433151) B433151
theorem B651887 : Blo 287828 651887 := bstep (se 1 (by rfl) ⟨488915, by rfl⟩ : syracuseStep 651887 = 977831) B977831
theorem B2203037 : Blo 287828 2203037 := bstep (se 3 (by rfl) ⟨413069, by rfl⟩ : syracuseStep 2203037 = 826139) B826139
theorem B434591 : Blo 287828 434591 := bstep (se 1 (by rfl) ⟨325943, by rfl⟩ : syracuseStep 434591 = 651887) B651887
theorem B35797535 : Blo 287828 35797535 := bstep (se 1 (by rfl) ⟨26848151, by rfl⟩ : syracuseStep 35797535 = 53696303) B53696303
theorem B5035567 : Blo 287828 5035567 := bstep (se 1 (by rfl) ⟨3776675, by rfl⟩ : syracuseStep 5035567 = 7553351) B7553351
theorem B3168767 : Blo 287828 3168767 := bstep (se 1 (by rfl) ⟨2376575, by rfl⟩ : syracuseStep 3168767 = 4753151) B4753151
theorem B1467071 : Blo 287828 1467071 := bstep (se 1 (by rfl) ⟨1100303, by rfl⟩ : syracuseStep 1467071 = 2200607) B2200607
theorem B263254153 : Blo 287828 263254153 := bstep (se 2 (by rfl) ⟨98720307, by rfl⟩ : syracuseStep 263254153 = 197440615) B197440615
theorem B491177 : Blo 287828 491177 := bstep (se 2 (by rfl) ⟨184191, by rfl⟩ : syracuseStep 491177 = 368383) B368383
theorem B23865023 : Blo 287828 23865023 := bstep (se 1 (by rfl) ⟨17898767, by rfl⟩ : syracuseStep 23865023 = 35797535) B35797535
theorem B1468691 : Blo 287828 1468691 := bstep (se 1 (by rfl) ⟨1101518, by rfl⟩ : syracuseStep 1468691 = 2203037) B2203037
theorem B351005537 : Blo 287828 351005537 := bstep (se 2 (by rfl) ⟨131627076, by rfl⟩ : syracuseStep 351005537 = 263254153) B263254153
theorem B289727 : Blo 287828 289727 := bstep (se 1 (by rfl) ⟨217295, by rfl⟩ : syracuseStep 289727 = 434591) B434591
theorem B978047 : Blo 287828 978047 := bstep (se 1 (by rfl) ⟨733535, by rfl⟩ : syracuseStep 978047 = 1467071) B1467071
theorem B8450045 : Blo 287828 8450045 := bstep (se 3 (by rfl) ⟨1584383, by rfl⟩ : syracuseStep 8450045 = 3168767) B3168767
theorem B6714089 : Blo 287828 6714089 := bstep (se 2 (by rfl) ⟨2517783, by rfl⟩ : syracuseStep 6714089 = 5035567) B5035567
theorem B327451 : Blo 287828 327451 := bstep (se 1 (by rfl) ⟨245588, by rfl⟩ : syracuseStep 327451 = 491177) B491177
theorem B234003691 : Blo 287828 234003691 := bstep (se 1 (by rfl) ⟨175502768, by rfl⟩ : syracuseStep 234003691 = 351005537) B351005537
theorem B436601 : Blo 287828 436601 := bstep (se 2 (by rfl) ⟨163725, by rfl⟩ : syracuseStep 436601 = 327451) B327451
theorem B15910015 : Blo 287828 15910015 := bstep (se 1 (by rfl) ⟨11932511, by rfl⟩ : syracuseStep 15910015 = 23865023) B23865023
theorem B4476059 : Blo 287828 4476059 := bstep (se 1 (by rfl) ⟨3357044, by rfl⟩ : syracuseStep 4476059 = 6714089) B6714089
theorem B979127 : Blo 287828 979127 := bstep (se 1 (by rfl) ⟨734345, by rfl⟩ : syracuseStep 979127 = 1468691) B1468691
theorem B652031 : Blo 287828 652031 := bstep (se 1 (by rfl) ⟨489023, by rfl⟩ : syracuseStep 652031 = 978047) B978047
theorem B5633363 : Blo 287828 5633363 := bstep (se 1 (by rfl) ⟨4225022, by rfl⟩ : syracuseStep 5633363 = 8450045) B8450045
theorem B2984039 : Blo 287828 2984039 := bstep (se 1 (by rfl) ⟨2238029, by rfl⟩ : syracuseStep 2984039 = 4476059) B4476059
theorem B434687 : Blo 287828 434687 := bstep (se 1 (by rfl) ⟨326015, by rfl⟩ : syracuseStep 434687 = 652031) B652031
theorem B21213353 : Blo 287828 21213353 := bstep (se 2 (by rfl) ⟨7955007, by rfl⟩ : syracuseStep 21213353 = 15910015) B15910015
theorem B3755575 : Blo 287828 3755575 := bstep (se 1 (by rfl) ⟨2816681, by rfl⟩ : syracuseStep 3755575 = 5633363) B5633363
theorem B312004921 : Blo 287828 312004921 := bstep (se 2 (by rfl) ⟨117001845, by rfl⟩ : syracuseStep 312004921 = 234003691) B234003691
theorem B291067 : Blo 287828 291067 := bstep (se 1 (by rfl) ⟨218300, by rfl⟩ : syracuseStep 291067 = 436601) B436601
theorem B652751 : Blo 287828 652751 := bstep (se 1 (by rfl) ⟨489563, by rfl⟩ : syracuseStep 652751 = 979127) B979127
theorem B435167 : Blo 287828 435167 := bstep (se 1 (by rfl) ⟨326375, by rfl⟩ : syracuseStep 435167 = 652751) B652751
theorem B416006561 : Blo 287828 416006561 := bstep (se 2 (by rfl) ⟨156002460, by rfl⟩ : syracuseStep 416006561 = 312004921) B312004921
theorem B14142235 : Blo 287828 14142235 := bstep (se 1 (by rfl) ⟨10606676, by rfl⟩ : syracuseStep 14142235 = 21213353) B21213353
theorem B1989359 : Blo 287828 1989359 := bstep (se 1 (by rfl) ⟨1492019, by rfl⟩ : syracuseStep 1989359 = 2984039) B2984039
theorem B5007433 : Blo 287828 5007433 := bstep (se 2 (by rfl) ⟨1877787, by rfl⟩ : syracuseStep 5007433 = 3755575) B3755575
theorem B289791 : Blo 287828 289791 := bstep (se 1 (by rfl) ⟨217343, by rfl⟩ : syracuseStep 289791 = 434687) B434687
theorem B18856313 : Blo 287828 18856313 := bstep (se 2 (by rfl) ⟨7071117, by rfl⟩ : syracuseStep 18856313 = 14142235) B14142235
theorem B1326239 : Blo 287828 1326239 := bstep (se 1 (by rfl) ⟨994679, by rfl⟩ : syracuseStep 1326239 = 1989359) B1989359
theorem B1109350829 : Blo 287828 1109350829 := bstep (se 3 (by rfl) ⟨208003280, by rfl⟩ : syracuseStep 1109350829 = 416006561) B416006561
theorem B6676577 : Blo 287828 6676577 := bstep (se 2 (by rfl) ⟨2503716, by rfl⟩ : syracuseStep 6676577 = 5007433) B5007433
theorem B290111 : Blo 287828 290111 := bstep (se 1 (by rfl) ⟨217583, by rfl⟩ : syracuseStep 290111 = 435167) B435167
theorem B12570875 : Blo 287828 12570875 := bstep (se 1 (by rfl) ⟨9428156, by rfl⟩ : syracuseStep 12570875 = 18856313) B18856313
theorem B739567219 : Blo 287828 739567219 := bstep (se 1 (by rfl) ⟨554675414, by rfl⟩ : syracuseStep 739567219 = 1109350829) B1109350829
theorem B4451051 : Blo 287828 4451051 := bstep (se 1 (by rfl) ⟨3338288, by rfl⟩ : syracuseStep 4451051 = 6676577) B6676577
theorem B884159 : Blo 287828 884159 := bstep (se 1 (by rfl) ⟨663119, by rfl⟩ : syracuseStep 884159 = 1326239) B1326239
theorem B986089625 : Blo 287828 986089625 := bstep (se 2 (by rfl) ⟨369783609, by rfl⟩ : syracuseStep 986089625 = 739567219) B739567219
theorem B2967367 : Blo 287828 2967367 := bstep (se 1 (by rfl) ⟨2225525, by rfl⟩ : syracuseStep 2967367 = 4451051) B4451051
theorem B8380583 : Blo 287828 8380583 := bstep (se 1 (by rfl) ⟨6285437, by rfl⟩ : syracuseStep 8380583 = 12570875) B12570875
theorem B589439 : Blo 287828 589439 := bstep (se 1 (by rfl) ⟨442079, by rfl⟩ : syracuseStep 589439 = 884159) B884159
theorem B657393083 : Blo 287828 657393083 := bstep (se 1 (by rfl) ⟨493044812, by rfl⟩ : syracuseStep 657393083 = 986089625) B986089625
theorem B5587055 : Blo 287828 5587055 := bstep (se 1 (by rfl) ⟨4190291, by rfl⟩ : syracuseStep 5587055 = 8380583) B8380583
theorem B3956489 : Blo 287828 3956489 := bstep (se 2 (by rfl) ⟨1483683, by rfl⟩ : syracuseStep 3956489 = 2967367) B2967367
theorem B392959 : Blo 287828 392959 := bstep (se 1 (by rfl) ⟨294719, by rfl⟩ : syracuseStep 392959 = 589439) B589439
theorem B2637659 : Blo 287828 2637659 := bstep (se 1 (by rfl) ⟨1978244, by rfl⟩ : syracuseStep 2637659 = 3956489) B3956489
theorem B3724703 : Blo 287828 3724703 := bstep (se 1 (by rfl) ⟨2793527, by rfl⟩ : syracuseStep 3724703 = 5587055) B5587055
theorem B438262055 : Blo 287828 438262055 := bstep (se 1 (by rfl) ⟨328696541, by rfl⟩ : syracuseStep 438262055 = 657393083) B657393083
theorem B523945 : Blo 287828 523945 := bstep (se 2 (by rfl) ⟨196479, by rfl⟩ : syracuseStep 523945 = 392959) B392959
theorem B698593 : Blo 287828 698593 := bstep (se 2 (by rfl) ⟨261972, by rfl⟩ : syracuseStep 698593 = 523945) B523945
theorem B292174703 : Blo 287828 292174703 := bstep (se 1 (by rfl) ⟨219131027, by rfl⟩ : syracuseStep 292174703 = 438262055) B438262055
theorem B1758439 : Blo 287828 1758439 := bstep (se 1 (by rfl) ⟨1318829, by rfl⟩ : syracuseStep 1758439 = 2637659) B2637659
theorem B2483135 : Blo 287828 2483135 := bstep (se 1 (by rfl) ⟨1862351, by rfl⟩ : syracuseStep 2483135 = 3724703) B3724703
theorem B194783135 : Blo 287828 194783135 := bstep (se 1 (by rfl) ⟨146087351, by rfl⟩ : syracuseStep 194783135 = 292174703) B292174703
theorem B931457 : Blo 287828 931457 := bstep (se 2 (by rfl) ⟨349296, by rfl⟩ : syracuseStep 931457 = 698593) B698593
theorem B1655423 : Blo 287828 1655423 := bstep (se 1 (by rfl) ⟨1241567, by rfl⟩ : syracuseStep 1655423 = 2483135) B2483135
theorem B2344585 : Blo 287828 2344585 := bstep (se 2 (by rfl) ⟨879219, by rfl⟩ : syracuseStep 2344585 = 1758439) B1758439
theorem B3126113 : Blo 287828 3126113 := bstep (se 2 (by rfl) ⟨1172292, by rfl⟩ : syracuseStep 3126113 = 2344585) B2344585
theorem B519421693 : Blo 287828 519421693 := bstep (se 3 (by rfl) ⟨97391567, by rfl⟩ : syracuseStep 519421693 = 194783135) B194783135
theorem B1103615 : Blo 287828 1103615 := bstep (se 1 (by rfl) ⟨827711, by rfl⟩ : syracuseStep 1103615 = 1655423) B1655423
theorem B2483885 : Blo 287828 2483885 := bstep (se 3 (by rfl) ⟨465728, by rfl⟩ : syracuseStep 2483885 = 931457) B931457
theorem B692562257 : Blo 287828 692562257 := bstep (se 2 (by rfl) ⟨259710846, by rfl⟩ : syracuseStep 692562257 = 519421693) B519421693
theorem B735743 : Blo 287828 735743 := bstep (se 1 (by rfl) ⟨551807, by rfl⟩ : syracuseStep 735743 = 1103615) B1103615
theorem B1655923 : Blo 287828 1655923 := bstep (se 1 (by rfl) ⟨1241942, by rfl⟩ : syracuseStep 1655923 = 2483885) B2483885
theorem B2084075 : Blo 287828 2084075 := bstep (se 1 (by rfl) ⟨1563056, by rfl⟩ : syracuseStep 2084075 = 3126113) B3126113
theorem B461708171 : Blo 287828 461708171 := bstep (se 1 (by rfl) ⟨346281128, by rfl⟩ : syracuseStep 461708171 = 692562257) B692562257
theorem B2207897 : Blo 287828 2207897 := bstep (se 2 (by rfl) ⟨827961, by rfl⟩ : syracuseStep 2207897 = 1655923) B1655923
theorem B1389383 : Blo 287828 1389383 := bstep (se 1 (by rfl) ⟨1042037, by rfl⟩ : syracuseStep 1389383 = 2084075) B2084075
theorem B490495 : Blo 287828 490495 := bstep (se 1 (by rfl) ⟨367871, by rfl⟩ : syracuseStep 490495 = 735743) B735743
theorem B926255 : Blo 287828 926255 := bstep (se 1 (by rfl) ⟨694691, by rfl⟩ : syracuseStep 926255 = 1389383) B1389383
theorem B307805447 : Blo 287828 307805447 := bstep (se 1 (by rfl) ⟨230854085, by rfl⟩ : syracuseStep 307805447 = 461708171) B461708171
theorem B1471931 : Blo 287828 1471931 := bstep (se 1 (by rfl) ⟨1103948, by rfl⟩ : syracuseStep 1471931 = 2207897) B2207897
theorem B653993 : Blo 287828 653993 := bstep (se 2 (by rfl) ⟨245247, by rfl⟩ : syracuseStep 653993 = 490495) B490495
theorem B435995 : Blo 287828 435995 := bstep (se 1 (by rfl) ⟨326996, by rfl⟩ : syracuseStep 435995 = 653993) B653993
theorem B205203631 : Blo 287828 205203631 := bstep (se 1 (by rfl) ⟨153902723, by rfl⟩ : syracuseStep 205203631 = 307805447) B307805447
theorem B2470013 : Blo 287828 2470013 := bstep (se 3 (by rfl) ⟨463127, by rfl⟩ : syracuseStep 2470013 = 926255) B926255
theorem B981287 : Blo 287828 981287 := bstep (se 1 (by rfl) ⟨735965, by rfl⟩ : syracuseStep 981287 = 1471931) B1471931
theorem B1646675 : Blo 287828 1646675 := bstep (se 1 (by rfl) ⟨1235006, by rfl⟩ : syracuseStep 1646675 = 2470013) B2470013
theorem B273604841 : Blo 287828 273604841 := bstep (se 2 (by rfl) ⟨102601815, by rfl⟩ : syracuseStep 273604841 = 205203631) B205203631
theorem B290663 : Blo 287828 290663 := bstep (se 1 (by rfl) ⟨217997, by rfl⟩ : syracuseStep 290663 = 435995) B435995
theorem B654191 : Blo 287828 654191 := bstep (se 1 (by rfl) ⟨490643, by rfl⟩ : syracuseStep 654191 = 981287) B981287
theorem B436127 : Blo 287828 436127 := bstep (se 1 (by rfl) ⟨327095, by rfl⟩ : syracuseStep 436127 = 654191) B654191
theorem B1097783 : Blo 287828 1097783 := bstep (se 1 (by rfl) ⟨823337, by rfl⟩ : syracuseStep 1097783 = 1646675) B1646675
theorem B182403227 : Blo 287828 182403227 := bstep (se 1 (by rfl) ⟨136802420, by rfl⟩ : syracuseStep 182403227 = 273604841) B273604841
theorem B121602151 : Blo 287828 121602151 := bstep (se 1 (by rfl) ⟨91201613, by rfl⟩ : syracuseStep 121602151 = 182403227) B182403227
theorem B731855 : Blo 287828 731855 := bstep (se 1 (by rfl) ⟨548891, by rfl⟩ : syracuseStep 731855 = 1097783) B1097783
theorem B290751 : Blo 287828 290751 := bstep (se 1 (by rfl) ⟨218063, by rfl⟩ : syracuseStep 290751 = 436127) B436127
theorem B648544805 : Blo 287828 648544805 := bstep (se 4 (by rfl) ⟨60801075, by rfl⟩ : syracuseStep 648544805 = 121602151) B121602151
theorem B487903 : Blo 287828 487903 := bstep (se 1 (by rfl) ⟨365927, by rfl⟩ : syracuseStep 487903 = 731855) B731855
theorem B432363203 : Blo 287828 432363203 := bstep (se 1 (by rfl) ⟨324272402, by rfl⟩ : syracuseStep 432363203 = 648544805) B648544805
theorem B650537 : Blo 287828 650537 := bstep (se 2 (by rfl) ⟨243951, by rfl⟩ : syracuseStep 650537 = 487903) B487903
theorem B433691 : Blo 287828 433691 := bstep (se 1 (by rfl) ⟨325268, by rfl⟩ : syracuseStep 433691 = 650537) B650537
theorem B288242135 : Blo 287828 288242135 := bstep (se 1 (by rfl) ⟨216181601, by rfl⟩ : syracuseStep 288242135 = 432363203) B432363203
theorem B192161423 : Blo 287828 192161423 := bstep (se 1 (by rfl) ⟨144121067, by rfl⟩ : syracuseStep 192161423 = 288242135) B288242135
theorem B289127 : Blo 287828 289127 := bstep (se 1 (by rfl) ⟨216845, by rfl⟩ : syracuseStep 289127 = 433691) B433691
theorem B128107615 : Blo 287828 128107615 := bstep (se 1 (by rfl) ⟨96080711, by rfl⟩ : syracuseStep 128107615 = 192161423) B192161423
theorem B170810153 : Blo 287828 170810153 := bstep (se 2 (by rfl) ⟨64053807, by rfl⟩ : syracuseStep 170810153 = 128107615) B128107615
theorem B113873435 : Blo 287828 113873435 := bstep (se 1 (by rfl) ⟨85405076, by rfl⟩ : syracuseStep 113873435 = 170810153) B170810153
theorem B75915623 : Blo 287828 75915623 := bstep (se 1 (by rfl) ⟨56936717, by rfl⟩ : syracuseStep 75915623 = 113873435) B113873435
theorem B50610415 : Blo 287828 50610415 := bstep (se 1 (by rfl) ⟨37957811, by rfl⟩ : syracuseStep 50610415 = 75915623) B75915623
theorem B67480553 : Blo 287828 67480553 := bstep (se 2 (by rfl) ⟨25305207, by rfl⟩ : syracuseStep 67480553 = 50610415) B50610415
theorem B44987035 : Blo 287828 44987035 := bstep (se 1 (by rfl) ⟨33740276, by rfl⟩ : syracuseStep 44987035 = 67480553) B67480553
theorem B59982713 : Blo 287828 59982713 := bstep (se 2 (by rfl) ⟨22493517, by rfl⟩ : syracuseStep 59982713 = 44987035) B44987035
theorem B39988475 : Blo 287828 39988475 := bstep (se 1 (by rfl) ⟨29991356, by rfl⟩ : syracuseStep 39988475 = 59982713) B59982713
theorem B26658983 : Blo 287828 26658983 := bstep (se 1 (by rfl) ⟨19994237, by rfl⟩ : syracuseStep 26658983 = 39988475) B39988475
theorem B71090621 : Blo 287828 71090621 := bstep (se 3 (by rfl) ⟨13329491, by rfl⟩ : syracuseStep 71090621 = 26658983) B26658983
theorem B47393747 : Blo 287828 47393747 := bstep (se 1 (by rfl) ⟨35545310, by rfl⟩ : syracuseStep 47393747 = 71090621) B71090621
theorem B31595831 : Blo 287828 31595831 := bstep (se 1 (by rfl) ⟨23696873, by rfl⟩ : syracuseStep 31595831 = 47393747) B47393747
theorem B21063887 : Blo 287828 21063887 := bstep (se 1 (by rfl) ⟨15797915, by rfl⟩ : syracuseStep 21063887 = 31595831) B31595831
theorem B14042591 : Blo 287828 14042591 := bstep (se 1 (by rfl) ⟨10531943, by rfl⟩ : syracuseStep 14042591 = 21063887) B21063887
theorem B9361727 : Blo 287828 9361727 := bstep (se 1 (by rfl) ⟨7021295, by rfl⟩ : syracuseStep 9361727 = 14042591) B14042591
theorem B6241151 : Blo 287828 6241151 := bstep (se 1 (by rfl) ⟨4680863, by rfl⟩ : syracuseStep 6241151 = 9361727) B9361727
theorem B4160767 : Blo 287828 4160767 := bstep (se 1 (by rfl) ⟨3120575, by rfl⟩ : syracuseStep 4160767 = 6241151) B6241151
theorem B5547689 : Blo 287828 5547689 := bstep (se 2 (by rfl) ⟨2080383, by rfl⟩ : syracuseStep 5547689 = 4160767) B4160767
theorem B3698459 : Blo 287828 3698459 := bstep (se 1 (by rfl) ⟨2773844, by rfl⟩ : syracuseStep 3698459 = 5547689) B5547689
theorem B2465639 : Blo 287828 2465639 := bstep (se 1 (by rfl) ⟨1849229, by rfl⟩ : syracuseStep 2465639 = 3698459) B3698459
theorem B1643759 : Blo 287828 1643759 := bstep (se 1 (by rfl) ⟨1232819, by rfl⟩ : syracuseStep 1643759 = 2465639) B2465639
theorem B1095839 : Blo 287828 1095839 := bstep (se 1 (by rfl) ⟨821879, by rfl⟩ : syracuseStep 1095839 = 1643759) B1643759
theorem B730559 : Blo 287828 730559 := bstep (se 1 (by rfl) ⟨547919, by rfl⟩ : syracuseStep 730559 = 1095839) B1095839
theorem B487039 : Blo 287828 487039 := bstep (se 1 (by rfl) ⟨365279, by rfl⟩ : syracuseStep 487039 = 730559) B730559
theorem B649385 : Blo 287828 649385 := bstep (se 2 (by rfl) ⟨243519, by rfl⟩ : syracuseStep 649385 = 487039) B487039
theorem B432923 : Blo 287828 432923 := bstep (se 1 (by rfl) ⟨324692, by rfl⟩ : syracuseStep 432923 = 649385) B649385
theorem B288615 : Blo 287828 288615 := bstep (se 1 (by rfl) ⟨216461, by rfl⟩ : syracuseStep 288615 = 432923) B432923

theorem C0 (j : ℕ) (h1 : 71957 ≤ j) (h2 : j ≤ 72656) : Blo 287828 (4 * j + 3) := by
  interval_cases j
  · exact B287831
  · exact B287835
  · exact B287839
  · exact B287843
  · exact B287847
  · exact B287851
  · exact B287855
  · exact B287859
  · exact B287863
  · exact B287867
  · exact B287871
  · exact B287875
  · exact B287879
  · exact B287883
  · exact B287887
  · exact B287891
  · exact B287895
  · exact B287899
  · exact B287903
  · exact B287907
  · exact B287911
  · exact B287915
  · exact B287919
  · exact B287923
  · exact B287927
  · exact B287931
  · exact B287935
  · exact B287939
  · exact B287943
  · exact B287947
  · exact B287951
  · exact B287955
  · exact B287959
  · exact B287963
  · exact B287967
  · exact B287971
  · exact B287975
  · exact B287979
  · exact B287983
  · exact B287987
  · exact B287991
  · exact B287995
  · exact B287999
  · exact B288003
  · exact B288007
  · exact B288011
  · exact B288015
  · exact B288019
  · exact B288023
  · exact B288027
  · exact B288031
  · exact B288035
  · exact B288039
  · exact B288043
  · exact B288047
  · exact B288051
  · exact B288055
  · exact B288059
  · exact B288063
  · exact B288067
  · exact B288071
  · exact B288075
  · exact B288079
  · exact B288083
  · exact B288087
  · exact B288091
  · exact B288095
  · exact B288099
  · exact B288103
  · exact B288107
  · exact B288111
  · exact B288115
  · exact B288119
  · exact B288123
  · exact B288127
  · exact B288131
  · exact B288135
  · exact B288139
  · exact B288143
  · exact B288147
  · exact B288151
  · exact B288155
  · exact B288159
  · exact B288163
  · exact B288167
  · exact B288171
  · exact B288175
  · exact B288179
  · exact B288183
  · exact B288187
  · exact B288191
  · exact B288195
  · exact B288199
  · exact B288203
  · exact B288207
  · exact B288211
  · exact B288215
  · exact B288219
  · exact B288223
  · exact B288227
  · exact B288231
  · exact B288235
  · exact B288239
  · exact B288243
  · exact B288247
  · exact B288251
  · exact B288255
  · exact B288259
  · exact B288263
  · exact B288267
  · exact B288271
  · exact B288275
  · exact B288279
  · exact B288283
  · exact B288287
  · exact B288291
  · exact B288295
  · exact B288299
  · exact B288303
  · exact B288307
  · exact B288311
  · exact B288315
  · exact B288319
  · exact B288323
  · exact B288327
  · exact B288331
  · exact B288335
  · exact B288339
  · exact B288343
  · exact B288347
  · exact B288351
  · exact B288355
  · exact B288359
  · exact B288363
  · exact B288367
  · exact B288371
  · exact B288375
  · exact B288379
  · exact B288383
  · exact B288387
  · exact B288391
  · exact B288395
  · exact B288399
  · exact B288403
  · exact B288407
  · exact B288411
  · exact B288415
  · exact B288419
  · exact B288423
  · exact B288427
  · exact B288431
  · exact B288435
  · exact B288439
  · exact B288443
  · exact B288447
  · exact B288451
  · exact B288455
  · exact B288459
  · exact B288463
  · exact B288467
  · exact B288471
  · exact B288475
  · exact B288479
  · exact B288483
  · exact B288487
  · exact B288491
  · exact B288495
  · exact B288499
  · exact B288503
  · exact B288507
  · exact B288511
  · exact B288515
  · exact B288519
  · exact B288523
  · exact B288527
  · exact B288531
  · exact B288535
  · exact B288539
  · exact B288543
  · exact B288547
  · exact B288551
  · exact B288555
  · exact B288559
  · exact B288563
  · exact B288567
  · exact B288571
  · exact B288575
  · exact B288579
  · exact B288583
  · exact B288587
  · exact B288591
  · exact B288595
  · exact B288599
  · exact B288603
  · exact B288607
  · exact B288611
  · exact B288615
  · exact B288619
  · exact B288623
  · exact B288627
  · exact B288631
  · exact B288635
  · exact B288639
  · exact B288643
  · exact B288647
  · exact B288651
  · exact B288655
  · exact B288659
  · exact B288663
  · exact B288667
  · exact B288671
  · exact B288675
  · exact B288679
  · exact B288683
  · exact B288687
  · exact B288691
  · exact B288695
  · exact B288699
  · exact B288703
  · exact B288707
  · exact B288711
  · exact B288715
  · exact B288719
  · exact B288723
  · exact B288727
  · exact B288731
  · exact B288735
  · exact B288739
  · exact B288743
  · exact B288747
  · exact B288751
  · exact B288755
  · exact B288759
  · exact B288763
  · exact B288767
  · exact B288771
  · exact B288775
  · exact B288779
  · exact B288783
  · exact B288787
  · exact B288791
  · exact B288795
  · exact B288799
  · exact B288803
  · exact B288807
  · exact B288811
  · exact B288815
  · exact B288819
  · exact B288823
  · exact B288827
  · exact B288831
  · exact B288835
  · exact B288839
  · exact B288843
  · exact B288847
  · exact B288851
  · exact B288855
  · exact B288859
  · exact B288863
  · exact B288867
  · exact B288871
  · exact B288875
  · exact B288879
  · exact B288883
  · exact B288887
  · exact B288891
  · exact B288895
  · exact B288899
  · exact B288903
  · exact B288907
  · exact B288911
  · exact B288915
  · exact B288919
  · exact B288923
  · exact B288927
  · exact B288931
  · exact B288935
  · exact B288939
  · exact B288943
  · exact B288947
  · exact B288951
  · exact B288955
  · exact B288959
  · exact B288963
  · exact B288967
  · exact B288971
  · exact B288975
  · exact B288979
  · exact B288983
  · exact B288987
  · exact B288991
  · exact B288995
  · exact B288999
  · exact B289003
  · exact B289007
  · exact B289011
  · exact B289015
  · exact B289019
  · exact B289023
  · exact B289027
  · exact B289031
  · exact B289035
  · exact B289039
  · exact B289043
  · exact B289047
  · exact B289051
  · exact B289055
  · exact B289059
  · exact B289063
  · exact B289067
  · exact B289071
  · exact B289075
  · exact B289079
  · exact B289083
  · exact B289087
  · exact B289091
  · exact B289095
  · exact B289099
  · exact B289103
  · exact B289107
  · exact B289111
  · exact B289115
  · exact B289119
  · exact B289123
  · exact B289127
  · exact B289131
  · exact B289135
  · exact B289139
  · exact B289143
  · exact B289147
  · exact B289151
  · exact B289155
  · exact B289159
  · exact B289163
  · exact B289167
  · exact B289171
  · exact B289175
  · exact B289179
  · exact B289183
  · exact B289187
  · exact B289191
  · exact B289195
  · exact B289199
  · exact B289203
  · exact B289207
  · exact B289211
  · exact B289215
  · exact B289219
  · exact B289223
  · exact B289227
  · exact B289231
  · exact B289235
  · exact B289239
  · exact B289243
  · exact B289247
  · exact B289251
  · exact B289255
  · exact B289259
  · exact B289263
  · exact B289267
  · exact B289271
  · exact B289275
  · exact B289279
  · exact B289283
  · exact B289287
  · exact B289291
  · exact B289295
  · exact B289299
  · exact B289303
  · exact B289307
  · exact B289311
  · exact B289315
  · exact B289319
  · exact B289323
  · exact B289327
  · exact B289331
  · exact B289335
  · exact B289339
  · exact B289343
  · exact B289347
  · exact B289351
  · exact B289355
  · exact B289359
  · exact B289363
  · exact B289367
  · exact B289371
  · exact B289375
  · exact B289379
  · exact B289383
  · exact B289387
  · exact B289391
  · exact B289395
  · exact B289399
  · exact B289403
  · exact B289407
  · exact B289411
  · exact B289415
  · exact B289419
  · exact B289423
  · exact B289427
  · exact B289431
  · exact B289435
  · exact B289439
  · exact B289443
  · exact B289447
  · exact B289451
  · exact B289455
  · exact B289459
  · exact B289463
  · exact B289467
  · exact B289471
  · exact B289475
  · exact B289479
  · exact B289483
  · exact B289487
  · exact B289491
  · exact B289495
  · exact B289499
  · exact B289503
  · exact B289507
  · exact B289511
  · exact B289515
  · exact B289519
  · exact B289523
  · exact B289527
  · exact B289531
  · exact B289535
  · exact B289539
  · exact B289543
  · exact B289547
  · exact B289551
  · exact B289555
  · exact B289559
  · exact B289563
  · exact B289567
  · exact B289571
  · exact B289575
  · exact B289579
  · exact B289583
  · exact B289587
  · exact B289591
  · exact B289595
  · exact B289599
  · exact B289603
  · exact B289607
  · exact B289611
  · exact B289615
  · exact B289619
  · exact B289623
  · exact B289627
  · exact B289631
  · exact B289635
  · exact B289639
  · exact B289643
  · exact B289647
  · exact B289651
  · exact B289655
  · exact B289659
  · exact B289663
  · exact B289667
  · exact B289671
  · exact B289675
  · exact B289679
  · exact B289683
  · exact B289687
  · exact B289691
  · exact B289695
  · exact B289699
  · exact B289703
  · exact B289707
  · exact B289711
  · exact B289715
  · exact B289719
  · exact B289723
  · exact B289727
  · exact B289731
  · exact B289735
  · exact B289739
  · exact B289743
  · exact B289747
  · exact B289751
  · exact B289755
  · exact B289759
  · exact B289763
  · exact B289767
  · exact B289771
  · exact B289775
  · exact B289779
  · exact B289783
  · exact B289787
  · exact B289791
  · exact B289795
  · exact B289799
  · exact B289803
  · exact B289807
  · exact B289811
  · exact B289815
  · exact B289819
  · exact B289823
  · exact B289827
  · exact B289831
  · exact B289835
  · exact B289839
  · exact B289843
  · exact B289847
  · exact B289851
  · exact B289855
  · exact B289859
  · exact B289863
  · exact B289867
  · exact B289871
  · exact B289875
  · exact B289879
  · exact B289883
  · exact B289887
  · exact B289891
  · exact B289895
  · exact B289899
  · exact B289903
  · exact B289907
  · exact B289911
  · exact B289915
  · exact B289919
  · exact B289923
  · exact B289927
  · exact B289931
  · exact B289935
  · exact B289939
  · exact B289943
  · exact B289947
  · exact B289951
  · exact B289955
  · exact B289959
  · exact B289963
  · exact B289967
  · exact B289971
  · exact B289975
  · exact B289979
  · exact B289983
  · exact B289987
  · exact B289991
  · exact B289995
  · exact B289999
  · exact B290003
  · exact B290007
  · exact B290011
  · exact B290015
  · exact B290019
  · exact B290023
  · exact B290027
  · exact B290031
  · exact B290035
  · exact B290039
  · exact B290043
  · exact B290047
  · exact B290051
  · exact B290055
  · exact B290059
  · exact B290063
  · exact B290067
  · exact B290071
  · exact B290075
  · exact B290079
  · exact B290083
  · exact B290087
  · exact B290091
  · exact B290095
  · exact B290099
  · exact B290103
  · exact B290107
  · exact B290111
  · exact B290115
  · exact B290119
  · exact B290123
  · exact B290127
  · exact B290131
  · exact B290135
  · exact B290139
  · exact B290143
  · exact B290147
  · exact B290151
  · exact B290155
  · exact B290159
  · exact B290163
  · exact B290167
  · exact B290171
  · exact B290175
  · exact B290179
  · exact B290183
  · exact B290187
  · exact B290191
  · exact B290195
  · exact B290199
  · exact B290203
  · exact B290207
  · exact B290211
  · exact B290215
  · exact B290219
  · exact B290223
  · exact B290227
  · exact B290231
  · exact B290235
  · exact B290239
  · exact B290243
  · exact B290247
  · exact B290251
  · exact B290255
  · exact B290259
  · exact B290263
  · exact B290267
  · exact B290271
  · exact B290275
  · exact B290279
  · exact B290283
  · exact B290287
  · exact B290291
  · exact B290295
  · exact B290299
  · exact B290303
  · exact B290307
  · exact B290311
  · exact B290315
  · exact B290319
  · exact B290323
  · exact B290327
  · exact B290331
  · exact B290335
  · exact B290339
  · exact B290343
  · exact B290347
  · exact B290351
  · exact B290355
  · exact B290359
  · exact B290363
  · exact B290367
  · exact B290371
  · exact B290375
  · exact B290379
  · exact B290383
  · exact B290387
  · exact B290391
  · exact B290395
  · exact B290399
  · exact B290403
  · exact B290407
  · exact B290411
  · exact B290415
  · exact B290419
  · exact B290423
  · exact B290427
  · exact B290431
  · exact B290435
  · exact B290439
  · exact B290443
  · exact B290447
  · exact B290451
  · exact B290455
  · exact B290459
  · exact B290463
  · exact B290467
  · exact B290471
  · exact B290475
  · exact B290479
  · exact B290483
  · exact B290487
  · exact B290491
  · exact B290495
  · exact B290499
  · exact B290503
  · exact B290507
  · exact B290511
  · exact B290515
  · exact B290519
  · exact B290523
  · exact B290527
  · exact B290531
  · exact B290535
  · exact B290539
  · exact B290543
  · exact B290547
  · exact B290551
  · exact B290555
  · exact B290559
  · exact B290563
  · exact B290567
  · exact B290571
  · exact B290575
  · exact B290579
  · exact B290583
  · exact B290587
  · exact B290591
  · exact B290595
  · exact B290599
  · exact B290603
  · exact B290607
  · exact B290611
  · exact B290615
  · exact B290619
  · exact B290623
  · exact B290627

theorem C1 (j : ℕ) (h1 : 72657 ≤ j) (h2 : j ≤ 72956) : Blo 287828 (4 * j + 3) := by
  interval_cases j
  · exact B290631
  · exact B290635
  · exact B290639
  · exact B290643
  · exact B290647
  · exact B290651
  · exact B290655
  · exact B290659
  · exact B290663
  · exact B290667
  · exact B290671
  · exact B290675
  · exact B290679
  · exact B290683
  · exact B290687
  · exact B290691
  · exact B290695
  · exact B290699
  · exact B290703
  · exact B290707
  · exact B290711
  · exact B290715
  · exact B290719
  · exact B290723
  · exact B290727
  · exact B290731
  · exact B290735
  · exact B290739
  · exact B290743
  · exact B290747
  · exact B290751
  · exact B290755
  · exact B290759
  · exact B290763
  · exact B290767
  · exact B290771
  · exact B290775
  · exact B290779
  · exact B290783
  · exact B290787
  · exact B290791
  · exact B290795
  · exact B290799
  · exact B290803
  · exact B290807
  · exact B290811
  · exact B290815
  · exact B290819
  · exact B290823
  · exact B290827
  · exact B290831
  · exact B290835
  · exact B290839
  · exact B290843
  · exact B290847
  · exact B290851
  · exact B290855
  · exact B290859
  · exact B290863
  · exact B290867
  · exact B290871
  · exact B290875
  · exact B290879
  · exact B290883
  · exact B290887
  · exact B290891
  · exact B290895
  · exact B290899
  · exact B290903
  · exact B290907
  · exact B290911
  · exact B290915
  · exact B290919
  · exact B290923
  · exact B290927
  · exact B290931
  · exact B290935
  · exact B290939
  · exact B290943
  · exact B290947
  · exact B290951
  · exact B290955
  · exact B290959
  · exact B290963
  · exact B290967
  · exact B290971
  · exact B290975
  · exact B290979
  · exact B290983
  · exact B290987
  · exact B290991
  · exact B290995
  · exact B290999
  · exact B291003
  · exact B291007
  · exact B291011
  · exact B291015
  · exact B291019
  · exact B291023
  · exact B291027
  · exact B291031
  · exact B291035
  · exact B291039
  · exact B291043
  · exact B291047
  · exact B291051
  · exact B291055
  · exact B291059
  · exact B291063
  · exact B291067
  · exact B291071
  · exact B291075
  · exact B291079
  · exact B291083
  · exact B291087
  · exact B291091
  · exact B291095
  · exact B291099
  · exact B291103
  · exact B291107
  · exact B291111
  · exact B291115
  · exact B291119
  · exact B291123
  · exact B291127
  · exact B291131
  · exact B291135
  · exact B291139
  · exact B291143
  · exact B291147
  · exact B291151
  · exact B291155
  · exact B291159
  · exact B291163
  · exact B291167
  · exact B291171
  · exact B291175
  · exact B291179
  · exact B291183
  · exact B291187
  · exact B291191
  · exact B291195
  · exact B291199
  · exact B291203
  · exact B291207
  · exact B291211
  · exact B291215
  · exact B291219
  · exact B291223
  · exact B291227
  · exact B291231
  · exact B291235
  · exact B291239
  · exact B291243
  · exact B291247
  · exact B291251
  · exact B291255
  · exact B291259
  · exact B291263
  · exact B291267
  · exact B291271
  · exact B291275
  · exact B291279
  · exact B291283
  · exact B291287
  · exact B291291
  · exact B291295
  · exact B291299
  · exact B291303
  · exact B291307
  · exact B291311
  · exact B291315
  · exact B291319
  · exact B291323
  · exact B291327
  · exact B291331
  · exact B291335
  · exact B291339
  · exact B291343
  · exact B291347
  · exact B291351
  · exact B291355
  · exact B291359
  · exact B291363
  · exact B291367
  · exact B291371
  · exact B291375
  · exact B291379
  · exact B291383
  · exact B291387
  · exact B291391
  · exact B291395
  · exact B291399
  · exact B291403
  · exact B291407
  · exact B291411
  · exact B291415
  · exact B291419
  · exact B291423
  · exact B291427
  · exact B291431
  · exact B291435
  · exact B291439
  · exact B291443
  · exact B291447
  · exact B291451
  · exact B291455
  · exact B291459
  · exact B291463
  · exact B291467
  · exact B291471
  · exact B291475
  · exact B291479
  · exact B291483
  · exact B291487
  · exact B291491
  · exact B291495
  · exact B291499
  · exact B291503
  · exact B291507
  · exact B291511
  · exact B291515
  · exact B291519
  · exact B291523
  · exact B291527
  · exact B291531
  · exact B291535
  · exact B291539
  · exact B291543
  · exact B291547
  · exact B291551
  · exact B291555
  · exact B291559
  · exact B291563
  · exact B291567
  · exact B291571
  · exact B291575
  · exact B291579
  · exact B291583
  · exact B291587
  · exact B291591
  · exact B291595
  · exact B291599
  · exact B291603
  · exact B291607
  · exact B291611
  · exact B291615
  · exact B291619
  · exact B291623
  · exact B291627
  · exact B291631
  · exact B291635
  · exact B291639
  · exact B291643
  · exact B291647
  · exact B291651
  · exact B291655
  · exact B291659
  · exact B291663
  · exact B291667
  · exact B291671
  · exact B291675
  · exact B291679
  · exact B291683
  · exact B291687
  · exact B291691
  · exact B291695
  · exact B291699
  · exact B291703
  · exact B291707
  · exact B291711
  · exact B291715
  · exact B291719
  · exact B291723
  · exact B291727
  · exact B291731
  · exact B291735
  · exact B291739
  · exact B291743
  · exact B291747
  · exact B291751
  · exact B291755
  · exact B291759
  · exact B291763
  · exact B291767
  · exact B291771
  · exact B291775
  · exact B291779
  · exact B291783
  · exact B291787
  · exact B291791
  · exact B291795
  · exact B291799
  · exact B291803
  · exact B291807
  · exact B291811
  · exact B291815
  · exact B291819
  · exact B291823
  · exact B291827

theorem solution (m : ℕ) (hlo : 287828 ≤ m) (hhi : m ≤ 291828) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 71957 ≤ j := by omega
    have hj2 : j ≤ 72956 := by omega
    have hb : Blo 287828 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 72657 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
