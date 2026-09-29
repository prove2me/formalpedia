-- Prove2me | solution 1 for syracuse_descends_range_634301_638301
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:04:39.808404+00:00
-- url     : https://prove2.me/submissions/1f76d3d1-afce-4894-bdfe-f322b4035eda

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


theorem B1605653 : Blo 634301 1605653 := bbase (se 6 (by rfl) ⟨37632, by rfl⟩ : syracuseStep 1605653 = 75265) (by norm_num)
theorem B1146901 : Blo 634301 1146901 := bbase (se 6 (by rfl) ⟨26880, by rfl⟩ : syracuseStep 1146901 = 53761) (by norm_num)
theorem B3440789 : Blo 634301 3440789 := bbase (se 6 (by rfl) ⟨80643, by rfl⟩ : syracuseStep 3440789 = 161287) (by norm_num)
theorem B1605845 : Blo 634301 1605845 := bbase (se 7 (by rfl) ⟨18818, by rfl⟩ : syracuseStep 1605845 = 37637) (by norm_num)
theorem B1310957 : Blo 634301 1310957 := bbase (se 3 (by rfl) ⟨245804, by rfl⟩ : syracuseStep 1310957 = 491609) (by norm_num)
theorem B688429 : Blo 634301 688429 := bbase (se 3 (by rfl) ⟨129080, by rfl⟩ : syracuseStep 688429 = 258161) (by norm_num)
theorem B1147189 : Blo 634301 1147189 := bbase (se 5 (by rfl) ⟨53774, by rfl⟩ : syracuseStep 1147189 = 107549) (by norm_num)
theorem B4882837 : Blo 634301 4882837 := bbase (se 6 (by rfl) ⟨114441, by rfl⟩ : syracuseStep 4882837 = 228883) (by norm_num)
theorem B1606189 : Blo 634301 1606189 := bbase (se 3 (by rfl) ⟨301160, by rfl⟩ : syracuseStep 1606189 = 602321) (by norm_num)
theorem B1016405 : Blo 634301 1016405 := bbase (se 8 (by rfl) ⟨5955, by rfl⟩ : syracuseStep 1016405 = 11911) (by norm_num)
theorem B1606301 : Blo 634301 1606301 := bbase (se 3 (by rfl) ⟨301181, by rfl⟩ : syracuseStep 1606301 = 602363) (by norm_num)
theorem B3211973 : Blo 634301 3211973 := bbase (se 4 (by rfl) ⟨301122, by rfl⟩ : syracuseStep 3211973 = 602245) (by norm_num)
theorem B2032373 : Blo 634301 2032373 := bbase (se 5 (by rfl) ⟨95267, by rfl⟩ : syracuseStep 2032373 = 190535) (by norm_num)
theorem B1016597 : Blo 634301 1016597 := bbase (se 6 (by rfl) ⟨23826, by rfl⟩ : syracuseStep 1016597 = 47653) (by norm_num)
theorem B4817717 : Blo 634301 4817717 := bbase (se 5 (by rfl) ⟨225830, by rfl⟩ : syracuseStep 4817717 = 451661) (by norm_num)
theorem B1147709 : Blo 634301 1147709 := bbase (se 3 (by rfl) ⟨215195, by rfl⟩ : syracuseStep 1147709 = 430391) (by norm_num)
theorem B1606493 : Blo 634301 1606493 := bbase (se 3 (by rfl) ⟨301217, by rfl⟩ : syracuseStep 1606493 = 602435) (by norm_num)
theorem B1016725 : Blo 634301 1016725 := bbase (se 6 (by rfl) ⟨23829, by rfl⟩ : syracuseStep 1016725 = 47659) (by norm_num)
theorem B1147853 : Blo 634301 1147853 := bbase (se 3 (by rfl) ⟨215222, by rfl⟩ : syracuseStep 1147853 = 430445) (by norm_num)
theorem B951461 : Blo 634301 951461 := bbase (se 4 (by rfl) ⟨89199, by rfl⟩ : syracuseStep 951461 = 178399) (by norm_num)
theorem B1148069 : Blo 634301 1148069 := bbase (se 4 (by rfl) ⟨107631, by rfl⟩ : syracuseStep 1148069 = 215263) (by norm_num)
theorem B1606837 : Blo 634301 1606837 := bbase (se 5 (by rfl) ⟨75320, by rfl⟩ : syracuseStep 1606837 = 150641) (by norm_num)
theorem B951485 : Blo 634301 951485 := bbase (se 3 (by rfl) ⟨178403, by rfl⟩ : syracuseStep 951485 = 356807) (by norm_num)
theorem B951509 : Blo 634301 951509 := bbase (se 7 (by rfl) ⟨11150, by rfl⟩ : syracuseStep 951509 = 22301) (by norm_num)
theorem B2295013 : Blo 634301 2295013 := bbase (se 4 (by rfl) ⟨215157, by rfl⟩ : syracuseStep 2295013 = 430315) (by norm_num)
theorem B951533 : Blo 634301 951533 := bbase (se 3 (by rfl) ⟨178412, by rfl⟩ : syracuseStep 951533 = 356825) (by norm_num)
theorem B1148141 : Blo 634301 1148141 := bbase (se 3 (by rfl) ⟨215276, by rfl⟩ : syracuseStep 1148141 = 430553) (by norm_num)
theorem B2032885 : Blo 634301 2032885 := bbase (se 5 (by rfl) ⟨95291, by rfl⟩ : syracuseStep 2032885 = 190583) (by norm_num)
theorem B2622709 : Blo 634301 2622709 := bbase (se 5 (by rfl) ⟨122939, by rfl⟩ : syracuseStep 2622709 = 245879) (by norm_num)
theorem B951557 : Blo 634301 951557 := bbase (se 4 (by rfl) ⟨89208, by rfl⟩ : syracuseStep 951557 = 178417) (by norm_num)
theorem B951581 : Blo 634301 951581 := bbase (se 3 (by rfl) ⟨178421, by rfl⟩ : syracuseStep 951581 = 356843) (by norm_num)
theorem B1606949 : Blo 634301 1606949 := bbase (se 4 (by rfl) ⟨150651, by rfl⟩ : syracuseStep 1606949 = 301303) (by norm_num)
theorem B951605 : Blo 634301 951605 := bbase (se 5 (by rfl) ⟨44606, by rfl⟩ : syracuseStep 951605 = 89213) (by norm_num)
theorem B951629 : Blo 634301 951629 := bbase (se 3 (by rfl) ⟨178430, by rfl⟩ : syracuseStep 951629 = 356861) (by norm_num)
theorem B951653 : Blo 634301 951653 := bbase (se 4 (by rfl) ⟨89217, by rfl⟩ : syracuseStep 951653 = 178435) (by norm_num)
theorem B951677 : Blo 634301 951677 := bbase (se 3 (by rfl) ⟨178439, by rfl⟩ : syracuseStep 951677 = 356879) (by norm_num)
theorem B951701 : Blo 634301 951701 := bbase (se 6 (by rfl) ⟨22305, by rfl⟩ : syracuseStep 951701 = 44611) (by norm_num)
theorem B951725 : Blo 634301 951725 := bbase (se 3 (by rfl) ⟨178448, by rfl⟩ : syracuseStep 951725 = 356897) (by norm_num)
theorem B951749 : Blo 634301 951749 := bbase (se 4 (by rfl) ⟨89226, by rfl⟩ : syracuseStep 951749 = 178453) (by norm_num)
theorem B951773 : Blo 634301 951773 := bbase (se 3 (by rfl) ⟨178457, by rfl⟩ : syracuseStep 951773 = 356915) (by norm_num)
theorem B1607141 : Blo 634301 1607141 := bbase (se 4 (by rfl) ⟨150669, by rfl⟩ : syracuseStep 1607141 = 301339) (by norm_num)
theorem B951797 : Blo 634301 951797 := bbase (se 5 (by rfl) ⟨44615, by rfl⟩ : syracuseStep 951797 = 89231) (by norm_num)
theorem B1934837 : Blo 634301 1934837 := bbase (se 5 (by rfl) ⟨90695, by rfl⟩ : syracuseStep 1934837 = 181391) (by norm_num)
theorem B4589045 : Blo 634301 4589045 := bbase (se 5 (by rfl) ⟨215111, by rfl⟩ : syracuseStep 4589045 = 430223) (by norm_num)
theorem B951821 : Blo 634301 951821 := bbase (se 3 (by rfl) ⟨178466, by rfl⟩ : syracuseStep 951821 = 356933) (by norm_num)
theorem B1017365 : Blo 634301 1017365 := bbase (se 6 (by rfl) ⟨23844, by rfl⟩ : syracuseStep 1017365 = 47689) (by norm_num)
theorem B951845 : Blo 634301 951845 := bbase (se 4 (by rfl) ⟨89235, by rfl⟩ : syracuseStep 951845 = 178471) (by norm_num)
theorem B951869 : Blo 634301 951869 := bbase (se 3 (by rfl) ⟨178475, by rfl⟩ : syracuseStep 951869 = 356951) (by norm_num)
theorem B951893 : Blo 634301 951893 := bbase (se 8 (by rfl) ⟨5577, by rfl⟩ : syracuseStep 951893 = 11155) (by norm_num)
theorem B1148509 : Blo 634301 1148509 := bbase (se 3 (by rfl) ⟨215345, by rfl⟩ : syracuseStep 1148509 = 430691) (by norm_num)
theorem B951917 : Blo 634301 951917 := bbase (se 3 (by rfl) ⟨178484, by rfl⟩ : syracuseStep 951917 = 356969) (by norm_num)
theorem B951941 : Blo 634301 951941 := bbase (se 4 (by rfl) ⟨89244, by rfl⟩ : syracuseStep 951941 = 178489) (by norm_num)
theorem B951965 : Blo 634301 951965 := bbase (se 3 (by rfl) ⟨178493, by rfl⟩ : syracuseStep 951965 = 356987) (by norm_num)
theorem B951989 : Blo 634301 951989 := bbase (se 5 (by rfl) ⟨44624, by rfl⟩ : syracuseStep 951989 = 89249) (by norm_num)
theorem B3049157 : Blo 634301 3049157 := bbase (se 4 (by rfl) ⟨285858, by rfl⟩ : syracuseStep 3049157 = 571717) (by norm_num)
theorem B952013 : Blo 634301 952013 := bbase (se 3 (by rfl) ⟨178502, by rfl⟩ : syracuseStep 952013 = 357005) (by norm_num)
theorem B952037 : Blo 634301 952037 := bbase (se 4 (by rfl) ⟨89253, by rfl⟩ : syracuseStep 952037 = 178507) (by norm_num)
theorem B952061 : Blo 634301 952061 := bbase (se 3 (by rfl) ⟨178511, by rfl⟩ : syracuseStep 952061 = 357023) (by norm_num)
theorem B952085 : Blo 634301 952085 := bbase (se 6 (by rfl) ⟨22314, by rfl⟩ : syracuseStep 952085 = 44629) (by norm_num)
theorem B952109 : Blo 634301 952109 := bbase (se 3 (by rfl) ⟨178520, by rfl⟩ : syracuseStep 952109 = 357041) (by norm_num)
theorem B1607485 : Blo 634301 1607485 := bbase (se 3 (by rfl) ⟨301403, by rfl⟩ : syracuseStep 1607485 = 602807) (by norm_num)
theorem B952133 : Blo 634301 952133 := bbase (se 4 (by rfl) ⟨89262, by rfl⟩ : syracuseStep 952133 = 178525) (by norm_num)
theorem B952157 : Blo 634301 952157 := bbase (se 3 (by rfl) ⟨178529, by rfl⟩ : syracuseStep 952157 = 357059) (by norm_num)
theorem B952181 : Blo 634301 952181 := bbase (se 5 (by rfl) ⟨44633, by rfl⟩ : syracuseStep 952181 = 89267) (by norm_num)
theorem B952205 : Blo 634301 952205 := bbase (se 3 (by rfl) ⟨178538, by rfl⟩ : syracuseStep 952205 = 357077) (by norm_num)
theorem B952229 : Blo 634301 952229 := bbase (se 4 (by rfl) ⟨89271, by rfl⟩ : syracuseStep 952229 = 178543) (by norm_num)
theorem B1607597 : Blo 634301 1607597 := bbase (se 3 (by rfl) ⟨301424, by rfl⟩ : syracuseStep 1607597 = 602849) (by norm_num)
theorem B952253 : Blo 634301 952253 := bbase (se 3 (by rfl) ⟨178547, by rfl⟩ : syracuseStep 952253 = 357095) (by norm_num)
theorem B3213269 : Blo 634301 3213269 := bbase (se 7 (by rfl) ⟨37655, by rfl⟩ : syracuseStep 3213269 = 75311) (by norm_num)
theorem B952277 : Blo 634301 952277 := bbase (se 7 (by rfl) ⟨11159, by rfl⟩ : syracuseStep 952277 = 22319) (by norm_num)
theorem B1017821 : Blo 634301 1017821 := bbase (se 3 (by rfl) ⟨190841, by rfl⟩ : syracuseStep 1017821 = 381683) (by norm_num)
theorem B952301 : Blo 634301 952301 := bbase (se 3 (by rfl) ⟨178556, by rfl⟩ : syracuseStep 952301 = 357113) (by norm_num)
theorem B952325 : Blo 634301 952325 := bbase (se 4 (by rfl) ⟨89280, by rfl⟩ : syracuseStep 952325 = 178561) (by norm_num)
theorem B952349 : Blo 634301 952349 := bbase (se 3 (by rfl) ⟨178565, by rfl⟩ : syracuseStep 952349 = 357131) (by norm_num)
theorem B952373 : Blo 634301 952373 := bbase (se 5 (by rfl) ⟨44642, by rfl⟩ : syracuseStep 952373 = 89285) (by norm_num)
theorem B952397 : Blo 634301 952397 := bbase (se 3 (by rfl) ⟨178574, by rfl⟩ : syracuseStep 952397 = 357149) (by norm_num)
theorem B952421 : Blo 634301 952421 := bbase (se 4 (by rfl) ⟨89289, by rfl⟩ : syracuseStep 952421 = 178579) (by norm_num)
theorem B1607789 : Blo 634301 1607789 := bbase (se 3 (by rfl) ⟨301460, by rfl⟩ : syracuseStep 1607789 = 602921) (by norm_num)
theorem B952445 : Blo 634301 952445 := bbase (se 3 (by rfl) ⟨178583, by rfl⟩ : syracuseStep 952445 = 357167) (by norm_num)
theorem B952469 : Blo 634301 952469 := bbase (se 6 (by rfl) ⟨22323, by rfl⟩ : syracuseStep 952469 = 44647) (by norm_num)
theorem B952493 : Blo 634301 952493 := bbase (se 3 (by rfl) ⟨178592, by rfl⟩ : syracuseStep 952493 = 357185) (by norm_num)
theorem B1018045 : Blo 634301 1018045 := bbase (se 3 (by rfl) ⟨190883, by rfl⟩ : syracuseStep 1018045 = 381767) (by norm_num)
theorem B952517 : Blo 634301 952517 := bbase (se 4 (by rfl) ⟨89298, by rfl⟩ : syracuseStep 952517 = 178597) (by norm_num)
theorem B952541 : Blo 634301 952541 := bbase (se 3 (by rfl) ⟨178601, by rfl⟩ : syracuseStep 952541 = 357203) (by norm_num)
theorem B1149149 : Blo 634301 1149149 := bbase (se 3 (by rfl) ⟨215465, by rfl⟩ : syracuseStep 1149149 = 430931) (by norm_num)
theorem B952565 : Blo 634301 952565 := bbase (se 5 (by rfl) ⟨44651, by rfl⟩ : syracuseStep 952565 = 89303) (by norm_num)
theorem B1018109 : Blo 634301 1018109 := bbase (se 3 (by rfl) ⟨190895, by rfl⟩ : syracuseStep 1018109 = 381791) (by norm_num)
theorem B952589 : Blo 634301 952589 := bbase (se 3 (by rfl) ⟨178610, by rfl⟩ : syracuseStep 952589 = 357221) (by norm_num)
theorem B952613 : Blo 634301 952613 := bbase (se 4 (by rfl) ⟨89307, by rfl⟩ : syracuseStep 952613 = 178615) (by norm_num)
theorem B952637 : Blo 634301 952637 := bbase (se 3 (by rfl) ⟨178619, by rfl⟩ : syracuseStep 952637 = 357239) (by norm_num)
theorem B952661 : Blo 634301 952661 := bbase (se 10 (by rfl) ⟨1395, by rfl⟩ : syracuseStep 952661 = 2791) (by norm_num)
theorem B952685 : Blo 634301 952685 := bbase (se 3 (by rfl) ⟨178628, by rfl⟩ : syracuseStep 952685 = 357257) (by norm_num)
theorem B1018237 : Blo 634301 1018237 := bbase (se 3 (by rfl) ⟨190919, by rfl⟩ : syracuseStep 1018237 = 381839) (by norm_num)
theorem B952709 : Blo 634301 952709 := bbase (se 4 (by rfl) ⟨89316, by rfl⟩ : syracuseStep 952709 = 178633) (by norm_num)
theorem B952733 : Blo 634301 952733 := bbase (se 3 (by rfl) ⟨178637, by rfl⟩ : syracuseStep 952733 = 357275) (by norm_num)
theorem B952757 : Blo 634301 952757 := bbase (se 5 (by rfl) ⟨44660, by rfl⟩ : syracuseStep 952757 = 89321) (by norm_num)
theorem B1608133 : Blo 634301 1608133 := bbase (se 4 (by rfl) ⟨150762, by rfl⟩ : syracuseStep 1608133 = 301525) (by norm_num)
theorem B952781 : Blo 634301 952781 := bbase (se 3 (by rfl) ⟨178646, by rfl⟩ : syracuseStep 952781 = 357293) (by norm_num)
theorem B952805 : Blo 634301 952805 := bbase (se 4 (by rfl) ⟨89325, by rfl⟩ : syracuseStep 952805 = 178651) (by norm_num)
theorem B952829 : Blo 634301 952829 := bbase (se 3 (by rfl) ⟨178655, by rfl⟩ : syracuseStep 952829 = 357311) (by norm_num)
theorem B952853 : Blo 634301 952853 := bbase (se 6 (by rfl) ⟨22332, by rfl⟩ : syracuseStep 952853 = 44665) (by norm_num)
theorem B952877 : Blo 634301 952877 := bbase (se 3 (by rfl) ⟨178664, by rfl⟩ : syracuseStep 952877 = 357329) (by norm_num)
theorem B1608245 : Blo 634301 1608245 := bbase (se 5 (by rfl) ⟨75386, by rfl⟩ : syracuseStep 1608245 = 150773) (by norm_num)
theorem B952901 : Blo 634301 952901 := bbase (se 4 (by rfl) ⟨89334, by rfl⟩ : syracuseStep 952901 = 178669) (by norm_num)
theorem B952925 : Blo 634301 952925 := bbase (se 3 (by rfl) ⟨178673, by rfl⟩ : syracuseStep 952925 = 357347) (by norm_num)
theorem B2722405 : Blo 634301 2722405 := bbase (se 4 (by rfl) ⟨255225, by rfl⟩ : syracuseStep 2722405 = 510451) (by norm_num)
theorem B952949 : Blo 634301 952949 := bbase (se 5 (by rfl) ⟨44669, by rfl⟩ : syracuseStep 952949 = 89339) (by norm_num)
theorem B2296453 : Blo 634301 2296453 := bbase (se 4 (by rfl) ⟨215292, by rfl⟩ : syracuseStep 2296453 = 430585) (by norm_num)
theorem B952973 : Blo 634301 952973 := bbase (se 3 (by rfl) ⟨178682, by rfl⟩ : syracuseStep 952973 = 357365) (by norm_num)
theorem B952997 : Blo 634301 952997 := bbase (se 4 (by rfl) ⟨89343, by rfl⟩ : syracuseStep 952997 = 178687) (by norm_num)
theorem B953021 : Blo 634301 953021 := bbase (se 3 (by rfl) ⟨178691, by rfl⟩ : syracuseStep 953021 = 357383) (by norm_num)
theorem B953045 : Blo 634301 953045 := bbase (se 7 (by rfl) ⟨11168, by rfl⟩ : syracuseStep 953045 = 22337) (by norm_num)
theorem B953069 : Blo 634301 953069 := bbase (se 3 (by rfl) ⟨178700, by rfl⟩ : syracuseStep 953069 = 357401) (by norm_num)
theorem B1608437 : Blo 634301 1608437 := bbase (se 5 (by rfl) ⟨75395, by rfl⟩ : syracuseStep 1608437 = 150791) (by norm_num)
theorem B953093 : Blo 634301 953093 := bbase (se 4 (by rfl) ⟨89352, by rfl⟩ : syracuseStep 953093 = 178705) (by norm_num)
theorem B953117 : Blo 634301 953117 := bbase (se 3 (by rfl) ⟨178709, by rfl⟩ : syracuseStep 953117 = 357419) (by norm_num)
theorem B953141 : Blo 634301 953141 := bbase (se 5 (by rfl) ⟨44678, by rfl⟩ : syracuseStep 953141 = 89357) (by norm_num)
theorem B953165 : Blo 634301 953165 := bbase (se 3 (by rfl) ⟨178718, by rfl⟩ : syracuseStep 953165 = 357437) (by norm_num)
theorem B953189 : Blo 634301 953189 := bbase (se 4 (by rfl) ⟨89361, by rfl⟩ : syracuseStep 953189 = 178723) (by norm_num)
theorem B953213 : Blo 634301 953213 := bbase (se 3 (by rfl) ⟨178727, by rfl⟩ : syracuseStep 953213 = 357455) (by norm_num)
theorem B953237 : Blo 634301 953237 := bbase (se 6 (by rfl) ⟨22341, by rfl⟩ : syracuseStep 953237 = 44683) (by norm_num)
theorem B3050405 : Blo 634301 3050405 := bbase (se 4 (by rfl) ⟨285975, by rfl⟩ : syracuseStep 3050405 = 571951) (by norm_num)
theorem B953261 : Blo 634301 953261 := bbase (se 3 (by rfl) ⟨178736, by rfl⟩ : syracuseStep 953261 = 357473) (by norm_num)
theorem B3476405 : Blo 634301 3476405 := bbase (se 5 (by rfl) ⟨162956, by rfl⟩ : syracuseStep 3476405 = 325913) (by norm_num)
theorem B2034629 : Blo 634301 2034629 := bbase (se 4 (by rfl) ⟨190746, by rfl⟩ : syracuseStep 2034629 = 381493) (by norm_num)
theorem B953285 : Blo 634301 953285 := bbase (se 4 (by rfl) ⟨89370, by rfl⟩ : syracuseStep 953285 = 178741) (by norm_num)
theorem B1149893 : Blo 634301 1149893 := bbase (se 4 (by rfl) ⟨107802, by rfl⟩ : syracuseStep 1149893 = 215605) (by norm_num)
theorem B953309 : Blo 634301 953309 := bbase (se 3 (by rfl) ⟨178745, by rfl⟩ : syracuseStep 953309 = 357491) (by norm_num)
theorem B953333 : Blo 634301 953333 := bbase (se 5 (by rfl) ⟨44687, by rfl⟩ : syracuseStep 953333 = 89375) (by norm_num)
theorem B953357 : Blo 634301 953357 := bbase (se 3 (by rfl) ⟨178754, by rfl⟩ : syracuseStep 953357 = 357509) (by norm_num)
theorem B953381 : Blo 634301 953381 := bbase (se 4 (by rfl) ⟨89379, by rfl⟩ : syracuseStep 953381 = 178759) (by norm_num)
theorem B953405 : Blo 634301 953405 := bbase (se 3 (by rfl) ⟨178763, by rfl⟩ : syracuseStep 953405 = 357527) (by norm_num)
theorem B1608781 : Blo 634301 1608781 := bbase (se 3 (by rfl) ⟨301646, by rfl⟩ : syracuseStep 1608781 = 603293) (by norm_num)
theorem B953429 : Blo 634301 953429 := bbase (se 8 (by rfl) ⟨5586, by rfl⟩ : syracuseStep 953429 = 11173) (by norm_num)
theorem B953453 : Blo 634301 953453 := bbase (se 3 (by rfl) ⟨178772, by rfl⟩ : syracuseStep 953453 = 357545) (by norm_num)
theorem B2034821 : Blo 634301 2034821 := bbase (se 4 (by rfl) ⟨190764, by rfl⟩ : syracuseStep 2034821 = 381529) (by norm_num)
theorem B953477 : Blo 634301 953477 := bbase (se 4 (by rfl) ⟨89388, by rfl⟩ : syracuseStep 953477 = 178777) (by norm_num)
theorem B953501 : Blo 634301 953501 := bbase (se 3 (by rfl) ⟨178781, by rfl⟩ : syracuseStep 953501 = 357563) (by norm_num)
theorem B953525 : Blo 634301 953525 := bbase (se 5 (by rfl) ⟨44696, by rfl⟩ : syracuseStep 953525 = 89393) (by norm_num)
theorem B1608893 : Blo 634301 1608893 := bbase (se 3 (by rfl) ⟨301667, by rfl⟩ : syracuseStep 1608893 = 603335) (by norm_num)
theorem B953549 : Blo 634301 953549 := bbase (se 3 (by rfl) ⟨178790, by rfl⟩ : syracuseStep 953549 = 357581) (by norm_num)
theorem B3214565 : Blo 634301 3214565 := bbase (se 4 (by rfl) ⟨301365, by rfl⟩ : syracuseStep 3214565 = 602731) (by norm_num)
theorem B953573 : Blo 634301 953573 := bbase (se 4 (by rfl) ⟨89397, by rfl⟩ : syracuseStep 953573 = 178795) (by norm_num)
theorem B953597 : Blo 634301 953597 := bbase (se 3 (by rfl) ⟨178799, by rfl⟩ : syracuseStep 953597 = 357599) (by norm_num)
theorem B953621 : Blo 634301 953621 := bbase (se 6 (by rfl) ⟨22350, by rfl⟩ : syracuseStep 953621 = 44701) (by norm_num)
theorem B953645 : Blo 634301 953645 := bbase (se 3 (by rfl) ⟨178808, by rfl⟩ : syracuseStep 953645 = 357617) (by norm_num)
theorem B953669 : Blo 634301 953669 := bbase (se 4 (by rfl) ⟨89406, by rfl⟩ : syracuseStep 953669 = 178813) (by norm_num)
theorem B953693 : Blo 634301 953693 := bbase (se 3 (by rfl) ⟨178817, by rfl⟩ : syracuseStep 953693 = 357635) (by norm_num)
theorem B953717 : Blo 634301 953717 := bbase (se 5 (by rfl) ⟨44705, by rfl⟩ : syracuseStep 953717 = 89411) (by norm_num)
theorem B1609085 : Blo 634301 1609085 := bbase (se 3 (by rfl) ⟨301703, by rfl⟩ : syracuseStep 1609085 = 603407) (by norm_num)
theorem B953741 : Blo 634301 953741 := bbase (se 3 (by rfl) ⟨178826, by rfl⟩ : syracuseStep 953741 = 357653) (by norm_num)
theorem B953765 : Blo 634301 953765 := bbase (se 4 (by rfl) ⟨89415, by rfl⟩ : syracuseStep 953765 = 178831) (by norm_num)
theorem B953789 : Blo 634301 953789 := bbase (se 3 (by rfl) ⟨178835, by rfl⟩ : syracuseStep 953789 = 357671) (by norm_num)
theorem B953813 : Blo 634301 953813 := bbase (se 7 (by rfl) ⟨11177, by rfl⟩ : syracuseStep 953813 = 22355) (by norm_num)
theorem B953837 : Blo 634301 953837 := bbase (se 3 (by rfl) ⟨178844, by rfl⟩ : syracuseStep 953837 = 357689) (by norm_num)
theorem B953861 : Blo 634301 953861 := bbase (se 4 (by rfl) ⟨89424, by rfl⟩ : syracuseStep 953861 = 178849) (by norm_num)
theorem B953885 : Blo 634301 953885 := bbase (se 3 (by rfl) ⟨178853, by rfl⟩ : syracuseStep 953885 = 357707) (by norm_num)
theorem B2428453 : Blo 634301 2428453 := bbase (se 4 (by rfl) ⟨227667, by rfl⟩ : syracuseStep 2428453 = 455335) (by norm_num)
theorem B953909 : Blo 634301 953909 := bbase (se 5 (by rfl) ⟨44714, by rfl⟩ : syracuseStep 953909 = 89429) (by norm_num)
theorem B1019461 : Blo 634301 1019461 := bbase (se 4 (by rfl) ⟨95574, by rfl⟩ : syracuseStep 1019461 = 191149) (by norm_num)
theorem B953933 : Blo 634301 953933 := bbase (se 3 (by rfl) ⟨178862, by rfl⟩ : syracuseStep 953933 = 357725) (by norm_num)
theorem B953957 : Blo 634301 953957 := bbase (se 4 (by rfl) ⟨89433, by rfl⟩ : syracuseStep 953957 = 178867) (by norm_num)
theorem B953981 : Blo 634301 953981 := bbase (se 3 (by rfl) ⟨178871, by rfl⟩ : syracuseStep 953981 = 357743) (by norm_num)
theorem B954005 : Blo 634301 954005 := bbase (se 6 (by rfl) ⟨22359, by rfl⟩ : syracuseStep 954005 = 44719) (by norm_num)
theorem B954029 : Blo 634301 954029 := bbase (se 3 (by rfl) ⟨178880, by rfl⟩ : syracuseStep 954029 = 357761) (by norm_num)
theorem B954053 : Blo 634301 954053 := bbase (se 4 (by rfl) ⟨89442, by rfl⟩ : syracuseStep 954053 = 178885) (by norm_num)
theorem B1609429 : Blo 634301 1609429 := bbase (se 7 (by rfl) ⟨18860, by rfl⟩ : syracuseStep 1609429 = 37721) (by norm_num)
theorem B954077 : Blo 634301 954077 := bbase (se 3 (by rfl) ⟨178889, by rfl⟩ : syracuseStep 954077 = 357779) (by norm_num)
theorem B954101 : Blo 634301 954101 := bbase (se 5 (by rfl) ⟨44723, by rfl⟩ : syracuseStep 954101 = 89447) (by norm_num)
theorem B954125 : Blo 634301 954125 := bbase (se 3 (by rfl) ⟨178898, by rfl⟩ : syracuseStep 954125 = 357797) (by norm_num)
theorem B954149 : Blo 634301 954149 := bbase (se 4 (by rfl) ⟨89451, by rfl⟩ : syracuseStep 954149 = 178903) (by norm_num)
theorem B954173 : Blo 634301 954173 := bbase (se 3 (by rfl) ⟨178907, by rfl⟩ : syracuseStep 954173 = 357815) (by norm_num)
theorem B1609541 : Blo 634301 1609541 := bbase (se 4 (by rfl) ⟨150894, by rfl⟩ : syracuseStep 1609541 = 301789) (by norm_num)
theorem B954197 : Blo 634301 954197 := bbase (se 9 (by rfl) ⟨2795, by rfl⟩ : syracuseStep 954197 = 5591) (by norm_num)
theorem B954221 : Blo 634301 954221 := bbase (se 3 (by rfl) ⟨178916, by rfl⟩ : syracuseStep 954221 = 357833) (by norm_num)
theorem B954245 : Blo 634301 954245 := bbase (se 4 (by rfl) ⟨89460, by rfl⟩ : syracuseStep 954245 = 178921) (by norm_num)
theorem B954269 : Blo 634301 954269 := bbase (se 3 (by rfl) ⟨178925, by rfl⟩ : syracuseStep 954269 = 357851) (by norm_num)
theorem B954293 : Blo 634301 954293 := bbase (se 5 (by rfl) ⟨44732, by rfl⟩ : syracuseStep 954293 = 89465) (by norm_num)
theorem B954317 : Blo 634301 954317 := bbase (se 3 (by rfl) ⟨178934, by rfl⟩ : syracuseStep 954317 = 357869) (by norm_num)
theorem B954341 : Blo 634301 954341 := bbase (se 4 (by rfl) ⟨89469, by rfl⟩ : syracuseStep 954341 = 178939) (by norm_num)
theorem B954365 : Blo 634301 954365 := bbase (se 3 (by rfl) ⟨178943, by rfl⟩ : syracuseStep 954365 = 357887) (by norm_num)
theorem B1609733 : Blo 634301 1609733 := bbase (se 4 (by rfl) ⟨150912, by rfl⟩ : syracuseStep 1609733 = 301825) (by norm_num)
theorem B954389 : Blo 634301 954389 := bbase (se 6 (by rfl) ⟨22368, by rfl⟩ : syracuseStep 954389 = 44737) (by norm_num)
theorem B954413 : Blo 634301 954413 := bbase (se 3 (by rfl) ⟨178952, by rfl⟩ : syracuseStep 954413 = 357905) (by norm_num)
theorem B1085501 : Blo 634301 1085501 := bbase (se 3 (by rfl) ⟨203531, by rfl⟩ : syracuseStep 1085501 = 407063) (by norm_num)
theorem B954437 : Blo 634301 954437 := bbase (se 4 (by rfl) ⟨89478, by rfl⟩ : syracuseStep 954437 = 178957) (by norm_num)
theorem B954461 : Blo 634301 954461 := bbase (se 3 (by rfl) ⟨178961, by rfl⟩ : syracuseStep 954461 = 357923) (by norm_num)
theorem B2199653 : Blo 634301 2199653 := bbase (se 4 (by rfl) ⟨206217, by rfl⟩ : syracuseStep 2199653 = 412435) (by norm_num)
theorem B2789477 : Blo 634301 2789477 := bbase (se 4 (by rfl) ⟨261513, by rfl⟩ : syracuseStep 2789477 = 523027) (by norm_num)
theorem B954485 : Blo 634301 954485 := bbase (se 5 (by rfl) ⟨44741, by rfl⟩ : syracuseStep 954485 = 89483) (by norm_num)
theorem B725117 : Blo 634301 725117 := bbase (se 3 (by rfl) ⟨135959, by rfl⟩ : syracuseStep 725117 = 271919) (by norm_num)
theorem B954509 : Blo 634301 954509 := bbase (se 3 (by rfl) ⟨178970, by rfl⟩ : syracuseStep 954509 = 357941) (by norm_num)
theorem B954533 : Blo 634301 954533 := bbase (se 4 (by rfl) ⟨89487, by rfl⟩ : syracuseStep 954533 = 178975) (by norm_num)
theorem B954557 : Blo 634301 954557 := bbase (se 3 (by rfl) ⟨178979, by rfl⟩ : syracuseStep 954557 = 357959) (by norm_num)
theorem B954581 : Blo 634301 954581 := bbase (se 7 (by rfl) ⟨11186, by rfl⟩ : syracuseStep 954581 = 22373) (by norm_num)
theorem B1020133 : Blo 634301 1020133 := bbase (se 4 (by rfl) ⟨95637, by rfl⟩ : syracuseStep 1020133 = 191275) (by norm_num)
theorem B954605 : Blo 634301 954605 := bbase (se 3 (by rfl) ⟨178988, by rfl⟩ : syracuseStep 954605 = 357977) (by norm_num)
theorem B954629 : Blo 634301 954629 := bbase (se 4 (by rfl) ⟨89496, by rfl⟩ : syracuseStep 954629 = 178993) (by norm_num)
theorem B954653 : Blo 634301 954653 := bbase (se 3 (by rfl) ⟨178997, by rfl⟩ : syracuseStep 954653 = 357995) (by norm_num)
theorem B954677 : Blo 634301 954677 := bbase (se 5 (by rfl) ⟨44750, by rfl⟩ : syracuseStep 954677 = 89501) (by norm_num)
theorem B954701 : Blo 634301 954701 := bbase (se 3 (by rfl) ⟨179006, by rfl⟩ : syracuseStep 954701 = 358013) (by norm_num)
theorem B1610077 : Blo 634301 1610077 := bbase (se 3 (by rfl) ⟨301889, by rfl⟩ : syracuseStep 1610077 = 603779) (by norm_num)
theorem B954725 : Blo 634301 954725 := bbase (se 4 (by rfl) ⟨89505, by rfl⟩ : syracuseStep 954725 = 179011) (by norm_num)
theorem B954749 : Blo 634301 954749 := bbase (se 3 (by rfl) ⟨179015, by rfl⟩ : syracuseStep 954749 = 358031) (by norm_num)
theorem B1806725 : Blo 634301 1806725 := bbase (se 4 (by rfl) ⟨169380, by rfl⟩ : syracuseStep 1806725 = 338761) (by norm_num)
theorem B954773 : Blo 634301 954773 := bbase (se 6 (by rfl) ⟨22377, by rfl⟩ : syracuseStep 954773 = 44755) (by norm_num)
theorem B954797 : Blo 634301 954797 := bbase (se 3 (by rfl) ⟨179024, by rfl⟩ : syracuseStep 954797 = 358049) (by norm_num)
theorem B954821 : Blo 634301 954821 := bbase (se 4 (by rfl) ⟨89514, by rfl⟩ : syracuseStep 954821 = 179029) (by norm_num)
theorem B1610189 : Blo 634301 1610189 := bbase (se 3 (by rfl) ⟨301910, by rfl⟩ : syracuseStep 1610189 = 603821) (by norm_num)
theorem B954845 : Blo 634301 954845 := bbase (se 3 (by rfl) ⟨179033, by rfl⟩ : syracuseStep 954845 = 358067) (by norm_num)
theorem B725477 : Blo 634301 725477 := bbase (se 4 (by rfl) ⟨68013, by rfl⟩ : syracuseStep 725477 = 136027) (by norm_num)
theorem B3215861 : Blo 634301 3215861 := bbase (se 5 (by rfl) ⟨150743, by rfl⟩ : syracuseStep 3215861 = 301487) (by norm_num)
theorem B954869 : Blo 634301 954869 := bbase (se 5 (by rfl) ⟨44759, by rfl⟩ : syracuseStep 954869 = 89519) (by norm_num)
theorem B954893 : Blo 634301 954893 := bbase (se 3 (by rfl) ⟨179042, by rfl⟩ : syracuseStep 954893 = 358085) (by norm_num)
theorem B954917 : Blo 634301 954917 := bbase (se 4 (by rfl) ⟨89523, by rfl⟩ : syracuseStep 954917 = 179047) (by norm_num)
theorem B954941 : Blo 634301 954941 := bbase (se 3 (by rfl) ⟨179051, by rfl⟩ : syracuseStep 954941 = 358103) (by norm_num)
theorem B954965 : Blo 634301 954965 := bbase (se 8 (by rfl) ⟨5595, by rfl⟩ : syracuseStep 954965 = 11191) (by norm_num)
theorem B954989 : Blo 634301 954989 := bbase (se 3 (by rfl) ⟨179060, by rfl⟩ : syracuseStep 954989 = 358121) (by norm_num)
theorem B955013 : Blo 634301 955013 := bbase (se 4 (by rfl) ⟨89532, by rfl⟩ : syracuseStep 955013 = 179065) (by norm_num)
theorem B1544845 : Blo 634301 1544845 := bbase (se 3 (by rfl) ⟨289658, by rfl⟩ : syracuseStep 1544845 = 579317) (by norm_num)
theorem B1610381 : Blo 634301 1610381 := bbase (se 3 (by rfl) ⟨301946, by rfl⟩ : syracuseStep 1610381 = 603893) (by norm_num)
theorem B955037 : Blo 634301 955037 := bbase (se 3 (by rfl) ⟨179069, by rfl⟩ : syracuseStep 955037 = 358139) (by norm_num)
theorem B955061 : Blo 634301 955061 := bbase (se 5 (by rfl) ⟨44768, by rfl⟩ : syracuseStep 955061 = 89537) (by norm_num)
theorem B725701 : Blo 634301 725701 := bbase (se 4 (by rfl) ⟨68034, by rfl⟩ : syracuseStep 725701 = 136069) (by norm_num)
theorem B955085 : Blo 634301 955085 := bbase (se 3 (by rfl) ⟨179078, by rfl⟩ : syracuseStep 955085 = 358157) (by norm_num)
theorem B955109 : Blo 634301 955109 := bbase (se 4 (by rfl) ⟨89541, by rfl⟩ : syracuseStep 955109 = 179083) (by norm_num)
theorem B955133 : Blo 634301 955133 := bbase (se 3 (by rfl) ⟨179087, by rfl⟩ : syracuseStep 955133 = 358175) (by norm_num)
theorem B955157 : Blo 634301 955157 := bbase (se 6 (by rfl) ⟨22386, by rfl⟩ : syracuseStep 955157 = 44773) (by norm_num)
theorem B955181 : Blo 634301 955181 := bbase (se 3 (by rfl) ⟨179096, by rfl⟩ : syracuseStep 955181 = 358193) (by norm_num)
theorem B955205 : Blo 634301 955205 := bbase (se 4 (by rfl) ⟨89550, by rfl⟩ : syracuseStep 955205 = 179101) (by norm_num)
theorem B3674965 : Blo 634301 3674965 := bbase (se 9 (by rfl) ⟨10766, by rfl⟩ : syracuseStep 3674965 = 21533) (by norm_num)
theorem B955229 : Blo 634301 955229 := bbase (se 3 (by rfl) ⟨179105, by rfl⟩ : syracuseStep 955229 = 358211) (by norm_num)
theorem B955253 : Blo 634301 955253 := bbase (se 5 (by rfl) ⟨44777, by rfl⟩ : syracuseStep 955253 = 89555) (by norm_num)
theorem B955277 : Blo 634301 955277 := bbase (se 3 (by rfl) ⟨179114, by rfl⟩ : syracuseStep 955277 = 358229) (by norm_num)
theorem B955301 : Blo 634301 955301 := bbase (se 4 (by rfl) ⟨89559, by rfl⟩ : syracuseStep 955301 = 179119) (by norm_num)
theorem B1086389 : Blo 634301 1086389 := bbase (se 5 (by rfl) ⟨50924, by rfl⟩ : syracuseStep 1086389 = 101849) (by norm_num)
theorem B955325 : Blo 634301 955325 := bbase (se 3 (by rfl) ⟨179123, by rfl⟩ : syracuseStep 955325 = 358247) (by norm_num)
theorem B955349 : Blo 634301 955349 := bbase (se 7 (by rfl) ⟨11195, by rfl⟩ : syracuseStep 955349 = 22391) (by norm_num)
theorem B1610725 : Blo 634301 1610725 := bbase (se 4 (by rfl) ⟨151005, by rfl⟩ : syracuseStep 1610725 = 302011) (by norm_num)
theorem B955373 : Blo 634301 955373 := bbase (se 3 (by rfl) ⟨179132, by rfl⟩ : syracuseStep 955373 = 358265) (by norm_num)
theorem B955397 : Blo 634301 955397 := bbase (se 4 (by rfl) ⟨89568, by rfl⟩ : syracuseStep 955397 = 179137) (by norm_num)
theorem B955421 : Blo 634301 955421 := bbase (se 3 (by rfl) ⟨179141, by rfl⟩ : syracuseStep 955421 = 358283) (by norm_num)
theorem B1807397 : Blo 634301 1807397 := bbase (se 4 (by rfl) ⟨169443, by rfl⟩ : syracuseStep 1807397 = 338887) (by norm_num)
theorem B955445 : Blo 634301 955445 := bbase (se 5 (by rfl) ⟨44786, by rfl⟩ : syracuseStep 955445 = 89573) (by norm_num)
theorem B955469 : Blo 634301 955469 := bbase (se 3 (by rfl) ⟨179150, by rfl⟩ : syracuseStep 955469 = 358301) (by norm_num)
theorem B1610837 : Blo 634301 1610837 := bbase (se 8 (by rfl) ⟨9438, by rfl⟩ : syracuseStep 1610837 = 18877) (by norm_num)
theorem B955493 : Blo 634301 955493 := bbase (se 4 (by rfl) ⟨89577, by rfl⟩ : syracuseStep 955493 = 179155) (by norm_num)
theorem B955517 : Blo 634301 955517 := bbase (se 3 (by rfl) ⟨179159, by rfl⟩ : syracuseStep 955517 = 358319) (by norm_num)
theorem B955541 : Blo 634301 955541 := bbase (se 6 (by rfl) ⟨22395, by rfl⟩ : syracuseStep 955541 = 44791) (by norm_num)
theorem B955565 : Blo 634301 955565 := bbase (se 3 (by rfl) ⟨179168, by rfl⟩ : syracuseStep 955565 = 358337) (by norm_num)
theorem B955589 : Blo 634301 955589 := bbase (se 4 (by rfl) ⟨89586, by rfl⟩ : syracuseStep 955589 = 179173) (by norm_num)
theorem B1021133 : Blo 634301 1021133 := bbase (se 3 (by rfl) ⟨191462, by rfl⟩ : syracuseStep 1021133 = 382925) (by norm_num)
theorem B955613 : Blo 634301 955613 := bbase (se 3 (by rfl) ⟨179177, by rfl⟩ : syracuseStep 955613 = 358355) (by norm_num)
theorem B955637 : Blo 634301 955637 := bbase (se 5 (by rfl) ⟨44795, by rfl⟩ : syracuseStep 955637 = 89591) (by norm_num)
theorem B955661 : Blo 634301 955661 := bbase (se 3 (by rfl) ⟨179186, by rfl⟩ : syracuseStep 955661 = 358373) (by norm_num)
theorem B1611029 : Blo 634301 1611029 := bbase (se 6 (by rfl) ⟨37758, by rfl⟩ : syracuseStep 1611029 = 75517) (by norm_num)
theorem B955685 : Blo 634301 955685 := bbase (se 4 (by rfl) ⟨89595, by rfl⟩ : syracuseStep 955685 = 179191) (by norm_num)
theorem B955709 : Blo 634301 955709 := bbase (se 3 (by rfl) ⟨179195, by rfl⟩ : syracuseStep 955709 = 358391) (by norm_num)
theorem B955733 : Blo 634301 955733 := bbase (se 14 (by rfl) ⟨87, by rfl⟩ : syracuseStep 955733 = 175) (by norm_num)
theorem B955757 : Blo 634301 955757 := bbase (se 3 (by rfl) ⟨179204, by rfl⟩ : syracuseStep 955757 = 358409) (by norm_num)
theorem B955781 : Blo 634301 955781 := bbase (se 4 (by rfl) ⟨89604, by rfl⟩ : syracuseStep 955781 = 179209) (by norm_num)
theorem B955805 : Blo 634301 955805 := bbase (se 3 (by rfl) ⟨179213, by rfl⟩ : syracuseStep 955805 = 358427) (by norm_num)
theorem B955829 : Blo 634301 955829 := bbase (se 5 (by rfl) ⟨44804, by rfl⟩ : syracuseStep 955829 = 89609) (by norm_num)
theorem B955853 : Blo 634301 955853 := bbase (se 3 (by rfl) ⟨179222, by rfl⟩ : syracuseStep 955853 = 358445) (by norm_num)
theorem B1807829 : Blo 634301 1807829 := bbase (se 7 (by rfl) ⟨21185, by rfl⟩ : syracuseStep 1807829 = 42371) (by norm_num)
theorem B955877 : Blo 634301 955877 := bbase (se 4 (by rfl) ⟨89613, by rfl⟩ : syracuseStep 955877 = 179227) (by norm_num)
theorem B955901 : Blo 634301 955901 := bbase (se 3 (by rfl) ⟨179231, by rfl⟩ : syracuseStep 955901 = 358463) (by norm_num)
theorem B955925 : Blo 634301 955925 := bbase (se 6 (by rfl) ⟨22404, by rfl⟩ : syracuseStep 955925 = 44809) (by norm_num)
theorem B2725397 : Blo 634301 2725397 := bbase (se 6 (by rfl) ⟨63876, by rfl⟩ : syracuseStep 2725397 = 127753) (by norm_num)
theorem B1087013 : Blo 634301 1087013 := bbase (se 4 (by rfl) ⟨101907, by rfl⟩ : syracuseStep 1087013 = 203815) (by norm_num)
theorem B955949 : Blo 634301 955949 := bbase (se 3 (by rfl) ⟨179240, by rfl⟩ : syracuseStep 955949 = 358481) (by norm_num)
theorem B955973 : Blo 634301 955973 := bbase (se 4 (by rfl) ⟨89622, by rfl⟩ : syracuseStep 955973 = 179245) (by norm_num)
theorem B955997 : Blo 634301 955997 := bbase (se 3 (by rfl) ⟨179249, by rfl⟩ : syracuseStep 955997 = 358499) (by norm_num)
theorem B1611373 : Blo 634301 1611373 := bbase (se 3 (by rfl) ⟨302132, by rfl⟩ : syracuseStep 1611373 = 604265) (by norm_num)
theorem B3053173 : Blo 634301 3053173 := bbase (se 5 (by rfl) ⟨143117, by rfl⟩ : syracuseStep 3053173 = 286235) (by norm_num)
theorem B956021 : Blo 634301 956021 := bbase (se 5 (by rfl) ⟨44813, by rfl⟩ : syracuseStep 956021 = 89627) (by norm_num)
theorem B956045 : Blo 634301 956045 := bbase (se 3 (by rfl) ⟨179258, by rfl⟩ : syracuseStep 956045 = 358517) (by norm_num)
theorem B956069 : Blo 634301 956069 := bbase (se 4 (by rfl) ⟨89631, by rfl⟩ : syracuseStep 956069 = 179263) (by norm_num)
theorem B956093 : Blo 634301 956093 := bbase (se 3 (by rfl) ⟨179267, by rfl⟩ : syracuseStep 956093 = 358535) (by norm_num)
theorem B956117 : Blo 634301 956117 := bbase (se 7 (by rfl) ⟨11204, by rfl⟩ : syracuseStep 956117 = 22409) (by norm_num)
theorem B1611485 : Blo 634301 1611485 := bbase (se 3 (by rfl) ⟨302153, by rfl⟩ : syracuseStep 1611485 = 604307) (by norm_num)
theorem B956141 : Blo 634301 956141 := bbase (se 3 (by rfl) ⟨179276, by rfl⟩ : syracuseStep 956141 = 358553) (by norm_num)
theorem B3217157 : Blo 634301 3217157 := bbase (se 4 (by rfl) ⟨301608, by rfl⟩ : syracuseStep 3217157 = 603217) (by norm_num)
theorem B956165 : Blo 634301 956165 := bbase (se 4 (by rfl) ⟨89640, by rfl⟩ : syracuseStep 956165 = 179281) (by norm_num)
theorem B956189 : Blo 634301 956189 := bbase (se 3 (by rfl) ⟨179285, by rfl⟩ : syracuseStep 956189 = 358571) (by norm_num)
theorem B956213 : Blo 634301 956213 := bbase (se 5 (by rfl) ⟨44822, by rfl⟩ : syracuseStep 956213 = 89645) (by norm_num)
theorem B956237 : Blo 634301 956237 := bbase (se 3 (by rfl) ⟨179294, by rfl⟩ : syracuseStep 956237 = 358589) (by norm_num)
theorem B956261 : Blo 634301 956261 := bbase (se 4 (by rfl) ⟨89649, by rfl⟩ : syracuseStep 956261 = 179299) (by norm_num)
theorem B956285 : Blo 634301 956285 := bbase (se 3 (by rfl) ⟨179303, by rfl⟩ : syracuseStep 956285 = 358607) (by norm_num)
theorem B956309 : Blo 634301 956309 := bbase (se 6 (by rfl) ⟨22413, by rfl⟩ : syracuseStep 956309 = 44827) (by norm_num)
theorem B1611677 : Blo 634301 1611677 := bbase (se 3 (by rfl) ⟨302189, by rfl⟩ : syracuseStep 1611677 = 604379) (by norm_num)
theorem B956333 : Blo 634301 956333 := bbase (se 3 (by rfl) ⟨179312, by rfl⟩ : syracuseStep 956333 = 358625) (by norm_num)
theorem B956357 : Blo 634301 956357 := bbase (se 4 (by rfl) ⟨89658, by rfl⟩ : syracuseStep 956357 = 179317) (by norm_num)
theorem B956381 : Blo 634301 956381 := bbase (se 3 (by rfl) ⟨179321, by rfl⟩ : syracuseStep 956381 = 358643) (by norm_num)
theorem B956405 : Blo 634301 956405 := bbase (se 5 (by rfl) ⟨44831, by rfl⟩ : syracuseStep 956405 = 89663) (by norm_num)
theorem B956429 : Blo 634301 956429 := bbase (se 3 (by rfl) ⟨179330, by rfl⟩ : syracuseStep 956429 = 358661) (by norm_num)
theorem B956453 : Blo 634301 956453 := bbase (se 4 (by rfl) ⟨89667, by rfl⟩ : syracuseStep 956453 = 179335) (by norm_num)
theorem B956477 : Blo 634301 956477 := bbase (se 3 (by rfl) ⟨179339, by rfl⟩ : syracuseStep 956477 = 358679) (by norm_num)
theorem B956501 : Blo 634301 956501 := bbase (se 8 (by rfl) ⟨5604, by rfl⟩ : syracuseStep 956501 = 11209) (by norm_num)
theorem B956525 : Blo 634301 956525 := bbase (se 3 (by rfl) ⟨179348, by rfl⟩ : syracuseStep 956525 = 358697) (by norm_num)
theorem B3479669 : Blo 634301 3479669 := bbase (se 5 (by rfl) ⟨163109, by rfl⟩ : syracuseStep 3479669 = 326219) (by norm_num)
theorem B727169 : Blo 634301 727169 := bbase (se 2 (by rfl) ⟨272688, by rfl⟩ : syracuseStep 727169 = 545377) (by norm_num)
theorem B956549 : Blo 634301 956549 := bbase (se 4 (by rfl) ⟨89676, by rfl⟩ : syracuseStep 956549 = 179353) (by norm_num)
theorem B956573 : Blo 634301 956573 := bbase (se 3 (by rfl) ⟨179357, by rfl⟩ : syracuseStep 956573 = 358715) (by norm_num)
theorem B956597 : Blo 634301 956597 := bbase (se 5 (by rfl) ⟨44840, by rfl⟩ : syracuseStep 956597 = 89681) (by norm_num)
theorem B1808581 : Blo 634301 1808581 := bbase (se 4 (by rfl) ⟨169554, by rfl⟩ : syracuseStep 1808581 = 339109) (by norm_num)
theorem B956621 : Blo 634301 956621 := bbase (se 3 (by rfl) ⟨179366, by rfl⟩ : syracuseStep 956621 = 358733) (by norm_num)
theorem B956645 : Blo 634301 956645 := bbase (se 4 (by rfl) ⟨89685, by rfl⟩ : syracuseStep 956645 = 179371) (by norm_num)
theorem B1612021 : Blo 634301 1612021 := bbase (se 5 (by rfl) ⟨75563, by rfl⟩ : syracuseStep 1612021 = 151127) (by norm_num)
theorem B956669 : Blo 634301 956669 := bbase (se 3 (by rfl) ⟨179375, by rfl⟩ : syracuseStep 956669 = 358751) (by norm_num)
theorem B956693 : Blo 634301 956693 := bbase (se 6 (by rfl) ⟨22422, by rfl⟩ : syracuseStep 956693 = 44845) (by norm_num)
theorem B956717 : Blo 634301 956717 := bbase (se 3 (by rfl) ⟨179384, by rfl⟩ : syracuseStep 956717 = 358769) (by norm_num)
theorem B956741 : Blo 634301 956741 := bbase (se 4 (by rfl) ⟨89694, by rfl⟩ : syracuseStep 956741 = 179389) (by norm_num)
theorem B956765 : Blo 634301 956765 := bbase (se 3 (by rfl) ⟨179393, by rfl⟩ : syracuseStep 956765 = 358787) (by norm_num)
theorem B1612133 : Blo 634301 1612133 := bbase (se 4 (by rfl) ⟨151137, by rfl⟩ : syracuseStep 1612133 = 302275) (by norm_num)
theorem B956789 : Blo 634301 956789 := bbase (se 5 (by rfl) ⟨44849, by rfl⟩ : syracuseStep 956789 = 89699) (by norm_num)
theorem B956813 : Blo 634301 956813 := bbase (se 3 (by rfl) ⟨179402, by rfl⟩ : syracuseStep 956813 = 358805) (by norm_num)
theorem B956837 : Blo 634301 956837 := bbase (se 4 (by rfl) ⟨89703, by rfl⟩ : syracuseStep 956837 = 179407) (by norm_num)
theorem B956861 : Blo 634301 956861 := bbase (se 3 (by rfl) ⟨179411, by rfl⟩ : syracuseStep 956861 = 358823) (by norm_num)
theorem B956885 : Blo 634301 956885 := bbase (se 7 (by rfl) ⟨11213, by rfl⟩ : syracuseStep 956885 = 22427) (by norm_num)
theorem B727525 : Blo 634301 727525 := bbase (se 4 (by rfl) ⟨68205, by rfl⟩ : syracuseStep 727525 = 136411) (by norm_num)
theorem B956909 : Blo 634301 956909 := bbase (se 3 (by rfl) ⟨179420, by rfl⟩ : syracuseStep 956909 = 358841) (by norm_num)
theorem B956933 : Blo 634301 956933 := bbase (se 4 (by rfl) ⟨89712, by rfl⟩ : syracuseStep 956933 = 179425) (by norm_num)
theorem B2726405 : Blo 634301 2726405 := bbase (se 4 (by rfl) ⟨255600, by rfl⟩ : syracuseStep 2726405 = 511201) (by norm_num)
theorem B956957 : Blo 634301 956957 := bbase (se 3 (by rfl) ⟨179429, by rfl⟩ : syracuseStep 956957 = 358859) (by norm_num)
theorem B1612325 : Blo 634301 1612325 := bbase (se 4 (by rfl) ⟨151155, by rfl⟩ : syracuseStep 1612325 = 302311) (by norm_num)
theorem B956981 : Blo 634301 956981 := bbase (se 5 (by rfl) ⟨44858, by rfl⟩ : syracuseStep 956981 = 89717) (by norm_num)
theorem B957005 : Blo 634301 957005 := bbase (se 3 (by rfl) ⟨179438, by rfl⟩ : syracuseStep 957005 = 358877) (by norm_num)
theorem B957029 : Blo 634301 957029 := bbase (se 4 (by rfl) ⟨89721, by rfl⟩ : syracuseStep 957029 = 179443) (by norm_num)
theorem B957053 : Blo 634301 957053 := bbase (se 3 (by rfl) ⟨179447, by rfl⟩ : syracuseStep 957053 = 358895) (by norm_num)
theorem B2038421 : Blo 634301 2038421 := bbase (se 6 (by rfl) ⟨47775, by rfl⟩ : syracuseStep 2038421 = 95551) (by norm_num)
theorem B957077 : Blo 634301 957077 := bbase (se 6 (by rfl) ⟨22431, by rfl⟩ : syracuseStep 957077 = 44863) (by norm_num)
theorem B957101 : Blo 634301 957101 := bbase (se 3 (by rfl) ⟨179456, by rfl⟩ : syracuseStep 957101 = 358913) (by norm_num)
theorem B957125 : Blo 634301 957125 := bbase (se 4 (by rfl) ⟨89730, by rfl⟩ : syracuseStep 957125 = 179461) (by norm_num)
theorem B957149 : Blo 634301 957149 := bbase (se 3 (by rfl) ⟨179465, by rfl⟩ : syracuseStep 957149 = 358931) (by norm_num)
theorem B957173 : Blo 634301 957173 := bbase (se 5 (by rfl) ⟨44867, by rfl⟩ : syracuseStep 957173 = 89735) (by norm_num)
theorem B727813 : Blo 634301 727813 := bbase (se 4 (by rfl) ⟨68232, by rfl⟩ : syracuseStep 727813 = 136465) (by norm_num)
theorem B957197 : Blo 634301 957197 := bbase (se 3 (by rfl) ⟨179474, by rfl⟩ : syracuseStep 957197 = 358949) (by norm_num)
theorem B957221 : Blo 634301 957221 := bbase (se 4 (by rfl) ⟨89739, by rfl⟩ : syracuseStep 957221 = 179479) (by norm_num)
theorem B957245 : Blo 634301 957245 := bbase (se 3 (by rfl) ⟨179483, by rfl⟩ : syracuseStep 957245 = 358967) (by norm_num)
theorem B957269 : Blo 634301 957269 := bbase (se 9 (by rfl) ⟨2804, by rfl⟩ : syracuseStep 957269 = 5609) (by norm_num)
theorem B957293 : Blo 634301 957293 := bbase (se 3 (by rfl) ⟨179492, by rfl⟩ : syracuseStep 957293 = 358985) (by norm_num)
theorem B1612669 : Blo 634301 1612669 := bbase (se 3 (by rfl) ⟨302375, by rfl⟩ : syracuseStep 1612669 = 604751) (by norm_num)
theorem B957317 : Blo 634301 957317 := bbase (se 4 (by rfl) ⟨89748, by rfl⟩ : syracuseStep 957317 = 179497) (by norm_num)
theorem B957341 : Blo 634301 957341 := bbase (se 3 (by rfl) ⟨179501, by rfl⟩ : syracuseStep 957341 = 359003) (by norm_num)
theorem B957365 : Blo 634301 957365 := bbase (se 5 (by rfl) ⟨44876, by rfl⟩ : syracuseStep 957365 = 89753) (by norm_num)
theorem B957389 : Blo 634301 957389 := bbase (se 3 (by rfl) ⟨179510, by rfl⟩ : syracuseStep 957389 = 359021) (by norm_num)
theorem B1842149 : Blo 634301 1842149 := bbase (se 4 (by rfl) ⟨172701, by rfl⟩ : syracuseStep 1842149 = 345403) (by norm_num)
theorem B957413 : Blo 634301 957413 := bbase (se 4 (by rfl) ⟨89757, by rfl⟩ : syracuseStep 957413 = 179515) (by norm_num)
theorem B1612781 : Blo 634301 1612781 := bbase (se 3 (by rfl) ⟨302396, by rfl⟩ : syracuseStep 1612781 = 604793) (by norm_num)
theorem B957437 : Blo 634301 957437 := bbase (se 3 (by rfl) ⟨179519, by rfl⟩ : syracuseStep 957437 = 359039) (by norm_num)
theorem B1514501 : Blo 634301 1514501 := bbase (se 4 (by rfl) ⟨141984, by rfl⟩ : syracuseStep 1514501 = 283969) (by norm_num)
theorem B3218453 : Blo 634301 3218453 := bbase (se 6 (by rfl) ⟨75432, by rfl⟩ : syracuseStep 3218453 = 150865) (by norm_num)
theorem B1449085 : Blo 634301 1449085 := bbase (se 3 (by rfl) ⟨271703, by rfl⟩ : syracuseStep 1449085 = 543407) (by norm_num)
theorem B1612973 : Blo 634301 1612973 := bbase (se 3 (by rfl) ⟨302432, by rfl⟩ : syracuseStep 1612973 = 604865) (by norm_num)
theorem B5446997 : Blo 634301 5446997 := bbase (se 11 (by rfl) ⟨3989, by rfl⟩ : syracuseStep 5446997 = 7979) (by norm_num)
theorem B859613 : Blo 634301 859613 := bbase (se 3 (by rfl) ⟨161177, by rfl⟩ : syracuseStep 859613 = 322355) (by norm_num)
theorem B1613317 : Blo 634301 1613317 := bbase (se 4 (by rfl) ⟨151248, by rfl⟩ : syracuseStep 1613317 = 302497) (by norm_num)
theorem B1613429 : Blo 634301 1613429 := bbase (se 5 (by rfl) ⟨75629, by rfl⟩ : syracuseStep 1613429 = 151259) (by norm_num)
theorem B1089221 : Blo 634301 1089221 := bbase (se 4 (by rfl) ⟨102114, by rfl⟩ : syracuseStep 1089221 = 204229) (by norm_num)
theorem B1548077 : Blo 634301 1548077 := bbase (se 3 (by rfl) ⟨290264, by rfl⟩ : syracuseStep 1548077 = 580529) (by norm_num)
theorem B1613621 : Blo 634301 1613621 := bbase (se 5 (by rfl) ⟨75638, by rfl⟩ : syracuseStep 1613621 = 151277) (by norm_num)
theorem B1679197 : Blo 634301 1679197 := bbase (se 3 (by rfl) ⟨314849, by rfl⟩ : syracuseStep 1679197 = 629699) (by norm_num)
theorem B1613965 : Blo 634301 1613965 := bbase (se 3 (by rfl) ⟨302618, by rfl⟩ : syracuseStep 1613965 = 605237) (by norm_num)
theorem B1614077 : Blo 634301 1614077 := bbase (se 3 (by rfl) ⟨302639, by rfl⟩ : syracuseStep 1614077 = 605279) (by norm_num)
theorem B3219749 : Blo 634301 3219749 := bbase (se 4 (by rfl) ⟨301851, by rfl⟩ : syracuseStep 3219749 = 603703) (by norm_num)
theorem B6103349 : Blo 634301 6103349 := bbase (se 5 (by rfl) ⟨286094, by rfl⟩ : syracuseStep 6103349 = 572189) (by norm_num)
theorem B1286533 : Blo 634301 1286533 := bbase (se 4 (by rfl) ⟨120612, by rfl⟩ : syracuseStep 1286533 = 241225) (by norm_num)
theorem B4825493 : Blo 634301 4825493 := bbase (se 6 (by rfl) ⟨113097, by rfl⟩ : syracuseStep 4825493 = 226195) (by norm_num)
theorem B1614269 : Blo 634301 1614269 := bbase (se 3 (by rfl) ⟨302675, by rfl⟩ : syracuseStep 1614269 = 605351) (by norm_num)
theorem B27927125 : Blo 634301 27927125 := bbase (se 8 (by rfl) ⟨163635, by rfl⟩ : syracuseStep 27927125 = 327271) (by norm_num)
theorem B1614613 : Blo 634301 1614613 := bbase (se 6 (by rfl) ⟨37842, by rfl⟩ : syracuseStep 1614613 = 75685) (by norm_num)
theorem B2040677 : Blo 634301 2040677 := bbase (se 4 (by rfl) ⟨191313, by rfl⟩ : syracuseStep 2040677 = 382627) (by norm_num)
theorem B1614725 : Blo 634301 1614725 := bbase (se 4 (by rfl) ⟨151380, by rfl⟩ : syracuseStep 1614725 = 302761) (by norm_num)
theorem B1811429 : Blo 634301 1811429 := bbase (se 4 (by rfl) ⟨169821, by rfl⟩ : syracuseStep 1811429 = 339643) (by norm_num)
theorem B2040805 : Blo 634301 2040805 := bbase (se 4 (by rfl) ⟨191325, by rfl⟩ : syracuseStep 2040805 = 382651) (by norm_num)
theorem B1614917 : Blo 634301 1614917 := bbase (se 4 (by rfl) ⟨151398, by rfl⟩ : syracuseStep 1614917 = 302797) (by norm_num)
theorem B1221725 : Blo 634301 1221725 := bbase (se 3 (by rfl) ⟨229073, by rfl⟩ : syracuseStep 1221725 = 458147) (by norm_num)
theorem B1090789 : Blo 634301 1090789 := bbase (se 4 (by rfl) ⟨102261, by rfl⟩ : syracuseStep 1090789 = 204523) (by norm_num)
theorem B1615261 : Blo 634301 1615261 := bbase (se 3 (by rfl) ⟨302861, by rfl⟩ : syracuseStep 1615261 = 605723) (by norm_num)
theorem B1615373 : Blo 634301 1615373 := bbase (se 3 (by rfl) ⟨302882, by rfl⟩ : syracuseStep 1615373 = 605765) (by norm_num)
theorem B3221045 : Blo 634301 3221045 := bbase (se 5 (by rfl) ⟨150986, by rfl⟩ : syracuseStep 3221045 = 301973) (by norm_num)
theorem B6530645 : Blo 634301 6530645 := bbase (se 8 (by rfl) ⟨38265, by rfl⟩ : syracuseStep 6530645 = 76531) (by norm_num)
theorem B1615565 : Blo 634301 1615565 := bbase (se 3 (by rfl) ⟨302918, by rfl⟩ : syracuseStep 1615565 = 605837) (by norm_num)
theorem B3057365 : Blo 634301 3057365 := bbase (se 7 (by rfl) ⟨35828, by rfl⟩ : syracuseStep 3057365 = 71657) (by norm_num)
theorem B861949 : Blo 634301 861949 := bbase (se 3 (by rfl) ⟨161615, by rfl⟩ : syracuseStep 861949 = 323231) (by norm_num)
theorem B763673 : Blo 634301 763673 := bbase (se 2 (by rfl) ⟨286377, by rfl⟩ : syracuseStep 763673 = 572755) (by norm_num)
theorem B764005 : Blo 634301 764005 := bbase (se 4 (by rfl) ⟨71625, by rfl⟩ : syracuseStep 764005 = 143251) (by norm_num)
theorem B1812613 : Blo 634301 1812613 := bbase (se 4 (by rfl) ⟨169932, by rfl⟩ : syracuseStep 1812613 = 339865) (by norm_num)
theorem B862381 : Blo 634301 862381 := bbase (se 3 (by rfl) ⟨161696, by rfl⟩ : syracuseStep 862381 = 323393) (by norm_num)
theorem B8726741 : Blo 634301 8726741 := bbase (se 7 (by rfl) ⟨102266, by rfl⟩ : syracuseStep 8726741 = 204533) (by norm_num)
theorem B764149 : Blo 634301 764149 := bbase (se 5 (by rfl) ⟨35819, by rfl⟩ : syracuseStep 764149 = 71639) (by norm_num)
theorem B1812773 : Blo 634301 1812773 := bbase (se 4 (by rfl) ⟨169947, by rfl⟩ : syracuseStep 1812773 = 339895) (by norm_num)
theorem B1813013 : Blo 634301 1813013 := bbase (se 6 (by rfl) ⟨42492, by rfl⟩ : syracuseStep 1813013 = 84985) (by norm_num)
theorem B797245 : Blo 634301 797245 := bbase (se 3 (by rfl) ⟨149483, by rfl⟩ : syracuseStep 797245 = 298967) (by norm_num)
theorem B1288901 : Blo 634301 1288901 := bbase (se 4 (by rfl) ⟨120834, by rfl⟩ : syracuseStep 1288901 = 241669) (by norm_num)
theorem B1813205 : Blo 634301 1813205 := bbase (se 7 (by rfl) ⟨21248, by rfl⟩ : syracuseStep 1813205 = 42497) (by norm_num)
theorem B3222341 : Blo 634301 3222341 := bbase (se 4 (by rfl) ⟨302094, by rfl⟩ : syracuseStep 3222341 = 604189) (by norm_num)
theorem B2141045 : Blo 634301 2141045 := bbase (se 5 (by rfl) ⟨100361, by rfl⟩ : syracuseStep 2141045 = 200723) (by norm_num)
theorem B765173 : Blo 634301 765173 := bbase (se 5 (by rfl) ⟨35867, by rfl⟩ : syracuseStep 765173 = 71735) (by norm_num)
theorem B2141477 : Blo 634301 2141477 := bbase (se 4 (by rfl) ⟨200763, by rfl⟩ : syracuseStep 2141477 = 401527) (by norm_num)
theorem B1355069 : Blo 634301 1355069 := bbase (se 3 (by rfl) ⟨254075, by rfl⟩ : syracuseStep 1355069 = 508151) (by norm_num)
theorem B1224157 : Blo 634301 1224157 := bbase (se 3 (by rfl) ⟨229529, by rfl⟩ : syracuseStep 1224157 = 459059) (by norm_num)
theorem B10333781 : Blo 634301 10333781 := bbase (se 8 (by rfl) ⟨60549, by rfl⟩ : syracuseStep 10333781 = 121099) (by norm_num)
theorem B3092069 : Blo 634301 3092069 := bbase (se 4 (by rfl) ⟨289881, by rfl⟩ : syracuseStep 3092069 = 579763) (by norm_num)
theorem B1748645 : Blo 634301 1748645 := bbase (se 4 (by rfl) ⟨163935, by rfl⟩ : syracuseStep 1748645 = 327871) (by norm_num)
theorem B1814197 : Blo 634301 1814197 := bbase (se 5 (by rfl) ⟨85040, by rfl⟩ : syracuseStep 1814197 = 170081) (by norm_num)
theorem B2141909 : Blo 634301 2141909 := bbase (se 7 (by rfl) ⟨25100, by rfl⟩ : syracuseStep 2141909 = 50201) (by norm_num)
theorem B5812021 : Blo 634301 5812021 := bbase (se 5 (by rfl) ⟨272438, by rfl⟩ : syracuseStep 5812021 = 544877) (by norm_num)
theorem B2043701 : Blo 634301 2043701 := bbase (se 5 (by rfl) ⟨95798, by rfl⟩ : syracuseStep 2043701 = 191597) (by norm_num)
theorem B3223637 : Blo 634301 3223637 := bbase (se 8 (by rfl) ⟨18888, by rfl⟩ : syracuseStep 3223637 = 37777) (by norm_num)
theorem B1650797 : Blo 634301 1650797 := bbase (se 3 (by rfl) ⟨309524, by rfl⟩ : syracuseStep 1650797 = 619049) (by norm_num)
theorem B2142341 : Blo 634301 2142341 := bbase (se 4 (by rfl) ⟨200844, by rfl⟩ : syracuseStep 2142341 = 401689) (by norm_num)
theorem B1355933 : Blo 634301 1355933 := bbase (se 3 (by rfl) ⟨254237, by rfl⟩ : syracuseStep 1355933 = 508475) (by norm_num)
theorem B1454357 : Blo 634301 1454357 := bbase (se 6 (by rfl) ⟨34086, by rfl⟩ : syracuseStep 1454357 = 68173) (by norm_num)
theorem B1356077 : Blo 634301 1356077 := bbase (se 3 (by rfl) ⟨254264, by rfl⟩ : syracuseStep 1356077 = 508529) (by norm_num)
theorem B766369 : Blo 634301 766369 := bbase (se 2 (by rfl) ⟨287388, by rfl⟩ : syracuseStep 766369 = 574777) (by norm_num)
theorem B1716677 : Blo 634301 1716677 := bbase (se 4 (by rfl) ⟨160938, by rfl⟩ : syracuseStep 1716677 = 321877) (by norm_num)
theorem B766441 : Blo 634301 766441 := bbase (se 2 (by rfl) ⟨287415, by rfl⟩ : syracuseStep 766441 = 574831) (by norm_num)
theorem B4076021 : Blo 634301 4076021 := bbase (se 5 (by rfl) ⟨191063, by rfl⟩ : syracuseStep 4076021 = 382127) (by norm_num)
theorem B9777685 : Blo 634301 9777685 := bbase (se 6 (by rfl) ⟨229164, by rfl⟩ : syracuseStep 9777685 = 458329) (by norm_num)
theorem B2142773 : Blo 634301 2142773 := bbase (se 5 (by rfl) ⟨100442, by rfl⟩ : syracuseStep 2142773 = 200885) (by norm_num)
theorem B1815301 : Blo 634301 1815301 := bbase (se 4 (by rfl) ⟨170184, by rfl⟩ : syracuseStep 1815301 = 340369) (by norm_num)
theorem B3683285 : Blo 634301 3683285 := bbase (se 7 (by rfl) ⟨43163, by rfl⟩ : syracuseStep 3683285 = 86327) (by norm_num)
theorem B2143205 : Blo 634301 2143205 := bbase (se 4 (by rfl) ⟨200925, by rfl⟩ : syracuseStep 2143205 = 401851) (by norm_num)
theorem B1717237 : Blo 634301 1717237 := bbase (se 5 (by rfl) ⟨80495, by rfl⟩ : syracuseStep 1717237 = 160991) (by norm_num)
theorem B1356821 : Blo 634301 1356821 := bbase (se 6 (by rfl) ⟨31800, by rfl⟩ : syracuseStep 1356821 = 63601) (by norm_num)
theorem B1455341 : Blo 634301 1455341 := bbase (se 3 (by rfl) ⟨272876, by rfl⟩ : syracuseStep 1455341 = 545753) (by norm_num)
theorem B3257605 : Blo 634301 3257605 := bbase (se 4 (by rfl) ⟨305400, by rfl⟩ : syracuseStep 3257605 = 610801) (by norm_num)
theorem B3224933 : Blo 634301 3224933 := bbase (se 4 (by rfl) ⟨302337, by rfl⟩ : syracuseStep 3224933 = 604675) (by norm_num)
theorem B2143637 : Blo 634301 2143637 := bbase (se 6 (by rfl) ⟨50241, by rfl⟩ : syracuseStep 2143637 = 100483) (by norm_num)
theorem B1357573 : Blo 634301 1357573 := bbase (se 4 (by rfl) ⟨127272, by rfl⟩ : syracuseStep 1357573 = 254545) (by norm_num)
theorem B2144069 : Blo 634301 2144069 := bbase (se 4 (by rfl) ⟨201006, by rfl⟩ : syracuseStep 2144069 = 402013) (by norm_num)
theorem B1357717 : Blo 634301 1357717 := bbase (se 6 (by rfl) ⟨31821, by rfl⟩ : syracuseStep 1357717 = 63643) (by norm_num)
theorem B1554509 : Blo 634301 1554509 := bbase (se 3 (by rfl) ⟨291470, by rfl⟩ : syracuseStep 1554509 = 582941) (by norm_num)
theorem B1816805 : Blo 634301 1816805 := bbase (se 4 (by rfl) ⟨170325, by rfl⟩ : syracuseStep 1816805 = 340651) (by norm_num)
theorem B2144501 : Blo 634301 2144501 := bbase (se 5 (by rfl) ⟨100523, by rfl⟩ : syracuseStep 2144501 = 201047) (by norm_num)
theorem B1358093 : Blo 634301 1358093 := bbase (se 3 (by rfl) ⟨254642, by rfl⟩ : syracuseStep 1358093 = 509285) (by norm_num)
theorem B3062245 : Blo 634301 3062245 := bbase (se 4 (by rfl) ⟨287085, by rfl⟩ : syracuseStep 3062245 = 574171) (by norm_num)
theorem B3619349 : Blo 634301 3619349 := bbase (se 6 (by rfl) ⟨84828, by rfl⟩ : syracuseStep 3619349 = 169657) (by norm_num)
theorem B3226229 : Blo 634301 3226229 := bbase (se 5 (by rfl) ⟨151229, by rfl⟩ : syracuseStep 3226229 = 302459) (by norm_num)
theorem B1358461 : Blo 634301 1358461 := bbase (se 3 (by rfl) ⟨254711, by rfl⟩ : syracuseStep 1358461 = 509423) (by norm_num)
theorem B2144933 : Blo 634301 2144933 := bbase (se 4 (by rfl) ⟨201087, by rfl⟩ : syracuseStep 2144933 = 402175) (by norm_num)
theorem B1293005 : Blo 634301 1293005 := bbase (se 3 (by rfl) ⟨242438, by rfl⟩ : syracuseStep 1293005 = 484877) (by norm_num)
theorem B2178085 : Blo 634301 2178085 := bbase (se 4 (by rfl) ⟨204195, by rfl⟩ : syracuseStep 2178085 = 408391) (by norm_num)
theorem B736337 : Blo 634301 736337 := bbase (se 2 (by rfl) ⟨276126, by rfl⟩ : syracuseStep 736337 = 552253) (by norm_num)
theorem B2145365 : Blo 634301 2145365 := bbase (se 8 (by rfl) ⟨12570, by rfl⟩ : syracuseStep 2145365 = 25141) (by norm_num)
theorem B4078997 : Blo 634301 4078997 := bbase (se 6 (by rfl) ⟨95601, by rfl⟩ : syracuseStep 4078997 = 191203) (by norm_num)
theorem B2145797 : Blo 634301 2145797 := bbase (se 4 (by rfl) ⟨201168, by rfl⟩ : syracuseStep 2145797 = 402337) (by norm_num)
theorem B3227525 : Blo 634301 3227525 := bbase (se 4 (by rfl) ⟨302580, by rfl⟩ : syracuseStep 3227525 = 605161) (by norm_num)
theorem B2146229 : Blo 634301 2146229 := bbase (se 5 (by rfl) ⟨100604, by rfl⟩ : syracuseStep 2146229 = 201209) (by norm_num)
theorem B802801 : Blo 634301 802801 := bbase (se 2 (by rfl) ⟨301050, by rfl⟩ : syracuseStep 802801 = 602101) (by norm_num)
theorem B4833269 : Blo 634301 4833269 := bbase (se 5 (by rfl) ⟨226559, by rfl⟩ : syracuseStep 4833269 = 453119) (by norm_num)
theorem B1359965 : Blo 634301 1359965 := bbase (se 3 (by rfl) ⟨254993, by rfl⟩ : syracuseStep 1359965 = 509987) (by norm_num)
theorem B966773 : Blo 634301 966773 := bbase (se 5 (by rfl) ⟨45317, by rfl⟩ : syracuseStep 966773 = 90635) (by norm_num)
theorem B802973 : Blo 634301 802973 := bbase (se 3 (by rfl) ⟨150557, by rfl⟩ : syracuseStep 802973 = 301115) (by norm_num)
theorem B803029 : Blo 634301 803029 := bbase (se 7 (by rfl) ⟨9410, by rfl⟩ : syracuseStep 803029 = 18821) (by norm_num)
theorem B1360109 : Blo 634301 1360109 := bbase (se 3 (by rfl) ⟨255020, by rfl⟩ : syracuseStep 1360109 = 510041) (by norm_num)
theorem B803125 : Blo 634301 803125 := bbase (se 5 (by rfl) ⟨37646, by rfl⟩ : syracuseStep 803125 = 75293) (by norm_num)
theorem B2146661 : Blo 634301 2146661 := bbase (se 4 (by rfl) ⟨201249, by rfl⟩ : syracuseStep 2146661 = 402499) (by norm_num)
theorem B803297 : Blo 634301 803297 := bbase (se 2 (by rfl) ⟨301236, by rfl⟩ : syracuseStep 803297 = 602473) (by norm_num)
theorem B803353 : Blo 634301 803353 := bbase (se 2 (by rfl) ⟨301257, by rfl⟩ : syracuseStep 803353 = 602515) (by norm_num)
theorem B1360469 : Blo 634301 1360469 := bbase (se 8 (by rfl) ⟨7971, by rfl⟩ : syracuseStep 1360469 = 15943) (by norm_num)
theorem B836185 : Blo 634301 836185 := bbase (se 2 (by rfl) ⟨313569, by rfl⟩ : syracuseStep 836185 = 627139) (by norm_num)
theorem B803449 : Blo 634301 803449 := bbase (se 2 (by rfl) ⟨301293, by rfl⟩ : syracuseStep 803449 = 602587) (by norm_num)
theorem B2147093 : Blo 634301 2147093 := bbase (se 6 (by rfl) ⟨50322, by rfl⟩ : syracuseStep 2147093 = 100645) (by norm_num)
theorem B803621 : Blo 634301 803621 := bbase (se 4 (by rfl) ⟨75339, by rfl⟩ : syracuseStep 803621 = 150679) (by norm_num)
theorem B803677 : Blo 634301 803677 := bbase (se 3 (by rfl) ⟨150689, by rfl⟩ : syracuseStep 803677 = 301379) (by norm_num)
theorem B803773 : Blo 634301 803773 := bbase (se 3 (by rfl) ⟨150707, by rfl⟩ : syracuseStep 803773 = 301415) (by norm_num)
theorem B15516629 : Blo 634301 15516629 := bbase (se 7 (by rfl) ⟨181835, by rfl⟩ : syracuseStep 15516629 = 363671) (by norm_num)
theorem B803945 : Blo 634301 803945 := bbase (se 2 (by rfl) ⟨301479, by rfl⟩ : syracuseStep 803945 = 602959) (by norm_num)
theorem B3228821 : Blo 634301 3228821 := bbase (se 6 (by rfl) ⟨75675, by rfl⟩ : syracuseStep 3228821 = 151351) (by norm_num)
theorem B804001 : Blo 634301 804001 := bbase (se 2 (by rfl) ⟨301500, by rfl⟩ : syracuseStep 804001 = 603001) (by norm_num)
theorem B2147525 : Blo 634301 2147525 := bbase (se 4 (by rfl) ⟨201330, by rfl⟩ : syracuseStep 2147525 = 402661) (by norm_num)
theorem B804097 : Blo 634301 804097 := bbase (se 2 (by rfl) ⟨301536, by rfl⟩ : syracuseStep 804097 = 603073) (by norm_num)
theorem B804269 : Blo 634301 804269 := bbase (se 3 (by rfl) ⟨150800, by rfl⟩ : syracuseStep 804269 = 301601) (by norm_num)
theorem B1361357 : Blo 634301 1361357 := bbase (se 3 (by rfl) ⟨255254, by rfl⟩ : syracuseStep 1361357 = 510509) (by norm_num)
theorem B804325 : Blo 634301 804325 := bbase (se 4 (by rfl) ⟨75405, by rfl⟩ : syracuseStep 804325 = 150811) (by norm_num)
theorem B804421 : Blo 634301 804421 := bbase (se 4 (by rfl) ⟨75414, by rfl⟩ : syracuseStep 804421 = 150829) (by norm_num)
theorem B2475605 : Blo 634301 2475605 := bbase (se 8 (by rfl) ⟨14505, by rfl⟩ : syracuseStep 2475605 = 29011) (by norm_num)
theorem B2147957 : Blo 634301 2147957 := bbase (se 5 (by rfl) ⟨100685, by rfl⟩ : syracuseStep 2147957 = 201371) (by norm_num)
theorem B2410181 : Blo 634301 2410181 := bbase (se 4 (by rfl) ⟨225954, by rfl⟩ : syracuseStep 2410181 = 451909) (by norm_num)
theorem B1361605 : Blo 634301 1361605 := bbase (se 4 (by rfl) ⟨127650, by rfl⟩ : syracuseStep 1361605 = 255301) (by norm_num)
theorem B5424853 : Blo 634301 5424853 := bbase (se 7 (by rfl) ⟨63572, by rfl⟩ : syracuseStep 5424853 = 127145) (by norm_num)
theorem B804593 : Blo 634301 804593 := bbase (se 2 (by rfl) ⟨301722, by rfl⟩ : syracuseStep 804593 = 603445) (by norm_num)
theorem B1525501 : Blo 634301 1525501 := bbase (se 3 (by rfl) ⟨286031, by rfl⟩ : syracuseStep 1525501 = 572063) (by norm_num)
theorem B1427237 : Blo 634301 1427237 := bbase (se 4 (by rfl) ⟨133803, by rfl⟩ : syracuseStep 1427237 = 267607) (by norm_num)
theorem B804649 : Blo 634301 804649 := bbase (se 2 (by rfl) ⟨301743, by rfl⟩ : syracuseStep 804649 = 603487) (by norm_num)
theorem B1525549 : Blo 634301 1525549 := bbase (se 3 (by rfl) ⟨286040, by rfl⟩ : syracuseStep 1525549 = 572081) (by norm_num)
theorem B1427309 : Blo 634301 1427309 := bbase (se 3 (by rfl) ⟨267620, by rfl⟩ : syracuseStep 1427309 = 535241) (by norm_num)
theorem B804745 : Blo 634301 804745 := bbase (se 2 (by rfl) ⟨301779, by rfl⟩ : syracuseStep 804745 = 603559) (by norm_num)
theorem B1427381 : Blo 634301 1427381 := bbase (se 5 (by rfl) ⟨66908, by rfl⟩ : syracuseStep 1427381 = 133817) (by norm_num)
theorem B2410469 : Blo 634301 2410469 := bbase (se 4 (by rfl) ⟨225981, by rfl⟩ : syracuseStep 2410469 = 451963) (by norm_num)
theorem B1427453 : Blo 634301 1427453 := bbase (se 3 (by rfl) ⟨267647, by rfl⟩ : syracuseStep 1427453 = 535295) (by norm_num)
theorem B903197 : Blo 634301 903197 := bbase (se 3 (by rfl) ⟨169349, by rfl⟩ : syracuseStep 903197 = 338699) (by norm_num)
theorem B2148389 : Blo 634301 2148389 := bbase (se 4 (by rfl) ⟨201411, by rfl⟩ : syracuseStep 2148389 = 402823) (by norm_num)
theorem B804917 : Blo 634301 804917 := bbase (se 5 (by rfl) ⟨37730, by rfl⟩ : syracuseStep 804917 = 75461) (by norm_num)
theorem B1427525 : Blo 634301 1427525 := bbase (se 4 (by rfl) ⟨133830, by rfl⟩ : syracuseStep 1427525 = 267661) (by norm_num)
theorem B804973 : Blo 634301 804973 := bbase (se 3 (by rfl) ⟨150932, by rfl⟩ : syracuseStep 804973 = 301865) (by norm_num)
theorem B1427597 : Blo 634301 1427597 := bbase (se 3 (by rfl) ⟨267674, by rfl⟩ : syracuseStep 1427597 = 535349) (by norm_num)
theorem B1362109 : Blo 634301 1362109 := bbase (se 3 (by rfl) ⟨255395, by rfl⟩ : syracuseStep 1362109 = 510791) (by norm_num)
theorem B805069 : Blo 634301 805069 := bbase (se 3 (by rfl) ⟨150950, by rfl⟩ : syracuseStep 805069 = 301901) (by norm_num)
theorem B1427669 : Blo 634301 1427669 := bbase (se 7 (by rfl) ⟨16730, by rfl⟩ : syracuseStep 1427669 = 33461) (by norm_num)
theorem B1427741 : Blo 634301 1427741 := bbase (se 3 (by rfl) ⟨267701, by rfl⟩ : syracuseStep 1427741 = 535403) (by norm_num)
theorem B1427813 : Blo 634301 1427813 := bbase (se 4 (by rfl) ⟨133857, by rfl⟩ : syracuseStep 1427813 = 267715) (by norm_num)
theorem B805241 : Blo 634301 805241 := bbase (se 2 (by rfl) ⟨301965, by rfl⟩ : syracuseStep 805241 = 603931) (by norm_num)
theorem B1526165 : Blo 634301 1526165 := bbase (se 6 (by rfl) ⟨35769, by rfl⟩ : syracuseStep 1526165 = 71539) (by norm_num)
theorem B3230117 : Blo 634301 3230117 := bbase (se 4 (by rfl) ⟨302823, by rfl⟩ : syracuseStep 3230117 = 605647) (by norm_num)
theorem B1427885 : Blo 634301 1427885 := bbase (se 3 (by rfl) ⟨267728, by rfl⟩ : syracuseStep 1427885 = 535457) (by norm_num)
theorem B805297 : Blo 634301 805297 := bbase (se 2 (by rfl) ⟨301986, by rfl⟩ : syracuseStep 805297 = 603973) (by norm_num)
theorem B2148821 : Blo 634301 2148821 := bbase (se 7 (by rfl) ⟨25181, by rfl⟩ : syracuseStep 2148821 = 50363) (by norm_num)
theorem B1427957 : Blo 634301 1427957 := bbase (se 5 (by rfl) ⟨66935, by rfl⟩ : syracuseStep 1427957 = 133871) (by norm_num)
theorem B805393 : Blo 634301 805393 := bbase (se 2 (by rfl) ⟨302022, by rfl⟩ : syracuseStep 805393 = 604045) (by norm_num)
theorem B1428029 : Blo 634301 1428029 := bbase (se 3 (by rfl) ⟨267755, by rfl⟩ : syracuseStep 1428029 = 535511) (by norm_num)
theorem B3066437 : Blo 634301 3066437 := bbase (se 4 (by rfl) ⟨287478, by rfl⟩ : syracuseStep 3066437 = 574957) (by norm_num)
theorem B2574949 : Blo 634301 2574949 := bbase (se 4 (by rfl) ⟨241401, by rfl⟩ : syracuseStep 2574949 = 482803) (by norm_num)
theorem B1428101 : Blo 634301 1428101 := bbase (se 4 (by rfl) ⟨133884, by rfl⟩ : syracuseStep 1428101 = 267769) (by norm_num)
theorem B969365 : Blo 634301 969365 := bbase (se 6 (by rfl) ⟨22719, by rfl⟩ : syracuseStep 969365 = 45439) (by norm_num)
theorem B805565 : Blo 634301 805565 := bbase (se 3 (by rfl) ⟨151043, by rfl⟩ : syracuseStep 805565 = 302087) (by norm_num)
theorem B1428173 : Blo 634301 1428173 := bbase (se 3 (by rfl) ⟨267782, by rfl⟩ : syracuseStep 1428173 = 535565) (by norm_num)
theorem B1526509 : Blo 634301 1526509 := bbase (se 3 (by rfl) ⟨286220, by rfl⟩ : syracuseStep 1526509 = 572441) (by norm_num)
theorem B805621 : Blo 634301 805621 := bbase (se 5 (by rfl) ⟨37763, by rfl⟩ : syracuseStep 805621 = 75527) (by norm_num)
theorem B1428245 : Blo 634301 1428245 := bbase (se 6 (by rfl) ⟨33474, by rfl⟩ : syracuseStep 1428245 = 66949) (by norm_num)
theorem B805717 : Blo 634301 805717 := bbase (se 9 (by rfl) ⟨2360, by rfl⟩ : syracuseStep 805717 = 4721) (by norm_num)
theorem B1428317 : Blo 634301 1428317 := bbase (se 3 (by rfl) ⟨267809, by rfl⟩ : syracuseStep 1428317 = 535619) (by norm_num)
theorem B2149253 : Blo 634301 2149253 := bbase (se 4 (by rfl) ⟨201492, by rfl⟩ : syracuseStep 2149253 = 402985) (by norm_num)
theorem B871309 : Blo 634301 871309 := bbase (se 3 (by rfl) ⟨163370, by rfl⟩ : syracuseStep 871309 = 326741) (by norm_num)
theorem B1428389 : Blo 634301 1428389 := bbase (se 4 (by rfl) ⟨133911, by rfl⟩ : syracuseStep 1428389 = 267823) (by norm_num)
theorem B1526741 : Blo 634301 1526741 := bbase (se 7 (by rfl) ⟨17891, by rfl⟩ : syracuseStep 1526741 = 35783) (by norm_num)
theorem B1428461 : Blo 634301 1428461 := bbase (se 3 (by rfl) ⟨267836, by rfl⟩ : syracuseStep 1428461 = 535673) (by norm_num)
theorem B805889 : Blo 634301 805889 := bbase (se 2 (by rfl) ⟨302208, by rfl⟩ : syracuseStep 805889 = 604417) (by norm_num)
theorem B1428533 : Blo 634301 1428533 := bbase (se 5 (by rfl) ⟨66962, by rfl⟩ : syracuseStep 1428533 = 133925) (by norm_num)
theorem B1362997 : Blo 634301 1362997 := bbase (se 5 (by rfl) ⟨63890, by rfl⟩ : syracuseStep 1362997 = 127781) (by norm_num)
theorem B805945 : Blo 634301 805945 := bbase (se 2 (by rfl) ⟨302229, by rfl⟩ : syracuseStep 805945 = 604459) (by norm_num)
theorem B1428605 : Blo 634301 1428605 := bbase (se 3 (by rfl) ⟨267863, by rfl⟩ : syracuseStep 1428605 = 535727) (by norm_num)
theorem B2411653 : Blo 634301 2411653 := bbase (se 4 (by rfl) ⟨226092, by rfl⟩ : syracuseStep 2411653 = 452185) (by norm_num)
theorem B1526933 : Blo 634301 1526933 := bbase (se 6 (by rfl) ⟨35787, by rfl⟩ : syracuseStep 1526933 = 71575) (by norm_num)
theorem B806041 : Blo 634301 806041 := bbase (se 2 (by rfl) ⟨302265, by rfl⟩ : syracuseStep 806041 = 604531) (by norm_num)
theorem B1428677 : Blo 634301 1428677 := bbase (se 4 (by rfl) ⟨133938, by rfl⟩ : syracuseStep 1428677 = 267877) (by norm_num)
theorem B2608357 : Blo 634301 2608357 := bbase (se 4 (by rfl) ⟨244533, by rfl⟩ : syracuseStep 2608357 = 489067) (by norm_num)
theorem B1428749 : Blo 634301 1428749 := bbase (se 3 (by rfl) ⟨267890, by rfl⟩ : syracuseStep 1428749 = 535781) (by norm_num)
theorem B2149685 : Blo 634301 2149685 := bbase (se 5 (by rfl) ⟨100766, by rfl⟩ : syracuseStep 2149685 = 201533) (by norm_num)
theorem B806213 : Blo 634301 806213 := bbase (se 4 (by rfl) ⟨75582, by rfl⟩ : syracuseStep 806213 = 151165) (by norm_num)
theorem B1428821 : Blo 634301 1428821 := bbase (se 11 (by rfl) ⟨1046, by rfl⟩ : syracuseStep 1428821 = 2093) (by norm_num)
theorem B806269 : Blo 634301 806269 := bbase (se 3 (by rfl) ⟨151175, by rfl⟩ : syracuseStep 806269 = 302351) (by norm_num)
theorem B1428893 : Blo 634301 1428893 := bbase (se 3 (by rfl) ⟨267917, by rfl⟩ : syracuseStep 1428893 = 535835) (by norm_num)
theorem B904621 : Blo 634301 904621 := bbase (se 3 (by rfl) ⟨169616, by rfl⟩ : syracuseStep 904621 = 339233) (by norm_num)
theorem B2411957 : Blo 634301 2411957 := bbase (se 5 (by rfl) ⟨113060, by rfl⟩ : syracuseStep 2411957 = 226121) (by norm_num)
theorem B1527221 : Blo 634301 1527221 := bbase (se 5 (by rfl) ⟨71588, by rfl⟩ : syracuseStep 1527221 = 143177) (by norm_num)
theorem B806365 : Blo 634301 806365 := bbase (se 3 (by rfl) ⟨151193, by rfl⟩ : syracuseStep 806365 = 302387) (by norm_num)
theorem B1428965 : Blo 634301 1428965 := bbase (se 4 (by rfl) ⟨133965, by rfl⟩ : syracuseStep 1428965 = 267931) (by norm_num)
theorem B1429037 : Blo 634301 1429037 := bbase (se 3 (by rfl) ⟨267944, by rfl⟩ : syracuseStep 1429037 = 535889) (by norm_num)
theorem B1429109 : Blo 634301 1429109 := bbase (se 5 (by rfl) ⟨66989, by rfl⟩ : syracuseStep 1429109 = 133979) (by norm_num)
theorem B806537 : Blo 634301 806537 := bbase (se 2 (by rfl) ⟨302451, by rfl⟩ : syracuseStep 806537 = 604903) (by norm_num)
theorem B5426837 : Blo 634301 5426837 := bbase (se 6 (by rfl) ⟨127191, by rfl⟩ : syracuseStep 5426837 = 254383) (by norm_num)
theorem B1429181 : Blo 634301 1429181 := bbase (se 3 (by rfl) ⟨267971, by rfl⟩ : syracuseStep 1429181 = 535943) (by norm_num)
theorem B806593 : Blo 634301 806593 := bbase (se 2 (by rfl) ⟨302472, by rfl⟩ : syracuseStep 806593 = 604945) (by norm_num)
theorem B2150117 : Blo 634301 2150117 := bbase (se 4 (by rfl) ⟨201573, by rfl⟩ : syracuseStep 2150117 = 403147) (by norm_num)
theorem B1429253 : Blo 634301 1429253 := bbase (se 4 (by rfl) ⟨133992, by rfl⟩ : syracuseStep 1429253 = 267985) (by norm_num)
theorem B806689 : Blo 634301 806689 := bbase (se 2 (by rfl) ⟨302508, by rfl⟩ : syracuseStep 806689 = 605017) (by norm_num)
theorem B1429325 : Blo 634301 1429325 := bbase (se 3 (by rfl) ⟨267998, by rfl⟩ : syracuseStep 1429325 = 535997) (by norm_num)
theorem B13782869 : Blo 634301 13782869 := bbase (se 9 (by rfl) ⟨40379, by rfl⟩ : syracuseStep 13782869 = 80759) (by norm_num)
theorem B1429397 : Blo 634301 1429397 := bbase (se 6 (by rfl) ⟨33501, by rfl⟩ : syracuseStep 1429397 = 67003) (by norm_num)
theorem B806861 : Blo 634301 806861 := bbase (se 3 (by rfl) ⟨151286, by rfl⟩ : syracuseStep 806861 = 302573) (by norm_num)
theorem B1429469 : Blo 634301 1429469 := bbase (se 3 (by rfl) ⟨268025, by rfl⟩ : syracuseStep 1429469 = 536051) (by norm_num)
theorem B905213 : Blo 634301 905213 := bbase (se 3 (by rfl) ⟨169727, by rfl⟩ : syracuseStep 905213 = 339455) (by norm_num)
theorem B806917 : Blo 634301 806917 := bbase (se 4 (by rfl) ⟨75648, by rfl⟩ : syracuseStep 806917 = 151297) (by norm_num)
theorem B1429541 : Blo 634301 1429541 := bbase (se 4 (by rfl) ⟨134019, by rfl⟩ : syracuseStep 1429541 = 268039) (by norm_num)
theorem B905293 : Blo 634301 905293 := bbase (se 3 (by rfl) ⟨169742, by rfl⟩ : syracuseStep 905293 = 339485) (by norm_num)
theorem B807013 : Blo 634301 807013 := bbase (se 4 (by rfl) ⟨75657, by rfl⟩ : syracuseStep 807013 = 151315) (by norm_num)
theorem B1429613 : Blo 634301 1429613 := bbase (se 3 (by rfl) ⟨268052, by rfl⟩ : syracuseStep 1429613 = 536105) (by norm_num)
theorem B2150549 : Blo 634301 2150549 := bbase (se 6 (by rfl) ⟨50403, by rfl⟩ : syracuseStep 2150549 = 100807) (by norm_num)
theorem B1429685 : Blo 634301 1429685 := bbase (se 5 (by rfl) ⟨67016, by rfl⟩ : syracuseStep 1429685 = 134033) (by norm_num)
theorem B905413 : Blo 634301 905413 := bbase (se 4 (by rfl) ⟨84882, by rfl⟩ : syracuseStep 905413 = 169765) (by norm_num)
theorem B1429757 : Blo 634301 1429757 := bbase (se 3 (by rfl) ⟨268079, by rfl⟩ : syracuseStep 1429757 = 536159) (by norm_num)
theorem B807185 : Blo 634301 807185 := bbase (se 2 (by rfl) ⟨302694, by rfl⟩ : syracuseStep 807185 = 605389) (by norm_num)
theorem B905509 : Blo 634301 905509 := bbase (se 4 (by rfl) ⟨84891, by rfl⟩ : syracuseStep 905509 = 169783) (by norm_num)
theorem B1429829 : Blo 634301 1429829 := bbase (se 4 (by rfl) ⟨134046, by rfl⟩ : syracuseStep 1429829 = 268093) (by norm_num)
theorem B807241 : Blo 634301 807241 := bbase (se 2 (by rfl) ⟨302715, by rfl⟩ : syracuseStep 807241 = 605431) (by norm_num)
theorem B708949 : Blo 634301 708949 := bbase (se 10 (by rfl) ⟨1038, by rfl⟩ : syracuseStep 708949 = 2077) (by norm_num)
theorem B1429901 : Blo 634301 1429901 := bbase (se 3 (by rfl) ⟨268106, by rfl⟩ : syracuseStep 1429901 = 536213) (by norm_num)
theorem B807337 : Blo 634301 807337 := bbase (se 2 (by rfl) ⟨302751, by rfl⟩ : syracuseStep 807337 = 605503) (by norm_num)
theorem B1429973 : Blo 634301 1429973 := bbase (se 7 (by rfl) ⟨16757, by rfl⟩ : syracuseStep 1429973 = 33515) (by norm_num)
theorem B774653 : Blo 634301 774653 := bbase (se 3 (by rfl) ⟨145247, by rfl⟩ : syracuseStep 774653 = 290495) (by norm_num)
theorem B1430045 : Blo 634301 1430045 := bbase (se 3 (by rfl) ⟨268133, by rfl⟩ : syracuseStep 1430045 = 536267) (by norm_num)
theorem B2150981 : Blo 634301 2150981 := bbase (se 4 (by rfl) ⟨201654, by rfl⟩ : syracuseStep 2150981 = 403309) (by norm_num)
theorem B807509 : Blo 634301 807509 := bbase (se 8 (by rfl) ⟨4731, by rfl⟩ : syracuseStep 807509 = 9463) (by norm_num)
theorem B1430117 : Blo 634301 1430117 := bbase (se 4 (by rfl) ⟨134073, by rfl⟩ : syracuseStep 1430117 = 268147) (by norm_num)
theorem B807565 : Blo 634301 807565 := bbase (se 3 (by rfl) ⟨151418, by rfl⟩ : syracuseStep 807565 = 302837) (by norm_num)
theorem B1430189 : Blo 634301 1430189 := bbase (se 3 (by rfl) ⟨268160, by rfl⟩ : syracuseStep 1430189 = 536321) (by norm_num)
theorem B807661 : Blo 634301 807661 := bbase (se 3 (by rfl) ⟨151436, by rfl⟩ : syracuseStep 807661 = 302873) (by norm_num)
theorem B1430261 : Blo 634301 1430261 := bbase (se 5 (by rfl) ⟨67043, by rfl⟩ : syracuseStep 1430261 = 134087) (by norm_num)
theorem B906005 : Blo 634301 906005 := bbase (se 6 (by rfl) ⟨21234, by rfl⟩ : syracuseStep 906005 = 42469) (by norm_num)
theorem B1430333 : Blo 634301 1430333 := bbase (se 3 (by rfl) ⟨268187, by rfl⟩ : syracuseStep 1430333 = 536375) (by norm_num)
theorem B1430405 : Blo 634301 1430405 := bbase (se 4 (by rfl) ⟨134100, by rfl⟩ : syracuseStep 1430405 = 268201) (by norm_num)
theorem B807833 : Blo 634301 807833 := bbase (se 2 (by rfl) ⟨302937, by rfl⟩ : syracuseStep 807833 = 605875) (by norm_num)
theorem B644045 : Blo 634301 644045 := bbase (se 3 (by rfl) ⟨120758, by rfl⟩ : syracuseStep 644045 = 241517) (by norm_num)
theorem B1430477 : Blo 634301 1430477 := bbase (se 3 (by rfl) ⟨268214, by rfl⟩ : syracuseStep 1430477 = 536429) (by norm_num)
theorem B2151413 : Blo 634301 2151413 := bbase (se 5 (by rfl) ⟨100847, by rfl⟩ : syracuseStep 2151413 = 201695) (by norm_num)
theorem B1430549 : Blo 634301 1430549 := bbase (se 6 (by rfl) ⟨33528, by rfl⟩ : syracuseStep 1430549 = 67057) (by norm_num)
theorem B1430621 : Blo 634301 1430621 := bbase (se 3 (by rfl) ⟨268241, by rfl⟩ : syracuseStep 1430621 = 536483) (by norm_num)
theorem B1430693 : Blo 634301 1430693 := bbase (se 4 (by rfl) ⟨134127, by rfl⟩ : syracuseStep 1430693 = 268255) (by norm_num)
theorem B1430765 : Blo 634301 1430765 := bbase (se 3 (by rfl) ⟨268268, by rfl⟩ : syracuseStep 1430765 = 536537) (by norm_num)
theorem B1430837 : Blo 634301 1430837 := bbase (se 5 (by rfl) ⟨67070, by rfl⟩ : syracuseStep 1430837 = 134141) (by norm_num)
theorem B906557 : Blo 634301 906557 := bbase (se 3 (by rfl) ⟨169979, by rfl⟩ : syracuseStep 906557 = 339959) (by norm_num)
theorem B11621717 : Blo 634301 11621717 := bbase (se 18 (by rfl) ⟨66, by rfl⟩ : syracuseStep 11621717 = 133) (by norm_num)
theorem B1430909 : Blo 634301 1430909 := bbase (se 3 (by rfl) ⟨268295, by rfl⟩ : syracuseStep 1430909 = 536591) (by norm_num)
theorem B2151845 : Blo 634301 2151845 := bbase (se 4 (by rfl) ⟨201735, by rfl⟩ : syracuseStep 2151845 = 403471) (by norm_num)
theorem B1070509 : Blo 634301 1070509 := bbase (se 3 (by rfl) ⟨200720, by rfl⟩ : syracuseStep 1070509 = 401441) (by norm_num)
theorem B1430981 : Blo 634301 1430981 := bbase (se 4 (by rfl) ⟨134154, by rfl⟩ : syracuseStep 1430981 = 268309) (by norm_num)
theorem B2414069 : Blo 634301 2414069 := bbase (se 5 (by rfl) ⟨113159, by rfl⟩ : syracuseStep 2414069 = 226319) (by norm_num)
theorem B644609 : Blo 634301 644609 := bbase (se 2 (by rfl) ⟨241728, by rfl⟩ : syracuseStep 644609 = 483457) (by norm_num)
theorem B1070597 : Blo 634301 1070597 := bbase (se 4 (by rfl) ⟨100368, by rfl⟩ : syracuseStep 1070597 = 200737) (by norm_num)
theorem B1431053 : Blo 634301 1431053 := bbase (se 3 (by rfl) ⟨268322, by rfl⟩ : syracuseStep 1431053 = 536645) (by norm_num)
theorem B1431125 : Blo 634301 1431125 := bbase (se 8 (by rfl) ⟨8385, by rfl⟩ : syracuseStep 1431125 = 16771) (by norm_num)
theorem B1070725 : Blo 634301 1070725 := bbase (se 4 (by rfl) ⟨100380, by rfl⟩ : syracuseStep 1070725 = 200761) (by norm_num)
theorem B1431197 : Blo 634301 1431197 := bbase (se 3 (by rfl) ⟨268349, by rfl⟩ : syracuseStep 1431197 = 536699) (by norm_num)
theorem B1070813 : Blo 634301 1070813 := bbase (se 3 (by rfl) ⟨200777, by rfl⟩ : syracuseStep 1070813 = 401555) (by norm_num)
theorem B1431269 : Blo 634301 1431269 := bbase (se 4 (by rfl) ⟨134181, by rfl⟩ : syracuseStep 1431269 = 268363) (by norm_num)
theorem B2414357 : Blo 634301 2414357 := bbase (se 6 (by rfl) ⟨56586, by rfl⟩ : syracuseStep 2414357 = 113173) (by norm_num)
theorem B1431341 : Blo 634301 1431341 := bbase (se 3 (by rfl) ⟨268376, by rfl⟩ : syracuseStep 1431341 = 536753) (by norm_num)
theorem B677693 : Blo 634301 677693 := bbase (se 3 (by rfl) ⟨127067, by rfl⟩ : syracuseStep 677693 = 254135) (by norm_num)
theorem B2152277 : Blo 634301 2152277 := bbase (se 9 (by rfl) ⟨6305, by rfl⟩ : syracuseStep 2152277 = 12611) (by norm_num)
theorem B1070941 : Blo 634301 1070941 := bbase (se 3 (by rfl) ⟨200801, by rfl⟩ : syracuseStep 1070941 = 401603) (by norm_num)
theorem B1431413 : Blo 634301 1431413 := bbase (se 5 (by rfl) ⟨67097, by rfl⟩ : syracuseStep 1431413 = 134195) (by norm_num)
theorem B677765 : Blo 634301 677765 := bbase (se 4 (by rfl) ⟨63540, by rfl⟩ : syracuseStep 677765 = 127081) (by norm_num)
theorem B1071029 : Blo 634301 1071029 := bbase (se 5 (by rfl) ⟨50204, by rfl⟩ : syracuseStep 1071029 = 100409) (by norm_num)
theorem B1431485 : Blo 634301 1431485 := bbase (se 3 (by rfl) ⟨268403, by rfl⟩ : syracuseStep 1431485 = 536807) (by norm_num)
theorem B743425 : Blo 634301 743425 := bbase (se 2 (by rfl) ⟨278784, by rfl⟩ : syracuseStep 743425 = 557569) (by norm_num)
theorem B1431557 : Blo 634301 1431557 := bbase (se 4 (by rfl) ⟨134208, by rfl⟩ : syracuseStep 1431557 = 268417) (by norm_num)
theorem B907309 : Blo 634301 907309 := bbase (se 3 (by rfl) ⟨170120, by rfl⟩ : syracuseStep 907309 = 340241) (by norm_num)
theorem B2709557 : Blo 634301 2709557 := bbase (se 5 (by rfl) ⟨127010, by rfl⟩ : syracuseStep 2709557 = 254021) (by norm_num)
theorem B1071157 : Blo 634301 1071157 := bbase (se 5 (by rfl) ⟨50210, by rfl⟩ : syracuseStep 1071157 = 100421) (by norm_num)
theorem B677953 : Blo 634301 677953 := bbase (se 2 (by rfl) ⟨254232, by rfl⟩ : syracuseStep 677953 = 508465) (by norm_num)
theorem B1431629 : Blo 634301 1431629 := bbase (se 3 (by rfl) ⟨268430, by rfl⟩ : syracuseStep 1431629 = 536861) (by norm_num)
theorem B645229 : Blo 634301 645229 := bbase (se 3 (by rfl) ⟨120980, by rfl⟩ : syracuseStep 645229 = 241961) (by norm_num)
theorem B1071245 : Blo 634301 1071245 := bbase (se 3 (by rfl) ⟨200858, by rfl⟩ : syracuseStep 1071245 = 401717) (by norm_num)
theorem B1628309 : Blo 634301 1628309 := bbase (se 6 (by rfl) ⟨38163, by rfl⟩ : syracuseStep 1628309 = 76327) (by norm_num)
theorem B1431701 : Blo 634301 1431701 := bbase (se 6 (by rfl) ⟨33555, by rfl⟩ : syracuseStep 1431701 = 67111) (by norm_num)
theorem B1431773 : Blo 634301 1431773 := bbase (se 3 (by rfl) ⟨268457, by rfl⟩ : syracuseStep 1431773 = 536915) (by norm_num)
theorem B678137 : Blo 634301 678137 := bbase (se 2 (by rfl) ⟨254301, by rfl⟩ : syracuseStep 678137 = 508603) (by norm_num)
theorem B2152709 : Blo 634301 2152709 := bbase (se 4 (by rfl) ⟨201816, by rfl⟩ : syracuseStep 2152709 = 403633) (by norm_num)
theorem B1071373 : Blo 634301 1071373 := bbase (se 3 (by rfl) ⟨200882, by rfl⟩ : syracuseStep 1071373 = 401765) (by norm_num)
theorem B1431845 : Blo 634301 1431845 := bbase (se 4 (by rfl) ⟨134235, by rfl⟩ : syracuseStep 1431845 = 268471) (by norm_num)
theorem B1071461 : Blo 634301 1071461 := bbase (se 4 (by rfl) ⟨100449, by rfl⟩ : syracuseStep 1071461 = 200899) (by norm_num)
theorem B1431917 : Blo 634301 1431917 := bbase (se 3 (by rfl) ⟨268484, by rfl⟩ : syracuseStep 1431917 = 536969) (by norm_num)
theorem B1628549 : Blo 634301 1628549 := bbase (se 4 (by rfl) ⟨152676, by rfl⟩ : syracuseStep 1628549 = 305353) (by norm_num)
theorem B3627413 : Blo 634301 3627413 := bbase (se 6 (by rfl) ⟨85017, by rfl⟩ : syracuseStep 3627413 = 170035) (by norm_num)
theorem B7756181 : Blo 634301 7756181 := bbase (se 6 (by rfl) ⟨181785, by rfl⟩ : syracuseStep 7756181 = 363571) (by norm_num)
theorem B1431989 : Blo 634301 1431989 := bbase (se 5 (by rfl) ⟨67124, by rfl⟩ : syracuseStep 1431989 = 134249) (by norm_num)
theorem B1071589 : Blo 634301 1071589 := bbase (se 4 (by rfl) ⟨100461, by rfl⟩ : syracuseStep 1071589 = 200923) (by norm_num)
theorem B1432061 : Blo 634301 1432061 := bbase (se 3 (by rfl) ⟨268511, by rfl⟩ : syracuseStep 1432061 = 537023) (by norm_num)
theorem B1071677 : Blo 634301 1071677 := bbase (se 3 (by rfl) ⟨200939, by rfl⟩ : syracuseStep 1071677 = 401879) (by norm_num)
theorem B1432133 : Blo 634301 1432133 := bbase (se 4 (by rfl) ⟨134262, by rfl⟩ : syracuseStep 1432133 = 268525) (by norm_num)
theorem B1432205 : Blo 634301 1432205 := bbase (se 3 (by rfl) ⟨268538, by rfl⟩ : syracuseStep 1432205 = 537077) (by norm_num)
theorem B1399445 : Blo 634301 1399445 := bbase (se 6 (by rfl) ⟨32799, by rfl⟩ : syracuseStep 1399445 = 65599) (by norm_num)
theorem B2153141 : Blo 634301 2153141 := bbase (se 5 (by rfl) ⟨100928, by rfl⟩ : syracuseStep 2153141 = 201857) (by norm_num)
theorem B1071805 : Blo 634301 1071805 := bbase (se 3 (by rfl) ⟨200963, by rfl⟩ : syracuseStep 1071805 = 401927) (by norm_num)
theorem B1432277 : Blo 634301 1432277 := bbase (se 7 (by rfl) ⟨16784, by rfl⟩ : syracuseStep 1432277 = 33569) (by norm_num)
theorem B1071893 : Blo 634301 1071893 := bbase (se 6 (by rfl) ⟨25122, by rfl⟩ : syracuseStep 1071893 = 50245) (by norm_num)
theorem B1432349 : Blo 634301 1432349 := bbase (se 3 (by rfl) ⟨268565, by rfl⟩ : syracuseStep 1432349 = 537131) (by norm_num)
theorem B1530661 : Blo 634301 1530661 := bbase (se 4 (by rfl) ⟨143499, by rfl⟩ : syracuseStep 1530661 = 286999) (by norm_num)
theorem B777001 : Blo 634301 777001 := bbase (se 2 (by rfl) ⟨291375, by rfl⟩ : syracuseStep 777001 = 582751) (by norm_num)
theorem B908101 : Blo 634301 908101 := bbase (se 4 (by rfl) ⟨85134, by rfl⟩ : syracuseStep 908101 = 170269) (by norm_num)
theorem B1432421 : Blo 634301 1432421 := bbase (se 4 (by rfl) ⟨134289, by rfl⟩ : syracuseStep 1432421 = 268579) (by norm_num)
theorem B1072021 : Blo 634301 1072021 := bbase (se 6 (by rfl) ⟨25125, by rfl⟩ : syracuseStep 1072021 = 50251) (by norm_num)
theorem B1432493 : Blo 634301 1432493 := bbase (se 3 (by rfl) ⟨268592, by rfl⟩ : syracuseStep 1432493 = 537185) (by norm_num)
theorem B2415541 : Blo 634301 2415541 := bbase (se 5 (by rfl) ⟨113228, by rfl⟩ : syracuseStep 2415541 = 226457) (by norm_num)
theorem B646105 : Blo 634301 646105 := bbase (se 2 (by rfl) ⟨242289, by rfl⟩ : syracuseStep 646105 = 484579) (by norm_num)
theorem B678889 : Blo 634301 678889 := bbase (se 2 (by rfl) ⟨254583, by rfl⟩ : syracuseStep 678889 = 509167) (by norm_num)
theorem B646121 : Blo 634301 646121 := bbase (se 2 (by rfl) ⟨242295, by rfl⟩ : syracuseStep 646121 = 484591) (by norm_num)
theorem B1072109 : Blo 634301 1072109 := bbase (se 3 (by rfl) ⟨201020, by rfl⟩ : syracuseStep 1072109 = 402041) (by norm_num)
theorem B1432565 : Blo 634301 1432565 := bbase (se 5 (by rfl) ⟨67151, by rfl⟩ : syracuseStep 1432565 = 134303) (by norm_num)
theorem B1530893 : Blo 634301 1530893 := bbase (se 3 (by rfl) ⟨287042, by rfl⟩ : syracuseStep 1530893 = 574085) (by norm_num)
theorem B678961 : Blo 634301 678961 := bbase (se 2 (by rfl) ⟨254610, by rfl⟩ : syracuseStep 678961 = 509221) (by norm_num)
theorem B1432637 : Blo 634301 1432637 := bbase (se 3 (by rfl) ⟨268619, by rfl⟩ : syracuseStep 1432637 = 537239) (by norm_num)
theorem B2153573 : Blo 634301 2153573 := bbase (se 4 (by rfl) ⟨201897, by rfl⟩ : syracuseStep 2153573 = 403795) (by norm_num)
theorem B1072237 : Blo 634301 1072237 := bbase (se 3 (by rfl) ⟨201044, by rfl⟩ : syracuseStep 1072237 = 402089) (by norm_num)
theorem B1432709 : Blo 634301 1432709 := bbase (se 4 (by rfl) ⟨134316, by rfl⟩ : syracuseStep 1432709 = 268633) (by norm_num)
theorem B908437 : Blo 634301 908437 := bbase (se 6 (by rfl) ⟨21291, by rfl⟩ : syracuseStep 908437 = 42583) (by norm_num)
theorem B1531037 : Blo 634301 1531037 := bbase (se 3 (by rfl) ⟨287069, by rfl⟩ : syracuseStep 1531037 = 574139) (by norm_num)
theorem B1072325 : Blo 634301 1072325 := bbase (se 4 (by rfl) ⟨100530, by rfl⟩ : syracuseStep 1072325 = 201061) (by norm_num)
theorem B1432781 : Blo 634301 1432781 := bbase (se 3 (by rfl) ⟨268646, by rfl⟩ : syracuseStep 1432781 = 537293) (by norm_num)
theorem B744665 : Blo 634301 744665 := bbase (se 2 (by rfl) ⟨279249, by rfl⟩ : syracuseStep 744665 = 558499) (by norm_num)
theorem B679141 : Blo 634301 679141 := bbase (se 4 (by rfl) ⟨63669, by rfl⟩ : syracuseStep 679141 = 127339) (by norm_num)
theorem B2415845 : Blo 634301 2415845 := bbase (se 4 (by rfl) ⟨226485, by rfl⟩ : syracuseStep 2415845 = 452971) (by norm_num)
theorem B1432853 : Blo 634301 1432853 := bbase (se 6 (by rfl) ⟨33582, by rfl⟩ : syracuseStep 1432853 = 67165) (by norm_num)
theorem B4087093 : Blo 634301 4087093 := bbase (se 5 (by rfl) ⟨191582, by rfl⟩ : syracuseStep 4087093 = 383165) (by norm_num)
theorem B1072453 : Blo 634301 1072453 := bbase (se 4 (by rfl) ⟨100542, by rfl⟩ : syracuseStep 1072453 = 201085) (by norm_num)
theorem B1432925 : Blo 634301 1432925 := bbase (se 3 (by rfl) ⟨268673, by rfl⟩ : syracuseStep 1432925 = 537347) (by norm_num)
theorem B908653 : Blo 634301 908653 := bbase (se 3 (by rfl) ⟨170372, by rfl⟩ : syracuseStep 908653 = 340745) (by norm_num)
theorem B1531277 : Blo 634301 1531277 := bbase (se 3 (by rfl) ⟨287114, by rfl⟩ : syracuseStep 1531277 = 574229) (by norm_num)
theorem B1072541 : Blo 634301 1072541 := bbase (se 3 (by rfl) ⟨201101, by rfl⟩ : syracuseStep 1072541 = 402203) (by norm_num)
theorem B1432997 : Blo 634301 1432997 := bbase (se 4 (by rfl) ⟨134343, by rfl⟩ : syracuseStep 1432997 = 268687) (by norm_num)
theorem B1433069 : Blo 634301 1433069 := bbase (se 3 (by rfl) ⟨268700, by rfl⟩ : syracuseStep 1433069 = 537401) (by norm_num)
theorem B1105429 : Blo 634301 1105429 := bbase (se 6 (by rfl) ⟨25908, by rfl⟩ : syracuseStep 1105429 = 51817) (by norm_num)
theorem B2154005 : Blo 634301 2154005 := bbase (se 6 (by rfl) ⟨50484, by rfl⟩ : syracuseStep 2154005 = 100969) (by norm_num)
theorem B1072669 : Blo 634301 1072669 := bbase (se 3 (by rfl) ⟨201125, by rfl⟩ : syracuseStep 1072669 = 402251) (by norm_num)
theorem B1433141 : Blo 634301 1433141 := bbase (se 5 (by rfl) ⟨67178, by rfl⟩ : syracuseStep 1433141 = 134357) (by norm_num)
theorem B3628597 : Blo 634301 3628597 := bbase (se 5 (by rfl) ⟨170090, by rfl⟩ : syracuseStep 3628597 = 340181) (by norm_num)
theorem B4841045 : Blo 634301 4841045 := bbase (se 8 (by rfl) ⟨28365, by rfl⟩ : syracuseStep 4841045 = 56731) (by norm_num)
theorem B1072757 : Blo 634301 1072757 := bbase (se 5 (by rfl) ⟨50285, by rfl⟩ : syracuseStep 1072757 = 100571) (by norm_num)
theorem B1433213 : Blo 634301 1433213 := bbase (se 3 (by rfl) ⟨268727, by rfl⟩ : syracuseStep 1433213 = 537455) (by norm_num)
theorem B679585 : Blo 634301 679585 := bbase (se 2 (by rfl) ⟨254844, by rfl⟩ : syracuseStep 679585 = 509689) (by norm_num)
theorem B1433285 : Blo 634301 1433285 := bbase (se 4 (by rfl) ⟨134370, by rfl⟩ : syracuseStep 1433285 = 268741) (by norm_num)
theorem B1072885 : Blo 634301 1072885 := bbase (se 5 (by rfl) ⟨50291, by rfl⟩ : syracuseStep 1072885 = 100583) (by norm_num)
theorem B1433357 : Blo 634301 1433357 := bbase (se 3 (by rfl) ⟨268754, by rfl⟩ : syracuseStep 1433357 = 537509) (by norm_num)
theorem B679709 : Blo 634301 679709 := bbase (se 3 (by rfl) ⟨127445, by rfl⟩ : syracuseStep 679709 = 254891) (by norm_num)
theorem B2711333 : Blo 634301 2711333 := bbase (se 4 (by rfl) ⟨254187, by rfl⟩ : syracuseStep 2711333 = 508375) (by norm_num)
theorem B1072973 : Blo 634301 1072973 := bbase (se 3 (by rfl) ⟨201182, by rfl⟩ : syracuseStep 1072973 = 402365) (by norm_num)
theorem B1433429 : Blo 634301 1433429 := bbase (se 9 (by rfl) ⟨4199, by rfl⟩ : syracuseStep 1433429 = 8399) (by norm_num)
theorem B4972373 : Blo 634301 4972373 := bbase (se 9 (by rfl) ⟨14567, by rfl⟩ : syracuseStep 4972373 = 29135) (by norm_num)
theorem B1433501 : Blo 634301 1433501 := bbase (se 3 (by rfl) ⟨268781, by rfl⟩ : syracuseStep 1433501 = 537563) (by norm_num)
theorem B1073101 : Blo 634301 1073101 := bbase (se 3 (by rfl) ⟨201206, by rfl⟩ : syracuseStep 1073101 = 402413) (by norm_num)
theorem B1433573 : Blo 634301 1433573 := bbase (se 4 (by rfl) ⟨134397, by rfl⟩ : syracuseStep 1433573 = 268795) (by norm_num)
theorem B679961 : Blo 634301 679961 := bbase (se 2 (by rfl) ⟨254985, by rfl⟩ : syracuseStep 679961 = 509971) (by norm_num)
theorem B1073189 : Blo 634301 1073189 := bbase (se 4 (by rfl) ⟨100611, by rfl⟩ : syracuseStep 1073189 = 201223) (by norm_num)
theorem B1433645 : Blo 634301 1433645 := bbase (se 3 (by rfl) ⟨268808, by rfl⟩ : syracuseStep 1433645 = 537617) (by norm_num)
theorem B1204301 : Blo 634301 1204301 := bbase (se 3 (by rfl) ⟨225806, by rfl⟩ : syracuseStep 1204301 = 451613) (by norm_num)
theorem B1433717 : Blo 634301 1433717 := bbase (se 5 (by rfl) ⟨67205, by rfl⟩ : syracuseStep 1433717 = 134411) (by norm_num)
theorem B1532045 : Blo 634301 1532045 := bbase (se 3 (by rfl) ⟨287258, by rfl⟩ : syracuseStep 1532045 = 574517) (by norm_num)
theorem B1073317 : Blo 634301 1073317 := bbase (se 4 (by rfl) ⟨100623, by rfl⟩ : syracuseStep 1073317 = 201247) (by norm_num)
theorem B1433789 : Blo 634301 1433789 := bbase (se 3 (by rfl) ⟨268835, by rfl⟩ : syracuseStep 1433789 = 537671) (by norm_num)
theorem B1630405 : Blo 634301 1630405 := bbase (se 4 (by rfl) ⟨152850, by rfl⟩ : syracuseStep 1630405 = 305701) (by norm_num)
theorem B1204445 : Blo 634301 1204445 := bbase (se 3 (by rfl) ⟨225833, by rfl⟩ : syracuseStep 1204445 = 451667) (by norm_num)
theorem B1073405 : Blo 634301 1073405 := bbase (se 3 (by rfl) ⟨201263, by rfl⟩ : syracuseStep 1073405 = 402527) (by norm_num)
theorem B1433861 : Blo 634301 1433861 := bbase (se 4 (by rfl) ⟨134424, by rfl⟩ : syracuseStep 1433861 = 268849) (by norm_num)
theorem B3432725 : Blo 634301 3432725 := bbase (se 6 (by rfl) ⟨80454, by rfl⟩ : syracuseStep 3432725 = 160909) (by norm_num)
theorem B1433933 : Blo 634301 1433933 := bbase (se 3 (by rfl) ⟨268862, by rfl⟩ : syracuseStep 1433933 = 537725) (by norm_num)
theorem B2580821 : Blo 634301 2580821 := bbase (se 10 (by rfl) ⟨3780, by rfl⟩ : syracuseStep 2580821 = 7561) (by norm_num)
theorem B1073533 : Blo 634301 1073533 := bbase (se 3 (by rfl) ⟨201287, by rfl⟩ : syracuseStep 1073533 = 402575) (by norm_num)
theorem B1434005 : Blo 634301 1434005 := bbase (se 6 (by rfl) ⟨33609, by rfl⟩ : syracuseStep 1434005 = 67219) (by norm_num)
theorem B1073621 : Blo 634301 1073621 := bbase (se 7 (by rfl) ⟨12581, by rfl⟩ : syracuseStep 1073621 = 25163) (by norm_num)
theorem B680405 : Blo 634301 680405 := bbase (se 7 (by rfl) ⟨7973, by rfl⟩ : syracuseStep 680405 = 15947) (by norm_num)
theorem B1434077 : Blo 634301 1434077 := bbase (se 3 (by rfl) ⟨268889, by rfl⟩ : syracuseStep 1434077 = 537779) (by norm_num)
theorem B1204733 : Blo 634301 1204733 := bbase (se 3 (by rfl) ⟨225887, by rfl⟩ : syracuseStep 1204733 = 451775) (by norm_num)
theorem B1434149 : Blo 634301 1434149 := bbase (se 4 (by rfl) ⟨134451, by rfl⟩ : syracuseStep 1434149 = 268903) (by norm_num)
theorem B1073749 : Blo 634301 1073749 := bbase (se 8 (by rfl) ⟨6291, by rfl⟩ : syracuseStep 1073749 = 12583) (by norm_num)
theorem B1434221 : Blo 634301 1434221 := bbase (se 3 (by rfl) ⟨268916, by rfl⟩ : syracuseStep 1434221 = 537833) (by norm_num)
theorem B1204885 : Blo 634301 1204885 := bbase (se 6 (by rfl) ⟨28239, by rfl⟩ : syracuseStep 1204885 = 56479) (by norm_num)
theorem B1073837 : Blo 634301 1073837 := bbase (se 3 (by rfl) ⟨201344, by rfl⟩ : syracuseStep 1073837 = 402689) (by norm_num)
theorem B1434293 : Blo 634301 1434293 := bbase (se 5 (by rfl) ⟨67232, by rfl⟩ : syracuseStep 1434293 = 134465) (by norm_num)
theorem B680653 : Blo 634301 680653 := bbase (se 3 (by rfl) ⟨127622, by rfl⟩ : syracuseStep 680653 = 255245) (by norm_num)
theorem B1434365 : Blo 634301 1434365 := bbase (se 3 (by rfl) ⟨268943, by rfl⟩ : syracuseStep 1434365 = 537887) (by norm_num)
theorem B2712325 : Blo 634301 2712325 := bbase (se 4 (by rfl) ⟨254280, by rfl⟩ : syracuseStep 2712325 = 508561) (by norm_num)
theorem B1073965 : Blo 634301 1073965 := bbase (se 3 (by rfl) ⟨201368, by rfl⟩ : syracuseStep 1073965 = 402737) (by norm_num)
theorem B1434437 : Blo 634301 1434437 := bbase (se 4 (by rfl) ⟨134478, by rfl⟩ : syracuseStep 1434437 = 268957) (by norm_num)
theorem B713605 : Blo 634301 713605 := bbase (se 4 (by rfl) ⟨66900, by rfl⟩ : syracuseStep 713605 = 133801) (by norm_num)
theorem B1074053 : Blo 634301 1074053 := bbase (se 4 (by rfl) ⟨100692, by rfl⟩ : syracuseStep 1074053 = 201385) (by norm_num)
theorem B1434509 : Blo 634301 1434509 := bbase (se 3 (by rfl) ⟨268970, by rfl⟩ : syracuseStep 1434509 = 537941) (by norm_num)
theorem B713641 : Blo 634301 713641 := bbase (se 2 (by rfl) ⟨267615, by rfl⟩ : syracuseStep 713641 = 535231) (by norm_num)
theorem B1205189 : Blo 634301 1205189 := bbase (se 4 (by rfl) ⟨112986, by rfl⟩ : syracuseStep 1205189 = 225973) (by norm_num)
theorem B713677 : Blo 634301 713677 := bbase (se 3 (by rfl) ⟨133814, by rfl⟩ : syracuseStep 713677 = 267629) (by norm_num)
theorem B1434581 : Blo 634301 1434581 := bbase (se 7 (by rfl) ⟨16811, by rfl⟩ : syracuseStep 1434581 = 33623) (by norm_num)
theorem B713713 : Blo 634301 713713 := bbase (se 2 (by rfl) ⟨267642, by rfl⟩ : syracuseStep 713713 = 535285) (by norm_num)
theorem B1074181 : Blo 634301 1074181 := bbase (se 4 (by rfl) ⟨100704, by rfl⟩ : syracuseStep 1074181 = 201409) (by norm_num)
theorem B713749 : Blo 634301 713749 := bbase (se 6 (by rfl) ⟨16728, by rfl⟩ : syracuseStep 713749 = 33457) (by norm_num)
theorem B1434653 : Blo 634301 1434653 := bbase (se 3 (by rfl) ⟨268997, by rfl⟩ : syracuseStep 1434653 = 537995) (by norm_num)
theorem B713785 : Blo 634301 713785 := bbase (se 2 (by rfl) ⟨267669, by rfl⟩ : syracuseStep 713785 = 535339) (by norm_num)
theorem B713821 : Blo 634301 713821 := bbase (se 3 (by rfl) ⟨133841, by rfl⟩ : syracuseStep 713821 = 267683) (by norm_num)
theorem B1074269 : Blo 634301 1074269 := bbase (se 3 (by rfl) ⟨201425, by rfl⟩ : syracuseStep 1074269 = 402851) (by norm_num)
theorem B1434725 : Blo 634301 1434725 := bbase (se 4 (by rfl) ⟨134505, by rfl⟩ : syracuseStep 1434725 = 269011) (by norm_num)
theorem B713857 : Blo 634301 713857 := bbase (se 2 (by rfl) ⟨267696, by rfl⟩ : syracuseStep 713857 = 535393) (by norm_num)
theorem B681097 : Blo 634301 681097 := bbase (se 2 (by rfl) ⟨255411, by rfl⟩ : syracuseStep 681097 = 510823) (by norm_num)
theorem B713893 : Blo 634301 713893 := bbase (se 4 (by rfl) ⟨66927, by rfl⟩ : syracuseStep 713893 = 133855) (by norm_num)
theorem B1434797 : Blo 634301 1434797 := bbase (se 3 (by rfl) ⟨269024, by rfl⟩ : syracuseStep 1434797 = 538049) (by norm_num)
theorem B681157 : Blo 634301 681157 := bbase (se 4 (by rfl) ⟨63858, by rfl⟩ : syracuseStep 681157 = 127717) (by norm_num)
theorem B713929 : Blo 634301 713929 := bbase (se 2 (by rfl) ⟨267723, by rfl⟩ : syracuseStep 713929 = 535447) (by norm_num)
theorem B1074397 : Blo 634301 1074397 := bbase (se 3 (by rfl) ⟨201449, by rfl⟩ : syracuseStep 1074397 = 402899) (by norm_num)
theorem B713965 : Blo 634301 713965 := bbase (se 3 (by rfl) ⟨133868, by rfl⟩ : syracuseStep 713965 = 267737) (by norm_num)
theorem B1434869 : Blo 634301 1434869 := bbase (se 5 (by rfl) ⟨67259, by rfl⟩ : syracuseStep 1434869 = 134519) (by norm_num)
theorem B714001 : Blo 634301 714001 := bbase (se 2 (by rfl) ⟨267750, by rfl⟩ : syracuseStep 714001 = 535501) (by norm_num)
theorem B2417957 : Blo 634301 2417957 := bbase (se 4 (by rfl) ⟨226683, by rfl⟩ : syracuseStep 2417957 = 453367) (by norm_num)
theorem B714037 : Blo 634301 714037 := bbase (se 5 (by rfl) ⟨33470, by rfl⟩ : syracuseStep 714037 = 66941) (by norm_num)
theorem B1074485 : Blo 634301 1074485 := bbase (se 5 (by rfl) ⟨50366, by rfl⟩ : syracuseStep 1074485 = 100733) (by norm_num)
theorem B1434941 : Blo 634301 1434941 := bbase (se 3 (by rfl) ⟨269051, by rfl⟩ : syracuseStep 1434941 = 538103) (by norm_num)
theorem B714073 : Blo 634301 714073 := bbase (se 2 (by rfl) ⟨267777, by rfl⟩ : syracuseStep 714073 = 535555) (by norm_num)
theorem B714109 : Blo 634301 714109 := bbase (se 3 (by rfl) ⟨133895, by rfl⟩ : syracuseStep 714109 = 267791) (by norm_num)
theorem B1435013 : Blo 634301 1435013 := bbase (se 4 (by rfl) ⟨134532, by rfl⟩ : syracuseStep 1435013 = 269065) (by norm_num)
theorem B714145 : Blo 634301 714145 := bbase (se 2 (by rfl) ⟨267804, by rfl⟩ : syracuseStep 714145 = 535609) (by norm_num)
theorem B1074613 : Blo 634301 1074613 := bbase (se 5 (by rfl) ⟨50372, by rfl⟩ : syracuseStep 1074613 = 100745) (by norm_num)
theorem B714181 : Blo 634301 714181 := bbase (se 4 (by rfl) ⟨66954, by rfl⟩ : syracuseStep 714181 = 133909) (by norm_num)
theorem B1435085 : Blo 634301 1435085 := bbase (se 3 (by rfl) ⟨269078, by rfl⟩ : syracuseStep 1435085 = 538157) (by norm_num)
theorem B714217 : Blo 634301 714217 := bbase (se 2 (by rfl) ⟨267831, by rfl⟩ : syracuseStep 714217 = 535663) (by norm_num)
theorem B1533421 : Blo 634301 1533421 := bbase (se 3 (by rfl) ⟨287516, by rfl⟩ : syracuseStep 1533421 = 575033) (by norm_num)
theorem B3630581 : Blo 634301 3630581 := bbase (se 5 (by rfl) ⟨170183, by rfl⟩ : syracuseStep 3630581 = 340367) (by norm_num)
theorem B681473 : Blo 634301 681473 := bbase (se 2 (by rfl) ⟨255552, by rfl⟩ : syracuseStep 681473 = 511105) (by norm_num)
theorem B714253 : Blo 634301 714253 := bbase (se 3 (by rfl) ⟨133922, by rfl⟩ : syracuseStep 714253 = 267845) (by norm_num)
theorem B1074701 : Blo 634301 1074701 := bbase (se 3 (by rfl) ⟨201506, by rfl⟩ : syracuseStep 1074701 = 403013) (by norm_num)
theorem B1435157 : Blo 634301 1435157 := bbase (se 6 (by rfl) ⟨33636, by rfl⟩ : syracuseStep 1435157 = 67273) (by norm_num)
theorem B714289 : Blo 634301 714289 := bbase (se 2 (by rfl) ⟨267858, by rfl⟩ : syracuseStep 714289 = 535717) (by norm_num)
theorem B2418245 : Blo 634301 2418245 := bbase (se 4 (by rfl) ⟨226710, by rfl⟩ : syracuseStep 2418245 = 453421) (by norm_num)
theorem B714325 : Blo 634301 714325 := bbase (se 8 (by rfl) ⟨4185, by rfl⟩ : syracuseStep 714325 = 8371) (by norm_num)
theorem B1435229 : Blo 634301 1435229 := bbase (se 3 (by rfl) ⟨269105, by rfl⟩ : syracuseStep 1435229 = 538211) (by norm_num)
theorem B714361 : Blo 634301 714361 := bbase (se 2 (by rfl) ⟨267885, by rfl⟩ : syracuseStep 714361 = 535771) (by norm_num)
theorem B1074829 : Blo 634301 1074829 := bbase (se 3 (by rfl) ⟨201530, by rfl⟩ : syracuseStep 1074829 = 403061) (by norm_num)
theorem B714397 : Blo 634301 714397 := bbase (se 3 (by rfl) ⟨133949, by rfl⟩ : syracuseStep 714397 = 267899) (by norm_num)
theorem B1435301 : Blo 634301 1435301 := bbase (se 4 (by rfl) ⟨134559, by rfl⟩ : syracuseStep 1435301 = 269119) (by norm_num)
theorem B1205941 : Blo 634301 1205941 := bbase (se 5 (by rfl) ⟨56528, by rfl⟩ : syracuseStep 1205941 = 113057) (by norm_num)
theorem B714433 : Blo 634301 714433 := bbase (se 2 (by rfl) ⟨267912, by rfl⟩ : syracuseStep 714433 = 535825) (by norm_num)
theorem B714469 : Blo 634301 714469 := bbase (se 4 (by rfl) ⟨66981, by rfl⟩ : syracuseStep 714469 = 133963) (by norm_num)
theorem B1074917 : Blo 634301 1074917 := bbase (se 4 (by rfl) ⟨100773, by rfl⟩ : syracuseStep 1074917 = 201547) (by norm_num)
theorem B1435373 : Blo 634301 1435373 := bbase (se 3 (by rfl) ⟨269132, by rfl⟩ : syracuseStep 1435373 = 538265) (by norm_num)
theorem B1632005 : Blo 634301 1632005 := bbase (se 4 (by rfl) ⟨153000, by rfl⟩ : syracuseStep 1632005 = 306001) (by norm_num)
theorem B714505 : Blo 634301 714505 := bbase (se 2 (by rfl) ⟨267939, by rfl⟩ : syracuseStep 714505 = 535879) (by norm_num)
theorem B714541 : Blo 634301 714541 := bbase (se 3 (by rfl) ⟨133976, by rfl⟩ : syracuseStep 714541 = 267953) (by norm_num)
theorem B1435445 : Blo 634301 1435445 := bbase (se 5 (by rfl) ⟨67286, by rfl⟩ : syracuseStep 1435445 = 134573) (by norm_num)
theorem B1206085 : Blo 634301 1206085 := bbase (se 4 (by rfl) ⟨113070, by rfl⟩ : syracuseStep 1206085 = 226141) (by norm_num)
theorem B714577 : Blo 634301 714577 := bbase (se 2 (by rfl) ⟨267966, by rfl⟩ : syracuseStep 714577 = 535933) (by norm_num)
theorem B1075045 : Blo 634301 1075045 := bbase (se 4 (by rfl) ⟨100785, by rfl⟩ : syracuseStep 1075045 = 201571) (by norm_num)
theorem B714613 : Blo 634301 714613 := bbase (se 5 (by rfl) ⟨33497, by rfl⟩ : syracuseStep 714613 = 66995) (by norm_num)
theorem B1435517 : Blo 634301 1435517 := bbase (se 3 (by rfl) ⟨269159, by rfl⟩ : syracuseStep 1435517 = 538319) (by norm_num)
theorem B714649 : Blo 634301 714649 := bbase (se 2 (by rfl) ⟨267993, by rfl⟩ : syracuseStep 714649 = 535987) (by norm_num)
theorem B714685 : Blo 634301 714685 := bbase (se 3 (by rfl) ⟨134003, by rfl⟩ : syracuseStep 714685 = 268007) (by norm_num)
theorem B1075133 : Blo 634301 1075133 := bbase (se 3 (by rfl) ⟨201587, by rfl⟩ : syracuseStep 1075133 = 403175) (by norm_num)
theorem B1435589 : Blo 634301 1435589 := bbase (se 4 (by rfl) ⟨134586, by rfl⟩ : syracuseStep 1435589 = 269173) (by norm_num)
theorem B714721 : Blo 634301 714721 := bbase (se 2 (by rfl) ⟨268020, by rfl⟩ : syracuseStep 714721 = 536041) (by norm_num)
theorem B1206245 : Blo 634301 1206245 := bbase (se 4 (by rfl) ⟨113085, by rfl⟩ : syracuseStep 1206245 = 226171) (by norm_num)
theorem B714757 : Blo 634301 714757 := bbase (se 4 (by rfl) ⟨67008, by rfl⟩ : syracuseStep 714757 = 134017) (by norm_num)
theorem B1435661 : Blo 634301 1435661 := bbase (se 3 (by rfl) ⟨269186, by rfl⟩ : syracuseStep 1435661 = 538373) (by norm_num)
theorem B714793 : Blo 634301 714793 := bbase (se 2 (by rfl) ⟨268047, by rfl⟩ : syracuseStep 714793 = 536095) (by norm_num)
theorem B1075261 : Blo 634301 1075261 := bbase (se 3 (by rfl) ⟨201611, by rfl⟩ : syracuseStep 1075261 = 403223) (by norm_num)
theorem B714829 : Blo 634301 714829 := bbase (se 3 (by rfl) ⟨134030, by rfl⟩ : syracuseStep 714829 = 268061) (by norm_num)
theorem B1435733 : Blo 634301 1435733 := bbase (se 8 (by rfl) ⟨8412, by rfl⟩ : syracuseStep 1435733 = 16825) (by norm_num)
theorem B714865 : Blo 634301 714865 := bbase (se 2 (by rfl) ⟨268074, by rfl⟩ : syracuseStep 714865 = 536149) (by norm_num)
theorem B1206389 : Blo 634301 1206389 := bbase (se 5 (by rfl) ⟨56549, by rfl⟩ : syracuseStep 1206389 = 113099) (by norm_num)
theorem B714901 : Blo 634301 714901 := bbase (se 6 (by rfl) ⟨16755, by rfl⟩ : syracuseStep 714901 = 33511) (by norm_num)
theorem B1075349 : Blo 634301 1075349 := bbase (se 6 (by rfl) ⟨25203, by rfl⟩ : syracuseStep 1075349 = 50407) (by norm_num)
theorem B1435805 : Blo 634301 1435805 := bbase (se 3 (by rfl) ⟨269213, by rfl⟩ : syracuseStep 1435805 = 538427) (by norm_num)
theorem B714937 : Blo 634301 714937 := bbase (se 2 (by rfl) ⟨268101, by rfl⟩ : syracuseStep 714937 = 536203) (by norm_num)
theorem B714973 : Blo 634301 714973 := bbase (se 3 (by rfl) ⟨134057, by rfl⟩ : syracuseStep 714973 = 268115) (by norm_num)
theorem B1435877 : Blo 634301 1435877 := bbase (se 4 (by rfl) ⟨134613, by rfl⟩ : syracuseStep 1435877 = 269227) (by norm_num)
theorem B715009 : Blo 634301 715009 := bbase (se 2 (by rfl) ⟨268128, by rfl⟩ : syracuseStep 715009 = 536257) (by norm_num)
theorem B1075477 : Blo 634301 1075477 := bbase (se 6 (by rfl) ⟨25206, by rfl⟩ : syracuseStep 1075477 = 50413) (by norm_num)
theorem B715045 : Blo 634301 715045 := bbase (se 4 (by rfl) ⟨67035, by rfl⟩ : syracuseStep 715045 = 134071) (by norm_num)
theorem B1435949 : Blo 634301 1435949 := bbase (se 3 (by rfl) ⟨269240, by rfl⟩ : syracuseStep 1435949 = 538481) (by norm_num)
theorem B715081 : Blo 634301 715081 := bbase (se 2 (by rfl) ⟨268155, by rfl⟩ : syracuseStep 715081 = 536311) (by norm_num)
theorem B715117 : Blo 634301 715117 := bbase (se 3 (by rfl) ⟨134084, by rfl⟩ : syracuseStep 715117 = 268169) (by norm_num)
theorem B1075565 : Blo 634301 1075565 := bbase (se 3 (by rfl) ⟨201668, by rfl⟩ : syracuseStep 1075565 = 403337) (by norm_num)
theorem B1436021 : Blo 634301 1436021 := bbase (se 5 (by rfl) ⟨67313, by rfl⟩ : syracuseStep 1436021 = 134627) (by norm_num)
theorem B715153 : Blo 634301 715153 := bbase (se 2 (by rfl) ⟨268182, by rfl⟩ : syracuseStep 715153 = 536365) (by norm_num)
theorem B1206677 : Blo 634301 1206677 := bbase (se 6 (by rfl) ⟨28281, by rfl⟩ : syracuseStep 1206677 = 56563) (by norm_num)
theorem B715189 : Blo 634301 715189 := bbase (se 5 (by rfl) ⟨33524, by rfl⟩ : syracuseStep 715189 = 67049) (by norm_num)
theorem B1436093 : Blo 634301 1436093 := bbase (se 3 (by rfl) ⟨269267, by rfl⟩ : syracuseStep 1436093 = 538535) (by norm_num)
theorem B7236053 : Blo 634301 7236053 := bbase (se 7 (by rfl) ⟨84797, by rfl⟩ : syracuseStep 7236053 = 169595) (by norm_num)
theorem B715225 : Blo 634301 715225 := bbase (se 2 (by rfl) ⟨268209, by rfl⟩ : syracuseStep 715225 = 536419) (by norm_num)
theorem B1075693 : Blo 634301 1075693 := bbase (se 3 (by rfl) ⟨201692, by rfl⟩ : syracuseStep 1075693 = 403385) (by norm_num)
theorem B715261 : Blo 634301 715261 := bbase (se 3 (by rfl) ⟨134111, by rfl⟩ : syracuseStep 715261 = 268223) (by norm_num)
theorem B1436165 : Blo 634301 1436165 := bbase (se 4 (by rfl) ⟨134640, by rfl⟩ : syracuseStep 1436165 = 269281) (by norm_num)
theorem B715297 : Blo 634301 715297 := bbase (se 2 (by rfl) ⟨268236, by rfl⟩ : syracuseStep 715297 = 536473) (by norm_num)
theorem B1206829 : Blo 634301 1206829 := bbase (se 3 (by rfl) ⟨226280, by rfl⟩ : syracuseStep 1206829 = 452561) (by norm_num)
theorem B715333 : Blo 634301 715333 := bbase (se 4 (by rfl) ⟨67062, by rfl⟩ : syracuseStep 715333 = 134125) (by norm_num)
theorem B1075781 : Blo 634301 1075781 := bbase (se 4 (by rfl) ⟨100854, by rfl⟩ : syracuseStep 1075781 = 201709) (by norm_num)
theorem B715369 : Blo 634301 715369 := bbase (se 2 (by rfl) ⟨268263, by rfl⟩ : syracuseStep 715369 = 536527) (by norm_num)
theorem B715405 : Blo 634301 715405 := bbase (se 3 (by rfl) ⟨134138, by rfl⟩ : syracuseStep 715405 = 268277) (by norm_num)
theorem B715441 : Blo 634301 715441 := bbase (se 2 (by rfl) ⟨268290, by rfl⟩ : syracuseStep 715441 = 536581) (by norm_num)
theorem B1075909 : Blo 634301 1075909 := bbase (se 4 (by rfl) ⟨100866, by rfl⟩ : syracuseStep 1075909 = 201733) (by norm_num)
theorem B715477 : Blo 634301 715477 := bbase (se 7 (by rfl) ⟨8384, by rfl⟩ : syracuseStep 715477 = 16769) (by norm_num)
theorem B2419429 : Blo 634301 2419429 := bbase (se 4 (by rfl) ⟨226821, by rfl⟩ : syracuseStep 2419429 = 453643) (by norm_num)
theorem B715513 : Blo 634301 715513 := bbase (se 2 (by rfl) ⟨268317, by rfl⟩ : syracuseStep 715513 = 536635) (by norm_num)
theorem B715549 : Blo 634301 715549 := bbase (se 3 (by rfl) ⟨134165, by rfl⟩ : syracuseStep 715549 = 268331) (by norm_num)
theorem B1075997 : Blo 634301 1075997 := bbase (se 3 (by rfl) ⟨201749, by rfl⟩ : syracuseStep 1075997 = 403499) (by norm_num)
theorem B1567525 : Blo 634301 1567525 := bbase (se 4 (by rfl) ⟨146955, by rfl⟩ : syracuseStep 1567525 = 293911) (by norm_num)
theorem B813889 : Blo 634301 813889 := bbase (se 2 (by rfl) ⟨305208, by rfl⟩ : syracuseStep 813889 = 610417) (by norm_num)
theorem B715585 : Blo 634301 715585 := bbase (se 2 (by rfl) ⟨268344, by rfl⟩ : syracuseStep 715585 = 536689) (by norm_num)
theorem B1207133 : Blo 634301 1207133 := bbase (se 3 (by rfl) ⟨226337, by rfl⟩ : syracuseStep 1207133 = 452675) (by norm_num)
theorem B715621 : Blo 634301 715621 := bbase (se 4 (by rfl) ⟨67089, by rfl⟩ : syracuseStep 715621 = 134179) (by norm_num)
theorem B715657 : Blo 634301 715657 := bbase (se 2 (by rfl) ⟨268371, by rfl⟩ : syracuseStep 715657 = 536743) (by norm_num)
theorem B1076125 : Blo 634301 1076125 := bbase (se 3 (by rfl) ⟨201773, by rfl⟩ : syracuseStep 1076125 = 403547) (by norm_num)
theorem B715693 : Blo 634301 715693 := bbase (se 3 (by rfl) ⟨134192, by rfl⟩ : syracuseStep 715693 = 268385) (by norm_num)
theorem B715729 : Blo 634301 715729 := bbase (se 2 (by rfl) ⟨268398, by rfl⟩ : syracuseStep 715729 = 536797) (by norm_num)
theorem B715765 : Blo 634301 715765 := bbase (se 5 (by rfl) ⟨33551, by rfl⟩ : syracuseStep 715765 = 67103) (by norm_num)
theorem B1076213 : Blo 634301 1076213 := bbase (se 5 (by rfl) ⟨50447, by rfl⟩ : syracuseStep 1076213 = 100895) (by norm_num)
theorem B2419733 : Blo 634301 2419733 := bbase (se 6 (by rfl) ⟨56712, by rfl⟩ : syracuseStep 2419733 = 113425) (by norm_num)
theorem B715801 : Blo 634301 715801 := bbase (se 2 (by rfl) ⟨268425, by rfl⟩ : syracuseStep 715801 = 536851) (by norm_num)
theorem B715837 : Blo 634301 715837 := bbase (se 3 (by rfl) ⟨134219, by rfl⟩ : syracuseStep 715837 = 268439) (by norm_num)
theorem B715873 : Blo 634301 715873 := bbase (se 2 (by rfl) ⟨268452, by rfl⟩ : syracuseStep 715873 = 536905) (by norm_num)
theorem B1076341 : Blo 634301 1076341 := bbase (se 5 (by rfl) ⟨50453, by rfl⟩ : syracuseStep 1076341 = 100907) (by norm_num)
theorem B715909 : Blo 634301 715909 := bbase (se 4 (by rfl) ⟨67116, by rfl⟩ : syracuseStep 715909 = 134233) (by norm_num)
theorem B715945 : Blo 634301 715945 := bbase (se 2 (by rfl) ⟨268479, by rfl⟩ : syracuseStep 715945 = 536959) (by norm_num)
theorem B715981 : Blo 634301 715981 := bbase (se 3 (by rfl) ⟨134246, by rfl⟩ : syracuseStep 715981 = 268493) (by norm_num)
theorem B1076429 : Blo 634301 1076429 := bbase (se 3 (by rfl) ⟨201830, by rfl⟩ : syracuseStep 1076429 = 403661) (by norm_num)
theorem B716017 : Blo 634301 716017 := bbase (se 2 (by rfl) ⟨268506, by rfl⟩ : syracuseStep 716017 = 537013) (by norm_num)
theorem B716053 : Blo 634301 716053 := bbase (se 6 (by rfl) ⟨16782, by rfl⟩ : syracuseStep 716053 = 33565) (by norm_num)
theorem B716089 : Blo 634301 716089 := bbase (se 2 (by rfl) ⟨268533, by rfl⟩ : syracuseStep 716089 = 537067) (by norm_num)
theorem B1076557 : Blo 634301 1076557 := bbase (se 3 (by rfl) ⟨201854, by rfl⟩ : syracuseStep 1076557 = 403709) (by norm_num)
theorem B716125 : Blo 634301 716125 := bbase (se 3 (by rfl) ⟨134273, by rfl⟩ : syracuseStep 716125 = 268547) (by norm_num)
theorem B1633637 : Blo 634301 1633637 := bbase (se 4 (by rfl) ⟨153153, by rfl⟩ : syracuseStep 1633637 = 306307) (by norm_num)
theorem B716161 : Blo 634301 716161 := bbase (se 2 (by rfl) ⟨268560, by rfl⟩ : syracuseStep 716161 = 537121) (by norm_num)
theorem B716197 : Blo 634301 716197 := bbase (se 4 (by rfl) ⟨67143, by rfl⟩ : syracuseStep 716197 = 134287) (by norm_num)
theorem B1076645 : Blo 634301 1076645 := bbase (se 4 (by rfl) ⟨100935, by rfl⟩ : syracuseStep 1076645 = 201871) (by norm_num)
theorem B716233 : Blo 634301 716233 := bbase (se 2 (by rfl) ⟨268587, by rfl⟩ : syracuseStep 716233 = 537175) (by norm_num)
theorem B716269 : Blo 634301 716269 := bbase (se 3 (by rfl) ⟨134300, by rfl⟩ : syracuseStep 716269 = 268601) (by norm_num)
theorem B716305 : Blo 634301 716305 := bbase (se 2 (by rfl) ⟨268614, by rfl⟩ : syracuseStep 716305 = 537229) (by norm_num)
theorem B1076773 : Blo 634301 1076773 := bbase (se 4 (by rfl) ⟨100947, by rfl⟩ : syracuseStep 1076773 = 201895) (by norm_num)
theorem B716341 : Blo 634301 716341 := bbase (se 5 (by rfl) ⟨33578, by rfl⟩ : syracuseStep 716341 = 67157) (by norm_num)
theorem B1207885 : Blo 634301 1207885 := bbase (se 3 (by rfl) ⟨226478, by rfl⟩ : syracuseStep 1207885 = 452957) (by norm_num)
theorem B716377 : Blo 634301 716377 := bbase (se 2 (by rfl) ⟨268641, by rfl⟩ : syracuseStep 716377 = 537283) (by norm_num)
theorem B716413 : Blo 634301 716413 := bbase (se 3 (by rfl) ⟨134327, by rfl⟩ : syracuseStep 716413 = 268655) (by norm_num)
theorem B1076861 : Blo 634301 1076861 := bbase (se 3 (by rfl) ⟨201911, by rfl⟩ : syracuseStep 1076861 = 403823) (by norm_num)
theorem B3632789 : Blo 634301 3632789 := bbase (se 6 (by rfl) ⟨85143, by rfl⟩ : syracuseStep 3632789 = 170287) (by norm_num)
theorem B716449 : Blo 634301 716449 := bbase (se 2 (by rfl) ⟨268668, by rfl⟩ : syracuseStep 716449 = 537337) (by norm_num)
theorem B716485 : Blo 634301 716485 := bbase (se 4 (by rfl) ⟨67170, by rfl⟩ : syracuseStep 716485 = 134341) (by norm_num)
theorem B1633997 : Blo 634301 1633997 := bbase (se 3 (by rfl) ⟨306374, by rfl⟩ : syracuseStep 1633997 = 612749) (by norm_num)
theorem B1208029 : Blo 634301 1208029 := bbase (se 3 (by rfl) ⟨226505, by rfl⟩ : syracuseStep 1208029 = 453011) (by norm_num)
theorem B716521 : Blo 634301 716521 := bbase (se 2 (by rfl) ⟨268695, by rfl⟩ : syracuseStep 716521 = 537391) (by norm_num)
theorem B1076989 : Blo 634301 1076989 := bbase (se 3 (by rfl) ⟨201935, by rfl⟩ : syracuseStep 1076989 = 403871) (by norm_num)
theorem B1306373 : Blo 634301 1306373 := bbase (se 4 (by rfl) ⟨122472, by rfl⟩ : syracuseStep 1306373 = 244945) (by norm_num)
theorem B716557 : Blo 634301 716557 := bbase (se 3 (by rfl) ⟨134354, by rfl⟩ : syracuseStep 716557 = 268709) (by norm_num)
theorem B716593 : Blo 634301 716593 := bbase (se 2 (by rfl) ⟨268722, by rfl⟩ : syracuseStep 716593 = 537445) (by norm_num)
theorem B716629 : Blo 634301 716629 := bbase (se 9 (by rfl) ⟨2099, by rfl⟩ : syracuseStep 716629 = 4199) (by norm_num)
theorem B1077077 : Blo 634301 1077077 := bbase (se 9 (by rfl) ⟨3155, by rfl⟩ : syracuseStep 1077077 = 6311) (by norm_num)
theorem B716665 : Blo 634301 716665 := bbase (se 2 (by rfl) ⟨268749, by rfl⟩ : syracuseStep 716665 = 537499) (by norm_num)
theorem B1208189 : Blo 634301 1208189 := bbase (se 3 (by rfl) ⟨226535, by rfl⟩ : syracuseStep 1208189 = 453071) (by norm_num)
theorem B716701 : Blo 634301 716701 := bbase (se 3 (by rfl) ⟨134381, by rfl⟩ : syracuseStep 716701 = 268763) (by norm_num)
theorem B716737 : Blo 634301 716737 := bbase (se 2 (by rfl) ⟨268776, by rfl⟩ : syracuseStep 716737 = 537553) (by norm_num)
theorem B716773 : Blo 634301 716773 := bbase (se 4 (by rfl) ⟨67197, by rfl⟩ : syracuseStep 716773 = 134395) (by norm_num)
theorem B716809 : Blo 634301 716809 := bbase (se 2 (by rfl) ⟨268803, by rfl⟩ : syracuseStep 716809 = 537607) (by norm_num)
theorem B1208333 : Blo 634301 1208333 := bbase (se 3 (by rfl) ⟨226562, by rfl⟩ : syracuseStep 1208333 = 453125) (by norm_num)
theorem B2617381 : Blo 634301 2617381 := bbase (se 4 (by rfl) ⟨245379, by rfl⟩ : syracuseStep 2617381 = 490759) (by norm_num)
theorem B716845 : Blo 634301 716845 := bbase (se 3 (by rfl) ⟨134408, by rfl⟩ : syracuseStep 716845 = 268817) (by norm_num)
theorem B716881 : Blo 634301 716881 := bbase (se 2 (by rfl) ⟨268830, by rfl⟩ : syracuseStep 716881 = 537661) (by norm_num)
theorem B716917 : Blo 634301 716917 := bbase (se 5 (by rfl) ⟨33605, by rfl⟩ : syracuseStep 716917 = 67211) (by norm_num)
theorem B716953 : Blo 634301 716953 := bbase (se 2 (by rfl) ⟨268857, by rfl⟩ : syracuseStep 716953 = 537715) (by norm_num)
theorem B716989 : Blo 634301 716989 := bbase (se 3 (by rfl) ⟨134435, by rfl⟩ : syracuseStep 716989 = 268871) (by norm_num)
theorem B1929413 : Blo 634301 1929413 := bbase (se 4 (by rfl) ⟨180882, by rfl⟩ : syracuseStep 1929413 = 361765) (by norm_num)
theorem B717025 : Blo 634301 717025 := bbase (se 2 (by rfl) ⟨268884, by rfl⟩ : syracuseStep 717025 = 537769) (by norm_num)
theorem B717061 : Blo 634301 717061 := bbase (se 4 (by rfl) ⟨67224, by rfl⟩ : syracuseStep 717061 = 134449) (by norm_num)
theorem B717097 : Blo 634301 717097 := bbase (se 2 (by rfl) ⟨268911, by rfl⟩ : syracuseStep 717097 = 537823) (by norm_num)
theorem B1208621 : Blo 634301 1208621 := bbase (se 3 (by rfl) ⟨226616, by rfl⟩ : syracuseStep 1208621 = 453233) (by norm_num)
theorem B717133 : Blo 634301 717133 := bbase (se 3 (by rfl) ⟨134462, by rfl⟩ : syracuseStep 717133 = 268925) (by norm_num)
theorem B1929557 : Blo 634301 1929557 := bbase (se 10 (by rfl) ⟨2826, by rfl⟩ : syracuseStep 1929557 = 5653) (by norm_num)
theorem B717169 : Blo 634301 717169 := bbase (se 2 (by rfl) ⟨268938, by rfl⟩ : syracuseStep 717169 = 537877) (by norm_num)
theorem B717205 : Blo 634301 717205 := bbase (se 6 (by rfl) ⟨16809, by rfl⟩ : syracuseStep 717205 = 33619) (by norm_num)
theorem B717241 : Blo 634301 717241 := bbase (se 2 (by rfl) ⟨268965, by rfl⟩ : syracuseStep 717241 = 537931) (by norm_num)
theorem B1208773 : Blo 634301 1208773 := bbase (se 4 (by rfl) ⟨113322, by rfl⟩ : syracuseStep 1208773 = 226645) (by norm_num)
theorem B717277 : Blo 634301 717277 := bbase (se 3 (by rfl) ⟨134489, by rfl⟩ : syracuseStep 717277 = 268979) (by norm_num)
theorem B717313 : Blo 634301 717313 := bbase (se 2 (by rfl) ⟨268992, by rfl⟩ : syracuseStep 717313 = 537985) (by norm_num)
theorem B717349 : Blo 634301 717349 := bbase (se 4 (by rfl) ⟨67251, by rfl⟩ : syracuseStep 717349 = 134503) (by norm_num)
theorem B717385 : Blo 634301 717385 := bbase (se 2 (by rfl) ⟨269019, by rfl⟩ : syracuseStep 717385 = 538039) (by norm_num)
theorem B717421 : Blo 634301 717421 := bbase (se 3 (by rfl) ⟨134516, by rfl⟩ : syracuseStep 717421 = 269033) (by norm_num)
theorem B717457 : Blo 634301 717457 := bbase (se 2 (by rfl) ⟨269046, by rfl⟩ : syracuseStep 717457 = 538093) (by norm_num)
theorem B2323109 : Blo 634301 2323109 := bbase (se 4 (by rfl) ⟨217791, by rfl⟩ : syracuseStep 2323109 = 435583) (by norm_num)
theorem B717493 : Blo 634301 717493 := bbase (se 5 (by rfl) ⟨33632, by rfl⟩ : syracuseStep 717493 = 67265) (by norm_num)
theorem B717529 : Blo 634301 717529 := bbase (se 2 (by rfl) ⟨269073, by rfl⟩ : syracuseStep 717529 = 538147) (by norm_num)
theorem B1209077 : Blo 634301 1209077 := bbase (se 5 (by rfl) ⟨56675, by rfl⟩ : syracuseStep 1209077 = 113351) (by norm_num)
theorem B717565 : Blo 634301 717565 := bbase (se 3 (by rfl) ⟨134543, by rfl⟩ : syracuseStep 717565 = 269087) (by norm_num)
theorem B717601 : Blo 634301 717601 := bbase (se 2 (by rfl) ⟨269100, by rfl⟩ : syracuseStep 717601 = 538201) (by norm_num)
theorem B717637 : Blo 634301 717637 := bbase (se 4 (by rfl) ⟨67278, by rfl⟩ : syracuseStep 717637 = 134557) (by norm_num)
theorem B717673 : Blo 634301 717673 := bbase (se 2 (by rfl) ⟨269127, by rfl⟩ : syracuseStep 717673 = 538255) (by norm_num)
theorem B717709 : Blo 634301 717709 := bbase (se 3 (by rfl) ⟨134570, by rfl⟩ : syracuseStep 717709 = 269141) (by norm_num)
theorem B717745 : Blo 634301 717745 := bbase (se 2 (by rfl) ⟨269154, by rfl⟩ : syracuseStep 717745 = 538309) (by norm_num)
theorem B717781 : Blo 634301 717781 := bbase (se 7 (by rfl) ⟨8411, by rfl⟩ : syracuseStep 717781 = 16823) (by norm_num)
theorem B717817 : Blo 634301 717817 := bbase (se 2 (by rfl) ⟨269181, by rfl⟩ : syracuseStep 717817 = 538363) (by norm_num)
theorem B717853 : Blo 634301 717853 := bbase (se 3 (by rfl) ⟨134597, by rfl⟩ : syracuseStep 717853 = 269195) (by norm_num)
theorem B717889 : Blo 634301 717889 := bbase (se 2 (by rfl) ⟨269208, by rfl⟩ : syracuseStep 717889 = 538417) (by norm_num)
theorem B2421845 : Blo 634301 2421845 := bbase (se 8 (by rfl) ⟨14190, by rfl⟩ : syracuseStep 2421845 = 28381) (by norm_num)
theorem B717925 : Blo 634301 717925 := bbase (se 4 (by rfl) ⟨67305, by rfl⟩ : syracuseStep 717925 = 134611) (by norm_num)
theorem B717961 : Blo 634301 717961 := bbase (se 2 (by rfl) ⟨269235, by rfl⟩ : syracuseStep 717961 = 538471) (by norm_num)
theorem B1569949 : Blo 634301 1569949 := bbase (se 3 (by rfl) ⟨294365, by rfl⟩ : syracuseStep 1569949 = 588731) (by norm_num)
theorem B717997 : Blo 634301 717997 := bbase (se 3 (by rfl) ⟨134624, by rfl⟩ : syracuseStep 717997 = 269249) (by norm_num)
theorem B718033 : Blo 634301 718033 := bbase (se 2 (by rfl) ⟨269262, by rfl⟩ : syracuseStep 718033 = 538525) (by norm_num)
theorem B718069 : Blo 634301 718069 := bbase (se 5 (by rfl) ⟨33659, by rfl⟩ : syracuseStep 718069 = 67319) (by norm_num)
theorem B1144133 : Blo 634301 1144133 := bbase (se 4 (by rfl) ⟨107262, by rfl⟩ : syracuseStep 1144133 = 214525) (by norm_num)
theorem B2422133 : Blo 634301 2422133 := bbase (se 5 (by rfl) ⟨113537, by rfl⟩ : syracuseStep 2422133 = 227075) (by norm_num)
theorem B1209829 : Blo 634301 1209829 := bbase (se 4 (by rfl) ⟨113421, by rfl⟩ : syracuseStep 1209829 = 226843) (by norm_num)
theorem B1209973 : Blo 634301 1209973 := bbase (se 5 (by rfl) ⟨56717, by rfl⟩ : syracuseStep 1209973 = 113435) (by norm_num)
theorem B2717333 : Blo 634301 2717333 := bbase (se 6 (by rfl) ⟨63687, by rfl⟩ : syracuseStep 2717333 = 127375) (by norm_num)
theorem B1210133 : Blo 634301 1210133 := bbase (se 6 (by rfl) ⟨28362, by rfl⟩ : syracuseStep 1210133 = 56725) (by norm_num)
theorem B1046333 : Blo 634301 1046333 := bbase (se 3 (by rfl) ⟨196187, by rfl⟩ : syracuseStep 1046333 = 392375) (by norm_num)
theorem B1210277 : Blo 634301 1210277 := bbase (se 4 (by rfl) ⟨113463, by rfl⟩ : syracuseStep 1210277 = 226927) (by norm_num)
theorem B2717621 : Blo 634301 2717621 := bbase (se 5 (by rfl) ⟨127388, by rfl⟩ : syracuseStep 2717621 = 254777) (by norm_num)
theorem B2586613 : Blo 634301 2586613 := bbase (se 5 (by rfl) ⟨121247, by rfl⟩ : syracuseStep 2586613 = 242495) (by norm_num)
theorem B1144997 : Blo 634301 1144997 := bbase (se 4 (by rfl) ⟨107343, by rfl⟩ : syracuseStep 1144997 = 214687) (by norm_num)
theorem B1308853 : Blo 634301 1308853 := bbase (se 5 (by rfl) ⟨61352, by rfl⟩ : syracuseStep 1308853 = 122705) (by norm_num)
theorem B1210565 : Blo 634301 1210565 := bbase (se 4 (by rfl) ⟨113490, by rfl⟩ : syracuseStep 1210565 = 226981) (by norm_num)
theorem B13760725 : Blo 634301 13760725 := bbase (se 7 (by rfl) ⟨161258, by rfl⟩ : syracuseStep 13760725 = 322517) (by norm_num)
theorem B1210717 : Blo 634301 1210717 := bbase (se 3 (by rfl) ⟨227009, by rfl⟩ : syracuseStep 1210717 = 454019) (by norm_num)
theorem B981445 : Blo 634301 981445 := bbase (se 4 (by rfl) ⟨92010, by rfl⟩ : syracuseStep 981445 = 184021) (by norm_num)
theorem B2292245 : Blo 634301 2292245 := bbase (se 6 (by rfl) ⟨53724, by rfl⟩ : syracuseStep 2292245 = 107449) (by norm_num)
theorem B2423317 : Blo 634301 2423317 := bbase (se 6 (by rfl) ⟨56796, by rfl⟩ : syracuseStep 2423317 = 113593) (by norm_num)
theorem B1211021 : Blo 634301 1211021 := bbase (se 3 (by rfl) ⟨227066, by rfl⟩ : syracuseStep 1211021 = 454133) (by norm_num)
theorem B2718373 : Blo 634301 2718373 := bbase (se 4 (by rfl) ⟨254847, by rfl⟩ : syracuseStep 2718373 = 509695) (by norm_num)
theorem B1473221 : Blo 634301 1473221 := bbase (se 4 (by rfl) ⟨138114, by rfl⟩ : syracuseStep 1473221 = 276229) (by norm_num)
theorem B1637117 : Blo 634301 1637117 := bbase (se 3 (by rfl) ⟨306959, by rfl⟩ : syracuseStep 1637117 = 613919) (by norm_num)
theorem B817933 : Blo 634301 817933 := bbase (se 3 (by rfl) ⟨153362, by rfl⟩ : syracuseStep 817933 = 306725) (by norm_num)
theorem B2292533 : Blo 634301 2292533 := bbase (se 5 (by rfl) ⟨107462, by rfl⟩ : syracuseStep 2292533 = 214925) (by norm_num)
theorem B1375133 : Blo 634301 1375133 := bbase (se 3 (by rfl) ⟨257837, by rfl⟩ : syracuseStep 1375133 = 515675) (by norm_num)
theorem B2948069 : Blo 634301 2948069 := bbase (se 4 (by rfl) ⟨276381, by rfl⟩ : syracuseStep 2948069 = 552763) (by norm_num)
theorem B916525 : Blo 634301 916525 := bbase (se 3 (by rfl) ⟨171848, by rfl⟩ : syracuseStep 916525 = 343697) (by norm_num)
theorem B1211773 : Blo 634301 1211773 := bbase (se 3 (by rfl) ⟨227207, by rfl⟩ : syracuseStep 1211773 = 454415) (by norm_num)
theorem B2719109 : Blo 634301 2719109 := bbase (se 4 (by rfl) ⟨254916, by rfl⟩ : syracuseStep 2719109 = 509833) (by norm_num)
theorem B1146325 : Blo 634301 1146325 := bbase (se 7 (by rfl) ⟨13433, by rfl⟩ : syracuseStep 1146325 = 26867) (by norm_num)
theorem B5438933 : Blo 634301 5438933 := bbase (se 7 (by rfl) ⟨63737, by rfl⟩ : syracuseStep 5438933 = 127475) (by norm_num)
theorem B687577 : Blo 634301 687577 := bbase (se 2 (by rfl) ⟨257841, by rfl⟩ : syracuseStep 687577 = 515683) (by norm_num)
theorem B1834517 : Blo 634301 1834517 := bbase (se 6 (by rfl) ⟨42996, by rfl⟩ : syracuseStep 1834517 = 85993) (by norm_num)
theorem B4587029 : Blo 634301 4587029 := bbase (se 6 (by rfl) ⟨107508, by rfl⟩ : syracuseStep 4587029 = 215017) (by norm_num)
theorem B1146469 : Blo 634301 1146469 := bbase (se 4 (by rfl) ⟨107481, by rfl⟩ : syracuseStep 1146469 = 214963) (by norm_num)
theorem B1834805 : Blo 634301 1834805 := bbase (se 5 (by rfl) ⟨86006, by rfl⟩ : syracuseStep 1834805 = 172013) (by norm_num)
theorem B2293685 : Blo 634301 2293685 := bbase (se 5 (by rfl) ⟨107516, by rfl⟩ : syracuseStep 2293685 = 215033) (by norm_num)
theorem B3964933 : Blo 634301 3964933 := bstep (se 4 (by rfl) ⟨371712, by rfl⟩ : syracuseStep 3964933 = 743425) B743425
theorem B2293859 : Blo 634301 2293859 := bstep (se 1 (by rfl) ⟨1720394, by rfl⟩ : syracuseStep 2293859 = 3440789) B3440789
theorem B1933645 : Blo 634301 1933645 := bstep (se 3 (by rfl) ⟨362558, by rfl⟩ : syracuseStep 1933645 = 725117) B725117
theorem B3211811 : Blo 634301 3211811 := bstep (se 1 (by rfl) ⟨2408858, by rfl⟩ : syracuseStep 3211811 = 4817717) B4817717
theorem B1114913 : Blo 634301 1114913 := bstep (se 2 (by rfl) ⟨418092, by rfl⟩ : syracuseStep 1114913 = 836185) B836185
theorem B1606513 : Blo 634301 1606513 := bstep (se 2 (by rfl) ⟨602442, by rfl⟩ : syracuseStep 1606513 = 1204885) B1204885
theorem B2032771 : Blo 634301 2032771 := bstep (se 1 (by rfl) ⟨1524578, by rfl⟩ : syracuseStep 2032771 = 3049157) B3049157
theorem B1606787 : Blo 634301 1606787 := bstep (se 1 (by rfl) ⟨1205090, by rfl⟩ : syracuseStep 1606787 = 2410181) B2410181
theorem B951473 : Blo 634301 951473 := bstep (se 2 (by rfl) ⟨356802, by rfl⟩ : syracuseStep 951473 = 713605) B713605
theorem B951491 : Blo 634301 951491 := bstep (se 1 (by rfl) ⟨713618, by rfl⟩ : syracuseStep 951491 = 1427237) B1427237
theorem B5440709 : Blo 634301 5440709 := bstep (se 4 (by rfl) ⟨510066, by rfl⟩ : syracuseStep 5440709 = 1020133) B1020133
theorem B951521 : Blo 634301 951521 := bstep (se 2 (by rfl) ⟨356820, by rfl⟩ : syracuseStep 951521 = 713641) B713641
theorem B951539 : Blo 634301 951539 := bstep (se 1 (by rfl) ⟨713654, by rfl⟩ : syracuseStep 951539 = 1427309) B1427309
theorem B1934605 : Blo 634301 1934605 := bstep (se 3 (by rfl) ⟨362738, by rfl⟩ : syracuseStep 1934605 = 725477) B725477
theorem B951569 : Blo 634301 951569 := bstep (se 2 (by rfl) ⟨356838, by rfl⟩ : syracuseStep 951569 = 713677) B713677
theorem B951587 : Blo 634301 951587 := bstep (se 1 (by rfl) ⟨713690, by rfl⟩ : syracuseStep 951587 = 1427381) B1427381
theorem B2721073 : Blo 634301 2721073 := bstep (se 2 (by rfl) ⟨1020402, by rfl⟩ : syracuseStep 2721073 = 2040805) B2040805
theorem B951617 : Blo 634301 951617 := bstep (se 2 (by rfl) ⟨356856, by rfl⟩ : syracuseStep 951617 = 713713) B713713
theorem B1606979 : Blo 634301 1606979 := bstep (se 1 (by rfl) ⟨1205234, by rfl⟩ : syracuseStep 1606979 = 2410469) B2410469
theorem B3212621 : Blo 634301 3212621 := bstep (se 3 (by rfl) ⟨602366, by rfl⟩ : syracuseStep 3212621 = 1204733) B1204733
theorem B951635 : Blo 634301 951635 := bstep (se 1 (by rfl) ⟨713726, by rfl⟩ : syracuseStep 951635 = 1427453) B1427453
theorem B951665 : Blo 634301 951665 := bstep (se 2 (by rfl) ⟨356874, by rfl⟩ : syracuseStep 951665 = 713749) B713749
theorem B951683 : Blo 634301 951683 := bstep (se 1 (by rfl) ⟨713762, by rfl⟩ : syracuseStep 951683 = 1427525) B1427525
theorem B951713 : Blo 634301 951713 := bstep (se 2 (by rfl) ⟨356892, by rfl⟩ : syracuseStep 951713 = 713785) B713785
theorem B951731 : Blo 634301 951731 := bstep (se 1 (by rfl) ⟨713798, by rfl⟩ : syracuseStep 951731 = 1427597) B1427597
theorem B951761 : Blo 634301 951761 := bstep (se 2 (by rfl) ⟨356910, by rfl⟩ : syracuseStep 951761 = 713821) B713821
theorem B951779 : Blo 634301 951779 := bstep (se 1 (by rfl) ⟨713834, by rfl⟩ : syracuseStep 951779 = 1427669) B1427669
theorem B951809 : Blo 634301 951809 := bstep (se 2 (by rfl) ⟨356928, by rfl⟩ : syracuseStep 951809 = 713857) B713857
theorem B951827 : Blo 634301 951827 := bstep (se 1 (by rfl) ⟨713870, by rfl⟩ : syracuseStep 951827 = 1427741) B1427741
theorem B951857 : Blo 634301 951857 := bstep (se 2 (by rfl) ⟨356946, by rfl⟩ : syracuseStep 951857 = 713893) B713893
theorem B951875 : Blo 634301 951875 := bstep (se 1 (by rfl) ⟨713906, by rfl⟩ : syracuseStep 951875 = 1427813) B1427813
theorem B3671621 : Blo 634301 3671621 := bstep (se 4 (by rfl) ⟨344214, by rfl⟩ : syracuseStep 3671621 = 688429) B688429
theorem B951905 : Blo 634301 951905 := bstep (se 2 (by rfl) ⟨356964, by rfl⟩ : syracuseStep 951905 = 713929) B713929
theorem B1017443 : Blo 634301 1017443 := bstep (se 1 (by rfl) ⟨763082, by rfl⟩ : syracuseStep 1017443 = 1526165) B1526165
theorem B951923 : Blo 634301 951923 := bstep (se 1 (by rfl) ⟨713942, by rfl⟩ : syracuseStep 951923 = 1427885) B1427885
theorem B951953 : Blo 634301 951953 := bstep (se 2 (by rfl) ⟨356982, by rfl⟩ : syracuseStep 951953 = 713965) B713965
theorem B951971 : Blo 634301 951971 := bstep (se 1 (by rfl) ⟨713978, by rfl⟩ : syracuseStep 951971 = 1427957) B1427957
theorem B952001 : Blo 634301 952001 := bstep (se 2 (by rfl) ⟨357000, by rfl⟩ : syracuseStep 952001 = 714001) B714001
theorem B952019 : Blo 634301 952019 := bstep (se 1 (by rfl) ⟨714014, by rfl⟩ : syracuseStep 952019 = 1428029) B1428029
theorem B952049 : Blo 634301 952049 := bstep (se 2 (by rfl) ⟨357018, by rfl⟩ : syracuseStep 952049 = 714037) B714037
theorem B952067 : Blo 634301 952067 := bstep (se 1 (by rfl) ⟨714050, by rfl⟩ : syracuseStep 952067 = 1428101) B1428101
theorem B952097 : Blo 634301 952097 := bstep (se 2 (by rfl) ⟨357036, by rfl⟩ : syracuseStep 952097 = 714073) B714073
theorem B952115 : Blo 634301 952115 := bstep (se 1 (by rfl) ⟨714086, by rfl⟩ : syracuseStep 952115 = 1428173) B1428173
theorem B952145 : Blo 634301 952145 := bstep (se 2 (by rfl) ⟨357054, by rfl⟩ : syracuseStep 952145 = 714109) B714109
theorem B952163 : Blo 634301 952163 := bstep (se 1 (by rfl) ⟨714122, by rfl⟩ : syracuseStep 952163 = 1428245) B1428245
theorem B952193 : Blo 634301 952193 := bstep (se 2 (by rfl) ⟨357072, by rfl⟩ : syracuseStep 952193 = 714145) B714145
theorem B952211 : Blo 634301 952211 := bstep (se 1 (by rfl) ⟨714158, by rfl⟩ : syracuseStep 952211 = 1428317) B1428317
theorem B952241 : Blo 634301 952241 := bstep (se 2 (by rfl) ⟨357090, by rfl⟩ : syracuseStep 952241 = 714181) B714181
theorem B2033603 : Blo 634301 2033603 := bstep (se 1 (by rfl) ⟨1525202, by rfl⟩ : syracuseStep 2033603 = 3050405) B3050405
theorem B952259 : Blo 634301 952259 := bstep (se 1 (by rfl) ⟨714194, by rfl⟩ : syracuseStep 952259 = 1428389) B1428389
theorem B952289 : Blo 634301 952289 := bstep (se 2 (by rfl) ⟨357108, by rfl⟩ : syracuseStep 952289 = 714217) B714217
theorem B1017827 : Blo 634301 1017827 := bstep (se 1 (by rfl) ⟨763370, by rfl⟩ : syracuseStep 1017827 = 1526741) B1526741
theorem B952307 : Blo 634301 952307 := bstep (se 1 (by rfl) ⟨714230, by rfl⟩ : syracuseStep 952307 = 1428461) B1428461
theorem B952337 : Blo 634301 952337 := bstep (se 2 (by rfl) ⟨357126, by rfl⟩ : syracuseStep 952337 = 714253) B714253
theorem B952355 : Blo 634301 952355 := bstep (se 1 (by rfl) ⟨714266, by rfl⟩ : syracuseStep 952355 = 1428533) B1428533
theorem B952385 : Blo 634301 952385 := bstep (se 2 (by rfl) ⟨357144, by rfl⟩ : syracuseStep 952385 = 714289) B714289
theorem B952403 : Blo 634301 952403 := bstep (se 1 (by rfl) ⟨714302, by rfl⟩ : syracuseStep 952403 = 1428605) B1428605
theorem B1017955 : Blo 634301 1017955 := bstep (se 1 (by rfl) ⟨763466, by rfl⟩ : syracuseStep 1017955 = 1526933) B1526933
theorem B952433 : Blo 634301 952433 := bstep (se 2 (by rfl) ⟨357162, by rfl⟩ : syracuseStep 952433 = 714325) B714325
theorem B952451 : Blo 634301 952451 := bstep (se 1 (by rfl) ⟨714338, by rfl⟩ : syracuseStep 952451 = 1428677) B1428677
theorem B952481 : Blo 634301 952481 := bstep (se 2 (by rfl) ⟨357180, by rfl⟩ : syracuseStep 952481 = 714361) B714361
theorem B952499 : Blo 634301 952499 := bstep (se 1 (by rfl) ⟨714374, by rfl⟩ : syracuseStep 952499 = 1428749) B1428749
theorem B952529 : Blo 634301 952529 := bstep (se 2 (by rfl) ⟨357198, by rfl⟩ : syracuseStep 952529 = 714397) B714397
theorem B952547 : Blo 634301 952547 := bstep (se 1 (by rfl) ⟨714410, by rfl⟩ : syracuseStep 952547 = 1428821) B1428821
theorem B1607921 : Blo 634301 1607921 := bstep (se 2 (by rfl) ⟨602970, by rfl⟩ : syracuseStep 1607921 = 1205941) B1205941
theorem B952577 : Blo 634301 952577 := bstep (se 2 (by rfl) ⟨357216, by rfl⟩ : syracuseStep 952577 = 714433) B714433
theorem B952595 : Blo 634301 952595 := bstep (se 1 (by rfl) ⟨714446, by rfl⟩ : syracuseStep 952595 = 1428893) B1428893
theorem B1607971 : Blo 634301 1607971 := bstep (se 1 (by rfl) ⟨1205978, by rfl⟩ : syracuseStep 1607971 = 2411957) B2411957
theorem B952625 : Blo 634301 952625 := bstep (se 2 (by rfl) ⟨357234, by rfl⟩ : syracuseStep 952625 = 714469) B714469
theorem B952643 : Blo 634301 952643 := bstep (se 1 (by rfl) ⟨714482, by rfl⟩ : syracuseStep 952643 = 1428965) B1428965
theorem B2034001 : Blo 634301 2034001 := bstep (se 2 (by rfl) ⟨762750, by rfl⟩ : syracuseStep 2034001 = 1525501) B1525501
theorem B1149265 : Blo 634301 1149265 := bstep (se 2 (by rfl) ⟨430974, by rfl⟩ : syracuseStep 1149265 = 861949) B861949
theorem B952673 : Blo 634301 952673 := bstep (se 2 (by rfl) ⟨357252, by rfl⟩ : syracuseStep 952673 = 714505) B714505
theorem B952691 : Blo 634301 952691 := bstep (se 1 (by rfl) ⟨714518, by rfl⟩ : syracuseStep 952691 = 1429037) B1429037
theorem B2034065 : Blo 634301 2034065 := bstep (se 2 (by rfl) ⟨762774, by rfl⟩ : syracuseStep 2034065 = 1525549) B1525549
theorem B952721 : Blo 634301 952721 := bstep (se 2 (by rfl) ⟨357270, by rfl⟩ : syracuseStep 952721 = 714541) B714541
theorem B952739 : Blo 634301 952739 := bstep (se 1 (by rfl) ⟨714554, by rfl⟩ : syracuseStep 952739 = 1429109) B1429109
theorem B1608113 : Blo 634301 1608113 := bstep (se 2 (by rfl) ⟨603042, by rfl⟩ : syracuseStep 1608113 = 1206085) B1206085
theorem B952769 : Blo 634301 952769 := bstep (se 2 (by rfl) ⟨357288, by rfl⟩ : syracuseStep 952769 = 714577) B714577
theorem B952787 : Blo 634301 952787 := bstep (se 1 (by rfl) ⟨714590, by rfl⟩ : syracuseStep 952787 = 1429181) B1429181
theorem B952817 : Blo 634301 952817 := bstep (se 2 (by rfl) ⟨357306, by rfl⟩ : syracuseStep 952817 = 714613) B714613
theorem B952835 : Blo 634301 952835 := bstep (se 1 (by rfl) ⟨714626, by rfl⟩ : syracuseStep 952835 = 1429253) B1429253
theorem B952865 : Blo 634301 952865 := bstep (se 2 (by rfl) ⟨357324, by rfl⟩ : syracuseStep 952865 = 714649) B714649
theorem B952883 : Blo 634301 952883 := bstep (se 1 (by rfl) ⟨714662, by rfl⟩ : syracuseStep 952883 = 1429325) B1429325
theorem B952913 : Blo 634301 952913 := bstep (se 2 (by rfl) ⟨357342, by rfl⟩ : syracuseStep 952913 = 714685) B714685
theorem B952931 : Blo 634301 952931 := bstep (se 1 (by rfl) ⟨714698, by rfl⟩ : syracuseStep 952931 = 1429397) B1429397
theorem B952961 : Blo 634301 952961 := bstep (se 2 (by rfl) ⟨357360, by rfl⟩ : syracuseStep 952961 = 714721) B714721
theorem B952979 : Blo 634301 952979 := bstep (se 1 (by rfl) ⟨714734, by rfl⟩ : syracuseStep 952979 = 1429469) B1429469
theorem B953009 : Blo 634301 953009 := bstep (se 2 (by rfl) ⟨357378, by rfl⟩ : syracuseStep 953009 = 714757) B714757
theorem B953027 : Blo 634301 953027 := bstep (se 1 (by rfl) ⟨714770, by rfl⟩ : syracuseStep 953027 = 1429541) B1429541
theorem B723667 : Blo 634301 723667 := bstep (se 1 (by rfl) ⟨542750, by rfl⟩ : syracuseStep 723667 = 1085501) B1085501
theorem B953057 : Blo 634301 953057 := bstep (se 2 (by rfl) ⟨357396, by rfl⟩ : syracuseStep 953057 = 714793) B714793
theorem B953075 : Blo 634301 953075 := bstep (se 1 (by rfl) ⟨714806, by rfl⟩ : syracuseStep 953075 = 1429613) B1429613
theorem B953105 : Blo 634301 953105 := bstep (se 2 (by rfl) ⟨357414, by rfl⟩ : syracuseStep 953105 = 714829) B714829
theorem B953123 : Blo 634301 953123 := bstep (se 1 (by rfl) ⟨714842, by rfl⟩ : syracuseStep 953123 = 1429685) B1429685
theorem B1018673 : Blo 634301 1018673 := bstep (se 2 (by rfl) ⟨382002, by rfl⟩ : syracuseStep 1018673 = 764005) B764005
theorem B953153 : Blo 634301 953153 := bstep (se 2 (by rfl) ⟨357432, by rfl⟩ : syracuseStep 953153 = 714865) B714865
theorem B953171 : Blo 634301 953171 := bstep (se 1 (by rfl) ⟨714878, by rfl⟩ : syracuseStep 953171 = 1429757) B1429757
theorem B953201 : Blo 634301 953201 := bstep (se 2 (by rfl) ⟨357450, by rfl⟩ : syracuseStep 953201 = 714901) B714901
theorem B953219 : Blo 634301 953219 := bstep (se 1 (by rfl) ⟨714914, by rfl⟩ : syracuseStep 953219 = 1429829) B1429829
theorem B1149841 : Blo 634301 1149841 := bstep (se 2 (by rfl) ⟨431190, by rfl⟩ : syracuseStep 1149841 = 862381) B862381
theorem B953249 : Blo 634301 953249 := bstep (se 2 (by rfl) ⟨357468, by rfl⟩ : syracuseStep 953249 = 714937) B714937
theorem B953267 : Blo 634301 953267 := bstep (se 1 (by rfl) ⟨714950, by rfl⟩ : syracuseStep 953267 = 1429901) B1429901
theorem B953297 : Blo 634301 953297 := bstep (se 2 (by rfl) ⟨357486, by rfl⟩ : syracuseStep 953297 = 714973) B714973
theorem B953315 : Blo 634301 953315 := bstep (se 1 (by rfl) ⟨714986, by rfl⟩ : syracuseStep 953315 = 1429973) B1429973
theorem B1018865 : Blo 634301 1018865 := bstep (se 2 (by rfl) ⟨382074, by rfl⟩ : syracuseStep 1018865 = 764149) B764149
theorem B953345 : Blo 634301 953345 := bstep (se 2 (by rfl) ⟨357504, by rfl⟩ : syracuseStep 953345 = 715009) B715009
theorem B953363 : Blo 634301 953363 := bstep (se 1 (by rfl) ⟨715022, by rfl⟩ : syracuseStep 953363 = 1430045) B1430045
theorem B953393 : Blo 634301 953393 := bstep (se 2 (by rfl) ⟨357522, by rfl⟩ : syracuseStep 953393 = 715045) B715045
theorem B953411 : Blo 634301 953411 := bstep (se 1 (by rfl) ⟨715058, by rfl⟩ : syracuseStep 953411 = 1430117) B1430117
theorem B953441 : Blo 634301 953441 := bstep (se 2 (by rfl) ⟨357540, by rfl⟩ : syracuseStep 953441 = 715081) B715081
theorem B953459 : Blo 634301 953459 := bstep (se 1 (by rfl) ⟨715094, by rfl⟩ : syracuseStep 953459 = 1430189) B1430189
theorem B953489 : Blo 634301 953489 := bstep (se 2 (by rfl) ⟨357558, by rfl⟩ : syracuseStep 953489 = 715117) B715117
theorem B953507 : Blo 634301 953507 := bstep (se 1 (by rfl) ⟨715130, by rfl⟩ : syracuseStep 953507 = 1430261) B1430261
theorem B953537 : Blo 634301 953537 := bstep (se 2 (by rfl) ⟨357576, by rfl⟩ : syracuseStep 953537 = 715153) B715153
theorem B2723021 : Blo 634301 2723021 := bstep (se 3 (by rfl) ⟨510566, by rfl⟩ : syracuseStep 2723021 = 1021133) B1021133
theorem B953555 : Blo 634301 953555 := bstep (se 1 (by rfl) ⟨715166, by rfl⟩ : syracuseStep 953555 = 1430333) B1430333
theorem B953585 : Blo 634301 953585 := bstep (se 2 (by rfl) ⟨357594, by rfl⟩ : syracuseStep 953585 = 715189) B715189
theorem B953603 : Blo 634301 953603 := bstep (se 1 (by rfl) ⟨715202, by rfl⟩ : syracuseStep 953603 = 1430405) B1430405
theorem B953633 : Blo 634301 953633 := bstep (se 2 (by rfl) ⟨357612, by rfl⟩ : syracuseStep 953633 = 715225) B715225
theorem B724259 : Blo 634301 724259 := bstep (se 1 (by rfl) ⟨543194, by rfl⟩ : syracuseStep 724259 = 1086389) B1086389
theorem B953651 : Blo 634301 953651 := bstep (se 1 (by rfl) ⟨715238, by rfl⟩ : syracuseStep 953651 = 1430477) B1430477
theorem B953681 : Blo 634301 953681 := bstep (se 2 (by rfl) ⟨357630, by rfl⟩ : syracuseStep 953681 = 715261) B715261
theorem B953699 : Blo 634301 953699 := bstep (se 1 (by rfl) ⟨715274, by rfl⟩ : syracuseStep 953699 = 1430549) B1430549
theorem B953729 : Blo 634301 953729 := bstep (se 2 (by rfl) ⟨357648, by rfl⟩ : syracuseStep 953729 = 715297) B715297
theorem B1609105 : Blo 634301 1609105 := bstep (se 2 (by rfl) ⟨603414, by rfl⟩ : syracuseStep 1609105 = 1206829) B1206829
theorem B953747 : Blo 634301 953747 := bstep (se 1 (by rfl) ⟨715310, by rfl⟩ : syracuseStep 953747 = 1430621) B1430621
theorem B953777 : Blo 634301 953777 := bstep (se 2 (by rfl) ⟨357666, by rfl⟩ : syracuseStep 953777 = 715333) B715333
theorem B953795 : Blo 634301 953795 := bstep (se 1 (by rfl) ⟨715346, by rfl⟩ : syracuseStep 953795 = 1430693) B1430693
theorem B953825 : Blo 634301 953825 := bstep (se 2 (by rfl) ⟨357684, by rfl⟩ : syracuseStep 953825 = 715369) B715369
theorem B953843 : Blo 634301 953843 := bstep (se 1 (by rfl) ⟨715382, by rfl⟩ : syracuseStep 953843 = 1430765) B1430765
theorem B953873 : Blo 634301 953873 := bstep (se 2 (by rfl) ⟨357702, by rfl⟩ : syracuseStep 953873 = 715405) B715405
theorem B953891 : Blo 634301 953891 := bstep (se 1 (by rfl) ⟨715418, by rfl⟩ : syracuseStep 953891 = 1430837) B1430837
theorem B953921 : Blo 634301 953921 := bstep (se 2 (by rfl) ⟨357720, by rfl⟩ : syracuseStep 953921 = 715441) B715441
theorem B953939 : Blo 634301 953939 := bstep (se 1 (by rfl) ⟨715454, by rfl⟩ : syracuseStep 953939 = 1430909) B1430909
theorem B953969 : Blo 634301 953969 := bstep (se 2 (by rfl) ⟨357738, by rfl⟩ : syracuseStep 953969 = 715477) B715477
theorem B953987 : Blo 634301 953987 := bstep (se 1 (by rfl) ⟨715490, by rfl⟩ : syracuseStep 953987 = 1430981) B1430981
theorem B954017 : Blo 634301 954017 := bstep (se 2 (by rfl) ⟨357756, by rfl⟩ : syracuseStep 954017 = 715513) B715513
theorem B1609379 : Blo 634301 1609379 := bstep (se 1 (by rfl) ⟨1207034, by rfl⟩ : syracuseStep 1609379 = 2414069) B2414069
theorem B954035 : Blo 634301 954035 := bstep (se 1 (by rfl) ⟨715526, by rfl⟩ : syracuseStep 954035 = 1431053) B1431053
theorem B724675 : Blo 634301 724675 := bstep (se 1 (by rfl) ⟨543506, by rfl⟩ : syracuseStep 724675 = 1087013) B1087013
theorem B954065 : Blo 634301 954065 := bstep (se 2 (by rfl) ⟨357774, by rfl⟩ : syracuseStep 954065 = 715549) B715549
theorem B954083 : Blo 634301 954083 := bstep (se 1 (by rfl) ⟨715562, by rfl⟩ : syracuseStep 954083 = 1431125) B1431125
theorem B1085185 : Blo 634301 1085185 := bstep (se 2 (by rfl) ⟨406944, by rfl⟩ : syracuseStep 1085185 = 813889) B813889
theorem B954113 : Blo 634301 954113 := bstep (se 2 (by rfl) ⟨357792, by rfl⟩ : syracuseStep 954113 = 715585) B715585
theorem B954131 : Blo 634301 954131 := bstep (se 1 (by rfl) ⟨715598, by rfl⟩ : syracuseStep 954131 = 1431197) B1431197
theorem B954161 : Blo 634301 954161 := bstep (se 2 (by rfl) ⟨357810, by rfl⟩ : syracuseStep 954161 = 715621) B715621
theorem B954179 : Blo 634301 954179 := bstep (se 1 (by rfl) ⟨715634, by rfl⟩ : syracuseStep 954179 = 1431269) B1431269
theorem B954209 : Blo 634301 954209 := bstep (se 2 (by rfl) ⟨357828, by rfl⟩ : syracuseStep 954209 = 715657) B715657
theorem B1609571 : Blo 634301 1609571 := bstep (se 1 (by rfl) ⟨1207178, by rfl⟩ : syracuseStep 1609571 = 2414357) B2414357
theorem B954227 : Blo 634301 954227 := bstep (se 1 (by rfl) ⟨715670, by rfl⟩ : syracuseStep 954227 = 1431341) B1431341
theorem B954257 : Blo 634301 954257 := bstep (se 2 (by rfl) ⟨357846, by rfl⟩ : syracuseStep 954257 = 715693) B715693
theorem B954275 : Blo 634301 954275 := bstep (se 1 (by rfl) ⟨715706, by rfl⟩ : syracuseStep 954275 = 1431413) B1431413
theorem B954305 : Blo 634301 954305 := bstep (se 2 (by rfl) ⟨357864, by rfl⟩ : syracuseStep 954305 = 715729) B715729
theorem B954323 : Blo 634301 954323 := bstep (se 1 (by rfl) ⟨715742, by rfl⟩ : syracuseStep 954323 = 1431485) B1431485
theorem B954353 : Blo 634301 954353 := bstep (se 2 (by rfl) ⟨357882, by rfl⟩ : syracuseStep 954353 = 715765) B715765
theorem B954371 : Blo 634301 954371 := bstep (se 1 (by rfl) ⟨715778, by rfl⟩ : syracuseStep 954371 = 1431557) B1431557
theorem B954401 : Blo 634301 954401 := bstep (se 2 (by rfl) ⟨357900, by rfl⟩ : syracuseStep 954401 = 715801) B715801
theorem B1806371 : Blo 634301 1806371 := bstep (se 1 (by rfl) ⟨1354778, by rfl⟩ : syracuseStep 1806371 = 2709557) B2709557
theorem B954419 : Blo 634301 954419 := bstep (se 1 (by rfl) ⟨715814, by rfl⟩ : syracuseStep 954419 = 1431629) B1431629
theorem B954449 : Blo 634301 954449 := bstep (se 2 (by rfl) ⟨357918, by rfl⟩ : syracuseStep 954449 = 715837) B715837
theorem B954467 : Blo 634301 954467 := bstep (se 1 (by rfl) ⟨715850, by rfl⟩ : syracuseStep 954467 = 1431701) B1431701
theorem B954497 : Blo 634301 954497 := bstep (se 2 (by rfl) ⟨357936, by rfl⟩ : syracuseStep 954497 = 715873) B715873
theorem B954515 : Blo 634301 954515 := bstep (se 1 (by rfl) ⟨715886, by rfl⟩ : syracuseStep 954515 = 1431773) B1431773
theorem B3215537 : Blo 634301 3215537 := bstep (se 2 (by rfl) ⟨1205826, by rfl⟩ : syracuseStep 3215537 = 2411653) B2411653
theorem B954545 : Blo 634301 954545 := bstep (se 2 (by rfl) ⟨357954, by rfl⟩ : syracuseStep 954545 = 715909) B715909
theorem B954563 : Blo 634301 954563 := bstep (se 1 (by rfl) ⟨715922, by rfl⟩ : syracuseStep 954563 = 1431845) B1431845
theorem B954593 : Blo 634301 954593 := bstep (se 2 (by rfl) ⟨357972, by rfl⟩ : syracuseStep 954593 = 715945) B715945
theorem B954611 : Blo 634301 954611 := bstep (se 1 (by rfl) ⟨715958, by rfl⟩ : syracuseStep 954611 = 1431917) B1431917
theorem B1085699 : Blo 634301 1085699 := bstep (se 1 (by rfl) ⟨814274, by rfl⟩ : syracuseStep 1085699 = 1628549) B1628549
theorem B954641 : Blo 634301 954641 := bstep (se 2 (by rfl) ⟨357990, by rfl⟩ : syracuseStep 954641 = 715981) B715981
theorem B954659 : Blo 634301 954659 := bstep (se 1 (by rfl) ⟨715994, by rfl⟩ : syracuseStep 954659 = 1431989) B1431989
theorem B3477809 : Blo 634301 3477809 := bstep (se 2 (by rfl) ⟨1304178, by rfl⟩ : syracuseStep 3477809 = 2608357) B2608357
theorem B954689 : Blo 634301 954689 := bstep (se 2 (by rfl) ⟨358008, by rfl⟩ : syracuseStep 954689 = 716017) B716017
theorem B954707 : Blo 634301 954707 := bstep (se 1 (by rfl) ⟨716030, by rfl⟩ : syracuseStep 954707 = 1432061) B1432061
theorem B954737 : Blo 634301 954737 := bstep (se 2 (by rfl) ⟨358026, by rfl⟩ : syracuseStep 954737 = 716053) B716053
theorem B954755 : Blo 634301 954755 := bstep (se 1 (by rfl) ⟨716066, by rfl⟩ : syracuseStep 954755 = 1432133) B1432133
theorem B954785 : Blo 634301 954785 := bstep (se 2 (by rfl) ⟨358044, by rfl⟩ : syracuseStep 954785 = 716089) B716089
theorem B954803 : Blo 634301 954803 := bstep (se 1 (by rfl) ⟨716102, by rfl⟩ : syracuseStep 954803 = 1432205) B1432205
theorem B954833 : Blo 634301 954833 := bstep (se 2 (by rfl) ⟨358062, by rfl⟩ : syracuseStep 954833 = 716125) B716125
theorem B954851 : Blo 634301 954851 := bstep (se 1 (by rfl) ⟨716138, by rfl⟩ : syracuseStep 954851 = 1432277) B1432277
theorem B954881 : Blo 634301 954881 := bstep (se 2 (by rfl) ⟨358080, by rfl⟩ : syracuseStep 954881 = 716161) B716161
theorem B954899 : Blo 634301 954899 := bstep (se 1 (by rfl) ⟨716174, by rfl⟩ : syracuseStep 954899 = 1432349) B1432349
theorem B954929 : Blo 634301 954929 := bstep (se 2 (by rfl) ⟨358098, by rfl⟩ : syracuseStep 954929 = 716197) B716197
theorem B954947 : Blo 634301 954947 := bstep (se 1 (by rfl) ⟨716210, by rfl⟩ : syracuseStep 954947 = 1432421) B1432421
theorem B954977 : Blo 634301 954977 := bstep (se 2 (by rfl) ⟨358116, by rfl⟩ : syracuseStep 954977 = 716233) B716233
theorem B954995 : Blo 634301 954995 := bstep (se 1 (by rfl) ⟨716246, by rfl⟩ : syracuseStep 954995 = 1432493) B1432493
theorem B955025 : Blo 634301 955025 := bstep (se 2 (by rfl) ⟨358134, by rfl⟩ : syracuseStep 955025 = 716269) B716269
theorem B955043 : Blo 634301 955043 := bstep (se 1 (by rfl) ⟨716282, by rfl⟩ : syracuseStep 955043 = 1432565) B1432565
theorem B1020595 : Blo 634301 1020595 := bstep (se 1 (by rfl) ⟨765446, by rfl⟩ : syracuseStep 1020595 = 1530893) B1530893
theorem B955073 : Blo 634301 955073 := bstep (se 2 (by rfl) ⟨358152, by rfl⟩ : syracuseStep 955073 = 716305) B716305
theorem B955091 : Blo 634301 955091 := bstep (se 1 (by rfl) ⟨716318, by rfl⟩ : syracuseStep 955091 = 1432637) B1432637
theorem B955121 : Blo 634301 955121 := bstep (se 2 (by rfl) ⟨358170, by rfl⟩ : syracuseStep 955121 = 716341) B716341
theorem B955139 : Blo 634301 955139 := bstep (se 1 (by rfl) ⟨716354, by rfl⟩ : syracuseStep 955139 = 1432709) B1432709
theorem B1610513 : Blo 634301 1610513 := bstep (se 2 (by rfl) ⟨603942, by rfl⟩ : syracuseStep 1610513 = 1207885) B1207885
theorem B1020691 : Blo 634301 1020691 := bstep (se 1 (by rfl) ⟨765518, by rfl⟩ : syracuseStep 1020691 = 1531037) B1531037
theorem B955169 : Blo 634301 955169 := bstep (se 2 (by rfl) ⟨358188, by rfl⟩ : syracuseStep 955169 = 716377) B716377
theorem B955187 : Blo 634301 955187 := bstep (se 1 (by rfl) ⟨716390, by rfl⟩ : syracuseStep 955187 = 1432781) B1432781
theorem B1610563 : Blo 634301 1610563 := bstep (se 1 (by rfl) ⟨1207922, by rfl⟩ : syracuseStep 1610563 = 2415845) B2415845
theorem B1807181 : Blo 634301 1807181 := bstep (se 3 (by rfl) ⟨338846, by rfl⟩ : syracuseStep 1807181 = 677693) B677693
theorem B955217 : Blo 634301 955217 := bstep (se 2 (by rfl) ⟨358206, by rfl⟩ : syracuseStep 955217 = 716413) B716413
theorem B955235 : Blo 634301 955235 := bstep (se 1 (by rfl) ⟨716426, by rfl⟩ : syracuseStep 955235 = 1432853) B1432853
theorem B955265 : Blo 634301 955265 := bstep (se 2 (by rfl) ⟨358224, by rfl⟩ : syracuseStep 955265 = 716449) B716449
theorem B955283 : Blo 634301 955283 := bstep (se 1 (by rfl) ⟨716462, by rfl⟩ : syracuseStep 955283 = 1432925) B1432925
theorem B955313 : Blo 634301 955313 := bstep (se 2 (by rfl) ⟨358242, by rfl⟩ : syracuseStep 955313 = 716485) B716485
theorem B1020851 : Blo 634301 1020851 := bstep (se 1 (by rfl) ⟨765638, by rfl⟩ : syracuseStep 1020851 = 1531277) B1531277
theorem B955331 : Blo 634301 955331 := bstep (se 1 (by rfl) ⟨716498, by rfl⟩ : syracuseStep 955331 = 1432997) B1432997
theorem B1610705 : Blo 634301 1610705 := bstep (se 2 (by rfl) ⟨604014, by rfl⟩ : syracuseStep 1610705 = 1208029) B1208029
theorem B955361 : Blo 634301 955361 := bstep (se 2 (by rfl) ⟨358260, by rfl⟩ : syracuseStep 955361 = 716521) B716521
theorem B955379 : Blo 634301 955379 := bstep (se 1 (by rfl) ⟨716534, by rfl⟩ : syracuseStep 955379 = 1433069) B1433069
theorem B1807373 : Blo 634301 1807373 := bstep (se 3 (by rfl) ⟨338882, by rfl⟩ : syracuseStep 1807373 = 677765) B677765
theorem B955409 : Blo 634301 955409 := bstep (se 2 (by rfl) ⟨358278, by rfl⟩ : syracuseStep 955409 = 716557) B716557
theorem B955427 : Blo 634301 955427 := bstep (se 1 (by rfl) ⟨716570, by rfl⟩ : syracuseStep 955427 = 1433141) B1433141
theorem B955457 : Blo 634301 955457 := bstep (se 2 (by rfl) ⟨358296, by rfl⟩ : syracuseStep 955457 = 716593) B716593
theorem B955475 : Blo 634301 955475 := bstep (se 1 (by rfl) ⟨716606, by rfl⟩ : syracuseStep 955475 = 1433213) B1433213
theorem B955505 : Blo 634301 955505 := bstep (se 2 (by rfl) ⟨358314, by rfl⟩ : syracuseStep 955505 = 716629) B716629
theorem B955523 : Blo 634301 955523 := bstep (se 1 (by rfl) ⟨716642, by rfl⟩ : syracuseStep 955523 = 1433285) B1433285
theorem B955553 : Blo 634301 955553 := bstep (se 2 (by rfl) ⟨358332, by rfl⟩ : syracuseStep 955553 = 716665) B716665
theorem B955571 : Blo 634301 955571 := bstep (se 1 (by rfl) ⟨716678, by rfl⟩ : syracuseStep 955571 = 1433357) B1433357
theorem B955601 : Blo 634301 955601 := bstep (se 2 (by rfl) ⟨358350, by rfl⟩ : syracuseStep 955601 = 716701) B716701
theorem B955619 : Blo 634301 955619 := bstep (se 1 (by rfl) ⟨716714, by rfl⟩ : syracuseStep 955619 = 1433429) B1433429
theorem B3314915 : Blo 634301 3314915 := bstep (se 1 (by rfl) ⟨2486186, by rfl⟩ : syracuseStep 3314915 = 4972373) B4972373
theorem B955649 : Blo 634301 955649 := bstep (se 2 (by rfl) ⟨358368, by rfl⟩ : syracuseStep 955649 = 716737) B716737
theorem B955667 : Blo 634301 955667 := bstep (se 1 (by rfl) ⟨716750, by rfl⟩ : syracuseStep 955667 = 1433501) B1433501
theorem B955697 : Blo 634301 955697 := bstep (se 2 (by rfl) ⟨358386, by rfl⟩ : syracuseStep 955697 = 716773) B716773
theorem B8262965 : Blo 634301 8262965 := bstep (se 5 (by rfl) ⟨387326, by rfl⟩ : syracuseStep 8262965 = 774653) B774653
theorem B955715 : Blo 634301 955715 := bstep (se 1 (by rfl) ⟨716786, by rfl⟩ : syracuseStep 955715 = 1433573) B1433573
theorem B955745 : Blo 634301 955745 := bstep (se 2 (by rfl) ⟨358404, by rfl⟩ : syracuseStep 955745 = 716809) B716809
theorem B955763 : Blo 634301 955763 := bstep (se 1 (by rfl) ⟨716822, by rfl⟩ : syracuseStep 955763 = 1433645) B1433645
theorem B955793 : Blo 634301 955793 := bstep (se 2 (by rfl) ⟨358422, by rfl⟩ : syracuseStep 955793 = 716845) B716845
theorem B955811 : Blo 634301 955811 := bstep (se 1 (by rfl) ⟨716858, by rfl⟩ : syracuseStep 955811 = 1433717) B1433717
theorem B955841 : Blo 634301 955841 := bstep (se 2 (by rfl) ⟨358440, by rfl⟩ : syracuseStep 955841 = 716881) B716881
theorem B955859 : Blo 634301 955859 := bstep (se 1 (by rfl) ⟨716894, by rfl⟩ : syracuseStep 955859 = 1433789) B1433789
theorem B955889 : Blo 634301 955889 := bstep (se 2 (by rfl) ⟨358458, by rfl⟩ : syracuseStep 955889 = 716917) B716917
theorem B955907 : Blo 634301 955907 := bstep (se 1 (by rfl) ⟨716930, by rfl⟩ : syracuseStep 955907 = 1433861) B1433861
theorem B955937 : Blo 634301 955937 := bstep (se 2 (by rfl) ⟨358476, by rfl⟩ : syracuseStep 955937 = 716953) B716953
theorem B4068899 : Blo 634301 4068899 := bstep (se 1 (by rfl) ⟨3051674, by rfl⟩ : syracuseStep 4068899 = 6103349) B6103349
theorem B955955 : Blo 634301 955955 := bstep (se 1 (by rfl) ⟨716966, by rfl⟩ : syracuseStep 955955 = 1433933) B1433933
theorem B10851893 : Blo 634301 10851893 := bstep (se 5 (by rfl) ⟨508682, by rfl⟩ : syracuseStep 10851893 = 1017365) B1017365
theorem B955985 : Blo 634301 955985 := bstep (se 2 (by rfl) ⟨358494, by rfl⟩ : syracuseStep 955985 = 716989) B716989
theorem B3216995 : Blo 634301 3216995 := bstep (se 1 (by rfl) ⟨2412746, by rfl⟩ : syracuseStep 3216995 = 4825493) B4825493
theorem B956003 : Blo 634301 956003 := bstep (se 1 (by rfl) ⟨717002, by rfl⟩ : syracuseStep 956003 = 1434005) B1434005
theorem B956033 : Blo 634301 956033 := bstep (se 2 (by rfl) ⟨358512, by rfl⟩ : syracuseStep 956033 = 717025) B717025
theorem B956051 : Blo 634301 956051 := bstep (se 1 (by rfl) ⟨717038, by rfl⟩ : syracuseStep 956051 = 1434077) B1434077
theorem B956081 : Blo 634301 956081 := bstep (se 2 (by rfl) ⟨358530, by rfl⟩ : syracuseStep 956081 = 717061) B717061
theorem B956099 : Blo 634301 956099 := bstep (se 1 (by rfl) ⟨717074, by rfl⟩ : syracuseStep 956099 = 1434149) B1434149
theorem B956129 : Blo 634301 956129 := bstep (se 2 (by rfl) ⟨358548, by rfl⟩ : syracuseStep 956129 = 717097) B717097
theorem B18618083 : Blo 634301 18618083 := bstep (se 1 (by rfl) ⟨13963562, by rfl⟩ : syracuseStep 18618083 = 27927125) B27927125
theorem B956147 : Blo 634301 956147 := bstep (se 1 (by rfl) ⟨717110, by rfl⟩ : syracuseStep 956147 = 1434221) B1434221
theorem B956177 : Blo 634301 956177 := bstep (se 2 (by rfl) ⟨358566, by rfl⟩ : syracuseStep 956177 = 717133) B717133
theorem B956195 : Blo 634301 956195 := bstep (se 1 (by rfl) ⟨717146, by rfl⟩ : syracuseStep 956195 = 1434293) B1434293
theorem B956225 : Blo 634301 956225 := bstep (se 2 (by rfl) ⟨358584, by rfl⟩ : syracuseStep 956225 = 717169) B717169
theorem B956243 : Blo 634301 956243 := bstep (se 1 (by rfl) ⟨717182, by rfl⟩ : syracuseStep 956243 = 1434365) B1434365
theorem B956273 : Blo 634301 956273 := bstep (se 2 (by rfl) ⟨358602, by rfl⟩ : syracuseStep 956273 = 717205) B717205
theorem B1021825 : Blo 634301 1021825 := bstep (se 2 (by rfl) ⟨383184, by rfl⟩ : syracuseStep 1021825 = 766369) B766369
theorem B956291 : Blo 634301 956291 := bstep (se 1 (by rfl) ⟨717218, by rfl⟩ : syracuseStep 956291 = 1434437) B1434437
theorem B956321 : Blo 634301 956321 := bstep (se 2 (by rfl) ⟨358620, by rfl⟩ : syracuseStep 956321 = 717241) B717241
theorem B1611697 : Blo 634301 1611697 := bstep (se 2 (by rfl) ⟨604386, by rfl⟩ : syracuseStep 1611697 = 1208773) B1208773
theorem B956339 : Blo 634301 956339 := bstep (se 1 (by rfl) ⟨717254, by rfl⟩ : syracuseStep 956339 = 1434509) B1434509
theorem B956369 : Blo 634301 956369 := bstep (se 2 (by rfl) ⟨358638, by rfl⟩ : syracuseStep 956369 = 717277) B717277
theorem B956387 : Blo 634301 956387 := bstep (se 1 (by rfl) ⟨717290, by rfl⟩ : syracuseStep 956387 = 1434581) B1434581
theorem B1808365 : Blo 634301 1808365 := bstep (se 3 (by rfl) ⟨339068, by rfl⟩ : syracuseStep 1808365 = 678137) B678137
theorem B956417 : Blo 634301 956417 := bstep (se 2 (by rfl) ⟨358656, by rfl⟩ : syracuseStep 956417 = 717313) B717313
theorem B956435 : Blo 634301 956435 := bstep (se 1 (by rfl) ⟨717326, by rfl⟩ : syracuseStep 956435 = 1434653) B1434653
theorem B956465 : Blo 634301 956465 := bstep (se 2 (by rfl) ⟨358674, by rfl⟩ : syracuseStep 956465 = 717349) B717349
theorem B956483 : Blo 634301 956483 := bstep (se 1 (by rfl) ⟨717362, by rfl⟩ : syracuseStep 956483 = 1434725) B1434725
theorem B956513 : Blo 634301 956513 := bstep (se 2 (by rfl) ⟨358692, by rfl⟩ : syracuseStep 956513 = 717385) B717385
theorem B956531 : Blo 634301 956531 := bstep (se 1 (by rfl) ⟨717398, by rfl⟩ : syracuseStep 956531 = 1434797) B1434797
theorem B956561 : Blo 634301 956561 := bstep (se 2 (by rfl) ⟨358710, by rfl⟩ : syracuseStep 956561 = 717421) B717421
theorem B956579 : Blo 634301 956579 := bstep (se 1 (by rfl) ⟨717434, by rfl⟩ : syracuseStep 956579 = 1434869) B1434869
theorem B956609 : Blo 634301 956609 := bstep (se 2 (by rfl) ⟨358728, by rfl⟩ : syracuseStep 956609 = 717457) B717457
theorem B1611971 : Blo 634301 1611971 := bstep (se 1 (by rfl) ⟨1208978, by rfl⟩ : syracuseStep 1611971 = 2417957) B2417957
theorem B956627 : Blo 634301 956627 := bstep (se 1 (by rfl) ⟨717470, by rfl⟩ : syracuseStep 956627 = 1434941) B1434941
theorem B956657 : Blo 634301 956657 := bstep (se 2 (by rfl) ⟨358746, by rfl⟩ : syracuseStep 956657 = 717493) B717493
theorem B956675 : Blo 634301 956675 := bstep (se 1 (by rfl) ⟨717506, by rfl⟩ : syracuseStep 956675 = 1435013) B1435013
theorem B956705 : Blo 634301 956705 := bstep (se 2 (by rfl) ⟨358764, by rfl⟩ : syracuseStep 956705 = 717529) B717529
theorem B956723 : Blo 634301 956723 := bstep (se 1 (by rfl) ⟨717542, by rfl⟩ : syracuseStep 956723 = 1435085) B1435085
theorem B956753 : Blo 634301 956753 := bstep (se 2 (by rfl) ⟨358782, by rfl⟩ : syracuseStep 956753 = 717565) B717565
theorem B956771 : Blo 634301 956771 := bstep (se 1 (by rfl) ⟨717578, by rfl⟩ : syracuseStep 956771 = 1435157) B1435157
theorem B956801 : Blo 634301 956801 := bstep (se 2 (by rfl) ⟨358800, by rfl⟩ : syracuseStep 956801 = 717601) B717601
theorem B1612163 : Blo 634301 1612163 := bstep (se 1 (by rfl) ⟨1209122, by rfl⟩ : syracuseStep 1612163 = 2418245) B2418245
theorem B3217805 : Blo 634301 3217805 := bstep (se 3 (by rfl) ⟨603338, by rfl⟩ : syracuseStep 3217805 = 1206677) B1206677
theorem B956819 : Blo 634301 956819 := bstep (se 1 (by rfl) ⟨717614, by rfl⟩ : syracuseStep 956819 = 1435229) B1435229
theorem B956849 : Blo 634301 956849 := bstep (se 2 (by rfl) ⟨358818, by rfl⟩ : syracuseStep 956849 = 717637) B717637
theorem B956867 : Blo 634301 956867 := bstep (se 1 (by rfl) ⟨717650, by rfl⟩ : syracuseStep 956867 = 1435301) B1435301
theorem B956897 : Blo 634301 956897 := bstep (se 2 (by rfl) ⟨358836, by rfl⟩ : syracuseStep 956897 = 717673) B717673
theorem B2038243 : Blo 634301 2038243 := bstep (se 1 (by rfl) ⟨1528682, by rfl⟩ : syracuseStep 2038243 = 3057365) B3057365
theorem B956915 : Blo 634301 956915 := bstep (se 1 (by rfl) ⟨717686, by rfl⟩ : syracuseStep 956915 = 1435373) B1435373
theorem B1088003 : Blo 634301 1088003 := bstep (se 1 (by rfl) ⟨816002, by rfl⟩ : syracuseStep 1088003 = 1632005) B1632005
theorem B956945 : Blo 634301 956945 := bstep (se 2 (by rfl) ⟨358854, by rfl⟩ : syracuseStep 956945 = 717709) B717709
theorem B956963 : Blo 634301 956963 := bstep (se 1 (by rfl) ⟨717722, by rfl⟩ : syracuseStep 956963 = 1435445) B1435445
theorem B956993 : Blo 634301 956993 := bstep (se 2 (by rfl) ⟨358872, by rfl⟩ : syracuseStep 956993 = 717745) B717745
theorem B957011 : Blo 634301 957011 := bstep (se 1 (by rfl) ⟨717758, by rfl⟩ : syracuseStep 957011 = 1435517) B1435517
theorem B957041 : Blo 634301 957041 := bstep (se 2 (by rfl) ⟨358890, by rfl⟩ : syracuseStep 957041 = 717781) B717781
theorem B957059 : Blo 634301 957059 := bstep (se 1 (by rfl) ⟨717794, by rfl⟩ : syracuseStep 957059 = 1435589) B1435589
theorem B957089 : Blo 634301 957089 := bstep (se 2 (by rfl) ⟨358908, by rfl⟩ : syracuseStep 957089 = 717817) B717817
theorem B957107 : Blo 634301 957107 := bstep (se 1 (by rfl) ⟨717830, by rfl⟩ : syracuseStep 957107 = 1435661) B1435661
theorem B957137 : Blo 634301 957137 := bstep (se 2 (by rfl) ⟨358926, by rfl⟩ : syracuseStep 957137 = 717853) B717853
theorem B957155 : Blo 634301 957155 := bstep (se 1 (by rfl) ⟨717866, by rfl⟩ : syracuseStep 957155 = 1435733) B1435733
theorem B957185 : Blo 634301 957185 := bstep (se 2 (by rfl) ⟨358944, by rfl⟩ : syracuseStep 957185 = 717889) B717889
theorem B957203 : Blo 634301 957203 := bstep (se 1 (by rfl) ⟨717902, by rfl⟩ : syracuseStep 957203 = 1435805) B1435805
theorem B957233 : Blo 634301 957233 := bstep (se 2 (by rfl) ⟨358962, by rfl⟩ : syracuseStep 957233 = 717925) B717925
theorem B957251 : Blo 634301 957251 := bstep (se 1 (by rfl) ⟨717938, by rfl⟩ : syracuseStep 957251 = 1435877) B1435877
theorem B957281 : Blo 634301 957281 := bstep (se 2 (by rfl) ⟨358980, by rfl⟩ : syracuseStep 957281 = 717961) B717961
theorem B957299 : Blo 634301 957299 := bstep (se 1 (by rfl) ⟨717974, by rfl⟩ : syracuseStep 957299 = 1435949) B1435949
theorem B957329 : Blo 634301 957329 := bstep (se 2 (by rfl) ⟨358998, by rfl⟩ : syracuseStep 957329 = 717997) B717997
theorem B957347 : Blo 634301 957347 := bstep (se 1 (by rfl) ⟨718010, by rfl⟩ : syracuseStep 957347 = 1436021) B1436021
theorem B957377 : Blo 634301 957377 := bstep (se 2 (by rfl) ⟨359016, by rfl⟩ : syracuseStep 957377 = 718033) B718033
theorem B957395 : Blo 634301 957395 := bstep (se 1 (by rfl) ⟨718046, by rfl⟩ : syracuseStep 957395 = 1436093) B1436093
theorem B4824035 : Blo 634301 4824035 := bstep (se 1 (by rfl) ⟨3618026, by rfl⟩ : syracuseStep 4824035 = 7236053) B7236053
theorem B957425 : Blo 634301 957425 := bstep (se 2 (by rfl) ⟨359034, by rfl⟩ : syracuseStep 957425 = 718069) B718069
theorem B957443 : Blo 634301 957443 := bstep (se 1 (by rfl) ⟨718082, by rfl⟩ : syracuseStep 957443 = 1436165) B1436165
theorem B859267 : Blo 634301 859267 := bstep (se 1 (by rfl) ⟨644450, by rfl⟩ : syracuseStep 859267 = 1288901) B1288901
theorem B1613105 : Blo 634301 1613105 := bstep (se 2 (by rfl) ⟨604914, by rfl⟩ : syracuseStep 1613105 = 1209829) B1209829
theorem B1613155 : Blo 634301 1613155 := bstep (se 1 (by rfl) ⟨1209866, by rfl⟩ : syracuseStep 1613155 = 2419733) B2419733
theorem B4070897 : Blo 634301 4070897 := bstep (se 2 (by rfl) ⟨1526586, by rfl⟩ : syracuseStep 4070897 = 3053173) B3053173
theorem B1613297 : Blo 634301 1613297 := bstep (se 2 (by rfl) ⟨604986, by rfl⟩ : syracuseStep 1613297 = 1209973) B1209973
theorem B1089091 : Blo 634301 1089091 := bstep (se 1 (by rfl) ⟨816818, by rfl⟩ : syracuseStep 1089091 = 1633637) B1633637
theorem B1810097 : Blo 634301 1810097 := bstep (se 2 (by rfl) ⟨678786, by rfl⟩ : syracuseStep 1810097 = 1357573) B1357573
theorem B6889187 : Blo 634301 6889187 := bstep (se 1 (by rfl) ⟨5166890, by rfl⟩ : syracuseStep 6889187 = 10333781) B10333781
theorem B1089331 : Blo 634301 1089331 := bstep (se 1 (by rfl) ⟨816998, by rfl⟩ : syracuseStep 1089331 = 1633997) B1633997
theorem B1810289 : Blo 634301 1810289 := bstep (se 2 (by rfl) ⟨678858, by rfl⟩ : syracuseStep 1810289 = 1357717) B1357717
theorem B3448817 : Blo 634301 3448817 := bstep (se 2 (by rfl) ⟨1293306, by rfl⟩ : syracuseStep 3448817 = 2586613) B2586613
theorem B1286275 : Blo 634301 1286275 := bstep (se 1 (by rfl) ⟨964706, by rfl⟩ : syracuseStep 1286275 = 1929413) B1929413
theorem B860305 : Blo 634301 860305 := bstep (se 2 (by rfl) ⟨322614, by rfl⟩ : syracuseStep 860305 = 645229) B645229
theorem B1286371 : Blo 634301 1286371 := bstep (se 1 (by rfl) ⟨964778, by rfl⟩ : syracuseStep 1286371 = 1929557) B1929557
theorem B1745137 : Blo 634301 1745137 := bstep (se 2 (by rfl) ⟨654426, by rfl⟩ : syracuseStep 1745137 = 1308853) B1308853
theorem B1548739 : Blo 634301 1548739 := bstep (se 1 (by rfl) ⟨1161554, by rfl⟩ : syracuseStep 1548739 = 2323109) B2323109
theorem B1614289 : Blo 634301 1614289 := bstep (se 2 (by rfl) ⟨605358, by rfl⟩ : syracuseStep 1614289 = 1210717) B1210717
theorem B2040461 : Blo 634301 2040461 := bstep (se 3 (by rfl) ⟨382586, by rfl⟩ : syracuseStep 2040461 = 765173) B765173
theorem B1614563 : Blo 634301 1614563 := bstep (se 1 (by rfl) ⟨1210922, by rfl⟩ : syracuseStep 1614563 = 2421845) B2421845
theorem B3613517 : Blo 634301 3613517 := bstep (se 3 (by rfl) ⟨677534, by rfl⟩ : syracuseStep 3613517 = 1355069) B1355069
theorem B1811281 : Blo 634301 1811281 := bstep (se 2 (by rfl) ⟨679230, by rfl⟩ : syracuseStep 1811281 = 1358461) B1358461
theorem B762755 : Blo 634301 762755 := bstep (se 1 (by rfl) ⟨572066, by rfl⟩ : syracuseStep 762755 = 1144133) B1144133
theorem B1614755 : Blo 634301 1614755 := bstep (se 1 (by rfl) ⟨1211066, by rfl⟩ : syracuseStep 1614755 = 2422133) B2422133
theorem B1090577 : Blo 634301 1090577 := bstep (se 2 (by rfl) ⟨408966, by rfl⟩ : syracuseStep 1090577 = 817933) B817933
theorem B2040881 : Blo 634301 2040881 := bstep (se 2 (by rfl) ⟨765330, by rfl⟩ : syracuseStep 2040881 = 1530661) B1530661
theorem B1811555 : Blo 634301 1811555 := bstep (se 1 (by rfl) ⟨1358666, by rfl⟩ : syracuseStep 1811555 = 2717333) B2717333
theorem B4072589 : Blo 634301 4072589 := bstep (se 3 (by rfl) ⟨763610, by rfl⟩ : syracuseStep 4072589 = 1527221) B1527221
theorem B697555 : Blo 634301 697555 := bstep (se 1 (by rfl) ⟨523166, by rfl⟩ : syracuseStep 697555 = 1046333) B1046333
theorem B3220721 : Blo 634301 3220721 := bstep (se 2 (by rfl) ⟨1207770, by rfl⟩ : syracuseStep 3220721 = 2415541) B2415541
theorem B861473 : Blo 634301 861473 := bstep (se 2 (by rfl) ⟨323052, by rfl⟩ : syracuseStep 861473 = 646105) B646105
theorem B1811747 : Blo 634301 1811747 := bstep (se 1 (by rfl) ⟨1358810, by rfl⟩ : syracuseStep 1811747 = 2717621) B2717621
theorem B1222033 : Blo 634301 1222033 := bstep (se 2 (by rfl) ⟨458262, by rfl⟩ : syracuseStep 1222033 = 916525) B916525
theorem B5449457 : Blo 634301 5449457 := bstep (se 2 (by rfl) ⟨2043546, by rfl⟩ : syracuseStep 5449457 = 4087093) B4087093
theorem B862003 : Blo 634301 862003 := bstep (se 1 (by rfl) ⟨646502, by rfl⟩ : syracuseStep 862003 = 1293005) B1293005
theorem B1615697 : Blo 634301 1615697 := bstep (se 2 (by rfl) ⟨605886, by rfl⟩ : syracuseStep 1615697 = 1211773) B1211773
theorem B1091411 : Blo 634301 1091411 := bstep (se 1 (by rfl) ⟨818558, by rfl⟩ : syracuseStep 1091411 = 1637117) B1637117
theorem B3483661 : Blo 634301 3483661 := bstep (se 3 (by rfl) ⟨653186, by rfl⟩ : syracuseStep 3483661 = 1306373) B1306373
theorem B1812557 : Blo 634301 1812557 := bstep (se 3 (by rfl) ⟨339854, by rfl⟩ : syracuseStep 1812557 = 679709) B679709
theorem B1812739 : Blo 634301 1812739 := bstep (se 1 (by rfl) ⟨1359554, by rfl⟩ : syracuseStep 1812739 = 2719109) B2719109
theorem B1223011 : Blo 634301 1223011 := bstep (se 1 (by rfl) ⟨917258, by rfl⟩ : syracuseStep 1223011 = 1834517) B1834517
theorem B3058019 : Blo 634301 3058019 := bstep (se 1 (by rfl) ⟨2293514, by rfl⟩ : syracuseStep 3058019 = 4587029) B4587029
theorem B2238929 : Blo 634301 2238929 := bstep (se 2 (by rfl) ⟨839598, by rfl⟩ : syracuseStep 2238929 = 1679197) B1679197
theorem B1223203 : Blo 634301 1223203 := bstep (se 1 (by rfl) ⟨917402, by rfl⟩ : syracuseStep 1223203 = 1834805) B1834805
theorem B3222179 : Blo 634301 3222179 := bstep (se 1 (by rfl) ⟨2416634, by rfl⟩ : syracuseStep 3222179 = 4833269) B4833269
theorem B1813229 : Blo 634301 1813229 := bstep (se 3 (by rfl) ⟨339980, by rfl⟩ : syracuseStep 1813229 = 679961) B679961
theorem B2173873 : Blo 634301 2173873 := bstep (se 2 (by rfl) ⟨815202, by rfl⟩ : syracuseStep 2173873 = 1630405) B1630405
theorem B3615749 : Blo 634301 3615749 := bstep (se 4 (by rfl) ⟨338976, by rfl⟩ : syracuseStep 3615749 = 677953) B677953
theorem B2141261 : Blo 634301 2141261 := bstep (se 3 (by rfl) ⟨401486, by rfl⟩ : syracuseStep 2141261 = 802973) B802973
theorem B2141315 : Blo 634301 2141315 := bstep (se 1 (by rfl) ⟨1605986, by rfl⟩ : syracuseStep 2141315 = 3211973) B3211973
theorem B1354915 : Blo 634301 1354915 := bstep (se 1 (by rfl) ⟨1016186, by rfl⟩ : syracuseStep 1354915 = 2032373) B2032373
theorem B765139 : Blo 634301 765139 := bstep (se 1 (by rfl) ⟨573854, by rfl⟩ : syracuseStep 765139 = 1147709) B1147709
theorem B765235 : Blo 634301 765235 := bstep (se 1 (by rfl) ⟨573926, by rfl⟩ : syracuseStep 765235 = 1147853) B1147853
theorem B2141585 : Blo 634301 2141585 := bstep (se 2 (by rfl) ⟨803094, by rfl⟩ : syracuseStep 2141585 = 1606189) B1606189
theorem B634307 : Blo 634301 634307 := bstep (se 1 (by rfl) ⟨475730, by rfl⟩ : syracuseStep 634307 = 951461) B951461
theorem B765379 : Blo 634301 765379 := bstep (se 1 (by rfl) ⟨574034, by rfl⟩ : syracuseStep 765379 = 1148069) B1148069
theorem B3222989 : Blo 634301 3222989 := bstep (se 3 (by rfl) ⟨604310, by rfl⟩ : syracuseStep 3222989 = 1208621) B1208621
theorem B634323 : Blo 634301 634323 := bstep (se 1 (by rfl) ⟨475742, by rfl⟩ : syracuseStep 634323 = 951485) B951485
theorem B634339 : Blo 634301 634339 := bstep (se 1 (by rfl) ⟨475754, by rfl⟩ : syracuseStep 634339 = 951509) B951509
theorem B634355 : Blo 634301 634355 := bstep (se 1 (by rfl) ⟨475766, by rfl⟩ : syracuseStep 634355 = 951533) B951533
theorem B634371 : Blo 634301 634371 := bstep (se 1 (by rfl) ⟨475778, by rfl⟩ : syracuseStep 634371 = 951557) B951557
theorem B634387 : Blo 634301 634387 := bstep (se 1 (by rfl) ⟨475790, by rfl⟩ : syracuseStep 634387 = 951581) B951581
theorem B634403 : Blo 634301 634403 := bstep (se 1 (by rfl) ⟨475802, by rfl⟩ : syracuseStep 634403 = 951605) B951605
theorem B634419 : Blo 634301 634419 := bstep (se 1 (by rfl) ⟨475814, by rfl⟩ : syracuseStep 634419 = 951629) B951629
theorem B634435 : Blo 634301 634435 := bstep (se 1 (by rfl) ⟨475826, by rfl⟩ : syracuseStep 634435 = 951653) B951653
theorem B634451 : Blo 634301 634451 := bstep (se 1 (by rfl) ⟨475838, by rfl⟩ : syracuseStep 634451 = 951677) B951677
theorem B634467 : Blo 634301 634467 := bstep (se 1 (by rfl) ⟨475850, by rfl⟩ : syracuseStep 634467 = 951701) B951701
theorem B634483 : Blo 634301 634483 := bstep (se 1 (by rfl) ⟨475862, by rfl⟩ : syracuseStep 634483 = 951725) B951725
theorem B634499 : Blo 634301 634499 := bstep (se 1 (by rfl) ⟨475874, by rfl⟩ : syracuseStep 634499 = 951749) B951749
theorem B634515 : Blo 634301 634515 := bstep (se 1 (by rfl) ⟨475886, by rfl⟩ : syracuseStep 634515 = 951773) B951773
theorem B634531 : Blo 634301 634531 := bstep (se 1 (by rfl) ⟨475898, by rfl⟩ : syracuseStep 634531 = 951797) B951797
theorem B1289891 : Blo 634301 1289891 := bstep (se 1 (by rfl) ⟨967418, by rfl⟩ : syracuseStep 1289891 = 1934837) B1934837
theorem B3059363 : Blo 634301 3059363 := bstep (se 1 (by rfl) ⟨2294522, by rfl⟩ : syracuseStep 3059363 = 4589045) B4589045
theorem B3616433 : Blo 634301 3616433 := bstep (se 2 (by rfl) ⟨1356162, by rfl⟩ : syracuseStep 3616433 = 2712325) B2712325
theorem B634547 : Blo 634301 634547 := bstep (se 1 (by rfl) ⟨475910, by rfl⟩ : syracuseStep 634547 = 951821) B951821
theorem B634563 : Blo 634301 634563 := bstep (se 1 (by rfl) ⟨475922, by rfl⟩ : syracuseStep 634563 = 951845) B951845
theorem B634579 : Blo 634301 634579 := bstep (se 1 (by rfl) ⟨475934, by rfl⟩ : syracuseStep 634579 = 951869) B951869
theorem B1650403 : Blo 634301 1650403 := bstep (se 1 (by rfl) ⟨1237802, by rfl⟩ : syracuseStep 1650403 = 2475605) B2475605
theorem B634595 : Blo 634301 634595 := bstep (se 1 (by rfl) ⟨475946, by rfl⟩ : syracuseStep 634595 = 951893) B951893
theorem B634611 : Blo 634301 634611 := bstep (se 1 (by rfl) ⟨475958, by rfl⟩ : syracuseStep 634611 = 951917) B951917
theorem B634627 : Blo 634301 634627 := bstep (se 1 (by rfl) ⟨475970, by rfl⟩ : syracuseStep 634627 = 951941) B951941
theorem B634643 : Blo 634301 634643 := bstep (se 1 (by rfl) ⟨475982, by rfl⟩ : syracuseStep 634643 = 951965) B951965
theorem B634659 : Blo 634301 634659 := bstep (se 1 (by rfl) ⟨475994, by rfl⟩ : syracuseStep 634659 = 951989) B951989
theorem B634675 : Blo 634301 634675 := bstep (se 1 (by rfl) ⟨476006, by rfl⟩ : syracuseStep 634675 = 952013) B952013
theorem B634691 : Blo 634301 634691 := bstep (se 1 (by rfl) ⟨476018, by rfl⟩ : syracuseStep 634691 = 952037) B952037
theorem B634707 : Blo 634301 634707 := bstep (se 1 (by rfl) ⟨476030, by rfl⟩ : syracuseStep 634707 = 952061) B952061
theorem B634723 : Blo 634301 634723 := bstep (se 1 (by rfl) ⟨476042, by rfl⟩ : syracuseStep 634723 = 952085) B952085
theorem B1355633 : Blo 634301 1355633 := bstep (se 2 (by rfl) ⟨508362, by rfl⟩ : syracuseStep 1355633 = 1016725) B1016725
theorem B634739 : Blo 634301 634739 := bstep (se 1 (by rfl) ⟨476054, by rfl⟩ : syracuseStep 634739 = 952109) B952109
theorem B634755 : Blo 634301 634755 := bstep (se 1 (by rfl) ⟨476066, by rfl⟩ : syracuseStep 634755 = 952133) B952133
theorem B1814413 : Blo 634301 1814413 := bstep (se 3 (by rfl) ⟨340202, by rfl⟩ : syracuseStep 1814413 = 680405) B680405
theorem B634771 : Blo 634301 634771 := bstep (se 1 (by rfl) ⟨476078, by rfl⟩ : syracuseStep 634771 = 952157) B952157
theorem B634787 : Blo 634301 634787 := bstep (se 1 (by rfl) ⟨476090, by rfl⟩ : syracuseStep 634787 = 952181) B952181
theorem B2142125 : Blo 634301 2142125 := bstep (se 3 (by rfl) ⟨401648, by rfl⟩ : syracuseStep 2142125 = 803297) B803297
theorem B634803 : Blo 634301 634803 := bstep (se 1 (by rfl) ⟨476102, by rfl⟩ : syracuseStep 634803 = 952205) B952205
theorem B634819 : Blo 634301 634819 := bstep (se 1 (by rfl) ⟨476114, by rfl⟩ : syracuseStep 634819 = 952229) B952229
theorem B634835 : Blo 634301 634835 := bstep (se 1 (by rfl) ⟨476126, by rfl⟩ : syracuseStep 634835 = 952253) B952253
theorem B2142179 : Blo 634301 2142179 := bstep (se 1 (by rfl) ⟨1606634, by rfl⟩ : syracuseStep 2142179 = 3213269) B3213269
theorem B634851 : Blo 634301 634851 := bstep (se 1 (by rfl) ⟨476138, by rfl⟩ : syracuseStep 634851 = 952277) B952277
theorem B634867 : Blo 634301 634867 := bstep (se 1 (by rfl) ⟨476150, by rfl⟩ : syracuseStep 634867 = 952301) B952301
theorem B634883 : Blo 634301 634883 := bstep (se 1 (by rfl) ⟨476162, by rfl⟩ : syracuseStep 634883 = 952325) B952325
theorem B634899 : Blo 634301 634899 := bstep (se 1 (by rfl) ⟨476174, by rfl⟩ : syracuseStep 634899 = 952349) B952349
theorem B634915 : Blo 634301 634915 := bstep (se 1 (by rfl) ⟨476186, by rfl⟩ : syracuseStep 634915 = 952373) B952373
theorem B634931 : Blo 634301 634931 := bstep (se 1 (by rfl) ⟨476198, by rfl⟩ : syracuseStep 634931 = 952397) B952397
theorem B634947 : Blo 634301 634947 := bstep (se 1 (by rfl) ⟨476210, by rfl⟩ : syracuseStep 634947 = 952421) B952421
theorem B634963 : Blo 634301 634963 := bstep (se 1 (by rfl) ⟨476222, by rfl⟩ : syracuseStep 634963 = 952445) B952445
theorem B634979 : Blo 634301 634979 := bstep (se 1 (by rfl) ⟨476234, by rfl⟩ : syracuseStep 634979 = 952469) B952469
theorem B634995 : Blo 634301 634995 := bstep (se 1 (by rfl) ⟨476246, by rfl⟩ : syracuseStep 634995 = 952493) B952493
theorem B635011 : Blo 634301 635011 := bstep (se 1 (by rfl) ⟨476258, by rfl⟩ : syracuseStep 635011 = 952517) B952517
theorem B635027 : Blo 634301 635027 := bstep (se 1 (by rfl) ⟨476270, by rfl⟩ : syracuseStep 635027 = 952541) B952541
theorem B635043 : Blo 634301 635043 := bstep (se 1 (by rfl) ⟨476282, by rfl⟩ : syracuseStep 635043 = 952565) B952565
theorem B635059 : Blo 634301 635059 := bstep (se 1 (by rfl) ⟨476294, by rfl⟩ : syracuseStep 635059 = 952589) B952589
theorem B635075 : Blo 634301 635075 := bstep (se 1 (by rfl) ⟨476306, by rfl⟩ : syracuseStep 635075 = 952613) B952613
theorem B4829381 : Blo 634301 4829381 := bstep (se 4 (by rfl) ⟨452754, by rfl⟩ : syracuseStep 4829381 = 905509) B905509
theorem B635091 : Blo 634301 635091 := bstep (se 1 (by rfl) ⟨476318, by rfl⟩ : syracuseStep 635091 = 952637) B952637
theorem B635107 : Blo 634301 635107 := bstep (se 1 (by rfl) ⟨476330, by rfl⟩ : syracuseStep 635107 = 952661) B952661
theorem B2142449 : Blo 634301 2142449 := bstep (se 2 (by rfl) ⟨803418, by rfl⟩ : syracuseStep 2142449 = 1606837) B1606837
theorem B635123 : Blo 634301 635123 := bstep (se 1 (by rfl) ⟨476342, by rfl⟩ : syracuseStep 635123 = 952685) B952685
theorem B635139 : Blo 634301 635139 := bstep (se 1 (by rfl) ⟨476354, by rfl⟩ : syracuseStep 635139 = 952709) B952709
theorem B635155 : Blo 634301 635155 := bstep (se 1 (by rfl) ⟨476366, by rfl⟩ : syracuseStep 635155 = 952733) B952733
theorem B635171 : Blo 634301 635171 := bstep (se 1 (by rfl) ⟨476378, by rfl⟩ : syracuseStep 635171 = 952757) B952757
theorem B3060017 : Blo 634301 3060017 := bstep (se 2 (by rfl) ⟨1147506, by rfl⟩ : syracuseStep 3060017 = 2295013) B2295013
theorem B635187 : Blo 634301 635187 := bstep (se 1 (by rfl) ⟨476390, by rfl⟩ : syracuseStep 635187 = 952781) B952781
theorem B635203 : Blo 634301 635203 := bstep (se 1 (by rfl) ⟨476402, by rfl⟩ : syracuseStep 635203 = 952805) B952805
theorem B635219 : Blo 634301 635219 := bstep (se 1 (by rfl) ⟨476414, by rfl⟩ : syracuseStep 635219 = 952829) B952829
theorem B635235 : Blo 634301 635235 := bstep (se 1 (by rfl) ⟨476426, by rfl⟩ : syracuseStep 635235 = 952853) B952853
theorem B635251 : Blo 634301 635251 := bstep (se 1 (by rfl) ⟨476438, by rfl⟩ : syracuseStep 635251 = 952877) B952877
theorem B635267 : Blo 634301 635267 := bstep (se 1 (by rfl) ⟨476450, by rfl⟩ : syracuseStep 635267 = 952901) B952901
theorem B2044291 : Blo 634301 2044291 := bstep (se 1 (by rfl) ⟨1533218, by rfl⟩ : syracuseStep 2044291 = 3066437) B3066437
theorem B635283 : Blo 634301 635283 := bstep (se 1 (by rfl) ⟨476462, by rfl⟩ : syracuseStep 635283 = 952925) B952925
theorem B635299 : Blo 634301 635299 := bstep (se 1 (by rfl) ⟨476474, by rfl⟩ : syracuseStep 635299 = 952949) B952949
theorem B635315 : Blo 634301 635315 := bstep (se 1 (by rfl) ⟨476486, by rfl⟩ : syracuseStep 635315 = 952973) B952973
theorem B635331 : Blo 634301 635331 := bstep (se 1 (by rfl) ⟨476498, by rfl⟩ : syracuseStep 635331 = 952997) B952997
theorem B635347 : Blo 634301 635347 := bstep (se 1 (by rfl) ⟨476510, by rfl⟩ : syracuseStep 635347 = 953021) B953021
theorem B635363 : Blo 634301 635363 := bstep (se 1 (by rfl) ⟨476522, by rfl⟩ : syracuseStep 635363 = 953045) B953045
theorem B635379 : Blo 634301 635379 := bstep (se 1 (by rfl) ⟨476534, by rfl⟩ : syracuseStep 635379 = 953069) B953069
theorem B635395 : Blo 634301 635395 := bstep (se 1 (by rfl) ⟨476546, by rfl⟩ : syracuseStep 635395 = 953093) B953093
theorem B635411 : Blo 634301 635411 := bstep (se 1 (by rfl) ⟨476558, by rfl⟩ : syracuseStep 635411 = 953117) B953117
theorem B635427 : Blo 634301 635427 := bstep (se 1 (by rfl) ⟨476570, by rfl⟩ : syracuseStep 635427 = 953141) B953141
theorem B635443 : Blo 634301 635443 := bstep (se 1 (by rfl) ⟨476582, by rfl⟩ : syracuseStep 635443 = 953165) B953165
theorem B635459 : Blo 634301 635459 := bstep (se 1 (by rfl) ⟨476594, by rfl⟩ : syracuseStep 635459 = 953189) B953189
theorem B635475 : Blo 634301 635475 := bstep (se 1 (by rfl) ⟨476606, by rfl⟩ : syracuseStep 635475 = 953213) B953213
theorem B635491 : Blo 634301 635491 := bstep (se 1 (by rfl) ⟨476618, by rfl⟩ : syracuseStep 635491 = 953237) B953237
theorem B635507 : Blo 634301 635507 := bstep (se 1 (by rfl) ⟨476630, by rfl⟩ : syracuseStep 635507 = 953261) B953261
theorem B1356419 : Blo 634301 1356419 := bstep (se 1 (by rfl) ⟨1017314, by rfl⟩ : syracuseStep 1356419 = 2034629) B2034629
theorem B635523 : Blo 634301 635523 := bstep (se 1 (by rfl) ⟨476642, by rfl⟩ : syracuseStep 635523 = 953285) B953285
theorem B766595 : Blo 634301 766595 := bstep (se 1 (by rfl) ⟨574946, by rfl⟩ : syracuseStep 766595 = 1149893) B1149893
theorem B2044561 : Blo 634301 2044561 := bstep (se 2 (by rfl) ⟨766710, by rfl⟩ : syracuseStep 2044561 = 1533421) B1533421
theorem B635539 : Blo 634301 635539 := bstep (se 1 (by rfl) ⟨476654, by rfl⟩ : syracuseStep 635539 = 953309) B953309
theorem B635555 : Blo 634301 635555 := bstep (se 1 (by rfl) ⟨476666, by rfl⟩ : syracuseStep 635555 = 953333) B953333
theorem B635571 : Blo 634301 635571 := bstep (se 1 (by rfl) ⟨476678, by rfl⟩ : syracuseStep 635571 = 953357) B953357
theorem B635587 : Blo 634301 635587 := bstep (se 1 (by rfl) ⟨476690, by rfl⟩ : syracuseStep 635587 = 953381) B953381
theorem B6861509 : Blo 634301 6861509 := bstep (se 4 (by rfl) ⟨643266, by rfl⟩ : syracuseStep 6861509 = 1286533) B1286533
theorem B635603 : Blo 634301 635603 := bstep (se 1 (by rfl) ⟨476702, by rfl⟩ : syracuseStep 635603 = 953405) B953405
theorem B635619 : Blo 634301 635619 := bstep (se 1 (by rfl) ⟨476714, by rfl⟩ : syracuseStep 635619 = 953429) B953429
theorem B635635 : Blo 634301 635635 := bstep (se 1 (by rfl) ⟨476726, by rfl⟩ : syracuseStep 635635 = 953453) B953453
theorem B635651 : Blo 634301 635651 := bstep (se 1 (by rfl) ⟨476738, by rfl⟩ : syracuseStep 635651 = 953477) B953477
theorem B2142989 : Blo 634301 2142989 := bstep (se 3 (by rfl) ⟨401810, by rfl⟩ : syracuseStep 2142989 = 803621) B803621
theorem B635667 : Blo 634301 635667 := bstep (se 1 (by rfl) ⟨476750, by rfl⟩ : syracuseStep 635667 = 953501) B953501
theorem B635683 : Blo 634301 635683 := bstep (se 1 (by rfl) ⟨476762, by rfl⟩ : syracuseStep 635683 = 953525) B953525
theorem B635699 : Blo 634301 635699 := bstep (se 1 (by rfl) ⟨476774, by rfl⟩ : syracuseStep 635699 = 953549) B953549
theorem B2143043 : Blo 634301 2143043 := bstep (se 1 (by rfl) ⟨1607282, by rfl⟩ : syracuseStep 2143043 = 3214565) B3214565
theorem B635715 : Blo 634301 635715 := bstep (se 1 (by rfl) ⟨476786, by rfl⟩ : syracuseStep 635715 = 953573) B953573
theorem B635731 : Blo 634301 635731 := bstep (se 1 (by rfl) ⟨476798, by rfl⟩ : syracuseStep 635731 = 953597) B953597
theorem B635747 : Blo 634301 635747 := bstep (se 1 (by rfl) ⟨476810, by rfl⟩ : syracuseStep 635747 = 953621) B953621
theorem B635763 : Blo 634301 635763 := bstep (se 1 (by rfl) ⟨476822, by rfl⟩ : syracuseStep 635763 = 953645) B953645
theorem B635779 : Blo 634301 635779 := bstep (se 1 (by rfl) ⟨476834, by rfl⟩ : syracuseStep 635779 = 953669) B953669
theorem B635795 : Blo 634301 635795 := bstep (se 1 (by rfl) ⟨476846, by rfl⟩ : syracuseStep 635795 = 953693) B953693
theorem B635811 : Blo 634301 635811 := bstep (se 1 (by rfl) ⟨476858, by rfl⟩ : syracuseStep 635811 = 953717) B953717
theorem B1815473 : Blo 634301 1815473 := bstep (se 2 (by rfl) ⟨680802, by rfl⟩ : syracuseStep 1815473 = 1361605) B1361605
theorem B635827 : Blo 634301 635827 := bstep (se 1 (by rfl) ⟨476870, by rfl⟩ : syracuseStep 635827 = 953741) B953741
theorem B7943093 : Blo 634301 7943093 := bstep (se 5 (by rfl) ⟨372332, by rfl⟩ : syracuseStep 7943093 = 744665) B744665
theorem B635843 : Blo 634301 635843 := bstep (se 1 (by rfl) ⟨476882, by rfl⟩ : syracuseStep 635843 = 953765) B953765
theorem B635859 : Blo 634301 635859 := bstep (se 1 (by rfl) ⟨476894, by rfl⟩ : syracuseStep 635859 = 953789) B953789
theorem B635875 : Blo 634301 635875 := bstep (se 1 (by rfl) ⟨476906, by rfl⟩ : syracuseStep 635875 = 953813) B953813
theorem B635891 : Blo 634301 635891 := bstep (se 1 (by rfl) ⟨476918, by rfl⟩ : syracuseStep 635891 = 953837) B953837
theorem B635907 : Blo 634301 635907 := bstep (se 1 (by rfl) ⟨476930, by rfl⟩ : syracuseStep 635907 = 953861) B953861
theorem B635923 : Blo 634301 635923 := bstep (se 1 (by rfl) ⟨476942, by rfl⟩ : syracuseStep 635923 = 953885) B953885
theorem B635939 : Blo 634301 635939 := bstep (se 1 (by rfl) ⟨476954, by rfl⟩ : syracuseStep 635939 = 953909) B953909
theorem B635955 : Blo 634301 635955 := bstep (se 1 (by rfl) ⟨476966, by rfl⟩ : syracuseStep 635955 = 953933) B953933
theorem B635971 : Blo 634301 635971 := bstep (se 1 (by rfl) ⟨476978, by rfl⟩ : syracuseStep 635971 = 953957) B953957
theorem B2143313 : Blo 634301 2143313 := bstep (se 2 (by rfl) ⟨803742, by rfl⟩ : syracuseStep 2143313 = 1607485) B1607485
theorem B635987 : Blo 634301 635987 := bstep (se 1 (by rfl) ⟨476990, by rfl⟩ : syracuseStep 635987 = 953981) B953981
theorem B3617891 : Blo 634301 3617891 := bstep (se 1 (by rfl) ⟨2713418, by rfl⟩ : syracuseStep 3617891 = 5426837) B5426837
theorem B636003 : Blo 634301 636003 := bstep (se 1 (by rfl) ⟨477002, by rfl⟩ : syracuseStep 636003 = 954005) B954005
theorem B636019 : Blo 634301 636019 := bstep (se 1 (by rfl) ⟨477014, by rfl⟩ : syracuseStep 636019 = 954029) B954029
theorem B636035 : Blo 634301 636035 := bstep (se 1 (by rfl) ⟨477026, by rfl⟩ : syracuseStep 636035 = 954053) B954053
theorem B636051 : Blo 634301 636051 := bstep (se 1 (by rfl) ⟨477038, by rfl⟩ : syracuseStep 636051 = 954077) B954077
theorem B636067 : Blo 634301 636067 := bstep (se 1 (by rfl) ⟨477050, by rfl⟩ : syracuseStep 636067 = 954101) B954101
theorem B636083 : Blo 634301 636083 := bstep (se 1 (by rfl) ⟨477062, by rfl⟩ : syracuseStep 636083 = 954125) B954125
theorem B636099 : Blo 634301 636099 := bstep (se 1 (by rfl) ⟨477074, by rfl⟩ : syracuseStep 636099 = 954149) B954149
theorem B3880133 : Blo 634301 3880133 := bstep (se 4 (by rfl) ⟨363762, by rfl⟩ : syracuseStep 3880133 = 727525) B727525
theorem B1717453 : Blo 634301 1717453 := bstep (se 3 (by rfl) ⟨322022, by rfl⟩ : syracuseStep 1717453 = 644045) B644045
theorem B636115 : Blo 634301 636115 := bstep (se 1 (by rfl) ⟨477086, by rfl⟩ : syracuseStep 636115 = 954173) B954173
theorem B636131 : Blo 634301 636131 := bstep (se 1 (by rfl) ⟨477098, by rfl⟩ : syracuseStep 636131 = 954197) B954197
theorem B9188579 : Blo 634301 9188579 := bstep (se 1 (by rfl) ⟨6891434, by rfl⟩ : syracuseStep 9188579 = 13782869) B13782869
theorem B636147 : Blo 634301 636147 := bstep (se 1 (by rfl) ⟨477110, by rfl⟩ : syracuseStep 636147 = 954221) B954221
theorem B636163 : Blo 634301 636163 := bstep (se 1 (by rfl) ⟨477122, by rfl⟩ : syracuseStep 636163 = 954245) B954245
theorem B636179 : Blo 634301 636179 := bstep (se 1 (by rfl) ⟨477134, by rfl⟩ : syracuseStep 636179 = 954269) B954269
theorem B636195 : Blo 634301 636195 := bstep (se 1 (by rfl) ⟨477146, by rfl⟩ : syracuseStep 636195 = 954293) B954293
theorem B636211 : Blo 634301 636211 := bstep (se 1 (by rfl) ⟨477158, by rfl⟩ : syracuseStep 636211 = 954317) B954317
theorem B636227 : Blo 634301 636227 := bstep (se 1 (by rfl) ⟨477170, by rfl⟩ : syracuseStep 636227 = 954341) B954341
theorem B636243 : Blo 634301 636243 := bstep (se 1 (by rfl) ⟨477182, by rfl⟩ : syracuseStep 636243 = 954365) B954365
theorem B636259 : Blo 634301 636259 := bstep (se 1 (by rfl) ⟨477194, by rfl⟩ : syracuseStep 636259 = 954389) B954389
theorem B636275 : Blo 634301 636275 := bstep (se 1 (by rfl) ⟨477206, by rfl⟩ : syracuseStep 636275 = 954413) B954413
theorem B636291 : Blo 634301 636291 := bstep (se 1 (by rfl) ⟨477218, by rfl⟩ : syracuseStep 636291 = 954437) B954437
theorem B636307 : Blo 634301 636307 := bstep (se 1 (by rfl) ⟨477230, by rfl⟩ : syracuseStep 636307 = 954461) B954461
theorem B636323 : Blo 634301 636323 := bstep (se 1 (by rfl) ⟨477242, by rfl⟩ : syracuseStep 636323 = 954485) B954485
theorem B636339 : Blo 634301 636339 := bstep (se 1 (by rfl) ⟨477254, by rfl⟩ : syracuseStep 636339 = 954509) B954509
theorem B636355 : Blo 634301 636355 := bstep (se 1 (by rfl) ⟨477266, by rfl⟩ : syracuseStep 636355 = 954533) B954533
theorem B636371 : Blo 634301 636371 := bstep (se 1 (by rfl) ⟨477278, by rfl⟩ : syracuseStep 636371 = 954557) B954557
theorem B636387 : Blo 634301 636387 := bstep (se 1 (by rfl) ⟨477290, by rfl⟩ : syracuseStep 636387 = 954581) B954581
theorem B636403 : Blo 634301 636403 := bstep (se 1 (by rfl) ⟨477302, by rfl⟩ : syracuseStep 636403 = 954605) B954605
theorem B636419 : Blo 634301 636419 := bstep (se 1 (by rfl) ⟨477314, by rfl⟩ : syracuseStep 636419 = 954629) B954629
theorem B636435 : Blo 634301 636435 := bstep (se 1 (by rfl) ⟨477326, by rfl⟩ : syracuseStep 636435 = 954653) B954653
theorem B636451 : Blo 634301 636451 := bstep (se 1 (by rfl) ⟨477338, by rfl⟩ : syracuseStep 636451 = 954677) B954677
theorem B636467 : Blo 634301 636467 := bstep (se 1 (by rfl) ⟨477350, by rfl⟩ : syracuseStep 636467 = 954701) B954701
theorem B636483 : Blo 634301 636483 := bstep (se 1 (by rfl) ⟨477362, by rfl⟩ : syracuseStep 636483 = 954725) B954725
theorem B1357393 : Blo 634301 1357393 := bstep (se 2 (by rfl) ⟨509022, by rfl⟩ : syracuseStep 1357393 = 1018045) B1018045
theorem B1816145 : Blo 634301 1816145 := bstep (se 2 (by rfl) ⟨681054, by rfl⟩ : syracuseStep 1816145 = 1362109) B1362109
theorem B636499 : Blo 634301 636499 := bstep (se 1 (by rfl) ⟨477374, by rfl⟩ : syracuseStep 636499 = 954749) B954749
theorem B636515 : Blo 634301 636515 := bstep (se 1 (by rfl) ⟨477386, by rfl⟩ : syracuseStep 636515 = 954773) B954773
theorem B2143853 : Blo 634301 2143853 := bstep (se 3 (by rfl) ⟨401972, by rfl⟩ : syracuseStep 2143853 = 803945) B803945
theorem B636531 : Blo 634301 636531 := bstep (se 1 (by rfl) ⟨477398, by rfl⟩ : syracuseStep 636531 = 954797) B954797
theorem B636547 : Blo 634301 636547 := bstep (se 1 (by rfl) ⟨477410, by rfl⟩ : syracuseStep 636547 = 954821) B954821
theorem B636563 : Blo 634301 636563 := bstep (se 1 (by rfl) ⟨477422, by rfl⟩ : syracuseStep 636563 = 954845) B954845
theorem B2143907 : Blo 634301 2143907 := bstep (se 1 (by rfl) ⟨1607930, by rfl⟩ : syracuseStep 2143907 = 3215861) B3215861
theorem B636579 : Blo 634301 636579 := bstep (se 1 (by rfl) ⟨477434, by rfl⟩ : syracuseStep 636579 = 954869) B954869
theorem B636595 : Blo 634301 636595 := bstep (se 1 (by rfl) ⟨477446, by rfl⟩ : syracuseStep 636595 = 954893) B954893
theorem B636611 : Blo 634301 636611 := bstep (se 1 (by rfl) ⟨477458, by rfl⟩ : syracuseStep 636611 = 954917) B954917
theorem B636627 : Blo 634301 636627 := bstep (se 1 (by rfl) ⟨477470, by rfl⟩ : syracuseStep 636627 = 954941) B954941
theorem B636643 : Blo 634301 636643 := bstep (se 1 (by rfl) ⟨477482, by rfl⟩ : syracuseStep 636643 = 954965) B954965
theorem B636659 : Blo 634301 636659 := bstep (se 1 (by rfl) ⟨477494, by rfl⟩ : syracuseStep 636659 = 954989) B954989
theorem B636675 : Blo 634301 636675 := bstep (se 1 (by rfl) ⟨477506, by rfl⟩ : syracuseStep 636675 = 955013) B955013
theorem B636691 : Blo 634301 636691 := bstep (se 1 (by rfl) ⟨477518, by rfl⟩ : syracuseStep 636691 = 955037) B955037
theorem B636707 : Blo 634301 636707 := bstep (se 1 (by rfl) ⟨477530, by rfl⟩ : syracuseStep 636707 = 955061) B955061
theorem B636723 : Blo 634301 636723 := bstep (se 1 (by rfl) ⟨477542, by rfl⟩ : syracuseStep 636723 = 955085) B955085
theorem B636739 : Blo 634301 636739 := bstep (se 1 (by rfl) ⟨477554, by rfl⟩ : syracuseStep 636739 = 955109) B955109
theorem B1357649 : Blo 634301 1357649 := bstep (se 2 (by rfl) ⟨509118, by rfl⟩ : syracuseStep 1357649 = 1018237) B1018237
theorem B636755 : Blo 634301 636755 := bstep (se 1 (by rfl) ⟨477566, by rfl⟩ : syracuseStep 636755 = 955133) B955133
theorem B636771 : Blo 634301 636771 := bstep (se 1 (by rfl) ⟨477578, by rfl⟩ : syracuseStep 636771 = 955157) B955157
theorem B636787 : Blo 634301 636787 := bstep (se 1 (by rfl) ⟨477590, by rfl⟩ : syracuseStep 636787 = 955181) B955181
theorem B636803 : Blo 634301 636803 := bstep (se 1 (by rfl) ⟨477602, by rfl⟩ : syracuseStep 636803 = 955205) B955205
theorem B636819 : Blo 634301 636819 := bstep (se 1 (by rfl) ⟨477614, by rfl⟩ : syracuseStep 636819 = 955229) B955229
theorem B636835 : Blo 634301 636835 := bstep (se 1 (by rfl) ⟨477626, by rfl⟩ : syracuseStep 636835 = 955253) B955253
theorem B2144177 : Blo 634301 2144177 := bstep (se 2 (by rfl) ⟨804066, by rfl⟩ : syracuseStep 2144177 = 1608133) B1608133
theorem B636851 : Blo 634301 636851 := bstep (se 1 (by rfl) ⟨477638, by rfl⟩ : syracuseStep 636851 = 955277) B955277
theorem B636867 : Blo 634301 636867 := bstep (se 1 (by rfl) ⟨477650, by rfl⟩ : syracuseStep 636867 = 955301) B955301
theorem B3061709 : Blo 634301 3061709 := bstep (se 3 (by rfl) ⟨574070, by rfl⟩ : syracuseStep 3061709 = 1148141) B1148141
theorem B3880909 : Blo 634301 3880909 := bstep (se 3 (by rfl) ⟨727670, by rfl⟩ : syracuseStep 3880909 = 1455341) B1455341
theorem B636883 : Blo 634301 636883 := bstep (se 1 (by rfl) ⟨477662, by rfl⟩ : syracuseStep 636883 = 955325) B955325
theorem B636899 : Blo 634301 636899 := bstep (se 1 (by rfl) ⟨477674, by rfl⟩ : syracuseStep 636899 = 955349) B955349
theorem B636915 : Blo 634301 636915 := bstep (se 1 (by rfl) ⟨477686, by rfl⟩ : syracuseStep 636915 = 955373) B955373
theorem B636931 : Blo 634301 636931 := bstep (se 1 (by rfl) ⟨477698, by rfl⟩ : syracuseStep 636931 = 955397) B955397
theorem B636947 : Blo 634301 636947 := bstep (se 1 (by rfl) ⟨477710, by rfl⟩ : syracuseStep 636947 = 955421) B955421
theorem B636963 : Blo 634301 636963 := bstep (se 1 (by rfl) ⟨477722, by rfl⟩ : syracuseStep 636963 = 955445) B955445
theorem B636979 : Blo 634301 636979 := bstep (se 1 (by rfl) ⟨477734, by rfl⟩ : syracuseStep 636979 = 955469) B955469
theorem B636995 : Blo 634301 636995 := bstep (se 1 (by rfl) ⟨477746, by rfl⟩ : syracuseStep 636995 = 955493) B955493
theorem B637011 : Blo 634301 637011 := bstep (se 1 (by rfl) ⟨477758, by rfl⟩ : syracuseStep 637011 = 955517) B955517
theorem B637027 : Blo 634301 637027 := bstep (se 1 (by rfl) ⟨477770, by rfl⟩ : syracuseStep 637027 = 955541) B955541
theorem B637043 : Blo 634301 637043 := bstep (se 1 (by rfl) ⟨477782, by rfl⟩ : syracuseStep 637043 = 955565) B955565
theorem B637059 : Blo 634301 637059 := bstep (se 1 (by rfl) ⟨477794, by rfl⟩ : syracuseStep 637059 = 955589) B955589
theorem B637075 : Blo 634301 637075 := bstep (se 1 (by rfl) ⟨477806, by rfl⟩ : syracuseStep 637075 = 955613) B955613
theorem B637091 : Blo 634301 637091 := bstep (se 1 (by rfl) ⟨477818, by rfl⟩ : syracuseStep 637091 = 955637) B955637
theorem B3061937 : Blo 634301 3061937 := bstep (se 2 (by rfl) ⟨1148226, by rfl⟩ : syracuseStep 3061937 = 2296453) B2296453
theorem B637107 : Blo 634301 637107 := bstep (se 1 (by rfl) ⟨477830, by rfl⟩ : syracuseStep 637107 = 955661) B955661
theorem B637123 : Blo 634301 637123 := bstep (se 1 (by rfl) ⟨477842, by rfl⟩ : syracuseStep 637123 = 955685) B955685
theorem B637139 : Blo 634301 637139 := bstep (se 1 (by rfl) ⟨477854, by rfl⟩ : syracuseStep 637139 = 955709) B955709
theorem B7747811 : Blo 634301 7747811 := bstep (se 1 (by rfl) ⟨5810858, by rfl⟩ : syracuseStep 7747811 = 11621717) B11621717
theorem B637155 : Blo 634301 637155 := bstep (se 1 (by rfl) ⟨477866, by rfl⟩ : syracuseStep 637155 = 955733) B955733
theorem B637171 : Blo 634301 637171 := bstep (se 1 (by rfl) ⟨477878, by rfl⟩ : syracuseStep 637171 = 955757) B955757
theorem B637187 : Blo 634301 637187 := bstep (se 1 (by rfl) ⟨477890, by rfl⟩ : syracuseStep 637187 = 955781) B955781
theorem B637203 : Blo 634301 637203 := bstep (se 1 (by rfl) ⟨477902, by rfl⟩ : syracuseStep 637203 = 955805) B955805
theorem B637219 : Blo 634301 637219 := bstep (se 1 (by rfl) ⟨477914, by rfl⟩ : syracuseStep 637219 = 955829) B955829
theorem B3225905 : Blo 634301 3225905 := bstep (se 2 (by rfl) ⟨1209714, by rfl⟩ : syracuseStep 3225905 = 2419429) B2419429
theorem B637235 : Blo 634301 637235 := bstep (se 1 (by rfl) ⟨477926, by rfl⟩ : syracuseStep 637235 = 955853) B955853
theorem B637251 : Blo 634301 637251 := bstep (se 1 (by rfl) ⟨477938, by rfl⟩ : syracuseStep 637251 = 955877) B955877
theorem B637267 : Blo 634301 637267 := bstep (se 1 (by rfl) ⟨477950, by rfl⟩ : syracuseStep 637267 = 955901) B955901
theorem B637283 : Blo 634301 637283 := bstep (se 1 (by rfl) ⟨477962, by rfl⟩ : syracuseStep 637283 = 955925) B955925
theorem B1816931 : Blo 634301 1816931 := bstep (se 1 (by rfl) ⟨1362698, by rfl⟩ : syracuseStep 1816931 = 2725397) B2725397
theorem B637299 : Blo 634301 637299 := bstep (se 1 (by rfl) ⟨477974, by rfl⟩ : syracuseStep 637299 = 955949) B955949
theorem B637315 : Blo 634301 637315 := bstep (se 1 (by rfl) ⟨477986, by rfl⟩ : syracuseStep 637315 = 955973) B955973
theorem B637331 : Blo 634301 637331 := bstep (se 1 (by rfl) ⟨477998, by rfl⟩ : syracuseStep 637331 = 955997) B955997
theorem B637347 : Blo 634301 637347 := bstep (se 1 (by rfl) ⟨478010, by rfl⟩ : syracuseStep 637347 = 956021) B956021
theorem B637363 : Blo 634301 637363 := bstep (se 1 (by rfl) ⟨478022, by rfl⟩ : syracuseStep 637363 = 956045) B956045
theorem B637379 : Blo 634301 637379 := bstep (se 1 (by rfl) ⟨478034, by rfl⟩ : syracuseStep 637379 = 956069) B956069
theorem B2144717 : Blo 634301 2144717 := bstep (se 3 (by rfl) ⟨402134, by rfl⟩ : syracuseStep 2144717 = 804269) B804269
theorem B637395 : Blo 634301 637395 := bstep (se 1 (by rfl) ⟨478046, by rfl⟩ : syracuseStep 637395 = 956093) B956093
theorem B637411 : Blo 634301 637411 := bstep (se 1 (by rfl) ⟨478058, by rfl⟩ : syracuseStep 637411 = 956117) B956117
theorem B637427 : Blo 634301 637427 := bstep (se 1 (by rfl) ⟨478070, by rfl⟩ : syracuseStep 637427 = 956141) B956141
theorem B2144771 : Blo 634301 2144771 := bstep (se 1 (by rfl) ⟨1608578, by rfl⟩ : syracuseStep 2144771 = 3217157) B3217157
theorem B637443 : Blo 634301 637443 := bstep (se 1 (by rfl) ⟨478082, by rfl⟩ : syracuseStep 637443 = 956165) B956165
theorem B1161745 : Blo 634301 1161745 := bstep (se 2 (by rfl) ⟨435654, by rfl⟩ : syracuseStep 1161745 = 871309) B871309
theorem B637459 : Blo 634301 637459 := bstep (se 1 (by rfl) ⟨478094, by rfl⟩ : syracuseStep 637459 = 956189) B956189
theorem B637475 : Blo 634301 637475 := bstep (se 1 (by rfl) ⟨478106, by rfl⟩ : syracuseStep 637475 = 956213) B956213
theorem B637491 : Blo 634301 637491 := bstep (se 1 (by rfl) ⟨478118, by rfl⟩ : syracuseStep 637491 = 956237) B956237
theorem B637507 : Blo 634301 637507 := bstep (se 1 (by rfl) ⟨478130, by rfl⟩ : syracuseStep 637507 = 956261) B956261
theorem B8141381 : Blo 634301 8141381 := bstep (se 4 (by rfl) ⟨763254, by rfl⟩ : syracuseStep 8141381 = 1526509) B1526509
theorem B637523 : Blo 634301 637523 := bstep (se 1 (by rfl) ⟨478142, by rfl⟩ : syracuseStep 637523 = 956285) B956285
theorem B637539 : Blo 634301 637539 := bstep (se 1 (by rfl) ⟨478154, by rfl⟩ : syracuseStep 637539 = 956309) B956309
theorem B637555 : Blo 634301 637555 := bstep (se 1 (by rfl) ⟨478166, by rfl⟩ : syracuseStep 637555 = 956333) B956333
theorem B637571 : Blo 634301 637571 := bstep (se 1 (by rfl) ⟨478178, by rfl⟩ : syracuseStep 637571 = 956357) B956357
theorem B637587 : Blo 634301 637587 := bstep (se 1 (by rfl) ⟨478190, by rfl⟩ : syracuseStep 637587 = 956381) B956381
theorem B637603 : Blo 634301 637603 := bstep (se 1 (by rfl) ⟨478202, by rfl⟩ : syracuseStep 637603 = 956405) B956405
theorem B1718957 : Blo 634301 1718957 := bstep (se 3 (by rfl) ⟨322304, by rfl⟩ : syracuseStep 1718957 = 644609) B644609
theorem B1817261 : Blo 634301 1817261 := bstep (se 3 (by rfl) ⟨340736, by rfl⟩ : syracuseStep 1817261 = 681473) B681473
theorem B637619 : Blo 634301 637619 := bstep (se 1 (by rfl) ⟨478214, by rfl⟩ : syracuseStep 637619 = 956429) B956429
theorem B637635 : Blo 634301 637635 := bstep (se 1 (by rfl) ⟨478226, by rfl⟩ : syracuseStep 637635 = 956453) B956453
theorem B637651 : Blo 634301 637651 := bstep (se 1 (by rfl) ⟨478238, by rfl⟩ : syracuseStep 637651 = 956477) B956477
theorem B637667 : Blo 634301 637667 := bstep (se 1 (by rfl) ⟨478250, by rfl⟩ : syracuseStep 637667 = 956501) B956501
theorem B1817329 : Blo 634301 1817329 := bstep (se 2 (by rfl) ⟨681498, by rfl⟩ : syracuseStep 1817329 = 1362997) B1362997
theorem B637683 : Blo 634301 637683 := bstep (se 1 (by rfl) ⟨478262, by rfl⟩ : syracuseStep 637683 = 956525) B956525
theorem B637699 : Blo 634301 637699 := bstep (se 1 (by rfl) ⟨478274, by rfl⟩ : syracuseStep 637699 = 956549) B956549
theorem B2145041 : Blo 634301 2145041 := bstep (se 2 (by rfl) ⟨804390, by rfl⟩ : syracuseStep 2145041 = 1608781) B1608781
theorem B637715 : Blo 634301 637715 := bstep (se 1 (by rfl) ⟨478286, by rfl⟩ : syracuseStep 637715 = 956573) B956573
theorem B637731 : Blo 634301 637731 := bstep (se 1 (by rfl) ⟨478298, by rfl⟩ : syracuseStep 637731 = 956597) B956597
theorem B637747 : Blo 634301 637747 := bstep (se 1 (by rfl) ⟨478310, by rfl⟩ : syracuseStep 637747 = 956621) B956621
theorem B637763 : Blo 634301 637763 := bstep (se 1 (by rfl) ⟨478322, by rfl⟩ : syracuseStep 637763 = 956645) B956645
theorem B637779 : Blo 634301 637779 := bstep (se 1 (by rfl) ⟨478334, by rfl⟩ : syracuseStep 637779 = 956669) B956669
theorem B637795 : Blo 634301 637795 := bstep (se 1 (by rfl) ⟨478346, by rfl⟩ : syracuseStep 637795 = 956693) B956693
theorem B637811 : Blo 634301 637811 := bstep (se 1 (by rfl) ⟨478358, by rfl⟩ : syracuseStep 637811 = 956717) B956717
theorem B637827 : Blo 634301 637827 := bstep (se 1 (by rfl) ⟨478370, by rfl⟩ : syracuseStep 637827 = 956741) B956741
theorem B637843 : Blo 634301 637843 := bstep (se 1 (by rfl) ⟨478382, by rfl⟩ : syracuseStep 637843 = 956765) B956765
theorem B637859 : Blo 634301 637859 := bstep (se 1 (by rfl) ⟨478394, by rfl⟩ : syracuseStep 637859 = 956789) B956789
theorem B637875 : Blo 634301 637875 := bstep (se 1 (by rfl) ⟨478406, by rfl⟩ : syracuseStep 637875 = 956813) B956813
theorem B637891 : Blo 634301 637891 := bstep (se 1 (by rfl) ⟨478418, by rfl⟩ : syracuseStep 637891 = 956837) B956837
theorem B637907 : Blo 634301 637907 := bstep (se 1 (by rfl) ⟨478430, by rfl⟩ : syracuseStep 637907 = 956861) B956861
theorem B637923 : Blo 634301 637923 := bstep (se 1 (by rfl) ⟨478442, by rfl⟩ : syracuseStep 637923 = 956885) B956885
theorem B637939 : Blo 634301 637939 := bstep (se 1 (by rfl) ⟨478454, by rfl⟩ : syracuseStep 637939 = 956909) B956909
theorem B637955 : Blo 634301 637955 := bstep (se 1 (by rfl) ⟨478466, by rfl⟩ : syracuseStep 637955 = 956933) B956933
theorem B1817603 : Blo 634301 1817603 := bstep (se 1 (by rfl) ⟨1363202, by rfl⟩ : syracuseStep 1817603 = 2726405) B2726405
theorem B637971 : Blo 634301 637971 := bstep (se 1 (by rfl) ⟨478478, by rfl⟩ : syracuseStep 637971 = 956957) B956957
theorem B637987 : Blo 634301 637987 := bstep (se 1 (by rfl) ⟨478490, by rfl⟩ : syracuseStep 637987 = 956981) B956981
theorem B638003 : Blo 634301 638003 := bstep (se 1 (by rfl) ⟨478502, by rfl⟩ : syracuseStep 638003 = 957005) B957005
theorem B638019 : Blo 634301 638019 := bstep (se 1 (by rfl) ⟨478514, by rfl⟩ : syracuseStep 638019 = 957029) B957029
theorem B638035 : Blo 634301 638035 := bstep (se 1 (by rfl) ⟨478526, by rfl⟩ : syracuseStep 638035 = 957053) B957053
theorem B1358947 : Blo 634301 1358947 := bstep (se 1 (by rfl) ⟨1019210, by rfl⟩ : syracuseStep 1358947 = 2038421) B2038421
theorem B932963 : Blo 634301 932963 := bstep (se 1 (by rfl) ⟨699722, by rfl⟩ : syracuseStep 932963 = 1399445) B1399445
theorem B638051 : Blo 634301 638051 := bstep (se 1 (by rfl) ⟨478538, by rfl⟩ : syracuseStep 638051 = 957077) B957077
theorem B638067 : Blo 634301 638067 := bstep (se 1 (by rfl) ⟨478550, by rfl⟩ : syracuseStep 638067 = 957101) B957101
theorem B638083 : Blo 634301 638083 := bstep (se 1 (by rfl) ⟨478562, by rfl⟩ : syracuseStep 638083 = 957125) B957125
theorem B638099 : Blo 634301 638099 := bstep (se 1 (by rfl) ⟨478574, by rfl⟩ : syracuseStep 638099 = 957149) B957149
theorem B638115 : Blo 634301 638115 := bstep (se 1 (by rfl) ⟨478586, by rfl⟩ : syracuseStep 638115 = 957173) B957173
theorem B638131 : Blo 634301 638131 := bstep (se 1 (by rfl) ⟨478598, by rfl⟩ : syracuseStep 638131 = 957197) B957197
theorem B638147 : Blo 634301 638147 := bstep (se 1 (by rfl) ⟨478610, by rfl⟩ : syracuseStep 638147 = 957221) B957221
theorem B638163 : Blo 634301 638163 := bstep (se 1 (by rfl) ⟨478622, by rfl⟩ : syracuseStep 638163 = 957245) B957245
theorem B638179 : Blo 634301 638179 := bstep (se 1 (by rfl) ⟨478634, by rfl⟩ : syracuseStep 638179 = 957269) B957269
theorem B638195 : Blo 634301 638195 := bstep (se 1 (by rfl) ⟨478646, by rfl⟩ : syracuseStep 638195 = 957293) B957293
theorem B638211 : Blo 634301 638211 := bstep (se 1 (by rfl) ⟨478658, by rfl⟩ : syracuseStep 638211 = 957317) B957317
theorem B638227 : Blo 634301 638227 := bstep (se 1 (by rfl) ⟨478670, by rfl⟩ : syracuseStep 638227 = 957341) B957341
theorem B638243 : Blo 634301 638243 := bstep (se 1 (by rfl) ⟨478682, by rfl⟩ : syracuseStep 638243 = 957365) B957365
theorem B2145581 : Blo 634301 2145581 := bstep (se 3 (by rfl) ⟨402296, by rfl⟩ : syracuseStep 2145581 = 804593) B804593
theorem B638259 : Blo 634301 638259 := bstep (se 1 (by rfl) ⟨478694, by rfl⟩ : syracuseStep 638259 = 957389) B957389
theorem B638275 : Blo 634301 638275 := bstep (se 1 (by rfl) ⟨478706, by rfl⟩ : syracuseStep 638275 = 957413) B957413
theorem B638291 : Blo 634301 638291 := bstep (se 1 (by rfl) ⟨478718, by rfl⟩ : syracuseStep 638291 = 957437) B957437
theorem B2145635 : Blo 634301 2145635 := bstep (se 1 (by rfl) ⟨1609226, by rfl⟩ : syracuseStep 2145635 = 3218453) B3218453
theorem B1359281 : Blo 634301 1359281 := bstep (se 2 (by rfl) ⟨509730, by rfl⟩ : syracuseStep 1359281 = 1019461) B1019461
theorem B2145905 : Blo 634301 2145905 := bstep (se 2 (by rfl) ⟨804714, by rfl⟩ : syracuseStep 2145905 = 1609429) B1609429
theorem B3227363 : Blo 634301 3227363 := bstep (se 1 (by rfl) ⟨2420522, by rfl⟩ : syracuseStep 3227363 = 4841045) B4841045
theorem B7749361 : Blo 634301 7749361 := bstep (se 2 (by rfl) ⟨2906010, by rfl⟩ : syracuseStep 7749361 = 5812021) B5812021
theorem B3489841 : Blo 634301 3489841 := bstep (se 2 (by rfl) ⟨1308690, by rfl⟩ : syracuseStep 3489841 = 2617381) B2617381
theorem B802867 : Blo 634301 802867 := bstep (se 1 (by rfl) ⟨602150, by rfl⟩ : syracuseStep 802867 = 1204301) B1204301
theorem B2408525 : Blo 634301 2408525 := bstep (se 3 (by rfl) ⟨451598, by rfl⟩ : syracuseStep 2408525 = 903197) B903197
theorem B2146445 : Blo 634301 2146445 := bstep (se 3 (by rfl) ⟨402458, by rfl⟩ : syracuseStep 2146445 = 804917) B804917
theorem B802963 : Blo 634301 802963 := bstep (se 1 (by rfl) ⟨602222, by rfl⟩ : syracuseStep 802963 = 1204445) B1204445
theorem B2146499 : Blo 634301 2146499 := bstep (se 1 (by rfl) ⟨1609874, by rfl⟩ : syracuseStep 2146499 = 3219749) B3219749
theorem B4145357 : Blo 634301 4145357 := bstep (se 3 (by rfl) ⟨777254, by rfl⟩ : syracuseStep 4145357 = 1554509) B1554509
theorem B1720547 : Blo 634301 1720547 := bstep (se 1 (by rfl) ⟨1290410, by rfl⟩ : syracuseStep 1720547 = 2580821) B2580821
theorem B3621125 : Blo 634301 3621125 := bstep (se 4 (by rfl) ⟨339480, by rfl⟩ : syracuseStep 3621125 = 678961) B678961
theorem B4342157 : Blo 634301 4342157 := bstep (se 3 (by rfl) ⟨814154, by rfl⟩ : syracuseStep 4342157 = 1628309) B1628309
theorem B2146769 : Blo 634301 2146769 := bstep (se 2 (by rfl) ⟨805038, by rfl⟩ : syracuseStep 2146769 = 1610077) B1610077
theorem B3228173 : Blo 634301 3228173 := bstep (se 3 (by rfl) ⟨605282, by rfl⟩ : syracuseStep 3228173 = 1210565) B1210565
theorem B1360451 : Blo 634301 1360451 := bstep (se 1 (by rfl) ⟨1020338, by rfl⟩ : syracuseStep 1360451 = 2040677) B2040677
theorem B3064397 : Blo 634301 3064397 := bstep (se 3 (by rfl) ⟨574574, by rfl⟩ : syracuseStep 3064397 = 1149149) B1149149
theorem B803459 : Blo 634301 803459 := bstep (se 1 (by rfl) ⟨602594, by rfl⟩ : syracuseStep 803459 = 1205189) B1205189
theorem B3621581 : Blo 634301 3621581 := bstep (se 3 (by rfl) ⟨679046, by rfl⟩ : syracuseStep 3621581 = 1358093) B1358093
theorem B8373061 : Blo 634301 8373061 := bstep (se 4 (by rfl) ⟨784974, by rfl⟩ : syracuseStep 8373061 = 1569949) B1569949
theorem B967601 : Blo 634301 967601 := bstep (se 2 (by rfl) ⟨362850, by rfl⟩ : syracuseStep 967601 = 725701) B725701
theorem B2147309 : Blo 634301 2147309 := bstep (se 3 (by rfl) ⟨402620, by rfl⟩ : syracuseStep 2147309 = 805241) B805241
theorem B2147363 : Blo 634301 2147363 := bstep (se 1 (by rfl) ⟨1610522, by rfl⟩ : syracuseStep 2147363 = 3221045) B3221045
theorem B4899953 : Blo 634301 4899953 := bstep (se 2 (by rfl) ⟨1837482, by rfl⟩ : syracuseStep 4899953 = 3674965) B3674965
theorem B5817541 : Blo 634301 5817541 := bstep (se 4 (by rfl) ⟨545394, by rfl⟩ : syracuseStep 5817541 = 1090789) B1090789
theorem B2147633 : Blo 634301 2147633 := bstep (se 2 (by rfl) ⟨805362, by rfl⟩ : syracuseStep 2147633 = 1610725) B1610725
theorem B804163 : Blo 634301 804163 := bstep (se 1 (by rfl) ⟨603122, by rfl⟩ : syracuseStep 804163 = 1206245) B1206245
theorem B804259 : Blo 634301 804259 := bstep (se 1 (by rfl) ⟨603194, by rfl⟩ : syracuseStep 804259 = 1206389) B1206389
theorem B5817827 : Blo 634301 5817827 := bstep (se 1 (by rfl) ⟨4363370, by rfl⟩ : syracuseStep 5817827 = 8726741) B8726741
theorem B4343473 : Blo 634301 4343473 := bstep (se 2 (by rfl) ⟨1628802, by rfl⟩ : syracuseStep 4343473 = 3257605) B3257605
theorem B2148173 : Blo 634301 2148173 := bstep (se 3 (by rfl) ⟨402782, by rfl⟩ : syracuseStep 2148173 = 805565) B805565
theorem B2148227 : Blo 634301 2148227 := bstep (se 1 (by rfl) ⟨1611170, by rfl⟩ : syracuseStep 2148227 = 3222341) B3222341
theorem B4835213 : Blo 634301 4835213 := bstep (se 3 (by rfl) ⟨906602, by rfl⟩ : syracuseStep 4835213 = 1813205) B1813205
theorem B1427345 : Blo 634301 1427345 := bstep (se 2 (by rfl) ⟨535254, by rfl⟩ : syracuseStep 1427345 = 1070509) B1070509
theorem B804755 : Blo 634301 804755 := bstep (se 1 (by rfl) ⟨603566, by rfl⟩ : syracuseStep 804755 = 1207133) B1207133
theorem B1427363 : Blo 634301 1427363 := bstep (se 1 (by rfl) ⟨1070522, by rfl⟩ : syracuseStep 1427363 = 2141045) B2141045
theorem B2148497 : Blo 634301 2148497 := bstep (se 2 (by rfl) ⟨805686, by rfl⟩ : syracuseStep 2148497 = 1611373) B1611373
theorem B1427633 : Blo 634301 1427633 := bstep (se 2 (by rfl) ⟨535362, by rfl⟩ : syracuseStep 1427633 = 1070725) B1070725
theorem B1427651 : Blo 634301 1427651 := bstep (se 1 (by rfl) ⟨1070738, by rfl⟩ : syracuseStep 1427651 = 2141477) B2141477
theorem B1165763 : Blo 634301 1165763 := bstep (se 1 (by rfl) ⟨874322, by rfl⟩ : syracuseStep 1165763 = 1748645) B1748645
theorem B1427921 : Blo 634301 1427921 := bstep (se 2 (by rfl) ⟨535470, by rfl⟩ : syracuseStep 1427921 = 1070941) B1070941
theorem B1427939 : Blo 634301 1427939 := bstep (se 1 (by rfl) ⟨1070954, by rfl⟩ : syracuseStep 1427939 = 2141909) B2141909
theorem B1362467 : Blo 634301 1362467 := bstep (se 1 (by rfl) ⟨1021850, by rfl⟩ : syracuseStep 1362467 = 2043701) B2043701
theorem B805459 : Blo 634301 805459 := bstep (se 1 (by rfl) ⟨604094, by rfl⟩ : syracuseStep 805459 = 1208189) B1208189
theorem B1722989 : Blo 634301 1722989 := bstep (se 3 (by rfl) ⟨323060, by rfl⟩ : syracuseStep 1722989 = 646121) B646121
theorem B2149037 : Blo 634301 2149037 := bstep (se 3 (by rfl) ⟨402944, by rfl⟩ : syracuseStep 2149037 = 805889) B805889
theorem B805555 : Blo 634301 805555 := bstep (se 1 (by rfl) ⟨604166, by rfl⟩ : syracuseStep 805555 = 1208333) B1208333
theorem B2149091 : Blo 634301 2149091 := bstep (se 1 (by rfl) ⟨1611818, by rfl⟩ : syracuseStep 2149091 = 3223637) B3223637
theorem B1428209 : Blo 634301 1428209 := bstep (se 2 (by rfl) ⟨535578, by rfl⟩ : syracuseStep 1428209 = 1071157) B1071157
theorem B1100531 : Blo 634301 1100531 := bstep (se 1 (by rfl) ⟨825398, by rfl⟩ : syracuseStep 1100531 = 1650797) B1650797
theorem B1428227 : Blo 634301 1428227 := bstep (se 1 (by rfl) ⟨1071170, by rfl⟩ : syracuseStep 1428227 = 2142341) B2142341
theorem B903955 : Blo 634301 903955 := bstep (se 1 (by rfl) ⟨677966, by rfl⟩ : syracuseStep 903955 = 1355933) B1355933
theorem B969571 : Blo 634301 969571 := bstep (se 1 (by rfl) ⟨727178, by rfl⟩ : syracuseStep 969571 = 1454357) B1454357
theorem B904051 : Blo 634301 904051 := bstep (se 1 (by rfl) ⟨678038, by rfl⟩ : syracuseStep 904051 = 1356077) B1356077
theorem B2411441 : Blo 634301 2411441 := bstep (se 2 (by rfl) ⟨904290, by rfl⟩ : syracuseStep 2411441 = 1808581) B1808581
theorem B8145845 : Blo 634301 8145845 := bstep (se 5 (by rfl) ⟨381836, by rfl⟩ : syracuseStep 8145845 = 763673) B763673
theorem B2149361 : Blo 634301 2149361 := bstep (se 2 (by rfl) ⟨806010, by rfl⟩ : syracuseStep 2149361 = 1612021) B1612021
theorem B5426189 : Blo 634301 5426189 := bstep (se 3 (by rfl) ⟨1017410, by rfl⟩ : syracuseStep 5426189 = 2034821) B2034821
theorem B1428497 : Blo 634301 1428497 := bstep (se 2 (by rfl) ⟨535686, by rfl⟩ : syracuseStep 1428497 = 1071373) B1071373
theorem B1428515 : Blo 634301 1428515 := bstep (se 1 (by rfl) ⟨1071386, by rfl⟩ : syracuseStep 1428515 = 2142773) B2142773
theorem B806051 : Blo 634301 806051 := bstep (se 1 (by rfl) ⟨604538, by rfl⟩ : syracuseStep 806051 = 1209077) B1209077
theorem B1428785 : Blo 634301 1428785 := bstep (se 2 (by rfl) ⟨535794, by rfl⟩ : syracuseStep 1428785 = 1071589) B1071589
theorem B4082993 : Blo 634301 4082993 := bstep (se 2 (by rfl) ⟨1531122, by rfl⟩ : syracuseStep 4082993 = 3062245) B3062245
theorem B1428803 : Blo 634301 1428803 := bstep (se 1 (by rfl) ⟨1071602, by rfl⟩ : syracuseStep 1428803 = 2143205) B2143205
theorem B904547 : Blo 634301 904547 := bstep (se 1 (by rfl) ⟨678410, by rfl⟩ : syracuseStep 904547 = 1356821) B1356821
theorem B3231089 : Blo 634301 3231089 := bstep (se 2 (by rfl) ⟨1211658, by rfl⟩ : syracuseStep 3231089 = 2423317) B2423317
theorem B2149901 : Blo 634301 2149901 := bstep (se 3 (by rfl) ⟨403106, by rfl⟩ : syracuseStep 2149901 = 806213) B806213
theorem B3624497 : Blo 634301 3624497 := bstep (se 2 (by rfl) ⟨1359186, by rfl⟩ : syracuseStep 3624497 = 2718373) B2718373
theorem B2149955 : Blo 634301 2149955 := bstep (se 1 (by rfl) ⟨1612466, by rfl⟩ : syracuseStep 2149955 = 3224933) B3224933
theorem B1429073 : Blo 634301 1429073 := bstep (se 2 (by rfl) ⟨535902, by rfl⟩ : syracuseStep 1429073 = 1071805) B1071805
theorem B1429091 : Blo 634301 1429091 := bstep (se 1 (by rfl) ⟨1071818, by rfl⟩ : syracuseStep 1429091 = 2143637) B2143637
theorem B970417 : Blo 634301 970417 := bstep (se 2 (by rfl) ⟨363906, by rfl⟩ : syracuseStep 970417 = 727813) B727813
theorem B1036001 : Blo 634301 1036001 := bstep (se 2 (by rfl) ⟨388500, by rfl⟩ : syracuseStep 1036001 = 777001) B777001
theorem B2150225 : Blo 634301 2150225 := bstep (se 2 (by rfl) ⟨806334, by rfl⟩ : syracuseStep 2150225 = 1612669) B1612669
theorem B806755 : Blo 634301 806755 := bstep (se 1 (by rfl) ⟨605066, by rfl⟩ : syracuseStep 806755 = 1210133) B1210133
theorem B1429361 : Blo 634301 1429361 := bstep (se 2 (by rfl) ⟨536010, by rfl⟩ : syracuseStep 1429361 = 1072021) B1072021
theorem B1429379 : Blo 634301 1429379 := bstep (se 1 (by rfl) ⟨1072034, by rfl⟩ : syracuseStep 1429379 = 2144069) B2144069
theorem B806851 : Blo 634301 806851 := bstep (se 1 (by rfl) ⟨605138, by rfl⟩ : syracuseStep 806851 = 1210277) B1210277
theorem B905185 : Blo 634301 905185 := bstep (se 2 (by rfl) ⟨339444, by rfl⟩ : syracuseStep 905185 = 678889) B678889
theorem B2904113 : Blo 634301 2904113 := bstep (se 2 (by rfl) ⟨1089042, by rfl⟩ : syracuseStep 2904113 = 2178085) B2178085
theorem B1429649 : Blo 634301 1429649 := bstep (se 2 (by rfl) ⟨536118, by rfl⟩ : syracuseStep 1429649 = 1072237) B1072237
theorem B1429667 : Blo 634301 1429667 := bstep (se 1 (by rfl) ⟨1072250, by rfl⟩ : syracuseStep 1429667 = 2144501) B2144501
theorem B905521 : Blo 634301 905521 := bstep (se 2 (by rfl) ⟨339570, by rfl⟩ : syracuseStep 905521 = 679141) B679141
theorem B2412899 : Blo 634301 2412899 := bstep (se 1 (by rfl) ⟨1809674, by rfl⟩ : syracuseStep 2412899 = 3619349) B3619349
theorem B1528163 : Blo 634301 1528163 := bstep (se 1 (by rfl) ⟨1146122, by rfl⟩ : syracuseStep 1528163 = 2292245) B2292245
theorem B2150765 : Blo 634301 2150765 := bstep (se 3 (by rfl) ⟨403268, by rfl⟩ : syracuseStep 2150765 = 806537) B806537
theorem B2150819 : Blo 634301 2150819 := bstep (se 1 (by rfl) ⟨1613114, by rfl⟩ : syracuseStep 2150819 = 3226229) B3226229
theorem B1429937 : Blo 634301 1429937 := bstep (se 2 (by rfl) ⟨536226, by rfl⟩ : syracuseStep 1429937 = 1072453) B1072453
theorem B807347 : Blo 634301 807347 := bstep (se 1 (by rfl) ⟨605510, by rfl⟩ : syracuseStep 807347 = 1211021) B1211021
theorem B1429955 : Blo 634301 1429955 := bstep (se 1 (by rfl) ⟨1072466, by rfl⟩ : syracuseStep 1429955 = 2144933) B2144933
theorem B2904589 : Blo 634301 2904589 := bstep (se 3 (by rfl) ⟨544610, by rfl⟩ : syracuseStep 2904589 = 1089221) B1089221
theorem B1528355 : Blo 634301 1528355 := bstep (se 1 (by rfl) ⟨1146266, by rfl⟩ : syracuseStep 1528355 = 2292533) B2292533
theorem B1528433 : Blo 634301 1528433 := bstep (se 2 (by rfl) ⟨573162, by rfl⟩ : syracuseStep 1528433 = 1146325) B1146325
theorem B2151089 : Blo 634301 2151089 := bstep (se 2 (by rfl) ⟨806658, by rfl⟩ : syracuseStep 2151089 = 1613317) B1613317
theorem B1430225 : Blo 634301 1430225 := bstep (se 2 (by rfl) ⟨536334, by rfl⟩ : syracuseStep 1430225 = 1072669) B1072669
theorem B1430243 : Blo 634301 1430243 := bstep (se 1 (by rfl) ⟨1072682, by rfl⟩ : syracuseStep 1430243 = 2145365) B2145365
theorem B4838129 : Blo 634301 4838129 := bstep (se 2 (by rfl) ⟨1814298, by rfl⟩ : syracuseStep 4838129 = 3628597) B3628597
theorem B7230221 : Blo 634301 7230221 := bstep (se 3 (by rfl) ⟨1355666, by rfl⟩ : syracuseStep 7230221 = 2711333) B2711333
theorem B1528625 : Blo 634301 1528625 := bstep (se 2 (by rfl) ⟨573234, by rfl⟩ : syracuseStep 1528625 = 1146469) B1146469
theorem B906113 : Blo 634301 906113 := bstep (se 2 (by rfl) ⟨339792, by rfl⟩ : syracuseStep 906113 = 679585) B679585
theorem B3625955 : Blo 634301 3625955 := bstep (se 1 (by rfl) ⟨2719466, by rfl⟩ : syracuseStep 3625955 = 5438933) B5438933
theorem B1430513 : Blo 634301 1430513 := bstep (se 2 (by rfl) ⟨536442, by rfl⟩ : syracuseStep 1430513 = 1072885) B1072885
theorem B1430531 : Blo 634301 1430531 := bstep (se 1 (by rfl) ⟨1072898, by rfl⟩ : syracuseStep 1430531 = 2145797) B2145797
theorem B2151629 : Blo 634301 2151629 := bstep (se 3 (by rfl) ⟨403430, by rfl⟩ : syracuseStep 2151629 = 806861) B806861
theorem B2151683 : Blo 634301 2151683 := bstep (se 1 (by rfl) ⟨1613762, by rfl⟩ : syracuseStep 2151683 = 3227525) B3227525
theorem B1430801 : Blo 634301 1430801 := bstep (se 2 (by rfl) ⟨536550, by rfl⟩ : syracuseStep 1430801 = 1073101) B1073101
theorem B1430819 : Blo 634301 1430819 := bstep (se 1 (by rfl) ⟨1073114, by rfl⟩ : syracuseStep 1430819 = 2146229) B2146229
theorem B1529123 : Blo 634301 1529123 := bstep (se 1 (by rfl) ⟨1146842, by rfl⟩ : syracuseStep 1529123 = 2293685) B2293685
theorem B1070401 : Blo 634301 1070401 := bstep (se 2 (by rfl) ⟨401400, by rfl⟩ : syracuseStep 1070401 = 802801) B802801
theorem B2413901 : Blo 634301 2413901 := bstep (se 3 (by rfl) ⟨452606, by rfl⟩ : syracuseStep 2413901 = 905213) B905213
theorem B1070435 : Blo 634301 1070435 := bstep (se 1 (by rfl) ⟨802826, by rfl⟩ : syracuseStep 1070435 = 1605653) B1605653
theorem B1529201 : Blo 634301 1529201 := bstep (se 2 (by rfl) ⟨573450, by rfl⟩ : syracuseStep 1529201 = 1146901) B1146901
theorem B906643 : Blo 634301 906643 := bstep (se 1 (by rfl) ⟨679982, by rfl⟩ : syracuseStep 906643 = 1359965) B1359965
theorem B1070563 : Blo 634301 1070563 := bstep (se 1 (by rfl) ⟨802922, by rfl⟩ : syracuseStep 1070563 = 1605845) B1605845
theorem B2151953 : Blo 634301 2151953 := bstep (se 2 (by rfl) ⟨806982, by rfl⟩ : syracuseStep 2151953 = 1613965) B1613965
theorem B1431089 : Blo 634301 1431089 := bstep (se 2 (by rfl) ⟨536658, by rfl⟩ : syracuseStep 1431089 = 1073317) B1073317
theorem B1431107 : Blo 634301 1431107 := bstep (se 1 (by rfl) ⟨1073330, by rfl⟩ : syracuseStep 1431107 = 2146661) B2146661
theorem B1070705 : Blo 634301 1070705 := bstep (se 2 (by rfl) ⟨401514, by rfl⟩ : syracuseStep 1070705 = 803029) B803029
theorem B2578061 : Blo 634301 2578061 := bstep (se 3 (by rfl) ⟨483386, by rfl⟩ : syracuseStep 2578061 = 966773) B966773
theorem B4085453 : Blo 634301 4085453 := bstep (se 3 (by rfl) ⟨766022, by rfl⟩ : syracuseStep 4085453 = 1532045) B1532045
theorem B677603 : Blo 634301 677603 := bstep (se 1 (by rfl) ⟨508202, by rfl⟩ : syracuseStep 677603 = 1016405) B1016405
theorem B906979 : Blo 634301 906979 := bstep (se 1 (by rfl) ⟨680234, by rfl⟩ : syracuseStep 906979 = 1360469) B1360469
theorem B1070833 : Blo 634301 1070833 := bstep (se 2 (by rfl) ⟨401562, by rfl⟩ : syracuseStep 1070833 = 803125) B803125
theorem B1529585 : Blo 634301 1529585 := bstep (se 2 (by rfl) ⟨573594, by rfl⟩ : syracuseStep 1529585 = 1147189) B1147189
theorem B1070867 : Blo 634301 1070867 := bstep (se 1 (by rfl) ⟨803150, by rfl⟩ : syracuseStep 1070867 = 1606301) B1606301
theorem B1431377 : Blo 634301 1431377 := bstep (se 2 (by rfl) ⟨536766, by rfl⟩ : syracuseStep 1431377 = 1073533) B1073533
theorem B677731 : Blo 634301 677731 := bstep (se 1 (by rfl) ⟨508298, by rfl⟩ : syracuseStep 677731 = 1016597) B1016597
theorem B1431395 : Blo 634301 1431395 := bstep (se 1 (by rfl) ⟨1073546, by rfl⟩ : syracuseStep 1431395 = 2147093) B2147093
theorem B6510449 : Blo 634301 6510449 := bstep (se 2 (by rfl) ⟨2441418, by rfl⟩ : syracuseStep 6510449 = 4882837) B4882837
theorem B1070995 : Blo 634301 1070995 := bstep (se 1 (by rfl) ⟨803246, by rfl⟩ : syracuseStep 1070995 = 1606493) B1606493
theorem B3626957 : Blo 634301 3626957 := bstep (se 3 (by rfl) ⟨680054, by rfl⟩ : syracuseStep 3626957 = 1360109) B1360109
theorem B10344419 : Blo 634301 10344419 := bstep (se 1 (by rfl) ⟨7758314, by rfl⟩ : syracuseStep 10344419 = 15516629) B15516629
theorem B1071137 : Blo 634301 1071137 := bstep (se 2 (by rfl) ⟨401676, by rfl⟩ : syracuseStep 1071137 = 803353) B803353
theorem B2152493 : Blo 634301 2152493 := bstep (se 3 (by rfl) ⟨403592, by rfl⟩ : syracuseStep 2152493 = 807185) B807185
theorem B2152547 : Blo 634301 2152547 := bstep (se 1 (by rfl) ⟨1614410, by rfl⟩ : syracuseStep 2152547 = 3228821) B3228821
theorem B1431665 : Blo 634301 1431665 := bstep (se 2 (by rfl) ⟨536874, by rfl⟩ : syracuseStep 1431665 = 1073749) B1073749
theorem B1431683 : Blo 634301 1431683 := bstep (se 1 (by rfl) ⟨1073762, by rfl⟩ : syracuseStep 1431683 = 2147525) B2147525
theorem B1071265 : Blo 634301 1071265 := bstep (se 2 (by rfl) ⟨401724, by rfl⟩ : syracuseStep 1071265 = 803449) B803449
theorem B1071299 : Blo 634301 1071299 := bstep (se 1 (by rfl) ⟨803474, by rfl⟩ : syracuseStep 1071299 = 1606949) B1606949
theorem B907537 : Blo 634301 907537 := bstep (se 2 (by rfl) ⟨340326, by rfl⟩ : syracuseStep 907537 = 680653) B680653
theorem B907571 : Blo 634301 907571 := bstep (se 1 (by rfl) ⟨680678, by rfl⟩ : syracuseStep 907571 = 1361357) B1361357
theorem B1071427 : Blo 634301 1071427 := bstep (se 1 (by rfl) ⟨803570, by rfl⟩ : syracuseStep 1071427 = 1607141) B1607141
theorem B2152817 : Blo 634301 2152817 := bstep (se 2 (by rfl) ⟨807306, by rfl⟩ : syracuseStep 2152817 = 1614613) B1614613
theorem B1431953 : Blo 634301 1431953 := bstep (se 2 (by rfl) ⟨536982, by rfl⟩ : syracuseStep 1431953 = 1073965) B1073965
theorem B1431971 : Blo 634301 1431971 := bstep (se 1 (by rfl) ⟨1073978, by rfl⟩ : syracuseStep 1431971 = 2147957) B2147957
theorem B1071569 : Blo 634301 1071569 := bstep (se 2 (by rfl) ⟨401838, by rfl⟩ : syracuseStep 1071569 = 803677) B803677
theorem B1071697 : Blo 634301 1071697 := bstep (se 2 (by rfl) ⟨401886, by rfl⟩ : syracuseStep 1071697 = 803773) B803773
theorem B1071731 : Blo 634301 1071731 := bstep (se 1 (by rfl) ⟨803798, by rfl⟩ : syracuseStep 1071731 = 1607597) B1607597
theorem B10869389 : Blo 634301 10869389 := bstep (se 3 (by rfl) ⟨2038010, by rfl⟩ : syracuseStep 10869389 = 4076021) B4076021
theorem B678547 : Blo 634301 678547 := bstep (se 1 (by rfl) ⟨508910, by rfl⟩ : syracuseStep 678547 = 1017821) B1017821
theorem B1432241 : Blo 634301 1432241 := bstep (se 2 (by rfl) ⟨537090, by rfl⟩ : syracuseStep 1432241 = 1074181) B1074181
theorem B7756469 : Blo 634301 7756469 := bstep (se 5 (by rfl) ⟨363584, by rfl⟩ : syracuseStep 7756469 = 727169) B727169
theorem B1432259 : Blo 634301 1432259 := bstep (se 1 (by rfl) ⟨1074194, by rfl⟩ : syracuseStep 1432259 = 2148389) B2148389
theorem B1071859 : Blo 634301 1071859 := bstep (se 1 (by rfl) ⟨803894, by rfl⟩ : syracuseStep 1071859 = 1607789) B1607789
theorem B908129 : Blo 634301 908129 := bstep (se 2 (by rfl) ⟨340548, by rfl⟩ : syracuseStep 908129 = 681097) B681097
theorem B1072001 : Blo 634301 1072001 := bstep (se 2 (by rfl) ⟨402000, by rfl⟩ : syracuseStep 1072001 = 804001) B804001
theorem B2153357 : Blo 634301 2153357 := bstep (se 3 (by rfl) ⟨403754, by rfl⟩ : syracuseStep 2153357 = 807509) B807509
theorem B908209 : Blo 634301 908209 := bstep (se 2 (by rfl) ⟨340578, by rfl⟩ : syracuseStep 908209 = 681157) B681157
theorem B2153411 : Blo 634301 2153411 := bstep (se 1 (by rfl) ⟨1615058, by rfl⟩ : syracuseStep 2153411 = 3230117) B3230117
theorem B1432529 : Blo 634301 1432529 := bstep (se 2 (by rfl) ⟨537198, by rfl⟩ : syracuseStep 1432529 = 1074397) B1074397
theorem B1432547 : Blo 634301 1432547 := bstep (se 1 (by rfl) ⟨1074410, by rfl⟩ : syracuseStep 1432547 = 2148821) B2148821
theorem B2710513 : Blo 634301 2710513 := bstep (se 2 (by rfl) ⟨1016442, by rfl⟩ : syracuseStep 2710513 = 2032885) B2032885
theorem B3496945 : Blo 634301 3496945 := bstep (se 2 (by rfl) ⟨1311354, by rfl⟩ : syracuseStep 3496945 = 2622709) B2622709
theorem B1072129 : Blo 634301 1072129 := bstep (se 2 (by rfl) ⟨402048, by rfl⟩ : syracuseStep 1072129 = 804097) B804097
theorem B1072163 : Blo 634301 1072163 := bstep (se 1 (by rfl) ⟨804122, by rfl⟩ : syracuseStep 1072163 = 1608245) B1608245
theorem B12213301 : Blo 634301 12213301 := bstep (se 5 (by rfl) ⟨572498, by rfl⟩ : syracuseStep 12213301 = 1144997) B1144997
theorem B1072291 : Blo 634301 1072291 := bstep (se 1 (by rfl) ⟨804218, by rfl⟩ : syracuseStep 1072291 = 1608437) B1608437
theorem B2153681 : Blo 634301 2153681 := bstep (se 2 (by rfl) ⟨807630, by rfl⟩ : syracuseStep 2153681 = 1615261) B1615261
theorem B1432817 : Blo 634301 1432817 := bstep (se 2 (by rfl) ⟨537306, by rfl⟩ : syracuseStep 1432817 = 1074613) B1074613
theorem B1432835 : Blo 634301 1432835 := bstep (se 1 (by rfl) ⟨1074626, by rfl⟩ : syracuseStep 1432835 = 2149253) B2149253
theorem B1072433 : Blo 634301 1072433 := bstep (se 2 (by rfl) ⟨402162, by rfl⟩ : syracuseStep 1072433 = 804325) B804325
theorem B2416013 : Blo 634301 2416013 := bstep (se 3 (by rfl) ⟨453002, by rfl⟩ : syracuseStep 2416013 = 906005) B906005
theorem B1072561 : Blo 634301 1072561 := bstep (se 2 (by rfl) ⟨402210, by rfl⟩ : syracuseStep 1072561 = 804421) B804421
theorem B1531345 : Blo 634301 1531345 := bstep (se 2 (by rfl) ⟨574254, by rfl⟩ : syracuseStep 1531345 = 1148509) B1148509
theorem B1072595 : Blo 634301 1072595 := bstep (se 1 (by rfl) ⟨804446, by rfl⟩ : syracuseStep 1072595 = 1608893) B1608893
theorem B1433105 : Blo 634301 1433105 := bstep (se 2 (by rfl) ⟨537414, by rfl⟩ : syracuseStep 1433105 = 1074829) B1074829
theorem B1433123 : Blo 634301 1433123 := bstep (se 1 (by rfl) ⟨1074842, by rfl⟩ : syracuseStep 1433123 = 2149685) B2149685
theorem B1072723 : Blo 634301 1072723 := bstep (se 1 (by rfl) ⟨804542, by rfl⟩ : syracuseStep 1072723 = 1609085) B1609085
theorem B7233137 : Blo 634301 7233137 := bstep (se 2 (by rfl) ⟨2712426, by rfl⟩ : syracuseStep 7233137 = 5424853) B5424853
theorem B1072865 : Blo 634301 1072865 := bstep (se 2 (by rfl) ⟨402324, by rfl⟩ : syracuseStep 1072865 = 804649) B804649
theorem B2154221 : Blo 634301 2154221 := bstep (se 3 (by rfl) ⟨403916, by rfl⟩ : syracuseStep 2154221 = 807833) B807833
theorem B1433393 : Blo 634301 1433393 := bstep (se 2 (by rfl) ⟨537522, by rfl⟩ : syracuseStep 1433393 = 1075045) B1075045
theorem B1433411 : Blo 634301 1433411 := bstep (se 1 (by rfl) ⟨1075058, by rfl⟩ : syracuseStep 1433411 = 2150117) B2150117
theorem B1072993 : Blo 634301 1072993 := bstep (se 2 (by rfl) ⟨402372, by rfl⟩ : syracuseStep 1072993 = 804745) B804745
theorem B1073027 : Blo 634301 1073027 := bstep (se 1 (by rfl) ⟨804770, by rfl⟩ : syracuseStep 1073027 = 1609541) B1609541
theorem B4087685 : Blo 634301 4087685 := bstep (se 4 (by rfl) ⟨383220, by rfl⟩ : syracuseStep 4087685 = 766441) B766441
theorem B1073155 : Blo 634301 1073155 := bstep (se 1 (by rfl) ⟨804866, by rfl⟩ : syracuseStep 1073155 = 1609733) B1609733
theorem B1466435 : Blo 634301 1466435 := bstep (se 1 (by rfl) ⟨1099826, by rfl⟩ : syracuseStep 1466435 = 2199653) B2199653
theorem B1859651 : Blo 634301 1859651 := bstep (se 1 (by rfl) ⟨1394738, by rfl⟩ : syracuseStep 1859651 = 2789477) B2789477
theorem B1433681 : Blo 634301 1433681 := bstep (se 2 (by rfl) ⟨537630, by rfl⟩ : syracuseStep 1433681 = 1075261) B1075261
theorem B1433699 : Blo 634301 1433699 := bstep (se 1 (by rfl) ⟨1075274, by rfl⟩ : syracuseStep 1433699 = 2150549) B2150549
theorem B1073297 : Blo 634301 1073297 := bstep (se 2 (by rfl) ⟨402486, by rfl⟩ : syracuseStep 1073297 = 804973) B804973
theorem B2416817 : Blo 634301 2416817 := bstep (se 2 (by rfl) ⟨906306, by rfl⟩ : syracuseStep 2416817 = 1812613) B1812613
theorem B1204483 : Blo 634301 1204483 := bstep (se 1 (by rfl) ⟨903362, by rfl⟩ : syracuseStep 1204483 = 1806725) B1806725
theorem B1073425 : Blo 634301 1073425 := bstep (se 2 (by rfl) ⟨402534, by rfl⟩ : syracuseStep 1073425 = 805069) B805069
theorem B1073459 : Blo 634301 1073459 := bstep (se 1 (by rfl) ⟨805094, by rfl⟩ : syracuseStep 1073459 = 1610189) B1610189
theorem B4251973 : Blo 634301 4251973 := bstep (se 4 (by rfl) ⟨398622, by rfl⟩ : syracuseStep 4251973 = 797245) B797245
theorem B1433969 : Blo 634301 1433969 := bstep (se 2 (by rfl) ⟨537738, by rfl⟩ : syracuseStep 1433969 = 1075477) B1075477
theorem B1433987 : Blo 634301 1433987 := bstep (se 1 (by rfl) ⟨1075490, by rfl⟩ : syracuseStep 1433987 = 2150981) B2150981
theorem B1073587 : Blo 634301 1073587 := bstep (se 1 (by rfl) ⟨805190, by rfl⟩ : syracuseStep 1073587 = 1610381) B1610381
theorem B1073729 : Blo 634301 1073729 := bstep (se 2 (by rfl) ⟨402648, by rfl⟩ : syracuseStep 1073729 = 805297) B805297
theorem B1434257 : Blo 634301 1434257 := bstep (se 2 (by rfl) ⟨537846, by rfl⟩ : syracuseStep 1434257 = 1075693) B1075693
theorem B1434275 : Blo 634301 1434275 := bstep (se 1 (by rfl) ⟨1075706, by rfl⟩ : syracuseStep 1434275 = 2151413) B2151413
theorem B1073857 : Blo 634301 1073857 := bstep (se 2 (by rfl) ⟨402696, by rfl⟩ : syracuseStep 1073857 = 805393) B805393
theorem B1204931 : Blo 634301 1204931 := bstep (se 1 (by rfl) ⟨903698, by rfl⟩ : syracuseStep 1204931 = 1807397) B1807397
theorem B1073891 : Blo 634301 1073891 := bstep (se 1 (by rfl) ⟨805418, by rfl⟩ : syracuseStep 1073891 = 1610837) B1610837
theorem B3433265 : Blo 634301 3433265 := bstep (se 2 (by rfl) ⟨1287474, by rfl⟩ : syracuseStep 3433265 = 2574949) B2574949
theorem B3629873 : Blo 634301 3629873 := bstep (se 2 (by rfl) ⟨1361202, by rfl⟩ : syracuseStep 3629873 = 2722405) B2722405
theorem B2417485 : Blo 634301 2417485 := bstep (se 3 (by rfl) ⟨453278, by rfl⟩ : syracuseStep 2417485 = 906557) B906557
theorem B1074019 : Blo 634301 1074019 := bstep (se 1 (by rfl) ⟨805514, by rfl⟩ : syracuseStep 1074019 = 1611029) B1611029
theorem B1434545 : Blo 634301 1434545 := bstep (se 2 (by rfl) ⟨537954, by rfl⟩ : syracuseStep 1434545 = 1075909) B1075909
theorem B1434563 : Blo 634301 1434563 := bstep (se 1 (by rfl) ⟨1075922, by rfl⟩ : syracuseStep 1434563 = 2151845) B2151845
theorem B1205219 : Blo 634301 1205219 := bstep (se 1 (by rfl) ⟨903914, by rfl⟩ : syracuseStep 1205219 = 1807829) B1807829
theorem B1074161 : Blo 634301 1074161 := bstep (se 2 (by rfl) ⟨402810, by rfl⟩ : syracuseStep 1074161 = 805621) B805621
theorem B713731 : Blo 634301 713731 := bstep (se 1 (by rfl) ⟨535298, by rfl⟩ : syracuseStep 713731 = 1070597) B1070597
theorem B2090033 : Blo 634301 2090033 := bstep (se 2 (by rfl) ⟨783762, by rfl⟩ : syracuseStep 2090033 = 1567525) B1567525
theorem B1074289 : Blo 634301 1074289 := bstep (se 2 (by rfl) ⟨402858, by rfl⟩ : syracuseStep 1074289 = 805717) B805717
theorem B713875 : Blo 634301 713875 := bstep (se 1 (by rfl) ⟨535406, by rfl⟩ : syracuseStep 713875 = 1070813) B1070813
theorem B1074323 : Blo 634301 1074323 := bstep (se 1 (by rfl) ⟨805742, by rfl⟩ : syracuseStep 1074323 = 1611485) B1611485
theorem B1434833 : Blo 634301 1434833 := bstep (se 2 (by rfl) ⟨538062, by rfl⟩ : syracuseStep 1434833 = 1076125) B1076125
theorem B1434851 : Blo 634301 1434851 := bstep (se 1 (by rfl) ⟨1076138, by rfl⟩ : syracuseStep 1434851 = 2152277) B2152277
theorem B1074451 : Blo 634301 1074451 := bstep (se 1 (by rfl) ⟨805838, by rfl⟩ : syracuseStep 1074451 = 1611677) B1611677
theorem B714019 : Blo 634301 714019 := bstep (se 1 (by rfl) ⟨535514, by rfl⟩ : syracuseStep 714019 = 1071029) B1071029
theorem B1074593 : Blo 634301 1074593 := bstep (se 2 (by rfl) ⟨402972, by rfl⟩ : syracuseStep 1074593 = 805945) B805945
theorem B2319779 : Blo 634301 2319779 := bstep (se 1 (by rfl) ⟨1739834, by rfl⟩ : syracuseStep 2319779 = 3479669) B3479669
theorem B714163 : Blo 634301 714163 := bstep (se 1 (by rfl) ⟨535622, by rfl⟩ : syracuseStep 714163 = 1071245) B1071245
theorem B1435121 : Blo 634301 1435121 := bstep (se 2 (by rfl) ⟨538170, by rfl⟩ : syracuseStep 1435121 = 1076341) B1076341
theorem B1435139 : Blo 634301 1435139 := bstep (se 1 (by rfl) ⟨1076354, by rfl⟩ : syracuseStep 1435139 = 2152709) B2152709
theorem B1074721 : Blo 634301 1074721 := bstep (se 2 (by rfl) ⟨403020, by rfl⟩ : syracuseStep 1074721 = 806041) B806041
theorem B714307 : Blo 634301 714307 := bstep (se 1 (by rfl) ⟨535730, by rfl⟩ : syracuseStep 714307 = 1071461) B1071461
theorem B1074755 : Blo 634301 1074755 := bstep (se 1 (by rfl) ⟨806066, by rfl⟩ : syracuseStep 1074755 = 1612133) B1612133
theorem B2418275 : Blo 634301 2418275 := bstep (se 1 (by rfl) ⟨1813706, by rfl⟩ : syracuseStep 2418275 = 3627413) B3627413
theorem B5170787 : Blo 634301 5170787 := bstep (se 1 (by rfl) ⟨3878090, by rfl⟩ : syracuseStep 5170787 = 7756181) B7756181
theorem B1074883 : Blo 634301 1074883 := bstep (se 1 (by rfl) ⟨806162, by rfl⟩ : syracuseStep 1074883 = 1612325) B1612325
theorem B714451 : Blo 634301 714451 := bstep (se 1 (by rfl) ⟨535838, by rfl⟩ : syracuseStep 714451 = 1071677) B1071677
theorem B1435409 : Blo 634301 1435409 := bstep (se 2 (by rfl) ⟨538278, by rfl⟩ : syracuseStep 1435409 = 1076557) B1076557
theorem B1435427 : Blo 634301 1435427 := bstep (se 1 (by rfl) ⟨1076570, by rfl⟩ : syracuseStep 1435427 = 2153141) B2153141
theorem B1075025 : Blo 634301 1075025 := bstep (se 2 (by rfl) ⟨403134, by rfl⟩ : syracuseStep 1075025 = 806269) B806269
theorem B714595 : Blo 634301 714595 := bstep (se 1 (by rfl) ⟨535946, by rfl⟩ : syracuseStep 714595 = 1071893) B1071893
theorem B1206161 : Blo 634301 1206161 := bstep (se 2 (by rfl) ⟨452310, by rfl⟩ : syracuseStep 1206161 = 904621) B904621
theorem B1632209 : Blo 634301 1632209 := bstep (se 2 (by rfl) ⟨612078, by rfl⟩ : syracuseStep 1632209 = 1224157) B1224157
theorem B1075153 : Blo 634301 1075153 := bstep (se 2 (by rfl) ⟨403182, by rfl⟩ : syracuseStep 1075153 = 806365) B806365
theorem B714739 : Blo 634301 714739 := bstep (se 1 (by rfl) ⟨536054, by rfl⟩ : syracuseStep 714739 = 1072109) B1072109
theorem B1075187 : Blo 634301 1075187 := bstep (se 1 (by rfl) ⟨806390, by rfl⟩ : syracuseStep 1075187 = 1612781) B1612781
theorem B1009667 : Blo 634301 1009667 := bstep (se 1 (by rfl) ⟨757250, by rfl⟩ : syracuseStep 1009667 = 1514501) B1514501
theorem B1435697 : Blo 634301 1435697 := bstep (se 2 (by rfl) ⟨538386, by rfl⟩ : syracuseStep 1435697 = 1076773) B1076773
theorem B3237937 : Blo 634301 3237937 := bstep (se 2 (by rfl) ⟨1214226, by rfl⟩ : syracuseStep 3237937 = 2428453) B2428453
theorem B1435715 : Blo 634301 1435715 := bstep (se 1 (by rfl) ⟨1076786, by rfl⟩ : syracuseStep 1435715 = 2153573) B2153573
theorem B1075315 : Blo 634301 1075315 := bstep (se 1 (by rfl) ⟨806486, by rfl⟩ : syracuseStep 1075315 = 1612973) B1612973
theorem B714883 : Blo 634301 714883 := bstep (se 1 (by rfl) ⟨536162, by rfl⟩ : syracuseStep 714883 = 1072325) B1072325
theorem B3631331 : Blo 634301 3631331 := bstep (se 1 (by rfl) ⟨2723498, by rfl⟩ : syracuseStep 3631331 = 5446997) B5446997
theorem B2418929 : Blo 634301 2418929 := bstep (se 2 (by rfl) ⟨907098, by rfl⟩ : syracuseStep 2418929 = 1814197) B1814197
theorem B1075457 : Blo 634301 1075457 := bstep (se 2 (by rfl) ⟨403296, by rfl⟩ : syracuseStep 1075457 = 806593) B806593
theorem B715027 : Blo 634301 715027 := bstep (se 1 (by rfl) ⟨536270, by rfl⟩ : syracuseStep 715027 = 1072541) B1072541
theorem B1435985 : Blo 634301 1435985 := bstep (se 2 (by rfl) ⟨538494, by rfl⟩ : syracuseStep 1435985 = 1076989) B1076989
theorem B1436003 : Blo 634301 1436003 := bstep (se 1 (by rfl) ⟨1077002, by rfl⟩ : syracuseStep 1436003 = 2154005) B2154005
theorem B1075585 : Blo 634301 1075585 := bstep (se 2 (by rfl) ⟨403344, by rfl⟩ : syracuseStep 1075585 = 806689) B806689
theorem B715171 : Blo 634301 715171 := bstep (se 1 (by rfl) ⟨536378, by rfl⟩ : syracuseStep 715171 = 1072757) B1072757
theorem B1075619 : Blo 634301 1075619 := bstep (se 1 (by rfl) ⟨806714, by rfl⟩ : syracuseStep 1075619 = 1613429) B1613429
theorem B1075747 : Blo 634301 1075747 := bstep (se 1 (by rfl) ⟨806810, by rfl⟩ : syracuseStep 1075747 = 1613621) B1613621
theorem B715315 : Blo 634301 715315 := bstep (se 1 (by rfl) ⟨536486, by rfl⟩ : syracuseStep 715315 = 1072973) B1072973
theorem B1075889 : Blo 634301 1075889 := bstep (se 2 (by rfl) ⟨403458, by rfl⟩ : syracuseStep 1075889 = 806917) B806917
theorem B715459 : Blo 634301 715459 := bstep (se 1 (by rfl) ⟨536594, by rfl⟩ : syracuseStep 715459 = 1073189) B1073189
theorem B1207057 : Blo 634301 1207057 := bstep (se 2 (by rfl) ⟨452646, by rfl⟩ : syracuseStep 1207057 = 905293) B905293
theorem B1076017 : Blo 634301 1076017 := bstep (se 2 (by rfl) ⟨403506, by rfl⟩ : syracuseStep 1076017 = 807013) B807013
theorem B715603 : Blo 634301 715603 := bstep (se 1 (by rfl) ⟨536702, by rfl⟩ : syracuseStep 715603 = 1073405) B1073405
theorem B1076051 : Blo 634301 1076051 := bstep (se 1 (by rfl) ⟨807038, by rfl⟩ : syracuseStep 1076051 = 1614077) B1614077
theorem B2288483 : Blo 634301 2288483 := bstep (se 1 (by rfl) ⟨1716362, by rfl⟩ : syracuseStep 2288483 = 3432725) B3432725
theorem B1207217 : Blo 634301 1207217 := bstep (se 2 (by rfl) ⟨452706, by rfl⟩ : syracuseStep 1207217 = 905413) B905413
theorem B1076179 : Blo 634301 1076179 := bstep (se 1 (by rfl) ⟨807134, by rfl⟩ : syracuseStep 1076179 = 1614269) B1614269
theorem B715747 : Blo 634301 715747 := bstep (se 1 (by rfl) ⟨536810, by rfl⟩ : syracuseStep 715747 = 1073621) B1073621
theorem B1076321 : Blo 634301 1076321 := bstep (se 2 (by rfl) ⟨403620, by rfl⟩ : syracuseStep 1076321 = 807241) B807241
theorem B945265 : Blo 634301 945265 := bstep (se 2 (by rfl) ⟨354474, by rfl⟩ : syracuseStep 945265 = 708949) B708949
theorem B715891 : Blo 634301 715891 := bstep (se 1 (by rfl) ⟨536918, by rfl⟩ : syracuseStep 715891 = 1073837) B1073837
theorem B1076449 : Blo 634301 1076449 := bstep (se 2 (by rfl) ⟨403668, by rfl⟩ : syracuseStep 1076449 = 807337) B807337
theorem B716035 : Blo 634301 716035 := bstep (se 1 (by rfl) ⟨537026, by rfl⟩ : syracuseStep 716035 = 1074053) B1074053
theorem B1076483 : Blo 634301 1076483 := bstep (se 1 (by rfl) ⟨807362, by rfl⟩ : syracuseStep 1076483 = 1614725) B1614725
theorem B1207619 : Blo 634301 1207619 := bstep (se 1 (by rfl) ⟨905714, by rfl⟩ : syracuseStep 1207619 = 1811429) B1811429
theorem B2714957 : Blo 634301 2714957 := bstep (se 3 (by rfl) ⟨509054, by rfl⟩ : syracuseStep 2714957 = 1018109) B1018109
theorem B13036913 : Blo 634301 13036913 := bstep (se 2 (by rfl) ⟨4888842, by rfl⟩ : syracuseStep 13036913 = 9777685) B9777685
theorem B1076611 : Blo 634301 1076611 := bstep (se 1 (by rfl) ⟨807458, by rfl⟩ : syracuseStep 1076611 = 1614917) B1614917
theorem B814483 : Blo 634301 814483 := bstep (se 1 (by rfl) ⟨610862, by rfl⟩ : syracuseStep 814483 = 1221725) B1221725
theorem B716179 : Blo 634301 716179 := bstep (se 1 (by rfl) ⟨537134, by rfl⟩ : syracuseStep 716179 = 1074269) B1074269
theorem B2059793 : Blo 634301 2059793 := bstep (se 2 (by rfl) ⟨772422, by rfl⟩ : syracuseStep 2059793 = 1544845) B1544845
theorem B1076753 : Blo 634301 1076753 := bstep (se 2 (by rfl) ⟨403782, by rfl⟩ : syracuseStep 1076753 = 807565) B807565
theorem B716323 : Blo 634301 716323 := bstep (se 1 (by rfl) ⟨537242, by rfl⟩ : syracuseStep 716323 = 1074485) B1074485
theorem B1076881 : Blo 634301 1076881 := bstep (se 2 (by rfl) ⟨403830, by rfl⟩ : syracuseStep 1076881 = 807661) B807661
theorem B2420387 : Blo 634301 2420387 := bstep (se 1 (by rfl) ⟨1815290, by rfl⟩ : syracuseStep 2420387 = 3630581) B3630581
theorem B2420401 : Blo 634301 2420401 := bstep (se 2 (by rfl) ⟨907650, by rfl⟩ : syracuseStep 2420401 = 1815301) B1815301
theorem B716467 : Blo 634301 716467 := bstep (se 1 (by rfl) ⟨537350, by rfl⟩ : syracuseStep 716467 = 1074701) B1074701
theorem B1076915 : Blo 634301 1076915 := bstep (se 1 (by rfl) ⟨807686, by rfl⟩ : syracuseStep 1076915 = 1615373) B1615373
theorem B4353763 : Blo 634301 4353763 := bstep (se 1 (by rfl) ⟨3265322, by rfl⟩ : syracuseStep 4353763 = 6530645) B6530645
theorem B1077043 : Blo 634301 1077043 := bstep (se 1 (by rfl) ⟨807782, by rfl⟩ : syracuseStep 1077043 = 1615565) B1615565
theorem B716611 : Blo 634301 716611 := bstep (se 1 (by rfl) ⟨537458, by rfl⟩ : syracuseStep 716611 = 1074917) B1074917
theorem B716755 : Blo 634301 716755 := bstep (se 1 (by rfl) ⟨537566, by rfl⟩ : syracuseStep 716755 = 1075133) B1075133
theorem B2289649 : Blo 634301 2289649 := bstep (se 2 (by rfl) ⟨858618, by rfl⟩ : syracuseStep 2289649 = 1717237) B1717237
theorem B716899 : Blo 634301 716899 := bstep (se 1 (by rfl) ⟨537674, by rfl⟩ : syracuseStep 716899 = 1075349) B1075349
theorem B1208515 : Blo 634301 1208515 := bstep (se 1 (by rfl) ⟨906386, by rfl⟩ : syracuseStep 1208515 = 1812773) B1812773
theorem B717043 : Blo 634301 717043 := bstep (se 1 (by rfl) ⟨537782, by rfl⟩ : syracuseStep 717043 = 1075565) B1075565
theorem B1208675 : Blo 634301 1208675 := bstep (se 1 (by rfl) ⟨906506, by rfl⟩ : syracuseStep 1208675 = 1813013) B1813013
theorem B717187 : Blo 634301 717187 := bstep (se 1 (by rfl) ⟨537890, by rfl⟩ : syracuseStep 717187 = 1075781) B1075781
theorem B2584973 : Blo 634301 2584973 := bstep (se 3 (by rfl) ⟨484682, by rfl⟩ : syracuseStep 2584973 = 969365) B969365
theorem B717331 : Blo 634301 717331 := bstep (se 1 (by rfl) ⟨537998, by rfl⟩ : syracuseStep 717331 = 1075997) B1075997
theorem B717475 : Blo 634301 717475 := bstep (se 1 (by rfl) ⟨538106, by rfl⟩ : syracuseStep 717475 = 1076213) B1076213
theorem B717619 : Blo 634301 717619 := bstep (se 1 (by rfl) ⟨538214, by rfl⟩ : syracuseStep 717619 = 1076429) B1076429
theorem B717763 : Blo 634301 717763 := bstep (se 1 (by rfl) ⟨538322, by rfl⟩ : syracuseStep 717763 = 1076645) B1076645
theorem B2061379 : Blo 634301 2061379 := bstep (se 1 (by rfl) ⟨1546034, by rfl⟩ : syracuseStep 2061379 = 3092069) B3092069
theorem B3667021 : Blo 634301 3667021 := bstep (se 3 (by rfl) ⟨687566, by rfl⟩ : syracuseStep 3667021 = 1375133) B1375133
theorem B717907 : Blo 634301 717907 := bstep (se 1 (by rfl) ⟨538430, by rfl⟩ : syracuseStep 717907 = 1076861) B1076861
theorem B2421859 : Blo 634301 2421859 := bstep (se 1 (by rfl) ⟨1816394, by rfl⟩ : syracuseStep 2421859 = 3632789) B3632789
theorem B9270413 : Blo 634301 9270413 := bstep (se 3 (by rfl) ⟨1738202, by rfl⟩ : syracuseStep 9270413 = 3476405) B3476405
theorem B718051 : Blo 634301 718051 := bstep (se 1 (by rfl) ⟨538538, by rfl⟩ : syracuseStep 718051 = 1077077) B1077077
theorem B4912397 : Blo 634301 4912397 := bstep (se 3 (by rfl) ⟨921074, by rfl⟩ : syracuseStep 4912397 = 1842149) B1842149
theorem B1209745 : Blo 634301 1209745 := bstep (se 2 (by rfl) ⟨453654, by rfl⟩ : syracuseStep 1209745 = 907309) B907309
theorem B1963565 : Blo 634301 1963565 := bstep (se 3 (by rfl) ⟨368168, by rfl⟩ : syracuseStep 1963565 = 736337) B736337
theorem B18347633 : Blo 634301 18347633 := bstep (se 2 (by rfl) ⟨6880362, by rfl⟩ : syracuseStep 18347633 = 13760725) B13760725
theorem B1144451 : Blo 634301 1144451 := bstep (se 1 (by rfl) ⟨858338, by rfl⟩ : syracuseStep 1144451 = 1716677) B1716677
theorem B16512821 : Blo 634301 16512821 := bstep (se 5 (by rfl) ⟨774038, by rfl⟩ : syracuseStep 16512821 = 1548077) B1548077
theorem B1308593 : Blo 634301 1308593 := bstep (se 2 (by rfl) ⟨490722, by rfl⟩ : syracuseStep 1308593 = 981445) B981445
theorem B2455523 : Blo 634301 2455523 := bstep (se 1 (by rfl) ⟨1841642, by rfl⟩ : syracuseStep 2455523 = 3683285) B3683285
theorem B1210801 : Blo 634301 1210801 := bstep (se 2 (by rfl) ⟨454050, by rfl⟩ : syracuseStep 1210801 = 908101) B908101
theorem B2292301 : Blo 634301 2292301 := bstep (se 3 (by rfl) ⟨429806, by rfl⟩ : syracuseStep 2292301 = 859613) B859613
theorem B1211203 : Blo 634301 1211203 := bstep (se 1 (by rfl) ⟨908402, by rfl⟩ : syracuseStep 1211203 = 1816805) B1816805
theorem B1932113 : Blo 634301 1932113 := bstep (se 2 (by rfl) ⟨724542, by rfl⟩ : syracuseStep 1932113 = 1449085) B1449085
theorem B1211249 : Blo 634301 1211249 := bstep (se 2 (by rfl) ⟨454218, by rfl⟩ : syracuseStep 1211249 = 908437) B908437
theorem B982147 : Blo 634301 982147 := bstep (se 1 (by rfl) ⟨736610, by rfl⟩ : syracuseStep 982147 = 1473221) B1473221
theorem B1211537 : Blo 634301 1211537 := bstep (se 2 (by rfl) ⟨454326, by rfl⟩ : syracuseStep 1211537 = 908653) B908653
theorem B55934165 : Blo 634301 55934165 := bstep (se 7 (by rfl) ⟨655478, by rfl⟩ : syracuseStep 55934165 = 1310957) B1310957
theorem B916769 : Blo 634301 916769 := bstep (se 2 (by rfl) ⟨343788, by rfl⟩ : syracuseStep 916769 = 687577) B687577
theorem B1965379 : Blo 634301 1965379 := bstep (se 1 (by rfl) ⟨1474034, by rfl⟩ : syracuseStep 1965379 = 2948069) B2948069
theorem B1473905 : Blo 634301 1473905 := bstep (se 2 (by rfl) ⟨552714, by rfl⟩ : syracuseStep 1473905 = 1105429) B1105429
theorem B2719331 : Blo 634301 2719331 := bstep (se 1 (by rfl) ⟨2039498, by rfl⟩ : syracuseStep 2719331 = 4078997) B4078997
theorem B1605683 : Blo 634301 1605683 := bstep (se 1 (by rfl) ⟨1204262, by rfl⟩ : syracuseStep 1605683 = 2408525) B2408525
theorem B4653121 : Blo 634301 4653121 := bstep (se 2 (by rfl) ⟨1744920, by rfl⟩ : syracuseStep 4653121 = 3489841) B3489841
theorem B1147031 : Blo 634301 1147031 := bstep (se 1 (by rfl) ⟨860273, by rfl⟩ : syracuseStep 1147031 = 1720547) B1720547
theorem B1147073 : Blo 634301 1147073 := bstep (se 2 (by rfl) ⟨430152, by rfl⟩ : syracuseStep 1147073 = 860305) B860305
theorem B17268997 : Blo 634301 17268997 := bstep (se 4 (by rfl) ⟨1618968, by rfl⟩ : syracuseStep 17268997 = 3237937) B3237937
theorem B2326849 : Blo 634301 2326849 := bstep (se 2 (by rfl) ⟨872568, by rfl⟩ : syracuseStep 2326849 = 1745137) B1745137
theorem B1605977 : Blo 634301 1605977 := bstep (se 2 (by rfl) ⟨602241, by rfl⟩ : syracuseStep 1605977 = 1204483) B1204483
theorem B5669297 : Blo 634301 5669297 := bstep (se 2 (by rfl) ⟨2125986, by rfl⟩ : syracuseStep 5669297 = 4251973) B4251973
theorem B951563 : Blo 634301 951563 := bstep (se 1 (by rfl) ⟨713672, by rfl⟩ : syracuseStep 951563 = 1427345) B1427345
theorem B951575 : Blo 634301 951575 := bstep (se 1 (by rfl) ⟨713681, by rfl⟩ : syracuseStep 951575 = 1427363) B1427363
theorem B951641 : Blo 634301 951641 := bstep (se 2 (by rfl) ⟨356865, by rfl⟩ : syracuseStep 951641 = 713731) B713731
theorem B951755 : Blo 634301 951755 := bstep (se 1 (by rfl) ⟨713816, by rfl⟩ : syracuseStep 951755 = 1427633) B1427633
theorem B951767 : Blo 634301 951767 := bstep (se 1 (by rfl) ⟨713825, by rfl⟩ : syracuseStep 951767 = 1427651) B1427651
theorem B951833 : Blo 634301 951833 := bstep (se 2 (by rfl) ⟨356937, by rfl⟩ : syracuseStep 951833 = 713875) B713875
theorem B951947 : Blo 634301 951947 := bstep (se 1 (by rfl) ⟨713960, by rfl⟩ : syracuseStep 951947 = 1427921) B1427921
theorem B951959 : Blo 634301 951959 := bstep (se 1 (by rfl) ⟨713969, by rfl⟩ : syracuseStep 951959 = 1427939) B1427939
theorem B952025 : Blo 634301 952025 := bstep (se 2 (by rfl) ⟨357009, by rfl⟩ : syracuseStep 952025 = 714019) B714019
theorem B952139 : Blo 634301 952139 := bstep (se 1 (by rfl) ⟨714104, by rfl⟩ : syracuseStep 952139 = 1428209) B1428209
theorem B952151 : Blo 634301 952151 := bstep (se 1 (by rfl) ⟨714113, by rfl⟩ : syracuseStep 952151 = 1428227) B1428227
theorem B952217 : Blo 634301 952217 := bstep (se 2 (by rfl) ⟨357081, by rfl⟩ : syracuseStep 952217 = 714163) B714163
theorem B1607627 : Blo 634301 1607627 := bstep (se 1 (by rfl) ⟨1205720, by rfl⟩ : syracuseStep 1607627 = 2411441) B2411441
theorem B952331 : Blo 634301 952331 := bstep (se 1 (by rfl) ⟨714248, by rfl⟩ : syracuseStep 952331 = 1428497) B1428497
theorem B952343 : Blo 634301 952343 := bstep (se 1 (by rfl) ⟨714257, by rfl⟩ : syracuseStep 952343 = 1428515) B1428515
theorem B952409 : Blo 634301 952409 := bstep (se 2 (by rfl) ⟨357153, by rfl⟩ : syracuseStep 952409 = 714307) B714307
theorem B952523 : Blo 634301 952523 := bstep (se 1 (by rfl) ⟨714392, by rfl⟩ : syracuseStep 952523 = 1428785) B1428785
theorem B2721995 : Blo 634301 2721995 := bstep (se 1 (by rfl) ⟨2041496, by rfl⟩ : syracuseStep 2721995 = 4082993) B4082993
theorem B952535 : Blo 634301 952535 := bstep (se 1 (by rfl) ⟨714401, by rfl⟩ : syracuseStep 952535 = 1428803) B1428803
theorem B952601 : Blo 634301 952601 := bstep (se 2 (by rfl) ⟨357225, by rfl⟩ : syracuseStep 952601 = 714451) B714451
theorem B2034013 : Blo 634301 2034013 := bstep (se 3 (by rfl) ⟨381377, by rfl⟩ : syracuseStep 2034013 = 762755) B762755
theorem B8259941 : Blo 634301 8259941 := bstep (se 4 (by rfl) ⟨774369, by rfl⟩ : syracuseStep 8259941 = 1548739) B1548739
theorem B952715 : Blo 634301 952715 := bstep (se 1 (by rfl) ⟨714536, by rfl⟩ : syracuseStep 952715 = 1429073) B1429073
theorem B952727 : Blo 634301 952727 := bstep (se 1 (by rfl) ⟨714545, by rfl⟩ : syracuseStep 952727 = 1429091) B1429091
theorem B1149337 : Blo 634301 1149337 := bstep (se 2 (by rfl) ⟨431001, by rfl⟩ : syracuseStep 1149337 = 862003) B862003
theorem B952793 : Blo 634301 952793 := bstep (se 2 (by rfl) ⟨357297, by rfl⟩ : syracuseStep 952793 = 714595) B714595
theorem B952907 : Blo 634301 952907 := bstep (se 1 (by rfl) ⟨714680, by rfl⟩ : syracuseStep 952907 = 1429361) B1429361
theorem B952919 : Blo 634301 952919 := bstep (se 1 (by rfl) ⟨714689, by rfl⟩ : syracuseStep 952919 = 1429379) B1429379
theorem B3213917 : Blo 634301 3213917 := bstep (se 3 (by rfl) ⟨602609, by rfl⟩ : syracuseStep 3213917 = 1205219) B1205219
theorem B952985 : Blo 634301 952985 := bstep (se 2 (by rfl) ⟨357369, by rfl⟩ : syracuseStep 952985 = 714739) B714739
theorem B4819661 : Blo 634301 4819661 := bstep (se 3 (by rfl) ⟨903686, by rfl⟩ : syracuseStep 4819661 = 1807373) B1807373
theorem B6195973 : Blo 634301 6195973 := bstep (se 4 (by rfl) ⟨580872, by rfl⟩ : syracuseStep 6195973 = 1161745) B1161745
theorem B953099 : Blo 634301 953099 := bstep (se 1 (by rfl) ⟨714824, by rfl⟩ : syracuseStep 953099 = 1429649) B1429649
theorem B953111 : Blo 634301 953111 := bstep (se 1 (by rfl) ⟨714833, by rfl⟩ : syracuseStep 953111 = 1429667) B1429667
theorem B5442349 : Blo 634301 5442349 := bstep (se 3 (by rfl) ⟨1020440, by rfl⟩ : syracuseStep 5442349 = 2040881) B2040881
theorem B723799 : Blo 634301 723799 := bstep (se 1 (by rfl) ⟨542849, by rfl⟩ : syracuseStep 723799 = 1085699) B1085699
theorem B953177 : Blo 634301 953177 := bstep (se 2 (by rfl) ⟨357441, by rfl⟩ : syracuseStep 953177 = 714883) B714883
theorem B1608599 : Blo 634301 1608599 := bstep (se 1 (by rfl) ⟨1206449, by rfl⟩ : syracuseStep 1608599 = 2412899) B2412899
theorem B1018775 : Blo 634301 1018775 := bstep (se 1 (by rfl) ⟨764081, by rfl⟩ : syracuseStep 1018775 = 1528163) B1528163
theorem B953291 : Blo 634301 953291 := bstep (se 1 (by rfl) ⟨714968, by rfl⟩ : syracuseStep 953291 = 1429937) B1429937
theorem B953303 : Blo 634301 953303 := bstep (se 1 (by rfl) ⟨714977, by rfl⟩ : syracuseStep 953303 = 1429955) B1429955
theorem B1018903 : Blo 634301 1018903 := bstep (se 1 (by rfl) ⟨764177, by rfl⟩ : syracuseStep 1018903 = 1528355) B1528355
theorem B953369 : Blo 634301 953369 := bstep (se 2 (by rfl) ⟨357513, by rfl⟩ : syracuseStep 953369 = 715027) B715027
theorem B1018955 : Blo 634301 1018955 := bstep (se 1 (by rfl) ⟨764216, by rfl⟩ : syracuseStep 1018955 = 1528433) B1528433
theorem B953483 : Blo 634301 953483 := bstep (se 1 (by rfl) ⟨715112, by rfl⟩ : syracuseStep 953483 = 1430225) B1430225
theorem B953495 : Blo 634301 953495 := bstep (se 1 (by rfl) ⟨715121, by rfl⟩ : syracuseStep 953495 = 1430243) B1430243
theorem B4820147 : Blo 634301 4820147 := bstep (se 1 (by rfl) ⟨3615110, by rfl⟩ : syracuseStep 4820147 = 7230221) B7230221
theorem B1019083 : Blo 634301 1019083 := bstep (se 1 (by rfl) ⟨764312, by rfl⟩ : syracuseStep 1019083 = 1528625) B1528625
theorem B953561 : Blo 634301 953561 := bstep (se 2 (by rfl) ⟨357585, by rfl⟩ : syracuseStep 953561 = 715171) B715171
theorem B953675 : Blo 634301 953675 := bstep (se 1 (by rfl) ⟨715256, by rfl⟩ : syracuseStep 953675 = 1430513) B1430513
theorem B953687 : Blo 634301 953687 := bstep (se 1 (by rfl) ⟨715265, by rfl⟩ : syracuseStep 953687 = 1430531) B1430531
theorem B953753 : Blo 634301 953753 := bstep (se 2 (by rfl) ⟨357657, by rfl⟩ : syracuseStep 953753 = 715315) B715315
theorem B2297261 : Blo 634301 2297261 := bstep (se 3 (by rfl) ⟨430736, by rfl⟩ : syracuseStep 2297261 = 861473) B861473
theorem B953867 : Blo 634301 953867 := bstep (se 1 (by rfl) ⟨715400, by rfl⟩ : syracuseStep 953867 = 1430801) B1430801
theorem B953879 : Blo 634301 953879 := bstep (se 1 (by rfl) ⟨715409, by rfl⟩ : syracuseStep 953879 = 1430819) B1430819
theorem B5508643 : Blo 634301 5508643 := bstep (se 1 (by rfl) ⟨4131482, by rfl⟩ : syracuseStep 5508643 = 8262965) B8262965
theorem B1609267 : Blo 634301 1609267 := bstep (se 1 (by rfl) ⟨1206950, by rfl⟩ : syracuseStep 1609267 = 2413901) B2413901
theorem B1019467 : Blo 634301 1019467 := bstep (se 1 (by rfl) ⟨764600, by rfl⟩ : syracuseStep 1019467 = 1529201) B1529201
theorem B953945 : Blo 634301 953945 := bstep (se 2 (by rfl) ⟨357729, by rfl⟩ : syracuseStep 953945 = 715459) B715459
theorem B1609409 : Blo 634301 1609409 := bstep (se 2 (by rfl) ⟨603528, by rfl⟩ : syracuseStep 1609409 = 1207057) B1207057
theorem B954059 : Blo 634301 954059 := bstep (se 1 (by rfl) ⟨715544, by rfl⟩ : syracuseStep 954059 = 1431089) B1431089
theorem B954071 : Blo 634301 954071 := bstep (se 1 (by rfl) ⟨715553, by rfl⟩ : syracuseStep 954071 = 1431107) B1431107
theorem B954137 : Blo 634301 954137 := bstep (se 2 (by rfl) ⟨357801, by rfl⟩ : syracuseStep 954137 = 715603) B715603
theorem B2723635 : Blo 634301 2723635 := bstep (se 1 (by rfl) ⟨2042726, by rfl⟩ : syracuseStep 2723635 = 4085453) B4085453
theorem B1019723 : Blo 634301 1019723 := bstep (se 1 (by rfl) ⟨764792, by rfl⟩ : syracuseStep 1019723 = 1529585) B1529585
theorem B954251 : Blo 634301 954251 := bstep (se 1 (by rfl) ⟨715688, by rfl⟩ : syracuseStep 954251 = 1431377) B1431377
theorem B954263 : Blo 634301 954263 := bstep (se 1 (by rfl) ⟨715697, by rfl⟩ : syracuseStep 954263 = 1431395) B1431395
theorem B954329 : Blo 634301 954329 := bstep (se 2 (by rfl) ⟨357873, by rfl⟩ : syracuseStep 954329 = 715747) B715747
theorem B954443 : Blo 634301 954443 := bstep (se 1 (by rfl) ⟨715832, by rfl⟩ : syracuseStep 954443 = 1431665) B1431665
theorem B954455 : Blo 634301 954455 := bstep (se 1 (by rfl) ⟨715841, by rfl⟩ : syracuseStep 954455 = 1431683) B1431683
theorem B5443685 : Blo 634301 5443685 := bstep (se 4 (by rfl) ⟨510345, by rfl⟩ : syracuseStep 5443685 = 1020691) B1020691
theorem B954521 : Blo 634301 954521 := bstep (se 2 (by rfl) ⟨357945, by rfl⟩ : syracuseStep 954521 = 715891) B715891
theorem B1806553 : Blo 634301 1806553 := bstep (se 2 (by rfl) ⟨677457, by rfl⟩ : syracuseStep 1806553 = 1354915) B1354915
theorem B954635 : Blo 634301 954635 := bstep (se 1 (by rfl) ⟨715976, by rfl⟩ : syracuseStep 954635 = 1431953) B1431953
theorem B954647 : Blo 634301 954647 := bstep (se 1 (by rfl) ⟨715985, by rfl⟩ : syracuseStep 954647 = 1431971) B1431971
theorem B1020185 : Blo 634301 1020185 := bstep (se 2 (by rfl) ⟨382569, by rfl⟩ : syracuseStep 1020185 = 765139) B765139
theorem B954713 : Blo 634301 954713 := bstep (se 2 (by rfl) ⟨358017, by rfl⟩ : syracuseStep 954713 = 716035) B716035
theorem B1020313 : Blo 634301 1020313 := bstep (se 2 (by rfl) ⟨382617, by rfl⟩ : syracuseStep 1020313 = 765235) B765235
theorem B7246259 : Blo 634301 7246259 := bstep (se 1 (by rfl) ⟨5434694, by rfl⟩ : syracuseStep 7246259 = 10869389) B10869389
theorem B954827 : Blo 634301 954827 := bstep (se 1 (by rfl) ⟨716120, by rfl⟩ : syracuseStep 954827 = 1432241) B1432241
theorem B954839 : Blo 634301 954839 := bstep (se 1 (by rfl) ⟨716129, by rfl⟩ : syracuseStep 954839 = 1432259) B1432259
theorem B1085977 : Blo 634301 1085977 := bstep (se 2 (by rfl) ⟨407241, by rfl⟩ : syracuseStep 1085977 = 814483) B814483
theorem B954905 : Blo 634301 954905 := bstep (se 2 (by rfl) ⟨358089, by rfl⟩ : syracuseStep 954905 = 716179) B716179
theorem B1806941 : Blo 634301 1806941 := bstep (se 3 (by rfl) ⟨338801, by rfl⟩ : syracuseStep 1806941 = 677603) B677603
theorem B4821605 : Blo 634301 4821605 := bstep (se 4 (by rfl) ⟨452025, by rfl⟩ : syracuseStep 4821605 = 904051) B904051
theorem B955019 : Blo 634301 955019 := bstep (se 1 (by rfl) ⟨716264, by rfl⟩ : syracuseStep 955019 = 1432529) B1432529
theorem B3216023 : Blo 634301 3216023 := bstep (se 1 (by rfl) ⟨2412017, by rfl⟩ : syracuseStep 3216023 = 4824035) B4824035
theorem B955031 : Blo 634301 955031 := bstep (se 1 (by rfl) ⟨716273, by rfl⟩ : syracuseStep 955031 = 1432547) B1432547
theorem B955097 : Blo 634301 955097 := bstep (se 2 (by rfl) ⟨358161, by rfl⟩ : syracuseStep 955097 = 716323) B716323
theorem B6132485 : Blo 634301 6132485 := bstep (se 4 (by rfl) ⟨574920, by rfl⟩ : syracuseStep 6132485 = 1149841) B1149841
theorem B955211 : Blo 634301 955211 := bstep (se 1 (by rfl) ⟨716408, by rfl⟩ : syracuseStep 955211 = 1432817) B1432817
theorem B955223 : Blo 634301 955223 := bstep (se 1 (by rfl) ⟨716417, by rfl⟩ : syracuseStep 955223 = 1432835) B1432835
theorem B955289 : Blo 634301 955289 := bstep (se 2 (by rfl) ⟨358233, by rfl⟩ : syracuseStep 955289 = 716467) B716467
theorem B1610675 : Blo 634301 1610675 := bstep (se 1 (by rfl) ⟨1208006, by rfl⟩ : syracuseStep 1610675 = 2416013) B2416013
theorem B2200537 : Blo 634301 2200537 := bstep (se 2 (by rfl) ⟨825201, by rfl⟩ : syracuseStep 2200537 = 1650403) B1650403
theorem B5805017 : Blo 634301 5805017 := bstep (se 2 (by rfl) ⟨2176881, by rfl⟩ : syracuseStep 5805017 = 4353763) B4353763
theorem B1446913 : Blo 634301 1446913 := bstep (se 2 (by rfl) ⟨542592, by rfl⟩ : syracuseStep 1446913 = 1085185) B1085185
theorem B955403 : Blo 634301 955403 := bstep (se 1 (by rfl) ⟨716552, by rfl⟩ : syracuseStep 955403 = 1433105) B1433105
theorem B955415 : Blo 634301 955415 := bstep (se 1 (by rfl) ⟨716561, by rfl⟩ : syracuseStep 955415 = 1433123) B1433123
theorem B4822091 : Blo 634301 4822091 := bstep (se 1 (by rfl) ⟨3616568, by rfl⟩ : syracuseStep 4822091 = 7233137) B7233137
theorem B955481 : Blo 634301 955481 := bstep (se 2 (by rfl) ⟨358305, by rfl⟩ : syracuseStep 955481 = 716611) B716611
theorem B4592791 : Blo 634301 4592791 := bstep (se 1 (by rfl) ⟨3444593, by rfl⟩ : syracuseStep 4592791 = 6889187) B6889187
theorem B955595 : Blo 634301 955595 := bstep (se 1 (by rfl) ⟨716696, by rfl⟩ : syracuseStep 955595 = 1433393) B1433393
theorem B955607 : Blo 634301 955607 := bstep (se 1 (by rfl) ⟨716705, by rfl⟩ : syracuseStep 955607 = 1433411) B1433411
theorem B2725123 : Blo 634301 2725123 := bstep (se 1 (by rfl) ⟨2043842, by rfl⟩ : syracuseStep 2725123 = 4087685) B4087685
theorem B955673 : Blo 634301 955673 := bstep (se 2 (by rfl) ⟨358377, by rfl⟩ : syracuseStep 955673 = 716755) B716755
theorem B3052865 : Blo 634301 3052865 := bstep (se 2 (by rfl) ⟨1144824, by rfl⟩ : syracuseStep 3052865 = 2289649) B2289649
theorem B2299211 : Blo 634301 2299211 := bstep (se 1 (by rfl) ⟨1724408, by rfl⟩ : syracuseStep 2299211 = 3448817) B3448817
theorem B2692445 : Blo 634301 2692445 := bstep (se 3 (by rfl) ⟨504833, by rfl⟩ : syracuseStep 2692445 = 1009667) B1009667
theorem B955787 : Blo 634301 955787 := bstep (se 1 (by rfl) ⟨716840, by rfl⟩ : syracuseStep 955787 = 1433681) B1433681
theorem B955799 : Blo 634301 955799 := bstep (se 1 (by rfl) ⟨716849, by rfl⟩ : syracuseStep 955799 = 1433699) B1433699
theorem B1611211 : Blo 634301 1611211 := bstep (se 1 (by rfl) ⟨1208408, by rfl⟩ : syracuseStep 1611211 = 2416817) B2416817
theorem B955865 : Blo 634301 955865 := bstep (se 2 (by rfl) ⟨358449, by rfl⟩ : syracuseStep 955865 = 716899) B716899
theorem B955979 : Blo 634301 955979 := bstep (se 1 (by rfl) ⟨716984, by rfl⟩ : syracuseStep 955979 = 1433969) B1433969
theorem B955991 : Blo 634301 955991 := bstep (se 1 (by rfl) ⟨716993, by rfl⟩ : syracuseStep 955991 = 1433987) B1433987
theorem B1611353 : Blo 634301 1611353 := bstep (se 2 (by rfl) ⟨604257, by rfl⟩ : syracuseStep 1611353 = 1208515) B1208515
theorem B956057 : Blo 634301 956057 := bstep (se 2 (by rfl) ⟨358521, by rfl⟩ : syracuseStep 956057 = 717043) B717043
theorem B956171 : Blo 634301 956171 := bstep (se 1 (by rfl) ⟨717128, by rfl⟩ : syracuseStep 956171 = 1434257) B1434257
theorem B956183 : Blo 634301 956183 := bstep (se 1 (by rfl) ⟨717137, by rfl⟩ : syracuseStep 956183 = 1434275) B1434275
theorem B956249 : Blo 634301 956249 := bstep (se 2 (by rfl) ⟨358593, by rfl⟩ : syracuseStep 956249 = 717187) B717187
theorem B2725721 : Blo 634301 2725721 := bstep (se 2 (by rfl) ⟨1022145, by rfl⟩ : syracuseStep 2725721 = 2044291) B2044291
theorem B7247717 : Blo 634301 7247717 := bstep (se 4 (by rfl) ⟨679473, by rfl⟩ : syracuseStep 7247717 = 1358947) B1358947
theorem B956363 : Blo 634301 956363 := bstep (se 1 (by rfl) ⟨717272, by rfl⟩ : syracuseStep 956363 = 1434545) B1434545
theorem B956375 : Blo 634301 956375 := bstep (se 1 (by rfl) ⟨717281, by rfl⟩ : syracuseStep 956375 = 1434563) B1434563
theorem B727051 : Blo 634301 727051 := bstep (se 1 (by rfl) ⟨545288, by rfl⟩ : syracuseStep 727051 = 1090577) B1090577
theorem B3872785 : Blo 634301 3872785 := bstep (se 2 (by rfl) ⟨1452294, by rfl⟩ : syracuseStep 3872785 = 2904589) B2904589
theorem B956441 : Blo 634301 956441 := bstep (se 2 (by rfl) ⟨358665, by rfl⟩ : syracuseStep 956441 = 717331) B717331
theorem B956555 : Blo 634301 956555 := bstep (se 1 (by rfl) ⟨717416, by rfl⟩ : syracuseStep 956555 = 1434833) B1434833
theorem B956567 : Blo 634301 956567 := bstep (se 1 (by rfl) ⟨717425, by rfl⟩ : syracuseStep 956567 = 1434851) B1434851
theorem B2726081 : Blo 634301 2726081 := bstep (se 2 (by rfl) ⟨1022280, by rfl⟩ : syracuseStep 2726081 = 2044561) B2044561
theorem B956633 : Blo 634301 956633 := bstep (se 2 (by rfl) ⟨358737, by rfl⟩ : syracuseStep 956633 = 717475) B717475
theorem B956747 : Blo 634301 956747 := bstep (se 1 (by rfl) ⟨717560, by rfl⟩ : syracuseStep 956747 = 1435121) B1435121
theorem B956759 : Blo 634301 956759 := bstep (se 1 (by rfl) ⟨717569, by rfl⟩ : syracuseStep 956759 = 1435139) B1435139
theorem B23239061 : Blo 634301 23239061 := bstep (se 6 (by rfl) ⟨544665, by rfl⟩ : syracuseStep 23239061 = 1089331) B1089331
theorem B1612183 : Blo 634301 1612183 := bstep (se 1 (by rfl) ⟨1209137, by rfl⟩ : syracuseStep 1612183 = 2418275) B2418275
theorem B3447191 : Blo 634301 3447191 := bstep (se 1 (by rfl) ⟨2585393, by rfl⟩ : syracuseStep 3447191 = 5170787) B5170787
theorem B956825 : Blo 634301 956825 := bstep (se 2 (by rfl) ⟨358809, by rfl⟩ : syracuseStep 956825 = 717619) B717619
theorem B956939 : Blo 634301 956939 := bstep (se 1 (by rfl) ⟨717704, by rfl⟩ : syracuseStep 956939 = 1435409) B1435409
theorem B956951 : Blo 634301 956951 := bstep (se 1 (by rfl) ⟨717713, by rfl⟩ : syracuseStep 956951 = 1435427) B1435427
theorem B727607 : Blo 634301 727607 := bstep (se 1 (by rfl) ⟨545705, by rfl⟩ : syracuseStep 727607 = 1091411) B1091411
theorem B957017 : Blo 634301 957017 := bstep (se 2 (by rfl) ⟨358881, by rfl⟩ : syracuseStep 957017 = 717763) B717763
theorem B957131 : Blo 634301 957131 := bstep (se 1 (by rfl) ⟨717848, by rfl⟩ : syracuseStep 957131 = 1435697) B1435697
theorem B957143 : Blo 634301 957143 := bstep (se 1 (by rfl) ⟨717857, by rfl⟩ : syracuseStep 957143 = 1435715) B1435715
theorem B957209 : Blo 634301 957209 := bstep (se 2 (by rfl) ⟨358953, by rfl⟩ : syracuseStep 957209 = 717907) B717907
theorem B1612619 : Blo 634301 1612619 := bstep (se 1 (by rfl) ⟨1209464, by rfl⟩ : syracuseStep 1612619 = 2418929) B2418929
theorem B957323 : Blo 634301 957323 := bstep (se 1 (by rfl) ⟨717992, by rfl⟩ : syracuseStep 957323 = 1435985) B1435985
theorem B2038679 : Blo 634301 2038679 := bstep (se 1 (by rfl) ⟨1529009, by rfl⟩ : syracuseStep 2038679 = 3058019) B3058019
theorem B957335 : Blo 634301 957335 := bstep (se 1 (by rfl) ⟨718001, by rfl⟩ : syracuseStep 957335 = 1436003) B1436003
theorem B4594637 : Blo 634301 4594637 := bstep (se 3 (by rfl) ⟨861494, by rfl⟩ : syracuseStep 4594637 = 1722989) B1722989
theorem B957401 : Blo 634301 957401 := bstep (se 2 (by rfl) ⟨359025, by rfl⟩ : syracuseStep 957401 = 718051) B718051
theorem B1612993 : Blo 634301 1612993 := bstep (se 2 (by rfl) ⟨604872, by rfl⟩ : syracuseStep 1612993 = 1209745) B1209745
theorem B1809857 : Blo 634301 1809857 := bstep (se 2 (by rfl) ⟨678696, by rfl⟩ : syracuseStep 1809857 = 1357393) B1357393
theorem B1809971 : Blo 634301 1809971 := bstep (se 1 (by rfl) ⟨1357478, by rfl⟩ : syracuseStep 1809971 = 2714957) B2714957
theorem B8691275 : Blo 634301 8691275 := bstep (se 1 (by rfl) ⟨6518456, by rfl⟩ : syracuseStep 8691275 = 13036913) B13036913
theorem B859927 : Blo 634301 859927 := bstep (se 1 (by rfl) ⟨644945, by rfl⟩ : syracuseStep 859927 = 1289891) B1289891
theorem B2039575 : Blo 634301 2039575 := bstep (se 1 (by rfl) ⟨1529681, by rfl⟩ : syracuseStep 2039575 = 3059363) B3059363
theorem B1613591 : Blo 634301 1613591 := bstep (se 1 (by rfl) ⟨1210193, by rfl⟩ : syracuseStep 1613591 = 2420387) B2420387
theorem B3219587 : Blo 634301 3219587 := bstep (se 1 (by rfl) ⟨2414690, by rfl⟩ : syracuseStep 3219587 = 4829381) B4829381
theorem B2040011 : Blo 634301 2040011 := bstep (se 1 (by rfl) ⟨1530008, by rfl⟩ : syracuseStep 2040011 = 3060017) B3060017
theorem B5808485 : Blo 634301 5808485 := bstep (se 4 (by rfl) ⟨544545, by rfl⟩ : syracuseStep 5808485 = 1089091) B1089091
theorem B1614401 : Blo 634301 1614401 := bstep (se 2 (by rfl) ⟨605400, by rfl⟩ : syracuseStep 1614401 = 1210801) B1210801
theorem B3056401 : Blo 634301 3056401 := bstep (se 2 (by rfl) ⟨1146150, by rfl⟩ : syracuseStep 3056401 = 2292301) B2292301
theorem B12231755 : Blo 634301 12231755 := bstep (se 1 (by rfl) ⟨9173816, by rfl⟩ : syracuseStep 12231755 = 18347633) B18347633
theorem B762967 : Blo 634301 762967 := bstep (se 1 (by rfl) ⟨572225, by rfl⟩ : syracuseStep 762967 = 1144451) B1144451
theorem B1614937 : Blo 634301 1614937 := bstep (se 2 (by rfl) ⟨605601, by rfl⟩ : syracuseStep 1614937 = 1211203) B1211203
theorem B41329925 : Blo 634301 41329925 := bstep (se 4 (by rfl) ⟨3874680, by rfl⟩ : syracuseStep 41329925 = 7749361) B7749361
theorem B2041139 : Blo 634301 2041139 := bstep (se 1 (by rfl) ⟨1530854, by rfl⟩ : syracuseStep 2041139 = 3061709) B3061709
theorem B3614017 : Blo 634301 3614017 := bstep (se 2 (by rfl) ⟨1355256, by rfl⟩ : syracuseStep 3614017 = 2710513) B2710513
theorem B4662593 : Blo 634301 4662593 := bstep (se 2 (by rfl) ⟨1748472, by rfl⟩ : syracuseStep 4662593 = 3496945) B3496945
theorem B2041291 : Blo 634301 2041291 := bstep (se 1 (by rfl) ⟨1530968, by rfl⟩ : syracuseStep 2041291 = 3061937) B3061937
theorem B1288075 : Blo 634301 1288075 := bstep (se 1 (by rfl) ⟨966056, by rfl⟩ : syracuseStep 1288075 = 1932113) B1932113
theorem B2762669 : Blo 634301 2762669 := bstep (se 3 (by rfl) ⟨518000, by rfl⟩ : syracuseStep 2762669 = 1036001) B1036001
theorem B2041793 : Blo 634301 2041793 := bstep (se 2 (by rfl) ⟨765672, by rfl⟩ : syracuseStep 2041793 = 1531345) B1531345
theorem B17410229 : Blo 634301 17410229 := bstep (se 5 (by rfl) ⟨816104, by rfl⟩ : syracuseStep 17410229 = 1632209) B1632209
theorem B4827437 : Blo 634301 4827437 := bstep (se 3 (by rfl) ⟨905144, by rfl⟩ : syracuseStep 4827437 = 1810289) B1810289
theorem B1812887 : Blo 634301 1812887 := bstep (se 1 (by rfl) ⟨1359665, by rfl⟩ : syracuseStep 1812887 = 2719331) B2719331
theorem B21146309 : Blo 634301 21146309 := bstep (se 4 (by rfl) ⟨1982466, by rfl⟩ : syracuseStep 21146309 = 3964933) B3964933
theorem B7744301 : Blo 634301 7744301 := bstep (se 3 (by rfl) ⟨1452056, by rfl⟩ : syracuseStep 7744301 = 2904113) B2904113
theorem B2763571 : Blo 634301 2763571 := bstep (se 1 (by rfl) ⟨2072678, by rfl⟩ : syracuseStep 2763571 = 4145357) B4145357
theorem B1715033 : Blo 634301 1715033 := bstep (se 2 (by rfl) ⟨643137, by rfl⟩ : syracuseStep 1715033 = 1286275) B1286275
theorem B3910493 : Blo 634301 3910493 := bstep (se 3 (by rfl) ⟨733217, by rfl⟩ : syracuseStep 3910493 = 1466435) B1466435
theorem B2894771 : Blo 634301 2894771 := bstep (se 1 (by rfl) ⟨2171078, by rfl⟩ : syracuseStep 2894771 = 4342157) B4342157
theorem B1715161 : Blo 634301 1715161 := bstep (se 2 (by rfl) ⟨643185, by rfl⟩ : syracuseStep 1715161 = 1286371) B1286371
theorem B2141207 : Blo 634301 2141207 := bstep (se 1 (by rfl) ⟨1605905, by rfl⟩ : syracuseStep 2141207 = 3211811) B3211811
theorem B634315 : Blo 634301 634315 := bstep (se 1 (by rfl) ⟨475736, by rfl⟩ : syracuseStep 634315 = 951473) B951473
theorem B634327 : Blo 634301 634327 := bstep (se 1 (by rfl) ⟨475745, by rfl⟩ : syracuseStep 634327 = 951491) B951491
theorem B634347 : Blo 634301 634347 := bstep (se 1 (by rfl) ⟨475760, by rfl⟩ : syracuseStep 634347 = 951521) B951521
theorem B634359 : Blo 634301 634359 := bstep (se 1 (by rfl) ⟨475769, by rfl⟩ : syracuseStep 634359 = 951539) B951539
theorem B634379 : Blo 634301 634379 := bstep (se 1 (by rfl) ⟨475784, by rfl⟩ : syracuseStep 634379 = 951569) B951569
theorem B634391 : Blo 634301 634391 := bstep (se 1 (by rfl) ⟨475793, by rfl⟩ : syracuseStep 634391 = 951587) B951587
theorem B634411 : Blo 634301 634411 := bstep (se 1 (by rfl) ⟨475808, by rfl⟩ : syracuseStep 634411 = 951617) B951617
theorem B2141747 : Blo 634301 2141747 := bstep (se 1 (by rfl) ⟨1606310, by rfl⟩ : syracuseStep 2141747 = 3212621) B3212621
theorem B634423 : Blo 634301 634423 := bstep (se 1 (by rfl) ⟨475817, by rfl⟩ : syracuseStep 634423 = 951635) B951635
theorem B634443 : Blo 634301 634443 := bstep (se 1 (by rfl) ⟨475832, by rfl⟩ : syracuseStep 634443 = 951665) B951665
theorem B634455 : Blo 634301 634455 := bstep (se 1 (by rfl) ⟨475841, by rfl⟩ : syracuseStep 634455 = 951683) B951683
theorem B634475 : Blo 634301 634475 := bstep (se 1 (by rfl) ⟨475856, by rfl⟩ : syracuseStep 634475 = 951713) B951713
theorem B634487 : Blo 634301 634487 := bstep (se 1 (by rfl) ⟨475865, by rfl⟩ : syracuseStep 634487 = 951731) B951731
theorem B634507 : Blo 634301 634507 := bstep (se 1 (by rfl) ⟨475880, by rfl⟩ : syracuseStep 634507 = 951761) B951761
theorem B634519 : Blo 634301 634519 := bstep (se 1 (by rfl) ⟨475889, by rfl⟩ : syracuseStep 634519 = 951779) B951779
theorem B3878551 : Blo 634301 3878551 := bstep (se 1 (by rfl) ⟨2908913, by rfl⟩ : syracuseStep 3878551 = 5817827) B5817827
theorem B634539 : Blo 634301 634539 := bstep (se 1 (by rfl) ⟨475904, by rfl⟩ : syracuseStep 634539 = 951809) B951809
theorem B634551 : Blo 634301 634551 := bstep (se 1 (by rfl) ⟨475913, by rfl⟩ : syracuseStep 634551 = 951827) B951827
theorem B634571 : Blo 634301 634571 := bstep (se 1 (by rfl) ⟨475928, by rfl⟩ : syracuseStep 634571 = 951857) B951857
theorem B634583 : Blo 634301 634583 := bstep (se 1 (by rfl) ⟨475937, by rfl⟩ : syracuseStep 634583 = 951875) B951875
theorem B634603 : Blo 634301 634603 := bstep (se 1 (by rfl) ⟨475952, by rfl⟩ : syracuseStep 634603 = 951905) B951905
theorem B634615 : Blo 634301 634615 := bstep (se 1 (by rfl) ⟨475961, by rfl⟩ : syracuseStep 634615 = 951923) B951923
theorem B634635 : Blo 634301 634635 := bstep (se 1 (by rfl) ⟨475976, by rfl⟩ : syracuseStep 634635 = 951953) B951953
theorem B3223313 : Blo 634301 3223313 := bstep (se 2 (by rfl) ⟨1208742, by rfl⟩ : syracuseStep 3223313 = 2417485) B2417485
theorem B634647 : Blo 634301 634647 := bstep (se 1 (by rfl) ⟨475985, by rfl⟩ : syracuseStep 634647 = 951971) B951971
theorem B634667 : Blo 634301 634667 := bstep (se 1 (by rfl) ⟨476000, by rfl⟩ : syracuseStep 634667 = 952001) B952001
theorem B634679 : Blo 634301 634679 := bstep (se 1 (by rfl) ⟨476009, by rfl⟩ : syracuseStep 634679 = 952019) B952019
theorem B2142017 : Blo 634301 2142017 := bstep (se 2 (by rfl) ⟨803256, by rfl⟩ : syracuseStep 2142017 = 1606513) B1606513
theorem B634699 : Blo 634301 634699 := bstep (se 1 (by rfl) ⟨476024, by rfl⟩ : syracuseStep 634699 = 952049) B952049
theorem B634711 : Blo 634301 634711 := bstep (se 1 (by rfl) ⟨476033, by rfl⟩ : syracuseStep 634711 = 952067) B952067
theorem B634731 : Blo 634301 634731 := bstep (se 1 (by rfl) ⟨476048, by rfl⟩ : syracuseStep 634731 = 952097) B952097
theorem B634743 : Blo 634301 634743 := bstep (se 1 (by rfl) ⟨476057, by rfl⟩ : syracuseStep 634743 = 952115) B952115
theorem B634763 : Blo 634301 634763 := bstep (se 1 (by rfl) ⟨476072, by rfl⟩ : syracuseStep 634763 = 952145) B952145
theorem B634775 : Blo 634301 634775 := bstep (se 1 (by rfl) ⟨476081, by rfl⟩ : syracuseStep 634775 = 952163) B952163
theorem B634795 : Blo 634301 634795 := bstep (se 1 (by rfl) ⟨476096, by rfl⟩ : syracuseStep 634795 = 952193) B952193
theorem B3223475 : Blo 634301 3223475 := bstep (se 1 (by rfl) ⟨2417606, by rfl⟩ : syracuseStep 3223475 = 4835213) B4835213
theorem B634807 : Blo 634301 634807 := bstep (se 1 (by rfl) ⟨476105, by rfl⟩ : syracuseStep 634807 = 952211) B952211
theorem B634827 : Blo 634301 634827 := bstep (se 1 (by rfl) ⟨476120, by rfl⟩ : syracuseStep 634827 = 952241) B952241
theorem B1355735 : Blo 634301 1355735 := bstep (se 1 (by rfl) ⟨1016801, by rfl⟩ : syracuseStep 1355735 = 2033603) B2033603
theorem B634839 : Blo 634301 634839 := bstep (se 1 (by rfl) ⟨476129, by rfl⟩ : syracuseStep 634839 = 952259) B952259
theorem B634859 : Blo 634301 634859 := bstep (se 1 (by rfl) ⟨476144, by rfl⟩ : syracuseStep 634859 = 952289) B952289
theorem B634871 : Blo 634301 634871 := bstep (se 1 (by rfl) ⟨476153, by rfl⟩ : syracuseStep 634871 = 952307) B952307
theorem B634891 : Blo 634301 634891 := bstep (se 1 (by rfl) ⟨476168, by rfl⟩ : syracuseStep 634891 = 952337) B952337
theorem B634903 : Blo 634301 634903 := bstep (se 1 (by rfl) ⟨476177, by rfl⟩ : syracuseStep 634903 = 952355) B952355
theorem B634923 : Blo 634301 634923 := bstep (se 1 (by rfl) ⟨476192, by rfl⟩ : syracuseStep 634923 = 952385) B952385
theorem B634935 : Blo 634301 634935 := bstep (se 1 (by rfl) ⟨476201, by rfl⟩ : syracuseStep 634935 = 952403) B952403
theorem B634955 : Blo 634301 634955 := bstep (se 1 (by rfl) ⟨476216, by rfl⟩ : syracuseStep 634955 = 952433) B952433
theorem B634967 : Blo 634301 634967 := bstep (se 1 (by rfl) ⟨476225, by rfl⟩ : syracuseStep 634967 = 952451) B952451
theorem B634987 : Blo 634301 634987 := bstep (se 1 (by rfl) ⟨476240, by rfl⟩ : syracuseStep 634987 = 952481) B952481
theorem B634999 : Blo 634301 634999 := bstep (se 1 (by rfl) ⟨476249, by rfl⟩ : syracuseStep 634999 = 952499) B952499
theorem B635019 : Blo 634301 635019 := bstep (se 1 (by rfl) ⟨476264, by rfl⟩ : syracuseStep 635019 = 952529) B952529
theorem B635031 : Blo 634301 635031 := bstep (se 1 (by rfl) ⟨476273, by rfl⟩ : syracuseStep 635031 = 952547) B952547
theorem B635051 : Blo 634301 635051 := bstep (se 1 (by rfl) ⟨476288, by rfl⟩ : syracuseStep 635051 = 952577) B952577
theorem B635063 : Blo 634301 635063 := bstep (se 1 (by rfl) ⟨476297, by rfl⟩ : syracuseStep 635063 = 952595) B952595
theorem B635083 : Blo 634301 635083 := bstep (se 1 (by rfl) ⟨476312, by rfl⟩ : syracuseStep 635083 = 952625) B952625
theorem B8171725 : Blo 634301 8171725 := bstep (se 3 (by rfl) ⟨1532198, by rfl⟩ : syracuseStep 8171725 = 3064397) B3064397
theorem B635095 : Blo 634301 635095 := bstep (se 1 (by rfl) ⟨476321, by rfl⟩ : syracuseStep 635095 = 952643) B952643
theorem B635115 : Blo 634301 635115 := bstep (se 1 (by rfl) ⟨476336, by rfl⟩ : syracuseStep 635115 = 952673) B952673
theorem B635127 : Blo 634301 635127 := bstep (se 1 (by rfl) ⟨476345, by rfl⟩ : syracuseStep 635127 = 952691) B952691
theorem B1356043 : Blo 634301 1356043 := bstep (se 1 (by rfl) ⟨1017032, by rfl⟩ : syracuseStep 1356043 = 2034065) B2034065
theorem B635147 : Blo 634301 635147 := bstep (se 1 (by rfl) ⟨476360, by rfl⟩ : syracuseStep 635147 = 952721) B952721
theorem B635159 : Blo 634301 635159 := bstep (se 1 (by rfl) ⟨476369, by rfl⟩ : syracuseStep 635159 = 952739) B952739
theorem B635179 : Blo 634301 635179 := bstep (se 1 (by rfl) ⟨476384, by rfl⟩ : syracuseStep 635179 = 952769) B952769
theorem B635191 : Blo 634301 635191 := bstep (se 1 (by rfl) ⟨476393, by rfl⟩ : syracuseStep 635191 = 952787) B952787
theorem B635211 : Blo 634301 635211 := bstep (se 1 (by rfl) ⟨476408, by rfl⟩ : syracuseStep 635211 = 952817) B952817
theorem B635223 : Blo 634301 635223 := bstep (se 1 (by rfl) ⟨476417, by rfl⟩ : syracuseStep 635223 = 952835) B952835
theorem B2142557 : Blo 634301 2142557 := bstep (se 3 (by rfl) ⟨401729, by rfl⟩ : syracuseStep 2142557 = 803459) B803459
theorem B2044253 : Blo 634301 2044253 := bstep (se 3 (by rfl) ⟨383297, by rfl⟩ : syracuseStep 2044253 = 766595) B766595
theorem B635243 : Blo 634301 635243 := bstep (se 1 (by rfl) ⟨476432, by rfl⟩ : syracuseStep 635243 = 952865) B952865
theorem B635255 : Blo 634301 635255 := bstep (se 1 (by rfl) ⟨476441, by rfl⟩ : syracuseStep 635255 = 952883) B952883
theorem B635275 : Blo 634301 635275 := bstep (se 1 (by rfl) ⟨476456, by rfl⟩ : syracuseStep 635275 = 952913) B952913
theorem B635287 : Blo 634301 635287 := bstep (se 1 (by rfl) ⟨476465, by rfl⟩ : syracuseStep 635287 = 952931) B952931
theorem B635307 : Blo 634301 635307 := bstep (se 1 (by rfl) ⟨476480, by rfl⟩ : syracuseStep 635307 = 952961) B952961
theorem B635319 : Blo 634301 635319 := bstep (se 1 (by rfl) ⟨476489, by rfl⟩ : syracuseStep 635319 = 952979) B952979
theorem B635339 : Blo 634301 635339 := bstep (se 1 (by rfl) ⟨476504, by rfl⟩ : syracuseStep 635339 = 953009) B953009
theorem B635351 : Blo 634301 635351 := bstep (se 1 (by rfl) ⟨476513, by rfl⟩ : syracuseStep 635351 = 953027) B953027
theorem B635371 : Blo 634301 635371 := bstep (se 1 (by rfl) ⟨476528, by rfl⟩ : syracuseStep 635371 = 953057) B953057
theorem B635383 : Blo 634301 635383 := bstep (se 1 (by rfl) ⟨476537, by rfl⟩ : syracuseStep 635383 = 953075) B953075
theorem B635403 : Blo 634301 635403 := bstep (se 1 (by rfl) ⟨476552, by rfl⟩ : syracuseStep 635403 = 953105) B953105
theorem B635415 : Blo 634301 635415 := bstep (se 1 (by rfl) ⟨476561, by rfl⟩ : syracuseStep 635415 = 953123) B953123
theorem B635435 : Blo 634301 635435 := bstep (se 1 (by rfl) ⟨476576, by rfl⟩ : syracuseStep 635435 = 953153) B953153
theorem B635447 : Blo 634301 635447 := bstep (se 1 (by rfl) ⟨476585, by rfl⟩ : syracuseStep 635447 = 953171) B953171
theorem B635467 : Blo 634301 635467 := bstep (se 1 (by rfl) ⟨476600, by rfl⟩ : syracuseStep 635467 = 953201) B953201
theorem B635479 : Blo 634301 635479 := bstep (se 1 (by rfl) ⟨476609, by rfl⟩ : syracuseStep 635479 = 953219) B953219
theorem B635499 : Blo 634301 635499 := bstep (se 1 (by rfl) ⟨476624, by rfl⟩ : syracuseStep 635499 = 953249) B953249
theorem B635511 : Blo 634301 635511 := bstep (se 1 (by rfl) ⟨476633, by rfl⟩ : syracuseStep 635511 = 953267) B953267
theorem B635531 : Blo 634301 635531 := bstep (se 1 (by rfl) ⟨476648, by rfl⟩ : syracuseStep 635531 = 953297) B953297
theorem B635543 : Blo 634301 635543 := bstep (se 1 (by rfl) ⟨476657, by rfl⟩ : syracuseStep 635543 = 953315) B953315
theorem B635563 : Blo 634301 635563 := bstep (se 1 (by rfl) ⟨476672, by rfl⟩ : syracuseStep 635563 = 953345) B953345
theorem B3617459 : Blo 634301 3617459 := bstep (se 1 (by rfl) ⟨2713094, by rfl⟩ : syracuseStep 3617459 = 5426189) B5426189
theorem B635575 : Blo 634301 635575 := bstep (se 1 (by rfl) ⟨476681, by rfl⟩ : syracuseStep 635575 = 953363) B953363
theorem B635595 : Blo 634301 635595 := bstep (se 1 (by rfl) ⟨476696, by rfl⟩ : syracuseStep 635595 = 953393) B953393
theorem B635607 : Blo 634301 635607 := bstep (se 1 (by rfl) ⟨476705, by rfl⟩ : syracuseStep 635607 = 953411) B953411
theorem B635627 : Blo 634301 635627 := bstep (se 1 (by rfl) ⟨476720, by rfl⟩ : syracuseStep 635627 = 953441) B953441
theorem B635639 : Blo 634301 635639 := bstep (se 1 (by rfl) ⟨476729, by rfl⟩ : syracuseStep 635639 = 953459) B953459
theorem B635659 : Blo 634301 635659 := bstep (se 1 (by rfl) ⟨476744, by rfl⟩ : syracuseStep 635659 = 953489) B953489
theorem B635671 : Blo 634301 635671 := bstep (se 1 (by rfl) ⟨476753, by rfl⟩ : syracuseStep 635671 = 953507) B953507
theorem B635691 : Blo 634301 635691 := bstep (se 1 (by rfl) ⟨476768, by rfl⟩ : syracuseStep 635691 = 953537) B953537
theorem B1815347 : Blo 634301 1815347 := bstep (se 1 (by rfl) ⟨1361510, by rfl⟩ : syracuseStep 1815347 = 2723021) B2723021
theorem B635703 : Blo 634301 635703 := bstep (se 1 (by rfl) ⟨476777, by rfl⟩ : syracuseStep 635703 = 953555) B953555
theorem B635723 : Blo 634301 635723 := bstep (se 1 (by rfl) ⟨476792, by rfl⟩ : syracuseStep 635723 = 953585) B953585
theorem B635735 : Blo 634301 635735 := bstep (se 1 (by rfl) ⟨476801, by rfl⟩ : syracuseStep 635735 = 953603) B953603
theorem B635755 : Blo 634301 635755 := bstep (se 1 (by rfl) ⟨476816, by rfl⟩ : syracuseStep 635755 = 953633) B953633
theorem B635767 : Blo 634301 635767 := bstep (se 1 (by rfl) ⟨476825, by rfl⟩ : syracuseStep 635767 = 953651) B953651
theorem B635787 : Blo 634301 635787 := bstep (se 1 (by rfl) ⟨476840, by rfl⟩ : syracuseStep 635787 = 953681) B953681
theorem B635799 : Blo 634301 635799 := bstep (se 1 (by rfl) ⟨476849, by rfl⟩ : syracuseStep 635799 = 953699) B953699
theorem B635819 : Blo 634301 635819 := bstep (se 1 (by rfl) ⟨476864, by rfl⟩ : syracuseStep 635819 = 953729) B953729
theorem B635831 : Blo 634301 635831 := bstep (se 1 (by rfl) ⟨476873, by rfl⟩ : syracuseStep 635831 = 953747) B953747
theorem B635851 : Blo 634301 635851 := bstep (se 1 (by rfl) ⟨476888, by rfl⟩ : syracuseStep 635851 = 953777) B953777
theorem B635863 : Blo 634301 635863 := bstep (se 1 (by rfl) ⟨476897, by rfl⟩ : syracuseStep 635863 = 953795) B953795
theorem B635883 : Blo 634301 635883 := bstep (se 1 (by rfl) ⟨476912, by rfl⟩ : syracuseStep 635883 = 953825) B953825
theorem B635895 : Blo 634301 635895 := bstep (se 1 (by rfl) ⟨476921, by rfl⟩ : syracuseStep 635895 = 953843) B953843
theorem B635915 : Blo 634301 635915 := bstep (se 1 (by rfl) ⟨476936, by rfl⟩ : syracuseStep 635915 = 953873) B953873
theorem B635927 : Blo 634301 635927 := bstep (se 1 (by rfl) ⟨476945, by rfl⟩ : syracuseStep 635927 = 953891) B953891
theorem B635947 : Blo 634301 635947 := bstep (se 1 (by rfl) ⟨476960, by rfl⟩ : syracuseStep 635947 = 953921) B953921
theorem B635959 : Blo 634301 635959 := bstep (se 1 (by rfl) ⟨476969, by rfl⟩ : syracuseStep 635959 = 953939) B953939
theorem B635979 : Blo 634301 635979 := bstep (se 1 (by rfl) ⟨476984, by rfl⟩ : syracuseStep 635979 = 953969) B953969
theorem B635991 : Blo 634301 635991 := bstep (se 1 (by rfl) ⟨476993, by rfl⟩ : syracuseStep 635991 = 953987) B953987
theorem B636011 : Blo 634301 636011 := bstep (se 1 (by rfl) ⟨477008, by rfl⟩ : syracuseStep 636011 = 954017) B954017
theorem B636023 : Blo 634301 636023 := bstep (se 1 (by rfl) ⟨477017, by rfl⟩ : syracuseStep 636023 = 954035) B954035
theorem B636043 : Blo 634301 636043 := bstep (se 1 (by rfl) ⟨477032, by rfl⟩ : syracuseStep 636043 = 954065) B954065
theorem B636055 : Blo 634301 636055 := bstep (se 1 (by rfl) ⟨477041, by rfl⟩ : syracuseStep 636055 = 954083) B954083
theorem B636075 : Blo 634301 636075 := bstep (se 1 (by rfl) ⟨477056, by rfl⟩ : syracuseStep 636075 = 954113) B954113
theorem B636087 : Blo 634301 636087 := bstep (se 1 (by rfl) ⟨477065, by rfl⟩ : syracuseStep 636087 = 954131) B954131
theorem B636107 : Blo 634301 636107 := bstep (se 1 (by rfl) ⟨477080, by rfl⟩ : syracuseStep 636107 = 954161) B954161
theorem B636119 : Blo 634301 636119 := bstep (se 1 (by rfl) ⟨477089, by rfl⟩ : syracuseStep 636119 = 954179) B954179
theorem B636139 : Blo 634301 636139 := bstep (se 1 (by rfl) ⟨477104, by rfl⟩ : syracuseStep 636139 = 954209) B954209
theorem B636151 : Blo 634301 636151 := bstep (se 1 (by rfl) ⟨477113, by rfl⟩ : syracuseStep 636151 = 954227) B954227
theorem B636171 : Blo 634301 636171 := bstep (se 1 (by rfl) ⟨477128, by rfl⟩ : syracuseStep 636171 = 954257) B954257
theorem B636183 : Blo 634301 636183 := bstep (se 1 (by rfl) ⟨477137, by rfl⟩ : syracuseStep 636183 = 954275) B954275
theorem B636203 : Blo 634301 636203 := bstep (se 1 (by rfl) ⟨477152, by rfl⟩ : syracuseStep 636203 = 954305) B954305
theorem B636215 : Blo 634301 636215 := bstep (se 1 (by rfl) ⟨477161, by rfl⟩ : syracuseStep 636215 = 954323) B954323
theorem B636235 : Blo 634301 636235 := bstep (se 1 (by rfl) ⟨477176, by rfl⟩ : syracuseStep 636235 = 954353) B954353
theorem B636247 : Blo 634301 636247 := bstep (se 1 (by rfl) ⟨477185, by rfl⟩ : syracuseStep 636247 = 954371) B954371
theorem B636267 : Blo 634301 636267 := bstep (se 1 (by rfl) ⟨477200, by rfl⟩ : syracuseStep 636267 = 954401) B954401
theorem B636279 : Blo 634301 636279 := bstep (se 1 (by rfl) ⟨477209, by rfl⟩ : syracuseStep 636279 = 954419) B954419
theorem B636299 : Blo 634301 636299 := bstep (se 1 (by rfl) ⟨477224, by rfl⟩ : syracuseStep 636299 = 954449) B954449
theorem B636311 : Blo 634301 636311 := bstep (se 1 (by rfl) ⟨477233, by rfl⟩ : syracuseStep 636311 = 954467) B954467
theorem B636331 : Blo 634301 636331 := bstep (se 1 (by rfl) ⟨477248, by rfl⟩ : syracuseStep 636331 = 954497) B954497
theorem B636343 : Blo 634301 636343 := bstep (se 1 (by rfl) ⟨477257, by rfl⟩ : syracuseStep 636343 = 954515) B954515
theorem B2143691 : Blo 634301 2143691 := bstep (se 1 (by rfl) ⟨1607768, by rfl⟩ : syracuseStep 2143691 = 3215537) B3215537
theorem B636363 : Blo 634301 636363 := bstep (se 1 (by rfl) ⟨477272, by rfl⟩ : syracuseStep 636363 = 954545) B954545
theorem B636375 : Blo 634301 636375 := bstep (se 1 (by rfl) ⟨477281, by rfl⟩ : syracuseStep 636375 = 954563) B954563
theorem B1357273 : Blo 634301 1357273 := bstep (se 2 (by rfl) ⟨508977, by rfl⟩ : syracuseStep 1357273 = 1017955) B1017955
theorem B636395 : Blo 634301 636395 := bstep (se 1 (by rfl) ⟨477296, by rfl⟩ : syracuseStep 636395 = 954593) B954593
theorem B636407 : Blo 634301 636407 := bstep (se 1 (by rfl) ⟨477305, by rfl⟩ : syracuseStep 636407 = 954611) B954611
theorem B636427 : Blo 634301 636427 := bstep (se 1 (by rfl) ⟨477320, by rfl⟩ : syracuseStep 636427 = 954641) B954641
theorem B636439 : Blo 634301 636439 := bstep (se 1 (by rfl) ⟨477329, by rfl⟩ : syracuseStep 636439 = 954659) B954659
theorem B636459 : Blo 634301 636459 := bstep (se 1 (by rfl) ⟨477344, by rfl⟩ : syracuseStep 636459 = 954689) B954689
theorem B636471 : Blo 634301 636471 := bstep (se 1 (by rfl) ⟨477353, by rfl⟩ : syracuseStep 636471 = 954707) B954707
theorem B636491 : Blo 634301 636491 := bstep (se 1 (by rfl) ⟨477368, by rfl⟩ : syracuseStep 636491 = 954737) B954737
theorem B636503 : Blo 634301 636503 := bstep (se 1 (by rfl) ⟨477377, by rfl⟩ : syracuseStep 636503 = 954755) B954755
theorem B636523 : Blo 634301 636523 := bstep (se 1 (by rfl) ⟨477392, by rfl⟩ : syracuseStep 636523 = 954785) B954785
theorem B636535 : Blo 634301 636535 := bstep (se 1 (by rfl) ⟨477401, by rfl⟩ : syracuseStep 636535 = 954803) B954803
theorem B636555 : Blo 634301 636555 := bstep (se 1 (by rfl) ⟨477416, by rfl⟩ : syracuseStep 636555 = 954833) B954833
theorem B636567 : Blo 634301 636567 := bstep (se 1 (by rfl) ⟨477425, by rfl⟩ : syracuseStep 636567 = 954851) B954851
theorem B636587 : Blo 634301 636587 := bstep (se 1 (by rfl) ⟨477440, by rfl⟩ : syracuseStep 636587 = 954881) B954881
theorem B636599 : Blo 634301 636599 := bstep (se 1 (by rfl) ⟨477449, by rfl⟩ : syracuseStep 636599 = 954899) B954899
theorem B636619 : Blo 634301 636619 := bstep (se 1 (by rfl) ⟨477464, by rfl⟩ : syracuseStep 636619 = 954929) B954929
theorem B636631 : Blo 634301 636631 := bstep (se 1 (by rfl) ⟨477473, by rfl⟩ : syracuseStep 636631 = 954947) B954947
theorem B2143961 : Blo 634301 2143961 := bstep (se 2 (by rfl) ⟨803985, by rfl⟩ : syracuseStep 2143961 = 1607971) B1607971
theorem B636651 : Blo 634301 636651 := bstep (se 1 (by rfl) ⟨477488, by rfl⟩ : syracuseStep 636651 = 954977) B954977
theorem B636663 : Blo 634301 636663 := bstep (se 1 (by rfl) ⟨477497, by rfl⟩ : syracuseStep 636663 = 954995) B954995
theorem B636683 : Blo 634301 636683 := bstep (se 1 (by rfl) ⟨477512, by rfl⟩ : syracuseStep 636683 = 955025) B955025
theorem B636695 : Blo 634301 636695 := bstep (se 1 (by rfl) ⟨477521, by rfl⟩ : syracuseStep 636695 = 955043) B955043
theorem B636715 : Blo 634301 636715 := bstep (se 1 (by rfl) ⟨477536, by rfl⟩ : syracuseStep 636715 = 955073) B955073
theorem B636727 : Blo 634301 636727 := bstep (se 1 (by rfl) ⟨477545, by rfl⟩ : syracuseStep 636727 = 955091) B955091
theorem B636747 : Blo 634301 636747 := bstep (se 1 (by rfl) ⟨477560, by rfl⟩ : syracuseStep 636747 = 955121) B955121
theorem B3225419 : Blo 634301 3225419 := bstep (se 1 (by rfl) ⟨2419064, by rfl⟩ : syracuseStep 3225419 = 4838129) B4838129
theorem B636759 : Blo 634301 636759 := bstep (se 1 (by rfl) ⟨477569, by rfl⟩ : syracuseStep 636759 = 955139) B955139
theorem B636779 : Blo 634301 636779 := bstep (se 1 (by rfl) ⟨477584, by rfl⟩ : syracuseStep 636779 = 955169) B955169
theorem B636791 : Blo 634301 636791 := bstep (se 1 (by rfl) ⟨477593, by rfl⟩ : syracuseStep 636791 = 955187) B955187
theorem B636811 : Blo 634301 636811 := bstep (se 1 (by rfl) ⟨477608, by rfl⟩ : syracuseStep 636811 = 955217) B955217
theorem B636823 : Blo 634301 636823 := bstep (se 1 (by rfl) ⟨477617, by rfl⟩ : syracuseStep 636823 = 955235) B955235
theorem B636843 : Blo 634301 636843 := bstep (se 1 (by rfl) ⟨477632, by rfl⟩ : syracuseStep 636843 = 955265) B955265
theorem B636855 : Blo 634301 636855 := bstep (se 1 (by rfl) ⟨477641, by rfl⟩ : syracuseStep 636855 = 955283) B955283
theorem B636875 : Blo 634301 636875 := bstep (se 1 (by rfl) ⟨477656, by rfl⟩ : syracuseStep 636875 = 955313) B955313
theorem B636887 : Blo 634301 636887 := bstep (se 1 (by rfl) ⟨477665, by rfl⟩ : syracuseStep 636887 = 955331) B955331
theorem B636907 : Blo 634301 636907 := bstep (se 1 (by rfl) ⟨477680, by rfl⟩ : syracuseStep 636907 = 955361) B955361
theorem B636919 : Blo 634301 636919 := bstep (se 1 (by rfl) ⟨477689, by rfl⟩ : syracuseStep 636919 = 955379) B955379
theorem B636939 : Blo 634301 636939 := bstep (se 1 (by rfl) ⟨477704, by rfl⟩ : syracuseStep 636939 = 955409) B955409
theorem B636951 : Blo 634301 636951 := bstep (se 1 (by rfl) ⟨477713, by rfl⟩ : syracuseStep 636951 = 955427) B955427
theorem B636971 : Blo 634301 636971 := bstep (se 1 (by rfl) ⟨477728, by rfl⟩ : syracuseStep 636971 = 955457) B955457
theorem B636983 : Blo 634301 636983 := bstep (se 1 (by rfl) ⟨477737, by rfl⟩ : syracuseStep 636983 = 955475) B955475
theorem B637003 : Blo 634301 637003 := bstep (se 1 (by rfl) ⟨477752, by rfl⟩ : syracuseStep 637003 = 955505) B955505
theorem B637015 : Blo 634301 637015 := bstep (se 1 (by rfl) ⟨477761, by rfl⟩ : syracuseStep 637015 = 955523) B955523
theorem B4831325 : Blo 634301 4831325 := bstep (se 3 (by rfl) ⟨905873, by rfl⟩ : syracuseStep 4831325 = 1811747) B1811747
theorem B3618917 : Blo 634301 3618917 := bstep (se 4 (by rfl) ⟨339273, by rfl⟩ : syracuseStep 3618917 = 678547) B678547
theorem B637035 : Blo 634301 637035 := bstep (se 1 (by rfl) ⟨477776, by rfl⟩ : syracuseStep 637035 = 955553) B955553
theorem B637047 : Blo 634301 637047 := bstep (se 1 (by rfl) ⟨477785, by rfl⟩ : syracuseStep 637047 = 955571) B955571
theorem B637067 : Blo 634301 637067 := bstep (se 1 (by rfl) ⟨477800, by rfl⟩ : syracuseStep 637067 = 955601) B955601
theorem B637079 : Blo 634301 637079 := bstep (se 1 (by rfl) ⟨477809, by rfl⟩ : syracuseStep 637079 = 955619) B955619
theorem B2209943 : Blo 634301 2209943 := bstep (se 1 (by rfl) ⟨1657457, by rfl⟩ : syracuseStep 2209943 = 3314915) B3314915
theorem B637099 : Blo 634301 637099 := bstep (se 1 (by rfl) ⟨477824, by rfl⟩ : syracuseStep 637099 = 955649) B955649
theorem B637111 : Blo 634301 637111 := bstep (se 1 (by rfl) ⟨477833, by rfl⟩ : syracuseStep 637111 = 955667) B955667
theorem B637131 : Blo 634301 637131 := bstep (se 1 (by rfl) ⟨477848, by rfl⟩ : syracuseStep 637131 = 955697) B955697
theorem B637143 : Blo 634301 637143 := bstep (se 1 (by rfl) ⟨477857, by rfl⟩ : syracuseStep 637143 = 955715) B955715
theorem B637163 : Blo 634301 637163 := bstep (se 1 (by rfl) ⟨477872, by rfl⟩ : syracuseStep 637163 = 955745) B955745
theorem B637175 : Blo 634301 637175 := bstep (se 1 (by rfl) ⟨477881, by rfl⟩ : syracuseStep 637175 = 955763) B955763
theorem B637195 : Blo 634301 637195 := bstep (se 1 (by rfl) ⟨477896, by rfl⟩ : syracuseStep 637195 = 955793) B955793
theorem B637207 : Blo 634301 637207 := bstep (se 1 (by rfl) ⟨477905, by rfl⟩ : syracuseStep 637207 = 955811) B955811
theorem B964889 : Blo 634301 964889 := bstep (se 2 (by rfl) ⟨361833, by rfl⟩ : syracuseStep 964889 = 723667) B723667
theorem B637227 : Blo 634301 637227 := bstep (se 1 (by rfl) ⟨477920, by rfl⟩ : syracuseStep 637227 = 955841) B955841
theorem B637239 : Blo 634301 637239 := bstep (se 1 (by rfl) ⟨477929, by rfl⟩ : syracuseStep 637239 = 955859) B955859
theorem B637259 : Blo 634301 637259 := bstep (se 1 (by rfl) ⟨477944, by rfl⟩ : syracuseStep 637259 = 955889) B955889
theorem B637271 : Blo 634301 637271 := bstep (se 1 (by rfl) ⟨477953, by rfl⟩ : syracuseStep 637271 = 955907) B955907
theorem B637291 : Blo 634301 637291 := bstep (se 1 (by rfl) ⟨477968, by rfl⟩ : syracuseStep 637291 = 955937) B955937
theorem B637303 : Blo 634301 637303 := bstep (se 1 (by rfl) ⟨477977, by rfl⟩ : syracuseStep 637303 = 955955) B955955
theorem B637323 : Blo 634301 637323 := bstep (se 1 (by rfl) ⟨477992, by rfl⟩ : syracuseStep 637323 = 955985) B955985
theorem B2144663 : Blo 634301 2144663 := bstep (se 1 (by rfl) ⟨1608497, by rfl⟩ : syracuseStep 2144663 = 3216995) B3216995
theorem B637335 : Blo 634301 637335 := bstep (se 1 (by rfl) ⟨478001, by rfl⟩ : syracuseStep 637335 = 956003) B956003
theorem B637355 : Blo 634301 637355 := bstep (se 1 (by rfl) ⟨478016, by rfl⟩ : syracuseStep 637355 = 956033) B956033
theorem B1718707 : Blo 634301 1718707 := bstep (se 1 (by rfl) ⟨1289030, by rfl⟩ : syracuseStep 1718707 = 2578061) B2578061
theorem B637367 : Blo 634301 637367 := bstep (se 1 (by rfl) ⟨478025, by rfl⟩ : syracuseStep 637367 = 956051) B956051
theorem B637387 : Blo 634301 637387 := bstep (se 1 (by rfl) ⟨478040, by rfl⟩ : syracuseStep 637387 = 956081) B956081
theorem B637399 : Blo 634301 637399 := bstep (se 1 (by rfl) ⟨478049, by rfl⟩ : syracuseStep 637399 = 956099) B956099
theorem B1292761 : Blo 634301 1292761 := bstep (se 2 (by rfl) ⟨484785, by rfl⟩ : syracuseStep 1292761 = 969571) B969571
theorem B637419 : Blo 634301 637419 := bstep (se 1 (by rfl) ⟨478064, by rfl⟩ : syracuseStep 637419 = 956129) B956129
theorem B637431 : Blo 634301 637431 := bstep (se 1 (by rfl) ⟨478073, by rfl⟩ : syracuseStep 637431 = 956147) B956147
theorem B637451 : Blo 634301 637451 := bstep (se 1 (by rfl) ⟨478088, by rfl⟩ : syracuseStep 637451 = 956177) B956177
theorem B637463 : Blo 634301 637463 := bstep (se 1 (by rfl) ⟨478097, by rfl⟩ : syracuseStep 637463 = 956195) B956195
theorem B637483 : Blo 634301 637483 := bstep (se 1 (by rfl) ⟨478112, by rfl⟩ : syracuseStep 637483 = 956225) B956225
theorem B637495 : Blo 634301 637495 := bstep (se 1 (by rfl) ⟨478121, by rfl⟩ : syracuseStep 637495 = 956243) B956243
theorem B2898497 : Blo 634301 2898497 := bstep (se 2 (by rfl) ⟨1086936, by rfl⟩ : syracuseStep 2898497 = 2173873) B2173873
theorem B4340299 : Blo 634301 4340299 := bstep (se 1 (by rfl) ⟨3255224, by rfl⟩ : syracuseStep 4340299 = 6510449) B6510449
theorem B637515 : Blo 634301 637515 := bstep (se 1 (by rfl) ⟨478136, by rfl⟩ : syracuseStep 637515 = 956273) B956273
theorem B637527 : Blo 634301 637527 := bstep (se 1 (by rfl) ⟨478145, by rfl⟩ : syracuseStep 637527 = 956291) B956291
theorem B637547 : Blo 634301 637547 := bstep (se 1 (by rfl) ⟨478160, by rfl⟩ : syracuseStep 637547 = 956321) B956321
theorem B637559 : Blo 634301 637559 := bstep (se 1 (by rfl) ⟨478169, by rfl⟩ : syracuseStep 637559 = 956339) B956339
theorem B637579 : Blo 634301 637579 := bstep (se 1 (by rfl) ⟨478184, by rfl⟩ : syracuseStep 637579 = 956369) B956369
theorem B637591 : Blo 634301 637591 := bstep (se 1 (by rfl) ⟨478193, by rfl⟩ : syracuseStep 637591 = 956387) B956387
theorem B6896279 : Blo 634301 6896279 := bstep (se 1 (by rfl) ⟨5172209, by rfl⟩ : syracuseStep 6896279 = 10344419) B10344419
theorem B637611 : Blo 634301 637611 := bstep (se 1 (by rfl) ⟨478208, by rfl⟩ : syracuseStep 637611 = 956417) B956417
theorem B637623 : Blo 634301 637623 := bstep (se 1 (by rfl) ⟨478217, by rfl⟩ : syracuseStep 637623 = 956435) B956435
theorem B637643 : Blo 634301 637643 := bstep (se 1 (by rfl) ⟨478232, by rfl⟩ : syracuseStep 637643 = 956465) B956465
theorem B637655 : Blo 634301 637655 := bstep (se 1 (by rfl) ⟨478241, by rfl⟩ : syracuseStep 637655 = 956483) B956483
theorem B637675 : Blo 634301 637675 := bstep (se 1 (by rfl) ⟨478256, by rfl⟩ : syracuseStep 637675 = 956513) B956513
theorem B637687 : Blo 634301 637687 := bstep (se 1 (by rfl) ⟨478265, by rfl⟩ : syracuseStep 637687 = 956531) B956531
theorem B637707 : Blo 634301 637707 := bstep (se 1 (by rfl) ⟨478280, by rfl⟩ : syracuseStep 637707 = 956561) B956561
theorem B637719 : Blo 634301 637719 := bstep (se 1 (by rfl) ⟨478289, by rfl⟩ : syracuseStep 637719 = 956579) B956579
theorem B637739 : Blo 634301 637739 := bstep (se 1 (by rfl) ⟨478304, by rfl⟩ : syracuseStep 637739 = 956609) B956609
theorem B637751 : Blo 634301 637751 := bstep (se 1 (by rfl) ⟨478313, by rfl⟩ : syracuseStep 637751 = 956627) B956627
theorem B1260353 : Blo 634301 1260353 := bstep (se 2 (by rfl) ⟨472632, by rfl⟩ : syracuseStep 1260353 = 945265) B945265
theorem B637771 : Blo 634301 637771 := bstep (se 1 (by rfl) ⟨478328, by rfl⟩ : syracuseStep 637771 = 956657) B956657
theorem B637783 : Blo 634301 637783 := bstep (se 1 (by rfl) ⟨478337, by rfl⟩ : syracuseStep 637783 = 956675) B956675
theorem B637803 : Blo 634301 637803 := bstep (se 1 (by rfl) ⟨478352, by rfl⟩ : syracuseStep 637803 = 956705) B956705
theorem B637815 : Blo 634301 637815 := bstep (se 1 (by rfl) ⟨478361, by rfl⟩ : syracuseStep 637815 = 956723) B956723
theorem B637835 : Blo 634301 637835 := bstep (se 1 (by rfl) ⟨478376, by rfl⟩ : syracuseStep 637835 = 956753) B956753
theorem B637847 : Blo 634301 637847 := bstep (se 1 (by rfl) ⟨478385, by rfl⟩ : syracuseStep 637847 = 956771) B956771
theorem B637867 : Blo 634301 637867 := bstep (se 1 (by rfl) ⟨478400, by rfl⟩ : syracuseStep 637867 = 956801) B956801
theorem B2145203 : Blo 634301 2145203 := bstep (se 1 (by rfl) ⟨1608902, by rfl⟩ : syracuseStep 2145203 = 3217805) B3217805
theorem B637879 : Blo 634301 637879 := bstep (se 1 (by rfl) ⟨478409, by rfl⟩ : syracuseStep 637879 = 956819) B956819
theorem B637899 : Blo 634301 637899 := bstep (se 1 (by rfl) ⟨478424, by rfl⟩ : syracuseStep 637899 = 956849) B956849
theorem B637911 : Blo 634301 637911 := bstep (se 1 (by rfl) ⟨478433, by rfl⟩ : syracuseStep 637911 = 956867) B956867
theorem B637931 : Blo 634301 637931 := bstep (se 1 (by rfl) ⟨478448, by rfl⟩ : syracuseStep 637931 = 956897) B956897
theorem B637943 : Blo 634301 637943 := bstep (se 1 (by rfl) ⟨478457, by rfl⟩ : syracuseStep 637943 = 956915) B956915
theorem B637963 : Blo 634301 637963 := bstep (se 1 (by rfl) ⟨478472, by rfl⟩ : syracuseStep 637963 = 956945) B956945
theorem B637975 : Blo 634301 637975 := bstep (se 1 (by rfl) ⟨478481, by rfl⟩ : syracuseStep 637975 = 956963) B956963
theorem B637995 : Blo 634301 637995 := bstep (se 1 (by rfl) ⟨478496, by rfl⟩ : syracuseStep 637995 = 956993) B956993
theorem B638007 : Blo 634301 638007 := bstep (se 1 (by rfl) ⟨478505, by rfl⟩ : syracuseStep 638007 = 957011) B957011
theorem B638027 : Blo 634301 638027 := bstep (se 1 (by rfl) ⟨478520, by rfl⟩ : syracuseStep 638027 = 957041) B957041
theorem B638039 : Blo 634301 638039 := bstep (se 1 (by rfl) ⟨478529, by rfl⟩ : syracuseStep 638039 = 957059) B957059
theorem B638059 : Blo 634301 638059 := bstep (se 1 (by rfl) ⟨478544, by rfl⟩ : syracuseStep 638059 = 957089) B957089
theorem B638071 : Blo 634301 638071 := bstep (se 1 (by rfl) ⟨478553, by rfl⟩ : syracuseStep 638071 = 957107) B957107
theorem B638091 : Blo 634301 638091 := bstep (se 1 (by rfl) ⟨478568, by rfl⟩ : syracuseStep 638091 = 957137) B957137
theorem B638103 : Blo 634301 638103 := bstep (se 1 (by rfl) ⟨478577, by rfl⟩ : syracuseStep 638103 = 957155) B957155
theorem B638123 : Blo 634301 638123 := bstep (se 1 (by rfl) ⟨478592, by rfl⟩ : syracuseStep 638123 = 957185) B957185
theorem B638135 : Blo 634301 638135 := bstep (se 1 (by rfl) ⟨478601, by rfl⟩ : syracuseStep 638135 = 957203) B957203
theorem B2145473 : Blo 634301 2145473 := bstep (se 2 (by rfl) ⟨804552, by rfl⟩ : syracuseStep 2145473 = 1609105) B1609105
theorem B638155 : Blo 634301 638155 := bstep (se 1 (by rfl) ⟨478616, by rfl⟩ : syracuseStep 638155 = 957233) B957233
theorem B638167 : Blo 634301 638167 := bstep (se 1 (by rfl) ⟨478625, by rfl⟩ : syracuseStep 638167 = 957251) B957251
theorem B638187 : Blo 634301 638187 := bstep (se 1 (by rfl) ⟨478640, by rfl⟩ : syracuseStep 638187 = 957281) B957281
theorem B638199 : Blo 634301 638199 := bstep (se 1 (by rfl) ⟨478649, by rfl⟩ : syracuseStep 638199 = 957299) B957299
theorem B638219 : Blo 634301 638219 := bstep (se 1 (by rfl) ⟨478664, by rfl⟩ : syracuseStep 638219 = 957329) B957329
theorem B638231 : Blo 634301 638231 := bstep (se 1 (by rfl) ⟨478673, by rfl⟩ : syracuseStep 638231 = 957347) B957347
theorem B638251 : Blo 634301 638251 := bstep (se 1 (by rfl) ⟨478688, by rfl⟩ : syracuseStep 638251 = 957377) B957377
theorem B638263 : Blo 634301 638263 := bstep (se 1 (by rfl) ⟨478697, by rfl⟩ : syracuseStep 638263 = 957395) B957395
theorem B638283 : Blo 634301 638283 := bstep (se 1 (by rfl) ⟨478712, by rfl⟩ : syracuseStep 638283 = 957425) B957425
theorem B638295 : Blo 634301 638295 := bstep (se 1 (by rfl) ⟨478721, by rfl⟩ : syracuseStep 638295 = 957443) B957443
theorem B3227201 : Blo 634301 3227201 := bstep (se 2 (by rfl) ⟨1210200, by rfl⟩ : syracuseStep 3227201 = 2420401) B2420401
theorem B1293889 : Blo 634301 1293889 := bstep (se 2 (by rfl) ⟨485208, by rfl⟩ : syracuseStep 1293889 = 970417) B970417
theorem B966233 : Blo 634301 966233 := bstep (se 2 (by rfl) ⟨362337, by rfl⟩ : syracuseStep 966233 = 724675) B724675
theorem B2146013 : Blo 634301 2146013 := bstep (se 3 (by rfl) ⟨402377, by rfl⟩ : syracuseStep 2146013 = 804755) B804755
theorem B3489581 : Blo 634301 3489581 := bstep (se 3 (by rfl) ⟨654296, by rfl⟩ : syracuseStep 3489581 = 1308593) B1308593
theorem B1360307 : Blo 634301 1360307 := bstep (se 1 (by rfl) ⟨1020230, by rfl⟩ : syracuseStep 1360307 = 2040461) B2040461
theorem B803287 : Blo 634301 803287 := bstep (se 1 (by rfl) ⟨602465, by rfl⟩ : syracuseStep 803287 = 1204931) B1204931
theorem B2409011 : Blo 634301 2409011 := bstep (se 1 (by rfl) ⟨1806758, by rfl⟩ : syracuseStep 2409011 = 3613517) B3613517
theorem B1393355 : Blo 634301 1393355 := bstep (se 1 (by rfl) ⟨1045016, by rfl⟩ : syracuseStep 1393355 = 2090033) B2090033
theorem B2147147 : Blo 634301 2147147 := bstep (se 1 (by rfl) ⟨1610360, by rfl⟩ : syracuseStep 2147147 = 3220721) B3220721
theorem B1360793 : Blo 634301 1360793 := bstep (se 2 (by rfl) ⟨510297, by rfl⟩ : syracuseStep 1360793 = 1020595) B1020595
theorem B9159749 : Blo 634301 9159749 := bstep (se 4 (by rfl) ⟨858726, by rfl⟩ : syracuseStep 9159749 = 1717453) B1717453
theorem B2147417 : Blo 634301 2147417 := bstep (se 2 (by rfl) ⟨805281, by rfl⟩ : syracuseStep 2147417 = 1610563) B1610563
theorem B3720293 : Blo 634301 3720293 := bstep (se 4 (by rfl) ⟨348777, by rfl⟩ : syracuseStep 3720293 = 697555) B697555
theorem B804107 : Blo 634301 804107 := bstep (se 1 (by rfl) ⟨603080, by rfl⟩ : syracuseStep 804107 = 1206161) B1206161
theorem B2901341 : Blo 634301 2901341 := bstep (se 3 (by rfl) ⟨544001, by rfl⟩ : syracuseStep 2901341 = 1088003) B1088003
theorem B3229145 : Blo 634301 3229145 := bstep (se 2 (by rfl) ⟨1210929, by rfl⟩ : syracuseStep 3229145 = 2421859) B2421859
theorem B1492619 : Blo 634301 1492619 := bstep (se 1 (by rfl) ⟨1119464, by rfl⟩ : syracuseStep 1492619 = 2238929) B2238929
theorem B1427201 : Blo 634301 1427201 := bstep (se 2 (by rfl) ⟨535200, by rfl⟩ : syracuseStep 1427201 = 1070401) B1070401
theorem B2148119 : Blo 634301 2148119 := bstep (se 1 (by rfl) ⟨1611089, by rfl⟩ : syracuseStep 2148119 = 3222179) B3222179
theorem B1525655 : Blo 634301 1525655 := bstep (se 1 (by rfl) ⟨1144241, by rfl⟩ : syracuseStep 1525655 = 2288483) B2288483
theorem B804811 : Blo 634301 804811 := bstep (se 1 (by rfl) ⟨603608, by rfl⟩ : syracuseStep 804811 = 1207217) B1207217
theorem B1427417 : Blo 634301 1427417 := bstep (se 2 (by rfl) ⟨535281, by rfl⟩ : syracuseStep 1427417 = 1070563) B1070563
theorem B2934749 : Blo 634301 2934749 := bstep (se 3 (by rfl) ⟨550265, by rfl⟩ : syracuseStep 2934749 = 1100531) B1100531
theorem B2410499 : Blo 634301 2410499 := bstep (se 1 (by rfl) ⟨1807874, by rfl⟩ : syracuseStep 2410499 = 3615749) B3615749
theorem B1427507 : Blo 634301 1427507 := bstep (se 1 (by rfl) ⟨1070630, by rfl⟩ : syracuseStep 1427507 = 2141261) B2141261
theorem B1427543 : Blo 634301 1427543 := bstep (se 1 (by rfl) ⟨1070657, by rfl⟩ : syracuseStep 1427543 = 2141315) B2141315
theorem B805079 : Blo 634301 805079 := bstep (se 1 (by rfl) ⟨603809, by rfl⟩ : syracuseStep 805079 = 1207619) B1207619
theorem B1427723 : Blo 634301 1427723 := bstep (se 1 (by rfl) ⟨1070792, by rfl⟩ : syracuseStep 1427723 = 2141585) B2141585
theorem B2148659 : Blo 634301 2148659 := bstep (se 1 (by rfl) ⟨1611494, by rfl⟩ : syracuseStep 2148659 = 3222989) B3222989
theorem B1427777 : Blo 634301 1427777 := bstep (se 2 (by rfl) ⟨535416, by rfl⟩ : syracuseStep 1427777 = 1070833) B1070833
theorem B4082021 : Blo 634301 4082021 := bstep (se 4 (by rfl) ⟨382689, by rfl⟩ : syracuseStep 4082021 = 765379) B765379
theorem B2410955 : Blo 634301 2410955 := bstep (se 1 (by rfl) ⟨1808216, by rfl⟩ : syracuseStep 2410955 = 3616433) B3616433
theorem B903641 : Blo 634301 903641 := bstep (se 2 (by rfl) ⟨338865, by rfl⟩ : syracuseStep 903641 = 677731) B677731
theorem B1362433 : Blo 634301 1362433 := bstep (se 2 (by rfl) ⟨510912, by rfl⟩ : syracuseStep 1362433 = 1021825) B1021825
theorem B1427993 : Blo 634301 1427993 := bstep (se 2 (by rfl) ⟨535497, by rfl⟩ : syracuseStep 1427993 = 1070995) B1070995
theorem B2148929 : Blo 634301 2148929 := bstep (se 2 (by rfl) ⟨805848, by rfl⟩ : syracuseStep 2148929 = 1611697) B1611697
theorem B903755 : Blo 634301 903755 := bstep (se 1 (by rfl) ⟨677816, by rfl⟩ : syracuseStep 903755 = 1355633) B1355633
theorem B1428083 : Blo 634301 1428083 := bstep (se 1 (by rfl) ⟨1071062, by rfl⟩ : syracuseStep 1428083 = 2142125) B2142125
theorem B2411153 : Blo 634301 2411153 := bstep (se 2 (by rfl) ⟨904182, by rfl⟩ : syracuseStep 2411153 = 1808365) B1808365
theorem B1428119 : Blo 634301 1428119 := bstep (se 1 (by rfl) ⟨1071089, by rfl⟩ : syracuseStep 1428119 = 2142179) B2142179
theorem B1428299 : Blo 634301 1428299 := bstep (se 1 (by rfl) ⟨1071224, by rfl⟩ : syracuseStep 1428299 = 2142449) B2142449
theorem B1428353 : Blo 634301 1428353 := bstep (se 2 (by rfl) ⟨535632, by rfl⟩ : syracuseStep 1428353 = 1071265) B1071265
theorem B805783 : Blo 634301 805783 := bstep (se 1 (by rfl) ⟨604337, by rfl⟩ : syracuseStep 805783 = 1208675) B1208675
theorem B1723315 : Blo 634301 1723315 := bstep (se 1 (by rfl) ⟨1292486, by rfl⟩ : syracuseStep 1723315 = 2584973) B2584973
theorem B3230765 : Blo 634301 3230765 := bstep (se 3 (by rfl) ⟨605768, by rfl⟩ : syracuseStep 3230765 = 1211537) B1211537
theorem B904279 : Blo 634301 904279 := bstep (se 1 (by rfl) ⟨678209, by rfl⟩ : syracuseStep 904279 = 1356419) B1356419
theorem B1428569 : Blo 634301 1428569 := bstep (se 2 (by rfl) ⟨535713, by rfl⟩ : syracuseStep 1428569 = 1071427) B1071427
theorem B2149469 : Blo 634301 2149469 := bstep (se 3 (by rfl) ⟨403025, by rfl⟩ : syracuseStep 2149469 = 806051) B806051
theorem B4574339 : Blo 634301 4574339 := bstep (se 1 (by rfl) ⟨3430754, by rfl⟩ : syracuseStep 4574339 = 6861509) B6861509
theorem B1428659 : Blo 634301 1428659 := bstep (se 1 (by rfl) ⟨1071494, by rfl⟩ : syracuseStep 1428659 = 2142989) B2142989
theorem B1428695 : Blo 634301 1428695 := bstep (se 1 (by rfl) ⟨1071521, by rfl⟩ : syracuseStep 1428695 = 2143043) B2143043
theorem B5295395 : Blo 634301 5295395 := bstep (se 1 (by rfl) ⟨3971546, by rfl⟩ : syracuseStep 5295395 = 7943093) B7943093
theorem B1428875 : Blo 634301 1428875 := bstep (se 1 (by rfl) ⟨1071656, by rfl⟩ : syracuseStep 1428875 = 2143313) B2143313
theorem B2411927 : Blo 634301 2411927 := bstep (se 1 (by rfl) ⟨1808945, by rfl⟩ : syracuseStep 2411927 = 3617891) B3617891
theorem B2444717 : Blo 634301 2444717 := bstep (se 3 (by rfl) ⟨458384, by rfl⟩ : syracuseStep 2444717 = 916769) B916769
theorem B6180275 : Blo 634301 6180275 := bstep (se 1 (by rfl) ⟨4635206, by rfl⟩ : syracuseStep 6180275 = 9270413) B9270413
theorem B1428929 : Blo 634301 1428929 := bstep (se 2 (by rfl) ⟨535848, by rfl⟩ : syracuseStep 1428929 = 1071697) B1071697
theorem B2412125 : Blo 634301 2412125 := bstep (se 3 (by rfl) ⟨452273, by rfl⟩ : syracuseStep 2412125 = 904547) B904547
theorem B1429145 : Blo 634301 1429145 := bstep (se 2 (by rfl) ⟨535929, by rfl⟩ : syracuseStep 1429145 = 1071859) B1071859
theorem B1429235 : Blo 634301 1429235 := bstep (se 1 (by rfl) ⟨1071926, by rfl⟩ : syracuseStep 1429235 = 2143853) B2143853
theorem B1429271 : Blo 634301 1429271 := bstep (se 1 (by rfl) ⟨1071953, by rfl⟩ : syracuseStep 1429271 = 2143907) B2143907
theorem B3624749 : Blo 634301 3624749 := bstep (se 3 (by rfl) ⟨679640, by rfl⟩ : syracuseStep 3624749 = 1359281) B1359281
theorem B905099 : Blo 634301 905099 := bstep (se 1 (by rfl) ⟨678824, by rfl⟩ : syracuseStep 905099 = 1357649) B1357649
theorem B1429451 : Blo 634301 1429451 := bstep (se 1 (by rfl) ⟨1072088, by rfl⟩ : syracuseStep 1429451 = 2144177) B2144177
theorem B1429505 : Blo 634301 1429505 := bstep (se 2 (by rfl) ⟨536064, by rfl⟩ : syracuseStep 1429505 = 1072129) B1072129
theorem B5165207 : Blo 634301 5165207 := bstep (se 1 (by rfl) ⟨3873905, by rfl⟩ : syracuseStep 5165207 = 7747811) B7747811
theorem B2150603 : Blo 634301 2150603 := bstep (se 1 (by rfl) ⟨1612952, by rfl⟩ : syracuseStep 2150603 = 3225905) B3225905
theorem B1429721 : Blo 634301 1429721 := bstep (se 2 (by rfl) ⟨536145, by rfl⟩ : syracuseStep 1429721 = 1072291) B1072291
theorem B1429811 : Blo 634301 1429811 := bstep (se 1 (by rfl) ⟨1072358, by rfl⟩ : syracuseStep 1429811 = 2144717) B2144717
theorem B1429847 : Blo 634301 1429847 := bstep (se 1 (by rfl) ⟨1072385, by rfl⟩ : syracuseStep 1429847 = 2144771) B2144771
theorem B5427587 : Blo 634301 5427587 := bstep (se 1 (by rfl) ⟨4070690, by rfl⟩ : syracuseStep 5427587 = 8141381) B8141381
theorem B2150873 : Blo 634301 2150873 := bstep (se 2 (by rfl) ⟨806577, by rfl⟩ : syracuseStep 2150873 = 1613155) B1613155
theorem B1430027 : Blo 634301 1430027 := bstep (se 1 (by rfl) ⟨1072520, by rfl⟩ : syracuseStep 1430027 = 2145041) B2145041
theorem B1430081 : Blo 634301 1430081 := bstep (se 2 (by rfl) ⟨536280, by rfl⟩ : syracuseStep 1430081 = 1072561) B1072561
theorem B807499 : Blo 634301 807499 := bstep (se 1 (by rfl) ⟨605624, by rfl⟩ : syracuseStep 807499 = 1211249) B1211249
theorem B1430297 : Blo 634301 1430297 := bstep (se 2 (by rfl) ⟨536361, by rfl⟩ : syracuseStep 1430297 = 1072723) B1072723
theorem B1430387 : Blo 634301 1430387 := bstep (se 1 (by rfl) ⟨1072790, by rfl⟩ : syracuseStep 1430387 = 2145581) B2145581
theorem B1430423 : Blo 634301 1430423 := bstep (se 1 (by rfl) ⟨1072817, by rfl⟩ : syracuseStep 1430423 = 2145635) B2145635
theorem B1430603 : Blo 634301 1430603 := bstep (se 1 (by rfl) ⟨1072952, by rfl⟩ : syracuseStep 1430603 = 2145905) B2145905
theorem B1430657 : Blo 634301 1430657 := bstep (se 2 (by rfl) ⟨536496, by rfl⟩ : syracuseStep 1430657 = 1072993) B1072993
theorem B2151575 : Blo 634301 2151575 := bstep (se 1 (by rfl) ⟨1613681, by rfl⟩ : syracuseStep 2151575 = 3227363) B3227363
theorem B1430873 : Blo 634301 1430873 := bstep (se 2 (by rfl) ⟨536577, by rfl⟩ : syracuseStep 1430873 = 1073155) B1073155
theorem B1070489 : Blo 634301 1070489 := bstep (se 2 (by rfl) ⟨401433, by rfl⟩ : syracuseStep 1070489 = 802867) B802867
theorem B1430963 : Blo 634301 1430963 := bstep (se 1 (by rfl) ⟨1073222, by rfl⟩ : syracuseStep 1430963 = 2146445) B2146445
theorem B1430999 : Blo 634301 1430999 := bstep (se 1 (by rfl) ⟨1073249, by rfl⟩ : syracuseStep 1430999 = 2146499) B2146499
theorem B2414083 : Blo 634301 2414083 := bstep (se 1 (by rfl) ⟨1810562, by rfl⟩ : syracuseStep 2414083 = 3621125) B3621125
theorem B1070617 : Blo 634301 1070617 := bstep (se 2 (by rfl) ⟨401481, by rfl⟩ : syracuseStep 1070617 = 802963) B802963
theorem B6116957 : Blo 634301 6116957 := bstep (se 3 (by rfl) ⟨1146929, by rfl⟩ : syracuseStep 6116957 = 2293859) B2293859
theorem B1431179 : Blo 634301 1431179 := bstep (se 1 (by rfl) ⟨1073384, by rfl⟩ : syracuseStep 1431179 = 2146769) B2146769
theorem B2152115 : Blo 634301 2152115 := bstep (se 1 (by rfl) ⟨1614086, by rfl⟩ : syracuseStep 2152115 = 3228173) B3228173
theorem B1431233 : Blo 634301 1431233 := bstep (se 2 (by rfl) ⟨536712, by rfl⟩ : syracuseStep 1431233 = 1073425) B1073425
theorem B906967 : Blo 634301 906967 := bstep (se 1 (by rfl) ⟨680225, by rfl⟩ : syracuseStep 906967 = 1360451) B1360451
theorem B2578193 : Blo 634301 2578193 := bstep (se 2 (by rfl) ⟨966822, by rfl⟩ : syracuseStep 2578193 = 1933645) B1933645
theorem B2414387 : Blo 634301 2414387 := bstep (se 1 (by rfl) ⟨1810790, by rfl⟩ : syracuseStep 2414387 = 3621581) B3621581
theorem B743275 : Blo 634301 743275 := bstep (se 1 (by rfl) ⟨557456, by rfl⟩ : syracuseStep 743275 = 1114913) B1114913
theorem B1431449 : Blo 634301 1431449 := bstep (se 2 (by rfl) ⟨536793, by rfl⟩ : syracuseStep 1431449 = 1073587) B1073587
theorem B2152385 : Blo 634301 2152385 := bstep (se 2 (by rfl) ⟨807144, by rfl⟩ : syracuseStep 2152385 = 1614289) B1614289
theorem B645067 : Blo 634301 645067 := bstep (se 1 (by rfl) ⟨483800, by rfl⟩ : syracuseStep 645067 = 967601) B967601
theorem B1431539 : Blo 634301 1431539 := bstep (se 1 (by rfl) ⟨1073654, by rfl⟩ : syracuseStep 1431539 = 2147309) B2147309
theorem B1431575 : Blo 634301 1431575 := bstep (se 1 (by rfl) ⟨1073681, by rfl⟩ : syracuseStep 1431575 = 2147363) B2147363
theorem B1071191 : Blo 634301 1071191 := bstep (se 1 (by rfl) ⟨803393, by rfl⟩ : syracuseStep 1071191 = 1606787) B1606787
theorem B3627139 : Blo 634301 3627139 := bstep (se 1 (by rfl) ⟨2720354, by rfl⟩ : syracuseStep 3627139 = 5440709) B5440709
theorem B1431755 : Blo 634301 1431755 := bstep (se 1 (by rfl) ⟨1073816, by rfl⟩ : syracuseStep 1431755 = 2147633) B2147633
theorem B1071319 : Blo 634301 1071319 := bstep (se 1 (by rfl) ⟨803489, by rfl⟩ : syracuseStep 1071319 = 1606979) B1606979
theorem B1431809 : Blo 634301 1431809 := bstep (se 2 (by rfl) ⟨536928, by rfl⟩ : syracuseStep 1431809 = 1073857) B1073857
theorem B2447747 : Blo 634301 2447747 := bstep (se 1 (by rfl) ⟨1835810, by rfl⟩ : syracuseStep 2447747 = 3671621) B3671621
theorem B678295 : Blo 634301 678295 := bstep (se 1 (by rfl) ⟨508721, by rfl⟩ : syracuseStep 678295 = 1017443) B1017443
theorem B11164081 : Blo 634301 11164081 := bstep (se 2 (by rfl) ⟨4186530, by rfl⟩ : syracuseStep 11164081 = 8373061) B8373061
theorem B2415041 : Blo 634301 2415041 := bstep (se 2 (by rfl) ⟨905640, by rfl⟩ : syracuseStep 2415041 = 1811281) B1811281
theorem B1432025 : Blo 634301 1432025 := bstep (se 2 (by rfl) ⟨537009, by rfl⟩ : syracuseStep 1432025 = 1074019) B1074019
theorem B2152925 : Blo 634301 2152925 := bstep (se 3 (by rfl) ⟨403673, by rfl⟩ : syracuseStep 2152925 = 807347) B807347
theorem B1432115 : Blo 634301 1432115 := bstep (se 1 (by rfl) ⟨1074086, by rfl⟩ : syracuseStep 1432115 = 2148173) B2148173
theorem B1432151 : Blo 634301 1432151 := bstep (se 1 (by rfl) ⟨1074113, by rfl⟩ : syracuseStep 1432151 = 2148227) B2148227
theorem B678551 : Blo 634301 678551 := bstep (se 1 (by rfl) ⟨508913, by rfl⟩ : syracuseStep 678551 = 1017827) B1017827
theorem B1432331 : Blo 634301 1432331 := bstep (se 1 (by rfl) ⟨1074248, by rfl⟩ : syracuseStep 1432331 = 2148497) B2148497
theorem B1432385 : Blo 634301 1432385 := bstep (se 2 (by rfl) ⟨537144, by rfl⟩ : syracuseStep 1432385 = 1074289) B1074289
theorem B1071947 : Blo 634301 1071947 := bstep (se 1 (by rfl) ⟨803960, by rfl⟩ : syracuseStep 1071947 = 1607921) B1607921
theorem B2710361 : Blo 634301 2710361 := bstep (se 2 (by rfl) ⟨1016385, by rfl⟩ : syracuseStep 2710361 = 2032771) B2032771
theorem B7756721 : Blo 634301 7756721 := bstep (se 2 (by rfl) ⟨2908770, by rfl⟩ : syracuseStep 7756721 = 5817541) B5817541
theorem B1072075 : Blo 634301 1072075 := bstep (se 1 (by rfl) ⟨804056, by rfl⟩ : syracuseStep 1072075 = 1608113) B1608113
theorem B2579473 : Blo 634301 2579473 := bstep (se 2 (by rfl) ⟨967302, by rfl⟩ : syracuseStep 2579473 = 1934605) B1934605
theorem B1432601 : Blo 634301 1432601 := bstep (se 2 (by rfl) ⟨537225, by rfl⟩ : syracuseStep 1432601 = 1074451) B1074451
theorem B3628097 : Blo 634301 3628097 := bstep (se 2 (by rfl) ⟨1360536, by rfl⟩ : syracuseStep 3628097 = 2721073) B2721073
theorem B1072217 : Blo 634301 1072217 := bstep (se 2 (by rfl) ⟨402081, by rfl⟩ : syracuseStep 1072217 = 804163) B804163
theorem B1432691 : Blo 634301 1432691 := bstep (se 1 (by rfl) ⟨1074518, by rfl⟩ : syracuseStep 1432691 = 2149037) B2149037
theorem B1432727 : Blo 634301 1432727 := bstep (se 1 (by rfl) ⟨1074545, by rfl⟩ : syracuseStep 1432727 = 2149091) B2149091
theorem B1629377 : Blo 634301 1629377 := bstep (se 2 (by rfl) ⟨611016, by rfl⟩ : syracuseStep 1629377 = 1222033) B1222033
theorem B679115 : Blo 634301 679115 := bstep (se 1 (by rfl) ⟨509336, by rfl⟩ : syracuseStep 679115 = 1018673) B1018673
theorem B1072345 : Blo 634301 1072345 := bstep (se 2 (by rfl) ⟨402129, by rfl⟩ : syracuseStep 1072345 = 804259) B804259
theorem B5430563 : Blo 634301 5430563 := bstep (se 1 (by rfl) ⟨4072922, by rfl⟩ : syracuseStep 5430563 = 8145845) B8145845
theorem B1432907 : Blo 634301 1432907 := bstep (se 1 (by rfl) ⟨1074680, by rfl⟩ : syracuseStep 1432907 = 2149361) B2149361
theorem B1432961 : Blo 634301 1432961 := bstep (se 2 (by rfl) ⟨537360, by rfl⟩ : syracuseStep 1432961 = 1074721) B1074721
theorem B5791297 : Blo 634301 5791297 := bstep (se 2 (by rfl) ⟨2171736, by rfl⟩ : syracuseStep 5791297 = 4343473) B4343473
theorem B2154059 : Blo 634301 2154059 := bstep (se 1 (by rfl) ⟨1615544, by rfl⟩ : syracuseStep 2154059 = 3231089) B3231089
theorem B1433177 : Blo 634301 1433177 := bstep (se 2 (by rfl) ⟨537441, by rfl⟩ : syracuseStep 1433177 = 1074883) B1074883
theorem B2416301 : Blo 634301 2416301 := bstep (se 3 (by rfl) ⟨453056, by rfl⟩ : syracuseStep 2416301 = 906113) B906113
theorem B1433267 : Blo 634301 1433267 := bstep (se 1 (by rfl) ⟨1074950, by rfl⟩ : syracuseStep 1433267 = 2149901) B2149901
theorem B2416331 : Blo 634301 2416331 := bstep (se 1 (by rfl) ⟨1812248, by rfl⟩ : syracuseStep 2416331 = 3624497) B3624497
theorem B1433303 : Blo 634301 1433303 := bstep (se 1 (by rfl) ⟨1074977, by rfl⟩ : syracuseStep 1433303 = 2149955) B2149955
theorem B1072919 : Blo 634301 1072919 := bstep (se 1 (by rfl) ⟨804689, by rfl⟩ : syracuseStep 1072919 = 1609379) B1609379
theorem B1433483 : Blo 634301 1433483 := bstep (se 1 (by rfl) ⟨1075112, by rfl⟩ : syracuseStep 1433483 = 2150225) B2150225
theorem B1073047 : Blo 634301 1073047 := bstep (se 1 (by rfl) ⟨804785, by rfl⟩ : syracuseStep 1073047 = 1609571) B1609571
theorem B1433537 : Blo 634301 1433537 := bstep (se 2 (by rfl) ⟨537576, by rfl⟩ : syracuseStep 1433537 = 1075153) B1075153
theorem B4644881 : Blo 634301 4644881 := bstep (se 2 (by rfl) ⟨1741830, by rfl⟩ : syracuseStep 4644881 = 3483661) B3483661
theorem B1204247 : Blo 634301 1204247 := bstep (se 1 (by rfl) ⟨903185, by rfl⟩ : syracuseStep 1204247 = 1806371) B1806371
theorem B1433753 : Blo 634301 1433753 := bstep (se 2 (by rfl) ⟨537657, by rfl⟩ : syracuseStep 1433753 = 1075315) B1075315
theorem B2318539 : Blo 634301 2318539 := bstep (se 1 (by rfl) ⟨1738904, by rfl⟩ : syracuseStep 2318539 = 3477809) B3477809
theorem B1433843 : Blo 634301 1433843 := bstep (se 1 (by rfl) ⟨1075382, by rfl⟩ : syracuseStep 1433843 = 2150765) B2150765
theorem B1433879 : Blo 634301 1433879 := bstep (se 1 (by rfl) ⟨1075409, by rfl⟩ : syracuseStep 1433879 = 2150819) B2150819
theorem B13066541 : Blo 634301 13066541 := bstep (se 3 (by rfl) ⟨2449976, by rfl⟩ : syracuseStep 13066541 = 4899953) B4899953
theorem B2416985 : Blo 634301 2416985 := bstep (se 2 (by rfl) ⟨906369, by rfl⟩ : syracuseStep 2416985 = 1812739) B1812739
theorem B16310645 : Blo 634301 16310645 := bstep (se 5 (by rfl) ⟨764561, by rfl⟩ : syracuseStep 16310645 = 1529123) B1529123
theorem B2712001 : Blo 634301 2712001 := bstep (se 2 (by rfl) ⟨1017000, by rfl⟩ : syracuseStep 2712001 = 2034001) B2034001
theorem B1532353 : Blo 634301 1532353 := bstep (se 2 (by rfl) ⟨574632, by rfl⟩ : syracuseStep 1532353 = 1149265) B1149265
theorem B1434059 : Blo 634301 1434059 := bstep (se 1 (by rfl) ⟨1075544, by rfl⟩ : syracuseStep 1434059 = 2151089) B2151089
theorem B1630681 : Blo 634301 1630681 := bstep (se 2 (by rfl) ⟨611505, by rfl⟩ : syracuseStep 1630681 = 1223011) B1223011
theorem B1434113 : Blo 634301 1434113 := bstep (se 2 (by rfl) ⟨537792, by rfl⟩ : syracuseStep 1434113 = 1075585) B1075585
theorem B1073675 : Blo 634301 1073675 := bstep (se 1 (by rfl) ⟨805256, by rfl⟩ : syracuseStep 1073675 = 1610513) B1610513
theorem B1204787 : Blo 634301 1204787 := bstep (se 1 (by rfl) ⟨903590, by rfl⟩ : syracuseStep 1204787 = 1807181) B1807181
theorem B680567 : Blo 634301 680567 := bstep (se 1 (by rfl) ⟨510425, by rfl⟩ : syracuseStep 680567 = 1020851) B1020851
theorem B1073803 : Blo 634301 1073803 := bstep (se 1 (by rfl) ⟨805352, by rfl⟩ : syracuseStep 1073803 = 1610705) B1610705
theorem B2417303 : Blo 634301 2417303 := bstep (se 1 (by rfl) ⟨1812977, by rfl⟩ : syracuseStep 2417303 = 3625955) B3625955
theorem B1630937 : Blo 634301 1630937 := bstep (se 2 (by rfl) ⟨611601, by rfl⟩ : syracuseStep 1630937 = 1223203) B1223203
theorem B1434329 : Blo 634301 1434329 := bstep (se 2 (by rfl) ⟨537873, by rfl⟩ : syracuseStep 1434329 = 1075747) B1075747
theorem B1073945 : Blo 634301 1073945 := bstep (se 2 (by rfl) ⟨402729, by rfl⟩ : syracuseStep 1073945 = 805459) B805459
theorem B1434419 : Blo 634301 1434419 := bstep (se 1 (by rfl) ⟨1075814, by rfl⟩ : syracuseStep 1434419 = 2151629) B2151629
theorem B1434455 : Blo 634301 1434455 := bstep (se 1 (by rfl) ⟨1075841, by rfl⟩ : syracuseStep 1434455 = 2151683) B2151683
theorem B713623 : Blo 634301 713623 := bstep (se 1 (by rfl) ⟨535217, by rfl⟩ : syracuseStep 713623 = 1070435) B1070435
theorem B1074073 : Blo 634301 1074073 := bstep (se 2 (by rfl) ⟨402777, by rfl⟩ : syracuseStep 1074073 = 805555) B805555
theorem B1434635 : Blo 634301 1434635 := bstep (se 1 (by rfl) ⟨1075976, by rfl⟩ : syracuseStep 1434635 = 2151953) B2151953
theorem B2712599 : Blo 634301 2712599 := bstep (se 1 (by rfl) ⟨2034449, by rfl⟩ : syracuseStep 2712599 = 4068899) B4068899
theorem B1205273 : Blo 634301 1205273 := bstep (se 2 (by rfl) ⟨451977, by rfl⟩ : syracuseStep 1205273 = 903955) B903955
theorem B7234595 : Blo 634301 7234595 := bstep (se 1 (by rfl) ⟨5425946, by rfl⟩ : syracuseStep 7234595 = 10851893) B10851893
theorem B1434689 : Blo 634301 1434689 := bstep (se 2 (by rfl) ⟨538008, by rfl⟩ : syracuseStep 1434689 = 1076017) B1076017
theorem B713803 : Blo 634301 713803 := bstep (se 1 (by rfl) ⟨535352, by rfl⟩ : syracuseStep 713803 = 1070705) B1070705
theorem B6186077 : Blo 634301 6186077 := bstep (se 3 (by rfl) ⟨1159889, by rfl⟩ : syracuseStep 6186077 = 2319779) B2319779
theorem B12412055 : Blo 634301 12412055 := bstep (se 1 (by rfl) ⟨9309041, by rfl⟩ : syracuseStep 12412055 = 18618083) B18618083
theorem B713911 : Blo 634301 713911 := bstep (se 1 (by rfl) ⟨535433, by rfl⟩ : syracuseStep 713911 = 1070867) B1070867
theorem B1434905 : Blo 634301 1434905 := bstep (se 2 (by rfl) ⟨538089, by rfl⟩ : syracuseStep 1434905 = 1076179) B1076179
theorem B2417971 : Blo 634301 2417971 := bstep (se 1 (by rfl) ⟨1813478, by rfl⟩ : syracuseStep 2417971 = 3626957) B3626957
theorem B714091 : Blo 634301 714091 := bstep (se 1 (by rfl) ⟨535568, by rfl⟩ : syracuseStep 714091 = 1071137) B1071137
theorem B1434995 : Blo 634301 1434995 := bstep (se 1 (by rfl) ⟨1076246, by rfl⟩ : syracuseStep 1434995 = 2152493) B2152493
theorem B1435031 : Blo 634301 1435031 := bstep (se 1 (by rfl) ⟨1076273, by rfl⟩ : syracuseStep 1435031 = 2152547) B2152547
theorem B714199 : Blo 634301 714199 := bstep (se 1 (by rfl) ⟨535649, by rfl⟩ : syracuseStep 714199 = 1071299) B1071299
theorem B1074647 : Blo 634301 1074647 := bstep (se 1 (by rfl) ⟨805985, by rfl⟩ : syracuseStep 1074647 = 1611971) B1611971
theorem B1435211 : Blo 634301 1435211 := bstep (se 1 (by rfl) ⟨1076408, by rfl⟩ : syracuseStep 1435211 = 2152817) B2152817
theorem B1074775 : Blo 634301 1074775 := bstep (se 1 (by rfl) ⟨806081, by rfl⟩ : syracuseStep 1074775 = 1612163) B1612163
theorem B1435265 : Blo 634301 1435265 := bstep (se 2 (by rfl) ⟨538224, by rfl⟩ : syracuseStep 1435265 = 1076449) B1076449
theorem B714379 : Blo 634301 714379 := bstep (se 1 (by rfl) ⟨535784, by rfl⟩ : syracuseStep 714379 = 1071569) B1071569
theorem B714487 : Blo 634301 714487 := bstep (se 1 (by rfl) ⟨535865, by rfl⟩ : syracuseStep 714487 = 1071731) B1071731
theorem B5170979 : Blo 634301 5170979 := bstep (se 1 (by rfl) ⟨3878234, by rfl⟩ : syracuseStep 5170979 = 7756469) B7756469
theorem B1435481 : Blo 634301 1435481 := bstep (se 2 (by rfl) ⟨538305, by rfl⟩ : syracuseStep 1435481 = 1076611) B1076611
theorem B714667 : Blo 634301 714667 := bstep (se 1 (by rfl) ⟨536000, by rfl⟩ : syracuseStep 714667 = 1072001) B1072001
theorem B1435571 : Blo 634301 1435571 := bstep (se 1 (by rfl) ⟨1076678, by rfl⟩ : syracuseStep 1435571 = 2153357) B2153357
theorem B1435607 : Blo 634301 1435607 := bstep (se 1 (by rfl) ⟨1076705, by rfl⟩ : syracuseStep 1435607 = 2153411) B2153411
theorem B714775 : Blo 634301 714775 := bstep (se 1 (by rfl) ⟨536081, by rfl⟩ : syracuseStep 714775 = 1072163) B1072163
theorem B1435787 : Blo 634301 1435787 := bstep (se 1 (by rfl) ⟨1076840, by rfl⟩ : syracuseStep 1435787 = 2153681) B2153681
theorem B1435841 : Blo 634301 1435841 := bstep (se 2 (by rfl) ⟨538440, by rfl⟩ : syracuseStep 1435841 = 1076881) B1076881
theorem B714955 : Blo 634301 714955 := bstep (se 1 (by rfl) ⟨536216, by rfl⟩ : syracuseStep 714955 = 1072433) B1072433
theorem B1075403 : Blo 634301 1075403 := bstep (se 1 (by rfl) ⟨806552, by rfl⟩ : syracuseStep 1075403 = 1613105) B1613105
theorem B715063 : Blo 634301 715063 := bstep (se 1 (by rfl) ⟨536297, by rfl⟩ : syracuseStep 715063 = 1072595) B1072595
theorem B2713931 : Blo 634301 2713931 := bstep (se 1 (by rfl) ⟨2035448, by rfl⟩ : syracuseStep 2713931 = 4070897) B4070897
theorem B1075531 : Blo 634301 1075531 := bstep (se 1 (by rfl) ⟨806648, by rfl⟩ : syracuseStep 1075531 = 1613297) B1613297
theorem B1436057 : Blo 634301 1436057 := bstep (se 2 (by rfl) ⟨538521, by rfl⟩ : syracuseStep 1436057 = 1077043) B1077043
theorem B1206731 : Blo 634301 1206731 := bstep (se 1 (by rfl) ⟨905048, by rfl⟩ : syracuseStep 1206731 = 1810097) B1810097
theorem B1075673 : Blo 634301 1075673 := bstep (se 2 (by rfl) ⟨403377, by rfl⟩ : syracuseStep 1075673 = 806755) B806755
theorem B715243 : Blo 634301 715243 := bstep (se 1 (by rfl) ⟨536432, by rfl⟩ : syracuseStep 715243 = 1072865) B1072865
theorem B1436147 : Blo 634301 1436147 := bstep (se 1 (by rfl) ⟨1077110, by rfl⟩ : syracuseStep 1436147 = 2154221) B2154221
theorem B2419217 : Blo 634301 2419217 := bstep (se 2 (by rfl) ⟨907206, by rfl⟩ : syracuseStep 2419217 = 1814413) B1814413
theorem B715351 : Blo 634301 715351 := bstep (se 1 (by rfl) ⟨536513, by rfl⟩ : syracuseStep 715351 = 1073027) B1073027
theorem B1075801 : Blo 634301 1075801 := bstep (se 2 (by rfl) ⟨403425, by rfl⟩ : syracuseStep 1075801 = 806851) B806851
theorem B1206913 : Blo 634301 1206913 := bstep (se 2 (by rfl) ⟨452592, by rfl⟩ : syracuseStep 1206913 = 905185) B905185
theorem B1239767 : Blo 634301 1239767 := bstep (se 1 (by rfl) ⟨929825, by rfl⟩ : syracuseStep 1239767 = 1859651) B1859651
theorem B715531 : Blo 634301 715531 := bstep (se 1 (by rfl) ⟨536648, by rfl⟩ : syracuseStep 715531 = 1073297) B1073297
theorem B715639 : Blo 634301 715639 := bstep (se 1 (by rfl) ⟨536729, by rfl⟩ : syracuseStep 715639 = 1073459) B1073459
theorem B715819 : Blo 634301 715819 := bstep (se 1 (by rfl) ⟨536864, by rfl⟩ : syracuseStep 715819 = 1073729) B1073729
theorem B1207361 : Blo 634301 1207361 := bstep (se 2 (by rfl) ⟨452760, by rfl⟩ : syracuseStep 1207361 = 905521) B905521
theorem B19557445 : Blo 634301 19557445 := bstep (se 4 (by rfl) ⟨1833510, by rfl⟩ : syracuseStep 19557445 = 3667021) B3667021
theorem B715927 : Blo 634301 715927 := bstep (se 1 (by rfl) ⟨536945, by rfl⟩ : syracuseStep 715927 = 1073891) B1073891
theorem B1076375 : Blo 634301 1076375 := bstep (se 1 (by rfl) ⟨807281, by rfl⟩ : syracuseStep 1076375 = 1614563) B1614563
theorem B2288843 : Blo 634301 2288843 := bstep (se 1 (by rfl) ⟨1716632, by rfl⟩ : syracuseStep 2288843 = 3433265) B3433265
theorem B2419915 : Blo 634301 2419915 := bstep (se 1 (by rfl) ⟨1814936, by rfl⟩ : syracuseStep 2419915 = 3629873) B3629873
theorem B1076503 : Blo 634301 1076503 := bstep (se 1 (by rfl) ⟨807377, by rfl⟩ : syracuseStep 1076503 = 1614755) B1614755
theorem B716107 : Blo 634301 716107 := bstep (se 1 (by rfl) ⟨537080, by rfl⟩ : syracuseStep 716107 = 1074161) B1074161
theorem B4582757 : Blo 634301 4582757 := bstep (se 4 (by rfl) ⟨429633, by rfl⟩ : syracuseStep 4582757 = 859267) B859267
theorem B1207703 : Blo 634301 1207703 := bstep (se 1 (by rfl) ⟨905777, by rfl⟩ : syracuseStep 1207703 = 1811555) B1811555
theorem B2715059 : Blo 634301 2715059 := bstep (se 1 (by rfl) ⟨2036294, by rfl⟩ : syracuseStep 2715059 = 4072589) B4072589
theorem B716215 : Blo 634301 716215 := bstep (se 1 (by rfl) ⟨537161, by rfl⟩ : syracuseStep 716215 = 1074323) B1074323
theorem B2420189 : Blo 634301 2420189 := bstep (se 3 (by rfl) ⟨453785, by rfl⟩ : syracuseStep 2420189 = 907571) B907571
theorem B716395 : Blo 634301 716395 := bstep (se 1 (by rfl) ⟨537296, by rfl⟩ : syracuseStep 716395 = 1074593) B1074593
theorem B716503 : Blo 634301 716503 := bstep (se 1 (by rfl) ⟨537377, by rfl⟩ : syracuseStep 716503 = 1074755) B1074755
theorem B3632971 : Blo 634301 3632971 := bstep (se 1 (by rfl) ⟨2724728, by rfl⟩ : syracuseStep 3632971 = 5449457) B5449457
theorem B3108701 : Blo 634301 3108701 := bstep (se 3 (by rfl) ⟨582881, by rfl⟩ : syracuseStep 3108701 = 1165763) B1165763
theorem B716683 : Blo 634301 716683 := bstep (se 1 (by rfl) ⟨537512, by rfl⟩ : syracuseStep 716683 = 1075025) B1075025
theorem B1077131 : Blo 634301 1077131 := bstep (se 1 (by rfl) ⟨807848, by rfl⟩ : syracuseStep 1077131 = 1615697) B1615697
theorem B716791 : Blo 634301 716791 := bstep (se 1 (by rfl) ⟨537593, by rfl⟩ : syracuseStep 716791 = 1075187) B1075187
theorem B1208371 : Blo 634301 1208371 := bstep (se 1 (by rfl) ⟨906278, by rfl⟩ : syracuseStep 1208371 = 1812557) B1812557
theorem B2748505 : Blo 634301 2748505 := bstep (se 2 (by rfl) ⟨1030689, by rfl⟩ : syracuseStep 2748505 = 2061379) B2061379
theorem B3633245 : Blo 634301 3633245 := bstep (se 3 (by rfl) ⟨681233, by rfl⟩ : syracuseStep 3633245 = 1362467) B1362467
theorem B2420887 : Blo 634301 2420887 := bstep (se 1 (by rfl) ⟨1815665, by rfl⟩ : syracuseStep 2420887 = 3631331) B3631331
theorem B716971 : Blo 634301 716971 := bstep (se 1 (by rfl) ⟨537728, by rfl⟩ : syracuseStep 716971 = 1075457) B1075457
theorem B717079 : Blo 634301 717079 := bstep (se 1 (by rfl) ⟨537809, by rfl⟩ : syracuseStep 717079 = 1075619) B1075619
theorem B717259 : Blo 634301 717259 := bstep (se 1 (by rfl) ⟨537944, by rfl⟩ : syracuseStep 717259 = 1075889) B1075889
theorem B1208819 : Blo 634301 1208819 := bstep (se 1 (by rfl) ⟨906614, by rfl⟩ : syracuseStep 1208819 = 1813229) B1813229
theorem B1208857 : Blo 634301 1208857 := bstep (se 2 (by rfl) ⟨453321, by rfl⟩ : syracuseStep 1208857 = 906643) B906643
theorem B717367 : Blo 634301 717367 := bstep (se 1 (by rfl) ⟨538025, by rfl⟩ : syracuseStep 717367 = 1076051) B1076051
theorem B717547 : Blo 634301 717547 := bstep (se 1 (by rfl) ⟨538160, by rfl⟩ : syracuseStep 717547 = 1076321) B1076321
theorem B717655 : Blo 634301 717655 := bstep (se 1 (by rfl) ⟨538241, by rfl⟩ : syracuseStep 717655 = 1076483) B1076483
theorem B2421677 : Blo 634301 2421677 := bstep (se 3 (by rfl) ⟨454064, by rfl⟩ : syracuseStep 2421677 = 908129) B908129
theorem B1209305 : Blo 634301 1209305 := bstep (se 2 (by rfl) ⟨453489, by rfl⟩ : syracuseStep 1209305 = 906979) B906979
theorem B1373195 : Blo 634301 1373195 := bstep (se 1 (by rfl) ⟨1029896, by rfl⟩ : syracuseStep 1373195 = 2059793) B2059793
theorem B717835 : Blo 634301 717835 := bstep (se 1 (by rfl) ⟨538376, by rfl⟩ : syracuseStep 717835 = 1076753) B1076753
theorem B717943 : Blo 634301 717943 := bstep (se 1 (by rfl) ⟨538457, by rfl⟩ : syracuseStep 717943 = 1076915) B1076915
theorem B5174545 : Blo 634301 5174545 := bstep (se 2 (by rfl) ⟨1940454, by rfl⟩ : syracuseStep 5174545 = 3880909) B3880909
theorem B2716973 : Blo 634301 2716973 := bstep (se 3 (by rfl) ⟨509432, by rfl⟩ : syracuseStep 2716973 = 1018865) B1018865
theorem B2487901 : Blo 634301 2487901 := bstep (se 3 (by rfl) ⟨466481, by rfl⟩ : syracuseStep 2487901 = 932963) B932963
theorem B1210049 : Blo 634301 1210049 := bstep (se 2 (by rfl) ⟨453768, by rfl⟩ : syracuseStep 1210049 = 907537) B907537
theorem B149157773 : Blo 634301 149157773 := bstep (se 3 (by rfl) ⟨27967082, by rfl⟩ : syracuseStep 149157773 = 55934165) B55934165
theorem B1210315 : Blo 634301 1210315 := bstep (se 1 (by rfl) ⟨907736, by rfl⟩ : syracuseStep 1210315 = 1815473) B1815473
theorem B2717657 : Blo 634301 2717657 := bstep (se 2 (by rfl) ⟨1019121, by rfl⟩ : syracuseStep 2717657 = 2038243) B2038243
theorem B1931357 : Blo 634301 1931357 := bstep (se 3 (by rfl) ⟨362129, by rfl⟩ : syracuseStep 1931357 = 724259) B724259
theorem B2586755 : Blo 634301 2586755 := bstep (se 1 (by rfl) ⟨1940066, by rfl⟩ : syracuseStep 2586755 = 3880133) B3880133
theorem B6125719 : Blo 634301 6125719 := bstep (se 1 (by rfl) ⟨4594289, by rfl⟩ : syracuseStep 6125719 = 9188579) B9188579
theorem B3274931 : Blo 634301 3274931 := bstep (se 1 (by rfl) ⟨2456198, by rfl⟩ : syracuseStep 3274931 = 4912397) B4912397
theorem B2423105 : Blo 634301 2423105 := bstep (se 2 (by rfl) ⟨908664, by rfl⟩ : syracuseStep 2423105 = 1817329) B1817329
theorem B1309043 : Blo 634301 1309043 := bstep (se 1 (by rfl) ⟨981782, by rfl⟩ : syracuseStep 1309043 = 1963565) B1963565
theorem B1210763 : Blo 634301 1210763 := bstep (se 1 (by rfl) ⟨908072, by rfl⟩ : syracuseStep 1210763 = 1816145) B1816145
theorem B11008547 : Blo 634301 11008547 := bstep (se 1 (by rfl) ⟨8256410, by rfl⟩ : syracuseStep 11008547 = 16512821) B16512821
theorem B1210945 : Blo 634301 1210945 := bstep (se 2 (by rfl) ⟨454104, by rfl⟩ : syracuseStep 1210945 = 908209) B908209
theorem B1637015 : Blo 634301 1637015 := bstep (se 1 (by rfl) ⟨1227761, by rfl⟩ : syracuseStep 1637015 = 2455523) B2455523
theorem B16284401 : Blo 634301 16284401 := bstep (se 2 (by rfl) ⟨6106650, by rfl⟩ : syracuseStep 16284401 = 12213301) B12213301
theorem B1309529 : Blo 634301 1309529 := bstep (se 2 (by rfl) ⟨491073, by rfl⟩ : syracuseStep 1309529 = 982147) B982147
theorem B1211287 : Blo 634301 1211287 := bstep (se 1 (by rfl) ⟨908465, by rfl⟩ : syracuseStep 1211287 = 1816931) B1816931
theorem B2620505 : Blo 634301 2620505 := bstep (se 2 (by rfl) ⟨982689, by rfl⟩ : syracuseStep 2620505 = 1965379) B1965379
theorem B1145971 : Blo 634301 1145971 := bstep (se 1 (by rfl) ⟨859478, by rfl⟩ : syracuseStep 1145971 = 1718957) B1718957
theorem B1211507 : Blo 634301 1211507 := bstep (se 1 (by rfl) ⟨908630, by rfl⟩ : syracuseStep 1211507 = 1817261) B1817261
theorem B1211735 : Blo 634301 1211735 := bstep (se 1 (by rfl) ⟨908801, by rfl⟩ : syracuseStep 1211735 = 1817603) B1817603
theorem B982603 : Blo 634301 982603 := bstep (se 1 (by rfl) ⟨736952, by rfl⟩ : syracuseStep 982603 = 1473905) B1473905
theorem B3211325 : Blo 634301 3211325 := bstep (se 3 (by rfl) ⟨602123, by rfl⟩ : syracuseStep 3211325 = 1204247) B1204247
theorem B1606007 : Blo 634301 1606007 := bstep (se 1 (by rfl) ⟨1204505, by rfl⟩ : syracuseStep 1606007 = 2409011) B2409011
theorem B1934227 : Blo 634301 1934227 := bstep (se 1 (by rfl) ⟨1450670, by rfl⟩ : syracuseStep 1934227 = 2901341) B2901341
theorem B951467 : Blo 634301 951467 := bstep (se 1 (by rfl) ⟨713600, by rfl⟩ : syracuseStep 951467 = 1427201) B1427201
theorem B951497 : Blo 634301 951497 := bstep (se 2 (by rfl) ⟨356811, by rfl⟩ : syracuseStep 951497 = 713623) B713623
theorem B951611 : Blo 634301 951611 := bstep (se 1 (by rfl) ⟨713708, by rfl⟩ : syracuseStep 951611 = 1427417) B1427417
theorem B1606999 : Blo 634301 1606999 := bstep (se 1 (by rfl) ⟨1205249, by rfl⟩ : syracuseStep 1606999 = 2410499) B2410499
theorem B951671 : Blo 634301 951671 := bstep (se 1 (by rfl) ⟨713753, by rfl⟩ : syracuseStep 951671 = 1427507) B1427507
theorem B951695 : Blo 634301 951695 := bstep (se 1 (by rfl) ⟨713771, by rfl⟩ : syracuseStep 951695 = 1427543) B1427543
theorem B951737 : Blo 634301 951737 := bstep (se 2 (by rfl) ⟨356901, by rfl⟩ : syracuseStep 951737 = 713803) B713803
theorem B1017289 : Blo 634301 1017289 := bstep (se 2 (by rfl) ⟨381483, by rfl⟩ : syracuseStep 1017289 = 762967) B762967
theorem B951815 : Blo 634301 951815 := bstep (se 1 (by rfl) ⟨713861, by rfl⟩ : syracuseStep 951815 = 1427723) B1427723
theorem B951851 : Blo 634301 951851 := bstep (se 1 (by rfl) ⟨713888, by rfl⟩ : syracuseStep 951851 = 1427777) B1427777
theorem B5506627 : Blo 634301 5506627 := bstep (se 1 (by rfl) ⟨4129970, by rfl⟩ : syracuseStep 5506627 = 8259941) B8259941
theorem B2721347 : Blo 634301 2721347 := bstep (se 1 (by rfl) ⟨2041010, by rfl⟩ : syracuseStep 2721347 = 4082021) B4082021
theorem B951881 : Blo 634301 951881 := bstep (se 2 (by rfl) ⟨356955, by rfl⟩ : syracuseStep 951881 = 713911) B713911
theorem B1607303 : Blo 634301 1607303 := bstep (se 1 (by rfl) ⟨1205477, by rfl⟩ : syracuseStep 1607303 = 2410955) B2410955
theorem B951995 : Blo 634301 951995 := bstep (se 1 (by rfl) ⟨713996, by rfl⟩ : syracuseStep 951995 = 1427993) B1427993
theorem B952055 : Blo 634301 952055 := bstep (se 1 (by rfl) ⟨714041, by rfl⟩ : syracuseStep 952055 = 1428083) B1428083
theorem B4818689 : Blo 634301 4818689 := bstep (se 2 (by rfl) ⟨1807008, by rfl⟩ : syracuseStep 4818689 = 3614017) B3614017
theorem B1607435 : Blo 634301 1607435 := bstep (se 1 (by rfl) ⟨1205576, by rfl⟩ : syracuseStep 1607435 = 2411153) B2411153
theorem B952079 : Blo 634301 952079 := bstep (se 1 (by rfl) ⟨714059, by rfl⟩ : syracuseStep 952079 = 1428119) B1428119
theorem B3213107 : Blo 634301 3213107 := bstep (se 1 (by rfl) ⟨2409830, by rfl⟩ : syracuseStep 3213107 = 4819661) B4819661
theorem B952121 : Blo 634301 952121 := bstep (se 2 (by rfl) ⟨357045, by rfl⟩ : syracuseStep 952121 = 714091) B714091
theorem B952199 : Blo 634301 952199 := bstep (se 1 (by rfl) ⟨714149, by rfl⟩ : syracuseStep 952199 = 1428299) B1428299
theorem B952235 : Blo 634301 952235 := bstep (se 1 (by rfl) ⟨714176, by rfl⟩ : syracuseStep 952235 = 1428353) B1428353
theorem B952265 : Blo 634301 952265 := bstep (se 2 (by rfl) ⟨357099, by rfl⟩ : syracuseStep 952265 = 714199) B714199
theorem B952379 : Blo 634301 952379 := bstep (se 1 (by rfl) ⟨714284, by rfl⟩ : syracuseStep 952379 = 1428569) B1428569
theorem B3049559 : Blo 634301 3049559 := bstep (se 1 (by rfl) ⟨2287169, by rfl⟩ : syracuseStep 3049559 = 4574339) B4574339
theorem B3213431 : Blo 634301 3213431 := bstep (se 1 (by rfl) ⟨2410073, by rfl⟩ : syracuseStep 3213431 = 4820147) B4820147
theorem B952439 : Blo 634301 952439 := bstep (se 1 (by rfl) ⟨714329, by rfl⟩ : syracuseStep 952439 = 1428659) B1428659
theorem B952463 : Blo 634301 952463 := bstep (se 1 (by rfl) ⟨714347, by rfl⟩ : syracuseStep 952463 = 1428695) B1428695
theorem B952505 : Blo 634301 952505 := bstep (se 2 (by rfl) ⟨357189, by rfl⟩ : syracuseStep 952505 = 714379) B714379
theorem B952583 : Blo 634301 952583 := bstep (se 1 (by rfl) ⟨714437, by rfl⟩ : syracuseStep 952583 = 1428875) B1428875
theorem B1607951 : Blo 634301 1607951 := bstep (se 1 (by rfl) ⟨1205963, by rfl⟩ : syracuseStep 1607951 = 2411927) B2411927
theorem B952619 : Blo 634301 952619 := bstep (se 1 (by rfl) ⟨714464, by rfl⟩ : syracuseStep 952619 = 1428929) B1428929
theorem B952649 : Blo 634301 952649 := bstep (se 2 (by rfl) ⟨357243, by rfl⟩ : syracuseStep 952649 = 714487) B714487
theorem B1608083 : Blo 634301 1608083 := bstep (se 1 (by rfl) ⟨1206062, by rfl⟩ : syracuseStep 1608083 = 2412125) B2412125
theorem B952763 : Blo 634301 952763 := bstep (se 1 (by rfl) ⟨714572, by rfl⟩ : syracuseStep 952763 = 1429145) B1429145
theorem B952823 : Blo 634301 952823 := bstep (se 1 (by rfl) ⟨714617, by rfl⟩ : syracuseStep 952823 = 1429235) B1429235
theorem B952847 : Blo 634301 952847 := bstep (se 1 (by rfl) ⟨714635, by rfl⟩ : syracuseStep 952847 = 1429271) B1429271
theorem B952889 : Blo 634301 952889 := bstep (se 2 (by rfl) ⟨357333, by rfl⟩ : syracuseStep 952889 = 714667) B714667
theorem B952967 : Blo 634301 952967 := bstep (se 1 (by rfl) ⟨714725, by rfl⟩ : syracuseStep 952967 = 1429451) B1429451
theorem B953003 : Blo 634301 953003 := bstep (se 1 (by rfl) ⟨714752, by rfl⟩ : syracuseStep 953003 = 1429505) B1429505
theorem B953033 : Blo 634301 953033 := bstep (se 2 (by rfl) ⟨357387, by rfl⟩ : syracuseStep 953033 = 714775) B714775
theorem B3443471 : Blo 634301 3443471 := bstep (se 1 (by rfl) ⟨2582603, by rfl⟩ : syracuseStep 3443471 = 5165207) B5165207
theorem B953147 : Blo 634301 953147 := bstep (se 1 (by rfl) ⟨714860, by rfl⟩ : syracuseStep 953147 = 1429721) B1429721
theorem B953207 : Blo 634301 953207 := bstep (se 1 (by rfl) ⟨714905, by rfl⟩ : syracuseStep 953207 = 1429811) B1429811
theorem B953231 : Blo 634301 953231 := bstep (se 1 (by rfl) ⟨714923, by rfl⟩ : syracuseStep 953231 = 1429847) B1429847
theorem B953273 : Blo 634301 953273 := bstep (se 2 (by rfl) ⟨357477, by rfl⟩ : syracuseStep 953273 = 714955) B714955
theorem B953351 : Blo 634301 953351 := bstep (se 1 (by rfl) ⟨715013, by rfl⟩ : syracuseStep 953351 = 1430027) B1430027
theorem B953387 : Blo 634301 953387 := bstep (se 1 (by rfl) ⟨715040, by rfl⟩ : syracuseStep 953387 = 1430081) B1430081
theorem B3214403 : Blo 634301 3214403 := bstep (se 1 (by rfl) ⟨2410802, by rfl⟩ : syracuseStep 3214403 = 4821605) B4821605
theorem B953417 : Blo 634301 953417 := bstep (se 2 (by rfl) ⟨357531, by rfl⟩ : syracuseStep 953417 = 715063) B715063
theorem B953531 : Blo 634301 953531 := bstep (se 1 (by rfl) ⟨715148, by rfl⟩ : syracuseStep 953531 = 1430297) B1430297
theorem B953591 : Blo 634301 953591 := bstep (se 1 (by rfl) ⟨715193, by rfl⟩ : syracuseStep 953591 = 1430387) B1430387
theorem B953615 : Blo 634301 953615 := bstep (se 1 (by rfl) ⟨715211, by rfl⟩ : syracuseStep 953615 = 1430423) B1430423
theorem B953657 : Blo 634301 953657 := bstep (se 2 (by rfl) ⟨357621, by rfl⟩ : syracuseStep 953657 = 715243) B715243
theorem B3870011 : Blo 634301 3870011 := bstep (se 1 (by rfl) ⟨2902508, by rfl⟩ : syracuseStep 3870011 = 5805017) B5805017
theorem B3214727 : Blo 634301 3214727 := bstep (se 1 (by rfl) ⟨2411045, by rfl⟩ : syracuseStep 3214727 = 4822091) B4822091
theorem B953735 : Blo 634301 953735 := bstep (se 1 (by rfl) ⟨715301, by rfl⟩ : syracuseStep 953735 = 1430603) B1430603
theorem B953771 : Blo 634301 953771 := bstep (se 1 (by rfl) ⟨715328, by rfl⟩ : syracuseStep 953771 = 1430657) B1430657
theorem B953801 : Blo 634301 953801 := bstep (se 2 (by rfl) ⟨357675, by rfl⟩ : syracuseStep 953801 = 715351) B715351
theorem B1609217 : Blo 634301 1609217 := bstep (se 2 (by rfl) ⟨603456, by rfl⟩ : syracuseStep 1609217 = 1206913) B1206913
theorem B2035243 : Blo 634301 2035243 := bstep (se 1 (by rfl) ⟨1526432, by rfl⟩ : syracuseStep 2035243 = 3052865) B3052865
theorem B953915 : Blo 634301 953915 := bstep (se 1 (by rfl) ⟨715436, by rfl⟩ : syracuseStep 953915 = 1430873) B1430873
theorem B7179853 : Blo 634301 7179853 := bstep (se 3 (by rfl) ⟨1346222, by rfl⟩ : syracuseStep 7179853 = 2692445) B2692445
theorem B953975 : Blo 634301 953975 := bstep (se 1 (by rfl) ⟨715481, by rfl⟩ : syracuseStep 953975 = 1430963) B1430963
theorem B953999 : Blo 634301 953999 := bstep (se 1 (by rfl) ⟨715499, by rfl⟩ : syracuseStep 953999 = 1430999) B1430999
theorem B8261297 : Blo 634301 8261297 := bstep (se 2 (by rfl) ⟨3097986, by rfl⟩ : syracuseStep 8261297 = 6195973) B6195973
theorem B954041 : Blo 634301 954041 := bstep (se 2 (by rfl) ⟨357765, by rfl⟩ : syracuseStep 954041 = 715531) B715531
theorem B954119 : Blo 634301 954119 := bstep (se 1 (by rfl) ⟨715589, by rfl⟩ : syracuseStep 954119 = 1431179) B1431179
theorem B954155 : Blo 634301 954155 := bstep (se 1 (by rfl) ⟨715616, by rfl⟩ : syracuseStep 954155 = 1431233) B1431233
theorem B954185 : Blo 634301 954185 := bstep (se 2 (by rfl) ⟨357819, by rfl⟩ : syracuseStep 954185 = 715639) B715639
theorem B1609591 : Blo 634301 1609591 := bstep (se 1 (by rfl) ⟨1207193, by rfl⟩ : syracuseStep 1609591 = 2414387) B2414387
theorem B2297753 : Blo 634301 2297753 := bstep (se 2 (by rfl) ⟨861657, by rfl⟩ : syracuseStep 2297753 = 1723315) B1723315
theorem B954299 : Blo 634301 954299 := bstep (se 1 (by rfl) ⟨715724, by rfl⟩ : syracuseStep 954299 = 1431449) B1431449
theorem B954359 : Blo 634301 954359 := bstep (se 1 (by rfl) ⟨715769, by rfl⟩ : syracuseStep 954359 = 1431539) B1431539
theorem B954383 : Blo 634301 954383 := bstep (se 1 (by rfl) ⟨715787, by rfl⟩ : syracuseStep 954383 = 1431575) B1431575
theorem B954425 : Blo 634301 954425 := bstep (se 2 (by rfl) ⟨357909, by rfl⟩ : syracuseStep 954425 = 715819) B715819
theorem B954503 : Blo 634301 954503 := bstep (se 1 (by rfl) ⟨715877, by rfl⟩ : syracuseStep 954503 = 1431755) B1431755
theorem B954539 : Blo 634301 954539 := bstep (se 1 (by rfl) ⟨715904, by rfl⟩ : syracuseStep 954539 = 1431809) B1431809
theorem B954569 : Blo 634301 954569 := bstep (se 2 (by rfl) ⟨357963, by rfl⟩ : syracuseStep 954569 = 715927) B715927
theorem B2298127 : Blo 634301 2298127 := bstep (se 1 (by rfl) ⟨1723595, by rfl⟩ : syracuseStep 2298127 = 3447191) B3447191
theorem B1610027 : Blo 634301 1610027 := bstep (se 1 (by rfl) ⟨1207520, by rfl⟩ : syracuseStep 1610027 = 2415041) B2415041
theorem B954683 : Blo 634301 954683 := bstep (se 1 (by rfl) ⟨716012, by rfl⟩ : syracuseStep 954683 = 1432025) B1432025
theorem B954743 : Blo 634301 954743 := bstep (se 1 (by rfl) ⟨716057, by rfl⟩ : syracuseStep 954743 = 1432115) B1432115
theorem B954767 : Blo 634301 954767 := bstep (se 1 (by rfl) ⟨716075, by rfl⟩ : syracuseStep 954767 = 1432151) B1432151
theorem B954809 : Blo 634301 954809 := bstep (se 2 (by rfl) ⟨358053, by rfl⟩ : syracuseStep 954809 = 716107) B716107
theorem B954887 : Blo 634301 954887 := bstep (se 1 (by rfl) ⟨716165, by rfl⟩ : syracuseStep 954887 = 1432331) B1432331
theorem B954923 : Blo 634301 954923 := bstep (se 1 (by rfl) ⟨716192, by rfl⟩ : syracuseStep 954923 = 1432385) B1432385
theorem B1806907 : Blo 634301 1806907 := bstep (se 1 (by rfl) ⟨1355180, by rfl⟩ : syracuseStep 1806907 = 2710361) B2710361
theorem B954953 : Blo 634301 954953 := bstep (se 2 (by rfl) ⟨358107, by rfl⟩ : syracuseStep 954953 = 716215) B716215
theorem B955067 : Blo 634301 955067 := bstep (se 1 (by rfl) ⟨716300, by rfl⟩ : syracuseStep 955067 = 1432601) B1432601
theorem B7344857 : Blo 634301 7344857 := bstep (se 2 (by rfl) ⟨2754321, by rfl⟩ : syracuseStep 7344857 = 5508643) B5508643
theorem B955127 : Blo 634301 955127 := bstep (se 1 (by rfl) ⟨716345, by rfl⟩ : syracuseStep 955127 = 1432691) B1432691
theorem B955151 : Blo 634301 955151 := bstep (se 1 (by rfl) ⟨716363, by rfl⟩ : syracuseStep 955151 = 1432727) B1432727
theorem B1086251 : Blo 634301 1086251 := bstep (se 1 (by rfl) ⟨814688, by rfl⟩ : syracuseStep 1086251 = 1629377) B1629377
theorem B955193 : Blo 634301 955193 := bstep (se 2 (by rfl) ⟨358197, by rfl⟩ : syracuseStep 955193 = 716395) B716395
theorem B955271 : Blo 634301 955271 := bstep (se 1 (by rfl) ⟨716453, by rfl⟩ : syracuseStep 955271 = 1432907) B1432907
theorem B955307 : Blo 634301 955307 := bstep (se 1 (by rfl) ⟨716480, by rfl⟩ : syracuseStep 955307 = 1432961) B1432961
theorem B955337 : Blo 634301 955337 := bstep (se 2 (by rfl) ⟨358251, by rfl⟩ : syracuseStep 955337 = 716503) B716503
theorem B955451 : Blo 634301 955451 := bstep (se 1 (by rfl) ⟨716588, by rfl⟩ : syracuseStep 955451 = 1433177) B1433177
theorem B4068413 : Blo 634301 4068413 := bstep (se 3 (by rfl) ⟨762827, by rfl⟩ : syracuseStep 4068413 = 1525655) B1525655
theorem B1610867 : Blo 634301 1610867 := bstep (se 1 (by rfl) ⟨1208150, by rfl⟩ : syracuseStep 1610867 = 2416301) B2416301
theorem B955511 : Blo 634301 955511 := bstep (se 1 (by rfl) ⟨716633, by rfl⟩ : syracuseStep 955511 = 1433267) B1433267
theorem B1610887 : Blo 634301 1610887 := bstep (se 1 (by rfl) ⟨1208165, by rfl⟩ : syracuseStep 1610887 = 2416331) B2416331
theorem B955535 : Blo 634301 955535 := bstep (se 1 (by rfl) ⟨716651, by rfl⟩ : syracuseStep 955535 = 1433303) B1433303
theorem B955577 : Blo 634301 955577 := bstep (se 2 (by rfl) ⟨358341, by rfl⟩ : syracuseStep 955577 = 716683) B716683
theorem B955655 : Blo 634301 955655 := bstep (se 1 (by rfl) ⟨716741, by rfl⟩ : syracuseStep 955655 = 1433483) B1433483
theorem B955691 : Blo 634301 955691 := bstep (se 1 (by rfl) ⟨716768, by rfl⟩ : syracuseStep 955691 = 1433537) B1433537
theorem B955721 : Blo 634301 955721 := bstep (se 2 (by rfl) ⟨358395, by rfl⟩ : syracuseStep 955721 = 716791) B716791
theorem B1611161 : Blo 634301 1611161 := bstep (se 2 (by rfl) ⟨604185, by rfl⟩ : syracuseStep 1611161 = 1208371) B1208371
theorem B955835 : Blo 634301 955835 := bstep (se 1 (by rfl) ⟨716876, by rfl⟩ : syracuseStep 955835 = 1433753) B1433753
theorem B955895 : Blo 634301 955895 := bstep (se 1 (by rfl) ⟨716921, by rfl⟩ : syracuseStep 955895 = 1433843) B1433843
theorem B955919 : Blo 634301 955919 := bstep (se 1 (by rfl) ⟨716939, by rfl⟩ : syracuseStep 955919 = 1433879) B1433879
theorem B955961 : Blo 634301 955961 := bstep (se 2 (by rfl) ⟨358485, by rfl⟩ : syracuseStep 955961 = 716971) B716971
theorem B1611323 : Blo 634301 1611323 := bstep (se 1 (by rfl) ⟨1208492, by rfl⟩ : syracuseStep 1611323 = 2416985) B2416985
theorem B3872323 : Blo 634301 3872323 := bstep (se 1 (by rfl) ⟨2904242, by rfl⟩ : syracuseStep 3872323 = 5808485) B5808485
theorem B956039 : Blo 634301 956039 := bstep (se 1 (by rfl) ⟨717029, by rfl⟩ : syracuseStep 956039 = 1434059) B1434059
theorem B956075 : Blo 634301 956075 := bstep (se 1 (by rfl) ⟨717056, by rfl⟩ : syracuseStep 956075 = 1434113) B1434113
theorem B1808057 : Blo 634301 1808057 := bstep (se 2 (by rfl) ⟨678021, by rfl⟩ : syracuseStep 1808057 = 1356043) B1356043
theorem B956105 : Blo 634301 956105 := bstep (se 2 (by rfl) ⟨358539, by rfl⟩ : syracuseStep 956105 = 717079) B717079
theorem B1611535 : Blo 634301 1611535 := bstep (se 1 (by rfl) ⟨1208651, by rfl⟩ : syracuseStep 1611535 = 2417303) B2417303
theorem B1087291 : Blo 634301 1087291 := bstep (se 1 (by rfl) ⟨815468, by rfl⟩ : syracuseStep 1087291 = 1630937) B1630937
theorem B956219 : Blo 634301 956219 := bstep (se 1 (by rfl) ⟨717164, by rfl⟩ : syracuseStep 956219 = 1434329) B1434329
theorem B956279 : Blo 634301 956279 := bstep (se 1 (by rfl) ⟨717209, by rfl⟩ : syracuseStep 956279 = 1434419) B1434419
theorem B956303 : Blo 634301 956303 := bstep (se 1 (by rfl) ⟨717227, by rfl⟩ : syracuseStep 956303 = 1434455) B1434455
theorem B956345 : Blo 634301 956345 := bstep (se 2 (by rfl) ⟨358629, by rfl⟩ : syracuseStep 956345 = 717259) B717259
theorem B956423 : Blo 634301 956423 := bstep (se 1 (by rfl) ⟨717317, by rfl⟩ : syracuseStep 956423 = 1434635) B1434635
theorem B1808399 : Blo 634301 1808399 := bstep (se 1 (by rfl) ⟨1356299, by rfl⟩ : syracuseStep 1808399 = 2712599) B2712599
theorem B4823063 : Blo 634301 4823063 := bstep (se 1 (by rfl) ⟨3617297, by rfl⟩ : syracuseStep 4823063 = 7234595) B7234595
theorem B1611809 : Blo 634301 1611809 := bstep (se 2 (by rfl) ⟨604428, by rfl⟩ : syracuseStep 1611809 = 1208857) B1208857
theorem B956459 : Blo 634301 956459 := bstep (se 1 (by rfl) ⟨717344, by rfl⟩ : syracuseStep 956459 = 1434689) B1434689
theorem B956489 : Blo 634301 956489 := bstep (se 2 (by rfl) ⟨358683, by rfl⟩ : syracuseStep 956489 = 717367) B717367
theorem B956603 : Blo 634301 956603 := bstep (se 1 (by rfl) ⟨717452, by rfl⟩ : syracuseStep 956603 = 1434905) B1434905
theorem B956663 : Blo 634301 956663 := bstep (se 1 (by rfl) ⟨717497, by rfl⟩ : syracuseStep 956663 = 1434995) B1434995
theorem B956687 : Blo 634301 956687 := bstep (se 1 (by rfl) ⟨717515, by rfl⟩ : syracuseStep 956687 = 1435031) B1435031
theorem B956729 : Blo 634301 956729 := bstep (se 2 (by rfl) ⟨358773, by rfl⟩ : syracuseStep 956729 = 717547) B717547
theorem B956807 : Blo 634301 956807 := bstep (se 1 (by rfl) ⟨717605, by rfl⟩ : syracuseStep 956807 = 1435211) B1435211
theorem B956843 : Blo 634301 956843 := bstep (se 1 (by rfl) ⟨717632, by rfl⟩ : syracuseStep 956843 = 1435265) B1435265
theorem B956873 : Blo 634301 956873 := bstep (se 2 (by rfl) ⟨358827, by rfl⟩ : syracuseStep 956873 = 717655) B717655
theorem B956987 : Blo 634301 956987 := bstep (se 1 (by rfl) ⟨717740, by rfl⟩ : syracuseStep 956987 = 1435481) B1435481
theorem B1841779 : Blo 634301 1841779 := bstep (se 1 (by rfl) ⟨1381334, by rfl⟩ : syracuseStep 1841779 = 2762669) B2762669
theorem B957047 : Blo 634301 957047 := bstep (se 1 (by rfl) ⟨717785, by rfl⟩ : syracuseStep 957047 = 1435571) B1435571
theorem B957071 : Blo 634301 957071 := bstep (se 1 (by rfl) ⟨717803, by rfl⟩ : syracuseStep 957071 = 1435607) B1435607
theorem B957113 : Blo 634301 957113 := bstep (se 2 (by rfl) ⟨358917, by rfl⟩ : syracuseStep 957113 = 717835) B717835
theorem B957191 : Blo 634301 957191 := bstep (se 1 (by rfl) ⟨717893, by rfl⟩ : syracuseStep 957191 = 1435787) B1435787
theorem B11606819 : Blo 634301 11606819 := bstep (se 1 (by rfl) ⟨8705114, by rfl⟩ : syracuseStep 11606819 = 17410229) B17410229
theorem B957227 : Blo 634301 957227 := bstep (se 1 (by rfl) ⟨717920, by rfl⟩ : syracuseStep 957227 = 1435841) B1435841
theorem B1940285 : Blo 634301 1940285 := bstep (se 3 (by rfl) ⟨363803, by rfl⟩ : syracuseStep 1940285 = 727607) B727607
theorem B957257 : Blo 634301 957257 := bstep (se 2 (by rfl) ⟨358971, by rfl⟩ : syracuseStep 957257 = 717943) B717943
theorem B3218291 : Blo 634301 3218291 := bstep (se 1 (by rfl) ⟨2413718, by rfl⟩ : syracuseStep 3218291 = 4827437) B4827437
theorem B1809287 : Blo 634301 1809287 := bstep (se 1 (by rfl) ⟨1356965, by rfl⟩ : syracuseStep 1809287 = 2713931) B2713931
theorem B957371 : Blo 634301 957371 := bstep (se 1 (by rfl) ⟨718028, by rfl⟩ : syracuseStep 957371 = 1436057) B1436057
theorem B957431 : Blo 634301 957431 := bstep (se 1 (by rfl) ⟨718073, by rfl⟩ : syracuseStep 957431 = 1436147) B1436147
theorem B1612811 : Blo 634301 1612811 := bstep (se 1 (by rfl) ⟨1209608, by rfl⟩ : syracuseStep 1612811 = 2419217) B2419217
theorem B1809469 : Blo 634301 1809469 := bstep (se 3 (by rfl) ⟨339275, by rfl⟩ : syracuseStep 1809469 = 678551) B678551
theorem B4365373 : Blo 634301 4365373 := bstep (se 3 (by rfl) ⟨818507, by rfl⟩ : syracuseStep 4365373 = 1637015) B1637015
theorem B14097539 : Blo 634301 14097539 := bstep (se 1 (by rfl) ⟨10573154, by rfl⟩ : syracuseStep 14097539 = 21146309) B21146309
theorem B1809697 : Blo 634301 1809697 := bstep (se 2 (by rfl) ⟨678636, by rfl⟩ : syracuseStep 1809697 = 1357273) B1357273
theorem B3218777 : Blo 634301 3218777 := bstep (se 2 (by rfl) ⟨1207041, by rfl⟩ : syracuseStep 3218777 = 2414083) B2414083
theorem B3317201 : Blo 634301 3317201 := bstep (se 2 (by rfl) ⟨1243950, by rfl⟩ : syracuseStep 3317201 = 2487901) B2487901
theorem B3055171 : Blo 634301 3055171 := bstep (se 1 (by rfl) ⟨2291378, by rfl⟩ : syracuseStep 3055171 = 4582757) B4582757
theorem B1810039 : Blo 634301 1810039 := bstep (se 1 (by rfl) ⟨1357529, by rfl⟩ : syracuseStep 1810039 = 2715059) B2715059
theorem B1613459 : Blo 634301 1613459 := bstep (se 1 (by rfl) ⟨1210094, by rfl⟩ : syracuseStep 1613459 = 2420189) B2420189
theorem B10886885 : Blo 634301 10886885 := bstep (se 4 (by rfl) ⟨1020645, by rfl⟩ : syracuseStep 10886885 = 2041291) B2041291
theorem B991033 : Blo 634301 991033 := bstep (se 2 (by rfl) ⟨371637, by rfl⟩ : syracuseStep 991033 = 743275) B743275
theorem B1613753 : Blo 634301 1613753 := bstep (se 2 (by rfl) ⟨605157, by rfl⟩ : syracuseStep 1613753 = 1210315) B1210315
theorem B8167625 : Blo 634301 8167625 := bstep (se 2 (by rfl) ⟨3062859, by rfl⟩ : syracuseStep 8167625 = 6125719) B6125719
theorem B1810973 : Blo 634301 1810973 := bstep (se 3 (by rfl) ⟨339557, by rfl⟩ : syracuseStep 1810973 = 679115) B679115
theorem B14885441 : Blo 634301 14885441 := bstep (se 2 (by rfl) ⟨5582040, by rfl⟩ : syracuseStep 14885441 = 11164081) B11164081
theorem B1614451 : Blo 634301 1614451 := bstep (se 1 (by rfl) ⟨1210838, by rfl⟩ : syracuseStep 1614451 = 2421677) B2421677
theorem B1614593 : Blo 634301 1614593 := bstep (se 2 (by rfl) ⟨605472, by rfl⟩ : syracuseStep 1614593 = 1210945) B1210945
theorem B1811315 : Blo 634301 1811315 := bstep (se 1 (by rfl) ⟨1358486, by rfl⟩ : syracuseStep 1811315 = 2716973) B2716973
theorem B1615049 : Blo 634301 1615049 := bstep (se 2 (by rfl) ⟨605643, by rfl⟩ : syracuseStep 1615049 = 1211287) B1211287
theorem B1811771 : Blo 634301 1811771 := bstep (se 1 (by rfl) ⟨1358828, by rfl⟩ : syracuseStep 1811771 = 2717657) B2717657
theorem B1287571 : Blo 634301 1287571 := bstep (se 1 (by rfl) ⟨965678, by rfl⟩ : syracuseStep 1287571 = 1931357) B1931357
theorem B3220883 : Blo 634301 3220883 := bstep (se 1 (by rfl) ⟨2415662, by rfl⟩ : syracuseStep 3220883 = 4831325) B4831325
theorem B1615403 : Blo 634301 1615403 := bstep (se 1 (by rfl) ⟨1211552, by rfl⟩ : syracuseStep 1615403 = 2423105) B2423105
theorem B4597519 : Blo 634301 4597519 := bstep (se 1 (by rfl) ⟨3448139, by rfl⟩ : syracuseStep 4597519 = 6896279) B6896279
theorem B10856267 : Blo 634301 10856267 := bstep (se 1 (by rfl) ⟨8142200, by rfl⟩ : syracuseStep 10856267 = 16284401) B16284401
theorem B1747003 : Blo 634301 1747003 := bstep (se 1 (by rfl) ⟨1310252, by rfl⟩ : syracuseStep 1747003 = 2620505) B2620505
theorem B3615293 : Blo 634301 3615293 := bstep (se 3 (by rfl) ⟨677867, by rfl⟩ : syracuseStep 3615293 = 1355735) B1355735
theorem B6204161 : Blo 634301 6204161 := bstep (se 2 (by rfl) ⟨2326560, by rfl⟩ : syracuseStep 6204161 = 4653121) B4653121
theorem B764687 : Blo 634301 764687 := bstep (se 1 (by rfl) ⟨573515, by rfl⟩ : syracuseStep 764687 = 1147031) B1147031
theorem B3091385 : Blo 634301 3091385 := bstep (se 2 (by rfl) ⟨1159269, by rfl⟩ : syracuseStep 3091385 = 2318539) B2318539
theorem B3779531 : Blo 634301 3779531 := bstep (se 1 (by rfl) ⟨2834648, by rfl⟩ : syracuseStep 3779531 = 5669297) B5669297
theorem B928903 : Blo 634301 928903 := bstep (se 1 (by rfl) ⟨696677, by rfl⟩ : syracuseStep 928903 = 1393355) B1393355
theorem B3616001 : Blo 634301 3616001 := bstep (se 2 (by rfl) ⟨1356000, by rfl⟩ : syracuseStep 3616001 = 2712001) B2712001
theorem B2043137 : Blo 634301 2043137 := bstep (se 2 (by rfl) ⟨766176, by rfl⟩ : syracuseStep 2043137 = 1532353) B1532353
theorem B6106499 : Blo 634301 6106499 := bstep (se 1 (by rfl) ⟨4579874, by rfl⟩ : syracuseStep 6106499 = 9159749) B9159749
theorem B634375 : Blo 634301 634375 := bstep (se 1 (by rfl) ⟨475781, by rfl⟩ : syracuseStep 634375 = 951563) B951563
theorem B634383 : Blo 634301 634383 := bstep (se 1 (by rfl) ⟨475787, by rfl⟩ : syracuseStep 634383 = 951575) B951575
theorem B634427 : Blo 634301 634427 := bstep (se 1 (by rfl) ⟨475820, by rfl⟩ : syracuseStep 634427 = 951641) B951641
theorem B634503 : Blo 634301 634503 := bstep (se 1 (by rfl) ⟨475877, by rfl⟩ : syracuseStep 634503 = 951755) B951755
theorem B634511 : Blo 634301 634511 := bstep (se 1 (by rfl) ⟨475883, by rfl⟩ : syracuseStep 634511 = 951767) B951767
theorem B634555 : Blo 634301 634555 := bstep (se 1 (by rfl) ⟨475916, by rfl⟩ : syracuseStep 634555 = 951833) B951833
theorem B4075201 : Blo 634301 4075201 := bstep (se 2 (by rfl) ⟨1528200, by rfl⟩ : syracuseStep 4075201 = 3056401) B3056401
theorem B634631 : Blo 634301 634631 := bstep (se 1 (by rfl) ⟨475973, by rfl⟩ : syracuseStep 634631 = 951947) B951947
theorem B634639 : Blo 634301 634639 := bstep (se 1 (by rfl) ⟨475979, by rfl⟩ : syracuseStep 634639 = 951959) B951959
theorem B634683 : Blo 634301 634683 := bstep (se 1 (by rfl) ⟨476012, by rfl⟩ : syracuseStep 634683 = 952025) B952025
theorem B634759 : Blo 634301 634759 := bstep (se 1 (by rfl) ⟨476069, by rfl⟩ : syracuseStep 634759 = 952139) B952139
theorem B634767 : Blo 634301 634767 := bstep (se 1 (by rfl) ⟨476075, by rfl⟩ : syracuseStep 634767 = 952151) B952151
theorem B634811 : Blo 634301 634811 := bstep (se 1 (by rfl) ⟨476108, by rfl⟩ : syracuseStep 634811 = 952217) B952217
theorem B634887 : Blo 634301 634887 := bstep (se 1 (by rfl) ⟨476165, by rfl⟩ : syracuseStep 634887 = 952331) B952331
theorem B634895 : Blo 634301 634895 := bstep (se 1 (by rfl) ⟨476171, by rfl⟩ : syracuseStep 634895 = 952343) B952343
theorem B634939 : Blo 634301 634939 := bstep (se 1 (by rfl) ⟨476204, by rfl⟩ : syracuseStep 634939 = 952409) B952409
theorem B635015 : Blo 634301 635015 := bstep (se 1 (by rfl) ⟨476261, by rfl⟩ : syracuseStep 635015 = 952523) B952523
theorem B1814663 : Blo 634301 1814663 := bstep (se 1 (by rfl) ⟨1360997, by rfl⟩ : syracuseStep 1814663 = 2721995) B2721995
theorem B635023 : Blo 634301 635023 := bstep (se 1 (by rfl) ⟨476267, by rfl⟩ : syracuseStep 635023 = 952535) B952535
theorem B635067 : Blo 634301 635067 := bstep (se 1 (by rfl) ⟨476300, by rfl⟩ : syracuseStep 635067 = 952601) B952601
theorem B635143 : Blo 634301 635143 := bstep (se 1 (by rfl) ⟨476357, by rfl⟩ : syracuseStep 635143 = 952715) B952715
theorem B635151 : Blo 634301 635151 := bstep (se 1 (by rfl) ⟨476363, by rfl⟩ : syracuseStep 635151 = 952727) B952727
theorem B635195 : Blo 634301 635195 := bstep (se 1 (by rfl) ⟨476396, by rfl⟩ : syracuseStep 635195 = 952793) B952793
theorem B635271 : Blo 634301 635271 := bstep (se 1 (by rfl) ⟨476453, by rfl⟩ : syracuseStep 635271 = 952907) B952907
theorem B635279 : Blo 634301 635279 := bstep (se 1 (by rfl) ⟨476459, by rfl⟩ : syracuseStep 635279 = 952919) B952919
theorem B2142611 : Blo 634301 2142611 := bstep (se 1 (by rfl) ⟨1606958, by rfl⟩ : syracuseStep 2142611 = 3213917) B3213917
theorem B3223961 : Blo 634301 3223961 := bstep (se 2 (by rfl) ⟨1208985, by rfl⟩ : syracuseStep 3223961 = 2417971) B2417971
theorem B635323 : Blo 634301 635323 := bstep (se 1 (by rfl) ⟨476492, by rfl⟩ : syracuseStep 635323 = 952985) B952985
theorem B635399 : Blo 634301 635399 := bstep (se 1 (by rfl) ⟨476549, by rfl⟩ : syracuseStep 635399 = 953099) B953099
theorem B635407 : Blo 634301 635407 := bstep (se 1 (by rfl) ⟨476555, by rfl⟩ : syracuseStep 635407 = 953111) B953111
theorem B635451 : Blo 634301 635451 := bstep (se 1 (by rfl) ⟨476588, by rfl⟩ : syracuseStep 635451 = 953177) B953177
theorem B635527 : Blo 634301 635527 := bstep (se 1 (by rfl) ⟨476645, by rfl⟩ : syracuseStep 635527 = 953291) B953291
theorem B635535 : Blo 634301 635535 := bstep (se 1 (by rfl) ⟨476651, by rfl⟩ : syracuseStep 635535 = 953303) B953303
theorem B12235445 : Blo 634301 12235445 := bstep (se 5 (by rfl) ⟨573536, by rfl⟩ : syracuseStep 12235445 = 1147073) B1147073
theorem B635579 : Blo 634301 635579 := bstep (se 1 (by rfl) ⟨476684, by rfl⟩ : syracuseStep 635579 = 953369) B953369
theorem B635655 : Blo 634301 635655 := bstep (se 1 (by rfl) ⟨476741, by rfl⟩ : syracuseStep 635655 = 953483) B953483
theorem B635663 : Blo 634301 635663 := bstep (se 1 (by rfl) ⟨476747, by rfl⟩ : syracuseStep 635663 = 953495) B953495
theorem B635707 : Blo 634301 635707 := bstep (se 1 (by rfl) ⟨476780, by rfl⟩ : syracuseStep 635707 = 953561) B953561
theorem B635783 : Blo 634301 635783 := bstep (se 1 (by rfl) ⟨476837, by rfl⟩ : syracuseStep 635783 = 953675) B953675
theorem B635791 : Blo 634301 635791 := bstep (se 1 (by rfl) ⟨476843, by rfl⟩ : syracuseStep 635791 = 953687) B953687
theorem B635835 : Blo 634301 635835 := bstep (se 1 (by rfl) ⟨476876, by rfl⟩ : syracuseStep 635835 = 953753) B953753
theorem B635911 : Blo 634301 635911 := bstep (se 1 (by rfl) ⟨476933, by rfl⟩ : syracuseStep 635911 = 953867) B953867
theorem B635919 : Blo 634301 635919 := bstep (se 1 (by rfl) ⟨476939, by rfl⟩ : syracuseStep 635919 = 953879) B953879
theorem B635963 : Blo 634301 635963 := bstep (se 1 (by rfl) ⟨476972, by rfl⟩ : syracuseStep 635963 = 953945) B953945
theorem B8696965 : Blo 634301 8696965 := bstep (se 4 (by rfl) ⟨815340, by rfl⟩ : syracuseStep 8696965 = 1630681) B1630681
theorem B636039 : Blo 634301 636039 := bstep (se 1 (by rfl) ⟨477029, by rfl⟩ : syracuseStep 636039 = 954059) B954059
theorem B636047 : Blo 634301 636047 := bstep (se 1 (by rfl) ⟨477035, by rfl⟩ : syracuseStep 636047 = 954071) B954071
theorem B1717433 : Blo 634301 1717433 := bstep (se 2 (by rfl) ⟨644037, by rfl⟩ : syracuseStep 1717433 = 1288075) B1288075
theorem B636091 : Blo 634301 636091 := bstep (se 1 (by rfl) ⟨477068, by rfl⟩ : syracuseStep 636091 = 954137) B954137
theorem B636167 : Blo 634301 636167 := bstep (se 1 (by rfl) ⟨477125, by rfl⟩ : syracuseStep 636167 = 954251) B954251
theorem B636175 : Blo 634301 636175 := bstep (se 1 (by rfl) ⟨477131, by rfl⟩ : syracuseStep 636175 = 954263) B954263
theorem B636219 : Blo 634301 636219 := bstep (se 1 (by rfl) ⟨477164, by rfl⟩ : syracuseStep 636219 = 954329) B954329
theorem B636295 : Blo 634301 636295 := bstep (se 1 (by rfl) ⟨477221, by rfl⟩ : syracuseStep 636295 = 954443) B954443
theorem B636303 : Blo 634301 636303 := bstep (se 1 (by rfl) ⟨477227, by rfl⟩ : syracuseStep 636303 = 954455) B954455
theorem B636347 : Blo 634301 636347 := bstep (se 1 (by rfl) ⟨477260, by rfl⟩ : syracuseStep 636347 = 954521) B954521
theorem B636423 : Blo 634301 636423 := bstep (se 1 (by rfl) ⟨477317, by rfl⟩ : syracuseStep 636423 = 954635) B954635
theorem B636431 : Blo 634301 636431 := bstep (se 1 (by rfl) ⟨477323, by rfl⟩ : syracuseStep 636431 = 954647) B954647
theorem B636475 : Blo 634301 636475 := bstep (se 1 (by rfl) ⟨477356, by rfl⟩ : syracuseStep 636475 = 954713) B954713
theorem B3618391 : Blo 634301 3618391 := bstep (se 1 (by rfl) ⟨2713793, by rfl⟩ : syracuseStep 3618391 = 5427587) B5427587
theorem B4830839 : Blo 634301 4830839 := bstep (se 1 (by rfl) ⟨3623129, by rfl⟩ : syracuseStep 4830839 = 7246259) B7246259
theorem B636551 : Blo 634301 636551 := bstep (se 1 (by rfl) ⟨477413, by rfl⟩ : syracuseStep 636551 = 954827) B954827
theorem B636559 : Blo 634301 636559 := bstep (se 1 (by rfl) ⟨477419, by rfl⟩ : syracuseStep 636559 = 954839) B954839
theorem B636603 : Blo 634301 636603 := bstep (se 1 (by rfl) ⟨477452, by rfl⟩ : syracuseStep 636603 = 954905) B954905
theorem B636679 : Blo 634301 636679 := bstep (se 1 (by rfl) ⟨477509, by rfl⟩ : syracuseStep 636679 = 955019) B955019
theorem B2144015 : Blo 634301 2144015 := bstep (se 1 (by rfl) ⟨1608011, by rfl⟩ : syracuseStep 2144015 = 3216023) B3216023
theorem B636687 : Blo 634301 636687 := bstep (se 1 (by rfl) ⟨477515, by rfl⟩ : syracuseStep 636687 = 955031) B955031
theorem B636731 : Blo 634301 636731 := bstep (se 1 (by rfl) ⟨477548, by rfl⟩ : syracuseStep 636731 = 955097) B955097
theorem B636807 : Blo 634301 636807 := bstep (se 1 (by rfl) ⟨477605, by rfl⟩ : syracuseStep 636807 = 955211) B955211
theorem B636815 : Blo 634301 636815 := bstep (se 1 (by rfl) ⟨477611, by rfl⟩ : syracuseStep 636815 = 955223) B955223
theorem B636859 : Blo 634301 636859 := bstep (se 1 (by rfl) ⟨477644, by rfl⟩ : syracuseStep 636859 = 955289) B955289
theorem B1816577 : Blo 634301 1816577 := bstep (se 2 (by rfl) ⟨681216, by rfl⟩ : syracuseStep 1816577 = 1362433) B1362433
theorem B636935 : Blo 634301 636935 := bstep (se 1 (by rfl) ⟨477701, by rfl⟩ : syracuseStep 636935 = 955403) B955403
theorem B636943 : Blo 634301 636943 := bstep (se 1 (by rfl) ⟨477707, by rfl⟩ : syracuseStep 636943 = 955415) B955415
theorem B2144285 : Blo 634301 2144285 := bstep (se 3 (by rfl) ⟨402053, by rfl⟩ : syracuseStep 2144285 = 804107) B804107
theorem B636987 : Blo 634301 636987 := bstep (se 1 (by rfl) ⟨477740, by rfl⟩ : syracuseStep 636987 = 955481) B955481
theorem B637063 : Blo 634301 637063 := bstep (se 1 (by rfl) ⟨477797, by rfl⟩ : syracuseStep 637063 = 955595) B955595
theorem B637071 : Blo 634301 637071 := bstep (se 1 (by rfl) ⟨477803, by rfl⟩ : syracuseStep 637071 = 955607) B955607
theorem B637115 : Blo 634301 637115 := bstep (se 1 (by rfl) ⟨477836, by rfl⟩ : syracuseStep 637115 = 955673) B955673
theorem B637191 : Blo 634301 637191 := bstep (se 1 (by rfl) ⟨477893, by rfl⟩ : syracuseStep 637191 = 955787) B955787
theorem B637199 : Blo 634301 637199 := bstep (se 1 (by rfl) ⟨477899, by rfl⟩ : syracuseStep 637199 = 955799) B955799
theorem B637243 : Blo 634301 637243 := bstep (se 1 (by rfl) ⟨477932, by rfl⟩ : syracuseStep 637243 = 955865) B955865
theorem B637319 : Blo 634301 637319 := bstep (se 1 (by rfl) ⟨477989, by rfl⟩ : syracuseStep 637319 = 955979) B955979
theorem B637327 : Blo 634301 637327 := bstep (se 1 (by rfl) ⟨477995, by rfl⟩ : syracuseStep 637327 = 955991) B955991
theorem B7256465 : Blo 634301 7256465 := bstep (se 2 (by rfl) ⟨2721174, by rfl⟩ : syracuseStep 7256465 = 5442349) B5442349
theorem B4077971 : Blo 634301 4077971 := bstep (se 1 (by rfl) ⟨3058478, by rfl⟩ : syracuseStep 4077971 = 6116957) B6116957
theorem B3684761 : Blo 634301 3684761 := bstep (se 2 (by rfl) ⟨1381785, by rfl⟩ : syracuseStep 3684761 = 2763571) B2763571
theorem B637371 : Blo 634301 637371 := bstep (se 1 (by rfl) ⟨478028, by rfl⟩ : syracuseStep 637371 = 956057) B956057
theorem B637447 : Blo 634301 637447 := bstep (se 1 (by rfl) ⟨478085, by rfl⟩ : syracuseStep 637447 = 956171) B956171
theorem B1718795 : Blo 634301 1718795 := bstep (se 1 (by rfl) ⟨1289096, by rfl⟩ : syracuseStep 1718795 = 2578193) B2578193
theorem B637455 : Blo 634301 637455 := bstep (se 1 (by rfl) ⟨478091, by rfl⟩ : syracuseStep 637455 = 956183) B956183
theorem B637499 : Blo 634301 637499 := bstep (se 1 (by rfl) ⟨478124, by rfl⟩ : syracuseStep 637499 = 956249) B956249
theorem B1817147 : Blo 634301 1817147 := bstep (se 1 (by rfl) ⟨1362860, by rfl⟩ : syracuseStep 1817147 = 2725721) B2725721
theorem B4831811 : Blo 634301 4831811 := bstep (se 1 (by rfl) ⟨3623858, by rfl⟩ : syracuseStep 4831811 = 7247717) B7247717
theorem B637575 : Blo 634301 637575 := bstep (se 1 (by rfl) ⟨478181, by rfl⟩ : syracuseStep 637575 = 956363) B956363
theorem B637583 : Blo 634301 637583 := bstep (se 1 (by rfl) ⟨478187, by rfl⟩ : syracuseStep 637583 = 956375) B956375
theorem B637627 : Blo 634301 637627 := bstep (se 1 (by rfl) ⟨478220, by rfl⟩ : syracuseStep 637627 = 956441) B956441
theorem B1358537 : Blo 634301 1358537 := bstep (se 2 (by rfl) ⟨509451, by rfl⟩ : syracuseStep 1358537 = 1018903) B1018903
theorem B637703 : Blo 634301 637703 := bstep (se 1 (by rfl) ⟨478277, by rfl⟩ : syracuseStep 637703 = 956555) B956555
theorem B637711 : Blo 634301 637711 := bstep (se 1 (by rfl) ⟨478283, by rfl⟩ : syracuseStep 637711 = 956567) B956567
theorem B1817387 : Blo 634301 1817387 := bstep (se 1 (by rfl) ⟨1363040, by rfl⟩ : syracuseStep 1817387 = 2726081) B2726081
theorem B637755 : Blo 634301 637755 := bstep (se 1 (by rfl) ⟨478316, by rfl⟩ : syracuseStep 637755 = 956633) B956633
theorem B637831 : Blo 634301 637831 := bstep (se 1 (by rfl) ⟨478373, by rfl⟩ : syracuseStep 637831 = 956747) B956747
theorem B637839 : Blo 634301 637839 := bstep (se 1 (by rfl) ⟨478379, by rfl⟩ : syracuseStep 637839 = 956759) B956759
theorem B1358777 : Blo 634301 1358777 := bstep (se 2 (by rfl) ⟨509541, by rfl⟩ : syracuseStep 1358777 = 1019083) B1019083
theorem B3226553 : Blo 634301 3226553 := bstep (se 2 (by rfl) ⟨1209957, by rfl⟩ : syracuseStep 3226553 = 2419915) B2419915
theorem B637883 : Blo 634301 637883 := bstep (se 1 (by rfl) ⟨478412, by rfl⟩ : syracuseStep 637883 = 956825) B956825
theorem B637959 : Blo 634301 637959 := bstep (se 1 (by rfl) ⟨478469, by rfl⟩ : syracuseStep 637959 = 956939) B956939
theorem B637967 : Blo 634301 637967 := bstep (se 1 (by rfl) ⟨478475, by rfl⟩ : syracuseStep 637967 = 956951) B956951
theorem B638011 : Blo 634301 638011 := bstep (se 1 (by rfl) ⟨478508, by rfl⟩ : syracuseStep 638011 = 957017) B957017
theorem B638087 : Blo 634301 638087 := bstep (se 1 (by rfl) ⟨478565, by rfl⟩ : syracuseStep 638087 = 957131) B957131
theorem B638095 : Blo 634301 638095 := bstep (se 1 (by rfl) ⟨478571, by rfl⟩ : syracuseStep 638095 = 957143) B957143
theorem B638139 : Blo 634301 638139 := bstep (se 1 (by rfl) ⟨478604, by rfl⟩ : syracuseStep 638139 = 957209) B957209
theorem B638215 : Blo 634301 638215 := bstep (se 1 (by rfl) ⟨478661, by rfl⟩ : syracuseStep 638215 = 957323) B957323
theorem B1359119 : Blo 634301 1359119 := bstep (se 1 (by rfl) ⟨1019339, by rfl⟩ : syracuseStep 1359119 = 2038679) B2038679
theorem B638223 : Blo 634301 638223 := bstep (se 1 (by rfl) ⟨478667, by rfl⟩ : syracuseStep 638223 = 957335) B957335
theorem B3063091 : Blo 634301 3063091 := bstep (se 1 (by rfl) ⟨2297318, by rfl⟩ : syracuseStep 3063091 = 4594637) B4594637
theorem B638267 : Blo 634301 638267 := bstep (se 1 (by rfl) ⟨478700, by rfl⟩ : syracuseStep 638267 = 957401) B957401
theorem B2145689 : Blo 634301 2145689 := bstep (se 2 (by rfl) ⟨804633, by rfl⟩ : syracuseStep 2145689 = 1609267) B1609267
theorem B1359289 : Blo 634301 1359289 := bstep (se 2 (by rfl) ⟨509733, by rfl⟩ : syracuseStep 1359289 = 1019467) B1019467
theorem B3620375 : Blo 634301 3620375 := bstep (se 1 (by rfl) ⟨2715281, by rfl⟩ : syracuseStep 3620375 = 5430563) B5430563
theorem B3096587 : Blo 634301 3096587 := bstep (se 1 (by rfl) ⟨2322440, by rfl⟩ : syracuseStep 3096587 = 4644881) B4644881
theorem B2146391 : Blo 634301 2146391 := bstep (se 1 (by rfl) ⟨1609793, by rfl⟩ : syracuseStep 2146391 = 3219587) B3219587
theorem B1360007 : Blo 634301 1360007 := bstep (se 1 (by rfl) ⟨1020005, by rfl⟩ : syracuseStep 1360007 = 2040011) B2040011
theorem B3227849 : Blo 634301 3227849 := bstep (se 2 (by rfl) ⟨1210443, by rfl⟩ : syracuseStep 3227849 = 2420887) B2420887
theorem B10895633 : Blo 634301 10895633 := bstep (se 2 (by rfl) ⟨4085862, by rfl⟩ : syracuseStep 10895633 = 8171725) B8171725
theorem B2408737 : Blo 634301 2408737 := bstep (se 2 (by rfl) ⟨903276, by rfl⟩ : syracuseStep 2408737 = 1806553) B1806553
theorem B803191 : Blo 634301 803191 := bstep (se 1 (by rfl) ⟨602393, by rfl⟩ : syracuseStep 803191 = 1204787) B1204787
theorem B1360417 : Blo 634301 1360417 := bstep (se 2 (by rfl) ⟨510156, by rfl⟩ : syracuseStep 1360417 = 1020313) B1020313
theorem B2146877 : Blo 634301 2146877 := bstep (se 3 (by rfl) ⟨402539, by rfl⟩ : syracuseStep 2146877 = 805079) B805079
theorem B6111845 : Blo 634301 6111845 := bstep (se 4 (by rfl) ⟨572985, by rfl⟩ : syracuseStep 6111845 = 1145971) B1145971
theorem B803515 : Blo 634301 803515 := bstep (se 1 (by rfl) ⟨602636, by rfl⟩ : syracuseStep 803515 = 1205273) B1205273
theorem B8274703 : Blo 634301 8274703 := bstep (se 1 (by rfl) ⟨6206027, by rfl⟩ : syracuseStep 8274703 = 12412055) B12412055
theorem B1360759 : Blo 634301 1360759 := bstep (se 1 (by rfl) ⟨1020569, by rfl⟩ : syracuseStep 1360759 = 2041139) B2041139
theorem B3490781 : Blo 634301 3490781 := bstep (se 3 (by rfl) ⟨654521, by rfl⟩ : syracuseStep 3490781 = 1309043) B1309043
theorem B2409709 : Blo 634301 2409709 := bstep (se 3 (by rfl) ⟨451820, by rfl⟩ : syracuseStep 2409709 = 903641) B903641
theorem B7259381 : Blo 634301 7259381 := bstep (se 5 (by rfl) ⟨340283, by rfl⟩ : syracuseStep 7259381 = 680567) B680567
theorem B2934049 : Blo 634301 2934049 := bstep (se 2 (by rfl) ⟨1100268, by rfl⟩ : syracuseStep 2934049 = 2200537) B2200537
theorem B1361195 : Blo 634301 1361195 := bstep (se 1 (by rfl) ⟨1020896, by rfl⟩ : syracuseStep 1361195 = 2041793) B2041793
theorem B2410013 : Blo 634301 2410013 := bstep (se 3 (by rfl) ⟨451877, by rfl⟩ : syracuseStep 2410013 = 903755) B903755
theorem B804487 : Blo 634301 804487 := bstep (se 1 (by rfl) ⟨603365, by rfl⟩ : syracuseStep 804487 = 1206731) B1206731
theorem B6899393 : Blo 634301 6899393 := bstep (se 2 (by rfl) ⟨2587272, by rfl⟩ : syracuseStep 6899393 = 5174545) B5174545
theorem B5162867 : Blo 634301 5162867 := bstep (se 1 (by rfl) ⟨3872150, by rfl⟩ : syracuseStep 5162867 = 7744301) B7744301
theorem B2606995 : Blo 634301 2606995 := bstep (se 1 (by rfl) ⟨1955246, by rfl⟩ : syracuseStep 2606995 = 3910493) B3910493
theorem B2148281 : Blo 634301 2148281 := bstep (se 2 (by rfl) ⟨805605, by rfl⟩ : syracuseStep 2148281 = 1611211) B1611211
theorem B1427471 : Blo 634301 1427471 := bstep (se 1 (by rfl) ⟨1070603, by rfl⟩ : syracuseStep 1427471 = 2141207) B2141207
theorem B1427489 : Blo 634301 1427489 := bstep (se 2 (by rfl) ⟨535308, by rfl⟩ : syracuseStep 1427489 = 1070617) B1070617
theorem B804907 : Blo 634301 804907 := bstep (se 1 (by rfl) ⟨603680, by rfl⟩ : syracuseStep 804907 = 1207361) B1207361
theorem B1525895 : Blo 634301 1525895 := bstep (se 1 (by rfl) ⟨1144421, by rfl⟩ : syracuseStep 1525895 = 2288843) B2288843
theorem B3360941 : Blo 634301 3360941 := bstep (se 3 (by rfl) ⟨630176, by rfl⟩ : syracuseStep 3360941 = 1260353) B1260353
theorem B13224181 : Blo 634301 13224181 := bstep (se 5 (by rfl) ⟨619883, by rfl⟩ : syracuseStep 13224181 = 1239767) B1239767
theorem B805135 : Blo 634301 805135 := bstep (se 1 (by rfl) ⟨603851, by rfl⟩ : syracuseStep 805135 = 1207703) B1207703
theorem B1427831 : Blo 634301 1427831 := bstep (se 1 (by rfl) ⟨1070873, by rfl⟩ : syracuseStep 1427831 = 2141747) B2141747
theorem B7719389 : Blo 634301 7719389 := bstep (se 3 (by rfl) ⟨1447385, by rfl⟩ : syracuseStep 7719389 = 2894771) B2894771
theorem B2148875 : Blo 634301 2148875 := bstep (se 1 (by rfl) ⟨1611656, by rfl⟩ : syracuseStep 2148875 = 3223313) B3223313
theorem B1428011 : Blo 634301 1428011 := bstep (se 1 (by rfl) ⟨1071008, by rfl⟩ : syracuseStep 1428011 = 2142017) B2142017
theorem B2148983 : Blo 634301 2148983 := bstep (se 1 (by rfl) ⟨1611737, by rfl⟩ : syracuseStep 2148983 = 3223475) B3223475
theorem B969401 : Blo 634301 969401 := bstep (se 2 (by rfl) ⟨363525, by rfl⟩ : syracuseStep 969401 = 727051) B727051
theorem B5163713 : Blo 634301 5163713 := bstep (se 2 (by rfl) ⟨1936392, by rfl⟩ : syracuseStep 5163713 = 3872785) B3872785
theorem B4836185 : Blo 634301 4836185 := bstep (se 2 (by rfl) ⟨1813569, by rfl⟩ : syracuseStep 4836185 = 3627139) B3627139
theorem B1428371 : Blo 634301 1428371 := bstep (se 1 (by rfl) ⟨1071278, by rfl⟩ : syracuseStep 1428371 = 2142557) B2142557
theorem B1362835 : Blo 634301 1362835 := bstep (se 1 (by rfl) ⟨1022126, by rfl⟩ : syracuseStep 1362835 = 2044253) B2044253
theorem B1428425 : Blo 634301 1428425 := bstep (se 2 (by rfl) ⟨535659, by rfl⟩ : syracuseStep 1428425 = 1071319) B1071319
theorem B805879 : Blo 634301 805879 := bstep (se 1 (by rfl) ⟨604409, by rfl⟩ : syracuseStep 805879 = 1208819) B1208819
theorem B2411639 : Blo 634301 2411639 := bstep (se 1 (by rfl) ⟨1808729, by rfl⟩ : syracuseStep 2411639 = 3617459) B3617459
theorem B904393 : Blo 634301 904393 := bstep (se 2 (by rfl) ⟨339147, by rfl⟩ : syracuseStep 904393 = 678295) B678295
theorem B2149577 : Blo 634301 2149577 := bstep (se 2 (by rfl) ⟨806091, by rfl⟩ : syracuseStep 2149577 = 1612183) B1612183
theorem B1723681 : Blo 634301 1723681 := bstep (se 2 (by rfl) ⟨646380, by rfl⟩ : syracuseStep 1723681 = 1292761) B1292761
theorem B806203 : Blo 634301 806203 := bstep (se 1 (by rfl) ⟨604652, by rfl⟩ : syracuseStep 806203 = 1209305) B1209305
theorem B5787065 : Blo 634301 5787065 := bstep (se 2 (by rfl) ⟨2170149, by rfl⟩ : syracuseStep 5787065 = 4340299) B4340299
theorem B1429127 : Blo 634301 1429127 := bstep (se 1 (by rfl) ⟨1071845, by rfl⟩ : syracuseStep 1429127 = 2143691) B2143691
theorem B4837157 : Blo 634301 4837157 := bstep (se 4 (by rfl) ⟨453483, by rfl⟩ : syracuseStep 4837157 = 906967) B906967
theorem B806699 : Blo 634301 806699 := bstep (se 1 (by rfl) ⟨605024, by rfl⟩ : syracuseStep 806699 = 1210049) B1210049
theorem B1429307 : Blo 634301 1429307 := bstep (se 1 (by rfl) ⟨1071980, by rfl⟩ : syracuseStep 1429307 = 2143961) B2143961
theorem B2150279 : Blo 634301 2150279 := bstep (se 1 (by rfl) ⟨1612709, by rfl⟩ : syracuseStep 2150279 = 3225419) B3225419
theorem B99438515 : Blo 634301 99438515 := bstep (se 1 (by rfl) ⟨74578886, by rfl⟩ : syracuseStep 99438515 = 149157773) B149157773
theorem B1429433 : Blo 634301 1429433 := bstep (se 2 (by rfl) ⟨536037, by rfl⟩ : syracuseStep 1429433 = 1072075) B1072075
theorem B2412611 : Blo 634301 2412611 := bstep (se 1 (by rfl) ⟨1809458, by rfl⟩ : syracuseStep 2412611 = 3618917) B3618917
theorem B1724503 : Blo 634301 1724503 := bstep (se 1 (by rfl) ⟨1293377, by rfl⟩ : syracuseStep 1724503 = 2586755) B2586755
theorem B2183287 : Blo 634301 2183287 := bstep (se 1 (by rfl) ⟨1637465, by rfl⟩ : syracuseStep 2183287 = 3274931) B3274931
theorem B643259 : Blo 634301 643259 := bstep (se 1 (by rfl) ⟨482444, by rfl⟩ : syracuseStep 643259 = 964889) B964889
theorem B2150657 : Blo 634301 2150657 := bstep (se 2 (by rfl) ⟨806496, by rfl⟩ : syracuseStep 2150657 = 1612993) B1612993
theorem B807175 : Blo 634301 807175 := bstep (se 1 (by rfl) ⟨605381, by rfl⟩ : syracuseStep 807175 = 1210763) B1210763
theorem B1429775 : Blo 634301 1429775 := bstep (se 1 (by rfl) ⟨1072331, by rfl⟩ : syracuseStep 1429775 = 2144663) B2144663
theorem B1429793 : Blo 634301 1429793 := bstep (se 2 (by rfl) ⟨536172, by rfl⟩ : syracuseStep 1429793 = 1072345) B1072345
theorem B873019 : Blo 634301 873019 := bstep (se 1 (by rfl) ⟨654764, by rfl⟩ : syracuseStep 873019 = 1309529) B1309529
theorem B1430135 : Blo 634301 1430135 := bstep (se 1 (by rfl) ⟨1072601, by rfl⟩ : syracuseStep 1430135 = 2145203) B2145203
theorem B807671 : Blo 634301 807671 := bstep (se 1 (by rfl) ⟨605753, by rfl⟩ : syracuseStep 807671 = 1211507) B1211507
theorem B7721729 : Blo 634301 7721729 := bstep (se 2 (by rfl) ⟨2895648, by rfl⟩ : syracuseStep 7721729 = 5791297) B5791297
theorem B1725185 : Blo 634301 1725185 := bstep (se 2 (by rfl) ⟨646944, by rfl⟩ : syracuseStep 1725185 = 1293889) B1293889
theorem B1430315 : Blo 634301 1430315 := bstep (se 1 (by rfl) ⟨1072736, by rfl⟩ : syracuseStep 1430315 = 2145473) B2145473
theorem B807823 : Blo 634301 807823 := bstep (se 1 (by rfl) ⟨605867, by rfl⟩ : syracuseStep 807823 = 1211735) B1211735
theorem B2413597 : Blo 634301 2413597 := bstep (se 3 (by rfl) ⟨452549, by rfl⟩ : syracuseStep 2413597 = 905099) B905099
theorem B2151467 : Blo 634301 2151467 := bstep (se 1 (by rfl) ⟨1613600, by rfl⟩ : syracuseStep 2151467 = 3227201) B3227201
theorem B644155 : Blo 634301 644155 := bstep (se 1 (by rfl) ⟨483116, by rfl⟩ : syracuseStep 644155 = 966233) B966233
theorem B1430675 : Blo 634301 1430675 := bstep (se 1 (by rfl) ⟨1073006, by rfl⟩ : syracuseStep 1430675 = 2146013) B2146013
theorem B1430729 : Blo 634301 1430729 := bstep (se 2 (by rfl) ⟨536523, by rfl⟩ : syracuseStep 1430729 = 1073047) B1073047
theorem B1070455 : Blo 634301 1070455 := bstep (se 1 (by rfl) ⟨802841, by rfl⟩ : syracuseStep 1070455 = 1605683) B1605683
theorem B1070651 : Blo 634301 1070651 := bstep (se 1 (by rfl) ⟨802988, by rfl⟩ : syracuseStep 1070651 = 1605977) B1605977
theorem B906871 : Blo 634301 906871 := bstep (se 1 (by rfl) ⟨680153, by rfl⟩ : syracuseStep 906871 = 1360307) B1360307
theorem B23025329 : Blo 634301 23025329 := bstep (se 2 (by rfl) ⟨8634498, by rfl⟩ : syracuseStep 23025329 = 17268997) B17268997
theorem B1431431 : Blo 634301 1431431 := bstep (se 1 (by rfl) ⟨1073573, by rfl⟩ : syracuseStep 1431431 = 2147147) B2147147
theorem B907195 : Blo 634301 907195 := bstep (se 1 (by rfl) ⟨680396, by rfl⟩ : syracuseStep 907195 = 1360793) B1360793
theorem B1071049 : Blo 634301 1071049 := bstep (se 2 (by rfl) ⟨401643, by rfl⟩ : syracuseStep 1071049 = 803287) B803287
theorem B1431611 : Blo 634301 1431611 := bstep (se 1 (by rfl) ⟨1073708, by rfl⟩ : syracuseStep 1431611 = 2147417) B2147417
theorem B2480195 : Blo 634301 2480195 := bstep (se 1 (by rfl) ⟨1860146, by rfl⟩ : syracuseStep 2480195 = 3720293) B3720293
theorem B1431737 : Blo 634301 1431737 := bstep (se 2 (by rfl) ⟨536901, by rfl⟩ : syracuseStep 1431737 = 1073803) B1073803
theorem B2152763 : Blo 634301 2152763 := bstep (se 1 (by rfl) ⟨1614572, by rfl⟩ : syracuseStep 2152763 = 3229145) B3229145
theorem B1432079 : Blo 634301 1432079 := bstep (se 1 (by rfl) ⟨1074059, by rfl⟩ : syracuseStep 1432079 = 2148119) B2148119
theorem B1432097 : Blo 634301 1432097 := bstep (se 2 (by rfl) ⟨537036, by rfl⟩ : syracuseStep 1432097 = 1074073) B1074073
theorem B1071751 : Blo 634301 1071751 := bstep (se 1 (by rfl) ⟨803813, by rfl⟩ : syracuseStep 1071751 = 1607627) B1607627
theorem B2153249 : Blo 634301 2153249 := bstep (se 2 (by rfl) ⟨807468, by rfl⟩ : syracuseStep 2153249 = 1614937) B1614937
theorem B1432439 : Blo 634301 1432439 := bstep (se 1 (by rfl) ⟨1074329, by rfl⟩ : syracuseStep 1432439 = 2148659) B2148659
theorem B12409861 : Blo 634301 12409861 := bstep (se 4 (by rfl) ⟨1163424, by rfl⟩ : syracuseStep 12409861 = 2326849) B2326849
theorem B1432619 : Blo 634301 1432619 := bstep (se 1 (by rfl) ⟨1074464, by rfl⟩ : syracuseStep 1432619 = 2148929) B2148929
theorem B1072399 : Blo 634301 1072399 := bstep (se 1 (by rfl) ⟨804299, by rfl⟩ : syracuseStep 1072399 = 1608599) B1608599
theorem B2153843 : Blo 634301 2153843 := bstep (se 1 (by rfl) ⟨1615382, by rfl⟩ : syracuseStep 2153843 = 3230765) B3230765
theorem B679303 : Blo 634301 679303 := bstep (se 1 (by rfl) ⟨509477, by rfl⟩ : syracuseStep 679303 = 1018955) B1018955
theorem B1432979 : Blo 634301 1432979 := bstep (se 1 (by rfl) ⟨1074734, by rfl⟩ : syracuseStep 1432979 = 2149469) B2149469
theorem B1433033 : Blo 634301 1433033 := bstep (se 2 (by rfl) ⟨537387, by rfl⟩ : syracuseStep 1433033 = 1074775) B1074775
theorem B3530263 : Blo 634301 3530263 := bstep (se 1 (by rfl) ⟨2647697, by rfl⟩ : syracuseStep 3530263 = 5295395) B5295395
theorem B1629811 : Blo 634301 1629811 := bstep (se 1 (by rfl) ⟨1222358, by rfl⟩ : syracuseStep 1629811 = 2444717) B2444717
theorem B4120183 : Blo 634301 4120183 := bstep (se 1 (by rfl) ⟨3090137, by rfl⟩ : syracuseStep 4120183 = 6180275) B6180275
theorem B1072939 : Blo 634301 1072939 := bstep (se 1 (by rfl) ⟨804704, by rfl⟩ : syracuseStep 1072939 = 1609409) B1609409
theorem B2416499 : Blo 634301 2416499 := bstep (se 1 (by rfl) ⟨1812374, by rfl⟩ : syracuseStep 2416499 = 3624749) B3624749
theorem B1073081 : Blo 634301 1073081 := bstep (se 2 (by rfl) ⟨402405, by rfl⟩ : syracuseStep 1073081 = 804811) B804811
theorem B3629123 : Blo 634301 3629123 := bstep (se 1 (by rfl) ⟨2721842, by rfl⟩ : syracuseStep 3629123 = 5443685) B5443685
theorem B5791877 : Blo 634301 5791877 := bstep (se 4 (by rfl) ⟨542988, by rfl⟩ : syracuseStep 5791877 = 1085977) B1085977
theorem B1433735 : Blo 634301 1433735 := bstep (se 1 (by rfl) ⟨1075301, by rfl⟩ : syracuseStep 1433735 = 2150603) B2150603
theorem B680123 : Blo 634301 680123 := bstep (se 1 (by rfl) ⟨510092, by rfl⟩ : syracuseStep 680123 = 1020185) B1020185
theorem B1433915 : Blo 634301 1433915 := bstep (se 1 (by rfl) ⟨1075436, by rfl⟩ : syracuseStep 1433915 = 2150873) B2150873
theorem B1204627 : Blo 634301 1204627 := bstep (se 1 (by rfl) ⟨903470, by rfl⟩ : syracuseStep 1204627 = 1806941) B1806941
theorem B1434041 : Blo 634301 1434041 := bstep (se 2 (by rfl) ⟨537765, by rfl⟩ : syracuseStep 1434041 = 1075531) B1075531
theorem B2712017 : Blo 634301 2712017 := bstep (se 2 (by rfl) ⟨1017006, by rfl⟩ : syracuseStep 2712017 = 2034013) B2034013
theorem B4088323 : Blo 634301 4088323 := bstep (se 1 (by rfl) ⟨3066242, by rfl⟩ : syracuseStep 4088323 = 6132485) B6132485
theorem B1532449 : Blo 634301 1532449 := bstep (se 2 (by rfl) ⟨574668, by rfl⟩ : syracuseStep 1532449 = 1149337) B1149337
theorem B1073783 : Blo 634301 1073783 := bstep (se 1 (by rfl) ⟨805337, by rfl⟩ : syracuseStep 1073783 = 1610675) B1610675
theorem B1434383 : Blo 634301 1434383 := bstep (se 1 (by rfl) ⟨1075787, by rfl⟩ : syracuseStep 1434383 = 2151575) B2151575
theorem B1434401 : Blo 634301 1434401 := bstep (se 2 (by rfl) ⟨537900, by rfl⟩ : syracuseStep 1434401 = 1075801) B1075801
theorem B1532807 : Blo 634301 1532807 := bstep (se 1 (by rfl) ⟨1149605, by rfl⟩ : syracuseStep 1532807 = 2299211) B2299211
theorem B713659 : Blo 634301 713659 := bstep (se 1 (by rfl) ⟨535244, by rfl⟩ : syracuseStep 713659 = 1070489) B1070489
theorem B1074235 : Blo 634301 1074235 := bstep (se 1 (by rfl) ⟨805676, by rfl⟩ : syracuseStep 1074235 = 1611353) B1611353
theorem B1434743 : Blo 634301 1434743 := bstep (se 1 (by rfl) ⟨1076057, by rfl⟩ : syracuseStep 1434743 = 2152115) B2152115
theorem B1074377 : Blo 634301 1074377 := bstep (se 2 (by rfl) ⟨402891, by rfl⟩ : syracuseStep 1074377 = 805783) B805783
theorem B2286881 : Blo 634301 2286881 := bstep (se 2 (by rfl) ⟨857580, by rfl⟩ : syracuseStep 2286881 = 1715161) B1715161
theorem B1434923 : Blo 634301 1434923 := bstep (se 1 (by rfl) ⟨1076192, by rfl⟩ : syracuseStep 1434923 = 2152385) B2152385
theorem B714127 : Blo 634301 714127 := bstep (se 1 (by rfl) ⟨535595, by rfl⟩ : syracuseStep 714127 = 1071191) B1071191
theorem B26076593 : Blo 634301 26076593 := bstep (se 2 (by rfl) ⟨9778722, by rfl⟩ : syracuseStep 26076593 = 19557445) B19557445
theorem B1205705 : Blo 634301 1205705 := bstep (se 2 (by rfl) ⟨452139, by rfl⟩ : syracuseStep 1205705 = 904279) B904279
theorem B1631831 : Blo 634301 1631831 := bstep (se 1 (by rfl) ⟨1223873, by rfl⟩ : syracuseStep 1631831 = 2447747) B2447747
theorem B15492707 : Blo 634301 15492707 := bstep (se 1 (by rfl) ⟨11619530, by rfl⟩ : syracuseStep 15492707 = 23239061) B23239061
theorem B1435283 : Blo 634301 1435283 := bstep (se 1 (by rfl) ⟨1076462, by rfl⟩ : syracuseStep 1435283 = 2152925) B2152925
theorem B1435337 : Blo 634301 1435337 := bstep (se 2 (by rfl) ⟨538251, by rfl⟩ : syracuseStep 1435337 = 1076503) B1076503
theorem B3860261 : Blo 634301 3860261 := bstep (se 4 (by rfl) ⟨361899, by rfl⟩ : syracuseStep 3860261 = 723799) B723799
theorem B714631 : Blo 634301 714631 := bstep (se 1 (by rfl) ⟨535973, by rfl⟩ : syracuseStep 714631 = 1071947) B1071947
theorem B1075079 : Blo 634301 1075079 := bstep (se 1 (by rfl) ⟨806309, by rfl⟩ : syracuseStep 1075079 = 1612619) B1612619
theorem B5171147 : Blo 634301 5171147 := bstep (se 1 (by rfl) ⟨3878360, by rfl⟩ : syracuseStep 5171147 = 7756721) B7756721
theorem B2418731 : Blo 634301 2418731 := bstep (se 1 (by rfl) ⟨1814048, by rfl⟩ : syracuseStep 2418731 = 3628097) B3628097
theorem B714811 : Blo 634301 714811 := bstep (se 1 (by rfl) ⟨536108, by rfl⟩ : syracuseStep 714811 = 1072217) B1072217
theorem B13789277 : Blo 634301 13789277 := bstep (se 3 (by rfl) ⟨2585489, by rfl⟩ : syracuseStep 13789277 = 5170979) B5170979
theorem B5171401 : Blo 634301 5171401 := bstep (se 2 (by rfl) ⟨1939275, by rfl⟩ : syracuseStep 5171401 = 3878551) B3878551
theorem B1206571 : Blo 634301 1206571 := bstep (se 1 (by rfl) ⟨904928, by rfl⟩ : syracuseStep 1206571 = 1809857) B1809857
theorem B1206647 : Blo 634301 1206647 := bstep (se 1 (by rfl) ⟨904985, by rfl⟩ : syracuseStep 1206647 = 1809971) B1809971
theorem B5794183 : Blo 634301 5794183 := bstep (se 1 (by rfl) ⟨4345637, by rfl⟩ : syracuseStep 5794183 = 8691275) B8691275
theorem B1436039 : Blo 634301 1436039 := bstep (se 1 (by rfl) ⟨1077029, by rfl⟩ : syracuseStep 1436039 = 2154059) B2154059
theorem B3631513 : Blo 634301 3631513 := bstep (se 2 (by rfl) ⟨1361817, by rfl⟩ : syracuseStep 3631513 = 2723635) B2723635
theorem B4843961 : Blo 634301 4843961 := bstep (se 2 (by rfl) ⟨1816485, by rfl⟩ : syracuseStep 4843961 = 3632971) B3632971
theorem B715279 : Blo 634301 715279 := bstep (se 1 (by rfl) ⟨536459, by rfl⟩ : syracuseStep 715279 = 1072919) B1072919
theorem B1075727 : Blo 634301 1075727 := bstep (se 1 (by rfl) ⟨806795, by rfl⟩ : syracuseStep 1075727 = 1613591) B1613591
theorem B7825997 : Blo 634301 7825997 := bstep (se 3 (by rfl) ⟨1467374, by rfl⟩ : syracuseStep 7825997 = 2934749) B2934749
theorem B3664673 : Blo 634301 3664673 := bstep (se 2 (by rfl) ⟨1374252, by rfl⟩ : syracuseStep 3664673 = 2748505) B2748505
theorem B8711027 : Blo 634301 8711027 := bstep (se 1 (by rfl) ⟨6533270, by rfl⟩ : syracuseStep 8711027 = 13066541) B13066541
theorem B10873763 : Blo 634301 10873763 := bstep (se 1 (by rfl) ⟨8155322, by rfl⟩ : syracuseStep 10873763 = 16310645) B16310645
theorem B715783 : Blo 634301 715783 := bstep (se 1 (by rfl) ⟨536837, by rfl⟩ : syracuseStep 715783 = 1073675) B1073675
theorem B1076267 : Blo 634301 1076267 := bstep (se 1 (by rfl) ⟨807200, by rfl⟩ : syracuseStep 1076267 = 1614401) B1614401
theorem B5893181 : Blo 634301 5893181 := bstep (se 3 (by rfl) ⟨1104971, by rfl⟩ : syracuseStep 5893181 = 2209943) B2209943
theorem B715963 : Blo 634301 715963 := bstep (se 1 (by rfl) ⟨536972, by rfl⟩ : syracuseStep 715963 = 1073945) B1073945
theorem B8154503 : Blo 634301 8154503 := bstep (se 1 (by rfl) ⟨6115877, by rfl⟩ : syracuseStep 8154503 = 12231755) B12231755
theorem B4124051 : Blo 634301 4124051 := bstep (se 1 (by rfl) ⟨3093038, by rfl⟩ : syracuseStep 4124051 = 6186077) B6186077
theorem B1076665 : Blo 634301 1076665 := bstep (se 2 (by rfl) ⟨403749, by rfl⟩ : syracuseStep 1076665 = 807499) B807499
theorem B27553283 : Blo 634301 27553283 := bstep (se 1 (by rfl) ⟨20664962, by rfl⟩ : syracuseStep 27553283 = 41329925) B41329925
theorem B3108395 : Blo 634301 3108395 := bstep (se 1 (by rfl) ⟨2331296, by rfl⟩ : syracuseStep 3108395 = 4662593) B4662593
theorem B716431 : Blo 634301 716431 := bstep (se 1 (by rfl) ⟨537323, by rfl⟩ : syracuseStep 716431 = 1074647) B1074647
theorem B1929217 : Blo 634301 1929217 := bstep (se 2 (by rfl) ⟨723456, by rfl⟩ : syracuseStep 1929217 = 1446913) B1446913
theorem B15921269 : Blo 634301 15921269 := bstep (se 5 (by rfl) ⟨746309, by rfl⟩ : syracuseStep 15921269 = 1492619) B1492619
theorem B716935 : Blo 634301 716935 := bstep (se 1 (by rfl) ⟨537701, by rfl⟩ : syracuseStep 716935 = 1075403) B1075403
theorem B6123721 : Blo 634301 6123721 := bstep (se 2 (by rfl) ⟨2296395, by rfl⟩ : syracuseStep 6123721 = 4592791) B4592791
theorem B1208591 : Blo 634301 1208591 := bstep (se 1 (by rfl) ⟨906443, by rfl⟩ : syracuseStep 1208591 = 1812887) B1812887
theorem B717115 : Blo 634301 717115 := bstep (se 1 (by rfl) ⟨537836, by rfl⟩ : syracuseStep 717115 = 1075673) B1075673
theorem B3633497 : Blo 634301 3633497 := bstep (se 2 (by rfl) ⟨1362561, by rfl⟩ : syracuseStep 3633497 = 2725123) B2725123
theorem B1143355 : Blo 634301 1143355 := bstep (se 1 (by rfl) ⟨857516, by rfl⟩ : syracuseStep 1143355 = 1715033) B1715033
theorem B717583 : Blo 634301 717583 := bstep (se 1 (by rfl) ⟨538187, by rfl⟩ : syracuseStep 717583 = 1076375) B1076375
theorem B2716733 : Blo 634301 2716733 := bstep (se 3 (by rfl) ⟨509387, by rfl⟩ : syracuseStep 2716733 = 1018775) B1018775
theorem B718087 : Blo 634301 718087 := bstep (se 1 (by rfl) ⟨538565, by rfl⟩ : syracuseStep 718087 = 1077131) B1077131
theorem B2422163 : Blo 634301 2422163 := bstep (se 1 (by rfl) ⟨1816622, by rfl⟩ : syracuseStep 2422163 = 3633245) B3633245
theorem B1210231 : Blo 634301 1210231 := bstep (se 1 (by rfl) ⟨907673, by rfl⟩ : syracuseStep 1210231 = 1815347) B1815347
theorem B2291609 : Blo 634301 2291609 := bstep (se 2 (by rfl) ⟨859353, by rfl⟩ : syracuseStep 2291609 = 1718707) B1718707
theorem B915463 : Blo 634301 915463 := bstep (se 1 (by rfl) ⟨686597, by rfl⟩ : syracuseStep 915463 = 1373195) B1373195
theorem B6126029 : Blo 634301 6126029 := bstep (se 3 (by rfl) ⟨1148630, by rfl⟩ : syracuseStep 6126029 = 2297261) B2297261
theorem B3439297 : Blo 634301 3439297 := bstep (se 2 (by rfl) ⟨1289736, by rfl⟩ : syracuseStep 3439297 = 2579473) B2579473
theorem B7339031 : Blo 634301 7339031 := bstep (se 1 (by rfl) ⟨5504273, by rfl⟩ : syracuseStep 7339031 = 11008547) B11008547
theorem B1932331 : Blo 634301 1932331 := bstep (se 1 (by rfl) ⟨1449248, by rfl⟩ : syracuseStep 1932331 = 2898497) B2898497
theorem B1310137 : Blo 634301 1310137 := bstep (se 2 (by rfl) ⟨491301, by rfl⟩ : syracuseStep 1310137 = 982603) B982603
theorem B9305549 : Blo 634301 9305549 := bstep (se 3 (by rfl) ⟨1744790, by rfl⟩ : syracuseStep 9305549 = 3489581) B3489581
theorem B2719261 : Blo 634301 2719261 := bstep (se 3 (by rfl) ⟨509861, by rfl⟩ : syracuseStep 2719261 = 1019723) B1019723
theorem B8289869 : Blo 634301 8289869 := bstep (se 3 (by rfl) ⟨1554350, by rfl⟩ : syracuseStep 8289869 = 3108701) B3108701
theorem B1146569 : Blo 634301 1146569 := bstep (se 2 (by rfl) ⟨429963, by rfl⟩ : syracuseStep 1146569 = 859927) B859927
theorem B2719433 : Blo 634301 2719433 := bstep (se 2 (by rfl) ⟨1019787, by rfl⟩ : syracuseStep 2719433 = 2039575) B2039575
theorem B3440357 : Blo 634301 3440357 := bstep (se 4 (by rfl) ⟨322533, by rfl⟩ : syracuseStep 3440357 = 645067) B645067
theorem B8257565 : Blo 634301 8257565 := bstep (se 3 (by rfl) ⟨1548293, by rfl⟩ : syracuseStep 8257565 = 3096587) B3096587
theorem B3211649 : Blo 634301 3211649 := bstep (se 2 (by rfl) ⟨1204368, by rfl⟩ : syracuseStep 3211649 = 2408737) B2408737
theorem B1606169 : Blo 634301 1606169 := bstep (se 2 (by rfl) ⟨602313, by rfl⟩ : syracuseStep 1606169 = 1204627) B1204627
theorem B1606675 : Blo 634301 1606675 := bstep (se 1 (by rfl) ⟨1205006, by rfl⟩ : syracuseStep 1606675 = 2410013) B2410013
theorem B3212459 : Blo 634301 3212459 := bstep (se 1 (by rfl) ⟨2409344, by rfl⟩ : syracuseStep 3212459 = 4818689) B4818689
theorem B3441911 : Blo 634301 3441911 := bstep (se 1 (by rfl) ⟨2581433, by rfl⟩ : syracuseStep 3441911 = 5162867) B5162867
theorem B951545 : Blo 634301 951545 := bstep (se 2 (by rfl) ⟨356829, by rfl⟩ : syracuseStep 951545 = 713659) B713659
theorem B951647 : Blo 634301 951647 := bstep (se 1 (by rfl) ⟨713735, by rfl⟩ : syracuseStep 951647 = 1427471) B1427471
theorem B951659 : Blo 634301 951659 := bstep (se 1 (by rfl) ⟨713744, by rfl⟩ : syracuseStep 951659 = 1427489) B1427489
theorem B2033039 : Blo 634301 2033039 := bstep (se 1 (by rfl) ⟨1524779, by rfl⟩ : syracuseStep 2033039 = 3049559) B3049559
theorem B1017263 : Blo 634301 1017263 := bstep (se 1 (by rfl) ⟨762947, by rfl⟩ : syracuseStep 1017263 = 1525895) B1525895
theorem B951887 : Blo 634301 951887 := bstep (se 1 (by rfl) ⟨713915, by rfl⟩ : syracuseStep 951887 = 1427831) B1427831
theorem B3212945 : Blo 634301 3212945 := bstep (se 2 (by rfl) ⟨1204854, by rfl⟩ : syracuseStep 3212945 = 2409709) B2409709
theorem B5146259 : Blo 634301 5146259 := bstep (se 1 (by rfl) ⟨3859694, by rfl⟩ : syracuseStep 5146259 = 7719389) B7719389
theorem B952007 : Blo 634301 952007 := bstep (se 1 (by rfl) ⟨714005, by rfl⟩ : syracuseStep 952007 = 1428011) B1428011
theorem B3442475 : Blo 634301 3442475 := bstep (se 1 (by rfl) ⟨2581856, by rfl⟩ : syracuseStep 3442475 = 5163713) B5163713
theorem B2295647 : Blo 634301 2295647 := bstep (se 1 (by rfl) ⟨1721735, by rfl⟩ : syracuseStep 2295647 = 3443471) B3443471
theorem B952169 : Blo 634301 952169 := bstep (se 2 (by rfl) ⟨357063, by rfl⟩ : syracuseStep 952169 = 714127) B714127
theorem B952247 : Blo 634301 952247 := bstep (se 1 (by rfl) ⟨714185, by rfl⟩ : syracuseStep 952247 = 1428371) B1428371
theorem B952283 : Blo 634301 952283 := bstep (se 1 (by rfl) ⟨714212, by rfl⟩ : syracuseStep 952283 = 1428425) B1428425
theorem B30902309 : Blo 634301 30902309 := bstep (se 4 (by rfl) ⟨2897091, by rfl⟩ : syracuseStep 30902309 = 5794183) B5794183
theorem B1607759 : Blo 634301 1607759 := bstep (se 1 (by rfl) ⟨1205819, by rfl⟩ : syracuseStep 1607759 = 2411639) B2411639
theorem B7342169 : Blo 634301 7342169 := bstep (se 2 (by rfl) ⟨2753313, by rfl⟩ : syracuseStep 7342169 = 5506627) B5506627
theorem B6130025 : Blo 634301 6130025 := bstep (se 2 (by rfl) ⟨2298759, by rfl⟩ : syracuseStep 6130025 = 4597519) B4597519
theorem B952751 : Blo 634301 952751 := bstep (se 1 (by rfl) ⟨714563, by rfl⟩ : syracuseStep 952751 = 1429127) B1429127
theorem B5507531 : Blo 634301 5507531 := bstep (se 1 (by rfl) ⟨4130648, by rfl⟩ : syracuseStep 5507531 = 8261297) B8261297
theorem B952841 : Blo 634301 952841 := bstep (se 2 (by rfl) ⟨357315, by rfl⟩ : syracuseStep 952841 = 714631) B714631
theorem B3475993 : Blo 634301 3475993 := bstep (se 2 (by rfl) ⟨1303497, by rfl⟩ : syracuseStep 3475993 = 2606995) B2606995
theorem B952871 : Blo 634301 952871 := bstep (se 1 (by rfl) ⟨714653, by rfl⟩ : syracuseStep 952871 = 1429307) B1429307
theorem B66292343 : Blo 634301 66292343 := bstep (se 1 (by rfl) ⟨49719257, by rfl⟩ : syracuseStep 66292343 = 99438515) B99438515
theorem B952955 : Blo 634301 952955 := bstep (se 1 (by rfl) ⟨714716, by rfl⟩ : syracuseStep 952955 = 1429433) B1429433
theorem B1608407 : Blo 634301 1608407 := bstep (se 1 (by rfl) ⟨1206305, by rfl⟩ : syracuseStep 1608407 = 2412611) B2412611
theorem B953081 : Blo 634301 953081 := bstep (se 2 (by rfl) ⟨357405, by rfl⟩ : syracuseStep 953081 = 714811) B714811
theorem B2329337 : Blo 634301 2329337 := bstep (se 2 (by rfl) ⟨873501, by rfl⟩ : syracuseStep 2329337 = 1747003) B1747003
theorem B953183 : Blo 634301 953183 := bstep (se 1 (by rfl) ⟨714887, by rfl⟩ : syracuseStep 953183 = 1429775) B1429775
theorem B953195 : Blo 634301 953195 := bstep (se 1 (by rfl) ⟨714896, by rfl⟩ : syracuseStep 953195 = 1429793) B1429793
theorem B17632241 : Blo 634301 17632241 := bstep (se 2 (by rfl) ⟨6612090, by rfl⟩ : syracuseStep 17632241 = 13224181) B13224181
theorem B1608761 : Blo 634301 1608761 := bstep (se 2 (by rfl) ⟨603285, by rfl⟩ : syracuseStep 1608761 = 1206571) B1206571
theorem B953423 : Blo 634301 953423 := bstep (se 1 (by rfl) ⟨715067, by rfl⟩ : syracuseStep 953423 = 1430135) B1430135
theorem B5147819 : Blo 634301 5147819 := bstep (se 1 (by rfl) ⟨3860864, by rfl⟩ : syracuseStep 5147819 = 7721729) B7721729
theorem B1150123 : Blo 634301 1150123 := bstep (se 1 (by rfl) ⟨862592, by rfl⟩ : syracuseStep 1150123 = 1725185) B1725185
theorem B953543 : Blo 634301 953543 := bstep (se 1 (by rfl) ⟨715157, by rfl⟩ : syracuseStep 953543 = 1430315) B1430315
theorem B953705 : Blo 634301 953705 := bstep (se 2 (by rfl) ⟨357639, by rfl⟩ : syracuseStep 953705 = 715279) B715279
theorem B953783 : Blo 634301 953783 := bstep (se 1 (by rfl) ⟨715337, by rfl⟩ : syracuseStep 953783 = 1430675) B1430675
theorem B953819 : Blo 634301 953819 := bstep (se 1 (by rfl) ⟨715364, by rfl⟩ : syracuseStep 953819 = 1430729) B1430729
theorem B3215213 : Blo 634301 3215213 := bstep (se 3 (by rfl) ⟨602852, by rfl⟩ : syracuseStep 3215213 = 1205705) B1205705
theorem B954287 : Blo 634301 954287 := bstep (se 1 (by rfl) ⟨715715, by rfl⟩ : syracuseStep 954287 = 1431431) B1431431
theorem B954377 : Blo 634301 954377 := bstep (se 2 (by rfl) ⟨357891, by rfl⟩ : syracuseStep 954377 = 715783) B715783
theorem B3215375 : Blo 634301 3215375 := bstep (se 1 (by rfl) ⟨2411531, by rfl⟩ : syracuseStep 3215375 = 4823063) B4823063
theorem B954407 : Blo 634301 954407 := bstep (se 1 (by rfl) ⟨715805, by rfl⟩ : syracuseStep 954407 = 1431611) B1431611
theorem B954491 : Blo 634301 954491 := bstep (se 1 (by rfl) ⟨715868, by rfl⟩ : syracuseStep 954491 = 1431737) B1431737
theorem B954617 : Blo 634301 954617 := bstep (se 2 (by rfl) ⟨357981, by rfl⟩ : syracuseStep 954617 = 715963) B715963
theorem B954719 : Blo 634301 954719 := bstep (se 1 (by rfl) ⟨716039, by rfl⟩ : syracuseStep 954719 = 1432079) B1432079
theorem B954731 : Blo 634301 954731 := bstep (se 1 (by rfl) ⟨716048, by rfl⟩ : syracuseStep 954731 = 1432097) B1432097
theorem B2298241 : Blo 634301 2298241 := bstep (se 2 (by rfl) ⟨861840, by rfl⟩ : syracuseStep 2298241 = 1723681) B1723681
theorem B954959 : Blo 634301 954959 := bstep (se 1 (by rfl) ⟨716219, by rfl⟩ : syracuseStep 954959 = 1432439) B1432439
theorem B955079 : Blo 634301 955079 := bstep (se 1 (by rfl) ⟨716309, by rfl⟩ : syracuseStep 955079 = 1432619) B1432619
theorem B9573137 : Blo 634301 9573137 := bstep (se 2 (by rfl) ⟨3589926, by rfl⟩ : syracuseStep 9573137 = 7179853) B7179853
theorem B955241 : Blo 634301 955241 := bstep (se 2 (by rfl) ⟨358215, by rfl⟩ : syracuseStep 955241 = 716431) B716431
theorem B955319 : Blo 634301 955319 := bstep (se 1 (by rfl) ⟨716489, by rfl⟩ : syracuseStep 955319 = 1432979) B1432979
theorem B955355 : Blo 634301 955355 := bstep (se 1 (by rfl) ⟨716516, by rfl⟩ : syracuseStep 955355 = 1433033) B1433033
theorem B1610999 : Blo 634301 1610999 := bstep (se 1 (by rfl) ⟨1208249, by rfl⟩ : syracuseStep 1610999 = 2416499) B2416499
theorem B955823 : Blo 634301 955823 := bstep (se 1 (by rfl) ⟨716867, by rfl⟩ : syracuseStep 955823 = 1433735) B1433735
theorem B2299337 : Blo 634301 2299337 := bstep (se 2 (by rfl) ⟨862251, by rfl⟩ : syracuseStep 2299337 = 1724503) B1724503
theorem B5445083 : Blo 634301 5445083 := bstep (se 1 (by rfl) ⟨4083812, by rfl⟩ : syracuseStep 5445083 = 8167625) B8167625
theorem B955913 : Blo 634301 955913 := bstep (se 2 (by rfl) ⟨358467, by rfl⟩ : syracuseStep 955913 = 716935) B716935
theorem B955943 : Blo 634301 955943 := bstep (se 1 (by rfl) ⟨716957, by rfl⟩ : syracuseStep 955943 = 1433915) B1433915
theorem B8164961 : Blo 634301 8164961 := bstep (se 2 (by rfl) ⟨3061860, by rfl⟩ : syracuseStep 8164961 = 6123721) B6123721
theorem B956027 : Blo 634301 956027 := bstep (se 1 (by rfl) ⟨717020, by rfl⟩ : syracuseStep 956027 = 1434041) B1434041
theorem B1808011 : Blo 634301 1808011 := bstep (se 1 (by rfl) ⟨1356008, by rfl⟩ : syracuseStep 1808011 = 2712017) B2712017
theorem B956153 : Blo 634301 956153 := bstep (se 2 (by rfl) ⟨358557, by rfl⟩ : syracuseStep 956153 = 717115) B717115
theorem B956255 : Blo 634301 956255 := bstep (se 1 (by rfl) ⟨717191, by rfl⟩ : syracuseStep 956255 = 1434383) B1434383
theorem B956267 : Blo 634301 956267 := bstep (se 1 (by rfl) ⟨717200, by rfl⟩ : syracuseStep 956267 = 1434401) B1434401
theorem B1021871 : Blo 634301 1021871 := bstep (se 1 (by rfl) ⟨766403, by rfl⟩ : syracuseStep 1021871 = 1532807) B1532807
theorem B956495 : Blo 634301 956495 := bstep (se 1 (by rfl) ⟨717371, by rfl⟩ : syracuseStep 956495 = 1434743) B1434743
theorem B956615 : Blo 634301 956615 := bstep (se 1 (by rfl) ⟨717461, by rfl⟩ : syracuseStep 956615 = 1434923) B1434923
theorem B17406197 : Blo 634301 17406197 := bstep (se 5 (by rfl) ⟨815915, by rfl⟩ : syracuseStep 17406197 = 1631831) B1631831
theorem B956777 : Blo 634301 956777 := bstep (se 2 (by rfl) ⟨358791, by rfl⟩ : syracuseStep 956777 = 717583) B717583
theorem B10328471 : Blo 634301 10328471 := bstep (se 1 (by rfl) ⟨7746353, by rfl⟩ : syracuseStep 10328471 = 15492707) B15492707
theorem B956855 : Blo 634301 956855 := bstep (se 1 (by rfl) ⟨717641, by rfl⟩ : syracuseStep 956855 = 1435283) B1435283
theorem B956891 : Blo 634301 956891 := bstep (se 1 (by rfl) ⟨717668, by rfl⟩ : syracuseStep 956891 = 1435337) B1435337
theorem B21142037 : Blo 634301 21142037 := bstep (se 6 (by rfl) ⟨495516, by rfl⟩ : syracuseStep 21142037 = 991033) B991033
theorem B3447431 : Blo 634301 3447431 := bstep (se 1 (by rfl) ⟨2585573, by rfl⟩ : syracuseStep 3447431 = 5171147) B5171147
theorem B1612487 : Blo 634301 1612487 := bstep (se 1 (by rfl) ⟨1209365, by rfl⟩ : syracuseStep 1612487 = 2418731) B2418731
theorem B3218129 : Blo 634301 3218129 := bstep (se 2 (by rfl) ⟨1206798, by rfl⟩ : syracuseStep 3218129 = 2413597) B2413597
theorem B957359 : Blo 634301 957359 := bstep (se 1 (by rfl) ⟨718019, by rfl⟩ : syracuseStep 957359 = 1436039) B1436039
theorem B957449 : Blo 634301 957449 := bstep (se 2 (by rfl) ⟨359043, by rfl⟩ : syracuseStep 957449 = 718087) B718087
theorem B5217331 : Blo 634301 5217331 := bstep (se 1 (by rfl) ⟨3912998, by rfl⟩ : syracuseStep 5217331 = 7825997) B7825997
theorem B4136107 : Blo 634301 4136107 := bstep (se 1 (by rfl) ⟨3102080, by rfl⟩ : syracuseStep 4136107 = 6204161) B6204161
theorem B5807351 : Blo 634301 5807351 := bstep (se 1 (by rfl) ⟨4355513, by rfl⟩ : syracuseStep 5807351 = 8711027) B8711027
theorem B7249175 : Blo 634301 7249175 := bstep (se 1 (by rfl) ⟨5436881, by rfl⟩ : syracuseStep 7249175 = 10873763) B10873763
theorem B2039165 : Blo 634301 2039165 := bstep (se 3 (by rfl) ⟨382343, by rfl⟩ : syracuseStep 2039165 = 764687) B764687
theorem B4824521 : Blo 634301 4824521 := bstep (se 2 (by rfl) ⟨1809195, by rfl⟩ : syracuseStep 4824521 = 3618391) B3618391
theorem B4070999 : Blo 634301 4070999 := bstep (se 1 (by rfl) ⟨3053249, by rfl⟩ : syracuseStep 4070999 = 6106499) B6106499
theorem B6987397 : Blo 634301 6987397 := bstep (se 4 (by rfl) ⟨655068, by rfl⟩ : syracuseStep 6987397 = 1310137) B1310137
theorem B2072263 : Blo 634301 2072263 := bstep (se 1 (by rfl) ⟨1554197, by rfl⟩ : syracuseStep 2072263 = 3108395) B3108395
theorem B1449721 : Blo 634301 1449721 := bstep (se 2 (by rfl) ⟨543645, by rfl⟩ : syracuseStep 1449721 = 1087291) B1087291
theorem B1613641 : Blo 634301 1613641 := bstep (se 2 (by rfl) ⟨605115, by rfl⟩ : syracuseStep 1613641 = 1210231) B1210231
theorem B1220617 : Blo 634301 1220617 := bstep (se 2 (by rfl) ⟨457731, by rfl⟩ : syracuseStep 1220617 = 915463) B915463
theorem B1811155 : Blo 634301 1811155 := bstep (se 1 (by rfl) ⟨1358366, by rfl⟩ : syracuseStep 1811155 = 2716733) B2716733
theorem B1614775 : Blo 634301 1614775 := bstep (se 1 (by rfl) ⟨1211081, by rfl⟩ : syracuseStep 1614775 = 2422163) B2422163
theorem B3220559 : Blo 634301 3220559 := bstep (se 1 (by rfl) ⟨2415419, by rfl⟩ : syracuseStep 3220559 = 4830839) B4830839
theorem B3221207 : Blo 634301 3221207 := bstep (se 1 (by rfl) ⟨2415905, by rfl⟩ : syracuseStep 3221207 = 4831811) B4831811
theorem B3057517 : Blo 634301 3057517 := bstep (se 3 (by rfl) ⟨573284, by rfl⟩ : syracuseStep 3057517 = 1146569) B1146569
theorem B1812385 : Blo 634301 1812385 := bstep (se 2 (by rfl) ⟨679644, by rfl⟩ : syracuseStep 1812385 = 1359289) B1359289
theorem B4892687 : Blo 634301 4892687 := bstep (se 1 (by rfl) ⟨3669515, by rfl⟩ : syracuseStep 4892687 = 7339031) B7339031
theorem B4073561 : Blo 634301 4073561 := bstep (se 2 (by rfl) ⟨1527585, by rfl⟩ : syracuseStep 4073561 = 3055171) B3055171
theorem B2173081 : Blo 634301 2173081 := bstep (se 2 (by rfl) ⟨814905, by rfl⟩ : syracuseStep 2173081 = 1629811) B1629811
theorem B6203699 : Blo 634301 6203699 := bstep (se 1 (by rfl) ⟨4652774, by rfl⟩ : syracuseStep 6203699 = 9305549) B9305549
theorem B37234997 : Blo 634301 37234997 := bstep (se 5 (by rfl) ⟨1745390, by rfl⟩ : syracuseStep 37234997 = 3490781) B3490781
theorem B1812955 : Blo 634301 1812955 := bstep (se 1 (by rfl) ⟨1359716, by rfl⟩ : syracuseStep 1812955 = 2719433) B2719433
theorem B2140883 : Blo 634301 2140883 := bstep (se 1 (by rfl) ⟨1605662, by rfl⟩ : syracuseStep 2140883 = 3211325) B3211325
theorem B4074563 : Blo 634301 4074563 := bstep (se 1 (by rfl) ⟨3055922, by rfl⟩ : syracuseStep 4074563 = 6111845) B6111845
theorem B1715357 : Blo 634301 1715357 := bstep (se 3 (by rfl) ⟨321629, by rfl⟩ : syracuseStep 1715357 = 643259) B643259
theorem B1813661 : Blo 634301 1813661 := bstep (se 3 (by rfl) ⟨340061, by rfl⟩ : syracuseStep 1813661 = 680123) B680123
theorem B5451097 : Blo 634301 5451097 := bstep (se 2 (by rfl) ⟨2044161, by rfl⟩ : syracuseStep 5451097 = 4088323) B4088323
theorem B1813889 : Blo 634301 1813889 := bstep (se 2 (by rfl) ⟨680208, by rfl⟩ : syracuseStep 1813889 = 1360417) B1360417
theorem B634311 : Blo 634301 634311 := bstep (se 1 (by rfl) ⟨475733, by rfl⟩ : syracuseStep 634311 = 951467) B951467
theorem B634331 : Blo 634301 634331 := bstep (se 1 (by rfl) ⟨475748, by rfl⟩ : syracuseStep 634331 = 951497) B951497
theorem B634407 : Blo 634301 634407 := bstep (se 1 (by rfl) ⟨475805, by rfl⟩ : syracuseStep 634407 = 951611) B951611
theorem B634447 : Blo 634301 634447 := bstep (se 1 (by rfl) ⟨475835, by rfl⟩ : syracuseStep 634447 = 951671) B951671
theorem B634463 : Blo 634301 634463 := bstep (se 1 (by rfl) ⟨475847, by rfl⟩ : syracuseStep 634463 = 951695) B951695
theorem B634491 : Blo 634301 634491 := bstep (se 1 (by rfl) ⟨475868, by rfl⟩ : syracuseStep 634491 = 951737) B951737
theorem B634543 : Blo 634301 634543 := bstep (se 1 (by rfl) ⟨475907, by rfl⟩ : syracuseStep 634543 = 951815) B951815
theorem B634567 : Blo 634301 634567 := bstep (se 1 (by rfl) ⟨475925, by rfl⟩ : syracuseStep 634567 = 951851) B951851
theorem B1814231 : Blo 634301 1814231 := bstep (se 1 (by rfl) ⟨1360673, by rfl⟩ : syracuseStep 1814231 = 2721347) B2721347
theorem B634587 : Blo 634301 634587 := bstep (se 1 (by rfl) ⟨475940, by rfl⟩ : syracuseStep 634587 = 951881) B951881
theorem B634663 : Blo 634301 634663 := bstep (se 1 (by rfl) ⟨475997, by rfl⟩ : syracuseStep 634663 = 951995) B951995
theorem B4599595 : Blo 634301 4599595 := bstep (se 1 (by rfl) ⟨3449696, by rfl⟩ : syracuseStep 4599595 = 6899393) B6899393
theorem B1814345 : Blo 634301 1814345 := bstep (se 2 (by rfl) ⟨680379, by rfl⟩ : syracuseStep 1814345 = 1360759) B1360759
theorem B634703 : Blo 634301 634703 := bstep (se 1 (by rfl) ⟨476027, by rfl⟩ : syracuseStep 634703 = 952055) B952055
theorem B634719 : Blo 634301 634719 := bstep (se 1 (by rfl) ⟨476039, by rfl⟩ : syracuseStep 634719 = 952079) B952079
theorem B2142071 : Blo 634301 2142071 := bstep (se 1 (by rfl) ⟨1606553, by rfl⟩ : syracuseStep 2142071 = 3213107) B3213107
theorem B634747 : Blo 634301 634747 := bstep (se 1 (by rfl) ⟨476060, by rfl⟩ : syracuseStep 634747 = 952121) B952121
theorem B634799 : Blo 634301 634799 := bstep (se 1 (by rfl) ⟨476099, by rfl⟩ : syracuseStep 634799 = 952199) B952199
theorem B634823 : Blo 634301 634823 := bstep (se 1 (by rfl) ⟨476117, by rfl⟩ : syracuseStep 634823 = 952235) B952235
theorem B634843 : Blo 634301 634843 := bstep (se 1 (by rfl) ⟨476132, by rfl⟩ : syracuseStep 634843 = 952265) B952265
theorem B634919 : Blo 634301 634919 := bstep (se 1 (by rfl) ⟨476189, by rfl⟩ : syracuseStep 634919 = 952379) B952379
theorem B2142287 : Blo 634301 2142287 := bstep (se 1 (by rfl) ⟨1606715, by rfl⟩ : syracuseStep 2142287 = 3213431) B3213431
theorem B634959 : Blo 634301 634959 := bstep (se 1 (by rfl) ⟨476219, by rfl⟩ : syracuseStep 634959 = 952439) B952439
theorem B634975 : Blo 634301 634975 := bstep (se 1 (by rfl) ⟨476231, by rfl⟩ : syracuseStep 634975 = 952463) B952463
theorem B2240627 : Blo 634301 2240627 := bstep (se 1 (by rfl) ⟨1680470, by rfl⟩ : syracuseStep 2240627 = 3360941) B3360941
theorem B635003 : Blo 634301 635003 := bstep (se 1 (by rfl) ⟨476252, by rfl⟩ : syracuseStep 635003 = 952505) B952505
theorem B635055 : Blo 634301 635055 := bstep (se 1 (by rfl) ⟨476291, by rfl⟩ : syracuseStep 635055 = 952583) B952583
theorem B635079 : Blo 634301 635079 := bstep (se 1 (by rfl) ⟨476309, by rfl⟩ : syracuseStep 635079 = 952619) B952619
theorem B635099 : Blo 634301 635099 := bstep (se 1 (by rfl) ⟨476324, by rfl⟩ : syracuseStep 635099 = 952649) B952649
theorem B635175 : Blo 634301 635175 := bstep (se 1 (by rfl) ⟨476381, by rfl⟩ : syracuseStep 635175 = 952763) B952763
theorem B635215 : Blo 634301 635215 := bstep (se 1 (by rfl) ⟨476411, by rfl⟩ : syracuseStep 635215 = 952823) B952823
theorem B635231 : Blo 634301 635231 := bstep (se 1 (by rfl) ⟨476423, by rfl⟩ : syracuseStep 635231 = 952847) B952847
theorem B635259 : Blo 634301 635259 := bstep (se 1 (by rfl) ⟨476444, by rfl⟩ : syracuseStep 635259 = 952889) B952889
theorem B3912065 : Blo 634301 3912065 := bstep (se 2 (by rfl) ⟨1467024, by rfl⟩ : syracuseStep 3912065 = 2934049) B2934049
theorem B635311 : Blo 634301 635311 := bstep (se 1 (by rfl) ⟨476483, by rfl⟩ : syracuseStep 635311 = 952967) B952967
theorem B635335 : Blo 634301 635335 := bstep (se 1 (by rfl) ⟨476501, by rfl⟩ : syracuseStep 635335 = 953003) B953003
theorem B2142665 : Blo 634301 2142665 := bstep (se 2 (by rfl) ⟨803499, by rfl⟩ : syracuseStep 2142665 = 1606999) B1606999
theorem B635355 : Blo 634301 635355 := bstep (se 1 (by rfl) ⟨476516, by rfl⟩ : syracuseStep 635355 = 953033) B953033
theorem B1716761 : Blo 634301 1716761 := bstep (se 2 (by rfl) ⟨643785, by rfl⟩ : syracuseStep 1716761 = 1287571) B1287571
theorem B635431 : Blo 634301 635431 := bstep (se 1 (by rfl) ⟨476573, by rfl⟩ : syracuseStep 635431 = 953147) B953147
theorem B3224123 : Blo 634301 3224123 := bstep (se 1 (by rfl) ⟨2418092, by rfl⟩ : syracuseStep 3224123 = 4836185) B4836185
theorem B635471 : Blo 634301 635471 := bstep (se 1 (by rfl) ⟨476603, by rfl⟩ : syracuseStep 635471 = 953207) B953207
theorem B635487 : Blo 634301 635487 := bstep (se 1 (by rfl) ⟨476615, by rfl⟩ : syracuseStep 635487 = 953231) B953231
theorem B1356385 : Blo 634301 1356385 := bstep (se 2 (by rfl) ⟨508644, by rfl⟩ : syracuseStep 1356385 = 1017289) B1017289
theorem B635515 : Blo 634301 635515 := bstep (se 1 (by rfl) ⟨476636, by rfl⟩ : syracuseStep 635515 = 953273) B953273
theorem B635567 : Blo 634301 635567 := bstep (se 1 (by rfl) ⟨476675, by rfl⟩ : syracuseStep 635567 = 953351) B953351
theorem B635591 : Blo 634301 635591 := bstep (se 1 (by rfl) ⟨476693, by rfl⟩ : syracuseStep 635591 = 953387) B953387
theorem B2142935 : Blo 634301 2142935 := bstep (se 1 (by rfl) ⟨1607201, by rfl⟩ : syracuseStep 2142935 = 3214403) B3214403
theorem B635611 : Blo 634301 635611 := bstep (se 1 (by rfl) ⟨476708, by rfl⟩ : syracuseStep 635611 = 953417) B953417
theorem B2896669 : Blo 634301 2896669 := bstep (se 3 (by rfl) ⟨543125, by rfl⟩ : syracuseStep 2896669 = 1086251) B1086251
theorem B635687 : Blo 634301 635687 := bstep (se 1 (by rfl) ⟨476765, by rfl⟩ : syracuseStep 635687 = 953531) B953531
theorem B635727 : Blo 634301 635727 := bstep (se 1 (by rfl) ⟨476795, by rfl⟩ : syracuseStep 635727 = 953591) B953591
theorem B635743 : Blo 634301 635743 := bstep (se 1 (by rfl) ⟨476807, by rfl⟩ : syracuseStep 635743 = 953615) B953615
theorem B635771 : Blo 634301 635771 := bstep (se 1 (by rfl) ⟨476828, by rfl⟩ : syracuseStep 635771 = 953657) B953657
theorem B2143151 : Blo 634301 2143151 := bstep (se 1 (by rfl) ⟨1607363, by rfl⟩ : syracuseStep 2143151 = 3214727) B3214727
theorem B635823 : Blo 634301 635823 := bstep (se 1 (by rfl) ⟨476867, by rfl⟩ : syracuseStep 635823 = 953735) B953735
theorem B635847 : Blo 634301 635847 := bstep (se 1 (by rfl) ⟨476885, by rfl⟩ : syracuseStep 635847 = 953771) B953771
theorem B635867 : Blo 634301 635867 := bstep (se 1 (by rfl) ⟨476900, by rfl⟩ : syracuseStep 635867 = 953801) B953801
theorem B635943 : Blo 634301 635943 := bstep (se 1 (by rfl) ⟨476957, by rfl⟩ : syracuseStep 635943 = 953915) B953915
theorem B635983 : Blo 634301 635983 := bstep (se 1 (by rfl) ⟨476987, by rfl⟩ : syracuseStep 635983 = 953975) B953975
theorem B635999 : Blo 634301 635999 := bstep (se 1 (by rfl) ⟨476999, by rfl⟩ : syracuseStep 635999 = 953999) B953999
theorem B636027 : Blo 634301 636027 := bstep (se 1 (by rfl) ⟨477020, by rfl⟩ : syracuseStep 636027 = 954041) B954041
theorem B636079 : Blo 634301 636079 := bstep (se 1 (by rfl) ⟨477059, by rfl⟩ : syracuseStep 636079 = 954119) B954119
theorem B3224771 : Blo 634301 3224771 := bstep (se 1 (by rfl) ⟨2418578, by rfl⟩ : syracuseStep 3224771 = 4837157) B4837157
theorem B636103 : Blo 634301 636103 := bstep (se 1 (by rfl) ⟨477077, by rfl⟩ : syracuseStep 636103 = 954155) B954155
theorem B636123 : Blo 634301 636123 := bstep (se 1 (by rfl) ⟨477092, by rfl⟩ : syracuseStep 636123 = 954185) B954185
theorem B636199 : Blo 634301 636199 := bstep (se 1 (by rfl) ⟨477149, by rfl⟩ : syracuseStep 636199 = 954299) B954299
theorem B636239 : Blo 634301 636239 := bstep (se 1 (by rfl) ⟨477179, by rfl⟩ : syracuseStep 636239 = 954359) B954359
theorem B636255 : Blo 634301 636255 := bstep (se 1 (by rfl) ⟨477191, by rfl⟩ : syracuseStep 636255 = 954383) B954383
theorem B636283 : Blo 634301 636283 := bstep (se 1 (by rfl) ⟨477212, by rfl⟩ : syracuseStep 636283 = 954425) B954425
theorem B636335 : Blo 634301 636335 := bstep (se 1 (by rfl) ⟨477251, by rfl⟩ : syracuseStep 636335 = 954503) B954503
theorem B636359 : Blo 634301 636359 := bstep (se 1 (by rfl) ⟨477269, by rfl⟩ : syracuseStep 636359 = 954539) B954539
theorem B636379 : Blo 634301 636379 := bstep (se 1 (by rfl) ⟨477284, by rfl⟩ : syracuseStep 636379 = 954569) B954569
theorem B8173061 : Blo 634301 8173061 := bstep (se 4 (by rfl) ⟨766224, by rfl⟩ : syracuseStep 8173061 = 1532449) B1532449
theorem B636455 : Blo 634301 636455 := bstep (se 1 (by rfl) ⟨477341, by rfl⟩ : syracuseStep 636455 = 954683) B954683
theorem B636495 : Blo 634301 636495 := bstep (se 1 (by rfl) ⟨477371, by rfl⟩ : syracuseStep 636495 = 954743) B954743
theorem B636511 : Blo 634301 636511 := bstep (se 1 (by rfl) ⟨477383, by rfl⟩ : syracuseStep 636511 = 954767) B954767
theorem B6895201 : Blo 634301 6895201 := bstep (se 2 (by rfl) ⟨2585700, by rfl⟩ : syracuseStep 6895201 = 5171401) B5171401
theorem B636539 : Blo 634301 636539 := bstep (se 1 (by rfl) ⟨477404, by rfl⟩ : syracuseStep 636539 = 954809) B954809
theorem B636591 : Blo 634301 636591 := bstep (se 1 (by rfl) ⟨477443, by rfl⟩ : syracuseStep 636591 = 954887) B954887
theorem B636615 : Blo 634301 636615 := bstep (se 1 (by rfl) ⟨477461, by rfl⟩ : syracuseStep 636615 = 954923) B954923
theorem B636635 : Blo 634301 636635 := bstep (se 1 (by rfl) ⟨477476, by rfl⟩ : syracuseStep 636635 = 954953) B954953
theorem B636711 : Blo 634301 636711 := bstep (se 1 (by rfl) ⟨477533, by rfl⟩ : syracuseStep 636711 = 955067) B955067
theorem B4896571 : Blo 634301 4896571 := bstep (se 1 (by rfl) ⟨3672428, by rfl⟩ : syracuseStep 4896571 = 7344857) B7344857
theorem B636751 : Blo 634301 636751 := bstep (se 1 (by rfl) ⟨477563, by rfl⟩ : syracuseStep 636751 = 955127) B955127
theorem B636767 : Blo 634301 636767 := bstep (se 1 (by rfl) ⟨477575, by rfl⟩ : syracuseStep 636767 = 955151) B955151
theorem B636795 : Blo 634301 636795 := bstep (se 1 (by rfl) ⟨477596, by rfl⟩ : syracuseStep 636795 = 955193) B955193
theorem B636847 : Blo 634301 636847 := bstep (se 1 (by rfl) ⟨477635, by rfl⟩ : syracuseStep 636847 = 955271) B955271
theorem B636871 : Blo 634301 636871 := bstep (se 1 (by rfl) ⟨477653, by rfl⟩ : syracuseStep 636871 = 955307) B955307
theorem B636891 : Blo 634301 636891 := bstep (se 1 (by rfl) ⟨477668, by rfl⟩ : syracuseStep 636891 = 955337) B955337
theorem B636967 : Blo 634301 636967 := bstep (se 1 (by rfl) ⟨477725, by rfl⟩ : syracuseStep 636967 = 955451) B955451
theorem B637007 : Blo 634301 637007 := bstep (se 1 (by rfl) ⟨477755, by rfl⟩ : syracuseStep 637007 = 955511) B955511
theorem B637023 : Blo 634301 637023 := bstep (se 1 (by rfl) ⟨477767, by rfl⟩ : syracuseStep 637023 = 955535) B955535
theorem B637051 : Blo 634301 637051 := bstep (se 1 (by rfl) ⟨477788, by rfl⟩ : syracuseStep 637051 = 955577) B955577
theorem B637103 : Blo 634301 637103 := bstep (se 1 (by rfl) ⟨477827, by rfl⟩ : syracuseStep 637103 = 955655) B955655
theorem B637127 : Blo 634301 637127 := bstep (se 1 (by rfl) ⟨477845, by rfl⟩ : syracuseStep 637127 = 955691) B955691
theorem B637147 : Blo 634301 637147 := bstep (se 1 (by rfl) ⟨477860, by rfl⟩ : syracuseStep 637147 = 955721) B955721
theorem B637223 : Blo 634301 637223 := bstep (se 1 (by rfl) ⟨477917, by rfl⟩ : syracuseStep 637223 = 955835) B955835
theorem B637263 : Blo 634301 637263 := bstep (se 1 (by rfl) ⟨477947, by rfl⟩ : syracuseStep 637263 = 955895) B955895
theorem B637279 : Blo 634301 637279 := bstep (se 1 (by rfl) ⟨477959, by rfl⟩ : syracuseStep 637279 = 955919) B955919
theorem B637307 : Blo 634301 637307 := bstep (se 1 (by rfl) ⟨477980, by rfl⟩ : syracuseStep 637307 = 955961) B955961
theorem B637359 : Blo 634301 637359 := bstep (se 1 (by rfl) ⟨478019, by rfl⟩ : syracuseStep 637359 = 956039) B956039
theorem B637383 : Blo 634301 637383 := bstep (se 1 (by rfl) ⟨478037, by rfl⟩ : syracuseStep 637383 = 956075) B956075
theorem B15350219 : Blo 634301 15350219 := bstep (se 1 (by rfl) ⟨11512664, by rfl⟩ : syracuseStep 15350219 = 23025329) B23025329
theorem B637403 : Blo 634301 637403 := bstep (se 1 (by rfl) ⟨478052, by rfl⟩ : syracuseStep 637403 = 956105) B956105
theorem B1817113 : Blo 634301 1817113 := bstep (se 2 (by rfl) ⟨681417, by rfl⟩ : syracuseStep 1817113 = 1362835) B1362835
theorem B637479 : Blo 634301 637479 := bstep (se 1 (by rfl) ⟨478109, by rfl⟩ : syracuseStep 637479 = 956219) B956219
theorem B637519 : Blo 634301 637519 := bstep (se 1 (by rfl) ⟨478139, by rfl⟩ : syracuseStep 637519 = 956279) B956279
theorem B637535 : Blo 634301 637535 := bstep (se 1 (by rfl) ⟨478151, by rfl⟩ : syracuseStep 637535 = 956303) B956303
theorem B637563 : Blo 634301 637563 := bstep (se 1 (by rfl) ⟨478172, by rfl⟩ : syracuseStep 637563 = 956345) B956345
theorem B637615 : Blo 634301 637615 := bstep (se 1 (by rfl) ⟨478211, by rfl⟩ : syracuseStep 637615 = 956423) B956423
theorem B637639 : Blo 634301 637639 := bstep (se 1 (by rfl) ⟨478229, by rfl⟩ : syracuseStep 637639 = 956459) B956459
theorem B1653463 : Blo 634301 1653463 := bstep (se 1 (by rfl) ⟨1240097, by rfl⟩ : syracuseStep 1653463 = 2480195) B2480195
theorem B637659 : Blo 634301 637659 := bstep (se 1 (by rfl) ⟨478244, by rfl⟩ : syracuseStep 637659 = 956489) B956489
theorem B637735 : Blo 634301 637735 := bstep (se 1 (by rfl) ⟨478301, by rfl⟩ : syracuseStep 637735 = 956603) B956603
theorem B637775 : Blo 634301 637775 := bstep (se 1 (by rfl) ⟨478331, by rfl⟩ : syracuseStep 637775 = 956663) B956663
theorem B637791 : Blo 634301 637791 := bstep (se 1 (by rfl) ⟨478343, by rfl⟩ : syracuseStep 637791 = 956687) B956687
theorem B637819 : Blo 634301 637819 := bstep (se 1 (by rfl) ⟨478364, by rfl⟩ : syracuseStep 637819 = 956729) B956729
theorem B637871 : Blo 634301 637871 := bstep (se 1 (by rfl) ⟨478403, by rfl⟩ : syracuseStep 637871 = 956807) B956807
theorem B637895 : Blo 634301 637895 := bstep (se 1 (by rfl) ⟨478421, by rfl⟩ : syracuseStep 637895 = 956843) B956843
theorem B637915 : Blo 634301 637915 := bstep (se 1 (by rfl) ⟨478436, by rfl⟩ : syracuseStep 637915 = 956873) B956873
theorem B637991 : Blo 634301 637991 := bstep (se 1 (by rfl) ⟨478493, by rfl⟩ : syracuseStep 637991 = 956987) B956987
theorem B638031 : Blo 634301 638031 := bstep (se 1 (by rfl) ⟨478523, by rfl⟩ : syracuseStep 638031 = 957047) B957047
theorem B638047 : Blo 634301 638047 := bstep (se 1 (by rfl) ⟨478535, by rfl⟩ : syracuseStep 638047 = 957071) B957071
theorem B638075 : Blo 634301 638075 := bstep (se 1 (by rfl) ⟨478556, by rfl⟩ : syracuseStep 638075 = 957113) B957113
theorem B638127 : Blo 634301 638127 := bstep (se 1 (by rfl) ⟨478595, by rfl⟩ : syracuseStep 638127 = 957191) B957191
theorem B638151 : Blo 634301 638151 := bstep (se 1 (by rfl) ⟨478613, by rfl⟩ : syracuseStep 638151 = 957227) B957227
theorem B638171 : Blo 634301 638171 := bstep (se 1 (by rfl) ⟨478628, by rfl⟩ : syracuseStep 638171 = 957257) B957257
theorem B2145527 : Blo 634301 2145527 := bstep (se 1 (by rfl) ⟨1609145, by rfl⟩ : syracuseStep 2145527 = 3218291) B3218291
theorem B638247 : Blo 634301 638247 := bstep (se 1 (by rfl) ⟨478685, by rfl⟩ : syracuseStep 638247 = 957371) B957371
theorem B638287 : Blo 634301 638287 := bstep (se 1 (by rfl) ⟨478715, by rfl⟩ : syracuseStep 638287 = 957431) B957431
theorem B2145851 : Blo 634301 2145851 := bstep (se 1 (by rfl) ⟨1609388, by rfl⟩ : syracuseStep 2145851 = 3218777) B3218777
theorem B2211467 : Blo 634301 2211467 := bstep (se 1 (by rfl) ⟨1658600, by rfl⟩ : syracuseStep 2211467 = 3317201) B3317201
theorem B6110957 : Blo 634301 6110957 := bstep (se 3 (by rfl) ⟨1145804, by rfl⟩ : syracuseStep 6110957 = 2291609) B2291609
theorem B7257923 : Blo 634301 7257923 := bstep (se 1 (by rfl) ⟨5443442, by rfl⟩ : syracuseStep 7257923 = 10886885) B10886885
theorem B2146121 : Blo 634301 2146121 := bstep (se 2 (by rfl) ⟨804795, by rfl⟩ : syracuseStep 2146121 = 1609591) B1609591
theorem B2572289 : Blo 634301 2572289 := bstep (se 2 (by rfl) ⟨964608, by rfl⟩ : syracuseStep 2572289 = 1929217) B1929217
theorem B3064169 : Blo 634301 3064169 := bstep (se 2 (by rfl) ⟨1149063, by rfl⟩ : syracuseStep 3064169 = 2298127) B2298127
theorem B1524473 : Blo 634301 1524473 := bstep (se 2 (by rfl) ⟨571677, by rfl⟩ : syracuseStep 1524473 = 1143355) B1143355
theorem B2409209 : Blo 634301 2409209 := bstep (se 2 (by rfl) ⟨903453, by rfl⟩ : syracuseStep 2409209 = 1806907) B1806907
theorem B1164025 : Blo 634301 1164025 := bstep (se 2 (by rfl) ⟨436509, by rfl⟩ : syracuseStep 1164025 = 873019) B873019
theorem B1524587 : Blo 634301 1524587 := bstep (se 1 (by rfl) ⟨1143440, by rfl⟩ : syracuseStep 1524587 = 2286881) B2286881
theorem B2147255 : Blo 634301 2147255 := bstep (se 1 (by rfl) ⟨1610441, by rfl⟩ : syracuseStep 2147255 = 3220883) B3220883
theorem B17384395 : Blo 634301 17384395 := bstep (se 1 (by rfl) ⟨13038296, by rfl⟩ : syracuseStep 17384395 = 26076593) B26076593
theorem B2573507 : Blo 634301 2573507 := bstep (se 1 (by rfl) ⟨1930130, by rfl⟩ : syracuseStep 2573507 = 3860261) B3860261
theorem B9192851 : Blo 634301 9192851 := bstep (se 1 (by rfl) ⟨6894638, by rfl⟩ : syracuseStep 9192851 = 13789277) B13789277
theorem B2147849 : Blo 634301 2147849 := bstep (se 2 (by rfl) ⟨805443, by rfl⟩ : syracuseStep 2147849 = 1610887) B1610887
theorem B804431 : Blo 634301 804431 := bstep (se 1 (by rfl) ⟨603323, by rfl⟩ : syracuseStep 804431 = 1206647) B1206647
theorem B3229307 : Blo 634301 3229307 := bstep (se 1 (by rfl) ⟨2421980, by rfl⟩ : syracuseStep 3229307 = 4843961) B4843961
theorem B2410195 : Blo 634301 2410195 := bstep (se 1 (by rfl) ⟨1807646, by rfl⟩ : syracuseStep 2410195 = 3615293) B3615293
theorem B1427273 : Blo 634301 1427273 := bstep (se 2 (by rfl) ⟨535227, by rfl⟩ : syracuseStep 1427273 = 1070455) B1070455
theorem B2443115 : Blo 634301 2443115 := bstep (se 1 (by rfl) ⟨1832336, by rfl⟩ : syracuseStep 2443115 = 3664673) B3664673
theorem B3622765 : Blo 634301 3622765 := bstep (se 3 (by rfl) ⟨679268, by rfl⟩ : syracuseStep 3622765 = 1358537) B1358537
theorem B5163097 : Blo 634301 5163097 := bstep (se 2 (by rfl) ⟨1936161, by rfl⟩ : syracuseStep 5163097 = 3872323) B3872323
theorem B30951517 : Blo 634301 30951517 := bstep (se 3 (by rfl) ⟨5803409, by rfl⟩ : syracuseStep 30951517 = 11606819) B11606819
theorem B2410667 : Blo 634301 2410667 := bstep (se 1 (by rfl) ⟨1808000, by rfl⟩ : syracuseStep 2410667 = 3616001) B3616001
theorem B1362091 : Blo 634301 1362091 := bstep (se 1 (by rfl) ⟨1021568, by rfl⟩ : syracuseStep 1362091 = 2043137) B2043137
theorem B18368855 : Blo 634301 18368855 := bstep (se 1 (by rfl) ⟨13776641, by rfl⟩ : syracuseStep 18368855 = 27553283) B27553283
theorem B2148713 : Blo 634301 2148713 := bstep (se 2 (by rfl) ⟨805767, by rfl⟩ : syracuseStep 2148713 = 1611535) B1611535
theorem B8243693 : Blo 634301 8243693 := bstep (se 3 (by rfl) ⟨1545692, by rfl⟩ : syracuseStep 8243693 = 3091385) B3091385
theorem B1428065 : Blo 634301 1428065 := bstep (se 2 (by rfl) ⟨535524, by rfl⟩ : syracuseStep 1428065 = 1071049) B1071049
theorem B805727 : Blo 634301 805727 := bstep (se 1 (by rfl) ⟨604295, by rfl⟩ : syracuseStep 805727 = 1208591) B1208591
theorem B1428407 : Blo 634301 1428407 := bstep (se 1 (by rfl) ⟨1071305, by rfl⟩ : syracuseStep 1428407 = 2142611) B2142611
theorem B2149307 : Blo 634301 2149307 := bstep (se 1 (by rfl) ⟨1611980, by rfl⟩ : syracuseStep 2149307 = 3223961) B3223961
theorem B1429001 : Blo 634301 1429001 := bstep (se 2 (by rfl) ⟨535875, by rfl⟩ : syracuseStep 1429001 = 1071751) B1071751
theorem B1429343 : Blo 634301 1429343 := bstep (se 1 (by rfl) ⟨1072007, by rfl⟩ : syracuseStep 1429343 = 2144015) B2144015
theorem B1429523 : Blo 634301 1429523 := bstep (se 1 (by rfl) ⟨1072142, by rfl⟩ : syracuseStep 1429523 = 2144285) B2144285
theorem B2576441 : Blo 634301 2576441 := bstep (se 2 (by rfl) ⟨966165, by rfl⟩ : syracuseStep 2576441 = 1932331) B1932331
theorem B2412625 : Blo 634301 2412625 := bstep (se 2 (by rfl) ⟨904734, by rfl⟩ : syracuseStep 2412625 = 1809469) B1809469
theorem B5820497 : Blo 634301 5820497 := bstep (se 2 (by rfl) ⟨2182686, by rfl⟩ : syracuseStep 5820497 = 4365373) B4365373
theorem B22106317 : Blo 634301 22106317 := bstep (se 3 (by rfl) ⟨4144934, by rfl⟩ : syracuseStep 22106317 = 8289869) B8289869
theorem B4837643 : Blo 634301 4837643 := bstep (se 1 (by rfl) ⟨3628232, by rfl⟩ : syracuseStep 4837643 = 7256465) B7256465
theorem B4084019 : Blo 634301 4084019 := bstep (se 1 (by rfl) ⟨3063014, by rfl⟩ : syracuseStep 4084019 = 6126029) B6126029
theorem B1429865 : Blo 634301 1429865 := bstep (se 2 (by rfl) ⟨536199, by rfl⟩ : syracuseStep 1429865 = 1072399) B1072399
theorem B2412929 : Blo 634301 2412929 := bstep (se 2 (by rfl) ⟨904848, by rfl⟩ : syracuseStep 2412929 = 1809697) B1809697
theorem B4084121 : Blo 634301 4084121 := bstep (se 2 (by rfl) ⟨1531545, by rfl⟩ : syracuseStep 4084121 = 3063091) B3063091
theorem B905737 : Blo 634301 905737 := bstep (se 2 (by rfl) ⟨339651, by rfl⟩ : syracuseStep 905737 = 679303) B679303
theorem B905851 : Blo 634301 905851 := bstep (se 1 (by rfl) ⟨679388, by rfl⟩ : syracuseStep 905851 = 1358777) B1358777
theorem B2151035 : Blo 634301 2151035 := bstep (se 1 (by rfl) ⟨1613276, by rfl⟩ : syracuseStep 2151035 = 3226553) B3226553
theorem B4707017 : Blo 634301 4707017 := bstep (se 2 (by rfl) ⟨1765131, by rfl⟩ : syracuseStep 4707017 = 3530263) B3530263
theorem B3625681 : Blo 634301 3625681 := bstep (se 2 (by rfl) ⟨1359630, by rfl⟩ : syracuseStep 3625681 = 2719261) B2719261
theorem B2151197 : Blo 634301 2151197 := bstep (se 3 (by rfl) ⟨403349, by rfl⟩ : syracuseStep 2151197 = 806699) B806699
theorem B5493577 : Blo 634301 5493577 := bstep (se 2 (by rfl) ⟨2060091, by rfl⟩ : syracuseStep 5493577 = 4120183) B4120183
theorem B2413385 : Blo 634301 2413385 := bstep (se 2 (by rfl) ⟨905019, by rfl⟩ : syracuseStep 2413385 = 1810039) B1810039
theorem B906079 : Blo 634301 906079 := bstep (se 1 (by rfl) ⟨679559, by rfl⟩ : syracuseStep 906079 = 1359119) B1359119
theorem B1430459 : Blo 634301 1430459 := bstep (se 1 (by rfl) ⟨1072844, by rfl⟩ : syracuseStep 1430459 = 2145689) B2145689
theorem B2413583 : Blo 634301 2413583 := bstep (se 1 (by rfl) ⟨1810187, by rfl⟩ : syracuseStep 2413583 = 3620375) B3620375
theorem B1430585 : Blo 634301 1430585 := bstep (se 2 (by rfl) ⟨536469, by rfl⟩ : syracuseStep 1430585 = 1072939) B1072939
theorem B1430927 : Blo 634301 1430927 := bstep (se 1 (by rfl) ⟨1073195, by rfl⟩ : syracuseStep 1430927 = 2146391) B2146391
theorem B906671 : Blo 634301 906671 := bstep (se 1 (by rfl) ⟨680003, by rfl⟩ : syracuseStep 906671 = 1360007) B1360007
theorem B2151899 : Blo 634301 2151899 := bstep (se 1 (by rfl) ⟨1613924, by rfl⟩ : syracuseStep 2151899 = 3227849) B3227849
theorem B7263755 : Blo 634301 7263755 := bstep (se 1 (by rfl) ⟨5447816, by rfl⟩ : syracuseStep 7263755 = 10895633) B10895633
theorem B1070671 : Blo 634301 1070671 := bstep (se 1 (by rfl) ⟨803003, by rfl⟩ : syracuseStep 1070671 = 1606007) B1606007
theorem B4839101 : Blo 634301 4839101 := bstep (se 3 (by rfl) ⟨907331, by rfl⟩ : syracuseStep 4839101 = 1814663) B1814663
theorem B1431251 : Blo 634301 1431251 := bstep (se 1 (by rfl) ⟨1073438, by rfl⟩ : syracuseStep 1431251 = 2146877) B2146877
theorem B1070921 : Blo 634301 1070921 := bstep (se 2 (by rfl) ⟨401595, by rfl⟩ : syracuseStep 1070921 = 803191) B803191
theorem B2152601 : Blo 634301 2152601 := bstep (se 2 (by rfl) ⟨807225, by rfl⟩ : syracuseStep 2152601 = 1614451) B1614451
theorem B4839587 : Blo 634301 4839587 := bstep (se 1 (by rfl) ⟨3629690, by rfl⟩ : syracuseStep 4839587 = 7259381) B7259381
theorem B907463 : Blo 634301 907463 := bstep (se 1 (by rfl) ⟨680597, by rfl⟩ : syracuseStep 907463 = 1361195) B1361195
theorem B1071353 : Blo 634301 1071353 := bstep (se 2 (by rfl) ⟨401757, by rfl⟩ : syracuseStep 1071353 = 803515) B803515
theorem B11032937 : Blo 634301 11032937 := bstep (se 2 (by rfl) ⟨4137351, by rfl⟩ : syracuseStep 11032937 = 8274703) B8274703
theorem B1071535 : Blo 634301 1071535 := bstep (se 1 (by rfl) ⟨803651, by rfl⟩ : syracuseStep 1071535 = 1607303) B1607303
theorem B1071623 : Blo 634301 1071623 := bstep (se 1 (by rfl) ⟨803717, by rfl⟩ : syracuseStep 1071623 = 1607435) B1607435
theorem B2578969 : Blo 634301 2578969 := bstep (se 2 (by rfl) ⟨967113, by rfl⟩ : syracuseStep 2578969 = 1934227) B1934227
theorem B1432187 : Blo 634301 1432187 := bstep (se 1 (by rfl) ⟨1074140, by rfl⟩ : syracuseStep 1432187 = 2148281) B2148281
theorem B1432313 : Blo 634301 1432313 := bstep (se 2 (by rfl) ⟨537117, by rfl⟩ : syracuseStep 1432313 = 1074235) B1074235
theorem B1071967 : Blo 634301 1071967 := bstep (se 1 (by rfl) ⟨803975, by rfl⟩ : syracuseStep 1071967 = 1607951) B1607951
theorem B1072055 : Blo 634301 1072055 := bstep (se 1 (by rfl) ⟨804041, by rfl⟩ : syracuseStep 1072055 = 1608083) B1608083
theorem B1432583 : Blo 634301 1432583 := bstep (se 1 (by rfl) ⟨1074437, by rfl⟩ : syracuseStep 1432583 = 2148875) B2148875
theorem B1432655 : Blo 634301 1432655 := bstep (se 1 (by rfl) ⟨1074491, by rfl⟩ : syracuseStep 1432655 = 2148983) B2148983
theorem B646267 : Blo 634301 646267 := bstep (se 1 (by rfl) ⟨484700, by rfl⟩ : syracuseStep 646267 = 969401) B969401
theorem B2153789 : Blo 634301 2153789 := bstep (se 3 (by rfl) ⟨403835, by rfl⟩ : syracuseStep 2153789 = 807671) B807671
theorem B1433051 : Blo 634301 1433051 := bstep (se 1 (by rfl) ⟨1074788, by rfl⟩ : syracuseStep 1433051 = 2149577) B2149577
theorem B1072649 : Blo 634301 1072649 := bstep (se 2 (by rfl) ⟨402243, by rfl⟩ : syracuseStep 1072649 = 804487) B804487
theorem B2580007 : Blo 634301 2580007 := bstep (se 1 (by rfl) ⟨1935005, by rfl⟩ : syracuseStep 2580007 = 3870011) B3870011
theorem B3858043 : Blo 634301 3858043 := bstep (se 1 (by rfl) ⟨2893532, by rfl⟩ : syracuseStep 3858043 = 5787065) B5787065
theorem B1072811 : Blo 634301 1072811 := bstep (se 1 (by rfl) ⟨804608, by rfl⟩ : syracuseStep 1072811 = 1609217) B1609217
theorem B1433519 : Blo 634301 1433519 := bstep (se 1 (by rfl) ⟨1075139, by rfl⟩ : syracuseStep 1433519 = 2150279) B2150279
theorem B1531835 : Blo 634301 1531835 := bstep (se 1 (by rfl) ⟨1148876, by rfl⟩ : syracuseStep 1531835 = 2297753) B2297753
theorem B1073209 : Blo 634301 1073209 := bstep (se 2 (by rfl) ⟨402453, by rfl⟩ : syracuseStep 1073209 = 804907) B804907
theorem B1433771 : Blo 634301 1433771 := bstep (se 1 (by rfl) ⟨1075328, by rfl⟩ : syracuseStep 1433771 = 2150657) B2150657
theorem B1073351 : Blo 634301 1073351 := bstep (se 1 (by rfl) ⟨805013, by rfl⟩ : syracuseStep 1073351 = 1610027) B1610027
theorem B1073513 : Blo 634301 1073513 := bstep (se 2 (by rfl) ⟨402567, by rfl⟩ : syracuseStep 1073513 = 805135) B805135
theorem B4842017 : Blo 634301 4842017 := bstep (se 2 (by rfl) ⟨1815756, by rfl⟩ : syracuseStep 4842017 = 3631513) B3631513
theorem B1434311 : Blo 634301 1434311 := bstep (se 1 (by rfl) ⟨1075733, by rfl⟩ : syracuseStep 1434311 = 2151467) B2151467
theorem B2712275 : Blo 634301 2712275 := bstep (se 1 (by rfl) ⟨2034206, by rfl⟩ : syracuseStep 2712275 = 4068413) B4068413
theorem B1073911 : Blo 634301 1073911 := bstep (se 1 (by rfl) ⟨805433, by rfl⟩ : syracuseStep 1073911 = 1610867) B1610867
theorem B1074107 : Blo 634301 1074107 := bstep (se 1 (by rfl) ⟨805580, by rfl⟩ : syracuseStep 1074107 = 1611161) B1611161
theorem B713767 : Blo 634301 713767 := bstep (se 1 (by rfl) ⟨535325, by rfl⟩ : syracuseStep 713767 = 1070651) B1070651
theorem B1074215 : Blo 634301 1074215 := bstep (se 1 (by rfl) ⟨805661, by rfl⟩ : syracuseStep 1074215 = 1611323) B1611323
theorem B1205371 : Blo 634301 1205371 := bstep (se 1 (by rfl) ⟨904028, by rfl⟩ : syracuseStep 1205371 = 1808057) B1808057
theorem B1074505 : Blo 634301 1074505 := bstep (se 2 (by rfl) ⟨402939, by rfl⟩ : syracuseStep 1074505 = 805879) B805879
theorem B1205599 : Blo 634301 1205599 := bstep (se 1 (by rfl) ⟨904199, by rfl⟩ : syracuseStep 1205599 = 1808399) B1808399
theorem B1074539 : Blo 634301 1074539 := bstep (se 1 (by rfl) ⟨805904, by rfl⟩ : syracuseStep 1074539 = 1611809) B1611809
theorem B1238537 : Blo 634301 1238537 := bstep (se 2 (by rfl) ⟨464451, by rfl⟩ : syracuseStep 1238537 = 928903) B928903
theorem B1435175 : Blo 634301 1435175 := bstep (se 1 (by rfl) ⟨1076381, by rfl⟩ : syracuseStep 1435175 = 2152763) B2152763
theorem B1205857 : Blo 634301 1205857 := bstep (se 2 (by rfl) ⟨452196, by rfl⟩ : syracuseStep 1205857 = 904393) B904393
theorem B1074937 : Blo 634301 1074937 := bstep (se 2 (by rfl) ⟨403101, by rfl⟩ : syracuseStep 1074937 = 806203) B806203
theorem B1435499 : Blo 634301 1435499 := bstep (se 1 (by rfl) ⟨1076624, by rfl⟩ : syracuseStep 1435499 = 2153249) B2153249
theorem B1435553 : Blo 634301 1435553 := bstep (se 2 (by rfl) ⟨538332, by rfl⟩ : syracuseStep 1435553 = 1076665) B1076665
theorem B1206191 : Blo 634301 1206191 := bstep (se 1 (by rfl) ⟨904643, by rfl⟩ : syracuseStep 1206191 = 1809287) B1809287
theorem B1075207 : Blo 634301 1075207 := bstep (se 1 (by rfl) ⟨806405, by rfl⟩ : syracuseStep 1075207 = 1612811) B1612811
theorem B2713657 : Blo 634301 2713657 := bstep (se 2 (by rfl) ⟨1017621, by rfl⟩ : syracuseStep 2713657 = 2035243) B2035243
theorem B9398359 : Blo 634301 9398359 := bstep (se 1 (by rfl) ⟨7048769, by rfl⟩ : syracuseStep 9398359 = 14097539) B14097539
theorem B1435895 : Blo 634301 1435895 := bstep (se 1 (by rfl) ⟨1076921, by rfl⟩ : syracuseStep 1435895 = 2153843) B2153843
theorem B5433601 : Blo 634301 5433601 := bstep (se 2 (by rfl) ⟨2037600, by rfl⟩ : syracuseStep 5433601 = 4075201) B4075201
theorem B1075639 : Blo 634301 1075639 := bstep (se 1 (by rfl) ⟨806729, by rfl⟩ : syracuseStep 1075639 = 1613459) B1613459
theorem B715387 : Blo 634301 715387 := bstep (se 1 (by rfl) ⟨536540, by rfl⟩ : syracuseStep 715387 = 1073081) B1073081
theorem B1075835 : Blo 634301 1075835 := bstep (se 1 (by rfl) ⟨806876, by rfl⟩ : syracuseStep 1075835 = 1613753) B1613753
theorem B2419415 : Blo 634301 2419415 := bstep (se 1 (by rfl) ⟨1814561, by rfl⟩ : syracuseStep 2419415 = 3629123) B3629123
theorem B3861251 : Blo 634301 3861251 := bstep (se 1 (by rfl) ⟨2895938, by rfl⟩ : syracuseStep 3861251 = 5791877) B5791877
theorem B2911049 : Blo 634301 2911049 := bstep (se 2 (by rfl) ⟨1091643, by rfl⟩ : syracuseStep 2911049 = 2183287) B2183287
theorem B3435493 : Blo 634301 3435493 := bstep (se 4 (by rfl) ⟨322077, by rfl⟩ : syracuseStep 3435493 = 644155) B644155
theorem B1076233 : Blo 634301 1076233 := bstep (se 2 (by rfl) ⟨403587, by rfl⟩ : syracuseStep 1076233 = 807175) B807175
theorem B1207315 : Blo 634301 1207315 := bstep (se 1 (by rfl) ⟨905486, by rfl⟩ : syracuseStep 1207315 = 1810973) B1810973
theorem B9923627 : Blo 634301 9923627 := bstep (se 1 (by rfl) ⟨7442720, by rfl⟩ : syracuseStep 9923627 = 14885441) B14885441
theorem B715855 : Blo 634301 715855 := bstep (se 1 (by rfl) ⟨536891, by rfl⟩ : syracuseStep 715855 = 1073783) B1073783
theorem B1076395 : Blo 634301 1076395 := bstep (se 1 (by rfl) ⟨807296, by rfl⟩ : syracuseStep 1076395 = 1614593) B1614593
theorem B1207543 : Blo 634301 1207543 := bstep (se 1 (by rfl) ⟨905657, by rfl⟩ : syracuseStep 1207543 = 1811315) B1811315
theorem B716251 : Blo 634301 716251 := bstep (se 1 (by rfl) ⟨537188, by rfl⟩ : syracuseStep 716251 = 1074377) B1074377
theorem B1076699 : Blo 634301 1076699 := bstep (se 1 (by rfl) ⟨807524, by rfl⟩ : syracuseStep 1076699 = 1615049) B1615049
theorem B1207847 : Blo 634301 1207847 := bstep (se 1 (by rfl) ⟨905885, by rfl⟩ : syracuseStep 1207847 = 1811771) B1811771
theorem B1076935 : Blo 634301 1076935 := bstep (se 1 (by rfl) ⟨807701, by rfl⟩ : syracuseStep 1076935 = 1615403) B1615403
theorem B1077097 : Blo 634301 1077097 := bstep (se 2 (by rfl) ⟨403911, by rfl⟩ : syracuseStep 1077097 = 807823) B807823
theorem B7237511 : Blo 634301 7237511 := bstep (se 1 (by rfl) ⟨5428133, by rfl⟩ : syracuseStep 7237511 = 10856267) B10856267
theorem B716719 : Blo 634301 716719 := bstep (se 1 (by rfl) ⟨537539, by rfl⟩ : syracuseStep 716719 = 1075079) B1075079
theorem B11595953 : Blo 634301 11595953 := bstep (se 2 (by rfl) ⟨4348482, by rfl⟩ : syracuseStep 11595953 = 8696965) B8696965
theorem B717151 : Blo 634301 717151 := bstep (se 1 (by rfl) ⟨537863, by rfl⟩ : syracuseStep 717151 = 1075727) B1075727
theorem B2519687 : Blo 634301 2519687 := bstep (se 1 (by rfl) ⟨1889765, by rfl⟩ : syracuseStep 2519687 = 3779531) B3779531
theorem B717511 : Blo 634301 717511 := bstep (se 1 (by rfl) ⟨538133, by rfl⟩ : syracuseStep 717511 = 1076267) B1076267
theorem B3928787 : Blo 634301 3928787 := bstep (se 1 (by rfl) ⟨2946590, by rfl⟩ : syracuseStep 3928787 = 5893181) B5893181
theorem B1209161 : Blo 634301 1209161 := bstep (se 2 (by rfl) ⟨453435, by rfl⟩ : syracuseStep 1209161 = 906871) B906871
theorem B5174093 : Blo 634301 5174093 := bstep (se 3 (by rfl) ⟨970142, by rfl⟩ : syracuseStep 5174093 = 1940285) B1940285
theorem B5436335 : Blo 634301 5436335 := bstep (se 1 (by rfl) ⟨4077251, by rfl⟩ : syracuseStep 5436335 = 8154503) B8154503
theorem B2749367 : Blo 634301 2749367 := bstep (se 1 (by rfl) ⟨2062025, by rfl⟩ : syracuseStep 2749367 = 4124051) B4124051
theorem B1209593 : Blo 634301 1209593 := bstep (se 2 (by rfl) ⟨453597, by rfl⟩ : syracuseStep 1209593 = 907195) B907195
theorem B10614179 : Blo 634301 10614179 := bstep (se 1 (by rfl) ⟨7960634, by rfl⟩ : syracuseStep 10614179 = 15921269) B15921269
theorem B2422331 : Blo 634301 2422331 := bstep (se 1 (by rfl) ⟨1816748, by rfl⟩ : syracuseStep 2422331 = 3633497) B3633497
theorem B8156963 : Blo 634301 8156963 := bstep (se 1 (by rfl) ⟨6117722, by rfl⟩ : syracuseStep 8156963 = 12235445) B12235445
theorem B1144955 : Blo 634301 1144955 := bstep (se 1 (by rfl) ⟨858716, by rfl⟩ : syracuseStep 1144955 = 1717433) B1717433
theorem B2455705 : Blo 634301 2455705 := bstep (se 2 (by rfl) ⟨920889, by rfl⟩ : syracuseStep 2455705 = 1841779) B1841779
theorem B4585729 : Blo 634301 4585729 := bstep (se 2 (by rfl) ⟨1719648, by rfl⟩ : syracuseStep 4585729 = 3439297) B3439297
theorem B1211051 : Blo 634301 1211051 := bstep (se 1 (by rfl) ⟨908288, by rfl⟩ : syracuseStep 1211051 = 1816577) B1816577
theorem B16546481 : Blo 634301 16546481 := bstep (se 2 (by rfl) ⟨6204930, by rfl⟩ : syracuseStep 16546481 = 12409861) B12409861
theorem B2718647 : Blo 634301 2718647 := bstep (se 1 (by rfl) ⟨2038985, by rfl⟩ : syracuseStep 2718647 = 4077971) B4077971
theorem B2456507 : Blo 634301 2456507 := bstep (se 1 (by rfl) ⟨1842380, by rfl⟩ : syracuseStep 2456507 = 3684761) B3684761
theorem B1145863 : Blo 634301 1145863 := bstep (se 1 (by rfl) ⟨859397, by rfl⟩ : syracuseStep 1145863 = 1718795) B1718795
theorem B1211431 : Blo 634301 1211431 := bstep (se 1 (by rfl) ⟨908573, by rfl⟩ : syracuseStep 1211431 = 1817147) B1817147
theorem B1211591 : Blo 634301 1211591 := bstep (se 1 (by rfl) ⟨908693, by rfl⟩ : syracuseStep 1211591 = 1817387) B1817387
theorem B2293571 : Blo 634301 2293571 := bstep (se 1 (by rfl) ⟨1720178, by rfl⟩ : syracuseStep 2293571 = 3440357) B3440357
theorem B22020173 : Blo 634301 22020173 := bstep (se 3 (by rfl) ⟨4128782, by rfl⟩ : syracuseStep 22020173 = 8257565) B8257565
theorem B1016315 : Blo 634301 1016315 := bstep (se 1 (by rfl) ⟨762236, by rfl⟩ : syracuseStep 1016315 = 1524473) B1524473
theorem B1606139 : Blo 634301 1606139 := bstep (se 1 (by rfl) ⟨1204604, by rfl⟩ : syracuseStep 1606139 = 2409209) B2409209
theorem B6128567 : Blo 634301 6128567 := bstep (se 1 (by rfl) ⟨4596425, by rfl⟩ : syracuseStep 6128567 = 9192851) B9192851
theorem B2294983 : Blo 634301 2294983 := bstep (se 1 (by rfl) ⟨1721237, by rfl⟩ : syracuseStep 2294983 = 3442475) B3442475
theorem B951515 : Blo 634301 951515 := bstep (se 1 (by rfl) ⟨713636, by rfl⟩ : syracuseStep 951515 = 1427273) B1427273
theorem B951689 : Blo 634301 951689 := bstep (se 2 (by rfl) ⟨356883, by rfl⟩ : syracuseStep 951689 = 713767) B713767
theorem B1607111 : Blo 634301 1607111 := bstep (se 1 (by rfl) ⟨1205333, by rfl⟩ : syracuseStep 1607111 = 2410667) B2410667
theorem B1607161 : Blo 634301 1607161 := bstep (se 2 (by rfl) ⟨602685, by rfl⟩ : syracuseStep 1607161 = 1205371) B1205371
theorem B3671687 : Blo 634301 3671687 := bstep (se 1 (by rfl) ⟨2753765, by rfl⟩ : syracuseStep 3671687 = 5507531) B5507531
theorem B952043 : Blo 634301 952043 := bstep (se 1 (by rfl) ⟨714032, by rfl⟩ : syracuseStep 952043 = 1428065) B1428065
theorem B1607465 : Blo 634301 1607465 := bstep (se 2 (by rfl) ⟨602799, by rfl⟩ : syracuseStep 1607465 = 1205599) B1205599
theorem B952271 : Blo 634301 952271 := bstep (se 1 (by rfl) ⟨714203, by rfl⟩ : syracuseStep 952271 = 1428407) B1428407
theorem B1607809 : Blo 634301 1607809 := bstep (se 2 (by rfl) ⟨602928, by rfl⟩ : syracuseStep 1607809 = 1205857) B1205857
theorem B3213593 : Blo 634301 3213593 := bstep (se 2 (by rfl) ⟨1205097, by rfl⟩ : syracuseStep 3213593 = 2410195) B2410195
theorem B4065565 : Blo 634301 4065565 := bstep (se 3 (by rfl) ⟨762293, by rfl⟩ : syracuseStep 4065565 = 1524587) B1524587
theorem B952667 : Blo 634301 952667 := bstep (se 1 (by rfl) ⟨714500, by rfl⟩ : syracuseStep 952667 = 1429001) B1429001
theorem B952895 : Blo 634301 952895 := bstep (se 1 (by rfl) ⟨714671, by rfl⟩ : syracuseStep 952895 = 1429343) B1429343
theorem B953015 : Blo 634301 953015 := bstep (se 1 (by rfl) ⟨714761, by rfl⟩ : syracuseStep 953015 = 1429523) B1429523
theorem B6884129 : Blo 634301 6884129 := bstep (se 2 (by rfl) ⟨2581548, by rfl⟩ : syracuseStep 6884129 = 5163097) B5163097
theorem B2722679 : Blo 634301 2722679 := bstep (se 1 (by rfl) ⟨2042009, by rfl⟩ : syracuseStep 2722679 = 4084019) B4084019
theorem B953243 : Blo 634301 953243 := bstep (se 1 (by rfl) ⟨714932, by rfl⟩ : syracuseStep 953243 = 1429865) B1429865
theorem B1608619 : Blo 634301 1608619 := bstep (se 1 (by rfl) ⟨1206464, by rfl⟩ : syracuseStep 1608619 = 2412929) B2412929
theorem B2722747 : Blo 634301 2722747 := bstep (se 1 (by rfl) ⟨2042060, by rfl⟩ : syracuseStep 2722747 = 4084121) B4084121
theorem B7244801 : Blo 634301 7244801 := bstep (se 2 (by rfl) ⟨2716800, by rfl⟩ : syracuseStep 7244801 = 5433601) B5433601
theorem B1608923 : Blo 634301 1608923 := bstep (se 1 (by rfl) ⟨1206692, by rfl⟩ : syracuseStep 1608923 = 2413385) B2413385
theorem B953639 : Blo 634301 953639 := bstep (se 1 (by rfl) ⟨715229, by rfl⟩ : syracuseStep 953639 = 1430459) B1430459
theorem B9178429 : Blo 634301 9178429 := bstep (se 3 (by rfl) ⟨1720955, by rfl⟩ : syracuseStep 9178429 = 3441911) B3441911
theorem B1609055 : Blo 634301 1609055 := bstep (se 1 (by rfl) ⟨1206791, by rfl⟩ : syracuseStep 1609055 = 2413583) B2413583
theorem B953723 : Blo 634301 953723 := bstep (se 1 (by rfl) ⟨715292, by rfl⟩ : syracuseStep 953723 = 1430585) B1430585
theorem B953849 : Blo 634301 953849 := bstep (se 2 (by rfl) ⟨357693, by rfl⟩ : syracuseStep 953849 = 715387) B715387
theorem B953951 : Blo 634301 953951 := bstep (se 1 (by rfl) ⟨715463, by rfl⟩ : syracuseStep 953951 = 1430927) B1430927
theorem B5443307 : Blo 634301 5443307 := bstep (se 1 (by rfl) ⟨4082480, by rfl⟩ : syracuseStep 5443307 = 8164961) B8164961
theorem B954167 : Blo 634301 954167 := bstep (se 1 (by rfl) ⟨715625, by rfl⟩ : syracuseStep 954167 = 1431251) B1431251
theorem B1609753 : Blo 634301 1609753 := bstep (se 2 (by rfl) ⟨603657, by rfl⟩ : syracuseStep 1609753 = 1207315) B1207315
theorem B954473 : Blo 634301 954473 := bstep (se 2 (by rfl) ⟨357927, by rfl⟩ : syracuseStep 954473 = 715855) B715855
theorem B11604131 : Blo 634301 11604131 := bstep (se 1 (by rfl) ⟨8703098, by rfl⟩ : syracuseStep 11604131 = 17406197) B17406197
theorem B6885647 : Blo 634301 6885647 := bstep (se 1 (by rfl) ⟨5164235, by rfl⟩ : syracuseStep 6885647 = 10328471) B10328471
theorem B1610057 : Blo 634301 1610057 := bstep (se 2 (by rfl) ⟨603771, by rfl⟩ : syracuseStep 1610057 = 1207543) B1207543
theorem B14094691 : Blo 634301 14094691 := bstep (se 1 (by rfl) ⟨10571018, by rfl⟩ : syracuseStep 14094691 = 21142037) B21142037
theorem B954791 : Blo 634301 954791 := bstep (se 1 (by rfl) ⟨716093, by rfl⟩ : syracuseStep 954791 = 1432187) B1432187
theorem B2298287 : Blo 634301 2298287 := bstep (se 1 (by rfl) ⟨1723715, by rfl⟩ : syracuseStep 2298287 = 3447431) B3447431
theorem B954875 : Blo 634301 954875 := bstep (se 1 (by rfl) ⟨716156, by rfl⟩ : syracuseStep 954875 = 1432313) B1432313
theorem B955001 : Blo 634301 955001 := bstep (se 2 (by rfl) ⟨358125, by rfl⟩ : syracuseStep 955001 = 716251) B716251
theorem B955055 : Blo 634301 955055 := bstep (se 1 (by rfl) ⟨716291, by rfl⟩ : syracuseStep 955055 = 1432583) B1432583
theorem B955103 : Blo 634301 955103 := bstep (se 1 (by rfl) ⟨716327, by rfl⟩ : syracuseStep 955103 = 1432655) B1432655
theorem B3871567 : Blo 634301 3871567 := bstep (se 1 (by rfl) ⟨2903675, by rfl⟩ : syracuseStep 3871567 = 5807351) B5807351
theorem B3216347 : Blo 634301 3216347 := bstep (se 1 (by rfl) ⟨2412260, by rfl⟩ : syracuseStep 3216347 = 4824521) B4824521
theorem B955367 : Blo 634301 955367 := bstep (se 1 (by rfl) ⟨716525, by rfl⟩ : syracuseStep 955367 = 1433051) B1433051
theorem B6132793 : Blo 634301 6132793 := bstep (se 2 (by rfl) ⟨2299797, by rfl⟩ : syracuseStep 6132793 = 4599595) B4599595
theorem B3216509 : Blo 634301 3216509 := bstep (se 3 (by rfl) ⟨603095, by rfl⟩ : syracuseStep 3216509 = 1206191) B1206191
theorem B955625 : Blo 634301 955625 := bstep (se 2 (by rfl) ⟨358359, by rfl⟩ : syracuseStep 955625 = 716719) B716719
theorem B955679 : Blo 634301 955679 := bstep (se 1 (by rfl) ⟨716759, by rfl⟩ : syracuseStep 955679 = 1433519) B1433519
theorem B1021223 : Blo 634301 1021223 := bstep (se 1 (by rfl) ⟨765917, by rfl⟩ : syracuseStep 1021223 = 1531835) B1531835
theorem B3216833 : Blo 634301 3216833 := bstep (se 2 (by rfl) ⟨1206312, by rfl⟩ : syracuseStep 3216833 = 2412625) B2412625
theorem B955847 : Blo 634301 955847 := bstep (se 1 (by rfl) ⟨716885, by rfl⟩ : syracuseStep 955847 = 1433771) B1433771
theorem B3053213 : Blo 634301 3053213 := bstep (se 3 (by rfl) ⟨572477, by rfl⟩ : syracuseStep 3053213 = 1144955) B1144955
theorem B956201 : Blo 634301 956201 := bstep (se 2 (by rfl) ⟨358575, by rfl⟩ : syracuseStep 956201 = 717151) B717151
theorem B956207 : Blo 634301 956207 := bstep (se 1 (by rfl) ⟨717155, by rfl⟩ : syracuseStep 956207 = 1434311) B1434311
theorem B1808183 : Blo 634301 1808183 := bstep (se 1 (by rfl) ⟨1356137, by rfl⟩ : syracuseStep 1808183 = 2712275) B2712275
theorem B1808513 : Blo 634301 1808513 := bstep (se 2 (by rfl) ⟨678192, by rfl⟩ : syracuseStep 1808513 = 1356385) B1356385
theorem B956681 : Blo 634301 956681 := bstep (se 2 (by rfl) ⟨358755, by rfl⟩ : syracuseStep 956681 = 717511) B717511
theorem B956783 : Blo 634301 956783 := bstep (se 1 (by rfl) ⟨717587, by rfl⟩ : syracuseStep 956783 = 1435175) B1435175
theorem B956999 : Blo 634301 956999 := bstep (se 1 (by rfl) ⟨717749, by rfl⟩ : syracuseStep 956999 = 1435499) B1435499
theorem B957035 : Blo 634301 957035 := bstep (se 1 (by rfl) ⟨717776, by rfl⟩ : syracuseStep 957035 = 1435553) B1435553
theorem B957263 : Blo 634301 957263 := bstep (se 1 (by rfl) ⟨717947, by rfl⟩ : syracuseStep 957263 = 1435895) B1435895
theorem B4135799 : Blo 634301 4135799 := bstep (se 1 (by rfl) ⟨3101849, by rfl⟩ : syracuseStep 4135799 = 6203699) B6203699
theorem B1612943 : Blo 634301 1612943 := bstep (se 1 (by rfl) ⟨1209707, by rfl⟩ : syracuseStep 1612943 = 2419415) B2419415
theorem B1940699 : Blo 634301 1940699 := bstep (se 1 (by rfl) ⟨1455524, by rfl⟩ : syracuseStep 1940699 = 2911049) B2911049
theorem B6528761 : Blo 634301 6528761 := bstep (se 2 (by rfl) ⟨2448285, by rfl⟩ : syracuseStep 6528761 = 4896571) B4896571
theorem B4825007 : Blo 634301 4825007 := bstep (se 1 (by rfl) ⟨3618755, by rfl⟩ : syracuseStep 4825007 = 7237511) B7237511
theorem B1679791 : Blo 634301 1679791 := bstep (se 1 (by rfl) ⟨1259843, by rfl⟩ : syracuseStep 1679791 = 2519687) B2519687
theorem B3449395 : Blo 634301 3449395 := bstep (se 1 (by rfl) ⟨2587046, by rfl⟩ : syracuseStep 3449395 = 5174093) B5174093
theorem B2204617 : Blo 634301 2204617 := bstep (se 2 (by rfl) ⟨826731, by rfl⟩ : syracuseStep 2204617 = 1653463) B1653463
theorem B5448707 : Blo 634301 5448707 := bstep (se 1 (by rfl) ⟨4086530, by rfl⟩ : syracuseStep 5448707 = 8173061) B8173061
theorem B1614887 : Blo 634301 1614887 := bstep (se 1 (by rfl) ⟨1211165, by rfl⟩ : syracuseStep 1614887 = 2422331) B2422331
theorem B1615241 : Blo 634301 1615241 := bstep (se 2 (by rfl) ⟨605715, by rfl⟩ : syracuseStep 1615241 = 1211431) B1211431
theorem B6956441 : Blo 634301 6956441 := bstep (se 2 (by rfl) ⟨2608665, by rfl⟩ : syracuseStep 6956441 = 5217331) B5217331
theorem B861689 : Blo 634301 861689 := bstep (se 2 (by rfl) ⟨323133, by rfl⟩ : syracuseStep 861689 = 646267) B646267
theorem B5514809 : Blo 634301 5514809 := bstep (se 2 (by rfl) ⟨2068053, by rfl⟩ : syracuseStep 5514809 = 4136107) B4136107
theorem B10233479 : Blo 634301 10233479 := bstep (se 1 (by rfl) ⟨7675109, by rfl⟩ : syracuseStep 10233479 = 15350219) B15350219
theorem B1812431 : Blo 634301 1812431 := bstep (se 1 (by rfl) ⟨1359323, by rfl⟩ : syracuseStep 1812431 = 2718647) B2718647
theorem B9316529 : Blo 634301 9316529 := bstep (se 2 (by rfl) ⟨3493698, by rfl⟩ : syracuseStep 9316529 = 6987397) B6987397
theorem B2763017 : Blo 634301 2763017 := bstep (se 2 (by rfl) ⟨1036131, by rfl⟩ : syracuseStep 2763017 = 2072263) B2072263
theorem B4073971 : Blo 634301 4073971 := bstep (se 1 (by rfl) ⟨3055478, by rfl⟩ : syracuseStep 4073971 = 6110957) B6110957
theorem B1714859 : Blo 634301 1714859 := bstep (se 1 (by rfl) ⟨1286144, by rfl⟩ : syracuseStep 1714859 = 2572289) B2572289
theorem B2042779 : Blo 634301 2042779 := bstep (se 1 (by rfl) ⟨1532084, by rfl⟩ : syracuseStep 2042779 = 3064169) B3064169
theorem B2141099 : Blo 634301 2141099 := bstep (se 1 (by rfl) ⟨1605824, by rfl⟩ : syracuseStep 2141099 = 3211649) B3211649
theorem B5975005 : Blo 634301 5975005 := bstep (se 3 (by rfl) ⟨1120313, by rfl⟩ : syracuseStep 5975005 = 2240627) B2240627
theorem B2141639 : Blo 634301 2141639 := bstep (se 1 (by rfl) ⟨1606229, by rfl⟩ : syracuseStep 2141639 = 3212459) B3212459
theorem B1715671 : Blo 634301 1715671 := bstep (se 1 (by rfl) ⟨1286753, by rfl⟩ : syracuseStep 1715671 = 2573507) B2573507
theorem B634363 : Blo 634301 634363 := bstep (se 1 (by rfl) ⟨475772, by rfl⟩ : syracuseStep 634363 = 951545) B951545
theorem B634431 : Blo 634301 634431 := bstep (se 1 (by rfl) ⟨475823, by rfl⟩ : syracuseStep 634431 = 951647) B951647
theorem B634439 : Blo 634301 634439 := bstep (se 1 (by rfl) ⟨475829, by rfl⟩ : syracuseStep 634439 = 951659) B951659
theorem B1552033 : Blo 634301 1552033 := bstep (se 2 (by rfl) ⟨582012, by rfl⟩ : syracuseStep 1552033 = 1164025) B1164025
theorem B634591 : Blo 634301 634591 := bstep (se 1 (by rfl) ⟨475943, by rfl⟩ : syracuseStep 634591 = 951887) B951887
theorem B2141963 : Blo 634301 2141963 := bstep (se 1 (by rfl) ⟨1606472, by rfl⟩ : syracuseStep 2141963 = 3212945) B3212945
theorem B634671 : Blo 634301 634671 := bstep (se 1 (by rfl) ⟨476003, by rfl⟩ : syracuseStep 634671 = 952007) B952007
theorem B634779 : Blo 634301 634779 := bstep (se 1 (by rfl) ⟨476084, by rfl⟩ : syracuseStep 634779 = 952169) B952169
theorem B23179193 : Blo 634301 23179193 := bstep (se 2 (by rfl) ⟨8692197, by rfl⟩ : syracuseStep 23179193 = 17384395) B17384395
theorem B634831 : Blo 634301 634831 := bstep (se 1 (by rfl) ⟨476123, by rfl⟩ : syracuseStep 634831 = 952247) B952247
theorem B634855 : Blo 634301 634855 := bstep (se 1 (by rfl) ⟨476141, by rfl⟩ : syracuseStep 634855 = 952283) B952283
theorem B2142233 : Blo 634301 2142233 := bstep (se 2 (by rfl) ⟨803337, by rfl⟩ : syracuseStep 2142233 = 1606675) B1606675
theorem B635167 : Blo 634301 635167 := bstep (se 1 (by rfl) ⟨476375, by rfl⟩ : syracuseStep 635167 = 952751) B952751
theorem B635227 : Blo 634301 635227 := bstep (se 1 (by rfl) ⟨476420, by rfl⟩ : syracuseStep 635227 = 952841) B952841
theorem B635247 : Blo 634301 635247 := bstep (se 1 (by rfl) ⟨476435, by rfl⟩ : syracuseStep 635247 = 952871) B952871
theorem B635303 : Blo 634301 635303 := bstep (se 1 (by rfl) ⟨476477, by rfl⟩ : syracuseStep 635303 = 952955) B952955
theorem B635387 : Blo 634301 635387 := bstep (se 1 (by rfl) ⟨476540, by rfl⟩ : syracuseStep 635387 = 953081) B953081
theorem B635455 : Blo 634301 635455 := bstep (se 1 (by rfl) ⟨476591, by rfl⟩ : syracuseStep 635455 = 953183) B953183
theorem B635463 : Blo 634301 635463 := bstep (se 1 (by rfl) ⟨476597, by rfl⟩ : syracuseStep 635463 = 953195) B953195
theorem B635615 : Blo 634301 635615 := bstep (se 1 (by rfl) ⟨476711, by rfl⟩ : syracuseStep 635615 = 953423) B953423
theorem B635695 : Blo 634301 635695 := bstep (se 1 (by rfl) ⟨476771, by rfl⟩ : syracuseStep 635695 = 953543) B953543
theorem B635803 : Blo 634301 635803 := bstep (se 1 (by rfl) ⟨476852, by rfl⟩ : syracuseStep 635803 = 953705) B953705
theorem B635855 : Blo 634301 635855 := bstep (se 1 (by rfl) ⟨476891, by rfl⟩ : syracuseStep 635855 = 953783) B953783
theorem B635879 : Blo 634301 635879 := bstep (se 1 (by rfl) ⟨476909, by rfl⟩ : syracuseStep 635879 = 953819) B953819
theorem B4830353 : Blo 634301 4830353 := bstep (se 2 (by rfl) ⟨1811382, by rfl⟩ : syracuseStep 4830353 = 3622765) B3622765
theorem B4076689 : Blo 634301 4076689 := bstep (se 2 (by rfl) ⟨1528758, by rfl⟩ : syracuseStep 4076689 = 3057517) B3057517
theorem B2143475 : Blo 634301 2143475 := bstep (se 1 (by rfl) ⟨1607606, by rfl⟩ : syracuseStep 2143475 = 3215213) B3215213
theorem B636191 : Blo 634301 636191 := bstep (se 1 (by rfl) ⟨477143, by rfl⟩ : syracuseStep 636191 = 954287) B954287
theorem B636251 : Blo 634301 636251 := bstep (se 1 (by rfl) ⟨477188, by rfl⟩ : syracuseStep 636251 = 954377) B954377
theorem B2143583 : Blo 634301 2143583 := bstep (se 1 (by rfl) ⟨1607687, by rfl⟩ : syracuseStep 2143583 = 3215375) B3215375
theorem B636271 : Blo 634301 636271 := bstep (se 1 (by rfl) ⟨477203, by rfl⟩ : syracuseStep 636271 = 954407) B954407
theorem B1717627 : Blo 634301 1717627 := bstep (se 1 (by rfl) ⟨1288220, by rfl⟩ : syracuseStep 1717627 = 2576441) B2576441
theorem B3880331 : Blo 634301 3880331 := bstep (se 1 (by rfl) ⟨2910248, by rfl⟩ : syracuseStep 3880331 = 5820497) B5820497
theorem B3618209 : Blo 634301 3618209 := bstep (se 2 (by rfl) ⟨1356828, by rfl⟩ : syracuseStep 3618209 = 2713657) B2713657
theorem B636327 : Blo 634301 636327 := bstep (se 1 (by rfl) ⟨477245, by rfl⟩ : syracuseStep 636327 = 954491) B954491
theorem B12531145 : Blo 634301 12531145 := bstep (se 2 (by rfl) ⟨4699179, by rfl⟩ : syracuseStep 12531145 = 9398359) B9398359
theorem B41268689 : Blo 634301 41268689 := bstep (se 2 (by rfl) ⟨15475758, by rfl⟩ : syracuseStep 41268689 = 30951517) B30951517
theorem B636411 : Blo 634301 636411 := bstep (se 1 (by rfl) ⟨477308, by rfl⟩ : syracuseStep 636411 = 954617) B954617
theorem B3225095 : Blo 634301 3225095 := bstep (se 1 (by rfl) ⟨2418821, by rfl⟩ : syracuseStep 3225095 = 4837643) B4837643
theorem B2897441 : Blo 634301 2897441 := bstep (se 2 (by rfl) ⟨1086540, by rfl⟩ : syracuseStep 2897441 = 2173081) B2173081
theorem B1816121 : Blo 634301 1816121 := bstep (se 2 (by rfl) ⟨681045, by rfl⟩ : syracuseStep 1816121 = 1362091) B1362091
theorem B636479 : Blo 634301 636479 := bstep (se 1 (by rfl) ⟨477359, by rfl⟩ : syracuseStep 636479 = 954719) B954719
theorem B636487 : Blo 634301 636487 := bstep (se 1 (by rfl) ⟨477365, by rfl⟩ : syracuseStep 636487 = 954731) B954731
theorem B636639 : Blo 634301 636639 := bstep (se 1 (by rfl) ⟨477479, by rfl⟩ : syracuseStep 636639 = 954959) B954959
theorem B636719 : Blo 634301 636719 := bstep (se 1 (by rfl) ⟨477539, by rfl⟩ : syracuseStep 636719 = 955079) B955079
theorem B636827 : Blo 634301 636827 := bstep (se 1 (by rfl) ⟨477620, by rfl⟩ : syracuseStep 636827 = 955241) B955241
theorem B636879 : Blo 634301 636879 := bstep (se 1 (by rfl) ⟨477659, by rfl⟩ : syracuseStep 636879 = 955319) B955319
theorem B636903 : Blo 634301 636903 := bstep (se 1 (by rfl) ⟨477677, by rfl⟩ : syracuseStep 636903 = 955355) B955355
theorem B3225581 : Blo 634301 3225581 := bstep (se 3 (by rfl) ⟨604796, by rfl⟩ : syracuseStep 3225581 = 1209593) B1209593
theorem B4634657 : Blo 634301 4634657 := bstep (se 2 (by rfl) ⟨1737996, by rfl⟩ : syracuseStep 4634657 = 3475993) B3475993
theorem B637215 : Blo 634301 637215 := bstep (se 1 (by rfl) ⟨477911, by rfl⟩ : syracuseStep 637215 = 955823) B955823
theorem B637275 : Blo 634301 637275 := bstep (se 1 (by rfl) ⟨477956, by rfl⟩ : syracuseStep 637275 = 955913) B955913
theorem B637295 : Blo 634301 637295 := bstep (se 1 (by rfl) ⟨477971, by rfl⟩ : syracuseStep 637295 = 955943) B955943
theorem B5421437 : Blo 634301 5421437 := bstep (se 3 (by rfl) ⟨1016519, by rfl⟩ : syracuseStep 5421437 = 2033039) B2033039
theorem B637351 : Blo 634301 637351 := bstep (se 1 (by rfl) ⟨478013, by rfl⟩ : syracuseStep 637351 = 956027) B956027
theorem B3226067 : Blo 634301 3226067 := bstep (se 1 (by rfl) ⟨2419550, by rfl⟩ : syracuseStep 3226067 = 4839101) B4839101
theorem B637435 : Blo 634301 637435 := bstep (se 1 (by rfl) ⟨478076, by rfl⟩ : syracuseStep 637435 = 956153) B956153
theorem B637503 : Blo 634301 637503 := bstep (se 1 (by rfl) ⟨478127, by rfl⟩ : syracuseStep 637503 = 956255) B956255
theorem B637511 : Blo 634301 637511 := bstep (se 1 (by rfl) ⟨478133, by rfl⟩ : syracuseStep 637511 = 956267) B956267
theorem B637663 : Blo 634301 637663 := bstep (se 1 (by rfl) ⟨478247, by rfl⟩ : syracuseStep 637663 = 956495) B956495
theorem B3226391 : Blo 634301 3226391 := bstep (se 1 (by rfl) ⟨2419793, by rfl⟩ : syracuseStep 3226391 = 4839587) B4839587
theorem B637743 : Blo 634301 637743 := bstep (se 1 (by rfl) ⟨478307, by rfl⟩ : syracuseStep 637743 = 956615) B956615
theorem B2145149 : Blo 634301 2145149 := bstep (se 3 (by rfl) ⟨402215, by rfl⟩ : syracuseStep 2145149 = 804431) B804431
theorem B7355291 : Blo 634301 7355291 := bstep (se 1 (by rfl) ⟨5516468, by rfl⟩ : syracuseStep 7355291 = 11032937) B11032937
theorem B637851 : Blo 634301 637851 := bstep (se 1 (by rfl) ⟨478388, by rfl⟩ : syracuseStep 637851 = 956777) B956777
theorem B637903 : Blo 634301 637903 := bstep (se 1 (by rfl) ⟨478427, by rfl⟩ : syracuseStep 637903 = 956855) B956855
theorem B637927 : Blo 634301 637927 := bstep (se 1 (by rfl) ⟨478445, by rfl⟩ : syracuseStep 637927 = 956891) B956891
theorem B2145419 : Blo 634301 2145419 := bstep (se 1 (by rfl) ⟨1609064, by rfl⟩ : syracuseStep 2145419 = 3218129) B3218129
theorem B638239 : Blo 634301 638239 := bstep (se 1 (by rfl) ⟨478679, by rfl⟩ : syracuseStep 638239 = 957359) B957359
theorem B638299 : Blo 634301 638299 := bstep (se 1 (by rfl) ⟨478724, by rfl⟩ : syracuseStep 638299 = 957449) B957449
theorem B4832783 : Blo 634301 4832783 := bstep (se 1 (by rfl) ⟨3624587, by rfl⟩ : syracuseStep 4832783 = 7249175) B7249175
theorem B1359443 : Blo 634301 1359443 := bstep (se 1 (by rfl) ⟨1019582, by rfl⟩ : syracuseStep 1359443 = 2039165) B2039165
theorem B19579117 : Blo 634301 19579117 := bstep (se 3 (by rfl) ⟨3671084, by rfl⟩ : syracuseStep 19579117 = 7342169) B7342169
theorem B29475089 : Blo 634301 29475089 := bstep (se 2 (by rfl) ⟨11053158, by rfl⟩ : syracuseStep 29475089 = 22106317) B22106317
theorem B3228011 : Blo 634301 3228011 := bstep (se 1 (by rfl) ⟨2421008, by rfl⟩ : syracuseStep 3228011 = 4842017) B4842017
theorem B3064321 : Blo 634301 3064321 := bstep (se 2 (by rfl) ⟨1149120, by rfl⟩ : syracuseStep 3064321 = 2298241) B2298241
theorem B2147039 : Blo 634301 2147039 := bstep (se 1 (by rfl) ⟨1610279, by rfl⟩ : syracuseStep 2147039 = 3220559) B3220559
theorem B4834241 : Blo 634301 4834241 := bstep (se 2 (by rfl) ⟨1812840, by rfl⟩ : syracuseStep 4834241 = 3625681) B3625681
theorem B7324769 : Blo 634301 7324769 := bstep (se 2 (by rfl) ⟨2746788, by rfl⟩ : syracuseStep 7324769 = 5493577) B5493577
theorem B2147471 : Blo 634301 2147471 := bstep (se 1 (by rfl) ⟨1610603, by rfl⟩ : syracuseStep 2147471 = 3221207) B3221207
theorem B3261791 : Blo 634301 3261791 := bstep (se 1 (by rfl) ⟨2446343, by rfl⟩ : syracuseStep 3261791 = 4892687) B4892687
theorem B24823331 : Blo 634301 24823331 := bstep (se 1 (by rfl) ⟨18617498, by rfl⟩ : syracuseStep 24823331 = 37234997) B37234997
theorem B3229469 : Blo 634301 3229469 := bstep (se 3 (by rfl) ⟨605525, by rfl⟩ : syracuseStep 3229469 = 1211051) B1211051
theorem B1427255 : Blo 634301 1427255 := bstep (se 1 (by rfl) ⟨1070441, by rfl⟩ : syracuseStep 1427255 = 2140883) B2140883
theorem B6211565 : Blo 634301 6211565 := bstep (se 3 (by rfl) ⟨1164668, by rfl⟩ : syracuseStep 6211565 = 2329337) B2329337
theorem B1427561 : Blo 634301 1427561 := bstep (se 2 (by rfl) ⟨535335, by rfl⟩ : syracuseStep 1427561 = 1070671) B1070671
theorem B9193601 : Blo 634301 9193601 := bstep (se 2 (by rfl) ⟨3447600, by rfl⟩ : syracuseStep 9193601 = 6895201) B6895201
theorem B2410681 : Blo 634301 2410681 := bstep (se 2 (by rfl) ⟨904005, by rfl⟩ : syracuseStep 2410681 = 1808011) B1808011
theorem B2148605 : Blo 634301 2148605 := bstep (se 3 (by rfl) ⟨402863, by rfl⟩ : syracuseStep 2148605 = 805727) B805727
theorem B805231 : Blo 634301 805231 := bstep (se 1 (by rfl) ⟨603923, by rfl⟩ : syracuseStep 805231 = 1207847) B1207847
theorem B1428047 : Blo 634301 1428047 := bstep (se 1 (by rfl) ⟨1071035, by rfl⟩ : syracuseStep 1428047 = 2142071) B2142071
theorem B1428191 : Blo 634301 1428191 := bstep (se 1 (by rfl) ⟨1071143, by rfl⟩ : syracuseStep 1428191 = 2142287) B2142287
theorem B2608043 : Blo 634301 2608043 := bstep (se 1 (by rfl) ⟨1956032, by rfl⟩ : syracuseStep 2608043 = 3912065) B3912065
theorem B1428443 : Blo 634301 1428443 := bstep (se 1 (by rfl) ⟨1071332, by rfl⟩ : syracuseStep 1428443 = 2142665) B2142665
theorem B6114305 : Blo 634301 6114305 := bstep (se 2 (by rfl) ⟨2292864, by rfl⟩ : syracuseStep 6114305 = 4585729) B4585729
theorem B2149415 : Blo 634301 2149415 := bstep (se 1 (by rfl) ⟨1612061, by rfl⟩ : syracuseStep 2149415 = 3224123) B3224123
theorem B1428623 : Blo 634301 1428623 := bstep (se 1 (by rfl) ⟨1071467, by rfl⟩ : syracuseStep 1428623 = 2142935) B2142935
theorem B806107 : Blo 634301 806107 := bstep (se 1 (by rfl) ⟨604580, by rfl⟩ : syracuseStep 806107 = 1209161) B1209161
theorem B1428713 : Blo 634301 1428713 := bstep (se 2 (by rfl) ⟨535767, by rfl⟩ : syracuseStep 1428713 = 1071535) B1071535
theorem B1428767 : Blo 634301 1428767 := bstep (se 1 (by rfl) ⟨1071575, by rfl⟩ : syracuseStep 1428767 = 2143151) B2143151
theorem B3624223 : Blo 634301 3624223 := bstep (se 1 (by rfl) ⟨2718167, by rfl⟩ : syracuseStep 3624223 = 5436335) B5436335
theorem B2149847 : Blo 634301 2149847 := bstep (se 1 (by rfl) ⟨1612385, by rfl⟩ : syracuseStep 2149847 = 3224771) B3224771
theorem B1429289 : Blo 634301 1429289 := bstep (se 2 (by rfl) ⟨535983, by rfl⟩ : syracuseStep 1429289 = 1071967) B1071967
theorem B1527817 : Blo 634301 1527817 := bstep (se 2 (by rfl) ⟨572931, by rfl⟩ : syracuseStep 1527817 = 1145863) B1145863
theorem B11030987 : Blo 634301 11030987 := bstep (se 1 (by rfl) ⟨8273240, by rfl⟩ : syracuseStep 11030987 = 16546481) B16546481
theorem B807727 : Blo 634301 807727 := bstep (se 1 (by rfl) ⟨605795, by rfl⟩ : syracuseStep 807727 = 1211591) B1211591
theorem B1430351 : Blo 634301 1430351 := bstep (se 1 (by rfl) ⟨1072763, by rfl⟩ : syracuseStep 1430351 = 2145527) B2145527
theorem B1430567 : Blo 634301 1430567 := bstep (se 1 (by rfl) ⟨1072925, by rfl⟩ : syracuseStep 1430567 = 2145851) B2145851
theorem B2151521 : Blo 634301 2151521 := bstep (se 2 (by rfl) ⟨806820, by rfl⟩ : syracuseStep 2151521 = 1613641) B1613641
theorem B1529047 : Blo 634301 1529047 := bstep (se 1 (by rfl) ⟨1146785, by rfl⟩ : syracuseStep 1529047 = 2293571) B2293571
theorem B4838615 : Blo 634301 4838615 := bstep (se 1 (by rfl) ⟨3628961, by rfl⟩ : syracuseStep 4838615 = 7257923) B7257923
theorem B1430747 : Blo 634301 1430747 := bstep (se 1 (by rfl) ⟨1073060, by rfl⟩ : syracuseStep 1430747 = 2146121) B2146121
theorem B1627489 : Blo 634301 1627489 := bstep (se 2 (by rfl) ⟨610308, by rfl⟩ : syracuseStep 1627489 = 1220617) B1220617
theorem B1430945 : Blo 634301 1430945 := bstep (se 2 (by rfl) ⟨536604, by rfl⟩ : syracuseStep 1430945 = 1073209) B1073209
theorem B1070779 : Blo 634301 1070779 := bstep (se 1 (by rfl) ⟨803084, by rfl⟩ : syracuseStep 1070779 = 1606169) B1606169
theorem B1431503 : Blo 634301 1431503 := bstep (se 1 (by rfl) ⟨1073627, by rfl⟩ : syracuseStep 1431503 = 2147255) B2147255
theorem B2414873 : Blo 634301 2414873 := bstep (se 2 (by rfl) ⟨905577, by rfl⟩ : syracuseStep 2414873 = 1811155) B1811155
theorem B678175 : Blo 634301 678175 := bstep (se 1 (by rfl) ⟨508631, by rfl⟩ : syracuseStep 678175 = 1017263) B1017263
theorem B1431881 : Blo 634301 1431881 := bstep (se 2 (by rfl) ⟨536955, by rfl⟩ : syracuseStep 1431881 = 1073911) B1073911
theorem B1431899 : Blo 634301 1431899 := bstep (se 1 (by rfl) ⟨1073924, by rfl⟩ : syracuseStep 1431899 = 2147849) B2147849
theorem B2152871 : Blo 634301 2152871 := bstep (se 1 (by rfl) ⟨1614653, by rfl⟩ : syracuseStep 2152871 = 3229307) B3229307
theorem B1530431 : Blo 634301 1530431 := bstep (se 1 (by rfl) ⟨1147823, by rfl⟩ : syracuseStep 1530431 = 2295647) B2295647
theorem B1628743 : Blo 634301 1628743 := bstep (se 1 (by rfl) ⟨1221557, by rfl⟩ : syracuseStep 1628743 = 2443115) B2443115
theorem B2153033 : Blo 634301 2153033 := bstep (se 2 (by rfl) ⟨807387, by rfl⟩ : syracuseStep 2153033 = 1614775) B1614775
theorem B20601539 : Blo 634301 20601539 := bstep (se 1 (by rfl) ⟨15451154, by rfl⟩ : syracuseStep 20601539 = 30902309) B30902309
theorem B1071839 : Blo 634301 1071839 := bstep (se 1 (by rfl) ⟨803879, by rfl⟩ : syracuseStep 1071839 = 1607759) B1607759
theorem B4578029 : Blo 634301 4578029 := bstep (se 3 (by rfl) ⟨858380, by rfl⟩ : syracuseStep 4578029 = 1716761) B1716761
theorem B12245903 : Blo 634301 12245903 := bstep (se 1 (by rfl) ⟨9184427, by rfl⟩ : syracuseStep 12245903 = 18368855) B18368855
theorem B1432475 : Blo 634301 1432475 := bstep (se 1 (by rfl) ⟨1074356, by rfl⟩ : syracuseStep 1432475 = 2148713) B2148713
theorem B4086683 : Blo 634301 4086683 := bstep (se 1 (by rfl) ⟨3065012, by rfl⟩ : syracuseStep 4086683 = 6130025) B6130025
theorem B5495795 : Blo 634301 5495795 := bstep (se 1 (by rfl) ⟨4121846, by rfl⟩ : syracuseStep 5495795 = 8243693) B8243693
theorem B44194895 : Blo 634301 44194895 := bstep (se 1 (by rfl) ⟨33146171, by rfl⟩ : syracuseStep 44194895 = 66292343) B66292343
theorem B1432673 : Blo 634301 1432673 := bstep (se 2 (by rfl) ⟨537252, by rfl⟩ : syracuseStep 1432673 = 1074505) B1074505
theorem B1072271 : Blo 634301 1072271 := bstep (se 1 (by rfl) ⟨804203, by rfl⟩ : syracuseStep 1072271 = 1608407) B1608407
theorem B1432871 : Blo 634301 1432871 := bstep (se 1 (by rfl) ⟨1074653, by rfl⟩ : syracuseStep 1432871 = 2149307) B2149307
theorem B11754827 : Blo 634301 11754827 := bstep (se 1 (by rfl) ⟨8816120, by rfl⟩ : syracuseStep 11754827 = 17632241) B17632241
theorem B1072507 : Blo 634301 1072507 := bstep (se 1 (by rfl) ⟨804380, by rfl⟩ : syracuseStep 1072507 = 1608761) B1608761
theorem B3431879 : Blo 634301 3431879 := bstep (se 1 (by rfl) ⟨2573909, by rfl⟩ : syracuseStep 3431879 = 5147819) B5147819
theorem B1433249 : Blo 634301 1433249 := bstep (se 2 (by rfl) ⟨537468, by rfl⟩ : syracuseStep 1433249 = 1074937) B1074937
theorem B2416513 : Blo 634301 2416513 := bstep (se 2 (by rfl) ⟨906192, by rfl⟩ : syracuseStep 2416513 = 1812385) B1812385
theorem B1433609 : Blo 634301 1433609 := bstep (se 2 (by rfl) ⟨537603, by rfl⟩ : syracuseStep 1433609 = 1075207) B1075207
theorem B1434023 : Blo 634301 1434023 := bstep (se 1 (by rfl) ⟨1075517, by rfl⟩ : syracuseStep 1434023 = 2151035) B2151035
theorem B3138011 : Blo 634301 3138011 := bstep (se 1 (by rfl) ⟨2353508, by rfl⟩ : syracuseStep 3138011 = 4707017) B4707017
theorem B6382091 : Blo 634301 6382091 := bstep (se 1 (by rfl) ⟨4786568, by rfl⟩ : syracuseStep 6382091 = 9573137) B9573137
theorem B1434131 : Blo 634301 1434131 := bstep (se 1 (by rfl) ⟨1075598, by rfl⟩ : syracuseStep 1434131 = 2151197) B2151197
theorem B1434185 : Blo 634301 1434185 := bstep (se 2 (by rfl) ⟨537819, by rfl⟩ : syracuseStep 1434185 = 1075639) B1075639
theorem B2417273 : Blo 634301 2417273 := bstep (se 2 (by rfl) ⟨906477, by rfl⟩ : syracuseStep 2417273 = 1812955) B1812955
theorem B1073999 : Blo 634301 1073999 := bstep (se 1 (by rfl) ⟨805499, by rfl⟩ : syracuseStep 1073999 = 1610999) B1610999
theorem B1532891 : Blo 634301 1532891 := bstep (se 1 (by rfl) ⟨1149668, by rfl⟩ : syracuseStep 1532891 = 2299337) B2299337
theorem B3630055 : Blo 634301 3630055 := bstep (se 1 (by rfl) ⟨2722541, by rfl⟩ : syracuseStep 3630055 = 5445083) B5445083
theorem B1434599 : Blo 634301 1434599 := bstep (se 1 (by rfl) ⟨1075949, by rfl⟩ : syracuseStep 1434599 = 2151899) B2151899
theorem B4842503 : Blo 634301 4842503 := bstep (se 1 (by rfl) ⟨3631877, by rfl⟩ : syracuseStep 4842503 = 7263755) B7263755
theorem B2417789 : Blo 634301 2417789 := bstep (se 3 (by rfl) ⟨453335, by rfl⟩ : syracuseStep 2417789 = 906671) B906671
theorem B713947 : Blo 634301 713947 := bstep (se 1 (by rfl) ⟨535460, by rfl⟩ : syracuseStep 713947 = 1070921) B1070921
theorem B681247 : Blo 634301 681247 := bstep (se 1 (by rfl) ⟨510935, by rfl⟩ : syracuseStep 681247 = 1021871) B1021871
theorem B4580657 : Blo 634301 4580657 := bstep (se 2 (by rfl) ⟨1717746, by rfl⟩ : syracuseStep 4580657 = 3435493) B3435493
theorem B1434977 : Blo 634301 1434977 := bstep (se 2 (by rfl) ⟨538116, by rfl⟩ : syracuseStep 1434977 = 1076233) B1076233
theorem B3302765 : Blo 634301 3302765 := bstep (se 3 (by rfl) ⟨619268, by rfl⟩ : syracuseStep 3302765 = 1238537) B1238537
theorem B1435067 : Blo 634301 1435067 := bstep (se 1 (by rfl) ⟨1076300, by rfl⟩ : syracuseStep 1435067 = 2152601) B2152601
theorem B714235 : Blo 634301 714235 := bstep (se 1 (by rfl) ⟨535676, by rfl⟩ : syracuseStep 714235 = 1071353) B1071353
theorem B1435193 : Blo 634301 1435193 := bstep (se 2 (by rfl) ⟨538197, by rfl⟩ : syracuseStep 1435193 = 1076395) B1076395
theorem B1533497 : Blo 634301 1533497 := bstep (se 2 (by rfl) ⟨575061, by rfl⟩ : syracuseStep 1533497 = 1150123) B1150123
theorem B714415 : Blo 634301 714415 := bstep (se 1 (by rfl) ⟨535811, by rfl⟩ : syracuseStep 714415 = 1071623) B1071623
theorem B13723357 : Blo 634301 13723357 := bstep (se 3 (by rfl) ⟨2573129, by rfl⟩ : syracuseStep 13723357 = 5146259) B5146259
theorem B7268129 : Blo 634301 7268129 := bstep (se 2 (by rfl) ⟨2725548, by rfl⟩ : syracuseStep 7268129 = 5451097) B5451097
theorem B1074991 : Blo 634301 1074991 := bstep (se 1 (by rfl) ⟨806243, by rfl⟩ : syracuseStep 1074991 = 1612487) B1612487
theorem B714703 : Blo 634301 714703 := bstep (se 1 (by rfl) ⟨536027, by rfl⟩ : syracuseStep 714703 = 1072055) B1072055
theorem B1435859 : Blo 634301 1435859 := bstep (se 1 (by rfl) ⟨1076894, by rfl⟩ : syracuseStep 1435859 = 2153789) B2153789
theorem B1435913 : Blo 634301 1435913 := bstep (se 2 (by rfl) ⟨538467, by rfl⟩ : syracuseStep 1435913 = 1076935) B1076935
theorem B715099 : Blo 634301 715099 := bstep (se 1 (by rfl) ⟨536324, by rfl⟩ : syracuseStep 715099 = 1072649) B1072649
theorem B2713999 : Blo 634301 2713999 := bstep (se 1 (by rfl) ⟨2035499, by rfl⟩ : syracuseStep 2713999 = 4070999) B4070999
theorem B715207 : Blo 634301 715207 := bstep (se 1 (by rfl) ⟨536405, by rfl⟩ : syracuseStep 715207 = 1072811) B1072811
theorem B1436129 : Blo 634301 1436129 := bstep (se 2 (by rfl) ⟨538548, by rfl⟩ : syracuseStep 1436129 = 1077097) B1077097
theorem B715567 : Blo 634301 715567 := bstep (se 1 (by rfl) ⟨536675, by rfl⟩ : syracuseStep 715567 = 1073351) B1073351
theorem B715675 : Blo 634301 715675 := bstep (se 1 (by rfl) ⟨536756, by rfl⟩ : syracuseStep 715675 = 1073513) B1073513
theorem B2419901 : Blo 634301 2419901 := bstep (se 3 (by rfl) ⟨453731, by rfl⟩ : syracuseStep 2419901 = 907463) B907463
theorem B716071 : Blo 634301 716071 := bstep (se 1 (by rfl) ⟨537053, by rfl⟩ : syracuseStep 716071 = 1074107) B1074107
theorem B1207649 : Blo 634301 1207649 := bstep (se 2 (by rfl) ⟨452868, by rfl⟩ : syracuseStep 1207649 = 905737) B905737
theorem B716143 : Blo 634301 716143 := bstep (se 1 (by rfl) ⟨537107, by rfl⟩ : syracuseStep 716143 = 1074215) B1074215
theorem B1207801 : Blo 634301 1207801 := bstep (se 2 (by rfl) ⟨452925, by rfl⟩ : syracuseStep 1207801 = 905851) B905851
theorem B716359 : Blo 634301 716359 := bstep (se 1 (by rfl) ⟨537269, by rfl⟩ : syracuseStep 716359 = 1074539) B1074539
theorem B3862225 : Blo 634301 3862225 := bstep (se 2 (by rfl) ⟨1448334, by rfl⟩ : syracuseStep 3862225 = 2896669) B2896669
theorem B1208105 : Blo 634301 1208105 := bstep (se 2 (by rfl) ⟨453039, by rfl⟩ : syracuseStep 1208105 = 906079) B906079
theorem B2715707 : Blo 634301 2715707 := bstep (se 1 (by rfl) ⟨2036780, by rfl⟩ : syracuseStep 2715707 = 4073561) B4073561
theorem B23588981 : Blo 634301 23588981 := bstep (se 5 (by rfl) ⟨1105733, by rfl⟩ : syracuseStep 23588981 = 2211467) B2211467
theorem B717223 : Blo 634301 717223 := bstep (se 1 (by rfl) ⟨537917, by rfl⟩ : syracuseStep 717223 = 1075835) B1075835
theorem B6615751 : Blo 634301 6615751 := bstep (se 1 (by rfl) ⟨4961813, by rfl⟩ : syracuseStep 6615751 = 9923627) B9923627
theorem B2716375 : Blo 634301 2716375 := bstep (se 1 (by rfl) ⟨2037281, by rfl⟩ : syracuseStep 2716375 = 4074563) B4074563
theorem B1143571 : Blo 634301 1143571 := bstep (se 1 (by rfl) ⟨857678, by rfl⟩ : syracuseStep 1143571 = 1715357) B1715357
theorem B1209107 : Blo 634301 1209107 := bstep (se 1 (by rfl) ⟨906830, by rfl⟩ : syracuseStep 1209107 = 1813661) B1813661
theorem B1209259 : Blo 634301 1209259 := bstep (se 1 (by rfl) ⟨906944, by rfl⟩ : syracuseStep 1209259 = 1813889) B1813889
theorem B717799 : Blo 634301 717799 := bstep (se 1 (by rfl) ⟨538349, by rfl⟩ : syracuseStep 717799 = 1076699) B1076699
theorem B1209487 : Blo 634301 1209487 := bstep (se 1 (by rfl) ⟨907115, by rfl⟩ : syracuseStep 1209487 = 1814231) B1814231
theorem B1209563 : Blo 634301 1209563 := bstep (se 1 (by rfl) ⟨907172, by rfl⟩ : syracuseStep 1209563 = 1814345) B1814345
theorem B41186677 : Blo 634301 41186677 := bstep (se 5 (by rfl) ⟨1930625, by rfl⟩ : syracuseStep 41186677 = 3861251) B3861251
theorem B7730635 : Blo 634301 7730635 := bstep (se 1 (by rfl) ⟨5797976, by rfl⟩ : syracuseStep 7730635 = 11595953) B11595953
theorem B3274273 : Blo 634301 3274273 := bstep (se 2 (by rfl) ⟨1227852, by rfl⟩ : syracuseStep 3274273 = 2455705) B2455705
theorem B2619191 : Blo 634301 2619191 := bstep (se 1 (by rfl) ⟨1964393, by rfl⟩ : syracuseStep 2619191 = 3928787) B3928787
theorem B1832911 : Blo 634301 1832911 := bstep (se 1 (by rfl) ⟨1374683, by rfl⟩ : syracuseStep 1832911 = 2749367) B2749367
theorem B3438625 : Blo 634301 3438625 := bstep (se 2 (by rfl) ⟨1289484, by rfl⟩ : syracuseStep 3438625 = 2578969) B2578969
theorem B2422817 : Blo 634301 2422817 := bstep (se 2 (by rfl) ⟨908556, by rfl⟩ : syracuseStep 2422817 = 1817113) B1817113
theorem B7076119 : Blo 634301 7076119 := bstep (se 1 (by rfl) ⟨5307089, by rfl⟩ : syracuseStep 7076119 = 10614179) B10614179
theorem B5437975 : Blo 634301 5437975 := bstep (se 1 (by rfl) ⟨4078481, by rfl⟩ : syracuseStep 5437975 = 8156963) B8156963
theorem B7731845 : Blo 634301 7731845 := bstep (se 4 (by rfl) ⟨724860, by rfl⟩ : syracuseStep 7731845 = 1449721) B1449721
theorem B1637671 : Blo 634301 1637671 := bstep (se 1 (by rfl) ⟨1228253, by rfl⟩ : syracuseStep 1637671 = 2456507) B2456507
theorem B3440009 : Blo 634301 3440009 := bstep (se 2 (by rfl) ⟨1290003, by rfl⟩ : syracuseStep 3440009 = 2580007) B2580007
theorem B5144057 : Blo 634301 5144057 := bstep (se 2 (by rfl) ⟨1929021, by rfl⟩ : syracuseStep 5144057 = 3858043) B3858043
theorem B14680115 : Blo 634301 14680115 := bstep (se 1 (by rfl) ⟨11010086, by rfl⟩ : syracuseStep 14680115 = 22020173) B22020173
theorem B7241885 : Blo 634301 7241885 := bstep (se 3 (by rfl) ⟨1357853, by rfl⟩ : syracuseStep 7241885 = 2715707) B2715707
theorem B4883179 : Blo 634301 4883179 := bstep (se 1 (by rfl) ⟨3662384, by rfl⟩ : syracuseStep 4883179 = 7324769) B7324769
theorem B16548887 : Blo 634301 16548887 := bstep (se 1 (by rfl) ⟨12411665, by rfl⟩ : syracuseStep 16548887 = 24823331) B24823331
theorem B951503 : Blo 634301 951503 := bstep (se 1 (by rfl) ⟨713627, by rfl⟩ : syracuseStep 951503 = 1427255) B1427255
theorem B951707 : Blo 634301 951707 := bstep (se 1 (by rfl) ⟨713780, by rfl⟩ : syracuseStep 951707 = 1427561) B1427561
theorem B6129067 : Blo 634301 6129067 := bstep (se 1 (by rfl) ⟨4596800, by rfl⟩ : syracuseStep 6129067 = 9193601) B9193601
theorem B951929 : Blo 634301 951929 := bstep (se 2 (by rfl) ⟨356973, by rfl⟩ : syracuseStep 951929 = 713947) B713947
theorem B952031 : Blo 634301 952031 := bstep (se 1 (by rfl) ⟨714023, by rfl⟩ : syracuseStep 952031 = 1428047) B1428047
theorem B952127 : Blo 634301 952127 := bstep (se 1 (by rfl) ⟨714095, by rfl⟩ : syracuseStep 952127 = 1428191) B1428191
theorem B75171685 : Blo 634301 75171685 := bstep (se 4 (by rfl) ⟨7047345, by rfl⟩ : syracuseStep 75171685 = 14094691) B14094691
theorem B952295 : Blo 634301 952295 := bstep (se 1 (by rfl) ⟨714221, by rfl⟩ : syracuseStep 952295 = 1428443) B1428443
theorem B952313 : Blo 634301 952313 := bstep (se 2 (by rfl) ⟨357117, by rfl⟩ : syracuseStep 952313 = 714235) B714235
theorem B952415 : Blo 634301 952415 := bstep (se 1 (by rfl) ⟨714311, by rfl⟩ : syracuseStep 952415 = 1428623) B1428623
theorem B952475 : Blo 634301 952475 := bstep (se 1 (by rfl) ⟨714356, by rfl⟩ : syracuseStep 952475 = 1428713) B1428713
theorem B952511 : Blo 634301 952511 := bstep (se 1 (by rfl) ⟨714383, by rfl⟩ : syracuseStep 952511 = 1428767) B1428767
theorem B952553 : Blo 634301 952553 := bstep (se 2 (by rfl) ⟨357207, by rfl⟩ : syracuseStep 952553 = 714415) B714415
theorem B952859 : Blo 634301 952859 := bstep (se 1 (by rfl) ⟨714644, by rfl⟩ : syracuseStep 952859 = 1429289) B1429289
theorem B952937 : Blo 634301 952937 := bstep (se 2 (by rfl) ⟨357351, by rfl⟩ : syracuseStep 952937 = 714703) B714703
theorem B7736087 : Blo 634301 7736087 := bstep (se 1 (by rfl) ⟨5802065, by rfl⟩ : syracuseStep 7736087 = 11604131) B11604131
theorem B4590431 : Blo 634301 4590431 := bstep (se 1 (by rfl) ⟨3442823, by rfl⟩ : syracuseStep 4590431 = 6885647) B6885647
theorem B3214241 : Blo 634301 3214241 := bstep (se 2 (by rfl) ⟨1205340, by rfl⟩ : syracuseStep 3214241 = 2410681) B2410681
theorem B953465 : Blo 634301 953465 := bstep (se 2 (by rfl) ⟨357549, by rfl⟩ : syracuseStep 953465 = 715099) B715099
theorem B953567 : Blo 634301 953567 := bstep (se 1 (by rfl) ⟨715175, by rfl⟩ : syracuseStep 953567 = 1430351) B1430351
theorem B953609 : Blo 634301 953609 := bstep (se 2 (by rfl) ⟨357603, by rfl⟩ : syracuseStep 953609 = 715207) B715207
theorem B953711 : Blo 634301 953711 := bstep (se 1 (by rfl) ⟨715283, by rfl⟩ : syracuseStep 953711 = 1430567) B1430567
theorem B953831 : Blo 634301 953831 := bstep (se 1 (by rfl) ⟨715373, by rfl⟩ : syracuseStep 953831 = 1430747) B1430747
theorem B953963 : Blo 634301 953963 := bstep (se 1 (by rfl) ⟨715472, by rfl⟩ : syracuseStep 953963 = 1430945) B1430945
theorem B954089 : Blo 634301 954089 := bstep (se 2 (by rfl) ⟨357783, by rfl⟩ : syracuseStep 954089 = 715567) B715567
theorem B2035475 : Blo 634301 2035475 := bstep (se 1 (by rfl) ⟨1526606, by rfl⟩ : syracuseStep 2035475 = 3053213) B3053213
theorem B954233 : Blo 634301 954233 := bstep (se 2 (by rfl) ⟨357837, by rfl⟩ : syracuseStep 954233 = 715675) B715675
theorem B2723705 : Blo 634301 2723705 := bstep (se 2 (by rfl) ⟨1021389, by rfl⟩ : syracuseStep 2723705 = 2042779) B2042779
theorem B7966673 : Blo 634301 7966673 := bstep (se 2 (by rfl) ⟨2987502, by rfl⟩ : syracuseStep 7966673 = 5975005) B5975005
theorem B954335 : Blo 634301 954335 := bstep (se 1 (by rfl) ⟨715751, by rfl⟩ : syracuseStep 954335 = 1431503) B1431503
theorem B2297837 : Blo 634301 2297837 := bstep (se 3 (by rfl) ⟨430844, by rfl⟩ : syracuseStep 2297837 = 861689) B861689
theorem B1609915 : Blo 634301 1609915 := bstep (se 1 (by rfl) ⟨1207436, by rfl⟩ : syracuseStep 1609915 = 2414873) B2414873
theorem B954587 : Blo 634301 954587 := bstep (se 1 (by rfl) ⟨715940, by rfl⟩ : syracuseStep 954587 = 1431881) B1431881
theorem B954599 : Blo 634301 954599 := bstep (se 1 (by rfl) ⟨715949, by rfl⟩ : syracuseStep 954599 = 1431899) B1431899
theorem B1020287 : Blo 634301 1020287 := bstep (se 1 (by rfl) ⟨765215, by rfl⟩ : syracuseStep 1020287 = 1530431) B1530431
theorem B954761 : Blo 634301 954761 := bstep (se 2 (by rfl) ⟨358035, by rfl⟩ : syracuseStep 954761 = 716071) B716071
theorem B20648357 : Blo 634301 20648357 := bstep (se 4 (by rfl) ⟨1935783, by rfl⟩ : syracuseStep 20648357 = 3871567) B3871567
theorem B13734359 : Blo 634301 13734359 := bstep (se 1 (by rfl) ⟨10300769, by rfl⟩ : syracuseStep 13734359 = 20601539) B20601539
theorem B954857 : Blo 634301 954857 := bstep (se 2 (by rfl) ⟨358071, by rfl⟩ : syracuseStep 954857 = 716143) B716143
theorem B3052019 : Blo 634301 3052019 := bstep (se 1 (by rfl) ⟨2289014, by rfl⟩ : syracuseStep 3052019 = 4578029) B4578029
theorem B2757199 : Blo 634301 2757199 := bstep (se 1 (by rfl) ⟨2067899, by rfl⟩ : syracuseStep 2757199 = 4135799) B4135799
theorem B8163935 : Blo 634301 8163935 := bstep (se 1 (by rfl) ⟨6122951, by rfl⟩ : syracuseStep 8163935 = 12245903) B12245903
theorem B954983 : Blo 634301 954983 := bstep (se 1 (by rfl) ⟨716237, by rfl⟩ : syracuseStep 954983 = 1432475) B1432475
theorem B2724455 : Blo 634301 2724455 := bstep (se 1 (by rfl) ⟨2043341, by rfl⟩ : syracuseStep 2724455 = 4086683) B4086683
theorem B1610401 : Blo 634301 1610401 := bstep (se 2 (by rfl) ⟨603900, by rfl⟩ : syracuseStep 1610401 = 1207801) B1207801
theorem B29463263 : Blo 634301 29463263 := bstep (se 1 (by rfl) ⟨22097447, by rfl⟩ : syracuseStep 29463263 = 44194895) B44194895
theorem B955115 : Blo 634301 955115 := bstep (se 1 (by rfl) ⟨716336, by rfl⟩ : syracuseStep 955115 = 1432673) B1432673
theorem B955145 : Blo 634301 955145 := bstep (se 2 (by rfl) ⟨358179, by rfl⟩ : syracuseStep 955145 = 716359) B716359
theorem B955247 : Blo 634301 955247 := bstep (se 1 (by rfl) ⟨716435, by rfl⟩ : syracuseStep 955247 = 1432871) B1432871
theorem B7836551 : Blo 634301 7836551 := bstep (se 1 (by rfl) ⟨5877413, by rfl⟩ : syracuseStep 7836551 = 11754827) B11754827
theorem B955499 : Blo 634301 955499 := bstep (se 1 (by rfl) ⟨716624, by rfl⟩ : syracuseStep 955499 = 1433249) B1433249
theorem B3216671 : Blo 634301 3216671 := bstep (se 1 (by rfl) ⟨2412503, by rfl⟩ : syracuseStep 3216671 = 4825007) B4825007
theorem B955739 : Blo 634301 955739 := bstep (se 1 (by rfl) ⟨716804, by rfl⟩ : syracuseStep 955739 = 1433609) B1433609
theorem B2037089 : Blo 634301 2037089 := bstep (se 2 (by rfl) ⟨763908, by rfl⟩ : syracuseStep 2037089 = 1527817) B1527817
theorem B956015 : Blo 634301 956015 := bstep (se 1 (by rfl) ⟨717011, by rfl⟩ : syracuseStep 956015 = 1434023) B1434023
theorem B956087 : Blo 634301 956087 := bstep (se 1 (by rfl) ⟨717065, by rfl⟩ : syracuseStep 956087 = 1434131) B1434131
theorem B956123 : Blo 634301 956123 := bstep (se 1 (by rfl) ⟨717092, by rfl⟩ : syracuseStep 956123 = 1434185) B1434185
theorem B1611515 : Blo 634301 1611515 := bstep (se 1 (by rfl) ⟨1208636, by rfl⟩ : syracuseStep 1611515 = 2417273) B2417273
theorem B956297 : Blo 634301 956297 := bstep (se 2 (by rfl) ⟨358611, by rfl⟩ : syracuseStep 956297 = 717223) B717223
theorem B58824629 : Blo 634301 58824629 := bstep (se 5 (by rfl) ⟨2757404, by rfl⟩ : syracuseStep 58824629 = 5514809) B5514809
theorem B956399 : Blo 634301 956399 := bstep (se 1 (by rfl) ⟨717299, by rfl⟩ : syracuseStep 956399 = 1434599) B1434599
theorem B1611859 : Blo 634301 1611859 := bstep (se 1 (by rfl) ⟨1208894, by rfl⟩ : syracuseStep 1611859 = 2417789) B2417789
theorem B3053771 : Blo 634301 3053771 := bstep (se 1 (by rfl) ⟨2290328, by rfl⟩ : syracuseStep 3053771 = 4580657) B4580657
theorem B956651 : Blo 634301 956651 := bstep (se 1 (by rfl) ⟨717488, by rfl⟩ : syracuseStep 956651 = 1434977) B1434977
theorem B2201843 : Blo 634301 2201843 := bstep (se 1 (by rfl) ⟨1651382, by rfl⟩ : syracuseStep 2201843 = 3302765) B3302765
theorem B8821001 : Blo 634301 8821001 := bstep (se 2 (by rfl) ⟨3307875, by rfl⟩ : syracuseStep 8821001 = 6615751) B6615751
theorem B956711 : Blo 634301 956711 := bstep (se 1 (by rfl) ⟨717533, by rfl⟩ : syracuseStep 956711 = 1435067) B1435067
theorem B956795 : Blo 634301 956795 := bstep (se 1 (by rfl) ⟨717596, by rfl⟩ : syracuseStep 956795 = 1435193) B1435193
theorem B6822319 : Blo 634301 6822319 := bstep (se 1 (by rfl) ⟨5116739, by rfl⟩ : syracuseStep 6822319 = 10233479) B10233479
theorem B1612345 : Blo 634301 1612345 := bstep (se 2 (by rfl) ⟨604629, by rfl⟩ : syracuseStep 1612345 = 1209259) B1209259
theorem B957065 : Blo 634301 957065 := bstep (se 2 (by rfl) ⟨358899, by rfl⟩ : syracuseStep 957065 = 717799) B717799
theorem B957239 : Blo 634301 957239 := bstep (se 1 (by rfl) ⟨717929, by rfl⟩ : syracuseStep 957239 = 1435859) B1435859
theorem B1842011 : Blo 634301 1842011 := bstep (se 1 (by rfl) ⟨1381508, by rfl⟩ : syracuseStep 1842011 = 2763017) B2763017
theorem B957275 : Blo 634301 957275 := bstep (se 1 (by rfl) ⟨717956, by rfl⟩ : syracuseStep 957275 = 1435913) B1435913
theorem B1612649 : Blo 634301 1612649 := bstep (se 2 (by rfl) ⟨604743, by rfl⟩ : syracuseStep 1612649 = 1209487) B1209487
theorem B2038729 : Blo 634301 2038729 := bstep (se 2 (by rfl) ⟨764523, by rfl⟩ : syracuseStep 2038729 = 1529047) B1529047
theorem B957419 : Blo 634301 957419 := bstep (se 1 (by rfl) ⟨718064, by rfl⟩ : syracuseStep 957419 = 1436129) B1436129
theorem B2169985 : Blo 634301 2169985 := bstep (se 2 (by rfl) ⟨813744, by rfl⟩ : syracuseStep 2169985 = 1627489) B1627489
theorem B4365697 : Blo 634301 4365697 := bstep (se 2 (by rfl) ⟨1637136, by rfl⟩ : syracuseStep 4365697 = 3274273) B3274273
theorem B18357677 : Blo 634301 18357677 := bstep (se 3 (by rfl) ⟨3442064, by rfl⟩ : syracuseStep 18357677 = 6884129) B6884129
theorem B1613267 : Blo 634301 1613267 := bstep (se 1 (by rfl) ⟨1209950, by rfl⟩ : syracuseStep 1613267 = 2419901) B2419901
theorem B6954781 : Blo 634301 6954781 := bstep (se 3 (by rfl) ⟨1304021, by rfl⟩ : syracuseStep 6954781 = 2608043) B2608043
theorem B7250633 : Blo 634301 7250633 := bstep (se 2 (by rfl) ⟨2718987, by rfl⟩ : syracuseStep 7250633 = 5437975) B5437975
theorem B2171657 : Blo 634301 2171657 := bstep (se 2 (by rfl) ⟨814371, by rfl⟩ : syracuseStep 2171657 = 1628743) B1628743
theorem B3220235 : Blo 634301 3220235 := bstep (se 1 (by rfl) ⟨2415176, by rfl⟩ : syracuseStep 3220235 = 4830353) B4830353
theorem B3220397 : Blo 634301 3220397 := bstep (se 3 (by rfl) ⟨603824, by rfl⟩ : syracuseStep 3220397 = 1207649) B1207649
theorem B1746127 : Blo 634301 1746127 := bstep (se 1 (by rfl) ⟨1309595, by rfl⟩ : syracuseStep 1746127 = 2619191) B2619191
theorem B3089771 : Blo 634301 3089771 := bstep (se 1 (by rfl) ⟨2317328, by rfl⟩ : syracuseStep 3089771 = 4634657) B4634657
theorem B1615211 : Blo 634301 1615211 := bstep (se 1 (by rfl) ⟨1211408, by rfl⟩ : syracuseStep 1615211 = 2422817) B2422817
theorem B3614291 : Blo 634301 3614291 := bstep (se 1 (by rfl) ⟨2710718, by rfl⟩ : syracuseStep 3614291 = 5421437) B5421437
theorem B5154563 : Blo 634301 5154563 := bstep (se 1 (by rfl) ⟨3865922, by rfl⟩ : syracuseStep 5154563 = 7731845) B7731845
theorem B3221855 : Blo 634301 3221855 := bstep (se 1 (by rfl) ⟨2416391, by rfl⟩ : syracuseStep 3221855 = 4832783) B4832783
theorem B9775525 : Blo 634301 9775525 := bstep (se 4 (by rfl) ⟨916455, by rfl⟩ : syracuseStep 9775525 = 1832911) B1832911
theorem B3222017 : Blo 634301 3222017 := bstep (se 2 (by rfl) ⟨1208256, by rfl⟩ : syracuseStep 3222017 = 2416513) B2416513
theorem B2239721 : Blo 634301 2239721 := bstep (se 2 (by rfl) ⟨839895, by rfl⟩ : syracuseStep 2239721 = 1679791) B1679791
theorem B3222827 : Blo 634301 3222827 := bstep (se 1 (by rfl) ⟨2417120, by rfl⟩ : syracuseStep 3222827 = 4834241) B4834241
theorem B4599193 : Blo 634301 4599193 := bstep (se 2 (by rfl) ⟨1724697, by rfl⟩ : syracuseStep 4599193 = 3449395) B3449395
theorem B634343 : Blo 634301 634343 := bstep (se 1 (by rfl) ⟨475757, by rfl⟩ : syracuseStep 634343 = 951515) B951515
theorem B634459 : Blo 634301 634459 := bstep (se 1 (by rfl) ⟨475844, by rfl⟩ : syracuseStep 634459 = 951689) B951689
theorem B634695 : Blo 634301 634695 := bstep (se 1 (by rfl) ⟨476021, by rfl⟩ : syracuseStep 634695 = 952043) B952043
theorem B634847 : Blo 634301 634847 := bstep (se 1 (by rfl) ⟨476135, by rfl⟩ : syracuseStep 634847 = 952271) B952271
theorem B4141043 : Blo 634301 4141043 := bstep (se 1 (by rfl) ⟨3105782, by rfl⟩ : syracuseStep 4141043 = 6211565) B6211565
theorem B17018909 : Blo 634301 17018909 := bstep (se 3 (by rfl) ⟨3191045, by rfl⟩ : syracuseStep 17018909 = 6382091) B6382091
theorem B3616933 : Blo 634301 3616933 := bstep (se 4 (by rfl) ⟨339087, by rfl⟩ : syracuseStep 3616933 = 678175) B678175
theorem B2142395 : Blo 634301 2142395 := bstep (se 1 (by rfl) ⟨1606796, by rfl⟩ : syracuseStep 2142395 = 3213593) B3213593
theorem B635111 : Blo 634301 635111 := bstep (se 1 (by rfl) ⟨476333, by rfl⟩ : syracuseStep 635111 = 952667) B952667
theorem B635263 : Blo 634301 635263 := bstep (se 1 (by rfl) ⟨476447, by rfl⟩ : syracuseStep 635263 = 952895) B952895
theorem B635343 : Blo 634301 635343 := bstep (se 1 (by rfl) ⟨476507, by rfl⟩ : syracuseStep 635343 = 953015) B953015
theorem B1815119 : Blo 634301 1815119 := bstep (se 1 (by rfl) ⟨1361339, by rfl⟩ : syracuseStep 1815119 = 2722679) B2722679
theorem B635495 : Blo 634301 635495 := bstep (se 1 (by rfl) ⟨476621, by rfl⟩ : syracuseStep 635495 = 953243) B953243
theorem B2142881 : Blo 634301 2142881 := bstep (se 2 (by rfl) ⟨803580, by rfl⟩ : syracuseStep 2142881 = 1607161) B1607161
theorem B4829867 : Blo 634301 4829867 := bstep (se 1 (by rfl) ⟨3622400, by rfl⟩ : syracuseStep 4829867 = 7244801) B7244801
theorem B4076203 : Blo 634301 4076203 := bstep (se 1 (by rfl) ⟨3057152, by rfl⟩ : syracuseStep 4076203 = 6114305) B6114305
theorem B3224285 : Blo 634301 3224285 := bstep (se 3 (by rfl) ⟨604553, by rfl⟩ : syracuseStep 3224285 = 1209107) B1209107
theorem B635759 : Blo 634301 635759 := bstep (se 1 (by rfl) ⟨476819, by rfl⟩ : syracuseStep 635759 = 953639) B953639
theorem B635815 : Blo 634301 635815 := bstep (se 1 (by rfl) ⟨476861, by rfl⟩ : syracuseStep 635815 = 953723) B953723
theorem B18297809 : Blo 634301 18297809 := bstep (se 2 (by rfl) ⟨6861678, by rfl⟩ : syracuseStep 18297809 = 13723357) B13723357
theorem B635899 : Blo 634301 635899 := bstep (se 1 (by rfl) ⟨476924, by rfl⟩ : syracuseStep 635899 = 953849) B953849
theorem B635967 : Blo 634301 635967 := bstep (se 1 (by rfl) ⟨476975, by rfl⟩ : syracuseStep 635967 = 953951) B953951
theorem B636111 : Blo 634301 636111 := bstep (se 1 (by rfl) ⟨477083, by rfl⟩ : syracuseStep 636111 = 954167) B954167
theorem B636315 : Blo 634301 636315 := bstep (se 1 (by rfl) ⟨477236, by rfl⟩ : syracuseStep 636315 = 954473) B954473
theorem B2143745 : Blo 634301 2143745 := bstep (se 2 (by rfl) ⟨803904, by rfl⟩ : syracuseStep 2143745 = 1607809) B1607809
theorem B636527 : Blo 634301 636527 := bstep (se 1 (by rfl) ⟨477395, by rfl⟩ : syracuseStep 636527 = 954791) B954791
theorem B7353991 : Blo 634301 7353991 := bstep (se 1 (by rfl) ⟨5515493, by rfl⟩ : syracuseStep 7353991 = 11030987) B11030987
theorem B636583 : Blo 634301 636583 := bstep (se 1 (by rfl) ⟨477437, by rfl⟩ : syracuseStep 636583 = 954875) B954875
theorem B5420753 : Blo 634301 5420753 := bstep (se 2 (by rfl) ⟨2032782, by rfl⟩ : syracuseStep 5420753 = 4065565) B4065565
theorem B636667 : Blo 634301 636667 := bstep (se 1 (by rfl) ⟨477500, by rfl⟩ : syracuseStep 636667 = 955001) B955001
theorem B636703 : Blo 634301 636703 := bstep (se 1 (by rfl) ⟨477527, by rfl⟩ : syracuseStep 636703 = 955055) B955055
theorem B636735 : Blo 634301 636735 := bstep (se 1 (by rfl) ⟨477551, by rfl⟩ : syracuseStep 636735 = 955103) B955103
theorem B3618665 : Blo 634301 3618665 := bstep (se 2 (by rfl) ⟨1356999, by rfl⟩ : syracuseStep 3618665 = 2713999) B2713999
theorem B2144231 : Blo 634301 2144231 := bstep (se 1 (by rfl) ⟨1608173, by rfl⟩ : syracuseStep 2144231 = 3216347) B3216347
theorem B636911 : Blo 634301 636911 := bstep (se 1 (by rfl) ⟨477683, by rfl⟩ : syracuseStep 636911 = 955367) B955367
theorem B2144339 : Blo 634301 2144339 := bstep (se 1 (by rfl) ⟨1608254, by rfl⟩ : syracuseStep 2144339 = 3216509) B3216509
theorem B3225743 : Blo 634301 3225743 := bstep (se 1 (by rfl) ⟨2419307, by rfl⟩ : syracuseStep 3225743 = 4838615) B4838615
theorem B637083 : Blo 634301 637083 := bstep (se 1 (by rfl) ⟨477812, by rfl⟩ : syracuseStep 637083 = 955625) B955625
theorem B637119 : Blo 634301 637119 := bstep (se 1 (by rfl) ⟨477839, by rfl⟩ : syracuseStep 637119 = 955679) B955679
theorem B8698109 : Blo 634301 8698109 := bstep (se 3 (by rfl) ⟨1630895, by rfl⟩ : syracuseStep 8698109 = 3261791) B3261791
theorem B2144555 : Blo 634301 2144555 := bstep (se 1 (by rfl) ⟨1608416, by rfl⟩ : syracuseStep 2144555 = 3216833) B3216833
theorem B637231 : Blo 634301 637231 := bstep (se 1 (by rfl) ⟨477923, by rfl⟩ : syracuseStep 637231 = 955847) B955847
theorem B637467 : Blo 634301 637467 := bstep (se 1 (by rfl) ⟨478100, by rfl⟩ : syracuseStep 637467 = 956201) B956201
theorem B637471 : Blo 634301 637471 := bstep (se 1 (by rfl) ⟨478103, by rfl⟩ : syracuseStep 637471 = 956207) B956207
theorem B2144825 : Blo 634301 2144825 := bstep (se 2 (by rfl) ⟨804309, by rfl⟩ : syracuseStep 2144825 = 1608619) B1608619
theorem B637787 : Blo 634301 637787 := bstep (se 1 (by rfl) ⟨478340, by rfl⟩ : syracuseStep 637787 = 956681) B956681
theorem B637855 : Blo 634301 637855 := bstep (se 1 (by rfl) ⟨478391, by rfl⟩ : syracuseStep 637855 = 956783) B956783
theorem B4832297 : Blo 634301 4832297 := bstep (se 2 (by rfl) ⟨1812111, by rfl⟩ : syracuseStep 4832297 = 3624223) B3624223
theorem B637999 : Blo 634301 637999 := bstep (se 1 (by rfl) ⟨478499, by rfl⟩ : syracuseStep 637999 = 956999) B956999
theorem B638023 : Blo 634301 638023 := bstep (se 1 (by rfl) ⟨478517, by rfl⟩ : syracuseStep 638023 = 957035) B957035
theorem B12237905 : Blo 634301 12237905 := bstep (se 2 (by rfl) ⟨4589214, by rfl⟩ : syracuseStep 12237905 = 9178429) B9178429
theorem B638175 : Blo 634301 638175 := bstep (se 1 (by rfl) ⟨478631, by rfl⟩ : syracuseStep 638175 = 957263) B957263
theorem B1293799 : Blo 634301 1293799 := bstep (se 1 (by rfl) ⟨970349, by rfl⟩ : syracuseStep 1293799 = 1940699) B1940699
theorem B2146337 : Blo 634301 2146337 := bstep (se 2 (by rfl) ⟨804876, by rfl⟩ : syracuseStep 2146337 = 1609753) B1609753
theorem B3228335 : Blo 634301 3228335 := bstep (se 1 (by rfl) ⟨2421251, by rfl⟩ : syracuseStep 3228335 = 4842503) B4842503
theorem B4637627 : Blo 634301 4637627 := bstep (se 1 (by rfl) ⟨3478220, by rfl⟩ : syracuseStep 4637627 = 6956441) B6956441
theorem B3621833 : Blo 634301 3621833 := bstep (se 2 (by rfl) ⟨1358187, by rfl⟩ : syracuseStep 3621833 = 2716375) B2716375
theorem B1524761 : Blo 634301 1524761 := bstep (se 2 (by rfl) ⟨571785, by rfl⟩ : syracuseStep 1524761 = 1143571) B1143571
theorem B12239909 : Blo 634301 12239909 := bstep (se 4 (by rfl) ⟨1147491, by rfl⟩ : syracuseStep 12239909 = 2294983) B2294983
theorem B8177057 : Blo 634301 8177057 := bstep (se 2 (by rfl) ⟨3066396, by rfl⟩ : syracuseStep 8177057 = 6132793) B6132793
theorem B6211019 : Blo 634301 6211019 := bstep (se 1 (by rfl) ⟨4658264, by rfl⟩ : syracuseStep 6211019 = 9316529) B9316529
theorem B10307513 : Blo 634301 10307513 := bstep (se 2 (by rfl) ⟨3865317, by rfl⟩ : syracuseStep 10307513 = 7730635) B7730635
theorem B1427399 : Blo 634301 1427399 := bstep (se 1 (by rfl) ⟨1070549, by rfl⟩ : syracuseStep 1427399 = 2141099) B2141099
theorem B1427705 : Blo 634301 1427705 := bstep (se 2 (by rfl) ⟨535389, by rfl⟩ : syracuseStep 1427705 = 1070779) B1070779
theorem B1427759 : Blo 634301 1427759 := bstep (se 1 (by rfl) ⟨1070819, by rfl⟩ : syracuseStep 1427759 = 2141639) B2141639
theorem B19614109 : Blo 634301 19614109 := bstep (se 3 (by rfl) ⟨3677645, by rfl⟩ : syracuseStep 19614109 = 7355291) B7355291
theorem B1427975 : Blo 634301 1427975 := bstep (se 1 (by rfl) ⟨1070981, by rfl⟩ : syracuseStep 1427975 = 2141963) B2141963
theorem B805403 : Blo 634301 805403 := bstep (se 1 (by rfl) ⟨604052, by rfl⟩ : syracuseStep 805403 = 1208105) B1208105
theorem B15452795 : Blo 634301 15452795 := bstep (se 1 (by rfl) ⟨11589596, by rfl⟩ : syracuseStep 15452795 = 23179193) B23179193
theorem B1428155 : Blo 634301 1428155 := bstep (se 1 (by rfl) ⟨1071116, by rfl⟩ : syracuseStep 1428155 = 2142233) B2142233
theorem B806375 : Blo 634301 806375 := bstep (se 1 (by rfl) ⟨604781, by rfl⟩ : syracuseStep 806375 = 1209563) B1209563
theorem B1428983 : Blo 634301 1428983 := bstep (se 1 (by rfl) ⟨1071737, by rfl⟩ : syracuseStep 1428983 = 2143475) B2143475
theorem B8277509 : Blo 634301 8277509 := bstep (se 4 (by rfl) ⟨776016, by rfl⟩ : syracuseStep 8277509 = 1552033) B1552033
theorem B1429055 : Blo 634301 1429055 := bstep (se 1 (by rfl) ⟨1071791, by rfl⟩ : syracuseStep 1429055 = 2143583) B2143583
theorem B2412139 : Blo 634301 2412139 := bstep (se 1 (by rfl) ⟨1809104, by rfl⟩ : syracuseStep 2412139 = 3618209) B3618209
theorem B27512459 : Blo 634301 27512459 := bstep (se 1 (by rfl) ⟨20634344, by rfl⟩ : syracuseStep 27512459 = 41268689) B41268689
theorem B2150063 : Blo 634301 2150063 := bstep (se 1 (by rfl) ⟨1612547, by rfl⟩ : syracuseStep 2150063 = 3225095) B3225095
theorem B20598533 : Blo 634301 20598533 := bstep (se 4 (by rfl) ⟨1931112, by rfl⟩ : syracuseStep 20598533 = 3862225) B3862225
theorem B2150387 : Blo 634301 2150387 := bstep (se 1 (by rfl) ⟨1612790, by rfl⟩ : syracuseStep 2150387 = 3225581) B3225581
theorem B3625181 : Blo 634301 3625181 := bstep (se 3 (by rfl) ⟨679721, by rfl⟩ : syracuseStep 3625181 = 1359443) B1359443
theorem B2150711 : Blo 634301 2150711 := bstep (se 1 (by rfl) ⟨1613033, by rfl⟩ : syracuseStep 2150711 = 3226067) B3226067
theorem B2183561 : Blo 634301 2183561 := bstep (se 2 (by rfl) ⟨818835, by rfl⟩ : syracuseStep 2183561 = 1637671) B1637671
theorem B1430009 : Blo 634301 1430009 := bstep (se 2 (by rfl) ⟨536253, by rfl⟩ : syracuseStep 1430009 = 1072507) B1072507
theorem B2150927 : Blo 634301 2150927 := bstep (se 1 (by rfl) ⟨1613195, by rfl⟩ : syracuseStep 2150927 = 3226391) B3226391
theorem B1430099 : Blo 634301 1430099 := bstep (se 1 (by rfl) ⟨1072574, by rfl⟩ : syracuseStep 1430099 = 2145149) B2145149
theorem B1430279 : Blo 634301 1430279 := bstep (se 1 (by rfl) ⟨1072709, by rfl⟩ : syracuseStep 1430279 = 2145419) B2145419
theorem B3429371 : Blo 634301 3429371 := bstep (se 1 (by rfl) ⟨2572028, by rfl⟩ : syracuseStep 3429371 = 5144057) B5144057
theorem B19650059 : Blo 634301 19650059 := bstep (se 1 (by rfl) ⟨14737544, by rfl⟩ : syracuseStep 19650059 = 29475089) B29475089
theorem B2152007 : Blo 634301 2152007 := bstep (se 1 (by rfl) ⟨1614005, by rfl⟩ : syracuseStep 2152007 = 3228011) B3228011
theorem B26105489 : Blo 634301 26105489 := bstep (se 2 (by rfl) ⟨9789558, by rfl⟩ : syracuseStep 26105489 = 19579117) B19579117
theorem B677543 : Blo 634301 677543 := bstep (se 1 (by rfl) ⟨508157, by rfl⟩ : syracuseStep 677543 = 1016315) B1016315
theorem B1070759 : Blo 634301 1070759 := bstep (se 1 (by rfl) ⟨803069, by rfl⟩ : syracuseStep 1070759 = 1606139) B1606139
theorem B1431359 : Blo 634301 1431359 := bstep (se 1 (by rfl) ⟨1073519, by rfl⟩ : syracuseStep 1431359 = 2147039) B2147039
theorem B4085711 : Blo 634301 4085711 := bstep (se 1 (by rfl) ⟨3064283, by rfl⟩ : syracuseStep 4085711 = 6128567) B6128567
theorem B4085761 : Blo 634301 4085761 := bstep (se 2 (by rfl) ⟨1532160, by rfl⟩ : syracuseStep 4085761 = 3064321) B3064321
theorem B1431647 : Blo 634301 1431647 := bstep (se 1 (by rfl) ⟨1073735, by rfl⟩ : syracuseStep 1431647 = 2147471) B2147471
theorem B1071407 : Blo 634301 1071407 := bstep (se 1 (by rfl) ⟨803555, by rfl⟩ : syracuseStep 1071407 = 1607111) B1607111
theorem B2152979 : Blo 634301 2152979 := bstep (se 1 (by rfl) ⟨1614734, by rfl⟩ : syracuseStep 2152979 = 3229469) B3229469
theorem B1071643 : Blo 634301 1071643 := bstep (se 1 (by rfl) ⟨803732, by rfl⟩ : syracuseStep 1071643 = 1607465) B1607465
theorem B2939489 : Blo 634301 2939489 := bstep (se 2 (by rfl) ⟨1102308, by rfl⟩ : syracuseStep 2939489 = 2204617) B2204617
theorem B4840073 : Blo 634301 4840073 := bstep (se 2 (by rfl) ⟨1815027, by rfl⟩ : syracuseStep 4840073 = 3630055) B3630055
theorem B1432403 : Blo 634301 1432403 := bstep (se 1 (by rfl) ⟨1074302, by rfl⟩ : syracuseStep 1432403 = 2148605) B2148605
theorem B908329 : Blo 634301 908329 := bstep (se 2 (by rfl) ⟨340623, by rfl⟩ : syracuseStep 908329 = 681247) B681247
theorem B1432943 : Blo 634301 1432943 := bstep (se 1 (by rfl) ⟨1074707, by rfl⟩ : syracuseStep 1432943 = 2149415) B2149415
theorem B1072615 : Blo 634301 1072615 := bstep (se 1 (by rfl) ⟨804461, by rfl⟩ : syracuseStep 1072615 = 1608923) B1608923
theorem B1072703 : Blo 634301 1072703 := bstep (se 1 (by rfl) ⟨804527, by rfl⟩ : syracuseStep 1072703 = 1609055) B1609055
theorem B1433231 : Blo 634301 1433231 := bstep (se 1 (by rfl) ⟨1074923, by rfl⟩ : syracuseStep 1433231 = 2149847) B2149847
theorem B1433321 : Blo 634301 1433321 := bstep (se 2 (by rfl) ⟨537495, by rfl⟩ : syracuseStep 1433321 = 1074991) B1074991
theorem B3628871 : Blo 634301 3628871 := bstep (se 1 (by rfl) ⟨2721653, by rfl⟩ : syracuseStep 3628871 = 5443307) B5443307
theorem B4087709 : Blo 634301 4087709 := bstep (se 3 (by rfl) ⟨766445, by rfl⟩ : syracuseStep 4087709 = 1532891) B1532891
theorem B1073371 : Blo 634301 1073371 := bstep (se 1 (by rfl) ⟨805028, by rfl⟩ : syracuseStep 1073371 = 1610057) B1610057
theorem B1532191 : Blo 634301 1532191 := bstep (se 1 (by rfl) ⟨1149143, by rfl⟩ : syracuseStep 1532191 = 2298287) B2298287
theorem B1073641 : Blo 634301 1073641 := bstep (se 2 (by rfl) ⟨402615, by rfl⟩ : syracuseStep 1073641 = 805231) B805231
theorem B5431961 : Blo 634301 5431961 := bstep (se 2 (by rfl) ⟨2036985, by rfl⟩ : syracuseStep 5431961 = 4073971) B4073971
theorem B1434347 : Blo 634301 1434347 := bstep (se 1 (by rfl) ⟨1075760, by rfl⟩ : syracuseStep 1434347 = 2151521) B2151521
theorem B680815 : Blo 634301 680815 := bstep (se 1 (by rfl) ⟨510611, by rfl⟩ : syracuseStep 680815 = 1021223) B1021223
theorem B1205455 : Blo 634301 1205455 := bstep (se 1 (by rfl) ⟨904091, by rfl⟩ : syracuseStep 1205455 = 1808183) B1808183
theorem B3630329 : Blo 634301 3630329 := bstep (se 2 (by rfl) ⟨1361373, by rfl⟩ : syracuseStep 3630329 = 2722747) B2722747
theorem B1205675 : Blo 634301 1205675 := bstep (se 1 (by rfl) ⟨904256, by rfl⟩ : syracuseStep 1205675 = 1808513) B1808513
theorem B4842989 : Blo 634301 4842989 := bstep (se 3 (by rfl) ⟨908060, by rfl⟩ : syracuseStep 4842989 = 1816121) B1816121
theorem B4089325 : Blo 634301 4089325 := bstep (se 3 (by rfl) ⟨766748, by rfl⟩ : syracuseStep 4089325 = 1533497) B1533497
theorem B1435247 : Blo 634301 1435247 := bstep (se 1 (by rfl) ⟨1076435, by rfl⟩ : syracuseStep 1435247 = 2152871) B2152871
theorem B1074809 : Blo 634301 1074809 := bstep (se 2 (by rfl) ⟨403053, by rfl⟩ : syracuseStep 1074809 = 806107) B806107
theorem B9791165 : Blo 634301 9791165 := bstep (se 3 (by rfl) ⟨1835843, by rfl⟩ : syracuseStep 9791165 = 3671687) B3671687
theorem B1435355 : Blo 634301 1435355 := bstep (se 1 (by rfl) ⟨1076516, by rfl⟩ : syracuseStep 1435355 = 2153033) B2153033
theorem B714559 : Blo 634301 714559 := bstep (se 1 (by rfl) ⟨535919, by rfl⟩ : syracuseStep 714559 = 1071839) B1071839
theorem B2287561 : Blo 634301 2287561 := bstep (se 2 (by rfl) ⟨857835, by rfl⟩ : syracuseStep 2287561 = 1715671) B1715671
theorem B3663863 : Blo 634301 3663863 := bstep (se 1 (by rfl) ⟨2747897, by rfl⟩ : syracuseStep 3663863 = 5495795) B5495795
theorem B714847 : Blo 634301 714847 := bstep (se 1 (by rfl) ⟨536135, by rfl⟩ : syracuseStep 714847 = 1072271) B1072271
theorem B1075295 : Blo 634301 1075295 := bstep (se 1 (by rfl) ⟨806471, by rfl⟩ : syracuseStep 1075295 = 1612943) B1612943
theorem B2287919 : Blo 634301 2287919 := bstep (se 1 (by rfl) ⟨1715939, by rfl⟩ : syracuseStep 2287919 = 3431879) B3431879
theorem B4352507 : Blo 634301 4352507 := bstep (se 1 (by rfl) ⟨3264380, by rfl⟩ : syracuseStep 4352507 = 6528761) B6528761
theorem B2092007 : Blo 634301 2092007 := bstep (se 1 (by rfl) ⟨1569005, by rfl⟩ : syracuseStep 2092007 = 3138011) B3138011
theorem B715999 : Blo 634301 715999 := bstep (se 1 (by rfl) ⟨536999, by rfl⟩ : syracuseStep 715999 = 1073999) B1073999
theorem B3632471 : Blo 634301 3632471 := bstep (se 1 (by rfl) ⟨2724353, by rfl⟩ : syracuseStep 3632471 = 5448707) B5448707
theorem B1076591 : Blo 634301 1076591 := bstep (se 1 (by rfl) ⟨807443, by rfl⟩ : syracuseStep 1076591 = 1614887) B1614887
theorem B1076827 : Blo 634301 1076827 := bstep (se 1 (by rfl) ⟨807620, by rfl⟩ : syracuseStep 1076827 = 1615241) B1615241
theorem B1076969 : Blo 634301 1076969 := bstep (se 2 (by rfl) ⟨403863, by rfl⟩ : syracuseStep 1076969 = 807727) B807727
theorem B4845419 : Blo 634301 4845419 := bstep (se 1 (by rfl) ⟨3634064, by rfl⟩ : syracuseStep 4845419 = 7268129) B7268129
theorem B1208287 : Blo 634301 1208287 := bstep (se 1 (by rfl) ⟨906215, by rfl⟩ : syracuseStep 1208287 = 1812431) B1812431
theorem B5435585 : Blo 634301 5435585 := bstep (se 2 (by rfl) ⟨2038344, by rfl⟩ : syracuseStep 5435585 = 4076689) B4076689
theorem B1143239 : Blo 634301 1143239 := bstep (se 1 (by rfl) ⟨857429, by rfl⟩ : syracuseStep 1143239 = 1714859) B1714859
theorem B54915569 : Blo 634301 54915569 := bstep (se 2 (by rfl) ⟨20593338, by rfl⟩ : syracuseStep 54915569 = 41186677) B41186677
theorem B2290169 : Blo 634301 2290169 := bstep (se 2 (by rfl) ⟨858813, by rfl⟩ : syracuseStep 2290169 = 1717627) B1717627
theorem B16708193 : Blo 634301 16708193 := bstep (se 2 (by rfl) ⟨6265572, by rfl⟩ : syracuseStep 16708193 = 12531145) B12531145
theorem B4584833 : Blo 634301 4584833 := bstep (se 2 (by rfl) ⟨1719312, by rfl⟩ : syracuseStep 4584833 = 3438625) B3438625
theorem B15725987 : Blo 634301 15725987 := bstep (se 1 (by rfl) ⟨11794490, by rfl⟩ : syracuseStep 15725987 = 23588981) B23588981
theorem B9434825 : Blo 634301 9434825 := bstep (se 2 (by rfl) ⟨3538059, by rfl⟩ : syracuseStep 9434825 = 7076119) B7076119
theorem B2586887 : Blo 634301 2586887 := bstep (se 1 (by rfl) ⟨1940165, by rfl⟩ : syracuseStep 2586887 = 3880331) B3880331
theorem B1931627 : Blo 634301 1931627 := bstep (se 1 (by rfl) ⟨1448720, by rfl⟩ : syracuseStep 1931627 = 2897441) B2897441
theorem B9173357 : Blo 634301 9173357 := bstep (se 3 (by rfl) ⟨1720004, by rfl⟩ : syracuseStep 9173357 = 3440009) B3440009
theorem B1016507 : Blo 634301 1016507 := bstep (se 1 (by rfl) ⟨762380, by rfl⟩ : syracuseStep 1016507 = 1524761) B1524761
theorem B8159939 : Blo 634301 8159939 := bstep (se 1 (by rfl) ⟨6119954, by rfl⟩ : syracuseStep 8159939 = 12239909) B12239909
theorem B2720765 : Blo 634301 2720765 := bstep (se 3 (by rfl) ⟨510143, by rfl⟩ : syracuseStep 2720765 = 1020287) B1020287
theorem B3048637 : Blo 634301 3048637 := bstep (se 3 (by rfl) ⟨571619, by rfl⟩ : syracuseStep 3048637 = 1143239) B1143239
theorem B951599 : Blo 634301 951599 := bstep (se 1 (by rfl) ⟨713699, by rfl⟩ : syracuseStep 951599 = 1427399) B1427399
theorem B951803 : Blo 634301 951803 := bstep (se 1 (by rfl) ⟨713852, by rfl⟩ : syracuseStep 951803 = 1427705) B1427705
theorem B951839 : Blo 634301 951839 := bstep (se 1 (by rfl) ⟨713879, by rfl⟩ : syracuseStep 951839 = 1427759) B1427759
theorem B1607273 : Blo 634301 1607273 := bstep (se 2 (by rfl) ⟨602727, by rfl⟩ : syracuseStep 1607273 = 1205455) B1205455
theorem B2328169 : Blo 634301 2328169 := bstep (se 2 (by rfl) ⟨873063, by rfl⟩ : syracuseStep 2328169 = 1746127) B1746127
theorem B951983 : Blo 634301 951983 := bstep (se 1 (by rfl) ⟨713987, by rfl⟩ : syracuseStep 951983 = 1427975) B1427975
theorem B952103 : Blo 634301 952103 := bstep (se 1 (by rfl) ⟨714077, by rfl⟩ : syracuseStep 952103 = 1428155) B1428155
theorem B952655 : Blo 634301 952655 := bstep (se 1 (by rfl) ⟨714491, by rfl⟩ : syracuseStep 952655 = 1428983) B1428983
theorem B952703 : Blo 634301 952703 := bstep (se 1 (by rfl) ⟨714527, by rfl⟩ : syracuseStep 952703 = 1429055) B1429055
theorem B952745 : Blo 634301 952745 := bstep (se 2 (by rfl) ⟨357279, by rfl⟩ : syracuseStep 952745 = 714559) B714559
theorem B13732355 : Blo 634301 13732355 := bstep (se 1 (by rfl) ⟨10299266, by rfl⟩ : syracuseStep 13732355 = 20598533) B20598533
theorem B3050081 : Blo 634301 3050081 := bstep (se 2 (by rfl) ⟨1143780, by rfl⟩ : syracuseStep 3050081 = 2287561) B2287561
theorem B5311115 : Blo 634301 5311115 := bstep (se 1 (by rfl) ⟨3983336, by rfl⟩ : syracuseStep 5311115 = 7966673) B7966673
theorem B953129 : Blo 634301 953129 := bstep (se 2 (by rfl) ⟨357423, by rfl⟩ : syracuseStep 953129 = 714847) B714847
theorem B13765571 : Blo 634301 13765571 := bstep (se 1 (by rfl) ⟨10324178, by rfl⟩ : syracuseStep 13765571 = 20648357) B20648357
theorem B953339 : Blo 634301 953339 := bstep (se 1 (by rfl) ⟨715004, by rfl⟩ : syracuseStep 953339 = 1430009) B1430009
theorem B953399 : Blo 634301 953399 := bstep (se 1 (by rfl) ⟨715049, by rfl⟩ : syracuseStep 953399 = 1430099) B1430099
theorem B5442623 : Blo 634301 5442623 := bstep (se 1 (by rfl) ⟨4081967, by rfl⟩ : syracuseStep 5442623 = 8163935) B8163935
theorem B953519 : Blo 634301 953519 := bstep (se 1 (by rfl) ⟨715139, by rfl⟩ : syracuseStep 953519 = 1430279) B1430279
theorem B26152145 : Blo 634301 26152145 := bstep (se 2 (by rfl) ⟨9807054, by rfl⟩ : syracuseStep 26152145 = 19614109) B19614109
theorem B17403659 : Blo 634301 17403659 := bstep (se 1 (by rfl) ⟨13052744, by rfl⟩ : syracuseStep 17403659 = 26105489) B26105489
theorem B954239 : Blo 634301 954239 := bstep (se 1 (by rfl) ⟨715679, by rfl⟩ : syracuseStep 954239 = 1431359) B1431359
theorem B2723807 : Blo 634301 2723807 := bstep (se 1 (by rfl) ⟨2042855, by rfl⟩ : syracuseStep 2723807 = 4085711) B4085711
theorem B954431 : Blo 634301 954431 := bstep (se 1 (by rfl) ⟨715823, by rfl⟩ : syracuseStep 954431 = 1431647) B1431647
theorem B2035847 : Blo 634301 2035847 := bstep (se 1 (by rfl) ⟨1526885, by rfl⟩ : syracuseStep 2035847 = 3053771) B3053771
theorem B954665 : Blo 634301 954665 := bstep (se 2 (by rfl) ⟨357999, by rfl⟩ : syracuseStep 954665 = 715999) B715999
theorem B1806781 : Blo 634301 1806781 := bstep (se 3 (by rfl) ⟨338771, by rfl⟩ : syracuseStep 1806781 = 677543) B677543
theorem B6132257 : Blo 634301 6132257 := bstep (se 2 (by rfl) ⟨2299596, by rfl⟩ : syracuseStep 6132257 = 4599193) B4599193
theorem B954935 : Blo 634301 954935 := bstep (se 1 (by rfl) ⟨716201, by rfl⟩ : syracuseStep 954935 = 1432403) B1432403
theorem B3216185 : Blo 634301 3216185 := bstep (se 2 (by rfl) ⟨1206069, by rfl⟩ : syracuseStep 3216185 = 2412139) B2412139
theorem B955295 : Blo 634301 955295 := bstep (se 1 (by rfl) ⟨716471, by rfl⟩ : syracuseStep 955295 = 1432943) B1432943
theorem B955487 : Blo 634301 955487 := bstep (se 1 (by rfl) ⟨716615, by rfl⟩ : syracuseStep 955487 = 1433231) B1433231
theorem B955547 : Blo 634301 955547 := bstep (se 1 (by rfl) ⟨716660, by rfl⟩ : syracuseStep 955547 = 1433321) B1433321
theorem B2725139 : Blo 634301 2725139 := bstep (se 1 (by rfl) ⟨2043854, by rfl⟩ : syracuseStep 2725139 = 4087709) B4087709
theorem B1611049 : Blo 634301 1611049 := bstep (se 2 (by rfl) ⟨604143, by rfl⟩ : syracuseStep 1611049 = 1208287) B1208287
theorem B4822577 : Blo 634301 4822577 := bstep (se 2 (by rfl) ⟨1808466, by rfl⟩ : syracuseStep 4822577 = 3616933) B3616933
theorem B956231 : Blo 634301 956231 := bstep (se 1 (by rfl) ⟨717173, by rfl⟩ : syracuseStep 956231 = 1434347) B1434347
theorem B3676265 : Blo 634301 3676265 := bstep (se 2 (by rfl) ⟨1378599, by rfl⟩ : syracuseStep 3676265 = 2757199) B2757199
theorem B956831 : Blo 634301 956831 := bstep (se 1 (by rfl) ⟨717623, by rfl⟩ : syracuseStep 956831 = 1435247) B1435247
theorem B956903 : Blo 634301 956903 := bstep (se 1 (by rfl) ⟨717677, by rfl⟩ : syracuseStep 956903 = 1435355) B1435355
theorem B9805321 : Blo 634301 9805321 := bstep (se 2 (by rfl) ⟨3676995, by rfl⟩ : syracuseStep 9805321 = 7353991) B7353991
theorem B2760695 : Blo 634301 2760695 := bstep (se 1 (by rfl) ⟨2070521, by rfl⟩ : syracuseStep 2760695 = 4141043) B4141043
theorem B5447681 : Blo 634301 5447681 := bstep (se 2 (by rfl) ⟨2042880, by rfl⟩ : syracuseStep 5447681 = 4085761) B4085761
theorem B11345939 : Blo 634301 11345939 := bstep (se 1 (by rfl) ⟨8509454, by rfl⟩ : syracuseStep 11345939 = 17018909) B17018909
theorem B36610379 : Blo 634301 36610379 := bstep (se 1 (by rfl) ⟨27457784, by rfl⟩ : syracuseStep 36610379 = 54915569) B54915569
theorem B3219911 : Blo 634301 3219911 := bstep (se 1 (by rfl) ⟨2414933, by rfl⟩ : syracuseStep 3219911 = 4829867) B4829867
theorem B12198539 : Blo 634301 12198539 := bstep (se 1 (by rfl) ⟨9148904, by rfl⟩ : syracuseStep 12198539 = 18297809) B18297809
theorem B3056555 : Blo 634301 3056555 := bstep (se 1 (by rfl) ⟨2292416, by rfl⟩ : syracuseStep 3056555 = 4584833) B4584833
theorem B3613835 : Blo 634301 3613835 := bstep (se 1 (by rfl) ⟨2710376, by rfl⟩ : syracuseStep 3613835 = 5420753) B5420753
theorem B2893313 : Blo 634301 2893313 := bstep (se 2 (by rfl) ⟨1084992, by rfl⟩ : syracuseStep 2893313 = 2169985) B2169985
theorem B1287751 : Blo 634301 1287751 := bstep (se 1 (by rfl) ⟨965813, by rfl⟩ : syracuseStep 1287751 = 1931627) B1931627
theorem B3221531 : Blo 634301 3221531 := bstep (se 1 (by rfl) ⟨2416148, by rfl⟩ : syracuseStep 3221531 = 4832297) B4832297
theorem B4827923 : Blo 634301 4827923 := bstep (se 1 (by rfl) ⟨3620942, by rfl⟩ : syracuseStep 4827923 = 7241885) B7241885
theorem B2042921 : Blo 634301 2042921 := bstep (se 2 (by rfl) ⟨766095, by rfl⟩ : syracuseStep 2042921 = 1532191) B1532191
theorem B3091751 : Blo 634301 3091751 := bstep (se 1 (by rfl) ⟨2318813, by rfl⟩ : syracuseStep 3091751 = 4637627) B4637627
theorem B634335 : Blo 634301 634335 := bstep (se 1 (by rfl) ⟨475751, by rfl⟩ : syracuseStep 634335 = 951503) B951503
theorem B634471 : Blo 634301 634471 := bstep (se 1 (by rfl) ⟨475853, by rfl⟩ : syracuseStep 634471 = 951707) B951707
theorem B5451371 : Blo 634301 5451371 := bstep (se 1 (by rfl) ⟨4088528, by rfl⟩ : syracuseStep 5451371 = 8177057) B8177057
theorem B4140679 : Blo 634301 4140679 := bstep (se 1 (by rfl) ⟨3105509, by rfl⟩ : syracuseStep 4140679 = 6211019) B6211019
theorem B634619 : Blo 634301 634619 := bstep (se 1 (by rfl) ⟨475964, by rfl⟩ : syracuseStep 634619 = 951929) B951929
theorem B634687 : Blo 634301 634687 := bstep (se 1 (by rfl) ⟨476015, by rfl⟩ : syracuseStep 634687 = 952031) B952031
theorem B634751 : Blo 634301 634751 := bstep (se 1 (by rfl) ⟨476063, by rfl⟩ : syracuseStep 634751 = 952127) B952127
theorem B8138717 : Blo 634301 8138717 := bstep (se 3 (by rfl) ⟨1526009, by rfl⟩ : syracuseStep 8138717 = 3052019) B3052019
theorem B634863 : Blo 634301 634863 := bstep (se 1 (by rfl) ⟨476147, by rfl⟩ : syracuseStep 634863 = 952295) B952295
theorem B634875 : Blo 634301 634875 := bstep (se 1 (by rfl) ⟨476156, by rfl⟩ : syracuseStep 634875 = 952313) B952313
theorem B634943 : Blo 634301 634943 := bstep (se 1 (by rfl) ⟨476207, by rfl⟩ : syracuseStep 634943 = 952415) B952415
theorem B634983 : Blo 634301 634983 := bstep (se 1 (by rfl) ⟨476237, by rfl⟩ : syracuseStep 634983 = 952475) B952475
theorem B635007 : Blo 634301 635007 := bstep (se 1 (by rfl) ⟨476255, by rfl⟩ : syracuseStep 635007 = 952511) B952511
theorem B635035 : Blo 634301 635035 := bstep (se 1 (by rfl) ⟨476276, by rfl⟩ : syracuseStep 635035 = 952553) B952553
theorem B635239 : Blo 634301 635239 := bstep (se 1 (by rfl) ⟨476429, by rfl⟩ : syracuseStep 635239 = 952859) B952859
theorem B635291 : Blo 634301 635291 := bstep (se 1 (by rfl) ⟨476468, by rfl⟩ : syracuseStep 635291 = 952937) B952937
theorem B10301863 : Blo 634301 10301863 := bstep (se 1 (by rfl) ⟨7726397, by rfl⟩ : syracuseStep 10301863 = 15452795) B15452795
theorem B5157391 : Blo 634301 5157391 := bstep (se 1 (by rfl) ⟨3868043, by rfl⟩ : syracuseStep 5157391 = 7736087) B7736087
theorem B8172089 : Blo 634301 8172089 := bstep (se 2 (by rfl) ⟨3064533, by rfl⟩ : syracuseStep 8172089 = 6129067) B6129067
theorem B3060287 : Blo 634301 3060287 := bstep (se 1 (by rfl) ⟨2295215, by rfl⟩ : syracuseStep 3060287 = 4590431) B4590431
theorem B2142827 : Blo 634301 2142827 := bstep (se 1 (by rfl) ⟨1607120, by rfl⟩ : syracuseStep 2142827 = 3214241) B3214241
theorem B5452433 : Blo 634301 5452433 := bstep (se 2 (by rfl) ⟨2044662, by rfl⟩ : syracuseStep 5452433 = 4089325) B4089325
theorem B635643 : Blo 634301 635643 := bstep (se 1 (by rfl) ⟨476732, by rfl⟩ : syracuseStep 635643 = 953465) B953465
theorem B635711 : Blo 634301 635711 := bstep (se 1 (by rfl) ⟨476783, by rfl⟩ : syracuseStep 635711 = 953567) B953567
theorem B635739 : Blo 634301 635739 := bstep (se 1 (by rfl) ⟨476804, by rfl⟩ : syracuseStep 635739 = 953609) B953609
theorem B635807 : Blo 634301 635807 := bstep (se 1 (by rfl) ⟨476855, by rfl⟩ : syracuseStep 635807 = 953711) B953711
theorem B635887 : Blo 634301 635887 := bstep (se 1 (by rfl) ⟨476915, by rfl⟩ : syracuseStep 635887 = 953831) B953831
theorem B635975 : Blo 634301 635975 := bstep (se 1 (by rfl) ⟨476981, by rfl⟩ : syracuseStep 635975 = 953963) B953963
theorem B636059 : Blo 634301 636059 := bstep (se 1 (by rfl) ⟨477044, by rfl⟩ : syracuseStep 636059 = 954089) B954089
theorem B1356983 : Blo 634301 1356983 := bstep (se 1 (by rfl) ⟨1017737, by rfl⟩ : syracuseStep 1356983 = 2035475) B2035475
theorem B636155 : Blo 634301 636155 := bstep (se 1 (by rfl) ⟨477116, by rfl⟩ : syracuseStep 636155 = 954233) B954233
theorem B1815803 : Blo 634301 1815803 := bstep (se 1 (by rfl) ⟨1361852, by rfl⟩ : syracuseStep 1815803 = 2723705) B2723705
theorem B636223 : Blo 634301 636223 := bstep (se 1 (by rfl) ⟨477167, by rfl⟩ : syracuseStep 636223 = 954335) B954335
theorem B636391 : Blo 634301 636391 := bstep (se 1 (by rfl) ⟨477293, by rfl⟩ : syracuseStep 636391 = 954587) B954587
theorem B636399 : Blo 634301 636399 := bstep (se 1 (by rfl) ⟨477299, by rfl⟩ : syracuseStep 636399 = 954599) B954599
theorem B636507 : Blo 634301 636507 := bstep (se 1 (by rfl) ⟨477380, by rfl⟩ : syracuseStep 636507 = 954761) B954761
theorem B1455707 : Blo 634301 1455707 := bstep (se 1 (by rfl) ⟨1091780, by rfl⟩ : syracuseStep 1455707 = 2183561) B2183561
theorem B9156239 : Blo 634301 9156239 := bstep (se 1 (by rfl) ⟨6867179, by rfl⟩ : syracuseStep 9156239 = 13734359) B13734359
theorem B636571 : Blo 634301 636571 := bstep (se 1 (by rfl) ⟨477428, by rfl⟩ : syracuseStep 636571 = 954857) B954857
theorem B636655 : Blo 634301 636655 := bstep (se 1 (by rfl) ⟨477491, by rfl⟩ : syracuseStep 636655 = 954983) B954983
theorem B19642175 : Blo 634301 19642175 := bstep (se 1 (by rfl) ⟨14731631, by rfl⟩ : syracuseStep 19642175 = 29463263) B29463263
theorem B636743 : Blo 634301 636743 := bstep (se 1 (by rfl) ⟨477557, by rfl⟩ : syracuseStep 636743 = 955115) B955115
theorem B636763 : Blo 634301 636763 := bstep (se 1 (by rfl) ⟨477572, by rfl⟩ : syracuseStep 636763 = 955145) B955145
theorem B636831 : Blo 634301 636831 := bstep (se 1 (by rfl) ⟨477623, by rfl⟩ : syracuseStep 636831 = 955247) B955247
theorem B5224367 : Blo 634301 5224367 := bstep (se 1 (by rfl) ⟨3918275, by rfl⟩ : syracuseStep 5224367 = 7836551) B7836551
theorem B636999 : Blo 634301 636999 := bstep (se 1 (by rfl) ⟨477749, by rfl⟩ : syracuseStep 636999 = 955499) B955499
theorem B2144447 : Blo 634301 2144447 := bstep (se 1 (by rfl) ⟨1608335, by rfl⟩ : syracuseStep 2144447 = 3216671) B3216671
theorem B637159 : Blo 634301 637159 := bstep (se 1 (by rfl) ⟨477869, by rfl⟩ : syracuseStep 637159 = 955739) B955739
theorem B1358059 : Blo 634301 1358059 := bstep (se 1 (by rfl) ⟨1018544, by rfl⟩ : syracuseStep 1358059 = 2037089) B2037089
theorem B637343 : Blo 634301 637343 := bstep (se 1 (by rfl) ⟨478007, by rfl⟩ : syracuseStep 637343 = 956015) B956015
theorem B637391 : Blo 634301 637391 := bstep (se 1 (by rfl) ⟨478043, by rfl⟩ : syracuseStep 637391 = 956087) B956087
theorem B637415 : Blo 634301 637415 := bstep (se 1 (by rfl) ⟨478061, by rfl⟩ : syracuseStep 637415 = 956123) B956123
theorem B637531 : Blo 634301 637531 := bstep (se 1 (by rfl) ⟨478148, by rfl⟩ : syracuseStep 637531 = 956297) B956297
theorem B637599 : Blo 634301 637599 := bstep (se 1 (by rfl) ⟨478199, by rfl⟩ : syracuseStep 637599 = 956399) B956399
theorem B637767 : Blo 634301 637767 := bstep (se 1 (by rfl) ⟨478325, by rfl⟩ : syracuseStep 637767 = 956651) B956651
theorem B5880667 : Blo 634301 5880667 := bstep (se 1 (by rfl) ⟨4410500, by rfl⟩ : syracuseStep 5880667 = 8821001) B8821001
theorem B637807 : Blo 634301 637807 := bstep (se 1 (by rfl) ⟨478355, by rfl⟩ : syracuseStep 637807 = 956711) B956711
theorem B637863 : Blo 634301 637863 := bstep (se 1 (by rfl) ⟨478397, by rfl⟩ : syracuseStep 637863 = 956795) B956795
theorem B3226715 : Blo 634301 3226715 := bstep (se 1 (by rfl) ⟨2420036, by rfl⟩ : syracuseStep 3226715 = 4840073) B4840073
theorem B638043 : Blo 634301 638043 := bstep (se 1 (by rfl) ⟨478532, by rfl⟩ : syracuseStep 638043 = 957065) B957065
theorem B638159 : Blo 634301 638159 := bstep (se 1 (by rfl) ⟨478619, by rfl⟩ : syracuseStep 638159 = 957239) B957239
theorem B1228007 : Blo 634301 1228007 := bstep (se 1 (by rfl) ⟨921005, by rfl⟩ : syracuseStep 1228007 = 1842011) B1842011
theorem B638183 : Blo 634301 638183 := bstep (se 1 (by rfl) ⟨478637, by rfl⟩ : syracuseStep 638183 = 957275) B957275
theorem B638279 : Blo 634301 638279 := bstep (se 1 (by rfl) ⟨478709, by rfl⟩ : syracuseStep 638279 = 957419) B957419
theorem B13745501 : Blo 634301 13745501 := bstep (se 3 (by rfl) ⟨2577281, by rfl⟩ : syracuseStep 13745501 = 5154563) B5154563
theorem B12238451 : Blo 634301 12238451 := bstep (se 1 (by rfl) ⟨9178838, by rfl⟩ : syracuseStep 12238451 = 18357677) B18357677
theorem B2146553 : Blo 634301 2146553 := bstep (se 2 (by rfl) ⟨804957, by rfl⟩ : syracuseStep 2146553 = 1609915) B1609915
theorem B3621307 : Blo 634301 3621307 := bstep (se 1 (by rfl) ⟨2715980, by rfl⟩ : syracuseStep 3621307 = 5431961) B5431961
theorem B4833755 : Blo 634301 4833755 := bstep (se 1 (by rfl) ⟨3625316, by rfl⟩ : syracuseStep 4833755 = 7250633) B7250633
theorem B2146823 : Blo 634301 2146823 := bstep (se 1 (by rfl) ⟨1610117, by rfl⟩ : syracuseStep 2146823 = 3220235) B3220235
theorem B2146931 : Blo 634301 2146931 := bstep (se 1 (by rfl) ⟨1610198, by rfl⟩ : syracuseStep 2146931 = 3220397) B3220397
theorem B2147201 : Blo 634301 2147201 := bstep (se 2 (by rfl) ⟨805200, by rfl⟩ : syracuseStep 2147201 = 1610401) B1610401
theorem B803783 : Blo 634301 803783 := bstep (se 1 (by rfl) ⟨602837, by rfl⟩ : syracuseStep 803783 = 1205675) B1205675
theorem B3228659 : Blo 634301 3228659 := bstep (se 1 (by rfl) ⟨2421494, by rfl⟩ : syracuseStep 3228659 = 4842989) B4842989
theorem B2409527 : Blo 634301 2409527 := bstep (se 1 (by rfl) ⟨1807145, by rfl⟩ : syracuseStep 2409527 = 3614291) B3614291
theorem B2442575 : Blo 634301 2442575 := bstep (se 1 (by rfl) ⟨1831931, by rfl⟩ : syracuseStep 2442575 = 3663863) B3663863
theorem B2147741 : Blo 634301 2147741 := bstep (se 3 (by rfl) ⟨402701, by rfl⟩ : syracuseStep 2147741 = 805403) B805403
theorem B1525279 : Blo 634301 1525279 := bstep (se 1 (by rfl) ⟨1143959, by rfl⟩ : syracuseStep 1525279 = 2287919) B2287919
theorem B2147903 : Blo 634301 2147903 := bstep (se 1 (by rfl) ⟨1610927, by rfl⟩ : syracuseStep 2147903 = 3221855) B3221855
theorem B2901671 : Blo 634301 2901671 := bstep (se 1 (by rfl) ⟨2176253, by rfl⟩ : syracuseStep 2901671 = 4352507) B4352507
theorem B2148011 : Blo 634301 2148011 := bstep (se 1 (by rfl) ⟨1611008, by rfl⟩ : syracuseStep 2148011 = 3222017) B3222017
theorem B1394671 : Blo 634301 1394671 := bstep (se 1 (by rfl) ⟨1046003, by rfl⟩ : syracuseStep 1394671 = 2092007) B2092007
theorem B1493147 : Blo 634301 1493147 := bstep (se 1 (by rfl) ⟨1119860, by rfl⟩ : syracuseStep 1493147 = 2239721) B2239721
theorem B2148551 : Blo 634301 2148551 := bstep (se 1 (by rfl) ⟨1611413, by rfl⟩ : syracuseStep 2148551 = 3222827) B3222827
theorem B3230279 : Blo 634301 3230279 := bstep (se 1 (by rfl) ⟨2422709, by rfl⟩ : syracuseStep 3230279 = 4845419) B4845419
theorem B2149145 : Blo 634301 2149145 := bstep (se 2 (by rfl) ⟨805929, by rfl⟩ : syracuseStep 2149145 = 1611859) B1611859
theorem B1428263 : Blo 634301 1428263 := bstep (se 1 (by rfl) ⟨1071197, by rfl⟩ : syracuseStep 1428263 = 2142395) B2142395
theorem B3623723 : Blo 634301 3623723 := bstep (se 1 (by rfl) ⟨2717792, by rfl⟩ : syracuseStep 3623723 = 5435585) B5435585
theorem B1526779 : Blo 634301 1526779 := bstep (se 1 (by rfl) ⟨1145084, by rfl⟩ : syracuseStep 1526779 = 2290169) B2290169
theorem B1428587 : Blo 634301 1428587 := bstep (se 1 (by rfl) ⟨1071440, by rfl⟩ : syracuseStep 1428587 = 2142881) B2142881
theorem B2149523 : Blo 634301 2149523 := bstep (se 1 (by rfl) ⟨1612142, by rfl⟩ : syracuseStep 2149523 = 3224285) B3224285
theorem B9096425 : Blo 634301 9096425 := bstep (se 2 (by rfl) ⟨3411159, by rfl⟩ : syracuseStep 9096425 = 6822319) B6822319
theorem B1428857 : Blo 634301 1428857 := bstep (se 2 (by rfl) ⟨535821, by rfl⟩ : syracuseStep 1428857 = 1071643) B1071643
theorem B2149793 : Blo 634301 2149793 := bstep (se 2 (by rfl) ⟨806172, by rfl⟩ : syracuseStep 2149793 = 1612345) B1612345
theorem B1429163 : Blo 634301 1429163 := bstep (se 1 (by rfl) ⟨1071872, by rfl⟩ : syracuseStep 1429163 = 2143745) B2143745
theorem B2412443 : Blo 634301 2412443 := bstep (se 1 (by rfl) ⟨1809332, by rfl⟩ : syracuseStep 2412443 = 3618665) B3618665
theorem B2150333 : Blo 634301 2150333 := bstep (se 3 (by rfl) ⟨403187, by rfl⟩ : syracuseStep 2150333 = 806375) B806375
theorem B1429487 : Blo 634301 1429487 := bstep (se 1 (by rfl) ⟨1072115, by rfl⟩ : syracuseStep 1429487 = 2144231) B2144231
theorem B22073357 : Blo 634301 22073357 := bstep (se 3 (by rfl) ⟨4138754, by rfl⟩ : syracuseStep 22073357 = 8277509) B8277509
theorem B1429559 : Blo 634301 1429559 := bstep (se 1 (by rfl) ⟨1072169, by rfl⟩ : syracuseStep 1429559 = 2144339) B2144339
theorem B2150495 : Blo 634301 2150495 := bstep (se 1 (by rfl) ⟨1612871, by rfl⟩ : syracuseStep 2150495 = 3225743) B3225743
theorem B1724591 : Blo 634301 1724591 := bstep (se 1 (by rfl) ⟨1293443, by rfl⟩ : syracuseStep 1724591 = 2586887) B2586887
theorem B1429703 : Blo 634301 1429703 := bstep (se 1 (by rfl) ⟨1072277, by rfl⟩ : syracuseStep 1429703 = 2144555) B2144555
theorem B6115571 : Blo 634301 6115571 := bstep (se 1 (by rfl) ⟨4586678, by rfl⟩ : syracuseStep 6115571 = 9173357) B9173357
theorem B1429883 : Blo 634301 1429883 := bstep (se 1 (by rfl) ⟨1072412, by rfl⟩ : syracuseStep 1429883 = 2144825) B2144825
theorem B5820929 : Blo 634301 5820929 := bstep (se 2 (by rfl) ⟨2182848, by rfl⟩ : syracuseStep 5820929 = 4365697) B4365697
theorem B1430153 : Blo 634301 1430153 := bstep (se 2 (by rfl) ⟨536307, by rfl⟩ : syracuseStep 1430153 = 1072615) B1072615
theorem B1725065 : Blo 634301 1725065 := bstep (se 2 (by rfl) ⟨646899, by rfl⟩ : syracuseStep 1725065 = 1293799) B1293799
theorem B1430891 : Blo 634301 1430891 := bstep (se 1 (by rfl) ⟨1073168, by rfl⟩ : syracuseStep 1430891 = 2146337) B2146337
theorem B9786743 : Blo 634301 9786743 := bstep (se 1 (by rfl) ⟨7340057, by rfl⟩ : syracuseStep 9786743 = 14680115) B14680115
theorem B1431161 : Blo 634301 1431161 := bstep (se 2 (by rfl) ⟨536685, by rfl⟩ : syracuseStep 1431161 = 1073371) B1073371
theorem B2152223 : Blo 634301 2152223 := bstep (se 1 (by rfl) ⟨1614167, by rfl⟩ : syracuseStep 2152223 = 3228335) B3228335
theorem B2414555 : Blo 634301 2414555 := bstep (se 1 (by rfl) ⟨1810916, by rfl⟩ : syracuseStep 2414555 = 3621833) B3621833
theorem B1431521 : Blo 634301 1431521 := bstep (se 2 (by rfl) ⟨536820, by rfl⟩ : syracuseStep 1431521 = 1073641) B1073641
theorem B6510905 : Blo 634301 6510905 := bstep (se 2 (by rfl) ⟨2441589, by rfl⟩ : syracuseStep 6510905 = 4883179) B4883179
theorem B6871675 : Blo 634301 6871675 := bstep (se 1 (by rfl) ⟨5153756, by rfl⟩ : syracuseStep 6871675 = 10307513) B10307513
theorem B7265213 : Blo 634301 7265213 := bstep (se 3 (by rfl) ⟨1362227, by rfl⟩ : syracuseStep 7265213 = 2724455) B2724455
theorem B5791085 : Blo 634301 5791085 := bstep (se 3 (by rfl) ⟨1085828, by rfl⟩ : syracuseStep 5791085 = 2171657) B2171657
theorem B18341639 : Blo 634301 18341639 := bstep (se 1 (by rfl) ⟨13756229, by rfl⟩ : syracuseStep 18341639 = 27512459) B27512459
theorem B1433375 : Blo 634301 1433375 := bstep (se 1 (by rfl) ⟨1075031, by rfl⟩ : syracuseStep 1433375 = 2150063) B2150063
theorem B100228913 : Blo 634301 100228913 := bstep (se 2 (by rfl) ⟨37585842, by rfl⟩ : syracuseStep 100228913 = 75171685) B75171685
theorem B1531891 : Blo 634301 1531891 := bstep (se 1 (by rfl) ⟨1148918, by rfl⟩ : syracuseStep 1531891 = 2297837) B2297837
theorem B1433591 : Blo 634301 1433591 := bstep (se 1 (by rfl) ⟨1075193, by rfl⟩ : syracuseStep 1433591 = 2150387) B2150387
theorem B44130365 : Blo 634301 44130365 := bstep (se 3 (by rfl) ⟨8274443, by rfl⟩ : syracuseStep 44130365 = 16548887) B16548887
theorem B2416787 : Blo 634301 2416787 := bstep (se 1 (by rfl) ⟨1812590, by rfl⟩ : syracuseStep 2416787 = 3625181) B3625181
theorem B1433807 : Blo 634301 1433807 := bstep (se 1 (by rfl) ⟨1075355, by rfl⟩ : syracuseStep 1433807 = 2150711) B2150711
theorem B1433951 : Blo 634301 1433951 := bstep (se 1 (by rfl) ⟨1075463, by rfl⟩ : syracuseStep 1433951 = 2150927) B2150927
theorem B13034033 : Blo 634301 13034033 := bstep (se 2 (by rfl) ⟨4887762, by rfl⟩ : syracuseStep 13034033 = 9775525) B9775525
theorem B2286247 : Blo 634301 2286247 := bstep (se 1 (by rfl) ⟨1714685, by rfl⟩ : syracuseStep 2286247 = 3429371) B3429371
theorem B13100039 : Blo 634301 13100039 := bstep (se 1 (by rfl) ⟨9825029, by rfl⟩ : syracuseStep 13100039 = 19650059) B19650059
theorem B1434671 : Blo 634301 1434671 := bstep (se 1 (by rfl) ⟨1076003, by rfl⟩ : syracuseStep 1434671 = 2152007) B2152007
theorem B713839 : Blo 634301 713839 := bstep (se 1 (by rfl) ⟨535379, by rfl⟩ : syracuseStep 713839 = 1070759) B1070759
theorem B1074343 : Blo 634301 1074343 := bstep (se 1 (by rfl) ⟨805757, by rfl⟩ : syracuseStep 1074343 = 1611515) B1611515
theorem B39216419 : Blo 634301 39216419 := bstep (se 1 (by rfl) ⟨29412314, by rfl⟩ : syracuseStep 39216419 = 58824629) B58824629
theorem B1467895 : Blo 634301 1467895 := bstep (se 1 (by rfl) ⟨1100921, by rfl⟩ : syracuseStep 1467895 = 2201843) B2201843
theorem B714271 : Blo 634301 714271 := bstep (se 1 (by rfl) ⟨535703, by rfl⟩ : syracuseStep 714271 = 1071407) B1071407
theorem B1435319 : Blo 634301 1435319 := bstep (se 1 (by rfl) ⟨1076489, by rfl⟩ : syracuseStep 1435319 = 2152979) B2152979
theorem B1959659 : Blo 634301 1959659 := bstep (se 1 (by rfl) ⟨1469744, by rfl⟩ : syracuseStep 1959659 = 2939489) B2939489
theorem B26109773 : Blo 634301 26109773 := bstep (se 3 (by rfl) ⟨4895582, by rfl⟩ : syracuseStep 26109773 = 9791165) B9791165
theorem B1075099 : Blo 634301 1075099 := bstep (se 1 (by rfl) ⟨806324, by rfl⟩ : syracuseStep 1075099 = 1612649) B1612649
theorem B3631013 : Blo 634301 3631013 := bstep (se 4 (by rfl) ⟨340407, by rfl⟩ : syracuseStep 3631013 = 680815) B680815
theorem B1435769 : Blo 634301 1435769 := bstep (se 2 (by rfl) ⟨538413, by rfl⟩ : syracuseStep 1435769 = 1076827) B1076827
theorem B1075511 : Blo 634301 1075511 := bstep (se 1 (by rfl) ⟨806633, by rfl⟩ : syracuseStep 1075511 = 1613267) B1613267
theorem B715135 : Blo 634301 715135 := bstep (se 1 (by rfl) ⟨536351, by rfl⟩ : syracuseStep 715135 = 1072703) B1072703
theorem B2419247 : Blo 634301 2419247 := bstep (se 1 (by rfl) ⟨1814435, by rfl⟩ : syracuseStep 2419247 = 3628871) B3628871
theorem B23194957 : Blo 634301 23194957 := bstep (se 3 (by rfl) ⟨4349054, by rfl⟩ : syracuseStep 23194957 = 8698109) B8698109
theorem B2420219 : Blo 634301 2420219 := bstep (se 1 (by rfl) ⟨1815164, by rfl⟩ : syracuseStep 2420219 = 3630329) B3630329
theorem B5434937 : Blo 634301 5434937 := bstep (se 2 (by rfl) ⟨2038101, by rfl⟩ : syracuseStep 5434937 = 4076203) B4076203
theorem B2059847 : Blo 634301 2059847 := bstep (se 1 (by rfl) ⟨1544885, by rfl⟩ : syracuseStep 2059847 = 3089771) B3089771
theorem B1076807 : Blo 634301 1076807 := bstep (se 1 (by rfl) ⟨807605, by rfl⟩ : syracuseStep 1076807 = 1615211) B1615211
theorem B716539 : Blo 634301 716539 := bstep (se 1 (by rfl) ⟨537404, by rfl⟩ : syracuseStep 716539 = 1074809) B1074809
theorem B716863 : Blo 634301 716863 := bstep (se 1 (by rfl) ⟨537647, by rfl⟩ : syracuseStep 716863 = 1075295) B1075295
theorem B2421647 : Blo 634301 2421647 := bstep (se 1 (by rfl) ⟨1816235, by rfl⟩ : syracuseStep 2421647 = 3632471) B3632471
theorem B717727 : Blo 634301 717727 := bstep (se 1 (by rfl) ⟨538295, by rfl⟩ : syracuseStep 717727 = 1076591) B1076591
theorem B717979 : Blo 634301 717979 := bstep (se 1 (by rfl) ⟨538484, by rfl⟩ : syracuseStep 717979 = 1076969) B1076969
theorem B1210079 : Blo 634301 1210079 := bstep (se 1 (by rfl) ⟨907559, by rfl⟩ : syracuseStep 1210079 = 1815119) B1815119
theorem B11138795 : Blo 634301 11138795 := bstep (se 1 (by rfl) ⟨8354096, by rfl⟩ : syracuseStep 11138795 = 16708193) B16708193
theorem B10483991 : Blo 634301 10483991 := bstep (se 1 (by rfl) ⟨7862993, by rfl⟩ : syracuseStep 10483991 = 15725987) B15725987
theorem B6289883 : Blo 634301 6289883 := bstep (se 1 (by rfl) ⟨4717412, by rfl⟩ : syracuseStep 6289883 = 9434825) B9434825
theorem B2718305 : Blo 634301 2718305 := bstep (se 2 (by rfl) ⟨1019364, by rfl⟩ : syracuseStep 2718305 = 2038729) B2038729
theorem B1211105 : Blo 634301 1211105 := bstep (se 2 (by rfl) ⟨454164, by rfl⟩ : syracuseStep 1211105 = 908329) B908329
theorem B8158603 : Blo 634301 8158603 := bstep (se 1 (by rfl) ⟨6118952, by rfl⟩ : syracuseStep 8158603 = 12237905) B12237905
theorem B9273041 : Blo 634301 9273041 := bstep (se 2 (by rfl) ⟨3477390, by rfl⟩ : syracuseStep 9273041 = 6954781) B6954781
theorem B5439959 : Blo 634301 5439959 := bstep (se 1 (by rfl) ⟨4079969, by rfl⟩ : syracuseStep 5439959 = 8159939) B8159939
theorem B1606351 : Blo 634301 1606351 := bstep (se 1 (by rfl) ⟨1204763, by rfl⟩ : syracuseStep 1606351 = 2409527) B2409527
theorem B3048329 : Blo 634301 3048329 := bstep (se 2 (by rfl) ⟨1143123, by rfl⟩ : syracuseStep 3048329 = 2286247) B2286247
theorem B1934447 : Blo 634301 1934447 := bstep (se 1 (by rfl) ⟨1450835, by rfl⟩ : syracuseStep 1934447 = 2901671) B2901671
theorem B951785 : Blo 634301 951785 := bstep (se 2 (by rfl) ⟨356919, by rfl⟩ : syracuseStep 951785 = 713839) B713839
theorem B4064849 : Blo 634301 4064849 := bstep (se 2 (by rfl) ⟨1524318, by rfl⟩ : syracuseStep 4064849 = 3048637) B3048637
theorem B2033387 : Blo 634301 2033387 := bstep (se 1 (by rfl) ⟨1525040, by rfl⟩ : syracuseStep 2033387 = 3050081) B3050081
theorem B3540743 : Blo 634301 3540743 := bstep (se 1 (by rfl) ⟨2655557, by rfl⟩ : syracuseStep 3540743 = 5311115) B5311115
theorem B952175 : Blo 634301 952175 := bstep (se 1 (by rfl) ⟨714131, by rfl⟩ : syracuseStep 952175 = 1428263) B1428263
theorem B9177047 : Blo 634301 9177047 := bstep (se 1 (by rfl) ⟨6882785, by rfl⟩ : syracuseStep 9177047 = 13765571) B13765571
theorem B2033705 : Blo 634301 2033705 := bstep (se 2 (by rfl) ⟨762639, by rfl⟩ : syracuseStep 2033705 = 1525279) B1525279
theorem B952361 : Blo 634301 952361 := bstep (se 2 (by rfl) ⟨357135, by rfl⟩ : syracuseStep 952361 = 714271) B714271
theorem B952391 : Blo 634301 952391 := bstep (se 1 (by rfl) ⟨714293, by rfl⟩ : syracuseStep 952391 = 1428587) B1428587
theorem B17434763 : Blo 634301 17434763 := bstep (se 1 (by rfl) ⟨13076072, by rfl⟩ : syracuseStep 17434763 = 26152145) B26152145
theorem B6064283 : Blo 634301 6064283 := bstep (se 1 (by rfl) ⟨4548212, by rfl⟩ : syracuseStep 6064283 = 9096425) B9096425
theorem B952571 : Blo 634301 952571 := bstep (se 1 (by rfl) ⟨714428, by rfl⟩ : syracuseStep 952571 = 1428857) B1428857
theorem B952775 : Blo 634301 952775 := bstep (se 1 (by rfl) ⟨714581, by rfl⟩ : syracuseStep 952775 = 1429163) B1429163
theorem B11602439 : Blo 634301 11602439 := bstep (se 1 (by rfl) ⟨8701829, by rfl⟩ : syracuseStep 11602439 = 17403659) B17403659
theorem B1608295 : Blo 634301 1608295 := bstep (se 1 (by rfl) ⟨1206221, by rfl⟩ : syracuseStep 1608295 = 2412443) B2412443
theorem B952991 : Blo 634301 952991 := bstep (se 1 (by rfl) ⟨714743, by rfl⟩ : syracuseStep 952991 = 1429487) B1429487
theorem B953039 : Blo 634301 953039 := bstep (se 1 (by rfl) ⟨714779, by rfl⟩ : syracuseStep 953039 = 1429559) B1429559
theorem B1149727 : Blo 634301 1149727 := bstep (se 1 (by rfl) ⟨862295, by rfl⟩ : syracuseStep 1149727 = 1724591) B1724591
theorem B953135 : Blo 634301 953135 := bstep (se 1 (by rfl) ⟨714851, by rfl⟩ : syracuseStep 953135 = 1429703) B1429703
theorem B953255 : Blo 634301 953255 := bstep (se 1 (by rfl) ⟨714941, by rfl⟩ : syracuseStep 953255 = 1429883) B1429883
theorem B953435 : Blo 634301 953435 := bstep (se 1 (by rfl) ⟨715076, by rfl⟩ : syracuseStep 953435 = 1430153) B1430153
theorem B1150043 : Blo 634301 1150043 := bstep (se 1 (by rfl) ⟨862532, by rfl⟩ : syracuseStep 1150043 = 1725065) B1725065
theorem B953513 : Blo 634301 953513 := bstep (se 2 (by rfl) ⟨357567, by rfl⟩ : syracuseStep 953513 = 715135) B715135
theorem B953927 : Blo 634301 953927 := bstep (se 1 (by rfl) ⟨715445, by rfl⟩ : syracuseStep 953927 = 1430891) B1430891
theorem B6524495 : Blo 634301 6524495 := bstep (se 1 (by rfl) ⟨4893371, by rfl⟩ : syracuseStep 6524495 = 9786743) B9786743
theorem B3215051 : Blo 634301 3215051 := bstep (se 1 (by rfl) ⟨2411288, by rfl⟩ : syracuseStep 3215051 = 4822577) B4822577
theorem B954107 : Blo 634301 954107 := bstep (se 1 (by rfl) ⟨715580, by rfl⟩ : syracuseStep 954107 = 1431161) B1431161
theorem B1609703 : Blo 634301 1609703 := bstep (se 1 (by rfl) ⟨1207277, by rfl⟩ : syracuseStep 1609703 = 2414555) B2414555
theorem B954347 : Blo 634301 954347 := bstep (se 1 (by rfl) ⟨715760, by rfl⟩ : syracuseStep 954347 = 1431521) B1431521
theorem B2035705 : Blo 634301 2035705 := bstep (se 2 (by rfl) ⟨763389, by rfl⟩ : syracuseStep 2035705 = 1526779) B1526779
theorem B955385 : Blo 634301 955385 := bstep (se 2 (by rfl) ⟨358269, by rfl⟩ : syracuseStep 955385 = 716539) B716539
theorem B12227759 : Blo 634301 12227759 := bstep (se 1 (by rfl) ⟨9170819, by rfl⟩ : syracuseStep 12227759 = 18341639) B18341639
theorem B955583 : Blo 634301 955583 := bstep (se 1 (by rfl) ⟨716687, by rfl⟩ : syracuseStep 955583 = 1433375) B1433375
theorem B66819275 : Blo 634301 66819275 := bstep (se 1 (by rfl) ⟨50114456, by rfl⟩ : syracuseStep 66819275 = 100228913) B100228913
theorem B955727 : Blo 634301 955727 := bstep (se 1 (by rfl) ⟨716795, by rfl⟩ : syracuseStep 955727 = 1433591) B1433591
theorem B1840463 : Blo 634301 1840463 := bstep (se 1 (by rfl) ⟨1380347, by rfl⟩ : syracuseStep 1840463 = 2760695) B2760695
theorem B955817 : Blo 634301 955817 := bstep (se 2 (by rfl) ⟨358431, by rfl⟩ : syracuseStep 955817 = 716863) B716863
theorem B1611191 : Blo 634301 1611191 := bstep (se 1 (by rfl) ⟨1208393, by rfl⟩ : syracuseStep 1611191 = 2416787) B2416787
theorem B955871 : Blo 634301 955871 := bstep (se 1 (by rfl) ⟨716903, by rfl⟩ : syracuseStep 955871 = 1433807) B1433807
theorem B955967 : Blo 634301 955967 := bstep (se 1 (by rfl) ⟨716975, by rfl⟩ : syracuseStep 955967 = 1433951) B1433951
theorem B8689355 : Blo 634301 8689355 := bstep (se 1 (by rfl) ⟨6517016, by rfl⟩ : syracuseStep 8689355 = 13034033) B13034033
theorem B8132359 : Blo 634301 8132359 := bstep (se 1 (by rfl) ⟨6099269, by rfl⟩ : syracuseStep 8132359 = 12198539) B12198539
theorem B13735817 : Blo 634301 13735817 := bstep (se 2 (by rfl) ⟨5150931, by rfl⟩ : syracuseStep 13735817 = 10301863) B10301863
theorem B956447 : Blo 634301 956447 := bstep (se 1 (by rfl) ⟨717335, by rfl⟩ : syracuseStep 956447 = 1434671) B1434671
theorem B956879 : Blo 634301 956879 := bstep (se 1 (by rfl) ⟨717659, by rfl⟩ : syracuseStep 956879 = 1435319) B1435319
theorem B956969 : Blo 634301 956969 := bstep (se 2 (by rfl) ⟨358863, by rfl⟩ : syracuseStep 956969 = 717727) B717727
theorem B17406515 : Blo 634301 17406515 := bstep (se 1 (by rfl) ⟨13054886, by rfl⟩ : syracuseStep 17406515 = 26109773) B26109773
theorem B957179 : Blo 634301 957179 := bstep (se 1 (by rfl) ⟨717884, by rfl⟩ : syracuseStep 957179 = 1435769) B1435769
theorem B957305 : Blo 634301 957305 := bstep (se 2 (by rfl) ⟨358989, by rfl⟩ : syracuseStep 957305 = 717979) B717979
theorem B1612831 : Blo 634301 1612831 := bstep (se 1 (by rfl) ⟨1209623, by rfl⟩ : syracuseStep 1612831 = 2419247) B2419247
theorem B3218615 : Blo 634301 3218615 := bstep (se 1 (by rfl) ⟨2413961, by rfl⟩ : syracuseStep 3218615 = 4827923) B4827923
theorem B1613479 : Blo 634301 1613479 := bstep (se 1 (by rfl) ⟨1210109, by rfl⟩ : syracuseStep 1613479 = 2420219) B2420219
theorem B1810745 : Blo 634301 1810745 := bstep (se 2 (by rfl) ⟨679029, by rfl⟩ : syracuseStep 1810745 = 1358059) B1358059
theorem B5448059 : Blo 634301 5448059 := bstep (se 1 (by rfl) ⟨4086044, by rfl⟩ : syracuseStep 5448059 = 8172089) B8172089
theorem B2040191 : Blo 634301 2040191 := bstep (se 1 (by rfl) ⟨1530143, by rfl⟩ : syracuseStep 2040191 = 3060287) B3060287
theorem B1614431 : Blo 634301 1614431 := bstep (se 1 (by rfl) ⟨1210823, by rfl⟩ : syracuseStep 1614431 = 2421647) B2421647
theorem B6104159 : Blo 634301 6104159 := bstep (se 1 (by rfl) ⟨4578119, by rfl⟩ : syracuseStep 6104159 = 9156239) B9156239
theorem B7840889 : Blo 634301 7840889 := bstep (se 2 (by rfl) ⟨2940333, by rfl⟩ : syracuseStep 7840889 = 5880667) B5880667
theorem B3482911 : Blo 634301 3482911 := bstep (se 1 (by rfl) ⟨2612183, by rfl⟩ : syracuseStep 3482911 = 5224367) B5224367
theorem B6989327 : Blo 634301 6989327 := bstep (se 1 (by rfl) ⟨5241995, by rfl⟩ : syracuseStep 6989327 = 10483991) B10483991
theorem B1812203 : Blo 634301 1812203 := bstep (se 1 (by rfl) ⟨1359152, by rfl⟩ : syracuseStep 1812203 = 2718305) B2718305
theorem B8170085 : Blo 634301 8170085 := bstep (se 4 (by rfl) ⟨765945, by rfl⟩ : syracuseStep 8170085 = 1531891) B1531891
theorem B58862285 : Blo 634301 58862285 := bstep (se 3 (by rfl) ⟨11036678, by rfl⟩ : syracuseStep 58862285 = 22073357) B22073357
theorem B3222503 : Blo 634301 3222503 := bstep (se 1 (by rfl) ⟨2416877, by rfl⟩ : syracuseStep 3222503 = 4833755) B4833755
theorem B4828409 : Blo 634301 4828409 := bstep (se 2 (by rfl) ⟨1810653, by rfl⟩ : syracuseStep 4828409 = 3621307) B3621307
theorem B1813843 : Blo 634301 1813843 := bstep (se 1 (by rfl) ⟨1360382, by rfl⟩ : syracuseStep 1813843 = 2720765) B2720765
theorem B634399 : Blo 634301 634399 := bstep (se 1 (by rfl) ⟨475799, by rfl⟩ : syracuseStep 634399 = 951599) B951599
theorem B634535 : Blo 634301 634535 := bstep (se 1 (by rfl) ⟨475901, by rfl⟩ : syracuseStep 634535 = 951803) B951803
theorem B634559 : Blo 634301 634559 := bstep (se 1 (by rfl) ⟨475919, by rfl⟩ : syracuseStep 634559 = 951839) B951839
theorem B634655 : Blo 634301 634655 := bstep (se 1 (by rfl) ⟨475991, by rfl⟩ : syracuseStep 634655 = 951983) B951983
theorem B634735 : Blo 634301 634735 := bstep (se 1 (by rfl) ⟨476051, by rfl⟩ : syracuseStep 634735 = 952103) B952103
theorem B995431 : Blo 634301 995431 := bstep (se 1 (by rfl) ⟨746573, by rfl⟩ : syracuseStep 995431 = 1493147) B1493147
theorem B635103 : Blo 634301 635103 := bstep (se 1 (by rfl) ⟨476327, by rfl⟩ : syracuseStep 635103 = 952655) B952655
theorem B635135 : Blo 634301 635135 := bstep (se 1 (by rfl) ⟨476351, by rfl⟩ : syracuseStep 635135 = 952703) B952703
theorem B635163 : Blo 634301 635163 := bstep (se 1 (by rfl) ⟨476372, by rfl⟩ : syracuseStep 635163 = 952745) B952745
theorem B9154903 : Blo 634301 9154903 := bstep (se 1 (by rfl) ⟨6866177, by rfl⟩ : syracuseStep 9154903 = 13732355) B13732355
theorem B635419 : Blo 634301 635419 := bstep (se 1 (by rfl) ⟨476564, by rfl⟩ : syracuseStep 635419 = 953129) B953129
theorem B635559 : Blo 634301 635559 := bstep (se 1 (by rfl) ⟨476669, by rfl⟩ : syracuseStep 635559 = 953339) B953339
theorem B635599 : Blo 634301 635599 := bstep (se 1 (by rfl) ⟨476699, by rfl⟩ : syracuseStep 635599 = 953399) B953399
theorem B1717001 : Blo 634301 1717001 := bstep (se 2 (by rfl) ⟨643875, by rfl⟩ : syracuseStep 1717001 = 1287751) B1287751
theorem B635679 : Blo 634301 635679 := bstep (se 1 (by rfl) ⟨476759, by rfl⟩ : syracuseStep 635679 = 953519) B953519
theorem B2143421 : Blo 634301 2143421 := bstep (se 3 (by rfl) ⟨401891, by rfl⟩ : syracuseStep 2143421 = 803783) B803783
theorem B636159 : Blo 634301 636159 := bstep (se 1 (by rfl) ⟨477119, by rfl⟩ : syracuseStep 636159 = 954239) B954239
theorem B1815871 : Blo 634301 1815871 := bstep (se 1 (by rfl) ⟨1361903, by rfl⟩ : syracuseStep 1815871 = 2723807) B2723807
theorem B636287 : Blo 634301 636287 := bstep (se 1 (by rfl) ⟨477215, by rfl⟩ : syracuseStep 636287 = 954431) B954431
theorem B1357231 : Blo 634301 1357231 := bstep (se 1 (by rfl) ⟨1017923, by rfl⟩ : syracuseStep 1357231 = 2035847) B2035847
theorem B4077047 : Blo 634301 4077047 := bstep (se 1 (by rfl) ⟨3057785, by rfl⟩ : syracuseStep 4077047 = 6115571) B6115571
theorem B636443 : Blo 634301 636443 := bstep (se 1 (by rfl) ⟨477332, by rfl⟩ : syracuseStep 636443 = 954665) B954665
theorem B3880619 : Blo 634301 3880619 := bstep (se 1 (by rfl) ⟨2910464, by rfl⟩ : syracuseStep 3880619 = 5820929) B5820929
theorem B636623 : Blo 634301 636623 := bstep (se 1 (by rfl) ⟨477467, by rfl⟩ : syracuseStep 636623 = 954935) B954935
theorem B2144123 : Blo 634301 2144123 := bstep (se 1 (by rfl) ⟨1608092, by rfl⟩ : syracuseStep 2144123 = 3216185) B3216185
theorem B636863 : Blo 634301 636863 := bstep (se 1 (by rfl) ⟨477647, by rfl⟩ : syracuseStep 636863 = 955295) B955295
theorem B636991 : Blo 634301 636991 := bstep (se 1 (by rfl) ⟨477743, by rfl⟩ : syracuseStep 636991 = 955487) B955487
theorem B637031 : Blo 634301 637031 := bstep (se 1 (by rfl) ⟨477773, by rfl⟩ : syracuseStep 637031 = 955547) B955547
theorem B1816759 : Blo 634301 1816759 := bstep (se 1 (by rfl) ⟨1362569, by rfl⟩ : syracuseStep 1816759 = 2725139) B2725139
theorem B637487 : Blo 634301 637487 := bstep (se 1 (by rfl) ⟨478115, by rfl⟩ : syracuseStep 637487 = 956231) B956231
theorem B4340603 : Blo 634301 4340603 := bstep (se 1 (by rfl) ⟨3255452, by rfl⟩ : syracuseStep 4340603 = 6510905) B6510905
theorem B637887 : Blo 634301 637887 := bstep (se 1 (by rfl) ⟨478415, by rfl⟩ : syracuseStep 637887 = 956831) B956831
theorem B637935 : Blo 634301 637935 := bstep (se 1 (by rfl) ⟨478451, by rfl⟩ : syracuseStep 637935 = 956903) B956903
theorem B3226877 : Blo 634301 3226877 := bstep (se 3 (by rfl) ⟨605039, by rfl⟩ : syracuseStep 3226877 = 1210079) B1210079
theorem B5520905 : Blo 634301 5520905 := bstep (se 2 (by rfl) ⟨2070339, by rfl⟩ : syracuseStep 5520905 = 4140679) B4140679
theorem B2146607 : Blo 634301 2146607 := bstep (se 1 (by rfl) ⟨1609955, by rfl⟩ : syracuseStep 2146607 = 3219911) B3219911
theorem B2409041 : Blo 634301 2409041 := bstep (se 2 (by rfl) ⟨903390, by rfl⟩ : syracuseStep 2409041 = 1806781) B1806781
theorem B8733359 : Blo 634301 8733359 := bstep (se 1 (by rfl) ⟨6550019, by rfl⟩ : syracuseStep 8733359 = 13100039) B13100039
theorem B2409223 : Blo 634301 2409223 := bstep (se 1 (by rfl) ⟨1806917, by rfl⟩ : syracuseStep 2409223 = 3613835) B3613835
theorem B2147687 : Blo 634301 2147687 := bstep (se 1 (by rfl) ⟨1610765, by rfl⟩ : syracuseStep 2147687 = 3221531) B3221531
theorem B2148065 : Blo 634301 2148065 := bstep (se 2 (by rfl) ⟨805524, by rfl⟩ : syracuseStep 2148065 = 1611049) B1611049
theorem B1361947 : Blo 634301 1361947 := bstep (se 1 (by rfl) ⟨1021460, by rfl⟩ : syracuseStep 1361947 = 2042921) B2042921
theorem B3623291 : Blo 634301 3623291 := bstep (se 1 (by rfl) ⟨2717468, by rfl⟩ : syracuseStep 3623291 = 5434937) B5434937
theorem B5425811 : Blo 634301 5425811 := bstep (se 1 (by rfl) ⟨4069358, by rfl⟩ : syracuseStep 5425811 = 8138717) B8138717
theorem B1428551 : Blo 634301 1428551 := bstep (se 1 (by rfl) ⟨1071413, by rfl⟩ : syracuseStep 1428551 = 2142827) B2142827
theorem B904655 : Blo 634301 904655 := bstep (se 1 (by rfl) ⟨678491, by rfl⟩ : syracuseStep 904655 = 1356983) B1356983
theorem B9162233 : Blo 634301 9162233 := bstep (se 2 (by rfl) ⟨3435837, by rfl⟩ : syracuseStep 9162233 = 6871675) B6871675
theorem B970471 : Blo 634301 970471 := bstep (se 1 (by rfl) ⟨727853, by rfl⟩ : syracuseStep 970471 = 1455707) B1455707
theorem B7425863 : Blo 634301 7425863 := bstep (se 1 (by rfl) ⟨5569397, by rfl⟩ : syracuseStep 7425863 = 11138795) B11138795
theorem B13094783 : Blo 634301 13094783 := bstep (se 1 (by rfl) ⟨9821087, by rfl⟩ : syracuseStep 13094783 = 19642175) B19642175
theorem B1429631 : Blo 634301 1429631 := bstep (se 1 (by rfl) ⟨1072223, by rfl⟩ : syracuseStep 1429631 = 2144447) B2144447
theorem B807403 : Blo 634301 807403 := bstep (se 1 (by rfl) ⟨605552, by rfl⟩ : syracuseStep 807403 = 1211105) B1211105
theorem B2151143 : Blo 634301 2151143 := bstep (se 1 (by rfl) ⟨1613357, by rfl⟩ : syracuseStep 2151143 = 3226715) B3226715
theorem B9163667 : Blo 634301 9163667 := bstep (se 1 (by rfl) ⟨6872750, by rfl⟩ : syracuseStep 9163667 = 13745501) B13745501
theorem B6182027 : Blo 634301 6182027 := bstep (se 1 (by rfl) ⟨4636520, by rfl⟩ : syracuseStep 6182027 = 9273041) B9273041
theorem B1431035 : Blo 634301 1431035 := bstep (se 1 (by rfl) ⟨1073276, by rfl⟩ : syracuseStep 1431035 = 2146553) B2146553
theorem B1431215 : Blo 634301 1431215 := bstep (se 1 (by rfl) ⟨1073411, by rfl⟩ : syracuseStep 1431215 = 2146823) B2146823
theorem B1431287 : Blo 634301 1431287 := bstep (se 1 (by rfl) ⟨1073465, by rfl⟩ : syracuseStep 1431287 = 2146931) B2146931
theorem B1431467 : Blo 634301 1431467 := bstep (se 1 (by rfl) ⟨1073600, by rfl⟩ : syracuseStep 1431467 = 2147201) B2147201
theorem B2152439 : Blo 634301 2152439 := bstep (se 1 (by rfl) ⟨1614329, by rfl⟩ : syracuseStep 2152439 = 3228659) B3228659
theorem B1628383 : Blo 634301 1628383 := bstep (se 1 (by rfl) ⟨1221287, by rfl⟩ : syracuseStep 1628383 = 2442575) B2442575
theorem B1431827 : Blo 634301 1431827 := bstep (se 1 (by rfl) ⟨1073870, by rfl⟩ : syracuseStep 1431827 = 2147741) B2147741
theorem B1431935 : Blo 634301 1431935 := bstep (se 1 (by rfl) ⟨1073951, by rfl⟩ : syracuseStep 1431935 = 2147903) B2147903
theorem B1071515 : Blo 634301 1071515 := bstep (se 1 (by rfl) ⟨803636, by rfl⟩ : syracuseStep 1071515 = 1607273) B1607273
theorem B1432007 : Blo 634301 1432007 := bstep (se 1 (by rfl) ⟨1074005, by rfl⟩ : syracuseStep 1432007 = 2148011) B2148011
theorem B1432367 : Blo 634301 1432367 := bstep (se 1 (by rfl) ⟨1074275, by rfl⟩ : syracuseStep 1432367 = 2148551) B2148551
theorem B1432457 : Blo 634301 1432457 := bstep (se 2 (by rfl) ⟨537171, by rfl⟩ : syracuseStep 1432457 = 1074343) B1074343
theorem B2153519 : Blo 634301 2153519 := bstep (se 1 (by rfl) ⟨1615139, by rfl⟩ : syracuseStep 2153519 = 3230279) B3230279
theorem B2710685 : Blo 634301 2710685 := bstep (se 3 (by rfl) ⟨508253, by rfl⟩ : syracuseStep 2710685 = 1016507) B1016507
theorem B1432763 : Blo 634301 1432763 := bstep (se 1 (by rfl) ⟨1074572, by rfl⟩ : syracuseStep 1432763 = 2149145) B2149145
theorem B2415815 : Blo 634301 2415815 := bstep (se 1 (by rfl) ⟨1811861, by rfl⟩ : syracuseStep 2415815 = 3623723) B3623723
theorem B1957193 : Blo 634301 1957193 := bstep (se 2 (by rfl) ⟨733947, by rfl⟩ : syracuseStep 1957193 = 1467895) B1467895
theorem B3628415 : Blo 634301 3628415 := bstep (se 1 (by rfl) ⟨2721311, by rfl⟩ : syracuseStep 3628415 = 5442623) B5442623
theorem B1433015 : Blo 634301 1433015 := bstep (se 1 (by rfl) ⟨1074761, by rfl⟩ : syracuseStep 1433015 = 2149523) B2149523
theorem B3104225 : Blo 634301 3104225 := bstep (se 2 (by rfl) ⟨1164084, by rfl⟩ : syracuseStep 3104225 = 2328169) B2328169
theorem B1433195 : Blo 634301 1433195 := bstep (se 1 (by rfl) ⟨1074896, by rfl⟩ : syracuseStep 1433195 = 2149793) B2149793
theorem B8150813 : Blo 634301 8150813 := bstep (se 3 (by rfl) ⟨1528277, by rfl⟩ : syracuseStep 8150813 = 3056555) B3056555
theorem B1433465 : Blo 634301 1433465 := bstep (se 2 (by rfl) ⟨537549, by rfl⟩ : syracuseStep 1433465 = 1075099) B1075099
theorem B1433555 : Blo 634301 1433555 := bstep (se 1 (by rfl) ⟨1075166, by rfl⟩ : syracuseStep 1433555 = 2150333) B2150333
theorem B1859561 : Blo 634301 1859561 := bstep (se 2 (by rfl) ⟨697335, by rfl⟩ : syracuseStep 1859561 = 1394671) B1394671
theorem B1433663 : Blo 634301 1433663 := bstep (se 1 (by rfl) ⟨1075247, by rfl⟩ : syracuseStep 1433663 = 2150495) B2150495
theorem B4088171 : Blo 634301 4088171 := bstep (se 1 (by rfl) ⟨3066128, by rfl⟩ : syracuseStep 4088171 = 6132257) B6132257
theorem B1434815 : Blo 634301 1434815 := bstep (se 1 (by rfl) ⟨1076111, by rfl⟩ : syracuseStep 1434815 = 2152223) B2152223
theorem B2450843 : Blo 634301 2450843 := bstep (se 1 (by rfl) ⟨1838132, by rfl⟩ : syracuseStep 2450843 = 3676265) B3676265
theorem B30926609 : Blo 634301 30926609 := bstep (se 2 (by rfl) ⟨11597478, by rfl⟩ : syracuseStep 30926609 = 23194957) B23194957
theorem B4843475 : Blo 634301 4843475 := bstep (se 1 (by rfl) ⟨3632606, by rfl⟩ : syracuseStep 4843475 = 7265213) B7265213
theorem B3860723 : Blo 634301 3860723 := bstep (se 1 (by rfl) ⟨2895542, by rfl⟩ : syracuseStep 3860723 = 5791085) B5791085
theorem B3631787 : Blo 634301 3631787 := bstep (se 1 (by rfl) ⟨2723840, by rfl⟩ : syracuseStep 3631787 = 5447681) B5447681
theorem B7563959 : Blo 634301 7563959 := bstep (se 1 (by rfl) ⟨5672969, by rfl⟩ : syracuseStep 7563959 = 11345939) B11345939
theorem B29420243 : Blo 634301 29420243 := bstep (se 1 (by rfl) ⟨22065182, by rfl⟩ : syracuseStep 29420243 = 44130365) B44130365
theorem B24406919 : Blo 634301 24406919 := bstep (se 1 (by rfl) ⟨18305189, by rfl⟩ : syracuseStep 24406919 = 36610379) B36610379
theorem B6876521 : Blo 634301 6876521 := bstep (se 2 (by rfl) ⟨2578695, by rfl⟩ : syracuseStep 6876521 = 5157391) B5157391
theorem B26144279 : Blo 634301 26144279 := bstep (se 1 (by rfl) ⟨19608209, by rfl⟩ : syracuseStep 26144279 = 39216419) B39216419
theorem B1928875 : Blo 634301 1928875 := bstep (se 1 (by rfl) ⟨1446656, by rfl⟩ : syracuseStep 1928875 = 2893313) B2893313
theorem B1306439 : Blo 634301 1306439 := bstep (se 1 (by rfl) ⟨979829, by rfl⟩ : syracuseStep 1306439 = 1959659) B1959659
theorem B2420675 : Blo 634301 2420675 := bstep (se 1 (by rfl) ⟨1815506, by rfl⟩ : syracuseStep 2420675 = 3631013) B3631013
theorem B717007 : Blo 634301 717007 := bstep (se 1 (by rfl) ⟨537755, by rfl⟩ : syracuseStep 717007 = 1075511) B1075511
theorem B2061167 : Blo 634301 2061167 := bstep (se 1 (by rfl) ⟨1545875, by rfl⟩ : syracuseStep 2061167 = 3091751) B3091751
theorem B1373231 : Blo 634301 1373231 := bstep (se 1 (by rfl) ⟨1029923, by rfl⟩ : syracuseStep 1373231 = 2059847) B2059847
theorem B717871 : Blo 634301 717871 := bstep (se 1 (by rfl) ⟨538403, by rfl⟩ : syracuseStep 717871 = 1076807) B1076807
theorem B3634247 : Blo 634301 3634247 := bstep (se 1 (by rfl) ⟨2725685, by rfl⟩ : syracuseStep 3634247 = 5451371) B5451371
theorem B3634955 : Blo 634301 3634955 := bstep (se 1 (by rfl) ⟨2726216, by rfl⟩ : syracuseStep 3634955 = 5452433) B5452433
theorem B1210535 : Blo 634301 1210535 := bstep (se 1 (by rfl) ⟨907901, by rfl⟩ : syracuseStep 1210535 = 1815803) B1815803
theorem B4193255 : Blo 634301 4193255 := bstep (se 1 (by rfl) ⟨3144941, by rfl⟩ : syracuseStep 4193255 = 6289883) B6289883
theorem B10878137 : Blo 634301 10878137 := bstep (se 2 (by rfl) ⟨4079301, by rfl⟩ : syracuseStep 10878137 = 8158603) B8158603
theorem B13073761 : Blo 634301 13073761 := bstep (se 2 (by rfl) ⟨4902660, by rfl⟩ : syracuseStep 13073761 = 9805321) B9805321
theorem B818671 : Blo 634301 818671 := bstep (se 1 (by rfl) ⟨614003, by rfl⟩ : syracuseStep 818671 = 1228007) B1228007
theorem B8158967 : Blo 634301 8158967 := bstep (se 1 (by rfl) ⟨6119225, by rfl⟩ : syracuseStep 8158967 = 12238451) B12238451
theorem B1606027 : Blo 634301 1606027 := bstep (se 1 (by rfl) ⟨1204520, by rfl⟩ : syracuseStep 1606027 = 2409041) B2409041
theorem B2032219 : Blo 634301 2032219 := bstep (se 1 (by rfl) ⟨1524164, by rfl⟩ : syracuseStep 2032219 = 3048329) B3048329
theorem B3212297 : Blo 634301 3212297 := bstep (se 2 (by rfl) ⟨1204611, by rfl⟩ : syracuseStep 3212297 = 2409223) B2409223
theorem B2360495 : Blo 634301 2360495 := bstep (se 1 (by rfl) ⟨1770371, by rfl⟩ : syracuseStep 2360495 = 3540743) B3540743
theorem B7734959 : Blo 634301 7734959 := bstep (se 1 (by rfl) ⟨5801219, by rfl⟩ : syracuseStep 7734959 = 11602439) B11602439
theorem B952367 : Blo 634301 952367 := bstep (se 1 (by rfl) ⟨714275, by rfl⟩ : syracuseStep 952367 = 1428551) B1428551
theorem B4950575 : Blo 634301 4950575 := bstep (se 1 (by rfl) ⟨3712931, by rfl⟩ : syracuseStep 4950575 = 7425863) B7425863
theorem B953087 : Blo 634301 953087 := bstep (se 1 (by rfl) ⟨714815, by rfl⟩ : syracuseStep 953087 = 1429631) B1429631
theorem B19631605 : Blo 634301 19631605 := bstep (se 5 (by rfl) ⟨920231, by rfl⟩ : syracuseStep 19631605 = 1840463) B1840463
theorem B954023 : Blo 634301 954023 := bstep (se 1 (by rfl) ⟨715517, by rfl⟩ : syracuseStep 954023 = 1431035) B1431035
theorem B954143 : Blo 634301 954143 := bstep (se 1 (by rfl) ⟨715607, by rfl⟩ : syracuseStep 954143 = 1431215) B1431215
theorem B954191 : Blo 634301 954191 := bstep (se 1 (by rfl) ⟨715643, by rfl⟩ : syracuseStep 954191 = 1431287) B1431287
theorem B954311 : Blo 634301 954311 := bstep (se 1 (by rfl) ⟨715733, by rfl⟩ : syracuseStep 954311 = 1431467) B1431467
theorem B954551 : Blo 634301 954551 := bstep (se 1 (by rfl) ⟨715913, by rfl⟩ : syracuseStep 954551 = 1431827) B1431827
theorem B954623 : Blo 634301 954623 := bstep (se 1 (by rfl) ⟨715967, by rfl⟩ : syracuseStep 954623 = 1431935) B1431935
theorem B954671 : Blo 634301 954671 := bstep (se 1 (by rfl) ⟨716003, by rfl⟩ : syracuseStep 954671 = 1432007) B1432007
theorem B11604343 : Blo 634301 11604343 := bstep (se 1 (by rfl) ⟨8703257, by rfl⟩ : syracuseStep 11604343 = 17406515) B17406515
theorem B954911 : Blo 634301 954911 := bstep (se 1 (by rfl) ⟨716183, by rfl⟩ : syracuseStep 954911 = 1432367) B1432367
theorem B954971 : Blo 634301 954971 := bstep (se 1 (by rfl) ⟨716228, by rfl⟩ : syracuseStep 954971 = 1432457) B1432457
theorem B1807123 : Blo 634301 1807123 := bstep (se 1 (by rfl) ⟨1355342, by rfl⟩ : syracuseStep 1807123 = 2710685) B2710685
theorem B955175 : Blo 634301 955175 := bstep (se 1 (by rfl) ⟨716381, by rfl⟩ : syracuseStep 955175 = 1432763) B1432763
theorem B1610543 : Blo 634301 1610543 := bstep (se 1 (by rfl) ⟨1207907, by rfl⟩ : syracuseStep 1610543 = 2415815) B2415815
theorem B955343 : Blo 634301 955343 := bstep (se 1 (by rfl) ⟨716507, by rfl⟩ : syracuseStep 955343 = 1433015) B1433015
theorem B2069483 : Blo 634301 2069483 := bstep (se 1 (by rfl) ⟨1552112, by rfl⟩ : syracuseStep 2069483 = 3104225) B3104225
theorem B955463 : Blo 634301 955463 := bstep (se 1 (by rfl) ⟨716597, by rfl⟩ : syracuseStep 955463 = 1433195) B1433195
theorem B955643 : Blo 634301 955643 := bstep (se 1 (by rfl) ⟨716732, by rfl⟩ : syracuseStep 955643 = 1433465) B1433465
theorem B955703 : Blo 634301 955703 := bstep (se 1 (by rfl) ⟨716777, by rfl⟩ : syracuseStep 955703 = 1433555) B1433555
theorem B955775 : Blo 634301 955775 := bstep (se 1 (by rfl) ⟨716831, by rfl⟩ : syracuseStep 955775 = 1433663) B1433663
theorem B2725447 : Blo 634301 2725447 := bstep (se 1 (by rfl) ⟨2044085, by rfl⟩ : syracuseStep 2725447 = 4088171) B4088171
theorem B956009 : Blo 634301 956009 := bstep (se 2 (by rfl) ⟨358503, by rfl⟩ : syracuseStep 956009 = 717007) B717007
theorem B4069439 : Blo 634301 4069439 := bstep (se 1 (by rfl) ⟨3052079, by rfl⟩ : syracuseStep 4069439 = 6104159) B6104159
theorem B956543 : Blo 634301 956543 := bstep (se 1 (by rfl) ⟨717407, by rfl⟩ : syracuseStep 956543 = 1434815) B1434815
theorem B4659551 : Blo 634301 4659551 := bstep (se 1 (by rfl) ⟨3494663, by rfl⟩ : syracuseStep 4659551 = 6989327) B6989327
theorem B20617739 : Blo 634301 20617739 := bstep (se 1 (by rfl) ⟨15463304, by rfl⟩ : syracuseStep 20617739 = 30926609) B30926609
theorem B957161 : Blo 634301 957161 := bstep (se 2 (by rfl) ⟨358935, by rfl⟩ : syracuseStep 957161 = 717871) B717871
theorem B5446723 : Blo 634301 5446723 := bstep (se 1 (by rfl) ⟨4085042, by rfl⟩ : syracuseStep 5446723 = 8170085) B8170085
theorem B1809641 : Blo 634301 1809641 := bstep (se 2 (by rfl) ⟨678615, by rfl⟩ : syracuseStep 1809641 = 1357231) B1357231
theorem B3218939 : Blo 634301 3218939 := bstep (se 1 (by rfl) ⟨2414204, by rfl⟩ : syracuseStep 3218939 = 4828409) B4828409
theorem B11182013 : Blo 634301 11182013 := bstep (se 3 (by rfl) ⟨2096627, by rfl⟩ : syracuseStep 11182013 = 4193255) B4193255
theorem B1613783 : Blo 634301 1613783 := bstep (se 1 (by rfl) ⟨1210337, by rfl⟩ : syracuseStep 1613783 = 2420675) B2420675
theorem B2171177 : Blo 634301 2171177 := bstep (se 2 (by rfl) ⟨814191, by rfl⟩ : syracuseStep 2171177 = 1628383) B1628383
theorem B2893735 : Blo 634301 2893735 := bstep (se 1 (by rfl) ⟨2170301, by rfl⟩ : syracuseStep 2893735 = 4340603) B4340603
theorem B1091561 : Blo 634301 1091561 := bstep (se 2 (by rfl) ⟨409335, by rfl⟩ : syracuseStep 1091561 = 818671) B818671
theorem B7252091 : Blo 634301 7252091 := bstep (se 1 (by rfl) ⟨5439068, by rfl⟩ : syracuseStep 7252091 = 10878137) B10878137
theorem B3680603 : Blo 634301 3680603 := bstep (se 1 (by rfl) ⟨2760452, by rfl⟩ : syracuseStep 3680603 = 5520905) B5520905
theorem B2141801 : Blo 634301 2141801 := bstep (se 2 (by rfl) ⟨803175, by rfl⟩ : syracuseStep 2141801 = 1606351) B1606351
theorem B12267125 : Blo 634301 12267125 := bstep (se 5 (by rfl) ⟨575021, by rfl⟩ : syracuseStep 12267125 = 1150043) B1150043
theorem B634523 : Blo 634301 634523 := bstep (se 1 (by rfl) ⟨475892, by rfl⟩ : syracuseStep 634523 = 951785) B951785
theorem B1355591 : Blo 634301 1355591 := bstep (se 1 (by rfl) ⟨1016693, by rfl⟩ : syracuseStep 1355591 = 2033387) B2033387
theorem B634783 : Blo 634301 634783 := bstep (se 1 (by rfl) ⟨476087, by rfl⟩ : syracuseStep 634783 = 952175) B952175
theorem B634907 : Blo 634301 634907 := bstep (se 1 (by rfl) ⟨476180, by rfl⟩ : syracuseStep 634907 = 952361) B952361
theorem B634927 : Blo 634301 634927 := bstep (se 1 (by rfl) ⟨476195, by rfl⟩ : syracuseStep 634927 = 952391) B952391
theorem B4042855 : Blo 634301 4042855 := bstep (se 1 (by rfl) ⟨3032141, by rfl⟩ : syracuseStep 4042855 = 6064283) B6064283
theorem B635047 : Blo 634301 635047 := bstep (se 1 (by rfl) ⟨476285, by rfl⟩ : syracuseStep 635047 = 952571) B952571
theorem B635183 : Blo 634301 635183 := bstep (se 1 (by rfl) ⟨476387, by rfl⟩ : syracuseStep 635183 = 952775) B952775
theorem B3617207 : Blo 634301 3617207 := bstep (se 1 (by rfl) ⟨2712905, by rfl⟩ : syracuseStep 3617207 = 5425811) B5425811
theorem B635327 : Blo 634301 635327 := bstep (se 1 (by rfl) ⟨476495, by rfl⟩ : syracuseStep 635327 = 952991) B952991
theorem B635359 : Blo 634301 635359 := bstep (se 1 (by rfl) ⟨476519, by rfl⟩ : syracuseStep 635359 = 953039) B953039
theorem B635423 : Blo 634301 635423 := bstep (se 1 (by rfl) ⟨476567, by rfl⟩ : syracuseStep 635423 = 953135) B953135
theorem B635503 : Blo 634301 635503 := bstep (se 1 (by rfl) ⟨476627, by rfl⟩ : syracuseStep 635503 = 953255) B953255
theorem B635623 : Blo 634301 635623 := bstep (se 1 (by rfl) ⟨476717, by rfl⟩ : syracuseStep 635623 = 953435) B953435
theorem B635675 : Blo 634301 635675 := bstep (se 1 (by rfl) ⟨476756, by rfl⟩ : syracuseStep 635675 = 953513) B953513
theorem B6108155 : Blo 634301 6108155 := bstep (se 1 (by rfl) ⟨4581116, by rfl⟩ : syracuseStep 6108155 = 9162233) B9162233
theorem B635951 : Blo 634301 635951 := bstep (se 1 (by rfl) ⟨476963, by rfl⟩ : syracuseStep 635951 = 953927) B953927
theorem B2143367 : Blo 634301 2143367 := bstep (se 1 (by rfl) ⟨1607525, by rfl⟩ : syracuseStep 2143367 = 3215051) B3215051
theorem B636071 : Blo 634301 636071 := bstep (se 1 (by rfl) ⟨477053, by rfl⟩ : syracuseStep 636071 = 954107) B954107
theorem B8729855 : Blo 634301 8729855 := bstep (se 1 (by rfl) ⟨6547391, by rfl⟩ : syracuseStep 8729855 = 13094783) B13094783
theorem B636231 : Blo 634301 636231 := bstep (se 1 (by rfl) ⟨477173, by rfl⟩ : syracuseStep 636231 = 954347) B954347
theorem B1815929 : Blo 634301 1815929 := bstep (se 2 (by rfl) ⟨680973, by rfl⟩ : syracuseStep 1815929 = 1361947) B1361947
theorem B5158525 : Blo 634301 5158525 := bstep (se 3 (by rfl) ⟨967223, by rfl⟩ : syracuseStep 5158525 = 1934447) B1934447
theorem B6109111 : Blo 634301 6109111 := bstep (se 1 (by rfl) ⟨4581833, by rfl⟩ : syracuseStep 6109111 = 9163667) B9163667
theorem B636923 : Blo 634301 636923 := bstep (se 1 (by rfl) ⟨477692, by rfl⟩ : syracuseStep 636923 = 955385) B955385
theorem B637055 : Blo 634301 637055 := bstep (se 1 (by rfl) ⟨477791, by rfl⟩ : syracuseStep 637055 = 955583) B955583
theorem B44546183 : Blo 634301 44546183 := bstep (se 1 (by rfl) ⟨33409637, by rfl⟩ : syracuseStep 44546183 = 66819275) B66819275
theorem B2144393 : Blo 634301 2144393 := bstep (se 2 (by rfl) ⟨804147, by rfl⟩ : syracuseStep 2144393 = 1608295) B1608295
theorem B637151 : Blo 634301 637151 := bstep (se 1 (by rfl) ⟨477863, by rfl⟩ : syracuseStep 637151 = 955727) B955727
theorem B637211 : Blo 634301 637211 := bstep (se 1 (by rfl) ⟨477908, by rfl⟩ : syracuseStep 637211 = 955817) B955817
theorem B637247 : Blo 634301 637247 := bstep (se 1 (by rfl) ⟨477935, by rfl⟩ : syracuseStep 637247 = 955871) B955871
theorem B637311 : Blo 634301 637311 := bstep (se 1 (by rfl) ⟨477983, by rfl⟩ : syracuseStep 637311 = 955967) B955967
theorem B9157211 : Blo 634301 9157211 := bstep (se 1 (by rfl) ⟨6867908, by rfl⟩ : syracuseStep 9157211 = 13735817) B13735817
theorem B637631 : Blo 634301 637631 := bstep (se 1 (by rfl) ⟨478223, by rfl⟩ : syracuseStep 637631 = 956447) B956447
theorem B637919 : Blo 634301 637919 := bstep (se 1 (by rfl) ⟨478439, by rfl⟩ : syracuseStep 637919 = 956879) B956879
theorem B637979 : Blo 634301 637979 := bstep (se 1 (by rfl) ⟨478484, by rfl⟩ : syracuseStep 637979 = 956969) B956969
theorem B638119 : Blo 634301 638119 := bstep (se 1 (by rfl) ⟨478589, by rfl⟩ : syracuseStep 638119 = 957179) B957179
theorem B638203 : Blo 634301 638203 := bstep (se 1 (by rfl) ⟨478652, by rfl⟩ : syracuseStep 638203 = 957305) B957305
theorem B2145743 : Blo 634301 2145743 := bstep (se 1 (by rfl) ⟨1609307, by rfl⟩ : syracuseStep 2145743 = 3218615) B3218615
theorem B2571833 : Blo 634301 2571833 := bstep (se 2 (by rfl) ⟨964437, by rfl⟩ : syracuseStep 2571833 = 1928875) B1928875
theorem B5423213 : Blo 634301 5423213 := bstep (se 3 (by rfl) ⟨1016852, by rfl⟩ : syracuseStep 5423213 = 2033705) B2033705
theorem B1327241 : Blo 634301 1327241 := bstep (se 2 (by rfl) ⟨497715, by rfl⟩ : syracuseStep 1327241 = 995431) B995431
theorem B1360127 : Blo 634301 1360127 := bstep (se 1 (by rfl) ⟨1020095, by rfl⟩ : syracuseStep 1360127 = 2040191) B2040191
theorem B12206537 : Blo 634301 12206537 := bstep (se 2 (by rfl) ⟨4577451, by rfl⟩ : syracuseStep 12206537 = 9154903) B9154903
theorem B5227259 : Blo 634301 5227259 := bstep (se 1 (by rfl) ⟨3920444, by rfl⟩ : syracuseStep 5227259 = 7840889) B7840889
theorem B3228983 : Blo 634301 3228983 := bstep (se 1 (by rfl) ⟨2421737, by rfl⟩ : syracuseStep 3228983 = 4843475) B4843475
theorem B2573815 : Blo 634301 2573815 := bstep (se 1 (by rfl) ⟨1930361, by rfl⟩ : syracuseStep 2573815 = 3860723) B3860723
theorem B39241523 : Blo 634301 39241523 := bstep (se 1 (by rfl) ⟨29431142, by rfl⟩ : syracuseStep 39241523 = 58862285) B58862285
theorem B19613495 : Blo 634301 19613495 := bstep (se 1 (by rfl) ⟨14710121, by rfl⟩ : syracuseStep 19613495 = 29420243) B29420243
theorem B16271279 : Blo 634301 16271279 := bstep (se 1 (by rfl) ⟨12203459, by rfl⟩ : syracuseStep 16271279 = 24406919) B24406919
theorem B2148335 : Blo 634301 2148335 := bstep (se 1 (by rfl) ⟨1611251, by rfl⟩ : syracuseStep 2148335 = 3222503) B3222503
theorem B870959 : Blo 634301 870959 := bstep (se 1 (by rfl) ⟨653219, by rfl⟩ : syracuseStep 870959 = 1306439) B1306439
theorem B1428947 : Blo 634301 1428947 := bstep (se 1 (by rfl) ⟨1071710, by rfl⟩ : syracuseStep 1428947 = 2143421) B2143421
theorem B2412413 : Blo 634301 2412413 := bstep (se 3 (by rfl) ⟨452327, by rfl⟩ : syracuseStep 2412413 = 904655) B904655
theorem B1429415 : Blo 634301 1429415 := bstep (se 1 (by rfl) ⟨1072061, by rfl⟩ : syracuseStep 1429415 = 2144123) B2144123
theorem B2150441 : Blo 634301 2150441 := bstep (se 2 (by rfl) ⟨806415, by rfl⟩ : syracuseStep 2150441 = 1612831) B1612831
theorem B807023 : Blo 634301 807023 := bstep (se 1 (by rfl) ⟨605267, by rfl⟩ : syracuseStep 807023 = 1210535) B1210535
theorem B2151251 : Blo 634301 2151251 := bstep (se 1 (by rfl) ⟨1613438, by rfl⟩ : syracuseStep 2151251 = 3226877) B3226877
theorem B2151305 : Blo 634301 2151305 := bstep (se 2 (by rfl) ⟨806739, by rfl⟩ : syracuseStep 2151305 = 1613479) B1613479
theorem B1431071 : Blo 634301 1431071 := bstep (se 1 (by rfl) ⟨1073303, by rfl⟩ : syracuseStep 1431071 = 2146607) B2146607
theorem B3626639 : Blo 634301 3626639 := bstep (se 1 (by rfl) ⟨2719979, by rfl⟩ : syracuseStep 3626639 = 5439959) B5439959
theorem B5822239 : Blo 634301 5822239 := bstep (se 1 (by rfl) ⟨4366679, by rfl⟩ : syracuseStep 5822239 = 8733359) B8733359
theorem B1431791 : Blo 634301 1431791 := bstep (se 1 (by rfl) ⟨1073843, by rfl⟩ : syracuseStep 1431791 = 2147687) B2147687
theorem B2709899 : Blo 634301 2709899 := bstep (se 1 (by rfl) ⟨2032424, by rfl⟩ : syracuseStep 2709899 = 4064849) B4064849
theorem B1432043 : Blo 634301 1432043 := bstep (se 1 (by rfl) ⟨1074032, by rfl⟩ : syracuseStep 1432043 = 2148065) B2148065
theorem B6118031 : Blo 634301 6118031 := bstep (se 1 (by rfl) ⟨4588523, by rfl⟩ : syracuseStep 6118031 = 9177047) B9177047
theorem B11623175 : Blo 634301 11623175 := bstep (se 1 (by rfl) ⟨8717381, by rfl⟩ : syracuseStep 11623175 = 17434763) B17434763
theorem B2415527 : Blo 634301 2415527 := bstep (se 1 (by rfl) ⟨1811645, by rfl⟩ : syracuseStep 2415527 = 3623291) B3623291
theorem B4643881 : Blo 634301 4643881 := bstep (se 2 (by rfl) ⟨1741455, by rfl⟩ : syracuseStep 4643881 = 3482911) B3482911
theorem B5496445 : Blo 634301 5496445 := bstep (se 3 (by rfl) ⟨1030583, by rfl⟩ : syracuseStep 5496445 = 2061167) B2061167
theorem B4349663 : Blo 634301 4349663 := bstep (se 1 (by rfl) ⟨3262247, by rfl⟩ : syracuseStep 4349663 = 6524495) B6524495
theorem B1073135 : Blo 634301 1073135 := bstep (se 1 (by rfl) ⟨804851, by rfl⟩ : syracuseStep 1073135 = 1609703) B1609703
theorem B3661949 : Blo 634301 3661949 := bstep (se 3 (by rfl) ⟨686615, by rfl⟩ : syracuseStep 3661949 = 1373231) B1373231
theorem B1434095 : Blo 634301 1434095 := bstep (se 1 (by rfl) ⟨1075571, by rfl⟩ : syracuseStep 1434095 = 2151143) B2151143
theorem B4121351 : Blo 634301 4121351 := bstep (se 1 (by rfl) ⟨3091013, by rfl⟩ : syracuseStep 4121351 = 6182027) B6182027
theorem B8151839 : Blo 634301 8151839 := bstep (se 1 (by rfl) ⟨6113879, by rfl⟩ : syracuseStep 8151839 = 12227759) B12227759
theorem B1074127 : Blo 634301 1074127 := bstep (se 1 (by rfl) ⟨805595, by rfl⟩ : syracuseStep 1074127 = 1611191) B1611191
theorem B1532969 : Blo 634301 1532969 := bstep (se 2 (by rfl) ⟨574863, by rfl⟩ : syracuseStep 1532969 = 1149727) B1149727
theorem B5792903 : Blo 634301 5792903 := bstep (se 1 (by rfl) ⟨4344677, by rfl⟩ : syracuseStep 5792903 = 8689355) B8689355
theorem B1434959 : Blo 634301 1434959 := bstep (se 1 (by rfl) ⟨1076219, by rfl⟩ : syracuseStep 1434959 = 2152439) B2152439
theorem B714343 : Blo 634301 714343 := bstep (se 1 (by rfl) ⟨535757, by rfl⟩ : syracuseStep 714343 = 1071515) B1071515
theorem B2418457 : Blo 634301 2418457 := bstep (se 2 (by rfl) ⟨906921, by rfl⟩ : syracuseStep 2418457 = 1813843) B1813843
theorem B1435679 : Blo 634301 1435679 := bstep (se 1 (by rfl) ⟨1076759, by rfl⟩ : syracuseStep 1435679 = 2153519) B2153519
theorem B1304795 : Blo 634301 1304795 := bstep (se 1 (by rfl) ⟨978596, by rfl⟩ : syracuseStep 1304795 = 1957193) B1957193
theorem B2418943 : Blo 634301 2418943 := bstep (se 1 (by rfl) ⟨1814207, by rfl⟩ : syracuseStep 2418943 = 3628415) B3628415
theorem B5433875 : Blo 634301 5433875 := bstep (se 1 (by rfl) ⟨4075406, by rfl⟩ : syracuseStep 5433875 = 8150813) B8150813
theorem B1239707 : Blo 634301 1239707 := bstep (se 1 (by rfl) ⟨929780, by rfl⟩ : syracuseStep 1239707 = 1859561) B1859561
theorem B2714273 : Blo 634301 2714273 := bstep (se 2 (by rfl) ⟨1017852, by rfl⟩ : syracuseStep 2714273 = 2035705) B2035705
theorem B1207163 : Blo 634301 1207163 := bstep (se 1 (by rfl) ⟨905372, by rfl⟩ : syracuseStep 1207163 = 1810745) B1810745
theorem B3632039 : Blo 634301 3632039 := bstep (se 1 (by rfl) ⟨2724029, by rfl⟩ : syracuseStep 3632039 = 5448059) B5448059
theorem B1076287 : Blo 634301 1076287 := bstep (se 1 (by rfl) ⟨807215, by rfl⟩ : syracuseStep 1076287 = 1614431) B1614431
theorem B1076537 : Blo 634301 1076537 := bstep (se 2 (by rfl) ⟨403701, by rfl⟩ : syracuseStep 1076537 = 807403) B807403
theorem B1633895 : Blo 634301 1633895 := bstep (se 1 (by rfl) ⟨1225421, by rfl⟩ : syracuseStep 1633895 = 2450843) B2450843
theorem B1208135 : Blo 634301 1208135 := bstep (se 1 (by rfl) ⟨906101, by rfl⟩ : syracuseStep 1208135 = 1812203) B1812203
theorem B2421161 : Blo 634301 2421161 := bstep (se 2 (by rfl) ⟨907935, by rfl⟩ : syracuseStep 2421161 = 1815871) B1815871
theorem B2421191 : Blo 634301 2421191 := bstep (se 1 (by rfl) ⟨1815893, by rfl⟩ : syracuseStep 2421191 = 3631787) B3631787
theorem B5042639 : Blo 634301 5042639 := bstep (se 1 (by rfl) ⟨3781979, by rfl⟩ : syracuseStep 5042639 = 7563959) B7563959
theorem B4584347 : Blo 634301 4584347 := bstep (se 1 (by rfl) ⟨3438260, by rfl⟩ : syracuseStep 4584347 = 6876521) B6876521
theorem B10843145 : Blo 634301 10843145 := bstep (se 2 (by rfl) ⟨4066179, by rfl⟩ : syracuseStep 10843145 = 8132359) B8132359
theorem B17429519 : Blo 634301 17429519 := bstep (se 1 (by rfl) ⟨13072139, by rfl⟩ : syracuseStep 17429519 = 26144279) B26144279
theorem B2422345 : Blo 634301 2422345 := bstep (se 2 (by rfl) ⟨908379, by rfl⟩ : syracuseStep 2422345 = 1816759) B1816759
theorem B1144667 : Blo 634301 1144667 := bstep (se 1 (by rfl) ⟨858500, by rfl⟩ : syracuseStep 1144667 = 1717001) B1717001
theorem B2422831 : Blo 634301 2422831 := bstep (se 1 (by rfl) ⟨1817123, by rfl⟩ : syracuseStep 2422831 = 3634247) B3634247
theorem B2718031 : Blo 634301 2718031 := bstep (se 1 (by rfl) ⟨2038523, by rfl⟩ : syracuseStep 2718031 = 4077047) B4077047
theorem B2587079 : Blo 634301 2587079 := bstep (se 1 (by rfl) ⟨1940309, by rfl⟩ : syracuseStep 2587079 = 3880619) B3880619
theorem B2423303 : Blo 634301 2423303 := bstep (se 1 (by rfl) ⟨1817477, by rfl⟩ : syracuseStep 2423303 = 3634955) B3634955
theorem B5175845 : Blo 634301 5175845 := bstep (se 4 (by rfl) ⟨485235, by rfl⟩ : syracuseStep 5175845 = 970471) B970471
theorem B17431681 : Blo 634301 17431681 := bstep (se 2 (by rfl) ⟨6536880, by rfl⟩ : syracuseStep 17431681 = 13073761) B13073761
theorem B5439311 : Blo 634301 5439311 := bstep (se 1 (by rfl) ⟨4079483, by rfl⟩ : syracuseStep 5439311 = 8158967) B8158967
theorem B884827 : Blo 634301 884827 := bstep (se 1 (by rfl) ⟨663620, by rfl⟩ : syracuseStep 884827 = 1327241) B1327241
theorem B9765197 : Blo 634301 9765197 := bstep (se 3 (by rfl) ⟨1830974, by rfl⟩ : syracuseStep 9765197 = 3661949) B3661949
theorem B1573663 : Blo 634301 1573663 := bstep (se 1 (by rfl) ⟨1180247, by rfl⟩ : syracuseStep 1573663 = 2360495) B2360495
theorem B13075663 : Blo 634301 13075663 := bstep (se 1 (by rfl) ⟨9806747, by rfl⟩ : syracuseStep 13075663 = 19613495) B19613495
theorem B10847519 : Blo 634301 10847519 := bstep (se 1 (by rfl) ⟨8135639, by rfl⟩ : syracuseStep 10847519 = 16271279) B16271279
theorem B952457 : Blo 634301 952457 := bstep (se 2 (by rfl) ⟨357171, by rfl⟩ : syracuseStep 952457 = 714343) B714343
theorem B952631 : Blo 634301 952631 := bstep (se 1 (by rfl) ⟨714473, by rfl⟩ : syracuseStep 952631 = 1428947) B1428947
theorem B1608275 : Blo 634301 1608275 := bstep (se 1 (by rfl) ⟨1206206, by rfl⟩ : syracuseStep 1608275 = 2412413) B2412413
theorem B952943 : Blo 634301 952943 := bstep (se 1 (by rfl) ⟨714707, by rfl⟩ : syracuseStep 952943 = 1429415) B1429415
theorem B954047 : Blo 634301 954047 := bstep (se 1 (by rfl) ⟨715535, by rfl⟩ : syracuseStep 954047 = 1431071) B1431071
theorem B954527 : Blo 634301 954527 := bstep (se 1 (by rfl) ⟨715895, by rfl⟩ : syracuseStep 954527 = 1431791) B1431791
theorem B1806599 : Blo 634301 1806599 := bstep (se 1 (by rfl) ⟨1354949, by rfl⟩ : syracuseStep 1806599 = 2709899) B2709899
theorem B954695 : Blo 634301 954695 := bstep (se 1 (by rfl) ⟨716021, by rfl⟩ : syracuseStep 954695 = 1432043) B1432043
theorem B1610351 : Blo 634301 1610351 := bstep (se 1 (by rfl) ⟨1207763, by rfl⟩ : syracuseStep 1610351 = 2415527) B2415527
theorem B1447451 : Blo 634301 1447451 := bstep (se 1 (by rfl) ⟨1085588, by rfl⟩ : syracuseStep 1447451 = 2171177) B2171177
theorem B956063 : Blo 634301 956063 := bstep (se 1 (by rfl) ⟨717047, by rfl⟩ : syracuseStep 956063 = 1434095) B1434095
theorem B15472457 : Blo 634301 15472457 := bstep (se 2 (by rfl) ⟨5802171, by rfl⟩ : syracuseStep 15472457 = 11604343) B11604343
theorem B1021979 : Blo 634301 1021979 := bstep (se 1 (by rfl) ⟨766484, by rfl⟩ : syracuseStep 1021979 = 1532969) B1532969
theorem B956639 : Blo 634301 956639 := bstep (se 1 (by rfl) ⟨717479, by rfl⟩ : syracuseStep 956639 = 1434959) B1434959
theorem B957119 : Blo 634301 957119 := bstep (se 1 (by rfl) ⟨717839, by rfl⟩ : syracuseStep 957119 = 1435679) B1435679
theorem B826471 : Blo 634301 826471 := bstep (se 1 (by rfl) ⟨619853, by rfl⟩ : syracuseStep 826471 = 1239707) B1239707
theorem B1809515 : Blo 634301 1809515 := bstep (se 1 (by rfl) ⟨1357136, by rfl⟩ : syracuseStep 1809515 = 2714273) B2714273
theorem B3219101 : Blo 634301 3219101 := bstep (se 3 (by rfl) ⟨603581, by rfl⟩ : syracuseStep 3219101 = 1207163) B1207163
theorem B1089263 : Blo 634301 1089263 := bstep (se 1 (by rfl) ⟨816947, by rfl⟩ : syracuseStep 1089263 = 1633895) B1633895
theorem B1614107 : Blo 634301 1614107 := bstep (se 1 (by rfl) ⟨1210580, by rfl⟩ : syracuseStep 1614107 = 2421161) B2421161
theorem B1614127 : Blo 634301 1614127 := bstep (se 1 (by rfl) ⟨1210595, by rfl⟩ : syracuseStep 1614127 = 2421191) B2421191
theorem B3056231 : Blo 634301 3056231 := bstep (se 1 (by rfl) ⟨2292173, by rfl⟩ : syracuseStep 3056231 = 4584347) B4584347
theorem B4072103 : Blo 634301 4072103 := bstep (se 1 (by rfl) ⟨3054077, by rfl⟩ : syracuseStep 4072103 = 6108155) B6108155
theorem B763111 : Blo 634301 763111 := bstep (se 1 (by rfl) ⟨572333, by rfl⟩ : syracuseStep 763111 = 1144667) B1144667
theorem B29697455 : Blo 634301 29697455 := bstep (se 1 (by rfl) ⟨22273091, by rfl⟩ : syracuseStep 29697455 = 44546183) B44546183
theorem B23242241 : Blo 634301 23242241 := bstep (se 2 (by rfl) ⟨8715840, by rfl⟩ : syracuseStep 23242241 = 17431681) B17431681
theorem B1615535 : Blo 634301 1615535 := bstep (se 1 (by rfl) ⟨1211651, by rfl⟩ : syracuseStep 1615535 = 2423303) B2423303
theorem B3450563 : Blo 634301 3450563 := bstep (se 1 (by rfl) ⟨2587922, by rfl⟩ : syracuseStep 3450563 = 5175845) B5175845
theorem B6104807 : Blo 634301 6104807 := bstep (se 1 (by rfl) ⟨4578605, by rfl⟩ : syracuseStep 6104807 = 9157211) B9157211
theorem B3221693 : Blo 634301 3221693 := bstep (se 3 (by rfl) ⟨604067, by rfl⟩ : syracuseStep 3221693 = 1208135) B1208135
theorem B1714555 : Blo 634301 1714555 := bstep (se 1 (by rfl) ⟨1285916, by rfl⟩ : syracuseStep 1714555 = 2571833) B2571833
theorem B3615475 : Blo 634301 3615475 := bstep (se 1 (by rfl) ⟨2711606, by rfl⟩ : syracuseStep 3615475 = 5423213) B5423213
theorem B8137691 : Blo 634301 8137691 := bstep (se 1 (by rfl) ⟨6103268, by rfl⟩ : syracuseStep 8137691 = 12206537) B12206537
theorem B2141369 : Blo 634301 2141369 := bstep (se 2 (by rfl) ⟨803013, by rfl⟩ : syracuseStep 2141369 = 1606027) B1606027
theorem B2141531 : Blo 634301 2141531 := bstep (se 1 (by rfl) ⟨1606148, by rfl⟩ : syracuseStep 2141531 = 3212297) B3212297
theorem B5156639 : Blo 634301 5156639 := bstep (se 1 (by rfl) ⟨3867479, by rfl⟩ : syracuseStep 5156639 = 7734959) B7734959
theorem B26161015 : Blo 634301 26161015 := bstep (se 1 (by rfl) ⟨19620761, by rfl⟩ : syracuseStep 26161015 = 39241523) B39241523
theorem B13447037 : Blo 634301 13447037 := bstep (se 3 (by rfl) ⟨2521319, by rfl⟩ : syracuseStep 13447037 = 5042639) B5042639
theorem B634911 : Blo 634301 634911 := bstep (se 1 (by rfl) ⟨476183, by rfl⟩ : syracuseStep 634911 = 952367) B952367
theorem B635391 : Blo 634301 635391 := bstep (se 1 (by rfl) ⟨476543, by rfl⟩ : syracuseStep 635391 = 953087) B953087
theorem B3224609 : Blo 634301 3224609 := bstep (se 2 (by rfl) ⟨1209228, by rfl⟩ : syracuseStep 3224609 = 2418457) B2418457
theorem B636015 : Blo 634301 636015 := bstep (se 1 (by rfl) ⟨477011, by rfl⟩ : syracuseStep 636015 = 954023) B954023
theorem B636095 : Blo 634301 636095 := bstep (se 1 (by rfl) ⟨477071, by rfl⟩ : syracuseStep 636095 = 954143) B954143
theorem B636127 : Blo 634301 636127 := bstep (se 1 (by rfl) ⟨477095, by rfl⟩ : syracuseStep 636127 = 954191) B954191
theorem B5518621 : Blo 634301 5518621 := bstep (se 3 (by rfl) ⟨1034741, by rfl⟩ : syracuseStep 5518621 = 2069483) B2069483
theorem B636207 : Blo 634301 636207 := bstep (se 1 (by rfl) ⟨477155, by rfl⟩ : syracuseStep 636207 = 954311) B954311
theorem B46478717 : Blo 634301 46478717 := bstep (se 3 (by rfl) ⟨8714759, by rfl⟩ : syracuseStep 46478717 = 17429519) B17429519
theorem B636367 : Blo 634301 636367 := bstep (se 1 (by rfl) ⟨477275, by rfl⟩ : syracuseStep 636367 = 954551) B954551
theorem B636415 : Blo 634301 636415 := bstep (se 1 (by rfl) ⟨477311, by rfl⟩ : syracuseStep 636415 = 954623) B954623
theorem B636447 : Blo 634301 636447 := bstep (se 1 (by rfl) ⟨477335, by rfl⟩ : syracuseStep 636447 = 954671) B954671
theorem B3225257 : Blo 634301 3225257 := bstep (se 2 (by rfl) ⟨1209471, by rfl⟩ : syracuseStep 3225257 = 2418943) B2418943
theorem B636607 : Blo 634301 636607 := bstep (se 1 (by rfl) ⟨477455, by rfl⟩ : syracuseStep 636607 = 954911) B954911
theorem B636647 : Blo 634301 636647 := bstep (se 1 (by rfl) ⟨477485, by rfl⟩ : syracuseStep 636647 = 954971) B954971
theorem B636783 : Blo 634301 636783 := bstep (se 1 (by rfl) ⟨477587, by rfl⟩ : syracuseStep 636783 = 955175) B955175
theorem B636895 : Blo 634301 636895 := bstep (se 1 (by rfl) ⟨477671, by rfl⟩ : syracuseStep 636895 = 955343) B955343
theorem B636975 : Blo 634301 636975 := bstep (se 1 (by rfl) ⟨477731, by rfl⟩ : syracuseStep 636975 = 955463) B955463
theorem B637095 : Blo 634301 637095 := bstep (se 1 (by rfl) ⟨477821, by rfl⟩ : syracuseStep 637095 = 955643) B955643
theorem B637135 : Blo 634301 637135 := bstep (se 1 (by rfl) ⟨477851, by rfl⟩ : syracuseStep 637135 = 955703) B955703
theorem B637183 : Blo 634301 637183 := bstep (se 1 (by rfl) ⟨477887, by rfl⟩ : syracuseStep 637183 = 955775) B955775
theorem B637339 : Blo 634301 637339 := bstep (se 1 (by rfl) ⟨478004, by rfl⟩ : syracuseStep 637339 = 956009) B956009
theorem B637695 : Blo 634301 637695 := bstep (se 1 (by rfl) ⟨478271, by rfl⟩ : syracuseStep 637695 = 956543) B956543
theorem B13745159 : Blo 634301 13745159 := bstep (se 1 (by rfl) ⟨10308869, by rfl⟩ : syracuseStep 13745159 = 20617739) B20617739
theorem B4078687 : Blo 634301 4078687 := bstep (se 1 (by rfl) ⟨3059015, by rfl⟩ : syracuseStep 4078687 = 6118031) B6118031
theorem B638107 : Blo 634301 638107 := bstep (se 1 (by rfl) ⟨478580, by rfl⟩ : syracuseStep 638107 = 957161) B957161
theorem B7748783 : Blo 634301 7748783 := bstep (se 1 (by rfl) ⟨5811587, by rfl⟩ : syracuseStep 7748783 = 11623175) B11623175
theorem B2145959 : Blo 634301 2145959 := bstep (se 1 (by rfl) ⟨1609469, by rfl⟩ : syracuseStep 2145959 = 3218939) B3218939
theorem B2899775 : Blo 634301 2899775 := bstep (se 1 (by rfl) ⟨2174831, by rfl⟩ : syracuseStep 2899775 = 4349663) B4349663
theorem B7454675 : Blo 634301 7454675 := bstep (se 1 (by rfl) ⟨5591006, by rfl⟩ : syracuseStep 7454675 = 11182013) B11182013
theorem B5390473 : Blo 634301 5390473 := bstep (se 2 (by rfl) ⟨2021427, by rfl⟩ : syracuseStep 5390473 = 4042855) B4042855
theorem B2409497 : Blo 634301 2409497 := bstep (se 2 (by rfl) ⟨903561, by rfl⟩ : syracuseStep 2409497 = 1807123) B1807123
theorem B6898877 : Blo 634301 6898877 := bstep (se 3 (by rfl) ⟨1293539, by rfl⟩ : syracuseStep 6898877 = 2587079) B2587079
theorem B4834727 : Blo 634301 4834727 := bstep (se 1 (by rfl) ⟨3626045, by rfl⟩ : syracuseStep 4834727 = 7252091) B7252091
theorem B869863 : Blo 634301 869863 := bstep (se 1 (by rfl) ⟨652397, by rfl⟩ : syracuseStep 869863 = 1304795) B1304795
theorem B3622583 : Blo 634301 3622583 := bstep (se 1 (by rfl) ⟨2716937, by rfl⟩ : syracuseStep 3622583 = 5433875) B5433875
theorem B3229793 : Blo 634301 3229793 := bstep (se 2 (by rfl) ⟨1211172, by rfl⟩ : syracuseStep 3229793 = 2422345) B2422345
theorem B1427867 : Blo 634301 1427867 := bstep (se 1 (by rfl) ⟨1070900, by rfl⟩ : syracuseStep 1427867 = 2141801) B2141801
theorem B8178083 : Blo 634301 8178083 := bstep (se 1 (by rfl) ⟨6133562, by rfl⟩ : syracuseStep 8178083 = 12267125) B12267125
theorem B903727 : Blo 634301 903727 := bstep (se 1 (by rfl) ⟨677795, by rfl⟩ : syracuseStep 903727 = 1355591) B1355591
theorem B8145481 : Blo 634301 8145481 := bstep (se 2 (by rfl) ⟨3054555, by rfl⟩ : syracuseStep 8145481 = 6109111) B6109111
theorem B55757429 : Blo 634301 55757429 := bstep (se 5 (by rfl) ⟨2613629, by rfl⟩ : syracuseStep 55757429 = 5227259) B5227259
theorem B3230441 : Blo 634301 3230441 := bstep (se 2 (by rfl) ⟨1211415, by rfl⟩ : syracuseStep 3230441 = 2422831) B2422831
theorem B2411471 : Blo 634301 2411471 := bstep (se 1 (by rfl) ⟨1808603, by rfl⟩ : syracuseStep 2411471 = 3617207) B3617207
theorem B3624041 : Blo 634301 3624041 := bstep (se 2 (by rfl) ⟨1359015, by rfl⟩ : syracuseStep 3624041 = 2718031) B2718031
theorem B7228763 : Blo 634301 7228763 := bstep (se 1 (by rfl) ⟨5421572, by rfl⟩ : syracuseStep 7228763 = 10843145) B10843145
theorem B1428911 : Blo 634301 1428911 := bstep (se 1 (by rfl) ⟨1071683, by rfl⟩ : syracuseStep 1428911 = 2143367) B2143367
theorem B5819903 : Blo 634301 5819903 := bstep (se 1 (by rfl) ⟨4364927, by rfl⟩ : syracuseStep 5819903 = 8729855) B8729855
theorem B7262297 : Blo 634301 7262297 := bstep (se 2 (by rfl) ⟨2723361, by rfl⟩ : syracuseStep 7262297 = 5446723) B5446723
theorem B1429595 : Blo 634301 1429595 := bstep (se 1 (by rfl) ⟨1072196, by rfl⟩ : syracuseStep 1429595 = 2144393) B2144393
theorem B7328593 : Blo 634301 7328593 := bstep (se 2 (by rfl) ⟨2748222, by rfl⟩ : syracuseStep 7328593 = 5496445) B5496445
theorem B1430495 : Blo 634301 1430495 := bstep (se 1 (by rfl) ⟨1072871, by rfl⟩ : syracuseStep 1430495 = 2145743) B2145743
theorem B3626207 : Blo 634301 3626207 := bstep (se 1 (by rfl) ⟨2719655, by rfl⟩ : syracuseStep 3626207 = 5439311) B5439311
theorem B906751 : Blo 634301 906751 := bstep (se 1 (by rfl) ⟨680063, by rfl⟩ : syracuseStep 906751 = 1360127) B1360127
theorem B2152061 : Blo 634301 2152061 := bstep (se 3 (by rfl) ⟨403511, by rfl⟩ : syracuseStep 2152061 = 807023) B807023
theorem B2709625 : Blo 634301 2709625 := bstep (se 2 (by rfl) ⟨1016109, by rfl⟩ : syracuseStep 2709625 = 2032219) B2032219
theorem B2152655 : Blo 634301 2152655 := bstep (se 1 (by rfl) ⟨1614491, by rfl⟩ : syracuseStep 2152655 = 3228983) B3228983
theorem B1432169 : Blo 634301 1432169 := bstep (se 2 (by rfl) ⟨537063, by rfl⟩ : syracuseStep 1432169 = 1074127) B1074127
theorem B1432223 : Blo 634301 1432223 := bstep (se 1 (by rfl) ⟨1074167, by rfl⟩ : syracuseStep 1432223 = 2148335) B2148335
theorem B3300383 : Blo 634301 3300383 := bstep (se 1 (by rfl) ⟨2475287, by rfl⟩ : syracuseStep 3300383 = 4950575) B4950575
theorem B3431753 : Blo 634301 3431753 := bstep (se 2 (by rfl) ⟨1286907, by rfl⟩ : syracuseStep 3431753 = 2573815) B2573815
theorem B3858313 : Blo 634301 3858313 := bstep (se 2 (by rfl) ⟨1446867, by rfl⟩ : syracuseStep 3858313 = 2893735) B2893735
theorem B1433627 : Blo 634301 1433627 := bstep (se 1 (by rfl) ⟨1075220, by rfl⟩ : syracuseStep 1433627 = 2150441) B2150441
theorem B1073695 : Blo 634301 1073695 := bstep (se 1 (by rfl) ⟨805271, by rfl⟩ : syracuseStep 1073695 = 1610543) B1610543
theorem B1434167 : Blo 634301 1434167 := bstep (se 1 (by rfl) ⟨1075625, by rfl⟩ : syracuseStep 1434167 = 2151251) B2151251
theorem B1434203 : Blo 634301 1434203 := bstep (se 1 (by rfl) ⟨1075652, by rfl⟩ : syracuseStep 1434203 = 2151305) B2151305
theorem B2417759 : Blo 634301 2417759 := bstep (se 1 (by rfl) ⟨1813319, by rfl⟩ : syracuseStep 2417759 = 3626639) B3626639
theorem B2712959 : Blo 634301 2712959 := bstep (se 1 (by rfl) ⟨2034719, by rfl⟩ : syracuseStep 2712959 = 4069439) B4069439
theorem B1435049 : Blo 634301 1435049 := bstep (se 2 (by rfl) ⟨538143, by rfl⟩ : syracuseStep 1435049 = 1076287) B1076287
theorem B3106367 : Blo 634301 3106367 := bstep (se 1 (by rfl) ⟨2329775, by rfl⟩ : syracuseStep 3106367 = 4659551) B4659551
theorem B26175473 : Blo 634301 26175473 := bstep (se 2 (by rfl) ⟨9815802, by rfl⟩ : syracuseStep 26175473 = 19631605) B19631605
theorem B1206427 : Blo 634301 1206427 := bstep (se 1 (by rfl) ⟨904820, by rfl⟩ : syracuseStep 1206427 = 1809641) B1809641
theorem B2910829 : Blo 634301 2910829 := bstep (se 3 (by rfl) ⟨545780, by rfl⟩ : syracuseStep 2910829 = 1091561) B1091561
theorem B1075855 : Blo 634301 1075855 := bstep (se 1 (by rfl) ⟨806891, by rfl⟩ : syracuseStep 1075855 = 1613783) B1613783
theorem B715423 : Blo 634301 715423 := bstep (se 1 (by rfl) ⟨536567, by rfl⟩ : syracuseStep 715423 = 1073135) B1073135
theorem B24767365 : Blo 634301 24767365 := bstep (se 4 (by rfl) ⟨2321940, by rfl⟩ : syracuseStep 24767365 = 4643881) B4643881
theorem B2747567 : Blo 634301 2747567 := bstep (se 1 (by rfl) ⟨2060675, by rfl⟩ : syracuseStep 2747567 = 4121351) B4121351
theorem B5434559 : Blo 634301 5434559 := bstep (se 1 (by rfl) ⟨4075919, by rfl⟩ : syracuseStep 5434559 = 8151839) B8151839
theorem B3861935 : Blo 634301 3861935 := bstep (se 1 (by rfl) ⟨2896451, by rfl⟩ : syracuseStep 3861935 = 5792903) B5792903
theorem B2322557 : Blo 634301 2322557 := bstep (se 3 (by rfl) ⟨435479, by rfl⟩ : syracuseStep 2322557 = 870959) B870959
theorem B2453735 : Blo 634301 2453735 := bstep (se 1 (by rfl) ⟨1840301, by rfl⟩ : syracuseStep 2453735 = 3680603) B3680603
theorem B2421359 : Blo 634301 2421359 := bstep (se 1 (by rfl) ⟨1816019, by rfl⟩ : syracuseStep 2421359 = 3632039) B3632039
theorem B3633929 : Blo 634301 3633929 := bstep (se 2 (by rfl) ⟨1362723, by rfl⟩ : syracuseStep 3633929 = 2725447) B2725447
theorem B6878033 : Blo 634301 6878033 := bstep (se 2 (by rfl) ⟨2579262, by rfl⟩ : syracuseStep 6878033 = 5158525) B5158525
theorem B717691 : Blo 634301 717691 := bstep (se 1 (by rfl) ⟨538268, by rfl⟩ : syracuseStep 717691 = 1076537) B1076537
theorem B7762985 : Blo 634301 7762985 := bstep (se 2 (by rfl) ⟨2911119, by rfl⟩ : syracuseStep 7762985 = 5822239) B5822239
theorem B1210619 : Blo 634301 1210619 := bstep (se 1 (by rfl) ⟨907964, by rfl⟩ : syracuseStep 1210619 = 1815929) B1815929
theorem B4719077 : Blo 634301 4719077 := bstep (se 4 (by rfl) ⟨442413, by rfl⟩ : syracuseStep 4719077 = 884827) B884827
theorem B1606331 : Blo 634301 1606331 := bstep (se 1 (by rfl) ⟨1204748, by rfl⟩ : syracuseStep 1606331 = 2409497) B2409497
theorem B2098217 : Blo 634301 2098217 := bstep (se 2 (by rfl) ⟨786831, by rfl⟩ : syracuseStep 2098217 = 1573663) B1573663
theorem B951911 : Blo 634301 951911 := bstep (se 1 (by rfl) ⟨713933, by rfl⟩ : syracuseStep 951911 = 1427867) B1427867
theorem B17434217 : Blo 634301 17434217 := bstep (se 2 (by rfl) ⟨6537831, by rfl⟩ : syracuseStep 17434217 = 13075663) B13075663
theorem B1607647 : Blo 634301 1607647 := bstep (se 1 (by rfl) ⟨1205735, by rfl⟩ : syracuseStep 1607647 = 2411471) B2411471
theorem B4819175 : Blo 634301 4819175 := bstep (se 1 (by rfl) ⟨3614381, by rfl⟩ : syracuseStep 4819175 = 7228763) B7228763
theorem B952607 : Blo 634301 952607 := bstep (se 1 (by rfl) ⟨714455, by rfl⟩ : syracuseStep 952607 = 1428911) B1428911
theorem B953063 : Blo 634301 953063 := bstep (se 1 (by rfl) ⟨714797, by rfl⟩ : syracuseStep 953063 = 1429595) B1429595
theorem B1608569 : Blo 634301 1608569 := bstep (se 2 (by rfl) ⟨603213, by rfl⟩ : syracuseStep 1608569 = 1206427) B1206427
theorem B953663 : Blo 634301 953663 := bstep (se 1 (by rfl) ⟨715247, by rfl⟩ : syracuseStep 953663 = 1430495) B1430495
theorem B953897 : Blo 634301 953897 := bstep (se 2 (by rfl) ⟨357711, by rfl⟩ : syracuseStep 953897 = 715423) B715423
theorem B4820633 : Blo 634301 4820633 := bstep (se 2 (by rfl) ⟨1807737, by rfl⟩ : syracuseStep 4820633 = 3615475) B3615475
theorem B954779 : Blo 634301 954779 := bstep (se 1 (by rfl) ⟨716084, by rfl⟩ : syracuseStep 954779 = 1432169) B1432169
theorem B954815 : Blo 634301 954815 := bstep (se 1 (by rfl) ⟨716111, by rfl⟩ : syracuseStep 954815 = 1432223) B1432223
theorem B2200255 : Blo 634301 2200255 := bstep (se 1 (by rfl) ⟨1650191, by rfl⟩ : syracuseStep 2200255 = 3300383) B3300383
theorem B726175 : Blo 634301 726175 := bstep (se 1 (by rfl) ⟨544631, by rfl⟩ : syracuseStep 726175 = 1089263) B1089263
theorem B955751 : Blo 634301 955751 := bstep (se 1 (by rfl) ⟨716813, by rfl⟩ : syracuseStep 955751 = 1433627) B1433627
theorem B956111 : Blo 634301 956111 := bstep (se 1 (by rfl) ⟨717083, by rfl⟩ : syracuseStep 956111 = 1434167) B1434167
theorem B956135 : Blo 634301 956135 := bstep (se 1 (by rfl) ⟨717101, by rfl⟩ : syracuseStep 956135 = 1434203) B1434203
theorem B2037487 : Blo 634301 2037487 := bstep (se 1 (by rfl) ⟨1528115, by rfl⟩ : syracuseStep 2037487 = 3056231) B3056231
theorem B1611839 : Blo 634301 1611839 := bstep (se 1 (by rfl) ⟨1208879, by rfl⟩ : syracuseStep 1611839 = 2417759) B2417759
theorem B1808639 : Blo 634301 1808639 := bstep (se 1 (by rfl) ⟨1356479, by rfl⟩ : syracuseStep 1808639 = 2712959) B2712959
theorem B956699 : Blo 634301 956699 := bstep (se 1 (by rfl) ⟨717524, by rfl⟩ : syracuseStep 956699 = 1435049) B1435049
theorem B2070911 : Blo 634301 2070911 := bstep (se 1 (by rfl) ⟨1553183, by rfl⟩ : syracuseStep 2070911 = 3106367) B3106367
theorem B9771457 : Blo 634301 9771457 := bstep (se 2 (by rfl) ⟨3664296, by rfl⟩ : syracuseStep 9771457 = 7328593) B7328593
theorem B2300375 : Blo 634301 2300375 := bstep (se 1 (by rfl) ⟨1725281, by rfl⟩ : syracuseStep 2300375 = 3450563) B3450563
theorem B4069871 : Blo 634301 4069871 := bstep (se 1 (by rfl) ⟨3052403, by rfl⟩ : syracuseStep 4069871 = 6104807) B6104807
theorem B956921 : Blo 634301 956921 := bstep (se 2 (by rfl) ⟨358845, by rfl⟩ : syracuseStep 956921 = 717691) B717691
theorem B4069925 : Blo 634301 4069925 := bstep (se 4 (by rfl) ⟨381555, by rfl⟩ : syracuseStep 4069925 = 763111) B763111
theorem B1548371 : Blo 634301 1548371 := bstep (se 1 (by rfl) ⟨1161278, by rfl⟩ : syracuseStep 1548371 = 2322557) B2322557
theorem B3612833 : Blo 634301 3612833 := bstep (se 2 (by rfl) ⟨1354812, by rfl⟩ : syracuseStep 3612833 = 2709625) B2709625
theorem B1614239 : Blo 634301 1614239 := bstep (se 1 (by rfl) ⟨1210679, by rfl⟩ : syracuseStep 1614239 = 2421359) B2421359
theorem B35858765 : Blo 634301 35858765 := bstep (se 3 (by rfl) ⟨6723518, by rfl⟩ : syracuseStep 35858765 = 13447037) B13447037
theorem B7187297 : Blo 634301 7187297 := bstep (se 2 (by rfl) ⟨2695236, by rfl⟩ : syracuseStep 7187297 = 5390473) B5390473
theorem B4599251 : Blo 634301 4599251 := bstep (se 1 (by rfl) ⟨3449438, by rfl⟩ : syracuseStep 4599251 = 6898877) B6898877
theorem B3223151 : Blo 634301 3223151 := bstep (se 1 (by rfl) ⟨2417363, by rfl⟩ : syracuseStep 3223151 = 4834727) B4834727
theorem B634971 : Blo 634301 634971 := bstep (se 1 (by rfl) ⟨476228, by rfl⟩ : syracuseStep 634971 = 952457) B952457
theorem B635087 : Blo 634301 635087 := bstep (se 1 (by rfl) ⟨476315, by rfl⟩ : syracuseStep 635087 = 952631) B952631
theorem B5452055 : Blo 634301 5452055 := bstep (se 1 (by rfl) ⟨4089041, by rfl⟩ : syracuseStep 5452055 = 8178083) B8178083
theorem B635295 : Blo 634301 635295 := bstep (se 1 (by rfl) ⟨476471, by rfl⟩ : syracuseStep 635295 = 952943) B952943
theorem B37171619 : Blo 634301 37171619 := bstep (se 1 (by rfl) ⟨27878714, by rfl⟩ : syracuseStep 37171619 = 55757429) B55757429
theorem B1159817 : Blo 634301 1159817 := bstep (se 2 (by rfl) ⟨434931, by rfl⟩ : syracuseStep 1159817 = 869863) B869863
theorem B3879935 : Blo 634301 3879935 := bstep (se 1 (by rfl) ⟨2909951, by rfl⟩ : syracuseStep 3879935 = 5819903) B5819903
theorem B636031 : Blo 634301 636031 := bstep (se 1 (by rfl) ⟨477023, by rfl⟩ : syracuseStep 636031 = 954047) B954047
theorem B636351 : Blo 634301 636351 := bstep (se 1 (by rfl) ⟨477263, by rfl⟩ : syracuseStep 636351 = 954527) B954527
theorem B636463 : Blo 634301 636463 := bstep (se 1 (by rfl) ⟨477347, by rfl⟩ : syracuseStep 636463 = 954695) B954695
theorem B10860641 : Blo 634301 10860641 := bstep (se 2 (by rfl) ⟨4072740, by rfl⟩ : syracuseStep 10860641 = 8145481) B8145481
theorem B3881105 : Blo 634301 3881105 := bstep (se 2 (by rfl) ⟨1455414, by rfl⟩ : syracuseStep 3881105 = 2910829) B2910829
theorem B964967 : Blo 634301 964967 := bstep (se 1 (by rfl) ⟨723725, by rfl⟩ : syracuseStep 964967 = 1447451) B1447451
theorem B637375 : Blo 634301 637375 := bstep (se 1 (by rfl) ⟨478031, by rfl⟩ : syracuseStep 637375 = 956063) B956063
theorem B637759 : Blo 634301 637759 := bstep (se 1 (by rfl) ⟨478319, by rfl⟩ : syracuseStep 637759 = 956639) B956639
theorem B638079 : Blo 634301 638079 := bstep (se 1 (by rfl) ⟨478559, by rfl⟩ : syracuseStep 638079 = 957119) B957119
theorem B2146067 : Blo 634301 2146067 := bstep (se 1 (by rfl) ⟨1609550, by rfl⟩ : syracuseStep 2146067 = 3219101) B3219101
theorem B34881353 : Blo 634301 34881353 := bstep (se 2 (by rfl) ⟨13080507, by rfl⟩ : syracuseStep 34881353 = 26161015) B26161015
theorem B17450315 : Blo 634301 17450315 := bstep (se 1 (by rfl) ⟨13087736, by rfl⟩ : syracuseStep 17450315 = 26175473) B26175473
theorem B2147795 : Blo 634301 2147795 := bstep (se 1 (by rfl) ⟨1610846, by rfl⟩ : syracuseStep 2147795 = 3221693) B3221693
theorem B7358161 : Blo 634301 7358161 := bstep (se 2 (by rfl) ⟨2759310, by rfl⟩ : syracuseStep 7358161 = 5518621) B5518621
theorem B5425127 : Blo 634301 5425127 := bstep (se 1 (by rfl) ⟨4068845, by rfl⟩ : syracuseStep 5425127 = 8137691) B8137691
theorem B1427579 : Blo 634301 1427579 := bstep (se 1 (by rfl) ⟨1070684, by rfl⟩ : syracuseStep 1427579 = 2141369) B2141369
theorem B3623039 : Blo 634301 3623039 := bstep (se 1 (by rfl) ⟨2717279, by rfl⟩ : syracuseStep 3623039 = 5434559) B5434559
theorem B1427687 : Blo 634301 1427687 := bstep (se 1 (by rfl) ⟨1070765, by rfl⟩ : syracuseStep 1427687 = 2141531) B2141531
theorem B2574623 : Blo 634301 2574623 := bstep (se 1 (by rfl) ⟨1930967, by rfl⟩ : syracuseStep 2574623 = 3861935) B3861935
theorem B7326845 : Blo 634301 7326845 := bstep (se 3 (by rfl) ⟨1373783, by rfl⟩ : syracuseStep 7326845 = 2747567) B2747567
theorem B2149739 : Blo 634301 2149739 := bstep (se 1 (by rfl) ⟨1612304, by rfl⟩ : syracuseStep 2149739 = 3224609) B3224609
theorem B30985811 : Blo 634301 30985811 := bstep (se 1 (by rfl) ⟨23239358, by rfl⟩ : syracuseStep 30985811 = 46478717) B46478717
theorem B2150171 : Blo 634301 2150171 := bstep (se 1 (by rfl) ⟨1612628, by rfl⟩ : syracuseStep 2150171 = 3225257) B3225257
theorem B1101961 : Blo 634301 1101961 := bstep (se 2 (by rfl) ⟨413235, by rfl⟩ : syracuseStep 1101961 = 826471) B826471
theorem B807079 : Blo 634301 807079 := bstep (se 1 (by rfl) ⟨605309, by rfl⟩ : syracuseStep 807079 = 1210619) B1210619
theorem B9163439 : Blo 634301 9163439 := bstep (se 1 (by rfl) ⟨6872579, by rfl⟩ : syracuseStep 9163439 = 13745159) B13745159
theorem B5165855 : Blo 634301 5165855 := bstep (se 1 (by rfl) ⟨3874391, by rfl⟩ : syracuseStep 5165855 = 7748783) B7748783
theorem B1430639 : Blo 634301 1430639 := bstep (se 1 (by rfl) ⟨1072979, by rfl⟩ : syracuseStep 1430639 = 2145959) B2145959
theorem B4969783 : Blo 634301 4969783 := bstep (se 1 (by rfl) ⟨3727337, by rfl⟩ : syracuseStep 4969783 = 7454675) B7454675
theorem B6510131 : Blo 634301 6510131 := bstep (se 1 (by rfl) ⟨4882598, by rfl⟩ : syracuseStep 6510131 = 9765197) B9765197
theorem B2152169 : Blo 634301 2152169 := bstep (se 2 (by rfl) ⟨807063, by rfl⟩ : syracuseStep 2152169 = 1614127) B1614127
theorem B1431593 : Blo 634301 1431593 := bstep (se 2 (by rfl) ⟨536847, by rfl⟩ : syracuseStep 1431593 = 1073695) B1073695
theorem B7231679 : Blo 634301 7231679 := bstep (se 1 (by rfl) ⟨5423759, by rfl⟩ : syracuseStep 7231679 = 10847519) B10847519
theorem B2415055 : Blo 634301 2415055 := bstep (se 1 (by rfl) ⟨1811291, by rfl⟩ : syracuseStep 2415055 = 3622583) B3622583
theorem B2153195 : Blo 634301 2153195 := bstep (se 1 (by rfl) ⟨1614896, by rfl⟩ : syracuseStep 2153195 = 3229793) B3229793
theorem B1072183 : Blo 634301 1072183 := bstep (se 1 (by rfl) ⟨804137, by rfl⟩ : syracuseStep 1072183 = 1608275) B1608275
theorem B2153627 : Blo 634301 2153627 := bstep (se 1 (by rfl) ⟨1615220, by rfl⟩ : syracuseStep 2153627 = 3230441) B3230441
theorem B2416027 : Blo 634301 2416027 := bstep (se 1 (by rfl) ⟨1812020, by rfl⟩ : syracuseStep 2416027 = 3624041) B3624041
theorem B4841531 : Blo 634301 4841531 := bstep (se 1 (by rfl) ⟨3631148, by rfl⟩ : syracuseStep 4841531 = 7262297) B7262297
theorem B1204399 : Blo 634301 1204399 := bstep (se 1 (by rfl) ⟨903299, by rfl⟩ : syracuseStep 1204399 = 1806599) B1806599
theorem B1073567 : Blo 634301 1073567 := bstep (se 1 (by rfl) ⟨805175, by rfl⟩ : syracuseStep 1073567 = 1610351) B1610351
theorem B2286073 : Blo 634301 2286073 := bstep (se 2 (by rfl) ⟨857277, by rfl⟩ : syracuseStep 2286073 = 1714555) B1714555
theorem B1204969 : Blo 634301 1204969 := bstep (se 2 (by rfl) ⟨451863, by rfl⟩ : syracuseStep 1204969 = 903727) B903727
theorem B2417471 : Blo 634301 2417471 := bstep (se 1 (by rfl) ⟨1813103, by rfl⟩ : syracuseStep 2417471 = 3626207) B3626207
theorem B1434473 : Blo 634301 1434473 := bstep (se 2 (by rfl) ⟨537927, by rfl⟩ : syracuseStep 1434473 = 1075855) B1075855
theorem B1434707 : Blo 634301 1434707 := bstep (se 1 (by rfl) ⟨1076030, by rfl⟩ : syracuseStep 1434707 = 2152061) B2152061
theorem B79193213 : Blo 634301 79193213 := bstep (se 3 (by rfl) ⟨14848727, by rfl⟩ : syracuseStep 79193213 = 29697455) B29697455
theorem B33023153 : Blo 634301 33023153 := bstep (se 2 (by rfl) ⟨12383682, by rfl⟩ : syracuseStep 33023153 = 24767365) B24767365
theorem B10314971 : Blo 634301 10314971 := bstep (se 1 (by rfl) ⟨7736228, by rfl⟩ : syracuseStep 10314971 = 15472457) B15472457
theorem B681319 : Blo 634301 681319 := bstep (se 1 (by rfl) ⟨510989, by rfl⟩ : syracuseStep 681319 = 1021979) B1021979
theorem B1435103 : Blo 634301 1435103 := bstep (se 1 (by rfl) ⟨1076327, by rfl⟩ : syracuseStep 1435103 = 2152655) B2152655
theorem B1206343 : Blo 634301 1206343 := bstep (se 1 (by rfl) ⟨904757, by rfl⟩ : syracuseStep 1206343 = 1809515) B1809515
theorem B2287835 : Blo 634301 2287835 := bstep (se 1 (by rfl) ⟨1715876, by rfl⟩ : syracuseStep 2287835 = 3431753) B3431753
theorem B1076071 : Blo 634301 1076071 := bstep (se 1 (by rfl) ⟨807053, by rfl⟩ : syracuseStep 1076071 = 1614107) B1614107
theorem B2714735 : Blo 634301 2714735 := bstep (se 1 (by rfl) ⟨2036051, by rfl⟩ : syracuseStep 2714735 = 4072103) B4072103
theorem B15494827 : Blo 634301 15494827 := bstep (se 1 (by rfl) ⟨11621120, by rfl⟩ : syracuseStep 15494827 = 23242241) B23242241
theorem B1077023 : Blo 634301 1077023 := bstep (se 1 (by rfl) ⟨807767, by rfl⟩ : syracuseStep 1077023 = 1615535) B1615535
theorem B1209001 : Blo 634301 1209001 := bstep (se 2 (by rfl) ⟨453375, by rfl⟩ : syracuseStep 1209001 = 906751) B906751
theorem B3437759 : Blo 634301 3437759 := bstep (se 1 (by rfl) ⟨2578319, by rfl⟩ : syracuseStep 3437759 = 5156639) B5156639
theorem B1635823 : Blo 634301 1635823 := bstep (se 1 (by rfl) ⟨1226867, by rfl⟩ : syracuseStep 1635823 = 2453735) B2453735
theorem B2422619 : Blo 634301 2422619 := bstep (se 1 (by rfl) ⟨1816964, by rfl⟩ : syracuseStep 2422619 = 3633929) B3633929
theorem B4585355 : Blo 634301 4585355 := bstep (se 1 (by rfl) ⟨3439016, by rfl⟩ : syracuseStep 4585355 = 6878033) B6878033
theorem B5175323 : Blo 634301 5175323 := bstep (se 1 (by rfl) ⟨3881492, by rfl⟩ : syracuseStep 5175323 = 7762985) B7762985
theorem B5438249 : Blo 634301 5438249 := bstep (se 2 (by rfl) ⟨2039343, by rfl⟩ : syracuseStep 5438249 = 4078687) B4078687
theorem B5144417 : Blo 634301 5144417 := bstep (se 2 (by rfl) ⟨1929156, by rfl⟩ : syracuseStep 5144417 = 3858313) B3858313
theorem B1933183 : Blo 634301 1933183 := bstep (se 1 (by rfl) ⟨1449887, by rfl⟩ : syracuseStep 1933183 = 2899775) B2899775
theorem B1605865 : Blo 634301 1605865 := bstep (se 2 (by rfl) ⟨602199, by rfl⟩ : syracuseStep 1605865 = 1204399) B1204399
theorem B3146051 : Blo 634301 3146051 := bstep (se 1 (by rfl) ⟨2359538, by rfl⟩ : syracuseStep 3146051 = 4719077) B4719077
theorem B11633543 : Blo 634301 11633543 := bstep (se 1 (by rfl) ⟨8725157, by rfl⟩ : syracuseStep 11633543 = 17450315) B17450315
theorem B1606625 : Blo 634301 1606625 := bstep (se 2 (by rfl) ⟨602484, by rfl⟩ : syracuseStep 1606625 = 1204969) B1204969
theorem B951719 : Blo 634301 951719 := bstep (se 1 (by rfl) ⟨713789, by rfl⟩ : syracuseStep 951719 = 1427579) B1427579
theorem B951791 : Blo 634301 951791 := bstep (se 1 (by rfl) ⟨713843, by rfl⟩ : syracuseStep 951791 = 1427687) B1427687
theorem B3212783 : Blo 634301 3212783 := bstep (se 1 (by rfl) ⟨2409587, by rfl⟩ : syracuseStep 3212783 = 4819175) B4819175
theorem B4884563 : Blo 634301 4884563 := bstep (se 1 (by rfl) ⟨3663422, by rfl⟩ : syracuseStep 4884563 = 7326845) B7326845
theorem B3213755 : Blo 634301 3213755 := bstep (se 1 (by rfl) ⟨2410316, by rfl⟩ : syracuseStep 3213755 = 4820633) B4820633
theorem B12192389 : Blo 634301 12192389 := bstep (se 4 (by rfl) ⟨1143036, by rfl⟩ : syracuseStep 12192389 = 2286073) B2286073
theorem B1608457 : Blo 634301 1608457 := bstep (se 2 (by rfl) ⟨603171, by rfl⟩ : syracuseStep 1608457 = 1206343) B1206343
theorem B3443903 : Blo 634301 3443903 := bstep (se 1 (by rfl) ⟨2582927, by rfl⟩ : syracuseStep 3443903 = 5165855) B5165855
theorem B953759 : Blo 634301 953759 := bstep (se 1 (by rfl) ⟨715319, by rfl⟩ : syracuseStep 953759 = 1430639) B1430639
theorem B954395 : Blo 634301 954395 := bstep (se 1 (by rfl) ⟨715796, by rfl⟩ : syracuseStep 954395 = 1431593) B1431593
theorem B4821119 : Blo 634301 4821119 := bstep (se 1 (by rfl) ⟨3615839, by rfl⟩ : syracuseStep 4821119 = 7231679) B7231679
theorem B1380607 : Blo 634301 1380607 := bstep (se 1 (by rfl) ⟨1035455, by rfl⟩ : syracuseStep 1380607 = 2070911) B2070911
theorem B1611647 : Blo 634301 1611647 := bstep (se 1 (by rfl) ⟨1208735, by rfl⟩ : syracuseStep 1611647 = 2417471) B2417471
theorem B956315 : Blo 634301 956315 := bstep (se 1 (by rfl) ⟨717236, by rfl⟩ : syracuseStep 956315 = 1434473) B1434473
theorem B956471 : Blo 634301 956471 := bstep (se 1 (by rfl) ⟨717353, by rfl⟩ : syracuseStep 956471 = 1434707) B1434707
theorem B52795475 : Blo 634301 52795475 := bstep (se 1 (by rfl) ⟨39596606, by rfl⟩ : syracuseStep 52795475 = 79193213) B79193213
theorem B3872933 : Blo 634301 3872933 := bstep (se 4 (by rfl) ⟨363087, by rfl⟩ : syracuseStep 3872933 = 726175) B726175
theorem B1612001 : Blo 634301 1612001 := bstep (se 2 (by rfl) ⟨604500, by rfl⟩ : syracuseStep 1612001 = 1209001) B1209001
theorem B956735 : Blo 634301 956735 := bstep (se 1 (by rfl) ⟨717551, by rfl⟩ : syracuseStep 956735 = 1435103) B1435103
theorem B6626377 : Blo 634301 6626377 := bstep (se 2 (by rfl) ⟨2484891, by rfl⟩ : syracuseStep 6626377 = 4969783) B4969783
theorem B1809823 : Blo 634301 1809823 := bstep (se 1 (by rfl) ⟨1357367, by rfl⟩ : syracuseStep 1809823 = 2714735) B2714735
theorem B24781079 : Blo 634301 24781079 := bstep (se 1 (by rfl) ⟨18585809, by rfl⟩ : syracuseStep 24781079 = 37171619) B37171619
theorem B3220073 : Blo 634301 3220073 := bstep (se 2 (by rfl) ⟨1207527, by rfl⟩ : syracuseStep 3220073 = 2415055) B2415055
theorem B1615079 : Blo 634301 1615079 := bstep (se 1 (by rfl) ⟨1211309, by rfl⟩ : syracuseStep 1615079 = 2422619) B2422619
theorem B3056903 : Blo 634301 3056903 := bstep (se 1 (by rfl) ⟨2292677, by rfl⟩ : syracuseStep 3056903 = 4585355) B4585355
theorem B3450215 : Blo 634301 3450215 := bstep (se 1 (by rfl) ⟨2587661, by rfl⟩ : syracuseStep 3450215 = 5175323) B5175323
theorem B3221369 : Blo 634301 3221369 := bstep (se 2 (by rfl) ⟨1208013, by rfl⟩ : syracuseStep 3221369 = 2416027) B2416027
theorem B634607 : Blo 634301 634607 := bstep (se 1 (by rfl) ⟨475955, by rfl⟩ : syracuseStep 634607 = 951911) B951911
theorem B3616751 : Blo 634301 3616751 := bstep (se 1 (by rfl) ⟨2712563, by rfl⟩ : syracuseStep 3616751 = 5425127) B5425127
theorem B635071 : Blo 634301 635071 := bstep (se 1 (by rfl) ⟨476303, by rfl⟩ : syracuseStep 635071 = 952607) B952607
theorem B635375 : Blo 634301 635375 := bstep (se 1 (by rfl) ⟨476531, by rfl⟩ : syracuseStep 635375 = 953063) B953063
theorem B635775 : Blo 634301 635775 := bstep (se 1 (by rfl) ⟨476831, by rfl⟩ : syracuseStep 635775 = 953663) B953663
theorem B9810881 : Blo 634301 9810881 := bstep (se 2 (by rfl) ⟨3679080, by rfl⟩ : syracuseStep 9810881 = 7358161) B7358161
theorem B635931 : Blo 634301 635931 := bstep (se 1 (by rfl) ⟨476948, by rfl⟩ : syracuseStep 635931 = 953897) B953897
theorem B20657207 : Blo 634301 20657207 := bstep (se 1 (by rfl) ⟨15492905, by rfl⟩ : syracuseStep 20657207 = 30985811) B30985811
theorem B2143529 : Blo 634301 2143529 := bstep (se 2 (by rfl) ⟨803823, by rfl⟩ : syracuseStep 2143529 = 1607647) B1607647
theorem B636519 : Blo 634301 636519 := bstep (se 1 (by rfl) ⟨477389, by rfl⟩ : syracuseStep 636519 = 954779) B954779
theorem B636543 : Blo 634301 636543 := bstep (se 1 (by rfl) ⟨477407, by rfl⟩ : syracuseStep 636543 = 954815) B954815
theorem B6108959 : Blo 634301 6108959 := bstep (se 1 (by rfl) ⟨4581719, by rfl⟩ : syracuseStep 6108959 = 9163439) B9163439
theorem B637167 : Blo 634301 637167 := bstep (se 1 (by rfl) ⟨477875, by rfl⟩ : syracuseStep 637167 = 955751) B955751
theorem B4340087 : Blo 634301 4340087 := bstep (se 1 (by rfl) ⟨3255065, by rfl⟩ : syracuseStep 4340087 = 6510131) B6510131
theorem B637407 : Blo 634301 637407 := bstep (se 1 (by rfl) ⟨478055, by rfl⟩ : syracuseStep 637407 = 956111) B956111
theorem B637423 : Blo 634301 637423 := bstep (se 1 (by rfl) ⟨478067, by rfl⟩ : syracuseStep 637423 = 956135) B956135
theorem B46938773 : Blo 634301 46938773 := bstep (se 6 (by rfl) ⟨1100127, by rfl⟩ : syracuseStep 46938773 = 2200255) B2200255
theorem B637799 : Blo 634301 637799 := bstep (se 1 (by rfl) ⟨478349, by rfl⟩ : syracuseStep 637799 = 956699) B956699
theorem B637947 : Blo 634301 637947 := bstep (se 1 (by rfl) ⟨478460, by rfl⟩ : syracuseStep 637947 = 956921) B956921
theorem B20659769 : Blo 634301 20659769 := bstep (se 2 (by rfl) ⟨7747413, by rfl⟩ : syracuseStep 20659769 = 15494827) B15494827
theorem B3227687 : Blo 634301 3227687 := bstep (se 1 (by rfl) ⟨2420765, by rfl⟩ : syracuseStep 3227687 = 4841531) B4841531
theorem B1032247 : Blo 634301 1032247 := bstep (se 1 (by rfl) ⟨774185, by rfl⟩ : syracuseStep 1032247 = 1548371) B1548371
theorem B2408555 : Blo 634301 2408555 := bstep (se 1 (by rfl) ⟨1806416, by rfl⟩ : syracuseStep 2408555 = 3612833) B3612833
theorem B6865661 : Blo 634301 6865661 := bstep (se 3 (by rfl) ⟨1287311, by rfl⟩ : syracuseStep 6865661 = 2574623) B2574623
theorem B2573245 : Blo 634301 2573245 := bstep (se 3 (by rfl) ⟨482483, by rfl⟩ : syracuseStep 2573245 = 964967) B964967
theorem B12371381 : Blo 634301 12371381 := bstep (se 5 (by rfl) ⟨579908, by rfl⟩ : syracuseStep 12371381 = 1159817) B1159817
theorem B1525223 : Blo 634301 1525223 := bstep (se 1 (by rfl) ⟨1143917, by rfl⟩ : syracuseStep 1525223 = 2287835) B2287835
theorem B23905843 : Blo 634301 23905843 := bstep (se 1 (by rfl) ⟨17929382, by rfl⟩ : syracuseStep 23905843 = 35858765) B35858765
theorem B2181097 : Blo 634301 2181097 := bstep (se 2 (by rfl) ⟨817911, by rfl⟩ : syracuseStep 2181097 = 1635823) B1635823
theorem B3066167 : Blo 634301 3066167 := bstep (se 1 (by rfl) ⟨2299625, by rfl⟩ : syracuseStep 3066167 = 4599251) B4599251
theorem B2148767 : Blo 634301 2148767 := bstep (se 1 (by rfl) ⟨1611575, by rfl⟩ : syracuseStep 2148767 = 3223151) B3223151
theorem B13028609 : Blo 634301 13028609 := bstep (se 2 (by rfl) ⟨4885728, by rfl⟩ : syracuseStep 13028609 = 9771457) B9771457
theorem B76664501 : Blo 634301 76664501 := bstep (se 5 (by rfl) ⟨3593648, by rfl⟩ : syracuseStep 76664501 = 7187297) B7187297
theorem B1429577 : Blo 634301 1429577 := bstep (se 2 (by rfl) ⟨536091, by rfl⟩ : syracuseStep 1429577 = 1072183) B1072183
theorem B3625499 : Blo 634301 3625499 := bstep (se 1 (by rfl) ⟨2719124, by rfl⟩ : syracuseStep 3625499 = 5438249) B5438249
theorem B2577577 : Blo 634301 2577577 := bstep (se 2 (by rfl) ⟨966591, by rfl⟩ : syracuseStep 2577577 = 1933183) B1933183
theorem B1430711 : Blo 634301 1430711 := bstep (se 1 (by rfl) ⟨1073033, by rfl⟩ : syracuseStep 1430711 = 2146067) B2146067
theorem B23254235 : Blo 634301 23254235 := bstep (se 1 (by rfl) ⟨17440676, by rfl⟩ : syracuseStep 23254235 = 34881353) B34881353
theorem B3429611 : Blo 634301 3429611 := bstep (se 1 (by rfl) ⟨2572208, by rfl⟩ : syracuseStep 3429611 = 5144417) B5144417
theorem B1070887 : Blo 634301 1070887 := bstep (se 1 (by rfl) ⟨803165, by rfl⟩ : syracuseStep 1070887 = 1606331) B1606331
theorem B1398811 : Blo 634301 1398811 := bstep (se 1 (by rfl) ⟨1049108, by rfl⟩ : syracuseStep 1398811 = 2098217) B2098217
theorem B1431863 : Blo 634301 1431863 := bstep (se 1 (by rfl) ⟨1073897, by rfl⟩ : syracuseStep 1431863 = 2147795) B2147795
theorem B2415359 : Blo 634301 2415359 := bstep (se 1 (by rfl) ⟨1811519, by rfl⟩ : syracuseStep 2415359 = 3623039) B3623039
theorem B908425 : Blo 634301 908425 := bstep (se 2 (by rfl) ⟨340659, by rfl⟩ : syracuseStep 908425 = 681319) B681319
theorem B1072379 : Blo 634301 1072379 := bstep (se 1 (by rfl) ⟨804284, by rfl⟩ : syracuseStep 1072379 = 1608569) B1608569
theorem B1433159 : Blo 634301 1433159 := bstep (se 1 (by rfl) ⟨1074869, by rfl⟩ : syracuseStep 1433159 = 2149739) B2149739
theorem B1433447 : Blo 634301 1433447 := bstep (se 1 (by rfl) ⟨1075085, by rfl⟩ : syracuseStep 1433447 = 2150171) B2150171
theorem B9167357 : Blo 634301 9167357 := bstep (se 3 (by rfl) ⟨1718879, by rfl⟩ : syracuseStep 9167357 = 3437759) B3437759
theorem B1434761 : Blo 634301 1434761 := bstep (se 2 (by rfl) ⟨538035, by rfl⟩ : syracuseStep 1434761 = 1076071) B1076071
theorem B1434779 : Blo 634301 1434779 := bstep (se 1 (by rfl) ⟨1076084, by rfl⟩ : syracuseStep 1434779 = 2152169) B2152169
theorem B1074559 : Blo 634301 1074559 := bstep (se 1 (by rfl) ⟨805919, by rfl⟩ : syracuseStep 1074559 = 1611839) B1611839
theorem B1205759 : Blo 634301 1205759 := bstep (se 1 (by rfl) ⟨904319, by rfl⟩ : syracuseStep 1205759 = 1808639) B1808639
theorem B46491245 : Blo 634301 46491245 := bstep (se 3 (by rfl) ⟨8717108, by rfl⟩ : syracuseStep 46491245 = 17434217) B17434217
theorem B1533583 : Blo 634301 1533583 := bstep (se 1 (by rfl) ⟨1150187, by rfl⟩ : syracuseStep 1533583 = 2300375) B2300375
theorem B2713247 : Blo 634301 2713247 := bstep (se 1 (by rfl) ⟨2034935, by rfl⟩ : syracuseStep 2713247 = 4069871) B4069871
theorem B2713283 : Blo 634301 2713283 := bstep (se 1 (by rfl) ⟨2034962, by rfl⟩ : syracuseStep 2713283 = 4069925) B4069925
theorem B1435463 : Blo 634301 1435463 := bstep (se 1 (by rfl) ⟨1076597, by rfl⟩ : syracuseStep 1435463 = 2153195) B2153195
theorem B1435751 : Blo 634301 1435751 := bstep (se 1 (by rfl) ⟨1076813, by rfl⟩ : syracuseStep 1435751 = 2153627) B2153627
theorem B1469281 : Blo 634301 1469281 := bstep (se 2 (by rfl) ⟨550980, by rfl⟩ : syracuseStep 1469281 = 1101961) B1101961
theorem B1076105 : Blo 634301 1076105 := bstep (se 2 (by rfl) ⟨403539, by rfl⟩ : syracuseStep 1076105 = 807079) B807079
theorem B715711 : Blo 634301 715711 := bstep (se 1 (by rfl) ⟨536783, by rfl⟩ : syracuseStep 715711 = 1073567) B1073567
theorem B1076159 : Blo 634301 1076159 := bstep (se 1 (by rfl) ⟨807119, by rfl⟩ : syracuseStep 1076159 = 1614239) B1614239
theorem B22015435 : Blo 634301 22015435 := bstep (se 1 (by rfl) ⟨16511576, by rfl⟩ : syracuseStep 22015435 = 33023153) B33023153
theorem B6876647 : Blo 634301 6876647 := bstep (se 1 (by rfl) ⟨5157485, by rfl⟩ : syracuseStep 6876647 = 10314971) B10314971
theorem B2716649 : Blo 634301 2716649 := bstep (se 2 (by rfl) ⟨1018743, by rfl⟩ : syracuseStep 2716649 = 2037487) B2037487
theorem B718015 : Blo 634301 718015 := bstep (se 1 (by rfl) ⟨538511, by rfl⟩ : syracuseStep 718015 = 1077023) B1077023
theorem B3634703 : Blo 634301 3634703 := bstep (se 1 (by rfl) ⟨2726027, by rfl⟩ : syracuseStep 3634703 = 5452055) B5452055
theorem B2586623 : Blo 634301 2586623 := bstep (se 1 (by rfl) ⟨1939967, by rfl⟩ : syracuseStep 2586623 = 3879935) B3879935
theorem B7240427 : Blo 634301 7240427 := bstep (se 1 (by rfl) ⟨5430320, by rfl⟩ : syracuseStep 7240427 = 10860641) B10860641
theorem B2587403 : Blo 634301 2587403 := bstep (se 1 (by rfl) ⟨1940552, by rfl⟩ : syracuseStep 2587403 = 3881105) B3881105
theorem B1605703 : Blo 634301 1605703 := bstep (se 1 (by rfl) ⟨1204277, by rfl⟩ : syracuseStep 1605703 = 2408555) B2408555
theorem B5505317 : Blo 634301 5505317 := bstep (se 4 (by rfl) ⟨516123, by rfl⟩ : syracuseStep 5505317 = 1032247) B1032247
theorem B8389469 : Blo 634301 8389469 := bstep (se 3 (by rfl) ⟨1573025, by rfl⟩ : syracuseStep 8389469 = 3146051) B3146051
theorem B1016815 : Blo 634301 1016815 := bstep (se 1 (by rfl) ⟨762611, by rfl⟩ : syracuseStep 1016815 = 1525223) B1525223
theorem B24446285 : Blo 634301 24446285 := bstep (se 3 (by rfl) ⟨4583678, by rfl⟩ : syracuseStep 24446285 = 9167357) B9167357
theorem B8128259 : Blo 634301 8128259 := bstep (se 1 (by rfl) ⟨6096194, by rfl⟩ : syracuseStep 8128259 = 12192389) B12192389
theorem B2295935 : Blo 634301 2295935 := bstep (se 1 (by rfl) ⟨1721951, by rfl⟩ : syracuseStep 2295935 = 3443903) B3443903
theorem B8685739 : Blo 634301 8685739 := bstep (se 1 (by rfl) ⟨6514304, by rfl⟩ : syracuseStep 8685739 = 13028609) B13028609
theorem B953051 : Blo 634301 953051 := bstep (se 1 (by rfl) ⟨714788, by rfl⟩ : syracuseStep 953051 = 1429577) B1429577
theorem B3214079 : Blo 634301 3214079 := bstep (se 1 (by rfl) ⟨2410559, by rfl⟩ : syracuseStep 3214079 = 4821119) B4821119
theorem B953807 : Blo 634301 953807 := bstep (se 1 (by rfl) ⟨715355, by rfl⟩ : syracuseStep 953807 = 1430711) B1430711
theorem B15502823 : Blo 634301 15502823 := bstep (se 1 (by rfl) ⟨11627117, by rfl⟩ : syracuseStep 15502823 = 23254235) B23254235
theorem B954281 : Blo 634301 954281 := bstep (se 2 (by rfl) ⟨357855, by rfl⟩ : syracuseStep 954281 = 715711) B715711
theorem B35196983 : Blo 634301 35196983 := bstep (se 1 (by rfl) ⟨26397737, by rfl⟩ : syracuseStep 35196983 = 52795475) B52795475
theorem B954575 : Blo 634301 954575 := bstep (se 1 (by rfl) ⟨715931, by rfl⟩ : syracuseStep 954575 = 1431863) B1431863
theorem B1610239 : Blo 634301 1610239 := bstep (se 1 (by rfl) ⟨1207679, by rfl⟩ : syracuseStep 1610239 = 2415359) B2415359
theorem B955439 : Blo 634301 955439 := bstep (se 1 (by rfl) ⟨716579, by rfl⟩ : syracuseStep 955439 = 1433159) B1433159
theorem B955631 : Blo 634301 955631 := bstep (se 1 (by rfl) ⟨716723, by rfl⟩ : syracuseStep 955631 = 1433447) B1433447
theorem B16520719 : Blo 634301 16520719 := bstep (se 1 (by rfl) ⟨12390539, by rfl⟩ : syracuseStep 16520719 = 24781079) B24781079
theorem B956507 : Blo 634301 956507 := bstep (se 1 (by rfl) ⟨717380, by rfl⟩ : syracuseStep 956507 = 1434761) B1434761
theorem B956519 : Blo 634301 956519 := bstep (se 1 (by rfl) ⟨717389, by rfl⟩ : syracuseStep 956519 = 1434779) B1434779
theorem B2037935 : Blo 634301 2037935 := bstep (se 1 (by rfl) ⟨1528451, by rfl⟩ : syracuseStep 2037935 = 3056903) B3056903
theorem B1808831 : Blo 634301 1808831 := bstep (se 1 (by rfl) ⟨1356623, by rfl⟩ : syracuseStep 1808831 = 2713247) B2713247
theorem B1808855 : Blo 634301 1808855 := bstep (se 1 (by rfl) ⟨1356641, by rfl⟩ : syracuseStep 1808855 = 2713283) B2713283
theorem B956975 : Blo 634301 956975 := bstep (se 1 (by rfl) ⟨717731, by rfl⟩ : syracuseStep 956975 = 1435463) B1435463
theorem B957167 : Blo 634301 957167 := bstep (se 1 (by rfl) ⟨717875, by rfl⟩ : syracuseStep 957167 = 1435751) B1435751
theorem B957353 : Blo 634301 957353 := bstep (se 2 (by rfl) ⟨359007, by rfl⟩ : syracuseStep 957353 = 718015) B718015
theorem B1811099 : Blo 634301 1811099 := bstep (se 1 (by rfl) ⟨1358324, by rfl⟩ : syracuseStep 1811099 = 2716649) B2716649
theorem B13771471 : Blo 634301 13771471 := bstep (se 1 (by rfl) ⟨10328603, by rfl⟩ : syracuseStep 13771471 = 20657207) B20657207
theorem B4072639 : Blo 634301 4072639 := bstep (se 1 (by rfl) ⟨3054479, by rfl⟩ : syracuseStep 4072639 = 6108959) B6108959
theorem B2893391 : Blo 634301 2893391 := bstep (se 1 (by rfl) ⟨2170043, by rfl⟩ : syracuseStep 2893391 = 4340087) B4340087
theorem B4826951 : Blo 634301 4826951 := bstep (se 1 (by rfl) ⟨3620213, by rfl⟩ : syracuseStep 4826951 = 7240427) B7240427
theorem B13773179 : Blo 634301 13773179 := bstep (se 1 (by rfl) ⟨10329884, by rfl⟩ : syracuseStep 13773179 = 20659769) B20659769
theorem B2141153 : Blo 634301 2141153 := bstep (se 2 (by rfl) ⟨802932, by rfl⟩ : syracuseStep 2141153 = 1605865) B1605865
theorem B634479 : Blo 634301 634479 := bstep (se 1 (by rfl) ⟨475859, by rfl⟩ : syracuseStep 634479 = 951719) B951719
theorem B634527 : Blo 634301 634527 := bstep (se 1 (by rfl) ⟨475895, by rfl⟩ : syracuseStep 634527 = 951791) B951791
theorem B2141855 : Blo 634301 2141855 := bstep (se 1 (by rfl) ⟨1606391, by rfl⟩ : syracuseStep 2141855 = 3212783) B3212783
theorem B3256375 : Blo 634301 3256375 := bstep (se 1 (by rfl) ⟨2442281, by rfl⟩ : syracuseStep 3256375 = 4884563) B4884563
theorem B2044111 : Blo 634301 2044111 := bstep (se 1 (by rfl) ⟨1533083, by rfl⟩ : syracuseStep 2044111 = 3066167) B3066167
theorem B2142503 : Blo 634301 2142503 := bstep (se 1 (by rfl) ⟨1606877, by rfl⟩ : syracuseStep 2142503 = 3213755) B3213755
theorem B2044777 : Blo 634301 2044777 := bstep (se 2 (by rfl) ⟨766791, by rfl⟩ : syracuseStep 2044777 = 1533583) B1533583
theorem B635839 : Blo 634301 635839 := bstep (se 1 (by rfl) ⟨476879, by rfl⟩ : syracuseStep 635839 = 953759) B953759
theorem B636263 : Blo 634301 636263 := bstep (se 1 (by rfl) ⟨477197, by rfl⟩ : syracuseStep 636263 = 954395) B954395
theorem B2144609 : Blo 634301 2144609 := bstep (se 2 (by rfl) ⟨804228, by rfl⟩ : syracuseStep 2144609 = 1608457) B1608457
theorem B637543 : Blo 634301 637543 := bstep (se 1 (by rfl) ⟨478157, by rfl⟩ : syracuseStep 637543 = 956315) B956315
theorem B637647 : Blo 634301 637647 := bstep (se 1 (by rfl) ⟨478235, by rfl⟩ : syracuseStep 637647 = 956471) B956471
theorem B637823 : Blo 634301 637823 := bstep (se 1 (by rfl) ⟨478367, by rfl⟩ : syracuseStep 637823 = 956735) B956735
theorem B2146715 : Blo 634301 2146715 := bstep (se 1 (by rfl) ⟨1610036, by rfl⟩ : syracuseStep 2146715 = 3220073) B3220073
theorem B803839 : Blo 634301 803839 := bstep (se 1 (by rfl) ⟨602879, by rfl⟩ : syracuseStep 803839 = 1205759) B1205759
theorem B2147579 : Blo 634301 2147579 := bstep (se 1 (by rfl) ⟨1610684, by rfl⟩ : syracuseStep 2147579 = 3221369) B3221369
theorem B6899741 : Blo 634301 6899741 := bstep (se 3 (by rfl) ⟨1293701, by rfl⟩ : syracuseStep 6899741 = 2587403) B2587403
theorem B1427849 : Blo 634301 1427849 := bstep (se 2 (by rfl) ⟨535443, by rfl⟩ : syracuseStep 1427849 = 1070887) B1070887
theorem B2411167 : Blo 634301 2411167 := bstep (se 1 (by rfl) ⟨1808375, by rfl⟩ : syracuseStep 2411167 = 3616751) B3616751
theorem B6540587 : Blo 634301 6540587 := bstep (se 1 (by rfl) ⟨4905440, by rfl⟩ : syracuseStep 6540587 = 9810881) B9810881
theorem B1429019 : Blo 634301 1429019 := bstep (se 1 (by rfl) ⟨1071764, by rfl⟩ : syracuseStep 1429019 = 2143529) B2143529
theorem B8835169 : Blo 634301 8835169 := bstep (se 2 (by rfl) ⟨3313188, by rfl⟩ : syracuseStep 8835169 = 6626377) B6626377
theorem B2413097 : Blo 634301 2413097 := bstep (se 2 (by rfl) ⟨904911, by rfl⟩ : syracuseStep 2413097 = 1809823) B1809823
theorem B2151791 : Blo 634301 2151791 := bstep (se 1 (by rfl) ⟨1613843, by rfl⟩ : syracuseStep 2151791 = 3227687) B3227687
theorem B4577107 : Blo 634301 4577107 := bstep (se 1 (by rfl) ⟨3432830, by rfl⟩ : syracuseStep 4577107 = 6865661) B6865661
theorem B7755695 : Blo 634301 7755695 := bstep (se 1 (by rfl) ⟨5816771, by rfl⟩ : syracuseStep 7755695 = 11633543) B11633543
theorem B1071083 : Blo 634301 1071083 := bstep (se 1 (by rfl) ⟨803312, by rfl⟩ : syracuseStep 1071083 = 1606625) B1606625
theorem B8247587 : Blo 634301 8247587 := bstep (se 1 (by rfl) ⟨6185690, by rfl⟩ : syracuseStep 8247587 = 12371381) B12371381
theorem B3430993 : Blo 634301 3430993 := bstep (se 2 (by rfl) ⟨1286622, by rfl⟩ : syracuseStep 3430993 = 2573245) B2573245
theorem B7363237 : Blo 634301 7363237 := bstep (se 4 (by rfl) ⟨690303, by rfl⟩ : syracuseStep 7363237 = 1380607) B1380607
theorem B1432511 : Blo 634301 1432511 := bstep (se 1 (by rfl) ⟨1074383, by rfl⟩ : syracuseStep 1432511 = 2148767) B2148767
theorem B1432745 : Blo 634301 1432745 := bstep (se 2 (by rfl) ⟨537279, by rfl⟩ : syracuseStep 1432745 = 1074559) B1074559
theorem B51109667 : Blo 634301 51109667 := bstep (se 1 (by rfl) ⟨38332250, by rfl⟩ : syracuseStep 51109667 = 76664501) B76664501
theorem B2416999 : Blo 634301 2416999 := bstep (se 1 (by rfl) ⟨1812749, by rfl⟩ : syracuseStep 2416999 = 3625499) B3625499
theorem B2286407 : Blo 634301 2286407 := bstep (se 1 (by rfl) ⟨1714805, by rfl⟩ : syracuseStep 2286407 = 3429611) B3429611
theorem B9200573 : Blo 634301 9200573 := bstep (se 3 (by rfl) ⟨1725107, by rfl⟩ : syracuseStep 9200573 = 3450215) B3450215
theorem B1959041 : Blo 634301 1959041 := bstep (se 2 (by rfl) ⟨734640, by rfl⟩ : syracuseStep 1959041 = 1469281) B1469281
theorem B1074431 : Blo 634301 1074431 := bstep (se 1 (by rfl) ⟨805823, by rfl⟩ : syracuseStep 1074431 = 1611647) B1611647
theorem B2581955 : Blo 634301 2581955 := bstep (se 1 (by rfl) ⟨1936466, by rfl⟩ : syracuseStep 2581955 = 3872933) B3872933
theorem B1074667 : Blo 634301 1074667 := bstep (se 1 (by rfl) ⟨806000, by rfl⟩ : syracuseStep 1074667 = 1612001) B1612001
theorem B29353913 : Blo 634301 29353913 := bstep (se 2 (by rfl) ⟨11007717, by rfl⟩ : syracuseStep 29353913 = 22015435) B22015435
theorem B714919 : Blo 634301 714919 := bstep (se 1 (by rfl) ⟨536189, by rfl⟩ : syracuseStep 714919 = 1072379) B1072379
theorem B4844933 : Blo 634301 4844933 := bstep (se 4 (by rfl) ⟨454212, by rfl⟩ : syracuseStep 4844933 = 908425) B908425
theorem B1076719 : Blo 634301 1076719 := bstep (se 1 (by rfl) ⟨807539, by rfl⟩ : syracuseStep 1076719 = 1615079) B1615079
theorem B30994163 : Blo 634301 30994163 := bstep (se 1 (by rfl) ⟨23245622, by rfl⟩ : syracuseStep 30994163 = 46491245) B46491245
theorem B3436769 : Blo 634301 3436769 := bstep (se 2 (by rfl) ⟨1288788, by rfl⟩ : syracuseStep 3436769 = 2577577) B2577577
theorem B717403 : Blo 634301 717403 := bstep (se 1 (by rfl) ⟨538052, by rfl⟩ : syracuseStep 717403 = 1076105) B1076105
theorem B717439 : Blo 634301 717439 := bstep (se 1 (by rfl) ⟨538079, by rfl⟩ : syracuseStep 717439 = 1076159) B1076159
theorem B4584431 : Blo 634301 4584431 := bstep (se 1 (by rfl) ⟨3438323, by rfl⟩ : syracuseStep 4584431 = 6876647) B6876647
theorem B1865081 : Blo 634301 1865081 := bstep (se 2 (by rfl) ⟨699405, by rfl⟩ : syracuseStep 1865081 = 1398811) B1398811
theorem B127497829 : Blo 634301 127497829 := bstep (se 4 (by rfl) ⟨11952921, by rfl⟩ : syracuseStep 127497829 = 23905843) B23905843
theorem B2423135 : Blo 634301 2423135 := bstep (se 1 (by rfl) ⟨1817351, by rfl⟩ : syracuseStep 2423135 = 3634703) B3634703
theorem B31292515 : Blo 634301 31292515 := bstep (se 1 (by rfl) ⟨23469386, by rfl⟩ : syracuseStep 31292515 = 46938773) B46938773
theorem B11632517 : Blo 634301 11632517 := bstep (se 4 (by rfl) ⟨1090548, by rfl⟩ : syracuseStep 11632517 = 2181097) B2181097
theorem B27590645 : Blo 634301 27590645 := bstep (se 5 (by rfl) ⟨1293311, by rfl⟩ : syracuseStep 27590645 = 2586623) B2586623
theorem B3670211 : Blo 634301 3670211 := bstep (se 1 (by rfl) ⟨2752658, by rfl⟩ : syracuseStep 3670211 = 5505317) B5505317
theorem B951899 : Blo 634301 951899 := bstep (se 1 (by rfl) ⟨713924, by rfl⟩ : syracuseStep 951899 = 1427849) B1427849
theorem B4360391 : Blo 634301 4360391 := bstep (se 1 (by rfl) ⟨3270293, by rfl⟩ : syracuseStep 4360391 = 6540587) B6540587
theorem B952679 : Blo 634301 952679 := bstep (se 1 (by rfl) ⟨714509, by rfl⟩ : syracuseStep 952679 = 1429019) B1429019
theorem B23464655 : Blo 634301 23464655 := bstep (se 1 (by rfl) ⟨17598491, by rfl⟩ : syracuseStep 23464655 = 35196983) B35196983
theorem B953225 : Blo 634301 953225 := bstep (se 2 (by rfl) ⟨357459, by rfl⟩ : syracuseStep 953225 = 714919) B714919
theorem B1608731 : Blo 634301 1608731 := bstep (se 1 (by rfl) ⟨1206548, by rfl⟩ : syracuseStep 1608731 = 2413097) B2413097
theorem B3214889 : Blo 634301 3214889 := bstep (se 2 (by rfl) ⟨1205583, by rfl⟩ : syracuseStep 3214889 = 2411167) B2411167
theorem B955007 : Blo 634301 955007 := bstep (se 1 (by rfl) ⟨716255, by rfl⟩ : syracuseStep 955007 = 1432511) B1432511
theorem B955163 : Blo 634301 955163 := bstep (se 1 (by rfl) ⟨716372, by rfl⟩ : syracuseStep 955163 = 1432745) B1432745
theorem B2725481 : Blo 634301 2725481 := bstep (se 2 (by rfl) ⟨1022055, by rfl⟩ : syracuseStep 2725481 = 2044111) B2044111
theorem B6133715 : Blo 634301 6133715 := bstep (se 1 (by rfl) ⟨4600286, by rfl⟩ : syracuseStep 6133715 = 9200573) B9200573
theorem B21993565 : Blo 634301 21993565 := bstep (se 3 (by rfl) ⟨4123793, by rfl⟩ : syracuseStep 21993565 = 8247587) B8247587
theorem B956537 : Blo 634301 956537 := bstep (se 2 (by rfl) ⟨358701, by rfl⟩ : syracuseStep 956537 = 717403) B717403
theorem B956585 : Blo 634301 956585 := bstep (se 2 (by rfl) ⟨358719, by rfl⟩ : syracuseStep 956585 = 717439) B717439
theorem B2726369 : Blo 634301 2726369 := bstep (se 2 (by rfl) ⟨1022388, by rfl⟩ : syracuseStep 2726369 = 2044777) B2044777
theorem B4823549 : Blo 634301 4823549 := bstep (se 3 (by rfl) ⟨904415, by rfl⟩ : syracuseStep 4823549 = 1808831) B1808831
theorem B3217967 : Blo 634301 3217967 := bstep (se 1 (by rfl) ⟨2413475, by rfl⟩ : syracuseStep 3217967 = 4826951) B4826951
theorem B19569275 : Blo 634301 19569275 := bstep (se 1 (by rfl) ⟨14676956, by rfl⟩ : syracuseStep 19569275 = 29353913) B29353913
theorem B22027625 : Blo 634301 22027625 := bstep (se 2 (by rfl) ⟨8260359, by rfl⟩ : syracuseStep 22027625 = 16520719) B16520719
theorem B6102809 : Blo 634301 6102809 := bstep (se 2 (by rfl) ⟨2288553, by rfl⟩ : syracuseStep 6102809 = 4577107) B4577107
theorem B3056287 : Blo 634301 3056287 := bstep (se 1 (by rfl) ⟨2292215, by rfl⟩ : syracuseStep 3056287 = 4584431) B4584431
theorem B41723353 : Blo 634301 41723353 := bstep (se 2 (by rfl) ⟨15646257, by rfl⟩ : syracuseStep 41723353 = 31292515) B31292515
theorem B1615423 : Blo 634301 1615423 := bstep (se 1 (by rfl) ⟨1211567, by rfl⟩ : syracuseStep 1615423 = 2423135) B2423135
theorem B18393763 : Blo 634301 18393763 := bstep (se 1 (by rfl) ⟨13795322, by rfl⟩ : syracuseStep 18393763 = 27590645) B27590645
theorem B2140937 : Blo 634301 2140937 := bstep (se 2 (by rfl) ⟨802851, by rfl⟩ : syracuseStep 2140937 = 1605703) B1605703
theorem B3222665 : Blo 634301 3222665 := bstep (se 2 (by rfl) ⟨1208499, by rfl⟩ : syracuseStep 3222665 = 2416999) B2416999
theorem B16297523 : Blo 634301 16297523 := bstep (se 1 (by rfl) ⟨12223142, by rfl⟩ : syracuseStep 16297523 = 24446285) B24446285
theorem B18361961 : Blo 634301 18361961 := bstep (se 2 (by rfl) ⟨6885735, by rfl⟩ : syracuseStep 18361961 = 13771471) B13771471
theorem B5418839 : Blo 634301 5418839 := bstep (se 1 (by rfl) ⟨4064129, by rfl⟩ : syracuseStep 5418839 = 8128259) B8128259
theorem B1355753 : Blo 634301 1355753 := bstep (se 2 (by rfl) ⟨508407, by rfl⟩ : syracuseStep 1355753 = 1016815) B1016815
theorem B4599827 : Blo 634301 4599827 := bstep (se 1 (by rfl) ⟨3449870, by rfl⟩ : syracuseStep 4599827 = 6899741) B6899741
theorem B635367 : Blo 634301 635367 := bstep (se 1 (by rfl) ⟨476525, by rfl⟩ : syracuseStep 635367 = 953051) B953051
theorem B2142719 : Blo 634301 2142719 := bstep (se 1 (by rfl) ⟨1607039, by rfl⟩ : syracuseStep 2142719 = 3214079) B3214079
theorem B635871 : Blo 634301 635871 := bstep (se 1 (by rfl) ⟨476903, by rfl⟩ : syracuseStep 635871 = 953807) B953807
theorem B10335215 : Blo 634301 10335215 := bstep (se 1 (by rfl) ⟨7751411, by rfl⟩ : syracuseStep 10335215 = 15502823) B15502823
theorem B636187 : Blo 634301 636187 := bstep (se 1 (by rfl) ⟨477140, by rfl⟩ : syracuseStep 636187 = 954281) B954281
theorem B636383 : Blo 634301 636383 := bstep (se 1 (by rfl) ⟨477287, by rfl⟩ : syracuseStep 636383 = 954575) B954575
theorem B11580985 : Blo 634301 11580985 := bstep (se 2 (by rfl) ⟨4342869, by rfl⟩ : syracuseStep 11580985 = 8685739) B8685739
theorem B636959 : Blo 634301 636959 := bstep (se 1 (by rfl) ⟨477719, by rfl⟩ : syracuseStep 636959 = 955439) B955439
theorem B637087 : Blo 634301 637087 := bstep (se 1 (by rfl) ⟨477815, by rfl⟩ : syracuseStep 637087 = 955631) B955631
theorem B637671 : Blo 634301 637671 := bstep (se 1 (by rfl) ⟨478253, by rfl⟩ : syracuseStep 637671 = 956507) B956507
theorem B637679 : Blo 634301 637679 := bstep (se 1 (by rfl) ⟨478259, by rfl⟩ : syracuseStep 637679 = 956519) B956519
theorem B1358623 : Blo 634301 1358623 := bstep (se 1 (by rfl) ⟨1018967, by rfl⟩ : syracuseStep 1358623 = 2037935) B2037935
theorem B637983 : Blo 634301 637983 := bstep (se 1 (by rfl) ⟨478487, by rfl⟩ : syracuseStep 637983 = 956975) B956975
theorem B638111 : Blo 634301 638111 := bstep (se 1 (by rfl) ⟨478583, by rfl⟩ : syracuseStep 638111 = 957167) B957167
theorem B638235 : Blo 634301 638235 := bstep (se 1 (by rfl) ⟨478676, by rfl⟩ : syracuseStep 638235 = 957353) B957353
theorem B4341833 : Blo 634301 4341833 := bstep (se 2 (by rfl) ⟨1628187, by rfl⟩ : syracuseStep 4341833 = 3256375) B3256375
theorem B11780225 : Blo 634301 11780225 := bstep (se 2 (by rfl) ⟨4417584, by rfl⟩ : syracuseStep 11780225 = 8835169) B8835169
theorem B1524271 : Blo 634301 1524271 := bstep (se 1 (by rfl) ⟨1143203, by rfl⟩ : syracuseStep 1524271 = 2286407) B2286407
theorem B2146985 : Blo 634301 2146985 := bstep (se 2 (by rfl) ⟨805119, by rfl⟩ : syracuseStep 2146985 = 1610239) B1610239
theorem B1721303 : Blo 634301 1721303 := bstep (se 1 (by rfl) ⟨1290977, by rfl⟩ : syracuseStep 1721303 = 2581955) B2581955
theorem B1427435 : Blo 634301 1427435 := bstep (se 1 (by rfl) ⟨1070576, by rfl⟩ : syracuseStep 1427435 = 2141153) B2141153
theorem B3229955 : Blo 634301 3229955 := bstep (se 1 (by rfl) ⟨2422466, by rfl⟩ : syracuseStep 3229955 = 4844933) B4844933
theorem B1427903 : Blo 634301 1427903 := bstep (se 1 (by rfl) ⟨1070927, by rfl⟩ : syracuseStep 1427903 = 2141855) B2141855
theorem B20662775 : Blo 634301 20662775 := bstep (se 1 (by rfl) ⟨15497081, by rfl⟩ : syracuseStep 20662775 = 30994163) B30994163
theorem B1428335 : Blo 634301 1428335 := bstep (se 1 (by rfl) ⟨1071251, by rfl⟩ : syracuseStep 1428335 = 2142503) B2142503
theorem B4574657 : Blo 634301 4574657 := bstep (se 2 (by rfl) ⟨1715496, by rfl⟩ : syracuseStep 4574657 = 3430993) B3430993
theorem B9817649 : Blo 634301 9817649 := bstep (se 2 (by rfl) ⟨3681618, by rfl⟩ : syracuseStep 9817649 = 7363237) B7363237
theorem B1429739 : Blo 634301 1429739 := bstep (se 1 (by rfl) ⟨1072304, by rfl⟩ : syracuseStep 1429739 = 2144609) B2144609
theorem B7755011 : Blo 634301 7755011 := bstep (se 1 (by rfl) ⟨5816258, by rfl⟩ : syracuseStep 7755011 = 11632517) B11632517
theorem B1431143 : Blo 634301 1431143 := bstep (se 1 (by rfl) ⟨1073357, by rfl⟩ : syracuseStep 1431143 = 2146715) B2146715
theorem B5592979 : Blo 634301 5592979 := bstep (se 1 (by rfl) ⟨4194734, by rfl⟩ : syracuseStep 5592979 = 8389469) B8389469
theorem B1431719 : Blo 634301 1431719 := bstep (se 1 (by rfl) ⟨1073789, by rfl⟩ : syracuseStep 1431719 = 2147579) B2147579
theorem B1071785 : Blo 634301 1071785 := bstep (se 2 (by rfl) ⟨401919, by rfl⟩ : syracuseStep 1071785 = 803839) B803839
theorem B1530623 : Blo 634301 1530623 := bstep (se 1 (by rfl) ⟨1147967, by rfl⟩ : syracuseStep 1530623 = 2295935) B2295935
theorem B5430185 : Blo 634301 5430185 := bstep (se 2 (by rfl) ⟨2036319, by rfl⟩ : syracuseStep 5430185 = 4072639) B4072639
theorem B1432889 : Blo 634301 1432889 := bstep (se 2 (by rfl) ⟨537333, by rfl⟩ : syracuseStep 1432889 = 1074667) B1074667
theorem B1434527 : Blo 634301 1434527 := bstep (se 1 (by rfl) ⟨1075895, by rfl⟩ : syracuseStep 1434527 = 2151791) B2151791
theorem B5170463 : Blo 634301 5170463 := bstep (se 1 (by rfl) ⟨3877847, by rfl⟩ : syracuseStep 5170463 = 7755695) B7755695
theorem B714055 : Blo 634301 714055 := bstep (se 1 (by rfl) ⟨535541, by rfl⟩ : syracuseStep 714055 = 1071083) B1071083
theorem B1205903 : Blo 634301 1205903 := bstep (se 1 (by rfl) ⟨904427, by rfl⟩ : syracuseStep 1205903 = 1808855) B1808855
theorem B1435625 : Blo 634301 1435625 := bstep (se 2 (by rfl) ⟨538359, by rfl⟩ : syracuseStep 1435625 = 1076719) B1076719
theorem B34073111 : Blo 634301 34073111 := bstep (se 1 (by rfl) ⟨25554833, by rfl⟩ : syracuseStep 34073111 = 51109667) B51109667
theorem B1207399 : Blo 634301 1207399 := bstep (se 1 (by rfl) ⟨905549, by rfl⟩ : syracuseStep 1207399 = 1811099) B1811099
theorem B1306027 : Blo 634301 1306027 := bstep (se 1 (by rfl) ⟨979520, by rfl⟩ : syracuseStep 1306027 = 1959041) B1959041
theorem B716287 : Blo 634301 716287 := bstep (se 1 (by rfl) ⟨537215, by rfl⟩ : syracuseStep 716287 = 1074431) B1074431
theorem B36728477 : Blo 634301 36728477 := bstep (se 3 (by rfl) ⟨6886589, by rfl⟩ : syracuseStep 36728477 = 13773179) B13773179
theorem B1928927 : Blo 634301 1928927 := bstep (se 1 (by rfl) ⟨1446695, by rfl⟩ : syracuseStep 1928927 = 2893391) B2893391
theorem B169997105 : Blo 634301 169997105 := bstep (se 2 (by rfl) ⟨63748914, by rfl⟩ : syracuseStep 169997105 = 127497829) B127497829
theorem B2291179 : Blo 634301 2291179 := bstep (se 1 (by rfl) ⟨1718384, by rfl⟩ : syracuseStep 2291179 = 3436769) B3436769
theorem B1243387 : Blo 634301 1243387 := bstep (se 1 (by rfl) ⟨932540, by rfl⟩ : syracuseStep 1243387 = 1865081) B1865081
theorem B1147535 : Blo 634301 1147535 := bstep (se 1 (by rfl) ⟨860651, by rfl⟩ : syracuseStep 1147535 = 1721303) B1721303
theorem B2032361 : Blo 634301 2032361 := bstep (se 2 (by rfl) ⟨762135, by rfl⟩ : syracuseStep 2032361 = 1524271) B1524271
theorem B951623 : Blo 634301 951623 := bstep (se 1 (by rfl) ⟨713717, by rfl⟩ : syracuseStep 951623 = 1427435) B1427435
theorem B951935 : Blo 634301 951935 := bstep (se 1 (by rfl) ⟨713951, by rfl⟩ : syracuseStep 951935 = 1427903) B1427903
theorem B952073 : Blo 634301 952073 := bstep (se 2 (by rfl) ⟨357027, by rfl⟩ : syracuseStep 952073 = 714055) B714055
theorem B952223 : Blo 634301 952223 := bstep (se 1 (by rfl) ⟨714167, by rfl⟩ : syracuseStep 952223 = 1428335) B1428335
theorem B953159 : Blo 634301 953159 := bstep (se 1 (by rfl) ⟨714869, by rfl⟩ : syracuseStep 953159 = 1429739) B1429739
theorem B954095 : Blo 634301 954095 := bstep (se 1 (by rfl) ⟨715571, by rfl⟩ : syracuseStep 954095 = 1431143) B1431143
theorem B954479 : Blo 634301 954479 := bstep (se 1 (by rfl) ⟨715859, by rfl⟩ : syracuseStep 954479 = 1431719) B1431719
theorem B1609865 : Blo 634301 1609865 := bstep (se 2 (by rfl) ⟨603699, by rfl⟩ : syracuseStep 1609865 = 1207399) B1207399
theorem B3215699 : Blo 634301 3215699 := bstep (se 1 (by rfl) ⟨2411774, by rfl⟩ : syracuseStep 3215699 = 4823549) B4823549
theorem B13046183 : Blo 634301 13046183 := bstep (se 1 (by rfl) ⟨9784637, by rfl⟩ : syracuseStep 13046183 = 19569275) B19569275
theorem B955049 : Blo 634301 955049 := bstep (se 2 (by rfl) ⟨358143, by rfl⟩ : syracuseStep 955049 = 716287) B716287
theorem B955259 : Blo 634301 955259 := bstep (se 1 (by rfl) ⟨716444, by rfl⟩ : syracuseStep 955259 = 1432889) B1432889
theorem B14685083 : Blo 634301 14685083 := bstep (se 1 (by rfl) ⟨11013812, by rfl⟩ : syracuseStep 14685083 = 22027625) B22027625
theorem B4068539 : Blo 634301 4068539 := bstep (se 1 (by rfl) ⟨3051404, by rfl⟩ : syracuseStep 4068539 = 6102809) B6102809
theorem B956351 : Blo 634301 956351 := bstep (se 1 (by rfl) ⟨717263, by rfl⟩ : syracuseStep 956351 = 1434527) B1434527
theorem B3446975 : Blo 634301 3446975 := bstep (se 1 (by rfl) ⟨2585231, by rfl⟩ : syracuseStep 3446975 = 5170463) B5170463
theorem B957083 : Blo 634301 957083 := bstep (se 1 (by rfl) ⟨717812, by rfl⟩ : syracuseStep 957083 = 1435625) B1435625
theorem B22715407 : Blo 634301 22715407 := bstep (se 1 (by rfl) ⟨17036555, by rfl⟩ : syracuseStep 22715407 = 34073111) B34073111
theorem B3054905 : Blo 634301 3054905 := bstep (se 2 (by rfl) ⟨1145589, by rfl⟩ : syracuseStep 3054905 = 2291179) B2291179
theorem B24485651 : Blo 634301 24485651 := bstep (se 1 (by rfl) ⟨18364238, by rfl⟩ : syracuseStep 24485651 = 36728477) B36728477
theorem B1285951 : Blo 634301 1285951 := bstep (se 1 (by rfl) ⟨964463, by rfl⟩ : syracuseStep 1285951 = 1928927) B1928927
theorem B3612559 : Blo 634301 3612559 := bstep (se 1 (by rfl) ⟨2709419, by rfl⟩ : syracuseStep 3612559 = 5418839) B5418839
theorem B6890143 : Blo 634301 6890143 := bstep (se 1 (by rfl) ⟨5167607, by rfl⟩ : syracuseStep 6890143 = 10335215) B10335215
theorem B1811497 : Blo 634301 1811497 := bstep (se 2 (by rfl) ⟨679311, by rfl⟩ : syracuseStep 1811497 = 1358623) B1358623
theorem B12199085 : Blo 634301 12199085 := bstep (se 3 (by rfl) ⟨2287328, by rfl⟩ : syracuseStep 12199085 = 4574657) B4574657
theorem B2894555 : Blo 634301 2894555 := bstep (se 1 (by rfl) ⟨2170916, by rfl⟩ : syracuseStep 2894555 = 4341833) B4341833
theorem B4075049 : Blo 634301 4075049 := bstep (se 2 (by rfl) ⟨1528143, by rfl⟩ : syracuseStep 4075049 = 3056287) B3056287
theorem B634599 : Blo 634301 634599 := bstep (se 1 (by rfl) ⟨475949, by rfl⟩ : syracuseStep 634599 = 951899) B951899
theorem B635119 : Blo 634301 635119 := bstep (se 1 (by rfl) ⟨476339, by rfl⟩ : syracuseStep 635119 = 952679) B952679
theorem B13775183 : Blo 634301 13775183 := bstep (se 1 (by rfl) ⟨10331387, by rfl⟩ : syracuseStep 13775183 = 20662775) B20662775
theorem B15643103 : Blo 634301 15643103 := bstep (se 1 (by rfl) ⟨11732327, by rfl⟩ : syracuseStep 15643103 = 23464655) B23464655
theorem B635483 : Blo 634301 635483 := bstep (se 1 (by rfl) ⟨476612, by rfl⟩ : syracuseStep 635483 = 953225) B953225
theorem B2143259 : Blo 634301 2143259 := bstep (se 1 (by rfl) ⟨1607444, by rfl⟩ : syracuseStep 2143259 = 3214889) B3214889
theorem B636671 : Blo 634301 636671 := bstep (se 1 (by rfl) ⟨477503, by rfl⟩ : syracuseStep 636671 = 955007) B955007
theorem B636775 : Blo 634301 636775 := bstep (se 1 (by rfl) ⟨477581, by rfl⟩ : syracuseStep 636775 = 955163) B955163
theorem B24525017 : Blo 634301 24525017 := bstep (se 2 (by rfl) ⟨9196881, by rfl⟩ : syracuseStep 24525017 = 18393763) B18393763
theorem B1816987 : Blo 634301 1816987 := bstep (se 1 (by rfl) ⟨1362740, by rfl⟩ : syracuseStep 1816987 = 2725481) B2725481
theorem B637691 : Blo 634301 637691 := bstep (se 1 (by rfl) ⟨478268, by rfl⟩ : syracuseStep 637691 = 956537) B956537
theorem B637723 : Blo 634301 637723 := bstep (se 1 (by rfl) ⟨478292, by rfl⟩ : syracuseStep 637723 = 956585) B956585
theorem B1817579 : Blo 634301 1817579 := bstep (se 1 (by rfl) ⟨1363184, by rfl⟩ : syracuseStep 1817579 = 2726369) B2726369
theorem B2145311 : Blo 634301 2145311 := bstep (se 1 (by rfl) ⟨1608983, by rfl⟩ : syracuseStep 2145311 = 3217967) B3217967
theorem B3620123 : Blo 634301 3620123 := bstep (se 1 (by rfl) ⟨2715092, by rfl⟩ : syracuseStep 3620123 = 5430185) B5430185
theorem B803935 : Blo 634301 803935 := bstep (se 1 (by rfl) ⟨602951, by rfl⟩ : syracuseStep 803935 = 1205903) B1205903
theorem B1427291 : Blo 634301 1427291 := bstep (se 1 (by rfl) ⟨1070468, by rfl⟩ : syracuseStep 1427291 = 2140937) B2140937
theorem B4081661 : Blo 634301 4081661 := bstep (se 3 (by rfl) ⟨765311, by rfl⟩ : syracuseStep 4081661 = 1530623) B1530623
theorem B2148443 : Blo 634301 2148443 := bstep (se 1 (by rfl) ⟨1611332, by rfl⟩ : syracuseStep 2148443 = 3222665) B3222665
theorem B6965477 : Blo 634301 6965477 := bstep (se 4 (by rfl) ⟨653013, by rfl⟩ : syracuseStep 6965477 = 1306027) B1306027
theorem B10865015 : Blo 634301 10865015 := bstep (se 1 (by rfl) ⟨8148761, by rfl⟩ : syracuseStep 10865015 = 16297523) B16297523
theorem B12241307 : Blo 634301 12241307 := bstep (se 1 (by rfl) ⟨9180980, by rfl⟩ : syracuseStep 12241307 = 18361961) B18361961
theorem B7457305 : Blo 634301 7457305 := bstep (se 2 (by rfl) ⟨2796489, by rfl⟩ : syracuseStep 7457305 = 5592979) B5592979
theorem B903835 : Blo 634301 903835 := bstep (se 1 (by rfl) ⟨677876, by rfl⟩ : syracuseStep 903835 = 1355753) B1355753
theorem B3066551 : Blo 634301 3066551 := bstep (se 1 (by rfl) ⟨2299913, by rfl⟩ : syracuseStep 3066551 = 4599827) B4599827
theorem B1657849 : Blo 634301 1657849 := bstep (se 2 (by rfl) ⟨621693, by rfl⟩ : syracuseStep 1657849 = 1243387) B1243387
theorem B1428479 : Blo 634301 1428479 := bstep (se 1 (by rfl) ⟨1071359, by rfl⟩ : syracuseStep 1428479 = 2142719) B2142719
theorem B113331403 : Blo 634301 113331403 := bstep (se 1 (by rfl) ⟨84998552, by rfl⟩ : syracuseStep 113331403 = 169997105) B169997105
theorem B7853483 : Blo 634301 7853483 := bstep (se 1 (by rfl) ⟨5890112, by rfl⟩ : syracuseStep 7853483 = 11780225) B11780225
theorem B2446807 : Blo 634301 2446807 := bstep (se 1 (by rfl) ⟨1835105, by rfl⟩ : syracuseStep 2446807 = 3670211) B3670211
theorem B1431323 : Blo 634301 1431323 := bstep (se 1 (by rfl) ⟨1073492, by rfl⟩ : syracuseStep 1431323 = 2146985) B2146985
theorem B2906927 : Blo 634301 2906927 := bstep (se 1 (by rfl) ⟨2180195, by rfl⟩ : syracuseStep 2906927 = 4360391) B4360391
theorem B2153303 : Blo 634301 2153303 := bstep (se 1 (by rfl) ⟨1614977, by rfl⟩ : syracuseStep 2153303 = 3229955) B3229955
theorem B55631137 : Blo 634301 55631137 := bstep (se 2 (by rfl) ⟨20861676, by rfl⟩ : syracuseStep 55631137 = 41723353) B41723353
theorem B1072487 : Blo 634301 1072487 := bstep (se 1 (by rfl) ⟨804365, by rfl⟩ : syracuseStep 1072487 = 1608731) B1608731
theorem B2153897 : Blo 634301 2153897 := bstep (se 2 (by rfl) ⟨807711, by rfl⟩ : syracuseStep 2153897 = 1615423) B1615423
theorem B6545099 : Blo 634301 6545099 := bstep (se 1 (by rfl) ⟨4908824, by rfl⟩ : syracuseStep 6545099 = 9817649) B9817649
theorem B5170007 : Blo 634301 5170007 := bstep (se 1 (by rfl) ⟨3877505, by rfl⟩ : syracuseStep 5170007 = 7755011) B7755011
theorem B4089143 : Blo 634301 4089143 := bstep (se 1 (by rfl) ⟨3066857, by rfl⟩ : syracuseStep 4089143 = 6133715) B6133715
theorem B714523 : Blo 634301 714523 := bstep (se 1 (by rfl) ⟨535892, by rfl⟩ : syracuseStep 714523 = 1071785) B1071785
theorem B29324753 : Blo 634301 29324753 := bstep (se 2 (by rfl) ⟨10996782, by rfl⟩ : syracuseStep 29324753 = 21993565) B21993565
theorem B61765253 : Blo 634301 61765253 := bstep (se 4 (by rfl) ⟨5790492, by rfl⟩ : syracuseStep 61765253 = 11580985) B11580985
theorem B951527 : Blo 634301 951527 := bstep (se 1 (by rfl) ⟨713645, by rfl⟩ : syracuseStep 951527 = 1427291) B1427291
theorem B41714941 : Blo 634301 41714941 := bstep (se 3 (by rfl) ⟨7821551, by rfl⟩ : syracuseStep 41714941 = 15643103) B15643103
theorem B2721107 : Blo 634301 2721107 := bstep (se 1 (by rfl) ⟨2040830, by rfl⟩ : syracuseStep 2721107 = 4081661) B4081661
theorem B7243343 : Blo 634301 7243343 := bstep (se 1 (by rfl) ⟨5432507, by rfl⟩ : syracuseStep 7243343 = 10865015) B10865015
theorem B8160871 : Blo 634301 8160871 := bstep (se 1 (by rfl) ⟨6120653, by rfl⟩ : syracuseStep 8160871 = 12241307) B12241307
theorem B952319 : Blo 634301 952319 := bstep (se 1 (by rfl) ⟨714239, by rfl⟩ : syracuseStep 952319 = 1428479) B1428479
theorem B952697 : Blo 634301 952697 := bstep (se 2 (by rfl) ⟨357261, by rfl⟩ : syracuseStep 952697 = 714523) B714523
theorem B20942621 : Blo 634301 20942621 := bstep (se 3 (by rfl) ⟨3926741, by rfl⟩ : syracuseStep 20942621 = 7853483) B7853483
theorem B954215 : Blo 634301 954215 := bstep (se 1 (by rfl) ⟨715661, by rfl⟩ : syracuseStep 954215 = 1431323) B1431323
theorem B2297983 : Blo 634301 2297983 := bstep (se 1 (by rfl) ⟨1723487, by rfl⟩ : syracuseStep 2297983 = 3446975) B3446975
theorem B1937951 : Blo 634301 1937951 := bstep (se 1 (by rfl) ⟨1453463, by rfl⟩ : syracuseStep 1937951 = 2906927) B2906927
theorem B2036603 : Blo 634301 2036603 := bstep (se 1 (by rfl) ⟨1527452, by rfl⟩ : syracuseStep 2036603 = 3054905) B3054905
theorem B4363399 : Blo 634301 4363399 := bstep (se 1 (by rfl) ⟨3272549, by rfl⟩ : syracuseStep 4363399 = 6545099) B6545099
theorem B16323767 : Blo 634301 16323767 := bstep (se 1 (by rfl) ⟨12242825, by rfl⟩ : syracuseStep 16323767 = 24485651) B24485651
theorem B3446671 : Blo 634301 3446671 := bstep (se 1 (by rfl) ⟨2585003, by rfl⟩ : syracuseStep 3446671 = 5170007) B5170007
theorem B8132723 : Blo 634301 8132723 := bstep (se 1 (by rfl) ⟨6099542, by rfl⟩ : syracuseStep 8132723 = 12199085) B12199085
theorem B9183455 : Blo 634301 9183455 := bstep (se 1 (by rfl) ⟨6887591, by rfl⟩ : syracuseStep 9183455 = 13775183) B13775183
theorem B30287209 : Blo 634301 30287209 := bstep (se 2 (by rfl) ⟨11357703, by rfl⟩ : syracuseStep 30287209 = 22715407) B22715407
theorem B1714601 : Blo 634301 1714601 := bstep (se 2 (by rfl) ⟨642975, by rfl⟩ : syracuseStep 1714601 = 1285951) B1285951
theorem B765023 : Blo 634301 765023 := bstep (se 1 (by rfl) ⟨573767, by rfl⟩ : syracuseStep 765023 = 1147535) B1147535
theorem B1354907 : Blo 634301 1354907 := bstep (se 1 (by rfl) ⟨1016180, by rfl⟩ : syracuseStep 1354907 = 2032361) B2032361
theorem B9186857 : Blo 634301 9186857 := bstep (se 2 (by rfl) ⟨3445071, by rfl⟩ : syracuseStep 9186857 = 6890143) B6890143
theorem B634415 : Blo 634301 634415 := bstep (se 1 (by rfl) ⟨475811, by rfl⟩ : syracuseStep 634415 = 951623) B951623
theorem B634623 : Blo 634301 634623 := bstep (se 1 (by rfl) ⟨475967, by rfl⟩ : syracuseStep 634623 = 951935) B951935
theorem B634715 : Blo 634301 634715 := bstep (se 1 (by rfl) ⟨476036, by rfl⟩ : syracuseStep 634715 = 952073) B952073
theorem B634815 : Blo 634301 634815 := bstep (se 1 (by rfl) ⟨476111, by rfl⟩ : syracuseStep 634815 = 952223) B952223
theorem B2044367 : Blo 634301 2044367 := bstep (se 1 (by rfl) ⟨1533275, by rfl⟩ : syracuseStep 2044367 = 3066551) B3066551
theorem B635439 : Blo 634301 635439 := bstep (se 1 (by rfl) ⟨476579, by rfl⟩ : syracuseStep 635439 = 953159) B953159
theorem B636063 : Blo 634301 636063 := bstep (se 1 (by rfl) ⟨477047, by rfl⟩ : syracuseStep 636063 = 954095) B954095
theorem B636319 : Blo 634301 636319 := bstep (se 1 (by rfl) ⟨477239, by rfl⟩ : syracuseStep 636319 = 954479) B954479
theorem B2143799 : Blo 634301 2143799 := bstep (se 1 (by rfl) ⟨1607849, by rfl⟩ : syracuseStep 2143799 = 3215699) B3215699
theorem B8697455 : Blo 634301 8697455 := bstep (se 1 (by rfl) ⟨6523091, by rfl⟩ : syracuseStep 8697455 = 13046183) B13046183
theorem B636699 : Blo 634301 636699 := bstep (se 1 (by rfl) ⟨477524, by rfl⟩ : syracuseStep 636699 = 955049) B955049
theorem B636839 : Blo 634301 636839 := bstep (se 1 (by rfl) ⟨477629, by rfl⟩ : syracuseStep 636839 = 955259) B955259
theorem B9943073 : Blo 634301 9943073 := bstep (se 2 (by rfl) ⟨3728652, by rfl⟩ : syracuseStep 9943073 = 7457305) B7457305
theorem B637567 : Blo 634301 637567 := bstep (se 1 (by rfl) ⟨478175, by rfl⟩ : syracuseStep 637567 = 956351) B956351
theorem B2210465 : Blo 634301 2210465 := bstep (se 2 (by rfl) ⟨828924, by rfl⟩ : syracuseStep 2210465 = 1657849) B1657849
theorem B151108537 : Blo 634301 151108537 := bstep (se 2 (by rfl) ⟨56665701, by rfl⟩ : syracuseStep 151108537 = 113331403) B113331403
theorem B638055 : Blo 634301 638055 := bstep (se 1 (by rfl) ⟨478541, by rfl⟩ : syracuseStep 638055 = 957083) B957083
theorem B7718813 : Blo 634301 7718813 := bstep (se 3 (by rfl) ⟨1447277, by rfl⟩ : syracuseStep 7718813 = 2894555) B2894555
theorem B3262409 : Blo 634301 3262409 := bstep (se 2 (by rfl) ⟨1223403, by rfl⟩ : syracuseStep 3262409 = 2446807) B2446807
theorem B1428839 : Blo 634301 1428839 := bstep (se 1 (by rfl) ⟨1071629, by rfl⟩ : syracuseStep 1428839 = 2143259) B2143259
theorem B19549835 : Blo 634301 19549835 := bstep (se 1 (by rfl) ⟨14662376, by rfl⟩ : syracuseStep 19549835 = 29324753) B29324753
theorem B41176835 : Blo 634301 41176835 := bstep (se 1 (by rfl) ⟨30882626, by rfl⟩ : syracuseStep 41176835 = 61765253) B61765253
theorem B74174849 : Blo 634301 74174849 := bstep (se 2 (by rfl) ⟨27815568, by rfl⟩ : syracuseStep 74174849 = 55631137) B55631137
theorem B1430207 : Blo 634301 1430207 := bstep (se 1 (by rfl) ⟨1072655, by rfl⟩ : syracuseStep 1430207 = 2145311) B2145311
theorem B2413415 : Blo 634301 2413415 := bstep (se 1 (by rfl) ⟨1810061, by rfl⟩ : syracuseStep 2413415 = 3620123) B3620123
theorem B2415329 : Blo 634301 2415329 := bstep (se 2 (by rfl) ⟨905748, by rfl⟩ : syracuseStep 2415329 = 1811497) B1811497
theorem B1432295 : Blo 634301 1432295 := bstep (se 1 (by rfl) ⟨1074221, by rfl⟩ : syracuseStep 1432295 = 2148443) B2148443
theorem B1071913 : Blo 634301 1071913 := bstep (se 2 (by rfl) ⟨401967, by rfl⟩ : syracuseStep 1071913 = 803935) B803935
theorem B4643651 : Blo 634301 4643651 := bstep (se 1 (by rfl) ⟨3482738, by rfl⟩ : syracuseStep 4643651 = 6965477) B6965477
theorem B1073243 : Blo 634301 1073243 := bstep (se 1 (by rfl) ⟨804932, by rfl⟩ : syracuseStep 1073243 = 1609865) B1609865
theorem B9790055 : Blo 634301 9790055 := bstep (se 1 (by rfl) ⟨7342541, by rfl⟩ : syracuseStep 9790055 = 14685083) B14685083
theorem B2712359 : Blo 634301 2712359 := bstep (se 1 (by rfl) ⟨2034269, by rfl⟩ : syracuseStep 2712359 = 4068539) B4068539
theorem B10904381 : Blo 634301 10904381 := bstep (se 3 (by rfl) ⟨2044571, by rfl⟩ : syracuseStep 10904381 = 4089143) B4089143
theorem B1205113 : Blo 634301 1205113 := bstep (se 2 (by rfl) ⟨451917, by rfl⟩ : syracuseStep 1205113 = 903835) B903835
theorem B1435535 : Blo 634301 1435535 := bstep (se 1 (by rfl) ⟨1076651, by rfl⟩ : syracuseStep 1435535 = 2153303) B2153303
theorem B714991 : Blo 634301 714991 := bstep (se 1 (by rfl) ⟨536243, by rfl⟩ : syracuseStep 714991 = 1072487) B1072487
theorem B1435931 : Blo 634301 1435931 := bstep (se 1 (by rfl) ⟨1076948, by rfl⟩ : syracuseStep 1435931 = 2153897) B2153897
theorem B2716699 : Blo 634301 2716699 := bstep (se 1 (by rfl) ⟨2037524, by rfl⟩ : syracuseStep 2716699 = 4075049) B4075049
theorem B4846877 : Blo 634301 4846877 := bstep (se 3 (by rfl) ⟨908789, by rfl⟩ : syracuseStep 4846877 = 1817579) B1817579
theorem B2422649 : Blo 634301 2422649 := bstep (se 2 (by rfl) ⟨908493, by rfl⟩ : syracuseStep 2422649 = 1816987) B1816987
theorem B16350011 : Blo 634301 16350011 := bstep (se 1 (by rfl) ⟨12262508, by rfl⟩ : syracuseStep 16350011 = 24525017) B24525017
theorem B4816745 : Blo 634301 4816745 := bstep (se 2 (by rfl) ⟨1806279, by rfl⟩ : syracuseStep 4816745 = 3612559) B3612559
theorem B1606817 : Blo 634301 1606817 := bstep (se 2 (by rfl) ⟨602556, by rfl⟩ : syracuseStep 1606817 = 1205113) B1205113
theorem B5145875 : Blo 634301 5145875 := bstep (se 1 (by rfl) ⟨3859406, by rfl⟩ : syracuseStep 5145875 = 7718813) B7718813
theorem B10881161 : Blo 634301 10881161 := bstep (se 2 (by rfl) ⟨4080435, by rfl⟩ : syracuseStep 10881161 = 8160871) B8160871
theorem B952559 : Blo 634301 952559 := bstep (se 1 (by rfl) ⟨714419, by rfl⟩ : syracuseStep 952559 = 1428839) B1428839
theorem B13961747 : Blo 634301 13961747 := bstep (se 1 (by rfl) ⟨10471310, by rfl⟩ : syracuseStep 13961747 = 20942621) B20942621
theorem B49449899 : Blo 634301 49449899 := bstep (se 1 (by rfl) ⟨37087424, by rfl⟩ : syracuseStep 49449899 = 74174849) B74174849
theorem B953321 : Blo 634301 953321 := bstep (se 2 (by rfl) ⟨357495, by rfl⟩ : syracuseStep 953321 = 714991) B714991
theorem B953471 : Blo 634301 953471 := bstep (se 1 (by rfl) ⟨715103, by rfl⟩ : syracuseStep 953471 = 1430207) B1430207
theorem B1608943 : Blo 634301 1608943 := bstep (se 1 (by rfl) ⟨1206707, by rfl⟩ : syracuseStep 1608943 = 2413415) B2413415
theorem B10882511 : Blo 634301 10882511 := bstep (se 1 (by rfl) ⟨8161883, by rfl⟩ : syracuseStep 10882511 = 16323767) B16323767
theorem B1610219 : Blo 634301 1610219 := bstep (se 1 (by rfl) ⟨1207664, by rfl⟩ : syracuseStep 1610219 = 2415329) B2415329
theorem B954863 : Blo 634301 954863 := bstep (se 1 (by rfl) ⟨716147, by rfl⟩ : syracuseStep 954863 = 1432295) B1432295
theorem B6526703 : Blo 634301 6526703 := bstep (se 1 (by rfl) ⟨4895027, by rfl⟩ : syracuseStep 6526703 = 9790055) B9790055
theorem B1808239 : Blo 634301 1808239 := bstep (se 1 (by rfl) ⟨1356179, by rfl⟩ : syracuseStep 1808239 = 2712359) B2712359
theorem B957023 : Blo 634301 957023 := bstep (se 1 (by rfl) ⟨717767, by rfl⟩ : syracuseStep 957023 = 1435535) B1435535
theorem B957287 : Blo 634301 957287 := bstep (se 1 (by rfl) ⟨717965, by rfl⟩ : syracuseStep 957287 = 1435931) B1435931
theorem B4595561 : Blo 634301 4595561 := bstep (se 2 (by rfl) ⟨1723335, by rfl⟩ : syracuseStep 4595561 = 3446671) B3446671
theorem B2040061 : Blo 634301 2040061 := bstep (se 3 (by rfl) ⟨382511, by rfl⟩ : syracuseStep 2040061 = 765023) B765023
theorem B3613085 : Blo 634301 3613085 := bstep (se 3 (by rfl) ⟨677453, by rfl⟩ : syracuseStep 3613085 = 1354907) B1354907
theorem B1615099 : Blo 634301 1615099 := bstep (se 1 (by rfl) ⟨1211324, by rfl⟩ : syracuseStep 1615099 = 2422649) B2422649
theorem B6628715 : Blo 634301 6628715 := bstep (se 1 (by rfl) ⟨4971536, by rfl⟩ : syracuseStep 6628715 = 9943073) B9943073
theorem B634351 : Blo 634301 634351 := bstep (se 1 (by rfl) ⟨475763, by rfl⟩ : syracuseStep 634351 = 951527) B951527
theorem B1814071 : Blo 634301 1814071 := bstep (se 1 (by rfl) ⟨1360553, by rfl⟩ : syracuseStep 1814071 = 2721107) B2721107
theorem B4828895 : Blo 634301 4828895 := bstep (se 1 (by rfl) ⟨3621671, by rfl⟩ : syracuseStep 4828895 = 7243343) B7243343
theorem B2174939 : Blo 634301 2174939 := bstep (se 1 (by rfl) ⟨1631204, by rfl⟩ : syracuseStep 2174939 = 3262409) B3262409
theorem B634879 : Blo 634301 634879 := bstep (se 1 (by rfl) ⟨476159, by rfl⟩ : syracuseStep 634879 = 952319) B952319
theorem B635131 : Blo 634301 635131 := bstep (se 1 (by rfl) ⟨476348, by rfl⟩ : syracuseStep 635131 = 952697) B952697
theorem B55619921 : Blo 634301 55619921 := bstep (se 2 (by rfl) ⟨20857470, by rfl⟩ : syracuseStep 55619921 = 41714941) B41714941
theorem B40382945 : Blo 634301 40382945 := bstep (se 2 (by rfl) ⟨15143604, by rfl⟩ : syracuseStep 40382945 = 30287209) B30287209
theorem B636143 : Blo 634301 636143 := bstep (se 1 (by rfl) ⟨477107, by rfl⟩ : syracuseStep 636143 = 954215) B954215
theorem B1291967 : Blo 634301 1291967 := bstep (se 1 (by rfl) ⟨968975, by rfl⟩ : syracuseStep 1291967 = 1937951) B1937951
theorem B1357735 : Blo 634301 1357735 := bstep (se 1 (by rfl) ⟨1018301, by rfl⟩ : syracuseStep 1357735 = 2036603) B2036603
theorem B5421815 : Blo 634301 5421815 := bstep (se 1 (by rfl) ⟨4066361, by rfl⟩ : syracuseStep 5421815 = 8132723) B8132723
theorem B3095767 : Blo 634301 3095767 := bstep (se 1 (by rfl) ⟨2321825, by rfl⟩ : syracuseStep 3095767 = 4643651) B4643651
theorem B3063977 : Blo 634301 3063977 := bstep (se 2 (by rfl) ⟨1148991, by rfl⟩ : syracuseStep 3063977 = 2297983) B2297983
theorem B3622265 : Blo 634301 3622265 := bstep (se 2 (by rfl) ⟨1358349, by rfl⟩ : syracuseStep 3622265 = 2716699) B2716699
theorem B5817865 : Blo 634301 5817865 := bstep (se 2 (by rfl) ⟨2181699, by rfl⟩ : syracuseStep 5817865 = 4363399) B4363399
theorem B1362911 : Blo 634301 1362911 := bstep (se 1 (by rfl) ⟨1022183, by rfl⟩ : syracuseStep 1362911 = 2044367) B2044367
theorem B3231251 : Blo 634301 3231251 := bstep (se 1 (by rfl) ⟨2423438, by rfl⟩ : syracuseStep 3231251 = 4846877) B4846877
theorem B1429199 : Blo 634301 1429199 := bstep (se 1 (by rfl) ⟨1071899, by rfl⟩ : syracuseStep 1429199 = 2143799) B2143799
theorem B1429217 : Blo 634301 1429217 := bstep (se 2 (by rfl) ⟨535956, by rfl⟩ : syracuseStep 1429217 = 1071913) B1071913
theorem B201478049 : Blo 634301 201478049 := bstep (se 2 (by rfl) ⟨75554268, by rfl⟩ : syracuseStep 201478049 = 151108537) B151108537
theorem B10900007 : Blo 634301 10900007 := bstep (se 1 (by rfl) ⟨8175005, by rfl⟩ : syracuseStep 10900007 = 16350011) B16350011
theorem B13033223 : Blo 634301 13033223 := bstep (se 1 (by rfl) ⟨9774917, by rfl⟩ : syracuseStep 13033223 = 19549835) B19549835
theorem B27451223 : Blo 634301 27451223 := bstep (se 1 (by rfl) ⟨20588417, by rfl⟩ : syracuseStep 27451223 = 41176835) B41176835
theorem B715495 : Blo 634301 715495 := bstep (se 1 (by rfl) ⟨536621, by rfl⟩ : syracuseStep 715495 = 1073243) B1073243
theorem B6122303 : Blo 634301 6122303 := bstep (se 1 (by rfl) ⟨4591727, by rfl⟩ : syracuseStep 6122303 = 9183455) B9183455
theorem B7269587 : Blo 634301 7269587 := bstep (se 1 (by rfl) ⟨5452190, by rfl⟩ : syracuseStep 7269587 = 10904381) B10904381
theorem B1143067 : Blo 634301 1143067 := bstep (se 1 (by rfl) ⟨857300, by rfl⟩ : syracuseStep 1143067 = 1714601) B1714601
theorem B6124571 : Blo 634301 6124571 := bstep (se 1 (by rfl) ⟨4593428, by rfl⟩ : syracuseStep 6124571 = 9186857) B9186857
theorem B5798303 : Blo 634301 5798303 := bstep (se 1 (by rfl) ⟨4348727, by rfl⟩ : syracuseStep 5798303 = 8697455) B8697455
theorem B1473643 : Blo 634301 1473643 := bstep (se 1 (by rfl) ⟨1105232, by rfl⟩ : syracuseStep 1473643 = 2210465) B2210465
theorem B3211163 : Blo 634301 3211163 := bstep (se 1 (by rfl) ⟨2408372, by rfl⟩ : syracuseStep 3211163 = 4816745) B4816745
theorem B2720081 : Blo 634301 2720081 := bstep (se 2 (by rfl) ⟨1020030, by rfl⟩ : syracuseStep 2720081 = 2040061) B2040061
theorem B9307831 : Blo 634301 9307831 := bstep (se 1 (by rfl) ⟨6980873, by rfl⟩ : syracuseStep 9307831 = 13961747) B13961747
theorem B32966599 : Blo 634301 32966599 := bstep (se 1 (by rfl) ⟨24724949, by rfl⟩ : syracuseStep 32966599 = 49449899) B49449899
theorem B952799 : Blo 634301 952799 := bstep (se 1 (by rfl) ⟨714599, by rfl⟩ : syracuseStep 952799 = 1429199) B1429199
theorem B952811 : Blo 634301 952811 := bstep (se 1 (by rfl) ⟨714608, by rfl⟩ : syracuseStep 952811 = 1429217) B1429217
theorem B134318699 : Blo 634301 134318699 := bstep (se 1 (by rfl) ⟨100739024, by rfl⟩ : syracuseStep 134318699 = 201478049) B201478049
theorem B953993 : Blo 634301 953993 := bstep (se 2 (by rfl) ⟨357747, by rfl⟩ : syracuseStep 953993 = 715495) B715495
theorem B17404541 : Blo 634301 17404541 := bstep (se 3 (by rfl) ⟨3263351, by rfl⟩ : syracuseStep 17404541 = 6526703) B6526703
theorem B8688815 : Blo 634301 8688815 := bstep (se 1 (by rfl) ⟨6516611, by rfl⟩ : syracuseStep 8688815 = 13033223) B13033223
theorem B3219263 : Blo 634301 3219263 := bstep (se 1 (by rfl) ⟨2414447, by rfl⟩ : syracuseStep 3219263 = 4828895) B4828895
theorem B1810313 : Blo 634301 1810313 := bstep (se 2 (by rfl) ⟨678867, by rfl⟩ : syracuseStep 1810313 = 1357735) B1357735
theorem B1449959 : Blo 634301 1449959 := bstep (se 1 (by rfl) ⟨1087469, by rfl⟩ : syracuseStep 1449959 = 2174939) B2174939
theorem B861311 : Blo 634301 861311 := bstep (se 1 (by rfl) ⟨645983, by rfl⟩ : syracuseStep 861311 = 1291967) B1291967
theorem B3614543 : Blo 634301 3614543 := bstep (se 1 (by rfl) ⟨2710907, by rfl⟩ : syracuseStep 3614543 = 5421815) B5421815
theorem B2140775 : Blo 634301 2140775 := bstep (se 1 (by rfl) ⟨1605581, by rfl⟩ : syracuseStep 2140775 = 3211163) B3211163
theorem B2042651 : Blo 634301 2042651 := bstep (se 1 (by rfl) ⟨1531988, by rfl⟩ : syracuseStep 2042651 = 3063977) B3063977
theorem B7254107 : Blo 634301 7254107 := bstep (se 1 (by rfl) ⟨5440580, by rfl⟩ : syracuseStep 7254107 = 10881161) B10881161
theorem B635039 : Blo 634301 635039 := bstep (se 1 (by rfl) ⟨476279, by rfl⟩ : syracuseStep 635039 = 952559) B952559
theorem B635547 : Blo 634301 635547 := bstep (se 1 (by rfl) ⟨476660, by rfl⟩ : syracuseStep 635547 = 953321) B953321
theorem B635647 : Blo 634301 635647 := bstep (se 1 (by rfl) ⟨476735, by rfl⟩ : syracuseStep 635647 = 953471) B953471
theorem B7255007 : Blo 634301 7255007 := bstep (se 1 (by rfl) ⟨5441255, by rfl⟩ : syracuseStep 7255007 = 10882511) B10882511
theorem B636575 : Blo 634301 636575 := bstep (se 1 (by rfl) ⟨477431, by rfl⟩ : syracuseStep 636575 = 954863) B954863
theorem B2145257 : Blo 634301 2145257 := bstep (se 2 (by rfl) ⟨804471, by rfl⟩ : syracuseStep 2145257 = 1608943) B1608943
theorem B638015 : Blo 634301 638015 := bstep (se 1 (by rfl) ⟨478511, by rfl⟩ : syracuseStep 638015 = 957023) B957023
theorem B638191 : Blo 634301 638191 := bstep (se 1 (by rfl) ⟨478643, by rfl⟩ : syracuseStep 638191 = 957287) B957287
theorem B18300815 : Blo 634301 18300815 := bstep (se 1 (by rfl) ⟨13725611, by rfl⟩ : syracuseStep 18300815 = 27451223) B27451223
theorem B3063707 : Blo 634301 3063707 := bstep (se 1 (by rfl) ⟨2297780, by rfl⟩ : syracuseStep 3063707 = 4595561) B4595561
theorem B2408723 : Blo 634301 2408723 := bstep (se 1 (by rfl) ⟨1806542, by rfl⟩ : syracuseStep 2408723 = 3613085) B3613085
theorem B1524089 : Blo 634301 1524089 := bstep (se 2 (by rfl) ⟨571533, by rfl⟩ : syracuseStep 1524089 = 1143067) B1143067
theorem B4081535 : Blo 634301 4081535 := bstep (se 1 (by rfl) ⟨3061151, by rfl⟩ : syracuseStep 4081535 = 6122303) B6122303
theorem B2410985 : Blo 634301 2410985 := bstep (se 2 (by rfl) ⟨904119, by rfl⟩ : syracuseStep 2410985 = 1808239) B1808239
theorem B37079947 : Blo 634301 37079947 := bstep (se 1 (by rfl) ⟨27809960, by rfl⟩ : syracuseStep 37079947 = 55619921) B55619921
theorem B26921963 : Blo 634301 26921963 := bstep (se 1 (by rfl) ⟨20191472, by rfl⟩ : syracuseStep 26921963 = 40382945) B40382945
theorem B4083047 : Blo 634301 4083047 := bstep (se 1 (by rfl) ⟨3062285, by rfl⟩ : syracuseStep 4083047 = 6124571) B6124571
theorem B1071211 : Blo 634301 1071211 := bstep (se 1 (by rfl) ⟨803408, by rfl⟩ : syracuseStep 1071211 = 1606817) B1606817
theorem B3430583 : Blo 634301 3430583 := bstep (se 1 (by rfl) ⟨2572937, by rfl⟩ : syracuseStep 3430583 = 5145875) B5145875
theorem B2414843 : Blo 634301 2414843 := bstep (se 1 (by rfl) ⟨1811132, by rfl⟩ : syracuseStep 2414843 = 3622265) B3622265
theorem B2153465 : Blo 634301 2153465 := bstep (se 2 (by rfl) ⟨807549, by rfl⟩ : syracuseStep 2153465 = 1615099) B1615099
theorem B7757153 : Blo 634301 7757153 := bstep (se 2 (by rfl) ⟨2908932, by rfl⟩ : syracuseStep 7757153 = 5817865) B5817865
theorem B2154167 : Blo 634301 2154167 := bstep (se 1 (by rfl) ⟨1615625, by rfl⟩ : syracuseStep 2154167 = 3231251) B3231251
theorem B1073479 : Blo 634301 1073479 := bstep (se 1 (by rfl) ⟨805109, by rfl⟩ : syracuseStep 1073479 = 1610219) B1610219
theorem B7266671 : Blo 634301 7266671 := bstep (se 1 (by rfl) ⟨5450003, by rfl⟩ : syracuseStep 7266671 = 10900007) B10900007
theorem B2418761 : Blo 634301 2418761 := bstep (se 2 (by rfl) ⟨907035, by rfl⟩ : syracuseStep 2418761 = 1814071) B1814071
theorem B7859429 : Blo 634301 7859429 := bstep (se 4 (by rfl) ⟨736821, by rfl⟩ : syracuseStep 7859429 = 1473643) B1473643
theorem B4419143 : Blo 634301 4419143 := bstep (se 1 (by rfl) ⟨3314357, by rfl⟩ : syracuseStep 4419143 = 6628715) B6628715
theorem B4846391 : Blo 634301 4846391 := bstep (se 1 (by rfl) ⟨3634793, by rfl⟩ : syracuseStep 4846391 = 7269587) B7269587
theorem B3634429 : Blo 634301 3634429 := bstep (se 3 (by rfl) ⟨681455, by rfl⟩ : syracuseStep 3634429 = 1362911) B1362911
theorem B3865535 : Blo 634301 3865535 := bstep (se 1 (by rfl) ⟨2899151, by rfl⟩ : syracuseStep 3865535 = 5798303) B5798303
theorem B4127689 : Blo 634301 4127689 := bstep (se 2 (by rfl) ⟨1547883, by rfl⟩ : syracuseStep 4127689 = 3095767) B3095767
theorem B1605815 : Blo 634301 1605815 := bstep (se 1 (by rfl) ⟨1204361, by rfl⟩ : syracuseStep 1605815 = 2408723) B2408723
theorem B1016059 : Blo 634301 1016059 := bstep (se 1 (by rfl) ⟨762044, by rfl⟩ : syracuseStep 1016059 = 1524089) B1524089
theorem B2721023 : Blo 634301 2721023 := bstep (se 1 (by rfl) ⟨2040767, by rfl⟩ : syracuseStep 2721023 = 4081535) B4081535
theorem B1607323 : Blo 634301 1607323 := bstep (se 1 (by rfl) ⟨1205492, by rfl⟩ : syracuseStep 1607323 = 2410985) B2410985
theorem B2722031 : Blo 634301 2722031 := bstep (se 1 (by rfl) ⟨2041523, by rfl⟩ : syracuseStep 2722031 = 4083047) B4083047
theorem B2296829 : Blo 634301 2296829 := bstep (se 3 (by rfl) ⟨430655, by rfl⟩ : syracuseStep 2296829 = 861311) B861311
theorem B11603027 : Blo 634301 11603027 := bstep (se 1 (by rfl) ⟨8702270, by rfl⟩ : syracuseStep 11603027 = 17404541) B17404541
theorem B1609895 : Blo 634301 1609895 := bstep (se 1 (by rfl) ⟨1207421, by rfl⟩ : syracuseStep 1609895 = 2414843) B2414843
theorem B197759717 : Blo 634301 197759717 := bstep (se 4 (by rfl) ⟨18539973, by rfl⟩ : syracuseStep 197759717 = 37079947) B37079947
theorem B1612507 : Blo 634301 1612507 := bstep (se 1 (by rfl) ⟨1209380, by rfl⟩ : syracuseStep 1612507 = 2418761) B2418761
theorem B12200543 : Blo 634301 12200543 := bstep (se 1 (by rfl) ⟨9150407, by rfl⟩ : syracuseStep 12200543 = 18300815) B18300815
theorem B2042471 : Blo 634301 2042471 := bstep (se 1 (by rfl) ⟨1531853, by rfl⟩ : syracuseStep 2042471 = 3063707) B3063707
theorem B7253549 : Blo 634301 7253549 := bstep (se 3 (by rfl) ⟨1360040, by rfl⟩ : syracuseStep 7253549 = 2720081) B2720081
theorem B635199 : Blo 634301 635199 := bstep (se 1 (by rfl) ⟨476399, by rfl⟩ : syracuseStep 635199 = 952799) B952799
theorem B635207 : Blo 634301 635207 := bstep (se 1 (by rfl) ⟨476405, by rfl⟩ : syracuseStep 635207 = 952811) B952811
theorem B635995 : Blo 634301 635995 := bstep (se 1 (by rfl) ⟨476996, by rfl⟩ : syracuseStep 635995 = 953993) B953993
theorem B43955465 : Blo 634301 43955465 := bstep (se 2 (by rfl) ⟨16483299, by rfl⟩ : syracuseStep 43955465 = 32966599) B32966599
theorem B2146175 : Blo 634301 2146175 := bstep (se 1 (by rfl) ⟨1609631, by rfl⟩ : syracuseStep 2146175 = 3219263) B3219263
theorem B2409695 : Blo 634301 2409695 := bstep (se 1 (by rfl) ⟨1807271, by rfl⟩ : syracuseStep 2409695 = 3614543) B3614543
theorem B1427183 : Blo 634301 1427183 := bstep (se 1 (by rfl) ⟨1070387, by rfl⟩ : syracuseStep 1427183 = 2140775) B2140775
theorem B1361767 : Blo 634301 1361767 := bstep (se 1 (by rfl) ⟨1021325, by rfl⟩ : syracuseStep 1361767 = 2042651) B2042651
theorem B4836071 : Blo 634301 4836071 := bstep (se 1 (by rfl) ⟨3627053, by rfl⟩ : syracuseStep 4836071 = 7254107) B7254107
theorem B1428281 : Blo 634301 1428281 := bstep (se 2 (by rfl) ⟨535605, by rfl⟩ : syracuseStep 1428281 = 1071211) B1071211
theorem B3230927 : Blo 634301 3230927 := bstep (se 1 (by rfl) ⟨2423195, by rfl⟩ : syracuseStep 3230927 = 4846391) B4846391
theorem B4836671 : Blo 634301 4836671 := bstep (se 1 (by rfl) ⟨3627503, by rfl⟩ : syracuseStep 4836671 = 7255007) B7255007
theorem B2577023 : Blo 634301 2577023 := bstep (se 1 (by rfl) ⟨1932767, by rfl⟩ : syracuseStep 2577023 = 3865535) B3865535
theorem B1430171 : Blo 634301 1430171 := bstep (se 1 (by rfl) ⟨1072628, by rfl⟩ : syracuseStep 1430171 = 2145257) B2145257
theorem B1431305 : Blo 634301 1431305 := bstep (se 2 (by rfl) ⟨536739, by rfl⟩ : syracuseStep 1431305 = 1073479) B1073479
theorem B89545799 : Blo 634301 89545799 := bstep (se 1 (by rfl) ⟨67159349, by rfl⟩ : syracuseStep 89545799 = 134318699) B134318699
theorem B17947975 : Blo 634301 17947975 := bstep (se 1 (by rfl) ⟨13460981, by rfl⟩ : syracuseStep 17947975 = 26921963) B26921963
theorem B12410441 : Blo 634301 12410441 := bstep (se 2 (by rfl) ⟨4653915, by rfl⟩ : syracuseStep 12410441 = 9307831) B9307831
theorem B5792543 : Blo 634301 5792543 := bstep (se 1 (by rfl) ⟨4344407, by rfl⟩ : syracuseStep 5792543 = 8688815) B8688815
theorem B2287055 : Blo 634301 2287055 := bstep (se 1 (by rfl) ⟨1715291, by rfl⟩ : syracuseStep 2287055 = 3430583) B3430583
theorem B1435643 : Blo 634301 1435643 := bstep (se 1 (by rfl) ⟨1076732, by rfl⟩ : syracuseStep 1435643 = 2153465) B2153465
theorem B5171435 : Blo 634301 5171435 := bstep (se 1 (by rfl) ⟨3878576, by rfl⟩ : syracuseStep 5171435 = 7757153) B7757153
theorem B1436111 : Blo 634301 1436111 := bstep (se 1 (by rfl) ⟨1077083, by rfl⟩ : syracuseStep 1436111 = 2154167) B2154167
theorem B1206875 : Blo 634301 1206875 := bstep (se 1 (by rfl) ⟨905156, by rfl⟩ : syracuseStep 1206875 = 1810313) B1810313
theorem B4844447 : Blo 634301 4844447 := bstep (se 1 (by rfl) ⟨3633335, by rfl⟩ : syracuseStep 4844447 = 7266671) B7266671
theorem B4845905 : Blo 634301 4845905 := bstep (se 2 (by rfl) ⟨1817214, by rfl⟩ : syracuseStep 4845905 = 3634429) B3634429
theorem B5239619 : Blo 634301 5239619 := bstep (se 1 (by rfl) ⟨3929714, by rfl⟩ : syracuseStep 5239619 = 7859429) B7859429
theorem B2946095 : Blo 634301 2946095 := bstep (se 1 (by rfl) ⟨2209571, by rfl⟩ : syracuseStep 2946095 = 4419143) B4419143
theorem B5503585 : Blo 634301 5503585 := bstep (se 2 (by rfl) ⟨2063844, by rfl⟩ : syracuseStep 5503585 = 4127689) B4127689
theorem B3866557 : Blo 634301 3866557 := bstep (se 3 (by rfl) ⟨724979, by rfl⟩ : syracuseStep 3866557 = 1449959) B1449959
theorem B1606463 : Blo 634301 1606463 := bstep (se 1 (by rfl) ⟨1204847, by rfl⟩ : syracuseStep 1606463 = 2409695) B2409695
theorem B951455 : Blo 634301 951455 := bstep (se 1 (by rfl) ⟨713591, by rfl⟩ : syracuseStep 951455 = 1427183) B1427183
theorem B952187 : Blo 634301 952187 := bstep (se 1 (by rfl) ⟨714140, by rfl⟩ : syracuseStep 952187 = 1428281) B1428281
theorem B7735351 : Blo 634301 7735351 := bstep (se 1 (by rfl) ⟨5801513, by rfl⟩ : syracuseStep 7735351 = 11603027) B11603027
theorem B953447 : Blo 634301 953447 := bstep (se 1 (by rfl) ⟨715085, by rfl⟩ : syracuseStep 953447 = 1430171) B1430171
theorem B117214573 : Blo 634301 117214573 := bstep (se 3 (by rfl) ⟨21977732, by rfl⟩ : syracuseStep 117214573 = 43955465) B43955465
theorem B954203 : Blo 634301 954203 := bstep (se 1 (by rfl) ⟨715652, by rfl⟩ : syracuseStep 954203 = 1431305) B1431305
theorem B6098813 : Blo 634301 6098813 := bstep (se 3 (by rfl) ⟨1143527, by rfl⟩ : syracuseStep 6098813 = 2287055) B2287055
theorem B957095 : Blo 634301 957095 := bstep (se 1 (by rfl) ⟨717821, by rfl⟩ : syracuseStep 957095 = 1435643) B1435643
theorem B3447623 : Blo 634301 3447623 := bstep (se 1 (by rfl) ⟨2585717, by rfl⟩ : syracuseStep 3447623 = 5171435) B5171435
theorem B957407 : Blo 634301 957407 := bstep (se 1 (by rfl) ⟨718055, by rfl⟩ : syracuseStep 957407 = 1436111) B1436111
theorem B8133695 : Blo 634301 8133695 := bstep (se 1 (by rfl) ⟨6100271, by rfl⟩ : syracuseStep 8133695 = 12200543) B12200543
theorem B23930633 : Blo 634301 23930633 := bstep (se 2 (by rfl) ⟨8973987, by rfl⟩ : syracuseStep 23930633 = 17947975) B17947975
theorem B5155409 : Blo 634301 5155409 := bstep (se 2 (by rfl) ⟨1933278, by rfl⟩ : syracuseStep 5155409 = 3866557) B3866557
theorem B1354745 : Blo 634301 1354745 := bstep (se 2 (by rfl) ⟨508029, by rfl⟩ : syracuseStep 1354745 = 1016059) B1016059
theorem B1814015 : Blo 634301 1814015 := bstep (se 1 (by rfl) ⟨1360511, by rfl⟩ : syracuseStep 1814015 = 2721023) B2721023
theorem B1814687 : Blo 634301 1814687 := bstep (se 1 (by rfl) ⟨1361015, by rfl⟩ : syracuseStep 1814687 = 2722031) B2722031
theorem B2143097 : Blo 634301 2143097 := bstep (se 2 (by rfl) ⟨803661, by rfl⟩ : syracuseStep 2143097 = 1607323) B1607323
theorem B3224447 : Blo 634301 3224447 := bstep (se 1 (by rfl) ⟨2418335, by rfl⟩ : syracuseStep 3224447 = 4836671) B4836671
theorem B1815689 : Blo 634301 1815689 := bstep (se 2 (by rfl) ⟨680883, by rfl⟩ : syracuseStep 1815689 = 1361767) B1361767
theorem B1718015 : Blo 634301 1718015 := bstep (se 1 (by rfl) ⟨1288511, by rfl⟩ : syracuseStep 1718015 = 2577023) B2577023
theorem B131839811 : Blo 634301 131839811 := bstep (se 1 (by rfl) ⟨98879858, by rfl⟩ : syracuseStep 131839811 = 197759717) B197759717
theorem B8273627 : Blo 634301 8273627 := bstep (se 1 (by rfl) ⟨6205220, by rfl⟩ : syracuseStep 8273627 = 12410441) B12410441
theorem B804583 : Blo 634301 804583 := bstep (se 1 (by rfl) ⟨603437, by rfl⟩ : syracuseStep 804583 = 1206875) B1206875
theorem B1361647 : Blo 634301 1361647 := bstep (se 1 (by rfl) ⟨1021235, by rfl⟩ : syracuseStep 1361647 = 2042471) B2042471
theorem B12896189 : Blo 634301 12896189 := bstep (se 3 (by rfl) ⟨2418035, by rfl⟩ : syracuseStep 12896189 = 4836071) B4836071
theorem B3229631 : Blo 634301 3229631 := bstep (se 1 (by rfl) ⟨2422223, by rfl⟩ : syracuseStep 3229631 = 4844447) B4844447
theorem B4835699 : Blo 634301 4835699 := bstep (se 1 (by rfl) ⟨3626774, by rfl⟩ : syracuseStep 4835699 = 7253549) B7253549
theorem B3230603 : Blo 634301 3230603 := bstep (se 1 (by rfl) ⟨2422952, by rfl⟩ : syracuseStep 3230603 = 4845905) B4845905
theorem B3493079 : Blo 634301 3493079 := bstep (se 1 (by rfl) ⟨2619809, by rfl⟩ : syracuseStep 3493079 = 5239619) B5239619
theorem B2150009 : Blo 634301 2150009 := bstep (se 2 (by rfl) ⟨806253, by rfl⟩ : syracuseStep 2150009 = 1612507) B1612507
theorem B1430783 : Blo 634301 1430783 := bstep (se 1 (by rfl) ⟨1073087, by rfl⟩ : syracuseStep 1430783 = 2146175) B2146175
theorem B1070543 : Blo 634301 1070543 := bstep (se 1 (by rfl) ⟨802907, by rfl⟩ : syracuseStep 1070543 = 1605815) B1605815
theorem B1531219 : Blo 634301 1531219 := bstep (se 1 (by rfl) ⟨1148414, by rfl⟩ : syracuseStep 1531219 = 2296829) B2296829
theorem B2153951 : Blo 634301 2153951 := bstep (se 1 (by rfl) ⟨1615463, by rfl⟩ : syracuseStep 2153951 = 3230927) B3230927
theorem B1073263 : Blo 634301 1073263 := bstep (se 1 (by rfl) ⟨804947, by rfl⟩ : syracuseStep 1073263 = 1609895) B1609895
theorem B59697199 : Blo 634301 59697199 := bstep (se 1 (by rfl) ⟨44772899, by rfl⟩ : syracuseStep 59697199 = 89545799) B89545799
theorem B3861695 : Blo 634301 3861695 := bstep (se 1 (by rfl) ⟨2896271, by rfl⟩ : syracuseStep 3861695 = 5792543) B5792543
theorem B1964063 : Blo 634301 1964063 := bstep (se 1 (by rfl) ⟨1473047, by rfl⟩ : syracuseStep 1964063 = 2946095) B2946095
theorem B7338113 : Blo 634301 7338113 := bstep (se 2 (by rfl) ⟨2751792, by rfl⟩ : syracuseStep 7338113 = 5503585) B5503585
theorem B37259509 : Blo 634301 37259509 := bstep (se 5 (by rfl) ⟨1746539, by rfl⟩ : syracuseStep 37259509 = 3493079) B3493079
theorem B4065875 : Blo 634301 4065875 := bstep (se 1 (by rfl) ⟨3049406, by rfl⟩ : syracuseStep 4065875 = 6098813) B6098813
theorem B79596265 : Blo 634301 79596265 := bstep (se 2 (by rfl) ⟨29848599, by rfl⟩ : syracuseStep 79596265 = 59697199) B59697199
theorem B953855 : Blo 634301 953855 := bstep (se 1 (by rfl) ⟨715391, by rfl⟩ : syracuseStep 953855 = 1430783) B1430783
theorem B2298415 : Blo 634301 2298415 := bstep (se 1 (by rfl) ⟨1723811, by rfl⟩ : syracuseStep 2298415 = 3447623) B3447623
theorem B10297853 : Blo 634301 10297853 := bstep (se 3 (by rfl) ⟨1930847, by rfl⟩ : syracuseStep 10297853 = 3861695) B3861695
theorem B87893207 : Blo 634301 87893207 := bstep (se 1 (by rfl) ⟨65919905, by rfl⟩ : syracuseStep 87893207 = 131839811) B131839811
theorem B4892075 : Blo 634301 4892075 := bstep (se 1 (by rfl) ⟨3669056, by rfl⟩ : syracuseStep 4892075 = 7338113) B7338113
theorem B2041625 : Blo 634301 2041625 := bstep (se 2 (by rfl) ⟨765609, by rfl⟩ : syracuseStep 2041625 = 1531219) B1531219
theorem B5515751 : Blo 634301 5515751 := bstep (se 1 (by rfl) ⟨4136813, by rfl⟩ : syracuseStep 5515751 = 8273627) B8273627
theorem B634303 : Blo 634301 634303 := bstep (se 1 (by rfl) ⟨475727, by rfl⟩ : syracuseStep 634303 = 951455) B951455
theorem B634791 : Blo 634301 634791 := bstep (se 1 (by rfl) ⟨476093, by rfl⟩ : syracuseStep 634791 = 952187) B952187
theorem B8597459 : Blo 634301 8597459 := bstep (se 1 (by rfl) ⟨6448094, by rfl⟩ : syracuseStep 8597459 = 12896189) B12896189
theorem B3223799 : Blo 634301 3223799 := bstep (se 1 (by rfl) ⟨2417849, by rfl⟩ : syracuseStep 3223799 = 4835699) B4835699
theorem B635631 : Blo 634301 635631 := bstep (se 1 (by rfl) ⟨476723, by rfl⟩ : syracuseStep 635631 = 953447) B953447
theorem B1815529 : Blo 634301 1815529 := bstep (se 2 (by rfl) ⟨680823, by rfl⟩ : syracuseStep 1815529 = 1361647) B1361647
theorem B636135 : Blo 634301 636135 := bstep (se 1 (by rfl) ⟨477101, by rfl⟩ : syracuseStep 636135 = 954203) B954203
theorem B638063 : Blo 634301 638063 := bstep (se 1 (by rfl) ⟨478547, by rfl⟩ : syracuseStep 638063 = 957095) B957095
theorem B156286097 : Blo 634301 156286097 := bstep (se 2 (by rfl) ⟨58607286, by rfl⟩ : syracuseStep 156286097 = 117214573) B117214573
theorem B638271 : Blo 634301 638271 := bstep (se 1 (by rfl) ⟨478703, by rfl⟩ : syracuseStep 638271 = 957407) B957407
theorem B5422463 : Blo 634301 5422463 := bstep (se 1 (by rfl) ⟨4066847, by rfl⟩ : syracuseStep 5422463 = 8133695) B8133695
theorem B903163 : Blo 634301 903163 := bstep (se 1 (by rfl) ⟨677372, by rfl⟩ : syracuseStep 903163 = 1354745) B1354745
theorem B1428731 : Blo 634301 1428731 := bstep (se 1 (by rfl) ⟨1071548, by rfl⟩ : syracuseStep 1428731 = 2143097) B2143097
theorem B2149631 : Blo 634301 2149631 := bstep (se 1 (by rfl) ⟨1612223, by rfl⟩ : syracuseStep 2149631 = 3224447) B3224447
theorem B1431017 : Blo 634301 1431017 := bstep (se 2 (by rfl) ⟨536631, by rfl⟩ : syracuseStep 1431017 = 1073263) B1073263
theorem B1070975 : Blo 634301 1070975 := bstep (se 1 (by rfl) ⟨803231, by rfl⟩ : syracuseStep 1070975 = 1606463) B1606463
theorem B2153087 : Blo 634301 2153087 := bstep (se 1 (by rfl) ⟨1614815, by rfl⟩ : syracuseStep 2153087 = 3229631) B3229631
theorem B2153735 : Blo 634301 2153735 := bstep (se 1 (by rfl) ⟨1615301, by rfl⟩ : syracuseStep 2153735 = 3230603) B3230603
theorem B1072777 : Blo 634301 1072777 := bstep (se 2 (by rfl) ⟨402291, by rfl⟩ : syracuseStep 1072777 = 804583) B804583
theorem B1433339 : Blo 634301 1433339 := bstep (se 1 (by rfl) ⟨1075004, by rfl⟩ : syracuseStep 1433339 = 2150009) B2150009
theorem B10313801 : Blo 634301 10313801 := bstep (se 2 (by rfl) ⟨3867675, by rfl⟩ : syracuseStep 10313801 = 7735351) B7735351
theorem B713695 : Blo 634301 713695 := bstep (se 1 (by rfl) ⟨535271, by rfl⟩ : syracuseStep 713695 = 1070543) B1070543
theorem B4581373 : Blo 634301 4581373 := bstep (se 3 (by rfl) ⟨859007, by rfl⟩ : syracuseStep 4581373 = 1718015) B1718015
theorem B1435967 : Blo 634301 1435967 := bstep (se 1 (by rfl) ⟨1076975, by rfl⟩ : syracuseStep 1435967 = 2153951) B2153951
theorem B15953755 : Blo 634301 15953755 := bstep (se 1 (by rfl) ⟨11965316, by rfl⟩ : syracuseStep 15953755 = 23930633) B23930633
theorem B3436939 : Blo 634301 3436939 := bstep (se 1 (by rfl) ⟨2577704, by rfl⟩ : syracuseStep 3436939 = 5155409) B5155409
theorem B1209343 : Blo 634301 1209343 := bstep (se 1 (by rfl) ⟨907007, by rfl⟩ : syracuseStep 1209343 = 1814015) B1814015
theorem B1209791 : Blo 634301 1209791 := bstep (se 1 (by rfl) ⟨907343, by rfl⟩ : syracuseStep 1209791 = 1814687) B1814687
theorem B1210459 : Blo 634301 1210459 := bstep (se 1 (by rfl) ⟨907844, by rfl⟩ : syracuseStep 1210459 = 1815689) B1815689
theorem B1309375 : Blo 634301 1309375 := bstep (se 1 (by rfl) ⟨982031, by rfl⟩ : syracuseStep 1309375 = 1964063) B1964063
theorem B951593 : Blo 634301 951593 := bstep (se 2 (by rfl) ⟨356847, by rfl⟩ : syracuseStep 951593 = 713695) B713695
theorem B952487 : Blo 634301 952487 := bstep (se 1 (by rfl) ⟨714365, by rfl⟩ : syracuseStep 952487 = 1428731) B1428731
theorem B49679345 : Blo 634301 49679345 := bstep (se 2 (by rfl) ⟨18629754, by rfl⟩ : syracuseStep 49679345 = 37259509) B37259509
theorem B954011 : Blo 634301 954011 := bstep (se 1 (by rfl) ⟨715508, by rfl⟩ : syracuseStep 954011 = 1431017) B1431017
theorem B6983333 : Blo 634301 6983333 := bstep (se 4 (by rfl) ⟨654687, by rfl⟩ : syracuseStep 6983333 = 1309375) B1309375
theorem B5444333 : Blo 634301 5444333 := bstep (se 3 (by rfl) ⟨1020812, by rfl⟩ : syracuseStep 5444333 = 2041625) B2041625
theorem B21271673 : Blo 634301 21271673 := bstep (se 2 (by rfl) ⟨7976877, by rfl⟩ : syracuseStep 21271673 = 15953755) B15953755
theorem B955559 : Blo 634301 955559 := bstep (se 1 (by rfl) ⟨716669, by rfl⟩ : syracuseStep 955559 = 1433339) B1433339
theorem B58595471 : Blo 634301 58595471 := bstep (se 1 (by rfl) ⟨43946603, by rfl⟩ : syracuseStep 58595471 = 87893207) B87893207
theorem B1612457 : Blo 634301 1612457 := bstep (se 2 (by rfl) ⟨604671, by rfl⟩ : syracuseStep 1612457 = 1209343) B1209343
theorem B957311 : Blo 634301 957311 := bstep (se 1 (by rfl) ⟨717983, by rfl⟩ : syracuseStep 957311 = 1435967) B1435967
theorem B3677167 : Blo 634301 3677167 := bstep (se 1 (by rfl) ⟨2757875, by rfl⟩ : syracuseStep 3677167 = 5515751) B5515751
theorem B1613945 : Blo 634301 1613945 := bstep (se 2 (by rfl) ⟨605229, by rfl⟩ : syracuseStep 1613945 = 1210459) B1210459
theorem B3614975 : Blo 634301 3614975 := bstep (se 1 (by rfl) ⟨2711231, by rfl⟩ : syracuseStep 3614975 = 5422463) B5422463
theorem B635903 : Blo 634301 635903 := bstep (se 1 (by rfl) ⟨476927, by rfl⟩ : syracuseStep 635903 = 953855) B953855
theorem B6108497 : Blo 634301 6108497 := bstep (se 2 (by rfl) ⟨2290686, by rfl⟩ : syracuseStep 6108497 = 4581373) B4581373
theorem B6865235 : Blo 634301 6865235 := bstep (se 1 (by rfl) ⟨5148926, by rfl⟩ : syracuseStep 6865235 = 10297853) B10297853
theorem B3064553 : Blo 634301 3064553 := bstep (se 2 (by rfl) ⟨1149207, by rfl⟩ : syracuseStep 3064553 = 2298415) B2298415
theorem B3261383 : Blo 634301 3261383 := bstep (se 1 (by rfl) ⟨2446037, by rfl⟩ : syracuseStep 3261383 = 4892075) B4892075
theorem B2149199 : Blo 634301 2149199 := bstep (se 1 (by rfl) ⟨1611899, by rfl⟩ : syracuseStep 2149199 = 3223799) B3223799
theorem B806527 : Blo 634301 806527 := bstep (se 1 (by rfl) ⟨604895, by rfl⟩ : syracuseStep 806527 = 1209791) B1209791
theorem B104190731 : Blo 634301 104190731 := bstep (se 1 (by rfl) ⟨78143048, by rfl⟩ : syracuseStep 104190731 = 156286097) B156286097
theorem B1430369 : Blo 634301 1430369 := bstep (se 2 (by rfl) ⟨536388, by rfl⟩ : syracuseStep 1430369 = 1072777) B1072777
theorem B22926557 : Blo 634301 22926557 := bstep (se 3 (by rfl) ⟨4298729, by rfl⟩ : syracuseStep 22926557 = 8597459) B8597459
theorem B2710583 : Blo 634301 2710583 := bstep (se 1 (by rfl) ⟨2032937, by rfl⟩ : syracuseStep 2710583 = 4065875) B4065875
theorem B1433087 : Blo 634301 1433087 := bstep (se 1 (by rfl) ⟨1074815, by rfl⟩ : syracuseStep 1433087 = 2149631) B2149631
theorem B1204217 : Blo 634301 1204217 := bstep (se 2 (by rfl) ⟨451581, by rfl⟩ : syracuseStep 1204217 = 903163) B903163
theorem B106128353 : Blo 634301 106128353 := bstep (se 2 (by rfl) ⟨39798132, by rfl⟩ : syracuseStep 106128353 = 79596265) B79596265
theorem B713983 : Blo 634301 713983 := bstep (se 1 (by rfl) ⟨535487, by rfl⟩ : syracuseStep 713983 = 1070975) B1070975
theorem B1435391 : Blo 634301 1435391 := bstep (se 1 (by rfl) ⟨1076543, by rfl⟩ : syracuseStep 1435391 = 2153087) B2153087
theorem B1435823 : Blo 634301 1435823 := bstep (se 1 (by rfl) ⟨1076867, by rfl⟩ : syracuseStep 1435823 = 2153735) B2153735
theorem B6875867 : Blo 634301 6875867 := bstep (se 1 (by rfl) ⟨5156900, by rfl⟩ : syracuseStep 6875867 = 10313801) B10313801
theorem B4582585 : Blo 634301 4582585 := bstep (se 2 (by rfl) ⟨1718469, by rfl⟩ : syracuseStep 4582585 = 3436939) B3436939
theorem B2420705 : Blo 634301 2420705 := bstep (se 2 (by rfl) ⟨907764, by rfl⟩ : syracuseStep 2420705 = 1815529) B1815529
theorem B951977 : Blo 634301 951977 := bstep (se 2 (by rfl) ⟨356991, by rfl⟩ : syracuseStep 951977 = 713983) B713983
theorem B4655555 : Blo 634301 4655555 := bstep (se 1 (by rfl) ⟨3491666, by rfl⟩ : syracuseStep 4655555 = 6983333) B6983333
theorem B56724461 : Blo 634301 56724461 := bstep (se 3 (by rfl) ⟨10635836, by rfl⟩ : syracuseStep 56724461 = 21271673) B21271673
theorem B953579 : Blo 634301 953579 := bstep (se 1 (by rfl) ⟨715184, by rfl⟩ : syracuseStep 953579 = 1430369) B1430369
theorem B39063647 : Blo 634301 39063647 := bstep (se 1 (by rfl) ⟨29297735, by rfl⟩ : syracuseStep 39063647 = 58595471) B58595471
theorem B1807055 : Blo 634301 1807055 := bstep (se 1 (by rfl) ⟨1355291, by rfl⟩ : syracuseStep 1807055 = 2710583) B2710583
theorem B955391 : Blo 634301 955391 := bstep (se 1 (by rfl) ⟨716543, by rfl⟩ : syracuseStep 955391 = 1433087) B1433087
theorem B956927 : Blo 634301 956927 := bstep (se 1 (by rfl) ⟨717695, by rfl⟩ : syracuseStep 956927 = 1435391) B1435391
theorem B957215 : Blo 634301 957215 := bstep (se 1 (by rfl) ⟨717911, by rfl⟩ : syracuseStep 957215 = 1435823) B1435823
theorem B1613803 : Blo 634301 1613803 := bstep (se 1 (by rfl) ⟨1210352, by rfl⟩ : syracuseStep 1613803 = 2420705) B2420705
theorem B4072331 : Blo 634301 4072331 := bstep (se 1 (by rfl) ⟨3054248, by rfl⟩ : syracuseStep 4072331 = 6108497) B6108497
theorem B2043035 : Blo 634301 2043035 := bstep (se 1 (by rfl) ⟨1532276, by rfl⟩ : syracuseStep 2043035 = 3064553) B3064553
theorem B2174255 : Blo 634301 2174255 := bstep (se 1 (by rfl) ⟨1630691, by rfl⟩ : syracuseStep 2174255 = 3261383) B3261383
theorem B634395 : Blo 634301 634395 := bstep (se 1 (by rfl) ⟨475796, by rfl⟩ : syracuseStep 634395 = 951593) B951593
theorem B634991 : Blo 634301 634991 := bstep (se 1 (by rfl) ⟨476243, by rfl⟩ : syracuseStep 634991 = 952487) B952487
theorem B636007 : Blo 634301 636007 := bstep (se 1 (by rfl) ⟨477005, by rfl⟩ : syracuseStep 636007 = 954011) B954011
theorem B637039 : Blo 634301 637039 := bstep (se 1 (by rfl) ⟨477779, by rfl⟩ : syracuseStep 637039 = 955559) B955559
theorem B15284371 : Blo 634301 15284371 := bstep (se 1 (by rfl) ⟨11463278, by rfl⟩ : syracuseStep 15284371 = 22926557) B22926557
theorem B6110113 : Blo 634301 6110113 := bstep (se 2 (by rfl) ⟨2291292, by rfl⟩ : syracuseStep 6110113 = 4582585) B4582585
theorem B638207 : Blo 634301 638207 := bstep (se 1 (by rfl) ⟨478655, by rfl⟩ : syracuseStep 638207 = 957311) B957311
theorem B802811 : Blo 634301 802811 := bstep (se 1 (by rfl) ⟨602108, by rfl⟩ : syracuseStep 802811 = 1204217) B1204217
theorem B2409983 : Blo 634301 2409983 := bstep (se 1 (by rfl) ⟨1807487, by rfl⟩ : syracuseStep 2409983 = 3614975) B3614975
theorem B4902889 : Blo 634301 4902889 := bstep (se 2 (by rfl) ⟨1838583, by rfl⟩ : syracuseStep 4902889 = 3677167) B3677167
theorem B4576823 : Blo 634301 4576823 := bstep (se 1 (by rfl) ⟨3432617, by rfl⟩ : syracuseStep 4576823 = 6865235) B6865235
theorem B1432799 : Blo 634301 1432799 := bstep (se 1 (by rfl) ⟨1074599, by rfl⟩ : syracuseStep 1432799 = 2149199) B2149199
theorem B33119563 : Blo 634301 33119563 := bstep (se 1 (by rfl) ⟨24839672, by rfl⟩ : syracuseStep 33119563 = 49679345) B49679345
theorem B283008941 : Blo 634301 283008941 := bstep (se 3 (by rfl) ⟨53064176, by rfl⟩ : syracuseStep 283008941 = 106128353) B106128353
theorem B3629555 : Blo 634301 3629555 := bstep (se 1 (by rfl) ⟨2722166, by rfl⟩ : syracuseStep 3629555 = 5444333) B5444333
theorem B69460487 : Blo 634301 69460487 := bstep (se 1 (by rfl) ⟨52095365, by rfl⟩ : syracuseStep 69460487 = 104190731) B104190731
theorem B1074971 : Blo 634301 1074971 := bstep (se 1 (by rfl) ⟨806228, by rfl⟩ : syracuseStep 1074971 = 1612457) B1612457
theorem B1075369 : Blo 634301 1075369 := bstep (se 2 (by rfl) ⟨403263, by rfl⟩ : syracuseStep 1075369 = 806527) B806527
theorem B1075963 : Blo 634301 1075963 := bstep (se 1 (by rfl) ⟨806972, by rfl⟩ : syracuseStep 1075963 = 1613945) B1613945
theorem B4583911 : Blo 634301 4583911 := bstep (se 1 (by rfl) ⟨3437933, by rfl⟩ : syracuseStep 4583911 = 6875867) B6875867
theorem B1606655 : Blo 634301 1606655 := bstep (se 1 (by rfl) ⟨1204991, by rfl⟩ : syracuseStep 1606655 = 2409983) B2409983
theorem B37816307 : Blo 634301 37816307 := bstep (se 1 (by rfl) ⟨28362230, by rfl⟩ : syracuseStep 37816307 = 56724461) B56724461
theorem B3051215 : Blo 634301 3051215 := bstep (se 1 (by rfl) ⟨2288411, by rfl⟩ : syracuseStep 3051215 = 4576823) B4576823
theorem B955199 : Blo 634301 955199 := bstep (se 1 (by rfl) ⟨716399, by rfl⟩ : syracuseStep 955199 = 1432799) B1432799
theorem B46306991 : Blo 634301 46306991 := bstep (se 1 (by rfl) ⟨34730243, by rfl⟩ : syracuseStep 46306991 = 69460487) B69460487
theorem B1449503 : Blo 634301 1449503 := bstep (se 1 (by rfl) ⟨1087127, by rfl⟩ : syracuseStep 1449503 = 2174255) B2174255
theorem B2140829 : Blo 634301 2140829 := bstep (se 3 (by rfl) ⟨401405, by rfl⟩ : syracuseStep 2140829 = 802811) B802811
theorem B634651 : Blo 634301 634651 := bstep (se 1 (by rfl) ⟨475988, by rfl⟩ : syracuseStep 634651 = 951977) B951977
theorem B635719 : Blo 634301 635719 := bstep (se 1 (by rfl) ⟨476789, by rfl⟩ : syracuseStep 635719 = 953579) B953579
theorem B636927 : Blo 634301 636927 := bstep (se 1 (by rfl) ⟨477695, by rfl⟩ : syracuseStep 636927 = 955391) B955391
theorem B637951 : Blo 634301 637951 := bstep (se 1 (by rfl) ⟨478463, by rfl⟩ : syracuseStep 637951 = 956927) B956927
theorem B638143 : Blo 634301 638143 := bstep (se 1 (by rfl) ⟨478607, by rfl⟩ : syracuseStep 638143 = 957215) B957215
theorem B6537185 : Blo 634301 6537185 := bstep (se 2 (by rfl) ⟨2451444, by rfl⟩ : syracuseStep 6537185 = 4902889) B4902889
theorem B6111881 : Blo 634301 6111881 := bstep (se 2 (by rfl) ⟨2291955, by rfl⟩ : syracuseStep 6111881 = 4583911) B4583911
theorem B1362023 : Blo 634301 1362023 := bstep (se 1 (by rfl) ⟨1021517, by rfl⟩ : syracuseStep 1362023 = 2043035) B2043035
theorem B8146817 : Blo 634301 8146817 := bstep (se 2 (by rfl) ⟨3055056, by rfl⟩ : syracuseStep 8146817 = 6110113) B6110113
theorem B44159417 : Blo 634301 44159417 := bstep (se 2 (by rfl) ⟨16559781, by rfl⟩ : syracuseStep 44159417 = 33119563) B33119563
theorem B2151737 : Blo 634301 2151737 := bstep (se 2 (by rfl) ⟨806901, by rfl⟩ : syracuseStep 2151737 = 1613803) B1613803
theorem B3103703 : Blo 634301 3103703 := bstep (se 1 (by rfl) ⟨2327777, by rfl⟩ : syracuseStep 3103703 = 4655555) B4655555
theorem B26042431 : Blo 634301 26042431 := bstep (se 1 (by rfl) ⟨19531823, by rfl⟩ : syracuseStep 26042431 = 39063647) B39063647
theorem B1433825 : Blo 634301 1433825 := bstep (se 2 (by rfl) ⟨537684, by rfl⟩ : syracuseStep 1433825 = 1075369) B1075369
theorem B1204703 : Blo 634301 1204703 := bstep (se 1 (by rfl) ⟨903527, by rfl⟩ : syracuseStep 1204703 = 1807055) B1807055
theorem B1434617 : Blo 634301 1434617 := bstep (se 2 (by rfl) ⟨537981, by rfl⟩ : syracuseStep 1434617 = 1075963) B1075963
theorem B188672627 : Blo 634301 188672627 := bstep (se 1 (by rfl) ⟨141504470, by rfl⟩ : syracuseStep 188672627 = 283008941) B283008941
theorem B2419703 : Blo 634301 2419703 := bstep (se 1 (by rfl) ⟨1814777, by rfl⟩ : syracuseStep 2419703 = 3629555) B3629555
theorem B2714887 : Blo 634301 2714887 := bstep (se 1 (by rfl) ⟨2036165, by rfl⟩ : syracuseStep 2714887 = 4072331) B4072331
theorem B716647 : Blo 634301 716647 := bstep (se 1 (by rfl) ⟨537485, by rfl⟩ : syracuseStep 716647 = 1074971) B1074971
theorem B20379161 : Blo 634301 20379161 := bstep (se 2 (by rfl) ⟨7642185, by rfl⟩ : syracuseStep 20379161 = 15284371) B15284371
theorem B2034143 : Blo 634301 2034143 := bstep (se 1 (by rfl) ⟨1525607, by rfl⟩ : syracuseStep 2034143 = 3051215) B3051215
theorem B30871327 : Blo 634301 30871327 := bstep (se 1 (by rfl) ⟨23153495, by rfl⟩ : syracuseStep 30871327 = 46306991) B46306991
theorem B2069135 : Blo 634301 2069135 := bstep (se 1 (by rfl) ⟨1551851, by rfl⟩ : syracuseStep 2069135 = 3103703) B3103703
theorem B955529 : Blo 634301 955529 := bstep (se 2 (by rfl) ⟨358323, by rfl⟩ : syracuseStep 955529 = 716647) B716647
theorem B955883 : Blo 634301 955883 := bstep (se 1 (by rfl) ⟨716912, by rfl⟩ : syracuseStep 955883 = 1433825) B1433825
theorem B956411 : Blo 634301 956411 := bstep (se 1 (by rfl) ⟨717308, by rfl⟩ : syracuseStep 956411 = 1434617) B1434617
theorem B1613135 : Blo 634301 1613135 := bstep (se 1 (by rfl) ⟨1209851, by rfl⟩ : syracuseStep 1613135 = 2419703) B2419703
theorem B4074587 : Blo 634301 4074587 := bstep (se 1 (by rfl) ⟨3055940, by rfl⟩ : syracuseStep 4074587 = 6111881) B6111881
theorem B25210871 : Blo 634301 25210871 := bstep (se 1 (by rfl) ⟨18908153, by rfl⟩ : syracuseStep 25210871 = 37816307) B37816307
theorem B29439611 : Blo 634301 29439611 := bstep (se 1 (by rfl) ⟨22079708, by rfl⟩ : syracuseStep 29439611 = 44159417) B44159417
theorem B636799 : Blo 634301 636799 := bstep (se 1 (by rfl) ⟨477599, by rfl⟩ : syracuseStep 636799 = 955199) B955199
theorem B54344429 : Blo 634301 54344429 := bstep (se 3 (by rfl) ⟨10189580, by rfl⟩ : syracuseStep 54344429 = 20379161) B20379161
theorem B3619849 : Blo 634301 3619849 := bstep (se 2 (by rfl) ⟨1357443, by rfl⟩ : syracuseStep 3619849 = 2714887) B2714887
theorem B966335 : Blo 634301 966335 := bstep (se 1 (by rfl) ⟨724751, by rfl⟩ : syracuseStep 966335 = 1449503) B1449503
theorem B803135 : Blo 634301 803135 := bstep (se 1 (by rfl) ⟨602351, by rfl⟩ : syracuseStep 803135 = 1204703) B1204703
theorem B125781751 : Blo 634301 125781751 := bstep (se 1 (by rfl) ⟨94336313, by rfl⟩ : syracuseStep 125781751 = 188672627) B188672627
theorem B1427219 : Blo 634301 1427219 := bstep (se 1 (by rfl) ⟨1070414, by rfl⟩ : syracuseStep 1427219 = 2140829) B2140829
theorem B34723241 : Blo 634301 34723241 := bstep (se 2 (by rfl) ⟨13021215, by rfl⟩ : syracuseStep 34723241 = 26042431) B26042431
theorem B1071103 : Blo 634301 1071103 := bstep (se 1 (by rfl) ⟨803327, by rfl⟩ : syracuseStep 1071103 = 1606655) B1606655
theorem B908015 : Blo 634301 908015 := bstep (se 1 (by rfl) ⟨681011, by rfl⟩ : syracuseStep 908015 = 1362023) B1362023
theorem B5431211 : Blo 634301 5431211 := bstep (se 1 (by rfl) ⟨4073408, by rfl⟩ : syracuseStep 5431211 = 8146817) B8146817
theorem B1434491 : Blo 634301 1434491 := bstep (se 1 (by rfl) ⟨1075868, by rfl⟩ : syracuseStep 1434491 = 2151737) B2151737
theorem B4358123 : Blo 634301 4358123 := bstep (se 1 (by rfl) ⟨3268592, by rfl⟩ : syracuseStep 4358123 = 6537185) B6537185
theorem B951479 : Blo 634301 951479 := bstep (se 1 (by rfl) ⟨713609, by rfl⟩ : syracuseStep 951479 = 1427219) B1427219
theorem B167709001 : Blo 634301 167709001 := bstep (se 2 (by rfl) ⟨62890875, by rfl⟩ : syracuseStep 167709001 = 125781751) B125781751
theorem B1379423 : Blo 634301 1379423 := bstep (se 1 (by rfl) ⟨1034567, by rfl⟩ : syracuseStep 1379423 = 2069135) B2069135
theorem B41161769 : Blo 634301 41161769 := bstep (se 2 (by rfl) ⟨15435663, by rfl⟩ : syracuseStep 41161769 = 30871327) B30871327
theorem B956327 : Blo 634301 956327 := bstep (se 1 (by rfl) ⟨717245, by rfl⟩ : syracuseStep 956327 = 1434491) B1434491
theorem B4826465 : Blo 634301 4826465 := bstep (se 2 (by rfl) ⟨1809924, by rfl⟩ : syracuseStep 4826465 = 3619849) B3619849
theorem B2141693 : Blo 634301 2141693 := bstep (se 3 (by rfl) ⟨401567, by rfl⟩ : syracuseStep 2141693 = 803135) B803135
theorem B1356095 : Blo 634301 1356095 := bstep (se 1 (by rfl) ⟨1017071, by rfl⟩ : syracuseStep 1356095 = 2034143) B2034143
theorem B637019 : Blo 634301 637019 := bstep (se 1 (by rfl) ⟨477764, by rfl⟩ : syracuseStep 637019 = 955529) B955529
theorem B23148827 : Blo 634301 23148827 := bstep (se 1 (by rfl) ⟨17361620, by rfl⟩ : syracuseStep 23148827 = 34723241) B34723241
theorem B637255 : Blo 634301 637255 := bstep (se 1 (by rfl) ⟨477941, by rfl⟩ : syracuseStep 637255 = 955883) B955883
theorem B637607 : Blo 634301 637607 := bstep (se 1 (by rfl) ⟨478205, by rfl⟩ : syracuseStep 637607 = 956411) B956411
theorem B3620807 : Blo 634301 3620807 := bstep (se 1 (by rfl) ⟨2715605, by rfl⟩ : syracuseStep 3620807 = 5431211) B5431211
theorem B10307573 : Blo 634301 10307573 := bstep (se 5 (by rfl) ⟨483167, by rfl⟩ : syracuseStep 10307573 = 966335) B966335
theorem B1428137 : Blo 634301 1428137 := bstep (se 2 (by rfl) ⟨535551, by rfl⟩ : syracuseStep 1428137 = 1071103) B1071103
theorem B36229619 : Blo 634301 36229619 := bstep (se 1 (by rfl) ⟨27172214, by rfl⟩ : syracuseStep 36229619 = 54344429) B54344429
theorem B2905415 : Blo 634301 2905415 := bstep (se 1 (by rfl) ⟨2179061, by rfl⟩ : syracuseStep 2905415 = 4358123) B4358123
theorem B1075423 : Blo 634301 1075423 := bstep (se 1 (by rfl) ⟨806567, by rfl⟩ : syracuseStep 1075423 = 1613135) B1613135
theorem B2421373 : Blo 634301 2421373 := bstep (se 3 (by rfl) ⟨454007, by rfl⟩ : syracuseStep 2421373 = 908015) B908015
theorem B2716391 : Blo 634301 2716391 := bstep (se 1 (by rfl) ⟨2037293, by rfl⟩ : syracuseStep 2716391 = 4074587) B4074587
theorem B16807247 : Blo 634301 16807247 := bstep (se 1 (by rfl) ⟨12605435, by rfl⟩ : syracuseStep 16807247 = 25210871) B25210871
theorem B19626407 : Blo 634301 19626407 := bstep (se 1 (by rfl) ⟨14719805, by rfl⟩ : syracuseStep 19626407 = 29439611) B29439611
theorem B952091 : Blo 634301 952091 := bstep (se 1 (by rfl) ⟨714068, by rfl⟩ : syracuseStep 952091 = 1428137) B1428137
theorem B919615 : Blo 634301 919615 := bstep (se 1 (by rfl) ⟨689711, by rfl⟩ : syracuseStep 919615 = 1379423) B1379423
theorem B24153079 : Blo 634301 24153079 := bstep (se 1 (by rfl) ⟨18114809, by rfl⟩ : syracuseStep 24153079 = 36229619) B36229619
theorem B223612001 : Blo 634301 223612001 := bstep (se 2 (by rfl) ⟨83854500, by rfl⟩ : syracuseStep 223612001 = 167709001) B167709001
theorem B1936943 : Blo 634301 1936943 := bstep (se 1 (by rfl) ⟨1452707, by rfl⟩ : syracuseStep 1936943 = 2905415) B2905415
theorem B3217643 : Blo 634301 3217643 := bstep (se 1 (by rfl) ⟨2413232, by rfl⟩ : syracuseStep 3217643 = 4826465) B4826465
theorem B1810927 : Blo 634301 1810927 := bstep (se 1 (by rfl) ⟨1358195, by rfl⟩ : syracuseStep 1810927 = 2716391) B2716391
theorem B13084271 : Blo 634301 13084271 := bstep (se 1 (by rfl) ⟨9813203, by rfl⟩ : syracuseStep 13084271 = 19626407) B19626407
theorem B634319 : Blo 634301 634319 := bstep (se 1 (by rfl) ⟨475739, by rfl⟩ : syracuseStep 634319 = 951479) B951479
theorem B27441179 : Blo 634301 27441179 := bstep (se 1 (by rfl) ⟨20580884, by rfl⟩ : syracuseStep 27441179 = 41161769) B41161769
theorem B637551 : Blo 634301 637551 := bstep (se 1 (by rfl) ⟨478163, by rfl⟩ : syracuseStep 637551 = 956327) B956327
theorem B3228497 : Blo 634301 3228497 := bstep (se 2 (by rfl) ⟨1210686, by rfl⟩ : syracuseStep 3228497 = 2421373) B2421373
theorem B1427795 : Blo 634301 1427795 := bstep (se 1 (by rfl) ⟨1070846, by rfl⟩ : syracuseStep 1427795 = 2141693) B2141693
theorem B904063 : Blo 634301 904063 := bstep (se 1 (by rfl) ⟨678047, by rfl⟩ : syracuseStep 904063 = 1356095) B1356095
theorem B2413871 : Blo 634301 2413871 := bstep (se 1 (by rfl) ⟨1810403, by rfl⟩ : syracuseStep 2413871 = 3620807) B3620807
theorem B6871715 : Blo 634301 6871715 := bstep (se 1 (by rfl) ⟨5153786, by rfl⟩ : syracuseStep 6871715 = 10307573) B10307573
theorem B1433897 : Blo 634301 1433897 := bstep (se 2 (by rfl) ⟨537711, by rfl⟩ : syracuseStep 1433897 = 1075423) B1075423
theorem B11204831 : Blo 634301 11204831 := bstep (se 1 (by rfl) ⟨8403623, by rfl⟩ : syracuseStep 11204831 = 16807247) B16807247
theorem B15432551 : Blo 634301 15432551 := bstep (se 1 (by rfl) ⟨11574413, by rfl⟩ : syracuseStep 15432551 = 23148827) B23148827
theorem B951863 : Blo 634301 951863 := bstep (se 1 (by rfl) ⟨713897, by rfl⟩ : syracuseStep 951863 = 1427795) B1427795
theorem B1609247 : Blo 634301 1609247 := bstep (se 1 (by rfl) ⟨1206935, by rfl⟩ : syracuseStep 1609247 = 2413871) B2413871
theorem B955931 : Blo 634301 955931 := bstep (se 1 (by rfl) ⟨716948, by rfl⟩ : syracuseStep 955931 = 1433897) B1433897
theorem B8722847 : Blo 634301 8722847 := bstep (se 1 (by rfl) ⟨6542135, by rfl⟩ : syracuseStep 8722847 = 13084271) B13084271
theorem B18294119 : Blo 634301 18294119 := bstep (se 1 (by rfl) ⟨13720589, by rfl⟩ : syracuseStep 18294119 = 27441179) B27441179
theorem B634727 : Blo 634301 634727 := bstep (se 1 (by rfl) ⟨476045, by rfl⟩ : syracuseStep 634727 = 952091) B952091
theorem B149074667 : Blo 634301 149074667 := bstep (se 1 (by rfl) ⟨111806000, by rfl⟩ : syracuseStep 149074667 = 223612001) B223612001
theorem B1291295 : Blo 634301 1291295 := bstep (se 1 (by rfl) ⟨968471, by rfl⟩ : syracuseStep 1291295 = 1936943) B1936943
theorem B1226153 : Blo 634301 1226153 := bstep (se 2 (by rfl) ⟨459807, by rfl⟩ : syracuseStep 1226153 = 919615) B919615
theorem B2145095 : Blo 634301 2145095 := bstep (se 1 (by rfl) ⟨1608821, by rfl⟩ : syracuseStep 2145095 = 3217643) B3217643
theorem B2152331 : Blo 634301 2152331 := bstep (se 1 (by rfl) ⟨1614248, by rfl⟩ : syracuseStep 2152331 = 3228497) B3228497
theorem B2414569 : Blo 634301 2414569 := bstep (se 2 (by rfl) ⟨905463, by rfl⟩ : syracuseStep 2414569 = 1810927) B1810927
theorem B1205417 : Blo 634301 1205417 := bstep (se 2 (by rfl) ⟨452031, by rfl⟩ : syracuseStep 1205417 = 904063) B904063
theorem B32204105 : Blo 634301 32204105 := bstep (se 2 (by rfl) ⟨12076539, by rfl⟩ : syracuseStep 32204105 = 24153079) B24153079
theorem B4581143 : Blo 634301 4581143 := bstep (se 1 (by rfl) ⟨3435857, by rfl⟩ : syracuseStep 4581143 = 6871715) B6871715
theorem B7469887 : Blo 634301 7469887 := bstep (se 1 (by rfl) ⟨5602415, by rfl⟩ : syracuseStep 7469887 = 11204831) B11204831
theorem B10288367 : Blo 634301 10288367 := bstep (se 1 (by rfl) ⟨7716275, by rfl⟩ : syracuseStep 10288367 = 15432551) B15432551
theorem B21469403 : Blo 634301 21469403 := bstep (se 1 (by rfl) ⟨16102052, by rfl⟩ : syracuseStep 21469403 = 32204105) B32204105
theorem B12196079 : Blo 634301 12196079 := bstep (se 1 (by rfl) ⟨9147059, by rfl⟩ : syracuseStep 12196079 = 18294119) B18294119
theorem B3054095 : Blo 634301 3054095 := bstep (se 1 (by rfl) ⟨2290571, by rfl⟩ : syracuseStep 3054095 = 4581143) B4581143
theorem B3219425 : Blo 634301 3219425 := bstep (se 2 (by rfl) ⟨1207284, by rfl⟩ : syracuseStep 3219425 = 2414569) B2414569
theorem B860863 : Blo 634301 860863 := bstep (se 1 (by rfl) ⟨645647, by rfl⟩ : syracuseStep 860863 = 1291295) B1291295
theorem B6858911 : Blo 634301 6858911 := bstep (se 1 (by rfl) ⟨5144183, by rfl⟩ : syracuseStep 6858911 = 10288367) B10288367
theorem B634575 : Blo 634301 634575 := bstep (se 1 (by rfl) ⟨475931, by rfl⟩ : syracuseStep 634575 = 951863) B951863
theorem B637287 : Blo 634301 637287 := bstep (se 1 (by rfl) ⟨477965, by rfl⟩ : syracuseStep 637287 = 955931) B955931
theorem B803611 : Blo 634301 803611 := bstep (se 1 (by rfl) ⟨602708, by rfl⟩ : syracuseStep 803611 = 1205417) B1205417
theorem B1430063 : Blo 634301 1430063 := bstep (se 1 (by rfl) ⟨1072547, by rfl⟩ : syracuseStep 1430063 = 2145095) B2145095
theorem B1072831 : Blo 634301 1072831 := bstep (se 1 (by rfl) ⟨804623, by rfl⟩ : syracuseStep 1072831 = 1609247) B1609247
theorem B1434887 : Blo 634301 1434887 := bstep (se 1 (by rfl) ⟨1076165, by rfl⟩ : syracuseStep 1434887 = 2152331) B2152331
theorem B23260925 : Blo 634301 23260925 := bstep (se 3 (by rfl) ⟨4361423, by rfl⟩ : syracuseStep 23260925 = 8722847) B8722847
theorem B99383111 : Blo 634301 99383111 := bstep (se 1 (by rfl) ⟨74537333, by rfl⟩ : syracuseStep 99383111 = 149074667) B149074667
theorem B817435 : Blo 634301 817435 := bstep (se 1 (by rfl) ⟨613076, by rfl⟩ : syracuseStep 817435 = 1226153) B1226153
theorem B9959849 : Blo 634301 9959849 := bstep (se 2 (by rfl) ⟨3734943, by rfl⟩ : syracuseStep 9959849 = 7469887) B7469887
theorem B1147817 : Blo 634301 1147817 := bstep (se 2 (by rfl) ⟨430431, by rfl⟩ : syracuseStep 1147817 = 860863) B860863
theorem B4359653 : Blo 634301 4359653 := bstep (se 4 (by rfl) ⟨408717, by rfl⟩ : syracuseStep 4359653 = 817435) B817435
theorem B953375 : Blo 634301 953375 := bstep (se 1 (by rfl) ⟨715031, by rfl⟩ : syracuseStep 953375 = 1430063) B1430063
theorem B8130719 : Blo 634301 8130719 := bstep (se 1 (by rfl) ⟨6098039, by rfl⟩ : syracuseStep 8130719 = 12196079) B12196079
theorem B2036063 : Blo 634301 2036063 := bstep (se 1 (by rfl) ⟨1527047, by rfl⟩ : syracuseStep 2036063 = 3054095) B3054095
theorem B956591 : Blo 634301 956591 := bstep (se 1 (by rfl) ⟨717443, by rfl⟩ : syracuseStep 956591 = 1434887) B1434887
theorem B15507283 : Blo 634301 15507283 := bstep (se 1 (by rfl) ⟨11630462, by rfl⟩ : syracuseStep 15507283 = 23260925) B23260925
theorem B2146283 : Blo 634301 2146283 := bstep (se 1 (by rfl) ⟨1609712, by rfl⟩ : syracuseStep 2146283 = 3219425) B3219425
theorem B4572607 : Blo 634301 4572607 := bstep (se 1 (by rfl) ⟨3429455, by rfl⟩ : syracuseStep 4572607 = 6858911) B6858911
theorem B6639899 : Blo 634301 6639899 := bstep (se 1 (by rfl) ⟨4979924, by rfl⟩ : syracuseStep 6639899 = 9959849) B9959849
theorem B1430441 : Blo 634301 1430441 := bstep (se 2 (by rfl) ⟨536415, by rfl⟩ : syracuseStep 1430441 = 1072831) B1072831
theorem B1071481 : Blo 634301 1071481 := bstep (se 2 (by rfl) ⟨401805, by rfl⟩ : syracuseStep 1071481 = 803611) B803611
theorem B14312935 : Blo 634301 14312935 := bstep (se 1 (by rfl) ⟨10734701, by rfl⟩ : syracuseStep 14312935 = 21469403) B21469403
theorem B66255407 : Blo 634301 66255407 := bstep (se 1 (by rfl) ⟨49691555, by rfl⟩ : syracuseStep 66255407 = 99383111) B99383111
theorem B6096809 : Blo 634301 6096809 := bstep (se 2 (by rfl) ⟨2286303, by rfl⟩ : syracuseStep 6096809 = 4572607) B4572607
theorem B953627 : Blo 634301 953627 := bstep (se 1 (by rfl) ⟨715220, by rfl⟩ : syracuseStep 953627 = 1430441) B1430441
theorem B765211 : Blo 634301 765211 := bstep (se 1 (by rfl) ⟨573908, by rfl⟩ : syracuseStep 765211 = 1147817) B1147817
theorem B17706397 : Blo 634301 17706397 := bstep (se 3 (by rfl) ⟨3319949, by rfl⟩ : syracuseStep 17706397 = 6639899) B6639899
theorem B635583 : Blo 634301 635583 := bstep (se 1 (by rfl) ⟨476687, by rfl⟩ : syracuseStep 635583 = 953375) B953375
theorem B5420479 : Blo 634301 5420479 := bstep (se 1 (by rfl) ⟨4065359, by rfl⟩ : syracuseStep 5420479 = 8130719) B8130719
theorem B637727 : Blo 634301 637727 := bstep (se 1 (by rfl) ⟨478295, by rfl⟩ : syracuseStep 637727 = 956591) B956591
theorem B76335653 : Blo 634301 76335653 := bstep (se 4 (by rfl) ⟨7156467, by rfl⟩ : syracuseStep 76335653 = 14312935) B14312935
theorem B1428641 : Blo 634301 1428641 := bstep (se 2 (by rfl) ⟨535740, by rfl⟩ : syracuseStep 1428641 = 1071481) B1071481
theorem B1430855 : Blo 634301 1430855 := bstep (se 1 (by rfl) ⟨1073141, by rfl⟩ : syracuseStep 1430855 = 2146283) B2146283
theorem B5429501 : Blo 634301 5429501 := bstep (se 3 (by rfl) ⟨1018031, by rfl⟩ : syracuseStep 5429501 = 2036063) B2036063
theorem B2906435 : Blo 634301 2906435 := bstep (se 1 (by rfl) ⟨2179826, by rfl⟩ : syracuseStep 2906435 = 4359653) B4359653
theorem B44170271 : Blo 634301 44170271 := bstep (se 1 (by rfl) ⟨33127703, by rfl⟩ : syracuseStep 44170271 = 66255407) B66255407
theorem B20676377 : Blo 634301 20676377 := bstep (se 2 (by rfl) ⟨7753641, by rfl⟩ : syracuseStep 20676377 = 15507283) B15507283
theorem B952427 : Blo 634301 952427 := bstep (se 1 (by rfl) ⟨714320, by rfl⟩ : syracuseStep 952427 = 1428641) B1428641
theorem B953903 : Blo 634301 953903 := bstep (se 1 (by rfl) ⟨715427, by rfl⟩ : syracuseStep 953903 = 1430855) B1430855
theorem B1937623 : Blo 634301 1937623 := bstep (se 1 (by rfl) ⟨1453217, by rfl⟩ : syracuseStep 1937623 = 2906435) B2906435
theorem B1020281 : Blo 634301 1020281 := bstep (se 2 (by rfl) ⟨382605, by rfl⟩ : syracuseStep 1020281 = 765211) B765211
theorem B16258157 : Blo 634301 16258157 := bstep (se 3 (by rfl) ⟨3048404, by rfl⟩ : syracuseStep 16258157 = 6096809) B6096809
theorem B203561741 : Blo 634301 203561741 := bstep (se 3 (by rfl) ⟨38167826, by rfl⟩ : syracuseStep 203561741 = 76335653) B76335653
theorem B635751 : Blo 634301 635751 := bstep (se 1 (by rfl) ⟨476813, by rfl⟩ : syracuseStep 635751 = 953627) B953627
theorem B3619667 : Blo 634301 3619667 := bstep (se 1 (by rfl) ⟨2714750, by rfl⟩ : syracuseStep 3619667 = 5429501) B5429501
theorem B23608529 : Blo 634301 23608529 := bstep (se 2 (by rfl) ⟨8853198, by rfl⟩ : syracuseStep 23608529 = 17706397) B17706397
theorem B7227305 : Blo 634301 7227305 := bstep (se 2 (by rfl) ⟨2710239, by rfl⟩ : syracuseStep 7227305 = 5420479) B5420479
theorem B29446847 : Blo 634301 29446847 := bstep (se 1 (by rfl) ⟨22085135, by rfl⟩ : syracuseStep 29446847 = 44170271) B44170271
theorem B13784251 : Blo 634301 13784251 := bstep (se 1 (by rfl) ⟨10338188, by rfl⟩ : syracuseStep 13784251 = 20676377) B20676377
theorem B2720749 : Blo 634301 2720749 := bstep (se 3 (by rfl) ⟨510140, by rfl⟩ : syracuseStep 2720749 = 1020281) B1020281
theorem B4818203 : Blo 634301 4818203 := bstep (se 1 (by rfl) ⟨3613652, by rfl⟩ : syracuseStep 4818203 = 7227305) B7227305
theorem B19631231 : Blo 634301 19631231 := bstep (se 1 (by rfl) ⟨14723423, by rfl⟩ : syracuseStep 19631231 = 29446847) B29446847
theorem B15739019 : Blo 634301 15739019 := bstep (se 1 (by rfl) ⟨11804264, by rfl⟩ : syracuseStep 15739019 = 23608529) B23608529
theorem B634951 : Blo 634301 634951 := bstep (se 1 (by rfl) ⟨476213, by rfl⟩ : syracuseStep 634951 = 952427) B952427
theorem B635935 : Blo 634301 635935 := bstep (se 1 (by rfl) ⟨476951, by rfl⟩ : syracuseStep 635935 = 953903) B953903
theorem B135707827 : Blo 634301 135707827 := bstep (se 1 (by rfl) ⟨101780870, by rfl⟩ : syracuseStep 135707827 = 203561741) B203561741
theorem B2413111 : Blo 634301 2413111 := bstep (se 1 (by rfl) ⟨1809833, by rfl⟩ : syracuseStep 2413111 = 3619667) B3619667
theorem B10838771 : Blo 634301 10838771 := bstep (se 1 (by rfl) ⟨8129078, by rfl⟩ : syracuseStep 10838771 = 16258157) B16258157
theorem B2583497 : Blo 634301 2583497 := bstep (se 2 (by rfl) ⟨968811, by rfl⟩ : syracuseStep 2583497 = 1937623) B1937623
theorem B18379001 : Blo 634301 18379001 := bstep (se 2 (by rfl) ⟨6892125, by rfl⟩ : syracuseStep 18379001 = 13784251) B13784251
theorem B3212135 : Blo 634301 3212135 := bstep (se 1 (by rfl) ⟨2409101, by rfl⟩ : syracuseStep 3212135 = 4818203) B4818203
theorem B3217481 : Blo 634301 3217481 := bstep (se 2 (by rfl) ⟨1206555, by rfl⟩ : syracuseStep 3217481 = 2413111) B2413111
theorem B10492679 : Blo 634301 10492679 := bstep (se 1 (by rfl) ⟨7869509, by rfl⟩ : syracuseStep 10492679 = 15739019) B15739019
theorem B13087487 : Blo 634301 13087487 := bstep (se 1 (by rfl) ⟨9815615, by rfl⟩ : syracuseStep 13087487 = 19631231) B19631231
theorem B7225847 : Blo 634301 7225847 := bstep (se 1 (by rfl) ⟨5419385, by rfl⟩ : syracuseStep 7225847 = 10838771) B10838771
theorem B1722331 : Blo 634301 1722331 := bstep (se 1 (by rfl) ⟨1291748, by rfl⟩ : syracuseStep 1722331 = 2583497) B2583497
theorem B3627665 : Blo 634301 3627665 := bstep (se 2 (by rfl) ⟨1360374, by rfl⟩ : syracuseStep 3627665 = 2720749) B2720749
theorem B12252667 : Blo 634301 12252667 := bstep (se 1 (by rfl) ⟨9189500, by rfl⟩ : syracuseStep 12252667 = 18379001) B18379001
theorem B180943769 : Blo 634301 180943769 := bstep (se 2 (by rfl) ⟨67853913, by rfl⟩ : syracuseStep 180943769 = 135707827) B135707827
theorem B4817231 : Blo 634301 4817231 := bstep (se 1 (by rfl) ⟨3612923, by rfl⟩ : syracuseStep 4817231 = 7225847) B7225847
theorem B2296441 : Blo 634301 2296441 := bstep (se 2 (by rfl) ⟨861165, by rfl⟩ : syracuseStep 2296441 = 1722331) B1722331
theorem B8724991 : Blo 634301 8724991 := bstep (se 1 (by rfl) ⟨6543743, by rfl⟩ : syracuseStep 8724991 = 13087487) B13087487
theorem B120629179 : Blo 634301 120629179 := bstep (se 1 (by rfl) ⟨90471884, by rfl⟩ : syracuseStep 120629179 = 180943769) B180943769
theorem B2141423 : Blo 634301 2141423 := bstep (se 1 (by rfl) ⟨1606067, by rfl⟩ : syracuseStep 2141423 = 3212135) B3212135
theorem B2144987 : Blo 634301 2144987 := bstep (se 1 (by rfl) ⟨1608740, by rfl⟩ : syracuseStep 2144987 = 3217481) B3217481
theorem B6995119 : Blo 634301 6995119 := bstep (se 1 (by rfl) ⟨5246339, by rfl⟩ : syracuseStep 6995119 = 10492679) B10492679
theorem B16336889 : Blo 634301 16336889 := bstep (se 2 (by rfl) ⟨6126333, by rfl⟩ : syracuseStep 16336889 = 12252667) B12252667
theorem B2418443 : Blo 634301 2418443 := bstep (se 1 (by rfl) ⟨1813832, by rfl⟩ : syracuseStep 2418443 = 3627665) B3627665
theorem B3211487 : Blo 634301 3211487 := bstep (se 1 (by rfl) ⟨2408615, by rfl⟩ : syracuseStep 3211487 = 4817231) B4817231
theorem B11633321 : Blo 634301 11633321 := bstep (se 2 (by rfl) ⟨4362495, by rfl⟩ : syracuseStep 11633321 = 8724991) B8724991
theorem B1612295 : Blo 634301 1612295 := bstep (se 1 (by rfl) ⟨1209221, by rfl⟩ : syracuseStep 1612295 = 2418443) B2418443
theorem B10891259 : Blo 634301 10891259 := bstep (se 1 (by rfl) ⟨8168444, by rfl⟩ : syracuseStep 10891259 = 16336889) B16336889
theorem B3061921 : Blo 634301 3061921 := bstep (se 2 (by rfl) ⟨1148220, by rfl⟩ : syracuseStep 3061921 = 2296441) B2296441
theorem B1427615 : Blo 634301 1427615 := bstep (se 1 (by rfl) ⟨1070711, by rfl⟩ : syracuseStep 1427615 = 2141423) B2141423
theorem B9326825 : Blo 634301 9326825 := bstep (se 2 (by rfl) ⟨3497559, by rfl⟩ : syracuseStep 9326825 = 6995119) B6995119
theorem B1429991 : Blo 634301 1429991 := bstep (se 1 (by rfl) ⟨1072493, by rfl⟩ : syracuseStep 1429991 = 2144987) B2144987
theorem B643355621 : Blo 634301 643355621 := bstep (se 4 (by rfl) ⟨60314589, by rfl⟩ : syracuseStep 643355621 = 120629179) B120629179
theorem B951743 : Blo 634301 951743 := bstep (se 1 (by rfl) ⟨713807, by rfl⟩ : syracuseStep 951743 = 1427615) B1427615
theorem B953327 : Blo 634301 953327 := bstep (se 1 (by rfl) ⟨714995, by rfl⟩ : syracuseStep 953327 = 1429991) B1429991
theorem B428903747 : Blo 634301 428903747 := bstep (se 1 (by rfl) ⟨321677810, by rfl⟩ : syracuseStep 428903747 = 643355621) B643355621
theorem B2140991 : Blo 634301 2140991 := bstep (se 1 (by rfl) ⟨1605743, by rfl⟩ : syracuseStep 2140991 = 3211487) B3211487
theorem B7260839 : Blo 634301 7260839 := bstep (se 1 (by rfl) ⟨5445629, by rfl⟩ : syracuseStep 7260839 = 10891259) B10891259
theorem B4082561 : Blo 634301 4082561 := bstep (se 2 (by rfl) ⟨1530960, by rfl⟩ : syracuseStep 4082561 = 3061921) B3061921
theorem B7755547 : Blo 634301 7755547 := bstep (se 1 (by rfl) ⟨5816660, by rfl⟩ : syracuseStep 7755547 = 11633321) B11633321
theorem B6217883 : Blo 634301 6217883 := bstep (se 1 (by rfl) ⟨4663412, by rfl⟩ : syracuseStep 6217883 = 9326825) B9326825
theorem B1074863 : Blo 634301 1074863 := bstep (se 1 (by rfl) ⟨806147, by rfl⟩ : syracuseStep 1074863 = 1612295) B1612295
theorem B2721707 : Blo 634301 2721707 := bstep (se 1 (by rfl) ⟨2041280, by rfl⟩ : syracuseStep 2721707 = 4082561) B4082561
theorem B285935831 : Blo 634301 285935831 := bstep (se 1 (by rfl) ⟨214451873, by rfl⟩ : syracuseStep 285935831 = 428903747) B428903747
theorem B634495 : Blo 634301 634495 := bstep (se 1 (by rfl) ⟨475871, by rfl⟩ : syracuseStep 634495 = 951743) B951743
theorem B635551 : Blo 634301 635551 := bstep (se 1 (by rfl) ⟨476663, by rfl⟩ : syracuseStep 635551 = 953327) B953327
theorem B4145255 : Blo 634301 4145255 := bstep (se 1 (by rfl) ⟨3108941, by rfl⟩ : syracuseStep 4145255 = 6217883) B6217883
theorem B1427327 : Blo 634301 1427327 := bstep (se 1 (by rfl) ⟨1070495, by rfl⟩ : syracuseStep 1427327 = 2140991) B2140991
theorem B10340729 : Blo 634301 10340729 := bstep (se 2 (by rfl) ⟨3877773, by rfl⟩ : syracuseStep 10340729 = 7755547) B7755547
theorem B4840559 : Blo 634301 4840559 := bstep (se 1 (by rfl) ⟨3630419, by rfl⟩ : syracuseStep 4840559 = 7260839) B7260839
theorem B716575 : Blo 634301 716575 := bstep (se 1 (by rfl) ⟨537431, by rfl⟩ : syracuseStep 716575 = 1074863) B1074863
theorem B951551 : Blo 634301 951551 := bstep (se 1 (by rfl) ⟨713663, by rfl⟩ : syracuseStep 951551 = 1427327) B1427327
theorem B955433 : Blo 634301 955433 := bstep (se 2 (by rfl) ⟨358287, by rfl⟩ : syracuseStep 955433 = 716575) B716575
theorem B2763503 : Blo 634301 2763503 := bstep (se 1 (by rfl) ⟨2072627, by rfl⟩ : syracuseStep 2763503 = 4145255) B4145255
theorem B1814471 : Blo 634301 1814471 := bstep (se 1 (by rfl) ⟨1360853, by rfl⟩ : syracuseStep 1814471 = 2721707) B2721707
theorem B190623887 : Blo 634301 190623887 := bstep (se 1 (by rfl) ⟨142967915, by rfl⟩ : syracuseStep 190623887 = 285935831) B285935831
theorem B6893819 : Blo 634301 6893819 := bstep (se 1 (by rfl) ⟨5170364, by rfl⟩ : syracuseStep 6893819 = 10340729) B10340729
theorem B3227039 : Blo 634301 3227039 := bstep (se 1 (by rfl) ⟨2420279, by rfl⟩ : syracuseStep 3227039 = 4840559) B4840559
theorem B1842335 : Blo 634301 1842335 := bstep (se 1 (by rfl) ⟨1381751, by rfl⟩ : syracuseStep 1842335 = 2763503) B2763503
theorem B127082591 : Blo 634301 127082591 := bstep (se 1 (by rfl) ⟨95311943, by rfl⟩ : syracuseStep 127082591 = 190623887) B190623887
theorem B4595879 : Blo 634301 4595879 := bstep (se 1 (by rfl) ⟨3446909, by rfl⟩ : syracuseStep 4595879 = 6893819) B6893819
theorem B634367 : Blo 634301 634367 := bstep (se 1 (by rfl) ⟨475775, by rfl⟩ : syracuseStep 634367 = 951551) B951551
theorem B636955 : Blo 634301 636955 := bstep (se 1 (by rfl) ⟨477716, by rfl⟩ : syracuseStep 636955 = 955433) B955433
theorem B2151359 : Blo 634301 2151359 := bstep (se 1 (by rfl) ⟨1613519, by rfl⟩ : syracuseStep 2151359 = 3227039) B3227039
theorem B1209647 : Blo 634301 1209647 := bstep (se 1 (by rfl) ⟨907235, by rfl⟩ : syracuseStep 1209647 = 1814471) B1814471
theorem B1228223 : Blo 634301 1228223 := bstep (se 1 (by rfl) ⟨921167, by rfl⟩ : syracuseStep 1228223 = 1842335) B1842335
theorem B84721727 : Blo 634301 84721727 := bstep (se 1 (by rfl) ⟨63541295, by rfl⟩ : syracuseStep 84721727 = 127082591) B127082591
theorem B3063919 : Blo 634301 3063919 := bstep (se 1 (by rfl) ⟨2297939, by rfl⟩ : syracuseStep 3063919 = 4595879) B4595879
theorem B806431 : Blo 634301 806431 := bstep (se 1 (by rfl) ⟨604823, by rfl⟩ : syracuseStep 806431 = 1209647) B1209647
theorem B1434239 : Blo 634301 1434239 := bstep (se 1 (by rfl) ⟨1075679, by rfl⟩ : syracuseStep 1434239 = 2151359) B2151359
theorem B956159 : Blo 634301 956159 := bstep (se 1 (by rfl) ⟨717119, by rfl⟩ : syracuseStep 956159 = 1434239) B1434239
theorem B56481151 : Blo 634301 56481151 := bstep (se 1 (by rfl) ⟨42360863, by rfl⟩ : syracuseStep 56481151 = 84721727) B84721727
theorem B4085225 : Blo 634301 4085225 := bstep (se 2 (by rfl) ⟨1531959, by rfl⟩ : syracuseStep 4085225 = 3063919) B3063919
theorem B1075241 : Blo 634301 1075241 := bstep (se 2 (by rfl) ⟨403215, by rfl⟩ : syracuseStep 1075241 = 806431) B806431
theorem B3275261 : Blo 634301 3275261 := bstep (se 3 (by rfl) ⟨614111, by rfl⟩ : syracuseStep 3275261 = 1228223) B1228223
theorem B2723483 : Blo 634301 2723483 := bstep (se 1 (by rfl) ⟨2042612, by rfl⟩ : syracuseStep 2723483 = 4085225) B4085225
theorem B75308201 : Blo 634301 75308201 := bstep (se 2 (by rfl) ⟨28240575, by rfl⟩ : syracuseStep 75308201 = 56481151) B56481151
theorem B637439 : Blo 634301 637439 := bstep (se 1 (by rfl) ⟨478079, by rfl⟩ : syracuseStep 637439 = 956159) B956159
theorem B2183507 : Blo 634301 2183507 := bstep (se 1 (by rfl) ⟨1637630, by rfl⟩ : syracuseStep 2183507 = 3275261) B3275261
theorem B716827 : Blo 634301 716827 := bstep (se 1 (by rfl) ⟨537620, by rfl⟩ : syracuseStep 716827 = 1075241) B1075241
theorem B50205467 : Blo 634301 50205467 := bstep (se 1 (by rfl) ⟨37654100, by rfl⟩ : syracuseStep 50205467 = 75308201) B75308201
theorem B955769 : Blo 634301 955769 := bstep (se 2 (by rfl) ⟨358413, by rfl⟩ : syracuseStep 955769 = 716827) B716827
theorem B1815655 : Blo 634301 1815655 := bstep (se 1 (by rfl) ⟨1361741, by rfl⟩ : syracuseStep 1815655 = 2723483) B2723483
theorem B1455671 : Blo 634301 1455671 := bstep (se 1 (by rfl) ⟨1091753, by rfl⟩ : syracuseStep 1455671 = 2183507) B2183507
theorem B637179 : Blo 634301 637179 := bstep (se 1 (by rfl) ⟨477884, by rfl⟩ : syracuseStep 637179 = 955769) B955769
theorem B3881789 : Blo 634301 3881789 := bstep (se 3 (by rfl) ⟨727835, by rfl⟩ : syracuseStep 3881789 = 1455671) B1455671
theorem B133881245 : Blo 634301 133881245 := bstep (se 3 (by rfl) ⟨25102733, by rfl⟩ : syracuseStep 133881245 = 50205467) B50205467
theorem B2420873 : Blo 634301 2420873 := bstep (se 2 (by rfl) ⟨907827, by rfl⟩ : syracuseStep 2420873 = 1815655) B1815655
theorem B1613915 : Blo 634301 1613915 := bstep (se 1 (by rfl) ⟨1210436, by rfl⟩ : syracuseStep 1613915 = 2420873) B2420873
theorem B89254163 : Blo 634301 89254163 := bstep (se 1 (by rfl) ⟨66940622, by rfl⟩ : syracuseStep 89254163 = 133881245) B133881245
theorem B2587859 : Blo 634301 2587859 := bstep (se 1 (by rfl) ⟨1940894, by rfl⟩ : syracuseStep 2587859 = 3881789) B3881789
theorem B1725239 : Blo 634301 1725239 := bstep (se 1 (by rfl) ⟨1293929, by rfl⟩ : syracuseStep 1725239 = 2587859) B2587859
theorem B1075943 : Blo 634301 1075943 := bstep (se 1 (by rfl) ⟨806957, by rfl⟩ : syracuseStep 1075943 = 1613915) B1613915
theorem B59502775 : Blo 634301 59502775 := bstep (se 1 (by rfl) ⟨44627081, by rfl⟩ : syracuseStep 59502775 = 89254163) B89254163
theorem B79337033 : Blo 634301 79337033 := bstep (se 2 (by rfl) ⟨29751387, by rfl⟩ : syracuseStep 79337033 = 59502775) B59502775
theorem B4600637 : Blo 634301 4600637 := bstep (se 3 (by rfl) ⟨862619, by rfl⟩ : syracuseStep 4600637 = 1725239) B1725239
theorem B717295 : Blo 634301 717295 := bstep (se 1 (by rfl) ⟨537971, by rfl⟩ : syracuseStep 717295 = 1075943) B1075943
theorem B52891355 : Blo 634301 52891355 := bstep (se 1 (by rfl) ⟨39668516, by rfl⟩ : syracuseStep 52891355 = 79337033) B79337033
theorem B956393 : Blo 634301 956393 := bstep (se 2 (by rfl) ⟨358647, by rfl⟩ : syracuseStep 956393 = 717295) B717295
theorem B3067091 : Blo 634301 3067091 := bstep (se 1 (by rfl) ⟨2300318, by rfl⟩ : syracuseStep 3067091 = 4600637) B4600637
theorem B35260903 : Blo 634301 35260903 := bstep (se 1 (by rfl) ⟨26445677, by rfl⟩ : syracuseStep 35260903 = 52891355) B52891355
theorem B2044727 : Blo 634301 2044727 := bstep (se 1 (by rfl) ⟨1533545, by rfl⟩ : syracuseStep 2044727 = 3067091) B3067091
theorem B637595 : Blo 634301 637595 := bstep (se 1 (by rfl) ⟨478196, by rfl⟩ : syracuseStep 637595 = 956393) B956393
theorem B188058149 : Blo 634301 188058149 := bstep (se 4 (by rfl) ⟨17630451, by rfl⟩ : syracuseStep 188058149 = 35260903) B35260903
theorem B1363151 : Blo 634301 1363151 := bstep (se 1 (by rfl) ⟨1022363, by rfl⟩ : syracuseStep 1363151 = 2044727) B2044727
theorem B125372099 : Blo 634301 125372099 := bstep (se 1 (by rfl) ⟨94029074, by rfl⟩ : syracuseStep 125372099 = 188058149) B188058149
theorem B908767 : Blo 634301 908767 := bstep (se 1 (by rfl) ⟨681575, by rfl⟩ : syracuseStep 908767 = 1363151) B1363151
theorem B83581399 : Blo 634301 83581399 := bstep (se 1 (by rfl) ⟨62686049, by rfl⟩ : syracuseStep 83581399 = 125372099) B125372099
theorem B1211689 : Blo 634301 1211689 := bstep (se 2 (by rfl) ⟨454383, by rfl⟩ : syracuseStep 1211689 = 908767) B908767
theorem B1615585 : Blo 634301 1615585 := bstep (se 2 (by rfl) ⟨605844, by rfl⟩ : syracuseStep 1615585 = 1211689) B1211689
theorem B111441865 : Blo 634301 111441865 := bstep (se 2 (by rfl) ⟨41790699, by rfl⟩ : syracuseStep 111441865 = 83581399) B83581399
theorem B148589153 : Blo 634301 148589153 := bstep (se 2 (by rfl) ⟨55720932, by rfl⟩ : syracuseStep 148589153 = 111441865) B111441865
theorem B2154113 : Blo 634301 2154113 := bstep (se 2 (by rfl) ⟨807792, by rfl⟩ : syracuseStep 2154113 = 1615585) B1615585
theorem B99059435 : Blo 634301 99059435 := bstep (se 1 (by rfl) ⟨74294576, by rfl⟩ : syracuseStep 99059435 = 148589153) B148589153
theorem B1436075 : Blo 634301 1436075 := bstep (se 1 (by rfl) ⟨1077056, by rfl⟩ : syracuseStep 1436075 = 2154113) B2154113
theorem B957383 : Blo 634301 957383 := bstep (se 1 (by rfl) ⟨718037, by rfl⟩ : syracuseStep 957383 = 1436075) B1436075
theorem B66039623 : Blo 634301 66039623 := bstep (se 1 (by rfl) ⟨49529717, by rfl⟩ : syracuseStep 66039623 = 99059435) B99059435
theorem B638255 : Blo 634301 638255 := bstep (se 1 (by rfl) ⟨478691, by rfl⟩ : syracuseStep 638255 = 957383) B957383
theorem B44026415 : Blo 634301 44026415 := bstep (se 1 (by rfl) ⟨33019811, by rfl⟩ : syracuseStep 44026415 = 66039623) B66039623
theorem B29350943 : Blo 634301 29350943 := bstep (se 1 (by rfl) ⟨22013207, by rfl⟩ : syracuseStep 29350943 = 44026415) B44026415
theorem B19567295 : Blo 634301 19567295 := bstep (se 1 (by rfl) ⟨14675471, by rfl⟩ : syracuseStep 19567295 = 29350943) B29350943
theorem B13044863 : Blo 634301 13044863 := bstep (se 1 (by rfl) ⟨9783647, by rfl⟩ : syracuseStep 13044863 = 19567295) B19567295
theorem B8696575 : Blo 634301 8696575 := bstep (se 1 (by rfl) ⟨6522431, by rfl⟩ : syracuseStep 8696575 = 13044863) B13044863
theorem B11595433 : Blo 634301 11595433 := bstep (se 2 (by rfl) ⟨4348287, by rfl⟩ : syracuseStep 11595433 = 8696575) B8696575
theorem B15460577 : Blo 634301 15460577 := bstep (se 2 (by rfl) ⟨5797716, by rfl⟩ : syracuseStep 15460577 = 11595433) B11595433
theorem B10307051 : Blo 634301 10307051 := bstep (se 1 (by rfl) ⟨7730288, by rfl⟩ : syracuseStep 10307051 = 15460577) B15460577
theorem B6871367 : Blo 634301 6871367 := bstep (se 1 (by rfl) ⟨5153525, by rfl⟩ : syracuseStep 6871367 = 10307051) B10307051
theorem B4580911 : Blo 634301 4580911 := bstep (se 1 (by rfl) ⟨3435683, by rfl⟩ : syracuseStep 4580911 = 6871367) B6871367
theorem B6107881 : Blo 634301 6107881 := bstep (se 2 (by rfl) ⟨2290455, by rfl⟩ : syracuseStep 6107881 = 4580911) B4580911
theorem B8143841 : Blo 634301 8143841 := bstep (se 2 (by rfl) ⟨3053940, by rfl⟩ : syracuseStep 8143841 = 6107881) B6107881
theorem B5429227 : Blo 634301 5429227 := bstep (se 1 (by rfl) ⟨4071920, by rfl⟩ : syracuseStep 5429227 = 8143841) B8143841
theorem B7238969 : Blo 634301 7238969 := bstep (se 2 (by rfl) ⟨2714613, by rfl⟩ : syracuseStep 7238969 = 5429227) B5429227
theorem B4825979 : Blo 634301 4825979 := bstep (se 1 (by rfl) ⟨3619484, by rfl⟩ : syracuseStep 4825979 = 7238969) B7238969
theorem B3217319 : Blo 634301 3217319 := bstep (se 1 (by rfl) ⟨2412989, by rfl⟩ : syracuseStep 3217319 = 4825979) B4825979
theorem B2144879 : Blo 634301 2144879 := bstep (se 1 (by rfl) ⟨1608659, by rfl⟩ : syracuseStep 2144879 = 3217319) B3217319
theorem B1429919 : Blo 634301 1429919 := bstep (se 1 (by rfl) ⟨1072439, by rfl⟩ : syracuseStep 1429919 = 2144879) B2144879
theorem B953279 : Blo 634301 953279 := bstep (se 1 (by rfl) ⟨714959, by rfl⟩ : syracuseStep 953279 = 1429919) B1429919
theorem B635519 : Blo 634301 635519 := bstep (se 1 (by rfl) ⟨476639, by rfl⟩ : syracuseStep 635519 = 953279) B953279

theorem C0 (j : ℕ) (h1 : 158575 ≤ j) (h2 : j ≤ 159274) : Blo 634301 (4 * j + 3) := by
  interval_cases j
  · exact B634303
  · exact B634307
  · exact B634311
  · exact B634315
  · exact B634319
  · exact B634323
  · exact B634327
  · exact B634331
  · exact B634335
  · exact B634339
  · exact B634343
  · exact B634347
  · exact B634351
  · exact B634355
  · exact B634359
  · exact B634363
  · exact B634367
  · exact B634371
  · exact B634375
  · exact B634379
  · exact B634383
  · exact B634387
  · exact B634391
  · exact B634395
  · exact B634399
  · exact B634403
  · exact B634407
  · exact B634411
  · exact B634415
  · exact B634419
  · exact B634423
  · exact B634427
  · exact B634431
  · exact B634435
  · exact B634439
  · exact B634443
  · exact B634447
  · exact B634451
  · exact B634455
  · exact B634459
  · exact B634463
  · exact B634467
  · exact B634471
  · exact B634475
  · exact B634479
  · exact B634483
  · exact B634487
  · exact B634491
  · exact B634495
  · exact B634499
  · exact B634503
  · exact B634507
  · exact B634511
  · exact B634515
  · exact B634519
  · exact B634523
  · exact B634527
  · exact B634531
  · exact B634535
  · exact B634539
  · exact B634543
  · exact B634547
  · exact B634551
  · exact B634555
  · exact B634559
  · exact B634563
  · exact B634567
  · exact B634571
  · exact B634575
  · exact B634579
  · exact B634583
  · exact B634587
  · exact B634591
  · exact B634595
  · exact B634599
  · exact B634603
  · exact B634607
  · exact B634611
  · exact B634615
  · exact B634619
  · exact B634623
  · exact B634627
  · exact B634631
  · exact B634635
  · exact B634639
  · exact B634643
  · exact B634647
  · exact B634651
  · exact B634655
  · exact B634659
  · exact B634663
  · exact B634667
  · exact B634671
  · exact B634675
  · exact B634679
  · exact B634683
  · exact B634687
  · exact B634691
  · exact B634695
  · exact B634699
  · exact B634703
  · exact B634707
  · exact B634711
  · exact B634715
  · exact B634719
  · exact B634723
  · exact B634727
  · exact B634731
  · exact B634735
  · exact B634739
  · exact B634743
  · exact B634747
  · exact B634751
  · exact B634755
  · exact B634759
  · exact B634763
  · exact B634767
  · exact B634771
  · exact B634775
  · exact B634779
  · exact B634783
  · exact B634787
  · exact B634791
  · exact B634795
  · exact B634799
  · exact B634803
  · exact B634807
  · exact B634811
  · exact B634815
  · exact B634819
  · exact B634823
  · exact B634827
  · exact B634831
  · exact B634835
  · exact B634839
  · exact B634843
  · exact B634847
  · exact B634851
  · exact B634855
  · exact B634859
  · exact B634863
  · exact B634867
  · exact B634871
  · exact B634875
  · exact B634879
  · exact B634883
  · exact B634887
  · exact B634891
  · exact B634895
  · exact B634899
  · exact B634903
  · exact B634907
  · exact B634911
  · exact B634915
  · exact B634919
  · exact B634923
  · exact B634927
  · exact B634931
  · exact B634935
  · exact B634939
  · exact B634943
  · exact B634947
  · exact B634951
  · exact B634955
  · exact B634959
  · exact B634963
  · exact B634967
  · exact B634971
  · exact B634975
  · exact B634979
  · exact B634983
  · exact B634987
  · exact B634991
  · exact B634995
  · exact B634999
  · exact B635003
  · exact B635007
  · exact B635011
  · exact B635015
  · exact B635019
  · exact B635023
  · exact B635027
  · exact B635031
  · exact B635035
  · exact B635039
  · exact B635043
  · exact B635047
  · exact B635051
  · exact B635055
  · exact B635059
  · exact B635063
  · exact B635067
  · exact B635071
  · exact B635075
  · exact B635079
  · exact B635083
  · exact B635087
  · exact B635091
  · exact B635095
  · exact B635099
  · exact B635103
  · exact B635107
  · exact B635111
  · exact B635115
  · exact B635119
  · exact B635123
  · exact B635127
  · exact B635131
  · exact B635135
  · exact B635139
  · exact B635143
  · exact B635147
  · exact B635151
  · exact B635155
  · exact B635159
  · exact B635163
  · exact B635167
  · exact B635171
  · exact B635175
  · exact B635179
  · exact B635183
  · exact B635187
  · exact B635191
  · exact B635195
  · exact B635199
  · exact B635203
  · exact B635207
  · exact B635211
  · exact B635215
  · exact B635219
  · exact B635223
  · exact B635227
  · exact B635231
  · exact B635235
  · exact B635239
  · exact B635243
  · exact B635247
  · exact B635251
  · exact B635255
  · exact B635259
  · exact B635263
  · exact B635267
  · exact B635271
  · exact B635275
  · exact B635279
  · exact B635283
  · exact B635287
  · exact B635291
  · exact B635295
  · exact B635299
  · exact B635303
  · exact B635307
  · exact B635311
  · exact B635315
  · exact B635319
  · exact B635323
  · exact B635327
  · exact B635331
  · exact B635335
  · exact B635339
  · exact B635343
  · exact B635347
  · exact B635351
  · exact B635355
  · exact B635359
  · exact B635363
  · exact B635367
  · exact B635371
  · exact B635375
  · exact B635379
  · exact B635383
  · exact B635387
  · exact B635391
  · exact B635395
  · exact B635399
  · exact B635403
  · exact B635407
  · exact B635411
  · exact B635415
  · exact B635419
  · exact B635423
  · exact B635427
  · exact B635431
  · exact B635435
  · exact B635439
  · exact B635443
  · exact B635447
  · exact B635451
  · exact B635455
  · exact B635459
  · exact B635463
  · exact B635467
  · exact B635471
  · exact B635475
  · exact B635479
  · exact B635483
  · exact B635487
  · exact B635491
  · exact B635495
  · exact B635499
  · exact B635503
  · exact B635507
  · exact B635511
  · exact B635515
  · exact B635519
  · exact B635523
  · exact B635527
  · exact B635531
  · exact B635535
  · exact B635539
  · exact B635543
  · exact B635547
  · exact B635551
  · exact B635555
  · exact B635559
  · exact B635563
  · exact B635567
  · exact B635571
  · exact B635575
  · exact B635579
  · exact B635583
  · exact B635587
  · exact B635591
  · exact B635595
  · exact B635599
  · exact B635603
  · exact B635607
  · exact B635611
  · exact B635615
  · exact B635619
  · exact B635623
  · exact B635627
  · exact B635631
  · exact B635635
  · exact B635639
  · exact B635643
  · exact B635647
  · exact B635651
  · exact B635655
  · exact B635659
  · exact B635663
  · exact B635667
  · exact B635671
  · exact B635675
  · exact B635679
  · exact B635683
  · exact B635687
  · exact B635691
  · exact B635695
  · exact B635699
  · exact B635703
  · exact B635707
  · exact B635711
  · exact B635715
  · exact B635719
  · exact B635723
  · exact B635727
  · exact B635731
  · exact B635735
  · exact B635739
  · exact B635743
  · exact B635747
  · exact B635751
  · exact B635755
  · exact B635759
  · exact B635763
  · exact B635767
  · exact B635771
  · exact B635775
  · exact B635779
  · exact B635783
  · exact B635787
  · exact B635791
  · exact B635795
  · exact B635799
  · exact B635803
  · exact B635807
  · exact B635811
  · exact B635815
  · exact B635819
  · exact B635823
  · exact B635827
  · exact B635831
  · exact B635835
  · exact B635839
  · exact B635843
  · exact B635847
  · exact B635851
  · exact B635855
  · exact B635859
  · exact B635863
  · exact B635867
  · exact B635871
  · exact B635875
  · exact B635879
  · exact B635883
  · exact B635887
  · exact B635891
  · exact B635895
  · exact B635899
  · exact B635903
  · exact B635907
  · exact B635911
  · exact B635915
  · exact B635919
  · exact B635923
  · exact B635927
  · exact B635931
  · exact B635935
  · exact B635939
  · exact B635943
  · exact B635947
  · exact B635951
  · exact B635955
  · exact B635959
  · exact B635963
  · exact B635967
  · exact B635971
  · exact B635975
  · exact B635979
  · exact B635983
  · exact B635987
  · exact B635991
  · exact B635995
  · exact B635999
  · exact B636003
  · exact B636007
  · exact B636011
  · exact B636015
  · exact B636019
  · exact B636023
  · exact B636027
  · exact B636031
  · exact B636035
  · exact B636039
  · exact B636043
  · exact B636047
  · exact B636051
  · exact B636055
  · exact B636059
  · exact B636063
  · exact B636067
  · exact B636071
  · exact B636075
  · exact B636079
  · exact B636083
  · exact B636087
  · exact B636091
  · exact B636095
  · exact B636099
  · exact B636103
  · exact B636107
  · exact B636111
  · exact B636115
  · exact B636119
  · exact B636123
  · exact B636127
  · exact B636131
  · exact B636135
  · exact B636139
  · exact B636143
  · exact B636147
  · exact B636151
  · exact B636155
  · exact B636159
  · exact B636163
  · exact B636167
  · exact B636171
  · exact B636175
  · exact B636179
  · exact B636183
  · exact B636187
  · exact B636191
  · exact B636195
  · exact B636199
  · exact B636203
  · exact B636207
  · exact B636211
  · exact B636215
  · exact B636219
  · exact B636223
  · exact B636227
  · exact B636231
  · exact B636235
  · exact B636239
  · exact B636243
  · exact B636247
  · exact B636251
  · exact B636255
  · exact B636259
  · exact B636263
  · exact B636267
  · exact B636271
  · exact B636275
  · exact B636279
  · exact B636283
  · exact B636287
  · exact B636291
  · exact B636295
  · exact B636299
  · exact B636303
  · exact B636307
  · exact B636311
  · exact B636315
  · exact B636319
  · exact B636323
  · exact B636327
  · exact B636331
  · exact B636335
  · exact B636339
  · exact B636343
  · exact B636347
  · exact B636351
  · exact B636355
  · exact B636359
  · exact B636363
  · exact B636367
  · exact B636371
  · exact B636375
  · exact B636379
  · exact B636383
  · exact B636387
  · exact B636391
  · exact B636395
  · exact B636399
  · exact B636403
  · exact B636407
  · exact B636411
  · exact B636415
  · exact B636419
  · exact B636423
  · exact B636427
  · exact B636431
  · exact B636435
  · exact B636439
  · exact B636443
  · exact B636447
  · exact B636451
  · exact B636455
  · exact B636459
  · exact B636463
  · exact B636467
  · exact B636471
  · exact B636475
  · exact B636479
  · exact B636483
  · exact B636487
  · exact B636491
  · exact B636495
  · exact B636499
  · exact B636503
  · exact B636507
  · exact B636511
  · exact B636515
  · exact B636519
  · exact B636523
  · exact B636527
  · exact B636531
  · exact B636535
  · exact B636539
  · exact B636543
  · exact B636547
  · exact B636551
  · exact B636555
  · exact B636559
  · exact B636563
  · exact B636567
  · exact B636571
  · exact B636575
  · exact B636579
  · exact B636583
  · exact B636587
  · exact B636591
  · exact B636595
  · exact B636599
  · exact B636603
  · exact B636607
  · exact B636611
  · exact B636615
  · exact B636619
  · exact B636623
  · exact B636627
  · exact B636631
  · exact B636635
  · exact B636639
  · exact B636643
  · exact B636647
  · exact B636651
  · exact B636655
  · exact B636659
  · exact B636663
  · exact B636667
  · exact B636671
  · exact B636675
  · exact B636679
  · exact B636683
  · exact B636687
  · exact B636691
  · exact B636695
  · exact B636699
  · exact B636703
  · exact B636707
  · exact B636711
  · exact B636715
  · exact B636719
  · exact B636723
  · exact B636727
  · exact B636731
  · exact B636735
  · exact B636739
  · exact B636743
  · exact B636747
  · exact B636751
  · exact B636755
  · exact B636759
  · exact B636763
  · exact B636767
  · exact B636771
  · exact B636775
  · exact B636779
  · exact B636783
  · exact B636787
  · exact B636791
  · exact B636795
  · exact B636799
  · exact B636803
  · exact B636807
  · exact B636811
  · exact B636815
  · exact B636819
  · exact B636823
  · exact B636827
  · exact B636831
  · exact B636835
  · exact B636839
  · exact B636843
  · exact B636847
  · exact B636851
  · exact B636855
  · exact B636859
  · exact B636863
  · exact B636867
  · exact B636871
  · exact B636875
  · exact B636879
  · exact B636883
  · exact B636887
  · exact B636891
  · exact B636895
  · exact B636899
  · exact B636903
  · exact B636907
  · exact B636911
  · exact B636915
  · exact B636919
  · exact B636923
  · exact B636927
  · exact B636931
  · exact B636935
  · exact B636939
  · exact B636943
  · exact B636947
  · exact B636951
  · exact B636955
  · exact B636959
  · exact B636963
  · exact B636967
  · exact B636971
  · exact B636975
  · exact B636979
  · exact B636983
  · exact B636987
  · exact B636991
  · exact B636995
  · exact B636999
  · exact B637003
  · exact B637007
  · exact B637011
  · exact B637015
  · exact B637019
  · exact B637023
  · exact B637027
  · exact B637031
  · exact B637035
  · exact B637039
  · exact B637043
  · exact B637047
  · exact B637051
  · exact B637055
  · exact B637059
  · exact B637063
  · exact B637067
  · exact B637071
  · exact B637075
  · exact B637079
  · exact B637083
  · exact B637087
  · exact B637091
  · exact B637095
  · exact B637099

theorem C1 (j : ℕ) (h1 : 159275 ≤ j) (h2 : j ≤ 159574) : Blo 634301 (4 * j + 3) := by
  interval_cases j
  · exact B637103
  · exact B637107
  · exact B637111
  · exact B637115
  · exact B637119
  · exact B637123
  · exact B637127
  · exact B637131
  · exact B637135
  · exact B637139
  · exact B637143
  · exact B637147
  · exact B637151
  · exact B637155
  · exact B637159
  · exact B637163
  · exact B637167
  · exact B637171
  · exact B637175
  · exact B637179
  · exact B637183
  · exact B637187
  · exact B637191
  · exact B637195
  · exact B637199
  · exact B637203
  · exact B637207
  · exact B637211
  · exact B637215
  · exact B637219
  · exact B637223
  · exact B637227
  · exact B637231
  · exact B637235
  · exact B637239
  · exact B637243
  · exact B637247
  · exact B637251
  · exact B637255
  · exact B637259
  · exact B637263
  · exact B637267
  · exact B637271
  · exact B637275
  · exact B637279
  · exact B637283
  · exact B637287
  · exact B637291
  · exact B637295
  · exact B637299
  · exact B637303
  · exact B637307
  · exact B637311
  · exact B637315
  · exact B637319
  · exact B637323
  · exact B637327
  · exact B637331
  · exact B637335
  · exact B637339
  · exact B637343
  · exact B637347
  · exact B637351
  · exact B637355
  · exact B637359
  · exact B637363
  · exact B637367
  · exact B637371
  · exact B637375
  · exact B637379
  · exact B637383
  · exact B637387
  · exact B637391
  · exact B637395
  · exact B637399
  · exact B637403
  · exact B637407
  · exact B637411
  · exact B637415
  · exact B637419
  · exact B637423
  · exact B637427
  · exact B637431
  · exact B637435
  · exact B637439
  · exact B637443
  · exact B637447
  · exact B637451
  · exact B637455
  · exact B637459
  · exact B637463
  · exact B637467
  · exact B637471
  · exact B637475
  · exact B637479
  · exact B637483
  · exact B637487
  · exact B637491
  · exact B637495
  · exact B637499
  · exact B637503
  · exact B637507
  · exact B637511
  · exact B637515
  · exact B637519
  · exact B637523
  · exact B637527
  · exact B637531
  · exact B637535
  · exact B637539
  · exact B637543
  · exact B637547
  · exact B637551
  · exact B637555
  · exact B637559
  · exact B637563
  · exact B637567
  · exact B637571
  · exact B637575
  · exact B637579
  · exact B637583
  · exact B637587
  · exact B637591
  · exact B637595
  · exact B637599
  · exact B637603
  · exact B637607
  · exact B637611
  · exact B637615
  · exact B637619
  · exact B637623
  · exact B637627
  · exact B637631
  · exact B637635
  · exact B637639
  · exact B637643
  · exact B637647
  · exact B637651
  · exact B637655
  · exact B637659
  · exact B637663
  · exact B637667
  · exact B637671
  · exact B637675
  · exact B637679
  · exact B637683
  · exact B637687
  · exact B637691
  · exact B637695
  · exact B637699
  · exact B637703
  · exact B637707
  · exact B637711
  · exact B637715
  · exact B637719
  · exact B637723
  · exact B637727
  · exact B637731
  · exact B637735
  · exact B637739
  · exact B637743
  · exact B637747
  · exact B637751
  · exact B637755
  · exact B637759
  · exact B637763
  · exact B637767
  · exact B637771
  · exact B637775
  · exact B637779
  · exact B637783
  · exact B637787
  · exact B637791
  · exact B637795
  · exact B637799
  · exact B637803
  · exact B637807
  · exact B637811
  · exact B637815
  · exact B637819
  · exact B637823
  · exact B637827
  · exact B637831
  · exact B637835
  · exact B637839
  · exact B637843
  · exact B637847
  · exact B637851
  · exact B637855
  · exact B637859
  · exact B637863
  · exact B637867
  · exact B637871
  · exact B637875
  · exact B637879
  · exact B637883
  · exact B637887
  · exact B637891
  · exact B637895
  · exact B637899
  · exact B637903
  · exact B637907
  · exact B637911
  · exact B637915
  · exact B637919
  · exact B637923
  · exact B637927
  · exact B637931
  · exact B637935
  · exact B637939
  · exact B637943
  · exact B637947
  · exact B637951
  · exact B637955
  · exact B637959
  · exact B637963
  · exact B637967
  · exact B637971
  · exact B637975
  · exact B637979
  · exact B637983
  · exact B637987
  · exact B637991
  · exact B637995
  · exact B637999
  · exact B638003
  · exact B638007
  · exact B638011
  · exact B638015
  · exact B638019
  · exact B638023
  · exact B638027
  · exact B638031
  · exact B638035
  · exact B638039
  · exact B638043
  · exact B638047
  · exact B638051
  · exact B638055
  · exact B638059
  · exact B638063
  · exact B638067
  · exact B638071
  · exact B638075
  · exact B638079
  · exact B638083
  · exact B638087
  · exact B638091
  · exact B638095
  · exact B638099
  · exact B638103
  · exact B638107
  · exact B638111
  · exact B638115
  · exact B638119
  · exact B638123
  · exact B638127
  · exact B638131
  · exact B638135
  · exact B638139
  · exact B638143
  · exact B638147
  · exact B638151
  · exact B638155
  · exact B638159
  · exact B638163
  · exact B638167
  · exact B638171
  · exact B638175
  · exact B638179
  · exact B638183
  · exact B638187
  · exact B638191
  · exact B638195
  · exact B638199
  · exact B638203
  · exact B638207
  · exact B638211
  · exact B638215
  · exact B638219
  · exact B638223
  · exact B638227
  · exact B638231
  · exact B638235
  · exact B638239
  · exact B638243
  · exact B638247
  · exact B638251
  · exact B638255
  · exact B638259
  · exact B638263
  · exact B638267
  · exact B638271
  · exact B638275
  · exact B638279
  · exact B638283
  · exact B638287
  · exact B638291
  · exact B638295
  · exact B638299

theorem solution (m : ℕ) (hlo : 634301 ≤ m) (hhi : m ≤ 638301) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 158575 ≤ j := by omega
    have hj2 : j ≤ 159574 := by omega
    have hb : Blo 634301 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 159275 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
