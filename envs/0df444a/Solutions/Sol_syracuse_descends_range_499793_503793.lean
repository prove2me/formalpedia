-- Prove2me | solution 1 for syracuse_descends_range_499793_503793
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:48:14.479221+00:00
-- url     : https://prove2.me/submissions/616032ad-0fed-40ab-85ca-ebd3759cdb50

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


theorem B753677 : Blo 499793 753677 := bbase (se 3 (by rfl) ⟨141314, by rfl⟩ : syracuseStep 753677 = 282629) (by norm_num)
theorem B1605653 : Blo 499793 1605653 := bbase (se 6 (by rfl) ⟨37632, by rfl⟩ : syracuseStep 1605653 = 75265) (by norm_num)
theorem B753701 : Blo 499793 753701 := bbase (se 4 (by rfl) ⟨70659, by rfl⟩ : syracuseStep 753701 = 141319) (by norm_num)
theorem B753725 : Blo 499793 753725 := bbase (se 3 (by rfl) ⟨141323, by rfl⟩ : syracuseStep 753725 = 282647) (by norm_num)
theorem B753749 : Blo 499793 753749 := bbase (se 8 (by rfl) ⟨4416, by rfl⟩ : syracuseStep 753749 = 8833) (by norm_num)
theorem B753773 : Blo 499793 753773 := bbase (se 3 (by rfl) ⟨141332, by rfl⟩ : syracuseStep 753773 = 282665) (by norm_num)
theorem B753797 : Blo 499793 753797 := bbase (se 4 (by rfl) ⟨70668, by rfl⟩ : syracuseStep 753797 = 141337) (by norm_num)
theorem B753821 : Blo 499793 753821 := bbase (se 3 (by rfl) ⟨141341, by rfl⟩ : syracuseStep 753821 = 282683) (by norm_num)
theorem B753845 : Blo 499793 753845 := bbase (se 5 (by rfl) ⟨35336, by rfl⟩ : syracuseStep 753845 = 70673) (by norm_num)
theorem B753869 : Blo 499793 753869 := bbase (se 3 (by rfl) ⟨141350, by rfl⟩ : syracuseStep 753869 = 282701) (by norm_num)
theorem B1147085 : Blo 499793 1147085 := bbase (se 3 (by rfl) ⟨215078, by rfl⟩ : syracuseStep 1147085 = 430157) (by norm_num)
theorem B753893 : Blo 499793 753893 := bbase (se 4 (by rfl) ⟨70677, by rfl⟩ : syracuseStep 753893 = 141355) (by norm_num)
theorem B950525 : Blo 499793 950525 := bbase (se 3 (by rfl) ⟨178223, by rfl⟩ : syracuseStep 950525 = 356447) (by norm_num)
theorem B753917 : Blo 499793 753917 := bbase (se 3 (by rfl) ⟨141359, by rfl⟩ : syracuseStep 753917 = 282719) (by norm_num)
theorem B753941 : Blo 499793 753941 := bbase (se 6 (by rfl) ⟨17670, by rfl⟩ : syracuseStep 753941 = 35341) (by norm_num)
theorem B753965 : Blo 499793 753965 := bbase (se 3 (by rfl) ⟨141368, by rfl⟩ : syracuseStep 753965 = 282737) (by norm_num)
theorem B1900853 : Blo 499793 1900853 := bbase (se 5 (by rfl) ⟨89102, by rfl⟩ : syracuseStep 1900853 = 178205) (by norm_num)
theorem B753989 : Blo 499793 753989 := bbase (se 4 (by rfl) ⟨70686, by rfl⟩ : syracuseStep 753989 = 141373) (by norm_num)
theorem B754013 : Blo 499793 754013 := bbase (se 3 (by rfl) ⟨141377, by rfl⟩ : syracuseStep 754013 = 282755) (by norm_num)
theorem B754037 : Blo 499793 754037 := bbase (se 5 (by rfl) ⟨35345, by rfl⟩ : syracuseStep 754037 = 70691) (by norm_num)
theorem B754061 : Blo 499793 754061 := bbase (se 3 (by rfl) ⟨141386, by rfl⟩ : syracuseStep 754061 = 282773) (by norm_num)
theorem B4882837 : Blo 499793 4882837 := bbase (se 6 (by rfl) ⟨114441, by rfl⟩ : syracuseStep 4882837 = 228883) (by norm_num)
theorem B754085 : Blo 499793 754085 := bbase (se 4 (by rfl) ⟨70695, by rfl⟩ : syracuseStep 754085 = 141391) (by norm_num)
theorem B754109 : Blo 499793 754109 := bbase (se 3 (by rfl) ⟨141395, by rfl⟩ : syracuseStep 754109 = 282791) (by norm_num)
theorem B754133 : Blo 499793 754133 := bbase (se 7 (by rfl) ⟨8837, by rfl⟩ : syracuseStep 754133 = 17675) (by norm_num)
theorem B557533 : Blo 499793 557533 := bbase (se 3 (by rfl) ⟨104537, by rfl⟩ : syracuseStep 557533 = 209075) (by norm_num)
theorem B754157 : Blo 499793 754157 := bbase (se 3 (by rfl) ⟨141404, by rfl⟩ : syracuseStep 754157 = 282809) (by norm_num)
theorem B754181 : Blo 499793 754181 := bbase (se 4 (by rfl) ⟨70704, by rfl⟩ : syracuseStep 754181 = 141409) (by norm_num)
theorem B754205 : Blo 499793 754205 := bbase (se 3 (by rfl) ⟨141413, by rfl⟩ : syracuseStep 754205 = 282827) (by norm_num)
theorem B1147429 : Blo 499793 1147429 := bbase (se 4 (by rfl) ⟨107571, by rfl⟩ : syracuseStep 1147429 = 215143) (by norm_num)
theorem B754229 : Blo 499793 754229 := bbase (se 5 (by rfl) ⟨35354, by rfl⟩ : syracuseStep 754229 = 70709) (by norm_num)
theorem B754253 : Blo 499793 754253 := bbase (se 3 (by rfl) ⟨141422, by rfl⟩ : syracuseStep 754253 = 282845) (by norm_num)
theorem B1901141 : Blo 499793 1901141 := bbase (se 8 (by rfl) ⟨11139, by rfl⟩ : syracuseStep 1901141 = 22279) (by norm_num)
theorem B754277 : Blo 499793 754277 := bbase (se 4 (by rfl) ⟨70713, by rfl⟩ : syracuseStep 754277 = 141427) (by norm_num)
theorem B754301 : Blo 499793 754301 := bbase (se 3 (by rfl) ⟨141431, by rfl⟩ : syracuseStep 754301 = 282863) (by norm_num)
theorem B754325 : Blo 499793 754325 := bbase (se 6 (by rfl) ⟨17679, by rfl⟩ : syracuseStep 754325 = 35359) (by norm_num)
theorem B754349 : Blo 499793 754349 := bbase (se 3 (by rfl) ⟨141440, by rfl⟩ : syracuseStep 754349 = 282881) (by norm_num)
theorem B754373 : Blo 499793 754373 := bbase (se 4 (by rfl) ⟨70722, by rfl⟩ : syracuseStep 754373 = 141445) (by norm_num)
theorem B754397 : Blo 499793 754397 := bbase (se 3 (by rfl) ⟨141449, by rfl⟩ : syracuseStep 754397 = 282899) (by norm_num)
theorem B754421 : Blo 499793 754421 := bbase (se 5 (by rfl) ⟨35363, by rfl⟩ : syracuseStep 754421 = 70727) (by norm_num)
theorem B754445 : Blo 499793 754445 := bbase (se 3 (by rfl) ⟨141458, by rfl⟩ : syracuseStep 754445 = 282917) (by norm_num)
theorem B1016597 : Blo 499793 1016597 := bbase (se 6 (by rfl) ⟨23826, by rfl⟩ : syracuseStep 1016597 = 47653) (by norm_num)
theorem B754469 : Blo 499793 754469 := bbase (se 4 (by rfl) ⟨70731, by rfl⟩ : syracuseStep 754469 = 141463) (by norm_num)
theorem B754493 : Blo 499793 754493 := bbase (se 3 (by rfl) ⟨141467, by rfl⟩ : syracuseStep 754493 = 282935) (by norm_num)
theorem B754517 : Blo 499793 754517 := bbase (se 9 (by rfl) ⟨2210, by rfl⟩ : syracuseStep 754517 = 4421) (by norm_num)
theorem B754541 : Blo 499793 754541 := bbase (se 3 (by rfl) ⟨141476, by rfl⟩ : syracuseStep 754541 = 282953) (by norm_num)
theorem B1016693 : Blo 499793 1016693 := bbase (se 5 (by rfl) ⟨47657, by rfl⟩ : syracuseStep 1016693 = 95315) (by norm_num)
theorem B754565 : Blo 499793 754565 := bbase (se 4 (by rfl) ⟨70740, by rfl⟩ : syracuseStep 754565 = 141481) (by norm_num)
theorem B1606549 : Blo 499793 1606549 := bbase (se 6 (by rfl) ⟨37653, by rfl⟩ : syracuseStep 1606549 = 75307) (by norm_num)
theorem B754589 : Blo 499793 754589 := bbase (se 3 (by rfl) ⟨141485, by rfl⟩ : syracuseStep 754589 = 282971) (by norm_num)
theorem B754613 : Blo 499793 754613 := bbase (se 5 (by rfl) ⟨35372, by rfl⟩ : syracuseStep 754613 = 70745) (by norm_num)
theorem B754637 : Blo 499793 754637 := bbase (se 3 (by rfl) ⟨141494, by rfl⟩ : syracuseStep 754637 = 282989) (by norm_num)
theorem B754661 : Blo 499793 754661 := bbase (se 4 (by rfl) ⟨70749, by rfl⟩ : syracuseStep 754661 = 141499) (by norm_num)
theorem B951277 : Blo 499793 951277 := bbase (se 3 (by rfl) ⟨178364, by rfl⟩ : syracuseStep 951277 = 356729) (by norm_num)
theorem B754685 : Blo 499793 754685 := bbase (se 3 (by rfl) ⟨141503, by rfl⟩ : syracuseStep 754685 = 283007) (by norm_num)
theorem B754709 : Blo 499793 754709 := bbase (se 6 (by rfl) ⟨17688, by rfl⟩ : syracuseStep 754709 = 35377) (by norm_num)
theorem B754733 : Blo 499793 754733 := bbase (se 3 (by rfl) ⟨141512, by rfl⟩ : syracuseStep 754733 = 283025) (by norm_num)
theorem B754757 : Blo 499793 754757 := bbase (se 4 (by rfl) ⟨70758, by rfl⟩ : syracuseStep 754757 = 141517) (by norm_num)
theorem B5407829 : Blo 499793 5407829 := bbase (se 8 (by rfl) ⟨31686, by rfl⟩ : syracuseStep 5407829 = 63373) (by norm_num)
theorem B754781 : Blo 499793 754781 := bbase (se 3 (by rfl) ⟨141521, by rfl⟩ : syracuseStep 754781 = 283043) (by norm_num)
theorem B754805 : Blo 499793 754805 := bbase (se 5 (by rfl) ⟨35381, by rfl⟩ : syracuseStep 754805 = 70763) (by norm_num)
theorem B951421 : Blo 499793 951421 := bbase (se 3 (by rfl) ⟨178391, by rfl⟩ : syracuseStep 951421 = 356783) (by norm_num)
theorem B754829 : Blo 499793 754829 := bbase (se 3 (by rfl) ⟨141530, by rfl⟩ : syracuseStep 754829 = 283061) (by norm_num)
theorem B754853 : Blo 499793 754853 := bbase (se 4 (by rfl) ⟨70767, by rfl⟩ : syracuseStep 754853 = 141535) (by norm_num)
theorem B754877 : Blo 499793 754877 := bbase (se 3 (by rfl) ⟨141539, by rfl⟩ : syracuseStep 754877 = 283079) (by norm_num)
theorem B754901 : Blo 499793 754901 := bbase (se 7 (by rfl) ⟨8846, by rfl⟩ : syracuseStep 754901 = 17693) (by norm_num)
theorem B754925 : Blo 499793 754925 := bbase (se 3 (by rfl) ⟨141548, by rfl⟩ : syracuseStep 754925 = 283097) (by norm_num)
theorem B754949 : Blo 499793 754949 := bbase (se 4 (by rfl) ⟨70776, by rfl⟩ : syracuseStep 754949 = 141553) (by norm_num)
theorem B951581 : Blo 499793 951581 := bbase (se 3 (by rfl) ⟨178421, by rfl⟩ : syracuseStep 951581 = 356843) (by norm_num)
theorem B754973 : Blo 499793 754973 := bbase (se 3 (by rfl) ⟨141557, by rfl⟩ : syracuseStep 754973 = 283115) (by norm_num)
theorem B918821 : Blo 499793 918821 := bbase (se 4 (by rfl) ⟨86139, by rfl⟩ : syracuseStep 918821 = 172279) (by norm_num)
theorem B754997 : Blo 499793 754997 := bbase (se 5 (by rfl) ⟨35390, by rfl⟩ : syracuseStep 754997 = 70781) (by norm_num)
theorem B755021 : Blo 499793 755021 := bbase (se 3 (by rfl) ⟨141566, by rfl⟩ : syracuseStep 755021 = 283133) (by norm_num)
theorem B755045 : Blo 499793 755045 := bbase (se 4 (by rfl) ⟨70785, by rfl⟩ : syracuseStep 755045 = 141571) (by norm_num)
theorem B755069 : Blo 499793 755069 := bbase (se 3 (by rfl) ⟨141575, by rfl⟩ : syracuseStep 755069 = 283151) (by norm_num)
theorem B755093 : Blo 499793 755093 := bbase (se 6 (by rfl) ⟨17697, by rfl⟩ : syracuseStep 755093 = 35395) (by norm_num)
theorem B951725 : Blo 499793 951725 := bbase (se 3 (by rfl) ⟨178448, by rfl⟩ : syracuseStep 951725 = 356897) (by norm_num)
theorem B755117 : Blo 499793 755117 := bbase (se 3 (by rfl) ⟨141584, by rfl⟩ : syracuseStep 755117 = 283169) (by norm_num)
theorem B755141 : Blo 499793 755141 := bbase (se 4 (by rfl) ⟨70794, by rfl⟩ : syracuseStep 755141 = 141589) (by norm_num)
theorem B755165 : Blo 499793 755165 := bbase (se 3 (by rfl) ⟨141593, by rfl⟩ : syracuseStep 755165 = 283187) (by norm_num)
theorem B755189 : Blo 499793 755189 := bbase (se 5 (by rfl) ⟨35399, by rfl⟩ : syracuseStep 755189 = 70799) (by norm_num)
theorem B755213 : Blo 499793 755213 := bbase (se 3 (by rfl) ⟨141602, by rfl⟩ : syracuseStep 755213 = 283205) (by norm_num)
theorem B755237 : Blo 499793 755237 := bbase (se 4 (by rfl) ⟨70803, by rfl⟩ : syracuseStep 755237 = 141607) (by norm_num)
theorem B755261 : Blo 499793 755261 := bbase (se 3 (by rfl) ⟨141611, by rfl⟩ : syracuseStep 755261 = 283223) (by norm_num)
theorem B755285 : Blo 499793 755285 := bbase (se 8 (by rfl) ⟨4425, by rfl⟩ : syracuseStep 755285 = 8851) (by norm_num)
theorem B755309 : Blo 499793 755309 := bbase (se 3 (by rfl) ⟨141620, by rfl⟩ : syracuseStep 755309 = 283241) (by norm_num)
theorem B755333 : Blo 499793 755333 := bbase (se 4 (by rfl) ⟨70812, by rfl⟩ : syracuseStep 755333 = 141625) (by norm_num)
theorem B755357 : Blo 499793 755357 := bbase (se 3 (by rfl) ⟨141629, by rfl⟩ : syracuseStep 755357 = 283259) (by norm_num)
theorem B755381 : Blo 499793 755381 := bbase (se 5 (by rfl) ⟨35408, by rfl⟩ : syracuseStep 755381 = 70817) (by norm_num)
theorem B952013 : Blo 499793 952013 := bbase (se 3 (by rfl) ⟨178502, by rfl⟩ : syracuseStep 952013 = 357005) (by norm_num)
theorem B755405 : Blo 499793 755405 := bbase (se 3 (by rfl) ⟨141638, by rfl⟩ : syracuseStep 755405 = 283277) (by norm_num)
theorem B755429 : Blo 499793 755429 := bbase (se 4 (by rfl) ⟨70821, by rfl⟩ : syracuseStep 755429 = 141643) (by norm_num)
theorem B1902325 : Blo 499793 1902325 := bbase (se 5 (by rfl) ⟨89171, by rfl⟩ : syracuseStep 1902325 = 178343) (by norm_num)
theorem B755453 : Blo 499793 755453 := bbase (se 3 (by rfl) ⟨141647, by rfl⟩ : syracuseStep 755453 = 283295) (by norm_num)
theorem B755477 : Blo 499793 755477 := bbase (se 6 (by rfl) ⟨17706, by rfl⟩ : syracuseStep 755477 = 35413) (by norm_num)
theorem B755501 : Blo 499793 755501 := bbase (se 3 (by rfl) ⟨141656, by rfl⟩ : syracuseStep 755501 = 283313) (by norm_num)
theorem B755525 : Blo 499793 755525 := bbase (se 4 (by rfl) ⟨70830, by rfl⟩ : syracuseStep 755525 = 141661) (by norm_num)
theorem B755549 : Blo 499793 755549 := bbase (se 3 (by rfl) ⟨141665, by rfl⟩ : syracuseStep 755549 = 283331) (by norm_num)
theorem B952165 : Blo 499793 952165 := bbase (se 4 (by rfl) ⟨89265, by rfl⟩ : syracuseStep 952165 = 178531) (by norm_num)
theorem B755573 : Blo 499793 755573 := bbase (se 5 (by rfl) ⟨35417, by rfl⟩ : syracuseStep 755573 = 70835) (by norm_num)
theorem B755597 : Blo 499793 755597 := bbase (se 3 (by rfl) ⟨141674, by rfl⟩ : syracuseStep 755597 = 283349) (by norm_num)
theorem B755621 : Blo 499793 755621 := bbase (se 4 (by rfl) ⟨70839, by rfl⟩ : syracuseStep 755621 = 141679) (by norm_num)
theorem B755645 : Blo 499793 755645 := bbase (se 3 (by rfl) ⟨141683, by rfl⟩ : syracuseStep 755645 = 283367) (by norm_num)
theorem B755669 : Blo 499793 755669 := bbase (se 7 (by rfl) ⟨8855, by rfl⟩ : syracuseStep 755669 = 17711) (by norm_num)
theorem B1902629 : Blo 499793 1902629 := bbase (se 4 (by rfl) ⟨178371, by rfl⟩ : syracuseStep 1902629 = 356743) (by norm_num)
theorem B952469 : Blo 499793 952469 := bbase (se 6 (by rfl) ⟨22323, by rfl⟩ : syracuseStep 952469 = 44647) (by norm_num)
theorem B919757 : Blo 499793 919757 := bbase (se 3 (by rfl) ⟨172454, by rfl⟩ : syracuseStep 919757 = 344909) (by norm_num)
theorem B10455317 : Blo 499793 10455317 := bbase (se 6 (by rfl) ⟨245046, by rfl⟩ : syracuseStep 10455317 = 490093) (by norm_num)
theorem B1804949 : Blo 499793 1804949 := bbase (se 6 (by rfl) ⟨42303, by rfl⟩ : syracuseStep 1804949 = 84607) (by norm_num)
theorem B1378997 : Blo 499793 1378997 := bbase (se 5 (by rfl) ⟨64640, by rfl⟩ : syracuseStep 1378997 = 129281) (by norm_num)
theorem B1543013 : Blo 499793 1543013 := bbase (se 4 (by rfl) ⟨144657, by rfl⟩ : syracuseStep 1543013 = 289315) (by norm_num)
theorem B953221 : Blo 499793 953221 := bbase (se 4 (by rfl) ⟨89364, by rfl⟩ : syracuseStep 953221 = 178729) (by norm_num)
theorem B953365 : Blo 499793 953365 := bbase (se 6 (by rfl) ⟨22344, by rfl⟩ : syracuseStep 953365 = 44689) (by norm_num)
theorem B953525 : Blo 499793 953525 := bbase (se 5 (by rfl) ⟨44696, by rfl⟩ : syracuseStep 953525 = 89393) (by norm_num)
theorem B855317 : Blo 499793 855317 := bbase (se 6 (by rfl) ⟨20046, by rfl⟩ : syracuseStep 855317 = 40093) (by norm_num)
theorem B953669 : Blo 499793 953669 := bbase (se 4 (by rfl) ⟨89406, by rfl⟩ : syracuseStep 953669 = 178813) (by norm_num)
theorem B953957 : Blo 499793 953957 := bbase (se 4 (by rfl) ⟨89433, by rfl⟩ : syracuseStep 953957 = 178867) (by norm_num)
theorem B2035397 : Blo 499793 2035397 := bbase (se 4 (by rfl) ⟨190818, by rfl⟩ : syracuseStep 2035397 = 381637) (by norm_num)
theorem B1609445 : Blo 499793 1609445 := bbase (se 4 (by rfl) ⟨150885, by rfl⟩ : syracuseStep 1609445 = 301771) (by norm_num)
theorem B954109 : Blo 499793 954109 := bbase (se 3 (by rfl) ⟨178895, by rfl⟩ : syracuseStep 954109 = 357791) (by norm_num)
theorem B954413 : Blo 499793 954413 := bbase (se 3 (by rfl) ⟨178952, by rfl⟩ : syracuseStep 954413 = 357905) (by norm_num)
theorem B1904741 : Blo 499793 1904741 := bbase (se 4 (by rfl) ⟨178569, by rfl⟩ : syracuseStep 1904741 = 357139) (by norm_num)
theorem B7213205 : Blo 499793 7213205 := bbase (se 6 (by rfl) ⟨169059, by rfl⟩ : syracuseStep 7213205 = 338119) (by norm_num)
theorem B1905029 : Blo 499793 1905029 := bbase (se 4 (by rfl) ⟨178596, by rfl⟩ : syracuseStep 1905029 = 357193) (by norm_num)
theorem B1282565 : Blo 499793 1282565 := bbase (se 4 (by rfl) ⟨120240, by rfl⟩ : syracuseStep 1282565 = 240481) (by norm_num)
theorem B7246421 : Blo 499793 7246421 := bbase (se 8 (by rfl) ⟨42459, by rfl⟩ : syracuseStep 7246421 = 84919) (by norm_num)
theorem B955165 : Blo 499793 955165 := bbase (se 3 (by rfl) ⟨179093, by rfl⟩ : syracuseStep 955165 = 358187) (by norm_num)
theorem B627521 : Blo 499793 627521 := bbase (se 2 (by rfl) ⟨235320, by rfl⟩ : syracuseStep 627521 = 470641) (by norm_num)
theorem B1839941 : Blo 499793 1839941 := bbase (se 4 (by rfl) ⟨172494, by rfl⟩ : syracuseStep 1839941 = 344989) (by norm_num)
theorem B955309 : Blo 499793 955309 := bbase (se 3 (by rfl) ⟨179120, by rfl⟩ : syracuseStep 955309 = 358241) (by norm_num)
theorem B1807397 : Blo 499793 1807397 := bbase (se 4 (by rfl) ⟨169443, by rfl⟩ : syracuseStep 1807397 = 338887) (by norm_num)
theorem B955469 : Blo 499793 955469 := bbase (se 3 (by rfl) ⟨179150, by rfl⟩ : syracuseStep 955469 = 358301) (by norm_num)
theorem B562297 : Blo 499793 562297 := bbase (se 2 (by rfl) ⟨210861, by rfl⟩ : syracuseStep 562297 = 421723) (by norm_num)
theorem B562333 : Blo 499793 562333 := bbase (se 3 (by rfl) ⟨105437, by rfl⟩ : syracuseStep 562333 = 210875) (by norm_num)
theorem B562369 : Blo 499793 562369 := bbase (se 2 (by rfl) ⟨210888, by rfl⟩ : syracuseStep 562369 = 421777) (by norm_num)
theorem B955613 : Blo 499793 955613 := bbase (se 3 (by rfl) ⟨179177, by rfl⟩ : syracuseStep 955613 = 358355) (by norm_num)
theorem B562405 : Blo 499793 562405 := bbase (se 4 (by rfl) ⟨52725, by rfl⟩ : syracuseStep 562405 = 105451) (by norm_num)
theorem B562441 : Blo 499793 562441 := bbase (se 2 (by rfl) ⟨210915, by rfl⟩ : syracuseStep 562441 = 421831) (by norm_num)
theorem B562477 : Blo 499793 562477 := bbase (se 3 (by rfl) ⟨105464, by rfl⟩ : syracuseStep 562477 = 210929) (by norm_num)
theorem B562513 : Blo 499793 562513 := bbase (se 2 (by rfl) ⟨210942, by rfl⟩ : syracuseStep 562513 = 421885) (by norm_num)
theorem B562549 : Blo 499793 562549 := bbase (se 5 (by rfl) ⟨26369, by rfl⟩ : syracuseStep 562549 = 52739) (by norm_num)
theorem B562585 : Blo 499793 562585 := bbase (se 2 (by rfl) ⟨210969, by rfl⟩ : syracuseStep 562585 = 421939) (by norm_num)
theorem B562621 : Blo 499793 562621 := bbase (se 3 (by rfl) ⟨105491, by rfl⟩ : syracuseStep 562621 = 210983) (by norm_num)
theorem B857557 : Blo 499793 857557 := bbase (se 7 (by rfl) ⟨10049, by rfl⟩ : syracuseStep 857557 = 20099) (by norm_num)
theorem B562657 : Blo 499793 562657 := bbase (se 2 (by rfl) ⟨210996, by rfl⟩ : syracuseStep 562657 = 421993) (by norm_num)
theorem B955901 : Blo 499793 955901 := bbase (se 3 (by rfl) ⟨179231, by rfl⟩ : syracuseStep 955901 = 358463) (by norm_num)
theorem B1218053 : Blo 499793 1218053 := bbase (se 4 (by rfl) ⟨114192, by rfl⟩ : syracuseStep 1218053 = 228385) (by norm_num)
theorem B562693 : Blo 499793 562693 := bbase (se 4 (by rfl) ⟨52752, by rfl⟩ : syracuseStep 562693 = 105505) (by norm_num)
theorem B1906213 : Blo 499793 1906213 := bbase (se 4 (by rfl) ⟨178707, by rfl⟩ : syracuseStep 1906213 = 357415) (by norm_num)
theorem B562729 : Blo 499793 562729 := bbase (se 2 (by rfl) ⟨211023, by rfl⟩ : syracuseStep 562729 = 422047) (by norm_num)
theorem B562765 : Blo 499793 562765 := bbase (se 3 (by rfl) ⟨105518, by rfl⟩ : syracuseStep 562765 = 211037) (by norm_num)
theorem B562801 : Blo 499793 562801 := bbase (se 2 (by rfl) ⟨211050, by rfl⟩ : syracuseStep 562801 = 422101) (by norm_num)
theorem B3806837 : Blo 499793 3806837 := bbase (se 5 (by rfl) ⟨178445, by rfl⟩ : syracuseStep 3806837 = 356891) (by norm_num)
theorem B3053173 : Blo 499793 3053173 := bbase (se 5 (by rfl) ⟨143117, by rfl⟩ : syracuseStep 3053173 = 286235) (by norm_num)
theorem B562837 : Blo 499793 562837 := bbase (se 6 (by rfl) ⟨13191, by rfl⟩ : syracuseStep 562837 = 26383) (by norm_num)
theorem B956053 : Blo 499793 956053 := bbase (se 6 (by rfl) ⟨22407, by rfl⟩ : syracuseStep 956053 = 44815) (by norm_num)
theorem B562873 : Blo 499793 562873 := bbase (se 2 (by rfl) ⟨211077, by rfl⟩ : syracuseStep 562873 = 422155) (by norm_num)
theorem B562909 : Blo 499793 562909 := bbase (se 3 (by rfl) ⟨105545, by rfl⟩ : syracuseStep 562909 = 211091) (by norm_num)
theorem B1218293 : Blo 499793 1218293 := bbase (se 5 (by rfl) ⟨57107, by rfl⟩ : syracuseStep 1218293 = 114215) (by norm_num)
theorem B562945 : Blo 499793 562945 := bbase (se 2 (by rfl) ⟨211104, by rfl⟩ : syracuseStep 562945 = 422209) (by norm_num)
theorem B562981 : Blo 499793 562981 := bbase (se 4 (by rfl) ⟨52779, by rfl⟩ : syracuseStep 562981 = 105559) (by norm_num)
theorem B563017 : Blo 499793 563017 := bbase (se 2 (by rfl) ⟨211131, by rfl⟩ : syracuseStep 563017 = 422263) (by norm_num)
theorem B1906517 : Blo 499793 1906517 := bbase (se 9 (by rfl) ⟨5585, by rfl⟩ : syracuseStep 1906517 = 11171) (by norm_num)
theorem B563053 : Blo 499793 563053 := bbase (se 3 (by rfl) ⟨105572, by rfl⟩ : syracuseStep 563053 = 211145) (by norm_num)
theorem B563089 : Blo 499793 563089 := bbase (se 2 (by rfl) ⟨211158, by rfl⟩ : syracuseStep 563089 = 422317) (by norm_num)
theorem B2037653 : Blo 499793 2037653 := bbase (se 6 (by rfl) ⟨47757, by rfl⟩ : syracuseStep 2037653 = 95515) (by norm_num)
theorem B563125 : Blo 499793 563125 := bbase (se 5 (by rfl) ⟨26396, by rfl⟩ : syracuseStep 563125 = 52793) (by norm_num)
theorem B1611701 : Blo 499793 1611701 := bbase (se 5 (by rfl) ⟨75548, by rfl⟩ : syracuseStep 1611701 = 151097) (by norm_num)
theorem B956357 : Blo 499793 956357 := bbase (se 4 (by rfl) ⟨89658, by rfl⟩ : syracuseStep 956357 = 179317) (by norm_num)
theorem B563161 : Blo 499793 563161 := bbase (se 2 (by rfl) ⟨211185, by rfl⟩ : syracuseStep 563161 = 422371) (by norm_num)
theorem B563197 : Blo 499793 563197 := bbase (se 3 (by rfl) ⟨105599, by rfl⟩ : syracuseStep 563197 = 211199) (by norm_num)
theorem B563233 : Blo 499793 563233 := bbase (se 2 (by rfl) ⟨211212, by rfl⟩ : syracuseStep 563233 = 422425) (by norm_num)
theorem B1251389 : Blo 499793 1251389 := bbase (se 3 (by rfl) ⟨234635, by rfl⟩ : syracuseStep 1251389 = 469271) (by norm_num)
theorem B563269 : Blo 499793 563269 := bbase (se 4 (by rfl) ⟨52806, by rfl⟩ : syracuseStep 563269 = 105613) (by norm_num)
theorem B563305 : Blo 499793 563305 := bbase (se 2 (by rfl) ⟨211239, by rfl⟩ : syracuseStep 563305 = 422479) (by norm_num)
theorem B563341 : Blo 499793 563341 := bbase (se 3 (by rfl) ⟨105626, by rfl⟩ : syracuseStep 563341 = 211253) (by norm_num)
theorem B858269 : Blo 499793 858269 := bbase (se 3 (by rfl) ⟨160925, by rfl⟩ : syracuseStep 858269 = 321851) (by norm_num)
theorem B563377 : Blo 499793 563377 := bbase (se 2 (by rfl) ⟨211266, by rfl⟩ : syracuseStep 563377 = 422533) (by norm_num)
theorem B563413 : Blo 499793 563413 := bbase (se 7 (by rfl) ⟨6602, by rfl⟩ : syracuseStep 563413 = 13205) (by norm_num)
theorem B563449 : Blo 499793 563449 := bbase (se 2 (by rfl) ⟨211293, by rfl⟩ : syracuseStep 563449 = 422587) (by norm_num)
theorem B563485 : Blo 499793 563485 := bbase (se 3 (by rfl) ⟨105653, by rfl⟩ : syracuseStep 563485 = 211307) (by norm_num)
theorem B563521 : Blo 499793 563521 := bbase (se 2 (by rfl) ⟨211320, by rfl⟩ : syracuseStep 563521 = 422641) (by norm_num)
theorem B8690005 : Blo 499793 8690005 := bbase (se 10 (by rfl) ⟨12729, by rfl⟩ : syracuseStep 8690005 = 25459) (by norm_num)
theorem B563557 : Blo 499793 563557 := bbase (se 4 (by rfl) ⟨52833, by rfl⟩ : syracuseStep 563557 = 105667) (by norm_num)
theorem B563593 : Blo 499793 563593 := bbase (se 2 (by rfl) ⟨211347, by rfl⟩ : syracuseStep 563593 = 422695) (by norm_num)
theorem B563629 : Blo 499793 563629 := bbase (se 3 (by rfl) ⟨105680, by rfl⟩ : syracuseStep 563629 = 211361) (by norm_num)
theorem B563665 : Blo 499793 563665 := bbase (se 2 (by rfl) ⟨211374, by rfl⟩ : syracuseStep 563665 = 422749) (by norm_num)
theorem B2169301 : Blo 499793 2169301 := bbase (se 7 (by rfl) ⟨25421, by rfl⟩ : syracuseStep 2169301 = 50843) (by norm_num)
theorem B563701 : Blo 499793 563701 := bbase (se 5 (by rfl) ⟨26423, by rfl⟩ : syracuseStep 563701 = 52847) (by norm_num)
theorem B563737 : Blo 499793 563737 := bbase (se 2 (by rfl) ⟨211401, by rfl⟩ : syracuseStep 563737 = 422803) (by norm_num)
theorem B563773 : Blo 499793 563773 := bbase (se 3 (by rfl) ⟨105707, by rfl⟩ : syracuseStep 563773 = 211415) (by norm_num)
theorem B563809 : Blo 499793 563809 := bbase (se 2 (by rfl) ⟨211428, by rfl⟩ : syracuseStep 563809 = 422857) (by norm_num)
theorem B2857589 : Blo 499793 2857589 := bbase (se 5 (by rfl) ⟨133949, by rfl⟩ : syracuseStep 2857589 = 267899) (by norm_num)
theorem B563845 : Blo 499793 563845 := bbase (se 4 (by rfl) ⟨52860, by rfl⟩ : syracuseStep 563845 = 105721) (by norm_num)
theorem B3218069 : Blo 499793 3218069 := bbase (se 6 (by rfl) ⟨75423, by rfl⟩ : syracuseStep 3218069 = 150847) (by norm_num)
theorem B563881 : Blo 499793 563881 := bbase (se 2 (by rfl) ⟨211455, by rfl⟩ : syracuseStep 563881 = 422911) (by norm_num)
theorem B1612469 : Blo 499793 1612469 := bbase (se 5 (by rfl) ⟨75584, by rfl⟩ : syracuseStep 1612469 = 151169) (by norm_num)
theorem B563917 : Blo 499793 563917 := bbase (se 3 (by rfl) ⟨105734, by rfl⟩ : syracuseStep 563917 = 211469) (by norm_num)
theorem B563953 : Blo 499793 563953 := bbase (se 2 (by rfl) ⟨211482, by rfl⟩ : syracuseStep 563953 = 422965) (by norm_num)
theorem B563989 : Blo 499793 563989 := bbase (se 6 (by rfl) ⟨13218, by rfl⟩ : syracuseStep 563989 = 26437) (by norm_num)
theorem B564025 : Blo 499793 564025 := bbase (se 2 (by rfl) ⟨211509, by rfl⟩ : syracuseStep 564025 = 423019) (by norm_num)
theorem B564061 : Blo 499793 564061 := bbase (se 3 (by rfl) ⟨105761, by rfl⟩ : syracuseStep 564061 = 211523) (by norm_num)
theorem B564097 : Blo 499793 564097 := bbase (se 2 (by rfl) ⟨211536, by rfl⟩ : syracuseStep 564097 = 423073) (by norm_num)
theorem B564133 : Blo 499793 564133 := bbase (se 4 (by rfl) ⟨52887, by rfl⟩ : syracuseStep 564133 = 105775) (by norm_num)
theorem B564169 : Blo 499793 564169 := bbase (se 2 (by rfl) ⟨211563, by rfl⟩ : syracuseStep 564169 = 423127) (by norm_num)
theorem B2530277 : Blo 499793 2530277 := bbase (se 4 (by rfl) ⟨237213, by rfl⟩ : syracuseStep 2530277 = 474427) (by norm_num)
theorem B564205 : Blo 499793 564205 := bbase (se 3 (by rfl) ⟨105788, by rfl⟩ : syracuseStep 564205 = 211577) (by norm_num)
theorem B564241 : Blo 499793 564241 := bbase (se 2 (by rfl) ⟨211590, by rfl⟩ : syracuseStep 564241 = 423181) (by norm_num)
theorem B564277 : Blo 499793 564277 := bbase (se 5 (by rfl) ⟨26450, by rfl⟩ : syracuseStep 564277 = 52901) (by norm_num)
theorem B564313 : Blo 499793 564313 := bbase (se 2 (by rfl) ⟨211617, by rfl⟩ : syracuseStep 564313 = 423235) (by norm_num)
theorem B564349 : Blo 499793 564349 := bbase (se 3 (by rfl) ⟨105815, by rfl⟩ : syracuseStep 564349 = 211631) (by norm_num)
theorem B564385 : Blo 499793 564385 := bbase (se 2 (by rfl) ⟨211644, by rfl⟩ : syracuseStep 564385 = 423289) (by norm_num)
theorem B1612981 : Blo 499793 1612981 := bbase (se 5 (by rfl) ⟨75608, by rfl⟩ : syracuseStep 1612981 = 151217) (by norm_num)
theorem B564421 : Blo 499793 564421 := bbase (se 4 (by rfl) ⟨52914, by rfl⟩ : syracuseStep 564421 = 105829) (by norm_num)
theorem B564457 : Blo 499793 564457 := bbase (se 2 (by rfl) ⟨211671, by rfl⟩ : syracuseStep 564457 = 423343) (by norm_num)
theorem B1219853 : Blo 499793 1219853 := bbase (se 3 (by rfl) ⟨228722, by rfl⟩ : syracuseStep 1219853 = 457445) (by norm_num)
theorem B564493 : Blo 499793 564493 := bbase (se 3 (by rfl) ⟨105842, by rfl⟩ : syracuseStep 564493 = 211685) (by norm_num)
theorem B564529 : Blo 499793 564529 := bbase (se 2 (by rfl) ⟨211698, by rfl⟩ : syracuseStep 564529 = 423397) (by norm_num)
theorem B564565 : Blo 499793 564565 := bbase (se 11 (by rfl) ⟨413, by rfl⟩ : syracuseStep 564565 = 827) (by norm_num)
theorem B564601 : Blo 499793 564601 := bbase (se 2 (by rfl) ⟨211725, by rfl⟩ : syracuseStep 564601 = 423451) (by norm_num)
theorem B564637 : Blo 499793 564637 := bbase (se 3 (by rfl) ⟨105869, by rfl⟩ : syracuseStep 564637 = 211739) (by norm_num)
theorem B1351093 : Blo 499793 1351093 := bbase (se 5 (by rfl) ⟨63332, by rfl⟩ : syracuseStep 1351093 = 126665) (by norm_num)
theorem B564673 : Blo 499793 564673 := bbase (se 2 (by rfl) ⟨211752, by rfl⟩ : syracuseStep 564673 = 423505) (by norm_num)
theorem B564709 : Blo 499793 564709 := bbase (se 4 (by rfl) ⟨52941, by rfl⟩ : syracuseStep 564709 = 105883) (by norm_num)
theorem B2137589 : Blo 499793 2137589 := bbase (se 5 (by rfl) ⟨100199, by rfl⟩ : syracuseStep 2137589 = 200399) (by norm_num)
theorem B564745 : Blo 499793 564745 := bbase (se 2 (by rfl) ⟨211779, by rfl⟩ : syracuseStep 564745 = 423559) (by norm_num)
theorem B564781 : Blo 499793 564781 := bbase (se 3 (by rfl) ⟨105896, by rfl⟩ : syracuseStep 564781 = 211793) (by norm_num)
theorem B1089085 : Blo 499793 1089085 := bbase (se 3 (by rfl) ⟨204203, by rfl⟩ : syracuseStep 1089085 = 408407) (by norm_num)
theorem B564817 : Blo 499793 564817 := bbase (se 2 (by rfl) ⟨211806, by rfl⟩ : syracuseStep 564817 = 423613) (by norm_num)
theorem B564853 : Blo 499793 564853 := bbase (se 5 (by rfl) ⟨26477, by rfl⟩ : syracuseStep 564853 = 52955) (by norm_num)
theorem B564889 : Blo 499793 564889 := bbase (se 2 (by rfl) ⟨211833, by rfl⟩ : syracuseStep 564889 = 423667) (by norm_num)
theorem B564925 : Blo 499793 564925 := bbase (se 3 (by rfl) ⟨105923, by rfl⟩ : syracuseStep 564925 = 211847) (by norm_num)
theorem B564961 : Blo 499793 564961 := bbase (se 2 (by rfl) ⟨211860, by rfl⟩ : syracuseStep 564961 = 423721) (by norm_num)
theorem B564997 : Blo 499793 564997 := bbase (se 4 (by rfl) ⟨52968, by rfl⟩ : syracuseStep 564997 = 105937) (by norm_num)
theorem B2858773 : Blo 499793 2858773 := bbase (se 6 (by rfl) ⟨67002, by rfl⟩ : syracuseStep 2858773 = 134005) (by norm_num)
theorem B565033 : Blo 499793 565033 := bbase (se 2 (by rfl) ⟨211887, by rfl⟩ : syracuseStep 565033 = 423775) (by norm_num)
theorem B565069 : Blo 499793 565069 := bbase (se 3 (by rfl) ⟨105950, by rfl⟩ : syracuseStep 565069 = 211901) (by norm_num)
theorem B565105 : Blo 499793 565105 := bbase (se 2 (by rfl) ⟨211914, by rfl⟩ : syracuseStep 565105 = 423829) (by norm_num)
theorem B761717 : Blo 499793 761717 := bbase (se 5 (by rfl) ⟨35705, by rfl⟩ : syracuseStep 761717 = 71411) (by norm_num)
theorem B565141 : Blo 499793 565141 := bbase (se 6 (by rfl) ⟨13245, by rfl⟩ : syracuseStep 565141 = 26491) (by norm_num)
theorem B1908629 : Blo 499793 1908629 := bbase (se 6 (by rfl) ⟨44733, by rfl⟩ : syracuseStep 1908629 = 89467) (by norm_num)
theorem B565177 : Blo 499793 565177 := bbase (se 2 (by rfl) ⟨211941, by rfl⟩ : syracuseStep 565177 = 423883) (by norm_num)
theorem B565213 : Blo 499793 565213 := bbase (se 3 (by rfl) ⟨105977, by rfl⟩ : syracuseStep 565213 = 211955) (by norm_num)
theorem B565249 : Blo 499793 565249 := bbase (se 2 (by rfl) ⟨211968, by rfl⟩ : syracuseStep 565249 = 423937) (by norm_num)
theorem B565285 : Blo 499793 565285 := bbase (se 4 (by rfl) ⟨52995, by rfl⟩ : syracuseStep 565285 = 105991) (by norm_num)
theorem B565321 : Blo 499793 565321 := bbase (se 2 (by rfl) ⟨211995, by rfl⟩ : syracuseStep 565321 = 423991) (by norm_num)
theorem B565357 : Blo 499793 565357 := bbase (se 3 (by rfl) ⟨106004, by rfl⟩ : syracuseStep 565357 = 212009) (by norm_num)
theorem B565393 : Blo 499793 565393 := bbase (se 2 (by rfl) ⟨212022, by rfl⟩ : syracuseStep 565393 = 424045) (by norm_num)
theorem B565429 : Blo 499793 565429 := bbase (se 5 (by rfl) ⟨26504, by rfl⟩ : syracuseStep 565429 = 53009) (by norm_num)
theorem B1908917 : Blo 499793 1908917 := bbase (se 5 (by rfl) ⟨89480, by rfl⟩ : syracuseStep 1908917 = 178961) (by norm_num)
theorem B565465 : Blo 499793 565465 := bbase (se 2 (by rfl) ⟨212049, by rfl⟩ : syracuseStep 565465 = 424099) (by norm_num)
theorem B2531573 : Blo 499793 2531573 := bbase (se 5 (by rfl) ⟨118667, by rfl⟩ : syracuseStep 2531573 = 237335) (by norm_num)
theorem B565501 : Blo 499793 565501 := bbase (se 3 (by rfl) ⟨106031, by rfl⟩ : syracuseStep 565501 = 212063) (by norm_num)
theorem B565537 : Blo 499793 565537 := bbase (se 2 (by rfl) ⟨212076, by rfl⟩ : syracuseStep 565537 = 424153) (by norm_num)
theorem B1450277 : Blo 499793 1450277 := bbase (se 4 (by rfl) ⟨135963, by rfl⟩ : syracuseStep 1450277 = 271927) (by norm_num)
theorem B565573 : Blo 499793 565573 := bbase (se 4 (by rfl) ⟨53022, by rfl⟩ : syracuseStep 565573 = 106045) (by norm_num)
theorem B565609 : Blo 499793 565609 := bbase (se 2 (by rfl) ⟨212103, by rfl⟩ : syracuseStep 565609 = 424207) (by norm_num)
theorem B565645 : Blo 499793 565645 := bbase (se 3 (by rfl) ⟨106058, by rfl⟩ : syracuseStep 565645 = 212117) (by norm_num)
theorem B4825493 : Blo 499793 4825493 := bbase (se 6 (by rfl) ⟨113097, by rfl⟩ : syracuseStep 4825493 = 226195) (by norm_num)
theorem B565681 : Blo 499793 565681 := bbase (se 2 (by rfl) ⟨212130, by rfl⟩ : syracuseStep 565681 = 424261) (by norm_num)
theorem B565717 : Blo 499793 565717 := bbase (se 7 (by rfl) ⟨6629, by rfl⟩ : syracuseStep 565717 = 13259) (by norm_num)
theorem B565753 : Blo 499793 565753 := bbase (se 2 (by rfl) ⟨212157, by rfl⟩ : syracuseStep 565753 = 424315) (by norm_num)
theorem B565789 : Blo 499793 565789 := bbase (se 3 (by rfl) ⟨106085, by rfl⟩ : syracuseStep 565789 = 212171) (by norm_num)
theorem B565825 : Blo 499793 565825 := bbase (se 2 (by rfl) ⟨212184, by rfl⟩ : syracuseStep 565825 = 424369) (by norm_num)
theorem B1352261 : Blo 499793 1352261 := bbase (se 4 (by rfl) ⟨126774, by rfl⟩ : syracuseStep 1352261 = 253549) (by norm_num)
theorem B565861 : Blo 499793 565861 := bbase (se 4 (by rfl) ⟨53049, by rfl⟩ : syracuseStep 565861 = 106099) (by norm_num)
theorem B565897 : Blo 499793 565897 := bbase (se 2 (by rfl) ⟨212211, by rfl⟩ : syracuseStep 565897 = 424423) (by norm_num)
theorem B565933 : Blo 499793 565933 := bbase (se 3 (by rfl) ⟨106112, by rfl⟩ : syracuseStep 565933 = 212225) (by norm_num)
theorem B565969 : Blo 499793 565969 := bbase (se 2 (by rfl) ⟨212238, by rfl⟩ : syracuseStep 565969 = 424477) (by norm_num)
theorem B566005 : Blo 499793 566005 := bbase (se 5 (by rfl) ⟨26531, by rfl⟩ : syracuseStep 566005 = 53063) (by norm_num)
theorem B2564885 : Blo 499793 2564885 := bbase (se 6 (by rfl) ⟨60114, by rfl⟩ : syracuseStep 2564885 = 120229) (by norm_num)
theorem B566041 : Blo 499793 566041 := bbase (se 2 (by rfl) ⟨212265, by rfl⟩ : syracuseStep 566041 = 424531) (by norm_num)
theorem B566077 : Blo 499793 566077 := bbase (se 3 (by rfl) ⟨106139, by rfl⟩ : syracuseStep 566077 = 212279) (by norm_num)
theorem B566113 : Blo 499793 566113 := bbase (se 2 (by rfl) ⟨212292, by rfl⟩ : syracuseStep 566113 = 424585) (by norm_num)
theorem B566149 : Blo 499793 566149 := bbase (se 4 (by rfl) ⟨53076, by rfl⟩ : syracuseStep 566149 = 106153) (by norm_num)
theorem B566185 : Blo 499793 566185 := bbase (se 2 (by rfl) ⟨212319, by rfl⟩ : syracuseStep 566185 = 424639) (by norm_num)
theorem B2171845 : Blo 499793 2171845 := bbase (se 4 (by rfl) ⟨203610, by rfl⟩ : syracuseStep 2171845 = 407221) (by norm_num)
theorem B566221 : Blo 499793 566221 := bbase (se 3 (by rfl) ⟨106166, by rfl⟩ : syracuseStep 566221 = 212333) (by norm_num)
theorem B566257 : Blo 499793 566257 := bbase (se 2 (by rfl) ⟨212346, by rfl⟩ : syracuseStep 566257 = 424693) (by norm_num)
theorem B566293 : Blo 499793 566293 := bbase (se 6 (by rfl) ⟨13272, by rfl⟩ : syracuseStep 566293 = 26545) (by norm_num)
theorem B4138037 : Blo 499793 4138037 := bbase (se 5 (by rfl) ⟨193970, by rfl⟩ : syracuseStep 4138037 = 387941) (by norm_num)
theorem B566329 : Blo 499793 566329 := bbase (se 2 (by rfl) ⟨212373, by rfl⟩ : syracuseStep 566329 = 424747) (by norm_num)
theorem B566365 : Blo 499793 566365 := bbase (se 3 (by rfl) ⟨106193, by rfl⟩ : syracuseStep 566365 = 212387) (by norm_num)
theorem B566401 : Blo 499793 566401 := bbase (se 2 (by rfl) ⟨212400, by rfl⟩ : syracuseStep 566401 = 424801) (by norm_num)
theorem B566437 : Blo 499793 566437 := bbase (se 4 (by rfl) ⟨53103, by rfl⟩ : syracuseStep 566437 = 106207) (by norm_num)
theorem B566473 : Blo 499793 566473 := bbase (se 2 (by rfl) ⟨212427, by rfl⟩ : syracuseStep 566473 = 424855) (by norm_num)
theorem B2139365 : Blo 499793 2139365 := bbase (se 4 (by rfl) ⟨200565, by rfl⟩ : syracuseStep 2139365 = 401131) (by norm_num)
theorem B566509 : Blo 499793 566509 := bbase (se 3 (by rfl) ⟨106220, by rfl⟩ : syracuseStep 566509 = 212441) (by norm_num)
theorem B566545 : Blo 499793 566545 := bbase (se 2 (by rfl) ⟨212454, by rfl⟩ : syracuseStep 566545 = 424909) (by norm_num)
theorem B2041109 : Blo 499793 2041109 := bbase (se 6 (by rfl) ⟨47838, by rfl⟩ : syracuseStep 2041109 = 95677) (by norm_num)
theorem B763165 : Blo 499793 763165 := bbase (se 3 (by rfl) ⟨143093, by rfl⟩ : syracuseStep 763165 = 286187) (by norm_num)
theorem B566581 : Blo 499793 566581 := bbase (se 5 (by rfl) ⟨26558, by rfl⟩ : syracuseStep 566581 = 53117) (by norm_num)
theorem B533833 : Blo 499793 533833 := bbase (se 2 (by rfl) ⟨200187, by rfl⟩ : syracuseStep 533833 = 400375) (by norm_num)
theorem B1910101 : Blo 499793 1910101 := bbase (se 12 (by rfl) ⟨699, by rfl⟩ : syracuseStep 1910101 = 1399) (by norm_num)
theorem B566617 : Blo 499793 566617 := bbase (se 2 (by rfl) ⟨212481, by rfl⟩ : syracuseStep 566617 = 424963) (by norm_num)
theorem B566653 : Blo 499793 566653 := bbase (se 3 (by rfl) ⟨106247, by rfl⟩ : syracuseStep 566653 = 212495) (by norm_num)
theorem B566689 : Blo 499793 566689 := bbase (se 2 (by rfl) ⟨212508, by rfl⟩ : syracuseStep 566689 = 425017) (by norm_num)
theorem B533953 : Blo 499793 533953 := bbase (se 2 (by rfl) ⟨200232, by rfl⟩ : syracuseStep 533953 = 400465) (by norm_num)
theorem B566725 : Blo 499793 566725 := bbase (se 4 (by rfl) ⟨53130, by rfl⟩ : syracuseStep 566725 = 106261) (by norm_num)
theorem B2139605 : Blo 499793 2139605 := bbase (se 7 (by rfl) ⟨25073, by rfl⟩ : syracuseStep 2139605 = 50147) (by norm_num)
theorem B2041301 : Blo 499793 2041301 := bbase (se 7 (by rfl) ⟨23921, by rfl⟩ : syracuseStep 2041301 = 47843) (by norm_num)
theorem B566761 : Blo 499793 566761 := bbase (se 2 (by rfl) ⟨212535, by rfl⟩ : syracuseStep 566761 = 425071) (by norm_num)
theorem B2532869 : Blo 499793 2532869 := bbase (se 4 (by rfl) ⟨237456, by rfl⟩ : syracuseStep 2532869 = 474913) (by norm_num)
theorem B1910405 : Blo 499793 1910405 := bbase (se 4 (by rfl) ⟨179100, by rfl⟩ : syracuseStep 1910405 = 358201) (by norm_num)
theorem B534205 : Blo 499793 534205 := bbase (se 3 (by rfl) ⟨100163, by rfl⟩ : syracuseStep 534205 = 200327) (by norm_num)
theorem B534209 : Blo 499793 534209 := bbase (se 2 (by rfl) ⟨200328, by rfl⟩ : syracuseStep 534209 = 400657) (by norm_num)
theorem B2860757 : Blo 499793 2860757 := bbase (se 7 (by rfl) ⟨33524, by rfl⟩ : syracuseStep 2860757 = 67049) (by norm_num)
theorem B632605 : Blo 499793 632605 := bbase (se 3 (by rfl) ⟨118613, by rfl⟩ : syracuseStep 632605 = 237227) (by norm_num)
theorem B894797 : Blo 499793 894797 := bbase (se 3 (by rfl) ⟨167774, by rfl⟩ : syracuseStep 894797 = 335549) (by norm_num)
theorem B632701 : Blo 499793 632701 := bbase (se 3 (by rfl) ⟨118631, by rfl⟩ : syracuseStep 632701 = 237263) (by norm_num)
theorem B632873 : Blo 499793 632873 := bbase (se 2 (by rfl) ⟨237327, by rfl⟩ : syracuseStep 632873 = 474655) (by norm_num)
theorem B1353797 : Blo 499793 1353797 := bbase (se 4 (by rfl) ⟨126918, by rfl⟩ : syracuseStep 1353797 = 253837) (by norm_num)
theorem B632929 : Blo 499793 632929 := bbase (se 2 (by rfl) ⟨237348, by rfl⟩ : syracuseStep 632929 = 474697) (by norm_num)
theorem B2402405 : Blo 499793 2402405 := bbase (se 4 (by rfl) ⟨225225, by rfl⟩ : syracuseStep 2402405 = 450451) (by norm_num)
theorem B764005 : Blo 499793 764005 := bbase (se 4 (by rfl) ⟨71625, by rfl⟩ : syracuseStep 764005 = 143251) (by norm_num)
theorem B633025 : Blo 499793 633025 := bbase (se 2 (by rfl) ⟨237384, by rfl⟩ : syracuseStep 633025 = 474769) (by norm_num)
theorem B1124549 : Blo 499793 1124549 := bbase (se 4 (by rfl) ⟨105426, by rfl⟩ : syracuseStep 1124549 = 210853) (by norm_num)
theorem B534773 : Blo 499793 534773 := bbase (se 5 (by rfl) ⟨25067, by rfl⟩ : syracuseStep 534773 = 50135) (by norm_num)
theorem B1124621 : Blo 499793 1124621 := bbase (se 3 (by rfl) ⟨210866, by rfl⟩ : syracuseStep 1124621 = 421733) (by norm_num)
theorem B3909941 : Blo 499793 3909941 := bbase (se 5 (by rfl) ⟨183278, by rfl⟩ : syracuseStep 3909941 = 366557) (by norm_num)
theorem B1124693 : Blo 499793 1124693 := bbase (se 10 (by rfl) ⟨1647, by rfl⟩ : syracuseStep 1124693 = 3295) (by norm_num)
theorem B633197 : Blo 499793 633197 := bbase (se 3 (by rfl) ⟨118724, by rfl⟩ : syracuseStep 633197 = 237449) (by norm_num)
theorem B3058037 : Blo 499793 3058037 := bbase (se 5 (by rfl) ⟨143345, by rfl⟩ : syracuseStep 3058037 = 286691) (by norm_num)
theorem B2402693 : Blo 499793 2402693 := bbase (se 4 (by rfl) ⟨225252, by rfl⟩ : syracuseStep 2402693 = 450505) (by norm_num)
theorem B600457 : Blo 499793 600457 := bbase (se 2 (by rfl) ⟨225171, by rfl⟩ : syracuseStep 600457 = 450343) (by norm_num)
theorem B1124765 : Blo 499793 1124765 := bbase (se 3 (by rfl) ⟨210893, by rfl⟩ : syracuseStep 1124765 = 421787) (by norm_num)
theorem B633253 : Blo 499793 633253 := bbase (se 4 (by rfl) ⟨59367, by rfl⟩ : syracuseStep 633253 = 118735) (by norm_num)
theorem B534961 : Blo 499793 534961 := bbase (se 2 (by rfl) ⟨200610, by rfl⟩ : syracuseStep 534961 = 401221) (by norm_num)
theorem B1124837 : Blo 499793 1124837 := bbase (se 4 (by rfl) ⟨105453, by rfl⟩ : syracuseStep 1124837 = 210907) (by norm_num)
theorem B633349 : Blo 499793 633349 := bbase (se 4 (by rfl) ⟨59376, by rfl⟩ : syracuseStep 633349 = 118753) (by norm_num)
theorem B1124909 : Blo 499793 1124909 := bbase (se 3 (by rfl) ⟨210920, by rfl⟩ : syracuseStep 1124909 = 421841) (by norm_num)
theorem B1124981 : Blo 499793 1124981 := bbase (se 5 (by rfl) ⟨52733, by rfl⟩ : syracuseStep 1124981 = 105467) (by norm_num)
theorem B2894453 : Blo 499793 2894453 := bbase (se 5 (by rfl) ⟨135677, by rfl⟩ : syracuseStep 2894453 = 271355) (by norm_num)
theorem B633521 : Blo 499793 633521 := bbase (se 2 (by rfl) ⟨237570, by rfl⟩ : syracuseStep 633521 = 475141) (by norm_num)
theorem B1452725 : Blo 499793 1452725 := bbase (se 5 (by rfl) ⟨68096, by rfl⟩ : syracuseStep 1452725 = 136193) (by norm_num)
theorem B1125053 : Blo 499793 1125053 := bbase (se 3 (by rfl) ⟨210947, by rfl⟩ : syracuseStep 1125053 = 421895) (by norm_num)
theorem B633577 : Blo 499793 633577 := bbase (se 2 (by rfl) ⟨237591, by rfl⟩ : syracuseStep 633577 = 475183) (by norm_num)
theorem B1125125 : Blo 499793 1125125 := bbase (se 4 (by rfl) ⟨105480, by rfl⟩ : syracuseStep 1125125 = 210961) (by norm_num)
theorem B2534165 : Blo 499793 2534165 := bbase (se 6 (by rfl) ⟨59394, by rfl⟩ : syracuseStep 2534165 = 118789) (by norm_num)
theorem B633673 : Blo 499793 633673 := bbase (se 2 (by rfl) ⟨237627, by rfl⟩ : syracuseStep 633673 = 475255) (by norm_num)
theorem B1125197 : Blo 499793 1125197 := bbase (se 3 (by rfl) ⟨210974, by rfl⟩ : syracuseStep 1125197 = 421949) (by norm_num)
theorem B1125269 : Blo 499793 1125269 := bbase (se 6 (by rfl) ⟨26373, by rfl⟩ : syracuseStep 1125269 = 52747) (by norm_num)
theorem B1125341 : Blo 499793 1125341 := bbase (se 3 (by rfl) ⟨211001, by rfl⟩ : syracuseStep 1125341 = 422003) (by norm_num)
theorem B633845 : Blo 499793 633845 := bbase (se 5 (by rfl) ⟨29711, by rfl⟩ : syracuseStep 633845 = 59423) (by norm_num)
theorem B1125413 : Blo 499793 1125413 := bbase (se 4 (by rfl) ⟨105507, by rfl⟩ : syracuseStep 1125413 = 211015) (by norm_num)
theorem B633901 : Blo 499793 633901 := bbase (se 3 (by rfl) ⟨118856, by rfl⟩ : syracuseStep 633901 = 237713) (by norm_num)
theorem B1125485 : Blo 499793 1125485 := bbase (se 3 (by rfl) ⟨211028, by rfl⟩ : syracuseStep 1125485 = 422057) (by norm_num)
theorem B633997 : Blo 499793 633997 := bbase (se 3 (by rfl) ⟨118874, by rfl⟩ : syracuseStep 633997 = 237749) (by norm_num)
theorem B1125557 : Blo 499793 1125557 := bbase (se 5 (by rfl) ⟨52760, by rfl⟩ : syracuseStep 1125557 = 105521) (by norm_num)
theorem B535781 : Blo 499793 535781 := bbase (se 4 (by rfl) ⟨50229, by rfl⟩ : syracuseStep 535781 = 100459) (by norm_num)
theorem B765173 : Blo 499793 765173 := bbase (se 5 (by rfl) ⟨35867, by rfl⟩ : syracuseStep 765173 = 71735) (by norm_num)
theorem B1125629 : Blo 499793 1125629 := bbase (se 3 (by rfl) ⟨211055, by rfl⟩ : syracuseStep 1125629 = 422111) (by norm_num)
theorem B634169 : Blo 499793 634169 := bbase (se 2 (by rfl) ⟨237813, by rfl⟩ : syracuseStep 634169 = 475627) (by norm_num)
theorem B1125701 : Blo 499793 1125701 := bbase (se 4 (by rfl) ⟨105534, by rfl⟩ : syracuseStep 1125701 = 211069) (by norm_num)
theorem B634225 : Blo 499793 634225 := bbase (se 2 (by rfl) ⟨237834, by rfl⟩ : syracuseStep 634225 = 475669) (by norm_num)
theorem B1125773 : Blo 499793 1125773 := bbase (se 3 (by rfl) ⟨211082, by rfl⟩ : syracuseStep 1125773 = 422165) (by norm_num)
theorem B634321 : Blo 499793 634321 := bbase (se 2 (by rfl) ⟨237870, by rfl⟩ : syracuseStep 634321 = 475741) (by norm_num)
theorem B1125845 : Blo 499793 1125845 := bbase (se 7 (by rfl) ⟨13193, by rfl⟩ : syracuseStep 1125845 = 26387) (by norm_num)
theorem B1224157 : Blo 499793 1224157 := bbase (se 3 (by rfl) ⟨229529, by rfl⟩ : syracuseStep 1224157 = 459059) (by norm_num)
theorem B1125917 : Blo 499793 1125917 := bbase (se 3 (by rfl) ⟨211109, by rfl⟩ : syracuseStep 1125917 = 422219) (by norm_num)
theorem B601673 : Blo 499793 601673 := bbase (se 2 (by rfl) ⟨225627, by rfl⟩ : syracuseStep 601673 = 451255) (by norm_num)
theorem B1125989 : Blo 499793 1125989 := bbase (se 4 (by rfl) ⟨105561, by rfl⟩ : syracuseStep 1125989 = 211123) (by norm_num)
theorem B634493 : Blo 499793 634493 := bbase (se 3 (by rfl) ⟨118967, by rfl⟩ : syracuseStep 634493 = 237935) (by norm_num)
theorem B536225 : Blo 499793 536225 := bbase (se 2 (by rfl) ⟨201084, by rfl⟩ : syracuseStep 536225 = 402169) (by norm_num)
theorem B1126061 : Blo 499793 1126061 := bbase (se 3 (by rfl) ⟨211136, by rfl⟩ : syracuseStep 1126061 = 422273) (by norm_num)
theorem B634549 : Blo 499793 634549 := bbase (se 5 (by rfl) ⟨29744, by rfl⟩ : syracuseStep 634549 = 59489) (by norm_num)
theorem B2141893 : Blo 499793 2141893 := bbase (se 4 (by rfl) ⟨200802, by rfl⟩ : syracuseStep 2141893 = 401605) (by norm_num)
theorem B1912517 : Blo 499793 1912517 := bbase (se 4 (by rfl) ⟨179298, by rfl⟩ : syracuseStep 1912517 = 358597) (by norm_num)
theorem B765677 : Blo 499793 765677 := bbase (se 3 (by rfl) ⟨143564, by rfl⟩ : syracuseStep 765677 = 287129) (by norm_num)
theorem B601841 : Blo 499793 601841 := bbase (se 2 (by rfl) ⟨225690, by rfl⟩ : syracuseStep 601841 = 451381) (by norm_num)
theorem B1126133 : Blo 499793 1126133 := bbase (se 5 (by rfl) ⟨52787, by rfl⟩ : syracuseStep 1126133 = 105575) (by norm_num)
theorem B634645 : Blo 499793 634645 := bbase (se 6 (by rfl) ⟨14874, by rfl⟩ : syracuseStep 634645 = 29749) (by norm_num)
theorem B6893333 : Blo 499793 6893333 := bbase (se 6 (by rfl) ⟨161562, by rfl⟩ : syracuseStep 6893333 = 323125) (by norm_num)
theorem B1126205 : Blo 499793 1126205 := bbase (se 3 (by rfl) ⟨211163, by rfl⟩ : syracuseStep 1126205 = 422327) (by norm_num)
theorem B2862965 : Blo 499793 2862965 := bbase (se 5 (by rfl) ⟨134201, by rfl⟩ : syracuseStep 2862965 = 268403) (by norm_num)
theorem B1126277 : Blo 499793 1126277 := bbase (se 4 (by rfl) ⟨105588, by rfl⟩ : syracuseStep 1126277 = 211177) (by norm_num)
theorem B536473 : Blo 499793 536473 := bbase (se 2 (by rfl) ⟨201177, by rfl⟩ : syracuseStep 536473 = 402355) (by norm_num)
theorem B634817 : Blo 499793 634817 := bbase (se 2 (by rfl) ⟨238056, by rfl⟩ : syracuseStep 634817 = 476113) (by norm_num)
theorem B1126349 : Blo 499793 1126349 := bbase (se 3 (by rfl) ⟨211190, by rfl⟩ : syracuseStep 1126349 = 422381) (by norm_num)
theorem B1912805 : Blo 499793 1912805 := bbase (se 4 (by rfl) ⟨179325, by rfl⟩ : syracuseStep 1912805 = 358651) (by norm_num)
theorem B634873 : Blo 499793 634873 := bbase (se 2 (by rfl) ⟨238077, by rfl⟩ : syracuseStep 634873 = 476155) (by norm_num)
theorem B1126421 : Blo 499793 1126421 := bbase (se 6 (by rfl) ⟨26400, by rfl⟩ : syracuseStep 1126421 = 52801) (by norm_num)
theorem B2535461 : Blo 499793 2535461 := bbase (se 4 (by rfl) ⟨237699, by rfl⟩ : syracuseStep 2535461 = 475399) (by norm_num)
theorem B602149 : Blo 499793 602149 := bbase (se 4 (by rfl) ⟨56451, by rfl⟩ : syracuseStep 602149 = 112903) (by norm_num)
theorem B634969 : Blo 499793 634969 := bbase (se 2 (by rfl) ⟨238113, by rfl⟩ : syracuseStep 634969 = 476227) (by norm_num)
theorem B1126493 : Blo 499793 1126493 := bbase (se 3 (by rfl) ⟨211217, by rfl⟩ : syracuseStep 1126493 = 422435) (by norm_num)
theorem B1126565 : Blo 499793 1126565 := bbase (se 4 (by rfl) ⟨105615, by rfl⟩ : syracuseStep 1126565 = 211231) (by norm_num)
theorem B1126637 : Blo 499793 1126637 := bbase (se 3 (by rfl) ⟨211244, by rfl⟩ : syracuseStep 1126637 = 422489) (by norm_num)
theorem B602365 : Blo 499793 602365 := bbase (se 3 (by rfl) ⟨112943, by rfl⟩ : syracuseStep 602365 = 225887) (by norm_num)
theorem B635141 : Blo 499793 635141 := bbase (se 4 (by rfl) ⟨59544, by rfl⟩ : syracuseStep 635141 = 119089) (by norm_num)
theorem B1126709 : Blo 499793 1126709 := bbase (se 5 (by rfl) ⟨52814, by rfl⟩ : syracuseStep 1126709 = 105629) (by norm_num)
theorem B635197 : Blo 499793 635197 := bbase (se 3 (by rfl) ⟨119099, by rfl⟩ : syracuseStep 635197 = 238199) (by norm_num)
theorem B536905 : Blo 499793 536905 := bbase (se 2 (by rfl) ⟨201339, by rfl⟩ : syracuseStep 536905 = 402679) (by norm_num)
theorem B1126781 : Blo 499793 1126781 := bbase (se 3 (by rfl) ⟨211271, by rfl⟩ : syracuseStep 1126781 = 422543) (by norm_num)
theorem B2568581 : Blo 499793 2568581 := bbase (se 4 (by rfl) ⟨240804, by rfl⟩ : syracuseStep 2568581 = 481609) (by norm_num)
theorem B536977 : Blo 499793 536977 := bbase (se 2 (by rfl) ⟨201366, by rfl⟩ : syracuseStep 536977 = 402733) (by norm_num)
theorem B635293 : Blo 499793 635293 := bbase (se 3 (by rfl) ⟨119117, by rfl⟩ : syracuseStep 635293 = 238235) (by norm_num)
theorem B1290653 : Blo 499793 1290653 := bbase (se 3 (by rfl) ⟨241997, by rfl⟩ : syracuseStep 1290653 = 483995) (by norm_num)
theorem B1126853 : Blo 499793 1126853 := bbase (se 4 (by rfl) ⟨105642, by rfl⟩ : syracuseStep 1126853 = 211285) (by norm_num)
theorem B1126925 : Blo 499793 1126925 := bbase (se 3 (by rfl) ⟨211298, by rfl⟩ : syracuseStep 1126925 = 422597) (by norm_num)
theorem B9777685 : Blo 499793 9777685 := bbase (se 6 (by rfl) ⟨229164, by rfl⟩ : syracuseStep 9777685 = 458329) (by norm_num)
theorem B602677 : Blo 499793 602677 := bbase (se 5 (by rfl) ⟨28250, by rfl⟩ : syracuseStep 602677 = 56501) (by norm_num)
theorem B3224117 : Blo 499793 3224117 := bbase (se 5 (by rfl) ⟨151130, by rfl⟩ : syracuseStep 3224117 = 302261) (by norm_num)
theorem B635465 : Blo 499793 635465 := bbase (se 2 (by rfl) ⟨238299, by rfl⟩ : syracuseStep 635465 = 476599) (by norm_num)
theorem B1126997 : Blo 499793 1126997 := bbase (se 8 (by rfl) ⟨6603, by rfl⟩ : syracuseStep 1126997 = 13207) (by norm_num)
theorem B635521 : Blo 499793 635521 := bbase (se 2 (by rfl) ⟨238320, by rfl⟩ : syracuseStep 635521 = 476641) (by norm_num)
theorem B1127069 : Blo 499793 1127069 := bbase (se 3 (by rfl) ⟨211325, by rfl⟩ : syracuseStep 1127069 = 422651) (by norm_num)
theorem B635617 : Blo 499793 635617 := bbase (se 2 (by rfl) ⟨238356, by rfl⟩ : syracuseStep 635617 = 476713) (by norm_num)
theorem B1127141 : Blo 499793 1127141 := bbase (se 4 (by rfl) ⟨105669, by rfl⟩ : syracuseStep 1127141 = 211339) (by norm_num)
theorem B537349 : Blo 499793 537349 := bbase (se 4 (by rfl) ⟨50376, by rfl⟩ : syracuseStep 537349 = 100753) (by norm_num)
theorem B1127213 : Blo 499793 1127213 := bbase (se 3 (by rfl) ⟨211352, by rfl⟩ : syracuseStep 1127213 = 422705) (by norm_num)
theorem B1127285 : Blo 499793 1127285 := bbase (se 5 (by rfl) ⟨52841, by rfl⟩ : syracuseStep 1127285 = 105683) (by norm_num)
theorem B635789 : Blo 499793 635789 := bbase (se 3 (by rfl) ⟨119210, by rfl⟩ : syracuseStep 635789 = 238421) (by norm_num)
theorem B1127357 : Blo 499793 1127357 := bbase (se 3 (by rfl) ⟨211379, by rfl⟩ : syracuseStep 1127357 = 422759) (by norm_num)
theorem B635845 : Blo 499793 635845 := bbase (se 4 (by rfl) ⟨59610, by rfl⟩ : syracuseStep 635845 = 119221) (by norm_num)
theorem B1127429 : Blo 499793 1127429 := bbase (se 4 (by rfl) ⟨105696, by rfl⟩ : syracuseStep 1127429 = 211393) (by norm_num)
theorem B635941 : Blo 499793 635941 := bbase (se 4 (by rfl) ⟨59619, by rfl⟩ : syracuseStep 635941 = 119239) (by norm_num)
theorem B1127501 : Blo 499793 1127501 := bbase (se 3 (by rfl) ⟨211406, by rfl⟩ : syracuseStep 1127501 = 422813) (by norm_num)
theorem B537725 : Blo 499793 537725 := bbase (se 3 (by rfl) ⟨100823, by rfl⟩ : syracuseStep 537725 = 201647) (by norm_num)
theorem B1127573 : Blo 499793 1127573 := bbase (se 6 (by rfl) ⟨26427, by rfl⟩ : syracuseStep 1127573 = 52855) (by norm_num)
theorem B2143381 : Blo 499793 2143381 := bbase (se 6 (by rfl) ⟨50235, by rfl⟩ : syracuseStep 2143381 = 100471) (by norm_num)
theorem B2143397 : Blo 499793 2143397 := bbase (se 4 (by rfl) ⟨200943, by rfl⟩ : syracuseStep 2143397 = 401887) (by norm_num)
theorem B537797 : Blo 499793 537797 := bbase (se 4 (by rfl) ⟨50418, by rfl⟩ : syracuseStep 537797 = 100837) (by norm_num)
theorem B636113 : Blo 499793 636113 := bbase (se 2 (by rfl) ⟨238542, by rfl⟩ : syracuseStep 636113 = 477085) (by norm_num)
theorem B3814613 : Blo 499793 3814613 := bbase (se 7 (by rfl) ⟨44702, by rfl⟩ : syracuseStep 3814613 = 89405) (by norm_num)
theorem B1127645 : Blo 499793 1127645 := bbase (se 3 (by rfl) ⟨211433, by rfl⟩ : syracuseStep 1127645 = 422867) (by norm_num)
theorem B636169 : Blo 499793 636169 := bbase (se 2 (by rfl) ⟨238563, by rfl⟩ : syracuseStep 636169 = 477127) (by norm_num)
theorem B1127717 : Blo 499793 1127717 := bbase (se 4 (by rfl) ⟨105723, by rfl⟩ : syracuseStep 1127717 = 211447) (by norm_num)
theorem B2536757 : Blo 499793 2536757 := bbase (se 5 (by rfl) ⟨118910, by rfl⟩ : syracuseStep 2536757 = 237821) (by norm_num)
theorem B636265 : Blo 499793 636265 := bbase (se 2 (by rfl) ⟨238599, by rfl⟩ : syracuseStep 636265 = 477199) (by norm_num)
theorem B1127789 : Blo 499793 1127789 := bbase (se 3 (by rfl) ⟨211460, by rfl⟩ : syracuseStep 1127789 = 422921) (by norm_num)
theorem B537985 : Blo 499793 537985 := bbase (se 2 (by rfl) ⟨201744, by rfl⟩ : syracuseStep 537985 = 403489) (by norm_num)
theorem B1127861 : Blo 499793 1127861 := bbase (se 5 (by rfl) ⟨52868, by rfl⟩ : syracuseStep 1127861 = 105737) (by norm_num)
theorem B2635253 : Blo 499793 2635253 := bbase (se 5 (by rfl) ⟨123527, by rfl⟩ : syracuseStep 2635253 = 247055) (by norm_num)
theorem B1127933 : Blo 499793 1127933 := bbase (se 3 (by rfl) ⟨211487, by rfl⟩ : syracuseStep 1127933 = 422975) (by norm_num)
theorem B636437 : Blo 499793 636437 := bbase (se 6 (by rfl) ⟨14916, by rfl⟩ : syracuseStep 636437 = 29833) (by norm_num)
theorem B1226285 : Blo 499793 1226285 := bbase (se 3 (by rfl) ⟨229928, by rfl⟩ : syracuseStep 1226285 = 459857) (by norm_num)
theorem B1128005 : Blo 499793 1128005 := bbase (se 4 (by rfl) ⟨105750, by rfl⟩ : syracuseStep 1128005 = 211501) (by norm_num)
theorem B636493 : Blo 499793 636493 := bbase (se 3 (by rfl) ⟨119342, by rfl⟩ : syracuseStep 636493 = 238685) (by norm_num)
theorem B570997 : Blo 499793 570997 := bbase (se 5 (by rfl) ⟨26765, by rfl⟩ : syracuseStep 570997 = 53531) (by norm_num)
theorem B1128077 : Blo 499793 1128077 := bbase (se 3 (by rfl) ⟨211514, by rfl⟩ : syracuseStep 1128077 = 423029) (by norm_num)
theorem B636589 : Blo 499793 636589 := bbase (se 3 (by rfl) ⟨119360, by rfl⟩ : syracuseStep 636589 = 238721) (by norm_num)
theorem B1357493 : Blo 499793 1357493 := bbase (se 5 (by rfl) ⟨63632, by rfl⟩ : syracuseStep 1357493 = 127265) (by norm_num)
theorem B1717957 : Blo 499793 1717957 := bbase (se 4 (by rfl) ⟨161058, by rfl⟩ : syracuseStep 1717957 = 322117) (by norm_num)
theorem B1128149 : Blo 499793 1128149 := bbase (se 7 (by rfl) ⟨13220, by rfl⟩ : syracuseStep 1128149 = 26441) (by norm_num)
theorem B1128221 : Blo 499793 1128221 := bbase (se 3 (by rfl) ⟨211541, by rfl⟩ : syracuseStep 1128221 = 423083) (by norm_num)
theorem B636761 : Blo 499793 636761 := bbase (se 2 (by rfl) ⟨238785, by rfl⟩ : syracuseStep 636761 = 477571) (by norm_num)
theorem B1128293 : Blo 499793 1128293 := bbase (se 4 (by rfl) ⟨105777, by rfl⟩ : syracuseStep 1128293 = 211555) (by norm_num)
theorem B636817 : Blo 499793 636817 := bbase (se 2 (by rfl) ⟨238806, by rfl⟩ : syracuseStep 636817 = 477613) (by norm_num)
theorem B1128365 : Blo 499793 1128365 := bbase (se 3 (by rfl) ⟨211568, by rfl⟩ : syracuseStep 1128365 = 423137) (by norm_num)
theorem B800693 : Blo 499793 800693 := bbase (se 5 (by rfl) ⟨37532, by rfl⟩ : syracuseStep 800693 = 75065) (by norm_num)
theorem B636913 : Blo 499793 636913 := bbase (se 2 (by rfl) ⟨238842, by rfl⟩ : syracuseStep 636913 = 477685) (by norm_num)
theorem B1128437 : Blo 499793 1128437 := bbase (se 5 (by rfl) ⟨52895, by rfl⟩ : syracuseStep 1128437 = 105791) (by norm_num)
theorem B604157 : Blo 499793 604157 := bbase (se 3 (by rfl) ⟨113279, by rfl⟩ : syracuseStep 604157 = 226559) (by norm_num)
theorem B1128509 : Blo 499793 1128509 := bbase (se 3 (by rfl) ⟨211595, by rfl⟩ : syracuseStep 1128509 = 423191) (by norm_num)
theorem B604253 : Blo 499793 604253 := bbase (se 3 (by rfl) ⟨113297, by rfl⟩ : syracuseStep 604253 = 226595) (by norm_num)
theorem B604273 : Blo 499793 604273 := bbase (se 2 (by rfl) ⟨226602, by rfl⟩ : syracuseStep 604273 = 453205) (by norm_num)
theorem B1128581 : Blo 499793 1128581 := bbase (se 4 (by rfl) ⟨105804, by rfl⟩ : syracuseStep 1128581 = 211609) (by norm_num)
theorem B637085 : Blo 499793 637085 := bbase (se 3 (by rfl) ⟨119453, by rfl⟩ : syracuseStep 637085 = 238907) (by norm_num)
theorem B1128653 : Blo 499793 1128653 := bbase (se 3 (by rfl) ⟨211622, by rfl⟩ : syracuseStep 1128653 = 423245) (by norm_num)
theorem B1521877 : Blo 499793 1521877 := bbase (se 7 (by rfl) ⟨17834, by rfl⟩ : syracuseStep 1521877 = 35669) (by norm_num)
theorem B637141 : Blo 499793 637141 := bbase (se 7 (by rfl) ⟨7466, by rfl⟩ : syracuseStep 637141 = 14933) (by norm_num)
theorem B604417 : Blo 499793 604417 := bbase (se 2 (by rfl) ⟨226656, by rfl⟩ : syracuseStep 604417 = 453313) (by norm_num)
theorem B1128725 : Blo 499793 1128725 := bbase (se 6 (by rfl) ⟨26454, by rfl⟩ : syracuseStep 1128725 = 52909) (by norm_num)
theorem B1423669 : Blo 499793 1423669 := bbase (se 5 (by rfl) ⟨66734, by rfl⟩ : syracuseStep 1423669 = 133469) (by norm_num)
theorem B637237 : Blo 499793 637237 := bbase (se 5 (by rfl) ⟨29870, by rfl⟩ : syracuseStep 637237 = 59741) (by norm_num)
theorem B571717 : Blo 499793 571717 := bbase (se 4 (by rfl) ⟨53598, by rfl⟩ : syracuseStep 571717 = 107197) (by norm_num)
theorem B1128797 : Blo 499793 1128797 := bbase (se 3 (by rfl) ⟨211649, by rfl⟩ : syracuseStep 1128797 = 423299) (by norm_num)
theorem B1128869 : Blo 499793 1128869 := bbase (se 4 (by rfl) ⟨105831, by rfl⟩ : syracuseStep 1128869 = 211663) (by norm_num)
theorem B637409 : Blo 499793 637409 := bbase (se 2 (by rfl) ⟨239028, by rfl⟩ : syracuseStep 637409 = 478057) (by norm_num)
theorem B1128941 : Blo 499793 1128941 := bbase (se 3 (by rfl) ⟨211676, by rfl⟩ : syracuseStep 1128941 = 423353) (by norm_num)
theorem B3619349 : Blo 499793 3619349 := bbase (se 6 (by rfl) ⟨84828, by rfl⟩ : syracuseStep 3619349 = 169657) (by norm_num)
theorem B637465 : Blo 499793 637465 := bbase (se 2 (by rfl) ⟨239049, by rfl⟩ : syracuseStep 637465 = 478099) (by norm_num)
theorem B1129013 : Blo 499793 1129013 := bbase (se 5 (by rfl) ⟨52922, by rfl⟩ : syracuseStep 1129013 = 105845) (by norm_num)
theorem B2538053 : Blo 499793 2538053 := bbase (se 4 (by rfl) ⟨237942, by rfl⟩ : syracuseStep 2538053 = 475885) (by norm_num)
theorem B637561 : Blo 499793 637561 := bbase (se 2 (by rfl) ⟨239085, by rfl⟩ : syracuseStep 637561 = 478171) (by norm_num)
theorem B1129085 : Blo 499793 1129085 := bbase (se 3 (by rfl) ⟨211703, by rfl⟩ : syracuseStep 1129085 = 423407) (by norm_num)
theorem B1129157 : Blo 499793 1129157 := bbase (se 4 (by rfl) ⟨105858, by rfl⟩ : syracuseStep 1129157 = 211717) (by norm_num)
theorem B1129229 : Blo 499793 1129229 := bbase (se 3 (by rfl) ⟨211730, by rfl⟩ : syracuseStep 1129229 = 423461) (by norm_num)
theorem B1129301 : Blo 499793 1129301 := bbase (se 9 (by rfl) ⟨3308, by rfl⟩ : syracuseStep 1129301 = 6617) (by norm_num)
theorem B4078421 : Blo 499793 4078421 := bbase (se 9 (by rfl) ⟨11948, by rfl⟩ : syracuseStep 4078421 = 23897) (by norm_num)
theorem B1129373 : Blo 499793 1129373 := bbase (se 3 (by rfl) ⟨211757, by rfl⟩ : syracuseStep 1129373 = 423515) (by norm_num)
theorem B1129445 : Blo 499793 1129445 := bbase (se 4 (by rfl) ⟨105885, by rfl⟩ : syracuseStep 1129445 = 211771) (by norm_num)
theorem B801821 : Blo 499793 801821 := bbase (se 3 (by rfl) ⟨150341, by rfl⟩ : syracuseStep 801821 = 300683) (by norm_num)
theorem B1129517 : Blo 499793 1129517 := bbase (se 3 (by rfl) ⟨211784, by rfl⟩ : syracuseStep 1129517 = 423569) (by norm_num)
theorem B2407477 : Blo 499793 2407477 := bbase (se 5 (by rfl) ⟨112850, by rfl⟩ : syracuseStep 2407477 = 225701) (by norm_num)
theorem B15416405 : Blo 499793 15416405 := bbase (se 8 (by rfl) ⟨90330, by rfl⟩ : syracuseStep 15416405 = 180661) (by norm_num)
theorem B1129589 : Blo 499793 1129589 := bbase (se 5 (by rfl) ⟨52949, by rfl⟩ : syracuseStep 1129589 = 105899) (by norm_num)
theorem B507017 : Blo 499793 507017 := bbase (se 2 (by rfl) ⟨190131, by rfl⟩ : syracuseStep 507017 = 380263) (by norm_num)
theorem B965773 : Blo 499793 965773 := bbase (se 3 (by rfl) ⟨181082, by rfl⟩ : syracuseStep 965773 = 362165) (by norm_num)
theorem B1129661 : Blo 499793 1129661 := bbase (se 3 (by rfl) ⟨211811, by rfl⟩ : syracuseStep 1129661 = 423623) (by norm_num)
theorem B1129733 : Blo 499793 1129733 := bbase (se 4 (by rfl) ⟨105912, by rfl⟩ : syracuseStep 1129733 = 211825) (by norm_num)
theorem B1129805 : Blo 499793 1129805 := bbase (se 3 (by rfl) ⟨211838, by rfl⟩ : syracuseStep 1129805 = 423677) (by norm_num)
theorem B2145653 : Blo 499793 2145653 := bbase (se 5 (by rfl) ⟨100577, by rfl⟩ : syracuseStep 2145653 = 201155) (by norm_num)
theorem B1129877 : Blo 499793 1129877 := bbase (se 6 (by rfl) ⟨26481, by rfl⟩ : syracuseStep 1129877 = 52963) (by norm_num)
theorem B1359301 : Blo 499793 1359301 := bbase (se 4 (by rfl) ⟨127434, by rfl⟩ : syracuseStep 1359301 = 254869) (by norm_num)
theorem B1129949 : Blo 499793 1129949 := bbase (se 3 (by rfl) ⟨211865, by rfl⟩ : syracuseStep 1129949 = 423731) (by norm_num)
theorem B1687013 : Blo 499793 1687013 := bbase (se 4 (by rfl) ⟨158157, by rfl⟩ : syracuseStep 1687013 = 316315) (by norm_num)
theorem B802333 : Blo 499793 802333 := bbase (se 3 (by rfl) ⟨150437, by rfl⟩ : syracuseStep 802333 = 300875) (by norm_num)
theorem B1130021 : Blo 499793 1130021 := bbase (se 4 (by rfl) ⟨105939, by rfl⟩ : syracuseStep 1130021 = 211879) (by norm_num)
theorem B1130093 : Blo 499793 1130093 := bbase (se 3 (by rfl) ⟨211892, by rfl⟩ : syracuseStep 1130093 = 423785) (by norm_num)
theorem B1130165 : Blo 499793 1130165 := bbase (se 5 (by rfl) ⟨52976, by rfl⟩ : syracuseStep 1130165 = 105953) (by norm_num)
theorem B1130237 : Blo 499793 1130237 := bbase (se 3 (by rfl) ⟨211919, by rfl⟩ : syracuseStep 1130237 = 423839) (by norm_num)
theorem B1130309 : Blo 499793 1130309 := bbase (se 4 (by rfl) ⟨105966, by rfl⟩ : syracuseStep 1130309 = 211933) (by norm_num)
theorem B2539349 : Blo 499793 2539349 := bbase (se 9 (by rfl) ⟨7439, by rfl⟩ : syracuseStep 2539349 = 14879) (by norm_num)
theorem B1130381 : Blo 499793 1130381 := bbase (se 3 (by rfl) ⟨211946, by rfl⟩ : syracuseStep 1130381 = 423893) (by norm_num)
theorem B1687445 : Blo 499793 1687445 := bbase (se 6 (by rfl) ⟨39549, by rfl⟩ : syracuseStep 1687445 = 79099) (by norm_num)
theorem B1130453 : Blo 499793 1130453 := bbase (se 7 (by rfl) ⟨13247, by rfl⟩ : syracuseStep 1130453 = 26495) (by norm_num)
theorem B1130525 : Blo 499793 1130525 := bbase (se 3 (by rfl) ⟨211973, by rfl⟩ : syracuseStep 1130525 = 423947) (by norm_num)
theorem B802877 : Blo 499793 802877 := bbase (se 3 (by rfl) ⟨150539, by rfl⟩ : syracuseStep 802877 = 301079) (by norm_num)
theorem B1130597 : Blo 499793 1130597 := bbase (se 4 (by rfl) ⟨105993, by rfl⟩ : syracuseStep 1130597 = 211987) (by norm_num)
theorem B1130669 : Blo 499793 1130669 := bbase (se 3 (by rfl) ⟨212000, by rfl⟩ : syracuseStep 1130669 = 424001) (by norm_num)
theorem B1130741 : Blo 499793 1130741 := bbase (se 5 (by rfl) ⟨53003, by rfl⟩ : syracuseStep 1130741 = 106007) (by norm_num)
theorem B1130813 : Blo 499793 1130813 := bbase (se 3 (by rfl) ⟨212027, by rfl⟩ : syracuseStep 1130813 = 424055) (by norm_num)
theorem B1687877 : Blo 499793 1687877 := bbase (se 4 (by rfl) ⟨158238, by rfl⟩ : syracuseStep 1687877 = 316477) (by norm_num)
theorem B1130885 : Blo 499793 1130885 := bbase (se 4 (by rfl) ⟨106020, by rfl⟩ : syracuseStep 1130885 = 212041) (by norm_num)
theorem B1360261 : Blo 499793 1360261 := bbase (se 4 (by rfl) ⟨127524, by rfl⟩ : syracuseStep 1360261 = 255049) (by norm_num)
theorem B1130957 : Blo 499793 1130957 := bbase (se 3 (by rfl) ⟨212054, by rfl⟩ : syracuseStep 1130957 = 424109) (by norm_num)
theorem B6406613 : Blo 499793 6406613 := bbase (se 7 (by rfl) ⟨75077, by rfl⟩ : syracuseStep 6406613 = 150155) (by norm_num)
theorem B3621365 : Blo 499793 3621365 := bbase (se 5 (by rfl) ⟨169751, by rfl⟩ : syracuseStep 3621365 = 339503) (by norm_num)
theorem B1131029 : Blo 499793 1131029 := bbase (se 6 (by rfl) ⟨26508, by rfl⟩ : syracuseStep 1131029 = 53017) (by norm_num)
theorem B2114117 : Blo 499793 2114117 := bbase (se 4 (by rfl) ⟨198198, by rfl⟩ : syracuseStep 2114117 = 396397) (by norm_num)
theorem B901709 : Blo 499793 901709 := bbase (se 3 (by rfl) ⟨169070, by rfl⟩ : syracuseStep 901709 = 338141) (by norm_num)
theorem B1131101 : Blo 499793 1131101 := bbase (se 3 (by rfl) ⟨212081, by rfl⟩ : syracuseStep 1131101 = 424163) (by norm_num)
theorem B803429 : Blo 499793 803429 := bbase (se 4 (by rfl) ⟨75321, by rfl⟩ : syracuseStep 803429 = 150643) (by norm_num)
theorem B803461 : Blo 499793 803461 := bbase (se 4 (by rfl) ⟨75324, by rfl⟩ : syracuseStep 803461 = 150649) (by norm_num)
theorem B1131173 : Blo 499793 1131173 := bbase (se 4 (by rfl) ⟨106047, by rfl⟩ : syracuseStep 1131173 = 212095) (by norm_num)
theorem B1360565 : Blo 499793 1360565 := bbase (se 5 (by rfl) ⟨63776, by rfl⟩ : syracuseStep 1360565 = 127553) (by norm_num)
theorem B1131245 : Blo 499793 1131245 := bbase (se 3 (by rfl) ⟨212108, by rfl⟩ : syracuseStep 1131245 = 424217) (by norm_num)
theorem B1688309 : Blo 499793 1688309 := bbase (se 5 (by rfl) ⟨79139, by rfl⟩ : syracuseStep 1688309 = 158279) (by norm_num)
theorem B574225 : Blo 499793 574225 := bbase (se 2 (by rfl) ⟨215334, by rfl⟩ : syracuseStep 574225 = 430669) (by norm_num)
theorem B1131317 : Blo 499793 1131317 := bbase (se 5 (by rfl) ⟨53030, by rfl⟩ : syracuseStep 1131317 = 106061) (by norm_num)
theorem B1131389 : Blo 499793 1131389 := bbase (se 3 (by rfl) ⟨212135, by rfl⟩ : syracuseStep 1131389 = 424271) (by norm_num)
theorem B1131461 : Blo 499793 1131461 := bbase (se 4 (by rfl) ⟨106074, by rfl⟩ : syracuseStep 1131461 = 212149) (by norm_num)
theorem B1131533 : Blo 499793 1131533 := bbase (se 3 (by rfl) ⟨212162, by rfl⟩ : syracuseStep 1131533 = 424325) (by norm_num)
theorem B1426517 : Blo 499793 1426517 := bbase (se 8 (by rfl) ⟨8358, by rfl⟩ : syracuseStep 1426517 = 16717) (by norm_num)
theorem B1131605 : Blo 499793 1131605 := bbase (se 8 (by rfl) ⟨6630, by rfl⟩ : syracuseStep 1131605 = 13261) (by norm_num)
theorem B2540645 : Blo 499793 2540645 := bbase (se 4 (by rfl) ⟨238185, by rfl⟩ : syracuseStep 2540645 = 476371) (by norm_num)
theorem B1131677 : Blo 499793 1131677 := bbase (se 3 (by rfl) ⟨212189, by rfl⟩ : syracuseStep 1131677 = 424379) (by norm_num)
theorem B1688741 : Blo 499793 1688741 := bbase (se 4 (by rfl) ⟨158319, by rfl⟩ : syracuseStep 1688741 = 316639) (by norm_num)
theorem B1131749 : Blo 499793 1131749 := bbase (se 4 (by rfl) ⟨106101, by rfl⟩ : syracuseStep 1131749 = 212203) (by norm_num)
theorem B1131821 : Blo 499793 1131821 := bbase (se 3 (by rfl) ⟨212216, by rfl⟩ : syracuseStep 1131821 = 424433) (by norm_num)
theorem B1131893 : Blo 499793 1131893 := bbase (se 5 (by rfl) ⟨53057, by rfl⟩ : syracuseStep 1131893 = 106115) (by norm_num)
theorem B1131965 : Blo 499793 1131965 := bbase (se 3 (by rfl) ⟨212243, by rfl⟩ : syracuseStep 1131965 = 424487) (by norm_num)
theorem B1132037 : Blo 499793 1132037 := bbase (se 4 (by rfl) ⟨106128, by rfl⟩ : syracuseStep 1132037 = 212257) (by norm_num)
theorem B804389 : Blo 499793 804389 := bbase (se 4 (by rfl) ⟨75411, by rfl⟩ : syracuseStep 804389 = 150823) (by norm_num)
theorem B1132109 : Blo 499793 1132109 := bbase (se 3 (by rfl) ⟨212270, by rfl⟩ : syracuseStep 1132109 = 424541) (by norm_num)
theorem B1689173 : Blo 499793 1689173 := bbase (se 8 (by rfl) ⟨9897, by rfl⟩ : syracuseStep 1689173 = 19795) (by norm_num)
theorem B1132181 : Blo 499793 1132181 := bbase (se 6 (by rfl) ⟨26535, by rfl⟩ : syracuseStep 1132181 = 53071) (by norm_num)
theorem B1525429 : Blo 499793 1525429 := bbase (se 5 (by rfl) ⟨71504, by rfl⟩ : syracuseStep 1525429 = 143009) (by norm_num)
theorem B1132253 : Blo 499793 1132253 := bbase (se 3 (by rfl) ⟨212297, by rfl⟩ : syracuseStep 1132253 = 424595) (by norm_num)
theorem B1623797 : Blo 499793 1623797 := bbase (se 5 (by rfl) ⟨76115, by rfl⟩ : syracuseStep 1623797 = 152231) (by norm_num)
theorem B1132325 : Blo 499793 1132325 := bbase (se 4 (by rfl) ⟨106155, by rfl⟩ : syracuseStep 1132325 = 212311) (by norm_num)
theorem B1132397 : Blo 499793 1132397 := bbase (se 3 (by rfl) ⟨212324, by rfl⟩ : syracuseStep 1132397 = 424649) (by norm_num)
theorem B1132469 : Blo 499793 1132469 := bbase (se 5 (by rfl) ⟨53084, by rfl⟩ : syracuseStep 1132469 = 106169) (by norm_num)
theorem B1132541 : Blo 499793 1132541 := bbase (se 3 (by rfl) ⟨212351, by rfl⟩ : syracuseStep 1132541 = 424703) (by norm_num)
theorem B1689605 : Blo 499793 1689605 := bbase (se 4 (by rfl) ⟨158400, by rfl⟩ : syracuseStep 1689605 = 316801) (by norm_num)
theorem B1132613 : Blo 499793 1132613 := bbase (se 4 (by rfl) ⟨106182, by rfl⟩ : syracuseStep 1132613 = 212365) (by norm_num)
theorem B1132685 : Blo 499793 1132685 := bbase (se 3 (by rfl) ⟨212378, by rfl⟩ : syracuseStep 1132685 = 424757) (by norm_num)
theorem B805069 : Blo 499793 805069 := bbase (se 3 (by rfl) ⟨150950, by rfl⟩ : syracuseStep 805069 = 301901) (by norm_num)
theorem B1132757 : Blo 499793 1132757 := bbase (se 7 (by rfl) ⟨13274, by rfl⟩ : syracuseStep 1132757 = 26549) (by norm_num)
theorem B1427701 : Blo 499793 1427701 := bbase (se 5 (by rfl) ⟨66923, by rfl⟩ : syracuseStep 1427701 = 133847) (by norm_num)
theorem B641293 : Blo 499793 641293 := bbase (se 3 (by rfl) ⟨120242, by rfl⟩ : syracuseStep 641293 = 240485) (by norm_num)
theorem B805133 : Blo 499793 805133 := bbase (se 3 (by rfl) ⟨150962, by rfl⟩ : syracuseStep 805133 = 301925) (by norm_num)
theorem B1132829 : Blo 499793 1132829 := bbase (se 3 (by rfl) ⟨212405, by rfl⟩ : syracuseStep 1132829 = 424811) (by norm_num)
theorem B1132901 : Blo 499793 1132901 := bbase (se 4 (by rfl) ⟨106209, by rfl⟩ : syracuseStep 1132901 = 212419) (by norm_num)
theorem B2541941 : Blo 499793 2541941 := bbase (se 5 (by rfl) ⟨119153, by rfl⟩ : syracuseStep 2541941 = 238307) (by norm_num)
theorem B1427861 : Blo 499793 1427861 := bbase (se 6 (by rfl) ⟨33465, by rfl⟩ : syracuseStep 1427861 = 66931) (by norm_num)
theorem B1132973 : Blo 499793 1132973 := bbase (se 3 (by rfl) ⟨212432, by rfl⟩ : syracuseStep 1132973 = 424865) (by norm_num)
theorem B1690037 : Blo 499793 1690037 := bbase (se 5 (by rfl) ⟨79220, by rfl⟩ : syracuseStep 1690037 = 158441) (by norm_num)
theorem B1133045 : Blo 499793 1133045 := bbase (se 5 (by rfl) ⟨53111, by rfl⟩ : syracuseStep 1133045 = 106223) (by norm_num)
theorem B1133117 : Blo 499793 1133117 := bbase (se 3 (by rfl) ⟨212459, by rfl⟩ : syracuseStep 1133117 = 424919) (by norm_num)
theorem B1428101 : Blo 499793 1428101 := bbase (se 4 (by rfl) ⟨133884, by rfl⟩ : syracuseStep 1428101 = 267769) (by norm_num)
theorem B1133189 : Blo 499793 1133189 := bbase (se 4 (by rfl) ⟨106236, by rfl⟩ : syracuseStep 1133189 = 212473) (by norm_num)
theorem B1067701 : Blo 499793 1067701 := bbase (se 5 (by rfl) ⟨50048, by rfl⟩ : syracuseStep 1067701 = 100097) (by norm_num)
theorem B1133261 : Blo 499793 1133261 := bbase (se 3 (by rfl) ⟨212486, by rfl⟩ : syracuseStep 1133261 = 424973) (by norm_num)
theorem B1133333 : Blo 499793 1133333 := bbase (se 6 (by rfl) ⟨26562, by rfl⟩ : syracuseStep 1133333 = 53125) (by norm_num)
theorem B1428293 : Blo 499793 1428293 := bbase (se 4 (by rfl) ⟨133902, by rfl⟩ : syracuseStep 1428293 = 267805) (by norm_num)
theorem B1526597 : Blo 499793 1526597 := bbase (se 4 (by rfl) ⟨143118, by rfl⟩ : syracuseStep 1526597 = 286237) (by norm_num)
theorem B1133405 : Blo 499793 1133405 := bbase (se 3 (by rfl) ⟨212513, by rfl⟩ : syracuseStep 1133405 = 425027) (by norm_num)
theorem B1690469 : Blo 499793 1690469 := bbase (se 4 (by rfl) ⟨158481, by rfl⟩ : syracuseStep 1690469 = 316963) (by norm_num)
theorem B871309 : Blo 499793 871309 := bbase (se 3 (by rfl) ⟨163370, by rfl⟩ : syracuseStep 871309 = 326741) (by norm_num)
theorem B1133477 : Blo 499793 1133477 := bbase (se 4 (by rfl) ⟨106263, by rfl⟩ : syracuseStep 1133477 = 212527) (by norm_num)
theorem B2411477 : Blo 499793 2411477 := bbase (se 7 (by rfl) ⟨28259, by rfl⟩ : syracuseStep 2411477 = 56519) (by norm_num)
theorem B2411669 : Blo 499793 2411669 := bbase (se 6 (by rfl) ⟨56523, by rfl⟩ : syracuseStep 2411669 = 113047) (by norm_num)
theorem B1690901 : Blo 499793 1690901 := bbase (se 6 (by rfl) ⟨39630, by rfl⟩ : syracuseStep 1690901 = 79261) (by norm_num)
theorem B2149685 : Blo 499793 2149685 := bbase (se 5 (by rfl) ⟨100766, by rfl⟩ : syracuseStep 2149685 = 201533) (by norm_num)
theorem B642433 : Blo 499793 642433 := bbase (se 2 (by rfl) ⟨240912, by rfl⟩ : syracuseStep 642433 = 481825) (by norm_num)
theorem B609805 : Blo 499793 609805 := bbase (se 3 (by rfl) ⟨114338, by rfl⟩ : syracuseStep 609805 = 228677) (by norm_num)
theorem B1068589 : Blo 499793 1068589 := bbase (se 3 (by rfl) ⟨200360, by rfl⟩ : syracuseStep 1068589 = 400721) (by norm_num)
theorem B773677 : Blo 499793 773677 := bbase (se 3 (by rfl) ⟨145064, by rfl⟩ : syracuseStep 773677 = 290129) (by norm_num)
theorem B806453 : Blo 499793 806453 := bbase (se 5 (by rfl) ⟨37802, by rfl⟩ : syracuseStep 806453 = 75605) (by norm_num)
theorem B904765 : Blo 499793 904765 := bbase (se 3 (by rfl) ⟨169643, by rfl⟩ : syracuseStep 904765 = 339287) (by norm_num)
theorem B2543237 : Blo 499793 2543237 := bbase (se 4 (by rfl) ⟨238428, by rfl⟩ : syracuseStep 2543237 = 476857) (by norm_num)
theorem B1068709 : Blo 499793 1068709 := bbase (se 4 (by rfl) ⟨100191, by rfl⟩ : syracuseStep 1068709 = 200383) (by norm_num)
theorem B1265341 : Blo 499793 1265341 := bbase (se 3 (by rfl) ⟨237251, by rfl⟩ : syracuseStep 1265341 = 474503) (by norm_num)
theorem B1691333 : Blo 499793 1691333 := bbase (se 4 (by rfl) ⟨158562, by rfl⟩ : syracuseStep 1691333 = 317125) (by norm_num)
theorem B806645 : Blo 499793 806645 := bbase (se 5 (by rfl) ⟨37811, by rfl⟩ : syracuseStep 806645 = 75623) (by norm_num)
theorem B1429285 : Blo 499793 1429285 := bbase (se 4 (by rfl) ⟨133995, by rfl⟩ : syracuseStep 1429285 = 267991) (by norm_num)
theorem B1265453 : Blo 499793 1265453 := bbase (se 3 (by rfl) ⟨237272, by rfl⟩ : syracuseStep 1265453 = 474545) (by norm_num)
theorem B642925 : Blo 499793 642925 := bbase (se 3 (by rfl) ⟨120548, by rfl⟩ : syracuseStep 642925 = 241097) (by norm_num)
theorem B905069 : Blo 499793 905069 := bbase (se 3 (by rfl) ⟨169700, by rfl⟩ : syracuseStep 905069 = 339401) (by norm_num)
theorem B806773 : Blo 499793 806773 := bbase (se 5 (by rfl) ⟨37817, by rfl⟩ : syracuseStep 806773 = 75635) (by norm_num)
theorem B1068965 : Blo 499793 1068965 := bbase (se 4 (by rfl) ⟨100215, by rfl⟩ : syracuseStep 1068965 = 200431) (by norm_num)
theorem B1265645 : Blo 499793 1265645 := bbase (se 3 (by rfl) ⟨237308, by rfl⟩ : syracuseStep 1265645 = 474617) (by norm_num)
theorem B1691765 : Blo 499793 1691765 := bbase (se 5 (by rfl) ⟨79301, by rfl⟩ : syracuseStep 1691765 = 158603) (by norm_num)
theorem B643253 : Blo 499793 643253 := bbase (se 5 (by rfl) ⟨30152, by rfl⟩ : syracuseStep 643253 = 60305) (by norm_num)
theorem B1265989 : Blo 499793 1265989 := bbase (se 4 (by rfl) ⟨118686, by rfl⟩ : syracuseStep 1265989 = 237373) (by norm_num)
theorem B708949 : Blo 499793 708949 := bbase (se 10 (by rfl) ⟨1038, by rfl⟩ : syracuseStep 708949 = 2077) (by norm_num)
theorem B1266101 : Blo 499793 1266101 := bbase (se 5 (by rfl) ⟨59348, by rfl⟩ : syracuseStep 1266101 = 118697) (by norm_num)
theorem B1692197 : Blo 499793 1692197 := bbase (se 4 (by rfl) ⟨158643, by rfl⟩ : syracuseStep 1692197 = 317287) (by norm_num)
theorem B2904661 : Blo 499793 2904661 := bbase (se 8 (by rfl) ⟨17019, by rfl⟩ : syracuseStep 2904661 = 34039) (by norm_num)
theorem B1266293 : Blo 499793 1266293 := bbase (se 5 (by rfl) ⟨59357, by rfl⟩ : syracuseStep 1266293 = 118715) (by norm_num)
theorem B906005 : Blo 499793 906005 := bbase (se 6 (by rfl) ⟨21234, by rfl⟩ : syracuseStep 906005 = 42469) (by norm_num)
theorem B1069853 : Blo 499793 1069853 := bbase (se 3 (by rfl) ⟨200597, by rfl⟩ : syracuseStep 1069853 = 401195) (by norm_num)
theorem B3822389 : Blo 499793 3822389 := bbase (se 5 (by rfl) ⟨179174, by rfl⟩ : syracuseStep 3822389 = 358349) (by norm_num)
theorem B1430389 : Blo 499793 1430389 := bbase (se 5 (by rfl) ⟨67049, by rfl⟩ : syracuseStep 1430389 = 134099) (by norm_num)
theorem B676757 : Blo 499793 676757 := bbase (se 6 (by rfl) ⟨15861, by rfl⟩ : syracuseStep 676757 = 31723) (by norm_num)
theorem B2544533 : Blo 499793 2544533 := bbase (se 6 (by rfl) ⟨59637, by rfl⟩ : syracuseStep 2544533 = 119275) (by norm_num)
theorem B1266637 : Blo 499793 1266637 := bbase (se 3 (by rfl) ⟨237494, by rfl⟩ : syracuseStep 1266637 = 474989) (by norm_num)
theorem B1692629 : Blo 499793 1692629 := bbase (se 7 (by rfl) ⟨19835, by rfl⟩ : syracuseStep 1692629 = 39671) (by norm_num)
theorem B1070093 : Blo 499793 1070093 := bbase (se 3 (by rfl) ⟨200642, by rfl⟩ : syracuseStep 1070093 = 401285) (by norm_num)
theorem B2151461 : Blo 499793 2151461 := bbase (se 4 (by rfl) ⟨201699, by rfl⟩ : syracuseStep 2151461 = 403399) (by norm_num)
theorem B1266749 : Blo 499793 1266749 := bbase (se 3 (by rfl) ⟨237515, by rfl⟩ : syracuseStep 1266749 = 475031) (by norm_num)
theorem B2282597 : Blo 499793 2282597 := bbase (se 4 (by rfl) ⟨213993, by rfl⟩ : syracuseStep 2282597 = 427987) (by norm_num)
theorem B1266941 : Blo 499793 1266941 := bbase (se 3 (by rfl) ⟨237551, by rfl⟩ : syracuseStep 1266941 = 475103) (by norm_num)
theorem B1693061 : Blo 499793 1693061 := bbase (se 4 (by rfl) ⟨158724, by rfl⟩ : syracuseStep 1693061 = 317449) (by norm_num)
theorem B4576661 : Blo 499793 4576661 := bbase (se 6 (by rfl) ⟨107265, by rfl⟩ : syracuseStep 4576661 = 214531) (by norm_num)
theorem B1070597 : Blo 499793 1070597 := bbase (se 4 (by rfl) ⟨100368, by rfl⟩ : syracuseStep 1070597 = 200737) (by norm_num)
theorem B1070605 : Blo 499793 1070605 := bbase (se 3 (by rfl) ⟨200738, by rfl⟩ : syracuseStep 1070605 = 401477) (by norm_num)
theorem B1267285 : Blo 499793 1267285 := bbase (se 8 (by rfl) ⟨7425, by rfl⟩ : syracuseStep 1267285 = 14851) (by norm_num)
theorem B611933 : Blo 499793 611933 := bbase (se 3 (by rfl) ⟨114737, by rfl⟩ : syracuseStep 611933 = 229475) (by norm_num)
theorem B611993 : Blo 499793 611993 := bbase (se 2 (by rfl) ⟨229497, by rfl⟩ : syracuseStep 611993 = 458995) (by norm_num)
theorem B1201837 : Blo 499793 1201837 := bbase (se 3 (by rfl) ⟨225344, by rfl⟩ : syracuseStep 1201837 = 450689) (by norm_num)
theorem B1267397 : Blo 499793 1267397 := bbase (se 4 (by rfl) ⟨118818, by rfl⟩ : syracuseStep 1267397 = 237637) (by norm_num)
theorem B2283221 : Blo 499793 2283221 := bbase (se 7 (by rfl) ⟨26756, by rfl⟩ : syracuseStep 2283221 = 53513) (by norm_num)
theorem B1693493 : Blo 499793 1693493 := bbase (se 5 (by rfl) ⟨79382, by rfl⟩ : syracuseStep 1693493 = 158765) (by norm_num)
theorem B513869 : Blo 499793 513869 := bbase (se 3 (by rfl) ⟨96350, by rfl⟩ : syracuseStep 513869 = 192701) (by norm_num)
theorem B1267589 : Blo 499793 1267589 := bbase (se 4 (by rfl) ⟨118836, by rfl⟩ : syracuseStep 1267589 = 237673) (by norm_num)
theorem B2545829 : Blo 499793 2545829 := bbase (se 4 (by rfl) ⟨238671, by rfl⟩ : syracuseStep 2545829 = 477343) (by norm_num)
theorem B8542421 : Blo 499793 8542421 := bbase (se 7 (by rfl) ⟨100106, by rfl⟩ : syracuseStep 8542421 = 200213) (by norm_num)
theorem B1267933 : Blo 499793 1267933 := bbase (se 3 (by rfl) ⟨237737, by rfl⟩ : syracuseStep 1267933 = 475475) (by norm_num)
theorem B1693925 : Blo 499793 1693925 := bbase (se 4 (by rfl) ⟨158805, by rfl⟩ : syracuseStep 1693925 = 317611) (by norm_num)
theorem B1202501 : Blo 499793 1202501 := bbase (se 4 (by rfl) ⟨112734, by rfl⟩ : syracuseStep 1202501 = 225469) (by norm_num)
theorem B1268045 : Blo 499793 1268045 := bbase (se 3 (by rfl) ⟨237758, by rfl⟩ : syracuseStep 1268045 = 475517) (by norm_num)
theorem B18340181 : Blo 499793 18340181 := bbase (se 10 (by rfl) ⟨26865, by rfl⟩ : syracuseStep 18340181 = 53731) (by norm_num)
theorem B1431893 : Blo 499793 1431893 := bbase (se 10 (by rfl) ⟨2097, by rfl⟩ : syracuseStep 1431893 = 4195) (by norm_num)
theorem B1268237 : Blo 499793 1268237 := bbase (se 3 (by rfl) ⟨237794, by rfl⟩ : syracuseStep 1268237 = 475589) (by norm_num)
theorem B1071733 : Blo 499793 1071733 := bbase (se 5 (by rfl) ⟨50237, by rfl⟩ : syracuseStep 1071733 = 100475) (by norm_num)
theorem B1694357 : Blo 499793 1694357 := bbase (se 6 (by rfl) ⟨39711, by rfl⟩ : syracuseStep 1694357 = 79423) (by norm_num)
theorem B1268581 : Blo 499793 1268581 := bbase (se 4 (by rfl) ⟨118929, by rfl⟩ : syracuseStep 1268581 = 237859) (by norm_num)
theorem B1858405 : Blo 499793 1858405 := bbase (se 4 (by rfl) ⟨174225, by rfl⟩ : syracuseStep 1858405 = 348451) (by norm_num)
theorem B1268693 : Blo 499793 1268693 := bbase (se 7 (by rfl) ⟨14867, by rfl⟩ : syracuseStep 1268693 = 29735) (by norm_num)
theorem B1072109 : Blo 499793 1072109 := bbase (se 3 (by rfl) ⟨201020, by rfl⟩ : syracuseStep 1072109 = 402041) (by norm_num)
theorem B1694789 : Blo 499793 1694789 := bbase (se 4 (by rfl) ⟨158886, by rfl⟩ : syracuseStep 1694789 = 317773) (by norm_num)
theorem B679045 : Blo 499793 679045 := bbase (se 4 (by rfl) ⟨63660, by rfl⟩ : syracuseStep 679045 = 127321) (by norm_num)
theorem B1268885 : Blo 499793 1268885 := bbase (se 6 (by rfl) ⟨29739, by rfl⟩ : syracuseStep 1268885 = 59479) (by norm_num)
theorem B679061 : Blo 499793 679061 := bbase (se 6 (by rfl) ⟨15915, by rfl⟩ : syracuseStep 679061 = 31831) (by norm_num)
theorem B2415781 : Blo 499793 2415781 := bbase (se 4 (by rfl) ⟨226479, by rfl⟩ : syracuseStep 2415781 = 452959) (by norm_num)
theorem B2547125 : Blo 499793 2547125 := bbase (se 5 (by rfl) ⟨119396, by rfl⟩ : syracuseStep 2547125 = 238793) (by norm_num)
theorem B712165 : Blo 499793 712165 := bbase (se 4 (by rfl) ⟨66765, by rfl⟩ : syracuseStep 712165 = 133531) (by norm_num)
theorem B1269229 : Blo 499793 1269229 := bbase (se 3 (by rfl) ⟨237980, by rfl⟩ : syracuseStep 1269229 = 475961) (by norm_num)
theorem B1695221 : Blo 499793 1695221 := bbase (se 5 (by rfl) ⟨79463, by rfl⟩ : syracuseStep 1695221 = 158927) (by norm_num)
theorem B1269341 : Blo 499793 1269341 := bbase (se 3 (by rfl) ⟨238001, by rfl⟩ : syracuseStep 1269341 = 476003) (by norm_num)
theorem B1203893 : Blo 499793 1203893 := bbase (se 5 (by rfl) ⟨56432, by rfl⟩ : syracuseStep 1203893 = 112865) (by norm_num)
theorem B843493 : Blo 499793 843493 := bbase (se 4 (by rfl) ⟨79077, by rfl⟩ : syracuseStep 843493 = 158155) (by norm_num)
theorem B1203989 : Blo 499793 1203989 := bbase (se 6 (by rfl) ⟨28218, by rfl⟩ : syracuseStep 1203989 = 56437) (by norm_num)
theorem B1269533 : Blo 499793 1269533 := bbase (se 3 (by rfl) ⟨238037, by rfl⟩ : syracuseStep 1269533 = 476075) (by norm_num)
theorem B843581 : Blo 499793 843581 := bbase (se 3 (by rfl) ⟨158171, by rfl⟩ : syracuseStep 843581 = 316343) (by norm_num)
theorem B4972373 : Blo 499793 4972373 := bbase (se 9 (by rfl) ⟨14567, by rfl⟩ : syracuseStep 4972373 = 29135) (by norm_num)
theorem B1433477 : Blo 499793 1433477 := bbase (se 4 (by rfl) ⟨134388, by rfl⟩ : syracuseStep 1433477 = 268777) (by norm_num)
theorem B1531781 : Blo 499793 1531781 := bbase (se 4 (by rfl) ⟨143604, by rfl⟩ : syracuseStep 1531781 = 287209) (by norm_num)
theorem B1695653 : Blo 499793 1695653 := bbase (se 4 (by rfl) ⟨158967, by rfl⟩ : syracuseStep 1695653 = 317935) (by norm_num)
theorem B843709 : Blo 499793 843709 := bbase (se 3 (by rfl) ⟨158195, by rfl⟩ : syracuseStep 843709 = 316391) (by norm_num)
theorem B843797 : Blo 499793 843797 := bbase (se 6 (by rfl) ⟨19776, by rfl⟩ : syracuseStep 843797 = 39553) (by norm_num)
theorem B1925141 : Blo 499793 1925141 := bbase (se 6 (by rfl) ⟨45120, by rfl⟩ : syracuseStep 1925141 = 90241) (by norm_num)
theorem B712757 : Blo 499793 712757 := bbase (se 5 (by rfl) ⟨33410, by rfl⟩ : syracuseStep 712757 = 66821) (by norm_num)
theorem B1269877 : Blo 499793 1269877 := bbase (se 5 (by rfl) ⟨59525, by rfl⟩ : syracuseStep 1269877 = 119051) (by norm_num)
theorem B712837 : Blo 499793 712837 := bbase (se 4 (by rfl) ⟨66828, by rfl⟩ : syracuseStep 712837 = 133657) (by norm_num)
theorem B843925 : Blo 499793 843925 := bbase (se 6 (by rfl) ⟨19779, by rfl⟩ : syracuseStep 843925 = 39559) (by norm_num)
theorem B1269989 : Blo 499793 1269989 := bbase (se 4 (by rfl) ⟨119061, by rfl⟩ : syracuseStep 1269989 = 238123) (by norm_num)
theorem B844013 : Blo 499793 844013 := bbase (se 3 (by rfl) ⟨158252, by rfl⟩ : syracuseStep 844013 = 316505) (by norm_num)
theorem B712957 : Blo 499793 712957 := bbase (se 3 (by rfl) ⟨133679, by rfl⟩ : syracuseStep 712957 = 267359) (by norm_num)
theorem B1696085 : Blo 499793 1696085 := bbase (se 10 (by rfl) ⟨2484, by rfl⟩ : syracuseStep 1696085 = 4969) (by norm_num)
theorem B713053 : Blo 499793 713053 := bbase (se 3 (by rfl) ⟨133697, by rfl⟩ : syracuseStep 713053 = 267395) (by norm_num)
theorem B844141 : Blo 499793 844141 := bbase (se 3 (by rfl) ⟨158276, by rfl⟩ : syracuseStep 844141 = 316553) (by norm_num)
theorem B4809077 : Blo 499793 4809077 := bbase (se 5 (by rfl) ⟨225425, by rfl⟩ : syracuseStep 4809077 = 450851) (by norm_num)
theorem B1270181 : Blo 499793 1270181 := bbase (se 4 (by rfl) ⟨119079, by rfl⟩ : syracuseStep 1270181 = 238159) (by norm_num)
theorem B844229 : Blo 499793 844229 := bbase (se 4 (by rfl) ⟨79146, by rfl⟩ : syracuseStep 844229 = 158293) (by norm_num)
theorem B1434149 : Blo 499793 1434149 := bbase (se 4 (by rfl) ⟨134451, by rfl⟩ : syracuseStep 1434149 = 268903) (by norm_num)
theorem B844357 : Blo 499793 844357 := bbase (se 4 (by rfl) ⟨79158, by rfl⟩ : syracuseStep 844357 = 158317) (by norm_num)
theorem B1073749 : Blo 499793 1073749 := bbase (se 8 (by rfl) ⟨6291, by rfl⟩ : syracuseStep 1073749 = 12583) (by norm_num)
theorem B844445 : Blo 499793 844445 := bbase (se 3 (by rfl) ⟨158333, by rfl⟩ : syracuseStep 844445 = 316667) (by norm_num)
theorem B2548421 : Blo 499793 2548421 := bbase (se 4 (by rfl) ⟨238914, by rfl⟩ : syracuseStep 2548421 = 477829) (by norm_num)
theorem B1270525 : Blo 499793 1270525 := bbase (se 3 (by rfl) ⟨238223, by rfl⟩ : syracuseStep 1270525 = 476447) (by norm_num)
theorem B1696517 : Blo 499793 1696517 := bbase (se 4 (by rfl) ⟨159048, by rfl⟩ : syracuseStep 1696517 = 318097) (by norm_num)
theorem B844573 : Blo 499793 844573 := bbase (se 3 (by rfl) ⟨158357, by rfl⟩ : syracuseStep 844573 = 316715) (by norm_num)
theorem B713549 : Blo 499793 713549 := bbase (se 3 (by rfl) ⟨133790, by rfl⟩ : syracuseStep 713549 = 267581) (by norm_num)
theorem B1270637 : Blo 499793 1270637 := bbase (se 3 (by rfl) ⟨238244, by rfl⟩ : syracuseStep 1270637 = 476489) (by norm_num)
theorem B844661 : Blo 499793 844661 := bbase (se 5 (by rfl) ⟨39593, by rfl⟩ : syracuseStep 844661 = 79187) (by norm_num)
theorem B1434581 : Blo 499793 1434581 := bbase (se 7 (by rfl) ⟨16811, by rfl⟩ : syracuseStep 1434581 = 33623) (by norm_num)
theorem B844789 : Blo 499793 844789 := bbase (se 5 (by rfl) ⟨39599, by rfl⟩ : syracuseStep 844789 = 79199) (by norm_num)
theorem B1270829 : Blo 499793 1270829 := bbase (se 3 (by rfl) ⟨238280, by rfl⟩ : syracuseStep 1270829 = 476561) (by norm_num)
theorem B844877 : Blo 499793 844877 := bbase (se 3 (by rfl) ⟨158414, by rfl⟩ : syracuseStep 844877 = 316829) (by norm_num)
theorem B1696949 : Blo 499793 1696949 := bbase (se 5 (by rfl) ⟨79544, by rfl⟩ : syracuseStep 1696949 = 159089) (by norm_num)
theorem B845005 : Blo 499793 845005 := bbase (se 3 (by rfl) ⟨158438, by rfl⟩ : syracuseStep 845005 = 316877) (by norm_num)
theorem B845093 : Blo 499793 845093 := bbase (se 4 (by rfl) ⟨79227, by rfl⟩ : syracuseStep 845093 = 158455) (by norm_num)
theorem B714101 : Blo 499793 714101 := bbase (se 5 (by rfl) ⟨33473, by rfl⟩ : syracuseStep 714101 = 66947) (by norm_num)
theorem B1271173 : Blo 499793 1271173 := bbase (se 4 (by rfl) ⟨119172, by rfl⟩ : syracuseStep 1271173 = 238345) (by norm_num)
theorem B845221 : Blo 499793 845221 := bbase (se 4 (by rfl) ⟨79239, by rfl⟩ : syracuseStep 845221 = 158479) (by norm_num)
theorem B1074637 : Blo 499793 1074637 := bbase (se 3 (by rfl) ⟨201494, by rfl⟩ : syracuseStep 1074637 = 402989) (by norm_num)
theorem B1271285 : Blo 499793 1271285 := bbase (se 5 (by rfl) ⟨59591, by rfl⟩ : syracuseStep 1271285 = 119183) (by norm_num)
theorem B845309 : Blo 499793 845309 := bbase (se 3 (by rfl) ⟨158495, by rfl⟩ : syracuseStep 845309 = 316991) (by norm_num)
theorem B4285973 : Blo 499793 4285973 := bbase (se 6 (by rfl) ⟨100452, by rfl⟩ : syracuseStep 4285973 = 200905) (by norm_num)
theorem B1697381 : Blo 499793 1697381 := bbase (se 4 (by rfl) ⟨159129, by rfl⟩ : syracuseStep 1697381 = 318259) (by norm_num)
theorem B845437 : Blo 499793 845437 := bbase (se 3 (by rfl) ⟨158519, by rfl⟩ : syracuseStep 845437 = 317039) (by norm_num)
theorem B1271477 : Blo 499793 1271477 := bbase (se 5 (by rfl) ⟨59600, by rfl⟩ : syracuseStep 1271477 = 119201) (by norm_num)
theorem B845525 : Blo 499793 845525 := bbase (se 7 (by rfl) ⟨9908, by rfl⟩ : syracuseStep 845525 = 19817) (by norm_num)
theorem B1173253 : Blo 499793 1173253 := bbase (se 4 (by rfl) ⟨109992, by rfl⟩ : syracuseStep 1173253 = 219985) (by norm_num)
theorem B1206085 : Blo 499793 1206085 := bbase (se 4 (by rfl) ⟨113070, by rfl⟩ : syracuseStep 1206085 = 226141) (by norm_num)
theorem B845653 : Blo 499793 845653 := bbase (se 9 (by rfl) ⟨2477, by rfl⟩ : syracuseStep 845653 = 4955) (by norm_num)
theorem B2713429 : Blo 499793 2713429 := bbase (se 9 (by rfl) ⟨7949, by rfl⟩ : syracuseStep 2713429 = 15899) (by norm_num)
theorem B845741 : Blo 499793 845741 := bbase (se 3 (by rfl) ⟨158576, by rfl⟩ : syracuseStep 845741 = 317153) (by norm_num)
theorem B1075133 : Blo 499793 1075133 := bbase (se 3 (by rfl) ⟨201587, by rfl⟩ : syracuseStep 1075133 = 403175) (by norm_num)
theorem B2549717 : Blo 499793 2549717 := bbase (se 7 (by rfl) ⟨29879, by rfl⟩ : syracuseStep 2549717 = 59759) (by norm_num)
theorem B1271821 : Blo 499793 1271821 := bbase (se 3 (by rfl) ⟨238466, by rfl⟩ : syracuseStep 1271821 = 476933) (by norm_num)
theorem B1697813 : Blo 499793 1697813 := bbase (se 6 (by rfl) ⟨39792, by rfl⟩ : syracuseStep 1697813 = 79585) (by norm_num)
theorem B845869 : Blo 499793 845869 := bbase (se 3 (by rfl) ⟨158600, by rfl⟩ : syracuseStep 845869 = 317201) (by norm_num)
theorem B714853 : Blo 499793 714853 := bbase (se 4 (by rfl) ⟨67017, by rfl⟩ : syracuseStep 714853 = 134035) (by norm_num)
theorem B1271933 : Blo 499793 1271933 := bbase (se 3 (by rfl) ⟨238487, by rfl⟩ : syracuseStep 1271933 = 476975) (by norm_num)
theorem B845957 : Blo 499793 845957 := bbase (se 4 (by rfl) ⟨79308, by rfl⟩ : syracuseStep 845957 = 158617) (by norm_num)
theorem B1632421 : Blo 499793 1632421 := bbase (se 4 (by rfl) ⟨153039, by rfl⟩ : syracuseStep 1632421 = 306079) (by norm_num)
theorem B846085 : Blo 499793 846085 := bbase (se 4 (by rfl) ⟨79320, by rfl⟩ : syracuseStep 846085 = 158641) (by norm_num)
theorem B1272125 : Blo 499793 1272125 := bbase (se 3 (by rfl) ⟨238523, by rfl⟩ : syracuseStep 1272125 = 477047) (by norm_num)
theorem B715093 : Blo 499793 715093 := bbase (se 10 (by rfl) ⟨1047, by rfl⟩ : syracuseStep 715093 = 2095) (by norm_num)
theorem B846173 : Blo 499793 846173 := bbase (se 3 (by rfl) ⟨158657, by rfl⟩ : syracuseStep 846173 = 317315) (by norm_num)
theorem B1206701 : Blo 499793 1206701 := bbase (se 3 (by rfl) ⟨226256, by rfl⟩ : syracuseStep 1206701 = 452513) (by norm_num)
theorem B1698245 : Blo 499793 1698245 := bbase (se 4 (by rfl) ⟨159210, by rfl⟩ : syracuseStep 1698245 = 318421) (by norm_num)
theorem B846301 : Blo 499793 846301 := bbase (se 3 (by rfl) ⟨158681, by rfl⟩ : syracuseStep 846301 = 317363) (by norm_num)
theorem B846389 : Blo 499793 846389 := bbase (se 5 (by rfl) ⟨39674, by rfl⟩ : syracuseStep 846389 = 79349) (by norm_num)
theorem B2419301 : Blo 499793 2419301 := bbase (se 4 (by rfl) ⟨226809, by rfl⟩ : syracuseStep 2419301 = 453619) (by norm_num)
theorem B1272469 : Blo 499793 1272469 := bbase (se 6 (by rfl) ⟨29823, by rfl⟩ : syracuseStep 1272469 = 59647) (by norm_num)
theorem B846517 : Blo 499793 846517 := bbase (se 5 (by rfl) ⟨39680, by rfl⟩ : syracuseStep 846517 = 79361) (by norm_num)
theorem B1141445 : Blo 499793 1141445 := bbase (se 4 (by rfl) ⟨107010, by rfl⟩ : syracuseStep 1141445 = 214021) (by norm_num)
theorem B1207037 : Blo 499793 1207037 := bbase (se 3 (by rfl) ⟨226319, by rfl⟩ : syracuseStep 1207037 = 452639) (by norm_num)
theorem B1272581 : Blo 499793 1272581 := bbase (se 4 (by rfl) ⟨119304, by rfl⟩ : syracuseStep 1272581 = 238609) (by norm_num)
theorem B846605 : Blo 499793 846605 := bbase (se 3 (by rfl) ⟨158738, by rfl⟩ : syracuseStep 846605 = 317477) (by norm_num)
theorem B1698677 : Blo 499793 1698677 := bbase (se 5 (by rfl) ⟨79625, by rfl⟩ : syracuseStep 1698677 = 159251) (by norm_num)
theorem B715645 : Blo 499793 715645 := bbase (se 3 (by rfl) ⟨134183, by rfl⟩ : syracuseStep 715645 = 268367) (by norm_num)
theorem B846733 : Blo 499793 846733 := bbase (se 3 (by rfl) ⟨158762, by rfl⟩ : syracuseStep 846733 = 317525) (by norm_num)
theorem B5696405 : Blo 499793 5696405 := bbase (se 6 (by rfl) ⟨133509, by rfl⟩ : syracuseStep 5696405 = 267019) (by norm_num)
theorem B1272773 : Blo 499793 1272773 := bbase (se 4 (by rfl) ⟨119322, by rfl⟩ : syracuseStep 1272773 = 238645) (by norm_num)
theorem B846821 : Blo 499793 846821 := bbase (se 4 (by rfl) ⟨79389, by rfl⟩ : syracuseStep 846821 = 158779) (by norm_num)
theorem B846949 : Blo 499793 846949 := bbase (se 4 (by rfl) ⟨79401, by rfl⟩ : syracuseStep 846949 = 158803) (by norm_num)
theorem B1207429 : Blo 499793 1207429 := bbase (se 4 (by rfl) ⟨113196, by rfl⟩ : syracuseStep 1207429 = 226393) (by norm_num)
theorem B847037 : Blo 499793 847037 := bbase (se 3 (by rfl) ⟨158819, by rfl⟩ : syracuseStep 847037 = 317639) (by norm_num)
theorem B715981 : Blo 499793 715981 := bbase (se 3 (by rfl) ⟨134246, by rfl⟩ : syracuseStep 715981 = 268493) (by norm_num)
theorem B1273117 : Blo 499793 1273117 := bbase (se 3 (by rfl) ⟨238709, by rfl⟩ : syracuseStep 1273117 = 477419) (by norm_num)
theorem B1699109 : Blo 499793 1699109 := bbase (se 4 (by rfl) ⟨159291, by rfl⟩ : syracuseStep 1699109 = 318583) (by norm_num)
theorem B847165 : Blo 499793 847165 := bbase (se 3 (by rfl) ⟨158843, by rfl⟩ : syracuseStep 847165 = 317687) (by norm_num)
theorem B552253 : Blo 499793 552253 := bbase (se 3 (by rfl) ⟨103547, by rfl⟩ : syracuseStep 552253 = 207095) (by norm_num)
theorem B1273229 : Blo 499793 1273229 := bbase (se 3 (by rfl) ⟨238730, by rfl⟩ : syracuseStep 1273229 = 477461) (by norm_num)
theorem B847253 : Blo 499793 847253 := bbase (se 6 (by rfl) ⟨19857, by rfl⟩ : syracuseStep 847253 = 39715) (by norm_num)
theorem B716197 : Blo 499793 716197 := bbase (se 4 (by rfl) ⟨67143, by rfl⟩ : syracuseStep 716197 = 134287) (by norm_num)
theorem B847381 : Blo 499793 847381 := bbase (se 6 (by rfl) ⟨19860, by rfl⟩ : syracuseStep 847381 = 39721) (by norm_num)
theorem B1273421 : Blo 499793 1273421 := bbase (se 3 (by rfl) ⟨238766, by rfl⟩ : syracuseStep 1273421 = 477533) (by norm_num)
theorem B847469 : Blo 499793 847469 := bbase (se 3 (by rfl) ⟨158900, by rfl⟩ : syracuseStep 847469 = 317801) (by norm_num)
theorem B1699541 : Blo 499793 1699541 := bbase (se 7 (by rfl) ⟨19916, by rfl⟩ : syracuseStep 1699541 = 39833) (by norm_num)
theorem B847597 : Blo 499793 847597 := bbase (se 3 (by rfl) ⟨158924, by rfl⟩ : syracuseStep 847597 = 317849) (by norm_num)
theorem B716573 : Blo 499793 716573 := bbase (se 3 (by rfl) ⟨134357, by rfl⟩ : syracuseStep 716573 = 268715) (by norm_num)
theorem B847685 : Blo 499793 847685 := bbase (se 4 (by rfl) ⟨79470, by rfl⟩ : syracuseStep 847685 = 158941) (by norm_num)
theorem B2420549 : Blo 499793 2420549 := bbase (se 4 (by rfl) ⟨226926, by rfl⟩ : syracuseStep 2420549 = 453853) (by norm_num)
theorem B1273765 : Blo 499793 1273765 := bbase (se 4 (by rfl) ⟨119415, by rfl⟩ : syracuseStep 1273765 = 238831) (by norm_num)
theorem B847813 : Blo 499793 847813 := bbase (se 4 (by rfl) ⟨79482, by rfl⟩ : syracuseStep 847813 = 158965) (by norm_num)
theorem B1273877 : Blo 499793 1273877 := bbase (se 6 (by rfl) ⟨29856, by rfl⟩ : syracuseStep 1273877 = 59713) (by norm_num)
theorem B847901 : Blo 499793 847901 := bbase (se 3 (by rfl) ⟨158981, by rfl⟩ : syracuseStep 847901 = 317963) (by norm_num)
theorem B749693 : Blo 499793 749693 := bbase (se 3 (by rfl) ⟨140567, by rfl⟩ : syracuseStep 749693 = 281135) (by norm_num)
theorem B1699973 : Blo 499793 1699973 := bbase (se 4 (by rfl) ⟨159372, by rfl⟩ : syracuseStep 1699973 = 318745) (by norm_num)
theorem B749717 : Blo 499793 749717 := bbase (se 6 (by rfl) ⟨17571, by rfl⟩ : syracuseStep 749717 = 35143) (by norm_num)
theorem B848029 : Blo 499793 848029 := bbase (se 3 (by rfl) ⟨159005, by rfl⟩ : syracuseStep 848029 = 318011) (by norm_num)
theorem B749741 : Blo 499793 749741 := bbase (se 3 (by rfl) ⟨140576, by rfl⟩ : syracuseStep 749741 = 281153) (by norm_num)
theorem B749765 : Blo 499793 749765 := bbase (se 4 (by rfl) ⟨70290, by rfl⟩ : syracuseStep 749765 = 140581) (by norm_num)
theorem B1274069 : Blo 499793 1274069 := bbase (se 7 (by rfl) ⟨14930, by rfl⟩ : syracuseStep 1274069 = 29861) (by norm_num)
theorem B749789 : Blo 499793 749789 := bbase (se 3 (by rfl) ⟨140585, by rfl⟩ : syracuseStep 749789 = 281171) (by norm_num)
theorem B749813 : Blo 499793 749813 := bbase (se 5 (by rfl) ⟨35147, by rfl⟩ : syracuseStep 749813 = 70295) (by norm_num)
theorem B848117 : Blo 499793 848117 := bbase (se 5 (by rfl) ⟨39755, by rfl⟩ : syracuseStep 848117 = 79511) (by norm_num)
theorem B749837 : Blo 499793 749837 := bbase (se 3 (by rfl) ⟨140594, by rfl⟩ : syracuseStep 749837 = 281189) (by norm_num)
theorem B6418709 : Blo 499793 6418709 := bbase (se 6 (by rfl) ⟨150438, by rfl⟩ : syracuseStep 6418709 = 300877) (by norm_num)
theorem B749861 : Blo 499793 749861 := bbase (se 4 (by rfl) ⟨70299, by rfl⟩ : syracuseStep 749861 = 140599) (by norm_num)
theorem B749885 : Blo 499793 749885 := bbase (se 3 (by rfl) ⟨140603, by rfl⟩ : syracuseStep 749885 = 281207) (by norm_num)
theorem B782669 : Blo 499793 782669 := bbase (se 3 (by rfl) ⟨146750, by rfl⟩ : syracuseStep 782669 = 293501) (by norm_num)
theorem B749909 : Blo 499793 749909 := bbase (se 10 (by rfl) ⟨1098, by rfl⟩ : syracuseStep 749909 = 2197) (by norm_num)
theorem B3207509 : Blo 499793 3207509 := bbase (se 10 (by rfl) ⟨4698, by rfl⟩ : syracuseStep 3207509 = 9397) (by norm_num)
theorem B749933 : Blo 499793 749933 := bbase (se 3 (by rfl) ⟨140612, by rfl⟩ : syracuseStep 749933 = 281225) (by norm_num)
theorem B848245 : Blo 499793 848245 := bbase (se 5 (by rfl) ⟨39761, by rfl⟩ : syracuseStep 848245 = 79523) (by norm_num)
theorem B749957 : Blo 499793 749957 := bbase (se 4 (by rfl) ⟨70308, by rfl⟩ : syracuseStep 749957 = 140617) (by norm_num)
theorem B749981 : Blo 499793 749981 := bbase (se 3 (by rfl) ⟨140621, by rfl⟩ : syracuseStep 749981 = 281243) (by norm_num)
theorem B1143197 : Blo 499793 1143197 := bbase (se 3 (by rfl) ⟨214349, by rfl⟩ : syracuseStep 1143197 = 428699) (by norm_num)
theorem B750005 : Blo 499793 750005 := bbase (se 5 (by rfl) ⟨35156, by rfl⟩ : syracuseStep 750005 = 70313) (by norm_num)
theorem B4288949 : Blo 499793 4288949 := bbase (se 5 (by rfl) ⟨201044, by rfl⟩ : syracuseStep 4288949 = 402089) (by norm_num)
theorem B750029 : Blo 499793 750029 := bbase (se 3 (by rfl) ⟨140630, by rfl⟩ : syracuseStep 750029 = 281261) (by norm_num)
theorem B848333 : Blo 499793 848333 := bbase (se 3 (by rfl) ⟨159062, by rfl⟩ : syracuseStep 848333 = 318125) (by norm_num)
theorem B750053 : Blo 499793 750053 := bbase (se 4 (by rfl) ⟨70317, by rfl⟩ : syracuseStep 750053 = 140635) (by norm_num)
theorem B750077 : Blo 499793 750077 := bbase (se 3 (by rfl) ⟨140639, by rfl⟩ : syracuseStep 750077 = 281279) (by norm_num)
theorem B750101 : Blo 499793 750101 := bbase (se 6 (by rfl) ⟨17580, by rfl⟩ : syracuseStep 750101 = 35161) (by norm_num)
theorem B750125 : Blo 499793 750125 := bbase (se 3 (by rfl) ⟨140648, by rfl⟩ : syracuseStep 750125 = 281297) (by norm_num)
theorem B1274413 : Blo 499793 1274413 := bbase (se 3 (by rfl) ⟨238952, by rfl⟩ : syracuseStep 1274413 = 477905) (by norm_num)
theorem B750149 : Blo 499793 750149 := bbase (se 4 (by rfl) ⟨70326, by rfl⟩ : syracuseStep 750149 = 140653) (by norm_num)
theorem B848461 : Blo 499793 848461 := bbase (se 3 (by rfl) ⟨159086, by rfl⟩ : syracuseStep 848461 = 318173) (by norm_num)
theorem B750173 : Blo 499793 750173 := bbase (se 3 (by rfl) ⟨140657, by rfl⟩ : syracuseStep 750173 = 281315) (by norm_num)
theorem B750197 : Blo 499793 750197 := bbase (se 5 (by rfl) ⟨35165, by rfl⟩ : syracuseStep 750197 = 70331) (by norm_num)
theorem B750221 : Blo 499793 750221 := bbase (se 3 (by rfl) ⟨140666, by rfl⟩ : syracuseStep 750221 = 281333) (by norm_num)
theorem B1274525 : Blo 499793 1274525 := bbase (se 3 (by rfl) ⟨238973, by rfl⟩ : syracuseStep 1274525 = 477947) (by norm_num)
theorem B750245 : Blo 499793 750245 := bbase (se 4 (by rfl) ⟨70335, by rfl⟩ : syracuseStep 750245 = 140671) (by norm_num)
theorem B848549 : Blo 499793 848549 := bbase (se 4 (by rfl) ⟨79551, by rfl⟩ : syracuseStep 848549 = 159103) (by norm_num)
theorem B750269 : Blo 499793 750269 := bbase (se 3 (by rfl) ⟨140675, by rfl⟩ : syracuseStep 750269 = 281351) (by norm_num)
theorem B750293 : Blo 499793 750293 := bbase (se 7 (by rfl) ⟨8792, by rfl⟩ : syracuseStep 750293 = 17585) (by norm_num)
theorem B750317 : Blo 499793 750317 := bbase (se 3 (by rfl) ⟨140684, by rfl⟩ : syracuseStep 750317 = 281369) (by norm_num)
theorem B750341 : Blo 499793 750341 := bbase (se 4 (by rfl) ⟨70344, by rfl⟩ : syracuseStep 750341 = 140689) (by norm_num)
theorem B750365 : Blo 499793 750365 := bbase (se 3 (by rfl) ⟨140693, by rfl⟩ : syracuseStep 750365 = 281387) (by norm_num)
theorem B848677 : Blo 499793 848677 := bbase (se 4 (by rfl) ⟨79563, by rfl⟩ : syracuseStep 848677 = 159127) (by norm_num)
theorem B750389 : Blo 499793 750389 := bbase (se 5 (by rfl) ⟨35174, by rfl⟩ : syracuseStep 750389 = 70349) (by norm_num)
theorem B750413 : Blo 499793 750413 := bbase (se 3 (by rfl) ⟨140702, by rfl⟩ : syracuseStep 750413 = 281405) (by norm_num)
theorem B1274717 : Blo 499793 1274717 := bbase (se 3 (by rfl) ⟨239009, by rfl⟩ : syracuseStep 1274717 = 478019) (by norm_num)
theorem B750437 : Blo 499793 750437 := bbase (se 4 (by rfl) ⟨70353, by rfl⟩ : syracuseStep 750437 = 140707) (by norm_num)
theorem B750461 : Blo 499793 750461 := bbase (se 3 (by rfl) ⟨140711, by rfl⟩ : syracuseStep 750461 = 281423) (by norm_num)
theorem B848765 : Blo 499793 848765 := bbase (se 3 (by rfl) ⟨159143, by rfl⟩ : syracuseStep 848765 = 318287) (by norm_num)
theorem B750485 : Blo 499793 750485 := bbase (se 6 (by rfl) ⟨17589, by rfl⟩ : syracuseStep 750485 = 35179) (by norm_num)
theorem B1930133 : Blo 499793 1930133 := bbase (se 6 (by rfl) ⟨45237, by rfl⟩ : syracuseStep 1930133 = 90475) (by norm_num)
theorem B750509 : Blo 499793 750509 := bbase (se 3 (by rfl) ⟨140720, by rfl⟩ : syracuseStep 750509 = 281441) (by norm_num)
theorem B750533 : Blo 499793 750533 := bbase (se 4 (by rfl) ⟨70362, by rfl⟩ : syracuseStep 750533 = 140725) (by norm_num)
theorem B750557 : Blo 499793 750557 := bbase (se 3 (by rfl) ⟨140729, by rfl⟩ : syracuseStep 750557 = 281459) (by norm_num)
theorem B750581 : Blo 499793 750581 := bbase (se 5 (by rfl) ⟨35183, by rfl⟩ : syracuseStep 750581 = 70367) (by norm_num)
theorem B848893 : Blo 499793 848893 := bbase (se 3 (by rfl) ⟨159167, by rfl⟩ : syracuseStep 848893 = 318335) (by norm_num)
theorem B750605 : Blo 499793 750605 := bbase (se 3 (by rfl) ⟨140738, by rfl⟩ : syracuseStep 750605 = 281477) (by norm_num)
theorem B750629 : Blo 499793 750629 := bbase (se 4 (by rfl) ⟨70371, by rfl⟩ : syracuseStep 750629 = 140743) (by norm_num)
theorem B750653 : Blo 499793 750653 := bbase (se 3 (by rfl) ⟨140747, by rfl⟩ : syracuseStep 750653 = 281495) (by norm_num)
theorem B750677 : Blo 499793 750677 := bbase (se 8 (by rfl) ⟨4398, by rfl⟩ : syracuseStep 750677 = 8797) (by norm_num)
theorem B848981 : Blo 499793 848981 := bbase (se 8 (by rfl) ⟨4974, by rfl⟩ : syracuseStep 848981 = 9949) (by norm_num)
theorem B750701 : Blo 499793 750701 := bbase (se 3 (by rfl) ⟨140756, by rfl⟩ : syracuseStep 750701 = 281513) (by norm_num)
theorem B750725 : Blo 499793 750725 := bbase (se 4 (by rfl) ⟨70380, by rfl⟩ : syracuseStep 750725 = 140761) (by norm_num)
theorem B750749 : Blo 499793 750749 := bbase (se 3 (by rfl) ⟨140765, by rfl⟩ : syracuseStep 750749 = 281531) (by norm_num)
theorem B750773 : Blo 499793 750773 := bbase (se 5 (by rfl) ⟨35192, by rfl⟩ : syracuseStep 750773 = 70385) (by norm_num)
theorem B1275061 : Blo 499793 1275061 := bbase (se 5 (by rfl) ⟨59768, by rfl⟩ : syracuseStep 1275061 = 119537) (by norm_num)
theorem B750797 : Blo 499793 750797 := bbase (se 3 (by rfl) ⟨140774, by rfl⟩ : syracuseStep 750797 = 281549) (by norm_num)
theorem B849109 : Blo 499793 849109 := bbase (se 7 (by rfl) ⟨9950, by rfl⟩ : syracuseStep 849109 = 19901) (by norm_num)
theorem B750821 : Blo 499793 750821 := bbase (se 4 (by rfl) ⟨70389, by rfl⟩ : syracuseStep 750821 = 140779) (by norm_num)
theorem B1144037 : Blo 499793 1144037 := bbase (se 4 (by rfl) ⟨107253, by rfl⟩ : syracuseStep 1144037 = 214507) (by norm_num)
theorem B750845 : Blo 499793 750845 := bbase (se 3 (by rfl) ⟨140783, by rfl⟩ : syracuseStep 750845 = 281567) (by norm_num)
theorem B1602821 : Blo 499793 1602821 := bbase (se 4 (by rfl) ⟨150264, by rfl⟩ : syracuseStep 1602821 = 300529) (by norm_num)
theorem B1307909 : Blo 499793 1307909 := bbase (se 4 (by rfl) ⟨122616, by rfl⟩ : syracuseStep 1307909 = 245233) (by norm_num)
theorem B750869 : Blo 499793 750869 := bbase (se 6 (by rfl) ⟨17598, by rfl⟩ : syracuseStep 750869 = 35197) (by norm_num)
theorem B1275173 : Blo 499793 1275173 := bbase (se 4 (by rfl) ⟨119547, by rfl⟩ : syracuseStep 1275173 = 239095) (by norm_num)
theorem B750893 : Blo 499793 750893 := bbase (se 3 (by rfl) ⟨140792, by rfl⟩ : syracuseStep 750893 = 281585) (by norm_num)
theorem B849197 : Blo 499793 849197 := bbase (se 3 (by rfl) ⟨159224, by rfl⟩ : syracuseStep 849197 = 318449) (by norm_num)
theorem B750917 : Blo 499793 750917 := bbase (se 4 (by rfl) ⟨70398, by rfl⟩ : syracuseStep 750917 = 140797) (by norm_num)
theorem B3437909 : Blo 499793 3437909 := bbase (se 13 (by rfl) ⟨629, by rfl⟩ : syracuseStep 3437909 = 1259) (by norm_num)
theorem B750941 : Blo 499793 750941 := bbase (se 3 (by rfl) ⟨140801, by rfl⟩ : syracuseStep 750941 = 281603) (by norm_num)
theorem B750965 : Blo 499793 750965 := bbase (se 5 (by rfl) ⟨35201, by rfl⟩ : syracuseStep 750965 = 70403) (by norm_num)
theorem B750989 : Blo 499793 750989 := bbase (se 3 (by rfl) ⟨140810, by rfl⟩ : syracuseStep 750989 = 281621) (by norm_num)
theorem B751013 : Blo 499793 751013 := bbase (se 4 (by rfl) ⟨70407, by rfl⟩ : syracuseStep 751013 = 140815) (by norm_num)
theorem B849325 : Blo 499793 849325 := bbase (se 3 (by rfl) ⟨159248, by rfl⟩ : syracuseStep 849325 = 318497) (by norm_num)
theorem B751037 : Blo 499793 751037 := bbase (se 3 (by rfl) ⟨140819, by rfl⟩ : syracuseStep 751037 = 281639) (by norm_num)
theorem B751061 : Blo 499793 751061 := bbase (se 7 (by rfl) ⟨8801, by rfl⟩ : syracuseStep 751061 = 17603) (by norm_num)
theorem B751085 : Blo 499793 751085 := bbase (se 3 (by rfl) ⟨140828, by rfl⟩ : syracuseStep 751085 = 281657) (by norm_num)
theorem B751109 : Blo 499793 751109 := bbase (se 4 (by rfl) ⟨70416, by rfl⟩ : syracuseStep 751109 = 140833) (by norm_num)
theorem B849413 : Blo 499793 849413 := bbase (se 4 (by rfl) ⟨79632, by rfl⟩ : syracuseStep 849413 = 159265) (by norm_num)
theorem B751133 : Blo 499793 751133 := bbase (se 3 (by rfl) ⟨140837, by rfl⟩ : syracuseStep 751133 = 281675) (by norm_num)
theorem B751157 : Blo 499793 751157 := bbase (se 5 (by rfl) ⟨35210, by rfl⟩ : syracuseStep 751157 = 70421) (by norm_num)
theorem B751181 : Blo 499793 751181 := bbase (se 3 (by rfl) ⟨140846, by rfl⟩ : syracuseStep 751181 = 281693) (by norm_num)
theorem B751205 : Blo 499793 751205 := bbase (se 4 (by rfl) ⟨70425, by rfl⟩ : syracuseStep 751205 = 140851) (by norm_num)
theorem B751229 : Blo 499793 751229 := bbase (se 3 (by rfl) ⟨140855, by rfl⟩ : syracuseStep 751229 = 281711) (by norm_num)
theorem B849541 : Blo 499793 849541 := bbase (se 4 (by rfl) ⟨79644, by rfl⟩ : syracuseStep 849541 = 159289) (by norm_num)
theorem B751253 : Blo 499793 751253 := bbase (se 6 (by rfl) ⟨17607, by rfl⟩ : syracuseStep 751253 = 35215) (by norm_num)
theorem B751277 : Blo 499793 751277 := bbase (se 3 (by rfl) ⟨140864, by rfl⟩ : syracuseStep 751277 = 281729) (by norm_num)
theorem B751301 : Blo 499793 751301 := bbase (se 4 (by rfl) ⟨70434, by rfl⟩ : syracuseStep 751301 = 140869) (by norm_num)
theorem B784069 : Blo 499793 784069 := bbase (se 4 (by rfl) ⟨73506, by rfl⟩ : syracuseStep 784069 = 147013) (by norm_num)
theorem B751325 : Blo 499793 751325 := bbase (se 3 (by rfl) ⟨140873, by rfl⟩ : syracuseStep 751325 = 281747) (by norm_num)
theorem B849629 : Blo 499793 849629 := bbase (se 3 (by rfl) ⟨159305, by rfl⟩ : syracuseStep 849629 = 318611) (by norm_num)
theorem B751349 : Blo 499793 751349 := bbase (se 5 (by rfl) ⟨35219, by rfl⟩ : syracuseStep 751349 = 70439) (by norm_num)
theorem B751373 : Blo 499793 751373 := bbase (se 3 (by rfl) ⟨140882, by rfl⟩ : syracuseStep 751373 = 281765) (by norm_num)
theorem B2029349 : Blo 499793 2029349 := bbase (se 4 (by rfl) ⟨190251, by rfl⟩ : syracuseStep 2029349 = 380503) (by norm_num)
theorem B751397 : Blo 499793 751397 := bbase (se 4 (by rfl) ⟨70443, by rfl⟩ : syracuseStep 751397 = 140887) (by norm_num)
theorem B3143477 : Blo 499793 3143477 := bbase (se 5 (by rfl) ⟨147350, by rfl⟩ : syracuseStep 3143477 = 294701) (by norm_num)
theorem B751421 : Blo 499793 751421 := bbase (se 3 (by rfl) ⟨140891, by rfl⟩ : syracuseStep 751421 = 281783) (by norm_num)
theorem B751445 : Blo 499793 751445 := bbase (se 9 (by rfl) ⟨2201, by rfl⟩ : syracuseStep 751445 = 4403) (by norm_num)
theorem B849757 : Blo 499793 849757 := bbase (se 3 (by rfl) ⟨159329, by rfl⟩ : syracuseStep 849757 = 318659) (by norm_num)
theorem B751469 : Blo 499793 751469 := bbase (se 3 (by rfl) ⟨140900, by rfl⟩ : syracuseStep 751469 = 281801) (by norm_num)
theorem B751493 : Blo 499793 751493 := bbase (se 4 (by rfl) ⟨70452, by rfl⟩ : syracuseStep 751493 = 140905) (by norm_num)
theorem B751517 : Blo 499793 751517 := bbase (se 3 (by rfl) ⟨140909, by rfl⟩ : syracuseStep 751517 = 281819) (by norm_num)
theorem B751541 : Blo 499793 751541 := bbase (se 5 (by rfl) ⟨35228, by rfl⟩ : syracuseStep 751541 = 70457) (by norm_num)
theorem B849845 : Blo 499793 849845 := bbase (se 5 (by rfl) ⟨39836, by rfl⟩ : syracuseStep 849845 = 79673) (by norm_num)
theorem B1898437 : Blo 499793 1898437 := bbase (se 4 (by rfl) ⟨177978, by rfl⟩ : syracuseStep 1898437 = 355957) (by norm_num)
theorem B751565 : Blo 499793 751565 := bbase (se 3 (by rfl) ⟨140918, by rfl⟩ : syracuseStep 751565 = 281837) (by norm_num)
theorem B751589 : Blo 499793 751589 := bbase (se 4 (by rfl) ⟨70461, by rfl⟩ : syracuseStep 751589 = 140923) (by norm_num)
theorem B751613 : Blo 499793 751613 := bbase (se 3 (by rfl) ⟨140927, by rfl⟩ : syracuseStep 751613 = 281855) (by norm_num)
theorem B3799061 : Blo 499793 3799061 := bbase (se 6 (by rfl) ⟨89040, by rfl⟩ : syracuseStep 3799061 = 178081) (by norm_num)
theorem B751637 : Blo 499793 751637 := bbase (se 6 (by rfl) ⟨17616, by rfl⟩ : syracuseStep 751637 = 35233) (by norm_num)
theorem B751661 : Blo 499793 751661 := bbase (se 3 (by rfl) ⟨140936, by rfl⟩ : syracuseStep 751661 = 281873) (by norm_num)
theorem B849973 : Blo 499793 849973 := bbase (se 5 (by rfl) ⟨39842, by rfl⟩ : syracuseStep 849973 = 79685) (by norm_num)
theorem B751685 : Blo 499793 751685 := bbase (se 4 (by rfl) ⟨70470, by rfl⟩ : syracuseStep 751685 = 140941) (by norm_num)
theorem B751709 : Blo 499793 751709 := bbase (se 3 (by rfl) ⟨140945, by rfl⟩ : syracuseStep 751709 = 281891) (by norm_num)
theorem B751733 : Blo 499793 751733 := bbase (se 5 (by rfl) ⟨35237, by rfl⟩ : syracuseStep 751733 = 70475) (by norm_num)
theorem B751757 : Blo 499793 751757 := bbase (se 3 (by rfl) ⟨140954, by rfl⟩ : syracuseStep 751757 = 281909) (by norm_num)
theorem B850061 : Blo 499793 850061 := bbase (se 3 (by rfl) ⟨159386, by rfl⟩ : syracuseStep 850061 = 318773) (by norm_num)
theorem B751781 : Blo 499793 751781 := bbase (se 4 (by rfl) ⟨70479, by rfl⟩ : syracuseStep 751781 = 140959) (by norm_num)
theorem B751805 : Blo 499793 751805 := bbase (se 3 (by rfl) ⟨140963, by rfl⟩ : syracuseStep 751805 = 281927) (by norm_num)
theorem B751829 : Blo 499793 751829 := bbase (se 7 (by rfl) ⟨8810, by rfl⟩ : syracuseStep 751829 = 17621) (by norm_num)
theorem B751853 : Blo 499793 751853 := bbase (se 3 (by rfl) ⟨140972, by rfl⟩ : syracuseStep 751853 = 281945) (by norm_num)
theorem B1898741 : Blo 499793 1898741 := bbase (se 5 (by rfl) ⟨89003, by rfl⟩ : syracuseStep 1898741 = 178007) (by norm_num)
theorem B751877 : Blo 499793 751877 := bbase (se 4 (by rfl) ⟨70488, by rfl⟩ : syracuseStep 751877 = 140977) (by norm_num)
theorem B751901 : Blo 499793 751901 := bbase (se 3 (by rfl) ⟨140981, by rfl⟩ : syracuseStep 751901 = 281963) (by norm_num)
theorem B751925 : Blo 499793 751925 := bbase (se 5 (by rfl) ⟨35246, by rfl⟩ : syracuseStep 751925 = 70493) (by norm_num)
theorem B751949 : Blo 499793 751949 := bbase (se 3 (by rfl) ⟨140990, by rfl⟩ : syracuseStep 751949 = 281981) (by norm_num)
theorem B751973 : Blo 499793 751973 := bbase (se 4 (by rfl) ⟨70497, by rfl⟩ : syracuseStep 751973 = 140995) (by norm_num)
theorem B751997 : Blo 499793 751997 := bbase (se 3 (by rfl) ⟨140999, by rfl⟩ : syracuseStep 751997 = 281999) (by norm_num)
theorem B752021 : Blo 499793 752021 := bbase (se 6 (by rfl) ⟨17625, by rfl⟩ : syracuseStep 752021 = 35251) (by norm_num)
theorem B752045 : Blo 499793 752045 := bbase (se 3 (by rfl) ⟨141008, by rfl⟩ : syracuseStep 752045 = 282017) (by norm_num)
theorem B752069 : Blo 499793 752069 := bbase (se 4 (by rfl) ⟨70506, by rfl⟩ : syracuseStep 752069 = 141013) (by norm_num)
theorem B752093 : Blo 499793 752093 := bbase (se 3 (by rfl) ⟨141017, by rfl⟩ : syracuseStep 752093 = 282035) (by norm_num)
theorem B752117 : Blo 499793 752117 := bbase (se 5 (by rfl) ⟨35255, by rfl⟩ : syracuseStep 752117 = 70511) (by norm_num)
theorem B752141 : Blo 499793 752141 := bbase (se 3 (by rfl) ⟨141026, by rfl⟩ : syracuseStep 752141 = 282053) (by norm_num)
theorem B752165 : Blo 499793 752165 := bbase (se 4 (by rfl) ⟨70515, by rfl⟩ : syracuseStep 752165 = 141031) (by norm_num)
theorem B752189 : Blo 499793 752189 := bbase (se 3 (by rfl) ⟨141035, by rfl⟩ : syracuseStep 752189 = 282071) (by norm_num)
theorem B752213 : Blo 499793 752213 := bbase (se 8 (by rfl) ⟨4407, by rfl⟩ : syracuseStep 752213 = 8815) (by norm_num)
theorem B752237 : Blo 499793 752237 := bbase (se 3 (by rfl) ⟨141044, by rfl⟩ : syracuseStep 752237 = 282089) (by norm_num)
theorem B752261 : Blo 499793 752261 := bbase (se 4 (by rfl) ⟨70524, by rfl⟩ : syracuseStep 752261 = 141049) (by norm_num)
theorem B752285 : Blo 499793 752285 := bbase (se 3 (by rfl) ⟨141053, by rfl⟩ : syracuseStep 752285 = 282107) (by norm_num)
theorem B752309 : Blo 499793 752309 := bbase (se 5 (by rfl) ⟨35264, by rfl⟩ : syracuseStep 752309 = 70529) (by norm_num)
theorem B752333 : Blo 499793 752333 := bbase (se 3 (by rfl) ⟨141062, by rfl⟩ : syracuseStep 752333 = 282125) (by norm_num)
theorem B752357 : Blo 499793 752357 := bbase (se 4 (by rfl) ⟨70533, by rfl⟩ : syracuseStep 752357 = 141067) (by norm_num)
theorem B2849525 : Blo 499793 2849525 := bbase (se 5 (by rfl) ⟨133571, by rfl⟩ : syracuseStep 2849525 = 267143) (by norm_num)
theorem B752381 : Blo 499793 752381 := bbase (se 3 (by rfl) ⟨141071, by rfl⟩ : syracuseStep 752381 = 282143) (by norm_num)
theorem B752405 : Blo 499793 752405 := bbase (se 6 (by rfl) ⟨17634, by rfl⟩ : syracuseStep 752405 = 35269) (by norm_num)
theorem B752429 : Blo 499793 752429 := bbase (se 3 (by rfl) ⟨141080, by rfl⟩ : syracuseStep 752429 = 282161) (by norm_num)
theorem B752453 : Blo 499793 752453 := bbase (se 4 (by rfl) ⟨70542, by rfl⟩ : syracuseStep 752453 = 141085) (by norm_num)
theorem B752477 : Blo 499793 752477 := bbase (se 3 (by rfl) ⟨141089, by rfl⟩ : syracuseStep 752477 = 282179) (by norm_num)
theorem B752501 : Blo 499793 752501 := bbase (se 5 (by rfl) ⟨35273, by rfl⟩ : syracuseStep 752501 = 70547) (by norm_num)
theorem B752525 : Blo 499793 752525 := bbase (se 3 (by rfl) ⟨141098, by rfl⟩ : syracuseStep 752525 = 282197) (by norm_num)
theorem B752549 : Blo 499793 752549 := bbase (se 4 (by rfl) ⟨70551, by rfl⟩ : syracuseStep 752549 = 141103) (by norm_num)
theorem B752573 : Blo 499793 752573 := bbase (se 3 (by rfl) ⟨141107, by rfl⟩ : syracuseStep 752573 = 282215) (by norm_num)
theorem B752597 : Blo 499793 752597 := bbase (se 7 (by rfl) ⟨8819, by rfl⟩ : syracuseStep 752597 = 17639) (by norm_num)
theorem B752621 : Blo 499793 752621 := bbase (se 3 (by rfl) ⟨141116, by rfl⟩ : syracuseStep 752621 = 282233) (by norm_num)
theorem B752645 : Blo 499793 752645 := bbase (se 4 (by rfl) ⟨70560, by rfl⟩ : syracuseStep 752645 = 141121) (by norm_num)
theorem B5405717 : Blo 499793 5405717 := bbase (se 6 (by rfl) ⟨126696, by rfl⟩ : syracuseStep 5405717 = 253393) (by norm_num)
theorem B752669 : Blo 499793 752669 := bbase (se 3 (by rfl) ⟨141125, by rfl⟩ : syracuseStep 752669 = 282251) (by norm_num)
theorem B752693 : Blo 499793 752693 := bbase (se 5 (by rfl) ⟨35282, by rfl⟩ : syracuseStep 752693 = 70565) (by norm_num)
theorem B752717 : Blo 499793 752717 := bbase (se 3 (by rfl) ⟨141134, by rfl⟩ : syracuseStep 752717 = 282269) (by norm_num)
theorem B949333 : Blo 499793 949333 := bbase (se 8 (by rfl) ⟨5562, by rfl⟩ : syracuseStep 949333 = 11125) (by norm_num)
theorem B752741 : Blo 499793 752741 := bbase (se 4 (by rfl) ⟨70569, by rfl⟩ : syracuseStep 752741 = 141139) (by norm_num)
theorem B752765 : Blo 499793 752765 := bbase (se 3 (by rfl) ⟨141143, by rfl⟩ : syracuseStep 752765 = 282287) (by norm_num)
theorem B752789 : Blo 499793 752789 := bbase (se 6 (by rfl) ⟨17643, by rfl⟩ : syracuseStep 752789 = 35287) (by norm_num)
theorem B883877 : Blo 499793 883877 := bbase (se 4 (by rfl) ⟨82863, by rfl⟩ : syracuseStep 883877 = 165727) (by norm_num)
theorem B752813 : Blo 499793 752813 := bbase (se 3 (by rfl) ⟨141152, by rfl⟩ : syracuseStep 752813 = 282305) (by norm_num)
theorem B752837 : Blo 499793 752837 := bbase (se 4 (by rfl) ⟨70578, by rfl⟩ : syracuseStep 752837 = 141157) (by norm_num)
theorem B752861 : Blo 499793 752861 := bbase (se 3 (by rfl) ⟨141161, by rfl⟩ : syracuseStep 752861 = 282323) (by norm_num)
theorem B949477 : Blo 499793 949477 := bbase (se 4 (by rfl) ⟨89013, by rfl⟩ : syracuseStep 949477 = 178027) (by norm_num)
theorem B752885 : Blo 499793 752885 := bbase (se 5 (by rfl) ⟨35291, by rfl⟩ : syracuseStep 752885 = 70583) (by norm_num)
theorem B2718965 : Blo 499793 2718965 := bbase (se 5 (by rfl) ⟨127451, by rfl⟩ : syracuseStep 2718965 = 254903) (by norm_num)
theorem B752909 : Blo 499793 752909 := bbase (se 3 (by rfl) ⟨141170, by rfl⟩ : syracuseStep 752909 = 282341) (by norm_num)
theorem B752933 : Blo 499793 752933 := bbase (se 4 (by rfl) ⟨70587, by rfl⟩ : syracuseStep 752933 = 141175) (by norm_num)
theorem B752957 : Blo 499793 752957 := bbase (se 3 (by rfl) ⟨141179, by rfl⟩ : syracuseStep 752957 = 282359) (by norm_num)
theorem B752981 : Blo 499793 752981 := bbase (se 11 (by rfl) ⟨551, by rfl⟩ : syracuseStep 752981 = 1103) (by norm_num)
theorem B753005 : Blo 499793 753005 := bbase (se 3 (by rfl) ⟨141188, by rfl⟩ : syracuseStep 753005 = 282377) (by norm_num)
theorem B949637 : Blo 499793 949637 := bbase (se 4 (by rfl) ⟨89028, by rfl⟩ : syracuseStep 949637 = 178057) (by norm_num)
theorem B753029 : Blo 499793 753029 := bbase (se 4 (by rfl) ⟨70596, by rfl⟩ : syracuseStep 753029 = 141193) (by norm_num)
theorem B753053 : Blo 499793 753053 := bbase (se 3 (by rfl) ⟨141197, by rfl⟩ : syracuseStep 753053 = 282395) (by norm_num)
theorem B753077 : Blo 499793 753077 := bbase (se 5 (by rfl) ⟨35300, by rfl⟩ : syracuseStep 753077 = 70601) (by norm_num)
theorem B753101 : Blo 499793 753101 := bbase (se 3 (by rfl) ⟨141206, by rfl⟩ : syracuseStep 753101 = 282413) (by norm_num)
theorem B5438933 : Blo 499793 5438933 := bbase (se 7 (by rfl) ⟨63737, by rfl⟩ : syracuseStep 5438933 = 127475) (by norm_num)
theorem B753125 : Blo 499793 753125 := bbase (se 4 (by rfl) ⟨70605, by rfl⟩ : syracuseStep 753125 = 141211) (by norm_num)
theorem B753149 : Blo 499793 753149 := bbase (se 3 (by rfl) ⟨141215, by rfl⟩ : syracuseStep 753149 = 282431) (by norm_num)
theorem B949781 : Blo 499793 949781 := bbase (se 6 (by rfl) ⟨22260, by rfl⟩ : syracuseStep 949781 = 44521) (by norm_num)
theorem B753173 : Blo 499793 753173 := bbase (se 6 (by rfl) ⟨17652, by rfl⟩ : syracuseStep 753173 = 35305) (by norm_num)
theorem B753197 : Blo 499793 753197 := bbase (se 3 (by rfl) ⟨141224, by rfl⟩ : syracuseStep 753197 = 282449) (by norm_num)
theorem B753221 : Blo 499793 753221 := bbase (se 4 (by rfl) ⟨70614, by rfl⟩ : syracuseStep 753221 = 141229) (by norm_num)
theorem B753245 : Blo 499793 753245 := bbase (se 3 (by rfl) ⟨141233, by rfl⟩ : syracuseStep 753245 = 282467) (by norm_num)
theorem B753269 : Blo 499793 753269 := bbase (se 5 (by rfl) ⟨35309, by rfl⟩ : syracuseStep 753269 = 70619) (by norm_num)
theorem B753293 : Blo 499793 753293 := bbase (se 3 (by rfl) ⟨141242, by rfl⟩ : syracuseStep 753293 = 282485) (by norm_num)
theorem B2293397 : Blo 499793 2293397 := bbase (se 6 (by rfl) ⟨53751, by rfl⟩ : syracuseStep 2293397 = 107503) (by norm_num)
theorem B753317 : Blo 499793 753317 := bbase (se 4 (by rfl) ⟨70623, by rfl⟩ : syracuseStep 753317 = 141247) (by norm_num)
theorem B753341 : Blo 499793 753341 := bbase (se 3 (by rfl) ⟨141251, by rfl⟩ : syracuseStep 753341 = 282503) (by norm_num)
theorem B753365 : Blo 499793 753365 := bbase (se 7 (by rfl) ⟨8828, by rfl⟩ : syracuseStep 753365 = 17657) (by norm_num)
theorem B753389 : Blo 499793 753389 := bbase (se 3 (by rfl) ⟨141260, by rfl⟩ : syracuseStep 753389 = 282521) (by norm_num)
theorem B753413 : Blo 499793 753413 := bbase (se 4 (by rfl) ⟨70632, by rfl⟩ : syracuseStep 753413 = 141265) (by norm_num)
theorem B753437 : Blo 499793 753437 := bbase (se 3 (by rfl) ⟨141269, by rfl⟩ : syracuseStep 753437 = 282539) (by norm_num)
theorem B950069 : Blo 499793 950069 := bbase (se 5 (by rfl) ⟨44534, by rfl⟩ : syracuseStep 950069 = 89069) (by norm_num)
theorem B1834805 : Blo 499793 1834805 := bbase (se 5 (by rfl) ⟨86006, by rfl⟩ : syracuseStep 1834805 = 172013) (by norm_num)
theorem B753461 : Blo 499793 753461 := bbase (se 5 (by rfl) ⟨35318, by rfl⟩ : syracuseStep 753461 = 70637) (by norm_num)
theorem B753485 : Blo 499793 753485 := bbase (se 3 (by rfl) ⟨141278, by rfl⟩ : syracuseStep 753485 = 282557) (by norm_num)
theorem B753509 : Blo 499793 753509 := bbase (se 4 (by rfl) ⟨70641, by rfl⟩ : syracuseStep 753509 = 141283) (by norm_num)
theorem B753533 : Blo 499793 753533 := bbase (se 3 (by rfl) ⟨141287, by rfl⟩ : syracuseStep 753533 = 282575) (by norm_num)
theorem B753557 : Blo 499793 753557 := bbase (se 6 (by rfl) ⟨17661, by rfl⟩ : syracuseStep 753557 = 35323) (by norm_num)
theorem B1146773 : Blo 499793 1146773 := bbase (se 6 (by rfl) ⟨26877, by rfl⟩ : syracuseStep 1146773 = 53755) (by norm_num)
theorem B753581 : Blo 499793 753581 := bbase (se 3 (by rfl) ⟨141296, by rfl⟩ : syracuseStep 753581 = 282593) (by norm_num)
theorem B753605 : Blo 499793 753605 := bbase (se 4 (by rfl) ⟨70650, by rfl⟩ : syracuseStep 753605 = 141301) (by norm_num)
theorem B950221 : Blo 499793 950221 := bbase (se 3 (by rfl) ⟨178166, by rfl⟩ : syracuseStep 950221 = 356333) (by norm_num)
theorem B753629 : Blo 499793 753629 := bbase (se 3 (by rfl) ⟨141305, by rfl⟩ : syracuseStep 753629 = 282611) (by norm_num)
theorem B2031605 : Blo 499793 2031605 := bbase (se 5 (by rfl) ⟨95231, by rfl⟩ : syracuseStep 2031605 = 190463) (by norm_num)
theorem B753653 : Blo 499793 753653 := bbase (se 5 (by rfl) ⟨35327, by rfl⟩ : syracuseStep 753653 = 70655) (by norm_num)
theorem B753665 : Blo 499793 753665 := bstep (se 2 (by rfl) ⟨282624, by rfl⟩ : syracuseStep 753665 = 565249) B565249
theorem B753683 : Blo 499793 753683 := bstep (se 1 (by rfl) ⟨565262, by rfl⟩ : syracuseStep 753683 = 1130525) B1130525
theorem B753713 : Blo 499793 753713 := bstep (se 2 (by rfl) ⟨282642, by rfl⟩ : syracuseStep 753713 = 565285) B565285
theorem B753731 : Blo 499793 753731 := bstep (se 1 (by rfl) ⟨565298, by rfl⟩ : syracuseStep 753731 = 1130597) B1130597
theorem B753761 : Blo 499793 753761 := bstep (se 2 (by rfl) ⟨282660, by rfl⟩ : syracuseStep 753761 = 565321) B565321
theorem B753779 : Blo 499793 753779 := bstep (se 1 (by rfl) ⟨565334, by rfl⟩ : syracuseStep 753779 = 1130669) B1130669
theorem B1900685 : Blo 499793 1900685 := bstep (se 3 (by rfl) ⟨356378, by rfl⟩ : syracuseStep 1900685 = 712757) B712757
theorem B753809 : Blo 499793 753809 := bstep (se 2 (by rfl) ⟨282678, by rfl⟩ : syracuseStep 753809 = 565357) B565357
theorem B753827 : Blo 499793 753827 := bstep (se 1 (by rfl) ⟨565370, by rfl⟩ : syracuseStep 753827 = 1130741) B1130741
theorem B950449 : Blo 499793 950449 := bstep (se 2 (by rfl) ⟨356418, by rfl⟩ : syracuseStep 950449 = 712837) B712837
theorem B753857 : Blo 499793 753857 := bstep (se 2 (by rfl) ⟨282696, by rfl⟩ : syracuseStep 753857 = 565393) B565393
theorem B753875 : Blo 499793 753875 := bstep (se 1 (by rfl) ⟨565406, by rfl⟩ : syracuseStep 753875 = 1130813) B1130813
theorem B753905 : Blo 499793 753905 := bstep (se 2 (by rfl) ⟨282714, by rfl⟩ : syracuseStep 753905 = 565429) B565429
theorem B753923 : Blo 499793 753923 := bstep (se 1 (by rfl) ⟨565442, by rfl⟩ : syracuseStep 753923 = 1130885) B1130885
theorem B753953 : Blo 499793 753953 := bstep (se 2 (by rfl) ⟨282732, by rfl⟩ : syracuseStep 753953 = 565465) B565465
theorem B753971 : Blo 499793 753971 := bstep (se 1 (by rfl) ⟨565478, by rfl⟩ : syracuseStep 753971 = 1130957) B1130957
theorem B950609 : Blo 499793 950609 := bstep (se 2 (by rfl) ⟨356478, by rfl⟩ : syracuseStep 950609 = 712957) B712957
theorem B754001 : Blo 499793 754001 := bstep (se 2 (by rfl) ⟨282750, by rfl⟩ : syracuseStep 754001 = 565501) B565501
theorem B754019 : Blo 499793 754019 := bstep (se 1 (by rfl) ⟨565514, by rfl⟩ : syracuseStep 754019 = 1131029) B1131029
theorem B754049 : Blo 499793 754049 := bstep (se 2 (by rfl) ⟨282768, by rfl⟩ : syracuseStep 754049 = 565537) B565537
theorem B1409411 : Blo 499793 1409411 := bstep (se 1 (by rfl) ⟨1057058, by rfl⟩ : syracuseStep 1409411 = 2114117) B2114117
theorem B754067 : Blo 499793 754067 := bstep (se 1 (by rfl) ⟨565550, by rfl⟩ : syracuseStep 754067 = 1131101) B1131101
theorem B754097 : Blo 499793 754097 := bstep (se 2 (by rfl) ⟨282786, by rfl⟩ : syracuseStep 754097 = 565573) B565573
theorem B754115 : Blo 499793 754115 := bstep (se 1 (by rfl) ⟨565586, by rfl⟩ : syracuseStep 754115 = 1131173) B1131173
theorem B754145 : Blo 499793 754145 := bstep (se 2 (by rfl) ⟨282804, by rfl⟩ : syracuseStep 754145 = 565609) B565609
theorem B754163 : Blo 499793 754163 := bstep (se 1 (by rfl) ⟨565622, by rfl⟩ : syracuseStep 754163 = 1131245) B1131245
theorem B754193 : Blo 499793 754193 := bstep (se 2 (by rfl) ⟨282822, by rfl⟩ : syracuseStep 754193 = 565645) B565645
theorem B754211 : Blo 499793 754211 := bstep (se 1 (by rfl) ⟨565658, by rfl⟩ : syracuseStep 754211 = 1131317) B1131317
theorem B754241 : Blo 499793 754241 := bstep (se 2 (by rfl) ⟨282840, by rfl⟩ : syracuseStep 754241 = 565681) B565681
theorem B754259 : Blo 499793 754259 := bstep (se 1 (by rfl) ⟨565694, by rfl⟩ : syracuseStep 754259 = 1131389) B1131389
theorem B754289 : Blo 499793 754289 := bstep (se 2 (by rfl) ⟨282858, by rfl⟩ : syracuseStep 754289 = 565717) B565717
theorem B754307 : Blo 499793 754307 := bstep (se 1 (by rfl) ⟨565730, by rfl⟩ : syracuseStep 754307 = 1131461) B1131461
theorem B754337 : Blo 499793 754337 := bstep (se 2 (by rfl) ⟨282876, by rfl⟩ : syracuseStep 754337 = 565753) B565753
theorem B754355 : Blo 499793 754355 := bstep (se 1 (by rfl) ⟨565766, by rfl⟩ : syracuseStep 754355 = 1131533) B1131533
theorem B754385 : Blo 499793 754385 := bstep (se 2 (by rfl) ⟨282894, by rfl⟩ : syracuseStep 754385 = 565789) B565789
theorem B3605219 : Blo 499793 3605219 := bstep (se 1 (by rfl) ⟨2703914, by rfl⟩ : syracuseStep 3605219 = 5407829) B5407829
theorem B951011 : Blo 499793 951011 := bstep (se 1 (by rfl) ⟨713258, by rfl⟩ : syracuseStep 951011 = 1426517) B1426517
theorem B754403 : Blo 499793 754403 := bstep (se 1 (by rfl) ⟨565802, by rfl⟩ : syracuseStep 754403 = 1131605) B1131605
theorem B754433 : Blo 499793 754433 := bstep (se 2 (by rfl) ⟨282912, by rfl⟩ : syracuseStep 754433 = 565825) B565825
theorem B754451 : Blo 499793 754451 := bstep (se 1 (by rfl) ⟨565838, by rfl⟩ : syracuseStep 754451 = 1131677) B1131677
theorem B754481 : Blo 499793 754481 := bstep (se 2 (by rfl) ⟨282930, by rfl⟩ : syracuseStep 754481 = 565861) B565861
theorem B754499 : Blo 499793 754499 := bstep (se 1 (by rfl) ⟨565874, by rfl⟩ : syracuseStep 754499 = 1131749) B1131749
theorem B754529 : Blo 499793 754529 := bstep (se 2 (by rfl) ⟨282948, by rfl⟩ : syracuseStep 754529 = 565897) B565897
theorem B754547 : Blo 499793 754547 := bstep (se 1 (by rfl) ⟨565910, by rfl⟩ : syracuseStep 754547 = 1131821) B1131821
theorem B754577 : Blo 499793 754577 := bstep (se 2 (by rfl) ⟨282966, by rfl⟩ : syracuseStep 754577 = 565933) B565933
theorem B754595 : Blo 499793 754595 := bstep (se 1 (by rfl) ⟨565946, by rfl⟩ : syracuseStep 754595 = 1131893) B1131893
theorem B754625 : Blo 499793 754625 := bstep (se 2 (by rfl) ⟨282984, by rfl⟩ : syracuseStep 754625 = 565969) B565969
theorem B754643 : Blo 499793 754643 := bstep (se 1 (by rfl) ⟨565982, by rfl⟩ : syracuseStep 754643 = 1131965) B1131965
theorem B754673 : Blo 499793 754673 := bstep (se 2 (by rfl) ⟨283002, by rfl⟩ : syracuseStep 754673 = 566005) B566005
theorem B754691 : Blo 499793 754691 := bstep (se 1 (by rfl) ⟨566018, by rfl⟩ : syracuseStep 754691 = 1132037) B1132037
theorem B754721 : Blo 499793 754721 := bstep (se 2 (by rfl) ⟨283020, by rfl⟩ : syracuseStep 754721 = 566041) B566041
theorem B754739 : Blo 499793 754739 := bstep (se 1 (by rfl) ⟨566054, by rfl⟩ : syracuseStep 754739 = 1132109) B1132109
theorem B754769 : Blo 499793 754769 := bstep (se 2 (by rfl) ⟨283038, by rfl⟩ : syracuseStep 754769 = 566077) B566077
theorem B754787 : Blo 499793 754787 := bstep (se 1 (by rfl) ⟨566090, by rfl⟩ : syracuseStep 754787 = 1132181) B1132181
theorem B754817 : Blo 499793 754817 := bstep (se 2 (by rfl) ⟨283056, by rfl⟩ : syracuseStep 754817 = 566113) B566113
theorem B754835 : Blo 499793 754835 := bstep (se 1 (by rfl) ⟨566126, by rfl⟩ : syracuseStep 754835 = 1132253) B1132253
theorem B1082531 : Blo 499793 1082531 := bstep (se 1 (by rfl) ⟨811898, by rfl⟩ : syracuseStep 1082531 = 1623797) B1623797
theorem B754865 : Blo 499793 754865 := bstep (se 2 (by rfl) ⟨283074, by rfl⟩ : syracuseStep 754865 = 566149) B566149
theorem B754883 : Blo 499793 754883 := bstep (se 1 (by rfl) ⟨566162, by rfl⟩ : syracuseStep 754883 = 1132325) B1132325
theorem B754913 : Blo 499793 754913 := bstep (se 2 (by rfl) ⟨283092, by rfl⟩ : syracuseStep 754913 = 566185) B566185
theorem B754931 : Blo 499793 754931 := bstep (se 1 (by rfl) ⟨566198, by rfl⟩ : syracuseStep 754931 = 1132397) B1132397
theorem B754961 : Blo 499793 754961 := bstep (se 2 (by rfl) ⟨283110, by rfl⟩ : syracuseStep 754961 = 566221) B566221
theorem B754979 : Blo 499793 754979 := bstep (se 1 (by rfl) ⟨566234, by rfl⟩ : syracuseStep 754979 = 1132469) B1132469
theorem B755009 : Blo 499793 755009 := bstep (se 2 (by rfl) ⟨283128, by rfl⟩ : syracuseStep 755009 = 566257) B566257
theorem B755027 : Blo 499793 755027 := bstep (se 1 (by rfl) ⟨566270, by rfl⟩ : syracuseStep 755027 = 1132541) B1132541
theorem B755057 : Blo 499793 755057 := bstep (se 2 (by rfl) ⟨283146, by rfl⟩ : syracuseStep 755057 = 566293) B566293
theorem B755075 : Blo 499793 755075 := bstep (se 1 (by rfl) ⟨566306, by rfl⟩ : syracuseStep 755075 = 1132613) B1132613
theorem B755105 : Blo 499793 755105 := bstep (se 2 (by rfl) ⟨283164, by rfl⟩ : syracuseStep 755105 = 566329) B566329
theorem B755123 : Blo 499793 755123 := bstep (se 1 (by rfl) ⟨566342, by rfl⟩ : syracuseStep 755123 = 1132685) B1132685
theorem B755153 : Blo 499793 755153 := bstep (se 2 (by rfl) ⟨283182, by rfl⟩ : syracuseStep 755153 = 566365) B566365
theorem B755171 : Blo 499793 755171 := bstep (se 1 (by rfl) ⟨566378, by rfl⟩ : syracuseStep 755171 = 1132757) B1132757
theorem B755201 : Blo 499793 755201 := bstep (se 2 (by rfl) ⟨283200, by rfl⟩ : syracuseStep 755201 = 566401) B566401
theorem B3606029 : Blo 499793 3606029 := bstep (se 3 (by rfl) ⟨676130, by rfl⟩ : syracuseStep 3606029 = 1352261) B1352261
theorem B755219 : Blo 499793 755219 := bstep (se 1 (by rfl) ⟨566414, by rfl⟩ : syracuseStep 755219 = 1132829) B1132829
theorem B755249 : Blo 499793 755249 := bstep (se 2 (by rfl) ⟨283218, by rfl⟩ : syracuseStep 755249 = 566437) B566437
theorem B755267 : Blo 499793 755267 := bstep (se 1 (by rfl) ⟨566450, by rfl⟩ : syracuseStep 755267 = 1132901) B1132901
theorem B755297 : Blo 499793 755297 := bstep (se 2 (by rfl) ⟨283236, by rfl⟩ : syracuseStep 755297 = 566473) B566473
theorem B951907 : Blo 499793 951907 := bstep (se 1 (by rfl) ⟨713930, by rfl⟩ : syracuseStep 951907 = 1427861) B1427861
theorem B755315 : Blo 499793 755315 := bstep (se 1 (by rfl) ⟨566486, by rfl⟩ : syracuseStep 755315 = 1132973) B1132973
theorem B755345 : Blo 499793 755345 := bstep (se 2 (by rfl) ⟨283254, by rfl⟩ : syracuseStep 755345 = 566509) B566509
theorem B755363 : Blo 499793 755363 := bstep (se 1 (by rfl) ⟨566522, by rfl⟩ : syracuseStep 755363 = 1133045) B1133045
theorem B755393 : Blo 499793 755393 := bstep (se 2 (by rfl) ⟨283272, by rfl⟩ : syracuseStep 755393 = 566545) B566545
theorem B3049157 : Blo 499793 3049157 := bstep (se 4 (by rfl) ⟨285858, by rfl⟩ : syracuseStep 3049157 = 571717) B571717
theorem B755411 : Blo 499793 755411 := bstep (se 1 (by rfl) ⟨566558, by rfl⟩ : syracuseStep 755411 = 1133117) B1133117
theorem B755441 : Blo 499793 755441 := bstep (se 2 (by rfl) ⟨283290, by rfl⟩ : syracuseStep 755441 = 566581) B566581
theorem B952067 : Blo 499793 952067 := bstep (se 1 (by rfl) ⟨714050, by rfl⟩ : syracuseStep 952067 = 1428101) B1428101
theorem B755459 : Blo 499793 755459 := bstep (se 1 (by rfl) ⟨566594, by rfl⟩ : syracuseStep 755459 = 1133189) B1133189
theorem B755489 : Blo 499793 755489 := bstep (se 2 (by rfl) ⟨283308, by rfl⟩ : syracuseStep 755489 = 566617) B566617
theorem B919331 : Blo 499793 919331 := bstep (se 1 (by rfl) ⟨689498, by rfl⟩ : syracuseStep 919331 = 1378997) B1378997
theorem B755507 : Blo 499793 755507 := bstep (se 1 (by rfl) ⟨566630, by rfl⟩ : syracuseStep 755507 = 1133261) B1133261
theorem B3802949 : Blo 499793 3802949 := bstep (se 4 (by rfl) ⟨356526, by rfl⟩ : syracuseStep 3802949 = 713053) B713053
theorem B755537 : Blo 499793 755537 := bstep (se 2 (by rfl) ⟨283326, by rfl⟩ : syracuseStep 755537 = 566653) B566653
theorem B755555 : Blo 499793 755555 := bstep (se 1 (by rfl) ⟨566666, by rfl⟩ : syracuseStep 755555 = 1133333) B1133333
theorem B755585 : Blo 499793 755585 := bstep (se 2 (by rfl) ⟨283344, by rfl⟩ : syracuseStep 755585 = 566689) B566689
theorem B1017731 : Blo 499793 1017731 := bstep (se 1 (by rfl) ⟨763298, by rfl⟩ : syracuseStep 1017731 = 1526597) B1526597
theorem B755603 : Blo 499793 755603 := bstep (se 1 (by rfl) ⟨566702, by rfl⟩ : syracuseStep 755603 = 1133405) B1133405
theorem B755633 : Blo 499793 755633 := bstep (se 2 (by rfl) ⟨283362, by rfl⟩ : syracuseStep 755633 = 566725) B566725
theorem B755651 : Blo 499793 755651 := bstep (se 1 (by rfl) ⟨566738, by rfl⟩ : syracuseStep 755651 = 1133477) B1133477
theorem B755681 : Blo 499793 755681 := bstep (se 2 (by rfl) ⟨283380, by rfl⟩ : syracuseStep 755681 = 566761) B566761
theorem B1607651 : Blo 499793 1607651 := bstep (se 1 (by rfl) ⟨1205738, by rfl⟩ : syracuseStep 1607651 = 2411477) B2411477
theorem B2852941 : Blo 499793 2852941 := bstep (se 3 (by rfl) ⟨534926, by rfl⟩ : syracuseStep 2852941 = 1069853) B1069853
theorem B1607779 : Blo 499793 1607779 := bstep (se 1 (by rfl) ⟨1205834, by rfl⟩ : syracuseStep 1607779 = 2411669) B2411669
theorem B1673389 : Blo 499793 1673389 := bstep (se 3 (by rfl) ⟨313760, by rfl⟩ : syracuseStep 1673389 = 627521) B627521
theorem B1902797 : Blo 499793 1902797 := bstep (se 3 (by rfl) ⟨356774, by rfl⟩ : syracuseStep 1902797 = 713549) B713549
theorem B2033905 : Blo 499793 2033905 := bstep (se 2 (by rfl) ⟨762714, by rfl⟩ : syracuseStep 2033905 = 1525429) B1525429
theorem B5147021 : Blo 499793 5147021 := bstep (se 3 (by rfl) ⟨965066, by rfl⟩ : syracuseStep 5147021 = 1930133) B1930133
theorem B1804685 : Blo 499793 1804685 := bstep (se 3 (by rfl) ⟨338378, by rfl⟩ : syracuseStep 1804685 = 676757) B676757
theorem B1608113 : Blo 499793 1608113 := bstep (se 2 (by rfl) ⟨603042, by rfl⟩ : syracuseStep 1608113 = 1206085) B1206085
theorem B5737229 : Blo 499793 5737229 := bstep (se 3 (by rfl) ⟨1075730, by rfl⟩ : syracuseStep 5737229 = 2151461) B2151461
theorem B953137 : Blo 499793 953137 := bstep (se 2 (by rfl) ⟨357426, by rfl⟩ : syracuseStep 953137 = 714853) B714853
theorem B1018673 : Blo 499793 1018673 := bstep (se 2 (by rfl) ⟨382002, by rfl⟩ : syracuseStep 1018673 = 764005) B764005
theorem B1903601 : Blo 499793 1903601 := bstep (se 2 (by rfl) ⟨713850, by rfl⟩ : syracuseStep 1903601 = 1427701) B1427701
theorem B855043 : Blo 499793 855043 := bstep (se 1 (by rfl) ⟨641282, by rfl⟩ : syracuseStep 855043 = 1282565) B1282565
theorem B3051107 : Blo 499793 3051107 := bstep (se 1 (by rfl) ⟨2288330, by rfl⟩ : syracuseStep 3051107 = 4576661) B4576661
theorem B1904269 : Blo 499793 1904269 := bstep (se 3 (by rfl) ⟨357050, by rfl⟩ : syracuseStep 1904269 = 714101) B714101
theorem B954193 : Blo 499793 954193 := bstep (se 2 (by rfl) ⟨357822, by rfl⟩ : syracuseStep 954193 = 715645) B715645
theorem B2854925 : Blo 499793 2854925 := bstep (se 3 (by rfl) ⟨535298, by rfl⟩ : syracuseStep 2854925 = 1070597) B1070597
theorem B12226787 : Blo 499793 12226787 := bstep (se 1 (by rfl) ⟨9170090, by rfl⟩ : syracuseStep 12226787 = 18340181) B18340181
theorem B954595 : Blo 499793 954595 := bstep (se 1 (by rfl) ⟨715946, by rfl⟩ : syracuseStep 954595 = 1431893) B1431893
theorem B954641 : Blo 499793 954641 := bstep (se 2 (by rfl) ⟨357990, by rfl⟩ : syracuseStep 954641 = 715981) B715981
theorem B1905059 : Blo 499793 1905059 := bstep (se 1 (by rfl) ⟨1428794, by rfl⟩ : syracuseStep 1905059 = 2857589) B2857589
theorem B856577 : Blo 499793 856577 := bstep (se 2 (by rfl) ⟨321216, by rfl⟩ : syracuseStep 856577 = 642433) B642433
theorem B954929 : Blo 499793 954929 := bstep (se 2 (by rfl) ⟨358098, by rfl⟩ : syracuseStep 954929 = 716197) B716197
theorem B2855857 : Blo 499793 2855857 := bstep (se 2 (by rfl) ⟨1070946, by rfl⟩ : syracuseStep 2855857 = 2141893) B2141893
theorem B1905713 : Blo 499793 1905713 := bstep (se 2 (by rfl) ⟨714642, by rfl⟩ : syracuseStep 1905713 = 1429285) B1429285
theorem B857233 : Blo 499793 857233 := bstep (se 2 (by rfl) ⟨321462, by rfl⟩ : syracuseStep 857233 = 642925) B642925
theorem B562387 : Blo 499793 562387 := bstep (se 1 (by rfl) ⟨421790, by rfl⟩ : syracuseStep 562387 = 843581) B843581
theorem B3314915 : Blo 499793 3314915 := bstep (se 1 (by rfl) ⟨2486186, by rfl⟩ : syracuseStep 3314915 = 4972373) B4972373
theorem B955651 : Blo 499793 955651 := bstep (se 1 (by rfl) ⟨716738, by rfl⟩ : syracuseStep 955651 = 1433477) B1433477
theorem B1021187 : Blo 499793 1021187 := bstep (se 1 (by rfl) ⟨765890, by rfl⟩ : syracuseStep 1021187 = 1531781) B1531781
theorem B1611085 : Blo 499793 1611085 := bstep (se 3 (by rfl) ⟨302078, by rfl⟩ : syracuseStep 1611085 = 604157) B604157
theorem B562531 : Blo 499793 562531 := bstep (se 1 (by rfl) ⟨421898, by rfl⟩ : syracuseStep 562531 = 843797) B843797
theorem B562675 : Blo 499793 562675 := bstep (se 1 (by rfl) ⟨422006, by rfl⟩ : syracuseStep 562675 = 844013) B844013
theorem B1611341 : Blo 499793 1611341 := bstep (se 3 (by rfl) ⟨302126, by rfl⟩ : syracuseStep 1611341 = 604253) B604253
theorem B3216995 : Blo 499793 3216995 := bstep (se 1 (by rfl) ⟨2412746, by rfl⟩ : syracuseStep 3216995 = 4825493) B4825493
theorem B562819 : Blo 499793 562819 := bstep (se 1 (by rfl) ⟨422114, by rfl⟩ : syracuseStep 562819 = 844229) B844229
theorem B956099 : Blo 499793 956099 := bstep (se 1 (by rfl) ⟨717074, by rfl⟩ : syracuseStep 956099 = 1434149) B1434149
theorem B562963 : Blo 499793 562963 := bstep (se 1 (by rfl) ⟨422222, by rfl⟩ : syracuseStep 562963 = 844445) B844445
theorem B1709923 : Blo 499793 1709923 := bstep (se 1 (by rfl) ⟨1282442, by rfl⟩ : syracuseStep 1709923 = 2564885) B2564885
theorem B563107 : Blo 499793 563107 := bstep (se 1 (by rfl) ⟨422330, by rfl⟩ : syracuseStep 563107 = 844661) B844661
theorem B956387 : Blo 499793 956387 := bstep (se 1 (by rfl) ⟨717290, by rfl⟩ : syracuseStep 956387 = 1434581) B1434581
theorem B2758691 : Blo 499793 2758691 := bstep (se 1 (by rfl) ⟨2069018, by rfl⟩ : syracuseStep 2758691 = 4138037) B4138037
theorem B563251 : Blo 499793 563251 := bstep (se 1 (by rfl) ⟨422438, by rfl⟩ : syracuseStep 563251 = 844877) B844877
theorem B5150789 : Blo 499793 5150789 := bstep (se 4 (by rfl) ⟨482886, by rfl⟩ : syracuseStep 5150789 = 965773) B965773
theorem B3872881 : Blo 499793 3872881 := bstep (se 2 (by rfl) ⟨1452330, by rfl⟩ : syracuseStep 3872881 = 2904661) B2904661
theorem B563395 : Blo 499793 563395 := bstep (se 1 (by rfl) ⟨422546, by rfl⟩ : syracuseStep 563395 = 845093) B845093
theorem B563539 : Blo 499793 563539 := bstep (se 1 (by rfl) ⟨422654, by rfl⟩ : syracuseStep 563539 = 845309) B845309
theorem B2857315 : Blo 499793 2857315 := bstep (se 1 (by rfl) ⟨2142986, by rfl⟩ : syracuseStep 2857315 = 4285973) B4285973
theorem B563683 : Blo 499793 563683 := bstep (se 1 (by rfl) ⟨422762, by rfl⟩ : syracuseStep 563683 = 845525) B845525
theorem B1907171 : Blo 499793 1907171 := bstep (se 1 (by rfl) ⟨1430378, by rfl⟩ : syracuseStep 1907171 = 2860757) B2860757
theorem B1907185 : Blo 499793 1907185 := bstep (se 2 (by rfl) ⟨715194, by rfl⟩ : syracuseStep 1907185 = 1430389) B1430389
theorem B596531 : Blo 499793 596531 := bstep (se 1 (by rfl) ⟨447398, by rfl⟩ : syracuseStep 596531 = 894797) B894797
theorem B563827 : Blo 499793 563827 := bstep (se 1 (by rfl) ⟨422870, by rfl⟩ : syracuseStep 563827 = 845741) B845741
theorem B563971 : Blo 499793 563971 := bstep (se 1 (by rfl) ⟨422978, by rfl⟩ : syracuseStep 563971 = 845957) B845957
theorem B4070213 : Blo 499793 4070213 := bstep (se 4 (by rfl) ⟨381582, by rfl⟩ : syracuseStep 4070213 = 763165) B763165
theorem B2857841 : Blo 499793 2857841 := bstep (se 2 (by rfl) ⟨1071690, by rfl⟩ : syracuseStep 2857841 = 2143381) B2143381
theorem B564115 : Blo 499793 564115 := bstep (se 1 (by rfl) ⟨423086, by rfl⟩ : syracuseStep 564115 = 846173) B846173
theorem B2038691 : Blo 499793 2038691 := bstep (se 1 (by rfl) ⟨1529018, by rfl⟩ : syracuseStep 2038691 = 3058037) B3058037
theorem B564259 : Blo 499793 564259 := bstep (se 1 (by rfl) ⟨423194, by rfl⟩ : syracuseStep 564259 = 846389) B846389
theorem B1612867 : Blo 499793 1612867 := bstep (se 1 (by rfl) ⟨1209650, by rfl⟩ : syracuseStep 1612867 = 2419301) B2419301
theorem B760963 : Blo 499793 760963 := bstep (se 1 (by rfl) ⟨570722, by rfl⟩ : syracuseStep 760963 = 1141445) B1141445
theorem B564403 : Blo 499793 564403 := bstep (se 1 (by rfl) ⟨423302, by rfl⟩ : syracuseStep 564403 = 846605) B846605
theorem B564547 : Blo 499793 564547 := bstep (se 1 (by rfl) ⟨423410, by rfl⟩ : syracuseStep 564547 = 846821) B846821
theorem B564691 : Blo 499793 564691 := bstep (se 1 (by rfl) ⟨423518, by rfl⟩ : syracuseStep 564691 = 847037) B847037
theorem B761329 : Blo 499793 761329 := bstep (se 2 (by rfl) ⟨285498, by rfl⟩ : syracuseStep 761329 = 570997) B570997
theorem B4070897 : Blo 499793 4070897 := bstep (se 2 (by rfl) ⟨1526586, by rfl⟩ : syracuseStep 4070897 = 3053173) B3053173
theorem B3808781 : Blo 499793 3808781 := bstep (se 3 (by rfl) ⟨714146, by rfl⟩ : syracuseStep 3808781 = 1428293) B1428293
theorem B564835 : Blo 499793 564835 := bstep (se 1 (by rfl) ⟨423626, by rfl⟩ : syracuseStep 564835 = 847253) B847253
theorem B564979 : Blo 499793 564979 := bstep (se 1 (by rfl) ⟨423734, by rfl⟩ : syracuseStep 564979 = 847469) B847469
theorem B4595555 : Blo 499793 4595555 := bstep (se 1 (by rfl) ⟨3446666, by rfl⟩ : syracuseStep 4595555 = 6893333) B6893333
theorem B565123 : Blo 499793 565123 := bstep (se 1 (by rfl) ⟨423842, by rfl⟩ : syracuseStep 565123 = 847685) B847685
theorem B1613699 : Blo 499793 1613699 := bstep (se 1 (by rfl) ⟨1210274, by rfl⟩ : syracuseStep 1613699 = 2420549) B2420549
theorem B1908643 : Blo 499793 1908643 := bstep (se 1 (by rfl) ⟨1431482, by rfl⟩ : syracuseStep 1908643 = 2862965) B2862965
theorem B2531249 : Blo 499793 2531249 := bstep (se 2 (by rfl) ⟨949218, by rfl⟩ : syracuseStep 2531249 = 1898437) B1898437
theorem B565267 : Blo 499793 565267 := bstep (se 1 (by rfl) ⟨423950, by rfl⟩ : syracuseStep 565267 = 847901) B847901
theorem B499795 : Blo 499793 499795 := bstep (se 1 (by rfl) ⟨374846, by rfl⟩ : syracuseStep 499795 = 749693) B749693
theorem B499811 : Blo 499793 499811 := bstep (se 1 (by rfl) ⟨374858, by rfl⟩ : syracuseStep 499811 = 749717) B749717
theorem B499827 : Blo 499793 499827 := bstep (se 1 (by rfl) ⟨374870, by rfl⟩ : syracuseStep 499827 = 749741) B749741
theorem B499843 : Blo 499793 499843 := bstep (se 1 (by rfl) ⟨374882, by rfl⟩ : syracuseStep 499843 = 749765) B749765
theorem B499859 : Blo 499793 499859 := bstep (se 1 (by rfl) ⟨374894, by rfl⟩ : syracuseStep 499859 = 749789) B749789
theorem B499875 : Blo 499793 499875 := bstep (se 1 (by rfl) ⟨374906, by rfl⟩ : syracuseStep 499875 = 749813) B749813
theorem B565411 : Blo 499793 565411 := bstep (se 1 (by rfl) ⟨424058, by rfl⟩ : syracuseStep 565411 = 848117) B848117
theorem B499891 : Blo 499793 499891 := bstep (se 1 (by rfl) ⟨374918, by rfl⟩ : syracuseStep 499891 = 749837) B749837
theorem B499907 : Blo 499793 499907 := bstep (se 1 (by rfl) ⟨374930, by rfl⟩ : syracuseStep 499907 = 749861) B749861
theorem B499923 : Blo 499793 499923 := bstep (se 1 (by rfl) ⟨374942, by rfl⟩ : syracuseStep 499923 = 749885) B749885
theorem B499939 : Blo 499793 499939 := bstep (se 1 (by rfl) ⟨374954, by rfl⟩ : syracuseStep 499939 = 749909) B749909
theorem B2138339 : Blo 499793 2138339 := bstep (se 1 (by rfl) ⟨1603754, by rfl⟩ : syracuseStep 2138339 = 3207509) B3207509
theorem B499955 : Blo 499793 499955 := bstep (se 1 (by rfl) ⟨374966, by rfl⟩ : syracuseStep 499955 = 749933) B749933
theorem B499971 : Blo 499793 499971 := bstep (se 1 (by rfl) ⟨374978, by rfl⟩ : syracuseStep 499971 = 749957) B749957
theorem B1712387 : Blo 499793 1712387 := bstep (se 1 (by rfl) ⟨1284290, by rfl⟩ : syracuseStep 1712387 = 2568581) B2568581
theorem B499987 : Blo 499793 499987 := bstep (se 1 (by rfl) ⟨374990, by rfl⟩ : syracuseStep 499987 = 749981) B749981
theorem B762131 : Blo 499793 762131 := bstep (se 1 (by rfl) ⟨571598, by rfl⟩ : syracuseStep 762131 = 1143197) B1143197
theorem B860435 : Blo 499793 860435 := bstep (se 1 (by rfl) ⟨645326, by rfl⟩ : syracuseStep 860435 = 1290653) B1290653
theorem B500003 : Blo 499793 500003 := bstep (se 1 (by rfl) ⟨375002, by rfl⟩ : syracuseStep 500003 = 750005) B750005
theorem B2859299 : Blo 499793 2859299 := bstep (se 1 (by rfl) ⟨2144474, by rfl⟩ : syracuseStep 2859299 = 4288949) B4288949
theorem B500019 : Blo 499793 500019 := bstep (se 1 (by rfl) ⟨375014, by rfl⟩ : syracuseStep 500019 = 750029) B750029
theorem B565555 : Blo 499793 565555 := bstep (se 1 (by rfl) ⟨424166, by rfl⟩ : syracuseStep 565555 = 848333) B848333
theorem B500035 : Blo 499793 500035 := bstep (se 1 (by rfl) ⟨375026, by rfl⟩ : syracuseStep 500035 = 750053) B750053
theorem B500051 : Blo 499793 500051 := bstep (se 1 (by rfl) ⟨375038, by rfl⟩ : syracuseStep 500051 = 750077) B750077
theorem B500067 : Blo 499793 500067 := bstep (se 1 (by rfl) ⟨375050, by rfl⟩ : syracuseStep 500067 = 750101) B750101
theorem B1352045 : Blo 499793 1352045 := bstep (se 3 (by rfl) ⟨253508, by rfl⟩ : syracuseStep 1352045 = 507017) B507017
theorem B500083 : Blo 499793 500083 := bstep (se 1 (by rfl) ⟨375062, by rfl⟩ : syracuseStep 500083 = 750125) B750125
theorem B500099 : Blo 499793 500099 := bstep (se 1 (by rfl) ⟨375074, by rfl⟩ : syracuseStep 500099 = 750149) B750149
theorem B1810829 : Blo 499793 1810829 := bstep (se 3 (by rfl) ⟨339530, by rfl⟩ : syracuseStep 1810829 = 679061) B679061
theorem B500115 : Blo 499793 500115 := bstep (se 1 (by rfl) ⟨375086, by rfl⟩ : syracuseStep 500115 = 750173) B750173
theorem B500131 : Blo 499793 500131 := bstep (se 1 (by rfl) ⟨375098, by rfl⟩ : syracuseStep 500131 = 750197) B750197
theorem B500147 : Blo 499793 500147 := bstep (se 1 (by rfl) ⟨375110, by rfl⟩ : syracuseStep 500147 = 750221) B750221
theorem B500163 : Blo 499793 500163 := bstep (se 1 (by rfl) ⟨375122, by rfl⟩ : syracuseStep 500163 = 750245) B750245
theorem B565699 : Blo 499793 565699 := bstep (se 1 (by rfl) ⟨424274, by rfl⟩ : syracuseStep 565699 = 848549) B848549
theorem B500179 : Blo 499793 500179 := bstep (se 1 (by rfl) ⟨375134, by rfl⟩ : syracuseStep 500179 = 750269) B750269
theorem B500195 : Blo 499793 500195 := bstep (se 1 (by rfl) ⟨375146, by rfl⟩ : syracuseStep 500195 = 750293) B750293
theorem B500211 : Blo 499793 500211 := bstep (se 1 (by rfl) ⟨375158, by rfl⟩ : syracuseStep 500211 = 750317) B750317
theorem B500227 : Blo 499793 500227 := bstep (se 1 (by rfl) ⟨375170, by rfl⟩ : syracuseStep 500227 = 750341) B750341
theorem B500243 : Blo 499793 500243 := bstep (se 1 (by rfl) ⟨375182, by rfl⟩ : syracuseStep 500243 = 750365) B750365
theorem B500259 : Blo 499793 500259 := bstep (se 1 (by rfl) ⟨375194, by rfl⟩ : syracuseStep 500259 = 750389) B750389
theorem B500275 : Blo 499793 500275 := bstep (se 1 (by rfl) ⟨375206, by rfl⟩ : syracuseStep 500275 = 750413) B750413
theorem B500291 : Blo 499793 500291 := bstep (se 1 (by rfl) ⟨375218, by rfl⟩ : syracuseStep 500291 = 750437) B750437
theorem B500307 : Blo 499793 500307 := bstep (se 1 (by rfl) ⟨375230, by rfl⟩ : syracuseStep 500307 = 750461) B750461
theorem B565843 : Blo 499793 565843 := bstep (se 1 (by rfl) ⟨424382, by rfl⟩ : syracuseStep 565843 = 848765) B848765
theorem B500323 : Blo 499793 500323 := bstep (se 1 (by rfl) ⟨375242, by rfl⟩ : syracuseStep 500323 = 750485) B750485
theorem B2892401 : Blo 499793 2892401 := bstep (se 2 (by rfl) ⟨1084650, by rfl⟩ : syracuseStep 2892401 = 2169301) B2169301
theorem B500339 : Blo 499793 500339 := bstep (se 1 (by rfl) ⟨375254, by rfl⟩ : syracuseStep 500339 = 750509) B750509
theorem B500355 : Blo 499793 500355 := bstep (se 1 (by rfl) ⟨375266, by rfl⟩ : syracuseStep 500355 = 750533) B750533
theorem B7250573 : Blo 499793 7250573 := bstep (se 3 (by rfl) ⟨1359482, by rfl⟩ : syracuseStep 7250573 = 2718965) B2718965
theorem B2040461 : Blo 499793 2040461 := bstep (se 3 (by rfl) ⟨382586, by rfl⟩ : syracuseStep 2040461 = 765173) B765173
theorem B500371 : Blo 499793 500371 := bstep (se 1 (by rfl) ⟨375278, by rfl⟩ : syracuseStep 500371 = 750557) B750557
theorem B500387 : Blo 499793 500387 := bstep (se 1 (by rfl) ⟨375290, by rfl⟩ : syracuseStep 500387 = 750581) B750581
theorem B500403 : Blo 499793 500403 := bstep (se 1 (by rfl) ⟨375302, by rfl⟩ : syracuseStep 500403 = 750605) B750605
theorem B500419 : Blo 499793 500419 := bstep (se 1 (by rfl) ⟨375314, by rfl⟩ : syracuseStep 500419 = 750629) B750629
theorem B500435 : Blo 499793 500435 := bstep (se 1 (by rfl) ⟨375326, by rfl⟩ : syracuseStep 500435 = 750653) B750653
theorem B500451 : Blo 499793 500451 := bstep (se 1 (by rfl) ⟨375338, by rfl⟩ : syracuseStep 500451 = 750677) B750677
theorem B565987 : Blo 499793 565987 := bstep (se 1 (by rfl) ⟨424490, by rfl⟩ : syracuseStep 565987 = 848981) B848981
theorem B500467 : Blo 499793 500467 := bstep (se 1 (by rfl) ⟨375350, by rfl⟩ : syracuseStep 500467 = 750701) B750701
theorem B500483 : Blo 499793 500483 := bstep (se 1 (by rfl) ⟨375362, by rfl⟩ : syracuseStep 500483 = 750725) B750725
theorem B500499 : Blo 499793 500499 := bstep (se 1 (by rfl) ⟨375374, by rfl⟩ : syracuseStep 500499 = 750749) B750749
theorem B500515 : Blo 499793 500515 := bstep (se 1 (by rfl) ⟨375386, by rfl⟩ : syracuseStep 500515 = 750773) B750773
theorem B500531 : Blo 499793 500531 := bstep (se 1 (by rfl) ⟨375398, by rfl⟩ : syracuseStep 500531 = 750797) B750797
theorem B5481269 : Blo 499793 5481269 := bstep (se 5 (by rfl) ⟨256934, by rfl⟩ : syracuseStep 5481269 = 513869) B513869
theorem B500547 : Blo 499793 500547 := bstep (se 1 (by rfl) ⟨375410, by rfl⟩ : syracuseStep 500547 = 750821) B750821
theorem B762691 : Blo 499793 762691 := bstep (se 1 (by rfl) ⟨572018, by rfl⟩ : syracuseStep 762691 = 1144037) B1144037
theorem B500563 : Blo 499793 500563 := bstep (se 1 (by rfl) ⟨375422, by rfl⟩ : syracuseStep 500563 = 750845) B750845
theorem B500579 : Blo 499793 500579 := bstep (se 1 (by rfl) ⟨375434, by rfl⟩ : syracuseStep 500579 = 750869) B750869
theorem B500595 : Blo 499793 500595 := bstep (se 1 (by rfl) ⟨375446, by rfl⟩ : syracuseStep 500595 = 750893) B750893
theorem B566131 : Blo 499793 566131 := bstep (se 1 (by rfl) ⟨424598, by rfl⟩ : syracuseStep 566131 = 849197) B849197
theorem B500611 : Blo 499793 500611 := bstep (se 1 (by rfl) ⟨375458, by rfl⟩ : syracuseStep 500611 = 750917) B750917
theorem B500627 : Blo 499793 500627 := bstep (se 1 (by rfl) ⟨375470, by rfl⟩ : syracuseStep 500627 = 750941) B750941
theorem B500643 : Blo 499793 500643 := bstep (se 1 (by rfl) ⟨375482, by rfl⟩ : syracuseStep 500643 = 750965) B750965
theorem B500659 : Blo 499793 500659 := bstep (se 1 (by rfl) ⟨375494, by rfl⟩ : syracuseStep 500659 = 750989) B750989
theorem B500675 : Blo 499793 500675 := bstep (se 1 (by rfl) ⟨375506, by rfl⟩ : syracuseStep 500675 = 751013) B751013
theorem B500691 : Blo 499793 500691 := bstep (se 1 (by rfl) ⟨375518, by rfl⟩ : syracuseStep 500691 = 751037) B751037
theorem B500707 : Blo 499793 500707 := bstep (se 1 (by rfl) ⟨375530, by rfl⟩ : syracuseStep 500707 = 751061) B751061
theorem B500723 : Blo 499793 500723 := bstep (se 1 (by rfl) ⟨375542, by rfl⟩ : syracuseStep 500723 = 751085) B751085
theorem B500739 : Blo 499793 500739 := bstep (se 1 (by rfl) ⟨375554, by rfl⟩ : syracuseStep 500739 = 751109) B751109
theorem B566275 : Blo 499793 566275 := bstep (se 1 (by rfl) ⟨424706, by rfl⟩ : syracuseStep 566275 = 849413) B849413
theorem B500755 : Blo 499793 500755 := bstep (se 1 (by rfl) ⟨375566, by rfl⟩ : syracuseStep 500755 = 751133) B751133
theorem B500771 : Blo 499793 500771 := bstep (se 1 (by rfl) ⟨375578, by rfl⟩ : syracuseStep 500771 = 751157) B751157
theorem B500787 : Blo 499793 500787 := bstep (se 1 (by rfl) ⟨375590, by rfl⟩ : syracuseStep 500787 = 751181) B751181
theorem B500803 : Blo 499793 500803 := bstep (se 1 (by rfl) ⟨375602, by rfl⟩ : syracuseStep 500803 = 751205) B751205
theorem B500819 : Blo 499793 500819 := bstep (se 1 (by rfl) ⟨375614, by rfl⟩ : syracuseStep 500819 = 751229) B751229
theorem B500835 : Blo 499793 500835 := bstep (se 1 (by rfl) ⟨375626, by rfl⟩ : syracuseStep 500835 = 751253) B751253
theorem B500851 : Blo 499793 500851 := bstep (se 1 (by rfl) ⟨375638, by rfl⟩ : syracuseStep 500851 = 751277) B751277
theorem B500867 : Blo 499793 500867 := bstep (se 1 (by rfl) ⟨375650, by rfl⟩ : syracuseStep 500867 = 751301) B751301
theorem B500883 : Blo 499793 500883 := bstep (se 1 (by rfl) ⟨375662, by rfl⟩ : syracuseStep 500883 = 751325) B751325
theorem B566419 : Blo 499793 566419 := bstep (se 1 (by rfl) ⟨424814, by rfl⟩ : syracuseStep 566419 = 849629) B849629
theorem B500899 : Blo 499793 500899 := bstep (se 1 (by rfl) ⟨375674, by rfl⟩ : syracuseStep 500899 = 751349) B751349
theorem B500915 : Blo 499793 500915 := bstep (se 1 (by rfl) ⟨375686, by rfl⟩ : syracuseStep 500915 = 751373) B751373
theorem B1352899 : Blo 499793 1352899 := bstep (se 1 (by rfl) ⟨1014674, by rfl⟩ : syracuseStep 1352899 = 2029349) B2029349
theorem B500931 : Blo 499793 500931 := bstep (se 1 (by rfl) ⟨375698, by rfl⟩ : syracuseStep 500931 = 751397) B751397
theorem B500947 : Blo 499793 500947 := bstep (se 1 (by rfl) ⟨375710, by rfl⟩ : syracuseStep 500947 = 751421) B751421
theorem B500963 : Blo 499793 500963 := bstep (se 1 (by rfl) ⟨375722, by rfl⟩ : syracuseStep 500963 = 751445) B751445
theorem B500979 : Blo 499793 500979 := bstep (se 1 (by rfl) ⟨375734, by rfl⟩ : syracuseStep 500979 = 751469) B751469
theorem B500995 : Blo 499793 500995 := bstep (se 1 (by rfl) ⟨375746, by rfl⟩ : syracuseStep 500995 = 751493) B751493
theorem B501011 : Blo 499793 501011 := bstep (se 1 (by rfl) ⟨375758, by rfl⟩ : syracuseStep 501011 = 751517) B751517
theorem B533795 : Blo 499793 533795 := bstep (se 1 (by rfl) ⟨400346, by rfl⟩ : syracuseStep 533795 = 800693) B800693
theorem B501027 : Blo 499793 501027 := bstep (se 1 (by rfl) ⟨375770, by rfl⟩ : syracuseStep 501027 = 751541) B751541
theorem B566563 : Blo 499793 566563 := bstep (se 1 (by rfl) ⟨424922, by rfl⟩ : syracuseStep 566563 = 849845) B849845
theorem B501043 : Blo 499793 501043 := bstep (se 1 (by rfl) ⟨375782, by rfl⟩ : syracuseStep 501043 = 751565) B751565
theorem B501059 : Blo 499793 501059 := bstep (se 1 (by rfl) ⟨375794, by rfl⟩ : syracuseStep 501059 = 751589) B751589
theorem B501075 : Blo 499793 501075 := bstep (se 1 (by rfl) ⟨375806, by rfl⟩ : syracuseStep 501075 = 751613) B751613
theorem B2532707 : Blo 499793 2532707 := bstep (se 1 (by rfl) ⟨1899530, by rfl⟩ : syracuseStep 2532707 = 3799061) B3799061
theorem B501091 : Blo 499793 501091 := bstep (se 1 (by rfl) ⟨375818, by rfl⟩ : syracuseStep 501091 = 751637) B751637
theorem B501107 : Blo 499793 501107 := bstep (se 1 (by rfl) ⟨375830, by rfl⟩ : syracuseStep 501107 = 751661) B751661
theorem B501123 : Blo 499793 501123 := bstep (se 1 (by rfl) ⟨375842, by rfl⟩ : syracuseStep 501123 = 751685) B751685
theorem B501139 : Blo 499793 501139 := bstep (se 1 (by rfl) ⟨375854, by rfl⟩ : syracuseStep 501139 = 751709) B751709
theorem B501155 : Blo 499793 501155 := bstep (se 1 (by rfl) ⟨375866, by rfl⟩ : syracuseStep 501155 = 751733) B751733
theorem B501171 : Blo 499793 501171 := bstep (se 1 (by rfl) ⟨375878, by rfl⟩ : syracuseStep 501171 = 751757) B751757
theorem B566707 : Blo 499793 566707 := bstep (se 1 (by rfl) ⟨425030, by rfl⟩ : syracuseStep 566707 = 850061) B850061
theorem B501187 : Blo 499793 501187 := bstep (se 1 (by rfl) ⟨375890, by rfl⟩ : syracuseStep 501187 = 751781) B751781
theorem B501203 : Blo 499793 501203 := bstep (se 1 (by rfl) ⟨375902, by rfl⟩ : syracuseStep 501203 = 751805) B751805
theorem B501219 : Blo 499793 501219 := bstep (se 1 (by rfl) ⟨375914, by rfl⟩ : syracuseStep 501219 = 751829) B751829
theorem B501235 : Blo 499793 501235 := bstep (se 1 (by rfl) ⟨375926, by rfl⟩ : syracuseStep 501235 = 751853) B751853
theorem B501251 : Blo 499793 501251 := bstep (se 1 (by rfl) ⟨375938, by rfl⟩ : syracuseStep 501251 = 751877) B751877
theorem B501267 : Blo 499793 501267 := bstep (se 1 (by rfl) ⟨375950, by rfl⟩ : syracuseStep 501267 = 751901) B751901
theorem B501283 : Blo 499793 501283 := bstep (se 1 (by rfl) ⟨375962, by rfl⟩ : syracuseStep 501283 = 751925) B751925
theorem B3221041 : Blo 499793 3221041 := bstep (se 2 (by rfl) ⟨1207890, by rfl⟩ : syracuseStep 3221041 = 2415781) B2415781
theorem B501299 : Blo 499793 501299 := bstep (se 1 (by rfl) ⟨375974, by rfl⟩ : syracuseStep 501299 = 751949) B751949
theorem B501315 : Blo 499793 501315 := bstep (se 1 (by rfl) ⟨375986, by rfl⟩ : syracuseStep 501315 = 751973) B751973
theorem B501331 : Blo 499793 501331 := bstep (se 1 (by rfl) ⟨375998, by rfl⟩ : syracuseStep 501331 = 751997) B751997
theorem B501347 : Blo 499793 501347 := bstep (se 1 (by rfl) ⟨376010, by rfl⟩ : syracuseStep 501347 = 752021) B752021
theorem B501363 : Blo 499793 501363 := bstep (se 1 (by rfl) ⟨376022, by rfl⟩ : syracuseStep 501363 = 752045) B752045
theorem B501379 : Blo 499793 501379 := bstep (se 1 (by rfl) ⟨376034, by rfl⟩ : syracuseStep 501379 = 752069) B752069
theorem B501395 : Blo 499793 501395 := bstep (se 1 (by rfl) ⟨376046, by rfl⟩ : syracuseStep 501395 = 752093) B752093
theorem B501411 : Blo 499793 501411 := bstep (se 1 (by rfl) ⟨376058, by rfl⟩ : syracuseStep 501411 = 752117) B752117
theorem B501427 : Blo 499793 501427 := bstep (se 1 (by rfl) ⟨376070, by rfl⟩ : syracuseStep 501427 = 752141) B752141
theorem B501443 : Blo 499793 501443 := bstep (se 1 (by rfl) ⟨376082, by rfl⟩ : syracuseStep 501443 = 752165) B752165
theorem B501459 : Blo 499793 501459 := bstep (se 1 (by rfl) ⟨376094, by rfl⟩ : syracuseStep 501459 = 752189) B752189
theorem B501475 : Blo 499793 501475 := bstep (se 1 (by rfl) ⟨376106, by rfl⟩ : syracuseStep 501475 = 752213) B752213
theorem B501491 : Blo 499793 501491 := bstep (se 1 (by rfl) ⟨376118, by rfl⟩ : syracuseStep 501491 = 752237) B752237
theorem B501507 : Blo 499793 501507 := bstep (se 1 (by rfl) ⟨376130, by rfl⟩ : syracuseStep 501507 = 752261) B752261
theorem B501523 : Blo 499793 501523 := bstep (se 1 (by rfl) ⟨376142, by rfl⟩ : syracuseStep 501523 = 752285) B752285
theorem B501539 : Blo 499793 501539 := bstep (se 1 (by rfl) ⟨376154, by rfl⟩ : syracuseStep 501539 = 752309) B752309
theorem B501555 : Blo 499793 501555 := bstep (se 1 (by rfl) ⟨376166, by rfl⟩ : syracuseStep 501555 = 752333) B752333
theorem B501571 : Blo 499793 501571 := bstep (se 1 (by rfl) ⟨376178, by rfl⟩ : syracuseStep 501571 = 752357) B752357
theorem B501587 : Blo 499793 501587 := bstep (se 1 (by rfl) ⟨376190, by rfl⟩ : syracuseStep 501587 = 752381) B752381
theorem B501603 : Blo 499793 501603 := bstep (se 1 (by rfl) ⟨376202, by rfl⟩ : syracuseStep 501603 = 752405) B752405
theorem B501619 : Blo 499793 501619 := bstep (se 1 (by rfl) ⟨376214, by rfl⟩ : syracuseStep 501619 = 752429) B752429
theorem B501635 : Blo 499793 501635 := bstep (se 1 (by rfl) ⟨376226, by rfl⟩ : syracuseStep 501635 = 752453) B752453
theorem B501651 : Blo 499793 501651 := bstep (se 1 (by rfl) ⟨376238, by rfl⟩ : syracuseStep 501651 = 752477) B752477
theorem B501667 : Blo 499793 501667 := bstep (se 1 (by rfl) ⟨376250, by rfl⟩ : syracuseStep 501667 = 752501) B752501
theorem B1812401 : Blo 499793 1812401 := bstep (se 2 (by rfl) ⟨679650, by rfl⟩ : syracuseStep 1812401 = 1359301) B1359301
theorem B501683 : Blo 499793 501683 := bstep (se 1 (by rfl) ⟨376262, by rfl⟩ : syracuseStep 501683 = 752525) B752525
theorem B501699 : Blo 499793 501699 := bstep (se 1 (by rfl) ⟨376274, by rfl⟩ : syracuseStep 501699 = 752549) B752549
theorem B501715 : Blo 499793 501715 := bstep (se 1 (by rfl) ⟨376286, by rfl⟩ : syracuseStep 501715 = 752573) B752573
theorem B501731 : Blo 499793 501731 := bstep (se 1 (by rfl) ⟨376298, by rfl⟩ : syracuseStep 501731 = 752597) B752597
theorem B501747 : Blo 499793 501747 := bstep (se 1 (by rfl) ⟨376310, by rfl⟩ : syracuseStep 501747 = 752621) B752621
theorem B501763 : Blo 499793 501763 := bstep (se 1 (by rfl) ⟨376322, by rfl⟩ : syracuseStep 501763 = 752645) B752645
theorem B534547 : Blo 499793 534547 := bstep (se 1 (by rfl) ⟨400910, by rfl⟩ : syracuseStep 534547 = 801821) B801821
theorem B501779 : Blo 499793 501779 := bstep (se 1 (by rfl) ⟨376334, by rfl⟩ : syracuseStep 501779 = 752669) B752669
theorem B501795 : Blo 499793 501795 := bstep (se 1 (by rfl) ⟨376346, by rfl⟩ : syracuseStep 501795 = 752693) B752693
theorem B501811 : Blo 499793 501811 := bstep (se 1 (by rfl) ⟨376358, by rfl⟩ : syracuseStep 501811 = 752717) B752717
theorem B501827 : Blo 499793 501827 := bstep (se 1 (by rfl) ⟨376370, by rfl⟩ : syracuseStep 501827 = 752741) B752741
theorem B1910861 : Blo 499793 1910861 := bstep (se 3 (by rfl) ⟨358286, by rfl⟩ : syracuseStep 1910861 = 716573) B716573
theorem B1452113 : Blo 499793 1452113 := bstep (se 2 (by rfl) ⟨544542, by rfl⟩ : syracuseStep 1452113 = 1089085) B1089085
theorem B501843 : Blo 499793 501843 := bstep (se 1 (by rfl) ⟨376382, by rfl⟩ : syracuseStep 501843 = 752765) B752765
theorem B501859 : Blo 499793 501859 := bstep (se 1 (by rfl) ⟨376394, by rfl⟩ : syracuseStep 501859 = 752789) B752789
theorem B501875 : Blo 499793 501875 := bstep (se 1 (by rfl) ⟨376406, by rfl⟩ : syracuseStep 501875 = 752813) B752813
theorem B501891 : Blo 499793 501891 := bstep (se 1 (by rfl) ⟨376418, by rfl⟩ : syracuseStep 501891 = 752837) B752837
theorem B2861189 : Blo 499793 2861189 := bstep (se 4 (by rfl) ⟨268236, by rfl⟩ : syracuseStep 2861189 = 536473) B536473
theorem B2533517 : Blo 499793 2533517 := bstep (se 3 (by rfl) ⟨475034, by rfl⟩ : syracuseStep 2533517 = 950069) B950069
theorem B501907 : Blo 499793 501907 := bstep (se 1 (by rfl) ⟨376430, by rfl⟩ : syracuseStep 501907 = 752861) B752861
theorem B501923 : Blo 499793 501923 := bstep (se 1 (by rfl) ⟨376442, by rfl⟩ : syracuseStep 501923 = 752885) B752885
theorem B501939 : Blo 499793 501939 := bstep (se 1 (by rfl) ⟨376454, by rfl⟩ : syracuseStep 501939 = 752909) B752909
theorem B501955 : Blo 499793 501955 := bstep (se 1 (by rfl) ⟨376466, by rfl⟩ : syracuseStep 501955 = 752933) B752933
theorem B501971 : Blo 499793 501971 := bstep (se 1 (by rfl) ⟨376478, by rfl⟩ : syracuseStep 501971 = 752957) B752957
theorem B501987 : Blo 499793 501987 := bstep (se 1 (by rfl) ⟨376490, by rfl⟩ : syracuseStep 501987 = 752981) B752981
theorem B502003 : Blo 499793 502003 := bstep (se 1 (by rfl) ⟨376502, by rfl⟩ : syracuseStep 502003 = 753005) B753005
theorem B633091 : Blo 499793 633091 := bstep (se 1 (by rfl) ⟨474818, by rfl⟩ : syracuseStep 633091 = 949637) B949637
theorem B502019 : Blo 499793 502019 := bstep (se 1 (by rfl) ⟨376514, by rfl⟩ : syracuseStep 502019 = 753029) B753029
theorem B502035 : Blo 499793 502035 := bstep (se 1 (by rfl) ⟨376526, by rfl⟩ : syracuseStep 502035 = 753053) B753053
theorem B502051 : Blo 499793 502051 := bstep (se 1 (by rfl) ⟨376538, by rfl⟩ : syracuseStep 502051 = 753077) B753077
theorem B1124657 : Blo 499793 1124657 := bstep (se 2 (by rfl) ⟨421746, by rfl⟩ : syracuseStep 1124657 = 843493) B843493
theorem B502067 : Blo 499793 502067 := bstep (se 1 (by rfl) ⟨376550, by rfl⟩ : syracuseStep 502067 = 753101) B753101
theorem B1124675 : Blo 499793 1124675 := bstep (se 1 (by rfl) ⟨843506, by rfl⟩ : syracuseStep 1124675 = 1687013) B1687013
theorem B502083 : Blo 499793 502083 := bstep (se 1 (by rfl) ⟨376562, by rfl⟩ : syracuseStep 502083 = 753125) B753125
theorem B502099 : Blo 499793 502099 := bstep (se 1 (by rfl) ⟨376574, by rfl⟩ : syracuseStep 502099 = 753149) B753149
theorem B633187 : Blo 499793 633187 := bstep (se 1 (by rfl) ⟨474890, by rfl⟩ : syracuseStep 633187 = 949781) B949781
theorem B502115 : Blo 499793 502115 := bstep (se 1 (by rfl) ⟨376586, by rfl⟩ : syracuseStep 502115 = 753173) B753173
theorem B3811697 : Blo 499793 3811697 := bstep (se 2 (by rfl) ⟨1429386, by rfl⟩ : syracuseStep 3811697 = 2858773) B2858773
theorem B502131 : Blo 499793 502131 := bstep (se 1 (by rfl) ⟨376598, by rfl⟩ : syracuseStep 502131 = 753197) B753197
theorem B502147 : Blo 499793 502147 := bstep (se 1 (by rfl) ⟨376610, by rfl⟩ : syracuseStep 502147 = 753221) B753221
theorem B502163 : Blo 499793 502163 := bstep (se 1 (by rfl) ⟨376622, by rfl⟩ : syracuseStep 502163 = 753245) B753245
theorem B502179 : Blo 499793 502179 := bstep (se 1 (by rfl) ⟨376634, by rfl⟩ : syracuseStep 502179 = 753269) B753269
theorem B502195 : Blo 499793 502195 := bstep (se 1 (by rfl) ⟨376646, by rfl⟩ : syracuseStep 502195 = 753293) B753293
theorem B502211 : Blo 499793 502211 := bstep (se 1 (by rfl) ⟨376658, by rfl⟩ : syracuseStep 502211 = 753317) B753317
theorem B502227 : Blo 499793 502227 := bstep (se 1 (by rfl) ⟨376670, by rfl⟩ : syracuseStep 502227 = 753341) B753341
theorem B502243 : Blo 499793 502243 := bstep (se 1 (by rfl) ⟨376682, by rfl⟩ : syracuseStep 502243 = 753365) B753365
theorem B502259 : Blo 499793 502259 := bstep (se 1 (by rfl) ⟨376694, by rfl⟩ : syracuseStep 502259 = 753389) B753389
theorem B502275 : Blo 499793 502275 := bstep (se 1 (by rfl) ⟨376706, by rfl⟩ : syracuseStep 502275 = 753413) B753413
theorem B502291 : Blo 499793 502291 := bstep (se 1 (by rfl) ⟨376718, by rfl⟩ : syracuseStep 502291 = 753437) B753437
theorem B1223203 : Blo 499793 1223203 := bstep (se 1 (by rfl) ⟨917402, by rfl⟩ : syracuseStep 1223203 = 1834805) B1834805
theorem B502307 : Blo 499793 502307 := bstep (se 1 (by rfl) ⟨376730, by rfl⟩ : syracuseStep 502307 = 753461) B753461
theorem B502323 : Blo 499793 502323 := bstep (se 1 (by rfl) ⟨376742, by rfl⟩ : syracuseStep 502323 = 753485) B753485
theorem B502339 : Blo 499793 502339 := bstep (se 1 (by rfl) ⟨376754, by rfl⟩ : syracuseStep 502339 = 753509) B753509
theorem B1124945 : Blo 499793 1124945 := bstep (se 2 (by rfl) ⟨421854, by rfl⟩ : syracuseStep 1124945 = 843709) B843709
theorem B502355 : Blo 499793 502355 := bstep (se 1 (by rfl) ⟨376766, by rfl⟩ : syracuseStep 502355 = 753533) B753533
theorem B1124963 : Blo 499793 1124963 := bstep (se 1 (by rfl) ⟨843722, by rfl⟩ : syracuseStep 1124963 = 1687445) B1687445
theorem B502371 : Blo 499793 502371 := bstep (se 1 (by rfl) ⟨376778, by rfl⟩ : syracuseStep 502371 = 753557) B753557
theorem B764515 : Blo 499793 764515 := bstep (se 1 (by rfl) ⟨573386, by rfl⟩ : syracuseStep 764515 = 1146773) B1146773
theorem B502387 : Blo 499793 502387 := bstep (se 1 (by rfl) ⟨376790, by rfl⟩ : syracuseStep 502387 = 753581) B753581
theorem B502403 : Blo 499793 502403 := bstep (se 1 (by rfl) ⟨376802, by rfl⟩ : syracuseStep 502403 = 753605) B753605
theorem B502419 : Blo 499793 502419 := bstep (se 1 (by rfl) ⟨376814, by rfl⟩ : syracuseStep 502419 = 753629) B753629
theorem B1354403 : Blo 499793 1354403 := bstep (se 1 (by rfl) ⟨1015802, by rfl⟩ : syracuseStep 1354403 = 2031605) B2031605
theorem B502435 : Blo 499793 502435 := bstep (se 1 (by rfl) ⟨376826, by rfl⟩ : syracuseStep 502435 = 753653) B753653
theorem B502451 : Blo 499793 502451 := bstep (se 1 (by rfl) ⟨376838, by rfl⟩ : syracuseStep 502451 = 753677) B753677
theorem B502467 : Blo 499793 502467 := bstep (se 1 (by rfl) ⟨376850, by rfl⟩ : syracuseStep 502467 = 753701) B753701
theorem B502483 : Blo 499793 502483 := bstep (se 1 (by rfl) ⟨376862, by rfl⟩ : syracuseStep 502483 = 753725) B753725
theorem B502499 : Blo 499793 502499 := bstep (se 1 (by rfl) ⟨376874, by rfl⟩ : syracuseStep 502499 = 753749) B753749
theorem B502515 : Blo 499793 502515 := bstep (se 1 (by rfl) ⟨376886, by rfl⟩ : syracuseStep 502515 = 753773) B753773
theorem B502531 : Blo 499793 502531 := bstep (se 1 (by rfl) ⟨376898, by rfl⟩ : syracuseStep 502531 = 753797) B753797
theorem B502547 : Blo 499793 502547 := bstep (se 1 (by rfl) ⟨376910, by rfl⟩ : syracuseStep 502547 = 753821) B753821
theorem B502563 : Blo 499793 502563 := bstep (se 1 (by rfl) ⟨376922, by rfl⟩ : syracuseStep 502563 = 753845) B753845
theorem B502579 : Blo 499793 502579 := bstep (se 1 (by rfl) ⟨376934, by rfl⟩ : syracuseStep 502579 = 753869) B753869
theorem B764723 : Blo 499793 764723 := bstep (se 1 (by rfl) ⟨573542, by rfl⟩ : syracuseStep 764723 = 1147085) B1147085
theorem B502595 : Blo 499793 502595 := bstep (se 1 (by rfl) ⟨376946, by rfl⟩ : syracuseStep 502595 = 753893) B753893
theorem B2141005 : Blo 499793 2141005 := bstep (se 3 (by rfl) ⟨401438, by rfl⟩ : syracuseStep 2141005 = 802877) B802877
theorem B633683 : Blo 499793 633683 := bstep (se 1 (by rfl) ⟨475262, by rfl⟩ : syracuseStep 633683 = 950525) B950525
theorem B502611 : Blo 499793 502611 := bstep (se 1 (by rfl) ⟨376958, by rfl⟩ : syracuseStep 502611 = 753917) B753917
theorem B502627 : Blo 499793 502627 := bstep (se 1 (by rfl) ⟨376970, by rfl⟩ : syracuseStep 502627 = 753941) B753941
theorem B1125233 : Blo 499793 1125233 := bstep (se 2 (by rfl) ⟨421962, by rfl⟩ : syracuseStep 1125233 = 843925) B843925
theorem B502643 : Blo 499793 502643 := bstep (se 1 (by rfl) ⟨376982, by rfl⟩ : syracuseStep 502643 = 753965) B753965
theorem B1125251 : Blo 499793 1125251 := bstep (se 1 (by rfl) ⟨843938, by rfl⟩ : syracuseStep 1125251 = 1687877) B1687877
theorem B502659 : Blo 499793 502659 := bstep (se 1 (by rfl) ⟨376994, by rfl⟩ : syracuseStep 502659 = 753989) B753989
theorem B502675 : Blo 499793 502675 := bstep (se 1 (by rfl) ⟨377006, by rfl⟩ : syracuseStep 502675 = 754013) B754013
theorem B502691 : Blo 499793 502691 := bstep (se 1 (by rfl) ⟨377018, by rfl⟩ : syracuseStep 502691 = 754037) B754037
theorem B502707 : Blo 499793 502707 := bstep (se 1 (by rfl) ⟨377030, by rfl⟩ : syracuseStep 502707 = 754061) B754061
theorem B502723 : Blo 499793 502723 := bstep (se 1 (by rfl) ⟨377042, by rfl⟩ : syracuseStep 502723 = 754085) B754085
theorem B502739 : Blo 499793 502739 := bstep (se 1 (by rfl) ⟨377054, by rfl⟩ : syracuseStep 502739 = 754109) B754109
theorem B4271075 : Blo 499793 4271075 := bstep (se 1 (by rfl) ⟨3203306, by rfl⟩ : syracuseStep 4271075 = 6406613) B6406613
theorem B502755 : Blo 499793 502755 := bstep (se 1 (by rfl) ⟨377066, by rfl⟩ : syracuseStep 502755 = 754133) B754133
theorem B502771 : Blo 499793 502771 := bstep (se 1 (by rfl) ⟨377078, by rfl⟩ : syracuseStep 502771 = 754157) B754157
theorem B502787 : Blo 499793 502787 := bstep (se 1 (by rfl) ⟨377090, by rfl⟩ : syracuseStep 502787 = 754181) B754181
theorem B502803 : Blo 499793 502803 := bstep (se 1 (by rfl) ⟨377102, by rfl⟩ : syracuseStep 502803 = 754205) B754205
theorem B502819 : Blo 499793 502819 := bstep (se 1 (by rfl) ⟨377114, by rfl⟩ : syracuseStep 502819 = 754229) B754229
theorem B601139 : Blo 499793 601139 := bstep (se 1 (by rfl) ⟨450854, by rfl⟩ : syracuseStep 601139 = 901709) B901709
theorem B502835 : Blo 499793 502835 := bstep (se 1 (by rfl) ⟨377126, by rfl⟩ : syracuseStep 502835 = 754253) B754253
theorem B535619 : Blo 499793 535619 := bstep (se 1 (by rfl) ⟨401714, by rfl⟩ : syracuseStep 535619 = 803429) B803429
theorem B502851 : Blo 499793 502851 := bstep (se 1 (by rfl) ⟨377138, by rfl⟩ : syracuseStep 502851 = 754277) B754277
theorem B502867 : Blo 499793 502867 := bstep (se 1 (by rfl) ⟨377150, by rfl⟩ : syracuseStep 502867 = 754301) B754301
theorem B502883 : Blo 499793 502883 := bstep (se 1 (by rfl) ⟨377162, by rfl⟩ : syracuseStep 502883 = 754325) B754325
theorem B502899 : Blo 499793 502899 := bstep (se 1 (by rfl) ⟨377174, by rfl⟩ : syracuseStep 502899 = 754349) B754349
theorem B502915 : Blo 499793 502915 := bstep (se 1 (by rfl) ⟨377186, by rfl⟩ : syracuseStep 502915 = 754373) B754373
theorem B1715341 : Blo 499793 1715341 := bstep (se 3 (by rfl) ⟨321626, by rfl⟩ : syracuseStep 1715341 = 643253) B643253
theorem B1125521 : Blo 499793 1125521 := bstep (se 2 (by rfl) ⟨422070, by rfl⟩ : syracuseStep 1125521 = 844141) B844141
theorem B502931 : Blo 499793 502931 := bstep (se 1 (by rfl) ⟨377198, by rfl⟩ : syracuseStep 502931 = 754397) B754397
theorem B1125539 : Blo 499793 1125539 := bstep (se 1 (by rfl) ⟨844154, by rfl⟩ : syracuseStep 1125539 = 1688309) B1688309
theorem B502947 : Blo 499793 502947 := bstep (se 1 (by rfl) ⟨377210, by rfl⟩ : syracuseStep 502947 = 754421) B754421
theorem B1813681 : Blo 499793 1813681 := bstep (se 2 (by rfl) ⟨680130, by rfl⟩ : syracuseStep 1813681 = 1360261) B1360261
theorem B502963 : Blo 499793 502963 := bstep (se 1 (by rfl) ⟨377222, by rfl⟩ : syracuseStep 502963 = 754445) B754445
theorem B502979 : Blo 499793 502979 := bstep (se 1 (by rfl) ⟨377234, by rfl⟩ : syracuseStep 502979 = 754469) B754469
theorem B502995 : Blo 499793 502995 := bstep (se 1 (by rfl) ⟨377246, by rfl⟩ : syracuseStep 502995 = 754493) B754493
theorem B503011 : Blo 499793 503011 := bstep (se 1 (by rfl) ⟨377258, by rfl⟩ : syracuseStep 503011 = 754517) B754517
theorem B503027 : Blo 499793 503027 := bstep (se 1 (by rfl) ⟨377270, by rfl⟩ : syracuseStep 503027 = 754541) B754541
theorem B503043 : Blo 499793 503043 := bstep (se 1 (by rfl) ⟨377282, by rfl⟩ : syracuseStep 503043 = 754565) B754565
theorem B503059 : Blo 499793 503059 := bstep (se 1 (by rfl) ⟨377294, by rfl⟩ : syracuseStep 503059 = 754589) B754589
theorem B503075 : Blo 499793 503075 := bstep (se 1 (by rfl) ⟨377306, by rfl⟩ : syracuseStep 503075 = 754613) B754613
theorem B503091 : Blo 499793 503091 := bstep (se 1 (by rfl) ⟨377318, by rfl⟩ : syracuseStep 503091 = 754637) B754637
theorem B503107 : Blo 499793 503107 := bstep (se 1 (by rfl) ⟨377330, by rfl⟩ : syracuseStep 503107 = 754661) B754661
theorem B503123 : Blo 499793 503123 := bstep (se 1 (by rfl) ⟨377342, by rfl⟩ : syracuseStep 503123 = 754685) B754685
theorem B503139 : Blo 499793 503139 := bstep (se 1 (by rfl) ⟨377354, by rfl⟩ : syracuseStep 503139 = 754709) B754709
theorem B503155 : Blo 499793 503155 := bstep (se 1 (by rfl) ⟨377366, by rfl⟩ : syracuseStep 503155 = 754733) B754733
theorem B503171 : Blo 499793 503171 := bstep (se 1 (by rfl) ⟨377378, by rfl⟩ : syracuseStep 503171 = 754757) B754757
theorem B503187 : Blo 499793 503187 := bstep (se 1 (by rfl) ⟨377390, by rfl⟩ : syracuseStep 503187 = 754781) B754781
theorem B503203 : Blo 499793 503203 := bstep (se 1 (by rfl) ⟨377402, by rfl⟩ : syracuseStep 503203 = 754805) B754805
theorem B1125809 : Blo 499793 1125809 := bstep (se 2 (by rfl) ⟨422178, by rfl⟩ : syracuseStep 1125809 = 844357) B844357
theorem B503219 : Blo 499793 503219 := bstep (se 1 (by rfl) ⟨377414, by rfl⟩ : syracuseStep 503219 = 754829) B754829
theorem B1125827 : Blo 499793 1125827 := bstep (se 1 (by rfl) ⟨844370, by rfl⟩ : syracuseStep 1125827 = 1688741) B1688741
theorem B503235 : Blo 499793 503235 := bstep (se 1 (by rfl) ⟨377426, by rfl⟩ : syracuseStep 503235 = 754853) B754853
theorem B503251 : Blo 499793 503251 := bstep (se 1 (by rfl) ⟨377438, by rfl⟩ : syracuseStep 503251 = 754877) B754877
theorem B503267 : Blo 499793 503267 := bstep (se 1 (by rfl) ⟨377450, by rfl⟩ : syracuseStep 503267 = 754901) B754901
theorem B503283 : Blo 499793 503283 := bstep (se 1 (by rfl) ⟨377462, by rfl⟩ : syracuseStep 503283 = 754925) B754925
theorem B503299 : Blo 499793 503299 := bstep (se 1 (by rfl) ⟨377474, by rfl⟩ : syracuseStep 503299 = 754949) B754949
theorem B634387 : Blo 499793 634387 := bstep (se 1 (by rfl) ⟨475790, by rfl⟩ : syracuseStep 634387 = 951581) B951581
theorem B503315 : Blo 499793 503315 := bstep (se 1 (by rfl) ⟨377486, by rfl⟩ : syracuseStep 503315 = 754973) B754973
theorem B503331 : Blo 499793 503331 := bstep (se 1 (by rfl) ⟨377498, by rfl⟩ : syracuseStep 503331 = 754997) B754997
theorem B503347 : Blo 499793 503347 := bstep (se 1 (by rfl) ⟨377510, by rfl⟩ : syracuseStep 503347 = 755021) B755021
theorem B503363 : Blo 499793 503363 := bstep (se 1 (by rfl) ⟨377522, by rfl⟩ : syracuseStep 503363 = 755045) B755045
theorem B503379 : Blo 499793 503379 := bstep (se 1 (by rfl) ⟨377534, by rfl⟩ : syracuseStep 503379 = 755069) B755069
theorem B503395 : Blo 499793 503395 := bstep (se 1 (by rfl) ⟨377546, by rfl⟩ : syracuseStep 503395 = 755093) B755093
theorem B634483 : Blo 499793 634483 := bstep (se 1 (by rfl) ⟨475862, by rfl⟩ : syracuseStep 634483 = 951725) B951725
theorem B503411 : Blo 499793 503411 := bstep (se 1 (by rfl) ⟨377558, by rfl⟩ : syracuseStep 503411 = 755117) B755117
theorem B503427 : Blo 499793 503427 := bstep (se 1 (by rfl) ⟨377570, by rfl⟩ : syracuseStep 503427 = 755141) B755141
theorem B503443 : Blo 499793 503443 := bstep (se 1 (by rfl) ⟨377582, by rfl⟩ : syracuseStep 503443 = 755165) B755165
theorem B503459 : Blo 499793 503459 := bstep (se 1 (by rfl) ⟨377594, by rfl⟩ : syracuseStep 503459 = 755189) B755189
theorem B503475 : Blo 499793 503475 := bstep (se 1 (by rfl) ⟨377606, by rfl⟩ : syracuseStep 503475 = 755213) B755213
theorem B503491 : Blo 499793 503491 := bstep (se 1 (by rfl) ⟨377618, by rfl⟩ : syracuseStep 503491 = 755237) B755237
theorem B1126097 : Blo 499793 1126097 := bstep (se 2 (by rfl) ⟨422286, by rfl⟩ : syracuseStep 1126097 = 844573) B844573
theorem B503507 : Blo 499793 503507 := bstep (se 1 (by rfl) ⟨377630, by rfl⟩ : syracuseStep 503507 = 755261) B755261
theorem B1126115 : Blo 499793 1126115 := bstep (se 1 (by rfl) ⟨844586, by rfl⟩ : syracuseStep 1126115 = 1689173) B1689173
theorem B503523 : Blo 499793 503523 := bstep (se 1 (by rfl) ⟨377642, by rfl⟩ : syracuseStep 503523 = 755285) B755285
theorem B503539 : Blo 499793 503539 := bstep (se 1 (by rfl) ⟨377654, by rfl⟩ : syracuseStep 503539 = 755309) B755309
theorem B503555 : Blo 499793 503555 := bstep (se 1 (by rfl) ⟨377666, by rfl⟩ : syracuseStep 503555 = 755333) B755333
theorem B503571 : Blo 499793 503571 := bstep (se 1 (by rfl) ⟨377678, by rfl⟩ : syracuseStep 503571 = 755357) B755357
theorem B503587 : Blo 499793 503587 := bstep (se 1 (by rfl) ⟨377690, by rfl⟩ : syracuseStep 503587 = 755381) B755381
theorem B503603 : Blo 499793 503603 := bstep (se 1 (by rfl) ⟨377702, by rfl⟩ : syracuseStep 503603 = 755405) B755405
theorem B503619 : Blo 499793 503619 := bstep (se 1 (by rfl) ⟨377714, by rfl⟩ : syracuseStep 503619 = 755429) B755429
theorem B503635 : Blo 499793 503635 := bstep (se 1 (by rfl) ⟨377726, by rfl⟩ : syracuseStep 503635 = 755453) B755453
theorem B503651 : Blo 499793 503651 := bstep (se 1 (by rfl) ⟨377738, by rfl⟩ : syracuseStep 503651 = 755477) B755477
theorem B2142065 : Blo 499793 2142065 := bstep (se 2 (by rfl) ⟨803274, by rfl⟩ : syracuseStep 2142065 = 1606549) B1606549
theorem B503667 : Blo 499793 503667 := bstep (se 1 (by rfl) ⟨377750, by rfl⟩ : syracuseStep 503667 = 755501) B755501
theorem B503683 : Blo 499793 503683 := bstep (se 1 (by rfl) ⟨377762, by rfl⟩ : syracuseStep 503683 = 755525) B755525
theorem B503699 : Blo 499793 503699 := bstep (se 1 (by rfl) ⟨377774, by rfl⟩ : syracuseStep 503699 = 755549) B755549
theorem B503715 : Blo 499793 503715 := bstep (se 1 (by rfl) ⟨377786, by rfl⟩ : syracuseStep 503715 = 755573) B755573
theorem B2895793 : Blo 499793 2895793 := bstep (se 2 (by rfl) ⟨1085922, by rfl⟩ : syracuseStep 2895793 = 2171845) B2171845
theorem B503731 : Blo 499793 503731 := bstep (se 1 (by rfl) ⟨377798, by rfl⟩ : syracuseStep 503731 = 755597) B755597
theorem B503747 : Blo 499793 503747 := bstep (se 1 (by rfl) ⟨377810, by rfl⟩ : syracuseStep 503747 = 755621) B755621
theorem B503763 : Blo 499793 503763 := bstep (se 1 (by rfl) ⟨377822, by rfl⟩ : syracuseStep 503763 = 755645) B755645
theorem B503779 : Blo 499793 503779 := bstep (se 1 (by rfl) ⟨377834, by rfl⟩ : syracuseStep 503779 = 755669) B755669
theorem B1126385 : Blo 499793 1126385 := bstep (se 2 (by rfl) ⟨422394, by rfl⟩ : syracuseStep 1126385 = 844789) B844789
theorem B1126403 : Blo 499793 1126403 := bstep (se 1 (by rfl) ⟨844802, by rfl⟩ : syracuseStep 1126403 = 1689605) B1689605
theorem B3420229 : Blo 499793 3420229 := bstep (se 4 (by rfl) ⟨320646, by rfl⟩ : syracuseStep 3420229 = 641293) B641293
theorem B634979 : Blo 499793 634979 := bstep (se 1 (by rfl) ⟨476234, by rfl⟩ : syracuseStep 634979 = 952469) B952469
theorem B536755 : Blo 499793 536755 := bstep (se 1 (by rfl) ⟨402566, by rfl⟩ : syracuseStep 536755 = 805133) B805133
theorem B1126673 : Blo 499793 1126673 := bstep (se 2 (by rfl) ⟨422502, by rfl⟩ : syracuseStep 1126673 = 845005) B845005
theorem B1126691 : Blo 499793 1126691 := bstep (se 1 (by rfl) ⟨845018, by rfl⟩ : syracuseStep 1126691 = 1690037) B1690037
theorem B1126961 : Blo 499793 1126961 := bstep (se 2 (by rfl) ⟨422610, by rfl⟩ : syracuseStep 1126961 = 845221) B845221
theorem B1028675 : Blo 499793 1028675 := bstep (se 1 (by rfl) ⟨771506, by rfl⟩ : syracuseStep 1028675 = 1543013) B1543013
theorem B1126979 : Blo 499793 1126979 := bstep (se 1 (by rfl) ⟨845234, by rfl⟩ : syracuseStep 1126979 = 1690469) B1690469
theorem B635683 : Blo 499793 635683 := bstep (se 1 (by rfl) ⟨476762, by rfl⟩ : syracuseStep 635683 = 953525) B953525
theorem B1127249 : Blo 499793 1127249 := bstep (se 2 (by rfl) ⟨422718, by rfl⟩ : syracuseStep 1127249 = 845437) B845437
theorem B1127267 : Blo 499793 1127267 := bstep (se 1 (by rfl) ⟨845450, by rfl⟩ : syracuseStep 1127267 = 1690901) B1690901
theorem B635779 : Blo 499793 635779 := bstep (se 1 (by rfl) ⟨476834, by rfl⟩ : syracuseStep 635779 = 953669) B953669
theorem B2536433 : Blo 499793 2536433 := bstep (se 2 (by rfl) ⟨951162, by rfl⟩ : syracuseStep 2536433 = 1902325) B1902325
theorem B537635 : Blo 499793 537635 := bstep (se 1 (by rfl) ⟨403226, by rfl⟩ : syracuseStep 537635 = 806453) B806453
theorem B1127537 : Blo 499793 1127537 := bstep (se 2 (by rfl) ⟨422826, by rfl⟩ : syracuseStep 1127537 = 845653) B845653
theorem B1127555 : Blo 499793 1127555 := bstep (se 1 (by rfl) ⟨845666, by rfl⟩ : syracuseStep 1127555 = 1691333) B1691333
theorem B1356931 : Blo 499793 1356931 := bstep (se 1 (by rfl) ⟨1017698, by rfl⟩ : syracuseStep 1356931 = 2035397) B2035397
theorem B537763 : Blo 499793 537763 := bstep (se 1 (by rfl) ⟨403322, by rfl⟩ : syracuseStep 537763 = 806645) B806645
theorem B603379 : Blo 499793 603379 := bstep (se 1 (by rfl) ⟨452534, by rfl⟩ : syracuseStep 603379 = 905069) B905069
theorem B636275 : Blo 499793 636275 := bstep (se 1 (by rfl) ⟨477206, by rfl⟩ : syracuseStep 636275 = 954413) B954413
theorem B1127825 : Blo 499793 1127825 := bstep (se 2 (by rfl) ⟨422934, by rfl⟩ : syracuseStep 1127825 = 845869) B845869
theorem B1127843 : Blo 499793 1127843 := bstep (se 1 (by rfl) ⟨845882, by rfl⟩ : syracuseStep 1127843 = 1691765) B1691765
theorem B2176561 : Blo 499793 2176561 := bstep (se 2 (by rfl) ⟨816210, by rfl⟩ : syracuseStep 2176561 = 1632421) B1632421
theorem B1128113 : Blo 499793 1128113 := bstep (se 2 (by rfl) ⟨423042, by rfl⟩ : syracuseStep 1128113 = 846085) B846085
theorem B1128131 : Blo 499793 1128131 := bstep (se 1 (by rfl) ⟨846098, by rfl⟩ : syracuseStep 1128131 = 1692197) B1692197
theorem B4830947 : Blo 499793 4830947 := bstep (se 1 (by rfl) ⟨3623210, by rfl⟩ : syracuseStep 4830947 = 7246421) B7246421
theorem B800609 : Blo 499793 800609 := bstep (se 2 (by rfl) ⟨300228, by rfl⟩ : syracuseStep 800609 = 600457) B600457
theorem B1226627 : Blo 499793 1226627 := bstep (se 1 (by rfl) ⟨919970, by rfl⟩ : syracuseStep 1226627 = 1839941) B1839941
theorem B1128401 : Blo 499793 1128401 := bstep (se 2 (by rfl) ⟨423150, by rfl⟩ : syracuseStep 1128401 = 846301) B846301
theorem B1128419 : Blo 499793 1128419 := bstep (se 1 (by rfl) ⟨846314, by rfl⟩ : syracuseStep 1128419 = 1692629) B1692629
theorem B636979 : Blo 499793 636979 := bstep (se 1 (by rfl) ⟨477734, by rfl⟩ : syracuseStep 636979 = 955469) B955469
theorem B1521731 : Blo 499793 1521731 := bstep (se 1 (by rfl) ⟨1141298, by rfl⟩ : syracuseStep 1521731 = 2282597) B2282597
theorem B637075 : Blo 499793 637075 := bstep (se 1 (by rfl) ⟨477806, by rfl⟩ : syracuseStep 637075 = 955613) B955613
theorem B1423601 : Blo 499793 1423601 := bstep (se 2 (by rfl) ⟨533850, by rfl⟩ : syracuseStep 1423601 = 1067701) B1067701
theorem B1128689 : Blo 499793 1128689 := bstep (se 2 (by rfl) ⟨423258, by rfl⟩ : syracuseStep 1128689 = 846517) B846517
theorem B1128707 : Blo 499793 1128707 := bstep (se 1 (by rfl) ⟨846530, by rfl⟩ : syracuseStep 1128707 = 1693061) B1693061
theorem B2537891 : Blo 499793 2537891 := bstep (se 1 (by rfl) ⟨1903418, by rfl⟩ : syracuseStep 2537891 = 3806837) B3806837
theorem B1522147 : Blo 499793 1522147 := bstep (se 1 (by rfl) ⟨1141610, by rfl⟩ : syracuseStep 1522147 = 2283221) B2283221
theorem B1128977 : Blo 499793 1128977 := bstep (se 2 (by rfl) ⟨423366, by rfl⟩ : syracuseStep 1128977 = 846733) B846733
theorem B1161745 : Blo 499793 1161745 := bstep (se 2 (by rfl) ⟨435654, by rfl⟩ : syracuseStep 1161745 = 871309) B871309
theorem B1128995 : Blo 499793 1128995 := bstep (se 1 (by rfl) ⟨846746, by rfl⟩ : syracuseStep 1128995 = 1693493) B1693493
theorem B1358435 : Blo 499793 1358435 := bstep (se 1 (by rfl) ⟨1018826, by rfl⟩ : syracuseStep 1358435 = 2037653) B2037653
theorem B637571 : Blo 499793 637571 := bstep (se 1 (by rfl) ⟨478178, by rfl⟩ : syracuseStep 637571 = 956357) B956357
theorem B3062533 : Blo 499793 3062533 := bstep (se 4 (by rfl) ⟨287112, by rfl⟩ : syracuseStep 3062533 = 574225) B574225
theorem B2145037 : Blo 499793 2145037 := bstep (se 3 (by rfl) ⟨402194, by rfl⟩ : syracuseStep 2145037 = 804389) B804389
theorem B572179 : Blo 499793 572179 := bstep (se 1 (by rfl) ⟨429134, by rfl⟩ : syracuseStep 572179 = 858269) B858269
theorem B1129265 : Blo 499793 1129265 := bstep (se 2 (by rfl) ⟨423474, by rfl⟩ : syracuseStep 1129265 = 846949) B846949
theorem B1129283 : Blo 499793 1129283 := bstep (se 1 (by rfl) ⟨846962, by rfl⟩ : syracuseStep 1129283 = 1693925) B1693925
theorem B801667 : Blo 499793 801667 := bstep (se 1 (by rfl) ⟨601250, by rfl⟩ : syracuseStep 801667 = 1202501) B1202501
theorem B1129553 : Blo 499793 1129553 := bstep (se 2 (by rfl) ⟨423582, by rfl⟩ : syracuseStep 1129553 = 847165) B847165
theorem B736337 : Blo 499793 736337 := bstep (se 2 (by rfl) ⟨276126, by rfl⟩ : syracuseStep 736337 = 552253) B552253
theorem B1129571 : Blo 499793 1129571 := bstep (se 1 (by rfl) ⟨847178, by rfl⟩ : syracuseStep 1129571 = 1694357) B1694357
theorem B2145379 : Blo 499793 2145379 := bstep (se 1 (by rfl) ⟨1609034, by rfl⟩ : syracuseStep 2145379 = 3218069) B3218069
theorem B3619981 : Blo 499793 3619981 := bstep (se 3 (by rfl) ⟨678746, by rfl⟩ : syracuseStep 3619981 = 1357493) B1357493
theorem B1424557 : Blo 499793 1424557 := bstep (se 3 (by rfl) ⟨267104, by rfl⟩ : syracuseStep 1424557 = 534209) B534209
theorem B2538701 : Blo 499793 2538701 := bstep (se 3 (by rfl) ⟨476006, by rfl⟩ : syracuseStep 2538701 = 952013) B952013
theorem B1686851 : Blo 499793 1686851 := bstep (se 1 (by rfl) ⟨1265138, by rfl⟩ : syracuseStep 1686851 = 2530277) B2530277
theorem B1129841 : Blo 499793 1129841 := bstep (se 2 (by rfl) ⟨423690, by rfl⟩ : syracuseStep 1129841 = 847381) B847381
theorem B1129859 : Blo 499793 1129859 := bstep (se 1 (by rfl) ⟨847394, by rfl⟩ : syracuseStep 1129859 = 1694789) B1694789
theorem B1424785 : Blo 499793 1424785 := bstep (se 2 (by rfl) ⟨534294, by rfl⟩ : syracuseStep 1424785 = 1068589) B1068589
theorem B1424945 : Blo 499793 1424945 := bstep (se 2 (by rfl) ⟨534354, by rfl⟩ : syracuseStep 1424945 = 1068709) B1068709
theorem B1687121 : Blo 499793 1687121 := bstep (se 2 (by rfl) ⟨632670, by rfl⟩ : syracuseStep 1687121 = 1265341) B1265341
theorem B1130129 : Blo 499793 1130129 := bstep (se 2 (by rfl) ⟨423798, by rfl⟩ : syracuseStep 1130129 = 847597) B847597
theorem B1425059 : Blo 499793 1425059 := bstep (se 1 (by rfl) ⟨1068794, by rfl⟩ : syracuseStep 1425059 = 2137589) B2137589
theorem B1130147 : Blo 499793 1130147 := bstep (se 1 (by rfl) ⟨847610, by rfl⟩ : syracuseStep 1130147 = 1695221) B1695221
theorem B802595 : Blo 499793 802595 := bstep (se 1 (by rfl) ⟨601946, by rfl⟩ : syracuseStep 802595 = 1203893) B1203893
theorem B2867021 : Blo 499793 2867021 := bstep (se 3 (by rfl) ⟨537566, by rfl⟩ : syracuseStep 2867021 = 1075133) B1075133
theorem B1130417 : Blo 499793 1130417 := bstep (se 2 (by rfl) ⟨423906, by rfl⟩ : syracuseStep 1130417 = 847813) B847813
theorem B1130435 : Blo 499793 1130435 := bstep (se 1 (by rfl) ⟨847826, by rfl⟩ : syracuseStep 1130435 = 1695653) B1695653
theorem B802865 : Blo 499793 802865 := bstep (se 2 (by rfl) ⟨301074, by rfl⟩ : syracuseStep 802865 = 602149) B602149
theorem B1687661 : Blo 499793 1687661 := bstep (se 3 (by rfl) ⟨316436, by rfl⟩ : syracuseStep 1687661 = 632873) B632873
theorem B1687715 : Blo 499793 1687715 := bstep (se 1 (by rfl) ⟨1265786, by rfl⟩ : syracuseStep 1687715 = 2531573) B2531573
theorem B966851 : Blo 499793 966851 := bstep (se 1 (by rfl) ⟨725138, by rfl⟩ : syracuseStep 966851 = 1450277) B1450277
theorem B1130705 : Blo 499793 1130705 := bstep (se 2 (by rfl) ⟨424014, by rfl⟩ : syracuseStep 1130705 = 848029) B848029
theorem B1130723 : Blo 499793 1130723 := bstep (se 1 (by rfl) ⟨848042, by rfl⟩ : syracuseStep 1130723 = 1696085) B1696085
theorem B803153 : Blo 499793 803153 := bstep (se 2 (by rfl) ⟨301182, by rfl⟩ : syracuseStep 803153 = 602365) B602365
theorem B1687985 : Blo 499793 1687985 := bstep (se 2 (by rfl) ⟨632994, by rfl⟩ : syracuseStep 1687985 = 1265989) B1265989
theorem B1130993 : Blo 499793 1130993 := bstep (se 2 (by rfl) ⟨424122, by rfl⟩ : syracuseStep 1130993 = 848245) B848245
theorem B1131011 : Blo 499793 1131011 := bstep (se 1 (by rfl) ⟨848258, by rfl⟩ : syracuseStep 1131011 = 1696517) B1696517
theorem B1426061 : Blo 499793 1426061 := bstep (se 3 (by rfl) ⟨267386, by rfl⟩ : syracuseStep 1426061 = 534773) B534773
theorem B6439621 : Blo 499793 6439621 := bstep (se 4 (by rfl) ⟨603714, by rfl⟩ : syracuseStep 6439621 = 1207429) B1207429
theorem B803569 : Blo 499793 803569 := bstep (se 2 (by rfl) ⟨301338, by rfl⟩ : syracuseStep 803569 = 602677) B602677
theorem B1131281 : Blo 499793 1131281 := bstep (se 2 (by rfl) ⟨424230, by rfl⟩ : syracuseStep 1131281 = 848461) B848461
theorem B1131299 : Blo 499793 1131299 := bstep (se 1 (by rfl) ⟨848474, by rfl⟩ : syracuseStep 1131299 = 1696949) B1696949
theorem B1426243 : Blo 499793 1426243 := bstep (se 1 (by rfl) ⟨1069682, by rfl⟩ : syracuseStep 1426243 = 2139365) B2139365
theorem B1360739 : Blo 499793 1360739 := bstep (se 1 (by rfl) ⟨1020554, by rfl⟩ : syracuseStep 1360739 = 2041109) B2041109
theorem B1688525 : Blo 499793 1688525 := bstep (se 3 (by rfl) ⟨316598, by rfl⟩ : syracuseStep 1688525 = 633197) B633197
theorem B1426403 : Blo 499793 1426403 := bstep (se 1 (by rfl) ⟨1069802, by rfl⟩ : syracuseStep 1426403 = 2139605) B2139605
theorem B1360867 : Blo 499793 1360867 := bstep (se 1 (by rfl) ⟨1020650, by rfl⟩ : syracuseStep 1360867 = 2041301) B2041301
theorem B1688579 : Blo 499793 1688579 := bstep (se 1 (by rfl) ⟨1266434, by rfl⟩ : syracuseStep 1688579 = 2532869) B2532869
theorem B1131569 : Blo 499793 1131569 := bstep (se 2 (by rfl) ⟨424338, by rfl⟩ : syracuseStep 1131569 = 848677) B848677
theorem B1131587 : Blo 499793 1131587 := bstep (se 1 (by rfl) ⟨848690, by rfl⟩ : syracuseStep 1131587 = 1697381) B1697381
theorem B1688849 : Blo 499793 1688849 := bstep (se 2 (by rfl) ⟨633318, by rfl⟩ : syracuseStep 1688849 = 1266637) B1266637
theorem B1131857 : Blo 499793 1131857 := bstep (se 2 (by rfl) ⟨424446, by rfl⟩ : syracuseStep 1131857 = 848893) B848893
theorem B1131875 : Blo 499793 1131875 := bstep (se 1 (by rfl) ⟨848906, by rfl⟩ : syracuseStep 1131875 = 1697813) B1697813
theorem B902531 : Blo 499793 902531 := bstep (se 1 (by rfl) ⟨676898, by rfl⟩ : syracuseStep 902531 = 1353797) B1353797
theorem B2606627 : Blo 499793 2606627 := bstep (se 1 (by rfl) ⟨1954970, by rfl⟩ : syracuseStep 2606627 = 3909941) B3909941
theorem B1132145 : Blo 499793 1132145 := bstep (se 2 (by rfl) ⟨424554, by rfl⟩ : syracuseStep 1132145 = 849109) B849109
theorem B804467 : Blo 499793 804467 := bstep (se 1 (by rfl) ⟨603350, by rfl⟩ : syracuseStep 804467 = 1206701) B1206701
theorem B1132163 : Blo 499793 1132163 := bstep (se 1 (by rfl) ⟨849122, by rfl⟩ : syracuseStep 1132163 = 1698245) B1698245
theorem B5719733 : Blo 499793 5719733 := bstep (se 5 (by rfl) ⟨268112, by rfl⟩ : syracuseStep 5719733 = 536225) B536225
theorem B15255317 : Blo 499793 15255317 := bstep (se 6 (by rfl) ⟨357546, by rfl⟩ : syracuseStep 15255317 = 715093) B715093
theorem B968483 : Blo 499793 968483 := bstep (se 1 (by rfl) ⟨726362, by rfl⟩ : syracuseStep 968483 = 1452725) B1452725
theorem B1689389 : Blo 499793 1689389 := bstep (se 3 (by rfl) ⟨316760, by rfl⟩ : syracuseStep 1689389 = 633521) B633521
theorem B804691 : Blo 499793 804691 := bstep (se 1 (by rfl) ⟨603518, by rfl⟩ : syracuseStep 804691 = 1207037) B1207037
theorem B1689443 : Blo 499793 1689443 := bstep (se 1 (by rfl) ⟨1267082, by rfl⟩ : syracuseStep 1689443 = 2534165) B2534165
theorem B1132433 : Blo 499793 1132433 := bstep (se 2 (by rfl) ⟨424662, by rfl⟩ : syracuseStep 1132433 = 849325) B849325
theorem B1132451 : Blo 499793 1132451 := bstep (se 1 (by rfl) ⟨849338, by rfl⟩ : syracuseStep 1132451 = 1698677) B1698677
theorem B2869253 : Blo 499793 2869253 := bstep (se 4 (by rfl) ⟨268992, by rfl⟩ : syracuseStep 2869253 = 537985) B537985
theorem B1427473 : Blo 499793 1427473 := bstep (se 2 (by rfl) ⟨535302, by rfl⟩ : syracuseStep 1427473 = 1070605) B1070605
theorem B2541617 : Blo 499793 2541617 := bstep (se 2 (by rfl) ⟨953106, by rfl⟩ : syracuseStep 2541617 = 1906213) B1906213
theorem B1689713 : Blo 499793 1689713 := bstep (se 2 (by rfl) ⟨633642, by rfl⟩ : syracuseStep 1689713 = 1267285) B1267285
theorem B1132721 : Blo 499793 1132721 := bstep (se 2 (by rfl) ⟨424770, by rfl⟩ : syracuseStep 1132721 = 849541) B849541
theorem B1132739 : Blo 499793 1132739 := bstep (se 1 (by rfl) ⟨849554, by rfl⟩ : syracuseStep 1132739 = 1699109) B1699109
theorem B1133009 : Blo 499793 1133009 := bstep (se 2 (by rfl) ⟨424878, by rfl⟩ : syracuseStep 1133009 = 849757) B849757
theorem B1133027 : Blo 499793 1133027 := bstep (se 1 (by rfl) ⟨849770, by rfl⟩ : syracuseStep 1133027 = 1699541) B1699541
theorem B510451 : Blo 499793 510451 := bstep (se 1 (by rfl) ⟨382838, by rfl⟩ : syracuseStep 510451 = 765677) B765677
theorem B1690253 : Blo 499793 1690253 := bstep (se 3 (by rfl) ⟨316922, by rfl⟩ : syracuseStep 1690253 = 633845) B633845
theorem B1690307 : Blo 499793 1690307 := bstep (se 1 (by rfl) ⟨1267730, by rfl⟩ : syracuseStep 1690307 = 2535461) B2535461
theorem B1133297 : Blo 499793 1133297 := bstep (se 2 (by rfl) ⟨424986, by rfl⟩ : syracuseStep 1133297 = 849973) B849973
theorem B1133315 : Blo 499793 1133315 := bstep (se 1 (by rfl) ⟨849986, by rfl⟩ : syracuseStep 1133315 = 1699973) B1699973
theorem B805697 : Blo 499793 805697 := bstep (se 2 (by rfl) ⟨302136, by rfl⟩ : syracuseStep 805697 = 604273) B604273
theorem B4279139 : Blo 499793 4279139 := bstep (se 1 (by rfl) ⟨3209354, by rfl⟩ : syracuseStep 4279139 = 6418709) B6418709
theorem B1690577 : Blo 499793 1690577 := bstep (se 2 (by rfl) ⟨633966, by rfl⟩ : syracuseStep 1690577 = 1267933) B1267933
theorem B805889 : Blo 499793 805889 := bstep (se 2 (by rfl) ⟨302208, by rfl⟩ : syracuseStep 805889 = 604417) B604417
theorem B2149411 : Blo 499793 2149411 := bstep (se 1 (by rfl) ⟨1612058, by rfl⟩ : syracuseStep 2149411 = 3224117) B3224117
theorem B11586673 : Blo 499793 11586673 := bstep (se 2 (by rfl) ⟨4345002, by rfl⟩ : syracuseStep 11586673 = 8690005) B8690005
theorem B1428749 : Blo 499793 1428749 := bstep (se 3 (by rfl) ⟨267890, by rfl⟩ : syracuseStep 1428749 = 535781) B535781
theorem B2280845 : Blo 499793 2280845 := bstep (se 3 (by rfl) ⟨427658, by rfl⟩ : syracuseStep 2280845 = 855317) B855317
theorem B1428931 : Blo 499793 1428931 := bstep (se 1 (by rfl) ⟨1071698, by rfl⟩ : syracuseStep 1428931 = 2143397) B2143397
theorem B2543075 : Blo 499793 2543075 := bstep (se 1 (by rfl) ⟨1907306, by rfl⟩ : syracuseStep 2543075 = 3814613) B3814613
theorem B1691117 : Blo 499793 1691117 := bstep (se 3 (by rfl) ⟨317084, by rfl⟩ : syracuseStep 1691117 = 634169) B634169
theorem B1428977 : Blo 499793 1428977 := bstep (se 2 (by rfl) ⟨535866, by rfl⟩ : syracuseStep 1428977 = 1071733) B1071733
theorem B1068547 : Blo 499793 1068547 := bstep (se 1 (by rfl) ⟨801410, by rfl⟩ : syracuseStep 1068547 = 1602821) B1602821
theorem B871939 : Blo 499793 871939 := bstep (se 1 (by rfl) ⟨653954, by rfl⟩ : syracuseStep 871939 = 1307909) B1307909
theorem B1691171 : Blo 499793 1691171 := bstep (se 1 (by rfl) ⟨1268378, by rfl⟩ : syracuseStep 1691171 = 2536757) B2536757
theorem B1756835 : Blo 499793 1756835 := bstep (se 1 (by rfl) ⟨1317626, by rfl⟩ : syracuseStep 1756835 = 2635253) B2635253
theorem B4181701 : Blo 499793 4181701 := bstep (se 4 (by rfl) ⟨392034, by rfl⟩ : syracuseStep 4181701 = 784069) B784069
theorem B1691441 : Blo 499793 1691441 := bstep (se 2 (by rfl) ⟨634290, by rfl⟩ : syracuseStep 1691441 = 1268581) B1268581
theorem B2477873 : Blo 499793 2477873 := bstep (se 2 (by rfl) ⟨929202, by rfl⟩ : syracuseStep 2477873 = 1858405) B1858405
theorem B1265777 : Blo 499793 1265777 := bstep (se 2 (by rfl) ⟨474666, by rfl⟩ : syracuseStep 1265777 = 949333) B949333
theorem B1265827 : Blo 499793 1265827 := bstep (se 1 (by rfl) ⟨949370, by rfl⟩ : syracuseStep 1265827 = 1898741) B1898741
theorem B905393 : Blo 499793 905393 := bstep (se 2 (by rfl) ⟨339522, by rfl⟩ : syracuseStep 905393 = 679045) B679045
theorem B2150641 : Blo 499793 2150641 := bstep (se 2 (by rfl) ⟨806490, by rfl⟩ : syracuseStep 2150641 = 1612981) B1612981
theorem B2543885 : Blo 499793 2543885 := bstep (se 3 (by rfl) ⟨476978, by rfl⟩ : syracuseStep 2543885 = 953957) B953957
theorem B1265969 : Blo 499793 1265969 := bstep (se 2 (by rfl) ⟨474738, by rfl⟩ : syracuseStep 1265969 = 949477) B949477
theorem B1691981 : Blo 499793 1691981 := bstep (se 3 (by rfl) ⟨317246, by rfl⟩ : syracuseStep 1691981 = 634493) B634493
theorem B2412899 : Blo 499793 2412899 := bstep (se 1 (by rfl) ⟨1809674, by rfl⟩ : syracuseStep 2412899 = 3619349) B3619349
theorem B1692035 : Blo 499793 1692035 := bstep (se 1 (by rfl) ⟨1269026, by rfl⟩ : syracuseStep 1692035 = 2538053) B2538053
theorem B14471621 : Blo 499793 14471621 := bstep (se 4 (by rfl) ⟨1356714, by rfl⟩ : syracuseStep 14471621 = 2713429) B2713429
theorem B1692305 : Blo 499793 1692305 := bstep (se 2 (by rfl) ⟨634614, by rfl⟩ : syracuseStep 1692305 = 1269229) B1269229
theorem B1069777 : Blo 499793 1069777 := bstep (se 2 (by rfl) ⟨401166, by rfl⟩ : syracuseStep 1069777 = 802333) B802333
theorem B10277603 : Blo 499793 10277603 := bstep (se 1 (by rfl) ⟨7708202, by rfl⟩ : syracuseStep 10277603 = 15416405) B15416405
theorem B1430435 : Blo 499793 1430435 := bstep (se 1 (by rfl) ⟨1072826, by rfl⟩ : syracuseStep 1430435 = 2145653) B2145653
theorem B3625955 : Blo 499793 3625955 := bstep (se 1 (by rfl) ⟨2719466, by rfl⟩ : syracuseStep 3625955 = 5438933) B5438933
theorem B1528931 : Blo 499793 1528931 := bstep (se 1 (by rfl) ⟨1146698, by rfl⟩ : syracuseStep 1528931 = 2293397) B2293397
theorem B1692845 : Blo 499793 1692845 := bstep (se 3 (by rfl) ⟨317408, by rfl⟩ : syracuseStep 1692845 = 634817) B634817
theorem B1692899 : Blo 499793 1692899 := bstep (se 1 (by rfl) ⟨1269674, by rfl⟩ : syracuseStep 1692899 = 2539349) B2539349
theorem B1266961 : Blo 499793 1266961 := bstep (se 2 (by rfl) ⟨475110, by rfl⟩ : syracuseStep 1266961 = 950221) B950221
theorem B1070435 : Blo 499793 1070435 := bstep (se 1 (by rfl) ⟨802826, by rfl⟩ : syracuseStep 1070435 = 1605653) B1605653
theorem B5133709 : Blo 499793 5133709 := bstep (se 3 (by rfl) ⟨962570, by rfl⟩ : syracuseStep 5133709 = 1925141) B1925141
theorem B1693169 : Blo 499793 1693169 := bstep (se 2 (by rfl) ⟨634938, by rfl⟩ : syracuseStep 1693169 = 1269877) B1269877
theorem B1267235 : Blo 499793 1267235 := bstep (se 1 (by rfl) ⟨950426, by rfl⟩ : syracuseStep 1267235 = 1900853) B1900853
theorem B2414243 : Blo 499793 2414243 := bstep (se 1 (by rfl) ⟨1810682, by rfl⟩ : syracuseStep 2414243 = 3621365) B3621365
theorem B1267427 : Blo 499793 1267427 := bstep (se 1 (by rfl) ⟨950570, by rfl⟩ : syracuseStep 1267427 = 1901141) B1901141
theorem B907043 : Blo 499793 907043 := bstep (se 1 (by rfl) ⟨680282, by rfl⟩ : syracuseStep 907043 = 1360565) B1360565
theorem B677731 : Blo 499793 677731 := bstep (se 1 (by rfl) ⟨508298, by rfl⟩ : syracuseStep 677731 = 1016597) B1016597
theorem B6510449 : Blo 499793 6510449 := bstep (se 2 (by rfl) ⟨2441418, by rfl⟩ : syracuseStep 6510449 = 4882837) B4882837
theorem B677795 : Blo 499793 677795 := bstep (se 1 (by rfl) ⟨508346, by rfl⟩ : syracuseStep 677795 = 1016693) B1016693
theorem B1693709 : Blo 499793 1693709 := bstep (se 3 (by rfl) ⟨317570, by rfl⟩ : syracuseStep 1693709 = 635141) B635141
theorem B1693763 : Blo 499793 1693763 := bstep (se 1 (by rfl) ⟨1270322, by rfl⟩ : syracuseStep 1693763 = 2540645) B2540645
theorem B1431665 : Blo 499793 1431665 := bstep (se 2 (by rfl) ⟨536874, by rfl⟩ : syracuseStep 1431665 = 1073749) B1073749
theorem B1071281 : Blo 499793 1071281 := bstep (se 2 (by rfl) ⟨401730, by rfl⟩ : syracuseStep 1071281 = 803461) B803461
theorem B2087117 : Blo 499793 2087117 := bstep (se 3 (by rfl) ⟨391334, by rfl⟩ : syracuseStep 2087117 = 782669) B782669
theorem B1694033 : Blo 499793 1694033 := bstep (se 2 (by rfl) ⟨635262, by rfl⟩ : syracuseStep 1694033 = 1270525) B1270525
theorem B1268369 : Blo 499793 1268369 := bstep (se 2 (by rfl) ⟨475638, by rfl⟩ : syracuseStep 1268369 = 951277) B951277
theorem B1268419 : Blo 499793 1268419 := bstep (se 1 (by rfl) ⟨951314, by rfl⟩ : syracuseStep 1268419 = 1902629) B1902629
theorem B613171 : Blo 499793 613171 := bstep (se 1 (by rfl) ⟨459878, by rfl⟩ : syracuseStep 613171 = 919757) B919757
theorem B1268561 : Blo 499793 1268561 := bstep (se 2 (by rfl) ⟨475710, by rfl⟩ : syracuseStep 1268561 = 951421) B951421
theorem B6970211 : Blo 499793 6970211 := bstep (se 1 (by rfl) ⟨5227658, by rfl⟩ : syracuseStep 6970211 = 10455317) B10455317
theorem B1694573 : Blo 499793 1694573 := bstep (se 3 (by rfl) ⟨317732, by rfl⟩ : syracuseStep 1694573 = 635465) B635465
theorem B1694627 : Blo 499793 1694627 := bstep (se 1 (by rfl) ⟨1270970, by rfl⟩ : syracuseStep 1694627 = 2541941) B2541941
theorem B9428021 : Blo 499793 9428021 := bstep (se 5 (by rfl) ⟨441938, by rfl⟩ : syracuseStep 9428021 = 883877) B883877
theorem B1203299 : Blo 499793 1203299 := bstep (se 1 (by rfl) ⟨902474, by rfl⟩ : syracuseStep 1203299 = 1804949) B1804949
theorem B2546801 : Blo 499793 2546801 := bstep (se 2 (by rfl) ⟨955050, by rfl⟩ : syracuseStep 2546801 = 1910101) B1910101
theorem B1694897 : Blo 499793 1694897 := bstep (se 2 (by rfl) ⟨635586, by rfl⟩ : syracuseStep 1694897 = 1271173) B1271173
theorem B711937 : Blo 499793 711937 := bstep (se 2 (by rfl) ⟨266976, by rfl⟩ : syracuseStep 711937 = 533953) B533953
theorem B2416013 : Blo 499793 2416013 := bstep (se 3 (by rfl) ⟨453002, by rfl⟩ : syracuseStep 2416013 = 906005) B906005
theorem B1433123 : Blo 499793 1433123 := bstep (se 1 (by rfl) ⟨1074842, by rfl⟩ : syracuseStep 1433123 = 2149685) B2149685
theorem B1564337 : Blo 499793 1564337 := bstep (se 2 (by rfl) ⟨586626, by rfl⟩ : syracuseStep 1564337 = 1173253) B1173253
theorem B1695437 : Blo 499793 1695437 := bstep (se 3 (by rfl) ⟨317894, by rfl⟩ : syracuseStep 1695437 = 635789) B635789
theorem B843473 : Blo 499793 843473 := bstep (se 2 (by rfl) ⟨316302, by rfl⟩ : syracuseStep 843473 = 632605) B632605
theorem B1695491 : Blo 499793 1695491 := bstep (se 1 (by rfl) ⟨1271618, by rfl⟩ : syracuseStep 1695491 = 2543237) B2543237
theorem B1269553 : Blo 499793 1269553 := bstep (se 2 (by rfl) ⟨476082, by rfl⟩ : syracuseStep 1269553 = 952165) B952165
theorem B1072963 : Blo 499793 1072963 := bstep (se 1 (by rfl) ⟨804722, by rfl⟩ : syracuseStep 1072963 = 1609445) B1609445
theorem B2973509 : Blo 499793 2973509 := bstep (se 4 (by rfl) ⟨278766, by rfl⟩ : syracuseStep 2973509 = 557533) B557533
theorem B843601 : Blo 499793 843601 := bstep (se 2 (by rfl) ⟨316350, by rfl⟩ : syracuseStep 843601 = 632701) B632701
theorem B843635 : Blo 499793 843635 := bstep (se 1 (by rfl) ⟨632726, by rfl⟩ : syracuseStep 843635 = 1265453) B1265453
theorem B712643 : Blo 499793 712643 := bstep (se 1 (by rfl) ⟨534482, by rfl⟩ : syracuseStep 712643 = 1068965) B1068965
theorem B843763 : Blo 499793 843763 := bstep (se 1 (by rfl) ⟨632822, by rfl⟩ : syracuseStep 843763 = 1265645) B1265645
theorem B1695761 : Blo 499793 1695761 := bstep (se 2 (by rfl) ⟨635910, by rfl⟩ : syracuseStep 1695761 = 1271821) B1271821
theorem B1269827 : Blo 499793 1269827 := bstep (se 1 (by rfl) ⟨952370, by rfl⟩ : syracuseStep 1269827 = 1904741) B1904741
theorem B4808803 : Blo 499793 4808803 := bstep (se 1 (by rfl) ⟨3606602, by rfl⟩ : syracuseStep 4808803 = 7213205) B7213205
theorem B843905 : Blo 499793 843905 := bstep (se 2 (by rfl) ⟨316464, by rfl⟩ : syracuseStep 843905 = 632929) B632929
theorem B6119621 : Blo 499793 6119621 := bstep (se 4 (by rfl) ⟨573714, by rfl⟩ : syracuseStep 6119621 = 1147429) B1147429
theorem B844033 : Blo 499793 844033 := bstep (se 2 (by rfl) ⟨316512, by rfl⟩ : syracuseStep 844033 = 633025) B633025
theorem B1270019 : Blo 499793 1270019 := bstep (se 1 (by rfl) ⟨952514, by rfl⟩ : syracuseStep 1270019 = 1905029) B1905029
theorem B1073425 : Blo 499793 1073425 := bstep (se 2 (by rfl) ⟨402534, by rfl⟩ : syracuseStep 1073425 = 805069) B805069
theorem B844067 : Blo 499793 844067 := bstep (se 1 (by rfl) ⟨633050, by rfl⟩ : syracuseStep 844067 = 1266101) B1266101
theorem B1433933 : Blo 499793 1433933 := bstep (se 3 (by rfl) ⟨268862, by rfl⟩ : syracuseStep 1433933 = 537725) B537725
theorem B844195 : Blo 499793 844195 := bstep (se 1 (by rfl) ⟨633146, by rfl⟩ : syracuseStep 844195 = 1266293) B1266293
theorem B1434125 : Blo 499793 1434125 := bstep (se 3 (by rfl) ⟨268898, by rfl⟩ : syracuseStep 1434125 = 537797) B537797
theorem B2548259 : Blo 499793 2548259 := bstep (se 1 (by rfl) ⟨1911194, by rfl⟩ : syracuseStep 2548259 = 3822389) B3822389
theorem B1696301 : Blo 499793 1696301 := bstep (se 3 (by rfl) ⟨318056, by rfl⟩ : syracuseStep 1696301 = 636113) B636113
theorem B844337 : Blo 499793 844337 := bstep (se 2 (by rfl) ⟨316626, by rfl⟩ : syracuseStep 844337 = 633253) B633253
theorem B713281 : Blo 499793 713281 := bstep (se 2 (by rfl) ⟨267480, by rfl⟩ : syracuseStep 713281 = 534961) B534961
theorem B1696355 : Blo 499793 1696355 := bstep (se 1 (by rfl) ⟨1272266, by rfl⟩ : syracuseStep 1696355 = 2544533) B2544533
theorem B844465 : Blo 499793 844465 := bstep (se 2 (by rfl) ⟨316674, by rfl⟩ : syracuseStep 844465 = 633349) B633349
theorem B713395 : Blo 499793 713395 := bstep (se 1 (by rfl) ⟨535046, by rfl⟩ : syracuseStep 713395 = 1070093) B1070093
theorem B1204931 : Blo 499793 1204931 := bstep (se 1 (by rfl) ⟨903698, by rfl⟩ : syracuseStep 1204931 = 1807397) B1807397
theorem B844499 : Blo 499793 844499 := bstep (se 1 (by rfl) ⟨633374, by rfl⟩ : syracuseStep 844499 = 1266749) B1266749
theorem B2450189 : Blo 499793 2450189 := bstep (se 3 (by rfl) ⟨459410, by rfl⟩ : syracuseStep 2450189 = 918821) B918821
theorem B844627 : Blo 499793 844627 := bstep (se 1 (by rfl) ⟨633470, by rfl⟩ : syracuseStep 844627 = 1266941) B1266941
theorem B1696625 : Blo 499793 1696625 := bstep (se 2 (by rfl) ⟨636234, by rfl⟩ : syracuseStep 1696625 = 1272469) B1272469
theorem B844769 : Blo 499793 844769 := bstep (se 2 (by rfl) ⟨316788, by rfl⟩ : syracuseStep 844769 = 633577) B633577
theorem B812035 : Blo 499793 812035 := bstep (se 1 (by rfl) ⟨609026, by rfl⟩ : syracuseStep 812035 = 1218053) B1218053
theorem B844897 : Blo 499793 844897 := bstep (se 2 (by rfl) ⟨316836, by rfl⟩ : syracuseStep 844897 = 633673) B633673
theorem B844931 : Blo 499793 844931 := bstep (se 1 (by rfl) ⟨633698, by rfl⟩ : syracuseStep 844931 = 1267397) B1267397
theorem B812195 : Blo 499793 812195 := bstep (se 1 (by rfl) ⟨609146, by rfl⟩ : syracuseStep 812195 = 1218293) B1218293
theorem B1270961 : Blo 499793 1270961 := bstep (se 2 (by rfl) ⟨476610, by rfl⟩ : syracuseStep 1270961 = 953221) B953221
theorem B1271011 : Blo 499793 1271011 := bstep (se 1 (by rfl) ⟨953258, by rfl⟩ : syracuseStep 1271011 = 1906517) B1906517
theorem B845059 : Blo 499793 845059 := bstep (se 1 (by rfl) ⟨633794, by rfl⟩ : syracuseStep 845059 = 1267589) B1267589
theorem B1074467 : Blo 499793 1074467 := bstep (se 1 (by rfl) ⟨805850, by rfl⟩ : syracuseStep 1074467 = 1611701) B1611701
theorem B2549069 : Blo 499793 2549069 := bstep (se 3 (by rfl) ⟨477950, by rfl⟩ : syracuseStep 2549069 = 955901) B955901
theorem B1271153 : Blo 499793 1271153 := bstep (se 2 (by rfl) ⟨476682, by rfl⟩ : syracuseStep 1271153 = 953365) B953365
theorem B1697165 : Blo 499793 1697165 := bstep (se 3 (by rfl) ⟨318218, by rfl⟩ : syracuseStep 1697165 = 636437) B636437
theorem B845201 : Blo 499793 845201 := bstep (se 2 (by rfl) ⟨316950, by rfl⟩ : syracuseStep 845201 = 633901) B633901
theorem B1697219 : Blo 499793 1697219 := bstep (se 1 (by rfl) ⟨1272914, by rfl⟩ : syracuseStep 1697219 = 2545829) B2545829
theorem B5694947 : Blo 499793 5694947 := bstep (se 1 (by rfl) ⟨4271210, by rfl⟩ : syracuseStep 5694947 = 8542421) B8542421
theorem B845329 : Blo 499793 845329 := bstep (se 2 (by rfl) ⟨316998, by rfl⟩ : syracuseStep 845329 = 633997) B633997
theorem B845363 : Blo 499793 845363 := bstep (se 1 (by rfl) ⟨634022, by rfl⟩ : syracuseStep 845363 = 1268045) B1268045
theorem B1631821 : Blo 499793 1631821 := bstep (se 3 (by rfl) ⟨305966, by rfl⟩ : syracuseStep 1631821 = 611933) B611933
theorem B845491 : Blo 499793 845491 := bstep (se 1 (by rfl) ⟨634118, by rfl⟩ : syracuseStep 845491 = 1268237) B1268237
theorem B1697489 : Blo 499793 1697489 := bstep (se 2 (by rfl) ⟨636558, by rfl⟩ : syracuseStep 1697489 = 1273117) B1273117
theorem B1631981 : Blo 499793 1631981 := bstep (se 3 (by rfl) ⟨305996, by rfl⟩ : syracuseStep 1631981 = 611993) B611993
theorem B1074979 : Blo 499793 1074979 := bstep (se 1 (by rfl) ⟨806234, by rfl⟩ : syracuseStep 1074979 = 1612469) B1612469
theorem B845633 : Blo 499793 845633 := bstep (se 2 (by rfl) ⟨317112, by rfl⟩ : syracuseStep 845633 = 634225) B634225
theorem B845761 : Blo 499793 845761 := bstep (se 2 (by rfl) ⟨317160, by rfl⟩ : syracuseStep 845761 = 634321) B634321
theorem B1632209 : Blo 499793 1632209 := bstep (se 2 (by rfl) ⟨612078, by rfl⟩ : syracuseStep 1632209 = 1224157) B1224157
theorem B845795 : Blo 499793 845795 := bstep (se 1 (by rfl) ⟨634346, by rfl⟩ : syracuseStep 845795 = 1268693) B1268693
theorem B714739 : Blo 499793 714739 := bstep (se 1 (by rfl) ⟨536054, by rfl⟩ : syracuseStep 714739 = 1072109) B1072109
theorem B813073 : Blo 499793 813073 := bstep (se 2 (by rfl) ⟨304902, by rfl⟩ : syracuseStep 813073 = 609805) B609805
theorem B1206353 : Blo 499793 1206353 := bstep (se 2 (by rfl) ⟨452382, by rfl⟩ : syracuseStep 1206353 = 904765) B904765
theorem B845923 : Blo 499793 845923 := bstep (se 1 (by rfl) ⟨634442, by rfl⟩ : syracuseStep 845923 = 1268885) B1268885
theorem B813235 : Blo 499793 813235 := bstep (se 1 (by rfl) ⟨609926, by rfl⟩ : syracuseStep 813235 = 1219853) B1219853
theorem B1698029 : Blo 499793 1698029 := bstep (se 3 (by rfl) ⟨318380, by rfl⟩ : syracuseStep 1698029 = 636761) B636761
theorem B846065 : Blo 499793 846065 := bstep (se 2 (by rfl) ⟨317274, by rfl⟩ : syracuseStep 846065 = 634549) B634549
theorem B1698083 : Blo 499793 1698083 := bstep (se 1 (by rfl) ⟨1273562, by rfl⟩ : syracuseStep 1698083 = 2547125) B2547125
theorem B1272145 : Blo 499793 1272145 := bstep (se 2 (by rfl) ⟨477054, by rfl⟩ : syracuseStep 1272145 = 954109) B954109
theorem B846193 : Blo 499793 846193 := bstep (se 2 (by rfl) ⟨317322, by rfl⟩ : syracuseStep 846193 = 634645) B634645
theorem B846227 : Blo 499793 846227 := bstep (se 1 (by rfl) ⟨634670, by rfl⟩ : syracuseStep 846227 = 1269341) B1269341
theorem B1075697 : Blo 499793 1075697 := bstep (se 2 (by rfl) ⟨403386, by rfl⟩ : syracuseStep 1075697 = 806773) B806773
theorem B846355 : Blo 499793 846355 := bstep (se 1 (by rfl) ⟨634766, by rfl⟩ : syracuseStep 846355 = 1269533) B1269533
theorem B1698353 : Blo 499793 1698353 := bstep (se 2 (by rfl) ⟨636882, by rfl⟩ : syracuseStep 1698353 = 1273765) B1273765
theorem B1272419 : Blo 499793 1272419 := bstep (se 1 (by rfl) ⟨954314, by rfl⟩ : syracuseStep 1272419 = 1908629) B1908629
theorem B846497 : Blo 499793 846497 := bstep (se 2 (by rfl) ⟨317436, by rfl⟩ : syracuseStep 846497 = 634873) B634873
theorem B846625 : Blo 499793 846625 := bstep (se 2 (by rfl) ⟨317484, by rfl⟩ : syracuseStep 846625 = 634969) B634969
theorem B1272611 : Blo 499793 1272611 := bstep (se 1 (by rfl) ⟨954458, by rfl⟩ : syracuseStep 1272611 = 1908917) B1908917
theorem B846659 : Blo 499793 846659 := bstep (se 1 (by rfl) ⟨634994, by rfl⟩ : syracuseStep 846659 = 1269989) B1269989
theorem B3337037 : Blo 499793 3337037 := bstep (se 3 (by rfl) ⟨625694, by rfl⟩ : syracuseStep 3337037 = 1251389) B1251389
theorem B3206051 : Blo 499793 3206051 := bstep (se 1 (by rfl) ⟨2404538, by rfl⟩ : syracuseStep 3206051 = 4809077) B4809077
theorem B846787 : Blo 499793 846787 := bstep (se 1 (by rfl) ⟨635090, by rfl⟩ : syracuseStep 846787 = 1270181) B1270181
theorem B1698893 : Blo 499793 1698893 := bstep (se 3 (by rfl) ⟨318542, by rfl⟩ : syracuseStep 1698893 = 637085) B637085
theorem B846929 : Blo 499793 846929 := bstep (se 2 (by rfl) ⟨317598, by rfl⟩ : syracuseStep 846929 = 635197) B635197
theorem B715873 : Blo 499793 715873 := bstep (se 2 (by rfl) ⟨268452, by rfl⟩ : syracuseStep 715873 = 536905) B536905
theorem B945265 : Blo 499793 945265 := bstep (se 2 (by rfl) ⟨354474, by rfl⟩ : syracuseStep 945265 = 708949) B708949
theorem B1698947 : Blo 499793 1698947 := bstep (se 1 (by rfl) ⟨1274210, by rfl⟩ : syracuseStep 1698947 = 2548421) B2548421
theorem B715969 : Blo 499793 715969 := bstep (se 2 (by rfl) ⟨268488, by rfl⟩ : syracuseStep 715969 = 536977) B536977
theorem B847057 : Blo 499793 847057 := bstep (se 2 (by rfl) ⟨317646, by rfl⟩ : syracuseStep 847057 = 635293) B635293
theorem B847091 : Blo 499793 847091 := bstep (se 1 (by rfl) ⟨635318, by rfl⟩ : syracuseStep 847091 = 1270637) B1270637
theorem B13036913 : Blo 499793 13036913 := bstep (se 2 (by rfl) ⟨4888842, by rfl⟩ : syracuseStep 13036913 = 9777685) B9777685
theorem B847219 : Blo 499793 847219 := bstep (se 1 (by rfl) ⟨635414, by rfl⟩ : syracuseStep 847219 = 1270829) B1270829
theorem B1699217 : Blo 499793 1699217 := bstep (se 2 (by rfl) ⟨637206, by rfl⟩ : syracuseStep 1699217 = 1274413) B1274413
theorem B847361 : Blo 499793 847361 := bstep (se 2 (by rfl) ⟨317760, by rfl⟩ : syracuseStep 847361 = 635521) B635521
theorem B847489 : Blo 499793 847489 := bstep (se 2 (by rfl) ⟨317808, by rfl⟩ : syracuseStep 847489 = 635617) B635617
theorem B847523 : Blo 499793 847523 := bstep (se 1 (by rfl) ⟨635642, by rfl⟩ : syracuseStep 847523 = 1271285) B1271285
theorem B716465 : Blo 499793 716465 := bstep (se 2 (by rfl) ⟨268674, by rfl⟩ : syracuseStep 716465 = 537349) B537349
theorem B1273553 : Blo 499793 1273553 := bstep (se 2 (by rfl) ⟨477582, by rfl⟩ : syracuseStep 1273553 = 955165) B955165
theorem B1273603 : Blo 499793 1273603 := bstep (se 1 (by rfl) ⟨955202, by rfl⟩ : syracuseStep 1273603 = 1910405) B1910405
theorem B847651 : Blo 499793 847651 := bstep (se 1 (by rfl) ⟨635738, by rfl⟩ : syracuseStep 847651 = 1271477) B1271477
theorem B1273745 : Blo 499793 1273745 := bstep (se 2 (by rfl) ⟨477654, by rfl⟩ : syracuseStep 1273745 = 955309) B955309
theorem B1699757 : Blo 499793 1699757 := bstep (se 3 (by rfl) ⟨318704, by rfl⟩ : syracuseStep 1699757 = 637409) B637409
theorem B847793 : Blo 499793 847793 := bstep (se 2 (by rfl) ⟨317922, by rfl⟩ : syracuseStep 847793 = 635845) B635845
theorem B1699811 : Blo 499793 1699811 := bstep (se 1 (by rfl) ⟨1274858, by rfl⟩ : syracuseStep 1699811 = 2549717) B2549717
theorem B847921 : Blo 499793 847921 := bstep (se 2 (by rfl) ⟨317970, by rfl⟩ : syracuseStep 847921 = 635941) B635941
theorem B1601603 : Blo 499793 1601603 := bstep (se 1 (by rfl) ⟨1201202, by rfl⟩ : syracuseStep 1601603 = 2402405) B2402405
theorem B847955 : Blo 499793 847955 := bstep (se 1 (by rfl) ⟨635966, by rfl⟩ : syracuseStep 847955 = 1271933) B1271933
theorem B749699 : Blo 499793 749699 := bstep (se 1 (by rfl) ⟨562274, by rfl⟩ : syracuseStep 749699 = 1124549) B1124549
theorem B749729 : Blo 499793 749729 := bstep (se 2 (by rfl) ⟨281148, by rfl⟩ : syracuseStep 749729 = 562297) B562297
theorem B749747 : Blo 499793 749747 := bstep (se 1 (by rfl) ⟨562310, by rfl⟩ : syracuseStep 749747 = 1124621) B1124621
theorem B749777 : Blo 499793 749777 := bstep (se 2 (by rfl) ⟨281166, by rfl⟩ : syracuseStep 749777 = 562333) B562333
theorem B848083 : Blo 499793 848083 := bstep (se 1 (by rfl) ⟨636062, by rfl⟩ : syracuseStep 848083 = 1272125) B1272125
theorem B749795 : Blo 499793 749795 := bstep (se 1 (by rfl) ⟨562346, by rfl⟩ : syracuseStep 749795 = 1124693) B1124693
theorem B1700081 : Blo 499793 1700081 := bstep (se 2 (by rfl) ⟨637530, by rfl⟩ : syracuseStep 1700081 = 1275061) B1275061
theorem B749825 : Blo 499793 749825 := bstep (se 2 (by rfl) ⟨281184, by rfl⟩ : syracuseStep 749825 = 562369) B562369
theorem B1601795 : Blo 499793 1601795 := bstep (se 1 (by rfl) ⟨1201346, by rfl⟩ : syracuseStep 1601795 = 2402693) B2402693
theorem B749843 : Blo 499793 749843 := bstep (se 1 (by rfl) ⟨562382, by rfl⟩ : syracuseStep 749843 = 1124765) B1124765
theorem B749873 : Blo 499793 749873 := bstep (se 2 (by rfl) ⟨281202, by rfl⟩ : syracuseStep 749873 = 562405) B562405
theorem B749891 : Blo 499793 749891 := bstep (se 1 (by rfl) ⟨562418, by rfl⟩ : syracuseStep 749891 = 1124837) B1124837
theorem B749921 : Blo 499793 749921 := bstep (se 2 (by rfl) ⟨281220, by rfl⟩ : syracuseStep 749921 = 562441) B562441
theorem B848225 : Blo 499793 848225 := bstep (se 2 (by rfl) ⟨318084, by rfl⟩ : syracuseStep 848225 = 636169) B636169
theorem B749939 : Blo 499793 749939 := bstep (se 1 (by rfl) ⟨562454, by rfl⟩ : syracuseStep 749939 = 1124909) B1124909
theorem B2847109 : Blo 499793 2847109 := bstep (se 4 (by rfl) ⟨266916, by rfl⟩ : syracuseStep 2847109 = 533833) B533833
theorem B749969 : Blo 499793 749969 := bstep (se 2 (by rfl) ⟨281238, by rfl⟩ : syracuseStep 749969 = 562477) B562477
theorem B749987 : Blo 499793 749987 := bstep (se 1 (by rfl) ⟨562490, by rfl⟩ : syracuseStep 749987 = 1124981) B1124981
theorem B1929635 : Blo 499793 1929635 := bstep (se 1 (by rfl) ⟨1447226, by rfl⟩ : syracuseStep 1929635 = 2894453) B2894453
theorem B750017 : Blo 499793 750017 := bstep (se 2 (by rfl) ⟨281256, by rfl⟩ : syracuseStep 750017 = 562513) B562513
theorem B750035 : Blo 499793 750035 := bstep (se 1 (by rfl) ⟨562526, by rfl⟩ : syracuseStep 750035 = 1125053) B1125053
theorem B848353 : Blo 499793 848353 := bstep (se 2 (by rfl) ⟨318132, by rfl⟩ : syracuseStep 848353 = 636265) B636265
theorem B750065 : Blo 499793 750065 := bstep (se 2 (by rfl) ⟨281274, by rfl⟩ : syracuseStep 750065 = 562549) B562549
theorem B750083 : Blo 499793 750083 := bstep (se 1 (by rfl) ⟨562562, by rfl⟩ : syracuseStep 750083 = 1125125) B1125125
theorem B848387 : Blo 499793 848387 := bstep (se 1 (by rfl) ⟨636290, by rfl⟩ : syracuseStep 848387 = 1272581) B1272581
theorem B750113 : Blo 499793 750113 := bstep (se 2 (by rfl) ⟨281292, by rfl⟩ : syracuseStep 750113 = 562585) B562585
theorem B750131 : Blo 499793 750131 := bstep (se 1 (by rfl) ⟨562598, by rfl⟩ : syracuseStep 750131 = 1125197) B1125197
theorem B750161 : Blo 499793 750161 := bstep (se 2 (by rfl) ⟨281310, by rfl⟩ : syracuseStep 750161 = 562621) B562621
theorem B3797603 : Blo 499793 3797603 := bstep (se 1 (by rfl) ⟨2848202, by rfl⟩ : syracuseStep 3797603 = 5696405) B5696405
theorem B750179 : Blo 499793 750179 := bstep (se 1 (by rfl) ⟨562634, by rfl⟩ : syracuseStep 750179 = 1125269) B1125269
theorem B1143409 : Blo 499793 1143409 := bstep (se 2 (by rfl) ⟨428778, by rfl⟩ : syracuseStep 1143409 = 857557) B857557
theorem B750209 : Blo 499793 750209 := bstep (se 2 (by rfl) ⟨281328, by rfl⟩ : syracuseStep 750209 = 562657) B562657
theorem B848515 : Blo 499793 848515 := bstep (se 1 (by rfl) ⟨636386, by rfl⟩ : syracuseStep 848515 = 1272773) B1272773
theorem B750227 : Blo 499793 750227 := bstep (se 1 (by rfl) ⟨562670, by rfl⟩ : syracuseStep 750227 = 1125341) B1125341
theorem B750257 : Blo 499793 750257 := bstep (se 2 (by rfl) ⟨281346, by rfl⟩ : syracuseStep 750257 = 562693) B562693
theorem B750275 : Blo 499793 750275 := bstep (se 1 (by rfl) ⟨562706, by rfl⟩ : syracuseStep 750275 = 1125413) B1125413
theorem B750305 : Blo 499793 750305 := bstep (se 2 (by rfl) ⟨281364, by rfl⟩ : syracuseStep 750305 = 562729) B562729
theorem B750323 : Blo 499793 750323 := bstep (se 1 (by rfl) ⟨562742, by rfl⟩ : syracuseStep 750323 = 1125485) B1125485
theorem B750353 : Blo 499793 750353 := bstep (se 2 (by rfl) ⟨281382, by rfl⟩ : syracuseStep 750353 = 562765) B562765
theorem B848657 : Blo 499793 848657 := bstep (se 2 (by rfl) ⟨318246, by rfl⟩ : syracuseStep 848657 = 636493) B636493
theorem B750371 : Blo 499793 750371 := bstep (se 1 (by rfl) ⟨562778, by rfl⟩ : syracuseStep 750371 = 1125557) B1125557
theorem B750401 : Blo 499793 750401 := bstep (se 2 (by rfl) ⟨281400, by rfl⟩ : syracuseStep 750401 = 562801) B562801
theorem B750419 : Blo 499793 750419 := bstep (se 1 (by rfl) ⟨562814, by rfl⟩ : syracuseStep 750419 = 1125629) B1125629
theorem B750449 : Blo 499793 750449 := bstep (se 2 (by rfl) ⟨281418, by rfl⟩ : syracuseStep 750449 = 562837) B562837
theorem B1274737 : Blo 499793 1274737 := bstep (se 2 (by rfl) ⟨478026, by rfl⟩ : syracuseStep 1274737 = 956053) B956053
theorem B750467 : Blo 499793 750467 := bstep (se 1 (by rfl) ⟨562850, by rfl⟩ : syracuseStep 750467 = 1125701) B1125701
theorem B1602449 : Blo 499793 1602449 := bstep (se 2 (by rfl) ⟨600918, by rfl⟩ : syracuseStep 1602449 = 1201837) B1201837
theorem B848785 : Blo 499793 848785 := bstep (se 2 (by rfl) ⟨318294, by rfl⟩ : syracuseStep 848785 = 636589) B636589
theorem B750497 : Blo 499793 750497 := bstep (se 2 (by rfl) ⟨281436, by rfl⟩ : syracuseStep 750497 = 562873) B562873
theorem B2290609 : Blo 499793 2290609 := bstep (se 2 (by rfl) ⟨858978, by rfl⟩ : syracuseStep 2290609 = 1717957) B1717957
theorem B750515 : Blo 499793 750515 := bstep (se 1 (by rfl) ⟨562886, by rfl⟩ : syracuseStep 750515 = 1125773) B1125773
theorem B848819 : Blo 499793 848819 := bstep (se 1 (by rfl) ⟨636614, by rfl⟩ : syracuseStep 848819 = 1273229) B1273229
theorem B750545 : Blo 499793 750545 := bstep (se 2 (by rfl) ⟨281454, by rfl⟩ : syracuseStep 750545 = 562909) B562909
theorem B750563 : Blo 499793 750563 := bstep (se 1 (by rfl) ⟨562922, by rfl⟩ : syracuseStep 750563 = 1125845) B1125845
theorem B750593 : Blo 499793 750593 := bstep (se 2 (by rfl) ⟨281472, by rfl⟩ : syracuseStep 750593 = 562945) B562945
theorem B750611 : Blo 499793 750611 := bstep (se 1 (by rfl) ⟨562958, by rfl⟩ : syracuseStep 750611 = 1125917) B1125917
theorem B750641 : Blo 499793 750641 := bstep (se 2 (by rfl) ⟨281490, by rfl⟩ : syracuseStep 750641 = 562981) B562981
theorem B848947 : Blo 499793 848947 := bstep (se 1 (by rfl) ⟨636710, by rfl⟩ : syracuseStep 848947 = 1273421) B1273421
theorem B750659 : Blo 499793 750659 := bstep (se 1 (by rfl) ⟨562994, by rfl⟩ : syracuseStep 750659 = 1125989) B1125989
theorem B5731397 : Blo 499793 5731397 := bstep (se 4 (by rfl) ⟨537318, by rfl⟩ : syracuseStep 5731397 = 1074637) B1074637
theorem B750689 : Blo 499793 750689 := bstep (se 2 (by rfl) ⟨281508, by rfl⟩ : syracuseStep 750689 = 563017) B563017
theorem B750707 : Blo 499793 750707 := bstep (se 1 (by rfl) ⟨563030, by rfl⟩ : syracuseStep 750707 = 1126061) B1126061
theorem B1275011 : Blo 499793 1275011 := bstep (se 1 (by rfl) ⟨956258, by rfl⟩ : syracuseStep 1275011 = 1912517) B1912517
theorem B750737 : Blo 499793 750737 := bstep (se 2 (by rfl) ⟨281526, by rfl⟩ : syracuseStep 750737 = 563053) B563053
theorem B750755 : Blo 499793 750755 := bstep (se 1 (by rfl) ⟨563066, by rfl⟩ : syracuseStep 750755 = 1126133) B1126133
theorem B750785 : Blo 499793 750785 := bstep (se 2 (by rfl) ⟨281544, by rfl⟩ : syracuseStep 750785 = 563089) B563089
theorem B849089 : Blo 499793 849089 := bstep (se 2 (by rfl) ⟨318408, by rfl⟩ : syracuseStep 849089 = 636817) B636817
theorem B750803 : Blo 499793 750803 := bstep (se 1 (by rfl) ⟨563102, by rfl⟩ : syracuseStep 750803 = 1126205) B1126205
theorem B750833 : Blo 499793 750833 := bstep (se 2 (by rfl) ⟨281562, by rfl⟩ : syracuseStep 750833 = 563125) B563125
theorem B750851 : Blo 499793 750851 := bstep (se 1 (by rfl) ⟨563138, by rfl⟩ : syracuseStep 750851 = 1126277) B1126277
theorem B750881 : Blo 499793 750881 := bstep (se 2 (by rfl) ⟨281580, by rfl⟩ : syracuseStep 750881 = 563161) B563161
theorem B750899 : Blo 499793 750899 := bstep (se 1 (by rfl) ⟨563174, by rfl⟩ : syracuseStep 750899 = 1126349) B1126349
theorem B849217 : Blo 499793 849217 := bstep (se 2 (by rfl) ⟨318456, by rfl⟩ : syracuseStep 849217 = 636913) B636913
theorem B1275203 : Blo 499793 1275203 := bstep (se 1 (by rfl) ⟨956402, by rfl⟩ : syracuseStep 1275203 = 1912805) B1912805
theorem B750929 : Blo 499793 750929 := bstep (se 2 (by rfl) ⟨281598, by rfl⟩ : syracuseStep 750929 = 563197) B563197
theorem B750947 : Blo 499793 750947 := bstep (se 1 (by rfl) ⟨563210, by rfl⟩ : syracuseStep 750947 = 1126421) B1126421
theorem B849251 : Blo 499793 849251 := bstep (se 1 (by rfl) ⟨636938, by rfl⟩ : syracuseStep 849251 = 1273877) B1273877
theorem B750977 : Blo 499793 750977 := bstep (se 2 (by rfl) ⟨281616, by rfl⟩ : syracuseStep 750977 = 563233) B563233
theorem B750995 : Blo 499793 750995 := bstep (se 1 (by rfl) ⟨563246, by rfl⟩ : syracuseStep 750995 = 1126493) B1126493
theorem B751025 : Blo 499793 751025 := bstep (se 2 (by rfl) ⟨281634, by rfl⟩ : syracuseStep 751025 = 563269) B563269
theorem B751043 : Blo 499793 751043 := bstep (se 1 (by rfl) ⟨563282, by rfl⟩ : syracuseStep 751043 = 1126565) B1126565
theorem B751073 : Blo 499793 751073 := bstep (se 2 (by rfl) ⟨281652, by rfl⟩ : syracuseStep 751073 = 563305) B563305
theorem B849379 : Blo 499793 849379 := bstep (se 1 (by rfl) ⟨637034, by rfl⟩ : syracuseStep 849379 = 1274069) B1274069
theorem B751091 : Blo 499793 751091 := bstep (se 1 (by rfl) ⟨563318, by rfl⟩ : syracuseStep 751091 = 1126637) B1126637
theorem B751121 : Blo 499793 751121 := bstep (se 2 (by rfl) ⟨281670, by rfl⟩ : syracuseStep 751121 = 563341) B563341
theorem B751139 : Blo 499793 751139 := bstep (se 1 (by rfl) ⟨563354, by rfl⟩ : syracuseStep 751139 = 1126709) B1126709
theorem B751169 : Blo 499793 751169 := bstep (se 2 (by rfl) ⟨281688, by rfl⟩ : syracuseStep 751169 = 563377) B563377
theorem B4126277 : Blo 499793 4126277 := bstep (se 4 (by rfl) ⟨386838, by rfl⟩ : syracuseStep 4126277 = 773677) B773677
theorem B751187 : Blo 499793 751187 := bstep (se 1 (by rfl) ⟨563390, by rfl⟩ : syracuseStep 751187 = 1126781) B1126781
theorem B2029169 : Blo 499793 2029169 := bstep (se 2 (by rfl) ⟨760938, by rfl⟩ : syracuseStep 2029169 = 1521877) B1521877
theorem B751217 : Blo 499793 751217 := bstep (se 2 (by rfl) ⟨281706, by rfl⟩ : syracuseStep 751217 = 563413) B563413
theorem B849521 : Blo 499793 849521 := bstep (se 2 (by rfl) ⟨318570, by rfl⟩ : syracuseStep 849521 = 637141) B637141
theorem B751235 : Blo 499793 751235 := bstep (se 1 (by rfl) ⟨563426, by rfl⟩ : syracuseStep 751235 = 1126853) B1126853
theorem B751265 : Blo 499793 751265 := bstep (se 2 (by rfl) ⟨281724, by rfl⟩ : syracuseStep 751265 = 563449) B563449
theorem B751283 : Blo 499793 751283 := bstep (se 1 (by rfl) ⟨563462, by rfl⟩ : syracuseStep 751283 = 1126925) B1126925
theorem B751313 : Blo 499793 751313 := bstep (se 2 (by rfl) ⟨281742, by rfl⟩ : syracuseStep 751313 = 563485) B563485
theorem B751331 : Blo 499793 751331 := bstep (se 1 (by rfl) ⟨563498, by rfl⟩ : syracuseStep 751331 = 1126997) B1126997
theorem B1898225 : Blo 499793 1898225 := bstep (se 2 (by rfl) ⟨711834, by rfl⟩ : syracuseStep 1898225 = 1423669) B1423669
theorem B849649 : Blo 499793 849649 := bstep (se 2 (by rfl) ⟨318618, by rfl⟩ : syracuseStep 849649 = 637237) B637237
theorem B751361 : Blo 499793 751361 := bstep (se 2 (by rfl) ⟨281760, by rfl⟩ : syracuseStep 751361 = 563521) B563521
theorem B751379 : Blo 499793 751379 := bstep (se 1 (by rfl) ⟨563534, by rfl⟩ : syracuseStep 751379 = 1127069) B1127069
theorem B849683 : Blo 499793 849683 := bstep (se 1 (by rfl) ⟨637262, by rfl⟩ : syracuseStep 849683 = 1274525) B1274525
theorem B751409 : Blo 499793 751409 := bstep (se 2 (by rfl) ⟨281778, by rfl⟩ : syracuseStep 751409 = 563557) B563557
theorem B751427 : Blo 499793 751427 := bstep (se 1 (by rfl) ⟨563570, by rfl⟩ : syracuseStep 751427 = 1127141) B1127141
theorem B751457 : Blo 499793 751457 := bstep (se 2 (by rfl) ⟨281796, by rfl⟩ : syracuseStep 751457 = 563593) B563593
theorem B751475 : Blo 499793 751475 := bstep (se 1 (by rfl) ⟨563606, by rfl⟩ : syracuseStep 751475 = 1127213) B1127213
theorem B751505 : Blo 499793 751505 := bstep (se 2 (by rfl) ⟨281814, by rfl⟩ : syracuseStep 751505 = 563629) B563629
theorem B849811 : Blo 499793 849811 := bstep (se 1 (by rfl) ⟨637358, by rfl⟩ : syracuseStep 849811 = 1274717) B1274717
theorem B751523 : Blo 499793 751523 := bstep (se 1 (by rfl) ⟨563642, by rfl⟩ : syracuseStep 751523 = 1127285) B1127285
theorem B751553 : Blo 499793 751553 := bstep (se 2 (by rfl) ⟨281832, by rfl⟩ : syracuseStep 751553 = 563665) B563665
theorem B751571 : Blo 499793 751571 := bstep (se 1 (by rfl) ⟨563678, by rfl⟩ : syracuseStep 751571 = 1127357) B1127357
theorem B751601 : Blo 499793 751601 := bstep (se 2 (by rfl) ⟨281850, by rfl⟩ : syracuseStep 751601 = 563701) B563701
theorem B751619 : Blo 499793 751619 := bstep (se 1 (by rfl) ⟨563714, by rfl⟩ : syracuseStep 751619 = 1127429) B1127429
theorem B751649 : Blo 499793 751649 := bstep (se 2 (by rfl) ⟨281868, by rfl⟩ : syracuseStep 751649 = 563737) B563737
theorem B849953 : Blo 499793 849953 := bstep (se 2 (by rfl) ⟨318732, by rfl⟩ : syracuseStep 849953 = 637465) B637465
theorem B751667 : Blo 499793 751667 := bstep (se 1 (by rfl) ⟨563750, by rfl⟩ : syracuseStep 751667 = 1127501) B1127501
theorem B751697 : Blo 499793 751697 := bstep (se 2 (by rfl) ⟨281886, by rfl⟩ : syracuseStep 751697 = 563773) B563773
theorem B751715 : Blo 499793 751715 := bstep (se 1 (by rfl) ⟨563786, by rfl⟩ : syracuseStep 751715 = 1127573) B1127573
theorem B751745 : Blo 499793 751745 := bstep (se 2 (by rfl) ⟨281904, by rfl⟩ : syracuseStep 751745 = 563809) B563809
theorem B751763 : Blo 499793 751763 := bstep (se 1 (by rfl) ⟨563822, by rfl⟩ : syracuseStep 751763 = 1127645) B1127645
theorem B850081 : Blo 499793 850081 := bstep (se 2 (by rfl) ⟨318780, by rfl⟩ : syracuseStep 850081 = 637561) B637561
theorem B751793 : Blo 499793 751793 := bstep (se 2 (by rfl) ⟨281922, by rfl⟩ : syracuseStep 751793 = 563845) B563845
theorem B751811 : Blo 499793 751811 := bstep (se 1 (by rfl) ⟨563858, by rfl⟩ : syracuseStep 751811 = 1127717) B1127717
theorem B850115 : Blo 499793 850115 := bstep (se 1 (by rfl) ⟨637586, by rfl⟩ : syracuseStep 850115 = 1275173) B1275173
theorem B751841 : Blo 499793 751841 := bstep (se 2 (by rfl) ⟨281940, by rfl⟩ : syracuseStep 751841 = 563881) B563881
theorem B2291939 : Blo 499793 2291939 := bstep (se 1 (by rfl) ⟨1718954, by rfl⟩ : syracuseStep 2291939 = 3437909) B3437909
theorem B751859 : Blo 499793 751859 := bstep (se 1 (by rfl) ⟨563894, by rfl⟩ : syracuseStep 751859 = 1127789) B1127789
theorem B751889 : Blo 499793 751889 := bstep (se 2 (by rfl) ⟨281958, by rfl⟩ : syracuseStep 751889 = 563917) B563917
theorem B751907 : Blo 499793 751907 := bstep (se 1 (by rfl) ⟨563930, by rfl⟩ : syracuseStep 751907 = 1127861) B1127861
theorem B751937 : Blo 499793 751937 := bstep (se 2 (by rfl) ⟨281976, by rfl⟩ : syracuseStep 751937 = 563953) B563953
theorem B2849093 : Blo 499793 2849093 := bstep (se 4 (by rfl) ⟨267102, by rfl⟩ : syracuseStep 2849093 = 534205) B534205
theorem B751955 : Blo 499793 751955 := bstep (se 1 (by rfl) ⟨563966, by rfl⟩ : syracuseStep 751955 = 1127933) B1127933
theorem B751985 : Blo 499793 751985 := bstep (se 2 (by rfl) ⟨281994, by rfl⟩ : syracuseStep 751985 = 563989) B563989
theorem B817523 : Blo 499793 817523 := bstep (se 1 (by rfl) ⟨613142, by rfl⟩ : syracuseStep 817523 = 1226285) B1226285
theorem B752003 : Blo 499793 752003 := bstep (se 1 (by rfl) ⟨564002, by rfl⟩ : syracuseStep 752003 = 1128005) B1128005
theorem B752033 : Blo 499793 752033 := bstep (se 2 (by rfl) ⟨282012, by rfl⟩ : syracuseStep 752033 = 564025) B564025
theorem B752051 : Blo 499793 752051 := bstep (se 1 (by rfl) ⟨564038, by rfl⟩ : syracuseStep 752051 = 1128077) B1128077
theorem B752081 : Blo 499793 752081 := bstep (se 2 (by rfl) ⟨282030, by rfl⟩ : syracuseStep 752081 = 564061) B564061
theorem B752099 : Blo 499793 752099 := bstep (se 1 (by rfl) ⟨564074, by rfl⟩ : syracuseStep 752099 = 1128149) B1128149
theorem B752129 : Blo 499793 752129 := bstep (se 2 (by rfl) ⟨282048, by rfl⟩ : syracuseStep 752129 = 564097) B564097
theorem B752147 : Blo 499793 752147 := bstep (se 1 (by rfl) ⟨564110, by rfl⟩ : syracuseStep 752147 = 1128221) B1128221
theorem B2095651 : Blo 499793 2095651 := bstep (se 1 (by rfl) ⟨1571738, by rfl⟩ : syracuseStep 2095651 = 3143477) B3143477
theorem B752177 : Blo 499793 752177 := bstep (se 2 (by rfl) ⟨282066, by rfl⟩ : syracuseStep 752177 = 564133) B564133
theorem B752195 : Blo 499793 752195 := bstep (se 1 (by rfl) ⟨564146, by rfl⟩ : syracuseStep 752195 = 1128293) B1128293
theorem B752225 : Blo 499793 752225 := bstep (se 2 (by rfl) ⟨282084, by rfl⟩ : syracuseStep 752225 = 564169) B564169
theorem B752243 : Blo 499793 752243 := bstep (se 1 (by rfl) ⟨564182, by rfl⟩ : syracuseStep 752243 = 1128365) B1128365
theorem B752273 : Blo 499793 752273 := bstep (se 2 (by rfl) ⟨282102, by rfl⟩ : syracuseStep 752273 = 564205) B564205
theorem B752291 : Blo 499793 752291 := bstep (se 1 (by rfl) ⟨564218, by rfl⟩ : syracuseStep 752291 = 1128437) B1128437
theorem B752321 : Blo 499793 752321 := bstep (se 2 (by rfl) ⟨282120, by rfl⟩ : syracuseStep 752321 = 564241) B564241
theorem B752339 : Blo 499793 752339 := bstep (se 1 (by rfl) ⟨564254, by rfl⟩ : syracuseStep 752339 = 1128509) B1128509
theorem B3209969 : Blo 499793 3209969 := bstep (se 2 (by rfl) ⟨1203738, by rfl⟩ : syracuseStep 3209969 = 2407477) B2407477
theorem B752369 : Blo 499793 752369 := bstep (se 2 (by rfl) ⟨282138, by rfl⟩ : syracuseStep 752369 = 564277) B564277
theorem B752387 : Blo 499793 752387 := bstep (se 1 (by rfl) ⟨564290, by rfl⟩ : syracuseStep 752387 = 1128581) B1128581
theorem B752417 : Blo 499793 752417 := bstep (se 2 (by rfl) ⟨282156, by rfl⟩ : syracuseStep 752417 = 564313) B564313
theorem B752435 : Blo 499793 752435 := bstep (se 1 (by rfl) ⟨564326, by rfl⟩ : syracuseStep 752435 = 1128653) B1128653
theorem B752465 : Blo 499793 752465 := bstep (se 2 (by rfl) ⟨282174, by rfl⟩ : syracuseStep 752465 = 564349) B564349
theorem B752483 : Blo 499793 752483 := bstep (se 1 (by rfl) ⟨564362, by rfl⟩ : syracuseStep 752483 = 1128725) B1128725
theorem B1604461 : Blo 499793 1604461 := bstep (se 3 (by rfl) ⟨300836, by rfl⟩ : syracuseStep 1604461 = 601673) B601673
theorem B752513 : Blo 499793 752513 := bstep (se 2 (by rfl) ⟨282192, by rfl⟩ : syracuseStep 752513 = 564385) B564385
theorem B752531 : Blo 499793 752531 := bstep (se 1 (by rfl) ⟨564398, by rfl⟩ : syracuseStep 752531 = 1128797) B1128797
theorem B752561 : Blo 499793 752561 := bstep (se 2 (by rfl) ⟨282210, by rfl⟩ : syracuseStep 752561 = 564421) B564421
theorem B752579 : Blo 499793 752579 := bstep (se 1 (by rfl) ⟨564434, by rfl⟩ : syracuseStep 752579 = 1128869) B1128869
theorem B752609 : Blo 499793 752609 := bstep (se 2 (by rfl) ⟨282228, by rfl⟩ : syracuseStep 752609 = 564457) B564457
theorem B752627 : Blo 499793 752627 := bstep (se 1 (by rfl) ⟨564470, by rfl⟩ : syracuseStep 752627 = 1128941) B1128941
theorem B752657 : Blo 499793 752657 := bstep (se 2 (by rfl) ⟨282246, by rfl⟩ : syracuseStep 752657 = 564493) B564493
theorem B752675 : Blo 499793 752675 := bstep (se 1 (by rfl) ⟨564506, by rfl⟩ : syracuseStep 752675 = 1129013) B1129013
theorem B752705 : Blo 499793 752705 := bstep (se 2 (by rfl) ⟨282264, by rfl⟩ : syracuseStep 752705 = 564529) B564529
theorem B752723 : Blo 499793 752723 := bstep (se 1 (by rfl) ⟨564542, by rfl⟩ : syracuseStep 752723 = 1129085) B1129085
theorem B752753 : Blo 499793 752753 := bstep (se 2 (by rfl) ⟨282282, by rfl⟩ : syracuseStep 752753 = 564565) B564565
theorem B752771 : Blo 499793 752771 := bstep (se 1 (by rfl) ⟨564578, by rfl⟩ : syracuseStep 752771 = 1129157) B1129157
theorem B752801 : Blo 499793 752801 := bstep (se 2 (by rfl) ⟨282300, by rfl⟩ : syracuseStep 752801 = 564601) B564601
theorem B1899683 : Blo 499793 1899683 := bstep (se 1 (by rfl) ⟨1424762, by rfl⟩ : syracuseStep 1899683 = 2849525) B2849525
theorem B752819 : Blo 499793 752819 := bstep (se 1 (by rfl) ⟨564614, by rfl⟩ : syracuseStep 752819 = 1129229) B1129229
theorem B752849 : Blo 499793 752849 := bstep (se 2 (by rfl) ⟨282318, by rfl⟩ : syracuseStep 752849 = 564637) B564637
theorem B752867 : Blo 499793 752867 := bstep (se 1 (by rfl) ⟨564650, by rfl⟩ : syracuseStep 752867 = 1129301) B1129301
theorem B2718947 : Blo 499793 2718947 := bstep (se 1 (by rfl) ⟨2039210, by rfl⟩ : syracuseStep 2718947 = 4078421) B4078421
theorem B1801457 : Blo 499793 1801457 := bstep (se 2 (by rfl) ⟨675546, by rfl⟩ : syracuseStep 1801457 = 1351093) B1351093
theorem B752897 : Blo 499793 752897 := bstep (se 2 (by rfl) ⟨282336, by rfl⟩ : syracuseStep 752897 = 564673) B564673
theorem B752915 : Blo 499793 752915 := bstep (se 1 (by rfl) ⟨564686, by rfl⟩ : syracuseStep 752915 = 1129373) B1129373
theorem B1604909 : Blo 499793 1604909 := bstep (se 3 (by rfl) ⟨300920, by rfl⟩ : syracuseStep 1604909 = 601841) B601841
theorem B949553 : Blo 499793 949553 := bstep (se 2 (by rfl) ⟨356082, by rfl⟩ : syracuseStep 949553 = 712165) B712165
theorem B752945 : Blo 499793 752945 := bstep (se 2 (by rfl) ⟨282354, by rfl⟩ : syracuseStep 752945 = 564709) B564709
theorem B752963 : Blo 499793 752963 := bstep (se 1 (by rfl) ⟨564722, by rfl⟩ : syracuseStep 752963 = 1129445) B1129445
theorem B752993 : Blo 499793 752993 := bstep (se 2 (by rfl) ⟨282372, by rfl⟩ : syracuseStep 752993 = 564745) B564745
theorem B3603811 : Blo 499793 3603811 := bstep (se 1 (by rfl) ⟨2702858, by rfl⟩ : syracuseStep 3603811 = 5405717) B5405717
theorem B753011 : Blo 499793 753011 := bstep (se 1 (by rfl) ⟨564758, by rfl⟩ : syracuseStep 753011 = 1129517) B1129517
theorem B3210637 : Blo 499793 3210637 := bstep (se 3 (by rfl) ⟨601994, by rfl⟩ : syracuseStep 3210637 = 1203989) B1203989
theorem B753041 : Blo 499793 753041 := bstep (se 2 (by rfl) ⟨282390, by rfl⟩ : syracuseStep 753041 = 564781) B564781
theorem B753059 : Blo 499793 753059 := bstep (se 1 (by rfl) ⟨564794, by rfl⟩ : syracuseStep 753059 = 1129589) B1129589
theorem B753089 : Blo 499793 753089 := bstep (se 2 (by rfl) ⟨282408, by rfl⟩ : syracuseStep 753089 = 564817) B564817
theorem B753107 : Blo 499793 753107 := bstep (se 1 (by rfl) ⟨564830, by rfl⟩ : syracuseStep 753107 = 1129661) B1129661
theorem B753137 : Blo 499793 753137 := bstep (se 2 (by rfl) ⟨282426, by rfl⟩ : syracuseStep 753137 = 564853) B564853
theorem B753155 : Blo 499793 753155 := bstep (se 1 (by rfl) ⟨564866, by rfl⟩ : syracuseStep 753155 = 1129733) B1129733
theorem B753185 : Blo 499793 753185 := bstep (se 2 (by rfl) ⟨282444, by rfl⟩ : syracuseStep 753185 = 564889) B564889
theorem B753203 : Blo 499793 753203 := bstep (se 1 (by rfl) ⟨564902, by rfl⟩ : syracuseStep 753203 = 1129805) B1129805
theorem B753233 : Blo 499793 753233 := bstep (se 2 (by rfl) ⟨282462, by rfl⟩ : syracuseStep 753233 = 564925) B564925
theorem B753251 : Blo 499793 753251 := bstep (se 1 (by rfl) ⟨564938, by rfl⟩ : syracuseStep 753251 = 1129877) B1129877
theorem B753281 : Blo 499793 753281 := bstep (se 2 (by rfl) ⟨282480, by rfl⟩ : syracuseStep 753281 = 564961) B564961
theorem B2031245 : Blo 499793 2031245 := bstep (se 3 (by rfl) ⟨380858, by rfl⟩ : syracuseStep 2031245 = 761717) B761717
theorem B753299 : Blo 499793 753299 := bstep (se 1 (by rfl) ⟨564974, by rfl⟩ : syracuseStep 753299 = 1129949) B1129949
theorem B753329 : Blo 499793 753329 := bstep (se 2 (by rfl) ⟨282498, by rfl⟩ : syracuseStep 753329 = 564997) B564997
theorem B753347 : Blo 499793 753347 := bstep (se 1 (by rfl) ⟨565010, by rfl⟩ : syracuseStep 753347 = 1130021) B1130021
theorem B753377 : Blo 499793 753377 := bstep (se 2 (by rfl) ⟨282516, by rfl⟩ : syracuseStep 753377 = 565033) B565033
theorem B753395 : Blo 499793 753395 := bstep (se 1 (by rfl) ⟨565046, by rfl⟩ : syracuseStep 753395 = 1130093) B1130093
theorem B753425 : Blo 499793 753425 := bstep (se 2 (by rfl) ⟨282534, by rfl⟩ : syracuseStep 753425 = 565069) B565069
theorem B753443 : Blo 499793 753443 := bstep (se 1 (by rfl) ⟨565082, by rfl⟩ : syracuseStep 753443 = 1130165) B1130165
theorem B753473 : Blo 499793 753473 := bstep (se 2 (by rfl) ⟨282552, by rfl⟩ : syracuseStep 753473 = 565105) B565105
theorem B753491 : Blo 499793 753491 := bstep (se 1 (by rfl) ⟨565118, by rfl⟩ : syracuseStep 753491 = 1130237) B1130237
theorem B753521 : Blo 499793 753521 := bstep (se 2 (by rfl) ⟨282570, by rfl⟩ : syracuseStep 753521 = 565141) B565141
theorem B753539 : Blo 499793 753539 := bstep (se 1 (by rfl) ⟨565154, by rfl⟩ : syracuseStep 753539 = 1130309) B1130309
theorem B753569 : Blo 499793 753569 := bstep (se 2 (by rfl) ⟨282588, by rfl⟩ : syracuseStep 753569 = 565177) B565177
theorem B753587 : Blo 499793 753587 := bstep (se 1 (by rfl) ⟨565190, by rfl⟩ : syracuseStep 753587 = 1130381) B1130381
theorem B753617 : Blo 499793 753617 := bstep (se 2 (by rfl) ⟨282606, by rfl⟩ : syracuseStep 753617 = 565213) B565213
theorem B753635 : Blo 499793 753635 := bstep (se 1 (by rfl) ⟨565226, by rfl⟩ : syracuseStep 753635 = 1130453) B1130453
theorem B753689 : Blo 499793 753689 := bstep (se 2 (by rfl) ⟨282633, by rfl⟩ : syracuseStep 753689 = 565267) B565267
theorem B753803 : Blo 499793 753803 := bstep (se 1 (by rfl) ⟨565352, by rfl⟩ : syracuseStep 753803 = 1130705) B1130705
theorem B753815 : Blo 499793 753815 := bstep (se 1 (by rfl) ⟨565361, by rfl⟩ : syracuseStep 753815 = 1130723) B1130723
theorem B753881 : Blo 499793 753881 := bstep (se 2 (by rfl) ⟨282705, by rfl⟩ : syracuseStep 753881 = 565411) B565411
theorem B753995 : Blo 499793 753995 := bstep (se 1 (by rfl) ⟨565496, by rfl⟩ : syracuseStep 753995 = 1130993) B1130993
theorem B754007 : Blo 499793 754007 := bstep (se 1 (by rfl) ⟨565505, by rfl⟩ : syracuseStep 754007 = 1131011) B1131011
theorem B754073 : Blo 499793 754073 := bstep (se 2 (by rfl) ⟨282777, by rfl⟩ : syracuseStep 754073 = 565555) B565555
theorem B950707 : Blo 499793 950707 := bstep (se 1 (by rfl) ⟨713030, by rfl⟩ : syracuseStep 950707 = 1426061) B1426061
theorem B754187 : Blo 499793 754187 := bstep (se 1 (by rfl) ⟨565640, by rfl⟩ : syracuseStep 754187 = 1131281) B1131281
theorem B754199 : Blo 499793 754199 := bstep (se 1 (by rfl) ⟨565649, by rfl⟩ : syracuseStep 754199 = 1131299) B1131299
theorem B754265 : Blo 499793 754265 := bstep (se 2 (by rfl) ⟨282849, by rfl⟩ : syracuseStep 754265 = 565699) B565699
theorem B5702237 : Blo 499793 5702237 := bstep (se 3 (by rfl) ⟨1069169, by rfl⟩ : syracuseStep 5702237 = 2138339) B2138339
theorem B950935 : Blo 499793 950935 := bstep (se 1 (by rfl) ⟨713201, by rfl⟩ : syracuseStep 950935 = 1426403) B1426403
theorem B754379 : Blo 499793 754379 := bstep (se 1 (by rfl) ⟨565784, by rfl⟩ : syracuseStep 754379 = 1131569) B1131569
theorem B754391 : Blo 499793 754391 := bstep (se 1 (by rfl) ⟨565793, by rfl⟩ : syracuseStep 754391 = 1131587) B1131587
theorem B951041 : Blo 499793 951041 := bstep (se 2 (by rfl) ⟨356640, by rfl⟩ : syracuseStep 951041 = 713281) B713281
theorem B754457 : Blo 499793 754457 := bstep (se 2 (by rfl) ⟨282921, by rfl⟩ : syracuseStep 754457 = 565843) B565843
theorem B754571 : Blo 499793 754571 := bstep (se 1 (by rfl) ⟨565928, by rfl⟩ : syracuseStep 754571 = 1131857) B1131857
theorem B754583 : Blo 499793 754583 := bstep (se 1 (by rfl) ⟨565937, by rfl⟩ : syracuseStep 754583 = 1131875) B1131875
theorem B951193 : Blo 499793 951193 := bstep (se 2 (by rfl) ⟨356697, by rfl⟩ : syracuseStep 951193 = 713395) B713395
theorem B8586161 : Blo 499793 8586161 := bstep (se 2 (by rfl) ⟨3219810, by rfl⟩ : syracuseStep 8586161 = 6439621) B6439621
theorem B754649 : Blo 499793 754649 := bstep (se 2 (by rfl) ⟨282993, by rfl⟩ : syracuseStep 754649 = 565987) B565987
theorem B754763 : Blo 499793 754763 := bstep (se 1 (by rfl) ⟨566072, by rfl⟩ : syracuseStep 754763 = 1132145) B1132145
theorem B754775 : Blo 499793 754775 := bstep (se 1 (by rfl) ⟨566081, by rfl⟩ : syracuseStep 754775 = 1132163) B1132163
theorem B1901657 : Blo 499793 1901657 := bstep (se 2 (by rfl) ⟨713121, by rfl⟩ : syracuseStep 1901657 = 1426243) B1426243
theorem B1016921 : Blo 499793 1016921 := bstep (se 2 (by rfl) ⟨381345, by rfl⟩ : syracuseStep 1016921 = 762691) B762691
theorem B2032771 : Blo 499793 2032771 := bstep (se 1 (by rfl) ⟨1524578, by rfl⟩ : syracuseStep 2032771 = 3049157) B3049157
theorem B754841 : Blo 499793 754841 := bstep (se 2 (by rfl) ⟨283065, by rfl⟩ : syracuseStep 754841 = 566131) B566131
theorem B754955 : Blo 499793 754955 := bstep (se 1 (by rfl) ⟨566216, by rfl⟩ : syracuseStep 754955 = 1132433) B1132433
theorem B754967 : Blo 499793 754967 := bstep (se 1 (by rfl) ⟨566225, by rfl⟩ : syracuseStep 754967 = 1132451) B1132451
theorem B755033 : Blo 499793 755033 := bstep (se 2 (by rfl) ⟨283137, by rfl⟩ : syracuseStep 755033 = 566275) B566275
theorem B755147 : Blo 499793 755147 := bstep (se 1 (by rfl) ⟨566360, by rfl⟩ : syracuseStep 755147 = 1132721) B1132721
theorem B755159 : Blo 499793 755159 := bstep (se 1 (by rfl) ⟨566369, by rfl⟩ : syracuseStep 755159 = 1132739) B1132739
theorem B755225 : Blo 499793 755225 := bstep (se 2 (by rfl) ⟨283209, by rfl⟩ : syracuseStep 755225 = 566419) B566419
theorem B1803865 : Blo 499793 1803865 := bstep (se 2 (by rfl) ⟨676449, by rfl⟩ : syracuseStep 1803865 = 1352899) B1352899
theorem B755339 : Blo 499793 755339 := bstep (se 1 (by rfl) ⟨566504, by rfl⟩ : syracuseStep 755339 = 1133009) B1133009
theorem B755351 : Blo 499793 755351 := bstep (se 1 (by rfl) ⟨566513, by rfl⟩ : syracuseStep 755351 = 1133027) B1133027
theorem B755417 : Blo 499793 755417 := bstep (se 2 (by rfl) ⟨283281, by rfl⟩ : syracuseStep 755417 = 566563) B566563
theorem B755531 : Blo 499793 755531 := bstep (se 1 (by rfl) ⟨566648, by rfl⟩ : syracuseStep 755531 = 1133297) B1133297
theorem B755543 : Blo 499793 755543 := bstep (se 1 (by rfl) ⟨566657, by rfl⟩ : syracuseStep 755543 = 1133315) B1133315
theorem B2852759 : Blo 499793 2852759 := bstep (se 1 (by rfl) ⟨2139569, by rfl⟩ : syracuseStep 2852759 = 4279139) B4279139
theorem B755609 : Blo 499793 755609 := bstep (se 2 (by rfl) ⟨283353, by rfl⟩ : syracuseStep 755609 = 566707) B566707
theorem B4294721 : Blo 499793 4294721 := bstep (se 2 (by rfl) ⟨1610520, by rfl⟩ : syracuseStep 4294721 = 3221041) B3221041
theorem B952499 : Blo 499793 952499 := bstep (se 1 (by rfl) ⟨714374, by rfl⟩ : syracuseStep 952499 = 1428749) B1428749
theorem B952651 : Blo 499793 952651 := bstep (se 1 (by rfl) ⟨714488, by rfl⟩ : syracuseStep 952651 = 1428977) B1428977
theorem B2034071 : Blo 499793 2034071 := bstep (se 1 (by rfl) ⟨1525553, by rfl⟩ : syracuseStep 2034071 = 3051107) B3051107
theorem B2722405 : Blo 499793 2722405 := bstep (se 4 (by rfl) ⟨255225, by rfl⟩ : syracuseStep 2722405 = 510451) B510451
theorem B952985 : Blo 499793 952985 := bstep (se 2 (by rfl) ⟨357369, by rfl⟩ : syracuseStep 952985 = 714739) B714739
theorem B1903283 : Blo 499793 1903283 := bstep (se 1 (by rfl) ⟨1427462, by rfl⟩ : syracuseStep 1903283 = 2854925) B2854925
theorem B1084097 : Blo 499793 1084097 := bstep (se 2 (by rfl) ⟨406536, by rfl⟩ : syracuseStep 1084097 = 813073) B813073
theorem B1903297 : Blo 499793 1903297 := bstep (se 2 (by rfl) ⟨713736, by rfl⟩ : syracuseStep 1903297 = 1427473) B1427473
theorem B6195973 : Blo 499793 6195973 := bstep (se 4 (by rfl) ⟨580872, by rfl⟩ : syracuseStep 6195973 = 1161745) B1161745
theorem B3803921 : Blo 499793 3803921 := bstep (se 2 (by rfl) ⟨1426470, by rfl⟩ : syracuseStep 3803921 = 2852941) B2852941
theorem B2231185 : Blo 499793 2231185 := bstep (se 2 (by rfl) ⟨836694, by rfl⟩ : syracuseStep 2231185 = 1673389) B1673389
theorem B1608599 : Blo 499793 1608599 := bstep (se 1 (by rfl) ⟨1206449, by rfl⟩ : syracuseStep 1608599 = 2412899) B2412899
theorem B1084313 : Blo 499793 1084313 := bstep (se 2 (by rfl) ⟨406617, by rfl⟩ : syracuseStep 1084313 = 813235) B813235
theorem B2886749 : Blo 499793 2886749 := bstep (se 3 (by rfl) ⟨541265, by rfl⟩ : syracuseStep 2886749 = 1082531) B1082531
theorem B6851735 : Blo 499793 6851735 := bstep (se 1 (by rfl) ⟨5138801, by rfl⟩ : syracuseStep 6851735 = 10277603) B10277603
theorem B953623 : Blo 499793 953623 := bstep (se 1 (by rfl) ⟨715217, by rfl⟩ : syracuseStep 953623 = 1430435) B1430435
theorem B2723165 : Blo 499793 2723165 := bstep (se 3 (by rfl) ⟨510593, by rfl⟩ : syracuseStep 2723165 = 1021187) B1021187
theorem B1019353 : Blo 499793 1019353 := bstep (se 2 (by rfl) ⟨382257, by rfl⟩ : syracuseStep 1019353 = 764515) B764515
theorem B2854673 : Blo 499793 2854673 := bstep (se 2 (by rfl) ⟨1070502, by rfl⟩ : syracuseStep 2854673 = 2141005) B2141005
theorem B954443 : Blo 499793 954443 := bstep (se 1 (by rfl) ⟨715832, by rfl⟩ : syracuseStep 954443 = 1431665) B1431665
theorem B6951005 : Blo 499793 6951005 := bstep (se 3 (by rfl) ⟨1303313, by rfl⟩ : syracuseStep 6951005 = 2606627) B2606627
theorem B954497 : Blo 499793 954497 := bstep (se 2 (by rfl) ⟨357936, by rfl⟩ : syracuseStep 954497 = 715873) B715873
theorem B5411117 : Blo 499793 5411117 := bstep (se 3 (by rfl) ⟨1014584, by rfl⟩ : syracuseStep 5411117 = 2029169) B2029169
theorem B1905227 : Blo 499793 1905227 := bstep (se 1 (by rfl) ⟨1428920, by rfl⟩ : syracuseStep 1905227 = 2857841) B2857841
theorem B1905241 : Blo 499793 1905241 := bstep (se 2 (by rfl) ⟨714465, by rfl⟩ : syracuseStep 1905241 = 1428931) B1428931
theorem B2134957 : Blo 499793 2134957 := bstep (se 3 (by rfl) ⟨400304, by rfl⟩ : syracuseStep 2134957 = 800609) B800609
theorem B5575601 : Blo 499793 5575601 := bstep (se 2 (by rfl) ⟨2090850, by rfl⟩ : syracuseStep 5575601 = 4181701) B4181701
theorem B1610675 : Blo 499793 1610675 := bstep (se 1 (by rfl) ⟨1208006, by rfl⟩ : syracuseStep 1610675 = 2416013) B2416013
theorem B955415 : Blo 499793 955415 := bstep (se 1 (by rfl) ⟨716561, by rfl⟩ : syracuseStep 955415 = 1433123) B1433123
theorem B1807453 : Blo 499793 1807453 := bstep (se 3 (by rfl) ⟨338897, by rfl⟩ : syracuseStep 1807453 = 677795) B677795
theorem B562315 : Blo 499793 562315 := bstep (se 1 (by rfl) ⟨421736, by rfl⟩ : syracuseStep 562315 = 843473) B843473
theorem B562423 : Blo 499793 562423 := bstep (se 1 (by rfl) ⟨421817, by rfl⟩ : syracuseStep 562423 = 843635) B843635
theorem B4560229 : Blo 499793 4560229 := bstep (se 4 (by rfl) ⟨427521, by rfl⟩ : syracuseStep 4560229 = 855043) B855043
theorem B4330853 : Blo 499793 4330853 := bstep (se 4 (by rfl) ⟨406017, by rfl⟩ : syracuseStep 4330853 = 812035) B812035
theorem B562603 : Blo 499793 562603 := bstep (se 1 (by rfl) ⟨421952, by rfl⟩ : syracuseStep 562603 = 843905) B843905
theorem B4560305 : Blo 499793 4560305 := bstep (se 2 (by rfl) ⟨1710114, by rfl⟩ : syracuseStep 4560305 = 3420229) B3420229
theorem B562711 : Blo 499793 562711 := bstep (se 1 (by rfl) ⟨422033, by rfl⟩ : syracuseStep 562711 = 844067) B844067
theorem B1906199 : Blo 499793 1906199 := bstep (se 1 (by rfl) ⟨1429649, by rfl⟩ : syracuseStep 1906199 = 2859299) B2859299
theorem B3216941 : Blo 499793 3216941 := bstep (se 3 (by rfl) ⟨603176, by rfl⟩ : syracuseStep 3216941 = 1206353) B1206353
theorem B955955 : Blo 499793 955955 := bstep (se 1 (by rfl) ⟨716966, by rfl⟩ : syracuseStep 955955 = 1433933) B1433933
theorem B562891 : Blo 499793 562891 := bstep (se 1 (by rfl) ⟨422168, by rfl⟩ : syracuseStep 562891 = 844337) B844337
theorem B562999 : Blo 499793 562999 := bstep (se 1 (by rfl) ⟨422249, by rfl⟩ : syracuseStep 562999 = 844499) B844499
theorem B563179 : Blo 499793 563179 := bstep (se 1 (by rfl) ⟨422384, by rfl⟩ : syracuseStep 563179 = 844769) B844769
theorem B563287 : Blo 499793 563287 := bstep (se 1 (by rfl) ⟨422465, by rfl⟩ : syracuseStep 563287 = 844931) B844931
theorem B9672965 : Blo 499793 9672965 := bstep (se 4 (by rfl) ⟨906840, by rfl⟩ : syracuseStep 9672965 = 1813681) B1813681
theorem B563467 : Blo 499793 563467 := bstep (se 1 (by rfl) ⟨422600, by rfl⟩ : syracuseStep 563467 = 845201) B845201
theorem B563575 : Blo 499793 563575 := bstep (se 1 (by rfl) ⟨422681, by rfl⟩ : syracuseStep 563575 = 845363) B845363
theorem B1087987 : Blo 499793 1087987 := bstep (se 1 (by rfl) ⟨815990, by rfl⟩ : syracuseStep 1087987 = 1631981) B1631981
theorem B563755 : Blo 499793 563755 := bstep (se 1 (by rfl) ⟨422816, by rfl⟩ : syracuseStep 563755 = 845633) B845633
theorem B3807809 : Blo 499793 3807809 := bstep (se 2 (by rfl) ⟨1427928, by rfl⟩ : syracuseStep 3807809 = 2855857) B2855857
theorem B563863 : Blo 499793 563863 := bstep (se 1 (by rfl) ⟨422897, by rfl⟩ : syracuseStep 563863 = 845795) B845795
theorem B1907459 : Blo 499793 1907459 := bstep (se 1 (by rfl) ⟨1430594, by rfl⟩ : syracuseStep 1907459 = 2861189) B2861189
theorem B564043 : Blo 499793 564043 := bstep (se 1 (by rfl) ⟨423032, by rfl⟩ : syracuseStep 564043 = 846065) B846065
theorem B564151 : Blo 499793 564151 := bstep (se 1 (by rfl) ⟨423113, by rfl⟩ : syracuseStep 564151 = 846227) B846227
theorem B564331 : Blo 499793 564331 := bstep (se 1 (by rfl) ⟨423248, by rfl⟩ : syracuseStep 564331 = 846497) B846497
theorem B564439 : Blo 499793 564439 := bstep (se 1 (by rfl) ⟨423329, by rfl⟩ : syracuseStep 564439 = 846659) B846659
theorem B2137367 : Blo 499793 2137367 := bstep (se 1 (by rfl) ⟨1603025, by rfl⟩ : syracuseStep 2137367 = 3206051) B3206051
theorem B8559917 : Blo 499793 8559917 := bstep (se 3 (by rfl) ⟨1604984, by rfl⟩ : syracuseStep 8559917 = 3209969) B3209969
theorem B564619 : Blo 499793 564619 := bstep (se 1 (by rfl) ⟨423464, by rfl⟩ : syracuseStep 564619 = 846929) B846929
theorem B564727 : Blo 499793 564727 := bstep (se 1 (by rfl) ⟨423545, by rfl⟩ : syracuseStep 564727 = 847091) B847091
theorem B8691275 : Blo 499793 8691275 := bstep (se 1 (by rfl) ⟨6518456, by rfl⟩ : syracuseStep 8691275 = 13036913) B13036913
theorem B564907 : Blo 499793 564907 := bstep (se 1 (by rfl) ⟨423680, by rfl⟩ : syracuseStep 564907 = 847361) B847361
theorem B565015 : Blo 499793 565015 := bstep (se 1 (by rfl) ⟨423761, by rfl⟩ : syracuseStep 565015 = 847523) B847523
theorem B565195 : Blo 499793 565195 := bstep (se 1 (by rfl) ⟨423896, by rfl⟩ : syracuseStep 565195 = 847793) B847793
theorem B565303 : Blo 499793 565303 := bstep (se 1 (by rfl) ⟨423977, by rfl⟩ : syracuseStep 565303 = 847955) B847955
theorem B499799 : Blo 499793 499799 := bstep (se 1 (by rfl) ⟨374849, by rfl⟩ : syracuseStep 499799 = 749699) B749699
theorem B499819 : Blo 499793 499819 := bstep (se 1 (by rfl) ⟨374864, by rfl⟩ : syracuseStep 499819 = 749729) B749729
theorem B499831 : Blo 499793 499831 := bstep (se 1 (by rfl) ⟨374873, by rfl⟩ : syracuseStep 499831 = 749747) B749747
theorem B499851 : Blo 499793 499851 := bstep (se 1 (by rfl) ⟨374888, by rfl⟩ : syracuseStep 499851 = 749777) B749777
theorem B499863 : Blo 499793 499863 := bstep (se 1 (by rfl) ⟨374897, by rfl⟩ : syracuseStep 499863 = 749795) B749795
theorem B499883 : Blo 499793 499883 := bstep (se 1 (by rfl) ⟨374912, by rfl⟩ : syracuseStep 499883 = 749825) B749825
theorem B499895 : Blo 499793 499895 := bstep (se 1 (by rfl) ⟨374921, by rfl⟩ : syracuseStep 499895 = 749843) B749843
theorem B499915 : Blo 499793 499915 := bstep (se 1 (by rfl) ⟨374936, by rfl⟩ : syracuseStep 499915 = 749873) B749873
theorem B499927 : Blo 499793 499927 := bstep (se 1 (by rfl) ⟨374945, by rfl⟩ : syracuseStep 499927 = 749891) B749891
theorem B499947 : Blo 499793 499947 := bstep (se 1 (by rfl) ⟨374960, by rfl⟩ : syracuseStep 499947 = 749921) B749921
theorem B565483 : Blo 499793 565483 := bstep (se 1 (by rfl) ⟨424112, by rfl⟩ : syracuseStep 565483 = 848225) B848225
theorem B499959 : Blo 499793 499959 := bstep (se 1 (by rfl) ⟨374969, by rfl⟩ : syracuseStep 499959 = 749939) B749939
theorem B499979 : Blo 499793 499979 := bstep (se 1 (by rfl) ⟨374984, by rfl⟩ : syracuseStep 499979 = 749969) B749969
theorem B499991 : Blo 499793 499991 := bstep (se 1 (by rfl) ⟨374993, by rfl⟩ : syracuseStep 499991 = 749987) B749987
theorem B1286423 : Blo 499793 1286423 := bstep (se 1 (by rfl) ⟨964817, by rfl⟩ : syracuseStep 1286423 = 1929635) B1929635
theorem B500011 : Blo 499793 500011 := bstep (se 1 (by rfl) ⟨375008, by rfl⟩ : syracuseStep 500011 = 750017) B750017
theorem B500023 : Blo 499793 500023 := bstep (se 1 (by rfl) ⟨375017, by rfl⟩ : syracuseStep 500023 = 750035) B750035
theorem B500043 : Blo 499793 500043 := bstep (se 1 (by rfl) ⟨375032, by rfl⟩ : syracuseStep 500043 = 750065) B750065
theorem B500055 : Blo 499793 500055 := bstep (se 1 (by rfl) ⟨375041, by rfl⟩ : syracuseStep 500055 = 750083) B750083
theorem B565591 : Blo 499793 565591 := bstep (se 1 (by rfl) ⟨424193, by rfl⟩ : syracuseStep 565591 = 848387) B848387
theorem B500075 : Blo 499793 500075 := bstep (se 1 (by rfl) ⟨375056, by rfl⟩ : syracuseStep 500075 = 750113) B750113
theorem B500087 : Blo 499793 500087 := bstep (se 1 (by rfl) ⟨375065, by rfl⟩ : syracuseStep 500087 = 750131) B750131
theorem B500107 : Blo 499793 500107 := bstep (se 1 (by rfl) ⟨375080, by rfl⟩ : syracuseStep 500107 = 750161) B750161
theorem B2531735 : Blo 499793 2531735 := bstep (se 1 (by rfl) ⟨1898801, by rfl⟩ : syracuseStep 2531735 = 3797603) B3797603
theorem B500119 : Blo 499793 500119 := bstep (se 1 (by rfl) ⟨375089, by rfl⟩ : syracuseStep 500119 = 750179) B750179
theorem B500139 : Blo 499793 500139 := bstep (se 1 (by rfl) ⟨375104, by rfl⟩ : syracuseStep 500139 = 750209) B750209
theorem B500151 : Blo 499793 500151 := bstep (se 1 (by rfl) ⟨375113, by rfl⟩ : syracuseStep 500151 = 750227) B750227
theorem B500171 : Blo 499793 500171 := bstep (se 1 (by rfl) ⟨375128, by rfl⟩ : syracuseStep 500171 = 750257) B750257
theorem B500183 : Blo 499793 500183 := bstep (se 1 (by rfl) ⟨375137, by rfl⟩ : syracuseStep 500183 = 750275) B750275
theorem B3809753 : Blo 499793 3809753 := bstep (se 2 (by rfl) ⟨1428657, by rfl⟩ : syracuseStep 3809753 = 2857315) B2857315
theorem B500203 : Blo 499793 500203 := bstep (se 1 (by rfl) ⟨375152, by rfl⟩ : syracuseStep 500203 = 750305) B750305
theorem B500215 : Blo 499793 500215 := bstep (se 1 (by rfl) ⟨375161, by rfl⟩ : syracuseStep 500215 = 750323) B750323
theorem B500235 : Blo 499793 500235 := bstep (se 1 (by rfl) ⟨375176, by rfl⟩ : syracuseStep 500235 = 750353) B750353
theorem B565771 : Blo 499793 565771 := bstep (se 1 (by rfl) ⟨424328, by rfl⟩ : syracuseStep 565771 = 848657) B848657
theorem B500247 : Blo 499793 500247 := bstep (se 1 (by rfl) ⟨375185, by rfl⟩ : syracuseStep 500247 = 750371) B750371
theorem B500267 : Blo 499793 500267 := bstep (se 1 (by rfl) ⟨375200, by rfl⟩ : syracuseStep 500267 = 750401) B750401
theorem B500279 : Blo 499793 500279 := bstep (se 1 (by rfl) ⟨375209, by rfl⟩ : syracuseStep 500279 = 750419) B750419
theorem B500299 : Blo 499793 500299 := bstep (se 1 (by rfl) ⟨375224, by rfl⟩ : syracuseStep 500299 = 750449) B750449
theorem B500311 : Blo 499793 500311 := bstep (se 1 (by rfl) ⟨375233, by rfl⟩ : syracuseStep 500311 = 750467) B750467
theorem B500331 : Blo 499793 500331 := bstep (se 1 (by rfl) ⟨375248, by rfl⟩ : syracuseStep 500331 = 750497) B750497
theorem B500343 : Blo 499793 500343 := bstep (se 1 (by rfl) ⟨375257, by rfl⟩ : syracuseStep 500343 = 750515) B750515
theorem B565879 : Blo 499793 565879 := bstep (se 1 (by rfl) ⟨424409, by rfl⟩ : syracuseStep 565879 = 848819) B848819
theorem B500363 : Blo 499793 500363 := bstep (se 1 (by rfl) ⟨375272, by rfl⟩ : syracuseStep 500363 = 750545) B750545
theorem B500375 : Blo 499793 500375 := bstep (se 1 (by rfl) ⟨375281, by rfl⟩ : syracuseStep 500375 = 750563) B750563
theorem B500395 : Blo 499793 500395 := bstep (se 1 (by rfl) ⟨375296, by rfl⟩ : syracuseStep 500395 = 750593) B750593
theorem B500407 : Blo 499793 500407 := bstep (se 1 (by rfl) ⟨375305, by rfl⟩ : syracuseStep 500407 = 750611) B750611
theorem B500427 : Blo 499793 500427 := bstep (se 1 (by rfl) ⟨375320, by rfl⟩ : syracuseStep 500427 = 750641) B750641
theorem B500439 : Blo 499793 500439 := bstep (se 1 (by rfl) ⟨375329, by rfl⟩ : syracuseStep 500439 = 750659) B750659
theorem B2794201 : Blo 499793 2794201 := bstep (se 2 (by rfl) ⟨1047825, by rfl⟩ : syracuseStep 2794201 = 2095651) B2095651
theorem B500459 : Blo 499793 500459 := bstep (se 1 (by rfl) ⟨375344, by rfl⟩ : syracuseStep 500459 = 750689) B750689
theorem B500471 : Blo 499793 500471 := bstep (se 1 (by rfl) ⟨375353, by rfl⟩ : syracuseStep 500471 = 750707) B750707
theorem B500491 : Blo 499793 500491 := bstep (se 1 (by rfl) ⟨375368, by rfl⟩ : syracuseStep 500491 = 750737) B750737
theorem B500503 : Blo 499793 500503 := bstep (se 1 (by rfl) ⟨375377, by rfl⟩ : syracuseStep 500503 = 750755) B750755
theorem B500523 : Blo 499793 500523 := bstep (se 1 (by rfl) ⟨375392, by rfl⟩ : syracuseStep 500523 = 750785) B750785
theorem B566059 : Blo 499793 566059 := bstep (se 1 (by rfl) ⟨424544, by rfl⟩ : syracuseStep 566059 = 849089) B849089
theorem B500535 : Blo 499793 500535 := bstep (se 1 (by rfl) ⟨375401, by rfl⟩ : syracuseStep 500535 = 750803) B750803
theorem B500555 : Blo 499793 500555 := bstep (se 1 (by rfl) ⟨375416, by rfl⟩ : syracuseStep 500555 = 750833) B750833
theorem B500567 : Blo 499793 500567 := bstep (se 1 (by rfl) ⟨375425, by rfl⟩ : syracuseStep 500567 = 750851) B750851
theorem B500587 : Blo 499793 500587 := bstep (se 1 (by rfl) ⟨375440, by rfl⟩ : syracuseStep 500587 = 750881) B750881
theorem B500599 : Blo 499793 500599 := bstep (se 1 (by rfl) ⟨375449, by rfl⟩ : syracuseStep 500599 = 750899) B750899
theorem B500619 : Blo 499793 500619 := bstep (se 1 (by rfl) ⟨375464, by rfl⟩ : syracuseStep 500619 = 750929) B750929
theorem B500631 : Blo 499793 500631 := bstep (se 1 (by rfl) ⟨375473, by rfl⟩ : syracuseStep 500631 = 750947) B750947
theorem B566167 : Blo 499793 566167 := bstep (se 1 (by rfl) ⟨424625, by rfl⟩ : syracuseStep 566167 = 849251) B849251
theorem B500651 : Blo 499793 500651 := bstep (se 1 (by rfl) ⟨375488, by rfl⟩ : syracuseStep 500651 = 750977) B750977
theorem B500663 : Blo 499793 500663 := bstep (se 1 (by rfl) ⟨375497, by rfl⟩ : syracuseStep 500663 = 750995) B750995
theorem B500683 : Blo 499793 500683 := bstep (se 1 (by rfl) ⟨375512, by rfl⟩ : syracuseStep 500683 = 751025) B751025
theorem B500695 : Blo 499793 500695 := bstep (se 1 (by rfl) ⟨375521, by rfl⟩ : syracuseStep 500695 = 751043) B751043
theorem B500715 : Blo 499793 500715 := bstep (se 1 (by rfl) ⟨375536, by rfl⟩ : syracuseStep 500715 = 751073) B751073
theorem B500727 : Blo 499793 500727 := bstep (se 1 (by rfl) ⟨375545, by rfl⟩ : syracuseStep 500727 = 751091) B751091
theorem B500747 : Blo 499793 500747 := bstep (se 1 (by rfl) ⟨375560, by rfl⟩ : syracuseStep 500747 = 751121) B751121
theorem B2860049 : Blo 499793 2860049 := bstep (se 2 (by rfl) ⟨1072518, by rfl⟩ : syracuseStep 2860049 = 2145037) B2145037
theorem B500759 : Blo 499793 500759 := bstep (se 1 (by rfl) ⟨375569, by rfl⟩ : syracuseStep 500759 = 751139) B751139
theorem B762905 : Blo 499793 762905 := bstep (se 2 (by rfl) ⟨286089, by rfl⟩ : syracuseStep 762905 = 572179) B572179
theorem B500779 : Blo 499793 500779 := bstep (se 1 (by rfl) ⟨375584, by rfl⟩ : syracuseStep 500779 = 751169) B751169
theorem B500791 : Blo 499793 500791 := bstep (se 1 (by rfl) ⟨375593, by rfl⟩ : syracuseStep 500791 = 751187) B751187
theorem B500811 : Blo 499793 500811 := bstep (se 1 (by rfl) ⟨375608, by rfl⟩ : syracuseStep 500811 = 751217) B751217
theorem B566347 : Blo 499793 566347 := bstep (se 1 (by rfl) ⟨424760, by rfl⟩ : syracuseStep 566347 = 849521) B849521
theorem B500823 : Blo 499793 500823 := bstep (se 1 (by rfl) ⟨375617, by rfl⟩ : syracuseStep 500823 = 751235) B751235
theorem B500843 : Blo 499793 500843 := bstep (se 1 (by rfl) ⟨375632, by rfl⟩ : syracuseStep 500843 = 751265) B751265
theorem B500855 : Blo 499793 500855 := bstep (se 1 (by rfl) ⟨375641, by rfl⟩ : syracuseStep 500855 = 751283) B751283
theorem B500875 : Blo 499793 500875 := bstep (se 1 (by rfl) ⟨375656, by rfl⟩ : syracuseStep 500875 = 751313) B751313
theorem B2139281 : Blo 499793 2139281 := bstep (se 2 (by rfl) ⟨802230, by rfl⟩ : syracuseStep 2139281 = 1604461) B1604461
theorem B500887 : Blo 499793 500887 := bstep (se 1 (by rfl) ⟨375665, by rfl⟩ : syracuseStep 500887 = 751331) B751331
theorem B3220631 : Blo 499793 3220631 := bstep (se 1 (by rfl) ⟨2415473, by rfl⟩ : syracuseStep 3220631 = 4830947) B4830947
theorem B500907 : Blo 499793 500907 := bstep (se 1 (by rfl) ⟨375680, by rfl⟩ : syracuseStep 500907 = 751361) B751361
theorem B500919 : Blo 499793 500919 := bstep (se 1 (by rfl) ⟨375689, by rfl⟩ : syracuseStep 500919 = 751379) B751379
theorem B566455 : Blo 499793 566455 := bstep (se 1 (by rfl) ⟨424841, by rfl⟩ : syracuseStep 566455 = 849683) B849683
theorem B500939 : Blo 499793 500939 := bstep (se 1 (by rfl) ⟨375704, by rfl⟩ : syracuseStep 500939 = 751409) B751409
theorem B500951 : Blo 499793 500951 := bstep (se 1 (by rfl) ⟨375713, by rfl⟩ : syracuseStep 500951 = 751427) B751427
theorem B500971 : Blo 499793 500971 := bstep (se 1 (by rfl) ⟨375728, by rfl⟩ : syracuseStep 500971 = 751457) B751457
theorem B500983 : Blo 499793 500983 := bstep (se 1 (by rfl) ⟨375737, by rfl⟩ : syracuseStep 500983 = 751475) B751475
theorem B501003 : Blo 499793 501003 := bstep (se 1 (by rfl) ⟨375752, by rfl⟩ : syracuseStep 501003 = 751505) B751505
theorem B501015 : Blo 499793 501015 := bstep (se 1 (by rfl) ⟨375761, by rfl⟩ : syracuseStep 501015 = 751523) B751523
theorem B501035 : Blo 499793 501035 := bstep (se 1 (by rfl) ⟨375776, by rfl⟩ : syracuseStep 501035 = 751553) B751553
theorem B501047 : Blo 499793 501047 := bstep (se 1 (by rfl) ⟨375785, by rfl⟩ : syracuseStep 501047 = 751571) B751571
theorem B501067 : Blo 499793 501067 := bstep (se 1 (by rfl) ⟨375800, by rfl⟩ : syracuseStep 501067 = 751601) B751601
theorem B501079 : Blo 499793 501079 := bstep (se 1 (by rfl) ⟨375809, by rfl⟩ : syracuseStep 501079 = 751619) B751619
theorem B501099 : Blo 499793 501099 := bstep (se 1 (by rfl) ⟨375824, by rfl⟩ : syracuseStep 501099 = 751649) B751649
theorem B566635 : Blo 499793 566635 := bstep (se 1 (by rfl) ⟨424976, by rfl⟩ : syracuseStep 566635 = 849953) B849953
theorem B501111 : Blo 499793 501111 := bstep (se 1 (by rfl) ⟨375833, by rfl⟩ : syracuseStep 501111 = 751667) B751667
theorem B501131 : Blo 499793 501131 := bstep (se 1 (by rfl) ⟨375848, by rfl⟩ : syracuseStep 501131 = 751697) B751697
theorem B501143 : Blo 499793 501143 := bstep (se 1 (by rfl) ⟨375857, by rfl⟩ : syracuseStep 501143 = 751715) B751715
theorem B501163 : Blo 499793 501163 := bstep (se 1 (by rfl) ⟨375872, by rfl⟩ : syracuseStep 501163 = 751745) B751745
theorem B501175 : Blo 499793 501175 := bstep (se 1 (by rfl) ⟨375881, by rfl⟩ : syracuseStep 501175 = 751763) B751763
theorem B501195 : Blo 499793 501195 := bstep (se 1 (by rfl) ⟨375896, by rfl⟩ : syracuseStep 501195 = 751793) B751793
theorem B501207 : Blo 499793 501207 := bstep (se 1 (by rfl) ⟨375905, by rfl⟩ : syracuseStep 501207 = 751811) B751811
theorem B566743 : Blo 499793 566743 := bstep (se 1 (by rfl) ⟨425057, by rfl⟩ : syracuseStep 566743 = 850115) B850115
theorem B2860505 : Blo 499793 2860505 := bstep (se 2 (by rfl) ⟨1072689, by rfl⟩ : syracuseStep 2860505 = 2145379) B2145379
theorem B501227 : Blo 499793 501227 := bstep (se 1 (by rfl) ⟨375920, by rfl⟩ : syracuseStep 501227 = 751841) B751841
theorem B501239 : Blo 499793 501239 := bstep (se 1 (by rfl) ⟨375929, by rfl⟩ : syracuseStep 501239 = 751859) B751859
theorem B501259 : Blo 499793 501259 := bstep (se 1 (by rfl) ⟨375944, by rfl⟩ : syracuseStep 501259 = 751889) B751889
theorem B4826641 : Blo 499793 4826641 := bstep (se 2 (by rfl) ⟨1809990, by rfl⟩ : syracuseStep 4826641 = 3619981) B3619981
theorem B501271 : Blo 499793 501271 := bstep (se 1 (by rfl) ⟨375953, by rfl⟩ : syracuseStep 501271 = 751907) B751907
theorem B501291 : Blo 499793 501291 := bstep (se 1 (by rfl) ⟨375968, by rfl⟩ : syracuseStep 501291 = 751937) B751937
theorem B501303 : Blo 499793 501303 := bstep (se 1 (by rfl) ⟨375977, by rfl⟩ : syracuseStep 501303 = 751955) B751955
theorem B501323 : Blo 499793 501323 := bstep (se 1 (by rfl) ⟨375992, by rfl⟩ : syracuseStep 501323 = 751985) B751985
theorem B501335 : Blo 499793 501335 := bstep (se 1 (by rfl) ⟨376001, by rfl⟩ : syracuseStep 501335 = 752003) B752003
theorem B501355 : Blo 499793 501355 := bstep (se 1 (by rfl) ⟨376016, by rfl⟩ : syracuseStep 501355 = 752033) B752033
theorem B501367 : Blo 499793 501367 := bstep (se 1 (by rfl) ⟨376025, by rfl⟩ : syracuseStep 501367 = 752051) B752051
theorem B501387 : Blo 499793 501387 := bstep (se 1 (by rfl) ⟨376040, by rfl⟩ : syracuseStep 501387 = 752081) B752081
theorem B501399 : Blo 499793 501399 := bstep (se 1 (by rfl) ⟨376049, by rfl⟩ : syracuseStep 501399 = 752099) B752099
theorem B501419 : Blo 499793 501419 := bstep (se 1 (by rfl) ⟨376064, by rfl⟩ : syracuseStep 501419 = 752129) B752129
theorem B501431 : Blo 499793 501431 := bstep (se 1 (by rfl) ⟨376073, by rfl⟩ : syracuseStep 501431 = 752147) B752147
theorem B501451 : Blo 499793 501451 := bstep (se 1 (by rfl) ⟨376088, by rfl⟩ : syracuseStep 501451 = 752177) B752177
theorem B501463 : Blo 499793 501463 := bstep (se 1 (by rfl) ⟨376097, by rfl⟩ : syracuseStep 501463 = 752195) B752195
theorem B501483 : Blo 499793 501483 := bstep (se 1 (by rfl) ⟨376112, by rfl⟩ : syracuseStep 501483 = 752225) B752225
theorem B501495 : Blo 499793 501495 := bstep (se 1 (by rfl) ⟨376121, by rfl⟩ : syracuseStep 501495 = 752243) B752243
theorem B501515 : Blo 499793 501515 := bstep (se 1 (by rfl) ⟨376136, by rfl⟩ : syracuseStep 501515 = 752273) B752273
theorem B501527 : Blo 499793 501527 := bstep (se 1 (by rfl) ⟨376145, by rfl⟩ : syracuseStep 501527 = 752291) B752291
theorem B501547 : Blo 499793 501547 := bstep (se 1 (by rfl) ⟨376160, by rfl⟩ : syracuseStep 501547 = 752321) B752321
theorem B4171565 : Blo 499793 4171565 := bstep (se 3 (by rfl) ⟨782168, by rfl⟩ : syracuseStep 4171565 = 1564337) B1564337
theorem B1910573 : Blo 499793 1910573 := bstep (se 3 (by rfl) ⟨358232, by rfl⟩ : syracuseStep 1910573 = 716465) B716465
theorem B501559 : Blo 499793 501559 := bstep (se 1 (by rfl) ⟨376169, by rfl⟩ : syracuseStep 501559 = 752339) B752339
theorem B501579 : Blo 499793 501579 := bstep (se 1 (by rfl) ⟨376184, by rfl⟩ : syracuseStep 501579 = 752369) B752369
theorem B501591 : Blo 499793 501591 := bstep (se 1 (by rfl) ⟨376193, by rfl⟩ : syracuseStep 501591 = 752387) B752387
theorem B501611 : Blo 499793 501611 := bstep (se 1 (by rfl) ⟨376208, by rfl⟩ : syracuseStep 501611 = 752417) B752417
theorem B501623 : Blo 499793 501623 := bstep (se 1 (by rfl) ⟨376217, by rfl⟩ : syracuseStep 501623 = 752435) B752435
theorem B501643 : Blo 499793 501643 := bstep (se 1 (by rfl) ⟨376232, by rfl⟩ : syracuseStep 501643 = 752465) B752465
theorem B501655 : Blo 499793 501655 := bstep (se 1 (by rfl) ⟨376241, by rfl⟩ : syracuseStep 501655 = 752483) B752483
theorem B501675 : Blo 499793 501675 := bstep (se 1 (by rfl) ⟨376256, by rfl⟩ : syracuseStep 501675 = 752513) B752513
theorem B501687 : Blo 499793 501687 := bstep (se 1 (by rfl) ⟨376265, by rfl⟩ : syracuseStep 501687 = 752531) B752531
theorem B501707 : Blo 499793 501707 := bstep (se 1 (by rfl) ⟨376280, by rfl⟩ : syracuseStep 501707 = 752561) B752561
theorem B501719 : Blo 499793 501719 := bstep (se 1 (by rfl) ⟨376289, by rfl⟩ : syracuseStep 501719 = 752579) B752579
theorem B501739 : Blo 499793 501739 := bstep (se 1 (by rfl) ⟨376304, by rfl⟩ : syracuseStep 501739 = 752609) B752609
theorem B501751 : Blo 499793 501751 := bstep (se 1 (by rfl) ⟨376313, by rfl⟩ : syracuseStep 501751 = 752627) B752627
theorem B501771 : Blo 499793 501771 := bstep (se 1 (by rfl) ⟨376328, by rfl⟩ : syracuseStep 501771 = 752657) B752657
theorem B501783 : Blo 499793 501783 := bstep (se 1 (by rfl) ⟨376337, by rfl⟩ : syracuseStep 501783 = 752675) B752675
theorem B501803 : Blo 499793 501803 := bstep (se 1 (by rfl) ⟨376352, by rfl⟩ : syracuseStep 501803 = 752705) B752705
theorem B501815 : Blo 499793 501815 := bstep (se 1 (by rfl) ⟨376361, by rfl⟩ : syracuseStep 501815 = 752723) B752723
theorem B501835 : Blo 499793 501835 := bstep (se 1 (by rfl) ⟨376376, by rfl⟩ : syracuseStep 501835 = 752753) B752753
theorem B501847 : Blo 499793 501847 := bstep (se 1 (by rfl) ⟨376385, by rfl⟩ : syracuseStep 501847 = 752771) B752771
theorem B2140253 : Blo 499793 2140253 := bstep (se 3 (by rfl) ⟨401297, by rfl⟩ : syracuseStep 2140253 = 802595) B802595
theorem B501867 : Blo 499793 501867 := bstep (se 1 (by rfl) ⟨376400, by rfl⟩ : syracuseStep 501867 = 752801) B752801
theorem B501879 : Blo 499793 501879 := bstep (se 1 (by rfl) ⟨376409, by rfl⟩ : syracuseStep 501879 = 752819) B752819
theorem B501899 : Blo 499793 501899 := bstep (se 1 (by rfl) ⟨376424, by rfl⟩ : syracuseStep 501899 = 752849) B752849
theorem B501911 : Blo 499793 501911 := bstep (se 1 (by rfl) ⟨376433, by rfl⟩ : syracuseStep 501911 = 752867) B752867
theorem B1812631 : Blo 499793 1812631 := bstep (se 1 (by rfl) ⟨1359473, by rfl⟩ : syracuseStep 1812631 = 2718947) B2718947
theorem B501931 : Blo 499793 501931 := bstep (se 1 (by rfl) ⟨376448, by rfl⟩ : syracuseStep 501931 = 752897) B752897
theorem B17410229 : Blo 499793 17410229 := bstep (se 5 (by rfl) ⟨816104, by rfl⟩ : syracuseStep 17410229 = 1632209) B1632209
theorem B501943 : Blo 499793 501943 := bstep (se 1 (by rfl) ⟨376457, by rfl⟩ : syracuseStep 501943 = 752915) B752915
theorem B633035 : Blo 499793 633035 := bstep (se 1 (by rfl) ⟨474776, by rfl⟩ : syracuseStep 633035 = 949553) B949553
theorem B501963 : Blo 499793 501963 := bstep (se 1 (by rfl) ⟨376472, by rfl⟩ : syracuseStep 501963 = 752945) B752945
theorem B1124567 : Blo 499793 1124567 := bstep (se 1 (by rfl) ⟨843425, by rfl⟩ : syracuseStep 1124567 = 1686851) B1686851
theorem B501975 : Blo 499793 501975 := bstep (se 1 (by rfl) ⟨376481, by rfl⟩ : syracuseStep 501975 = 752963) B752963
theorem B501995 : Blo 499793 501995 := bstep (se 1 (by rfl) ⟨376496, by rfl⟩ : syracuseStep 501995 = 752993) B752993
theorem B502007 : Blo 499793 502007 := bstep (se 1 (by rfl) ⟨376505, by rfl⟩ : syracuseStep 502007 = 753011) B753011
theorem B15444229 : Blo 499793 15444229 := bstep (se 4 (by rfl) ⟨1447896, by rfl⟩ : syracuseStep 15444229 = 2895793) B2895793
theorem B502027 : Blo 499793 502027 := bstep (se 1 (by rfl) ⟨376520, by rfl⟩ : syracuseStep 502027 = 753041) B753041
theorem B502039 : Blo 499793 502039 := bstep (se 1 (by rfl) ⟨376529, by rfl⟩ : syracuseStep 502039 = 753059) B753059
theorem B502059 : Blo 499793 502059 := bstep (se 1 (by rfl) ⟨376544, by rfl⟩ : syracuseStep 502059 = 753089) B753089
theorem B502071 : Blo 499793 502071 := bstep (se 1 (by rfl) ⟨376553, by rfl⟩ : syracuseStep 502071 = 753107) B753107
theorem B502091 : Blo 499793 502091 := bstep (se 1 (by rfl) ⟨376568, by rfl⟩ : syracuseStep 502091 = 753137) B753137
theorem B502103 : Blo 499793 502103 := bstep (se 1 (by rfl) ⟨376577, by rfl⟩ : syracuseStep 502103 = 753155) B753155
theorem B502123 : Blo 499793 502123 := bstep (se 1 (by rfl) ⟨376592, by rfl⟩ : syracuseStep 502123 = 753185) B753185
theorem B502135 : Blo 499793 502135 := bstep (se 1 (by rfl) ⟨376601, by rfl⟩ : syracuseStep 502135 = 753203) B753203
theorem B1124747 : Blo 499793 1124747 := bstep (se 1 (by rfl) ⟨843560, by rfl⟩ : syracuseStep 1124747 = 1687121) B1687121
theorem B502155 : Blo 499793 502155 := bstep (se 1 (by rfl) ⟨376616, by rfl⟩ : syracuseStep 502155 = 753233) B753233
theorem B502167 : Blo 499793 502167 := bstep (se 1 (by rfl) ⟨376625, by rfl⟩ : syracuseStep 502167 = 753251) B753251
theorem B502187 : Blo 499793 502187 := bstep (se 1 (by rfl) ⟨376640, by rfl⟩ : syracuseStep 502187 = 753281) B753281
theorem B1354163 : Blo 499793 1354163 := bstep (se 1 (by rfl) ⟨1015622, by rfl⟩ : syracuseStep 1354163 = 2031245) B2031245
theorem B502199 : Blo 499793 502199 := bstep (se 1 (by rfl) ⟨376649, by rfl⟩ : syracuseStep 502199 = 753299) B753299
theorem B1124801 : Blo 499793 1124801 := bstep (se 2 (by rfl) ⟨421800, by rfl⟩ : syracuseStep 1124801 = 843601) B843601
theorem B502219 : Blo 499793 502219 := bstep (se 1 (by rfl) ⟨376664, by rfl⟩ : syracuseStep 502219 = 753329) B753329
theorem B502231 : Blo 499793 502231 := bstep (se 1 (by rfl) ⟨376673, by rfl⟩ : syracuseStep 502231 = 753347) B753347
theorem B502251 : Blo 499793 502251 := bstep (se 1 (by rfl) ⟨376688, by rfl⟩ : syracuseStep 502251 = 753377) B753377
theorem B502263 : Blo 499793 502263 := bstep (se 1 (by rfl) ⟨376697, by rfl⟩ : syracuseStep 502263 = 753395) B753395
theorem B502283 : Blo 499793 502283 := bstep (se 1 (by rfl) ⟨376712, by rfl⟩ : syracuseStep 502283 = 753425) B753425
theorem B502295 : Blo 499793 502295 := bstep (se 1 (by rfl) ⟨376721, by rfl⟩ : syracuseStep 502295 = 753443) B753443
theorem B502315 : Blo 499793 502315 := bstep (se 1 (by rfl) ⟨376736, by rfl⟩ : syracuseStep 502315 = 753473) B753473
theorem B1911347 : Blo 499793 1911347 := bstep (se 1 (by rfl) ⟨1433510, by rfl⟩ : syracuseStep 1911347 = 2867021) B2867021
theorem B502327 : Blo 499793 502327 := bstep (se 1 (by rfl) ⟨376745, by rfl⟩ : syracuseStep 502327 = 753491) B753491
theorem B502347 : Blo 499793 502347 := bstep (se 1 (by rfl) ⟨376760, by rfl⟩ : syracuseStep 502347 = 753521) B753521
theorem B502359 : Blo 499793 502359 := bstep (se 1 (by rfl) ⟨376769, by rfl⟩ : syracuseStep 502359 = 753539) B753539
theorem B502379 : Blo 499793 502379 := bstep (se 1 (by rfl) ⟨376784, by rfl⟩ : syracuseStep 502379 = 753569) B753569
theorem B502391 : Blo 499793 502391 := bstep (se 1 (by rfl) ⟨376793, by rfl⟩ : syracuseStep 502391 = 753587) B753587
theorem B502411 : Blo 499793 502411 := bstep (se 1 (by rfl) ⟨376808, by rfl⟩ : syracuseStep 502411 = 753617) B753617
theorem B502423 : Blo 499793 502423 := bstep (se 1 (by rfl) ⟨376817, by rfl⟩ : syracuseStep 502423 = 753635) B753635
theorem B1125017 : Blo 499793 1125017 := bstep (se 2 (by rfl) ⟨421881, by rfl⟩ : syracuseStep 1125017 = 843763) B843763
theorem B502443 : Blo 499793 502443 := bstep (se 1 (by rfl) ⟨376832, by rfl⟩ : syracuseStep 502443 = 753665) B753665
theorem B502455 : Blo 499793 502455 := bstep (se 1 (by rfl) ⟨376841, by rfl⟩ : syracuseStep 502455 = 753683) B753683
theorem B535243 : Blo 499793 535243 := bstep (se 1 (by rfl) ⟨401432, by rfl⟩ : syracuseStep 535243 = 802865) B802865
theorem B502475 : Blo 499793 502475 := bstep (se 1 (by rfl) ⟨376856, by rfl⟩ : syracuseStep 502475 = 753713) B753713
theorem B502487 : Blo 499793 502487 := bstep (se 1 (by rfl) ⟨376865, by rfl⟩ : syracuseStep 502487 = 753731) B753731
theorem B502507 : Blo 499793 502507 := bstep (se 1 (by rfl) ⟨376880, by rfl⟩ : syracuseStep 502507 = 753761) B753761
theorem B1125107 : Blo 499793 1125107 := bstep (se 1 (by rfl) ⟨843830, by rfl⟩ : syracuseStep 1125107 = 1687661) B1687661
theorem B502519 : Blo 499793 502519 := bstep (se 1 (by rfl) ⟨376889, by rfl⟩ : syracuseStep 502519 = 753779) B753779
theorem B502539 : Blo 499793 502539 := bstep (se 1 (by rfl) ⟨376904, by rfl⟩ : syracuseStep 502539 = 753809) B753809
theorem B1125143 : Blo 499793 1125143 := bstep (se 1 (by rfl) ⟨843857, by rfl⟩ : syracuseStep 1125143 = 1687715) B1687715
theorem B502551 : Blo 499793 502551 := bstep (se 1 (by rfl) ⟨376913, by rfl⟩ : syracuseStep 502551 = 753827) B753827
theorem B502571 : Blo 499793 502571 := bstep (se 1 (by rfl) ⟨376928, by rfl⟩ : syracuseStep 502571 = 753857) B753857
theorem B502583 : Blo 499793 502583 := bstep (se 1 (by rfl) ⟨376937, by rfl⟩ : syracuseStep 502583 = 753875) B753875
theorem B502603 : Blo 499793 502603 := bstep (se 1 (by rfl) ⟨376952, by rfl⟩ : syracuseStep 502603 = 753905) B753905
theorem B502615 : Blo 499793 502615 := bstep (se 1 (by rfl) ⟨376961, by rfl⟩ : syracuseStep 502615 = 753923) B753923
theorem B502635 : Blo 499793 502635 := bstep (se 1 (by rfl) ⟨376976, by rfl⟩ : syracuseStep 502635 = 753953) B753953
theorem B502647 : Blo 499793 502647 := bstep (se 1 (by rfl) ⟨376985, by rfl⟩ : syracuseStep 502647 = 753971) B753971
theorem B633739 : Blo 499793 633739 := bstep (se 1 (by rfl) ⟨475304, by rfl⟩ : syracuseStep 633739 = 950609) B950609
theorem B502667 : Blo 499793 502667 := bstep (se 1 (by rfl) ⟨377000, by rfl⟩ : syracuseStep 502667 = 754001) B754001
theorem B502679 : Blo 499793 502679 := bstep (se 1 (by rfl) ⟨377009, by rfl⟩ : syracuseStep 502679 = 754019) B754019
theorem B502699 : Blo 499793 502699 := bstep (se 1 (by rfl) ⟨377024, by rfl⟩ : syracuseStep 502699 = 754049) B754049
theorem B502711 : Blo 499793 502711 := bstep (se 1 (by rfl) ⟨377033, by rfl⟩ : syracuseStep 502711 = 754067) B754067
theorem B1125323 : Blo 499793 1125323 := bstep (se 1 (by rfl) ⟨843992, by rfl⟩ : syracuseStep 1125323 = 1687985) B1687985
theorem B502731 : Blo 499793 502731 := bstep (se 1 (by rfl) ⟨377048, by rfl⟩ : syracuseStep 502731 = 754097) B754097
theorem B502743 : Blo 499793 502743 := bstep (se 1 (by rfl) ⟨377057, by rfl⟩ : syracuseStep 502743 = 754115) B754115
theorem B502763 : Blo 499793 502763 := bstep (se 1 (by rfl) ⟨377072, by rfl⟩ : syracuseStep 502763 = 754145) B754145
theorem B502775 : Blo 499793 502775 := bstep (se 1 (by rfl) ⟨377081, by rfl⟩ : syracuseStep 502775 = 754163) B754163
theorem B1125377 : Blo 499793 1125377 := bstep (se 2 (by rfl) ⟨422016, by rfl⟩ : syracuseStep 1125377 = 844033) B844033
theorem B502795 : Blo 499793 502795 := bstep (se 1 (by rfl) ⟨377096, by rfl⟩ : syracuseStep 502795 = 754193) B754193
theorem B502807 : Blo 499793 502807 := bstep (se 1 (by rfl) ⟨377105, by rfl⟩ : syracuseStep 502807 = 754211) B754211
theorem B502827 : Blo 499793 502827 := bstep (se 1 (by rfl) ⟨377120, by rfl⟩ : syracuseStep 502827 = 754241) B754241
theorem B502839 : Blo 499793 502839 := bstep (se 1 (by rfl) ⟨377129, by rfl⟩ : syracuseStep 502839 = 754259) B754259
theorem B502859 : Blo 499793 502859 := bstep (se 1 (by rfl) ⟨377144, by rfl⟩ : syracuseStep 502859 = 754289) B754289
theorem B502871 : Blo 499793 502871 := bstep (se 1 (by rfl) ⟨377153, by rfl⟩ : syracuseStep 502871 = 754307) B754307
theorem B502891 : Blo 499793 502891 := bstep (se 1 (by rfl) ⟨377168, by rfl⟩ : syracuseStep 502891 = 754337) B754337
theorem B502903 : Blo 499793 502903 := bstep (se 1 (by rfl) ⟨377177, by rfl⟩ : syracuseStep 502903 = 754355) B754355
theorem B502923 : Blo 499793 502923 := bstep (se 1 (by rfl) ⟨377192, by rfl⟩ : syracuseStep 502923 = 754385) B754385
theorem B2403479 : Blo 499793 2403479 := bstep (se 1 (by rfl) ⟨1802609, by rfl⟩ : syracuseStep 2403479 = 3605219) B3605219
theorem B634007 : Blo 499793 634007 := bstep (se 1 (by rfl) ⟨475505, by rfl⟩ : syracuseStep 634007 = 951011) B951011
theorem B502935 : Blo 499793 502935 := bstep (se 1 (by rfl) ⟨377201, by rfl⟩ : syracuseStep 502935 = 754403) B754403
theorem B502955 : Blo 499793 502955 := bstep (se 1 (by rfl) ⟨377216, by rfl⟩ : syracuseStep 502955 = 754433) B754433
theorem B502967 : Blo 499793 502967 := bstep (se 1 (by rfl) ⟨377225, by rfl⟩ : syracuseStep 502967 = 754451) B754451
theorem B502987 : Blo 499793 502987 := bstep (se 1 (by rfl) ⟨377240, by rfl⟩ : syracuseStep 502987 = 754481) B754481
theorem B502999 : Blo 499793 502999 := bstep (se 1 (by rfl) ⟨377249, by rfl⟩ : syracuseStep 502999 = 754499) B754499
theorem B1125593 : Blo 499793 1125593 := bstep (se 2 (by rfl) ⟨422097, by rfl⟩ : syracuseStep 1125593 = 844195) B844195
theorem B503019 : Blo 499793 503019 := bstep (se 1 (by rfl) ⟨377264, by rfl⟩ : syracuseStep 503019 = 754529) B754529
theorem B503031 : Blo 499793 503031 := bstep (se 1 (by rfl) ⟨377273, by rfl⟩ : syracuseStep 503031 = 754547) B754547
theorem B503051 : Blo 499793 503051 := bstep (se 1 (by rfl) ⟨377288, by rfl⟩ : syracuseStep 503051 = 754577) B754577
theorem B503063 : Blo 499793 503063 := bstep (se 1 (by rfl) ⟨377297, by rfl⟩ : syracuseStep 503063 = 754595) B754595
theorem B503083 : Blo 499793 503083 := bstep (se 1 (by rfl) ⟨377312, by rfl⟩ : syracuseStep 503083 = 754625) B754625
theorem B1125683 : Blo 499793 1125683 := bstep (se 1 (by rfl) ⟨844262, by rfl⟩ : syracuseStep 1125683 = 1688525) B1688525
theorem B503095 : Blo 499793 503095 := bstep (se 1 (by rfl) ⟨377321, by rfl⟩ : syracuseStep 503095 = 754643) B754643
theorem B503115 : Blo 499793 503115 := bstep (se 1 (by rfl) ⟨377336, by rfl⟩ : syracuseStep 503115 = 754673) B754673
theorem B1125719 : Blo 499793 1125719 := bstep (se 1 (by rfl) ⟨844289, by rfl⟩ : syracuseStep 1125719 = 1688579) B1688579
theorem B503127 : Blo 499793 503127 := bstep (se 1 (by rfl) ⟨377345, by rfl⟩ : syracuseStep 503127 = 754691) B754691
theorem B4271453 : Blo 499793 4271453 := bstep (se 3 (by rfl) ⟨800897, by rfl⟩ : syracuseStep 4271453 = 1601795) B1601795
theorem B4566365 : Blo 499793 4566365 := bstep (se 3 (by rfl) ⟨856193, by rfl⟩ : syracuseStep 4566365 = 1712387) B1712387
theorem B503147 : Blo 499793 503147 := bstep (se 1 (by rfl) ⟨377360, by rfl⟩ : syracuseStep 503147 = 754721) B754721
theorem B503159 : Blo 499793 503159 := bstep (se 1 (by rfl) ⟨377369, by rfl⟩ : syracuseStep 503159 = 754739) B754739
theorem B503179 : Blo 499793 503179 := bstep (se 1 (by rfl) ⟨377384, by rfl⟩ : syracuseStep 503179 = 754769) B754769
theorem B503191 : Blo 499793 503191 := bstep (se 1 (by rfl) ⟨377393, by rfl⟩ : syracuseStep 503191 = 754787) B754787
theorem B503211 : Blo 499793 503211 := bstep (se 1 (by rfl) ⟨377408, by rfl⟩ : syracuseStep 503211 = 754817) B754817
theorem B503223 : Blo 499793 503223 := bstep (se 1 (by rfl) ⟨377417, by rfl⟩ : syracuseStep 503223 = 754835) B754835
theorem B503243 : Blo 499793 503243 := bstep (se 1 (by rfl) ⟨377432, by rfl⟩ : syracuseStep 503243 = 754865) B754865
theorem B503255 : Blo 499793 503255 := bstep (se 1 (by rfl) ⟨377441, by rfl⟩ : syracuseStep 503255 = 754883) B754883
theorem B503275 : Blo 499793 503275 := bstep (se 1 (by rfl) ⟨377456, by rfl⟩ : syracuseStep 503275 = 754913) B754913
theorem B503287 : Blo 499793 503287 := bstep (se 1 (by rfl) ⟨377465, by rfl⟩ : syracuseStep 503287 = 754931) B754931
theorem B1125899 : Blo 499793 1125899 := bstep (se 1 (by rfl) ⟨844424, by rfl⟩ : syracuseStep 1125899 = 1688849) B1688849
theorem B503307 : Blo 499793 503307 := bstep (se 1 (by rfl) ⟨377480, by rfl⟩ : syracuseStep 503307 = 754961) B754961
theorem B503319 : Blo 499793 503319 := bstep (se 1 (by rfl) ⟨377489, by rfl⟩ : syracuseStep 503319 = 754979) B754979
theorem B503339 : Blo 499793 503339 := bstep (se 1 (by rfl) ⟨377504, by rfl⟩ : syracuseStep 503339 = 755009) B755009
theorem B2141741 : Blo 499793 2141741 := bstep (se 3 (by rfl) ⟨401576, by rfl⟩ : syracuseStep 2141741 = 803153) B803153
theorem B503351 : Blo 499793 503351 := bstep (se 1 (by rfl) ⟨377513, by rfl⟩ : syracuseStep 503351 = 755027) B755027
theorem B1125953 : Blo 499793 1125953 := bstep (se 2 (by rfl) ⟨422232, by rfl⟩ : syracuseStep 1125953 = 844465) B844465
theorem B503371 : Blo 499793 503371 := bstep (se 1 (by rfl) ⟨377528, by rfl⟩ : syracuseStep 503371 = 755057) B755057
theorem B601687 : Blo 499793 601687 := bstep (se 1 (by rfl) ⟨451265, by rfl⟩ : syracuseStep 601687 = 902531) B902531
theorem B503383 : Blo 499793 503383 := bstep (se 1 (by rfl) ⟨377537, by rfl⟩ : syracuseStep 503383 = 755075) B755075
theorem B503403 : Blo 499793 503403 := bstep (se 1 (by rfl) ⟨377552, by rfl⟩ : syracuseStep 503403 = 755105) B755105
theorem B503415 : Blo 499793 503415 := bstep (se 1 (by rfl) ⟨377561, by rfl⟩ : syracuseStep 503415 = 755123) B755123
theorem B503435 : Blo 499793 503435 := bstep (se 1 (by rfl) ⟨377576, by rfl⟩ : syracuseStep 503435 = 755153) B755153
theorem B503447 : Blo 499793 503447 := bstep (se 1 (by rfl) ⟨377585, by rfl⟩ : syracuseStep 503447 = 755171) B755171
theorem B503467 : Blo 499793 503467 := bstep (se 1 (by rfl) ⟨377600, by rfl⟩ : syracuseStep 503467 = 755201) B755201
theorem B2404019 : Blo 499793 2404019 := bstep (se 1 (by rfl) ⟨1803014, by rfl⟩ : syracuseStep 2404019 = 3606029) B3606029
theorem B503479 : Blo 499793 503479 := bstep (se 1 (by rfl) ⟨377609, by rfl⟩ : syracuseStep 503479 = 755219) B755219
theorem B503499 : Blo 499793 503499 := bstep (se 1 (by rfl) ⟨377624, by rfl⟩ : syracuseStep 503499 = 755249) B755249
theorem B503511 : Blo 499793 503511 := bstep (se 1 (by rfl) ⟨377633, by rfl⟩ : syracuseStep 503511 = 755267) B755267
theorem B503531 : Blo 499793 503531 := bstep (se 1 (by rfl) ⟨377648, by rfl⟩ : syracuseStep 503531 = 755297) B755297
theorem B536311 : Blo 499793 536311 := bstep (se 1 (by rfl) ⟨402233, by rfl⟩ : syracuseStep 536311 = 804467) B804467
theorem B503543 : Blo 499793 503543 := bstep (se 1 (by rfl) ⟨377657, by rfl⟩ : syracuseStep 503543 = 755315) B755315
theorem B503563 : Blo 499793 503563 := bstep (se 1 (by rfl) ⟨377672, by rfl⟩ : syracuseStep 503563 = 755345) B755345
theorem B503575 : Blo 499793 503575 := bstep (se 1 (by rfl) ⟨377681, by rfl⟩ : syracuseStep 503575 = 755363) B755363
theorem B1126169 : Blo 499793 1126169 := bstep (se 2 (by rfl) ⟨422313, by rfl⟩ : syracuseStep 1126169 = 844627) B844627
theorem B3813155 : Blo 499793 3813155 := bstep (se 1 (by rfl) ⟨2859866, by rfl⟩ : syracuseStep 3813155 = 5719733) B5719733
theorem B503595 : Blo 499793 503595 := bstep (se 1 (by rfl) ⟨377696, by rfl⟩ : syracuseStep 503595 = 755393) B755393
theorem B503607 : Blo 499793 503607 := bstep (se 1 (by rfl) ⟨377705, by rfl⟩ : syracuseStep 503607 = 755411) B755411
theorem B503627 : Blo 499793 503627 := bstep (se 1 (by rfl) ⟨377720, by rfl⟩ : syracuseStep 503627 = 755441) B755441
theorem B634711 : Blo 499793 634711 := bstep (se 1 (by rfl) ⟨476033, by rfl⟩ : syracuseStep 634711 = 952067) B952067
theorem B503639 : Blo 499793 503639 := bstep (se 1 (by rfl) ⟨377729, by rfl⟩ : syracuseStep 503639 = 755459) B755459
theorem B10170211 : Blo 499793 10170211 := bstep (se 1 (by rfl) ⟨7627658, by rfl⟩ : syracuseStep 10170211 = 15255317) B15255317
theorem B503659 : Blo 499793 503659 := bstep (se 1 (by rfl) ⟨377744, by rfl⟩ : syracuseStep 503659 = 755489) B755489
theorem B1126259 : Blo 499793 1126259 := bstep (se 1 (by rfl) ⟨844694, by rfl⟩ : syracuseStep 1126259 = 1689389) B1689389
theorem B503671 : Blo 499793 503671 := bstep (se 1 (by rfl) ⟨377753, by rfl⟩ : syracuseStep 503671 = 755507) B755507
theorem B2535299 : Blo 499793 2535299 := bstep (se 1 (by rfl) ⟨1901474, by rfl⟩ : syracuseStep 2535299 = 3802949) B3802949
theorem B503691 : Blo 499793 503691 := bstep (se 1 (by rfl) ⟨377768, by rfl⟩ : syracuseStep 503691 = 755537) B755537
theorem B1126295 : Blo 499793 1126295 := bstep (se 1 (by rfl) ⟨844721, by rfl⟩ : syracuseStep 1126295 = 1689443) B1689443
theorem B503703 : Blo 499793 503703 := bstep (se 1 (by rfl) ⟨377777, by rfl⟩ : syracuseStep 503703 = 755555) B755555
theorem B503723 : Blo 499793 503723 := bstep (se 1 (by rfl) ⟨377792, by rfl⟩ : syracuseStep 503723 = 755585) B755585
theorem B503735 : Blo 499793 503735 := bstep (se 1 (by rfl) ⟨377801, by rfl⟩ : syracuseStep 503735 = 755603) B755603
theorem B503755 : Blo 499793 503755 := bstep (se 1 (by rfl) ⟨377816, by rfl⟩ : syracuseStep 503755 = 755633) B755633
theorem B503767 : Blo 499793 503767 := bstep (se 1 (by rfl) ⟨377825, by rfl⟩ : syracuseStep 503767 = 755651) B755651
theorem B1814489 : Blo 499793 1814489 := bstep (se 2 (by rfl) ⟨680433, by rfl⟩ : syracuseStep 1814489 = 1360867) B1360867
theorem B503787 : Blo 499793 503787 := bstep (se 1 (by rfl) ⟨377840, by rfl⟩ : syracuseStep 503787 = 755681) B755681
theorem B1912835 : Blo 499793 1912835 := bstep (se 1 (by rfl) ⟨1434626, by rfl⟩ : syracuseStep 1912835 = 2869253) B2869253
theorem B1126475 : Blo 499793 1126475 := bstep (se 1 (by rfl) ⟨844856, by rfl⟩ : syracuseStep 1126475 = 1689713) B1689713
theorem B1126529 : Blo 499793 1126529 := bstep (se 2 (by rfl) ⟨422448, by rfl⟩ : syracuseStep 1126529 = 844897) B844897
theorem B1126745 : Blo 499793 1126745 := bstep (se 2 (by rfl) ⟨422529, by rfl⟩ : syracuseStep 1126745 = 845059) B845059
theorem B1126835 : Blo 499793 1126835 := bstep (se 1 (by rfl) ⟨845126, by rfl⟩ : syracuseStep 1126835 = 1690253) B1690253
theorem B1126871 : Blo 499793 1126871 := bstep (se 1 (by rfl) ⟨845153, by rfl⟩ : syracuseStep 1126871 = 1690307) B1690307
theorem B537131 : Blo 499793 537131 := bstep (se 1 (by rfl) ⟨402848, by rfl⟩ : syracuseStep 537131 = 805697) B805697
theorem B1127051 : Blo 499793 1127051 := bstep (se 1 (by rfl) ⟨845288, by rfl⟩ : syracuseStep 1127051 = 1690577) B1690577
theorem B1127105 : Blo 499793 1127105 := bstep (se 2 (by rfl) ⟨422664, by rfl⟩ : syracuseStep 1127105 = 845329) B845329
theorem B2175761 : Blo 499793 2175761 := bstep (se 2 (by rfl) ⟨815910, by rfl⟩ : syracuseStep 2175761 = 1631821) B1631821
theorem B1127321 : Blo 499793 1127321 := bstep (se 2 (by rfl) ⟨422745, by rfl⟩ : syracuseStep 1127321 = 845491) B845491
theorem B1127411 : Blo 499793 1127411 := bstep (se 1 (by rfl) ⟨845558, by rfl⟩ : syracuseStep 1127411 = 1691117) B1691117
theorem B1127447 : Blo 499793 1127447 := bstep (se 1 (by rfl) ⟨845585, by rfl⟩ : syracuseStep 1127447 = 1691171) B1691171
theorem B1127627 : Blo 499793 1127627 := bstep (se 1 (by rfl) ⟨845720, by rfl⟩ : syracuseStep 1127627 = 1691441) B1691441
theorem B1651915 : Blo 499793 1651915 := bstep (se 1 (by rfl) ⟨1238936, by rfl⟩ : syracuseStep 1651915 = 2477873) B2477873
theorem B1127681 : Blo 499793 1127681 := bstep (se 2 (by rfl) ⟨422880, by rfl⟩ : syracuseStep 1127681 = 845761) B845761
theorem B603595 : Blo 499793 603595 := bstep (se 1 (by rfl) ⟨452696, by rfl⟩ : syracuseStep 603595 = 905393) B905393
theorem B1127897 : Blo 499793 1127897 := bstep (se 2 (by rfl) ⟨422961, by rfl⟩ : syracuseStep 1127897 = 845923) B845923
theorem B2143705 : Blo 499793 2143705 := bstep (se 2 (by rfl) ⟨803889, by rfl⟩ : syracuseStep 2143705 = 1607779) B1607779
theorem B636427 : Blo 499793 636427 := bstep (se 1 (by rfl) ⟨477320, by rfl⟩ : syracuseStep 636427 = 954641) B954641
theorem B1127987 : Blo 499793 1127987 := bstep (se 1 (by rfl) ⟨845990, by rfl⟩ : syracuseStep 1127987 = 1691981) B1691981
theorem B1128023 : Blo 499793 1128023 := bstep (se 1 (by rfl) ⟨846017, by rfl⟩ : syracuseStep 1128023 = 1692035) B1692035
theorem B4077149 : Blo 499793 4077149 := bstep (se 3 (by rfl) ⟨764465, by rfl⟩ : syracuseStep 4077149 = 1528931) B1528931
theorem B9647747 : Blo 499793 9647747 := bstep (se 1 (by rfl) ⟨7235810, by rfl⟩ : syracuseStep 9647747 = 14471621) B14471621
theorem B571051 : Blo 499793 571051 := bstep (se 1 (by rfl) ⟨428288, by rfl⟩ : syracuseStep 571051 = 856577) B856577
theorem B1128203 : Blo 499793 1128203 := bstep (se 1 (by rfl) ⟨846152, by rfl⟩ : syracuseStep 1128203 = 1692305) B1692305
theorem B1128257 : Blo 499793 1128257 := bstep (se 2 (by rfl) ⟨423096, by rfl⟩ : syracuseStep 1128257 = 846193) B846193
theorem B1128473 : Blo 499793 1128473 := bstep (se 2 (by rfl) ⟨423177, by rfl⟩ : syracuseStep 1128473 = 846355) B846355
theorem B1423453 : Blo 499793 1423453 := bstep (se 3 (by rfl) ⟨266897, by rfl⟩ : syracuseStep 1423453 = 533795) B533795
theorem B1128563 : Blo 499793 1128563 := bstep (se 1 (by rfl) ⟨846422, by rfl⟩ : syracuseStep 1128563 = 1692845) B1692845
theorem B1128599 : Blo 499793 1128599 := bstep (se 1 (by rfl) ⟨846449, by rfl⟩ : syracuseStep 1128599 = 1692899) B1692899
theorem B2209943 : Blo 499793 2209943 := bstep (se 1 (by rfl) ⟨1657457, by rfl⟩ : syracuseStep 2209943 = 3314915) B3314915
theorem B1128779 : Blo 499793 1128779 := bstep (se 1 (by rfl) ⟨846584, by rfl⟩ : syracuseStep 1128779 = 1693169) B1693169
theorem B1128833 : Blo 499793 1128833 := bstep (se 2 (by rfl) ⟨423312, by rfl⟩ : syracuseStep 1128833 = 846625) B846625
theorem B2144663 : Blo 499793 2144663 := bstep (se 1 (by rfl) ⟨1608497, by rfl⟩ : syracuseStep 2144663 = 3216995) B3216995
theorem B637399 : Blo 499793 637399 := bstep (se 1 (by rfl) ⟨478049, by rfl⟩ : syracuseStep 637399 = 956099) B956099
theorem B4340299 : Blo 499793 4340299 := bstep (se 1 (by rfl) ⟨3255224, by rfl⟩ : syracuseStep 4340299 = 6510449) B6510449
theorem B1129049 : Blo 499793 1129049 := bstep (se 2 (by rfl) ⟨423393, by rfl⟩ : syracuseStep 1129049 = 846787) B846787
theorem B1129139 : Blo 499793 1129139 := bstep (se 1 (by rfl) ⟨846854, by rfl⟩ : syracuseStep 1129139 = 1693709) B1693709
theorem B1129175 : Blo 499793 1129175 := bstep (se 1 (by rfl) ⟨846881, by rfl⟩ : syracuseStep 1129175 = 1693763) B1693763
theorem B2865881 : Blo 499793 2865881 := bstep (se 2 (by rfl) ⟨1074705, by rfl⟩ : syracuseStep 2865881 = 2149411) B2149411
theorem B1391411 : Blo 499793 1391411 := bstep (se 1 (by rfl) ⟨1043558, by rfl⟩ : syracuseStep 1391411 = 2087117) B2087117
theorem B19249973 : Blo 499793 19249973 := bstep (se 5 (by rfl) ⟨902342, by rfl⟩ : syracuseStep 19249973 = 1804685) B1804685
theorem B15448897 : Blo 499793 15448897 := bstep (se 2 (by rfl) ⟨5793336, by rfl⟩ : syracuseStep 15448897 = 11586673) B11586673
theorem B1260353 : Blo 499793 1260353 := bstep (se 2 (by rfl) ⟨472632, by rfl⟩ : syracuseStep 1260353 = 945265) B945265
theorem B1129355 : Blo 499793 1129355 := bstep (se 1 (by rfl) ⟨847016, by rfl⟩ : syracuseStep 1129355 = 1694033) B1694033
theorem B1129409 : Blo 499793 1129409 := bstep (se 2 (by rfl) ⟨423528, by rfl⟩ : syracuseStep 1129409 = 847057) B847057
theorem B6437981 : Blo 499793 6437981 := bstep (se 3 (by rfl) ⟨1207121, by rfl⟩ : syracuseStep 6437981 = 2414243) B2414243
theorem B1129625 : Blo 499793 1129625 := bstep (se 2 (by rfl) ⟨423609, by rfl⟩ : syracuseStep 1129625 = 847219) B847219
theorem B1129715 : Blo 499793 1129715 := bstep (se 1 (by rfl) ⟨847286, by rfl⟩ : syracuseStep 1129715 = 1694573) B1694573
theorem B1129751 : Blo 499793 1129751 := bstep (se 1 (by rfl) ⟨847313, by rfl⟩ : syracuseStep 1129751 = 1694627) B1694627
theorem B1359127 : Blo 499793 1359127 := bstep (se 1 (by rfl) ⟨1019345, by rfl⟩ : syracuseStep 1359127 = 2038691) B2038691
theorem B1424729 : Blo 499793 1424729 := bstep (se 2 (by rfl) ⟨534273, by rfl⟩ : syracuseStep 1424729 = 1068547) B1068547
theorem B1162585 : Blo 499793 1162585 := bstep (se 2 (by rfl) ⟨435969, by rfl⟩ : syracuseStep 1162585 = 871939) B871939
theorem B802199 : Blo 499793 802199 := bstep (se 1 (by rfl) ⟨601649, by rfl⟩ : syracuseStep 802199 = 1203299) B1203299
theorem B1129931 : Blo 499793 1129931 := bstep (se 1 (by rfl) ⟨847448, by rfl⟩ : syracuseStep 1129931 = 1694897) B1694897
theorem B1129985 : Blo 499793 1129985 := bstep (se 2 (by rfl) ⟨423744, by rfl⟩ : syracuseStep 1129985 = 847489) B847489
theorem B2539025 : Blo 499793 2539025 := bstep (se 2 (by rfl) ⟨952134, by rfl⟩ : syracuseStep 2539025 = 1904269) B1904269
theorem B2539187 : Blo 499793 2539187 := bstep (se 1 (by rfl) ⟨1904390, by rfl⟩ : syracuseStep 2539187 = 3808781) B3808781
theorem B1130201 : Blo 499793 1130201 := bstep (se 2 (by rfl) ⟨423825, by rfl⟩ : syracuseStep 1130201 = 847651) B847651
theorem B1130291 : Blo 499793 1130291 := bstep (se 1 (by rfl) ⟨847718, by rfl⟩ : syracuseStep 1130291 = 1695437) B1695437
theorem B1130327 : Blo 499793 1130327 := bstep (se 1 (by rfl) ⟨847745, by rfl⟩ : syracuseStep 1130327 = 1695491) B1695491
theorem B1982339 : Blo 499793 1982339 := bstep (se 1 (by rfl) ⟨1486754, by rfl⟩ : syracuseStep 1982339 = 2973509) B2973509
theorem B3063703 : Blo 499793 3063703 := bstep (se 1 (by rfl) ⟨2297777, by rfl⟩ : syracuseStep 3063703 = 4595555) B4595555
theorem B1687499 : Blo 499793 1687499 := bstep (se 1 (by rfl) ⟨1265624, by rfl⟩ : syracuseStep 1687499 = 2531249) B2531249
theorem B1130507 : Blo 499793 1130507 := bstep (se 1 (by rfl) ⟨847880, by rfl⟩ : syracuseStep 1130507 = 1695761) B1695761
theorem B1130561 : Blo 499793 1130561 := bstep (se 2 (by rfl) ⟨423960, by rfl⟩ : syracuseStep 1130561 = 847921) B847921
theorem B7356509 : Blo 499793 7356509 := bstep (se 3 (by rfl) ⟨1379345, by rfl⟩ : syracuseStep 7356509 = 2758691) B2758691
theorem B4079747 : Blo 499793 4079747 := bstep (se 1 (by rfl) ⟨3059810, by rfl⟩ : syracuseStep 4079747 = 6119621) B6119621
theorem B508087 : Blo 499793 508087 := bstep (se 1 (by rfl) ⟨381065, by rfl⟩ : syracuseStep 508087 = 762131) B762131
theorem B573623 : Blo 499793 573623 := bstep (se 1 (by rfl) ⟨430217, by rfl⟩ : syracuseStep 573623 = 860435) B860435
theorem B1687769 : Blo 499793 1687769 := bstep (se 2 (by rfl) ⟨632913, by rfl⟩ : syracuseStep 1687769 = 1265827) B1265827
theorem B901363 : Blo 499793 901363 := bstep (se 1 (by rfl) ⟨676022, by rfl⟩ : syracuseStep 901363 = 1352045) B1352045
theorem B1130777 : Blo 499793 1130777 := bstep (se 2 (by rfl) ⟨424041, by rfl⟩ : syracuseStep 1130777 = 848083) B848083
theorem B2867521 : Blo 499793 2867521 := bstep (se 2 (by rfl) ⟨1075320, by rfl⟩ : syracuseStep 2867521 = 2150641) B2150641
theorem B1130867 : Blo 499793 1130867 := bstep (se 1 (by rfl) ⟨848150, by rfl⟩ : syracuseStep 1130867 = 1696301) B1696301
theorem B1130903 : Blo 499793 1130903 := bstep (se 1 (by rfl) ⟨848177, by rfl⟩ : syracuseStep 1130903 = 1696355) B1696355
theorem B4833715 : Blo 499793 4833715 := bstep (se 1 (by rfl) ⟨3625286, by rfl⟩ : syracuseStep 4833715 = 7250573) B7250573
theorem B1360307 : Blo 499793 1360307 := bstep (se 1 (by rfl) ⟨1020230, by rfl⟩ : syracuseStep 1360307 = 2040461) B2040461
theorem B803287 : Blo 499793 803287 := bstep (se 1 (by rfl) ⟨602465, by rfl⟩ : syracuseStep 803287 = 1204931) B1204931
theorem B3654179 : Blo 499793 3654179 := bstep (se 1 (by rfl) ⟨2740634, by rfl⟩ : syracuseStep 3654179 = 5481269) B5481269
theorem B1131083 : Blo 499793 1131083 := bstep (se 1 (by rfl) ⟨848312, by rfl⟩ : syracuseStep 1131083 = 1696625) B1696625
theorem B1131137 : Blo 499793 1131137 := bstep (se 2 (by rfl) ⟨424176, by rfl⟩ : syracuseStep 1131137 = 848353) B848353
theorem B4571909 : Blo 499793 4571909 := bstep (se 4 (by rfl) ⟨428616, by rfl⟩ : syracuseStep 4571909 = 857233) B857233
theorem B541463 : Blo 499793 541463 := bstep (se 1 (by rfl) ⟨406097, by rfl⟩ : syracuseStep 541463 = 812195) B812195
theorem B1524545 : Blo 499793 1524545 := bstep (se 2 (by rfl) ⟨571704, by rfl⟩ : syracuseStep 1524545 = 1143409) B1143409
theorem B1131353 : Blo 499793 1131353 := bstep (se 2 (by rfl) ⟨424257, by rfl⟩ : syracuseStep 1131353 = 848515) B848515
theorem B1688471 : Blo 499793 1688471 := bstep (se 1 (by rfl) ⟨1266353, by rfl⟩ : syracuseStep 1688471 = 2532707) B2532707
theorem B1131443 : Blo 499793 1131443 := bstep (se 1 (by rfl) ⟨848582, by rfl⟩ : syracuseStep 1131443 = 1697165) B1697165
theorem B1426369 : Blo 499793 1426369 := bstep (se 2 (by rfl) ⟨534888, by rfl⟩ : syracuseStep 1426369 = 1069777) B1069777
theorem B1131479 : Blo 499793 1131479 := bstep (se 1 (by rfl) ⟨848609, by rfl⟩ : syracuseStep 1131479 = 1697219) B1697219
theorem B3818501 : Blo 499793 3818501 := bstep (se 4 (by rfl) ⟨357984, by rfl⟩ : syracuseStep 3818501 = 715969) B715969
theorem B1131659 : Blo 499793 1131659 := bstep (se 1 (by rfl) ⟨848744, by rfl⟩ : syracuseStep 1131659 = 1697489) B1697489
theorem B1131713 : Blo 499793 1131713 := bstep (se 2 (by rfl) ⟨424392, by rfl⟩ : syracuseStep 1131713 = 848785) B848785
theorem B968075 : Blo 499793 968075 := bstep (se 1 (by rfl) ⟨726056, by rfl⟩ : syracuseStep 968075 = 1452113) B1452113
theorem B1131929 : Blo 499793 1131929 := bstep (se 2 (by rfl) ⟨424473, by rfl⟩ : syracuseStep 1131929 = 848947) B848947
theorem B1689011 : Blo 499793 1689011 := bstep (se 1 (by rfl) ⟨1266758, by rfl⟩ : syracuseStep 1689011 = 2533517) B2533517
theorem B1590749 : Blo 499793 1590749 := bstep (se 3 (by rfl) ⟨298265, by rfl⟩ : syracuseStep 1590749 = 596531) B596531
theorem B1132019 : Blo 499793 1132019 := bstep (se 1 (by rfl) ⟨849014, by rfl⟩ : syracuseStep 1132019 = 1698029) B1698029
theorem B1132055 : Blo 499793 1132055 := bstep (se 1 (by rfl) ⟨849041, by rfl⟩ : syracuseStep 1132055 = 1698083) B1698083
theorem B2541131 : Blo 499793 2541131 := bstep (se 1 (by rfl) ⟨1905848, by rfl⟩ : syracuseStep 2541131 = 3811697) B3811697
theorem B804505 : Blo 499793 804505 := bstep (se 2 (by rfl) ⟨301689, by rfl⟩ : syracuseStep 804505 = 603379) B603379
theorem B1689281 : Blo 499793 1689281 := bstep (se 2 (by rfl) ⟨633480, by rfl⟩ : syracuseStep 1689281 = 1266961) B1266961
theorem B1132235 : Blo 499793 1132235 := bstep (se 1 (by rfl) ⟨849176, by rfl⟩ : syracuseStep 1132235 = 1698353) B1698353
theorem B1132289 : Blo 499793 1132289 := bstep (se 2 (by rfl) ⟨424608, by rfl⟩ : syracuseStep 1132289 = 849217) B849217
theorem B2148113 : Blo 499793 2148113 := bstep (se 2 (by rfl) ⟨805542, by rfl⟩ : syracuseStep 2148113 = 1611085) B1611085
theorem B902935 : Blo 499793 902935 := bstep (se 1 (by rfl) ⟨677201, by rfl⟩ : syracuseStep 902935 = 1354403) B1354403
theorem B509815 : Blo 499793 509815 := bstep (se 1 (by rfl) ⟨382361, by rfl⟩ : syracuseStep 509815 = 764723) B764723
theorem B1132505 : Blo 499793 1132505 := bstep (se 2 (by rfl) ⟨424689, by rfl⟩ : syracuseStep 1132505 = 849379) B849379
theorem B1132595 : Blo 499793 1132595 := bstep (se 1 (by rfl) ⟨849446, by rfl⟩ : syracuseStep 1132595 = 1698893) B1698893
theorem B2902081 : Blo 499793 2902081 := bstep (se 2 (by rfl) ⟨1088280, by rfl⟩ : syracuseStep 2902081 = 2176561) B2176561
theorem B1132631 : Blo 499793 1132631 := bstep (se 1 (by rfl) ⟨849473, by rfl⟩ : syracuseStep 1132631 = 1698947) B1698947
theorem B1689821 : Blo 499793 1689821 := bstep (se 3 (by rfl) ⟨316841, by rfl⟩ : syracuseStep 1689821 = 633683) B633683
theorem B1132811 : Blo 499793 1132811 := bstep (se 1 (by rfl) ⟨849608, by rfl⟩ : syracuseStep 1132811 = 1699217) B1699217
theorem B1132865 : Blo 499793 1132865 := bstep (se 2 (by rfl) ⟨424824, by rfl⟩ : syracuseStep 1132865 = 849649) B849649
theorem B2279897 : Blo 499793 2279897 := bstep (se 2 (by rfl) ⟨854961, by rfl⟩ : syracuseStep 2279897 = 1709923) B1709923
theorem B903641 : Blo 499793 903641 := bstep (se 2 (by rfl) ⟨338865, by rfl⟩ : syracuseStep 903641 = 677731) B677731
theorem B1133081 : Blo 499793 1133081 := bstep (se 2 (by rfl) ⟨424905, by rfl⟩ : syracuseStep 1133081 = 849811) B849811
theorem B1428043 : Blo 499793 1428043 := bstep (se 1 (by rfl) ⟨1071032, by rfl⟩ : syracuseStep 1428043 = 2142065) B2142065
theorem B1133171 : Blo 499793 1133171 := bstep (se 1 (by rfl) ⟨849878, by rfl⟩ : syracuseStep 1133171 = 1699757) B1699757
theorem B1133207 : Blo 499793 1133207 := bstep (se 1 (by rfl) ⟨849905, by rfl⟩ : syracuseStep 1133207 = 1699811) B1699811
theorem B2149037 : Blo 499793 2149037 := bstep (se 3 (by rfl) ⟨402944, by rfl⟩ : syracuseStep 2149037 = 805889) B805889
theorem B1067735 : Blo 499793 1067735 := bstep (se 1 (by rfl) ⟨800801, by rfl⟩ : syracuseStep 1067735 = 1601603) B1601603
theorem B5163841 : Blo 499793 5163841 := bstep (se 2 (by rfl) ⟨1936440, by rfl⟩ : syracuseStep 5163841 = 3872881) B3872881
theorem B1133387 : Blo 499793 1133387 := bstep (se 1 (by rfl) ⟨850040, by rfl⟩ : syracuseStep 1133387 = 1700081) B1700081
theorem B1428317 : Blo 499793 1428317 := bstep (se 3 (by rfl) ⟨267809, by rfl⟩ : syracuseStep 1428317 = 535619) B535619
theorem B1133441 : Blo 499793 1133441 := bstep (se 2 (by rfl) ⟨425040, by rfl⟩ : syracuseStep 1133441 = 850081) B850081
theorem B1068299 : Blo 499793 1068299 := bstep (se 1 (by rfl) ⟨801224, by rfl⟩ : syracuseStep 1068299 = 1602449) B1602449
theorem B2542913 : Blo 499793 2542913 := bstep (se 2 (by rfl) ⟨953592, by rfl⟩ : syracuseStep 2542913 = 1907185) B1907185
theorem B1690955 : Blo 499793 1690955 := bstep (se 1 (by rfl) ⟨1268216, by rfl⟩ : syracuseStep 1690955 = 2536433) B2536433
theorem B3820931 : Blo 499793 3820931 := bstep (se 1 (by rfl) ⟨2865698, by rfl⟩ : syracuseStep 3820931 = 5731397) B5731397
theorem B1691225 : Blo 499793 1691225 := bstep (se 2 (by rfl) ⟨634209, by rfl⟩ : syracuseStep 1691225 = 1268419) B1268419
theorem B4083377 : Blo 499793 4083377 := bstep (se 2 (by rfl) ⟨1531266, by rfl⟩ : syracuseStep 4083377 = 3062533) B3062533
theorem B6082253 : Blo 499793 6082253 := bstep (se 3 (by rfl) ⟨1140422, by rfl⟩ : syracuseStep 6082253 = 2280845) B2280845
theorem B1265483 : Blo 499793 1265483 := bstep (se 1 (by rfl) ⟨949112, by rfl⟩ : syracuseStep 1265483 = 1898225) B1898225
theorem B1068889 : Blo 499793 1068889 := bstep (se 2 (by rfl) ⟨400833, by rfl⟩ : syracuseStep 1068889 = 801667) B801667
theorem B2150489 : Blo 499793 2150489 := bstep (se 2 (by rfl) ⟨806433, by rfl⟩ : syracuseStep 2150489 = 1612867) B1612867
theorem B1527959 : Blo 499793 1527959 := bstep (se 1 (by rfl) ⟨1145969, by rfl⟩ : syracuseStep 1527959 = 2291939) B2291939
theorem B545015 : Blo 499793 545015 := bstep (se 1 (by rfl) ⟨408761, by rfl⟩ : syracuseStep 545015 = 817523) B817523
theorem B1691927 : Blo 499793 1691927 := bstep (se 1 (by rfl) ⟨1268945, by rfl⟩ : syracuseStep 1691927 = 2537891) B2537891
theorem B905623 : Blo 499793 905623 := bstep (se 1 (by rfl) ⟨679217, by rfl⟩ : syracuseStep 905623 = 1358435) B1358435
theorem B4805081 : Blo 499793 4805081 := bstep (se 2 (by rfl) ⟨1801905, by rfl⟩ : syracuseStep 4805081 = 3603811) B3603811
theorem B4280849 : Blo 499793 4280849 := bstep (se 2 (by rfl) ⟨1605318, by rfl⟩ : syracuseStep 4280849 = 3210637) B3210637
theorem B1266455 : Blo 499793 1266455 := bstep (se 1 (by rfl) ⟨949841, by rfl⟩ : syracuseStep 1266455 = 1899683) B1899683
theorem B1692467 : Blo 499793 1692467 := bstep (se 1 (by rfl) ⟨1269350, by rfl⟩ : syracuseStep 1692467 = 2538701) B2538701
theorem B1200971 : Blo 499793 1200971 := bstep (se 1 (by rfl) ⟨900728, by rfl⟩ : syracuseStep 1200971 = 1801457) B1801457
theorem B1069939 : Blo 499793 1069939 := bstep (se 1 (by rfl) ⟨802454, by rfl⟩ : syracuseStep 1069939 = 1604909) B1604909
theorem B1692737 : Blo 499793 1692737 := bstep (se 2 (by rfl) ⟨634776, by rfl⟩ : syracuseStep 1692737 = 1269553) B1269553
theorem B1430617 : Blo 499793 1430617 := bstep (se 2 (by rfl) ⟨536481, by rfl⟩ : syracuseStep 1430617 = 1072963) B1072963
theorem B2544857 : Blo 499793 2544857 := bstep (se 2 (by rfl) ⟨954321, by rfl⟩ : syracuseStep 2544857 = 1908643) B1908643
theorem B1267123 : Blo 499793 1267123 := bstep (se 1 (by rfl) ⟨950342, by rfl⟩ : syracuseStep 1267123 = 1900685) B1900685
theorem B644567 : Blo 499793 644567 := bstep (se 1 (by rfl) ⟨483425, by rfl⟩ : syracuseStep 644567 = 966851) B966851
theorem B6411737 : Blo 499793 6411737 := bstep (se 2 (by rfl) ⟨2404401, by rfl⟩ : syracuseStep 6411737 = 4808803) B4808803
theorem B1267265 : Blo 499793 1267265 := bstep (se 2 (by rfl) ⟨475224, by rfl⟩ : syracuseStep 1267265 = 950449) B950449
theorem B939607 : Blo 499793 939607 := bstep (se 1 (by rfl) ⟨704705, by rfl⟩ : syracuseStep 939607 = 1409411) B1409411
theorem B1693277 : Blo 499793 1693277 := bstep (se 3 (by rfl) ⟨317489, by rfl⟩ : syracuseStep 1693277 = 634979) B634979
theorem B1431233 : Blo 499793 1431233 := bstep (se 2 (by rfl) ⟨536712, by rfl⟩ : syracuseStep 1431233 = 1073425) B1073425
theorem B907159 : Blo 499793 907159 := bstep (se 1 (by rfl) ⟨680369, by rfl⟩ : syracuseStep 907159 = 1360739) B1360739
theorem B1071425 : Blo 499793 1071425 := bstep (se 2 (by rfl) ⟨401784, by rfl⟩ : syracuseStep 1071425 = 803569) B803569
theorem B645655 : Blo 499793 645655 := bstep (se 1 (by rfl) ⟨484241, by rfl⟩ : syracuseStep 645655 = 968483) B968483
theorem B612887 : Blo 499793 612887 := bstep (se 1 (by rfl) ⟨459665, by rfl⟩ : syracuseStep 612887 = 919331) B919331
theorem B1071767 : Blo 499793 1071767 := bstep (se 1 (by rfl) ⟨803825, by rfl⟩ : syracuseStep 1071767 = 1607651) B1607651
theorem B1694411 : Blo 499793 1694411 := bstep (se 1 (by rfl) ⟨1270808, by rfl⟩ : syracuseStep 1694411 = 2541617) B2541617
theorem B3824333 : Blo 499793 3824333 := bstep (se 3 (by rfl) ⟨717062, by rfl⟩ : syracuseStep 3824333 = 1434125) B1434125
theorem B2546477 : Blo 499793 2546477 := bstep (se 3 (by rfl) ⟨477464, by rfl⟩ : syracuseStep 2546477 = 954929) B954929
theorem B1268531 : Blo 499793 1268531 := bstep (se 1 (by rfl) ⟨951398, by rfl⟩ : syracuseStep 1268531 = 1902797) B1902797
theorem B3431347 : Blo 499793 3431347 := bstep (se 1 (by rfl) ⟨2573510, by rfl⟩ : syracuseStep 3431347 = 5147021) B5147021
theorem B1072075 : Blo 499793 1072075 := bstep (se 1 (by rfl) ⟨804056, by rfl⟩ : syracuseStep 1072075 = 1608113) B1608113
theorem B1694681 : Blo 499793 1694681 := bstep (se 2 (by rfl) ⟨635505, by rfl⟩ : syracuseStep 1694681 = 1271011) B1271011
theorem B3824819 : Blo 499793 3824819 := bstep (se 1 (by rfl) ⟨2868614, by rfl⟩ : syracuseStep 3824819 = 5737229) B5737229
theorem B679115 : Blo 499793 679115 := bstep (se 1 (by rfl) ⟨509336, by rfl⟩ : syracuseStep 679115 = 1018673) B1018673
theorem B1269067 : Blo 499793 1269067 := bstep (se 1 (by rfl) ⟨951800, by rfl⟩ : syracuseStep 1269067 = 1903601) B1903601
theorem B1269209 : Blo 499793 1269209 := bstep (se 2 (by rfl) ⟨475953, by rfl⟩ : syracuseStep 1269209 = 951907) B951907
theorem B1695383 : Blo 499793 1695383 := bstep (se 1 (by rfl) ⟨1271537, by rfl⟩ : syracuseStep 1695383 = 2543075) B2543075
theorem B1433305 : Blo 499793 1433305 := bstep (se 2 (by rfl) ⟨537489, by rfl⟩ : syracuseStep 1433305 = 1074979) B1074979
theorem B1171223 : Blo 499793 1171223 := bstep (se 1 (by rfl) ⟨878417, by rfl⟩ : syracuseStep 1171223 = 1756835) B1756835
theorem B1072921 : Blo 499793 1072921 := bstep (se 2 (by rfl) ⟨402345, by rfl⟩ : syracuseStep 1072921 = 804691) B804691
theorem B712729 : Blo 499793 712729 := bstep (se 2 (by rfl) ⟨267273, by rfl⟩ : syracuseStep 712729 = 534547) B534547
theorem B843851 : Blo 499793 843851 := bstep (se 1 (by rfl) ⟨632888, by rfl⟩ : syracuseStep 843851 = 1265777) B1265777
theorem B1433693 : Blo 499793 1433693 := bstep (se 3 (by rfl) ⟨268817, by rfl⟩ : syracuseStep 1433693 = 537635) B537635
theorem B8151191 : Blo 499793 8151191 := bstep (se 1 (by rfl) ⟨6113393, by rfl⟩ : syracuseStep 8151191 = 12226787) B12226787
theorem B1695923 : Blo 499793 1695923 := bstep (se 1 (by rfl) ⟨1271942, by rfl⟩ : syracuseStep 1695923 = 2543885) B2543885
theorem B843979 : Blo 499793 843979 := bstep (se 1 (by rfl) ⟨632984, by rfl⟩ : syracuseStep 843979 = 1265969) B1265969
theorem B1270039 : Blo 499793 1270039 := bstep (se 1 (by rfl) ⟨952529, by rfl⟩ : syracuseStep 1270039 = 1905059) B1905059
theorem B2711873 : Blo 499793 2711873 := bstep (se 2 (by rfl) ⟨1016952, by rfl⟩ : syracuseStep 2711873 = 2033905) B2033905
theorem B844121 : Blo 499793 844121 := bstep (se 2 (by rfl) ⟨316545, by rfl⟩ : syracuseStep 844121 = 633091) B633091
theorem B1696193 : Blo 499793 1696193 := bstep (se 2 (by rfl) ⟨636072, by rfl⟩ : syracuseStep 1696193 = 1272145) B1272145
theorem B844249 : Blo 499793 844249 := bstep (se 2 (by rfl) ⟨316593, by rfl⟩ : syracuseStep 844249 = 633187) B633187
theorem B2417303 : Blo 499793 2417303 := bstep (se 1 (by rfl) ⟨1812977, by rfl⟩ : syracuseStep 2417303 = 3625955) B3625955
theorem B1270475 : Blo 499793 1270475 := bstep (se 1 (by rfl) ⟨952856, by rfl⟩ : syracuseStep 1270475 = 1905713) B1905713
theorem B1630937 : Blo 499793 1630937 := bstep (se 2 (by rfl) ⟨611601, by rfl⟩ : syracuseStep 1630937 = 1223203) B1223203
theorem B713623 : Blo 499793 713623 := bstep (se 1 (by rfl) ⟨535217, by rfl⟩ : syracuseStep 713623 = 1070435) B1070435
theorem B1696733 : Blo 499793 1696733 := bstep (se 3 (by rfl) ⟨318137, by rfl⟩ : syracuseStep 1696733 = 636275) B636275
theorem B844823 : Blo 499793 844823 := bstep (se 1 (by rfl) ⟨633617, by rfl⟩ : syracuseStep 844823 = 1267235) B1267235
theorem B1074227 : Blo 499793 1074227 := bstep (se 1 (by rfl) ⟨805670, by rfl⟩ : syracuseStep 1074227 = 1611341) B1611341
theorem B1270849 : Blo 499793 1270849 := bstep (se 2 (by rfl) ⟨476568, by rfl⟩ : syracuseStep 1270849 = 953137) B953137
theorem B844951 : Blo 499793 844951 := bstep (se 1 (by rfl) ⟨633713, by rfl⟩ : syracuseStep 844951 = 1267427) B1267427
theorem B3433859 : Blo 499793 3433859 := bstep (se 1 (by rfl) ⟨2575394, by rfl⟩ : syracuseStep 3433859 = 5150789) B5150789
theorem B714187 : Blo 499793 714187 := bstep (se 1 (by rfl) ⟨535640, by rfl⟩ : syracuseStep 714187 = 1071281) B1071281
theorem B2287121 : Blo 499793 2287121 := bstep (se 2 (by rfl) ⟨857670, by rfl⟩ : syracuseStep 2287121 = 1715341) B1715341
theorem B1271447 : Blo 499793 1271447 := bstep (se 1 (by rfl) ⟨953585, by rfl⟩ : syracuseStep 1271447 = 1907171) B1907171
theorem B845579 : Blo 499793 845579 := bstep (se 1 (by rfl) ⟨634184, by rfl⟩ : syracuseStep 845579 = 1268369) B1268369
theorem B2713475 : Blo 499793 2713475 := bstep (se 1 (by rfl) ⟨2035106, by rfl⟩ : syracuseStep 2713475 = 4070213) B4070213
theorem B845707 : Blo 499793 845707 := bstep (se 1 (by rfl) ⟨634280, by rfl⟩ : syracuseStep 845707 = 1268561) B1268561
theorem B4646807 : Blo 499793 4646807 := bstep (se 1 (by rfl) ⟨3485105, by rfl⟩ : syracuseStep 4646807 = 6970211) B6970211
theorem B845849 : Blo 499793 845849 := bstep (se 2 (by rfl) ⟨317193, by rfl⟩ : syracuseStep 845849 = 634387) B634387
theorem B6285347 : Blo 499793 6285347 := bstep (se 1 (by rfl) ⟨4714010, by rfl⟩ : syracuseStep 6285347 = 9428021) B9428021
theorem B1697867 : Blo 499793 1697867 := bstep (se 1 (by rfl) ⟨1273400, by rfl⟩ : syracuseStep 1697867 = 2546801) B2546801
theorem B2418781 : Blo 499793 2418781 := bstep (se 3 (by rfl) ⟨453521, by rfl⟩ : syracuseStep 2418781 = 907043) B907043
theorem B845977 : Blo 499793 845977 := bstep (se 2 (by rfl) ⟨317241, by rfl⟩ : syracuseStep 845977 = 634483) B634483
theorem B12216581 : Blo 499793 12216581 := bstep (se 4 (by rfl) ⟨1145304, by rfl⟩ : syracuseStep 12216581 = 2290609) B2290609
theorem B2713931 : Blo 499793 2713931 := bstep (se 1 (by rfl) ⟨2035448, by rfl⟩ : syracuseStep 2713931 = 4070897) B4070897
theorem B1698137 : Blo 499793 1698137 := bstep (se 2 (by rfl) ⟨636801, by rfl⟩ : syracuseStep 1698137 = 1273603) B1273603
theorem B2713949 : Blo 499793 2713949 := bstep (se 3 (by rfl) ⟨508865, by rfl⟩ : syracuseStep 2713949 = 1017731) B1017731
theorem B1272257 : Blo 499793 1272257 := bstep (se 2 (by rfl) ⟨477096, by rfl⟩ : syracuseStep 1272257 = 954193) B954193
theorem B1075799 : Blo 499793 1075799 := bstep (se 1 (by rfl) ⟨806849, by rfl⟩ : syracuseStep 1075799 = 1613699) B1613699
theorem B2550365 : Blo 499793 2550365 := bstep (se 3 (by rfl) ⟨478193, by rfl⟩ : syracuseStep 2550365 = 956387) B956387
theorem B846551 : Blo 499793 846551 := bstep (se 1 (by rfl) ⟨634913, by rfl⟩ : syracuseStep 846551 = 1269827) B1269827
theorem B846679 : Blo 499793 846679 := bstep (se 1 (by rfl) ⟨635009, by rfl⟩ : syracuseStep 846679 = 1270019) B1270019
theorem B715673 : Blo 499793 715673 := bstep (se 2 (by rfl) ⟨268377, by rfl⟩ : syracuseStep 715673 = 536755) B536755
theorem B1207219 : Blo 499793 1207219 := bstep (se 1 (by rfl) ⟨905414, by rfl⟩ : syracuseStep 1207219 = 1810829) B1810829
theorem B1272793 : Blo 499793 1272793 := bstep (se 2 (by rfl) ⟨477297, by rfl⟩ : syracuseStep 1272793 = 954595) B954595
theorem B1698839 : Blo 499793 1698839 := bstep (se 1 (by rfl) ⟨1274129, by rfl⟩ : syracuseStep 1698839 = 2548259) B2548259
theorem B1928267 : Blo 499793 1928267 := bstep (se 1 (by rfl) ⟨1446200, by rfl⟩ : syracuseStep 1928267 = 2892401) B2892401
theorem B3796145 : Blo 499793 3796145 := bstep (se 2 (by rfl) ⟨1423554, by rfl⟩ : syracuseStep 3796145 = 2847109) B2847109
theorem B1633459 : Blo 499793 1633459 := bstep (se 1 (by rfl) ⟨1225094, by rfl⟩ : syracuseStep 1633459 = 2450189) B2450189
theorem B7236965 : Blo 499793 7236965 := bstep (se 4 (by rfl) ⟨678465, by rfl⟩ : syracuseStep 7236965 = 1356931) B1356931
theorem B847307 : Blo 499793 847307 := bstep (se 1 (by rfl) ⟨635480, by rfl⟩ : syracuseStep 847307 = 1270961) B1270961
theorem B716311 : Blo 499793 716311 := bstep (se 1 (by rfl) ⟨537233, by rfl⟩ : syracuseStep 716311 = 1074467) B1074467
theorem B1699379 : Blo 499793 1699379 := bstep (se 1 (by rfl) ⟨1274534, by rfl⟩ : syracuseStep 1699379 = 2549069) B2549069
theorem B847435 : Blo 499793 847435 := bstep (se 1 (by rfl) ⟨635576, by rfl⟩ : syracuseStep 847435 = 1271153) B1271153
theorem B3796631 : Blo 499793 3796631 := bstep (se 1 (by rfl) ⟨2847473, by rfl⟩ : syracuseStep 3796631 = 5694947) B5694947
theorem B847577 : Blo 499793 847577 := bstep (se 2 (by rfl) ⟨317841, by rfl⟩ : syracuseStep 847577 = 635683) B635683
theorem B1699649 : Blo 499793 1699649 := bstep (se 2 (by rfl) ⟨637368, by rfl⟩ : syracuseStep 1699649 = 1274737) B1274737
theorem B847705 : Blo 499793 847705 := bstep (se 2 (by rfl) ⟨317889, by rfl⟩ : syracuseStep 847705 = 635779) B635779
theorem B1208267 : Blo 499793 1208267 := bstep (se 1 (by rfl) ⟨906200, by rfl⟩ : syracuseStep 1208267 = 1812401) B1812401
theorem B1273907 : Blo 499793 1273907 := bstep (se 1 (by rfl) ⟨955430, by rfl⟩ : syracuseStep 1273907 = 1910861) B1910861
theorem B749771 : Blo 499793 749771 := bstep (se 1 (by rfl) ⟨562328, by rfl⟩ : syracuseStep 749771 = 1124657) B1124657
theorem B749783 : Blo 499793 749783 := bstep (se 1 (by rfl) ⟨562337, by rfl⟩ : syracuseStep 749783 = 1124675) B1124675
theorem B717017 : Blo 499793 717017 := bstep (se 2 (by rfl) ⟨268881, by rfl⟩ : syracuseStep 717017 = 537763) B537763
theorem B749849 : Blo 499793 749849 := bstep (se 2 (by rfl) ⟨281193, by rfl⟩ : syracuseStep 749849 = 562387) B562387
theorem B717131 : Blo 499793 717131 := bstep (se 1 (by rfl) ⟨537848, by rfl⟩ : syracuseStep 717131 = 1075697) B1075697
theorem B1274201 : Blo 499793 1274201 := bstep (se 2 (by rfl) ⟨477825, by rfl⟩ : syracuseStep 1274201 = 955651) B955651
theorem B1700189 : Blo 499793 1700189 := bstep (se 3 (by rfl) ⟨318785, by rfl⟩ : syracuseStep 1700189 = 637571) B637571
theorem B749963 : Blo 499793 749963 := bstep (se 1 (by rfl) ⟨562472, by rfl⟩ : syracuseStep 749963 = 1124945) B1124945
theorem B749975 : Blo 499793 749975 := bstep (se 1 (by rfl) ⟨562481, by rfl⟩ : syracuseStep 749975 = 1124963) B1124963
theorem B848279 : Blo 499793 848279 := bstep (se 1 (by rfl) ⟨636209, by rfl⟩ : syracuseStep 848279 = 1272419) B1272419
theorem B750041 : Blo 499793 750041 := bstep (se 2 (by rfl) ⟨281265, by rfl⟩ : syracuseStep 750041 = 562531) B562531
theorem B6844945 : Blo 499793 6844945 := bstep (se 2 (by rfl) ⟨2566854, by rfl⟩ : syracuseStep 6844945 = 5133709) B5133709
theorem B848407 : Blo 499793 848407 := bstep (se 1 (by rfl) ⟨636305, by rfl⟩ : syracuseStep 848407 = 1272611) B1272611
theorem B2224691 : Blo 499793 2224691 := bstep (se 1 (by rfl) ⟨1668518, by rfl⟩ : syracuseStep 2224691 = 3337037) B3337037
theorem B750155 : Blo 499793 750155 := bstep (se 1 (by rfl) ⟨562616, by rfl⟩ : syracuseStep 750155 = 1125233) B1125233
theorem B750167 : Blo 499793 750167 := bstep (se 1 (by rfl) ⟨562625, by rfl⟩ : syracuseStep 750167 = 1125251) B1125251
theorem B2847383 : Blo 499793 2847383 := bstep (se 1 (by rfl) ⟨2135537, by rfl⟩ : syracuseStep 2847383 = 4271075) B4271075
theorem B750233 : Blo 499793 750233 := bstep (se 2 (by rfl) ⟨281337, by rfl⟩ : syracuseStep 750233 = 562675) B562675
theorem B750347 : Blo 499793 750347 := bstep (se 1 (by rfl) ⟨562760, by rfl⟩ : syracuseStep 750347 = 1125521) B1125521
theorem B750359 : Blo 499793 750359 := bstep (se 1 (by rfl) ⟨562769, by rfl⟩ : syracuseStep 750359 = 1125539) B1125539
theorem B750425 : Blo 499793 750425 := bstep (se 2 (by rfl) ⟨281409, by rfl⟩ : syracuseStep 750425 = 562819) B562819
theorem B750539 : Blo 499793 750539 := bstep (se 1 (by rfl) ⟨562904, by rfl⟩ : syracuseStep 750539 = 1125809) B1125809
theorem B750551 : Blo 499793 750551 := bstep (se 1 (by rfl) ⟨562913, by rfl⟩ : syracuseStep 750551 = 1125827) B1125827
theorem B750617 : Blo 499793 750617 := bstep (se 2 (by rfl) ⟨281481, by rfl⟩ : syracuseStep 750617 = 562963) B562963
theorem B750731 : Blo 499793 750731 := bstep (se 1 (by rfl) ⟨563048, by rfl⟩ : syracuseStep 750731 = 1126097) B1126097
theorem B849035 : Blo 499793 849035 := bstep (se 1 (by rfl) ⟨636776, by rfl⟩ : syracuseStep 849035 = 1273553) B1273553
theorem B750743 : Blo 499793 750743 := bstep (se 1 (by rfl) ⟨563057, by rfl⟩ : syracuseStep 750743 = 1126115) B1126115
theorem B750809 : Blo 499793 750809 := bstep (se 2 (by rfl) ⟨281553, by rfl⟩ : syracuseStep 750809 = 563107) B563107
theorem B849163 : Blo 499793 849163 := bstep (se 1 (by rfl) ⟨636872, by rfl⟩ : syracuseStep 849163 = 1273745) B1273745
theorem B750923 : Blo 499793 750923 := bstep (se 1 (by rfl) ⟨563192, by rfl⟩ : syracuseStep 750923 = 1126385) B1126385
theorem B750935 : Blo 499793 750935 := bstep (se 1 (by rfl) ⟨563201, by rfl⟩ : syracuseStep 750935 = 1126403) B1126403
theorem B751001 : Blo 499793 751001 := bstep (se 2 (by rfl) ⟨281625, by rfl⟩ : syracuseStep 751001 = 563251) B563251
theorem B849305 : Blo 499793 849305 := bstep (se 2 (by rfl) ⟨318489, by rfl⟩ : syracuseStep 849305 = 636979) B636979
theorem B1603037 : Blo 499793 1603037 := bstep (se 3 (by rfl) ⟨300569, by rfl⟩ : syracuseStep 1603037 = 601139) B601139
theorem B751115 : Blo 499793 751115 := bstep (se 1 (by rfl) ⟨563336, by rfl⟩ : syracuseStep 751115 = 1126673) B1126673
theorem B751127 : Blo 499793 751127 := bstep (se 1 (by rfl) ⟨563345, by rfl⟩ : syracuseStep 751127 = 1126691) B1126691
theorem B849433 : Blo 499793 849433 := bstep (se 2 (by rfl) ⟨318537, by rfl⟩ : syracuseStep 849433 = 637075) B637075
theorem B1963565 : Blo 499793 1963565 := bstep (se 3 (by rfl) ⟨368168, by rfl⟩ : syracuseStep 1963565 = 736337) B736337
theorem B751193 : Blo 499793 751193 := bstep (se 2 (by rfl) ⟨281697, by rfl⟩ : syracuseStep 751193 = 563395) B563395
theorem B751307 : Blo 499793 751307 := bstep (se 1 (by rfl) ⟨563480, by rfl⟩ : syracuseStep 751307 = 1126961) B1126961
theorem B685783 : Blo 499793 685783 := bstep (se 1 (by rfl) ⟨514337, by rfl⟩ : syracuseStep 685783 = 1028675) B1028675
theorem B751319 : Blo 499793 751319 := bstep (se 1 (by rfl) ⟨563489, by rfl⟩ : syracuseStep 751319 = 1126979) B1126979
theorem B751385 : Blo 499793 751385 := bstep (se 2 (by rfl) ⟨281769, by rfl⟩ : syracuseStep 751385 = 563539) B563539
theorem B751499 : Blo 499793 751499 := bstep (se 1 (by rfl) ⟨563624, by rfl⟩ : syracuseStep 751499 = 1127249) B1127249
theorem B751511 : Blo 499793 751511 := bstep (se 1 (by rfl) ⟨563633, by rfl⟩ : syracuseStep 751511 = 1127267) B1127267
theorem B2029529 : Blo 499793 2029529 := bstep (se 2 (by rfl) ⟨761073, by rfl⟩ : syracuseStep 2029529 = 1522147) B1522147
theorem B751577 : Blo 499793 751577 := bstep (se 2 (by rfl) ⟨281841, by rfl⟩ : syracuseStep 751577 = 563683) B563683
theorem B751691 : Blo 499793 751691 := bstep (se 1 (by rfl) ⟨563768, by rfl⟩ : syracuseStep 751691 = 1127537) B1127537
theorem B751703 : Blo 499793 751703 := bstep (se 1 (by rfl) ⟨563777, by rfl⟩ : syracuseStep 751703 = 1127555) B1127555
theorem B850007 : Blo 499793 850007 := bstep (se 1 (by rfl) ⟨637505, by rfl⟩ : syracuseStep 850007 = 1275011) B1275011
theorem B751769 : Blo 499793 751769 := bstep (se 2 (by rfl) ⟨281913, by rfl⟩ : syracuseStep 751769 = 563827) B563827
theorem B850135 : Blo 499793 850135 := bstep (se 1 (by rfl) ⟨637601, by rfl⟩ : syracuseStep 850135 = 1275203) B1275203
theorem B751883 : Blo 499793 751883 := bstep (se 1 (by rfl) ⟨563912, by rfl⟩ : syracuseStep 751883 = 1127825) B1127825
theorem B751895 : Blo 499793 751895 := bstep (se 1 (by rfl) ⟨563921, by rfl⟩ : syracuseStep 751895 = 1127843) B1127843
theorem B751961 : Blo 499793 751961 := bstep (se 2 (by rfl) ⟨281985, by rfl⟩ : syracuseStep 751961 = 563971) B563971
theorem B2750851 : Blo 499793 2750851 := bstep (se 1 (by rfl) ⟨2063138, by rfl⟩ : syracuseStep 2750851 = 4126277) B4126277
theorem B817561 : Blo 499793 817561 := bstep (se 2 (by rfl) ⟨306585, by rfl⟩ : syracuseStep 817561 = 613171) B613171
theorem B752075 : Blo 499793 752075 := bstep (se 1 (by rfl) ⟨564056, by rfl⟩ : syracuseStep 752075 = 1128113) B1128113
theorem B752087 : Blo 499793 752087 := bstep (se 1 (by rfl) ⟨564065, by rfl⟩ : syracuseStep 752087 = 1128131) B1128131
theorem B752153 : Blo 499793 752153 := bstep (se 2 (by rfl) ⟨282057, by rfl⟩ : syracuseStep 752153 = 564115) B564115
theorem B817751 : Blo 499793 817751 := bstep (se 1 (by rfl) ⟨613313, by rfl⟩ : syracuseStep 817751 = 1226627) B1226627
theorem B752267 : Blo 499793 752267 := bstep (se 1 (by rfl) ⟨564200, by rfl⟩ : syracuseStep 752267 = 1128401) B1128401
theorem B752279 : Blo 499793 752279 := bstep (se 1 (by rfl) ⟨564209, by rfl⟩ : syracuseStep 752279 = 1128419) B1128419
theorem B1014487 : Blo 499793 1014487 := bstep (se 1 (by rfl) ⟨760865, by rfl⟩ : syracuseStep 1014487 = 1521731) B1521731
theorem B752345 : Blo 499793 752345 := bstep (se 2 (by rfl) ⟨282129, by rfl⟩ : syracuseStep 752345 = 564259) B564259
theorem B949067 : Blo 499793 949067 := bstep (se 1 (by rfl) ⟨711800, by rfl⟩ : syracuseStep 949067 = 1423601) B1423601
theorem B752459 : Blo 499793 752459 := bstep (se 1 (by rfl) ⟨564344, by rfl⟩ : syracuseStep 752459 = 1128689) B1128689
theorem B752471 : Blo 499793 752471 := bstep (se 1 (by rfl) ⟨564353, by rfl⟩ : syracuseStep 752471 = 1128707) B1128707
theorem B1014617 : Blo 499793 1014617 := bstep (se 2 (by rfl) ⟨380481, by rfl⟩ : syracuseStep 1014617 = 760963) B760963
theorem B1899395 : Blo 499793 1899395 := bstep (se 1 (by rfl) ⟨1424546, by rfl⟩ : syracuseStep 1899395 = 2849093) B2849093
theorem B1899409 : Blo 499793 1899409 := bstep (se 2 (by rfl) ⟨712278, by rfl⟩ : syracuseStep 1899409 = 1424557) B1424557
theorem B752537 : Blo 499793 752537 := bstep (se 2 (by rfl) ⟨282201, by rfl⟩ : syracuseStep 752537 = 564403) B564403
theorem B949249 : Blo 499793 949249 := bstep (se 2 (by rfl) ⟨355968, by rfl⟩ : syracuseStep 949249 = 711937) B711937
theorem B752651 : Blo 499793 752651 := bstep (se 1 (by rfl) ⟨564488, by rfl⟩ : syracuseStep 752651 = 1128977) B1128977
theorem B752663 : Blo 499793 752663 := bstep (se 1 (by rfl) ⟨564497, by rfl⟩ : syracuseStep 752663 = 1128995) B1128995
theorem B752729 : Blo 499793 752729 := bstep (se 2 (by rfl) ⟨282273, by rfl⟩ : syracuseStep 752729 = 564547) B564547
theorem B1899713 : Blo 499793 1899713 := bstep (se 2 (by rfl) ⟨712392, by rfl⟩ : syracuseStep 1899713 = 1424785) B1424785
theorem B752843 : Blo 499793 752843 := bstep (se 1 (by rfl) ⟨564632, by rfl⟩ : syracuseStep 752843 = 1129265) B1129265
theorem B752855 : Blo 499793 752855 := bstep (se 1 (by rfl) ⟨564641, by rfl⟩ : syracuseStep 752855 = 1129283) B1129283
theorem B752921 : Blo 499793 752921 := bstep (se 2 (by rfl) ⟨282345, by rfl⟩ : syracuseStep 752921 = 564691) B564691
theorem B1015105 : Blo 499793 1015105 := bstep (se 2 (by rfl) ⟨380664, by rfl⟩ : syracuseStep 1015105 = 761329) B761329
theorem B753035 : Blo 499793 753035 := bstep (se 1 (by rfl) ⟨564776, by rfl⟩ : syracuseStep 753035 = 1129553) B1129553
theorem B753047 : Blo 499793 753047 := bstep (se 1 (by rfl) ⟨564785, by rfl⟩ : syracuseStep 753047 = 1129571) B1129571
theorem B753113 : Blo 499793 753113 := bstep (se 2 (by rfl) ⟨282417, by rfl⟩ : syracuseStep 753113 = 564835) B564835
theorem B753227 : Blo 499793 753227 := bstep (se 1 (by rfl) ⟨564920, by rfl⟩ : syracuseStep 753227 = 1129841) B1129841
theorem B753239 : Blo 499793 753239 := bstep (se 1 (by rfl) ⟨564929, by rfl⟩ : syracuseStep 753239 = 1129859) B1129859
theorem B753305 : Blo 499793 753305 := bstep (se 2 (by rfl) ⟨282489, by rfl⟩ : syracuseStep 753305 = 564979) B564979
theorem B949963 : Blo 499793 949963 := bstep (se 1 (by rfl) ⟨712472, by rfl⟩ : syracuseStep 949963 = 1424945) B1424945
theorem B753419 : Blo 499793 753419 := bstep (se 1 (by rfl) ⟨565064, by rfl⟩ : syracuseStep 753419 = 1130129) B1130129
theorem B950039 : Blo 499793 950039 := bstep (se 1 (by rfl) ⟨712529, by rfl⟩ : syracuseStep 950039 = 1425059) B1425059
theorem B753431 : Blo 499793 753431 := bstep (se 1 (by rfl) ⟨565073, by rfl⟩ : syracuseStep 753431 = 1130147) B1130147
theorem B753497 : Blo 499793 753497 := bstep (se 2 (by rfl) ⟨282561, by rfl⟩ : syracuseStep 753497 = 565123) B565123
theorem B1900381 : Blo 499793 1900381 := bstep (se 3 (by rfl) ⟨356321, by rfl⟩ : syracuseStep 1900381 = 712643) B712643
theorem B753611 : Blo 499793 753611 := bstep (se 1 (by rfl) ⟨565208, by rfl⟩ : syracuseStep 753611 = 1130417) B1130417
theorem B753623 : Blo 499793 753623 := bstep (se 1 (by rfl) ⟨565217, by rfl⟩ : syracuseStep 753623 = 1130435) B1130435
theorem B753671 : Blo 499793 753671 := bstep (se 1 (by rfl) ⟨565253, by rfl⟩ : syracuseStep 753671 = 1130507) B1130507
theorem B950305 : Blo 499793 950305 := bstep (se 2 (by rfl) ⟨356364, by rfl⟩ : syracuseStep 950305 = 712729) B712729
theorem B753707 : Blo 499793 753707 := bstep (se 1 (by rfl) ⟨565280, by rfl⟩ : syracuseStep 753707 = 1130561) B1130561
theorem B753737 : Blo 499793 753737 := bstep (se 2 (by rfl) ⟨282651, by rfl⟩ : syracuseStep 753737 = 565303) B565303
theorem B2719831 : Blo 499793 2719831 := bstep (se 1 (by rfl) ⟨2039873, by rfl⟩ : syracuseStep 2719831 = 4079747) B4079747
theorem B753851 : Blo 499793 753851 := bstep (se 1 (by rfl) ⟨565388, by rfl⟩ : syracuseStep 753851 = 1130777) B1130777
theorem B753911 : Blo 499793 753911 := bstep (se 1 (by rfl) ⟨565433, by rfl⟩ : syracuseStep 753911 = 1130867) B1130867
theorem B753935 : Blo 499793 753935 := bstep (se 1 (by rfl) ⟨565451, by rfl⟩ : syracuseStep 753935 = 1130903) B1130903
theorem B753977 : Blo 499793 753977 := bstep (se 2 (by rfl) ⟨282741, by rfl⟩ : syracuseStep 753977 = 565483) B565483
theorem B754055 : Blo 499793 754055 := bstep (se 1 (by rfl) ⟨565541, by rfl⟩ : syracuseStep 754055 = 1131083) B1131083
theorem B3801491 : Blo 499793 3801491 := bstep (se 1 (by rfl) ⟨2851118, by rfl⟩ : syracuseStep 3801491 = 5702237) B5702237
theorem B754091 : Blo 499793 754091 := bstep (se 1 (by rfl) ⟨565568, by rfl⟩ : syracuseStep 754091 = 1131137) B1131137
theorem B754121 : Blo 499793 754121 := bstep (se 2 (by rfl) ⟨282795, by rfl⟩ : syracuseStep 754121 = 565591) B565591
theorem B3047939 : Blo 499793 3047939 := bstep (se 1 (by rfl) ⟨2285954, by rfl⟩ : syracuseStep 3047939 = 4571909) B4571909
theorem B1016363 : Blo 499793 1016363 := bstep (se 1 (by rfl) ⟨762272, by rfl⟩ : syracuseStep 1016363 = 1524545) B1524545
theorem B754235 : Blo 499793 754235 := bstep (se 1 (by rfl) ⟨565676, by rfl⟩ : syracuseStep 754235 = 1131353) B1131353
theorem B754295 : Blo 499793 754295 := bstep (se 1 (by rfl) ⟨565721, by rfl⟩ : syracuseStep 754295 = 1131443) B1131443
theorem B754319 : Blo 499793 754319 := bstep (se 1 (by rfl) ⟨565739, by rfl⟩ : syracuseStep 754319 = 1131479) B1131479
theorem B754361 : Blo 499793 754361 := bstep (se 2 (by rfl) ⟨282885, by rfl⟩ : syracuseStep 754361 = 565771) B565771
theorem B754439 : Blo 499793 754439 := bstep (se 1 (by rfl) ⟨565829, by rfl⟩ : syracuseStep 754439 = 1131659) B1131659
theorem B754475 : Blo 499793 754475 := bstep (se 1 (by rfl) ⟨565856, by rfl⟩ : syracuseStep 754475 = 1131713) B1131713
theorem B754505 : Blo 499793 754505 := bstep (se 2 (by rfl) ⟨282939, by rfl⟩ : syracuseStep 754505 = 565879) B565879
theorem B754619 : Blo 499793 754619 := bstep (se 1 (by rfl) ⟨565964, by rfl⟩ : syracuseStep 754619 = 1131929) B1131929
theorem B54887381 : Blo 499793 54887381 := bstep (se 7 (by rfl) ⟨643211, by rfl⟩ : syracuseStep 54887381 = 1286423) B1286423
theorem B754679 : Blo 499793 754679 := bstep (se 1 (by rfl) ⟨566009, by rfl⟩ : syracuseStep 754679 = 1132019) B1132019
theorem B754703 : Blo 499793 754703 := bstep (se 1 (by rfl) ⟨566027, by rfl⟩ : syracuseStep 754703 = 1132055) B1132055
theorem B754745 : Blo 499793 754745 := bstep (se 2 (by rfl) ⟨283029, by rfl⟩ : syracuseStep 754745 = 566059) B566059
theorem B754823 : Blo 499793 754823 := bstep (se 1 (by rfl) ⟨566117, by rfl⟩ : syracuseStep 754823 = 1132235) B1132235
theorem B754859 : Blo 499793 754859 := bstep (se 1 (by rfl) ⟨566144, by rfl⟩ : syracuseStep 754859 = 1132289) B1132289
theorem B951497 : Blo 499793 951497 := bstep (se 2 (by rfl) ⟨356811, by rfl⟩ : syracuseStep 951497 = 713623) B713623
theorem B754889 : Blo 499793 754889 := bstep (se 2 (by rfl) ⟨283083, by rfl⟩ : syracuseStep 754889 = 566167) B566167
theorem B1901825 : Blo 499793 1901825 := bstep (se 2 (by rfl) ⟨713184, by rfl⟩ : syracuseStep 1901825 = 1426369) B1426369
theorem B1901839 : Blo 499793 1901839 := bstep (se 1 (by rfl) ⟨1426379, by rfl⟩ : syracuseStep 1901839 = 2852759) B2852759
theorem B755003 : Blo 499793 755003 := bstep (se 1 (by rfl) ⟨566252, by rfl⟩ : syracuseStep 755003 = 1132505) B1132505
theorem B755063 : Blo 499793 755063 := bstep (se 1 (by rfl) ⟨566297, by rfl⟩ : syracuseStep 755063 = 1132595) B1132595
theorem B755087 : Blo 499793 755087 := bstep (se 1 (by rfl) ⟨566315, by rfl⟩ : syracuseStep 755087 = 1132631) B1132631
theorem B755129 : Blo 499793 755129 := bstep (se 2 (by rfl) ⟨283173, by rfl⟩ : syracuseStep 755129 = 566347) B566347
theorem B755207 : Blo 499793 755207 := bstep (se 1 (by rfl) ⟨566405, by rfl⟩ : syracuseStep 755207 = 1132811) B1132811
theorem B755243 : Blo 499793 755243 := bstep (se 1 (by rfl) ⟨566432, by rfl⟩ : syracuseStep 755243 = 1132865) B1132865
theorem B755273 : Blo 499793 755273 := bstep (se 2 (by rfl) ⟨283227, by rfl⟩ : syracuseStep 755273 = 566455) B566455
theorem B755387 : Blo 499793 755387 := bstep (se 1 (by rfl) ⟨566540, by rfl⟩ : syracuseStep 755387 = 1133081) B1133081
theorem B755447 : Blo 499793 755447 := bstep (se 1 (by rfl) ⟨566585, by rfl⟩ : syracuseStep 755447 = 1133171) B1133171
theorem B755471 : Blo 499793 755471 := bstep (se 1 (by rfl) ⟨566603, by rfl⟩ : syracuseStep 755471 = 1133207) B1133207
theorem B722731 : Blo 499793 722731 := bstep (se 1 (by rfl) ⟨542048, by rfl⟩ : syracuseStep 722731 = 1084097) B1084097
theorem B755513 : Blo 499793 755513 := bstep (se 2 (by rfl) ⟨283317, by rfl⟩ : syracuseStep 755513 = 566635) B566635
theorem B755591 : Blo 499793 755591 := bstep (se 1 (by rfl) ⟨566693, by rfl⟩ : syracuseStep 755591 = 1133387) B1133387
theorem B952211 : Blo 499793 952211 := bstep (se 1 (by rfl) ⟨714158, by rfl⟩ : syracuseStep 952211 = 1428317) B1428317
theorem B755627 : Blo 499793 755627 := bstep (se 1 (by rfl) ⟨566720, by rfl⟩ : syracuseStep 755627 = 1133441) B1133441
theorem B952249 : Blo 499793 952249 := bstep (se 2 (by rfl) ⟨357093, by rfl⟩ : syracuseStep 952249 = 714187) B714187
theorem B722875 : Blo 499793 722875 := bstep (se 1 (by rfl) ⟨542156, by rfl⟩ : syracuseStep 722875 = 1084313) B1084313
theorem B755657 : Blo 499793 755657 := bstep (se 2 (by rfl) ⟨283371, by rfl⟩ : syracuseStep 755657 = 566743) B566743
theorem B5802029 : Blo 499793 5802029 := bstep (se 3 (by rfl) ⟨1087880, by rfl⟩ : syracuseStep 5802029 = 2175761) B2175761
theorem B1443901 : Blo 499793 1443901 := bstep (se 3 (by rfl) ⟨270731, by rfl⟩ : syracuseStep 1443901 = 541463) B541463
theorem B1903115 : Blo 499793 1903115 := bstep (se 1 (by rfl) ⟨1427336, by rfl⟩ : syracuseStep 1903115 = 2854673) B2854673
theorem B3869441 : Blo 499793 3869441 := bstep (se 2 (by rfl) ⟨1451040, by rfl⟩ : syracuseStep 3869441 = 2902081) B2902081
theorem B1018639 : Blo 499793 1018639 := bstep (se 1 (by rfl) ⟨763979, by rfl⟩ : syracuseStep 1018639 = 1527959) B1527959
theorem B3607411 : Blo 499793 3607411 := bstep (se 1 (by rfl) ⟨2705558, by rfl⟩ : syracuseStep 3607411 = 5411117) B5411117
theorem B2853899 : Blo 499793 2853899 := bstep (se 1 (by rfl) ⟨2140424, by rfl⟩ : syracuseStep 2853899 = 4280849) B4280849
theorem B1904057 : Blo 499793 1904057 := bstep (se 2 (by rfl) ⟨714021, by rfl⟩ : syracuseStep 1904057 = 1428043) B1428043
theorem B2887235 : Blo 499793 2887235 := bstep (se 1 (by rfl) ⟨2165426, by rfl⟩ : syracuseStep 2887235 = 4330853) B4330853
theorem B8261297 : Blo 499793 8261297 := bstep (se 2 (by rfl) ⟨3097986, by rfl⟩ : syracuseStep 8261297 = 6195973) B6195973
theorem B6885121 : Blo 499793 6885121 := bstep (se 2 (by rfl) ⟨2581920, by rfl⟩ : syracuseStep 6885121 = 5163841) B5163841
theorem B5410597 : Blo 499793 5410597 := bstep (se 4 (by rfl) ⟨507243, by rfl⟩ : syracuseStep 5410597 = 1014487) B1014487
theorem B954155 : Blo 499793 954155 := bstep (se 1 (by rfl) ⟨715616, by rfl⟩ : syracuseStep 954155 = 1431233) B1431233
theorem B12160813 : Blo 499793 12160813 := bstep (se 3 (by rfl) ⟨2280152, by rfl⟩ : syracuseStep 12160813 = 4560305) B4560305
theorem B1609625 : Blo 499793 1609625 := bstep (se 2 (by rfl) ⟨603609, by rfl⟩ : syracuseStep 1609625 = 1207219) B1207219
theorem B6098989 : Blo 499793 6098989 := bstep (se 3 (by rfl) ⟨1143560, by rfl⟩ : syracuseStep 6098989 = 2287121) B2287121
theorem B59609621 : Blo 499793 59609621 := bstep (se 6 (by rfl) ⟨1397100, by rfl⟩ : syracuseStep 59609621 = 2794201) B2794201
theorem B955081 : Blo 499793 955081 := bstep (se 2 (by rfl) ⟨358155, by rfl⟩ : syracuseStep 955081 = 716311) B716311
theorem B5706611 : Blo 499793 5706611 := bstep (se 1 (by rfl) ⟨4279958, by rfl⟩ : syracuseStep 5706611 = 8559917) B8559917
theorem B562567 : Blo 499793 562567 := bstep (se 1 (by rfl) ⟨421925, by rfl⟩ : syracuseStep 562567 = 843851) B843851
theorem B955795 : Blo 499793 955795 := bstep (se 1 (by rfl) ⟨716846, by rfl⟩ : syracuseStep 955795 = 1433693) B1433693
theorem B1807915 : Blo 499793 1807915 := bstep (se 1 (by rfl) ⟨1355936, by rfl⟩ : syracuseStep 1807915 = 2711873) B2711873
theorem B562747 : Blo 499793 562747 := bstep (se 1 (by rfl) ⟨422060, by rfl⟩ : syracuseStep 562747 = 844121) B844121
theorem B1611535 : Blo 499793 1611535 := bstep (se 1 (by rfl) ⟨1208651, by rfl⟩ : syracuseStep 1611535 = 2417303) B2417303
theorem B1087291 : Blo 499793 1087291 := bstep (se 1 (by rfl) ⟨815468, by rfl⟩ : syracuseStep 1087291 = 1630937) B1630937
theorem B9639749 : Blo 499793 9639749 := bstep (se 4 (by rfl) ⟨903726, by rfl⟩ : syracuseStep 9639749 = 1807453) B1807453
theorem B1906699 : Blo 499793 1906699 := bstep (se 1 (by rfl) ⟨1430024, by rfl⟩ : syracuseStep 1906699 = 2860049) B2860049
theorem B563215 : Blo 499793 563215 := bstep (se 1 (by rfl) ⟨422411, by rfl⟩ : syracuseStep 563215 = 844823) B844823
theorem B2857133 : Blo 499793 2857133 := bstep (se 3 (by rfl) ⟨535712, by rfl⟩ : syracuseStep 2857133 = 1071425) B1071425
theorem B1907003 : Blo 499793 1907003 := bstep (se 1 (by rfl) ⟨1430252, by rfl⟩ : syracuseStep 1907003 = 2860505) B2860505
theorem B563719 : Blo 499793 563719 := bstep (se 1 (by rfl) ⟨422789, by rfl⟩ : syracuseStep 563719 = 845579) B845579
theorem B1808983 : Blo 499793 1808983 := bstep (se 1 (by rfl) ⟨1356737, by rfl⟩ : syracuseStep 1808983 = 2713475) B2713475
theorem B563899 : Blo 499793 563899 := bstep (se 1 (by rfl) ⟨422924, by rfl⟩ : syracuseStep 563899 = 845849) B845849
theorem B1907489 : Blo 499793 1907489 := bstep (se 2 (by rfl) ⟨715308, by rfl⟩ : syracuseStep 1907489 = 1430617) B1430617
theorem B11606819 : Blo 499793 11606819 := bstep (se 1 (by rfl) ⟨8705114, by rfl⟩ : syracuseStep 11606819 = 17410229) B17410229
theorem B1809287 : Blo 499793 1809287 := bstep (se 1 (by rfl) ⟨1356965, by rfl⟩ : syracuseStep 1809287 = 2713931) B2713931
theorem B1809299 : Blo 499793 1809299 := bstep (se 1 (by rfl) ⟨1356974, by rfl⟩ : syracuseStep 1809299 = 2713949) B2713949
theorem B2202553 : Blo 499793 2202553 := bstep (se 2 (by rfl) ⟨825957, by rfl⟩ : syracuseStep 2202553 = 1651915) B1651915
theorem B6200453 : Blo 499793 6200453 := bstep (se 4 (by rfl) ⟨581292, by rfl⟩ : syracuseStep 6200453 = 1162585) B1162585
theorem B564367 : Blo 499793 564367 := bstep (se 1 (by rfl) ⟨423275, by rfl⟩ : syracuseStep 564367 = 846551) B846551
theorem B2858273 : Blo 499793 2858273 := bstep (se 2 (by rfl) ⟨1071852, by rfl⟩ : syracuseStep 2858273 = 2143705) B2143705
theorem B1285511 : Blo 499793 1285511 := bstep (se 1 (by rfl) ⟨964133, by rfl⟩ : syracuseStep 1285511 = 1928267) B1928267
theorem B2530763 : Blo 499793 2530763 := bstep (se 1 (by rfl) ⟨1898072, by rfl⟩ : syracuseStep 2530763 = 3796145) B3796145
theorem B761401 : Blo 499793 761401 := bstep (se 2 (by rfl) ⟨285525, by rfl⟩ : syracuseStep 761401 = 571051) B571051
theorem B4824643 : Blo 499793 4824643 := bstep (se 1 (by rfl) ⟨3618482, by rfl⟩ : syracuseStep 4824643 = 7236965) B7236965
theorem B564871 : Blo 499793 564871 := bstep (se 1 (by rfl) ⟨423653, by rfl⟩ : syracuseStep 564871 = 847307) B847307
theorem B3219173 : Blo 499793 3219173 := bstep (se 4 (by rfl) ⟨301797, by rfl⟩ : syracuseStep 3219173 = 603595) B603595
theorem B1908461 : Blo 499793 1908461 := bstep (se 3 (by rfl) ⟨357836, by rfl⟩ : syracuseStep 1908461 = 715673) B715673
theorem B2531087 : Blo 499793 2531087 := bstep (se 1 (by rfl) ⟨1898315, by rfl⟩ : syracuseStep 2531087 = 3796631) B3796631
theorem B565051 : Blo 499793 565051 := bstep (se 1 (by rfl) ⟨423788, by rfl⟩ : syracuseStep 565051 = 847577) B847577
theorem B499847 : Blo 499793 499847 := bstep (se 1 (by rfl) ⟨374885, by rfl⟩ : syracuseStep 499847 = 749771) B749771
theorem B499855 : Blo 499793 499855 := bstep (se 1 (by rfl) ⟨374891, by rfl⟩ : syracuseStep 499855 = 749783) B749783
theorem B499899 : Blo 499793 499899 := bstep (se 1 (by rfl) ⟨374924, by rfl⟩ : syracuseStep 499899 = 749849) B749849
theorem B499975 : Blo 499793 499975 := bstep (se 1 (by rfl) ⟨374981, by rfl⟩ : syracuseStep 499975 = 749963) B749963
theorem B499983 : Blo 499793 499983 := bstep (se 1 (by rfl) ⟨374987, by rfl⟩ : syracuseStep 499983 = 749975) B749975
theorem B565519 : Blo 499793 565519 := bstep (se 1 (by rfl) ⟨424139, by rfl⟩ : syracuseStep 565519 = 848279) B848279
theorem B500027 : Blo 499793 500027 := bstep (se 1 (by rfl) ⟨375020, by rfl⟩ : syracuseStep 500027 = 750041) B750041
theorem B1483127 : Blo 499793 1483127 := bstep (se 1 (by rfl) ⟨1112345, by rfl⟩ : syracuseStep 1483127 = 2224691) B2224691
theorem B500103 : Blo 499793 500103 := bstep (se 1 (by rfl) ⟨375077, by rfl⟩ : syracuseStep 500103 = 750155) B750155
theorem B500111 : Blo 499793 500111 := bstep (se 1 (by rfl) ⟨375083, by rfl⟩ : syracuseStep 500111 = 750167) B750167
theorem B500155 : Blo 499793 500155 := bstep (se 1 (by rfl) ⟨375116, by rfl⟩ : syracuseStep 500155 = 750233) B750233
theorem B500231 : Blo 499793 500231 := bstep (se 1 (by rfl) ⟨375173, by rfl⟩ : syracuseStep 500231 = 750347) B750347
theorem B500239 : Blo 499793 500239 := bstep (se 1 (by rfl) ⟨375179, by rfl⟩ : syracuseStep 500239 = 750359) B750359
theorem B1810973 : Blo 499793 1810973 := bstep (se 3 (by rfl) ⟨339557, by rfl⟩ : syracuseStep 1810973 = 679115) B679115
theorem B1090081 : Blo 499793 1090081 := bstep (se 2 (by rfl) ⟨408780, by rfl⟩ : syracuseStep 1090081 = 817561) B817561
theorem B500283 : Blo 499793 500283 := bstep (se 1 (by rfl) ⟨375212, by rfl⟩ : syracuseStep 500283 = 750425) B750425
theorem B500359 : Blo 499793 500359 := bstep (se 1 (by rfl) ⟨375269, by rfl⟩ : syracuseStep 500359 = 750539) B750539
theorem B500367 : Blo 499793 500367 := bstep (se 1 (by rfl) ⟨375275, by rfl⟩ : syracuseStep 500367 = 750551) B750551
theorem B1450649 : Blo 499793 1450649 := bstep (se 2 (by rfl) ⟨543993, by rfl⟩ : syracuseStep 1450649 = 1087987) B1087987
theorem B500411 : Blo 499793 500411 := bstep (se 1 (by rfl) ⟨375308, by rfl⟩ : syracuseStep 500411 = 750617) B750617
theorem B860873 : Blo 499793 860873 := bstep (se 2 (by rfl) ⟨322827, by rfl⟩ : syracuseStep 860873 = 645655) B645655
theorem B500487 : Blo 499793 500487 := bstep (se 1 (by rfl) ⟨375365, by rfl⟩ : syracuseStep 500487 = 750731) B750731
theorem B566023 : Blo 499793 566023 := bstep (se 1 (by rfl) ⟨424517, by rfl⟩ : syracuseStep 566023 = 849035) B849035
theorem B500495 : Blo 499793 500495 := bstep (se 1 (by rfl) ⟨375371, by rfl⟩ : syracuseStep 500495 = 750743) B750743
theorem B500539 : Blo 499793 500539 := bstep (se 1 (by rfl) ⟨375404, by rfl⟩ : syracuseStep 500539 = 750809) B750809
theorem B500615 : Blo 499793 500615 := bstep (se 1 (by rfl) ⟨375461, by rfl⟩ : syracuseStep 500615 = 750923) B750923
theorem B500623 : Blo 499793 500623 := bstep (se 1 (by rfl) ⟨375467, by rfl⟩ : syracuseStep 500623 = 750935) B750935
theorem B500667 : Blo 499793 500667 := bstep (se 1 (by rfl) ⟨375500, by rfl⟩ : syracuseStep 500667 = 751001) B751001
theorem B566203 : Blo 499793 566203 := bstep (se 1 (by rfl) ⟨424652, by rfl⟩ : syracuseStep 566203 = 849305) B849305
theorem B500743 : Blo 499793 500743 := bstep (se 1 (by rfl) ⟨375557, by rfl⟩ : syracuseStep 500743 = 751115) B751115
theorem B500751 : Blo 499793 500751 := bstep (se 1 (by rfl) ⟨375563, by rfl⟩ : syracuseStep 500751 = 751127) B751127
theorem B500795 : Blo 499793 500795 := bstep (se 1 (by rfl) ⟨375596, by rfl⟩ : syracuseStep 500795 = 751193) B751193
theorem B6431831 : Blo 499793 6431831 := bstep (se 1 (by rfl) ⟨4823873, by rfl⟩ : syracuseStep 6431831 = 9647747) B9647747
theorem B500871 : Blo 499793 500871 := bstep (se 1 (by rfl) ⟨375653, by rfl⟩ : syracuseStep 500871 = 751307) B751307
theorem B500879 : Blo 499793 500879 := bstep (se 1 (by rfl) ⟨375659, by rfl⟩ : syracuseStep 500879 = 751319) B751319
theorem B500923 : Blo 499793 500923 := bstep (se 1 (by rfl) ⟨375692, by rfl⟩ : syracuseStep 500923 = 751385) B751385
theorem B2532545 : Blo 499793 2532545 := bstep (se 2 (by rfl) ⟨949704, by rfl⟩ : syracuseStep 2532545 = 1899409) B1899409
theorem B500999 : Blo 499793 500999 := bstep (se 1 (by rfl) ⟨375749, by rfl⟩ : syracuseStep 500999 = 751499) B751499
theorem B501007 : Blo 499793 501007 := bstep (se 1 (by rfl) ⟨375755, by rfl⟩ : syracuseStep 501007 = 751511) B751511
theorem B1353019 : Blo 499793 1353019 := bstep (se 1 (by rfl) ⟨1014764, by rfl⟩ : syracuseStep 1353019 = 2029529) B2029529
theorem B501051 : Blo 499793 501051 := bstep (se 1 (by rfl) ⟨375788, by rfl⟩ : syracuseStep 501051 = 751577) B751577
theorem B501127 : Blo 499793 501127 := bstep (se 1 (by rfl) ⟨375845, by rfl⟩ : syracuseStep 501127 = 751691) B751691
theorem B501135 : Blo 499793 501135 := bstep (se 1 (by rfl) ⟨375851, by rfl⟩ : syracuseStep 501135 = 751703) B751703
theorem B566671 : Blo 499793 566671 := bstep (se 1 (by rfl) ⟨425003, by rfl⟩ : syracuseStep 566671 = 850007) B850007
theorem B501179 : Blo 499793 501179 := bstep (se 1 (by rfl) ⟨375884, by rfl⟩ : syracuseStep 501179 = 751769) B751769
theorem B501255 : Blo 499793 501255 := bstep (se 1 (by rfl) ⟨375941, by rfl⟩ : syracuseStep 501255 = 751883) B751883
theorem B501263 : Blo 499793 501263 := bstep (se 1 (by rfl) ⟨375947, by rfl⟩ : syracuseStep 501263 = 751895) B751895
theorem B501307 : Blo 499793 501307 := bstep (se 1 (by rfl) ⟨375980, by rfl⟩ : syracuseStep 501307 = 751961) B751961
theorem B501383 : Blo 499793 501383 := bstep (se 1 (by rfl) ⟨376037, by rfl⟩ : syracuseStep 501383 = 752075) B752075
theorem B501391 : Blo 499793 501391 := bstep (se 1 (by rfl) ⟨376043, by rfl⟩ : syracuseStep 501391 = 752087) B752087
theorem B501435 : Blo 499793 501435 := bstep (se 1 (by rfl) ⟨376076, by rfl⟩ : syracuseStep 501435 = 752153) B752153
theorem B1812169 : Blo 499793 1812169 := bstep (se 2 (by rfl) ⟨679563, by rfl⟩ : syracuseStep 1812169 = 1359127) B1359127
theorem B1353473 : Blo 499793 1353473 := bstep (se 2 (by rfl) ⟨507552, by rfl⟩ : syracuseStep 1353473 = 1015105) B1015105
theorem B501511 : Blo 499793 501511 := bstep (se 1 (by rfl) ⟨376133, by rfl⟩ : syracuseStep 501511 = 752267) B752267
theorem B501519 : Blo 499793 501519 := bstep (se 1 (by rfl) ⟨376139, by rfl⟩ : syracuseStep 501519 = 752279) B752279
theorem B10889005 : Blo 499793 10889005 := bstep (se 3 (by rfl) ⟨2041688, by rfl⟩ : syracuseStep 10889005 = 4083377) B4083377
theorem B501563 : Blo 499793 501563 := bstep (se 1 (by rfl) ⟨376172, by rfl⟩ : syracuseStep 501563 = 752345) B752345
theorem B1910587 : Blo 499793 1910587 := bstep (se 1 (by rfl) ⟨1432940, by rfl⟩ : syracuseStep 1910587 = 2865881) B2865881
theorem B927607 : Blo 499793 927607 := bstep (se 1 (by rfl) ⟨695705, by rfl⟩ : syracuseStep 927607 = 1391411) B1391411
theorem B632711 : Blo 499793 632711 := bstep (se 1 (by rfl) ⟨474533, by rfl⟩ : syracuseStep 632711 = 949067) B949067
theorem B501639 : Blo 499793 501639 := bstep (se 1 (by rfl) ⟨376229, by rfl⟩ : syracuseStep 501639 = 752459) B752459
theorem B501647 : Blo 499793 501647 := bstep (se 1 (by rfl) ⟨376235, by rfl⟩ : syracuseStep 501647 = 752471) B752471
theorem B501691 : Blo 499793 501691 := bstep (se 1 (by rfl) ⟨376268, by rfl⟩ : syracuseStep 501691 = 752537) B752537
theorem B501767 : Blo 499793 501767 := bstep (se 1 (by rfl) ⟨376325, by rfl⟩ : syracuseStep 501767 = 752651) B752651
theorem B501775 : Blo 499793 501775 := bstep (se 1 (by rfl) ⟨376331, by rfl⟩ : syracuseStep 501775 = 752663) B752663
theorem B501819 : Blo 499793 501819 := bstep (se 1 (by rfl) ⟨376364, by rfl⟩ : syracuseStep 501819 = 752729) B752729
theorem B501895 : Blo 499793 501895 := bstep (se 1 (by rfl) ⟨376421, by rfl⟩ : syracuseStep 501895 = 752843) B752843
theorem B501903 : Blo 499793 501903 := bstep (se 1 (by rfl) ⟨376427, by rfl⟩ : syracuseStep 501903 = 752855) B752855
theorem B501947 : Blo 499793 501947 := bstep (se 1 (by rfl) ⟨376460, by rfl⟩ : syracuseStep 501947 = 752921) B752921
theorem B502023 : Blo 499793 502023 := bstep (se 1 (by rfl) ⟨376517, by rfl⟩ : syracuseStep 502023 = 753035) B753035
theorem B534799 : Blo 499793 534799 := bstep (se 1 (by rfl) ⟨401099, by rfl⟩ : syracuseStep 534799 = 802199) B802199
theorem B502031 : Blo 499793 502031 := bstep (se 1 (by rfl) ⟨376523, by rfl⟩ : syracuseStep 502031 = 753047) B753047
theorem B1911073 : Blo 499793 1911073 := bstep (se 2 (by rfl) ⟨716652, by rfl⟩ : syracuseStep 1911073 = 1433305) B1433305
theorem B502075 : Blo 499793 502075 := bstep (se 1 (by rfl) ⟨376556, by rfl⟩ : syracuseStep 502075 = 753113) B753113
theorem B502151 : Blo 499793 502151 := bstep (se 1 (by rfl) ⟨376613, by rfl⟩ : syracuseStep 502151 = 753227) B753227
theorem B502159 : Blo 499793 502159 := bstep (se 1 (by rfl) ⟨376619, by rfl⟩ : syracuseStep 502159 = 753239) B753239
theorem B502203 : Blo 499793 502203 := bstep (se 1 (by rfl) ⟨376652, by rfl⟩ : syracuseStep 502203 = 753305) B753305
theorem B2533841 : Blo 499793 2533841 := bstep (se 2 (by rfl) ⟨950190, by rfl⟩ : syracuseStep 2533841 = 1900381) B1900381
theorem B502279 : Blo 499793 502279 := bstep (se 1 (by rfl) ⟨376709, by rfl⟩ : syracuseStep 502279 = 753419) B753419
theorem B633359 : Blo 499793 633359 := bstep (se 1 (by rfl) ⟨475019, by rfl⟩ : syracuseStep 633359 = 950039) B950039
theorem B502287 : Blo 499793 502287 := bstep (se 1 (by rfl) ⟨376715, by rfl⟩ : syracuseStep 502287 = 753431) B753431
theorem B502331 : Blo 499793 502331 := bstep (se 1 (by rfl) ⟨376748, by rfl⟩ : syracuseStep 502331 = 753497) B753497
theorem B1321559 : Blo 499793 1321559 := bstep (se 1 (by rfl) ⟨991169, by rfl⟩ : syracuseStep 1321559 = 1982339) B1982339
theorem B1124999 : Blo 499793 1124999 := bstep (se 1 (by rfl) ⟨843749, by rfl⟩ : syracuseStep 1124999 = 1687499) B1687499
theorem B502407 : Blo 499793 502407 := bstep (se 1 (by rfl) ⟨376805, by rfl⟩ : syracuseStep 502407 = 753611) B753611
theorem B502415 : Blo 499793 502415 := bstep (se 1 (by rfl) ⟨376811, by rfl⟩ : syracuseStep 502415 = 753623) B753623
theorem B502459 : Blo 499793 502459 := bstep (se 1 (by rfl) ⟨376844, by rfl⟩ : syracuseStep 502459 = 753689) B753689
theorem B502535 : Blo 499793 502535 := bstep (se 1 (by rfl) ⟨376901, by rfl⟩ : syracuseStep 502535 = 753803) B753803
theorem B502543 : Blo 499793 502543 := bstep (se 1 (by rfl) ⟨376907, by rfl⟩ : syracuseStep 502543 = 753815) B753815
theorem B1125179 : Blo 499793 1125179 := bstep (se 1 (by rfl) ⟨843884, by rfl⟩ : syracuseStep 1125179 = 1687769) B1687769
theorem B502587 : Blo 499793 502587 := bstep (se 1 (by rfl) ⟨376940, by rfl⟩ : syracuseStep 502587 = 753881) B753881
theorem B502663 : Blo 499793 502663 := bstep (se 1 (by rfl) ⟨376997, by rfl⟩ : syracuseStep 502663 = 753995) B753995
theorem B502671 : Blo 499793 502671 := bstep (se 1 (by rfl) ⟨377003, by rfl⟩ : syracuseStep 502671 = 754007) B754007
theorem B1125305 : Blo 499793 1125305 := bstep (se 2 (by rfl) ⟨421989, by rfl⟩ : syracuseStep 1125305 = 843979) B843979
theorem B502715 : Blo 499793 502715 := bstep (se 1 (by rfl) ⟨377036, by rfl⟩ : syracuseStep 502715 = 754073) B754073
theorem B502791 : Blo 499793 502791 := bstep (se 1 (by rfl) ⟨377093, by rfl⟩ : syracuseStep 502791 = 754187) B754187
theorem B502799 : Blo 499793 502799 := bstep (se 1 (by rfl) ⟨377099, by rfl⟩ : syracuseStep 502799 = 754199) B754199
theorem B2436119 : Blo 499793 2436119 := bstep (se 1 (by rfl) ⟨1827089, by rfl⟩ : syracuseStep 2436119 = 3654179) B3654179
theorem B502843 : Blo 499793 502843 := bstep (se 1 (by rfl) ⟨377132, by rfl⟩ : syracuseStep 502843 = 754265) B754265
theorem B502919 : Blo 499793 502919 := bstep (se 1 (by rfl) ⟨377189, by rfl⟩ : syracuseStep 502919 = 754379) B754379
theorem B502927 : Blo 499793 502927 := bstep (se 1 (by rfl) ⟨377195, by rfl⟩ : syracuseStep 502927 = 754391) B754391
theorem B502971 : Blo 499793 502971 := bstep (se 1 (by rfl) ⟨377228, by rfl⟩ : syracuseStep 502971 = 754457) B754457
theorem B1912045 : Blo 499793 1912045 := bstep (se 3 (by rfl) ⟨358508, by rfl⟩ : syracuseStep 1912045 = 717017) B717017
theorem B503047 : Blo 499793 503047 := bstep (se 1 (by rfl) ⟨377285, by rfl⟩ : syracuseStep 503047 = 754571) B754571
theorem B1125647 : Blo 499793 1125647 := bstep (se 1 (by rfl) ⟨844235, by rfl⟩ : syracuseStep 1125647 = 1688471) B1688471
theorem B503055 : Blo 499793 503055 := bstep (se 1 (by rfl) ⟨377291, by rfl⟩ : syracuseStep 503055 = 754583) B754583
theorem B1125665 : Blo 499793 1125665 := bstep (se 2 (by rfl) ⟨422124, by rfl⟩ : syracuseStep 1125665 = 844249) B844249
theorem B503099 : Blo 499793 503099 := bstep (se 1 (by rfl) ⟨377324, by rfl⟩ : syracuseStep 503099 = 754649) B754649
theorem B1453373 : Blo 499793 1453373 := bstep (se 3 (by rfl) ⟨272507, by rfl⟩ : syracuseStep 1453373 = 545015) B545015
theorem B503175 : Blo 499793 503175 := bstep (se 1 (by rfl) ⟨377381, by rfl⟩ : syracuseStep 503175 = 754763) B754763
theorem B503183 : Blo 499793 503183 := bstep (se 1 (by rfl) ⟨377387, by rfl⟩ : syracuseStep 503183 = 754775) B754775
theorem B503227 : Blo 499793 503227 := bstep (se 1 (by rfl) ⟨377420, by rfl⟩ : syracuseStep 503227 = 754841) B754841
theorem B503303 : Blo 499793 503303 := bstep (se 1 (by rfl) ⟨377477, by rfl⟩ : syracuseStep 503303 = 754955) B754955
theorem B503311 : Blo 499793 503311 := bstep (se 1 (by rfl) ⟨377483, by rfl⟩ : syracuseStep 503311 = 754967) B754967
theorem B1912349 : Blo 499793 1912349 := bstep (se 3 (by rfl) ⟨358565, by rfl⟩ : syracuseStep 1912349 = 717131) B717131
theorem B503355 : Blo 499793 503355 := bstep (se 1 (by rfl) ⟨377516, by rfl⟩ : syracuseStep 503355 = 755033) B755033
theorem B1126007 : Blo 499793 1126007 := bstep (se 1 (by rfl) ⟨844505, by rfl⟩ : syracuseStep 1126007 = 1689011) B1689011
theorem B503431 : Blo 499793 503431 := bstep (se 1 (by rfl) ⟨377573, by rfl⟩ : syracuseStep 503431 = 755147) B755147
theorem B503439 : Blo 499793 503439 := bstep (se 1 (by rfl) ⟨377579, by rfl⟩ : syracuseStep 503439 = 755159) B755159
theorem B1060499 : Blo 499793 1060499 := bstep (se 1 (by rfl) ⟨795374, by rfl⟩ : syracuseStep 1060499 = 1590749) B1590749
theorem B503483 : Blo 499793 503483 := bstep (se 1 (by rfl) ⟨377612, by rfl⟩ : syracuseStep 503483 = 755225) B755225
theorem B503559 : Blo 499793 503559 := bstep (se 1 (by rfl) ⟨377669, by rfl⟩ : syracuseStep 503559 = 755339) B755339
theorem B503567 : Blo 499793 503567 := bstep (se 1 (by rfl) ⟨377675, by rfl⟩ : syracuseStep 503567 = 755351) B755351
theorem B1126187 : Blo 499793 1126187 := bstep (se 1 (by rfl) ⟨844640, by rfl⟩ : syracuseStep 1126187 = 1689281) B1689281
theorem B503611 : Blo 499793 503611 := bstep (se 1 (by rfl) ⟨377708, by rfl⟩ : syracuseStep 503611 = 755417) B755417
theorem B503687 : Blo 499793 503687 := bstep (se 1 (by rfl) ⟨377765, by rfl⟩ : syracuseStep 503687 = 755531) B755531
theorem B503695 : Blo 499793 503695 := bstep (se 1 (by rfl) ⟨377771, by rfl⟩ : syracuseStep 503695 = 755543) B755543
theorem B503739 : Blo 499793 503739 := bstep (se 1 (by rfl) ⟨377804, by rfl⟩ : syracuseStep 503739 = 755609) B755609
theorem B2863147 : Blo 499793 2863147 := bstep (se 1 (by rfl) ⟨2147360, by rfl⟩ : syracuseStep 2863147 = 4294721) B4294721
theorem B1126547 : Blo 499793 1126547 := bstep (se 1 (by rfl) ⟨844910, by rfl⟩ : syracuseStep 1126547 = 1689821) B1689821
theorem B1126601 : Blo 499793 1126601 := bstep (se 2 (by rfl) ⟨422475, by rfl⟩ : syracuseStep 1126601 = 844951) B844951
theorem B1356047 : Blo 499793 1356047 := bstep (se 1 (by rfl) ⟨1017035, by rfl⟩ : syracuseStep 1356047 = 2034071) B2034071
theorem B1519931 : Blo 499793 1519931 := bstep (se 1 (by rfl) ⟨1139948, by rfl⟩ : syracuseStep 1519931 = 2279897) B2279897
theorem B2535947 : Blo 499793 2535947 := bstep (se 1 (by rfl) ⟨1901960, by rfl⟩ : syracuseStep 2535947 = 3803921) B3803921
theorem B2536109 : Blo 499793 2536109 := bstep (se 3 (by rfl) ⟨475520, by rfl⟩ : syracuseStep 2536109 = 951041) B951041
theorem B6435521 : Blo 499793 6435521 := bstep (se 2 (by rfl) ⟨2413320, by rfl⟩ : syracuseStep 6435521 = 4826641) B4826641
theorem B4567823 : Blo 499793 4567823 := bstep (se 1 (by rfl) ⟨3425867, by rfl⟩ : syracuseStep 4567823 = 6851735) B6851735
theorem B2405153 : Blo 499793 2405153 := bstep (se 2 (by rfl) ⟨901932, by rfl⟩ : syracuseStep 2405153 = 1803865) B1803865
theorem B4829989 : Blo 499793 4829989 := bstep (se 4 (by rfl) ⟨452811, by rfl⟩ : syracuseStep 4829989 = 905623) B905623
theorem B1127303 : Blo 499793 1127303 := bstep (se 1 (by rfl) ⟨845477, by rfl⟩ : syracuseStep 1127303 = 1690955) B1690955
theorem B1815443 : Blo 499793 1815443 := bstep (se 1 (by rfl) ⟨1361582, by rfl⟩ : syracuseStep 1815443 = 2723165) B2723165
theorem B1127483 : Blo 499793 1127483 := bstep (se 1 (by rfl) ⟨845612, by rfl⟩ : syracuseStep 1127483 = 1691225) B1691225
theorem B1127609 : Blo 499793 1127609 := bstep (se 2 (by rfl) ⟨422853, by rfl⟩ : syracuseStep 1127609 = 845707) B845707
theorem B4634003 : Blo 499793 4634003 := bstep (se 1 (by rfl) ⟨3475502, by rfl⟩ : syracuseStep 4634003 = 6951005) B6951005
theorem B636331 : Blo 499793 636331 := bstep (se 1 (by rfl) ⟨477248, by rfl⟩ : syracuseStep 636331 = 954497) B954497
theorem B3225041 : Blo 499793 3225041 := bstep (se 2 (by rfl) ⟨1209390, by rfl⟩ : syracuseStep 3225041 = 2418781) B2418781
theorem B2864605 : Blo 499793 2864605 := bstep (se 3 (by rfl) ⟨537113, by rfl⟩ : syracuseStep 2864605 = 1074227) B1074227
theorem B1127951 : Blo 499793 1127951 := bstep (se 1 (by rfl) ⟨845963, by rfl⟩ : syracuseStep 1127951 = 1691927) B1691927
theorem B1127969 : Blo 499793 1127969 := bstep (se 2 (by rfl) ⟨422988, by rfl⟩ : syracuseStep 1127969 = 845977) B845977
theorem B20592305 : Blo 499793 20592305 := bstep (se 2 (by rfl) ⟨7722114, by rfl⟩ : syracuseStep 20592305 = 15444229) B15444229
theorem B1128311 : Blo 499793 1128311 := bstep (se 1 (by rfl) ⟨846233, by rfl⟩ : syracuseStep 1128311 = 1692467) B1692467
theorem B800647 : Blo 499793 800647 := bstep (se 1 (by rfl) ⟨600485, by rfl⟩ : syracuseStep 800647 = 1200971) B1200971
theorem B1128491 : Blo 499793 1128491 := bstep (se 1 (by rfl) ⟨846368, by rfl⟩ : syracuseStep 1128491 = 1692737) B1692737
theorem B2537729 : Blo 499793 2537729 := bstep (se 2 (by rfl) ⟨951648, by rfl⟩ : syracuseStep 2537729 = 1903297) B1903297
theorem B4274491 : Blo 499793 4274491 := bstep (se 1 (by rfl) ⟨3205868, by rfl⟩ : syracuseStep 4274491 = 6411737) B6411737
theorem B2144627 : Blo 499793 2144627 := bstep (se 1 (by rfl) ⟨1608470, by rfl⟩ : syracuseStep 2144627 = 3216941) B3216941
theorem B637303 : Blo 499793 637303 := bstep (se 1 (by rfl) ⟨477977, by rfl⟩ : syracuseStep 637303 = 955955) B955955
theorem B1128851 : Blo 499793 1128851 := bstep (se 1 (by rfl) ⟨846638, by rfl⟩ : syracuseStep 1128851 = 1693277) B1693277
theorem B1128905 : Blo 499793 1128905 := bstep (se 2 (by rfl) ⟨423339, by rfl⟩ : syracuseStep 1128905 = 846679) B846679
theorem B4274765 : Blo 499793 4274765 := bstep (se 3 (by rfl) ⟨801518, by rfl⟩ : syracuseStep 4274765 = 1603037) B1603037
theorem B2177945 : Blo 499793 2177945 := bstep (se 2 (by rfl) ⟨816729, by rfl⟩ : syracuseStep 2177945 = 1633459) B1633459
theorem B82394117 : Blo 499793 82394117 := bstep (se 4 (by rfl) ⟨7724448, by rfl⟩ : syracuseStep 82394117 = 15448897) B15448897
theorem B2538539 : Blo 499793 2538539 := bstep (se 1 (by rfl) ⟨1903904, by rfl⟩ : syracuseStep 2538539 = 3807809) B3807809
theorem B1129607 : Blo 499793 1129607 := bstep (se 1 (by rfl) ⟨847205, by rfl⟩ : syracuseStep 1129607 = 1694411) B1694411
theorem B1359137 : Blo 499793 1359137 := bstep (se 2 (by rfl) ⟨509676, by rfl⟩ : syracuseStep 1359137 = 1019353) B1019353
theorem B1129787 : Blo 499793 1129787 := bstep (se 1 (by rfl) ⟨847340, by rfl⟩ : syracuseStep 1129787 = 1694681) B1694681
theorem B1129913 : Blo 499793 1129913 := bstep (se 2 (by rfl) ⟨423717, by rfl⟩ : syracuseStep 1129913 = 847435) B847435
theorem B11124173 : Blo 499793 11124173 := bstep (se 3 (by rfl) ⟨2085782, by rfl⟩ : syracuseStep 11124173 = 4171565) B4171565
theorem B1424911 : Blo 499793 1424911 := bstep (se 1 (by rfl) ⟨1068683, by rfl⟩ : syracuseStep 1424911 = 2137367) B2137367
theorem B1130255 : Blo 499793 1130255 := bstep (se 1 (by rfl) ⟨847691, by rfl⟩ : syracuseStep 1130255 = 1695383) B1695383
theorem B1425185 : Blo 499793 1425185 := bstep (se 2 (by rfl) ⟨534444, by rfl⟩ : syracuseStep 1425185 = 1068889) B1068889
theorem B1130273 : Blo 499793 1130273 := bstep (se 2 (by rfl) ⟨423852, by rfl⟩ : syracuseStep 1130273 = 847705) B847705
theorem B1130615 : Blo 499793 1130615 := bstep (se 1 (by rfl) ⟨847961, by rfl⟩ : syracuseStep 1130615 = 1695923) B1695923
theorem B1687823 : Blo 499793 1687823 := bstep (se 1 (by rfl) ⟨1265867, by rfl⟩ : syracuseStep 1687823 = 2531735) B2531735
theorem B1130795 : Blo 499793 1130795 := bstep (se 1 (by rfl) ⟨848096, by rfl⟩ : syracuseStep 1130795 = 1696193) B1696193
theorem B2539835 : Blo 499793 2539835 := bstep (se 1 (by rfl) ⟨1904876, by rfl⟩ : syracuseStep 2539835 = 3809753) B3809753
theorem B2539997 : Blo 499793 2539997 := bstep (se 3 (by rfl) ⟨476249, by rfl⟩ : syracuseStep 2539997 = 952499) B952499
theorem B1688093 : Blo 499793 1688093 := bstep (se 3 (by rfl) ⟨316517, by rfl⟩ : syracuseStep 1688093 = 633035) B633035
theorem B1131155 : Blo 499793 1131155 := bstep (se 1 (by rfl) ⟨848366, by rfl⟩ : syracuseStep 1131155 = 1696733) B1696733
theorem B508603 : Blo 499793 508603 := bstep (se 1 (by rfl) ⟨381452, by rfl⟩ : syracuseStep 508603 = 762905) B762905
theorem B9126593 : Blo 499793 9126593 := bstep (se 2 (by rfl) ⟨3422472, by rfl⟩ : syracuseStep 9126593 = 6844945) B6844945
theorem B1131209 : Blo 499793 1131209 := bstep (se 2 (by rfl) ⟨424203, by rfl⟩ : syracuseStep 1131209 = 848407) B848407
theorem B1426187 : Blo 499793 1426187 := bstep (se 1 (by rfl) ⟨1069640, by rfl⟩ : syracuseStep 1426187 = 2139281) B2139281
theorem B2147087 : Blo 499793 2147087 := bstep (se 1 (by rfl) ⟨1610315, by rfl⟩ : syracuseStep 2147087 = 3220631) B3220631
theorem B2540321 : Blo 499793 2540321 := bstep (se 2 (by rfl) ⟨952620, by rfl⟩ : syracuseStep 2540321 = 1905241) B1905241
theorem B1426585 : Blo 499793 1426585 := bstep (se 2 (by rfl) ⟨534969, by rfl⟩ : syracuseStep 1426585 = 1069939) B1069939
theorem B2409709 : Blo 499793 2409709 := bstep (se 3 (by rfl) ⟨451820, by rfl⟩ : syracuseStep 2409709 = 903641) B903641
theorem B3097871 : Blo 499793 3097871 := bstep (se 1 (by rfl) ⟨2323403, by rfl⟩ : syracuseStep 3097871 = 4646807) B4646807
theorem B1131911 : Blo 499793 1131911 := bstep (se 1 (by rfl) ⟨848933, by rfl⟩ : syracuseStep 1131911 = 1697867) B1697867
theorem B1426835 : Blo 499793 1426835 := bstep (se 1 (by rfl) ⟨1070126, by rfl⟩ : syracuseStep 1426835 = 2140253) B2140253
theorem B8144387 : Blo 499793 8144387 := bstep (se 1 (by rfl) ⟨6108290, by rfl⟩ : syracuseStep 8144387 = 12216581) B12216581
theorem B1132091 : Blo 499793 1132091 := bstep (se 1 (by rfl) ⟨849068, by rfl⟩ : syracuseStep 1132091 = 1698137) B1698137
theorem B2868797 : Blo 499793 2868797 := bstep (se 3 (by rfl) ⟨537899, by rfl⟩ : syracuseStep 2868797 = 1075799) B1075799
theorem B1132217 : Blo 499793 1132217 := bstep (se 2 (by rfl) ⟨424581, by rfl⟩ : syracuseStep 1132217 = 849163) B849163
theorem B2541293 : Blo 499793 2541293 := bstep (se 3 (by rfl) ⟨476492, by rfl⟩ : syracuseStep 2541293 = 952985) B952985
theorem B6080305 : Blo 499793 6080305 := bstep (se 2 (by rfl) ⟨2280114, by rfl⟩ : syracuseStep 6080305 = 4560229) B4560229
theorem B1689497 : Blo 499793 1689497 := bstep (se 2 (by rfl) ⟨633561, by rfl⟩ : syracuseStep 1689497 = 1267123) B1267123
theorem B1132559 : Blo 499793 1132559 := bstep (se 1 (by rfl) ⟨849419, by rfl⟩ : syracuseStep 1132559 = 1698839) B1698839
theorem B1132577 : Blo 499793 1132577 := bstep (se 2 (by rfl) ⟨424716, by rfl⟩ : syracuseStep 1132577 = 849433) B849433
theorem B3360941 : Blo 499793 3360941 := bstep (se 3 (by rfl) ⟨630176, by rfl⟩ : syracuseStep 3360941 = 1260353) B1260353
theorem B1427827 : Blo 499793 1427827 := bstep (se 1 (by rfl) ⟨1070870, by rfl⟩ : syracuseStep 1427827 = 2141741) B2141741
theorem B1132919 : Blo 499793 1132919 := bstep (se 1 (by rfl) ⟨849689, by rfl⟩ : syracuseStep 1132919 = 1699379) B1699379
theorem B2542103 : Blo 499793 2542103 := bstep (se 1 (by rfl) ⟨1906577, by rfl⟩ : syracuseStep 2542103 = 3813155) B3813155
theorem B1133099 : Blo 499793 1133099 := bstep (se 1 (by rfl) ⟨849824, by rfl⟩ : syracuseStep 1133099 = 1699649) B1699649
theorem B1690199 : Blo 499793 1690199 := bstep (se 1 (by rfl) ⟨1267649, by rfl⟩ : syracuseStep 1690199 = 2535299) B2535299
theorem B805511 : Blo 499793 805511 := bstep (se 1 (by rfl) ⟨604133, by rfl⟩ : syracuseStep 805511 = 1208267) B1208267
theorem B1133459 : Blo 499793 1133459 := bstep (se 1 (by rfl) ⟨850094, by rfl⟩ : syracuseStep 1133459 = 1700189) B1700189
theorem B1133513 : Blo 499793 1133513 := bstep (se 2 (by rfl) ⟨425067, by rfl⟩ : syracuseStep 1133513 = 850135) B850135
theorem B6409277 : Blo 499793 6409277 := bstep (se 3 (by rfl) ⟨1201739, by rfl⟩ : syracuseStep 6409277 = 2403479) B2403479
theorem B1690685 : Blo 499793 1690685 := bstep (se 3 (by rfl) ⟨317003, by rfl⟩ : syracuseStep 1690685 = 634007) B634007
theorem B5787065 : Blo 499793 5787065 := bstep (se 2 (by rfl) ⟨2170149, by rfl⟩ : syracuseStep 5787065 = 4340299) B4340299
theorem B1429433 : Blo 499793 1429433 := bstep (se 2 (by rfl) ⟨536037, by rfl⟩ : syracuseStep 1429433 = 1072075) B1072075
theorem B1265665 : Blo 499793 1265665 := bstep (se 2 (by rfl) ⟨474624, by rfl⟩ : syracuseStep 1265665 = 949249) B949249
theorem B1429775 : Blo 499793 1429775 := bstep (se 1 (by rfl) ⟨1072331, by rfl⟩ : syracuseStep 1429775 = 2144663) B2144663
theorem B545167 : Blo 499793 545167 := bstep (se 1 (by rfl) ⟨408875, by rfl⟩ : syracuseStep 545167 = 817751) B817751
theorem B1692089 : Blo 499793 1692089 := bstep (se 2 (by rfl) ⟨634533, by rfl⟩ : syracuseStep 1692089 = 1269067) B1269067
theorem B12833315 : Blo 499793 12833315 := bstep (se 1 (by rfl) ⟨9624986, by rfl⟩ : syracuseStep 12833315 = 19249973) B19249973
theorem B676411 : Blo 499793 676411 := bstep (se 1 (by rfl) ⟨507308, by rfl⟩ : syracuseStep 676411 = 1014617) B1014617
theorem B1266263 : Blo 499793 1266263 := bstep (se 1 (by rfl) ⟨949697, by rfl⟩ : syracuseStep 1266263 = 1899395) B1899395
theorem B1266475 : Blo 499793 1266475 := bstep (se 1 (by rfl) ⟨949856, by rfl⟩ : syracuseStep 1266475 = 1899713) B1899713
theorem B1266617 : Blo 499793 1266617 := bstep (se 2 (by rfl) ⟨474981, by rfl⟩ : syracuseStep 1266617 = 949963) B949963
theorem B1692683 : Blo 499793 1692683 := bstep (se 1 (by rfl) ⟨1269512, by rfl⟩ : syracuseStep 1692683 = 2539025) B2539025
theorem B1430561 : Blo 499793 1430561 := bstep (se 2 (by rfl) ⟨536460, by rfl⟩ : syracuseStep 1430561 = 1072921) B1072921
theorem B1692791 : Blo 499793 1692791 := bstep (se 1 (by rfl) ⟨1269593, by rfl⟩ : syracuseStep 1692791 = 2539187) B2539187
theorem B4084937 : Blo 499793 4084937 := bstep (se 2 (by rfl) ⟨1531851, by rfl⟩ : syracuseStep 4084937 = 3063703) B3063703
theorem B4904339 : Blo 499793 4904339 := bstep (se 1 (by rfl) ⟨3678254, by rfl⟩ : syracuseStep 4904339 = 7356509) B7356509
theorem B2545181 : Blo 499793 2545181 := bstep (se 3 (by rfl) ⟨477221, by rfl⟩ : syracuseStep 2545181 = 954443) B954443
theorem B677449 : Blo 499793 677449 := bstep (se 2 (by rfl) ⟨254043, by rfl⟩ : syracuseStep 677449 = 508087) B508087
theorem B906871 : Blo 499793 906871 := bstep (se 1 (by rfl) ⟨680153, by rfl⟩ : syracuseStep 906871 = 1360307) B1360307
theorem B1201817 : Blo 499793 1201817 := bstep (se 2 (by rfl) ⟨450681, by rfl⟩ : syracuseStep 1201817 = 901363) B901363
theorem B1693385 : Blo 499793 1693385 := bstep (se 2 (by rfl) ⟨635019, by rfl⟩ : syracuseStep 1693385 = 1270039) B1270039
theorem B3823361 : Blo 499793 3823361 := bstep (se 2 (by rfl) ⟨1433760, by rfl⟩ : syracuseStep 3823361 = 2867521) B2867521
theorem B1267609 : Blo 499793 1267609 := bstep (se 2 (by rfl) ⟨475353, by rfl⟩ : syracuseStep 1267609 = 950707) B950707
theorem B6444953 : Blo 499793 6444953 := bstep (se 2 (by rfl) ⟨2416857, by rfl⟩ : syracuseStep 6444953 = 4833715) B4833715
theorem B5724107 : Blo 499793 5724107 := bstep (se 1 (by rfl) ⟨4293080, by rfl⟩ : syracuseStep 5724107 = 8586161) B8586161
theorem B2545667 : Blo 499793 2545667 := bstep (se 1 (by rfl) ⟨1909250, by rfl⟩ : syracuseStep 2545667 = 3818501) B3818501
theorem B1267771 : Blo 499793 1267771 := bstep (se 1 (by rfl) ⟨950828, by rfl⟩ : syracuseStep 1267771 = 1901657) B1901657
theorem B1267913 : Blo 499793 1267913 := bstep (se 2 (by rfl) ⟨475467, by rfl⟩ : syracuseStep 1267913 = 950935) B950935
theorem B645383 : Blo 499793 645383 := bstep (se 1 (by rfl) ⟨484037, by rfl⟩ : syracuseStep 645383 = 968075) B968075
theorem B1694087 : Blo 499793 1694087 := bstep (se 1 (by rfl) ⟨1270565, by rfl⟩ : syracuseStep 1694087 = 2541131) B2541131
theorem B1432075 : Blo 499793 1432075 := bstep (se 1 (by rfl) ⟨1074056, by rfl⟩ : syracuseStep 1432075 = 2148113) B2148113
theorem B1268257 : Blo 499793 1268257 := bstep (se 2 (by rfl) ⟨475596, by rfl⟩ : syracuseStep 1268257 = 951193) B951193
theorem B1694465 : Blo 499793 1694465 := bstep (se 2 (by rfl) ⟨635424, by rfl⟩ : syracuseStep 1694465 = 1270849) B1270849
theorem B1432349 : Blo 499793 1432349 := bstep (se 3 (by rfl) ⟨268565, by rfl⟩ : syracuseStep 1432349 = 537131) B537131
theorem B2710361 : Blo 499793 2710361 := bstep (se 2 (by rfl) ⟨1016385, by rfl⟩ : syracuseStep 2710361 = 2032771) B2032771
theorem B1432691 : Blo 499793 1432691 := bstep (se 1 (by rfl) ⟨1074518, by rfl⟩ : syracuseStep 1432691 = 2149037) B2149037
theorem B1268855 : Blo 499793 1268855 := bstep (se 1 (by rfl) ⟨951641, by rfl⟩ : syracuseStep 1268855 = 1903283) B1903283
theorem B711823 : Blo 499793 711823 := bstep (se 1 (by rfl) ⟨533867, by rfl⟩ : syracuseStep 711823 = 1067735) B1067735
theorem B1924499 : Blo 499793 1924499 := bstep (se 1 (by rfl) ⟨1443374, by rfl⟩ : syracuseStep 1924499 = 2886749) B2886749
theorem B712199 : Blo 499793 712199 := bstep (se 1 (by rfl) ⟨534149, by rfl⟩ : syracuseStep 712199 = 1068299) B1068299
theorem B1072673 : Blo 499793 1072673 := bstep (se 2 (by rfl) ⟨402252, by rfl⟩ : syracuseStep 1072673 = 804505) B804505
theorem B1695275 : Blo 499793 1695275 := bstep (se 1 (by rfl) ⟨1271456, by rfl⟩ : syracuseStep 1695275 = 2542913) B2542913
theorem B2547287 : Blo 499793 2547287 := bstep (se 1 (by rfl) ⟨1910465, by rfl⟩ : syracuseStep 2547287 = 3820931) B3820931
theorem B1203913 : Blo 499793 1203913 := bstep (se 2 (by rfl) ⟨451467, by rfl⟩ : syracuseStep 1203913 = 902935) B902935
theorem B4284197 : Blo 499793 4284197 := bstep (se 4 (by rfl) ⟨401643, by rfl⟩ : syracuseStep 4284197 = 803287) B803287
theorem B14868269 : Blo 499793 14868269 := bstep (se 3 (by rfl) ⟨2787800, by rfl⟩ : syracuseStep 14868269 = 5575601) B5575601
theorem B4054835 : Blo 499793 4054835 := bstep (se 1 (by rfl) ⟨3041126, by rfl⟩ : syracuseStep 4054835 = 6082253) B6082253
theorem B679753 : Blo 499793 679753 := bstep (se 2 (by rfl) ⟨254907, by rfl⟩ : syracuseStep 679753 = 509815) B509815
theorem B843655 : Blo 499793 843655 := bstep (se 1 (by rfl) ⟨632741, by rfl⟩ : syracuseStep 843655 = 1265483) B1265483
theorem B1433659 : Blo 499793 1433659 := bstep (se 1 (by rfl) ⟨1075244, by rfl⟩ : syracuseStep 1433659 = 2150489) B2150489
theorem B2547773 : Blo 499793 2547773 := bstep (se 3 (by rfl) ⟨477707, by rfl⟩ : syracuseStep 2547773 = 955415) B955415
theorem B2416841 : Blo 499793 2416841 := bstep (se 2 (by rfl) ⟨906315, by rfl⟩ : syracuseStep 2416841 = 1812631) B1812631
theorem B2711789 : Blo 499793 2711789 := bstep (se 3 (by rfl) ⟨508460, by rfl⟩ : syracuseStep 2711789 = 1016921) B1016921
theorem B3203387 : Blo 499793 3203387 := bstep (se 1 (by rfl) ⟨2402540, by rfl⟩ : syracuseStep 3203387 = 4805081) B4805081
theorem B1270151 : Blo 499793 1270151 := bstep (se 1 (by rfl) ⟨952613, by rfl⟩ : syracuseStep 1270151 = 1905227) B1905227
theorem B1270201 : Blo 499793 1270201 := bstep (se 2 (by rfl) ⟨476325, by rfl⟩ : syracuseStep 1270201 = 952651) B952651
theorem B844303 : Blo 499793 844303 := bstep (se 1 (by rfl) ⟨633227, by rfl⟩ : syracuseStep 844303 = 1266455) B1266455
theorem B1073783 : Blo 499793 1073783 := bstep (se 1 (by rfl) ⟨805337, by rfl⟩ : syracuseStep 1073783 = 1610675) B1610675
theorem B3629873 : Blo 499793 3629873 := bstep (se 2 (by rfl) ⟨1361202, by rfl⟩ : syracuseStep 3629873 = 2722405) B2722405
theorem B1696571 : Blo 499793 1696571 := bstep (se 1 (by rfl) ⟨1272428, by rfl⟩ : syracuseStep 1696571 = 2544857) B2544857
theorem B713657 : Blo 499793 713657 := bstep (se 2 (by rfl) ⟨267621, by rfl⟩ : syracuseStep 713657 = 535243) B535243
theorem B1270799 : Blo 499793 1270799 := bstep (se 1 (by rfl) ⟨953099, by rfl⟩ : syracuseStep 1270799 = 1906199) B1906199
theorem B844843 : Blo 499793 844843 := bstep (se 1 (by rfl) ⟨633632, by rfl⟩ : syracuseStep 844843 = 1267265) B1267265
theorem B844985 : Blo 499793 844985 := bstep (se 2 (by rfl) ⟨316869, by rfl⟩ : syracuseStep 844985 = 633739) B633739
theorem B2974913 : Blo 499793 2974913 := bstep (se 2 (by rfl) ⟨1115592, by rfl⟩ : syracuseStep 2974913 = 2231185) B2231185
theorem B1697057 : Blo 499793 1697057 := bstep (se 2 (by rfl) ⟨636396, by rfl⟩ : syracuseStep 1697057 = 1272793) B1272793
theorem B6448643 : Blo 499793 6448643 := bstep (se 1 (by rfl) ⟨4836482, by rfl⟩ : syracuseStep 6448643 = 9672965) B9672965
theorem B10872397 : Blo 499793 10872397 := bstep (se 3 (by rfl) ⟨2038574, by rfl⟩ : syracuseStep 10872397 = 4077149) B4077149
theorem B1271497 : Blo 499793 1271497 := bstep (se 2 (by rfl) ⟨476811, by rfl⟩ : syracuseStep 1271497 = 953623) B953623
theorem B714511 : Blo 499793 714511 := bstep (se 1 (by rfl) ⟨535883, by rfl⟩ : syracuseStep 714511 = 1071767) B1071767
theorem B2549555 : Blo 499793 2549555 := bstep (se 1 (by rfl) ⟨1912166, by rfl⟩ : syracuseStep 2549555 = 3824333) B3824333
theorem B1271639 : Blo 499793 1271639 := bstep (se 1 (by rfl) ⟨953729, by rfl⟩ : syracuseStep 1271639 = 1907459) B1907459
theorem B1697651 : Blo 499793 1697651 := bstep (se 1 (by rfl) ⟨1273238, by rfl⟩ : syracuseStep 1697651 = 2546477) B2546477
theorem B14444405 : Blo 499793 14444405 := bstep (se 5 (by rfl) ⟨677081, by rfl⟩ : syracuseStep 14444405 = 1354163) B1354163
theorem B845687 : Blo 499793 845687 := bstep (se 1 (by rfl) ⟨634265, by rfl⟩ : syracuseStep 845687 = 1268531) B1268531
theorem B2549879 : Blo 499793 2549879 := bstep (se 1 (by rfl) ⟨1912409, by rfl⟩ : syracuseStep 2549879 = 3824819) B3824819
theorem B6875381 : Blo 499793 6875381 := bstep (se 5 (by rfl) ⟨322283, by rfl⟩ : syracuseStep 6875381 = 644567) B644567
theorem B846139 : Blo 499793 846139 := bstep (se 1 (by rfl) ⟨634604, by rfl⟩ : syracuseStep 846139 = 1269209) B1269209
theorem B715081 : Blo 499793 715081 := bstep (se 2 (by rfl) ⟨268155, by rfl⟩ : syracuseStep 715081 = 536311) B536311
theorem B5794183 : Blo 499793 5794183 := bstep (se 1 (by rfl) ⟨4345637, by rfl⟩ : syracuseStep 5794183 = 8691275) B8691275
theorem B846281 : Blo 499793 846281 := bstep (se 2 (by rfl) ⟨317355, by rfl⟩ : syracuseStep 846281 = 634711) B634711
theorem B13560281 : Blo 499793 13560281 := bstep (se 2 (by rfl) ⟨5085105, by rfl⟩ : syracuseStep 13560281 = 10170211) B10170211
theorem B780815 : Blo 499793 780815 := bstep (se 1 (by rfl) ⟨585611, by rfl⟩ : syracuseStep 780815 = 1171223) B1171223
theorem B5434127 : Blo 499793 5434127 := bstep (se 1 (by rfl) ⟨4075595, by rfl⟩ : syracuseStep 5434127 = 8151191) B8151191
theorem B5893181 : Blo 499793 5893181 := bstep (se 3 (by rfl) ⟨1104971, by rfl⟩ : syracuseStep 5893181 = 2209943) B2209943
theorem B846983 : Blo 499793 846983 := bstep (se 1 (by rfl) ⟨635237, by rfl⟩ : syracuseStep 846983 = 1270475) B1270475
theorem B2289239 : Blo 499793 2289239 := bstep (se 1 (by rfl) ⟨1716929, by rfl⟩ : syracuseStep 2289239 = 3433859) B3433859
theorem B847631 : Blo 499793 847631 := bstep (se 1 (by rfl) ⟨635723, by rfl⟩ : syracuseStep 847631 = 1271447) B1271447
theorem B1273715 : Blo 499793 1273715 := bstep (se 1 (by rfl) ⟨955286, by rfl⟩ : syracuseStep 1273715 = 1910573) B1910573
theorem B2846609 : Blo 499793 2846609 := bstep (se 2 (by rfl) ⟨1067478, by rfl⟩ : syracuseStep 2846609 = 2134957) B2134957
theorem B4190231 : Blo 499793 4190231 := bstep (se 1 (by rfl) ⟨3142673, by rfl⟩ : syracuseStep 4190231 = 6285347) B6285347
theorem B1634365 : Blo 499793 1634365 := bstep (se 3 (by rfl) ⟨306443, by rfl⟩ : syracuseStep 1634365 = 612887) B612887
theorem B749711 : Blo 499793 749711 := bstep (se 1 (by rfl) ⟨562283, by rfl⟩ : syracuseStep 749711 = 1124567) B1124567
theorem B749753 : Blo 499793 749753 := bstep (se 2 (by rfl) ⟨281157, by rfl⟩ : syracuseStep 749753 = 562315) B562315
theorem B749831 : Blo 499793 749831 := bstep (se 1 (by rfl) ⟨562373, by rfl⟩ : syracuseStep 749831 = 1124747) B1124747
theorem B749867 : Blo 499793 749867 := bstep (se 1 (by rfl) ⟨562400, by rfl⟩ : syracuseStep 749867 = 1124801) B1124801
theorem B848171 : Blo 499793 848171 := bstep (se 1 (by rfl) ⟨636128, by rfl⟩ : syracuseStep 848171 = 1272257) B1272257
theorem B749897 : Blo 499793 749897 := bstep (se 2 (by rfl) ⟨281211, by rfl⟩ : syracuseStep 749897 = 562423) B562423
theorem B1274231 : Blo 499793 1274231 := bstep (se 1 (by rfl) ⟨955673, by rfl⟩ : syracuseStep 1274231 = 1911347) B1911347
theorem B1700243 : Blo 499793 1700243 := bstep (se 1 (by rfl) ⟨1275182, by rfl⟩ : syracuseStep 1700243 = 2550365) B2550365
theorem B750011 : Blo 499793 750011 := bstep (se 1 (by rfl) ⟨562508, by rfl⟩ : syracuseStep 750011 = 1125017) B1125017
theorem B750071 : Blo 499793 750071 := bstep (se 1 (by rfl) ⟨562553, by rfl⟩ : syracuseStep 750071 = 1125107) B1125107
theorem B750095 : Blo 499793 750095 := bstep (se 1 (by rfl) ⟨562571, by rfl⟩ : syracuseStep 750095 = 1125143) B1125143
theorem B750137 : Blo 499793 750137 := bstep (se 2 (by rfl) ⟨281301, by rfl⟩ : syracuseStep 750137 = 562603) B562603
theorem B750215 : Blo 499793 750215 := bstep (se 1 (by rfl) ⟨562661, by rfl⟩ : syracuseStep 750215 = 1125323) B1125323
theorem B750251 : Blo 499793 750251 := bstep (se 1 (by rfl) ⟨562688, by rfl⟩ : syracuseStep 750251 = 1125377) B1125377
theorem B848569 : Blo 499793 848569 := bstep (se 2 (by rfl) ⟨318213, by rfl⟩ : syracuseStep 848569 = 636427) B636427
theorem B750281 : Blo 499793 750281 := bstep (se 2 (by rfl) ⟨281355, by rfl⟩ : syracuseStep 750281 = 562711) B562711
theorem B750395 : Blo 499793 750395 := bstep (se 1 (by rfl) ⟨562796, by rfl⟩ : syracuseStep 750395 = 1125593) B1125593
theorem B750455 : Blo 499793 750455 := bstep (se 1 (by rfl) ⟨562841, by rfl⟩ : syracuseStep 750455 = 1125683) B1125683
theorem B750479 : Blo 499793 750479 := bstep (se 1 (by rfl) ⟨562859, by rfl⟩ : syracuseStep 750479 = 1125719) B1125719
theorem B2847635 : Blo 499793 2847635 := bstep (se 1 (by rfl) ⟨2135726, by rfl⟩ : syracuseStep 2847635 = 4271453) B4271453
theorem B3044243 : Blo 499793 3044243 := bstep (se 1 (by rfl) ⟨2283182, by rfl⟩ : syracuseStep 3044243 = 4566365) B4566365
theorem B750521 : Blo 499793 750521 := bstep (se 2 (by rfl) ⟨281445, by rfl⟩ : syracuseStep 750521 = 562891) B562891
theorem B914377 : Blo 499793 914377 := bstep (se 2 (by rfl) ⟨342891, by rfl⟩ : syracuseStep 914377 = 685783) B685783
theorem B24474581 : Blo 499793 24474581 := bstep (se 7 (by rfl) ⟨286811, by rfl⟩ : syracuseStep 24474581 = 573623) B573623
theorem B750599 : Blo 499793 750599 := bstep (se 1 (by rfl) ⟨562949, by rfl⟩ : syracuseStep 750599 = 1125899) B1125899
theorem B750635 : Blo 499793 750635 := bstep (se 1 (by rfl) ⟨562976, by rfl⟩ : syracuseStep 750635 = 1125953) B1125953
theorem B4289597 : Blo 499793 4289597 := bstep (se 3 (by rfl) ⟨804299, by rfl⟩ : syracuseStep 4289597 = 1608599) B1608599
theorem B750665 : Blo 499793 750665 := bstep (se 2 (by rfl) ⟨281499, by rfl⟩ : syracuseStep 750665 = 562999) B562999
theorem B1602679 : Blo 499793 1602679 := bstep (se 1 (by rfl) ⟨1202009, by rfl⟩ : syracuseStep 1602679 = 2404019) B2404019
theorem B750779 : Blo 499793 750779 := bstep (se 1 (by rfl) ⟨563084, by rfl⟩ : syracuseStep 750779 = 1126169) B1126169
theorem B1209545 : Blo 499793 1209545 := bstep (se 2 (by rfl) ⟨453579, by rfl⟩ : syracuseStep 1209545 = 907159) B907159
theorem B750839 : Blo 499793 750839 := bstep (se 1 (by rfl) ⟨563129, by rfl⟩ : syracuseStep 750839 = 1126259) B1126259
theorem B750863 : Blo 499793 750863 := bstep (se 1 (by rfl) ⟨563147, by rfl⟩ : syracuseStep 750863 = 1126295) B1126295
theorem B750905 : Blo 499793 750905 := bstep (se 2 (by rfl) ⟨281589, by rfl⟩ : syracuseStep 750905 = 563179) B563179
theorem B1209659 : Blo 499793 1209659 := bstep (se 1 (by rfl) ⟨907244, by rfl⟩ : syracuseStep 1209659 = 1814489) B1814489
theorem B1275223 : Blo 499793 1275223 := bstep (se 1 (by rfl) ⟨956417, by rfl⟩ : syracuseStep 1275223 = 1912835) B1912835
theorem B849271 : Blo 499793 849271 := bstep (se 1 (by rfl) ⟨636953, by rfl⟩ : syracuseStep 849271 = 1273907) B1273907
theorem B750983 : Blo 499793 750983 := bstep (se 1 (by rfl) ⟨563237, by rfl⟩ : syracuseStep 750983 = 1126475) B1126475
theorem B751019 : Blo 499793 751019 := bstep (se 1 (by rfl) ⟨563264, by rfl⟩ : syracuseStep 751019 = 1126529) B1126529
theorem B751049 : Blo 499793 751049 := bstep (se 2 (by rfl) ⟨281643, by rfl⟩ : syracuseStep 751049 = 563287) B563287
theorem B1897937 : Blo 499793 1897937 := bstep (se 2 (by rfl) ⟨711726, by rfl⟩ : syracuseStep 1897937 = 1423453) B1423453
theorem B751163 : Blo 499793 751163 := bstep (se 1 (by rfl) ⟨563372, by rfl⟩ : syracuseStep 751163 = 1126745) B1126745
theorem B849467 : Blo 499793 849467 := bstep (se 1 (by rfl) ⟨637100, by rfl⟩ : syracuseStep 849467 = 1274201) B1274201
theorem B751223 : Blo 499793 751223 := bstep (se 1 (by rfl) ⟨563417, by rfl⟩ : syracuseStep 751223 = 1126835) B1126835
theorem B751247 : Blo 499793 751247 := bstep (se 1 (by rfl) ⟨563435, by rfl⟩ : syracuseStep 751247 = 1126871) B1126871
theorem B751289 : Blo 499793 751289 := bstep (se 2 (by rfl) ⟨281733, by rfl⟩ : syracuseStep 751289 = 563467) B563467
theorem B751367 : Blo 499793 751367 := bstep (se 1 (by rfl) ⟨563525, by rfl⟩ : syracuseStep 751367 = 1127051) B1127051
theorem B1898255 : Blo 499793 1898255 := bstep (se 1 (by rfl) ⟨1423691, by rfl⟩ : syracuseStep 1898255 = 2847383) B2847383
theorem B5011237 : Blo 499793 5011237 := bstep (se 4 (by rfl) ⟨469803, by rfl⟩ : syracuseStep 5011237 = 939607) B939607
theorem B3208997 : Blo 499793 3208997 := bstep (se 4 (by rfl) ⟨300843, by rfl⟩ : syracuseStep 3208997 = 601687) B601687
theorem B751403 : Blo 499793 751403 := bstep (se 1 (by rfl) ⟨563552, by rfl⟩ : syracuseStep 751403 = 1127105) B1127105
theorem B751433 : Blo 499793 751433 := bstep (se 2 (by rfl) ⟨281787, by rfl⟩ : syracuseStep 751433 = 563575) B563575
theorem B3667801 : Blo 499793 3667801 := bstep (se 2 (by rfl) ⟨1375425, by rfl⟩ : syracuseStep 3667801 = 2750851) B2750851
theorem B751547 : Blo 499793 751547 := bstep (se 1 (by rfl) ⟨563660, by rfl⟩ : syracuseStep 751547 = 1127321) B1127321
theorem B849865 : Blo 499793 849865 := bstep (se 2 (by rfl) ⟨318699, by rfl⟩ : syracuseStep 849865 = 637399) B637399
theorem B751607 : Blo 499793 751607 := bstep (se 1 (by rfl) ⟨563705, by rfl⟩ : syracuseStep 751607 = 1127411) B1127411
theorem B751631 : Blo 499793 751631 := bstep (se 1 (by rfl) ⟨563723, by rfl⟩ : syracuseStep 751631 = 1127447) B1127447
theorem B751673 : Blo 499793 751673 := bstep (se 2 (by rfl) ⟨281877, by rfl⟩ : syracuseStep 751673 = 563755) B563755
theorem B751751 : Blo 499793 751751 := bstep (se 1 (by rfl) ⟨563813, by rfl⟩ : syracuseStep 751751 = 1127627) B1127627
theorem B751787 : Blo 499793 751787 := bstep (se 1 (by rfl) ⟨563840, by rfl⟩ : syracuseStep 751787 = 1127681) B1127681
theorem B751817 : Blo 499793 751817 := bstep (se 2 (by rfl) ⟨281931, by rfl⟩ : syracuseStep 751817 = 563863) B563863
theorem B751931 : Blo 499793 751931 := bstep (se 1 (by rfl) ⟨563948, by rfl⟩ : syracuseStep 751931 = 1127897) B1127897
theorem B1309043 : Blo 499793 1309043 := bstep (se 1 (by rfl) ⟨981782, by rfl⟩ : syracuseStep 1309043 = 1963565) B1963565
theorem B751991 : Blo 499793 751991 := bstep (se 1 (by rfl) ⟨563993, by rfl⟩ : syracuseStep 751991 = 1127987) B1127987
theorem B752015 : Blo 499793 752015 := bstep (se 1 (by rfl) ⟨564011, by rfl⟩ : syracuseStep 752015 = 1128023) B1128023
theorem B73202069 : Blo 499793 73202069 := bstep (se 6 (by rfl) ⟨1715673, by rfl⟩ : syracuseStep 73202069 = 3431347) B3431347
theorem B752057 : Blo 499793 752057 := bstep (se 2 (by rfl) ⟨282021, by rfl⟩ : syracuseStep 752057 = 564043) B564043
theorem B752135 : Blo 499793 752135 := bstep (se 1 (by rfl) ⟨564101, by rfl⟩ : syracuseStep 752135 = 1128203) B1128203
theorem B752171 : Blo 499793 752171 := bstep (se 1 (by rfl) ⟨564128, by rfl⟩ : syracuseStep 752171 = 1128257) B1128257
theorem B752201 : Blo 499793 752201 := bstep (se 2 (by rfl) ⟨282075, by rfl⟩ : syracuseStep 752201 = 564151) B564151
theorem B752315 : Blo 499793 752315 := bstep (se 1 (by rfl) ⟨564236, by rfl⟩ : syracuseStep 752315 = 1128473) B1128473
theorem B752375 : Blo 499793 752375 := bstep (se 1 (by rfl) ⟨564281, by rfl⟩ : syracuseStep 752375 = 1128563) B1128563
theorem B752399 : Blo 499793 752399 := bstep (se 1 (by rfl) ⟨564299, by rfl⟩ : syracuseStep 752399 = 1128599) B1128599
theorem B752441 : Blo 499793 752441 := bstep (se 2 (by rfl) ⟨282165, by rfl⟩ : syracuseStep 752441 = 564331) B564331
theorem B752519 : Blo 499793 752519 := bstep (se 1 (by rfl) ⟨564389, by rfl⟩ : syracuseStep 752519 = 1128779) B1128779
theorem B752555 : Blo 499793 752555 := bstep (se 1 (by rfl) ⟨564416, by rfl⟩ : syracuseStep 752555 = 1128833) B1128833
theorem B752585 : Blo 499793 752585 := bstep (se 2 (by rfl) ⟨282219, by rfl⟩ : syracuseStep 752585 = 564439) B564439
theorem B752699 : Blo 499793 752699 := bstep (se 1 (by rfl) ⟨564524, by rfl⟩ : syracuseStep 752699 = 1129049) B1129049
theorem B752759 : Blo 499793 752759 := bstep (se 1 (by rfl) ⟨564569, by rfl⟩ : syracuseStep 752759 = 1129139) B1129139
theorem B752783 : Blo 499793 752783 := bstep (se 1 (by rfl) ⟨564587, by rfl⟩ : syracuseStep 752783 = 1129175) B1129175
theorem B752825 : Blo 499793 752825 := bstep (se 2 (by rfl) ⟨282309, by rfl⟩ : syracuseStep 752825 = 564619) B564619
theorem B752903 : Blo 499793 752903 := bstep (se 1 (by rfl) ⟨564677, by rfl⟩ : syracuseStep 752903 = 1129355) B1129355
theorem B752939 : Blo 499793 752939 := bstep (se 1 (by rfl) ⟨564704, by rfl⟩ : syracuseStep 752939 = 1129409) B1129409
theorem B752969 : Blo 499793 752969 := bstep (se 2 (by rfl) ⟨282363, by rfl⟩ : syracuseStep 752969 = 564727) B564727
theorem B4291987 : Blo 499793 4291987 := bstep (se 1 (by rfl) ⟨3218990, by rfl⟩ : syracuseStep 4291987 = 6437981) B6437981
theorem B753083 : Blo 499793 753083 := bstep (se 1 (by rfl) ⟨564812, by rfl⟩ : syracuseStep 753083 = 1129625) B1129625
theorem B753143 : Blo 499793 753143 := bstep (se 1 (by rfl) ⟨564857, by rfl⟩ : syracuseStep 753143 = 1129715) B1129715
theorem B753167 : Blo 499793 753167 := bstep (se 1 (by rfl) ⟨564875, by rfl⟩ : syracuseStep 753167 = 1129751) B1129751
theorem B753209 : Blo 499793 753209 := bstep (se 2 (by rfl) ⟨282453, by rfl⟩ : syracuseStep 753209 = 564907) B564907
theorem B949819 : Blo 499793 949819 := bstep (se 1 (by rfl) ⟨712364, by rfl⟩ : syracuseStep 949819 = 1424729) B1424729
theorem B753287 : Blo 499793 753287 := bstep (se 1 (by rfl) ⟨564965, by rfl⟩ : syracuseStep 753287 = 1129931) B1129931
theorem B753323 : Blo 499793 753323 := bstep (se 1 (by rfl) ⟨564992, by rfl⟩ : syracuseStep 753323 = 1129985) B1129985
theorem B753353 : Blo 499793 753353 := bstep (se 2 (by rfl) ⟨282507, by rfl⟩ : syracuseStep 753353 = 565015) B565015
theorem B753467 : Blo 499793 753467 := bstep (se 1 (by rfl) ⟨565100, by rfl⟩ : syracuseStep 753467 = 1130201) B1130201
theorem B753527 : Blo 499793 753527 := bstep (se 1 (by rfl) ⟨565145, by rfl⟩ : syracuseStep 753527 = 1130291) B1130291
theorem B753551 : Blo 499793 753551 := bstep (se 1 (by rfl) ⟨565163, by rfl⟩ : syracuseStep 753551 = 1130327) B1130327
theorem B753593 : Blo 499793 753593 := bstep (se 2 (by rfl) ⟨282597, by rfl⟩ : syracuseStep 753593 = 565195) B565195
theorem B753743 : Blo 499793 753743 := bstep (se 1 (by rfl) ⟨565307, by rfl⟩ : syracuseStep 753743 = 1130615) B1130615
theorem B753863 : Blo 499793 753863 := bstep (se 1 (by rfl) ⟨565397, by rfl⟩ : syracuseStep 753863 = 1130795) B1130795
theorem B2031959 : Blo 499793 2031959 := bstep (se 1 (by rfl) ⟨1523969, by rfl⟩ : syracuseStep 2031959 = 3047939) B3047939
theorem B754025 : Blo 499793 754025 := bstep (se 2 (by rfl) ⟨282759, by rfl⟩ : syracuseStep 754025 = 565519) B565519
theorem B754103 : Blo 499793 754103 := bstep (se 1 (by rfl) ⟨565577, by rfl⟩ : syracuseStep 754103 = 1131155) B1131155
theorem B754139 : Blo 499793 754139 := bstep (se 1 (by rfl) ⟨565604, by rfl⟩ : syracuseStep 754139 = 1131209) B1131209
theorem B950791 : Blo 499793 950791 := bstep (se 1 (by rfl) ⟨713093, by rfl⟩ : syracuseStep 950791 = 1426187) B1426187
theorem B2065247 : Blo 499793 2065247 := bstep (se 1 (by rfl) ⟨1548935, by rfl⟩ : syracuseStep 2065247 = 3097871) B3097871
theorem B754607 : Blo 499793 754607 := bstep (se 1 (by rfl) ⟨565955, by rfl⟩ : syracuseStep 754607 = 1131911) B1131911
theorem B754697 : Blo 499793 754697 := bstep (se 2 (by rfl) ⟨283011, by rfl⟩ : syracuseStep 754697 = 566023) B566023
theorem B754727 : Blo 499793 754727 := bstep (se 1 (by rfl) ⟨566045, by rfl⟩ : syracuseStep 754727 = 1132091) B1132091
theorem B754811 : Blo 499793 754811 := bstep (se 1 (by rfl) ⟨566108, by rfl⟩ : syracuseStep 754811 = 1132217) B1132217
theorem B754937 : Blo 499793 754937 := bstep (se 2 (by rfl) ⟨283101, by rfl⟩ : syracuseStep 754937 = 566203) B566203
theorem B755039 : Blo 499793 755039 := bstep (se 1 (by rfl) ⟨566279, by rfl⟩ : syracuseStep 755039 = 1132559) B1132559
theorem B755051 : Blo 499793 755051 := bstep (se 1 (by rfl) ⟨566288, by rfl⟩ : syracuseStep 755051 = 1132577) B1132577
theorem B3868019 : Blo 499793 3868019 := bstep (se 1 (by rfl) ⟨2901014, by rfl⟩ : syracuseStep 3868019 = 5802029) B5802029
theorem B1902113 : Blo 499793 1902113 := bstep (se 2 (by rfl) ⟨713292, by rfl⟩ : syracuseStep 1902113 = 1426585) B1426585
theorem B755279 : Blo 499793 755279 := bstep (se 1 (by rfl) ⟨566459, by rfl⟩ : syracuseStep 755279 = 1132919) B1132919
theorem B3212945 : Blo 499793 3212945 := bstep (se 2 (by rfl) ⟨1204854, by rfl⟩ : syracuseStep 3212945 = 2409709) B2409709
theorem B755399 : Blo 499793 755399 := bstep (se 1 (by rfl) ⟨566549, by rfl⟩ : syracuseStep 755399 = 1133099) B1133099
theorem B1804025 : Blo 499793 1804025 := bstep (se 2 (by rfl) ⟨676509, by rfl⟩ : syracuseStep 1804025 = 1353019) B1353019
theorem B755561 : Blo 499793 755561 := bstep (se 2 (by rfl) ⟨283335, by rfl⟩ : syracuseStep 755561 = 566671) B566671
theorem B755639 : Blo 499793 755639 := bstep (se 1 (by rfl) ⟨566729, by rfl⟩ : syracuseStep 755639 = 1133459) B1133459
theorem B755675 : Blo 499793 755675 := bstep (se 1 (by rfl) ⟨566756, by rfl⟩ : syracuseStep 755675 = 1133513) B1133513
theorem B1902599 : Blo 499793 1902599 := bstep (se 1 (by rfl) ⟨1426949, by rfl⟩ : syracuseStep 1902599 = 2853899) B2853899
theorem B30902309 : Blo 499793 30902309 := bstep (se 4 (by rfl) ⟨2897091, by rfl⟩ : syracuseStep 30902309 = 5794183) B5794183
theorem B14518673 : Blo 499793 14518673 := bstep (se 2 (by rfl) ⟨5444502, by rfl⟩ : syracuseStep 14518673 = 10889005) B10889005
theorem B5507531 : Blo 499793 5507531 := bstep (se 1 (by rfl) ⟨4130648, by rfl⟩ : syracuseStep 5507531 = 8261297) B8261297
theorem B1903085 : Blo 499793 1903085 := bstep (se 3 (by rfl) ⟨356828, by rfl⟩ : syracuseStep 1903085 = 713657) B713657
theorem B952955 : Blo 499793 952955 := bstep (se 1 (by rfl) ⟨714716, by rfl⟩ : syracuseStep 952955 = 1429433) B1429433
theorem B953183 : Blo 499793 953183 := bstep (se 1 (by rfl) ⟨714887, by rfl⟩ : syracuseStep 953183 = 1429775) B1429775
theorem B3607525 : Blo 499793 3607525 := bstep (se 4 (by rfl) ⟨338205, by rfl⟩ : syracuseStep 3607525 = 676411) B676411
theorem B8555543 : Blo 499793 8555543 := bstep (se 1 (by rfl) ⟨6416657, by rfl⟩ : syracuseStep 8555543 = 12833315) B12833315
theorem B953441 : Blo 499793 953441 := bstep (se 2 (by rfl) ⟨357540, by rfl⟩ : syracuseStep 953441 = 715081) B715081
theorem B1903769 : Blo 499793 1903769 := bstep (se 2 (by rfl) ⟨713913, by rfl⟩ : syracuseStep 1903769 = 1427827) B1427827
theorem B3804407 : Blo 499793 3804407 := bstep (se 1 (by rfl) ⟨2853305, by rfl⟩ : syracuseStep 3804407 = 5706611) B5706611
theorem B953707 : Blo 499793 953707 := bstep (se 1 (by rfl) ⟨715280, by rfl⟩ : syracuseStep 953707 = 1430561) B1430561
theorem B2723291 : Blo 499793 2723291 := bstep (se 1 (by rfl) ⟨2042468, by rfl⟩ : syracuseStep 2723291 = 4084937) B4084937
theorem B3804893 : Blo 499793 3804893 := bstep (se 3 (by rfl) ⟨713417, by rfl⟩ : syracuseStep 3804893 = 1426835) B1426835
theorem B6426499 : Blo 499793 6426499 := bstep (se 1 (by rfl) ⟨4819874, by rfl⟩ : syracuseStep 6426499 = 9639749) B9639749
theorem B4296635 : Blo 499793 4296635 := bstep (se 1 (by rfl) ⟨3222476, by rfl⟩ : syracuseStep 4296635 = 6444953) B6444953
theorem B1904755 : Blo 499793 1904755 := bstep (se 1 (by rfl) ⟨1428566, by rfl⟩ : syracuseStep 1904755 = 2857133) B2857133
theorem B954899 : Blo 499793 954899 := bstep (se 1 (by rfl) ⟨716174, by rfl⟩ : syracuseStep 954899 = 1432349) B1432349
theorem B1806907 : Blo 499793 1806907 := bstep (se 1 (by rfl) ⟨1355180, by rfl⟩ : syracuseStep 1806907 = 2710361) B2710361
theorem B955127 : Blo 499793 955127 := bstep (se 1 (by rfl) ⟨716345, by rfl⟩ : syracuseStep 955127 = 1432691) B1432691
theorem B4133635 : Blo 499793 4133635 := bstep (se 1 (by rfl) ⟨3100226, by rfl⟩ : syracuseStep 4133635 = 6200453) B6200453
theorem B1905515 : Blo 499793 1905515 := bstep (se 1 (by rfl) ⟨1429136, by rfl⟩ : syracuseStep 1905515 = 2858273) B2858273
theorem B1282999 : Blo 499793 1282999 := bstep (se 1 (by rfl) ⟨962249, by rfl⟩ : syracuseStep 1282999 = 1924499) B1924499
theorem B9180161 : Blo 499793 9180161 := bstep (se 2 (by rfl) ⟨3442560, by rfl⟩ : syracuseStep 9180161 = 6885121) B6885121
theorem B7214129 : Blo 499793 7214129 := bstep (se 2 (by rfl) ⟨2705298, by rfl⟩ : syracuseStep 7214129 = 5410597) B5410597
theorem B2856131 : Blo 499793 2856131 := bstep (se 1 (by rfl) ⟨2142098, by rfl⟩ : syracuseStep 2856131 = 4284197) B4284197
theorem B8131985 : Blo 499793 8131985 := bstep (se 2 (by rfl) ⟨3049494, by rfl⟩ : syracuseStep 8131985 = 6098989) B6098989
theorem B1611227 : Blo 499793 1611227 := bstep (se 1 (by rfl) ⟨1208420, by rfl⟩ : syracuseStep 1611227 = 2416841) B2416841
theorem B1807859 : Blo 499793 1807859 := bstep (se 1 (by rfl) ⟨1355894, by rfl⟩ : syracuseStep 1807859 = 2711789) B2711789
theorem B2135591 : Blo 499793 2135591 := bstep (se 1 (by rfl) ⟨1601693, by rfl⟩ : syracuseStep 2135591 = 3203387) B3203387
theorem B988751 : Blo 499793 988751 := bstep (se 1 (by rfl) ⟨741563, by rfl⟩ : syracuseStep 988751 = 1483127) B1483127
theorem B726889 : Blo 499793 726889 := bstep (se 2 (by rfl) ⟨272583, by rfl⟩ : syracuseStep 726889 = 545167) B545167
theorem B563323 : Blo 499793 563323 := bstep (se 1 (by rfl) ⟨422492, by rfl⟩ : syracuseStep 563323 = 844985) B844985
theorem B4299095 : Blo 499793 4299095 := bstep (se 1 (by rfl) ⟨3224321, by rfl⟩ : syracuseStep 4299095 = 6448643) B6448643
theorem B563791 : Blo 499793 563791 := bstep (se 1 (by rfl) ⟨422843, by rfl⟩ : syracuseStep 563791 = 845687) B845687
theorem B1219169 : Blo 499793 1219169 := bstep (se 2 (by rfl) ⟨457188, by rfl⟩ : syracuseStep 1219169 = 914377) B914377
theorem B2136905 : Blo 499793 2136905 := bstep (se 2 (by rfl) ⟨801339, by rfl⟩ : syracuseStep 2136905 = 1602679) B1602679
theorem B564187 : Blo 499793 564187 := bstep (se 1 (by rfl) ⟨423140, by rfl⟩ : syracuseStep 564187 = 846281) B846281
theorem B564655 : Blo 499793 564655 := bstep (se 1 (by rfl) ⟨423491, by rfl⟩ : syracuseStep 564655 = 846983) B846983
theorem B9182645 : Blo 499793 9182645 := bstep (se 5 (by rfl) ⟨430436, by rfl⟩ : syracuseStep 9182645 = 860873) B860873
theorem B1449721 : Blo 499793 1449721 := bstep (se 2 (by rfl) ⟨543645, by rfl⟩ : syracuseStep 1449721 = 1087291) B1087291
theorem B4890401 : Blo 499793 4890401 := bstep (se 2 (by rfl) ⟨1833900, by rfl⟩ : syracuseStep 4890401 = 3667801) B3667801
theorem B565087 : Blo 499793 565087 := bstep (se 1 (by rfl) ⟨423815, by rfl⟩ : syracuseStep 565087 = 847631) B847631
theorem B2793487 : Blo 499793 2793487 := bstep (se 1 (by rfl) ⟨2095115, by rfl⟩ : syracuseStep 2793487 = 4190231) B4190231
theorem B499807 : Blo 499793 499807 := bstep (se 1 (by rfl) ⟨374855, by rfl⟩ : syracuseStep 499807 = 749711) B749711
theorem B499835 : Blo 499793 499835 := bstep (se 1 (by rfl) ⟨374876, by rfl⟩ : syracuseStep 499835 = 749753) B749753
theorem B499887 : Blo 499793 499887 := bstep (se 1 (by rfl) ⟨374915, by rfl⟩ : syracuseStep 499887 = 749831) B749831
theorem B499911 : Blo 499793 499911 := bstep (se 1 (by rfl) ⟨374933, by rfl⟩ : syracuseStep 499911 = 749867) B749867
theorem B565447 : Blo 499793 565447 := bstep (se 1 (by rfl) ⟨424085, by rfl⟩ : syracuseStep 565447 = 848171) B848171
theorem B499931 : Blo 499793 499931 := bstep (se 1 (by rfl) ⟨374948, by rfl⟩ : syracuseStep 499931 = 749897) B749897
theorem B500007 : Blo 499793 500007 := bstep (se 1 (by rfl) ⟨375005, by rfl⟩ : syracuseStep 500007 = 750011) B750011
theorem B500047 : Blo 499793 500047 := bstep (se 1 (by rfl) ⟨375035, by rfl⟩ : syracuseStep 500047 = 750071) B750071
theorem B500063 : Blo 499793 500063 := bstep (se 1 (by rfl) ⟨375047, by rfl⟩ : syracuseStep 500063 = 750095) B750095
theorem B500091 : Blo 499793 500091 := bstep (se 1 (by rfl) ⟨375068, by rfl⟩ : syracuseStep 500091 = 750137) B750137
theorem B3613061 : Blo 499793 3613061 := bstep (se 4 (by rfl) ⟨338724, by rfl⟩ : syracuseStep 3613061 = 677449) B677449
theorem B500143 : Blo 499793 500143 := bstep (se 1 (by rfl) ⟨375107, by rfl⟩ : syracuseStep 500143 = 750215) B750215
theorem B500167 : Blo 499793 500167 := bstep (se 1 (by rfl) ⟨375125, by rfl⟩ : syracuseStep 500167 = 750251) B750251
theorem B500187 : Blo 499793 500187 := bstep (se 1 (by rfl) ⟨375140, by rfl⟩ : syracuseStep 500187 = 750281) B750281
theorem B500263 : Blo 499793 500263 := bstep (se 1 (by rfl) ⟨375197, by rfl⟩ : syracuseStep 500263 = 750395) B750395
theorem B500303 : Blo 499793 500303 := bstep (se 1 (by rfl) ⟨375227, by rfl⟩ : syracuseStep 500303 = 750455) B750455
theorem B500319 : Blo 499793 500319 := bstep (se 1 (by rfl) ⟨375239, by rfl⟩ : syracuseStep 500319 = 750479) B750479
theorem B500347 : Blo 499793 500347 := bstep (se 1 (by rfl) ⟨375260, by rfl⟩ : syracuseStep 500347 = 750521) B750521
theorem B500399 : Blo 499793 500399 := bstep (se 1 (by rfl) ⟨375299, by rfl⟩ : syracuseStep 500399 = 750599) B750599
theorem B1909433 : Blo 499793 1909433 := bstep (se 2 (by rfl) ⟨716037, by rfl⟩ : syracuseStep 1909433 = 1432075) B1432075
theorem B500423 : Blo 499793 500423 := bstep (se 1 (by rfl) ⟨375317, by rfl⟩ : syracuseStep 500423 = 750635) B750635
theorem B2859731 : Blo 499793 2859731 := bstep (se 1 (by rfl) ⟨2144798, by rfl⟩ : syracuseStep 2859731 = 4289597) B4289597
theorem B500443 : Blo 499793 500443 := bstep (se 1 (by rfl) ⟨375332, by rfl⟩ : syracuseStep 500443 = 750665) B750665
theorem B500519 : Blo 499793 500519 := bstep (se 1 (by rfl) ⟨375389, by rfl⟩ : syracuseStep 500519 = 750779) B750779
theorem B500559 : Blo 499793 500559 := bstep (se 1 (by rfl) ⟨375419, by rfl⟩ : syracuseStep 500559 = 750839) B750839
theorem B500575 : Blo 499793 500575 := bstep (se 1 (by rfl) ⟨375431, by rfl⟩ : syracuseStep 500575 = 750863) B750863
theorem B500603 : Blo 499793 500603 := bstep (se 1 (by rfl) ⟨375452, by rfl⟩ : syracuseStep 500603 = 750905) B750905
theorem B500655 : Blo 499793 500655 := bstep (se 1 (by rfl) ⟨375491, by rfl⟩ : syracuseStep 500655 = 750983) B750983
theorem B3089335 : Blo 499793 3089335 := bstep (se 1 (by rfl) ⟨2317001, by rfl⟩ : syracuseStep 3089335 = 4634003) B4634003
theorem B500679 : Blo 499793 500679 := bstep (se 1 (by rfl) ⟨375509, by rfl⟩ : syracuseStep 500679 = 751019) B751019
theorem B500699 : Blo 499793 500699 := bstep (se 1 (by rfl) ⟨375524, by rfl⟩ : syracuseStep 500699 = 751049) B751049
theorem B500775 : Blo 499793 500775 := bstep (se 1 (by rfl) ⟨375581, by rfl⟩ : syracuseStep 500775 = 751163) B751163
theorem B566311 : Blo 499793 566311 := bstep (se 1 (by rfl) ⟨424733, by rfl⟩ : syracuseStep 566311 = 849467) B849467
theorem B500815 : Blo 499793 500815 := bstep (se 1 (by rfl) ⟨375611, by rfl⟩ : syracuseStep 500815 = 751223) B751223
theorem B500831 : Blo 499793 500831 := bstep (se 1 (by rfl) ⟨375623, by rfl⟩ : syracuseStep 500831 = 751247) B751247
theorem B500859 : Blo 499793 500859 := bstep (se 1 (by rfl) ⟨375644, by rfl⟩ : syracuseStep 500859 = 751289) B751289
theorem B500911 : Blo 499793 500911 := bstep (se 1 (by rfl) ⟨375683, by rfl⟩ : syracuseStep 500911 = 751367) B751367
theorem B2139331 : Blo 499793 2139331 := bstep (se 1 (by rfl) ⟨1604498, by rfl⟩ : syracuseStep 2139331 = 3208997) B3208997
theorem B500935 : Blo 499793 500935 := bstep (se 1 (by rfl) ⟨375701, by rfl⟩ : syracuseStep 500935 = 751403) B751403
theorem B29664461 : Blo 499793 29664461 := bstep (se 3 (by rfl) ⟨5562086, by rfl⟩ : syracuseStep 29664461 = 11124173) B11124173
theorem B500955 : Blo 499793 500955 := bstep (se 1 (by rfl) ⟨375716, by rfl⟩ : syracuseStep 500955 = 751433) B751433
theorem B501031 : Blo 499793 501031 := bstep (se 1 (by rfl) ⟨375773, by rfl⟩ : syracuseStep 501031 = 751547) B751547
theorem B501071 : Blo 499793 501071 := bstep (se 1 (by rfl) ⟨375803, by rfl⟩ : syracuseStep 501071 = 751607) B751607
theorem B501087 : Blo 499793 501087 := bstep (se 1 (by rfl) ⟨375815, by rfl⟩ : syracuseStep 501087 = 751631) B751631
theorem B501115 : Blo 499793 501115 := bstep (se 1 (by rfl) ⟨375836, by rfl⟩ : syracuseStep 501115 = 751673) B751673
theorem B3810725 : Blo 499793 3810725 := bstep (se 4 (by rfl) ⟨357255, by rfl⟩ : syracuseStep 3810725 = 714511) B714511
theorem B501167 : Blo 499793 501167 := bstep (se 1 (by rfl) ⟨375875, by rfl⟩ : syracuseStep 501167 = 751751) B751751
theorem B501191 : Blo 499793 501191 := bstep (se 1 (by rfl) ⟨375893, by rfl⟩ : syracuseStep 501191 = 751787) B751787
theorem B501211 : Blo 499793 501211 := bstep (se 1 (by rfl) ⟨375908, by rfl⟩ : syracuseStep 501211 = 751817) B751817
theorem B501287 : Blo 499793 501287 := bstep (se 1 (by rfl) ⟨375965, by rfl⟩ : syracuseStep 501287 = 751931) B751931
theorem B501327 : Blo 499793 501327 := bstep (se 1 (by rfl) ⟨375995, by rfl⟩ : syracuseStep 501327 = 751991) B751991
theorem B501343 : Blo 499793 501343 := bstep (se 1 (by rfl) ⟨376007, by rfl⟩ : syracuseStep 501343 = 752015) B752015
theorem B48801379 : Blo 499793 48801379 := bstep (se 1 (by rfl) ⟨36601034, by rfl⟩ : syracuseStep 48801379 = 73202069) B73202069
theorem B501371 : Blo 499793 501371 := bstep (se 1 (by rfl) ⟨376028, by rfl⟩ : syracuseStep 501371 = 752057) B752057
theorem B501423 : Blo 499793 501423 := bstep (se 1 (by rfl) ⟨376067, by rfl⟩ : syracuseStep 501423 = 752135) B752135
theorem B501447 : Blo 499793 501447 := bstep (se 1 (by rfl) ⟨376085, by rfl⟩ : syracuseStep 501447 = 752171) B752171
theorem B501467 : Blo 499793 501467 := bstep (se 1 (by rfl) ⟨376100, by rfl⟩ : syracuseStep 501467 = 752201) B752201
theorem B2827997 : Blo 499793 2827997 := bstep (se 3 (by rfl) ⟨530249, by rfl⟩ : syracuseStep 2827997 = 1060499) B1060499
theorem B501543 : Blo 499793 501543 := bstep (se 1 (by rfl) ⟨376157, by rfl⟩ : syracuseStep 501543 = 752315) B752315
theorem B501583 : Blo 499793 501583 := bstep (se 1 (by rfl) ⟨376187, by rfl⟩ : syracuseStep 501583 = 752375) B752375
theorem B501599 : Blo 499793 501599 := bstep (se 1 (by rfl) ⟨376199, by rfl⟩ : syracuseStep 501599 = 752399) B752399
theorem B501627 : Blo 499793 501627 := bstep (se 1 (by rfl) ⟨376220, by rfl⟩ : syracuseStep 501627 = 752441) B752441
theorem B501679 : Blo 499793 501679 := bstep (se 1 (by rfl) ⟨376259, by rfl⟩ : syracuseStep 501679 = 752519) B752519
theorem B1451963 : Blo 499793 1451963 := bstep (se 1 (by rfl) ⟨1088972, by rfl⟩ : syracuseStep 1451963 = 2177945) B2177945
theorem B501703 : Blo 499793 501703 := bstep (se 1 (by rfl) ⟨376277, by rfl⟩ : syracuseStep 501703 = 752555) B752555
theorem B501723 : Blo 499793 501723 := bstep (se 1 (by rfl) ⟨376292, by rfl⟩ : syracuseStep 501723 = 752585) B752585
theorem B54929411 : Blo 499793 54929411 := bstep (se 1 (by rfl) ⟨41197058, by rfl⟩ : syracuseStep 54929411 = 82394117) B82394117
theorem B4270117 : Blo 499793 4270117 := bstep (se 4 (by rfl) ⟨400323, by rfl⟩ : syracuseStep 4270117 = 800647) B800647
theorem B501799 : Blo 499793 501799 := bstep (se 1 (by rfl) ⟨376349, by rfl⟩ : syracuseStep 501799 = 752699) B752699
theorem B501839 : Blo 499793 501839 := bstep (se 1 (by rfl) ⟨376379, by rfl⟩ : syracuseStep 501839 = 752759) B752759
theorem B6432857 : Blo 499793 6432857 := bstep (se 2 (by rfl) ⟨2412321, by rfl⟩ : syracuseStep 6432857 = 4824643) B4824643
theorem B501855 : Blo 499793 501855 := bstep (se 1 (by rfl) ⟨376391, by rfl⟩ : syracuseStep 501855 = 752783) B752783
theorem B501883 : Blo 499793 501883 := bstep (se 1 (by rfl) ⟨376412, by rfl⟩ : syracuseStep 501883 = 752825) B752825
theorem B501935 : Blo 499793 501935 := bstep (se 1 (by rfl) ⟨376451, by rfl⟩ : syracuseStep 501935 = 752903) B752903
theorem B501959 : Blo 499793 501959 := bstep (se 1 (by rfl) ⟨376469, by rfl⟩ : syracuseStep 501959 = 752939) B752939
theorem B501979 : Blo 499793 501979 := bstep (se 1 (by rfl) ⟨376484, by rfl⟩ : syracuseStep 501979 = 752969) B752969
theorem B502055 : Blo 499793 502055 := bstep (se 1 (by rfl) ⟨376541, by rfl⟩ : syracuseStep 502055 = 753083) B753083
theorem B502095 : Blo 499793 502095 := bstep (se 1 (by rfl) ⟨376571, by rfl⟩ : syracuseStep 502095 = 753143) B753143
theorem B502111 : Blo 499793 502111 := bstep (se 1 (by rfl) ⟨376583, by rfl⟩ : syracuseStep 502111 = 753167) B753167
theorem B502139 : Blo 499793 502139 := bstep (se 1 (by rfl) ⟨376604, by rfl⟩ : syracuseStep 502139 = 753209) B753209
theorem B502191 : Blo 499793 502191 := bstep (se 1 (by rfl) ⟨376643, by rfl⟩ : syracuseStep 502191 = 753287) B753287
theorem B502215 : Blo 499793 502215 := bstep (se 1 (by rfl) ⟨376661, by rfl⟩ : syracuseStep 502215 = 753323) B753323
theorem B502235 : Blo 499793 502235 := bstep (se 1 (by rfl) ⟨376676, by rfl⟩ : syracuseStep 502235 = 753353) B753353
theorem B1124873 : Blo 499793 1124873 := bstep (se 2 (by rfl) ⟨421827, by rfl⟩ : syracuseStep 1124873 = 843655) B843655
theorem B502311 : Blo 499793 502311 := bstep (se 1 (by rfl) ⟨376733, by rfl⟩ : syracuseStep 502311 = 753467) B753467
theorem B502351 : Blo 499793 502351 := bstep (se 1 (by rfl) ⟨376763, by rfl⟩ : syracuseStep 502351 = 753527) B753527
theorem B502367 : Blo 499793 502367 := bstep (se 1 (by rfl) ⟨376775, by rfl⟩ : syracuseStep 502367 = 753551) B753551
theorem B502395 : Blo 499793 502395 := bstep (se 1 (by rfl) ⟨376796, by rfl⟩ : syracuseStep 502395 = 753593) B753593
theorem B502447 : Blo 499793 502447 := bstep (se 1 (by rfl) ⟨376835, by rfl⟩ : syracuseStep 502447 = 753671) B753671
theorem B502471 : Blo 499793 502471 := bstep (se 1 (by rfl) ⟨376853, by rfl⟩ : syracuseStep 502471 = 753707) B753707
theorem B502491 : Blo 499793 502491 := bstep (se 1 (by rfl) ⟨376868, by rfl⟩ : syracuseStep 502491 = 753737) B753737
theorem B1911545 : Blo 499793 1911545 := bstep (se 2 (by rfl) ⟨716829, by rfl⟩ : syracuseStep 1911545 = 1433659) B1433659
theorem B502567 : Blo 499793 502567 := bstep (se 1 (by rfl) ⟨376925, by rfl⟩ : syracuseStep 502567 = 753851) B753851
theorem B502607 : Blo 499793 502607 := bstep (se 1 (by rfl) ⟨376955, by rfl⟩ : syracuseStep 502607 = 753911) B753911
theorem B1125215 : Blo 499793 1125215 := bstep (se 1 (by rfl) ⟨843911, by rfl⟩ : syracuseStep 1125215 = 1687823) B1687823
theorem B502623 : Blo 499793 502623 := bstep (se 1 (by rfl) ⟨376967, by rfl⟩ : syracuseStep 502623 = 753935) B753935
theorem B502651 : Blo 499793 502651 := bstep (se 1 (by rfl) ⟨376988, by rfl⟩ : syracuseStep 502651 = 753977) B753977
theorem B502703 : Blo 499793 502703 := bstep (se 1 (by rfl) ⟨377027, by rfl⟩ : syracuseStep 502703 = 754055) B754055
theorem B2534327 : Blo 499793 2534327 := bstep (se 1 (by rfl) ⟨1900745, by rfl⟩ : syracuseStep 2534327 = 3801491) B3801491
theorem B502727 : Blo 499793 502727 := bstep (se 1 (by rfl) ⟨377045, by rfl⟩ : syracuseStep 502727 = 754091) B754091
theorem B502747 : Blo 499793 502747 := bstep (se 1 (by rfl) ⟨377060, by rfl⟩ : syracuseStep 502747 = 754121) B754121
theorem B1125395 : Blo 499793 1125395 := bstep (se 1 (by rfl) ⟨844046, by rfl⟩ : syracuseStep 1125395 = 1688093) B1688093
theorem B502823 : Blo 499793 502823 := bstep (se 1 (by rfl) ⟨377117, by rfl⟩ : syracuseStep 502823 = 754235) B754235
theorem B502863 : Blo 499793 502863 := bstep (se 1 (by rfl) ⟨377147, by rfl⟩ : syracuseStep 502863 = 754295) B754295
theorem B502879 : Blo 499793 502879 := bstep (se 1 (by rfl) ⟨377159, by rfl⟩ : syracuseStep 502879 = 754319) B754319
theorem B502907 : Blo 499793 502907 := bstep (se 1 (by rfl) ⟨377180, by rfl⟩ : syracuseStep 502907 = 754361) B754361
theorem B502959 : Blo 499793 502959 := bstep (se 1 (by rfl) ⟨377219, by rfl⟩ : syracuseStep 502959 = 754439) B754439
theorem B502983 : Blo 499793 502983 := bstep (se 1 (by rfl) ⟨377237, by rfl⟩ : syracuseStep 502983 = 754475) B754475
theorem B503003 : Blo 499793 503003 := bstep (se 1 (by rfl) ⟨377252, by rfl⟩ : syracuseStep 503003 = 754505) B754505
theorem B503079 : Blo 499793 503079 := bstep (se 1 (by rfl) ⟨377309, by rfl⟩ : syracuseStep 503079 = 754619) B754619
theorem B503119 : Blo 499793 503119 := bstep (se 1 (by rfl) ⟨377339, by rfl⟩ : syracuseStep 503119 = 754679) B754679
theorem B503135 : Blo 499793 503135 := bstep (se 1 (by rfl) ⟨377351, by rfl⟩ : syracuseStep 503135 = 754703) B754703
theorem B1125737 : Blo 499793 1125737 := bstep (se 2 (by rfl) ⟨422151, by rfl⟩ : syracuseStep 1125737 = 844303) B844303
theorem B503163 : Blo 499793 503163 := bstep (se 1 (by rfl) ⟨377372, by rfl⟩ : syracuseStep 503163 = 754745) B754745
theorem B503215 : Blo 499793 503215 := bstep (se 1 (by rfl) ⟨377411, by rfl⟩ : syracuseStep 503215 = 754823) B754823
theorem B503239 : Blo 499793 503239 := bstep (se 1 (by rfl) ⟨377429, by rfl⟩ : syracuseStep 503239 = 754859) B754859
theorem B634331 : Blo 499793 634331 := bstep (se 1 (by rfl) ⟨475748, by rfl⟩ : syracuseStep 634331 = 951497) B951497
theorem B503259 : Blo 499793 503259 := bstep (se 1 (by rfl) ⟨377444, by rfl⟩ : syracuseStep 503259 = 754889) B754889
theorem B503335 : Blo 499793 503335 := bstep (se 1 (by rfl) ⟨377501, by rfl⟩ : syracuseStep 503335 = 755003) B755003
theorem B503375 : Blo 499793 503375 := bstep (se 1 (by rfl) ⟨377531, by rfl⟩ : syracuseStep 503375 = 755063) B755063
theorem B503391 : Blo 499793 503391 := bstep (se 1 (by rfl) ⟨377543, by rfl⟩ : syracuseStep 503391 = 755087) B755087
theorem B503419 : Blo 499793 503419 := bstep (se 1 (by rfl) ⟨377564, by rfl⟩ : syracuseStep 503419 = 755129) B755129
theorem B503471 : Blo 499793 503471 := bstep (se 1 (by rfl) ⟨377603, by rfl⟩ : syracuseStep 503471 = 755207) B755207
theorem B503495 : Blo 499793 503495 := bstep (se 1 (by rfl) ⟨377621, by rfl⟩ : syracuseStep 503495 = 755243) B755243
theorem B1912531 : Blo 499793 1912531 := bstep (se 1 (by rfl) ⟨1434398, by rfl⟩ : syracuseStep 1912531 = 2868797) B2868797
theorem B503515 : Blo 499793 503515 := bstep (se 1 (by rfl) ⟨377636, by rfl⟩ : syracuseStep 503515 = 755273) B755273
theorem B503591 : Blo 499793 503591 := bstep (se 1 (by rfl) ⟨377693, by rfl⟩ : syracuseStep 503591 = 755387) B755387
theorem B503631 : Blo 499793 503631 := bstep (se 1 (by rfl) ⟨377723, by rfl⟩ : syracuseStep 503631 = 755447) B755447
theorem B503647 : Blo 499793 503647 := bstep (se 1 (by rfl) ⟨377735, by rfl⟩ : syracuseStep 503647 = 755471) B755471
theorem B503675 : Blo 499793 503675 := bstep (se 1 (by rfl) ⟨377756, by rfl⟩ : syracuseStep 503675 = 755513) B755513
theorem B503727 : Blo 499793 503727 := bstep (se 1 (by rfl) ⟨377795, by rfl⟩ : syracuseStep 503727 = 755591) B755591
theorem B634807 : Blo 499793 634807 := bstep (se 1 (by rfl) ⟨476105, by rfl⟩ : syracuseStep 634807 = 952211) B952211
theorem B1126331 : Blo 499793 1126331 := bstep (se 1 (by rfl) ⟨844748, by rfl⟩ : syracuseStep 1126331 = 1689497) B1689497
theorem B503751 : Blo 499793 503751 := bstep (se 1 (by rfl) ⟨377813, by rfl⟩ : syracuseStep 503751 = 755627) B755627
theorem B503771 : Blo 499793 503771 := bstep (se 1 (by rfl) ⟨377828, by rfl⟩ : syracuseStep 503771 = 755657) B755657
theorem B1126457 : Blo 499793 1126457 := bstep (se 2 (by rfl) ⟨422421, by rfl⟩ : syracuseStep 1126457 = 844843) B844843
theorem B2240627 : Blo 499793 2240627 := bstep (se 1 (by rfl) ⟨1680470, by rfl⟩ : syracuseStep 2240627 = 3360941) B3360941
theorem B2863421 : Blo 499793 2863421 := bstep (se 3 (by rfl) ⟨536891, by rfl⟩ : syracuseStep 2863421 = 1073783) B1073783
theorem B2535785 : Blo 499793 2535785 := bstep (se 2 (by rfl) ⟨950919, by rfl⟩ : syracuseStep 2535785 = 1901839) B1901839
theorem B1126799 : Blo 499793 1126799 := bstep (se 1 (by rfl) ⟨845099, by rfl⟩ : syracuseStep 1126799 = 1690199) B1690199
theorem B4272851 : Blo 499793 4272851 := bstep (se 1 (by rfl) ⟨3204638, by rfl⟩ : syracuseStep 4272851 = 6409277) B6409277
theorem B1127123 : Blo 499793 1127123 := bstep (se 1 (by rfl) ⟨845342, by rfl⟩ : syracuseStep 1127123 = 1690685) B1690685
theorem B14496529 : Blo 499793 14496529 := bstep (se 2 (by rfl) ⟨5436198, by rfl⟩ : syracuseStep 14496529 = 10872397) B10872397
theorem B9679661 : Blo 499793 9679661 := bstep (se 3 (by rfl) ⟨1814936, by rfl⟩ : syracuseStep 9679661 = 3629873) B3629873
theorem B963641 : Blo 499793 963641 := bstep (se 2 (by rfl) ⟨361365, by rfl⟩ : syracuseStep 963641 = 722731) B722731
theorem B8107073 : Blo 499793 8107073 := bstep (se 2 (by rfl) ⟨3040152, by rfl⟩ : syracuseStep 8107073 = 6080305) B6080305
theorem B636103 : Blo 499793 636103 := bstep (se 1 (by rfl) ⟨477077, by rfl⟩ : syracuseStep 636103 = 954155) B954155
theorem B963833 : Blo 499793 963833 := bstep (se 2 (by rfl) ⟨361437, by rfl⟩ : syracuseStep 963833 = 722875) B722875
theorem B5813765 : Blo 499793 5813765 := bstep (se 4 (by rfl) ⟨545040, by rfl⟩ : syracuseStep 5813765 = 1090081) B1090081
theorem B1128059 : Blo 499793 1128059 := bstep (se 1 (by rfl) ⟨846044, by rfl⟩ : syracuseStep 1128059 = 1692089) B1692089
theorem B1128185 : Blo 499793 1128185 := bstep (se 2 (by rfl) ⟨423069, by rfl⟩ : syracuseStep 1128185 = 846139) B846139
theorem B1128455 : Blo 499793 1128455 := bstep (se 1 (by rfl) ⟨846341, by rfl⟩ : syracuseStep 1128455 = 1692683) B1692683
theorem B1128527 : Blo 499793 1128527 := bstep (se 1 (by rfl) ⟨846395, by rfl⟩ : syracuseStep 1128527 = 1692791) B1692791
theorem B3225757 : Blo 499793 3225757 := bstep (se 3 (by rfl) ⟨604829, by rfl⟩ : syracuseStep 3225757 = 1209659) B1209659
theorem B1128923 : Blo 499793 1128923 := bstep (se 1 (by rfl) ⟨846692, by rfl⟩ : syracuseStep 1128923 = 1693385) B1693385
theorem B3816071 : Blo 499793 3816071 := bstep (se 1 (by rfl) ⟨2862053, by rfl⟩ : syracuseStep 3816071 = 5724107) B5724107
theorem B52312949 : Blo 499793 52312949 := bstep (se 5 (by rfl) ⟨2452169, by rfl⟩ : syracuseStep 52312949 = 4904339) B4904339
theorem B1129391 : Blo 499793 1129391 := bstep (se 1 (by rfl) ⟨847043, by rfl⟩ : syracuseStep 1129391 = 1694087) B1694087
theorem B1129643 : Blo 499793 1129643 := bstep (se 1 (by rfl) ⟨847232, by rfl⟩ : syracuseStep 1129643 = 1694465) B1694465
theorem B1687175 : Blo 499793 1687175 := bstep (se 1 (by rfl) ⟨1265381, by rfl⟩ : syracuseStep 1687175 = 2530763) B2530763
theorem B1687229 : Blo 499793 1687229 := bstep (se 3 (by rfl) ⟨316355, by rfl⟩ : syracuseStep 1687229 = 632711) B632711
theorem B1130183 : Blo 499793 1130183 := bstep (se 1 (by rfl) ⟨847637, by rfl⟩ : syracuseStep 1130183 = 1695275) B1695275
theorem B2146115 : Blo 499793 2146115 := bstep (se 1 (by rfl) ⟨1609586, by rfl⟩ : syracuseStep 2146115 = 3219173) B3219173
theorem B1687391 : Blo 499793 1687391 := bstep (se 1 (by rfl) ⟨1265543, by rfl⟩ : syracuseStep 1687391 = 2531087) B2531087
theorem B9912179 : Blo 499793 9912179 := bstep (se 1 (by rfl) ⟨7434134, by rfl⟩ : syracuseStep 9912179 = 14868269) B14868269
theorem B2703223 : Blo 499793 2703223 := bstep (se 1 (by rfl) ⟨2027417, by rfl⟩ : syracuseStep 2703223 = 4054835) B4054835
theorem B1687553 : Blo 499793 1687553 := bstep (se 2 (by rfl) ⟨632832, by rfl⟩ : syracuseStep 1687553 = 1265665) B1265665
theorem B3817529 : Blo 499793 3817529 := bstep (se 2 (by rfl) ⟨1431573, by rfl⟩ : syracuseStep 3817529 = 2863147) B2863147
theorem B2179153 : Blo 499793 2179153 := bstep (se 2 (by rfl) ⟨817182, by rfl⟩ : syracuseStep 2179153 = 1634365) B1634365
theorem B967099 : Blo 499793 967099 := bstep (se 1 (by rfl) ⟨725324, by rfl⟩ : syracuseStep 967099 = 1450649) B1450649
theorem B1131047 : Blo 499793 1131047 := bstep (se 1 (by rfl) ⟨848285, by rfl⟩ : syracuseStep 1131047 = 1696571) B1696571
theorem B1721021 : Blo 499793 1721021 := bstep (se 3 (by rfl) ⟨322691, by rfl⟩ : syracuseStep 1721021 = 645383) B645383
theorem B1688363 : Blo 499793 1688363 := bstep (se 1 (by rfl) ⟨1266272, by rfl⟩ : syracuseStep 1688363 = 2532545) B2532545
theorem B1983275 : Blo 499793 1983275 := bstep (se 1 (by rfl) ⟨1487456, by rfl⟩ : syracuseStep 1983275 = 2974913) B2974913
theorem B1131371 : Blo 499793 1131371 := bstep (se 1 (by rfl) ⟨848528, by rfl⟩ : syracuseStep 1131371 = 1697057) B1697057
theorem B1131425 : Blo 499793 1131425 := bstep (se 2 (by rfl) ⟨424284, by rfl⟩ : syracuseStep 1131425 = 848569) B848569
theorem B3490781 : Blo 499793 3490781 := bstep (se 3 (by rfl) ⟨654521, by rfl⟩ : syracuseStep 3490781 = 1309043) B1309043
theorem B6439985 : Blo 499793 6439985 := bstep (se 2 (by rfl) ⟨2414994, by rfl⟩ : syracuseStep 6439985 = 4829989) B4829989
theorem B1688633 : Blo 499793 1688633 := bstep (se 2 (by rfl) ⟨633237, by rfl⟩ : syracuseStep 1688633 = 1266475) B1266475
theorem B902315 : Blo 499793 902315 := bstep (se 1 (by rfl) ⟨676736, by rfl⟩ : syracuseStep 902315 = 1353473) B1353473
theorem B1131767 : Blo 499793 1131767 := bstep (se 1 (by rfl) ⟨848825, by rfl⟩ : syracuseStep 1131767 = 1697651) B1697651
theorem B1688957 : Blo 499793 1688957 := bstep (se 3 (by rfl) ⟨316679, by rfl⟩ : syracuseStep 1688957 = 633359) B633359
theorem B1689227 : Blo 499793 1689227 := bstep (se 1 (by rfl) ⟨1266920, by rfl⟩ : syracuseStep 1689227 = 2533841) B2533841
theorem B2148029 : Blo 499793 2148029 := bstep (se 3 (by rfl) ⟨402755, by rfl⟩ : syracuseStep 2148029 = 805511) B805511
theorem B1132361 : Blo 499793 1132361 := bstep (se 2 (by rfl) ⟨424635, by rfl⟩ : syracuseStep 1132361 = 849271) B849271
theorem B3622751 : Blo 499793 3622751 := bstep (se 1 (by rfl) ⟨2717063, by rfl⟩ : syracuseStep 3622751 = 5434127) B5434127
theorem B3819473 : Blo 499793 3819473 := bstep (se 2 (by rfl) ⟨1432302, by rfl⟩ : syracuseStep 3819473 = 2864605) B2864605
theorem B1624079 : Blo 499793 1624079 := bstep (se 1 (by rfl) ⟨1218059, by rfl⟩ : syracuseStep 1624079 = 2436119) B2436119
theorem B2410553 : Blo 499793 2410553 := bstep (se 2 (by rfl) ⟨903957, by rfl⟩ : syracuseStep 2410553 = 1807915) B1807915
theorem B30951517 : Blo 499793 30951517 := bstep (se 3 (by rfl) ⟨5803409, by rfl⟩ : syracuseStep 30951517 = 11606819) B11606819
theorem B968915 : Blo 499793 968915 := bstep (se 1 (by rfl) ⟨726686, by rfl⟩ : syracuseStep 968915 = 1453373) B1453373
theorem B2148713 : Blo 499793 2148713 := bstep (se 2 (by rfl) ⟨805767, by rfl⟩ : syracuseStep 2148713 = 1611535) B1611535
theorem B1526159 : Blo 499793 1526159 := bstep (se 1 (by rfl) ⟨1144619, by rfl⟩ : syracuseStep 1526159 = 2289239) B2289239
theorem B1690145 : Blo 499793 1690145 := bstep (se 2 (by rfl) ⟨633804, by rfl⟩ : syracuseStep 1690145 = 1267609) B1267609
theorem B1133153 : Blo 499793 1133153 := bstep (se 2 (by rfl) ⟨424932, by rfl⟩ : syracuseStep 1133153 = 849865) B849865
theorem B2542265 : Blo 499793 2542265 := bstep (se 2 (by rfl) ⟨953349, by rfl⟩ : syracuseStep 2542265 = 1906699) B1906699
theorem B1690361 : Blo 499793 1690361 := bstep (se 2 (by rfl) ⟨633885, by rfl⟩ : syracuseStep 1690361 = 1267771) B1267771
theorem B904031 : Blo 499793 904031 := bstep (se 1 (by rfl) ⟨678023, by rfl⟩ : syracuseStep 904031 = 1356047) B1356047
theorem B1133495 : Blo 499793 1133495 := bstep (se 1 (by rfl) ⟨850121, by rfl⟩ : syracuseStep 1133495 = 1700243) B1700243
theorem B1690631 : Blo 499793 1690631 := bstep (se 1 (by rfl) ⟨1267973, by rfl⟩ : syracuseStep 1690631 = 2535947) B2535947
theorem B1690739 : Blo 499793 1690739 := bstep (se 1 (by rfl) ⟨1268054, by rfl⟩ : syracuseStep 1690739 = 2536109) B2536109
theorem B1691009 : Blo 499793 1691009 := bstep (se 2 (by rfl) ⟨634128, by rfl⟩ : syracuseStep 1691009 = 1268257) B1268257
theorem B3624365 : Blo 499793 3624365 := bstep (se 3 (by rfl) ⟨679568, by rfl⟩ : syracuseStep 3624365 = 1359137) B1359137
theorem B2411977 : Blo 499793 2411977 := bstep (se 2 (by rfl) ⟨904491, by rfl⟩ : syracuseStep 2411977 = 1808983) B1808983
theorem B806363 : Blo 499793 806363 := bstep (se 1 (by rfl) ⟨604772, by rfl⟩ : syracuseStep 806363 = 1209545) B1209545
theorem B1265291 : Blo 499793 1265291 := bstep (se 1 (by rfl) ⟨948968, by rfl⟩ : syracuseStep 1265291 = 1897937) B1897937
theorem B2150027 : Blo 499793 2150027 := bstep (se 1 (by rfl) ⟨1612520, by rfl⟩ : syracuseStep 2150027 = 3225041) B3225041
theorem B3428029 : Blo 499793 3428029 := bstep (se 3 (by rfl) ⟨642755, by rfl⟩ : syracuseStep 3428029 = 1285511) B1285511
theorem B1265503 : Blo 499793 1265503 := bstep (se 1 (by rfl) ⟨949127, by rfl⟩ : syracuseStep 1265503 = 1898255) B1898255
theorem B2936737 : Blo 499793 2936737 := bstep (se 2 (by rfl) ⟨1101276, by rfl⟩ : syracuseStep 2936737 = 2202553) B2202553
theorem B1691819 : Blo 499793 1691819 := bstep (se 1 (by rfl) ⟨1268864, by rfl⟩ : syracuseStep 1691819 = 2537729) B2537729
theorem B26726597 : Blo 499793 26726597 := bstep (se 4 (by rfl) ⟨2505618, by rfl⟩ : syracuseStep 26726597 = 5011237) B5011237
theorem B1429751 : Blo 499793 1429751 := bstep (se 1 (by rfl) ⟨1072313, by rfl⟩ : syracuseStep 1429751 = 2144627) B2144627
theorem B5722649 : Blo 499793 5722649 := bstep (se 2 (by rfl) ⟨2145993, by rfl⟩ : syracuseStep 5722649 = 4291987) B4291987
theorem B1692359 : Blo 499793 1692359 := bstep (se 1 (by rfl) ⟨1269269, by rfl⟩ : syracuseStep 1692359 = 2538539) B2538539
theorem B1266425 : Blo 499793 1266425 := bstep (se 2 (by rfl) ⟨474909, by rfl⟩ : syracuseStep 1266425 = 949819) B949819
theorem B906337 : Blo 499793 906337 := bstep (se 2 (by rfl) ⟨339876, by rfl⟩ : syracuseStep 906337 = 679753) B679753
theorem B1267073 : Blo 499793 1267073 := bstep (se 2 (by rfl) ⟨475152, by rfl⟩ : syracuseStep 1267073 = 950305) B950305
theorem B3626441 : Blo 499793 3626441 := bstep (se 2 (by rfl) ⟨1359915, by rfl⟩ : syracuseStep 3626441 = 2719831) B2719831
theorem B1693223 : Blo 499793 1693223 := bstep (se 1 (by rfl) ⟨1269917, by rfl⟩ : syracuseStep 1693223 = 2539835) B2539835
theorem B1693331 : Blo 499793 1693331 := bstep (se 1 (by rfl) ⟨1269998, by rfl⟩ : syracuseStep 1693331 = 2539997) B2539997
theorem B677575 : Blo 499793 677575 := bstep (se 1 (by rfl) ⟨508181, by rfl⟩ : syracuseStep 677575 = 1016363) B1016363
theorem B6084395 : Blo 499793 6084395 := bstep (se 1 (by rfl) ⟨4563296, by rfl⟩ : syracuseStep 6084395 = 9126593) B9126593
theorem B1693547 : Blo 499793 1693547 := bstep (se 1 (by rfl) ⟨1270160, by rfl⟩ : syracuseStep 1693547 = 2540321) B2540321
theorem B1693601 : Blo 499793 1693601 := bstep (se 2 (by rfl) ⟨635100, by rfl⟩ : syracuseStep 1693601 = 1270201) B1270201
theorem B36591587 : Blo 499793 36591587 := bstep (se 1 (by rfl) ⟨27443690, by rfl⟩ : syracuseStep 36591587 = 54887381) B54887381
theorem B4053149 : Blo 499793 4053149 := bstep (se 3 (by rfl) ⟨759965, by rfl⟩ : syracuseStep 4053149 = 1519931) B1519931
theorem B1267883 : Blo 499793 1267883 := bstep (se 1 (by rfl) ⟨950912, by rfl⟩ : syracuseStep 1267883 = 1901825) B1901825
theorem B678137 : Blo 499793 678137 := bstep (se 2 (by rfl) ⟨254301, by rfl⟩ : syracuseStep 678137 = 508603) B508603
theorem B5429591 : Blo 499793 5429591 := bstep (se 1 (by rfl) ⟨4072193, by rfl⟩ : syracuseStep 5429591 = 8144387) B8144387
theorem B1694195 : Blo 499793 1694195 := bstep (se 1 (by rfl) ⟨1270646, by rfl⟩ : syracuseStep 1694195 = 2541293) B2541293
theorem B1268743 : Blo 499793 1268743 := bstep (se 1 (by rfl) ⟨951557, by rfl⟩ : syracuseStep 1268743 = 1903115) B1903115
theorem B1694735 : Blo 499793 1694735 := bstep (se 1 (by rfl) ⟨1271051, by rfl⟩ : syracuseStep 1694735 = 2542103) B2542103
theorem B2579627 : Blo 499793 2579627 := bstep (se 1 (by rfl) ⟨1934720, by rfl⟩ : syracuseStep 2579627 = 3869441) B3869441
theorem B5725565 : Blo 499793 5725565 := bstep (se 3 (by rfl) ⟨1073543, by rfl⟩ : syracuseStep 5725565 = 2147087) B2147087
theorem B6413741 : Blo 499793 6413741 := bstep (se 3 (by rfl) ⟨1202576, by rfl⟩ : syracuseStep 6413741 = 2405153) B2405153
theorem B1695329 : Blo 499793 1695329 := bstep (se 2 (by rfl) ⟨635748, by rfl⟩ : syracuseStep 1695329 = 1271497) B1271497
theorem B2416225 : Blo 499793 2416225 := bstep (se 2 (by rfl) ⟨906084, by rfl⟩ : syracuseStep 2416225 = 1812169) B1812169
theorem B3858043 : Blo 499793 3858043 := bstep (se 1 (by rfl) ⟨2893532, by rfl⟩ : syracuseStep 3858043 = 5787065) B5787065
theorem B1269371 : Blo 499793 1269371 := bstep (se 1 (by rfl) ⟨952028, by rfl⟩ : syracuseStep 1269371 = 1904057) B1904057
theorem B1924823 : Blo 499793 1924823 := bstep (se 1 (by rfl) ⟨1443617, by rfl⟩ : syracuseStep 1924823 = 2887235) B2887235
theorem B2547449 : Blo 499793 2547449 := bstep (se 2 (by rfl) ⟨955293, by rfl⟩ : syracuseStep 2547449 = 1910587) B1910587
theorem B1236809 : Blo 499793 1236809 := bstep (se 2 (by rfl) ⟨463803, by rfl⟩ : syracuseStep 1236809 = 927607) B927607
theorem B1269665 : Blo 499793 1269665 := bstep (se 2 (by rfl) ⟨476124, by rfl⟩ : syracuseStep 1269665 = 952249) B952249
theorem B1073083 : Blo 499793 1073083 := bstep (se 1 (by rfl) ⟨804812, by rfl⟩ : syracuseStep 1073083 = 1609625) B1609625
theorem B1925201 : Blo 499793 1925201 := bstep (se 2 (by rfl) ⟨721950, by rfl⟩ : syracuseStep 1925201 = 1443901) B1443901
theorem B39739747 : Blo 499793 39739747 := bstep (se 1 (by rfl) ⟨29804810, by rfl⟩ : syracuseStep 39739747 = 59609621) B59609621
theorem B713065 : Blo 499793 713065 := bstep (se 2 (by rfl) ⟨267399, by rfl⟩ : syracuseStep 713065 = 534799) B534799
theorem B2548097 : Blo 499793 2548097 := bstep (se 2 (by rfl) ⟨955536, by rfl⟩ : syracuseStep 2548097 = 1911073) B1911073
theorem B844175 : Blo 499793 844175 := bstep (se 1 (by rfl) ⟨633131, by rfl⟩ : syracuseStep 844175 = 1266263) B1266263
theorem B844411 : Blo 499793 844411 := bstep (se 1 (by rfl) ⟨633308, by rfl⟩ : syracuseStep 844411 = 1266617) B1266617
theorem B1696787 : Blo 499793 1696787 := bstep (se 1 (by rfl) ⟨1272590, by rfl⟩ : syracuseStep 1696787 = 2545181) B2545181
theorem B4809881 : Blo 499793 4809881 := bstep (se 2 (by rfl) ⟨1803705, by rfl⟩ : syracuseStep 4809881 = 3607411) B3607411
theorem B2548907 : Blo 499793 2548907 := bstep (se 1 (by rfl) ⟨1911680, by rfl⟩ : syracuseStep 2548907 = 3823361) B3823361
theorem B1697111 : Blo 499793 1697111 := bstep (se 1 (by rfl) ⟨1272833, by rfl⟩ : syracuseStep 1697111 = 2545667) B2545667
theorem B5432741 : Blo 499793 5432741 := bstep (se 4 (by rfl) ⟨509319, by rfl⟩ : syracuseStep 5432741 = 1018639) B1018639
theorem B845275 : Blo 499793 845275 := bstep (se 1 (by rfl) ⟨633956, by rfl⟩ : syracuseStep 845275 = 1267913) B1267913
theorem B1271335 : Blo 499793 1271335 := bstep (se 1 (by rfl) ⟨953501, by rfl⟩ : syracuseStep 1271335 = 1907003) B1907003
theorem B2549393 : Blo 499793 2549393 := bstep (se 2 (by rfl) ⟨956022, by rfl⟩ : syracuseStep 2549393 = 1912045) B1912045
theorem B3204845 : Blo 499793 3204845 := bstep (se 3 (by rfl) ⟨600908, by rfl⟩ : syracuseStep 3204845 = 1201817) B1201817
theorem B1271659 : Blo 499793 1271659 := bstep (se 1 (by rfl) ⟨953744, by rfl⟩ : syracuseStep 1271659 = 1907489) B1907489
theorem B1206191 : Blo 499793 1206191 := bstep (se 1 (by rfl) ⟨904643, by rfl⟩ : syracuseStep 1206191 = 1809287) B1809287
theorem B1206199 : Blo 499793 1206199 := bstep (se 1 (by rfl) ⟨904649, by rfl⟩ : syracuseStep 1206199 = 1809299) B1809299
theorem B845903 : Blo 499793 845903 := bstep (se 1 (by rfl) ⟨634427, by rfl⟩ : syracuseStep 845903 = 1268855) B1268855
theorem B715115 : Blo 499793 715115 := bstep (se 1 (by rfl) ⟨536336, by rfl⟩ : syracuseStep 715115 = 1072673) B1072673
theorem B1698191 : Blo 499793 1698191 := bstep (se 1 (by rfl) ⟨1273643, by rfl⟩ : syracuseStep 1698191 = 2547287) B2547287
theorem B16214417 : Blo 499793 16214417 := bstep (se 2 (by rfl) ⟨6080406, by rfl⟩ : syracuseStep 16214417 = 12160813) B12160813
theorem B1272307 : Blo 499793 1272307 := bstep (se 1 (by rfl) ⟨954230, by rfl⟩ : syracuseStep 1272307 = 1908461) B1908461
theorem B1698515 : Blo 499793 1698515 := bstep (se 1 (by rfl) ⟨1273886, by rfl⟩ : syracuseStep 1698515 = 2547773) B2547773
theorem B846767 : Blo 499793 846767 := bstep (se 1 (by rfl) ⟨635075, by rfl⟩ : syracuseStep 846767 = 1270151) B1270151
theorem B1207315 : Blo 499793 1207315 := bstep (se 1 (by rfl) ⟨905486, by rfl⟩ : syracuseStep 1207315 = 1810973) B1810973
theorem B847199 : Blo 499793 847199 := bstep (se 1 (by rfl) ⟨635399, by rfl⟩ : syracuseStep 847199 = 1270799) B1270799
theorem B4287887 : Blo 499793 4287887 := bstep (se 1 (by rfl) ⟨3215915, by rfl⟩ : syracuseStep 4287887 = 6431831) B6431831
theorem B1273441 : Blo 499793 1273441 := bstep (se 2 (by rfl) ⟨477540, by rfl⟩ : syracuseStep 1273441 = 955081) B955081
theorem B1699703 : Blo 499793 1699703 := bstep (se 1 (by rfl) ⟨1274777, by rfl⟩ : syracuseStep 1699703 = 2549555) B2549555
theorem B847759 : Blo 499793 847759 := bstep (se 1 (by rfl) ⟨635819, by rfl⟩ : syracuseStep 847759 = 1271639) B1271639
theorem B9629603 : Blo 499793 9629603 := bstep (se 1 (by rfl) ⟨7222202, by rfl⟩ : syracuseStep 9629603 = 14444405) B14444405
theorem B1699919 : Blo 499793 1699919 := bstep (se 1 (by rfl) ⟨1274939, by rfl⟩ : syracuseStep 1699919 = 2549879) B2549879
theorem B4583587 : Blo 499793 4583587 := bstep (se 1 (by rfl) ⟨3437690, by rfl⟩ : syracuseStep 4583587 = 6875381) B6875381
theorem B9040187 : Blo 499793 9040187 := bstep (se 1 (by rfl) ⟨6780140, by rfl⟩ : syracuseStep 9040187 = 13560281) B13560281
theorem B520543 : Blo 499793 520543 := bstep (se 1 (by rfl) ⟨390407, by rfl⟩ : syracuseStep 520543 = 780815) B780815
theorem B881039 : Blo 499793 881039 := bstep (se 1 (by rfl) ⟨660779, by rfl⟩ : syracuseStep 881039 = 1321559) B1321559
theorem B749999 : Blo 499793 749999 := bstep (se 1 (by rfl) ⟨562499, by rfl⟩ : syracuseStep 749999 = 1124999) B1124999
theorem B1700297 : Blo 499793 1700297 := bstep (se 2 (by rfl) ⟨637611, by rfl⟩ : syracuseStep 1700297 = 1275223) B1275223
theorem B750089 : Blo 499793 750089 := bstep (se 2 (by rfl) ⟨281283, by rfl⟩ : syracuseStep 750089 = 562567) B562567
theorem B1274393 : Blo 499793 1274393 := bstep (se 2 (by rfl) ⟨477897, by rfl⟩ : syracuseStep 1274393 = 955795) B955795
theorem B750119 : Blo 499793 750119 := bstep (se 1 (by rfl) ⟨562589, by rfl⟩ : syracuseStep 750119 = 1125179) B1125179
theorem B848441 : Blo 499793 848441 := bstep (se 2 (by rfl) ⟨318165, by rfl⟩ : syracuseStep 848441 = 636331) B636331
theorem B750203 : Blo 499793 750203 := bstep (se 1 (by rfl) ⟨562652, by rfl⟩ : syracuseStep 750203 = 1125305) B1125305
theorem B3928787 : Blo 499793 3928787 := bstep (se 1 (by rfl) ⟨2946590, by rfl⟩ : syracuseStep 3928787 = 5893181) B5893181
theorem B750329 : Blo 499793 750329 := bstep (se 2 (by rfl) ⟨281373, by rfl⟩ : syracuseStep 750329 = 562747) B562747
theorem B1209161 : Blo 499793 1209161 := bstep (se 2 (by rfl) ⟨453435, by rfl⟩ : syracuseStep 1209161 = 906871) B906871
theorem B750431 : Blo 499793 750431 := bstep (se 1 (by rfl) ⟨562823, by rfl⟩ : syracuseStep 750431 = 1125647) B1125647
theorem B750443 : Blo 499793 750443 := bstep (se 1 (by rfl) ⟨562832, by rfl⟩ : syracuseStep 750443 = 1125665) B1125665
theorem B1274899 : Blo 499793 1274899 := bstep (se 1 (by rfl) ⟨956174, by rfl⟩ : syracuseStep 1274899 = 1912349) B1912349
theorem B750671 : Blo 499793 750671 := bstep (se 1 (by rfl) ⟨563003, by rfl⟩ : syracuseStep 750671 = 1126007) B1126007
theorem B750791 : Blo 499793 750791 := bstep (se 1 (by rfl) ⟨563093, by rfl⟩ : syracuseStep 750791 = 1126187) B1126187
theorem B849143 : Blo 499793 849143 := bstep (se 1 (by rfl) ⟨636857, by rfl⟩ : syracuseStep 849143 = 1273715) B1273715
theorem B1897739 : Blo 499793 1897739 := bstep (se 1 (by rfl) ⟨1423304, by rfl⟩ : syracuseStep 1897739 = 2846609) B2846609
theorem B750953 : Blo 499793 750953 := bstep (se 2 (by rfl) ⟨281607, by rfl⟩ : syracuseStep 750953 = 563215) B563215
theorem B751031 : Blo 499793 751031 := bstep (se 1 (by rfl) ⟨563273, by rfl⟩ : syracuseStep 751031 = 1126547) B1126547
theorem B751067 : Blo 499793 751067 := bstep (se 1 (by rfl) ⟨563300, by rfl⟩ : syracuseStep 751067 = 1126601) B1126601
theorem B849487 : Blo 499793 849487 := bstep (se 1 (by rfl) ⟨637115, by rfl⟩ : syracuseStep 849487 = 1274231) B1274231
theorem B5699321 : Blo 499793 5699321 := bstep (se 2 (by rfl) ⟨2137245, by rfl⟩ : syracuseStep 5699321 = 4274491) B4274491
theorem B4290347 : Blo 499793 4290347 := bstep (se 1 (by rfl) ⟨3217760, by rfl⟩ : syracuseStep 4290347 = 6435521) B6435521
theorem B849737 : Blo 499793 849737 := bstep (se 2 (by rfl) ⟨318651, by rfl⟩ : syracuseStep 849737 = 637303) B637303
theorem B3045215 : Blo 499793 3045215 := bstep (se 1 (by rfl) ⟨2283911, by rfl⟩ : syracuseStep 3045215 = 4567823) B4567823
theorem B751535 : Blo 499793 751535 := bstep (se 1 (by rfl) ⟨563651, by rfl⟩ : syracuseStep 751535 = 1127303) B1127303
theorem B1898423 : Blo 499793 1898423 := bstep (se 1 (by rfl) ⟨1423817, by rfl⟩ : syracuseStep 1898423 = 2847635) B2847635
theorem B2029495 : Blo 499793 2029495 := bstep (se 1 (by rfl) ⟨1522121, by rfl⟩ : syracuseStep 2029495 = 3044243) B3044243
theorem B1210295 : Blo 499793 1210295 := bstep (se 1 (by rfl) ⟨907721, by rfl⟩ : syracuseStep 1210295 = 1815443) B1815443
theorem B16316387 : Blo 499793 16316387 := bstep (se 1 (by rfl) ⟨12237290, by rfl⟩ : syracuseStep 16316387 = 24474581) B24474581
theorem B751625 : Blo 499793 751625 := bstep (se 2 (by rfl) ⟨281859, by rfl⟩ : syracuseStep 751625 = 563719) B563719
theorem B751655 : Blo 499793 751655 := bstep (se 1 (by rfl) ⟨563741, by rfl⟩ : syracuseStep 751655 = 1127483) B1127483
theorem B751739 : Blo 499793 751739 := bstep (se 1 (by rfl) ⟨563804, by rfl⟩ : syracuseStep 751739 = 1127609) B1127609
theorem B751865 : Blo 499793 751865 := bstep (se 2 (by rfl) ⟨281949, by rfl⟩ : syracuseStep 751865 = 563899) B563899
theorem B751967 : Blo 499793 751967 := bstep (se 1 (by rfl) ⟨563975, by rfl⟩ : syracuseStep 751967 = 1127951) B1127951
theorem B751979 : Blo 499793 751979 := bstep (se 1 (by rfl) ⟨563984, by rfl⟩ : syracuseStep 751979 = 1127969) B1127969
theorem B13728203 : Blo 499793 13728203 := bstep (se 1 (by rfl) ⟨10296152, by rfl⟩ : syracuseStep 13728203 = 20592305) B20592305
theorem B752207 : Blo 499793 752207 := bstep (se 1 (by rfl) ⟨564155, by rfl⟩ : syracuseStep 752207 = 1128311) B1128311
theorem B1899197 : Blo 499793 1899197 := bstep (se 3 (by rfl) ⟨356099, by rfl⟩ : syracuseStep 1899197 = 712199) B712199
theorem B752327 : Blo 499793 752327 := bstep (se 1 (by rfl) ⟨564245, by rfl⟩ : syracuseStep 752327 = 1128491) B1128491
theorem B949097 : Blo 499793 949097 := bstep (se 2 (by rfl) ⟨355911, by rfl⟩ : syracuseStep 949097 = 711823) B711823
theorem B752489 : Blo 499793 752489 := bstep (se 2 (by rfl) ⟨282183, by rfl⟩ : syracuseStep 752489 = 564367) B564367
theorem B752567 : Blo 499793 752567 := bstep (se 1 (by rfl) ⟨564425, by rfl⟩ : syracuseStep 752567 = 1128851) B1128851
theorem B752603 : Blo 499793 752603 := bstep (se 1 (by rfl) ⟨564452, by rfl⟩ : syracuseStep 752603 = 1128905) B1128905
theorem B2849843 : Blo 499793 2849843 := bstep (se 1 (by rfl) ⟨2137382, by rfl⟩ : syracuseStep 2849843 = 4274765) B4274765
theorem B1899881 : Blo 499793 1899881 := bstep (se 2 (by rfl) ⟨712455, by rfl⟩ : syracuseStep 1899881 = 1424911) B1424911
theorem B1015201 : Blo 499793 1015201 := bstep (se 2 (by rfl) ⟨380700, by rfl⟩ : syracuseStep 1015201 = 761401) B761401
theorem B753071 : Blo 499793 753071 := bstep (se 1 (by rfl) ⟨564803, by rfl⟩ : syracuseStep 753071 = 1129607) B1129607
theorem B753161 : Blo 499793 753161 := bstep (se 2 (by rfl) ⟨282435, by rfl⟩ : syracuseStep 753161 = 564871) B564871
theorem B753191 : Blo 499793 753191 := bstep (se 1 (by rfl) ⟨564893, by rfl⟩ : syracuseStep 753191 = 1129787) B1129787
theorem B1605217 : Blo 499793 1605217 := bstep (se 2 (by rfl) ⟨601956, by rfl⟩ : syracuseStep 1605217 = 1203913) B1203913
theorem B753275 : Blo 499793 753275 := bstep (se 1 (by rfl) ⟨564956, by rfl⟩ : syracuseStep 753275 = 1129913) B1129913
theorem B753401 : Blo 499793 753401 := bstep (se 2 (by rfl) ⟨282525, by rfl⟩ : syracuseStep 753401 = 565051) B565051
theorem B753503 : Blo 499793 753503 := bstep (se 1 (by rfl) ⟨565127, by rfl⟩ : syracuseStep 753503 = 1130255) B1130255
theorem B950123 : Blo 499793 950123 := bstep (se 1 (by rfl) ⟨712592, by rfl⟩ : syracuseStep 950123 = 1425185) B1425185
theorem B753515 : Blo 499793 753515 := bstep (se 1 (by rfl) ⟨565136, by rfl⟩ : syracuseStep 753515 = 1130273) B1130273
theorem B753929 : Blo 499793 753929 := bstep (se 2 (by rfl) ⟨282723, by rfl⟩ : syracuseStep 753929 = 565447) B565447
theorem B754031 : Blo 499793 754031 := bstep (se 1 (by rfl) ⟨565523, by rfl⟩ : syracuseStep 754031 = 1131047) B1131047
theorem B52986329 : Blo 499793 52986329 := bstep (se 2 (by rfl) ⟨19869873, by rfl⟩ : syracuseStep 52986329 = 39739747) B39739747
theorem B950753 : Blo 499793 950753 := bstep (se 2 (by rfl) ⟨356532, by rfl⟩ : syracuseStep 950753 = 713065) B713065
theorem B1376831 : Blo 499793 1376831 := bstep (se 1 (by rfl) ⟨1032623, by rfl⟩ : syracuseStep 1376831 = 2065247) B2065247
theorem B754247 : Blo 499793 754247 := bstep (se 1 (by rfl) ⟨565685, by rfl⟩ : syracuseStep 754247 = 1131371) B1131371
theorem B754283 : Blo 499793 754283 := bstep (se 1 (by rfl) ⟨565712, by rfl⟩ : syracuseStep 754283 = 1131425) B1131425
theorem B4293323 : Blo 499793 4293323 := bstep (se 1 (by rfl) ⟨3219992, by rfl⟩ : syracuseStep 4293323 = 6439985) B6439985
theorem B754511 : Blo 499793 754511 := bstep (se 1 (by rfl) ⟨565883, by rfl⟩ : syracuseStep 754511 = 1131767) B1131767
theorem B754907 : Blo 499793 754907 := bstep (se 1 (by rfl) ⟨566180, by rfl⟩ : syracuseStep 754907 = 1132361) B1132361
theorem B1082719 : Blo 499793 1082719 := bstep (se 1 (by rfl) ⟨812039, by rfl⟩ : syracuseStep 1082719 = 1624079) B1624079
theorem B1607035 : Blo 499793 1607035 := bstep (se 1 (by rfl) ⟨1205276, by rfl⟩ : syracuseStep 1607035 = 2410553) B2410553
theorem B755081 : Blo 499793 755081 := bstep (se 2 (by rfl) ⟨283155, by rfl⟩ : syracuseStep 755081 = 566311) B566311
theorem B2852441 : Blo 499793 2852441 := bstep (se 2 (by rfl) ⟨1069665, by rfl⟩ : syracuseStep 2852441 = 2139331) B2139331
theorem B3671687 : Blo 499793 3671687 := bstep (se 1 (by rfl) ⟨2753765, by rfl⟩ : syracuseStep 3671687 = 5507531) B5507531
theorem B755435 : Blo 499793 755435 := bstep (se 1 (by rfl) ⟨566576, by rfl⟩ : syracuseStep 755435 = 1133153) B1133153
theorem B4589389 : Blo 499793 4589389 := bstep (se 3 (by rfl) ⟨860510, by rfl⟩ : syracuseStep 4589389 = 1721021) B1721021
theorem B755663 : Blo 499793 755663 := bstep (se 1 (by rfl) ⟨566747, by rfl⟩ : syracuseStep 755663 = 1133495) B1133495
theorem B5703695 : Blo 499793 5703695 := bstep (se 1 (by rfl) ⟨4277771, by rfl⟩ : syracuseStep 5703695 = 8555543) B8555543
theorem B1608265 : Blo 499793 1608265 := bstep (se 2 (by rfl) ⟨603099, by rfl⟩ : syracuseStep 1608265 = 1206199) B1206199
theorem B1904087 : Blo 499793 1904087 := bstep (se 1 (by rfl) ⟨1428065, by rfl⟩ : syracuseStep 1904087 = 2856131) B2856131
theorem B659167 : Blo 499793 659167 := bstep (se 1 (by rfl) ⟨494375, by rfl⟩ : syracuseStep 659167 = 988751) B988751
theorem B1609753 : Blo 499793 1609753 := bstep (se 2 (by rfl) ⟨603657, by rfl⟩ : syracuseStep 1609753 = 1207315) B1207315
theorem B3215969 : Blo 499793 3215969 := bstep (se 2 (by rfl) ⟨1205988, by rfl⟩ : syracuseStep 3215969 = 2411977) B2411977
theorem B3216509 : Blo 499793 3216509 := bstep (se 3 (by rfl) ⟨603095, by rfl⟩ : syracuseStep 3216509 = 1206191) B1206191
theorem B1283215 : Blo 499793 1283215 := bstep (se 1 (by rfl) ⟨962411, by rfl⟩ : syracuseStep 1283215 = 1924823) B1924823
theorem B3871901 : Blo 499793 3871901 := bstep (se 3 (by rfl) ⟨725981, by rfl⟩ : syracuseStep 3871901 = 1451963) B1451963
theorem B562783 : Blo 499793 562783 := bstep (se 1 (by rfl) ⟨422087, by rfl⟩ : syracuseStep 562783 = 844175) B844175
theorem B694057 : Blo 499793 694057 := bstep (se 2 (by rfl) ⟨260271, by rfl⟩ : syracuseStep 694057 = 520543) B520543
theorem B1906487 : Blo 499793 1906487 := bstep (se 1 (by rfl) ⟨1429865, by rfl⟩ : syracuseStep 1906487 = 2859731) B2859731
theorem B1808365 : Blo 499793 1808365 := bstep (se 3 (by rfl) ⟨339068, by rfl⟩ : syracuseStep 1808365 = 678137) B678137
theorem B1906973 : Blo 499793 1906973 := bstep (se 3 (by rfl) ⟨357557, by rfl⟩ : syracuseStep 1906973 = 715115) B715115
theorem B4069757 : Blo 499793 4069757 := bstep (se 3 (by rfl) ⟨763079, by rfl⟩ : syracuseStep 4069757 = 1526159) B1526159
theorem B2136563 : Blo 499793 2136563 := bstep (se 1 (by rfl) ⟨1602422, by rfl⟩ : syracuseStep 2136563 = 3204845) B3204845
theorem B1710665 : Blo 499793 1710665 := bstep (se 2 (by rfl) ⟨641499, by rfl⟩ : syracuseStep 1710665 = 1282999) B1282999
theorem B563935 : Blo 499793 563935 := bstep (se 1 (by rfl) ⟨422951, by rfl⟩ : syracuseStep 563935 = 845903) B845903
theorem B3251117 : Blo 499793 3251117 := bstep (se 3 (by rfl) ⟨609584, by rfl⟩ : syracuseStep 3251117 = 1219169) B1219169
theorem B564511 : Blo 499793 564511 := bstep (se 1 (by rfl) ⟨423383, by rfl⟩ : syracuseStep 564511 = 846767) B846767
theorem B564799 : Blo 499793 564799 := bstep (se 1 (by rfl) ⟨423599, by rfl⟩ : syracuseStep 564799 = 847199) B847199
theorem B2858591 : Blo 499793 2858591 := bstep (se 1 (by rfl) ⟨2143943, by rfl⟩ : syracuseStep 2858591 = 4287887) B4287887
theorem B2530925 : Blo 499793 2530925 := bstep (se 3 (by rfl) ⟨474548, by rfl⟩ : syracuseStep 2530925 = 949097) B949097
theorem B4301009 : Blo 499793 4301009 := bstep (se 2 (by rfl) ⟨1612878, by rfl⟩ : syracuseStep 4301009 = 3225757) B3225757
theorem B1908947 : Blo 499793 1908947 := bstep (se 1 (by rfl) ⟨1431710, by rfl⟩ : syracuseStep 1908947 = 2863421) B2863421
theorem B499999 : Blo 499793 499999 := bstep (se 1 (by rfl) ⟨374999, by rfl⟩ : syracuseStep 499999 = 749999) B749999
theorem B500059 : Blo 499793 500059 := bstep (se 1 (by rfl) ⟨375044, by rfl⟩ : syracuseStep 500059 = 750089) B750089
theorem B500079 : Blo 499793 500079 := bstep (se 1 (by rfl) ⟨375059, by rfl⟩ : syracuseStep 500079 = 750119) B750119
theorem B565627 : Blo 499793 565627 := bstep (se 1 (by rfl) ⟨424220, by rfl⟩ : syracuseStep 565627 = 848441) B848441
theorem B500135 : Blo 499793 500135 := bstep (se 1 (by rfl) ⟨375101, by rfl⟩ : syracuseStep 500135 = 750203) B750203
theorem B500219 : Blo 499793 500219 := bstep (se 1 (by rfl) ⟨375164, by rfl⟩ : syracuseStep 500219 = 750329) B750329
theorem B500287 : Blo 499793 500287 := bstep (se 1 (by rfl) ⟨375215, by rfl⟩ : syracuseStep 500287 = 750431) B750431
theorem B500295 : Blo 499793 500295 := bstep (se 1 (by rfl) ⟨375221, by rfl⟩ : syracuseStep 500295 = 750443) B750443
theorem B500447 : Blo 499793 500447 := bstep (se 1 (by rfl) ⟨375335, by rfl⟩ : syracuseStep 500447 = 750671) B750671
theorem B500527 : Blo 499793 500527 := bstep (se 1 (by rfl) ⟨375395, by rfl⟩ : syracuseStep 500527 = 750791) B750791
theorem B566095 : Blo 499793 566095 := bstep (se 1 (by rfl) ⟨424571, by rfl⟩ : syracuseStep 566095 = 849143) B849143
theorem B500635 : Blo 499793 500635 := bstep (se 1 (by rfl) ⟨375476, by rfl⟩ : syracuseStep 500635 = 750953) B750953
theorem B500687 : Blo 499793 500687 := bstep (se 1 (by rfl) ⟨375515, by rfl⟩ : syracuseStep 500687 = 751031) B751031
theorem B500711 : Blo 499793 500711 := bstep (se 1 (by rfl) ⟨375533, by rfl⟩ : syracuseStep 500711 = 751067) B751067
theorem B3875843 : Blo 499793 3875843 := bstep (se 1 (by rfl) ⟨2906882, by rfl⟩ : syracuseStep 3875843 = 5813765) B5813765
theorem B2860231 : Blo 499793 2860231 := bstep (se 1 (by rfl) ⟨2145173, by rfl⟩ : syracuseStep 2860231 = 4290347) B4290347
theorem B566491 : Blo 499793 566491 := bstep (se 1 (by rfl) ⟨424868, by rfl⟩ : syracuseStep 566491 = 849737) B849737
theorem B501023 : Blo 499793 501023 := bstep (se 1 (by rfl) ⟨375767, by rfl⟩ : syracuseStep 501023 = 751535) B751535
theorem B501083 : Blo 499793 501083 := bstep (se 1 (by rfl) ⟨375812, by rfl⟩ : syracuseStep 501083 = 751625) B751625
theorem B501103 : Blo 499793 501103 := bstep (se 1 (by rfl) ⟨375827, by rfl⟩ : syracuseStep 501103 = 751655) B751655
theorem B501159 : Blo 499793 501159 := bstep (se 1 (by rfl) ⟨375869, by rfl⟩ : syracuseStep 501159 = 751739) B751739
theorem B501243 : Blo 499793 501243 := bstep (se 1 (by rfl) ⟨375932, by rfl⟩ : syracuseStep 501243 = 751865) B751865
theorem B501311 : Blo 499793 501311 := bstep (se 1 (by rfl) ⟨375983, by rfl⟩ : syracuseStep 501311 = 751967) B751967
theorem B501319 : Blo 499793 501319 := bstep (se 1 (by rfl) ⟨375989, by rfl⟩ : syracuseStep 501319 = 751979) B751979
theorem B9152135 : Blo 499793 9152135 := bstep (se 1 (by rfl) ⟨6864101, by rfl⟩ : syracuseStep 9152135 = 13728203) B13728203
theorem B501471 : Blo 499793 501471 := bstep (se 1 (by rfl) ⟨376103, by rfl⟩ : syracuseStep 501471 = 752207) B752207
theorem B501551 : Blo 499793 501551 := bstep (se 1 (by rfl) ⟨376163, by rfl⟩ : syracuseStep 501551 = 752327) B752327
theorem B1353601 : Blo 499793 1353601 := bstep (se 2 (by rfl) ⟨507600, by rfl⟩ : syracuseStep 1353601 = 1015201) B1015201
theorem B501659 : Blo 499793 501659 := bstep (se 1 (by rfl) ⟨376244, by rfl⟩ : syracuseStep 501659 = 752489) B752489
theorem B34875299 : Blo 499793 34875299 := bstep (se 1 (by rfl) ⟨26156474, by rfl⟩ : syracuseStep 34875299 = 52312949) B52312949
theorem B501711 : Blo 499793 501711 := bstep (se 1 (by rfl) ⟨376283, by rfl⟩ : syracuseStep 501711 = 752567) B752567
theorem B501735 : Blo 499793 501735 := bstep (se 1 (by rfl) ⟨376301, by rfl⟩ : syracuseStep 501735 = 752603) B752603
theorem B2140289 : Blo 499793 2140289 := bstep (se 2 (by rfl) ⟨802608, by rfl⟩ : syracuseStep 2140289 = 1605217) B1605217
theorem B3221633 : Blo 499793 3221633 := bstep (se 2 (by rfl) ⟨1208112, by rfl⟩ : syracuseStep 3221633 = 2416225) B2416225
theorem B502047 : Blo 499793 502047 := bstep (se 1 (by rfl) ⟨376535, by rfl⟩ : syracuseStep 502047 = 753071) B753071
theorem B37234997 : Blo 499793 37234997 := bstep (se 5 (by rfl) ⟨1745390, by rfl⟩ : syracuseStep 37234997 = 3490781) B3490781
theorem B502107 : Blo 499793 502107 := bstep (se 1 (by rfl) ⟨376580, by rfl⟩ : syracuseStep 502107 = 753161) B753161
theorem B502127 : Blo 499793 502127 := bstep (se 1 (by rfl) ⟨376595, by rfl⟩ : syracuseStep 502127 = 753191) B753191
theorem B502183 : Blo 499793 502183 := bstep (se 1 (by rfl) ⟨376637, by rfl⟩ : syracuseStep 502183 = 753275) B753275
theorem B1124783 : Blo 499793 1124783 := bstep (se 1 (by rfl) ⟨843587, by rfl⟩ : syracuseStep 1124783 = 1687175) B1687175
theorem B1124819 : Blo 499793 1124819 := bstep (se 1 (by rfl) ⟨843614, by rfl⟩ : syracuseStep 1124819 = 1687229) B1687229
theorem B502267 : Blo 499793 502267 := bstep (se 1 (by rfl) ⟨376700, by rfl⟩ : syracuseStep 502267 = 753401) B753401
theorem B1124927 : Blo 499793 1124927 := bstep (se 1 (by rfl) ⟨843695, by rfl⟩ : syracuseStep 1124927 = 1687391) B1687391
theorem B502335 : Blo 499793 502335 := bstep (se 1 (by rfl) ⟨376751, by rfl⟩ : syracuseStep 502335 = 753503) B753503
theorem B633415 : Blo 499793 633415 := bstep (se 1 (by rfl) ⟨475061, by rfl⟩ : syracuseStep 633415 = 950123) B950123
theorem B502343 : Blo 499793 502343 := bstep (se 1 (by rfl) ⟨376757, by rfl⟩ : syracuseStep 502343 = 753515) B753515
theorem B1125035 : Blo 499793 1125035 := bstep (se 1 (by rfl) ⟨843776, by rfl⟩ : syracuseStep 1125035 = 1687553) B1687553
theorem B502495 : Blo 499793 502495 := bstep (se 1 (by rfl) ⟨376871, by rfl⟩ : syracuseStep 502495 = 753743) B753743
theorem B502575 : Blo 499793 502575 := bstep (se 1 (by rfl) ⟨376931, by rfl⟩ : syracuseStep 502575 = 753863) B753863
theorem B1354639 : Blo 499793 1354639 := bstep (se 1 (by rfl) ⟨1015979, by rfl⟩ : syracuseStep 1354639 = 2031959) B2031959
theorem B502683 : Blo 499793 502683 := bstep (se 1 (by rfl) ⟨377012, by rfl⟩ : syracuseStep 502683 = 754025) B754025
theorem B502735 : Blo 499793 502735 := bstep (se 1 (by rfl) ⟨377051, by rfl⟩ : syracuseStep 502735 = 754103) B754103
theorem B5975005 : Blo 499793 5975005 := bstep (se 3 (by rfl) ⟨1120313, by rfl⟩ : syracuseStep 5975005 = 2240627) B2240627
theorem B502759 : Blo 499793 502759 := bstep (se 1 (by rfl) ⟨377069, by rfl⟩ : syracuseStep 502759 = 754139) B754139
theorem B1125575 : Blo 499793 1125575 := bstep (se 1 (by rfl) ⟨844181, by rfl⟩ : syracuseStep 1125575 = 1688363) B1688363
theorem B1322183 : Blo 499793 1322183 := bstep (se 1 (by rfl) ⟨991637, by rfl⟩ : syracuseStep 1322183 = 1983275) B1983275
theorem B1289465 : Blo 499793 1289465 := bstep (se 2 (by rfl) ⟨483549, by rfl⟩ : syracuseStep 1289465 = 967099) B967099
theorem B503071 : Blo 499793 503071 := bstep (se 1 (by rfl) ⟨377303, by rfl⟩ : syracuseStep 503071 = 754607) B754607
theorem B3812669 : Blo 499793 3812669 := bstep (se 3 (by rfl) ⟨714875, by rfl⟩ : syracuseStep 3812669 = 1429751) B1429751
theorem B503131 : Blo 499793 503131 := bstep (se 1 (by rfl) ⟨377348, by rfl⟩ : syracuseStep 503131 = 754697) B754697
theorem B503151 : Blo 499793 503151 := bstep (se 1 (by rfl) ⟨377363, by rfl⟩ : syracuseStep 503151 = 754727) B754727
theorem B1125755 : Blo 499793 1125755 := bstep (se 1 (by rfl) ⟨844316, by rfl⟩ : syracuseStep 1125755 = 1688633) B1688633
theorem B503207 : Blo 499793 503207 := bstep (se 1 (by rfl) ⟨377405, by rfl⟩ : syracuseStep 503207 = 754811) B754811
theorem B601543 : Blo 499793 601543 := bstep (se 1 (by rfl) ⟨451157, by rfl⟩ : syracuseStep 601543 = 902315) B902315
theorem B1125881 : Blo 499793 1125881 := bstep (se 2 (by rfl) ⟨422205, by rfl⟩ : syracuseStep 1125881 = 844411) B844411
theorem B503291 : Blo 499793 503291 := bstep (se 1 (by rfl) ⟨377468, by rfl⟩ : syracuseStep 503291 = 754937) B754937
theorem B503359 : Blo 499793 503359 := bstep (se 1 (by rfl) ⟨377519, by rfl⟩ : syracuseStep 503359 = 755039) B755039
theorem B503367 : Blo 499793 503367 := bstep (se 1 (by rfl) ⟨377525, by rfl⟩ : syracuseStep 503367 = 755051) B755051
theorem B1125971 : Blo 499793 1125971 := bstep (se 1 (by rfl) ⟨844478, by rfl⟩ : syracuseStep 1125971 = 1688957) B1688957
theorem B503519 : Blo 499793 503519 := bstep (se 1 (by rfl) ⟨377639, by rfl⟩ : syracuseStep 503519 = 755279) B755279
theorem B1126151 : Blo 499793 1126151 := bstep (se 1 (by rfl) ⟨844613, by rfl⟩ : syracuseStep 1126151 = 1689227) B1689227
theorem B2141963 : Blo 499793 2141963 := bstep (se 1 (by rfl) ⟨1606472, by rfl⟩ : syracuseStep 2141963 = 3212945) B3212945
theorem B503599 : Blo 499793 503599 := bstep (se 1 (by rfl) ⟨377699, by rfl⟩ : syracuseStep 503599 = 755399) B755399
theorem B503707 : Blo 499793 503707 := bstep (se 1 (by rfl) ⟨377780, by rfl⟩ : syracuseStep 503707 = 755561) B755561
theorem B503759 : Blo 499793 503759 := bstep (se 1 (by rfl) ⟨377819, by rfl⟩ : syracuseStep 503759 = 755639) B755639
theorem B503783 : Blo 499793 503783 := bstep (se 1 (by rfl) ⟨377837, by rfl⟩ : syracuseStep 503783 = 755675) B755675
theorem B9679115 : Blo 499793 9679115 := bstep (se 1 (by rfl) ⟨7259336, by rfl⟩ : syracuseStep 9679115 = 14518673) B14518673
theorem B1126763 : Blo 499793 1126763 := bstep (se 1 (by rfl) ⟨845072, by rfl⟩ : syracuseStep 1126763 = 1690145) B1690145
theorem B635303 : Blo 499793 635303 := bstep (se 1 (by rfl) ⟨476477, by rfl⟩ : syracuseStep 635303 = 952955) B952955
theorem B1126907 : Blo 499793 1126907 := bstep (se 1 (by rfl) ⟨845180, by rfl⟩ : syracuseStep 1126907 = 1690361) B1690361
theorem B602687 : Blo 499793 602687 := bstep (se 1 (by rfl) ⟨452015, by rfl⟩ : syracuseStep 602687 = 904031) B904031
theorem B635455 : Blo 499793 635455 := bstep (se 1 (by rfl) ⟨476591, by rfl⟩ : syracuseStep 635455 = 953183) B953183
theorem B1127033 : Blo 499793 1127033 := bstep (se 2 (by rfl) ⟨422637, by rfl⟩ : syracuseStep 1127033 = 845275) B845275
theorem B1127087 : Blo 499793 1127087 := bstep (se 1 (by rfl) ⟨845315, by rfl⟩ : syracuseStep 1127087 = 1690631) B1690631
theorem B635627 : Blo 499793 635627 := bstep (se 1 (by rfl) ⟨476720, by rfl⟩ : syracuseStep 635627 = 953441) B953441
theorem B1127159 : Blo 499793 1127159 := bstep (se 1 (by rfl) ⟨845369, by rfl⟩ : syracuseStep 1127159 = 1690739) B1690739
theorem B2536271 : Blo 499793 2536271 := bstep (se 1 (by rfl) ⟨1902203, by rfl⟩ : syracuseStep 2536271 = 3804407) B3804407
theorem B1127339 : Blo 499793 1127339 := bstep (se 1 (by rfl) ⟨845504, by rfl⟩ : syracuseStep 1127339 = 1691009) B1691009
theorem B537575 : Blo 499793 537575 := bstep (se 1 (by rfl) ⟨403181, by rfl⟩ : syracuseStep 537575 = 806363) B806363
theorem B1815527 : Blo 499793 1815527 := bstep (se 1 (by rfl) ⟨1361645, by rfl⟩ : syracuseStep 1815527 = 2723291) B2723291
theorem B2536595 : Blo 499793 2536595 := bstep (se 1 (by rfl) ⟨1902446, by rfl⟩ : syracuseStep 2536595 = 3804893) B3804893
theorem B2864423 : Blo 499793 2864423 := bstep (se 1 (by rfl) ⟨2148317, by rfl⟩ : syracuseStep 2864423 = 4296635) B4296635
theorem B1127879 : Blo 499793 1127879 := bstep (se 1 (by rfl) ⟨845909, by rfl⟩ : syracuseStep 1127879 = 1691819) B1691819
theorem B41268689 : Blo 499793 41268689 := bstep (se 2 (by rfl) ⟨15475758, by rfl⟩ : syracuseStep 41268689 = 30951517) B30951517
theorem B636599 : Blo 499793 636599 := bstep (se 1 (by rfl) ⟨477449, by rfl⟩ : syracuseStep 636599 = 954899) B954899
theorem B3815099 : Blo 499793 3815099 := bstep (se 1 (by rfl) ⟨2861324, by rfl⟩ : syracuseStep 3815099 = 5722649) B5722649
theorem B1128239 : Blo 499793 1128239 := bstep (se 1 (by rfl) ⟨846179, by rfl⟩ : syracuseStep 1128239 = 1692359) B1692359
theorem B636751 : Blo 499793 636751 := bstep (se 1 (by rfl) ⟨477563, by rfl⟩ : syracuseStep 636751 = 955127) B955127
theorem B2570221 : Blo 499793 2570221 := bstep (se 3 (by rfl) ⟨481916, by rfl⟩ : syracuseStep 2570221 = 963833) B963833
theorem B5421323 : Blo 499793 5421323 := bstep (se 1 (by rfl) ⟨4065992, by rfl⟩ : syracuseStep 5421323 = 8131985) B8131985
theorem B1423727 : Blo 499793 1423727 := bstep (se 1 (by rfl) ⟨1067795, by rfl⟩ : syracuseStep 1423727 = 2135591) B2135591
theorem B1128815 : Blo 499793 1128815 := bstep (se 1 (by rfl) ⟨846611, by rfl⟩ : syracuseStep 1128815 = 1693223) B1693223
theorem B1128887 : Blo 499793 1128887 := bstep (se 1 (by rfl) ⟨846665, by rfl⟩ : syracuseStep 1128887 = 1693331) B1693331
theorem B1129031 : Blo 499793 1129031 := bstep (se 1 (by rfl) ⟨846773, by rfl⟩ : syracuseStep 1129031 = 1693547) B1693547
theorem B1129067 : Blo 499793 1129067 := bstep (se 1 (by rfl) ⟨846800, by rfl⟩ : syracuseStep 1129067 = 1693601) B1693601
theorem B24394391 : Blo 499793 24394391 := bstep (se 1 (by rfl) ⟨18295793, by rfl⟩ : syracuseStep 24394391 = 36591587) B36591587
theorem B2702099 : Blo 499793 2702099 := bstep (se 1 (by rfl) ⟨2026574, by rfl⟩ : syracuseStep 2702099 = 4053149) B4053149
theorem B3619727 : Blo 499793 3619727 := bstep (se 1 (by rfl) ⟨2714795, by rfl⟩ : syracuseStep 3619727 = 5429591) B5429591
theorem B2866063 : Blo 499793 2866063 := bstep (se 1 (by rfl) ⟨2149547, by rfl⟩ : syracuseStep 2866063 = 4299095) B4299095
theorem B1129463 : Blo 499793 1129463 := bstep (se 1 (by rfl) ⟨847097, by rfl⟩ : syracuseStep 1129463 = 1694195) B1694195
theorem B1424603 : Blo 499793 1424603 := bstep (se 1 (by rfl) ⟨1068452, by rfl⟩ : syracuseStep 1424603 = 2136905) B2136905
theorem B1129823 : Blo 499793 1129823 := bstep (se 1 (by rfl) ⟨847367, by rfl⟩ : syracuseStep 1129823 = 1694735) B1694735
theorem B4570705 : Blo 499793 4570705 := bstep (se 2 (by rfl) ⟨1714014, by rfl⟩ : syracuseStep 4570705 = 3428029) B3428029
theorem B3817043 : Blo 499793 3817043 := bstep (se 1 (by rfl) ⟨2862782, by rfl⟩ : syracuseStep 3817043 = 5725565) B5725565
theorem B4275827 : Blo 499793 4275827 := bstep (se 1 (by rfl) ⟨3206870, by rfl⟩ : syracuseStep 4275827 = 6413741) B6413741
theorem B1130219 : Blo 499793 1130219 := bstep (se 1 (by rfl) ⟨847664, by rfl⟩ : syracuseStep 1130219 = 1695329) B1695329
theorem B1687337 : Blo 499793 1687337 := bstep (se 2 (by rfl) ⟨632751, by rfl⟩ : syracuseStep 1687337 = 1265503) B1265503
theorem B8568665 : Blo 499793 8568665 := bstep (se 2 (by rfl) ⟨3213249, by rfl⟩ : syracuseStep 8568665 = 6426499) B6426499
theorem B1130345 : Blo 499793 1130345 := bstep (se 2 (by rfl) ⟨423879, by rfl⟩ : syracuseStep 1130345 = 847759) B847759
theorem B3260267 : Blo 499793 3260267 := bstep (se 1 (by rfl) ⟨2445200, by rfl⟩ : syracuseStep 3260267 = 4890401) B4890401
theorem B3915649 : Blo 499793 3915649 := bstep (se 2 (by rfl) ⟨1468368, by rfl⟩ : syracuseStep 3915649 = 2936737) B2936737
theorem B2539673 : Blo 499793 2539673 := bstep (se 2 (by rfl) ⟨952377, by rfl⟩ : syracuseStep 2539673 = 1904755) B1904755
theorem B6111449 : Blo 499793 6111449 := bstep (se 2 (by rfl) ⟨2291793, by rfl⟩ : syracuseStep 6111449 = 4583587) B4583587
theorem B2408707 : Blo 499793 2408707 := bstep (se 1 (by rfl) ⟨1806530, by rfl⟩ : syracuseStep 2408707 = 3613061) B3613061
theorem B1131191 : Blo 499793 1131191 := bstep (se 1 (by rfl) ⟨848393, by rfl⟩ : syracuseStep 1131191 = 1696787) B1696787
theorem B2409209 : Blo 499793 2409209 := bstep (se 2 (by rfl) ⟨903453, by rfl⟩ : syracuseStep 2409209 = 1806907) B1806907
theorem B19776307 : Blo 499793 19776307 := bstep (se 1 (by rfl) ⟨14832230, by rfl⟩ : syracuseStep 19776307 = 29664461) B29664461
theorem B1131407 : Blo 499793 1131407 := bstep (se 1 (by rfl) ⟨848555, by rfl⟩ : syracuseStep 1131407 = 1697111) B1697111
theorem B2540483 : Blo 499793 2540483 := bstep (se 1 (by rfl) ⟨1905362, by rfl⟩ : syracuseStep 2540483 = 3810725) B3810725
theorem B3621827 : Blo 499793 3621827 := bstep (se 1 (by rfl) ⟨2716370, by rfl⟩ : syracuseStep 3621827 = 5432741) B5432741
theorem B1885331 : Blo 499793 1885331 := bstep (se 1 (by rfl) ⟨1413998, by rfl⟩ : syracuseStep 1885331 = 2827997) B2827997
theorem B36619607 : Blo 499793 36619607 := bstep (se 1 (by rfl) ⟨27464705, by rfl⟩ : syracuseStep 36619607 = 54929411) B54929411
theorem B1132127 : Blo 499793 1132127 := bstep (se 1 (by rfl) ⟨849095, by rfl⟩ : syracuseStep 1132127 = 1698191) B1698191
theorem B1132343 : Blo 499793 1132343 := bstep (se 1 (by rfl) ⟨849257, by rfl⟩ : syracuseStep 1132343 = 1698515) B1698515
theorem B1689551 : Blo 499793 1689551 := bstep (se 1 (by rfl) ⟨1267163, by rfl⟩ : syracuseStep 1689551 = 2534327) B2534327
theorem B1132649 : Blo 499793 1132649 := bstep (se 2 (by rfl) ⟨424743, by rfl⟩ : syracuseStep 1132649 = 849487) B849487
theorem B903433 : Blo 499793 903433 := bstep (se 2 (by rfl) ⟨338787, by rfl⟩ : syracuseStep 903433 = 677575) B677575
theorem B969185 : Blo 499793 969185 := bstep (se 2 (by rfl) ⟨363444, by rfl⟩ : syracuseStep 969185 = 726889) B726889
theorem B2705993 : Blo 499793 2705993 := bstep (se 2 (by rfl) ⟨1014747, by rfl⟩ : syracuseStep 2705993 = 2029495) B2029495
theorem B1133135 : Blo 499793 1133135 := bstep (se 1 (by rfl) ⟨849851, by rfl⟩ : syracuseStep 1133135 = 1699703) B1699703
theorem B1133279 : Blo 499793 1133279 := bstep (se 1 (by rfl) ⟨849959, by rfl⟩ : syracuseStep 1133279 = 1699919) B1699919
theorem B1690523 : Blo 499793 1690523 := bstep (se 1 (by rfl) ⟨1267892, by rfl⟩ : syracuseStep 1690523 = 2535785) B2535785
theorem B1133531 : Blo 499793 1133531 := bstep (se 1 (by rfl) ⟨850148, by rfl⟩ : syracuseStep 1133531 = 1700297) B1700297
theorem B806107 : Blo 499793 806107 := bstep (se 1 (by rfl) ⟨604580, by rfl⟩ : syracuseStep 806107 = 1209161) B1209161
theorem B642427 : Blo 499793 642427 := bstep (se 1 (by rfl) ⟨481820, by rfl⟩ : syracuseStep 642427 = 963641) B963641
theorem B1265159 : Blo 499793 1265159 := bstep (se 1 (by rfl) ⟨948869, by rfl⟩ : syracuseStep 1265159 = 1897739) B1897739
theorem B1691549 : Blo 499793 1691549 := bstep (se 3 (by rfl) ⟨317165, by rfl⟩ : syracuseStep 1691549 = 634331) B634331
theorem B1265615 : Blo 499793 1265615 := bstep (se 1 (by rfl) ⟨949211, by rfl⟩ : syracuseStep 1265615 = 1898423) B1898423
theorem B806863 : Blo 499793 806863 := bstep (se 1 (by rfl) ⟨605147, by rfl⟩ : syracuseStep 806863 = 1210295) B1210295
theorem B1691657 : Blo 499793 1691657 := bstep (se 2 (by rfl) ⟨634371, by rfl⟩ : syracuseStep 1691657 = 1268743) B1268743
theorem B2544047 : Blo 499793 2544047 := bstep (se 1 (by rfl) ⟨1908035, by rfl⟩ : syracuseStep 2544047 = 3816071) B3816071
theorem B1266131 : Blo 499793 1266131 := bstep (se 1 (by rfl) ⟨949598, by rfl⟩ : syracuseStep 1266131 = 1899197) B1899197
theorem B3298157 : Blo 499793 3298157 := bstep (se 3 (by rfl) ⟨618404, by rfl⟩ : syracuseStep 3298157 = 1236809) B1236809
theorem B1266587 : Blo 499793 1266587 := bstep (se 1 (by rfl) ⟨949940, by rfl⟩ : syracuseStep 1266587 = 1899881) B1899881
theorem B26432477 : Blo 499793 26432477 := bstep (se 3 (by rfl) ⟨4956089, by rfl⟩ : syracuseStep 26432477 = 9912179) B9912179
theorem B1430743 : Blo 499793 1430743 := bstep (se 1 (by rfl) ⟨1073057, by rfl⟩ : syracuseStep 1430743 = 2146115) B2146115
theorem B1430777 : Blo 499793 1430777 := bstep (se 2 (by rfl) ⟨536541, by rfl⟩ : syracuseStep 1430777 = 1073083) B1073083
theorem B3724649 : Blo 499793 3724649 := bstep (se 2 (by rfl) ⟨1396743, by rfl⟩ : syracuseStep 3724649 = 2793487) B2793487
theorem B2545019 : Blo 499793 2545019 := bstep (se 1 (by rfl) ⟨1908764, by rfl⟩ : syracuseStep 2545019 = 3817529) B3817529
theorem B2905537 : Blo 499793 2905537 := bstep (se 2 (by rfl) ⟨1089576, by rfl⟩ : syracuseStep 2905537 = 2179153) B2179153
theorem B5133869 : Blo 499793 5133869 := bstep (se 3 (by rfl) ⟨962600, by rfl⟩ : syracuseStep 5133869 = 1925201) B1925201
theorem B1267721 : Blo 499793 1267721 := bstep (se 2 (by rfl) ⟨475395, by rfl⟩ : syracuseStep 1267721 = 950791) B950791
theorem B24107165 : Blo 499793 24107165 := bstep (se 3 (by rfl) ⟨4520093, by rfl⟩ : syracuseStep 24107165 = 9040187) B9040187
theorem B2578679 : Blo 499793 2578679 := bstep (se 1 (by rfl) ⟨1934009, by rfl⟩ : syracuseStep 2578679 = 3868019) B3868019
theorem B1268075 : Blo 499793 1268075 := bstep (se 1 (by rfl) ⟨951056, by rfl⟩ : syracuseStep 1268075 = 1902113) B1902113
theorem B1432019 : Blo 499793 1432019 := bstep (se 1 (by rfl) ⟨1074014, by rfl⟩ : syracuseStep 1432019 = 2148029) B2148029
theorem B1202683 : Blo 499793 1202683 := bstep (se 1 (by rfl) ⟨902012, by rfl⟩ : syracuseStep 1202683 = 1804025) B1804025
theorem B2415167 : Blo 499793 2415167 := bstep (se 1 (by rfl) ⟨1811375, by rfl⟩ : syracuseStep 2415167 = 3622751) B3622751
theorem B4119113 : Blo 499793 4119113 := bstep (se 2 (by rfl) ⟨1544667, by rfl⟩ : syracuseStep 4119113 = 3089335) B3089335
theorem B2546315 : Blo 499793 2546315 := bstep (se 1 (by rfl) ⟨1909736, by rfl⟩ : syracuseStep 2546315 = 3819473) B3819473
theorem B1268399 : Blo 499793 1268399 := bstep (se 1 (by rfl) ⟨951299, by rfl⟩ : syracuseStep 1268399 = 1902599) B1902599
theorem B20601539 : Blo 499793 20601539 := bstep (se 1 (by rfl) ⟨15451154, by rfl⟩ : syracuseStep 20601539 = 30902309) B30902309
theorem B645943 : Blo 499793 645943 := bstep (se 1 (by rfl) ⟨484457, by rfl⟩ : syracuseStep 645943 = 968915) B968915
theorem B1432475 : Blo 499793 1432475 := bstep (se 1 (by rfl) ⟨1074356, by rfl⟩ : syracuseStep 1432475 = 2148713) B2148713
theorem B1268723 : Blo 499793 1268723 := bstep (se 1 (by rfl) ⟨951542, by rfl⟩ : syracuseStep 1268723 = 1903085) B1903085
theorem B1694843 : Blo 499793 1694843 := bstep (se 1 (by rfl) ⟨1271132, by rfl⟩ : syracuseStep 1694843 = 2542265) B2542265
theorem B1695113 : Blo 499793 1695113 := bstep (se 2 (by rfl) ⟨635667, by rfl⟩ : syracuseStep 1695113 = 1271335) B1271335
theorem B1269179 : Blo 499793 1269179 := bstep (se 1 (by rfl) ⟨951884, by rfl⟩ : syracuseStep 1269179 = 1903769) B1903769
theorem B65068505 : Blo 499793 65068505 := bstep (se 2 (by rfl) ⟨24400689, by rfl⟩ : syracuseStep 65068505 = 48801379) B48801379
theorem B2416243 : Blo 499793 2416243 := bstep (se 1 (by rfl) ⟨1812182, by rfl⟩ : syracuseStep 2416243 = 3624365) B3624365
theorem B843527 : Blo 499793 843527 := bstep (se 1 (by rfl) ⟨632645, by rfl⟩ : syracuseStep 843527 = 1265291) B1265291
theorem B1433351 : Blo 499793 1433351 := bstep (se 1 (by rfl) ⟨1075013, by rfl⟩ : syracuseStep 1433351 = 2150027) B2150027
theorem B1695545 : Blo 499793 1695545 := bstep (se 2 (by rfl) ⟨635829, by rfl⟩ : syracuseStep 1695545 = 1271659) B1271659
theorem B5693489 : Blo 499793 5693489 := bstep (se 2 (by rfl) ⟨2135058, by rfl⟩ : syracuseStep 5693489 = 4270117) B4270117
theorem B17817731 : Blo 499793 17817731 := bstep (se 1 (by rfl) ⟨13363298, by rfl⟩ : syracuseStep 17817731 = 26726597) B26726597
theorem B844283 : Blo 499793 844283 := bstep (se 1 (by rfl) ⟨633212, by rfl⟩ : syracuseStep 844283 = 1266425) B1266425
theorem B1270343 : Blo 499793 1270343 := bstep (se 1 (by rfl) ⟨952757, by rfl⟩ : syracuseStep 1270343 = 1905515) B1905515
theorem B1696409 : Blo 499793 1696409 := bstep (se 2 (by rfl) ⟨636153, by rfl⟩ : syracuseStep 1696409 = 1272307) B1272307
theorem B6120107 : Blo 499793 6120107 := bstep (se 1 (by rfl) ⟨4590080, by rfl⟩ : syracuseStep 6120107 = 9180161) B9180161
theorem B4809419 : Blo 499793 4809419 := bstep (se 1 (by rfl) ⟨3607064, by rfl⟩ : syracuseStep 4809419 = 7214129) B7214129
theorem B844715 : Blo 499793 844715 := bstep (se 1 (by rfl) ⟨633536, by rfl⟩ : syracuseStep 844715 = 1267073) B1267073
theorem B2417627 : Blo 499793 2417627 := bstep (se 1 (by rfl) ⟨1813220, by rfl⟩ : syracuseStep 2417627 = 3626441) B3626441
theorem B1074151 : Blo 499793 1074151 := bstep (se 1 (by rfl) ⟨805613, by rfl⟩ : syracuseStep 1074151 = 1611227) B1611227
theorem B1205239 : Blo 499793 1205239 := bstep (se 1 (by rfl) ⟨903929, by rfl⟩ : syracuseStep 1205239 = 1807859) B1807859
theorem B4056263 : Blo 499793 4056263 := bstep (se 1 (by rfl) ⟨3042197, by rfl⟩ : syracuseStep 4056263 = 6084395) B6084395
theorem B4810033 : Blo 499793 4810033 := bstep (se 2 (by rfl) ⟨1803762, by rfl⟩ : syracuseStep 4810033 = 3607525) B3607525
theorem B22046053 : Blo 499793 22046053 := bstep (se 4 (by rfl) ⟨2066817, by rfl⟩ : syracuseStep 22046053 = 4133635) B4133635
theorem B845255 : Blo 499793 845255 := bstep (se 1 (by rfl) ⟨633941, by rfl⟩ : syracuseStep 845255 = 1267883) B1267883
theorem B1271609 : Blo 499793 1271609 := bstep (se 2 (by rfl) ⟨476853, by rfl⟩ : syracuseStep 1271609 = 953707) B953707
theorem B1697921 : Blo 499793 1697921 := bstep (se 2 (by rfl) ⟨636720, by rfl⟩ : syracuseStep 1697921 = 1273441) B1273441
theorem B8120573 : Blo 499793 8120573 := bstep (se 3 (by rfl) ⟨1522607, by rfl⟩ : syracuseStep 8120573 = 3045215) B3045215
theorem B2550041 : Blo 499793 2550041 := bstep (se 2 (by rfl) ⟨956265, by rfl⟩ : syracuseStep 2550041 = 1912531) B1912531
theorem B6121763 : Blo 499793 6121763 := bstep (se 1 (by rfl) ⟨4591322, by rfl⟩ : syracuseStep 6121763 = 9182645) B9182645
theorem B846247 : Blo 499793 846247 := bstep (se 1 (by rfl) ⟨634685, by rfl⟩ : syracuseStep 846247 = 1269371) B1269371
theorem B1698299 : Blo 499793 1698299 := bstep (se 1 (by rfl) ⟨1273724, by rfl⟩ : syracuseStep 1698299 = 2547449) B2547449
theorem B846409 : Blo 499793 846409 := bstep (se 2 (by rfl) ⟨317403, by rfl⟩ : syracuseStep 846409 = 634807) B634807
theorem B846443 : Blo 499793 846443 := bstep (se 1 (by rfl) ⟨634832, by rfl⟩ : syracuseStep 846443 = 1269665) B1269665
theorem B1698731 : Blo 499793 1698731 := bstep (se 1 (by rfl) ⟨1274048, by rfl⟩ : syracuseStep 1698731 = 2548097) B2548097
theorem B1272955 : Blo 499793 1272955 := bstep (se 1 (by rfl) ⟨954716, by rfl⟩ : syracuseStep 1272955 = 1909433) B1909433
theorem B3206587 : Blo 499793 3206587 := bstep (se 1 (by rfl) ⟨2404940, by rfl⟩ : syracuseStep 3206587 = 4809881) B4809881
theorem B1699271 : Blo 499793 1699271 := bstep (se 1 (by rfl) ⟨1274453, by rfl⟩ : syracuseStep 1699271 = 2548907) B2548907
theorem B19328705 : Blo 499793 19328705 := bstep (se 2 (by rfl) ⟨7248264, by rfl⟩ : syracuseStep 19328705 = 14496529) B14496529
theorem B1699595 : Blo 499793 1699595 := bstep (se 1 (by rfl) ⟨1274696, by rfl⟩ : syracuseStep 1699595 = 2549393) B2549393
theorem B1699865 : Blo 499793 1699865 := bstep (se 2 (by rfl) ⟨637449, by rfl⟩ : syracuseStep 1699865 = 1274899) B1274899
theorem B4288571 : Blo 499793 4288571 := bstep (se 1 (by rfl) ⟨3216428, by rfl⟩ : syracuseStep 4288571 = 6432857) B6432857
theorem B1208449 : Blo 499793 1208449 := bstep (se 2 (by rfl) ⟨453168, by rfl⟩ : syracuseStep 1208449 = 906337) B906337
theorem B848137 : Blo 499793 848137 := bstep (se 2 (by rfl) ⟨318051, by rfl⟩ : syracuseStep 848137 = 636103) B636103
theorem B10809611 : Blo 499793 10809611 := bstep (se 1 (by rfl) ⟨8107208, by rfl⟩ : syracuseStep 10809611 = 16214417) B16214417
theorem B749915 : Blo 499793 749915 := bstep (se 1 (by rfl) ⟨562436, by rfl⟩ : syracuseStep 749915 = 1124873) B1124873
theorem B1274363 : Blo 499793 1274363 := bstep (se 1 (by rfl) ⟨955772, by rfl⟩ : syracuseStep 1274363 = 1911545) B1911545
theorem B750143 : Blo 499793 750143 := bstep (se 1 (by rfl) ⟨562607, by rfl⟩ : syracuseStep 750143 = 1125215) B1125215
theorem B750263 : Blo 499793 750263 := bstep (se 1 (by rfl) ⟨562697, by rfl⟩ : syracuseStep 750263 = 1125395) B1125395
theorem B750491 : Blo 499793 750491 := bstep (se 1 (by rfl) ⟨562868, by rfl⟩ : syracuseStep 750491 = 1125737) B1125737
theorem B6419735 : Blo 499793 6419735 := bstep (se 1 (by rfl) ⟨4814801, by rfl⟩ : syracuseStep 6419735 = 9629603) B9629603
theorem B750887 : Blo 499793 750887 := bstep (se 1 (by rfl) ⟨563165, by rfl⟩ : syracuseStep 750887 = 1126331) B1126331
theorem B750971 : Blo 499793 750971 := bstep (se 1 (by rfl) ⟨563228, by rfl⟩ : syracuseStep 750971 = 1126457) B1126457
theorem B751097 : Blo 499793 751097 := bstep (se 2 (by rfl) ⟨281661, by rfl⟩ : syracuseStep 751097 = 563323) B563323
theorem B751199 : Blo 499793 751199 := bstep (se 1 (by rfl) ⟨563399, by rfl⟩ : syracuseStep 751199 = 1126799) B1126799
theorem B587359 : Blo 499793 587359 := bstep (se 1 (by rfl) ⟨440519, by rfl⟩ : syracuseStep 587359 = 881039) B881039
theorem B849595 : Blo 499793 849595 := bstep (se 1 (by rfl) ⟨637196, by rfl⟩ : syracuseStep 849595 = 1274393) B1274393
theorem B6879005 : Blo 499793 6879005 := bstep (se 3 (by rfl) ⟨1289813, by rfl⟩ : syracuseStep 6879005 = 2579627) B2579627
theorem B2848567 : Blo 499793 2848567 := bstep (se 1 (by rfl) ⟨2136425, by rfl⟩ : syracuseStep 2848567 = 4272851) B4272851
theorem B751415 : Blo 499793 751415 := bstep (se 1 (by rfl) ⟨563561, by rfl⟩ : syracuseStep 751415 = 1127123) B1127123
theorem B2619191 : Blo 499793 2619191 := bstep (se 1 (by rfl) ⟨1964393, by rfl⟩ : syracuseStep 2619191 = 3928787) B3928787
theorem B6453107 : Blo 499793 6453107 := bstep (se 1 (by rfl) ⟨4839830, by rfl⟩ : syracuseStep 6453107 = 9679661) B9679661
theorem B5404715 : Blo 499793 5404715 := bstep (se 1 (by rfl) ⟨4053536, by rfl⟩ : syracuseStep 5404715 = 8107073) B8107073
theorem B751721 : Blo 499793 751721 := bstep (se 2 (by rfl) ⟨281895, by rfl⟩ : syracuseStep 751721 = 563791) B563791
theorem B752039 : Blo 499793 752039 := bstep (se 1 (by rfl) ⟨564029, by rfl⟩ : syracuseStep 752039 = 1128059) B1128059
theorem B3799547 : Blo 499793 3799547 := bstep (se 1 (by rfl) ⟨2849660, by rfl⟩ : syracuseStep 3799547 = 5699321) B5699321
theorem B752123 : Blo 499793 752123 := bstep (se 1 (by rfl) ⟨564092, by rfl⟩ : syracuseStep 752123 = 1128185) B1128185
theorem B752249 : Blo 499793 752249 := bstep (se 2 (by rfl) ⟨282093, by rfl⟩ : syracuseStep 752249 = 564187) B564187
theorem B7731845 : Blo 499793 7731845 := bstep (se 4 (by rfl) ⟨724860, by rfl⟩ : syracuseStep 7731845 = 1449721) B1449721
theorem B10877591 : Blo 499793 10877591 := bstep (se 1 (by rfl) ⟨8158193, by rfl⟩ : syracuseStep 10877591 = 16316387) B16316387
theorem B752303 : Blo 499793 752303 := bstep (se 1 (by rfl) ⟨564227, by rfl⟩ : syracuseStep 752303 = 1128455) B1128455
theorem B752351 : Blo 499793 752351 := bstep (se 1 (by rfl) ⟨564263, by rfl⟩ : syracuseStep 752351 = 1128527) B1128527
theorem B752615 : Blo 499793 752615 := bstep (se 1 (by rfl) ⟨564461, by rfl⟩ : syracuseStep 752615 = 1128923) B1128923
theorem B752873 : Blo 499793 752873 := bstep (se 2 (by rfl) ⟨282327, by rfl⟩ : syracuseStep 752873 = 564655) B564655
theorem B752927 : Blo 499793 752927 := bstep (se 1 (by rfl) ⟨564695, by rfl⟩ : syracuseStep 752927 = 1129391) B1129391
theorem B1899895 : Blo 499793 1899895 := bstep (se 1 (by rfl) ⟨1424921, by rfl⟩ : syracuseStep 1899895 = 2849843) B2849843
theorem B753095 : Blo 499793 753095 := bstep (se 1 (by rfl) ⟨564821, by rfl⟩ : syracuseStep 753095 = 1129643) B1129643
theorem B5144057 : Blo 499793 5144057 := bstep (se 2 (by rfl) ⟨1929021, by rfl⟩ : syracuseStep 5144057 = 3858043) B3858043
theorem B753449 : Blo 499793 753449 := bstep (se 2 (by rfl) ⟨282543, by rfl⟩ : syracuseStep 753449 = 565087) B565087
theorem B753455 : Blo 499793 753455 := bstep (se 1 (by rfl) ⟨565091, by rfl⟩ : syracuseStep 753455 = 1130183) B1130183
theorem B3604297 : Blo 499793 3604297 := bstep (se 2 (by rfl) ⟨1351611, by rfl⟩ : syracuseStep 3604297 = 2703223) B2703223
theorem B35324219 : Blo 499793 35324219 := bstep (se 1 (by rfl) ⟨26493164, by rfl⟩ : syracuseStep 35324219 = 52986329) B52986329
theorem B917887 : Blo 499793 917887 := bstep (se 1 (by rfl) ⟨688415, by rfl⟩ : syracuseStep 917887 = 1376831) B1376831
theorem B754127 : Blo 499793 754127 := bstep (se 1 (by rfl) ⟨565595, by rfl⟩ : syracuseStep 754127 = 1131191) B1131191
theorem B754169 : Blo 499793 754169 := bstep (se 2 (by rfl) ⟨282813, by rfl⟩ : syracuseStep 754169 = 565627) B565627
theorem B1606139 : Blo 499793 1606139 := bstep (se 1 (by rfl) ⟨1204604, by rfl⟩ : syracuseStep 1606139 = 2409209) B2409209
theorem B754271 : Blo 499793 754271 := bstep (se 1 (by rfl) ⟨565703, by rfl⟩ : syracuseStep 754271 = 1131407) B1131407
theorem B24413071 : Blo 499793 24413071 := bstep (se 1 (by rfl) ⟨18309803, by rfl⟩ : syracuseStep 24413071 = 36619607) B36619607
theorem B1901627 : Blo 499793 1901627 := bstep (se 1 (by rfl) ⟨1426220, by rfl⟩ : syracuseStep 1901627 = 2852441) B2852441
theorem B754751 : Blo 499793 754751 := bstep (se 1 (by rfl) ⟨566063, by rfl⟩ : syracuseStep 754751 = 1132127) B1132127
theorem B754793 : Blo 499793 754793 := bstep (se 2 (by rfl) ⟨283047, by rfl⟩ : syracuseStep 754793 = 566095) B566095
theorem B754895 : Blo 499793 754895 := bstep (se 1 (by rfl) ⟨566171, by rfl⟩ : syracuseStep 754895 = 1132343) B1132343
theorem B1606985 : Blo 499793 1606985 := bstep (se 2 (by rfl) ⟨602619, by rfl⟩ : syracuseStep 1606985 = 1205239) B1205239
theorem B3802463 : Blo 499793 3802463 := bstep (se 1 (by rfl) ⟨2851847, by rfl⟩ : syracuseStep 3802463 = 5703695) B5703695
theorem B12846437 : Blo 499793 12846437 := bstep (se 4 (by rfl) ⟨1204353, by rfl⟩ : syracuseStep 12846437 = 2408707) B2408707
theorem B755099 : Blo 499793 755099 := bstep (se 1 (by rfl) ⟨566324, by rfl⟩ : syracuseStep 755099 = 1132649) B1132649
theorem B1607165 : Blo 499793 1607165 := bstep (se 3 (by rfl) ⟨301343, by rfl⟩ : syracuseStep 1607165 = 602687) B602687
theorem B755321 : Blo 499793 755321 := bstep (se 2 (by rfl) ⟨283245, by rfl⟩ : syracuseStep 755321 = 566491) B566491
theorem B1803995 : Blo 499793 1803995 := bstep (se 1 (by rfl) ⟨1352996, by rfl⟩ : syracuseStep 1803995 = 2705993) B2705993
theorem B755423 : Blo 499793 755423 := bstep (se 1 (by rfl) ⟨566567, by rfl⟩ : syracuseStep 755423 = 1133135) B1133135
theorem B1443625 : Blo 499793 1443625 := bstep (se 2 (by rfl) ⟨541359, by rfl⟩ : syracuseStep 1443625 = 1082719) B1082719
theorem B29394737 : Blo 499793 29394737 := bstep (se 2 (by rfl) ⟨11023026, by rfl⟩ : syracuseStep 29394737 = 22046053) B22046053
theorem B755519 : Blo 499793 755519 := bstep (se 1 (by rfl) ⟨566639, by rfl⟩ : syracuseStep 755519 = 1133279) B1133279
theorem B755687 : Blo 499793 755687 := bstep (se 1 (by rfl) ⟨566765, by rfl⟩ : syracuseStep 755687 = 1133531) B1133531
theorem B10325069 : Blo 499793 10325069 := bstep (se 3 (by rfl) ⟨1935950, by rfl⟩ : syracuseStep 10325069 = 3871901) B3871901
theorem B2198771 : Blo 499793 2198771 := bstep (se 1 (by rfl) ⟨1649078, by rfl⟩ : syracuseStep 2198771 = 3298157) B3298157
theorem B953851 : Blo 499793 953851 := bstep (se 1 (by rfl) ⟨715388, by rfl⟩ : syracuseStep 953851 = 1430777) B1430777
theorem B1806185 : Blo 499793 1806185 := bstep (se 2 (by rfl) ⟨677319, by rfl⟩ : syracuseStep 1806185 = 1354639) B1354639
theorem B7966673 : Blo 499793 7966673 := bstep (se 2 (by rfl) ⟨2987502, by rfl⟩ : syracuseStep 7966673 = 5975005) B5975005
theorem B954679 : Blo 499793 954679 := bstep (se 1 (by rfl) ⟨716009, by rfl⟩ : syracuseStep 954679 = 1432019) B1432019
theorem B1610111 : Blo 499793 1610111 := bstep (se 1 (by rfl) ⟨1207583, by rfl⟩ : syracuseStep 1610111 = 2415167) B2415167
theorem B13734359 : Blo 499793 13734359 := bstep (se 1 (by rfl) ⟨10300769, by rfl⟩ : syracuseStep 13734359 = 20601539) B20601539
theorem B954983 : Blo 499793 954983 := bstep (se 1 (by rfl) ⟨716237, by rfl⟩ : syracuseStep 954983 = 1432475) B1432475
theorem B1905727 : Blo 499793 1905727 := bstep (se 1 (by rfl) ⟨1429295, by rfl⟩ : syracuseStep 1905727 = 2858591) B2858591
theorem B562351 : Blo 499793 562351 := bstep (se 1 (by rfl) ⟨421763, by rfl⟩ : syracuseStep 562351 = 843527) B843527
theorem B955567 : Blo 499793 955567 := bstep (se 1 (by rfl) ⟨716675, by rfl⟩ : syracuseStep 955567 = 1433351) B1433351
theorem B1611265 : Blo 499793 1611265 := bstep (se 2 (by rfl) ⟨604224, by rfl⟩ : syracuseStep 1611265 = 1208449) B1208449
theorem B562855 : Blo 499793 562855 := bstep (se 1 (by rfl) ⟨422141, by rfl⟩ : syracuseStep 562855 = 844283) B844283
theorem B563143 : Blo 499793 563143 := bstep (se 1 (by rfl) ⟨422357, by rfl⟩ : syracuseStep 563143 = 844715) B844715
theorem B1611751 : Blo 499793 1611751 := bstep (se 1 (by rfl) ⟨1208813, by rfl⟩ : syracuseStep 1611751 = 2417627) B2417627
theorem B563503 : Blo 499793 563503 := bstep (se 1 (by rfl) ⟨422627, by rfl⟩ : syracuseStep 563503 = 845255) B845255
theorem B6101423 : Blo 499793 6101423 := bstep (se 1 (by rfl) ⟨4576067, by rfl⟩ : syracuseStep 6101423 = 9152135) B9152135
theorem B5413715 : Blo 499793 5413715 := bstep (se 1 (by rfl) ⟨4060286, by rfl⟩ : syracuseStep 5413715 = 8120573) B8120573
theorem B1710953 : Blo 499793 1710953 := bstep (se 2 (by rfl) ⟨641607, by rfl⟩ : syracuseStep 1710953 = 1283215) B1283215
theorem B1907657 : Blo 499793 1907657 := bstep (se 2 (by rfl) ⟨715371, by rfl⟩ : syracuseStep 1907657 = 1430743) B1430743
theorem B564295 : Blo 499793 564295 := bstep (se 1 (by rfl) ⟨423221, by rfl⟩ : syracuseStep 564295 = 846443) B846443
theorem B3874049 : Blo 499793 3874049 := bstep (se 2 (by rfl) ⟨1452768, by rfl⟩ : syracuseStep 3874049 = 2905537) B2905537
theorem B859643 : Blo 499793 859643 := bstep (se 1 (by rfl) ⟨644732, by rfl⟩ : syracuseStep 859643 = 1289465) B1289465
theorem B925409 : Blo 499793 925409 := bstep (se 2 (by rfl) ⟨347028, by rfl⟩ : syracuseStep 925409 = 694057) B694057
theorem B12885803 : Blo 499793 12885803 := bstep (se 1 (by rfl) ⟨9664352, by rfl⟩ : syracuseStep 12885803 = 19328705) B19328705
theorem B13705109 : Blo 499793 13705109 := bstep (se 6 (by rfl) ⟨321213, by rfl⟩ : syracuseStep 13705109 = 642427) B642427
theorem B2859047 : Blo 499793 2859047 := bstep (se 1 (by rfl) ⟨2144285, by rfl⟩ : syracuseStep 2859047 = 4288571) B4288571
theorem B499943 : Blo 499793 499943 := bstep (se 1 (by rfl) ⟨374957, by rfl⟩ : syracuseStep 499943 = 749915) B749915
theorem B500095 : Blo 499793 500095 := bstep (se 1 (by rfl) ⟨375071, by rfl⟩ : syracuseStep 500095 = 750143) B750143
theorem B500175 : Blo 499793 500175 := bstep (se 1 (by rfl) ⟨375131, by rfl⟩ : syracuseStep 500175 = 750263) B750263
theorem B500327 : Blo 499793 500327 := bstep (se 1 (by rfl) ⟨375245, by rfl⟩ : syracuseStep 500327 = 750491) B750491
theorem B500591 : Blo 499793 500591 := bstep (se 1 (by rfl) ⟨375443, by rfl⟩ : syracuseStep 500591 = 750887) B750887
theorem B1909615 : Blo 499793 1909615 := bstep (se 1 (by rfl) ⟨1432211, by rfl⟩ : syracuseStep 1909615 = 2864423) B2864423
theorem B500647 : Blo 499793 500647 := bstep (se 1 (by rfl) ⟨375485, by rfl⟩ : syracuseStep 500647 = 750971) B750971
theorem B500731 : Blo 499793 500731 := bstep (se 1 (by rfl) ⟨375548, by rfl⟩ : syracuseStep 500731 = 751097) B751097
theorem B500799 : Blo 499793 500799 := bstep (se 1 (by rfl) ⟨375599, by rfl⟩ : syracuseStep 500799 = 751199) B751199
theorem B861257 : Blo 499793 861257 := bstep (se 2 (by rfl) ⟨322971, by rfl⟩ : syracuseStep 861257 = 645943) B645943
theorem B3515557 : Blo 499793 3515557 := bstep (se 4 (by rfl) ⟨329583, by rfl⟩ : syracuseStep 3515557 = 659167) B659167
theorem B500943 : Blo 499793 500943 := bstep (se 1 (by rfl) ⟨375707, by rfl⟩ : syracuseStep 500943 = 751415) B751415
theorem B1746127 : Blo 499793 1746127 := bstep (se 1 (by rfl) ⟨1309595, by rfl⟩ : syracuseStep 1746127 = 2619191) B2619191
theorem B4302071 : Blo 499793 4302071 := bstep (se 1 (by rfl) ⟨3226553, by rfl⟩ : syracuseStep 4302071 = 6453107) B6453107
theorem B501147 : Blo 499793 501147 := bstep (se 1 (by rfl) ⟨375860, by rfl⟩ : syracuseStep 501147 = 751721) B751721
theorem B3614215 : Blo 499793 3614215 := bstep (se 1 (by rfl) ⟨2710661, by rfl⟩ : syracuseStep 3614215 = 5421323) B5421323
theorem B501359 : Blo 499793 501359 := bstep (se 1 (by rfl) ⟨376019, by rfl⟩ : syracuseStep 501359 = 752039) B752039
theorem B2533031 : Blo 499793 2533031 := bstep (se 1 (by rfl) ⟨1899773, by rfl⟩ : syracuseStep 2533031 = 3799547) B3799547
theorem B501415 : Blo 499793 501415 := bstep (se 1 (by rfl) ⟨376061, by rfl⟩ : syracuseStep 501415 = 752123) B752123
theorem B501499 : Blo 499793 501499 := bstep (se 1 (by rfl) ⟨376124, by rfl⟩ : syracuseStep 501499 = 752249) B752249
theorem B5154563 : Blo 499793 5154563 := bstep (se 1 (by rfl) ⟨3865922, by rfl⟩ : syracuseStep 5154563 = 7731845) B7731845
theorem B16262927 : Blo 499793 16262927 := bstep (se 1 (by rfl) ⟨12197195, by rfl⟩ : syracuseStep 16262927 = 24394391) B24394391
theorem B7251727 : Blo 499793 7251727 := bstep (se 1 (by rfl) ⟨5438795, by rfl⟩ : syracuseStep 7251727 = 10877591) B10877591
theorem B501535 : Blo 499793 501535 := bstep (se 1 (by rfl) ⟨376151, by rfl⟩ : syracuseStep 501535 = 752303) B752303
theorem B501567 : Blo 499793 501567 := bstep (se 1 (by rfl) ⟨376175, by rfl⟩ : syracuseStep 501567 = 752351) B752351
theorem B2533193 : Blo 499793 2533193 := bstep (se 2 (by rfl) ⟨949947, by rfl⟩ : syracuseStep 2533193 = 1899895) B1899895
theorem B501743 : Blo 499793 501743 := bstep (se 1 (by rfl) ⟨376307, by rfl⟩ : syracuseStep 501743 = 752615) B752615
theorem B7219205 : Blo 499793 7219205 := bstep (se 4 (by rfl) ⟨676800, by rfl⟩ : syracuseStep 7219205 = 1353601) B1353601
theorem B3221657 : Blo 499793 3221657 := bstep (se 2 (by rfl) ⟨1208121, by rfl⟩ : syracuseStep 3221657 = 2416243) B2416243
theorem B501915 : Blo 499793 501915 := bstep (se 1 (by rfl) ⟨376436, by rfl⟩ : syracuseStep 501915 = 752873) B752873
theorem B501951 : Blo 499793 501951 := bstep (se 1 (by rfl) ⟨376463, by rfl⟩ : syracuseStep 501951 = 752927) B752927
theorem B502063 : Blo 499793 502063 := bstep (se 1 (by rfl) ⟨376547, by rfl⟩ : syracuseStep 502063 = 753095) B753095
theorem B5220865 : Blo 499793 5220865 := bstep (se 2 (by rfl) ⟨1957824, by rfl⟩ : syracuseStep 5220865 = 3915649) B3915649
theorem B1124891 : Blo 499793 1124891 := bstep (se 1 (by rfl) ⟨843668, by rfl⟩ : syracuseStep 1124891 = 1687337) B1687337
theorem B502299 : Blo 499793 502299 := bstep (se 1 (by rfl) ⟨376724, by rfl⟩ : syracuseStep 502299 = 753449) B753449
theorem B502303 : Blo 499793 502303 := bstep (se 1 (by rfl) ⟨376727, by rfl⟩ : syracuseStep 502303 = 753455) B753455
theorem B5712443 : Blo 499793 5712443 := bstep (se 1 (by rfl) ⟨4284332, by rfl⟩ : syracuseStep 5712443 = 8568665) B8568665
theorem B2173511 : Blo 499793 2173511 := bstep (se 1 (by rfl) ⟨1630133, by rfl⟩ : syracuseStep 2173511 = 3260267) B3260267
theorem B4074299 : Blo 499793 4074299 := bstep (se 1 (by rfl) ⟨3055724, by rfl⟩ : syracuseStep 4074299 = 6111449) B6111449
theorem B502619 : Blo 499793 502619 := bstep (se 1 (by rfl) ⟨376964, by rfl⟩ : syracuseStep 502619 = 753929) B753929
theorem B502687 : Blo 499793 502687 := bstep (se 1 (by rfl) ⟨377015, by rfl⟩ : syracuseStep 502687 = 754031) B754031
theorem B633835 : Blo 499793 633835 := bstep (se 1 (by rfl) ⟨475376, by rfl⟩ : syracuseStep 633835 = 950753) B950753
theorem B502831 : Blo 499793 502831 := bstep (se 1 (by rfl) ⟨377123, by rfl⟩ : syracuseStep 502831 = 754247) B754247
theorem B502855 : Blo 499793 502855 := bstep (se 1 (by rfl) ⟨377141, by rfl⟩ : syracuseStep 502855 = 754283) B754283
theorem B2862215 : Blo 499793 2862215 := bstep (se 1 (by rfl) ⟨2146661, by rfl⟩ : syracuseStep 2862215 = 4293323) B4293323
theorem B503007 : Blo 499793 503007 := bstep (se 1 (by rfl) ⟨377255, by rfl⟩ : syracuseStep 503007 = 754511) B754511
theorem B1256887 : Blo 499793 1256887 := bstep (se 1 (by rfl) ⟨942665, by rfl⟩ : syracuseStep 1256887 = 1885331) B1885331
theorem B503271 : Blo 499793 503271 := bstep (se 1 (by rfl) ⟨377453, by rfl⟩ : syracuseStep 503271 = 754907) B754907
theorem B503387 : Blo 499793 503387 := bstep (se 1 (by rfl) ⟨377540, by rfl⟩ : syracuseStep 503387 = 755081) B755081
theorem B503623 : Blo 499793 503623 := bstep (se 1 (by rfl) ⟨377717, by rfl⟩ : syracuseStep 503623 = 755435) B755435
theorem B1126367 : Blo 499793 1126367 := bstep (se 1 (by rfl) ⟨844775, by rfl⟩ : syracuseStep 1126367 = 1689551) B1689551
theorem B503775 : Blo 499793 503775 := bstep (se 1 (by rfl) ⟨377831, by rfl⟩ : syracuseStep 503775 = 755663) B755663
theorem B3813641 : Blo 499793 3813641 := bstep (se 2 (by rfl) ⟨1430115, by rfl⟩ : syracuseStep 3813641 = 2860231) B2860231
theorem B2142713 : Blo 499793 2142713 := bstep (se 2 (by rfl) ⟨803517, by rfl⟩ : syracuseStep 2142713 = 1607035) B1607035
theorem B1127015 : Blo 499793 1127015 := bstep (se 1 (by rfl) ⟨845261, by rfl⟩ : syracuseStep 1127015 = 1690523) B1690523
theorem B1127699 : Blo 499793 1127699 := bstep (se 1 (by rfl) ⟨845774, by rfl⟩ : syracuseStep 1127699 = 1691549) B1691549
theorem B1127771 : Blo 499793 1127771 := bstep (se 1 (by rfl) ⟨845828, by rfl⟩ : syracuseStep 1127771 = 1691657) B1691657
theorem B2143979 : Blo 499793 2143979 := bstep (se 1 (by rfl) ⟨1607984, by rfl⟩ : syracuseStep 2143979 = 3215969) B3215969
theorem B1128329 : Blo 499793 1128329 := bstep (se 2 (by rfl) ⟨423123, by rfl⟩ : syracuseStep 1128329 = 846247) B846247
theorem B2144339 : Blo 499793 2144339 := bstep (se 1 (by rfl) ⟨1608254, by rfl⟩ : syracuseStep 2144339 = 3216509) B3216509
theorem B1128545 : Blo 499793 1128545 := bstep (se 2 (by rfl) ⟨423204, by rfl⟩ : syracuseStep 1128545 = 846409) B846409
theorem B3422579 : Blo 499793 3422579 := bstep (se 1 (by rfl) ⟨2566934, by rfl⟩ : syracuseStep 3422579 = 5133869) B5133869
theorem B16071443 : Blo 499793 16071443 := bstep (se 1 (by rfl) ⟨12053582, by rfl⟩ : syracuseStep 16071443 = 24107165) B24107165
theorem B1719119 : Blo 499793 1719119 := bstep (se 1 (by rfl) ⟨1289339, by rfl⟩ : syracuseStep 1719119 = 2578679) B2578679
theorem B1424375 : Blo 499793 1424375 := bstep (se 1 (by rfl) ⟨1068281, by rfl⟩ : syracuseStep 1424375 = 2136563) B2136563
theorem B4275449 : Blo 499793 4275449 := bstep (se 2 (by rfl) ⟨1603293, by rfl⟩ : syracuseStep 4275449 = 3206587) B3206587
theorem B802057 : Blo 499793 802057 := bstep (se 2 (by rfl) ⟨300771, by rfl⟩ : syracuseStep 802057 = 601543) B601543
theorem B1129895 : Blo 499793 1129895 := bstep (se 1 (by rfl) ⟨847421, by rfl⟩ : syracuseStep 1129895 = 1694843) B1694843
theorem B1130075 : Blo 499793 1130075 := bstep (se 1 (by rfl) ⟨847556, by rfl⟩ : syracuseStep 1130075 = 1695113) B1695113
theorem B1687283 : Blo 499793 1687283 := bstep (se 1 (by rfl) ⟨1265462, by rfl⟩ : syracuseStep 1687283 = 2530925) B2530925
theorem B1130363 : Blo 499793 1130363 := bstep (se 1 (by rfl) ⟨847772, by rfl⟩ : syracuseStep 1130363 = 1695545) B1695545
theorem B2146337 : Blo 499793 2146337 := bstep (se 2 (by rfl) ⟨804876, by rfl⟩ : syracuseStep 2146337 = 1609753) B1609753
theorem B11878487 : Blo 499793 11878487 := bstep (se 1 (by rfl) ⟨8908865, by rfl⟩ : syracuseStep 11878487 = 17817731) B17817731
theorem B2867339 : Blo 499793 2867339 := bstep (se 1 (by rfl) ⟨2150504, by rfl⟩ : syracuseStep 2867339 = 4301009) B4301009
theorem B1130849 : Blo 499793 1130849 := bstep (se 2 (by rfl) ⟨424068, by rfl⟩ : syracuseStep 1130849 = 848137) B848137
theorem B1130939 : Blo 499793 1130939 := bstep (se 1 (by rfl) ⟨848204, by rfl⟩ : syracuseStep 1130939 = 1696409) B1696409
theorem B4080071 : Blo 499793 4080071 := bstep (se 1 (by rfl) ⟨3060053, by rfl⟩ : syracuseStep 4080071 = 6120107) B6120107
theorem B2704175 : Blo 499793 2704175 := bstep (se 1 (by rfl) ⟨2028131, by rfl⟩ : syracuseStep 2704175 = 4056263) B4056263
theorem B23250199 : Blo 499793 23250199 := bstep (se 1 (by rfl) ⟨17437649, by rfl⟩ : syracuseStep 23250199 = 34875299) B34875299
theorem B1426859 : Blo 499793 1426859 := bstep (se 1 (by rfl) ⟨1070144, by rfl⟩ : syracuseStep 1426859 = 2140289) B2140289
theorem B2147755 : Blo 499793 2147755 := bstep (se 1 (by rfl) ⟨1610816, by rfl⟩ : syracuseStep 2147755 = 3221633) B3221633
theorem B1131947 : Blo 499793 1131947 := bstep (se 1 (by rfl) ⟨848960, by rfl⟩ : syracuseStep 1131947 = 1697921) B1697921
theorem B4081175 : Blo 499793 4081175 := bstep (se 1 (by rfl) ⟨3060881, by rfl⟩ : syracuseStep 4081175 = 6121763) B6121763
theorem B24823331 : Blo 499793 24823331 := bstep (se 1 (by rfl) ⟨18617498, by rfl⟩ : syracuseStep 24823331 = 37234997) B37234997
theorem B1132199 : Blo 499793 1132199 := bstep (se 1 (by rfl) ⟨849149, by rfl⟩ : syracuseStep 1132199 = 1698299) B1698299
theorem B1132487 : Blo 499793 1132487 := bstep (se 1 (by rfl) ⟨849365, by rfl⟩ : syracuseStep 1132487 = 1698731) B1698731
theorem B2541779 : Blo 499793 2541779 := bstep (se 1 (by rfl) ⟨1906334, by rfl⟩ : syracuseStep 2541779 = 3812669) B3812669
theorem B1132793 : Blo 499793 1132793 := bstep (se 2 (by rfl) ⟨424797, by rfl⟩ : syracuseStep 1132793 = 849595) B849595
theorem B1132847 : Blo 499793 1132847 := bstep (se 1 (by rfl) ⟨849635, by rfl⟩ : syracuseStep 1132847 = 1699271) B1699271
theorem B8669645 : Blo 499793 8669645 := bstep (se 3 (by rfl) ⟨1625558, by rfl⟩ : syracuseStep 8669645 = 3251117) B3251117
theorem B1427975 : Blo 499793 1427975 := bstep (se 1 (by rfl) ⟨1070981, by rfl⟩ : syracuseStep 1427975 = 2141963) B2141963
theorem B1133063 : Blo 499793 1133063 := bstep (se 1 (by rfl) ⟨849797, by rfl⟩ : syracuseStep 1133063 = 1699595) B1699595
theorem B3426961 : Blo 499793 3426961 := bstep (se 2 (by rfl) ⟨1285110, by rfl⟩ : syracuseStep 3426961 = 2570221) B2570221
theorem B2411153 : Blo 499793 2411153 := bstep (se 2 (by rfl) ⟨904182, by rfl⟩ : syracuseStep 2411153 = 1808365) B1808365
theorem B1133243 : Blo 499793 1133243 := bstep (se 1 (by rfl) ⟨849932, by rfl⟩ : syracuseStep 1133243 = 1699865) B1699865
theorem B1690847 : Blo 499793 1690847 := bstep (se 1 (by rfl) ⟨1268135, by rfl⟩ : syracuseStep 1690847 = 2536271) B2536271
theorem B1691063 : Blo 499793 1691063 := bstep (se 1 (by rfl) ⟨1268297, by rfl⟩ : syracuseStep 1691063 = 2536595) B2536595
theorem B4279823 : Blo 499793 4279823 := bstep (se 1 (by rfl) ⟨3209867, by rfl⟩ : syracuseStep 4279823 = 6419735) B6419735
theorem B27512459 : Blo 499793 27512459 := bstep (se 1 (by rfl) ⟨20634344, by rfl⟩ : syracuseStep 27512459 = 41268689) B41268689
theorem B2543399 : Blo 499793 2543399 := bstep (se 1 (by rfl) ⟨1907549, by rfl⟩ : syracuseStep 2543399 = 3815099) B3815099
theorem B3821417 : Blo 499793 3821417 := bstep (se 2 (by rfl) ⟨1433031, by rfl⟩ : syracuseStep 3821417 = 2866063) B2866063
theorem B2413151 : Blo 499793 2413151 := bstep (se 1 (by rfl) ⟨1809863, by rfl⟩ : syracuseStep 2413151 = 3619727) B3619727
theorem B3429371 : Blo 499793 3429371 := bstep (se 1 (by rfl) ⟨2572028, by rfl⟩ : syracuseStep 3429371 = 5144057) B5144057
theorem B2544695 : Blo 499793 2544695 := bstep (se 1 (by rfl) ⟨1908521, by rfl⟩ : syracuseStep 2544695 = 3817043) B3817043
theorem B4805729 : Blo 499793 4805729 := bstep (se 2 (by rfl) ⟨1802148, by rfl⟩ : syracuseStep 4805729 = 3604297) B3604297
theorem B1693115 : Blo 499793 1693115 := bstep (se 1 (by rfl) ⟨1269836, by rfl⟩ : syracuseStep 1693115 = 2539673) B2539673
theorem B1693655 : Blo 499793 1693655 := bstep (se 1 (by rfl) ⟨1270241, by rfl⟩ : syracuseStep 1693655 = 2540483) B2540483
theorem B2414551 : Blo 499793 2414551 := bstep (se 1 (by rfl) ⟨1810913, by rfl⟩ : syracuseStep 2414551 = 3621827) B3621827
theorem B26368409 : Blo 499793 26368409 := bstep (se 2 (by rfl) ⟨9888153, by rfl⟩ : syracuseStep 26368409 = 19776307) B19776307
theorem B1694141 : Blo 499793 1694141 := bstep (se 3 (by rfl) ⟨317651, by rfl⟩ : syracuseStep 1694141 = 635303) B635303
theorem B1432201 : Blo 499793 1432201 := bstep (se 2 (by rfl) ⟨537075, by rfl⟩ : syracuseStep 1432201 = 1074151) B1074151
theorem B6413377 : Blo 499793 6413377 := bstep (se 2 (by rfl) ⟨2405016, by rfl⟩ : syracuseStep 6413377 = 4810033) B4810033
theorem B1695005 : Blo 499793 1695005 := bstep (se 3 (by rfl) ⟨317813, by rfl⟩ : syracuseStep 1695005 = 635627) B635627
theorem B1269391 : Blo 499793 1269391 := bstep (se 1 (by rfl) ⟨952043, by rfl⟩ : syracuseStep 1269391 = 1904087) B1904087
theorem B843439 : Blo 499793 843439 := bstep (se 1 (by rfl) ⟨632579, by rfl⟩ : syracuseStep 843439 = 1265159) B1265159
theorem B6119185 : Blo 499793 6119185 := bstep (se 2 (by rfl) ⟨2294694, by rfl⟩ : syracuseStep 6119185 = 4589389) B4589389
theorem B1433533 : Blo 499793 1433533 := bstep (se 3 (by rfl) ⟨268787, by rfl⟩ : syracuseStep 1433533 = 537575) B537575
theorem B843743 : Blo 499793 843743 := bstep (se 1 (by rfl) ⟨632807, by rfl⟩ : syracuseStep 843743 = 1265615) B1265615
theorem B1696031 : Blo 499793 1696031 := bstep (se 1 (by rfl) ⟨1272023, by rfl⟩ : syracuseStep 1696031 = 2544047) B2544047
theorem B844087 : Blo 499793 844087 := bstep (se 1 (by rfl) ⟨633065, by rfl⟩ : syracuseStep 844087 = 1266131) B1266131
theorem B1204577 : Blo 499793 1204577 := bstep (se 2 (by rfl) ⟨451716, by rfl⟩ : syracuseStep 1204577 = 903433) B903433
theorem B8577413 : Blo 499793 8577413 := bstep (se 4 (by rfl) ⟨804132, by rfl⟩ : syracuseStep 8577413 = 1608265) B1608265
theorem B844391 : Blo 499793 844391 := bstep (se 1 (by rfl) ⟨633293, by rfl⟩ : syracuseStep 844391 = 1266587) B1266587
theorem B17621651 : Blo 499793 17621651 := bstep (se 1 (by rfl) ⟨13216238, by rfl⟩ : syracuseStep 17621651 = 26432477) B26432477
theorem B844553 : Blo 499793 844553 := bstep (se 2 (by rfl) ⟨316707, by rfl⟩ : syracuseStep 844553 = 633415) B633415
theorem B2483099 : Blo 499793 2483099 := bstep (se 1 (by rfl) ⟨1862324, by rfl⟩ : syracuseStep 2483099 = 3724649) B3724649
theorem B1696679 : Blo 499793 1696679 := bstep (se 1 (by rfl) ⟨1272509, by rfl⟩ : syracuseStep 1696679 = 2545019) B2545019
theorem B1270991 : Blo 499793 1270991 := bstep (se 1 (by rfl) ⟨953243, by rfl⟩ : syracuseStep 1270991 = 1906487) B1906487
theorem B845147 : Blo 499793 845147 := bstep (se 1 (by rfl) ⟨633860, by rfl⟩ : syracuseStep 845147 = 1267721) B1267721
theorem B1697273 : Blo 499793 1697273 := bstep (se 2 (by rfl) ⟨636477, by rfl⟩ : syracuseStep 1697273 = 1272955) B1272955
theorem B1271315 : Blo 499793 1271315 := bstep (se 1 (by rfl) ⟨953486, by rfl⟩ : syracuseStep 1271315 = 1906973) B1906973
theorem B845383 : Blo 499793 845383 := bstep (se 1 (by rfl) ⟨634037, by rfl⟩ : syracuseStep 845383 = 1268075) B1268075
theorem B2713171 : Blo 499793 2713171 := bstep (se 1 (by rfl) ⟨2034878, by rfl⟩ : syracuseStep 2713171 = 4069757) B4069757
theorem B1074809 : Blo 499793 1074809 := bstep (se 2 (by rfl) ⟨403053, by rfl⟩ : syracuseStep 1074809 = 806107) B806107
theorem B9791165 : Blo 499793 9791165 := bstep (se 3 (by rfl) ⟨1835843, by rfl⟩ : syracuseStep 9791165 = 3671687) B3671687
theorem B1140443 : Blo 499793 1140443 := bstep (se 1 (by rfl) ⟨855332, by rfl⟩ : syracuseStep 1140443 = 1710665) B1710665
theorem B2746075 : Blo 499793 2746075 := bstep (se 1 (by rfl) ⟨2059556, by rfl⟩ : syracuseStep 2746075 = 4119113) B4119113
theorem B1697543 : Blo 499793 1697543 := bstep (se 1 (by rfl) ⟨1273157, by rfl⟩ : syracuseStep 1697543 = 2546315) B2546315
theorem B845599 : Blo 499793 845599 := bstep (se 1 (by rfl) ⟨634199, by rfl⟩ : syracuseStep 845599 = 1268399) B1268399
theorem B1697597 : Blo 499793 1697597 := bstep (se 3 (by rfl) ⟨318299, by rfl⟩ : syracuseStep 1697597 = 636599) B636599
theorem B845815 : Blo 499793 845815 := bstep (se 1 (by rfl) ⟨634361, by rfl⟩ : syracuseStep 845815 = 1268723) B1268723
theorem B846119 : Blo 499793 846119 := bstep (se 1 (by rfl) ⟨634589, by rfl⟩ : syracuseStep 846119 = 1269179) B1269179
theorem B43379003 : Blo 499793 43379003 := bstep (se 1 (by rfl) ⟨32534252, by rfl⟩ : syracuseStep 43379003 = 65068505) B65068505
theorem B1075817 : Blo 499793 1075817 := bstep (se 2 (by rfl) ⟨403431, by rfl⟩ : syracuseStep 1075817 = 806863) B806863
theorem B3795659 : Blo 499793 3795659 := bstep (se 1 (by rfl) ⟨2846744, by rfl⟩ : syracuseStep 3795659 = 5693489) B5693489
theorem B1272631 : Blo 499793 1272631 := bstep (se 1 (by rfl) ⟨954473, by rfl⟩ : syracuseStep 1272631 = 1908947) B1908947
theorem B846895 : Blo 499793 846895 := bstep (se 1 (by rfl) ⟨635171, by rfl⟩ : syracuseStep 846895 = 1270343) B1270343
theorem B3206279 : Blo 499793 3206279 := bstep (se 1 (by rfl) ⟨2404709, by rfl⟩ : syracuseStep 3206279 = 4809419) B4809419
theorem B2583895 : Blo 499793 2583895 := bstep (se 1 (by rfl) ⟨1937921, by rfl⟩ : syracuseStep 2583895 = 3875843) B3875843
theorem B847273 : Blo 499793 847273 := bstep (se 2 (by rfl) ⟨317727, by rfl⟩ : syracuseStep 847273 = 635455) B635455
theorem B847739 : Blo 499793 847739 := bstep (se 1 (by rfl) ⟨635804, by rfl⟩ : syracuseStep 847739 = 1271609) B1271609
theorem B2584493 : Blo 499793 2584493 := bstep (se 3 (by rfl) ⟨484592, by rfl⟩ : syracuseStep 2584493 = 969185) B969185
theorem B1700027 : Blo 499793 1700027 := bstep (se 1 (by rfl) ⟨1275020, by rfl⟩ : syracuseStep 1700027 = 2550041) B2550041
theorem B749855 : Blo 499793 749855 := bstep (se 1 (by rfl) ⟨562391, by rfl⟩ : syracuseStep 749855 = 1124783) B1124783
theorem B749879 : Blo 499793 749879 := bstep (se 1 (by rfl) ⟨562409, by rfl⟩ : syracuseStep 749879 = 1124819) B1124819
theorem B749951 : Blo 499793 749951 := bstep (se 1 (by rfl) ⟨562463, by rfl⟩ : syracuseStep 749951 = 1124927) B1124927
theorem B750023 : Blo 499793 750023 := bstep (se 1 (by rfl) ⟨562517, by rfl⟩ : syracuseStep 750023 = 1125035) B1125035
theorem B7205597 : Blo 499793 7205597 := bstep (se 3 (by rfl) ⟨1351049, by rfl⟩ : syracuseStep 7205597 = 2702099) B2702099
theorem B750377 : Blo 499793 750377 := bstep (se 2 (by rfl) ⟨281391, by rfl⟩ : syracuseStep 750377 = 562783) B562783
theorem B783145 : Blo 499793 783145 := bstep (se 2 (by rfl) ⟨293679, by rfl⟩ : syracuseStep 783145 = 587359) B587359
theorem B750383 : Blo 499793 750383 := bstep (se 1 (by rfl) ⟨562787, by rfl⟩ : syracuseStep 750383 = 1125575) B1125575
theorem B881455 : Blo 499793 881455 := bstep (se 1 (by rfl) ⟨661091, by rfl⟩ : syracuseStep 881455 = 1322183) B1322183
theorem B750503 : Blo 499793 750503 := bstep (se 1 (by rfl) ⟨562877, by rfl⟩ : syracuseStep 750503 = 1125755) B1125755
theorem B750587 : Blo 499793 750587 := bstep (se 1 (by rfl) ⟨562940, by rfl⟩ : syracuseStep 750587 = 1125881) B1125881
theorem B750647 : Blo 499793 750647 := bstep (se 1 (by rfl) ⟨562985, by rfl⟩ : syracuseStep 750647 = 1125971) B1125971
theorem B3798089 : Blo 499793 3798089 := bstep (se 2 (by rfl) ⟨1424283, by rfl⟩ : syracuseStep 3798089 = 2848567) B2848567
theorem B849001 : Blo 499793 849001 := bstep (se 2 (by rfl) ⟨318375, by rfl⟩ : syracuseStep 849001 = 636751) B636751
theorem B750767 : Blo 499793 750767 := bstep (se 1 (by rfl) ⟨563075, by rfl⟩ : syracuseStep 750767 = 1126151) B1126151
theorem B7206407 : Blo 499793 7206407 := bstep (se 1 (by rfl) ⟨5404805, by rfl⟩ : syracuseStep 7206407 = 10809611) B10809611
theorem B6452743 : Blo 499793 6452743 := bstep (se 1 (by rfl) ⟨4839557, by rfl⟩ : syracuseStep 6452743 = 9679115) B9679115
theorem B751175 : Blo 499793 751175 := bstep (se 1 (by rfl) ⟨563381, by rfl⟩ : syracuseStep 751175 = 1126763) B1126763
theorem B751271 : Blo 499793 751271 := bstep (se 1 (by rfl) ⟨563453, by rfl⟩ : syracuseStep 751271 = 1126907) B1126907
theorem B849575 : Blo 499793 849575 := bstep (se 1 (by rfl) ⟨637181, by rfl⟩ : syracuseStep 849575 = 1274363) B1274363
theorem B751355 : Blo 499793 751355 := bstep (se 1 (by rfl) ⟨563516, by rfl⟩ : syracuseStep 751355 = 1127033) B1127033
theorem B751391 : Blo 499793 751391 := bstep (se 1 (by rfl) ⟨563543, by rfl⟩ : syracuseStep 751391 = 1127087) B1127087
theorem B751439 : Blo 499793 751439 := bstep (se 1 (by rfl) ⟨563579, by rfl⟩ : syracuseStep 751439 = 1127159) B1127159
theorem B751559 : Blo 499793 751559 := bstep (se 1 (by rfl) ⟨563669, by rfl⟩ : syracuseStep 751559 = 1127339) B1127339
theorem B1210351 : Blo 499793 1210351 := bstep (se 1 (by rfl) ⟨907763, by rfl⟩ : syracuseStep 1210351 = 1815527) B1815527
theorem B1603577 : Blo 499793 1603577 := bstep (se 2 (by rfl) ⟨601341, by rfl⟩ : syracuseStep 1603577 = 1202683) B1202683
theorem B751913 : Blo 499793 751913 := bstep (se 2 (by rfl) ⟨281967, by rfl⟩ : syracuseStep 751913 = 563935) B563935
theorem B751919 : Blo 499793 751919 := bstep (se 1 (by rfl) ⟨563939, by rfl⟩ : syracuseStep 751919 = 1127879) B1127879
theorem B4586003 : Blo 499793 4586003 := bstep (se 1 (by rfl) ⟨3439502, by rfl⟩ : syracuseStep 4586003 = 6879005) B6879005
theorem B752159 : Blo 499793 752159 := bstep (se 1 (by rfl) ⟨564119, by rfl⟩ : syracuseStep 752159 = 1128239) B1128239
theorem B3603143 : Blo 499793 3603143 := bstep (se 1 (by rfl) ⟨2702357, by rfl⟩ : syracuseStep 3603143 = 5404715) B5404715
theorem B949151 : Blo 499793 949151 := bstep (se 1 (by rfl) ⟨711863, by rfl⟩ : syracuseStep 949151 = 1423727) B1423727
theorem B752543 : Blo 499793 752543 := bstep (se 1 (by rfl) ⟨564407, by rfl⟩ : syracuseStep 752543 = 1128815) B1128815
theorem B752591 : Blo 499793 752591 := bstep (se 1 (by rfl) ⟨564443, by rfl⟩ : syracuseStep 752591 = 1128887) B1128887
theorem B752681 : Blo 499793 752681 := bstep (se 2 (by rfl) ⟨282255, by rfl⟩ : syracuseStep 752681 = 564511) B564511
theorem B752687 : Blo 499793 752687 := bstep (se 1 (by rfl) ⟨564515, by rfl⟩ : syracuseStep 752687 = 1129031) B1129031
theorem B752711 : Blo 499793 752711 := bstep (se 1 (by rfl) ⟨564533, by rfl⟩ : syracuseStep 752711 = 1129067) B1129067
theorem B752975 : Blo 499793 752975 := bstep (se 1 (by rfl) ⟨564731, by rfl⟩ : syracuseStep 752975 = 1129463) B1129463
theorem B753065 : Blo 499793 753065 := bstep (se 2 (by rfl) ⟨282399, by rfl⟩ : syracuseStep 753065 = 564799) B564799
theorem B6094273 : Blo 499793 6094273 := bstep (se 2 (by rfl) ⟨2285352, by rfl⟩ : syracuseStep 6094273 = 4570705) B4570705
theorem B949735 : Blo 499793 949735 := bstep (se 1 (by rfl) ⟨712301, by rfl⟩ : syracuseStep 949735 = 1424603) B1424603
theorem B753215 : Blo 499793 753215 := bstep (se 1 (by rfl) ⟨564911, by rfl⟩ : syracuseStep 753215 = 1129823) B1129823
theorem B2850551 : Blo 499793 2850551 := bstep (se 1 (by rfl) ⟨2137913, by rfl⟩ : syracuseStep 2850551 = 4275827) B4275827
theorem B753479 : Blo 499793 753479 := bstep (se 1 (by rfl) ⟨565109, by rfl⟩ : syracuseStep 753479 = 1130219) B1130219
theorem B753563 : Blo 499793 753563 := bstep (se 1 (by rfl) ⟨565172, by rfl⟩ : syracuseStep 753563 = 1130345) B1130345
theorem B753899 : Blo 499793 753899 := bstep (se 1 (by rfl) ⟨565424, by rfl⟩ : syracuseStep 753899 = 1130849) B1130849
theorem B753959 : Blo 499793 753959 := bstep (se 1 (by rfl) ⟨565469, by rfl⟩ : syracuseStep 753959 = 1130939) B1130939
theorem B1802783 : Blo 499793 1802783 := bstep (se 1 (by rfl) ⟨1352087, by rfl⟩ : syracuseStep 1802783 = 2704175) B2704175
theorem B951239 : Blo 499793 951239 := bstep (se 1 (by rfl) ⟨713429, by rfl⟩ : syracuseStep 951239 = 1426859) B1426859
theorem B754631 : Blo 499793 754631 := bstep (se 1 (by rfl) ⟨565973, by rfl⟩ : syracuseStep 754631 = 1131947) B1131947
theorem B2720783 : Blo 499793 2720783 := bstep (se 1 (by rfl) ⟨2040587, by rfl⟩ : syracuseStep 2720783 = 4081175) B4081175
theorem B16548887 : Blo 499793 16548887 := bstep (se 1 (by rfl) ⟨12411665, by rfl⟩ : syracuseStep 16548887 = 24823331) B24823331
theorem B754799 : Blo 499793 754799 := bstep (se 1 (by rfl) ⟨566099, by rfl⟩ : syracuseStep 754799 = 1132199) B1132199
theorem B10880189 : Blo 499793 10880189 := bstep (se 3 (by rfl) ⟨2040035, by rfl⟩ : syracuseStep 10880189 = 4080071) B4080071
theorem B19596491 : Blo 499793 19596491 := bstep (se 1 (by rfl) ⟨14697368, by rfl⟩ : syracuseStep 19596491 = 29394737) B29394737
theorem B754991 : Blo 499793 754991 := bstep (se 1 (by rfl) ⟨566243, by rfl⟩ : syracuseStep 754991 = 1132487) B1132487
theorem B755195 : Blo 499793 755195 := bstep (se 1 (by rfl) ⟨566396, by rfl⟩ : syracuseStep 755195 = 1132793) B1132793
theorem B755231 : Blo 499793 755231 := bstep (se 1 (by rfl) ⟨566423, by rfl⟩ : syracuseStep 755231 = 1132847) B1132847
theorem B4687409 : Blo 499793 4687409 := bstep (se 2 (by rfl) ⟨1757778, by rfl⟩ : syracuseStep 4687409 = 3515557) B3515557
theorem B2328169 : Blo 499793 2328169 := bstep (se 2 (by rfl) ⟨873063, by rfl⟩ : syracuseStep 2328169 = 1746127) B1746127
theorem B951983 : Blo 499793 951983 := bstep (se 1 (by rfl) ⟨713987, by rfl⟩ : syracuseStep 951983 = 1427975) B1427975
theorem B755375 : Blo 499793 755375 := bstep (se 1 (by rfl) ⟨566531, by rfl⟩ : syracuseStep 755375 = 1133063) B1133063
theorem B31000265 : Blo 499793 31000265 := bstep (se 2 (by rfl) ⟨11625099, by rfl⟩ : syracuseStep 31000265 = 23250199) B23250199
theorem B1607435 : Blo 499793 1607435 := bstep (se 1 (by rfl) ⟨1205576, by rfl⟩ : syracuseStep 1607435 = 2411153) B2411153
theorem B755495 : Blo 499793 755495 := bstep (se 1 (by rfl) ⟨566621, by rfl⟩ : syracuseStep 755495 = 1133243) B1133243
theorem B4818953 : Blo 499793 4818953 := bstep (se 2 (by rfl) ⟨1807107, by rfl⟩ : syracuseStep 4818953 = 3614215) B3614215
theorem B6883379 : Blo 499793 6883379 := bstep (se 1 (by rfl) ⟨5162534, by rfl⟩ : syracuseStep 6883379 = 10325069) B10325069
theorem B2853215 : Blo 499793 2853215 := bstep (se 1 (by rfl) ⟨2139911, by rfl⟩ : syracuseStep 2853215 = 4279823) B4279823
theorem B9668969 : Blo 499793 9668969 := bstep (se 2 (by rfl) ⟨3625863, by rfl⟩ : syracuseStep 9668969 = 7251727) B7251727
theorem B5311115 : Blo 499793 5311115 := bstep (se 1 (by rfl) ⟨3983336, by rfl⟩ : syracuseStep 5311115 = 7966673) B7966673
theorem B1608767 : Blo 499793 1608767 := bstep (se 1 (by rfl) ⟨1206575, by rfl⟩ : syracuseStep 1608767 = 2413151) B2413151
theorem B36507509 : Blo 499793 36507509 := bstep (se 5 (by rfl) ⟨1711289, by rfl⟩ : syracuseStep 36507509 = 3422579) B3422579
theorem B4067615 : Blo 499793 4067615 := bstep (se 1 (by rfl) ⟨3050711, by rfl⟩ : syracuseStep 4067615 = 6101423) B6101423
theorem B3445193 : Blo 499793 3445193 := bstep (se 2 (by rfl) ⟨1291947, by rfl⟩ : syracuseStep 3445193 = 2583895) B2583895
theorem B3609143 : Blo 499793 3609143 := bstep (se 1 (by rfl) ⟨2706857, by rfl⟩ : syracuseStep 3609143 = 5413715) B5413715
theorem B8590535 : Blo 499793 8590535 := bstep (se 1 (by rfl) ⟨6442901, by rfl⟩ : syracuseStep 8590535 = 12885803) B12885803
theorem B562495 : Blo 499793 562495 := bstep (se 1 (by rfl) ⟨421871, by rfl⟩ : syracuseStep 562495 = 843743) B843743
theorem B1906031 : Blo 499793 1906031 := bstep (se 1 (by rfl) ⟨1429523, by rfl⟩ : syracuseStep 1906031 = 2859047) B2859047
theorem B562927 : Blo 499793 562927 := bstep (se 1 (by rfl) ⟨422195, by rfl⟩ : syracuseStep 562927 = 844391) B844391
theorem B563035 : Blo 499793 563035 := bstep (se 1 (by rfl) ⟨422276, by rfl⟩ : syracuseStep 563035 = 844553) B844553
theorem B115677341 : Blo 499793 115677341 := bstep (se 3 (by rfl) ⟨21689501, by rfl⟩ : syracuseStep 115677341 = 43379003) B43379003
theorem B563431 : Blo 499793 563431 := bstep (se 1 (by rfl) ⟨422573, by rfl⟩ : syracuseStep 563431 = 845147) B845147
theorem B760295 : Blo 499793 760295 := bstep (se 1 (by rfl) ⟨570221, by rfl⟩ : syracuseStep 760295 = 1140443) B1140443
theorem B564079 : Blo 499793 564079 := bstep (se 1 (by rfl) ⟨423059, by rfl⟩ : syracuseStep 564079 = 846119) B846119
theorem B3808295 : Blo 499793 3808295 := bstep (se 1 (by rfl) ⟨2856221, by rfl⟩ : syracuseStep 3808295 = 5712443) B5712443
theorem B2530439 : Blo 499793 2530439 := bstep (se 1 (by rfl) ⟨1897829, by rfl⟩ : syracuseStep 2530439 = 3795659) B3795659
theorem B9608381 : Blo 499793 9608381 := bstep (se 3 (by rfl) ⟨1801571, by rfl⟩ : syracuseStep 9608381 = 3603143) B3603143
theorem B2137519 : Blo 499793 2137519 := bstep (se 1 (by rfl) ⟨1603139, by rfl⟩ : syracuseStep 2137519 = 3206279) B3206279
theorem B1908143 : Blo 499793 1908143 := bstep (se 1 (by rfl) ⟨1431107, by rfl⟩ : syracuseStep 1908143 = 2862215) B2862215
theorem B565159 : Blo 499793 565159 := bstep (se 1 (by rfl) ⟨423869, by rfl⟩ : syracuseStep 565159 = 847739) B847739
theorem B3219401 : Blo 499793 3219401 := bstep (se 2 (by rfl) ⟨1207275, by rfl⟩ : syracuseStep 3219401 = 2414551) B2414551
theorem B1613801 : Blo 499793 1613801 := bstep (se 2 (by rfl) ⟨605175, by rfl⟩ : syracuseStep 1613801 = 1210351) B1210351
theorem B499903 : Blo 499793 499903 := bstep (se 1 (by rfl) ⟨374927, by rfl⟩ : syracuseStep 499903 = 749855) B749855
theorem B499919 : Blo 499793 499919 := bstep (se 1 (by rfl) ⟨374939, by rfl⟩ : syracuseStep 499919 = 749879) B749879
theorem B499967 : Blo 499793 499967 := bstep (se 1 (by rfl) ⟨374975, by rfl⟩ : syracuseStep 499967 = 749951) B749951
theorem B500015 : Blo 499793 500015 := bstep (se 1 (by rfl) ⟨375011, by rfl⟩ : syracuseStep 500015 = 750023) B750023
theorem B500251 : Blo 499793 500251 := bstep (se 1 (by rfl) ⟨375188, by rfl⟩ : syracuseStep 500251 = 750377) B750377
theorem B500255 : Blo 499793 500255 := bstep (se 1 (by rfl) ⟨375191, by rfl⟩ : syracuseStep 500255 = 750383) B750383
theorem B500335 : Blo 499793 500335 := bstep (se 1 (by rfl) ⟨375251, by rfl⟩ : syracuseStep 500335 = 750503) B750503
theorem B500391 : Blo 499793 500391 := bstep (se 1 (by rfl) ⟨375293, by rfl⟩ : syracuseStep 500391 = 750587) B750587
theorem B500431 : Blo 499793 500431 := bstep (se 1 (by rfl) ⟨375323, by rfl⟩ : syracuseStep 500431 = 750647) B750647
theorem B2532059 : Blo 499793 2532059 := bstep (se 1 (by rfl) ⟨1899044, by rfl⟩ : syracuseStep 2532059 = 3798089) B3798089
theorem B500511 : Blo 499793 500511 := bstep (se 1 (by rfl) ⟨375383, by rfl⟩ : syracuseStep 500511 = 750767) B750767
theorem B1909601 : Blo 499793 1909601 := bstep (se 2 (by rfl) ⟨716100, by rfl⟩ : syracuseStep 1909601 = 1432201) B1432201
theorem B500783 : Blo 499793 500783 := bstep (se 1 (by rfl) ⟨375587, by rfl⟩ : syracuseStep 500783 = 751175) B751175
theorem B500847 : Blo 499793 500847 := bstep (se 1 (by rfl) ⟨375635, by rfl⟩ : syracuseStep 500847 = 751271) B751271
theorem B566383 : Blo 499793 566383 := bstep (se 1 (by rfl) ⟨424787, by rfl⟩ : syracuseStep 566383 = 849575) B849575
theorem B500903 : Blo 499793 500903 := bstep (se 1 (by rfl) ⟨375677, by rfl⟩ : syracuseStep 500903 = 751355) B751355
theorem B500927 : Blo 499793 500927 := bstep (se 1 (by rfl) ⟨375695, by rfl⟩ : syracuseStep 500927 = 751391) B751391
theorem B500959 : Blo 499793 500959 := bstep (se 1 (by rfl) ⟨375719, by rfl⟩ : syracuseStep 500959 = 751439) B751439
theorem B501039 : Blo 499793 501039 := bstep (se 1 (by rfl) ⟨375779, by rfl⟩ : syracuseStep 501039 = 751559) B751559
theorem B501275 : Blo 499793 501275 := bstep (se 1 (by rfl) ⟨375956, by rfl⟩ : syracuseStep 501275 = 751913) B751913
theorem B501279 : Blo 499793 501279 := bstep (se 1 (by rfl) ⟨375959, by rfl⟩ : syracuseStep 501279 = 751919) B751919
theorem B3057335 : Blo 499793 3057335 := bstep (se 1 (by rfl) ⟨2293001, by rfl⟩ : syracuseStep 3057335 = 4586003) B4586003
theorem B501439 : Blo 499793 501439 := bstep (se 1 (by rfl) ⟨376079, by rfl⟩ : syracuseStep 501439 = 752159) B752159
theorem B2467757 : Blo 499793 2467757 := bstep (se 3 (by rfl) ⟨462704, by rfl⟩ : syracuseStep 2467757 = 925409) B925409
theorem B632767 : Blo 499793 632767 := bstep (se 1 (by rfl) ⟨474575, by rfl⟩ : syracuseStep 632767 = 949151) B949151
theorem B501695 : Blo 499793 501695 := bstep (se 1 (by rfl) ⟨376271, by rfl⟩ : syracuseStep 501695 = 752543) B752543
theorem B501727 : Blo 499793 501727 := bstep (se 1 (by rfl) ⟨376295, by rfl⟩ : syracuseStep 501727 = 752591) B752591
theorem B501787 : Blo 499793 501787 := bstep (se 1 (by rfl) ⟨376340, by rfl⟩ : syracuseStep 501787 = 752681) B752681
theorem B501791 : Blo 499793 501791 := bstep (se 1 (by rfl) ⟨376343, by rfl⟩ : syracuseStep 501791 = 752687) B752687
theorem B501807 : Blo 499793 501807 := bstep (se 1 (by rfl) ⟨376355, by rfl⟩ : syracuseStep 501807 = 752711) B752711
theorem B501983 : Blo 499793 501983 := bstep (se 1 (by rfl) ⟨376487, by rfl⟩ : syracuseStep 501983 = 752975) B752975
theorem B1124585 : Blo 499793 1124585 := bstep (se 2 (by rfl) ⟨421719, by rfl⟩ : syracuseStep 1124585 = 843439) B843439
theorem B502043 : Blo 499793 502043 := bstep (se 1 (by rfl) ⟨376532, by rfl⟩ : syracuseStep 502043 = 753065) B753065
theorem B502143 : Blo 499793 502143 := bstep (se 1 (by rfl) ⟨376607, by rfl⟩ : syracuseStep 502143 = 753215) B753215
theorem B1124855 : Blo 499793 1124855 := bstep (se 1 (by rfl) ⟨843641, by rfl⟩ : syracuseStep 1124855 = 1687283) B1687283
theorem B502319 : Blo 499793 502319 := bstep (se 1 (by rfl) ⟨376739, by rfl⟩ : syracuseStep 502319 = 753479) B753479
theorem B1911377 : Blo 499793 1911377 := bstep (se 2 (by rfl) ⟨716766, by rfl⟩ : syracuseStep 1911377 = 1433533) B1433533
theorem B502375 : Blo 499793 502375 := bstep (se 1 (by rfl) ⟨376781, by rfl⟩ : syracuseStep 502375 = 753563) B753563
theorem B1911559 : Blo 499793 1911559 := bstep (se 1 (by rfl) ⟨1433669, by rfl⟩ : syracuseStep 1911559 = 2867339) B2867339
theorem B502751 : Blo 499793 502751 := bstep (se 1 (by rfl) ⟨377063, by rfl⟩ : syracuseStep 502751 = 754127) B754127
theorem B502779 : Blo 499793 502779 := bstep (se 1 (by rfl) ⟨377084, by rfl⟩ : syracuseStep 502779 = 754169) B754169
theorem B502847 : Blo 499793 502847 := bstep (se 1 (by rfl) ⟨377135, by rfl⟩ : syracuseStep 502847 = 754271) B754271
theorem B1125449 : Blo 499793 1125449 := bstep (se 2 (by rfl) ⟨422043, by rfl⟩ : syracuseStep 1125449 = 844087) B844087
theorem B1223849 : Blo 499793 1223849 := bstep (se 2 (by rfl) ⟨458943, by rfl⟩ : syracuseStep 1223849 = 917887) B917887
theorem B503167 : Blo 499793 503167 := bstep (se 1 (by rfl) ⟨377375, by rfl⟩ : syracuseStep 503167 = 754751) B754751
theorem B503195 : Blo 499793 503195 := bstep (se 1 (by rfl) ⟨377396, by rfl⟩ : syracuseStep 503195 = 754793) B754793
theorem B503263 : Blo 499793 503263 := bstep (se 1 (by rfl) ⟨377447, by rfl⟩ : syracuseStep 503263 = 754895) B754895
theorem B2534975 : Blo 499793 2534975 := bstep (se 1 (by rfl) ⟨1901231, by rfl⟩ : syracuseStep 2534975 = 3802463) B3802463
theorem B8564291 : Blo 499793 8564291 := bstep (se 1 (by rfl) ⟨6423218, by rfl⟩ : syracuseStep 8564291 = 12846437) B12846437
theorem B503399 : Blo 499793 503399 := bstep (se 1 (by rfl) ⟨377549, by rfl⟩ : syracuseStep 503399 = 755099) B755099
theorem B503547 : Blo 499793 503547 := bstep (se 1 (by rfl) ⟨377660, by rfl⟩ : syracuseStep 503547 = 755321) B755321
theorem B503615 : Blo 499793 503615 := bstep (se 1 (by rfl) ⟨377711, by rfl⟩ : syracuseStep 503615 = 755423) B755423
theorem B32550761 : Blo 499793 32550761 := bstep (se 2 (by rfl) ⟨12206535, by rfl⟩ : syracuseStep 32550761 = 24413071) B24413071
theorem B503679 : Blo 499793 503679 := bstep (se 1 (by rfl) ⟨377759, by rfl⟩ : syracuseStep 503679 = 755519) B755519
theorem B5713901 : Blo 499793 5713901 := bstep (se 3 (by rfl) ⟨1071356, by rfl⟩ : syracuseStep 5713901 = 2142713) B2142713
theorem B503791 : Blo 499793 503791 := bstep (se 1 (by rfl) ⟨377843, by rfl⟩ : syracuseStep 503791 = 755687) B755687
theorem B5779763 : Blo 499793 5779763 := bstep (se 1 (by rfl) ⟨4334822, by rfl⟩ : syracuseStep 5779763 = 8669645) B8669645
theorem B2863673 : Blo 499793 2863673 := bstep (se 2 (by rfl) ⟨1073877, by rfl⟩ : syracuseStep 2863673 = 2147755) B2147755
theorem B1127177 : Blo 499793 1127177 := bstep (se 2 (by rfl) ⟨422691, by rfl⟩ : syracuseStep 1127177 = 845383) B845383
theorem B3617561 : Blo 499793 3617561 := bstep (se 2 (by rfl) ⟨1356585, by rfl⟩ : syracuseStep 3617561 = 2713171) B2713171
theorem B1127231 : Blo 499793 1127231 := bstep (se 1 (by rfl) ⟨845423, by rfl⟩ : syracuseStep 1127231 = 1690847) B1690847
theorem B1127375 : Blo 499793 1127375 := bstep (se 1 (by rfl) ⟨845531, by rfl⟩ : syracuseStep 1127375 = 1691063) B1691063
theorem B1127465 : Blo 499793 1127465 := bstep (se 2 (by rfl) ⟨422799, by rfl⟩ : syracuseStep 1127465 = 845599) B845599
theorem B1127753 : Blo 499793 1127753 := bstep (se 2 (by rfl) ⟨422907, by rfl⟩ : syracuseStep 1127753 = 845815) B845815
theorem B9156239 : Blo 499793 9156239 := bstep (se 1 (by rfl) ⟨6867179, by rfl⟩ : syracuseStep 9156239 = 13734359) B13734359
theorem B636655 : Blo 499793 636655 := bstep (se 1 (by rfl) ⟨477491, by rfl⟩ : syracuseStep 636655 = 954983) B954983
theorem B6961153 : Blo 499793 6961153 := bstep (se 2 (by rfl) ⟨2610432, by rfl⟩ : syracuseStep 6961153 = 5220865) B5220865
theorem B4569281 : Blo 499793 4569281 := bstep (se 2 (by rfl) ⟨1713480, by rfl⟩ : syracuseStep 4569281 = 3426961) B3426961
theorem B1128743 : Blo 499793 1128743 := bstep (se 1 (by rfl) ⟨846557, by rfl⟩ : syracuseStep 1128743 = 1693115) B1693115
theorem B1129103 : Blo 499793 1129103 := bstep (se 1 (by rfl) ⟨846827, by rfl⟩ : syracuseStep 1129103 = 1693655) B1693655
theorem B1129193 : Blo 499793 1129193 := bstep (se 2 (by rfl) ⟨423447, by rfl⟩ : syracuseStep 1129193 = 846895) B846895
theorem B17578939 : Blo 499793 17578939 := bstep (se 1 (by rfl) ⟨13184204, by rfl⟩ : syracuseStep 17578939 = 26368409) B26368409
theorem B1129427 : Blo 499793 1129427 := bstep (se 1 (by rfl) ⟨847070, by rfl⟩ : syracuseStep 1129427 = 1694141) B1694141
theorem B1129697 : Blo 499793 1129697 := bstep (se 2 (by rfl) ⟨423636, by rfl⟩ : syracuseStep 1129697 = 847273) B847273
theorem B13745501 : Blo 499793 13745501 := bstep (se 3 (by rfl) ⟨2577281, by rfl⟩ : syracuseStep 13745501 = 5154563) B5154563
theorem B1130003 : Blo 499793 1130003 := bstep (se 1 (by rfl) ⟨847502, by rfl⟩ : syracuseStep 1130003 = 1695005) B1695005
theorem B573095 : Blo 499793 573095 := bstep (se 1 (by rfl) ⟨429821, by rfl⟩ : syracuseStep 573095 = 859643) B859643
theorem B1130687 : Blo 499793 1130687 := bstep (se 1 (by rfl) ⟨848015, by rfl⟩ : syracuseStep 1130687 = 1696031) B1696031
theorem B803051 : Blo 499793 803051 := bstep (se 1 (by rfl) ⟨602288, by rfl⟩ : syracuseStep 803051 = 1204577) B1204577
theorem B5718275 : Blo 499793 5718275 := bstep (se 1 (by rfl) ⟨4288706, by rfl⟩ : syracuseStep 5718275 = 8577413) B8577413
theorem B11747767 : Blo 499793 11747767 := bstep (se 1 (by rfl) ⟨8810825, by rfl⟩ : syracuseStep 11747767 = 17621651) B17621651
theorem B1655399 : Blo 499793 1655399 := bstep (se 1 (by rfl) ⟨1241549, by rfl⟩ : syracuseStep 1655399 = 2483099) B2483099
theorem B1131119 : Blo 499793 1131119 := bstep (se 1 (by rfl) ⟨848339, by rfl⟩ : syracuseStep 1131119 = 1696679) B1696679
theorem B574171 : Blo 499793 574171 := bstep (se 1 (by rfl) ⟨430628, by rfl⟩ : syracuseStep 574171 = 861257) B861257
theorem B2868047 : Blo 499793 2868047 := bstep (se 1 (by rfl) ⟨2151035, by rfl⟩ : syracuseStep 2868047 = 4302071) B4302071
theorem B1131515 : Blo 499793 1131515 := bstep (se 1 (by rfl) ⟨848636, by rfl⟩ : syracuseStep 1131515 = 1697273) B1697273
theorem B1688687 : Blo 499793 1688687 := bstep (se 1 (by rfl) ⟨1266515, by rfl⟩ : syracuseStep 1688687 = 2533031) B2533031
theorem B1131695 : Blo 499793 1131695 := bstep (se 1 (by rfl) ⟨848771, by rfl⟩ : syracuseStep 1131695 = 1697543) B1697543
theorem B1131731 : Blo 499793 1131731 := bstep (se 1 (by rfl) ⟨848798, by rfl⟩ : syracuseStep 1131731 = 1697597) B1697597
theorem B1688795 : Blo 499793 1688795 := bstep (se 1 (by rfl) ⟨1266596, by rfl⟩ : syracuseStep 1688795 = 2533193) B2533193
theorem B2540969 : Blo 499793 2540969 := bstep (se 2 (by rfl) ⟨952863, by rfl⟩ : syracuseStep 2540969 = 1905727) B1905727
theorem B2147771 : Blo 499793 2147771 := bstep (se 1 (by rfl) ⟨1610828, by rfl⟩ : syracuseStep 2147771 = 3221657) B3221657
theorem B1132001 : Blo 499793 1132001 := bstep (se 2 (by rfl) ⟨424500, by rfl⟩ : syracuseStep 1132001 = 849001) B849001
theorem B2148353 : Blo 499793 2148353 := bstep (se 2 (by rfl) ⟨805632, by rfl⟩ : syracuseStep 2148353 = 1611265) B1611265
theorem B8603657 : Blo 499793 8603657 := bstep (se 2 (by rfl) ⟨3226371, by rfl⟩ : syracuseStep 8603657 = 6452743) B6452743
theorem B6703397 : Blo 499793 6703397 := bstep (se 4 (by rfl) ⟨628443, by rfl⟩ : syracuseStep 6703397 = 1256887) B1256887
theorem B1722995 : Blo 499793 1722995 := bstep (se 1 (by rfl) ⟨1292246, by rfl⟩ : syracuseStep 1722995 = 2584493) B2584493
theorem B2149001 : Blo 499793 2149001 := bstep (se 2 (by rfl) ⟨805875, by rfl⟩ : syracuseStep 2149001 = 1611751) B1611751
theorem B1133351 : Blo 499793 1133351 := bstep (se 1 (by rfl) ⟨850013, by rfl⟩ : syracuseStep 1133351 = 1700027) B1700027
theorem B2542427 : Blo 499793 2542427 := bstep (se 1 (by rfl) ⟨1906820, by rfl⟩ : syracuseStep 2542427 = 3813641) B3813641
theorem B4803731 : Blo 499793 4803731 := bstep (se 1 (by rfl) ⟨3602798, by rfl⟩ : syracuseStep 4803731 = 7205597) B7205597
theorem B4804271 : Blo 499793 4804271 := bstep (se 1 (by rfl) ⟨3603203, by rfl⟩ : syracuseStep 4804271 = 7206407) B7206407
theorem B1429319 : Blo 499793 1429319 := bstep (se 1 (by rfl) ⟨1071989, by rfl⟩ : syracuseStep 1429319 = 2143979) B2143979
theorem B1069051 : Blo 499793 1069051 := bstep (se 1 (by rfl) ⟨801788, by rfl⟩ : syracuseStep 1069051 = 1603577) B1603577
theorem B1429559 : Blo 499793 1429559 := bstep (se 1 (by rfl) ⟨1072169, by rfl⟩ : syracuseStep 1429559 = 2144339) B2144339
theorem B1069409 : Blo 499793 1069409 := bstep (se 2 (by rfl) ⟨401028, by rfl⟩ : syracuseStep 1069409 = 802057) B802057
theorem B1266313 : Blo 499793 1266313 := bstep (se 2 (by rfl) ⟨474867, by rfl⟩ : syracuseStep 1266313 = 949735) B949735
theorem B1692521 : Blo 499793 1692521 := bstep (se 2 (by rfl) ⟨634695, by rfl⟩ : syracuseStep 1692521 = 1269391) B1269391
theorem B1430891 : Blo 499793 1430891 := bstep (se 1 (by rfl) ⟨1073168, by rfl⟩ : syracuseStep 1430891 = 2146337) B2146337
theorem B7918991 : Blo 499793 7918991 := bstep (se 1 (by rfl) ⟨5939243, by rfl⟩ : syracuseStep 7918991 = 11878487) B11878487
theorem B1070759 : Blo 499793 1070759 := bstep (se 1 (by rfl) ⟨803069, by rfl⟩ : syracuseStep 1070759 = 1606139) B1606139
theorem B1267751 : Blo 499793 1267751 := bstep (se 1 (by rfl) ⟨950813, by rfl⟩ : syracuseStep 1267751 = 1901627) B1901627
theorem B94197917 : Blo 499793 94197917 := bstep (se 3 (by rfl) ⟨17662109, by rfl⟩ : syracuseStep 94197917 = 35324219) B35324219
theorem B1071323 : Blo 499793 1071323 := bstep (se 1 (by rfl) ⟨803492, by rfl⟩ : syracuseStep 1071323 = 1606985) B1606985
theorem B1071443 : Blo 499793 1071443 := bstep (se 1 (by rfl) ⟨803582, by rfl⟩ : syracuseStep 1071443 = 1607165) B1607165
theorem B1202663 : Blo 499793 1202663 := bstep (se 1 (by rfl) ⟨901997, by rfl⟩ : syracuseStep 1202663 = 1803995) B1803995
theorem B2546153 : Blo 499793 2546153 := bstep (se 2 (by rfl) ⟨954807, by rfl⟩ : syracuseStep 2546153 = 1909615) B1909615
theorem B1694519 : Blo 499793 1694519 := bstep (se 1 (by rfl) ⟨1270889, by rfl⟩ : syracuseStep 1694519 = 2541779) B2541779
theorem B1465847 : Blo 499793 1465847 := bstep (se 1 (by rfl) ⟨1099385, by rfl⟩ : syracuseStep 1465847 = 2198771) B2198771
theorem B3661433 : Blo 499793 3661433 := bstep (se 2 (by rfl) ⟨1373037, by rfl⟩ : syracuseStep 3661433 = 2746075) B2746075
theorem B18341639 : Blo 499793 18341639 := bstep (se 1 (by rfl) ⟨13756229, by rfl⟩ : syracuseStep 18341639 = 27512459) B27512459
theorem B1695599 : Blo 499793 1695599 := bstep (se 1 (by rfl) ⟨1271699, by rfl⟩ : syracuseStep 1695599 = 2543399) B2543399
theorem B2547611 : Blo 499793 2547611 := bstep (se 1 (by rfl) ⟨1910708, by rfl⟩ : syracuseStep 2547611 = 3821417) B3821417
theorem B1073407 : Blo 499793 1073407 := bstep (se 1 (by rfl) ⟨805055, by rfl⟩ : syracuseStep 1073407 = 1610111) B1610111
theorem B2286247 : Blo 499793 2286247 := bstep (se 1 (by rfl) ⟨1714685, by rfl⟩ : syracuseStep 2286247 = 3429371) B3429371
theorem B1696463 : Blo 499793 1696463 := bstep (se 1 (by rfl) ⟨1272347, by rfl⟩ : syracuseStep 1696463 = 2544695) B2544695
theorem B3203819 : Blo 499793 3203819 := bstep (se 1 (by rfl) ⟨2402864, by rfl⟩ : syracuseStep 3203819 = 4805729) B4805729
theorem B1696841 : Blo 499793 1696841 := bstep (se 2 (by rfl) ⟨636315, by rfl⟩ : syracuseStep 1696841 = 1272631) B1272631
theorem B845113 : Blo 499793 845113 := bstep (se 2 (by rfl) ⟨316917, by rfl⟩ : syracuseStep 845113 = 633835) B633835
theorem B26109773 : Blo 499793 26109773 := bstep (se 3 (by rfl) ⟨4895582, by rfl⟩ : syracuseStep 26109773 = 9791165) B9791165
theorem B1140635 : Blo 499793 1140635 := bstep (se 1 (by rfl) ⟨855476, by rfl⟩ : syracuseStep 1140635 = 1710953) B1710953
theorem B1271771 : Blo 499793 1271771 := bstep (se 1 (by rfl) ⟨953828, by rfl⟩ : syracuseStep 1271771 = 1907657) B1907657
theorem B1271801 : Blo 499793 1271801 := bstep (se 2 (by rfl) ⟨476925, by rfl⟩ : syracuseStep 1271801 = 953851) B953851
theorem B2582699 : Blo 499793 2582699 := bstep (se 1 (by rfl) ⟨1937024, by rfl⟩ : syracuseStep 2582699 = 3874049) B3874049
theorem B9136739 : Blo 499793 9136739 := bstep (se 1 (by rfl) ⟨6852554, by rfl⟩ : syracuseStep 9136739 = 13705109) B13705109
theorem B1272905 : Blo 499793 1272905 := bstep (se 2 (by rfl) ⟨477339, by rfl⟩ : syracuseStep 1272905 = 954679) B954679
theorem B847327 : Blo 499793 847327 := bstep (se 1 (by rfl) ⟨635495, by rfl⟩ : syracuseStep 847327 = 1270991) B1270991
theorem B30797333 : Blo 499793 30797333 := bstep (se 6 (by rfl) ⟨721812, by rfl⟩ : syracuseStep 30797333 = 1443625) B1443625
theorem B847543 : Blo 499793 847543 := bstep (se 1 (by rfl) ⟨635657, by rfl⟩ : syracuseStep 847543 = 1271315) B1271315
theorem B1044193 : Blo 499793 1044193 := bstep (se 2 (by rfl) ⟨391572, by rfl⟩ : syracuseStep 1044193 = 783145) B783145
theorem B1175273 : Blo 499793 1175273 := bstep (se 2 (by rfl) ⟨440727, by rfl⟩ : syracuseStep 1175273 = 881455) B881455
theorem B716539 : Blo 499793 716539 := bstep (se 1 (by rfl) ⟨537404, by rfl⟩ : syracuseStep 716539 = 1074809) B1074809
theorem B10841951 : Blo 499793 10841951 := bstep (se 1 (by rfl) ⟨8131463, by rfl⟩ : syracuseStep 10841951 = 16262927) B16262927
theorem B4812803 : Blo 499793 4812803 := bstep (se 1 (by rfl) ⟨3609602, by rfl⟩ : syracuseStep 4812803 = 7219205) B7219205
theorem B5796029 : Blo 499793 5796029 := bstep (se 3 (by rfl) ⟨1086755, by rfl⟩ : syracuseStep 5796029 = 2173511) B2173511
theorem B749801 : Blo 499793 749801 := bstep (se 2 (by rfl) ⟨281175, by rfl⟩ : syracuseStep 749801 = 562351) B562351
theorem B1274089 : Blo 499793 1274089 := bstep (se 2 (by rfl) ⟨477783, by rfl⟩ : syracuseStep 1274089 = 955567) B955567
theorem B749927 : Blo 499793 749927 := bstep (se 1 (by rfl) ⟨562445, by rfl⟩ : syracuseStep 749927 = 1124891) B1124891
theorem B717211 : Blo 499793 717211 := bstep (se 1 (by rfl) ⟨537908, by rfl⟩ : syracuseStep 717211 = 1075817) B1075817
theorem B2716199 : Blo 499793 2716199 := bstep (se 1 (by rfl) ⟨2037149, by rfl⟩ : syracuseStep 2716199 = 4074299) B4074299
theorem B750473 : Blo 499793 750473 := bstep (se 2 (by rfl) ⟨281427, by rfl⟩ : syracuseStep 750473 = 562855) B562855
theorem B750857 : Blo 499793 750857 := bstep (se 2 (by rfl) ⟨281571, by rfl⟩ : syracuseStep 750857 = 563143) B563143
theorem B750911 : Blo 499793 750911 := bstep (se 1 (by rfl) ⟨563183, by rfl⟩ : syracuseStep 750911 = 1126367) B1126367
theorem B751337 : Blo 499793 751337 := bstep (se 2 (by rfl) ⟨281751, by rfl⟩ : syracuseStep 751337 = 563503) B563503
theorem B751343 : Blo 499793 751343 := bstep (se 1 (by rfl) ⟨563507, by rfl⟩ : syracuseStep 751343 = 1127015) B1127015
theorem B751799 : Blo 499793 751799 := bstep (se 1 (by rfl) ⟨563849, by rfl⟩ : syracuseStep 751799 = 1127699) B1127699
theorem B751847 : Blo 499793 751847 := bstep (se 1 (by rfl) ⟨563885, by rfl⟩ : syracuseStep 751847 = 1127771) B1127771
theorem B752219 : Blo 499793 752219 := bstep (se 1 (by rfl) ⟨564164, by rfl⟩ : syracuseStep 752219 = 1128329) B1128329
theorem B752363 : Blo 499793 752363 := bstep (se 1 (by rfl) ⟨564272, by rfl⟩ : syracuseStep 752363 = 1128545) B1128545
theorem B8551169 : Blo 499793 8551169 := bstep (se 2 (by rfl) ⟨3206688, by rfl⟩ : syracuseStep 8551169 = 6413377) B6413377
theorem B752393 : Blo 499793 752393 := bstep (se 2 (by rfl) ⟨282147, by rfl⟩ : syracuseStep 752393 = 564295) B564295
theorem B10714295 : Blo 499793 10714295 := bstep (se 1 (by rfl) ⟨8035721, by rfl⟩ : syracuseStep 10714295 = 16071443) B16071443
theorem B1146079 : Blo 499793 1146079 := bstep (se 1 (by rfl) ⟨859559, by rfl⟩ : syracuseStep 1146079 = 1719119) B1719119
theorem B8125697 : Blo 499793 8125697 := bstep (se 2 (by rfl) ⟨3047136, by rfl⟩ : syracuseStep 8125697 = 6094273) B6094273
theorem B949583 : Blo 499793 949583 := bstep (se 1 (by rfl) ⟨712187, by rfl⟩ : syracuseStep 949583 = 1424375) B1424375
theorem B2850299 : Blo 499793 2850299 := bstep (se 1 (by rfl) ⟨2137724, by rfl⟩ : syracuseStep 2850299 = 4275449) B4275449
theorem B4816493 : Blo 499793 4816493 := bstep (se 3 (by rfl) ⟨903092, by rfl⟩ : syracuseStep 4816493 = 1806185) B1806185
theorem B753263 : Blo 499793 753263 := bstep (se 1 (by rfl) ⟨564947, by rfl⟩ : syracuseStep 753263 = 1129895) B1129895
theorem B8158913 : Blo 499793 8158913 := bstep (se 2 (by rfl) ⟨3059592, by rfl⟩ : syracuseStep 8158913 = 6119185) B6119185
theorem B753383 : Blo 499793 753383 := bstep (se 1 (by rfl) ⟨565037, by rfl⟩ : syracuseStep 753383 = 1130075) B1130075
theorem B1900367 : Blo 499793 1900367 := bstep (se 1 (by rfl) ⟨1425275, by rfl⟩ : syracuseStep 1900367 = 2850551) B2850551
theorem B753575 : Blo 499793 753575 := bstep (se 1 (by rfl) ⟨565181, by rfl⟩ : syracuseStep 753575 = 1130363) B1130363
theorem B753791 : Blo 499793 753791 := bstep (se 1 (by rfl) ⟨565343, by rfl⟩ : syracuseStep 753791 = 1130687) B1130687
theorem B754079 : Blo 499793 754079 := bstep (se 1 (by rfl) ⟨565559, by rfl⟩ : syracuseStep 754079 = 1131119) B1131119
theorem B15663689 : Blo 499793 15663689 := bstep (se 2 (by rfl) ⟨5873883, by rfl⟩ : syracuseStep 15663689 = 11747767) B11747767
theorem B754343 : Blo 499793 754343 := bstep (se 1 (by rfl) ⟨565757, by rfl⟩ : syracuseStep 754343 = 1131515) B1131515
theorem B10846973 : Blo 499793 10846973 := bstep (se 3 (by rfl) ⟨2033807, by rfl⟩ : syracuseStep 10846973 = 4067615) B4067615
theorem B754463 : Blo 499793 754463 := bstep (se 1 (by rfl) ⟨565847, by rfl⟩ : syracuseStep 754463 = 1131695) B1131695
theorem B754487 : Blo 499793 754487 := bstep (se 1 (by rfl) ⟨565865, by rfl⟩ : syracuseStep 754487 = 1131731) B1131731
theorem B3048329 : Blo 499793 3048329 := bstep (se 2 (by rfl) ⟨1143123, by rfl⟩ : syracuseStep 3048329 = 2286247) B2286247
theorem B2851757 : Blo 499793 2851757 := bstep (se 3 (by rfl) ⟨534704, by rfl⟩ : syracuseStep 2851757 = 1069409) B1069409
theorem B754667 : Blo 499793 754667 := bstep (se 1 (by rfl) ⟨566000, by rfl⟩ : syracuseStep 754667 = 1132001) B1132001
theorem B3212635 : Blo 499793 3212635 := bstep (se 1 (by rfl) ⟨2409476, by rfl⟩ : syracuseStep 3212635 = 4818953) B4818953
theorem B5735771 : Blo 499793 5735771 := bstep (se 1 (by rfl) ⟨4301828, by rfl⟩ : syracuseStep 5735771 = 8603657) B8603657
theorem B4588919 : Blo 499793 4588919 := bstep (se 1 (by rfl) ⟨3441689, by rfl⟩ : syracuseStep 4588919 = 6883379) B6883379
theorem B755177 : Blo 499793 755177 := bstep (se 2 (by rfl) ⟨283191, by rfl⟩ : syracuseStep 755177 = 566383) B566383
theorem B1902143 : Blo 499793 1902143 := bstep (se 1 (by rfl) ⟨1426607, by rfl⟩ : syracuseStep 1902143 = 2853215) B2853215
theorem B1148663 : Blo 499793 1148663 := bstep (se 1 (by rfl) ⟨861497, by rfl⟩ : syracuseStep 1148663 = 1722995) B1722995
theorem B3540743 : Blo 499793 3540743 := bstep (se 1 (by rfl) ⟨2655557, by rfl⟩ : syracuseStep 3540743 = 5311115) B5311115
theorem B755567 : Blo 499793 755567 := bstep (se 1 (by rfl) ⟨566675, by rfl⟩ : syracuseStep 755567 = 1133351) B1133351
theorem B952879 : Blo 499793 952879 := bstep (se 1 (by rfl) ⟨714659, by rfl⟩ : syracuseStep 952879 = 1429319) B1429319
theorem B953039 : Blo 499793 953039 := bstep (se 1 (by rfl) ⟨714779, by rfl⟩ : syracuseStep 953039 = 1429559) B1429559
theorem B2296795 : Blo 499793 2296795 := bstep (se 1 (by rfl) ⟨1722596, by rfl⟩ : syracuseStep 2296795 = 3445193) B3445193
theorem B953927 : Blo 499793 953927 := bstep (se 1 (by rfl) ⟨715445, by rfl⟩ : syracuseStep 953927 = 1430891) B1430891
theorem B5279327 : Blo 499793 5279327 := bstep (se 1 (by rfl) ⟨3959495, by rfl⟩ : syracuseStep 5279327 = 7918991) B7918991
theorem B2855357 : Blo 499793 2855357 := bstep (se 3 (by rfl) ⟨535379, by rfl⟩ : syracuseStep 2855357 = 1070759) B1070759
theorem B955385 : Blo 499793 955385 := bstep (se 2 (by rfl) ⟨358269, by rfl⟩ : syracuseStep 955385 = 716539) B716539
theorem B12227759 : Blo 499793 12227759 := bstep (se 1 (by rfl) ⟨9170819, by rfl⟩ : syracuseStep 12227759 = 18341639) B18341639
theorem B6887197 : Blo 499793 6887197 := bstep (se 3 (by rfl) ⟨1291349, by rfl⟩ : syracuseStep 6887197 = 2582699) B2582699
theorem B2135879 : Blo 499793 2135879 := bstep (se 1 (by rfl) ⟨1601909, by rfl⟩ : syracuseStep 2135879 = 3203819) B3203819
theorem B956281 : Blo 499793 956281 := bstep (se 2 (by rfl) ⟨358605, by rfl⟩ : syracuseStep 956281 = 717211) B717211
theorem B2038223 : Blo 499793 2038223 := bstep (se 1 (by rfl) ⟨1528667, by rfl⟩ : syracuseStep 2038223 = 3057335) B3057335
theorem B17406515 : Blo 499793 17406515 := bstep (se 1 (by rfl) ⟨13054886, by rfl⟩ : syracuseStep 17406515 = 26109773) B26109773
theorem B760423 : Blo 499793 760423 := bstep (se 1 (by rfl) ⟨570317, by rfl⟩ : syracuseStep 760423 = 1140635) B1140635
theorem B1645171 : Blo 499793 1645171 := bstep (se 1 (by rfl) ⟨1233878, by rfl⟩ : syracuseStep 1645171 = 2467757) B2467757
theorem B5709527 : Blo 499793 5709527 := bstep (se 1 (by rfl) ⟨4282145, by rfl⟩ : syracuseStep 5709527 = 8564291) B8564291
theorem B21700507 : Blo 499793 21700507 := bstep (se 1 (by rfl) ⟨16275380, by rfl⟩ : syracuseStep 21700507 = 32550761) B32550761
theorem B3809267 : Blo 499793 3809267 := bstep (se 1 (by rfl) ⟨2856950, by rfl⟩ : syracuseStep 3809267 = 5713901) B5713901
theorem B9281537 : Blo 499793 9281537 := bstep (se 2 (by rfl) ⟨3480576, by rfl⟩ : syracuseStep 9281537 = 6961153) B6961153
theorem B499867 : Blo 499793 499867 := bstep (se 1 (by rfl) ⟨374900, by rfl⟩ : syracuseStep 499867 = 749801) B749801
theorem B499951 : Blo 499793 499951 := bstep (se 1 (by rfl) ⟨374963, by rfl⟩ : syracuseStep 499951 = 749927) B749927
theorem B1810799 : Blo 499793 1810799 := bstep (se 1 (by rfl) ⟨1358099, by rfl⟩ : syracuseStep 1810799 = 2716199) B2716199
theorem B1909115 : Blo 499793 1909115 := bstep (se 1 (by rfl) ⟨1431836, by rfl⟩ : syracuseStep 1909115 = 2863673) B2863673
theorem B500315 : Blo 499793 500315 := bstep (se 1 (by rfl) ⟨375236, by rfl⟩ : syracuseStep 500315 = 750473) B750473
theorem B500571 : Blo 499793 500571 := bstep (se 1 (by rfl) ⟨375428, by rfl⟩ : syracuseStep 500571 = 750857) B750857
theorem B2532221 : Blo 499793 2532221 := bstep (se 3 (by rfl) ⟨474791, by rfl⟩ : syracuseStep 2532221 = 949583) B949583
theorem B500607 : Blo 499793 500607 := bstep (se 1 (by rfl) ⟨375455, by rfl⟩ : syracuseStep 500607 = 750911) B750911
theorem B6104159 : Blo 499793 6104159 := bstep (se 1 (by rfl) ⟨4578119, by rfl⟩ : syracuseStep 6104159 = 9156239) B9156239
theorem B500891 : Blo 499793 500891 := bstep (se 1 (by rfl) ⟨375668, by rfl⟩ : syracuseStep 500891 = 751337) B751337
theorem B500895 : Blo 499793 500895 := bstep (se 1 (by rfl) ⟨375671, by rfl⟩ : syracuseStep 500895 = 751343) B751343
theorem B23438585 : Blo 499793 23438585 := bstep (se 2 (by rfl) ⟨8789469, by rfl⟩ : syracuseStep 23438585 = 17578939) B17578939
theorem B501199 : Blo 499793 501199 := bstep (se 1 (by rfl) ⟨375899, by rfl⟩ : syracuseStep 501199 = 751799) B751799
theorem B501231 : Blo 499793 501231 := bstep (se 1 (by rfl) ⟨375923, by rfl⟩ : syracuseStep 501231 = 751847) B751847
theorem B501479 : Blo 499793 501479 := bstep (se 1 (by rfl) ⟨376109, by rfl⟩ : syracuseStep 501479 = 752219) B752219
theorem B501575 : Blo 499793 501575 := bstep (se 1 (by rfl) ⟨376181, by rfl⟩ : syracuseStep 501575 = 752363) B752363
theorem B501595 : Blo 499793 501595 := bstep (se 1 (by rfl) ⟨376196, by rfl⟩ : syracuseStep 501595 = 752393) B752393
theorem B5417131 : Blo 499793 5417131 := bstep (se 1 (by rfl) ⟨4062848, by rfl⟩ : syracuseStep 5417131 = 8125697) B8125697
theorem B502175 : Blo 499793 502175 := bstep (se 1 (by rfl) ⟨376631, by rfl⟩ : syracuseStep 502175 = 753263) B753263
theorem B502255 : Blo 499793 502255 := bstep (se 1 (by rfl) ⟨376691, by rfl⟩ : syracuseStep 502255 = 753383) B753383
theorem B4303469 : Blo 499793 4303469 := bstep (se 3 (by rfl) ⟨806900, by rfl⟩ : syracuseStep 4303469 = 1613801) B1613801
theorem B502383 : Blo 499793 502383 := bstep (se 1 (by rfl) ⟨376787, by rfl⟩ : syracuseStep 502383 = 753575) B753575
theorem B535367 : Blo 499793 535367 := bstep (se 1 (by rfl) ⟨401525, by rfl⟩ : syracuseStep 535367 = 803051) B803051
theorem B502599 : Blo 499793 502599 := bstep (se 1 (by rfl) ⟨376949, by rfl⟩ : syracuseStep 502599 = 753899) B753899
theorem B3812183 : Blo 499793 3812183 := bstep (se 1 (by rfl) ⟨2859137, by rfl⟩ : syracuseStep 3812183 = 5718275) B5718275
theorem B502639 : Blo 499793 502639 := bstep (se 1 (by rfl) ⟨376979, by rfl⟩ : syracuseStep 502639 = 753959) B753959
theorem B1912031 : Blo 499793 1912031 := bstep (se 1 (by rfl) ⟨1434023, by rfl⟩ : syracuseStep 1912031 = 2868047) B2868047
theorem B634159 : Blo 499793 634159 := bstep (se 1 (by rfl) ⟨475619, by rfl⟩ : syracuseStep 634159 = 951239) B951239
theorem B503087 : Blo 499793 503087 := bstep (se 1 (by rfl) ⟨377315, by rfl⟩ : syracuseStep 503087 = 754631) B754631
theorem B1813855 : Blo 499793 1813855 := bstep (se 1 (by rfl) ⟨1360391, by rfl⟩ : syracuseStep 1813855 = 2720783) B2720783
theorem B1125791 : Blo 499793 1125791 := bstep (se 1 (by rfl) ⟨844343, by rfl⟩ : syracuseStep 1125791 = 1688687) B1688687
theorem B503199 : Blo 499793 503199 := bstep (se 1 (by rfl) ⟨377399, by rfl⟩ : syracuseStep 503199 = 754799) B754799
theorem B7253459 : Blo 499793 7253459 := bstep (se 1 (by rfl) ⟨5440094, by rfl⟩ : syracuseStep 7253459 = 10880189) B10880189
theorem B1125863 : Blo 499793 1125863 := bstep (se 1 (by rfl) ⟨844397, by rfl⟩ : syracuseStep 1125863 = 1688795) B1688795
theorem B503327 : Blo 499793 503327 := bstep (se 1 (by rfl) ⟨377495, by rfl⟩ : syracuseStep 503327 = 754991) B754991
theorem B503463 : Blo 499793 503463 := bstep (se 1 (by rfl) ⟨377597, by rfl⟩ : syracuseStep 503463 = 755195) B755195
theorem B503487 : Blo 499793 503487 := bstep (se 1 (by rfl) ⟨377615, by rfl⟩ : syracuseStep 503487 = 755231) B755231
theorem B3124939 : Blo 499793 3124939 := bstep (se 1 (by rfl) ⟨2343704, by rfl⟩ : syracuseStep 3124939 = 4687409) B4687409
theorem B634655 : Blo 499793 634655 := bstep (se 1 (by rfl) ⟨475991, by rfl⟩ : syracuseStep 634655 = 951983) B951983
theorem B503583 : Blo 499793 503583 := bstep (se 1 (by rfl) ⟨377687, by rfl⟩ : syracuseStep 503583 = 755375) B755375
theorem B503663 : Blo 499793 503663 := bstep (se 1 (by rfl) ⟨377747, by rfl⟩ : syracuseStep 503663 = 755495) B755495
theorem B4468931 : Blo 499793 4468931 := bstep (se 1 (by rfl) ⟨3351698, by rfl⟩ : syracuseStep 4468931 = 6703397) B6703397
theorem B1126817 : Blo 499793 1126817 := bstep (se 2 (by rfl) ⟨422556, by rfl⟩ : syracuseStep 1126817 = 845113) B845113
theorem B2406095 : Blo 499793 2406095 := bstep (se 1 (by rfl) ⟨1804571, by rfl⟩ : syracuseStep 2406095 = 3609143) B3609143
theorem B1128347 : Blo 499793 1128347 := bstep (se 1 (by rfl) ⟨846260, by rfl⟩ : syracuseStep 1128347 = 1692521) B1692521
theorem B3062245 : Blo 499793 3062245 := bstep (se 4 (by rfl) ⟨287085, by rfl⟩ : syracuseStep 3062245 = 574171) B574171
theorem B77118227 : Blo 499793 77118227 := bstep (se 1 (by rfl) ⟨57838670, by rfl⟩ : syracuseStep 77118227 = 115677341) B115677341
theorem B62798611 : Blo 499793 62798611 := bstep (se 1 (by rfl) ⟨47098958, by rfl⟩ : syracuseStep 62798611 = 94197917) B94197917
theorem B506863 : Blo 499793 506863 := bstep (se 1 (by rfl) ⟨380147, by rfl⟩ : syracuseStep 506863 = 760295) B760295
theorem B801775 : Blo 499793 801775 := bstep (se 1 (by rfl) ⟨601331, by rfl⟩ : syracuseStep 801775 = 1202663) B1202663
theorem B1129679 : Blo 499793 1129679 := bstep (se 1 (by rfl) ⟨847259, by rfl⟩ : syracuseStep 1129679 = 1694519) B1694519
theorem B1129769 : Blo 499793 1129769 := bstep (se 2 (by rfl) ⟨423663, by rfl⟩ : syracuseStep 1129769 = 847327) B847327
theorem B2538863 : Blo 499793 2538863 := bstep (se 1 (by rfl) ⟨1904147, by rfl⟩ : syracuseStep 2538863 = 3808295) B3808295
theorem B1686959 : Blo 499793 1686959 := bstep (se 1 (by rfl) ⟨1265219, by rfl⟩ : syracuseStep 1686959 = 2530439) B2530439
theorem B6405587 : Blo 499793 6405587 := bstep (se 1 (by rfl) ⟨4804190, by rfl⟩ : syracuseStep 6405587 = 9608381) B9608381
theorem B1130057 : Blo 499793 1130057 := bstep (se 2 (by rfl) ⟨423771, by rfl⟩ : syracuseStep 1130057 = 847543) B847543
theorem B1392257 : Blo 499793 1392257 := bstep (se 2 (by rfl) ⟨522096, by rfl⟩ : syracuseStep 1392257 = 1044193) B1044193
theorem B2440955 : Blo 499793 2440955 := bstep (se 1 (by rfl) ⟨1830716, by rfl⟩ : syracuseStep 2440955 = 3661433) B3661433
theorem B1130399 : Blo 499793 1130399 := bstep (se 1 (by rfl) ⟨847799, by rfl⟩ : syracuseStep 1130399 = 1695599) B1695599
theorem B2146267 : Blo 499793 2146267 := bstep (se 1 (by rfl) ⟨1609700, by rfl⟩ : syracuseStep 2146267 = 3219401) B3219401
theorem B1425401 : Blo 499793 1425401 := bstep (se 2 (by rfl) ⟨534525, by rfl⟩ : syracuseStep 1425401 = 1069051) B1069051
theorem B1130975 : Blo 499793 1130975 := bstep (se 1 (by rfl) ⟨848231, by rfl⟩ : syracuseStep 1130975 = 1696463) B1696463
theorem B1688039 : Blo 499793 1688039 := bstep (se 1 (by rfl) ⟨1266029, by rfl⟩ : syracuseStep 1688039 = 2532059) B2532059
theorem B1131227 : Blo 499793 1131227 := bstep (se 1 (by rfl) ⟨848420, by rfl⟩ : syracuseStep 1131227 = 1696841) B1696841
theorem B1688417 : Blo 499793 1688417 := bstep (se 2 (by rfl) ⟨633156, by rfl⟩ : syracuseStep 1688417 = 1266313) B1266313
theorem B6112421 : Blo 499793 6112421 := bstep (se 4 (by rfl) ⟨573039, by rfl⟩ : syracuseStep 6112421 = 1146079) B1146079
theorem B24364637 : Blo 499793 24364637 := bstep (se 3 (by rfl) ⟨4568369, by rfl⟩ : syracuseStep 24364637 = 9136739) B9136739
theorem B20531555 : Blo 499793 20531555 := bstep (se 1 (by rfl) ⟨15398666, by rfl⟩ : syracuseStep 20531555 = 30797333) B30797333
theorem B1689983 : Blo 499793 1689983 := bstep (se 1 (by rfl) ⟨1267487, by rfl⟩ : syracuseStep 1689983 = 2534975) B2534975
theorem B7227967 : Blo 499793 7227967 := bstep (se 1 (by rfl) ⟨5420975, by rfl⟩ : syracuseStep 7227967 = 10841951) B10841951
theorem B3853175 : Blo 499793 3853175 := bstep (se 1 (by rfl) ⟨2889881, by rfl⟩ : syracuseStep 3853175 = 5779763) B5779763
theorem B3263597 : Blo 499793 3263597 := bstep (se 3 (by rfl) ⟨611924, by rfl⟩ : syracuseStep 3263597 = 1223849) B1223849
theorem B2411707 : Blo 499793 2411707 := bstep (se 1 (by rfl) ⟨1808780, by rfl⟩ : syracuseStep 2411707 = 3617561) B3617561
theorem B1528253 : Blo 499793 1528253 := bstep (se 3 (by rfl) ⟨286547, by rfl⟩ : syracuseStep 1528253 = 573095) B573095
theorem B9163667 : Blo 499793 9163667 := bstep (se 1 (by rfl) ⟨6872750, by rfl⟩ : syracuseStep 9163667 = 13745501) B13745501
theorem B1266911 : Blo 499793 1266911 := bstep (se 1 (by rfl) ⟨950183, by rfl⟩ : syracuseStep 1266911 = 1900367) B1900367
theorem B1431209 : Blo 499793 1431209 := bstep (se 2 (by rfl) ⟨536703, by rfl⟩ : syracuseStep 1431209 = 1073407) B1073407
theorem B13064327 : Blo 499793 13064327 := bstep (se 1 (by rfl) ⟨9798245, by rfl⟩ : syracuseStep 13064327 = 19596491) B19596491
theorem B1693979 : Blo 499793 1693979 := bstep (se 1 (by rfl) ⟨1270484, by rfl⟩ : syracuseStep 1693979 = 2540969) B2540969
theorem B1431847 : Blo 499793 1431847 := bstep (se 1 (by rfl) ⟨1073885, by rfl⟩ : syracuseStep 1431847 = 2147771) B2147771
theorem B20666843 : Blo 499793 20666843 := bstep (se 1 (by rfl) ⟨15500132, by rfl⟩ : syracuseStep 20666843 = 31000265) B31000265
theorem B1071623 : Blo 499793 1071623 := bstep (se 1 (by rfl) ⟨803717, by rfl⟩ : syracuseStep 1071623 = 1607435) B1607435
theorem B1432235 : Blo 499793 1432235 := bstep (se 1 (by rfl) ⟨1074176, by rfl⟩ : syracuseStep 1432235 = 2148353) B2148353
theorem B4807421 : Blo 499793 4807421 := bstep (se 3 (by rfl) ⟨901391, by rfl⟩ : syracuseStep 4807421 = 1802783) B1802783
theorem B6445979 : Blo 499793 6445979 := bstep (se 1 (by rfl) ⟨4834484, by rfl⟩ : syracuseStep 6445979 = 9668969) B9668969
theorem B4414397 : Blo 499793 4414397 := bstep (se 3 (by rfl) ⟨827699, by rfl⟩ : syracuseStep 4414397 = 1655399) B1655399
theorem B1432667 : Blo 499793 1432667 := bstep (se 1 (by rfl) ⟨1074500, by rfl⟩ : syracuseStep 1432667 = 2149001) B2149001
theorem B1694951 : Blo 499793 1694951 := bstep (se 1 (by rfl) ⟨1271213, by rfl⟩ : syracuseStep 1694951 = 2542427) B2542427
theorem B1072511 : Blo 499793 1072511 := bstep (se 1 (by rfl) ⟨804383, by rfl⟩ : syracuseStep 1072511 = 1608767) B1608767
theorem B3202487 : Blo 499793 3202487 := bstep (se 1 (by rfl) ⟨2401865, by rfl⟩ : syracuseStep 3202487 = 4803731) B4803731
theorem B3104225 : Blo 499793 3104225 := bstep (se 2 (by rfl) ⟨1164084, by rfl⟩ : syracuseStep 3104225 = 2328169) B2328169
theorem B3202847 : Blo 499793 3202847 := bstep (se 1 (by rfl) ⟨2402135, by rfl⟩ : syracuseStep 3202847 = 4804271) B4804271
theorem B24338339 : Blo 499793 24338339 := bstep (se 1 (by rfl) ⟨18253754, by rfl⟩ : syracuseStep 24338339 = 36507509) B36507509
theorem B843689 : Blo 499793 843689 := bstep (se 2 (by rfl) ⟨316383, by rfl⟩ : syracuseStep 843689 = 632767) B632767
theorem B44130365 : Blo 499793 44130365 := bstep (se 3 (by rfl) ⟨8274443, by rfl⟩ : syracuseStep 44130365 = 16548887) B16548887
theorem B5727023 : Blo 499793 5727023 := bstep (se 1 (by rfl) ⟨4295267, by rfl⟩ : syracuseStep 5727023 = 8590535) B8590535
theorem B1270687 : Blo 499793 1270687 := bstep (se 1 (by rfl) ⟨953015, by rfl⟩ : syracuseStep 1270687 = 1906031) B1906031
theorem B2548745 : Blo 499793 2548745 := bstep (se 2 (by rfl) ⟨955779, by rfl⟩ : syracuseStep 2548745 = 1911559) B1911559
theorem B845167 : Blo 499793 845167 := bstep (se 1 (by rfl) ⟨633875, by rfl⟩ : syracuseStep 845167 = 1267751) B1267751
theorem B714215 : Blo 499793 714215 := bstep (se 1 (by rfl) ⟨535661, by rfl⟩ : syracuseStep 714215 = 1071323) B1071323
theorem B714295 : Blo 499793 714295 := bstep (se 1 (by rfl) ⟨535721, by rfl⟩ : syracuseStep 714295 = 1071443) B1071443
theorem B1697435 : Blo 499793 1697435 := bstep (se 1 (by rfl) ⟨1273076, by rfl⟩ : syracuseStep 1697435 = 2546153) B2546153
theorem B1272095 : Blo 499793 1272095 := bstep (se 1 (by rfl) ⟨954071, by rfl⟩ : syracuseStep 1272095 = 1908143) B1908143
theorem B977231 : Blo 499793 977231 := bstep (se 1 (by rfl) ⟨732923, by rfl⟩ : syracuseStep 977231 = 1465847) B1465847
theorem B1698407 : Blo 499793 1698407 := bstep (se 1 (by rfl) ⟨1273805, by rfl⟩ : syracuseStep 1698407 = 2547611) B2547611
theorem B1698785 : Blo 499793 1698785 := bstep (se 2 (by rfl) ⟨637044, by rfl⟩ : syracuseStep 1698785 = 1274089) B1274089
theorem B1273067 : Blo 499793 1273067 := bstep (se 1 (by rfl) ⟨954800, by rfl⟩ : syracuseStep 1273067 = 1909601) B1909601
theorem B847847 : Blo 499793 847847 := bstep (se 1 (by rfl) ⟨635885, by rfl⟩ : syracuseStep 847847 = 1271771) B1271771
theorem B847867 : Blo 499793 847867 := bstep (se 1 (by rfl) ⟨635900, by rfl⟩ : syracuseStep 847867 = 1271801) B1271801
theorem B749723 : Blo 499793 749723 := bstep (se 1 (by rfl) ⟨562292, by rfl⟩ : syracuseStep 749723 = 1124585) B1124585
theorem B749903 : Blo 499793 749903 := bstep (se 1 (by rfl) ⟨562427, by rfl⟩ : syracuseStep 749903 = 1124855) B1124855
theorem B1274251 : Blo 499793 1274251 := bstep (se 1 (by rfl) ⟨955688, by rfl⟩ : syracuseStep 1274251 = 1911377) B1911377
theorem B749993 : Blo 499793 749993 := bstep (se 2 (by rfl) ⟨281247, by rfl⟩ : syracuseStep 749993 = 562495) B562495
theorem B750299 : Blo 499793 750299 := bstep (se 1 (by rfl) ⟨562724, by rfl⟩ : syracuseStep 750299 = 1125449) B1125449
theorem B848603 : Blo 499793 848603 := bstep (se 1 (by rfl) ⟨636452, by rfl⟩ : syracuseStep 848603 = 1272905) B1272905
theorem B750569 : Blo 499793 750569 := bstep (se 2 (by rfl) ⟨281463, by rfl⟩ : syracuseStep 750569 = 562927) B562927
theorem B848873 : Blo 499793 848873 := bstep (se 2 (by rfl) ⟨318327, by rfl⟩ : syracuseStep 848873 = 636655) B636655
theorem B750713 : Blo 499793 750713 := bstep (se 2 (by rfl) ⟨281517, by rfl⟩ : syracuseStep 750713 = 563035) B563035
theorem B783515 : Blo 499793 783515 := bstep (se 1 (by rfl) ⟨587636, by rfl⟩ : syracuseStep 783515 = 1175273) B1175273
theorem B3208535 : Blo 499793 3208535 := bstep (se 1 (by rfl) ⟨2406401, by rfl⟩ : syracuseStep 3208535 = 4812803) B4812803
theorem B3864019 : Blo 499793 3864019 := bstep (se 1 (by rfl) ⟨2898014, by rfl⟩ : syracuseStep 3864019 = 5796029) B5796029
theorem B751241 : Blo 499793 751241 := bstep (se 2 (by rfl) ⟨281715, by rfl⟩ : syracuseStep 751241 = 563431) B563431
theorem B751451 : Blo 499793 751451 := bstep (se 1 (by rfl) ⟨563588, by rfl⟩ : syracuseStep 751451 = 1127177) B1127177
theorem B751487 : Blo 499793 751487 := bstep (se 1 (by rfl) ⟨563615, by rfl⟩ : syracuseStep 751487 = 1127231) B1127231
theorem B751583 : Blo 499793 751583 := bstep (se 1 (by rfl) ⟨563687, by rfl⟩ : syracuseStep 751583 = 1127375) B1127375
theorem B751643 : Blo 499793 751643 := bstep (se 1 (by rfl) ⟨563732, by rfl⟩ : syracuseStep 751643 = 1127465) B1127465
theorem B751835 : Blo 499793 751835 := bstep (se 1 (by rfl) ⟨563876, by rfl⟩ : syracuseStep 751835 = 1127753) B1127753
theorem B752105 : Blo 499793 752105 := bstep (se 2 (by rfl) ⟨282039, by rfl⟩ : syracuseStep 752105 = 564079) B564079
theorem B3046187 : Blo 499793 3046187 := bstep (se 1 (by rfl) ⟨2284640, by rfl⟩ : syracuseStep 3046187 = 4569281) B4569281
theorem B752495 : Blo 499793 752495 := bstep (se 1 (by rfl) ⟨564371, by rfl⟩ : syracuseStep 752495 = 1128743) B1128743
theorem B752735 : Blo 499793 752735 := bstep (se 1 (by rfl) ⟨564551, by rfl⟩ : syracuseStep 752735 = 1129103) B1129103
theorem B752795 : Blo 499793 752795 := bstep (se 1 (by rfl) ⟨564596, by rfl⟩ : syracuseStep 752795 = 1129193) B1129193
theorem B5700779 : Blo 499793 5700779 := bstep (se 1 (by rfl) ⟨4275584, by rfl⟩ : syracuseStep 5700779 = 8551169) B8551169
theorem B2850025 : Blo 499793 2850025 := bstep (se 2 (by rfl) ⟨1068759, by rfl⟩ : syracuseStep 2850025 = 2137519) B2137519
theorem B752951 : Blo 499793 752951 := bstep (se 1 (by rfl) ⟨564713, by rfl⟩ : syracuseStep 752951 = 1129427) B1129427
theorem B7142863 : Blo 499793 7142863 := bstep (se 1 (by rfl) ⟨5357147, by rfl⟩ : syracuseStep 7142863 = 10714295) B10714295
theorem B753131 : Blo 499793 753131 := bstep (se 1 (by rfl) ⟨564848, by rfl⟩ : syracuseStep 753131 = 1129697) B1129697
theorem B1900199 : Blo 499793 1900199 := bstep (se 1 (by rfl) ⟨1425149, by rfl⟩ : syracuseStep 1900199 = 2850299) B2850299
theorem B753335 : Blo 499793 753335 := bstep (se 1 (by rfl) ⟨565001, by rfl⟩ : syracuseStep 753335 = 1130003) B1130003
theorem B3210995 : Blo 499793 3210995 := bstep (se 1 (by rfl) ⟨2408246, by rfl⟩ : syracuseStep 3210995 = 4816493) B4816493
theorem B5439275 : Blo 499793 5439275 := bstep (se 1 (by rfl) ⟨4079456, by rfl⟩ : syracuseStep 5439275 = 8158913) B8158913
theorem B753545 : Blo 499793 753545 := bstep (se 2 (by rfl) ⟨282579, by rfl⟩ : syracuseStep 753545 = 565159) B565159
theorem B753983 : Blo 499793 753983 := bstep (se 1 (by rfl) ⟨565487, by rfl⟩ : syracuseStep 753983 = 1130975) B1130975
theorem B754151 : Blo 499793 754151 := bstep (se 1 (by rfl) ⟨565613, by rfl⟩ : syracuseStep 754151 = 1131227) B1131227
theorem B2032219 : Blo 499793 2032219 := bstep (se 1 (by rfl) ⟨1524164, by rfl⟩ : syracuseStep 2032219 = 3048329) B3048329
theorem B1901171 : Blo 499793 1901171 := bstep (se 1 (by rfl) ⟨1425878, by rfl⟩ : syracuseStep 1901171 = 2851757) B2851757
theorem B2360495 : Blo 499793 2360495 := bstep (se 1 (by rfl) ⟨1770371, by rfl⟩ : syracuseStep 2360495 = 3540743) B3540743
theorem B952393 : Blo 499793 952393 := bstep (se 2 (by rfl) ⟨357147, by rfl⟩ : syracuseStep 952393 = 714295) B714295
theorem B1903571 : Blo 499793 1903571 := bstep (se 1 (by rfl) ⟨1427678, by rfl⟩ : syracuseStep 1903571 = 2855357) B2855357
theorem B1018835 : Blo 499793 1018835 := bstep (se 1 (by rfl) ⟨764126, by rfl⟩ : syracuseStep 1018835 = 1528253) B1528253
theorem B9637289 : Blo 499793 9637289 := bstep (se 2 (by rfl) ⟨3613983, by rfl⟩ : syracuseStep 9637289 = 7227967) B7227967
theorem B1904573 : Blo 499793 1904573 := bstep (se 3 (by rfl) ⟨357107, by rfl⟩ : syracuseStep 1904573 = 714215) B714215
theorem B3215609 : Blo 499793 3215609 := bstep (se 2 (by rfl) ⟨1205853, by rfl⟩ : syracuseStep 3215609 = 2411707) B2411707
theorem B11604343 : Blo 499793 11604343 := bstep (se 1 (by rfl) ⟨8703257, by rfl⟩ : syracuseStep 11604343 = 17406515) B17406515
theorem B954823 : Blo 499793 954823 := bstep (se 1 (by rfl) ⟨716117, by rfl⟩ : syracuseStep 954823 = 1432235) B1432235
theorem B4297319 : Blo 499793 4297319 := bstep (se 1 (by rfl) ⟨3222989, by rfl⟩ : syracuseStep 4297319 = 6445979) B6445979
theorem B4166585 : Blo 499793 4166585 := bstep (se 2 (by rfl) ⟨1562469, by rfl⟩ : syracuseStep 4166585 = 3124939) B3124939
theorem B2134991 : Blo 499793 2134991 := bstep (se 1 (by rfl) ⟨1601243, by rfl⟩ : syracuseStep 2134991 = 3202487) B3202487
theorem B2069483 : Blo 499793 2069483 := bstep (se 1 (by rfl) ⟨1552112, by rfl⟩ : syracuseStep 2069483 = 3104225) B3104225
theorem B3806351 : Blo 499793 3806351 := bstep (se 1 (by rfl) ⟨2854763, by rfl⟩ : syracuseStep 3806351 = 5709527) B5709527
theorem B2135231 : Blo 499793 2135231 := bstep (se 1 (by rfl) ⟨1601423, by rfl⟩ : syracuseStep 2135231 = 3202847) B3202847
theorem B16225559 : Blo 499793 16225559 := bstep (se 1 (by rfl) ⟨12169169, by rfl⟩ : syracuseStep 16225559 = 24338339) B24338339
theorem B562459 : Blo 499793 562459 := bstep (se 1 (by rfl) ⟨421844, by rfl⟩ : syracuseStep 562459 = 843689) B843689
theorem B4069439 : Blo 499793 4069439 := bstep (se 1 (by rfl) ⟨3052079, by rfl⟩ : syracuseStep 4069439 = 6104159) B6104159
theorem B5152025 : Blo 499793 5152025 := bstep (se 2 (by rfl) ⟨1932009, by rfl⟩ : syracuseStep 5152025 = 3864019) B3864019
theorem B9182929 : Blo 499793 9182929 := bstep (se 2 (by rfl) ⟨3443598, by rfl⟩ : syracuseStep 9182929 = 6887197) B6887197
theorem B11771725 : Blo 499793 11771725 := bstep (se 3 (by rfl) ⟨2207198, by rfl⟩ : syracuseStep 11771725 = 4414397) B4414397
theorem B565231 : Blo 499793 565231 := bstep (se 1 (by rfl) ⟨423923, by rfl⟩ : syracuseStep 565231 = 847847) B847847
theorem B499815 : Blo 499793 499815 := bstep (se 1 (by rfl) ⟨374861, by rfl⟩ : syracuseStep 499815 = 749723) B749723
theorem B499935 : Blo 499793 499935 := bstep (se 1 (by rfl) ⟨374951, by rfl⟩ : syracuseStep 499935 = 749903) B749903
theorem B499995 : Blo 499793 499995 := bstep (se 1 (by rfl) ⟨374996, by rfl⟩ : syracuseStep 499995 = 749993) B749993
theorem B1909129 : Blo 499793 1909129 := bstep (se 2 (by rfl) ⟨715923, by rfl⟩ : syracuseStep 1909129 = 1431847) B1431847
theorem B500199 : Blo 499793 500199 := bstep (se 1 (by rfl) ⟨375149, by rfl⟩ : syracuseStep 500199 = 750299) B750299
theorem B565735 : Blo 499793 565735 := bstep (se 1 (by rfl) ⟨424301, by rfl⟩ : syracuseStep 565735 = 848603) B848603
theorem B500379 : Blo 499793 500379 := bstep (se 1 (by rfl) ⟨375284, by rfl⟩ : syracuseStep 500379 = 750569) B750569
theorem B565915 : Blo 499793 565915 := bstep (se 1 (by rfl) ⟨424436, by rfl⟩ : syracuseStep 565915 = 848873) B848873
theorem B500475 : Blo 499793 500475 := bstep (se 1 (by rfl) ⟨375356, by rfl⟩ : syracuseStep 500475 = 750713) B750713
theorem B2139023 : Blo 499793 2139023 := bstep (se 1 (by rfl) ⟨1604267, by rfl⟩ : syracuseStep 2139023 = 3208535) B3208535
theorem B83731481 : Blo 499793 83731481 := bstep (se 2 (by rfl) ⟨31399305, by rfl⟩ : syracuseStep 83731481 = 62798611) B62798611
theorem B500827 : Blo 499793 500827 := bstep (se 1 (by rfl) ⟨375620, by rfl⟩ : syracuseStep 500827 = 751241) B751241
theorem B500967 : Blo 499793 500967 := bstep (se 1 (by rfl) ⟨375725, by rfl⟩ : syracuseStep 500967 = 751451) B751451
theorem B41100533 : Blo 499793 41100533 := bstep (se 5 (by rfl) ⟨1926587, by rfl⟩ : syracuseStep 41100533 = 3853175) B3853175
theorem B500991 : Blo 499793 500991 := bstep (se 1 (by rfl) ⟨375743, by rfl⟩ : syracuseStep 500991 = 751487) B751487
theorem B501055 : Blo 499793 501055 := bstep (se 1 (by rfl) ⟨375791, by rfl⟩ : syracuseStep 501055 = 751583) B751583
theorem B501095 : Blo 499793 501095 := bstep (se 1 (by rfl) ⟨375821, by rfl⟩ : syracuseStep 501095 = 751643) B751643
theorem B501223 : Blo 499793 501223 := bstep (se 1 (by rfl) ⟨375917, by rfl⟩ : syracuseStep 501223 = 751835) B751835
theorem B501403 : Blo 499793 501403 := bstep (se 1 (by rfl) ⟨376052, by rfl⟩ : syracuseStep 501403 = 752105) B752105
theorem B501663 : Blo 499793 501663 := bstep (se 1 (by rfl) ⟨376247, by rfl⟩ : syracuseStep 501663 = 752495) B752495
theorem B501823 : Blo 499793 501823 := bstep (se 1 (by rfl) ⟨376367, by rfl⟩ : syracuseStep 501823 = 752735) B752735
theorem B501863 : Blo 499793 501863 := bstep (se 1 (by rfl) ⟨376397, by rfl⟩ : syracuseStep 501863 = 752795) B752795
theorem B501967 : Blo 499793 501967 := bstep (se 1 (by rfl) ⟨376475, by rfl⟩ : syracuseStep 501967 = 752951) B752951
theorem B1124639 : Blo 499793 1124639 := bstep (se 1 (by rfl) ⟨843479, by rfl⟩ : syracuseStep 1124639 = 1686959) B1686959
theorem B4270391 : Blo 499793 4270391 := bstep (se 1 (by rfl) ⟨3202793, by rfl⟩ : syracuseStep 4270391 = 6405587) B6405587
theorem B502087 : Blo 499793 502087 := bstep (se 1 (by rfl) ⟨376565, by rfl⟩ : syracuseStep 502087 = 753131) B753131
theorem B928171 : Blo 499793 928171 := bstep (se 1 (by rfl) ⟨696128, by rfl⟩ : syracuseStep 928171 = 1392257) B1392257
theorem B502223 : Blo 499793 502223 := bstep (se 1 (by rfl) ⟨376667, by rfl⟩ : syracuseStep 502223 = 753335) B753335
theorem B2140663 : Blo 499793 2140663 := bstep (se 1 (by rfl) ⟨1605497, by rfl⟩ : syracuseStep 2140663 = 3210995) B3210995
theorem B502363 : Blo 499793 502363 := bstep (se 1 (by rfl) ⟨376772, by rfl⟩ : syracuseStep 502363 = 753545) B753545
theorem B2861689 : Blo 499793 2861689 := bstep (se 2 (by rfl) ⟨1073133, by rfl⟩ : syracuseStep 2861689 = 2146267) B2146267
theorem B502527 : Blo 499793 502527 := bstep (se 1 (by rfl) ⟨376895, by rfl⟩ : syracuseStep 502527 = 753791) B753791
theorem B502719 : Blo 499793 502719 := bstep (se 1 (by rfl) ⟨377039, by rfl⟩ : syracuseStep 502719 = 754079) B754079
theorem B1125359 : Blo 499793 1125359 := bstep (se 1 (by rfl) ⟨844019, by rfl⟩ : syracuseStep 1125359 = 1688039) B1688039
theorem B502895 : Blo 499793 502895 := bstep (se 1 (by rfl) ⟨377171, by rfl⟩ : syracuseStep 502895 = 754343) B754343
theorem B502975 : Blo 499793 502975 := bstep (se 1 (by rfl) ⟨377231, by rfl⟩ : syracuseStep 502975 = 754463) B754463
theorem B502991 : Blo 499793 502991 := bstep (se 1 (by rfl) ⟨377243, by rfl⟩ : syracuseStep 502991 = 754487) B754487
theorem B1125611 : Blo 499793 1125611 := bstep (se 1 (by rfl) ⟨844208, by rfl⟩ : syracuseStep 1125611 = 1688417) B1688417
theorem B503111 : Blo 499793 503111 := bstep (se 1 (by rfl) ⟨377333, by rfl⟩ : syracuseStep 503111 = 754667) B754667
theorem B4074947 : Blo 499793 4074947 := bstep (se 1 (by rfl) ⟨3056210, by rfl⟩ : syracuseStep 4074947 = 6112421) B6112421
theorem B3059279 : Blo 499793 3059279 := bstep (se 1 (by rfl) ⟨2294459, by rfl⟩ : syracuseStep 3059279 = 4588919) B4588919
theorem B503451 : Blo 499793 503451 := bstep (se 1 (by rfl) ⟨377588, by rfl⟩ : syracuseStep 503451 = 755177) B755177
theorem B765775 : Blo 499793 765775 := bstep (se 1 (by rfl) ⟨574331, by rfl⟩ : syracuseStep 765775 = 1148663) B1148663
theorem B503711 : Blo 499793 503711 := bstep (se 1 (by rfl) ⟨377783, by rfl⟩ : syracuseStep 503711 = 755567) B755567
theorem B1126655 : Blo 499793 1126655 := bstep (se 1 (by rfl) ⟨844991, by rfl⟩ : syracuseStep 1126655 = 1689983) B1689983
theorem B635359 : Blo 499793 635359 := bstep (se 1 (by rfl) ⟨476519, by rfl⟩ : syracuseStep 635359 = 953039) B953039
theorem B1126889 : Blo 499793 1126889 := bstep (se 2 (by rfl) ⟨422583, by rfl⟩ : syracuseStep 1126889 = 845167) B845167
theorem B2175731 : Blo 499793 2175731 := bstep (se 1 (by rfl) ⟨1631798, by rfl⟩ : syracuseStep 2175731 = 3263597) B3263597
theorem B635951 : Blo 499793 635951 := bstep (se 1 (by rfl) ⟨476963, by rfl⟩ : syracuseStep 635951 = 953927) B953927
theorem B3519551 : Blo 499793 3519551 := bstep (se 1 (by rfl) ⟨2639663, by rfl⟩ : syracuseStep 3519551 = 5279327) B5279327
theorem B7222841 : Blo 499793 7222841 := bstep (se 2 (by rfl) ⟨2708565, by rfl⟩ : syracuseStep 7222841 = 5417131) B5417131
theorem B6109111 : Blo 499793 6109111 := bstep (se 1 (by rfl) ⟨4581833, by rfl⟩ : syracuseStep 6109111 = 9163667) B9163667
theorem B636923 : Blo 499793 636923 := bstep (se 1 (by rfl) ⟨477692, by rfl⟩ : syracuseStep 636923 = 955385) B955385
theorem B1423919 : Blo 499793 1423919 := bstep (se 1 (by rfl) ⟨1067939, by rfl⟩ : syracuseStep 1423919 = 2135879) B2135879
theorem B3062393 : Blo 499793 3062393 := bstep (se 2 (by rfl) ⟨1148397, by rfl⟩ : syracuseStep 3062393 = 2296795) B2296795
theorem B1129319 : Blo 499793 1129319 := bstep (se 1 (by rfl) ⟨846989, by rfl⟩ : syracuseStep 1129319 = 1693979) B1693979
theorem B1358815 : Blo 499793 1358815 := bstep (se 1 (by rfl) ⟨1019111, by rfl⟩ : syracuseStep 1358815 = 2038223) B2038223
theorem B13777895 : Blo 499793 13777895 := bstep (se 1 (by rfl) ⟨10333421, by rfl⟩ : syracuseStep 13777895 = 20666843) B20666843
theorem B3816557 : Blo 499793 3816557 := bstep (se 3 (by rfl) ⟨715604, by rfl⟩ : syracuseStep 3816557 = 1431209) B1431209
theorem B1129967 : Blo 499793 1129967 := bstep (se 1 (by rfl) ⟨847475, by rfl⟩ : syracuseStep 1129967 = 1694951) B1694951
theorem B2703269 : Blo 499793 2703269 := bstep (se 4 (by rfl) ⟨253431, by rfl⟩ : syracuseStep 2703269 = 506863) B506863
theorem B2539511 : Blo 499793 2539511 := bstep (se 1 (by rfl) ⟨1904633, by rfl⟩ : syracuseStep 2539511 = 3809267) B3809267
theorem B1130489 : Blo 499793 1130489 := bstep (se 2 (by rfl) ⟨423933, by rfl⟩ : syracuseStep 1130489 = 847867) B847867
theorem B3818015 : Blo 499793 3818015 := bstep (se 1 (by rfl) ⟨2863511, by rfl⟩ : syracuseStep 3818015 = 5727023) B5727023
theorem B1688147 : Blo 499793 1688147 := bstep (se 1 (by rfl) ⟨1266110, by rfl⟩ : syracuseStep 1688147 = 2532221) B2532221
theorem B1131623 : Blo 499793 1131623 := bstep (se 1 (by rfl) ⟨848717, by rfl⟩ : syracuseStep 1131623 = 1697435) B1697435
theorem B1132271 : Blo 499793 1132271 := bstep (se 1 (by rfl) ⟨849203, by rfl⟩ : syracuseStep 1132271 = 1698407) B1698407
theorem B2868979 : Blo 499793 2868979 := bstep (se 1 (by rfl) ⟨2151734, by rfl⟩ : syracuseStep 2868979 = 4303469) B4303469
theorem B2541455 : Blo 499793 2541455 := bstep (se 1 (by rfl) ⟨1906091, by rfl⟩ : syracuseStep 2541455 = 3812183) B3812183
theorem B1132523 : Blo 499793 1132523 := bstep (se 1 (by rfl) ⟨849392, by rfl⟩ : syracuseStep 1132523 = 1698785) B1698785
theorem B1427645 : Blo 499793 1427645 := bstep (se 3 (by rfl) ⟨267683, by rfl⟩ : syracuseStep 1427645 = 535367) B535367
theorem B4835639 : Blo 499793 4835639 := bstep (se 1 (by rfl) ⟨3626729, by rfl⟩ : syracuseStep 4835639 = 7253459) B7253459
theorem B3820445 : Blo 499793 3820445 := bstep (se 3 (by rfl) ⟨716333, by rfl⟩ : syracuseStep 3820445 = 1432667) B1432667
theorem B4082993 : Blo 499793 4082993 := bstep (se 2 (by rfl) ⟨1531122, by rfl⟩ : syracuseStep 4082993 = 3062245) B3062245
theorem B1069033 : Blo 499793 1069033 := bstep (se 2 (by rfl) ⟨400887, by rfl⟩ : syracuseStep 1069033 = 801775) B801775
theorem B9523817 : Blo 499793 9523817 := bstep (se 2 (by rfl) ⟨3571431, by rfl⟩ : syracuseStep 9523817 = 7142863) B7142863
theorem B1692413 : Blo 499793 1692413 := bstep (se 3 (by rfl) ⟨317327, by rfl⟩ : syracuseStep 1692413 = 634655) B634655
theorem B1692575 : Blo 499793 1692575 := bstep (se 1 (by rfl) ⟨1269431, by rfl⟩ : syracuseStep 1692575 = 2538863) B2538863
theorem B1266799 : Blo 499793 1266799 := bstep (se 1 (by rfl) ⟨950099, by rfl⟩ : syracuseStep 1266799 = 1900199) B1900199
theorem B1627303 : Blo 499793 1627303 := bstep (se 1 (by rfl) ⟨1220477, by rfl⟩ : syracuseStep 1627303 = 2440955) B2440955
theorem B3626183 : Blo 499793 3626183 := bstep (se 1 (by rfl) ⟨2719637, by rfl⟩ : syracuseStep 3626183 = 5439275) B5439275
theorem B10442459 : Blo 499793 10442459 := bstep (se 1 (by rfl) ⟨7831844, by rfl⟩ : syracuseStep 10442459 = 15663689) B15663689
theorem B7231315 : Blo 499793 7231315 := bstep (se 1 (by rfl) ⟨5423486, by rfl⟩ : syracuseStep 7231315 = 10846973) B10846973
theorem B3823847 : Blo 499793 3823847 := bstep (se 1 (by rfl) ⟨2867885, by rfl⟩ : syracuseStep 3823847 = 5735771) B5735771
theorem B1268095 : Blo 499793 1268095 := bstep (se 1 (by rfl) ⟨951071, by rfl⟩ : syracuseStep 1268095 = 1902143) B1902143
theorem B16243091 : Blo 499793 16243091 := bstep (se 1 (by rfl) ⟨12182318, by rfl⟩ : syracuseStep 16243091 = 24364637) B24364637
theorem B1694249 : Blo 499793 1694249 := bstep (se 2 (by rfl) ⟨635343, by rfl⟩ : syracuseStep 1694249 = 1270687) B1270687
theorem B13687703 : Blo 499793 13687703 := bstep (se 1 (by rfl) ⟨10265777, by rfl⟩ : syracuseStep 13687703 = 20531555) B20531555
theorem B4283513 : Blo 499793 4283513 := bstep (se 2 (by rfl) ⟨1606317, by rfl⟩ : syracuseStep 4283513 = 3212635) B3212635
theorem B8774245 : Blo 499793 8774245 := bstep (se 4 (by rfl) ⟨822585, by rfl⟩ : syracuseStep 8774245 = 1645171) B1645171
theorem B1270505 : Blo 499793 1270505 := bstep (se 2 (by rfl) ⟨476439, by rfl⟩ : syracuseStep 1270505 = 952879) B952879
theorem B8151839 : Blo 499793 8151839 := bstep (se 1 (by rfl) ⟨6113879, by rfl⟩ : syracuseStep 8151839 = 12227759) B12227759
theorem B844607 : Blo 499793 844607 := bstep (se 1 (by rfl) ⟨633455, by rfl⟩ : syracuseStep 844607 = 1266911) B1266911
theorem B8709551 : Blo 499793 8709551 := bstep (se 1 (by rfl) ⟨6532163, by rfl⟩ : syracuseStep 8709551 = 13064327) B13064327
theorem B714415 : Blo 499793 714415 := bstep (se 1 (by rfl) ⟨535811, by rfl⟩ : syracuseStep 714415 = 1071623) B1071623
theorem B845545 : Blo 499793 845545 := bstep (se 2 (by rfl) ⟨317079, by rfl⟩ : syracuseStep 845545 = 634159) B634159
theorem B2418473 : Blo 499793 2418473 := bstep (se 2 (by rfl) ⟨906927, by rfl⟩ : syracuseStep 2418473 = 1813855) B1813855
theorem B3204947 : Blo 499793 3204947 := bstep (se 1 (by rfl) ⟨2403710, by rfl⟩ : syracuseStep 3204947 = 4807421) B4807421
theorem B715007 : Blo 499793 715007 := bstep (se 1 (by rfl) ⟨536255, by rfl⟩ : syracuseStep 715007 = 1072511) B1072511
theorem B6187691 : Blo 499793 6187691 := bstep (se 1 (by rfl) ⟨4640768, by rfl⟩ : syracuseStep 6187691 = 9281537) B9281537
theorem B29420243 : Blo 499793 29420243 := bstep (se 1 (by rfl) ⟨22065182, by rfl⟩ : syracuseStep 29420243 = 44130365) B44130365
theorem B1207199 : Blo 499793 1207199 := bstep (se 1 (by rfl) ⟨905399, by rfl⟩ : syracuseStep 1207199 = 1810799) B1810799
theorem B1272743 : Blo 499793 1272743 := bstep (se 1 (by rfl) ⟨954557, by rfl⟩ : syracuseStep 1272743 = 1909115) B1909115
theorem B1699001 : Blo 499793 1699001 := bstep (se 2 (by rfl) ⟨637125, by rfl⟩ : syracuseStep 1699001 = 1274251) B1274251
theorem B1699163 : Blo 499793 1699163 := bstep (se 1 (by rfl) ⟨1274372, by rfl⟩ : syracuseStep 1699163 = 2548745) B2548745
theorem B15625723 : Blo 499793 15625723 := bstep (se 1 (by rfl) ⟨11719292, by rfl⟩ : syracuseStep 15625723 = 23438585) B23438585
theorem B848063 : Blo 499793 848063 := bstep (se 1 (by rfl) ⟨636047, by rfl⟩ : syracuseStep 848063 = 1272095) B1272095
theorem B651487 : Blo 499793 651487 := bstep (se 1 (by rfl) ⟨488615, by rfl⟩ : syracuseStep 651487 = 977231) B977231
theorem B1274687 : Blo 499793 1274687 := bstep (se 1 (by rfl) ⟨956015, by rfl⟩ : syracuseStep 1274687 = 1912031) B1912031
theorem B848711 : Blo 499793 848711 := bstep (se 1 (by rfl) ⟨636533, by rfl⟩ : syracuseStep 848711 = 1273067) B1273067
theorem B750527 : Blo 499793 750527 := bstep (se 1 (by rfl) ⟨562895, by rfl⟩ : syracuseStep 750527 = 1125791) B1125791
theorem B950267 : Blo 499793 950267 := bstep (se 1 (by rfl) ⟨712700, by rfl⟩ : syracuseStep 950267 = 1425401) B1425401
theorem B750575 : Blo 499793 750575 := bstep (se 1 (by rfl) ⟨562931, by rfl⟩ : syracuseStep 750575 = 1125863) B1125863
theorem B1275041 : Blo 499793 1275041 := bstep (se 2 (by rfl) ⟨478140, by rfl⟩ : syracuseStep 1275041 = 956281) B956281
theorem B2979287 : Blo 499793 2979287 := bstep (se 1 (by rfl) ⟨2234465, by rfl⟩ : syracuseStep 2979287 = 4468931) B4468931
theorem B751211 : Blo 499793 751211 := bstep (se 1 (by rfl) ⟨563408, by rfl⟩ : syracuseStep 751211 = 1126817) B1126817
theorem B522343 : Blo 499793 522343 := bstep (se 1 (by rfl) ⟨391757, by rfl⟩ : syracuseStep 522343 = 783515) B783515
theorem B1013897 : Blo 499793 1013897 := bstep (se 2 (by rfl) ⟨380211, by rfl⟩ : syracuseStep 1013897 = 760423) B760423
theorem B1604063 : Blo 499793 1604063 := bstep (se 1 (by rfl) ⟨1203047, by rfl⟩ : syracuseStep 1604063 = 2406095) B2406095
theorem B752231 : Blo 499793 752231 := bstep (se 1 (by rfl) ⟨564173, by rfl⟩ : syracuseStep 752231 = 1128347) B1128347
theorem B3800033 : Blo 499793 3800033 := bstep (se 2 (by rfl) ⟨1425012, by rfl⟩ : syracuseStep 3800033 = 2850025) B2850025
theorem B51412151 : Blo 499793 51412151 := bstep (se 1 (by rfl) ⟨38559113, by rfl⟩ : syracuseStep 51412151 = 77118227) B77118227
theorem B2030791 : Blo 499793 2030791 := bstep (se 1 (by rfl) ⟨1523093, by rfl⟩ : syracuseStep 2030791 = 3046187) B3046187
theorem B3800519 : Blo 499793 3800519 := bstep (se 1 (by rfl) ⟨2850389, by rfl⟩ : syracuseStep 3800519 = 5700779) B5700779
theorem B753119 : Blo 499793 753119 := bstep (se 1 (by rfl) ⟨564839, by rfl⟩ : syracuseStep 753119 = 1129679) B1129679
theorem B753179 : Blo 499793 753179 := bstep (se 1 (by rfl) ⟨564884, by rfl⟩ : syracuseStep 753179 = 1129769) B1129769
theorem B753371 : Blo 499793 753371 := bstep (se 1 (by rfl) ⟨565028, by rfl⟩ : syracuseStep 753371 = 1130057) B1130057
theorem B28934009 : Blo 499793 28934009 := bstep (se 2 (by rfl) ⟨10850253, by rfl⟩ : syracuseStep 28934009 = 21700507) B21700507
theorem B753599 : Blo 499793 753599 := bstep (se 1 (by rfl) ⟨565199, by rfl⟩ : syracuseStep 753599 = 1130399) B1130399
theorem B754313 : Blo 499793 754313 := bstep (se 2 (by rfl) ⟨282867, by rfl⟩ : syracuseStep 754313 = 565735) B565735
theorem B754415 : Blo 499793 754415 := bstep (se 1 (by rfl) ⟨565811, by rfl⟩ : syracuseStep 754415 = 1131623) B1131623
theorem B1573663 : Blo 499793 1573663 := bstep (se 1 (by rfl) ⟨1180247, by rfl⟩ : syracuseStep 1573663 = 2360495) B2360495
theorem B11698993 : Blo 499793 11698993 := bstep (se 2 (by rfl) ⟨4387122, by rfl⟩ : syracuseStep 11698993 = 8774245) B8774245
theorem B754553 : Blo 499793 754553 := bstep (se 2 (by rfl) ⟨282957, by rfl⟩ : syracuseStep 754553 = 565915) B565915
theorem B754847 : Blo 499793 754847 := bstep (se 1 (by rfl) ⟨566135, by rfl⟩ : syracuseStep 754847 = 1132271) B1132271
theorem B755015 : Blo 499793 755015 := bstep (se 1 (by rfl) ⟨566261, by rfl⟩ : syracuseStep 755015 = 1132523) B1132523
theorem B951763 : Blo 499793 951763 := bstep (se 1 (by rfl) ⟨713822, by rfl⟩ : syracuseStep 951763 = 1427645) B1427645
theorem B2721995 : Blo 499793 2721995 := bstep (se 1 (by rfl) ⟨2041496, by rfl⟩ : syracuseStep 2721995 = 4082993) B4082993
theorem B4950245 : Blo 499793 4950245 := bstep (se 4 (by rfl) ⟨464085, by rfl⟩ : syracuseStep 4950245 = 928171) B928171
theorem B952553 : Blo 499793 952553 := bstep (se 2 (by rfl) ⟨357207, by rfl⟩ : syracuseStep 952553 = 714415) B714415
theorem B6424859 : Blo 499793 6424859 := bstep (se 1 (by rfl) ⟨4818644, by rfl⟩ : syracuseStep 6424859 = 9637289) B9637289
theorem B2854217 : Blo 499793 2854217 := bstep (se 2 (by rfl) ⟨1070331, by rfl⟩ : syracuseStep 2854217 = 2140663) B2140663
theorem B10817039 : Blo 499793 10817039 := bstep (se 1 (by rfl) ⟨8112779, by rfl⟩ : syracuseStep 10817039 = 16225559) B16225559
theorem B2855675 : Blo 499793 2855675 := bstep (se 1 (by rfl) ⟨2141756, by rfl⟩ : syracuseStep 2855675 = 4283513) B4283513
theorem B1021033 : Blo 499793 1021033 := bstep (se 2 (by rfl) ⟨382887, by rfl⟩ : syracuseStep 1021033 = 765775) B765775
theorem B15472457 : Blo 499793 15472457 := bstep (se 2 (by rfl) ⟨5802171, by rfl⟩ : syracuseStep 15472457 = 11604343) B11604343
theorem B563071 : Blo 499793 563071 := bstep (se 1 (by rfl) ⟨422303, by rfl⟩ : syracuseStep 563071 = 844607) B844607
theorem B1906685 : Blo 499793 1906685 := bstep (se 3 (by rfl) ⟨357503, by rfl⟩ : syracuseStep 1906685 = 715007) B715007
theorem B27400355 : Blo 499793 27400355 := bstep (se 1 (by rfl) ⟨20550266, by rfl⟩ : syracuseStep 27400355 = 41100533) B41100533
theorem B5806367 : Blo 499793 5806367 := bstep (se 1 (by rfl) ⟨4354775, by rfl⟩ : syracuseStep 5806367 = 8709551) B8709551
theorem B1612315 : Blo 499793 1612315 := bstep (se 1 (by rfl) ⟨1209236, by rfl⟩ : syracuseStep 1612315 = 2418473) B2418473
theorem B2136631 : Blo 499793 2136631 := bstep (se 1 (by rfl) ⟨1602473, by rfl⟩ : syracuseStep 2136631 = 3204947) B3204947
theorem B2169737 : Blo 499793 2169737 := bstep (se 2 (by rfl) ⟨813651, by rfl⟩ : syracuseStep 2169737 = 1627303) B1627303
theorem B2039519 : Blo 499793 2039519 := bstep (se 1 (by rfl) ⟨1529639, by rfl⟩ : syracuseStep 2039519 = 3059279) B3059279
theorem B9641753 : Blo 499793 9641753 := bstep (se 2 (by rfl) ⟨3615657, by rfl⟩ : syracuseStep 9641753 = 7231315) B7231315
theorem B36741053 : Blo 499793 36741053 := bstep (se 3 (by rfl) ⟨6888947, by rfl⟩ : syracuseStep 36741053 = 13777895) B13777895
theorem B565375 : Blo 499793 565375 := bstep (se 1 (by rfl) ⟨424031, by rfl⟩ : syracuseStep 565375 = 848063) B848063
theorem B696457 : Blo 499793 696457 := bstep (se 2 (by rfl) ⟨261171, by rfl⟩ : syracuseStep 696457 = 522343) B522343
theorem B1450487 : Blo 499793 1450487 := bstep (se 1 (by rfl) ⟨1087865, by rfl⟩ : syracuseStep 1450487 = 2175731) B2175731
theorem B565807 : Blo 499793 565807 := bstep (se 1 (by rfl) ⟨424355, by rfl⟩ : syracuseStep 565807 = 848711) B848711
theorem B500351 : Blo 499793 500351 := bstep (se 1 (by rfl) ⟨375263, by rfl⟩ : syracuseStep 500351 = 750527) B750527
theorem B500383 : Blo 499793 500383 := bstep (se 1 (by rfl) ⟨375287, by rfl⟩ : syracuseStep 500383 = 750575) B750575
theorem B13738733 : Blo 499793 13738733 := bstep (se 3 (by rfl) ⟨2576012, by rfl⟩ : syracuseStep 13738733 = 5152025) B5152025
theorem B500807 : Blo 499793 500807 := bstep (se 1 (by rfl) ⟨375605, by rfl⟩ : syracuseStep 500807 = 751211) B751211
theorem B1811753 : Blo 499793 1811753 := bstep (se 2 (by rfl) ⟨679407, by rfl⟩ : syracuseStep 1811753 = 1358815) B1358815
theorem B501487 : Blo 499793 501487 := bstep (se 1 (by rfl) ⟨376115, by rfl⟩ : syracuseStep 501487 = 752231) B752231
theorem B2041595 : Blo 499793 2041595 := bstep (se 1 (by rfl) ⟨1531196, by rfl⟩ : syracuseStep 2041595 = 3062393) B3062393
theorem B2533355 : Blo 499793 2533355 := bstep (se 1 (by rfl) ⟨1900016, by rfl⟩ : syracuseStep 2533355 = 3800033) B3800033
theorem B2533679 : Blo 499793 2533679 := bstep (se 1 (by rfl) ⟨1900259, by rfl⟩ : syracuseStep 2533679 = 3800519) B3800519
theorem B502079 : Blo 499793 502079 := bstep (se 1 (by rfl) ⟨376559, by rfl⟩ : syracuseStep 502079 = 753119) B753119
theorem B502119 : Blo 499793 502119 := bstep (se 1 (by rfl) ⟨376589, by rfl⟩ : syracuseStep 502119 = 753179) B753179
theorem B502247 : Blo 499793 502247 := bstep (se 1 (by rfl) ⟨376685, by rfl⟩ : syracuseStep 502247 = 753371) B753371
theorem B502399 : Blo 499793 502399 := bstep (se 1 (by rfl) ⟨376799, by rfl⟩ : syracuseStep 502399 = 753599) B753599
theorem B633511 : Blo 499793 633511 := bstep (se 1 (by rfl) ⟨475133, by rfl⟩ : syracuseStep 633511 = 950267) B950267
theorem B502655 : Blo 499793 502655 := bstep (se 1 (by rfl) ⟨376991, by rfl⟩ : syracuseStep 502655 = 753983) B753983
theorem B502767 : Blo 499793 502767 := bstep (se 1 (by rfl) ⟨377075, by rfl⟩ : syracuseStep 502767 = 754151) B754151
theorem B1125431 : Blo 499793 1125431 := bstep (se 1 (by rfl) ⟨844073, by rfl⟩ : syracuseStep 1125431 = 1688147) B1688147
theorem B3223759 : Blo 499793 3223759 := bstep (se 1 (by rfl) ⟨2417819, by rfl⟩ : syracuseStep 3223759 = 4835639) B4835639
theorem B1127393 : Blo 499793 1127393 := bstep (se 2 (by rfl) ⟨422772, by rfl⟩ : syracuseStep 1127393 = 845545) B845545
theorem B5518621 : Blo 499793 5518621 := bstep (se 3 (by rfl) ⟨1034741, by rfl⟩ : syracuseStep 5518621 = 2069483) B2069483
theorem B2143739 : Blo 499793 2143739 := bstep (se 1 (by rfl) ⟨1607804, by rfl⟩ : syracuseStep 2143739 = 3215609) B3215609
theorem B2864879 : Blo 499793 2864879 := bstep (se 1 (by rfl) ⟨2148659, by rfl⟩ : syracuseStep 2864879 = 4297319) B4297319
theorem B1128275 : Blo 499793 1128275 := bstep (se 1 (by rfl) ⟨846206, by rfl⟩ : syracuseStep 1128275 = 1692413) B1692413
theorem B1128383 : Blo 499793 1128383 := bstep (se 1 (by rfl) ⟨846287, by rfl⟩ : syracuseStep 1128383 = 1692575) B1692575
theorem B1423327 : Blo 499793 1423327 := bstep (se 1 (by rfl) ⟨1067495, by rfl⟩ : syracuseStep 1423327 = 2134991) B2134991
theorem B2537567 : Blo 499793 2537567 := bstep (se 1 (by rfl) ⟨1903175, by rfl⟩ : syracuseStep 2537567 = 3806351) B3806351
theorem B1423487 : Blo 499793 1423487 := bstep (se 1 (by rfl) ⟨1067615, by rfl⟩ : syracuseStep 1423487 = 2135231) B2135231
theorem B3815585 : Blo 499793 3815585 := bstep (se 2 (by rfl) ⟨1430844, by rfl⟩ : syracuseStep 3815585 = 2861689) B2861689
theorem B6961639 : Blo 499793 6961639 := bstep (se 1 (by rfl) ⟨5221229, by rfl⟩ : syracuseStep 6961639 = 10442459) B10442459
theorem B10828727 : Blo 499793 10828727 := bstep (se 1 (by rfl) ⟨8121545, by rfl⟩ : syracuseStep 10828727 = 16243091) B16243091
theorem B1129499 : Blo 499793 1129499 := bstep (se 1 (by rfl) ⟨847124, by rfl⟩ : syracuseStep 1129499 = 1694249) B1694249
theorem B9125135 : Blo 499793 9125135 := bstep (se 1 (by rfl) ⟨6843851, by rfl⟩ : syracuseStep 9125135 = 13687703) B13687703
theorem B1425377 : Blo 499793 1425377 := bstep (se 2 (by rfl) ⟨534516, by rfl⟩ : syracuseStep 1425377 = 1069033) B1069033
theorem B868649 : Blo 499793 868649 := bstep (se 2 (by rfl) ⟨325743, by rfl⟩ : syracuseStep 868649 = 651487) B651487
theorem B2703725 : Blo 499793 2703725 := bstep (se 3 (by rfl) ⟨506948, by rfl⟩ : syracuseStep 2703725 = 1013897) B1013897
theorem B1426015 : Blo 499793 1426015 := bstep (se 1 (by rfl) ⟨1069511, by rfl⟩ : syracuseStep 1426015 = 2139023) B2139023
theorem B55820987 : Blo 499793 55820987 := bstep (se 1 (by rfl) ⟨41865740, by rfl⟩ : syracuseStep 55820987 = 83731481) B83731481
theorem B1689065 : Blo 499793 1689065 := bstep (se 2 (by rfl) ⟨633399, by rfl⟩ : syracuseStep 1689065 = 1266799) B1266799
theorem B19613495 : Blo 499793 19613495 := bstep (se 1 (by rfl) ⟨14710121, by rfl⟩ : syracuseStep 19613495 = 29420243) B29420243
theorem B804799 : Blo 499793 804799 := bstep (se 1 (by rfl) ⟨603599, by rfl⟩ : syracuseStep 804799 = 1207199) B1207199
theorem B1132667 : Blo 499793 1132667 := bstep (se 1 (by rfl) ⟨849500, by rfl⟩ : syracuseStep 1132667 = 1699001) B1699001
theorem B1132775 : Blo 499793 1132775 := bstep (se 1 (by rfl) ⟨849581, by rfl⟩ : syracuseStep 1132775 = 1699163) B1699163
theorem B8145481 : Blo 499793 8145481 := bstep (se 2 (by rfl) ⟨3054555, by rfl⟩ : syracuseStep 8145481 = 6109111) B6109111
theorem B1690793 : Blo 499793 1690793 := bstep (se 2 (by rfl) ⟨634047, by rfl⟩ : syracuseStep 1690793 = 1268095) B1268095
theorem B2346367 : Blo 499793 2346367 := bstep (se 1 (by rfl) ⟨1759775, by rfl⟩ : syracuseStep 2346367 = 3519551) B3519551
theorem B1986191 : Blo 499793 1986191 := bstep (se 1 (by rfl) ⟨1489643, by rfl⟩ : syracuseStep 1986191 = 2979287) B2979287
theorem B2707721 : Blo 499793 2707721 := bstep (se 2 (by rfl) ⟨1015395, by rfl⟩ : syracuseStep 2707721 = 2030791) B2030791
theorem B1069375 : Blo 499793 1069375 := bstep (se 1 (by rfl) ⟨802031, by rfl⟩ : syracuseStep 1069375 = 1604063) B1604063
theorem B2544371 : Blo 499793 2544371 := bstep (se 1 (by rfl) ⟨1908278, by rfl⟩ : syracuseStep 2544371 = 3816557) B3816557
theorem B12243905 : Blo 499793 12243905 := bstep (se 2 (by rfl) ⟨4591464, by rfl⟩ : syracuseStep 12243905 = 9182929) B9182929
theorem B19289339 : Blo 499793 19289339 := bstep (se 1 (by rfl) ⟨14467004, by rfl⟩ : syracuseStep 19289339 = 28934009) B28934009
theorem B1693007 : Blo 499793 1693007 := bstep (se 1 (by rfl) ⟨1269755, by rfl⟩ : syracuseStep 1693007 = 2539511) B2539511
theorem B2545343 : Blo 499793 2545343 := bstep (se 1 (by rfl) ⟨1909007, by rfl⟩ : syracuseStep 2545343 = 3818015) B3818015
theorem B1267447 : Blo 499793 1267447 := bstep (se 1 (by rfl) ⟨950585, by rfl⟩ : syracuseStep 1267447 = 1901171) B1901171
theorem B2545505 : Blo 499793 2545505 := bstep (se 2 (by rfl) ⟨954564, by rfl⟩ : syracuseStep 2545505 = 1909129) B1909129
theorem B2709625 : Blo 499793 2709625 := bstep (se 2 (by rfl) ⟨1016109, by rfl⟩ : syracuseStep 2709625 = 2032219) B2032219
theorem B1694303 : Blo 499793 1694303 := bstep (se 1 (by rfl) ⟨1270727, by rfl⟩ : syracuseStep 1694303 = 2541455) B2541455
theorem B2546963 : Blo 499793 2546963 := bstep (se 1 (by rfl) ⟨1910222, by rfl⟩ : syracuseStep 2546963 = 3820445) B3820445
theorem B1269047 : Blo 499793 1269047 := bstep (se 1 (by rfl) ⟨951785, by rfl⟩ : syracuseStep 1269047 = 1903571) B1903571
theorem B679223 : Blo 499793 679223 := bstep (se 1 (by rfl) ⟨509417, by rfl⟩ : syracuseStep 679223 = 1018835) B1018835
theorem B3825305 : Blo 499793 3825305 := bstep (se 2 (by rfl) ⟨1434489, by rfl⟩ : syracuseStep 3825305 = 2868979) B2868979
theorem B1269715 : Blo 499793 1269715 := bstep (se 1 (by rfl) ⟨952286, by rfl⟩ : syracuseStep 1269715 = 1904573) B1904573
theorem B1269857 : Blo 499793 1269857 := bstep (se 2 (by rfl) ⟨476196, by rfl⟩ : syracuseStep 1269857 = 952393) B952393
theorem B1695869 : Blo 499793 1695869 := bstep (se 3 (by rfl) ⟨317975, by rfl⟩ : syracuseStep 1695869 = 635951) B635951
theorem B6349211 : Blo 499793 6349211 := bstep (se 1 (by rfl) ⟨4761908, by rfl⟩ : syracuseStep 6349211 = 9523817) B9523817
theorem B2777723 : Blo 499793 2777723 := bstep (se 1 (by rfl) ⟨2083292, by rfl⟩ : syracuseStep 2777723 = 4166585) B4166585
theorem B2417455 : Blo 499793 2417455 := bstep (se 1 (by rfl) ⟨1813091, by rfl⟩ : syracuseStep 2417455 = 3626183) B3626183
theorem B2712959 : Blo 499793 2712959 := bstep (se 1 (by rfl) ⟨2034719, by rfl⟩ : syracuseStep 2712959 = 4069439) B4069439
theorem B2549231 : Blo 499793 2549231 := bstep (se 1 (by rfl) ⟨1911923, by rfl⟩ : syracuseStep 2549231 = 3823847) B3823847
theorem B20834297 : Blo 499793 20834297 := bstep (se 2 (by rfl) ⟨7812861, by rfl⟩ : syracuseStep 20834297 = 15625723) B15625723
theorem B1698461 : Blo 499793 1698461 := bstep (se 3 (by rfl) ⟨318461, by rfl⟩ : syracuseStep 1698461 = 636923) B636923
theorem B847003 : Blo 499793 847003 := bstep (se 1 (by rfl) ⟨635252, by rfl⟩ : syracuseStep 847003 = 1270505) B1270505
theorem B5434559 : Blo 499793 5434559 := bstep (se 1 (by rfl) ⟨4075919, by rfl⟩ : syracuseStep 5434559 = 8151839) B8151839
theorem B1273097 : Blo 499793 1273097 := bstep (se 2 (by rfl) ⟨477411, by rfl⟩ : syracuseStep 1273097 = 954823) B954823
theorem B847145 : Blo 499793 847145 := bstep (se 2 (by rfl) ⟨317679, by rfl⟩ : syracuseStep 847145 = 635359) B635359
theorem B3797117 : Blo 499793 3797117 := bstep (se 3 (by rfl) ⟨711959, by rfl⟩ : syracuseStep 3797117 = 1423919) B1423919
theorem B749759 : Blo 499793 749759 := bstep (se 1 (by rfl) ⟨562319, by rfl⟩ : syracuseStep 749759 = 1124639) B1124639
theorem B2846927 : Blo 499793 2846927 := bstep (se 1 (by rfl) ⟨2135195, by rfl⟩ : syracuseStep 2846927 = 4270391) B4270391
theorem B749945 : Blo 499793 749945 := bstep (se 2 (by rfl) ⟨281229, by rfl⟩ : syracuseStep 749945 = 562459) B562459
theorem B4125127 : Blo 499793 4125127 := bstep (se 1 (by rfl) ⟨3093845, by rfl⟩ : syracuseStep 4125127 = 6187691) B6187691
theorem B848495 : Blo 499793 848495 := bstep (se 1 (by rfl) ⟨636371, by rfl⟩ : syracuseStep 848495 = 1272743) B1272743
theorem B750239 : Blo 499793 750239 := bstep (se 1 (by rfl) ⟨562679, by rfl⟩ : syracuseStep 750239 = 1125359) B1125359
theorem B750407 : Blo 499793 750407 := bstep (se 1 (by rfl) ⟨562805, by rfl⟩ : syracuseStep 750407 = 1125611) B1125611
theorem B2716631 : Blo 499793 2716631 := bstep (se 1 (by rfl) ⟨2037473, by rfl⟩ : syracuseStep 2716631 = 4074947) B4074947
theorem B751103 : Blo 499793 751103 := bstep (se 1 (by rfl) ⟨563327, by rfl⟩ : syracuseStep 751103 = 1126655) B1126655
theorem B751259 : Blo 499793 751259 := bstep (se 1 (by rfl) ⟨563444, by rfl⟩ : syracuseStep 751259 = 1126889) B1126889
theorem B849791 : Blo 499793 849791 := bstep (se 1 (by rfl) ⟨637343, by rfl⟩ : syracuseStep 849791 = 1274687) B1274687
theorem B850027 : Blo 499793 850027 := bstep (se 1 (by rfl) ⟨637520, by rfl⟩ : syracuseStep 850027 = 1275041) B1275041
theorem B4815227 : Blo 499793 4815227 := bstep (se 1 (by rfl) ⟨3611420, by rfl⟩ : syracuseStep 4815227 = 7222841) B7222841
theorem B752879 : Blo 499793 752879 := bstep (se 1 (by rfl) ⟨564659, by rfl⟩ : syracuseStep 752879 = 1129319) B1129319
theorem B34274767 : Blo 499793 34274767 := bstep (se 1 (by rfl) ⟨25706075, by rfl⟩ : syracuseStep 34274767 = 51412151) B51412151
theorem B753311 : Blo 499793 753311 := bstep (se 1 (by rfl) ⟨564983, by rfl⟩ : syracuseStep 753311 = 1129967) B1129967
theorem B15695633 : Blo 499793 15695633 := bstep (se 2 (by rfl) ⟨5885862, by rfl⟩ : syracuseStep 15695633 = 11771725) B11771725
theorem B1802179 : Blo 499793 1802179 := bstep (se 1 (by rfl) ⟨1351634, by rfl⟩ : syracuseStep 1802179 = 2703269) B2703269
theorem B753641 : Blo 499793 753641 := bstep (se 2 (by rfl) ⟨282615, by rfl⟩ : syracuseStep 753641 = 565231) B565231
theorem B753659 : Blo 499793 753659 := bstep (se 1 (by rfl) ⟨565244, by rfl⟩ : syracuseStep 753659 = 1130489) B1130489
theorem B753833 : Blo 499793 753833 := bstep (se 2 (by rfl) ⟨282687, by rfl⟩ : syracuseStep 753833 = 565375) B565375
theorem B1802483 : Blo 499793 1802483 := bstep (se 1 (by rfl) ⟨1351862, by rfl⟩ : syracuseStep 1802483 = 2703725) B2703725
theorem B754409 : Blo 499793 754409 := bstep (se 2 (by rfl) ⟨282903, by rfl⟩ : syracuseStep 754409 = 565807) B565807
theorem B1901353 : Blo 499793 1901353 := bstep (se 2 (by rfl) ⟨713007, by rfl⟩ : syracuseStep 1901353 = 1426015) B1426015
theorem B2098217 : Blo 499793 2098217 := bstep (se 2 (by rfl) ⟨786831, by rfl⟩ : syracuseStep 2098217 = 1573663) B1573663
theorem B15598657 : Blo 499793 15598657 := bstep (se 2 (by rfl) ⟨5849496, by rfl⟩ : syracuseStep 15598657 = 11698993) B11698993
theorem B13075663 : Blo 499793 13075663 := bstep (se 1 (by rfl) ⟨9806747, by rfl⟩ : syracuseStep 13075663 = 19613495) B19613495
theorem B755111 : Blo 499793 755111 := bstep (se 1 (by rfl) ⟨566333, by rfl⟩ : syracuseStep 755111 = 1132667) B1132667
theorem B755183 : Blo 499793 755183 := bstep (se 1 (by rfl) ⟨566387, by rfl⟩ : syracuseStep 755183 = 1132775) B1132775
theorem B1902811 : Blo 499793 1902811 := bstep (se 1 (by rfl) ⟨1427108, by rfl⟩ : syracuseStep 1902811 = 2854217) B2854217
theorem B7211359 : Blo 499793 7211359 := bstep (se 1 (by rfl) ⟨5408519, by rfl⟩ : syracuseStep 7211359 = 10817039) B10817039
theorem B1805147 : Blo 499793 1805147 := bstep (se 1 (by rfl) ⟨1353860, by rfl⟩ : syracuseStep 1805147 = 2707721) B2707721
theorem B1903783 : Blo 499793 1903783 := bstep (se 1 (by rfl) ⟨1427837, by rfl⟩ : syracuseStep 1903783 = 2855675) B2855675
theorem B8162603 : Blo 499793 8162603 := bstep (se 1 (by rfl) ⟨6121952, by rfl⟩ : syracuseStep 8162603 = 12243905) B12243905
theorem B3870911 : Blo 499793 3870911 := bstep (se 1 (by rfl) ⟨2903183, by rfl⟩ : syracuseStep 3870911 = 5806367) B5806367
theorem B1446491 : Blo 499793 1446491 := bstep (se 1 (by rfl) ⟨1084868, by rfl⟩ : syracuseStep 1446491 = 2169737) B2169737
theorem B6427835 : Blo 499793 6427835 := bstep (se 1 (by rfl) ⟨4820876, by rfl⟩ : syracuseStep 6427835 = 9641753) B9641753
theorem B4232807 : Blo 499793 4232807 := bstep (se 1 (by rfl) ⟨3174605, by rfl⟩ : syracuseStep 4232807 = 6349211) B6349211
theorem B4298345 : Blo 499793 4298345 := bstep (se 2 (by rfl) ⟨1611879, by rfl⟩ : syracuseStep 4298345 = 3223759) B3223759
theorem B1808639 : Blo 499793 1808639 := bstep (se 1 (by rfl) ⟨1356479, by rfl⟩ : syracuseStep 1808639 = 2712959) B2712959
theorem B564763 : Blo 499793 564763 := bstep (se 1 (by rfl) ⟨423572, by rfl⟩ : syracuseStep 564763 = 847145) B847145
theorem B2531411 : Blo 499793 2531411 := bstep (se 1 (by rfl) ⟨1898558, by rfl⟩ : syracuseStep 2531411 = 3797117) B3797117
theorem B499839 : Blo 499793 499839 := bstep (se 1 (by rfl) ⟨374879, by rfl⟩ : syracuseStep 499839 = 749759) B749759
theorem B3612833 : Blo 499793 3612833 := bstep (se 2 (by rfl) ⟨1354812, by rfl⟩ : syracuseStep 3612833 = 2709625) B2709625
theorem B499963 : Blo 499793 499963 := bstep (se 1 (by rfl) ⟨374972, by rfl⟩ : syracuseStep 499963 = 749945) B749945
theorem B565663 : Blo 499793 565663 := bstep (se 1 (by rfl) ⟨424247, by rfl⟩ : syracuseStep 565663 = 848495) B848495
theorem B500159 : Blo 499793 500159 := bstep (se 1 (by rfl) ⟨375119, by rfl⟩ : syracuseStep 500159 = 750239) B750239
theorem B500271 : Blo 499793 500271 := bstep (se 1 (by rfl) ⟨375203, by rfl⟩ : syracuseStep 500271 = 750407) B750407
theorem B9282185 : Blo 499793 9282185 := bstep (se 2 (by rfl) ⟨3480819, by rfl⟩ : syracuseStep 9282185 = 6961639) B6961639
theorem B1811087 : Blo 499793 1811087 := bstep (se 1 (by rfl) ⟨1358315, by rfl⟩ : syracuseStep 1811087 = 2716631) B2716631
theorem B1811261 : Blo 499793 1811261 := bstep (se 3 (by rfl) ⟨339611, by rfl⟩ : syracuseStep 1811261 = 679223) B679223
theorem B500735 : Blo 499793 500735 := bstep (se 1 (by rfl) ⟨375551, by rfl⟩ : syracuseStep 500735 = 751103) B751103
theorem B500839 : Blo 499793 500839 := bstep (se 1 (by rfl) ⟨375629, by rfl⟩ : syracuseStep 500839 = 751259) B751259
theorem B1909919 : Blo 499793 1909919 := bstep (se 1 (by rfl) ⟨1432439, by rfl⟩ : syracuseStep 1909919 = 2864879) B2864879
theorem B566527 : Blo 499793 566527 := bstep (se 1 (by rfl) ⟨424895, by rfl⟩ : syracuseStep 566527 = 849791) B849791
theorem B7219151 : Blo 499793 7219151 := bstep (se 1 (by rfl) ⟨5414363, by rfl⟩ : syracuseStep 7219151 = 10828727) B10828727
theorem B501919 : Blo 499793 501919 := bstep (se 1 (by rfl) ⟨376439, by rfl⟩ : syracuseStep 501919 = 752879) B752879
theorem B502207 : Blo 499793 502207 := bstep (se 1 (by rfl) ⟨376655, by rfl⟩ : syracuseStep 502207 = 753311) B753311
theorem B10463755 : Blo 499793 10463755 := bstep (se 1 (by rfl) ⟨7847816, by rfl⟩ : syracuseStep 10463755 = 15695633) B15695633
theorem B2402905 : Blo 499793 2402905 := bstep (se 2 (by rfl) ⟨901089, by rfl⟩ : syracuseStep 2402905 = 1802179) B1802179
theorem B502427 : Blo 499793 502427 := bstep (se 1 (by rfl) ⟨376820, by rfl⟩ : syracuseStep 502427 = 753641) B753641
theorem B502439 : Blo 499793 502439 := bstep (se 1 (by rfl) ⟨376829, by rfl⟩ : syracuseStep 502439 = 753659) B753659
theorem B928609 : Blo 499793 928609 := bstep (se 2 (by rfl) ⟨348228, by rfl⟩ : syracuseStep 928609 = 696457) B696457
theorem B502875 : Blo 499793 502875 := bstep (se 1 (by rfl) ⟨377156, by rfl⟩ : syracuseStep 502875 = 754313) B754313
theorem B502943 : Blo 499793 502943 := bstep (se 1 (by rfl) ⟨377207, by rfl⟩ : syracuseStep 502943 = 754415) B754415
theorem B503035 : Blo 499793 503035 := bstep (se 1 (by rfl) ⟨377276, by rfl⟩ : syracuseStep 503035 = 754553) B754553
theorem B503231 : Blo 499793 503231 := bstep (se 1 (by rfl) ⟨377423, by rfl⟩ : syracuseStep 503231 = 754847) B754847
theorem B503343 : Blo 499793 503343 := bstep (se 1 (by rfl) ⟨377507, by rfl⟩ : syracuseStep 503343 = 755015) B755015
theorem B1126043 : Blo 499793 1126043 := bstep (se 1 (by rfl) ⟨844532, by rfl⟩ : syracuseStep 1126043 = 1689065) B1689065
theorem B3223273 : Blo 499793 3223273 := bstep (se 2 (by rfl) ⟨1208727, by rfl⟩ : syracuseStep 3223273 = 2417455) B2417455
theorem B1814663 : Blo 499793 1814663 := bstep (se 1 (by rfl) ⟨1360997, by rfl⟩ : syracuseStep 1814663 = 2721995) B2721995
theorem B635035 : Blo 499793 635035 := bstep (se 1 (by rfl) ⟨476276, by rfl⟩ : syracuseStep 635035 = 952553) B952553
theorem B1127195 : Blo 499793 1127195 := bstep (se 1 (by rfl) ⟨845396, by rfl⟩ : syracuseStep 1127195 = 1690793) B1690793
theorem B1324127 : Blo 499793 1324127 := bstep (se 1 (by rfl) ⟨993095, by rfl⟩ : syracuseStep 1324127 = 1986191) B1986191
theorem B10860641 : Blo 499793 10860641 := bstep (se 2 (by rfl) ⟨4072740, by rfl⟩ : syracuseStep 10860641 = 8145481) B8145481
theorem B12859559 : Blo 499793 12859559 := bstep (se 1 (by rfl) ⟨9644669, by rfl⟩ : syracuseStep 12859559 = 19289339) B19289339
theorem B1128671 : Blo 499793 1128671 := bstep (se 1 (by rfl) ⟨846503, by rfl⟩ : syracuseStep 1128671 = 1693007) B1693007
theorem B18266903 : Blo 499793 18266903 := bstep (se 1 (by rfl) ⟨13700177, by rfl⟩ : syracuseStep 18266903 = 27400355) B27400355
theorem B1129337 : Blo 499793 1129337 := bstep (se 2 (by rfl) ⟨423501, by rfl⟩ : syracuseStep 1129337 = 847003) B847003
theorem B1129535 : Blo 499793 1129535 := bstep (se 1 (by rfl) ⟨847151, by rfl⟩ : syracuseStep 1129535 = 1694303) B1694303
theorem B3128489 : Blo 499793 3128489 := bstep (se 2 (by rfl) ⟨1173183, by rfl⟩ : syracuseStep 3128489 = 2346367) B2346367
theorem B1359679 : Blo 499793 1359679 := bstep (se 1 (by rfl) ⟨1019759, by rfl⟩ : syracuseStep 1359679 = 2039519) B2039519
theorem B24494035 : Blo 499793 24494035 := bstep (se 1 (by rfl) ⟨18370526, by rfl⟩ : syracuseStep 24494035 = 36741053) B36741053
theorem B1130579 : Blo 499793 1130579 := bstep (se 1 (by rfl) ⟨847934, by rfl⟩ : syracuseStep 1130579 = 1695869) B1695869
theorem B966991 : Blo 499793 966991 := bstep (se 1 (by rfl) ⟨725243, by rfl⟩ : syracuseStep 966991 = 1450487) B1450487
theorem B1851815 : Blo 499793 1851815 := bstep (se 1 (by rfl) ⟨1388861, by rfl⟩ : syracuseStep 1851815 = 2777723) B2777723
theorem B1425833 : Blo 499793 1425833 := bstep (se 2 (by rfl) ⟨534687, by rfl⟩ : syracuseStep 1425833 = 1069375) B1069375
theorem B9159155 : Blo 499793 9159155 := bstep (se 1 (by rfl) ⟨6869366, by rfl⟩ : syracuseStep 9159155 = 13738733) B13738733
theorem B1361063 : Blo 499793 1361063 := bstep (se 1 (by rfl) ⟨1020797, by rfl⟩ : syracuseStep 1361063 = 2041595) B2041595
theorem B1688903 : Blo 499793 1688903 := bstep (se 1 (by rfl) ⟨1266677, by rfl⟩ : syracuseStep 1688903 = 2533355) B2533355
theorem B1361377 : Blo 499793 1361377 := bstep (se 2 (by rfl) ⟨510516, by rfl⟩ : syracuseStep 1361377 = 1021033) B1021033
theorem B1689119 : Blo 499793 1689119 := bstep (se 1 (by rfl) ⟨1266839, by rfl⟩ : syracuseStep 1689119 = 2533679) B2533679
theorem B7358161 : Blo 499793 7358161 := bstep (se 2 (by rfl) ⟨2759310, by rfl⟩ : syracuseStep 7358161 = 5518621) B5518621
theorem B1132307 : Blo 499793 1132307 := bstep (se 1 (by rfl) ⟨849230, by rfl⟩ : syracuseStep 1132307 = 1698461) B1698461
theorem B3623039 : Blo 499793 3623039 := bstep (se 1 (by rfl) ⟨2717279, by rfl⟩ : syracuseStep 3623039 = 5434559) B5434559
theorem B1689929 : Blo 499793 1689929 := bstep (se 2 (by rfl) ⟨633723, by rfl⟩ : syracuseStep 1689929 = 1267447) B1267447
theorem B1133369 : Blo 499793 1133369 := bstep (se 2 (by rfl) ⟨425013, by rfl⟩ : syracuseStep 1133369 = 850027) B850027
theorem B2149753 : Blo 499793 2149753 := bstep (se 2 (by rfl) ⟨806157, by rfl⟩ : syracuseStep 2149753 = 1612315) B1612315
theorem B1429159 : Blo 499793 1429159 := bstep (se 1 (by rfl) ⟨1071869, by rfl⟩ : syracuseStep 1429159 = 2143739) B2143739
theorem B1691711 : Blo 499793 1691711 := bstep (se 1 (by rfl) ⟨1268783, by rfl⟩ : syracuseStep 1691711 = 2537567) B2537567
theorem B2543723 : Blo 499793 2543723 := bstep (se 1 (by rfl) ⟨1907792, by rfl⟩ : syracuseStep 2543723 = 3815585) B3815585
theorem B45699689 : Blo 499793 45699689 := bstep (se 2 (by rfl) ⟨17137383, by rfl⟩ : syracuseStep 45699689 = 34274767) B34274767
theorem B6083423 : Blo 499793 6083423 := bstep (se 1 (by rfl) ⟨4562567, by rfl⟩ : syracuseStep 6083423 = 9125135) B9125135
theorem B1692953 : Blo 499793 1692953 := bstep (se 2 (by rfl) ⟨634857, by rfl⟩ : syracuseStep 1692953 = 1269715) B1269715
theorem B37213991 : Blo 499793 37213991 := bstep (se 1 (by rfl) ⟨27910493, by rfl⟩ : syracuseStep 37213991 = 55820987) B55820987
theorem B4283239 : Blo 499793 4283239 := bstep (se 1 (by rfl) ⟨3212429, by rfl⟩ : syracuseStep 4283239 = 6424859) B6424859
theorem B1269017 : Blo 499793 1269017 := bstep (se 2 (by rfl) ⟨475881, by rfl⟩ : syracuseStep 1269017 = 951763) B951763
theorem B9265589 : Blo 499793 9265589 := bstep (se 5 (by rfl) ⟨434324, by rfl⟩ : syracuseStep 9265589 = 868649) B868649
theorem B1696247 : Blo 499793 1696247 := bstep (se 1 (by rfl) ⟨1272185, by rfl⟩ : syracuseStep 1696247 = 2544371) B2544371
theorem B844681 : Blo 499793 844681 := bstep (se 2 (by rfl) ⟨316755, by rfl⟩ : syracuseStep 844681 = 633511) B633511
theorem B1696895 : Blo 499793 1696895 := bstep (se 1 (by rfl) ⟨1272671, by rfl⟩ : syracuseStep 1696895 = 2545343) B2545343
theorem B10314971 : Blo 499793 10314971 := bstep (se 1 (by rfl) ⟨7736228, by rfl⟩ : syracuseStep 10314971 = 15472457) B15472457
theorem B1697003 : Blo 499793 1697003 := bstep (se 1 (by rfl) ⟨1272752, by rfl⟩ : syracuseStep 1697003 = 2545505) B2545505
theorem B1271123 : Blo 499793 1271123 := bstep (se 1 (by rfl) ⟨953342, by rfl⟩ : syracuseStep 1271123 = 1906685) B1906685
theorem B1697975 : Blo 499793 1697975 := bstep (se 1 (by rfl) ⟨1273481, by rfl⟩ : syracuseStep 1697975 = 2546963) B2546963
theorem B846031 : Blo 499793 846031 := bstep (se 1 (by rfl) ⟨634523, by rfl⟩ : syracuseStep 846031 = 1269047) B1269047
theorem B2550203 : Blo 499793 2550203 := bstep (se 1 (by rfl) ⟨1912652, by rfl⟩ : syracuseStep 2550203 = 3825305) B3825305
theorem B846571 : Blo 499793 846571 := bstep (se 1 (by rfl) ⟨634928, by rfl⟩ : syracuseStep 846571 = 1269857) B1269857
theorem B5500169 : Blo 499793 5500169 := bstep (se 2 (by rfl) ⟨2062563, by rfl⟩ : syracuseStep 5500169 = 4125127) B4125127
theorem B13200653 : Blo 499793 13200653 := bstep (se 3 (by rfl) ⟨2475122, by rfl⟩ : syracuseStep 13200653 = 4950245) B4950245
theorem B1207835 : Blo 499793 1207835 := bstep (se 1 (by rfl) ⟨905876, by rfl⟩ : syracuseStep 1207835 = 1811753) B1811753
theorem B1699487 : Blo 499793 1699487 := bstep (se 1 (by rfl) ⟨1274615, by rfl⟩ : syracuseStep 1699487 = 2549231) B2549231
theorem B13889531 : Blo 499793 13889531 := bstep (se 1 (by rfl) ⟨10417148, by rfl⟩ : syracuseStep 13889531 = 20834297) B20834297
theorem B750287 : Blo 499793 750287 := bstep (se 1 (by rfl) ⟨562715, by rfl⟩ : syracuseStep 750287 = 1125431) B1125431
theorem B848731 : Blo 499793 848731 := bstep (se 1 (by rfl) ⟨636548, by rfl⟩ : syracuseStep 848731 = 1273097) B1273097
theorem B750761 : Blo 499793 750761 := bstep (se 2 (by rfl) ⟨281535, by rfl⟩ : syracuseStep 750761 = 563071) B563071
theorem B1897769 : Blo 499793 1897769 := bstep (se 2 (by rfl) ⟨711663, by rfl⟩ : syracuseStep 1897769 = 1423327) B1423327
theorem B1897951 : Blo 499793 1897951 := bstep (se 1 (by rfl) ⟨1423463, by rfl⟩ : syracuseStep 1897951 = 2846927) B2846927
theorem B751595 : Blo 499793 751595 := bstep (se 1 (by rfl) ⟨563696, by rfl⟩ : syracuseStep 751595 = 1127393) B1127393
theorem B2848841 : Blo 499793 2848841 := bstep (se 2 (by rfl) ⟨1068315, by rfl⟩ : syracuseStep 2848841 = 2136631) B2136631
theorem B752183 : Blo 499793 752183 := bstep (se 1 (by rfl) ⟨564137, by rfl⟩ : syracuseStep 752183 = 1128275) B1128275
theorem B752255 : Blo 499793 752255 := bstep (se 1 (by rfl) ⟨564191, by rfl⟩ : syracuseStep 752255 = 1128383) B1128383
theorem B948991 : Blo 499793 948991 := bstep (se 1 (by rfl) ⟨711743, by rfl⟩ : syracuseStep 948991 = 1423487) B1423487
theorem B3210151 : Blo 499793 3210151 := bstep (se 1 (by rfl) ⟨2407613, by rfl⟩ : syracuseStep 3210151 = 4815227) B4815227
theorem B752999 : Blo 499793 752999 := bstep (se 1 (by rfl) ⟨564749, by rfl⟩ : syracuseStep 752999 = 1129499) B1129499
theorem B4292261 : Blo 499793 4292261 := bstep (se 4 (by rfl) ⟨402399, by rfl⟩ : syracuseStep 4292261 = 804799) B804799
theorem B3801005 : Blo 499793 3801005 := bstep (se 3 (by rfl) ⟨712688, by rfl⟩ : syracuseStep 3801005 = 1425377) B1425377
theorem B753719 : Blo 499793 753719 := bstep (se 1 (by rfl) ⟨565289, by rfl⟩ : syracuseStep 753719 = 1130579) B1130579
theorem B950555 : Blo 499793 950555 := bstep (se 1 (by rfl) ⟨712916, by rfl⟩ : syracuseStep 950555 = 1425833) B1425833
theorem B754217 : Blo 499793 754217 := bstep (se 2 (by rfl) ⟨282831, by rfl⟩ : syracuseStep 754217 = 565663) B565663
theorem B754871 : Blo 499793 754871 := bstep (se 1 (by rfl) ⟨566153, by rfl⟩ : syracuseStep 754871 = 1132307) B1132307
theorem B17434217 : Blo 499793 17434217 := bstep (se 2 (by rfl) ⟨6537831, by rfl⟩ : syracuseStep 17434217 = 13075663) B13075663
theorem B755369 : Blo 499793 755369 := bstep (se 2 (by rfl) ⟨283263, by rfl⟩ : syracuseStep 755369 = 566527) B566527
theorem B755579 : Blo 499793 755579 := bstep (se 1 (by rfl) ⟨566684, by rfl⟩ : syracuseStep 755579 = 1133369) B1133369
theorem B5441735 : Blo 499793 5441735 := bstep (se 1 (by rfl) ⟨4081301, by rfl⟩ : syracuseStep 5441735 = 8162603) B8162603
theorem B2821871 : Blo 499793 2821871 := bstep (se 1 (by rfl) ⟨2116403, by rfl⟩ : syracuseStep 2821871 = 4232807) B4232807
theorem B24809327 : Blo 499793 24809327 := bstep (se 1 (by rfl) ⟨18606995, by rfl⟩ : syracuseStep 24809327 = 37213991) B37213991
theorem B1905545 : Blo 499793 1905545 := bstep (se 2 (by rfl) ⟨714579, by rfl⟩ : syracuseStep 1905545 = 1429159) B1429159
theorem B4297697 : Blo 499793 4297697 := bstep (se 2 (by rfl) ⟨1611636, by rfl⟩ : syracuseStep 4297697 = 3223273) B3223273
theorem B2530601 : Blo 499793 2530601 := bstep (se 2 (by rfl) ⟨948975, by rfl⟩ : syracuseStep 2530601 = 1897951) B1897951
theorem B500191 : Blo 499793 500191 := bstep (se 1 (by rfl) ⟨375143, by rfl⟩ : syracuseStep 500191 = 750287) B750287
theorem B500507 : Blo 499793 500507 := bstep (se 1 (by rfl) ⟨375380, by rfl⟩ : syracuseStep 500507 = 750761) B750761
theorem B5710985 : Blo 499793 5710985 := bstep (se 2 (by rfl) ⟨2141619, by rfl⟩ : syracuseStep 5710985 = 4283239) B4283239
theorem B501063 : Blo 499793 501063 := bstep (se 1 (by rfl) ⟨375797, by rfl⟩ : syracuseStep 501063 = 751595) B751595
theorem B501455 : Blo 499793 501455 := bstep (se 1 (by rfl) ⟨376091, by rfl⟩ : syracuseStep 501455 = 752183) B752183
theorem B501503 : Blo 499793 501503 := bstep (se 1 (by rfl) ⟨376127, by rfl⟩ : syracuseStep 501503 = 752255) B752255
theorem B501999 : Blo 499793 501999 := bstep (se 1 (by rfl) ⟨376499, by rfl⟩ : syracuseStep 501999 = 752999) B752999
theorem B1812905 : Blo 499793 1812905 := bstep (se 2 (by rfl) ⟨679839, by rfl⟩ : syracuseStep 1812905 = 1359679) B1359679
theorem B2861507 : Blo 499793 2861507 := bstep (se 1 (by rfl) ⟨2146130, by rfl⟩ : syracuseStep 2861507 = 4292261) B4292261
theorem B2534003 : Blo 499793 2534003 := bstep (se 1 (by rfl) ⟨1900502, by rfl⟩ : syracuseStep 2534003 = 3801005) B3801005
theorem B502555 : Blo 499793 502555 := bstep (se 1 (by rfl) ⟨376916, by rfl⟩ : syracuseStep 502555 = 753833) B753833
theorem B6106103 : Blo 499793 6106103 := bstep (se 1 (by rfl) ⟨4579577, by rfl⟩ : syracuseStep 6106103 = 9159155) B9159155
theorem B1289321 : Blo 499793 1289321 := bstep (se 2 (by rfl) ⟨483495, by rfl⟩ : syracuseStep 1289321 = 966991) B966991
theorem B502939 : Blo 499793 502939 := bstep (se 1 (by rfl) ⟨377204, by rfl⟩ : syracuseStep 502939 = 754409) B754409
theorem B1125935 : Blo 499793 1125935 := bstep (se 1 (by rfl) ⟨844451, by rfl⟩ : syracuseStep 1125935 = 1688903) B1688903
theorem B503407 : Blo 499793 503407 := bstep (se 1 (by rfl) ⟨377555, by rfl⟩ : syracuseStep 503407 = 755111) B755111
theorem B503455 : Blo 499793 503455 := bstep (se 1 (by rfl) ⟨377591, by rfl⟩ : syracuseStep 503455 = 755183) B755183
theorem B1126079 : Blo 499793 1126079 := bstep (se 1 (by rfl) ⟨844559, by rfl⟩ : syracuseStep 1126079 = 1689119) B1689119
theorem B2535137 : Blo 499793 2535137 := bstep (se 2 (by rfl) ⟨950676, by rfl⟩ : syracuseStep 2535137 = 1901353) B1901353
theorem B1126241 : Blo 499793 1126241 := bstep (se 2 (by rfl) ⟨422340, by rfl⟩ : syracuseStep 1126241 = 844681) B844681
theorem B1126619 : Blo 499793 1126619 := bstep (se 1 (by rfl) ⟨844964, by rfl⟩ : syracuseStep 1126619 = 1689929) B1689929
theorem B1815169 : Blo 499793 1815169 := bstep (se 2 (by rfl) ⟨680688, by rfl⟩ : syracuseStep 1815169 = 1361377) B1361377
theorem B9810881 : Blo 499793 9810881 := bstep (se 2 (by rfl) ⟨3679080, by rfl⟩ : syracuseStep 9810881 = 7358161) B7358161
theorem B1127807 : Blo 499793 1127807 := bstep (se 1 (by rfl) ⟨845855, by rfl⟩ : syracuseStep 1127807 = 1691711) B1691711
theorem B1128041 : Blo 499793 1128041 := bstep (se 2 (by rfl) ⟨423015, by rfl⟩ : syracuseStep 1128041 = 846031) B846031
theorem B2537081 : Blo 499793 2537081 := bstep (se 2 (by rfl) ⟨951405, by rfl⟩ : syracuseStep 2537081 = 1902811) B1902811
theorem B964327 : Blo 499793 964327 := bstep (se 1 (by rfl) ⟨723245, by rfl⟩ : syracuseStep 964327 = 1446491) B1446491
theorem B9615145 : Blo 499793 9615145 := bstep (se 2 (by rfl) ⟨3605679, by rfl⟩ : syracuseStep 9615145 = 7211359) B7211359
theorem B1128635 : Blo 499793 1128635 := bstep (se 1 (by rfl) ⟨846476, by rfl⟩ : syracuseStep 1128635 = 1692953) B1692953
theorem B1128761 : Blo 499793 1128761 := bstep (se 2 (by rfl) ⟨423285, by rfl⟩ : syracuseStep 1128761 = 846571) B846571
theorem B2865563 : Blo 499793 2865563 := bstep (se 1 (by rfl) ⟨2149172, by rfl⟩ : syracuseStep 2865563 = 4298345) B4298345
theorem B2538377 : Blo 499793 2538377 := bstep (se 2 (by rfl) ⟨951891, by rfl⟩ : syracuseStep 2538377 = 1903783) B1903783
theorem B2866337 : Blo 499793 2866337 := bstep (se 2 (by rfl) ⟨1074876, by rfl⟩ : syracuseStep 2866337 = 2149753) B2149753
theorem B1687607 : Blo 499793 1687607 := bstep (se 1 (by rfl) ⟨1265705, by rfl⟩ : syracuseStep 1687607 = 2531411) B2531411
theorem B2408555 : Blo 499793 2408555 := bstep (se 1 (by rfl) ⟨1806416, by rfl⟩ : syracuseStep 2408555 = 3612833) B3612833
theorem B6177059 : Blo 499793 6177059 := bstep (se 1 (by rfl) ⟨4632794, by rfl⟩ : syracuseStep 6177059 = 9265589) B9265589
theorem B1130831 : Blo 499793 1130831 := bstep (se 1 (by rfl) ⟨848123, by rfl⟩ : syracuseStep 1130831 = 1696247) B1696247
theorem B1131263 : Blo 499793 1131263 := bstep (se 1 (by rfl) ⟨848447, by rfl⟩ : syracuseStep 1131263 = 1696895) B1696895
theorem B1131335 : Blo 499793 1131335 := bstep (se 1 (by rfl) ⟨848501, by rfl⟩ : syracuseStep 1131335 = 1697003) B1697003
theorem B1131641 : Blo 499793 1131641 := bstep (se 2 (by rfl) ⟨424365, by rfl⟩ : syracuseStep 1131641 = 848731) B848731
theorem B1131983 : Blo 499793 1131983 := bstep (se 1 (by rfl) ⟨848987, by rfl⟩ : syracuseStep 1131983 = 1697975) B1697975
theorem B19810325 : Blo 499793 19810325 := bstep (se 6 (by rfl) ⟨464304, by rfl⟩ : syracuseStep 19810325 = 928609) B928609
theorem B8800435 : Blo 499793 8800435 := bstep (se 1 (by rfl) ⟨6600326, by rfl⟩ : syracuseStep 8800435 = 13200653) B13200653
theorem B805223 : Blo 499793 805223 := bstep (se 1 (by rfl) ⟨603917, by rfl⟩ : syracuseStep 805223 = 1207835) B1207835
theorem B1132991 : Blo 499793 1132991 := bstep (se 1 (by rfl) ⟨849743, by rfl⟩ : syracuseStep 1132991 = 1699487) B1699487
theorem B9259687 : Blo 499793 9259687 := bstep (se 1 (by rfl) ⟨6944765, by rfl⟩ : syracuseStep 9259687 = 13889531) B13889531
theorem B1265179 : Blo 499793 1265179 := bstep (se 1 (by rfl) ⟨948884, by rfl⟩ : syracuseStep 1265179 = 1897769) B1897769
theorem B1265321 : Blo 499793 1265321 := bstep (se 2 (by rfl) ⟨474495, by rfl⟩ : syracuseStep 1265321 = 948991) B948991
theorem B4280201 : Blo 499793 4280201 := bstep (se 2 (by rfl) ⟨1605075, by rfl⟩ : syracuseStep 4280201 = 3210151) B3210151
theorem B8573039 : Blo 499793 8573039 := bstep (se 1 (by rfl) ⟨6429779, by rfl⟩ : syracuseStep 8573039 = 12859559) B12859559
theorem B12177935 : Blo 499793 12177935 := bstep (se 1 (by rfl) ⟨9133451, by rfl⟩ : syracuseStep 12177935 = 18266903) B18266903
theorem B2085659 : Blo 499793 2085659 := bstep (se 1 (by rfl) ⟨1564244, by rfl⟩ : syracuseStep 2085659 = 3128489) B3128489
theorem B32658713 : Blo 499793 32658713 := bstep (se 2 (by rfl) ⟨12247017, by rfl⟩ : syracuseStep 32658713 = 24494035) B24494035
theorem B1201655 : Blo 499793 1201655 := bstep (se 1 (by rfl) ⟨901241, by rfl⟩ : syracuseStep 1201655 = 1802483) B1802483
theorem B1234543 : Blo 499793 1234543 := bstep (se 1 (by rfl) ⟨925907, by rfl⟩ : syracuseStep 1234543 = 1851815) B1851815
theorem B4839101 : Blo 499793 4839101 := bstep (se 3 (by rfl) ⟨907331, by rfl⟩ : syracuseStep 4839101 = 1814663) B1814663
theorem B1398811 : Blo 499793 1398811 := bstep (se 1 (by rfl) ⟨1049108, by rfl⟩ : syracuseStep 1398811 = 2098217) B2098217
theorem B907375 : Blo 499793 907375 := bstep (se 1 (by rfl) ⟨680531, by rfl⟩ : syracuseStep 907375 = 1361063) B1361063
theorem B2415359 : Blo 499793 2415359 := bstep (se 1 (by rfl) ⟨1811519, by rfl⟩ : syracuseStep 2415359 = 3623039) B3623039
theorem B20798209 : Blo 499793 20798209 := bstep (se 2 (by rfl) ⟨7799328, by rfl⟩ : syracuseStep 20798209 = 15598657) B15598657
theorem B1203431 : Blo 499793 1203431 := bstep (se 1 (by rfl) ⟨902573, by rfl⟩ : syracuseStep 1203431 = 1805147) B1805147
theorem B1695815 : Blo 499793 1695815 := bstep (se 1 (by rfl) ⟨1271861, by rfl⟩ : syracuseStep 1695815 = 2543723) B2543723
theorem B2580607 : Blo 499793 2580607 := bstep (se 1 (by rfl) ⟨1935455, by rfl⟩ : syracuseStep 2580607 = 3870911) B3870911
theorem B3531005 : Blo 499793 3531005 := bstep (se 3 (by rfl) ⟨662063, by rfl⟩ : syracuseStep 3531005 = 1324127) B1324127
theorem B30466459 : Blo 499793 30466459 := bstep (se 1 (by rfl) ⟨22849844, by rfl⟩ : syracuseStep 30466459 = 45699689) B45699689
theorem B4055615 : Blo 499793 4055615 := bstep (se 1 (by rfl) ⟨3041711, by rfl⟩ : syracuseStep 4055615 = 6083423) B6083423
theorem B13951673 : Blo 499793 13951673 := bstep (se 2 (by rfl) ⟨5231877, by rfl⟩ : syracuseStep 13951673 = 10463755) B10463755
theorem B3203873 : Blo 499793 3203873 := bstep (se 2 (by rfl) ⟨1201452, by rfl⟩ : syracuseStep 3203873 = 2402905) B2402905
theorem B4285223 : Blo 499793 4285223 := bstep (se 1 (by rfl) ⟨3213917, by rfl⟩ : syracuseStep 4285223 = 6427835) B6427835
theorem B1205759 : Blo 499793 1205759 := bstep (se 1 (by rfl) ⟨904319, by rfl⟩ : syracuseStep 1205759 = 1808639) B1808639
theorem B846011 : Blo 499793 846011 := bstep (se 1 (by rfl) ⟨634508, by rfl⟩ : syracuseStep 846011 = 1269017) B1269017
theorem B846713 : Blo 499793 846713 := bstep (se 2 (by rfl) ⟨317517, by rfl⟩ : syracuseStep 846713 = 635035) B635035
theorem B6188123 : Blo 499793 6188123 := bstep (se 1 (by rfl) ⟨4641092, by rfl⟩ : syracuseStep 6188123 = 9282185) B9282185
theorem B1207391 : Blo 499793 1207391 := bstep (se 1 (by rfl) ⟨905543, by rfl⟩ : syracuseStep 1207391 = 1811087) B1811087
theorem B1207507 : Blo 499793 1207507 := bstep (se 1 (by rfl) ⟨905630, by rfl⟩ : syracuseStep 1207507 = 1811261) B1811261
theorem B1273279 : Blo 499793 1273279 := bstep (se 1 (by rfl) ⟨954959, by rfl⟩ : syracuseStep 1273279 = 1909919) B1909919
theorem B6876647 : Blo 499793 6876647 := bstep (se 1 (by rfl) ⟨5157485, by rfl⟩ : syracuseStep 6876647 = 10314971) B10314971
theorem B847415 : Blo 499793 847415 := bstep (se 1 (by rfl) ⟨635561, by rfl⟩ : syracuseStep 847415 = 1271123) B1271123
theorem B4812767 : Blo 499793 4812767 := bstep (se 1 (by rfl) ⟨3609575, by rfl⟩ : syracuseStep 4812767 = 7219151) B7219151
theorem B1700135 : Blo 499793 1700135 := bstep (se 1 (by rfl) ⟨1275101, by rfl⟩ : syracuseStep 1700135 = 2550203) B2550203
theorem B3666779 : Blo 499793 3666779 := bstep (se 1 (by rfl) ⟨2750084, by rfl⟩ : syracuseStep 3666779 = 5500169) B5500169
theorem B750695 : Blo 499793 750695 := bstep (se 1 (by rfl) ⟨563021, by rfl⟩ : syracuseStep 750695 = 1126043) B1126043
theorem B751463 : Blo 499793 751463 := bstep (se 1 (by rfl) ⟨563597, by rfl⟩ : syracuseStep 751463 = 1127195) B1127195
theorem B1899227 : Blo 499793 1899227 := bstep (se 1 (by rfl) ⟨1424420, by rfl⟩ : syracuseStep 1899227 = 2848841) B2848841
theorem B7240427 : Blo 499793 7240427 := bstep (se 1 (by rfl) ⟨5430320, by rfl⟩ : syracuseStep 7240427 = 10860641) B10860641
theorem B752447 : Blo 499793 752447 := bstep (se 1 (by rfl) ⟨564335, by rfl⟩ : syracuseStep 752447 = 1128671) B1128671
theorem B752891 : Blo 499793 752891 := bstep (se 1 (by rfl) ⟨564668, by rfl⟩ : syracuseStep 752891 = 1129337) B1129337
theorem B753017 : Blo 499793 753017 := bstep (se 2 (by rfl) ⟨282381, by rfl⟩ : syracuseStep 753017 = 564763) B564763
theorem B753023 : Blo 499793 753023 := bstep (se 1 (by rfl) ⟨564767, by rfl⟩ : syracuseStep 753023 = 1129535) B1129535
theorem B1605703 : Blo 499793 1605703 := bstep (se 1 (by rfl) ⟨1204277, by rfl⟩ : syracuseStep 1605703 = 2408555) B2408555
theorem B3440809 : Blo 499793 3440809 := bstep (se 2 (by rfl) ⟨1290303, by rfl⟩ : syracuseStep 3440809 = 2580607) B2580607
theorem B753887 : Blo 499793 753887 := bstep (se 1 (by rfl) ⟨565415, by rfl⟩ : syracuseStep 753887 = 1130831) B1130831
theorem B754175 : Blo 499793 754175 := bstep (se 1 (by rfl) ⟨565631, by rfl⟩ : syracuseStep 754175 = 1131263) B1131263
theorem B754223 : Blo 499793 754223 := bstep (se 1 (by rfl) ⟨565667, by rfl⟩ : syracuseStep 754223 = 1131335) B1131335
theorem B754427 : Blo 499793 754427 := bstep (se 1 (by rfl) ⟨565820, by rfl⟩ : syracuseStep 754427 = 1131641) B1131641
theorem B754655 : Blo 499793 754655 := bstep (se 1 (by rfl) ⟨565991, by rfl⟩ : syracuseStep 754655 = 1131983) B1131983
theorem B13206883 : Blo 499793 13206883 := bstep (se 1 (by rfl) ⟨9905162, by rfl⟩ : syracuseStep 13206883 = 19810325) B19810325
theorem B755327 : Blo 499793 755327 := bstep (se 1 (by rfl) ⟨566495, by rfl⟩ : syracuseStep 755327 = 1132991) B1132991
theorem B2853467 : Blo 499793 2853467 := bstep (se 1 (by rfl) ⟨2140100, by rfl⟩ : syracuseStep 2853467 = 4280201) B4280201
theorem B11733913 : Blo 499793 11733913 := bstep (se 2 (by rfl) ⟨4400217, by rfl⟩ : syracuseStep 11733913 = 8800435) B8800435
theorem B49384997 : Blo 499793 49384997 := bstep (se 4 (by rfl) ⟨4629843, by rfl⟩ : syracuseStep 49384997 = 9259687) B9259687
theorem B1610009 : Blo 499793 1610009 := bstep (se 2 (by rfl) ⟨603753, by rfl⟩ : syracuseStep 1610009 = 1207507) B1207507
theorem B2135915 : Blo 499793 2135915 := bstep (se 1 (by rfl) ⟨1601936, by rfl⟩ : syracuseStep 2135915 = 3203873) B3203873
theorem B2856815 : Blo 499793 2856815 := bstep (se 1 (by rfl) ⟨2142611, by rfl⟩ : syracuseStep 2856815 = 4285223) B4285223
theorem B3807323 : Blo 499793 3807323 := bstep (se 1 (by rfl) ⟨2855492, by rfl⟩ : syracuseStep 3807323 = 5710985) B5710985
theorem B564007 : Blo 499793 564007 := bstep (se 1 (by rfl) ⟨423005, by rfl⟩ : syracuseStep 564007 = 846011) B846011
theorem B1907671 : Blo 499793 1907671 := bstep (se 1 (by rfl) ⟨1430753, by rfl⟩ : syracuseStep 1907671 = 2861507) B2861507
theorem B564475 : Blo 499793 564475 := bstep (se 1 (by rfl) ⟨423356, by rfl⟩ : syracuseStep 564475 = 846713) B846713
theorem B4070735 : Blo 499793 4070735 := bstep (se 1 (by rfl) ⟨3053051, by rfl⟩ : syracuseStep 4070735 = 6106103) B6106103
theorem B859547 : Blo 499793 859547 := bstep (se 1 (by rfl) ⟨644660, by rfl⟩ : syracuseStep 859547 = 1289321) B1289321
theorem B1646057 : Blo 499793 1646057 := bstep (se 2 (by rfl) ⟨617271, by rfl⟩ : syracuseStep 1646057 = 1234543) B1234543
theorem B1285769 : Blo 499793 1285769 := bstep (se 2 (by rfl) ⟨482163, by rfl⟩ : syracuseStep 1285769 = 964327) B964327
theorem B564943 : Blo 499793 564943 := bstep (se 1 (by rfl) ⟨423707, by rfl⟩ : syracuseStep 564943 = 847415) B847415
theorem B12820193 : Blo 499793 12820193 := bstep (se 2 (by rfl) ⟨4807572, by rfl⟩ : syracuseStep 12820193 = 9615145) B9615145
theorem B3219709 : Blo 499793 3219709 := bstep (se 3 (by rfl) ⟨603695, by rfl⟩ : syracuseStep 3219709 = 1207391) B1207391
theorem B500463 : Blo 499793 500463 := bstep (se 1 (by rfl) ⟨375347, by rfl⟩ : syracuseStep 500463 = 750695) B750695
theorem B27730945 : Blo 499793 27730945 := bstep (se 2 (by rfl) ⟨10399104, by rfl⟩ : syracuseStep 27730945 = 20798209) B20798209
theorem B500975 : Blo 499793 500975 := bstep (se 1 (by rfl) ⟨375731, by rfl⟩ : syracuseStep 500975 = 751463) B751463
theorem B1910375 : Blo 499793 1910375 := bstep (se 1 (by rfl) ⟨1432781, by rfl⟩ : syracuseStep 1910375 = 2865563) B2865563
theorem B4826951 : Blo 499793 4826951 := bstep (se 1 (by rfl) ⟨3620213, by rfl⟩ : syracuseStep 4826951 = 7240427) B7240427
theorem B501631 : Blo 499793 501631 := bstep (se 1 (by rfl) ⟨376223, by rfl⟩ : syracuseStep 501631 = 752447) B752447
theorem B1910891 : Blo 499793 1910891 := bstep (se 1 (by rfl) ⟨1433168, by rfl⟩ : syracuseStep 1910891 = 2866337) B2866337
theorem B501927 : Blo 499793 501927 := bstep (se 1 (by rfl) ⟨376445, by rfl⟩ : syracuseStep 501927 = 752891) B752891
theorem B502011 : Blo 499793 502011 := bstep (se 1 (by rfl) ⟨376508, by rfl⟩ : syracuseStep 502011 = 753017) B753017
theorem B502015 : Blo 499793 502015 := bstep (se 1 (by rfl) ⟨376511, by rfl⟩ : syracuseStep 502015 = 753023) B753023
theorem B1125071 : Blo 499793 1125071 := bstep (se 1 (by rfl) ⟨843803, by rfl⟩ : syracuseStep 1125071 = 1687607) B1687607
theorem B502479 : Blo 499793 502479 := bstep (se 1 (by rfl) ⟨376859, by rfl⟩ : syracuseStep 502479 = 753719) B753719
theorem B502811 : Blo 499793 502811 := bstep (se 1 (by rfl) ⟨377108, by rfl⟩ : syracuseStep 502811 = 754217) B754217
theorem B2534813 : Blo 499793 2534813 := bstep (se 3 (by rfl) ⟨475277, by rfl⟩ : syracuseStep 2534813 = 950555) B950555
theorem B503247 : Blo 499793 503247 := bstep (se 1 (by rfl) ⟨377435, by rfl⟩ : syracuseStep 503247 = 754871) B754871
theorem B503579 : Blo 499793 503579 := bstep (se 1 (by rfl) ⟨377684, by rfl⟩ : syracuseStep 503579 = 755369) B755369
theorem B503719 : Blo 499793 503719 := bstep (se 1 (by rfl) ⟨377789, by rfl⟩ : syracuseStep 503719 = 755579) B755579
theorem B536815 : Blo 499793 536815 := bstep (se 1 (by rfl) ⟨402611, by rfl⟩ : syracuseStep 536815 = 805223) B805223
theorem B5715359 : Blo 499793 5715359 := bstep (se 1 (by rfl) ⟨4286519, by rfl⟩ : syracuseStep 5715359 = 8573039) B8573039
theorem B1390439 : Blo 499793 1390439 := bstep (se 1 (by rfl) ⟨1042829, by rfl⟩ : syracuseStep 1390439 = 2085659) B2085659
theorem B2865131 : Blo 499793 2865131 := bstep (se 1 (by rfl) ⟨2148848, by rfl⟩ : syracuseStep 2865131 = 4297697) B4297697
theorem B21772475 : Blo 499793 21772475 := bstep (se 1 (by rfl) ⟨16329356, by rfl⟩ : syracuseStep 21772475 = 32658713) B32658713
theorem B801103 : Blo 499793 801103 := bstep (se 1 (by rfl) ⟨600827, by rfl⟩ : syracuseStep 801103 = 1201655) B1201655
theorem B3226067 : Blo 499793 3226067 := bstep (se 1 (by rfl) ⟨2419550, by rfl⟩ : syracuseStep 3226067 = 4839101) B4839101
theorem B1686905 : Blo 499793 1686905 := bstep (se 2 (by rfl) ⟨632589, by rfl⟩ : syracuseStep 1686905 = 1265179) B1265179
theorem B1687067 : Blo 499793 1687067 := bstep (se 1 (by rfl) ⟨1265300, by rfl⟩ : syracuseStep 1687067 = 2530601) B2530601
theorem B1130543 : Blo 499793 1130543 := bstep (se 1 (by rfl) ⟨847907, by rfl⟩ : syracuseStep 1130543 = 1695815) B1695815
theorem B2703743 : Blo 499793 2703743 := bstep (se 1 (by rfl) ⟨2027807, by rfl⟩ : syracuseStep 2703743 = 4055615) B4055615
theorem B803839 : Blo 499793 803839 := bstep (se 1 (by rfl) ⟨602879, by rfl⟩ : syracuseStep 803839 = 1205759) B1205759
theorem B1689335 : Blo 499793 1689335 := bstep (se 1 (by rfl) ⟨1267001, by rfl⟩ : syracuseStep 1689335 = 2534003) B2534003
theorem B6440957 : Blo 499793 6440957 := bstep (se 3 (by rfl) ⟨1207679, by rfl⟩ : syracuseStep 6440957 = 2415359) B2415359
theorem B1690091 : Blo 499793 1690091 := bstep (se 1 (by rfl) ⟨1267568, by rfl⟩ : syracuseStep 1690091 = 2535137) B2535137
theorem B1133423 : Blo 499793 1133423 := bstep (se 1 (by rfl) ⟨850067, by rfl⟩ : syracuseStep 1133423 = 1700135) B1700135
theorem B2444519 : Blo 499793 2444519 := bstep (se 1 (by rfl) ⟨1833389, by rfl⟩ : syracuseStep 2444519 = 3666779) B3666779
theorem B6540587 : Blo 499793 6540587 := bstep (se 1 (by rfl) ⟨4905440, by rfl⟩ : syracuseStep 6540587 = 9810881) B9810881
theorem B1691387 : Blo 499793 1691387 := bstep (se 1 (by rfl) ⟨1268540, by rfl⟩ : syracuseStep 1691387 = 2537081) B2537081
theorem B1266151 : Blo 499793 1266151 := bstep (se 1 (by rfl) ⟨949613, by rfl⟩ : syracuseStep 1266151 = 1899227) B1899227
theorem B1692251 : Blo 499793 1692251 := bstep (se 1 (by rfl) ⟨1269188, by rfl⟩ : syracuseStep 1692251 = 2538377) B2538377
theorem B7524989 : Blo 499793 7524989 := bstep (se 3 (by rfl) ⟨1410935, by rfl⟩ : syracuseStep 7524989 = 2821871) B2821871
theorem B4118039 : Blo 499793 4118039 := bstep (se 1 (by rfl) ⟨3088529, by rfl⟩ : syracuseStep 4118039 = 6177059) B6177059
theorem B3627823 : Blo 499793 3627823 := bstep (se 1 (by rfl) ⟨2720867, by rfl⟩ : syracuseStep 3627823 = 5441735) B5441735
theorem B162487781 : Blo 499793 162487781 := bstep (se 4 (by rfl) ⟨15233229, by rfl⟩ : syracuseStep 162487781 = 30466459) B30466459
theorem B843547 : Blo 499793 843547 := bstep (se 1 (by rfl) ⟨632660, by rfl⟩ : syracuseStep 843547 = 1265321) B1265321
theorem B16539551 : Blo 499793 16539551 := bstep (se 1 (by rfl) ⟨12404663, by rfl⟩ : syracuseStep 16539551 = 24809327) B24809327
theorem B8118623 : Blo 499793 8118623 := bstep (se 1 (by rfl) ⟨6088967, by rfl⟩ : syracuseStep 8118623 = 12177935) B12177935
theorem B1270363 : Blo 499793 1270363 := bstep (se 1 (by rfl) ⟨952772, by rfl⟩ : syracuseStep 1270363 = 1905545) B1905545
theorem B46491245 : Blo 499793 46491245 := bstep (se 3 (by rfl) ⟨8717108, by rfl⟩ : syracuseStep 46491245 = 17434217) B17434217
theorem B1697705 : Blo 499793 1697705 := bstep (se 2 (by rfl) ⟨636639, by rfl⟩ : syracuseStep 1697705 = 1273279) B1273279
theorem B2354003 : Blo 499793 2354003 := bstep (se 1 (by rfl) ⟨1765502, by rfl⟩ : syracuseStep 2354003 = 3531005) B3531005
theorem B9301115 : Blo 499793 9301115 := bstep (se 1 (by rfl) ⟨6975836, by rfl⟩ : syracuseStep 9301115 = 13951673) B13951673
theorem B2420225 : Blo 499793 2420225 := bstep (se 2 (by rfl) ⟨907584, by rfl⟩ : syracuseStep 2420225 = 1815169) B1815169
theorem B1208603 : Blo 499793 1208603 := bstep (se 1 (by rfl) ⟨906452, by rfl⟩ : syracuseStep 1208603 = 1812905) B1812905
theorem B4125415 : Blo 499793 4125415 := bstep (se 1 (by rfl) ⟨3094061, by rfl⟩ : syracuseStep 4125415 = 6188123) B6188123
theorem B4584431 : Blo 499793 4584431 := bstep (se 1 (by rfl) ⟨3438323, by rfl⟩ : syracuseStep 4584431 = 6876647) B6876647
theorem B750623 : Blo 499793 750623 := bstep (se 1 (by rfl) ⟨562967, by rfl⟩ : syracuseStep 750623 = 1125935) B1125935
theorem B750719 : Blo 499793 750719 := bstep (se 1 (by rfl) ⟨563039, by rfl⟩ : syracuseStep 750719 = 1126079) B1126079
theorem B750827 : Blo 499793 750827 := bstep (se 1 (by rfl) ⟨563120, by rfl⟩ : syracuseStep 750827 = 1126241) B1126241
theorem B3208511 : Blo 499793 3208511 := bstep (se 1 (by rfl) ⟨2406383, by rfl⟩ : syracuseStep 3208511 = 4812767) B4812767
theorem B1865081 : Blo 499793 1865081 := bstep (se 2 (by rfl) ⟨699405, by rfl⟩ : syracuseStep 1865081 = 1398811) B1398811
theorem B751079 : Blo 499793 751079 := bstep (se 1 (by rfl) ⟨563309, by rfl⟩ : syracuseStep 751079 = 1126619) B1126619
theorem B1209833 : Blo 499793 1209833 := bstep (se 2 (by rfl) ⟨453687, by rfl⟩ : syracuseStep 1209833 = 907375) B907375
theorem B3209149 : Blo 499793 3209149 := bstep (se 3 (by rfl) ⟨601715, by rfl⟩ : syracuseStep 3209149 = 1203431) B1203431
theorem B751871 : Blo 499793 751871 := bstep (se 1 (by rfl) ⟨563903, by rfl⟩ : syracuseStep 751871 = 1127807) B1127807
theorem B752027 : Blo 499793 752027 := bstep (se 1 (by rfl) ⟨564020, by rfl⟩ : syracuseStep 752027 = 1128041) B1128041
theorem B752423 : Blo 499793 752423 := bstep (se 1 (by rfl) ⟨564317, by rfl⟩ : syracuseStep 752423 = 1128635) B1128635
theorem B752507 : Blo 499793 752507 := bstep (se 1 (by rfl) ⟨564380, by rfl⟩ : syracuseStep 752507 = 1128761) B1128761
theorem B753695 : Blo 499793 753695 := bstep (se 1 (by rfl) ⟨565271, by rfl⟩ : syracuseStep 753695 = 1130543) B1130543
theorem B1802495 : Blo 499793 1802495 := bstep (se 1 (by rfl) ⟨1351871, by rfl⟩ : syracuseStep 1802495 = 2703743) B2703743
theorem B4292945 : Blo 499793 4292945 := bstep (se 2 (by rfl) ⟨1609854, by rfl⟩ : syracuseStep 4292945 = 3219709) B3219709
theorem B18350981 : Blo 499793 18350981 := bstep (se 4 (by rfl) ⟨1720404, by rfl⟩ : syracuseStep 18350981 = 3440809) B3440809
theorem B4293971 : Blo 499793 4293971 := bstep (se 1 (by rfl) ⟨3220478, by rfl⟩ : syracuseStep 4293971 = 6440957) B6440957
theorem B1902311 : Blo 499793 1902311 := bstep (se 1 (by rfl) ⟨1426733, by rfl⟩ : syracuseStep 1902311 = 2853467) B2853467
theorem B755615 : Blo 499793 755615 := bstep (se 1 (by rfl) ⟨566711, by rfl⟩ : syracuseStep 755615 = 1133423) B1133423
theorem B4360391 : Blo 499793 4360391 := bstep (se 1 (by rfl) ⟨3270293, by rfl⟩ : syracuseStep 4360391 = 6540587) B6540587
theorem B5016659 : Blo 499793 5016659 := bstep (se 1 (by rfl) ⟨3762494, by rfl⟩ : syracuseStep 5016659 = 7524989) B7524989
theorem B1904543 : Blo 499793 1904543 := bstep (se 1 (by rfl) ⟨1428407, by rfl⟩ : syracuseStep 1904543 = 2856815) B2856815
theorem B857179 : Blo 499793 857179 := bstep (se 1 (by rfl) ⟨642884, by rfl⟩ : syracuseStep 857179 = 1285769) B1285769
theorem B5412415 : Blo 499793 5412415 := bstep (se 1 (by rfl) ⟨4059311, by rfl⟩ : syracuseStep 5412415 = 8118623) B8118623
theorem B3217967 : Blo 499793 3217967 := bstep (se 1 (by rfl) ⟨2413475, by rfl⟩ : syracuseStep 3217967 = 4826951) B4826951
theorem B1613483 : Blo 499793 1613483 := bstep (se 1 (by rfl) ⟨1210112, by rfl⟩ : syracuseStep 1613483 = 2420225) B2420225
theorem B3056287 : Blo 499793 3056287 := bstep (se 1 (by rfl) ⟨2292215, by rfl⟩ : syracuseStep 3056287 = 4584431) B4584431
theorem B500415 : Blo 499793 500415 := bstep (se 1 (by rfl) ⟨375311, by rfl⟩ : syracuseStep 500415 = 750623) B750623
theorem B500479 : Blo 499793 500479 := bstep (se 1 (by rfl) ⟨375359, by rfl⟩ : syracuseStep 500479 = 750719) B750719
theorem B500551 : Blo 499793 500551 := bstep (se 1 (by rfl) ⟨375413, by rfl⟩ : syracuseStep 500551 = 750827) B750827
theorem B25109365 : Blo 499793 25109365 := bstep (se 5 (by rfl) ⟨1177001, by rfl⟩ : syracuseStep 25109365 = 2354003) B2354003
theorem B2139007 : Blo 499793 2139007 := bstep (se 1 (by rfl) ⟨1604255, by rfl⟩ : syracuseStep 2139007 = 3208511) B3208511
theorem B3810239 : Blo 499793 3810239 := bstep (se 1 (by rfl) ⟨2857679, by rfl⟩ : syracuseStep 3810239 = 5715359) B5715359
theorem B500719 : Blo 499793 500719 := bstep (se 1 (by rfl) ⟨375539, by rfl⟩ : syracuseStep 500719 = 751079) B751079
theorem B926959 : Blo 499793 926959 := bstep (se 1 (by rfl) ⟨695219, by rfl⟩ : syracuseStep 926959 = 1390439) B1390439
theorem B1910087 : Blo 499793 1910087 := bstep (se 1 (by rfl) ⟨1432565, by rfl⟩ : syracuseStep 1910087 = 2865131) B2865131
theorem B501247 : Blo 499793 501247 := bstep (se 1 (by rfl) ⟨375935, by rfl⟩ : syracuseStep 501247 = 751871) B751871
theorem B501351 : Blo 499793 501351 := bstep (se 1 (by rfl) ⟨376013, by rfl⟩ : syracuseStep 501351 = 752027) B752027
theorem B501615 : Blo 499793 501615 := bstep (se 1 (by rfl) ⟨376211, by rfl⟩ : syracuseStep 501615 = 752423) B752423
theorem B501671 : Blo 499793 501671 := bstep (se 1 (by rfl) ⟨376253, by rfl⟩ : syracuseStep 501671 = 752507) B752507
theorem B1124603 : Blo 499793 1124603 := bstep (se 1 (by rfl) ⟨843452, by rfl⟩ : syracuseStep 1124603 = 1686905) B1686905
theorem B1124711 : Blo 499793 1124711 := bstep (se 1 (by rfl) ⟨843533, by rfl⟩ : syracuseStep 1124711 = 1687067) B1687067
theorem B1124729 : Blo 499793 1124729 := bstep (se 2 (by rfl) ⟨421773, by rfl⟩ : syracuseStep 1124729 = 843547) B843547
theorem B2140937 : Blo 499793 2140937 := bstep (se 2 (by rfl) ⟨802851, by rfl⟩ : syracuseStep 2140937 = 1605703) B1605703
theorem B502591 : Blo 499793 502591 := bstep (se 1 (by rfl) ⟨376943, by rfl⟩ : syracuseStep 502591 = 753887) B753887
theorem B502783 : Blo 499793 502783 := bstep (se 1 (by rfl) ⟨377087, by rfl⟩ : syracuseStep 502783 = 754175) B754175
theorem B502815 : Blo 499793 502815 := bstep (se 1 (by rfl) ⟨377111, by rfl⟩ : syracuseStep 502815 = 754223) B754223
theorem B502951 : Blo 499793 502951 := bstep (se 1 (by rfl) ⟨377213, by rfl⟩ : syracuseStep 502951 = 754427) B754427
theorem B503103 : Blo 499793 503103 := bstep (se 1 (by rfl) ⟨377327, by rfl⟩ : syracuseStep 503103 = 754655) B754655
theorem B503551 : Blo 499793 503551 := bstep (se 1 (by rfl) ⟨377663, by rfl⟩ : syracuseStep 503551 = 755327) B755327
theorem B1126223 : Blo 499793 1126223 := bstep (se 1 (by rfl) ⟨844667, by rfl⟩ : syracuseStep 1126223 = 1689335) B1689335
theorem B36974593 : Blo 499793 36974593 := bstep (se 2 (by rfl) ⟨13865472, by rfl⟩ : syracuseStep 36974593 = 27730945) B27730945
theorem B1126727 : Blo 499793 1126727 := bstep (se 1 (by rfl) ⟨845045, by rfl⟩ : syracuseStep 1126727 = 1690091) B1690091
theorem B17609177 : Blo 499793 17609177 := bstep (se 2 (by rfl) ⟨6603441, by rfl⟩ : syracuseStep 17609177 = 13206883) B13206883
theorem B1127591 : Blo 499793 1127591 := bstep (se 1 (by rfl) ⟨845693, by rfl⟩ : syracuseStep 1127591 = 1691387) B1691387
theorem B1128167 : Blo 499793 1128167 := bstep (se 1 (by rfl) ⟨846125, by rfl⟩ : syracuseStep 1128167 = 1692251) B1692251
theorem B1423943 : Blo 499793 1423943 := bstep (se 1 (by rfl) ⟨1067957, by rfl⟩ : syracuseStep 1423943 = 2135915) B2135915
theorem B2538215 : Blo 499793 2538215 := bstep (se 1 (by rfl) ⟨1903661, by rfl⟩ : syracuseStep 2538215 = 3807323) B3807323
theorem B573031 : Blo 499793 573031 := bstep (se 1 (by rfl) ⟨429773, by rfl⟩ : syracuseStep 573031 = 859547) B859547
theorem B1097371 : Blo 499793 1097371 := bstep (se 1 (by rfl) ⟨823028, by rfl⟩ : syracuseStep 1097371 = 1646057) B1646057
theorem B11026367 : Blo 499793 11026367 := bstep (se 1 (by rfl) ⟨8269775, by rfl⟩ : syracuseStep 11026367 = 16539551) B16539551
theorem B1688201 : Blo 499793 1688201 := bstep (se 2 (by rfl) ⟨633075, by rfl⟩ : syracuseStep 1688201 = 1266151) B1266151
theorem B1131803 : Blo 499793 1131803 := bstep (se 1 (by rfl) ⟨848852, by rfl⟩ : syracuseStep 1131803 = 1697705) B1697705
theorem B1689875 : Blo 499793 1689875 := bstep (se 1 (by rfl) ⟨1267406, by rfl⟩ : syracuseStep 1689875 = 2534813) B2534813
theorem B4278865 : Blo 499793 4278865 := bstep (se 2 (by rfl) ⟨1604574, by rfl⟩ : syracuseStep 4278865 = 3209149) B3209149
theorem B805735 : Blo 499793 805735 := bstep (se 1 (by rfl) ⟨604301, by rfl⟩ : syracuseStep 805735 = 1208603) B1208603
theorem B1068137 : Blo 499793 1068137 := bstep (se 2 (by rfl) ⟨400551, by rfl⟩ : syracuseStep 1068137 = 801103) B801103
theorem B806555 : Blo 499793 806555 := bstep (se 1 (by rfl) ⟨604916, by rfl⟩ : syracuseStep 806555 = 1209833) B1209833
theorem B4837097 : Blo 499793 4837097 := bstep (se 2 (by rfl) ⟨1813911, by rfl⟩ : syracuseStep 4837097 = 3627823) B3627823
theorem B2543561 : Blo 499793 2543561 := bstep (se 2 (by rfl) ⟨953835, by rfl⟩ : syracuseStep 2543561 = 1907671) B1907671
theorem B2150711 : Blo 499793 2150711 := bstep (se 1 (by rfl) ⟨1613033, by rfl⟩ : syracuseStep 2150711 = 3226067) B3226067
theorem B1693817 : Blo 499793 1693817 := bstep (se 2 (by rfl) ⟨635181, by rfl⟩ : syracuseStep 1693817 = 1270363) B1270363
theorem B1071785 : Blo 499793 1071785 := bstep (se 2 (by rfl) ⟨401919, by rfl⟩ : syracuseStep 1071785 = 803839) B803839
theorem B32923331 : Blo 499793 32923331 := bstep (se 1 (by rfl) ⟨24692498, by rfl⟩ : syracuseStep 32923331 = 49384997) B49384997
theorem B1073339 : Blo 499793 1073339 := bstep (se 1 (by rfl) ⟨805004, by rfl⟩ : syracuseStep 1073339 = 1610009) B1610009
theorem B2745359 : Blo 499793 2745359 := bstep (se 1 (by rfl) ⟨2059019, by rfl⟩ : syracuseStep 2745359 = 4118039) B4118039
theorem B62580869 : Blo 499793 62580869 := bstep (se 4 (by rfl) ⟨5866956, by rfl⟩ : syracuseStep 62580869 = 11733913) B11733913
theorem B2713823 : Blo 499793 2713823 := bstep (se 1 (by rfl) ⟨2035367, by rfl⟩ : syracuseStep 2713823 = 4070735) B4070735
theorem B108325187 : Blo 499793 108325187 := bstep (se 1 (by rfl) ⟨81243890, by rfl⟩ : syracuseStep 108325187 = 162487781) B162487781
theorem B8546795 : Blo 499793 8546795 := bstep (se 1 (by rfl) ⟨6410096, by rfl⟩ : syracuseStep 8546795 = 12820193) B12820193
theorem B715753 : Blo 499793 715753 := bstep (se 2 (by rfl) ⟨268407, by rfl⟩ : syracuseStep 715753 = 536815) B536815
theorem B5500553 : Blo 499793 5500553 := bstep (se 2 (by rfl) ⟨2062707, by rfl⟩ : syracuseStep 5500553 = 4125415) B4125415
theorem B1273583 : Blo 499793 1273583 := bstep (se 1 (by rfl) ⟨955187, by rfl⟩ : syracuseStep 1273583 = 1910375) B1910375
theorem B30994163 : Blo 499793 30994163 := bstep (se 1 (by rfl) ⟨23245622, by rfl⟩ : syracuseStep 30994163 = 46491245) B46491245
theorem B1273927 : Blo 499793 1273927 := bstep (se 1 (by rfl) ⟨955445, by rfl⟩ : syracuseStep 1273927 = 1910891) B1910891
theorem B750047 : Blo 499793 750047 := bstep (se 1 (by rfl) ⟨562535, by rfl⟩ : syracuseStep 750047 = 1125071) B1125071
theorem B24802973 : Blo 499793 24802973 := bstep (se 3 (by rfl) ⟨4650557, by rfl⟩ : syracuseStep 24802973 = 9301115) B9301115
theorem B6518717 : Blo 499793 6518717 := bstep (se 3 (by rfl) ⟨1222259, by rfl⟩ : syracuseStep 6518717 = 2444519) B2444519
theorem B1243387 : Blo 499793 1243387 := bstep (se 1 (by rfl) ⟨932540, by rfl⟩ : syracuseStep 1243387 = 1865081) B1865081
theorem B752009 : Blo 499793 752009 := bstep (se 2 (by rfl) ⟨282003, by rfl⟩ : syracuseStep 752009 = 564007) B564007
theorem B14514983 : Blo 499793 14514983 := bstep (se 1 (by rfl) ⟨10886237, by rfl⟩ : syracuseStep 14514983 = 21772475) B21772475
theorem B752633 : Blo 499793 752633 := bstep (se 2 (by rfl) ⟨282237, by rfl⟩ : syracuseStep 752633 = 564475) B564475
theorem B753257 : Blo 499793 753257 := bstep (se 2 (by rfl) ⟨282471, by rfl⟩ : syracuseStep 753257 = 564943) B564943
theorem B754535 : Blo 499793 754535 := bstep (se 1 (by rfl) ⟨565901, by rfl⟩ : syracuseStep 754535 = 1131803) B1131803
theorem B53511029 : Blo 499793 53511029 := bstep (se 5 (by rfl) ⟨2508329, by rfl⟩ : syracuseStep 53511029 = 5016659) B5016659
theorem B2852009 : Blo 499793 2852009 := bstep (se 2 (by rfl) ⟨1069503, by rfl⟩ : syracuseStep 2852009 = 2139007) B2139007
theorem B5705153 : Blo 499793 5705153 := bstep (se 2 (by rfl) ⟨2139432, by rfl⟩ : syracuseStep 5705153 = 4278865) B4278865
theorem B954337 : Blo 499793 954337 := bstep (se 2 (by rfl) ⟨357876, by rfl⟩ : syracuseStep 954337 = 715753) B715753
theorem B41720579 : Blo 499793 41720579 := bstep (se 1 (by rfl) ⟨31290434, by rfl⟩ : syracuseStep 41720579 = 62580869) B62580869
theorem B1809215 : Blo 499793 1809215 := bstep (se 1 (by rfl) ⟨1356911, by rfl⟩ : syracuseStep 1809215 = 2713823) B2713823
theorem B7216553 : Blo 499793 7216553 := bstep (se 2 (by rfl) ⟨2706207, by rfl⟩ : syracuseStep 7216553 = 5412415) B5412415
theorem B11739451 : Blo 499793 11739451 := bstep (se 1 (by rfl) ⟨8804588, by rfl⟩ : syracuseStep 11739451 = 17609177) B17609177
theorem B500031 : Blo 499793 500031 := bstep (se 1 (by rfl) ⟨375023, by rfl⟩ : syracuseStep 500031 = 750047) B750047
theorem B501339 : Blo 499793 501339 := bstep (se 1 (by rfl) ⟨376004, by rfl⟩ : syracuseStep 501339 = 752009) B752009
theorem B9676655 : Blo 499793 9676655 := bstep (se 1 (by rfl) ⟨7257491, by rfl⟩ : syracuseStep 9676655 = 14514983) B14514983
theorem B501755 : Blo 499793 501755 := bstep (se 1 (by rfl) ⟨376316, by rfl⟩ : syracuseStep 501755 = 752633) B752633
theorem B764041 : Blo 499793 764041 := bstep (se 2 (by rfl) ⟨286515, by rfl⟩ : syracuseStep 764041 = 573031) B573031
theorem B502171 : Blo 499793 502171 := bstep (se 1 (by rfl) ⟨376628, by rfl⟩ : syracuseStep 502171 = 753257) B753257
theorem B7350911 : Blo 499793 7350911 := bstep (se 1 (by rfl) ⟨5513183, by rfl⟩ : syracuseStep 7350911 = 11026367) B11026367
theorem B502463 : Blo 499793 502463 := bstep (se 1 (by rfl) ⟨376847, by rfl⟩ : syracuseStep 502463 = 753695) B753695
theorem B2861963 : Blo 499793 2861963 := bstep (se 1 (by rfl) ⟨2146472, by rfl⟩ : syracuseStep 2861963 = 4292945) B4292945
theorem B1125467 : Blo 499793 1125467 := bstep (se 1 (by rfl) ⟨844100, by rfl⟩ : syracuseStep 1125467 = 1688201) B1688201
theorem B12233987 : Blo 499793 12233987 := bstep (se 1 (by rfl) ⟨9175490, by rfl⟩ : syracuseStep 12233987 = 18350981) B18350981
theorem B4075049 : Blo 499793 4075049 := bstep (se 2 (by rfl) ⟨1528143, by rfl⟩ : syracuseStep 4075049 = 3056287) B3056287
theorem B2862647 : Blo 499793 2862647 := bstep (se 1 (by rfl) ⟨2146985, by rfl⟩ : syracuseStep 2862647 = 4293971) B4293971
theorem B503743 : Blo 499793 503743 := bstep (se 1 (by rfl) ⟨377807, by rfl⟩ : syracuseStep 503743 = 755615) B755615
theorem B1126583 : Blo 499793 1126583 := bstep (se 1 (by rfl) ⟨844937, by rfl⟩ : syracuseStep 1126583 = 1689875) B1689875
theorem B1129211 : Blo 499793 1129211 := bstep (se 1 (by rfl) ⟨846908, by rfl⟩ : syracuseStep 1129211 = 1693817) B1693817
theorem B2145311 : Blo 499793 2145311 := bstep (se 1 (by rfl) ⟨1608983, by rfl⟩ : syracuseStep 2145311 = 3217967) B3217967
theorem B49299457 : Blo 499793 49299457 := bstep (se 2 (by rfl) ⟨18487296, by rfl⟩ : syracuseStep 49299457 = 36974593) B36974593
theorem B2540159 : Blo 499793 2540159 := bstep (se 1 (by rfl) ⟨1905119, by rfl⟩ : syracuseStep 2540159 = 3810239) B3810239
theorem B1427291 : Blo 499793 1427291 := bstep (se 1 (by rfl) ⟨1070468, by rfl⟩ : syracuseStep 1427291 = 2140937) B2140937
theorem B20662775 : Blo 499793 20662775 := bstep (se 1 (by rfl) ⟨15497081, by rfl⟩ : syracuseStep 20662775 = 30994163) B30994163
theorem B1657849 : Blo 499793 1657849 := bstep (se 2 (by rfl) ⟨621693, by rfl⟩ : syracuseStep 1657849 = 1243387) B1243387
theorem B5852645 : Blo 499793 5852645 := bstep (se 4 (by rfl) ⟨548685, by rfl⟩ : syracuseStep 5852645 = 1097371) B1097371
theorem B16535315 : Blo 499793 16535315 := bstep (se 1 (by rfl) ⟨12401486, by rfl⟩ : syracuseStep 16535315 = 24802973) B24802973
theorem B4345811 : Blo 499793 4345811 := bstep (se 1 (by rfl) ⟨3259358, by rfl⟩ : syracuseStep 4345811 = 6518717) B6518717
theorem B14668141 : Blo 499793 14668141 := bstep (se 3 (by rfl) ⟨2750276, by rfl⟩ : syracuseStep 14668141 = 5500553) B5500553
theorem B2150813 : Blo 499793 2150813 := bstep (se 3 (by rfl) ⟨403277, by rfl⟩ : syracuseStep 2150813 = 806555) B806555
theorem B1692143 : Blo 499793 1692143 := bstep (se 1 (by rfl) ⟨1269107, by rfl⟩ : syracuseStep 1692143 = 2538215) B2538215
theorem B12898925 : Blo 499793 12898925 := bstep (se 3 (by rfl) ⟨2418548, by rfl⟩ : syracuseStep 12898925 = 4837097) B4837097
theorem B1201663 : Blo 499793 1201663 := bstep (se 1 (by rfl) ⟨901247, by rfl⟩ : syracuseStep 1201663 = 1802495) B1802495
theorem B1268207 : Blo 499793 1268207 := bstep (se 1 (by rfl) ⟨951155, by rfl⟩ : syracuseStep 1268207 = 1902311) B1902311
theorem B33479153 : Blo 499793 33479153 := bstep (se 2 (by rfl) ⟨12554682, by rfl⟩ : syracuseStep 33479153 = 25109365) B25109365
theorem B2906927 : Blo 499793 2906927 := bstep (se 1 (by rfl) ⟨2180195, by rfl⟩ : syracuseStep 2906927 = 4360391) B4360391
theorem B1235945 : Blo 499793 1235945 := bstep (se 2 (by rfl) ⟨463479, by rfl⟩ : syracuseStep 1235945 = 926959) B926959
theorem B712091 : Blo 499793 712091 := bstep (se 1 (by rfl) ⟨534068, by rfl⟩ : syracuseStep 712091 = 1068137) B1068137
theorem B1269695 : Blo 499793 1269695 := bstep (se 1 (by rfl) ⟨952271, by rfl⟩ : syracuseStep 1269695 = 1904543) B1904543
theorem B1695707 : Blo 499793 1695707 := bstep (se 1 (by rfl) ⟨1271780, by rfl⟩ : syracuseStep 1695707 = 2543561) B2543561
theorem B1433807 : Blo 499793 1433807 := bstep (se 1 (by rfl) ⟨1075355, by rfl⟩ : syracuseStep 1433807 = 2150711) B2150711
theorem B1074313 : Blo 499793 1074313 := bstep (se 2 (by rfl) ⟨402867, by rfl⟩ : syracuseStep 1074313 = 805735) B805735
theorem B714523 : Blo 499793 714523 := bstep (se 1 (by rfl) ⟨535892, by rfl⟩ : syracuseStep 714523 = 1071785) B1071785
theorem B1075655 : Blo 499793 1075655 := bstep (se 1 (by rfl) ⟨806741, by rfl⟩ : syracuseStep 1075655 = 1613483) B1613483
theorem B21948887 : Blo 499793 21948887 := bstep (se 1 (by rfl) ⟨16461665, by rfl⟩ : syracuseStep 21948887 = 32923331) B32923331
theorem B1698569 : Blo 499793 1698569 := bstep (se 2 (by rfl) ⟨636963, by rfl⟩ : syracuseStep 1698569 = 1273927) B1273927
theorem B715559 : Blo 499793 715559 := bstep (se 1 (by rfl) ⟨536669, by rfl⟩ : syracuseStep 715559 = 1073339) B1073339
theorem B1830239 : Blo 499793 1830239 := bstep (se 1 (by rfl) ⟨1372679, by rfl⟩ : syracuseStep 1830239 = 2745359) B2745359
theorem B1273391 : Blo 499793 1273391 := bstep (se 1 (by rfl) ⟨955043, by rfl⟩ : syracuseStep 1273391 = 1910087) B1910087
theorem B1142905 : Blo 499793 1142905 := bstep (se 2 (by rfl) ⟨428589, by rfl⟩ : syracuseStep 1142905 = 857179) B857179
theorem B749735 : Blo 499793 749735 := bstep (se 1 (by rfl) ⟨562301, by rfl⟩ : syracuseStep 749735 = 1124603) B1124603
theorem B72216791 : Blo 499793 72216791 := bstep (se 1 (by rfl) ⟨54162593, by rfl⟩ : syracuseStep 72216791 = 108325187) B108325187
theorem B749807 : Blo 499793 749807 := bstep (se 1 (by rfl) ⟨562355, by rfl⟩ : syracuseStep 749807 = 1124711) B1124711
theorem B749819 : Blo 499793 749819 := bstep (se 1 (by rfl) ⟨562364, by rfl⟩ : syracuseStep 749819 = 1124729) B1124729
theorem B5697863 : Blo 499793 5697863 := bstep (se 1 (by rfl) ⟨4273397, by rfl⟩ : syracuseStep 5697863 = 8546795) B8546795
theorem B849055 : Blo 499793 849055 := bstep (se 1 (by rfl) ⟨636791, by rfl⟩ : syracuseStep 849055 = 1273583) B1273583
theorem B750815 : Blo 499793 750815 := bstep (se 1 (by rfl) ⟨563111, by rfl⟩ : syracuseStep 750815 = 1126223) B1126223
theorem B751151 : Blo 499793 751151 := bstep (se 1 (by rfl) ⟨563363, by rfl⟩ : syracuseStep 751151 = 1126727) B1126727
theorem B751727 : Blo 499793 751727 := bstep (se 1 (by rfl) ⟨563795, by rfl⟩ : syracuseStep 751727 = 1127591) B1127591
theorem B752111 : Blo 499793 752111 := bstep (se 1 (by rfl) ⟨564083, by rfl⟩ : syracuseStep 752111 = 1128167) B1128167
theorem B949295 : Blo 499793 949295 := bstep (se 1 (by rfl) ⟨711971, by rfl⟩ : syracuseStep 949295 = 1423943) B1423943
theorem B65732609 : Blo 499793 65732609 := bstep (se 2 (by rfl) ⟨24649728, by rfl⟩ : syracuseStep 65732609 = 49299457) B49299457
theorem B1901339 : Blo 499793 1901339 := bstep (se 1 (by rfl) ⟨1426004, by rfl⟩ : syracuseStep 1901339 = 2852009) B2852009
theorem B951527 : Blo 499793 951527 := bstep (se 1 (by rfl) ⟨713645, by rfl⟩ : syracuseStep 951527 = 1427291) B1427291
theorem B3803435 : Blo 499793 3803435 := bstep (se 1 (by rfl) ⟨2852576, by rfl⟩ : syracuseStep 3803435 = 5705153) B5705153
theorem B3901763 : Blo 499793 3901763 := bstep (se 1 (by rfl) ⟨2926322, by rfl⟩ : syracuseStep 3901763 = 5852645) B5852645
theorem B952697 : Blo 499793 952697 := bstep (se 2 (by rfl) ⟨357261, by rfl⟩ : syracuseStep 952697 = 714523) B714523
theorem B1018721 : Blo 499793 1018721 := bstep (se 2 (by rfl) ⟨382020, by rfl⟩ : syracuseStep 1018721 = 764041) B764041
theorem B22319435 : Blo 499793 22319435 := bstep (se 1 (by rfl) ⟨16739576, by rfl⟩ : syracuseStep 22319435 = 33479153) B33479153
theorem B1937951 : Blo 499793 1937951 := bstep (se 1 (by rfl) ⟨1453463, by rfl⟩ : syracuseStep 1937951 = 2906927) B2906927
theorem B823963 : Blo 499793 823963 := bstep (se 1 (by rfl) ⟨617972, by rfl⟩ : syracuseStep 823963 = 1235945) B1235945
theorem B955871 : Blo 499793 955871 := bstep (se 1 (by rfl) ⟨716903, by rfl⟩ : syracuseStep 955871 = 1433807) B1433807
theorem B1907975 : Blo 499793 1907975 := bstep (se 1 (by rfl) ⟨1430981, by rfl⟩ : syracuseStep 1907975 = 2861963) B2861963
theorem B1908157 : Blo 499793 1908157 := bstep (se 3 (by rfl) ⟨357779, by rfl⟩ : syracuseStep 1908157 = 715559) B715559
theorem B1220159 : Blo 499793 1220159 := bstep (se 1 (by rfl) ⟨915119, by rfl⟩ : syracuseStep 1220159 = 1830239) B1830239
theorem B1908431 : Blo 499793 1908431 := bstep (se 1 (by rfl) ⟨1431323, by rfl⟩ : syracuseStep 1908431 = 2862647) B2862647
theorem B499823 : Blo 499793 499823 := bstep (se 1 (by rfl) ⟨374867, by rfl⟩ : syracuseStep 499823 = 749735) B749735
theorem B48144527 : Blo 499793 48144527 := bstep (se 1 (by rfl) ⟨36108395, by rfl⟩ : syracuseStep 48144527 = 72216791) B72216791
theorem B499871 : Blo 499793 499871 := bstep (se 1 (by rfl) ⟨374903, by rfl⟩ : syracuseStep 499871 = 749807) B749807
theorem B499879 : Blo 499793 499879 := bstep (se 1 (by rfl) ⟨374909, by rfl⟩ : syracuseStep 499879 = 749819) B749819
theorem B500543 : Blo 499793 500543 := bstep (se 1 (by rfl) ⟨375407, by rfl⟩ : syracuseStep 500543 = 750815) B750815
theorem B500767 : Blo 499793 500767 := bstep (se 1 (by rfl) ⟨375575, by rfl⟩ : syracuseStep 500767 = 751151) B751151
theorem B501151 : Blo 499793 501151 := bstep (se 1 (by rfl) ⟨375863, by rfl⟩ : syracuseStep 501151 = 751727) B751727
theorem B501407 : Blo 499793 501407 := bstep (se 1 (by rfl) ⟨376055, by rfl⟩ : syracuseStep 501407 = 752111) B752111
theorem B632863 : Blo 499793 632863 := bstep (se 1 (by rfl) ⟨474647, by rfl⟩ : syracuseStep 632863 = 949295) B949295
theorem B503023 : Blo 499793 503023 := bstep (se 1 (by rfl) ⟨377267, by rfl⟩ : syracuseStep 503023 = 754535) B754535
theorem B13775183 : Blo 499793 13775183 := bstep (se 1 (by rfl) ⟨10331387, by rfl⟩ : syracuseStep 13775183 = 20662775) B20662775
theorem B11023543 : Blo 499793 11023543 := bstep (se 1 (by rfl) ⟨8267657, by rfl⟩ : syracuseStep 11023543 = 16535315) B16535315
theorem B2897207 : Blo 499793 2897207 := bstep (se 1 (by rfl) ⟨2172905, by rfl⟩ : syracuseStep 2897207 = 4345811) B4345811
theorem B1128095 : Blo 499793 1128095 := bstep (se 1 (by rfl) ⟨846071, by rfl⟩ : syracuseStep 1128095 = 1692143) B1692143
theorem B8599283 : Blo 499793 8599283 := bstep (se 1 (by rfl) ⟨6449462, by rfl⟩ : syracuseStep 8599283 = 12898925) B12898925
theorem B2210465 : Blo 499793 2210465 := bstep (se 2 (by rfl) ⟨828924, by rfl⟩ : syracuseStep 2210465 = 1657849) B1657849
theorem B1130471 : Blo 499793 1130471 := bstep (se 1 (by rfl) ⟨847853, by rfl⟩ : syracuseStep 1130471 = 1695707) B1695707
theorem B1523873 : Blo 499793 1523873 := bstep (se 2 (by rfl) ⟨571452, by rfl⟩ : syracuseStep 1523873 = 1142905) B1142905
theorem B1132073 : Blo 499793 1132073 := bstep (se 2 (by rfl) ⟨424527, by rfl⟩ : syracuseStep 1132073 = 849055) B849055
theorem B14632591 : Blo 499793 14632591 := bstep (se 1 (by rfl) ⟨10974443, by rfl⟩ : syracuseStep 14632591 = 21948887) B21948887
theorem B4900607 : Blo 499793 4900607 := bstep (se 1 (by rfl) ⟨3675455, by rfl⟩ : syracuseStep 4900607 = 7350911) B7350911
theorem B1132379 : Blo 499793 1132379 := bstep (se 1 (by rfl) ⟨849284, by rfl⟩ : syracuseStep 1132379 = 1698569) B1698569
theorem B1430207 : Blo 499793 1430207 := bstep (se 1 (by rfl) ⟨1072655, by rfl⟩ : syracuseStep 1430207 = 2145311) B2145311
theorem B15652601 : Blo 499793 15652601 := bstep (se 2 (by rfl) ⟨5869725, by rfl⟩ : syracuseStep 15652601 = 11739451) B11739451
theorem B1693439 : Blo 499793 1693439 := bstep (se 1 (by rfl) ⟨1270079, by rfl⟩ : syracuseStep 1693439 = 2540159) B2540159
theorem B35674019 : Blo 499793 35674019 := bstep (se 1 (by rfl) ⟨26755514, by rfl⟩ : syracuseStep 35674019 = 53511029) B53511029
theorem B1432417 : Blo 499793 1432417 := bstep (se 2 (by rfl) ⟨537156, by rfl⟩ : syracuseStep 1432417 = 1074313) B1074313
theorem B1433875 : Blo 499793 1433875 := bstep (se 1 (by rfl) ⟨1075406, by rfl⟩ : syracuseStep 1433875 = 2150813) B2150813
theorem B845471 : Blo 499793 845471 := bstep (se 1 (by rfl) ⟨634103, by rfl⟩ : syracuseStep 845471 = 1268207) B1268207
theorem B27813719 : Blo 499793 27813719 := bstep (se 1 (by rfl) ⟨20860289, by rfl⟩ : syracuseStep 27813719 = 41720579) B41720579
theorem B1206143 : Blo 499793 1206143 := bstep (se 1 (by rfl) ⟨904607, by rfl⟩ : syracuseStep 1206143 = 1809215) B1809215
theorem B4811035 : Blo 499793 4811035 := bstep (se 1 (by rfl) ⟨3608276, by rfl⟩ : syracuseStep 4811035 = 7216553) B7216553
theorem B846463 : Blo 499793 846463 := bstep (se 1 (by rfl) ⟨634847, by rfl⟩ : syracuseStep 846463 = 1269695) B1269695
theorem B1272449 : Blo 499793 1272449 := bstep (se 2 (by rfl) ⟨477168, by rfl⟩ : syracuseStep 1272449 = 954337) B954337
theorem B19557521 : Blo 499793 19557521 := bstep (se 2 (by rfl) ⟨7334070, by rfl⟩ : syracuseStep 19557521 = 14668141) B14668141
theorem B6451103 : Blo 499793 6451103 := bstep (se 1 (by rfl) ⟨4838327, by rfl⟩ : syracuseStep 6451103 = 9676655) B9676655
theorem B717103 : Blo 499793 717103 := bstep (se 1 (by rfl) ⟨537827, by rfl⟩ : syracuseStep 717103 = 1075655) B1075655
theorem B1602217 : Blo 499793 1602217 := bstep (se 2 (by rfl) ⟨600831, by rfl⟩ : syracuseStep 1602217 = 1201663) B1201663
theorem B750311 : Blo 499793 750311 := bstep (se 1 (by rfl) ⟨562733, by rfl⟩ : syracuseStep 750311 = 1125467) B1125467
theorem B8155991 : Blo 499793 8155991 := bstep (se 1 (by rfl) ⟨6116993, by rfl⟩ : syracuseStep 8155991 = 12233987) B12233987
theorem B2716699 : Blo 499793 2716699 := bstep (se 1 (by rfl) ⟨2037524, by rfl⟩ : syracuseStep 2716699 = 4075049) B4075049
theorem B848927 : Blo 499793 848927 := bstep (se 1 (by rfl) ⟨636695, by rfl⟩ : syracuseStep 848927 = 1273391) B1273391
theorem B751055 : Blo 499793 751055 := bstep (se 1 (by rfl) ⟨563291, by rfl⟩ : syracuseStep 751055 = 1126583) B1126583
theorem B3798575 : Blo 499793 3798575 := bstep (se 1 (by rfl) ⟨2848931, by rfl⟩ : syracuseStep 3798575 = 5697863) B5697863
theorem B1898909 : Blo 499793 1898909 := bstep (se 3 (by rfl) ⟨356045, by rfl⟩ : syracuseStep 1898909 = 712091) B712091
theorem B752807 : Blo 499793 752807 := bstep (se 1 (by rfl) ⟨564605, by rfl⟩ : syracuseStep 752807 = 1129211) B1129211
theorem B1015915 : Blo 499793 1015915 := bstep (se 1 (by rfl) ⟨761936, by rfl⟩ : syracuseStep 1015915 = 1523873) B1523873
theorem B754715 : Blo 499793 754715 := bstep (se 1 (by rfl) ⟨566036, by rfl⟩ : syracuseStep 754715 = 1132073) B1132073
theorem B754919 : Blo 499793 754919 := bstep (se 1 (by rfl) ⟨566189, by rfl⟩ : syracuseStep 754919 = 1132379) B1132379
theorem B14879623 : Blo 499793 14879623 := bstep (se 1 (by rfl) ⟨11159717, by rfl⟩ : syracuseStep 14879623 = 22319435) B22319435
theorem B953471 : Blo 499793 953471 := bstep (se 1 (by rfl) ⟨715103, by rfl⟩ : syracuseStep 953471 = 1430207) B1430207
theorem B956137 : Blo 499793 956137 := bstep (se 2 (by rfl) ⟨358551, by rfl⟩ : syracuseStep 956137 = 717103) B717103
theorem B2136289 : Blo 499793 2136289 := bstep (se 2 (by rfl) ⟨801108, by rfl⟩ : syracuseStep 2136289 = 1602217) B1602217
theorem B563647 : Blo 499793 563647 := bstep (se 1 (by rfl) ⟨422735, by rfl⟩ : syracuseStep 563647 = 845471) B845471
theorem B4300735 : Blo 499793 4300735 := bstep (se 1 (by rfl) ⟨3225551, by rfl⟩ : syracuseStep 4300735 = 6451103) B6451103
theorem B9183455 : Blo 499793 9183455 := bstep (se 1 (by rfl) ⟨6887591, by rfl⟩ : syracuseStep 9183455 = 13775183) B13775183
theorem B500207 : Blo 499793 500207 := bstep (se 1 (by rfl) ⟨375155, by rfl⟩ : syracuseStep 500207 = 750311) B750311
theorem B565951 : Blo 499793 565951 := bstep (se 1 (by rfl) ⟨424463, by rfl⟩ : syracuseStep 565951 = 848927) B848927
theorem B500703 : Blo 499793 500703 := bstep (se 1 (by rfl) ⟨375527, by rfl⟩ : syracuseStep 500703 = 751055) B751055
theorem B2532383 : Blo 499793 2532383 := bstep (se 1 (by rfl) ⟨1899287, by rfl⟩ : syracuseStep 2532383 = 3798575) B3798575
theorem B1909889 : Blo 499793 1909889 := bstep (se 2 (by rfl) ⟨716208, by rfl⟩ : syracuseStep 1909889 = 1432417) B1432417
theorem B501871 : Blo 499793 501871 := bstep (se 1 (by rfl) ⟨376403, by rfl⟩ : syracuseStep 501871 = 752807) B752807
theorem B43821739 : Blo 499793 43821739 := bstep (se 1 (by rfl) ⟨32866304, by rfl⟩ : syracuseStep 43821739 = 65732609) B65732609
theorem B1911833 : Blo 499793 1911833 := bstep (se 2 (by rfl) ⟨716937, by rfl⟩ : syracuseStep 1911833 = 1433875) B1433875
theorem B2535623 : Blo 499793 2535623 := bstep (se 1 (by rfl) ⟨1901717, by rfl⟩ : syracuseStep 2535623 = 3803435) B3803435
theorem B2601175 : Blo 499793 2601175 := bstep (se 1 (by rfl) ⟨1950881, by rfl⟩ : syracuseStep 2601175 = 3901763) B3901763
theorem B635131 : Blo 499793 635131 := bstep (se 1 (by rfl) ⟨476348, by rfl⟩ : syracuseStep 635131 = 952697) B952697
theorem B19510121 : Blo 499793 19510121 := bstep (se 2 (by rfl) ⟨7316295, by rfl⟩ : syracuseStep 19510121 = 14632591) B14632591
theorem B1291967 : Blo 499793 1291967 := bstep (se 1 (by rfl) ⟨968975, by rfl⟩ : syracuseStep 1291967 = 1937951) B1937951
theorem B2537405 : Blo 499793 2537405 := bstep (se 3 (by rfl) ⟨475763, by rfl⟩ : syracuseStep 2537405 = 951527) B951527
theorem B1128617 : Blo 499793 1128617 := bstep (se 2 (by rfl) ⟨423231, by rfl⟩ : syracuseStep 1128617 = 846463) B846463
theorem B637247 : Blo 499793 637247 := bstep (se 1 (by rfl) ⟨477935, by rfl⟩ : syracuseStep 637247 = 955871) B955871
theorem B10435067 : Blo 499793 10435067 := bstep (se 1 (by rfl) ⟨7826300, by rfl⟩ : syracuseStep 10435067 = 15652601) B15652601
theorem B1128959 : Blo 499793 1128959 := bstep (se 1 (by rfl) ⟨846719, by rfl⟩ : syracuseStep 1128959 = 1693439) B1693439
theorem B32096351 : Blo 499793 32096351 := bstep (se 1 (by rfl) ⟨24072263, by rfl⟩ : syracuseStep 32096351 = 48144527) B48144527
theorem B1098617 : Blo 499793 1098617 := bstep (se 2 (by rfl) ⟨411981, by rfl⟩ : syracuseStep 1098617 = 823963) B823963
theorem B804095 : Blo 499793 804095 := bstep (se 1 (by rfl) ⟨603071, by rfl⟩ : syracuseStep 804095 = 1206143) B1206143
theorem B3622265 : Blo 499793 3622265 := bstep (se 2 (by rfl) ⟨1358349, by rfl⟩ : syracuseStep 3622265 = 2716699) B2716699
theorem B14698057 : Blo 499793 14698057 := bstep (se 2 (by rfl) ⟨5511771, by rfl⟩ : syracuseStep 14698057 = 11023543) B11023543
theorem B1265939 : Blo 499793 1265939 := bstep (se 1 (by rfl) ⟨949454, by rfl⟩ : syracuseStep 1265939 = 1898909) B1898909
theorem B2544209 : Blo 499793 2544209 := bstep (se 2 (by rfl) ⟨954078, by rfl⟩ : syracuseStep 2544209 = 1908157) B1908157
theorem B1267559 : Blo 499793 1267559 := bstep (se 1 (by rfl) ⟨950669, by rfl⟩ : syracuseStep 1267559 = 1901339) B1901339
theorem B3267071 : Blo 499793 3267071 := bstep (se 1 (by rfl) ⟨2450303, by rfl⟩ : syracuseStep 3267071 = 4900607) B4900607
theorem B679147 : Blo 499793 679147 := bstep (se 1 (by rfl) ⟨509360, by rfl⟩ : syracuseStep 679147 = 1018721) B1018721
theorem B843817 : Blo 499793 843817 := bstep (se 2 (by rfl) ⟨316431, by rfl⟩ : syracuseStep 843817 = 632863) B632863
theorem B6414713 : Blo 499793 6414713 := bstep (se 2 (by rfl) ⟨2405517, by rfl⟩ : syracuseStep 6414713 = 4811035) B4811035
theorem B23782679 : Blo 499793 23782679 := bstep (se 1 (by rfl) ⟨17837009, by rfl⟩ : syracuseStep 23782679 = 35674019) B35674019
theorem B1271983 : Blo 499793 1271983 := bstep (se 1 (by rfl) ⟨953987, by rfl⟩ : syracuseStep 1271983 = 1907975) B1907975
theorem B813439 : Blo 499793 813439 := bstep (se 1 (by rfl) ⟨610079, by rfl⟩ : syracuseStep 813439 = 1220159) B1220159
theorem B1272287 : Blo 499793 1272287 := bstep (se 1 (by rfl) ⟨954215, by rfl⟩ : syracuseStep 1272287 = 1908431) B1908431
theorem B18542479 : Blo 499793 18542479 := bstep (se 1 (by rfl) ⟨13906859, by rfl⟩ : syracuseStep 18542479 = 27813719) B27813719
theorem B848299 : Blo 499793 848299 := bstep (se 1 (by rfl) ⟨636224, by rfl⟩ : syracuseStep 848299 = 1272449) B1272449
theorem B13038347 : Blo 499793 13038347 := bstep (se 1 (by rfl) ⟨9778760, by rfl⟩ : syracuseStep 13038347 = 19557521) B19557521
theorem B5437327 : Blo 499793 5437327 := bstep (se 1 (by rfl) ⟨4077995, by rfl⟩ : syracuseStep 5437327 = 8155991) B8155991
theorem B1931471 : Blo 499793 1931471 := bstep (se 1 (by rfl) ⟨1448603, by rfl⟩ : syracuseStep 1931471 = 2897207) B2897207
theorem B752063 : Blo 499793 752063 := bstep (se 1 (by rfl) ⟨564047, by rfl⟩ : syracuseStep 752063 = 1128095) B1128095
theorem B5732855 : Blo 499793 5732855 := bstep (se 1 (by rfl) ⟨4299641, by rfl⟩ : syracuseStep 5732855 = 8599283) B8599283
theorem B1473643 : Blo 499793 1473643 := bstep (se 1 (by rfl) ⟨1105232, by rfl⟩ : syracuseStep 1473643 = 2210465) B2210465
theorem B753647 : Blo 499793 753647 := bstep (se 1 (by rfl) ⟨565235, by rfl⟩ : syracuseStep 753647 = 1130471) B1130471
theorem B21397567 : Blo 499793 21397567 := bstep (se 1 (by rfl) ⟨16048175, by rfl⟩ : syracuseStep 21397567 = 32096351) B32096351
theorem B754601 : Blo 499793 754601 := bstep (se 2 (by rfl) ⟨282975, by rfl⟩ : syracuseStep 754601 = 565951) B565951
theorem B19597409 : Blo 499793 19597409 := bstep (se 2 (by rfl) ⟨7349028, by rfl⟩ : syracuseStep 19597409 = 14698057) B14698057
theorem B1084585 : Blo 499793 1084585 := bstep (se 2 (by rfl) ⟨406719, by rfl⟩ : syracuseStep 1084585 = 813439) B813439
theorem B58428985 : Blo 499793 58428985 := bstep (se 2 (by rfl) ⟨21910869, by rfl⟩ : syracuseStep 58428985 = 43821739) B43821739
theorem B7249769 : Blo 499793 7249769 := bstep (se 2 (by rfl) ⟨2718663, by rfl⟩ : syracuseStep 7249769 = 5437327) B5437327
theorem B8692231 : Blo 499793 8692231 := bstep (se 1 (by rfl) ⟨6519173, by rfl⟩ : syracuseStep 8692231 = 13038347) B13038347
theorem B861311 : Blo 499793 861311 := bstep (se 1 (by rfl) ⟨645983, by rfl⟩ : syracuseStep 861311 = 1291967) B1291967
theorem B1287647 : Blo 499793 1287647 := bstep (se 1 (by rfl) ⟨965735, by rfl⟩ : syracuseStep 1287647 = 1931471) B1931471
theorem B501375 : Blo 499793 501375 := bstep (se 1 (by rfl) ⟨376031, by rfl⟩ : syracuseStep 501375 = 752063) B752063
theorem B6956711 : Blo 499793 6956711 := bstep (se 1 (by rfl) ⟨5217533, by rfl⟩ : syracuseStep 6956711 = 10435067) B10435067
theorem B502431 : Blo 499793 502431 := bstep (se 1 (by rfl) ⟨376823, by rfl⟩ : syracuseStep 502431 = 753647) B753647
theorem B1125089 : Blo 499793 1125089 := bstep (se 2 (by rfl) ⟨421908, by rfl⟩ : syracuseStep 1125089 = 843817) B843817
theorem B1354553 : Blo 499793 1354553 := bstep (se 2 (by rfl) ⟨507957, by rfl⟩ : syracuseStep 1354553 = 1015915) B1015915
theorem B503143 : Blo 499793 503143 := bstep (se 1 (by rfl) ⟨377357, by rfl⟩ : syracuseStep 503143 = 754715) B754715
theorem B503279 : Blo 499793 503279 := bstep (se 1 (by rfl) ⟨377459, by rfl⟩ : syracuseStep 503279 = 754919) B754919
theorem B536063 : Blo 499793 536063 := bstep (se 1 (by rfl) ⟨402047, by rfl⟩ : syracuseStep 536063 = 804095) B804095
theorem B2929645 : Blo 499793 2929645 := bstep (se 3 (by rfl) ⟨549308, by rfl⟩ : syracuseStep 2929645 = 1098617) B1098617
theorem B19839497 : Blo 499793 19839497 := bstep (se 2 (by rfl) ⟨7439811, by rfl⟩ : syracuseStep 19839497 = 14879623) B14879623
theorem B2178047 : Blo 499793 2178047 := bstep (se 1 (by rfl) ⟨1633535, by rfl⟩ : syracuseStep 2178047 = 3267071) B3267071
theorem B24723305 : Blo 499793 24723305 := bstep (se 2 (by rfl) ⟨9271239, by rfl⟩ : syracuseStep 24723305 = 18542479) B18542479
theorem B4276475 : Blo 499793 4276475 := bstep (se 1 (by rfl) ⟨3207356, by rfl⟩ : syracuseStep 4276475 = 6414713) B6414713
theorem B1131065 : Blo 499793 1131065 := bstep (se 2 (by rfl) ⟨424149, by rfl⟩ : syracuseStep 1131065 = 848299) B848299
theorem B1688255 : Blo 499793 1688255 := bstep (se 1 (by rfl) ⟨1266191, by rfl⟩ : syracuseStep 1688255 = 2532383) B2532383
theorem B3622117 : Blo 499793 3622117 := bstep (se 4 (by rfl) ⟨339573, by rfl⟩ : syracuseStep 3622117 = 679147) B679147
theorem B1690415 : Blo 499793 1690415 := bstep (se 1 (by rfl) ⟨1267811, by rfl⟩ : syracuseStep 1690415 = 2535623) B2535623
theorem B2542589 : Blo 499793 2542589 := bstep (se 3 (by rfl) ⟨476735, by rfl⟩ : syracuseStep 2542589 = 953471) B953471
theorem B1691603 : Blo 499793 1691603 := bstep (se 1 (by rfl) ⟨1268702, by rfl⟩ : syracuseStep 1691603 = 2537405) B2537405
theorem B3821903 : Blo 499793 3821903 := bstep (se 1 (by rfl) ⟨2866427, by rfl⟩ : syracuseStep 3821903 = 5732855) B5732855
theorem B2414843 : Blo 499793 2414843 := bstep (se 1 (by rfl) ⟨1811132, by rfl⟩ : syracuseStep 2414843 = 3622265) B3622265
theorem B843959 : Blo 499793 843959 := bstep (se 1 (by rfl) ⟨632969, by rfl⟩ : syracuseStep 843959 = 1265939) B1265939
theorem B1695977 : Blo 499793 1695977 := bstep (se 2 (by rfl) ⟨635991, by rfl⟩ : syracuseStep 1695977 = 1271983) B1271983
theorem B1696139 : Blo 499793 1696139 := bstep (se 1 (by rfl) ⟨1272104, by rfl⟩ : syracuseStep 1696139 = 2544209) B2544209
theorem B845039 : Blo 499793 845039 := bstep (se 1 (by rfl) ⟨633779, by rfl⟩ : syracuseStep 845039 = 1267559) B1267559
theorem B6122303 : Blo 499793 6122303 := bstep (se 1 (by rfl) ⟨4591727, by rfl⟩ : syracuseStep 6122303 = 9183455) B9183455
theorem B3468233 : Blo 499793 3468233 := bstep (se 2 (by rfl) ⟨1300587, by rfl⟩ : syracuseStep 3468233 = 2601175) B2601175
theorem B846841 : Blo 499793 846841 := bstep (se 2 (by rfl) ⟨317565, by rfl⟩ : syracuseStep 846841 = 635131) B635131
theorem B7859429 : Blo 499793 7859429 := bstep (se 4 (by rfl) ⟨736821, by rfl⟩ : syracuseStep 7859429 = 1473643) B1473643
theorem B1273259 : Blo 499793 1273259 := bstep (se 1 (by rfl) ⟨954944, by rfl⟩ : syracuseStep 1273259 = 1909889) B1909889
theorem B1699325 : Blo 499793 1699325 := bstep (se 3 (by rfl) ⟨318623, by rfl⟩ : syracuseStep 1699325 = 637247) B637247
theorem B15855119 : Blo 499793 15855119 := bstep (se 1 (by rfl) ⟨11891339, by rfl⟩ : syracuseStep 15855119 = 23782679) B23782679
theorem B848191 : Blo 499793 848191 := bstep (se 1 (by rfl) ⟨636143, by rfl⟩ : syracuseStep 848191 = 1272287) B1272287
theorem B1274555 : Blo 499793 1274555 := bstep (se 1 (by rfl) ⟨955916, by rfl⟩ : syracuseStep 1274555 = 1911833) B1911833
theorem B1274849 : Blo 499793 1274849 := bstep (se 2 (by rfl) ⟨478068, by rfl⟩ : syracuseStep 1274849 = 956137) B956137
theorem B2848385 : Blo 499793 2848385 := bstep (se 2 (by rfl) ⟨1068144, by rfl⟩ : syracuseStep 2848385 = 2136289) B2136289
theorem B13006747 : Blo 499793 13006747 := bstep (se 1 (by rfl) ⟨9755060, by rfl⟩ : syracuseStep 13006747 = 19510121) B19510121
theorem B751529 : Blo 499793 751529 := bstep (se 2 (by rfl) ⟨281823, by rfl⟩ : syracuseStep 751529 = 563647) B563647
theorem B752411 : Blo 499793 752411 := bstep (se 1 (by rfl) ⟨564308, by rfl⟩ : syracuseStep 752411 = 1128617) B1128617
theorem B752639 : Blo 499793 752639 := bstep (se 1 (by rfl) ⟨564479, by rfl⟩ : syracuseStep 752639 = 1128959) B1128959
theorem B5734313 : Blo 499793 5734313 := bstep (se 2 (by rfl) ⟨2150367, by rfl⟩ : syracuseStep 5734313 = 4300735) B4300735
theorem B2850983 : Blo 499793 2850983 := bstep (se 1 (by rfl) ⟨2138237, by rfl⟩ : syracuseStep 2850983 = 4276475) B4276475
theorem B754043 : Blo 499793 754043 := bstep (se 1 (by rfl) ⟨565532, by rfl⟩ : syracuseStep 754043 = 1131065) B1131065
theorem B2296829 : Blo 499793 2296829 := bstep (se 3 (by rfl) ⟨430655, by rfl⟩ : syracuseStep 2296829 = 861311) B861311
theorem B1609895 : Blo 499793 1609895 := bstep (se 1 (by rfl) ⟨1207421, by rfl⟩ : syracuseStep 1609895 = 2414843) B2414843
theorem B1446113 : Blo 499793 1446113 := bstep (se 2 (by rfl) ⟨542292, by rfl⟩ : syracuseStep 1446113 = 1084585) B1084585
theorem B562639 : Blo 499793 562639 := bstep (se 1 (by rfl) ⟨421979, by rfl⟩ : syracuseStep 562639 = 843959) B843959
theorem B563359 : Blo 499793 563359 := bstep (se 1 (by rfl) ⟨422519, by rfl⟩ : syracuseStep 563359 = 845039) B845039
theorem B858431 : Blo 499793 858431 := bstep (se 1 (by rfl) ⟨643823, by rfl⟩ : syracuseStep 858431 = 1287647) B1287647
theorem B3906193 : Blo 499793 3906193 := bstep (se 2 (by rfl) ⟨1464822, by rfl⟩ : syracuseStep 3906193 = 2929645) B2929645
theorem B5808125 : Blo 499793 5808125 := bstep (se 3 (by rfl) ⟨1089023, by rfl⟩ : syracuseStep 5808125 = 2178047) B2178047
theorem B501019 : Blo 499793 501019 := bstep (se 1 (by rfl) ⟨375764, by rfl⟩ : syracuseStep 501019 = 751529) B751529
theorem B501607 : Blo 499793 501607 := bstep (se 1 (by rfl) ⟨376205, by rfl⟩ : syracuseStep 501607 = 752411) B752411
theorem B501759 : Blo 499793 501759 := bstep (se 1 (by rfl) ⟨376319, by rfl⟩ : syracuseStep 501759 = 752639) B752639
theorem B1125503 : Blo 499793 1125503 := bstep (se 1 (by rfl) ⟨844127, by rfl⟩ : syracuseStep 1125503 = 1688255) B1688255
theorem B503067 : Blo 499793 503067 := bstep (se 1 (by rfl) ⟨377300, by rfl⟩ : syracuseStep 503067 = 754601) B754601
theorem B4829489 : Blo 499793 4829489 := bstep (se 2 (by rfl) ⟨1811058, by rfl⟩ : syracuseStep 4829489 = 3622117) B3622117
theorem B1126943 : Blo 499793 1126943 := bstep (se 1 (by rfl) ⟨845207, by rfl⟩ : syracuseStep 1126943 = 1690415) B1690415
theorem B1127735 : Blo 499793 1127735 := bstep (se 1 (by rfl) ⟨845801, by rfl⟩ : syracuseStep 1127735 = 1691603) B1691603
theorem B1129121 : Blo 499793 1129121 := bstep (se 2 (by rfl) ⟨423420, by rfl⟩ : syracuseStep 1129121 = 846841) B846841
theorem B77905313 : Blo 499793 77905313 := bstep (se 2 (by rfl) ⟨29214492, by rfl⟩ : syracuseStep 77905313 = 58428985) B58428985
theorem B4833179 : Blo 499793 4833179 := bstep (se 1 (by rfl) ⟨3624884, by rfl⟩ : syracuseStep 4833179 = 7249769) B7249769
theorem B1130651 : Blo 499793 1130651 := bstep (se 1 (by rfl) ⟨847988, by rfl⟩ : syracuseStep 1130651 = 1695977) B1695977
theorem B1130759 : Blo 499793 1130759 := bstep (se 1 (by rfl) ⟨848069, by rfl⟩ : syracuseStep 1130759 = 1696139) B1696139
theorem B1130921 : Blo 499793 1130921 := bstep (se 2 (by rfl) ⟨424095, by rfl⟩ : syracuseStep 1130921 = 848191) B848191
theorem B4637807 : Blo 499793 4637807 := bstep (se 1 (by rfl) ⟨3478355, by rfl⟩ : syracuseStep 4637807 = 6956711) B6956711
theorem B52905325 : Blo 499793 52905325 := bstep (se 3 (by rfl) ⟨9919748, by rfl⟩ : syracuseStep 52905325 = 19839497) B19839497
theorem B903035 : Blo 499793 903035 := bstep (se 1 (by rfl) ⟨677276, by rfl⟩ : syracuseStep 903035 = 1354553) B1354553
theorem B4081535 : Blo 499793 4081535 := bstep (se 1 (by rfl) ⟨3061151, by rfl⟩ : syracuseStep 4081535 = 6122303) B6122303
theorem B2312155 : Blo 499793 2312155 := bstep (se 1 (by rfl) ⟨1734116, by rfl⟩ : syracuseStep 2312155 = 3468233) B3468233
theorem B1132883 : Blo 499793 1132883 := bstep (se 1 (by rfl) ⟨849662, by rfl⟩ : syracuseStep 1132883 = 1699325) B1699325
theorem B10570079 : Blo 499793 10570079 := bstep (se 1 (by rfl) ⟨7927559, by rfl⟩ : syracuseStep 10570079 = 15855119) B15855119
theorem B1429501 : Blo 499793 1429501 := bstep (se 3 (by rfl) ⟨268031, by rfl⟩ : syracuseStep 1429501 = 536063) B536063
theorem B3822875 : Blo 499793 3822875 := bstep (se 1 (by rfl) ⟨2867156, by rfl⟩ : syracuseStep 3822875 = 5734313) B5734313
theorem B28530089 : Blo 499793 28530089 := bstep (se 2 (by rfl) ⟨10698783, by rfl⟩ : syracuseStep 28530089 = 21397567) B21397567
theorem B11589641 : Blo 499793 11589641 := bstep (se 2 (by rfl) ⟨4346115, by rfl⟩ : syracuseStep 11589641 = 8692231) B8692231
theorem B13064939 : Blo 499793 13064939 := bstep (se 1 (by rfl) ⟨9798704, by rfl⟩ : syracuseStep 13064939 = 19597409) B19597409
theorem B1695059 : Blo 499793 1695059 := bstep (se 1 (by rfl) ⟨1271294, by rfl⟩ : syracuseStep 1695059 = 2542589) B2542589
theorem B2547935 : Blo 499793 2547935 := bstep (se 1 (by rfl) ⟨1910951, by rfl⟩ : syracuseStep 2547935 = 3821903) B3821903
theorem B750059 : Blo 499793 750059 := bstep (se 1 (by rfl) ⟨562544, by rfl⟩ : syracuseStep 750059 = 1125089) B1125089
theorem B5239619 : Blo 499793 5239619 := bstep (se 1 (by rfl) ⟨3929714, by rfl⟩ : syracuseStep 5239619 = 7859429) B7859429
theorem B848839 : Blo 499793 848839 := bstep (se 1 (by rfl) ⟨636629, by rfl⟩ : syracuseStep 848839 = 1273259) B1273259
theorem B849703 : Blo 499793 849703 := bstep (se 1 (by rfl) ⟨637277, by rfl⟩ : syracuseStep 849703 = 1274555) B1274555
theorem B849899 : Blo 499793 849899 := bstep (se 1 (by rfl) ⟨637424, by rfl⟩ : syracuseStep 849899 = 1274849) B1274849
theorem B1898923 : Blo 499793 1898923 := bstep (se 1 (by rfl) ⟨1424192, by rfl⟩ : syracuseStep 1898923 = 2848385) B2848385
theorem B69369317 : Blo 499793 69369317 := bstep (se 4 (by rfl) ⟨6503373, by rfl⟩ : syracuseStep 69369317 = 13006747) B13006747
theorem B16482203 : Blo 499793 16482203 := bstep (se 1 (by rfl) ⟨12361652, by rfl⟩ : syracuseStep 16482203 = 24723305) B24723305
theorem B753767 : Blo 499793 753767 := bstep (se 1 (by rfl) ⟨565325, by rfl⟩ : syracuseStep 753767 = 1130651) B1130651
theorem B1900655 : Blo 499793 1900655 := bstep (se 1 (by rfl) ⟨1425491, by rfl⟩ : syracuseStep 1900655 = 2850983) B2850983
theorem B753839 : Blo 499793 753839 := bstep (se 1 (by rfl) ⟨565379, by rfl⟩ : syracuseStep 753839 = 1130759) B1130759
theorem B753947 : Blo 499793 753947 := bstep (se 1 (by rfl) ⟨565460, by rfl⟩ : syracuseStep 753947 = 1130921) B1130921
theorem B2721023 : Blo 499793 2721023 := bstep (se 1 (by rfl) ⟨2040767, by rfl⟩ : syracuseStep 2721023 = 4081535) B4081535
theorem B755255 : Blo 499793 755255 := bstep (se 1 (by rfl) ⟨566441, by rfl⟩ : syracuseStep 755255 = 1132883) B1132883
theorem B7046719 : Blo 499793 7046719 := bstep (se 1 (by rfl) ⟨5285039, by rfl⟩ : syracuseStep 7046719 = 10570079) B10570079
theorem B3082873 : Blo 499793 3082873 := bstep (se 2 (by rfl) ⟨1156077, by rfl⟩ : syracuseStep 3082873 = 2312155) B2312155
theorem B1906001 : Blo 499793 1906001 := bstep (se 2 (by rfl) ⟨714750, by rfl⟩ : syracuseStep 1906001 = 1429501) B1429501
theorem B3872083 : Blo 499793 3872083 := bstep (se 1 (by rfl) ⟨2904062, by rfl⟩ : syracuseStep 3872083 = 5808125) B5808125
theorem B3219659 : Blo 499793 3219659 := bstep (se 1 (by rfl) ⟨2414744, by rfl⟩ : syracuseStep 3219659 = 4829489) B4829489
theorem B500039 : Blo 499793 500039 := bstep (se 1 (by rfl) ⟨375029, by rfl⟩ : syracuseStep 500039 = 750059) B750059
theorem B2531897 : Blo 499793 2531897 := bstep (se 2 (by rfl) ⟨949461, by rfl⟩ : syracuseStep 2531897 = 1898923) B1898923
theorem B566599 : Blo 499793 566599 := bstep (se 1 (by rfl) ⟨424949, by rfl⟩ : syracuseStep 566599 = 849899) B849899
theorem B46246211 : Blo 499793 46246211 := bstep (se 1 (by rfl) ⟨34684658, by rfl⟩ : syracuseStep 46246211 = 69369317) B69369317
theorem B10988135 : Blo 499793 10988135 := bstep (se 1 (by rfl) ⟨8241101, by rfl⟩ : syracuseStep 10988135 = 16482203) B16482203
theorem B3222119 : Blo 499793 3222119 := bstep (se 1 (by rfl) ⟨2416589, by rfl⟩ : syracuseStep 3222119 = 4833179) B4833179
theorem B502695 : Blo 499793 502695 := bstep (se 1 (by rfl) ⟨377021, by rfl⟩ : syracuseStep 502695 = 754043) B754043
theorem B3091871 : Blo 499793 3091871 := bstep (se 1 (by rfl) ⟨2318903, by rfl⟩ : syracuseStep 3091871 = 4637807) B4637807
theorem B964075 : Blo 499793 964075 := bstep (se 1 (by rfl) ⟨723056, by rfl⟩ : syracuseStep 964075 = 1446113) B1446113
theorem B19020059 : Blo 499793 19020059 := bstep (se 1 (by rfl) ⟨14265044, by rfl⟩ : syracuseStep 19020059 = 28530089) B28530089
theorem B1130039 : Blo 499793 1130039 := bstep (se 1 (by rfl) ⟨847529, by rfl⟩ : syracuseStep 1130039 = 1695059) B1695059
theorem B2408093 : Blo 499793 2408093 := bstep (se 3 (by rfl) ⟨451517, by rfl⟩ : syracuseStep 2408093 = 903035) B903035
theorem B1131785 : Blo 499793 1131785 := bstep (se 2 (by rfl) ⟨424419, by rfl⟩ : syracuseStep 1131785 = 848839) B848839
theorem B1132937 : Blo 499793 1132937 := bstep (se 2 (by rfl) ⟨424851, by rfl⟩ : syracuseStep 1132937 = 849703) B849703
theorem B3493079 : Blo 499793 3493079 := bstep (se 1 (by rfl) ⟨2619809, by rfl⟩ : syracuseStep 3493079 = 5239619) B5239619
theorem B70540433 : Blo 499793 70540433 := bstep (se 2 (by rfl) ⟨26452662, by rfl⟩ : syracuseStep 70540433 = 52905325) B52905325
theorem B1531219 : Blo 499793 1531219 := bstep (se 1 (by rfl) ⟨1148414, by rfl⟩ : syracuseStep 1531219 = 2296829) B2296829
theorem B1073263 : Blo 499793 1073263 := bstep (se 1 (by rfl) ⟨804947, by rfl⟩ : syracuseStep 1073263 = 1609895) B1609895
theorem B2548583 : Blo 499793 2548583 := bstep (se 1 (by rfl) ⟨1911437, by rfl⟩ : syracuseStep 2548583 = 3822875) B3822875
theorem B7726427 : Blo 499793 7726427 := bstep (se 1 (by rfl) ⟨5794820, by rfl⟩ : syracuseStep 7726427 = 11589641) B11589641
theorem B8709959 : Blo 499793 8709959 := bstep (se 1 (by rfl) ⟨6532469, by rfl⟩ : syracuseStep 8709959 = 13064939) B13064939
theorem B1698623 : Blo 499793 1698623 := bstep (se 1 (by rfl) ⟨1273967, by rfl⟩ : syracuseStep 1698623 = 2547935) B2547935
theorem B2289149 : Blo 499793 2289149 := bstep (se 3 (by rfl) ⟨429215, by rfl⟩ : syracuseStep 2289149 = 858431) B858431
theorem B750185 : Blo 499793 750185 := bstep (se 2 (by rfl) ⟨281319, by rfl⟩ : syracuseStep 750185 = 562639) B562639
theorem B750335 : Blo 499793 750335 := bstep (se 1 (by rfl) ⟨562751, by rfl⟩ : syracuseStep 750335 = 1125503) B1125503
theorem B751145 : Blo 499793 751145 := bstep (se 2 (by rfl) ⟨281679, by rfl⟩ : syracuseStep 751145 = 563359) B563359
theorem B751295 : Blo 499793 751295 := bstep (se 1 (by rfl) ⟨563471, by rfl⟩ : syracuseStep 751295 = 1126943) B1126943
theorem B5208257 : Blo 499793 5208257 := bstep (se 2 (by rfl) ⟨1953096, by rfl⟩ : syracuseStep 5208257 = 3906193) B3906193
theorem B751823 : Blo 499793 751823 := bstep (se 1 (by rfl) ⟨563867, by rfl⟩ : syracuseStep 751823 = 1127735) B1127735
theorem B752747 : Blo 499793 752747 := bstep (se 1 (by rfl) ⟨564560, by rfl⟩ : syracuseStep 752747 = 1129121) B1129121
theorem B51936875 : Blo 499793 51936875 := bstep (se 1 (by rfl) ⟨38952656, by rfl⟩ : syracuseStep 51936875 = 77905313) B77905313
theorem B754523 : Blo 499793 754523 := bstep (se 1 (by rfl) ⟨565892, by rfl⟩ : syracuseStep 754523 = 1131785) B1131785
theorem B755291 : Blo 499793 755291 := bstep (se 1 (by rfl) ⟨566468, by rfl⟩ : syracuseStep 755291 = 1132937) B1132937
theorem B755465 : Blo 499793 755465 := bstep (se 2 (by rfl) ⟨283299, by rfl⟩ : syracuseStep 755465 = 566599) B566599
theorem B37259509 : Blo 499793 37259509 := bstep (se 5 (by rfl) ⟨1746539, by rfl⟩ : syracuseStep 37259509 = 3493079) B3493079
theorem B47026955 : Blo 499793 47026955 := bstep (se 1 (by rfl) ⟨35270216, by rfl⟩ : syracuseStep 47026955 = 70540433) B70540433
theorem B5150951 : Blo 499793 5150951 := bstep (se 1 (by rfl) ⟨3863213, by rfl⟩ : syracuseStep 5150951 = 7726427) B7726427
theorem B5806639 : Blo 499793 5806639 := bstep (se 1 (by rfl) ⟨4354979, by rfl⟩ : syracuseStep 5806639 = 8709959) B8709959
theorem B1285433 : Blo 499793 1285433 := bstep (se 2 (by rfl) ⟨482037, by rfl⟩ : syracuseStep 1285433 = 964075) B964075
theorem B500123 : Blo 499793 500123 := bstep (se 1 (by rfl) ⟨375092, by rfl⟩ : syracuseStep 500123 = 750185) B750185
theorem B500223 : Blo 499793 500223 := bstep (se 1 (by rfl) ⟨375167, by rfl⟩ : syracuseStep 500223 = 750335) B750335
theorem B500763 : Blo 499793 500763 := bstep (se 1 (by rfl) ⟨375572, by rfl⟩ : syracuseStep 500763 = 751145) B751145
theorem B500863 : Blo 499793 500863 := bstep (se 1 (by rfl) ⟨375647, by rfl⟩ : syracuseStep 500863 = 751295) B751295
theorem B501215 : Blo 499793 501215 := bstep (se 1 (by rfl) ⟨375911, by rfl⟩ : syracuseStep 501215 = 751823) B751823
theorem B2041625 : Blo 499793 2041625 := bstep (se 2 (by rfl) ⟨765609, by rfl⟩ : syracuseStep 2041625 = 1531219) B1531219
theorem B501831 : Blo 499793 501831 := bstep (se 1 (by rfl) ⟨376373, by rfl⟩ : syracuseStep 501831 = 752747) B752747
theorem B502511 : Blo 499793 502511 := bstep (se 1 (by rfl) ⟨376883, by rfl⟩ : syracuseStep 502511 = 753767) B753767
theorem B502559 : Blo 499793 502559 := bstep (se 1 (by rfl) ⟨376919, by rfl⟩ : syracuseStep 502559 = 753839) B753839
theorem B502631 : Blo 499793 502631 := bstep (se 1 (by rfl) ⟨376973, by rfl⟩ : syracuseStep 502631 = 753947) B753947
theorem B1814015 : Blo 499793 1814015 := bstep (se 1 (by rfl) ⟨1360511, by rfl⟩ : syracuseStep 1814015 = 2721023) B2721023
theorem B503503 : Blo 499793 503503 := bstep (se 1 (by rfl) ⟨377627, by rfl⟩ : syracuseStep 503503 = 755255) B755255
theorem B4110497 : Blo 499793 4110497 := bstep (se 2 (by rfl) ⟨1541436, by rfl⟩ : syracuseStep 4110497 = 3082873) B3082873
theorem B2146439 : Blo 499793 2146439 := bstep (se 1 (by rfl) ⟨1609829, by rfl⟩ : syracuseStep 2146439 = 3219659) B3219659
theorem B1687931 : Blo 499793 1687931 := bstep (se 1 (by rfl) ⟨1265948, by rfl⟩ : syracuseStep 1687931 = 2531897) B2531897
theorem B7325423 : Blo 499793 7325423 := bstep (se 1 (by rfl) ⟨5494067, by rfl⟩ : syracuseStep 7325423 = 10988135) B10988135
theorem B2148079 : Blo 499793 2148079 := bstep (se 1 (by rfl) ⟨1611059, by rfl⟩ : syracuseStep 2148079 = 3222119) B3222119
theorem B5162777 : Blo 499793 5162777 := bstep (se 2 (by rfl) ⟨1936041, by rfl⟩ : syracuseStep 5162777 = 3872083) B3872083
theorem B1132415 : Blo 499793 1132415 := bstep (se 1 (by rfl) ⟨849311, by rfl⟩ : syracuseStep 1132415 = 1698623) B1698623
theorem B1526099 : Blo 499793 1526099 := bstep (se 1 (by rfl) ⟨1144574, by rfl⟩ : syracuseStep 1526099 = 2289149) B2289149
theorem B34624583 : Blo 499793 34624583 := bstep (se 1 (by rfl) ⟨25968437, by rfl⟩ : syracuseStep 34624583 = 51936875) B51936875
theorem B1267103 : Blo 499793 1267103 := bstep (se 1 (by rfl) ⟨950327, by rfl⟩ : syracuseStep 1267103 = 1900655) B1900655
theorem B1431017 : Blo 499793 1431017 := bstep (se 2 (by rfl) ⟨536631, by rfl⟩ : syracuseStep 1431017 = 1073263) B1073263
theorem B1270667 : Blo 499793 1270667 := bstep (se 1 (by rfl) ⟨953000, by rfl⟩ : syracuseStep 1270667 = 1906001) B1906001
theorem B13888685 : Blo 499793 13888685 := bstep (se 3 (by rfl) ⟨2604128, by rfl⟩ : syracuseStep 13888685 = 5208257) B5208257
theorem B1699055 : Blo 499793 1699055 := bstep (se 1 (by rfl) ⟨1274291, by rfl⟩ : syracuseStep 1699055 = 2548583) B2548583
theorem B30830807 : Blo 499793 30830807 := bstep (se 1 (by rfl) ⟨23123105, by rfl⟩ : syracuseStep 30830807 = 46246211) B46246211
theorem B2061247 : Blo 499793 2061247 := bstep (se 1 (by rfl) ⟨1545935, by rfl⟩ : syracuseStep 2061247 = 3091871) B3091871
theorem B37582501 : Blo 499793 37582501 := bstep (se 4 (by rfl) ⟨3523359, by rfl⟩ : syracuseStep 37582501 = 7046719) B7046719
theorem B12680039 : Blo 499793 12680039 := bstep (se 1 (by rfl) ⟨9510029, by rfl⟩ : syracuseStep 12680039 = 19020059) B19020059
theorem B753359 : Blo 499793 753359 := bstep (se 1 (by rfl) ⟨565019, by rfl⟩ : syracuseStep 753359 = 1130039) B1130039
theorem B1605395 : Blo 499793 1605395 := bstep (se 1 (by rfl) ⟨1204046, by rfl⟩ : syracuseStep 1605395 = 2408093) B2408093
theorem B4883615 : Blo 499793 4883615 := bstep (se 1 (by rfl) ⟨3662711, by rfl⟩ : syracuseStep 4883615 = 7325423) B7325423
theorem B3441851 : Blo 499793 3441851 := bstep (se 1 (by rfl) ⟨2581388, by rfl⟩ : syracuseStep 3441851 = 5162777) B5162777
theorem B754943 : Blo 499793 754943 := bstep (se 1 (by rfl) ⟨566207, by rfl⟩ : syracuseStep 754943 = 1132415) B1132415
theorem B49679345 : Blo 499793 49679345 := bstep (se 2 (by rfl) ⟨18629754, by rfl⟩ : syracuseStep 49679345 = 37259509) B37259509
theorem B954011 : Blo 499793 954011 := bstep (se 1 (by rfl) ⟨715508, by rfl⟩ : syracuseStep 954011 = 1431017) B1431017
theorem B5444333 : Blo 499793 5444333 := bstep (se 3 (by rfl) ⟨1020812, by rfl⟩ : syracuseStep 5444333 = 2041625) B2041625
theorem B856955 : Blo 499793 856955 := bstep (se 1 (by rfl) ⟨642716, by rfl⟩ : syracuseStep 856955 = 1285433) B1285433
theorem B4069597 : Blo 499793 4069597 := bstep (se 3 (by rfl) ⟨763049, by rfl⟩ : syracuseStep 4069597 = 1526099) B1526099
theorem B50110001 : Blo 499793 50110001 := bstep (se 2 (by rfl) ⟨18791250, by rfl⟩ : syracuseStep 50110001 = 37582501) B37582501
theorem B20553871 : Blo 499793 20553871 := bstep (se 1 (by rfl) ⟨15415403, by rfl⟩ : syracuseStep 20553871 = 30830807) B30830807
theorem B7742185 : Blo 499793 7742185 := bstep (se 2 (by rfl) ⟨2903319, by rfl⟩ : syracuseStep 7742185 = 5806639) B5806639
theorem B502239 : Blo 499793 502239 := bstep (se 1 (by rfl) ⟨376679, by rfl⟩ : syracuseStep 502239 = 753359) B753359
theorem B1125287 : Blo 499793 1125287 := bstep (se 1 (by rfl) ⟨843965, by rfl⟩ : syracuseStep 1125287 = 1687931) B1687931
theorem B503015 : Blo 499793 503015 := bstep (se 1 (by rfl) ⟨377261, by rfl⟩ : syracuseStep 503015 = 754523) B754523
theorem B503527 : Blo 499793 503527 := bstep (se 1 (by rfl) ⟨377645, by rfl⟩ : syracuseStep 503527 = 755291) B755291
theorem B503643 : Blo 499793 503643 := bstep (se 1 (by rfl) ⟨377732, by rfl⟩ : syracuseStep 503643 = 755465) B755465
theorem B2864105 : Blo 499793 2864105 := bstep (se 2 (by rfl) ⟨1074039, by rfl⟩ : syracuseStep 2864105 = 2148079) B2148079
theorem B23083055 : Blo 499793 23083055 := bstep (se 1 (by rfl) ⟨17312291, by rfl⟩ : syracuseStep 23083055 = 34624583) B34624583
theorem B9259123 : Blo 499793 9259123 := bstep (se 1 (by rfl) ⟨6944342, by rfl⟩ : syracuseStep 9259123 = 13888685) B13888685
theorem B1132703 : Blo 499793 1132703 := bstep (se 1 (by rfl) ⟨849527, by rfl⟩ : syracuseStep 1132703 = 1699055) B1699055
theorem B2740331 : Blo 499793 2740331 := bstep (se 1 (by rfl) ⟨2055248, by rfl⟩ : syracuseStep 2740331 = 4110497) B4110497
theorem B1070263 : Blo 499793 1070263 := bstep (se 1 (by rfl) ⟨802697, by rfl⟩ : syracuseStep 1070263 = 1605395) B1605395
theorem B1430959 : Blo 499793 1430959 := bstep (se 1 (by rfl) ⟨1073219, by rfl⟩ : syracuseStep 1430959 = 2146439) B2146439
theorem B31351303 : Blo 499793 31351303 := bstep (se 1 (by rfl) ⟨23513477, by rfl⟩ : syracuseStep 31351303 = 47026955) B47026955
theorem B844735 : Blo 499793 844735 := bstep (se 1 (by rfl) ⟨633551, by rfl⟩ : syracuseStep 844735 = 1267103) B1267103
theorem B3433967 : Blo 499793 3433967 := bstep (se 1 (by rfl) ⟨2575475, by rfl⟩ : syracuseStep 3433967 = 5150951) B5150951
theorem B847111 : Blo 499793 847111 := bstep (se 1 (by rfl) ⟨635333, by rfl⟩ : syracuseStep 847111 = 1270667) B1270667
theorem B2748329 : Blo 499793 2748329 := bstep (se 2 (by rfl) ⟨1030623, by rfl⟩ : syracuseStep 2748329 = 2061247) B2061247
theorem B1209343 : Blo 499793 1209343 := bstep (se 1 (by rfl) ⟨907007, by rfl⟩ : syracuseStep 1209343 = 1814015) B1814015
theorem B8453359 : Blo 499793 8453359 := bstep (se 1 (by rfl) ⟨6340019, by rfl⟩ : syracuseStep 8453359 = 12680039) B12680039
theorem B2294567 : Blo 499793 2294567 := bstep (se 1 (by rfl) ⟨1720925, by rfl⟩ : syracuseStep 2294567 = 3441851) B3441851
theorem B755135 : Blo 499793 755135 := bstep (se 1 (by rfl) ⟨566351, by rfl⟩ : syracuseStep 755135 = 1132703) B1132703
theorem B41291653 : Blo 499793 41291653 := bstep (se 4 (by rfl) ⟨3871092, by rfl⟩ : syracuseStep 41291653 = 7742185) B7742185
theorem B5708069 : Blo 499793 5708069 := bstep (se 4 (by rfl) ⟨535131, by rfl⟩ : syracuseStep 5708069 = 1070263) B1070263
theorem B1612457 : Blo 499793 1612457 := bstep (se 2 (by rfl) ⟨604671, by rfl⟩ : syracuseStep 1612457 = 1209343) B1209343
theorem B1907945 : Blo 499793 1907945 := bstep (se 2 (by rfl) ⟨715479, by rfl⟩ : syracuseStep 1907945 = 1430959) B1430959
theorem B1909403 : Blo 499793 1909403 := bstep (se 1 (by rfl) ⟨1432052, by rfl⟩ : syracuseStep 1909403 = 2864105) B2864105
theorem B27405161 : Blo 499793 27405161 := bstep (se 2 (by rfl) ⟨10276935, by rfl⟩ : syracuseStep 27405161 = 20553871) B20553871
theorem B3255743 : Blo 499793 3255743 := bstep (se 1 (by rfl) ⟨2441807, by rfl⟩ : syracuseStep 3255743 = 4883615) B4883615
theorem B503295 : Blo 499793 503295 := bstep (se 1 (by rfl) ⟨377471, by rfl⟩ : syracuseStep 503295 = 754943) B754943
theorem B1126313 : Blo 499793 1126313 := bstep (se 2 (by rfl) ⟨422367, by rfl⟩ : syracuseStep 1126313 = 844735) B844735
theorem B636007 : Blo 499793 636007 := bstep (se 1 (by rfl) ⟨477005, by rfl⟩ : syracuseStep 636007 = 954011) B954011
theorem B571303 : Blo 499793 571303 := bstep (se 1 (by rfl) ⟨428477, by rfl⟩ : syracuseStep 571303 = 856955) B856955
theorem B1129481 : Blo 499793 1129481 := bstep (se 2 (by rfl) ⟨423555, by rfl⟩ : syracuseStep 1129481 = 847111) B847111
theorem B33406667 : Blo 499793 33406667 := bstep (se 1 (by rfl) ⟨25055000, by rfl⟩ : syracuseStep 33406667 = 50110001) B50110001
theorem B5426129 : Blo 499793 5426129 := bstep (se 2 (by rfl) ⟨2034798, by rfl⟩ : syracuseStep 5426129 = 4069597) B4069597
theorem B15388703 : Blo 499793 15388703 := bstep (se 1 (by rfl) ⟨11541527, by rfl⟩ : syracuseStep 15388703 = 23083055) B23083055
theorem B33119563 : Blo 499793 33119563 := bstep (se 1 (by rfl) ⟨24839672, by rfl⟩ : syracuseStep 33119563 = 49679345) B49679345
theorem B167206949 : Blo 499793 167206949 := bstep (se 4 (by rfl) ⟨15675651, by rfl⟩ : syracuseStep 167206949 = 31351303) B31351303
theorem B1826887 : Blo 499793 1826887 := bstep (se 1 (by rfl) ⟨1370165, by rfl⟩ : syracuseStep 1826887 = 2740331) B2740331
theorem B12345497 : Blo 499793 12345497 := bstep (se 2 (by rfl) ⟨4629561, by rfl⟩ : syracuseStep 12345497 = 9259123) B9259123
theorem B3629555 : Blo 499793 3629555 := bstep (se 1 (by rfl) ⟨2722166, by rfl⟩ : syracuseStep 3629555 = 5444333) B5444333
theorem B2289311 : Blo 499793 2289311 := bstep (se 1 (by rfl) ⟨1716983, by rfl⟩ : syracuseStep 2289311 = 3433967) B3433967
theorem B750191 : Blo 499793 750191 := bstep (se 1 (by rfl) ⟨562643, by rfl⟩ : syracuseStep 750191 = 1125287) B1125287
theorem B1832219 : Blo 499793 1832219 := bstep (se 1 (by rfl) ⟨1374164, by rfl⟩ : syracuseStep 1832219 = 2748329) B2748329
theorem B11271145 : Blo 499793 11271145 := bstep (se 2 (by rfl) ⟨4226679, by rfl⟩ : syracuseStep 11271145 = 8453359) B8453359
theorem B10259135 : Blo 499793 10259135 := bstep (se 1 (by rfl) ⟨7694351, by rfl⟩ : syracuseStep 10259135 = 15388703) B15388703
theorem B3805379 : Blo 499793 3805379 := bstep (se 1 (by rfl) ⟨2854034, by rfl⟩ : syracuseStep 3805379 = 5708069) B5708069
theorem B55055537 : Blo 499793 55055537 := bstep (se 2 (by rfl) ⟨20645826, by rfl⟩ : syracuseStep 55055537 = 41291653) B41291653
theorem B8230331 : Blo 499793 8230331 := bstep (se 1 (by rfl) ⟨6172748, by rfl⟩ : syracuseStep 8230331 = 12345497) B12345497
theorem B2170495 : Blo 499793 2170495 := bstep (se 1 (by rfl) ⟨1627871, by rfl⟩ : syracuseStep 2170495 = 3255743) B3255743
theorem B761737 : Blo 499793 761737 := bstep (se 2 (by rfl) ⟨285651, by rfl⟩ : syracuseStep 761737 = 571303) B571303
theorem B500127 : Blo 499793 500127 := bstep (se 1 (by rfl) ⟨375095, by rfl⟩ : syracuseStep 500127 = 750191) B750191
theorem B1221479 : Blo 499793 1221479 := bstep (se 1 (by rfl) ⟨916109, by rfl⟩ : syracuseStep 1221479 = 1832219) B1832219
theorem B2435849 : Blo 499793 2435849 := bstep (se 2 (by rfl) ⟨913443, by rfl⟩ : syracuseStep 2435849 = 1826887) B1826887
theorem B503423 : Blo 499793 503423 := bstep (se 1 (by rfl) ⟨377567, by rfl⟩ : syracuseStep 503423 = 755135) B755135
theorem B3617419 : Blo 499793 3617419 := bstep (se 1 (by rfl) ⟨2713064, by rfl⟩ : syracuseStep 3617419 = 5426129) B5426129
theorem B18270107 : Blo 499793 18270107 := bstep (se 1 (by rfl) ⟨13702580, by rfl⟩ : syracuseStep 18270107 = 27405161) B27405161
theorem B1526207 : Blo 499793 1526207 := bstep (se 1 (by rfl) ⟨1144655, by rfl⟩ : syracuseStep 1526207 = 2289311) B2289311
theorem B15028193 : Blo 499793 15028193 := bstep (se 2 (by rfl) ⟨5635572, by rfl⟩ : syracuseStep 15028193 = 11271145) B11271145
theorem B44159417 : Blo 499793 44159417 := bstep (se 2 (by rfl) ⟨16559781, by rfl⟩ : syracuseStep 44159417 = 33119563) B33119563
theorem B22271111 : Blo 499793 22271111 := bstep (se 1 (by rfl) ⟨16703333, by rfl⟩ : syracuseStep 22271111 = 33406667) B33406667
theorem B1529711 : Blo 499793 1529711 := bstep (se 1 (by rfl) ⟨1147283, by rfl⟩ : syracuseStep 1529711 = 2294567) B2294567
theorem B1074971 : Blo 499793 1074971 := bstep (se 1 (by rfl) ⟨806228, by rfl⟩ : syracuseStep 1074971 = 1612457) B1612457
theorem B1271963 : Blo 499793 1271963 := bstep (se 1 (by rfl) ⟨953972, by rfl⟩ : syracuseStep 1271963 = 1907945) B1907945
theorem B111471299 : Blo 499793 111471299 := bstep (se 1 (by rfl) ⟨83603474, by rfl⟩ : syracuseStep 111471299 = 167206949) B167206949
theorem B2419703 : Blo 499793 2419703 := bstep (se 1 (by rfl) ⟨1814777, by rfl⟩ : syracuseStep 2419703 = 3629555) B3629555
theorem B1272935 : Blo 499793 1272935 := bstep (se 1 (by rfl) ⟨954701, by rfl⟩ : syracuseStep 1272935 = 1909403) B1909403
theorem B848009 : Blo 499793 848009 := bstep (se 2 (by rfl) ⟨318003, by rfl⟩ : syracuseStep 848009 = 636007) B636007
theorem B750875 : Blo 499793 750875 := bstep (se 1 (by rfl) ⟨563156, by rfl⟩ : syracuseStep 750875 = 1126313) B1126313
theorem B752987 : Blo 499793 752987 := bstep (se 1 (by rfl) ⟨564740, by rfl⟩ : syracuseStep 752987 = 1129481) B1129481
theorem B14847407 : Blo 499793 14847407 := bstep (se 1 (by rfl) ⟨11135555, by rfl⟩ : syracuseStep 14847407 = 22271111) B22271111
theorem B36703691 : Blo 499793 36703691 := bstep (se 1 (by rfl) ⟨27527768, by rfl⟩ : syracuseStep 36703691 = 55055537) B55055537
theorem B1019807 : Blo 499793 1019807 := bstep (se 1 (by rfl) ⟨764855, by rfl⟩ : syracuseStep 1019807 = 1529711) B1529711
theorem B4823225 : Blo 499793 4823225 := bstep (se 2 (by rfl) ⟨1808709, by rfl⟩ : syracuseStep 4823225 = 3617419) B3617419
theorem B4069885 : Blo 499793 4069885 := bstep (se 3 (by rfl) ⟨763103, by rfl⟩ : syracuseStep 4069885 = 1526207) B1526207
theorem B1613135 : Blo 499793 1613135 := bstep (se 1 (by rfl) ⟨1209851, by rfl⟩ : syracuseStep 1613135 = 2419703) B2419703
theorem B565339 : Blo 499793 565339 := bstep (se 1 (by rfl) ⟨424004, by rfl⟩ : syracuseStep 565339 = 848009) B848009
theorem B11575973 : Blo 499793 11575973 := bstep (se 4 (by rfl) ⟨1085247, by rfl⟩ : syracuseStep 11575973 = 2170495) B2170495
theorem B500583 : Blo 499793 500583 := bstep (se 1 (by rfl) ⟨375437, by rfl⟩ : syracuseStep 500583 = 750875) B750875
theorem B501991 : Blo 499793 501991 := bstep (se 1 (by rfl) ⟨376493, by rfl⟩ : syracuseStep 501991 = 752987) B752987
theorem B2536919 : Blo 499793 2536919 := bstep (se 1 (by rfl) ⟨1902689, by rfl⟩ : syracuseStep 2536919 = 3805379) B3805379
theorem B29439611 : Blo 499793 29439611 := bstep (se 1 (by rfl) ⟨22079708, by rfl⟩ : syracuseStep 29439611 = 44159417) B44159417
theorem B5486887 : Blo 499793 5486887 := bstep (se 1 (by rfl) ⟨4115165, by rfl⟩ : syracuseStep 5486887 = 8230331) B8230331
theorem B2866589 : Blo 499793 2866589 := bstep (se 3 (by rfl) ⟨537485, by rfl⟩ : syracuseStep 2866589 = 1074971) B1074971
theorem B1623899 : Blo 499793 1623899 := bstep (se 1 (by rfl) ⟨1217924, by rfl⟩ : syracuseStep 1623899 = 2435849) B2435849
theorem B12180071 : Blo 499793 12180071 := bstep (se 1 (by rfl) ⟨9135053, by rfl⟩ : syracuseStep 12180071 = 18270107) B18270107
theorem B6839423 : Blo 499793 6839423 := bstep (se 1 (by rfl) ⟨5129567, by rfl⟩ : syracuseStep 6839423 = 10259135) B10259135
theorem B814319 : Blo 499793 814319 := bstep (se 1 (by rfl) ⟨610739, by rfl⟩ : syracuseStep 814319 = 1221479) B1221479
theorem B847975 : Blo 499793 847975 := bstep (se 1 (by rfl) ⟨635981, by rfl⟩ : syracuseStep 847975 = 1271963) B1271963
theorem B74314199 : Blo 499793 74314199 := bstep (se 1 (by rfl) ⟨55735649, by rfl⟩ : syracuseStep 74314199 = 111471299) B111471299
theorem B848623 : Blo 499793 848623 := bstep (se 1 (by rfl) ⟨636467, by rfl⟩ : syracuseStep 848623 = 1272935) B1272935
theorem B1015649 : Blo 499793 1015649 := bstep (se 2 (by rfl) ⟨380868, by rfl⟩ : syracuseStep 1015649 = 761737) B761737
theorem B40075181 : Blo 499793 40075181 := bstep (se 3 (by rfl) ⟨7514096, by rfl⟩ : syracuseStep 40075181 = 15028193) B15028193
theorem B753785 : Blo 499793 753785 := bstep (se 2 (by rfl) ⟨282669, by rfl⟩ : syracuseStep 753785 = 565339) B565339
theorem B9898271 : Blo 499793 9898271 := bstep (se 1 (by rfl) ⟨7423703, by rfl⟩ : syracuseStep 9898271 = 14847407) B14847407
theorem B3215483 : Blo 499793 3215483 := bstep (se 1 (by rfl) ⟨2411612, by rfl⟩ : syracuseStep 3215483 = 4823225) B4823225
theorem B4559615 : Blo 499793 4559615 := bstep (se 1 (by rfl) ⟨3419711, by rfl⟩ : syracuseStep 4559615 = 6839423) B6839423
theorem B4330397 : Blo 499793 4330397 := bstep (se 3 (by rfl) ⟨811949, by rfl⟩ : syracuseStep 4330397 = 1623899) B1623899
theorem B7315849 : Blo 499793 7315849 := bstep (se 2 (by rfl) ⟨2743443, by rfl⟩ : syracuseStep 7315849 = 5486887) B5486887
theorem B4301693 : Blo 499793 4301693 := bstep (se 3 (by rfl) ⟨806567, by rfl⟩ : syracuseStep 4301693 = 1613135) B1613135
theorem B1911059 : Blo 499793 1911059 := bstep (se 1 (by rfl) ⟨1433294, by rfl⟩ : syracuseStep 1911059 = 2866589) B2866589
theorem B26716787 : Blo 499793 26716787 := bstep (se 1 (by rfl) ⟨20037590, by rfl⟩ : syracuseStep 26716787 = 40075181) B40075181
theorem B1130633 : Blo 499793 1130633 := bstep (se 2 (by rfl) ⟨423987, by rfl⟩ : syracuseStep 1130633 = 847975) B847975
theorem B7717315 : Blo 499793 7717315 := bstep (se 1 (by rfl) ⟨5787986, by rfl⟩ : syracuseStep 7717315 = 11575973) B11575973
theorem B1131497 : Blo 499793 1131497 := bstep (se 2 (by rfl) ⟨424311, by rfl⟩ : syracuseStep 1131497 = 848623) B848623
theorem B542879 : Blo 499793 542879 := bstep (se 1 (by rfl) ⟨407159, by rfl⟩ : syracuseStep 542879 = 814319) B814319
theorem B5426513 : Blo 499793 5426513 := bstep (se 2 (by rfl) ⟨2034942, by rfl⟩ : syracuseStep 5426513 = 4069885) B4069885
theorem B1691279 : Blo 499793 1691279 := bstep (se 1 (by rfl) ⟨1268459, by rfl⟩ : syracuseStep 1691279 = 2536919) B2536919
theorem B677099 : Blo 499793 677099 := bstep (se 1 (by rfl) ⟨507824, by rfl⟩ : syracuseStep 677099 = 1015649) B1015649
theorem B24469127 : Blo 499793 24469127 := bstep (se 1 (by rfl) ⟨18351845, by rfl⟩ : syracuseStep 24469127 = 36703691) B36703691
theorem B679871 : Blo 499793 679871 := bstep (se 1 (by rfl) ⟨509903, by rfl⟩ : syracuseStep 679871 = 1019807) B1019807
theorem B8120047 : Blo 499793 8120047 := bstep (se 1 (by rfl) ⟨6090035, by rfl⟩ : syracuseStep 8120047 = 12180071) B12180071
theorem B49542799 : Blo 499793 49542799 := bstep (se 1 (by rfl) ⟨37157099, by rfl⟩ : syracuseStep 49542799 = 74314199) B74314199
theorem B19626407 : Blo 499793 19626407 := bstep (se 1 (by rfl) ⟨14719805, by rfl⟩ : syracuseStep 19626407 = 29439611) B29439611
theorem B753755 : Blo 499793 753755 := bstep (se 1 (by rfl) ⟨565316, by rfl⟩ : syracuseStep 753755 = 1130633) B1130633
theorem B10289753 : Blo 499793 10289753 := bstep (se 2 (by rfl) ⟨3858657, by rfl⟩ : syracuseStep 10289753 = 7717315) B7717315
theorem B754331 : Blo 499793 754331 := bstep (se 1 (by rfl) ⟨565748, by rfl⟩ : syracuseStep 754331 = 1131497) B1131497
theorem B2886931 : Blo 499793 2886931 := bstep (se 1 (by rfl) ⟨2165198, by rfl⟩ : syracuseStep 2886931 = 4330397) B4330397
theorem B1805597 : Blo 499793 1805597 := bstep (se 3 (by rfl) ⟨338549, by rfl⟩ : syracuseStep 1805597 = 677099) B677099
theorem B13084271 : Blo 499793 13084271 := bstep (se 1 (by rfl) ⟨9813203, by rfl⟩ : syracuseStep 13084271 = 19626407) B19626407
theorem B1812989 : Blo 499793 1812989 := bstep (se 3 (by rfl) ⟨339935, by rfl⟩ : syracuseStep 1812989 = 679871) B679871
theorem B502523 : Blo 499793 502523 := bstep (se 1 (by rfl) ⟨376892, by rfl⟩ : syracuseStep 502523 = 753785) B753785
theorem B6598847 : Blo 499793 6598847 := bstep (se 1 (by rfl) ⟨4949135, by rfl⟩ : syracuseStep 6598847 = 9898271) B9898271
theorem B3617675 : Blo 499793 3617675 := bstep (se 1 (by rfl) ⟨2713256, by rfl⟩ : syracuseStep 3617675 = 5426513) B5426513
theorem B10826729 : Blo 499793 10826729 := bstep (se 2 (by rfl) ⟨4060023, by rfl⟩ : syracuseStep 10826729 = 8120047) B8120047
theorem B1127519 : Blo 499793 1127519 := bstep (se 1 (by rfl) ⟨845639, by rfl⟩ : syracuseStep 1127519 = 1691279) B1691279
theorem B2143655 : Blo 499793 2143655 := bstep (se 1 (by rfl) ⟨1607741, by rfl⟩ : syracuseStep 2143655 = 3215483) B3215483
theorem B2867795 : Blo 499793 2867795 := bstep (se 1 (by rfl) ⟨2150846, by rfl⟩ : syracuseStep 2867795 = 4301693) B4301693
theorem B17811191 : Blo 499793 17811191 := bstep (se 1 (by rfl) ⟨13358393, by rfl⟩ : syracuseStep 17811191 = 26716787) B26716787
theorem B9754465 : Blo 499793 9754465 := bstep (se 2 (by rfl) ⟨3657924, by rfl⟩ : syracuseStep 9754465 = 7315849) B7315849
theorem B5790709 : Blo 499793 5790709 := bstep (se 5 (by rfl) ⟨271439, by rfl⟩ : syracuseStep 5790709 = 542879) B542879
theorem B3039743 : Blo 499793 3039743 := bstep (se 1 (by rfl) ⟨2279807, by rfl⟩ : syracuseStep 3039743 = 4559615) B4559615
theorem B16312751 : Blo 499793 16312751 := bstep (se 1 (by rfl) ⟨12234563, by rfl⟩ : syracuseStep 16312751 = 24469127) B24469127
theorem B1274039 : Blo 499793 1274039 := bstep (se 1 (by rfl) ⟨955529, by rfl⟩ : syracuseStep 1274039 = 1911059) B1911059
theorem B66057065 : Blo 499793 66057065 := bstep (se 2 (by rfl) ⟨24771399, by rfl⟩ : syracuseStep 66057065 = 49542799) B49542799
theorem B8722847 : Blo 499793 8722847 := bstep (se 1 (by rfl) ⟨6542135, by rfl⟩ : syracuseStep 8722847 = 13084271) B13084271
theorem B4399231 : Blo 499793 4399231 := bstep (se 1 (by rfl) ⟨3299423, by rfl⟩ : syracuseStep 4399231 = 6598847) B6598847
theorem B7217819 : Blo 499793 7217819 := bstep (se 1 (by rfl) ⟨5413364, by rfl⟩ : syracuseStep 7217819 = 10826729) B10826729
theorem B502503 : Blo 499793 502503 := bstep (se 1 (by rfl) ⟨376877, by rfl⟩ : syracuseStep 502503 = 753755) B753755
theorem B1911863 : Blo 499793 1911863 := bstep (se 1 (by rfl) ⟨1433897, by rfl⟩ : syracuseStep 1911863 = 2867795) B2867795
theorem B6859835 : Blo 499793 6859835 := bstep (se 1 (by rfl) ⟨5144876, by rfl⟩ : syracuseStep 6859835 = 10289753) B10289753
theorem B502887 : Blo 499793 502887 := bstep (se 1 (by rfl) ⟨377165, by rfl⟩ : syracuseStep 502887 = 754331) B754331
theorem B11874127 : Blo 499793 11874127 := bstep (se 1 (by rfl) ⟨8905595, by rfl⟩ : syracuseStep 11874127 = 17811191) B17811191
theorem B3849241 : Blo 499793 3849241 := bstep (se 2 (by rfl) ⟨1443465, by rfl⟩ : syracuseStep 3849241 = 2886931) B2886931
theorem B30883781 : Blo 499793 30883781 := bstep (se 4 (by rfl) ⟨2895354, by rfl⟩ : syracuseStep 30883781 = 5790709) B5790709
theorem B4834637 : Blo 499793 4834637 := bstep (se 3 (by rfl) ⟨906494, by rfl⟩ : syracuseStep 4834637 = 1812989) B1812989
theorem B2411783 : Blo 499793 2411783 := bstep (se 1 (by rfl) ⟨1808837, by rfl⟩ : syracuseStep 2411783 = 3617675) B3617675
theorem B1429103 : Blo 499793 1429103 := bstep (se 1 (by rfl) ⟨1071827, by rfl⟩ : syracuseStep 1429103 = 2143655) B2143655
theorem B1203731 : Blo 499793 1203731 := bstep (se 1 (by rfl) ⟨902798, by rfl⟩ : syracuseStep 1203731 = 1805597) B1805597
theorem B2026495 : Blo 499793 2026495 := bstep (se 1 (by rfl) ⟨1519871, by rfl⟩ : syracuseStep 2026495 = 3039743) B3039743
theorem B10875167 : Blo 499793 10875167 := bstep (se 1 (by rfl) ⟨8156375, by rfl⟩ : syracuseStep 10875167 = 16312751) B16312751
theorem B13005953 : Blo 499793 13005953 := bstep (se 2 (by rfl) ⟨4877232, by rfl⟩ : syracuseStep 13005953 = 9754465) B9754465
theorem B849359 : Blo 499793 849359 := bstep (se 1 (by rfl) ⟨637019, by rfl⟩ : syracuseStep 849359 = 1274039) B1274039
theorem B44038043 : Blo 499793 44038043 := bstep (se 1 (by rfl) ⟨33028532, by rfl⟩ : syracuseStep 44038043 = 66057065) B66057065
theorem B751679 : Blo 499793 751679 := bstep (se 1 (by rfl) ⟨563759, by rfl⟩ : syracuseStep 751679 = 1127519) B1127519
theorem B5865641 : Blo 499793 5865641 := bstep (se 2 (by rfl) ⟨2199615, by rfl⟩ : syracuseStep 5865641 = 4399231) B4399231
theorem B1607855 : Blo 499793 1607855 := bstep (se 1 (by rfl) ⟨1205891, by rfl⟩ : syracuseStep 1607855 = 2411783) B2411783
theorem B952735 : Blo 499793 952735 := bstep (se 1 (by rfl) ⟨714551, by rfl⟩ : syracuseStep 952735 = 1429103) B1429103
theorem B15832169 : Blo 499793 15832169 := bstep (se 2 (by rfl) ⟨5937063, by rfl⟩ : syracuseStep 15832169 = 11874127) B11874127
theorem B7250111 : Blo 499793 7250111 := bstep (se 1 (by rfl) ⟨5437583, by rfl⟩ : syracuseStep 7250111 = 10875167) B10875167
theorem B566239 : Blo 499793 566239 := bstep (se 1 (by rfl) ⟨424679, by rfl⟩ : syracuseStep 566239 = 849359) B849359
theorem B501119 : Blo 499793 501119 := bstep (se 1 (by rfl) ⟨375839, by rfl⟩ : syracuseStep 501119 = 751679) B751679
theorem B82356749 : Blo 499793 82356749 := bstep (se 3 (by rfl) ⟨15441890, by rfl⟩ : syracuseStep 82356749 = 30883781) B30883781
theorem B3223091 : Blo 499793 3223091 := bstep (se 1 (by rfl) ⟨2417318, by rfl⟩ : syracuseStep 3223091 = 4834637) B4834637
theorem B2701993 : Blo 499793 2701993 := bstep (se 2 (by rfl) ⟨1013247, by rfl⟩ : syracuseStep 2701993 = 2026495) B2026495
theorem B802487 : Blo 499793 802487 := bstep (se 1 (by rfl) ⟨601865, by rfl⟩ : syracuseStep 802487 = 1203731) B1203731
theorem B4573223 : Blo 499793 4573223 := bstep (se 1 (by rfl) ⟨3429917, by rfl⟩ : syracuseStep 4573223 = 6859835) B6859835
theorem B8670635 : Blo 499793 8670635 := bstep (se 1 (by rfl) ⟨6502976, by rfl⟩ : syracuseStep 8670635 = 13005953) B13005953
theorem B5132321 : Blo 499793 5132321 := bstep (se 2 (by rfl) ⟨1924620, by rfl⟩ : syracuseStep 5132321 = 3849241) B3849241
theorem B4811879 : Blo 499793 4811879 := bstep (se 1 (by rfl) ⟨3608909, by rfl⟩ : syracuseStep 4811879 = 7217819) B7217819
theorem B23260925 : Blo 499793 23260925 := bstep (se 3 (by rfl) ⟨4361423, by rfl⟩ : syracuseStep 23260925 = 8722847) B8722847
theorem B1274575 : Blo 499793 1274575 := bstep (se 1 (by rfl) ⟨955931, by rfl⟩ : syracuseStep 1274575 = 1911863) B1911863
theorem B29358695 : Blo 499793 29358695 := bstep (se 1 (by rfl) ⟨22019021, by rfl⟩ : syracuseStep 29358695 = 44038043) B44038043
theorem B754985 : Blo 499793 754985 := bstep (se 2 (by rfl) ⟨283119, by rfl⟩ : syracuseStep 754985 = 566239) B566239
theorem B3048815 : Blo 499793 3048815 := bstep (se 1 (by rfl) ⟨2286611, by rfl⟩ : syracuseStep 3048815 = 4573223) B4573223
theorem B10554779 : Blo 499793 10554779 := bstep (se 1 (by rfl) ⟨7916084, by rfl⟩ : syracuseStep 10554779 = 15832169) B15832169
theorem B15507283 : Blo 499793 15507283 := bstep (se 1 (by rfl) ⟨11630462, by rfl⟩ : syracuseStep 15507283 = 23260925) B23260925
theorem B8594909 : Blo 499793 8594909 := bstep (se 3 (by rfl) ⟨1611545, by rfl⟩ : syracuseStep 8594909 = 3223091) B3223091
theorem B19572463 : Blo 499793 19572463 := bstep (se 1 (by rfl) ⟨14679347, by rfl⟩ : syracuseStep 19572463 = 29358695) B29358695
theorem B2139965 : Blo 499793 2139965 := bstep (se 3 (by rfl) ⟨401243, by rfl⟩ : syracuseStep 2139965 = 802487) B802487
theorem B3910427 : Blo 499793 3910427 := bstep (se 1 (by rfl) ⟨2932820, by rfl⟩ : syracuseStep 3910427 = 5865641) B5865641
theorem B5780423 : Blo 499793 5780423 := bstep (se 1 (by rfl) ⟨4335317, by rfl⟩ : syracuseStep 5780423 = 8670635) B8670635
theorem B3421547 : Blo 499793 3421547 := bstep (se 1 (by rfl) ⟨2566160, by rfl⟩ : syracuseStep 3421547 = 5132321) B5132321
theorem B4833407 : Blo 499793 4833407 := bstep (se 1 (by rfl) ⟨3625055, by rfl⟩ : syracuseStep 4833407 = 7250111) B7250111
theorem B54904499 : Blo 499793 54904499 := bstep (se 1 (by rfl) ⟨41178374, by rfl⟩ : syracuseStep 54904499 = 82356749) B82356749
theorem B1270313 : Blo 499793 1270313 := bstep (se 2 (by rfl) ⟨476367, by rfl⟩ : syracuseStep 1270313 = 952735) B952735
theorem B4287613 : Blo 499793 4287613 := bstep (se 3 (by rfl) ⟨803927, by rfl⟩ : syracuseStep 4287613 = 1607855) B1607855
theorem B1699433 : Blo 499793 1699433 := bstep (se 2 (by rfl) ⟨637287, by rfl⟩ : syracuseStep 1699433 = 1274575) B1274575
theorem B3207919 : Blo 499793 3207919 := bstep (se 1 (by rfl) ⟨2405939, by rfl⟩ : syracuseStep 3207919 = 4811879) B4811879
theorem B3602657 : Blo 499793 3602657 := bstep (se 2 (by rfl) ⟨1350996, by rfl⟩ : syracuseStep 3602657 = 2701993) B2701993
theorem B2032543 : Blo 499793 2032543 := bstep (se 1 (by rfl) ⟨1524407, by rfl⟩ : syracuseStep 2032543 = 3048815) B3048815
theorem B36602999 : Blo 499793 36602999 := bstep (se 1 (by rfl) ⟨27452249, by rfl⟩ : syracuseStep 36602999 = 54904499) B54904499
theorem B2401771 : Blo 499793 2401771 := bstep (se 1 (by rfl) ⟨1801328, by rfl⟩ : syracuseStep 2401771 = 3602657) B3602657
theorem B3222271 : Blo 499793 3222271 := bstep (se 1 (by rfl) ⟨2416703, by rfl⟩ : syracuseStep 3222271 = 4833407) B4833407
theorem B503323 : Blo 499793 503323 := bstep (se 1 (by rfl) ⟨377492, by rfl⟩ : syracuseStep 503323 = 754985) B754985
theorem B26096617 : Blo 499793 26096617 := bstep (se 2 (by rfl) ⟨9786231, by rfl⟩ : syracuseStep 26096617 = 19572463) B19572463
theorem B5716817 : Blo 499793 5716817 := bstep (se 2 (by rfl) ⟨2143806, by rfl⟩ : syracuseStep 5716817 = 4287613) B4287613
theorem B4277225 : Blo 499793 4277225 := bstep (se 2 (by rfl) ⟨1603959, by rfl⟩ : syracuseStep 4277225 = 3207919) B3207919
theorem B1426643 : Blo 499793 1426643 := bstep (se 1 (by rfl) ⟨1069982, by rfl⟩ : syracuseStep 1426643 = 2139965) B2139965
theorem B2606951 : Blo 499793 2606951 := bstep (se 1 (by rfl) ⟨1955213, by rfl⟩ : syracuseStep 2606951 = 3910427) B3910427
theorem B1132955 : Blo 499793 1132955 := bstep (se 1 (by rfl) ⟨849716, by rfl⟩ : syracuseStep 1132955 = 1699433) B1699433
theorem B3853615 : Blo 499793 3853615 := bstep (se 1 (by rfl) ⟨2890211, by rfl⟩ : syracuseStep 3853615 = 5780423) B5780423
theorem B2281031 : Blo 499793 2281031 := bstep (se 1 (by rfl) ⟨1710773, by rfl⟩ : syracuseStep 2281031 = 3421547) B3421547
theorem B7036519 : Blo 499793 7036519 := bstep (se 1 (by rfl) ⟨5277389, by rfl⟩ : syracuseStep 7036519 = 10554779) B10554779
theorem B846875 : Blo 499793 846875 := bstep (se 1 (by rfl) ⟨635156, by rfl⟩ : syracuseStep 846875 = 1270313) B1270313
theorem B5729939 : Blo 499793 5729939 := bstep (se 1 (by rfl) ⟨4297454, by rfl⟩ : syracuseStep 5729939 = 8594909) B8594909
theorem B20676377 : Blo 499793 20676377 := bstep (se 2 (by rfl) ⟨7753641, by rfl⟩ : syracuseStep 20676377 = 15507283) B15507283
theorem B2851483 : Blo 499793 2851483 := bstep (se 1 (by rfl) ⟨2138612, by rfl⟩ : syracuseStep 2851483 = 4277225) B4277225
theorem B951095 : Blo 499793 951095 := bstep (se 1 (by rfl) ⟨713321, by rfl⟩ : syracuseStep 951095 = 1426643) B1426643
theorem B1737967 : Blo 499793 1737967 := bstep (se 1 (by rfl) ⟨1303475, by rfl⟩ : syracuseStep 1737967 = 2606951) B2606951
theorem B755303 : Blo 499793 755303 := bstep (se 1 (by rfl) ⟨566477, by rfl⟩ : syracuseStep 755303 = 1132955) B1132955
theorem B4296361 : Blo 499793 4296361 := bstep (se 2 (by rfl) ⟨1611135, by rfl⟩ : syracuseStep 4296361 = 3222271) B3222271
theorem B564583 : Blo 499793 564583 := bstep (se 1 (by rfl) ⟨423437, by rfl⟩ : syracuseStep 564583 = 846875) B846875
theorem B3811211 : Blo 499793 3811211 := bstep (se 1 (by rfl) ⟨2858408, by rfl⟩ : syracuseStep 3811211 = 5716817) B5716817
theorem B9382025 : Blo 499793 9382025 := bstep (se 2 (by rfl) ⟨3518259, by rfl⟩ : syracuseStep 9382025 = 7036519) B7036519
theorem B1520687 : Blo 499793 1520687 := bstep (se 1 (by rfl) ⟨1140515, by rfl⟩ : syracuseStep 1520687 = 2281031) B2281031
theorem B3819959 : Blo 499793 3819959 := bstep (se 1 (by rfl) ⟨2864969, by rfl⟩ : syracuseStep 3819959 = 5729939) B5729939
theorem B13784251 : Blo 499793 13784251 := bstep (se 1 (by rfl) ⟨10338188, by rfl⟩ : syracuseStep 13784251 = 20676377) B20676377
theorem B24401999 : Blo 499793 24401999 := bstep (se 1 (by rfl) ⟨18301499, by rfl⟩ : syracuseStep 24401999 = 36602999) B36602999
theorem B3202361 : Blo 499793 3202361 := bstep (se 2 (by rfl) ⟨1200885, by rfl⟩ : syracuseStep 3202361 = 2401771) B2401771
theorem B5138153 : Blo 499793 5138153 := bstep (se 2 (by rfl) ⟨1926807, by rfl⟩ : syracuseStep 5138153 = 3853615) B3853615
theorem B10840229 : Blo 499793 10840229 := bstep (se 4 (by rfl) ⟨1016271, by rfl⟩ : syracuseStep 10840229 = 2032543) B2032543
theorem B34795489 : Blo 499793 34795489 := bstep (se 2 (by rfl) ⟨13048308, by rfl⟩ : syracuseStep 34795489 = 26096617) B26096617
theorem B3801977 : Blo 499793 3801977 := bstep (se 2 (by rfl) ⟨1425741, by rfl⟩ : syracuseStep 3801977 = 2851483) B2851483
theorem B2134907 : Blo 499793 2134907 := bstep (se 1 (by rfl) ⟨1601180, by rfl⟩ : syracuseStep 2134907 = 3202361) B3202361
theorem B634063 : Blo 499793 634063 := bstep (se 1 (by rfl) ⟨475547, by rfl⟩ : syracuseStep 634063 = 951095) B951095
theorem B503535 : Blo 499793 503535 := bstep (se 1 (by rfl) ⟨377651, by rfl⟩ : syracuseStep 503535 = 755303) B755303
theorem B16267999 : Blo 499793 16267999 := bstep (se 1 (by rfl) ⟨12200999, by rfl⟩ : syracuseStep 16267999 = 24401999) B24401999
theorem B25018733 : Blo 499793 25018733 := bstep (se 3 (by rfl) ⟨4691012, by rfl⟩ : syracuseStep 25018733 = 9382025) B9382025
theorem B3425435 : Blo 499793 3425435 := bstep (se 1 (by rfl) ⟨2569076, by rfl⟩ : syracuseStep 3425435 = 5138153) B5138153
theorem B2540807 : Blo 499793 2540807 := bstep (se 1 (by rfl) ⟨1905605, by rfl⟩ : syracuseStep 2540807 = 3811211) B3811211
theorem B7226819 : Blo 499793 7226819 := bstep (se 1 (by rfl) ⟨5420114, by rfl⟩ : syracuseStep 7226819 = 10840229) B10840229
theorem B2546639 : Blo 499793 2546639 := bstep (se 1 (by rfl) ⟨1909979, by rfl⟩ : syracuseStep 2546639 = 3819959) B3819959
theorem B2317289 : Blo 499793 2317289 := bstep (se 2 (by rfl) ⟨868983, by rfl⟩ : syracuseStep 2317289 = 1737967) B1737967
theorem B5728481 : Blo 499793 5728481 := bstep (se 2 (by rfl) ⟨2148180, by rfl⟩ : syracuseStep 5728481 = 4296361) B4296361
theorem B46393985 : Blo 499793 46393985 := bstep (se 2 (by rfl) ⟨17397744, by rfl⟩ : syracuseStep 46393985 = 34795489) B34795489
theorem B18379001 : Blo 499793 18379001 := bstep (se 2 (by rfl) ⟨6892125, by rfl⟩ : syracuseStep 18379001 = 13784251) B13784251
theorem B1013791 : Blo 499793 1013791 := bstep (se 1 (by rfl) ⟨760343, by rfl⟩ : syracuseStep 1013791 = 1520687) B1520687
theorem B752777 : Blo 499793 752777 := bstep (se 2 (by rfl) ⟨282291, by rfl⟩ : syracuseStep 752777 = 564583) B564583
theorem B16679155 : Blo 499793 16679155 := bstep (se 1 (by rfl) ⟨12509366, by rfl⟩ : syracuseStep 16679155 = 25018733) B25018733
theorem B4817879 : Blo 499793 4817879 := bstep (se 1 (by rfl) ⟨3613409, by rfl⟩ : syracuseStep 4817879 = 7226819) B7226819
theorem B1351721 : Blo 499793 1351721 := bstep (se 2 (by rfl) ⟨506895, by rfl⟩ : syracuseStep 1351721 = 1013791) B1013791
theorem B501851 : Blo 499793 501851 := bstep (se 1 (by rfl) ⟨376388, by rfl⟩ : syracuseStep 501851 = 752777) B752777
theorem B2534651 : Blo 499793 2534651 := bstep (se 1 (by rfl) ⟨1900988, by rfl⟩ : syracuseStep 2534651 = 3801977) B3801977
theorem B1423271 : Blo 499793 1423271 := bstep (se 1 (by rfl) ⟨1067453, by rfl⟩ : syracuseStep 1423271 = 2134907) B2134907
theorem B3818987 : Blo 499793 3818987 := bstep (se 1 (by rfl) ⟨2864240, by rfl⟩ : syracuseStep 3818987 = 5728481) B5728481
theorem B123717293 : Blo 499793 123717293 := bstep (se 3 (by rfl) ⟨23196992, by rfl⟩ : syracuseStep 123717293 = 46393985) B46393985
theorem B6179437 : Blo 499793 6179437 := bstep (se 3 (by rfl) ⟨1158644, by rfl⟩ : syracuseStep 6179437 = 2317289) B2317289
theorem B49010669 : Blo 499793 49010669 := bstep (se 3 (by rfl) ⟨9189500, by rfl⟩ : syracuseStep 49010669 = 18379001) B18379001
theorem B2283623 : Blo 499793 2283623 := bstep (se 1 (by rfl) ⟨1712717, by rfl⟩ : syracuseStep 2283623 = 3425435) B3425435
theorem B1693871 : Blo 499793 1693871 := bstep (se 1 (by rfl) ⟨1270403, by rfl⟩ : syracuseStep 1693871 = 2540807) B2540807
theorem B845417 : Blo 499793 845417 := bstep (se 2 (by rfl) ⟨317031, by rfl⟩ : syracuseStep 845417 = 634063) B634063
theorem B1697759 : Blo 499793 1697759 := bstep (se 1 (by rfl) ⟨1273319, by rfl⟩ : syracuseStep 1697759 = 2546639) B2546639
theorem B21690665 : Blo 499793 21690665 := bstep (se 2 (by rfl) ⟨8133999, by rfl⟩ : syracuseStep 21690665 = 16267999) B16267999
theorem B3211919 : Blo 499793 3211919 := bstep (se 1 (by rfl) ⟨2408939, by rfl⟩ : syracuseStep 3211919 = 4817879) B4817879
theorem B82478195 : Blo 499793 82478195 := bstep (se 1 (by rfl) ⟨61858646, by rfl⟩ : syracuseStep 82478195 = 123717293) B123717293
theorem B32673779 : Blo 499793 32673779 := bstep (se 1 (by rfl) ⟨24505334, by rfl⟩ : syracuseStep 32673779 = 49010669) B49010669
theorem B563611 : Blo 499793 563611 := bstep (se 1 (by rfl) ⟨422708, by rfl⟩ : syracuseStep 563611 = 845417) B845417
theorem B14460443 : Blo 499793 14460443 := bstep (se 1 (by rfl) ⟨10845332, by rfl⟩ : syracuseStep 14460443 = 21690665) B21690665
theorem B8239249 : Blo 499793 8239249 := bstep (se 2 (by rfl) ⟨3089718, by rfl⟩ : syracuseStep 8239249 = 6179437) B6179437
theorem B1522415 : Blo 499793 1522415 := bstep (se 1 (by rfl) ⟨1141811, by rfl⟩ : syracuseStep 1522415 = 2283623) B2283623
theorem B1129247 : Blo 499793 1129247 := bstep (se 1 (by rfl) ⟨846935, by rfl⟩ : syracuseStep 1129247 = 1693871) B1693871
theorem B901147 : Blo 499793 901147 := bstep (se 1 (by rfl) ⟨675860, by rfl⟩ : syracuseStep 901147 = 1351721) B1351721
theorem B1131839 : Blo 499793 1131839 := bstep (se 1 (by rfl) ⟨848879, by rfl⟩ : syracuseStep 1131839 = 1697759) B1697759
theorem B1689767 : Blo 499793 1689767 := bstep (se 1 (by rfl) ⟨1267325, by rfl⟩ : syracuseStep 1689767 = 2534651) B2534651
theorem B22238873 : Blo 499793 22238873 := bstep (se 2 (by rfl) ⟨8339577, by rfl⟩ : syracuseStep 22238873 = 16679155) B16679155
theorem B2545991 : Blo 499793 2545991 := bstep (se 1 (by rfl) ⟨1909493, by rfl⟩ : syracuseStep 2545991 = 3818987) B3818987
theorem B948847 : Blo 499793 948847 := bstep (se 1 (by rfl) ⟨711635, by rfl⟩ : syracuseStep 948847 = 1423271) B1423271
theorem B54985463 : Blo 499793 54985463 := bstep (se 1 (by rfl) ⟨41239097, by rfl⟩ : syracuseStep 54985463 = 82478195) B82478195
theorem B43942661 : Blo 499793 43942661 := bstep (se 4 (by rfl) ⟨4119624, by rfl⟩ : syracuseStep 43942661 = 8239249) B8239249
theorem B754559 : Blo 499793 754559 := bstep (se 1 (by rfl) ⟨565919, by rfl⟩ : syracuseStep 754559 = 1131839) B1131839
theorem B9640295 : Blo 499793 9640295 := bstep (se 1 (by rfl) ⟨7230221, by rfl⟩ : syracuseStep 9640295 = 14460443) B14460443
theorem B2141279 : Blo 499793 2141279 := bstep (se 1 (by rfl) ⟨1605959, by rfl⟩ : syracuseStep 2141279 = 3211919) B3211919
theorem B1126511 : Blo 499793 1126511 := bstep (se 1 (by rfl) ⟨844883, by rfl⟩ : syracuseStep 1126511 = 1689767) B1689767
theorem B14825915 : Blo 499793 14825915 := bstep (se 1 (by rfl) ⟨11119436, by rfl⟩ : syracuseStep 14825915 = 22238873) B22238873
theorem B1265129 : Blo 499793 1265129 := bstep (se 2 (by rfl) ⟨474423, by rfl⟩ : syracuseStep 1265129 = 948847) B948847
theorem B1201529 : Blo 499793 1201529 := bstep (se 2 (by rfl) ⟨450573, by rfl⟩ : syracuseStep 1201529 = 901147) B901147
theorem B21782519 : Blo 499793 21782519 := bstep (se 1 (by rfl) ⟨16336889, by rfl⟩ : syracuseStep 21782519 = 32673779) B32673779
theorem B1697327 : Blo 499793 1697327 := bstep (se 1 (by rfl) ⟨1272995, by rfl⟩ : syracuseStep 1697327 = 2545991) B2545991
theorem B751481 : Blo 499793 751481 := bstep (se 2 (by rfl) ⟨281805, by rfl⟩ : syracuseStep 751481 = 563611) B563611
theorem B1014943 : Blo 499793 1014943 := bstep (se 1 (by rfl) ⟨761207, by rfl⟩ : syracuseStep 1014943 = 1522415) B1522415
theorem B752831 : Blo 499793 752831 := bstep (se 1 (by rfl) ⟨564623, by rfl⟩ : syracuseStep 752831 = 1129247) B1129247
theorem B29295107 : Blo 499793 29295107 := bstep (se 1 (by rfl) ⟨21971330, by rfl⟩ : syracuseStep 29295107 = 43942661) B43942661
theorem B6426863 : Blo 499793 6426863 := bstep (se 1 (by rfl) ⟨4820147, by rfl⟩ : syracuseStep 6426863 = 9640295) B9640295
theorem B14521679 : Blo 499793 14521679 := bstep (se 1 (by rfl) ⟨10891259, by rfl⟩ : syracuseStep 14521679 = 21782519) B21782519
theorem B500987 : Blo 499793 500987 := bstep (se 1 (by rfl) ⟨375740, by rfl⟩ : syracuseStep 500987 = 751481) B751481
theorem B1353257 : Blo 499793 1353257 := bstep (se 2 (by rfl) ⟨507471, by rfl⟩ : syracuseStep 1353257 = 1014943) B1014943
theorem B501887 : Blo 499793 501887 := bstep (se 1 (by rfl) ⟨376415, by rfl⟩ : syracuseStep 501887 = 752831) B752831
theorem B503039 : Blo 499793 503039 := bstep (se 1 (by rfl) ⟨377279, by rfl⟩ : syracuseStep 503039 = 754559) B754559
theorem B801019 : Blo 499793 801019 := bstep (se 1 (by rfl) ⟨600764, by rfl⟩ : syracuseStep 801019 = 1201529) B1201529
theorem B1131551 : Blo 499793 1131551 := bstep (se 1 (by rfl) ⟨848663, by rfl⟩ : syracuseStep 1131551 = 1697327) B1697327
theorem B1427519 : Blo 499793 1427519 := bstep (se 1 (by rfl) ⟨1070639, by rfl⟩ : syracuseStep 1427519 = 2141279) B2141279
theorem B9883943 : Blo 499793 9883943 := bstep (se 1 (by rfl) ⟨7412957, by rfl⟩ : syracuseStep 9883943 = 14825915) B14825915
theorem B36656975 : Blo 499793 36656975 := bstep (se 1 (by rfl) ⟨27492731, by rfl⟩ : syracuseStep 36656975 = 54985463) B54985463
theorem B843419 : Blo 499793 843419 := bstep (se 1 (by rfl) ⟨632564, by rfl⟩ : syracuseStep 843419 = 1265129) B1265129
theorem B751007 : Blo 499793 751007 := bstep (se 1 (by rfl) ⟨563255, by rfl⟩ : syracuseStep 751007 = 1126511) B1126511
theorem B19530071 : Blo 499793 19530071 := bstep (se 1 (by rfl) ⟨14647553, by rfl⟩ : syracuseStep 19530071 = 29295107) B29295107
theorem B754367 : Blo 499793 754367 := bstep (se 1 (by rfl) ⟨565775, by rfl⟩ : syracuseStep 754367 = 1131551) B1131551
theorem B951679 : Blo 499793 951679 := bstep (se 1 (by rfl) ⟨713759, by rfl⟩ : syracuseStep 951679 = 1427519) B1427519
theorem B6589295 : Blo 499793 6589295 := bstep (se 1 (by rfl) ⟨4941971, by rfl⟩ : syracuseStep 6589295 = 9883943) B9883943
theorem B562279 : Blo 499793 562279 := bstep (se 1 (by rfl) ⟨421709, by rfl⟩ : syracuseStep 562279 = 843419) B843419
theorem B500671 : Blo 499793 500671 := bstep (se 1 (by rfl) ⟨375503, by rfl⟩ : syracuseStep 500671 = 751007) B751007
theorem B4272101 : Blo 499793 4272101 := bstep (se 4 (by rfl) ⟨400509, by rfl⟩ : syracuseStep 4272101 = 801019) B801019
theorem B9681119 : Blo 499793 9681119 := bstep (se 1 (by rfl) ⟨7260839, by rfl⟩ : syracuseStep 9681119 = 14521679) B14521679
theorem B902171 : Blo 499793 902171 := bstep (se 1 (by rfl) ⟨676628, by rfl⟩ : syracuseStep 902171 = 1353257) B1353257
theorem B4284575 : Blo 499793 4284575 := bstep (se 1 (by rfl) ⟨3213431, by rfl⟩ : syracuseStep 4284575 = 6426863) B6426863
theorem B24437983 : Blo 499793 24437983 := bstep (se 1 (by rfl) ⟨18328487, by rfl⟩ : syracuseStep 24437983 = 36656975) B36656975
theorem B4392863 : Blo 499793 4392863 := bstep (se 1 (by rfl) ⟨3294647, by rfl⟩ : syracuseStep 4392863 = 6589295) B6589295
theorem B2856383 : Blo 499793 2856383 := bstep (se 1 (by rfl) ⟨2142287, by rfl⟩ : syracuseStep 2856383 = 4284575) B4284575
theorem B13020047 : Blo 499793 13020047 := bstep (se 1 (by rfl) ⟨9765035, by rfl⟩ : syracuseStep 13020047 = 19530071) B19530071
theorem B502911 : Blo 499793 502911 := bstep (se 1 (by rfl) ⟨377183, by rfl⟩ : syracuseStep 502911 = 754367) B754367
theorem B601447 : Blo 499793 601447 := bstep (se 1 (by rfl) ⟨451085, by rfl⟩ : syracuseStep 601447 = 902171) B902171
theorem B32583977 : Blo 499793 32583977 := bstep (se 2 (by rfl) ⟨12218991, by rfl⟩ : syracuseStep 32583977 = 24437983) B24437983
theorem B1268905 : Blo 499793 1268905 := bstep (se 2 (by rfl) ⟨475839, by rfl⟩ : syracuseStep 1268905 = 951679) B951679
theorem B749705 : Blo 499793 749705 := bstep (se 2 (by rfl) ⟨281139, by rfl⟩ : syracuseStep 749705 = 562279) B562279
theorem B2848067 : Blo 499793 2848067 := bstep (se 1 (by rfl) ⟨2136050, by rfl⟩ : syracuseStep 2848067 = 4272101) B4272101
theorem B6454079 : Blo 499793 6454079 := bstep (se 1 (by rfl) ⟨4840559, by rfl⟩ : syracuseStep 6454079 = 9681119) B9681119
theorem B1904255 : Blo 499793 1904255 := bstep (se 1 (by rfl) ⟨1428191, by rfl⟩ : syracuseStep 1904255 = 2856383) B2856383
theorem B499803 : Blo 499793 499803 := bstep (se 1 (by rfl) ⟨374852, by rfl⟩ : syracuseStep 499803 = 749705) B749705
theorem B4302719 : Blo 499793 4302719 := bstep (se 1 (by rfl) ⟨3227039, by rfl⟩ : syracuseStep 4302719 = 6454079) B6454079
theorem B2928575 : Blo 499793 2928575 := bstep (se 1 (by rfl) ⟨2196431, by rfl⟩ : syracuseStep 2928575 = 4392863) B4392863
theorem B801929 : Blo 499793 801929 := bstep (se 2 (by rfl) ⟨300723, by rfl⟩ : syracuseStep 801929 = 601447) B601447
theorem B1691873 : Blo 499793 1691873 := bstep (se 2 (by rfl) ⟨634452, by rfl⟩ : syracuseStep 1691873 = 1268905) B1268905
theorem B8680031 : Blo 499793 8680031 := bstep (se 1 (by rfl) ⟨6510023, by rfl⟩ : syracuseStep 8680031 = 13020047) B13020047
theorem B21722651 : Blo 499793 21722651 := bstep (se 1 (by rfl) ⟨16291988, by rfl⟩ : syracuseStep 21722651 = 32583977) B32583977
theorem B1898711 : Blo 499793 1898711 := bstep (se 1 (by rfl) ⟨1424033, by rfl⟩ : syracuseStep 1898711 = 2848067) B2848067
theorem B534619 : Blo 499793 534619 := bstep (se 1 (by rfl) ⟨400964, by rfl⟩ : syracuseStep 534619 = 801929) B801929
theorem B1127915 : Blo 499793 1127915 := bstep (se 1 (by rfl) ⟨845936, by rfl⟩ : syracuseStep 1127915 = 1691873) B1691873
theorem B2868479 : Blo 499793 2868479 := bstep (se 1 (by rfl) ⟨2151359, by rfl⟩ : syracuseStep 2868479 = 4302719) B4302719
theorem B1952383 : Blo 499793 1952383 := bstep (se 1 (by rfl) ⟨1464287, by rfl⟩ : syracuseStep 1952383 = 2928575) B2928575
theorem B5786687 : Blo 499793 5786687 := bstep (se 1 (by rfl) ⟨4340015, by rfl⟩ : syracuseStep 5786687 = 8680031) B8680031
theorem B1265807 : Blo 499793 1265807 := bstep (se 1 (by rfl) ⟨949355, by rfl⟩ : syracuseStep 1265807 = 1898711) B1898711
theorem B1269503 : Blo 499793 1269503 := bstep (se 1 (by rfl) ⟨952127, by rfl⟩ : syracuseStep 1269503 = 1904255) B1904255
theorem B14481767 : Blo 499793 14481767 := bstep (se 1 (by rfl) ⟨10861325, by rfl⟩ : syracuseStep 14481767 = 21722651) B21722651
theorem B2851301 : Blo 499793 2851301 := bstep (se 4 (by rfl) ⟨267309, by rfl⟩ : syracuseStep 2851301 = 534619) B534619
theorem B1912319 : Blo 499793 1912319 := bstep (se 1 (by rfl) ⟨1434239, by rfl⟩ : syracuseStep 1912319 = 2868479) B2868479
theorem B2603177 : Blo 499793 2603177 := bstep (se 2 (by rfl) ⟨976191, by rfl⟩ : syracuseStep 2603177 = 1952383) B1952383
theorem B9654511 : Blo 499793 9654511 := bstep (se 1 (by rfl) ⟨7240883, by rfl⟩ : syracuseStep 9654511 = 14481767) B14481767
theorem B843871 : Blo 499793 843871 := bstep (se 1 (by rfl) ⟨632903, by rfl⟩ : syracuseStep 843871 = 1265807) B1265807
theorem B846335 : Blo 499793 846335 := bstep (se 1 (by rfl) ⟨634751, by rfl⟩ : syracuseStep 846335 = 1269503) B1269503
theorem B15431165 : Blo 499793 15431165 := bstep (se 3 (by rfl) ⟨2893343, by rfl⟩ : syracuseStep 15431165 = 5786687) B5786687
theorem B751943 : Blo 499793 751943 := bstep (se 1 (by rfl) ⟨563957, by rfl⟩ : syracuseStep 751943 = 1127915) B1127915
theorem B1900867 : Blo 499793 1900867 := bstep (se 1 (by rfl) ⟨1425650, by rfl⟩ : syracuseStep 1900867 = 2851301) B2851301
theorem B564223 : Blo 499793 564223 := bstep (se 1 (by rfl) ⟨423167, by rfl⟩ : syracuseStep 564223 = 846335) B846335
theorem B501295 : Blo 499793 501295 := bstep (se 1 (by rfl) ⟨375971, by rfl⟩ : syracuseStep 501295 = 751943) B751943
theorem B1125161 : Blo 499793 1125161 := bstep (se 2 (by rfl) ⟨421935, by rfl⟩ : syracuseStep 1125161 = 843871) B843871
theorem B12872681 : Blo 499793 12872681 := bstep (se 2 (by rfl) ⟨4827255, by rfl⟩ : syracuseStep 12872681 = 9654511) B9654511
theorem B1274879 : Blo 499793 1274879 := bstep (se 1 (by rfl) ⟨956159, by rfl⟩ : syracuseStep 1274879 = 1912319) B1912319
theorem B10287443 : Blo 499793 10287443 := bstep (se 1 (by rfl) ⟨7715582, by rfl⟩ : syracuseStep 10287443 = 15431165) B15431165
theorem B1735451 : Blo 499793 1735451 := bstep (se 1 (by rfl) ⟨1301588, by rfl⟩ : syracuseStep 1735451 = 2603177) B2603177
theorem B27433181 : Blo 499793 27433181 := bstep (se 3 (by rfl) ⟨5143721, by rfl⟩ : syracuseStep 27433181 = 10287443) B10287443
theorem B1156967 : Blo 499793 1156967 := bstep (se 1 (by rfl) ⟨867725, by rfl⟩ : syracuseStep 1156967 = 1735451) B1735451
theorem B2534489 : Blo 499793 2534489 := bstep (se 2 (by rfl) ⟨950433, by rfl⟩ : syracuseStep 2534489 = 1900867) B1900867
theorem B750107 : Blo 499793 750107 := bstep (se 1 (by rfl) ⟨562580, by rfl⟩ : syracuseStep 750107 = 1125161) B1125161
theorem B8581787 : Blo 499793 8581787 := bstep (se 1 (by rfl) ⟨6436340, by rfl⟩ : syracuseStep 8581787 = 12872681) B12872681
theorem B849919 : Blo 499793 849919 := bstep (se 1 (by rfl) ⟨637439, by rfl⟩ : syracuseStep 849919 = 1274879) B1274879
theorem B752297 : Blo 499793 752297 := bstep (se 2 (by rfl) ⟨282111, by rfl⟩ : syracuseStep 752297 = 564223) B564223
theorem B500071 : Blo 499793 500071 := bstep (se 1 (by rfl) ⟨375053, by rfl⟩ : syracuseStep 500071 = 750107) B750107
theorem B501531 : Blo 499793 501531 := bstep (se 1 (by rfl) ⟨376148, by rfl⟩ : syracuseStep 501531 = 752297) B752297
theorem B73155149 : Blo 499793 73155149 := bstep (se 3 (by rfl) ⟨13716590, by rfl⟩ : syracuseStep 73155149 = 27433181) B27433181
theorem B771311 : Blo 499793 771311 := bstep (se 1 (by rfl) ⟨578483, by rfl⟩ : syracuseStep 771311 = 1156967) B1156967
theorem B1689659 : Blo 499793 1689659 := bstep (se 1 (by rfl) ⟨1267244, by rfl⟩ : syracuseStep 1689659 = 2534489) B2534489
theorem B1133225 : Blo 499793 1133225 := bstep (se 2 (by rfl) ⟨424959, by rfl⟩ : syracuseStep 1133225 = 849919) B849919
theorem B5721191 : Blo 499793 5721191 := bstep (se 1 (by rfl) ⟨4290893, by rfl⟩ : syracuseStep 5721191 = 8581787) B8581787
theorem B755483 : Blo 499793 755483 := bstep (se 1 (by rfl) ⟨566612, by rfl⟩ : syracuseStep 755483 = 1133225) B1133225
theorem B48770099 : Blo 499793 48770099 := bstep (se 1 (by rfl) ⟨36577574, by rfl⟩ : syracuseStep 48770099 = 73155149) B73155149
theorem B1126439 : Blo 499793 1126439 := bstep (se 1 (by rfl) ⟨844829, by rfl⟩ : syracuseStep 1126439 = 1689659) B1689659
theorem B3814127 : Blo 499793 3814127 := bstep (se 1 (by rfl) ⟨2860595, by rfl⟩ : syracuseStep 3814127 = 5721191) B5721191
theorem B514207 : Blo 499793 514207 := bstep (se 1 (by rfl) ⟨385655, by rfl⟩ : syracuseStep 514207 = 771311) B771311
theorem B32513399 : Blo 499793 32513399 := bstep (se 1 (by rfl) ⟨24385049, by rfl⟩ : syracuseStep 32513399 = 48770099) B48770099
theorem B503655 : Blo 499793 503655 := bstep (se 1 (by rfl) ⟨377741, by rfl⟩ : syracuseStep 503655 = 755483) B755483
theorem B2542751 : Blo 499793 2542751 := bstep (se 1 (by rfl) ⟨1907063, by rfl⟩ : syracuseStep 2542751 = 3814127) B3814127
theorem B2742437 : Blo 499793 2742437 := bstep (se 4 (by rfl) ⟨257103, by rfl⟩ : syracuseStep 2742437 = 514207) B514207
theorem B750959 : Blo 499793 750959 := bstep (se 1 (by rfl) ⟨563219, by rfl⟩ : syracuseStep 750959 = 1126439) B1126439
theorem B500639 : Blo 499793 500639 := bstep (se 1 (by rfl) ⟨375479, by rfl⟩ : syracuseStep 500639 = 750959) B750959
theorem B21675599 : Blo 499793 21675599 := bstep (se 1 (by rfl) ⟨16256699, by rfl⟩ : syracuseStep 21675599 = 32513399) B32513399
theorem B1695167 : Blo 499793 1695167 := bstep (se 1 (by rfl) ⟨1271375, by rfl⟩ : syracuseStep 1695167 = 2542751) B2542751
theorem B1828291 : Blo 499793 1828291 := bstep (se 1 (by rfl) ⟨1371218, by rfl⟩ : syracuseStep 1828291 = 2742437) B2742437
theorem B2437721 : Blo 499793 2437721 := bstep (se 2 (by rfl) ⟨914145, by rfl⟩ : syracuseStep 2437721 = 1828291) B1828291
theorem B1130111 : Blo 499793 1130111 := bstep (se 1 (by rfl) ⟨847583, by rfl⟩ : syracuseStep 1130111 = 1695167) B1695167
theorem B14450399 : Blo 499793 14450399 := bstep (se 1 (by rfl) ⟨10837799, by rfl⟩ : syracuseStep 14450399 = 21675599) B21675599
theorem B1625147 : Blo 499793 1625147 := bstep (se 1 (by rfl) ⟨1218860, by rfl⟩ : syracuseStep 1625147 = 2437721) B2437721
theorem B753407 : Blo 499793 753407 := bstep (se 1 (by rfl) ⟨565055, by rfl⟩ : syracuseStep 753407 = 1130111) B1130111
theorem B9633599 : Blo 499793 9633599 := bstep (se 1 (by rfl) ⟨7225199, by rfl⟩ : syracuseStep 9633599 = 14450399) B14450399
theorem B1083431 : Blo 499793 1083431 := bstep (se 1 (by rfl) ⟨812573, by rfl⟩ : syracuseStep 1083431 = 1625147) B1625147
theorem B502271 : Blo 499793 502271 := bstep (se 1 (by rfl) ⟨376703, by rfl⟩ : syracuseStep 502271 = 753407) B753407
theorem B6422399 : Blo 499793 6422399 := bstep (se 1 (by rfl) ⟨4816799, by rfl⟩ : syracuseStep 6422399 = 9633599) B9633599
theorem B722287 : Blo 499793 722287 := bstep (se 1 (by rfl) ⟨541715, by rfl⟩ : syracuseStep 722287 = 1083431) B1083431
theorem B4281599 : Blo 499793 4281599 := bstep (se 1 (by rfl) ⟨3211199, by rfl⟩ : syracuseStep 4281599 = 6422399) B6422399
theorem B2854399 : Blo 499793 2854399 := bstep (se 1 (by rfl) ⟨2140799, by rfl⟩ : syracuseStep 2854399 = 4281599) B4281599
theorem B963049 : Blo 499793 963049 := bstep (se 2 (by rfl) ⟨361143, by rfl⟩ : syracuseStep 963049 = 722287) B722287
theorem B3805865 : Blo 499793 3805865 := bstep (se 2 (by rfl) ⟨1427199, by rfl⟩ : syracuseStep 3805865 = 2854399) B2854399
theorem B1284065 : Blo 499793 1284065 := bstep (se 2 (by rfl) ⟨481524, by rfl⟩ : syracuseStep 1284065 = 963049) B963049
theorem B856043 : Blo 499793 856043 := bstep (se 1 (by rfl) ⟨642032, by rfl⟩ : syracuseStep 856043 = 1284065) B1284065
theorem B2537243 : Blo 499793 2537243 := bstep (se 1 (by rfl) ⟨1902932, by rfl⟩ : syracuseStep 2537243 = 3805865) B3805865
theorem B570695 : Blo 499793 570695 := bstep (se 1 (by rfl) ⟨428021, by rfl⟩ : syracuseStep 570695 = 856043) B856043
theorem B1691495 : Blo 499793 1691495 := bstep (se 1 (by rfl) ⟨1268621, by rfl⟩ : syracuseStep 1691495 = 2537243) B2537243
theorem B1127663 : Blo 499793 1127663 := bstep (se 1 (by rfl) ⟨845747, by rfl⟩ : syracuseStep 1127663 = 1691495) B1691495
theorem B6087413 : Blo 499793 6087413 := bstep (se 5 (by rfl) ⟨285347, by rfl⟩ : syracuseStep 6087413 = 570695) B570695
theorem B4058275 : Blo 499793 4058275 := bstep (se 1 (by rfl) ⟨3043706, by rfl⟩ : syracuseStep 4058275 = 6087413) B6087413
theorem B751775 : Blo 499793 751775 := bstep (se 1 (by rfl) ⟨563831, by rfl⟩ : syracuseStep 751775 = 1127663) B1127663
theorem B5411033 : Blo 499793 5411033 := bstep (se 2 (by rfl) ⟨2029137, by rfl⟩ : syracuseStep 5411033 = 4058275) B4058275
theorem B501183 : Blo 499793 501183 := bstep (se 1 (by rfl) ⟨375887, by rfl⟩ : syracuseStep 501183 = 751775) B751775
theorem B3607355 : Blo 499793 3607355 := bstep (se 1 (by rfl) ⟨2705516, by rfl⟩ : syracuseStep 3607355 = 5411033) B5411033
theorem B2404903 : Blo 499793 2404903 := bstep (se 1 (by rfl) ⟨1803677, by rfl⟩ : syracuseStep 2404903 = 3607355) B3607355
theorem B3206537 : Blo 499793 3206537 := bstep (se 2 (by rfl) ⟨1202451, by rfl⟩ : syracuseStep 3206537 = 2404903) B2404903
theorem B2137691 : Blo 499793 2137691 := bstep (se 1 (by rfl) ⟨1603268, by rfl⟩ : syracuseStep 2137691 = 3206537) B3206537
theorem B1425127 : Blo 499793 1425127 := bstep (se 1 (by rfl) ⟨1068845, by rfl⟩ : syracuseStep 1425127 = 2137691) B2137691
theorem B1900169 : Blo 499793 1900169 := bstep (se 2 (by rfl) ⟨712563, by rfl⟩ : syracuseStep 1900169 = 1425127) B1425127
theorem B1266779 : Blo 499793 1266779 := bstep (se 1 (by rfl) ⟨950084, by rfl⟩ : syracuseStep 1266779 = 1900169) B1900169
theorem B844519 : Blo 499793 844519 := bstep (se 1 (by rfl) ⟨633389, by rfl⟩ : syracuseStep 844519 = 1266779) B1266779
theorem B1126025 : Blo 499793 1126025 := bstep (se 2 (by rfl) ⟨422259, by rfl⟩ : syracuseStep 1126025 = 844519) B844519
theorem B750683 : Blo 499793 750683 := bstep (se 1 (by rfl) ⟨563012, by rfl⟩ : syracuseStep 750683 = 1126025) B1126025
theorem B500455 : Blo 499793 500455 := bstep (se 1 (by rfl) ⟨375341, by rfl⟩ : syracuseStep 500455 = 750683) B750683

theorem C0 (j : ℕ) (h1 : 124948 ≤ j) (h2 : j ≤ 125647) : Blo 499793 (4 * j + 3) := by
  interval_cases j
  · exact B499795
  · exact B499799
  · exact B499803
  · exact B499807
  · exact B499811
  · exact B499815
  · exact B499819
  · exact B499823
  · exact B499827
  · exact B499831
  · exact B499835
  · exact B499839
  · exact B499843
  · exact B499847
  · exact B499851
  · exact B499855
  · exact B499859
  · exact B499863
  · exact B499867
  · exact B499871
  · exact B499875
  · exact B499879
  · exact B499883
  · exact B499887
  · exact B499891
  · exact B499895
  · exact B499899
  · exact B499903
  · exact B499907
  · exact B499911
  · exact B499915
  · exact B499919
  · exact B499923
  · exact B499927
  · exact B499931
  · exact B499935
  · exact B499939
  · exact B499943
  · exact B499947
  · exact B499951
  · exact B499955
  · exact B499959
  · exact B499963
  · exact B499967
  · exact B499971
  · exact B499975
  · exact B499979
  · exact B499983
  · exact B499987
  · exact B499991
  · exact B499995
  · exact B499999
  · exact B500003
  · exact B500007
  · exact B500011
  · exact B500015
  · exact B500019
  · exact B500023
  · exact B500027
  · exact B500031
  · exact B500035
  · exact B500039
  · exact B500043
  · exact B500047
  · exact B500051
  · exact B500055
  · exact B500059
  · exact B500063
  · exact B500067
  · exact B500071
  · exact B500075
  · exact B500079
  · exact B500083
  · exact B500087
  · exact B500091
  · exact B500095
  · exact B500099
  · exact B500103
  · exact B500107
  · exact B500111
  · exact B500115
  · exact B500119
  · exact B500123
  · exact B500127
  · exact B500131
  · exact B500135
  · exact B500139
  · exact B500143
  · exact B500147
  · exact B500151
  · exact B500155
  · exact B500159
  · exact B500163
  · exact B500167
  · exact B500171
  · exact B500175
  · exact B500179
  · exact B500183
  · exact B500187
  · exact B500191
  · exact B500195
  · exact B500199
  · exact B500203
  · exact B500207
  · exact B500211
  · exact B500215
  · exact B500219
  · exact B500223
  · exact B500227
  · exact B500231
  · exact B500235
  · exact B500239
  · exact B500243
  · exact B500247
  · exact B500251
  · exact B500255
  · exact B500259
  · exact B500263
  · exact B500267
  · exact B500271
  · exact B500275
  · exact B500279
  · exact B500283
  · exact B500287
  · exact B500291
  · exact B500295
  · exact B500299
  · exact B500303
  · exact B500307
  · exact B500311
  · exact B500315
  · exact B500319
  · exact B500323
  · exact B500327
  · exact B500331
  · exact B500335
  · exact B500339
  · exact B500343
  · exact B500347
  · exact B500351
  · exact B500355
  · exact B500359
  · exact B500363
  · exact B500367
  · exact B500371
  · exact B500375
  · exact B500379
  · exact B500383
  · exact B500387
  · exact B500391
  · exact B500395
  · exact B500399
  · exact B500403
  · exact B500407
  · exact B500411
  · exact B500415
  · exact B500419
  · exact B500423
  · exact B500427
  · exact B500431
  · exact B500435
  · exact B500439
  · exact B500443
  · exact B500447
  · exact B500451
  · exact B500455
  · exact B500459
  · exact B500463
  · exact B500467
  · exact B500471
  · exact B500475
  · exact B500479
  · exact B500483
  · exact B500487
  · exact B500491
  · exact B500495
  · exact B500499
  · exact B500503
  · exact B500507
  · exact B500511
  · exact B500515
  · exact B500519
  · exact B500523
  · exact B500527
  · exact B500531
  · exact B500535
  · exact B500539
  · exact B500543
  · exact B500547
  · exact B500551
  · exact B500555
  · exact B500559
  · exact B500563
  · exact B500567
  · exact B500571
  · exact B500575
  · exact B500579
  · exact B500583
  · exact B500587
  · exact B500591
  · exact B500595
  · exact B500599
  · exact B500603
  · exact B500607
  · exact B500611
  · exact B500615
  · exact B500619
  · exact B500623
  · exact B500627
  · exact B500631
  · exact B500635
  · exact B500639
  · exact B500643
  · exact B500647
  · exact B500651
  · exact B500655
  · exact B500659
  · exact B500663
  · exact B500667
  · exact B500671
  · exact B500675
  · exact B500679
  · exact B500683
  · exact B500687
  · exact B500691
  · exact B500695
  · exact B500699
  · exact B500703
  · exact B500707
  · exact B500711
  · exact B500715
  · exact B500719
  · exact B500723
  · exact B500727
  · exact B500731
  · exact B500735
  · exact B500739
  · exact B500743
  · exact B500747
  · exact B500751
  · exact B500755
  · exact B500759
  · exact B500763
  · exact B500767
  · exact B500771
  · exact B500775
  · exact B500779
  · exact B500783
  · exact B500787
  · exact B500791
  · exact B500795
  · exact B500799
  · exact B500803
  · exact B500807
  · exact B500811
  · exact B500815
  · exact B500819
  · exact B500823
  · exact B500827
  · exact B500831
  · exact B500835
  · exact B500839
  · exact B500843
  · exact B500847
  · exact B500851
  · exact B500855
  · exact B500859
  · exact B500863
  · exact B500867
  · exact B500871
  · exact B500875
  · exact B500879
  · exact B500883
  · exact B500887
  · exact B500891
  · exact B500895
  · exact B500899
  · exact B500903
  · exact B500907
  · exact B500911
  · exact B500915
  · exact B500919
  · exact B500923
  · exact B500927
  · exact B500931
  · exact B500935
  · exact B500939
  · exact B500943
  · exact B500947
  · exact B500951
  · exact B500955
  · exact B500959
  · exact B500963
  · exact B500967
  · exact B500971
  · exact B500975
  · exact B500979
  · exact B500983
  · exact B500987
  · exact B500991
  · exact B500995
  · exact B500999
  · exact B501003
  · exact B501007
  · exact B501011
  · exact B501015
  · exact B501019
  · exact B501023
  · exact B501027
  · exact B501031
  · exact B501035
  · exact B501039
  · exact B501043
  · exact B501047
  · exact B501051
  · exact B501055
  · exact B501059
  · exact B501063
  · exact B501067
  · exact B501071
  · exact B501075
  · exact B501079
  · exact B501083
  · exact B501087
  · exact B501091
  · exact B501095
  · exact B501099
  · exact B501103
  · exact B501107
  · exact B501111
  · exact B501115
  · exact B501119
  · exact B501123
  · exact B501127
  · exact B501131
  · exact B501135
  · exact B501139
  · exact B501143
  · exact B501147
  · exact B501151
  · exact B501155
  · exact B501159
  · exact B501163
  · exact B501167
  · exact B501171
  · exact B501175
  · exact B501179
  · exact B501183
  · exact B501187
  · exact B501191
  · exact B501195
  · exact B501199
  · exact B501203
  · exact B501207
  · exact B501211
  · exact B501215
  · exact B501219
  · exact B501223
  · exact B501227
  · exact B501231
  · exact B501235
  · exact B501239
  · exact B501243
  · exact B501247
  · exact B501251
  · exact B501255
  · exact B501259
  · exact B501263
  · exact B501267
  · exact B501271
  · exact B501275
  · exact B501279
  · exact B501283
  · exact B501287
  · exact B501291
  · exact B501295
  · exact B501299
  · exact B501303
  · exact B501307
  · exact B501311
  · exact B501315
  · exact B501319
  · exact B501323
  · exact B501327
  · exact B501331
  · exact B501335
  · exact B501339
  · exact B501343
  · exact B501347
  · exact B501351
  · exact B501355
  · exact B501359
  · exact B501363
  · exact B501367
  · exact B501371
  · exact B501375
  · exact B501379
  · exact B501383
  · exact B501387
  · exact B501391
  · exact B501395
  · exact B501399
  · exact B501403
  · exact B501407
  · exact B501411
  · exact B501415
  · exact B501419
  · exact B501423
  · exact B501427
  · exact B501431
  · exact B501435
  · exact B501439
  · exact B501443
  · exact B501447
  · exact B501451
  · exact B501455
  · exact B501459
  · exact B501463
  · exact B501467
  · exact B501471
  · exact B501475
  · exact B501479
  · exact B501483
  · exact B501487
  · exact B501491
  · exact B501495
  · exact B501499
  · exact B501503
  · exact B501507
  · exact B501511
  · exact B501515
  · exact B501519
  · exact B501523
  · exact B501527
  · exact B501531
  · exact B501535
  · exact B501539
  · exact B501543
  · exact B501547
  · exact B501551
  · exact B501555
  · exact B501559
  · exact B501563
  · exact B501567
  · exact B501571
  · exact B501575
  · exact B501579
  · exact B501583
  · exact B501587
  · exact B501591
  · exact B501595
  · exact B501599
  · exact B501603
  · exact B501607
  · exact B501611
  · exact B501615
  · exact B501619
  · exact B501623
  · exact B501627
  · exact B501631
  · exact B501635
  · exact B501639
  · exact B501643
  · exact B501647
  · exact B501651
  · exact B501655
  · exact B501659
  · exact B501663
  · exact B501667
  · exact B501671
  · exact B501675
  · exact B501679
  · exact B501683
  · exact B501687
  · exact B501691
  · exact B501695
  · exact B501699
  · exact B501703
  · exact B501707
  · exact B501711
  · exact B501715
  · exact B501719
  · exact B501723
  · exact B501727
  · exact B501731
  · exact B501735
  · exact B501739
  · exact B501743
  · exact B501747
  · exact B501751
  · exact B501755
  · exact B501759
  · exact B501763
  · exact B501767
  · exact B501771
  · exact B501775
  · exact B501779
  · exact B501783
  · exact B501787
  · exact B501791
  · exact B501795
  · exact B501799
  · exact B501803
  · exact B501807
  · exact B501811
  · exact B501815
  · exact B501819
  · exact B501823
  · exact B501827
  · exact B501831
  · exact B501835
  · exact B501839
  · exact B501843
  · exact B501847
  · exact B501851
  · exact B501855
  · exact B501859
  · exact B501863
  · exact B501867
  · exact B501871
  · exact B501875
  · exact B501879
  · exact B501883
  · exact B501887
  · exact B501891
  · exact B501895
  · exact B501899
  · exact B501903
  · exact B501907
  · exact B501911
  · exact B501915
  · exact B501919
  · exact B501923
  · exact B501927
  · exact B501931
  · exact B501935
  · exact B501939
  · exact B501943
  · exact B501947
  · exact B501951
  · exact B501955
  · exact B501959
  · exact B501963
  · exact B501967
  · exact B501971
  · exact B501975
  · exact B501979
  · exact B501983
  · exact B501987
  · exact B501991
  · exact B501995
  · exact B501999
  · exact B502003
  · exact B502007
  · exact B502011
  · exact B502015
  · exact B502019
  · exact B502023
  · exact B502027
  · exact B502031
  · exact B502035
  · exact B502039
  · exact B502043
  · exact B502047
  · exact B502051
  · exact B502055
  · exact B502059
  · exact B502063
  · exact B502067
  · exact B502071
  · exact B502075
  · exact B502079
  · exact B502083
  · exact B502087
  · exact B502091
  · exact B502095
  · exact B502099
  · exact B502103
  · exact B502107
  · exact B502111
  · exact B502115
  · exact B502119
  · exact B502123
  · exact B502127
  · exact B502131
  · exact B502135
  · exact B502139
  · exact B502143
  · exact B502147
  · exact B502151
  · exact B502155
  · exact B502159
  · exact B502163
  · exact B502167
  · exact B502171
  · exact B502175
  · exact B502179
  · exact B502183
  · exact B502187
  · exact B502191
  · exact B502195
  · exact B502199
  · exact B502203
  · exact B502207
  · exact B502211
  · exact B502215
  · exact B502219
  · exact B502223
  · exact B502227
  · exact B502231
  · exact B502235
  · exact B502239
  · exact B502243
  · exact B502247
  · exact B502251
  · exact B502255
  · exact B502259
  · exact B502263
  · exact B502267
  · exact B502271
  · exact B502275
  · exact B502279
  · exact B502283
  · exact B502287
  · exact B502291
  · exact B502295
  · exact B502299
  · exact B502303
  · exact B502307
  · exact B502311
  · exact B502315
  · exact B502319
  · exact B502323
  · exact B502327
  · exact B502331
  · exact B502335
  · exact B502339
  · exact B502343
  · exact B502347
  · exact B502351
  · exact B502355
  · exact B502359
  · exact B502363
  · exact B502367
  · exact B502371
  · exact B502375
  · exact B502379
  · exact B502383
  · exact B502387
  · exact B502391
  · exact B502395
  · exact B502399
  · exact B502403
  · exact B502407
  · exact B502411
  · exact B502415
  · exact B502419
  · exact B502423
  · exact B502427
  · exact B502431
  · exact B502435
  · exact B502439
  · exact B502443
  · exact B502447
  · exact B502451
  · exact B502455
  · exact B502459
  · exact B502463
  · exact B502467
  · exact B502471
  · exact B502475
  · exact B502479
  · exact B502483
  · exact B502487
  · exact B502491
  · exact B502495
  · exact B502499
  · exact B502503
  · exact B502507
  · exact B502511
  · exact B502515
  · exact B502519
  · exact B502523
  · exact B502527
  · exact B502531
  · exact B502535
  · exact B502539
  · exact B502543
  · exact B502547
  · exact B502551
  · exact B502555
  · exact B502559
  · exact B502563
  · exact B502567
  · exact B502571
  · exact B502575
  · exact B502579
  · exact B502583
  · exact B502587
  · exact B502591

theorem C1 (j : ℕ) (h1 : 125648 ≤ j) (h2 : j ≤ 125947) : Blo 499793 (4 * j + 3) := by
  interval_cases j
  · exact B502595
  · exact B502599
  · exact B502603
  · exact B502607
  · exact B502611
  · exact B502615
  · exact B502619
  · exact B502623
  · exact B502627
  · exact B502631
  · exact B502635
  · exact B502639
  · exact B502643
  · exact B502647
  · exact B502651
  · exact B502655
  · exact B502659
  · exact B502663
  · exact B502667
  · exact B502671
  · exact B502675
  · exact B502679
  · exact B502683
  · exact B502687
  · exact B502691
  · exact B502695
  · exact B502699
  · exact B502703
  · exact B502707
  · exact B502711
  · exact B502715
  · exact B502719
  · exact B502723
  · exact B502727
  · exact B502731
  · exact B502735
  · exact B502739
  · exact B502743
  · exact B502747
  · exact B502751
  · exact B502755
  · exact B502759
  · exact B502763
  · exact B502767
  · exact B502771
  · exact B502775
  · exact B502779
  · exact B502783
  · exact B502787
  · exact B502791
  · exact B502795
  · exact B502799
  · exact B502803
  · exact B502807
  · exact B502811
  · exact B502815
  · exact B502819
  · exact B502823
  · exact B502827
  · exact B502831
  · exact B502835
  · exact B502839
  · exact B502843
  · exact B502847
  · exact B502851
  · exact B502855
  · exact B502859
  · exact B502863
  · exact B502867
  · exact B502871
  · exact B502875
  · exact B502879
  · exact B502883
  · exact B502887
  · exact B502891
  · exact B502895
  · exact B502899
  · exact B502903
  · exact B502907
  · exact B502911
  · exact B502915
  · exact B502919
  · exact B502923
  · exact B502927
  · exact B502931
  · exact B502935
  · exact B502939
  · exact B502943
  · exact B502947
  · exact B502951
  · exact B502955
  · exact B502959
  · exact B502963
  · exact B502967
  · exact B502971
  · exact B502975
  · exact B502979
  · exact B502983
  · exact B502987
  · exact B502991
  · exact B502995
  · exact B502999
  · exact B503003
  · exact B503007
  · exact B503011
  · exact B503015
  · exact B503019
  · exact B503023
  · exact B503027
  · exact B503031
  · exact B503035
  · exact B503039
  · exact B503043
  · exact B503047
  · exact B503051
  · exact B503055
  · exact B503059
  · exact B503063
  · exact B503067
  · exact B503071
  · exact B503075
  · exact B503079
  · exact B503083
  · exact B503087
  · exact B503091
  · exact B503095
  · exact B503099
  · exact B503103
  · exact B503107
  · exact B503111
  · exact B503115
  · exact B503119
  · exact B503123
  · exact B503127
  · exact B503131
  · exact B503135
  · exact B503139
  · exact B503143
  · exact B503147
  · exact B503151
  · exact B503155
  · exact B503159
  · exact B503163
  · exact B503167
  · exact B503171
  · exact B503175
  · exact B503179
  · exact B503183
  · exact B503187
  · exact B503191
  · exact B503195
  · exact B503199
  · exact B503203
  · exact B503207
  · exact B503211
  · exact B503215
  · exact B503219
  · exact B503223
  · exact B503227
  · exact B503231
  · exact B503235
  · exact B503239
  · exact B503243
  · exact B503247
  · exact B503251
  · exact B503255
  · exact B503259
  · exact B503263
  · exact B503267
  · exact B503271
  · exact B503275
  · exact B503279
  · exact B503283
  · exact B503287
  · exact B503291
  · exact B503295
  · exact B503299
  · exact B503303
  · exact B503307
  · exact B503311
  · exact B503315
  · exact B503319
  · exact B503323
  · exact B503327
  · exact B503331
  · exact B503335
  · exact B503339
  · exact B503343
  · exact B503347
  · exact B503351
  · exact B503355
  · exact B503359
  · exact B503363
  · exact B503367
  · exact B503371
  · exact B503375
  · exact B503379
  · exact B503383
  · exact B503387
  · exact B503391
  · exact B503395
  · exact B503399
  · exact B503403
  · exact B503407
  · exact B503411
  · exact B503415
  · exact B503419
  · exact B503423
  · exact B503427
  · exact B503431
  · exact B503435
  · exact B503439
  · exact B503443
  · exact B503447
  · exact B503451
  · exact B503455
  · exact B503459
  · exact B503463
  · exact B503467
  · exact B503471
  · exact B503475
  · exact B503479
  · exact B503483
  · exact B503487
  · exact B503491
  · exact B503495
  · exact B503499
  · exact B503503
  · exact B503507
  · exact B503511
  · exact B503515
  · exact B503519
  · exact B503523
  · exact B503527
  · exact B503531
  · exact B503535
  · exact B503539
  · exact B503543
  · exact B503547
  · exact B503551
  · exact B503555
  · exact B503559
  · exact B503563
  · exact B503567
  · exact B503571
  · exact B503575
  · exact B503579
  · exact B503583
  · exact B503587
  · exact B503591
  · exact B503595
  · exact B503599
  · exact B503603
  · exact B503607
  · exact B503611
  · exact B503615
  · exact B503619
  · exact B503623
  · exact B503627
  · exact B503631
  · exact B503635
  · exact B503639
  · exact B503643
  · exact B503647
  · exact B503651
  · exact B503655
  · exact B503659
  · exact B503663
  · exact B503667
  · exact B503671
  · exact B503675
  · exact B503679
  · exact B503683
  · exact B503687
  · exact B503691
  · exact B503695
  · exact B503699
  · exact B503703
  · exact B503707
  · exact B503711
  · exact B503715
  · exact B503719
  · exact B503723
  · exact B503727
  · exact B503731
  · exact B503735
  · exact B503739
  · exact B503743
  · exact B503747
  · exact B503751
  · exact B503755
  · exact B503759
  · exact B503763
  · exact B503767
  · exact B503771
  · exact B503775
  · exact B503779
  · exact B503783
  · exact B503787
  · exact B503791

theorem solution (m : ℕ) (hlo : 499793 ≤ m) (hhi : m ≤ 503793) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 124948 ≤ j := by omega
    have hj2 : j ≤ 125947 := by omega
    have hb : Blo 499793 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 125648 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
