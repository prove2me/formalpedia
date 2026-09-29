-- Prove2me | solution 1 for syracuse_descends_range_1315976_1317976
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:33.189361+00:00
-- url     : https://prove2.me/submissions/274e45fc-83cd-4193-9735-88716289a65b

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


theorem B1581061 : Blo 1315976 1581061 := bbase (se 4 (by rfl) ⟨148224, by rfl⟩ : syracuseStep 1581061 = 296449) (by norm_num)
theorem B1974293 : Blo 1315976 1974293 := bbase (se 6 (by rfl) ⟨46272, by rfl⟩ : syracuseStep 1974293 = 92545) (by norm_num)
theorem B1974317 : Blo 1315976 1974317 := bbase (se 3 (by rfl) ⟨370184, by rfl⟩ : syracuseStep 1974317 = 740369) (by norm_num)
theorem B4997173 : Blo 1315976 4997173 := bbase (se 5 (by rfl) ⟨234242, by rfl⟩ : syracuseStep 4997173 = 468485) (by norm_num)
theorem B1974341 : Blo 1315976 1974341 := bbase (se 4 (by rfl) ⟨185094, by rfl⟩ : syracuseStep 1974341 = 370189) (by norm_num)
theorem B3162197 : Blo 1315976 3162197 := bbase (se 8 (by rfl) ⟨18528, by rfl⟩ : syracuseStep 3162197 = 37057) (by norm_num)
theorem B1974365 : Blo 1315976 1974365 := bbase (se 3 (by rfl) ⟨370193, by rfl⟩ : syracuseStep 1974365 = 740387) (by norm_num)
theorem B1581157 : Blo 1315976 1581157 := bbase (se 4 (by rfl) ⟨148233, by rfl⟩ : syracuseStep 1581157 = 296467) (by norm_num)
theorem B1974389 : Blo 1315976 1974389 := bbase (se 5 (by rfl) ⟨92549, by rfl⟩ : syracuseStep 1974389 = 185099) (by norm_num)
theorem B6668405 : Blo 1315976 6668405 := bbase (se 5 (by rfl) ⟨312581, by rfl⟩ : syracuseStep 6668405 = 625163) (by norm_num)
theorem B2498701 : Blo 1315976 2498701 := bbase (se 3 (by rfl) ⟨468506, by rfl⟩ : syracuseStep 2498701 = 937013) (by norm_num)
theorem B1974413 : Blo 1315976 1974413 := bbase (se 3 (by rfl) ⟨370202, by rfl⟩ : syracuseStep 1974413 = 740405) (by norm_num)
theorem B1974437 : Blo 1315976 1974437 := bbase (se 4 (by rfl) ⟨185103, by rfl⟩ : syracuseStep 1974437 = 370207) (by norm_num)
theorem B1974461 : Blo 1315976 1974461 := bbase (se 3 (by rfl) ⟨370211, by rfl⟩ : syracuseStep 1974461 = 740423) (by norm_num)
theorem B1409233 : Blo 1315976 1409233 := bbase (se 2 (by rfl) ⟨528462, by rfl⟩ : syracuseStep 1409233 = 1056925) (by norm_num)
theorem B1974485 : Blo 1315976 1974485 := bbase (se 7 (by rfl) ⟨23138, by rfl⟩ : syracuseStep 1974485 = 46277) (by norm_num)
theorem B1974509 : Blo 1315976 1974509 := bbase (se 3 (by rfl) ⟨370220, by rfl⟩ : syracuseStep 1974509 = 740441) (by norm_num)
theorem B1876213 : Blo 1315976 1876213 := bbase (se 5 (by rfl) ⟨87947, by rfl⟩ : syracuseStep 1876213 = 175895) (by norm_num)
theorem B1974533 : Blo 1315976 1974533 := bbase (se 4 (by rfl) ⟨185112, by rfl⟩ : syracuseStep 1974533 = 370225) (by norm_num)
theorem B6086917 : Blo 1315976 6086917 := bbase (se 4 (by rfl) ⟨570648, by rfl⟩ : syracuseStep 6086917 = 1141297) (by norm_num)
theorem B3334405 : Blo 1315976 3334405 := bbase (se 4 (by rfl) ⟨312600, by rfl⟩ : syracuseStep 3334405 = 625201) (by norm_num)
theorem B2498845 : Blo 1315976 2498845 := bbase (se 3 (by rfl) ⟨468533, by rfl⟩ : syracuseStep 2498845 = 937067) (by norm_num)
theorem B1974557 : Blo 1315976 1974557 := bbase (se 3 (by rfl) ⟨370229, by rfl⟩ : syracuseStep 1974557 = 740459) (by norm_num)
theorem B1335593 : Blo 1315976 1335593 := bbase (se 2 (by rfl) ⟨500847, by rfl⟩ : syracuseStep 1335593 = 1001695) (by norm_num)
theorem B1974581 : Blo 1315976 1974581 := bbase (se 5 (by rfl) ⟨92558, by rfl⟩ : syracuseStep 1974581 = 185117) (by norm_num)
theorem B1974605 : Blo 1315976 1974605 := bbase (se 3 (by rfl) ⟨370238, by rfl⟩ : syracuseStep 1974605 = 740477) (by norm_num)
theorem B4997477 : Blo 1315976 4997477 := bbase (se 4 (by rfl) ⟨468513, by rfl⟩ : syracuseStep 4997477 = 937027) (by norm_num)
theorem B1974629 : Blo 1315976 1974629 := bbase (se 4 (by rfl) ⟨185121, by rfl⟩ : syracuseStep 1974629 = 370243) (by norm_num)
theorem B3334517 : Blo 1315976 3334517 := bbase (se 5 (by rfl) ⟨156305, by rfl⟩ : syracuseStep 3334517 = 312611) (by norm_num)
theorem B1974653 : Blo 1315976 1974653 := bbase (se 3 (by rfl) ⟨370247, by rfl⟩ : syracuseStep 1974653 = 740495) (by norm_num)
theorem B1581445 : Blo 1315976 1581445 := bbase (se 4 (by rfl) ⟨148260, by rfl⟩ : syracuseStep 1581445 = 296521) (by norm_num)
theorem B1974677 : Blo 1315976 1974677 := bbase (se 6 (by rfl) ⟨46281, by rfl⟩ : syracuseStep 1974677 = 92563) (by norm_num)
theorem B8438165 : Blo 1315976 8438165 := bbase (se 6 (by rfl) ⟨197769, by rfl⟩ : syracuseStep 8438165 = 395539) (by norm_num)
theorem B1974701 : Blo 1315976 1974701 := bbase (se 3 (by rfl) ⟨370256, by rfl⟩ : syracuseStep 1974701 = 740513) (by norm_num)
theorem B2499005 : Blo 1315976 2499005 := bbase (se 3 (by rfl) ⟨468563, by rfl⟩ : syracuseStep 2499005 = 937127) (by norm_num)
theorem B1974725 : Blo 1315976 1974725 := bbase (se 4 (by rfl) ⟨185130, by rfl⟩ : syracuseStep 1974725 = 370261) (by norm_num)
theorem B1974749 : Blo 1315976 1974749 := bbase (se 3 (by rfl) ⟨370265, by rfl⟩ : syracuseStep 1974749 = 740531) (by norm_num)
theorem B1974773 : Blo 1315976 1974773 := bbase (se 5 (by rfl) ⟨92567, by rfl⟩ : syracuseStep 1974773 = 185135) (by norm_num)
theorem B1974797 : Blo 1315976 1974797 := bbase (se 3 (by rfl) ⟨370274, by rfl⟩ : syracuseStep 1974797 = 740549) (by norm_num)
theorem B1974821 : Blo 1315976 1974821 := bbase (se 4 (by rfl) ⟨185139, by rfl⟩ : syracuseStep 1974821 = 370279) (by norm_num)
theorem B2253349 : Blo 1315976 2253349 := bbase (se 4 (by rfl) ⟨211251, by rfl⟩ : syracuseStep 2253349 = 422503) (by norm_num)
theorem B1335853 : Blo 1315976 1335853 := bbase (se 3 (by rfl) ⟨250472, by rfl⟩ : syracuseStep 1335853 = 500945) (by norm_num)
theorem B3334709 : Blo 1315976 3334709 := bbase (se 5 (by rfl) ⟨156314, by rfl⟩ : syracuseStep 3334709 = 312629) (by norm_num)
theorem B1974845 : Blo 1315976 1974845 := bbase (se 3 (by rfl) ⟨370283, by rfl⟩ : syracuseStep 1974845 = 740567) (by norm_num)
theorem B1581637 : Blo 1315976 1581637 := bbase (se 4 (by rfl) ⟨148278, by rfl⟩ : syracuseStep 1581637 = 296557) (by norm_num)
theorem B1876549 : Blo 1315976 1876549 := bbase (se 4 (by rfl) ⟨175926, by rfl⟩ : syracuseStep 1876549 = 351853) (by norm_num)
theorem B2499149 : Blo 1315976 2499149 := bbase (se 3 (by rfl) ⟨468590, by rfl⟩ : syracuseStep 2499149 = 937181) (by norm_num)
theorem B1974869 : Blo 1315976 1974869 := bbase (se 8 (by rfl) ⟨11571, by rfl⟩ : syracuseStep 1974869 = 23143) (by norm_num)
theorem B1974893 : Blo 1315976 1974893 := bbase (se 3 (by rfl) ⟨370292, by rfl⟩ : syracuseStep 1974893 = 740585) (by norm_num)
theorem B1974917 : Blo 1315976 1974917 := bbase (se 4 (by rfl) ⟨185148, by rfl⟩ : syracuseStep 1974917 = 370297) (by norm_num)
theorem B1974941 : Blo 1315976 1974941 := bbase (se 3 (by rfl) ⟨370301, by rfl⟩ : syracuseStep 1974941 = 740603) (by norm_num)
theorem B1974965 : Blo 1315976 1974965 := bbase (se 5 (by rfl) ⟨92576, by rfl⟩ : syracuseStep 1974965 = 185153) (by norm_num)
theorem B1974989 : Blo 1315976 1974989 := bbase (se 3 (by rfl) ⟨370310, by rfl⟩ : syracuseStep 1974989 = 740621) (by norm_num)
theorem B1975013 : Blo 1315976 1975013 := bbase (se 4 (by rfl) ⟨185157, by rfl⟩ : syracuseStep 1975013 = 370315) (by norm_num)
theorem B2220797 : Blo 1315976 2220797 := bbase (se 3 (by rfl) ⟨416399, by rfl⟩ : syracuseStep 2220797 = 832799) (by norm_num)
theorem B1975037 : Blo 1315976 1975037 := bbase (se 3 (by rfl) ⟨370319, by rfl⟩ : syracuseStep 1975037 = 740639) (by norm_num)
theorem B2810629 : Blo 1315976 2810629 := bbase (se 4 (by rfl) ⟨263496, by rfl⟩ : syracuseStep 2810629 = 526993) (by norm_num)
theorem B1975061 : Blo 1315976 1975061 := bbase (se 6 (by rfl) ⟨46290, by rfl⟩ : syracuseStep 1975061 = 92581) (by norm_num)
theorem B1975085 : Blo 1315976 1975085 := bbase (se 3 (by rfl) ⟨370328, by rfl⟩ : syracuseStep 1975085 = 740657) (by norm_num)
theorem B1975109 : Blo 1315976 1975109 := bbase (se 4 (by rfl) ⟨185166, by rfl⟩ : syracuseStep 1975109 = 370333) (by norm_num)
theorem B1975133 : Blo 1315976 1975133 := bbase (se 3 (by rfl) ⟨370337, by rfl⟩ : syracuseStep 1975133 = 740675) (by norm_num)
theorem B2499437 : Blo 1315976 2499437 := bbase (se 3 (by rfl) ⟨468644, by rfl⟩ : syracuseStep 2499437 = 937289) (by norm_num)
theorem B1975157 : Blo 1315976 1975157 := bbase (se 5 (by rfl) ⟨92585, by rfl⟩ : syracuseStep 1975157 = 185171) (by norm_num)
theorem B2220925 : Blo 1315976 2220925 := bbase (se 3 (by rfl) ⟨416423, by rfl⟩ : syracuseStep 2220925 = 832847) (by norm_num)
theorem B1975181 : Blo 1315976 1975181 := bbase (se 3 (by rfl) ⟨370346, by rfl⟩ : syracuseStep 1975181 = 740693) (by norm_num)
theorem B3335053 : Blo 1315976 3335053 := bbase (se 3 (by rfl) ⟨625322, by rfl⟩ : syracuseStep 3335053 = 1250645) (by norm_num)
theorem B1975205 : Blo 1315976 1975205 := bbase (se 4 (by rfl) ⟨185175, by rfl⟩ : syracuseStep 1975205 = 370351) (by norm_num)
theorem B1975229 : Blo 1315976 1975229 := bbase (se 3 (by rfl) ⟨370355, by rfl⟩ : syracuseStep 1975229 = 740711) (by norm_num)
theorem B2221013 : Blo 1315976 2221013 := bbase (se 7 (by rfl) ⟨26027, by rfl⟩ : syracuseStep 2221013 = 52055) (by norm_num)
theorem B1975253 : Blo 1315976 1975253 := bbase (se 7 (by rfl) ⟨23147, by rfl⟩ : syracuseStep 1975253 = 46295) (by norm_num)
theorem B22815701 : Blo 1315976 22815701 := bbase (se 7 (by rfl) ⟨267371, by rfl⟩ : syracuseStep 22815701 = 534743) (by norm_num)
theorem B4219877 : Blo 1315976 4219877 := bbase (se 4 (by rfl) ⟨395613, by rfl⟩ : syracuseStep 4219877 = 791227) (by norm_num)
theorem B1975277 : Blo 1315976 1975277 := bbase (se 3 (by rfl) ⟨370364, by rfl⟩ : syracuseStep 1975277 = 740729) (by norm_num)
theorem B3335165 : Blo 1315976 3335165 := bbase (se 3 (by rfl) ⟨625343, by rfl⟩ : syracuseStep 3335165 = 1250687) (by norm_num)
theorem B2499589 : Blo 1315976 2499589 := bbase (se 4 (by rfl) ⟨234336, by rfl⟩ : syracuseStep 2499589 = 468673) (by norm_num)
theorem B1975301 : Blo 1315976 1975301 := bbase (se 4 (by rfl) ⟨185184, by rfl⟩ : syracuseStep 1975301 = 370369) (by norm_num)
theorem B1975325 : Blo 1315976 1975325 := bbase (se 3 (by rfl) ⟨370373, by rfl⟩ : syracuseStep 1975325 = 740747) (by norm_num)
theorem B1975349 : Blo 1315976 1975349 := bbase (se 5 (by rfl) ⟨92594, by rfl⟩ : syracuseStep 1975349 = 185189) (by norm_num)
theorem B7603253 : Blo 1315976 7603253 := bbase (se 5 (by rfl) ⟨356402, by rfl⟩ : syracuseStep 7603253 = 712805) (by norm_num)
theorem B3753029 : Blo 1315976 3753029 := bbase (se 4 (by rfl) ⟨351846, by rfl⟩ : syracuseStep 3753029 = 703693) (by norm_num)
theorem B1975373 : Blo 1315976 1975373 := bbase (se 3 (by rfl) ⟨370382, by rfl⟩ : syracuseStep 1975373 = 740765) (by norm_num)
theorem B2221141 : Blo 1315976 2221141 := bbase (se 8 (by rfl) ⟨13014, by rfl⟩ : syracuseStep 2221141 = 26029) (by norm_num)
theorem B1975397 : Blo 1315976 1975397 := bbase (se 4 (by rfl) ⟨185193, by rfl⟩ : syracuseStep 1975397 = 370387) (by norm_num)
theorem B1975421 : Blo 1315976 1975421 := bbase (se 3 (by rfl) ⟨370391, by rfl⟩ : syracuseStep 1975421 = 740783) (by norm_num)
theorem B6325397 : Blo 1315976 6325397 := bbase (se 6 (by rfl) ⟨148251, by rfl⟩ : syracuseStep 6325397 = 296503) (by norm_num)
theorem B1975445 : Blo 1315976 1975445 := bbase (se 6 (by rfl) ⟨46299, by rfl⟩ : syracuseStep 1975445 = 92599) (by norm_num)
theorem B2221229 : Blo 1315976 2221229 := bbase (se 3 (by rfl) ⟨416480, by rfl⟩ : syracuseStep 2221229 = 832961) (by norm_num)
theorem B1975469 : Blo 1315976 1975469 := bbase (se 3 (by rfl) ⟨370400, by rfl⟩ : syracuseStep 1975469 = 740801) (by norm_num)
theorem B3335357 : Blo 1315976 3335357 := bbase (se 3 (by rfl) ⟨625379, by rfl⟩ : syracuseStep 3335357 = 1250759) (by norm_num)
theorem B1975493 : Blo 1315976 1975493 := bbase (se 4 (by rfl) ⟨185202, by rfl⟩ : syracuseStep 1975493 = 370405) (by norm_num)
theorem B1975517 : Blo 1315976 1975517 := bbase (se 3 (by rfl) ⟨370409, by rfl⟩ : syracuseStep 1975517 = 740819) (by norm_num)
theorem B2254061 : Blo 1315976 2254061 := bbase (se 3 (by rfl) ⟨422636, by rfl⟩ : syracuseStep 2254061 = 845273) (by norm_num)
theorem B1975541 : Blo 1315976 1975541 := bbase (se 5 (by rfl) ⟨92603, by rfl⟩ : syracuseStep 1975541 = 185207) (by norm_num)
theorem B6505733 : Blo 1315976 6505733 := bbase (se 4 (by rfl) ⟨609912, by rfl⟩ : syracuseStep 6505733 = 1219825) (by norm_num)
theorem B1975565 : Blo 1315976 1975565 := bbase (se 3 (by rfl) ⟨370418, by rfl⟩ : syracuseStep 1975565 = 740837) (by norm_num)
theorem B1975589 : Blo 1315976 1975589 := bbase (se 4 (by rfl) ⟨185211, by rfl⟩ : syracuseStep 1975589 = 370423) (by norm_num)
theorem B2221357 : Blo 1315976 2221357 := bbase (se 3 (by rfl) ⟨416504, by rfl⟩ : syracuseStep 2221357 = 833009) (by norm_num)
theorem B2499893 : Blo 1315976 2499893 := bbase (se 5 (by rfl) ⟨117182, by rfl⟩ : syracuseStep 2499893 = 234365) (by norm_num)
theorem B1975613 : Blo 1315976 1975613 := bbase (se 3 (by rfl) ⟨370427, by rfl⟩ : syracuseStep 1975613 = 740855) (by norm_num)
theorem B1975637 : Blo 1315976 1975637 := bbase (se 12 (by rfl) ⟨723, by rfl⟩ : syracuseStep 1975637 = 1447) (by norm_num)
theorem B7505237 : Blo 1315976 7505237 := bbase (se 12 (by rfl) ⟨2748, by rfl⟩ : syracuseStep 7505237 = 5497) (by norm_num)
theorem B4441445 : Blo 1315976 4441445 := bbase (se 4 (by rfl) ⟨416385, by rfl⟩ : syracuseStep 4441445 = 832771) (by norm_num)
theorem B1975661 : Blo 1315976 1975661 := bbase (se 3 (by rfl) ⟨370436, by rfl⟩ : syracuseStep 1975661 = 740873) (by norm_num)
theorem B2221445 : Blo 1315976 2221445 := bbase (se 4 (by rfl) ⟨208260, by rfl⟩ : syracuseStep 2221445 = 416521) (by norm_num)
theorem B1975685 : Blo 1315976 1975685 := bbase (se 4 (by rfl) ⟨185220, by rfl⟩ : syracuseStep 1975685 = 370441) (by norm_num)
theorem B6669701 : Blo 1315976 6669701 := bbase (se 4 (by rfl) ⟨625284, by rfl⟩ : syracuseStep 6669701 = 1250569) (by norm_num)
theorem B1975709 : Blo 1315976 1975709 := bbase (se 3 (by rfl) ⟨370445, by rfl⟩ : syracuseStep 1975709 = 740891) (by norm_num)
theorem B1975733 : Blo 1315976 1975733 := bbase (se 5 (by rfl) ⟨92612, by rfl⟩ : syracuseStep 1975733 = 185225) (by norm_num)
theorem B1582517 : Blo 1315976 1582517 := bbase (se 5 (by rfl) ⟨74180, by rfl⟩ : syracuseStep 1582517 = 148361) (by norm_num)
theorem B1975757 : Blo 1315976 1975757 := bbase (se 3 (by rfl) ⟨370454, by rfl⟩ : syracuseStep 1975757 = 740909) (by norm_num)
theorem B1975781 : Blo 1315976 1975781 := bbase (se 4 (by rfl) ⟨185229, by rfl⟩ : syracuseStep 1975781 = 370459) (by norm_num)
theorem B1975805 : Blo 1315976 1975805 := bbase (se 3 (by rfl) ⟨370463, by rfl⟩ : syracuseStep 1975805 = 740927) (by norm_num)
theorem B2221573 : Blo 1315976 2221573 := bbase (se 4 (by rfl) ⟨208272, by rfl⟩ : syracuseStep 2221573 = 416545) (by norm_num)
theorem B1975829 : Blo 1315976 1975829 := bbase (se 6 (by rfl) ⟨46308, by rfl⟩ : syracuseStep 1975829 = 92617) (by norm_num)
theorem B3335701 : Blo 1315976 3335701 := bbase (se 6 (by rfl) ⟨78180, by rfl⟩ : syracuseStep 3335701 = 156361) (by norm_num)
theorem B1975853 : Blo 1315976 1975853 := bbase (se 3 (by rfl) ⟨370472, by rfl⟩ : syracuseStep 1975853 = 740945) (by norm_num)
theorem B1975877 : Blo 1315976 1975877 := bbase (se 4 (by rfl) ⟨185238, by rfl⟩ : syracuseStep 1975877 = 370477) (by norm_num)
theorem B2221661 : Blo 1315976 2221661 := bbase (se 3 (by rfl) ⟨416561, by rfl⟩ : syracuseStep 2221661 = 833123) (by norm_num)
theorem B1975901 : Blo 1315976 1975901 := bbase (se 3 (by rfl) ⟨370481, by rfl⟩ : syracuseStep 1975901 = 740963) (by norm_num)
theorem B1975925 : Blo 1315976 1975925 := bbase (se 5 (by rfl) ⟨92621, by rfl⟩ : syracuseStep 1975925 = 185243) (by norm_num)
theorem B3335813 : Blo 1315976 3335813 := bbase (se 4 (by rfl) ⟨312732, by rfl⟩ : syracuseStep 3335813 = 625465) (by norm_num)
theorem B1975949 : Blo 1315976 1975949 := bbase (se 3 (by rfl) ⟨370490, by rfl⟩ : syracuseStep 1975949 = 740981) (by norm_num)
theorem B1926805 : Blo 1315976 1926805 := bbase (se 6 (by rfl) ⟨45159, by rfl⟩ : syracuseStep 1926805 = 90319) (by norm_num)
theorem B1975973 : Blo 1315976 1975973 := bbase (se 4 (by rfl) ⟨185247, by rfl⟩ : syracuseStep 1975973 = 370495) (by norm_num)
theorem B1975997 : Blo 1315976 1975997 := bbase (se 3 (by rfl) ⟨370499, by rfl⟩ : syracuseStep 1975997 = 740999) (by norm_num)
theorem B1976021 : Blo 1315976 1976021 := bbase (se 7 (by rfl) ⟨23156, by rfl⟩ : syracuseStep 1976021 = 46313) (by norm_num)
theorem B2221789 : Blo 1315976 2221789 := bbase (se 3 (by rfl) ⟨416585, by rfl⟩ : syracuseStep 2221789 = 833171) (by norm_num)
theorem B1976045 : Blo 1315976 1976045 := bbase (se 3 (by rfl) ⟨370508, by rfl⟩ : syracuseStep 1976045 = 741017) (by norm_num)
theorem B1976069 : Blo 1315976 1976069 := bbase (se 4 (by rfl) ⟨185256, by rfl⟩ : syracuseStep 1976069 = 370513) (by norm_num)
theorem B4441877 : Blo 1315976 4441877 := bbase (se 6 (by rfl) ⟨104106, by rfl⟩ : syracuseStep 4441877 = 208213) (by norm_num)
theorem B1976093 : Blo 1315976 1976093 := bbase (se 3 (by rfl) ⟨370517, by rfl⟩ : syracuseStep 1976093 = 741035) (by norm_num)
theorem B2221877 : Blo 1315976 2221877 := bbase (se 5 (by rfl) ⟨104150, by rfl⟩ : syracuseStep 2221877 = 208301) (by norm_num)
theorem B1976117 : Blo 1315976 1976117 := bbase (se 5 (by rfl) ⟨92630, by rfl⟩ : syracuseStep 1976117 = 185261) (by norm_num)
theorem B3336005 : Blo 1315976 3336005 := bbase (se 4 (by rfl) ⟨312750, by rfl⟩ : syracuseStep 3336005 = 625501) (by norm_num)
theorem B1976141 : Blo 1315976 1976141 := bbase (se 3 (by rfl) ⟨370526, by rfl⟩ : syracuseStep 1976141 = 741053) (by norm_num)
theorem B10004309 : Blo 1315976 10004309 := bbase (se 9 (by rfl) ⟨29309, by rfl⟩ : syracuseStep 10004309 = 58619) (by norm_num)
theorem B1976165 : Blo 1315976 1976165 := bbase (se 4 (by rfl) ⟨185265, by rfl⟩ : syracuseStep 1976165 = 370531) (by norm_num)
theorem B1976189 : Blo 1315976 1976189 := bbase (se 3 (by rfl) ⟨370535, by rfl⟩ : syracuseStep 1976189 = 741071) (by norm_num)
theorem B1976213 : Blo 1315976 1976213 := bbase (se 6 (by rfl) ⟨46317, by rfl⟩ : syracuseStep 1976213 = 92635) (by norm_num)
theorem B5621669 : Blo 1315976 5621669 := bbase (se 4 (by rfl) ⟨527031, by rfl⟩ : syracuseStep 5621669 = 1054063) (by norm_num)
theorem B1976237 : Blo 1315976 1976237 := bbase (se 3 (by rfl) ⟨370544, by rfl⟩ : syracuseStep 1976237 = 741089) (by norm_num)
theorem B1583021 : Blo 1315976 1583021 := bbase (se 3 (by rfl) ⟨296816, by rfl⟩ : syracuseStep 1583021 = 593633) (by norm_num)
theorem B2222005 : Blo 1315976 2222005 := bbase (se 5 (by rfl) ⟨104156, by rfl⟩ : syracuseStep 2222005 = 208313) (by norm_num)
theorem B1976261 : Blo 1315976 1976261 := bbase (se 4 (by rfl) ⟨185274, by rfl⟩ : syracuseStep 1976261 = 370549) (by norm_num)
theorem B2779085 : Blo 1315976 2779085 := bbase (se 3 (by rfl) ⟨521078, by rfl⟩ : syracuseStep 2779085 = 1042157) (by norm_num)
theorem B33736661 : Blo 1315976 33736661 := bbase (se 7 (by rfl) ⟨395351, by rfl⟩ : syracuseStep 33736661 = 790703) (by norm_num)
theorem B1976285 : Blo 1315976 1976285 := bbase (se 3 (by rfl) ⟨370553, by rfl⟩ : syracuseStep 1976285 = 741107) (by norm_num)
theorem B1583069 : Blo 1315976 1583069 := bbase (se 3 (by rfl) ⟨296825, by rfl⟩ : syracuseStep 1583069 = 593651) (by norm_num)
theorem B1976309 : Blo 1315976 1976309 := bbase (se 5 (by rfl) ⟨92639, by rfl⟩ : syracuseStep 1976309 = 185279) (by norm_num)
theorem B1689601 : Blo 1315976 1689601 := bbase (se 2 (by rfl) ⟨633600, by rfl⟩ : syracuseStep 1689601 = 1267201) (by norm_num)
theorem B2222093 : Blo 1315976 2222093 := bbase (se 3 (by rfl) ⟨416642, by rfl⟩ : syracuseStep 2222093 = 833285) (by norm_num)
theorem B1976333 : Blo 1315976 1976333 := bbase (se 3 (by rfl) ⟨370562, by rfl⟩ : syracuseStep 1976333 = 741125) (by norm_num)
theorem B2000933 : Blo 1315976 2000933 := bbase (se 4 (by rfl) ⟨187587, by rfl⟩ : syracuseStep 2000933 = 375175) (by norm_num)
theorem B3164197 : Blo 1315976 3164197 := bbase (se 4 (by rfl) ⟨296643, by rfl⟩ : syracuseStep 3164197 = 593287) (by norm_num)
theorem B2500645 : Blo 1315976 2500645 := bbase (se 4 (by rfl) ⟨234435, by rfl⟩ : syracuseStep 2500645 = 468871) (by norm_num)
theorem B1976357 : Blo 1315976 1976357 := bbase (se 4 (by rfl) ⟨185283, by rfl⟩ : syracuseStep 1976357 = 370567) (by norm_num)
theorem B1976381 : Blo 1315976 1976381 := bbase (se 3 (by rfl) ⟨370571, by rfl⟩ : syracuseStep 1976381 = 741143) (by norm_num)
theorem B6006869 : Blo 1315976 6006869 := bbase (se 8 (by rfl) ⟨35196, by rfl⟩ : syracuseStep 6006869 = 70393) (by norm_num)
theorem B1976405 : Blo 1315976 1976405 := bbase (se 8 (by rfl) ⟨11580, by rfl⟩ : syracuseStep 1976405 = 23161) (by norm_num)
theorem B1976429 : Blo 1315976 1976429 := bbase (se 3 (by rfl) ⟨370580, by rfl⟩ : syracuseStep 1976429 = 741161) (by norm_num)
theorem B3164293 : Blo 1315976 3164293 := bbase (se 4 (by rfl) ⟨296652, by rfl⟩ : syracuseStep 3164293 = 593305) (by norm_num)
theorem B1976453 : Blo 1315976 1976453 := bbase (se 4 (by rfl) ⟨185292, by rfl⟩ : syracuseStep 1976453 = 370585) (by norm_num)
theorem B1353865 : Blo 1315976 1353865 := bbase (se 2 (by rfl) ⟨507699, by rfl⟩ : syracuseStep 1353865 = 1015399) (by norm_num)
theorem B2222221 : Blo 1315976 2222221 := bbase (se 3 (by rfl) ⟨416666, by rfl⟩ : syracuseStep 2222221 = 833333) (by norm_num)
theorem B1976477 : Blo 1315976 1976477 := bbase (se 3 (by rfl) ⟨370589, by rfl⟩ : syracuseStep 1976477 = 741179) (by norm_num)
theorem B2500789 : Blo 1315976 2500789 := bbase (se 5 (by rfl) ⟨117224, by rfl⟩ : syracuseStep 2500789 = 234449) (by norm_num)
theorem B1976501 : Blo 1315976 1976501 := bbase (se 5 (by rfl) ⟨92648, by rfl⟩ : syracuseStep 1976501 = 185297) (by norm_num)
theorem B5621957 : Blo 1315976 5621957 := bbase (se 4 (by rfl) ⟨527058, by rfl⟩ : syracuseStep 5621957 = 1054117) (by norm_num)
theorem B4442309 : Blo 1315976 4442309 := bbase (se 4 (by rfl) ⟨416466, by rfl⟩ : syracuseStep 4442309 = 832933) (by norm_num)
theorem B1976525 : Blo 1315976 1976525 := bbase (se 3 (by rfl) ⟨370598, by rfl⟩ : syracuseStep 1976525 = 741197) (by norm_num)
theorem B1583329 : Blo 1315976 1583329 := bbase (se 2 (by rfl) ⟨593748, by rfl⟩ : syracuseStep 1583329 = 1187497) (by norm_num)
theorem B2812133 : Blo 1315976 2812133 := bbase (se 4 (by rfl) ⟨263637, by rfl⟩ : syracuseStep 2812133 = 527275) (by norm_num)
theorem B2222309 : Blo 1315976 2222309 := bbase (se 4 (by rfl) ⟨208341, by rfl⟩ : syracuseStep 2222309 = 416683) (by norm_num)
theorem B1976549 : Blo 1315976 1976549 := bbase (se 4 (by rfl) ⟨185301, by rfl⟩ : syracuseStep 1976549 = 370603) (by norm_num)
theorem B9996533 : Blo 1315976 9996533 := bbase (se 5 (by rfl) ⟨468587, by rfl⟩ : syracuseStep 9996533 = 937175) (by norm_num)
theorem B4221173 : Blo 1315976 4221173 := bbase (se 5 (by rfl) ⟨197867, by rfl⟩ : syracuseStep 4221173 = 395735) (by norm_num)
theorem B1976573 : Blo 1315976 1976573 := bbase (se 3 (by rfl) ⟨370607, by rfl⟩ : syracuseStep 1976573 = 741215) (by norm_num)
theorem B1976597 : Blo 1315976 1976597 := bbase (se 6 (by rfl) ⟨46326, by rfl⟩ : syracuseStep 1976597 = 92653) (by norm_num)
theorem B1976621 : Blo 1315976 1976621 := bbase (se 3 (by rfl) ⟨370616, by rfl⟩ : syracuseStep 1976621 = 741233) (by norm_num)
theorem B1976645 : Blo 1315976 1976645 := bbase (se 4 (by rfl) ⟨185310, by rfl⟩ : syracuseStep 1976645 = 370621) (by norm_num)
theorem B2500949 : Blo 1315976 2500949 := bbase (se 10 (by rfl) ⟨3663, by rfl⟩ : syracuseStep 2500949 = 7327) (by norm_num)
theorem B1976669 : Blo 1315976 1976669 := bbase (se 3 (by rfl) ⟨370625, by rfl⟩ : syracuseStep 1976669 = 741251) (by norm_num)
theorem B2222437 : Blo 1315976 2222437 := bbase (se 4 (by rfl) ⟨208353, by rfl⟩ : syracuseStep 2222437 = 416707) (by norm_num)
theorem B2812277 : Blo 1315976 2812277 := bbase (se 5 (by rfl) ⟨131825, by rfl⟩ : syracuseStep 2812277 = 263651) (by norm_num)
theorem B1976693 : Blo 1315976 1976693 := bbase (se 5 (by rfl) ⟨92657, by rfl⟩ : syracuseStep 1976693 = 185315) (by norm_num)
theorem B1976717 : Blo 1315976 1976717 := bbase (se 3 (by rfl) ⟨370634, by rfl⟩ : syracuseStep 1976717 = 741269) (by norm_num)
theorem B4999589 : Blo 1315976 4999589 := bbase (se 4 (by rfl) ⟨468711, by rfl⟩ : syracuseStep 4999589 = 937423) (by norm_num)
theorem B1976741 : Blo 1315976 1976741 := bbase (se 4 (by rfl) ⟨185319, by rfl⟩ : syracuseStep 1976741 = 370639) (by norm_num)
theorem B2222525 : Blo 1315976 2222525 := bbase (se 3 (by rfl) ⟨416723, by rfl⟩ : syracuseStep 2222525 = 833447) (by norm_num)
theorem B1976765 : Blo 1315976 1976765 := bbase (se 3 (by rfl) ⟨370643, by rfl⟩ : syracuseStep 1976765 = 741287) (by norm_num)
theorem B6326741 : Blo 1315976 6326741 := bbase (se 7 (by rfl) ⟨74141, by rfl⟩ : syracuseStep 6326741 = 148283) (by norm_num)
theorem B1976789 : Blo 1315976 1976789 := bbase (se 7 (by rfl) ⟨23165, by rfl⟩ : syracuseStep 1976789 = 46331) (by norm_num)
theorem B2501093 : Blo 1315976 2501093 := bbase (se 4 (by rfl) ⟨234477, by rfl⟩ : syracuseStep 2501093 = 468955) (by norm_num)
theorem B1976813 : Blo 1315976 1976813 := bbase (se 3 (by rfl) ⟨370652, by rfl⟩ : syracuseStep 1976813 = 741305) (by norm_num)
theorem B1976837 : Blo 1315976 1976837 := bbase (se 4 (by rfl) ⟨185328, by rfl⟩ : syracuseStep 1976837 = 370657) (by norm_num)
theorem B4745749 : Blo 1315976 4745749 := bbase (se 6 (by rfl) ⟨111228, by rfl⟩ : syracuseStep 4745749 = 222457) (by norm_num)
theorem B1976861 : Blo 1315976 1976861 := bbase (se 3 (by rfl) ⟨370661, by rfl⟩ : syracuseStep 1976861 = 741323) (by norm_num)
theorem B1976885 : Blo 1315976 1976885 := bbase (se 5 (by rfl) ⟨92666, by rfl⟩ : syracuseStep 1976885 = 185333) (by norm_num)
theorem B2222653 : Blo 1315976 2222653 := bbase (se 3 (by rfl) ⟨416747, by rfl⟩ : syracuseStep 2222653 = 833495) (by norm_num)
theorem B1665613 : Blo 1315976 1665613 := bbase (se 3 (by rfl) ⟨312302, by rfl⟩ : syracuseStep 1665613 = 624605) (by norm_num)
theorem B1976909 : Blo 1315976 1976909 := bbase (se 3 (by rfl) ⟨370670, by rfl⟩ : syracuseStep 1976909 = 741341) (by norm_num)
theorem B1976933 : Blo 1315976 1976933 := bbase (se 4 (by rfl) ⟨185337, by rfl⟩ : syracuseStep 1976933 = 370675) (by norm_num)
theorem B4442741 : Blo 1315976 4442741 := bbase (se 5 (by rfl) ⟨208253, by rfl⟩ : syracuseStep 4442741 = 416507) (by norm_num)
theorem B2108029 : Blo 1315976 2108029 := bbase (se 3 (by rfl) ⟨395255, by rfl⟩ : syracuseStep 2108029 = 790511) (by norm_num)
theorem B1976957 : Blo 1315976 1976957 := bbase (se 3 (by rfl) ⟨370679, by rfl⟩ : syracuseStep 1976957 = 741359) (by norm_num)
theorem B2001541 : Blo 1315976 2001541 := bbase (se 4 (by rfl) ⟨187644, by rfl⟩ : syracuseStep 2001541 = 375289) (by norm_num)
theorem B2222741 : Blo 1315976 2222741 := bbase (se 6 (by rfl) ⟨52095, by rfl⟩ : syracuseStep 2222741 = 104191) (by norm_num)
theorem B6670997 : Blo 1315976 6670997 := bbase (se 6 (by rfl) ⟨156351, by rfl⟩ : syracuseStep 6670997 = 312703) (by norm_num)
theorem B4999877 : Blo 1315976 4999877 := bbase (se 4 (by rfl) ⟨468738, by rfl⟩ : syracuseStep 4999877 = 937477) (by norm_num)
theorem B2534093 : Blo 1315976 2534093 := bbase (se 3 (by rfl) ⟨475142, by rfl⟩ : syracuseStep 2534093 = 950285) (by norm_num)
theorem B2812637 : Blo 1315976 2812637 := bbase (se 3 (by rfl) ⟨527369, by rfl⟩ : syracuseStep 2812637 = 1054739) (by norm_num)
theorem B1665785 : Blo 1315976 1665785 := bbase (se 2 (by rfl) ⟨624669, by rfl⟩ : syracuseStep 1665785 = 1249339) (by norm_num)
theorem B2501381 : Blo 1315976 2501381 := bbase (se 4 (by rfl) ⟨234504, by rfl⟩ : syracuseStep 2501381 = 469009) (by norm_num)
theorem B2222869 : Blo 1315976 2222869 := bbase (se 6 (by rfl) ⟨52098, by rfl⟩ : syracuseStep 2222869 = 104197) (by norm_num)
theorem B1665841 : Blo 1315976 1665841 := bbase (se 2 (by rfl) ⟨624690, by rfl⟩ : syracuseStep 1665841 = 1249381) (by norm_num)
theorem B1690417 : Blo 1315976 1690417 := bbase (se 2 (by rfl) ⟨633906, by rfl⟩ : syracuseStep 1690417 = 1267813) (by norm_num)
theorem B4746053 : Blo 1315976 4746053 := bbase (se 4 (by rfl) ⟨444942, by rfl⟩ : syracuseStep 4746053 = 889885) (by norm_num)
theorem B2222957 : Blo 1315976 2222957 := bbase (se 3 (by rfl) ⟨416804, by rfl⟩ : syracuseStep 2222957 = 833609) (by norm_num)
theorem B1665937 : Blo 1315976 1665937 := bbase (se 2 (by rfl) ⟨624726, by rfl⟩ : syracuseStep 1665937 = 1249453) (by norm_num)
theorem B2501533 : Blo 1315976 2501533 := bbase (se 3 (by rfl) ⟨469037, by rfl⟩ : syracuseStep 2501533 = 938075) (by norm_num)
theorem B5622709 : Blo 1315976 5622709 := bbase (se 5 (by rfl) ⟨263564, by rfl⟩ : syracuseStep 5622709 = 527129) (by norm_num)
theorem B2534341 : Blo 1315976 2534341 := bbase (se 4 (by rfl) ⟨237594, by rfl⟩ : syracuseStep 2534341 = 475189) (by norm_num)
theorem B3378133 : Blo 1315976 3378133 := bbase (se 7 (by rfl) ⟨39587, by rfl⟩ : syracuseStep 3378133 = 79175) (by norm_num)
theorem B2223085 : Blo 1315976 2223085 := bbase (se 3 (by rfl) ⟨416828, by rfl⟩ : syracuseStep 2223085 = 833657) (by norm_num)
theorem B4443173 : Blo 1315976 4443173 := bbase (se 4 (by rfl) ⟨416547, by rfl⟩ : syracuseStep 4443173 = 833095) (by norm_num)
theorem B1690669 : Blo 1315976 1690669 := bbase (se 3 (by rfl) ⟨317000, by rfl⟩ : syracuseStep 1690669 = 634001) (by norm_num)
theorem B6663221 : Blo 1315976 6663221 := bbase (se 5 (by rfl) ⟨312338, by rfl⟩ : syracuseStep 6663221 = 624677) (by norm_num)
theorem B1666109 : Blo 1315976 1666109 := bbase (se 3 (by rfl) ⟨312395, by rfl⟩ : syracuseStep 1666109 = 624791) (by norm_num)
theorem B2223173 : Blo 1315976 2223173 := bbase (se 4 (by rfl) ⟨208422, by rfl⟩ : syracuseStep 2223173 = 416845) (by norm_num)
theorem B1666165 : Blo 1315976 1666165 := bbase (se 5 (by rfl) ⟨78101, by rfl⟩ : syracuseStep 1666165 = 156203) (by norm_num)
theorem B6089861 : Blo 1315976 6089861 := bbase (se 4 (by rfl) ⟨570924, by rfl⟩ : syracuseStep 6089861 = 1141849) (by norm_num)
theorem B2223301 : Blo 1315976 2223301 := bbase (se 4 (by rfl) ⟨208434, by rfl⟩ : syracuseStep 2223301 = 416869) (by norm_num)
theorem B3165389 : Blo 1315976 3165389 := bbase (se 3 (by rfl) ⟨593510, by rfl⟩ : syracuseStep 3165389 = 1187021) (by norm_num)
theorem B2501837 : Blo 1315976 2501837 := bbase (se 3 (by rfl) ⟨469094, by rfl⟩ : syracuseStep 2501837 = 938189) (by norm_num)
theorem B1666261 : Blo 1315976 1666261 := bbase (se 7 (by rfl) ⟨19526, by rfl⟩ : syracuseStep 1666261 = 39053) (by norm_num)
theorem B6753557 : Blo 1315976 6753557 := bbase (se 6 (by rfl) ⟨158286, by rfl⟩ : syracuseStep 6753557 = 316573) (by norm_num)
theorem B2223389 : Blo 1315976 2223389 := bbase (se 3 (by rfl) ⟨416885, by rfl⟩ : syracuseStep 2223389 = 833771) (by norm_num)
theorem B1666433 : Blo 1315976 1666433 := bbase (se 2 (by rfl) ⟨624912, by rfl⟩ : syracuseStep 1666433 = 1249825) (by norm_num)
theorem B2223517 : Blo 1315976 2223517 := bbase (se 3 (by rfl) ⟨416909, by rfl⟩ : syracuseStep 2223517 = 833819) (by norm_num)
theorem B1666489 : Blo 1315976 1666489 := bbase (se 2 (by rfl) ⟨624933, by rfl⟩ : syracuseStep 1666489 = 1249867) (by norm_num)
theorem B4443605 : Blo 1315976 4443605 := bbase (se 7 (by rfl) ⟨52073, by rfl⟩ : syracuseStep 4443605 = 104147) (by norm_num)
theorem B2223605 : Blo 1315976 2223605 := bbase (se 5 (by rfl) ⟨104231, by rfl⟩ : syracuseStep 2223605 = 208463) (by norm_num)
theorem B1666585 : Blo 1315976 1666585 := bbase (se 2 (by rfl) ⟨624969, by rfl⟩ : syracuseStep 1666585 = 1249939) (by norm_num)
theorem B2960981 : Blo 1315976 2960981 := bbase (se 8 (by rfl) ⟨17349, by rfl⟩ : syracuseStep 2960981 = 34699) (by norm_num)
theorem B2813525 : Blo 1315976 2813525 := bbase (se 8 (by rfl) ⟨16485, by rfl⟩ : syracuseStep 2813525 = 32971) (by norm_num)
theorem B2223733 : Blo 1315976 2223733 := bbase (se 5 (by rfl) ⟨104237, by rfl⟩ : syracuseStep 2223733 = 208475) (by norm_num)
theorem B5623445 : Blo 1315976 5623445 := bbase (se 6 (by rfl) ⟨131799, by rfl⟩ : syracuseStep 5623445 = 263599) (by norm_num)
theorem B2961053 : Blo 1315976 2961053 := bbase (se 3 (by rfl) ⟨555197, by rfl⟩ : syracuseStep 2961053 = 1110395) (by norm_num)
theorem B1502885 : Blo 1315976 1502885 := bbase (se 4 (by rfl) ⟨140895, by rfl⟩ : syracuseStep 1502885 = 281791) (by norm_num)
theorem B1666757 : Blo 1315976 1666757 := bbase (se 4 (by rfl) ⟨156258, by rfl⟩ : syracuseStep 1666757 = 312517) (by norm_num)
theorem B2223821 : Blo 1315976 2223821 := bbase (se 3 (by rfl) ⟨416966, by rfl⟩ : syracuseStep 2223821 = 833933) (by norm_num)
theorem B2961125 : Blo 1315976 2961125 := bbase (se 4 (by rfl) ⟨277605, by rfl⟩ : syracuseStep 2961125 = 555211) (by norm_num)
theorem B1666813 : Blo 1315976 1666813 := bbase (se 3 (by rfl) ⟨312527, by rfl⟩ : syracuseStep 1666813 = 625055) (by norm_num)
theorem B2961197 : Blo 1315976 2961197 := bbase (se 3 (by rfl) ⟨555224, by rfl⟩ : syracuseStep 2961197 = 1110449) (by norm_num)
theorem B2002733 : Blo 1315976 2002733 := bbase (se 3 (by rfl) ⟨375512, by rfl⟩ : syracuseStep 2002733 = 751025) (by norm_num)
theorem B3747653 : Blo 1315976 3747653 := bbase (se 4 (by rfl) ⟨351342, by rfl⟩ : syracuseStep 3747653 = 702685) (by norm_num)
theorem B2813773 : Blo 1315976 2813773 := bbase (se 3 (by rfl) ⟨527582, by rfl⟩ : syracuseStep 2813773 = 1055165) (by norm_num)
theorem B2223949 : Blo 1315976 2223949 := bbase (se 3 (by rfl) ⟨416990, by rfl⟩ : syracuseStep 2223949 = 833981) (by norm_num)
theorem B1666909 : Blo 1315976 1666909 := bbase (se 3 (by rfl) ⟨312545, by rfl⟩ : syracuseStep 1666909 = 625091) (by norm_num)
theorem B5001061 : Blo 1315976 5001061 := bbase (se 4 (by rfl) ⟨468849, by rfl⟩ : syracuseStep 5001061 = 937699) (by norm_num)
theorem B2961269 : Blo 1315976 2961269 := bbase (se 5 (by rfl) ⟨138809, by rfl⟩ : syracuseStep 2961269 = 277619) (by norm_num)
theorem B4444037 : Blo 1315976 4444037 := bbase (se 4 (by rfl) ⟨416628, by rfl⟩ : syracuseStep 4444037 = 833257) (by norm_num)
theorem B2224037 : Blo 1315976 2224037 := bbase (se 4 (by rfl) ⟨208503, by rfl⟩ : syracuseStep 2224037 = 417007) (by norm_num)
theorem B2961341 : Blo 1315976 2961341 := bbase (se 3 (by rfl) ⟨555251, by rfl⟩ : syracuseStep 2961341 = 1110503) (by norm_num)
theorem B2109413 : Blo 1315976 2109413 := bbase (se 4 (by rfl) ⟨197757, by rfl⟩ : syracuseStep 2109413 = 395515) (by norm_num)
theorem B2961413 : Blo 1315976 2961413 := bbase (se 4 (by rfl) ⟨277632, by rfl⟩ : syracuseStep 2961413 = 555265) (by norm_num)
theorem B1667081 : Blo 1315976 1667081 := bbase (se 2 (by rfl) ⟨625155, by rfl⟩ : syracuseStep 1667081 = 1250311) (by norm_num)
theorem B1667137 : Blo 1315976 1667137 := bbase (se 2 (by rfl) ⟨625176, by rfl⟩ : syracuseStep 1667137 = 1250353) (by norm_num)
theorem B2961485 : Blo 1315976 2961485 := bbase (se 3 (by rfl) ⟨555278, by rfl⟩ : syracuseStep 2961485 = 1110557) (by norm_num)
theorem B7499861 : Blo 1315976 7499861 := bbase (se 8 (by rfl) ⟨43944, by rfl⟩ : syracuseStep 7499861 = 87889) (by norm_num)
theorem B3166349 : Blo 1315976 3166349 := bbase (se 3 (by rfl) ⟨593690, by rfl⟩ : syracuseStep 3166349 = 1187381) (by norm_num)
theorem B2961557 : Blo 1315976 2961557 := bbase (se 6 (by rfl) ⟨69411, by rfl⟩ : syracuseStep 2961557 = 138823) (by norm_num)
theorem B5001365 : Blo 1315976 5001365 := bbase (se 6 (by rfl) ⟨117219, by rfl⟩ : syracuseStep 5001365 = 234439) (by norm_num)
theorem B1667233 : Blo 1315976 1667233 := bbase (se 2 (by rfl) ⟨625212, by rfl⟩ : syracuseStep 1667233 = 1250425) (by norm_num)
theorem B2961629 : Blo 1315976 2961629 := bbase (se 3 (by rfl) ⟨555305, by rfl⟩ : syracuseStep 2961629 = 1110611) (by norm_num)
theorem B4002085 : Blo 1315976 4002085 := bbase (se 4 (by rfl) ⟨375195, by rfl⟩ : syracuseStep 4002085 = 750391) (by norm_num)
theorem B2961701 : Blo 1315976 2961701 := bbase (se 4 (by rfl) ⟨277659, by rfl⟩ : syracuseStep 2961701 = 555319) (by norm_num)
theorem B4444469 : Blo 1315976 4444469 := bbase (se 5 (by rfl) ⟨208334, by rfl⟩ : syracuseStep 4444469 = 416669) (by norm_num)
theorem B6664517 : Blo 1315976 6664517 := bbase (se 4 (by rfl) ⟨624798, by rfl⟩ : syracuseStep 6664517 = 1249597) (by norm_num)
theorem B2814277 : Blo 1315976 2814277 := bbase (se 4 (by rfl) ⟨263838, by rfl⟩ : syracuseStep 2814277 = 527677) (by norm_num)
theorem B1667405 : Blo 1315976 1667405 := bbase (se 3 (by rfl) ⟨312638, by rfl⟩ : syracuseStep 1667405 = 625277) (by norm_num)
theorem B2961773 : Blo 1315976 2961773 := bbase (se 3 (by rfl) ⟨555332, by rfl⟩ : syracuseStep 2961773 = 1110665) (by norm_num)
theorem B1667461 : Blo 1315976 1667461 := bbase (se 4 (by rfl) ⟨156324, by rfl⟩ : syracuseStep 1667461 = 312649) (by norm_num)
theorem B3658133 : Blo 1315976 3658133 := bbase (se 6 (by rfl) ⟨85737, by rfl⟩ : syracuseStep 3658133 = 171475) (by norm_num)
theorem B2961845 : Blo 1315976 2961845 := bbase (se 5 (by rfl) ⟨138836, by rfl⟩ : syracuseStep 2961845 = 277673) (by norm_num)
theorem B1667557 : Blo 1315976 1667557 := bbase (se 4 (by rfl) ⟨156333, by rfl⟩ : syracuseStep 1667557 = 312667) (by norm_num)
theorem B2961917 : Blo 1315976 2961917 := bbase (se 3 (by rfl) ⟨555359, by rfl⟩ : syracuseStep 2961917 = 1110719) (by norm_num)
theorem B2961989 : Blo 1315976 2961989 := bbase (se 4 (by rfl) ⟨277686, by rfl⟩ : syracuseStep 2961989 = 555373) (by norm_num)
theorem B2962061 : Blo 1315976 2962061 := bbase (se 3 (by rfl) ⟨555386, by rfl⟩ : syracuseStep 2962061 = 1110773) (by norm_num)
theorem B1667729 : Blo 1315976 1667729 := bbase (se 2 (by rfl) ⟨625398, by rfl⟩ : syracuseStep 1667729 = 1250797) (by norm_num)
theorem B9491093 : Blo 1315976 9491093 := bbase (se 6 (by rfl) ⟨222447, by rfl⟩ : syracuseStep 9491093 = 444895) (by norm_num)
theorem B3043997 : Blo 1315976 3043997 := bbase (se 3 (by rfl) ⟨570749, by rfl⟩ : syracuseStep 3043997 = 1141499) (by norm_num)
theorem B1667785 : Blo 1315976 1667785 := bbase (se 2 (by rfl) ⟨625419, by rfl⟩ : syracuseStep 1667785 = 1250839) (by norm_num)
theorem B2962133 : Blo 1315976 2962133 := bbase (se 7 (by rfl) ⟨34712, by rfl⟩ : syracuseStep 2962133 = 69425) (by norm_num)
theorem B1405669 : Blo 1315976 1405669 := bbase (se 4 (by rfl) ⟨131781, by rfl⟩ : syracuseStep 1405669 = 263563) (by norm_num)
theorem B4444901 : Blo 1315976 4444901 := bbase (se 4 (by rfl) ⟨416709, by rfl⟩ : syracuseStep 4444901 = 833419) (by norm_num)
theorem B3560197 : Blo 1315976 3560197 := bbase (se 4 (by rfl) ⟨333768, by rfl⟩ : syracuseStep 3560197 = 667537) (by norm_num)
theorem B2962205 : Blo 1315976 2962205 := bbase (se 3 (by rfl) ⟨555413, by rfl⟩ : syracuseStep 2962205 = 1110827) (by norm_num)
theorem B2888485 : Blo 1315976 2888485 := bbase (se 4 (by rfl) ⟨270795, by rfl⟩ : syracuseStep 2888485 = 541591) (by norm_num)
theorem B1667881 : Blo 1315976 1667881 := bbase (se 2 (by rfl) ⟨625455, by rfl⟩ : syracuseStep 1667881 = 1250911) (by norm_num)
theorem B8557397 : Blo 1315976 8557397 := bbase (se 9 (by rfl) ⟨25070, by rfl⟩ : syracuseStep 8557397 = 50141) (by norm_num)
theorem B1405793 : Blo 1315976 1405793 := bbase (se 2 (by rfl) ⟨527172, by rfl⟩ : syracuseStep 1405793 = 1054345) (by norm_num)
theorem B2962277 : Blo 1315976 2962277 := bbase (se 4 (by rfl) ⟨277713, by rfl⟩ : syracuseStep 2962277 = 555427) (by norm_num)
theorem B2372485 : Blo 1315976 2372485 := bbase (se 4 (by rfl) ⟨222420, by rfl⟩ : syracuseStep 2372485 = 444841) (by norm_num)
theorem B2110349 : Blo 1315976 2110349 := bbase (se 3 (by rfl) ⟨395690, by rfl⟩ : syracuseStep 2110349 = 791381) (by norm_num)
theorem B2962349 : Blo 1315976 2962349 := bbase (se 3 (by rfl) ⟨555440, by rfl⟩ : syracuseStep 2962349 = 1110881) (by norm_num)
theorem B1668053 : Blo 1315976 1668053 := bbase (se 7 (by rfl) ⟨19547, by rfl⟩ : syracuseStep 1668053 = 39095) (by norm_num)
theorem B3748837 : Blo 1315976 3748837 := bbase (se 4 (by rfl) ⟨351453, by rfl⟩ : syracuseStep 3748837 = 702907) (by norm_num)
theorem B2962421 : Blo 1315976 2962421 := bbase (se 5 (by rfl) ⟨138863, by rfl⟩ : syracuseStep 2962421 = 277727) (by norm_num)
theorem B2962493 : Blo 1315976 2962493 := bbase (se 3 (by rfl) ⟨555467, by rfl⟩ : syracuseStep 2962493 = 1110935) (by norm_num)
theorem B3331165 : Blo 1315976 3331165 := bbase (se 3 (by rfl) ⟨624593, by rfl⟩ : syracuseStep 3331165 = 1249187) (by norm_num)
theorem B1406045 : Blo 1315976 1406045 := bbase (se 3 (by rfl) ⟨263633, by rfl⟩ : syracuseStep 1406045 = 527267) (by norm_num)
theorem B3748997 : Blo 1315976 3748997 := bbase (se 4 (by rfl) ⟨351468, by rfl⟩ : syracuseStep 3748997 = 702937) (by norm_num)
theorem B2962565 : Blo 1315976 2962565 := bbase (se 4 (by rfl) ⟨277740, by rfl⟩ : syracuseStep 2962565 = 555481) (by norm_num)
theorem B4445333 : Blo 1315976 4445333 := bbase (se 6 (by rfl) ⟨104187, by rfl⟩ : syracuseStep 4445333 = 208375) (by norm_num)
theorem B3003581 : Blo 1315976 3003581 := bbase (se 3 (by rfl) ⟨563171, by rfl⟩ : syracuseStep 3003581 = 1126343) (by norm_num)
theorem B3331277 : Blo 1315976 3331277 := bbase (se 3 (by rfl) ⟨624614, by rfl⟩ : syracuseStep 3331277 = 1249229) (by norm_num)
theorem B2962637 : Blo 1315976 2962637 := bbase (se 3 (by rfl) ⟨555494, by rfl⟩ : syracuseStep 2962637 = 1110989) (by norm_num)
theorem B7501045 : Blo 1315976 7501045 := bbase (se 5 (by rfl) ⟨351611, by rfl⟩ : syracuseStep 7501045 = 703223) (by norm_num)
theorem B2962709 : Blo 1315976 2962709 := bbase (se 6 (by rfl) ⟨69438, by rfl⟩ : syracuseStep 2962709 = 138877) (by norm_num)
theorem B2372917 : Blo 1315976 2372917 := bbase (se 5 (by rfl) ⟨111230, by rfl⟩ : syracuseStep 2372917 = 222461) (by norm_num)
theorem B2962781 : Blo 1315976 2962781 := bbase (se 3 (by rfl) ⟨555521, by rfl⟩ : syracuseStep 2962781 = 1111043) (by norm_num)
theorem B3749237 : Blo 1315976 3749237 := bbase (se 5 (by rfl) ⟨175745, by rfl⟩ : syracuseStep 3749237 = 351491) (by norm_num)
theorem B3331469 : Blo 1315976 3331469 := bbase (se 3 (by rfl) ⟨624650, by rfl⟩ : syracuseStep 3331469 = 1249301) (by norm_num)
theorem B2962853 : Blo 1315976 2962853 := bbase (se 4 (by rfl) ⟨277767, by rfl⟩ : syracuseStep 2962853 = 555535) (by norm_num)
theorem B4003253 : Blo 1315976 4003253 := bbase (se 5 (by rfl) ⟨187652, by rfl⟩ : syracuseStep 4003253 = 375305) (by norm_num)
theorem B2962925 : Blo 1315976 2962925 := bbase (se 3 (by rfl) ⟨555548, by rfl⟩ : syracuseStep 2962925 = 1111097) (by norm_num)
theorem B2110997 : Blo 1315976 2110997 := bbase (se 6 (by rfl) ⟨49476, by rfl⟩ : syracuseStep 2110997 = 98953) (by norm_num)
theorem B1406489 : Blo 1315976 1406489 := bbase (se 2 (by rfl) ⟨527433, by rfl⟩ : syracuseStep 1406489 = 1054867) (by norm_num)
theorem B3749429 : Blo 1315976 3749429 := bbase (se 5 (by rfl) ⟨175754, by rfl⟩ : syracuseStep 3749429 = 351509) (by norm_num)
theorem B2962997 : Blo 1315976 2962997 := bbase (se 5 (by rfl) ⟨138890, by rfl⟩ : syracuseStep 2962997 = 277781) (by norm_num)
theorem B4445765 : Blo 1315976 4445765 := bbase (se 4 (by rfl) ⟨416790, by rfl⟩ : syracuseStep 4445765 = 833581) (by norm_num)
theorem B6665813 : Blo 1315976 6665813 := bbase (se 8 (by rfl) ⟨39057, by rfl⟩ : syracuseStep 6665813 = 78115) (by norm_num)
theorem B2963069 : Blo 1315976 2963069 := bbase (se 3 (by rfl) ⟨555575, by rfl⟩ : syracuseStep 2963069 = 1111151) (by norm_num)
theorem B2963141 : Blo 1315976 2963141 := bbase (se 4 (by rfl) ⟨277794, by rfl⟩ : syracuseStep 2963141 = 555589) (by norm_num)
theorem B3331813 : Blo 1315976 3331813 := bbase (se 4 (by rfl) ⟨312357, by rfl⟩ : syracuseStep 3331813 = 624715) (by norm_num)
theorem B2963213 : Blo 1315976 2963213 := bbase (se 3 (by rfl) ⟨555602, by rfl⟩ : syracuseStep 2963213 = 1111205) (by norm_num)
theorem B2569997 : Blo 1315976 2569997 := bbase (se 3 (by rfl) ⟨481874, by rfl⟩ : syracuseStep 2569997 = 963749) (by norm_num)
theorem B1406737 : Blo 1315976 1406737 := bbase (se 2 (by rfl) ⟨527526, by rfl⟩ : syracuseStep 1406737 = 1055053) (by norm_num)
theorem B1480477 : Blo 1315976 1480477 := bbase (se 3 (by rfl) ⟨277589, by rfl⟩ : syracuseStep 1480477 = 555179) (by norm_num)
theorem B2373437 : Blo 1315976 2373437 := bbase (se 3 (by rfl) ⟨445019, by rfl⟩ : syracuseStep 2373437 = 890039) (by norm_num)
theorem B1480513 : Blo 1315976 1480513 := bbase (se 2 (by rfl) ⟨555192, by rfl⟩ : syracuseStep 1480513 = 1110385) (by norm_num)
theorem B3331925 : Blo 1315976 3331925 := bbase (se 9 (by rfl) ⟨9761, by rfl⟩ : syracuseStep 3331925 = 19523) (by norm_num)
theorem B2963285 : Blo 1315976 2963285 := bbase (se 9 (by rfl) ⟨8681, by rfl⟩ : syracuseStep 2963285 = 17363) (by norm_num)
theorem B1480549 : Blo 1315976 1480549 := bbase (se 4 (by rfl) ⟨138801, by rfl⟩ : syracuseStep 1480549 = 277603) (by norm_num)
theorem B1480585 : Blo 1315976 1480585 := bbase (se 2 (by rfl) ⟨555219, by rfl⟩ : syracuseStep 1480585 = 1110439) (by norm_num)
theorem B2963357 : Blo 1315976 2963357 := bbase (se 3 (by rfl) ⟨555629, by rfl⟩ : syracuseStep 2963357 = 1111259) (by norm_num)
theorem B1480621 : Blo 1315976 1480621 := bbase (se 3 (by rfl) ⟨277616, by rfl⟩ : syracuseStep 1480621 = 555233) (by norm_num)
theorem B1480657 : Blo 1315976 1480657 := bbase (se 2 (by rfl) ⟨555246, by rfl⟩ : syracuseStep 1480657 = 1110493) (by norm_num)
theorem B2963429 : Blo 1315976 2963429 := bbase (se 4 (by rfl) ⟨277821, by rfl⟩ : syracuseStep 2963429 = 555643) (by norm_num)
theorem B1480693 : Blo 1315976 1480693 := bbase (se 5 (by rfl) ⟨69407, by rfl⟩ : syracuseStep 1480693 = 138815) (by norm_num)
theorem B4446197 : Blo 1315976 4446197 := bbase (se 5 (by rfl) ⟨208415, by rfl⟩ : syracuseStep 4446197 = 416831) (by norm_num)
theorem B3332117 : Blo 1315976 3332117 := bbase (se 6 (by rfl) ⟨78096, by rfl⟩ : syracuseStep 3332117 = 156193) (by norm_num)
theorem B1480729 : Blo 1315976 1480729 := bbase (se 2 (by rfl) ⟨555273, by rfl⟩ : syracuseStep 1480729 = 1110547) (by norm_num)
theorem B2963501 : Blo 1315976 2963501 := bbase (se 3 (by rfl) ⟨555656, by rfl⟩ : syracuseStep 2963501 = 1111313) (by norm_num)
theorem B1480765 : Blo 1315976 1480765 := bbase (se 3 (by rfl) ⟨277643, by rfl⟩ : syracuseStep 1480765 = 555287) (by norm_num)
theorem B2373725 : Blo 1315976 2373725 := bbase (se 3 (by rfl) ⟨445073, by rfl⟩ : syracuseStep 2373725 = 890147) (by norm_num)
theorem B1480801 : Blo 1315976 1480801 := bbase (se 2 (by rfl) ⟨555300, by rfl⟩ : syracuseStep 1480801 = 1110601) (by norm_num)
theorem B6330469 : Blo 1315976 6330469 := bbase (se 4 (by rfl) ⟨593481, by rfl⟩ : syracuseStep 6330469 = 1186963) (by norm_num)
theorem B2963573 : Blo 1315976 2963573 := bbase (se 5 (by rfl) ⟨138917, by rfl⟩ : syracuseStep 2963573 = 277835) (by norm_num)
theorem B4274309 : Blo 1315976 4274309 := bbase (se 4 (by rfl) ⟨400716, by rfl⟩ : syracuseStep 4274309 = 801433) (by norm_num)
theorem B1480837 : Blo 1315976 1480837 := bbase (se 4 (by rfl) ⟨138828, by rfl⟩ : syracuseStep 1480837 = 277657) (by norm_num)
theorem B4216981 : Blo 1315976 4216981 := bbase (se 6 (by rfl) ⟨98835, by rfl⟩ : syracuseStep 4216981 = 197671) (by norm_num)
theorem B8124565 : Blo 1315976 8124565 := bbase (se 6 (by rfl) ⟨190419, by rfl⟩ : syracuseStep 8124565 = 380839) (by norm_num)
theorem B1480873 : Blo 1315976 1480873 := bbase (se 2 (by rfl) ⟨555327, by rfl⟩ : syracuseStep 1480873 = 1110655) (by norm_num)
theorem B2963645 : Blo 1315976 2963645 := bbase (se 3 (by rfl) ⟨555683, by rfl⟩ : syracuseStep 2963645 = 1111367) (by norm_num)
theorem B1874117 : Blo 1315976 1874117 := bbase (se 4 (by rfl) ⟨175698, by rfl⟩ : syracuseStep 1874117 = 351397) (by norm_num)
theorem B1480909 : Blo 1315976 1480909 := bbase (se 3 (by rfl) ⟨277670, by rfl⟩ : syracuseStep 1480909 = 555341) (by norm_num)
theorem B1407181 : Blo 1315976 1407181 := bbase (se 3 (by rfl) ⟨263846, by rfl⟩ : syracuseStep 1407181 = 527693) (by norm_num)
theorem B5003477 : Blo 1315976 5003477 := bbase (se 7 (by rfl) ⟨58634, by rfl⟩ : syracuseStep 5003477 = 117269) (by norm_num)
theorem B1480945 : Blo 1315976 1480945 := bbase (se 2 (by rfl) ⟨555354, by rfl⟩ : syracuseStep 1480945 = 1110709) (by norm_num)
theorem B2963717 : Blo 1315976 2963717 := bbase (se 4 (by rfl) ⟨277848, by rfl⟩ : syracuseStep 2963717 = 555697) (by norm_num)
theorem B1407241 : Blo 1315976 1407241 := bbase (se 2 (by rfl) ⟨527715, by rfl⟩ : syracuseStep 1407241 = 1055431) (by norm_num)
theorem B1480981 : Blo 1315976 1480981 := bbase (se 6 (by rfl) ⟨34710, by rfl⟩ : syracuseStep 1480981 = 69421) (by norm_num)
theorem B8444213 : Blo 1315976 8444213 := bbase (se 5 (by rfl) ⟨395822, by rfl⟩ : syracuseStep 8444213 = 791645) (by norm_num)
theorem B1481017 : Blo 1315976 1481017 := bbase (se 2 (by rfl) ⟨555381, by rfl⟩ : syracuseStep 1481017 = 1110763) (by norm_num)
theorem B2406725 : Blo 1315976 2406725 := bbase (se 4 (by rfl) ⟨225630, by rfl⟩ : syracuseStep 2406725 = 451261) (by norm_num)
theorem B2963789 : Blo 1315976 2963789 := bbase (se 3 (by rfl) ⟨555710, by rfl⟩ : syracuseStep 2963789 = 1111421) (by norm_num)
theorem B1481053 : Blo 1315976 1481053 := bbase (se 3 (by rfl) ⟨277697, by rfl⟩ : syracuseStep 1481053 = 555395) (by norm_num)
theorem B3332461 : Blo 1315976 3332461 := bbase (se 3 (by rfl) ⟨624836, by rfl⟩ : syracuseStep 3332461 = 1249673) (by norm_num)
theorem B1481089 : Blo 1315976 1481089 := bbase (se 2 (by rfl) ⟨555408, by rfl⟩ : syracuseStep 1481089 = 1110817) (by norm_num)
theorem B2963861 : Blo 1315976 2963861 := bbase (se 6 (by rfl) ⟨69465, by rfl⟩ : syracuseStep 2963861 = 138931) (by norm_num)
theorem B6412709 : Blo 1315976 6412709 := bbase (se 4 (by rfl) ⟨601191, by rfl⟩ : syracuseStep 6412709 = 1202383) (by norm_num)
theorem B1481125 : Blo 1315976 1481125 := bbase (se 4 (by rfl) ⟨138855, by rfl⟩ : syracuseStep 1481125 = 277711) (by norm_num)
theorem B4446629 : Blo 1315976 4446629 := bbase (se 4 (by rfl) ⟨416871, by rfl⟩ : syracuseStep 4446629 = 833743) (by norm_num)
theorem B1481161 : Blo 1315976 1481161 := bbase (se 2 (by rfl) ⟨555435, by rfl⟩ : syracuseStep 1481161 = 1110871) (by norm_num)
theorem B3332573 : Blo 1315976 3332573 := bbase (se 3 (by rfl) ⟨624857, by rfl⟩ : syracuseStep 3332573 = 1249715) (by norm_num)
theorem B2963933 : Blo 1315976 2963933 := bbase (se 3 (by rfl) ⟨555737, by rfl⟩ : syracuseStep 2963933 = 1111475) (by norm_num)
theorem B1481197 : Blo 1315976 1481197 := bbase (se 3 (by rfl) ⟨277724, by rfl⟩ : syracuseStep 1481197 = 555449) (by norm_num)
theorem B5003765 : Blo 1315976 5003765 := bbase (se 5 (by rfl) ⟨234551, by rfl⟩ : syracuseStep 5003765 = 469103) (by norm_num)
theorem B3045893 : Blo 1315976 3045893 := bbase (se 4 (by rfl) ⟨285552, by rfl⟩ : syracuseStep 3045893 = 571105) (by norm_num)
theorem B2374157 : Blo 1315976 2374157 := bbase (se 3 (by rfl) ⟨445154, by rfl⟩ : syracuseStep 2374157 = 890309) (by norm_num)
theorem B1481233 : Blo 1315976 1481233 := bbase (se 2 (by rfl) ⟨555462, by rfl⟩ : syracuseStep 1481233 = 1110925) (by norm_num)
theorem B3750421 : Blo 1315976 3750421 := bbase (se 6 (by rfl) ⟨87900, by rfl⟩ : syracuseStep 3750421 = 175801) (by norm_num)
theorem B2964005 : Blo 1315976 2964005 := bbase (se 4 (by rfl) ⟨277875, by rfl⟩ : syracuseStep 2964005 = 555751) (by norm_num)
theorem B1481269 : Blo 1315976 1481269 := bbase (se 5 (by rfl) ⟨69434, by rfl⟩ : syracuseStep 1481269 = 138869) (by norm_num)
theorem B1481305 : Blo 1315976 1481305 := bbase (se 2 (by rfl) ⟨555489, by rfl⟩ : syracuseStep 1481305 = 1110979) (by norm_num)
theorem B2964077 : Blo 1315976 2964077 := bbase (se 3 (by rfl) ⟨555764, by rfl⟩ : syracuseStep 2964077 = 1111529) (by norm_num)
theorem B1481341 : Blo 1315976 1481341 := bbase (se 3 (by rfl) ⟨277751, by rfl⟩ : syracuseStep 1481341 = 555503) (by norm_num)
theorem B3332765 : Blo 1315976 3332765 := bbase (se 3 (by rfl) ⟨624893, by rfl⟩ : syracuseStep 3332765 = 1249787) (by norm_num)
theorem B2374301 : Blo 1315976 2374301 := bbase (se 3 (by rfl) ⟨445181, by rfl⟩ : syracuseStep 2374301 = 890363) (by norm_num)
theorem B1481377 : Blo 1315976 1481377 := bbase (se 2 (by rfl) ⟨555516, by rfl⟩ : syracuseStep 1481377 = 1111033) (by norm_num)
theorem B2964149 : Blo 1315976 2964149 := bbase (se 5 (by rfl) ⟨138944, by rfl⟩ : syracuseStep 2964149 = 277889) (by norm_num)
theorem B1481413 : Blo 1315976 1481413 := bbase (se 4 (by rfl) ⟨138882, by rfl⟩ : syracuseStep 1481413 = 277765) (by norm_num)
theorem B1481449 : Blo 1315976 1481449 := bbase (se 2 (by rfl) ⟨555543, by rfl⟩ : syracuseStep 1481449 = 1111087) (by norm_num)
theorem B1874669 : Blo 1315976 1874669 := bbase (se 3 (by rfl) ⟨351500, by rfl⟩ : syracuseStep 1874669 = 703001) (by norm_num)
theorem B2964221 : Blo 1315976 2964221 := bbase (se 3 (by rfl) ⟨555791, by rfl⟩ : syracuseStep 2964221 = 1111583) (by norm_num)
theorem B1481485 : Blo 1315976 1481485 := bbase (se 3 (by rfl) ⟨277778, by rfl⟩ : syracuseStep 1481485 = 555557) (by norm_num)
theorem B1481521 : Blo 1315976 1481521 := bbase (se 2 (by rfl) ⟨555570, by rfl⟩ : syracuseStep 1481521 = 1111141) (by norm_num)
theorem B1334081 : Blo 1315976 1334081 := bbase (se 2 (by rfl) ⟨500280, by rfl⟩ : syracuseStep 1334081 = 1000561) (by norm_num)
theorem B2964293 : Blo 1315976 2964293 := bbase (se 4 (by rfl) ⟨277902, by rfl⟩ : syracuseStep 2964293 = 555805) (by norm_num)
theorem B1481557 : Blo 1315976 1481557 := bbase (se 9 (by rfl) ⟨4340, by rfl⟩ : syracuseStep 1481557 = 8681) (by norm_num)
theorem B4447061 : Blo 1315976 4447061 := bbase (se 9 (by rfl) ⟨13028, by rfl⟩ : syracuseStep 4447061 = 26057) (by norm_num)
theorem B6667109 : Blo 1315976 6667109 := bbase (se 4 (by rfl) ⟨625041, by rfl⟩ : syracuseStep 6667109 = 1250083) (by norm_num)
theorem B5626741 : Blo 1315976 5626741 := bbase (se 5 (by rfl) ⟨263753, by rfl⟩ : syracuseStep 5626741 = 527507) (by norm_num)
theorem B1481593 : Blo 1315976 1481593 := bbase (se 2 (by rfl) ⟨555597, by rfl⟩ : syracuseStep 1481593 = 1111195) (by norm_num)
theorem B2964365 : Blo 1315976 2964365 := bbase (se 3 (by rfl) ⟨555818, by rfl⟩ : syracuseStep 2964365 = 1111637) (by norm_num)
theorem B1481629 : Blo 1315976 1481629 := bbase (se 3 (by rfl) ⟨277805, by rfl⟩ : syracuseStep 1481629 = 555611) (by norm_num)
theorem B2137013 : Blo 1315976 2137013 := bbase (se 5 (by rfl) ⟨100172, by rfl⟩ : syracuseStep 2137013 = 200345) (by norm_num)
theorem B1481665 : Blo 1315976 1481665 := bbase (se 2 (by rfl) ⟨555624, by rfl⟩ : syracuseStep 1481665 = 1111249) (by norm_num)
theorem B2964437 : Blo 1315976 2964437 := bbase (se 7 (by rfl) ⟨34739, by rfl⟩ : syracuseStep 2964437 = 69479) (by norm_num)
theorem B1481701 : Blo 1315976 1481701 := bbase (se 4 (by rfl) ⟨138909, by rfl⟩ : syracuseStep 1481701 = 277819) (by norm_num)
theorem B6085621 : Blo 1315976 6085621 := bbase (se 5 (by rfl) ⟨285263, by rfl⟩ : syracuseStep 6085621 = 570527) (by norm_num)
theorem B3333109 : Blo 1315976 3333109 := bbase (se 5 (by rfl) ⟨156239, by rfl⟩ : syracuseStep 3333109 = 312479) (by norm_num)
theorem B1481737 : Blo 1315976 1481737 := bbase (se 2 (by rfl) ⟨555651, by rfl⟩ : syracuseStep 1481737 = 1111303) (by norm_num)
theorem B2964509 : Blo 1315976 2964509 := bbase (se 3 (by rfl) ⟨555845, by rfl⟩ : syracuseStep 2964509 = 1111691) (by norm_num)
theorem B1481773 : Blo 1315976 1481773 := bbase (se 3 (by rfl) ⟨277832, by rfl⟩ : syracuseStep 1481773 = 555665) (by norm_num)
theorem B1334341 : Blo 1315976 1334341 := bbase (se 4 (by rfl) ⟨125094, by rfl⟩ : syracuseStep 1334341 = 250189) (by norm_num)
theorem B1481809 : Blo 1315976 1481809 := bbase (se 2 (by rfl) ⟨555678, by rfl⟩ : syracuseStep 1481809 = 1111357) (by norm_num)
theorem B5069909 : Blo 1315976 5069909 := bbase (se 8 (by rfl) ⟨29706, by rfl⟩ : syracuseStep 5069909 = 59413) (by norm_num)
theorem B3333221 : Blo 1315976 3333221 := bbase (se 4 (by rfl) ⟨312489, by rfl⟩ : syracuseStep 3333221 = 624979) (by norm_num)
theorem B2964581 : Blo 1315976 2964581 := bbase (se 4 (by rfl) ⟨277929, by rfl⟩ : syracuseStep 2964581 = 555859) (by norm_num)
theorem B5700725 : Blo 1315976 5700725 := bbase (se 5 (by rfl) ⟨267221, by rfl⟩ : syracuseStep 5700725 = 534443) (by norm_num)
theorem B1481845 : Blo 1315976 1481845 := bbase (se 5 (by rfl) ⟨69461, by rfl⟩ : syracuseStep 1481845 = 138923) (by norm_num)
theorem B1481881 : Blo 1315976 1481881 := bbase (se 2 (by rfl) ⟨555705, by rfl⟩ : syracuseStep 1481881 = 1111411) (by norm_num)
theorem B2964653 : Blo 1315976 2964653 := bbase (se 3 (by rfl) ⟨555872, by rfl⟩ : syracuseStep 2964653 = 1111745) (by norm_num)
theorem B7503029 : Blo 1315976 7503029 := bbase (se 5 (by rfl) ⟨351704, by rfl⟩ : syracuseStep 7503029 = 703409) (by norm_num)
theorem B1481917 : Blo 1315976 1481917 := bbase (se 3 (by rfl) ⟨277859, by rfl⟩ : syracuseStep 1481917 = 555719) (by norm_num)
theorem B1481953 : Blo 1315976 1481953 := bbase (se 2 (by rfl) ⟨555732, by rfl⟩ : syracuseStep 1481953 = 1111465) (by norm_num)
theorem B2964725 : Blo 1315976 2964725 := bbase (se 5 (by rfl) ⟨138971, by rfl⟩ : syracuseStep 2964725 = 277943) (by norm_num)
theorem B1481989 : Blo 1315976 1481989 := bbase (se 4 (by rfl) ⟨138936, by rfl⟩ : syracuseStep 1481989 = 277873) (by norm_num)
theorem B4447493 : Blo 1315976 4447493 := bbase (se 4 (by rfl) ⟨416952, by rfl⟩ : syracuseStep 4447493 = 833905) (by norm_num)
theorem B3333413 : Blo 1315976 3333413 := bbase (se 4 (by rfl) ⟨312507, by rfl⟩ : syracuseStep 3333413 = 625015) (by norm_num)
theorem B1482025 : Blo 1315976 1482025 := bbase (se 2 (by rfl) ⟨555759, by rfl⟩ : syracuseStep 1482025 = 1111519) (by norm_num)
theorem B2964797 : Blo 1315976 2964797 := bbase (se 3 (by rfl) ⟨555899, by rfl⟩ : syracuseStep 2964797 = 1111799) (by norm_num)
theorem B1482061 : Blo 1315976 1482061 := bbase (se 3 (by rfl) ⟨277886, by rfl⟩ : syracuseStep 1482061 = 555773) (by norm_num)
theorem B1482097 : Blo 1315976 1482097 := bbase (se 2 (by rfl) ⟨555786, by rfl⟩ : syracuseStep 1482097 = 1111573) (by norm_num)
theorem B2964869 : Blo 1315976 2964869 := bbase (se 4 (by rfl) ⟨277956, by rfl⟩ : syracuseStep 2964869 = 555913) (by norm_num)
theorem B1482133 : Blo 1315976 1482133 := bbase (se 6 (by rfl) ⟨34737, by rfl⟩ : syracuseStep 1482133 = 69475) (by norm_num)
theorem B16883093 : Blo 1315976 16883093 := bbase (se 6 (by rfl) ⟨395697, by rfl⟩ : syracuseStep 16883093 = 791395) (by norm_num)
theorem B1334701 : Blo 1315976 1334701 := bbase (se 3 (by rfl) ⟨250256, by rfl⟩ : syracuseStep 1334701 = 500513) (by norm_num)
theorem B1482169 : Blo 1315976 1482169 := bbase (se 2 (by rfl) ⟨555813, by rfl⟩ : syracuseStep 1482169 = 1111627) (by norm_num)
theorem B2964941 : Blo 1315976 2964941 := bbase (se 3 (by rfl) ⟨555926, by rfl⟩ : syracuseStep 2964941 = 1111853) (by norm_num)
theorem B9493973 : Blo 1315976 9493973 := bbase (se 7 (by rfl) ⟨111257, by rfl⟩ : syracuseStep 9493973 = 222515) (by norm_num)
theorem B1875421 : Blo 1315976 1875421 := bbase (se 3 (by rfl) ⟨351641, by rfl⟩ : syracuseStep 1875421 = 703283) (by norm_num)
theorem B1482205 : Blo 1315976 1482205 := bbase (se 3 (by rfl) ⟨277913, by rfl⟩ : syracuseStep 1482205 = 555827) (by norm_num)
theorem B1482241 : Blo 1315976 1482241 := bbase (se 2 (by rfl) ⟨555840, by rfl⟩ : syracuseStep 1482241 = 1111681) (by norm_num)
theorem B2965013 : Blo 1315976 2965013 := bbase (se 6 (by rfl) ⟨69492, by rfl⟩ : syracuseStep 2965013 = 138985) (by norm_num)
theorem B1482277 : Blo 1315976 1482277 := bbase (se 4 (by rfl) ⟨138963, by rfl⟩ : syracuseStep 1482277 = 277927) (by norm_num)
theorem B1482313 : Blo 1315976 1482313 := bbase (se 2 (by rfl) ⟨555867, by rfl⟩ : syracuseStep 1482313 = 1111735) (by norm_num)
theorem B2965085 : Blo 1315976 2965085 := bbase (se 3 (by rfl) ⟨555953, by rfl⟩ : syracuseStep 2965085 = 1111907) (by norm_num)
theorem B3751525 : Blo 1315976 3751525 := bbase (se 4 (by rfl) ⟨351705, by rfl⟩ : syracuseStep 3751525 = 703411) (by norm_num)
theorem B1482349 : Blo 1315976 1482349 := bbase (se 3 (by rfl) ⟨277940, by rfl⟩ : syracuseStep 1482349 = 555881) (by norm_num)
theorem B3333757 : Blo 1315976 3333757 := bbase (se 3 (by rfl) ⟨625079, by rfl⟩ : syracuseStep 3333757 = 1250159) (by norm_num)
theorem B1482385 : Blo 1315976 1482385 := bbase (se 2 (by rfl) ⟨555894, by rfl⟩ : syracuseStep 1482385 = 1111789) (by norm_num)
theorem B2965157 : Blo 1315976 2965157 := bbase (se 4 (by rfl) ⟨277983, by rfl⟩ : syracuseStep 2965157 = 555967) (by norm_num)
theorem B1482421 : Blo 1315976 1482421 := bbase (se 5 (by rfl) ⟨69488, by rfl⟩ : syracuseStep 1482421 = 138977) (by norm_num)
theorem B4447925 : Blo 1315976 4447925 := bbase (se 5 (by rfl) ⟨208496, by rfl⟩ : syracuseStep 4447925 = 416993) (by norm_num)
theorem B1482457 : Blo 1315976 1482457 := bbase (se 2 (by rfl) ⟨555921, by rfl⟩ : syracuseStep 1482457 = 1111843) (by norm_num)
theorem B1973981 : Blo 1315976 1973981 := bbase (se 3 (by rfl) ⟨370121, by rfl⟩ : syracuseStep 1973981 = 740243) (by norm_num)
theorem B3333869 : Blo 1315976 3333869 := bbase (se 3 (by rfl) ⟨625100, by rfl⟩ : syracuseStep 3333869 = 1250201) (by norm_num)
theorem B2965229 : Blo 1315976 2965229 := bbase (se 3 (by rfl) ⟨555980, by rfl⟩ : syracuseStep 2965229 = 1111961) (by norm_num)
theorem B1974005 : Blo 1315976 1974005 := bbase (se 5 (by rfl) ⟨92531, by rfl⟩ : syracuseStep 1974005 = 185063) (by norm_num)
theorem B1482493 : Blo 1315976 1482493 := bbase (se 3 (by rfl) ⟨277967, by rfl⟩ : syracuseStep 1482493 = 555935) (by norm_num)
theorem B1974029 : Blo 1315976 1974029 := bbase (se 3 (by rfl) ⟨370130, by rfl⟩ : syracuseStep 1974029 = 740261) (by norm_num)
theorem B1482529 : Blo 1315976 1482529 := bbase (se 2 (by rfl) ⟨555948, by rfl⟩ : syracuseStep 1482529 = 1111897) (by norm_num)
theorem B1974053 : Blo 1315976 1974053 := bbase (se 4 (by rfl) ⟨185067, by rfl⟩ : syracuseStep 1974053 = 370135) (by norm_num)
theorem B2965301 : Blo 1315976 2965301 := bbase (se 5 (by rfl) ⟨138998, by rfl⟩ : syracuseStep 2965301 = 277997) (by norm_num)
theorem B1974077 : Blo 1315976 1974077 := bbase (se 3 (by rfl) ⟨370139, by rfl⟩ : syracuseStep 1974077 = 740279) (by norm_num)
theorem B4742981 : Blo 1315976 4742981 := bbase (se 4 (by rfl) ⟨444654, by rfl⟩ : syracuseStep 4742981 = 889309) (by norm_num)
theorem B1482565 : Blo 1315976 1482565 := bbase (se 4 (by rfl) ⟨138990, by rfl⟩ : syracuseStep 1482565 = 277981) (by norm_num)
theorem B1974101 : Blo 1315976 1974101 := bbase (se 9 (by rfl) ⟨5783, by rfl⟩ : syracuseStep 1974101 = 11567) (by norm_num)
theorem B32481109 : Blo 1315976 32481109 := bbase (se 9 (by rfl) ⟨95159, by rfl⟩ : syracuseStep 32481109 = 190319) (by norm_num)
theorem B1482601 : Blo 1315976 1482601 := bbase (se 2 (by rfl) ⟨555975, by rfl⟩ : syracuseStep 1482601 = 1111951) (by norm_num)
theorem B1974125 : Blo 1315976 1974125 := bbase (se 3 (by rfl) ⟨370148, by rfl⟩ : syracuseStep 1974125 = 740297) (by norm_num)
theorem B11255669 : Blo 1315976 11255669 := bbase (se 5 (by rfl) ⟨527609, by rfl⟩ : syracuseStep 11255669 = 1055219) (by norm_num)
theorem B2965373 : Blo 1315976 2965373 := bbase (se 3 (by rfl) ⟨556007, by rfl⟩ : syracuseStep 2965373 = 1112015) (by norm_num)
theorem B1974149 : Blo 1315976 1974149 := bbase (se 4 (by rfl) ⟨185076, by rfl⟩ : syracuseStep 1974149 = 370153) (by norm_num)
theorem B1482637 : Blo 1315976 1482637 := bbase (se 3 (by rfl) ⟨277994, by rfl⟩ : syracuseStep 1482637 = 555989) (by norm_num)
theorem B1974173 : Blo 1315976 1974173 := bbase (se 3 (by rfl) ⟨370157, by rfl⟩ : syracuseStep 1974173 = 740315) (by norm_num)
theorem B3334061 : Blo 1315976 3334061 := bbase (se 3 (by rfl) ⟨625136, by rfl⟩ : syracuseStep 3334061 = 1250273) (by norm_num)
theorem B1482673 : Blo 1315976 1482673 := bbase (se 2 (by rfl) ⟨556002, by rfl⟩ : syracuseStep 1482673 = 1112005) (by norm_num)
theorem B1974197 : Blo 1315976 1974197 := bbase (se 5 (by rfl) ⟨92540, by rfl⟩ : syracuseStep 1974197 = 185081) (by norm_num)
theorem B2965445 : Blo 1315976 2965445 := bbase (se 4 (by rfl) ⟨278010, by rfl⟩ : syracuseStep 2965445 = 556021) (by norm_num)
theorem B1974221 : Blo 1315976 1974221 := bbase (se 3 (by rfl) ⟨370166, by rfl⟩ : syracuseStep 1974221 = 740333) (by norm_num)
theorem B1482709 : Blo 1315976 1482709 := bbase (se 7 (by rfl) ⟨17375, by rfl⟩ : syracuseStep 1482709 = 34751) (by norm_num)
theorem B1974245 : Blo 1315976 1974245 := bbase (se 4 (by rfl) ⟨185085, by rfl⟩ : syracuseStep 1974245 = 370171) (by norm_num)
theorem B1900525 : Blo 1315976 1900525 := bbase (se 3 (by rfl) ⟨356348, by rfl⟩ : syracuseStep 1900525 = 712697) (by norm_num)
theorem B11247605 : Blo 1315976 11247605 := bbase (se 5 (by rfl) ⟨527231, by rfl⟩ : syracuseStep 11247605 = 1054463) (by norm_num)
theorem B1974269 : Blo 1315976 1974269 := bbase (se 3 (by rfl) ⟨370175, by rfl⟩ : syracuseStep 1974269 = 740351) (by norm_num)
theorem B2252801 : Blo 1315976 2252801 := bstep (se 2 (by rfl) ⟨844800, by rfl⟩ : syracuseStep 2252801 = 1689601) B1689601
theorem B1974275 : Blo 1315976 1974275 := bstep (se 1 (by rfl) ⟨1480706, by rfl⟩ : syracuseStep 1974275 = 2961413) B2961413
theorem B1974305 : Blo 1315976 1974305 := bstep (se 2 (by rfl) ⟨740364, by rfl⟩ : syracuseStep 1974305 = 1480729) B1480729
theorem B4218929 : Blo 1315976 4218929 := bstep (se 2 (by rfl) ⟨1582098, by rfl⟩ : syracuseStep 4218929 = 3164197) B3164197
theorem B3334193 : Blo 1315976 3334193 := bstep (se 2 (by rfl) ⟨1250322, by rfl⟩ : syracuseStep 3334193 = 2500645) B2500645
theorem B1974323 : Blo 1315976 1974323 := bstep (se 1 (by rfl) ⟨1480742, by rfl⟩ : syracuseStep 1974323 = 2961485) B2961485
theorem B32489525 : Blo 1315976 32489525 := bstep (se 5 (by rfl) ⟨1522946, by rfl⟩ : syracuseStep 32489525 = 3045893) B3045893
theorem B1974353 : Blo 1315976 1974353 := bstep (se 2 (by rfl) ⟨740382, by rfl⟩ : syracuseStep 1974353 = 1480765) B1480765
theorem B1974371 : Blo 1315976 1974371 := bstep (se 1 (by rfl) ⟨1480778, by rfl⟩ : syracuseStep 1974371 = 2961557) B2961557
theorem B3334243 : Blo 1315976 3334243 := bstep (se 1 (by rfl) ⟨2500682, by rfl⟩ : syracuseStep 3334243 = 5001365) B5001365
theorem B1974401 : Blo 1315976 1974401 := bstep (se 2 (by rfl) ⟨740400, by rfl⟩ : syracuseStep 1974401 = 1480801) B1480801
theorem B1974419 : Blo 1315976 1974419 := bstep (se 1 (by rfl) ⟨1480814, by rfl⟩ : syracuseStep 1974419 = 2961629) B2961629
theorem B1974449 : Blo 1315976 1974449 := bstep (se 2 (by rfl) ⟨740418, by rfl⟩ : syracuseStep 1974449 = 1480837) B1480837
theorem B4219057 : Blo 1315976 4219057 := bstep (se 2 (by rfl) ⟨1582146, by rfl⟩ : syracuseStep 4219057 = 3164293) B3164293
theorem B1974467 : Blo 1315976 1974467 := bstep (se 1 (by rfl) ⟨1480850, by rfl⟩ : syracuseStep 1974467 = 2961701) B2961701
theorem B1974497 : Blo 1315976 1974497 := bstep (se 2 (by rfl) ⟨740436, by rfl⟩ : syracuseStep 1974497 = 1480873) B1480873
theorem B3334385 : Blo 1315976 3334385 := bstep (se 2 (by rfl) ⟨1250394, by rfl⟩ : syracuseStep 3334385 = 2500789) B2500789
theorem B1974515 : Blo 1315976 1974515 := bstep (se 1 (by rfl) ⟨1480886, by rfl⟩ : syracuseStep 1974515 = 2961773) B2961773
theorem B1974545 : Blo 1315976 1974545 := bstep (se 2 (by rfl) ⟨740454, by rfl⟩ : syracuseStep 1974545 = 1480909) B1480909
theorem B1876241 : Blo 1315976 1876241 := bstep (se 2 (by rfl) ⟨703590, by rfl⟩ : syracuseStep 1876241 = 1407181) B1407181
theorem B1974563 : Blo 1315976 1974563 := bstep (se 1 (by rfl) ⟨1480922, by rfl⟩ : syracuseStep 1974563 = 2961845) B2961845
theorem B1974593 : Blo 1315976 1974593 := bstep (se 2 (by rfl) ⟨740472, by rfl⟩ : syracuseStep 1974593 = 1480945) B1480945
theorem B1974611 : Blo 1315976 1974611 := bstep (se 1 (by rfl) ⟨1480958, by rfl⟩ : syracuseStep 1974611 = 2961917) B2961917
theorem B1876321 : Blo 1315976 1876321 := bstep (se 2 (by rfl) ⟨703620, by rfl⟩ : syracuseStep 1876321 = 1407241) B1407241
theorem B1974641 : Blo 1315976 1974641 := bstep (se 2 (by rfl) ⟨740490, by rfl⟩ : syracuseStep 1974641 = 1480981) B1480981
theorem B1974659 : Blo 1315976 1974659 := bstep (se 1 (by rfl) ⟨1480994, by rfl⟩ : syracuseStep 1974659 = 2961989) B2961989
theorem B1974689 : Blo 1315976 1974689 := bstep (se 2 (by rfl) ⟨740508, by rfl⟩ : syracuseStep 1974689 = 1481017) B1481017
theorem B3752369 : Blo 1315976 3752369 := bstep (se 2 (by rfl) ⟨1407138, by rfl⟩ : syracuseStep 3752369 = 2814277) B2814277
theorem B1974707 : Blo 1315976 1974707 := bstep (se 1 (by rfl) ⟨1481030, by rfl⟩ : syracuseStep 1974707 = 2962061) B2962061
theorem B1974737 : Blo 1315976 1974737 := bstep (se 2 (by rfl) ⟨740526, by rfl⟩ : syracuseStep 1974737 = 1481053) B1481053
theorem B1974755 : Blo 1315976 1974755 := bstep (se 1 (by rfl) ⟨1481066, by rfl⟩ : syracuseStep 1974755 = 2962133) B2962133
theorem B1974785 : Blo 1315976 1974785 := bstep (se 2 (by rfl) ⟨740544, by rfl⟩ : syracuseStep 1974785 = 1481089) B1481089
theorem B4997645 : Blo 1315976 4997645 := bstep (se 3 (by rfl) ⟨937058, by rfl⟩ : syracuseStep 4997645 = 1874117) B1874117
theorem B1974803 : Blo 1315976 1974803 := bstep (se 1 (by rfl) ⟨1481102, by rfl⟩ : syracuseStep 1974803 = 2962205) B2962205
theorem B1974833 : Blo 1315976 1974833 := bstep (se 2 (by rfl) ⟨740562, by rfl⟩ : syracuseStep 1974833 = 1481125) B1481125
theorem B1974851 : Blo 1315976 1974851 := bstep (se 1 (by rfl) ⟨1481138, by rfl⟩ : syracuseStep 1974851 = 2962277) B2962277
theorem B1974881 : Blo 1315976 1974881 := bstep (se 2 (by rfl) ⟨740580, by rfl⟩ : syracuseStep 1974881 = 1481161) B1481161
theorem B1974899 : Blo 1315976 1974899 := bstep (se 1 (by rfl) ⟨1481174, by rfl⟩ : syracuseStep 1974899 = 2962349) B2962349
theorem B1974929 : Blo 1315976 1974929 := bstep (se 2 (by rfl) ⟨740598, by rfl⟩ : syracuseStep 1974929 = 1481197) B1481197
theorem B1974947 : Blo 1315976 1974947 := bstep (se 1 (by rfl) ⟨1481210, by rfl⟩ : syracuseStep 1974947 = 2962421) B2962421
theorem B1974977 : Blo 1315976 1974977 := bstep (se 2 (by rfl) ⟨740616, by rfl⟩ : syracuseStep 1974977 = 1481233) B1481233
theorem B1974995 : Blo 1315976 1974995 := bstep (se 1 (by rfl) ⟨1481246, by rfl⟩ : syracuseStep 1974995 = 2962493) B2962493
theorem B1975025 : Blo 1315976 1975025 := bstep (se 2 (by rfl) ⟨740634, by rfl⟩ : syracuseStep 1975025 = 1481269) B1481269
theorem B2499331 : Blo 1315976 2499331 := bstep (se 1 (by rfl) ⟨1874498, by rfl⟩ : syracuseStep 2499331 = 3748997) B3748997
theorem B1975043 : Blo 1315976 1975043 := bstep (se 1 (by rfl) ⟨1481282, by rfl⟩ : syracuseStep 1975043 = 2962565) B2962565
theorem B2220817 : Blo 1315976 2220817 := bstep (se 2 (by rfl) ⟨832806, by rfl⟩ : syracuseStep 2220817 = 1665613) B1665613
theorem B61621013 : Blo 1315976 61621013 := bstep (se 6 (by rfl) ⟨1444242, by rfl⟩ : syracuseStep 61621013 = 2888485) B2888485
theorem B1975073 : Blo 1315976 1975073 := bstep (se 2 (by rfl) ⟨740652, by rfl⟩ : syracuseStep 1975073 = 1481305) B1481305
theorem B2220851 : Blo 1315976 2220851 := bstep (se 1 (by rfl) ⟨1665638, by rfl⟩ : syracuseStep 2220851 = 3331277) B3331277
theorem B1975091 : Blo 1315976 1975091 := bstep (se 1 (by rfl) ⟨1481318, by rfl⟩ : syracuseStep 1975091 = 2962637) B2962637
theorem B2810705 : Blo 1315976 2810705 := bstep (se 2 (by rfl) ⟨1054014, by rfl⟩ : syracuseStep 2810705 = 2108029) B2108029
theorem B1975121 : Blo 1315976 1975121 := bstep (se 2 (by rfl) ⟨740670, by rfl⟩ : syracuseStep 1975121 = 1481341) B1481341
theorem B1975139 : Blo 1315976 1975139 := bstep (se 1 (by rfl) ⟨1481354, by rfl⟩ : syracuseStep 1975139 = 2962709) B2962709
theorem B1975169 : Blo 1315976 1975169 := bstep (se 2 (by rfl) ⟨740688, by rfl⟩ : syracuseStep 1975169 = 1481377) B1481377
theorem B1975187 : Blo 1315976 1975187 := bstep (se 1 (by rfl) ⟨1481390, by rfl⟩ : syracuseStep 1975187 = 2962781) B2962781
theorem B2499491 : Blo 1315976 2499491 := bstep (se 1 (by rfl) ⟨1874618, by rfl⟩ : syracuseStep 2499491 = 3749237) B3749237
theorem B1975217 : Blo 1315976 1975217 := bstep (se 2 (by rfl) ⟨740706, by rfl⟩ : syracuseStep 1975217 = 1481413) B1481413
theorem B2220979 : Blo 1315976 2220979 := bstep (se 1 (by rfl) ⟨1665734, by rfl⟩ : syracuseStep 2220979 = 3331469) B3331469
theorem B1975235 : Blo 1315976 1975235 := bstep (se 1 (by rfl) ⟨1481426, by rfl⟩ : syracuseStep 1975235 = 2962853) B2962853
theorem B1975265 : Blo 1315976 1975265 := bstep (se 2 (by rfl) ⟨740724, by rfl⟩ : syracuseStep 1975265 = 1481449) B1481449
theorem B1975283 : Blo 1315976 1975283 := bstep (se 1 (by rfl) ⟨1481462, by rfl⟩ : syracuseStep 1975283 = 2962925) B2962925
theorem B1975313 : Blo 1315976 1975313 := bstep (se 2 (by rfl) ⟨740742, by rfl⟩ : syracuseStep 1975313 = 1481485) B1481485
theorem B1975331 : Blo 1315976 1975331 := bstep (se 1 (by rfl) ⟨1481498, by rfl⟩ : syracuseStep 1975331 = 2962997) B2962997
theorem B2221121 : Blo 1315976 2221121 := bstep (se 2 (by rfl) ⟨832920, by rfl⟩ : syracuseStep 2221121 = 1665841) B1665841
theorem B1975361 : Blo 1315976 1975361 := bstep (se 2 (by rfl) ⟨740760, by rfl⟩ : syracuseStep 1975361 = 1481521) B1481521
theorem B2253889 : Blo 1315976 2253889 := bstep (se 2 (by rfl) ⟨845208, by rfl⟩ : syracuseStep 2253889 = 1690417) B1690417
theorem B1975379 : Blo 1315976 1975379 := bstep (se 1 (by rfl) ⟨1481534, by rfl⟩ : syracuseStep 1975379 = 2963069) B2963069
theorem B1975409 : Blo 1315976 1975409 := bstep (se 2 (by rfl) ⟨740778, by rfl⟩ : syracuseStep 1975409 = 1481557) B1481557
theorem B1975427 : Blo 1315976 1975427 := bstep (se 1 (by rfl) ⟨1481570, by rfl⟩ : syracuseStep 1975427 = 2963141) B2963141
theorem B4220045 : Blo 1315976 4220045 := bstep (se 3 (by rfl) ⟨791258, by rfl⟩ : syracuseStep 4220045 = 1582517) B1582517
theorem B1975457 : Blo 1315976 1975457 := bstep (se 2 (by rfl) ⟨740796, by rfl⟩ : syracuseStep 1975457 = 1481593) B1481593
theorem B3163313 : Blo 1315976 3163313 := bstep (se 2 (by rfl) ⟨1186242, by rfl⟩ : syracuseStep 3163313 = 2372485) B2372485
theorem B1975475 : Blo 1315976 1975475 := bstep (se 1 (by rfl) ⟨1481606, by rfl⟩ : syracuseStep 1975475 = 2963213) B2963213
theorem B1713331 : Blo 1315976 1713331 := bstep (se 1 (by rfl) ⟨1284998, by rfl⟩ : syracuseStep 1713331 = 2569997) B2569997
theorem B2221249 : Blo 1315976 2221249 := bstep (se 2 (by rfl) ⟨832968, by rfl⟩ : syracuseStep 2221249 = 1665937) B1665937
theorem B1975505 : Blo 1315976 1975505 := bstep (se 2 (by rfl) ⟨740814, by rfl⟩ : syracuseStep 1975505 = 1481629) B1481629
theorem B3335377 : Blo 1315976 3335377 := bstep (se 2 (by rfl) ⟨1250766, by rfl⟩ : syracuseStep 3335377 = 2501533) B2501533
theorem B1582291 : Blo 1315976 1582291 := bstep (se 1 (by rfl) ⟨1186718, by rfl⟩ : syracuseStep 1582291 = 2373437) B2373437
theorem B2221283 : Blo 1315976 2221283 := bstep (se 1 (by rfl) ⟨1665962, by rfl⟩ : syracuseStep 2221283 = 3331925) B3331925
theorem B1975523 : Blo 1315976 1975523 := bstep (se 1 (by rfl) ⟨1481642, by rfl⟩ : syracuseStep 1975523 = 2963285) B2963285
theorem B6669539 : Blo 1315976 6669539 := bstep (se 1 (by rfl) ⟨5002154, by rfl⟩ : syracuseStep 6669539 = 10004309) B10004309
theorem B7496945 : Blo 1315976 7496945 := bstep (se 2 (by rfl) ⟨2811354, by rfl⟩ : syracuseStep 7496945 = 5622709) B5622709
theorem B1975553 : Blo 1315976 1975553 := bstep (se 2 (by rfl) ⟨740832, by rfl⟩ : syracuseStep 1975553 = 1481665) B1481665
theorem B1975571 : Blo 1315976 1975571 := bstep (se 1 (by rfl) ⟨1481678, by rfl⟩ : syracuseStep 1975571 = 2963357) B2963357
theorem B4998449 : Blo 1315976 4998449 := bstep (se 2 (by rfl) ⟨1874418, by rfl⟩ : syracuseStep 4998449 = 3748837) B3748837
theorem B1975601 : Blo 1315976 1975601 := bstep (se 2 (by rfl) ⟨740850, by rfl⟩ : syracuseStep 1975601 = 1481701) B1481701
theorem B1852723 : Blo 1315976 1852723 := bstep (se 1 (by rfl) ⟨1389542, by rfl⟩ : syracuseStep 1852723 = 2779085) B2779085
theorem B1975619 : Blo 1315976 1975619 := bstep (se 1 (by rfl) ⟨1481714, by rfl⟩ : syracuseStep 1975619 = 2963429) B2963429
theorem B1975649 : Blo 1315976 1975649 := bstep (se 2 (by rfl) ⟨740868, by rfl⟩ : syracuseStep 1975649 = 1481737) B1481737
theorem B2221411 : Blo 1315976 2221411 := bstep (se 1 (by rfl) ⟨1666058, by rfl⟩ : syracuseStep 2221411 = 3332117) B3332117
theorem B1975667 : Blo 1315976 1975667 := bstep (se 1 (by rfl) ⟨1481750, by rfl⟩ : syracuseStep 1975667 = 2963501) B2963501
theorem B1975697 : Blo 1315976 1975697 := bstep (se 2 (by rfl) ⟨740886, by rfl⟩ : syracuseStep 1975697 = 1481773) B1481773
theorem B2254225 : Blo 1315976 2254225 := bstep (se 2 (by rfl) ⟨845334, by rfl⟩ : syracuseStep 2254225 = 1690669) B1690669
theorem B1582483 : Blo 1315976 1582483 := bstep (se 1 (by rfl) ⟨1186862, by rfl⟩ : syracuseStep 1582483 = 2373725) B2373725
theorem B1975715 : Blo 1315976 1975715 := bstep (se 1 (by rfl) ⟨1481786, by rfl⟩ : syracuseStep 1975715 = 2963573) B2963573
theorem B1779121 : Blo 1315976 1779121 := bstep (se 2 (by rfl) ⟨667170, by rfl⟩ : syracuseStep 1779121 = 1334341) B1334341
theorem B1975745 : Blo 1315976 1975745 := bstep (se 2 (by rfl) ⟨740904, by rfl⟩ : syracuseStep 1975745 = 1481809) B1481809
theorem B4441553 : Blo 1315976 4441553 := bstep (se 2 (by rfl) ⟨1665582, by rfl⟩ : syracuseStep 4441553 = 3331165) B3331165
theorem B1975763 : Blo 1315976 1975763 := bstep (se 1 (by rfl) ⟨1481822, by rfl⟩ : syracuseStep 1975763 = 2963645) B2963645
theorem B3335651 : Blo 1315976 3335651 := bstep (se 1 (by rfl) ⟨2501738, by rfl⟩ : syracuseStep 3335651 = 5003477) B5003477
theorem B2221553 : Blo 1315976 2221553 := bstep (se 2 (by rfl) ⟨833082, by rfl⟩ : syracuseStep 2221553 = 1666165) B1666165
theorem B1975793 : Blo 1315976 1975793 := bstep (se 2 (by rfl) ⟨740922, by rfl⟩ : syracuseStep 1975793 = 1481845) B1481845
theorem B1975811 : Blo 1315976 1975811 := bstep (se 1 (by rfl) ⟨1481858, by rfl⟩ : syracuseStep 1975811 = 2963717) B2963717
theorem B1975841 : Blo 1315976 1975841 := bstep (se 2 (by rfl) ⟨740940, by rfl⟩ : syracuseStep 1975841 = 1481881) B1481881
theorem B5629475 : Blo 1315976 5629475 := bstep (se 1 (by rfl) ⟨4222106, by rfl⟩ : syracuseStep 5629475 = 8444213) B8444213
theorem B1975859 : Blo 1315976 1975859 := bstep (se 1 (by rfl) ⟨1481894, by rfl⟩ : syracuseStep 1975859 = 2963789) B2963789
theorem B1975889 : Blo 1315976 1975889 := bstep (se 2 (by rfl) ⟨740958, by rfl⟩ : syracuseStep 1975889 = 1481917) B1481917
theorem B1975907 : Blo 1315976 1975907 := bstep (se 1 (by rfl) ⟨1481930, by rfl⟩ : syracuseStep 1975907 = 2963861) B2963861
theorem B2221681 : Blo 1315976 2221681 := bstep (se 2 (by rfl) ⟨833130, by rfl⟩ : syracuseStep 2221681 = 1666261) B1666261
theorem B1975937 : Blo 1315976 1975937 := bstep (se 2 (by rfl) ⟨740976, by rfl⟩ : syracuseStep 1975937 = 1481953) B1481953
theorem B2221715 : Blo 1315976 2221715 := bstep (se 1 (by rfl) ⟨1666286, by rfl⟩ : syracuseStep 2221715 = 3332573) B3332573
theorem B1975955 : Blo 1315976 1975955 := bstep (se 1 (by rfl) ⟨1481966, by rfl⟩ : syracuseStep 1975955 = 2963933) B2963933
theorem B3335843 : Blo 1315976 3335843 := bstep (se 1 (by rfl) ⟨2501882, by rfl⟩ : syracuseStep 3335843 = 5003765) B5003765
theorem B1975985 : Blo 1315976 1975985 := bstep (se 2 (by rfl) ⟨740994, by rfl⟩ : syracuseStep 1975985 = 1481989) B1481989
theorem B1976003 : Blo 1315976 1976003 := bstep (se 1 (by rfl) ⟨1482002, by rfl⟩ : syracuseStep 1976003 = 2964005) B2964005
theorem B1976033 : Blo 1315976 1976033 := bstep (se 2 (by rfl) ⟨741012, by rfl⟩ : syracuseStep 1976033 = 1482025) B1482025
theorem B3163889 : Blo 1315976 3163889 := bstep (se 2 (by rfl) ⟨1186458, by rfl⟩ : syracuseStep 3163889 = 2372917) B2372917
theorem B1976051 : Blo 1315976 1976051 := bstep (se 1 (by rfl) ⟨1482038, by rfl⟩ : syracuseStep 1976051 = 2964077) B2964077
theorem B4007693 : Blo 1315976 4007693 := bstep (se 3 (by rfl) ⟨751442, by rfl⟩ : syracuseStep 4007693 = 1502885) B1502885
theorem B1976081 : Blo 1315976 1976081 := bstep (se 2 (by rfl) ⟨741030, by rfl⟩ : syracuseStep 1976081 = 1482061) B1482061
theorem B2221843 : Blo 1315976 2221843 := bstep (se 1 (by rfl) ⟨1666382, by rfl⟩ : syracuseStep 2221843 = 3332765) B3332765
theorem B1582867 : Blo 1315976 1582867 := bstep (se 1 (by rfl) ⟨1187150, by rfl⟩ : syracuseStep 1582867 = 2374301) B2374301
theorem B1976099 : Blo 1315976 1976099 := bstep (se 1 (by rfl) ⟨1482074, by rfl⟩ : syracuseStep 1976099 = 2964149) B2964149
theorem B1689395 : Blo 1315976 1689395 := bstep (se 1 (by rfl) ⟨1267046, by rfl⟩ : syracuseStep 1689395 = 2534093) B2534093
theorem B1976129 : Blo 1315976 1976129 := bstep (se 2 (by rfl) ⟨741048, by rfl⟩ : syracuseStep 1976129 = 1482097) B1482097
theorem B1976147 : Blo 1315976 1976147 := bstep (se 1 (by rfl) ⟨1482110, by rfl⟩ : syracuseStep 1976147 = 2964221) B2964221
theorem B1976177 : Blo 1315976 1976177 := bstep (se 2 (by rfl) ⟨741066, by rfl⟩ : syracuseStep 1976177 = 1482133) B1482133
theorem B3164035 : Blo 1315976 3164035 := bstep (se 1 (by rfl) ⟨2373026, by rfl⟩ : syracuseStep 3164035 = 4746053) B4746053
theorem B1976195 : Blo 1315976 1976195 := bstep (se 1 (by rfl) ⟨1482146, by rfl⟩ : syracuseStep 1976195 = 2964293) B2964293
theorem B2221985 : Blo 1315976 2221985 := bstep (se 2 (by rfl) ⟨833244, by rfl⟩ : syracuseStep 2221985 = 1666489) B1666489
theorem B1976225 : Blo 1315976 1976225 := bstep (se 2 (by rfl) ⟨741084, by rfl⟩ : syracuseStep 1976225 = 1482169) B1482169
theorem B1976243 : Blo 1315976 1976243 := bstep (se 1 (by rfl) ⟨1482182, by rfl⟩ : syracuseStep 1976243 = 2964365) B2964365
theorem B4999117 : Blo 1315976 4999117 := bstep (se 3 (by rfl) ⟨937334, by rfl⟩ : syracuseStep 4999117 = 1874669) B1874669
theorem B2500561 : Blo 1315976 2500561 := bstep (se 2 (by rfl) ⟨937710, by rfl⟩ : syracuseStep 2500561 = 1875421) B1875421
theorem B1976273 : Blo 1315976 1976273 := bstep (se 2 (by rfl) ⟨741102, by rfl⟩ : syracuseStep 1976273 = 1482205) B1482205
theorem B1976291 : Blo 1315976 1976291 := bstep (se 1 (by rfl) ⟨1482218, by rfl⟩ : syracuseStep 1976291 = 2964437) B2964437
theorem B4442093 : Blo 1315976 4442093 := bstep (se 3 (by rfl) ⟨832892, by rfl⟩ : syracuseStep 4442093 = 1665785) B1665785
theorem B1976321 : Blo 1315976 1976321 := bstep (se 2 (by rfl) ⟨741120, by rfl⟩ : syracuseStep 1976321 = 1482241) B1482241
theorem B6670349 : Blo 1315976 6670349 := bstep (se 3 (by rfl) ⟨1250690, by rfl⟩ : syracuseStep 6670349 = 2501381) B2501381
theorem B1976339 : Blo 1315976 1976339 := bstep (se 1 (by rfl) ⟨1482254, by rfl⟩ : syracuseStep 1976339 = 2964509) B2964509
theorem B2222113 : Blo 1315976 2222113 := bstep (se 2 (by rfl) ⟨833292, by rfl⟩ : syracuseStep 2222113 = 1666585) B1666585
theorem B4442147 : Blo 1315976 4442147 := bstep (se 1 (by rfl) ⟨3331610, by rfl⟩ : syracuseStep 4442147 = 6663221) B6663221
theorem B1976369 : Blo 1315976 1976369 := bstep (se 2 (by rfl) ⟨741138, by rfl⟩ : syracuseStep 1976369 = 1482277) B1482277
theorem B2222147 : Blo 1315976 2222147 := bstep (se 1 (by rfl) ⟨1666610, by rfl⟩ : syracuseStep 2222147 = 3333221) B3333221
theorem B1976387 : Blo 1315976 1976387 := bstep (se 1 (by rfl) ⟨1482290, by rfl⟩ : syracuseStep 1976387 = 2964581) B2964581
theorem B1976417 : Blo 1315976 1976417 := bstep (se 2 (by rfl) ⟨741156, by rfl⟩ : syracuseStep 1976417 = 1482313) B1482313
theorem B1976435 : Blo 1315976 1976435 := bstep (se 1 (by rfl) ⟨1482326, by rfl⟩ : syracuseStep 1976435 = 2964653) B2964653
theorem B1976465 : Blo 1315976 1976465 := bstep (se 2 (by rfl) ⟨741174, by rfl⟩ : syracuseStep 1976465 = 1482349) B1482349
theorem B1976483 : Blo 1315976 1976483 := bstep (se 1 (by rfl) ⟨1482362, by rfl⟩ : syracuseStep 1976483 = 2964725) B2964725
theorem B3557549 : Blo 1315976 3557549 := bstep (se 3 (by rfl) ⟨667040, by rfl⟩ : syracuseStep 3557549 = 1334081) B1334081
theorem B1976513 : Blo 1315976 1976513 := bstep (se 2 (by rfl) ⟨741192, by rfl⟩ : syracuseStep 1976513 = 1482385) B1482385
theorem B2222275 : Blo 1315976 2222275 := bstep (se 1 (by rfl) ⟨1666706, by rfl⟩ : syracuseStep 2222275 = 3333413) B3333413
theorem B1976531 : Blo 1315976 1976531 := bstep (se 1 (by rfl) ⟨1482398, by rfl⟩ : syracuseStep 1976531 = 2964797) B2964797
theorem B1976561 : Blo 1315976 1976561 := bstep (se 2 (by rfl) ⟨741210, by rfl⟩ : syracuseStep 1976561 = 1482421) B1482421
theorem B1976579 : Blo 1315976 1976579 := bstep (se 1 (by rfl) ⟨1482434, by rfl⟩ : syracuseStep 1976579 = 2964869) B2964869
theorem B1976609 : Blo 1315976 1976609 := bstep (se 2 (by rfl) ⟨741228, by rfl⟩ : syracuseStep 1976609 = 1482457) B1482457
theorem B4442417 : Blo 1315976 4442417 := bstep (se 2 (by rfl) ⟨1665906, by rfl⟩ : syracuseStep 4442417 = 3331813) B3331813
theorem B1976627 : Blo 1315976 1976627 := bstep (se 1 (by rfl) ⟨1482470, by rfl⟩ : syracuseStep 1976627 = 2964941) B2964941
theorem B16886069 : Blo 1315976 16886069 := bstep (se 5 (by rfl) ⟨791534, by rfl⟩ : syracuseStep 16886069 = 1583069) B1583069
theorem B2222417 : Blo 1315976 2222417 := bstep (se 2 (by rfl) ⟨833406, by rfl⟩ : syracuseStep 2222417 = 1666813) B1666813
theorem B1976657 : Blo 1315976 1976657 := bstep (se 2 (by rfl) ⟨741246, by rfl⟩ : syracuseStep 1976657 = 1482493) B1482493
theorem B1976675 : Blo 1315976 1976675 := bstep (se 1 (by rfl) ⟨1482506, by rfl⟩ : syracuseStep 1976675 = 2965013) B2965013
theorem B1976705 : Blo 1315976 1976705 := bstep (se 2 (by rfl) ⟨741264, by rfl⟩ : syracuseStep 1976705 = 1482529) B1482529
theorem B1976723 : Blo 1315976 1976723 := bstep (se 1 (by rfl) ⟨1482542, by rfl⟩ : syracuseStep 1976723 = 2965085) B2965085
theorem B1976753 : Blo 1315976 1976753 := bstep (se 2 (by rfl) ⟨741282, by rfl⟩ : syracuseStep 1976753 = 1482565) B1482565
theorem B1976771 : Blo 1315976 1976771 := bstep (se 1 (by rfl) ⟨1482578, by rfl⟩ : syracuseStep 1976771 = 2965157) B2965157
theorem B4221389 : Blo 1315976 4221389 := bstep (se 3 (by rfl) ⟨791510, by rfl⟩ : syracuseStep 4221389 = 1583021) B1583021
theorem B2222545 : Blo 1315976 2222545 := bstep (se 2 (by rfl) ⟨833454, by rfl⟩ : syracuseStep 2222545 = 1666909) B1666909
theorem B1976801 : Blo 1315976 1976801 := bstep (se 2 (by rfl) ⟨741300, by rfl⟩ : syracuseStep 1976801 = 1482601) B1482601
theorem B2222579 : Blo 1315976 2222579 := bstep (se 1 (by rfl) ⟨1666934, by rfl⟩ : syracuseStep 2222579 = 3333869) B3333869
theorem B1976819 : Blo 1315976 1976819 := bstep (se 1 (by rfl) ⟨1482614, by rfl⟩ : syracuseStep 1976819 = 2965229) B2965229
theorem B1976849 : Blo 1315976 1976849 := bstep (se 2 (by rfl) ⟨741318, by rfl⟩ : syracuseStep 1976849 = 1482637) B1482637
theorem B1976867 : Blo 1315976 1976867 := bstep (se 1 (by rfl) ⟨1482650, by rfl⟩ : syracuseStep 1976867 = 2965301) B2965301
theorem B1976897 : Blo 1315976 1976897 := bstep (se 2 (by rfl) ⟨741336, by rfl⟩ : syracuseStep 1976897 = 1482673) B1482673
theorem B1976915 : Blo 1315976 1976915 := bstep (se 1 (by rfl) ⟨1482686, by rfl⟩ : syracuseStep 1976915 = 2965373) B2965373
theorem B1976945 : Blo 1315976 1976945 := bstep (se 2 (by rfl) ⟨741354, by rfl⟩ : syracuseStep 1976945 = 1482709) B1482709
theorem B2222707 : Blo 1315976 2222707 := bstep (se 1 (by rfl) ⟨1667030, by rfl⟩ : syracuseStep 2222707 = 3334061) B3334061
theorem B1976963 : Blo 1315976 1976963 := bstep (se 1 (by rfl) ⟨1482722, by rfl⟩ : syracuseStep 1976963 = 2965445) B2965445
theorem B2534033 : Blo 1315976 2534033 := bstep (se 2 (by rfl) ⟨950262, by rfl⟩ : syracuseStep 2534033 = 1900525) B1900525
theorem B7498403 : Blo 1315976 7498403 := bstep (se 1 (by rfl) ⟨5623802, by rfl⟩ : syracuseStep 7498403 = 11247605) B11247605
theorem B2108081 : Blo 1315976 2108081 := bstep (se 2 (by rfl) ⟨790530, by rfl⟩ : syracuseStep 2108081 = 1581061) B1581061
theorem B4999907 : Blo 1315976 4999907 := bstep (se 1 (by rfl) ⟨3749930, by rfl⟩ : syracuseStep 4999907 = 7499861) B7499861
theorem B6662897 : Blo 1315976 6662897 := bstep (se 2 (by rfl) ⟨2498586, by rfl⟩ : syracuseStep 6662897 = 4997173) B4997173
theorem B2222849 : Blo 1315976 2222849 := bstep (se 2 (by rfl) ⟨833568, by rfl⟩ : syracuseStep 2222849 = 1667137) B1667137
theorem B2108209 : Blo 1315976 2108209 := bstep (se 2 (by rfl) ⟨790578, by rfl⟩ : syracuseStep 2108209 = 1581157) B1581157
theorem B8440625 : Blo 1315976 8440625 := bstep (se 2 (by rfl) ⟨3165234, by rfl⟩ : syracuseStep 8440625 = 6330469) B6330469
theorem B4442957 : Blo 1315976 4442957 := bstep (se 3 (by rfl) ⟨833054, by rfl⟩ : syracuseStep 4442957 = 1666109) B1666109
theorem B1805153 : Blo 1315976 1805153 := bstep (se 2 (by rfl) ⟨676932, by rfl⟩ : syracuseStep 1805153 = 1353865) B1353865
theorem B5622641 : Blo 1315976 5622641 := bstep (se 2 (by rfl) ⟨2108490, by rfl⟩ : syracuseStep 5622641 = 4216981) B4216981
theorem B10832753 : Blo 1315976 10832753 := bstep (se 2 (by rfl) ⟨4062282, by rfl⟩ : syracuseStep 10832753 = 8124565) B8124565
theorem B2222977 : Blo 1315976 2222977 := bstep (se 2 (by rfl) ⟨833616, by rfl⟩ : syracuseStep 2222977 = 1667233) B1667233
theorem B4443011 : Blo 1315976 4443011 := bstep (se 1 (by rfl) ⟨3332258, by rfl⟩ : syracuseStep 4443011 = 6664517) B6664517
theorem B8432525 : Blo 1315976 8432525 := bstep (se 3 (by rfl) ⟨1581098, by rfl⟩ : syracuseStep 8432525 = 3162197) B3162197
theorem B13519757 : Blo 1315976 13519757 := bstep (se 3 (by rfl) ⟨2534954, by rfl⟩ : syracuseStep 13519757 = 5069909) B5069909
theorem B2223011 : Blo 1315976 2223011 := bstep (se 1 (by rfl) ⟨1667258, by rfl⟩ : syracuseStep 2223011 = 3334517) B3334517
theorem B1666003 : Blo 1315976 1666003 := bstep (se 1 (by rfl) ⟨1249502, by rfl⟩ : syracuseStep 1666003 = 2499005) B2499005
theorem B2501617 : Blo 1315976 2501617 := bstep (se 2 (by rfl) ⟨938106, by rfl⟩ : syracuseStep 2501617 = 1876213) B1876213
theorem B11398157 : Blo 1315976 11398157 := bstep (se 3 (by rfl) ⟨2137154, by rfl⟩ : syracuseStep 11398157 = 4274309) B4274309
theorem B16239629 : Blo 1315976 16239629 := bstep (se 3 (by rfl) ⟨3044930, by rfl⟩ : syracuseStep 16239629 = 6089861) B6089861
theorem B2223139 : Blo 1315976 2223139 := bstep (se 1 (by rfl) ⟨1667354, by rfl⟩ : syracuseStep 2223139 = 3334709) B3334709
theorem B5336113 : Blo 1315976 5336113 := bstep (se 2 (by rfl) ⟨2001042, by rfl⟩ : syracuseStep 5336113 = 4002085) B4002085
theorem B1666099 : Blo 1315976 1666099 := bstep (se 1 (by rfl) ⟨1249574, by rfl⟩ : syracuseStep 1666099 = 2499149) B2499149
theorem B6327395 : Blo 1315976 6327395 := bstep (se 1 (by rfl) ⟨4745546, by rfl⟩ : syracuseStep 6327395 = 9491093) B9491093
theorem B4443281 : Blo 1315976 4443281 := bstep (se 2 (by rfl) ⟨1666230, by rfl⟩ : syracuseStep 4443281 = 3332461) B3332461
theorem B2108593 : Blo 1315976 2108593 := bstep (se 2 (by rfl) ⟨790722, by rfl⟩ : syracuseStep 2108593 = 1581445) B1581445
theorem B2223281 : Blo 1315976 2223281 := bstep (se 2 (by rfl) ⟨833730, by rfl⟩ : syracuseStep 2223281 = 1667461) B1667461
theorem B5704931 : Blo 1315976 5704931 := bstep (se 1 (by rfl) ⟨4278698, by rfl⟩ : syracuseStep 5704931 = 8557397) B8557397
theorem B2223409 : Blo 1315976 2223409 := bstep (se 2 (by rfl) ⟨833778, by rfl⟩ : syracuseStep 2223409 = 1667557) B1667557
theorem B2223443 : Blo 1315976 2223443 := bstep (se 1 (by rfl) ⟨1667582, by rfl⟩ : syracuseStep 2223443 = 3335165) B3335165
theorem B6327665 : Blo 1315976 6327665 := bstep (se 2 (by rfl) ⟨2372874, by rfl⟩ : syracuseStep 6327665 = 4745749) B4745749
theorem B5000561 : Blo 1315976 5000561 := bstep (se 2 (by rfl) ⟨1875210, by rfl⟩ : syracuseStep 5000561 = 3750421) B3750421
theorem B2502019 : Blo 1315976 2502019 := bstep (se 1 (by rfl) ⟨1876514, by rfl⟩ : syracuseStep 2502019 = 3753029) B3753029
theorem B18009485 : Blo 1315976 18009485 := bstep (se 3 (by rfl) ⟨3376778, by rfl⟩ : syracuseStep 18009485 = 6753557) B6753557
theorem B1781137 : Blo 1315976 1781137 := bstep (se 2 (by rfl) ⟨667926, by rfl⟩ : syracuseStep 1781137 = 1335853) B1335853
theorem B2108849 : Blo 1315976 2108849 := bstep (se 2 (by rfl) ⟨790818, by rfl⟩ : syracuseStep 2108849 = 1581637) B1581637
theorem B2502065 : Blo 1315976 2502065 := bstep (se 2 (by rfl) ⟨938274, by rfl⟩ : syracuseStep 2502065 = 1876549) B1876549
theorem B2002387 : Blo 1315976 2002387 := bstep (se 1 (by rfl) ⟨1501790, by rfl⟩ : syracuseStep 2002387 = 3003581) B3003581
theorem B2223571 : Blo 1315976 2223571 := bstep (se 1 (by rfl) ⟨1667678, by rfl⟩ : syracuseStep 2223571 = 3335357) B3335357
theorem B1502707 : Blo 1315976 1502707 := bstep (se 1 (by rfl) ⟨1127030, by rfl⟩ : syracuseStep 1502707 = 2254061) B2254061
theorem B4337155 : Blo 1315976 4337155 := bstep (se 1 (by rfl) ⟨3252866, by rfl⟩ : syracuseStep 4337155 = 6505733) B6505733
theorem B1666595 : Blo 1315976 1666595 := bstep (se 1 (by rfl) ⟨1249946, by rfl⟩ : syracuseStep 1666595 = 2499893) B2499893
theorem B2960963 : Blo 1315976 2960963 := bstep (se 1 (by rfl) ⟨2220722, by rfl⟩ : syracuseStep 2960963 = 4441445) B4441445
theorem B2223713 : Blo 1315976 2223713 := bstep (se 2 (by rfl) ⟨833892, by rfl⟩ : syracuseStep 2223713 = 1667785) B1667785
theorem B7499405 : Blo 1315976 7499405 := bstep (se 3 (by rfl) ⟨1406138, by rfl⟩ : syracuseStep 7499405 = 2812277) B2812277
theorem B4443821 : Blo 1315976 4443821 := bstep (se 3 (by rfl) ⟨833216, by rfl⟩ : syracuseStep 4443821 = 1666433) B1666433
theorem B3747505 : Blo 1315976 3747505 := bstep (se 2 (by rfl) ⟨1405314, by rfl⟩ : syracuseStep 3747505 = 2810629) B2810629
theorem B4746929 : Blo 1315976 4746929 := bstep (se 2 (by rfl) ⟨1780098, by rfl⟩ : syracuseStep 4746929 = 3560197) B3560197
theorem B2223841 : Blo 1315976 2223841 := bstep (se 2 (by rfl) ⟨833940, by rfl⟩ : syracuseStep 2223841 = 1667881) B1667881
theorem B4443875 : Blo 1315976 4443875 := bstep (se 1 (by rfl) ⟨3332906, by rfl⟩ : syracuseStep 4443875 = 6665813) B6665813
theorem B2223875 : Blo 1315976 2223875 := bstep (se 1 (by rfl) ⟨1667906, by rfl⟩ : syracuseStep 2223875 = 3335813) B3335813
theorem B17100557 : Blo 1315976 17100557 := bstep (se 3 (by rfl) ⟨3206354, by rfl⟩ : syracuseStep 17100557 = 6412709) B6412709
theorem B2961233 : Blo 1315976 2961233 := bstep (se 2 (by rfl) ⟨1110462, by rfl⟩ : syracuseStep 2961233 = 2220925) B2220925
theorem B2961251 : Blo 1315976 2961251 := bstep (se 1 (by rfl) ⟨2220938, by rfl⟩ : syracuseStep 2961251 = 4441877) B4441877
theorem B2224003 : Blo 1315976 2224003 := bstep (se 1 (by rfl) ⟨1668002, by rfl⟩ : syracuseStep 2224003 = 3336005) B3336005
theorem B3379121 : Blo 1315976 3379121 := bstep (se 2 (by rfl) ⟨1267170, by rfl⟩ : syracuseStep 3379121 = 2534341) B2534341
theorem B3747779 : Blo 1315976 3747779 := bstep (se 1 (by rfl) ⟨2810834, by rfl⟩ : syracuseStep 3747779 = 5621669) B5621669
theorem B22491107 : Blo 1315976 22491107 := bstep (se 1 (by rfl) ⟨16868330, by rfl⟩ : syracuseStep 22491107 = 33736661) B33736661
theorem B4444145 : Blo 1315976 4444145 := bstep (se 2 (by rfl) ⟨1666554, by rfl⟩ : syracuseStep 4444145 = 3333109) B3333109
theorem B2961521 : Blo 1315976 2961521 := bstep (se 2 (by rfl) ⟨1110570, by rfl⟩ : syracuseStep 2961521 = 2221141) B2221141
theorem B3747971 : Blo 1315976 3747971 := bstep (se 1 (by rfl) ⟨2810978, by rfl⟩ : syracuseStep 3747971 = 5621957) B5621957
theorem B2961539 : Blo 1315976 2961539 := bstep (se 1 (by rfl) ⟨2221154, by rfl⟩ : syracuseStep 2961539 = 4442309) B4442309
theorem B9998477 : Blo 1315976 9998477 := bstep (se 3 (by rfl) ⟨1874714, by rfl⟩ : syracuseStep 9998477 = 3749429) B3749429
theorem B6664355 : Blo 1315976 6664355 := bstep (se 1 (by rfl) ⟨4998266, by rfl⟩ : syracuseStep 6664355 = 9996533) B9996533
theorem B2814115 : Blo 1315976 2814115 := bstep (se 1 (by rfl) ⟨2110586, by rfl⟩ : syracuseStep 2814115 = 4221173) B4221173
theorem B1667299 : Blo 1315976 1667299 := bstep (se 1 (by rfl) ⟨1250474, by rfl⟩ : syracuseStep 1667299 = 2500949) B2500949
theorem B1667395 : Blo 1315976 1667395 := bstep (se 1 (by rfl) ⟨1250546, by rfl⟩ : syracuseStep 1667395 = 2501093) B2501093
theorem B2961809 : Blo 1315976 2961809 := bstep (se 2 (by rfl) ⟨1110678, by rfl⟩ : syracuseStep 2961809 = 2221357) B2221357
theorem B2961827 : Blo 1315976 2961827 := bstep (se 1 (by rfl) ⟨2221370, by rfl⟩ : syracuseStep 2961827 = 4442741) B4442741
theorem B4444685 : Blo 1315976 4444685 := bstep (se 3 (by rfl) ⟨833378, by rfl⟩ : syracuseStep 4444685 = 1666757) B1666757
theorem B4444739 : Blo 1315976 4444739 := bstep (se 1 (by rfl) ⟨3333554, by rfl⟩ : syracuseStep 4444739 = 6667109) B6667109
theorem B2962097 : Blo 1315976 2962097 := bstep (se 2 (by rfl) ⟨1110786, by rfl⟩ : syracuseStep 2962097 = 2221573) B2221573
theorem B2962115 : Blo 1315976 2962115 := bstep (se 1 (by rfl) ⟨2221586, by rfl⟩ : syracuseStep 2962115 = 4443173) B4443173
theorem B5002019 : Blo 1315976 5002019 := bstep (se 1 (by rfl) ⟨3751514, by rfl⟩ : syracuseStep 5002019 = 7503029) B7503029
theorem B5002033 : Blo 1315976 5002033 := bstep (se 2 (by rfl) ⟨1875762, by rfl⟩ : syracuseStep 5002033 = 3751525) B3751525
theorem B2110259 : Blo 1315976 2110259 := bstep (se 1 (by rfl) ⟨1582694, by rfl⟩ : syracuseStep 2110259 = 3165389) B3165389
theorem B1667891 : Blo 1315976 1667891 := bstep (se 1 (by rfl) ⟨1250918, by rfl⟩ : syracuseStep 1667891 = 2501837) B2501837
theorem B4445009 : Blo 1315976 4445009 := bstep (se 2 (by rfl) ⟨1666878, by rfl⟩ : syracuseStep 4445009 = 3333757) B3333757
theorem B2569073 : Blo 1315976 2569073 := bstep (se 2 (by rfl) ⟨963402, by rfl⟩ : syracuseStep 2569073 = 1926805) B1926805
theorem B3748781 : Blo 1315976 3748781 := bstep (se 3 (by rfl) ⟨702896, by rfl⟩ : syracuseStep 3748781 = 1405793) B1405793
theorem B6665165 : Blo 1315976 6665165 := bstep (se 3 (by rfl) ⟨1249718, by rfl⟩ : syracuseStep 6665165 = 2499437) B2499437
theorem B2962385 : Blo 1315976 2962385 := bstep (se 2 (by rfl) ⟨1110894, by rfl⟩ : syracuseStep 2962385 = 2221789) B2221789
theorem B2962403 : Blo 1315976 2962403 := bstep (se 1 (by rfl) ⟨2221802, by rfl⟩ : syracuseStep 2962403 = 4443605) B4443605
theorem B6329315 : Blo 1315976 6329315 := bstep (se 1 (by rfl) ⟨4746986, by rfl⟩ : syracuseStep 6329315 = 9493973) B9493973
theorem B3748963 : Blo 1315976 3748963 := bstep (se 1 (by rfl) ⟨2811722, by rfl⟩ : syracuseStep 3748963 = 5623445) B5623445
theorem B43308145 : Blo 1315976 43308145 := bstep (se 2 (by rfl) ⟨16240554, by rfl⟩ : syracuseStep 43308145 = 32481109) B32481109
theorem B1315987 : Blo 1315976 1315987 := bstep (se 1 (by rfl) ⟨986990, by rfl⟩ : syracuseStep 1315987 = 1973981) B1973981
theorem B1316003 : Blo 1315976 1316003 := bstep (se 1 (by rfl) ⟨987002, by rfl⟩ : syracuseStep 1316003 = 1974005) B1974005
theorem B1316019 : Blo 1315976 1316019 := bstep (se 1 (by rfl) ⟨987014, by rfl⟩ : syracuseStep 1316019 = 1974029) B1974029
theorem B1316035 : Blo 1315976 1316035 := bstep (se 1 (by rfl) ⟨987026, by rfl⟩ : syracuseStep 1316035 = 1974053) B1974053
theorem B1316051 : Blo 1315976 1316051 := bstep (se 1 (by rfl) ⟨987038, by rfl⟩ : syracuseStep 1316051 = 1974077) B1974077
theorem B1316067 : Blo 1315976 1316067 := bstep (se 1 (by rfl) ⟨987050, by rfl⟩ : syracuseStep 1316067 = 1974101) B1974101
theorem B2962673 : Blo 1315976 2962673 := bstep (se 2 (by rfl) ⟨1111002, by rfl⟩ : syracuseStep 2962673 = 2222005) B2222005
theorem B1316083 : Blo 1315976 1316083 := bstep (se 1 (by rfl) ⟨987062, by rfl⟩ : syracuseStep 1316083 = 1974125) B1974125
theorem B1316099 : Blo 1315976 1316099 := bstep (se 1 (by rfl) ⟨987074, by rfl⟩ : syracuseStep 1316099 = 1974149) B1974149
theorem B2962691 : Blo 1315976 2962691 := bstep (se 1 (by rfl) ⟨2222018, by rfl⟩ : syracuseStep 2962691 = 4444037) B4444037
theorem B5625101 : Blo 1315976 5625101 := bstep (se 3 (by rfl) ⟨1054706, by rfl⟩ : syracuseStep 5625101 = 2109413) B2109413
theorem B11253005 : Blo 1315976 11253005 := bstep (se 3 (by rfl) ⟨2109938, by rfl⟩ : syracuseStep 11253005 = 4219877) B4219877
theorem B1316115 : Blo 1315976 1316115 := bstep (se 1 (by rfl) ⟨987086, by rfl⟩ : syracuseStep 1316115 = 1974173) B1974173
theorem B1316131 : Blo 1315976 1316131 := bstep (se 1 (by rfl) ⟨987098, by rfl⟩ : syracuseStep 1316131 = 1974197) B1974197
theorem B1316147 : Blo 1315976 1316147 := bstep (se 1 (by rfl) ⟨987110, by rfl⟩ : syracuseStep 1316147 = 1974221) B1974221
theorem B1316163 : Blo 1315976 1316163 := bstep (se 1 (by rfl) ⟨987122, by rfl⟩ : syracuseStep 1316163 = 1974245) B1974245
theorem B1316179 : Blo 1315976 1316179 := bstep (se 1 (by rfl) ⟨987134, by rfl⟩ : syracuseStep 1316179 = 1974269) B1974269
theorem B1316195 : Blo 1315976 1316195 := bstep (se 1 (by rfl) ⟨987146, by rfl⟩ : syracuseStep 1316195 = 1974293) B1974293
theorem B4445549 : Blo 1315976 4445549 := bstep (se 3 (by rfl) ⟨833540, by rfl⟩ : syracuseStep 4445549 = 1667081) B1667081
theorem B1316211 : Blo 1315976 1316211 := bstep (se 1 (by rfl) ⟨987158, by rfl⟩ : syracuseStep 1316211 = 1974317) B1974317
theorem B1316227 : Blo 1315976 1316227 := bstep (se 1 (by rfl) ⟨987170, by rfl⟩ : syracuseStep 1316227 = 1974341) B1974341
theorem B1316243 : Blo 1315976 1316243 := bstep (se 1 (by rfl) ⟨987182, by rfl⟩ : syracuseStep 1316243 = 1974365) B1974365
theorem B1316259 : Blo 1315976 1316259 := bstep (se 1 (by rfl) ⟨987194, by rfl⟩ : syracuseStep 1316259 = 1974389) B1974389
theorem B4445603 : Blo 1315976 4445603 := bstep (se 1 (by rfl) ⟨3334202, by rfl⟩ : syracuseStep 4445603 = 6668405) B6668405
theorem B1316275 : Blo 1315976 1316275 := bstep (se 1 (by rfl) ⟨987206, by rfl⟩ : syracuseStep 1316275 = 1974413) B1974413
theorem B1316291 : Blo 1315976 1316291 := bstep (se 1 (by rfl) ⟨987218, by rfl⟩ : syracuseStep 1316291 = 1974437) B1974437
theorem B1316307 : Blo 1315976 1316307 := bstep (se 1 (by rfl) ⟨987230, by rfl⟩ : syracuseStep 1316307 = 1974461) B1974461
theorem B1316323 : Blo 1315976 1316323 := bstep (se 1 (by rfl) ⟨987242, by rfl⟩ : syracuseStep 1316323 = 1974485) B1974485
theorem B1316339 : Blo 1315976 1316339 := bstep (se 1 (by rfl) ⟨987254, by rfl⟩ : syracuseStep 1316339 = 1974509) B1974509
theorem B1316355 : Blo 1315976 1316355 := bstep (se 1 (by rfl) ⟨987266, by rfl⟩ : syracuseStep 1316355 = 1974533) B1974533
theorem B3331601 : Blo 1315976 3331601 := bstep (se 2 (by rfl) ⟨1249350, by rfl⟩ : syracuseStep 3331601 = 2498701) B2498701
theorem B2962961 : Blo 1315976 2962961 := bstep (se 2 (by rfl) ⟨1111110, by rfl⟩ : syracuseStep 2962961 = 2222221) B2222221
theorem B1316371 : Blo 1315976 1316371 := bstep (se 1 (by rfl) ⟨987278, by rfl⟩ : syracuseStep 1316371 = 1974557) B1974557
theorem B1316387 : Blo 1315976 1316387 := bstep (se 1 (by rfl) ⟨987290, by rfl⟩ : syracuseStep 1316387 = 1974581) B1974581
theorem B2962979 : Blo 1315976 2962979 := bstep (se 1 (by rfl) ⟨2222234, by rfl⟩ : syracuseStep 2962979 = 4444469) B4444469
theorem B1316403 : Blo 1315976 1316403 := bstep (se 1 (by rfl) ⟨987302, by rfl⟩ : syracuseStep 1316403 = 1974605) B1974605
theorem B3331651 : Blo 1315976 3331651 := bstep (se 1 (by rfl) ⟨2498738, by rfl⟩ : syracuseStep 3331651 = 4997477) B4997477
theorem B1316419 : Blo 1315976 1316419 := bstep (se 1 (by rfl) ⟨987314, by rfl⟩ : syracuseStep 1316419 = 1974629) B1974629
theorem B3749453 : Blo 1315976 3749453 := bstep (se 3 (by rfl) ⟨703022, by rfl⟩ : syracuseStep 3749453 = 1406045) B1406045
theorem B1316435 : Blo 1315976 1316435 := bstep (se 1 (by rfl) ⟨987326, by rfl⟩ : syracuseStep 1316435 = 1974653) B1974653
theorem B1316451 : Blo 1315976 1316451 := bstep (se 1 (by rfl) ⟨987338, by rfl⟩ : syracuseStep 1316451 = 1974677) B1974677
theorem B5625443 : Blo 1315976 5625443 := bstep (se 1 (by rfl) ⟨4219082, by rfl⟩ : syracuseStep 5625443 = 8438165) B8438165
theorem B2438755 : Blo 1315976 2438755 := bstep (se 1 (by rfl) ⟨1829066, by rfl⟩ : syracuseStep 2438755 = 3658133) B3658133
theorem B1316467 : Blo 1315976 1316467 := bstep (se 1 (by rfl) ⟨987350, by rfl⟩ : syracuseStep 1316467 = 1974701) B1974701
theorem B2111105 : Blo 1315976 2111105 := bstep (se 2 (by rfl) ⟨791664, by rfl⟩ : syracuseStep 2111105 = 1583329) B1583329
theorem B1316483 : Blo 1315976 1316483 := bstep (se 1 (by rfl) ⟨987362, by rfl⟩ : syracuseStep 1316483 = 1974725) B1974725
theorem B1316499 : Blo 1315976 1316499 := bstep (se 1 (by rfl) ⟨987374, by rfl⟩ : syracuseStep 1316499 = 1974749) B1974749
theorem B1316515 : Blo 1315976 1316515 := bstep (se 1 (by rfl) ⟨987386, by rfl⟩ : syracuseStep 1316515 = 1974773) B1974773
theorem B8115889 : Blo 1315976 8115889 := bstep (se 2 (by rfl) ⟨3043458, by rfl⟩ : syracuseStep 8115889 = 6086917) B6086917
theorem B4445873 : Blo 1315976 4445873 := bstep (se 2 (by rfl) ⟨1667202, by rfl⟩ : syracuseStep 4445873 = 3334405) B3334405
theorem B1316531 : Blo 1315976 1316531 := bstep (se 1 (by rfl) ⟨987398, by rfl⟩ : syracuseStep 1316531 = 1974797) B1974797
theorem B1316547 : Blo 1315976 1316547 := bstep (se 1 (by rfl) ⟨987410, by rfl⟩ : syracuseStep 1316547 = 1974821) B1974821
theorem B8443597 : Blo 1315976 8443597 := bstep (se 3 (by rfl) ⟨1583174, by rfl⟩ : syracuseStep 8443597 = 3166349) B3166349
theorem B3331793 : Blo 1315976 3331793 := bstep (se 2 (by rfl) ⟨1249422, by rfl⟩ : syracuseStep 3331793 = 2498845) B2498845
theorem B1316563 : Blo 1315976 1316563 := bstep (se 1 (by rfl) ⟨987422, by rfl⟩ : syracuseStep 1316563 = 1974845) B1974845
theorem B1316579 : Blo 1315976 1316579 := bstep (se 1 (by rfl) ⟨987434, by rfl⟩ : syracuseStep 1316579 = 1974869) B1974869
theorem B1316595 : Blo 1315976 1316595 := bstep (se 1 (by rfl) ⟨987446, by rfl⟩ : syracuseStep 1316595 = 1974893) B1974893
theorem B1316611 : Blo 1315976 1316611 := bstep (se 1 (by rfl) ⟨987458, by rfl⟩ : syracuseStep 1316611 = 1974917) B1974917
theorem B2029331 : Blo 1315976 2029331 := bstep (se 1 (by rfl) ⟨1521998, by rfl⟩ : syracuseStep 2029331 = 3043997) B3043997
theorem B1316627 : Blo 1315976 1316627 := bstep (se 1 (by rfl) ⟨987470, by rfl⟩ : syracuseStep 1316627 = 1974941) B1974941
theorem B1316643 : Blo 1315976 1316643 := bstep (se 1 (by rfl) ⟨987482, by rfl⟩ : syracuseStep 1316643 = 1974965) B1974965
theorem B2963249 : Blo 1315976 2963249 := bstep (se 2 (by rfl) ⟨1111218, by rfl⟩ : syracuseStep 2963249 = 2222437) B2222437
theorem B1316659 : Blo 1315976 1316659 := bstep (se 1 (by rfl) ⟨987494, by rfl⟩ : syracuseStep 1316659 = 1974989) B1974989
theorem B1316675 : Blo 1315976 1316675 := bstep (se 1 (by rfl) ⟨987506, by rfl⟩ : syracuseStep 1316675 = 1975013) B1975013
theorem B2963267 : Blo 1315976 2963267 := bstep (se 1 (by rfl) ⟨2222450, by rfl⟩ : syracuseStep 2963267 = 4444901) B4444901
theorem B1480531 : Blo 1315976 1480531 := bstep (se 1 (by rfl) ⟨1110398, by rfl⟩ : syracuseStep 1480531 = 2220797) B2220797
theorem B1316691 : Blo 1315976 1316691 := bstep (se 1 (by rfl) ⟨987518, by rfl⟩ : syracuseStep 1316691 = 1975037) B1975037
theorem B1316707 : Blo 1315976 1316707 := bstep (se 1 (by rfl) ⟨987530, by rfl⟩ : syracuseStep 1316707 = 1975061) B1975061
theorem B1316723 : Blo 1315976 1316723 := bstep (se 1 (by rfl) ⟨987542, by rfl⟩ : syracuseStep 1316723 = 1975085) B1975085
theorem B1316739 : Blo 1315976 1316739 := bstep (se 1 (by rfl) ⟨987554, by rfl⟩ : syracuseStep 1316739 = 1975109) B1975109
theorem B1316755 : Blo 1315976 1316755 := bstep (se 1 (by rfl) ⟨987566, by rfl⟩ : syracuseStep 1316755 = 1975133) B1975133
theorem B1316771 : Blo 1315976 1316771 := bstep (se 1 (by rfl) ⟨987578, by rfl⟩ : syracuseStep 1316771 = 1975157) B1975157
theorem B1316787 : Blo 1315976 1316787 := bstep (se 1 (by rfl) ⟨987590, by rfl⟩ : syracuseStep 1316787 = 1975181) B1975181
theorem B1406899 : Blo 1315976 1406899 := bstep (se 1 (by rfl) ⟨1055174, by rfl⟩ : syracuseStep 1406899 = 2110349) B2110349
theorem B1316803 : Blo 1315976 1316803 := bstep (se 1 (by rfl) ⟨987602, by rfl⟩ : syracuseStep 1316803 = 1975205) B1975205
theorem B1316819 : Blo 1315976 1316819 := bstep (se 1 (by rfl) ⟨987614, by rfl⟩ : syracuseStep 1316819 = 1975229) B1975229
theorem B1480675 : Blo 1315976 1480675 := bstep (se 1 (by rfl) ⟨1110506, by rfl⟩ : syracuseStep 1480675 = 2221013) B2221013
theorem B1316835 : Blo 1315976 1316835 := bstep (se 1 (by rfl) ⟨987626, by rfl⟩ : syracuseStep 1316835 = 1975253) B1975253
theorem B15210467 : Blo 1315976 15210467 := bstep (se 1 (by rfl) ⟨11407850, by rfl⟩ : syracuseStep 15210467 = 22815701) B22815701
theorem B1316851 : Blo 1315976 1316851 := bstep (se 1 (by rfl) ⟨987638, by rfl⟩ : syracuseStep 1316851 = 1975277) B1975277
theorem B1316867 : Blo 1315976 1316867 := bstep (se 1 (by rfl) ⟨987650, by rfl⟩ : syracuseStep 1316867 = 1975301) B1975301
theorem B1316883 : Blo 1315976 1316883 := bstep (se 1 (by rfl) ⟨987662, by rfl⟩ : syracuseStep 1316883 = 1975325) B1975325
theorem B1316899 : Blo 1315976 1316899 := bstep (se 1 (by rfl) ⟨987674, by rfl⟩ : syracuseStep 1316899 = 1975349) B1975349
theorem B5068835 : Blo 1315976 5068835 := bstep (se 1 (by rfl) ⟨3801626, by rfl⟩ : syracuseStep 5068835 = 7603253) B7603253
theorem B3004465 : Blo 1315976 3004465 := bstep (se 2 (by rfl) ⟨1126674, by rfl⟩ : syracuseStep 3004465 = 2253349) B2253349
theorem B1316915 : Blo 1315976 1316915 := bstep (se 1 (by rfl) ⟨987686, by rfl⟩ : syracuseStep 1316915 = 1975373) B1975373
theorem B1316931 : Blo 1315976 1316931 := bstep (se 1 (by rfl) ⟨987698, by rfl⟩ : syracuseStep 1316931 = 1975397) B1975397
theorem B2963537 : Blo 1315976 2963537 := bstep (se 2 (by rfl) ⟨1111326, by rfl⟩ : syracuseStep 2963537 = 2222653) B2222653
theorem B1316947 : Blo 1315976 1316947 := bstep (se 1 (by rfl) ⟨987710, by rfl⟩ : syracuseStep 1316947 = 1975421) B1975421
theorem B4216931 : Blo 1315976 4216931 := bstep (se 1 (by rfl) ⟨3162698, by rfl⟩ : syracuseStep 4216931 = 6325397) B6325397
theorem B1316963 : Blo 1315976 1316963 := bstep (se 1 (by rfl) ⟨987722, by rfl⟩ : syracuseStep 1316963 = 1975445) B1975445
theorem B2963555 : Blo 1315976 2963555 := bstep (se 1 (by rfl) ⟨2222666, by rfl⟩ : syracuseStep 2963555 = 4445333) B4445333
theorem B3561581 : Blo 1315976 3561581 := bstep (se 3 (by rfl) ⟨667796, by rfl⟩ : syracuseStep 3561581 = 1335593) B1335593
theorem B1480819 : Blo 1315976 1480819 := bstep (se 1 (by rfl) ⟨1110614, by rfl⟩ : syracuseStep 1480819 = 2221229) B2221229
theorem B1316979 : Blo 1315976 1316979 := bstep (se 1 (by rfl) ⟨987734, by rfl⟩ : syracuseStep 1316979 = 1975469) B1975469
theorem B1316995 : Blo 1315976 1316995 := bstep (se 1 (by rfl) ⟨987746, by rfl⟩ : syracuseStep 1316995 = 1975493) B1975493
theorem B1317011 : Blo 1315976 1317011 := bstep (se 1 (by rfl) ⟨987758, by rfl⟩ : syracuseStep 1317011 = 1975517) B1975517
theorem B1317027 : Blo 1315976 1317027 := bstep (se 1 (by rfl) ⟨987770, by rfl⟩ : syracuseStep 1317027 = 1975541) B1975541
theorem B2668721 : Blo 1315976 2668721 := bstep (se 2 (by rfl) ⟨1000770, by rfl⟩ : syracuseStep 2668721 = 2001541) B2001541
theorem B1317043 : Blo 1315976 1317043 := bstep (se 1 (by rfl) ⟨987782, by rfl⟩ : syracuseStep 1317043 = 1975565) B1975565
theorem B1317059 : Blo 1315976 1317059 := bstep (se 1 (by rfl) ⟨987794, by rfl⟩ : syracuseStep 1317059 = 1975589) B1975589
theorem B4446413 : Blo 1315976 4446413 := bstep (se 3 (by rfl) ⟨833702, by rfl⟩ : syracuseStep 4446413 = 1667405) B1667405
theorem B1317075 : Blo 1315976 1317075 := bstep (se 1 (by rfl) ⟨987806, by rfl⟩ : syracuseStep 1317075 = 1975613) B1975613
theorem B1317091 : Blo 1315976 1317091 := bstep (se 1 (by rfl) ⟨987818, by rfl⟩ : syracuseStep 1317091 = 1975637) B1975637
theorem B5003491 : Blo 1315976 5003491 := bstep (se 1 (by rfl) ⟨3752618, by rfl⟩ : syracuseStep 5003491 = 7505237) B7505237
theorem B1317107 : Blo 1315976 1317107 := bstep (se 1 (by rfl) ⟨987830, by rfl⟩ : syracuseStep 1317107 = 1975661) B1975661
theorem B1480963 : Blo 1315976 1480963 := bstep (se 1 (by rfl) ⟨1110722, by rfl⟩ : syracuseStep 1480963 = 2221445) B2221445
theorem B1317123 : Blo 1315976 1317123 := bstep (se 1 (by rfl) ⟨987842, by rfl⟩ : syracuseStep 1317123 = 1975685) B1975685
theorem B4446467 : Blo 1315976 4446467 := bstep (se 1 (by rfl) ⟨3334850, by rfl⟩ : syracuseStep 4446467 = 6669701) B6669701
theorem B1317139 : Blo 1315976 1317139 := bstep (se 1 (by rfl) ⟨987854, by rfl⟩ : syracuseStep 1317139 = 1975709) B1975709
theorem B2668835 : Blo 1315976 2668835 := bstep (se 1 (by rfl) ⟨2001626, by rfl⟩ : syracuseStep 2668835 = 4003253) B4003253
theorem B1317155 : Blo 1315976 1317155 := bstep (se 1 (by rfl) ⟨987866, by rfl⟩ : syracuseStep 1317155 = 1975733) B1975733
theorem B1874225 : Blo 1315976 1874225 := bstep (se 2 (by rfl) ⟨702834, by rfl⟩ : syracuseStep 1874225 = 1405669) B1405669
theorem B1317171 : Blo 1315976 1317171 := bstep (se 1 (by rfl) ⟨987878, by rfl⟩ : syracuseStep 1317171 = 1975757) B1975757
theorem B1317187 : Blo 1315976 1317187 := bstep (se 1 (by rfl) ⟨987890, by rfl⟩ : syracuseStep 1317187 = 1975781) B1975781
theorem B1317203 : Blo 1315976 1317203 := bstep (se 1 (by rfl) ⟨987902, by rfl⟩ : syracuseStep 1317203 = 1975805) B1975805
theorem B1317219 : Blo 1315976 1317219 := bstep (se 1 (by rfl) ⟨987914, by rfl⟩ : syracuseStep 1317219 = 1975829) B1975829
theorem B1407331 : Blo 1315976 1407331 := bstep (se 1 (by rfl) ⟨1055498, by rfl⟩ : syracuseStep 1407331 = 2110997) B2110997
theorem B2963825 : Blo 1315976 2963825 := bstep (se 2 (by rfl) ⟨1111434, by rfl⟩ : syracuseStep 2963825 = 2222869) B2222869
theorem B1317235 : Blo 1315976 1317235 := bstep (se 1 (by rfl) ⟨987926, by rfl⟩ : syracuseStep 1317235 = 1975853) B1975853
theorem B1317251 : Blo 1315976 1317251 := bstep (se 1 (by rfl) ⟨987938, by rfl⟩ : syracuseStep 1317251 = 1975877) B1975877
theorem B2963843 : Blo 1315976 2963843 := bstep (se 1 (by rfl) ⟨2222882, by rfl⟩ : syracuseStep 2963843 = 4445765) B4445765
theorem B1481107 : Blo 1315976 1481107 := bstep (se 1 (by rfl) ⟨1110830, by rfl⟩ : syracuseStep 1481107 = 2221661) B2221661
theorem B1317267 : Blo 1315976 1317267 := bstep (se 1 (by rfl) ⟨987950, by rfl⟩ : syracuseStep 1317267 = 1975901) B1975901
theorem B1317283 : Blo 1315976 1317283 := bstep (se 1 (by rfl) ⟨987962, by rfl⟩ : syracuseStep 1317283 = 1975925) B1975925
theorem B1317299 : Blo 1315976 1317299 := bstep (se 1 (by rfl) ⟨987974, by rfl⟩ : syracuseStep 1317299 = 1975949) B1975949
theorem B1317315 : Blo 1315976 1317315 := bstep (se 1 (by rfl) ⟨987986, by rfl⟩ : syracuseStep 1317315 = 1975973) B1975973
theorem B1317331 : Blo 1315976 1317331 := bstep (se 1 (by rfl) ⟨987998, by rfl⟩ : syracuseStep 1317331 = 1975997) B1975997
theorem B1317347 : Blo 1315976 1317347 := bstep (se 1 (by rfl) ⟨988010, by rfl⟩ : syracuseStep 1317347 = 1976021) B1976021
theorem B7502321 : Blo 1315976 7502321 := bstep (se 2 (by rfl) ⟨2813370, by rfl⟩ : syracuseStep 7502321 = 5626741) B5626741
theorem B1317363 : Blo 1315976 1317363 := bstep (se 1 (by rfl) ⟨988022, by rfl⟩ : syracuseStep 1317363 = 1976045) B1976045
theorem B1317379 : Blo 1315976 1317379 := bstep (se 1 (by rfl) ⟨988034, by rfl⟩ : syracuseStep 1317379 = 1976069) B1976069
theorem B4446737 : Blo 1315976 4446737 := bstep (se 2 (by rfl) ⟨1667526, by rfl⟩ : syracuseStep 4446737 = 3335053) B3335053
theorem B1317395 : Blo 1315976 1317395 := bstep (se 1 (by rfl) ⟨988046, by rfl⟩ : syracuseStep 1317395 = 1976093) B1976093
theorem B1481251 : Blo 1315976 1481251 := bstep (se 1 (by rfl) ⟨1110938, by rfl⟩ : syracuseStep 1481251 = 2221877) B2221877
theorem B1317411 : Blo 1315976 1317411 := bstep (se 1 (by rfl) ⟨988058, by rfl⟩ : syracuseStep 1317411 = 1976117) B1976117
theorem B1317427 : Blo 1315976 1317427 := bstep (se 1 (by rfl) ⟨988070, by rfl⟩ : syracuseStep 1317427 = 1976141) B1976141
theorem B1317443 : Blo 1315976 1317443 := bstep (se 1 (by rfl) ⟨988082, by rfl⟩ : syracuseStep 1317443 = 1976165) B1976165
theorem B1317459 : Blo 1315976 1317459 := bstep (se 1 (by rfl) ⟨988094, by rfl⟩ : syracuseStep 1317459 = 1976189) B1976189
theorem B1317475 : Blo 1315976 1317475 := bstep (se 1 (by rfl) ⟨988106, by rfl⟩ : syracuseStep 1317475 = 1976213) B1976213
theorem B4504177 : Blo 1315976 4504177 := bstep (se 2 (by rfl) ⟨1689066, by rfl⟩ : syracuseStep 4504177 = 3378133) B3378133
theorem B1317491 : Blo 1315976 1317491 := bstep (se 1 (by rfl) ⟨988118, by rfl⟩ : syracuseStep 1317491 = 1976237) B1976237
theorem B1317507 : Blo 1315976 1317507 := bstep (se 1 (by rfl) ⟨988130, by rfl⟩ : syracuseStep 1317507 = 1976261) B1976261
theorem B2964113 : Blo 1315976 2964113 := bstep (se 2 (by rfl) ⟨1111542, by rfl⟩ : syracuseStep 2964113 = 2223085) B2223085
theorem B1317523 : Blo 1315976 1317523 := bstep (se 1 (by rfl) ⟨988142, by rfl⟩ : syracuseStep 1317523 = 1976285) B1976285
theorem B2964131 : Blo 1315976 2964131 := bstep (se 1 (by rfl) ⟨2223098, by rfl⟩ : syracuseStep 2964131 = 4446197) B4446197
theorem B1317539 : Blo 1315976 1317539 := bstep (se 1 (by rfl) ⟨988154, by rfl⟩ : syracuseStep 1317539 = 1976309) B1976309
theorem B3332785 : Blo 1315976 3332785 := bstep (se 2 (by rfl) ⟨1249794, by rfl⟩ : syracuseStep 3332785 = 2499589) B2499589
theorem B1481395 : Blo 1315976 1481395 := bstep (se 1 (by rfl) ⟨1111046, by rfl⟩ : syracuseStep 1481395 = 2222093) B2222093
theorem B1317555 : Blo 1315976 1317555 := bstep (se 1 (by rfl) ⟨988166, by rfl⟩ : syracuseStep 1317555 = 1976333) B1976333
theorem B1333955 : Blo 1315976 1333955 := bstep (se 1 (by rfl) ⟨1000466, by rfl⟩ : syracuseStep 1333955 = 2000933) B2000933
theorem B1317571 : Blo 1315976 1317571 := bstep (se 1 (by rfl) ⟨988178, by rfl⟩ : syracuseStep 1317571 = 1976357) B1976357
theorem B6331085 : Blo 1315976 6331085 := bstep (se 3 (by rfl) ⟨1187078, by rfl⟩ : syracuseStep 6331085 = 2374157) B2374157
theorem B1317587 : Blo 1315976 1317587 := bstep (se 1 (by rfl) ⟨988190, by rfl⟩ : syracuseStep 1317587 = 1976381) B1976381
theorem B4004579 : Blo 1315976 4004579 := bstep (se 1 (by rfl) ⟨3003434, by rfl⟩ : syracuseStep 4004579 = 6006869) B6006869
theorem B1317603 : Blo 1315976 1317603 := bstep (se 1 (by rfl) ⟨988202, by rfl⟩ : syracuseStep 1317603 = 1976405) B1976405
theorem B3750637 : Blo 1315976 3750637 := bstep (se 3 (by rfl) ⟨703244, by rfl⟩ : syracuseStep 3750637 = 1406489) B1406489
theorem B1317619 : Blo 1315976 1317619 := bstep (se 1 (by rfl) ⟨988214, by rfl⟩ : syracuseStep 1317619 = 1976429) B1976429
theorem B1317635 : Blo 1315976 1317635 := bstep (se 1 (by rfl) ⟨988226, by rfl⟩ : syracuseStep 1317635 = 1976453) B1976453
theorem B1317651 : Blo 1315976 1317651 := bstep (se 1 (by rfl) ⟨988238, by rfl⟩ : syracuseStep 1317651 = 1976477) B1976477
theorem B1317667 : Blo 1315976 1317667 := bstep (se 1 (by rfl) ⟨988250, by rfl⟩ : syracuseStep 1317667 = 1976501) B1976501
theorem B1317683 : Blo 1315976 1317683 := bstep (se 1 (by rfl) ⟨988262, by rfl⟩ : syracuseStep 1317683 = 1976525) B1976525
theorem B1874755 : Blo 1315976 1874755 := bstep (se 1 (by rfl) ⟨1406066, by rfl⟩ : syracuseStep 1874755 = 2812133) B2812133
theorem B1481539 : Blo 1315976 1481539 := bstep (se 1 (by rfl) ⟨1111154, by rfl⟩ : syracuseStep 1481539 = 2222309) B2222309
theorem B1317699 : Blo 1315976 1317699 := bstep (se 1 (by rfl) ⟨988274, by rfl⟩ : syracuseStep 1317699 = 1976549) B1976549
theorem B1317715 : Blo 1315976 1317715 := bstep (se 1 (by rfl) ⟨988286, by rfl⟩ : syracuseStep 1317715 = 1976573) B1976573
theorem B1317731 : Blo 1315976 1317731 := bstep (se 1 (by rfl) ⟨988298, by rfl⟩ : syracuseStep 1317731 = 1976597) B1976597
theorem B1317747 : Blo 1315976 1317747 := bstep (se 1 (by rfl) ⟨988310, by rfl⟩ : syracuseStep 1317747 = 1976621) B1976621
theorem B1604483 : Blo 1315976 1604483 := bstep (se 1 (by rfl) ⟨1203362, by rfl⟩ : syracuseStep 1604483 = 2406725) B2406725
theorem B1317763 : Blo 1315976 1317763 := bstep (se 1 (by rfl) ⟨988322, by rfl⟩ : syracuseStep 1317763 = 1976645) B1976645
theorem B1317779 : Blo 1315976 1317779 := bstep (se 1 (by rfl) ⟨988334, by rfl⟩ : syracuseStep 1317779 = 1976669) B1976669
theorem B1317795 : Blo 1315976 1317795 := bstep (se 1 (by rfl) ⟨988346, by rfl⟩ : syracuseStep 1317795 = 1976693) B1976693
theorem B2964401 : Blo 1315976 2964401 := bstep (se 2 (by rfl) ⟨1111650, by rfl⟩ : syracuseStep 2964401 = 2223301) B2223301
theorem B1317811 : Blo 1315976 1317811 := bstep (se 1 (by rfl) ⟨988358, by rfl⟩ : syracuseStep 1317811 = 1976717) B1976717
theorem B3333059 : Blo 1315976 3333059 := bstep (se 1 (by rfl) ⟨2499794, by rfl⟩ : syracuseStep 3333059 = 4999589) B4999589
theorem B2964419 : Blo 1315976 2964419 := bstep (se 1 (by rfl) ⟨2223314, by rfl⟩ : syracuseStep 2964419 = 4446629) B4446629
theorem B1317827 : Blo 1315976 1317827 := bstep (se 1 (by rfl) ⟨988370, by rfl⟩ : syracuseStep 1317827 = 1976741) B1976741
theorem B1481683 : Blo 1315976 1481683 := bstep (se 1 (by rfl) ⟨1111262, by rfl⟩ : syracuseStep 1481683 = 2222525) B2222525
theorem B1317843 : Blo 1315976 1317843 := bstep (se 1 (by rfl) ⟨988382, by rfl⟩ : syracuseStep 1317843 = 1976765) B1976765
theorem B4217827 : Blo 1315976 4217827 := bstep (se 1 (by rfl) ⟨3163370, by rfl⟩ : syracuseStep 4217827 = 6326741) B6326741
theorem B1317859 : Blo 1315976 1317859 := bstep (se 1 (by rfl) ⟨988394, by rfl⟩ : syracuseStep 1317859 = 1976789) B1976789
theorem B10001393 : Blo 1315976 10001393 := bstep (se 2 (by rfl) ⟨3750522, by rfl⟩ : syracuseStep 10001393 = 7501045) B7501045
theorem B1317875 : Blo 1315976 1317875 := bstep (se 1 (by rfl) ⟨988406, by rfl⟩ : syracuseStep 1317875 = 1976813) B1976813
theorem B1317891 : Blo 1315976 1317891 := bstep (se 1 (by rfl) ⟨988418, by rfl⟩ : syracuseStep 1317891 = 1976837) B1976837
theorem B1317907 : Blo 1315976 1317907 := bstep (se 1 (by rfl) ⟨988430, by rfl⟩ : syracuseStep 1317907 = 1976861) B1976861
theorem B30063637 : Blo 1315976 30063637 := bstep (se 6 (by rfl) ⟨704616, by rfl⟩ : syracuseStep 30063637 = 1409233) B1409233
theorem B1317923 : Blo 1315976 1317923 := bstep (se 1 (by rfl) ⟨988442, by rfl⟩ : syracuseStep 1317923 = 1976885) B1976885
theorem B4447277 : Blo 1315976 4447277 := bstep (se 3 (by rfl) ⟨833864, by rfl⟩ : syracuseStep 4447277 = 1667729) B1667729
theorem B1317939 : Blo 1315976 1317939 := bstep (se 1 (by rfl) ⟨988454, by rfl⟩ : syracuseStep 1317939 = 1976909) B1976909
theorem B1317955 : Blo 1315976 1317955 := bstep (se 1 (by rfl) ⟨988466, by rfl⟩ : syracuseStep 1317955 = 1976933) B1976933
theorem B1317971 : Blo 1315976 1317971 := bstep (se 1 (by rfl) ⟨988478, by rfl⟩ : syracuseStep 1317971 = 1976957) B1976957
theorem B1481827 : Blo 1315976 1481827 := bstep (se 1 (by rfl) ⟨1111370, by rfl⟩ : syracuseStep 1481827 = 2222741) B2222741
theorem B4447331 : Blo 1315976 4447331 := bstep (se 1 (by rfl) ⟨3335498, by rfl⟩ : syracuseStep 4447331 = 6670997) B6670997
theorem B3333251 : Blo 1315976 3333251 := bstep (se 1 (by rfl) ⟨2499938, by rfl⟩ : syracuseStep 3333251 = 4999877) B4999877
theorem B1875091 : Blo 1315976 1875091 := bstep (se 1 (by rfl) ⟨1406318, by rfl⟩ : syracuseStep 1875091 = 2812637) B2812637
theorem B2964689 : Blo 1315976 2964689 := bstep (se 2 (by rfl) ⟨1111758, by rfl⟩ : syracuseStep 2964689 = 2223517) B2223517
theorem B2964707 : Blo 1315976 2964707 := bstep (se 1 (by rfl) ⟨2223530, by rfl⟩ : syracuseStep 2964707 = 4447061) B4447061
theorem B1481971 : Blo 1315976 1481971 := bstep (se 1 (by rfl) ⟨1111478, by rfl⟩ : syracuseStep 1481971 = 2222957) B2222957
theorem B1424675 : Blo 1315976 1424675 := bstep (se 1 (by rfl) ⟨1068506, by rfl⟩ : syracuseStep 1424675 = 2137013) B2137013
theorem B4447601 : Blo 1315976 4447601 := bstep (se 2 (by rfl) ⟨1667850, by rfl⟩ : syracuseStep 4447601 = 3335701) B3335701
theorem B1482115 : Blo 1315976 1482115 := bstep (se 1 (by rfl) ⟨1111586, by rfl⟩ : syracuseStep 1482115 = 2223173) B2223173
theorem B3800483 : Blo 1315976 3800483 := bstep (se 1 (by rfl) ⟨2850362, by rfl⟩ : syracuseStep 3800483 = 5700725) B5700725
theorem B2964977 : Blo 1315976 2964977 := bstep (se 2 (by rfl) ⟨1111866, by rfl⟩ : syracuseStep 2964977 = 2223733) B2223733
theorem B2964995 : Blo 1315976 2964995 := bstep (se 1 (by rfl) ⟨2223746, by rfl⟩ : syracuseStep 2964995 = 4447493) B4447493
theorem B1482259 : Blo 1315976 1482259 := bstep (se 1 (by rfl) ⟨1111694, by rfl⟩ : syracuseStep 1482259 = 2223389) B2223389
theorem B7118405 : Blo 1315976 7118405 := bstep (se 4 (by rfl) ⟨667350, by rfl⟩ : syracuseStep 7118405 = 1334701) B1334701
theorem B11255395 : Blo 1315976 11255395 := bstep (se 1 (by rfl) ⟨8441546, by rfl⟩ : syracuseStep 11255395 = 16883093) B16883093
theorem B1482403 : Blo 1315976 1482403 := bstep (se 1 (by rfl) ⟨1111802, by rfl⟩ : syracuseStep 1482403 = 2223605) B2223605
theorem B1875649 : Blo 1315976 1875649 := bstep (se 2 (by rfl) ⟨703368, by rfl⟩ : syracuseStep 1875649 = 1406737) B1406737
theorem B1973969 : Blo 1315976 1973969 := bstep (se 2 (by rfl) ⟨740238, by rfl⟩ : syracuseStep 1973969 = 1480477) B1480477
theorem B1973987 : Blo 1315976 1973987 := bstep (se 1 (by rfl) ⟨1480490, by rfl⟩ : syracuseStep 1973987 = 2960981) B2960981
theorem B1875683 : Blo 1315976 1875683 := bstep (se 1 (by rfl) ⟨1406762, by rfl⟩ : syracuseStep 1875683 = 2813525) B2813525
theorem B1974017 : Blo 1315976 1974017 := bstep (se 2 (by rfl) ⟨740256, by rfl⟩ : syracuseStep 1974017 = 1480513) B1480513
theorem B3751697 : Blo 1315976 3751697 := bstep (se 2 (by rfl) ⟨1406886, by rfl⟩ : syracuseStep 3751697 = 2813773) B2813773
theorem B2965265 : Blo 1315976 2965265 := bstep (se 2 (by rfl) ⟨1111974, by rfl⟩ : syracuseStep 2965265 = 2223949) B2223949
theorem B1974035 : Blo 1315976 1974035 := bstep (se 1 (by rfl) ⟨1480526, by rfl⟩ : syracuseStep 1974035 = 2961053) B2961053
theorem B2965283 : Blo 1315976 2965283 := bstep (se 1 (by rfl) ⟨2223962, by rfl⟩ : syracuseStep 2965283 = 4447925) B4447925
theorem B1974065 : Blo 1315976 1974065 := bstep (se 2 (by rfl) ⟨740274, by rfl⟩ : syracuseStep 1974065 = 1480549) B1480549
theorem B6668081 : Blo 1315976 6668081 := bstep (se 2 (by rfl) ⟨2500530, by rfl⟩ : syracuseStep 6668081 = 5001061) B5001061
theorem B1482547 : Blo 1315976 1482547 := bstep (se 1 (by rfl) ⟨1111910, by rfl⟩ : syracuseStep 1482547 = 2223821) B2223821
theorem B1974083 : Blo 1315976 1974083 := bstep (se 1 (by rfl) ⟨1480562, by rfl⟩ : syracuseStep 1974083 = 2961125) B2961125
theorem B1974113 : Blo 1315976 1974113 := bstep (se 2 (by rfl) ⟨740292, by rfl⟩ : syracuseStep 1974113 = 1480585) B1480585
theorem B1974131 : Blo 1315976 1974131 := bstep (se 1 (by rfl) ⟨1480598, by rfl⟩ : syracuseStep 1974131 = 2961197) B2961197
theorem B1335155 : Blo 1315976 1335155 := bstep (se 1 (by rfl) ⟨1001366, by rfl⟩ : syracuseStep 1335155 = 2002733) B2002733
theorem B3161987 : Blo 1315976 3161987 := bstep (se 1 (by rfl) ⟨2371490, by rfl⟩ : syracuseStep 3161987 = 4742981) B4742981
theorem B2498435 : Blo 1315976 2498435 := bstep (se 1 (by rfl) ⟨1873826, by rfl⟩ : syracuseStep 2498435 = 3747653) B3747653
theorem B4448141 : Blo 1315976 4448141 := bstep (se 3 (by rfl) ⟨834026, by rfl⟩ : syracuseStep 4448141 = 1668053) B1668053
theorem B1974161 : Blo 1315976 1974161 := bstep (se 2 (by rfl) ⟨740310, by rfl⟩ : syracuseStep 1974161 = 1480621) B1480621
theorem B1974179 : Blo 1315976 1974179 := bstep (se 1 (by rfl) ⟨1480634, by rfl⟩ : syracuseStep 1974179 = 2961269) B2961269
theorem B7503779 : Blo 1315976 7503779 := bstep (se 1 (by rfl) ⟨5627834, by rfl⟩ : syracuseStep 7503779 = 11255669) B11255669
theorem B1974209 : Blo 1315976 1974209 := bstep (se 2 (by rfl) ⟨740328, by rfl⟩ : syracuseStep 1974209 = 1480657) B1480657
theorem B1482691 : Blo 1315976 1482691 := bstep (se 1 (by rfl) ⟨1112018, by rfl⟩ : syracuseStep 1482691 = 2224037) B2224037
theorem B32456645 : Blo 1315976 32456645 := bstep (se 4 (by rfl) ⟨3042810, by rfl⟩ : syracuseStep 32456645 = 6085621) B6085621
theorem B1974227 : Blo 1315976 1974227 := bstep (se 1 (by rfl) ⟨1480670, by rfl⟩ : syracuseStep 1974227 = 2961341) B2961341
theorem B1974257 : Blo 1315976 1974257 := bstep (se 2 (by rfl) ⟨740346, by rfl⟩ : syracuseStep 1974257 = 1480693) B1480693
theorem B21659683 : Blo 1315976 21659683 := bstep (se 1 (by rfl) ⟨16244762, by rfl⟩ : syracuseStep 21659683 = 32489525) B32489525
theorem B4005953 : Blo 1315976 4005953 := bstep (se 2 (by rfl) ⟨1502232, by rfl⟩ : syracuseStep 4005953 = 3004465) B3004465
theorem B1974347 : Blo 1315976 1974347 := bstep (se 1 (by rfl) ⟨1480760, by rfl⟩ : syracuseStep 1974347 = 2961521) B2961521
theorem B1974359 : Blo 1315976 1974359 := bstep (se 1 (by rfl) ⟨1480769, by rfl⟩ : syracuseStep 1974359 = 2961539) B2961539
theorem B1974425 : Blo 1315976 1974425 := bstep (se 2 (by rfl) ⟨740409, by rfl⟩ : syracuseStep 1974425 = 1480819) B1480819
theorem B3752153 : Blo 1315976 3752153 := bstep (se 2 (by rfl) ⟨1407057, by rfl⟩ : syracuseStep 3752153 = 2814115) B2814115
theorem B1974539 : Blo 1315976 1974539 := bstep (se 1 (by rfl) ⟨1480904, by rfl⟩ : syracuseStep 1974539 = 2961809) B2961809
theorem B1974551 : Blo 1315976 1974551 := bstep (se 1 (by rfl) ⟨1480913, by rfl⟩ : syracuseStep 1974551 = 2961827) B2961827
theorem B1974617 : Blo 1315976 1974617 := bstep (se 2 (by rfl) ⟨740481, by rfl⟩ : syracuseStep 1974617 = 1480963) B1480963
theorem B9994589 : Blo 1315976 9994589 := bstep (se 3 (by rfl) ⟨1873985, by rfl⟩ : syracuseStep 9994589 = 3747971) B3747971
theorem B1974731 : Blo 1315976 1974731 := bstep (se 1 (by rfl) ⟨1481048, by rfl⟩ : syracuseStep 1974731 = 2962097) B2962097
theorem B1974743 : Blo 1315976 1974743 := bstep (se 1 (by rfl) ⟨1481057, by rfl⟩ : syracuseStep 1974743 = 2962115) B2962115
theorem B1876441 : Blo 1315976 1876441 := bstep (se 2 (by rfl) ⟨703665, by rfl⟩ : syracuseStep 1876441 = 1407331) B1407331
theorem B3334679 : Blo 1315976 3334679 := bstep (se 1 (by rfl) ⟨2501009, by rfl⟩ : syracuseStep 3334679 = 5002019) B5002019
theorem B1974809 : Blo 1315976 1974809 := bstep (se 2 (by rfl) ⟨740553, by rfl⟩ : syracuseStep 1974809 = 1481107) B1481107
theorem B15213149 : Blo 1315976 15213149 := bstep (se 3 (by rfl) ⟨2852465, by rfl⟩ : syracuseStep 15213149 = 5704931) B5704931
theorem B2499187 : Blo 1315976 2499187 := bstep (se 1 (by rfl) ⟨1874390, by rfl⟩ : syracuseStep 2499187 = 3748781) B3748781
theorem B1974923 : Blo 1315976 1974923 := bstep (se 1 (by rfl) ⟨1481192, by rfl⟩ : syracuseStep 1974923 = 2962385) B2962385
theorem B1974935 : Blo 1315976 1974935 := bstep (se 1 (by rfl) ⟨1481201, by rfl⟩ : syracuseStep 1974935 = 2962403) B2962403
theorem B4219543 : Blo 1315976 4219543 := bstep (se 1 (by rfl) ⟨3164657, by rfl⟩ : syracuseStep 4219543 = 6329315) B6329315
theorem B1975001 : Blo 1315976 1975001 := bstep (se 2 (by rfl) ⟨740625, by rfl⟩ : syracuseStep 1975001 = 1481251) B1481251
theorem B4997933 : Blo 1315976 4997933 := bstep (se 3 (by rfl) ⟨937112, by rfl⟩ : syracuseStep 4997933 = 1874225) B1874225
theorem B4997963 : Blo 1315976 4997963 := bstep (se 1 (by rfl) ⟨3748472, by rfl⟩ : syracuseStep 4997963 = 7496945) B7496945
theorem B1975115 : Blo 1315976 1975115 := bstep (se 1 (by rfl) ⟨1481336, by rfl⟩ : syracuseStep 1975115 = 2962673) B2962673
theorem B1975127 : Blo 1315976 1975127 := bstep (se 1 (by rfl) ⟨1481345, by rfl⟩ : syracuseStep 1975127 = 2962691) B2962691
theorem B1975193 : Blo 1315976 1975193 := bstep (se 2 (by rfl) ⟨740697, by rfl⟩ : syracuseStep 1975193 = 1481395) B1481395
theorem B2221067 : Blo 1315976 2221067 := bstep (se 1 (by rfl) ⟨1665800, by rfl⟩ : syracuseStep 2221067 = 3331601) B3331601
theorem B1975307 : Blo 1315976 1975307 := bstep (se 1 (by rfl) ⟨1481480, by rfl⟩ : syracuseStep 1975307 = 2962961) B2962961
theorem B1975319 : Blo 1315976 1975319 := bstep (se 1 (by rfl) ⟨1481489, by rfl⟩ : syracuseStep 1975319 = 2962979) B2962979
theorem B3752983 : Blo 1315976 3752983 := bstep (se 1 (by rfl) ⟨2814737, by rfl⟩ : syracuseStep 3752983 = 5629475) B5629475
theorem B2499635 : Blo 1315976 2499635 := bstep (se 1 (by rfl) ⟨1874726, by rfl⟩ : syracuseStep 2499635 = 3749453) B3749453
theorem B2810945 : Blo 1315976 2810945 := bstep (se 2 (by rfl) ⟨1054104, by rfl⟩ : syracuseStep 2810945 = 2108209) B2108209
theorem B6669377 : Blo 1315976 6669377 := bstep (se 2 (by rfl) ⟨2501016, by rfl⟩ : syracuseStep 6669377 = 5002033) B5002033
theorem B2499673 : Blo 1315976 2499673 := bstep (se 2 (by rfl) ⟨937377, by rfl⟩ : syracuseStep 2499673 = 1874755) B1874755
theorem B1975385 : Blo 1315976 1975385 := bstep (se 2 (by rfl) ⟨740769, by rfl⟩ : syracuseStep 1975385 = 1481539) B1481539
theorem B2221195 : Blo 1315976 2221195 := bstep (se 1 (by rfl) ⟨1665896, by rfl⟩ : syracuseStep 2221195 = 3331793) B3331793
theorem B2671795 : Blo 1315976 2671795 := bstep (se 1 (by rfl) ⟨2003846, by rfl⟩ : syracuseStep 2671795 = 4007693) B4007693
theorem B1975499 : Blo 1315976 1975499 := bstep (se 1 (by rfl) ⟨1481624, by rfl⟩ : syracuseStep 1975499 = 2963249) B2963249
theorem B1975511 : Blo 1315976 1975511 := bstep (se 1 (by rfl) ⟨1481633, by rfl⟩ : syracuseStep 1975511 = 2963267) B2963267
theorem B2221337 : Blo 1315976 2221337 := bstep (se 2 (by rfl) ⟨833001, by rfl⟩ : syracuseStep 2221337 = 1666003) B1666003
theorem B1975577 : Blo 1315976 1975577 := bstep (se 2 (by rfl) ⟨740841, by rfl⟩ : syracuseStep 1975577 = 1481683) B1481683
theorem B3335489 : Blo 1315976 3335489 := bstep (se 2 (by rfl) ⟨1250808, by rfl⟩ : syracuseStep 3335489 = 2501617) B2501617
theorem B17114485 : Blo 1315976 17114485 := bstep (se 5 (by rfl) ⟨802241, by rfl⟩ : syracuseStep 17114485 = 1604483) B1604483
theorem B1975691 : Blo 1315976 1975691 := bstep (se 1 (by rfl) ⟨1481768, by rfl⟩ : syracuseStep 1975691 = 2963537) B2963537
theorem B2811287 : Blo 1315976 2811287 := bstep (se 1 (by rfl) ⟨2108465, by rfl⟩ : syracuseStep 2811287 = 4216931) B4216931
theorem B1975703 : Blo 1315976 1975703 := bstep (se 1 (by rfl) ⟨1481777, by rfl⟩ : syracuseStep 1975703 = 2963555) B2963555
theorem B2221465 : Blo 1315976 2221465 := bstep (se 2 (by rfl) ⟨833049, by rfl⟩ : syracuseStep 2221465 = 1666099) B1666099
theorem B4998617 : Blo 1315976 4998617 := bstep (se 2 (by rfl) ⟨1874481, by rfl⟩ : syracuseStep 4998617 = 3748963) B3748963
theorem B1975769 : Blo 1315976 1975769 := bstep (se 2 (by rfl) ⟨740913, by rfl⟩ : syracuseStep 1975769 = 1481827) B1481827
theorem B2500121 : Blo 1315976 2500121 := bstep (se 2 (by rfl) ⟨937545, by rfl⟩ : syracuseStep 2500121 = 1875091) B1875091
theorem B11257379 : Blo 1315976 11257379 := bstep (se 1 (by rfl) ⟨8443034, by rfl⟩ : syracuseStep 11257379 = 16886069) B16886069
theorem B2811457 : Blo 1315976 2811457 := bstep (se 2 (by rfl) ⟨1054296, by rfl⟩ : syracuseStep 2811457 = 2108593) B2108593
theorem B1975883 : Blo 1315976 1975883 := bstep (se 1 (by rfl) ⟨1481912, by rfl⟩ : syracuseStep 1975883 = 2963825) B2963825
theorem B1975895 : Blo 1315976 1975895 := bstep (se 1 (by rfl) ⟨1481921, by rfl⟩ : syracuseStep 1975895 = 2963843) B2963843
theorem B1975961 : Blo 1315976 1975961 := bstep (se 2 (by rfl) ⟨740985, by rfl⟩ : syracuseStep 1975961 = 1481971) B1481971
theorem B1689355 : Blo 1315976 1689355 := bstep (se 1 (by rfl) ⟨1267016, by rfl⟩ : syracuseStep 1689355 = 2534033) B2534033
theorem B1976075 : Blo 1315976 1976075 := bstep (se 1 (by rfl) ⟨1482056, by rfl⟩ : syracuseStep 1976075 = 2964113) B2964113
theorem B4998935 : Blo 1315976 4998935 := bstep (se 1 (by rfl) ⟨3749201, by rfl⟩ : syracuseStep 4998935 = 7498403) B7498403
theorem B1976087 : Blo 1315976 1976087 := bstep (se 1 (by rfl) ⟨1482065, by rfl⟩ : syracuseStep 1976087 = 2964131) B2964131
theorem B12658477 : Blo 1315976 12658477 := bstep (se 3 (by rfl) ⟨2373464, by rfl⟩ : syracuseStep 12658477 = 4746929) B4746929
theorem B4220723 : Blo 1315976 4220723 := bstep (se 1 (by rfl) ⟨3165542, by rfl⟩ : syracuseStep 4220723 = 6331085) B6331085
theorem B4441931 : Blo 1315976 4441931 := bstep (se 1 (by rfl) ⟨3331448, by rfl⟩ : syracuseStep 4441931 = 6662897) B6662897
theorem B1976153 : Blo 1315976 1976153 := bstep (se 2 (by rfl) ⟨741057, by rfl⟩ : syracuseStep 1976153 = 1482115) B1482115
theorem B3336025 : Blo 1315976 3336025 := bstep (se 2 (by rfl) ⟨1251009, by rfl⟩ : syracuseStep 3336025 = 2502019) B2502019
theorem B3557213 : Blo 1315976 3557213 := bstep (se 3 (by rfl) ⟨666977, by rfl⟩ : syracuseStep 3557213 = 1333955) B1333955
theorem B1976267 : Blo 1315976 1976267 := bstep (se 1 (by rfl) ⟨1482200, by rfl⟩ : syracuseStep 1976267 = 2964401) B2964401
theorem B2222039 : Blo 1315976 2222039 := bstep (se 1 (by rfl) ⟨1666529, by rfl⟩ : syracuseStep 2222039 = 3333059) B3333059
theorem B1976279 : Blo 1315976 1976279 := bstep (se 1 (by rfl) ⟨1482209, by rfl⟩ : syracuseStep 1976279 = 2964419) B2964419
theorem B1976345 : Blo 1315976 1976345 := bstep (se 2 (by rfl) ⟨741129, by rfl⟩ : syracuseStep 1976345 = 1482259) B1482259
theorem B2222167 : Blo 1315976 2222167 := bstep (se 1 (by rfl) ⟨1666625, by rfl⟩ : syracuseStep 2222167 = 3333251) B3333251
theorem B4442201 : Blo 1315976 4442201 := bstep (se 2 (by rfl) ⟨1665825, by rfl⟩ : syracuseStep 4442201 = 3331651) B3331651
theorem B1976459 : Blo 1315976 1976459 := bstep (se 1 (by rfl) ⟨1482344, by rfl⟩ : syracuseStep 1976459 = 2964689) B2964689
theorem B1976471 : Blo 1315976 1976471 := bstep (se 1 (by rfl) ⟨1482353, by rfl⟩ : syracuseStep 1976471 = 2964707) B2964707
theorem B1976537 : Blo 1315976 1976537 := bstep (se 2 (by rfl) ⟨741201, by rfl⟩ : syracuseStep 1976537 = 1482403) B1482403
theorem B2500865 : Blo 1315976 2500865 := bstep (se 2 (by rfl) ⟨937824, by rfl⟩ : syracuseStep 2500865 = 1875649) B1875649
theorem B11258129 : Blo 1315976 11258129 := bstep (se 2 (by rfl) ⟨4221798, by rfl⟩ : syracuseStep 11258129 = 8443597) B8443597
theorem B2533655 : Blo 1315976 2533655 := bstep (se 1 (by rfl) ⟨1900241, by rfl⟩ : syracuseStep 2533655 = 3800483) B3800483
theorem B6850861 : Blo 1315976 6850861 := bstep (se 3 (by rfl) ⟨1284536, by rfl⟩ : syracuseStep 6850861 = 2569073) B2569073
theorem B1976651 : Blo 1315976 1976651 := bstep (se 1 (by rfl) ⟨1482488, by rfl⟩ : syracuseStep 1976651 = 2964977) B2964977
theorem B1976663 : Blo 1315976 1976663 := bstep (se 1 (by rfl) ⟨1482497, by rfl⟩ : syracuseStep 1976663 = 2964995) B2964995
theorem B4745603 : Blo 1315976 4745603 := bstep (se 1 (by rfl) ⟨3559202, by rfl⟩ : syracuseStep 4745603 = 7118405) B7118405
theorem B1976729 : Blo 1315976 1976729 := bstep (se 2 (by rfl) ⟨741273, by rfl⟩ : syracuseStep 1976729 = 1482547) B1482547
theorem B4999603 : Blo 1315976 4999603 := bstep (se 1 (by rfl) ⟨3749702, by rfl⟩ : syracuseStep 4999603 = 7499405) B7499405
theorem B2501131 : Blo 1315976 2501131 := bstep (se 1 (by rfl) ⟨1875848, by rfl⟩ : syracuseStep 2501131 = 3751697) B3751697
theorem B1976843 : Blo 1315976 1976843 := bstep (se 1 (by rfl) ⟨1482632, by rfl⟩ : syracuseStep 1976843 = 2965265) B2965265
theorem B1976855 : Blo 1315976 1976855 := bstep (se 1 (by rfl) ⟨1482641, by rfl⟩ : syracuseStep 1976855 = 2965283) B2965283
theorem B2107991 : Blo 1315976 2107991 := bstep (se 1 (by rfl) ⟨1580993, by rfl⟩ : syracuseStep 2107991 = 3161987) B3161987
theorem B1665623 : Blo 1315976 1665623 := bstep (se 1 (by rfl) ⟨1249217, by rfl⟩ : syracuseStep 1665623 = 2498435) B2498435
theorem B1976921 : Blo 1315976 1976921 := bstep (se 2 (by rfl) ⟨741345, by rfl⟩ : syracuseStep 1976921 = 1482691) B1482691
theorem B21637763 : Blo 1315976 21637763 := bstep (se 1 (by rfl) ⟨16228322, by rfl⟩ : syracuseStep 21637763 = 32456645) B32456645
theorem B14994071 : Blo 1315976 14994071 := bstep (se 1 (by rfl) ⟨11245553, by rfl⟩ : syracuseStep 14994071 = 22491107) B22491107
theorem B1501867 : Blo 1315976 1501867 := bstep (se 1 (by rfl) ⟨1126400, by rfl⟩ : syracuseStep 1501867 = 2252801) B2252801
theorem B2812619 : Blo 1315976 2812619 := bstep (se 1 (by rfl) ⟨2109464, by rfl⟩ : syracuseStep 2812619 = 4218929) B4218929
theorem B2222795 : Blo 1315976 2222795 := bstep (se 1 (by rfl) ⟨1667096, by rfl⟩ : syracuseStep 2222795 = 3334193) B3334193
theorem B43305677 : Blo 1315976 43305677 := bstep (se 3 (by rfl) ⟨8119814, by rfl⟩ : syracuseStep 43305677 = 16239629) B16239629
theorem B4442903 : Blo 1315976 4442903 := bstep (se 1 (by rfl) ⟨3332177, by rfl⟩ : syracuseStep 4442903 = 6664355) B6664355
theorem B2222923 : Blo 1315976 2222923 := bstep (se 1 (by rfl) ⟨1667192, by rfl⟩ : syracuseStep 2222923 = 3334385) B3334385
theorem B2501579 : Blo 1315976 2501579 := bstep (se 1 (by rfl) ⟨1876184, by rfl⟩ : syracuseStep 2501579 = 3752369) B3752369
theorem B9497549 : Blo 1315976 9497549 := bstep (se 3 (by rfl) ⟨1780790, by rfl⟩ : syracuseStep 9497549 = 3561581) B3561581
theorem B2223065 : Blo 1315976 2223065 := bstep (se 2 (by rfl) ⟨833649, by rfl⟩ : syracuseStep 2223065 = 1667299) B1667299
theorem B6671321 : Blo 1315976 6671321 := bstep (se 2 (by rfl) ⟨2501745, by rfl⟩ : syracuseStep 6671321 = 5003491) B5003491
theorem B2223193 : Blo 1315976 2223193 := bstep (se 2 (by rfl) ⟨833697, by rfl⟩ : syracuseStep 2223193 = 1667395) B1667395
theorem B2501761 : Blo 1315976 2501761 := bstep (se 2 (by rfl) ⟨938160, by rfl⟩ : syracuseStep 2501761 = 1876321) B1876321
theorem B24022277 : Blo 1315976 24022277 := bstep (se 4 (by rfl) ⟨2252088, by rfl⟩ : syracuseStep 24022277 = 4504177) B4504177
theorem B1666327 : Blo 1315976 1666327 := bstep (se 1 (by rfl) ⟨1249745, by rfl⟩ : syracuseStep 1666327 = 2499491) B2499491
theorem B4443443 : Blo 1315976 4443443 := bstep (se 1 (by rfl) ⟨3332582, by rfl⟩ : syracuseStep 4443443 = 6665165) B6665165
theorem B2813363 : Blo 1315976 2813363 := bstep (se 1 (by rfl) ⟨2110022, by rfl⟩ : syracuseStep 2813363 = 4220045) B4220045
theorem B4443713 : Blo 1315976 4443713 := bstep (se 2 (by rfl) ⟨1666392, by rfl⟩ : syracuseStep 4443713 = 3332785) B3332785
theorem B9137765 : Blo 1315976 9137765 := bstep (se 4 (by rfl) ⟨856665, by rfl⟩ : syracuseStep 9137765 = 1713331) B1713331
theorem B2961035 : Blo 1315976 2961035 := bstep (se 1 (by rfl) ⟨2220776, by rfl⟩ : syracuseStep 2961035 = 4441553) B4441553
theorem B5000849 : Blo 1315976 5000849 := bstep (se 2 (by rfl) ⟨1875318, by rfl⟩ : syracuseStep 5000849 = 3750637) B3750637
theorem B2223767 : Blo 1315976 2223767 := bstep (se 1 (by rfl) ⟨1667825, by rfl⟩ : syracuseStep 2223767 = 3335651) B3335651
theorem B2961089 : Blo 1315976 2961089 := bstep (se 2 (by rfl) ⟨1110408, by rfl⟩ : syracuseStep 2961089 = 2220817) B2220817
theorem B2223895 : Blo 1315976 2223895 := bstep (se 1 (by rfl) ⟨1667921, by rfl⟩ : syracuseStep 2223895 = 3335843) B3335843
theorem B5623597 : Blo 1315976 5623597 := bstep (se 3 (by rfl) ⟨1054424, by rfl⟩ : syracuseStep 5623597 = 2108849) B2108849
theorem B2109259 : Blo 1315976 2109259 := bstep (se 1 (by rfl) ⟨1581944, by rfl⟩ : syracuseStep 2109259 = 3163889) B3163889
theorem B14241653 : Blo 1315976 14241653 := bstep (se 5 (by rfl) ⟨667577, by rfl⟩ : syracuseStep 14241653 = 1335155) B1335155
theorem B2961305 : Blo 1315976 2961305 := bstep (se 2 (by rfl) ⟨1110489, by rfl⟩ : syracuseStep 2961305 = 2220979) B2220979
theorem B5623769 : Blo 1315976 5623769 := bstep (se 2 (by rfl) ⟨2108913, by rfl⟩ : syracuseStep 5623769 = 4217827) B4217827
theorem B2961395 : Blo 1315976 2961395 := bstep (se 1 (by rfl) ⟨2221046, by rfl⟩ : syracuseStep 2961395 = 4442093) B4442093
theorem B2961431 : Blo 1315976 2961431 := bstep (se 1 (by rfl) ⟨2221073, by rfl⟩ : syracuseStep 2961431 = 4442147) B4442147
theorem B3379223 : Blo 1315976 3379223 := bstep (se 1 (by rfl) ⟨2534417, by rfl⟩ : syracuseStep 3379223 = 5068835) B5068835
theorem B7114817 : Blo 1315976 7114817 := bstep (se 2 (by rfl) ⟨2668056, by rfl⟩ : syracuseStep 7114817 = 5336113) B5336113
theorem B4444253 : Blo 1315976 4444253 := bstep (se 3 (by rfl) ⟨833297, by rfl⟩ : syracuseStep 4444253 = 1666595) B1666595
theorem B8441957 : Blo 1315976 8441957 := bstep (se 4 (by rfl) ⟨791433, by rfl⟩ : syracuseStep 8441957 = 1582867) B1582867
theorem B2371699 : Blo 1315976 2371699 := bstep (se 1 (by rfl) ⟨1778774, by rfl⟩ : syracuseStep 2371699 = 3557549) B3557549
theorem B2961611 : Blo 1315976 2961611 := bstep (se 1 (by rfl) ⟨2221208, by rfl⟩ : syracuseStep 2961611 = 4442417) B4442417
theorem B2961665 : Blo 1315976 2961665 := bstep (se 2 (by rfl) ⟨1110624, by rfl⟩ : syracuseStep 2961665 = 2221249) B2221249
theorem B2109721 : Blo 1315976 2109721 := bstep (se 2 (by rfl) ⟨791145, by rfl⟩ : syracuseStep 2109721 = 1582291) B1582291
theorem B2814259 : Blo 1315976 2814259 := bstep (se 1 (by rfl) ⟨2110694, by rfl⟩ : syracuseStep 2814259 = 4221389) B4221389
theorem B5001547 : Blo 1315976 5001547 := bstep (se 1 (by rfl) ⟨3751160, by rfl⟩ : syracuseStep 5001547 = 7502321) B7502321
theorem B2470297 : Blo 1315976 2470297 := bstep (se 2 (by rfl) ⟨926361, by rfl⟩ : syracuseStep 2470297 = 1852723) B1852723
theorem B1405387 : Blo 1315976 1405387 := bstep (se 1 (by rfl) ⟨1054040, by rfl⟩ : syracuseStep 1405387 = 2108081) B2108081
theorem B2961881 : Blo 1315976 2961881 := bstep (se 2 (by rfl) ⟨1110705, by rfl⟩ : syracuseStep 2961881 = 2221411) B2221411
theorem B2109977 : Blo 1315976 2109977 := bstep (se 2 (by rfl) ⟨791241, by rfl⟩ : syracuseStep 2109977 = 1582483) B1582483
theorem B2961971 : Blo 1315976 2961971 := bstep (se 1 (by rfl) ⟨2221478, by rfl⟩ : syracuseStep 2961971 = 4442957) B4442957
theorem B2372161 : Blo 1315976 2372161 := bstep (se 2 (by rfl) ⟨889560, by rfl⟩ : syracuseStep 2372161 = 1779121) B1779121
theorem B3748427 : Blo 1315976 3748427 := bstep (se 1 (by rfl) ⟨2811320, by rfl⟩ : syracuseStep 3748427 = 5622641) B5622641
theorem B7221835 : Blo 1315976 7221835 := bstep (se 1 (by rfl) ⟨5416376, by rfl⟩ : syracuseStep 7221835 = 10832753) B10832753
theorem B2962007 : Blo 1315976 2962007 := bstep (se 1 (by rfl) ⟨2221505, by rfl⟩ : syracuseStep 2962007 = 4443011) B4443011
theorem B10678877 : Blo 1315976 10678877 := bstep (se 3 (by rfl) ⟨2002289, by rfl⟩ : syracuseStep 10678877 = 4004579) B4004579
theorem B5001821 : Blo 1315976 5001821 := bstep (se 3 (by rfl) ⟨937841, by rfl⟩ : syracuseStep 5001821 = 1875683) B1875683
theorem B2003609 : Blo 1315976 2003609 := bstep (se 2 (by rfl) ⟨751353, by rfl⟩ : syracuseStep 2003609 = 1502707) B1502707
theorem B7598771 : Blo 1315976 7598771 := bstep (se 1 (by rfl) ⟨5699078, by rfl⟩ : syracuseStep 7598771 = 11398157) B11398157
theorem B5411549 : Blo 1315976 5411549 := bstep (se 3 (by rfl) ⟨1014665, by rfl⟩ : syracuseStep 5411549 = 2029331) B2029331
theorem B2962187 : Blo 1315976 2962187 := bstep (se 1 (by rfl) ⟨2221640, by rfl⟩ : syracuseStep 2962187 = 4443281) B4443281
theorem B2962241 : Blo 1315976 2962241 := bstep (se 2 (by rfl) ⟨1110840, by rfl⟩ : syracuseStep 2962241 = 2221681) B2221681
theorem B4813741 : Blo 1315976 4813741 := bstep (se 3 (by rfl) ⟨902576, by rfl⟩ : syracuseStep 4813741 = 1805153) B1805153
theorem B12006323 : Blo 1315976 12006323 := bstep (se 1 (by rfl) ⟨9004742, by rfl⟩ : syracuseStep 12006323 = 18009485) B18009485
theorem B1668043 : Blo 1315976 1668043 := bstep (se 1 (by rfl) ⟨1251032, by rfl⟩ : syracuseStep 1668043 = 2502065) B2502065
theorem B2962457 : Blo 1315976 2962457 := bstep (se 2 (by rfl) ⟨1110921, by rfl⟩ : syracuseStep 2962457 = 2221843) B2221843
theorem B2962547 : Blo 1315976 2962547 := bstep (se 1 (by rfl) ⟨2221910, by rfl⟩ : syracuseStep 2962547 = 4443821) B4443821
theorem B1315979 : Blo 1315976 1315979 := bstep (se 1 (by rfl) ⟨986984, by rfl⟩ : syracuseStep 1315979 = 1973969) B1973969
theorem B1315991 : Blo 1315976 1315991 := bstep (se 1 (by rfl) ⟨986993, by rfl⟩ : syracuseStep 1315991 = 1973987) B1973987
theorem B2962583 : Blo 1315976 2962583 := bstep (se 1 (by rfl) ⟨2221937, by rfl⟩ : syracuseStep 2962583 = 4443875) B4443875
theorem B1316011 : Blo 1315976 1316011 := bstep (se 1 (by rfl) ⟨987008, by rfl⟩ : syracuseStep 1316011 = 1974017) B1974017
theorem B11400371 : Blo 1315976 11400371 := bstep (se 1 (by rfl) ⟨8550278, by rfl⟩ : syracuseStep 11400371 = 17100557) B17100557
theorem B1316023 : Blo 1315976 1316023 := bstep (se 1 (by rfl) ⟨987017, by rfl⟩ : syracuseStep 1316023 = 1974035) B1974035
theorem B1316043 : Blo 1315976 1316043 := bstep (se 1 (by rfl) ⟨987032, by rfl⟩ : syracuseStep 1316043 = 1974065) B1974065
theorem B4445387 : Blo 1315976 4445387 := bstep (se 1 (by rfl) ⟨3334040, by rfl⟩ : syracuseStep 4445387 = 6668081) B6668081
theorem B1316055 : Blo 1315976 1316055 := bstep (se 1 (by rfl) ⟨987041, by rfl⟩ : syracuseStep 1316055 = 1974083) B1974083
theorem B1316075 : Blo 1315976 1316075 := bstep (se 1 (by rfl) ⟨987056, by rfl⟩ : syracuseStep 1316075 = 1974113) B1974113
theorem B1316087 : Blo 1315976 1316087 := bstep (se 1 (by rfl) ⟨987065, by rfl⟩ : syracuseStep 1316087 = 1974131) B1974131
theorem B1316107 : Blo 1315976 1316107 := bstep (se 1 (by rfl) ⟨987080, by rfl⟩ : syracuseStep 1316107 = 1974161) B1974161
theorem B6665489 : Blo 1315976 6665489 := bstep (se 2 (by rfl) ⟨2499558, by rfl⟩ : syracuseStep 6665489 = 4999117) B4999117
theorem B1316119 : Blo 1315976 1316119 := bstep (se 1 (by rfl) ⟨987089, by rfl⟩ : syracuseStep 1316119 = 1974179) B1974179
theorem B5002519 : Blo 1315976 5002519 := bstep (se 1 (by rfl) ⟨3751889, by rfl⟩ : syracuseStep 5002519 = 7503779) B7503779
theorem B1316139 : Blo 1315976 1316139 := bstep (se 1 (by rfl) ⟨987104, by rfl⟩ : syracuseStep 1316139 = 1974209) B1974209
theorem B1316151 : Blo 1315976 1316151 := bstep (se 1 (by rfl) ⟨987113, by rfl⟩ : syracuseStep 1316151 = 1974227) B1974227
theorem B1316171 : Blo 1315976 1316171 := bstep (se 1 (by rfl) ⟨987128, by rfl⟩ : syracuseStep 1316171 = 1974257) B1974257
theorem B2962763 : Blo 1315976 2962763 := bstep (se 1 (by rfl) ⟨2222072, by rfl⟩ : syracuseStep 2962763 = 4444145) B4444145
theorem B1316183 : Blo 1315976 1316183 := bstep (se 1 (by rfl) ⟨987137, by rfl⟩ : syracuseStep 1316183 = 1974275) B1974275
theorem B1316203 : Blo 1315976 1316203 := bstep (se 1 (by rfl) ⟨987152, by rfl⟩ : syracuseStep 1316203 = 1974305) B1974305
theorem B1316215 : Blo 1315976 1316215 := bstep (se 1 (by rfl) ⟨987161, by rfl⟩ : syracuseStep 1316215 = 1974323) B1974323
theorem B2962817 : Blo 1315976 2962817 := bstep (se 2 (by rfl) ⟨1111056, by rfl⟩ : syracuseStep 2962817 = 2222113) B2222113
theorem B1316235 : Blo 1315976 1316235 := bstep (se 1 (by rfl) ⟨987176, by rfl⟩ : syracuseStep 1316235 = 1974353) B1974353
theorem B1316247 : Blo 1315976 1316247 := bstep (se 1 (by rfl) ⟨987185, by rfl⟩ : syracuseStep 1316247 = 1974371) B1974371
theorem B1316267 : Blo 1315976 1316267 := bstep (se 1 (by rfl) ⟨987200, by rfl⟩ : syracuseStep 1316267 = 1974401) B1974401
theorem B6665651 : Blo 1315976 6665651 := bstep (se 1 (by rfl) ⟨4999238, by rfl⟩ : syracuseStep 6665651 = 9998477) B9998477
theorem B1316279 : Blo 1315976 1316279 := bstep (se 1 (by rfl) ⟨987209, by rfl⟩ : syracuseStep 1316279 = 1974419) B1974419
theorem B160339397 : Blo 1315976 160339397 := bstep (se 4 (by rfl) ⟨15031818, by rfl⟩ : syracuseStep 160339397 = 30063637) B30063637
theorem B1316299 : Blo 1315976 1316299 := bstep (se 1 (by rfl) ⟨987224, by rfl⟩ : syracuseStep 1316299 = 1974449) B1974449
theorem B1316311 : Blo 1315976 1316311 := bstep (se 1 (by rfl) ⟨987233, by rfl⟩ : syracuseStep 1316311 = 1974467) B1974467
theorem B4445657 : Blo 1315976 4445657 := bstep (se 2 (by rfl) ⟨1667121, by rfl⟩ : syracuseStep 4445657 = 3334243) B3334243
theorem B1316331 : Blo 1315976 1316331 := bstep (se 1 (by rfl) ⟨987248, by rfl⟩ : syracuseStep 1316331 = 1974497) B1974497
theorem B1316343 : Blo 1315976 1316343 := bstep (se 1 (by rfl) ⟨987257, by rfl⟩ : syracuseStep 1316343 = 1974515) B1974515
theorem B1316363 : Blo 1315976 1316363 := bstep (se 1 (by rfl) ⟨987272, by rfl⟩ : syracuseStep 1316363 = 1974545) B1974545
theorem B1316375 : Blo 1315976 1316375 := bstep (se 1 (by rfl) ⟨987281, by rfl⟩ : syracuseStep 1316375 = 1974563) B1974563
theorem B1316395 : Blo 1315976 1316395 := bstep (se 1 (by rfl) ⟨987296, by rfl⟩ : syracuseStep 1316395 = 1974593) B1974593
theorem B1316407 : Blo 1315976 1316407 := bstep (se 1 (by rfl) ⟨987305, by rfl⟩ : syracuseStep 1316407 = 1974611) B1974611
theorem B5625409 : Blo 1315976 5625409 := bstep (se 2 (by rfl) ⟨2109528, by rfl⟩ : syracuseStep 5625409 = 4219057) B4219057
theorem B1316427 : Blo 1315976 1316427 := bstep (se 1 (by rfl) ⟨987320, by rfl⟩ : syracuseStep 1316427 = 1974641) B1974641
theorem B1316439 : Blo 1315976 1316439 := bstep (se 1 (by rfl) ⟨987329, by rfl⟩ : syracuseStep 1316439 = 1974659) B1974659
theorem B2963033 : Blo 1315976 2963033 := bstep (se 2 (by rfl) ⟨1111137, by rfl⟩ : syracuseStep 2963033 = 2222275) B2222275
theorem B1316459 : Blo 1315976 1316459 := bstep (se 1 (by rfl) ⟨987344, by rfl⟩ : syracuseStep 1316459 = 1974689) B1974689
theorem B1316471 : Blo 1315976 1316471 := bstep (se 1 (by rfl) ⟨987353, by rfl⟩ : syracuseStep 1316471 = 1974707) B1974707
theorem B1316491 : Blo 1315976 1316491 := bstep (se 1 (by rfl) ⟨987368, by rfl⟩ : syracuseStep 1316491 = 1974737) B1974737
theorem B1316503 : Blo 1315976 1316503 := bstep (se 1 (by rfl) ⟨987377, by rfl⟩ : syracuseStep 1316503 = 1974755) B1974755
theorem B1316523 : Blo 1315976 1316523 := bstep (se 1 (by rfl) ⟨987392, by rfl⟩ : syracuseStep 1316523 = 1974785) B1974785
theorem B3331763 : Blo 1315976 3331763 := bstep (se 1 (by rfl) ⟨2498822, by rfl⟩ : syracuseStep 3331763 = 4997645) B4997645
theorem B2963123 : Blo 1315976 2963123 := bstep (se 1 (by rfl) ⟨2222342, by rfl⟩ : syracuseStep 2963123 = 4444685) B4444685
theorem B1316535 : Blo 1315976 1316535 := bstep (se 1 (by rfl) ⟨987401, by rfl⟩ : syracuseStep 1316535 = 1974803) B1974803
theorem B1316555 : Blo 1315976 1316555 := bstep (se 1 (by rfl) ⟨987416, by rfl⟩ : syracuseStep 1316555 = 1974833) B1974833
theorem B1316567 : Blo 1315976 1316567 := bstep (se 1 (by rfl) ⟨987425, by rfl⟩ : syracuseStep 1316567 = 1974851) B1974851
theorem B2963159 : Blo 1315976 2963159 := bstep (se 1 (by rfl) ⟨2222369, by rfl⟩ : syracuseStep 2963159 = 4444739) B4444739
theorem B1316587 : Blo 1315976 1316587 := bstep (se 1 (by rfl) ⟨987440, by rfl⟩ : syracuseStep 1316587 = 1974881) B1974881
theorem B1316599 : Blo 1315976 1316599 := bstep (se 1 (by rfl) ⟨987449, by rfl⟩ : syracuseStep 1316599 = 1974899) B1974899
theorem B1316619 : Blo 1315976 1316619 := bstep (se 1 (by rfl) ⟨987464, by rfl⟩ : syracuseStep 1316619 = 1974929) B1974929
theorem B1316631 : Blo 1315976 1316631 := bstep (se 1 (by rfl) ⟨987473, by rfl⟩ : syracuseStep 1316631 = 1974947) B1974947
theorem B1316651 : Blo 1315976 1316651 := bstep (se 1 (by rfl) ⟨987488, by rfl⟩ : syracuseStep 1316651 = 1974977) B1974977
theorem B7116589 : Blo 1315976 7116589 := bstep (se 3 (by rfl) ⟨1334360, by rfl⟩ : syracuseStep 7116589 = 2668721) B2668721
theorem B8435501 : Blo 1315976 8435501 := bstep (se 3 (by rfl) ⟨1581656, by rfl⟩ : syracuseStep 8435501 = 3163313) B3163313
theorem B1316663 : Blo 1315976 1316663 := bstep (se 1 (by rfl) ⟨987497, by rfl⟩ : syracuseStep 1316663 = 1974995) B1974995
theorem B1316683 : Blo 1315976 1316683 := bstep (se 1 (by rfl) ⟨987512, by rfl⟩ : syracuseStep 1316683 = 1975025) B1975025
theorem B1316695 : Blo 1315976 1316695 := bstep (se 1 (by rfl) ⟨987521, by rfl⟩ : syracuseStep 1316695 = 1975043) B1975043
theorem B13006693 : Blo 1315976 13006693 := bstep (se 4 (by rfl) ⟨1219377, by rfl⟩ : syracuseStep 13006693 = 2438755) B2438755
theorem B1316715 : Blo 1315976 1316715 := bstep (se 1 (by rfl) ⟨987536, by rfl⟩ : syracuseStep 1316715 = 1975073) B1975073
theorem B1480567 : Blo 1315976 1480567 := bstep (se 1 (by rfl) ⟨1110425, by rfl⟩ : syracuseStep 1480567 = 2220851) B2220851
theorem B1316727 : Blo 1315976 1316727 := bstep (se 1 (by rfl) ⟨987545, by rfl⟩ : syracuseStep 1316727 = 1975091) B1975091
theorem B1316747 : Blo 1315976 1316747 := bstep (se 1 (by rfl) ⟨987560, by rfl⟩ : syracuseStep 1316747 = 1975121) B1975121
theorem B2963339 : Blo 1315976 2963339 := bstep (se 1 (by rfl) ⟨2222504, by rfl⟩ : syracuseStep 2963339 = 4445009) B4445009
theorem B1316759 : Blo 1315976 1316759 := bstep (se 1 (by rfl) ⟨987569, by rfl⟩ : syracuseStep 1316759 = 1975139) B1975139
theorem B1316779 : Blo 1315976 1316779 := bstep (se 1 (by rfl) ⟨987584, by rfl⟩ : syracuseStep 1316779 = 1975169) B1975169
theorem B1316791 : Blo 1315976 1316791 := bstep (se 1 (by rfl) ⟨987593, by rfl⟩ : syracuseStep 1316791 = 1975187) B1975187
theorem B2963393 : Blo 1315976 2963393 := bstep (se 2 (by rfl) ⟨1111272, by rfl⟩ : syracuseStep 2963393 = 2222545) B2222545
theorem B1316811 : Blo 1315976 1316811 := bstep (se 1 (by rfl) ⟨987608, by rfl⟩ : syracuseStep 1316811 = 1975217) B1975217
theorem B1316823 : Blo 1315976 1316823 := bstep (se 1 (by rfl) ⟨987617, by rfl⟩ : syracuseStep 1316823 = 1975235) B1975235
theorem B1316843 : Blo 1315976 1316843 := bstep (se 1 (by rfl) ⟨987632, by rfl⟩ : syracuseStep 1316843 = 1975265) B1975265
theorem B1316855 : Blo 1315976 1316855 := bstep (se 1 (by rfl) ⟨987641, by rfl⟩ : syracuseStep 1316855 = 1975283) B1975283
theorem B1316875 : Blo 1315976 1316875 := bstep (se 1 (by rfl) ⟨987656, by rfl⟩ : syracuseStep 1316875 = 1975313) B1975313
theorem B1316887 : Blo 1315976 1316887 := bstep (se 1 (by rfl) ⟨987665, by rfl⟩ : syracuseStep 1316887 = 1975331) B1975331
theorem B1480747 : Blo 1315976 1480747 := bstep (se 1 (by rfl) ⟨1110560, by rfl⟩ : syracuseStep 1480747 = 2221121) B2221121
theorem B1316907 : Blo 1315976 1316907 := bstep (se 1 (by rfl) ⟨987680, by rfl⟩ : syracuseStep 1316907 = 1975361) B1975361
theorem B5003309 : Blo 1315976 5003309 := bstep (se 3 (by rfl) ⟨938120, by rfl⟩ : syracuseStep 5003309 = 1876241) B1876241
theorem B1316919 : Blo 1315976 1316919 := bstep (se 1 (by rfl) ⟨987689, by rfl⟩ : syracuseStep 1316919 = 1975379) B1975379
theorem B1316939 : Blo 1315976 1316939 := bstep (se 1 (by rfl) ⟨987704, by rfl⟩ : syracuseStep 1316939 = 1975409) B1975409
theorem B1316951 : Blo 1315976 1316951 := bstep (se 1 (by rfl) ⟨987713, by rfl⟩ : syracuseStep 1316951 = 1975427) B1975427
theorem B3799133 : Blo 1315976 3799133 := bstep (se 3 (by rfl) ⟨712337, by rfl⟩ : syracuseStep 3799133 = 1424675) B1424675
theorem B7116893 : Blo 1315976 7116893 := bstep (se 3 (by rfl) ⟨1334417, by rfl⟩ : syracuseStep 7116893 = 2668835) B2668835
theorem B1316971 : Blo 1315976 1316971 := bstep (se 1 (by rfl) ⟨987728, by rfl⟩ : syracuseStep 1316971 = 1975457) B1975457
theorem B1316983 : Blo 1315976 1316983 := bstep (se 1 (by rfl) ⟨987737, by rfl⟩ : syracuseStep 1316983 = 1975475) B1975475
theorem B1317003 : Blo 1315976 1317003 := bstep (se 1 (by rfl) ⟨987752, by rfl⟩ : syracuseStep 1317003 = 1975505) B1975505
theorem B1480855 : Blo 1315976 1480855 := bstep (se 1 (by rfl) ⟨1110641, by rfl⟩ : syracuseStep 1480855 = 2221283) B2221283
theorem B1317015 : Blo 1315976 1317015 := bstep (se 1 (by rfl) ⟨987761, by rfl⟩ : syracuseStep 1317015 = 1975523) B1975523
theorem B2963609 : Blo 1315976 2963609 := bstep (se 2 (by rfl) ⟨1111353, by rfl⟩ : syracuseStep 2963609 = 2222707) B2222707
theorem B4446359 : Blo 1315976 4446359 := bstep (se 1 (by rfl) ⟨3334769, by rfl⟩ : syracuseStep 4446359 = 6669539) B6669539
theorem B1317035 : Blo 1315976 1317035 := bstep (se 1 (by rfl) ⟨987776, by rfl⟩ : syracuseStep 1317035 = 1975553) B1975553
theorem B3750067 : Blo 1315976 3750067 := bstep (se 1 (by rfl) ⟨2812550, by rfl⟩ : syracuseStep 3750067 = 5625101) B5625101
theorem B7502003 : Blo 1315976 7502003 := bstep (se 1 (by rfl) ⟨5626502, by rfl⟩ : syracuseStep 7502003 = 11253005) B11253005
theorem B1317047 : Blo 1315976 1317047 := bstep (se 1 (by rfl) ⟨987785, by rfl⟩ : syracuseStep 1317047 = 1975571) B1975571
theorem B3332299 : Blo 1315976 3332299 := bstep (se 1 (by rfl) ⟨2499224, by rfl⟩ : syracuseStep 3332299 = 4998449) B4998449
theorem B1317067 : Blo 1315976 1317067 := bstep (se 1 (by rfl) ⟨987800, by rfl⟩ : syracuseStep 1317067 = 1975601) B1975601
theorem B1317079 : Blo 1315976 1317079 := bstep (se 1 (by rfl) ⟨987809, by rfl⟩ : syracuseStep 1317079 = 1975619) B1975619
theorem B1317099 : Blo 1315976 1317099 := bstep (se 1 (by rfl) ⟨987824, by rfl⟩ : syracuseStep 1317099 = 1975649) B1975649
theorem B2963699 : Blo 1315976 2963699 := bstep (se 1 (by rfl) ⟨2222774, by rfl⟩ : syracuseStep 2963699 = 4445549) B4445549
theorem B1317111 : Blo 1315976 1317111 := bstep (se 1 (by rfl) ⟨987833, by rfl⟩ : syracuseStep 1317111 = 1975667) B1975667
theorem B1317131 : Blo 1315976 1317131 := bstep (se 1 (by rfl) ⟨987848, by rfl⟩ : syracuseStep 1317131 = 1975697) B1975697
theorem B1317143 : Blo 1315976 1317143 := bstep (se 1 (by rfl) ⟨987857, by rfl⟩ : syracuseStep 1317143 = 1975715) B1975715
theorem B2963735 : Blo 1315976 2963735 := bstep (se 1 (by rfl) ⟨2222801, by rfl⟩ : syracuseStep 2963735 = 4445603) B4445603
theorem B1317163 : Blo 1315976 1317163 := bstep (se 1 (by rfl) ⟨987872, by rfl⟩ : syracuseStep 1317163 = 1975745) B1975745
theorem B1317175 : Blo 1315976 1317175 := bstep (se 1 (by rfl) ⟨987881, by rfl⟩ : syracuseStep 1317175 = 1975763) B1975763
theorem B1481035 : Blo 1315976 1481035 := bstep (se 1 (by rfl) ⟨1110776, by rfl⟩ : syracuseStep 1481035 = 2221553) B2221553
theorem B1317195 : Blo 1315976 1317195 := bstep (se 1 (by rfl) ⟨987896, by rfl⟩ : syracuseStep 1317195 = 1975793) B1975793
theorem B1317207 : Blo 1315976 1317207 := bstep (se 1 (by rfl) ⟨987905, by rfl⟩ : syracuseStep 1317207 = 1975811) B1975811
theorem B3332441 : Blo 1315976 3332441 := bstep (se 2 (by rfl) ⟨1249665, by rfl⟩ : syracuseStep 3332441 = 2499331) B2499331
theorem B1317227 : Blo 1315976 1317227 := bstep (se 1 (by rfl) ⟨987920, by rfl⟩ : syracuseStep 1317227 = 1975841) B1975841
theorem B1317239 : Blo 1315976 1317239 := bstep (se 1 (by rfl) ⟨987929, by rfl⟩ : syracuseStep 1317239 = 1975859) B1975859
theorem B1317259 : Blo 1315976 1317259 := bstep (se 1 (by rfl) ⟨987944, by rfl⟩ : syracuseStep 1317259 = 1975889) B1975889
theorem B3750295 : Blo 1315976 3750295 := bstep (se 1 (by rfl) ⟨2812721, by rfl⟩ : syracuseStep 3750295 = 5625443) B5625443
theorem B1317271 : Blo 1315976 1317271 := bstep (se 1 (by rfl) ⟨987953, by rfl⟩ : syracuseStep 1317271 = 1975907) B1975907
theorem B1317291 : Blo 1315976 1317291 := bstep (se 1 (by rfl) ⟨987968, by rfl⟩ : syracuseStep 1317291 = 1975937) B1975937
theorem B1407403 : Blo 1315976 1407403 := bstep (se 1 (by rfl) ⟨1055552, by rfl⟩ : syracuseStep 1407403 = 2111105) B2111105
theorem B1481143 : Blo 1315976 1481143 := bstep (se 1 (by rfl) ⟨1110857, by rfl⟩ : syracuseStep 1481143 = 2221715) B2221715
theorem B1317303 : Blo 1315976 1317303 := bstep (se 1 (by rfl) ⟨987977, by rfl⟩ : syracuseStep 1317303 = 1975955) B1975955
theorem B2963915 : Blo 1315976 2963915 := bstep (se 1 (by rfl) ⟨2222936, by rfl⟩ : syracuseStep 2963915 = 4445873) B4445873
theorem B1317323 : Blo 1315976 1317323 := bstep (se 1 (by rfl) ⟨987992, by rfl⟩ : syracuseStep 1317323 = 1975985) B1975985
theorem B1317335 : Blo 1315976 1317335 := bstep (se 1 (by rfl) ⟨988001, by rfl⟩ : syracuseStep 1317335 = 1976003) B1976003
theorem B1317355 : Blo 1315976 1317355 := bstep (se 1 (by rfl) ⟨988016, by rfl⟩ : syracuseStep 1317355 = 1976033) B1976033
theorem B1317367 : Blo 1315976 1317367 := bstep (se 1 (by rfl) ⟨988025, by rfl⟩ : syracuseStep 1317367 = 1976051) B1976051
theorem B2963969 : Blo 1315976 2963969 := bstep (se 2 (by rfl) ⟨1111488, by rfl⟩ : syracuseStep 2963969 = 2222977) B2222977
theorem B1317387 : Blo 1315976 1317387 := bstep (se 1 (by rfl) ⟨988040, by rfl⟩ : syracuseStep 1317387 = 1976081) B1976081
theorem B1317399 : Blo 1315976 1317399 := bstep (se 1 (by rfl) ⟨988049, by rfl⟩ : syracuseStep 1317399 = 1976099) B1976099
theorem B1317419 : Blo 1315976 1317419 := bstep (se 1 (by rfl) ⟨988064, by rfl⟩ : syracuseStep 1317419 = 1976129) B1976129
theorem B1317431 : Blo 1315976 1317431 := bstep (se 1 (by rfl) ⟨988073, by rfl⟩ : syracuseStep 1317431 = 1976147) B1976147
theorem B1317451 : Blo 1315976 1317451 := bstep (se 1 (by rfl) ⟨988088, by rfl⟩ : syracuseStep 1317451 = 1976177) B1976177
theorem B1317463 : Blo 1315976 1317463 := bstep (se 1 (by rfl) ⟨988097, by rfl⟩ : syracuseStep 1317463 = 1976195) B1976195
theorem B1481323 : Blo 1315976 1481323 := bstep (se 1 (by rfl) ⟨1110992, by rfl⟩ : syracuseStep 1481323 = 2221985) B2221985
theorem B1317483 : Blo 1315976 1317483 := bstep (se 1 (by rfl) ⟨988112, by rfl⟩ : syracuseStep 1317483 = 1976225) B1976225
theorem B1317495 : Blo 1315976 1317495 := bstep (se 1 (by rfl) ⟨988121, by rfl⟩ : syracuseStep 1317495 = 1976243) B1976243
theorem B1317515 : Blo 1315976 1317515 := bstep (se 1 (by rfl) ⟨988136, by rfl⟩ : syracuseStep 1317515 = 1976273) B1976273
theorem B10140311 : Blo 1315976 10140311 := bstep (se 1 (by rfl) ⟨7605233, by rfl⟩ : syracuseStep 10140311 = 15210467) B15210467
theorem B1317527 : Blo 1315976 1317527 := bstep (se 1 (by rfl) ⟨988145, by rfl⟩ : syracuseStep 1317527 = 1976291) B1976291
theorem B1317547 : Blo 1315976 1317547 := bstep (se 1 (by rfl) ⟨988160, by rfl⟩ : syracuseStep 1317547 = 1976321) B1976321
theorem B4446899 : Blo 1315976 4446899 := bstep (se 1 (by rfl) ⟨3335174, by rfl⟩ : syracuseStep 4446899 = 6670349) B6670349
theorem B1317559 : Blo 1315976 1317559 := bstep (se 1 (by rfl) ⟨988169, by rfl⟩ : syracuseStep 1317559 = 1976339) B1976339
theorem B1317579 : Blo 1315976 1317579 := bstep (se 1 (by rfl) ⟨988184, by rfl⟩ : syracuseStep 1317579 = 1976369) B1976369
theorem B1481431 : Blo 1315976 1481431 := bstep (se 1 (by rfl) ⟨1111073, by rfl⟩ : syracuseStep 1481431 = 2222147) B2222147
theorem B2964185 : Blo 1315976 2964185 := bstep (se 2 (by rfl) ⟨1111569, by rfl⟩ : syracuseStep 2964185 = 2223139) B2223139
theorem B1317591 : Blo 1315976 1317591 := bstep (se 1 (by rfl) ⟨988193, by rfl⟩ : syracuseStep 1317591 = 1976387) B1976387
theorem B1317611 : Blo 1315976 1317611 := bstep (se 1 (by rfl) ⟨988208, by rfl⟩ : syracuseStep 1317611 = 1976417) B1976417
theorem B1317623 : Blo 1315976 1317623 := bstep (se 1 (by rfl) ⟨988217, by rfl⟩ : syracuseStep 1317623 = 1976435) B1976435
theorem B3005185 : Blo 1315976 3005185 := bstep (se 2 (by rfl) ⟨1126944, by rfl⟩ : syracuseStep 3005185 = 2253889) B2253889
theorem B1317643 : Blo 1315976 1317643 := bstep (se 1 (by rfl) ⟨988232, by rfl⟩ : syracuseStep 1317643 = 1976465) B1976465
theorem B1317655 : Blo 1315976 1317655 := bstep (se 1 (by rfl) ⟨988241, by rfl⟩ : syracuseStep 1317655 = 1976483) B1976483
theorem B1317675 : Blo 1315976 1317675 := bstep (se 1 (by rfl) ⟨988256, by rfl⟩ : syracuseStep 1317675 = 1976513) B1976513
theorem B2964275 : Blo 1315976 2964275 := bstep (se 1 (by rfl) ⟨2223206, by rfl⟩ : syracuseStep 2964275 = 4446413) B4446413
theorem B1317687 : Blo 1315976 1317687 := bstep (se 1 (by rfl) ⟨988265, by rfl⟩ : syracuseStep 1317687 = 1976531) B1976531
theorem B57744193 : Blo 1315976 57744193 := bstep (se 2 (by rfl) ⟨21654072, by rfl⟩ : syracuseStep 57744193 = 43308145) B43308145
theorem B1317707 : Blo 1315976 1317707 := bstep (se 1 (by rfl) ⟨988280, by rfl⟩ : syracuseStep 1317707 = 1976561) B1976561
theorem B2964311 : Blo 1315976 2964311 := bstep (se 1 (by rfl) ⟨2223233, by rfl⟩ : syracuseStep 2964311 = 4446467) B4446467
theorem B1317719 : Blo 1315976 1317719 := bstep (se 1 (by rfl) ⟨988289, by rfl⟩ : syracuseStep 1317719 = 1976579) B1976579
theorem B1317739 : Blo 1315976 1317739 := bstep (se 1 (by rfl) ⟨988304, by rfl⟩ : syracuseStep 1317739 = 1976609) B1976609
theorem B1317751 : Blo 1315976 1317751 := bstep (se 1 (by rfl) ⟨988313, by rfl⟩ : syracuseStep 1317751 = 1976627) B1976627
theorem B1481611 : Blo 1315976 1481611 := bstep (se 1 (by rfl) ⟨1111208, by rfl⟩ : syracuseStep 1481611 = 2222417) B2222417
theorem B1317771 : Blo 1315976 1317771 := bstep (se 1 (by rfl) ⟨988328, by rfl⟩ : syracuseStep 1317771 = 1976657) B1976657
theorem B1317783 : Blo 1315976 1317783 := bstep (se 1 (by rfl) ⟨988337, by rfl⟩ : syracuseStep 1317783 = 1976675) B1976675
theorem B1317803 : Blo 1315976 1317803 := bstep (se 1 (by rfl) ⟨988352, by rfl⟩ : syracuseStep 1317803 = 1976705) B1976705
theorem B1317815 : Blo 1315976 1317815 := bstep (se 1 (by rfl) ⟨988361, by rfl⟩ : syracuseStep 1317815 = 1976723) B1976723
theorem B4447169 : Blo 1315976 4447169 := bstep (se 2 (by rfl) ⟨1667688, by rfl⟩ : syracuseStep 4447169 = 3335377) B3335377
theorem B1317835 : Blo 1315976 1317835 := bstep (se 1 (by rfl) ⟨988376, by rfl⟩ : syracuseStep 1317835 = 1976753) B1976753
theorem B1317847 : Blo 1315976 1317847 := bstep (se 1 (by rfl) ⟨988385, by rfl⟩ : syracuseStep 1317847 = 1976771) B1976771
theorem B1317867 : Blo 1315976 1317867 := bstep (se 1 (by rfl) ⟨988400, by rfl⟩ : syracuseStep 1317867 = 1976801) B1976801
theorem B1481719 : Blo 1315976 1481719 := bstep (se 1 (by rfl) ⟨1111289, by rfl⟩ : syracuseStep 1481719 = 2222579) B2222579
theorem B1317879 : Blo 1315976 1317879 := bstep (se 1 (by rfl) ⟨988409, by rfl⟩ : syracuseStep 1317879 = 1976819) B1976819
theorem B2964491 : Blo 1315976 2964491 := bstep (se 1 (by rfl) ⟨2223368, by rfl⟩ : syracuseStep 2964491 = 4446737) B4446737
theorem B1317899 : Blo 1315976 1317899 := bstep (se 1 (by rfl) ⟨988424, by rfl⟩ : syracuseStep 1317899 = 1976849) B1976849
theorem B1317911 : Blo 1315976 1317911 := bstep (se 1 (by rfl) ⟨988433, by rfl⟩ : syracuseStep 1317911 = 1976867) B1976867
theorem B1317931 : Blo 1315976 1317931 := bstep (se 1 (by rfl) ⟨988448, by rfl⟩ : syracuseStep 1317931 = 1976897) B1976897
theorem B1317943 : Blo 1315976 1317943 := bstep (se 1 (by rfl) ⟨988457, by rfl⟩ : syracuseStep 1317943 = 1976915) B1976915
theorem B2964545 : Blo 1315976 2964545 := bstep (se 2 (by rfl) ⟨1111704, by rfl⟩ : syracuseStep 2964545 = 2223409) B2223409
theorem B1317963 : Blo 1315976 1317963 := bstep (se 1 (by rfl) ⟨988472, by rfl⟩ : syracuseStep 1317963 = 1976945) B1976945
theorem B1317975 : Blo 1315976 1317975 := bstep (se 1 (by rfl) ⟨988481, by rfl⟩ : syracuseStep 1317975 = 1976963) B1976963
theorem B3333271 : Blo 1315976 3333271 := bstep (se 1 (by rfl) ⟨2499953, by rfl⟩ : syracuseStep 3333271 = 4999907) B4999907
theorem B1481899 : Blo 1315976 1481899 := bstep (se 1 (by rfl) ⟨1111424, by rfl⟩ : syracuseStep 1481899 = 2222849) B2222849
theorem B3005633 : Blo 1315976 3005633 := bstep (se 2 (by rfl) ⟨1127112, by rfl⟩ : syracuseStep 3005633 = 2254225) B2254225
theorem B2374849 : Blo 1315976 2374849 := bstep (se 2 (by rfl) ⟨890568, by rfl⟩ : syracuseStep 2374849 = 1781137) B1781137
theorem B5627083 : Blo 1315976 5627083 := bstep (se 1 (by rfl) ⟨4220312, by rfl⟩ : syracuseStep 5627083 = 8440625) B8440625
theorem B1482007 : Blo 1315976 1482007 := bstep (se 1 (by rfl) ⟨1111505, by rfl⟩ : syracuseStep 1482007 = 2223011) B2223011
theorem B2669849 : Blo 1315976 2669849 := bstep (se 2 (by rfl) ⟨1001193, by rfl⟩ : syracuseStep 2669849 = 2002387) B2002387
theorem B2964761 : Blo 1315976 2964761 := bstep (se 2 (by rfl) ⟨1111785, by rfl⟩ : syracuseStep 2964761 = 2223571) B2223571
theorem B6667595 : Blo 1315976 6667595 := bstep (se 1 (by rfl) ⟨5000696, by rfl⟩ : syracuseStep 6667595 = 10001393) B10001393
theorem B5782873 : Blo 1315976 5782873 := bstep (se 2 (by rfl) ⟨2168577, by rfl⟩ : syracuseStep 5782873 = 4337155) B4337155
theorem B2964851 : Blo 1315976 2964851 := bstep (se 1 (by rfl) ⟨2223638, by rfl⟩ : syracuseStep 2964851 = 4447277) B4447277
theorem B164322701 : Blo 1315976 164322701 := bstep (se 3 (by rfl) ⟨30810506, by rfl⟩ : syracuseStep 164322701 = 61621013) B61621013
theorem B4218263 : Blo 1315976 4218263 := bstep (se 1 (by rfl) ⟨3163697, by rfl⟩ : syracuseStep 4218263 = 6327395) B6327395
theorem B2964887 : Blo 1315976 2964887 := bstep (se 1 (by rfl) ⟨2223665, by rfl⟩ : syracuseStep 2964887 = 4447331) B4447331
theorem B1482187 : Blo 1315976 1482187 := bstep (se 1 (by rfl) ⟨1111640, by rfl⟩ : syracuseStep 1482187 = 2223281) B2223281
theorem B15007193 : Blo 1315976 15007193 := bstep (se 2 (by rfl) ⟨5627697, by rfl⟩ : syracuseStep 15007193 = 11255395) B11255395
theorem B4505053 : Blo 1315976 4505053 := bstep (se 3 (by rfl) ⟨844697, by rfl⟩ : syracuseStep 4505053 = 1689395) B1689395
theorem B5627357 : Blo 1315976 5627357 := bstep (se 3 (by rfl) ⟨1055129, by rfl⟩ : syracuseStep 5627357 = 2110259) B2110259
theorem B4447709 : Blo 1315976 4447709 := bstep (se 3 (by rfl) ⟨833945, by rfl⟩ : syracuseStep 4447709 = 1667891) B1667891
theorem B7495213 : Blo 1315976 7495213 := bstep (se 3 (by rfl) ⟨1405352, by rfl⟩ : syracuseStep 7495213 = 2810705) B2810705
theorem B1482295 : Blo 1315976 1482295 := bstep (se 1 (by rfl) ⟨1111721, by rfl⟩ : syracuseStep 1482295 = 2223443) B2223443
theorem B4996673 : Blo 1315976 4996673 := bstep (se 2 (by rfl) ⟨1873752, by rfl⟩ : syracuseStep 4996673 = 3747505) B3747505
theorem B10821185 : Blo 1315976 10821185 := bstep (se 2 (by rfl) ⟨4057944, by rfl⟩ : syracuseStep 10821185 = 8115889) B8115889
theorem B4218443 : Blo 1315976 4218443 := bstep (se 1 (by rfl) ⟨3163832, by rfl⟩ : syracuseStep 4218443 = 6327665) B6327665
theorem B3333707 : Blo 1315976 3333707 := bstep (se 1 (by rfl) ⟨2500280, by rfl⟩ : syracuseStep 3333707 = 5000561) B5000561
theorem B2965067 : Blo 1315976 2965067 := bstep (se 1 (by rfl) ⟨2223800, by rfl⟩ : syracuseStep 2965067 = 4447601) B4447601
theorem B7503461 : Blo 1315976 7503461 := bstep (se 4 (by rfl) ⟨703449, by rfl⟩ : syracuseStep 7503461 = 1406899) B1406899
theorem B2965121 : Blo 1315976 2965121 := bstep (se 2 (by rfl) ⟨1111920, by rfl⟩ : syracuseStep 2965121 = 2223841) B2223841
theorem B22486733 : Blo 1315976 22486733 := bstep (se 3 (by rfl) ⟨4216262, by rfl⟩ : syracuseStep 22486733 = 8432525) B8432525
theorem B36052685 : Blo 1315976 36052685 := bstep (se 3 (by rfl) ⟨6759878, by rfl⟩ : syracuseStep 36052685 = 13519757) B13519757
theorem B1973975 : Blo 1315976 1973975 := bstep (se 1 (by rfl) ⟨1480481, by rfl⟩ : syracuseStep 1973975 = 2960963) B2960963
theorem B1482475 : Blo 1315976 1482475 := bstep (se 1 (by rfl) ⟨1111856, by rfl⟩ : syracuseStep 1482475 = 2223713) B2223713
theorem B1974041 : Blo 1315976 1974041 := bstep (se 2 (by rfl) ⟨740265, by rfl⟩ : syracuseStep 1974041 = 1480531) B1480531
theorem B1482583 : Blo 1315976 1482583 := bstep (se 1 (by rfl) ⟨1111937, by rfl⟩ : syracuseStep 1482583 = 2223875) B2223875
theorem B4218713 : Blo 1315976 4218713 := bstep (se 2 (by rfl) ⟨1582017, by rfl⟩ : syracuseStep 4218713 = 3164035) B3164035
theorem B2965337 : Blo 1315976 2965337 := bstep (se 2 (by rfl) ⟨1112001, by rfl⟩ : syracuseStep 2965337 = 2224003) B2224003
theorem B1974155 : Blo 1315976 1974155 := bstep (se 1 (by rfl) ⟨1480616, by rfl⟩ : syracuseStep 1974155 = 2961233) B2961233
theorem B1974167 : Blo 1315976 1974167 := bstep (se 1 (by rfl) ⟨1480625, by rfl⟩ : syracuseStep 1974167 = 2961251) B2961251
theorem B2965427 : Blo 1315976 2965427 := bstep (se 1 (by rfl) ⟨2224070, by rfl⟩ : syracuseStep 2965427 = 4448141) B4448141
theorem B3334081 : Blo 1315976 3334081 := bstep (se 2 (by rfl) ⟨1250280, by rfl⟩ : syracuseStep 3334081 = 2500561) B2500561
theorem B2252747 : Blo 1315976 2252747 := bstep (se 1 (by rfl) ⟨1689560, by rfl⟩ : syracuseStep 2252747 = 3379121) B3379121
theorem B2498519 : Blo 1315976 2498519 := bstep (se 1 (by rfl) ⟨1873889, by rfl⟩ : syracuseStep 2498519 = 3747779) B3747779
theorem B1974233 : Blo 1315976 1974233 := bstep (se 2 (by rfl) ⟨740337, by rfl⟩ : syracuseStep 1974233 = 1480675) B1480675
theorem B1974287 : Blo 1315976 1974287 := bstep (se 1 (by rfl) ⟨1480715, by rfl⟩ : syracuseStep 1974287 = 2961431) B2961431
theorem B2252815 : Blo 1315976 2252815 := bstep (se 1 (by rfl) ⟨1689611, by rfl⟩ : syracuseStep 2252815 = 3379223) B3379223
theorem B4743211 : Blo 1315976 4743211 := bstep (se 1 (by rfl) ⟨3557408, by rfl⟩ : syracuseStep 4743211 = 7114817) B7114817
theorem B2670635 : Blo 1315976 2670635 := bstep (se 1 (by rfl) ⟨2002976, by rfl⟩ : syracuseStep 2670635 = 4005953) B4005953
theorem B1974329 : Blo 1315976 1974329 := bstep (se 2 (by rfl) ⟨740373, by rfl⟩ : syracuseStep 1974329 = 1480747) B1480747
theorem B5627971 : Blo 1315976 5627971 := bstep (se 1 (by rfl) ⟨4220978, by rfl⟩ : syracuseStep 5627971 = 8441957) B8441957
theorem B1974407 : Blo 1315976 1974407 := bstep (se 1 (by rfl) ⟨1480805, by rfl⟩ : syracuseStep 1974407 = 2961611) B2961611
theorem B1974443 : Blo 1315976 1974443 := bstep (se 1 (by rfl) ⟨1480832, by rfl⟩ : syracuseStep 1974443 = 2961665) B2961665
theorem B1974473 : Blo 1315976 1974473 := bstep (se 2 (by rfl) ⟨740427, by rfl⟩ : syracuseStep 1974473 = 1480855) B1480855
theorem B1974587 : Blo 1315976 1974587 := bstep (se 1 (by rfl) ⟨1480940, by rfl⟩ : syracuseStep 1974587 = 2961881) B2961881
theorem B1974647 : Blo 1315976 1974647 := bstep (se 1 (by rfl) ⟨1480985, by rfl⟩ : syracuseStep 1974647 = 2961971) B2961971
theorem B2498951 : Blo 1315976 2498951 := bstep (se 1 (by rfl) ⟨1874213, by rfl⟩ : syracuseStep 2498951 = 3748427) B3748427
theorem B1974671 : Blo 1315976 1974671 := bstep (se 1 (by rfl) ⟨1481003, by rfl⟩ : syracuseStep 1974671 = 2962007) B2962007
theorem B7119251 : Blo 1315976 7119251 := bstep (se 1 (by rfl) ⟨5339438, by rfl⟩ : syracuseStep 7119251 = 10678877) B10678877
theorem B3334547 : Blo 1315976 3334547 := bstep (se 1 (by rfl) ⟨2500910, by rfl⟩ : syracuseStep 3334547 = 5001821) B5001821
theorem B10142099 : Blo 1315976 10142099 := bstep (se 1 (by rfl) ⟨7606574, by rfl⟩ : syracuseStep 10142099 = 15213149) B15213149
theorem B3752345 : Blo 1315976 3752345 := bstep (se 2 (by rfl) ⟨1407129, by rfl⟩ : syracuseStep 3752345 = 2814259) B2814259
theorem B1974713 : Blo 1315976 1974713 := bstep (se 2 (by rfl) ⟨740517, by rfl⟩ : syracuseStep 1974713 = 1481035) B1481035
theorem B6668729 : Blo 1315976 6668729 := bstep (se 2 (by rfl) ⟨2500773, by rfl⟩ : syracuseStep 6668729 = 5001547) B5001547
theorem B1335739 : Blo 1315976 1335739 := bstep (se 1 (by rfl) ⟨1001804, by rfl⟩ : syracuseStep 1335739 = 2003609) B2003609
theorem B1974791 : Blo 1315976 1974791 := bstep (se 1 (by rfl) ⟨1481093, by rfl⟩ : syracuseStep 1974791 = 2962187) B2962187
theorem B3293729 : Blo 1315976 3293729 := bstep (se 2 (by rfl) ⟨1235148, by rfl⟩ : syracuseStep 3293729 = 2470297) B2470297
theorem B1974827 : Blo 1315976 1974827 := bstep (se 1 (by rfl) ⟨1481120, by rfl⟩ : syracuseStep 1974827 = 2962241) B2962241
theorem B1876537 : Blo 1315976 1876537 := bstep (se 2 (by rfl) ⟨703701, by rfl⟩ : syracuseStep 1876537 = 1407403) B1407403
theorem B1974857 : Blo 1315976 1974857 := bstep (se 2 (by rfl) ⟨740571, by rfl⟩ : syracuseStep 1974857 = 1481143) B1481143
theorem B12649061 : Blo 1315976 12649061 := bstep (se 4 (by rfl) ⟨1185849, by rfl⟩ : syracuseStep 12649061 = 2371699) B2371699
theorem B8004215 : Blo 1315976 8004215 := bstep (se 1 (by rfl) ⟨6003161, by rfl⟩ : syracuseStep 8004215 = 12006323) B12006323
theorem B3334841 : Blo 1315976 3334841 := bstep (se 2 (by rfl) ⟨1250565, by rfl⟩ : syracuseStep 3334841 = 2501131) B2501131
theorem B1974971 : Blo 1315976 1974971 := bstep (se 1 (by rfl) ⟨1481228, by rfl⟩ : syracuseStep 1974971 = 2962457) B2962457
theorem B1975031 : Blo 1315976 1975031 := bstep (se 1 (by rfl) ⟨1481273, by rfl⟩ : syracuseStep 1975031 = 2962547) B2962547
theorem B3162881 : Blo 1315976 3162881 := bstep (se 2 (by rfl) ⟨1186080, by rfl⟩ : syracuseStep 3162881 = 2372161) B2372161
theorem B1975055 : Blo 1315976 1975055 := bstep (se 1 (by rfl) ⟨1481291, by rfl⟩ : syracuseStep 1975055 = 2962583) B2962583
theorem B22504229 : Blo 1315976 22504229 := bstep (se 4 (by rfl) ⟨2109771, by rfl⟩ : syracuseStep 22504229 = 4219543) B4219543
theorem B1975097 : Blo 1315976 1975097 := bstep (se 2 (by rfl) ⟨740661, by rfl⟩ : syracuseStep 1975097 = 1481323) B1481323
theorem B1975175 : Blo 1315976 1975175 := bstep (se 1 (by rfl) ⟨1481381, by rfl⟩ : syracuseStep 1975175 = 2962763) B2962763
theorem B1975211 : Blo 1315976 1975211 := bstep (se 1 (by rfl) ⟨1481408, by rfl⟩ : syracuseStep 1975211 = 2962817) B2962817
theorem B1975241 : Blo 1315976 1975241 := bstep (se 2 (by rfl) ⟨740715, by rfl⟩ : syracuseStep 1975241 = 1481431) B1481431
theorem B4006913 : Blo 1315976 4006913 := bstep (se 2 (by rfl) ⟨1502592, by rfl⟩ : syracuseStep 4006913 = 3005185) B3005185
theorem B7504919 : Blo 1315976 7504919 := bstep (se 1 (by rfl) ⟨5628689, by rfl⟩ : syracuseStep 7504919 = 11257379) B11257379
theorem B1975355 : Blo 1315976 1975355 := bstep (se 1 (by rfl) ⟨1481516, by rfl⟩ : syracuseStep 1975355 = 2963033) B2963033
theorem B2221175 : Blo 1315976 2221175 := bstep (se 1 (by rfl) ⟨1665881, by rfl⟩ : syracuseStep 2221175 = 3331763) B3331763
theorem B1975415 : Blo 1315976 1975415 := bstep (se 1 (by rfl) ⟨1481561, by rfl⟩ : syracuseStep 1975415 = 2963123) B2963123
theorem B1975439 : Blo 1315976 1975439 := bstep (se 1 (by rfl) ⟨1481579, by rfl⟩ : syracuseStep 1975439 = 2963159) B2963159
theorem B1975481 : Blo 1315976 1975481 := bstep (se 2 (by rfl) ⟨740805, by rfl⟩ : syracuseStep 1975481 = 1481611) B1481611
theorem B1975559 : Blo 1315976 1975559 := bstep (se 1 (by rfl) ⟨1481669, by rfl⟩ : syracuseStep 1975559 = 2963339) B2963339
theorem B1975595 : Blo 1315976 1975595 := bstep (se 1 (by rfl) ⟨1481696, by rfl⟩ : syracuseStep 1975595 = 2963393) B2963393
theorem B1975625 : Blo 1315976 1975625 := bstep (se 2 (by rfl) ⟨740859, by rfl⟩ : syracuseStep 1975625 = 1481719) B1481719
theorem B3335539 : Blo 1315976 3335539 := bstep (se 1 (by rfl) ⟨2501654, by rfl⟩ : syracuseStep 3335539 = 5003309) B5003309
theorem B2532755 : Blo 1315976 2532755 := bstep (se 1 (by rfl) ⟨1899566, by rfl⟩ : syracuseStep 2532755 = 3799133) B3799133
theorem B4744595 : Blo 1315976 4744595 := bstep (se 1 (by rfl) ⟨3558446, by rfl⟩ : syracuseStep 4744595 = 7116893) B7116893
theorem B1975739 : Blo 1315976 1975739 := bstep (se 1 (by rfl) ⟨1481804, by rfl⟩ : syracuseStep 1975739 = 2963609) B2963609
theorem B1975799 : Blo 1315976 1975799 := bstep (se 1 (by rfl) ⟨1481849, by rfl⟩ : syracuseStep 1975799 = 2963699) B2963699
theorem B3335681 : Blo 1315976 3335681 := bstep (se 2 (by rfl) ⟨1250880, by rfl⟩ : syracuseStep 3335681 = 2501761) B2501761
theorem B7505419 : Blo 1315976 7505419 := bstep (se 1 (by rfl) ⟨5629064, by rfl⟩ : syracuseStep 7505419 = 11258129) B11258129
theorem B1689103 : Blo 1315976 1689103 := bstep (se 1 (by rfl) ⟨1266827, by rfl⟩ : syracuseStep 1689103 = 2533655) B2533655
theorem B1975823 : Blo 1315976 1975823 := bstep (se 1 (by rfl) ⟨1481867, by rfl⟩ : syracuseStep 1975823 = 2963735) B2963735
theorem B2221627 : Blo 1315976 2221627 := bstep (se 1 (by rfl) ⟨1666220, by rfl⟩ : syracuseStep 2221627 = 3332441) B3332441
theorem B1975865 : Blo 1315976 1975865 := bstep (se 2 (by rfl) ⟨740949, by rfl⟩ : syracuseStep 1975865 = 1481899) B1481899
theorem B5621309 : Blo 1315976 5621309 := bstep (se 3 (by rfl) ⟨1053995, by rfl⟩ : syracuseStep 5621309 = 2107991) B2107991
theorem B4441661 : Blo 1315976 4441661 := bstep (se 3 (by rfl) ⟨832811, by rfl⟩ : syracuseStep 4441661 = 1665623) B1665623
theorem B36537925 : Blo 1315976 36537925 := bstep (se 4 (by rfl) ⟨3425430, by rfl⟩ : syracuseStep 36537925 = 6850861) B6850861
theorem B3163735 : Blo 1315976 3163735 := bstep (se 1 (by rfl) ⟨2372801, by rfl⟩ : syracuseStep 3163735 = 4745603) B4745603
theorem B1975943 : Blo 1315976 1975943 := bstep (se 1 (by rfl) ⟨1481957, by rfl⟩ : syracuseStep 1975943 = 2963915) B2963915
theorem B1975979 : Blo 1315976 1975979 := bstep (se 1 (by rfl) ⟨1481984, by rfl⟩ : syracuseStep 1975979 = 2963969) B2963969
theorem B2221769 : Blo 1315976 2221769 := bstep (se 2 (by rfl) ⟨833163, by rfl⟩ : syracuseStep 2221769 = 1666327) B1666327
theorem B1976009 : Blo 1315976 1976009 := bstep (se 2 (by rfl) ⟨741003, by rfl⟩ : syracuseStep 1976009 = 1482007) B1482007
theorem B6670025 : Blo 1315976 6670025 := bstep (se 2 (by rfl) ⟨2501259, by rfl⟩ : syracuseStep 6670025 = 5002519) B5002519
theorem B11249381 : Blo 1315976 11249381 := bstep (se 4 (by rfl) ⟨1054629, by rfl⟩ : syracuseStep 11249381 = 2109259) B2109259
theorem B9996047 : Blo 1315976 9996047 := bstep (se 1 (by rfl) ⟨7497035, by rfl⟩ : syracuseStep 9996047 = 14994071) B14994071
theorem B6760207 : Blo 1315976 6760207 := bstep (se 1 (by rfl) ⟨5070155, by rfl⟩ : syracuseStep 6760207 = 10140311) B10140311
theorem B7710497 : Blo 1315976 7710497 := bstep (se 2 (by rfl) ⟨2891436, by rfl⟩ : syracuseStep 7710497 = 5782873) B5782873
theorem B28870451 : Blo 1315976 28870451 := bstep (se 1 (by rfl) ⟨21652838, by rfl⟩ : syracuseStep 28870451 = 43305677) B43305677
theorem B1976123 : Blo 1315976 1976123 := bstep (se 1 (by rfl) ⟨1482092, by rfl⟩ : syracuseStep 1976123 = 2964185) B2964185
theorem B1976183 : Blo 1315976 1976183 := bstep (se 1 (by rfl) ⟨1482137, by rfl⟩ : syracuseStep 1976183 = 2964275) B2964275
theorem B1976207 : Blo 1315976 1976207 := bstep (se 1 (by rfl) ⟨1482155, by rfl⟩ : syracuseStep 1976207 = 2964311) B2964311
theorem B1976249 : Blo 1315976 1976249 := bstep (se 2 (by rfl) ⟨741093, by rfl⟩ : syracuseStep 1976249 = 1482187) B1482187
theorem B6006737 : Blo 1315976 6006737 := bstep (se 2 (by rfl) ⟨2252526, by rfl⟩ : syracuseStep 6006737 = 4505053) B4505053
theorem B1976327 : Blo 1315976 1976327 := bstep (se 1 (by rfl) ⟨1482245, by rfl⟩ : syracuseStep 1976327 = 2964491) B2964491
theorem B1976363 : Blo 1315976 1976363 := bstep (se 1 (by rfl) ⟨1482272, by rfl⟩ : syracuseStep 1976363 = 2964545) B2964545
theorem B1976393 : Blo 1315976 1976393 := bstep (se 2 (by rfl) ⟨741147, by rfl⟩ : syracuseStep 1976393 = 1482295) B1482295
theorem B1779899 : Blo 1315976 1779899 := bstep (se 1 (by rfl) ⟨1334924, by rfl⟩ : syracuseStep 1779899 = 2669849) B2669849
theorem B1976507 : Blo 1315976 1976507 := bstep (se 1 (by rfl) ⟨1482380, by rfl⟩ : syracuseStep 1976507 = 2964761) B2964761
theorem B1976567 : Blo 1315976 1976567 := bstep (se 1 (by rfl) ⟨1482425, by rfl⟩ : syracuseStep 1976567 = 2964851) B2964851
theorem B2812175 : Blo 1315976 2812175 := bstep (se 1 (by rfl) ⟨2109131, by rfl⟩ : syracuseStep 2812175 = 4218263) B4218263
theorem B1976591 : Blo 1315976 1976591 := bstep (se 1 (by rfl) ⟨1482443, by rfl⟩ : syracuseStep 1976591 = 2964887) B2964887
theorem B1976633 : Blo 1315976 1976633 := bstep (se 2 (by rfl) ⟨741237, by rfl⟩ : syracuseStep 1976633 = 1482475) B1482475
theorem B10004795 : Blo 1315976 10004795 := bstep (se 1 (by rfl) ⟨7503596, by rfl⟩ : syracuseStep 10004795 = 15007193) B15007193
theorem B2812295 : Blo 1315976 2812295 := bstep (se 1 (by rfl) ⟨2109221, by rfl⟩ : syracuseStep 2812295 = 4218443) B4218443
theorem B2222471 : Blo 1315976 2222471 := bstep (se 1 (by rfl) ⟨1666853, by rfl⟩ : syracuseStep 2222471 = 3333707) B3333707
theorem B1976711 : Blo 1315976 1976711 := bstep (se 1 (by rfl) ⟨1482533, by rfl⟩ : syracuseStep 1976711 = 2965067) B2965067
theorem B9488785 : Blo 1315976 9488785 := bstep (se 2 (by rfl) ⟨3558294, by rfl⟩ : syracuseStep 9488785 = 7116589) B7116589
theorem B7498129 : Blo 1315976 7498129 := bstep (se 2 (by rfl) ⟨2811798, by rfl⟩ : syracuseStep 7498129 = 5623597) B5623597
theorem B16877969 : Blo 1315976 16877969 := bstep (se 2 (by rfl) ⟨6329238, by rfl⟩ : syracuseStep 16877969 = 12658477) B12658477
theorem B1976747 : Blo 1315976 1976747 := bstep (se 1 (by rfl) ⟨1482560, by rfl⟩ : syracuseStep 1976747 = 2965121) B2965121
theorem B1976777 : Blo 1315976 1976777 := bstep (se 2 (by rfl) ⟨741291, by rfl⟩ : syracuseStep 1976777 = 1482583) B1482583
theorem B2812475 : Blo 1315976 2812475 := bstep (se 1 (by rfl) ⟨2109356, by rfl⟩ : syracuseStep 2812475 = 4218713) B4218713
theorem B1976891 : Blo 1315976 1976891 := bstep (se 1 (by rfl) ⟨1482668, by rfl⟩ : syracuseStep 1976891 = 2965337) B2965337
theorem B1976951 : Blo 1315976 1976951 := bstep (se 1 (by rfl) ⟨1482713, by rfl⟩ : syracuseStep 1976951 = 2965427) B2965427
theorem B1501831 : Blo 1315976 1501831 := bstep (se 1 (by rfl) ⟨1126373, by rfl⟩ : syracuseStep 1501831 = 2252747) B2252747
theorem B1665679 : Blo 1315976 1665679 := bstep (se 1 (by rfl) ⟨1249259, by rfl⟩ : syracuseStep 1665679 = 2498519) B2498519
theorem B28879577 : Blo 1315976 28879577 := bstep (se 2 (by rfl) ⟨10829841, by rfl⟩ : syracuseStep 28879577 = 21659683) B21659683
theorem B2501435 : Blo 1315976 2501435 := bstep (se 1 (by rfl) ⟨1876076, by rfl⟩ : syracuseStep 2501435 = 3752153) B3752153
theorem B6663059 : Blo 1315976 6663059 := bstep (se 1 (by rfl) ⟨4997294, by rfl⟩ : syracuseStep 6663059 = 9994589) B9994589
theorem B5000089 : Blo 1315976 5000089 := bstep (se 2 (by rfl) ⟨1875033, by rfl⟩ : syracuseStep 5000089 = 3750067) B3750067
theorem B4443065 : Blo 1315976 4443065 := bstep (se 2 (by rfl) ⟨1666149, by rfl⟩ : syracuseStep 4443065 = 3332299) B3332299
theorem B2223119 : Blo 1315976 2223119 := bstep (se 1 (by rfl) ⟨1667339, by rfl⟩ : syracuseStep 2223119 = 3334679) B3334679
theorem B2812961 : Blo 1315976 2812961 := bstep (se 2 (by rfl) ⟨1054860, by rfl⟩ : syracuseStep 2812961 = 2109721) B2109721
theorem B5065847 : Blo 1315976 5065847 := bstep (se 1 (by rfl) ⟨3799385, by rfl⟩ : syracuseStep 5065847 = 7598771) B7598771
theorem B8015021 : Blo 1315976 8015021 := bstep (se 3 (by rfl) ⟨1502816, by rfl⟩ : syracuseStep 8015021 = 3005633) B3005633
theorem B5000393 : Blo 1315976 5000393 := bstep (se 2 (by rfl) ⟨1875147, by rfl⟩ : syracuseStep 5000393 = 3750295) B3750295
theorem B2501921 : Blo 1315976 2501921 := bstep (se 2 (by rfl) ⟨938220, by rfl⟩ : syracuseStep 2501921 = 1876441) B1876441
theorem B1666423 : Blo 1315976 1666423 := bstep (se 1 (by rfl) ⟨1249817, by rfl⟩ : syracuseStep 1666423 = 2499635) B2499635
theorem B9629113 : Blo 1315976 9629113 := bstep (se 2 (by rfl) ⟨3610917, by rfl⟩ : syracuseStep 9629113 = 7221835) B7221835
theorem B4443659 : Blo 1315976 4443659 := bstep (se 1 (by rfl) ⟨3332744, by rfl⟩ : syracuseStep 4443659 = 6665489) B6665489
theorem B2223659 : Blo 1315976 2223659 := bstep (se 1 (by rfl) ⟨1667744, by rfl⟩ : syracuseStep 2223659 = 3335489) B3335489
theorem B2002489 : Blo 1315976 2002489 := bstep (se 2 (by rfl) ⟨750933, by rfl⟩ : syracuseStep 2002489 = 1501867) B1501867
theorem B4443767 : Blo 1315976 4443767 := bstep (se 1 (by rfl) ⟨3332825, by rfl⟩ : syracuseStep 4443767 = 6665651) B6665651
theorem B1666747 : Blo 1315976 1666747 := bstep (se 1 (by rfl) ⟨1250060, by rfl⟩ : syracuseStep 1666747 = 2500121) B2500121
theorem B76992257 : Blo 1315976 76992257 := bstep (se 2 (by rfl) ⟨28872096, by rfl⟩ : syracuseStep 76992257 = 57744193) B57744193
theorem B5623667 : Blo 1315976 5623667 := bstep (se 1 (by rfl) ⟨4217750, by rfl⟩ : syracuseStep 5623667 = 8435501) B8435501
theorem B2813815 : Blo 1315976 2813815 := bstep (se 1 (by rfl) ⟨2110361, by rfl⟩ : syracuseStep 2813815 = 4220723) B4220723
theorem B2961287 : Blo 1315976 2961287 := bstep (se 1 (by rfl) ⟨2220965, by rfl⟩ : syracuseStep 2961287 = 4441931) B4441931
theorem B6418321 : Blo 1315976 6418321 := bstep (se 2 (by rfl) ⟨2406870, by rfl⟩ : syracuseStep 6418321 = 4813741) B4813741
theorem B2371475 : Blo 1315976 2371475 := bstep (se 1 (by rfl) ⟨1778606, by rfl⟩ : syracuseStep 2371475 = 3557213) B3557213
theorem B2224057 : Blo 1315976 2224057 := bstep (se 2 (by rfl) ⟨834021, by rfl⟩ : syracuseStep 2224057 = 1668043) B1668043
theorem B2961467 : Blo 1315976 2961467 := bstep (se 1 (by rfl) ⟨2221100, by rfl⟩ : syracuseStep 2961467 = 4442201) B4442201
theorem B5001335 : Blo 1315976 5001335 := bstep (se 1 (by rfl) ⟨3751001, by rfl⟩ : syracuseStep 5001335 = 7502003) B7502003
theorem B1667243 : Blo 1315976 1667243 := bstep (se 1 (by rfl) ⟨1250432, by rfl⟩ : syracuseStep 1667243 = 2500865) B2500865
theorem B2961593 : Blo 1315976 2961593 := bstep (se 2 (by rfl) ⟨1110597, by rfl⟩ : syracuseStep 2961593 = 2221195) B2221195
theorem B4444361 : Blo 1315976 4444361 := bstep (se 2 (by rfl) ⟨1666635, by rfl⟩ : syracuseStep 4444361 = 3333271) B3333271
theorem B3166465 : Blo 1315976 3166465 := bstep (se 2 (by rfl) ⟨1187424, by rfl⟩ : syracuseStep 3166465 = 2374849) B2374849
theorem B22819313 : Blo 1315976 22819313 := bstep (se 2 (by rfl) ⟨8557242, by rfl⟩ : syracuseStep 22819313 = 17114485) B17114485
theorem B2961935 : Blo 1315976 2961935 := bstep (se 1 (by rfl) ⟨2221451, by rfl⟩ : syracuseStep 2961935 = 4442903) B4442903
theorem B2961953 : Blo 1315976 2961953 := bstep (se 2 (by rfl) ⟨1110732, by rfl⟩ : syracuseStep 2961953 = 2221465) B2221465
theorem B14430797 : Blo 1315976 14430797 := bstep (se 3 (by rfl) ⟨2705774, by rfl⟩ : syracuseStep 14430797 = 5411549) B5411549
theorem B1667719 : Blo 1315976 1667719 := bstep (se 1 (by rfl) ⟨1250789, by rfl⟩ : syracuseStep 1667719 = 2501579) B2501579
theorem B3748609 : Blo 1315976 3748609 := bstep (se 2 (by rfl) ⟨1405728, by rfl⟩ : syracuseStep 3748609 = 2811457) B2811457
theorem B7500545 : Blo 1315976 7500545 := bstep (se 2 (by rfl) ⟨2812704, by rfl⟩ : syracuseStep 7500545 = 5625409) B5625409
theorem B2962295 : Blo 1315976 2962295 := bstep (se 1 (by rfl) ⟨2221721, by rfl⟩ : syracuseStep 2962295 = 4443443) B4443443
theorem B4445063 : Blo 1315976 4445063 := bstep (se 1 (by rfl) ⟨3333797, by rfl⟩ : syracuseStep 4445063 = 6667595) B6667595
theorem B109548467 : Blo 1315976 109548467 := bstep (se 1 (by rfl) ⟨82161350, by rfl⟩ : syracuseStep 109548467 = 164322701) B164322701
theorem B3331115 : Blo 1315976 3331115 := bstep (se 1 (by rfl) ⟨2498336, by rfl⟩ : syracuseStep 3331115 = 4996673) B4996673
theorem B7214123 : Blo 1315976 7214123 := bstep (se 1 (by rfl) ⟨5410592, by rfl⟩ : syracuseStep 7214123 = 10821185) B10821185
theorem B2962475 : Blo 1315976 2962475 := bstep (se 1 (by rfl) ⟨2221856, by rfl⟩ : syracuseStep 2962475 = 4443713) B4443713
theorem B5002307 : Blo 1315976 5002307 := bstep (se 1 (by rfl) ⟨3751730, by rfl⟩ : syracuseStep 5002307 = 7503461) B7503461
theorem B6091843 : Blo 1315976 6091843 := bstep (se 1 (by rfl) ⟨4568882, by rfl⟩ : syracuseStep 6091843 = 9137765) B9137765
theorem B1315983 : Blo 1315976 1315983 := bstep (se 1 (by rfl) ⟨986987, by rfl⟩ : syracuseStep 1315983 = 1973975) B1973975
theorem B1316027 : Blo 1315976 1316027 := bstep (se 1 (by rfl) ⟨987020, by rfl⟩ : syracuseStep 1316027 = 1974041) B1974041
theorem B4445441 : Blo 1315976 4445441 := bstep (se 2 (by rfl) ⟨1667040, by rfl⟩ : syracuseStep 4445441 = 3334081) B3334081
theorem B1316103 : Blo 1315976 1316103 := bstep (se 1 (by rfl) ⟨987077, by rfl⟩ : syracuseStep 1316103 = 1974155) B1974155
theorem B1316111 : Blo 1315976 1316111 := bstep (se 1 (by rfl) ⟨987083, by rfl⟩ : syracuseStep 1316111 = 1974167) B1974167
theorem B1316155 : Blo 1315976 1316155 := bstep (se 1 (by rfl) ⟨987116, by rfl⟩ : syracuseStep 1316155 = 1974233) B1974233
theorem B3749179 : Blo 1315976 3749179 := bstep (se 1 (by rfl) ⟨2811884, by rfl⟩ : syracuseStep 3749179 = 5623769) B5623769
theorem B1316231 : Blo 1315976 1316231 := bstep (se 1 (by rfl) ⟨987173, by rfl⟩ : syracuseStep 1316231 = 1974347) B1974347
theorem B1316239 : Blo 1315976 1316239 := bstep (se 1 (by rfl) ⟨987179, by rfl⟩ : syracuseStep 1316239 = 1974359) B1974359
theorem B2962835 : Blo 1315976 2962835 := bstep (se 1 (by rfl) ⟨2222126, by rfl⟩ : syracuseStep 2962835 = 4444253) B4444253
theorem B1316283 : Blo 1315976 1316283 := bstep (se 1 (by rfl) ⟨987212, by rfl⟩ : syracuseStep 1316283 = 1974425) B1974425
theorem B2962889 : Blo 1315976 2962889 := bstep (se 2 (by rfl) ⟨1111083, by rfl⟩ : syracuseStep 2962889 = 2222167) B2222167
theorem B1316359 : Blo 1315976 1316359 := bstep (se 1 (by rfl) ⟨987269, by rfl⟩ : syracuseStep 1316359 = 1974539) B1974539
theorem B1316367 : Blo 1315976 1316367 := bstep (se 1 (by rfl) ⟨987275, by rfl⟩ : syracuseStep 1316367 = 1974551) B1974551
theorem B1316411 : Blo 1315976 1316411 := bstep (se 1 (by rfl) ⟨987308, by rfl⟩ : syracuseStep 1316411 = 1974617) B1974617
theorem B1316487 : Blo 1315976 1316487 := bstep (se 1 (by rfl) ⟨987365, by rfl⟩ : syracuseStep 1316487 = 1974731) B1974731
theorem B1316495 : Blo 1315976 1316495 := bstep (se 1 (by rfl) ⟨987371, by rfl⟩ : syracuseStep 1316495 = 1974743) B1974743
theorem B1316539 : Blo 1315976 1316539 := bstep (se 1 (by rfl) ⟨987404, by rfl⟩ : syracuseStep 1316539 = 1974809) B1974809
theorem B1406651 : Blo 1315976 1406651 := bstep (se 1 (by rfl) ⟨1054988, by rfl⟩ : syracuseStep 1406651 = 2109977) B2109977
theorem B1316615 : Blo 1315976 1316615 := bstep (se 1 (by rfl) ⟨987461, by rfl⟩ : syracuseStep 1316615 = 1974923) B1974923
theorem B1316623 : Blo 1315976 1316623 := bstep (se 1 (by rfl) ⟨987467, by rfl⟩ : syracuseStep 1316623 = 1974935) B1974935
theorem B1316667 : Blo 1315976 1316667 := bstep (se 1 (by rfl) ⟨987500, by rfl⟩ : syracuseStep 1316667 = 1975001) B1975001
theorem B3331955 : Blo 1315976 3331955 := bstep (se 1 (by rfl) ⟨2498966, by rfl⟩ : syracuseStep 3331955 = 4997933) B4997933
theorem B3331975 : Blo 1315976 3331975 := bstep (se 1 (by rfl) ⟨2498981, by rfl⟩ : syracuseStep 3331975 = 4997963) B4997963
theorem B1316743 : Blo 1315976 1316743 := bstep (se 1 (by rfl) ⟨987557, by rfl⟩ : syracuseStep 1316743 = 1975115) B1975115
theorem B1316751 : Blo 1315976 1316751 := bstep (se 1 (by rfl) ⟨987563, by rfl⟩ : syracuseStep 1316751 = 1975127) B1975127
theorem B6666137 : Blo 1315976 6666137 := bstep (se 2 (by rfl) ⟨2499801, by rfl⟩ : syracuseStep 6666137 = 4999603) B4999603
theorem B1873849 : Blo 1315976 1873849 := bstep (se 2 (by rfl) ⟨702693, by rfl⟩ : syracuseStep 1873849 = 1405387) B1405387
theorem B1316795 : Blo 1315976 1316795 := bstep (se 1 (by rfl) ⟨987596, by rfl⟩ : syracuseStep 1316795 = 1975193) B1975193
theorem B1480711 : Blo 1315976 1480711 := bstep (se 1 (by rfl) ⟨1110533, by rfl⟩ : syracuseStep 1480711 = 2221067) B2221067
theorem B1316871 : Blo 1315976 1316871 := bstep (se 1 (by rfl) ⟨987653, by rfl⟩ : syracuseStep 1316871 = 1975307) B1975307
theorem B1316879 : Blo 1315976 1316879 := bstep (se 1 (by rfl) ⟨987659, by rfl⟩ : syracuseStep 1316879 = 1975319) B1975319
theorem B1873963 : Blo 1315976 1873963 := bstep (se 1 (by rfl) ⟨1405472, by rfl⟩ : syracuseStep 1873963 = 2810945) B2810945
theorem B4446251 : Blo 1315976 4446251 := bstep (se 1 (by rfl) ⟨3334688, by rfl⟩ : syracuseStep 4446251 = 6669377) B6669377
theorem B1316923 : Blo 1315976 1316923 := bstep (se 1 (by rfl) ⟨987692, by rfl⟩ : syracuseStep 1316923 = 1975385) B1975385
theorem B7600247 : Blo 1315976 7600247 := bstep (se 1 (by rfl) ⟨5700185, by rfl⟩ : syracuseStep 7600247 = 11400371) B11400371
theorem B1316999 : Blo 1315976 1316999 := bstep (se 1 (by rfl) ⟨987749, by rfl⟩ : syracuseStep 1316999 = 1975499) B1975499
theorem B2963591 : Blo 1315976 2963591 := bstep (se 1 (by rfl) ⟨2222693, by rfl⟩ : syracuseStep 2963591 = 4445387) B4445387
theorem B1317007 : Blo 1315976 1317007 := bstep (se 1 (by rfl) ⟨987755, by rfl⟩ : syracuseStep 1317007 = 1975511) B1975511
theorem B3332249 : Blo 1315976 3332249 := bstep (se 2 (by rfl) ⟨1249593, by rfl⟩ : syracuseStep 3332249 = 2499187) B2499187
theorem B1480891 : Blo 1315976 1480891 := bstep (se 1 (by rfl) ⟨1110668, by rfl⟩ : syracuseStep 1480891 = 2221337) B2221337
theorem B1317051 : Blo 1315976 1317051 := bstep (se 1 (by rfl) ⟨987788, by rfl⟩ : syracuseStep 1317051 = 1975577) B1975577
theorem B1317127 : Blo 1315976 1317127 := bstep (se 1 (by rfl) ⟨987845, by rfl⟩ : syracuseStep 1317127 = 1975691) B1975691
theorem B1874191 : Blo 1315976 1874191 := bstep (se 1 (by rfl) ⟨1405643, by rfl⟩ : syracuseStep 1874191 = 2811287) B2811287
theorem B1317135 : Blo 1315976 1317135 := bstep (se 1 (by rfl) ⟨987851, by rfl⟩ : syracuseStep 1317135 = 1975703) B1975703
theorem B3332411 : Blo 1315976 3332411 := bstep (se 1 (by rfl) ⟨2499308, by rfl⟩ : syracuseStep 3332411 = 4998617) B4998617
theorem B1317179 : Blo 1315976 1317179 := bstep (se 1 (by rfl) ⟨987884, by rfl⟩ : syracuseStep 1317179 = 1975769) B1975769
theorem B2963771 : Blo 1315976 2963771 := bstep (se 1 (by rfl) ⟨2222828, by rfl⟩ : syracuseStep 2963771 = 4445657) B4445657
theorem B1317255 : Blo 1315976 1317255 := bstep (se 1 (by rfl) ⟨987941, by rfl⟩ : syracuseStep 1317255 = 1975883) B1975883
theorem B1317263 : Blo 1315976 1317263 := bstep (se 1 (by rfl) ⟨987947, by rfl⟩ : syracuseStep 1317263 = 1975895) B1975895
theorem B2963897 : Blo 1315976 2963897 := bstep (se 2 (by rfl) ⟨1111461, by rfl⟩ : syracuseStep 2963897 = 2222923) B2222923
theorem B1317307 : Blo 1315976 1317307 := bstep (se 1 (by rfl) ⟨987980, by rfl⟩ : syracuseStep 1317307 = 1975961) B1975961
theorem B1317383 : Blo 1315976 1317383 := bstep (se 1 (by rfl) ⟨988037, by rfl⟩ : syracuseStep 1317383 = 1976075) B1976075
theorem B427571725 : Blo 1315976 427571725 := bstep (se 3 (by rfl) ⟨80169698, by rfl⟩ : syracuseStep 427571725 = 160339397) B160339397
theorem B3332623 : Blo 1315976 3332623 := bstep (se 1 (by rfl) ⟨2499467, by rfl⟩ : syracuseStep 3332623 = 4998935) B4998935
theorem B1317391 : Blo 1315976 1317391 := bstep (se 1 (by rfl) ⟨988043, by rfl⟩ : syracuseStep 1317391 = 1976087) B1976087
theorem B1317435 : Blo 1315976 1317435 := bstep (se 1 (by rfl) ⟨988076, by rfl⟩ : syracuseStep 1317435 = 1976153) B1976153
theorem B1317511 : Blo 1315976 1317511 := bstep (se 1 (by rfl) ⟨988133, by rfl⟩ : syracuseStep 1317511 = 1976267) B1976267
theorem B1481359 : Blo 1315976 1481359 := bstep (se 1 (by rfl) ⟨1111019, by rfl⟩ : syracuseStep 1481359 = 2222039) B2222039
theorem B1317519 : Blo 1315976 1317519 := bstep (se 1 (by rfl) ⟨988139, by rfl⟩ : syracuseStep 1317519 = 1976279) B1976279
theorem B1317563 : Blo 1315976 1317563 := bstep (se 1 (by rfl) ⟨988172, by rfl⟩ : syracuseStep 1317563 = 1976345) B1976345
theorem B5003977 : Blo 1315976 5003977 := bstep (se 2 (by rfl) ⟨1876491, by rfl⟩ : syracuseStep 5003977 = 3752983) B3752983
theorem B9009893 : Blo 1315976 9009893 := bstep (se 4 (by rfl) ⟨844677, by rfl⟩ : syracuseStep 9009893 = 1689355) B1689355
theorem B1317639 : Blo 1315976 1317639 := bstep (se 1 (by rfl) ⟨988229, by rfl⟩ : syracuseStep 1317639 = 1976459) B1976459
theorem B2964239 : Blo 1315976 2964239 := bstep (se 1 (by rfl) ⟨2223179, by rfl⟩ : syracuseStep 2964239 = 4446359) B4446359
theorem B1317647 : Blo 1315976 1317647 := bstep (se 1 (by rfl) ⟨988235, by rfl⟩ : syracuseStep 1317647 = 1976471) B1976471
theorem B3332897 : Blo 1315976 3332897 := bstep (se 2 (by rfl) ⟨1249836, by rfl⟩ : syracuseStep 3332897 = 2499673) B2499673
theorem B2964257 : Blo 1315976 2964257 := bstep (se 2 (by rfl) ⟨1111596, by rfl⟩ : syracuseStep 2964257 = 2223193) B2223193
theorem B1317691 : Blo 1315976 1317691 := bstep (se 1 (by rfl) ⟨988268, by rfl⟩ : syracuseStep 1317691 = 1976537) B1976537
theorem B1317767 : Blo 1315976 1317767 := bstep (se 1 (by rfl) ⟨988325, by rfl⟩ : syracuseStep 1317767 = 1976651) B1976651
theorem B1317775 : Blo 1315976 1317775 := bstep (se 1 (by rfl) ⟨988331, by rfl⟩ : syracuseStep 1317775 = 1976663) B1976663
theorem B3562393 : Blo 1315976 3562393 := bstep (se 2 (by rfl) ⟨1335897, by rfl⟩ : syracuseStep 3562393 = 2671795) B2671795
theorem B7502777 : Blo 1315976 7502777 := bstep (se 2 (by rfl) ⟨2813541, by rfl⟩ : syracuseStep 7502777 = 5627083) B5627083
theorem B1317819 : Blo 1315976 1317819 := bstep (se 1 (by rfl) ⟨988364, by rfl⟩ : syracuseStep 1317819 = 1976729) B1976729
theorem B1317895 : Blo 1315976 1317895 := bstep (se 1 (by rfl) ⟨988421, by rfl⟩ : syracuseStep 1317895 = 1976843) B1976843
theorem B1317903 : Blo 1315976 1317903 := bstep (se 1 (by rfl) ⟨988427, by rfl⟩ : syracuseStep 1317903 = 1976855) B1976855
theorem B1317947 : Blo 1315976 1317947 := bstep (se 1 (by rfl) ⟨988460, by rfl⟩ : syracuseStep 1317947 = 1976921) B1976921
theorem B14425175 : Blo 1315976 14425175 := bstep (se 1 (by rfl) ⟨10818881, by rfl⟩ : syracuseStep 14425175 = 21637763) B21637763
theorem B2964599 : Blo 1315976 2964599 := bstep (se 1 (by rfl) ⟨2223449, by rfl⟩ : syracuseStep 2964599 = 4446899) B4446899
theorem B1875079 : Blo 1315976 1875079 := bstep (se 1 (by rfl) ⟨1406309, by rfl⟩ : syracuseStep 1875079 = 2812619) B2812619
theorem B1481863 : Blo 1315976 1481863 := bstep (se 1 (by rfl) ⟨1111397, by rfl⟩ : syracuseStep 1481863 = 2222795) B2222795
theorem B2964779 : Blo 1315976 2964779 := bstep (se 1 (by rfl) ⟨2223584, by rfl⟩ : syracuseStep 2964779 = 4447169) B4447169
theorem B6331699 : Blo 1315976 6331699 := bstep (se 1 (by rfl) ⟨4748774, by rfl⟩ : syracuseStep 6331699 = 9497549) B9497549
theorem B1482043 : Blo 1315976 1482043 := bstep (se 1 (by rfl) ⟨1111532, by rfl⟩ : syracuseStep 1482043 = 2223065) B2223065
theorem B4447547 : Blo 1315976 4447547 := bstep (se 1 (by rfl) ⟨3335660, by rfl⟩ : syracuseStep 4447547 = 6671321) B6671321
theorem B9993617 : Blo 1315976 9993617 := bstep (se 2 (by rfl) ⟨3747606, by rfl⟩ : syracuseStep 9993617 = 7495213) B7495213
theorem B16014851 : Blo 1315976 16014851 := bstep (se 1 (by rfl) ⟨12011138, by rfl⟩ : syracuseStep 16014851 = 24022277) B24022277
theorem B1875575 : Blo 1315976 1875575 := bstep (se 1 (by rfl) ⟨1406681, by rfl⟩ : syracuseStep 1875575 = 2813363) B2813363
theorem B3751571 : Blo 1315976 3751571 := bstep (se 1 (by rfl) ⟨2813678, by rfl⟩ : syracuseStep 3751571 = 5627357) B5627357
theorem B2965139 : Blo 1315976 2965139 := bstep (se 1 (by rfl) ⟨2223854, by rfl⟩ : syracuseStep 2965139 = 4447709) B4447709
theorem B2965193 : Blo 1315976 2965193 := bstep (se 2 (by rfl) ⟨1111947, by rfl⟩ : syracuseStep 2965193 = 2223895) B2223895
theorem B1974023 : Blo 1315976 1974023 := bstep (se 1 (by rfl) ⟨1480517, by rfl⟩ : syracuseStep 1974023 = 2961035) B2961035
theorem B3333899 : Blo 1315976 3333899 := bstep (se 1 (by rfl) ⟨2500424, by rfl⟩ : syracuseStep 3333899 = 5000849) B5000849
theorem B1482511 : Blo 1315976 1482511 := bstep (se 1 (by rfl) ⟨1111883, by rfl⟩ : syracuseStep 1482511 = 2223767) B2223767
theorem B4448033 : Blo 1315976 4448033 := bstep (se 2 (by rfl) ⟨1668012, by rfl⟩ : syracuseStep 4448033 = 3336025) B3336025
theorem B1974059 : Blo 1315976 1974059 := bstep (se 1 (by rfl) ⟨1480544, by rfl⟩ : syracuseStep 1974059 = 2961089) B2961089
theorem B17342257 : Blo 1315976 17342257 := bstep (se 2 (by rfl) ⟨6503346, by rfl⟩ : syracuseStep 17342257 = 13006693) B13006693
theorem B14991155 : Blo 1315976 14991155 := bstep (se 1 (by rfl) ⟨11243366, by rfl⟩ : syracuseStep 14991155 = 22486733) B22486733
theorem B24035123 : Blo 1315976 24035123 := bstep (se 1 (by rfl) ⟨18026342, by rfl⟩ : syracuseStep 24035123 = 36052685) B36052685
theorem B1974089 : Blo 1315976 1974089 := bstep (se 2 (by rfl) ⟨740283, by rfl⟩ : syracuseStep 1974089 = 1480567) B1480567
theorem B9494435 : Blo 1315976 9494435 := bstep (se 1 (by rfl) ⟨7120826, by rfl⟩ : syracuseStep 9494435 = 14241653) B14241653
theorem B1974203 : Blo 1315976 1974203 := bstep (se 1 (by rfl) ⟨1480652, by rfl⟩ : syracuseStep 1974203 = 2961305) B2961305
theorem B1974263 : Blo 1315976 1974263 := bstep (se 1 (by rfl) ⟨1480697, by rfl⟩ : syracuseStep 1974263 = 2961395) B2961395
theorem B1974281 : Blo 1315976 1974281 := bstep (se 2 (by rfl) ⟨740355, by rfl⟩ : syracuseStep 1974281 = 1480711) B1480711
theorem B1974311 : Blo 1315976 1974311 := bstep (se 1 (by rfl) ⟨1480733, by rfl⟩ : syracuseStep 1974311 = 2961467) B2961467
theorem B6324281 : Blo 1315976 6324281 := bstep (se 2 (by rfl) ⟨2371605, by rfl⟩ : syracuseStep 6324281 = 4743211) B4743211
theorem B2498617 : Blo 1315976 2498617 := bstep (se 2 (by rfl) ⟨936981, by rfl⟩ : syracuseStep 2498617 = 1873963) B1873963
theorem B3334223 : Blo 1315976 3334223 := bstep (se 1 (by rfl) ⟨2500667, by rfl⟩ : syracuseStep 3334223 = 5001335) B5001335
theorem B7503961 : Blo 1315976 7503961 := bstep (se 2 (by rfl) ⟨2813985, by rfl⟩ : syracuseStep 7503961 = 5627971) B5627971
theorem B1974395 : Blo 1315976 1974395 := bstep (se 1 (by rfl) ⟨1480796, by rfl⟩ : syracuseStep 1974395 = 2961593) B2961593
theorem B1974521 : Blo 1315976 1974521 := bstep (se 2 (by rfl) ⟨740445, by rfl⟩ : syracuseStep 1974521 = 1480891) B1480891
theorem B15212875 : Blo 1315976 15212875 := bstep (se 1 (by rfl) ⟨11409656, by rfl⟩ : syracuseStep 15212875 = 22819313) B22819313
theorem B1974623 : Blo 1315976 1974623 := bstep (se 1 (by rfl) ⟨1480967, by rfl⟩ : syracuseStep 1974623 = 2961935) B2961935
theorem B2498921 : Blo 1315976 2498921 := bstep (se 2 (by rfl) ⟨937095, by rfl⟩ : syracuseStep 2498921 = 1874191) B1874191
theorem B2195819 : Blo 1315976 2195819 := bstep (se 1 (by rfl) ⟨1646864, by rfl⟩ : syracuseStep 2195819 = 3293729) B3293729
theorem B1974635 : Blo 1315976 1974635 := bstep (se 1 (by rfl) ⟨1480976, by rfl⟩ : syracuseStep 1974635 = 2961953) B2961953
theorem B1974863 : Blo 1315976 1974863 := bstep (se 1 (by rfl) ⟨1481147, by rfl⟩ : syracuseStep 1974863 = 2962295) B2962295
theorem B73032311 : Blo 1315976 73032311 := bstep (se 1 (by rfl) ⟨54774233, by rfl⟩ : syracuseStep 73032311 = 109548467) B109548467
theorem B2220743 : Blo 1315976 2220743 := bstep (se 1 (by rfl) ⟨1665557, by rfl⟩ : syracuseStep 2220743 = 3331115) B3331115
theorem B4809415 : Blo 1315976 4809415 := bstep (se 1 (by rfl) ⟨3607061, by rfl⟩ : syracuseStep 4809415 = 7214123) B7214123
theorem B1974983 : Blo 1315976 1974983 := bstep (se 1 (by rfl) ⟨1481237, by rfl⟩ : syracuseStep 1974983 = 2962475) B2962475
theorem B3334871 : Blo 1315976 3334871 := bstep (se 1 (by rfl) ⟨2501153, by rfl⟩ : syracuseStep 3334871 = 5002307) B5002307
theorem B2220905 : Blo 1315976 2220905 := bstep (se 2 (by rfl) ⟨832839, by rfl⟩ : syracuseStep 2220905 = 1665679) B1665679
theorem B1975145 : Blo 1315976 1975145 := bstep (se 2 (by rfl) ⟨740679, by rfl⟩ : syracuseStep 1975145 = 1481359) B1481359
theorem B3163063 : Blo 1315976 3163063 := bstep (se 1 (by rfl) ⟨2372297, by rfl⟩ : syracuseStep 3163063 = 4744595) B4744595
theorem B1975223 : Blo 1315976 1975223 := bstep (se 1 (by rfl) ⟨1481417, by rfl⟩ : syracuseStep 1975223 = 2962835) B2962835
theorem B1975259 : Blo 1315976 1975259 := bstep (se 1 (by rfl) ⟨1481444, by rfl⟩ : syracuseStep 1975259 = 2962889) B2962889
theorem B4998145 : Blo 1315976 4998145 := bstep (se 2 (by rfl) ⟨1874304, by rfl⟩ : syracuseStep 4998145 = 3748609) B3748609
theorem B2221303 : Blo 1315976 2221303 := bstep (se 1 (by rfl) ⟨1665977, by rfl⟩ : syracuseStep 2221303 = 3331955) B3331955
theorem B1975727 : Blo 1315976 1975727 := bstep (se 1 (by rfl) ⟨1481795, by rfl⟩ : syracuseStep 1975727 = 2963591) B2963591
theorem B2221499 : Blo 1315976 2221499 := bstep (se 1 (by rfl) ⟨1666124, by rfl⟩ : syracuseStep 2221499 = 3332249) B3332249
theorem B1975817 : Blo 1315976 1975817 := bstep (se 2 (by rfl) ⟨740931, by rfl⟩ : syracuseStep 1975817 = 1481863) B1481863
theorem B2221607 : Blo 1315976 2221607 := bstep (se 1 (by rfl) ⟨1666205, by rfl⟩ : syracuseStep 2221607 = 3332411) B3332411
theorem B1975847 : Blo 1315976 1975847 := bstep (se 1 (by rfl) ⟨1481885, by rfl⟩ : syracuseStep 1975847 = 2963771) B2963771
theorem B6669863 : Blo 1315976 6669863 := bstep (se 1 (by rfl) ⟨5002397, by rfl⟩ : syracuseStep 6669863 = 10004795) B10004795
theorem B1975931 : Blo 1315976 1975931 := bstep (se 1 (by rfl) ⟨1481948, by rfl⟩ : syracuseStep 1975931 = 2963897) B2963897
theorem B4998905 : Blo 1315976 4998905 := bstep (se 2 (by rfl) ⟨1874589, by rfl⟩ : syracuseStep 4998905 = 3749179) B3749179
theorem B1976057 : Blo 1315976 1976057 := bstep (se 2 (by rfl) ⟨741021, by rfl⟩ : syracuseStep 1976057 = 1482043) B1482043
theorem B19253051 : Blo 1315976 19253051 := bstep (se 1 (by rfl) ⟨14439788, by rfl⟩ : syracuseStep 19253051 = 28879577) B28879577
theorem B2221897 : Blo 1315976 2221897 := bstep (se 2 (by rfl) ⟨833211, by rfl⟩ : syracuseStep 2221897 = 1666423) B1666423
theorem B1976159 : Blo 1315976 1976159 := bstep (se 1 (by rfl) ⟨1482119, by rfl⟩ : syracuseStep 1976159 = 2964239) B2964239
theorem B2221931 : Blo 1315976 2221931 := bstep (se 1 (by rfl) ⟨1666448, by rfl⟩ : syracuseStep 2221931 = 3332897) B3332897
theorem B1976171 : Blo 1315976 1976171 := bstep (se 1 (by rfl) ⟨1482128, by rfl⟩ : syracuseStep 1976171 = 2964257) B2964257
theorem B12838817 : Blo 1315976 12838817 := bstep (se 2 (by rfl) ⟨4814556, by rfl⟩ : syracuseStep 12838817 = 9629113) B9629113
theorem B4442039 : Blo 1315976 4442039 := bstep (se 1 (by rfl) ⟨3331529, by rfl⟩ : syracuseStep 4442039 = 6663059) B6663059
theorem B3377231 : Blo 1315976 3377231 := bstep (se 1 (by rfl) ⟨2532923, by rfl⟩ : syracuseStep 3377231 = 5065847) B5065847
theorem B1976399 : Blo 1315976 1976399 := bstep (se 1 (by rfl) ⟨1482299, by rfl⟩ : syracuseStep 1976399 = 2964599) B2964599
theorem B5343347 : Blo 1315976 5343347 := bstep (se 1 (by rfl) ⟨4007510, by rfl⟩ : syracuseStep 5343347 = 8015021) B8015021
theorem B1976519 : Blo 1315976 1976519 := bstep (se 1 (by rfl) ⟨1482389, by rfl⟩ : syracuseStep 1976519 = 2964779) B2964779
theorem B2222329 : Blo 1315976 2222329 := bstep (se 2 (by rfl) ⟨833373, by rfl⟩ : syracuseStep 2222329 = 1666747) B1666747
theorem B6662411 : Blo 1315976 6662411 := bstep (se 1 (by rfl) ⟨4996808, by rfl⟩ : syracuseStep 6662411 = 9993617) B9993617
theorem B10676567 : Blo 1315976 10676567 := bstep (se 1 (by rfl) ⟨8007425, by rfl⟩ : syracuseStep 10676567 = 16014851) B16014851
theorem B9013609 : Blo 1315976 9013609 := bstep (se 2 (by rfl) ⟨3380103, by rfl⟩ : syracuseStep 9013609 = 6760207) B6760207
theorem B1976681 : Blo 1315976 1976681 := bstep (se 2 (by rfl) ⟨741255, by rfl⟩ : syracuseStep 1976681 = 1482511) B1482511
theorem B2501047 : Blo 1315976 2501047 := bstep (se 1 (by rfl) ⟨1875785, by rfl⟩ : syracuseStep 2501047 = 3751571) B3751571
theorem B1976759 : Blo 1315976 1976759 := bstep (se 1 (by rfl) ⟨1482569, by rfl⟩ : syracuseStep 1976759 = 2965139) B2965139
theorem B1976795 : Blo 1315976 1976795 := bstep (se 1 (by rfl) ⟨1482596, by rfl⟩ : syracuseStep 1976795 = 2965193) B2965193
theorem B2222599 : Blo 1315976 2222599 := bstep (se 1 (by rfl) ⟨1666949, by rfl⟩ : syracuseStep 2222599 = 3333899) B3333899
theorem B4442633 : Blo 1315976 4442633 := bstep (se 2 (by rfl) ⟨1665987, by rfl⟩ : syracuseStep 4442633 = 3331975) B3331975
theorem B16017965 : Blo 1315976 16017965 := bstep (se 3 (by rfl) ⟨3003368, by rfl⟩ : syracuseStep 16017965 = 6006737) B6006737
theorem B42740405 : Blo 1315976 42740405 := bstep (se 5 (by rfl) ⟨2003456, by rfl⟩ : syracuseStep 42740405 = 4006913) B4006913
theorem B1780423 : Blo 1315976 1780423 := bstep (se 1 (by rfl) ⟨1335317, by rfl⟩ : syracuseStep 1780423 = 2670635) B2670635
theorem B4746167 : Blo 1315976 4746167 := bstep (se 1 (by rfl) ⟨3559625, by rfl⟩ : syracuseStep 4746167 = 7119251) B7119251
theorem B2223031 : Blo 1315976 2223031 := bstep (se 1 (by rfl) ⟨1667273, by rfl⟩ : syracuseStep 2223031 = 3334547) B3334547
theorem B6761399 : Blo 1315976 6761399 := bstep (se 1 (by rfl) ⟨5071049, by rfl⟩ : syracuseStep 6761399 = 10142099) B10142099
theorem B4221953 : Blo 1315976 4221953 := bstep (se 2 (by rfl) ⟨1583232, by rfl⟩ : syracuseStep 4221953 = 3166465) B3166465
theorem B9620531 : Blo 1315976 9620531 := bstep (se 1 (by rfl) ⟨7215398, by rfl⟩ : syracuseStep 9620531 = 14430797) B14430797
theorem B8432707 : Blo 1315976 8432707 := bstep (se 1 (by rfl) ⟨6324530, by rfl⟩ : syracuseStep 8432707 = 12649061) B12649061
theorem B2223227 : Blo 1315976 2223227 := bstep (se 1 (by rfl) ⟨1667420, by rfl⟩ : syracuseStep 2223227 = 3334841) B3334841
theorem B2108587 : Blo 1315976 2108587 := bstep (se 1 (by rfl) ⟨1581440, by rfl⟩ : syracuseStep 2108587 = 3162881) B3162881
theorem B5000363 : Blo 1315976 5000363 := bstep (se 1 (by rfl) ⟨3750272, by rfl⟩ : syracuseStep 5000363 = 7500545) B7500545
theorem B12651713 : Blo 1315976 12651713 := bstep (se 2 (by rfl) ⟨4744392, by rfl⟩ : syracuseStep 12651713 = 9488785) B9488785
theorem B9997505 : Blo 1315976 9997505 := bstep (se 2 (by rfl) ⟨3749064, by rfl⟩ : syracuseStep 9997505 = 7498129) B7498129
theorem B15002819 : Blo 1315976 15002819 := bstep (se 1 (by rfl) ⟨11252114, by rfl⟩ : syracuseStep 15002819 = 22504229) B22504229
theorem B1780985 : Blo 1315976 1780985 := bstep (se 2 (by rfl) ⟨667869, by rfl⟩ : syracuseStep 1780985 = 1335739) B1335739
theorem B4443497 : Blo 1315976 4443497 := bstep (se 2 (by rfl) ⟨1666311, by rfl⟩ : syracuseStep 4443497 = 3332623) B3332623
theorem B2223625 : Blo 1315976 2223625 := bstep (se 2 (by rfl) ⟨833859, by rfl⟩ : syracuseStep 2223625 = 1667719) B1667719
theorem B6671969 : Blo 1315976 6671969 := bstep (se 2 (by rfl) ⟨2501988, by rfl⟩ : syracuseStep 6671969 = 5003977) B5003977
theorem B2223787 : Blo 1315976 2223787 := bstep (se 1 (by rfl) ⟨1667840, by rfl⟩ : syracuseStep 2223787 = 3335681) B3335681
theorem B6663869 : Blo 1315976 6663869 := bstep (se 3 (by rfl) ⟨1249475, by rfl⟩ : syracuseStep 6663869 = 2498951) B2498951
theorem B3747539 : Blo 1315976 3747539 := bstep (se 1 (by rfl) ⟨2810654, by rfl⟩ : syracuseStep 3747539 = 5621309) B5621309
theorem B2961107 : Blo 1315976 2961107 := bstep (se 1 (by rfl) ⟨2220830, by rfl⟩ : syracuseStep 2961107 = 4441661) B4441661
theorem B6754013 : Blo 1315976 6754013 := bstep (se 3 (by rfl) ⟨1266377, by rfl⟩ : syracuseStep 6754013 = 2532755) B2532755
theorem B10006253 : Blo 1315976 10006253 := bstep (se 3 (by rfl) ⟨1876172, by rfl⟩ : syracuseStep 10006253 = 3752345) B3752345
theorem B7499587 : Blo 1315976 7499587 := bstep (se 1 (by rfl) ⟨5624690, by rfl⟩ : syracuseStep 7499587 = 11249381) B11249381
theorem B6664031 : Blo 1315976 6664031 := bstep (se 1 (by rfl) ⟨4998023, by rfl⟩ : syracuseStep 6664031 = 9996047) B9996047
theorem B5140331 : Blo 1315976 5140331 := bstep (se 1 (by rfl) ⟨3855248, by rfl⟩ : syracuseStep 5140331 = 7710497) B7710497
theorem B19246967 : Blo 1315976 19246967 := bstep (se 1 (by rfl) ⟨14435225, by rfl⟩ : syracuseStep 19246967 = 28870451) B28870451
theorem B4444091 : Blo 1315976 4444091 := bstep (se 1 (by rfl) ⟨3333068, by rfl⟩ : syracuseStep 4444091 = 6666137) B6666137
theorem B5066831 : Blo 1315976 5066831 := bstep (se 1 (by rfl) ⟨3800123, by rfl⟩ : syracuseStep 5066831 = 7600247) B7600247
theorem B8122457 : Blo 1315976 8122457 := bstep (se 2 (by rfl) ⟨3045921, by rfl⟩ : syracuseStep 8122457 = 6091843) B6091843
theorem B11251979 : Blo 1315976 11251979 := bstep (se 1 (by rfl) ⟨8438984, by rfl⟩ : syracuseStep 11251979 = 16877969) B16877969
theorem B21344573 : Blo 1315976 21344573 := bstep (se 3 (by rfl) ⟨4002107, by rfl⟩ : syracuseStep 21344573 = 8004215) B8004215
theorem B5001533 : Blo 1315976 5001533 := bstep (se 3 (by rfl) ⟨937787, by rfl⟩ : syracuseStep 5001533 = 1875575) B1875575
theorem B8442265 : Blo 1315976 8442265 := bstep (se 2 (by rfl) ⟨3165849, by rfl⟩ : syracuseStep 8442265 = 6331699) B6331699
theorem B1667623 : Blo 1315976 1667623 := bstep (se 1 (by rfl) ⟨1250717, by rfl⟩ : syracuseStep 1667623 = 2501435) B2501435
theorem B18985589 : Blo 1315976 18985589 := bstep (se 5 (by rfl) ⟨889949, by rfl⟩ : syracuseStep 18985589 = 1779899) B1779899
theorem B15004277 : Blo 1315976 15004277 := bstep (se 5 (by rfl) ⟨703325, by rfl⟩ : syracuseStep 15004277 = 1406651) B1406651
theorem B2962043 : Blo 1315976 2962043 := bstep (se 1 (by rfl) ⟨2221532, by rfl⟩ : syracuseStep 2962043 = 4443065) B4443065
theorem B5001851 : Blo 1315976 5001851 := bstep (se 1 (by rfl) ⟨3751388, by rfl⟩ : syracuseStep 5001851 = 7502777) B7502777
theorem B10007225 : Blo 1315976 10007225 := bstep (se 2 (by rfl) ⟨3752709, by rfl⟩ : syracuseStep 10007225 = 7505419) B7505419
theorem B2962169 : Blo 1315976 2962169 := bstep (se 2 (by rfl) ⟨1110813, by rfl⟩ : syracuseStep 2962169 = 2221627) B2221627
theorem B34231045 : Blo 1315976 34231045 := bstep (se 4 (by rfl) ⟨3209160, by rfl⟩ : syracuseStep 34231045 = 6418321) B6418321
theorem B1667947 : Blo 1315976 1667947 := bstep (se 1 (by rfl) ⟨1250960, by rfl⟩ : syracuseStep 1667947 = 2501921) B2501921
theorem B2962439 : Blo 1315976 2962439 := bstep (se 1 (by rfl) ⟨2221829, by rfl⟩ : syracuseStep 2962439 = 4443659) B4443659
theorem B23123009 : Blo 1315976 23123009 := bstep (se 2 (by rfl) ⟨8671128, by rfl⟩ : syracuseStep 23123009 = 17342257) B17342257
theorem B2962511 : Blo 1315976 2962511 := bstep (se 1 (by rfl) ⟨2221883, by rfl⟩ : syracuseStep 2962511 = 4443767) B4443767
theorem B51328171 : Blo 1315976 51328171 := bstep (se 1 (by rfl) ⟨38496128, by rfl⟩ : syracuseStep 51328171 = 76992257) B76992257
theorem B1316015 : Blo 1315976 1316015 := bstep (se 1 (by rfl) ⟨987011, by rfl⟩ : syracuseStep 1316015 = 1974023) B1974023
theorem B1316039 : Blo 1315976 1316039 := bstep (se 1 (by rfl) ⟨987029, by rfl⟩ : syracuseStep 1316039 = 1974059) B1974059
theorem B1316059 : Blo 1315976 1316059 := bstep (se 1 (by rfl) ⟨987044, by rfl⟩ : syracuseStep 1316059 = 1974089) B1974089
theorem B3749111 : Blo 1315976 3749111 := bstep (se 1 (by rfl) ⟨2811833, by rfl⟩ : syracuseStep 3749111 = 5623667) B5623667
theorem B6329623 : Blo 1315976 6329623 := bstep (se 1 (by rfl) ⟨4747217, by rfl⟩ : syracuseStep 6329623 = 9494435) B9494435
theorem B1316135 : Blo 1315976 1316135 := bstep (se 1 (by rfl) ⟨987101, by rfl⟩ : syracuseStep 1316135 = 1974203) B1974203
theorem B1316175 : Blo 1315976 1316175 := bstep (se 1 (by rfl) ⟨987131, by rfl⟩ : syracuseStep 1316175 = 1974263) B1974263
theorem B1316191 : Blo 1315976 1316191 := bstep (se 1 (by rfl) ⟨987143, by rfl⟩ : syracuseStep 1316191 = 1974287) B1974287
theorem B1316219 : Blo 1315976 1316219 := bstep (se 1 (by rfl) ⟨987164, by rfl⟩ : syracuseStep 1316219 = 1974329) B1974329
theorem B9008549 : Blo 1315976 9008549 := bstep (se 4 (by rfl) ⟨844551, by rfl⟩ : syracuseStep 9008549 = 1689103) B1689103
theorem B12015013 : Blo 1315976 12015013 := bstep (se 4 (by rfl) ⟨1126407, by rfl⟩ : syracuseStep 12015013 = 2252815) B2252815
theorem B1316271 : Blo 1315976 1316271 := bstep (se 1 (by rfl) ⟨987203, by rfl⟩ : syracuseStep 1316271 = 1974407) B1974407
theorem B1316295 : Blo 1315976 1316295 := bstep (se 1 (by rfl) ⟨987221, by rfl⟩ : syracuseStep 1316295 = 1974443) B1974443
theorem B1316315 : Blo 1315976 1316315 := bstep (se 1 (by rfl) ⟨987236, by rfl⟩ : syracuseStep 1316315 = 1974473) B1974473
theorem B2962907 : Blo 1315976 2962907 := bstep (se 1 (by rfl) ⟨2222180, by rfl⟩ : syracuseStep 2962907 = 4444361) B4444361
theorem B1316391 : Blo 1315976 1316391 := bstep (se 1 (by rfl) ⟨987293, by rfl⟩ : syracuseStep 1316391 = 1974587) B1974587
theorem B38467133 : Blo 1315976 38467133 := bstep (se 3 (by rfl) ⟨7212587, by rfl⟩ : syracuseStep 38467133 = 14425175) B14425175
theorem B1316431 : Blo 1315976 1316431 := bstep (se 1 (by rfl) ⟨987323, by rfl⟩ : syracuseStep 1316431 = 1974647) B1974647
theorem B1316447 : Blo 1315976 1316447 := bstep (se 1 (by rfl) ⟨987335, by rfl⟩ : syracuseStep 1316447 = 1974671) B1974671
theorem B1316475 : Blo 1315976 1316475 := bstep (se 1 (by rfl) ⟨987356, by rfl⟩ : syracuseStep 1316475 = 1974713) B1974713
theorem B4445819 : Blo 1315976 4445819 := bstep (se 1 (by rfl) ⟨3334364, by rfl⟩ : syracuseStep 4445819 = 6668729) B6668729
theorem B10679941 : Blo 1315976 10679941 := bstep (se 4 (by rfl) ⟨1001244, by rfl⟩ : syracuseStep 10679941 = 2002489) B2002489
theorem B10008197 : Blo 1315976 10008197 := bstep (se 4 (by rfl) ⟨938268, by rfl⟩ : syracuseStep 10008197 = 1876537) B1876537
theorem B1316527 : Blo 1315976 1316527 := bstep (se 1 (by rfl) ⟨987395, by rfl⟩ : syracuseStep 1316527 = 1974791) B1974791
theorem B1316551 : Blo 1315976 1316551 := bstep (se 1 (by rfl) ⟨987413, by rfl⟩ : syracuseStep 1316551 = 1974827) B1974827
theorem B1316571 : Blo 1315976 1316571 := bstep (se 1 (by rfl) ⟨987428, by rfl⟩ : syracuseStep 1316571 = 1974857) B1974857
theorem B4445981 : Blo 1315976 4445981 := bstep (se 3 (by rfl) ⟨833621, by rfl⟩ : syracuseStep 4445981 = 1667243) B1667243
theorem B1316647 : Blo 1315976 1316647 := bstep (se 1 (by rfl) ⟨987485, by rfl⟩ : syracuseStep 1316647 = 1974971) B1974971
theorem B1316687 : Blo 1315976 1316687 := bstep (se 1 (by rfl) ⟨987515, by rfl⟩ : syracuseStep 1316687 = 1975031) B1975031
theorem B1316703 : Blo 1315976 1316703 := bstep (se 1 (by rfl) ⟨987527, by rfl⟩ : syracuseStep 1316703 = 1975055) B1975055
theorem B1316731 : Blo 1315976 1316731 := bstep (se 1 (by rfl) ⟨987548, by rfl⟩ : syracuseStep 1316731 = 1975097) B1975097
theorem B1316783 : Blo 1315976 1316783 := bstep (se 1 (by rfl) ⟨987587, by rfl⟩ : syracuseStep 1316783 = 1975175) B1975175
theorem B2963375 : Blo 1315976 2963375 := bstep (se 1 (by rfl) ⟨2222531, by rfl⟩ : syracuseStep 2963375 = 4445063) B4445063
theorem B1316807 : Blo 1315976 1316807 := bstep (se 1 (by rfl) ⟨987605, by rfl⟩ : syracuseStep 1316807 = 1975211) B1975211
theorem B1316827 : Blo 1315976 1316827 := bstep (se 1 (by rfl) ⟨987620, by rfl⟩ : syracuseStep 1316827 = 1975241) B1975241
theorem B5003279 : Blo 1315976 5003279 := bstep (se 1 (by rfl) ⟨3752459, by rfl⟩ : syracuseStep 5003279 = 7504919) B7504919
theorem B570095633 : Blo 1315976 570095633 := bstep (se 2 (by rfl) ⟨213785862, by rfl⟩ : syracuseStep 570095633 = 427571725) B427571725
theorem B10000421 : Blo 1315976 10000421 := bstep (se 4 (by rfl) ⟨937539, by rfl⟩ : syracuseStep 10000421 = 1875079) B1875079
theorem B8009765 : Blo 1315976 8009765 := bstep (se 4 (by rfl) ⟨750915, by rfl⟩ : syracuseStep 8009765 = 1501831) B1501831
theorem B1316903 : Blo 1315976 1316903 := bstep (se 1 (by rfl) ⟨987677, by rfl⟩ : syracuseStep 1316903 = 1975355) B1975355
theorem B1480783 : Blo 1315976 1480783 := bstep (se 1 (by rfl) ⟨1110587, by rfl⟩ : syracuseStep 1480783 = 2221175) B2221175
theorem B1316943 : Blo 1315976 1316943 := bstep (se 1 (by rfl) ⟨987707, by rfl⟩ : syracuseStep 1316943 = 1975415) B1975415
theorem B1316959 : Blo 1315976 1316959 := bstep (se 1 (by rfl) ⟨987719, by rfl⟩ : syracuseStep 1316959 = 1975439) B1975439
theorem B1316987 : Blo 1315976 1316987 := bstep (se 1 (by rfl) ⟨987740, by rfl⟩ : syracuseStep 1316987 = 1975481) B1975481
theorem B2963627 : Blo 1315976 2963627 := bstep (se 1 (by rfl) ⟨2222720, by rfl⟩ : syracuseStep 2963627 = 4445441) B4445441
theorem B1317039 : Blo 1315976 1317039 := bstep (se 1 (by rfl) ⟨987779, by rfl⟩ : syracuseStep 1317039 = 1975559) B1975559
theorem B1317063 : Blo 1315976 1317063 := bstep (se 1 (by rfl) ⟨987797, by rfl⟩ : syracuseStep 1317063 = 1975595) B1975595
theorem B1317083 : Blo 1315976 1317083 := bstep (se 1 (by rfl) ⟨987812, by rfl⟩ : syracuseStep 1317083 = 1975625) B1975625
theorem B1317159 : Blo 1315976 1317159 := bstep (se 1 (by rfl) ⟨987869, by rfl⟩ : syracuseStep 1317159 = 1975739) B1975739
theorem B1317199 : Blo 1315976 1317199 := bstep (se 1 (by rfl) ⟨987899, by rfl⟩ : syracuseStep 1317199 = 1975799) B1975799
theorem B1317215 : Blo 1315976 1317215 := bstep (se 1 (by rfl) ⟨987911, by rfl⟩ : syracuseStep 1317215 = 1975823) B1975823
theorem B1317243 : Blo 1315976 1317243 := bstep (se 1 (by rfl) ⟨987932, by rfl⟩ : syracuseStep 1317243 = 1975865) B1975865
theorem B1317295 : Blo 1315976 1317295 := bstep (se 1 (by rfl) ⟨987971, by rfl⟩ : syracuseStep 1317295 = 1975943) B1975943
theorem B1317319 : Blo 1315976 1317319 := bstep (se 1 (by rfl) ⟨987989, by rfl⟩ : syracuseStep 1317319 = 1975979) B1975979
theorem B1481179 : Blo 1315976 1481179 := bstep (se 1 (by rfl) ⟨1110884, by rfl⟩ : syracuseStep 1481179 = 2221769) B2221769
theorem B1317339 : Blo 1315976 1317339 := bstep (se 1 (by rfl) ⟨988004, by rfl⟩ : syracuseStep 1317339 = 1976009) B1976009
theorem B4446683 : Blo 1315976 4446683 := bstep (se 1 (by rfl) ⟨3335012, by rfl⟩ : syracuseStep 4446683 = 6670025) B6670025
theorem B6666785 : Blo 1315976 6666785 := bstep (se 2 (by rfl) ⟨2500044, by rfl⟩ : syracuseStep 6666785 = 5000089) B5000089
theorem B4749857 : Blo 1315976 4749857 := bstep (se 2 (by rfl) ⟨1781196, by rfl⟩ : syracuseStep 4749857 = 3562393) B3562393
theorem B1317415 : Blo 1315976 1317415 := bstep (se 1 (by rfl) ⟨988061, by rfl⟩ : syracuseStep 1317415 = 1976123) B1976123
theorem B1317455 : Blo 1315976 1317455 := bstep (se 1 (by rfl) ⟨988091, by rfl⟩ : syracuseStep 1317455 = 1976183) B1976183
theorem B1317471 : Blo 1315976 1317471 := bstep (se 1 (by rfl) ⟨988103, by rfl⟩ : syracuseStep 1317471 = 1976207) B1976207
theorem B1317499 : Blo 1315976 1317499 := bstep (se 1 (by rfl) ⟨988124, by rfl⟩ : syracuseStep 1317499 = 1976249) B1976249
theorem B1317551 : Blo 1315976 1317551 := bstep (se 1 (by rfl) ⟨988163, by rfl⟩ : syracuseStep 1317551 = 1976327) B1976327
theorem B2964167 : Blo 1315976 2964167 := bstep (se 1 (by rfl) ⟨2223125, by rfl⟩ : syracuseStep 2964167 = 4446251) B4446251
theorem B1317575 : Blo 1315976 1317575 := bstep (se 1 (by rfl) ⟨988181, by rfl⟩ : syracuseStep 1317575 = 1976363) B1976363
theorem B1317595 : Blo 1315976 1317595 := bstep (se 1 (by rfl) ⟨988196, by rfl⟩ : syracuseStep 1317595 = 1976393) B1976393
theorem B1317671 : Blo 1315976 1317671 := bstep (se 1 (by rfl) ⟨988253, by rfl⟩ : syracuseStep 1317671 = 1976507) B1976507
theorem B1317711 : Blo 1315976 1317711 := bstep (se 1 (by rfl) ⟨988283, by rfl⟩ : syracuseStep 1317711 = 1976567) B1976567
theorem B1874783 : Blo 1315976 1874783 := bstep (se 1 (by rfl) ⟨1406087, by rfl⟩ : syracuseStep 1874783 = 2812175) B2812175
theorem B1317727 : Blo 1315976 1317727 := bstep (se 1 (by rfl) ⟨988295, by rfl⟩ : syracuseStep 1317727 = 1976591) B1976591
theorem B1317755 : Blo 1315976 1317755 := bstep (se 1 (by rfl) ⟨988316, by rfl⟩ : syracuseStep 1317755 = 1976633) B1976633
theorem B1874863 : Blo 1315976 1874863 := bstep (se 1 (by rfl) ⟨1406147, by rfl⟩ : syracuseStep 1874863 = 2812295) B2812295
theorem B1481647 : Blo 1315976 1481647 := bstep (se 1 (by rfl) ⟨1111235, by rfl⟩ : syracuseStep 1481647 = 2222471) B2222471
theorem B1317807 : Blo 1315976 1317807 := bstep (se 1 (by rfl) ⟨988355, by rfl⟩ : syracuseStep 1317807 = 1976711) B1976711
theorem B1317831 : Blo 1315976 1317831 := bstep (se 1 (by rfl) ⟨988373, by rfl⟩ : syracuseStep 1317831 = 1976747) B1976747
theorem B1317851 : Blo 1315976 1317851 := bstep (se 1 (by rfl) ⟨988388, by rfl⟩ : syracuseStep 1317851 = 1976777) B1976777
theorem B1874983 : Blo 1315976 1874983 := bstep (se 1 (by rfl) ⟨1406237, by rfl⟩ : syracuseStep 1874983 = 2812475) B2812475
theorem B1317927 : Blo 1315976 1317927 := bstep (se 1 (by rfl) ⟨988445, by rfl⟩ : syracuseStep 1317927 = 1976891) B1976891
theorem B1317967 : Blo 1315976 1317967 := bstep (se 1 (by rfl) ⟨988475, by rfl⟩ : syracuseStep 1317967 = 1976951) B1976951
theorem B4447385 : Blo 1315976 4447385 := bstep (se 2 (by rfl) ⟨1667769, by rfl⟩ : syracuseStep 4447385 = 3335539) B3335539
theorem B24026381 : Blo 1315976 24026381 := bstep (se 3 (by rfl) ⟨4504946, by rfl⟩ : syracuseStep 24026381 = 9009893) B9009893
theorem B1482079 : Blo 1315976 1482079 := bstep (se 1 (by rfl) ⟨1111559, by rfl⟩ : syracuseStep 1482079 = 2223119) B2223119
theorem B1875307 : Blo 1315976 1875307 := bstep (se 1 (by rfl) ⟨1406480, by rfl⟩ : syracuseStep 1875307 = 2812961) B2812961
theorem B48717233 : Blo 1315976 48717233 := bstep (se 2 (by rfl) ⟨18268962, by rfl⟩ : syracuseStep 48717233 = 36537925) B36537925
theorem B4218313 : Blo 1315976 4218313 := bstep (se 2 (by rfl) ⟨1581867, by rfl⟩ : syracuseStep 4218313 = 3163735) B3163735
theorem B3333595 : Blo 1315976 3333595 := bstep (se 1 (by rfl) ⟨2500196, by rfl⟩ : syracuseStep 3333595 = 5000393) B5000393
theorem B2965031 : Blo 1315976 2965031 := bstep (se 1 (by rfl) ⟨2223773, by rfl⟩ : syracuseStep 2965031 = 4447547) B4447547
theorem B1482439 : Blo 1315976 1482439 := bstep (se 1 (by rfl) ⟨1111829, by rfl⟩ : syracuseStep 1482439 = 2223659) B2223659
theorem B6323933 : Blo 1315976 6323933 := bstep (se 3 (by rfl) ⟨1185737, by rfl⟩ : syracuseStep 6323933 = 2371475) B2371475
theorem B3751753 : Blo 1315976 3751753 := bstep (se 2 (by rfl) ⟨1406907, by rfl⟩ : syracuseStep 3751753 = 2813815) B2813815
theorem B2965355 : Blo 1315976 2965355 := bstep (se 1 (by rfl) ⟨2224016, by rfl⟩ : syracuseStep 2965355 = 4448033) B4448033
theorem B9994103 : Blo 1315976 9994103 := bstep (se 1 (by rfl) ⟨7495577, by rfl⟩ : syracuseStep 9994103 = 14991155) B14991155
theorem B16023415 : Blo 1315976 16023415 := bstep (se 1 (by rfl) ⟨12017561, by rfl⟩ : syracuseStep 16023415 = 24035123) B24035123
theorem B2498465 : Blo 1315976 2498465 := bstep (se 2 (by rfl) ⟨936924, by rfl⟩ : syracuseStep 2498465 = 1873849) B1873849
theorem B2965409 : Blo 1315976 2965409 := bstep (se 2 (by rfl) ⟨1112028, by rfl⟩ : syracuseStep 2965409 = 2224057) B2224057
theorem B1974191 : Blo 1315976 1974191 := bstep (se 1 (by rfl) ⟨1480643, by rfl⟩ : syracuseStep 1974191 = 2961287) B2961287
theorem B5414971 : Blo 1315976 5414971 := bstep (se 1 (by rfl) ⟨4061228, by rfl⟩ : syracuseStep 5414971 = 8122457) B8122457
theorem B1974377 : Blo 1315976 1974377 := bstep (se 2 (by rfl) ⟨740391, by rfl⟩ : syracuseStep 1974377 = 1480783) B1480783
theorem B61661357 : Blo 1315976 61661357 := bstep (se 3 (by rfl) ⟨11561504, by rfl⟩ : syracuseStep 61661357 = 23123009) B23123009
theorem B3334355 : Blo 1315976 3334355 := bstep (se 1 (by rfl) ⟨2500766, by rfl⟩ : syracuseStep 3334355 = 5001533) B5001533
theorem B12657059 : Blo 1315976 12657059 := bstep (se 1 (by rfl) ⟨9492794, by rfl⟩ : syracuseStep 12657059 = 18985589) B18985589
theorem B10002851 : Blo 1315976 10002851 := bstep (se 1 (by rfl) ⟨7502138, by rfl⟩ : syracuseStep 10002851 = 15004277) B15004277
theorem B1974695 : Blo 1315976 1974695 := bstep (se 1 (by rfl) ⟨1481021, by rfl⟩ : syracuseStep 1974695 = 2962043) B2962043
theorem B3334567 : Blo 1315976 3334567 := bstep (se 1 (by rfl) ⟨2500925, by rfl⟩ : syracuseStep 3334567 = 5001851) B5001851
theorem B20283833 : Blo 1315976 20283833 := bstep (se 2 (by rfl) ⟨7606437, by rfl⟩ : syracuseStep 20283833 = 15212875) B15212875
theorem B12018145 : Blo 1315976 12018145 := bstep (se 2 (by rfl) ⟨4506804, by rfl⟩ : syracuseStep 12018145 = 9013609) B9013609
theorem B1974779 : Blo 1315976 1974779 := bstep (se 1 (by rfl) ⟨1481084, by rfl⟩ : syracuseStep 1974779 = 2962169) B2962169
theorem B11256353 : Blo 1315976 11256353 := bstep (se 2 (by rfl) ⟨4221132, by rfl⟩ : syracuseStep 11256353 = 8442265) B8442265
theorem B3334729 : Blo 1315976 3334729 := bstep (se 2 (by rfl) ⟨1250523, by rfl⟩ : syracuseStep 3334729 = 2501047) B2501047
theorem B1974905 : Blo 1315976 1974905 := bstep (se 2 (by rfl) ⟨740589, by rfl⟩ : syracuseStep 1974905 = 1481179) B1481179
theorem B1974959 : Blo 1315976 1974959 := bstep (se 1 (by rfl) ⟨1481219, by rfl⟩ : syracuseStep 1974959 = 2962439) B2962439
theorem B56959685 : Blo 1315976 56959685 := bstep (se 4 (by rfl) ⟨5339970, by rfl⟩ : syracuseStep 56959685 = 10679941) B10679941
theorem B1975007 : Blo 1315976 1975007 := bstep (se 1 (by rfl) ⟨1481255, by rfl⟩ : syracuseStep 1975007 = 2962511) B2962511
theorem B56918861 : Blo 1315976 56918861 := bstep (se 3 (by rfl) ⟨10672286, by rfl⟩ : syracuseStep 56918861 = 21344573) B21344573
theorem B2499407 : Blo 1315976 2499407 := bstep (se 1 (by rfl) ⟨1874555, by rfl⟩ : syracuseStep 2499407 = 3749111) B3749111
theorem B6005699 : Blo 1315976 6005699 := bstep (se 1 (by rfl) ⟨4504274, by rfl⟩ : syracuseStep 6005699 = 9008549) B9008549
theorem B1975271 : Blo 1315976 1975271 := bstep (se 1 (by rfl) ⟨1481453, by rfl⟩ : syracuseStep 1975271 = 2962907) B2962907
theorem B9495589 : Blo 1315976 9495589 := bstep (se 4 (by rfl) ⟨890211, by rfl⟩ : syracuseStep 9495589 = 1780423) B1780423
theorem B2499817 : Blo 1315976 2499817 := bstep (se 2 (by rfl) ⟨937431, by rfl⟩ : syracuseStep 2499817 = 1874863) B1874863
theorem B1975529 : Blo 1315976 1975529 := bstep (se 2 (by rfl) ⟨740823, by rfl⟩ : syracuseStep 1975529 = 1481647) B1481647
theorem B1975583 : Blo 1315976 1975583 := bstep (se 1 (by rfl) ⟨1481687, by rfl⟩ : syracuseStep 1975583 = 2963375) B2963375
theorem B3335519 : Blo 1315976 3335519 := bstep (se 1 (by rfl) ⟨2501639, by rfl⟩ : syracuseStep 3335519 = 5003279) B5003279
theorem B2499977 : Blo 1315976 2499977 := bstep (se 2 (by rfl) ⟨937491, by rfl⟩ : syracuseStep 2499977 = 1874983) B1874983
theorem B1975751 : Blo 1315976 1975751 := bstep (se 1 (by rfl) ⟨1481813, by rfl⟩ : syracuseStep 1975751 = 2963627) B2963627
theorem B4441607 : Blo 1315976 4441607 := bstep (se 1 (by rfl) ⟨3331205, by rfl⟩ : syracuseStep 4441607 = 6662411) B6662411
theorem B2811449 : Blo 1315976 2811449 := bstep (se 2 (by rfl) ⟨1054293, by rfl⟩ : syracuseStep 2811449 = 2108587) B2108587
theorem B68437561 : Blo 1315976 68437561 := bstep (se 2 (by rfl) ⟨25664085, by rfl⟩ : syracuseStep 68437561 = 51328171) B51328171
theorem B8439497 : Blo 1315976 8439497 := bstep (se 2 (by rfl) ⟨3164811, by rfl⟩ : syracuseStep 8439497 = 6329623) B6329623
theorem B28493603 : Blo 1315976 28493603 := bstep (se 1 (by rfl) ⟨21370202, by rfl⟩ : syracuseStep 28493603 = 42740405) B42740405
theorem B1976105 : Blo 1315976 1976105 := bstep (se 2 (by rfl) ⟨741039, by rfl⟩ : syracuseStep 1976105 = 1482079) B1482079
theorem B1976111 : Blo 1315976 1976111 := bstep (se 1 (by rfl) ⟨1482083, by rfl⟩ : syracuseStep 1976111 = 2964167) B2964167
theorem B2500409 : Blo 1315976 2500409 := bstep (se 2 (by rfl) ⟨937653, by rfl⟩ : syracuseStep 2500409 = 1875307) B1875307
theorem B3164111 : Blo 1315976 3164111 := bstep (se 1 (by rfl) ⟨2373083, by rfl⟩ : syracuseStep 3164111 = 4746167) B4746167
theorem B16017587 : Blo 1315976 16017587 := bstep (se 1 (by rfl) ⟨12013190, by rfl⟩ : syracuseStep 16017587 = 24026381) B24026381
theorem B4999421 : Blo 1315976 4999421 := bstep (se 3 (by rfl) ⟨937391, by rfl⟩ : syracuseStep 4999421 = 1874783) B1874783
theorem B1976585 : Blo 1315976 1976585 := bstep (se 2 (by rfl) ⟨741219, by rfl⟩ : syracuseStep 1976585 = 1482439) B1482439
theorem B1976687 : Blo 1315976 1976687 := bstep (se 1 (by rfl) ⟨1482515, by rfl⟩ : syracuseStep 1976687 = 2965031) B2965031
theorem B6662573 : Blo 1315976 6662573 := bstep (se 3 (by rfl) ⟨1249232, by rfl⟩ : syracuseStep 6662573 = 2498465) B2498465
theorem B34236845 : Blo 1315976 34236845 := bstep (se 3 (by rfl) ⟨6419408, by rfl⟩ : syracuseStep 34236845 = 12838817) B12838817
theorem B4442579 : Blo 1315976 4442579 := bstep (se 1 (by rfl) ⟨3331934, by rfl⟩ : syracuseStep 4442579 = 6663869) B6663869
theorem B6670835 : Blo 1315976 6670835 := bstep (se 1 (by rfl) ⟨5003126, by rfl⟩ : syracuseStep 6670835 = 10006253) B10006253
theorem B4442687 : Blo 1315976 4442687 := bstep (se 1 (by rfl) ⟨3332015, by rfl⟩ : syracuseStep 4442687 = 6664031) B6664031
theorem B3426887 : Blo 1315976 3426887 := bstep (se 1 (by rfl) ⟨2570165, by rfl⟩ : syracuseStep 3426887 = 5140331) B5140331
theorem B1976903 : Blo 1315976 1976903 := bstep (se 1 (by rfl) ⟨1482677, by rfl⟩ : syracuseStep 1976903 = 2965355) B2965355
theorem B6662735 : Blo 1315976 6662735 := bstep (se 1 (by rfl) ⟨4997051, by rfl⟩ : syracuseStep 6662735 = 9994103) B9994103
theorem B12831311 : Blo 1315976 12831311 := bstep (se 1 (by rfl) ⟨9623483, by rfl⟩ : syracuseStep 12831311 = 19246967) B19246967
theorem B1976939 : Blo 1315976 1976939 := bstep (se 1 (by rfl) ⟨1482704, by rfl⟩ : syracuseStep 1976939 = 2965409) B2965409
theorem B2222815 : Blo 1315976 2222815 := bstep (se 1 (by rfl) ⟨1667111, by rfl⟩ : syracuseStep 2222815 = 3334223) B3334223
theorem B10005281 : Blo 1315976 10005281 := bstep (se 2 (by rfl) ⟨3751980, by rfl⟩ : syracuseStep 10005281 = 7503961) B7503961
theorem B13511549 : Blo 1315976 13511549 := bstep (se 3 (by rfl) ⟨2533415, by rfl⟩ : syracuseStep 13511549 = 5066831) B5066831
theorem B1665947 : Blo 1315976 1665947 := bstep (se 1 (by rfl) ⟨1249460, by rfl⟩ : syracuseStep 1665947 = 2498921) B2498921
theorem B6671483 : Blo 1315976 6671483 := bstep (se 1 (by rfl) ⟨5003612, by rfl⟩ : syracuseStep 6671483 = 10007225) B10007225
theorem B2223247 : Blo 1315976 2223247 := bstep (se 1 (by rfl) ⟨1667435, by rfl⟩ : syracuseStep 2223247 = 3334871) B3334871
theorem B2223497 : Blo 1315976 2223497 := bstep (se 2 (by rfl) ⟨833811, by rfl⟩ : syracuseStep 2223497 = 1667623) B1667623
theorem B28470845 : Blo 1315976 28470845 := bstep (se 3 (by rfl) ⟨5338283, by rfl⟩ : syracuseStep 28470845 = 10676567) B10676567
theorem B45641393 : Blo 1315976 45641393 := bstep (se 2 (by rfl) ⟨17115522, by rfl⟩ : syracuseStep 45641393 = 34231045) B34231045
theorem B25644755 : Blo 1315976 25644755 := bstep (se 1 (by rfl) ⟨19233566, by rfl⟩ : syracuseStep 25644755 = 38467133) B38467133
theorem B6672131 : Blo 1315976 6672131 := bstep (se 1 (by rfl) ⟨5004098, by rfl⟩ : syracuseStep 6672131 = 10008197) B10008197
theorem B2223929 : Blo 1315976 2223929 := bstep (se 2 (by rfl) ⟨833973, by rfl⟩ : syracuseStep 2223929 = 1667947) B1667947
theorem B2961359 : Blo 1315976 2961359 := bstep (se 1 (by rfl) ⟨2221019, by rfl⟩ : syracuseStep 2961359 = 4442039) B4442039
theorem B6664193 : Blo 1315976 6664193 := bstep (se 2 (by rfl) ⟨2499072, by rfl⟩ : syracuseStep 6664193 = 4998145) B4998145
theorem B380063755 : Blo 1315976 380063755 := bstep (se 1 (by rfl) ⟨285047816, by rfl⟩ : syracuseStep 380063755 = 570095633) B570095633
theorem B11243609 : Blo 1315976 11243609 := bstep (se 2 (by rfl) ⟨4216353, by rfl⟩ : syracuseStep 11243609 = 8432707) B8432707
theorem B194752829 : Blo 1315976 194752829 := bstep (se 3 (by rfl) ⟨36516155, by rfl⟩ : syracuseStep 194752829 = 73032311) B73032311
theorem B2961737 : Blo 1315976 2961737 := bstep (se 2 (by rfl) ⟨1110651, by rfl⟩ : syracuseStep 2961737 = 2221303) B2221303
theorem B2961755 : Blo 1315976 2961755 := bstep (se 1 (by rfl) ⟨2221316, by rfl⟩ : syracuseStep 2961755 = 4442633) B4442633
theorem B4444523 : Blo 1315976 4444523 := bstep (se 1 (by rfl) ⟨3333392, by rfl⟩ : syracuseStep 4444523 = 6666785) B6666785
theorem B3166571 : Blo 1315976 3166571 := bstep (se 1 (by rfl) ⟨2374928, by rfl⟩ : syracuseStep 3166571 = 4749857) B4749857
theorem B10678643 : Blo 1315976 10678643 := bstep (se 1 (by rfl) ⟨8008982, by rfl⟩ : syracuseStep 10678643 = 16017965) B16017965
theorem B16020017 : Blo 1315976 16020017 := bstep (se 2 (by rfl) ⟨6007506, by rfl⟩ : syracuseStep 16020017 = 12015013) B12015013
theorem B16863821 : Blo 1315976 16863821 := bstep (se 3 (by rfl) ⟨3161966, by rfl⟩ : syracuseStep 16863821 = 6323933) B6323933
theorem B5624417 : Blo 1315976 5624417 := bstep (se 2 (by rfl) ⟨2109156, by rfl⟩ : syracuseStep 5624417 = 4218313) B4218313
theorem B4444793 : Blo 1315976 4444793 := bstep (se 2 (by rfl) ⟨1666797, by rfl⟩ : syracuseStep 4444793 = 3333595) B3333595
theorem B2814635 : Blo 1315976 2814635 := bstep (se 1 (by rfl) ⟨2110976, by rfl⟩ : syracuseStep 2814635 = 4221953) B4221953
theorem B8434475 : Blo 1315976 8434475 := bstep (se 1 (by rfl) ⟨6325856, by rfl⟩ : syracuseStep 8434475 = 12651713) B12651713
theorem B6665003 : Blo 1315976 6665003 := bstep (se 1 (by rfl) ⟨4998752, by rfl⟩ : syracuseStep 6665003 = 9997505) B9997505
theorem B2962331 : Blo 1315976 2962331 := bstep (se 1 (by rfl) ⟨2221748, by rfl⟩ : syracuseStep 2962331 = 4443497) B4443497
theorem B32478155 : Blo 1315976 32478155 := bstep (se 1 (by rfl) ⟨24358616, by rfl⟩ : syracuseStep 32478155 = 48717233) B48717233
theorem B9999449 : Blo 1315976 9999449 := bstep (se 2 (by rfl) ⟨3749793, by rfl⟩ : syracuseStep 9999449 = 7499587) B7499587
theorem B2962529 : Blo 1315976 2962529 := bstep (se 2 (by rfl) ⟨1110948, by rfl⟩ : syracuseStep 2962529 = 2221897) B2221897
theorem B5002337 : Blo 1315976 5002337 := bstep (se 2 (by rfl) ⟨1875876, by rfl⟩ : syracuseStep 5002337 = 3751753) B3751753
theorem B4502675 : Blo 1315976 4502675 := bstep (se 1 (by rfl) ⟨3377006, by rfl⟩ : syracuseStep 4502675 = 6754013) B6754013
theorem B1316127 : Blo 1315976 1316127 := bstep (se 1 (by rfl) ⟨987095, by rfl⟩ : syracuseStep 1316127 = 1974191) B1974191
theorem B2962727 : Blo 1315976 2962727 := bstep (se 1 (by rfl) ⟨2222045, by rfl⟩ : syracuseStep 2962727 = 4444091) B4444091
theorem B1316187 : Blo 1315976 1316187 := bstep (se 1 (by rfl) ⟨987140, by rfl⟩ : syracuseStep 1316187 = 1974281) B1974281
theorem B1316207 : Blo 1315976 1316207 := bstep (se 1 (by rfl) ⟨987155, by rfl⟩ : syracuseStep 1316207 = 1974311) B1974311
theorem B4216187 : Blo 1315976 4216187 := bstep (se 1 (by rfl) ⟨3162140, by rfl⟩ : syracuseStep 4216187 = 6324281) B6324281
theorem B3331489 : Blo 1315976 3331489 := bstep (se 2 (by rfl) ⟨1249308, by rfl⟩ : syracuseStep 3331489 = 2498617) B2498617
theorem B1316263 : Blo 1315976 1316263 := bstep (se 1 (by rfl) ⟨987197, by rfl⟩ : syracuseStep 1316263 = 1974395) B1974395
theorem B1316347 : Blo 1315976 1316347 := bstep (se 1 (by rfl) ⟨987260, by rfl⟩ : syracuseStep 1316347 = 1974521) B1974521
theorem B7501319 : Blo 1315976 7501319 := bstep (se 1 (by rfl) ⟨5625989, by rfl⟩ : syracuseStep 7501319 = 11251979) B11251979
theorem B1316415 : Blo 1315976 1316415 := bstep (se 1 (by rfl) ⟨987311, by rfl⟩ : syracuseStep 1316415 = 1974623) B1974623
theorem B1463879 : Blo 1315976 1463879 := bstep (se 1 (by rfl) ⟨1097909, by rfl⟩ : syracuseStep 1463879 = 2195819) B2195819
theorem B1316423 : Blo 1315976 1316423 := bstep (se 1 (by rfl) ⟨987317, by rfl⟩ : syracuseStep 1316423 = 1974635) B1974635
theorem B2963105 : Blo 1315976 2963105 := bstep (se 2 (by rfl) ⟨1111164, by rfl⟩ : syracuseStep 2963105 = 2222329) B2222329
theorem B1316575 : Blo 1315976 1316575 := bstep (se 1 (by rfl) ⟨987431, by rfl⟩ : syracuseStep 1316575 = 1974863) B1974863
theorem B1480495 : Blo 1315976 1480495 := bstep (se 1 (by rfl) ⟨1110371, by rfl⟩ : syracuseStep 1480495 = 2220743) B2220743
theorem B1316655 : Blo 1315976 1316655 := bstep (se 1 (by rfl) ⟨987491, by rfl⟩ : syracuseStep 1316655 = 1974983) B1974983
theorem B1480603 : Blo 1315976 1480603 := bstep (se 1 (by rfl) ⟨1110452, by rfl⟩ : syracuseStep 1480603 = 2220905) B2220905
theorem B1316763 : Blo 1315976 1316763 := bstep (se 1 (by rfl) ⟨987572, by rfl⟩ : syracuseStep 1316763 = 1975145) B1975145
theorem B1316815 : Blo 1315976 1316815 := bstep (se 1 (by rfl) ⟨987611, by rfl⟩ : syracuseStep 1316815 = 1975223) B1975223
theorem B1316839 : Blo 1315976 1316839 := bstep (se 1 (by rfl) ⟨987629, by rfl⟩ : syracuseStep 1316839 = 1975259) B1975259
theorem B4749293 : Blo 1315976 4749293 := bstep (se 3 (by rfl) ⟨890492, by rfl⟩ : syracuseStep 4749293 = 1780985) B1780985
theorem B2963465 : Blo 1315976 2963465 := bstep (se 2 (by rfl) ⟨1111299, by rfl⟩ : syracuseStep 2963465 = 2222599) B2222599
theorem B6412553 : Blo 1315976 6412553 := bstep (se 2 (by rfl) ⟨2404707, by rfl⟩ : syracuseStep 6412553 = 4809415) B4809415
theorem B1317151 : Blo 1315976 1317151 := bstep (se 1 (by rfl) ⟨987863, by rfl⟩ : syracuseStep 1317151 = 1975727) B1975727
theorem B1480999 : Blo 1315976 1480999 := bstep (se 1 (by rfl) ⟨1110749, by rfl⟩ : syracuseStep 1480999 = 2221499) B2221499
theorem B1317211 : Blo 1315976 1317211 := bstep (se 1 (by rfl) ⟨987908, by rfl⟩ : syracuseStep 1317211 = 1975817) B1975817
theorem B1481071 : Blo 1315976 1481071 := bstep (se 1 (by rfl) ⟨1110803, by rfl⟩ : syracuseStep 1481071 = 2221607) B2221607
theorem B1317231 : Blo 1315976 1317231 := bstep (se 1 (by rfl) ⟨987923, by rfl⟩ : syracuseStep 1317231 = 1975847) B1975847
theorem B4446575 : Blo 1315976 4446575 := bstep (se 1 (by rfl) ⟨3334931, by rfl⟩ : syracuseStep 4446575 = 6669863) B6669863
theorem B2963879 : Blo 1315976 2963879 := bstep (se 1 (by rfl) ⟨2222909, by rfl⟩ : syracuseStep 2963879 = 4445819) B4445819
theorem B1317287 : Blo 1315976 1317287 := bstep (se 1 (by rfl) ⟨987965, by rfl⟩ : syracuseStep 1317287 = 1975931) B1975931
theorem B3332603 : Blo 1315976 3332603 := bstep (se 1 (by rfl) ⟨2499452, by rfl⟩ : syracuseStep 3332603 = 4998905) B4998905
theorem B1317371 : Blo 1315976 1317371 := bstep (se 1 (by rfl) ⟨988028, by rfl⟩ : syracuseStep 1317371 = 1976057) B1976057
theorem B2963987 : Blo 1315976 2963987 := bstep (se 1 (by rfl) ⟨2222990, by rfl⟩ : syracuseStep 2963987 = 4445981) B4445981
theorem B12835367 : Blo 1315976 12835367 := bstep (se 1 (by rfl) ⟨9626525, by rfl⟩ : syracuseStep 12835367 = 19253051) B19253051
theorem B1317439 : Blo 1315976 1317439 := bstep (se 1 (by rfl) ⟨988079, by rfl⟩ : syracuseStep 1317439 = 1976159) B1976159
theorem B1481287 : Blo 1315976 1481287 := bstep (se 1 (by rfl) ⟨1110965, by rfl⟩ : syracuseStep 1481287 = 2221931) B2221931
theorem B1317447 : Blo 1315976 1317447 := bstep (se 1 (by rfl) ⟨988085, by rfl⟩ : syracuseStep 1317447 = 1976171) B1976171
theorem B4217417 : Blo 1315976 4217417 := bstep (se 2 (by rfl) ⟨1581531, by rfl⟩ : syracuseStep 4217417 = 3163063) B3163063
theorem B2964041 : Blo 1315976 2964041 := bstep (se 2 (by rfl) ⟨1111515, by rfl⟩ : syracuseStep 2964041 = 2223031) B2223031
theorem B6666947 : Blo 1315976 6666947 := bstep (se 1 (by rfl) ⟨5000210, by rfl⟩ : syracuseStep 6666947 = 10000421) B10000421
theorem B5339843 : Blo 1315976 5339843 := bstep (se 1 (by rfl) ⟨4004882, by rfl⟩ : syracuseStep 5339843 = 8009765) B8009765
theorem B2251487 : Blo 1315976 2251487 := bstep (se 1 (by rfl) ⟨1688615, by rfl⟩ : syracuseStep 2251487 = 3377231) B3377231
theorem B1317599 : Blo 1315976 1317599 := bstep (se 1 (by rfl) ⟨988199, by rfl⟩ : syracuseStep 1317599 = 1976399) B1976399
theorem B3562231 : Blo 1315976 3562231 := bstep (se 1 (by rfl) ⟨2671673, by rfl⟩ : syracuseStep 3562231 = 5343347) B5343347
theorem B1317679 : Blo 1315976 1317679 := bstep (se 1 (by rfl) ⟨988259, by rfl⟩ : syracuseStep 1317679 = 1976519) B1976519
theorem B1317787 : Blo 1315976 1317787 := bstep (se 1 (by rfl) ⟨988340, by rfl⟩ : syracuseStep 1317787 = 1976681) B1976681
theorem B1317839 : Blo 1315976 1317839 := bstep (se 1 (by rfl) ⟨988379, by rfl⟩ : syracuseStep 1317839 = 1976759) B1976759
theorem B2964455 : Blo 1315976 2964455 := bstep (se 1 (by rfl) ⟨2223341, by rfl⟩ : syracuseStep 2964455 = 4446683) B4446683
theorem B1317863 : Blo 1315976 1317863 := bstep (se 1 (by rfl) ⟨988397, by rfl⟩ : syracuseStep 1317863 = 1976795) B1976795
theorem B72121589 : Blo 1315976 72121589 := bstep (se 5 (by rfl) ⟨3380699, by rfl⟩ : syracuseStep 72121589 = 6761399) B6761399
theorem B2964833 : Blo 1315976 2964833 := bstep (se 2 (by rfl) ⟨1111812, by rfl⟩ : syracuseStep 2964833 = 2223625) B2223625
theorem B6413687 : Blo 1315976 6413687 := bstep (se 1 (by rfl) ⟨4810265, by rfl⟩ : syracuseStep 6413687 = 9620531) B9620531
theorem B1482151 : Blo 1315976 1482151 := bstep (se 1 (by rfl) ⟨1111613, by rfl⟩ : syracuseStep 1482151 = 2223227) B2223227
theorem B2964923 : Blo 1315976 2964923 := bstep (se 1 (by rfl) ⟨2223692, by rfl⟩ : syracuseStep 2964923 = 4447385) B4447385
theorem B3333575 : Blo 1315976 3333575 := bstep (se 1 (by rfl) ⟨2500181, by rfl⟩ : syracuseStep 3333575 = 5000363) B5000363
theorem B10001879 : Blo 1315976 10001879 := bstep (se 1 (by rfl) ⟨7501409, by rfl⟩ : syracuseStep 10001879 = 15002819) B15002819
theorem B2965049 : Blo 1315976 2965049 := bstep (se 2 (by rfl) ⟨1111893, by rfl⟩ : syracuseStep 2965049 = 2223787) B2223787
theorem B4447979 : Blo 1315976 4447979 := bstep (se 1 (by rfl) ⟨3335984, by rfl⟩ : syracuseStep 4447979 = 6671969) B6671969
theorem B2498359 : Blo 1315976 2498359 := bstep (se 1 (by rfl) ⟨1873769, by rfl⟩ : syracuseStep 2498359 = 3747539) B3747539
theorem B1974071 : Blo 1315976 1974071 := bstep (se 1 (by rfl) ⟨1480553, by rfl⟩ : syracuseStep 1974071 = 2961107) B2961107
theorem B21364553 : Blo 1315976 21364553 := bstep (se 2 (by rfl) ⟨8011707, by rfl⟩ : syracuseStep 21364553 = 16023415) B16023415
theorem B7495739 : Blo 1315976 7495739 := bstep (se 1 (by rfl) ⟨5621804, by rfl⟩ : syracuseStep 7495739 = 11243609) B11243609
theorem B41107571 : Blo 1315976 41107571 := bstep (se 1 (by rfl) ⟨30830678, by rfl⟩ : syracuseStep 41107571 = 61661357) B61661357
theorem B129835219 : Blo 1315976 129835219 := bstep (se 1 (by rfl) ⟨97376414, by rfl⟩ : syracuseStep 129835219 = 194752829) B194752829
theorem B1974491 : Blo 1315976 1974491 := bstep (se 1 (by rfl) ⟨1480868, by rfl⟩ : syracuseStep 1974491 = 2961737) B2961737
theorem B1974503 : Blo 1315976 1974503 := bstep (se 1 (by rfl) ⟨1480877, by rfl⟩ : syracuseStep 1974503 = 2961755) B2961755
theorem B7119095 : Blo 1315976 7119095 := bstep (se 1 (by rfl) ⟨5339321, by rfl⟩ : syracuseStep 7119095 = 10678643) B10678643
theorem B8438039 : Blo 1315976 8438039 := bstep (se 1 (by rfl) ⟨6328529, by rfl⟩ : syracuseStep 8438039 = 12657059) B12657059
theorem B6668567 : Blo 1315976 6668567 := bstep (se 1 (by rfl) ⟨5001425, by rfl⟩ : syracuseStep 6668567 = 10002851) B10002851
theorem B7504235 : Blo 1315976 7504235 := bstep (se 1 (by rfl) ⟨5628176, by rfl⟩ : syracuseStep 7504235 = 11256353) B11256353
theorem B1974665 : Blo 1315976 1974665 := bstep (se 2 (by rfl) ⟨740499, by rfl⟩ : syracuseStep 1974665 = 1480999) B1480999
theorem B1974761 : Blo 1315976 1974761 := bstep (se 2 (by rfl) ⟨740535, by rfl⟩ : syracuseStep 1974761 = 1481071) B1481071
theorem B37945907 : Blo 1315976 37945907 := bstep (se 1 (by rfl) ⟨28459430, by rfl⟩ : syracuseStep 37945907 = 56918861) B56918861
theorem B1974887 : Blo 1315976 1974887 := bstep (se 1 (by rfl) ⟨1481165, by rfl⟩ : syracuseStep 1974887 = 2962331) B2962331
theorem B16024193 : Blo 1315976 16024193 := bstep (se 2 (by rfl) ⟨6009072, by rfl⟩ : syracuseStep 16024193 = 12018145) B12018145
theorem B21652103 : Blo 1315976 21652103 := bstep (se 1 (by rfl) ⟨16239077, by rfl⟩ : syracuseStep 21652103 = 32478155) B32478155
theorem B1975019 : Blo 1315976 1975019 := bstep (se 1 (by rfl) ⟨1481264, by rfl⟩ : syracuseStep 1975019 = 2962529) B2962529
theorem B3334891 : Blo 1315976 3334891 := bstep (se 1 (by rfl) ⟨2501168, by rfl⟩ : syracuseStep 3334891 = 5002337) B5002337
theorem B1975049 : Blo 1315976 1975049 := bstep (se 2 (by rfl) ⟨740643, by rfl⟩ : syracuseStep 1975049 = 1481287) B1481287
theorem B1975151 : Blo 1315976 1975151 := bstep (se 1 (by rfl) ⟨1481363, by rfl⟩ : syracuseStep 1975151 = 2962727) B2962727
theorem B2810791 : Blo 1315976 2810791 := bstep (se 1 (by rfl) ⟨2108093, by rfl⟩ : syracuseStep 2810791 = 4216187) B4216187
theorem B1975403 : Blo 1315976 1975403 := bstep (se 1 (by rfl) ⟨1481552, by rfl⟩ : syracuseStep 1975403 = 2963105) B2963105
theorem B1975643 : Blo 1315976 1975643 := bstep (se 1 (by rfl) ⟨1481732, by rfl⟩ : syracuseStep 1975643 = 2963465) B2963465
theorem B7497197 : Blo 1315976 7497197 := bstep (se 3 (by rfl) ⟨1405724, by rfl⟩ : syracuseStep 7497197 = 2811449) B2811449
theorem B1975919 : Blo 1315976 1975919 := bstep (se 1 (by rfl) ⟨1481939, by rfl⟩ : syracuseStep 1975919 = 2963879) B2963879
theorem B4441715 : Blo 1315976 4441715 := bstep (se 1 (by rfl) ⟨3331286, by rfl⟩ : syracuseStep 4441715 = 6662573) B6662573
theorem B22824563 : Blo 1315976 22824563 := bstep (se 1 (by rfl) ⟨17118422, by rfl⟩ : syracuseStep 22824563 = 34236845) B34236845
theorem B2221735 : Blo 1315976 2221735 := bstep (se 1 (by rfl) ⟨1666301, by rfl⟩ : syracuseStep 2221735 = 3332603) B3332603
theorem B1975991 : Blo 1315976 1975991 := bstep (se 1 (by rfl) ⟨1481993, by rfl⟩ : syracuseStep 1975991 = 2963987) B2963987
theorem B2811611 : Blo 1315976 2811611 := bstep (se 1 (by rfl) ⟨2108708, by rfl⟩ : syracuseStep 2811611 = 4217417) B4217417
theorem B1976027 : Blo 1315976 1976027 := bstep (se 1 (by rfl) ⟨1482020, by rfl⟩ : syracuseStep 1976027 = 2964041) B2964041
theorem B4441823 : Blo 1315976 4441823 := bstep (se 1 (by rfl) ⟨3331367, by rfl⟩ : syracuseStep 4441823 = 6662735) B6662735
theorem B8554207 : Blo 1315976 8554207 := bstep (se 1 (by rfl) ⟨6415655, by rfl⟩ : syracuseStep 8554207 = 12831311) B12831311
theorem B7505693 : Blo 1315976 7505693 := bstep (se 3 (by rfl) ⟨1407317, by rfl⟩ : syracuseStep 7505693 = 2814635) B2814635
theorem B6670187 : Blo 1315976 6670187 := bstep (se 1 (by rfl) ⟨5002640, by rfl⟩ : syracuseStep 6670187 = 10005281) B10005281
theorem B4441985 : Blo 1315976 4441985 := bstep (se 2 (by rfl) ⟨1665744, by rfl⟩ : syracuseStep 4441985 = 3331489) B3331489
theorem B1976201 : Blo 1315976 1976201 := bstep (se 2 (by rfl) ⟨741075, by rfl⟩ : syracuseStep 1976201 = 1482151) B1482151
theorem B1976303 : Blo 1315976 1976303 := bstep (se 1 (by rfl) ⟨1482227, by rfl⟩ : syracuseStep 1976303 = 2964455) B2964455
theorem B48081059 : Blo 1315976 48081059 := bstep (se 1 (by rfl) ⟨36060794, by rfl⟩ : syracuseStep 48081059 = 72121589) B72121589
theorem B1976555 : Blo 1315976 1976555 := bstep (se 1 (by rfl) ⟨1482416, by rfl⟩ : syracuseStep 1976555 = 2964833) B2964833
theorem B1976615 : Blo 1315976 1976615 := bstep (se 1 (by rfl) ⟨1482461, by rfl⟩ : syracuseStep 1976615 = 2964923) B2964923
theorem B2222383 : Blo 1315976 2222383 := bstep (se 1 (by rfl) ⟨1666787, by rfl⟩ : syracuseStep 2222383 = 3333575) B3333575
theorem B1976699 : Blo 1315976 1976699 := bstep (se 1 (by rfl) ⟨1482524, by rfl⟩ : syracuseStep 1976699 = 2965049) B2965049
theorem B4442525 : Blo 1315976 4442525 := bstep (se 3 (by rfl) ⟨832973, by rfl⟩ : syracuseStep 4442525 = 1665947) B1665947
theorem B30427595 : Blo 1315976 30427595 := bstep (se 1 (by rfl) ⟨22820696, by rfl⟩ : syracuseStep 30427595 = 45641393) B45641393
theorem B4442795 : Blo 1315976 4442795 := bstep (se 1 (by rfl) ⟨3332096, by rfl⟩ : syracuseStep 4442795 = 6664193) B6664193
theorem B506751673 : Blo 1315976 506751673 := bstep (se 2 (by rfl) ⟨190031877, by rfl⟩ : syracuseStep 506751673 = 380063755) B380063755
theorem B7219961 : Blo 1315976 7219961 := bstep (se 2 (by rfl) ⟨2707485, by rfl⟩ : syracuseStep 7219961 = 5414971) B5414971
theorem B2222903 : Blo 1315976 2222903 := bstep (se 1 (by rfl) ⟨1667177, by rfl⟩ : syracuseStep 2222903 = 3334355) B3334355
theorem B11242547 : Blo 1315976 11242547 := bstep (se 1 (by rfl) ⟨8431910, by rfl⟩ : syracuseStep 11242547 = 16863821) B16863821
theorem B37973123 : Blo 1315976 37973123 := bstep (se 1 (by rfl) ⟨28479842, by rfl⟩ : syracuseStep 37973123 = 56959685) B56959685
theorem B5622983 : Blo 1315976 5622983 := bstep (se 1 (by rfl) ⟨4217237, by rfl⟩ : syracuseStep 5622983 = 8434475) B8434475
theorem B4443335 : Blo 1315976 4443335 := bstep (se 1 (by rfl) ⟨3332501, by rfl⟩ : syracuseStep 4443335 = 6665003) B6665003
theorem B1666271 : Blo 1315976 1666271 := bstep (se 1 (by rfl) ⟨1249703, by rfl⟩ : syracuseStep 1666271 = 2499407) B2499407
theorem B3001783 : Blo 1315976 3001783 := bstep (se 1 (by rfl) ⟨2251337, by rfl⟩ : syracuseStep 3001783 = 4502675) B4502675
theorem B2223679 : Blo 1315976 2223679 := bstep (se 1 (by rfl) ⟨1667759, by rfl⟩ : syracuseStep 2223679 = 3335519) B3335519
theorem B1666651 : Blo 1315976 1666651 := bstep (se 1 (by rfl) ⟨1249988, by rfl⟩ : syracuseStep 1666651 = 2499977) B2499977
theorem B2961071 : Blo 1315976 2961071 := bstep (se 1 (by rfl) ⟨2220803, by rfl⟩ : syracuseStep 2961071 = 4441607) B4441607
theorem B5000879 : Blo 1315976 5000879 := bstep (se 1 (by rfl) ⟨3750659, by rfl⟩ : syracuseStep 5000879 = 7501319) B7501319
theorem B2109407 : Blo 1315976 2109407 := bstep (se 1 (by rfl) ⟨1582055, by rfl⟩ : syracuseStep 2109407 = 3164111) B3164111
theorem B12660785 : Blo 1315976 12660785 := bstep (se 2 (by rfl) ⟨4747794, by rfl⟩ : syracuseStep 12660785 = 9495589) B9495589
theorem B10678391 : Blo 1315976 10678391 := bstep (se 1 (by rfl) ⟨8008793, by rfl⟩ : syracuseStep 10678391 = 16017587) B16017587
theorem B3903677 : Blo 1315976 3903677 := bstep (se 3 (by rfl) ⟨731939, by rfl⟩ : syracuseStep 3903677 = 1463879) B1463879
theorem B9138365 : Blo 1315976 9138365 := bstep (se 3 (by rfl) ⟨1713443, by rfl⟩ : syracuseStep 9138365 = 3426887) B3426887
theorem B2961719 : Blo 1315976 2961719 := bstep (se 1 (by rfl) ⟨2221289, by rfl⟩ : syracuseStep 2961719 = 4442579) B4442579
theorem B8556911 : Blo 1315976 8556911 := bstep (se 1 (by rfl) ⟨6417683, by rfl⟩ : syracuseStep 8556911 = 12835367) B12835367
theorem B2961791 : Blo 1315976 2961791 := bstep (se 1 (by rfl) ⟨2221343, by rfl⟩ : syracuseStep 2961791 = 4442687) B4442687
theorem B4444631 : Blo 1315976 4444631 := bstep (se 1 (by rfl) ⟨3333473, by rfl⟩ : syracuseStep 4444631 = 6666947) B6666947
theorem B3559895 : Blo 1315976 3559895 := bstep (se 1 (by rfl) ⟨2669921, by rfl⟩ : syracuseStep 3559895 = 5339843) B5339843
theorem B9007699 : Blo 1315976 9007699 := bstep (se 1 (by rfl) ⟨6755774, by rfl⟩ : syracuseStep 9007699 = 13511549) B13511549
theorem B3331145 : Blo 1315976 3331145 := bstep (se 2 (by rfl) ⟨1249179, by rfl⟩ : syracuseStep 3331145 = 2498359) B2498359
theorem B1316047 : Blo 1315976 1316047 := bstep (se 1 (by rfl) ⟨987035, by rfl⟩ : syracuseStep 1316047 = 1974071) B1974071
theorem B14243035 : Blo 1315976 14243035 := bstep (se 1 (by rfl) ⟨10682276, by rfl⟩ : syracuseStep 14243035 = 21364553) B21364553
theorem B1316251 : Blo 1315976 1316251 := bstep (se 1 (by rfl) ⟨987188, by rfl⟩ : syracuseStep 1316251 = 1974377) B1974377
theorem B2963015 : Blo 1315976 2963015 := bstep (se 1 (by rfl) ⟨2222261, by rfl⟩ : syracuseStep 2963015 = 4444523) B4444523
theorem B1316463 : Blo 1315976 1316463 := bstep (se 1 (by rfl) ⟨987347, by rfl⟩ : syracuseStep 1316463 = 1974695) B1974695
theorem B13522555 : Blo 1315976 13522555 := bstep (se 1 (by rfl) ⟨10141916, by rfl⟩ : syracuseStep 13522555 = 20283833) B20283833
theorem B1316519 : Blo 1315976 1316519 := bstep (se 1 (by rfl) ⟨987389, by rfl⟩ : syracuseStep 1316519 = 1974779) B1974779
theorem B10680011 : Blo 1315976 10680011 := bstep (se 1 (by rfl) ⟨8010008, by rfl⟩ : syracuseStep 10680011 = 16020017) B16020017
theorem B1316603 : Blo 1315976 1316603 := bstep (se 1 (by rfl) ⟨987452, by rfl⟩ : syracuseStep 1316603 = 1974905) B1974905
theorem B2963195 : Blo 1315976 2963195 := bstep (se 1 (by rfl) ⟨2222396, by rfl⟩ : syracuseStep 2963195 = 4444793) B4444793
theorem B1316639 : Blo 1315976 1316639 := bstep (se 1 (by rfl) ⟨987479, by rfl⟩ : syracuseStep 1316639 = 1974959) B1974959
theorem B1316671 : Blo 1315976 1316671 := bstep (se 1 (by rfl) ⟨987503, by rfl⟩ : syracuseStep 1316671 = 1975007) B1975007
theorem B4446089 : Blo 1315976 4446089 := bstep (se 2 (by rfl) ⟨1667283, by rfl⟩ : syracuseStep 4446089 = 3334567) B3334567
theorem B4003799 : Blo 1315976 4003799 := bstep (se 1 (by rfl) ⟨3002849, by rfl⟩ : syracuseStep 4003799 = 6005699) B6005699
theorem B1316847 : Blo 1315976 1316847 := bstep (se 1 (by rfl) ⟨987635, by rfl⟩ : syracuseStep 1316847 = 1975271) B1975271
theorem B6666299 : Blo 1315976 6666299 := bstep (se 1 (by rfl) ⟨4999724, by rfl⟩ : syracuseStep 6666299 = 9999449) B9999449
theorem B4446305 : Blo 1315976 4446305 := bstep (se 2 (by rfl) ⟨1667364, by rfl⟩ : syracuseStep 4446305 = 3334729) B3334729
theorem B1317019 : Blo 1315976 1317019 := bstep (se 1 (by rfl) ⟨987764, by rfl⟩ : syracuseStep 1317019 = 1975529) B1975529
theorem B1317055 : Blo 1315976 1317055 := bstep (se 1 (by rfl) ⟨987791, by rfl⟩ : syracuseStep 1317055 = 1975583) B1975583
theorem B8444189 : Blo 1315976 8444189 := bstep (se 3 (by rfl) ⟨1583285, by rfl⟩ : syracuseStep 8444189 = 3166571) B3166571
theorem B2963753 : Blo 1315976 2963753 := bstep (se 2 (by rfl) ⟨1111407, by rfl⟩ : syracuseStep 2963753 = 2222815) B2222815
theorem B1317167 : Blo 1315976 1317167 := bstep (se 1 (by rfl) ⟨987875, by rfl⟩ : syracuseStep 1317167 = 1975751) B1975751
theorem B4749641 : Blo 1315976 4749641 := bstep (se 2 (by rfl) ⟨1781115, by rfl⟩ : syracuseStep 4749641 = 3562231) B3562231
theorem B5626331 : Blo 1315976 5626331 := bstep (se 1 (by rfl) ⟨4219748, by rfl⟩ : syracuseStep 5626331 = 8439497) B8439497
theorem B18995735 : Blo 1315976 18995735 := bstep (se 1 (by rfl) ⟨14246801, by rfl⟩ : syracuseStep 18995735 = 28493603) B28493603
theorem B1317403 : Blo 1315976 1317403 := bstep (se 1 (by rfl) ⟨988052, by rfl⟩ : syracuseStep 1317403 = 1976105) B1976105
theorem B1317407 : Blo 1315976 1317407 := bstep (se 1 (by rfl) ⟨988055, by rfl⟩ : syracuseStep 1317407 = 1976111) B1976111
theorem B3332947 : Blo 1315976 3332947 := bstep (se 1 (by rfl) ⟨2499710, by rfl⟩ : syracuseStep 3332947 = 4999421) B4999421
theorem B4275035 : Blo 1315976 4275035 := bstep (se 1 (by rfl) ⟨3206276, by rfl⟩ : syracuseStep 4275035 = 6412553) B6412553
theorem B1317723 : Blo 1315976 1317723 := bstep (se 1 (by rfl) ⟨988292, by rfl⟩ : syracuseStep 1317723 = 1976585) B1976585
theorem B2964329 : Blo 1315976 2964329 := bstep (se 2 (by rfl) ⟨1111623, by rfl⟩ : syracuseStep 2964329 = 2223247) B2223247
theorem B2964383 : Blo 1315976 2964383 := bstep (se 1 (by rfl) ⟨2223287, by rfl⟩ : syracuseStep 2964383 = 4446575) B4446575
theorem B1317791 : Blo 1315976 1317791 := bstep (se 1 (by rfl) ⟨988343, by rfl⟩ : syracuseStep 1317791 = 1976687) B1976687
theorem B14998445 : Blo 1315976 14998445 := bstep (se 3 (by rfl) ⟨2812208, by rfl⟩ : syracuseStep 14998445 = 5624417) B5624417
theorem B3333089 : Blo 1315976 3333089 := bstep (se 2 (by rfl) ⟨1249908, by rfl⟩ : syracuseStep 3333089 = 2499817) B2499817
theorem B4447223 : Blo 1315976 4447223 := bstep (se 1 (by rfl) ⟨3335417, by rfl⟩ : syracuseStep 4447223 = 6670835) B6670835
theorem B1317935 : Blo 1315976 1317935 := bstep (se 1 (by rfl) ⟨988451, by rfl⟩ : syracuseStep 1317935 = 1976903) B1976903
theorem B1317959 : Blo 1315976 1317959 := bstep (se 1 (by rfl) ⟨988469, by rfl⟩ : syracuseStep 1317959 = 1976939) B1976939
theorem B6003965 : Blo 1315976 6003965 := bstep (se 3 (by rfl) ⟨1125743, by rfl⟩ : syracuseStep 6003965 = 2251487) B2251487
theorem B91250081 : Blo 1315976 91250081 := bstep (se 2 (by rfl) ⟨34218780, by rfl⟩ : syracuseStep 91250081 = 68437561) B68437561
theorem B4447655 : Blo 1315976 4447655 := bstep (se 1 (by rfl) ⟨3335741, by rfl⟩ : syracuseStep 4447655 = 6671483) B6671483
theorem B6667757 : Blo 1315976 6667757 := bstep (se 3 (by rfl) ⟨1250204, by rfl⟩ : syracuseStep 6667757 = 2500409) B2500409
theorem B4275791 : Blo 1315976 4275791 := bstep (se 1 (by rfl) ⟨3206843, by rfl⟩ : syracuseStep 4275791 = 6413687) B6413687
theorem B1482331 : Blo 1315976 1482331 := bstep (se 1 (by rfl) ⟨1111748, by rfl⟩ : syracuseStep 1482331 = 2223497) B2223497
theorem B6667919 : Blo 1315976 6667919 := bstep (se 1 (by rfl) ⟨5000939, by rfl⟩ : syracuseStep 6667919 = 10001879) B10001879
theorem B18980563 : Blo 1315976 18980563 := bstep (se 1 (by rfl) ⟨14235422, by rfl⟩ : syracuseStep 18980563 = 28470845) B28470845
theorem B1973993 : Blo 1315976 1973993 := bstep (se 2 (by rfl) ⟨740247, by rfl⟩ : syracuseStep 1973993 = 1480495) B1480495
theorem B17096503 : Blo 1315976 17096503 := bstep (se 1 (by rfl) ⟨12822377, by rfl⟩ : syracuseStep 17096503 = 25644755) B25644755
theorem B2965319 : Blo 1315976 2965319 := bstep (se 1 (by rfl) ⟨2223989, by rfl⟩ : syracuseStep 2965319 = 4447979) B4447979
theorem B4448087 : Blo 1315976 4448087 := bstep (se 1 (by rfl) ⟨3336065, by rfl⟩ : syracuseStep 4448087 = 6672131) B6672131
theorem B1974137 : Blo 1315976 1974137 := bstep (se 2 (by rfl) ⟨740301, by rfl⟩ : syracuseStep 1974137 = 1480603) B1480603
theorem B1482619 : Blo 1315976 1482619 := bstep (se 1 (by rfl) ⟨1111964, by rfl⟩ : syracuseStep 1482619 = 2223929) B2223929
theorem B12664781 : Blo 1315976 12664781 := bstep (se 3 (by rfl) ⟨2374646, by rfl⟩ : syracuseStep 12664781 = 4749293) B4749293
theorem B1974239 : Blo 1315976 1974239 := bstep (se 1 (by rfl) ⟨1480679, by rfl⟩ : syracuseStep 1974239 = 2961359) B2961359
theorem B4997159 : Blo 1315976 4997159 := bstep (se 1 (by rfl) ⟨3747869, by rfl⟩ : syracuseStep 4997159 = 7495739) B7495739
theorem B7118927 : Blo 1315976 7118927 := bstep (se 1 (by rfl) ⟨5339195, by rfl⟩ : syracuseStep 7118927 = 10678391) B10678391
theorem B1974479 : Blo 1315976 1974479 := bstep (se 1 (by rfl) ⟨1480859, by rfl⟩ : syracuseStep 1974479 = 2961719) B2961719
theorem B1974527 : Blo 1315976 1974527 := bstep (se 1 (by rfl) ⟨1480895, by rfl⟩ : syracuseStep 1974527 = 2961791) B2961791
theorem B173113625 : Blo 1315976 173113625 := bstep (se 2 (by rfl) ⟨64917609, by rfl⟩ : syracuseStep 173113625 = 129835219) B129835219
theorem B25297271 : Blo 1315976 25297271 := bstep (se 1 (by rfl) ⟨18972953, by rfl⟩ : syracuseStep 25297271 = 37945907) B37945907
theorem B10682795 : Blo 1315976 10682795 := bstep (se 1 (by rfl) ⟨8012096, by rfl⟩ : syracuseStep 10682795 = 16024193) B16024193
theorem B14434735 : Blo 1315976 14434735 := bstep (se 1 (by rfl) ⟨10826051, by rfl⟩ : syracuseStep 14434735 = 21652103) B21652103
theorem B2220763 : Blo 1315976 2220763 := bstep (se 1 (by rfl) ⟨1665572, by rfl⟩ : syracuseStep 2220763 = 3331145) B3331145
theorem B12010265 : Blo 1315976 12010265 := bstep (se 2 (by rfl) ⟨4503849, by rfl⟩ : syracuseStep 12010265 = 9007699) B9007699
theorem B675668897 : Blo 1315976 675668897 := bstep (se 2 (by rfl) ⟨253375836, by rfl⟩ : syracuseStep 675668897 = 506751673) B506751673
theorem B4998131 : Blo 1315976 4998131 := bstep (se 1 (by rfl) ⟨3748598, by rfl⟩ : syracuseStep 4998131 = 7497197) B7497197
theorem B1975343 : Blo 1315976 1975343 := bstep (se 1 (by rfl) ⟨1481507, by rfl⟩ : syracuseStep 1975343 = 2963015) B2963015
theorem B7120007 : Blo 1315976 7120007 := bstep (se 1 (by rfl) ⟨5340005, by rfl⟩ : syracuseStep 7120007 = 10680011) B10680011
theorem B1975463 : Blo 1315976 1975463 := bstep (se 1 (by rfl) ⟨1481597, by rfl⟩ : syracuseStep 1975463 = 2963195) B2963195
theorem B5629459 : Blo 1315976 5629459 := bstep (se 1 (by rfl) ⟨4222094, by rfl⟩ : syracuseStep 5629459 = 8444189) B8444189
theorem B1975835 : Blo 1315976 1975835 := bstep (se 1 (by rfl) ⟨1481876, by rfl⟩ : syracuseStep 1975835 = 2963753) B2963753
theorem B18990713 : Blo 1315976 18990713 := bstep (se 2 (by rfl) ⟨7121517, by rfl⟩ : syracuseStep 18990713 = 14243035) B14243035
theorem B20285063 : Blo 1315976 20285063 := bstep (se 1 (by rfl) ⟨15213797, by rfl⟩ : syracuseStep 20285063 = 30427595) B30427595
theorem B1976219 : Blo 1315976 1976219 := bstep (se 1 (by rfl) ⟨1482164, by rfl⟩ : syracuseStep 1976219 = 2964329) B2964329
theorem B7497629 : Blo 1315976 7497629 := bstep (se 3 (by rfl) ⟨1405805, by rfl⟩ : syracuseStep 7497629 = 2811611) B2811611
theorem B1976255 : Blo 1315976 1976255 := bstep (se 1 (by rfl) ⟨1482191, by rfl⟩ : syracuseStep 1976255 = 2964383) B2964383
theorem B2222059 : Blo 1315976 2222059 := bstep (se 1 (by rfl) ⟨1666544, by rfl⟩ : syracuseStep 2222059 = 3333089) B3333089
theorem B25315415 : Blo 1315976 25315415 := bstep (se 1 (by rfl) ⟨18986561, by rfl⟩ : syracuseStep 25315415 = 37973123) B37973123
theorem B2222201 : Blo 1315976 2222201 := bstep (se 2 (by rfl) ⟨833325, by rfl⟩ : syracuseStep 2222201 = 1666651) B1666651
theorem B1976441 : Blo 1315976 1976441 := bstep (se 2 (by rfl) ⟨741165, by rfl⟩ : syracuseStep 1976441 = 1482331) B1482331
theorem B42707189 : Blo 1315976 42707189 := bstep (se 5 (by rfl) ⟨2001899, by rfl⟩ : syracuseStep 42707189 = 4003799) B4003799
theorem B25307417 : Blo 1315976 25307417 := bstep (se 2 (by rfl) ⟨9490281, by rfl⟩ : syracuseStep 25307417 = 18980563) B18980563
theorem B11405609 : Blo 1315976 11405609 := bstep (se 2 (by rfl) ⟨4277103, by rfl⟩ : syracuseStep 11405609 = 8554207) B8554207
theorem B1976825 : Blo 1315976 1976825 := bstep (se 2 (by rfl) ⟨741309, by rfl⟩ : syracuseStep 1976825 = 1482619) B1482619
theorem B1976879 : Blo 1315976 1976879 := bstep (se 1 (by rfl) ⟨1482659, by rfl⟩ : syracuseStep 1976879 = 2965319) B2965319
theorem B8440523 : Blo 1315976 8440523 := bstep (se 1 (by rfl) ⟨6330392, by rfl⟩ : syracuseStep 8440523 = 12660785) B12660785
theorem B27405047 : Blo 1315976 27405047 := bstep (se 1 (by rfl) ⟨20553785, by rfl⟩ : syracuseStep 27405047 = 41107571) B41107571
theorem B5704607 : Blo 1315976 5704607 := bstep (se 1 (by rfl) ⟨4278455, by rfl⟩ : syracuseStep 5704607 = 8556911) B8556911
theorem B4443389 : Blo 1315976 4443389 := bstep (se 3 (by rfl) ⟨833135, by rfl⟩ : syracuseStep 4443389 = 1666271) B1666271
theorem B2961143 : Blo 1315976 2961143 := bstep (se 1 (by rfl) ⟨2220857, by rfl⟩ : syracuseStep 2961143 = 4441715) B4441715
theorem B4443929 : Blo 1315976 4443929 := bstep (se 2 (by rfl) ⟨1666473, by rfl⟩ : syracuseStep 4443929 = 3332947) B3332947
theorem B2961215 : Blo 1315976 2961215 := bstep (se 1 (by rfl) ⟨2220911, by rfl⟩ : syracuseStep 2961215 = 4441823) B4441823
theorem B3747721 : Blo 1315976 3747721 := bstep (se 2 (by rfl) ⟨1405395, by rfl⟩ : syracuseStep 3747721 = 2810791) B2810791
theorem B2961323 : Blo 1315976 2961323 := bstep (se 1 (by rfl) ⟨2220992, by rfl⟩ : syracuseStep 2961323 = 4441985) B4441985
theorem B4444199 : Blo 1315976 4444199 := bstep (se 1 (by rfl) ⟨3333149, by rfl⟩ : syracuseStep 4444199 = 6666299) B6666299
theorem B3166427 : Blo 1315976 3166427 := bstep (se 1 (by rfl) ⟨2374820, by rfl⟩ : syracuseStep 3166427 = 4749641) B4749641
theorem B2961683 : Blo 1315976 2961683 := bstep (se 1 (by rfl) ⟨2221262, by rfl⟩ : syracuseStep 2961683 = 4442525) B4442525
theorem B2961863 : Blo 1315976 2961863 := bstep (se 1 (by rfl) ⟨2221397, by rfl⟩ : syracuseStep 2961863 = 4442795) B4442795
theorem B4813307 : Blo 1315976 4813307 := bstep (se 1 (by rfl) ⟨3609980, by rfl⟩ : syracuseStep 4813307 = 7219961) B7219961
theorem B4002377 : Blo 1315976 4002377 := bstep (se 2 (by rfl) ⟨1500891, by rfl⟩ : syracuseStep 4002377 = 3001783) B3001783
theorem B9998963 : Blo 1315976 9998963 := bstep (se 1 (by rfl) ⟨7499222, by rfl⟩ : syracuseStep 9998963 = 14998445) B14998445
theorem B3748655 : Blo 1315976 3748655 := bstep (se 1 (by rfl) ⟨2811491, by rfl⟩ : syracuseStep 3748655 = 5622983) B5622983
theorem B2962223 : Blo 1315976 2962223 := bstep (se 1 (by rfl) ⟨2221667, by rfl⟩ : syracuseStep 2962223 = 4443335) B4443335
theorem B4002643 : Blo 1315976 4002643 := bstep (se 1 (by rfl) ⟨3001982, by rfl⟩ : syracuseStep 4002643 = 6003965) B6003965
theorem B2962313 : Blo 1315976 2962313 := bstep (se 2 (by rfl) ⟨1110867, by rfl⟩ : syracuseStep 2962313 = 2221735) B2221735
theorem B4445171 : Blo 1315976 4445171 := bstep (se 1 (by rfl) ⟨3333878, by rfl⟩ : syracuseStep 4445171 = 6667757) B6667757
theorem B22795337 : Blo 1315976 22795337 := bstep (se 2 (by rfl) ⟨8548251, by rfl⟩ : syracuseStep 22795337 = 17096503) B17096503
theorem B4445279 : Blo 1315976 4445279 := bstep (se 1 (by rfl) ⟨3333959, by rfl⟩ : syracuseStep 4445279 = 6667919) B6667919
theorem B1315995 : Blo 1315976 1315995 := bstep (se 1 (by rfl) ⟨986996, by rfl⟩ : syracuseStep 1315995 = 1973993) B1973993
theorem B75937013 : Blo 1315976 75937013 := bstep (se 5 (by rfl) ⟨3559547, by rfl⟩ : syracuseStep 75937013 = 7119095) B7119095
theorem B1316091 : Blo 1315976 1316091 := bstep (se 1 (by rfl) ⟨987068, by rfl⟩ : syracuseStep 1316091 = 1974137) B1974137
theorem B5625085 : Blo 1315976 5625085 := bstep (se 3 (by rfl) ⟨1054703, by rfl⟩ : syracuseStep 5625085 = 2109407) B2109407
theorem B8443187 : Blo 1315976 8443187 := bstep (se 1 (by rfl) ⟨6332390, by rfl⟩ : syracuseStep 8443187 = 12664781) B12664781
theorem B1316159 : Blo 1315976 1316159 := bstep (se 1 (by rfl) ⟨987119, by rfl⟩ : syracuseStep 1316159 = 1974239) B1974239
theorem B2602451 : Blo 1315976 2602451 := bstep (se 1 (by rfl) ⟨1951838, by rfl⟩ : syracuseStep 2602451 = 3903677) B3903677
theorem B6092243 : Blo 1315976 6092243 := bstep (se 1 (by rfl) ⟨4569182, by rfl⟩ : syracuseStep 6092243 = 9138365) B9138365
theorem B1316327 : Blo 1315976 1316327 := bstep (se 1 (by rfl) ⟨987245, by rfl⟩ : syracuseStep 1316327 = 1974491) B1974491
theorem B1316335 : Blo 1315976 1316335 := bstep (se 1 (by rfl) ⟨987251, by rfl⟩ : syracuseStep 1316335 = 1974503) B1974503
theorem B5625359 : Blo 1315976 5625359 := bstep (se 1 (by rfl) ⟨4219019, by rfl⟩ : syracuseStep 5625359 = 8438039) B8438039
theorem B4445711 : Blo 1315976 4445711 := bstep (se 1 (by rfl) ⟨3334283, by rfl⟩ : syracuseStep 4445711 = 6668567) B6668567
theorem B5002823 : Blo 1315976 5002823 := bstep (se 1 (by rfl) ⟨3752117, by rfl⟩ : syracuseStep 5002823 = 7504235) B7504235
theorem B1316443 : Blo 1315976 1316443 := bstep (se 1 (by rfl) ⟨987332, by rfl⟩ : syracuseStep 1316443 = 1974665) B1974665
theorem B2963087 : Blo 1315976 2963087 := bstep (se 1 (by rfl) ⟨2222315, by rfl⟩ : syracuseStep 2963087 = 4444631) B4444631
theorem B2373263 : Blo 1315976 2373263 := bstep (se 1 (by rfl) ⟨1779947, by rfl⟩ : syracuseStep 2373263 = 3559895) B3559895
theorem B1316507 : Blo 1315976 1316507 := bstep (se 1 (by rfl) ⟨987380, by rfl⟩ : syracuseStep 1316507 = 1974761) B1974761
theorem B2963177 : Blo 1315976 2963177 := bstep (se 2 (by rfl) ⟨1111191, by rfl⟩ : syracuseStep 2963177 = 2222383) B2222383
theorem B1316591 : Blo 1315976 1316591 := bstep (se 1 (by rfl) ⟨987443, by rfl⟩ : syracuseStep 1316591 = 1974887) B1974887
theorem B1316679 : Blo 1315976 1316679 := bstep (se 1 (by rfl) ⟨987509, by rfl⟩ : syracuseStep 1316679 = 1975019) B1975019
theorem B1316699 : Blo 1315976 1316699 := bstep (se 1 (by rfl) ⟨987524, by rfl⟩ : syracuseStep 1316699 = 1975049) B1975049
theorem B1316767 : Blo 1315976 1316767 := bstep (se 1 (by rfl) ⟨987575, by rfl⟩ : syracuseStep 1316767 = 1975151) B1975151
theorem B1316935 : Blo 1315976 1316935 := bstep (se 1 (by rfl) ⟨987701, by rfl⟩ : syracuseStep 1316935 = 1975403) B1975403
theorem B1317095 : Blo 1315976 1317095 := bstep (se 1 (by rfl) ⟨987821, by rfl⟩ : syracuseStep 1317095 = 1975643) B1975643
theorem B4446521 : Blo 1315976 4446521 := bstep (se 2 (by rfl) ⟨1667445, by rfl⟩ : syracuseStep 4446521 = 3334891) B3334891
theorem B1317279 : Blo 1315976 1317279 := bstep (se 1 (by rfl) ⟨987959, by rfl⟩ : syracuseStep 1317279 = 1975919) B1975919
theorem B1317327 : Blo 1315976 1317327 := bstep (se 1 (by rfl) ⟨987995, by rfl⟩ : syracuseStep 1317327 = 1975991) B1975991
theorem B1317351 : Blo 1315976 1317351 := bstep (se 1 (by rfl) ⟨988013, by rfl⟩ : syracuseStep 1317351 = 1976027) B1976027
theorem B5003795 : Blo 1315976 5003795 := bstep (se 1 (by rfl) ⟨3752846, by rfl⟩ : syracuseStep 5003795 = 7505693) B7505693
theorem B4446791 : Blo 1315976 4446791 := bstep (se 1 (by rfl) ⟨3335093, by rfl⟩ : syracuseStep 4446791 = 6670187) B6670187
theorem B2964059 : Blo 1315976 2964059 := bstep (se 1 (by rfl) ⟨2223044, by rfl⟩ : syracuseStep 2964059 = 4446089) B4446089
theorem B1317467 : Blo 1315976 1317467 := bstep (se 1 (by rfl) ⟨988100, by rfl⟩ : syracuseStep 1317467 = 1976201) B1976201
theorem B1317535 : Blo 1315976 1317535 := bstep (se 1 (by rfl) ⟨988151, by rfl⟩ : syracuseStep 1317535 = 1976303) B1976303
theorem B2964203 : Blo 1315976 2964203 := bstep (se 1 (by rfl) ⟨2223152, by rfl⟩ : syracuseStep 2964203 = 4446305) B4446305
theorem B32054039 : Blo 1315976 32054039 := bstep (se 1 (by rfl) ⟨24040529, by rfl⟩ : syracuseStep 32054039 = 48081059) B48081059
theorem B1317703 : Blo 1315976 1317703 := bstep (se 1 (by rfl) ⟨988277, by rfl⟩ : syracuseStep 1317703 = 1976555) B1976555
theorem B1317743 : Blo 1315976 1317743 := bstep (se 1 (by rfl) ⟨988307, by rfl⟩ : syracuseStep 1317743 = 1976615) B1976615
theorem B1317799 : Blo 1315976 1317799 := bstep (se 1 (by rfl) ⟨988349, by rfl⟩ : syracuseStep 1317799 = 1976699) B1976699
theorem B60865501 : Blo 1315976 60865501 := bstep (se 3 (by rfl) ⟨11412281, by rfl⟩ : syracuseStep 60865501 = 22824563) B22824563
theorem B3750887 : Blo 1315976 3750887 := bstep (se 1 (by rfl) ⟨2813165, by rfl⟩ : syracuseStep 3750887 = 5626331) B5626331
theorem B12663823 : Blo 1315976 12663823 := bstep (se 1 (by rfl) ⟨9497867, by rfl⟩ : syracuseStep 12663823 = 18995735) B18995735
theorem B1481935 : Blo 1315976 1481935 := bstep (se 1 (by rfl) ⟨1111451, by rfl⟩ : syracuseStep 1481935 = 2222903) B2222903
theorem B2850023 : Blo 1315976 2850023 := bstep (se 1 (by rfl) ⟨2137517, by rfl⟩ : syracuseStep 2850023 = 4275035) B4275035
theorem B2964815 : Blo 1315976 2964815 := bstep (se 1 (by rfl) ⟨2223611, by rfl⟩ : syracuseStep 2964815 = 4447223) B4447223
theorem B7495031 : Blo 1315976 7495031 := bstep (se 1 (by rfl) ⟨5621273, by rfl⟩ : syracuseStep 7495031 = 11242547) B11242547
theorem B2964905 : Blo 1315976 2964905 := bstep (se 2 (by rfl) ⟨1111839, by rfl⟩ : syracuseStep 2964905 = 2223679) B2223679
theorem B18030073 : Blo 1315976 18030073 := bstep (se 2 (by rfl) ⟨6761277, by rfl⟩ : syracuseStep 18030073 = 13522555) B13522555
theorem B60833387 : Blo 1315976 60833387 := bstep (se 1 (by rfl) ⟨45625040, by rfl⟩ : syracuseStep 60833387 = 91250081) B91250081
theorem B2965103 : Blo 1315976 2965103 := bstep (se 1 (by rfl) ⟨2223827, by rfl⟩ : syracuseStep 2965103 = 4447655) B4447655
theorem B2850527 : Blo 1315976 2850527 := bstep (se 1 (by rfl) ⟨2137895, by rfl⟩ : syracuseStep 2850527 = 4275791) B4275791
theorem B1974047 : Blo 1315976 1974047 := bstep (se 1 (by rfl) ⟨1480535, by rfl⟩ : syracuseStep 1974047 = 2961071) B2961071
theorem B3333919 : Blo 1315976 3333919 := bstep (se 1 (by rfl) ⟨2500439, by rfl⟩ : syracuseStep 3333919 = 5000879) B5000879
theorem B2965391 : Blo 1315976 2965391 := bstep (se 1 (by rfl) ⟨2224043, by rfl⟩ : syracuseStep 2965391 = 4448087) B4448087
theorem B1974455 : Blo 1315976 1974455 := bstep (se 1 (by rfl) ⟨1480841, by rfl⟩ : syracuseStep 1974455 = 2961683) B2961683
theorem B115409083 : Blo 1315976 115409083 := bstep (se 1 (by rfl) ⟨86556812, by rfl⟩ : syracuseStep 115409083 = 173113625) B173113625
theorem B1974575 : Blo 1315976 1974575 := bstep (se 1 (by rfl) ⟨1480931, by rfl⟩ : syracuseStep 1974575 = 2961863) B2961863
theorem B2499103 : Blo 1315976 2499103 := bstep (se 1 (by rfl) ⟨1874327, by rfl⟩ : syracuseStep 2499103 = 3748655) B3748655
theorem B1974815 : Blo 1315976 1974815 := bstep (se 1 (by rfl) ⟨1481111, by rfl⟩ : syracuseStep 1974815 = 2962223) B2962223
theorem B1974875 : Blo 1315976 1974875 := bstep (se 1 (by rfl) ⟨1481156, by rfl⟩ : syracuseStep 1974875 = 2962313) B2962313
theorem B450445931 : Blo 1315976 450445931 := bstep (se 1 (by rfl) ⟨337834448, by rfl⟩ : syracuseStep 450445931 = 675668897) B675668897
theorem B15196891 : Blo 1315976 15196891 := bstep (se 1 (by rfl) ⟨11397668, by rfl⟩ : syracuseStep 15196891 = 22795337) B22795337
theorem B5628791 : Blo 1315976 5628791 := bstep (se 1 (by rfl) ⟨4221593, by rfl⟩ : syracuseStep 5628791 = 8443187) B8443187
theorem B3335215 : Blo 1315976 3335215 := bstep (se 1 (by rfl) ⟨2501411, by rfl⟩ : syracuseStep 3335215 = 5002823) B5002823
theorem B1975391 : Blo 1315976 1975391 := bstep (se 1 (by rfl) ⟨1481543, by rfl⟩ : syracuseStep 1975391 = 2963087) B2963087
theorem B1582175 : Blo 1315976 1582175 := bstep (se 1 (by rfl) ⟨1186631, by rfl⟩ : syracuseStep 1582175 = 2373263) B2373263
theorem B1975451 : Blo 1315976 1975451 := bstep (se 1 (by rfl) ⟨1481588, by rfl⟩ : syracuseStep 1975451 = 2963177) B2963177
theorem B4998419 : Blo 1315976 4998419 := bstep (se 1 (by rfl) ⟨3748814, by rfl⟩ : syracuseStep 4998419 = 7497629) B7497629
theorem B16885097 : Blo 1315976 16885097 := bstep (se 2 (by rfl) ⟨6331911, by rfl⟩ : syracuseStep 16885097 = 12663823) B12663823
theorem B16876943 : Blo 1315976 16876943 := bstep (se 1 (by rfl) ⟨12657707, by rfl⟩ : syracuseStep 16876943 = 25315415) B25315415
theorem B7603739 : Blo 1315976 7603739 := bstep (se 1 (by rfl) ⟨5702804, by rfl⟩ : syracuseStep 7603739 = 11405609) B11405609
theorem B1975913 : Blo 1315976 1975913 := bstep (se 2 (by rfl) ⟨740967, by rfl⟩ : syracuseStep 1975913 = 1481935) B1481935
theorem B3335863 : Blo 1315976 3335863 := bstep (se 1 (by rfl) ⟨2501897, by rfl⟩ : syracuseStep 3335863 = 5003795) B5003795
theorem B1976039 : Blo 1315976 1976039 := bstep (se 1 (by rfl) ⟨1482029, by rfl⟩ : syracuseStep 1976039 = 2964059) B2964059
theorem B1976135 : Blo 1315976 1976135 := bstep (se 1 (by rfl) ⟨1482101, by rfl⟩ : syracuseStep 1976135 = 2964203) B2964203
theorem B18270031 : Blo 1315976 18270031 := bstep (se 1 (by rfl) ⟨13702523, by rfl⟩ : syracuseStep 18270031 = 27405047) B27405047
theorem B3803071 : Blo 1315976 3803071 := bstep (se 1 (by rfl) ⟨2852303, by rfl⟩ : syracuseStep 3803071 = 5704607) B5704607
theorem B7505945 : Blo 1315976 7505945 := bstep (se 2 (by rfl) ⟨2814729, by rfl⟩ : syracuseStep 7505945 = 5629459) B5629459
theorem B1976543 : Blo 1315976 1976543 := bstep (se 1 (by rfl) ⟨1482407, by rfl⟩ : syracuseStep 1976543 = 2964815) B2964815
theorem B1976603 : Blo 1315976 1976603 := bstep (se 1 (by rfl) ⟨1482452, by rfl⟩ : syracuseStep 1976603 = 2964905) B2964905
theorem B1976735 : Blo 1315976 1976735 := bstep (se 1 (by rfl) ⟨1482551, by rfl⟩ : syracuseStep 1976735 = 2965103) B2965103
theorem B1976927 : Blo 1315976 1976927 := bstep (se 1 (by rfl) ⟨1482695, by rfl⟩ : syracuseStep 1976927 = 2965391) B2965391
theorem B4745951 : Blo 1315976 4745951 := bstep (se 1 (by rfl) ⟨3559463, by rfl⟩ : syracuseStep 4745951 = 7118927) B7118927
theorem B7121863 : Blo 1315976 7121863 := bstep (se 1 (by rfl) ⟨5341397, by rfl⟩ : syracuseStep 7121863 = 10682795) B10682795
theorem B8006843 : Blo 1315976 8006843 := bstep (se 1 (by rfl) ⟨6005132, by rfl⟩ : syracuseStep 8006843 = 12010265) B12010265
theorem B19246313 : Blo 1315976 19246313 := bstep (se 2 (by rfl) ⟨7217367, by rfl⟩ : syracuseStep 19246313 = 14434735) B14434735
theorem B4746671 : Blo 1315976 4746671 := bstep (se 1 (by rfl) ⟨3560003, by rfl⟩ : syracuseStep 4746671 = 7120007) B7120007
theorem B2961017 : Blo 1315976 2961017 := bstep (se 2 (by rfl) ⟨1110381, by rfl⟩ : syracuseStep 2961017 = 2220763) B2220763
theorem B12660475 : Blo 1315976 12660475 := bstep (se 1 (by rfl) ⟨9495356, by rfl⟩ : syracuseStep 12660475 = 18990713) B18990713
theorem B5336857 : Blo 1315976 5336857 := bstep (se 2 (by rfl) ⟨2001321, by rfl⟩ : syracuseStep 5336857 = 4002643) B4002643
theorem B81154001 : Blo 1315976 81154001 := bstep (se 2 (by rfl) ⟨30432750, by rfl⟩ : syracuseStep 81154001 = 60865501) B60865501
theorem B28471459 : Blo 1315976 28471459 := bstep (se 1 (by rfl) ⟨21353594, by rfl⟩ : syracuseStep 28471459 = 42707189) B42707189
theorem B16871611 : Blo 1315976 16871611 := bstep (se 1 (by rfl) ⟨12653708, by rfl⟩ : syracuseStep 16871611 = 25307417) B25307417
theorem B162222365 : Blo 1315976 162222365 := bstep (se 3 (by rfl) ⟨30416693, by rfl⟩ : syracuseStep 162222365 = 60833387) B60833387
theorem B7500113 : Blo 1315976 7500113 := bstep (se 2 (by rfl) ⟨2812542, by rfl⟩ : syracuseStep 7500113 = 5625085) B5625085
theorem B21369359 : Blo 1315976 21369359 := bstep (se 1 (by rfl) ⟨16027019, by rfl⟩ : syracuseStep 21369359 = 32054039) B32054039
theorem B24040097 : Blo 1315976 24040097 := bstep (se 2 (by rfl) ⟨9015036, by rfl⟩ : syracuseStep 24040097 = 18030073) B18030073
theorem B2962259 : Blo 1315976 2962259 := bstep (se 1 (by rfl) ⟨2221694, by rfl⟩ : syracuseStep 2962259 = 4443389) B4443389
theorem B4445225 : Blo 1315976 4445225 := bstep (se 2 (by rfl) ⟨1666959, by rfl⟩ : syracuseStep 4445225 = 3333919) B3333919
theorem B2962619 : Blo 1315976 2962619 := bstep (se 1 (by rfl) ⟨2221964, by rfl⟩ : syracuseStep 2962619 = 4443929) B4443929
theorem B1316031 : Blo 1315976 1316031 := bstep (se 1 (by rfl) ⟨987023, by rfl⟩ : syracuseStep 1316031 = 1974047) B1974047
theorem B2962745 : Blo 1315976 2962745 := bstep (se 2 (by rfl) ⟨1111029, by rfl⟩ : syracuseStep 2962745 = 2222059) B2222059
theorem B3331439 : Blo 1315976 3331439 := bstep (se 1 (by rfl) ⟨2498579, by rfl⟩ : syracuseStep 3331439 = 4997159) B4997159
theorem B2962799 : Blo 1315976 2962799 := bstep (se 1 (by rfl) ⟨2222099, by rfl⟩ : syracuseStep 2962799 = 4444199) B4444199
theorem B1316319 : Blo 1315976 1316319 := bstep (se 1 (by rfl) ⟨987239, by rfl⟩ : syracuseStep 1316319 = 1974479) B1974479
theorem B2110951 : Blo 1315976 2110951 := bstep (se 1 (by rfl) ⟨1583213, by rfl⟩ : syracuseStep 2110951 = 3166427) B3166427
theorem B1316351 : Blo 1315976 1316351 := bstep (se 1 (by rfl) ⟨987263, by rfl⟩ : syracuseStep 1316351 = 1974527) B1974527
theorem B16864847 : Blo 1315976 16864847 := bstep (se 1 (by rfl) ⟨12648635, by rfl⟩ : syracuseStep 16864847 = 25297271) B25297271
theorem B3208871 : Blo 1315976 3208871 := bstep (se 1 (by rfl) ⟨2406653, by rfl⟩ : syracuseStep 3208871 = 4813307) B4813307
theorem B6665975 : Blo 1315976 6665975 := bstep (se 1 (by rfl) ⟨4999481, by rfl⟩ : syracuseStep 6665975 = 9998963) B9998963
theorem B7600061 : Blo 1315976 7600061 := bstep (se 3 (by rfl) ⟨1425011, by rfl⟩ : syracuseStep 7600061 = 2850023) B2850023
theorem B3332087 : Blo 1315976 3332087 := bstep (se 1 (by rfl) ⟨2499065, by rfl⟩ : syracuseStep 3332087 = 4998131) B4998131
theorem B2963447 : Blo 1315976 2963447 := bstep (se 1 (by rfl) ⟨2222585, by rfl⟩ : syracuseStep 2963447 = 4445171) B4445171
theorem B1316895 : Blo 1315976 1316895 := bstep (se 1 (by rfl) ⟨987671, by rfl⟩ : syracuseStep 1316895 = 1975343) B1975343
theorem B2963519 : Blo 1315976 2963519 := bstep (se 1 (by rfl) ⟨2222639, by rfl⟩ : syracuseStep 2963519 = 4445279) B4445279
theorem B1316975 : Blo 1315976 1316975 := bstep (se 1 (by rfl) ⟨987731, by rfl⟩ : syracuseStep 1316975 = 1975463) B1975463
theorem B50624675 : Blo 1315976 50624675 := bstep (se 1 (by rfl) ⟨37968506, by rfl⟩ : syracuseStep 50624675 = 75937013) B75937013
theorem B1734967 : Blo 1315976 1734967 := bstep (se 1 (by rfl) ⟨1301225, by rfl⟩ : syracuseStep 1734967 = 2602451) B2602451
theorem B4061495 : Blo 1315976 4061495 := bstep (se 1 (by rfl) ⟨3046121, by rfl⟩ : syracuseStep 4061495 = 6092243) B6092243
theorem B3750239 : Blo 1315976 3750239 := bstep (se 1 (by rfl) ⟨2812679, by rfl⟩ : syracuseStep 3750239 = 5625359) B5625359
theorem B2963807 : Blo 1315976 2963807 := bstep (se 1 (by rfl) ⟨2222855, by rfl⟩ : syracuseStep 2963807 = 4445711) B4445711
theorem B1317223 : Blo 1315976 1317223 := bstep (se 1 (by rfl) ⟨987917, by rfl⟩ : syracuseStep 1317223 = 1975835) B1975835
theorem B13523375 : Blo 1315976 13523375 := bstep (se 1 (by rfl) ⟨10142531, by rfl⟩ : syracuseStep 13523375 = 20285063) B20285063
theorem B1317479 : Blo 1315976 1317479 := bstep (se 1 (by rfl) ⟨988109, by rfl⟩ : syracuseStep 1317479 = 1976219) B1976219
theorem B1317503 : Blo 1315976 1317503 := bstep (se 1 (by rfl) ⟨988127, by rfl⟩ : syracuseStep 1317503 = 1976255) B1976255
theorem B1481467 : Blo 1315976 1481467 := bstep (se 1 (by rfl) ⟨1111100, by rfl⟩ : syracuseStep 1481467 = 2222201) B2222201
theorem B1317627 : Blo 1315976 1317627 := bstep (se 1 (by rfl) ⟨988220, by rfl⟩ : syracuseStep 1317627 = 1976441) B1976441
theorem B10673005 : Blo 1315976 10673005 := bstep (se 3 (by rfl) ⟨2001188, by rfl⟩ : syracuseStep 10673005 = 4002377) B4002377
theorem B2964347 : Blo 1315976 2964347 := bstep (se 1 (by rfl) ⟨2223260, by rfl⟩ : syracuseStep 2964347 = 4446521) B4446521
theorem B1317883 : Blo 1315976 1317883 := bstep (se 1 (by rfl) ⟨988412, by rfl⟩ : syracuseStep 1317883 = 1976825) B1976825
theorem B1317919 : Blo 1315976 1317919 := bstep (se 1 (by rfl) ⟨988439, by rfl⟩ : syracuseStep 1317919 = 1976879) B1976879
theorem B2964527 : Blo 1315976 2964527 := bstep (se 1 (by rfl) ⟨2223395, by rfl⟩ : syracuseStep 2964527 = 4446791) B4446791
theorem B5627015 : Blo 1315976 5627015 := bstep (se 1 (by rfl) ⟨4220261, by rfl⟩ : syracuseStep 5627015 = 8440523) B8440523
theorem B4996687 : Blo 1315976 4996687 := bstep (se 1 (by rfl) ⟨3747515, by rfl⟩ : syracuseStep 4996687 = 7495031) B7495031
theorem B1900351 : Blo 1315976 1900351 := bstep (se 1 (by rfl) ⟨1425263, by rfl⟩ : syracuseStep 1900351 = 2850527) B2850527
theorem B1974095 : Blo 1315976 1974095 := bstep (se 1 (by rfl) ⟨1480571, by rfl⟩ : syracuseStep 1974095 = 2961143) B2961143
theorem B4996961 : Blo 1315976 4996961 := bstep (se 2 (by rfl) ⟨1873860, by rfl⟩ : syracuseStep 4996961 = 3747721) B3747721
theorem B1974143 : Blo 1315976 1974143 := bstep (se 1 (by rfl) ⟨1480607, by rfl⟩ : syracuseStep 1974143 = 2961215) B2961215
theorem B10002365 : Blo 1315976 10002365 := bstep (se 3 (by rfl) ⟨1875443, by rfl⟩ : syracuseStep 10002365 = 3750887) B3750887
theorem B1974215 : Blo 1315976 1974215 := bstep (se 1 (by rfl) ⟨1480661, by rfl⟩ : syracuseStep 1974215 = 2961323) B2961323
theorem B37961945 : Blo 1315976 37961945 := bstep (se 2 (by rfl) ⟨14235729, by rfl⟩ : syracuseStep 37961945 = 28471459) B28471459
theorem B153878777 : Blo 1315976 153878777 := bstep (se 2 (by rfl) ⟨57704541, by rfl⟩ : syracuseStep 153878777 = 115409083) B115409083
theorem B22495481 : Blo 1315976 22495481 := bstep (se 2 (by rfl) ⟨8435805, by rfl⟩ : syracuseStep 22495481 = 16871611) B16871611
theorem B4219133 : Blo 1315976 4219133 := bstep (se 3 (by rfl) ⟨791087, by rfl⟩ : syracuseStep 4219133 = 1582175) B1582175
theorem B14246239 : Blo 1315976 14246239 := bstep (se 1 (by rfl) ⟨10684679, by rfl⟩ : syracuseStep 14246239 = 21369359) B21369359
theorem B1974839 : Blo 1315976 1974839 := bstep (se 1 (by rfl) ⟨1481129, by rfl⟩ : syracuseStep 1974839 = 2962259) B2962259
theorem B1975079 : Blo 1315976 1975079 := bstep (se 1 (by rfl) ⟨1481309, by rfl⟩ : syracuseStep 1975079 = 2962619) B2962619
theorem B1975163 : Blo 1315976 1975163 := bstep (se 1 (by rfl) ⟨1481372, by rfl⟩ : syracuseStep 1975163 = 2962745) B2962745
theorem B11256731 : Blo 1315976 11256731 := bstep (se 1 (by rfl) ⟨8442548, by rfl⟩ : syracuseStep 11256731 = 16885097) B16885097
theorem B2220959 : Blo 1315976 2220959 := bstep (se 1 (by rfl) ⟨1665719, by rfl⟩ : syracuseStep 2220959 = 3331439) B3331439
theorem B1975199 : Blo 1315976 1975199 := bstep (se 1 (by rfl) ⟨1481399, by rfl⟩ : syracuseStep 1975199 = 2962799) B2962799
theorem B1975289 : Blo 1315976 1975289 := bstep (se 2 (by rfl) ⟨740733, by rfl⟩ : syracuseStep 1975289 = 1481467) B1481467
theorem B2139247 : Blo 1315976 2139247 := bstep (se 1 (by rfl) ⟨1604435, by rfl⟩ : syracuseStep 2139247 = 3208871) B3208871
theorem B36062333 : Blo 1315976 36062333 := bstep (se 3 (by rfl) ⟨6761687, by rfl⟩ : syracuseStep 36062333 = 13523375) B13523375
theorem B14230673 : Blo 1315976 14230673 := bstep (se 2 (by rfl) ⟨5336502, by rfl⟩ : syracuseStep 14230673 = 10673005) B10673005
theorem B2221391 : Blo 1315976 2221391 := bstep (se 1 (by rfl) ⟨1666043, by rfl⟩ : syracuseStep 2221391 = 3332087) B3332087
theorem B1975631 : Blo 1315976 1975631 := bstep (se 1 (by rfl) ⟨1481723, by rfl⟩ : syracuseStep 1975631 = 2963447) B2963447
theorem B1975679 : Blo 1315976 1975679 := bstep (se 1 (by rfl) ⟨1481759, by rfl⟩ : syracuseStep 1975679 = 2963519) B2963519
theorem B2500159 : Blo 1315976 2500159 := bstep (se 1 (by rfl) ⟨1875119, by rfl⟩ : syracuseStep 2500159 = 3750239) B3750239
theorem B1975871 : Blo 1315976 1975871 := bstep (se 1 (by rfl) ⟨1481903, by rfl⟩ : syracuseStep 1975871 = 2963807) B2963807
theorem B10135205 : Blo 1315976 10135205 := bstep (se 4 (by rfl) ⟨950175, by rfl⟩ : syracuseStep 10135205 = 1900351) B1900351
theorem B3163967 : Blo 1315976 3163967 := bstep (se 1 (by rfl) ⟨2372975, by rfl⟩ : syracuseStep 3163967 = 4745951) B4745951
theorem B1976231 : Blo 1315976 1976231 := bstep (se 1 (by rfl) ⟨1482173, by rfl⟩ : syracuseStep 1976231 = 2964347) B2964347
theorem B1976351 : Blo 1315976 1976351 := bstep (se 1 (by rfl) ⟨1482263, by rfl⟩ : syracuseStep 1976351 = 2964527) B2964527
theorem B6662249 : Blo 1315976 6662249 := bstep (se 2 (by rfl) ⟨2498343, by rfl⟩ : syracuseStep 6662249 = 4996687) B4996687
theorem B12830875 : Blo 1315976 12830875 := bstep (se 1 (by rfl) ⟨9623156, by rfl⟩ : syracuseStep 12830875 = 19246313) B19246313
theorem B3164447 : Blo 1315976 3164447 := bstep (se 1 (by rfl) ⟨2373335, by rfl⟩ : syracuseStep 3164447 = 4746671) B4746671
theorem B15010109 : Blo 1315976 15010109 := bstep (se 3 (by rfl) ⟨2814395, by rfl⟩ : syracuseStep 15010109 = 5628791) B5628791
theorem B54102667 : Blo 1315976 54102667 := bstep (se 1 (by rfl) ⟨40577000, by rfl⟩ : syracuseStep 54102667 = 81154001) B81154001
theorem B5000075 : Blo 1315976 5000075 := bstep (se 1 (by rfl) ⟨3750056, by rfl⟩ : syracuseStep 5000075 = 7500113) B7500113
theorem B300297287 : Blo 1315976 300297287 := bstep (se 1 (by rfl) ⟨225222965, by rfl⟩ : syracuseStep 300297287 = 450445931) B450445931
theorem B2313289 : Blo 1315976 2313289 := bstep (se 2 (by rfl) ⟨867483, by rfl⟩ : syracuseStep 2313289 = 1734967) B1734967
theorem B16026731 : Blo 1315976 16026731 := bstep (se 1 (by rfl) ⟨12020048, by rfl⟩ : syracuseStep 16026731 = 24040097) B24040097
theorem B11251295 : Blo 1315976 11251295 := bstep (se 1 (by rfl) ⟨8438471, by rfl⟩ : syracuseStep 11251295 = 16876943) B16876943
theorem B20262521 : Blo 1315976 20262521 := bstep (se 2 (by rfl) ⟨7598445, by rfl⟩ : syracuseStep 20262521 = 15196891) B15196891
theorem B11243231 : Blo 1315976 11243231 := bstep (se 1 (by rfl) ⟨8432423, by rfl⟩ : syracuseStep 11243231 = 16864847) B16864847
theorem B4443983 : Blo 1315976 4443983 := bstep (se 1 (by rfl) ⟨3332987, by rfl⟩ : syracuseStep 4443983 = 6665975) B6665975
theorem B5066707 : Blo 1315976 5066707 := bstep (se 1 (by rfl) ⟨3800030, by rfl⟩ : syracuseStep 5066707 = 7600061) B7600061
theorem B28463237 : Blo 1315976 28463237 := bstep (se 4 (by rfl) ⟨2668428, by rfl⟩ : syracuseStep 28463237 = 5336857) B5336857
theorem B2707663 : Blo 1315976 2707663 := bstep (se 1 (by rfl) ⟨2030747, by rfl⟩ : syracuseStep 2707663 = 4061495) B4061495
theorem B2814601 : Blo 1315976 2814601 := bstep (se 2 (by rfl) ⟨1055475, by rfl⟩ : syracuseStep 2814601 = 2110951) B2110951
theorem B5337895 : Blo 1315976 5337895 := bstep (se 1 (by rfl) ⟨4003421, by rfl⟩ : syracuseStep 5337895 = 8006843) B8006843
theorem B16880633 : Blo 1315976 16880633 := bstep (se 2 (by rfl) ⟨6330237, by rfl⟩ : syracuseStep 16880633 = 12660475) B12660475
theorem B37983269 : Blo 1315976 37983269 := bstep (se 4 (by rfl) ⟨3560931, by rfl⟩ : syracuseStep 37983269 = 7121863) B7121863
theorem B24360041 : Blo 1315976 24360041 := bstep (se 2 (by rfl) ⟨9135015, by rfl⟩ : syracuseStep 24360041 = 18270031) B18270031
theorem B1316063 : Blo 1315976 1316063 := bstep (se 1 (by rfl) ⟨987047, by rfl⟩ : syracuseStep 1316063 = 1974095) B1974095
theorem B3331307 : Blo 1315976 3331307 := bstep (se 1 (by rfl) ⟨2498480, by rfl⟩ : syracuseStep 3331307 = 4996961) B4996961
theorem B1316095 : Blo 1315976 1316095 := bstep (se 1 (by rfl) ⟨987071, by rfl⟩ : syracuseStep 1316095 = 1974143) B1974143
theorem B1316143 : Blo 1315976 1316143 := bstep (se 1 (by rfl) ⟨987107, by rfl⟩ : syracuseStep 1316143 = 1974215) B1974215
theorem B1316303 : Blo 1315976 1316303 := bstep (se 1 (by rfl) ⟨987227, by rfl⟩ : syracuseStep 1316303 = 1974455) B1974455
theorem B108148243 : Blo 1315976 108148243 := bstep (se 1 (by rfl) ⟨81111182, by rfl⟩ : syracuseStep 108148243 = 162222365) B162222365
theorem B1316383 : Blo 1315976 1316383 := bstep (se 1 (by rfl) ⟨987287, by rfl⟩ : syracuseStep 1316383 = 1974575) B1974575
theorem B1316543 : Blo 1315976 1316543 := bstep (se 1 (by rfl) ⟨987407, by rfl⟩ : syracuseStep 1316543 = 1974815) B1974815
theorem B1316583 : Blo 1315976 1316583 := bstep (se 1 (by rfl) ⟨987437, by rfl⟩ : syracuseStep 1316583 = 1974875) B1974875
theorem B2963483 : Blo 1315976 2963483 := bstep (se 1 (by rfl) ⟨2222612, by rfl⟩ : syracuseStep 2963483 = 4445225) B4445225
theorem B3332137 : Blo 1315976 3332137 := bstep (se 2 (by rfl) ⟨1249551, by rfl⟩ : syracuseStep 3332137 = 2499103) B2499103
theorem B1316927 : Blo 1315976 1316927 := bstep (se 1 (by rfl) ⟨987695, by rfl⟩ : syracuseStep 1316927 = 1975391) B1975391
theorem B1316967 : Blo 1315976 1316967 := bstep (se 1 (by rfl) ⟨987725, by rfl⟩ : syracuseStep 1316967 = 1975451) B1975451
theorem B3332279 : Blo 1315976 3332279 := bstep (se 1 (by rfl) ⟨2499209, by rfl⟩ : syracuseStep 3332279 = 4998419) B4998419
theorem B5069159 : Blo 1315976 5069159 := bstep (se 1 (by rfl) ⟨3801869, by rfl⟩ : syracuseStep 5069159 = 7603739) B7603739
theorem B1317275 : Blo 1315976 1317275 := bstep (se 1 (by rfl) ⟨987956, by rfl⟩ : syracuseStep 1317275 = 1975913) B1975913
theorem B1317359 : Blo 1315976 1317359 := bstep (se 1 (by rfl) ⟨988019, by rfl⟩ : syracuseStep 1317359 = 1976039) B1976039
theorem B1317423 : Blo 1315976 1317423 := bstep (se 1 (by rfl) ⟨988067, by rfl⟩ : syracuseStep 1317423 = 1976135) B1976135
theorem B5003963 : Blo 1315976 5003963 := bstep (se 1 (by rfl) ⟨3752972, by rfl⟩ : syracuseStep 5003963 = 7505945) B7505945
theorem B4446953 : Blo 1315976 4446953 := bstep (se 2 (by rfl) ⟨1667607, by rfl⟩ : syracuseStep 4446953 = 3335215) B3335215
theorem B33749783 : Blo 1315976 33749783 := bstep (se 1 (by rfl) ⟨25312337, by rfl⟩ : syracuseStep 33749783 = 50624675) B50624675
theorem B1317695 : Blo 1315976 1317695 := bstep (se 1 (by rfl) ⟨988271, by rfl⟩ : syracuseStep 1317695 = 1976543) B1976543
theorem B1317735 : Blo 1315976 1317735 := bstep (se 1 (by rfl) ⟨988301, by rfl⟩ : syracuseStep 1317735 = 1976603) B1976603
theorem B1317823 : Blo 1315976 1317823 := bstep (se 1 (by rfl) ⟨988367, by rfl⟩ : syracuseStep 1317823 = 1976735) B1976735
theorem B1317951 : Blo 1315976 1317951 := bstep (se 1 (by rfl) ⟨988463, by rfl⟩ : syracuseStep 1317951 = 1976927) B1976927
theorem B3751343 : Blo 1315976 3751343 := bstep (se 1 (by rfl) ⟨2813507, by rfl⟩ : syracuseStep 3751343 = 5627015) B5627015
theorem B4447817 : Blo 1315976 4447817 := bstep (se 2 (by rfl) ⟨1667931, by rfl⟩ : syracuseStep 4447817 = 3335863) B3335863
theorem B1974011 : Blo 1315976 1974011 := bstep (se 1 (by rfl) ⟨1480508, by rfl⟩ : syracuseStep 1974011 = 2961017) B2961017
theorem B5070761 : Blo 1315976 5070761 := bstep (se 2 (by rfl) ⟨1901535, by rfl⟩ : syracuseStep 5070761 = 3803071) B3803071
theorem B6668243 : Blo 1315976 6668243 := bstep (se 1 (by rfl) ⟨5001182, by rfl⟩ : syracuseStep 6668243 = 10002365) B10002365
theorem B12337541 : Blo 1315976 12337541 := bstep (se 4 (by rfl) ⟨1156644, by rfl⟩ : syracuseStep 12337541 = 2313289) B2313289
theorem B7504487 : Blo 1315976 7504487 := bstep (se 1 (by rfl) ⟨5628365, by rfl⟩ : syracuseStep 7504487 = 11256731) B11256731
theorem B25322179 : Blo 1315976 25322179 := bstep (se 1 (by rfl) ⟨18991634, by rfl⟩ : syracuseStep 25322179 = 37983269) B37983269
theorem B8438525 : Blo 1315976 8438525 := bstep (se 3 (by rfl) ⟨1582223, by rfl⟩ : syracuseStep 8438525 = 3164447) B3164447
theorem B9487115 : Blo 1315976 9487115 := bstep (se 1 (by rfl) ⟨7115336, by rfl⟩ : syracuseStep 9487115 = 14230673) B14230673
theorem B2220871 : Blo 1315976 2220871 := bstep (se 1 (by rfl) ⟨1665653, by rfl⟩ : syracuseStep 2220871 = 3331307) B3331307
theorem B3752801 : Blo 1315976 3752801 := bstep (se 2 (by rfl) ⟨1407300, by rfl⟩ : syracuseStep 3752801 = 2814601) B2814601
theorem B1975655 : Blo 1315976 1975655 := bstep (se 1 (by rfl) ⟨1481741, by rfl⟩ : syracuseStep 1975655 = 2963483) B2963483
theorem B4441499 : Blo 1315976 4441499 := bstep (se 1 (by rfl) ⟨3331124, by rfl⟩ : syracuseStep 4441499 = 6662249) B6662249
theorem B2221519 : Blo 1315976 2221519 := bstep (se 1 (by rfl) ⟨1666139, by rfl⟩ : syracuseStep 2221519 = 3332279) B3332279
theorem B2852329 : Blo 1315976 2852329 := bstep (se 2 (by rfl) ⟨1069623, by rfl⟩ : syracuseStep 2852329 = 2139247) B2139247
theorem B3335975 : Blo 1315976 3335975 := bstep (se 1 (by rfl) ⟨2501981, by rfl⟩ : syracuseStep 3335975 = 5003963) B5003963
theorem B144197657 : Blo 1315976 144197657 := bstep (se 2 (by rfl) ⟨54074121, by rfl⟩ : syracuseStep 144197657 = 108148243) B108148243
theorem B200198191 : Blo 1315976 200198191 := bstep (se 1 (by rfl) ⟨150148643, by rfl⟩ : syracuseStep 200198191 = 300297287) B300297287
theorem B10684487 : Blo 1315976 10684487 := bstep (se 1 (by rfl) ⟨8013365, by rfl⟩ : syracuseStep 10684487 = 16026731) B16026731
theorem B2500895 : Blo 1315976 2500895 := bstep (se 1 (by rfl) ⟨1875671, by rfl⟩ : syracuseStep 2500895 = 3751343) B3751343
theorem B4442849 : Blo 1315976 4442849 := bstep (se 2 (by rfl) ⟨1666068, by rfl⟩ : syracuseStep 4442849 = 3332137) B3332137
theorem B18975491 : Blo 1315976 18975491 := bstep (se 1 (by rfl) ⟨14231618, by rfl⟩ : syracuseStep 18975491 = 28463237) B28463237
theorem B25307963 : Blo 1315976 25307963 := bstep (se 1 (by rfl) ⟨18980972, by rfl⟩ : syracuseStep 25307963 = 37961945) B37961945
theorem B11251021 : Blo 1315976 11251021 := bstep (se 3 (by rfl) ⟨2109566, by rfl⟩ : syracuseStep 11251021 = 4219133) B4219133
theorem B16240027 : Blo 1315976 16240027 := bstep (se 1 (by rfl) ⟨12180020, by rfl⟩ : syracuseStep 16240027 = 24360041) B24360041
theorem B68431333 : Blo 1315976 68431333 := bstep (se 4 (by rfl) ⟨6415437, by rfl⟩ : syracuseStep 68431333 = 12830875) B12830875
theorem B2109311 : Blo 1315976 2109311 := bstep (se 1 (by rfl) ⟨1581983, by rfl⟩ : syracuseStep 2109311 = 3163967) B3163967
theorem B10006739 : Blo 1315976 10006739 := bstep (se 1 (by rfl) ⟨7505054, by rfl⟩ : syracuseStep 10006739 = 15010109) B15010109
theorem B3379439 : Blo 1315976 3379439 := bstep (se 1 (by rfl) ⟨2534579, by rfl⟩ : syracuseStep 3379439 = 5069159) B5069159
theorem B22499855 : Blo 1315976 22499855 := bstep (se 1 (by rfl) ⟨16874891, by rfl⟩ : syracuseStep 22499855 = 33749783) B33749783
theorem B7500863 : Blo 1315976 7500863 := bstep (se 1 (by rfl) ⟨5625647, by rfl⟩ : syracuseStep 7500863 = 11251295) B11251295
theorem B1316007 : Blo 1315976 1316007 := bstep (se 1 (by rfl) ⟨987005, by rfl⟩ : syracuseStep 1316007 = 1974011) B1974011
theorem B2962655 : Blo 1315976 2962655 := bstep (se 1 (by rfl) ⟨2221991, by rfl⟩ : syracuseStep 2962655 = 4443983) B4443983
theorem B6755609 : Blo 1315976 6755609 := bstep (se 2 (by rfl) ⟨2533353, by rfl⟩ : syracuseStep 6755609 = 5066707) B5066707
theorem B3380507 : Blo 1315976 3380507 := bstep (se 1 (by rfl) ⟨2535380, by rfl⟩ : syracuseStep 3380507 = 5070761) B5070761
theorem B4445495 : Blo 1315976 4445495 := bstep (se 1 (by rfl) ⟨3334121, by rfl⟩ : syracuseStep 4445495 = 6668243) B6668243
theorem B102585851 : Blo 1315976 102585851 := bstep (se 1 (by rfl) ⟨76939388, by rfl⟩ : syracuseStep 102585851 = 153878777) B153878777
theorem B14996987 : Blo 1315976 14996987 := bstep (se 1 (by rfl) ⟨11247740, by rfl⟩ : syracuseStep 14996987 = 22495481) B22495481
theorem B3610217 : Blo 1315976 3610217 := bstep (se 2 (by rfl) ⟨1353831, by rfl⟩ : syracuseStep 3610217 = 2707663) B2707663
theorem B1316559 : Blo 1315976 1316559 := bstep (se 1 (by rfl) ⟨987419, by rfl⟩ : syracuseStep 1316559 = 1974839) B1974839
theorem B18994985 : Blo 1315976 18994985 := bstep (se 2 (by rfl) ⟨7123119, by rfl⟩ : syracuseStep 18994985 = 14246239) B14246239
theorem B1316719 : Blo 1315976 1316719 := bstep (se 1 (by rfl) ⟨987539, by rfl⟩ : syracuseStep 1316719 = 1975079) B1975079
theorem B1316775 : Blo 1315976 1316775 := bstep (se 1 (by rfl) ⟨987581, by rfl⟩ : syracuseStep 1316775 = 1975163) B1975163
theorem B1480639 : Blo 1315976 1480639 := bstep (se 1 (by rfl) ⟨1110479, by rfl⟩ : syracuseStep 1480639 = 2220959) B2220959
theorem B1316799 : Blo 1315976 1316799 := bstep (se 1 (by rfl) ⟨987599, by rfl⟩ : syracuseStep 1316799 = 1975199) B1975199
theorem B1316859 : Blo 1315976 1316859 := bstep (se 1 (by rfl) ⟨987644, by rfl⟩ : syracuseStep 1316859 = 1975289) B1975289
theorem B11253755 : Blo 1315976 11253755 := bstep (se 1 (by rfl) ⟨8440316, by rfl⟩ : syracuseStep 11253755 = 16880633) B16880633
theorem B24041555 : Blo 1315976 24041555 := bstep (se 1 (by rfl) ⟨18031166, by rfl⟩ : syracuseStep 24041555 = 36062333) B36062333
theorem B72136889 : Blo 1315976 72136889 := bstep (se 2 (by rfl) ⟨27051333, by rfl⟩ : syracuseStep 72136889 = 54102667) B54102667
theorem B1480927 : Blo 1315976 1480927 := bstep (se 1 (by rfl) ⟨1110695, by rfl⟩ : syracuseStep 1480927 = 2221391) B2221391
theorem B1317087 : Blo 1315976 1317087 := bstep (se 1 (by rfl) ⟨987815, by rfl⟩ : syracuseStep 1317087 = 1975631) B1975631
theorem B1317119 : Blo 1315976 1317119 := bstep (se 1 (by rfl) ⟨987839, by rfl⟩ : syracuseStep 1317119 = 1975679) B1975679
theorem B1317247 : Blo 1315976 1317247 := bstep (se 1 (by rfl) ⟨987935, by rfl⟩ : syracuseStep 1317247 = 1975871) B1975871
theorem B7117193 : Blo 1315976 7117193 := bstep (se 2 (by rfl) ⟨2668947, by rfl⟩ : syracuseStep 7117193 = 5337895) B5337895
theorem B6756803 : Blo 1315976 6756803 := bstep (se 1 (by rfl) ⟨5067602, by rfl⟩ : syracuseStep 6756803 = 10135205) B10135205
theorem B1317487 : Blo 1315976 1317487 := bstep (se 1 (by rfl) ⟨988115, by rfl⟩ : syracuseStep 1317487 = 1976231) B1976231
theorem B1317567 : Blo 1315976 1317567 := bstep (se 1 (by rfl) ⟨988175, by rfl⟩ : syracuseStep 1317567 = 1976351) B1976351
theorem B54033389 : Blo 1315976 54033389 := bstep (se 3 (by rfl) ⟨10131260, by rfl⟩ : syracuseStep 54033389 = 20262521) B20262521
theorem B2964635 : Blo 1315976 2964635 := bstep (se 1 (by rfl) ⟨2223476, by rfl⟩ : syracuseStep 2964635 = 4446953) B4446953
theorem B3333383 : Blo 1315976 3333383 := bstep (se 1 (by rfl) ⟨2500037, by rfl⟩ : syracuseStep 3333383 = 5000075) B5000075
theorem B3333545 : Blo 1315976 3333545 := bstep (se 2 (by rfl) ⟨1250079, by rfl⟩ : syracuseStep 3333545 = 2500159) B2500159
theorem B2965211 : Blo 1315976 2965211 := bstep (se 1 (by rfl) ⟨2223908, by rfl⟩ : syracuseStep 2965211 = 4447817) B4447817
theorem B7495487 : Blo 1315976 7495487 := bstep (se 1 (by rfl) ⟨5621615, by rfl⟩ : syracuseStep 7495487 = 11243231) B11243231
theorem B8225027 : Blo 1315976 8225027 := bstep (se 1 (by rfl) ⟨6168770, by rfl⟩ : syracuseStep 8225027 = 12337541) B12337541
theorem B1974569 : Blo 1315976 1974569 := bstep (se 2 (by rfl) ⟨740463, by rfl⟩ : syracuseStep 1974569 = 1480927) B1480927
theorem B14999903 : Blo 1315976 14999903 := bstep (se 1 (by rfl) ⟨11249927, by rfl⟩ : syracuseStep 14999903 = 22499855) B22499855
theorem B6324743 : Blo 1315976 6324743 := bstep (se 1 (by rfl) ⟨4743557, by rfl⟩ : syracuseStep 6324743 = 9487115) B9487115
theorem B9011837 : Blo 1315976 9011837 := bstep (se 3 (by rfl) ⟨1689719, by rfl⟩ : syracuseStep 9011837 = 3379439) B3379439
theorem B18014957 : Blo 1315976 18014957 := bstep (se 3 (by rfl) ⟨3377804, by rfl⟩ : syracuseStep 18014957 = 6755609) B6755609
theorem B6669053 : Blo 1315976 6669053 := bstep (se 3 (by rfl) ⟨1250447, by rfl⟩ : syracuseStep 6669053 = 2500895) B2500895
theorem B1975103 : Blo 1315976 1975103 := bstep (se 1 (by rfl) ⟨1481327, by rfl⟩ : syracuseStep 1975103 = 2962655) B2962655
theorem B2253671 : Blo 1315976 2253671 := bstep (se 1 (by rfl) ⟨1690253, by rfl⟩ : syracuseStep 2253671 = 3380507) B3380507
theorem B9627245 : Blo 1315976 9627245 := bstep (se 3 (by rfl) ⟨1805108, by rfl⟩ : syracuseStep 9627245 = 3610217) B3610217
theorem B15001361 : Blo 1315976 15001361 := bstep (se 2 (by rfl) ⟨5625510, by rfl⟩ : syracuseStep 15001361 = 11251021) B11251021
theorem B12650327 : Blo 1315976 12650327 := bstep (se 1 (by rfl) ⟨9487745, by rfl⟩ : syracuseStep 12650327 = 18975491) B18975491
theorem B21653369 : Blo 1315976 21653369 := bstep (se 2 (by rfl) ⟨8120013, by rfl⟩ : syracuseStep 21653369 = 16240027) B16240027
theorem B3803105 : Blo 1315976 3803105 := bstep (se 2 (by rfl) ⟨1426164, by rfl⟩ : syracuseStep 3803105 = 2852329) B2852329
theorem B36022259 : Blo 1315976 36022259 := bstep (se 1 (by rfl) ⟨27016694, by rfl⟩ : syracuseStep 36022259 = 54033389) B54033389
theorem B1976423 : Blo 1315976 1976423 := bstep (se 1 (by rfl) ⟨1482317, by rfl⟩ : syracuseStep 1976423 = 2964635) B2964635
theorem B2222255 : Blo 1315976 2222255 := bstep (se 1 (by rfl) ⟨1666691, by rfl⟩ : syracuseStep 2222255 = 3333383) B3333383
theorem B2222363 : Blo 1315976 2222363 := bstep (se 1 (by rfl) ⟨1666772, by rfl⟩ : syracuseStep 2222363 = 3333545) B3333545
theorem B1976807 : Blo 1315976 1976807 := bstep (se 1 (by rfl) ⟨1482605, by rfl⟩ : syracuseStep 1976807 = 2965211) B2965211
theorem B266930921 : Blo 1315976 266930921 := bstep (se 2 (by rfl) ⟨100099095, by rfl⟩ : syracuseStep 266930921 = 200198191) B200198191
theorem B6671159 : Blo 1315976 6671159 := bstep (se 1 (by rfl) ⟨5003369, by rfl⟩ : syracuseStep 6671159 = 10006739) B10006739
theorem B2501867 : Blo 1315976 2501867 := bstep (se 1 (by rfl) ⟨1876400, by rfl⟩ : syracuseStep 2501867 = 3752801) B3752801
theorem B5000575 : Blo 1315976 5000575 := bstep (se 1 (by rfl) ⟨3750431, by rfl⟩ : syracuseStep 5000575 = 7500863) B7500863
theorem B33762905 : Blo 1315976 33762905 := bstep (se 2 (by rfl) ⟨12661089, by rfl⟩ : syracuseStep 33762905 = 25322179) B25322179
theorem B2960999 : Blo 1315976 2960999 := bstep (se 1 (by rfl) ⟨2220749, by rfl⟩ : syracuseStep 2960999 = 4441499) B4441499
theorem B68390567 : Blo 1315976 68390567 := bstep (se 1 (by rfl) ⟨51292925, by rfl⟩ : syracuseStep 68390567 = 102585851) B102585851
theorem B9997991 : Blo 1315976 9997991 := bstep (se 1 (by rfl) ⟨7498493, by rfl⟩ : syracuseStep 9997991 = 14996987) B14996987
theorem B2961161 : Blo 1315976 2961161 := bstep (se 2 (by rfl) ⟨1110435, by rfl⟩ : syracuseStep 2961161 = 2220871) B2220871
theorem B2223983 : Blo 1315976 2223983 := bstep (se 1 (by rfl) ⟨1667987, by rfl⟩ : syracuseStep 2223983 = 3335975) B3335975
theorem B7122991 : Blo 1315976 7122991 := bstep (se 1 (by rfl) ⟨5342243, by rfl⟩ : syracuseStep 7122991 = 10684487) B10684487
theorem B16027703 : Blo 1315976 16027703 := bstep (se 1 (by rfl) ⟨12020777, by rfl⟩ : syracuseStep 16027703 = 24041555) B24041555
theorem B48091259 : Blo 1315976 48091259 := bstep (se 1 (by rfl) ⟨36068444, by rfl⟩ : syracuseStep 48091259 = 72136889) B72136889
theorem B2961899 : Blo 1315976 2961899 := bstep (se 1 (by rfl) ⟨2221424, by rfl⟩ : syracuseStep 2961899 = 4442849) B4442849
theorem B16871975 : Blo 1315976 16871975 := bstep (se 1 (by rfl) ⟨12653981, by rfl⟩ : syracuseStep 16871975 = 25307963) B25307963
theorem B2962025 : Blo 1315976 2962025 := bstep (se 2 (by rfl) ⟨1110759, by rfl⟩ : syracuseStep 2962025 = 2221519) B2221519
theorem B1406207 : Blo 1315976 1406207 := bstep (se 1 (by rfl) ⟨1054655, by rfl⟩ : syracuseStep 1406207 = 2109311) B2109311
theorem B5002991 : Blo 1315976 5002991 := bstep (se 1 (by rfl) ⟨3752243, by rfl⟩ : syracuseStep 5002991 = 7504487) B7504487
theorem B5625683 : Blo 1315976 5625683 := bstep (se 1 (by rfl) ⟨4219262, by rfl⟩ : syracuseStep 5625683 = 8438525) B8438525
theorem B2963663 : Blo 1315976 2963663 := bstep (se 1 (by rfl) ⟨2222747, by rfl⟩ : syracuseStep 2963663 = 4445495) B4445495
theorem B1317103 : Blo 1315976 1317103 := bstep (se 1 (by rfl) ⟨987827, by rfl⟩ : syracuseStep 1317103 = 1975655) B1975655
theorem B18979181 : Blo 1315976 18979181 := bstep (se 3 (by rfl) ⟨3558596, by rfl⟩ : syracuseStep 18979181 = 7117193) B7117193
theorem B12663323 : Blo 1315976 12663323 := bstep (se 1 (by rfl) ⟨9497492, by rfl⟩ : syracuseStep 12663323 = 18994985) B18994985
theorem B7502503 : Blo 1315976 7502503 := bstep (se 1 (by rfl) ⟨5626877, by rfl⟩ : syracuseStep 7502503 = 11253755) B11253755
theorem B96131771 : Blo 1315976 96131771 := bstep (se 1 (by rfl) ⟨72098828, by rfl⟩ : syracuseStep 96131771 = 144197657) B144197657
theorem B4504535 : Blo 1315976 4504535 := bstep (se 1 (by rfl) ⟨3378401, by rfl⟩ : syracuseStep 4504535 = 6756803) B6756803
theorem B91241777 : Blo 1315976 91241777 := bstep (se 2 (by rfl) ⟨34215666, by rfl⟩ : syracuseStep 91241777 = 68431333) B68431333
theorem B4996991 : Blo 1315976 4996991 := bstep (se 1 (by rfl) ⟨3747743, by rfl⟩ : syracuseStep 4996991 = 7495487) B7495487
theorem B1974185 : Blo 1315976 1974185 := bstep (se 2 (by rfl) ⟨740319, by rfl⟩ : syracuseStep 1974185 = 1480639) B1480639
theorem B1974599 : Blo 1315976 1974599 := bstep (se 1 (by rfl) ⟨1480949, by rfl⟩ : syracuseStep 1974599 = 2961899) B2961899
theorem B11247983 : Blo 1315976 11247983 := bstep (se 1 (by rfl) ⟨8435987, by rfl⟩ : syracuseStep 11247983 = 16871975) B16871975
theorem B1974683 : Blo 1315976 1974683 := bstep (se 1 (by rfl) ⟨1481012, by rfl⟩ : syracuseStep 1974683 = 2962025) B2962025
theorem B12009971 : Blo 1315976 12009971 := bstep (se 1 (by rfl) ⟨9007478, by rfl⟩ : syracuseStep 12009971 = 18014957) B18014957
theorem B10003337 : Blo 1315976 10003337 := bstep (se 2 (by rfl) ⟨3751251, by rfl⟩ : syracuseStep 10003337 = 7502503) B7502503
theorem B3335327 : Blo 1315976 3335327 := bstep (se 1 (by rfl) ⟨2501495, by rfl⟩ : syracuseStep 3335327 = 5002991) B5002991
theorem B14435579 : Blo 1315976 14435579 := bstep (se 1 (by rfl) ⟨10826684, by rfl⟩ : syracuseStep 14435579 = 21653369) B21653369
theorem B1975775 : Blo 1315976 1975775 := bstep (se 1 (by rfl) ⟨1481831, by rfl⟩ : syracuseStep 1975775 = 2963663) B2963663
theorem B64087847 : Blo 1315976 64087847 := bstep (se 1 (by rfl) ⟨48065885, by rfl⟩ : syracuseStep 64087847 = 96131771) B96131771
theorem B60827851 : Blo 1315976 60827851 := bstep (se 1 (by rfl) ⟨45620888, by rfl⟩ : syracuseStep 60827851 = 91241777) B91241777
theorem B10685135 : Blo 1315976 10685135 := bstep (se 1 (by rfl) ⟨8013851, by rfl⟩ : syracuseStep 10685135 = 16027703) B16027703
theorem B9497321 : Blo 1315976 9497321 := bstep (se 2 (by rfl) ⟨3561495, by rfl⟩ : syracuseStep 9497321 = 7122991) B7122991
theorem B5483351 : Blo 1315976 5483351 := bstep (se 1 (by rfl) ⟨4112513, by rfl⟩ : syracuseStep 5483351 = 8225027) B8225027
theorem B6007891 : Blo 1315976 6007891 := bstep (se 1 (by rfl) ⟨4505918, by rfl⟩ : syracuseStep 6007891 = 9011837) B9011837
theorem B1502447 : Blo 1315976 1502447 := bstep (se 1 (by rfl) ⟨1126835, by rfl⟩ : syracuseStep 1502447 = 2253671) B2253671
theorem B6671645 : Blo 1315976 6671645 := bstep (se 3 (by rfl) ⟨1250933, by rfl⟩ : syracuseStep 6671645 = 2501867) B2501867
theorem B6418163 : Blo 1315976 6418163 := bstep (se 1 (by rfl) ⟨4813622, by rfl⟩ : syracuseStep 6418163 = 9627245) B9627245
theorem B8433551 : Blo 1315976 8433551 := bstep (se 1 (by rfl) ⟨6325163, by rfl⟩ : syracuseStep 8433551 = 12650327) B12650327
theorem B2535403 : Blo 1315976 2535403 := bstep (se 1 (by rfl) ⟨1901552, by rfl⟩ : syracuseStep 2535403 = 3803105) B3803105
theorem B24014839 : Blo 1315976 24014839 := bstep (se 1 (by rfl) ⟨18011129, by rfl⟩ : syracuseStep 24014839 = 36022259) B36022259
theorem B12652787 : Blo 1315976 12652787 := bstep (se 1 (by rfl) ⟨9489590, by rfl⟩ : syracuseStep 12652787 = 18979181) B18979181
theorem B8442215 : Blo 1315976 8442215 := bstep (se 1 (by rfl) ⟨6331661, by rfl⟩ : syracuseStep 8442215 = 12663323) B12663323
theorem B711815789 : Blo 1315976 711815789 := bstep (se 3 (by rfl) ⟨133465460, by rfl⟩ : syracuseStep 711815789 = 266930921) B266930921
theorem B3003023 : Blo 1315976 3003023 := bstep (se 1 (by rfl) ⟨2252267, by rfl⟩ : syracuseStep 3003023 = 4504535) B4504535
theorem B22508603 : Blo 1315976 22508603 := bstep (se 1 (by rfl) ⟨16881452, by rfl⟩ : syracuseStep 22508603 = 33762905) B33762905
theorem B45593711 : Blo 1315976 45593711 := bstep (se 1 (by rfl) ⟨34195283, by rfl⟩ : syracuseStep 45593711 = 68390567) B68390567
theorem B6665327 : Blo 1315976 6665327 := bstep (se 1 (by rfl) ⟨4998995, by rfl⟩ : syracuseStep 6665327 = 9997991) B9997991
theorem B3331327 : Blo 1315976 3331327 := bstep (se 1 (by rfl) ⟨2498495, by rfl⟩ : syracuseStep 3331327 = 4996991) B4996991
theorem B1316123 : Blo 1315976 1316123 := bstep (se 1 (by rfl) ⟨987092, by rfl⟩ : syracuseStep 1316123 = 1974185) B1974185
theorem B1316379 : Blo 1315976 1316379 := bstep (se 1 (by rfl) ⟨987284, by rfl⟩ : syracuseStep 1316379 = 1974569) B1974569
theorem B9999935 : Blo 1315976 9999935 := bstep (se 1 (by rfl) ⟨7499951, by rfl⟩ : syracuseStep 9999935 = 14999903) B14999903
theorem B128243357 : Blo 1315976 128243357 := bstep (se 3 (by rfl) ⟨24045629, by rfl⟩ : syracuseStep 128243357 = 48091259) B48091259
theorem B4216495 : Blo 1315976 4216495 := bstep (se 1 (by rfl) ⟨3162371, by rfl⟩ : syracuseStep 4216495 = 6324743) B6324743
theorem B4446035 : Blo 1315976 4446035 := bstep (se 1 (by rfl) ⟨3334526, by rfl⟩ : syracuseStep 4446035 = 6669053) B6669053
theorem B1316735 : Blo 1315976 1316735 := bstep (se 1 (by rfl) ⟨987551, by rfl⟩ : syracuseStep 1316735 = 1975103) B1975103
theorem B3749885 : Blo 1315976 3749885 := bstep (se 3 (by rfl) ⟨703103, by rfl⟩ : syracuseStep 3749885 = 1406207) B1406207
theorem B10000907 : Blo 1315976 10000907 := bstep (se 1 (by rfl) ⟨7500680, by rfl⟩ : syracuseStep 10000907 = 15001361) B15001361
theorem B3750455 : Blo 1315976 3750455 := bstep (se 1 (by rfl) ⟨2812841, by rfl⟩ : syracuseStep 3750455 = 5625683) B5625683
theorem B1317615 : Blo 1315976 1317615 := bstep (se 1 (by rfl) ⟨988211, by rfl⟩ : syracuseStep 1317615 = 1976423) B1976423
theorem B1481503 : Blo 1315976 1481503 := bstep (se 1 (by rfl) ⟨1111127, by rfl⟩ : syracuseStep 1481503 = 2222255) B2222255
theorem B1481575 : Blo 1315976 1481575 := bstep (se 1 (by rfl) ⟨1111181, by rfl⟩ : syracuseStep 1481575 = 2222363) B2222363
theorem B1317871 : Blo 1315976 1317871 := bstep (se 1 (by rfl) ⟨988403, by rfl⟩ : syracuseStep 1317871 = 1976807) B1976807
theorem B6667433 : Blo 1315976 6667433 := bstep (se 2 (by rfl) ⟨2500287, by rfl⟩ : syracuseStep 6667433 = 5000575) B5000575
theorem B4447439 : Blo 1315976 4447439 := bstep (se 1 (by rfl) ⟨3335579, by rfl⟩ : syracuseStep 4447439 = 6671159) B6671159
theorem B1973999 : Blo 1315976 1973999 := bstep (se 1 (by rfl) ⟨1480499, by rfl⟩ : syracuseStep 1973999 = 2960999) B2960999
theorem B1974107 : Blo 1315976 1974107 := bstep (se 1 (by rfl) ⟨1480580, by rfl⟩ : syracuseStep 1974107 = 2961161) B2961161
theorem B1482655 : Blo 1315976 1482655 := bstep (se 1 (by rfl) ⟨1111991, by rfl⟩ : syracuseStep 1482655 = 2223983) B2223983
theorem B5628143 : Blo 1315976 5628143 := bstep (se 1 (by rfl) ⟨4221107, by rfl⟩ : syracuseStep 5628143 = 8442215) B8442215
theorem B6668891 : Blo 1315976 6668891 := bstep (se 1 (by rfl) ⟨5001668, by rfl⟩ : syracuseStep 6668891 = 10003337) B10003337
theorem B4006525 : Blo 1315976 4006525 := bstep (se 3 (by rfl) ⟨751223, by rfl⟩ : syracuseStep 4006525 = 1502447) B1502447
theorem B1975337 : Blo 1315976 1975337 := bstep (se 2 (by rfl) ⟨740751, by rfl⟩ : syracuseStep 1975337 = 1481503) B1481503
theorem B1975433 : Blo 1315976 1975433 := bstep (se 2 (by rfl) ⟨740787, by rfl⟩ : syracuseStep 1975433 = 1481575) B1481575
theorem B2499923 : Blo 1315976 2499923 := bstep (se 1 (by rfl) ⟨1874942, by rfl⟩ : syracuseStep 2499923 = 3749885) B3749885
theorem B4441769 : Blo 1315976 4441769 := bstep (se 2 (by rfl) ⟨1665663, by rfl⟩ : syracuseStep 4441769 = 3331327) B3331327
theorem B2500303 : Blo 1315976 2500303 := bstep (se 1 (by rfl) ⟨1875227, by rfl⟩ : syracuseStep 2500303 = 3750455) B3750455
theorem B3655567 : Blo 1315976 3655567 := bstep (se 1 (by rfl) ⟨2741675, by rfl⟩ : syracuseStep 3655567 = 5483351) B5483351
theorem B17115101 : Blo 1315976 17115101 := bstep (se 3 (by rfl) ⟨3209081, by rfl⟩ : syracuseStep 17115101 = 6418163) B6418163
theorem B5621993 : Blo 1315976 5621993 := bstep (se 2 (by rfl) ⟨2108247, by rfl⟩ : syracuseStep 5621993 = 4216495) B4216495
theorem B1976873 : Blo 1315976 1976873 := bstep (se 2 (by rfl) ⟨741327, by rfl⟩ : syracuseStep 1976873 = 1482655) B1482655
theorem B5622367 : Blo 1315976 5622367 := bstep (se 1 (by rfl) ⟨4216775, by rfl⟩ : syracuseStep 5622367 = 8433551) B8433551
theorem B7498655 : Blo 1315976 7498655 := bstep (se 1 (by rfl) ⟨5623991, by rfl⟩ : syracuseStep 7498655 = 11247983) B11247983
theorem B81103801 : Blo 1315976 81103801 := bstep (se 2 (by rfl) ⟨30413925, by rfl⟩ : syracuseStep 81103801 = 60827851) B60827851
theorem B2002015 : Blo 1315976 2002015 := bstep (se 1 (by rfl) ⟨1501511, by rfl⟩ : syracuseStep 2002015 = 3003023) B3003023
theorem B30395807 : Blo 1315976 30395807 := bstep (se 1 (by rfl) ⟨22796855, by rfl⟩ : syracuseStep 30395807 = 45593711) B45593711
theorem B4443551 : Blo 1315976 4443551 := bstep (se 1 (by rfl) ⟨3332663, by rfl⟩ : syracuseStep 4443551 = 6665327) B6665327
theorem B2223551 : Blo 1315976 2223551 := bstep (se 1 (by rfl) ⟨1667663, by rfl⟩ : syracuseStep 2223551 = 3335327) B3335327
theorem B85495571 : Blo 1315976 85495571 := bstep (se 1 (by rfl) ⟨64121678, by rfl⟩ : syracuseStep 85495571 = 128243357) B128243357
theorem B42725231 : Blo 1315976 42725231 := bstep (se 1 (by rfl) ⟨32043923, by rfl⟩ : syracuseStep 42725231 = 64087847) B64087847
theorem B32026589 : Blo 1315976 32026589 := bstep (se 3 (by rfl) ⟨6004985, by rfl⟩ : syracuseStep 32026589 = 12009971) B12009971
theorem B7123423 : Blo 1315976 7123423 := bstep (se 1 (by rfl) ⟨5342567, by rfl⟩ : syracuseStep 7123423 = 10685135) B10685135
theorem B4444955 : Blo 1315976 4444955 := bstep (se 1 (by rfl) ⟨3333716, by rfl⟩ : syracuseStep 4444955 = 6667433) B6667433
theorem B1315999 : Blo 1315976 1315999 := bstep (se 1 (by rfl) ⟨986999, by rfl⟩ : syracuseStep 1315999 = 1973999) B1973999
theorem B1316071 : Blo 1315976 1316071 := bstep (se 1 (by rfl) ⟨987053, by rfl⟩ : syracuseStep 1316071 = 1974107) B1974107
theorem B3380537 : Blo 1315976 3380537 := bstep (se 2 (by rfl) ⟨1267701, by rfl⟩ : syracuseStep 3380537 = 2535403) B2535403
theorem B32019785 : Blo 1315976 32019785 := bstep (se 2 (by rfl) ⟨12007419, by rfl⟩ : syracuseStep 32019785 = 24014839) B24014839
theorem B8435191 : Blo 1315976 8435191 := bstep (se 1 (by rfl) ⟨6326393, by rfl⟩ : syracuseStep 8435191 = 12652787) B12652787
theorem B1316399 : Blo 1315976 1316399 := bstep (se 1 (by rfl) ⟨987299, by rfl⟩ : syracuseStep 1316399 = 1974599) B1974599
theorem B1316455 : Blo 1315976 1316455 := bstep (se 1 (by rfl) ⟨987341, by rfl⟩ : syracuseStep 1316455 = 1974683) B1974683
theorem B474543859 : Blo 1315976 474543859 := bstep (se 1 (by rfl) ⟨355907894, by rfl⟩ : syracuseStep 474543859 = 711815789) B711815789
theorem B15005735 : Blo 1315976 15005735 := bstep (se 1 (by rfl) ⟨11254301, by rfl⟩ : syracuseStep 15005735 = 22508603) B22508603
theorem B9623719 : Blo 1315976 9623719 := bstep (se 1 (by rfl) ⟨7217789, by rfl⟩ : syracuseStep 9623719 = 14435579) B14435579
theorem B1317183 : Blo 1315976 1317183 := bstep (se 1 (by rfl) ⟨987887, by rfl⟩ : syracuseStep 1317183 = 1975775) B1975775
theorem B6666623 : Blo 1315976 6666623 := bstep (se 1 (by rfl) ⟨4999967, by rfl⟩ : syracuseStep 6666623 = 9999935) B9999935
theorem B2964023 : Blo 1315976 2964023 := bstep (se 1 (by rfl) ⟨2223017, by rfl⟩ : syracuseStep 2964023 = 4446035) B4446035
theorem B8010521 : Blo 1315976 8010521 := bstep (se 2 (by rfl) ⟨3003945, by rfl⟩ : syracuseStep 8010521 = 6007891) B6007891
theorem B6667271 : Blo 1315976 6667271 := bstep (se 1 (by rfl) ⟨5000453, by rfl⟩ : syracuseStep 6667271 = 10000907) B10000907
theorem B6331547 : Blo 1315976 6331547 := bstep (se 1 (by rfl) ⟨4748660, by rfl⟩ : syracuseStep 6331547 = 9497321) B9497321
theorem B2964959 : Blo 1315976 2964959 := bstep (se 1 (by rfl) ⟨2223719, by rfl⟩ : syracuseStep 2964959 = 4447439) B4447439
theorem B4447763 : Blo 1315976 4447763 := bstep (se 1 (by rfl) ⟨3335822, by rfl⟩ : syracuseStep 4447763 = 6671645) B6671645
theorem B3752095 : Blo 1315976 3752095 := bstep (se 1 (by rfl) ⟨2814071, by rfl⟩ : syracuseStep 3752095 = 5628143) B5628143
theorem B7496489 : Blo 1315976 7496489 := bstep (se 2 (by rfl) ⟨2811183, by rfl⟩ : syracuseStep 7496489 = 5622367) B5622367
theorem B5342033 : Blo 1315976 5342033 := bstep (se 2 (by rfl) ⟨2003262, by rfl⟩ : syracuseStep 5342033 = 4006525) B4006525
theorem B2253691 : Blo 1315976 2253691 := bstep (se 1 (by rfl) ⟨1690268, by rfl⟩ : syracuseStep 2253691 = 3380537) B3380537
theorem B10003823 : Blo 1315976 10003823 := bstep (se 1 (by rfl) ⟨7502867, by rfl⟩ : syracuseStep 10003823 = 15005735) B15005735
theorem B1976015 : Blo 1315976 1976015 := bstep (se 1 (by rfl) ⟨1482011, by rfl⟩ : syracuseStep 1976015 = 2964023) B2964023
theorem B4999103 : Blo 1315976 4999103 := bstep (se 1 (by rfl) ⟨3749327, by rfl⟩ : syracuseStep 4999103 = 7498655) B7498655
theorem B4221031 : Blo 1315976 4221031 := bstep (se 1 (by rfl) ⟨3165773, by rfl⟩ : syracuseStep 4221031 = 6331547) B6331547
theorem B1976639 : Blo 1315976 1976639 := bstep (se 1 (by rfl) ⟨1482479, by rfl⟩ : syracuseStep 1976639 = 2964959) B2964959
theorem B21351059 : Blo 1315976 21351059 := bstep (se 1 (by rfl) ⟨16013294, by rfl⟩ : syracuseStep 21351059 = 32026589) B32026589
theorem B12831625 : Blo 1315976 12831625 := bstep (se 2 (by rfl) ⟨4811859, by rfl⟩ : syracuseStep 12831625 = 9623719) B9623719
theorem B10677413 : Blo 1315976 10677413 := bstep (se 4 (by rfl) ⟨1001007, by rfl⟩ : syracuseStep 10677413 = 2002015) B2002015
theorem B9497897 : Blo 1315976 9497897 := bstep (se 2 (by rfl) ⟨3561711, by rfl⟩ : syracuseStep 9497897 = 7123423) B7123423
theorem B2961179 : Blo 1315976 2961179 := bstep (se 1 (by rfl) ⟨2220884, by rfl⟩ : syracuseStep 2961179 = 4441769) B4441769
theorem B108138401 : Blo 1315976 108138401 := bstep (se 2 (by rfl) ⟨40551900, by rfl⟩ : syracuseStep 108138401 = 81103801) B81103801
theorem B3747995 : Blo 1315976 3747995 := bstep (se 1 (by rfl) ⟨2810996, by rfl⟩ : syracuseStep 3747995 = 5621993) B5621993
theorem B4444415 : Blo 1315976 4444415 := bstep (se 1 (by rfl) ⟨3333311, by rfl⟩ : syracuseStep 4444415 = 6666623) B6666623
theorem B4444847 : Blo 1315976 4444847 := bstep (se 1 (by rfl) ⟨3333635, by rfl⟩ : syracuseStep 4444847 = 6667271) B6667271
theorem B20263871 : Blo 1315976 20263871 := bstep (se 1 (by rfl) ⟨15197903, by rfl⟩ : syracuseStep 20263871 = 30395807) B30395807
theorem B2962367 : Blo 1315976 2962367 := bstep (se 1 (by rfl) ⟨2221775, by rfl⟩ : syracuseStep 2962367 = 4443551) B4443551
theorem B56997047 : Blo 1315976 56997047 := bstep (se 1 (by rfl) ⟨42747785, by rfl⟩ : syracuseStep 56997047 = 85495571) B85495571
theorem B4445927 : Blo 1315976 4445927 := bstep (se 1 (by rfl) ⟨3334445, by rfl⟩ : syracuseStep 4445927 = 6668891) B6668891
theorem B2963303 : Blo 1315976 2963303 := bstep (se 1 (by rfl) ⟨2222477, by rfl⟩ : syracuseStep 2963303 = 4444955) B4444955
theorem B1316891 : Blo 1315976 1316891 := bstep (se 1 (by rfl) ⟨987668, by rfl⟩ : syracuseStep 1316891 = 1975337) B1975337
theorem B1316955 : Blo 1315976 1316955 := bstep (se 1 (by rfl) ⟨987716, by rfl⟩ : syracuseStep 1316955 = 1975433) B1975433
theorem B21346523 : Blo 1315976 21346523 := bstep (se 1 (by rfl) ⟨16009892, by rfl⟩ : syracuseStep 21346523 = 32019785) B32019785
theorem B6666461 : Blo 1315976 6666461 := bstep (se 3 (by rfl) ⟨1249961, by rfl⟩ : syracuseStep 6666461 = 2499923) B2499923
theorem B11410067 : Blo 1315976 11410067 := bstep (se 1 (by rfl) ⟨8557550, by rfl⟩ : syracuseStep 11410067 = 17115101) B17115101
theorem B1317915 : Blo 1315976 1317915 := bstep (se 1 (by rfl) ⟨988436, by rfl⟩ : syracuseStep 1317915 = 1976873) B1976873
theorem B5340347 : Blo 1315976 5340347 := bstep (se 1 (by rfl) ⟨4005260, by rfl⟩ : syracuseStep 5340347 = 8010521) B8010521
theorem B11246921 : Blo 1315976 11246921 := bstep (se 2 (by rfl) ⟨4217595, by rfl⟩ : syracuseStep 11246921 = 8435191) B8435191
theorem B3333737 : Blo 1315976 3333737 := bstep (se 2 (by rfl) ⟨1250151, by rfl⟩ : syracuseStep 3333737 = 2500303) B2500303
theorem B1482367 : Blo 1315976 1482367 := bstep (se 1 (by rfl) ⟨1111775, by rfl⟩ : syracuseStep 1482367 = 2223551) B2223551
theorem B632725145 : Blo 1315976 632725145 := bstep (se 2 (by rfl) ⟨237271929, by rfl⟩ : syracuseStep 632725145 = 474543859) B474543859
theorem B2965175 : Blo 1315976 2965175 := bstep (se 1 (by rfl) ⟨2223881, by rfl⟩ : syracuseStep 2965175 = 4447763) B4447763
theorem B4874089 : Blo 1315976 4874089 := bstep (se 2 (by rfl) ⟨1827783, by rfl⟩ : syracuseStep 4874089 = 3655567) B3655567
theorem B28483487 : Blo 1315976 28483487 := bstep (se 1 (by rfl) ⟨21362615, by rfl⟩ : syracuseStep 28483487 = 42725231) B42725231
theorem B2498663 : Blo 1315976 2498663 := bstep (se 1 (by rfl) ⟨1873997, by rfl⟩ : syracuseStep 2498663 = 3747995) B3747995
theorem B5628041 : Blo 1315976 5628041 := bstep (se 2 (by rfl) ⟨2110515, by rfl⟩ : syracuseStep 5628041 = 4221031) B4221031
theorem B4997659 : Blo 1315976 4997659 := bstep (se 1 (by rfl) ⟨3748244, by rfl⟩ : syracuseStep 4997659 = 7496489) B7496489
theorem B1974911 : Blo 1315976 1974911 := bstep (se 1 (by rfl) ⟨1481183, by rfl⟩ : syracuseStep 1974911 = 2962367) B2962367
theorem B6669215 : Blo 1315976 6669215 := bstep (se 1 (by rfl) ⟨5001911, by rfl⟩ : syracuseStep 6669215 = 10003823) B10003823
theorem B1975535 : Blo 1315976 1975535 := bstep (se 1 (by rfl) ⟨1481651, by rfl⟩ : syracuseStep 1975535 = 2963303) B2963303
theorem B14231015 : Blo 1315976 14231015 := bstep (se 1 (by rfl) ⟨10673261, by rfl⟩ : syracuseStep 14231015 = 21346523) B21346523
theorem B1976489 : Blo 1315976 1976489 := bstep (se 2 (by rfl) ⟨741183, by rfl⟩ : syracuseStep 1976489 = 1482367) B1482367
theorem B7497947 : Blo 1315976 7497947 := bstep (se 1 (by rfl) ⟨5623460, by rfl⟩ : syracuseStep 7497947 = 11246921) B11246921
theorem B2222491 : Blo 1315976 2222491 := bstep (se 1 (by rfl) ⟨1666868, by rfl⟩ : syracuseStep 2222491 = 3333737) B3333737
theorem B421816763 : Blo 1315976 421816763 := bstep (se 1 (by rfl) ⟨316362572, by rfl⟩ : syracuseStep 421816763 = 632725145) B632725145
theorem B1976783 : Blo 1315976 1976783 := bstep (se 1 (by rfl) ⟨1482587, by rfl⟩ : syracuseStep 1976783 = 2965175) B2965175
theorem B6498785 : Blo 1315976 6498785 := bstep (se 2 (by rfl) ⟨2437044, by rfl⟩ : syracuseStep 6498785 = 4874089) B4874089
theorem B54036989 : Blo 1315976 54036989 := bstep (se 3 (by rfl) ⟨10131935, by rfl⟩ : syracuseStep 54036989 = 20263871) B20263871
theorem B72092267 : Blo 1315976 72092267 := bstep (se 1 (by rfl) ⟨54069200, by rfl⟩ : syracuseStep 72092267 = 108138401) B108138401
theorem B37998031 : Blo 1315976 37998031 := bstep (se 1 (by rfl) ⟨28498523, by rfl⟩ : syracuseStep 37998031 = 56997047) B56997047
theorem B17108833 : Blo 1315976 17108833 := bstep (se 2 (by rfl) ⟨6415812, by rfl⟩ : syracuseStep 17108833 = 12831625) B12831625
theorem B4444307 : Blo 1315976 4444307 := bstep (se 1 (by rfl) ⟨3333230, by rfl⟩ : syracuseStep 4444307 = 6666461) B6666461
theorem B14234039 : Blo 1315976 14234039 := bstep (se 1 (by rfl) ⟨10675529, by rfl⟩ : syracuseStep 14234039 = 21351059) B21351059
theorem B7606711 : Blo 1315976 7606711 := bstep (se 1 (by rfl) ⟨5705033, by rfl⟩ : syracuseStep 7606711 = 11410067) B11410067
theorem B3560231 : Blo 1315976 3560231 := bstep (se 1 (by rfl) ⟨2670173, by rfl⟩ : syracuseStep 3560231 = 5340347) B5340347
theorem B2962943 : Blo 1315976 2962943 := bstep (se 1 (by rfl) ⟨2222207, by rfl⟩ : syracuseStep 2962943 = 4444415) B4444415
theorem B5002793 : Blo 1315976 5002793 := bstep (se 2 (by rfl) ⟨1876047, by rfl⟩ : syracuseStep 5002793 = 3752095) B3752095
theorem B2963231 : Blo 1315976 2963231 := bstep (se 1 (by rfl) ⟨2222423, by rfl⟩ : syracuseStep 2963231 = 4444847) B4444847
theorem B3561355 : Blo 1315976 3561355 := bstep (se 1 (by rfl) ⟨2671016, by rfl⟩ : syracuseStep 3561355 = 5342033) B5342033
theorem B1317343 : Blo 1315976 1317343 := bstep (se 1 (by rfl) ⟨988007, by rfl⟩ : syracuseStep 1317343 = 1976015) B1976015
theorem B2963951 : Blo 1315976 2963951 := bstep (se 1 (by rfl) ⟨2222963, by rfl⟩ : syracuseStep 2963951 = 4445927) B4445927
theorem B3004921 : Blo 1315976 3004921 := bstep (se 2 (by rfl) ⟨1126845, by rfl⟩ : syracuseStep 3004921 = 2253691) B2253691
theorem B3332735 : Blo 1315976 3332735 := bstep (se 1 (by rfl) ⟨2499551, by rfl⟩ : syracuseStep 3332735 = 4999103) B4999103
theorem B1317759 : Blo 1315976 1317759 := bstep (se 1 (by rfl) ⟨988319, by rfl⟩ : syracuseStep 1317759 = 1976639) B1976639
theorem B7118275 : Blo 1315976 7118275 := bstep (se 1 (by rfl) ⟨5338706, by rfl⟩ : syracuseStep 7118275 = 10677413) B10677413
theorem B6331931 : Blo 1315976 6331931 := bstep (se 1 (by rfl) ⟨4748948, by rfl⟩ : syracuseStep 6331931 = 9497897) B9497897
theorem B1974119 : Blo 1315976 1974119 := bstep (se 1 (by rfl) ⟨1480589, by rfl⟩ : syracuseStep 1974119 = 2961179) B2961179
theorem B18988991 : Blo 1315976 18988991 := bstep (se 1 (by rfl) ⟨14241743, by rfl⟩ : syracuseStep 18988991 = 28483487) B28483487
theorem B3752027 : Blo 1315976 3752027 := bstep (se 1 (by rfl) ⟨2814020, by rfl⟩ : syracuseStep 3752027 = 5628041) B5628041
theorem B10142281 : Blo 1315976 10142281 := bstep (se 2 (by rfl) ⟨3803355, by rfl⟩ : syracuseStep 10142281 = 7606711) B7606711
theorem B9487343 : Blo 1315976 9487343 := bstep (se 1 (by rfl) ⟨7115507, by rfl⟩ : syracuseStep 9487343 = 14231015) B14231015
theorem B1975295 : Blo 1315976 1975295 := bstep (se 1 (by rfl) ⟨1481471, by rfl⟩ : syracuseStep 1975295 = 2962943) B2962943
theorem B3335195 : Blo 1315976 3335195 := bstep (se 1 (by rfl) ⟨2501396, by rfl⟩ : syracuseStep 3335195 = 5002793) B5002793
theorem B1975487 : Blo 1315976 1975487 := bstep (se 1 (by rfl) ⟨1481615, by rfl⟩ : syracuseStep 1975487 = 2963231) B2963231
theorem B4998631 : Blo 1315976 4998631 := bstep (se 1 (by rfl) ⟨3748973, by rfl⟩ : syracuseStep 4998631 = 7497947) B7497947
theorem B1975967 : Blo 1315976 1975967 := bstep (se 1 (by rfl) ⟨1481975, by rfl⟩ : syracuseStep 1975967 = 2963951) B2963951
theorem B2221823 : Blo 1315976 2221823 := bstep (se 1 (by rfl) ⟨1666367, by rfl⟩ : syracuseStep 2221823 = 3332735) B3332735
theorem B4221287 : Blo 1315976 4221287 := bstep (se 1 (by rfl) ⟨3165965, by rfl⟩ : syracuseStep 4221287 = 6331931) B6331931
theorem B12659327 : Blo 1315976 12659327 := bstep (se 1 (by rfl) ⟨9494495, by rfl⟩ : syracuseStep 12659327 = 18988991) B18988991
theorem B16026245 : Blo 1315976 16026245 := bstep (se 4 (by rfl) ⟨1502460, by rfl⟩ : syracuseStep 16026245 = 3004921) B3004921
theorem B1665775 : Blo 1315976 1665775 := bstep (se 1 (by rfl) ⟨1249331, by rfl⟩ : syracuseStep 1665775 = 2498663) B2498663
theorem B9489359 : Blo 1315976 9489359 := bstep (se 1 (by rfl) ⟨7117019, by rfl⟩ : syracuseStep 9489359 = 14234039) B14234039
theorem B6663545 : Blo 1315976 6663545 := bstep (se 2 (by rfl) ⟨2498829, by rfl⟩ : syracuseStep 6663545 = 4997659) B4997659
theorem B281211175 : Blo 1315976 281211175 := bstep (se 1 (by rfl) ⟨210908381, by rfl⟩ : syracuseStep 281211175 = 421816763) B421816763
theorem B36024659 : Blo 1315976 36024659 := bstep (se 1 (by rfl) ⟨27018494, by rfl⟩ : syracuseStep 36024659 = 54036989) B54036989
theorem B9491033 : Blo 1315976 9491033 := bstep (se 2 (by rfl) ⟨3559137, by rfl⟩ : syracuseStep 9491033 = 7118275) B7118275
theorem B50664041 : Blo 1315976 50664041 := bstep (se 2 (by rfl) ⟨18999015, by rfl⟩ : syracuseStep 50664041 = 37998031) B37998031
theorem B22811777 : Blo 1315976 22811777 := bstep (se 2 (by rfl) ⟨8554416, by rfl⟩ : syracuseStep 22811777 = 17108833) B17108833
theorem B4748473 : Blo 1315976 4748473 := bstep (se 2 (by rfl) ⟨1780677, by rfl⟩ : syracuseStep 4748473 = 3561355) B3561355
theorem B1316079 : Blo 1315976 1316079 := bstep (se 1 (by rfl) ⟨987059, by rfl⟩ : syracuseStep 1316079 = 1974119) B1974119
theorem B2962871 : Blo 1315976 2962871 := bstep (se 1 (by rfl) ⟨2222153, by rfl⟩ : syracuseStep 2962871 = 4444307) B4444307
theorem B1316607 : Blo 1315976 1316607 := bstep (se 1 (by rfl) ⟨987455, by rfl⟩ : syracuseStep 1316607 = 1974911) B1974911
theorem B2963321 : Blo 1315976 2963321 := bstep (se 2 (by rfl) ⟨1111245, by rfl⟩ : syracuseStep 2963321 = 2222491) B2222491
theorem B4446143 : Blo 1315976 4446143 := bstep (se 1 (by rfl) ⟨3334607, by rfl⟩ : syracuseStep 4446143 = 6669215) B6669215
theorem B1317023 : Blo 1315976 1317023 := bstep (se 1 (by rfl) ⟨987767, by rfl⟩ : syracuseStep 1317023 = 1975535) B1975535
theorem B1317659 : Blo 1315976 1317659 := bstep (se 1 (by rfl) ⟨988244, by rfl⟩ : syracuseStep 1317659 = 1976489) B1976489
theorem B1317855 : Blo 1315976 1317855 := bstep (se 1 (by rfl) ⟨988391, by rfl⟩ : syracuseStep 1317855 = 1976783) B1976783
theorem B4332523 : Blo 1315976 4332523 := bstep (se 1 (by rfl) ⟨3249392, by rfl⟩ : syracuseStep 4332523 = 6498785) B6498785
theorem B48061511 : Blo 1315976 48061511 := bstep (se 1 (by rfl) ⟨36046133, by rfl⟩ : syracuseStep 48061511 = 72092267) B72092267
theorem B9493949 : Blo 1315976 9493949 := bstep (se 3 (by rfl) ⟨1780115, by rfl⟩ : syracuseStep 9493949 = 3560231) B3560231
theorem B374948233 : Blo 1315976 374948233 := bstep (se 2 (by rfl) ⟨140605587, by rfl⟩ : syracuseStep 374948233 = 281211175) B281211175
theorem B33776027 : Blo 1315976 33776027 := bstep (se 1 (by rfl) ⟨25332020, by rfl⟩ : syracuseStep 33776027 = 50664041) B50664041
theorem B6324895 : Blo 1315976 6324895 := bstep (se 1 (by rfl) ⟨4743671, by rfl⟩ : syracuseStep 6324895 = 9487343) B9487343
theorem B1975247 : Blo 1315976 1975247 := bstep (se 1 (by rfl) ⟨1481435, by rfl⟩ : syracuseStep 1975247 = 2962871) B2962871
theorem B2221033 : Blo 1315976 2221033 := bstep (se 2 (by rfl) ⟨832887, by rfl⟩ : syracuseStep 2221033 = 1665775) B1665775
theorem B1975547 : Blo 1315976 1975547 := bstep (se 1 (by rfl) ⟨1481660, by rfl⟩ : syracuseStep 1975547 = 2963321) B2963321
theorem B5776697 : Blo 1315976 5776697 := bstep (se 2 (by rfl) ⟨2166261, by rfl⟩ : syracuseStep 5776697 = 4332523) B4332523
theorem B8439551 : Blo 1315976 8439551 := bstep (se 1 (by rfl) ⟨6329663, by rfl⟩ : syracuseStep 8439551 = 12659327) B12659327
theorem B10684163 : Blo 1315976 10684163 := bstep (se 1 (by rfl) ⟨8013122, by rfl⟩ : syracuseStep 10684163 = 16026245) B16026245
theorem B32041007 : Blo 1315976 32041007 := bstep (se 1 (by rfl) ⟨24030755, by rfl⟩ : syracuseStep 32041007 = 48061511) B48061511
theorem B4442363 : Blo 1315976 4442363 := bstep (se 1 (by rfl) ⟨3331772, by rfl⟩ : syracuseStep 4442363 = 6663545) B6663545
theorem B2501351 : Blo 1315976 2501351 := bstep (se 1 (by rfl) ⟨1876013, by rfl⟩ : syracuseStep 2501351 = 3752027) B3752027
theorem B2223463 : Blo 1315976 2223463 := bstep (se 1 (by rfl) ⟨1667597, by rfl⟩ : syracuseStep 2223463 = 3335195) B3335195
theorem B15207851 : Blo 1315976 15207851 := bstep (se 1 (by rfl) ⟨11405888, by rfl⟩ : syracuseStep 15207851 = 22811777) B22811777
theorem B25309421 : Blo 1315976 25309421 := bstep (se 3 (by rfl) ⟨4745516, by rfl⟩ : syracuseStep 25309421 = 9491033) B9491033
theorem B2814191 : Blo 1315976 2814191 := bstep (se 1 (by rfl) ⟨2110643, by rfl⟩ : syracuseStep 2814191 = 4221287) B4221287
theorem B6664841 : Blo 1315976 6664841 := bstep (se 2 (by rfl) ⟨2499315, by rfl⟩ : syracuseStep 6664841 = 4998631) B4998631
theorem B6329299 : Blo 1315976 6329299 := bstep (se 1 (by rfl) ⟨4746974, by rfl⟩ : syracuseStep 6329299 = 9493949) B9493949
theorem B24016439 : Blo 1315976 24016439 := bstep (se 1 (by rfl) ⟨18012329, by rfl⟩ : syracuseStep 24016439 = 36024659) B36024659
theorem B1316863 : Blo 1315976 1316863 := bstep (se 1 (by rfl) ⟨987647, by rfl⟩ : syracuseStep 1316863 = 1975295) B1975295
theorem B13523041 : Blo 1315976 13523041 := bstep (se 2 (by rfl) ⟨5071140, by rfl⟩ : syracuseStep 13523041 = 10142281) B10142281
theorem B1316991 : Blo 1315976 1316991 := bstep (se 1 (by rfl) ⟨987743, by rfl⟩ : syracuseStep 1316991 = 1975487) B1975487
theorem B1317311 : Blo 1315976 1317311 := bstep (se 1 (by rfl) ⟨987983, by rfl⟩ : syracuseStep 1317311 = 1975967) B1975967
theorem B1481215 : Blo 1315976 1481215 := bstep (se 1 (by rfl) ⟨1110911, by rfl⟩ : syracuseStep 1481215 = 2221823) B2221823
theorem B2964095 : Blo 1315976 2964095 := bstep (se 1 (by rfl) ⟨2223071, by rfl⟩ : syracuseStep 2964095 = 4446143) B4446143
theorem B6331297 : Blo 1315976 6331297 := bstep (se 2 (by rfl) ⟨2374236, by rfl⟩ : syracuseStep 6331297 = 4748473) B4748473
theorem B25304957 : Blo 1315976 25304957 := bstep (se 3 (by rfl) ⟨4744679, by rfl⟩ : syracuseStep 25304957 = 9489359) B9489359
theorem B1876127 : Blo 1315976 1876127 := bstep (se 1 (by rfl) ⟨1407095, by rfl⟩ : syracuseStep 1876127 = 2814191) B2814191
theorem B72122885 : Blo 1315976 72122885 := bstep (se 4 (by rfl) ⟨6761520, by rfl⟩ : syracuseStep 72122885 = 13523041) B13523041
theorem B1974953 : Blo 1315976 1974953 := bstep (se 2 (by rfl) ⟨740607, by rfl⟩ : syracuseStep 1974953 = 1481215) B1481215
theorem B8439065 : Blo 1315976 8439065 := bstep (se 2 (by rfl) ⟨3164649, by rfl⟩ : syracuseStep 8439065 = 6329299) B6329299
theorem B1976063 : Blo 1315976 1976063 := bstep (se 1 (by rfl) ⟨1482047, by rfl⟩ : syracuseStep 1976063 = 2964095) B2964095
theorem B16869971 : Blo 1315976 16869971 := bstep (se 1 (by rfl) ⟨12652478, by rfl⟩ : syracuseStep 16869971 = 25304957) B25304957
theorem B4443227 : Blo 1315976 4443227 := bstep (se 1 (by rfl) ⟨3332420, by rfl⟩ : syracuseStep 4443227 = 6664841) B6664841
theorem B15404525 : Blo 1315976 15404525 := bstep (se 3 (by rfl) ⟨2888348, by rfl⟩ : syracuseStep 15404525 = 5776697) B5776697
theorem B8433193 : Blo 1315976 8433193 := bstep (se 2 (by rfl) ⟨3162447, by rfl⟩ : syracuseStep 8433193 = 6324895) B6324895
theorem B16010959 : Blo 1315976 16010959 := bstep (se 1 (by rfl) ⟨12008219, by rfl⟩ : syracuseStep 16010959 = 24016439) B24016439
theorem B7122775 : Blo 1315976 7122775 := bstep (se 1 (by rfl) ⟨5342081, by rfl⟩ : syracuseStep 7122775 = 10684163) B10684163
theorem B8441729 : Blo 1315976 8441729 := bstep (se 2 (by rfl) ⟨3165648, by rfl⟩ : syracuseStep 8441729 = 6331297) B6331297
theorem B2961377 : Blo 1315976 2961377 := bstep (se 2 (by rfl) ⟨1110516, by rfl⟩ : syracuseStep 2961377 = 2221033) B2221033
theorem B21360671 : Blo 1315976 21360671 := bstep (se 1 (by rfl) ⟨16020503, by rfl⟩ : syracuseStep 21360671 = 32041007) B32041007
theorem B2961575 : Blo 1315976 2961575 := bstep (se 1 (by rfl) ⟨2221181, by rfl⟩ : syracuseStep 2961575 = 4442363) B4442363
theorem B1667567 : Blo 1315976 1667567 := bstep (se 1 (by rfl) ⟨1250675, by rfl⟩ : syracuseStep 1667567 = 2501351) B2501351
theorem B10138567 : Blo 1315976 10138567 := bstep (se 1 (by rfl) ⟨7603925, by rfl⟩ : syracuseStep 10138567 = 15207851) B15207851
theorem B16872947 : Blo 1315976 16872947 := bstep (se 1 (by rfl) ⟨12654710, by rfl⟩ : syracuseStep 16872947 = 25309421) B25309421
theorem B7998895637 : Blo 1315976 7998895637 := bstep (se 6 (by rfl) ⟨187474116, by rfl⟩ : syracuseStep 7998895637 = 374948233) B374948233
theorem B22517351 : Blo 1315976 22517351 := bstep (se 1 (by rfl) ⟨16888013, by rfl⟩ : syracuseStep 22517351 = 33776027) B33776027
theorem B1316831 : Blo 1315976 1316831 := bstep (se 1 (by rfl) ⟨987623, by rfl⟩ : syracuseStep 1316831 = 1975247) B1975247
theorem B1317031 : Blo 1315976 1317031 := bstep (se 1 (by rfl) ⟨987773, by rfl⟩ : syracuseStep 1317031 = 1975547) B1975547
theorem B5626367 : Blo 1315976 5626367 := bstep (se 1 (by rfl) ⟨4219775, by rfl⟩ : syracuseStep 5626367 = 8439551) B8439551
theorem B2964617 : Blo 1315976 2964617 := bstep (se 2 (by rfl) ⟨1111731, by rfl⟩ : syracuseStep 2964617 = 2223463) B2223463
theorem B1974383 : Blo 1315976 1974383 := bstep (se 1 (by rfl) ⟨1480787, by rfl⟩ : syracuseStep 1974383 = 2961575) B2961575
theorem B11248631 : Blo 1315976 11248631 := bstep (se 1 (by rfl) ⟨8436473, by rfl⟩ : syracuseStep 11248631 = 16872947) B16872947
theorem B13518089 : Blo 1315976 13518089 := bstep (se 2 (by rfl) ⟨5069283, by rfl⟩ : syracuseStep 13518089 = 10138567) B10138567
theorem B1976411 : Blo 1315976 1976411 := bstep (se 1 (by rfl) ⟨1482308, by rfl⟩ : syracuseStep 1976411 = 2964617) B2964617
theorem B9497033 : Blo 1315976 9497033 := bstep (se 2 (by rfl) ⟨3561387, by rfl⟩ : syracuseStep 9497033 = 7122775) B7122775
theorem B14240447 : Blo 1315976 14240447 := bstep (se 1 (by rfl) ⟨10680335, by rfl⟩ : syracuseStep 14240447 = 21360671) B21360671
theorem B48081923 : Blo 1315976 48081923 := bstep (se 1 (by rfl) ⟨36061442, by rfl⟩ : syracuseStep 48081923 = 72122885) B72122885
theorem B15011567 : Blo 1315976 15011567 := bstep (se 1 (by rfl) ⟨11258675, by rfl⟩ : syracuseStep 15011567 = 22517351) B22517351
theorem B11244257 : Blo 1315976 11244257 := bstep (se 2 (by rfl) ⟨4216596, by rfl⟩ : syracuseStep 11244257 = 8433193) B8433193
theorem B2962151 : Blo 1315976 2962151 := bstep (se 1 (by rfl) ⟨2221613, by rfl⟩ : syracuseStep 2962151 = 4443227) B4443227
theorem B10269683 : Blo 1315976 10269683 := bstep (se 1 (by rfl) ⟨7702262, by rfl⟩ : syracuseStep 10269683 = 15404525) B15404525
theorem B5003005 : Blo 1315976 5003005 := bstep (se 3 (by rfl) ⟨938063, by rfl⟩ : syracuseStep 5003005 = 1876127) B1876127
theorem B1316635 : Blo 1315976 1316635 := bstep (se 1 (by rfl) ⟨987476, by rfl⟩ : syracuseStep 1316635 = 1974953) B1974953
theorem B5626043 : Blo 1315976 5626043 := bstep (se 1 (by rfl) ⟨4219532, by rfl⟩ : syracuseStep 5626043 = 8439065) B8439065
theorem B5332597091 : Blo 1315976 5332597091 := bstep (se 1 (by rfl) ⟨3999447818, by rfl⟩ : syracuseStep 5332597091 = 7998895637) B7998895637
theorem B1317375 : Blo 1315976 1317375 := bstep (se 1 (by rfl) ⟨988031, by rfl⟩ : syracuseStep 1317375 = 1976063) B1976063
theorem B4446845 : Blo 1315976 4446845 := bstep (se 3 (by rfl) ⟨833783, by rfl⟩ : syracuseStep 4446845 = 1667567) B1667567
theorem B3750911 : Blo 1315976 3750911 := bstep (se 1 (by rfl) ⟨2813183, by rfl⟩ : syracuseStep 3750911 = 5626367) B5626367
theorem B11246647 : Blo 1315976 11246647 := bstep (se 1 (by rfl) ⟨8434985, by rfl⟩ : syracuseStep 11246647 = 16869971) B16869971
theorem B21347945 : Blo 1315976 21347945 := bstep (se 2 (by rfl) ⟨8005479, by rfl⟩ : syracuseStep 21347945 = 16010959) B16010959
theorem B5627819 : Blo 1315976 5627819 := bstep (se 1 (by rfl) ⟨4220864, by rfl⟩ : syracuseStep 5627819 = 8441729) B8441729
theorem B1974251 : Blo 1315976 1974251 := bstep (se 1 (by rfl) ⟨1480688, by rfl⟩ : syracuseStep 1974251 = 2961377) B2961377
theorem B7496171 : Blo 1315976 7496171 := bstep (se 1 (by rfl) ⟨5622128, by rfl⟩ : syracuseStep 7496171 = 11244257) B11244257
theorem B1974767 : Blo 1315976 1974767 := bstep (se 1 (by rfl) ⟨1481075, by rfl⟩ : syracuseStep 1974767 = 2962151) B2962151
theorem B9012059 : Blo 1315976 9012059 := bstep (se 1 (by rfl) ⟨6759044, by rfl⟩ : syracuseStep 9012059 = 13518089) B13518089
theorem B2500607 : Blo 1315976 2500607 := bstep (se 1 (by rfl) ⟨1875455, by rfl⟩ : syracuseStep 2500607 = 3750911) B3750911
theorem B6670673 : Blo 1315976 6670673 := bstep (se 2 (by rfl) ⟨2501502, by rfl⟩ : syracuseStep 6670673 = 5003005) B5003005
theorem B14231963 : Blo 1315976 14231963 := bstep (se 1 (by rfl) ⟨10673972, by rfl⟩ : syracuseStep 14231963 = 21347945) B21347945
theorem B7499087 : Blo 1315976 7499087 := bstep (se 1 (by rfl) ⟨5624315, by rfl⟩ : syracuseStep 7499087 = 11248631) B11248631
theorem B14995529 : Blo 1315976 14995529 := bstep (se 2 (by rfl) ⟨5623323, by rfl⟩ : syracuseStep 14995529 = 11246647) B11246647
theorem B10007711 : Blo 1315976 10007711 := bstep (se 1 (by rfl) ⟨7505783, by rfl⟩ : syracuseStep 10007711 = 15011567) B15011567
theorem B1316167 : Blo 1315976 1316167 := bstep (se 1 (by rfl) ⟨987125, by rfl⟩ : syracuseStep 1316167 = 1974251) B1974251
theorem B1316255 : Blo 1315976 1316255 := bstep (se 1 (by rfl) ⟨987191, by rfl⟩ : syracuseStep 1316255 = 1974383) B1974383
theorem B6846455 : Blo 1315976 6846455 := bstep (se 1 (by rfl) ⟨5134841, by rfl⟩ : syracuseStep 6846455 = 10269683) B10269683
theorem B1317607 : Blo 1315976 1317607 := bstep (se 1 (by rfl) ⟨988205, by rfl⟩ : syracuseStep 1317607 = 1976411) B1976411
theorem B3750695 : Blo 1315976 3750695 := bstep (se 1 (by rfl) ⟨2813021, by rfl⟩ : syracuseStep 3750695 = 5626043) B5626043
theorem B3555064727 : Blo 1315976 3555064727 := bstep (se 1 (by rfl) ⟨2666298545, by rfl⟩ : syracuseStep 3555064727 = 5332597091) B5332597091
theorem B6331355 : Blo 1315976 6331355 := bstep (se 1 (by rfl) ⟨4748516, by rfl⟩ : syracuseStep 6331355 = 9497033) B9497033
theorem B2964563 : Blo 1315976 2964563 := bstep (se 1 (by rfl) ⟨2223422, by rfl⟩ : syracuseStep 2964563 = 4446845) B4446845
theorem B9493631 : Blo 1315976 9493631 := bstep (se 1 (by rfl) ⟨7120223, by rfl⟩ : syracuseStep 9493631 = 14240447) B14240447
theorem B32054615 : Blo 1315976 32054615 := bstep (se 1 (by rfl) ⟨24040961, by rfl⟩ : syracuseStep 32054615 = 48081923) B48081923
theorem B3751879 : Blo 1315976 3751879 := bstep (se 1 (by rfl) ⟨2813909, by rfl⟩ : syracuseStep 3751879 = 5627819) B5627819
theorem B4997447 : Blo 1315976 4997447 := bstep (se 1 (by rfl) ⟨3748085, by rfl⟩ : syracuseStep 4997447 = 7496171) B7496171
theorem B2500463 : Blo 1315976 2500463 := bstep (se 1 (by rfl) ⟨1875347, by rfl⟩ : syracuseStep 2500463 = 3750695) B3750695
theorem B4220903 : Blo 1315976 4220903 := bstep (se 1 (by rfl) ⟨3165677, by rfl⟩ : syracuseStep 4220903 = 6331355) B6331355
theorem B1976375 : Blo 1315976 1976375 := bstep (se 1 (by rfl) ⟨1482281, by rfl⟩ : syracuseStep 1976375 = 2964563) B2964563
theorem B4999391 : Blo 1315976 4999391 := bstep (se 1 (by rfl) ⟨3749543, by rfl⟩ : syracuseStep 4999391 = 7499087) B7499087
theorem B9997019 : Blo 1315976 9997019 := bstep (se 1 (by rfl) ⟨7497764, by rfl⟩ : syracuseStep 9997019 = 14995529) B14995529
theorem B6008039 : Blo 1315976 6008039 := bstep (se 1 (by rfl) ⟨4506029, by rfl⟩ : syracuseStep 6008039 = 9012059) B9012059
theorem B6671807 : Blo 1315976 6671807 := bstep (se 1 (by rfl) ⟨5003855, by rfl⟩ : syracuseStep 6671807 = 10007711) B10007711
theorem B1667071 : Blo 1315976 1667071 := bstep (se 1 (by rfl) ⟨1250303, by rfl⟩ : syracuseStep 1667071 = 2500607) B2500607
theorem B6329087 : Blo 1315976 6329087 := bstep (se 1 (by rfl) ⟨4746815, by rfl⟩ : syracuseStep 6329087 = 9493631) B9493631
theorem B21369743 : Blo 1315976 21369743 := bstep (se 1 (by rfl) ⟨16027307, by rfl⟩ : syracuseStep 21369743 = 32054615) B32054615
theorem B5002505 : Blo 1315976 5002505 := bstep (se 2 (by rfl) ⟨1875939, by rfl⟩ : syracuseStep 5002505 = 3751879) B3751879
theorem B18257213 : Blo 1315976 18257213 := bstep (se 3 (by rfl) ⟨3423227, by rfl⟩ : syracuseStep 18257213 = 6846455) B6846455
theorem B1316511 : Blo 1315976 1316511 := bstep (se 1 (by rfl) ⟨987383, by rfl⟩ : syracuseStep 1316511 = 1974767) B1974767
theorem B37951901 : Blo 1315976 37951901 := bstep (se 3 (by rfl) ⟨7115981, by rfl⟩ : syracuseStep 37951901 = 14231963) B14231963
theorem B4447115 : Blo 1315976 4447115 := bstep (se 1 (by rfl) ⟨3335336, by rfl⟩ : syracuseStep 4447115 = 6670673) B6670673
theorem B2370043151 : Blo 1315976 2370043151 := bstep (se 1 (by rfl) ⟨1777532363, by rfl⟩ : syracuseStep 2370043151 = 3555064727) B3555064727
theorem B4219391 : Blo 1315976 4219391 := bstep (se 1 (by rfl) ⟨3164543, by rfl⟩ : syracuseStep 4219391 = 6329087) B6329087
theorem B14246495 : Blo 1315976 14246495 := bstep (se 1 (by rfl) ⟨10684871, by rfl⟩ : syracuseStep 14246495 = 21369743) B21369743
theorem B3335003 : Blo 1315976 3335003 := bstep (se 1 (by rfl) ⟨2501252, by rfl⟩ : syracuseStep 3335003 = 5002505) B5002505
theorem B2222761 : Blo 1315976 2222761 := bstep (se 2 (by rfl) ⟨833535, by rfl⟩ : syracuseStep 2222761 = 1667071) B1667071
theorem B1666975 : Blo 1315976 1666975 := bstep (se 1 (by rfl) ⟨1250231, by rfl⟩ : syracuseStep 1666975 = 2500463) B2500463
theorem B2813935 : Blo 1315976 2813935 := bstep (se 1 (by rfl) ⟨2110451, by rfl⟩ : syracuseStep 2813935 = 4220903) B4220903
theorem B25301267 : Blo 1315976 25301267 := bstep (se 1 (by rfl) ⟨18975950, by rfl⟩ : syracuseStep 25301267 = 37951901) B37951901
theorem B6664679 : Blo 1315976 6664679 := bstep (se 1 (by rfl) ⟨4998509, by rfl⟩ : syracuseStep 6664679 = 9997019) B9997019
theorem B1580028767 : Blo 1315976 1580028767 := bstep (se 1 (by rfl) ⟨1185021575, by rfl⟩ : syracuseStep 1580028767 = 2370043151) B2370043151
theorem B3331631 : Blo 1315976 3331631 := bstep (se 1 (by rfl) ⟨2498723, by rfl⟩ : syracuseStep 3331631 = 4997447) B4997447
theorem B12171475 : Blo 1315976 12171475 := bstep (se 1 (by rfl) ⟨9128606, by rfl⟩ : syracuseStep 12171475 = 18257213) B18257213
theorem B1317583 : Blo 1315976 1317583 := bstep (se 1 (by rfl) ⟨988187, by rfl⟩ : syracuseStep 1317583 = 1976375) B1976375
theorem B3332927 : Blo 1315976 3332927 := bstep (se 1 (by rfl) ⟨2499695, by rfl⟩ : syracuseStep 3332927 = 4999391) B4999391
theorem B2964743 : Blo 1315976 2964743 := bstep (se 1 (by rfl) ⟨2223557, by rfl⟩ : syracuseStep 2964743 = 4447115) B4447115
theorem B4005359 : Blo 1315976 4005359 := bstep (se 1 (by rfl) ⟨3004019, by rfl⟩ : syracuseStep 4005359 = 6008039) B6008039
theorem B4447871 : Blo 1315976 4447871 := bstep (se 1 (by rfl) ⟨3335903, by rfl⟩ : syracuseStep 4447871 = 6671807) B6671807
theorem B16867511 : Blo 1315976 16867511 := bstep (se 1 (by rfl) ⟨12650633, by rfl⟩ : syracuseStep 16867511 = 25301267) B25301267
theorem B1053352511 : Blo 1315976 1053352511 := bstep (se 1 (by rfl) ⟨790014383, by rfl⟩ : syracuseStep 1053352511 = 1580028767) B1580028767
theorem B2221087 : Blo 1315976 2221087 := bstep (se 1 (by rfl) ⟨1665815, by rfl⟩ : syracuseStep 2221087 = 3331631) B3331631
theorem B64914533 : Blo 1315976 64914533 := bstep (se 4 (by rfl) ⟨6085737, by rfl⟩ : syracuseStep 64914533 = 12171475) B12171475
theorem B2221951 : Blo 1315976 2221951 := bstep (se 1 (by rfl) ⟨1666463, by rfl⟩ : syracuseStep 2221951 = 3332927) B3332927
theorem B1976495 : Blo 1315976 1976495 := bstep (se 1 (by rfl) ⟨1482371, by rfl⟩ : syracuseStep 1976495 = 2964743) B2964743
theorem B2222633 : Blo 1315976 2222633 := bstep (se 2 (by rfl) ⟨833487, by rfl⟩ : syracuseStep 2222633 = 1666975) B1666975
theorem B4443119 : Blo 1315976 4443119 := bstep (se 1 (by rfl) ⟨3332339, by rfl⟩ : syracuseStep 4443119 = 6664679) B6664679
theorem B2812927 : Blo 1315976 2812927 := bstep (se 1 (by rfl) ⟨2109695, by rfl⟩ : syracuseStep 2812927 = 4219391) B4219391
theorem B9497663 : Blo 1315976 9497663 := bstep (se 1 (by rfl) ⟨7123247, by rfl⟩ : syracuseStep 9497663 = 14246495) B14246495
theorem B2223335 : Blo 1315976 2223335 := bstep (se 1 (by rfl) ⟨1667501, by rfl⟩ : syracuseStep 2223335 = 3335003) B3335003
theorem B2963681 : Blo 1315976 2963681 := bstep (se 2 (by rfl) ⟨1111380, by rfl⟩ : syracuseStep 2963681 = 2222761) B2222761
theorem B2670239 : Blo 1315976 2670239 := bstep (se 1 (by rfl) ⟨2002679, by rfl⟩ : syracuseStep 2670239 = 4005359) B4005359
theorem B2965247 : Blo 1315976 2965247 := bstep (se 1 (by rfl) ⟨2223935, by rfl⟩ : syracuseStep 2965247 = 4447871) B4447871
theorem B3751913 : Blo 1315976 3751913 := bstep (se 2 (by rfl) ⟨1406967, by rfl⟩ : syracuseStep 3751913 = 2813935) B2813935
theorem B702235007 : Blo 1315976 702235007 := bstep (se 1 (by rfl) ⟨526676255, by rfl⟩ : syracuseStep 702235007 = 1053352511) B1053352511
theorem B1975787 : Blo 1315976 1975787 := bstep (se 1 (by rfl) ⟨1481840, by rfl⟩ : syracuseStep 1975787 = 2963681) B2963681
theorem B1780159 : Blo 1315976 1780159 := bstep (se 1 (by rfl) ⟨1335119, by rfl⟩ : syracuseStep 1780159 = 2670239) B2670239
theorem B1976831 : Blo 1315976 1976831 := bstep (se 1 (by rfl) ⟨1482623, by rfl⟩ : syracuseStep 1976831 = 2965247) B2965247
theorem B2501275 : Blo 1315976 2501275 := bstep (se 1 (by rfl) ⟨1875956, by rfl⟩ : syracuseStep 2501275 = 3751913) B3751913
theorem B2961449 : Blo 1315976 2961449 := bstep (se 2 (by rfl) ⟨1110543, by rfl⟩ : syracuseStep 2961449 = 2221087) B2221087
theorem B2962079 : Blo 1315976 2962079 := bstep (se 1 (by rfl) ⟨2221559, by rfl⟩ : syracuseStep 2962079 = 4443119) B4443119
theorem B2962601 : Blo 1315976 2962601 := bstep (se 2 (by rfl) ⟨1110975, by rfl⟩ : syracuseStep 2962601 = 2221951) B2221951
theorem B11245007 : Blo 1315976 11245007 := bstep (se 1 (by rfl) ⟨8433755, by rfl⟩ : syracuseStep 11245007 = 16867511) B16867511
theorem B43276355 : Blo 1315976 43276355 := bstep (se 1 (by rfl) ⟨32457266, by rfl⟩ : syracuseStep 43276355 = 64914533) B64914533
theorem B3750569 : Blo 1315976 3750569 := bstep (se 2 (by rfl) ⟨1406463, by rfl⟩ : syracuseStep 3750569 = 2812927) B2812927
theorem B1317663 : Blo 1315976 1317663 := bstep (se 1 (by rfl) ⟨988247, by rfl⟩ : syracuseStep 1317663 = 1976495) B1976495
theorem B1481755 : Blo 1315976 1481755 := bstep (se 1 (by rfl) ⟨1111316, by rfl⟩ : syracuseStep 1481755 = 2222633) B2222633
theorem B6331775 : Blo 1315976 6331775 := bstep (se 1 (by rfl) ⟨4748831, by rfl⟩ : syracuseStep 6331775 = 9497663) B9497663
theorem B1482223 : Blo 1315976 1482223 := bstep (se 1 (by rfl) ⟨1111667, by rfl⟩ : syracuseStep 1482223 = 2223335) B2223335
theorem B1974299 : Blo 1315976 1974299 := bstep (se 1 (by rfl) ⟨1480724, by rfl⟩ : syracuseStep 1974299 = 2961449) B2961449
theorem B468156671 : Blo 1315976 468156671 := bstep (se 1 (by rfl) ⟨351117503, by rfl⟩ : syracuseStep 468156671 = 702235007) B702235007
theorem B1974719 : Blo 1315976 1974719 := bstep (se 1 (by rfl) ⟨1481039, by rfl⟩ : syracuseStep 1974719 = 2962079) B2962079
theorem B1975067 : Blo 1315976 1975067 := bstep (se 1 (by rfl) ⟨1481300, by rfl⟩ : syracuseStep 1975067 = 2962601) B2962601
theorem B3335033 : Blo 1315976 3335033 := bstep (se 2 (by rfl) ⟨1250637, by rfl⟩ : syracuseStep 3335033 = 2501275) B2501275
theorem B7496671 : Blo 1315976 7496671 := bstep (se 1 (by rfl) ⟨5622503, by rfl⟩ : syracuseStep 7496671 = 11245007) B11245007
theorem B16884733 : Blo 1315976 16884733 := bstep (se 3 (by rfl) ⟨3165887, by rfl⟩ : syracuseStep 16884733 = 6331775) B6331775
theorem B1975673 : Blo 1315976 1975673 := bstep (se 2 (by rfl) ⟨740877, by rfl⟩ : syracuseStep 1975673 = 1481755) B1481755
theorem B2500379 : Blo 1315976 2500379 := bstep (se 1 (by rfl) ⟨1875284, by rfl⟩ : syracuseStep 2500379 = 3750569) B3750569
theorem B1976297 : Blo 1315976 1976297 := bstep (se 2 (by rfl) ⟨741111, by rfl⟩ : syracuseStep 1976297 = 1482223) B1482223
theorem B2373545 : Blo 1315976 2373545 := bstep (se 2 (by rfl) ⟨890079, by rfl⟩ : syracuseStep 2373545 = 1780159) B1780159
theorem B1317191 : Blo 1315976 1317191 := bstep (se 1 (by rfl) ⟨987893, by rfl⟩ : syracuseStep 1317191 = 1975787) B1975787
theorem B28850903 : Blo 1315976 28850903 := bstep (se 1 (by rfl) ⟨21638177, by rfl⟩ : syracuseStep 28850903 = 43276355) B43276355
theorem B1317887 : Blo 1315976 1317887 := bstep (se 1 (by rfl) ⟨988415, by rfl⟩ : syracuseStep 1317887 = 1976831) B1976831
theorem B1582363 : Blo 1315976 1582363 := bstep (se 1 (by rfl) ⟨1186772, by rfl⟩ : syracuseStep 1582363 = 2373545) B2373545
theorem B9995561 : Blo 1315976 9995561 := bstep (se 2 (by rfl) ⟨3748335, by rfl⟩ : syracuseStep 9995561 = 7496671) B7496671
theorem B22512977 : Blo 1315976 22512977 := bstep (se 2 (by rfl) ⟨8442366, by rfl⟩ : syracuseStep 22512977 = 16884733) B16884733
theorem B2223355 : Blo 1315976 2223355 := bstep (se 1 (by rfl) ⟨1667516, by rfl⟩ : syracuseStep 2223355 = 3335033) B3335033
theorem B1666919 : Blo 1315976 1666919 := bstep (se 1 (by rfl) ⟨1250189, by rfl⟩ : syracuseStep 1666919 = 2500379) B2500379
theorem B1316199 : Blo 1315976 1316199 := bstep (se 1 (by rfl) ⟨987149, by rfl⟩ : syracuseStep 1316199 = 1974299) B1974299
theorem B312104447 : Blo 1315976 312104447 := bstep (se 1 (by rfl) ⟨234078335, by rfl⟩ : syracuseStep 312104447 = 468156671) B468156671
theorem B1316479 : Blo 1315976 1316479 := bstep (se 1 (by rfl) ⟨987359, by rfl⟩ : syracuseStep 1316479 = 1974719) B1974719
theorem B1316711 : Blo 1315976 1316711 := bstep (se 1 (by rfl) ⟨987533, by rfl⟩ : syracuseStep 1316711 = 1975067) B1975067
theorem B1317115 : Blo 1315976 1317115 := bstep (se 1 (by rfl) ⟨987836, by rfl⟩ : syracuseStep 1317115 = 1975673) B1975673
theorem B1317531 : Blo 1315976 1317531 := bstep (se 1 (by rfl) ⟨988148, by rfl⟩ : syracuseStep 1317531 = 1976297) B1976297
theorem B19233935 : Blo 1315976 19233935 := bstep (se 1 (by rfl) ⟨14425451, by rfl⟩ : syracuseStep 19233935 = 28850903) B28850903
theorem B15008651 : Blo 1315976 15008651 := bstep (se 1 (by rfl) ⟨11256488, by rfl⟩ : syracuseStep 15008651 = 22512977) B22512977
theorem B208069631 : Blo 1315976 208069631 := bstep (se 1 (by rfl) ⟨156052223, by rfl⟩ : syracuseStep 208069631 = 312104447) B312104447
theorem B12822623 : Blo 1315976 12822623 := bstep (se 1 (by rfl) ⟨9616967, by rfl⟩ : syracuseStep 12822623 = 19233935) B19233935
theorem B6663707 : Blo 1315976 6663707 := bstep (se 1 (by rfl) ⟨4997780, by rfl⟩ : syracuseStep 6663707 = 9995561) B9995561
theorem B2109817 : Blo 1315976 2109817 := bstep (se 2 (by rfl) ⟨791181, by rfl⟩ : syracuseStep 2109817 = 1582363) B1582363
theorem B4445117 : Blo 1315976 4445117 := bstep (se 3 (by rfl) ⟨833459, by rfl⟩ : syracuseStep 4445117 = 1666919) B1666919
theorem B2964473 : Blo 1315976 2964473 := bstep (se 2 (by rfl) ⟨1111677, by rfl⟩ : syracuseStep 2964473 = 2223355) B2223355
theorem B1976315 : Blo 1315976 1976315 := bstep (se 1 (by rfl) ⟨1482236, by rfl⟩ : syracuseStep 1976315 = 2964473) B2964473
theorem B4442471 : Blo 1315976 4442471 := bstep (se 1 (by rfl) ⟨3331853, by rfl⟩ : syracuseStep 4442471 = 6663707) B6663707
theorem B10005767 : Blo 1315976 10005767 := bstep (se 1 (by rfl) ⟨7504325, by rfl⟩ : syracuseStep 10005767 = 15008651) B15008651
theorem B8548415 : Blo 1315976 8548415 := bstep (se 1 (by rfl) ⟨6411311, by rfl⟩ : syracuseStep 8548415 = 12822623) B12822623
theorem B11252357 : Blo 1315976 11252357 := bstep (se 4 (by rfl) ⟨1054908, by rfl⟩ : syracuseStep 11252357 = 2109817) B2109817
theorem B2963411 : Blo 1315976 2963411 := bstep (se 1 (by rfl) ⟨2222558, by rfl⟩ : syracuseStep 2963411 = 4445117) B4445117
theorem B138713087 : Blo 1315976 138713087 := bstep (se 1 (by rfl) ⟨104034815, by rfl⟩ : syracuseStep 138713087 = 208069631) B208069631
theorem B369901565 : Blo 1315976 369901565 := bstep (se 3 (by rfl) ⟨69356543, by rfl⟩ : syracuseStep 369901565 = 138713087) B138713087
theorem B1975607 : Blo 1315976 1975607 := bstep (se 1 (by rfl) ⟨1481705, by rfl⟩ : syracuseStep 1975607 = 2963411) B2963411
theorem B6670511 : Blo 1315976 6670511 := bstep (se 1 (by rfl) ⟨5002883, by rfl⟩ : syracuseStep 6670511 = 10005767) B10005767
theorem B2961647 : Blo 1315976 2961647 := bstep (se 1 (by rfl) ⟨2221235, by rfl⟩ : syracuseStep 2961647 = 4442471) B4442471
theorem B5698943 : Blo 1315976 5698943 := bstep (se 1 (by rfl) ⟨4274207, by rfl⟩ : syracuseStep 5698943 = 8548415) B8548415
theorem B7501571 : Blo 1315976 7501571 := bstep (se 1 (by rfl) ⟨5626178, by rfl⟩ : syracuseStep 7501571 = 11252357) B11252357
theorem B1317543 : Blo 1315976 1317543 := bstep (se 1 (by rfl) ⟨988157, by rfl⟩ : syracuseStep 1317543 = 1976315) B1976315
theorem B1974431 : Blo 1315976 1974431 := bstep (se 1 (by rfl) ⟨1480823, by rfl⟩ : syracuseStep 1974431 = 2961647) B2961647
theorem B5001047 : Blo 1315976 5001047 := bstep (se 1 (by rfl) ⟨3750785, by rfl⟩ : syracuseStep 5001047 = 7501571) B7501571
theorem B246601043 : Blo 1315976 246601043 := bstep (se 1 (by rfl) ⟨184950782, by rfl⟩ : syracuseStep 246601043 = 369901565) B369901565
theorem B1317071 : Blo 1315976 1317071 := bstep (se 1 (by rfl) ⟨987803, by rfl⟩ : syracuseStep 1317071 = 1975607) B1975607
theorem B3799295 : Blo 1315976 3799295 := bstep (se 1 (by rfl) ⟨2849471, by rfl⟩ : syracuseStep 3799295 = 5698943) B5698943
theorem B4447007 : Blo 1315976 4447007 := bstep (se 1 (by rfl) ⟨3335255, by rfl⟩ : syracuseStep 4447007 = 6670511) B6670511
theorem B2532863 : Blo 1315976 2532863 := bstep (se 1 (by rfl) ⟨1899647, by rfl⟩ : syracuseStep 2532863 = 3799295) B3799295
theorem B164400695 : Blo 1315976 164400695 := bstep (se 1 (by rfl) ⟨123300521, by rfl⟩ : syracuseStep 164400695 = 246601043) B246601043
theorem B1316287 : Blo 1315976 1316287 := bstep (se 1 (by rfl) ⟨987215, by rfl⟩ : syracuseStep 1316287 = 1974431) B1974431
theorem B2964671 : Blo 1315976 2964671 := bstep (se 1 (by rfl) ⟨2223503, by rfl⟩ : syracuseStep 2964671 = 4447007) B4447007
theorem B3334031 : Blo 1315976 3334031 := bstep (se 1 (by rfl) ⟨2500523, by rfl⟩ : syracuseStep 3334031 = 5001047) B5001047
theorem B1688575 : Blo 1315976 1688575 := bstep (se 1 (by rfl) ⟨1266431, by rfl⟩ : syracuseStep 1688575 = 2532863) B2532863
theorem B1976447 : Blo 1315976 1976447 := bstep (se 1 (by rfl) ⟨1482335, by rfl⟩ : syracuseStep 1976447 = 2964671) B2964671
theorem B2222687 : Blo 1315976 2222687 := bstep (se 1 (by rfl) ⟨1667015, by rfl⟩ : syracuseStep 2222687 = 3334031) B3334031
theorem B109600463 : Blo 1315976 109600463 := bstep (se 1 (by rfl) ⟨82200347, by rfl⟩ : syracuseStep 109600463 = 164400695) B164400695
theorem B292267901 : Blo 1315976 292267901 := bstep (se 3 (by rfl) ⟨54800231, by rfl⟩ : syracuseStep 292267901 = 109600463) B109600463
theorem B2251433 : Blo 1315976 2251433 := bstep (se 2 (by rfl) ⟨844287, by rfl⟩ : syracuseStep 2251433 = 1688575) B1688575
theorem B1317631 : Blo 1315976 1317631 := bstep (se 1 (by rfl) ⟨988223, by rfl⟩ : syracuseStep 1317631 = 1976447) B1976447
theorem B1481791 : Blo 1315976 1481791 := bstep (se 1 (by rfl) ⟨1111343, by rfl⟩ : syracuseStep 1481791 = 2222687) B2222687
theorem B1975721 : Blo 1315976 1975721 := bstep (se 2 (by rfl) ⟨740895, by rfl⟩ : syracuseStep 1975721 = 1481791) B1481791
theorem B194845267 : Blo 1315976 194845267 := bstep (se 1 (by rfl) ⟨146133950, by rfl⟩ : syracuseStep 194845267 = 292267901) B292267901
theorem B6003821 : Blo 1315976 6003821 := bstep (se 3 (by rfl) ⟨1125716, by rfl⟩ : syracuseStep 6003821 = 2251433) B2251433
theorem B259793689 : Blo 1315976 259793689 := bstep (se 2 (by rfl) ⟨97422633, by rfl⟩ : syracuseStep 259793689 = 194845267) B194845267
theorem B4002547 : Blo 1315976 4002547 := bstep (se 1 (by rfl) ⟨3001910, by rfl⟩ : syracuseStep 4002547 = 6003821) B6003821
theorem B1317147 : Blo 1315976 1317147 := bstep (se 1 (by rfl) ⟨987860, by rfl⟩ : syracuseStep 1317147 = 1975721) B1975721
theorem B346391585 : Blo 1315976 346391585 := bstep (se 2 (by rfl) ⟨129896844, by rfl⟩ : syracuseStep 346391585 = 259793689) B259793689
theorem B5336729 : Blo 1315976 5336729 := bstep (se 2 (by rfl) ⟨2001273, by rfl⟩ : syracuseStep 5336729 = 4002547) B4002547
theorem B3557819 : Blo 1315976 3557819 := bstep (se 1 (by rfl) ⟨2668364, by rfl⟩ : syracuseStep 3557819 = 5336729) B5336729
theorem B230927723 : Blo 1315976 230927723 := bstep (se 1 (by rfl) ⟨173195792, by rfl⟩ : syracuseStep 230927723 = 346391585) B346391585
theorem B2371879 : Blo 1315976 2371879 := bstep (se 1 (by rfl) ⟨1778909, by rfl⟩ : syracuseStep 2371879 = 3557819) B3557819
theorem B153951815 : Blo 1315976 153951815 := bstep (se 1 (by rfl) ⟨115463861, by rfl⟩ : syracuseStep 153951815 = 230927723) B230927723
theorem B3162505 : Blo 1315976 3162505 := bstep (se 2 (by rfl) ⟨1185939, by rfl⟩ : syracuseStep 3162505 = 2371879) B2371879
theorem B102634543 : Blo 1315976 102634543 := bstep (se 1 (by rfl) ⟨76975907, by rfl⟩ : syracuseStep 102634543 = 153951815) B153951815
theorem B4216673 : Blo 1315976 4216673 := bstep (se 2 (by rfl) ⟨1581252, by rfl⟩ : syracuseStep 4216673 = 3162505) B3162505
theorem B136846057 : Blo 1315976 136846057 := bstep (se 2 (by rfl) ⟨51317271, by rfl⟩ : syracuseStep 136846057 = 102634543) B102634543
theorem B182461409 : Blo 1315976 182461409 := bstep (se 2 (by rfl) ⟨68423028, by rfl⟩ : syracuseStep 182461409 = 136846057) B136846057
theorem B2811115 : Blo 1315976 2811115 := bstep (se 1 (by rfl) ⟨2108336, by rfl⟩ : syracuseStep 2811115 = 4216673) B4216673
theorem B14992613 : Blo 1315976 14992613 := bstep (se 4 (by rfl) ⟨1405557, by rfl⟩ : syracuseStep 14992613 = 2811115) B2811115
theorem B121640939 : Blo 1315976 121640939 := bstep (se 1 (by rfl) ⟨91230704, by rfl⟩ : syracuseStep 121640939 = 182461409) B182461409
theorem B9995075 : Blo 1315976 9995075 := bstep (se 1 (by rfl) ⟨7496306, by rfl⟩ : syracuseStep 9995075 = 14992613) B14992613
theorem B81093959 : Blo 1315976 81093959 := bstep (se 1 (by rfl) ⟨60820469, by rfl⟩ : syracuseStep 81093959 = 121640939) B121640939
theorem B6663383 : Blo 1315976 6663383 := bstep (se 1 (by rfl) ⟨4997537, by rfl⟩ : syracuseStep 6663383 = 9995075) B9995075
theorem B54062639 : Blo 1315976 54062639 := bstep (se 1 (by rfl) ⟨40546979, by rfl⟩ : syracuseStep 54062639 = 81093959) B81093959
theorem B4442255 : Blo 1315976 4442255 := bstep (se 1 (by rfl) ⟨3331691, by rfl⟩ : syracuseStep 4442255 = 6663383) B6663383
theorem B36041759 : Blo 1315976 36041759 := bstep (se 1 (by rfl) ⟨27031319, by rfl⟩ : syracuseStep 36041759 = 54062639) B54062639
theorem B24027839 : Blo 1315976 24027839 := bstep (se 1 (by rfl) ⟨18020879, by rfl⟩ : syracuseStep 24027839 = 36041759) B36041759
theorem B2961503 : Blo 1315976 2961503 := bstep (se 1 (by rfl) ⟨2221127, by rfl⟩ : syracuseStep 2961503 = 4442255) B4442255
theorem B1974335 : Blo 1315976 1974335 := bstep (se 1 (by rfl) ⟨1480751, by rfl⟩ : syracuseStep 1974335 = 2961503) B2961503
theorem B16018559 : Blo 1315976 16018559 := bstep (se 1 (by rfl) ⟨12013919, by rfl⟩ : syracuseStep 16018559 = 24027839) B24027839
theorem B10679039 : Blo 1315976 10679039 := bstep (se 1 (by rfl) ⟨8009279, by rfl⟩ : syracuseStep 10679039 = 16018559) B16018559
theorem B1316223 : Blo 1315976 1316223 := bstep (se 1 (by rfl) ⟨987167, by rfl⟩ : syracuseStep 1316223 = 1974335) B1974335
theorem B7119359 : Blo 1315976 7119359 := bstep (se 1 (by rfl) ⟨5339519, by rfl⟩ : syracuseStep 7119359 = 10679039) B10679039
theorem B4746239 : Blo 1315976 4746239 := bstep (se 1 (by rfl) ⟨3559679, by rfl⟩ : syracuseStep 4746239 = 7119359) B7119359
theorem B3164159 : Blo 1315976 3164159 := bstep (se 1 (by rfl) ⟨2373119, by rfl⟩ : syracuseStep 3164159 = 4746239) B4746239
theorem B2109439 : Blo 1315976 2109439 := bstep (se 1 (by rfl) ⟨1582079, by rfl⟩ : syracuseStep 2109439 = 3164159) B3164159
theorem B2812585 : Blo 1315976 2812585 := bstep (se 2 (by rfl) ⟨1054719, by rfl⟩ : syracuseStep 2812585 = 2109439) B2109439
theorem B3750113 : Blo 1315976 3750113 := bstep (se 2 (by rfl) ⟨1406292, by rfl⟩ : syracuseStep 3750113 = 2812585) B2812585
theorem B2500075 : Blo 1315976 2500075 := bstep (se 1 (by rfl) ⟨1875056, by rfl⟩ : syracuseStep 2500075 = 3750113) B3750113
theorem B3333433 : Blo 1315976 3333433 := bstep (se 2 (by rfl) ⟨1250037, by rfl⟩ : syracuseStep 3333433 = 2500075) B2500075
theorem B4444577 : Blo 1315976 4444577 := bstep (se 2 (by rfl) ⟨1666716, by rfl⟩ : syracuseStep 4444577 = 3333433) B3333433
theorem B2963051 : Blo 1315976 2963051 := bstep (se 1 (by rfl) ⟨2222288, by rfl⟩ : syracuseStep 2963051 = 4444577) B4444577
theorem B1975367 : Blo 1315976 1975367 := bstep (se 1 (by rfl) ⟨1481525, by rfl⟩ : syracuseStep 1975367 = 2963051) B2963051
theorem B1316911 : Blo 1315976 1316911 := bstep (se 1 (by rfl) ⟨987683, by rfl⟩ : syracuseStep 1316911 = 1975367) B1975367

theorem C0 (j : ℕ) (h1 : 328994 ≤ j) (h2 : j ≤ 329493) : Blo 1315976 (4 * j + 3) := by
  interval_cases j
  · exact B1315979
  · exact B1315983
  · exact B1315987
  · exact B1315991
  · exact B1315995
  · exact B1315999
  · exact B1316003
  · exact B1316007
  · exact B1316011
  · exact B1316015
  · exact B1316019
  · exact B1316023
  · exact B1316027
  · exact B1316031
  · exact B1316035
  · exact B1316039
  · exact B1316043
  · exact B1316047
  · exact B1316051
  · exact B1316055
  · exact B1316059
  · exact B1316063
  · exact B1316067
  · exact B1316071
  · exact B1316075
  · exact B1316079
  · exact B1316083
  · exact B1316087
  · exact B1316091
  · exact B1316095
  · exact B1316099
  · exact B1316103
  · exact B1316107
  · exact B1316111
  · exact B1316115
  · exact B1316119
  · exact B1316123
  · exact B1316127
  · exact B1316131
  · exact B1316135
  · exact B1316139
  · exact B1316143
  · exact B1316147
  · exact B1316151
  · exact B1316155
  · exact B1316159
  · exact B1316163
  · exact B1316167
  · exact B1316171
  · exact B1316175
  · exact B1316179
  · exact B1316183
  · exact B1316187
  · exact B1316191
  · exact B1316195
  · exact B1316199
  · exact B1316203
  · exact B1316207
  · exact B1316211
  · exact B1316215
  · exact B1316219
  · exact B1316223
  · exact B1316227
  · exact B1316231
  · exact B1316235
  · exact B1316239
  · exact B1316243
  · exact B1316247
  · exact B1316251
  · exact B1316255
  · exact B1316259
  · exact B1316263
  · exact B1316267
  · exact B1316271
  · exact B1316275
  · exact B1316279
  · exact B1316283
  · exact B1316287
  · exact B1316291
  · exact B1316295
  · exact B1316299
  · exact B1316303
  · exact B1316307
  · exact B1316311
  · exact B1316315
  · exact B1316319
  · exact B1316323
  · exact B1316327
  · exact B1316331
  · exact B1316335
  · exact B1316339
  · exact B1316343
  · exact B1316347
  · exact B1316351
  · exact B1316355
  · exact B1316359
  · exact B1316363
  · exact B1316367
  · exact B1316371
  · exact B1316375
  · exact B1316379
  · exact B1316383
  · exact B1316387
  · exact B1316391
  · exact B1316395
  · exact B1316399
  · exact B1316403
  · exact B1316407
  · exact B1316411
  · exact B1316415
  · exact B1316419
  · exact B1316423
  · exact B1316427
  · exact B1316431
  · exact B1316435
  · exact B1316439
  · exact B1316443
  · exact B1316447
  · exact B1316451
  · exact B1316455
  · exact B1316459
  · exact B1316463
  · exact B1316467
  · exact B1316471
  · exact B1316475
  · exact B1316479
  · exact B1316483
  · exact B1316487
  · exact B1316491
  · exact B1316495
  · exact B1316499
  · exact B1316503
  · exact B1316507
  · exact B1316511
  · exact B1316515
  · exact B1316519
  · exact B1316523
  · exact B1316527
  · exact B1316531
  · exact B1316535
  · exact B1316539
  · exact B1316543
  · exact B1316547
  · exact B1316551
  · exact B1316555
  · exact B1316559
  · exact B1316563
  · exact B1316567
  · exact B1316571
  · exact B1316575
  · exact B1316579
  · exact B1316583
  · exact B1316587
  · exact B1316591
  · exact B1316595
  · exact B1316599
  · exact B1316603
  · exact B1316607
  · exact B1316611
  · exact B1316615
  · exact B1316619
  · exact B1316623
  · exact B1316627
  · exact B1316631
  · exact B1316635
  · exact B1316639
  · exact B1316643
  · exact B1316647
  · exact B1316651
  · exact B1316655
  · exact B1316659
  · exact B1316663
  · exact B1316667
  · exact B1316671
  · exact B1316675
  · exact B1316679
  · exact B1316683
  · exact B1316687
  · exact B1316691
  · exact B1316695
  · exact B1316699
  · exact B1316703
  · exact B1316707
  · exact B1316711
  · exact B1316715
  · exact B1316719
  · exact B1316723
  · exact B1316727
  · exact B1316731
  · exact B1316735
  · exact B1316739
  · exact B1316743
  · exact B1316747
  · exact B1316751
  · exact B1316755
  · exact B1316759
  · exact B1316763
  · exact B1316767
  · exact B1316771
  · exact B1316775
  · exact B1316779
  · exact B1316783
  · exact B1316787
  · exact B1316791
  · exact B1316795
  · exact B1316799
  · exact B1316803
  · exact B1316807
  · exact B1316811
  · exact B1316815
  · exact B1316819
  · exact B1316823
  · exact B1316827
  · exact B1316831
  · exact B1316835
  · exact B1316839
  · exact B1316843
  · exact B1316847
  · exact B1316851
  · exact B1316855
  · exact B1316859
  · exact B1316863
  · exact B1316867
  · exact B1316871
  · exact B1316875
  · exact B1316879
  · exact B1316883
  · exact B1316887
  · exact B1316891
  · exact B1316895
  · exact B1316899
  · exact B1316903
  · exact B1316907
  · exact B1316911
  · exact B1316915
  · exact B1316919
  · exact B1316923
  · exact B1316927
  · exact B1316931
  · exact B1316935
  · exact B1316939
  · exact B1316943
  · exact B1316947
  · exact B1316951
  · exact B1316955
  · exact B1316959
  · exact B1316963
  · exact B1316967
  · exact B1316971
  · exact B1316975
  · exact B1316979
  · exact B1316983
  · exact B1316987
  · exact B1316991
  · exact B1316995
  · exact B1316999
  · exact B1317003
  · exact B1317007
  · exact B1317011
  · exact B1317015
  · exact B1317019
  · exact B1317023
  · exact B1317027
  · exact B1317031
  · exact B1317035
  · exact B1317039
  · exact B1317043
  · exact B1317047
  · exact B1317051
  · exact B1317055
  · exact B1317059
  · exact B1317063
  · exact B1317067
  · exact B1317071
  · exact B1317075
  · exact B1317079
  · exact B1317083
  · exact B1317087
  · exact B1317091
  · exact B1317095
  · exact B1317099
  · exact B1317103
  · exact B1317107
  · exact B1317111
  · exact B1317115
  · exact B1317119
  · exact B1317123
  · exact B1317127
  · exact B1317131
  · exact B1317135
  · exact B1317139
  · exact B1317143
  · exact B1317147
  · exact B1317151
  · exact B1317155
  · exact B1317159
  · exact B1317163
  · exact B1317167
  · exact B1317171
  · exact B1317175
  · exact B1317179
  · exact B1317183
  · exact B1317187
  · exact B1317191
  · exact B1317195
  · exact B1317199
  · exact B1317203
  · exact B1317207
  · exact B1317211
  · exact B1317215
  · exact B1317219
  · exact B1317223
  · exact B1317227
  · exact B1317231
  · exact B1317235
  · exact B1317239
  · exact B1317243
  · exact B1317247
  · exact B1317251
  · exact B1317255
  · exact B1317259
  · exact B1317263
  · exact B1317267
  · exact B1317271
  · exact B1317275
  · exact B1317279
  · exact B1317283
  · exact B1317287
  · exact B1317291
  · exact B1317295
  · exact B1317299
  · exact B1317303
  · exact B1317307
  · exact B1317311
  · exact B1317315
  · exact B1317319
  · exact B1317323
  · exact B1317327
  · exact B1317331
  · exact B1317335
  · exact B1317339
  · exact B1317343
  · exact B1317347
  · exact B1317351
  · exact B1317355
  · exact B1317359
  · exact B1317363
  · exact B1317367
  · exact B1317371
  · exact B1317375
  · exact B1317379
  · exact B1317383
  · exact B1317387
  · exact B1317391
  · exact B1317395
  · exact B1317399
  · exact B1317403
  · exact B1317407
  · exact B1317411
  · exact B1317415
  · exact B1317419
  · exact B1317423
  · exact B1317427
  · exact B1317431
  · exact B1317435
  · exact B1317439
  · exact B1317443
  · exact B1317447
  · exact B1317451
  · exact B1317455
  · exact B1317459
  · exact B1317463
  · exact B1317467
  · exact B1317471
  · exact B1317475
  · exact B1317479
  · exact B1317483
  · exact B1317487
  · exact B1317491
  · exact B1317495
  · exact B1317499
  · exact B1317503
  · exact B1317507
  · exact B1317511
  · exact B1317515
  · exact B1317519
  · exact B1317523
  · exact B1317527
  · exact B1317531
  · exact B1317535
  · exact B1317539
  · exact B1317543
  · exact B1317547
  · exact B1317551
  · exact B1317555
  · exact B1317559
  · exact B1317563
  · exact B1317567
  · exact B1317571
  · exact B1317575
  · exact B1317579
  · exact B1317583
  · exact B1317587
  · exact B1317591
  · exact B1317595
  · exact B1317599
  · exact B1317603
  · exact B1317607
  · exact B1317611
  · exact B1317615
  · exact B1317619
  · exact B1317623
  · exact B1317627
  · exact B1317631
  · exact B1317635
  · exact B1317639
  · exact B1317643
  · exact B1317647
  · exact B1317651
  · exact B1317655
  · exact B1317659
  · exact B1317663
  · exact B1317667
  · exact B1317671
  · exact B1317675
  · exact B1317679
  · exact B1317683
  · exact B1317687
  · exact B1317691
  · exact B1317695
  · exact B1317699
  · exact B1317703
  · exact B1317707
  · exact B1317711
  · exact B1317715
  · exact B1317719
  · exact B1317723
  · exact B1317727
  · exact B1317731
  · exact B1317735
  · exact B1317739
  · exact B1317743
  · exact B1317747
  · exact B1317751
  · exact B1317755
  · exact B1317759
  · exact B1317763
  · exact B1317767
  · exact B1317771
  · exact B1317775
  · exact B1317779
  · exact B1317783
  · exact B1317787
  · exact B1317791
  · exact B1317795
  · exact B1317799
  · exact B1317803
  · exact B1317807
  · exact B1317811
  · exact B1317815
  · exact B1317819
  · exact B1317823
  · exact B1317827
  · exact B1317831
  · exact B1317835
  · exact B1317839
  · exact B1317843
  · exact B1317847
  · exact B1317851
  · exact B1317855
  · exact B1317859
  · exact B1317863
  · exact B1317867
  · exact B1317871
  · exact B1317875
  · exact B1317879
  · exact B1317883
  · exact B1317887
  · exact B1317891
  · exact B1317895
  · exact B1317899
  · exact B1317903
  · exact B1317907
  · exact B1317911
  · exact B1317915
  · exact B1317919
  · exact B1317923
  · exact B1317927
  · exact B1317931
  · exact B1317935
  · exact B1317939
  · exact B1317943
  · exact B1317947
  · exact B1317951
  · exact B1317955
  · exact B1317959
  · exact B1317963
  · exact B1317967
  · exact B1317971
  · exact B1317975

theorem solution (m : ℕ) (hlo : 1315976 ≤ m) (hhi : m ≤ 1317976) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 328994 ≤ j := by omega
    have hj2 : j ≤ 329493 := by omega
    have hb : Blo 1315976 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
