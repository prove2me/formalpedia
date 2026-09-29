-- Prove2me | solution 1 for syracuse_descends_range_1829616_1831616
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:59:16.977329+00:00
-- url     : https://prove2.me/submissions/f9fa518a-be2c-41e0-980f-6848c4e43ca8

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


theorem B6176789 : Blo 1829616 6176789 := bbase (se 6 (by rfl) ⟨144768, by rfl⟩ : syracuseStep 6176789 = 289537) (by norm_num)
theorem B4120613 : Blo 1829616 4120613 := bbase (se 4 (by rfl) ⟨386307, by rfl⟩ : syracuseStep 4120613 = 772615) (by norm_num)
theorem B3088469 : Blo 1829616 3088469 := bbase (se 8 (by rfl) ⟨18096, by rfl⟩ : syracuseStep 3088469 = 36193) (by norm_num)
theorem B2744429 : Blo 1829616 2744429 := bbase (se 3 (by rfl) ⟨514580, by rfl⟩ : syracuseStep 2744429 = 1029161) (by norm_num)
theorem B4120685 : Blo 1829616 4120685 := bbase (se 3 (by rfl) ⟨772628, by rfl⟩ : syracuseStep 4120685 = 1545257) (by norm_num)
theorem B1982581 : Blo 1829616 1982581 := bbase (se 5 (by rfl) ⟨92933, by rfl⟩ : syracuseStep 1982581 = 185867) (by norm_num)
theorem B3473533 : Blo 1829616 3473533 := bbase (se 3 (by rfl) ⟨651287, by rfl⟩ : syracuseStep 3473533 = 1302575) (by norm_num)
theorem B2744453 : Blo 1829616 2744453 := bbase (se 4 (by rfl) ⟨257292, by rfl⟩ : syracuseStep 2744453 = 514585) (by norm_num)
theorem B2744477 : Blo 1829616 2744477 := bbase (se 3 (by rfl) ⟨514589, by rfl⟩ : syracuseStep 2744477 = 1029179) (by norm_num)
theorem B2605213 : Blo 1829616 2605213 := bbase (se 3 (by rfl) ⟨488477, by rfl⟩ : syracuseStep 2605213 = 976955) (by norm_num)
theorem B5865637 : Blo 1829616 5865637 := bbase (se 4 (by rfl) ⟨549903, by rfl⟩ : syracuseStep 5865637 = 1099807) (by norm_num)
theorem B2744501 : Blo 1829616 2744501 := bbase (se 5 (by rfl) ⟨128648, by rfl⟩ : syracuseStep 2744501 = 257297) (by norm_num)
theorem B4120757 : Blo 1829616 4120757 := bbase (se 5 (by rfl) ⟨193160, by rfl⟩ : syracuseStep 4120757 = 386321) (by norm_num)
theorem B2744525 : Blo 1829616 2744525 := bbase (se 3 (by rfl) ⟨514598, by rfl⟩ : syracuseStep 2744525 = 1029197) (by norm_num)
theorem B3088597 : Blo 1829616 3088597 := bbase (se 7 (by rfl) ⟨36194, by rfl⟩ : syracuseStep 3088597 = 72389) (by norm_num)
theorem B4948181 : Blo 1829616 4948181 := bbase (se 7 (by rfl) ⟨57986, by rfl⟩ : syracuseStep 4948181 = 115973) (by norm_num)
theorem B2744549 : Blo 1829616 2744549 := bbase (se 4 (by rfl) ⟨257301, by rfl⟩ : syracuseStep 2744549 = 514603) (by norm_num)
theorem B2474221 : Blo 1829616 2474221 := bbase (se 3 (by rfl) ⟨463916, by rfl⟩ : syracuseStep 2474221 = 927833) (by norm_num)
theorem B6594805 : Blo 1829616 6594805 := bbase (se 5 (by rfl) ⟨309131, by rfl⟩ : syracuseStep 6594805 = 618263) (by norm_num)
theorem B2744573 : Blo 1829616 2744573 := bbase (se 3 (by rfl) ⟨514607, by rfl⟩ : syracuseStep 2744573 = 1029215) (by norm_num)
theorem B4120829 : Blo 1829616 4120829 := bbase (se 3 (by rfl) ⟨772655, by rfl⟩ : syracuseStep 4120829 = 1545311) (by norm_num)
theorem B4399373 : Blo 1829616 4399373 := bbase (se 3 (by rfl) ⟨824882, by rfl⟩ : syracuseStep 4399373 = 1649765) (by norm_num)
theorem B2744597 : Blo 1829616 2744597 := bbase (se 6 (by rfl) ⟨64326, by rfl⟩ : syracuseStep 2744597 = 128653) (by norm_num)
theorem B2744621 : Blo 1829616 2744621 := bbase (se 3 (by rfl) ⟨514616, by rfl⟩ : syracuseStep 2744621 = 1029233) (by norm_num)
theorem B3088685 : Blo 1829616 3088685 := bbase (se 3 (by rfl) ⟨579128, by rfl⟩ : syracuseStep 3088685 = 1158257) (by norm_num)
theorem B2744645 : Blo 1829616 2744645 := bbase (se 4 (by rfl) ⟨257310, by rfl⟩ : syracuseStep 2744645 = 514621) (by norm_num)
theorem B4120901 : Blo 1829616 4120901 := bbase (se 4 (by rfl) ⟨386334, by rfl⟩ : syracuseStep 4120901 = 772669) (by norm_num)
theorem B2744669 : Blo 1829616 2744669 := bbase (se 3 (by rfl) ⟨514625, by rfl⟩ : syracuseStep 2744669 = 1029251) (by norm_num)
theorem B2933101 : Blo 1829616 2933101 := bbase (se 3 (by rfl) ⟨549956, by rfl⟩ : syracuseStep 2933101 = 1099913) (by norm_num)
theorem B2744693 : Blo 1829616 2744693 := bbase (se 5 (by rfl) ⟨128657, by rfl⟩ : syracuseStep 2744693 = 257315) (by norm_num)
theorem B2744717 : Blo 1829616 2744717 := bbase (se 3 (by rfl) ⟨514634, by rfl⟩ : syracuseStep 2744717 = 1029269) (by norm_num)
theorem B4120973 : Blo 1829616 4120973 := bbase (se 3 (by rfl) ⟨772682, by rfl⟩ : syracuseStep 4120973 = 1545365) (by norm_num)
theorem B2744741 : Blo 1829616 2744741 := bbase (se 4 (by rfl) ⟨257319, by rfl⟩ : syracuseStep 2744741 = 514639) (by norm_num)
theorem B3473837 : Blo 1829616 3473837 := bbase (se 3 (by rfl) ⟨651344, by rfl⟩ : syracuseStep 3473837 = 1302689) (by norm_num)
theorem B3088813 : Blo 1829616 3088813 := bbase (se 3 (by rfl) ⟨579152, by rfl⟩ : syracuseStep 3088813 = 1158305) (by norm_num)
theorem B9265589 : Blo 1829616 9265589 := bbase (se 5 (by rfl) ⟨434324, by rfl⟩ : syracuseStep 9265589 = 868649) (by norm_num)
theorem B2744765 : Blo 1829616 2744765 := bbase (se 3 (by rfl) ⟨514643, by rfl⟩ : syracuseStep 2744765 = 1029287) (by norm_num)
theorem B6177221 : Blo 1829616 6177221 := bbase (se 4 (by rfl) ⟨579114, by rfl⟩ : syracuseStep 6177221 = 1158229) (by norm_num)
theorem B2744789 : Blo 1829616 2744789 := bbase (se 7 (by rfl) ⟨32165, by rfl⟩ : syracuseStep 2744789 = 64331) (by norm_num)
theorem B4121045 : Blo 1829616 4121045 := bbase (se 7 (by rfl) ⟨48293, by rfl⟩ : syracuseStep 4121045 = 96587) (by norm_num)
theorem B2744813 : Blo 1829616 2744813 := bbase (se 3 (by rfl) ⟨514652, by rfl⟩ : syracuseStep 2744813 = 1029305) (by norm_num)
theorem B2605549 : Blo 1829616 2605549 := bbase (se 3 (by rfl) ⟨488540, by rfl⟩ : syracuseStep 2605549 = 977081) (by norm_num)
theorem B4399613 : Blo 1829616 4399613 := bbase (se 3 (by rfl) ⟨824927, by rfl⟩ : syracuseStep 4399613 = 1649855) (by norm_num)
theorem B3908101 : Blo 1829616 3908101 := bbase (se 4 (by rfl) ⟨366384, by rfl⟩ : syracuseStep 3908101 = 732769) (by norm_num)
theorem B2744837 : Blo 1829616 2744837 := bbase (se 4 (by rfl) ⟨257328, by rfl⟩ : syracuseStep 2744837 = 514657) (by norm_num)
theorem B3088901 : Blo 1829616 3088901 := bbase (se 4 (by rfl) ⟨289584, by rfl⟩ : syracuseStep 3088901 = 579169) (by norm_num)
theorem B2744861 : Blo 1829616 2744861 := bbase (se 3 (by rfl) ⟨514661, by rfl⟩ : syracuseStep 2744861 = 1029323) (by norm_num)
theorem B4121117 : Blo 1829616 4121117 := bbase (se 3 (by rfl) ⟨772709, by rfl⟩ : syracuseStep 4121117 = 1545419) (by norm_num)
theorem B9519653 : Blo 1829616 9519653 := bbase (se 4 (by rfl) ⟨892467, by rfl⟩ : syracuseStep 9519653 = 1784935) (by norm_num)
theorem B2744885 : Blo 1829616 2744885 := bbase (se 5 (by rfl) ⟨128666, by rfl⟩ : syracuseStep 2744885 = 257333) (by norm_num)
theorem B2744909 : Blo 1829616 2744909 := bbase (se 3 (by rfl) ⟨514670, by rfl⟩ : syracuseStep 2744909 = 1029341) (by norm_num)
theorem B6431333 : Blo 1829616 6431333 := bbase (se 4 (by rfl) ⟨602937, by rfl⟩ : syracuseStep 6431333 = 1205875) (by norm_num)
theorem B2744933 : Blo 1829616 2744933 := bbase (se 4 (by rfl) ⟨257337, by rfl⟩ : syracuseStep 2744933 = 514675) (by norm_num)
theorem B2744957 : Blo 1829616 2744957 := bbase (se 3 (by rfl) ⟨514679, by rfl⟩ : syracuseStep 2744957 = 1029359) (by norm_num)
theorem B3089029 : Blo 1829616 3089029 := bbase (se 4 (by rfl) ⟨289596, by rfl⟩ : syracuseStep 3089029 = 579193) (by norm_num)
theorem B6947477 : Blo 1829616 6947477 := bbase (se 6 (by rfl) ⟨162831, by rfl⟩ : syracuseStep 6947477 = 325663) (by norm_num)
theorem B2744981 : Blo 1829616 2744981 := bbase (se 6 (by rfl) ⟨64335, by rfl⟩ : syracuseStep 2744981 = 128671) (by norm_num)
theorem B2745005 : Blo 1829616 2745005 := bbase (se 3 (by rfl) ⟨514688, by rfl⟩ : syracuseStep 2745005 = 1029377) (by norm_num)
theorem B2745029 : Blo 1829616 2745029 := bbase (se 4 (by rfl) ⟨257346, by rfl⟩ : syracuseStep 2745029 = 514693) (by norm_num)
theorem B2605765 : Blo 1829616 2605765 := bbase (se 4 (by rfl) ⟨244290, by rfl⟩ : syracuseStep 2605765 = 488581) (by norm_num)
theorem B2745053 : Blo 1829616 2745053 := bbase (se 3 (by rfl) ⟨514697, by rfl⟩ : syracuseStep 2745053 = 1029395) (by norm_num)
theorem B3089117 : Blo 1829616 3089117 := bbase (se 3 (by rfl) ⟨579209, by rfl⟩ : syracuseStep 3089117 = 1158419) (by norm_num)
theorem B2745077 : Blo 1829616 2745077 := bbase (se 5 (by rfl) ⟨128675, by rfl⟩ : syracuseStep 2745077 = 257351) (by norm_num)
theorem B2745101 : Blo 1829616 2745101 := bbase (se 3 (by rfl) ⟨514706, by rfl⟩ : syracuseStep 2745101 = 1029413) (by norm_num)
theorem B6259477 : Blo 1829616 6259477 := bbase (se 6 (by rfl) ⟨146706, by rfl⟩ : syracuseStep 6259477 = 293413) (by norm_num)
theorem B2745125 : Blo 1829616 2745125 := bbase (se 4 (by rfl) ⟨257355, by rfl⟩ : syracuseStep 2745125 = 514711) (by norm_num)
theorem B2745149 : Blo 1829616 2745149 := bbase (se 3 (by rfl) ⟨514715, by rfl⟩ : syracuseStep 2745149 = 1029431) (by norm_num)
theorem B2745173 : Blo 1829616 2745173 := bbase (se 9 (by rfl) ⟨8042, by rfl⟩ : syracuseStep 2745173 = 16085) (by norm_num)
theorem B3089245 : Blo 1829616 3089245 := bbase (se 3 (by rfl) ⟨579233, by rfl⟩ : syracuseStep 3089245 = 1158467) (by norm_num)
theorem B2745197 : Blo 1829616 2745197 := bbase (se 3 (by rfl) ⟨514724, by rfl⟩ : syracuseStep 2745197 = 1029449) (by norm_num)
theorem B6177653 : Blo 1829616 6177653 := bbase (se 5 (by rfl) ⟨289577, by rfl⟩ : syracuseStep 6177653 = 579155) (by norm_num)
theorem B2474869 : Blo 1829616 2474869 := bbase (se 5 (by rfl) ⟨116009, by rfl⟩ : syracuseStep 2474869 = 232019) (by norm_num)
theorem B2745221 : Blo 1829616 2745221 := bbase (se 4 (by rfl) ⟨257364, by rfl⟩ : syracuseStep 2745221 = 514729) (by norm_num)
theorem B5211029 : Blo 1829616 5211029 := bbase (se 6 (by rfl) ⟨122133, by rfl⟩ : syracuseStep 5211029 = 244267) (by norm_num)
theorem B2745245 : Blo 1829616 2745245 := bbase (se 3 (by rfl) ⟨514733, by rfl⟩ : syracuseStep 2745245 = 1029467) (by norm_num)
theorem B6947765 : Blo 1829616 6947765 := bbase (se 5 (by rfl) ⟨325676, by rfl⟩ : syracuseStep 6947765 = 651353) (by norm_num)
theorem B2745269 : Blo 1829616 2745269 := bbase (se 5 (by rfl) ⟨128684, by rfl⟩ : syracuseStep 2745269 = 257369) (by norm_num)
theorem B3089333 : Blo 1829616 3089333 := bbase (se 5 (by rfl) ⟨144812, by rfl⟩ : syracuseStep 3089333 = 289625) (by norm_num)
theorem B13198261 : Blo 1829616 13198261 := bbase (se 5 (by rfl) ⟨618668, by rfl⟩ : syracuseStep 13198261 = 1237337) (by norm_num)
theorem B2745293 : Blo 1829616 2745293 := bbase (se 3 (by rfl) ⟨514742, by rfl⟩ : syracuseStep 2745293 = 1029485) (by norm_num)
theorem B2745317 : Blo 1829616 2745317 := bbase (se 4 (by rfl) ⟨257373, by rfl⟩ : syracuseStep 2745317 = 514747) (by norm_num)
theorem B10421237 : Blo 1829616 10421237 := bbase (se 5 (by rfl) ⟨488495, by rfl⟩ : syracuseStep 10421237 = 976991) (by norm_num)
theorem B2745341 : Blo 1829616 2745341 := bbase (se 3 (by rfl) ⟨514751, by rfl⟩ : syracuseStep 2745341 = 1029503) (by norm_num)
theorem B3343357 : Blo 1829616 3343357 := bbase (se 3 (by rfl) ⟨626879, by rfl⟩ : syracuseStep 3343357 = 1253759) (by norm_num)
theorem B2745365 : Blo 1829616 2745365 := bbase (se 6 (by rfl) ⟨64344, by rfl⟩ : syracuseStep 2745365 = 128689) (by norm_num)
theorem B2745389 : Blo 1829616 2745389 := bbase (se 3 (by rfl) ⟨514760, by rfl⟩ : syracuseStep 2745389 = 1029521) (by norm_num)
theorem B3089461 : Blo 1829616 3089461 := bbase (se 5 (by rfl) ⟨144818, by rfl⟩ : syracuseStep 3089461 = 289637) (by norm_num)
theorem B2008121 : Blo 1829616 2008121 := bbase (se 2 (by rfl) ⟨753045, by rfl⟩ : syracuseStep 2008121 = 1506091) (by norm_num)
theorem B2606141 : Blo 1829616 2606141 := bbase (se 3 (by rfl) ⟨488651, by rfl⟩ : syracuseStep 2606141 = 977303) (by norm_num)
theorem B2745413 : Blo 1829616 2745413 := bbase (se 4 (by rfl) ⟨257382, by rfl⟩ : syracuseStep 2745413 = 514765) (by norm_num)
theorem B9290821 : Blo 1829616 9290821 := bbase (se 4 (by rfl) ⟨871014, by rfl⟩ : syracuseStep 9290821 = 1742029) (by norm_num)
theorem B2475085 : Blo 1829616 2475085 := bbase (se 3 (by rfl) ⟨464078, by rfl⟩ : syracuseStep 2475085 = 928157) (by norm_num)
theorem B2745437 : Blo 1829616 2745437 := bbase (se 3 (by rfl) ⟨514769, by rfl⟩ : syracuseStep 2745437 = 1029539) (by norm_num)
theorem B2745461 : Blo 1829616 2745461 := bbase (se 5 (by rfl) ⟨128693, by rfl⟩ : syracuseStep 2745461 = 257387) (by norm_num)
theorem B2745485 : Blo 1829616 2745485 := bbase (se 3 (by rfl) ⟨514778, by rfl⟩ : syracuseStep 2745485 = 1029557) (by norm_num)
theorem B3089549 : Blo 1829616 3089549 := bbase (se 3 (by rfl) ⟨579290, by rfl⟩ : syracuseStep 3089549 = 1158581) (by norm_num)
theorem B3474589 : Blo 1829616 3474589 := bbase (se 3 (by rfl) ⟨651485, by rfl⟩ : syracuseStep 3474589 = 1302971) (by norm_num)
theorem B2507933 : Blo 1829616 2507933 := bbase (se 3 (by rfl) ⟨470237, by rfl⟩ : syracuseStep 2507933 = 940475) (by norm_num)
theorem B2745509 : Blo 1829616 2745509 := bbase (se 4 (by rfl) ⟨257391, by rfl⟩ : syracuseStep 2745509 = 514783) (by norm_num)
theorem B3523757 : Blo 1829616 3523757 := bbase (se 3 (by rfl) ⟨660704, by rfl⟩ : syracuseStep 3523757 = 1321409) (by norm_num)
theorem B2745533 : Blo 1829616 2745533 := bbase (se 3 (by rfl) ⟨514787, by rfl⟩ : syracuseStep 2745533 = 1029575) (by norm_num)
theorem B2745557 : Blo 1829616 2745557 := bbase (se 7 (by rfl) ⟨32174, by rfl⟩ : syracuseStep 2745557 = 64349) (by norm_num)
theorem B3130589 : Blo 1829616 3130589 := bbase (se 3 (by rfl) ⟨586985, by rfl⟩ : syracuseStep 3130589 = 1173971) (by norm_num)
theorem B2745581 : Blo 1829616 2745581 := bbase (se 3 (by rfl) ⟨514796, by rfl⟩ : syracuseStep 2745581 = 1029593) (by norm_num)
theorem B2745605 : Blo 1829616 2745605 := bbase (se 4 (by rfl) ⟨257400, by rfl⟩ : syracuseStep 2745605 = 514801) (by norm_num)
theorem B3089677 : Blo 1829616 3089677 := bbase (se 3 (by rfl) ⟨579314, by rfl⟩ : syracuseStep 3089677 = 1158629) (by norm_num)
theorem B2745629 : Blo 1829616 2745629 := bbase (se 3 (by rfl) ⟨514805, by rfl⟩ : syracuseStep 2745629 = 1029611) (by norm_num)
theorem B6178085 : Blo 1829616 6178085 := bbase (se 4 (by rfl) ⟨579195, by rfl⟩ : syracuseStep 6178085 = 1158391) (by norm_num)
theorem B3474733 : Blo 1829616 3474733 := bbase (se 3 (by rfl) ⟨651512, by rfl⟩ : syracuseStep 3474733 = 1303025) (by norm_num)
theorem B2745653 : Blo 1829616 2745653 := bbase (se 5 (by rfl) ⟨128702, by rfl⟩ : syracuseStep 2745653 = 257405) (by norm_num)
theorem B2114881 : Blo 1829616 2114881 := bbase (se 2 (by rfl) ⟨793080, by rfl⟩ : syracuseStep 2114881 = 1586161) (by norm_num)
theorem B2745677 : Blo 1829616 2745677 := bbase (se 3 (by rfl) ⟨514814, by rfl⟩ : syracuseStep 2745677 = 1029629) (by norm_num)
theorem B2745701 : Blo 1829616 2745701 := bbase (se 4 (by rfl) ⟨257409, by rfl⟩ : syracuseStep 2745701 = 514819) (by norm_num)
theorem B3089765 : Blo 1829616 3089765 := bbase (se 4 (by rfl) ⟨289665, by rfl⟩ : syracuseStep 3089765 = 579331) (by norm_num)
theorem B3908989 : Blo 1829616 3908989 := bbase (se 3 (by rfl) ⟨732935, by rfl⟩ : syracuseStep 3908989 = 1465871) (by norm_num)
theorem B2745725 : Blo 1829616 2745725 := bbase (se 3 (by rfl) ⟨514823, by rfl⟩ : syracuseStep 2745725 = 1029647) (by norm_num)
theorem B2745749 : Blo 1829616 2745749 := bbase (se 6 (by rfl) ⟨64353, by rfl⟩ : syracuseStep 2745749 = 128707) (by norm_num)
theorem B2745773 : Blo 1829616 2745773 := bbase (se 3 (by rfl) ⟨514832, by rfl⟩ : syracuseStep 2745773 = 1029665) (by norm_num)
theorem B3761605 : Blo 1829616 3761605 := bbase (se 4 (by rfl) ⟨352650, by rfl⟩ : syracuseStep 3761605 = 705301) (by norm_num)
theorem B2745797 : Blo 1829616 2745797 := bbase (se 4 (by rfl) ⟨257418, by rfl⟩ : syracuseStep 2745797 = 514837) (by norm_num)
theorem B3474893 : Blo 1829616 3474893 := bbase (se 3 (by rfl) ⟨651542, by rfl⟩ : syracuseStep 3474893 = 1303085) (by norm_num)
theorem B2745821 : Blo 1829616 2745821 := bbase (se 3 (by rfl) ⟨514841, by rfl⟩ : syracuseStep 2745821 = 1029683) (by norm_num)
theorem B3089893 : Blo 1829616 3089893 := bbase (se 4 (by rfl) ⟨289677, by rfl⟩ : syracuseStep 3089893 = 579355) (by norm_num)
theorem B4695533 : Blo 1829616 4695533 := bbase (se 3 (by rfl) ⟨880412, by rfl⟩ : syracuseStep 4695533 = 1760825) (by norm_num)
theorem B2745845 : Blo 1829616 2745845 := bbase (se 5 (by rfl) ⟨128711, by rfl⟩ : syracuseStep 2745845 = 257423) (by norm_num)
theorem B2745869 : Blo 1829616 2745869 := bbase (se 3 (by rfl) ⟨514850, by rfl⟩ : syracuseStep 2745869 = 1029701) (by norm_num)
theorem B2745893 : Blo 1829616 2745893 := bbase (se 4 (by rfl) ⟨257427, by rfl⟩ : syracuseStep 2745893 = 514855) (by norm_num)
theorem B2745917 : Blo 1829616 2745917 := bbase (se 3 (by rfl) ⟨514859, by rfl⟩ : syracuseStep 2745917 = 1029719) (by norm_num)
theorem B3089981 : Blo 1829616 3089981 := bbase (se 3 (by rfl) ⟨579371, by rfl⟩ : syracuseStep 3089981 = 1158743) (by norm_num)
theorem B2745941 : Blo 1829616 2745941 := bbase (se 8 (by rfl) ⟨16089, by rfl⟩ : syracuseStep 2745941 = 32179) (by norm_num)
theorem B3475037 : Blo 1829616 3475037 := bbase (se 3 (by rfl) ⟨651569, by rfl⟩ : syracuseStep 3475037 = 1303139) (by norm_num)
theorem B2745965 : Blo 1829616 2745965 := bbase (se 3 (by rfl) ⟨514868, by rfl⟩ : syracuseStep 2745965 = 1029737) (by norm_num)
theorem B2745989 : Blo 1829616 2745989 := bbase (se 4 (by rfl) ⟨257436, by rfl⟩ : syracuseStep 2745989 = 514873) (by norm_num)
theorem B2746013 : Blo 1829616 2746013 := bbase (se 3 (by rfl) ⟨514877, by rfl⟩ : syracuseStep 2746013 = 1029755) (by norm_num)
theorem B2746037 : Blo 1829616 2746037 := bbase (se 5 (by rfl) ⟨128720, by rfl⟩ : syracuseStep 2746037 = 257441) (by norm_num)
theorem B3090109 : Blo 1829616 3090109 := bbase (se 3 (by rfl) ⟨579395, by rfl⟩ : syracuseStep 3090109 = 1158791) (by norm_num)
theorem B9266885 : Blo 1829616 9266885 := bbase (se 4 (by rfl) ⟨868770, by rfl⟩ : syracuseStep 9266885 = 1737541) (by norm_num)
theorem B2746061 : Blo 1829616 2746061 := bbase (se 3 (by rfl) ⟨514886, by rfl⟩ : syracuseStep 2746061 = 1029773) (by norm_num)
theorem B6178517 : Blo 1829616 6178517 := bbase (se 7 (by rfl) ⟨72404, by rfl⟩ : syracuseStep 6178517 = 144809) (by norm_num)
theorem B2746085 : Blo 1829616 2746085 := bbase (se 4 (by rfl) ⟨257445, by rfl⟩ : syracuseStep 2746085 = 514891) (by norm_num)
theorem B2746109 : Blo 1829616 2746109 := bbase (se 3 (by rfl) ⟨514895, by rfl⟩ : syracuseStep 2746109 = 1029791) (by norm_num)
theorem B2746133 : Blo 1829616 2746133 := bbase (se 6 (by rfl) ⟨64362, by rfl⟩ : syracuseStep 2746133 = 128725) (by norm_num)
theorem B3090197 : Blo 1829616 3090197 := bbase (se 6 (by rfl) ⟨72426, by rfl⟩ : syracuseStep 3090197 = 144853) (by norm_num)
theorem B2746157 : Blo 1829616 2746157 := bbase (se 3 (by rfl) ⟨514904, by rfl⟩ : syracuseStep 2746157 = 1029809) (by norm_num)
theorem B2746181 : Blo 1829616 2746181 := bbase (se 4 (by rfl) ⟨257454, by rfl⟩ : syracuseStep 2746181 = 514909) (by norm_num)
theorem B2746205 : Blo 1829616 2746205 := bbase (se 3 (by rfl) ⟨514913, by rfl⟩ : syracuseStep 2746205 = 1029827) (by norm_num)
theorem B3909485 : Blo 1829616 3909485 := bbase (se 3 (by rfl) ⟨733028, by rfl⟩ : syracuseStep 3909485 = 1466057) (by norm_num)
theorem B2746229 : Blo 1829616 2746229 := bbase (se 5 (by rfl) ⟨128729, by rfl⟩ : syracuseStep 2746229 = 257459) (by norm_num)
theorem B3475325 : Blo 1829616 3475325 := bbase (se 3 (by rfl) ⟨651623, by rfl⟩ : syracuseStep 3475325 = 1303247) (by norm_num)
theorem B2746253 : Blo 1829616 2746253 := bbase (se 3 (by rfl) ⟨514922, by rfl⟩ : syracuseStep 2746253 = 1029845) (by norm_num)
theorem B3090325 : Blo 1829616 3090325 := bbase (se 6 (by rfl) ⟨72429, by rfl⟩ : syracuseStep 3090325 = 144859) (by norm_num)
theorem B2746277 : Blo 1829616 2746277 := bbase (se 4 (by rfl) ⟨257463, by rfl⟩ : syracuseStep 2746277 = 514927) (by norm_num)
theorem B2746301 : Blo 1829616 2746301 := bbase (se 3 (by rfl) ⟨514931, by rfl⟩ : syracuseStep 2746301 = 1029863) (by norm_num)
theorem B2746325 : Blo 1829616 2746325 := bbase (se 7 (by rfl) ⟨32183, by rfl⟩ : syracuseStep 2746325 = 64367) (by norm_num)
theorem B2746349 : Blo 1829616 2746349 := bbase (se 3 (by rfl) ⟨514940, by rfl⟩ : syracuseStep 2746349 = 1029881) (by norm_num)
theorem B3090413 : Blo 1829616 3090413 := bbase (se 3 (by rfl) ⟨579452, by rfl⟩ : syracuseStep 3090413 = 1158905) (by norm_num)
theorem B2746373 : Blo 1829616 2746373 := bbase (se 4 (by rfl) ⟨257472, by rfl⟩ : syracuseStep 2746373 = 514945) (by norm_num)
theorem B30083093 : Blo 1829616 30083093 := bbase (se 6 (by rfl) ⟨705072, by rfl⟩ : syracuseStep 30083093 = 1410145) (by norm_num)
theorem B3475477 : Blo 1829616 3475477 := bbase (se 6 (by rfl) ⟨81456, by rfl⟩ : syracuseStep 3475477 = 162913) (by norm_num)
theorem B2746397 : Blo 1829616 2746397 := bbase (se 3 (by rfl) ⟨514949, by rfl⟩ : syracuseStep 2746397 = 1029899) (by norm_num)
theorem B7047205 : Blo 1829616 7047205 := bbase (se 4 (by rfl) ⟨660675, by rfl⟩ : syracuseStep 7047205 = 1321351) (by norm_num)
theorem B2746421 : Blo 1829616 2746421 := bbase (se 5 (by rfl) ⟨128738, by rfl⟩ : syracuseStep 2746421 = 257477) (by norm_num)
theorem B2746445 : Blo 1829616 2746445 := bbase (se 3 (by rfl) ⟨514958, by rfl⟩ : syracuseStep 2746445 = 1029917) (by norm_num)
theorem B6948949 : Blo 1829616 6948949 := bbase (se 8 (by rfl) ⟨40716, by rfl⟩ : syracuseStep 6948949 = 81433) (by norm_num)
theorem B2746469 : Blo 1829616 2746469 := bbase (se 4 (by rfl) ⟨257481, by rfl⟩ : syracuseStep 2746469 = 514963) (by norm_num)
theorem B2058349 : Blo 1829616 2058349 := bbase (se 3 (by rfl) ⟨385940, by rfl⟩ : syracuseStep 2058349 = 771881) (by norm_num)
theorem B3090541 : Blo 1829616 3090541 := bbase (se 3 (by rfl) ⟨579476, by rfl⟩ : syracuseStep 3090541 = 1158953) (by norm_num)
theorem B2746493 : Blo 1829616 2746493 := bbase (se 3 (by rfl) ⟨514967, by rfl⟩ : syracuseStep 2746493 = 1029935) (by norm_num)
theorem B6178949 : Blo 1829616 6178949 := bbase (se 4 (by rfl) ⟨579276, by rfl⟩ : syracuseStep 6178949 = 1158553) (by norm_num)
theorem B2058385 : Blo 1829616 2058385 := bbase (se 2 (by rfl) ⟨771894, by rfl⟩ : syracuseStep 2058385 = 1543789) (by norm_num)
theorem B2746517 : Blo 1829616 2746517 := bbase (se 6 (by rfl) ⟨64371, by rfl⟩ : syracuseStep 2746517 = 128743) (by norm_num)
theorem B2746541 : Blo 1829616 2746541 := bbase (se 3 (by rfl) ⟨514976, by rfl⟩ : syracuseStep 2746541 = 1029953) (by norm_num)
theorem B2058421 : Blo 1829616 2058421 := bbase (se 5 (by rfl) ⟨96488, by rfl⟩ : syracuseStep 2058421 = 192977) (by norm_num)
theorem B11733173 : Blo 1829616 11733173 := bbase (se 5 (by rfl) ⟨549992, by rfl⟩ : syracuseStep 11733173 = 1099985) (by norm_num)
theorem B2746565 : Blo 1829616 2746565 := bbase (se 4 (by rfl) ⟨257490, by rfl⟩ : syracuseStep 2746565 = 514981) (by norm_num)
theorem B3090629 : Blo 1829616 3090629 := bbase (se 4 (by rfl) ⟨289746, by rfl⟩ : syracuseStep 3090629 = 579493) (by norm_num)
theorem B2058457 : Blo 1829616 2058457 := bbase (se 2 (by rfl) ⟨771921, by rfl⟩ : syracuseStep 2058457 = 1543843) (by norm_num)
theorem B4761821 : Blo 1829616 4761821 := bbase (se 3 (by rfl) ⟨892841, by rfl⟩ : syracuseStep 4761821 = 1785683) (by norm_num)
theorem B2746589 : Blo 1829616 2746589 := bbase (se 3 (by rfl) ⟨514985, by rfl⟩ : syracuseStep 2746589 = 1029971) (by norm_num)
theorem B2115829 : Blo 1829616 2115829 := bbase (se 5 (by rfl) ⟨99179, by rfl⟩ : syracuseStep 2115829 = 198359) (by norm_num)
theorem B2746613 : Blo 1829616 2746613 := bbase (se 5 (by rfl) ⟨128747, by rfl⟩ : syracuseStep 2746613 = 257495) (by norm_num)
theorem B2058493 : Blo 1829616 2058493 := bbase (se 3 (by rfl) ⟨385967, by rfl⟩ : syracuseStep 2058493 = 771935) (by norm_num)
theorem B2746637 : Blo 1829616 2746637 := bbase (se 3 (by rfl) ⟨514994, by rfl⟩ : syracuseStep 2746637 = 1029989) (by norm_num)
theorem B2058529 : Blo 1829616 2058529 := bbase (se 2 (by rfl) ⟨771948, by rfl⟩ : syracuseStep 2058529 = 1543897) (by norm_num)
theorem B2746661 : Blo 1829616 2746661 := bbase (se 4 (by rfl) ⟨257499, by rfl⟩ : syracuseStep 2746661 = 514999) (by norm_num)
theorem B2746685 : Blo 1829616 2746685 := bbase (se 3 (by rfl) ⟨515003, by rfl⟩ : syracuseStep 2746685 = 1030007) (by norm_num)
theorem B2058565 : Blo 1829616 2058565 := bbase (se 4 (by rfl) ⟨192990, by rfl⟩ : syracuseStep 2058565 = 385981) (by norm_num)
theorem B3475781 : Blo 1829616 3475781 := bbase (se 4 (by rfl) ⟨325854, by rfl⟩ : syracuseStep 3475781 = 651709) (by norm_num)
theorem B3090757 : Blo 1829616 3090757 := bbase (se 4 (by rfl) ⟨289758, by rfl⟩ : syracuseStep 3090757 = 579517) (by norm_num)
theorem B2746709 : Blo 1829616 2746709 := bbase (se 10 (by rfl) ⟨4023, by rfl⟩ : syracuseStep 2746709 = 8047) (by norm_num)
theorem B2058601 : Blo 1829616 2058601 := bbase (se 2 (by rfl) ⟨771975, by rfl⟩ : syracuseStep 2058601 = 1543951) (by norm_num)
theorem B2746733 : Blo 1829616 2746733 := bbase (se 3 (by rfl) ⟨515012, by rfl⟩ : syracuseStep 2746733 = 1030025) (by norm_num)
theorem B6949253 : Blo 1829616 6949253 := bbase (se 4 (by rfl) ⟨651492, by rfl⟩ : syracuseStep 6949253 = 1302985) (by norm_num)
theorem B2746757 : Blo 1829616 2746757 := bbase (se 4 (by rfl) ⟨257508, by rfl⟩ : syracuseStep 2746757 = 515017) (by norm_num)
theorem B2058637 : Blo 1829616 2058637 := bbase (se 3 (by rfl) ⟨385994, by rfl⟩ : syracuseStep 2058637 = 771989) (by norm_num)
theorem B2746781 : Blo 1829616 2746781 := bbase (se 3 (by rfl) ⟨515021, by rfl⟩ : syracuseStep 2746781 = 1030043) (by norm_num)
theorem B3090845 : Blo 1829616 3090845 := bbase (se 3 (by rfl) ⟨579533, by rfl⟩ : syracuseStep 3090845 = 1159067) (by norm_num)
theorem B2058673 : Blo 1829616 2058673 := bbase (se 2 (by rfl) ⟨772002, by rfl⟩ : syracuseStep 2058673 = 1544005) (by norm_num)
theorem B2746805 : Blo 1829616 2746805 := bbase (se 5 (by rfl) ⟨128756, by rfl⟩ : syracuseStep 2746805 = 257513) (by norm_num)
theorem B5212613 : Blo 1829616 5212613 := bbase (se 4 (by rfl) ⟨488682, by rfl⟩ : syracuseStep 5212613 = 977365) (by norm_num)
theorem B2746829 : Blo 1829616 2746829 := bbase (se 3 (by rfl) ⟨515030, by rfl⟩ : syracuseStep 2746829 = 1030061) (by norm_num)
theorem B2607565 : Blo 1829616 2607565 := bbase (se 3 (by rfl) ⟨488918, by rfl⟩ : syracuseStep 2607565 = 977837) (by norm_num)
theorem B2058709 : Blo 1829616 2058709 := bbase (se 7 (by rfl) ⟨24125, by rfl⟩ : syracuseStep 2058709 = 48251) (by norm_num)
theorem B2746853 : Blo 1829616 2746853 := bbase (se 4 (by rfl) ⟨257517, by rfl⟩ : syracuseStep 2746853 = 515035) (by norm_num)
theorem B4950517 : Blo 1829616 4950517 := bbase (se 5 (by rfl) ⟨232055, by rfl⟩ : syracuseStep 4950517 = 464111) (by norm_num)
theorem B2058745 : Blo 1829616 2058745 := bbase (se 2 (by rfl) ⟨772029, by rfl⟩ : syracuseStep 2058745 = 1544059) (by norm_num)
theorem B2746877 : Blo 1829616 2746877 := bbase (se 3 (by rfl) ⟨515039, by rfl⟩ : syracuseStep 2746877 = 1030079) (by norm_num)
theorem B2746901 : Blo 1829616 2746901 := bbase (se 6 (by rfl) ⟨64380, by rfl⟩ : syracuseStep 2746901 = 128761) (by norm_num)
theorem B5286421 : Blo 1829616 5286421 := bbase (se 6 (by rfl) ⟨123900, by rfl⟩ : syracuseStep 5286421 = 247801) (by norm_num)
theorem B2058781 : Blo 1829616 2058781 := bbase (se 3 (by rfl) ⟨386021, by rfl⟩ : syracuseStep 2058781 = 772043) (by norm_num)
theorem B2746925 : Blo 1829616 2746925 := bbase (se 3 (by rfl) ⟨515048, by rfl⟩ : syracuseStep 2746925 = 1030097) (by norm_num)
theorem B6179381 : Blo 1829616 6179381 := bbase (se 5 (by rfl) ⟨289658, by rfl⟩ : syracuseStep 6179381 = 579317) (by norm_num)
theorem B2058817 : Blo 1829616 2058817 := bbase (se 2 (by rfl) ⟨772056, by rfl⟩ : syracuseStep 2058817 = 1544113) (by norm_num)
theorem B2746949 : Blo 1829616 2746949 := bbase (se 4 (by rfl) ⟨257526, by rfl⟩ : syracuseStep 2746949 = 515053) (by norm_num)
theorem B2746973 : Blo 1829616 2746973 := bbase (se 3 (by rfl) ⟨515057, by rfl⟩ : syracuseStep 2746973 = 1030115) (by norm_num)
theorem B2058853 : Blo 1829616 2058853 := bbase (se 4 (by rfl) ⟨193017, by rfl⟩ : syracuseStep 2058853 = 386035) (by norm_num)
theorem B2198125 : Blo 1829616 2198125 := bbase (se 3 (by rfl) ⟨412148, by rfl⟩ : syracuseStep 2198125 = 824297) (by norm_num)
theorem B2746997 : Blo 1829616 2746997 := bbase (se 5 (by rfl) ⟨128765, by rfl⟩ : syracuseStep 2746997 = 257531) (by norm_num)
theorem B2058889 : Blo 1829616 2058889 := bbase (se 2 (by rfl) ⟨772083, by rfl⟩ : syracuseStep 2058889 = 1544167) (by norm_num)
theorem B2747021 : Blo 1829616 2747021 := bbase (se 3 (by rfl) ⟨515066, by rfl⟩ : syracuseStep 2747021 = 1030133) (by norm_num)
theorem B10431125 : Blo 1829616 10431125 := bbase (se 6 (by rfl) ⟨244479, by rfl⟩ : syracuseStep 10431125 = 488959) (by norm_num)
theorem B2198173 : Blo 1829616 2198173 := bbase (se 3 (by rfl) ⟨412157, by rfl⟩ : syracuseStep 2198173 = 824315) (by norm_num)
theorem B2747045 : Blo 1829616 2747045 := bbase (se 4 (by rfl) ⟨257535, by rfl⟩ : syracuseStep 2747045 = 515071) (by norm_num)
theorem B2058925 : Blo 1829616 2058925 := bbase (se 3 (by rfl) ⟨386048, by rfl⟩ : syracuseStep 2058925 = 772097) (by norm_num)
theorem B19303093 : Blo 1829616 19303093 := bbase (se 5 (by rfl) ⟨904832, by rfl⟩ : syracuseStep 19303093 = 1809665) (by norm_num)
theorem B2747069 : Blo 1829616 2747069 := bbase (se 3 (by rfl) ⟨515075, by rfl⟩ : syracuseStep 2747069 = 1030151) (by norm_num)
theorem B3910349 : Blo 1829616 3910349 := bbase (se 3 (by rfl) ⟨733190, by rfl⟩ : syracuseStep 3910349 = 1466381) (by norm_num)
theorem B2058961 : Blo 1829616 2058961 := bbase (se 2 (by rfl) ⟨772110, by rfl⟩ : syracuseStep 2058961 = 1544221) (by norm_num)
theorem B13191893 : Blo 1829616 13191893 := bbase (se 7 (by rfl) ⟨154592, by rfl⟩ : syracuseStep 13191893 = 309185) (by norm_num)
theorem B20859605 : Blo 1829616 20859605 := bbase (se 7 (by rfl) ⟨244448, by rfl⟩ : syracuseStep 20859605 = 488897) (by norm_num)
theorem B2747093 : Blo 1829616 2747093 := bbase (se 7 (by rfl) ⟨32192, by rfl⟩ : syracuseStep 2747093 = 64385) (by norm_num)
theorem B2747117 : Blo 1829616 2747117 := bbase (se 3 (by rfl) ⟨515084, by rfl⟩ : syracuseStep 2747117 = 1030169) (by norm_num)
theorem B2058997 : Blo 1829616 2058997 := bbase (se 5 (by rfl) ⟨96515, by rfl⟩ : syracuseStep 2058997 = 193031) (by norm_num)
theorem B2747141 : Blo 1829616 2747141 := bbase (se 4 (by rfl) ⟨257544, by rfl⟩ : syracuseStep 2747141 = 515089) (by norm_num)
theorem B2059033 : Blo 1829616 2059033 := bbase (se 2 (by rfl) ⟨772137, by rfl⟩ : syracuseStep 2059033 = 1544275) (by norm_num)
theorem B2747165 : Blo 1829616 2747165 := bbase (se 3 (by rfl) ⟨515093, by rfl⟩ : syracuseStep 2747165 = 1030187) (by norm_num)
theorem B2747189 : Blo 1829616 2747189 := bbase (se 5 (by rfl) ⟨128774, by rfl⟩ : syracuseStep 2747189 = 257549) (by norm_num)
theorem B4631357 : Blo 1829616 4631357 := bbase (se 3 (by rfl) ⟨868379, by rfl⟩ : syracuseStep 4631357 = 1736759) (by norm_num)
theorem B2059069 : Blo 1829616 2059069 := bbase (se 3 (by rfl) ⟨386075, by rfl⟩ : syracuseStep 2059069 = 772151) (by norm_num)
theorem B6597445 : Blo 1829616 6597445 := bbase (se 4 (by rfl) ⟨618510, by rfl⟩ : syracuseStep 6597445 = 1237021) (by norm_num)
theorem B2747213 : Blo 1829616 2747213 := bbase (se 3 (by rfl) ⟨515102, by rfl⟩ : syracuseStep 2747213 = 1030205) (by norm_num)
theorem B3910493 : Blo 1829616 3910493 := bbase (se 3 (by rfl) ⟨733217, by rfl⟩ : syracuseStep 3910493 = 1466435) (by norm_num)
theorem B2059105 : Blo 1829616 2059105 := bbase (se 2 (by rfl) ⟨772164, by rfl⟩ : syracuseStep 2059105 = 1544329) (by norm_num)
theorem B2747237 : Blo 1829616 2747237 := bbase (se 4 (by rfl) ⟨257553, by rfl⟩ : syracuseStep 2747237 = 515107) (by norm_num)
theorem B2747261 : Blo 1829616 2747261 := bbase (se 3 (by rfl) ⟨515111, by rfl⟩ : syracuseStep 2747261 = 1030223) (by norm_num)
theorem B2059141 : Blo 1829616 2059141 := bbase (se 4 (by rfl) ⟨193044, by rfl⟩ : syracuseStep 2059141 = 386089) (by norm_num)
theorem B2747285 : Blo 1829616 2747285 := bbase (se 6 (by rfl) ⟨64389, by rfl⟩ : syracuseStep 2747285 = 128779) (by norm_num)
theorem B2059177 : Blo 1829616 2059177 := bbase (se 2 (by rfl) ⟨772191, by rfl⟩ : syracuseStep 2059177 = 1544383) (by norm_num)
theorem B2747309 : Blo 1829616 2747309 := bbase (se 3 (by rfl) ⟨515120, by rfl⟩ : syracuseStep 2747309 = 1030241) (by norm_num)
theorem B2747333 : Blo 1829616 2747333 := bbase (se 4 (by rfl) ⟨257562, by rfl⟩ : syracuseStep 2747333 = 515125) (by norm_num)
theorem B2059213 : Blo 1829616 2059213 := bbase (se 3 (by rfl) ⟨386102, by rfl⟩ : syracuseStep 2059213 = 772205) (by norm_num)
theorem B9268181 : Blo 1829616 9268181 := bbase (se 7 (by rfl) ⟨108611, by rfl⟩ : syracuseStep 9268181 = 217223) (by norm_num)
theorem B2747357 : Blo 1829616 2747357 := bbase (se 3 (by rfl) ⟨515129, by rfl⟩ : syracuseStep 2747357 = 1030259) (by norm_num)
theorem B6179813 : Blo 1829616 6179813 := bbase (se 4 (by rfl) ⟨579357, by rfl⟩ : syracuseStep 6179813 = 1158715) (by norm_num)
theorem B2059249 : Blo 1829616 2059249 := bbase (se 2 (by rfl) ⟨772218, by rfl⟩ : syracuseStep 2059249 = 1544437) (by norm_num)
theorem B2747381 : Blo 1829616 2747381 := bbase (se 5 (by rfl) ⟨128783, by rfl⟩ : syracuseStep 2747381 = 257567) (by norm_num)
theorem B2747405 : Blo 1829616 2747405 := bbase (se 3 (by rfl) ⟨515138, by rfl⟩ : syracuseStep 2747405 = 1030277) (by norm_num)
theorem B2059285 : Blo 1829616 2059285 := bbase (se 6 (by rfl) ⟨48264, by rfl⟩ : syracuseStep 2059285 = 96529) (by norm_num)
theorem B3476533 : Blo 1829616 3476533 := bbase (se 5 (by rfl) ⟨162962, by rfl⟩ : syracuseStep 3476533 = 325925) (by norm_num)
theorem B2059321 : Blo 1829616 2059321 := bbase (se 2 (by rfl) ⟨772245, by rfl⟩ : syracuseStep 2059321 = 1544491) (by norm_num)
theorem B19786837 : Blo 1829616 19786837 := bbase (se 8 (by rfl) ⟨115938, by rfl⟩ : syracuseStep 19786837 = 231877) (by norm_num)
theorem B2059357 : Blo 1829616 2059357 := bbase (se 3 (by rfl) ⟨386129, by rfl⟩ : syracuseStep 2059357 = 772259) (by norm_num)
theorem B5213285 : Blo 1829616 5213285 := bbase (se 4 (by rfl) ⟨488745, by rfl⟩ : syracuseStep 5213285 = 977491) (by norm_num)
theorem B2059393 : Blo 1829616 2059393 := bbase (se 2 (by rfl) ⟨772272, by rfl⟩ : syracuseStep 2059393 = 1544545) (by norm_num)
theorem B4631701 : Blo 1829616 4631701 := bbase (se 6 (by rfl) ⟨108555, by rfl⟩ : syracuseStep 4631701 = 217111) (by norm_num)
theorem B7818389 : Blo 1829616 7818389 := bbase (se 6 (by rfl) ⟨183243, by rfl⟩ : syracuseStep 7818389 = 366487) (by norm_num)
theorem B2059429 : Blo 1829616 2059429 := bbase (se 4 (by rfl) ⟨193071, by rfl⟩ : syracuseStep 2059429 = 386143) (by norm_num)
theorem B3476677 : Blo 1829616 3476677 := bbase (se 4 (by rfl) ⟨325938, by rfl⟩ : syracuseStep 3476677 = 651877) (by norm_num)
theorem B2059465 : Blo 1829616 2059465 := bbase (se 2 (by rfl) ⟨772299, by rfl⟩ : syracuseStep 2059465 = 1544599) (by norm_num)
theorem B2059501 : Blo 1829616 2059501 := bbase (se 3 (by rfl) ⟨386156, by rfl⟩ : syracuseStep 2059501 = 772313) (by norm_num)
theorem B4631813 : Blo 1829616 4631813 := bbase (se 4 (by rfl) ⟨434232, by rfl⟩ : syracuseStep 4631813 = 868465) (by norm_num)
theorem B2059537 : Blo 1829616 2059537 := bbase (se 2 (by rfl) ⟨772326, by rfl⟩ : syracuseStep 2059537 = 1544653) (by norm_num)
theorem B33393941 : Blo 1829616 33393941 := bbase (se 6 (by rfl) ⟨782670, by rfl⟩ : syracuseStep 33393941 = 1565341) (by norm_num)
theorem B2059573 : Blo 1829616 2059573 := bbase (se 5 (by rfl) ⟨96542, by rfl⟩ : syracuseStep 2059573 = 193085) (by norm_num)
theorem B2198845 : Blo 1829616 2198845 := bbase (se 3 (by rfl) ⟨412283, by rfl⟩ : syracuseStep 2198845 = 824567) (by norm_num)
theorem B2059609 : Blo 1829616 2059609 := bbase (se 2 (by rfl) ⟨772353, by rfl⟩ : syracuseStep 2059609 = 1544707) (by norm_num)
theorem B2542949 : Blo 1829616 2542949 := bbase (se 4 (by rfl) ⟨238401, by rfl⟩ : syracuseStep 2542949 = 476803) (by norm_num)
theorem B3476837 : Blo 1829616 3476837 := bbase (se 4 (by rfl) ⟨325953, by rfl⟩ : syracuseStep 3476837 = 651907) (by norm_num)
theorem B2059645 : Blo 1829616 2059645 := bbase (se 3 (by rfl) ⟨386183, by rfl⟩ : syracuseStep 2059645 = 772367) (by norm_num)
theorem B6180245 : Blo 1829616 6180245 := bbase (se 6 (by rfl) ⟨144849, by rfl⟩ : syracuseStep 6180245 = 289699) (by norm_num)
theorem B2059681 : Blo 1829616 2059681 := bbase (se 2 (by rfl) ⟨772380, by rfl⟩ : syracuseStep 2059681 = 1544761) (by norm_num)
theorem B4632005 : Blo 1829616 4632005 := bbase (se 4 (by rfl) ⟨434250, by rfl⟩ : syracuseStep 4632005 = 868501) (by norm_num)
theorem B2059717 : Blo 1829616 2059717 := bbase (se 4 (by rfl) ⟨193098, by rfl⟩ : syracuseStep 2059717 = 386197) (by norm_num)
theorem B28184021 : Blo 1829616 28184021 := bbase (se 7 (by rfl) ⟨330281, by rfl⟩ : syracuseStep 28184021 = 660563) (by norm_num)
theorem B2059753 : Blo 1829616 2059753 := bbase (se 2 (by rfl) ⟨772407, by rfl⟩ : syracuseStep 2059753 = 1544815) (by norm_num)
theorem B3476981 : Blo 1829616 3476981 := bbase (se 5 (by rfl) ⟨162983, by rfl⟩ : syracuseStep 3476981 = 325967) (by norm_num)
theorem B2641405 : Blo 1829616 2641405 := bbase (se 3 (by rfl) ⟨495263, by rfl⟩ : syracuseStep 2641405 = 990527) (by norm_num)
theorem B2059789 : Blo 1829616 2059789 := bbase (se 3 (by rfl) ⟨386210, by rfl⟩ : syracuseStep 2059789 = 772421) (by norm_num)
theorem B5213717 : Blo 1829616 5213717 := bbase (se 6 (by rfl) ⟨122196, by rfl⟩ : syracuseStep 5213717 = 244393) (by norm_num)
theorem B2059825 : Blo 1829616 2059825 := bbase (se 2 (by rfl) ⟨772434, by rfl⟩ : syracuseStep 2059825 = 1544869) (by norm_num)
theorem B3911237 : Blo 1829616 3911237 := bbase (se 4 (by rfl) ⟨366678, by rfl⟩ : syracuseStep 3911237 = 733357) (by norm_num)
theorem B2059861 : Blo 1829616 2059861 := bbase (se 8 (by rfl) ⟨12069, by rfl⟩ : syracuseStep 2059861 = 24139) (by norm_num)
theorem B4173421 : Blo 1829616 4173421 := bbase (se 3 (by rfl) ⟨782516, by rfl⟩ : syracuseStep 4173421 = 1565033) (by norm_num)
theorem B2059897 : Blo 1829616 2059897 := bbase (se 2 (by rfl) ⟨772461, by rfl⟩ : syracuseStep 2059897 = 1544923) (by norm_num)
theorem B2059933 : Blo 1829616 2059933 := bbase (se 3 (by rfl) ⟨386237, by rfl⟩ : syracuseStep 2059933 = 772475) (by norm_num)
theorem B12521141 : Blo 1829616 12521141 := bbase (se 5 (by rfl) ⟨586928, by rfl⟩ : syracuseStep 12521141 = 1173857) (by norm_num)
theorem B2059969 : Blo 1829616 2059969 := bbase (se 2 (by rfl) ⟨772488, by rfl⟩ : syracuseStep 2059969 = 1544977) (by norm_num)
theorem B2060005 : Blo 1829616 2060005 := bbase (se 4 (by rfl) ⟨193125, by rfl⟩ : syracuseStep 2060005 = 386251) (by norm_num)
theorem B2060041 : Blo 1829616 2060041 := bbase (se 2 (by rfl) ⟨772515, by rfl⟩ : syracuseStep 2060041 = 1545031) (by norm_num)
theorem B4632349 : Blo 1829616 4632349 := bbase (se 3 (by rfl) ⟨868565, by rfl⟩ : syracuseStep 4632349 = 1737131) (by norm_num)
theorem B2060077 : Blo 1829616 2060077 := bbase (se 3 (by rfl) ⟨386264, by rfl⟩ : syracuseStep 2060077 = 772529) (by norm_num)
theorem B6180677 : Blo 1829616 6180677 := bbase (se 4 (by rfl) ⟨579438, by rfl⟩ : syracuseStep 6180677 = 1158877) (by norm_num)
theorem B2060113 : Blo 1829616 2060113 := bbase (se 2 (by rfl) ⟨772542, by rfl⟩ : syracuseStep 2060113 = 1545085) (by norm_num)
theorem B2060149 : Blo 1829616 2060149 := bbase (se 5 (by rfl) ⟨96569, by rfl⟩ : syracuseStep 2060149 = 193139) (by norm_num)
theorem B4632461 : Blo 1829616 4632461 := bbase (se 3 (by rfl) ⟨868586, by rfl⟩ : syracuseStep 4632461 = 1737173) (by norm_num)
theorem B9891733 : Blo 1829616 9891733 := bbase (se 6 (by rfl) ⟨231837, by rfl⟩ : syracuseStep 9891733 = 463675) (by norm_num)
theorem B15642517 : Blo 1829616 15642517 := bbase (se 6 (by rfl) ⟨366621, by rfl⟩ : syracuseStep 15642517 = 733243) (by norm_num)
theorem B2060185 : Blo 1829616 2060185 := bbase (se 2 (by rfl) ⟨772569, by rfl⟩ : syracuseStep 2060185 = 1545139) (by norm_num)
theorem B2060221 : Blo 1829616 2060221 := bbase (se 3 (by rfl) ⟨386291, by rfl⟩ : syracuseStep 2060221 = 772583) (by norm_num)
theorem B2060257 : Blo 1829616 2060257 := bbase (se 2 (by rfl) ⟨772596, by rfl⟩ : syracuseStep 2060257 = 1545193) (by norm_num)
theorem B2060293 : Blo 1829616 2060293 := bbase (se 4 (by rfl) ⟨193152, by rfl⟩ : syracuseStep 2060293 = 386305) (by norm_num)
theorem B8794133 : Blo 1829616 8794133 := bbase (se 6 (by rfl) ⟨206112, by rfl⟩ : syracuseStep 8794133 = 412225) (by norm_num)
theorem B2060329 : Blo 1829616 2060329 := bbase (se 2 (by rfl) ⟨772623, by rfl⟩ : syracuseStep 2060329 = 1545247) (by norm_num)
theorem B4632653 : Blo 1829616 4632653 := bbase (se 3 (by rfl) ⟨868622, by rfl⟩ : syracuseStep 4632653 = 1737245) (by norm_num)
theorem B2060365 : Blo 1829616 2060365 := bbase (se 3 (by rfl) ⟨386318, by rfl⟩ : syracuseStep 2060365 = 772637) (by norm_num)
theorem B2060401 : Blo 1829616 2060401 := bbase (se 2 (by rfl) ⟨772650, by rfl⟩ : syracuseStep 2060401 = 1545301) (by norm_num)
theorem B2060437 : Blo 1829616 2060437 := bbase (se 6 (by rfl) ⟨48291, by rfl⟩ : syracuseStep 2060437 = 96583) (by norm_num)
theorem B4116653 : Blo 1829616 4116653 := bbase (se 3 (by rfl) ⟨771872, by rfl⟩ : syracuseStep 4116653 = 1543745) (by norm_num)
theorem B1855661 : Blo 1829616 1855661 := bbase (se 3 (by rfl) ⟨347936, by rfl⟩ : syracuseStep 1855661 = 695873) (by norm_num)
theorem B2060473 : Blo 1829616 2060473 := bbase (se 2 (by rfl) ⟨772677, by rfl⟩ : syracuseStep 2060473 = 1545355) (by norm_num)
theorem B2060509 : Blo 1829616 2060509 := bbase (se 3 (by rfl) ⟨386345, by rfl⟩ : syracuseStep 2060509 = 772691) (by norm_num)
theorem B9269477 : Blo 1829616 9269477 := bbase (se 4 (by rfl) ⟨869013, by rfl⟩ : syracuseStep 9269477 = 1738027) (by norm_num)
theorem B4116725 : Blo 1829616 4116725 := bbase (se 5 (by rfl) ⟨192971, by rfl⟩ : syracuseStep 4116725 = 385943) (by norm_num)
theorem B6598901 : Blo 1829616 6598901 := bbase (se 5 (by rfl) ⟨309323, by rfl⟩ : syracuseStep 6598901 = 618647) (by norm_num)
theorem B6181109 : Blo 1829616 6181109 := bbase (se 5 (by rfl) ⟨289739, by rfl⟩ : syracuseStep 6181109 = 579479) (by norm_num)
theorem B2060545 : Blo 1829616 2060545 := bbase (se 2 (by rfl) ⟨772704, by rfl⟩ : syracuseStep 2060545 = 1545409) (by norm_num)
theorem B5214469 : Blo 1829616 5214469 := bbase (se 4 (by rfl) ⟨488856, by rfl⟩ : syracuseStep 5214469 = 977713) (by norm_num)
theorem B1954081 : Blo 1829616 1954081 := bbase (se 2 (by rfl) ⟨732780, by rfl⟩ : syracuseStep 1954081 = 1465561) (by norm_num)
theorem B2199845 : Blo 1829616 2199845 := bbase (se 4 (by rfl) ⟨206235, by rfl⟩ : syracuseStep 2199845 = 412471) (by norm_num)
theorem B4116797 : Blo 1829616 4116797 := bbase (se 3 (by rfl) ⟨771899, by rfl⟩ : syracuseStep 4116797 = 1543799) (by norm_num)
theorem B1954153 : Blo 1829616 1954153 := bbase (se 2 (by rfl) ⟨732807, by rfl⟩ : syracuseStep 1954153 = 1465615) (by norm_num)
theorem B2199917 : Blo 1829616 2199917 := bbase (se 3 (by rfl) ⟨412484, by rfl⟩ : syracuseStep 2199917 = 824969) (by norm_num)
theorem B4116869 : Blo 1829616 4116869 := bbase (se 4 (by rfl) ⟨385956, by rfl⟩ : syracuseStep 4116869 = 771913) (by norm_num)
theorem B3297685 : Blo 1829616 3297685 := bbase (se 6 (by rfl) ⟨77289, by rfl⟩ : syracuseStep 3297685 = 154579) (by norm_num)
theorem B4632997 : Blo 1829616 4632997 := bbase (se 4 (by rfl) ⟨434343, by rfl⟩ : syracuseStep 4632997 = 868687) (by norm_num)
theorem B1855921 : Blo 1829616 1855921 := bbase (se 2 (by rfl) ⟨695970, by rfl⟩ : syracuseStep 1855921 = 1391941) (by norm_num)
theorem B6951365 : Blo 1829616 6951365 := bbase (se 4 (by rfl) ⟨651690, by rfl⟩ : syracuseStep 6951365 = 1303381) (by norm_num)
theorem B4116941 : Blo 1829616 4116941 := bbase (se 3 (by rfl) ⟨771926, by rfl⟩ : syracuseStep 4116941 = 1543853) (by norm_num)
theorem B4117013 : Blo 1829616 4117013 := bbase (se 6 (by rfl) ⟨96492, by rfl⟩ : syracuseStep 4117013 = 192985) (by norm_num)
theorem B4633109 : Blo 1829616 4633109 := bbase (se 6 (by rfl) ⟨108588, by rfl⟩ : syracuseStep 4633109 = 217177) (by norm_num)
theorem B4117085 : Blo 1829616 4117085 := bbase (se 3 (by rfl) ⟨771953, by rfl⟩ : syracuseStep 4117085 = 1543907) (by norm_num)
theorem B9892469 : Blo 1829616 9892469 := bbase (se 5 (by rfl) ⟨463709, by rfl⟩ : syracuseStep 9892469 = 927419) (by norm_num)
theorem B2200225 : Blo 1829616 2200225 := bbase (se 2 (by rfl) ⟨825084, by rfl⟩ : syracuseStep 2200225 = 1650169) (by norm_num)
theorem B4117157 : Blo 1829616 4117157 := bbase (se 4 (by rfl) ⟨385983, by rfl⟩ : syracuseStep 4117157 = 771967) (by norm_num)
theorem B6599333 : Blo 1829616 6599333 := bbase (se 4 (by rfl) ⟨618687, by rfl⟩ : syracuseStep 6599333 = 1237375) (by norm_num)
theorem B6181541 : Blo 1829616 6181541 := bbase (se 4 (by rfl) ⟨579519, by rfl⟩ : syracuseStep 6181541 = 1159039) (by norm_num)
theorem B1856201 : Blo 1829616 1856201 := bbase (se 2 (by rfl) ⟨696075, by rfl⟩ : syracuseStep 1856201 = 1392151) (by norm_num)
theorem B4633301 : Blo 1829616 4633301 := bbase (se 7 (by rfl) ⟨54296, by rfl⟩ : syracuseStep 4633301 = 108593) (by norm_num)
theorem B1954525 : Blo 1829616 1954525 := bbase (se 3 (by rfl) ⟨366473, by rfl⟩ : syracuseStep 1954525 = 732947) (by norm_num)
theorem B6951653 : Blo 1829616 6951653 := bbase (se 4 (by rfl) ⟨651717, by rfl⟩ : syracuseStep 6951653 = 1303435) (by norm_num)
theorem B4117229 : Blo 1829616 4117229 := bbase (se 3 (by rfl) ⟨771980, by rfl⟩ : syracuseStep 4117229 = 1543961) (by norm_num)
theorem B4174589 : Blo 1829616 4174589 := bbase (se 3 (by rfl) ⟨782735, by rfl⟩ : syracuseStep 4174589 = 1565471) (by norm_num)
theorem B4117301 : Blo 1829616 4117301 := bbase (se 5 (by rfl) ⟨192998, by rfl⟩ : syracuseStep 4117301 = 385997) (by norm_num)
theorem B2200393 : Blo 1829616 2200393 := bbase (se 2 (by rfl) ⟨825147, by rfl⟩ : syracuseStep 2200393 = 1650295) (by norm_num)
theorem B4117373 : Blo 1829616 4117373 := bbase (se 3 (by rfl) ⟨772007, by rfl⟩ : syracuseStep 4117373 = 1544015) (by norm_num)
theorem B7820165 : Blo 1829616 7820165 := bbase (se 4 (by rfl) ⟨733140, by rfl⟩ : syracuseStep 7820165 = 1466281) (by norm_num)
theorem B4117445 : Blo 1829616 4117445 := bbase (se 4 (by rfl) ⟨386010, by rfl⟩ : syracuseStep 4117445 = 772021) (by norm_num)
theorem B4117517 : Blo 1829616 4117517 := bbase (se 3 (by rfl) ⟨772034, by rfl⟩ : syracuseStep 4117517 = 1544069) (by norm_num)
theorem B1856525 : Blo 1829616 1856525 := bbase (se 3 (by rfl) ⟨348098, by rfl⟩ : syracuseStep 1856525 = 696197) (by norm_num)
theorem B3298325 : Blo 1829616 3298325 := bbase (se 6 (by rfl) ⟨77304, by rfl⟩ : syracuseStep 3298325 = 154609) (by norm_num)
theorem B4633645 : Blo 1829616 4633645 := bbase (se 3 (by rfl) ⟨868808, by rfl⟩ : syracuseStep 4633645 = 1737617) (by norm_num)
theorem B4117589 : Blo 1829616 4117589 := bbase (se 8 (by rfl) ⟨24126, by rfl⟩ : syracuseStep 4117589 = 48253) (by norm_num)
theorem B1954901 : Blo 1829616 1954901 := bbase (se 8 (by rfl) ⟨11454, by rfl⟩ : syracuseStep 1954901 = 22909) (by norm_num)
theorem B5944421 : Blo 1829616 5944421 := bbase (se 4 (by rfl) ⟨557289, by rfl⟩ : syracuseStep 5944421 = 1114579) (by norm_num)
theorem B2782325 : Blo 1829616 2782325 := bbase (se 5 (by rfl) ⟨130421, by rfl⟩ : syracuseStep 2782325 = 260843) (by norm_num)
theorem B2970749 : Blo 1829616 2970749 := bbase (se 3 (by rfl) ⟨557015, by rfl⟩ : syracuseStep 2970749 = 1114031) (by norm_num)
theorem B4117661 : Blo 1829616 4117661 := bbase (se 3 (by rfl) ⟨772061, by rfl⟩ : syracuseStep 4117661 = 1544123) (by norm_num)
theorem B4633757 : Blo 1829616 4633757 := bbase (se 3 (by rfl) ⟨868829, by rfl⟩ : syracuseStep 4633757 = 1737659) (by norm_num)
theorem B1954973 : Blo 1829616 1954973 := bbase (se 3 (by rfl) ⟨366557, by rfl⟩ : syracuseStep 1954973 = 733115) (by norm_num)
theorem B5862613 : Blo 1829616 5862613 := bbase (se 7 (by rfl) ⟨68702, by rfl⟩ : syracuseStep 5862613 = 137405) (by norm_num)
theorem B4117733 : Blo 1829616 4117733 := bbase (se 4 (by rfl) ⟨386037, by rfl⟩ : syracuseStep 4117733 = 772075) (by norm_num)
theorem B4117805 : Blo 1829616 4117805 := bbase (se 3 (by rfl) ⟨772088, by rfl⟩ : syracuseStep 4117805 = 1544177) (by norm_num)
theorem B17593685 : Blo 1829616 17593685 := bbase (se 13 (by rfl) ⟨3221, by rfl⟩ : syracuseStep 17593685 = 6443) (by norm_num)
theorem B1955161 : Blo 1829616 1955161 := bbase (se 2 (by rfl) ⟨733185, by rfl⟩ : syracuseStep 1955161 = 1466371) (by norm_num)
theorem B4633949 : Blo 1829616 4633949 := bbase (se 3 (by rfl) ⟨868865, by rfl⟩ : syracuseStep 4633949 = 1737731) (by norm_num)
theorem B4117877 : Blo 1829616 4117877 := bbase (se 5 (by rfl) ⟨193025, by rfl⟩ : syracuseStep 4117877 = 386051) (by norm_num)
theorem B4117949 : Blo 1829616 4117949 := bbase (se 3 (by rfl) ⟨772115, by rfl⟩ : syracuseStep 4117949 = 1544231) (by norm_num)
theorem B2315729 : Blo 1829616 2315729 := bbase (se 2 (by rfl) ⟨868398, by rfl⟩ : syracuseStep 2315729 = 1736797) (by norm_num)
theorem B5862869 : Blo 1829616 5862869 := bbase (se 7 (by rfl) ⟨68705, by rfl⟩ : syracuseStep 5862869 = 137411) (by norm_num)
theorem B9270773 : Blo 1829616 9270773 := bbase (se 5 (by rfl) ⟨434567, by rfl⟩ : syracuseStep 9270773 = 869135) (by norm_num)
theorem B4118021 : Blo 1829616 4118021 := bbase (se 4 (by rfl) ⟨386064, by rfl⟩ : syracuseStep 4118021 = 772129) (by norm_num)
theorem B2315785 : Blo 1829616 2315785 := bbase (se 2 (by rfl) ⟨868419, by rfl⟩ : syracuseStep 2315785 = 1736839) (by norm_num)
theorem B1955345 : Blo 1829616 1955345 := bbase (se 2 (by rfl) ⟨733254, by rfl⟩ : syracuseStep 1955345 = 1466509) (by norm_num)
theorem B4118093 : Blo 1829616 4118093 := bbase (se 3 (by rfl) ⟨772142, by rfl⟩ : syracuseStep 4118093 = 1544285) (by norm_num)
theorem B2315881 : Blo 1829616 2315881 := bbase (se 2 (by rfl) ⟨868455, by rfl⟩ : syracuseStep 2315881 = 1736911) (by norm_num)
theorem B8795765 : Blo 1829616 8795765 := bbase (se 5 (by rfl) ⟨412301, by rfl⟩ : syracuseStep 8795765 = 824603) (by norm_num)
theorem B4118165 : Blo 1829616 4118165 := bbase (se 6 (by rfl) ⟨96519, by rfl⟩ : syracuseStep 4118165 = 193039) (by norm_num)
theorem B6600341 : Blo 1829616 6600341 := bbase (se 6 (by rfl) ⟨154695, by rfl⟩ : syracuseStep 6600341 = 309391) (by norm_num)
theorem B4634293 : Blo 1829616 4634293 := bbase (se 5 (by rfl) ⟨217232, by rfl⟩ : syracuseStep 4634293 = 434465) (by norm_num)
theorem B4118237 : Blo 1829616 4118237 := bbase (se 3 (by rfl) ⟨772169, by rfl⟩ : syracuseStep 4118237 = 1544339) (by norm_num)
theorem B3299069 : Blo 1829616 3299069 := bbase (se 3 (by rfl) ⟨618575, by rfl⟩ : syracuseStep 3299069 = 1237151) (by norm_num)
theorem B2316053 : Blo 1829616 2316053 := bbase (se 6 (by rfl) ⟨54282, by rfl⟩ : syracuseStep 2316053 = 108565) (by norm_num)
theorem B4118309 : Blo 1829616 4118309 := bbase (se 4 (by rfl) ⟨386091, by rfl⟩ : syracuseStep 4118309 = 772183) (by norm_num)
theorem B4634405 : Blo 1829616 4634405 := bbase (se 4 (by rfl) ⟨434475, by rfl⟩ : syracuseStep 4634405 = 868951) (by norm_num)
theorem B2316109 : Blo 1829616 2316109 := bbase (se 3 (by rfl) ⟨434270, by rfl⟩ : syracuseStep 2316109 = 868541) (by norm_num)
theorem B15644501 : Blo 1829616 15644501 := bbase (se 9 (by rfl) ⟨45833, by rfl⟩ : syracuseStep 15644501 = 91667) (by norm_num)
theorem B7821157 : Blo 1829616 7821157 := bbase (se 4 (by rfl) ⟨733233, by rfl⟩ : syracuseStep 7821157 = 1466467) (by norm_num)
theorem B4118381 : Blo 1829616 4118381 := bbase (se 3 (by rfl) ⟨772196, by rfl⟩ : syracuseStep 4118381 = 1544393) (by norm_num)
theorem B6952837 : Blo 1829616 6952837 := bbase (se 4 (by rfl) ⟨651828, by rfl⟩ : syracuseStep 6952837 = 1303657) (by norm_num)
theorem B9262997 : Blo 1829616 9262997 := bbase (se 6 (by rfl) ⟨217101, by rfl⟩ : syracuseStep 9262997 = 434203) (by norm_num)
theorem B13907861 : Blo 1829616 13907861 := bbase (se 6 (by rfl) ⟨325965, by rfl⟩ : syracuseStep 13907861 = 651931) (by norm_num)
theorem B2348957 : Blo 1829616 2348957 := bbase (se 3 (by rfl) ⟨440429, by rfl⟩ : syracuseStep 2348957 = 880859) (by norm_num)
theorem B2316205 : Blo 1829616 2316205 := bbase (se 3 (by rfl) ⟨434288, by rfl⟩ : syracuseStep 2316205 = 868577) (by norm_num)
theorem B4118453 : Blo 1829616 4118453 := bbase (se 5 (by rfl) ⟨193052, by rfl⟩ : syracuseStep 4118453 = 386105) (by norm_num)
theorem B11139029 : Blo 1829616 11139029 := bbase (se 7 (by rfl) ⟨130535, by rfl⟩ : syracuseStep 11139029 = 261071) (by norm_num)
theorem B4634597 : Blo 1829616 4634597 := bbase (se 4 (by rfl) ⟨434493, by rfl⟩ : syracuseStep 4634597 = 868987) (by norm_num)
theorem B4118525 : Blo 1829616 4118525 := bbase (se 3 (by rfl) ⟨772223, by rfl⟩ : syracuseStep 4118525 = 1544447) (by norm_num)
theorem B4118597 : Blo 1829616 4118597 := bbase (se 4 (by rfl) ⟨386118, by rfl⟩ : syracuseStep 4118597 = 772237) (by norm_num)
theorem B2783317 : Blo 1829616 2783317 := bbase (se 8 (by rfl) ⟨16308, by rfl⟩ : syracuseStep 2783317 = 32617) (by norm_num)
theorem B2316377 : Blo 1829616 2316377 := bbase (se 2 (by rfl) ⟨868641, by rfl⟩ : syracuseStep 2316377 = 1737283) (by norm_num)
theorem B4118669 : Blo 1829616 4118669 := bbase (se 3 (by rfl) ⟨772250, by rfl⟩ : syracuseStep 4118669 = 1544501) (by norm_num)
theorem B2316433 : Blo 1829616 2316433 := bbase (se 2 (by rfl) ⟨868662, by rfl⟩ : syracuseStep 2316433 = 1737325) (by norm_num)
theorem B2783413 : Blo 1829616 2783413 := bbase (se 5 (by rfl) ⟨130472, by rfl⟩ : syracuseStep 2783413 = 260945) (by norm_num)
theorem B6953141 : Blo 1829616 6953141 := bbase (se 5 (by rfl) ⟨325928, by rfl⟩ : syracuseStep 6953141 = 651857) (by norm_num)
theorem B4118741 : Blo 1829616 4118741 := bbase (se 7 (by rfl) ⟨48266, by rfl⟩ : syracuseStep 4118741 = 96533) (by norm_num)
theorem B2316529 : Blo 1829616 2316529 := bbase (se 2 (by rfl) ⟨868698, by rfl⟩ : syracuseStep 2316529 = 1737397) (by norm_num)
theorem B3709189 : Blo 1829616 3709189 := bbase (se 4 (by rfl) ⟨347736, by rfl⟩ : syracuseStep 3709189 = 695473) (by norm_num)
theorem B4118813 : Blo 1829616 4118813 := bbase (se 3 (by rfl) ⟨772277, by rfl⟩ : syracuseStep 4118813 = 1544555) (by norm_num)
theorem B13900085 : Blo 1829616 13900085 := bbase (se 5 (by rfl) ⟨651566, by rfl⟩ : syracuseStep 13900085 = 1303133) (by norm_num)
theorem B4634941 : Blo 1829616 4634941 := bbase (se 3 (by rfl) ⟨869051, by rfl⟩ : syracuseStep 4634941 = 1738103) (by norm_num)
theorem B6175061 : Blo 1829616 6175061 := bbase (se 10 (by rfl) ⟨9045, by rfl⟩ : syracuseStep 6175061 = 18091) (by norm_num)
theorem B4118885 : Blo 1829616 4118885 := bbase (se 4 (by rfl) ⟨386145, by rfl⟩ : syracuseStep 4118885 = 772291) (by norm_num)
theorem B2783621 : Blo 1829616 2783621 := bbase (se 4 (by rfl) ⟨260964, by rfl⟩ : syracuseStep 2783621 = 521929) (by norm_num)
theorem B2316701 : Blo 1829616 2316701 := bbase (se 3 (by rfl) ⟨434381, by rfl⟩ : syracuseStep 2316701 = 868763) (by norm_num)
theorem B4118957 : Blo 1829616 4118957 := bbase (se 3 (by rfl) ⟨772304, by rfl⟩ : syracuseStep 4118957 = 1544609) (by norm_num)
theorem B4635053 : Blo 1829616 4635053 := bbase (se 3 (by rfl) ⟨869072, by rfl⟩ : syracuseStep 4635053 = 1738145) (by norm_num)
theorem B2783693 : Blo 1829616 2783693 := bbase (se 3 (by rfl) ⟨521942, by rfl⟩ : syracuseStep 2783693 = 1043885) (by norm_num)
theorem B2316757 : Blo 1829616 2316757 := bbase (se 7 (by rfl) ⟨27149, by rfl⟩ : syracuseStep 2316757 = 54299) (by norm_num)
theorem B7043573 : Blo 1829616 7043573 := bbase (se 5 (by rfl) ⟨330167, by rfl⟩ : syracuseStep 7043573 = 660335) (by norm_num)
theorem B4119029 : Blo 1829616 4119029 := bbase (se 5 (by rfl) ⟨193079, by rfl⟩ : syracuseStep 4119029 = 386159) (by norm_num)
theorem B2316853 : Blo 1829616 2316853 := bbase (se 5 (by rfl) ⟨108602, by rfl⟩ : syracuseStep 2316853 = 217205) (by norm_num)
theorem B4119101 : Blo 1829616 4119101 := bbase (se 3 (by rfl) ⟨772331, by rfl⟩ : syracuseStep 4119101 = 1544663) (by norm_num)
theorem B4635245 : Blo 1829616 4635245 := bbase (se 3 (by rfl) ⟨869108, by rfl⟩ : syracuseStep 4635245 = 1738217) (by norm_num)
theorem B2349685 : Blo 1829616 2349685 := bbase (se 5 (by rfl) ⟨110141, by rfl⟩ : syracuseStep 2349685 = 220283) (by norm_num)
theorem B4119173 : Blo 1829616 4119173 := bbase (se 4 (by rfl) ⟨386172, by rfl⟩ : syracuseStep 4119173 = 772345) (by norm_num)
theorem B2087569 : Blo 1829616 2087569 := bbase (se 2 (by rfl) ⟨782838, by rfl⟩ : syracuseStep 2087569 = 1565677) (by norm_num)
theorem B2349721 : Blo 1829616 2349721 := bbase (se 2 (by rfl) ⟨881145, by rfl⟩ : syracuseStep 2349721 = 1762291) (by norm_num)
theorem B4119245 : Blo 1829616 4119245 := bbase (se 3 (by rfl) ⟨772358, by rfl⟩ : syracuseStep 4119245 = 1544717) (by norm_num)
theorem B2317025 : Blo 1829616 2317025 := bbase (se 2 (by rfl) ⟨868884, by rfl⟩ : syracuseStep 2317025 = 1737769) (by norm_num)
theorem B6175493 : Blo 1829616 6175493 := bbase (se 4 (by rfl) ⟨578952, by rfl⟩ : syracuseStep 6175493 = 1157905) (by norm_num)
theorem B2931461 : Blo 1829616 2931461 := bbase (se 4 (by rfl) ⟨274824, by rfl⟩ : syracuseStep 2931461 = 549649) (by norm_num)
theorem B9272069 : Blo 1829616 9272069 := bbase (se 4 (by rfl) ⟨869256, by rfl⟩ : syracuseStep 9272069 = 1738513) (by norm_num)
theorem B4119317 : Blo 1829616 4119317 := bbase (se 6 (by rfl) ⟨96546, by rfl⟩ : syracuseStep 4119317 = 193093) (by norm_num)
theorem B2317081 : Blo 1829616 2317081 := bbase (se 2 (by rfl) ⟨868905, by rfl⟩ : syracuseStep 2317081 = 1737811) (by norm_num)
theorem B4119389 : Blo 1829616 4119389 := bbase (se 3 (by rfl) ⟨772385, by rfl⟩ : syracuseStep 4119389 = 1544771) (by norm_num)
theorem B2317177 : Blo 1829616 2317177 := bbase (se 2 (by rfl) ⟨868941, by rfl⟩ : syracuseStep 2317177 = 1737883) (by norm_num)
theorem B4397989 : Blo 1829616 4397989 := bbase (se 4 (by rfl) ⟨412311, by rfl⟩ : syracuseStep 4397989 = 824623) (by norm_num)
theorem B4119461 : Blo 1829616 4119461 := bbase (se 4 (by rfl) ⟨386199, by rfl⟩ : syracuseStep 4119461 = 772399) (by norm_num)
theorem B2931653 : Blo 1829616 2931653 := bbase (se 4 (by rfl) ⟨274842, by rfl⟩ : syracuseStep 2931653 = 549685) (by norm_num)
theorem B4635589 : Blo 1829616 4635589 := bbase (se 4 (by rfl) ⟨434586, by rfl⟩ : syracuseStep 4635589 = 869173) (by norm_num)
theorem B4119533 : Blo 1829616 4119533 := bbase (se 3 (by rfl) ⟨772412, by rfl⟩ : syracuseStep 4119533 = 1544825) (by norm_num)
theorem B3300373 : Blo 1829616 3300373 := bbase (se 6 (by rfl) ⟨77352, by rfl⟩ : syracuseStep 3300373 = 154705) (by norm_num)
theorem B2317349 : Blo 1829616 2317349 := bbase (se 4 (by rfl) ⟨217251, by rfl⟩ : syracuseStep 2317349 = 434503) (by norm_num)
theorem B4119605 : Blo 1829616 4119605 := bbase (se 5 (by rfl) ⟨193106, by rfl⟩ : syracuseStep 4119605 = 386213) (by norm_num)
theorem B4635701 : Blo 1829616 4635701 := bbase (se 5 (by rfl) ⟨217298, by rfl⟩ : syracuseStep 4635701 = 434597) (by norm_num)
theorem B2473021 : Blo 1829616 2473021 := bbase (se 3 (by rfl) ⟨463691, by rfl⟩ : syracuseStep 2473021 = 927383) (by norm_num)
theorem B2317405 : Blo 1829616 2317405 := bbase (se 3 (by rfl) ⟨434513, by rfl⟩ : syracuseStep 2317405 = 869027) (by norm_num)
theorem B4234357 : Blo 1829616 4234357 := bbase (se 5 (by rfl) ⟨198485, by rfl⟩ : syracuseStep 4234357 = 396971) (by norm_num)
theorem B4119677 : Blo 1829616 4119677 := bbase (se 3 (by rfl) ⟨772439, by rfl⟩ : syracuseStep 4119677 = 1544879) (by norm_num)
theorem B3013757 : Blo 1829616 3013757 := bbase (se 3 (by rfl) ⟨565079, by rfl⟩ : syracuseStep 3013757 = 1130159) (by norm_num)
theorem B3087517 : Blo 1829616 3087517 := bbase (se 3 (by rfl) ⟨578909, by rfl⟩ : syracuseStep 3087517 = 1157819) (by norm_num)
theorem B9264293 : Blo 1829616 9264293 := bbase (se 4 (by rfl) ⟨868527, by rfl⟩ : syracuseStep 9264293 = 1737055) (by norm_num)
theorem B6175925 : Blo 1829616 6175925 := bbase (se 5 (by rfl) ⟨289496, by rfl⟩ : syracuseStep 6175925 = 578993) (by norm_num)
theorem B2317501 : Blo 1829616 2317501 := bbase (se 3 (by rfl) ⟨434531, by rfl⟩ : syracuseStep 2317501 = 869063) (by norm_num)
theorem B4119749 : Blo 1829616 4119749 := bbase (se 4 (by rfl) ⟨386226, by rfl⟩ : syracuseStep 4119749 = 772453) (by norm_num)
theorem B3087605 : Blo 1829616 3087605 := bbase (se 5 (by rfl) ⟨144731, by rfl⟩ : syracuseStep 3087605 = 289463) (by norm_num)
theorem B4635893 : Blo 1829616 4635893 := bbase (se 5 (by rfl) ⟨217307, by rfl⟩ : syracuseStep 4635893 = 434615) (by norm_num)
theorem B4119821 : Blo 1829616 4119821 := bbase (se 3 (by rfl) ⟨772466, by rfl⟩ : syracuseStep 4119821 = 1544933) (by norm_num)
theorem B4119893 : Blo 1829616 4119893 := bbase (se 11 (by rfl) ⟨3017, by rfl⟩ : syracuseStep 4119893 = 6035) (by norm_num)
theorem B2317673 : Blo 1829616 2317673 := bbase (se 2 (by rfl) ⟨869127, by rfl⟩ : syracuseStep 2317673 = 1738255) (by norm_num)
theorem B3087733 : Blo 1829616 3087733 := bbase (se 5 (by rfl) ⟨144737, by rfl⟩ : syracuseStep 3087733 = 289475) (by norm_num)
theorem B15859061 : Blo 1829616 15859061 := bbase (se 5 (by rfl) ⟨743393, by rfl⟩ : syracuseStep 15859061 = 1486787) (by norm_num)
theorem B4119965 : Blo 1829616 4119965 := bbase (se 3 (by rfl) ⟨772493, by rfl⟩ : syracuseStep 4119965 = 1544987) (by norm_num)
theorem B2317729 : Blo 1829616 2317729 := bbase (se 2 (by rfl) ⟨869148, by rfl⟩ : syracuseStep 2317729 = 1738297) (by norm_num)
theorem B3087821 : Blo 1829616 3087821 := bbase (se 3 (by rfl) ⟨578966, by rfl⟩ : syracuseStep 3087821 = 1157933) (by norm_num)
theorem B4120037 : Blo 1829616 4120037 := bbase (se 4 (by rfl) ⟨386253, by rfl⟩ : syracuseStep 4120037 = 772507) (by norm_num)
theorem B2473453 : Blo 1829616 2473453 := bbase (se 3 (by rfl) ⟨463772, by rfl⟩ : syracuseStep 2473453 = 927545) (by norm_num)
theorem B2317825 : Blo 1829616 2317825 := bbase (se 2 (by rfl) ⟨869184, by rfl⟩ : syracuseStep 2317825 = 1738369) (by norm_num)
theorem B19037717 : Blo 1829616 19037717 := bbase (se 6 (by rfl) ⟨446196, by rfl⟩ : syracuseStep 19037717 = 892393) (by norm_num)
theorem B4120109 : Blo 1829616 4120109 := bbase (se 3 (by rfl) ⟨772520, by rfl⟩ : syracuseStep 4120109 = 1545041) (by norm_num)
theorem B3087949 : Blo 1829616 3087949 := bbase (se 3 (by rfl) ⟨578990, by rfl⟩ : syracuseStep 3087949 = 1157981) (by norm_num)
theorem B4636237 : Blo 1829616 4636237 := bbase (se 3 (by rfl) ⟨869294, by rfl⟩ : syracuseStep 4636237 = 1738589) (by norm_num)
theorem B6176357 : Blo 1829616 6176357 := bbase (se 4 (by rfl) ⟨579033, by rfl⟩ : syracuseStep 6176357 = 1158067) (by norm_num)
theorem B4120181 : Blo 1829616 4120181 := bbase (se 5 (by rfl) ⟨193133, by rfl⟩ : syracuseStep 4120181 = 386267) (by norm_num)
theorem B3088037 : Blo 1829616 3088037 := bbase (se 4 (by rfl) ⟨289503, by rfl⟩ : syracuseStep 3088037 = 579007) (by norm_num)
theorem B2317997 : Blo 1829616 2317997 := bbase (se 3 (by rfl) ⟨434624, by rfl⟩ : syracuseStep 2317997 = 869249) (by norm_num)
theorem B4120253 : Blo 1829616 4120253 := bbase (se 3 (by rfl) ⟨772547, by rfl⟩ : syracuseStep 4120253 = 1545095) (by norm_num)
theorem B2318053 : Blo 1829616 2318053 := bbase (se 4 (by rfl) ⟨217317, by rfl⟩ : syracuseStep 2318053 = 434635) (by norm_num)
theorem B4120325 : Blo 1829616 4120325 := bbase (se 4 (by rfl) ⟨386280, by rfl⟩ : syracuseStep 4120325 = 772561) (by norm_num)
theorem B3088165 : Blo 1829616 3088165 := bbase (se 4 (by rfl) ⟨289515, by rfl⟩ : syracuseStep 3088165 = 579031) (by norm_num)
theorem B4947749 : Blo 1829616 4947749 := bbase (se 4 (by rfl) ⟨463851, by rfl⟩ : syracuseStep 4947749 = 927703) (by norm_num)
theorem B11280181 : Blo 1829616 11280181 := bbase (se 5 (by rfl) ⟨528758, by rfl⟩ : syracuseStep 11280181 = 1057517) (by norm_num)
theorem B4120397 : Blo 1829616 4120397 := bbase (se 3 (by rfl) ⟨772574, by rfl⟩ : syracuseStep 4120397 = 1545149) (by norm_num)
theorem B4398941 : Blo 1829616 4398941 := bbase (se 3 (by rfl) ⟨824801, by rfl⟩ : syracuseStep 4398941 = 1649603) (by norm_num)
theorem B3964781 : Blo 1829616 3964781 := bbase (se 3 (by rfl) ⟨743396, by rfl⟩ : syracuseStep 3964781 = 1486793) (by norm_num)
theorem B3088253 : Blo 1829616 3088253 := bbase (se 3 (by rfl) ⟨579047, by rfl⟩ : syracuseStep 3088253 = 1158095) (by norm_num)
theorem B4398997 : Blo 1829616 4398997 := bbase (se 6 (by rfl) ⟨103101, by rfl⟩ : syracuseStep 4398997 = 206203) (by norm_num)
theorem B4120469 : Blo 1829616 4120469 := bbase (se 6 (by rfl) ⟨96573, by rfl⟩ : syracuseStep 4120469 = 193147) (by norm_num)
theorem B4120541 : Blo 1829616 4120541 := bbase (se 3 (by rfl) ⟨772601, by rfl⟩ : syracuseStep 4120541 = 1545203) (by norm_num)
theorem B3088381 : Blo 1829616 3088381 := bbase (se 3 (by rfl) ⟨579071, by rfl⟩ : syracuseStep 3088381 = 1158143) (by norm_num)
theorem B3088435 : Blo 1829616 3088435 := bstep (se 1 (by rfl) ⟨2316326, by rfl⟩ : syracuseStep 3088435 = 4632653) B4632653
theorem B9265265 : Blo 1829616 9265265 := bstep (se 2 (by rfl) ⟨3474474, by rfl⟩ : syracuseStep 9265265 = 6948949) B6948949
theorem B3711089 : Blo 1829616 3711089 := bstep (se 2 (by rfl) ⟨1391658, by rfl⟩ : syracuseStep 3711089 = 2783317) B2783317
theorem B2744435 : Blo 1829616 2744435 := bstep (se 1 (by rfl) ⟨2058326, by rfl⟩ : syracuseStep 2744435 = 4116653) B4116653
theorem B2744465 : Blo 1829616 2744465 := bstep (se 2 (by rfl) ⟨1029174, by rfl⟩ : syracuseStep 2744465 = 2058349) B2058349
theorem B4120721 : Blo 1829616 4120721 := bstep (se 2 (by rfl) ⟨1545270, by rfl⟩ : syracuseStep 4120721 = 3090541) B3090541
theorem B2744483 : Blo 1829616 2744483 := bstep (se 1 (by rfl) ⟨2058362, by rfl⟩ : syracuseStep 2744483 = 4116725) B4116725
theorem B4399267 : Blo 1829616 4399267 := bstep (se 1 (by rfl) ⟨3299450, by rfl⟩ : syracuseStep 4399267 = 6598901) B6598901
theorem B4120739 : Blo 1829616 4120739 := bstep (se 1 (by rfl) ⟨3090554, by rfl⟩ : syracuseStep 4120739 = 6181109) B6181109
theorem B2744513 : Blo 1829616 2744513 := bstep (se 2 (by rfl) ⟨1029192, by rfl⟩ : syracuseStep 2744513 = 2058385) B2058385
theorem B3088577 : Blo 1829616 3088577 := bstep (se 2 (by rfl) ⟨1158216, by rfl⟩ : syracuseStep 3088577 = 2316433) B2316433
theorem B3473617 : Blo 1829616 3473617 := bstep (se 2 (by rfl) ⟨1302606, by rfl⟩ : syracuseStep 3473617 = 2605213) B2605213
theorem B2744531 : Blo 1829616 2744531 := bstep (se 1 (by rfl) ⟨2058398, by rfl⟩ : syracuseStep 2744531 = 4116797) B4116797
theorem B6177005 : Blo 1829616 6177005 := bstep (se 3 (by rfl) ⟨1158188, by rfl⟩ : syracuseStep 6177005 = 2316377) B2316377
theorem B2744561 : Blo 1829616 2744561 := bstep (se 2 (by rfl) ⟨1029210, by rfl⟩ : syracuseStep 2744561 = 2058421) B2058421
theorem B2744579 : Blo 1829616 2744579 := bstep (se 1 (by rfl) ⟨2058434, by rfl⟩ : syracuseStep 2744579 = 4116869) B4116869
theorem B2744609 : Blo 1829616 2744609 := bstep (se 2 (by rfl) ⟨1029228, by rfl⟩ : syracuseStep 2744609 = 2058457) B2058457
theorem B6177059 : Blo 1829616 6177059 := bstep (se 1 (by rfl) ⟨4632794, by rfl⟩ : syracuseStep 6177059 = 9265589) B9265589
theorem B2744627 : Blo 1829616 2744627 := bstep (se 1 (by rfl) ⟨2058470, by rfl⟩ : syracuseStep 2744627 = 4116941) B4116941
theorem B3088705 : Blo 1829616 3088705 := bstep (se 2 (by rfl) ⟨1158264, by rfl⟩ : syracuseStep 3088705 = 2316529) B2316529
theorem B2744657 : Blo 1829616 2744657 := bstep (se 2 (by rfl) ⟨1029246, by rfl⟩ : syracuseStep 2744657 = 2058493) B2058493
theorem B2933075 : Blo 1829616 2933075 := bstep (se 1 (by rfl) ⟨2199806, by rfl⟩ : syracuseStep 2933075 = 4399613) B4399613
theorem B2744675 : Blo 1829616 2744675 := bstep (se 1 (by rfl) ⟨2058506, by rfl⟩ : syracuseStep 2744675 = 4117013) B4117013
theorem B3088739 : Blo 1829616 3088739 := bstep (se 1 (by rfl) ⟨2316554, by rfl⟩ : syracuseStep 3088739 = 4633109) B4633109
theorem B2744705 : Blo 1829616 2744705 := bstep (se 2 (by rfl) ⟨1029264, by rfl⟩ : syracuseStep 2744705 = 2058529) B2058529
theorem B2605441 : Blo 1829616 2605441 := bstep (se 2 (by rfl) ⟨977040, by rfl⟩ : syracuseStep 2605441 = 1954081) B1954081
theorem B2744723 : Blo 1829616 2744723 := bstep (se 1 (by rfl) ⟨2058542, by rfl⟩ : syracuseStep 2744723 = 4117085) B4117085
theorem B6594979 : Blo 1829616 6594979 := bstep (se 1 (by rfl) ⟨4946234, by rfl⟩ : syracuseStep 6594979 = 9892469) B9892469
theorem B2744753 : Blo 1829616 2744753 := bstep (se 2 (by rfl) ⟨1029282, by rfl⟩ : syracuseStep 2744753 = 2058565) B2058565
theorem B4121009 : Blo 1829616 4121009 := bstep (se 2 (by rfl) ⟨1545378, by rfl⟩ : syracuseStep 4121009 = 3090757) B3090757
theorem B2744771 : Blo 1829616 2744771 := bstep (se 1 (by rfl) ⟨2058578, by rfl⟩ : syracuseStep 2744771 = 4117157) B4117157
theorem B4121027 : Blo 1829616 4121027 := bstep (se 1 (by rfl) ⟨3090770, by rfl⟩ : syracuseStep 4121027 = 6181541) B6181541
theorem B9396685 : Blo 1829616 9396685 := bstep (se 3 (by rfl) ⟨1761878, by rfl⟩ : syracuseStep 9396685 = 3523757) B3523757
theorem B2744801 : Blo 1829616 2744801 := bstep (se 2 (by rfl) ⟨1029300, by rfl⟩ : syracuseStep 2744801 = 2058601) B2058601
theorem B2605537 : Blo 1829616 2605537 := bstep (se 2 (by rfl) ⟨977076, by rfl⟩ : syracuseStep 2605537 = 1954153) B1954153
theorem B3088867 : Blo 1829616 3088867 := bstep (se 1 (by rfl) ⟨2316650, by rfl⟩ : syracuseStep 3088867 = 4633301) B4633301
theorem B2744819 : Blo 1829616 2744819 := bstep (se 1 (by rfl) ⟨2058614, by rfl⟩ : syracuseStep 2744819 = 4117229) B4117229
theorem B2744849 : Blo 1829616 2744849 := bstep (se 2 (by rfl) ⟨1029318, by rfl⟩ : syracuseStep 2744849 = 2058637) B2058637
theorem B2744867 : Blo 1829616 2744867 := bstep (se 1 (by rfl) ⟨2058650, by rfl⟩ : syracuseStep 2744867 = 4117301) B4117301
theorem B6177329 : Blo 1829616 6177329 := bstep (se 2 (by rfl) ⟨2316498, by rfl⟩ : syracuseStep 6177329 = 4632997) B4632997
theorem B2744897 : Blo 1829616 2744897 := bstep (se 2 (by rfl) ⟨1029336, by rfl⟩ : syracuseStep 2744897 = 2058673) B2058673
theorem B2474561 : Blo 1829616 2474561 := bstep (se 2 (by rfl) ⟨927960, by rfl⟩ : syracuseStep 2474561 = 1855921) B1855921
theorem B2744915 : Blo 1829616 2744915 := bstep (se 1 (by rfl) ⟨2058686, by rfl⟩ : syracuseStep 2744915 = 4117373) B4117373
theorem B3474019 : Blo 1829616 3474019 := bstep (se 1 (by rfl) ⟨2605514, by rfl⟩ : syracuseStep 3474019 = 5211029) B5211029
theorem B2744945 : Blo 1829616 2744945 := bstep (se 2 (by rfl) ⟨1029354, by rfl⟩ : syracuseStep 2744945 = 2058709) B2058709
theorem B3089009 : Blo 1829616 3089009 := bstep (se 2 (by rfl) ⟨1158378, by rfl⟩ : syracuseStep 3089009 = 2316757) B2316757
theorem B2744963 : Blo 1829616 2744963 := bstep (se 1 (by rfl) ⟨2058722, by rfl⟩ : syracuseStep 2744963 = 4117445) B4117445
theorem B3474065 : Blo 1829616 3474065 := bstep (se 2 (by rfl) ⟨1302774, by rfl⟩ : syracuseStep 3474065 = 2605549) B2605549
theorem B2744993 : Blo 1829616 2744993 := bstep (se 2 (by rfl) ⟨1029372, by rfl⟩ : syracuseStep 2744993 = 2058745) B2058745
theorem B6947491 : Blo 1829616 6947491 := bstep (se 1 (by rfl) ⟨5210618, by rfl⟩ : syracuseStep 6947491 = 10421237) B10421237
theorem B5210801 : Blo 1829616 5210801 := bstep (se 2 (by rfl) ⟨1954050, by rfl⟩ : syracuseStep 5210801 = 3908101) B3908101
theorem B2745011 : Blo 1829616 2745011 := bstep (se 1 (by rfl) ⟨2058758, by rfl⟩ : syracuseStep 2745011 = 4117517) B4117517
theorem B11731661 : Blo 1829616 11731661 := bstep (se 3 (by rfl) ⟨2199686, by rfl⟩ : syracuseStep 11731661 = 4399373) B4399373
theorem B2745041 : Blo 1829616 2745041 := bstep (se 2 (by rfl) ⟨1029390, by rfl⟩ : syracuseStep 2745041 = 2058781) B2058781
theorem B2745059 : Blo 1829616 2745059 := bstep (se 1 (by rfl) ⟨2058794, by rfl⟩ : syracuseStep 2745059 = 4117589) B4117589
theorem B3089137 : Blo 1829616 3089137 := bstep (se 2 (by rfl) ⟨1158426, by rfl⟩ : syracuseStep 3089137 = 2316853) B2316853
theorem B2745089 : Blo 1829616 2745089 := bstep (se 2 (by rfl) ⟨1029408, by rfl⟩ : syracuseStep 2745089 = 2058817) B2058817
theorem B5866253 : Blo 1829616 5866253 := bstep (se 3 (by rfl) ⟨1099922, by rfl⟩ : syracuseStep 5866253 = 2199845) B2199845
theorem B2745107 : Blo 1829616 2745107 := bstep (se 1 (by rfl) ⟨2058830, by rfl⟩ : syracuseStep 2745107 = 4117661) B4117661
theorem B3089171 : Blo 1829616 3089171 := bstep (se 1 (by rfl) ⟨2316878, by rfl⟩ : syracuseStep 3089171 = 4633757) B4633757
theorem B150340373 : Blo 1829616 150340373 := bstep (se 6 (by rfl) ⟨3523602, by rfl⟩ : syracuseStep 150340373 = 7047205) B7047205
theorem B2745137 : Blo 1829616 2745137 := bstep (se 2 (by rfl) ⟨1029426, by rfl⟩ : syracuseStep 2745137 = 2058853) B2058853
theorem B2745155 : Blo 1829616 2745155 := bstep (se 1 (by rfl) ⟨2058866, by rfl⟩ : syracuseStep 2745155 = 4117733) B4117733
theorem B2745185 : Blo 1829616 2745185 := bstep (se 2 (by rfl) ⟨1029444, by rfl⟩ : syracuseStep 2745185 = 2058889) B2058889
theorem B2745203 : Blo 1829616 2745203 := bstep (se 1 (by rfl) ⟨2058902, by rfl⟩ : syracuseStep 2745203 = 4117805) B4117805
theorem B2933633 : Blo 1829616 2933633 := bstep (se 2 (by rfl) ⟨1100112, by rfl⟩ : syracuseStep 2933633 = 2200225) B2200225
theorem B2745233 : Blo 1829616 2745233 := bstep (se 2 (by rfl) ⟨1029462, by rfl⟩ : syracuseStep 2745233 = 2058925) B2058925
theorem B3089299 : Blo 1829616 3089299 := bstep (se 1 (by rfl) ⟨2316974, by rfl⟩ : syracuseStep 3089299 = 4633949) B4633949
theorem B2745251 : Blo 1829616 2745251 := bstep (se 1 (by rfl) ⟨2058938, by rfl⟩ : syracuseStep 2745251 = 4117877) B4117877
theorem B3474353 : Blo 1829616 3474353 := bstep (se 2 (by rfl) ⟨1302882, by rfl⟩ : syracuseStep 3474353 = 2605765) B2605765
theorem B2745281 : Blo 1829616 2745281 := bstep (se 2 (by rfl) ⟨1029480, by rfl⟩ : syracuseStep 2745281 = 2058961) B2058961
theorem B102949829 : Blo 1829616 102949829 := bstep (se 4 (by rfl) ⟨9651546, by rfl⟩ : syracuseStep 102949829 = 19303093) B19303093
theorem B14844869 : Blo 1829616 14844869 := bstep (se 4 (by rfl) ⟨1391706, by rfl⟩ : syracuseStep 14844869 = 2783413) B2783413
theorem B5866445 : Blo 1829616 5866445 := bstep (se 3 (by rfl) ⟨1099958, by rfl⟩ : syracuseStep 5866445 = 2199917) B2199917
theorem B2606033 : Blo 1829616 2606033 := bstep (se 2 (by rfl) ⟨977262, by rfl⟩ : syracuseStep 2606033 = 1954525) B1954525
theorem B2745299 : Blo 1829616 2745299 := bstep (se 1 (by rfl) ⟨2058974, by rfl⟩ : syracuseStep 2745299 = 4117949) B4117949
theorem B3908579 : Blo 1829616 3908579 := bstep (se 1 (by rfl) ⟨2931434, by rfl⟩ : syracuseStep 3908579 = 5862869) B5862869
theorem B2745329 : Blo 1829616 2745329 := bstep (se 2 (by rfl) ⟨1029498, by rfl⟩ : syracuseStep 2745329 = 2058997) B2058997
theorem B3130355 : Blo 1829616 3130355 := bstep (se 1 (by rfl) ⟨2347766, by rfl⟩ : syracuseStep 3130355 = 4695533) B4695533
theorem B2745347 : Blo 1829616 2745347 := bstep (se 1 (by rfl) ⟨2059010, by rfl⟩ : syracuseStep 2745347 = 4118021) B4118021
theorem B2745377 : Blo 1829616 2745377 := bstep (se 2 (by rfl) ⟨1029516, by rfl⟩ : syracuseStep 2745377 = 2059033) B2059033
theorem B3089441 : Blo 1829616 3089441 := bstep (se 2 (by rfl) ⟨1158540, by rfl⟩ : syracuseStep 3089441 = 2317081) B2317081
theorem B2745395 : Blo 1829616 2745395 := bstep (se 1 (by rfl) ⟨2059046, by rfl⟩ : syracuseStep 2745395 = 4118093) B4118093
theorem B27124789 : Blo 1829616 27124789 := bstep (se 5 (by rfl) ⟨1271474, by rfl⟩ : syracuseStep 27124789 = 2542949) B2542949
theorem B6177869 : Blo 1829616 6177869 := bstep (se 3 (by rfl) ⟨1158350, by rfl⟩ : syracuseStep 6177869 = 2316701) B2316701
theorem B2745425 : Blo 1829616 2745425 := bstep (se 2 (by rfl) ⟨1029534, by rfl⟩ : syracuseStep 2745425 = 2059069) B2059069
theorem B2933857 : Blo 1829616 2933857 := bstep (se 2 (by rfl) ⟨1100196, by rfl⟩ : syracuseStep 2933857 = 2200393) B2200393
theorem B2745443 : Blo 1829616 2745443 := bstep (se 1 (by rfl) ⟨2059082, by rfl⟩ : syracuseStep 2745443 = 4118165) B4118165
theorem B4400227 : Blo 1829616 4400227 := bstep (se 1 (by rfl) ⟨3300170, by rfl⟩ : syracuseStep 4400227 = 6600341) B6600341
theorem B2745473 : Blo 1829616 2745473 := bstep (se 2 (by rfl) ⟨1029552, by rfl⟩ : syracuseStep 2745473 = 2059105) B2059105
theorem B6177923 : Blo 1829616 6177923 := bstep (se 1 (by rfl) ⟨4633442, by rfl⟩ : syracuseStep 6177923 = 9266885) B9266885
theorem B2745491 : Blo 1829616 2745491 := bstep (se 1 (by rfl) ⟨2059118, by rfl⟩ : syracuseStep 2745491 = 4118237) B4118237
theorem B3089569 : Blo 1829616 3089569 := bstep (se 2 (by rfl) ⟨1158588, by rfl⟩ : syracuseStep 3089569 = 2317177) B2317177
theorem B2745521 : Blo 1829616 2745521 := bstep (se 2 (by rfl) ⟨1029570, by rfl⟩ : syracuseStep 2745521 = 2059141) B2059141
theorem B2745539 : Blo 1829616 2745539 := bstep (se 1 (by rfl) ⟨2059154, by rfl⟩ : syracuseStep 2745539 = 4118309) B4118309
theorem B3089603 : Blo 1829616 3089603 := bstep (se 1 (by rfl) ⟨2317202, by rfl⟩ : syracuseStep 3089603 = 4634405) B4634405
theorem B2745569 : Blo 1829616 2745569 := bstep (se 2 (by rfl) ⟨1029588, by rfl⟩ : syracuseStep 2745569 = 2059177) B2059177
theorem B10429667 : Blo 1829616 10429667 := bstep (se 1 (by rfl) ⟨7822250, by rfl⟩ : syracuseStep 10429667 = 15644501) B15644501
theorem B17597681 : Blo 1829616 17597681 := bstep (se 2 (by rfl) ⟨6599130, by rfl⟩ : syracuseStep 17597681 = 13198261) B13198261
theorem B2745587 : Blo 1829616 2745587 := bstep (se 1 (by rfl) ⟨2059190, by rfl⟩ : syracuseStep 2745587 = 4118381) B4118381
theorem B2745617 : Blo 1829616 2745617 := bstep (se 2 (by rfl) ⟨1029606, by rfl⟩ : syracuseStep 2745617 = 2059213) B2059213
theorem B2745635 : Blo 1829616 2745635 := bstep (se 1 (by rfl) ⟨2059226, by rfl⟩ : syracuseStep 2745635 = 4118453) B4118453
theorem B2745665 : Blo 1829616 2745665 := bstep (se 2 (by rfl) ⟨1029624, by rfl⟩ : syracuseStep 2745665 = 2059249) B2059249
theorem B3089731 : Blo 1829616 3089731 := bstep (se 1 (by rfl) ⟨2317298, by rfl⟩ : syracuseStep 3089731 = 4634597) B4634597
theorem B4457809 : Blo 1829616 4457809 := bstep (se 2 (by rfl) ⟨1671678, by rfl⟩ : syracuseStep 4457809 = 3343357) B3343357
theorem B2745683 : Blo 1829616 2745683 := bstep (se 1 (by rfl) ⟨2059262, by rfl⟩ : syracuseStep 2745683 = 4118525) B4118525
theorem B20055395 : Blo 1829616 20055395 := bstep (se 1 (by rfl) ⟨15041546, by rfl⟩ : syracuseStep 20055395 = 30083093) B30083093
theorem B2745713 : Blo 1829616 2745713 := bstep (se 2 (by rfl) ⟨1029642, by rfl⟩ : syracuseStep 2745713 = 2059285) B2059285
theorem B4400497 : Blo 1829616 4400497 := bstep (se 2 (by rfl) ⟨1650186, by rfl⟩ : syracuseStep 4400497 = 3300373) B3300373
theorem B2745731 : Blo 1829616 2745731 := bstep (se 1 (by rfl) ⟨2059298, by rfl⟩ : syracuseStep 2745731 = 4118597) B4118597
theorem B6178193 : Blo 1829616 6178193 := bstep (se 2 (by rfl) ⟨2316822, by rfl⟩ : syracuseStep 6178193 = 4633645) B4633645
theorem B2745761 : Blo 1829616 2745761 := bstep (se 2 (by rfl) ⟨1029660, by rfl⟩ : syracuseStep 2745761 = 2059321) B2059321
theorem B12387761 : Blo 1829616 12387761 := bstep (se 2 (by rfl) ⟨4645410, by rfl⟩ : syracuseStep 12387761 = 9290821) B9290821
theorem B2745779 : Blo 1829616 2745779 := bstep (se 1 (by rfl) ⟨2059334, by rfl⟩ : syracuseStep 2745779 = 4118669) B4118669
theorem B2745809 : Blo 1829616 2745809 := bstep (se 2 (by rfl) ⟨1029678, by rfl⟩ : syracuseStep 2745809 = 2059357) B2059357
theorem B3089873 : Blo 1829616 3089873 := bstep (se 2 (by rfl) ⟨1158702, by rfl⟩ : syracuseStep 3089873 = 2317405) B2317405
theorem B2745827 : Blo 1829616 2745827 := bstep (se 1 (by rfl) ⟨2059370, by rfl⟩ : syracuseStep 2745827 = 4118741) B4118741
theorem B5645809 : Blo 1829616 5645809 := bstep (se 2 (by rfl) ⟨2117178, by rfl⟩ : syracuseStep 5645809 = 4234357) B4234357
theorem B2745857 : Blo 1829616 2745857 := bstep (se 2 (by rfl) ⟨1029696, by rfl⟩ : syracuseStep 2745857 = 2059393) B2059393
theorem B2745875 : Blo 1829616 2745875 := bstep (se 1 (by rfl) ⟨2059406, by rfl⟩ : syracuseStep 2745875 = 4118813) B4118813
theorem B9266723 : Blo 1829616 9266723 := bstep (se 1 (by rfl) ⟨6950042, by rfl⟩ : syracuseStep 9266723 = 13900085) B13900085
theorem B2745905 : Blo 1829616 2745905 := bstep (se 2 (by rfl) ⟨1029714, by rfl⟩ : syracuseStep 2745905 = 2059429) B2059429
theorem B2745923 : Blo 1829616 2745923 := bstep (se 1 (by rfl) ⟨2059442, by rfl⟩ : syracuseStep 2745923 = 4118885) B4118885
theorem B3090001 : Blo 1829616 3090001 := bstep (se 2 (by rfl) ⟨1158750, by rfl⟩ : syracuseStep 3090001 = 2317501) B2317501
theorem B2745953 : Blo 1829616 2745953 := bstep (se 2 (by rfl) ⟨1029732, by rfl⟩ : syracuseStep 2745953 = 2059465) B2059465
theorem B7816817 : Blo 1829616 7816817 := bstep (se 2 (by rfl) ⟨2931306, by rfl⟩ : syracuseStep 7816817 = 5862613) B5862613
theorem B2745971 : Blo 1829616 2745971 := bstep (se 1 (by rfl) ⟨2059478, by rfl⟩ : syracuseStep 2745971 = 4118957) B4118957
theorem B3090035 : Blo 1829616 3090035 := bstep (se 1 (by rfl) ⟨2317526, by rfl⟩ : syracuseStep 3090035 = 4635053) B4635053
theorem B3475075 : Blo 1829616 3475075 := bstep (se 1 (by rfl) ⟨2606306, by rfl⟩ : syracuseStep 3475075 = 5212613) B5212613
theorem B2746001 : Blo 1829616 2746001 := bstep (se 2 (by rfl) ⟨1029750, by rfl⟩ : syracuseStep 2746001 = 2059501) B2059501
theorem B4695715 : Blo 1829616 4695715 := bstep (se 1 (by rfl) ⟨3521786, by rfl⟩ : syracuseStep 4695715 = 7043573) B7043573
theorem B2746019 : Blo 1829616 2746019 := bstep (se 1 (by rfl) ⟨2059514, by rfl⟩ : syracuseStep 2746019 = 4119029) B4119029
theorem B2746049 : Blo 1829616 2746049 := bstep (se 2 (by rfl) ⟨1029768, by rfl⟩ : syracuseStep 2746049 = 2059537) B2059537
theorem B2746067 : Blo 1829616 2746067 := bstep (se 1 (by rfl) ⟨2059550, by rfl⟩ : syracuseStep 2746067 = 4119101) B4119101
theorem B2746097 : Blo 1829616 2746097 := bstep (se 2 (by rfl) ⟨1029786, by rfl⟩ : syracuseStep 2746097 = 2059573) B2059573
theorem B3090163 : Blo 1829616 3090163 := bstep (se 1 (by rfl) ⟨2317622, by rfl⟩ : syracuseStep 3090163 = 4635245) B4635245
theorem B2746115 : Blo 1829616 2746115 := bstep (se 1 (by rfl) ⟨2059586, by rfl⟩ : syracuseStep 2746115 = 4119173) B4119173
theorem B17598221 : Blo 1829616 17598221 := bstep (se 3 (by rfl) ⟨3299666, by rfl⟩ : syracuseStep 17598221 = 6599333) B6599333
theorem B2746145 : Blo 1829616 2746145 := bstep (se 2 (by rfl) ⟨1029804, by rfl⟩ : syracuseStep 2746145 = 2059609) B2059609
theorem B2746163 : Blo 1829616 2746163 := bstep (se 1 (by rfl) ⟨2059622, by rfl⟩ : syracuseStep 2746163 = 4119245) B4119245
theorem B2606899 : Blo 1829616 2606899 := bstep (se 1 (by rfl) ⟨1955174, by rfl⟩ : syracuseStep 2606899 = 3910349) B3910349
theorem B19793717 : Blo 1829616 19793717 := bstep (se 5 (by rfl) ⟨927830, by rfl⟩ : syracuseStep 19793717 = 1855661) B1855661
theorem B2746193 : Blo 1829616 2746193 := bstep (se 2 (by rfl) ⟨1029822, by rfl⟩ : syracuseStep 2746193 = 2059645) B2059645
theorem B2746211 : Blo 1829616 2746211 := bstep (se 1 (by rfl) ⟨2059658, by rfl⟩ : syracuseStep 2746211 = 4119317) B4119317
theorem B4949869 : Blo 1829616 4949869 := bstep (se 3 (by rfl) ⟨928100, by rfl⟩ : syracuseStep 4949869 = 1856201) B1856201
theorem B2746241 : Blo 1829616 2746241 := bstep (se 2 (by rfl) ⟨1029840, by rfl⟩ : syracuseStep 2746241 = 2059681) B2059681
theorem B3090305 : Blo 1829616 3090305 := bstep (se 2 (by rfl) ⟨1158864, by rfl⟩ : syracuseStep 3090305 = 2317729) B2317729
theorem B2746259 : Blo 1829616 2746259 := bstep (se 1 (by rfl) ⟨2059694, by rfl⟩ : syracuseStep 2746259 = 4119389) B4119389
theorem B2606995 : Blo 1829616 2606995 := bstep (se 1 (by rfl) ⟨1955246, by rfl⟩ : syracuseStep 2606995 = 3910493) B3910493
theorem B6178733 : Blo 1829616 6178733 := bstep (se 3 (by rfl) ⟨1158512, by rfl⟩ : syracuseStep 6178733 = 2317025) B2317025
theorem B2746289 : Blo 1829616 2746289 := bstep (se 2 (by rfl) ⟨1029858, by rfl⟩ : syracuseStep 2746289 = 2059717) B2059717
theorem B2746307 : Blo 1829616 2746307 := bstep (se 1 (by rfl) ⟨2059730, by rfl⟩ : syracuseStep 2746307 = 4119461) B4119461
theorem B2746337 : Blo 1829616 2746337 := bstep (se 2 (by rfl) ⟨1029876, by rfl⟩ : syracuseStep 2746337 = 2059753) B2059753
theorem B6178787 : Blo 1829616 6178787 := bstep (se 1 (by rfl) ⟨4634090, by rfl⟩ : syracuseStep 6178787 = 9268181) B9268181
theorem B2746355 : Blo 1829616 2746355 := bstep (se 1 (by rfl) ⟨2059766, by rfl⟩ : syracuseStep 2746355 = 4119533) B4119533
theorem B3090433 : Blo 1829616 3090433 := bstep (se 2 (by rfl) ⟨1158912, by rfl⟩ : syracuseStep 3090433 = 2317825) B2317825
theorem B2746385 : Blo 1829616 2746385 := bstep (se 2 (by rfl) ⟨1029894, by rfl⟩ : syracuseStep 2746385 = 2059789) B2059789
theorem B2746403 : Blo 1829616 2746403 := bstep (se 1 (by rfl) ⟨2059802, by rfl⟩ : syracuseStep 2746403 = 4119605) B4119605
theorem B3090467 : Blo 1829616 3090467 := bstep (se 1 (by rfl) ⟨2317850, by rfl⟩ : syracuseStep 3090467 = 4635701) B4635701
theorem B2746433 : Blo 1829616 2746433 := bstep (se 2 (by rfl) ⟨1029912, by rfl⟩ : syracuseStep 2746433 = 2059825) B2059825
theorem B3475523 : Blo 1829616 3475523 := bstep (se 1 (by rfl) ⟨2606642, by rfl⟩ : syracuseStep 3475523 = 5213285) B5213285
theorem B2746451 : Blo 1829616 2746451 := bstep (se 1 (by rfl) ⟨2059838, by rfl⟩ : syracuseStep 2746451 = 4119677) B4119677
theorem B2009171 : Blo 1829616 2009171 := bstep (se 1 (by rfl) ⟨1506878, by rfl⟩ : syracuseStep 2009171 = 3013757) B3013757
theorem B5212259 : Blo 1829616 5212259 := bstep (se 1 (by rfl) ⟨3909194, by rfl⟩ : syracuseStep 5212259 = 7818389) B7818389
theorem B2746481 : Blo 1829616 2746481 := bstep (se 2 (by rfl) ⟨1029930, by rfl⟩ : syracuseStep 2746481 = 2059861) B2059861
theorem B2746499 : Blo 1829616 2746499 := bstep (se 1 (by rfl) ⟨2059874, by rfl⟩ : syracuseStep 2746499 = 4119749) B4119749
theorem B5564561 : Blo 1829616 5564561 := bstep (se 2 (by rfl) ⟨2086710, by rfl⟩ : syracuseStep 5564561 = 4173421) B4173421
theorem B2746529 : Blo 1829616 2746529 := bstep (se 2 (by rfl) ⟨1029948, by rfl⟩ : syracuseStep 2746529 = 2059897) B2059897
theorem B2058403 : Blo 1829616 2058403 := bstep (se 1 (by rfl) ⟨1543802, by rfl⟩ : syracuseStep 2058403 = 3087605) B3087605
theorem B3090595 : Blo 1829616 3090595 := bstep (se 1 (by rfl) ⟨2317946, by rfl⟩ : syracuseStep 3090595 = 4635893) B4635893
theorem B2746547 : Blo 1829616 2746547 := bstep (se 1 (by rfl) ⟨2059910, by rfl⟩ : syracuseStep 2746547 = 4119821) B4119821
theorem B2746577 : Blo 1829616 2746577 := bstep (se 2 (by rfl) ⟨1029966, by rfl⟩ : syracuseStep 2746577 = 2059933) B2059933
theorem B2746595 : Blo 1829616 2746595 := bstep (se 1 (by rfl) ⟨2059946, by rfl⟩ : syracuseStep 2746595 = 4119893) B4119893
theorem B6179057 : Blo 1829616 6179057 := bstep (se 2 (by rfl) ⟨2317146, by rfl⟩ : syracuseStep 6179057 = 4634293) B4634293
theorem B2746625 : Blo 1829616 2746625 := bstep (se 2 (by rfl) ⟨1029984, by rfl⟩ : syracuseStep 2746625 = 2059969) B2059969
theorem B2746643 : Blo 1829616 2746643 := bstep (se 1 (by rfl) ⟨2059982, by rfl⟩ : syracuseStep 2746643 = 4119965) B4119965
theorem B2746673 : Blo 1829616 2746673 := bstep (se 2 (by rfl) ⟨1030002, by rfl⟩ : syracuseStep 2746673 = 2060005) B2060005
theorem B3090737 : Blo 1829616 3090737 := bstep (se 2 (by rfl) ⟨1159026, by rfl⟩ : syracuseStep 3090737 = 2318053) B2318053
theorem B2058547 : Blo 1829616 2058547 := bstep (se 1 (by rfl) ⟨1543910, by rfl⟩ : syracuseStep 2058547 = 3087821) B3087821
theorem B2746691 : Blo 1829616 2746691 := bstep (se 1 (by rfl) ⟨2060018, by rfl⟩ : syracuseStep 2746691 = 4120037) B4120037
theorem B9267533 : Blo 1829616 9267533 := bstep (se 3 (by rfl) ⟨1737662, by rfl⟩ : syracuseStep 9267533 = 3475325) B3475325
theorem B2746721 : Blo 1829616 2746721 := bstep (se 2 (by rfl) ⟨1030020, by rfl⟩ : syracuseStep 2746721 = 2060041) B2060041
theorem B12691811 : Blo 1829616 12691811 := bstep (se 1 (by rfl) ⟨9518858, by rfl⟩ : syracuseStep 12691811 = 19037717) B19037717
theorem B3475811 : Blo 1829616 3475811 := bstep (se 1 (by rfl) ⟨2606858, by rfl⟩ : syracuseStep 3475811 = 5213717) B5213717
theorem B2746739 : Blo 1829616 2746739 := bstep (se 1 (by rfl) ⟨2060054, by rfl⟩ : syracuseStep 2746739 = 4120109) B4120109
theorem B2607491 : Blo 1829616 2607491 := bstep (se 1 (by rfl) ⟨1955618, by rfl⟩ : syracuseStep 2607491 = 3911237) B3911237
theorem B2746769 : Blo 1829616 2746769 := bstep (se 2 (by rfl) ⟨1030038, by rfl⟩ : syracuseStep 2746769 = 2060077) B2060077
theorem B2746787 : Blo 1829616 2746787 := bstep (se 1 (by rfl) ⟨2060090, by rfl⟩ : syracuseStep 2746787 = 4120181) B4120181
theorem B2746817 : Blo 1829616 2746817 := bstep (se 2 (by rfl) ⟨1030056, by rfl⟩ : syracuseStep 2746817 = 2060113) B2060113
theorem B2058691 : Blo 1829616 2058691 := bstep (se 1 (by rfl) ⟨1544018, by rfl⟩ : syracuseStep 2058691 = 3088037) B3088037
theorem B2746835 : Blo 1829616 2746835 := bstep (se 1 (by rfl) ⟨2060126, by rfl⟩ : syracuseStep 2746835 = 4120253) B4120253
theorem B2746865 : Blo 1829616 2746865 := bstep (se 2 (by rfl) ⟨1030074, by rfl⟩ : syracuseStep 2746865 = 2060149) B2060149
theorem B2746883 : Blo 1829616 2746883 := bstep (se 1 (by rfl) ⟨2060162, by rfl⟩ : syracuseStep 2746883 = 4120325) B4120325
theorem B7817741 : Blo 1829616 7817741 := bstep (se 3 (by rfl) ⟨1465826, by rfl⟩ : syracuseStep 7817741 = 2931653) B2931653
theorem B2746913 : Blo 1829616 2746913 := bstep (se 2 (by rfl) ⟨1030092, by rfl⟩ : syracuseStep 2746913 = 2060185) B2060185
theorem B2746931 : Blo 1829616 2746931 := bstep (se 1 (by rfl) ⟨2060198, by rfl⟩ : syracuseStep 2746931 = 4120397) B4120397
theorem B2746961 : Blo 1829616 2746961 := bstep (se 2 (by rfl) ⟨1030110, by rfl⟩ : syracuseStep 2746961 = 2060221) B2060221
theorem B2058835 : Blo 1829616 2058835 := bstep (se 1 (by rfl) ⟨1544126, by rfl⟩ : syracuseStep 2058835 = 3088253) B3088253
theorem B2746979 : Blo 1829616 2746979 := bstep (se 1 (by rfl) ⟨2060234, by rfl⟩ : syracuseStep 2746979 = 4120469) B4120469
theorem B2747009 : Blo 1829616 2747009 := bstep (se 2 (by rfl) ⟨1030128, by rfl⟩ : syracuseStep 2747009 = 2060257) B2060257
theorem B2747027 : Blo 1829616 2747027 := bstep (se 1 (by rfl) ⟨2060270, by rfl⟩ : syracuseStep 2747027 = 4120541) B4120541
theorem B2747057 : Blo 1829616 2747057 := bstep (se 2 (by rfl) ⟨1030146, by rfl⟩ : syracuseStep 2747057 = 2060293) B2060293
theorem B2747075 : Blo 1829616 2747075 := bstep (se 1 (by rfl) ⟨2060306, by rfl⟩ : syracuseStep 2747075 = 4120613) B4120613
theorem B4950733 : Blo 1829616 4950733 := bstep (se 3 (by rfl) ⟨928262, by rfl⟩ : syracuseStep 4950733 = 1856525) B1856525
theorem B2747105 : Blo 1829616 2747105 := bstep (se 2 (by rfl) ⟨1030164, by rfl⟩ : syracuseStep 2747105 = 2060329) B2060329
theorem B2058979 : Blo 1829616 2058979 := bstep (se 1 (by rfl) ⟨1544234, by rfl⟩ : syracuseStep 2058979 = 3088469) B3088469
theorem B1829619 : Blo 1829616 1829619 := bstep (se 1 (by rfl) ⟨1372214, by rfl⟩ : syracuseStep 1829619 = 2744429) B2744429
theorem B2747123 : Blo 1829616 2747123 := bstep (se 1 (by rfl) ⟨2060342, by rfl⟩ : syracuseStep 2747123 = 4120685) B4120685
theorem B1829635 : Blo 1829616 1829635 := bstep (se 1 (by rfl) ⟨1372226, by rfl⟩ : syracuseStep 1829635 = 2744453) B2744453
theorem B6179597 : Blo 1829616 6179597 := bstep (se 3 (by rfl) ⟨1158674, by rfl⟩ : syracuseStep 6179597 = 2317349) B2317349
theorem B2747153 : Blo 1829616 2747153 := bstep (se 2 (by rfl) ⟨1030182, by rfl⟩ : syracuseStep 2747153 = 2060365) B2060365
theorem B1829651 : Blo 1829616 1829651 := bstep (se 1 (by rfl) ⟨1372238, by rfl⟩ : syracuseStep 1829651 = 2744477) B2744477
theorem B1829667 : Blo 1829616 1829667 := bstep (se 1 (by rfl) ⟨1372250, by rfl⟩ : syracuseStep 1829667 = 2744501) B2744501
theorem B2747171 : Blo 1829616 2747171 := bstep (se 1 (by rfl) ⟨2060378, by rfl⟩ : syracuseStep 2747171 = 4120757) B4120757
theorem B1829683 : Blo 1829616 1829683 := bstep (se 1 (by rfl) ⟨1372262, by rfl⟩ : syracuseStep 1829683 = 2744525) B2744525
theorem B2747201 : Blo 1829616 2747201 := bstep (se 2 (by rfl) ⟨1030200, by rfl⟩ : syracuseStep 2747201 = 2060401) B2060401
theorem B1829699 : Blo 1829616 1829699 := bstep (se 1 (by rfl) ⟨1372274, by rfl⟩ : syracuseStep 1829699 = 2744549) B2744549
theorem B6179651 : Blo 1829616 6179651 := bstep (se 1 (by rfl) ⟨4634738, by rfl⟩ : syracuseStep 6179651 = 9269477) B9269477
theorem B6949709 : Blo 1829616 6949709 := bstep (se 3 (by rfl) ⟨1303070, by rfl⟩ : syracuseStep 6949709 = 2606141) B2606141
theorem B4631377 : Blo 1829616 4631377 := bstep (se 2 (by rfl) ⟨1736766, by rfl⟩ : syracuseStep 4631377 = 3473533) B3473533
theorem B1829715 : Blo 1829616 1829715 := bstep (se 1 (by rfl) ⟨1372286, by rfl⟩ : syracuseStep 1829715 = 2744573) B2744573
theorem B2747219 : Blo 1829616 2747219 := bstep (se 1 (by rfl) ⟨2060414, by rfl⟩ : syracuseStep 2747219 = 4120829) B4120829
theorem B1829731 : Blo 1829616 1829731 := bstep (se 1 (by rfl) ⟨1372298, by rfl⟩ : syracuseStep 1829731 = 2744597) B2744597
theorem B2747249 : Blo 1829616 2747249 := bstep (se 2 (by rfl) ⟨1030218, by rfl⟩ : syracuseStep 2747249 = 2060437) B2060437
theorem B1829747 : Blo 1829616 1829747 := bstep (se 1 (by rfl) ⟨1372310, by rfl⟩ : syracuseStep 1829747 = 2744621) B2744621
theorem B2059123 : Blo 1829616 2059123 := bstep (se 1 (by rfl) ⟨1544342, by rfl⟩ : syracuseStep 2059123 = 3088685) B3088685
theorem B1829763 : Blo 1829616 1829763 := bstep (se 1 (by rfl) ⟨1372322, by rfl⟩ : syracuseStep 1829763 = 2744645) B2744645
theorem B2747267 : Blo 1829616 2747267 := bstep (se 1 (by rfl) ⟨2060450, by rfl⟩ : syracuseStep 2747267 = 4120901) B4120901
theorem B5213069 : Blo 1829616 5213069 := bstep (se 3 (by rfl) ⟨977450, by rfl⟩ : syracuseStep 5213069 = 1954901) B1954901
theorem B1829779 : Blo 1829616 1829779 := bstep (se 1 (by rfl) ⟨1372334, by rfl⟩ : syracuseStep 1829779 = 2744669) B2744669
theorem B2747297 : Blo 1829616 2747297 := bstep (se 2 (by rfl) ⟨1030236, by rfl⟩ : syracuseStep 2747297 = 2060473) B2060473
theorem B1829795 : Blo 1829616 1829795 := bstep (se 1 (by rfl) ⟨1372346, by rfl⟩ : syracuseStep 1829795 = 2744693) B2744693
theorem B1829811 : Blo 1829616 1829811 := bstep (se 1 (by rfl) ⟨1372358, by rfl⟩ : syracuseStep 1829811 = 2744717) B2744717
theorem B2747315 : Blo 1829616 2747315 := bstep (se 1 (by rfl) ⟨2060486, by rfl⟩ : syracuseStep 2747315 = 4120973) B4120973
theorem B1829827 : Blo 1829616 1829827 := bstep (se 1 (by rfl) ⟨1372370, by rfl⟩ : syracuseStep 1829827 = 2744741) B2744741
theorem B2747345 : Blo 1829616 2747345 := bstep (se 2 (by rfl) ⟨1030254, by rfl⟩ : syracuseStep 2747345 = 2060509) B2060509
theorem B1829843 : Blo 1829616 1829843 := bstep (se 1 (by rfl) ⟨1372382, by rfl⟩ : syracuseStep 1829843 = 2744765) B2744765
theorem B1829859 : Blo 1829616 1829859 := bstep (se 1 (by rfl) ⟨1372394, by rfl⟩ : syracuseStep 1829859 = 2744789) B2744789
theorem B2747363 : Blo 1829616 2747363 := bstep (se 1 (by rfl) ⟨2060522, by rfl⟩ : syracuseStep 2747363 = 4121045) B4121045
theorem B8793073 : Blo 1829616 8793073 := bstep (se 2 (by rfl) ⟨3297402, by rfl⟩ : syracuseStep 8793073 = 6594805) B6594805
theorem B1829875 : Blo 1829616 1829875 := bstep (se 1 (by rfl) ⟨1372406, by rfl⟩ : syracuseStep 1829875 = 2744813) B2744813
theorem B2821105 : Blo 1829616 2821105 := bstep (se 2 (by rfl) ⟨1057914, by rfl⟩ : syracuseStep 2821105 = 2115829) B2115829
theorem B2747393 : Blo 1829616 2747393 := bstep (se 2 (by rfl) ⟨1030272, by rfl⟩ : syracuseStep 2747393 = 2060545) B2060545
theorem B1829891 : Blo 1829616 1829891 := bstep (se 1 (by rfl) ⟨1372418, by rfl⟩ : syracuseStep 1829891 = 2744837) B2744837
theorem B2059267 : Blo 1829616 2059267 := bstep (se 1 (by rfl) ⟨1544450, by rfl⟩ : syracuseStep 2059267 = 3088901) B3088901
theorem B1829907 : Blo 1829616 1829907 := bstep (se 1 (by rfl) ⟨1372430, by rfl⟩ : syracuseStep 1829907 = 2744861) B2744861
theorem B2747411 : Blo 1829616 2747411 := bstep (se 1 (by rfl) ⟨2060558, by rfl⟩ : syracuseStep 2747411 = 4121117) B4121117
theorem B1829923 : Blo 1829616 1829923 := bstep (se 1 (by rfl) ⟨1372442, by rfl⟩ : syracuseStep 1829923 = 2744885) B2744885
theorem B1829939 : Blo 1829616 1829939 := bstep (se 1 (by rfl) ⟨1372454, by rfl⟩ : syracuseStep 1829939 = 2744909) B2744909
theorem B1829955 : Blo 1829616 1829955 := bstep (se 1 (by rfl) ⟨1372466, by rfl⟩ : syracuseStep 1829955 = 2744933) B2744933
theorem B6687821 : Blo 1829616 6687821 := bstep (se 3 (by rfl) ⟨1253966, by rfl⟩ : syracuseStep 6687821 = 2507933) B2507933
theorem B5213261 : Blo 1829616 5213261 := bstep (se 3 (by rfl) ⟨977486, by rfl⟩ : syracuseStep 5213261 = 1954973) B1954973
theorem B6179921 : Blo 1829616 6179921 := bstep (se 2 (by rfl) ⟨2317470, by rfl⟩ : syracuseStep 6179921 = 4634941) B4634941
theorem B1829971 : Blo 1829616 1829971 := bstep (se 1 (by rfl) ⟨1372478, by rfl⟩ : syracuseStep 1829971 = 2744957) B2744957
theorem B4631651 : Blo 1829616 4631651 := bstep (se 1 (by rfl) ⟨3473738, by rfl⟩ : syracuseStep 4631651 = 6947477) B6947477
theorem B1829987 : Blo 1829616 1829987 := bstep (se 1 (by rfl) ⟨1372490, by rfl⟩ : syracuseStep 1829987 = 2744981) B2744981
theorem B1830003 : Blo 1829616 1830003 := bstep (se 1 (by rfl) ⟨1372502, by rfl⟩ : syracuseStep 1830003 = 2745005) B2745005
theorem B1830019 : Blo 1829616 1830019 := bstep (se 1 (by rfl) ⟨1372514, by rfl⟩ : syracuseStep 1830019 = 2745029) B2745029
theorem B3910801 : Blo 1829616 3910801 := bstep (se 2 (by rfl) ⟨1466550, by rfl⟩ : syracuseStep 3910801 = 2933101) B2933101
theorem B1830035 : Blo 1829616 1830035 := bstep (se 1 (by rfl) ⟨1372526, by rfl⟩ : syracuseStep 1830035 = 2745053) B2745053
theorem B2059411 : Blo 1829616 2059411 := bstep (se 1 (by rfl) ⟨1544558, by rfl⟩ : syracuseStep 2059411 = 3089117) B3089117
theorem B1830051 : Blo 1829616 1830051 := bstep (se 1 (by rfl) ⟨1372538, by rfl⟩ : syracuseStep 1830051 = 2745077) B2745077
theorem B1830067 : Blo 1829616 1830067 := bstep (se 1 (by rfl) ⟨1372550, by rfl⟩ : syracuseStep 1830067 = 2745101) B2745101
theorem B1830083 : Blo 1829616 1830083 := bstep (se 1 (by rfl) ⟨1372562, by rfl⟩ : syracuseStep 1830083 = 2745125) B2745125
theorem B1830099 : Blo 1829616 1830099 := bstep (se 1 (by rfl) ⟨1372574, by rfl⟩ : syracuseStep 1830099 = 2745149) B2745149
theorem B1830115 : Blo 1829616 1830115 := bstep (se 1 (by rfl) ⟨1372586, by rfl⟩ : syracuseStep 1830115 = 2745173) B2745173
theorem B1830131 : Blo 1829616 1830131 := bstep (se 1 (by rfl) ⟨1372598, by rfl⟩ : syracuseStep 1830131 = 2745197) B2745197
theorem B1830147 : Blo 1829616 1830147 := bstep (se 1 (by rfl) ⟨1372610, by rfl⟩ : syracuseStep 1830147 = 2745221) B2745221
theorem B1830163 : Blo 1829616 1830163 := bstep (se 1 (by rfl) ⟨1372622, by rfl⟩ : syracuseStep 1830163 = 2745245) B2745245
theorem B3476753 : Blo 1829616 3476753 := bstep (se 2 (by rfl) ⟨1303782, by rfl⟩ : syracuseStep 3476753 = 2607565) B2607565
theorem B4631843 : Blo 1829616 4631843 := bstep (se 1 (by rfl) ⟨3473882, by rfl⟩ : syracuseStep 4631843 = 6947765) B6947765
theorem B1830179 : Blo 1829616 1830179 := bstep (se 1 (by rfl) ⟨1372634, by rfl⟩ : syracuseStep 1830179 = 2745269) B2745269
theorem B2059555 : Blo 1829616 2059555 := bstep (se 1 (by rfl) ⟨1544666, by rfl⟩ : syracuseStep 2059555 = 3089333) B3089333
theorem B1830195 : Blo 1829616 1830195 := bstep (se 1 (by rfl) ⟨1372646, by rfl⟩ : syracuseStep 1830195 = 2745293) B2745293
theorem B1830211 : Blo 1829616 1830211 := bstep (se 1 (by rfl) ⟨1372658, by rfl⟩ : syracuseStep 1830211 = 2745317) B2745317
theorem B1830227 : Blo 1829616 1830227 := bstep (se 1 (by rfl) ⟨1372670, by rfl⟩ : syracuseStep 1830227 = 2745341) B2745341
theorem B1830243 : Blo 1829616 1830243 := bstep (se 1 (by rfl) ⟨1372682, by rfl⟩ : syracuseStep 1830243 = 2745365) B2745365
theorem B7048561 : Blo 1829616 7048561 := bstep (se 2 (by rfl) ⟨2643210, by rfl⟩ : syracuseStep 7048561 = 5286421) B5286421
theorem B1830259 : Blo 1829616 1830259 := bstep (se 1 (by rfl) ⟨1372694, by rfl⟩ : syracuseStep 1830259 = 2745389) B2745389
theorem B1830275 : Blo 1829616 1830275 := bstep (se 1 (by rfl) ⟨1372706, by rfl⟩ : syracuseStep 1830275 = 2745413) B2745413
theorem B1830291 : Blo 1829616 1830291 := bstep (se 1 (by rfl) ⟨1372718, by rfl⟩ : syracuseStep 1830291 = 2745437) B2745437
theorem B1854883 : Blo 1829616 1854883 := bstep (se 1 (by rfl) ⟨1391162, by rfl⟩ : syracuseStep 1854883 = 2782325) B2782325
theorem B1830307 : Blo 1829616 1830307 := bstep (se 1 (by rfl) ⟨1372730, by rfl⟩ : syracuseStep 1830307 = 2745461) B2745461
theorem B1830323 : Blo 1829616 1830323 := bstep (se 1 (by rfl) ⟨1372742, by rfl⟩ : syracuseStep 1830323 = 2745485) B2745485
theorem B2059699 : Blo 1829616 2059699 := bstep (se 1 (by rfl) ⟨1544774, by rfl⟩ : syracuseStep 2059699 = 3089549) B3089549
theorem B1830339 : Blo 1829616 1830339 := bstep (se 1 (by rfl) ⟨1372754, by rfl⟩ : syracuseStep 1830339 = 2745509) B2745509
theorem B1830355 : Blo 1829616 1830355 := bstep (se 1 (by rfl) ⟨1372766, by rfl⟩ : syracuseStep 1830355 = 2745533) B2745533
theorem B1830371 : Blo 1829616 1830371 := bstep (se 1 (by rfl) ⟨1372778, by rfl⟩ : syracuseStep 1830371 = 2745557) B2745557
theorem B3132913 : Blo 1829616 3132913 := bstep (se 2 (by rfl) ⟨1174842, by rfl⟩ : syracuseStep 3132913 = 2349685) B2349685
theorem B1830387 : Blo 1829616 1830387 := bstep (se 1 (by rfl) ⟨1372790, by rfl⟩ : syracuseStep 1830387 = 2745581) B2745581
theorem B1830403 : Blo 1829616 1830403 := bstep (se 1 (by rfl) ⟨1372802, by rfl⟩ : syracuseStep 1830403 = 2745605) B2745605
theorem B1830419 : Blo 1829616 1830419 := bstep (se 1 (by rfl) ⟨1372814, by rfl⟩ : syracuseStep 1830419 = 2745629) B2745629
theorem B3132961 : Blo 1829616 3132961 := bstep (se 2 (by rfl) ⟨1174860, by rfl⟩ : syracuseStep 3132961 = 2349721) B2349721
theorem B1830435 : Blo 1829616 1830435 := bstep (se 1 (by rfl) ⟨1372826, by rfl⟩ : syracuseStep 1830435 = 2745653) B2745653
theorem B1830451 : Blo 1829616 1830451 := bstep (se 1 (by rfl) ⟨1372838, by rfl⟩ : syracuseStep 1830451 = 2745677) B2745677
theorem B1830467 : Blo 1829616 1830467 := bstep (se 1 (by rfl) ⟨1372850, by rfl⟩ : syracuseStep 1830467 = 2745701) B2745701
theorem B2059843 : Blo 1829616 2059843 := bstep (se 1 (by rfl) ⟨1544882, by rfl⟩ : syracuseStep 2059843 = 3089765) B3089765
theorem B1830483 : Blo 1829616 1830483 := bstep (se 1 (by rfl) ⟨1372862, by rfl⟩ : syracuseStep 1830483 = 2745725) B2745725
theorem B1830499 : Blo 1829616 1830499 := bstep (se 1 (by rfl) ⟨1372874, by rfl⟩ : syracuseStep 1830499 = 2745749) B2745749
theorem B6180461 : Blo 1829616 6180461 := bstep (se 3 (by rfl) ⟨1158836, by rfl⟩ : syracuseStep 6180461 = 2317673) B2317673
theorem B1830515 : Blo 1829616 1830515 := bstep (se 1 (by rfl) ⟨1372886, by rfl⟩ : syracuseStep 1830515 = 2745773) B2745773
theorem B1830531 : Blo 1829616 1830531 := bstep (se 1 (by rfl) ⟨1372898, by rfl⟩ : syracuseStep 1830531 = 2745797) B2745797
theorem B1830547 : Blo 1829616 1830547 := bstep (se 1 (by rfl) ⟨1372910, by rfl⟩ : syracuseStep 1830547 = 2745821) B2745821
theorem B1830563 : Blo 1829616 1830563 := bstep (se 1 (by rfl) ⟨1372922, by rfl⟩ : syracuseStep 1830563 = 2745845) B2745845
theorem B6180515 : Blo 1829616 6180515 := bstep (se 1 (by rfl) ⟨4635386, by rfl⟩ : syracuseStep 6180515 = 9270773) B9270773
theorem B1830579 : Blo 1829616 1830579 := bstep (se 1 (by rfl) ⟨1372934, by rfl⟩ : syracuseStep 1830579 = 2745869) B2745869
theorem B1830595 : Blo 1829616 1830595 := bstep (se 1 (by rfl) ⟨1372946, by rfl⟩ : syracuseStep 1830595 = 2745893) B2745893
theorem B1830611 : Blo 1829616 1830611 := bstep (se 1 (by rfl) ⟨1372958, by rfl⟩ : syracuseStep 1830611 = 2745917) B2745917
theorem B2059987 : Blo 1829616 2059987 := bstep (se 1 (by rfl) ⟨1544990, by rfl⟩ : syracuseStep 2059987 = 3089981) B3089981
theorem B1830627 : Blo 1829616 1830627 := bstep (se 1 (by rfl) ⟨1372970, by rfl⟩ : syracuseStep 1830627 = 2745941) B2745941
theorem B1830643 : Blo 1829616 1830643 := bstep (se 1 (by rfl) ⟨1372982, by rfl⟩ : syracuseStep 1830643 = 2745965) B2745965
theorem B1830659 : Blo 1829616 1830659 := bstep (se 1 (by rfl) ⟨1372994, by rfl⟩ : syracuseStep 1830659 = 2745989) B2745989
theorem B1830675 : Blo 1829616 1830675 := bstep (se 1 (by rfl) ⟨1373006, by rfl⟩ : syracuseStep 1830675 = 2746013) B2746013
theorem B1830691 : Blo 1829616 1830691 := bstep (se 1 (by rfl) ⟨1373018, by rfl⟩ : syracuseStep 1830691 = 2746037) B2746037
theorem B1830707 : Blo 1829616 1830707 := bstep (se 1 (by rfl) ⟨1373030, by rfl⟩ : syracuseStep 1830707 = 2746061) B2746061
theorem B1830723 : Blo 1829616 1830723 := bstep (se 1 (by rfl) ⟨1373042, by rfl⟩ : syracuseStep 1830723 = 2746085) B2746085
theorem B1830739 : Blo 1829616 1830739 := bstep (se 1 (by rfl) ⟨1373054, by rfl⟩ : syracuseStep 1830739 = 2746109) B2746109
theorem B1830755 : Blo 1829616 1830755 := bstep (se 1 (by rfl) ⟨1373066, by rfl⟩ : syracuseStep 1830755 = 2746133) B2746133
theorem B2060131 : Blo 1829616 2060131 := bstep (se 1 (by rfl) ⟨1545098, by rfl⟩ : syracuseStep 2060131 = 3090197) B3090197
theorem B1830771 : Blo 1829616 1830771 := bstep (se 1 (by rfl) ⟨1373078, by rfl⟩ : syracuseStep 1830771 = 2746157) B2746157
theorem B1830787 : Blo 1829616 1830787 := bstep (se 1 (by rfl) ⟨1373090, by rfl⟩ : syracuseStep 1830787 = 2746181) B2746181
theorem B1830803 : Blo 1829616 1830803 := bstep (se 1 (by rfl) ⟨1373102, by rfl⟩ : syracuseStep 1830803 = 2746205) B2746205
theorem B1830819 : Blo 1829616 1830819 := bstep (se 1 (by rfl) ⟨1373114, by rfl⟩ : syracuseStep 1830819 = 2746229) B2746229
theorem B6180785 : Blo 1829616 6180785 := bstep (se 2 (by rfl) ⟨2317794, by rfl⟩ : syracuseStep 6180785 = 4635589) B4635589
theorem B1830835 : Blo 1829616 1830835 := bstep (se 1 (by rfl) ⟨1373126, by rfl⟩ : syracuseStep 1830835 = 2746253) B2746253
theorem B1830851 : Blo 1829616 1830851 := bstep (se 1 (by rfl) ⟨1373138, by rfl⟩ : syracuseStep 1830851 = 2746277) B2746277
theorem B1830867 : Blo 1829616 1830867 := bstep (se 1 (by rfl) ⟨1373150, by rfl⟩ : syracuseStep 1830867 = 2746301) B2746301
theorem B1830883 : Blo 1829616 1830883 := bstep (se 1 (by rfl) ⟨1373162, by rfl⟩ : syracuseStep 1830883 = 2746325) B2746325
theorem B7426019 : Blo 1829616 7426019 := bstep (se 1 (by rfl) ⟨5569514, by rfl⟩ : syracuseStep 7426019 = 11139029) B11139029
theorem B1830899 : Blo 1829616 1830899 := bstep (se 1 (by rfl) ⟨1373174, by rfl⟩ : syracuseStep 1830899 = 2746349) B2746349
theorem B2060275 : Blo 1829616 2060275 := bstep (se 1 (by rfl) ⟨1545206, by rfl⟩ : syracuseStep 2060275 = 3090413) B3090413
theorem B1830915 : Blo 1829616 1830915 := bstep (se 1 (by rfl) ⟨1373186, by rfl⟩ : syracuseStep 1830915 = 2746373) B2746373
theorem B1830931 : Blo 1829616 1830931 := bstep (se 1 (by rfl) ⟨1373198, by rfl⟩ : syracuseStep 1830931 = 2746397) B2746397
theorem B45117461 : Blo 1829616 45117461 := bstep (se 6 (by rfl) ⟨1057440, by rfl⟩ : syracuseStep 45117461 = 2114881) B2114881
theorem B1830947 : Blo 1829616 1830947 := bstep (se 1 (by rfl) ⟨1373210, by rfl⟩ : syracuseStep 1830947 = 2746421) B2746421
theorem B5214253 : Blo 1829616 5214253 := bstep (se 3 (by rfl) ⟨977672, by rfl⟩ : syracuseStep 5214253 = 1955345) B1955345
theorem B1830963 : Blo 1829616 1830963 := bstep (se 1 (by rfl) ⟨1373222, by rfl⟩ : syracuseStep 1830963 = 2746445) B2746445
theorem B1830979 : Blo 1829616 1830979 := bstep (se 1 (by rfl) ⟨1373234, by rfl⟩ : syracuseStep 1830979 = 2746469) B2746469
theorem B3297361 : Blo 1829616 3297361 := bstep (se 2 (by rfl) ⟨1236510, by rfl⟩ : syracuseStep 3297361 = 2473021) B2473021
theorem B1830995 : Blo 1829616 1830995 := bstep (se 1 (by rfl) ⟨1373246, by rfl⟩ : syracuseStep 1830995 = 2746493) B2746493
theorem B1831011 : Blo 1829616 1831011 := bstep (se 1 (by rfl) ⟨1373258, by rfl⟩ : syracuseStep 1831011 = 2746517) B2746517
theorem B26382449 : Blo 1829616 26382449 := bstep (se 2 (by rfl) ⟨9893418, by rfl⟩ : syracuseStep 26382449 = 19786837) B19786837
theorem B1831027 : Blo 1829616 1831027 := bstep (se 1 (by rfl) ⟨1373270, by rfl⟩ : syracuseStep 1831027 = 2746541) B2746541
theorem B1831043 : Blo 1829616 1831043 := bstep (se 1 (by rfl) ⟨1373282, by rfl⟩ : syracuseStep 1831043 = 2746565) B2746565
theorem B2060419 : Blo 1829616 2060419 := bstep (se 1 (by rfl) ⟨1545314, by rfl⟩ : syracuseStep 2060419 = 3090629) B3090629
theorem B3174547 : Blo 1829616 3174547 := bstep (se 1 (by rfl) ⟨2380910, by rfl⟩ : syracuseStep 3174547 = 4761821) B4761821
theorem B1831059 : Blo 1829616 1831059 := bstep (se 1 (by rfl) ⟨1373294, by rfl⟩ : syracuseStep 1831059 = 2746589) B2746589
theorem B1831075 : Blo 1829616 1831075 := bstep (se 1 (by rfl) ⟨1373306, by rfl⟩ : syracuseStep 1831075 = 2746613) B2746613
theorem B1831091 : Blo 1829616 1831091 := bstep (se 1 (by rfl) ⟨1373318, by rfl⟩ : syracuseStep 1831091 = 2746637) B2746637
theorem B1831107 : Blo 1829616 1831107 := bstep (se 1 (by rfl) ⟨1373330, by rfl⟩ : syracuseStep 1831107 = 2746661) B2746661
theorem B4116689 : Blo 1829616 4116689 := bstep (se 2 (by rfl) ⟨1543758, by rfl⟩ : syracuseStep 4116689 = 3087517) B3087517
theorem B4632785 : Blo 1829616 4632785 := bstep (se 2 (by rfl) ⟨1737294, by rfl⟩ : syracuseStep 4632785 = 3474589) B3474589
theorem B1831123 : Blo 1829616 1831123 := bstep (se 1 (by rfl) ⟨1373342, by rfl⟩ : syracuseStep 1831123 = 2746685) B2746685
theorem B4116707 : Blo 1829616 4116707 := bstep (se 1 (by rfl) ⟨3087530, by rfl⟩ : syracuseStep 4116707 = 6175061) B6175061
theorem B1831139 : Blo 1829616 1831139 := bstep (se 1 (by rfl) ⟨1373354, by rfl⟩ : syracuseStep 1831139 = 2746709) B2746709
theorem B1831155 : Blo 1829616 1831155 := bstep (se 1 (by rfl) ⟨1373366, by rfl⟩ : syracuseStep 1831155 = 2746733) B2746733
theorem B4632835 : Blo 1829616 4632835 := bstep (se 1 (by rfl) ⟨3474626, by rfl⟩ : syracuseStep 4632835 = 6949253) B6949253
theorem B1855747 : Blo 1829616 1855747 := bstep (se 1 (by rfl) ⟨1391810, by rfl⟩ : syracuseStep 1855747 = 2783621) B2783621
theorem B1831171 : Blo 1829616 1831171 := bstep (se 1 (by rfl) ⟨1373378, by rfl⟩ : syracuseStep 1831171 = 2746757) B2746757
theorem B17150221 : Blo 1829616 17150221 := bstep (se 3 (by rfl) ⟨3215666, by rfl⟩ : syracuseStep 17150221 = 6431333) B6431333
theorem B1831187 : Blo 1829616 1831187 := bstep (se 1 (by rfl) ⟨1373390, by rfl⟩ : syracuseStep 1831187 = 2746781) B2746781
theorem B2060563 : Blo 1829616 2060563 := bstep (se 1 (by rfl) ⟨1545422, by rfl⟩ : syracuseStep 2060563 = 3090845) B3090845
theorem B1831203 : Blo 1829616 1831203 := bstep (se 1 (by rfl) ⟨1373402, by rfl⟩ : syracuseStep 1831203 = 2746805) B2746805
theorem B1855795 : Blo 1829616 1855795 := bstep (se 1 (by rfl) ⟨1391846, by rfl⟩ : syracuseStep 1855795 = 2783693) B2783693
theorem B1831219 : Blo 1829616 1831219 := bstep (se 1 (by rfl) ⟨1373414, by rfl⟩ : syracuseStep 1831219 = 2746829) B2746829
theorem B1831235 : Blo 1829616 1831235 := bstep (se 1 (by rfl) ⟨1373426, by rfl⟩ : syracuseStep 1831235 = 2746853) B2746853
theorem B11727173 : Blo 1829616 11727173 := bstep (se 4 (by rfl) ⟨1099422, by rfl⟩ : syracuseStep 11727173 = 2198845) B2198845
theorem B1831251 : Blo 1829616 1831251 := bstep (se 1 (by rfl) ⟨1373438, by rfl⟩ : syracuseStep 1831251 = 2746877) B2746877
theorem B1831267 : Blo 1829616 1831267 := bstep (se 1 (by rfl) ⟨1373450, by rfl⟩ : syracuseStep 1831267 = 2746901) B2746901
theorem B1831283 : Blo 1829616 1831283 := bstep (se 1 (by rfl) ⟨1373462, by rfl⟩ : syracuseStep 1831283 = 2746925) B2746925
theorem B1831299 : Blo 1829616 1831299 := bstep (se 1 (by rfl) ⟨1373474, by rfl⟩ : syracuseStep 1831299 = 2746949) B2746949
theorem B4632977 : Blo 1829616 4632977 := bstep (se 2 (by rfl) ⟨1737366, by rfl⟩ : syracuseStep 4632977 = 3474733) B3474733
theorem B1831315 : Blo 1829616 1831315 := bstep (se 1 (by rfl) ⟨1373486, by rfl⟩ : syracuseStep 1831315 = 2746973) B2746973
theorem B1831331 : Blo 1829616 1831331 := bstep (se 1 (by rfl) ⟨1373498, by rfl⟩ : syracuseStep 1831331 = 2746997) B2746997
theorem B1831347 : Blo 1829616 1831347 := bstep (se 1 (by rfl) ⟨1373510, by rfl⟩ : syracuseStep 1831347 = 2747021) B2747021
theorem B1831363 : Blo 1829616 1831363 := bstep (se 1 (by rfl) ⟨1373522, by rfl⟩ : syracuseStep 1831363 = 2747045) B2747045
theorem B6181325 : Blo 1829616 6181325 := bstep (se 3 (by rfl) ⟨1158998, by rfl⟩ : syracuseStep 6181325 = 2317997) B2317997
theorem B1831379 : Blo 1829616 1831379 := bstep (se 1 (by rfl) ⟨1373534, by rfl⟩ : syracuseStep 1831379 = 2747069) B2747069
theorem B8794595 : Blo 1829616 8794595 := bstep (se 1 (by rfl) ⟨6595946, by rfl⟩ : syracuseStep 8794595 = 13191893) B13191893
theorem B13906403 : Blo 1829616 13906403 := bstep (se 1 (by rfl) ⟨10429802, by rfl⟩ : syracuseStep 13906403 = 20859605) B20859605
theorem B1831395 : Blo 1829616 1831395 := bstep (se 1 (by rfl) ⟨1373546, by rfl⟩ : syracuseStep 1831395 = 2747093) B2747093
theorem B4116977 : Blo 1829616 4116977 := bstep (se 2 (by rfl) ⟨1543866, by rfl⟩ : syracuseStep 4116977 = 3087733) B3087733
theorem B1831411 : Blo 1829616 1831411 := bstep (se 1 (by rfl) ⟨1373558, by rfl⟩ : syracuseStep 1831411 = 2747117) B2747117
theorem B4116995 : Blo 1829616 4116995 := bstep (se 1 (by rfl) ⟨3087746, by rfl⟩ : syracuseStep 4116995 = 6175493) B6175493
theorem B1954307 : Blo 1829616 1954307 := bstep (se 1 (by rfl) ⟨1465730, by rfl⟩ : syracuseStep 1954307 = 2931461) B2931461
theorem B1831427 : Blo 1829616 1831427 := bstep (se 1 (by rfl) ⟨1373570, by rfl⟩ : syracuseStep 1831427 = 2747141) B2747141
theorem B6181379 : Blo 1829616 6181379 := bstep (se 1 (by rfl) ⟨4636034, by rfl⟩ : syracuseStep 6181379 = 9272069) B9272069
theorem B1831443 : Blo 1829616 1831443 := bstep (se 1 (by rfl) ⟨1373582, by rfl⟩ : syracuseStep 1831443 = 2747165) B2747165
theorem B1831459 : Blo 1829616 1831459 := bstep (se 1 (by rfl) ⟨1373594, by rfl⟩ : syracuseStep 1831459 = 2747189) B2747189
theorem B1831475 : Blo 1829616 1831475 := bstep (se 1 (by rfl) ⟨1373606, by rfl⟩ : syracuseStep 1831475 = 2747213) B2747213
theorem B1831491 : Blo 1829616 1831491 := bstep (se 1 (by rfl) ⟨1373618, by rfl⟩ : syracuseStep 1831491 = 2747237) B2747237
theorem B1831507 : Blo 1829616 1831507 := bstep (se 1 (by rfl) ⟨1373630, by rfl⟩ : syracuseStep 1831507 = 2747261) B2747261
theorem B1831523 : Blo 1829616 1831523 := bstep (se 1 (by rfl) ⟨1373642, by rfl⟩ : syracuseStep 1831523 = 2747285) B2747285
theorem B1831539 : Blo 1829616 1831539 := bstep (se 1 (by rfl) ⟨1373654, by rfl⟩ : syracuseStep 1831539 = 2747309) B2747309
theorem B1831555 : Blo 1829616 1831555 := bstep (se 1 (by rfl) ⟨1373666, by rfl⟩ : syracuseStep 1831555 = 2747333) B2747333
theorem B3297937 : Blo 1829616 3297937 := bstep (se 2 (by rfl) ⟨1236726, by rfl⟩ : syracuseStep 3297937 = 2473453) B2473453
theorem B1831571 : Blo 1829616 1831571 := bstep (se 1 (by rfl) ⟨1373678, by rfl⟩ : syracuseStep 1831571 = 2747357) B2747357
theorem B1831587 : Blo 1829616 1831587 := bstep (se 1 (by rfl) ⟨1373690, by rfl⟩ : syracuseStep 1831587 = 2747381) B2747381
theorem B1831603 : Blo 1829616 1831603 := bstep (se 1 (by rfl) ⟨1373702, by rfl⟩ : syracuseStep 1831603 = 2747405) B2747405
theorem B4117265 : Blo 1829616 4117265 := bstep (se 2 (by rfl) ⟨1543974, by rfl⟩ : syracuseStep 4117265 = 3087949) B3087949
theorem B6181649 : Blo 1829616 6181649 := bstep (se 2 (by rfl) ⟨2318118, by rfl⟩ : syracuseStep 6181649 = 4636237) B4636237
theorem B4117283 : Blo 1829616 4117283 := bstep (se 1 (by rfl) ⟨3087962, by rfl⟩ : syracuseStep 4117283 = 6175925) B6175925
theorem B22262627 : Blo 1829616 22262627 := bstep (se 1 (by rfl) ⟨16696970, by rfl⟩ : syracuseStep 22262627 = 33393941) B33393941
theorem B10572707 : Blo 1829616 10572707 := bstep (se 1 (by rfl) ⟨7929530, by rfl⟩ : syracuseStep 10572707 = 15859061) B15859061
theorem B10425293 : Blo 1829616 10425293 := bstep (se 3 (by rfl) ⟨1954742, by rfl⟩ : syracuseStep 10425293 = 3909485) B3909485
theorem B10572749 : Blo 1829616 10572749 := bstep (se 3 (by rfl) ⟨1982390, by rfl⟩ : syracuseStep 10572749 = 3964781) B3964781
theorem B18789347 : Blo 1829616 18789347 := bstep (se 1 (by rfl) ⟨14092010, by rfl⟩ : syracuseStep 18789347 = 28184021) B28184021
theorem B20853773 : Blo 1829616 20853773 := bstep (se 3 (by rfl) ⟨3910082, by rfl⟩ : syracuseStep 20853773 = 7820165) B7820165
theorem B4117553 : Blo 1829616 4117553 := bstep (se 2 (by rfl) ⟨1544082, by rfl⟩ : syracuseStep 4117553 = 3088165) B3088165
theorem B4117571 : Blo 1829616 4117571 := bstep (se 1 (by rfl) ⟨3088178, by rfl⟩ : syracuseStep 4117571 = 6176357) B6176357
theorem B6263885 : Blo 1829616 6263885 := bstep (se 3 (by rfl) ⟨1174478, by rfl⟩ : syracuseStep 6263885 = 2348957) B2348957
theorem B9270449 : Blo 1829616 9270449 := bstep (se 2 (by rfl) ⟨3476418, by rfl⟩ : syracuseStep 9270449 = 6952837) B6952837
theorem B3298499 : Blo 1829616 3298499 := bstep (se 1 (by rfl) ⟨2473874, by rfl⟩ : syracuseStep 3298499 = 4947749) B4947749
theorem B4117841 : Blo 1829616 4117841 := bstep (se 2 (by rfl) ⟨1544190, by rfl⟩ : syracuseStep 4117841 = 3088381) B3088381
theorem B5862755 : Blo 1829616 5862755 := bstep (se 1 (by rfl) ⟨4397066, by rfl⟩ : syracuseStep 5862755 = 8794133) B8794133
theorem B4117859 : Blo 1829616 4117859 := bstep (se 1 (by rfl) ⟨3088394, by rfl⟩ : syracuseStep 4117859 = 6176789) B6176789
theorem B4633969 : Blo 1829616 4633969 := bstep (se 2 (by rfl) ⟨1737738, by rfl⟩ : syracuseStep 4633969 = 3475477) B3475477
theorem B3298787 : Blo 1829616 3298787 := bstep (se 1 (by rfl) ⟨2474090, by rfl⟩ : syracuseStep 3298787 = 4948181) B4948181
theorem B7820849 : Blo 1829616 7820849 := bstep (se 2 (by rfl) ⟨2932818, by rfl⟩ : syracuseStep 7820849 = 5865637) B5865637
theorem B35182133 : Blo 1829616 35182133 := bstep (se 5 (by rfl) ⟨1649162, by rfl⟩ : syracuseStep 35182133 = 3298325) B3298325
theorem B4118129 : Blo 1829616 4118129 := bstep (se 2 (by rfl) ⟨1544298, by rfl⟩ : syracuseStep 4118129 = 3088597) B3088597
theorem B2315891 : Blo 1829616 2315891 := bstep (se 1 (by rfl) ⟨1736918, by rfl⟩ : syracuseStep 2315891 = 3473837) B3473837
theorem B4118147 : Blo 1829616 4118147 := bstep (se 1 (by rfl) ⟨3088610, by rfl⟩ : syracuseStep 4118147 = 6177221) B6177221
theorem B4634243 : Blo 1829616 4634243 := bstep (se 1 (by rfl) ⟨3475682, by rfl⟩ : syracuseStep 4634243 = 6951365) B6951365
theorem B3298961 : Blo 1829616 3298961 := bstep (se 2 (by rfl) ⟨1237110, by rfl⟩ : syracuseStep 3298961 = 2474221) B2474221
theorem B4945585 : Blo 1829616 4945585 := bstep (se 2 (by rfl) ⟨1854594, by rfl⟩ : syracuseStep 4945585 = 3709189) B3709189
theorem B6952625 : Blo 1829616 6952625 := bstep (se 2 (by rfl) ⟨2607234, by rfl⟩ : syracuseStep 6952625 = 5214469) B5214469
theorem B6346435 : Blo 1829616 6346435 := bstep (se 1 (by rfl) ⟨4759826, by rfl⟩ : syracuseStep 6346435 = 9519653) B9519653
theorem B4634435 : Blo 1829616 4634435 := bstep (se 1 (by rfl) ⟨3475826, by rfl⟩ : syracuseStep 4634435 = 6951653) B6951653
theorem B4396913 : Blo 1829616 4396913 := bstep (se 2 (by rfl) ⟨1648842, by rfl⟩ : syracuseStep 4396913 = 3297685) B3297685
theorem B4118417 : Blo 1829616 4118417 := bstep (se 2 (by rfl) ⟨1544406, by rfl⟩ : syracuseStep 4118417 = 3088813) B3088813
theorem B4118435 : Blo 1829616 4118435 := bstep (se 1 (by rfl) ⟨3088826, by rfl⟩ : syracuseStep 4118435 = 6177653) B6177653
theorem B21419957 : Blo 1829616 21419957 := bstep (se 5 (by rfl) ⟨1004060, by rfl⟩ : syracuseStep 21419957 = 2008121) B2008121
theorem B6600689 : Blo 1829616 6600689 := bstep (se 2 (by rfl) ⟨2475258, by rfl⟩ : syracuseStep 6600689 = 4950517) B4950517
theorem B3962947 : Blo 1829616 3962947 := bstep (se 1 (by rfl) ⟨2972210, by rfl⟩ : syracuseStep 3962947 = 5944421) B5944421
theorem B1980499 : Blo 1829616 1980499 := bstep (se 1 (by rfl) ⟨1485374, by rfl⟩ : syracuseStep 1980499 = 2970749) B2970749
theorem B2930833 : Blo 1829616 2930833 := bstep (se 2 (by rfl) ⟨1099062, by rfl⟩ : syracuseStep 2930833 = 2198125) B2198125
theorem B2087059 : Blo 1829616 2087059 := bstep (se 1 (by rfl) ⟨1565294, by rfl⟩ : syracuseStep 2087059 = 3130589) B3130589
theorem B4118705 : Blo 1829616 4118705 := bstep (se 2 (by rfl) ⟨1544514, by rfl⟩ : syracuseStep 4118705 = 3089029) B3089029
theorem B2783425 : Blo 1829616 2783425 := bstep (se 2 (by rfl) ⟨1043784, by rfl⟩ : syracuseStep 2783425 = 2087569) B2087569
theorem B4118723 : Blo 1829616 4118723 := bstep (se 1 (by rfl) ⟨3089042, by rfl⟩ : syracuseStep 4118723 = 6178085) B6178085
theorem B2930897 : Blo 1829616 2930897 := bstep (se 2 (by rfl) ⟨1099086, by rfl⟩ : syracuseStep 2930897 = 2198173) B2198173
theorem B11729123 : Blo 1829616 11729123 := bstep (se 1 (by rfl) ⟨8796842, by rfl⟩ : syracuseStep 11729123 = 17593685) B17593685
theorem B2316595 : Blo 1829616 2316595 := bstep (se 1 (by rfl) ⟨1737446, by rfl⟩ : syracuseStep 2316595 = 3474893) B3474893
theorem B8345969 : Blo 1829616 8345969 := bstep (se 2 (by rfl) ⟨3129738, by rfl⟩ : syracuseStep 8345969 = 6259477) B6259477
theorem B2316691 : Blo 1829616 2316691 := bstep (se 1 (by rfl) ⟨1737518, by rfl⟩ : syracuseStep 2316691 = 3475037) B3475037
theorem B5863843 : Blo 1829616 5863843 := bstep (se 1 (by rfl) ⟨4397882, by rfl⟩ : syracuseStep 5863843 = 8795765) B8795765
theorem B8796593 : Blo 1829616 8796593 := bstep (se 2 (by rfl) ⟨3298722, by rfl⟩ : syracuseStep 8796593 = 6597445) B6597445
theorem B4118993 : Blo 1829616 4118993 := bstep (se 2 (by rfl) ⟨1544622, by rfl⟩ : syracuseStep 4118993 = 3089245) B3089245
theorem B4119011 : Blo 1829616 4119011 := bstep (se 1 (by rfl) ⟨3089258, by rfl⟩ : syracuseStep 4119011 = 6178517) B6178517
theorem B3299825 : Blo 1829616 3299825 := bstep (se 2 (by rfl) ⟨1237434, by rfl⟩ : syracuseStep 3299825 = 2474869) B2474869
theorem B6175277 : Blo 1829616 6175277 := bstep (se 3 (by rfl) ⟨1157864, by rfl⟩ : syracuseStep 6175277 = 2315729) B2315729
theorem B5863985 : Blo 1829616 5863985 := bstep (se 2 (by rfl) ⟨2198994, by rfl⟩ : syracuseStep 5863985 = 4397989) B4397989
theorem B6175331 : Blo 1829616 6175331 := bstep (se 1 (by rfl) ⟨4631498, by rfl⟩ : syracuseStep 6175331 = 9262997) B9262997
theorem B9271907 : Blo 1829616 9271907 := bstep (se 1 (by rfl) ⟨6953930, by rfl⟩ : syracuseStep 9271907 = 13907861) B13907861
theorem B4119281 : Blo 1829616 4119281 := bstep (se 2 (by rfl) ⟨1544730, by rfl⟩ : syracuseStep 4119281 = 3089461) B3089461
theorem B4635377 : Blo 1829616 4635377 := bstep (se 2 (by rfl) ⟨1738266, by rfl⟩ : syracuseStep 4635377 = 3476533) B3476533
theorem B4119299 : Blo 1829616 4119299 := bstep (se 1 (by rfl) ⟨3089474, by rfl⟩ : syracuseStep 4119299 = 6178949) B6178949
theorem B3300113 : Blo 1829616 3300113 := bstep (se 2 (by rfl) ⟨1237542, by rfl⟩ : syracuseStep 3300113 = 2475085) B2475085
theorem B7822115 : Blo 1829616 7822115 := bstep (se 1 (by rfl) ⟨5866586, by rfl⟩ : syracuseStep 7822115 = 11733173) B11733173
theorem B4635427 : Blo 1829616 4635427 := bstep (se 1 (by rfl) ⟨3476570, by rfl⟩ : syracuseStep 4635427 = 6953141) B6953141
theorem B6175601 : Blo 1829616 6175601 := bstep (se 2 (by rfl) ⟨2315850, by rfl⟩ : syracuseStep 6175601 = 4631701) B4631701
theorem B2317187 : Blo 1829616 2317187 := bstep (se 1 (by rfl) ⟨1737890, by rfl⟩ : syracuseStep 2317187 = 3475781) B3475781
theorem B4635569 : Blo 1829616 4635569 := bstep (se 2 (by rfl) ⟨1738338, by rfl⟩ : syracuseStep 4635569 = 3476677) B3476677
theorem B4119569 : Blo 1829616 4119569 := bstep (se 2 (by rfl) ⟨1544838, by rfl⟩ : syracuseStep 4119569 = 3089677) B3089677
theorem B4119587 : Blo 1829616 4119587 := bstep (se 1 (by rfl) ⟨3089690, by rfl⟩ : syracuseStep 4119587 = 6179381) B6179381
theorem B6954083 : Blo 1829616 6954083 := bstep (se 1 (by rfl) ⟨5215562, by rfl⟩ : syracuseStep 6954083 = 10431125) B10431125
theorem B10427525 : Blo 1829616 10427525 := bstep (se 4 (by rfl) ⟨977580, by rfl⟩ : syracuseStep 10427525 = 1955161) B1955161
theorem B3087571 : Blo 1829616 3087571 := bstep (se 1 (by rfl) ⟨2315678, by rfl⟩ : syracuseStep 3087571 = 4631357) B4631357
theorem B4119857 : Blo 1829616 4119857 := bstep (se 2 (by rfl) ⟨1544946, by rfl⟩ : syracuseStep 4119857 = 3089893) B3089893
theorem B4119875 : Blo 1829616 4119875 := bstep (se 1 (by rfl) ⟨3089906, by rfl⟩ : syracuseStep 4119875 = 6179813) B6179813
theorem B20847941 : Blo 1829616 20847941 := bstep (se 4 (by rfl) ⟨1954494, by rfl⟩ : syracuseStep 20847941 = 3908989) B3908989
theorem B11132237 : Blo 1829616 11132237 := bstep (se 3 (by rfl) ⟨2087294, by rfl⟩ : syracuseStep 11132237 = 4174589) B4174589
theorem B8797517 : Blo 1829616 8797517 := bstep (se 3 (by rfl) ⟨1649534, by rfl⟩ : syracuseStep 8797517 = 3299069) B3299069
theorem B3521873 : Blo 1829616 3521873 := bstep (se 2 (by rfl) ⟨1320702, by rfl⟩ : syracuseStep 3521873 = 2641405) B2641405
theorem B3087713 : Blo 1829616 3087713 := bstep (se 2 (by rfl) ⟨1157892, by rfl⟩ : syracuseStep 3087713 = 2315785) B2315785
theorem B6176141 : Blo 1829616 6176141 := bstep (se 3 (by rfl) ⟨1158026, by rfl⟩ : syracuseStep 6176141 = 2316053) B2316053
theorem B6176195 : Blo 1829616 6176195 := bstep (se 1 (by rfl) ⟨4632146, by rfl⟩ : syracuseStep 6176195 = 9264293) B9264293
theorem B3087841 : Blo 1829616 3087841 := bstep (se 2 (by rfl) ⟨1157940, by rfl⟩ : syracuseStep 3087841 = 2315881) B2315881
theorem B3087875 : Blo 1829616 3087875 := bstep (se 1 (by rfl) ⟨2315906, by rfl⟩ : syracuseStep 3087875 = 4631813) B4631813
theorem B2317891 : Blo 1829616 2317891 := bstep (se 1 (by rfl) ⟨1738418, by rfl⟩ : syracuseStep 2317891 = 3476837) B3476837
theorem B4120145 : Blo 1829616 4120145 := bstep (se 2 (by rfl) ⟨1545054, by rfl⟩ : syracuseStep 4120145 = 3090109) B3090109
theorem B4120163 : Blo 1829616 4120163 := bstep (se 1 (by rfl) ⟨3090122, by rfl⟩ : syracuseStep 4120163 = 6180245) B6180245
theorem B3088003 : Blo 1829616 3088003 := bstep (se 1 (by rfl) ⟨2316002, by rfl⟩ : syracuseStep 3088003 = 4632005) B4632005
theorem B2317987 : Blo 1829616 2317987 := bstep (se 1 (by rfl) ⟨1738490, by rfl⟩ : syracuseStep 2317987 = 3476981) B3476981
theorem B20061893 : Blo 1829616 20061893 := bstep (se 4 (by rfl) ⟨1880802, by rfl⟩ : syracuseStep 20061893 = 3761605) B3761605
theorem B6176465 : Blo 1829616 6176465 := bstep (se 2 (by rfl) ⟨2316174, by rfl⟩ : syracuseStep 6176465 = 4632349) B4632349
theorem B15040241 : Blo 1829616 15040241 := bstep (se 2 (by rfl) ⟨5640090, by rfl⟩ : syracuseStep 15040241 = 11280181) B11280181
theorem B3088145 : Blo 1829616 3088145 := bstep (se 2 (by rfl) ⟨1158054, by rfl⟩ : syracuseStep 3088145 = 2316109) B2316109
theorem B42295061 : Blo 1829616 42295061 := bstep (se 6 (by rfl) ⟨991290, by rfl⟩ : syracuseStep 42295061 = 1982581) B1982581
theorem B8347427 : Blo 1829616 8347427 := bstep (se 1 (by rfl) ⟨6260570, by rfl⟩ : syracuseStep 8347427 = 12521141) B12521141
theorem B10428209 : Blo 1829616 10428209 := bstep (se 2 (by rfl) ⟨3910578, by rfl⟩ : syracuseStep 10428209 = 7821157) B7821157
theorem B13188977 : Blo 1829616 13188977 := bstep (se 2 (by rfl) ⟨4945866, by rfl⟩ : syracuseStep 13188977 = 9891733) B9891733
theorem B5865329 : Blo 1829616 5865329 := bstep (se 2 (by rfl) ⟨2199498, by rfl⟩ : syracuseStep 5865329 = 4398997) B4398997
theorem B20856689 : Blo 1829616 20856689 := bstep (se 2 (by rfl) ⟨7821258, by rfl⟩ : syracuseStep 20856689 = 15642517) B15642517
theorem B4120433 : Blo 1829616 4120433 := bstep (se 2 (by rfl) ⟨1545162, by rfl⟩ : syracuseStep 4120433 = 3090325) B3090325
theorem B4120451 : Blo 1829616 4120451 := bstep (se 1 (by rfl) ⟨3090338, by rfl⟩ : syracuseStep 4120451 = 6180677) B6180677
theorem B3088273 : Blo 1829616 3088273 := bstep (se 2 (by rfl) ⟨1158102, by rfl⟩ : syracuseStep 3088273 = 2316205) B2316205
theorem B2932627 : Blo 1829616 2932627 := bstep (se 1 (by rfl) ⟨2199470, by rfl⟩ : syracuseStep 2932627 = 4398941) B4398941
theorem B3088307 : Blo 1829616 3088307 := bstep (se 1 (by rfl) ⟨2316230, by rfl⟩ : syracuseStep 3088307 = 4632461) B4632461
theorem B4120577 : Blo 1829616 4120577 := bstep (se 2 (by rfl) ⟨1545216, by rfl⟩ : syracuseStep 4120577 = 3090433) B3090433
theorem B17588299 : Blo 1829616 17588299 := bstep (se 1 (by rfl) ⟨13191224, by rfl⟩ : syracuseStep 17588299 = 26382449) B26382449
theorem B6176843 : Blo 1829616 6176843 := bstep (se 1 (by rfl) ⟨4632632, by rfl⟩ : syracuseStep 6176843 = 9265265) B9265265
theorem B2474059 : Blo 1829616 2474059 := bstep (se 1 (by rfl) ⟨1855544, by rfl⟩ : syracuseStep 2474059 = 3711089) B3711089
theorem B5283929 : Blo 1829616 5283929 := bstep (se 2 (by rfl) ⟨1981473, by rfl⟩ : syracuseStep 5283929 = 3962947) B3962947
theorem B2744459 : Blo 1829616 2744459 := bstep (se 1 (by rfl) ⟨2058344, by rfl⟩ : syracuseStep 2744459 = 4116689) B4116689
theorem B3088523 : Blo 1829616 3088523 := bstep (se 1 (by rfl) ⟨2316392, by rfl⟩ : syracuseStep 3088523 = 4632785) B4632785
theorem B2744471 : Blo 1829616 2744471 := bstep (se 1 (by rfl) ⟨2058353, by rfl⟩ : syracuseStep 2744471 = 4116707) B4116707
theorem B3907777 : Blo 1829616 3907777 := bstep (se 2 (by rfl) ⟨1465416, by rfl⟩ : syracuseStep 3907777 = 2930833) B2930833
theorem B13902029 : Blo 1829616 13902029 := bstep (se 3 (by rfl) ⟨2606630, by rfl⟩ : syracuseStep 13902029 = 5213261) B5213261
theorem B2744537 : Blo 1829616 2744537 := bstep (se 2 (by rfl) ⟨1029201, by rfl⟩ : syracuseStep 2744537 = 2058403) B2058403
theorem B5865689 : Blo 1829616 5865689 := bstep (se 2 (by rfl) ⟨2199633, by rfl⟩ : syracuseStep 5865689 = 4399267) B4399267
theorem B4120793 : Blo 1829616 4120793 := bstep (se 2 (by rfl) ⟨1545297, by rfl⟩ : syracuseStep 4120793 = 3090595) B3090595
theorem B5357789 : Blo 1829616 5357789 := bstep (se 3 (by rfl) ⟨1004585, by rfl⟩ : syracuseStep 5357789 = 2009171) B2009171
theorem B3711233 : Blo 1829616 3711233 := bstep (se 2 (by rfl) ⟨1391712, by rfl⟩ : syracuseStep 3711233 = 2783425) B2783425
theorem B3088651 : Blo 1829616 3088651 := bstep (se 1 (by rfl) ⟨2316488, by rfl⟩ : syracuseStep 3088651 = 4632977) B4632977
theorem B4120883 : Blo 1829616 4120883 := bstep (se 1 (by rfl) ⟨3090662, by rfl⟩ : syracuseStep 4120883 = 6181325) B6181325
theorem B2744651 : Blo 1829616 2744651 := bstep (se 1 (by rfl) ⟨2058488, by rfl⟩ : syracuseStep 2744651 = 4116977) B4116977
theorem B2744663 : Blo 1829616 2744663 := bstep (se 1 (by rfl) ⟨2058497, by rfl⟩ : syracuseStep 2744663 = 4116995) B4116995
theorem B4120919 : Blo 1829616 4120919 := bstep (se 1 (by rfl) ⟨3090689, by rfl⟩ : syracuseStep 4120919 = 6181379) B6181379
theorem B6177113 : Blo 1829616 6177113 := bstep (se 2 (by rfl) ⟨2316417, by rfl⟩ : syracuseStep 6177113 = 4632835) B4632835
theorem B2474329 : Blo 1829616 2474329 := bstep (se 2 (by rfl) ⟨927873, by rfl⟩ : syracuseStep 2474329 = 1855747) B1855747
theorem B2744729 : Blo 1829616 2744729 := bstep (se 2 (by rfl) ⟨1029273, by rfl⟩ : syracuseStep 2744729 = 2058547) B2058547
theorem B3088793 : Blo 1829616 3088793 := bstep (se 2 (by rfl) ⟨1158297, by rfl⟩ : syracuseStep 3088793 = 2316595) B2316595
theorem B2474393 : Blo 1829616 2474393 := bstep (se 2 (by rfl) ⟨927897, by rfl⟩ : syracuseStep 2474393 = 1855795) B1855795
theorem B3473867 : Blo 1829616 3473867 := bstep (se 1 (by rfl) ⟨2605400, by rfl⟩ : syracuseStep 3473867 = 5210801) B5210801
theorem B3473921 : Blo 1829616 3473921 := bstep (se 2 (by rfl) ⟨1302720, by rfl⟩ : syracuseStep 3473921 = 2605441) B2605441
theorem B2744843 : Blo 1829616 2744843 := bstep (se 1 (by rfl) ⟨2058632, by rfl⟩ : syracuseStep 2744843 = 4117265) B4117265
theorem B4121099 : Blo 1829616 4121099 := bstep (se 1 (by rfl) ⟨3090824, by rfl⟩ : syracuseStep 4121099 = 6181649) B6181649
theorem B2744855 : Blo 1829616 2744855 := bstep (se 1 (by rfl) ⟨2058641, by rfl⟩ : syracuseStep 2744855 = 4117283) B4117283
theorem B3088921 : Blo 1829616 3088921 := bstep (se 2 (by rfl) ⟨1158345, by rfl⟩ : syracuseStep 3088921 = 2316691) B2316691
theorem B2744921 : Blo 1829616 2744921 := bstep (se 2 (by rfl) ⟨1029345, by rfl⟩ : syracuseStep 2744921 = 2058691) B2058691
theorem B68633219 : Blo 1829616 68633219 := bstep (se 1 (by rfl) ⟨51474914, by rfl⟩ : syracuseStep 68633219 = 102949829) B102949829
theorem B9896579 : Blo 1829616 9896579 := bstep (se 1 (by rfl) ⟨7422434, by rfl⟩ : syracuseStep 9896579 = 14844869) B14844869
theorem B12526231 : Blo 1829616 12526231 := bstep (se 1 (by rfl) ⟨9394673, by rfl⟩ : syracuseStep 12526231 = 18789347) B18789347
theorem B13902515 : Blo 1829616 13902515 := bstep (se 1 (by rfl) ⟨10426886, by rfl⟩ : syracuseStep 13902515 = 20853773) B20853773
theorem B2745035 : Blo 1829616 2745035 := bstep (se 1 (by rfl) ⟨2058776, by rfl⟩ : syracuseStep 2745035 = 4117553) B4117553
theorem B2745047 : Blo 1829616 2745047 := bstep (se 1 (by rfl) ⟨2058785, by rfl⟩ : syracuseStep 2745047 = 4117571) B4117571
theorem B2745113 : Blo 1829616 2745113 := bstep (se 2 (by rfl) ⟨1029417, by rfl⟩ : syracuseStep 2745113 = 2058835) B2058835
theorem B11731787 : Blo 1829616 11731787 := bstep (se 1 (by rfl) ⟨8798840, by rfl⟩ : syracuseStep 11731787 = 17597681) B17597681
theorem B25043813 : Blo 1829616 25043813 := bstep (se 4 (by rfl) ⟨2347857, by rfl⟩ : syracuseStep 25043813 = 4695715) B4695715
theorem B2745227 : Blo 1829616 2745227 := bstep (se 1 (by rfl) ⟨2058920, by rfl⟩ : syracuseStep 2745227 = 4117841) B4117841
theorem B3908503 : Blo 1829616 3908503 := bstep (se 1 (by rfl) ⟨2931377, by rfl⟩ : syracuseStep 3908503 = 5862755) B5862755
theorem B2745239 : Blo 1829616 2745239 := bstep (se 1 (by rfl) ⟨2058929, by rfl⟩ : syracuseStep 2745239 = 4117859) B4117859
theorem B8258507 : Blo 1829616 8258507 := bstep (se 1 (by rfl) ⟨6193880, by rfl⟩ : syracuseStep 8258507 = 12387761) B12387761
theorem B2745305 : Blo 1829616 2745305 := bstep (se 2 (by rfl) ⟨1029489, by rfl⟩ : syracuseStep 2745305 = 2058979) B2058979
theorem B6177815 : Blo 1829616 6177815 := bstep (se 1 (by rfl) ⟨4633361, by rfl⟩ : syracuseStep 6177815 = 9266723) B9266723
theorem B23454755 : Blo 1829616 23454755 := bstep (se 1 (by rfl) ⟨17591066, by rfl⟩ : syracuseStep 23454755 = 35182133) B35182133
theorem B5211211 : Blo 1829616 5211211 := bstep (se 1 (by rfl) ⟨3908408, by rfl⟩ : syracuseStep 5211211 = 7816817) B7816817
theorem B2745419 : Blo 1829616 2745419 := bstep (se 1 (by rfl) ⟨2059064, by rfl⟩ : syracuseStep 2745419 = 4118129) B4118129
theorem B2745431 : Blo 1829616 2745431 := bstep (se 1 (by rfl) ⟨2059073, by rfl⟩ : syracuseStep 2745431 = 4118147) B4118147
theorem B3089495 : Blo 1829616 3089495 := bstep (se 1 (by rfl) ⟨2317121, by rfl⟩ : syracuseStep 3089495 = 4634243) B4634243
theorem B2745497 : Blo 1829616 2745497 := bstep (se 2 (by rfl) ⟨1029561, by rfl⟩ : syracuseStep 2745497 = 2059123) B2059123
theorem B11732147 : Blo 1829616 11732147 := bstep (se 1 (by rfl) ⟨8799110, by rfl⟩ : syracuseStep 11732147 = 17598221) B17598221
theorem B3089623 : Blo 1829616 3089623 := bstep (se 1 (by rfl) ⟨2317217, by rfl⟩ : syracuseStep 3089623 = 4634435) B4634435
theorem B2745611 : Blo 1829616 2745611 := bstep (se 1 (by rfl) ⟨2059208, by rfl⟩ : syracuseStep 2745611 = 4118417) B4118417
theorem B2745623 : Blo 1829616 2745623 := bstep (se 1 (by rfl) ⟨2059217, by rfl⟩ : syracuseStep 2745623 = 4118435) B4118435
theorem B14279971 : Blo 1829616 14279971 := bstep (se 1 (by rfl) ⟨10709978, by rfl⟩ : syracuseStep 14279971 = 21419957) B21419957
theorem B11724097 : Blo 1829616 11724097 := bstep (se 2 (by rfl) ⟨4396536, by rfl⟩ : syracuseStep 11724097 = 8793073) B8793073
theorem B3761473 : Blo 1829616 3761473 := bstep (se 2 (by rfl) ⟨1410552, by rfl⟩ : syracuseStep 3761473 = 2821105) B2821105
theorem B4400459 : Blo 1829616 4400459 := bstep (se 1 (by rfl) ⟨3300344, by rfl⟩ : syracuseStep 4400459 = 6600689) B6600689
theorem B2745689 : Blo 1829616 2745689 := bstep (se 2 (by rfl) ⟨1029633, by rfl⟩ : syracuseStep 2745689 = 2059267) B2059267
theorem B5211485 : Blo 1829616 5211485 := bstep (se 3 (by rfl) ⟨977153, by rfl⟩ : syracuseStep 5211485 = 1954307) B1954307
theorem B3474839 : Blo 1829616 3474839 := bstep (se 1 (by rfl) ⟨2606129, by rfl⟩ : syracuseStep 3474839 = 5212259) B5212259
theorem B2745803 : Blo 1829616 2745803 := bstep (se 1 (by rfl) ⟨2059352, by rfl⟩ : syracuseStep 2745803 = 4118705) B4118705
theorem B2745815 : Blo 1829616 2745815 := bstep (se 1 (by rfl) ⟨2059361, by rfl⟩ : syracuseStep 2745815 = 4118723) B4118723
theorem B2745881 : Blo 1829616 2745881 := bstep (se 2 (by rfl) ⟨1029705, by rfl⟩ : syracuseStep 2745881 = 2059411) B2059411
theorem B6178355 : Blo 1829616 6178355 := bstep (se 1 (by rfl) ⟨4633766, by rfl⟩ : syracuseStep 6178355 = 9267533) B9267533
theorem B5563979 : Blo 1829616 5563979 := bstep (se 1 (by rfl) ⟨4172984, by rfl⟩ : syracuseStep 5563979 = 8345969) B8345969
theorem B2745995 : Blo 1829616 2745995 := bstep (se 1 (by rfl) ⟨2059496, by rfl⟩ : syracuseStep 2745995 = 4118993) B4118993
theorem B2746007 : Blo 1829616 2746007 := bstep (se 1 (by rfl) ⟨2059505, by rfl⟩ : syracuseStep 2746007 = 4119011) B4119011
theorem B5211827 : Blo 1829616 5211827 := bstep (se 1 (by rfl) ⟨3908870, by rfl⟩ : syracuseStep 5211827 = 7817741) B7817741
theorem B3909323 : Blo 1829616 3909323 := bstep (se 1 (by rfl) ⟨2931992, by rfl⟩ : syracuseStep 3909323 = 5863985) B5863985
theorem B2746073 : Blo 1829616 2746073 := bstep (se 2 (by rfl) ⟨1029777, by rfl⟩ : syracuseStep 2746073 = 2059555) B2059555
theorem B6178625 : Blo 1829616 6178625 := bstep (se 2 (by rfl) ⟨2316984, by rfl⟩ : syracuseStep 6178625 = 4633969) B4633969
theorem B9398081 : Blo 1829616 9398081 := bstep (se 2 (by rfl) ⟨3524280, by rfl⟩ : syracuseStep 9398081 = 7048561) B7048561
theorem B5867329 : Blo 1829616 5867329 := bstep (se 2 (by rfl) ⟨2200248, by rfl⟩ : syracuseStep 5867329 = 4400497) B4400497
theorem B2746187 : Blo 1829616 2746187 := bstep (se 1 (by rfl) ⟨2059640, by rfl⟩ : syracuseStep 2746187 = 4119281) B4119281
theorem B3090251 : Blo 1829616 3090251 := bstep (se 1 (by rfl) ⟨2317688, by rfl⟩ : syracuseStep 3090251 = 4635377) B4635377
theorem B2746199 : Blo 1829616 2746199 := bstep (se 1 (by rfl) ⟨2059649, by rfl⟩ : syracuseStep 2746199 = 4119299) B4119299
theorem B2746265 : Blo 1829616 2746265 := bstep (se 2 (by rfl) ⟨1029849, by rfl⟩ : syracuseStep 2746265 = 2059699) B2059699
theorem B3475379 : Blo 1829616 3475379 := bstep (se 1 (by rfl) ⟨2606534, by rfl⟩ : syracuseStep 3475379 = 5213069) B5213069
theorem B3090379 : Blo 1829616 3090379 := bstep (se 1 (by rfl) ⟨2317784, by rfl⟩ : syracuseStep 3090379 = 4635569) B4635569
theorem B2746379 : Blo 1829616 2746379 := bstep (se 1 (by rfl) ⟨2059784, by rfl⟩ : syracuseStep 2746379 = 4119569) B4119569
theorem B2746391 : Blo 1829616 2746391 := bstep (se 1 (by rfl) ⟨2059793, by rfl⟩ : syracuseStep 2746391 = 4119587) B4119587
theorem B8800301 : Blo 1829616 8800301 := bstep (se 3 (by rfl) ⟨1650056, by rfl⟩ : syracuseStep 8800301 = 3300113) B3300113
theorem B4458547 : Blo 1829616 4458547 := bstep (se 1 (by rfl) ⟨3343910, by rfl⟩ : syracuseStep 4458547 = 6687821) B6687821
theorem B2746457 : Blo 1829616 2746457 := bstep (se 2 (by rfl) ⟨1029921, by rfl⟩ : syracuseStep 2746457 = 2059843) B2059843
theorem B3090521 : Blo 1829616 3090521 := bstep (se 2 (by rfl) ⟨1158945, by rfl⟩ : syracuseStep 3090521 = 2317891) B2317891
theorem B13903973 : Blo 1829616 13903973 := bstep (se 4 (by rfl) ⟨1303497, by rfl⟩ : syracuseStep 13903973 = 2606995) B2606995
theorem B2746571 : Blo 1829616 2746571 := bstep (se 1 (by rfl) ⟨2059928, by rfl⟩ : syracuseStep 2746571 = 4119857) B4119857
theorem B2746583 : Blo 1829616 2746583 := bstep (se 1 (by rfl) ⟨2059937, by rfl⟩ : syracuseStep 2746583 = 4119875) B4119875
theorem B3090649 : Blo 1829616 3090649 := bstep (se 2 (by rfl) ⟨1158993, by rfl⟩ : syracuseStep 3090649 = 2317987) B2317987
theorem B2058475 : Blo 1829616 2058475 := bstep (se 1 (by rfl) ⟨1543856, by rfl⟩ : syracuseStep 2058475 = 3087713) B3087713
theorem B2746649 : Blo 1829616 2746649 := bstep (se 2 (by rfl) ⟨1029993, by rfl⟩ : syracuseStep 2746649 = 2059987) B2059987
theorem B15640877 : Blo 1829616 15640877 := bstep (se 3 (by rfl) ⟨2932664, by rfl⟩ : syracuseStep 15640877 = 5865329) B5865329
theorem B2058583 : Blo 1829616 2058583 := bstep (se 1 (by rfl) ⟨1543937, by rfl⟩ : syracuseStep 2058583 = 3087875) B3087875
theorem B6179165 : Blo 1829616 6179165 := bstep (se 3 (by rfl) ⟨1158593, by rfl⟩ : syracuseStep 6179165 = 2317187) B2317187
theorem B2746763 : Blo 1829616 2746763 := bstep (se 1 (by rfl) ⟨2060072, by rfl⟩ : syracuseStep 2746763 = 4120145) B4120145
theorem B2746775 : Blo 1829616 2746775 := bstep (se 1 (by rfl) ⟨2060081, by rfl⟩ : syracuseStep 2746775 = 4120163) B4120163
theorem B3475865 : Blo 1829616 3475865 := bstep (se 2 (by rfl) ⟨1303449, by rfl⟩ : syracuseStep 3475865 = 2606899) B2606899
theorem B2746841 : Blo 1829616 2746841 := bstep (se 2 (by rfl) ⟨1030065, by rfl⟩ : syracuseStep 2746841 = 2060131) B2060131
theorem B13896197 : Blo 1829616 13896197 := bstep (se 4 (by rfl) ⟨1302768, by rfl⟩ : syracuseStep 13896197 = 2605537) B2605537
theorem B2058763 : Blo 1829616 2058763 := bstep (se 1 (by rfl) ⟨1544072, by rfl⟩ : syracuseStep 2058763 = 3088145) B3088145
theorem B5564951 : Blo 1829616 5564951 := bstep (se 1 (by rfl) ⟨4173713, by rfl⟩ : syracuseStep 5564951 = 8347427) B8347427
theorem B3910169 : Blo 1829616 3910169 := bstep (se 2 (by rfl) ⟨1466313, by rfl⟩ : syracuseStep 3910169 = 2932627) B2932627
theorem B6949421 : Blo 1829616 6949421 := bstep (se 3 (by rfl) ⟨1303016, by rfl⟩ : syracuseStep 6949421 = 2606033) B2606033
theorem B8792651 : Blo 1829616 8792651 := bstep (se 1 (by rfl) ⟨6594488, by rfl⟩ : syracuseStep 8792651 = 13188977) B13188977
theorem B13904459 : Blo 1829616 13904459 := bstep (se 1 (by rfl) ⟨10428344, by rfl⟩ : syracuseStep 13904459 = 20856689) B20856689
theorem B2746955 : Blo 1829616 2746955 := bstep (se 1 (by rfl) ⟨2060216, by rfl⟩ : syracuseStep 2746955 = 4120433) B4120433
theorem B2746967 : Blo 1829616 2746967 := bstep (se 1 (by rfl) ⟨2060225, by rfl⟩ : syracuseStep 2746967 = 4120451) B4120451
theorem B10422877 : Blo 1829616 10422877 := bstep (se 3 (by rfl) ⟨1954289, by rfl⟩ : syracuseStep 10422877 = 3908579) B3908579
theorem B19802717 : Blo 1829616 19802717 := bstep (se 3 (by rfl) ⟨3713009, by rfl⟩ : syracuseStep 19802717 = 7426019) B7426019
theorem B2058871 : Blo 1829616 2058871 := bstep (se 1 (by rfl) ⟨1544153, by rfl⟩ : syracuseStep 2058871 = 3088307) B3088307
theorem B2747033 : Blo 1829616 2747033 := bstep (se 2 (by rfl) ⟨1030137, by rfl⟩ : syracuseStep 2747033 = 2060275) B2060275
theorem B1829623 : Blo 1829616 1829623 := bstep (se 1 (by rfl) ⟨1372217, by rfl⟩ : syracuseStep 1829623 = 2744435) B2744435
theorem B1829643 : Blo 1829616 1829643 := bstep (se 1 (by rfl) ⟨1372232, by rfl⟩ : syracuseStep 1829643 = 2744465) B2744465
theorem B2747147 : Blo 1829616 2747147 := bstep (se 1 (by rfl) ⟨2060360, by rfl⟩ : syracuseStep 2747147 = 4120721) B4120721
theorem B1829655 : Blo 1829616 1829655 := bstep (se 1 (by rfl) ⟨1372241, by rfl⟩ : syracuseStep 1829655 = 2744483) B2744483
theorem B2747159 : Blo 1829616 2747159 := bstep (se 1 (by rfl) ⟨2060369, by rfl⟩ : syracuseStep 2747159 = 4120739) B4120739
theorem B2640665 : Blo 1829616 2640665 := bstep (se 2 (by rfl) ⟨990249, by rfl⟩ : syracuseStep 2640665 = 1980499) B1980499
theorem B1829675 : Blo 1829616 1829675 := bstep (se 1 (by rfl) ⟨1372256, by rfl⟩ : syracuseStep 1829675 = 2744513) B2744513
theorem B2059051 : Blo 1829616 2059051 := bstep (se 1 (by rfl) ⟨1544288, by rfl⟩ : syracuseStep 2059051 = 3088577) B3088577
theorem B1829687 : Blo 1829616 1829687 := bstep (se 1 (by rfl) ⟨1372265, by rfl⟩ : syracuseStep 1829687 = 2744531) B2744531
theorem B1829707 : Blo 1829616 1829707 := bstep (se 1 (by rfl) ⟨1372280, by rfl⟩ : syracuseStep 1829707 = 2744561) B2744561
theorem B1829719 : Blo 1829616 1829719 := bstep (se 1 (by rfl) ⟨1372289, by rfl⟩ : syracuseStep 1829719 = 2744579) B2744579
theorem B2747225 : Blo 1829616 2747225 := bstep (se 2 (by rfl) ⟨1030209, by rfl⟩ : syracuseStep 2747225 = 2060419) B2060419
theorem B1829739 : Blo 1829616 1829739 := bstep (se 1 (by rfl) ⟨1372304, by rfl⟩ : syracuseStep 1829739 = 2744609) B2744609
theorem B1829751 : Blo 1829616 1829751 := bstep (se 1 (by rfl) ⟨1372313, by rfl⟩ : syracuseStep 1829751 = 2744627) B2744627
theorem B7818115 : Blo 1829616 7818115 := bstep (se 1 (by rfl) ⟨5863586, by rfl⟩ : syracuseStep 7818115 = 11727173) B11727173
theorem B1829771 : Blo 1829616 1829771 := bstep (se 1 (by rfl) ⟨1372328, by rfl⟩ : syracuseStep 1829771 = 2744657) B2744657
theorem B1829783 : Blo 1829616 1829783 := bstep (se 1 (by rfl) ⟨1372337, by rfl⟩ : syracuseStep 1829783 = 2744675) B2744675
theorem B2059159 : Blo 1829616 2059159 := bstep (se 1 (by rfl) ⟨1544369, by rfl⟩ : syracuseStep 2059159 = 3088739) B3088739
theorem B1829803 : Blo 1829616 1829803 := bstep (se 1 (by rfl) ⟨1372352, by rfl⟩ : syracuseStep 1829803 = 2744705) B2744705
theorem B1829815 : Blo 1829616 1829815 := bstep (se 1 (by rfl) ⟨1372361, by rfl⟩ : syracuseStep 1829815 = 2744723) B2744723
theorem B4631489 : Blo 1829616 4631489 := bstep (se 2 (by rfl) ⟨1736808, by rfl⟩ : syracuseStep 4631489 = 3473617) B3473617
theorem B1829835 : Blo 1829616 1829835 := bstep (se 1 (by rfl) ⟨1372376, by rfl⟩ : syracuseStep 1829835 = 2744753) B2744753
theorem B2747339 : Blo 1829616 2747339 := bstep (se 1 (by rfl) ⟨2060504, by rfl⟩ : syracuseStep 2747339 = 4121009) B4121009
theorem B1829847 : Blo 1829616 1829847 := bstep (se 1 (by rfl) ⟨1372385, by rfl⟩ : syracuseStep 1829847 = 2744771) B2744771
theorem B2747351 : Blo 1829616 2747351 := bstep (se 1 (by rfl) ⟨2060513, by rfl⟩ : syracuseStep 2747351 = 4121027) B4121027
theorem B1829867 : Blo 1829616 1829867 := bstep (se 1 (by rfl) ⟨1372400, by rfl⟩ : syracuseStep 1829867 = 2744801) B2744801
theorem B1829879 : Blo 1829616 1829879 := bstep (se 1 (by rfl) ⟨1372409, by rfl⟩ : syracuseStep 1829879 = 2744819) B2744819
theorem B1829899 : Blo 1829616 1829899 := bstep (se 1 (by rfl) ⟨1372424, by rfl⟩ : syracuseStep 1829899 = 2744849) B2744849
theorem B22866961 : Blo 1829616 22866961 := bstep (se 2 (by rfl) ⟨8575110, by rfl⟩ : syracuseStep 22866961 = 17150221) B17150221
theorem B1829911 : Blo 1829616 1829911 := bstep (se 1 (by rfl) ⟨1372433, by rfl⟩ : syracuseStep 1829911 = 2744867) B2744867
theorem B2747417 : Blo 1829616 2747417 := bstep (se 2 (by rfl) ⟨1030281, by rfl⟩ : syracuseStep 2747417 = 2060563) B2060563
theorem B1829931 : Blo 1829616 1829931 := bstep (se 1 (by rfl) ⟨1372448, by rfl⟩ : syracuseStep 1829931 = 2744897) B2744897
theorem B1829943 : Blo 1829616 1829943 := bstep (se 1 (by rfl) ⟨1372457, by rfl⟩ : syracuseStep 1829943 = 2744915) B2744915
theorem B1829963 : Blo 1829616 1829963 := bstep (se 1 (by rfl) ⟨1372472, by rfl⟩ : syracuseStep 1829963 = 2744945) B2744945
theorem B2059339 : Blo 1829616 2059339 := bstep (se 1 (by rfl) ⟨1544504, by rfl⟩ : syracuseStep 2059339 = 3089009) B3089009
theorem B1829975 : Blo 1829616 1829975 := bstep (se 1 (by rfl) ⟨1372481, by rfl⟩ : syracuseStep 1829975 = 2744963) B2744963
theorem B1829995 : Blo 1829616 1829995 := bstep (se 1 (by rfl) ⟨1372496, by rfl⟩ : syracuseStep 1829995 = 2744993) B2744993
theorem B1830007 : Blo 1829616 1830007 := bstep (se 1 (by rfl) ⟨1372505, by rfl⟩ : syracuseStep 1830007 = 2745011) B2745011
theorem B1830027 : Blo 1829616 1830027 := bstep (se 1 (by rfl) ⟨1372520, by rfl⟩ : syracuseStep 1830027 = 2745041) B2745041
theorem B1830039 : Blo 1829616 1830039 := bstep (se 1 (by rfl) ⟨1372529, by rfl⟩ : syracuseStep 1830039 = 2745059) B2745059
theorem B1830059 : Blo 1829616 1830059 := bstep (se 1 (by rfl) ⟨1372544, by rfl⟩ : syracuseStep 1830059 = 2745089) B2745089
theorem B3910835 : Blo 1829616 3910835 := bstep (se 1 (by rfl) ⟨2933126, by rfl⟩ : syracuseStep 3910835 = 5866253) B5866253
theorem B1830071 : Blo 1829616 1830071 := bstep (se 1 (by rfl) ⟨1372553, by rfl⟩ : syracuseStep 1830071 = 2745107) B2745107
theorem B2059447 : Blo 1829616 2059447 := bstep (se 1 (by rfl) ⟨1544585, by rfl⟩ : syracuseStep 2059447 = 3089171) B3089171
theorem B1830091 : Blo 1829616 1830091 := bstep (se 1 (by rfl) ⟨1372568, by rfl⟩ : syracuseStep 1830091 = 2745137) B2745137
theorem B1830103 : Blo 1829616 1830103 := bstep (se 1 (by rfl) ⟨1372577, by rfl⟩ : syracuseStep 1830103 = 2745155) B2745155
theorem B8793305 : Blo 1829616 8793305 := bstep (se 2 (by rfl) ⟨3297489, by rfl⟩ : syracuseStep 8793305 = 6594979) B6594979
theorem B7818457 : Blo 1829616 7818457 := bstep (se 2 (by rfl) ⟨2931921, by rfl⟩ : syracuseStep 7818457 = 5863843) B5863843
theorem B1830123 : Blo 1829616 1830123 := bstep (se 1 (by rfl) ⟨1372592, by rfl⟩ : syracuseStep 1830123 = 2745185) B2745185
theorem B1830135 : Blo 1829616 1830135 := bstep (se 1 (by rfl) ⟨1372601, by rfl⟩ : syracuseStep 1830135 = 2745203) B2745203
theorem B1830155 : Blo 1829616 1830155 := bstep (se 1 (by rfl) ⟨1372616, by rfl⟩ : syracuseStep 1830155 = 2745233) B2745233
theorem B12528913 : Blo 1829616 12528913 := bstep (se 2 (by rfl) ⟨4698342, by rfl⟩ : syracuseStep 12528913 = 9396685) B9396685
theorem B1830167 : Blo 1829616 1830167 := bstep (se 1 (by rfl) ⟨1372625, by rfl⟩ : syracuseStep 1830167 = 2745251) B2745251
theorem B7048471 : Blo 1829616 7048471 := bstep (se 1 (by rfl) ⟨5286353, by rfl⟩ : syracuseStep 7048471 = 10572707) B10572707
theorem B1830187 : Blo 1829616 1830187 := bstep (se 1 (by rfl) ⟨1372640, by rfl⟩ : syracuseStep 1830187 = 2745281) B2745281
theorem B6950195 : Blo 1829616 6950195 := bstep (se 1 (by rfl) ⟨5212646, by rfl⟩ : syracuseStep 6950195 = 10425293) B10425293
theorem B7048499 : Blo 1829616 7048499 := bstep (se 1 (by rfl) ⟨5286374, by rfl⟩ : syracuseStep 7048499 = 10572749) B10572749
theorem B1830199 : Blo 1829616 1830199 := bstep (se 1 (by rfl) ⟨1372649, by rfl⟩ : syracuseStep 1830199 = 2745299) B2745299
theorem B1830219 : Blo 1829616 1830219 := bstep (se 1 (by rfl) ⟨1372664, by rfl⟩ : syracuseStep 1830219 = 2745329) B2745329
theorem B1830231 : Blo 1829616 1830231 := bstep (se 1 (by rfl) ⟨1372673, by rfl⟩ : syracuseStep 1830231 = 2745347) B2745347
theorem B1830251 : Blo 1829616 1830251 := bstep (se 1 (by rfl) ⟨1372688, by rfl⟩ : syracuseStep 1830251 = 2745377) B2745377
theorem B2059627 : Blo 1829616 2059627 := bstep (se 1 (by rfl) ⟨1544720, by rfl⟩ : syracuseStep 2059627 = 3089441) B3089441
theorem B1830263 : Blo 1829616 1830263 := bstep (se 1 (by rfl) ⟨1372697, by rfl⟩ : syracuseStep 1830263 = 2745395) B2745395
theorem B1830283 : Blo 1829616 1830283 := bstep (se 1 (by rfl) ⟨1372712, by rfl⟩ : syracuseStep 1830283 = 2745425) B2745425
theorem B1830295 : Blo 1829616 1830295 := bstep (se 1 (by rfl) ⟨1372721, by rfl⟩ : syracuseStep 1830295 = 2745443) B2745443
theorem B1830315 : Blo 1829616 1830315 := bstep (se 1 (by rfl) ⟨1372736, by rfl⟩ : syracuseStep 1830315 = 2745473) B2745473
theorem B1830327 : Blo 1829616 1830327 := bstep (se 1 (by rfl) ⟨1372745, by rfl⟩ : syracuseStep 1830327 = 2745491) B2745491
theorem B1830347 : Blo 1829616 1830347 := bstep (se 1 (by rfl) ⟨1372760, by rfl⟩ : syracuseStep 1830347 = 2745521) B2745521
theorem B6180299 : Blo 1829616 6180299 := bstep (se 1 (by rfl) ⟨4635224, by rfl⟩ : syracuseStep 6180299 = 9270449) B9270449
theorem B1830359 : Blo 1829616 1830359 := bstep (se 1 (by rfl) ⟨1372769, by rfl⟩ : syracuseStep 1830359 = 2745539) B2745539
theorem B2198999 : Blo 1829616 2198999 := bstep (se 1 (by rfl) ⟨1649249, by rfl⟩ : syracuseStep 2198999 = 3298499) B3298499
theorem B4632025 : Blo 1829616 4632025 := bstep (se 2 (by rfl) ⟨1737009, by rfl⟩ : syracuseStep 4632025 = 3474019) B3474019
theorem B2059735 : Blo 1829616 2059735 := bstep (se 1 (by rfl) ⟨1544801, by rfl⟩ : syracuseStep 2059735 = 3089603) B3089603
theorem B1830379 : Blo 1829616 1830379 := bstep (se 1 (by rfl) ⟨1372784, by rfl⟩ : syracuseStep 1830379 = 2745569) B2745569
theorem B1830391 : Blo 1829616 1830391 := bstep (se 1 (by rfl) ⟨1372793, by rfl⟩ : syracuseStep 1830391 = 2745587) B2745587
theorem B1830411 : Blo 1829616 1830411 := bstep (se 1 (by rfl) ⟨1372808, by rfl⟩ : syracuseStep 1830411 = 2745617) B2745617
theorem B1830423 : Blo 1829616 1830423 := bstep (se 1 (by rfl) ⟨1372817, by rfl⟩ : syracuseStep 1830423 = 2745635) B2745635
theorem B1830443 : Blo 1829616 1830443 := bstep (se 1 (by rfl) ⟨1372832, by rfl⟩ : syracuseStep 1830443 = 2745665) B2745665
theorem B1830455 : Blo 1829616 1830455 := bstep (se 1 (by rfl) ⟨1372841, by rfl⟩ : syracuseStep 1830455 = 2745683) B2745683
theorem B1830475 : Blo 1829616 1830475 := bstep (se 1 (by rfl) ⟨1372856, by rfl⟩ : syracuseStep 1830475 = 2745713) B2745713
theorem B1830487 : Blo 1829616 1830487 := bstep (se 1 (by rfl) ⟨1372865, by rfl⟩ : syracuseStep 1830487 = 2745731) B2745731
theorem B53481053 : Blo 1829616 53481053 := bstep (se 3 (by rfl) ⟨10027697, by rfl⟩ : syracuseStep 53481053 = 20055395) B20055395
theorem B9268829 : Blo 1829616 9268829 := bstep (se 3 (by rfl) ⟨1737905, by rfl⟩ : syracuseStep 9268829 = 3475811) B3475811
theorem B1830507 : Blo 1829616 1830507 := bstep (se 1 (by rfl) ⟨1372880, by rfl⟩ : syracuseStep 1830507 = 2745761) B2745761
theorem B1830519 : Blo 1829616 1830519 := bstep (se 1 (by rfl) ⟨1372889, by rfl⟩ : syracuseStep 1830519 = 2745779) B2745779
theorem B1830539 : Blo 1829616 1830539 := bstep (se 1 (by rfl) ⟨1372904, by rfl⟩ : syracuseStep 1830539 = 2745809) B2745809
theorem B2059915 : Blo 1829616 2059915 := bstep (se 1 (by rfl) ⟨1544936, by rfl⟩ : syracuseStep 2059915 = 3089873) B3089873
theorem B1830551 : Blo 1829616 1830551 := bstep (se 1 (by rfl) ⟨1372913, by rfl⟩ : syracuseStep 1830551 = 2745827) B2745827
theorem B2199191 : Blo 1829616 2199191 := bstep (se 1 (by rfl) ⟨1649393, by rfl⟩ : syracuseStep 2199191 = 3298787) B3298787
theorem B1830571 : Blo 1829616 1830571 := bstep (se 1 (by rfl) ⟨1372928, by rfl⟩ : syracuseStep 1830571 = 2745857) B2745857
theorem B1830583 : Blo 1829616 1830583 := bstep (se 1 (by rfl) ⟨1372937, by rfl⟩ : syracuseStep 1830583 = 2745875) B2745875
theorem B1830603 : Blo 1829616 1830603 := bstep (se 1 (by rfl) ⟨1372952, by rfl⟩ : syracuseStep 1830603 = 2745905) B2745905
theorem B5213899 : Blo 1829616 5213899 := bstep (se 1 (by rfl) ⟨3910424, by rfl⟩ : syracuseStep 5213899 = 7820849) B7820849
theorem B1830615 : Blo 1829616 1830615 := bstep (se 1 (by rfl) ⟨1372961, by rfl⟩ : syracuseStep 1830615 = 2745923) B2745923
theorem B6180569 : Blo 1829616 6180569 := bstep (se 2 (by rfl) ⟨2317713, by rfl⟩ : syracuseStep 6180569 = 4635427) B4635427
theorem B1830635 : Blo 1829616 1830635 := bstep (se 1 (by rfl) ⟨1372976, by rfl⟩ : syracuseStep 1830635 = 2745953) B2745953
theorem B1830647 : Blo 1829616 1830647 := bstep (se 1 (by rfl) ⟨1372985, by rfl⟩ : syracuseStep 1830647 = 2745971) B2745971
theorem B2060023 : Blo 1829616 2060023 := bstep (se 1 (by rfl) ⟨1545017, by rfl⟩ : syracuseStep 2060023 = 3090035) B3090035
theorem B1830667 : Blo 1829616 1830667 := bstep (se 1 (by rfl) ⟨1373000, by rfl⟩ : syracuseStep 1830667 = 2746001) B2746001
theorem B2199307 : Blo 1829616 2199307 := bstep (se 1 (by rfl) ⟨1649480, by rfl⟩ : syracuseStep 2199307 = 3298961) B3298961
theorem B1830679 : Blo 1829616 1830679 := bstep (se 1 (by rfl) ⟨1373009, by rfl⟩ : syracuseStep 1830679 = 2746019) B2746019
theorem B1830699 : Blo 1829616 1830699 := bstep (se 1 (by rfl) ⟨1373024, by rfl⟩ : syracuseStep 1830699 = 2746049) B2746049
theorem B1830711 : Blo 1829616 1830711 := bstep (se 1 (by rfl) ⟨1373033, by rfl⟩ : syracuseStep 1830711 = 2746067) B2746067
theorem B1830731 : Blo 1829616 1830731 := bstep (se 1 (by rfl) ⟨1373048, by rfl⟩ : syracuseStep 1830731 = 2746097) B2746097
theorem B1830743 : Blo 1829616 1830743 := bstep (se 1 (by rfl) ⟨1373057, by rfl⟩ : syracuseStep 1830743 = 2746115) B2746115
theorem B1830763 : Blo 1829616 1830763 := bstep (se 1 (by rfl) ⟨1373072, by rfl⟩ : syracuseStep 1830763 = 2746145) B2746145
theorem B1830775 : Blo 1829616 1830775 := bstep (se 1 (by rfl) ⟨1373081, by rfl⟩ : syracuseStep 1830775 = 2746163) B2746163
theorem B1830795 : Blo 1829616 1830795 := bstep (se 1 (by rfl) ⟨1373096, by rfl⟩ : syracuseStep 1830795 = 2746193) B2746193
theorem B1830807 : Blo 1829616 1830807 := bstep (se 1 (by rfl) ⟨1373105, by rfl⟩ : syracuseStep 1830807 = 2746211) B2746211
theorem B1830827 : Blo 1829616 1830827 := bstep (se 1 (by rfl) ⟨1373120, by rfl⟩ : syracuseStep 1830827 = 2746241) B2746241
theorem B2060203 : Blo 1829616 2060203 := bstep (se 1 (by rfl) ⟨1545152, by rfl⟩ : syracuseStep 2060203 = 3090305) B3090305
theorem B1830839 : Blo 1829616 1830839 := bstep (se 1 (by rfl) ⟨1373129, by rfl⟩ : syracuseStep 1830839 = 2746259) B2746259
theorem B1830859 : Blo 1829616 1830859 := bstep (se 1 (by rfl) ⟨1373144, by rfl⟩ : syracuseStep 1830859 = 2746289) B2746289
theorem B1830871 : Blo 1829616 1830871 := bstep (se 1 (by rfl) ⟨1373153, by rfl⟩ : syracuseStep 1830871 = 2746307) B2746307
theorem B1830891 : Blo 1829616 1830891 := bstep (se 1 (by rfl) ⟨1373168, by rfl⟩ : syracuseStep 1830891 = 2746337) B2746337
theorem B1830903 : Blo 1829616 1830903 := bstep (se 1 (by rfl) ⟨1373177, by rfl⟩ : syracuseStep 1830903 = 2746355) B2746355
theorem B1830923 : Blo 1829616 1830923 := bstep (se 1 (by rfl) ⟨1373192, by rfl⟩ : syracuseStep 1830923 = 2746385) B2746385
theorem B1830935 : Blo 1829616 1830935 := bstep (se 1 (by rfl) ⟨1373201, by rfl⟩ : syracuseStep 1830935 = 2746403) B2746403
theorem B2060311 : Blo 1829616 2060311 := bstep (se 1 (by rfl) ⟨1545233, by rfl⟩ : syracuseStep 2060311 = 3090467) B3090467
theorem B1830955 : Blo 1829616 1830955 := bstep (se 1 (by rfl) ⟨1373216, by rfl⟩ : syracuseStep 1830955 = 2746433) B2746433
theorem B1830967 : Blo 1829616 1830967 := bstep (se 1 (by rfl) ⟨1373225, by rfl⟩ : syracuseStep 1830967 = 2746451) B2746451
theorem B1830987 : Blo 1829616 1830987 := bstep (se 1 (by rfl) ⟨1373240, by rfl⟩ : syracuseStep 1830987 = 2746481) B2746481
theorem B1830999 : Blo 1829616 1830999 := bstep (se 1 (by rfl) ⟨1373249, by rfl⟩ : syracuseStep 1830999 = 2746499) B2746499
theorem B1831019 : Blo 1829616 1831019 := bstep (se 1 (by rfl) ⟨1373264, by rfl⟩ : syracuseStep 1831019 = 2746529) B2746529
theorem B1831031 : Blo 1829616 1831031 := bstep (se 1 (by rfl) ⟨1373273, by rfl⟩ : syracuseStep 1831031 = 2746547) B2746547
theorem B3911809 : Blo 1829616 3911809 := bstep (se 2 (by rfl) ⟨1466928, by rfl⟩ : syracuseStep 3911809 = 2933857) B2933857
theorem B1953931 : Blo 1829616 1953931 := bstep (se 1 (by rfl) ⟨1465448, by rfl⟩ : syracuseStep 1953931 = 2930897) B2930897
theorem B1831051 : Blo 1829616 1831051 := bstep (se 1 (by rfl) ⟨1373288, by rfl⟩ : syracuseStep 1831051 = 2746577) B2746577
theorem B7819415 : Blo 1829616 7819415 := bstep (se 1 (by rfl) ⟨5864561, by rfl⟩ : syracuseStep 7819415 = 11729123) B11729123
theorem B1831063 : Blo 1829616 1831063 := bstep (se 1 (by rfl) ⟨1373297, by rfl⟩ : syracuseStep 1831063 = 2746595) B2746595
theorem B1831083 : Blo 1829616 1831083 := bstep (se 1 (by rfl) ⟨1373312, by rfl⟩ : syracuseStep 1831083 = 2746625) B2746625
theorem B6598829 : Blo 1829616 6598829 := bstep (se 3 (by rfl) ⟨1237280, by rfl⟩ : syracuseStep 6598829 = 2474561) B2474561
theorem B59355317 : Blo 1829616 59355317 := bstep (se 5 (by rfl) ⟨2782280, by rfl⟩ : syracuseStep 59355317 = 5564561) B5564561
theorem B1831095 : Blo 1829616 1831095 := bstep (se 1 (by rfl) ⟨1373321, by rfl⟩ : syracuseStep 1831095 = 2746643) B2746643
theorem B5214401 : Blo 1829616 5214401 := bstep (se 2 (by rfl) ⟨1955400, by rfl⟩ : syracuseStep 5214401 = 3910801) B3910801
theorem B1831115 : Blo 1829616 1831115 := bstep (se 1 (by rfl) ⟨1373336, by rfl⟩ : syracuseStep 1831115 = 2746673) B2746673
theorem B2060491 : Blo 1829616 2060491 := bstep (se 1 (by rfl) ⟨1545368, by rfl⟩ : syracuseStep 2060491 = 3090737) B3090737
theorem B1831127 : Blo 1829616 1831127 := bstep (se 1 (by rfl) ⟨1373345, by rfl⟩ : syracuseStep 1831127 = 2746691) B2746691
theorem B1831147 : Blo 1829616 1831147 := bstep (se 1 (by rfl) ⟨1373360, by rfl⟩ : syracuseStep 1831147 = 2746721) B2746721
theorem B1831159 : Blo 1829616 1831159 := bstep (se 1 (by rfl) ⟨1373369, by rfl⟩ : syracuseStep 1831159 = 2746739) B2746739
theorem B1831179 : Blo 1829616 1831179 := bstep (se 1 (by rfl) ⟨1373384, by rfl⟩ : syracuseStep 1831179 = 2746769) B2746769
theorem B1831191 : Blo 1829616 1831191 := bstep (se 1 (by rfl) ⟨1373393, by rfl⟩ : syracuseStep 1831191 = 2746787) B2746787
theorem B4116761 : Blo 1829616 4116761 := bstep (se 2 (by rfl) ⟨1543785, by rfl⟩ : syracuseStep 4116761 = 3087571) B3087571
theorem B1831211 : Blo 1829616 1831211 := bstep (se 1 (by rfl) ⟨1373408, by rfl⟩ : syracuseStep 1831211 = 2746817) B2746817
theorem B1831223 : Blo 1829616 1831223 := bstep (se 1 (by rfl) ⟨1373417, by rfl⟩ : syracuseStep 1831223 = 2746835) B2746835
theorem B2199883 : Blo 1829616 2199883 := bstep (se 1 (by rfl) ⟨1649912, by rfl⟩ : syracuseStep 2199883 = 3299825) B3299825
theorem B1831243 : Blo 1829616 1831243 := bstep (se 1 (by rfl) ⟨1373432, by rfl⟩ : syracuseStep 1831243 = 2746865) B2746865
theorem B1831255 : Blo 1829616 1831255 := bstep (se 1 (by rfl) ⟨1373441, by rfl⟩ : syracuseStep 1831255 = 2746883) B2746883
theorem B1831275 : Blo 1829616 1831275 := bstep (se 1 (by rfl) ⟨1373456, by rfl⟩ : syracuseStep 1831275 = 2746913) B2746913
theorem B4116851 : Blo 1829616 4116851 := bstep (se 1 (by rfl) ⟨3087638, by rfl⟩ : syracuseStep 4116851 = 6175277) B6175277
theorem B1831287 : Blo 1829616 1831287 := bstep (se 1 (by rfl) ⟨1373465, by rfl⟩ : syracuseStep 1831287 = 2746931) B2746931
theorem B1831307 : Blo 1829616 1831307 := bstep (se 1 (by rfl) ⟨1373480, by rfl⟩ : syracuseStep 1831307 = 2746961) B2746961
theorem B4116887 : Blo 1829616 4116887 := bstep (se 1 (by rfl) ⟨3087665, by rfl⟩ : syracuseStep 4116887 = 6175331) B6175331
theorem B1831319 : Blo 1829616 1831319 := bstep (se 1 (by rfl) ⟨1373489, by rfl⟩ : syracuseStep 1831319 = 2746979) B2746979
theorem B6181271 : Blo 1829616 6181271 := bstep (se 1 (by rfl) ⟨4635953, by rfl⟩ : syracuseStep 6181271 = 9271907) B9271907
theorem B1831339 : Blo 1829616 1831339 := bstep (se 1 (by rfl) ⟨1373504, by rfl⟩ : syracuseStep 1831339 = 2747009) B2747009
theorem B1831351 : Blo 1829616 1831351 := bstep (se 1 (by rfl) ⟨1373513, by rfl⟩ : syracuseStep 1831351 = 2747027) B2747027
theorem B5943745 : Blo 1829616 5943745 := bstep (se 2 (by rfl) ⟨2228904, by rfl⟩ : syracuseStep 5943745 = 4457809) B4457809
theorem B1831371 : Blo 1829616 1831371 := bstep (se 1 (by rfl) ⟨1373528, by rfl⟩ : syracuseStep 1831371 = 2747057) B2747057
theorem B1831383 : Blo 1829616 1831383 := bstep (se 1 (by rfl) ⟨1373537, by rfl⟩ : syracuseStep 1831383 = 2747075) B2747075
theorem B1831403 : Blo 1829616 1831403 := bstep (se 1 (by rfl) ⟨1373552, by rfl⟩ : syracuseStep 1831403 = 2747105) B2747105
theorem B1831415 : Blo 1829616 1831415 := bstep (se 1 (by rfl) ⟨1373561, by rfl⟩ : syracuseStep 1831415 = 2747123) B2747123
theorem B1831435 : Blo 1829616 1831435 := bstep (se 1 (by rfl) ⟨1373576, by rfl⟩ : syracuseStep 1831435 = 2747153) B2747153
theorem B5214743 : Blo 1829616 5214743 := bstep (se 1 (by rfl) ⟨3911057, by rfl⟩ : syracuseStep 5214743 = 7822115) B7822115
theorem B1831447 : Blo 1829616 1831447 := bstep (se 1 (by rfl) ⟨1373585, by rfl⟩ : syracuseStep 1831447 = 2747171) B2747171
theorem B1831467 : Blo 1829616 1831467 := bstep (se 1 (by rfl) ⟨1373600, by rfl⟩ : syracuseStep 1831467 = 2747201) B2747201
theorem B4633139 : Blo 1829616 4633139 := bstep (se 1 (by rfl) ⟨3474854, by rfl⟩ : syracuseStep 4633139 = 6949709) B6949709
theorem B1831479 : Blo 1829616 1831479 := bstep (se 1 (by rfl) ⟨1373609, by rfl⟩ : syracuseStep 1831479 = 2747219) B2747219
theorem B4117067 : Blo 1829616 4117067 := bstep (se 1 (by rfl) ⟨3087800, by rfl⟩ : syracuseStep 4117067 = 6175601) B6175601
theorem B1831499 : Blo 1829616 1831499 := bstep (se 1 (by rfl) ⟨1373624, by rfl⟩ : syracuseStep 1831499 = 2747249) B2747249
theorem B1831511 : Blo 1829616 1831511 := bstep (se 1 (by rfl) ⟨1373633, by rfl⟩ : syracuseStep 1831511 = 2747267) B2747267
theorem B1831531 : Blo 1829616 1831531 := bstep (se 1 (by rfl) ⟨1373648, by rfl⟩ : syracuseStep 1831531 = 2747297) B2747297
theorem B1831543 : Blo 1829616 1831543 := bstep (se 1 (by rfl) ⟨1373657, by rfl⟩ : syracuseStep 1831543 = 2747315) B2747315
theorem B4117121 : Blo 1829616 4117121 := bstep (se 2 (by rfl) ⟨1543920, by rfl⟩ : syracuseStep 4117121 = 3087841) B3087841
theorem B1831563 : Blo 1829616 1831563 := bstep (se 1 (by rfl) ⟨1373672, by rfl⟩ : syracuseStep 1831563 = 2747345) B2747345
theorem B1831575 : Blo 1829616 1831575 := bstep (se 1 (by rfl) ⟨1373681, by rfl⟩ : syracuseStep 1831575 = 2747363) B2747363
theorem B1831595 : Blo 1829616 1831595 := bstep (se 1 (by rfl) ⟨1373696, by rfl⟩ : syracuseStep 1831595 = 2747393) B2747393
theorem B1831607 : Blo 1829616 1831607 := bstep (se 1 (by rfl) ⟨1373705, by rfl⟩ : syracuseStep 1831607 = 2747411) B2747411
theorem B6951683 : Blo 1829616 6951683 := bstep (se 1 (by rfl) ⟨5213762, by rfl⟩ : syracuseStep 6951683 = 10427525) B10427525
theorem B4117337 : Blo 1829616 4117337 := bstep (se 2 (by rfl) ⟨1544001, by rfl⟩ : syracuseStep 4117337 = 3088003) B3088003
theorem B4633433 : Blo 1829616 4633433 := bstep (se 2 (by rfl) ⟨1737537, by rfl⟩ : syracuseStep 4633433 = 3475075) B3475075
theorem B13898627 : Blo 1829616 13898627 := bstep (se 1 (by rfl) ⟨10423970, by rfl⟩ : syracuseStep 13898627 = 20847941) B20847941
theorem B2347915 : Blo 1829616 2347915 := bstep (se 1 (by rfl) ⟨1760936, by rfl⟩ : syracuseStep 2347915 = 3521873) B3521873
theorem B4117427 : Blo 1829616 4117427 := bstep (se 1 (by rfl) ⟨3088070, by rfl⟩ : syracuseStep 4117427 = 6176141) B6176141
theorem B4117463 : Blo 1829616 4117463 := bstep (se 1 (by rfl) ⟨3088097, by rfl⟩ : syracuseStep 4117463 = 6176195) B6176195
theorem B13374595 : Blo 1829616 13374595 := bstep (se 1 (by rfl) ⟨10030946, by rfl⟩ : syracuseStep 13374595 = 20061893) B20061893
theorem B4117643 : Blo 1829616 4117643 := bstep (se 1 (by rfl) ⟨3088232, by rfl⟩ : syracuseStep 4117643 = 6176465) B6176465
theorem B6599825 : Blo 1829616 6599825 := bstep (se 2 (by rfl) ⟨2474934, by rfl⟩ : syracuseStep 6599825 = 4949869) B4949869
theorem B4117697 : Blo 1829616 4117697 := bstep (se 2 (by rfl) ⟨1544136, by rfl⟩ : syracuseStep 4117697 = 3088273) B3088273
theorem B6952139 : Blo 1829616 6952139 := bstep (se 1 (by rfl) ⟨5214104, by rfl⟩ : syracuseStep 6952139 = 10428209) B10428209
theorem B15643853 : Blo 1829616 15643853 := bstep (se 3 (by rfl) ⟨2933222, by rfl⟩ : syracuseStep 15643853 = 5866445) B5866445
theorem B30078307 : Blo 1829616 30078307 := bstep (se 1 (by rfl) ⟨22558730, by rfl⟩ : syracuseStep 30078307 = 45117461) B45117461
theorem B6952337 : Blo 1829616 6952337 := bstep (se 2 (by rfl) ⟨2607126, by rfl⟩ : syracuseStep 6952337 = 5214253) B5214253
theorem B4117913 : Blo 1829616 4117913 := bstep (se 2 (by rfl) ⟨1544217, by rfl⟩ : syracuseStep 4117913 = 3088435) B3088435
theorem B4396481 : Blo 1829616 4396481 := bstep (se 2 (by rfl) ⟨1648680, by rfl⟩ : syracuseStep 4396481 = 3297361) B3297361
theorem B4118003 : Blo 1829616 4118003 := bstep (se 1 (by rfl) ⟨3088502, by rfl⟩ : syracuseStep 4118003 = 6177005) B6177005
theorem B16709125 : Blo 1829616 16709125 := bstep (se 4 (by rfl) ⟨1566480, by rfl⟩ : syracuseStep 16709125 = 3132961) B3132961
theorem B4118039 : Blo 1829616 4118039 := bstep (se 1 (by rfl) ⟨3088529, by rfl⟩ : syracuseStep 4118039 = 6177059) B6177059
theorem B2782745 : Blo 1829616 2782745 := bstep (se 2 (by rfl) ⟨1043529, by rfl⟩ : syracuseStep 2782745 = 2087059) B2087059
theorem B4232729 : Blo 1829616 4232729 := bstep (se 2 (by rfl) ⟨1587273, by rfl⟩ : syracuseStep 4232729 = 3174547) B3174547
theorem B1955383 : Blo 1829616 1955383 := bstep (se 1 (by rfl) ⟨1466537, by rfl⟩ : syracuseStep 1955383 = 2933075) B2933075
theorem B5863063 : Blo 1829616 5863063 := bstep (se 1 (by rfl) ⟨4397297, by rfl⟩ : syracuseStep 5863063 = 8794595) B8794595
theorem B9270935 : Blo 1829616 9270935 := bstep (se 1 (by rfl) ⟨6953201, by rfl⟩ : syracuseStep 9270935 = 13906403) B13906403
theorem B4118219 : Blo 1829616 4118219 := bstep (se 1 (by rfl) ⟨3088664, by rfl⟩ : syracuseStep 4118219 = 6177329) B6177329
theorem B4118273 : Blo 1829616 4118273 := bstep (se 2 (by rfl) ⟨1544352, by rfl⟩ : syracuseStep 4118273 = 3088705) B3088705
theorem B2316043 : Blo 1829616 2316043 := bstep (se 1 (by rfl) ⟨1737032, by rfl⟩ : syracuseStep 2316043 = 3474065) B3474065
theorem B7821107 : Blo 1829616 7821107 := bstep (se 1 (by rfl) ⟨5865830, by rfl⟩ : syracuseStep 7821107 = 11731661) B11731661
theorem B100226915 : Blo 1829616 100226915 := bstep (se 1 (by rfl) ⟨75170186, by rfl⟩ : syracuseStep 100226915 = 150340373) B150340373
theorem B23467877 : Blo 1829616 23467877 := bstep (se 4 (by rfl) ⟨2200113, by rfl⟩ : syracuseStep 23467877 = 4400227) B4400227
theorem B1955755 : Blo 1829616 1955755 := bstep (se 1 (by rfl) ⟨1466816, by rfl⟩ : syracuseStep 1955755 = 2933633) B2933633
theorem B4118489 : Blo 1829616 4118489 := bstep (se 2 (by rfl) ⟨1544433, by rfl⟩ : syracuseStep 4118489 = 3088867) B3088867
theorem B2086903 : Blo 1829616 2086903 := bstep (se 1 (by rfl) ⟨1565177, by rfl⟩ : syracuseStep 2086903 = 3130355) B3130355
theorem B4118579 : Blo 1829616 4118579 := bstep (se 1 (by rfl) ⟨3088934, by rfl⟩ : syracuseStep 4118579 = 6177869) B6177869
theorem B4175923 : Blo 1829616 4175923 := bstep (se 1 (by rfl) ⟨3131942, by rfl⟩ : syracuseStep 4175923 = 6263885) B6263885
theorem B4118615 : Blo 1829616 4118615 := bstep (se 1 (by rfl) ⟨3088961, by rfl⟩ : syracuseStep 4118615 = 6177923) B6177923
theorem B6953111 : Blo 1829616 6953111 := bstep (se 1 (by rfl) ⟨5214833, by rfl⟩ : syracuseStep 6953111 = 10429667) B10429667
theorem B4397249 : Blo 1829616 4397249 := bstep (se 2 (by rfl) ⟨1648968, by rfl⟩ : syracuseStep 4397249 = 3297937) B3297937
theorem B9263321 : Blo 1829616 9263321 := bstep (se 2 (by rfl) ⟨3473745, by rfl⟩ : syracuseStep 9263321 = 6947491) B6947491
theorem B4118795 : Blo 1829616 4118795 := bstep (se 1 (by rfl) ⟨3089096, by rfl⟩ : syracuseStep 4118795 = 6178193) B6178193
theorem B6600977 : Blo 1829616 6600977 := bstep (se 2 (by rfl) ⟨2475366, by rfl⟩ : syracuseStep 6600977 = 4950733) B4950733
theorem B4118849 : Blo 1829616 4118849 := bstep (se 2 (by rfl) ⟨1544568, by rfl⟩ : syracuseStep 4118849 = 3089137) B3089137
theorem B6953309 : Blo 1829616 6953309 := bstep (se 3 (by rfl) ⟨1303745, by rfl⟩ : syracuseStep 6953309 = 2607491) B2607491
theorem B6175169 : Blo 1829616 6175169 := bstep (se 2 (by rfl) ⟨2315688, by rfl⟩ : syracuseStep 6175169 = 4631377) B4631377
theorem B4635083 : Blo 1829616 4635083 := bstep (se 1 (by rfl) ⟨3476312, by rfl⟩ : syracuseStep 4635083 = 6952625) B6952625
theorem B4119065 : Blo 1829616 4119065 := bstep (se 2 (by rfl) ⟨1544649, by rfl⟩ : syracuseStep 4119065 = 3089299) B3089299
theorem B13195811 : Blo 1829616 13195811 := bstep (se 1 (by rfl) ⟨9896858, by rfl⟩ : syracuseStep 13195811 = 19793717) B19793717
theorem B2931275 : Blo 1829616 2931275 := bstep (se 1 (by rfl) ⟨2198456, by rfl⟩ : syracuseStep 2931275 = 4396913) B4396913
theorem B4119155 : Blo 1829616 4119155 := bstep (se 1 (by rfl) ⟨3089366, by rfl⟩ : syracuseStep 4119155 = 6178733) B6178733
theorem B4119191 : Blo 1829616 4119191 := bstep (se 1 (by rfl) ⟨3089393, by rfl⟩ : syracuseStep 4119191 = 6178787) B6178787
theorem B2317015 : Blo 1829616 2317015 := bstep (se 1 (by rfl) ⟨1737761, by rfl⟩ : syracuseStep 2317015 = 3475523) B3475523
theorem B36166385 : Blo 1829616 36166385 := bstep (se 2 (by rfl) ⟨13562394, by rfl⟩ : syracuseStep 36166385 = 27124789) B27124789
theorem B4119371 : Blo 1829616 4119371 := bstep (se 1 (by rfl) ⟨3089528, by rfl⟩ : syracuseStep 4119371 = 6179057) B6179057
theorem B4119425 : Blo 1829616 4119425 := bstep (se 2 (by rfl) ⟨1544784, by rfl⟩ : syracuseStep 4119425 = 3089569) B3089569
theorem B8461207 : Blo 1829616 8461207 := bstep (se 1 (by rfl) ⟨6345905, by rfl⟩ : syracuseStep 8461207 = 12691811) B12691811
theorem B5864395 : Blo 1829616 5864395 := bstep (se 1 (by rfl) ⟨4398296, by rfl⟩ : syracuseStep 5864395 = 8796593) B8796593
theorem B6175709 : Blo 1829616 6175709 := bstep (se 3 (by rfl) ⟨1157945, by rfl⟩ : syracuseStep 6175709 = 2315891) B2315891
theorem B4119641 : Blo 1829616 4119641 := bstep (se 2 (by rfl) ⟨1544865, by rfl⟩ : syracuseStep 4119641 = 3089731) B3089731
theorem B4119731 : Blo 1829616 4119731 := bstep (se 1 (by rfl) ⟨3089798, by rfl⟩ : syracuseStep 4119731 = 6179597) B6179597
theorem B4119767 : Blo 1829616 4119767 := bstep (se 1 (by rfl) ⟨3089825, by rfl⟩ : syracuseStep 4119767 = 6179651) B6179651
theorem B2473177 : Blo 1829616 2473177 := bstep (se 2 (by rfl) ⟨927441, by rfl⟩ : syracuseStep 2473177 = 1854883) B1854883
theorem B4177217 : Blo 1829616 4177217 := bstep (se 2 (by rfl) ⟨1566456, by rfl⟩ : syracuseStep 4177217 = 3132913) B3132913
theorem B7527745 : Blo 1829616 7527745 := bstep (se 2 (by rfl) ⟨2822904, by rfl⟩ : syracuseStep 7527745 = 5645809) B5645809
theorem B4119947 : Blo 1829616 4119947 := bstep (se 1 (by rfl) ⟨3089960, by rfl⟩ : syracuseStep 4119947 = 6179921) B6179921
theorem B3087767 : Blo 1829616 3087767 := bstep (se 1 (by rfl) ⟨2315825, by rfl⟩ : syracuseStep 3087767 = 4631651) B4631651
theorem B4636055 : Blo 1829616 4636055 := bstep (se 1 (by rfl) ⟨3477041, by rfl⟩ : syracuseStep 4636055 = 6954083) B6954083
theorem B4120001 : Blo 1829616 4120001 := bstep (se 2 (by rfl) ⟨1545000, by rfl⟩ : syracuseStep 4120001 = 3090001) B3090001
theorem B2317835 : Blo 1829616 2317835 := bstep (se 1 (by rfl) ⟨1738376, by rfl⟩ : syracuseStep 2317835 = 3476753) B3476753
theorem B3087895 : Blo 1829616 3087895 := bstep (se 1 (by rfl) ⟨2315921, by rfl⟩ : syracuseStep 3087895 = 4631843) B4631843
theorem B7421491 : Blo 1829616 7421491 := bstep (se 1 (by rfl) ⟨5566118, by rfl⟩ : syracuseStep 7421491 = 11132237) B11132237
theorem B5865011 : Blo 1829616 5865011 := bstep (se 1 (by rfl) ⟨4398758, by rfl⟩ : syracuseStep 5865011 = 8797517) B8797517
theorem B6594113 : Blo 1829616 6594113 := bstep (se 2 (by rfl) ⟨2472792, by rfl⟩ : syracuseStep 6594113 = 4945585) B4945585
theorem B8461913 : Blo 1829616 8461913 := bstep (se 2 (by rfl) ⟨3173217, by rfl⟩ : syracuseStep 8461913 = 6346435) B6346435
theorem B59367005 : Blo 1829616 59367005 := bstep (se 3 (by rfl) ⟨11131313, by rfl⟩ : syracuseStep 59367005 = 22262627) B22262627
theorem B4120217 : Blo 1829616 4120217 := bstep (se 2 (by rfl) ⟨1545081, by rfl⟩ : syracuseStep 4120217 = 3090163) B3090163
theorem B4120307 : Blo 1829616 4120307 := bstep (se 1 (by rfl) ⟨3090230, by rfl⟩ : syracuseStep 4120307 = 6180461) B6180461
theorem B4120343 : Blo 1829616 4120343 := bstep (se 1 (by rfl) ⟨3090257, by rfl⟩ : syracuseStep 4120343 = 6180515) B6180515
theorem B9264941 : Blo 1829616 9264941 := bstep (se 3 (by rfl) ⟨1737176, by rfl⟩ : syracuseStep 9264941 = 3474353) B3474353
theorem B10026827 : Blo 1829616 10026827 := bstep (se 1 (by rfl) ⟨7520120, by rfl⟩ : syracuseStep 10026827 = 15040241) B15040241
theorem B28196707 : Blo 1829616 28196707 := bstep (se 1 (by rfl) ⟨21147530, by rfl⟩ : syracuseStep 28196707 = 42295061) B42295061
theorem B4120523 : Blo 1829616 4120523 := bstep (se 1 (by rfl) ⟨3090392, by rfl⟩ : syracuseStep 4120523 = 6180785) B6180785
theorem B3522619 : Blo 1829616 3522619 := bstep (se 1 (by rfl) ⟨2641964, by rfl⟩ : syracuseStep 3522619 = 5283929) B5283929
theorem B4399219 : Blo 1829616 4399219 := bstep (se 1 (by rfl) ⟨3299414, by rfl⟩ : syracuseStep 4399219 = 6598829) B6598829
theorem B3571859 : Blo 1829616 3571859 := bstep (se 1 (by rfl) ⟨2678894, by rfl⟩ : syracuseStep 3571859 = 5357789) B5357789
theorem B2474155 : Blo 1829616 2474155 := bstep (se 1 (by rfl) ⟨1855616, by rfl⟩ : syracuseStep 2474155 = 3711233) B3711233
theorem B2605241 : Blo 1829616 2605241 := bstep (se 2 (by rfl) ⟨976965, by rfl⟩ : syracuseStep 2605241 = 1953931) B1953931
theorem B2744507 : Blo 1829616 2744507 := bstep (se 1 (by rfl) ⟨2058380, by rfl⟩ : syracuseStep 2744507 = 4116761) B4116761
theorem B2744567 : Blo 1829616 2744567 := bstep (se 1 (by rfl) ⟨2058425, by rfl⟩ : syracuseStep 2744567 = 4116851) B4116851
theorem B5210369 : Blo 1829616 5210369 := bstep (se 2 (by rfl) ⟨1953888, by rfl⟩ : syracuseStep 5210369 = 3907777) B3907777
theorem B2744591 : Blo 1829616 2744591 := bstep (se 1 (by rfl) ⟨2058443, by rfl⟩ : syracuseStep 2744591 = 4116887) B4116887
theorem B4120847 : Blo 1829616 4120847 := bstep (se 1 (by rfl) ⟨3090635, by rfl⟩ : syracuseStep 4120847 = 6181271) B6181271
theorem B4120865 : Blo 1829616 4120865 := bstep (se 2 (by rfl) ⟨1545324, by rfl⟩ : syracuseStep 4120865 = 3090649) B3090649
theorem B10428709 : Blo 1829616 10428709 := bstep (se 4 (by rfl) ⟨977691, by rfl⟩ : syracuseStep 10428709 = 1955383) B1955383
theorem B2744633 : Blo 1829616 2744633 := bstep (se 2 (by rfl) ⟨1029237, by rfl⟩ : syracuseStep 2744633 = 2058475) B2058475
theorem B3088759 : Blo 1829616 3088759 := bstep (se 1 (by rfl) ⟨2316569, by rfl⟩ : syracuseStep 3088759 = 4633139) B4633139
theorem B2744711 : Blo 1829616 2744711 := bstep (se 1 (by rfl) ⟨2058533, by rfl⟩ : syracuseStep 2744711 = 4117067) B4117067
theorem B2744747 : Blo 1829616 2744747 := bstep (se 1 (by rfl) ⟨2058560, by rfl⟩ : syracuseStep 2744747 = 4117121) B4117121
theorem B2933177 : Blo 1829616 2933177 := bstep (se 2 (by rfl) ⟨1099941, by rfl⟩ : syracuseStep 2933177 = 2199883) B2199883
theorem B2744777 : Blo 1829616 2744777 := bstep (se 2 (by rfl) ⟨1029291, by rfl⟩ : syracuseStep 2744777 = 2058583) B2058583
theorem B2744891 : Blo 1829616 2744891 := bstep (se 1 (by rfl) ⟨2058668, by rfl⟩ : syracuseStep 2744891 = 4117337) B4117337
theorem B3088955 : Blo 1829616 3088955 := bstep (se 1 (by rfl) ⟨2316716, by rfl⟩ : syracuseStep 3088955 = 4633433) B4633433
theorem B16695875 : Blo 1829616 16695875 := bstep (se 1 (by rfl) ⟨12521906, by rfl⟩ : syracuseStep 16695875 = 25043813) B25043813
theorem B9265751 : Blo 1829616 9265751 := bstep (se 1 (by rfl) ⟨6949313, by rfl⟩ : syracuseStep 9265751 = 13898627) B13898627
theorem B2744951 : Blo 1829616 2744951 := bstep (se 1 (by rfl) ⟨2058713, by rfl⟩ : syracuseStep 2744951 = 4117427) B4117427
theorem B5505671 : Blo 1829616 5505671 := bstep (se 1 (by rfl) ⟨4129253, by rfl⟩ : syracuseStep 5505671 = 8258507) B8258507
theorem B2744975 : Blo 1829616 2744975 := bstep (se 1 (by rfl) ⟨2058731, by rfl⟩ : syracuseStep 2744975 = 4117463) B4117463
theorem B2745017 : Blo 1829616 2745017 := bstep (se 2 (by rfl) ⟨1029381, by rfl⟩ : syracuseStep 2745017 = 2058763) B2058763
theorem B2745095 : Blo 1829616 2745095 := bstep (se 1 (by rfl) ⟨2058821, by rfl⟩ : syracuseStep 2745095 = 4117643) B4117643
theorem B4399883 : Blo 1829616 4399883 := bstep (se 1 (by rfl) ⟨3299912, by rfl⟩ : syracuseStep 4399883 = 6599825) B6599825
theorem B2745131 : Blo 1829616 2745131 := bstep (se 1 (by rfl) ⟨2058848, by rfl⟩ : syracuseStep 2745131 = 4117697) B4117697
theorem B10429235 : Blo 1829616 10429235 := bstep (se 1 (by rfl) ⟨7821926, by rfl⟩ : syracuseStep 10429235 = 15643853) B15643853
theorem B2745161 : Blo 1829616 2745161 := bstep (se 2 (by rfl) ⟨1029435, by rfl⟩ : syracuseStep 2745161 = 2058871) B2058871
theorem B2933639 : Blo 1829616 2933639 := bstep (se 1 (by rfl) ⟨2200229, by rfl⟩ : syracuseStep 2933639 = 4400459) B4400459
theorem B3474323 : Blo 1829616 3474323 := bstep (se 1 (by rfl) ⟨2605742, by rfl⟩ : syracuseStep 3474323 = 5211485) B5211485
theorem B2745275 : Blo 1829616 2745275 := bstep (se 1 (by rfl) ⟨2058956, by rfl⟩ : syracuseStep 2745275 = 4117913) B4117913
theorem B3089353 : Blo 1829616 3089353 := bstep (se 2 (by rfl) ⟨1158507, by rfl⟩ : syracuseStep 3089353 = 2317015) B2317015
theorem B2745335 : Blo 1829616 2745335 := bstep (se 1 (by rfl) ⟨2059001, by rfl⟩ : syracuseStep 2745335 = 4118003) B4118003
theorem B2745359 : Blo 1829616 2745359 := bstep (se 1 (by rfl) ⟨2059019, by rfl⟩ : syracuseStep 2745359 = 4118039) B4118039
theorem B2745401 : Blo 1829616 2745401 := bstep (se 2 (by rfl) ⟨1029525, by rfl⟩ : syracuseStep 2745401 = 2059051) B2059051
theorem B9266237 : Blo 1829616 9266237 := bstep (se 3 (by rfl) ⟨1737419, by rfl⟩ : syracuseStep 9266237 = 3474839) B3474839
theorem B3474551 : Blo 1829616 3474551 := bstep (se 1 (by rfl) ⟨2605913, by rfl⟩ : syracuseStep 3474551 = 5211827) B5211827
theorem B2745479 : Blo 1829616 2745479 := bstep (se 1 (by rfl) ⟨2059109, by rfl⟩ : syracuseStep 2745479 = 4118219) B4118219
theorem B2745515 : Blo 1829616 2745515 := bstep (se 1 (by rfl) ⟨2059136, by rfl⟩ : syracuseStep 2745515 = 4118273) B4118273
theorem B3130553 : Blo 1829616 3130553 := bstep (se 2 (by rfl) ⟨1173957, by rfl⟩ : syracuseStep 3130553 = 2347915) B2347915
theorem B11281609 : Blo 1829616 11281609 := bstep (se 2 (by rfl) ⟨4230603, by rfl⟩ : syracuseStep 11281609 = 8461207) B8461207
theorem B5211337 : Blo 1829616 5211337 := bstep (se 2 (by rfl) ⟨1954251, by rfl⟩ : syracuseStep 5211337 = 3908503) B3908503
theorem B2745545 : Blo 1829616 2745545 := bstep (se 2 (by rfl) ⟨1029579, by rfl⟩ : syracuseStep 2745545 = 2059159) B2059159
theorem B2745659 : Blo 1829616 2745659 := bstep (se 1 (by rfl) ⟨2059244, by rfl⟩ : syracuseStep 2745659 = 4118489) B4118489
theorem B5866867 : Blo 1829616 5866867 := bstep (se 1 (by rfl) ⟨4400150, by rfl⟩ : syracuseStep 5866867 = 8800301) B8800301
theorem B2745719 : Blo 1829616 2745719 := bstep (se 1 (by rfl) ⟨2059289, by rfl⟩ : syracuseStep 2745719 = 4118579) B4118579
theorem B2745743 : Blo 1829616 2745743 := bstep (se 1 (by rfl) ⟨2059307, by rfl⟩ : syracuseStep 2745743 = 4118615) B4118615
theorem B6948281 : Blo 1829616 6948281 := bstep (se 2 (by rfl) ⟨2605605, by rfl⟩ : syracuseStep 6948281 = 5211211) B5211211
theorem B2745785 : Blo 1829616 2745785 := bstep (se 2 (by rfl) ⟨1029669, by rfl⟩ : syracuseStep 2745785 = 2059339) B2059339
theorem B2745863 : Blo 1829616 2745863 := bstep (se 1 (by rfl) ⟨2059397, by rfl⟩ : syracuseStep 2745863 = 4118795) B4118795
theorem B4400651 : Blo 1829616 4400651 := bstep (se 1 (by rfl) ⟨3300488, by rfl⟩ : syracuseStep 4400651 = 6600977) B6600977
theorem B23447069 : Blo 1829616 23447069 := bstep (se 3 (by rfl) ⟨4396325, by rfl⟩ : syracuseStep 23447069 = 8792651) B8792651
theorem B7816733 : Blo 1829616 7816733 := bstep (se 3 (by rfl) ⟨1465637, by rfl⟩ : syracuseStep 7816733 = 2931275) B2931275
theorem B2745899 : Blo 1829616 2745899 := bstep (se 1 (by rfl) ⟨2059424, by rfl⟩ : syracuseStep 2745899 = 4118849) B4118849
theorem B2745929 : Blo 1829616 2745929 := bstep (se 2 (by rfl) ⟨1029723, by rfl⟩ : syracuseStep 2745929 = 2059447) B2059447
theorem B3090055 : Blo 1829616 3090055 := bstep (se 1 (by rfl) ⟨2317541, by rfl⟩ : syracuseStep 3090055 = 4635083) B4635083
theorem B2746043 : Blo 1829616 2746043 := bstep (se 1 (by rfl) ⟨2059532, by rfl⟩ : syracuseStep 2746043 = 4119065) B4119065
theorem B2606779 : Blo 1829616 2606779 := bstep (se 1 (by rfl) ⟨1955084, by rfl⟩ : syracuseStep 2606779 = 3910169) B3910169
theorem B16705217 : Blo 1829616 16705217 := bstep (se 2 (by rfl) ⟨6264456, by rfl⟩ : syracuseStep 16705217 = 12528913) B12528913
theorem B9397961 : Blo 1829616 9397961 := bstep (se 2 (by rfl) ⟨3524235, by rfl⟩ : syracuseStep 9397961 = 7048471) B7048471
theorem B19039961 : Blo 1829616 19039961 := bstep (se 2 (by rfl) ⟨7139985, by rfl⟩ : syracuseStep 19039961 = 14279971) B14279971
theorem B2746103 : Blo 1829616 2746103 := bstep (se 1 (by rfl) ⟨2059577, by rfl⟩ : syracuseStep 2746103 = 4119155) B4119155
theorem B15632129 : Blo 1829616 15632129 := bstep (se 2 (by rfl) ⟨5862048, by rfl⟩ : syracuseStep 15632129 = 11724097) B11724097
theorem B5015297 : Blo 1829616 5015297 := bstep (se 2 (by rfl) ⟨1880736, by rfl⟩ : syracuseStep 5015297 = 3761473) B3761473
theorem B10036993 : Blo 1829616 10036993 := bstep (se 2 (by rfl) ⟨3763872, by rfl⟩ : syracuseStep 10036993 = 7527745) B7527745
theorem B2746127 : Blo 1829616 2746127 := bstep (se 1 (by rfl) ⟨2059595, by rfl⟩ : syracuseStep 2746127 = 4119191) B4119191
theorem B2746169 : Blo 1829616 2746169 := bstep (se 2 (by rfl) ⟨1029813, by rfl⟩ : syracuseStep 2746169 = 2059627) B2059627
theorem B2746247 : Blo 1829616 2746247 := bstep (se 1 (by rfl) ⟨2059685, by rfl⟩ : syracuseStep 2746247 = 4119371) B4119371
theorem B2746283 : Blo 1829616 2746283 := bstep (se 1 (by rfl) ⟨2059712, by rfl⟩ : syracuseStep 2746283 = 4119425) B4119425
theorem B2746313 : Blo 1829616 2746313 := bstep (se 2 (by rfl) ⟨1029867, by rfl⟩ : syracuseStep 2746313 = 2059735) B2059735
theorem B2746427 : Blo 1829616 2746427 := bstep (se 1 (by rfl) ⟨2059820, by rfl⟩ : syracuseStep 2746427 = 4119641) B4119641
theorem B2746487 : Blo 1829616 2746487 := bstep (se 1 (by rfl) ⟨2059865, by rfl⟩ : syracuseStep 2746487 = 4119731) B4119731
theorem B2607223 : Blo 1829616 2607223 := bstep (se 1 (by rfl) ⟨1955417, by rfl⟩ : syracuseStep 2607223 = 3910835) B3910835
theorem B2746511 : Blo 1829616 2746511 := bstep (se 1 (by rfl) ⟨2059883, by rfl⟩ : syracuseStep 2746511 = 4119767) B4119767
theorem B2746553 : Blo 1829616 2746553 := bstep (se 2 (by rfl) ⟨1029957, by rfl⟩ : syracuseStep 2746553 = 2059915) B2059915
theorem B7817417 : Blo 1829616 7817417 := bstep (se 2 (by rfl) ⟨2931531, by rfl⟩ : syracuseStep 7817417 = 5863063) B5863063
theorem B10430693 : Blo 1829616 10430693 := bstep (se 4 (by rfl) ⟨977877, by rfl⟩ : syracuseStep 10430693 = 1955755) B1955755
theorem B2746631 : Blo 1829616 2746631 := bstep (se 1 (by rfl) ⟨2059973, by rfl⟩ : syracuseStep 2746631 = 4119947) B4119947
theorem B2058511 : Blo 1829616 2058511 := bstep (se 1 (by rfl) ⟨1543883, by rfl⟩ : syracuseStep 2058511 = 3087767) B3087767
theorem B3090703 : Blo 1829616 3090703 := bstep (se 1 (by rfl) ⟨2318027, by rfl⟩ : syracuseStep 3090703 = 4636055) B4636055
theorem B2746667 : Blo 1829616 2746667 := bstep (se 1 (by rfl) ⟨2060000, by rfl⟩ : syracuseStep 2746667 = 4120001) B4120001
theorem B2746697 : Blo 1829616 2746697 := bstep (se 2 (by rfl) ⟨1030011, by rfl⟩ : syracuseStep 2746697 = 2060023) B2060023
theorem B3910007 : Blo 1829616 3910007 := bstep (se 1 (by rfl) ⟨2932505, by rfl⟩ : syracuseStep 3910007 = 5865011) B5865011
theorem B35654035 : Blo 1829616 35654035 := bstep (se 1 (by rfl) ⟨26740526, by rfl⟩ : syracuseStep 35654035 = 53481053) B53481053
theorem B39578003 : Blo 1829616 39578003 := bstep (se 1 (by rfl) ⟨29683502, by rfl⟩ : syracuseStep 39578003 = 59367005) B59367005
theorem B6179219 : Blo 1829616 6179219 := bstep (se 1 (by rfl) ⟨4634414, by rfl⟩ : syracuseStep 6179219 = 9268829) B9268829
theorem B2746811 : Blo 1829616 2746811 := bstep (se 1 (by rfl) ⟨2060108, by rfl⟩ : syracuseStep 2746811 = 4120217) B4120217
theorem B37595609 : Blo 1829616 37595609 := bstep (se 2 (by rfl) ⟨14098353, by rfl⟩ : syracuseStep 37595609 = 28196707) B28196707
theorem B2746871 : Blo 1829616 2746871 := bstep (se 1 (by rfl) ⟨2060153, by rfl⟩ : syracuseStep 2746871 = 4120307) B4120307
theorem B2746895 : Blo 1829616 2746895 := bstep (se 1 (by rfl) ⟨2060171, by rfl⟩ : syracuseStep 2746895 = 4120343) B4120343
theorem B2746937 : Blo 1829616 2746937 := bstep (se 2 (by rfl) ⟨1030101, by rfl⟩ : syracuseStep 2746937 = 2060203) B2060203
theorem B2747015 : Blo 1829616 2747015 := bstep (se 1 (by rfl) ⟨2060261, by rfl⟩ : syracuseStep 2747015 = 4120523) B4120523
theorem B2747051 : Blo 1829616 2747051 := bstep (se 1 (by rfl) ⟨2060288, by rfl⟩ : syracuseStep 2747051 = 4120577) B4120577
theorem B2747081 : Blo 1829616 2747081 := bstep (se 2 (by rfl) ⟨1030155, by rfl⟩ : syracuseStep 2747081 = 2060311) B2060311
theorem B1829639 : Blo 1829616 1829639 := bstep (se 1 (by rfl) ⟨1372229, by rfl⟩ : syracuseStep 1829639 = 2744459) B2744459
theorem B2059015 : Blo 1829616 2059015 := bstep (se 1 (by rfl) ⟨1544261, by rfl⟩ : syracuseStep 2059015 = 3088523) B3088523
theorem B1829647 : Blo 1829616 1829647 := bstep (se 1 (by rfl) ⟨1372235, by rfl⟩ : syracuseStep 1829647 = 2744471) B2744471
theorem B5212943 : Blo 1829616 5212943 := bstep (se 1 (by rfl) ⟨3909707, by rfl⟩ : syracuseStep 5212943 = 7819415) B7819415
theorem B39570211 : Blo 1829616 39570211 := bstep (se 1 (by rfl) ⟨29677658, by rfl⟩ : syracuseStep 39570211 = 59355317) B59355317
theorem B3476267 : Blo 1829616 3476267 := bstep (se 1 (by rfl) ⟨2607200, by rfl⟩ : syracuseStep 3476267 = 5214401) B5214401
theorem B9268019 : Blo 1829616 9268019 := bstep (se 1 (by rfl) ⟨6951014, by rfl⟩ : syracuseStep 9268019 = 13902029) B13902029
theorem B1829691 : Blo 1829616 1829691 := bstep (se 1 (by rfl) ⟨1372268, by rfl⟩ : syracuseStep 1829691 = 2744537) B2744537
theorem B3910459 : Blo 1829616 3910459 := bstep (se 1 (by rfl) ⟨2932844, by rfl⟩ : syracuseStep 3910459 = 5865689) B5865689
theorem B2747195 : Blo 1829616 2747195 := bstep (se 1 (by rfl) ⟨2060396, by rfl⟩ : syracuseStep 2747195 = 4120793) B4120793
theorem B2747255 : Blo 1829616 2747255 := bstep (se 1 (by rfl) ⟨2060441, by rfl⟩ : syracuseStep 2747255 = 4120883) B4120883
theorem B1829767 : Blo 1829616 1829767 := bstep (se 1 (by rfl) ⟨1372325, by rfl⟩ : syracuseStep 1829767 = 2744651) B2744651
theorem B1829775 : Blo 1829616 1829775 := bstep (se 1 (by rfl) ⟨1372331, by rfl⟩ : syracuseStep 1829775 = 2744663) B2744663
theorem B2747279 : Blo 1829616 2747279 := bstep (se 1 (by rfl) ⟨2060459, by rfl⟩ : syracuseStep 2747279 = 4120919) B4120919
theorem B2747321 : Blo 1829616 2747321 := bstep (se 2 (by rfl) ⟨1030245, by rfl⟩ : syracuseStep 2747321 = 2060491) B2060491
theorem B1829819 : Blo 1829616 1829819 := bstep (se 1 (by rfl) ⟨1372364, by rfl⟩ : syracuseStep 1829819 = 2744729) B2744729
theorem B2059195 : Blo 1829616 2059195 := bstep (se 1 (by rfl) ⟨1544396, by rfl⟩ : syracuseStep 2059195 = 3088793) B3088793
theorem B1829895 : Blo 1829616 1829895 := bstep (se 1 (by rfl) ⟨1372421, by rfl⟩ : syracuseStep 1829895 = 2744843) B2744843
theorem B2747399 : Blo 1829616 2747399 := bstep (se 1 (by rfl) ⟨2060549, by rfl⟩ : syracuseStep 2747399 = 4121099) B4121099
theorem B1829903 : Blo 1829616 1829903 := bstep (se 1 (by rfl) ⟨1372427, by rfl⟩ : syracuseStep 1829903 = 2744855) B2744855
theorem B3476495 : Blo 1829616 3476495 := bstep (se 1 (by rfl) ⟨2607371, by rfl⟩ : syracuseStep 3476495 = 5214743) B5214743
theorem B1829947 : Blo 1829616 1829947 := bstep (se 1 (by rfl) ⟨1372460, by rfl⟩ : syracuseStep 1829947 = 2744921) B2744921
theorem B45755479 : Blo 1829616 45755479 := bstep (se 1 (by rfl) ⟨34316609, by rfl⟩ : syracuseStep 45755479 = 68633219) B68633219
theorem B6597719 : Blo 1829616 6597719 := bstep (se 1 (by rfl) ⟨4948289, by rfl⟩ : syracuseStep 6597719 = 9896579) B9896579
theorem B9268343 : Blo 1829616 9268343 := bstep (se 1 (by rfl) ⟨6951257, by rfl⟩ : syracuseStep 9268343 = 13902515) B13902515
theorem B1830023 : Blo 1829616 1830023 := bstep (se 1 (by rfl) ⟨1372517, by rfl⟩ : syracuseStep 1830023 = 2745035) B2745035
theorem B1830031 : Blo 1829616 1830031 := bstep (se 1 (by rfl) ⟨1372523, by rfl⟩ : syracuseStep 1830031 = 2745047) B2745047
theorem B1830075 : Blo 1829616 1830075 := bstep (se 1 (by rfl) ⟨1372556, by rfl⟩ : syracuseStep 1830075 = 2745113) B2745113
theorem B1830151 : Blo 1829616 1830151 := bstep (se 1 (by rfl) ⟨1372613, by rfl⟩ : syracuseStep 1830151 = 2745227) B2745227
theorem B1830159 : Blo 1829616 1830159 := bstep (se 1 (by rfl) ⟨1372619, by rfl⟩ : syracuseStep 1830159 = 2745239) B2745239
theorem B1830203 : Blo 1829616 1830203 := bstep (se 1 (by rfl) ⟨1372652, by rfl⟩ : syracuseStep 1830203 = 2745305) B2745305
theorem B1830279 : Blo 1829616 1830279 := bstep (se 1 (by rfl) ⟨1372709, by rfl⟩ : syracuseStep 1830279 = 2745419) B2745419
theorem B1830287 : Blo 1829616 1830287 := bstep (se 1 (by rfl) ⟨1372715, by rfl⟩ : syracuseStep 1830287 = 2745431) B2745431
theorem B2059663 : Blo 1829616 2059663 := bstep (se 1 (by rfl) ⟨1544747, by rfl⟩ : syracuseStep 2059663 = 3089495) B3089495
theorem B1830331 : Blo 1829616 1830331 := bstep (se 1 (by rfl) ⟨1372748, by rfl⟩ : syracuseStep 1830331 = 2745497) B2745497
theorem B13897169 : Blo 1829616 13897169 := bstep (se 2 (by rfl) ⟨5211438, by rfl⟩ : syracuseStep 13897169 = 10422877) B10422877
theorem B18795997 : Blo 1829616 18795997 := bstep (se 3 (by rfl) ⟨3524249, by rfl⟩ : syracuseStep 18795997 = 7048499) B7048499
theorem B1830407 : Blo 1829616 1830407 := bstep (se 1 (by rfl) ⟨1372805, by rfl⟩ : syracuseStep 1830407 = 2745611) B2745611
theorem B1830415 : Blo 1829616 1830415 := bstep (se 1 (by rfl) ⟨1372811, by rfl⟩ : syracuseStep 1830415 = 2745623) B2745623
theorem B1830459 : Blo 1829616 1830459 := bstep (se 1 (by rfl) ⟨1372844, by rfl⟩ : syracuseStep 1830459 = 2745689) B2745689
theorem B1830535 : Blo 1829616 1830535 := bstep (se 1 (by rfl) ⟨1372901, by rfl⟩ : syracuseStep 1830535 = 2745803) B2745803
theorem B1830543 : Blo 1829616 1830543 := bstep (se 1 (by rfl) ⟨1372907, by rfl⟩ : syracuseStep 1830543 = 2745815) B2745815
theorem B1855163 : Blo 1829616 1855163 := bstep (se 1 (by rfl) ⟨1391372, by rfl⟩ : syracuseStep 1855163 = 2782745) B2782745
theorem B1830587 : Blo 1829616 1830587 := bstep (se 1 (by rfl) ⟨1372940, by rfl⟩ : syracuseStep 1830587 = 2745881) B2745881
theorem B2821819 : Blo 1829616 2821819 := bstep (se 1 (by rfl) ⟨2116364, by rfl⟩ : syracuseStep 2821819 = 4232729) B4232729
theorem B6598381 : Blo 1829616 6598381 := bstep (se 3 (by rfl) ⟨1237196, by rfl⟩ : syracuseStep 6598381 = 2474393) B2474393
theorem B1830663 : Blo 1829616 1830663 := bstep (se 1 (by rfl) ⟨1372997, by rfl⟩ : syracuseStep 1830663 = 2745995) B2745995
theorem B1830671 : Blo 1829616 1830671 := bstep (se 1 (by rfl) ⟨1373003, by rfl⟩ : syracuseStep 1830671 = 2746007) B2746007
theorem B6180623 : Blo 1829616 6180623 := bstep (se 1 (by rfl) ⟨4635467, by rfl⟩ : syracuseStep 6180623 = 9270935) B9270935
theorem B1830715 : Blo 1829616 1830715 := bstep (se 1 (by rfl) ⟨1373036, by rfl⟩ : syracuseStep 1830715 = 2746073) B2746073
theorem B10424153 : Blo 1829616 10424153 := bstep (se 2 (by rfl) ⟨3909057, by rfl⟩ : syracuseStep 10424153 = 7818115) B7818115
theorem B5214071 : Blo 1829616 5214071 := bstep (se 1 (by rfl) ⟨3910553, by rfl⟩ : syracuseStep 5214071 = 7821107) B7821107
theorem B1830791 : Blo 1829616 1830791 := bstep (se 1 (by rfl) ⟨1373093, by rfl⟩ : syracuseStep 1830791 = 2746187) B2746187
theorem B2060167 : Blo 1829616 2060167 := bstep (se 1 (by rfl) ⟨1545125, by rfl⟩ : syracuseStep 2060167 = 3090251) B3090251
theorem B1830799 : Blo 1829616 1830799 := bstep (se 1 (by rfl) ⟨1373099, by rfl⟩ : syracuseStep 1830799 = 2746199) B2746199
theorem B66817943 : Blo 1829616 66817943 := bstep (se 1 (by rfl) ⟨50113457, by rfl⟩ : syracuseStep 66817943 = 100226915) B100226915
theorem B7819193 : Blo 1829616 7819193 := bstep (se 2 (by rfl) ⟨2932197, by rfl⟩ : syracuseStep 7819193 = 5864395) B5864395
theorem B1830843 : Blo 1829616 1830843 := bstep (se 1 (by rfl) ⟨1373132, by rfl⟩ : syracuseStep 1830843 = 2746265) B2746265
theorem B1830919 : Blo 1829616 1830919 := bstep (se 1 (by rfl) ⟨1373189, by rfl⟩ : syracuseStep 1830919 = 2746379) B2746379
theorem B1830927 : Blo 1829616 1830927 := bstep (se 1 (by rfl) ⟨1373195, by rfl⟩ : syracuseStep 1830927 = 2746391) B2746391
theorem B6180893 : Blo 1829616 6180893 := bstep (se 3 (by rfl) ⟨1158917, by rfl⟩ : syracuseStep 6180893 = 2317835) B2317835
theorem B1830971 : Blo 1829616 1830971 := bstep (se 1 (by rfl) ⟨1373228, by rfl⟩ : syracuseStep 1830971 = 2746457) B2746457
theorem B2060347 : Blo 1829616 2060347 := bstep (se 1 (by rfl) ⟨1545260, by rfl⟩ : syracuseStep 2060347 = 3090521) B3090521
theorem B9269315 : Blo 1829616 9269315 := bstep (se 1 (by rfl) ⟨6951986, by rfl⟩ : syracuseStep 9269315 = 13903973) B13903973
theorem B35188829 : Blo 1829616 35188829 := bstep (se 3 (by rfl) ⟨6597905, by rfl⟩ : syracuseStep 35188829 = 13195811) B13195811
theorem B1831047 : Blo 1829616 1831047 := bstep (se 1 (by rfl) ⟨1373285, by rfl⟩ : syracuseStep 1831047 = 2746571) B2746571
theorem B1831055 : Blo 1829616 1831055 := bstep (se 1 (by rfl) ⟨1373291, by rfl⟩ : syracuseStep 1831055 = 2746583) B2746583
theorem B1831099 : Blo 1829616 1831099 := bstep (se 1 (by rfl) ⟨1373324, by rfl⟩ : syracuseStep 1831099 = 2746649) B2746649
theorem B22565101 : Blo 1829616 22565101 := bstep (se 3 (by rfl) ⟨4230956, by rfl⟩ : syracuseStep 22565101 = 8461913) B8461913
theorem B1831175 : Blo 1829616 1831175 := bstep (se 1 (by rfl) ⟨1373381, by rfl⟩ : syracuseStep 1831175 = 2746763) B2746763
theorem B1831183 : Blo 1829616 1831183 := bstep (se 1 (by rfl) ⟨1373387, by rfl⟩ : syracuseStep 1831183 = 2746775) B2746775
theorem B3297569 : Blo 1829616 3297569 := bstep (se 2 (by rfl) ⟨1236588, by rfl⟩ : syracuseStep 3297569 = 2473177) B2473177
theorem B10424609 : Blo 1829616 10424609 := bstep (se 2 (by rfl) ⟨3909228, by rfl⟩ : syracuseStep 10424609 = 7818457) B7818457
theorem B4116779 : Blo 1829616 4116779 := bstep (se 1 (by rfl) ⟨3087584, by rfl⟩ : syracuseStep 4116779 = 6175169) B6175169
theorem B1831227 : Blo 1829616 1831227 := bstep (se 1 (by rfl) ⟨1373420, by rfl⟩ : syracuseStep 1831227 = 2746841) B2746841
theorem B4632947 : Blo 1829616 4632947 := bstep (se 1 (by rfl) ⟨3474710, by rfl⟩ : syracuseStep 4632947 = 6949421) B6949421
theorem B9269639 : Blo 1829616 9269639 := bstep (se 1 (by rfl) ⟨6952229, by rfl⟩ : syracuseStep 9269639 = 13904459) B13904459
theorem B1831303 : Blo 1829616 1831303 := bstep (se 1 (by rfl) ⟨1373477, by rfl⟩ : syracuseStep 1831303 = 2746955) B2746955
theorem B1831311 : Blo 1829616 1831311 := bstep (se 1 (by rfl) ⟨1373483, by rfl⟩ : syracuseStep 1831311 = 2746967) B2746967
theorem B13201811 : Blo 1829616 13201811 := bstep (se 1 (by rfl) ⟨9901358, by rfl⟩ : syracuseStep 13201811 = 19802717) B19802717
theorem B1831355 : Blo 1829616 1831355 := bstep (se 1 (by rfl) ⟨1373516, by rfl⟩ : syracuseStep 1831355 = 2747033) B2747033
theorem B40104409 : Blo 1829616 40104409 := bstep (se 2 (by rfl) ⟨15039153, by rfl⟩ : syracuseStep 40104409 = 30078307) B30078307
theorem B1831431 : Blo 1829616 1831431 := bstep (se 1 (by rfl) ⟨1373573, by rfl⟩ : syracuseStep 1831431 = 2747147) B2747147
theorem B1831439 : Blo 1829616 1831439 := bstep (se 1 (by rfl) ⟨1373579, by rfl⟩ : syracuseStep 1831439 = 2747159) B2747159
theorem B10424861 : Blo 1829616 10424861 := bstep (se 3 (by rfl) ⟨1954661, by rfl⟩ : syracuseStep 10424861 = 3909323) B3909323
theorem B1831483 : Blo 1829616 1831483 := bstep (se 1 (by rfl) ⟨1373612, by rfl⟩ : syracuseStep 1831483 = 2747225) B2747225
theorem B1831559 : Blo 1829616 1831559 := bstep (se 1 (by rfl) ⟨1373669, by rfl⟩ : syracuseStep 1831559 = 2747339) B2747339
theorem B1831567 : Blo 1829616 1831567 := bstep (se 1 (by rfl) ⟨1373675, by rfl⟩ : syracuseStep 1831567 = 2747351) B2747351
theorem B4117139 : Blo 1829616 4117139 := bstep (se 1 (by rfl) ⟨3087854, by rfl⟩ : syracuseStep 4117139 = 6175709) B6175709
theorem B22278833 : Blo 1829616 22278833 := bstep (se 2 (by rfl) ⟨8354562, by rfl⟩ : syracuseStep 22278833 = 16709125) B16709125
theorem B1831611 : Blo 1829616 1831611 := bstep (se 1 (by rfl) ⟨1373708, by rfl⟩ : syracuseStep 1831611 = 2747417) B2747417
theorem B4117193 : Blo 1829616 4117193 := bstep (se 2 (by rfl) ⟨1543947, by rfl⟩ : syracuseStep 4117193 = 3087895) B3087895
theorem B7041773 : Blo 1829616 7041773 := bstep (se 3 (by rfl) ⟨1320332, by rfl⟩ : syracuseStep 7041773 = 2640665) B2640665
theorem B5862203 : Blo 1829616 5862203 := bstep (se 1 (by rfl) ⟨4396652, by rfl⟩ : syracuseStep 5862203 = 8793305) B8793305
theorem B4633463 : Blo 1829616 4633463 := bstep (se 1 (by rfl) ⟨3475097, by rfl⟩ : syracuseStep 4633463 = 6950195) B6950195
theorem B6951865 : Blo 1829616 6951865 := bstep (se 2 (by rfl) ⟨2606949, by rfl⟩ : syracuseStep 6951865 = 5213899) B5213899
theorem B31699973 : Blo 1829616 31699973 := bstep (se 4 (by rfl) ⟨2971872, by rfl⟩ : syracuseStep 31699973 = 5943745) B5943745
theorem B4396075 : Blo 1829616 4396075 := bstep (se 1 (by rfl) ⟨3297056, by rfl⟩ : syracuseStep 4396075 = 6594113) B6594113
theorem B11130149 : Blo 1829616 11130149 := bstep (se 4 (by rfl) ⟨1043451, by rfl⟩ : syracuseStep 11130149 = 2086903) B2086903
theorem B4117895 : Blo 1829616 4117895 := bstep (se 1 (by rfl) ⟨3088421, by rfl⟩ : syracuseStep 4117895 = 6176843) B6176843
theorem B5567897 : Blo 1829616 5567897 := bstep (se 2 (by rfl) ⟨2087961, by rfl⟩ : syracuseStep 5567897 = 4175923) B4175923
theorem B23451065 : Blo 1829616 23451065 := bstep (se 2 (by rfl) ⟨8794149, by rfl⟩ : syracuseStep 23451065 = 17588299) B17588299
theorem B3298745 : Blo 1829616 3298745 := bstep (se 2 (by rfl) ⟨1237029, by rfl⟩ : syracuseStep 3298745 = 2474059) B2474059
theorem B5215745 : Blo 1829616 5215745 := bstep (se 2 (by rfl) ⟨1955904, by rfl⟩ : syracuseStep 5215745 = 3911809) B3911809
theorem B4118075 : Blo 1829616 4118075 := bstep (se 1 (by rfl) ⟨3088556, by rfl⟩ : syracuseStep 4118075 = 6177113) B6177113
theorem B23778917 : Blo 1829616 23778917 := bstep (se 4 (by rfl) ⟨2229273, by rfl⟩ : syracuseStep 23778917 = 4458547) B4458547
theorem B2315947 : Blo 1829616 2315947 := bstep (se 1 (by rfl) ⟨1736960, by rfl⟩ : syracuseStep 2315947 = 3473921) B3473921
theorem B4118201 : Blo 1829616 4118201 := bstep (se 2 (by rfl) ⟨1544325, by rfl⟩ : syracuseStep 4118201 = 3088651) B3088651
theorem B3299105 : Blo 1829616 3299105 := bstep (se 2 (by rfl) ⟨1237164, by rfl⟩ : syracuseStep 3299105 = 2474329) B2474329
theorem B4634455 : Blo 1829616 4634455 := bstep (se 1 (by rfl) ⟨3475841, by rfl⟩ : syracuseStep 4634455 = 6951683) B6951683
theorem B7821191 : Blo 1829616 7821191 := bstep (se 1 (by rfl) ⟨5865893, by rfl⟩ : syracuseStep 7821191 = 11731787) B11731787
theorem B4118543 : Blo 1829616 4118543 := bstep (se 1 (by rfl) ⟨3088907, by rfl⟩ : syracuseStep 4118543 = 6177815) B6177815
theorem B15636503 : Blo 1829616 15636503 := bstep (se 1 (by rfl) ⟨11727377, by rfl⟩ : syracuseStep 15636503 = 23454755) B23454755
theorem B4118561 : Blo 1829616 4118561 := bstep (se 2 (by rfl) ⟨1544460, by rfl⟩ : syracuseStep 4118561 = 3088921) B3088921
theorem B7821431 : Blo 1829616 7821431 := bstep (se 1 (by rfl) ⟨5866073, by rfl⟩ : syracuseStep 7821431 = 11732147) B11732147
theorem B4634759 : Blo 1829616 4634759 := bstep (se 1 (by rfl) ⟨3476069, by rfl⟩ : syracuseStep 4634759 = 6952139) B6952139
theorem B16701641 : Blo 1829616 16701641 := bstep (se 2 (by rfl) ⟨6263115, by rfl⟩ : syracuseStep 16701641 = 12526231) B12526231
theorem B4634891 : Blo 1829616 4634891 := bstep (se 1 (by rfl) ⟨3476168, by rfl⟩ : syracuseStep 4634891 = 6952337) B6952337
theorem B2930987 : Blo 1829616 2930987 := bstep (se 1 (by rfl) ⟨2198240, by rfl⟩ : syracuseStep 2930987 = 4396481) B4396481
theorem B4118903 : Blo 1829616 4118903 := bstep (se 1 (by rfl) ⟨3089177, by rfl⟩ : syracuseStep 4118903 = 6178355) B6178355
theorem B3709319 : Blo 1829616 3709319 := bstep (se 1 (by rfl) ⟨2781989, by rfl⟩ : syracuseStep 3709319 = 5563979) B5563979
theorem B9263645 : Blo 1829616 9263645 := bstep (se 3 (by rfl) ⟨1736933, by rfl⟩ : syracuseStep 9263645 = 3473867) B3473867
theorem B4119083 : Blo 1829616 4119083 := bstep (se 1 (by rfl) ⟨3089312, by rfl⟩ : syracuseStep 4119083 = 6178625) B6178625
theorem B6265387 : Blo 1829616 6265387 := bstep (se 1 (by rfl) ⟨4699040, by rfl⟩ : syracuseStep 6265387 = 9398081) B9398081
theorem B5863997 : Blo 1829616 5863997 := bstep (se 3 (by rfl) ⟨1099499, by rfl⟩ : syracuseStep 5863997 = 2198999) B2198999
theorem B15645251 : Blo 1829616 15645251 := bstep (se 1 (by rfl) ⟨11733938, by rfl⟩ : syracuseStep 15645251 = 23467877) B23467877
theorem B2316919 : Blo 1829616 2316919 := bstep (se 1 (by rfl) ⟨1737689, by rfl⟩ : syracuseStep 2316919 = 3475379) B3475379
theorem B30489281 : Blo 1829616 30489281 := bstep (se 2 (by rfl) ⟨11433480, by rfl⟩ : syracuseStep 30489281 = 22866961) B22866961
theorem B4635407 : Blo 1829616 4635407 := bstep (se 1 (by rfl) ⟨3476555, by rfl⟩ : syracuseStep 4635407 = 6953111) B6953111
theorem B2931499 : Blo 1829616 2931499 := bstep (se 1 (by rfl) ⟨2198624, by rfl⟩ : syracuseStep 2931499 = 4397249) B4397249
theorem B6175547 : Blo 1829616 6175547 := bstep (se 1 (by rfl) ⟨4631660, by rfl⟩ : syracuseStep 6175547 = 9263321) B9263321
theorem B17832793 : Blo 1829616 17832793 := bstep (se 2 (by rfl) ⟨6687297, by rfl⟩ : syracuseStep 17832793 = 13374595) B13374595
theorem B10427251 : Blo 1829616 10427251 := bstep (se 1 (by rfl) ⟨7820438, by rfl⟩ : syracuseStep 10427251 = 15640877) B15640877
theorem B4119443 : Blo 1829616 4119443 := bstep (se 1 (by rfl) ⟨3089582, by rfl⟩ : syracuseStep 4119443 = 6179165) B6179165
theorem B4635539 : Blo 1829616 4635539 := bstep (se 1 (by rfl) ⟨3476654, by rfl⟩ : syracuseStep 4635539 = 6953309) B6953309
theorem B2317243 : Blo 1829616 2317243 := bstep (se 1 (by rfl) ⟨1737932, by rfl⟩ : syracuseStep 2317243 = 3475865) B3475865
theorem B4119497 : Blo 1829616 4119497 := bstep (se 2 (by rfl) ⟨1544811, by rfl⟩ : syracuseStep 4119497 = 3089623) B3089623
theorem B9264131 : Blo 1829616 9264131 := bstep (se 1 (by rfl) ⟨6948098, by rfl⟩ : syracuseStep 9264131 = 13896197) B13896197
theorem B3709967 : Blo 1829616 3709967 := bstep (se 1 (by rfl) ⟨2782475, by rfl⟩ : syracuseStep 3709967 = 5564951) B5564951
theorem B5864509 : Blo 1829616 5864509 := bstep (se 3 (by rfl) ⟨1099595, by rfl⟩ : syracuseStep 5864509 = 2199191) B2199191
theorem B6176033 : Blo 1829616 6176033 := bstep (se 2 (by rfl) ⟨2316012, by rfl⟩ : syracuseStep 6176033 = 4632025) B4632025
theorem B3087659 : Blo 1829616 3087659 := bstep (se 1 (by rfl) ⟨2315744, by rfl⟩ : syracuseStep 3087659 = 4631489) B4631489
theorem B96443693 : Blo 1829616 96443693 := bstep (se 3 (by rfl) ⟨18083192, by rfl⟩ : syracuseStep 96443693 = 36166385) B36166385
theorem B9895321 : Blo 1829616 9895321 := bstep (se 2 (by rfl) ⟨3710745, by rfl⟩ : syracuseStep 9895321 = 7421491) B7421491
theorem B2784811 : Blo 1829616 2784811 := bstep (se 1 (by rfl) ⟨2088608, by rfl⟩ : syracuseStep 2784811 = 4177217) B4177217
theorem B4120199 : Blo 1829616 4120199 := bstep (se 1 (by rfl) ⟨3090149, by rfl⟩ : syracuseStep 4120199 = 6180299) B6180299
theorem B3088057 : Blo 1829616 3088057 := bstep (se 2 (by rfl) ⟨1158021, by rfl⟩ : syracuseStep 3088057 = 2316043) B2316043
theorem B2932409 : Blo 1829616 2932409 := bstep (se 2 (by rfl) ⟨1099653, by rfl⟩ : syracuseStep 2932409 = 2199307) B2199307
theorem B7823105 : Blo 1829616 7823105 := bstep (se 2 (by rfl) ⟨2933664, by rfl⟩ : syracuseStep 7823105 = 5867329) B5867329
theorem B4120379 : Blo 1829616 4120379 := bstep (se 1 (by rfl) ⟨3090284, by rfl⟩ : syracuseStep 4120379 = 6180569) B6180569
theorem B6176627 : Blo 1829616 6176627 := bstep (se 1 (by rfl) ⟨4632470, by rfl⟩ : syracuseStep 6176627 = 9264941) B9264941
theorem B6684551 : Blo 1829616 6684551 := bstep (se 1 (by rfl) ⟨5013413, by rfl⟩ : syracuseStep 6684551 = 10026827) B10026827
theorem B4120505 : Blo 1829616 4120505 := bstep (se 2 (by rfl) ⟨1545189, by rfl⟩ : syracuseStep 4120505 = 3090379) B3090379
theorem B4120595 : Blo 1829616 4120595 := bstep (se 1 (by rfl) ⟨3090446, by rfl⟩ : syracuseStep 4120595 = 6180893) B6180893
theorem B5865625 : Blo 1829616 5865625 := bstep (se 2 (by rfl) ⟨2199609, by rfl⟩ : syracuseStep 5865625 = 4399219) B4399219
theorem B3473579 : Blo 1829616 3473579 := bstep (se 1 (by rfl) ⟨2605184, by rfl⟩ : syracuseStep 3473579 = 5210369) B5210369
theorem B2744519 : Blo 1829616 2744519 := bstep (se 1 (by rfl) ⟨2058389, by rfl⟩ : syracuseStep 2744519 = 4116779) B4116779
theorem B23445733 : Blo 1829616 23445733 := bstep (se 4 (by rfl) ⟨2198037, by rfl⟩ : syracuseStep 23445733 = 4396075) B4396075
theorem B3088631 : Blo 1829616 3088631 := bstep (se 1 (by rfl) ⟨2316473, by rfl⟩ : syracuseStep 3088631 = 4632947) B4632947
theorem B2744681 : Blo 1829616 2744681 := bstep (se 2 (by rfl) ⟨1029255, by rfl⟩ : syracuseStep 2744681 = 2058511) B2058511
theorem B4120937 : Blo 1829616 4120937 := bstep (se 2 (by rfl) ⟨1545351, by rfl⟩ : syracuseStep 4120937 = 3090703) B3090703
theorem B6177167 : Blo 1829616 6177167 := bstep (se 1 (by rfl) ⟨4632875, by rfl⟩ : syracuseStep 6177167 = 9265751) B9265751
theorem B3670447 : Blo 1829616 3670447 := bstep (se 1 (by rfl) ⟨2752835, by rfl⟩ : syracuseStep 3670447 = 5505671) B5505671
theorem B2744759 : Blo 1829616 2744759 := bstep (se 1 (by rfl) ⟨2058569, by rfl⟩ : syracuseStep 2744759 = 4117139) B4117139
theorem B14852555 : Blo 1829616 14852555 := bstep (se 1 (by rfl) ⟨11139416, by rfl⟩ : syracuseStep 14852555 = 22278833) B22278833
theorem B2744795 : Blo 1829616 2744795 := bstep (se 1 (by rfl) ⟨2058596, by rfl⟩ : syracuseStep 2744795 = 4117193) B4117193
theorem B6947309 : Blo 1829616 6947309 := bstep (se 3 (by rfl) ⟨1302620, by rfl⟩ : syracuseStep 6947309 = 2605241) B2605241
theorem B2933255 : Blo 1829616 2933255 := bstep (se 1 (by rfl) ⟨2199941, by rfl⟩ : syracuseStep 2933255 = 4399883) B4399883
theorem B47538713 : Blo 1829616 47538713 := bstep (se 2 (by rfl) ⟨17827017, by rfl⟩ : syracuseStep 47538713 = 35654035) B35654035
theorem B3908135 : Blo 1829616 3908135 := bstep (se 1 (by rfl) ⟨2931101, by rfl⟩ : syracuseStep 3908135 = 5862203) B5862203
theorem B3088975 : Blo 1829616 3088975 := bstep (se 1 (by rfl) ⟨2316731, by rfl⟩ : syracuseStep 3088975 = 4633463) B4633463
theorem B6177491 : Blo 1829616 6177491 := bstep (se 1 (by rfl) ⟨4633118, by rfl⟩ : syracuseStep 6177491 = 9266237) B9266237
theorem B3089225 : Blo 1829616 3089225 := bstep (se 2 (by rfl) ⟨1158459, by rfl⟩ : syracuseStep 3089225 = 2316919) B2316919
theorem B2745263 : Blo 1829616 2745263 := bstep (se 1 (by rfl) ⟨2058947, by rfl⟩ : syracuseStep 2745263 = 4117895) B4117895
theorem B2933767 : Blo 1829616 2933767 := bstep (se 1 (by rfl) ⟨2200325, by rfl⟩ : syracuseStep 2933767 = 4400651) B4400651
theorem B2745353 : Blo 1829616 2745353 := bstep (se 2 (by rfl) ⟨1029507, by rfl⟩ : syracuseStep 2745353 = 2059015) B2059015
theorem B15631379 : Blo 1829616 15631379 := bstep (se 1 (by rfl) ⟨11723534, by rfl⟩ : syracuseStep 15631379 = 23447069) B23447069
theorem B5211155 : Blo 1829616 5211155 := bstep (se 1 (by rfl) ⟨3908366, by rfl⟩ : syracuseStep 5211155 = 7816733) B7816733
theorem B2745383 : Blo 1829616 2745383 := bstep (se 1 (by rfl) ⟨2059037, by rfl⟩ : syracuseStep 2745383 = 4118075) B4118075
theorem B3908665 : Blo 1829616 3908665 := bstep (se 2 (by rfl) ⟨1465749, by rfl⟩ : syracuseStep 3908665 = 2931499) B2931499
theorem B15852611 : Blo 1829616 15852611 := bstep (se 1 (by rfl) ⟨11889458, by rfl⟩ : syracuseStep 15852611 = 23778917) B23778917
theorem B2745467 : Blo 1829616 2745467 := bstep (se 1 (by rfl) ⟨2059100, by rfl⟩ : syracuseStep 2745467 = 4118201) B4118201
theorem B13903001 : Blo 1829616 13903001 := bstep (se 2 (by rfl) ⟨5213625, by rfl⟩ : syracuseStep 13903001 = 10427251) B10427251
theorem B10421419 : Blo 1829616 10421419 := bstep (se 1 (by rfl) ⟨7816064, by rfl⟩ : syracuseStep 10421419 = 15632129) B15632129
theorem B3343531 : Blo 1829616 3343531 := bstep (se 1 (by rfl) ⟨2507648, by rfl⟩ : syracuseStep 3343531 = 5015297) B5015297
theorem B2745593 : Blo 1829616 2745593 := bstep (se 2 (by rfl) ⟨1029597, by rfl⟩ : syracuseStep 2745593 = 2059195) B2059195
theorem B3089657 : Blo 1829616 3089657 := bstep (se 2 (by rfl) ⟨1158621, by rfl⟩ : syracuseStep 3089657 = 2317243) B2317243
theorem B2745695 : Blo 1829616 2745695 := bstep (se 1 (by rfl) ⟨2059271, by rfl⟩ : syracuseStep 2745695 = 4118543) B4118543
theorem B2745707 : Blo 1829616 2745707 := bstep (se 1 (by rfl) ⟨2059280, by rfl⟩ : syracuseStep 2745707 = 4118561) B4118561
theorem B3089839 : Blo 1829616 3089839 := bstep (se 1 (by rfl) ⟨2317379, by rfl⟩ : syracuseStep 3089839 = 4634759) B4634759
theorem B61007305 : Blo 1829616 61007305 := bstep (se 2 (by rfl) ⟨22877739, by rfl⟩ : syracuseStep 61007305 = 45755479) B45755479
theorem B5211611 : Blo 1829616 5211611 := bstep (se 1 (by rfl) ⟨3908708, by rfl⟩ : syracuseStep 5211611 = 7817417) B7817417
theorem B11134427 : Blo 1829616 11134427 := bstep (se 1 (by rfl) ⟨8350820, by rfl⟩ : syracuseStep 11134427 = 16701641) B16701641
theorem B3089927 : Blo 1829616 3089927 := bstep (se 1 (by rfl) ⟨2317445, by rfl⟩ : syracuseStep 3089927 = 4634891) B4634891
theorem B2745935 : Blo 1829616 2745935 := bstep (se 1 (by rfl) ⟨2059451, by rfl⟩ : syracuseStep 2745935 = 4118903) B4118903
theorem B2606671 : Blo 1829616 2606671 := bstep (se 1 (by rfl) ⟨1955003, by rfl⟩ : syracuseStep 2606671 = 3910007) B3910007
theorem B15042145 : Blo 1829616 15042145 := bstep (se 2 (by rfl) ⟨5640804, by rfl⟩ : syracuseStep 15042145 = 11281609) B11281609
theorem B6948449 : Blo 1829616 6948449 := bstep (se 2 (by rfl) ⟨2605668, by rfl⟩ : syracuseStep 6948449 = 5211337) B5211337
theorem B2746055 : Blo 1829616 2746055 := bstep (se 1 (by rfl) ⟨2059541, by rfl⟩ : syracuseStep 2746055 = 4119083) B4119083
theorem B3909331 : Blo 1829616 3909331 := bstep (se 1 (by rfl) ⟨2931998, by rfl⟩ : syracuseStep 3909331 = 5863997) B5863997
theorem B10430167 : Blo 1829616 10430167 := bstep (se 1 (by rfl) ⟨7822625, by rfl⟩ : syracuseStep 10430167 = 15645251) B15645251
theorem B20326187 : Blo 1829616 20326187 := bstep (se 1 (by rfl) ⟨15244640, by rfl⟩ : syracuseStep 20326187 = 30489281) B30489281
theorem B3475295 : Blo 1829616 3475295 := bstep (se 1 (by rfl) ⟨2606471, by rfl⟩ : syracuseStep 3475295 = 5212943) B5212943
theorem B3090271 : Blo 1829616 3090271 := bstep (se 1 (by rfl) ⟨2317703, by rfl⟩ : syracuseStep 3090271 = 4635407) B4635407
theorem B2746217 : Blo 1829616 2746217 := bstep (se 2 (by rfl) ⟨1029831, by rfl⟩ : syracuseStep 2746217 = 2059663) B2059663
theorem B6178679 : Blo 1829616 6178679 := bstep (se 1 (by rfl) ⟨4634009, by rfl⟩ : syracuseStep 6178679 = 9268019) B9268019
theorem B31287221 : Blo 1829616 31287221 := bstep (se 5 (by rfl) ⟨1466588, by rfl⟩ : syracuseStep 31287221 = 2933177) B2933177
theorem B2746295 : Blo 1829616 2746295 := bstep (se 1 (by rfl) ⟨2059721, by rfl⟩ : syracuseStep 2746295 = 4119443) B4119443
theorem B3090359 : Blo 1829616 3090359 := bstep (se 1 (by rfl) ⟨2317769, by rfl⟩ : syracuseStep 3090359 = 4635539) B4635539
theorem B18778061 : Blo 1829616 18778061 := bstep (se 3 (by rfl) ⟨3520886, by rfl⟩ : syracuseStep 18778061 = 7041773) B7041773
theorem B25061329 : Blo 1829616 25061329 := bstep (se 2 (by rfl) ⟨9397998, by rfl⟩ : syracuseStep 25061329 = 18795997) B18795997
theorem B2746331 : Blo 1829616 2746331 := bstep (se 1 (by rfl) ⟨2059748, by rfl⟩ : syracuseStep 2746331 = 4119497) B4119497
theorem B3713081 : Blo 1829616 3713081 := bstep (se 2 (by rfl) ⟨1392405, by rfl⟩ : syracuseStep 3713081 = 2784811) B2784811
theorem B6178895 : Blo 1829616 6178895 := bstep (se 1 (by rfl) ⟨4634171, by rfl⟩ : syracuseStep 6178895 = 9268343) B9268343
theorem B2058439 : Blo 1829616 2058439 := bstep (se 1 (by rfl) ⟨1543829, by rfl⟩ : syracuseStep 2058439 = 3087659) B3087659
theorem B3475705 : Blo 1829616 3475705 := bstep (se 2 (by rfl) ⟨1303389, by rfl⟩ : syracuseStep 3475705 = 2606779) B2606779
theorem B3762425 : Blo 1829616 3762425 := bstep (se 2 (by rfl) ⟨1410909, by rfl⟩ : syracuseStep 3762425 = 2821819) B2821819
theorem B2746799 : Blo 1829616 2746799 := bstep (se 1 (by rfl) ⟨2060099, by rfl⟩ : syracuseStep 2746799 = 4120199) B4120199
theorem B6179273 : Blo 1829616 6179273 := bstep (se 2 (by rfl) ⟨2317227, by rfl⟩ : syracuseStep 6179273 = 4634455) B4634455
theorem B2746889 : Blo 1829616 2746889 := bstep (se 2 (by rfl) ⟨1030083, by rfl⟩ : syracuseStep 2746889 = 2060167) B2060167
theorem B2746919 : Blo 1829616 2746919 := bstep (se 1 (by rfl) ⟨2060189, by rfl⟩ : syracuseStep 2746919 = 4120379) B4120379
theorem B6949435 : Blo 1829616 6949435 := bstep (se 1 (by rfl) ⟨5212076, by rfl⟩ : syracuseStep 6949435 = 10424153) B10424153
theorem B3476047 : Blo 1829616 3476047 := bstep (se 1 (by rfl) ⟨2607035, by rfl⟩ : syracuseStep 3476047 = 5214071) B5214071
theorem B5212795 : Blo 1829616 5212795 := bstep (se 1 (by rfl) ⟨3909596, by rfl⟩ : syracuseStep 5212795 = 7819193) B7819193
theorem B2747003 : Blo 1829616 2747003 := bstep (se 1 (by rfl) ⟨2060252, by rfl⟩ : syracuseStep 2747003 = 4120505) B4120505
theorem B6179543 : Blo 1829616 6179543 := bstep (se 1 (by rfl) ⟨4634657, by rfl⟩ : syracuseStep 6179543 = 9269315) B9269315
theorem B2747129 : Blo 1829616 2747129 := bstep (se 2 (by rfl) ⟨1030173, by rfl⟩ : syracuseStep 2747129 = 2060347) B2060347
theorem B1829671 : Blo 1829616 1829671 := bstep (se 1 (by rfl) ⟨1372253, by rfl⟩ : syracuseStep 1829671 = 2744507) B2744507
theorem B3476297 : Blo 1829616 3476297 := bstep (se 2 (by rfl) ⟨1303611, by rfl⟩ : syracuseStep 3476297 = 2607223) B2607223
theorem B1829711 : Blo 1829616 1829711 := bstep (se 1 (by rfl) ⟨1372283, by rfl⟩ : syracuseStep 1829711 = 2744567) B2744567
theorem B1829727 : Blo 1829616 1829727 := bstep (se 1 (by rfl) ⟨1372295, by rfl⟩ : syracuseStep 1829727 = 2744591) B2744591
theorem B2747231 : Blo 1829616 2747231 := bstep (se 1 (by rfl) ⟨2060423, by rfl⟩ : syracuseStep 2747231 = 4120847) B4120847
theorem B6949739 : Blo 1829616 6949739 := bstep (se 1 (by rfl) ⟨5212304, by rfl⟩ : syracuseStep 6949739 = 10424609) B10424609
theorem B2747243 : Blo 1829616 2747243 := bstep (se 1 (by rfl) ⟨2060432, by rfl⟩ : syracuseStep 2747243 = 4120865) B4120865
theorem B1829755 : Blo 1829616 1829755 := bstep (se 1 (by rfl) ⟨1372316, by rfl⟩ : syracuseStep 1829755 = 2744633) B2744633
theorem B1829807 : Blo 1829616 1829807 := bstep (se 1 (by rfl) ⟨1372355, by rfl⟩ : syracuseStep 1829807 = 2744711) B2744711
theorem B6179759 : Blo 1829616 6179759 := bstep (se 1 (by rfl) ⟨4634819, by rfl⟩ : syracuseStep 6179759 = 9269639) B9269639
theorem B8801207 : Blo 1829616 8801207 := bstep (se 1 (by rfl) ⟨6600905, by rfl⟩ : syracuseStep 8801207 = 13201811) B13201811
theorem B1829831 : Blo 1829616 1829831 := bstep (se 1 (by rfl) ⟨1372373, by rfl⟩ : syracuseStep 1829831 = 2744747) B2744747
theorem B1829851 : Blo 1829616 1829851 := bstep (se 1 (by rfl) ⟨1372388, by rfl⟩ : syracuseStep 1829851 = 2744777) B2744777
theorem B18787301 : Blo 1829616 18787301 := bstep (se 4 (by rfl) ⟨1761309, by rfl⟩ : syracuseStep 18787301 = 3522619) B3522619
theorem B6949907 : Blo 1829616 6949907 := bstep (se 1 (by rfl) ⟨5212430, by rfl⟩ : syracuseStep 6949907 = 10424861) B10424861
theorem B1829927 : Blo 1829616 1829927 := bstep (se 1 (by rfl) ⟨1372445, by rfl⟩ : syracuseStep 1829927 = 2744891) B2744891
theorem B2059303 : Blo 1829616 2059303 := bstep (se 1 (by rfl) ⟨1544477, by rfl⟩ : syracuseStep 2059303 = 3088955) B3088955
theorem B13904945 : Blo 1829616 13904945 := bstep (se 2 (by rfl) ⟨5214354, by rfl⟩ : syracuseStep 13904945 = 10428709) B10428709
theorem B1829967 : Blo 1829616 1829967 := bstep (se 1 (by rfl) ⟨1372475, by rfl⟩ : syracuseStep 1829967 = 2744951) B2744951
theorem B1829983 : Blo 1829616 1829983 := bstep (se 1 (by rfl) ⟨1372487, by rfl⟩ : syracuseStep 1829983 = 2744975) B2744975
theorem B1830011 : Blo 1829616 1830011 := bstep (se 1 (by rfl) ⟨1372508, by rfl⟩ : syracuseStep 1830011 = 2745017) B2745017
theorem B1830063 : Blo 1829616 1830063 := bstep (se 1 (by rfl) ⟨1372547, by rfl⟩ : syracuseStep 1830063 = 2745095) B2745095
theorem B1830087 : Blo 1829616 1830087 := bstep (se 1 (by rfl) ⟨1372565, by rfl⟩ : syracuseStep 1830087 = 2745131) B2745131
theorem B1830107 : Blo 1829616 1830107 := bstep (se 1 (by rfl) ⟨1372580, by rfl⟩ : syracuseStep 1830107 = 2745161) B2745161
theorem B53472545 : Blo 1829616 53472545 := bstep (se 2 (by rfl) ⟨20052204, by rfl⟩ : syracuseStep 53472545 = 40104409) B40104409
theorem B1830183 : Blo 1829616 1830183 := bstep (se 1 (by rfl) ⟨1372637, by rfl⟩ : syracuseStep 1830183 = 2745275) B2745275
theorem B1830223 : Blo 1829616 1830223 := bstep (se 1 (by rfl) ⟨1372667, by rfl⟩ : syracuseStep 1830223 = 2745335) B2745335
theorem B1830239 : Blo 1829616 1830239 := bstep (se 1 (by rfl) ⟨1372679, by rfl⟩ : syracuseStep 1830239 = 2745359) B2745359
theorem B1830267 : Blo 1829616 1830267 := bstep (se 1 (by rfl) ⟨1372700, by rfl⟩ : syracuseStep 1830267 = 2745401) B2745401
theorem B8793517 : Blo 1829616 8793517 := bstep (se 3 (by rfl) ⟨1648784, by rfl⟩ : syracuseStep 8793517 = 3297569) B3297569
theorem B1830319 : Blo 1829616 1830319 := bstep (se 1 (by rfl) ⟨1372739, by rfl⟩ : syracuseStep 1830319 = 2745479) B2745479
theorem B1830343 : Blo 1829616 1830343 := bstep (se 1 (by rfl) ⟨1372757, by rfl⟩ : syracuseStep 1830343 = 2745515) B2745515
theorem B1830363 : Blo 1829616 1830363 := bstep (se 1 (by rfl) ⟨1372772, by rfl⟩ : syracuseStep 1830363 = 2745545) B2745545
theorem B1830439 : Blo 1829616 1830439 := bstep (se 1 (by rfl) ⟨1372829, by rfl⟩ : syracuseStep 1830439 = 2745659) B2745659
theorem B1830479 : Blo 1829616 1830479 := bstep (se 1 (by rfl) ⟨1372859, by rfl⟩ : syracuseStep 1830479 = 2745719) B2745719
theorem B1830495 : Blo 1829616 1830495 := bstep (se 1 (by rfl) ⟨1372871, by rfl⟩ : syracuseStep 1830495 = 2745743) B2745743
theorem B4632187 : Blo 1829616 4632187 := bstep (se 1 (by rfl) ⟨3474140, by rfl⟩ : syracuseStep 4632187 = 6948281) B6948281
theorem B15634043 : Blo 1829616 15634043 := bstep (se 1 (by rfl) ⟨11725532, by rfl⟩ : syracuseStep 15634043 = 23451065) B23451065
theorem B1830523 : Blo 1829616 1830523 := bstep (se 1 (by rfl) ⟨1372892, by rfl⟩ : syracuseStep 1830523 = 2745785) B2745785
theorem B2199163 : Blo 1829616 2199163 := bstep (se 1 (by rfl) ⟨1649372, by rfl⟩ : syracuseStep 2199163 = 3298745) B3298745
theorem B3477163 : Blo 1829616 3477163 := bstep (se 1 (by rfl) ⟨2607872, by rfl⟩ : syracuseStep 3477163 = 5215745) B5215745
theorem B1830575 : Blo 1829616 1830575 := bstep (se 1 (by rfl) ⟨1372931, by rfl⟩ : syracuseStep 1830575 = 2745863) B2745863
theorem B9891517 : Blo 1829616 9891517 := bstep (se 3 (by rfl) ⟨1854659, by rfl⟩ : syracuseStep 9891517 = 3709319) B3709319
theorem B1830599 : Blo 1829616 1830599 := bstep (se 1 (by rfl) ⟨1372949, by rfl⟩ : syracuseStep 1830599 = 2745899) B2745899
theorem B52760281 : Blo 1829616 52760281 := bstep (se 2 (by rfl) ⟨19785105, by rfl⟩ : syracuseStep 52760281 = 39570211) B39570211
theorem B1830619 : Blo 1829616 1830619 := bstep (se 1 (by rfl) ⟨1372964, by rfl⟩ : syracuseStep 1830619 = 2745929) B2745929
theorem B14847725 : Blo 1829616 14847725 := bstep (se 3 (by rfl) ⟨2783948, by rfl⟩ : syracuseStep 14847725 = 5567897) B5567897
theorem B5213945 : Blo 1829616 5213945 := bstep (se 2 (by rfl) ⟨1955229, by rfl⟩ : syracuseStep 5213945 = 3910459) B3910459
theorem B23777057 : Blo 1829616 23777057 := bstep (se 2 (by rfl) ⟨8916396, by rfl⟩ : syracuseStep 23777057 = 17832793) B17832793
theorem B1830695 : Blo 1829616 1830695 := bstep (se 1 (by rfl) ⟨1373021, by rfl⟩ : syracuseStep 1830695 = 2746043) B2746043
theorem B12693307 : Blo 1829616 12693307 := bstep (se 1 (by rfl) ⟨9519980, by rfl⟩ : syracuseStep 12693307 = 19039961) B19039961
theorem B1830735 : Blo 1829616 1830735 := bstep (se 1 (by rfl) ⟨1373051, by rfl⟩ : syracuseStep 1830735 = 2746103) B2746103
theorem B1830751 : Blo 1829616 1830751 := bstep (se 1 (by rfl) ⟨1373063, by rfl⟩ : syracuseStep 1830751 = 2746127) B2746127
theorem B2199403 : Blo 1829616 2199403 := bstep (se 1 (by rfl) ⟨1649552, by rfl⟩ : syracuseStep 2199403 = 3299105) B3299105
theorem B1830779 : Blo 1829616 1830779 := bstep (se 1 (by rfl) ⟨1373084, by rfl⟩ : syracuseStep 1830779 = 2746169) B2746169
theorem B9269153 : Blo 1829616 9269153 := bstep (se 2 (by rfl) ⟨3475932, by rfl⟩ : syracuseStep 9269153 = 6951865) B6951865
theorem B1830831 : Blo 1829616 1830831 := bstep (se 1 (by rfl) ⟨1373123, by rfl⟩ : syracuseStep 1830831 = 2746247) B2746247
theorem B5214127 : Blo 1829616 5214127 := bstep (se 1 (by rfl) ⟨3910595, by rfl⟩ : syracuseStep 5214127 = 7821191) B7821191
theorem B1830855 : Blo 1829616 1830855 := bstep (se 1 (by rfl) ⟨1373141, by rfl⟩ : syracuseStep 1830855 = 2746283) B2746283
theorem B1830875 : Blo 1829616 1830875 := bstep (se 1 (by rfl) ⟨1373156, by rfl⟩ : syracuseStep 1830875 = 2746313) B2746313
theorem B10424335 : Blo 1829616 10424335 := bstep (se 1 (by rfl) ⟨7818251, by rfl⟩ : syracuseStep 10424335 = 15636503) B15636503
theorem B1830951 : Blo 1829616 1830951 := bstep (se 1 (by rfl) ⟨1373213, by rfl⟩ : syracuseStep 1830951 = 2746427) B2746427
theorem B1830991 : Blo 1829616 1830991 := bstep (se 1 (by rfl) ⟨1373243, by rfl⟩ : syracuseStep 1830991 = 2746487) B2746487
theorem B5214287 : Blo 1829616 5214287 := bstep (se 1 (by rfl) ⟨3910715, by rfl⟩ : syracuseStep 5214287 = 7821431) B7821431
theorem B7819345 : Blo 1829616 7819345 := bstep (se 2 (by rfl) ⟨2932254, by rfl⟩ : syracuseStep 7819345 = 5864509) B5864509
theorem B1831007 : Blo 1829616 1831007 := bstep (se 1 (by rfl) ⟨1373255, by rfl⟩ : syracuseStep 1831007 = 2746511) B2746511
theorem B1831035 : Blo 1829616 1831035 := bstep (se 1 (by rfl) ⟨1373276, by rfl⟩ : syracuseStep 1831035 = 2746553) B2746553
theorem B1831087 : Blo 1829616 1831087 := bstep (se 1 (by rfl) ⟨1373315, by rfl⟩ : syracuseStep 1831087 = 2746631) B2746631
theorem B1953991 : Blo 1829616 1953991 := bstep (se 1 (by rfl) ⟨1465493, by rfl⟩ : syracuseStep 1953991 = 2930987) B2930987
theorem B1831111 : Blo 1829616 1831111 := bstep (se 1 (by rfl) ⟨1373333, by rfl⟩ : syracuseStep 1831111 = 2746667) B2746667
theorem B1831131 : Blo 1829616 1831131 := bstep (se 1 (by rfl) ⟨1373348, by rfl⟩ : syracuseStep 1831131 = 2746697) B2746697
theorem B1831207 : Blo 1829616 1831207 := bstep (se 1 (by rfl) ⟨1373405, by rfl⟩ : syracuseStep 1831207 = 2746811) B2746811
theorem B25063739 : Blo 1829616 25063739 := bstep (se 1 (by rfl) ⟨18797804, by rfl⟩ : syracuseStep 25063739 = 37595609) B37595609
theorem B1831247 : Blo 1829616 1831247 := bstep (se 1 (by rfl) ⟨1373435, by rfl⟩ : syracuseStep 1831247 = 2746871) B2746871
theorem B1831263 : Blo 1829616 1831263 := bstep (se 1 (by rfl) ⟨1373447, by rfl⟩ : syracuseStep 1831263 = 2746895) B2746895
theorem B1831291 : Blo 1829616 1831291 := bstep (se 1 (by rfl) ⟨1373468, by rfl⟩ : syracuseStep 1831291 = 2746937) B2746937
theorem B1831343 : Blo 1829616 1831343 := bstep (se 1 (by rfl) ⟨1373507, by rfl⟩ : syracuseStep 1831343 = 2747015) B2747015
theorem B1831367 : Blo 1829616 1831367 := bstep (se 1 (by rfl) ⟨1373525, by rfl⟩ : syracuseStep 1831367 = 2747051) B2747051
theorem B1831387 : Blo 1829616 1831387 := bstep (se 1 (by rfl) ⟨1373540, by rfl⟩ : syracuseStep 1831387 = 2747081) B2747081
theorem B13193761 : Blo 1829616 13193761 := bstep (se 2 (by rfl) ⟨4947660, by rfl⟩ : syracuseStep 13193761 = 9895321) B9895321
theorem B4117031 : Blo 1829616 4117031 := bstep (se 1 (by rfl) ⟨3087773, by rfl⟩ : syracuseStep 4117031 = 6175547) B6175547
theorem B1831463 : Blo 1829616 1831463 := bstep (se 1 (by rfl) ⟨1373597, by rfl⟩ : syracuseStep 1831463 = 2747195) B2747195
theorem B1831503 : Blo 1829616 1831503 := bstep (se 1 (by rfl) ⟨1373627, by rfl⟩ : syracuseStep 1831503 = 2747255) B2747255
theorem B1831519 : Blo 1829616 1831519 := bstep (se 1 (by rfl) ⟨1373639, by rfl⟩ : syracuseStep 1831519 = 2747279) B2747279
theorem B1831547 : Blo 1829616 1831547 := bstep (se 1 (by rfl) ⟨1373660, by rfl⟩ : syracuseStep 1831547 = 2747321) B2747321
theorem B1831599 : Blo 1829616 1831599 := bstep (se 1 (by rfl) ⟨1373699, by rfl⟩ : syracuseStep 1831599 = 2747399) B2747399
theorem B4117355 : Blo 1829616 4117355 := bstep (se 1 (by rfl) ⟨3088016, by rfl⟩ : syracuseStep 4117355 = 6176033) B6176033
theorem B64295795 : Blo 1829616 64295795 := bstep (se 1 (by rfl) ⟨48221846, by rfl⟩ : syracuseStep 64295795 = 96443693) B96443693
theorem B4117409 : Blo 1829616 4117409 := bstep (se 2 (by rfl) ⟨1544028, by rfl⟩ : syracuseStep 4117409 = 3088057) B3088057
theorem B13382657 : Blo 1829616 13382657 := bstep (se 2 (by rfl) ⟨5018496, by rfl⟩ : syracuseStep 13382657 = 10036993) B10036993
theorem B1954939 : Blo 1829616 1954939 := bstep (se 1 (by rfl) ⟨1466204, by rfl⟩ : syracuseStep 1954939 = 2932409) B2932409
theorem B5215403 : Blo 1829616 5215403 := bstep (se 1 (by rfl) ⟨3911552, by rfl⟩ : syracuseStep 5215403 = 7823105) B7823105
theorem B4117751 : Blo 1829616 4117751 := bstep (se 1 (by rfl) ⟨3088313, by rfl⟩ : syracuseStep 4117751 = 6176627) B6176627
theorem B44545295 : Blo 1829616 44545295 := bstep (se 1 (by rfl) ⟨33408971, by rfl⟩ : syracuseStep 44545295 = 66817943) B66817943
theorem B23459219 : Blo 1829616 23459219 := bstep (se 1 (by rfl) ⟨17594414, by rfl⟩ : syracuseStep 23459219 = 35188829) B35188829
theorem B2381239 : Blo 1829616 2381239 := bstep (se 1 (by rfl) ⟨1785929, by rfl⟩ : syracuseStep 2381239 = 3571859) B3571859
theorem B39572981 : Blo 1829616 39572981 := bstep (se 5 (by rfl) ⟨1854983, by rfl⟩ : syracuseStep 39572981 = 3709967) B3709967
theorem B30086801 : Blo 1829616 30086801 := bstep (se 2 (by rfl) ⟨11282550, by rfl⟩ : syracuseStep 30086801 = 22565101) B22565101
theorem B11130583 : Blo 1829616 11130583 := bstep (se 1 (by rfl) ⟨8347937, by rfl⟩ : syracuseStep 11130583 = 16695875) B16695875
theorem B4118345 : Blo 1829616 4118345 := bstep (se 2 (by rfl) ⟨1544379, by rfl⟩ : syracuseStep 4118345 = 3088759) B3088759
theorem B6952823 : Blo 1829616 6952823 := bstep (se 1 (by rfl) ⟨5214617, by rfl⟩ : syracuseStep 6952823 = 10429235) B10429235
theorem B1955759 : Blo 1829616 1955759 := bstep (se 1 (by rfl) ⟨1466819, by rfl⟩ : syracuseStep 1955759 = 2933639) B2933639
theorem B2316215 : Blo 1829616 2316215 := bstep (se 1 (by rfl) ⟨1737161, by rfl⟩ : syracuseStep 2316215 = 3474323) B3474323
theorem B21133315 : Blo 1829616 21133315 := bstep (se 1 (by rfl) ⟨15849986, by rfl⟩ : syracuseStep 21133315 = 31699973) B31699973
theorem B8353849 : Blo 1829616 8353849 := bstep (se 2 (by rfl) ⟨3132693, by rfl⟩ : syracuseStep 8353849 = 6265387) B6265387
theorem B2316367 : Blo 1829616 2316367 := bstep (se 1 (by rfl) ⟨1737275, by rfl⟩ : syracuseStep 2316367 = 3474551) B3474551
theorem B2087035 : Blo 1829616 2087035 := bstep (se 1 (by rfl) ⟨1565276, by rfl⟩ : syracuseStep 2087035 = 3130553) B3130553
theorem B7420099 : Blo 1829616 7420099 := bstep (se 1 (by rfl) ⟨5565074, by rfl⟩ : syracuseStep 7420099 = 11130149) B11130149
theorem B13195493 : Blo 1829616 13195493 := bstep (se 4 (by rfl) ⟨1237077, by rfl⟩ : syracuseStep 13195493 = 2474155) B2474155
theorem B6265307 : Blo 1829616 6265307 := bstep (se 1 (by rfl) ⟨4698980, by rfl⟩ : syracuseStep 6265307 = 9397961) B9397961
theorem B4119137 : Blo 1829616 4119137 := bstep (se 2 (by rfl) ⟨1544676, by rfl⟩ : syracuseStep 4119137 = 3089353) B3089353
theorem B6953795 : Blo 1829616 6953795 := bstep (se 1 (by rfl) ⟨5215346, by rfl⟩ : syracuseStep 6953795 = 10430693) B10430693
theorem B26385335 : Blo 1829616 26385335 := bstep (se 1 (by rfl) ⟨19789001, by rfl⟩ : syracuseStep 26385335 = 39578003) B39578003
theorem B4119479 : Blo 1829616 4119479 := bstep (se 1 (by rfl) ⟨3089609, by rfl⟩ : syracuseStep 4119479 = 6179219) B6179219
theorem B6175763 : Blo 1829616 6175763 := bstep (se 1 (by rfl) ⟨4631822, by rfl⟩ : syracuseStep 6175763 = 9263645) B9263645
theorem B7822489 : Blo 1829616 7822489 := bstep (se 2 (by rfl) ⟨2933433, by rfl⟩ : syracuseStep 7822489 = 5866867) B5866867
theorem B4947101 : Blo 1829616 4947101 := bstep (se 3 (by rfl) ⟨927581, by rfl⟩ : syracuseStep 4947101 = 1855163) B1855163
theorem B44547245 : Blo 1829616 44547245 := bstep (se 3 (by rfl) ⟨8352608, by rfl⟩ : syracuseStep 44547245 = 16705217) B16705217
theorem B2317511 : Blo 1829616 2317511 := bstep (se 1 (by rfl) ⟨1738133, by rfl⟩ : syracuseStep 2317511 = 3476267) B3476267
theorem B6176087 : Blo 1829616 6176087 := bstep (se 1 (by rfl) ⟨4632065, by rfl⟩ : syracuseStep 6176087 = 9264131) B9264131
theorem B2317663 : Blo 1829616 2317663 := bstep (se 1 (by rfl) ⟨1738247, by rfl⟩ : syracuseStep 2317663 = 3476495) B3476495
theorem B4398479 : Blo 1829616 4398479 := bstep (se 1 (by rfl) ⟨3298859, by rfl⟩ : syracuseStep 4398479 = 6597719) B6597719
theorem B4120073 : Blo 1829616 4120073 := bstep (se 2 (by rfl) ⟨1545027, by rfl⟩ : syracuseStep 4120073 = 3090055) B3090055
theorem B3087929 : Blo 1829616 3087929 := bstep (se 2 (by rfl) ⟨1157973, by rfl⟩ : syracuseStep 3087929 = 2315947) B2315947
theorem B9264779 : Blo 1829616 9264779 := bstep (se 1 (by rfl) ⟨6948584, by rfl⟩ : syracuseStep 9264779 = 13897169) B13897169
theorem B8797841 : Blo 1829616 8797841 := bstep (se 2 (by rfl) ⟨3299190, by rfl⟩ : syracuseStep 8797841 = 6598381) B6598381
theorem B4120415 : Blo 1829616 4120415 := bstep (se 1 (by rfl) ⟨3090311, by rfl⟩ : syracuseStep 4120415 = 6180623) B6180623
theorem B4456367 : Blo 1829616 4456367 := bstep (se 1 (by rfl) ⟨3342275, by rfl⟩ : syracuseStep 4456367 = 6684551) B6684551
theorem B3088489 : Blo 1829616 3088489 := bstep (se 2 (by rfl) ⟨1158183, by rfl⟩ : syracuseStep 3088489 = 2316367) B2316367
theorem B2744585 : Blo 1829616 2744585 := bstep (se 2 (by rfl) ⟨1029219, by rfl⟩ : syracuseStep 2744585 = 2058439) B2058439
theorem B2605321 : Blo 1829616 2605321 := bstep (se 2 (by rfl) ⟨976995, by rfl⟩ : syracuseStep 2605321 = 1953991) B1953991
theorem B31260977 : Blo 1829616 31260977 := bstep (se 2 (by rfl) ⟨11722866, by rfl⟩ : syracuseStep 31260977 = 23445733) B23445733
theorem B2744687 : Blo 1829616 2744687 := bstep (se 1 (by rfl) ⟨2058515, by rfl⟩ : syracuseStep 2744687 = 4117031) B4117031
theorem B2744903 : Blo 1829616 2744903 := bstep (se 1 (by rfl) ⟨2058677, by rfl⟩ : syracuseStep 2744903 = 4117355) B4117355
theorem B2744939 : Blo 1829616 2744939 := bstep (se 1 (by rfl) ⟨2058704, by rfl⟩ : syracuseStep 2744939 = 4117409) B4117409
theorem B8921771 : Blo 1829616 8921771 := bstep (se 1 (by rfl) ⟨6691328, by rfl⟩ : syracuseStep 8921771 = 13382657) B13382657
theorem B10420919 : Blo 1829616 10420919 := bstep (se 1 (by rfl) ⟨7815689, by rfl⟩ : syracuseStep 10420919 = 15631379) B15631379
theorem B3474103 : Blo 1829616 3474103 := bstep (se 1 (by rfl) ⟨2605577, by rfl⟩ : syracuseStep 3474103 = 5211155) B5211155
theorem B10568407 : Blo 1829616 10568407 := bstep (se 1 (by rfl) ⟨7926305, by rfl⟩ : syracuseStep 10568407 = 15852611) B15852611
theorem B9265913 : Blo 1829616 9265913 := bstep (se 2 (by rfl) ⟨3474717, by rfl⟩ : syracuseStep 9265913 = 6949435) B6949435
theorem B2745167 : Blo 1829616 2745167 := bstep (se 1 (by rfl) ⟨2058875, by rfl⟩ : syracuseStep 2745167 = 4117751) B4117751
theorem B29696863 : Blo 1829616 29696863 := bstep (se 1 (by rfl) ⟨22272647, by rfl⟩ : syracuseStep 29696863 = 44545295) B44545295
theorem B15639479 : Blo 1829616 15639479 := bstep (se 1 (by rfl) ⟨11729609, by rfl⟩ : syracuseStep 15639479 = 23459219) B23459219
theorem B3474407 : Blo 1829616 3474407 := bstep (se 1 (by rfl) ⟨2605805, by rfl⟩ : syracuseStep 3474407 = 5211611) B5211611
theorem B2745563 : Blo 1829616 2745563 := bstep (se 1 (by rfl) ⟨2059172, by rfl⟩ : syracuseStep 2745563 = 4118345) B4118345
theorem B20858147 : Blo 1829616 20858147 := bstep (se 1 (by rfl) ⟨15643610, by rfl⟩ : syracuseStep 20858147 = 31287221) B31287221
theorem B12518707 : Blo 1829616 12518707 := bstep (se 1 (by rfl) ⟨9389030, by rfl⟩ : syracuseStep 12518707 = 18778061) B18778061
theorem B2745737 : Blo 1829616 2745737 := bstep (se 2 (by rfl) ⟨1029651, by rfl⟩ : syracuseStep 2745737 = 2059303) B2059303
theorem B5211553 : Blo 1829616 5211553 := bstep (se 2 (by rfl) ⟨1954332, by rfl⟩ : syracuseStep 5211553 = 3908665) B3908665
theorem B10421693 : Blo 1829616 10421693 := bstep (se 3 (by rfl) ⟨1954067, by rfl⟩ : syracuseStep 10421693 = 3908135) B3908135
theorem B2606585 : Blo 1829616 2606585 := bstep (se 2 (by rfl) ⟨977469, by rfl⟩ : syracuseStep 2606585 = 1954939) B1954939
theorem B2508283 : Blo 1829616 2508283 := bstep (se 1 (by rfl) ⟨1881212, by rfl⟩ : syracuseStep 2508283 = 3762425) B3762425
theorem B10429985 : Blo 1829616 10429985 := bstep (se 2 (by rfl) ⟨3911244, by rfl⟩ : syracuseStep 10429985 = 7822489) B7822489
theorem B13895225 : Blo 1829616 13895225 := bstep (se 2 (by rfl) ⟨5210709, by rfl⟩ : syracuseStep 13895225 = 10421419) B10421419
theorem B4458041 : Blo 1829616 4458041 := bstep (se 2 (by rfl) ⟨1671765, by rfl⟩ : syracuseStep 4458041 = 3343531) B3343531
theorem B2746091 : Blo 1829616 2746091 := bstep (se 1 (by rfl) ⟨2059568, by rfl⟩ : syracuseStep 2746091 = 4119137) B4119137
theorem B3090217 : Blo 1829616 3090217 := bstep (se 2 (by rfl) ⟨1158831, by rfl⟩ : syracuseStep 3090217 = 2317663) B2317663
theorem B11724689 : Blo 1829616 11724689 := bstep (se 2 (by rfl) ⟨4396758, by rfl⟩ : syracuseStep 11724689 = 8793517) B8793517
theorem B17590223 : Blo 1829616 17590223 := bstep (se 1 (by rfl) ⟨13192667, by rfl⟩ : syracuseStep 17590223 = 26385335) B26385335
theorem B2746319 : Blo 1829616 2746319 := bstep (se 1 (by rfl) ⟨2059739, by rfl⟩ : syracuseStep 2746319 = 4119479) B4119479
theorem B5867471 : Blo 1829616 5867471 := bstep (se 1 (by rfl) ⟨4400603, by rfl⟩ : syracuseStep 5867471 = 8801207) B8801207
theorem B3475561 : Blo 1829616 3475561 := bstep (se 2 (by rfl) ⟨1303335, by rfl⟩ : syracuseStep 3475561 = 2606671) B2606671
theorem B29698163 : Blo 1829616 29698163 := bstep (se 1 (by rfl) ⟨22273622, by rfl⟩ : syracuseStep 29698163 = 44547245) B44547245
theorem B20056193 : Blo 1829616 20056193 := bstep (se 2 (by rfl) ⟨7521072, by rfl⟩ : syracuseStep 20056193 = 15042145) B15042145
theorem B5212441 : Blo 1829616 5212441 := bstep (se 2 (by rfl) ⟨1954665, by rfl⟩ : syracuseStep 5212441 = 3909331) B3909331
theorem B70347041 : Blo 1829616 70347041 := bstep (se 2 (by rfl) ⟨26380140, by rfl⟩ : syracuseStep 70347041 = 52760281) B52760281
theorem B2746715 : Blo 1829616 2746715 := bstep (se 1 (by rfl) ⟨2060036, by rfl⟩ : syracuseStep 2746715 = 4120073) B4120073
theorem B2058619 : Blo 1829616 2058619 := bstep (se 1 (by rfl) ⟨1543964, by rfl⟩ : syracuseStep 2058619 = 3087929) B3087929
theorem B10422695 : Blo 1829616 10422695 := bstep (se 1 (by rfl) ⟨7817021, by rfl⟩ : syracuseStep 10422695 = 15634043) B15634043
theorem B9898483 : Blo 1829616 9898483 := bstep (se 1 (by rfl) ⟨7423862, by rfl⟩ : syracuseStep 9898483 = 14847725) B14847725
theorem B3475963 : Blo 1829616 3475963 := bstep (se 1 (by rfl) ⟨2606972, by rfl⟩ : syracuseStep 3475963 = 5213945) B5213945
theorem B2746943 : Blo 1829616 2746943 := bstep (se 1 (by rfl) ⟨2060207, by rfl⟩ : syracuseStep 2746943 = 4120415) B4120415
theorem B6179435 : Blo 1829616 6179435 := bstep (se 1 (by rfl) ⟨4634576, by rfl⟩ : syracuseStep 6179435 = 9269153) B9269153
theorem B2747063 : Blo 1829616 2747063 := bstep (se 1 (by rfl) ⟨2060297, by rfl⟩ : syracuseStep 2747063 = 4120595) B4120595
theorem B3476191 : Blo 1829616 3476191 := bstep (se 1 (by rfl) ⟨2607143, by rfl⟩ : syracuseStep 3476191 = 5214287) B5214287
theorem B1829679 : Blo 1829616 1829679 := bstep (se 1 (by rfl) ⟨1372259, by rfl⟩ : syracuseStep 1829679 = 2744519) B2744519
theorem B2059087 : Blo 1829616 2059087 := bstep (se 1 (by rfl) ⟨1544315, by rfl⟩ : syracuseStep 2059087 = 3088631) B3088631
theorem B1829787 : Blo 1829616 1829787 := bstep (se 1 (by rfl) ⟨1372340, by rfl⟩ : syracuseStep 1829787 = 2744681) B2744681
theorem B2747291 : Blo 1829616 2747291 := bstep (se 1 (by rfl) ⟨2060468, by rfl⟩ : syracuseStep 2747291 = 4120937) B4120937
theorem B1829839 : Blo 1829616 1829839 := bstep (se 1 (by rfl) ⟨1372379, by rfl⟩ : syracuseStep 1829839 = 2744759) B2744759
theorem B1829863 : Blo 1829616 1829863 := bstep (se 1 (by rfl) ⟨1372397, by rfl⟩ : syracuseStep 1829863 = 2744795) B2744795
theorem B4631539 : Blo 1829616 4631539 := bstep (se 1 (by rfl) ⟨3473654, by rfl⟩ : syracuseStep 4631539 = 6947309) B6947309
theorem B6180029 : Blo 1829616 6180029 := bstep (se 3 (by rfl) ⟨1158755, by rfl⟩ : syracuseStep 6180029 = 2317511) B2317511
theorem B2059483 : Blo 1829616 2059483 := bstep (se 1 (by rfl) ⟨1544612, by rfl⟩ : syracuseStep 2059483 = 3089225) B3089225
theorem B4893929 : Blo 1829616 4893929 := bstep (se 2 (by rfl) ⟨1835223, by rfl⟩ : syracuseStep 4893929 = 3670447) B3670447
theorem B42863863 : Blo 1829616 42863863 := bstep (se 1 (by rfl) ⟨32147897, by rfl⟩ : syracuseStep 42863863 = 64295795) B64295795
theorem B1830175 : Blo 1829616 1830175 := bstep (se 1 (by rfl) ⟨1372631, by rfl⟩ : syracuseStep 1830175 = 2745263) B2745263
theorem B1830235 : Blo 1829616 1830235 := bstep (se 1 (by rfl) ⟨1372676, by rfl⟩ : syracuseStep 1830235 = 2745353) B2745353
theorem B1830255 : Blo 1829616 1830255 := bstep (se 1 (by rfl) ⟨1372691, by rfl⟩ : syracuseStep 1830255 = 2745383) B2745383
theorem B17591681 : Blo 1829616 17591681 := bstep (se 2 (by rfl) ⟨6596880, by rfl⟩ : syracuseStep 17591681 = 13193761) B13193761
theorem B1830311 : Blo 1829616 1830311 := bstep (se 1 (by rfl) ⟨1372733, by rfl⟩ : syracuseStep 1830311 = 2745467) B2745467
theorem B9268667 : Blo 1829616 9268667 := bstep (se 1 (by rfl) ⟨6951500, by rfl⟩ : syracuseStep 9268667 = 13903001) B13903001
theorem B3476935 : Blo 1829616 3476935 := bstep (se 1 (by rfl) ⟨2607701, by rfl⟩ : syracuseStep 3476935 = 5215403) B5215403
theorem B6950393 : Blo 1829616 6950393 := bstep (se 2 (by rfl) ⟨2606397, by rfl⟩ : syracuseStep 6950393 = 5212795) B5212795
theorem B1830395 : Blo 1829616 1830395 := bstep (se 1 (by rfl) ⟨1372796, by rfl⟩ : syracuseStep 1830395 = 2745593) B2745593
theorem B2059771 : Blo 1829616 2059771 := bstep (se 1 (by rfl) ⟨1544828, by rfl⟩ : syracuseStep 2059771 = 3089657) B3089657
theorem B1830463 : Blo 1829616 1830463 := bstep (se 1 (by rfl) ⟨1372847, by rfl⟩ : syracuseStep 1830463 = 2745695) B2745695
theorem B1830471 : Blo 1829616 1830471 := bstep (se 1 (by rfl) ⟨1372853, by rfl⟩ : syracuseStep 1830471 = 2745707) B2745707
theorem B26381987 : Blo 1829616 26381987 := bstep (se 1 (by rfl) ⟨19786490, by rfl⟩ : syracuseStep 26381987 = 39572981) B39572981
theorem B2059951 : Blo 1829616 2059951 := bstep (se 1 (by rfl) ⟨1544963, by rfl⟩ : syracuseStep 2059951 = 3089927) B3089927
theorem B1830623 : Blo 1829616 1830623 := bstep (se 1 (by rfl) ⟨1372967, by rfl⟩ : syracuseStep 1830623 = 2745935) B2745935
theorem B4632299 : Blo 1829616 4632299 := bstep (se 1 (by rfl) ⟨3474224, by rfl⟩ : syracuseStep 4632299 = 6948449) B6948449
theorem B20057867 : Blo 1829616 20057867 := bstep (se 1 (by rfl) ⟨15043400, by rfl⟩ : syracuseStep 20057867 = 30086801) B30086801
theorem B1830703 : Blo 1829616 1830703 := bstep (se 1 (by rfl) ⟨1373027, by rfl⟩ : syracuseStep 1830703 = 2746055) B2746055
theorem B1830811 : Blo 1829616 1830811 := bstep (se 1 (by rfl) ⟨1373108, by rfl⟩ : syracuseStep 1830811 = 2746217) B2746217
theorem B16707485 : Blo 1829616 16707485 := bstep (se 3 (by rfl) ⟨3132653, by rfl⟩ : syracuseStep 16707485 = 6265307) B6265307
theorem B1830863 : Blo 1829616 1830863 := bstep (se 1 (by rfl) ⟨1373147, by rfl⟩ : syracuseStep 1830863 = 2746295) B2746295
theorem B2060239 : Blo 1829616 2060239 := bstep (se 1 (by rfl) ⟨1545179, by rfl⟩ : syracuseStep 2060239 = 3090359) B3090359
theorem B1830887 : Blo 1829616 1830887 := bstep (se 1 (by rfl) ⟨1373165, by rfl⟩ : syracuseStep 1830887 = 2746331) B2746331
theorem B3911689 : Blo 1829616 3911689 := bstep (se 2 (by rfl) ⟨1466883, by rfl⟩ : syracuseStep 3911689 = 2933767) B2933767
theorem B1831199 : Blo 1829616 1831199 := bstep (se 1 (by rfl) ⟨1373399, by rfl⟩ : syracuseStep 1831199 = 2746799) B2746799
theorem B1831259 : Blo 1829616 1831259 := bstep (se 1 (by rfl) ⟨1373444, by rfl⟩ : syracuseStep 1831259 = 2746889) B2746889
theorem B1831279 : Blo 1829616 1831279 := bstep (se 1 (by rfl) ⟨1373459, by rfl⟩ : syracuseStep 1831279 = 2746919) B2746919
theorem B1831335 : Blo 1829616 1831335 := bstep (se 1 (by rfl) ⟨1373501, by rfl⟩ : syracuseStep 1831335 = 2747003) B2747003
theorem B1831419 : Blo 1829616 1831419 := bstep (se 1 (by rfl) ⟨1373564, by rfl⟩ : syracuseStep 1831419 = 2747129) B2747129
theorem B1831487 : Blo 1829616 1831487 := bstep (se 1 (by rfl) ⟨1373615, by rfl⟩ : syracuseStep 1831487 = 2747231) B2747231
theorem B4633159 : Blo 1829616 4633159 := bstep (se 1 (by rfl) ⟨3474869, by rfl⟩ : syracuseStep 4633159 = 6949739) B6949739
theorem B3174985 : Blo 1829616 3174985 := bstep (se 2 (by rfl) ⟨1190619, by rfl⟩ : syracuseStep 3174985 = 2381239) B2381239
theorem B1831495 : Blo 1829616 1831495 := bstep (se 1 (by rfl) ⟨1373621, by rfl⟩ : syracuseStep 1831495 = 2747243) B2747243
theorem B81343073 : Blo 1829616 81343073 := bstep (se 2 (by rfl) ⟨30503652, by rfl⟩ : syracuseStep 81343073 = 61007305) B61007305
theorem B4117175 : Blo 1829616 4117175 := bstep (se 1 (by rfl) ⟨3087881, by rfl⟩ : syracuseStep 4117175 = 6175763) B6175763
theorem B4633271 : Blo 1829616 4633271 := bstep (se 1 (by rfl) ⟨3474953, by rfl⟩ : syracuseStep 4633271 = 6949907) B6949907
theorem B9269963 : Blo 1829616 9269963 := bstep (se 1 (by rfl) ⟨6952472, by rfl⟩ : syracuseStep 9269963 = 13904945) B13904945
theorem B3298067 : Blo 1829616 3298067 := bstep (se 1 (by rfl) ⟨2473550, by rfl⟩ : syracuseStep 3298067 = 4947101) B4947101
theorem B54203165 : Blo 1829616 54203165 := bstep (se 3 (by rfl) ⟨10163093, by rfl⟩ : syracuseStep 54203165 = 20326187) B20326187
theorem B35648363 : Blo 1829616 35648363 := bstep (se 1 (by rfl) ⟨26736272, by rfl⟩ : syracuseStep 35648363 = 53472545) B53472545
theorem B9270125 : Blo 1829616 9270125 := bstep (se 3 (by rfl) ⟨1738148, by rfl⟩ : syracuseStep 9270125 = 3476297) B3476297
theorem B4117391 : Blo 1829616 4117391 := bstep (se 1 (by rfl) ⟨3088043, by rfl⟩ : syracuseStep 4117391 = 6176087) B6176087
theorem B14840777 : Blo 1829616 14840777 := bstep (se 2 (by rfl) ⟨5565291, by rfl⟩ : syracuseStep 14840777 = 11130583) B11130583
theorem B13906889 : Blo 1829616 13906889 := bstep (se 2 (by rfl) ⟨5215083, by rfl⟩ : syracuseStep 13906889 = 10430167) B10430167
theorem B5215357 : Blo 1829616 5215357 := bstep (se 3 (by rfl) ⟨977879, by rfl⟩ : syracuseStep 5215357 = 1955759) B1955759
theorem B6952169 : Blo 1829616 6952169 := bstep (se 2 (by rfl) ⟨2607063, by rfl⟩ : syracuseStep 6952169 = 5214127) B5214127
theorem B2970911 : Blo 1829616 2970911 := bstep (se 1 (by rfl) ⟨2228183, by rfl⟩ : syracuseStep 2970911 = 4456367) B4456367
theorem B28177753 : Blo 1829616 28177753 := bstep (se 2 (by rfl) ⟨10566657, by rfl⟩ : syracuseStep 28177753 = 21133315) B21133315
theorem B13899113 : Blo 1829616 13899113 := bstep (se 2 (by rfl) ⟨5212167, by rfl⟩ : syracuseStep 13899113 = 10424335) B10424335
theorem B11138465 : Blo 1829616 11138465 := bstep (se 2 (by rfl) ⟨4176924, by rfl⟩ : syracuseStep 11138465 = 8353849) B8353849
theorem B10425793 : Blo 1829616 10425793 := bstep (se 2 (by rfl) ⟨3909672, by rfl⟩ : syracuseStep 10425793 = 7819345) B7819345
theorem B2315719 : Blo 1829616 2315719 := bstep (se 1 (by rfl) ⟨1736789, by rfl⟩ : syracuseStep 2315719 = 3473579) B3473579
theorem B9901549 : Blo 1829616 9901549 := bstep (se 3 (by rfl) ⟨1856540, by rfl⟩ : syracuseStep 9901549 = 3713081) B3713081
theorem B7820833 : Blo 1829616 7820833 := bstep (se 2 (by rfl) ⟨2932812, by rfl⟩ : syracuseStep 7820833 = 5865625) B5865625
theorem B16709159 : Blo 1829616 16709159 := bstep (se 1 (by rfl) ⟨12531869, by rfl⟩ : syracuseStep 16709159 = 25063739) B25063739
theorem B9893465 : Blo 1829616 9893465 := bstep (se 2 (by rfl) ⟨3710049, by rfl⟩ : syracuseStep 9893465 = 7420099) B7420099
theorem B4118111 : Blo 1829616 4118111 := bstep (se 1 (by rfl) ⟨3088583, by rfl⟩ : syracuseStep 4118111 = 6177167) B6177167
theorem B9901703 : Blo 1829616 9901703 := bstep (se 1 (by rfl) ⟨7426277, by rfl⟩ : syracuseStep 9901703 = 14852555) B14852555
theorem B4634273 : Blo 1829616 4634273 := bstep (se 2 (by rfl) ⟨1737852, by rfl⟩ : syracuseStep 4634273 = 3475705) B3475705
theorem B1955503 : Blo 1829616 1955503 := bstep (se 1 (by rfl) ⟨1466627, by rfl⟩ : syracuseStep 1955503 = 2933255) B2933255
theorem B31692475 : Blo 1829616 31692475 := bstep (se 1 (by rfl) ⟨23769356, by rfl⟩ : syracuseStep 31692475 = 47538713) B47538713
theorem B4118327 : Blo 1829616 4118327 := bstep (se 1 (by rfl) ⟨3088745, by rfl⟩ : syracuseStep 4118327 = 6177491) B6177491
theorem B11130853 : Blo 1829616 11130853 := bstep (se 4 (by rfl) ⟨1043517, by rfl⟩ : syracuseStep 11130853 = 2087035) B2087035
theorem B4118633 : Blo 1829616 4118633 := bstep (se 2 (by rfl) ⟨1544487, by rfl⟩ : syracuseStep 4118633 = 3088975) B3088975
theorem B4634729 : Blo 1829616 4634729 := bstep (se 2 (by rfl) ⟨1738023, by rfl⟩ : syracuseStep 4634729 = 3476047) B3476047
theorem B2316863 : Blo 1829616 2316863 := bstep (se 1 (by rfl) ⟨1737647, by rfl⟩ : syracuseStep 2316863 = 3475295) B3475295
theorem B4119119 : Blo 1829616 4119119 := bstep (se 1 (by rfl) ⟨3089339, by rfl⟩ : syracuseStep 4119119 = 6178679) B6178679
theorem B4635215 : Blo 1829616 4635215 := bstep (se 1 (by rfl) ⟨3476411, by rfl⟩ : syracuseStep 4635215 = 6952823) B6952823
theorem B4119263 : Blo 1829616 4119263 := bstep (se 1 (by rfl) ⟨3089447, by rfl⟩ : syracuseStep 4119263 = 6178895) B6178895
theorem B8796995 : Blo 1829616 8796995 := bstep (se 1 (by rfl) ⟨6597746, by rfl⟩ : syracuseStep 8796995 = 13195493) B13195493
theorem B4119515 : Blo 1829616 4119515 := bstep (se 1 (by rfl) ⟨3089636, by rfl⟩ : syracuseStep 4119515 = 6179273) B6179273
theorem B4119695 : Blo 1829616 4119695 := bstep (se 1 (by rfl) ⟨3089771, by rfl⟩ : syracuseStep 4119695 = 6179543) B6179543
theorem B4635863 : Blo 1829616 4635863 := bstep (se 1 (by rfl) ⟨3476897, by rfl⟩ : syracuseStep 4635863 = 6953795) B6953795
theorem B4119785 : Blo 1829616 4119785 := bstep (se 2 (by rfl) ⟨1544919, by rfl⟩ : syracuseStep 4119785 = 3089839) B3089839
theorem B4119839 : Blo 1829616 4119839 := bstep (se 1 (by rfl) ⟨3089879, by rfl⟩ : syracuseStep 4119839 = 6179759) B6179759
theorem B12524867 : Blo 1829616 12524867 := bstep (se 1 (by rfl) ⟨9393650, by rfl⟩ : syracuseStep 12524867 = 18787301) B18787301
theorem B6176249 : Blo 1829616 6176249 := bstep (se 2 (by rfl) ⟨2316093, by rfl⟩ : syracuseStep 6176249 = 4632187) B4632187
theorem B2932217 : Blo 1829616 2932217 := bstep (se 2 (by rfl) ⟨1099581, by rfl⟩ : syracuseStep 2932217 = 2199163) B2199163
theorem B4636217 : Blo 1829616 4636217 := bstep (se 2 (by rfl) ⟨1738581, by rfl⟩ : syracuseStep 4636217 = 3477163) B3477163
theorem B13188689 : Blo 1829616 13188689 := bstep (se 2 (by rfl) ⟨4945758, by rfl⟩ : syracuseStep 13188689 = 9891517) B9891517
theorem B2932319 : Blo 1829616 2932319 := bstep (se 1 (by rfl) ⟨2199239, by rfl⟩ : syracuseStep 2932319 = 4398479) B4398479
theorem B118767221 : Blo 1829616 118767221 := bstep (se 5 (by rfl) ⟨5567213, by rfl⟩ : syracuseStep 118767221 = 11134427) B11134427
theorem B16924409 : Blo 1829616 16924409 := bstep (se 2 (by rfl) ⟨6346653, by rfl⟩ : syracuseStep 16924409 = 12693307) B12693307
theorem B6176519 : Blo 1829616 6176519 := bstep (se 1 (by rfl) ⟨4632389, by rfl⟩ : syracuseStep 6176519 = 9264779) B9264779
theorem B5865227 : Blo 1829616 5865227 := bstep (se 1 (by rfl) ⟨4398920, by rfl⟩ : syracuseStep 5865227 = 8797841) B8797841
theorem B4120361 : Blo 1829616 4120361 := bstep (se 2 (by rfl) ⟨1545135, by rfl⟩ : syracuseStep 4120361 = 3090271) B3090271
theorem B2932537 : Blo 1829616 2932537 := bstep (se 2 (by rfl) ⟨1099701, by rfl⟩ : syracuseStep 2932537 = 2199403) B2199403
theorem B6176573 : Blo 1829616 6176573 := bstep (se 3 (by rfl) ⟨1158107, by rfl⟩ : syracuseStep 6176573 = 2316215) B2316215
theorem B15851371 : Blo 1829616 15851371 := bstep (se 1 (by rfl) ⟨11888528, by rfl⟩ : syracuseStep 15851371 = 23777057) B23777057
theorem B33415105 : Blo 1829616 33415105 := bstep (se 2 (by rfl) ⟨12530664, by rfl⟩ : syracuseStep 33415105 = 25061329) B25061329
theorem B20840651 : Blo 1829616 20840651 := bstep (se 1 (by rfl) ⟨15630488, by rfl⟩ : syracuseStep 20840651 = 31260977) B31260977
theorem B3473761 : Blo 1829616 3473761 := bstep (se 2 (by rfl) ⟨1302660, by rfl⟩ : syracuseStep 3473761 = 2605321) B2605321
theorem B5947847 : Blo 1829616 5947847 := bstep (se 1 (by rfl) ⟨4460885, by rfl⟩ : syracuseStep 5947847 = 8921771) B8921771
theorem B6947279 : Blo 1829616 6947279 := bstep (se 1 (by rfl) ⟨5210459, by rfl⟩ : syracuseStep 6947279 = 10420919) B10420919
theorem B2744783 : Blo 1829616 2744783 := bstep (se 1 (by rfl) ⟨2058587, by rfl⟩ : syracuseStep 2744783 = 4117175) B4117175
theorem B3088847 : Blo 1829616 3088847 := bstep (se 1 (by rfl) ⟨2316635, by rfl⟩ : syracuseStep 3088847 = 4633271) B4633271
theorem B2744825 : Blo 1829616 2744825 := bstep (se 2 (by rfl) ⟨1029309, by rfl⟩ : syracuseStep 2744825 = 2058619) B2058619
theorem B6177275 : Blo 1829616 6177275 := bstep (se 1 (by rfl) ⟨4632956, by rfl⟩ : syracuseStep 6177275 = 9265913) B9265913
theorem B36135443 : Blo 1829616 36135443 := bstep (se 1 (by rfl) ⟨27101582, by rfl⟩ : syracuseStep 36135443 = 54203165) B54203165
theorem B23765575 : Blo 1829616 23765575 := bstep (se 1 (by rfl) ⟨17824181, by rfl⟩ : syracuseStep 23765575 = 35648363) B35648363
theorem B2744927 : Blo 1829616 2744927 := bstep (se 1 (by rfl) ⟨2058695, by rfl⟩ : syracuseStep 2744927 = 4117391) B4117391
theorem B13197977 : Blo 1829616 13197977 := bstep (se 2 (by rfl) ⟨4949241, by rfl⟩ : syracuseStep 13197977 = 9898483) B9898483
theorem B6177545 : Blo 1829616 6177545 := bstep (se 2 (by rfl) ⟨2316579, by rfl⟩ : syracuseStep 6177545 = 4633159) B4633159
theorem B9266075 : Blo 1829616 9266075 := bstep (se 1 (by rfl) ⟨6949556, by rfl⟩ : syracuseStep 9266075 = 13899113) B13899113
theorem B14091209 : Blo 1829616 14091209 := bstep (se 2 (by rfl) ⟨5284203, by rfl⟩ : syracuseStep 14091209 = 10568407) B10568407
theorem B6947795 : Blo 1829616 6947795 := bstep (se 1 (by rfl) ⟨5210846, by rfl⟩ : syracuseStep 6947795 = 10421693) B10421693
theorem B169026533 : Blo 1829616 169026533 := bstep (se 4 (by rfl) ⟨15846237, by rfl⟩ : syracuseStep 169026533 = 31692475) B31692475
theorem B6595643 : Blo 1829616 6595643 := bstep (se 1 (by rfl) ⟨4946732, by rfl⟩ : syracuseStep 6595643 = 9893465) B9893465
theorem B2745407 : Blo 1829616 2745407 := bstep (se 1 (by rfl) ⟨2059055, by rfl⟩ : syracuseStep 2745407 = 4118111) B4118111
theorem B2745449 : Blo 1829616 2745449 := bstep (se 2 (by rfl) ⟨1029543, by rfl⟩ : syracuseStep 2745449 = 2059087) B2059087
theorem B3089515 : Blo 1829616 3089515 := bstep (se 1 (by rfl) ⟨2317136, by rfl⟩ : syracuseStep 3089515 = 4634273) B4634273
theorem B2745551 : Blo 1829616 2745551 := bstep (se 1 (by rfl) ⟨2059163, by rfl⟩ : syracuseStep 2745551 = 4118327) B4118327
theorem B7816459 : Blo 1829616 7816459 := bstep (se 1 (by rfl) ⟨5862344, by rfl⟩ : syracuseStep 7816459 = 11724689) B11724689
theorem B2745755 : Blo 1829616 2745755 := bstep (se 1 (by rfl) ⟨2059316, by rfl⟩ : syracuseStep 2745755 = 4118633) B4118633
theorem B3089819 : Blo 1829616 3089819 := bstep (se 1 (by rfl) ⟨2317364, by rfl⟩ : syracuseStep 3089819 = 4634729) B4634729
theorem B13370795 : Blo 1829616 13370795 := bstep (se 1 (by rfl) ⟨10028096, by rfl⟩ : syracuseStep 13370795 = 20056193) B20056193
theorem B6178301 : Blo 1829616 6178301 := bstep (se 3 (by rfl) ⟨1158431, by rfl⟩ : syracuseStep 6178301 = 2316863) B2316863
theorem B6948463 : Blo 1829616 6948463 := bstep (se 1 (by rfl) ⟨5211347, by rfl⟩ : syracuseStep 6948463 = 10422695) B10422695
theorem B2745977 : Blo 1829616 2745977 := bstep (se 2 (by rfl) ⟨1029741, by rfl⟩ : syracuseStep 2745977 = 2059483) B2059483
theorem B26404541 : Blo 1829616 26404541 := bstep (se 3 (by rfl) ⟨4950851, by rfl⟩ : syracuseStep 26404541 = 9901703) B9901703
theorem B2746079 : Blo 1829616 2746079 := bstep (se 1 (by rfl) ⟨2059559, by rfl⟩ : syracuseStep 2746079 = 4119119) B4119119
theorem B3090143 : Blo 1829616 3090143 := bstep (se 1 (by rfl) ⟨2317607, by rfl⟩ : syracuseStep 3090143 = 4635215) B4635215
theorem B37570337 : Blo 1829616 37570337 := bstep (se 2 (by rfl) ⟨14088876, by rfl⟩ : syracuseStep 37570337 = 28177753) B28177753
theorem B2746175 : Blo 1829616 2746175 := bstep (se 1 (by rfl) ⟨2059631, by rfl⟩ : syracuseStep 2746175 = 4119263) B4119263
theorem B6948737 : Blo 1829616 6948737 := bstep (se 2 (by rfl) ⟨2605776, by rfl⟩ : syracuseStep 6948737 = 5211553) B5211553
theorem B2746343 : Blo 1829616 2746343 := bstep (se 1 (by rfl) ⟨2059757, by rfl⟩ : syracuseStep 2746343 = 4119515) B4119515
theorem B2746361 : Blo 1829616 2746361 := bstep (se 2 (by rfl) ⟨1029885, by rfl⟩ : syracuseStep 2746361 = 2059771) B2059771
theorem B3344377 : Blo 1829616 3344377 := bstep (se 2 (by rfl) ⟨1254141, by rfl⟩ : syracuseStep 3344377 = 2508283) B2508283
theorem B2746463 : Blo 1829616 2746463 := bstep (se 1 (by rfl) ⟨2059847, by rfl⟩ : syracuseStep 2746463 = 4119695) B4119695
theorem B3090575 : Blo 1829616 3090575 := bstep (se 1 (by rfl) ⟨2317931, by rfl⟩ : syracuseStep 3090575 = 4635863) B4635863
theorem B2746523 : Blo 1829616 2746523 := bstep (se 1 (by rfl) ⟨2059892, by rfl⟩ : syracuseStep 2746523 = 4119785) B4119785
theorem B3262619 : Blo 1829616 3262619 := bstep (se 1 (by rfl) ⟨2446964, by rfl⟩ : syracuseStep 3262619 = 4893929) B4893929
theorem B2746559 : Blo 1829616 2746559 := bstep (se 1 (by rfl) ⟨2059919, by rfl⟩ : syracuseStep 2746559 = 4119839) B4119839
theorem B8349911 : Blo 1829616 8349911 := bstep (se 1 (by rfl) ⟨6262433, by rfl⟩ : syracuseStep 8349911 = 12524867) B12524867
theorem B2746601 : Blo 1829616 2746601 := bstep (se 2 (by rfl) ⟨1029975, by rfl⟩ : syracuseStep 2746601 = 2059951) B2059951
theorem B2607337 : Blo 1829616 2607337 := bstep (se 2 (by rfl) ⟨977751, by rfl⟩ : syracuseStep 2607337 = 1955503) B1955503
theorem B6179111 : Blo 1829616 6179111 := bstep (se 1 (by rfl) ⟨4634333, by rfl⟩ : syracuseStep 6179111 = 9268667) B9268667
theorem B3090811 : Blo 1829616 3090811 := bstep (se 1 (by rfl) ⟨2318108, by rfl⟩ : syracuseStep 3090811 = 4636217) B4636217
theorem B8792459 : Blo 1829616 8792459 := bstep (se 1 (by rfl) ⟨6594344, by rfl⟩ : syracuseStep 8792459 = 13188689) B13188689
theorem B3910049 : Blo 1829616 3910049 := bstep (se 2 (by rfl) ⟨1466268, by rfl⟩ : syracuseStep 3910049 = 2932537) B2932537
theorem B79178147 : Blo 1829616 79178147 := bstep (se 1 (by rfl) ⟨59383610, by rfl⟩ : syracuseStep 79178147 = 118767221) B118767221
theorem B11282939 : Blo 1829616 11282939 := bstep (se 1 (by rfl) ⟨8462204, by rfl⟩ : syracuseStep 11282939 = 16924409) B16924409
theorem B13371911 : Blo 1829616 13371911 := bstep (se 1 (by rfl) ⟨10028933, by rfl⟩ : syracuseStep 13371911 = 20057867) B20057867
theorem B3910151 : Blo 1829616 3910151 := bstep (se 1 (by rfl) ⟨2932613, by rfl⟩ : syracuseStep 3910151 = 5865227) B5865227
theorem B2746907 : Blo 1829616 2746907 := bstep (se 1 (by rfl) ⟨2060180, by rfl⟩ : syracuseStep 2746907 = 4120361) B4120361
theorem B2746985 : Blo 1829616 2746985 := bstep (se 2 (by rfl) ⟨1030119, by rfl⟩ : syracuseStep 2746985 = 2060239) B2060239
theorem B1829723 : Blo 1829616 1829723 := bstep (se 1 (by rfl) ⟨1372292, by rfl⟩ : syracuseStep 1829723 = 2744585) B2744585
theorem B1829791 : Blo 1829616 1829791 := bstep (se 1 (by rfl) ⟨1372343, by rfl⟩ : syracuseStep 1829791 = 2744687) B2744687
theorem B6949921 : Blo 1829616 6949921 := bstep (se 2 (by rfl) ⟨2606220, by rfl⟩ : syracuseStep 6949921 = 5212441) B5212441
theorem B1829935 : Blo 1829616 1829935 := bstep (se 1 (by rfl) ⟨1372451, by rfl⟩ : syracuseStep 1829935 = 2744903) B2744903
theorem B1829959 : Blo 1829616 1829959 := bstep (se 1 (by rfl) ⟨1372469, by rfl⟩ : syracuseStep 1829959 = 2744939) B2744939
theorem B6179975 : Blo 1829616 6179975 := bstep (se 1 (by rfl) ⟨4634981, by rfl⟩ : syracuseStep 6179975 = 9269963) B9269963
theorem B2198711 : Blo 1829616 2198711 := bstep (se 1 (by rfl) ⟨1649033, by rfl⟩ : syracuseStep 2198711 = 3298067) B3298067
theorem B1830111 : Blo 1829616 1830111 := bstep (se 1 (by rfl) ⟨1372583, by rfl⟩ : syracuseStep 1830111 = 2745167) B2745167
theorem B6180083 : Blo 1829616 6180083 := bstep (se 1 (by rfl) ⟨4635062, by rfl⟩ : syracuseStep 6180083 = 9270125) B9270125
theorem B1830375 : Blo 1829616 1830375 := bstep (se 1 (by rfl) ⟨1372781, by rfl⟩ : syracuseStep 1830375 = 2745563) B2745563
theorem B13905431 : Blo 1829616 13905431 := bstep (se 1 (by rfl) ⟨10429073, by rfl⟩ : syracuseStep 13905431 = 20858147) B20858147
theorem B4632137 : Blo 1829616 4632137 := bstep (se 2 (by rfl) ⟨1737051, by rfl⟩ : syracuseStep 4632137 = 3474103) B3474103
theorem B1830491 : Blo 1829616 1830491 := bstep (se 1 (by rfl) ⟨1372868, by rfl⟩ : syracuseStep 1830491 = 2745737) B2745737
theorem B7425643 : Blo 1829616 7425643 := bstep (se 1 (by rfl) ⟨5569232, by rfl⟩ : syracuseStep 7425643 = 11138465) B11138465
theorem B46911149 : Blo 1829616 46911149 := bstep (se 3 (by rfl) ⟨8795840, by rfl⟩ : syracuseStep 46911149 = 17591681) B17591681
theorem B39595817 : Blo 1829616 39595817 := bstep (se 2 (by rfl) ⟨14848431, by rfl⟩ : syracuseStep 39595817 = 29696863) B29696863
theorem B1830727 : Blo 1829616 1830727 := bstep (se 1 (by rfl) ⟨1373045, by rfl⟩ : syracuseStep 1830727 = 2746091) B2746091
theorem B11726815 : Blo 1829616 11726815 := bstep (se 1 (by rfl) ⟨8795111, by rfl⟩ : syracuseStep 11726815 = 17590223) B17590223
theorem B1830879 : Blo 1829616 1830879 := bstep (se 1 (by rfl) ⟨1373159, by rfl⟩ : syracuseStep 1830879 = 2746319) B2746319
theorem B3911647 : Blo 1829616 3911647 := bstep (se 1 (by rfl) ⟨2933735, by rfl⟩ : syracuseStep 3911647 = 5867471) B5867471
theorem B6950893 : Blo 1829616 6950893 := bstep (se 3 (by rfl) ⟨1303292, by rfl⟩ : syracuseStep 6950893 = 2606585) B2606585
theorem B1831143 : Blo 1829616 1831143 := bstep (se 1 (by rfl) ⟨1373357, by rfl⟩ : syracuseStep 1831143 = 2746715) B2746715
theorem B7819517 : Blo 1829616 7819517 := bstep (se 3 (by rfl) ⟨1466159, by rfl⟩ : syracuseStep 7819517 = 2932319) B2932319
theorem B57151817 : Blo 1829616 57151817 := bstep (se 2 (by rfl) ⟨21431931, by rfl⟩ : syracuseStep 57151817 = 42863863) B42863863
theorem B1831295 : Blo 1829616 1831295 := bstep (se 1 (by rfl) ⟨1373471, by rfl⟩ : syracuseStep 1831295 = 2746943) B2746943
theorem B16691609 : Blo 1829616 16691609 := bstep (se 2 (by rfl) ⟨6259353, by rfl⟩ : syracuseStep 16691609 = 12518707) B12518707
theorem B1831375 : Blo 1829616 1831375 := bstep (se 1 (by rfl) ⟨1373531, by rfl⟩ : syracuseStep 1831375 = 2747063) B2747063
theorem B1831527 : Blo 1829616 1831527 := bstep (se 1 (by rfl) ⟨1373645, by rfl⟩ : syracuseStep 1831527 = 2747291) B2747291
theorem B13202065 : Blo 1829616 13202065 := bstep (se 2 (by rfl) ⟨4950774, by rfl⟩ : syracuseStep 13202065 = 9901549) B9901549
theorem B4117499 : Blo 1829616 4117499 := bstep (se 1 (by rfl) ⟨3088124, by rfl⟩ : syracuseStep 4117499 = 6176249) B6176249
theorem B4633595 : Blo 1829616 4633595 := bstep (se 1 (by rfl) ⟨3475196, by rfl⟩ : syracuseStep 4633595 = 6950393) B6950393
theorem B1954811 : Blo 1829616 1954811 := bstep (se 1 (by rfl) ⟨1466108, by rfl⟩ : syracuseStep 1954811 = 2932217) B2932217
theorem B4117679 : Blo 1829616 4117679 := bstep (se 1 (by rfl) ⟨3088259, by rfl⟩ : syracuseStep 4117679 = 6176519) B6176519
theorem B4117715 : Blo 1829616 4117715 := bstep (se 1 (by rfl) ⟨3088286, by rfl⟩ : syracuseStep 4117715 = 6176573) B6176573
theorem B44553473 : Blo 1829616 44553473 := bstep (se 2 (by rfl) ⟨16707552, by rfl⟩ : syracuseStep 44553473 = 33415105) B33415105
theorem B11138323 : Blo 1829616 11138323 := bstep (se 1 (by rfl) ⟨8353742, by rfl⟩ : syracuseStep 11138323 = 16707485) B16707485
theorem B14841137 : Blo 1829616 14841137 := bstep (se 2 (by rfl) ⟨5565426, by rfl⟩ : syracuseStep 14841137 = 11130853) B11130853
theorem B5215585 : Blo 1829616 5215585 := bstep (se 2 (by rfl) ⟨1955844, by rfl⟩ : syracuseStep 5215585 = 3911689) B3911689
theorem B4117985 : Blo 1829616 4117985 := bstep (se 2 (by rfl) ⟨1544244, by rfl⟩ : syracuseStep 4117985 = 3088489) B3088489
theorem B4634081 : Blo 1829616 4634081 := bstep (se 2 (by rfl) ⟨1737780, by rfl⟩ : syracuseStep 4634081 = 3475561) B3475561
theorem B47552437 : Blo 1829616 47552437 := bstep (se 5 (by rfl) ⟨2229020, by rfl⟩ : syracuseStep 47552437 = 4458041) B4458041
theorem B10426319 : Blo 1829616 10426319 := bstep (se 1 (by rfl) ⟨7819739, by rfl⟩ : syracuseStep 10426319 = 15639479) B15639479
theorem B9271259 : Blo 1829616 9271259 := bstep (se 1 (by rfl) ⟨6953444, by rfl⟩ : syracuseStep 9271259 = 13906889) B13906889
theorem B2316271 : Blo 1829616 2316271 := bstep (se 1 (by rfl) ⟨1737203, by rfl⟩ : syracuseStep 2316271 = 3474407) B3474407
theorem B4634617 : Blo 1829616 4634617 := bstep (se 2 (by rfl) ⟨1737981, by rfl⟩ : syracuseStep 4634617 = 3475963) B3475963
theorem B4233313 : Blo 1829616 4233313 := bstep (se 2 (by rfl) ⟨1587492, by rfl⟩ : syracuseStep 4233313 = 3174985) B3174985
theorem B4634779 : Blo 1829616 4634779 := bstep (se 1 (by rfl) ⟨3476084, by rfl⟩ : syracuseStep 4634779 = 6952169) B6952169
theorem B1980607 : Blo 1829616 1980607 := bstep (se 1 (by rfl) ⟨1485455, by rfl⟩ : syracuseStep 1980607 = 2970911) B2970911
theorem B4634921 : Blo 1829616 4634921 := bstep (se 2 (by rfl) ⟨1738095, by rfl⟩ : syracuseStep 4634921 = 3476191) B3476191
theorem B6953323 : Blo 1829616 6953323 := bstep (se 1 (by rfl) ⟨5214992, by rfl⟩ : syracuseStep 6953323 = 10429985) B10429985
theorem B11139439 : Blo 1829616 11139439 := bstep (se 1 (by rfl) ⟨8354579, by rfl⟩ : syracuseStep 11139439 = 16709159) B16709159
theorem B9263483 : Blo 1829616 9263483 := bstep (se 1 (by rfl) ⟨6947612, by rfl⟩ : syracuseStep 9263483 = 13895225) B13895225
theorem B6175385 : Blo 1829616 6175385 := bstep (se 2 (by rfl) ⟨2315769, by rfl⟩ : syracuseStep 6175385 = 4631539) B4631539
theorem B19798775 : Blo 1829616 19798775 := bstep (se 1 (by rfl) ⟨14849081, by rfl⟩ : syracuseStep 19798775 = 29698163) B29698163
theorem B6953809 : Blo 1829616 6953809 := bstep (se 2 (by rfl) ⟨2607678, by rfl⟩ : syracuseStep 6953809 = 5215357) B5215357
theorem B46898027 : Blo 1829616 46898027 := bstep (se 1 (by rfl) ⟨35173520, by rfl⟩ : syracuseStep 46898027 = 70347041) B70347041
theorem B216914861 : Blo 1829616 216914861 := bstep (se 3 (by rfl) ⟨40671536, by rfl⟩ : syracuseStep 216914861 = 81343073) B81343073
theorem B4119623 : Blo 1829616 4119623 := bstep (se 1 (by rfl) ⟨3089717, by rfl⟩ : syracuseStep 4119623 = 6179435) B6179435
theorem B5864663 : Blo 1829616 5864663 := bstep (se 1 (by rfl) ⟨4398497, by rfl⟩ : syracuseStep 5864663 = 8796995) B8796995
theorem B13901057 : Blo 1829616 13901057 := bstep (se 2 (by rfl) ⟨5212896, by rfl⟩ : syracuseStep 13901057 = 10425793) B10425793
theorem B3087625 : Blo 1829616 3087625 := bstep (se 2 (by rfl) ⟨1157859, by rfl⟩ : syracuseStep 3087625 = 2315719) B2315719
theorem B4635913 : Blo 1829616 4635913 := bstep (se 2 (by rfl) ⟨1738467, by rfl⟩ : syracuseStep 4635913 = 3476935) B3476935
theorem B10427777 : Blo 1829616 10427777 := bstep (se 2 (by rfl) ⟨3910416, by rfl⟩ : syracuseStep 10427777 = 7820833) B7820833
theorem B4120019 : Blo 1829616 4120019 := bstep (se 1 (by rfl) ⟨3090014, by rfl⟩ : syracuseStep 4120019 = 6180029) B6180029
theorem B4120289 : Blo 1829616 4120289 := bstep (se 2 (by rfl) ⟨1545108, by rfl⟩ : syracuseStep 4120289 = 3090217) B3090217
theorem B17587991 : Blo 1829616 17587991 := bstep (se 1 (by rfl) ⟨13190993, by rfl⟩ : syracuseStep 17587991 = 26381987) B26381987
theorem B21135161 : Blo 1829616 21135161 := bstep (se 2 (by rfl) ⟨7925685, by rfl⟩ : syracuseStep 21135161 = 15851371) B15851371
theorem B3088199 : Blo 1829616 3088199 := bstep (se 1 (by rfl) ⟨2316149, by rfl⟩ : syracuseStep 3088199 = 4632299) B4632299
theorem B39575405 : Blo 1829616 39575405 := bstep (se 3 (by rfl) ⟨7420388, by rfl⟩ : syracuseStep 39575405 = 14840777) B14840777
theorem B5644417 : Blo 1829616 5644417 := bstep (se 2 (by rfl) ⟨2116656, by rfl⟩ : syracuseStep 5644417 = 4233313) B4233313
theorem B13893767 : Blo 1829616 13893767 := bstep (se 1 (by rfl) ⟨10420325, by rfl⟩ : syracuseStep 13893767 = 20840651) B20840651
theorem B38101211 : Blo 1829616 38101211 := bstep (se 1 (by rfl) ⟨28575908, by rfl⟩ : syracuseStep 38101211 = 57151817) B57151817
theorem B3965231 : Blo 1829616 3965231 := bstep (se 1 (by rfl) ⟨2973923, by rfl⟩ : syracuseStep 3965231 = 5947847) B5947847
theorem B8700317 : Blo 1829616 8700317 := bstep (se 3 (by rfl) ⟨1631309, by rfl⟩ : syracuseStep 8700317 = 3262619) B3262619
theorem B8798651 : Blo 1829616 8798651 := bstep (se 1 (by rfl) ⟨6598988, by rfl⟩ : syracuseStep 8798651 = 13197977) B13197977
theorem B14852585 : Blo 1829616 14852585 := bstep (se 2 (by rfl) ⟨5569719, by rfl⟩ : syracuseStep 14852585 = 11139439) B11139439
theorem B4121081 : Blo 1829616 4121081 := bstep (se 2 (by rfl) ⟨1545405, by rfl⟩ : syracuseStep 4121081 = 3090811) B3090811
theorem B15639101 : Blo 1829616 15639101 := bstep (se 3 (by rfl) ⟨2932331, by rfl⟩ : syracuseStep 15639101 = 5864663) B5864663
theorem B6177383 : Blo 1829616 6177383 := bstep (se 1 (by rfl) ⟨4633037, by rfl⟩ : syracuseStep 6177383 = 9266075) B9266075
theorem B2744999 : Blo 1829616 2744999 := bstep (se 1 (by rfl) ⟨2058749, by rfl⟩ : syracuseStep 2744999 = 4117499) B4117499
theorem B3089063 : Blo 1829616 3089063 := bstep (se 1 (by rfl) ⟨2316797, by rfl⟩ : syracuseStep 3089063 = 4633595) B4633595
theorem B31687433 : Blo 1829616 31687433 := bstep (se 2 (by rfl) ⟨11882787, by rfl⟩ : syracuseStep 31687433 = 23765575) B23765575
theorem B2745119 : Blo 1829616 2745119 := bstep (se 1 (by rfl) ⟨2058839, by rfl⟩ : syracuseStep 2745119 = 4117679) B4117679
theorem B2745143 : Blo 1829616 2745143 := bstep (se 1 (by rfl) ⟨2058857, by rfl⟩ : syracuseStep 2745143 = 4117715) B4117715
theorem B8913863 : Blo 1829616 8913863 := bstep (se 1 (by rfl) ⟨6685397, by rfl⟩ : syracuseStep 8913863 = 13370795) B13370795
theorem B2745323 : Blo 1829616 2745323 := bstep (se 1 (by rfl) ⟨2058992, by rfl⟩ : syracuseStep 2745323 = 4117985) B4117985
theorem B3089387 : Blo 1829616 3089387 := bstep (se 1 (by rfl) ⟨2317040, by rfl⟩ : syracuseStep 3089387 = 4634081) B4634081
theorem B9266561 : Blo 1829616 9266561 := bstep (se 2 (by rfl) ⟨3474960, by rfl⟩ : syracuseStep 9266561 = 6949921) B6949921
theorem B3089947 : Blo 1829616 3089947 := bstep (se 1 (by rfl) ⟨2317460, by rfl⟩ : syracuseStep 3089947 = 4634921) B4634921
theorem B2606699 : Blo 1829616 2606699 := bstep (se 1 (by rfl) ⟨1955024, by rfl⟩ : syracuseStep 2606699 = 3910049) B3910049
theorem B7521959 : Blo 1829616 7521959 := bstep (se 1 (by rfl) ⟨5641469, by rfl⟩ : syracuseStep 7521959 = 11282939) B11282939
theorem B8914607 : Blo 1829616 8914607 := bstep (se 1 (by rfl) ⟨6685955, by rfl⟩ : syracuseStep 8914607 = 13371911) B13371911
theorem B10421945 : Blo 1829616 10421945 := bstep (se 2 (by rfl) ⟨3908229, by rfl⟩ : syracuseStep 10421945 = 7816459) B7816459
theorem B13199183 : Blo 1829616 13199183 := bstep (se 1 (by rfl) ⟨9899387, by rfl⟩ : syracuseStep 13199183 = 19798775) B19798775
theorem B2746415 : Blo 1829616 2746415 := bstep (se 1 (by rfl) ⟨2059811, by rfl⟩ : syracuseStep 2746415 = 4119623) B4119623
theorem B9267371 : Blo 1829616 9267371 := bstep (se 1 (by rfl) ⟨6950528, by rfl⟩ : syracuseStep 9267371 = 13901057) B13901057
theorem B2746679 : Blo 1829616 2746679 := bstep (se 1 (by rfl) ⟨2060009, by rfl⟩ : syracuseStep 2746679 = 4120019) B4120019
theorem B578439629 : Blo 1829616 578439629 := bstep (se 3 (by rfl) ⟨108457430, by rfl⟩ : syracuseStep 578439629 = 216914861) B216914861
theorem B2746859 : Blo 1829616 2746859 := bstep (se 1 (by rfl) ⟨2060144, by rfl⟩ : syracuseStep 2746859 = 4120289) B4120289
theorem B11725327 : Blo 1829616 11725327 := bstep (se 1 (by rfl) ⟨8793995, by rfl⟩ : syracuseStep 11725327 = 17587991) B17587991
theorem B71346709 : Blo 1829616 71346709 := bstep (se 6 (by rfl) ⟨1672188, by rfl⟩ : syracuseStep 71346709 = 3344377) B3344377
theorem B26397211 : Blo 1829616 26397211 := bstep (se 1 (by rfl) ⟨19797908, by rfl⟩ : syracuseStep 26397211 = 39595817) B39595817
theorem B2058799 : Blo 1829616 2058799 := bstep (se 1 (by rfl) ⟨1544099, by rfl⟩ : syracuseStep 2058799 = 3088199) B3088199
theorem B9267857 : Blo 1829616 9267857 := bstep (se 2 (by rfl) ⟨3475446, by rfl⟩ : syracuseStep 9267857 = 6950893) B6950893
theorem B5212829 : Blo 1829616 5212829 := bstep (se 3 (by rfl) ⟨977405, by rfl⟩ : syracuseStep 5212829 = 1954811) B1954811
theorem B6179489 : Blo 1829616 6179489 := bstep (se 2 (by rfl) ⟨2317308, by rfl⟩ : syracuseStep 6179489 = 4634617) B4634617
theorem B5213011 : Blo 1829616 5213011 := bstep (se 1 (by rfl) ⟨3909758, by rfl⟩ : syracuseStep 5213011 = 7819517) B7819517
theorem B6179705 : Blo 1829616 6179705 := bstep (se 2 (by rfl) ⟨2317389, by rfl⟩ : syracuseStep 6179705 = 4634779) B4634779
theorem B2640809 : Blo 1829616 2640809 := bstep (se 2 (by rfl) ⟨990303, by rfl⟩ : syracuseStep 2640809 = 1980607) B1980607
theorem B11127739 : Blo 1829616 11127739 := bstep (se 1 (by rfl) ⟨8345804, by rfl⟩ : syracuseStep 11127739 = 16691609) B16691609
theorem B4631519 : Blo 1829616 4631519 := bstep (se 1 (by rfl) ⟨3473639, by rfl⟩ : syracuseStep 4631519 = 6947279) B6947279
theorem B1829855 : Blo 1829616 1829855 := bstep (se 1 (by rfl) ⟨1372391, by rfl⟩ : syracuseStep 1829855 = 2744783) B2744783
theorem B2059231 : Blo 1829616 2059231 := bstep (se 1 (by rfl) ⟨1544423, by rfl⟩ : syracuseStep 2059231 = 3088847) B3088847
theorem B3476449 : Blo 1829616 3476449 := bstep (se 2 (by rfl) ⟨1303668, by rfl⟩ : syracuseStep 3476449 = 2607337) B2607337
theorem B1829883 : Blo 1829616 1829883 := bstep (se 1 (by rfl) ⟨1372412, by rfl⟩ : syracuseStep 1829883 = 2744825) B2744825
theorem B1829951 : Blo 1829616 1829951 := bstep (se 1 (by rfl) ⟨1372463, by rfl⟩ : syracuseStep 1829951 = 2744927) B2744927
theorem B4631681 : Blo 1829616 4631681 := bstep (se 2 (by rfl) ⟨1736880, by rfl⟩ : syracuseStep 4631681 = 3473761) B3473761
theorem B4631863 : Blo 1829616 4631863 := bstep (se 1 (by rfl) ⟨3473897, by rfl⟩ : syracuseStep 4631863 = 6947795) B6947795
theorem B112684355 : Blo 1829616 112684355 := bstep (se 1 (by rfl) ⟨84513266, by rfl⟩ : syracuseStep 112684355 = 169026533) B169026533
theorem B1830271 : Blo 1829616 1830271 := bstep (se 1 (by rfl) ⟨1372703, by rfl⟩ : syracuseStep 1830271 = 2745407) B2745407
theorem B1830299 : Blo 1829616 1830299 := bstep (se 1 (by rfl) ⟨1372724, by rfl⟩ : syracuseStep 1830299 = 2745449) B2745449
theorem B1830367 : Blo 1829616 1830367 := bstep (se 1 (by rfl) ⟨1372775, by rfl⟩ : syracuseStep 1830367 = 2745551) B2745551
theorem B1830503 : Blo 1829616 1830503 := bstep (se 1 (by rfl) ⟨1372877, by rfl⟩ : syracuseStep 1830503 = 2745755) B2745755
theorem B2059879 : Blo 1829616 2059879 := bstep (se 1 (by rfl) ⟨1544909, by rfl⟩ : syracuseStep 2059879 = 3089819) B3089819
theorem B1830651 : Blo 1829616 1830651 := bstep (se 1 (by rfl) ⟨1372988, by rfl⟩ : syracuseStep 1830651 = 2745977) B2745977
theorem B1830719 : Blo 1829616 1830719 := bstep (se 1 (by rfl) ⟨1373039, by rfl⟩ : syracuseStep 1830719 = 2746079) B2746079
theorem B2060095 : Blo 1829616 2060095 := bstep (se 1 (by rfl) ⟨1545071, by rfl⟩ : syracuseStep 2060095 = 3090143) B3090143
theorem B25046891 : Blo 1829616 25046891 := bstep (se 1 (by rfl) ⟨18785168, by rfl⟩ : syracuseStep 25046891 = 37570337) B37570337
theorem B1830783 : Blo 1829616 1830783 := bstep (se 1 (by rfl) ⟨1373087, by rfl⟩ : syracuseStep 1830783 = 2746175) B2746175
theorem B4632491 : Blo 1829616 4632491 := bstep (se 1 (by rfl) ⟨3474368, by rfl⟩ : syracuseStep 4632491 = 6948737) B6948737
theorem B6950879 : Blo 1829616 6950879 := bstep (se 1 (by rfl) ⟨5213159, by rfl⟩ : syracuseStep 6950879 = 10426319) B10426319
theorem B6180839 : Blo 1829616 6180839 := bstep (se 1 (by rfl) ⟨4635629, by rfl⟩ : syracuseStep 6180839 = 9271259) B9271259
theorem B1830895 : Blo 1829616 1830895 := bstep (se 1 (by rfl) ⟨1373171, by rfl⟩ : syracuseStep 1830895 = 2746343) B2746343
theorem B1830907 : Blo 1829616 1830907 := bstep (se 1 (by rfl) ⟨1373180, by rfl⟩ : syracuseStep 1830907 = 2746361) B2746361
theorem B1830975 : Blo 1829616 1830975 := bstep (se 1 (by rfl) ⟨1373231, by rfl⟩ : syracuseStep 1830975 = 2746463) B2746463
theorem B2060383 : Blo 1829616 2060383 := bstep (se 1 (by rfl) ⟨1545287, by rfl⟩ : syracuseStep 2060383 = 3090575) B3090575
theorem B1831015 : Blo 1829616 1831015 := bstep (se 1 (by rfl) ⟨1373261, by rfl⟩ : syracuseStep 1831015 = 2746523) B2746523
theorem B1831039 : Blo 1829616 1831039 := bstep (se 1 (by rfl) ⟨1373279, by rfl⟩ : syracuseStep 1831039 = 2746559) B2746559
theorem B5566607 : Blo 1829616 5566607 := bstep (se 1 (by rfl) ⟨4174955, by rfl⟩ : syracuseStep 5566607 = 8349911) B8349911
theorem B1831067 : Blo 1829616 1831067 := bstep (se 1 (by rfl) ⟨1373300, by rfl⟩ : syracuseStep 1831067 = 2746601) B2746601
theorem B5861639 : Blo 1829616 5861639 := bstep (se 1 (by rfl) ⟨4396229, by rfl⟩ : syracuseStep 5861639 = 8792459) B8792459
theorem B52785431 : Blo 1829616 52785431 := bstep (se 1 (by rfl) ⟨39589073, by rfl⟩ : syracuseStep 52785431 = 79178147) B79178147
theorem B4116833 : Blo 1829616 4116833 := bstep (se 2 (by rfl) ⟨1543812, by rfl⟩ : syracuseStep 4116833 = 3087625) B3087625
theorem B6181217 : Blo 1829616 6181217 := bstep (se 2 (by rfl) ⟨2317956, by rfl⟩ : syracuseStep 6181217 = 4635913) B4635913
theorem B1831271 : Blo 1829616 1831271 := bstep (se 1 (by rfl) ⟨1373453, by rfl⟩ : syracuseStep 1831271 = 2746907) B2746907
theorem B1831323 : Blo 1829616 1831323 := bstep (se 1 (by rfl) ⟨1373492, by rfl⟩ : syracuseStep 1831323 = 2746985) B2746985
theorem B4116923 : Blo 1829616 4116923 := bstep (se 1 (by rfl) ⟨3087692, by rfl⟩ : syracuseStep 4116923 = 6175385) B6175385
theorem B31265351 : Blo 1829616 31265351 := bstep (se 1 (by rfl) ⟨23449013, by rfl⟩ : syracuseStep 31265351 = 46898027) B46898027
theorem B9900857 : Blo 1829616 9900857 := bstep (se 2 (by rfl) ⟨3712821, by rfl⟩ : syracuseStep 9900857 = 7425643) B7425643
theorem B6951851 : Blo 1829616 6951851 := bstep (se 1 (by rfl) ⟨5213888, by rfl⟩ : syracuseStep 6951851 = 10427777) B10427777
theorem B9270287 : Blo 1829616 9270287 := bstep (se 1 (by rfl) ⟨6952715, by rfl⟩ : syracuseStep 9270287 = 13905431) B13905431
theorem B31274099 : Blo 1829616 31274099 := bstep (se 1 (by rfl) ⟨23455574, by rfl⟩ : syracuseStep 31274099 = 46911149) B46911149
theorem B63403249 : Blo 1829616 63403249 := bstep (se 2 (by rfl) ⟨23776218, by rfl⟩ : syracuseStep 63403249 = 47552437) B47552437
theorem B26383603 : Blo 1829616 26383603 := bstep (se 1 (by rfl) ⟨19787702, by rfl⟩ : syracuseStep 26383603 = 39575405) B39575405
theorem B15635753 : Blo 1829616 15635753 := bstep (se 2 (by rfl) ⟨5863407, by rfl⟩ : syracuseStep 15635753 = 11726815) B11726815
theorem B5215529 : Blo 1829616 5215529 := bstep (se 2 (by rfl) ⟨1955823, by rfl⟩ : syracuseStep 5215529 = 3911647) B3911647
theorem B4118183 : Blo 1829616 4118183 := bstep (se 1 (by rfl) ⟨3088637, by rfl⟩ : syracuseStep 4118183 = 6177275) B6177275
theorem B24090295 : Blo 1829616 24090295 := bstep (se 1 (by rfl) ⟨18067721, by rfl⟩ : syracuseStep 24090295 = 36135443) B36135443
theorem B9271097 : Blo 1829616 9271097 := bstep (se 2 (by rfl) ⟨3476661, by rfl⟩ : syracuseStep 9271097 = 6953323) B6953323
theorem B5863229 : Blo 1829616 5863229 := bstep (se 3 (by rfl) ⟨1099355, by rfl⟩ : syracuseStep 5863229 = 2198711) B2198711
theorem B4118363 : Blo 1829616 4118363 := bstep (se 1 (by rfl) ⟨3088772, by rfl⟩ : syracuseStep 4118363 = 6177545) B6177545
theorem B9394139 : Blo 1829616 9394139 := bstep (se 1 (by rfl) ⟨7045604, by rfl⟩ : syracuseStep 9394139 = 14091209) B14091209
theorem B4397095 : Blo 1829616 4397095 := bstep (se 1 (by rfl) ⟨3297821, by rfl⟩ : syracuseStep 4397095 = 6595643) B6595643
theorem B29702315 : Blo 1829616 29702315 := bstep (se 1 (by rfl) ⟨22276736, by rfl⟩ : syracuseStep 29702315 = 44553473) B44553473
theorem B17602753 : Blo 1829616 17602753 := bstep (se 2 (by rfl) ⟨6601032, by rfl⟩ : syracuseStep 17602753 = 13202065) B13202065
theorem B9894091 : Blo 1829616 9894091 := bstep (se 1 (by rfl) ⟨7420568, by rfl⟩ : syracuseStep 9894091 = 14841137) B14841137
theorem B4118867 : Blo 1829616 4118867 := bstep (se 1 (by rfl) ⟨3089150, by rfl⟩ : syracuseStep 4118867 = 6178301) B6178301
theorem B9271745 : Blo 1829616 9271745 := bstep (se 2 (by rfl) ⟨3476904, by rfl⟩ : syracuseStep 9271745 = 6953809) B6953809
theorem B17603027 : Blo 1829616 17603027 := bstep (se 1 (by rfl) ⟨13202270, by rfl⟩ : syracuseStep 17603027 = 26404541) B26404541
theorem B10427069 : Blo 1829616 10427069 := bstep (se 3 (by rfl) ⟨1955075, by rfl⟩ : syracuseStep 10427069 = 3910151) B3910151
theorem B4119353 : Blo 1829616 4119353 := bstep (se 2 (by rfl) ⟨1544757, by rfl⟩ : syracuseStep 4119353 = 3089515) B3089515
theorem B4119407 : Blo 1829616 4119407 := bstep (se 1 (by rfl) ⟨3089555, by rfl⟩ : syracuseStep 4119407 = 6179111) B6179111
theorem B6175655 : Blo 1829616 6175655 := bstep (se 1 (by rfl) ⟨4631741, by rfl⟩ : syracuseStep 6175655 = 9263483) B9263483
theorem B14851097 : Blo 1829616 14851097 := bstep (se 2 (by rfl) ⟨5569161, by rfl⟩ : syracuseStep 14851097 = 11138323) B11138323
theorem B6954113 : Blo 1829616 6954113 := bstep (se 2 (by rfl) ⟨2607792, by rfl⟩ : syracuseStep 6954113 = 5215585) B5215585
theorem B4119983 : Blo 1829616 4119983 := bstep (se 1 (by rfl) ⟨3089987, by rfl⟩ : syracuseStep 4119983 = 6179975) B6179975
theorem B9264617 : Blo 1829616 9264617 := bstep (se 2 (by rfl) ⟨3474231, by rfl⟩ : syracuseStep 9264617 = 6948463) B6948463
theorem B4120055 : Blo 1829616 4120055 := bstep (se 1 (by rfl) ⟨3090041, by rfl⟩ : syracuseStep 4120055 = 6180083) B6180083
theorem B3088091 : Blo 1829616 3088091 := bstep (se 1 (by rfl) ⟨2316068, by rfl⟩ : syracuseStep 3088091 = 4632137) B4632137
theorem B14090107 : Blo 1829616 14090107 := bstep (se 1 (by rfl) ⟨10567580, by rfl⟩ : syracuseStep 14090107 = 21135161) B21135161
theorem B3088361 : Blo 1829616 3088361 := bstep (se 2 (by rfl) ⟨1158135, by rfl⟩ : syracuseStep 3088361 = 2316271) B2316271
theorem B3711071 : Blo 1829616 3711071 := bstep (se 1 (by rfl) ⟨2783303, by rfl⟩ : syracuseStep 3711071 = 5566607) B5566607
theorem B3907759 : Blo 1829616 3907759 := bstep (se 1 (by rfl) ⟨2930819, by rfl⟩ : syracuseStep 3907759 = 5861639) B5861639
theorem B2744555 : Blo 1829616 2744555 := bstep (se 1 (by rfl) ⟨2058416, by rfl⟩ : syracuseStep 2744555 = 4116833) B4116833
theorem B4120811 : Blo 1829616 4120811 := bstep (se 1 (by rfl) ⟨3090608, by rfl⟩ : syracuseStep 4120811 = 6181217) B6181217
theorem B23470337 : Blo 1829616 23470337 := bstep (se 2 (by rfl) ⟨8801376, by rfl⟩ : syracuseStep 23470337 = 17602753) B17602753
theorem B5800211 : Blo 1829616 5800211 := bstep (se 1 (by rfl) ⟨4350158, by rfl⟩ : syracuseStep 5800211 = 8700317) B8700317
theorem B2744615 : Blo 1829616 2744615 := bstep (se 1 (by rfl) ⟨2058461, by rfl⟩ : syracuseStep 2744615 = 4116923) B4116923
theorem B5865767 : Blo 1829616 5865767 := bstep (se 1 (by rfl) ⟨4399325, by rfl⟩ : syracuseStep 5865767 = 8798651) B8798651
theorem B2745065 : Blo 1829616 2745065 := bstep (se 2 (by rfl) ⟨1029399, by rfl⟩ : syracuseStep 2745065 = 2058799) B2058799
theorem B20849399 : Blo 1829616 20849399 := bstep (se 1 (by rfl) ⟨15637049, by rfl⟩ : syracuseStep 20849399 = 31274099) B31274099
theorem B6177707 : Blo 1829616 6177707 := bstep (se 1 (by rfl) ⟨4633280, by rfl⟩ : syracuseStep 6177707 = 9266561) B9266561
theorem B5014639 : Blo 1829616 5014639 := bstep (se 1 (by rfl) ⟨3760979, by rfl⟩ : syracuseStep 5014639 = 7521959) B7521959
theorem B2745455 : Blo 1829616 2745455 := bstep (se 1 (by rfl) ⟨2059091, by rfl⟩ : syracuseStep 2745455 = 4118183) B4118183
theorem B6947963 : Blo 1829616 6947963 := bstep (se 1 (by rfl) ⟨5210972, by rfl⟩ : syracuseStep 6947963 = 10421945) B10421945
theorem B3908819 : Blo 1829616 3908819 := bstep (se 1 (by rfl) ⟨2931614, by rfl⟩ : syracuseStep 3908819 = 5863229) B5863229
theorem B8799455 : Blo 1829616 8799455 := bstep (se 1 (by rfl) ⟨6599591, by rfl⟩ : syracuseStep 8799455 = 13199183) B13199183
theorem B2745575 : Blo 1829616 2745575 := bstep (se 1 (by rfl) ⟨2059181, by rfl⟩ : syracuseStep 2745575 = 4118363) B4118363
theorem B14836985 : Blo 1829616 14836985 := bstep (se 2 (by rfl) ⟨5563869, by rfl⟩ : syracuseStep 14836985 = 11127739) B11127739
theorem B2745641 : Blo 1829616 2745641 := bstep (se 2 (by rfl) ⟨1029615, by rfl⟩ : syracuseStep 2745641 = 2059231) B2059231
theorem B6178247 : Blo 1829616 6178247 := bstep (se 1 (by rfl) ⟨4633685, by rfl⟩ : syracuseStep 6178247 = 9267371) B9267371
theorem B19801543 : Blo 1829616 19801543 := bstep (se 1 (by rfl) ⟨14851157, by rfl⟩ : syracuseStep 19801543 = 29702315) B29702315
theorem B2745911 : Blo 1829616 2745911 := bstep (se 1 (by rfl) ⟨2059433, by rfl⟩ : syracuseStep 2745911 = 4118867) B4118867
theorem B35178137 : Blo 1829616 35178137 := bstep (se 2 (by rfl) ⟨13191801, by rfl⟩ : syracuseStep 35178137 = 26383603) B26383603
theorem B6178571 : Blo 1829616 6178571 := bstep (se 1 (by rfl) ⟨4633928, by rfl⟩ : syracuseStep 6178571 = 9267857) B9267857
theorem B3475219 : Blo 1829616 3475219 := bstep (se 1 (by rfl) ⟨2606414, by rfl⟩ : syracuseStep 3475219 = 5212829) B5212829
theorem B2746235 : Blo 1829616 2746235 := bstep (se 1 (by rfl) ⟨2059676, by rfl⟩ : syracuseStep 2746235 = 4119353) B4119353
theorem B2746271 : Blo 1829616 2746271 := bstep (se 1 (by rfl) ⟨2059703, by rfl⟩ : syracuseStep 2746271 = 4119407) B4119407
theorem B2746505 : Blo 1829616 2746505 := bstep (se 2 (by rfl) ⟨1029939, by rfl⟩ : syracuseStep 2746505 = 2059879) B2059879
theorem B75122903 : Blo 1829616 75122903 := bstep (se 1 (by rfl) ⟨56342177, by rfl⟩ : syracuseStep 75122903 = 112684355) B112684355
theorem B2746655 : Blo 1829616 2746655 := bstep (se 1 (by rfl) ⟨2059991, by rfl⟩ : syracuseStep 2746655 = 4119983) B4119983
theorem B2746703 : Blo 1829616 2746703 := bstep (se 1 (by rfl) ⟨2060027, by rfl⟩ : syracuseStep 2746703 = 4120055) B4120055
theorem B2746793 : Blo 1829616 2746793 := bstep (se 2 (by rfl) ⟨1030047, by rfl⟩ : syracuseStep 2746793 = 2060095) B2060095
theorem B2058727 : Blo 1829616 2058727 := bstep (se 1 (by rfl) ⟨1544045, by rfl⟩ : syracuseStep 2058727 = 3088091) B3088091
theorem B18786809 : Blo 1829616 18786809 := bstep (se 2 (by rfl) ⟨7045053, by rfl⟩ : syracuseStep 18786809 = 14090107) B14090107
theorem B16697927 : Blo 1829616 16697927 := bstep (se 1 (by rfl) ⟨12523445, by rfl⟩ : syracuseStep 16697927 = 25046891) B25046891
theorem B2058907 : Blo 1829616 2058907 := bstep (se 1 (by rfl) ⟨1544180, by rfl⟩ : syracuseStep 2058907 = 3088361) B3088361
theorem B2747177 : Blo 1829616 2747177 := bstep (se 2 (by rfl) ⟨1030191, by rfl⟩ : syracuseStep 2747177 = 2060383) B2060383
theorem B13192121 : Blo 1829616 13192121 := bstep (se 2 (by rfl) ⟨4947045, by rfl⟩ : syracuseStep 13192121 = 9894091) B9894091
theorem B2747387 : Blo 1829616 2747387 := bstep (se 1 (by rfl) ⟨2060540, by rfl⟩ : syracuseStep 2747387 = 4121081) B4121081
theorem B20843567 : Blo 1829616 20843567 := bstep (se 1 (by rfl) ⟨15632675, by rfl⟩ : syracuseStep 20843567 = 31265351) B31265351
theorem B1829999 : Blo 1829616 1829999 := bstep (se 1 (by rfl) ⟨1372499, by rfl⟩ : syracuseStep 1829999 = 2744999) B2744999
theorem B2059375 : Blo 1829616 2059375 := bstep (se 1 (by rfl) ⟨1544531, by rfl⟩ : syracuseStep 2059375 = 3089063) B3089063
theorem B1830079 : Blo 1829616 1830079 := bstep (se 1 (by rfl) ⟨1372559, by rfl⟩ : syracuseStep 1830079 = 2745119) B2745119
theorem B1830095 : Blo 1829616 1830095 := bstep (se 1 (by rfl) ⟨1372571, by rfl⟩ : syracuseStep 1830095 = 2745143) B2745143
theorem B5942575 : Blo 1829616 5942575 := bstep (se 1 (by rfl) ⟨4456931, by rfl⟩ : syracuseStep 5942575 = 8913863) B8913863
theorem B1830215 : Blo 1829616 1830215 := bstep (se 1 (by rfl) ⟨1372661, by rfl⟩ : syracuseStep 1830215 = 2745323) B2745323
theorem B2059591 : Blo 1829616 2059591 := bstep (se 1 (by rfl) ⟨1544693, by rfl⟩ : syracuseStep 2059591 = 3089387) B3089387
theorem B6180191 : Blo 1829616 6180191 := bstep (se 1 (by rfl) ⟨4635143, by rfl⟩ : syracuseStep 6180191 = 9270287) B9270287
theorem B15633769 : Blo 1829616 15633769 := bstep (se 2 (by rfl) ⟨5862663, by rfl⟩ : syracuseStep 15633769 = 11725327) B11725327
theorem B35196281 : Blo 1829616 35196281 := bstep (se 2 (by rfl) ⟨13198605, by rfl⟩ : syracuseStep 35196281 = 26397211) B26397211
theorem B10423835 : Blo 1829616 10423835 := bstep (se 1 (by rfl) ⟨7817876, by rfl⟩ : syracuseStep 10423835 = 15635753) B15635753
theorem B3477019 : Blo 1829616 3477019 := bstep (se 1 (by rfl) ⟨2607764, by rfl⟩ : syracuseStep 3477019 = 5215529) B5215529
theorem B6950681 : Blo 1829616 6950681 := bstep (se 2 (by rfl) ⟨2606505, by rfl⟩ : syracuseStep 6950681 = 5213011) B5213011
theorem B5943071 : Blo 1829616 5943071 := bstep (se 1 (by rfl) ⟨4457303, by rfl⟩ : syracuseStep 5943071 = 8914607) B8914607
theorem B6180731 : Blo 1829616 6180731 := bstep (se 1 (by rfl) ⟨4635548, by rfl⟩ : syracuseStep 6180731 = 9271097) B9271097
theorem B6262759 : Blo 1829616 6262759 := bstep (se 1 (by rfl) ⟨4697069, by rfl⟩ : syracuseStep 6262759 = 9394139) B9394139
theorem B1830943 : Blo 1829616 1830943 := bstep (se 1 (by rfl) ⟨1373207, by rfl⟩ : syracuseStep 1830943 = 2746415) B2746415
theorem B1831119 : Blo 1829616 1831119 := bstep (se 1 (by rfl) ⟨1373339, by rfl⟩ : syracuseStep 1831119 = 2746679) B2746679
theorem B6951197 : Blo 1829616 6951197 := bstep (se 3 (by rfl) ⟨1303349, by rfl⟩ : syracuseStep 6951197 = 2606699) B2606699
theorem B6181163 : Blo 1829616 6181163 := bstep (se 1 (by rfl) ⟨4635872, by rfl⟩ : syracuseStep 6181163 = 9271745) B9271745
theorem B385626419 : Blo 1829616 385626419 := bstep (se 1 (by rfl) ⟨289219814, by rfl⟩ : syracuseStep 385626419 = 578439629) B578439629
theorem B11735351 : Blo 1829616 11735351 := bstep (se 1 (by rfl) ⟨8801513, by rfl⟩ : syracuseStep 11735351 = 17603027) B17603027
theorem B84537665 : Blo 1829616 84537665 := bstep (se 2 (by rfl) ⟨31701624, by rfl⟩ : syracuseStep 84537665 = 63403249) B63403249
theorem B1831239 : Blo 1829616 1831239 := bstep (se 1 (by rfl) ⟨1373429, by rfl⟩ : syracuseStep 1831239 = 2746859) B2746859
theorem B6951379 : Blo 1829616 6951379 := bstep (se 1 (by rfl) ⟨5213534, by rfl⟩ : syracuseStep 6951379 = 10427069) B10427069
theorem B4117103 : Blo 1829616 4117103 := bstep (se 1 (by rfl) ⟨3087827, by rfl⟩ : syracuseStep 4117103 = 6175655) B6175655
theorem B9900731 : Blo 1829616 9900731 := bstep (se 1 (by rfl) ⟨7425548, by rfl⟩ : syracuseStep 9900731 = 14851097) B14851097
theorem B7042157 : Blo 1829616 7042157 := bstep (se 3 (by rfl) ⟨1320404, by rfl⟩ : syracuseStep 7042157 = 2640809) B2640809
theorem B4633919 : Blo 1829616 4633919 := bstep (se 1 (by rfl) ⟨3475439, by rfl⟩ : syracuseStep 4633919 = 6950879) B6950879
theorem B5862793 : Blo 1829616 5862793 := bstep (se 2 (by rfl) ⟨2198547, by rfl⟩ : syracuseStep 5862793 = 4397095) B4397095
theorem B9262511 : Blo 1829616 9262511 := bstep (se 1 (by rfl) ⟨6946883, by rfl⟩ : syracuseStep 9262511 = 13893767) B13893767
theorem B380515781 : Blo 1829616 380515781 := bstep (se 4 (by rfl) ⟨35673354, by rfl⟩ : syracuseStep 380515781 = 71346709) B71346709
theorem B25400807 : Blo 1829616 25400807 := bstep (se 1 (by rfl) ⟨19050605, by rfl⟩ : syracuseStep 25400807 = 38101211) B38101211
theorem B7525889 : Blo 1829616 7525889 := bstep (se 2 (by rfl) ⟨2822208, by rfl⟩ : syracuseStep 7525889 = 5644417) B5644417
theorem B35190287 : Blo 1829616 35190287 := bstep (se 1 (by rfl) ⟨26392715, by rfl⟩ : syracuseStep 35190287 = 52785431) B52785431
theorem B9901723 : Blo 1829616 9901723 := bstep (se 1 (by rfl) ⟨7426292, by rfl⟩ : syracuseStep 9901723 = 14852585) B14852585
theorem B10426067 : Blo 1829616 10426067 := bstep (se 1 (by rfl) ⟨7819550, by rfl⟩ : syracuseStep 10426067 = 15639101) B15639101
theorem B4118255 : Blo 1829616 4118255 := bstep (se 1 (by rfl) ⟨3088691, by rfl⟩ : syracuseStep 4118255 = 6177383) B6177383
theorem B21124955 : Blo 1829616 21124955 := bstep (se 1 (by rfl) ⟨15843716, by rfl⟩ : syracuseStep 21124955 = 31687433) B31687433
theorem B6600571 : Blo 1829616 6600571 := bstep (se 1 (by rfl) ⟨4950428, by rfl⟩ : syracuseStep 6600571 = 9900857) B9900857
theorem B4634567 : Blo 1829616 4634567 := bstep (se 1 (by rfl) ⟨3475925, by rfl⟩ : syracuseStep 4634567 = 6951851) B6951851
theorem B10573949 : Blo 1829616 10573949 := bstep (se 3 (by rfl) ⟨1982615, by rfl⟩ : syracuseStep 10573949 = 3965231) B3965231
theorem B4635265 : Blo 1829616 4635265 := bstep (se 2 (by rfl) ⟨1738224, by rfl⟩ : syracuseStep 4635265 = 3476449) B3476449
theorem B6175817 : Blo 1829616 6175817 := bstep (se 2 (by rfl) ⟨2315931, by rfl⟩ : syracuseStep 6175817 = 4631863) B4631863
theorem B4119659 : Blo 1829616 4119659 := bstep (se 1 (by rfl) ⟨3089744, by rfl⟩ : syracuseStep 4119659 = 6179489) B6179489
theorem B4119803 : Blo 1829616 4119803 := bstep (se 1 (by rfl) ⟨3089852, by rfl⟩ : syracuseStep 4119803 = 6179705) B6179705
theorem B3087679 : Blo 1829616 3087679 := bstep (se 1 (by rfl) ⟨2315759, by rfl⟩ : syracuseStep 3087679 = 4631519) B4631519
theorem B4119929 : Blo 1829616 4119929 := bstep (se 2 (by rfl) ⟨1544973, by rfl⟩ : syracuseStep 4119929 = 3089947) B3089947
theorem B3087787 : Blo 1829616 3087787 := bstep (se 1 (by rfl) ⟨2315840, by rfl⟩ : syracuseStep 3087787 = 4631681) B4631681
theorem B4636075 : Blo 1829616 4636075 := bstep (se 1 (by rfl) ⟨3477056, by rfl⟩ : syracuseStep 4636075 = 6954113) B6954113
theorem B32120393 : Blo 1829616 32120393 := bstep (se 2 (by rfl) ⟨12045147, by rfl⟩ : syracuseStep 32120393 = 24090295) B24090295
theorem B6176411 : Blo 1829616 6176411 := bstep (se 1 (by rfl) ⟨4632308, by rfl⟩ : syracuseStep 6176411 = 9264617) B9264617
theorem B3088327 : Blo 1829616 3088327 := bstep (se 1 (by rfl) ⟨2316245, by rfl⟩ : syracuseStep 3088327 = 4632491) B4632491
theorem B4120559 : Blo 1829616 4120559 := bstep (se 1 (by rfl) ⟨3090419, by rfl⟩ : syracuseStep 4120559 = 6180839) B6180839
theorem B2474047 : Blo 1829616 2474047 := bstep (se 1 (by rfl) ⟨1855535, by rfl⟩ : syracuseStep 2474047 = 3711071) B3711071
theorem B15646891 : Blo 1829616 15646891 := bstep (se 1 (by rfl) ⟨11735168, by rfl⟩ : syracuseStep 15646891 = 23470337) B23470337
theorem B3866807 : Blo 1829616 3866807 := bstep (se 1 (by rfl) ⟨2900105, by rfl⟩ : syracuseStep 3866807 = 5800211) B5800211
theorem B4120775 : Blo 1829616 4120775 := bstep (se 1 (by rfl) ⟨3090581, by rfl⟩ : syracuseStep 4120775 = 6181163) B6181163
theorem B7823567 : Blo 1829616 7823567 := bstep (se 1 (by rfl) ⟨5867675, by rfl⟩ : syracuseStep 7823567 = 11735351) B11735351
theorem B5210345 : Blo 1829616 5210345 := bstep (se 2 (by rfl) ⟨1953879, by rfl⟩ : syracuseStep 5210345 = 3907759) B3907759
theorem B28197197 : Blo 1829616 28197197 := bstep (se 3 (by rfl) ⟨5286974, by rfl⟩ : syracuseStep 28197197 = 10573949) B10573949
theorem B2744735 : Blo 1829616 2744735 := bstep (se 1 (by rfl) ⟨2058551, by rfl⟩ : syracuseStep 2744735 = 4117103) B4117103
theorem B2744969 : Blo 1829616 2744969 := bstep (se 2 (by rfl) ⟨1029363, by rfl⟩ : syracuseStep 2744969 = 2058727) B2058727
theorem B4694771 : Blo 1829616 4694771 := bstep (se 1 (by rfl) ⟨3521078, by rfl⟩ : syracuseStep 4694771 = 7042157) B7042157
theorem B2605879 : Blo 1829616 2605879 := bstep (se 1 (by rfl) ⟨1954409, by rfl⟩ : syracuseStep 2605879 = 3908819) B3908819
theorem B2745209 : Blo 1829616 2745209 := bstep (se 2 (by rfl) ⟨1029453, by rfl⟩ : syracuseStep 2745209 = 2058907) B2058907
theorem B3089279 : Blo 1829616 3089279 := bstep (se 1 (by rfl) ⟨2316959, by rfl⟩ : syracuseStep 3089279 = 4633919) B4633919
theorem B16933871 : Blo 1829616 16933871 := bstep (se 1 (by rfl) ⟨12700403, by rfl⟩ : syracuseStep 16933871 = 25400807) B25400807
theorem B2745503 : Blo 1829616 2745503 := bstep (se 1 (by rfl) ⟨2059127, by rfl⟩ : syracuseStep 2745503 = 4118255) B4118255
theorem B14083303 : Blo 1829616 14083303 := bstep (se 1 (by rfl) ⟨10562477, by rfl⟩ : syracuseStep 14083303 = 21124955) B21124955
theorem B3089711 : Blo 1829616 3089711 := bstep (se 1 (by rfl) ⟨2317283, by rfl⟩ : syracuseStep 3089711 = 4634567) B4634567
theorem B2745833 : Blo 1829616 2745833 := bstep (se 2 (by rfl) ⟨1029687, by rfl⟩ : syracuseStep 2745833 = 2059375) B2059375
theorem B7923433 : Blo 1829616 7923433 := bstep (se 2 (by rfl) ⟨2971287, by rfl⟩ : syracuseStep 7923433 = 5942575) B5942575
theorem B2746121 : Blo 1829616 2746121 := bstep (se 2 (by rfl) ⟨1029795, by rfl⟩ : syracuseStep 2746121 = 2059591) B2059591
theorem B7817057 : Blo 1829616 7817057 := bstep (se 2 (by rfl) ⟨2931396, by rfl⟩ : syracuseStep 7817057 = 5862793) B5862793
theorem B35203045 : Blo 1829616 35203045 := bstep (se 4 (by rfl) ⟨3300285, by rfl⟩ : syracuseStep 35203045 = 6600571) B6600571
theorem B13895711 : Blo 1829616 13895711 := bstep (se 1 (by rfl) ⟨10421783, by rfl⟩ : syracuseStep 13895711 = 20843567) B20843567
theorem B2746439 : Blo 1829616 2746439 := bstep (se 1 (by rfl) ⟨2059829, by rfl⟩ : syracuseStep 2746439 = 4119659) B4119659
theorem B2746535 : Blo 1829616 2746535 := bstep (se 1 (by rfl) ⟨2059901, by rfl⟩ : syracuseStep 2746535 = 4119803) B4119803
theorem B23464187 : Blo 1829616 23464187 := bstep (se 1 (by rfl) ⟨17598140, by rfl⟩ : syracuseStep 23464187 = 35196281) B35196281
theorem B2746619 : Blo 1829616 2746619 := bstep (se 1 (by rfl) ⟨2059964, by rfl⟩ : syracuseStep 2746619 = 4119929) B4119929
theorem B6949223 : Blo 1829616 6949223 := bstep (se 1 (by rfl) ⟨5211917, by rfl⟩ : syracuseStep 6949223 = 10423835) B10423835
theorem B8350345 : Blo 1829616 8350345 := bstep (se 2 (by rfl) ⟨3131379, by rfl⟩ : syracuseStep 8350345 = 6262759) B6262759
theorem B2747039 : Blo 1829616 2747039 := bstep (se 1 (by rfl) ⟨2060279, by rfl⟩ : syracuseStep 2747039 = 4120559) B4120559
theorem B1829703 : Blo 1829616 1829703 := bstep (se 1 (by rfl) ⟨1372277, by rfl⟩ : syracuseStep 1829703 = 2744555) B2744555
theorem B2747207 : Blo 1829616 2747207 := bstep (se 1 (by rfl) ⟨2060405, by rfl⟩ : syracuseStep 2747207 = 4120811) B4120811
theorem B1829743 : Blo 1829616 1829743 := bstep (se 1 (by rfl) ⟨1372307, by rfl⟩ : syracuseStep 1829743 = 2744615) B2744615
theorem B3910511 : Blo 1829616 3910511 := bstep (se 1 (by rfl) ⟨2932883, by rfl⟩ : syracuseStep 3910511 = 5865767) B5865767
theorem B257084279 : Blo 1829616 257084279 := bstep (se 1 (by rfl) ⟨192813209, by rfl⟩ : syracuseStep 257084279 = 385626419) B385626419
theorem B1830043 : Blo 1829616 1830043 := bstep (se 1 (by rfl) ⟨1372532, by rfl⟩ : syracuseStep 1830043 = 2745065) B2745065
theorem B23465213 : Blo 1829616 23465213 := bstep (se 3 (by rfl) ⟨4399727, by rfl⟩ : syracuseStep 23465213 = 8799455) B8799455
theorem B9268505 : Blo 1829616 9268505 := bstep (se 2 (by rfl) ⟨3475689, by rfl⟩ : syracuseStep 9268505 = 6951379) B6951379
theorem B1830303 : Blo 1829616 1830303 := bstep (se 1 (by rfl) ⟨1372727, by rfl⟩ : syracuseStep 1830303 = 2745455) B2745455
theorem B4631975 : Blo 1829616 4631975 := bstep (se 1 (by rfl) ⟨3473981, by rfl⟩ : syracuseStep 4631975 = 6947963) B6947963
theorem B342617525 : Blo 1829616 342617525 := bstep (se 5 (by rfl) ⟨16060196, by rfl⟩ : syracuseStep 342617525 = 32120393) B32120393
theorem B1830383 : Blo 1829616 1830383 := bstep (se 1 (by rfl) ⟨1372787, by rfl⟩ : syracuseStep 1830383 = 2745575) B2745575
theorem B9891323 : Blo 1829616 9891323 := bstep (se 1 (by rfl) ⟨7418492, by rfl⟩ : syracuseStep 9891323 = 14836985) B14836985
theorem B6180353 : Blo 1829616 6180353 := bstep (se 2 (by rfl) ⟨2317632, by rfl⟩ : syracuseStep 6180353 = 4635265) B4635265
theorem B1830427 : Blo 1829616 1830427 := bstep (se 1 (by rfl) ⟨1372820, by rfl⟩ : syracuseStep 1830427 = 2745641) B2745641
theorem B253677187 : Blo 1829616 253677187 := bstep (se 1 (by rfl) ⟨190257890, by rfl⟩ : syracuseStep 253677187 = 380515781) B380515781
theorem B5017259 : Blo 1829616 5017259 := bstep (se 1 (by rfl) ⟨3762944, by rfl⟩ : syracuseStep 5017259 = 7525889) B7525889
theorem B1830607 : Blo 1829616 1830607 := bstep (se 1 (by rfl) ⟨1372955, by rfl⟩ : syracuseStep 1830607 = 2745911) B2745911
theorem B6950711 : Blo 1829616 6950711 := bstep (se 1 (by rfl) ⟨5213033, by rfl⟩ : syracuseStep 6950711 = 10426067) B10426067
theorem B1830823 : Blo 1829616 1830823 := bstep (se 1 (by rfl) ⟨1373117, by rfl⟩ : syracuseStep 1830823 = 2746235) B2746235
theorem B1830847 : Blo 1829616 1830847 := bstep (se 1 (by rfl) ⟨1373135, by rfl⟩ : syracuseStep 1830847 = 2746271) B2746271
theorem B1831003 : Blo 1829616 1831003 := bstep (se 1 (by rfl) ⟨1373252, by rfl⟩ : syracuseStep 1831003 = 2746505) B2746505
theorem B50081935 : Blo 1829616 50081935 := bstep (se 1 (by rfl) ⟨37561451, by rfl⟩ : syracuseStep 50081935 = 75122903) B75122903
theorem B1831103 : Blo 1829616 1831103 := bstep (se 1 (by rfl) ⟨1373327, by rfl⟩ : syracuseStep 1831103 = 2746655) B2746655
theorem B1831135 : Blo 1829616 1831135 := bstep (se 1 (by rfl) ⟨1373351, by rfl⟩ : syracuseStep 1831135 = 2746703) B2746703
theorem B1831195 : Blo 1829616 1831195 := bstep (se 1 (by rfl) ⟨1373396, by rfl⟩ : syracuseStep 1831195 = 2746793) B2746793
theorem B4116905 : Blo 1829616 4116905 := bstep (se 2 (by rfl) ⟨1543839, by rfl⟩ : syracuseStep 4116905 = 3087679) B3087679
theorem B20845025 : Blo 1829616 20845025 := bstep (se 2 (by rfl) ⟨7816884, by rfl⟩ : syracuseStep 20845025 = 15633769) B15633769
theorem B1831451 : Blo 1829616 1831451 := bstep (se 1 (by rfl) ⟨1373588, by rfl⟩ : syracuseStep 1831451 = 2747177) B2747177
theorem B4117049 : Blo 1829616 4117049 := bstep (se 2 (by rfl) ⟨1543893, by rfl⟩ : syracuseStep 4117049 = 3087787) B3087787
theorem B6181433 : Blo 1829616 6181433 := bstep (se 2 (by rfl) ⟨2318037, by rfl⟩ : syracuseStep 6181433 = 4636075) B4636075
theorem B8794747 : Blo 1829616 8794747 := bstep (se 1 (by rfl) ⟨6596060, by rfl⟩ : syracuseStep 8794747 = 13192121) B13192121
theorem B1831591 : Blo 1829616 1831591 := bstep (se 1 (by rfl) ⟨1373693, by rfl⟩ : syracuseStep 1831591 = 2747387) B2747387
theorem B4117211 : Blo 1829616 4117211 := bstep (se 1 (by rfl) ⟨3087908, by rfl⟩ : syracuseStep 4117211 = 6175817) B6175817
theorem B13202297 : Blo 1829616 13202297 := bstep (se 2 (by rfl) ⟨4950861, by rfl⟩ : syracuseStep 13202297 = 9901723) B9901723
theorem B4633625 : Blo 1829616 4633625 := bstep (se 2 (by rfl) ⟨1737609, by rfl⟩ : syracuseStep 4633625 = 3475219) B3475219
theorem B4117607 : Blo 1829616 4117607 := bstep (se 1 (by rfl) ⟨3088205, by rfl⟩ : syracuseStep 4117607 = 6176411) B6176411
theorem B4633787 : Blo 1829616 4633787 := bstep (se 1 (by rfl) ⟨3475340, by rfl⟩ : syracuseStep 4633787 = 6950681) B6950681
theorem B3962047 : Blo 1829616 3962047 := bstep (se 1 (by rfl) ⟨2971535, by rfl⟩ : syracuseStep 3962047 = 5943071) B5943071
theorem B4117769 : Blo 1829616 4117769 := bstep (se 2 (by rfl) ⟨1544163, by rfl⟩ : syracuseStep 4117769 = 3088327) B3088327
theorem B4634131 : Blo 1829616 4634131 := bstep (se 1 (by rfl) ⟨3475598, by rfl⟩ : syracuseStep 4634131 = 6951197) B6951197
theorem B56358443 : Blo 1829616 56358443 := bstep (se 1 (by rfl) ⟨42268832, by rfl⟩ : syracuseStep 56358443 = 84537665) B84537665
theorem B6600487 : Blo 1829616 6600487 := bstep (se 1 (by rfl) ⟨4950365, by rfl⟩ : syracuseStep 6600487 = 9900731) B9900731
theorem B13899599 : Blo 1829616 13899599 := bstep (se 1 (by rfl) ⟨10424699, by rfl⟩ : syracuseStep 13899599 = 20849399) B20849399
theorem B26744741 : Blo 1829616 26744741 := bstep (se 4 (by rfl) ⟨2507319, by rfl⟩ : syracuseStep 26744741 = 5014639) B5014639
theorem B4118471 : Blo 1829616 4118471 := bstep (se 1 (by rfl) ⟨3088853, by rfl⟩ : syracuseStep 4118471 = 6177707) B6177707
theorem B6175007 : Blo 1829616 6175007 := bstep (se 1 (by rfl) ⟨4631255, by rfl⟩ : syracuseStep 6175007 = 9262511) B9262511
theorem B4118831 : Blo 1829616 4118831 := bstep (se 1 (by rfl) ⟨3089123, by rfl⟩ : syracuseStep 4118831 = 6178247) B6178247
theorem B23460191 : Blo 1829616 23460191 := bstep (se 1 (by rfl) ⟨17595143, by rfl⟩ : syracuseStep 23460191 = 35190287) B35190287
theorem B23452091 : Blo 1829616 23452091 := bstep (se 1 (by rfl) ⟨17589068, by rfl⟩ : syracuseStep 23452091 = 35178137) B35178137
theorem B4119047 : Blo 1829616 4119047 := bstep (se 1 (by rfl) ⟨3089285, by rfl⟩ : syracuseStep 4119047 = 6178571) B6178571
theorem B12524539 : Blo 1829616 12524539 := bstep (se 1 (by rfl) ⟨9393404, by rfl⟩ : syracuseStep 12524539 = 18786809) B18786809
theorem B11131951 : Blo 1829616 11131951 := bstep (se 1 (by rfl) ⟨8348963, by rfl⟩ : syracuseStep 11131951 = 16697927) B16697927
theorem B26402057 : Blo 1829616 26402057 := bstep (se 2 (by rfl) ⟨9900771, by rfl⟩ : syracuseStep 26402057 = 19801543) B19801543
theorem B4636025 : Blo 1829616 4636025 := bstep (se 2 (by rfl) ⟨1738509, by rfl⟩ : syracuseStep 4636025 = 3477019) B3477019
theorem B4120127 : Blo 1829616 4120127 := bstep (se 1 (by rfl) ⟨3090095, by rfl⟩ : syracuseStep 4120127 = 6180191) B6180191
theorem B4120487 : Blo 1829616 4120487 := bstep (se 1 (by rfl) ⟨3090365, by rfl⟩ : syracuseStep 4120487 = 6180731) B6180731
theorem B2744603 : Blo 1829616 2744603 := bstep (se 1 (by rfl) ⟨2058452, by rfl⟩ : syracuseStep 2744603 = 4116905) B4116905
theorem B2744699 : Blo 1829616 2744699 := bstep (se 1 (by rfl) ⟨2058524, by rfl⟩ : syracuseStep 2744699 = 4117049) B4117049
theorem B4120955 : Blo 1829616 4120955 := bstep (se 1 (by rfl) ⟨3090716, by rfl⟩ : syracuseStep 4120955 = 6181433) B6181433
theorem B2744807 : Blo 1829616 2744807 := bstep (se 1 (by rfl) ⟨2058605, by rfl⟩ : syracuseStep 2744807 = 4117211) B4117211
theorem B3129847 : Blo 1829616 3129847 := bstep (se 1 (by rfl) ⟨2347385, by rfl⟩ : syracuseStep 3129847 = 4694771) B4694771
theorem B13894253 : Blo 1829616 13894253 := bstep (se 3 (by rfl) ⟨2605172, by rfl⟩ : syracuseStep 13894253 = 5210345) B5210345
theorem B3089083 : Blo 1829616 3089083 := bstep (se 1 (by rfl) ⟨2316812, by rfl⟩ : syracuseStep 3089083 = 4633625) B4633625
theorem B2745071 : Blo 1829616 2745071 := bstep (se 1 (by rfl) ⟨2058803, by rfl⟩ : syracuseStep 2745071 = 4117607) B4117607
theorem B3089191 : Blo 1829616 3089191 := bstep (se 1 (by rfl) ⟨2316893, by rfl⟩ : syracuseStep 3089191 = 4633787) B4633787
theorem B2745179 : Blo 1829616 2745179 := bstep (se 1 (by rfl) ⟨2058884, by rfl⟩ : syracuseStep 2745179 = 4117769) B4117769
theorem B11133793 : Blo 1829616 11133793 := bstep (se 2 (by rfl) ⟨4175172, by rfl⟩ : syracuseStep 11133793 = 8350345) B8350345
theorem B3474505 : Blo 1829616 3474505 := bstep (se 2 (by rfl) ⟨1302939, by rfl⟩ : syracuseStep 3474505 = 2605879) B2605879
theorem B9266399 : Blo 1829616 9266399 := bstep (se 1 (by rfl) ⟨6949799, by rfl⟩ : syracuseStep 9266399 = 13899599) B13899599
theorem B5211371 : Blo 1829616 5211371 := bstep (se 1 (by rfl) ⟨3908528, by rfl⟩ : syracuseStep 5211371 = 7817057) B7817057
theorem B2745647 : Blo 1829616 2745647 := bstep (se 1 (by rfl) ⟨2059235, by rfl⟩ : syracuseStep 2745647 = 4118471) B4118471
theorem B2745887 : Blo 1829616 2745887 := bstep (se 1 (by rfl) ⟨2059415, by rfl⟩ : syracuseStep 2745887 = 4118831) B4118831
theorem B15640127 : Blo 1829616 15640127 := bstep (se 1 (by rfl) ⟨11730095, by rfl⟩ : syracuseStep 15640127 = 23460191) B23460191
theorem B18777737 : Blo 1829616 18777737 := bstep (se 2 (by rfl) ⟨7041651, by rfl⟩ : syracuseStep 18777737 = 14083303) B14083303
theorem B2746031 : Blo 1829616 2746031 := bstep (se 1 (by rfl) ⟨2059523, by rfl⟩ : syracuseStep 2746031 = 4119047) B4119047
theorem B2607007 : Blo 1829616 2607007 := bstep (se 1 (by rfl) ⟨1955255, by rfl⟩ : syracuseStep 2607007 = 3910511) B3910511
theorem B6178841 : Blo 1829616 6178841 := bstep (se 2 (by rfl) ⟨2317065, by rfl⟩ : syracuseStep 6178841 = 4634131) B4634131
theorem B6179003 : Blo 1829616 6179003 := bstep (se 1 (by rfl) ⟨4634252, by rfl⟩ : syracuseStep 6179003 = 9268505) B9268505
theorem B3090683 : Blo 1829616 3090683 := bstep (se 1 (by rfl) ⟨2318012, by rfl⟩ : syracuseStep 3090683 = 4636025) B4636025
theorem B228411683 : Blo 1829616 228411683 := bstep (se 1 (by rfl) ⟨171308762, by rfl⟩ : syracuseStep 228411683 = 342617525) B342617525
theorem B2746751 : Blo 1829616 2746751 := bstep (se 1 (by rfl) ⟨2060063, by rfl⟩ : syracuseStep 2746751 = 4120127) B4120127
theorem B8800649 : Blo 1829616 8800649 := bstep (se 2 (by rfl) ⟨3300243, by rfl⟩ : syracuseStep 8800649 = 6600487) B6600487
theorem B3344839 : Blo 1829616 3344839 := bstep (se 1 (by rfl) ⟨2508629, by rfl⟩ : syracuseStep 3344839 = 5017259) B5017259
theorem B2746991 : Blo 1829616 2746991 := bstep (se 1 (by rfl) ⟨2060243, by rfl⟩ : syracuseStep 2746991 = 4120487) B4120487
theorem B45156989 : Blo 1829616 45156989 := bstep (se 3 (by rfl) ⟨8466935, by rfl⟩ : syracuseStep 45156989 = 16933871) B16933871
theorem B2747183 : Blo 1829616 2747183 := bstep (se 1 (by rfl) ⟨2060387, by rfl⟩ : syracuseStep 2747183 = 4120775) B4120775
theorem B66775913 : Blo 1829616 66775913 := bstep (se 2 (by rfl) ⟨25040967, by rfl⟩ : syracuseStep 66775913 = 50081935) B50081935
theorem B1829823 : Blo 1829616 1829823 := bstep (se 1 (by rfl) ⟨1372367, by rfl⟩ : syracuseStep 1829823 = 2744735) B2744735
theorem B13896683 : Blo 1829616 13896683 := bstep (se 1 (by rfl) ⟨10422512, by rfl⟩ : syracuseStep 13896683 = 20845025) B20845025
theorem B1829979 : Blo 1829616 1829979 := bstep (se 1 (by rfl) ⟨1372484, by rfl⟩ : syracuseStep 1829979 = 2744969) B2744969
theorem B1830139 : Blo 1829616 1830139 := bstep (se 1 (by rfl) ⟨1372604, by rfl⟩ : syracuseStep 1830139 = 2745209) B2745209
theorem B8801531 : Blo 1829616 8801531 := bstep (se 1 (by rfl) ⟨6601148, by rfl⟩ : syracuseStep 8801531 = 13202297) B13202297
theorem B2059519 : Blo 1829616 2059519 := bstep (se 1 (by rfl) ⟨1544639, by rfl⟩ : syracuseStep 2059519 = 3089279) B3089279
theorem B1830335 : Blo 1829616 1830335 := bstep (se 1 (by rfl) ⟨1372751, by rfl⟩ : syracuseStep 1830335 = 2745503) B2745503
theorem B11726329 : Blo 1829616 11726329 := bstep (se 2 (by rfl) ⟨4397373, by rfl⟩ : syracuseStep 11726329 = 8794747) B8794747
theorem B2059807 : Blo 1829616 2059807 := bstep (se 1 (by rfl) ⟨1544855, by rfl⟩ : syracuseStep 2059807 = 3089711) B3089711
theorem B1830555 : Blo 1829616 1830555 := bstep (se 1 (by rfl) ⟨1372916, by rfl⟩ : syracuseStep 1830555 = 2745833) B2745833
theorem B37572295 : Blo 1829616 37572295 := bstep (se 1 (by rfl) ⟨28179221, by rfl⟩ : syracuseStep 37572295 = 56358443) B56358443
theorem B1830747 : Blo 1829616 1830747 := bstep (se 1 (by rfl) ⟨1373060, by rfl⟩ : syracuseStep 1830747 = 2746121) B2746121
theorem B17829827 : Blo 1829616 17829827 := bstep (se 1 (by rfl) ⟨13372370, by rfl⟩ : syracuseStep 17829827 = 26744741) B26744741
theorem B16699385 : Blo 1829616 16699385 := bstep (se 2 (by rfl) ⟨6262269, by rfl⟩ : syracuseStep 16699385 = 12524539) B12524539
theorem B1830959 : Blo 1829616 1830959 := bstep (se 1 (by rfl) ⟨1373219, by rfl⟩ : syracuseStep 1830959 = 2746439) B2746439
theorem B1831023 : Blo 1829616 1831023 := bstep (se 1 (by rfl) ⟨1373267, by rfl⟩ : syracuseStep 1831023 = 2746535) B2746535
theorem B15642791 : Blo 1829616 15642791 := bstep (se 1 (by rfl) ⟨11732093, by rfl⟩ : syracuseStep 15642791 = 23464187) B23464187
theorem B1831079 : Blo 1829616 1831079 := bstep (se 1 (by rfl) ⟨1373309, by rfl⟩ : syracuseStep 1831079 = 2746619) B2746619
theorem B4116671 : Blo 1829616 4116671 := bstep (se 1 (by rfl) ⟨3087503, by rfl⟩ : syracuseStep 4116671 = 6175007) B6175007
theorem B4632815 : Blo 1829616 4632815 := bstep (se 1 (by rfl) ⟨3474611, by rfl⟩ : syracuseStep 4632815 = 6949223) B6949223
theorem B15634727 : Blo 1829616 15634727 := bstep (se 1 (by rfl) ⟨11726045, by rfl⟩ : syracuseStep 15634727 = 23452091) B23452091
theorem B1831359 : Blo 1829616 1831359 := bstep (se 1 (by rfl) ⟨1373519, by rfl⟩ : syracuseStep 1831359 = 2747039) B2747039
theorem B1831471 : Blo 1829616 1831471 := bstep (se 1 (by rfl) ⟨1373603, by rfl⟩ : syracuseStep 1831471 = 2747207) B2747207
theorem B171389519 : Blo 1829616 171389519 := bstep (se 1 (by rfl) ⟨128542139, by rfl⟩ : syracuseStep 171389519 = 257084279) B257084279
theorem B15643475 : Blo 1829616 15643475 := bstep (se 1 (by rfl) ⟨11732606, by rfl⟩ : syracuseStep 15643475 = 23465213) B23465213
theorem B338236249 : Blo 1829616 338236249 := bstep (se 2 (by rfl) ⟨126838593, by rfl⟩ : syracuseStep 338236249 = 253677187) B253677187
theorem B17601371 : Blo 1829616 17601371 := bstep (se 1 (by rfl) ⟨13201028, by rfl⟩ : syracuseStep 17601371 = 26402057) B26402057
theorem B10564577 : Blo 1829616 10564577 := bstep (se 2 (by rfl) ⟨3961716, by rfl⟩ : syracuseStep 10564577 = 7923433) B7923433
theorem B4633807 : Blo 1829616 4633807 := bstep (se 1 (by rfl) ⟨3475355, by rfl⟩ : syracuseStep 4633807 = 6950711) B6950711
theorem B46937393 : Blo 1829616 46937393 := bstep (se 2 (by rfl) ⟨17601522, by rfl⟩ : syracuseStep 46937393 = 35203045) B35203045
theorem B3298729 : Blo 1829616 3298729 := bstep (se 2 (by rfl) ⟨1237023, by rfl⟩ : syracuseStep 3298729 = 2474047) B2474047
theorem B2577871 : Blo 1829616 2577871 := bstep (se 1 (by rfl) ⟨1933403, by rfl⟩ : syracuseStep 2577871 = 3866807) B3866807
theorem B5215711 : Blo 1829616 5215711 := bstep (se 1 (by rfl) ⟨3911783, by rfl⟩ : syracuseStep 5215711 = 7823567) B7823567
theorem B18798131 : Blo 1829616 18798131 := bstep (se 1 (by rfl) ⟨14098598, by rfl⟩ : syracuseStep 18798131 = 28197197) B28197197
theorem B20862521 : Blo 1829616 20862521 := bstep (se 2 (by rfl) ⟨7823445, by rfl⟩ : syracuseStep 20862521 = 15646891) B15646891
theorem B9263807 : Blo 1829616 9263807 := bstep (se 1 (by rfl) ⟨6947855, by rfl⟩ : syracuseStep 9263807 = 13895711) B13895711
theorem B14842601 : Blo 1829616 14842601 := bstep (se 2 (by rfl) ⟨5565975, by rfl⟩ : syracuseStep 14842601 = 11131951) B11131951
theorem B5282729 : Blo 1829616 5282729 := bstep (se 2 (by rfl) ⟨1981023, by rfl⟩ : syracuseStep 5282729 = 3962047) B3962047
theorem B3087983 : Blo 1829616 3087983 := bstep (se 1 (by rfl) ⟨2315987, by rfl⟩ : syracuseStep 3087983 = 4631975) B4631975
theorem B6594215 : Blo 1829616 6594215 := bstep (se 1 (by rfl) ⟨4945661, by rfl⟩ : syracuseStep 6594215 = 9891323) B9891323
theorem B4120235 : Blo 1829616 4120235 := bstep (se 1 (by rfl) ⟨3090176, by rfl⟩ : syracuseStep 4120235 = 6180353) B6180353
theorem B10428527 : Blo 1829616 10428527 := bstep (se 1 (by rfl) ⟨7821395, by rfl⟩ : syracuseStep 10428527 = 15642791) B15642791
theorem B2744447 : Blo 1829616 2744447 := bstep (se 1 (by rfl) ⟨2058335, by rfl⟩ : syracuseStep 2744447 = 4116671) B4116671
theorem B3088543 : Blo 1829616 3088543 := bstep (se 1 (by rfl) ⟨2316407, by rfl⟩ : syracuseStep 3088543 = 4632815) B4632815
theorem B10428983 : Blo 1829616 10428983 := bstep (se 1 (by rfl) ⟨7821737, by rfl⟩ : syracuseStep 10428983 = 15643475) B15643475
theorem B6177599 : Blo 1829616 6177599 := bstep (se 1 (by rfl) ⟨4633199, by rfl⟩ : syracuseStep 6177599 = 9266399) B9266399
theorem B3474247 : Blo 1829616 3474247 := bstep (se 1 (by rfl) ⟨2605685, by rfl⟩ : syracuseStep 3474247 = 5211371) B5211371
theorem B12518491 : Blo 1829616 12518491 := bstep (se 1 (by rfl) ⟨9388868, by rfl⟩ : syracuseStep 12518491 = 18777737) B18777737
theorem B152274455 : Blo 1829616 152274455 := bstep (se 1 (by rfl) ⟨114205841, by rfl⟩ : syracuseStep 152274455 = 228411683) B228411683
theorem B5867099 : Blo 1829616 5867099 := bstep (se 1 (by rfl) ⟨4400324, by rfl⟩ : syracuseStep 5867099 = 8800649) B8800649
theorem B6178409 : Blo 1829616 6178409 := bstep (se 2 (by rfl) ⟨2316903, by rfl⟩ : syracuseStep 6178409 = 4633807) B4633807
theorem B2746025 : Blo 1829616 2746025 := bstep (se 2 (by rfl) ⟨1029759, by rfl⟩ : syracuseStep 2746025 = 2059519) B2059519
theorem B44517275 : Blo 1829616 44517275 := bstep (se 1 (by rfl) ⟨33387956, by rfl⟩ : syracuseStep 44517275 = 66775913) B66775913
theorem B2746409 : Blo 1829616 2746409 := bstep (se 2 (by rfl) ⟨1029903, by rfl⟩ : syracuseStep 2746409 = 2059807) B2059807
theorem B5867687 : Blo 1829616 5867687 := bstep (se 1 (by rfl) ⟨4400765, by rfl⟩ : syracuseStep 5867687 = 8801531) B8801531
theorem B50096393 : Blo 1829616 50096393 := bstep (se 2 (by rfl) ⟨18786147, by rfl⟩ : syracuseStep 50096393 = 37572295) B37572295
theorem B2058655 : Blo 1829616 2058655 := bstep (se 1 (by rfl) ⟨1543991, by rfl⟩ : syracuseStep 2058655 = 3087983) B3087983
theorem B2746823 : Blo 1829616 2746823 := bstep (se 1 (by rfl) ⟨2060117, by rfl⟩ : syracuseStep 2746823 = 4120235) B4120235
theorem B3476009 : Blo 1829616 3476009 := bstep (se 2 (by rfl) ⟨1303503, by rfl⟩ : syracuseStep 3476009 = 2607007) B2607007
theorem B1829735 : Blo 1829616 1829735 := bstep (se 1 (by rfl) ⟨1372301, by rfl⟩ : syracuseStep 1829735 = 2744603) B2744603
theorem B10423151 : Blo 1829616 10423151 := bstep (se 1 (by rfl) ⟨7817363, by rfl⟩ : syracuseStep 10423151 = 15634727) B15634727
theorem B1829799 : Blo 1829616 1829799 := bstep (se 1 (by rfl) ⟨1372349, by rfl⟩ : syracuseStep 1829799 = 2744699) B2744699
theorem B2747303 : Blo 1829616 2747303 := bstep (se 1 (by rfl) ⟨2060477, by rfl⟩ : syracuseStep 2747303 = 4120955) B4120955
theorem B1829871 : Blo 1829616 1829871 := bstep (se 1 (by rfl) ⟨1372403, by rfl⟩ : syracuseStep 1829871 = 2744807) B2744807
theorem B1830047 : Blo 1829616 1830047 := bstep (se 1 (by rfl) ⟨1372535, by rfl⟩ : syracuseStep 1830047 = 2745071) B2745071
theorem B1830119 : Blo 1829616 1830119 := bstep (se 1 (by rfl) ⟨1372589, by rfl⟩ : syracuseStep 1830119 = 2745179) B2745179
theorem B11734247 : Blo 1829616 11734247 := bstep (se 1 (by rfl) ⟨8800685, by rfl⟩ : syracuseStep 11734247 = 17601371) B17601371
theorem B1830431 : Blo 1829616 1830431 := bstep (se 1 (by rfl) ⟨1372823, by rfl⟩ : syracuseStep 1830431 = 2745647) B2745647
theorem B1830591 : Blo 1829616 1830591 := bstep (se 1 (by rfl) ⟨1372943, by rfl⟩ : syracuseStep 1830591 = 2745887) B2745887
theorem B11132923 : Blo 1829616 11132923 := bstep (se 1 (by rfl) ⟨8349692, by rfl⟩ : syracuseStep 11132923 = 16699385) B16699385
theorem B1830687 : Blo 1829616 1830687 := bstep (se 1 (by rfl) ⟨1373015, by rfl⟩ : syracuseStep 1830687 = 2746031) B2746031
theorem B450981665 : Blo 1829616 450981665 := bstep (se 2 (by rfl) ⟨169118124, by rfl⟩ : syracuseStep 450981665 = 338236249) B338236249
theorem B4632673 : Blo 1829616 4632673 := bstep (se 2 (by rfl) ⟨1737252, by rfl⟩ : syracuseStep 4632673 = 3474505) B3474505
theorem B71356565 : Blo 1829616 71356565 := bstep (se 6 (by rfl) ⟨1672419, by rfl⟩ : syracuseStep 71356565 = 3344839) B3344839
theorem B2060455 : Blo 1829616 2060455 := bstep (se 1 (by rfl) ⟨1545341, by rfl⟩ : syracuseStep 2060455 = 3090683) B3090683
theorem B1831167 : Blo 1829616 1831167 := bstep (se 1 (by rfl) ⟨1373375, by rfl⟩ : syracuseStep 1831167 = 2746751) B2746751
theorem B1831327 : Blo 1829616 1831327 := bstep (se 1 (by rfl) ⟨1373495, by rfl⟩ : syracuseStep 1831327 = 2746991) B2746991
theorem B17584573 : Blo 1829616 17584573 := bstep (se 3 (by rfl) ⟨3297107, by rfl⟩ : syracuseStep 17584573 = 6594215) B6594215
theorem B59380229 : Blo 1829616 59380229 := bstep (se 4 (by rfl) ⟨5566896, by rfl⟩ : syracuseStep 59380229 = 11133793) B11133793
theorem B1831455 : Blo 1829616 1831455 := bstep (se 1 (by rfl) ⟨1373591, by rfl⟩ : syracuseStep 1831455 = 2747183) B2747183
theorem B3437161 : Blo 1829616 3437161 := bstep (se 2 (by rfl) ⟨1288935, by rfl⟩ : syracuseStep 3437161 = 2577871) B2577871
theorem B15635105 : Blo 1829616 15635105 := bstep (se 2 (by rfl) ⟨5863164, by rfl⟩ : syracuseStep 15635105 = 11726329) B11726329
theorem B16692517 : Blo 1829616 16692517 := bstep (se 4 (by rfl) ⟨1564923, by rfl⟩ : syracuseStep 16692517 = 3129847) B3129847
theorem B114259679 : Blo 1829616 114259679 := bstep (se 1 (by rfl) ⟨85694759, by rfl⟩ : syracuseStep 114259679 = 171389519) B171389519
theorem B9262835 : Blo 1829616 9262835 := bstep (se 1 (by rfl) ⟨6947126, by rfl⟩ : syracuseStep 9262835 = 13894253) B13894253
theorem B7043051 : Blo 1829616 7043051 := bstep (se 1 (by rfl) ⟨5282288, by rfl⟩ : syracuseStep 7043051 = 10564577) B10564577
theorem B31291595 : Blo 1829616 31291595 := bstep (se 1 (by rfl) ⟨23468696, by rfl⟩ : syracuseStep 31291595 = 46937393) B46937393
theorem B4118777 : Blo 1829616 4118777 := bstep (se 2 (by rfl) ⟨1544541, by rfl⟩ : syracuseStep 4118777 = 3089083) B3089083
theorem B12532087 : Blo 1829616 12532087 := bstep (se 1 (by rfl) ⟨9399065, by rfl⟩ : syracuseStep 12532087 = 18798131) B18798131
theorem B13908347 : Blo 1829616 13908347 := bstep (se 1 (by rfl) ⟨10431260, by rfl⟩ : syracuseStep 13908347 = 20862521) B20862521
theorem B10426751 : Blo 1829616 10426751 := bstep (se 1 (by rfl) ⟨7820063, by rfl⟩ : syracuseStep 10426751 = 15640127) B15640127
theorem B4118921 : Blo 1829616 4118921 := bstep (se 2 (by rfl) ⟨1544595, by rfl⟩ : syracuseStep 4118921 = 3089191) B3089191
theorem B4119227 : Blo 1829616 4119227 := bstep (se 1 (by rfl) ⟨3089420, by rfl⟩ : syracuseStep 4119227 = 6178841) B6178841
theorem B4119335 : Blo 1829616 4119335 := bstep (se 1 (by rfl) ⟨3089501, by rfl⟩ : syracuseStep 4119335 = 6179003) B6179003
theorem B30104659 : Blo 1829616 30104659 := bstep (se 1 (by rfl) ⟨22578494, by rfl⟩ : syracuseStep 30104659 = 45156989) B45156989
theorem B6175871 : Blo 1829616 6175871 := bstep (se 1 (by rfl) ⟨4631903, by rfl⟩ : syracuseStep 6175871 = 9263807) B9263807
theorem B9895067 : Blo 1829616 9895067 := bstep (se 1 (by rfl) ⟨7421300, by rfl⟩ : syracuseStep 9895067 = 14842601) B14842601
theorem B4398305 : Blo 1829616 4398305 := bstep (se 2 (by rfl) ⟨1649364, by rfl⟩ : syracuseStep 4398305 = 3298729) B3298729
theorem B3521819 : Blo 1829616 3521819 := bstep (se 1 (by rfl) ⟨2641364, by rfl⟩ : syracuseStep 3521819 = 5282729) B5282729
theorem B6954281 : Blo 1829616 6954281 := bstep (se 2 (by rfl) ⟨2607855, by rfl⟩ : syracuseStep 6954281 = 5215711) B5215711
theorem B9264455 : Blo 1829616 9264455 := bstep (se 1 (by rfl) ⟨6948341, by rfl⟩ : syracuseStep 9264455 = 13896683) B13896683
theorem B11886551 : Blo 1829616 11886551 := bstep (se 1 (by rfl) ⟨8914913, by rfl⟩ : syracuseStep 11886551 = 17829827) B17829827
theorem B6176897 : Blo 1829616 6176897 := bstep (se 2 (by rfl) ⟨2316336, by rfl⟩ : syracuseStep 6176897 = 4632673) B4632673
theorem B190284173 : Blo 1829616 190284173 := bstep (se 3 (by rfl) ⟨35678282, by rfl⟩ : syracuseStep 190284173 = 71356565) B71356565
theorem B15647165 : Blo 1829616 15647165 := bstep (se 3 (by rfl) ⟨2933843, by rfl⟩ : syracuseStep 15647165 = 5867687) B5867687
theorem B2744873 : Blo 1829616 2744873 := bstep (se 2 (by rfl) ⟨1029327, by rfl⟩ : syracuseStep 2744873 = 2058655) B2058655
theorem B23446097 : Blo 1829616 23446097 := bstep (se 2 (by rfl) ⟨8792286, by rfl⟩ : syracuseStep 23446097 = 17584573) B17584573
theorem B101516303 : Blo 1829616 101516303 := bstep (se 1 (by rfl) ⟨76137227, by rfl⟩ : syracuseStep 101516303 = 152274455) B152274455
theorem B2745851 : Blo 1829616 2745851 := bstep (se 1 (by rfl) ⟨2059388, by rfl⟩ : syracuseStep 2745851 = 4118777) B4118777
theorem B2745947 : Blo 1829616 2745947 := bstep (se 1 (by rfl) ⟨2059460, by rfl⟩ : syracuseStep 2745947 = 4118921) B4118921
theorem B2746151 : Blo 1829616 2746151 := bstep (se 1 (by rfl) ⟨2059613, by rfl⟩ : syracuseStep 2746151 = 4119227) B4119227
theorem B2746223 : Blo 1829616 2746223 := bstep (se 1 (by rfl) ⟨2059667, by rfl⟩ : syracuseStep 2746223 = 4119335) B4119335
theorem B6948767 : Blo 1829616 6948767 := bstep (se 1 (by rfl) ⟨5211575, by rfl⟩ : syracuseStep 6948767 = 10423151) B10423151
theorem B6596711 : Blo 1829616 6596711 := bstep (se 1 (by rfl) ⟨4947533, by rfl⟩ : syracuseStep 6596711 = 9895067) B9895067
theorem B7924367 : Blo 1829616 7924367 := bstep (se 1 (by rfl) ⟨5943275, by rfl⟩ : syracuseStep 7924367 = 11886551) B11886551
theorem B1829631 : Blo 1829616 1829631 := bstep (se 1 (by rfl) ⟨1372223, by rfl⟩ : syracuseStep 1829631 = 2744447) B2744447
theorem B2747273 : Blo 1829616 2747273 := bstep (se 2 (by rfl) ⟨1030227, by rfl⟩ : syracuseStep 2747273 = 2060455) B2060455
theorem B39586819 : Blo 1829616 39586819 := bstep (se 1 (by rfl) ⟨29690114, by rfl⟩ : syracuseStep 39586819 = 59380229) B59380229
theorem B10423403 : Blo 1829616 10423403 := bstep (se 1 (by rfl) ⟨7817552, by rfl⟩ : syracuseStep 10423403 = 15635105) B15635105
theorem B3911399 : Blo 1829616 3911399 := bstep (se 1 (by rfl) ⟨2933549, by rfl⟩ : syracuseStep 3911399 = 5867099) B5867099
theorem B4632329 : Blo 1829616 4632329 := bstep (se 2 (by rfl) ⟨1737123, by rfl⟩ : syracuseStep 4632329 = 3474247) B3474247
theorem B1830683 : Blo 1829616 1830683 := bstep (se 1 (by rfl) ⟨1373012, by rfl⟩ : syracuseStep 1830683 = 2746025) B2746025
theorem B76173119 : Blo 1829616 76173119 := bstep (se 1 (by rfl) ⟨57129839, by rfl⟩ : syracuseStep 76173119 = 114259679) B114259679
theorem B1830939 : Blo 1829616 1830939 := bstep (se 1 (by rfl) ⟨1373204, by rfl⟩ : syracuseStep 1830939 = 2746409) B2746409
theorem B16691321 : Blo 1829616 16691321 := bstep (se 2 (by rfl) ⟨6259245, by rfl⟩ : syracuseStep 16691321 = 12518491) B12518491
theorem B20861063 : Blo 1829616 20861063 := bstep (se 1 (by rfl) ⟨15645797, by rfl⟩ : syracuseStep 20861063 = 31291595) B31291595
theorem B6951167 : Blo 1829616 6951167 := bstep (se 1 (by rfl) ⟨5213375, by rfl⟩ : syracuseStep 6951167 = 10426751) B10426751
theorem B1831215 : Blo 1829616 1831215 := bstep (se 1 (by rfl) ⟨1373411, by rfl⟩ : syracuseStep 1831215 = 2746823) B2746823
theorem B1831535 : Blo 1829616 1831535 := bstep (se 1 (by rfl) ⟨1373651, by rfl⟩ : syracuseStep 1831535 = 2747303) B2747303
theorem B4117247 : Blo 1829616 4117247 := bstep (se 1 (by rfl) ⟨3087935, by rfl⟩ : syracuseStep 4117247 = 6175871) B6175871
theorem B2347879 : Blo 1829616 2347879 := bstep (se 1 (by rfl) ⟨1760909, by rfl⟩ : syracuseStep 2347879 = 3521819) B3521819
theorem B18781469 : Blo 1829616 18781469 := bstep (se 3 (by rfl) ⟨3521525, by rfl⟩ : syracuseStep 18781469 = 7043051) B7043051
theorem B6952351 : Blo 1829616 6952351 := bstep (se 1 (by rfl) ⟨5214263, by rfl⟩ : syracuseStep 6952351 = 10428527) B10428527
theorem B4118057 : Blo 1829616 4118057 := bstep (se 2 (by rfl) ⟨1544271, by rfl⟩ : syracuseStep 4118057 = 3088543) B3088543
theorem B6952655 : Blo 1829616 6952655 := bstep (se 1 (by rfl) ⟨5214491, by rfl⟩ : syracuseStep 6952655 = 10428983) B10428983
theorem B4118399 : Blo 1829616 4118399 := bstep (se 1 (by rfl) ⟨3088799, by rfl⟩ : syracuseStep 4118399 = 6177599) B6177599
theorem B18331525 : Blo 1829616 18331525 := bstep (se 4 (by rfl) ⟨1718580, by rfl⟩ : syracuseStep 18331525 = 3437161) B3437161
theorem B11728813 : Blo 1829616 11728813 := bstep (se 3 (by rfl) ⟨2199152, by rfl⟩ : syracuseStep 11728813 = 4398305) B4398305
theorem B4118939 : Blo 1829616 4118939 := bstep (se 1 (by rfl) ⟨3089204, by rfl⟩ : syracuseStep 4118939 = 6178409) B6178409
theorem B6175223 : Blo 1829616 6175223 := bstep (se 1 (by rfl) ⟨4631417, by rfl⟩ : syracuseStep 6175223 = 9262835) B9262835
theorem B29678183 : Blo 1829616 29678183 := bstep (se 1 (by rfl) ⟨22258637, by rfl⟩ : syracuseStep 29678183 = 44517275) B44517275
theorem B40139545 : Blo 1829616 40139545 := bstep (se 2 (by rfl) ⟨15052329, by rfl⟩ : syracuseStep 40139545 = 30104659) B30104659
theorem B33397595 : Blo 1829616 33397595 := bstep (se 1 (by rfl) ⟨25048196, by rfl⟩ : syracuseStep 33397595 = 50096393) B50096393
theorem B9272231 : Blo 1829616 9272231 := bstep (se 1 (by rfl) ⟨6954173, by rfl⟩ : syracuseStep 9272231 = 13908347) B13908347
theorem B2317339 : Blo 1829616 2317339 := bstep (se 1 (by rfl) ⟨1738004, by rfl⟩ : syracuseStep 2317339 = 3476009) B3476009
theorem B22256689 : Blo 1829616 22256689 := bstep (se 2 (by rfl) ⟨8346258, by rfl⟩ : syracuseStep 22256689 = 16692517) B16692517
theorem B66837797 : Blo 1829616 66837797 := bstep (se 4 (by rfl) ⟨6266043, by rfl⟩ : syracuseStep 66837797 = 12532087) B12532087
theorem B7822831 : Blo 1829616 7822831 := bstep (se 1 (by rfl) ⟨5867123, by rfl⟩ : syracuseStep 7822831 = 11734247) B11734247
theorem B4636187 : Blo 1829616 4636187 := bstep (se 1 (by rfl) ⟨3477140, by rfl⟩ : syracuseStep 4636187 = 6954281) B6954281
theorem B6176303 : Blo 1829616 6176303 := bstep (se 1 (by rfl) ⟨4632227, by rfl⟩ : syracuseStep 6176303 = 9264455) B9264455
theorem B300654443 : Blo 1829616 300654443 := bstep (se 1 (by rfl) ⟨225490832, by rfl⟩ : syracuseStep 300654443 = 450981665) B450981665
theorem B14843897 : Blo 1829616 14843897 := bstep (se 2 (by rfl) ⟨5566461, by rfl⟩ : syracuseStep 14843897 = 11132923) B11132923
theorem B15630731 : Blo 1829616 15630731 := bstep (se 1 (by rfl) ⟨11723048, by rfl⟩ : syracuseStep 15630731 = 23446097) B23446097
theorem B2744831 : Blo 1829616 2744831 := bstep (se 1 (by rfl) ⟨2058623, by rfl⟩ : syracuseStep 2744831 = 4117247) B4117247
theorem B2745371 : Blo 1829616 2745371 := bstep (se 1 (by rfl) ⟨2059028, by rfl⟩ : syracuseStep 2745371 = 4118057) B4118057
theorem B53519393 : Blo 1829616 53519393 := bstep (se 2 (by rfl) ⟨20069772, by rfl⟩ : syracuseStep 53519393 = 40139545) B40139545
theorem B3130505 : Blo 1829616 3130505 := bstep (se 2 (by rfl) ⟨1173939, by rfl⟩ : syracuseStep 3130505 = 2347879) B2347879
theorem B2745599 : Blo 1829616 2745599 := bstep (se 1 (by rfl) ⟨2059199, by rfl⟩ : syracuseStep 2745599 = 4118399) B4118399
theorem B52782425 : Blo 1829616 52782425 := bstep (se 2 (by rfl) ⟨19793409, by rfl⟩ : syracuseStep 52782425 = 39586819) B39586819
theorem B3089785 : Blo 1829616 3089785 := bstep (se 2 (by rfl) ⟨1158669, by rfl⟩ : syracuseStep 3089785 = 2317339) B2317339
theorem B2745959 : Blo 1829616 2745959 := bstep (se 1 (by rfl) ⟨2059469, by rfl⟩ : syracuseStep 2745959 = 4118939) B4118939
theorem B19785455 : Blo 1829616 19785455 := bstep (se 1 (by rfl) ⟨14839091, by rfl⟩ : syracuseStep 19785455 = 29678183) B29678183
theorem B10430441 : Blo 1829616 10430441 := bstep (se 2 (by rfl) ⟨3911415, by rfl⟩ : syracuseStep 10430441 = 7822831) B7822831
theorem B6948935 : Blo 1829616 6948935 := bstep (se 1 (by rfl) ⟨5211701, by rfl⟩ : syracuseStep 6948935 = 10423403) B10423403
theorem B44558531 : Blo 1829616 44558531 := bstep (se 1 (by rfl) ⟨33418898, by rfl⟩ : syracuseStep 44558531 = 66837797) B66837797
theorem B3090791 : Blo 1829616 3090791 := bstep (se 1 (by rfl) ⟨2318093, by rfl⟩ : syracuseStep 3090791 = 4636187) B4636187
theorem B2607599 : Blo 1829616 2607599 := bstep (se 1 (by rfl) ⟨1955699, by rfl⟩ : syracuseStep 2607599 = 3911399) B3911399
theorem B200436295 : Blo 1829616 200436295 := bstep (se 1 (by rfl) ⟨150327221, by rfl⟩ : syracuseStep 200436295 = 300654443) B300654443
theorem B11127547 : Blo 1829616 11127547 := bstep (se 1 (by rfl) ⟨8345660, by rfl⟩ : syracuseStep 11127547 = 16691321) B16691321
theorem B126856115 : Blo 1829616 126856115 := bstep (se 1 (by rfl) ⟨95142086, by rfl⟩ : syracuseStep 126856115 = 190284173) B190284173
theorem B10431443 : Blo 1829616 10431443 := bstep (se 1 (by rfl) ⟨7823582, by rfl⟩ : syracuseStep 10431443 = 15647165) B15647165
theorem B1829915 : Blo 1829616 1829915 := bstep (se 1 (by rfl) ⟨1372436, by rfl⟩ : syracuseStep 1829915 = 2744873) B2744873
theorem B67677535 : Blo 1829616 67677535 := bstep (se 1 (by rfl) ⟨50758151, by rfl⟩ : syracuseStep 67677535 = 101516303) B101516303
theorem B12520979 : Blo 1829616 12520979 := bstep (se 1 (by rfl) ⟨9390734, by rfl⟩ : syracuseStep 12520979 = 18781469) B18781469
theorem B1830567 : Blo 1829616 1830567 := bstep (se 1 (by rfl) ⟨1372925, by rfl⟩ : syracuseStep 1830567 = 2745851) B2745851
theorem B1830631 : Blo 1829616 1830631 := bstep (se 1 (by rfl) ⟨1372973, by rfl⟩ : syracuseStep 1830631 = 2745947) B2745947
theorem B1830767 : Blo 1829616 1830767 := bstep (se 1 (by rfl) ⟨1373075, by rfl⟩ : syracuseStep 1830767 = 2746151) B2746151
theorem B1830815 : Blo 1829616 1830815 := bstep (se 1 (by rfl) ⟨1373111, by rfl⟩ : syracuseStep 1830815 = 2746223) B2746223
theorem B4632511 : Blo 1829616 4632511 := bstep (se 1 (by rfl) ⟨3474383, by rfl⟩ : syracuseStep 4632511 = 6948767) B6948767
theorem B29675585 : Blo 1829616 29675585 := bstep (se 2 (by rfl) ⟨11128344, by rfl⟩ : syracuseStep 29675585 = 22256689) B22256689
theorem B4116815 : Blo 1829616 4116815 := bstep (se 1 (by rfl) ⟨3087611, by rfl⟩ : syracuseStep 4116815 = 6175223) B6175223
theorem B9269801 : Blo 1829616 9269801 := bstep (se 2 (by rfl) ⟨3476175, by rfl⟩ : syracuseStep 9269801 = 6952351) B6952351
theorem B1831515 : Blo 1829616 1831515 := bstep (se 1 (by rfl) ⟨1373636, by rfl⟩ : syracuseStep 1831515 = 2747273) B2747273
theorem B6181487 : Blo 1829616 6181487 := bstep (se 1 (by rfl) ⟨4636115, by rfl⟩ : syracuseStep 6181487 = 9272231) B9272231
theorem B4117535 : Blo 1829616 4117535 := bstep (se 1 (by rfl) ⟨3088151, by rfl⟩ : syracuseStep 4117535 = 6176303) B6176303
theorem B24442033 : Blo 1829616 24442033 := bstep (se 2 (by rfl) ⟨9165762, by rfl⟩ : syracuseStep 24442033 = 18331525) B18331525
theorem B4117931 : Blo 1829616 4117931 := bstep (se 1 (by rfl) ⟨3088448, by rfl⟩ : syracuseStep 4117931 = 6176897) B6176897
theorem B13907375 : Blo 1829616 13907375 := bstep (se 1 (by rfl) ⟨10430531, by rfl⟩ : syracuseStep 13907375 = 20861063) B20861063
theorem B4634111 : Blo 1829616 4634111 := bstep (se 1 (by rfl) ⟨3475583, by rfl⟩ : syracuseStep 4634111 = 6951167) B6951167
theorem B4635103 : Blo 1829616 4635103 := bstep (se 1 (by rfl) ⟨3476327, by rfl⟩ : syracuseStep 4635103 = 6952655) B6952655
theorem B4397807 : Blo 1829616 4397807 := bstep (se 1 (by rfl) ⟨3298355, by rfl⟩ : syracuseStep 4397807 = 6596711) B6596711
theorem B5282911 : Blo 1829616 5282911 := bstep (se 1 (by rfl) ⟨3962183, by rfl⟩ : syracuseStep 5282911 = 7924367) B7924367
theorem B22265063 : Blo 1829616 22265063 := bstep (se 1 (by rfl) ⟨16698797, by rfl⟩ : syracuseStep 22265063 = 33397595) B33397595
theorem B3088219 : Blo 1829616 3088219 := bstep (se 1 (by rfl) ⟨2316164, by rfl⟩ : syracuseStep 3088219 = 4632329) B4632329
theorem B50782079 : Blo 1829616 50782079 := bstep (se 1 (by rfl) ⟨38086559, by rfl⟩ : syracuseStep 50782079 = 76173119) B76173119
theorem B15638417 : Blo 1829616 15638417 := bstep (se 2 (by rfl) ⟨5864406, by rfl⟩ : syracuseStep 15638417 = 11728813) B11728813
theorem B9895931 : Blo 1829616 9895931 := bstep (se 1 (by rfl) ⟨7421948, by rfl⟩ : syracuseStep 9895931 = 14843897) B14843897
theorem B19783723 : Blo 1829616 19783723 := bstep (se 1 (by rfl) ⟨14837792, by rfl⟩ : syracuseStep 19783723 = 29675585) B29675585
theorem B2744543 : Blo 1829616 2744543 := bstep (se 1 (by rfl) ⟨2058407, by rfl⟩ : syracuseStep 2744543 = 4116815) B4116815
theorem B10420487 : Blo 1829616 10420487 := bstep (se 1 (by rfl) ⟨7815365, by rfl⟩ : syracuseStep 10420487 = 15630731) B15630731
theorem B4120991 : Blo 1829616 4120991 := bstep (se 1 (by rfl) ⟨3090743, by rfl⟩ : syracuseStep 4120991 = 6181487) B6181487
theorem B2745023 : Blo 1829616 2745023 := bstep (se 1 (by rfl) ⟨2058767, by rfl⟩ : syracuseStep 2745023 = 4117535) B4117535
theorem B267248393 : Blo 1829616 267248393 := bstep (se 2 (by rfl) ⟨100218147, by rfl⟩ : syracuseStep 267248393 = 200436295) B200436295
theorem B2745287 : Blo 1829616 2745287 := bstep (se 1 (by rfl) ⟨2058965, by rfl⟩ : syracuseStep 2745287 = 4117931) B4117931
theorem B14836729 : Blo 1829616 14836729 := bstep (se 2 (by rfl) ⟨5563773, by rfl⟩ : syracuseStep 14836729 = 11127547) B11127547
theorem B3089407 : Blo 1829616 3089407 := bstep (se 1 (by rfl) ⟨2317055, by rfl⟩ : syracuseStep 3089407 = 4634111) B4634111
theorem B13190303 : Blo 1829616 13190303 := bstep (se 1 (by rfl) ⟨9892727, by rfl⟩ : syracuseStep 13190303 = 19785455) B19785455
theorem B29705687 : Blo 1829616 29705687 := bstep (se 1 (by rfl) ⟨22279265, by rfl⟩ : syracuseStep 29705687 = 44558531) B44558531
theorem B32589377 : Blo 1829616 32589377 := bstep (se 2 (by rfl) ⟨12221016, by rfl⟩ : syracuseStep 32589377 = 24442033) B24442033
theorem B90236713 : Blo 1829616 90236713 := bstep (se 2 (by rfl) ⟨33838767, by rfl⟩ : syracuseStep 90236713 = 67677535) B67677535
theorem B6597287 : Blo 1829616 6597287 := bstep (se 1 (by rfl) ⟨4947965, by rfl⟩ : syracuseStep 6597287 = 9895931) B9895931
theorem B1829887 : Blo 1829616 1829887 := bstep (se 1 (by rfl) ⟨1372415, by rfl⟩ : syracuseStep 1829887 = 2744831) B2744831
theorem B6179867 : Blo 1829616 6179867 := bstep (se 1 (by rfl) ⟨4634900, by rfl⟩ : syracuseStep 6179867 = 9269801) B9269801
theorem B28175525 : Blo 1829616 28175525 := bstep (se 4 (by rfl) ⟨2641455, by rfl⟩ : syracuseStep 28175525 = 5282911) B5282911
theorem B6180137 : Blo 1829616 6180137 := bstep (se 2 (by rfl) ⟨2317551, by rfl⟩ : syracuseStep 6180137 = 4635103) B4635103
theorem B1830247 : Blo 1829616 1830247 := bstep (se 1 (by rfl) ⟨1372685, by rfl⟩ : syracuseStep 1830247 = 2745371) B2745371
theorem B1830399 : Blo 1829616 1830399 := bstep (se 1 (by rfl) ⟨1372799, by rfl⟩ : syracuseStep 1830399 = 2745599) B2745599
theorem B35188283 : Blo 1829616 35188283 := bstep (se 1 (by rfl) ⟨26391212, by rfl⟩ : syracuseStep 35188283 = 52782425) B52782425
theorem B1830639 : Blo 1829616 1830639 := bstep (se 1 (by rfl) ⟨1372979, by rfl⟩ : syracuseStep 1830639 = 2745959) B2745959
theorem B4632623 : Blo 1829616 4632623 := bstep (se 1 (by rfl) ⟨3474467, by rfl⟩ : syracuseStep 4632623 = 6948935) B6948935
theorem B2060527 : Blo 1829616 2060527 := bstep (se 1 (by rfl) ⟨1545395, by rfl⟩ : syracuseStep 2060527 = 3090791) B3090791
theorem B84570743 : Blo 1829616 84570743 := bstep (se 1 (by rfl) ⟨63428057, by rfl⟩ : syracuseStep 84570743 = 126856115) B126856115
theorem B4117625 : Blo 1829616 4117625 := bstep (se 2 (by rfl) ⟨1544109, by rfl⟩ : syracuseStep 4117625 = 3088219) B3088219
theorem B33854719 : Blo 1829616 33854719 := bstep (se 1 (by rfl) ⟨25391039, by rfl⟩ : syracuseStep 33854719 = 50782079) B50782079
theorem B10425611 : Blo 1829616 10425611 := bstep (se 1 (by rfl) ⟨7819208, by rfl⟩ : syracuseStep 10425611 = 15638417) B15638417
theorem B142718381 : Blo 1829616 142718381 := bstep (se 3 (by rfl) ⟨26759696, by rfl⟩ : syracuseStep 142718381 = 53519393) B53519393
theorem B2087003 : Blo 1829616 2087003 := bstep (se 1 (by rfl) ⟨1565252, by rfl⟩ : syracuseStep 2087003 = 3130505) B3130505
theorem B9271583 : Blo 1829616 9271583 := bstep (se 1 (by rfl) ⟨6953687, by rfl⟩ : syracuseStep 9271583 = 13907375) B13907375
theorem B6953597 : Blo 1829616 6953597 := bstep (se 3 (by rfl) ⟨1303799, by rfl⟩ : syracuseStep 6953597 = 2607599) B2607599
theorem B6953627 : Blo 1829616 6953627 := bstep (se 1 (by rfl) ⟨5215220, by rfl⟩ : syracuseStep 6953627 = 10430441) B10430441
theorem B2931871 : Blo 1829616 2931871 := bstep (se 1 (by rfl) ⟨2198903, by rfl⟩ : syracuseStep 2931871 = 4397807) B4397807
theorem B4119713 : Blo 1829616 4119713 := bstep (se 2 (by rfl) ⟨1544892, by rfl⟩ : syracuseStep 4119713 = 3089785) B3089785
theorem B6954295 : Blo 1829616 6954295 := bstep (se 1 (by rfl) ⟨5215721, by rfl⟩ : syracuseStep 6954295 = 10431443) B10431443
theorem B14843375 : Blo 1829616 14843375 := bstep (se 1 (by rfl) ⟨11132531, by rfl⟩ : syracuseStep 14843375 = 22265063) B22265063
theorem B8347319 : Blo 1829616 8347319 := bstep (se 1 (by rfl) ⟨6260489, by rfl⟩ : syracuseStep 8347319 = 12520979) B12520979
theorem B6176681 : Blo 1829616 6176681 := bstep (se 2 (by rfl) ⟨2316255, by rfl⟩ : syracuseStep 6176681 = 4632511) B4632511
theorem B3088415 : Blo 1829616 3088415 := bstep (se 1 (by rfl) ⟨2316311, by rfl⟩ : syracuseStep 3088415 = 4632623) B4632623
theorem B26378297 : Blo 1829616 26378297 := bstep (se 2 (by rfl) ⟨9891861, by rfl⟩ : syracuseStep 26378297 = 19783723) B19783723
theorem B6946991 : Blo 1829616 6946991 := bstep (se 1 (by rfl) ⟨5210243, by rfl⟩ : syracuseStep 6946991 = 10420487) B10420487
theorem B2745083 : Blo 1829616 2745083 := bstep (se 1 (by rfl) ⟨2058812, by rfl⟩ : syracuseStep 2745083 = 4117625) B4117625
theorem B21726251 : Blo 1829616 21726251 := bstep (se 1 (by rfl) ⟨16294688, by rfl⟩ : syracuseStep 21726251 = 32589377) B32589377
theorem B3909161 : Blo 1829616 3909161 := bstep (se 2 (by rfl) ⟨1465935, by rfl⟩ : syracuseStep 3909161 = 2931871) B2931871
theorem B45139625 : Blo 1829616 45139625 := bstep (se 2 (by rfl) ⟨16927359, by rfl⟩ : syracuseStep 45139625 = 33854719) B33854719
theorem B2746475 : Blo 1829616 2746475 := bstep (se 1 (by rfl) ⟨2059856, by rfl⟩ : syracuseStep 2746475 = 4119713) B4119713
theorem B5564879 : Blo 1829616 5564879 := bstep (se 1 (by rfl) ⟨4173659, by rfl⟩ : syracuseStep 5564879 = 8347319) B8347319
theorem B1829695 : Blo 1829616 1829695 := bstep (se 1 (by rfl) ⟨1372271, by rfl⟩ : syracuseStep 1829695 = 2744543) B2744543
theorem B5565341 : Blo 1829616 5565341 := bstep (se 3 (by rfl) ⟨1043501, by rfl⟩ : syracuseStep 5565341 = 2087003) B2087003
theorem B2747327 : Blo 1829616 2747327 := bstep (se 1 (by rfl) ⟨2060495, by rfl⟩ : syracuseStep 2747327 = 4120991) B4120991
theorem B2747369 : Blo 1829616 2747369 := bstep (se 2 (by rfl) ⟨1030263, by rfl⟩ : syracuseStep 2747369 = 2060527) B2060527
theorem B56380495 : Blo 1829616 56380495 := bstep (se 1 (by rfl) ⟨42285371, by rfl⟩ : syracuseStep 56380495 = 84570743) B84570743
theorem B1830015 : Blo 1829616 1830015 := bstep (se 1 (by rfl) ⟨1372511, by rfl⟩ : syracuseStep 1830015 = 2745023) B2745023
theorem B1830191 : Blo 1829616 1830191 := bstep (se 1 (by rfl) ⟨1372643, by rfl⟩ : syracuseStep 1830191 = 2745287) B2745287
theorem B8793535 : Blo 1829616 8793535 := bstep (se 1 (by rfl) ⟨6595151, by rfl⟩ : syracuseStep 8793535 = 13190303) B13190303
theorem B6950407 : Blo 1829616 6950407 := bstep (se 1 (by rfl) ⟨5212805, by rfl⟩ : syracuseStep 6950407 = 10425611) B10425611
theorem B95145587 : Blo 1829616 95145587 := bstep (se 1 (by rfl) ⟨71359190, by rfl⟩ : syracuseStep 95145587 = 142718381) B142718381
theorem B19803791 : Blo 1829616 19803791 := bstep (se 1 (by rfl) ⟨14852843, by rfl⟩ : syracuseStep 19803791 = 29705687) B29705687
theorem B6181055 : Blo 1829616 6181055 := bstep (se 1 (by rfl) ⟨4635791, by rfl⟩ : syracuseStep 6181055 = 9271583) B9271583
theorem B23458855 : Blo 1829616 23458855 := bstep (se 1 (by rfl) ⟨17594141, by rfl⟩ : syracuseStep 23458855 = 35188283) B35188283
theorem B4117787 : Blo 1829616 4117787 := bstep (se 1 (by rfl) ⟨3088340, by rfl⟩ : syracuseStep 4117787 = 6176681) B6176681
theorem B178165595 : Blo 1829616 178165595 := bstep (se 1 (by rfl) ⟨133624196, by rfl⟩ : syracuseStep 178165595 = 267248393) B267248393
theorem B19782305 : Blo 1829616 19782305 := bstep (se 2 (by rfl) ⟨7418364, by rfl⟩ : syracuseStep 19782305 = 14836729) B14836729
theorem B4119209 : Blo 1829616 4119209 := bstep (se 2 (by rfl) ⟨1544703, by rfl⟩ : syracuseStep 4119209 = 3089407) B3089407
theorem B9272393 : Blo 1829616 9272393 := bstep (se 2 (by rfl) ⟨3477147, by rfl⟩ : syracuseStep 9272393 = 6954295) B6954295
theorem B4635731 : Blo 1829616 4635731 := bstep (se 1 (by rfl) ⟨3476798, by rfl⟩ : syracuseStep 4635731 = 6953597) B6953597
theorem B4635751 : Blo 1829616 4635751 := bstep (se 1 (by rfl) ⟨3476813, by rfl⟩ : syracuseStep 4635751 = 6953627) B6953627
theorem B4398191 : Blo 1829616 4398191 := bstep (se 1 (by rfl) ⟨3298643, by rfl⟩ : syracuseStep 4398191 = 6597287) B6597287
theorem B4119911 : Blo 1829616 4119911 := bstep (se 1 (by rfl) ⟨3089933, by rfl⟩ : syracuseStep 4119911 = 6179867) B6179867
theorem B18783683 : Blo 1829616 18783683 := bstep (se 1 (by rfl) ⟨14087762, by rfl⟩ : syracuseStep 18783683 = 28175525) B28175525
theorem B4120091 : Blo 1829616 4120091 := bstep (se 1 (by rfl) ⟨3090068, by rfl⟩ : syracuseStep 4120091 = 6180137) B6180137
theorem B9895583 : Blo 1829616 9895583 := bstep (se 1 (by rfl) ⟨7421687, by rfl⟩ : syracuseStep 9895583 = 14843375) B14843375
theorem B120315617 : Blo 1829616 120315617 := bstep (se 2 (by rfl) ⟨45118356, by rfl⟩ : syracuseStep 120315617 = 90236713) B90236713
theorem B4120703 : Blo 1829616 4120703 := bstep (se 1 (by rfl) ⟨3090527, by rfl⟩ : syracuseStep 4120703 = 6181055) B6181055
theorem B14484167 : Blo 1829616 14484167 := bstep (se 1 (by rfl) ⟨10863125, by rfl⟩ : syracuseStep 14484167 = 21726251) B21726251
theorem B2745191 : Blo 1829616 2745191 := bstep (se 1 (by rfl) ⟨2058893, by rfl⟩ : syracuseStep 2745191 = 4117787) B4117787
theorem B2606107 : Blo 1829616 2606107 := bstep (se 1 (by rfl) ⟨1954580, by rfl⟩ : syracuseStep 2606107 = 3909161) B3909161
theorem B118777063 : Blo 1829616 118777063 := bstep (se 1 (by rfl) ⟨89082797, by rfl⟩ : syracuseStep 118777063 = 178165595) B178165595
theorem B31278473 : Blo 1829616 31278473 := bstep (se 2 (by rfl) ⟨11729427, by rfl⟩ : syracuseStep 31278473 = 23458855) B23458855
theorem B2746139 : Blo 1829616 2746139 := bstep (se 1 (by rfl) ⟨2059604, by rfl⟩ : syracuseStep 2746139 = 4119209) B4119209
theorem B11724713 : Blo 1829616 11724713 := bstep (se 2 (by rfl) ⟨4396767, by rfl⟩ : syracuseStep 11724713 = 8793535) B8793535
theorem B9267209 : Blo 1829616 9267209 := bstep (se 2 (by rfl) ⟨3475203, by rfl⟩ : syracuseStep 9267209 = 6950407) B6950407
theorem B3090487 : Blo 1829616 3090487 := bstep (se 1 (by rfl) ⟨2317865, by rfl⟩ : syracuseStep 3090487 = 4635731) B4635731
theorem B2746607 : Blo 1829616 2746607 := bstep (se 1 (by rfl) ⟨2059955, by rfl⟩ : syracuseStep 2746607 = 4119911) B4119911
theorem B2746727 : Blo 1829616 2746727 := bstep (se 1 (by rfl) ⟨2060045, by rfl⟩ : syracuseStep 2746727 = 4120091) B4120091
theorem B6597055 : Blo 1829616 6597055 := bstep (se 1 (by rfl) ⟨4947791, by rfl⟩ : syracuseStep 6597055 = 9895583) B9895583
theorem B80210411 : Blo 1829616 80210411 := bstep (se 1 (by rfl) ⟨60157808, by rfl⟩ : syracuseStep 80210411 = 120315617) B120315617
theorem B2058943 : Blo 1829616 2058943 := bstep (se 1 (by rfl) ⟨1544207, by rfl⟩ : syracuseStep 2058943 = 3088415) B3088415
theorem B4631327 : Blo 1829616 4631327 := bstep (se 1 (by rfl) ⟨3473495, by rfl⟩ : syracuseStep 4631327 = 6946991) B6946991
theorem B1830055 : Blo 1829616 1830055 := bstep (se 1 (by rfl) ⟨1372541, by rfl⟩ : syracuseStep 1830055 = 2745083) B2745083
theorem B30093083 : Blo 1829616 30093083 := bstep (se 1 (by rfl) ⟨22569812, by rfl⟩ : syracuseStep 30093083 = 45139625) B45139625
theorem B1830983 : Blo 1829616 1830983 := bstep (se 1 (by rfl) ⟨1373237, by rfl⟩ : syracuseStep 1830983 = 2746475) B2746475
theorem B75173993 : Blo 1829616 75173993 := bstep (se 2 (by rfl) ⟨28190247, by rfl⟩ : syracuseStep 75173993 = 56380495) B56380495
theorem B6181001 : Blo 1829616 6181001 := bstep (se 2 (by rfl) ⟨2317875, by rfl⟩ : syracuseStep 6181001 = 4635751) B4635751
theorem B1831551 : Blo 1829616 1831551 := bstep (se 1 (by rfl) ⟨1373663, by rfl⟩ : syracuseStep 1831551 = 2747327) B2747327
theorem B1831579 : Blo 1829616 1831579 := bstep (se 1 (by rfl) ⟨1373684, by rfl⟩ : syracuseStep 1831579 = 2747369) B2747369
theorem B6181595 : Blo 1829616 6181595 := bstep (se 1 (by rfl) ⟨4636196, by rfl⟩ : syracuseStep 6181595 = 9272393) B9272393
theorem B12522455 : Blo 1829616 12522455 := bstep (se 1 (by rfl) ⟨9391841, by rfl⟩ : syracuseStep 12522455 = 18783683) B18783683
theorem B13202527 : Blo 1829616 13202527 := bstep (se 1 (by rfl) ⟨9901895, by rfl⟩ : syracuseStep 13202527 = 19803791) B19803791
theorem B17585531 : Blo 1829616 17585531 := bstep (se 1 (by rfl) ⟨13189148, by rfl⟩ : syracuseStep 17585531 = 26378297) B26378297
theorem B3709919 : Blo 1829616 3709919 := bstep (se 1 (by rfl) ⟨2782439, by rfl⟩ : syracuseStep 3709919 = 5564879) B5564879
theorem B13188203 : Blo 1829616 13188203 := bstep (se 1 (by rfl) ⟨9891152, by rfl⟩ : syracuseStep 13188203 = 19782305) B19782305
theorem B3710227 : Blo 1829616 3710227 := bstep (se 1 (by rfl) ⟨2782670, by rfl⟩ : syracuseStep 3710227 = 5565341) B5565341
theorem B2932127 : Blo 1829616 2932127 := bstep (se 1 (by rfl) ⟨2199095, by rfl⟩ : syracuseStep 2932127 = 4398191) B4398191
theorem B63430391 : Blo 1829616 63430391 := bstep (se 1 (by rfl) ⟨47572793, by rfl⟩ : syracuseStep 63430391 = 95145587) B95145587
theorem B4120649 : Blo 1829616 4120649 := bstep (se 2 (by rfl) ⟨1545243, by rfl⟩ : syracuseStep 4120649 = 3090487) B3090487
theorem B4120667 : Blo 1829616 4120667 := bstep (se 1 (by rfl) ⟨3090500, by rfl⟩ : syracuseStep 4120667 = 6181001) B6181001
theorem B4121063 : Blo 1829616 4121063 := bstep (se 1 (by rfl) ⟨3090797, by rfl⟩ : syracuseStep 4121063 = 6181595) B6181595
theorem B8348303 : Blo 1829616 8348303 := bstep (se 1 (by rfl) ⟨6261227, by rfl⟩ : syracuseStep 8348303 = 12522455) B12522455
theorem B11723687 : Blo 1829616 11723687 := bstep (se 1 (by rfl) ⟨8792765, by rfl⟩ : syracuseStep 11723687 = 17585531) B17585531
theorem B2745257 : Blo 1829616 2745257 := bstep (se 2 (by rfl) ⟨1029471, by rfl⟩ : syracuseStep 2745257 = 2058943) B2058943
theorem B7816475 : Blo 1829616 7816475 := bstep (se 1 (by rfl) ⟨5862356, by rfl⟩ : syracuseStep 7816475 = 11724713) B11724713
theorem B6178139 : Blo 1829616 6178139 := bstep (se 1 (by rfl) ⟨4633604, by rfl⟩ : syracuseStep 6178139 = 9267209) B9267209
theorem B3474809 : Blo 1829616 3474809 := bstep (se 2 (by rfl) ⟨1303053, by rfl⟩ : syracuseStep 3474809 = 2606107) B2606107
theorem B158369417 : Blo 1829616 158369417 := bstep (se 2 (by rfl) ⟨59388531, by rfl⟩ : syracuseStep 158369417 = 118777063) B118777063
theorem B8792135 : Blo 1829616 8792135 := bstep (se 1 (by rfl) ⟨6594101, by rfl⟩ : syracuseStep 8792135 = 13188203) B13188203
theorem B2747135 : Blo 1829616 2747135 := bstep (se 1 (by rfl) ⟨2060351, by rfl⟩ : syracuseStep 2747135 = 4120703) B4120703
theorem B1830127 : Blo 1829616 1830127 := bstep (se 1 (by rfl) ⟨1372595, by rfl⟩ : syracuseStep 1830127 = 2745191) B2745191
theorem B20852315 : Blo 1829616 20852315 := bstep (se 1 (by rfl) ⟨15639236, by rfl⟩ : syracuseStep 20852315 = 31278473) B31278473
theorem B1830759 : Blo 1829616 1830759 := bstep (se 1 (by rfl) ⟨1373069, by rfl⟩ : syracuseStep 1830759 = 2746139) B2746139
theorem B1831071 : Blo 1829616 1831071 := bstep (se 1 (by rfl) ⟨1373303, by rfl⟩ : syracuseStep 1831071 = 2746607) B2746607
theorem B1831151 : Blo 1829616 1831151 := bstep (se 1 (by rfl) ⟨1373363, by rfl⟩ : syracuseStep 1831151 = 2746727) B2746727
theorem B53473607 : Blo 1829616 53473607 := bstep (se 1 (by rfl) ⟨40105205, by rfl⟩ : syracuseStep 53473607 = 80210411) B80210411
theorem B1954751 : Blo 1829616 1954751 := bstep (se 1 (by rfl) ⟨1466063, by rfl⟩ : syracuseStep 1954751 = 2932127) B2932127
theorem B9893117 : Blo 1829616 9893117 := bstep (se 3 (by rfl) ⟨1854959, by rfl⟩ : syracuseStep 9893117 = 3709919) B3709919
theorem B50115995 : Blo 1829616 50115995 := bstep (se 1 (by rfl) ⟨37586996, by rfl⟩ : syracuseStep 50115995 = 75173993) B75173993
theorem B9656111 : Blo 1829616 9656111 := bstep (se 1 (by rfl) ⟨7242083, by rfl⟩ : syracuseStep 9656111 = 14484167) B14484167
theorem B8796073 : Blo 1829616 8796073 := bstep (se 2 (by rfl) ⟨3298527, by rfl⟩ : syracuseStep 8796073 = 6597055) B6597055
theorem B17603369 : Blo 1829616 17603369 := bstep (se 2 (by rfl) ⟨6601263, by rfl⟩ : syracuseStep 17603369 = 13202527) B13202527
theorem B4946969 : Blo 1829616 4946969 := bstep (se 2 (by rfl) ⟨1855113, by rfl⟩ : syracuseStep 4946969 = 3710227) B3710227
theorem B3087551 : Blo 1829616 3087551 := bstep (se 1 (by rfl) ⟨2315663, by rfl⟩ : syracuseStep 3087551 = 4631327) B4631327
theorem B42286927 : Blo 1829616 42286927 := bstep (se 1 (by rfl) ⟨31715195, by rfl⟩ : syracuseStep 42286927 = 63430391) B63430391
theorem B20062055 : Blo 1829616 20062055 := bstep (se 1 (by rfl) ⟨15046541, by rfl⟩ : syracuseStep 20062055 = 30093083) B30093083
theorem B7815791 : Blo 1829616 7815791 := bstep (se 1 (by rfl) ⟨5861843, by rfl⟩ : syracuseStep 7815791 = 11723687) B11723687
theorem B5210983 : Blo 1829616 5210983 := bstep (se 1 (by rfl) ⟨3908237, by rfl⟩ : syracuseStep 5210983 = 7816475) B7816475
theorem B105579611 : Blo 1829616 105579611 := bstep (se 1 (by rfl) ⟨79184708, by rfl⟩ : syracuseStep 105579611 = 158369417) B158369417
theorem B2058367 : Blo 1829616 2058367 := bstep (se 1 (by rfl) ⟨1543775, by rfl⟩ : syracuseStep 2058367 = 3087551) B3087551
theorem B5212669 : Blo 1829616 5212669 := bstep (se 3 (by rfl) ⟨977375, by rfl⟩ : syracuseStep 5212669 = 1954751) B1954751
theorem B2747099 : Blo 1829616 2747099 := bstep (se 1 (by rfl) ⟨2060324, by rfl⟩ : syracuseStep 2747099 = 4120649) B4120649
theorem B2747111 : Blo 1829616 2747111 := bstep (se 1 (by rfl) ⟨2060333, by rfl⟩ : syracuseStep 2747111 = 4120667) B4120667
theorem B2747375 : Blo 1829616 2747375 := bstep (se 1 (by rfl) ⟨2060531, by rfl⟩ : syracuseStep 2747375 = 4121063) B4121063
theorem B1830171 : Blo 1829616 1830171 := bstep (se 1 (by rfl) ⟨1372628, by rfl⟩ : syracuseStep 1830171 = 2745257) B2745257
theorem B26381645 : Blo 1829616 26381645 := bstep (se 3 (by rfl) ⟨4946558, by rfl⟩ : syracuseStep 26381645 = 9893117) B9893117
theorem B33410663 : Blo 1829616 33410663 := bstep (se 1 (by rfl) ⟨25057997, by rfl⟩ : syracuseStep 33410663 = 50115995) B50115995
theorem B5861423 : Blo 1829616 5861423 := bstep (se 1 (by rfl) ⟨4396067, by rfl⟩ : syracuseStep 5861423 = 8792135) B8792135
theorem B22262141 : Blo 1829616 22262141 := bstep (se 3 (by rfl) ⟨4174151, by rfl⟩ : syracuseStep 22262141 = 8348303) B8348303
theorem B1831423 : Blo 1829616 1831423 := bstep (se 1 (by rfl) ⟨1373567, by rfl⟩ : syracuseStep 1831423 = 2747135) B2747135
theorem B11735579 : Blo 1829616 11735579 := bstep (se 1 (by rfl) ⟨8801684, by rfl⟩ : syracuseStep 11735579 = 17603369) B17603369
theorem B3297979 : Blo 1829616 3297979 := bstep (se 1 (by rfl) ⟨2473484, by rfl⟩ : syracuseStep 3297979 = 4946969) B4946969
theorem B56382569 : Blo 1829616 56382569 := bstep (se 2 (by rfl) ⟨21143463, by rfl⟩ : syracuseStep 56382569 = 42286927) B42286927
theorem B11728097 : Blo 1829616 11728097 := bstep (se 2 (by rfl) ⟨4398036, by rfl⟩ : syracuseStep 11728097 = 8796073) B8796073
theorem B13374703 : Blo 1829616 13374703 := bstep (se 1 (by rfl) ⟨10031027, by rfl⟩ : syracuseStep 13374703 = 20062055) B20062055
theorem B35649071 : Blo 1829616 35649071 := bstep (se 1 (by rfl) ⟨26736803, by rfl⟩ : syracuseStep 35649071 = 53473607) B53473607
theorem B4118759 : Blo 1829616 4118759 := bstep (se 1 (by rfl) ⟨3089069, by rfl⟩ : syracuseStep 4118759 = 6178139) B6178139
theorem B2316539 : Blo 1829616 2316539 := bstep (se 1 (by rfl) ⟨1737404, by rfl⟩ : syracuseStep 2316539 = 3474809) B3474809
theorem B6437407 : Blo 1829616 6437407 := bstep (se 1 (by rfl) ⟨4828055, by rfl⟩ : syracuseStep 6437407 = 9656111) B9656111
theorem B13901543 : Blo 1829616 13901543 := bstep (se 1 (by rfl) ⟨10426157, by rfl⟩ : syracuseStep 13901543 = 20852315) B20852315
theorem B3907615 : Blo 1829616 3907615 := bstep (se 1 (by rfl) ⟨2930711, by rfl⟩ : syracuseStep 3907615 = 5861423) B5861423
theorem B2744489 : Blo 1829616 2744489 := bstep (se 2 (by rfl) ⟨1029183, by rfl⟩ : syracuseStep 2744489 = 2058367) B2058367
theorem B7823719 : Blo 1829616 7823719 := bstep (se 1 (by rfl) ⟨5867789, by rfl⟩ : syracuseStep 7823719 = 11735579) B11735579
theorem B6177437 : Blo 1829616 6177437 := bstep (se 3 (by rfl) ⟨1158269, by rfl⟩ : syracuseStep 6177437 = 2316539) B2316539
theorem B70386407 : Blo 1829616 70386407 := bstep (se 1 (by rfl) ⟨52789805, by rfl⟩ : syracuseStep 70386407 = 105579611) B105579611
theorem B17589221 : Blo 1829616 17589221 := bstep (se 4 (by rfl) ⟨1648989, by rfl⟩ : syracuseStep 17589221 = 3297979) B3297979
theorem B23766047 : Blo 1829616 23766047 := bstep (se 1 (by rfl) ⟨17824535, by rfl⟩ : syracuseStep 23766047 = 35649071) B35649071
theorem B6947977 : Blo 1829616 6947977 := bstep (se 2 (by rfl) ⟨2605491, by rfl⟩ : syracuseStep 6947977 = 5210983) B5210983
theorem B2745839 : Blo 1829616 2745839 := bstep (se 1 (by rfl) ⟨2059379, by rfl⟩ : syracuseStep 2745839 = 4118759) B4118759
theorem B20842109 : Blo 1829616 20842109 := bstep (se 3 (by rfl) ⟨3907895, by rfl⟩ : syracuseStep 20842109 = 7815791) B7815791
theorem B9267695 : Blo 1829616 9267695 := bstep (se 1 (by rfl) ⟨6950771, by rfl⟩ : syracuseStep 9267695 = 13901543) B13901543
theorem B6950225 : Blo 1829616 6950225 := bstep (se 2 (by rfl) ⟨2606334, by rfl⟩ : syracuseStep 6950225 = 5212669) B5212669
theorem B37588379 : Blo 1829616 37588379 := bstep (se 1 (by rfl) ⟨28191284, by rfl⟩ : syracuseStep 37588379 = 56382569) B56382569
theorem B7818731 : Blo 1829616 7818731 := bstep (se 1 (by rfl) ⟨5864048, by rfl⟩ : syracuseStep 7818731 = 11728097) B11728097
theorem B71331749 : Blo 1829616 71331749 := bstep (se 4 (by rfl) ⟨6687351, by rfl⟩ : syracuseStep 71331749 = 13374703) B13374703
theorem B1831399 : Blo 1829616 1831399 := bstep (se 1 (by rfl) ⟨1373549, by rfl⟩ : syracuseStep 1831399 = 2747099) B2747099
theorem B1831407 : Blo 1829616 1831407 := bstep (se 1 (by rfl) ⟨1373555, by rfl⟩ : syracuseStep 1831407 = 2747111) B2747111
theorem B1831583 : Blo 1829616 1831583 := bstep (se 1 (by rfl) ⟨1373687, by rfl⟩ : syracuseStep 1831583 = 2747375) B2747375
theorem B14841427 : Blo 1829616 14841427 := bstep (se 1 (by rfl) ⟨11131070, by rfl⟩ : syracuseStep 14841427 = 22262141) B22262141
theorem B8583209 : Blo 1829616 8583209 := bstep (se 2 (by rfl) ⟨3218703, by rfl⟩ : syracuseStep 8583209 = 6437407) B6437407
theorem B17587763 : Blo 1829616 17587763 := bstep (se 1 (by rfl) ⟨13190822, by rfl⟩ : syracuseStep 17587763 = 26381645) B26381645
theorem B22273775 : Blo 1829616 22273775 := bstep (se 1 (by rfl) ⟨16705331, by rfl⟩ : syracuseStep 22273775 = 33410663) B33410663
theorem B5210153 : Blo 1829616 5210153 := bstep (se 2 (by rfl) ⟨1953807, by rfl⟩ : syracuseStep 5210153 = 3907615) B3907615
theorem B46924271 : Blo 1829616 46924271 := bstep (se 1 (by rfl) ⟨35193203, by rfl⟩ : syracuseStep 46924271 = 70386407) B70386407
theorem B15844031 : Blo 1829616 15844031 := bstep (se 1 (by rfl) ⟨11883023, by rfl⟩ : syracuseStep 15844031 = 23766047) B23766047
theorem B13894739 : Blo 1829616 13894739 := bstep (se 1 (by rfl) ⟨10421054, by rfl⟩ : syracuseStep 13894739 = 20842109) B20842109
theorem B6178463 : Blo 1829616 6178463 := bstep (se 1 (by rfl) ⟨4633847, by rfl⟩ : syracuseStep 6178463 = 9267695) B9267695
theorem B5212487 : Blo 1829616 5212487 := bstep (se 1 (by rfl) ⟨3909365, by rfl⟩ : syracuseStep 5212487 = 7818731) B7818731
theorem B11725175 : Blo 1829616 11725175 := bstep (se 1 (by rfl) ⟨8793881, by rfl⟩ : syracuseStep 11725175 = 17587763) B17587763
theorem B1829659 : Blo 1829616 1829659 := bstep (se 1 (by rfl) ⟨1372244, by rfl⟩ : syracuseStep 1829659 = 2744489) B2744489
theorem B10431625 : Blo 1829616 10431625 := bstep (se 2 (by rfl) ⟨3911859, by rfl⟩ : syracuseStep 10431625 = 7823719) B7823719
theorem B11726147 : Blo 1829616 11726147 := bstep (se 1 (by rfl) ⟨8794610, by rfl⟩ : syracuseStep 11726147 = 17589221) B17589221
theorem B1830559 : Blo 1829616 1830559 := bstep (se 1 (by rfl) ⟨1372919, by rfl⟩ : syracuseStep 1830559 = 2745839) B2745839
theorem B5722139 : Blo 1829616 5722139 := bstep (se 1 (by rfl) ⟨4291604, by rfl⟩ : syracuseStep 5722139 = 8583209) B8583209
theorem B19788569 : Blo 1829616 19788569 := bstep (se 2 (by rfl) ⟨7420713, by rfl⟩ : syracuseStep 19788569 = 14841427) B14841427
theorem B4633483 : Blo 1829616 4633483 := bstep (se 1 (by rfl) ⟨3475112, by rfl⟩ : syracuseStep 4633483 = 6950225) B6950225
theorem B14849183 : Blo 1829616 14849183 := bstep (se 1 (by rfl) ⟨11136887, by rfl⟩ : syracuseStep 14849183 = 22273775) B22273775
theorem B4118291 : Blo 1829616 4118291 := bstep (se 1 (by rfl) ⟨3088718, by rfl⟩ : syracuseStep 4118291 = 6177437) B6177437
theorem B100235677 : Blo 1829616 100235677 := bstep (se 3 (by rfl) ⟨18794189, by rfl⟩ : syracuseStep 100235677 = 37588379) B37588379
theorem B9263969 : Blo 1829616 9263969 := bstep (se 2 (by rfl) ⟨3473988, by rfl⟩ : syracuseStep 9263969 = 6947977) B6947977
theorem B47554499 : Blo 1829616 47554499 := bstep (se 1 (by rfl) ⟨35665874, by rfl⟩ : syracuseStep 47554499 = 71331749) B71331749
theorem B3473435 : Blo 1829616 3473435 := bstep (se 1 (by rfl) ⟨2605076, by rfl⟩ : syracuseStep 3473435 = 5210153) B5210153
theorem B31269725 : Blo 1829616 31269725 := bstep (se 3 (by rfl) ⟨5863073, by rfl⟩ : syracuseStep 31269725 = 11726147) B11726147
theorem B2745527 : Blo 1829616 2745527 := bstep (se 1 (by rfl) ⟨2059145, by rfl⟩ : syracuseStep 2745527 = 4118291) B4118291
theorem B6177977 : Blo 1829616 6177977 := bstep (se 2 (by rfl) ⟨2316741, by rfl⟩ : syracuseStep 6177977 = 4633483) B4633483
theorem B3474991 : Blo 1829616 3474991 := bstep (se 1 (by rfl) ⟨2606243, by rfl⟩ : syracuseStep 3474991 = 5212487) B5212487
theorem B7816783 : Blo 1829616 7816783 := bstep (se 1 (by rfl) ⟨5862587, by rfl⟩ : syracuseStep 7816783 = 11725175) B11725175
theorem B10562687 : Blo 1829616 10562687 := bstep (se 1 (by rfl) ⟨7922015, by rfl⟩ : syracuseStep 10562687 = 15844031) B15844031
theorem B13192379 : Blo 1829616 13192379 := bstep (se 1 (by rfl) ⟨9894284, by rfl⟩ : syracuseStep 13192379 = 19788569) B19788569
theorem B133647569 : Blo 1829616 133647569 := bstep (se 2 (by rfl) ⟨50117838, by rfl⟩ : syracuseStep 133647569 = 100235677) B100235677
theorem B3814759 : Blo 1829616 3814759 := bstep (se 1 (by rfl) ⟨2861069, by rfl⟩ : syracuseStep 3814759 = 5722139) B5722139
theorem B31282847 : Blo 1829616 31282847 := bstep (se 1 (by rfl) ⟨23462135, by rfl⟩ : syracuseStep 31282847 = 46924271) B46924271
theorem B39597821 : Blo 1829616 39597821 := bstep (se 3 (by rfl) ⟨7424591, by rfl⟩ : syracuseStep 39597821 = 14849183) B14849183
theorem B9263159 : Blo 1829616 9263159 := bstep (se 1 (by rfl) ⟨6947369, by rfl⟩ : syracuseStep 9263159 = 13894739) B13894739
theorem B4118975 : Blo 1829616 4118975 := bstep (se 1 (by rfl) ⟨3089231, by rfl⟩ : syracuseStep 4118975 = 6178463) B6178463
theorem B13908833 : Blo 1829616 13908833 := bstep (se 2 (by rfl) ⟨5215812, by rfl⟩ : syracuseStep 13908833 = 10431625) B10431625
theorem B6175979 : Blo 1829616 6175979 := bstep (se 1 (by rfl) ⟨4631984, by rfl⟩ : syracuseStep 6175979 = 9263969) B9263969
theorem B31702999 : Blo 1829616 31702999 := bstep (se 1 (by rfl) ⟨23777249, by rfl⟩ : syracuseStep 31702999 = 47554499) B47554499
theorem B2745983 : Blo 1829616 2745983 := bstep (se 1 (by rfl) ⟨2059487, by rfl⟩ : syracuseStep 2745983 = 4118975) B4118975
theorem B10422377 : Blo 1829616 10422377 := bstep (se 2 (by rfl) ⟨3908391, by rfl⟩ : syracuseStep 10422377 = 7816783) B7816783
theorem B89098379 : Blo 1829616 89098379 := bstep (se 1 (by rfl) ⟨66823784, by rfl⟩ : syracuseStep 89098379 = 133647569) B133647569
theorem B1830351 : Blo 1829616 1830351 := bstep (se 1 (by rfl) ⟨1372763, by rfl⟩ : syracuseStep 1830351 = 2745527) B2745527
theorem B26398547 : Blo 1829616 26398547 := bstep (se 1 (by rfl) ⟨19798910, by rfl⟩ : syracuseStep 26398547 = 39597821) B39597821
theorem B20345381 : Blo 1829616 20345381 := bstep (se 4 (by rfl) ⟨1907379, by rfl⟩ : syracuseStep 20345381 = 3814759) B3814759
theorem B4633321 : Blo 1829616 4633321 := bstep (se 2 (by rfl) ⟨1737495, by rfl⟩ : syracuseStep 4633321 = 3474991) B3474991
theorem B7041791 : Blo 1829616 7041791 := bstep (se 1 (by rfl) ⟨5281343, by rfl⟩ : syracuseStep 7041791 = 10562687) B10562687
theorem B8794919 : Blo 1829616 8794919 := bstep (se 1 (by rfl) ⟨6596189, by rfl⟩ : syracuseStep 8794919 = 13192379) B13192379
theorem B4117319 : Blo 1829616 4117319 := bstep (se 1 (by rfl) ⟨3087989, by rfl⟩ : syracuseStep 4117319 = 6175979) B6175979
theorem B2315623 : Blo 1829616 2315623 := bstep (se 1 (by rfl) ⟨1736717, by rfl⟩ : syracuseStep 2315623 = 3473435) B3473435
theorem B20846483 : Blo 1829616 20846483 := bstep (se 1 (by rfl) ⟨15634862, by rfl⟩ : syracuseStep 20846483 = 31269725) B31269725
theorem B4118651 : Blo 1829616 4118651 := bstep (se 1 (by rfl) ⟨3088988, by rfl⟩ : syracuseStep 4118651 = 6177977) B6177977
theorem B20855231 : Blo 1829616 20855231 := bstep (se 1 (by rfl) ⟨15641423, by rfl⟩ : syracuseStep 20855231 = 31282847) B31282847
theorem B6175439 : Blo 1829616 6175439 := bstep (se 1 (by rfl) ⟨4631579, by rfl⟩ : syracuseStep 6175439 = 9263159) B9263159
theorem B9272555 : Blo 1829616 9272555 := bstep (se 1 (by rfl) ⟨6954416, by rfl⟩ : syracuseStep 9272555 = 13908833) B13908833
theorem B42270665 : Blo 1829616 42270665 := bstep (se 2 (by rfl) ⟨15851499, by rfl⟩ : syracuseStep 42270665 = 31702999) B31702999
theorem B4694527 : Blo 1829616 4694527 := bstep (se 1 (by rfl) ⟨3520895, by rfl⟩ : syracuseStep 4694527 = 7041791) B7041791
theorem B2744879 : Blo 1829616 2744879 := bstep (se 1 (by rfl) ⟨2058659, by rfl⟩ : syracuseStep 2744879 = 4117319) B4117319
theorem B6177761 : Blo 1829616 6177761 := bstep (se 2 (by rfl) ⟨2316660, by rfl⟩ : syracuseStep 6177761 = 4633321) B4633321
theorem B6948251 : Blo 1829616 6948251 := bstep (se 1 (by rfl) ⟨5211188, by rfl⟩ : syracuseStep 6948251 = 10422377) B10422377
theorem B2745767 : Blo 1829616 2745767 := bstep (se 1 (by rfl) ⟨2059325, by rfl⟩ : syracuseStep 2745767 = 4118651) B4118651
theorem B13903487 : Blo 1829616 13903487 := bstep (se 1 (by rfl) ⟨10427615, by rfl⟩ : syracuseStep 13903487 = 20855231) B20855231
theorem B17599031 : Blo 1829616 17599031 := bstep (se 1 (by rfl) ⟨13199273, by rfl⟩ : syracuseStep 17599031 = 26398547) B26398547
theorem B1830655 : Blo 1829616 1830655 := bstep (se 1 (by rfl) ⟨1372991, by rfl⟩ : syracuseStep 1830655 = 2745983) B2745983
theorem B13897655 : Blo 1829616 13897655 := bstep (se 1 (by rfl) ⟨10423241, by rfl⟩ : syracuseStep 13897655 = 20846483) B20846483
theorem B4116959 : Blo 1829616 4116959 := bstep (se 1 (by rfl) ⟨3087719, by rfl⟩ : syracuseStep 4116959 = 6175439) B6175439
theorem B6181703 : Blo 1829616 6181703 := bstep (se 1 (by rfl) ⟨4636277, by rfl⟩ : syracuseStep 6181703 = 9272555) B9272555
theorem B13563587 : Blo 1829616 13563587 := bstep (se 1 (by rfl) ⟨10172690, by rfl⟩ : syracuseStep 13563587 = 20345381) B20345381
theorem B5863279 : Blo 1829616 5863279 := bstep (se 1 (by rfl) ⟨4397459, by rfl⟩ : syracuseStep 5863279 = 8794919) B8794919
theorem B59398919 : Blo 1829616 59398919 := bstep (se 1 (by rfl) ⟨44549189, by rfl⟩ : syracuseStep 59398919 = 89098379) B89098379
theorem B3087497 : Blo 1829616 3087497 := bstep (se 2 (by rfl) ⟨1157811, by rfl⟩ : syracuseStep 3087497 = 2315623) B2315623
theorem B450887093 : Blo 1829616 450887093 := bstep (se 5 (by rfl) ⟨21135332, by rfl⟩ : syracuseStep 450887093 = 42270665) B42270665
theorem B2744639 : Blo 1829616 2744639 := bstep (se 1 (by rfl) ⟨2058479, by rfl⟩ : syracuseStep 2744639 = 4116959) B4116959
theorem B4121135 : Blo 1829616 4121135 := bstep (se 1 (by rfl) ⟨3090851, by rfl⟩ : syracuseStep 4121135 = 6181703) B6181703
theorem B6259369 : Blo 1829616 6259369 := bstep (se 2 (by rfl) ⟨2347263, by rfl⟩ : syracuseStep 6259369 = 4694527) B4694527
theorem B11732687 : Blo 1829616 11732687 := bstep (se 1 (by rfl) ⟨8799515, by rfl⟩ : syracuseStep 11732687 = 17599031) B17599031
theorem B2058331 : Blo 1829616 2058331 := bstep (se 1 (by rfl) ⟨1543748, by rfl⟩ : syracuseStep 2058331 = 3087497) B3087497
theorem B300591395 : Blo 1829616 300591395 := bstep (se 1 (by rfl) ⟨225443546, by rfl⟩ : syracuseStep 300591395 = 450887093) B450887093
theorem B7817705 : Blo 1829616 7817705 := bstep (se 2 (by rfl) ⟨2931639, by rfl⟩ : syracuseStep 7817705 = 5863279) B5863279
theorem B1829919 : Blo 1829616 1829919 := bstep (se 1 (by rfl) ⟨1372439, by rfl⟩ : syracuseStep 1829919 = 2744879) B2744879
theorem B4632167 : Blo 1829616 4632167 := bstep (se 1 (by rfl) ⟨3474125, by rfl⟩ : syracuseStep 4632167 = 6948251) B6948251
theorem B1830511 : Blo 1829616 1830511 := bstep (se 1 (by rfl) ⟨1372883, by rfl⟩ : syracuseStep 1830511 = 2745767) B2745767
theorem B9268991 : Blo 1829616 9268991 := bstep (se 1 (by rfl) ⟨6951743, by rfl⟩ : syracuseStep 9268991 = 13903487) B13903487
theorem B4118507 : Blo 1829616 4118507 := bstep (se 1 (by rfl) ⟨3088880, by rfl⟩ : syracuseStep 4118507 = 6177761) B6177761
theorem B9042391 : Blo 1829616 9042391 := bstep (se 1 (by rfl) ⟨6781793, by rfl⟩ : syracuseStep 9042391 = 13563587) B13563587
theorem B39599279 : Blo 1829616 39599279 := bstep (se 1 (by rfl) ⟨29699459, by rfl⟩ : syracuseStep 39599279 = 59398919) B59398919
theorem B9265103 : Blo 1829616 9265103 := bstep (se 1 (by rfl) ⟨6948827, by rfl⟩ : syracuseStep 9265103 = 13897655) B13897655
theorem B2744441 : Blo 1829616 2744441 := bstep (se 2 (by rfl) ⟨1029165, by rfl⟩ : syracuseStep 2744441 = 2058331) B2058331
theorem B2745671 : Blo 1829616 2745671 := bstep (se 1 (by rfl) ⟨2059253, by rfl⟩ : syracuseStep 2745671 = 4118507) B4118507
theorem B200394263 : Blo 1829616 200394263 := bstep (se 1 (by rfl) ⟨150295697, by rfl⟩ : syracuseStep 200394263 = 300591395) B300591395
theorem B5211803 : Blo 1829616 5211803 := bstep (se 1 (by rfl) ⟨3908852, by rfl⟩ : syracuseStep 5211803 = 7817705) B7817705
theorem B6179327 : Blo 1829616 6179327 := bstep (se 1 (by rfl) ⟨4634495, by rfl⟩ : syracuseStep 6179327 = 9268991) B9268991
theorem B1829759 : Blo 1829616 1829759 := bstep (se 1 (by rfl) ⟨1372319, by rfl⟩ : syracuseStep 1829759 = 2744639) B2744639
theorem B2747423 : Blo 1829616 2747423 := bstep (se 1 (by rfl) ⟨2060567, by rfl⟩ : syracuseStep 2747423 = 4121135) B4121135
theorem B26399519 : Blo 1829616 26399519 := bstep (se 1 (by rfl) ⟨19799639, by rfl⟩ : syracuseStep 26399519 = 39599279) B39599279
theorem B12056521 : Blo 1829616 12056521 := bstep (se 2 (by rfl) ⟨4521195, by rfl⟩ : syracuseStep 12056521 = 9042391) B9042391
theorem B8345825 : Blo 1829616 8345825 := bstep (se 2 (by rfl) ⟨3129684, by rfl⟩ : syracuseStep 8345825 = 6259369) B6259369
theorem B7821791 : Blo 1829616 7821791 := bstep (se 1 (by rfl) ⟨5866343, by rfl⟩ : syracuseStep 7821791 = 11732687) B11732687
theorem B3088111 : Blo 1829616 3088111 := bstep (se 1 (by rfl) ⟨2316083, by rfl⟩ : syracuseStep 3088111 = 4632167) B4632167
theorem B6176735 : Blo 1829616 6176735 := bstep (se 1 (by rfl) ⟨4632551, by rfl⟩ : syracuseStep 6176735 = 9265103) B9265103
theorem B133596175 : Blo 1829616 133596175 := bstep (se 1 (by rfl) ⟨100197131, by rfl⟩ : syracuseStep 133596175 = 200394263) B200394263
theorem B5563883 : Blo 1829616 5563883 := bstep (se 1 (by rfl) ⟨4172912, by rfl⟩ : syracuseStep 5563883 = 8345825) B8345825
theorem B16075361 : Blo 1829616 16075361 := bstep (se 2 (by rfl) ⟨6028260, by rfl⟩ : syracuseStep 16075361 = 12056521) B12056521
theorem B1829627 : Blo 1829616 1829627 := bstep (se 1 (by rfl) ⟨1372220, by rfl⟩ : syracuseStep 1829627 = 2744441) B2744441
theorem B17599679 : Blo 1829616 17599679 := bstep (se 1 (by rfl) ⟨13199759, by rfl⟩ : syracuseStep 17599679 = 26399519) B26399519
theorem B1830447 : Blo 1829616 1830447 := bstep (se 1 (by rfl) ⟨1372835, by rfl⟩ : syracuseStep 1830447 = 2745671) B2745671
theorem B5214527 : Blo 1829616 5214527 := bstep (se 1 (by rfl) ⟨3910895, by rfl⟩ : syracuseStep 5214527 = 7821791) B7821791
theorem B13898141 : Blo 1829616 13898141 := bstep (se 3 (by rfl) ⟨2605901, by rfl⟩ : syracuseStep 13898141 = 5211803) B5211803
theorem B1831615 : Blo 1829616 1831615 := bstep (se 1 (by rfl) ⟨1373711, by rfl⟩ : syracuseStep 1831615 = 2747423) B2747423
theorem B4117481 : Blo 1829616 4117481 := bstep (se 2 (by rfl) ⟨1544055, by rfl⟩ : syracuseStep 4117481 = 3088111) B3088111
theorem B4117823 : Blo 1829616 4117823 := bstep (se 1 (by rfl) ⟨3088367, by rfl⟩ : syracuseStep 4117823 = 6176735) B6176735
theorem B4119551 : Blo 1829616 4119551 := bstep (se 1 (by rfl) ⟨3089663, by rfl⟩ : syracuseStep 4119551 = 6179327) B6179327
theorem B9265427 : Blo 1829616 9265427 := bstep (se 1 (by rfl) ⟨6949070, by rfl⟩ : syracuseStep 9265427 = 13898141) B13898141
theorem B2744987 : Blo 1829616 2744987 := bstep (se 1 (by rfl) ⟨2058740, by rfl⟩ : syracuseStep 2744987 = 4117481) B4117481
theorem B2745215 : Blo 1829616 2745215 := bstep (se 1 (by rfl) ⟨2058911, by rfl⟩ : syracuseStep 2745215 = 4117823) B4117823
theorem B178128233 : Blo 1829616 178128233 := bstep (se 2 (by rfl) ⟨66798087, by rfl⟩ : syracuseStep 178128233 = 133596175) B133596175
theorem B10716907 : Blo 1829616 10716907 := bstep (se 1 (by rfl) ⟨8037680, by rfl⟩ : syracuseStep 10716907 = 16075361) B16075361
theorem B2746367 : Blo 1829616 2746367 := bstep (se 1 (by rfl) ⟨2059775, by rfl⟩ : syracuseStep 2746367 = 4119551) B4119551
theorem B11733119 : Blo 1829616 11733119 := bstep (se 1 (by rfl) ⟨8799839, by rfl⟩ : syracuseStep 11733119 = 17599679) B17599679
theorem B3476351 : Blo 1829616 3476351 := bstep (se 1 (by rfl) ⟨2607263, by rfl⟩ : syracuseStep 3476351 = 5214527) B5214527
theorem B3709255 : Blo 1829616 3709255 := bstep (se 1 (by rfl) ⟨2781941, by rfl⟩ : syracuseStep 3709255 = 5563883) B5563883
theorem B6176951 : Blo 1829616 6176951 := bstep (se 1 (by rfl) ⟨4632713, by rfl⟩ : syracuseStep 6176951 = 9265427) B9265427
theorem B118752155 : Blo 1829616 118752155 := bstep (se 1 (by rfl) ⟨89064116, by rfl⟩ : syracuseStep 118752155 = 178128233) B178128233
theorem B14289209 : Blo 1829616 14289209 := bstep (se 2 (by rfl) ⟨5358453, by rfl⟩ : syracuseStep 14289209 = 10716907) B10716907
theorem B1829991 : Blo 1829616 1829991 := bstep (se 1 (by rfl) ⟨1372493, by rfl⟩ : syracuseStep 1829991 = 2744987) B2744987
theorem B1830143 : Blo 1829616 1830143 := bstep (se 1 (by rfl) ⟨1372607, by rfl⟩ : syracuseStep 1830143 = 2745215) B2745215
theorem B1830911 : Blo 1829616 1830911 := bstep (se 1 (by rfl) ⟨1373183, by rfl⟩ : syracuseStep 1830911 = 2746367) B2746367
theorem B4945673 : Blo 1829616 4945673 := bstep (se 2 (by rfl) ⟨1854627, by rfl⟩ : syracuseStep 4945673 = 3709255) B3709255
theorem B7822079 : Blo 1829616 7822079 := bstep (se 1 (by rfl) ⟨5866559, by rfl⟩ : syracuseStep 7822079 = 11733119) B11733119
theorem B2317567 : Blo 1829616 2317567 := bstep (se 1 (by rfl) ⟨1738175, by rfl⟩ : syracuseStep 2317567 = 3476351) B3476351
theorem B79168103 : Blo 1829616 79168103 := bstep (se 1 (by rfl) ⟨59376077, by rfl⟩ : syracuseStep 79168103 = 118752155) B118752155
theorem B3090089 : Blo 1829616 3090089 := bstep (se 2 (by rfl) ⟨1158783, by rfl⟩ : syracuseStep 3090089 = 2317567) B2317567
theorem B3297115 : Blo 1829616 3297115 := bstep (se 1 (by rfl) ⟨2472836, by rfl⟩ : syracuseStep 3297115 = 4945673) B4945673
theorem B5214719 : Blo 1829616 5214719 := bstep (se 1 (by rfl) ⟨3911039, by rfl⟩ : syracuseStep 5214719 = 7822079) B7822079
theorem B4117967 : Blo 1829616 4117967 := bstep (se 1 (by rfl) ⟨3088475, by rfl⟩ : syracuseStep 4117967 = 6176951) B6176951
theorem B9526139 : Blo 1829616 9526139 := bstep (se 1 (by rfl) ⟨7144604, by rfl⟩ : syracuseStep 9526139 = 14289209) B14289209
theorem B2745311 : Blo 1829616 2745311 := bstep (se 1 (by rfl) ⟨2058983, by rfl⟩ : syracuseStep 2745311 = 4117967) B4117967
theorem B6350759 : Blo 1829616 6350759 := bstep (se 1 (by rfl) ⟨4763069, by rfl⟩ : syracuseStep 6350759 = 9526139) B9526139
theorem B2060059 : Blo 1829616 2060059 := bstep (se 1 (by rfl) ⟨1545044, by rfl⟩ : syracuseStep 2060059 = 3090089) B3090089
theorem B13905917 : Blo 1829616 13905917 := bstep (se 3 (by rfl) ⟨2607359, by rfl⟩ : syracuseStep 13905917 = 5214719) B5214719
theorem B4396153 : Blo 1829616 4396153 := bstep (se 2 (by rfl) ⟨1648557, by rfl⟩ : syracuseStep 4396153 = 3297115) B3297115
theorem B52778735 : Blo 1829616 52778735 := bstep (se 1 (by rfl) ⟨39584051, by rfl⟩ : syracuseStep 52778735 = 79168103) B79168103
theorem B35185823 : Blo 1829616 35185823 := bstep (se 1 (by rfl) ⟨26389367, by rfl⟩ : syracuseStep 35185823 = 52778735) B52778735
theorem B67741429 : Blo 1829616 67741429 := bstep (se 5 (by rfl) ⟨3175379, by rfl⟩ : syracuseStep 67741429 = 6350759) B6350759
theorem B2746745 : Blo 1829616 2746745 := bstep (se 2 (by rfl) ⟨1030029, by rfl⟩ : syracuseStep 2746745 = 2060059) B2060059
theorem B1830207 : Blo 1829616 1830207 := bstep (se 1 (by rfl) ⟨1372655, by rfl⟩ : syracuseStep 1830207 = 2745311) B2745311
theorem B5861537 : Blo 1829616 5861537 := bstep (se 2 (by rfl) ⟨2198076, by rfl⟩ : syracuseStep 5861537 = 4396153) B4396153
theorem B9270611 : Blo 1829616 9270611 := bstep (se 1 (by rfl) ⟨6952958, by rfl⟩ : syracuseStep 9270611 = 13905917) B13905917
theorem B3907691 : Blo 1829616 3907691 := bstep (se 1 (by rfl) ⟨2930768, by rfl⟩ : syracuseStep 3907691 = 5861537) B5861537
theorem B23457215 : Blo 1829616 23457215 := bstep (se 1 (by rfl) ⟨17592911, by rfl⟩ : syracuseStep 23457215 = 35185823) B35185823
theorem B6180407 : Blo 1829616 6180407 := bstep (se 1 (by rfl) ⟨4635305, by rfl⟩ : syracuseStep 6180407 = 9270611) B9270611
theorem B1831163 : Blo 1829616 1831163 := bstep (se 1 (by rfl) ⟨1373372, by rfl⟩ : syracuseStep 1831163 = 2746745) B2746745
theorem B90321905 : Blo 1829616 90321905 := bstep (se 2 (by rfl) ⟨33870714, by rfl⟩ : syracuseStep 90321905 = 67741429) B67741429
theorem B2605127 : Blo 1829616 2605127 := bstep (se 1 (by rfl) ⟨1953845, by rfl⟩ : syracuseStep 2605127 = 3907691) B3907691
theorem B60214603 : Blo 1829616 60214603 := bstep (se 1 (by rfl) ⟨45160952, by rfl⟩ : syracuseStep 60214603 = 90321905) B90321905
theorem B15638143 : Blo 1829616 15638143 := bstep (se 1 (by rfl) ⟨11728607, by rfl⟩ : syracuseStep 15638143 = 23457215) B23457215
theorem B4120271 : Blo 1829616 4120271 := bstep (se 1 (by rfl) ⟨3090203, by rfl⟩ : syracuseStep 4120271 = 6180407) B6180407
theorem B6947005 : Blo 1829616 6947005 := bstep (se 3 (by rfl) ⟨1302563, by rfl⟩ : syracuseStep 6947005 = 2605127) B2605127
theorem B20850857 : Blo 1829616 20850857 := bstep (se 2 (by rfl) ⟨7819071, by rfl⟩ : syracuseStep 20850857 = 15638143) B15638143
theorem B2746847 : Blo 1829616 2746847 := bstep (se 1 (by rfl) ⟨2060135, by rfl⟩ : syracuseStep 2746847 = 4120271) B4120271
theorem B80286137 : Blo 1829616 80286137 := bstep (se 2 (by rfl) ⟨30107301, by rfl⟩ : syracuseStep 80286137 = 60214603) B60214603
theorem B1831231 : Blo 1829616 1831231 := bstep (se 1 (by rfl) ⟨1373423, by rfl⟩ : syracuseStep 1831231 = 2746847) B2746847
theorem B9262673 : Blo 1829616 9262673 := bstep (se 2 (by rfl) ⟨3473502, by rfl⟩ : syracuseStep 9262673 = 6947005) B6947005
theorem B53524091 : Blo 1829616 53524091 := bstep (se 1 (by rfl) ⟨40143068, by rfl⟩ : syracuseStep 53524091 = 80286137) B80286137
theorem B13900571 : Blo 1829616 13900571 := bstep (se 1 (by rfl) ⟨10425428, by rfl⟩ : syracuseStep 13900571 = 20850857) B20850857
theorem B9267047 : Blo 1829616 9267047 := bstep (se 1 (by rfl) ⟨6950285, by rfl⟩ : syracuseStep 9267047 = 13900571) B13900571
theorem B6175115 : Blo 1829616 6175115 := bstep (se 1 (by rfl) ⟨4631336, by rfl⟩ : syracuseStep 6175115 = 9262673) B9262673
theorem B35682727 : Blo 1829616 35682727 := bstep (se 1 (by rfl) ⟨26762045, by rfl⟩ : syracuseStep 35682727 = 53524091) B53524091
theorem B6178031 : Blo 1829616 6178031 := bstep (se 1 (by rfl) ⟨4633523, by rfl⟩ : syracuseStep 6178031 = 9267047) B9267047
theorem B4116743 : Blo 1829616 4116743 := bstep (se 1 (by rfl) ⟨3087557, by rfl⟩ : syracuseStep 4116743 = 6175115) B6175115
theorem B47576969 : Blo 1829616 47576969 := bstep (se 2 (by rfl) ⟨17841363, by rfl⟩ : syracuseStep 47576969 = 35682727) B35682727
theorem B2744495 : Blo 1829616 2744495 := bstep (se 1 (by rfl) ⟨2058371, by rfl⟩ : syracuseStep 2744495 = 4116743) B4116743
theorem B4118687 : Blo 1829616 4118687 := bstep (se 1 (by rfl) ⟨3089015, by rfl⟩ : syracuseStep 4118687 = 6178031) B6178031
theorem B31717979 : Blo 1829616 31717979 := bstep (se 1 (by rfl) ⟨23788484, by rfl⟩ : syracuseStep 31717979 = 47576969) B47576969
theorem B2745791 : Blo 1829616 2745791 := bstep (se 1 (by rfl) ⟨2059343, by rfl⟩ : syracuseStep 2745791 = 4118687) B4118687
theorem B21145319 : Blo 1829616 21145319 := bstep (se 1 (by rfl) ⟨15858989, by rfl⟩ : syracuseStep 21145319 = 31717979) B31717979
theorem B1829663 : Blo 1829616 1829663 := bstep (se 1 (by rfl) ⟨1372247, by rfl⟩ : syracuseStep 1829663 = 2744495) B2744495
theorem B1830527 : Blo 1829616 1830527 := bstep (se 1 (by rfl) ⟨1372895, by rfl⟩ : syracuseStep 1830527 = 2745791) B2745791
theorem B14096879 : Blo 1829616 14096879 := bstep (se 1 (by rfl) ⟨10572659, by rfl⟩ : syracuseStep 14096879 = 21145319) B21145319
theorem B9397919 : Blo 1829616 9397919 := bstep (se 1 (by rfl) ⟨7048439, by rfl⟩ : syracuseStep 9397919 = 14096879) B14096879
theorem B6265279 : Blo 1829616 6265279 := bstep (se 1 (by rfl) ⟨4698959, by rfl⟩ : syracuseStep 6265279 = 9397919) B9397919
theorem B8353705 : Blo 1829616 8353705 := bstep (se 2 (by rfl) ⟨3132639, by rfl⟩ : syracuseStep 8353705 = 6265279) B6265279
theorem B11138273 : Blo 1829616 11138273 := bstep (se 2 (by rfl) ⟨4176852, by rfl⟩ : syracuseStep 11138273 = 8353705) B8353705
theorem B7425515 : Blo 1829616 7425515 := bstep (se 1 (by rfl) ⟨5569136, by rfl⟩ : syracuseStep 7425515 = 11138273) B11138273
theorem B4950343 : Blo 1829616 4950343 := bstep (se 1 (by rfl) ⟨3712757, by rfl⟩ : syracuseStep 4950343 = 7425515) B7425515
theorem B6600457 : Blo 1829616 6600457 := bstep (se 2 (by rfl) ⟨2475171, by rfl⟩ : syracuseStep 6600457 = 4950343) B4950343
theorem B8800609 : Blo 1829616 8800609 := bstep (se 2 (by rfl) ⟨3300228, by rfl⟩ : syracuseStep 8800609 = 6600457) B6600457
theorem B11734145 : Blo 1829616 11734145 := bstep (se 2 (by rfl) ⟨4400304, by rfl⟩ : syracuseStep 11734145 = 8800609) B8800609
theorem B7822763 : Blo 1829616 7822763 := bstep (se 1 (by rfl) ⟨5867072, by rfl⟩ : syracuseStep 7822763 = 11734145) B11734145
theorem B5215175 : Blo 1829616 5215175 := bstep (se 1 (by rfl) ⟨3911381, by rfl⟩ : syracuseStep 5215175 = 7822763) B7822763
theorem B3476783 : Blo 1829616 3476783 := bstep (se 1 (by rfl) ⟨2607587, by rfl⟩ : syracuseStep 3476783 = 5215175) B5215175
theorem B9271421 : Blo 1829616 9271421 := bstep (se 3 (by rfl) ⟨1738391, by rfl⟩ : syracuseStep 9271421 = 3476783) B3476783
theorem B6180947 : Blo 1829616 6180947 := bstep (se 1 (by rfl) ⟨4635710, by rfl⟩ : syracuseStep 6180947 = 9271421) B9271421
theorem B4120631 : Blo 1829616 4120631 := bstep (se 1 (by rfl) ⟨3090473, by rfl⟩ : syracuseStep 4120631 = 6180947) B6180947
theorem B2747087 : Blo 1829616 2747087 := bstep (se 1 (by rfl) ⟨2060315, by rfl⟩ : syracuseStep 2747087 = 4120631) B4120631
theorem B1831391 : Blo 1829616 1831391 := bstep (se 1 (by rfl) ⟨1373543, by rfl⟩ : syracuseStep 1831391 = 2747087) B2747087

theorem C0 (j : ℕ) (h1 : 457404 ≤ j) (h2 : j ≤ 457903) : Blo 1829616 (4 * j + 3) := by
  interval_cases j
  · exact B1829619
  · exact B1829623
  · exact B1829627
  · exact B1829631
  · exact B1829635
  · exact B1829639
  · exact B1829643
  · exact B1829647
  · exact B1829651
  · exact B1829655
  · exact B1829659
  · exact B1829663
  · exact B1829667
  · exact B1829671
  · exact B1829675
  · exact B1829679
  · exact B1829683
  · exact B1829687
  · exact B1829691
  · exact B1829695
  · exact B1829699
  · exact B1829703
  · exact B1829707
  · exact B1829711
  · exact B1829715
  · exact B1829719
  · exact B1829723
  · exact B1829727
  · exact B1829731
  · exact B1829735
  · exact B1829739
  · exact B1829743
  · exact B1829747
  · exact B1829751
  · exact B1829755
  · exact B1829759
  · exact B1829763
  · exact B1829767
  · exact B1829771
  · exact B1829775
  · exact B1829779
  · exact B1829783
  · exact B1829787
  · exact B1829791
  · exact B1829795
  · exact B1829799
  · exact B1829803
  · exact B1829807
  · exact B1829811
  · exact B1829815
  · exact B1829819
  · exact B1829823
  · exact B1829827
  · exact B1829831
  · exact B1829835
  · exact B1829839
  · exact B1829843
  · exact B1829847
  · exact B1829851
  · exact B1829855
  · exact B1829859
  · exact B1829863
  · exact B1829867
  · exact B1829871
  · exact B1829875
  · exact B1829879
  · exact B1829883
  · exact B1829887
  · exact B1829891
  · exact B1829895
  · exact B1829899
  · exact B1829903
  · exact B1829907
  · exact B1829911
  · exact B1829915
  · exact B1829919
  · exact B1829923
  · exact B1829927
  · exact B1829931
  · exact B1829935
  · exact B1829939
  · exact B1829943
  · exact B1829947
  · exact B1829951
  · exact B1829955
  · exact B1829959
  · exact B1829963
  · exact B1829967
  · exact B1829971
  · exact B1829975
  · exact B1829979
  · exact B1829983
  · exact B1829987
  · exact B1829991
  · exact B1829995
  · exact B1829999
  · exact B1830003
  · exact B1830007
  · exact B1830011
  · exact B1830015
  · exact B1830019
  · exact B1830023
  · exact B1830027
  · exact B1830031
  · exact B1830035
  · exact B1830039
  · exact B1830043
  · exact B1830047
  · exact B1830051
  · exact B1830055
  · exact B1830059
  · exact B1830063
  · exact B1830067
  · exact B1830071
  · exact B1830075
  · exact B1830079
  · exact B1830083
  · exact B1830087
  · exact B1830091
  · exact B1830095
  · exact B1830099
  · exact B1830103
  · exact B1830107
  · exact B1830111
  · exact B1830115
  · exact B1830119
  · exact B1830123
  · exact B1830127
  · exact B1830131
  · exact B1830135
  · exact B1830139
  · exact B1830143
  · exact B1830147
  · exact B1830151
  · exact B1830155
  · exact B1830159
  · exact B1830163
  · exact B1830167
  · exact B1830171
  · exact B1830175
  · exact B1830179
  · exact B1830183
  · exact B1830187
  · exact B1830191
  · exact B1830195
  · exact B1830199
  · exact B1830203
  · exact B1830207
  · exact B1830211
  · exact B1830215
  · exact B1830219
  · exact B1830223
  · exact B1830227
  · exact B1830231
  · exact B1830235
  · exact B1830239
  · exact B1830243
  · exact B1830247
  · exact B1830251
  · exact B1830255
  · exact B1830259
  · exact B1830263
  · exact B1830267
  · exact B1830271
  · exact B1830275
  · exact B1830279
  · exact B1830283
  · exact B1830287
  · exact B1830291
  · exact B1830295
  · exact B1830299
  · exact B1830303
  · exact B1830307
  · exact B1830311
  · exact B1830315
  · exact B1830319
  · exact B1830323
  · exact B1830327
  · exact B1830331
  · exact B1830335
  · exact B1830339
  · exact B1830343
  · exact B1830347
  · exact B1830351
  · exact B1830355
  · exact B1830359
  · exact B1830363
  · exact B1830367
  · exact B1830371
  · exact B1830375
  · exact B1830379
  · exact B1830383
  · exact B1830387
  · exact B1830391
  · exact B1830395
  · exact B1830399
  · exact B1830403
  · exact B1830407
  · exact B1830411
  · exact B1830415
  · exact B1830419
  · exact B1830423
  · exact B1830427
  · exact B1830431
  · exact B1830435
  · exact B1830439
  · exact B1830443
  · exact B1830447
  · exact B1830451
  · exact B1830455
  · exact B1830459
  · exact B1830463
  · exact B1830467
  · exact B1830471
  · exact B1830475
  · exact B1830479
  · exact B1830483
  · exact B1830487
  · exact B1830491
  · exact B1830495
  · exact B1830499
  · exact B1830503
  · exact B1830507
  · exact B1830511
  · exact B1830515
  · exact B1830519
  · exact B1830523
  · exact B1830527
  · exact B1830531
  · exact B1830535
  · exact B1830539
  · exact B1830543
  · exact B1830547
  · exact B1830551
  · exact B1830555
  · exact B1830559
  · exact B1830563
  · exact B1830567
  · exact B1830571
  · exact B1830575
  · exact B1830579
  · exact B1830583
  · exact B1830587
  · exact B1830591
  · exact B1830595
  · exact B1830599
  · exact B1830603
  · exact B1830607
  · exact B1830611
  · exact B1830615
  · exact B1830619
  · exact B1830623
  · exact B1830627
  · exact B1830631
  · exact B1830635
  · exact B1830639
  · exact B1830643
  · exact B1830647
  · exact B1830651
  · exact B1830655
  · exact B1830659
  · exact B1830663
  · exact B1830667
  · exact B1830671
  · exact B1830675
  · exact B1830679
  · exact B1830683
  · exact B1830687
  · exact B1830691
  · exact B1830695
  · exact B1830699
  · exact B1830703
  · exact B1830707
  · exact B1830711
  · exact B1830715
  · exact B1830719
  · exact B1830723
  · exact B1830727
  · exact B1830731
  · exact B1830735
  · exact B1830739
  · exact B1830743
  · exact B1830747
  · exact B1830751
  · exact B1830755
  · exact B1830759
  · exact B1830763
  · exact B1830767
  · exact B1830771
  · exact B1830775
  · exact B1830779
  · exact B1830783
  · exact B1830787
  · exact B1830791
  · exact B1830795
  · exact B1830799
  · exact B1830803
  · exact B1830807
  · exact B1830811
  · exact B1830815
  · exact B1830819
  · exact B1830823
  · exact B1830827
  · exact B1830831
  · exact B1830835
  · exact B1830839
  · exact B1830843
  · exact B1830847
  · exact B1830851
  · exact B1830855
  · exact B1830859
  · exact B1830863
  · exact B1830867
  · exact B1830871
  · exact B1830875
  · exact B1830879
  · exact B1830883
  · exact B1830887
  · exact B1830891
  · exact B1830895
  · exact B1830899
  · exact B1830903
  · exact B1830907
  · exact B1830911
  · exact B1830915
  · exact B1830919
  · exact B1830923
  · exact B1830927
  · exact B1830931
  · exact B1830935
  · exact B1830939
  · exact B1830943
  · exact B1830947
  · exact B1830951
  · exact B1830955
  · exact B1830959
  · exact B1830963
  · exact B1830967
  · exact B1830971
  · exact B1830975
  · exact B1830979
  · exact B1830983
  · exact B1830987
  · exact B1830991
  · exact B1830995
  · exact B1830999
  · exact B1831003
  · exact B1831007
  · exact B1831011
  · exact B1831015
  · exact B1831019
  · exact B1831023
  · exact B1831027
  · exact B1831031
  · exact B1831035
  · exact B1831039
  · exact B1831043
  · exact B1831047
  · exact B1831051
  · exact B1831055
  · exact B1831059
  · exact B1831063
  · exact B1831067
  · exact B1831071
  · exact B1831075
  · exact B1831079
  · exact B1831083
  · exact B1831087
  · exact B1831091
  · exact B1831095
  · exact B1831099
  · exact B1831103
  · exact B1831107
  · exact B1831111
  · exact B1831115
  · exact B1831119
  · exact B1831123
  · exact B1831127
  · exact B1831131
  · exact B1831135
  · exact B1831139
  · exact B1831143
  · exact B1831147
  · exact B1831151
  · exact B1831155
  · exact B1831159
  · exact B1831163
  · exact B1831167
  · exact B1831171
  · exact B1831175
  · exact B1831179
  · exact B1831183
  · exact B1831187
  · exact B1831191
  · exact B1831195
  · exact B1831199
  · exact B1831203
  · exact B1831207
  · exact B1831211
  · exact B1831215
  · exact B1831219
  · exact B1831223
  · exact B1831227
  · exact B1831231
  · exact B1831235
  · exact B1831239
  · exact B1831243
  · exact B1831247
  · exact B1831251
  · exact B1831255
  · exact B1831259
  · exact B1831263
  · exact B1831267
  · exact B1831271
  · exact B1831275
  · exact B1831279
  · exact B1831283
  · exact B1831287
  · exact B1831291
  · exact B1831295
  · exact B1831299
  · exact B1831303
  · exact B1831307
  · exact B1831311
  · exact B1831315
  · exact B1831319
  · exact B1831323
  · exact B1831327
  · exact B1831331
  · exact B1831335
  · exact B1831339
  · exact B1831343
  · exact B1831347
  · exact B1831351
  · exact B1831355
  · exact B1831359
  · exact B1831363
  · exact B1831367
  · exact B1831371
  · exact B1831375
  · exact B1831379
  · exact B1831383
  · exact B1831387
  · exact B1831391
  · exact B1831395
  · exact B1831399
  · exact B1831403
  · exact B1831407
  · exact B1831411
  · exact B1831415
  · exact B1831419
  · exact B1831423
  · exact B1831427
  · exact B1831431
  · exact B1831435
  · exact B1831439
  · exact B1831443
  · exact B1831447
  · exact B1831451
  · exact B1831455
  · exact B1831459
  · exact B1831463
  · exact B1831467
  · exact B1831471
  · exact B1831475
  · exact B1831479
  · exact B1831483
  · exact B1831487
  · exact B1831491
  · exact B1831495
  · exact B1831499
  · exact B1831503
  · exact B1831507
  · exact B1831511
  · exact B1831515
  · exact B1831519
  · exact B1831523
  · exact B1831527
  · exact B1831531
  · exact B1831535
  · exact B1831539
  · exact B1831543
  · exact B1831547
  · exact B1831551
  · exact B1831555
  · exact B1831559
  · exact B1831563
  · exact B1831567
  · exact B1831571
  · exact B1831575
  · exact B1831579
  · exact B1831583
  · exact B1831587
  · exact B1831591
  · exact B1831595
  · exact B1831599
  · exact B1831603
  · exact B1831607
  · exact B1831611
  · exact B1831615

theorem solution (m : ℕ) (hlo : 1829616 ≤ m) (hhi : m ≤ 1831616) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 457404 ≤ j := by omega
    have hj2 : j ≤ 457903 := by omega
    have hb : Blo 1829616 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
