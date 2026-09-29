-- Prove2me | solution 1 for syracuse_descends_range_1032607_1036607
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:22.505487+00:00
-- url     : https://prove2.me/submissions/5fd442b1-c56c-46e3-abb6-73744494121f

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


theorem B3932165 : Blo 1032607 3932165 := bbase (se 4 (by rfl) ⟨368640, by rfl⟩ : syracuseStep 3932165 = 737281) (by norm_num)
theorem B1310737 : Blo 1032607 1310737 := bbase (se 2 (by rfl) ⟨491526, by rfl⟩ : syracuseStep 1310737 = 983053) (by norm_num)
theorem B2326589 : Blo 1032607 2326589 := bbase (se 3 (by rfl) ⟨436235, by rfl⟩ : syracuseStep 2326589 = 872471) (by norm_num)
theorem B1966189 : Blo 1032607 1966189 := bbase (se 3 (by rfl) ⟨368660, by rfl⟩ : syracuseStep 1966189 = 737321) (by norm_num)
theorem B1310833 : Blo 1032607 1310833 := bbase (se 2 (by rfl) ⟨491562, by rfl⟩ : syracuseStep 1310833 = 983125) (by norm_num)
theorem B4259957 : Blo 1032607 4259957 := bbase (se 5 (by rfl) ⟨199685, by rfl⟩ : syracuseStep 4259957 = 399371) (by norm_num)
theorem B2326661 : Blo 1032607 2326661 := bbase (se 4 (by rfl) ⟨218124, by rfl⟩ : syracuseStep 2326661 = 436249) (by norm_num)
theorem B2621605 : Blo 1032607 2621605 := bbase (se 4 (by rfl) ⟨245775, by rfl⟩ : syracuseStep 2621605 = 491551) (by norm_num)
theorem B1474733 : Blo 1032607 1474733 := bbase (se 3 (by rfl) ⟨276512, by rfl⟩ : syracuseStep 1474733 = 553025) (by norm_num)
theorem B2326733 : Blo 1032607 2326733 := bbase (se 3 (by rfl) ⟨436262, by rfl⟩ : syracuseStep 2326733 = 872525) (by norm_num)
theorem B5603573 : Blo 1032607 5603573 := bbase (se 5 (by rfl) ⟨262667, by rfl⟩ : syracuseStep 5603573 = 525335) (by norm_num)
theorem B1966349 : Blo 1032607 1966349 := bbase (se 3 (by rfl) ⟨368690, by rfl⟩ : syracuseStep 1966349 = 737381) (by norm_num)
theorem B2326805 : Blo 1032607 2326805 := bbase (se 6 (by rfl) ⟨54534, by rfl⟩ : syracuseStep 2326805 = 109069) (by norm_num)
theorem B2621717 : Blo 1032607 2621717 := bbase (se 6 (by rfl) ⟨61446, by rfl⟩ : syracuseStep 2621717 = 122893) (by norm_num)
theorem B1311005 : Blo 1032607 1311005 := bbase (se 3 (by rfl) ⟨245813, by rfl⟩ : syracuseStep 1311005 = 491627) (by norm_num)
theorem B1311061 : Blo 1032607 1311061 := bbase (se 10 (by rfl) ⟨1920, by rfl⟩ : syracuseStep 1311061 = 3841) (by norm_num)
theorem B2326877 : Blo 1032607 2326877 := bbase (se 3 (by rfl) ⟨436289, by rfl⟩ : syracuseStep 2326877 = 872579) (by norm_num)
theorem B3408229 : Blo 1032607 3408229 := bbase (se 4 (by rfl) ⟨319521, by rfl⟩ : syracuseStep 3408229 = 639043) (by norm_num)
theorem B1966493 : Blo 1032607 1966493 := bbase (se 3 (by rfl) ⟨368717, by rfl⟩ : syracuseStep 1966493 = 737435) (by norm_num)
theorem B2326949 : Blo 1032607 2326949 := bbase (se 4 (by rfl) ⟨218151, by rfl⟩ : syracuseStep 2326949 = 436303) (by norm_num)
theorem B1311157 : Blo 1032607 1311157 := bbase (se 5 (by rfl) ⟨61460, by rfl⟩ : syracuseStep 1311157 = 122921) (by norm_num)
theorem B1049041 : Blo 1032607 1049041 := bbase (se 2 (by rfl) ⟨393390, by rfl⟩ : syracuseStep 1049041 = 786781) (by norm_num)
theorem B1769941 : Blo 1032607 1769941 := bbase (se 7 (by rfl) ⟨20741, by rfl⟩ : syracuseStep 1769941 = 41483) (by norm_num)
theorem B2621909 : Blo 1032607 2621909 := bbase (se 7 (by rfl) ⟨30725, by rfl⟩ : syracuseStep 2621909 = 61451) (by norm_num)
theorem B4719077 : Blo 1032607 4719077 := bbase (se 4 (by rfl) ⟨442413, by rfl⟩ : syracuseStep 4719077 = 884827) (by norm_num)
theorem B4424165 : Blo 1032607 4424165 := bbase (se 4 (by rfl) ⟨414765, by rfl⟩ : syracuseStep 4424165 = 829531) (by norm_num)
theorem B2327021 : Blo 1032607 2327021 := bbase (se 3 (by rfl) ⟨436316, by rfl⟩ : syracuseStep 2327021 = 872633) (by norm_num)
theorem B2327093 : Blo 1032607 2327093 := bbase (se 5 (by rfl) ⟨109082, by rfl⟩ : syracuseStep 2327093 = 218165) (by norm_num)
theorem B1180217 : Blo 1032607 1180217 := bbase (se 2 (by rfl) ⟨442581, by rfl⟩ : syracuseStep 1180217 = 885163) (by norm_num)
theorem B2982469 : Blo 1032607 2982469 := bbase (se 4 (by rfl) ⟨279606, by rfl⟩ : syracuseStep 2982469 = 559213) (by norm_num)
theorem B1311329 : Blo 1032607 1311329 := bbase (se 2 (by rfl) ⟨491748, by rfl⟩ : syracuseStep 1311329 = 983497) (by norm_num)
theorem B2327165 : Blo 1032607 2327165 := bbase (se 3 (by rfl) ⟨436343, by rfl⟩ : syracuseStep 2327165 = 872687) (by norm_num)
theorem B1311385 : Blo 1032607 1311385 := bbase (se 2 (by rfl) ⟨491769, by rfl⟩ : syracuseStep 1311385 = 983539) (by norm_num)
theorem B2949797 : Blo 1032607 2949797 := bbase (se 4 (by rfl) ⟨276543, by rfl⟩ : syracuseStep 2949797 = 553087) (by norm_num)
theorem B2654893 : Blo 1032607 2654893 := bbase (se 3 (by rfl) ⟨497792, by rfl⟩ : syracuseStep 2654893 = 995585) (by norm_num)
theorem B1966781 : Blo 1032607 1966781 := bbase (se 3 (by rfl) ⟨368771, by rfl⟩ : syracuseStep 1966781 = 737543) (by norm_num)
theorem B2327237 : Blo 1032607 2327237 := bbase (se 4 (by rfl) ⟨218178, by rfl⟩ : syracuseStep 2327237 = 436357) (by norm_num)
theorem B1573597 : Blo 1032607 1573597 := bbase (se 3 (by rfl) ⟨295049, by rfl⟩ : syracuseStep 1573597 = 590099) (by norm_num)
theorem B1311481 : Blo 1032607 1311481 := bbase (se 2 (by rfl) ⟨491805, by rfl⟩ : syracuseStep 1311481 = 983611) (by norm_num)
theorem B3539717 : Blo 1032607 3539717 := bbase (se 4 (by rfl) ⟨331848, by rfl⟩ : syracuseStep 3539717 = 663697) (by norm_num)
theorem B2327309 : Blo 1032607 2327309 := bbase (se 3 (by rfl) ⟨436370, by rfl⟩ : syracuseStep 2327309 = 872741) (by norm_num)
theorem B2622253 : Blo 1032607 2622253 := bbase (se 3 (by rfl) ⟨491672, by rfl⟩ : syracuseStep 2622253 = 983345) (by norm_num)
theorem B2327381 : Blo 1032607 2327381 := bbase (se 9 (by rfl) ⟨6818, by rfl⟩ : syracuseStep 2327381 = 13637) (by norm_num)
theorem B1966933 : Blo 1032607 1966933 := bbase (se 9 (by rfl) ⟨5762, by rfl⟩ : syracuseStep 1966933 = 11525) (by norm_num)
theorem B2327453 : Blo 1032607 2327453 := bbase (se 3 (by rfl) ⟨436397, by rfl⟩ : syracuseStep 2327453 = 872795) (by norm_num)
theorem B2622365 : Blo 1032607 2622365 := bbase (se 3 (by rfl) ⟨491693, by rfl⟩ : syracuseStep 2622365 = 983387) (by norm_num)
theorem B1311653 : Blo 1032607 1311653 := bbase (se 4 (by rfl) ⟨122967, by rfl⟩ : syracuseStep 1311653 = 245935) (by norm_num)
theorem B1573805 : Blo 1032607 1573805 := bbase (se 3 (by rfl) ⟨295088, by rfl⟩ : syracuseStep 1573805 = 590177) (by norm_num)
theorem B1311709 : Blo 1032607 1311709 := bbase (se 3 (by rfl) ⟨245945, by rfl⟩ : syracuseStep 1311709 = 491891) (by norm_num)
theorem B2327525 : Blo 1032607 2327525 := bbase (se 4 (by rfl) ⟨218205, by rfl⟩ : syracuseStep 2327525 = 436411) (by norm_num)
theorem B1180669 : Blo 1032607 1180669 := bbase (se 3 (by rfl) ⟨221375, by rfl⟩ : syracuseStep 1180669 = 442751) (by norm_num)
theorem B1180681 : Blo 1032607 1180681 := bbase (se 2 (by rfl) ⟨442755, by rfl⟩ : syracuseStep 1180681 = 885511) (by norm_num)
theorem B2327597 : Blo 1032607 2327597 := bbase (se 3 (by rfl) ⟨436424, by rfl⟩ : syracuseStep 2327597 = 872849) (by norm_num)
theorem B1049645 : Blo 1032607 1049645 := bbase (se 3 (by rfl) ⟨196808, by rfl⟩ : syracuseStep 1049645 = 393617) (by norm_num)
theorem B1311805 : Blo 1032607 1311805 := bbase (se 3 (by rfl) ⟨245963, by rfl⟩ : syracuseStep 1311805 = 491927) (by norm_num)
theorem B1180741 : Blo 1032607 1180741 := bbase (se 4 (by rfl) ⟨110694, by rfl⟩ : syracuseStep 1180741 = 221389) (by norm_num)
theorem B2622557 : Blo 1032607 2622557 := bbase (se 3 (by rfl) ⟨491729, by rfl⟩ : syracuseStep 2622557 = 983459) (by norm_num)
theorem B2327669 : Blo 1032607 2327669 := bbase (se 5 (by rfl) ⟨109109, by rfl⟩ : syracuseStep 2327669 = 218219) (by norm_num)
theorem B1967237 : Blo 1032607 1967237 := bbase (se 4 (by rfl) ⟨184428, by rfl⟩ : syracuseStep 1967237 = 368857) (by norm_num)
theorem B2098325 : Blo 1032607 2098325 := bbase (se 6 (by rfl) ⟨49179, by rfl⟩ : syracuseStep 2098325 = 98359) (by norm_num)
theorem B2327741 : Blo 1032607 2327741 := bbase (se 3 (by rfl) ⟨436451, by rfl⟩ : syracuseStep 2327741 = 872903) (by norm_num)
theorem B5244101 : Blo 1032607 5244101 := bbase (se 4 (by rfl) ⟨491634, by rfl⟩ : syracuseStep 5244101 = 983269) (by norm_num)
theorem B2327813 : Blo 1032607 2327813 := bbase (se 4 (by rfl) ⟨218232, by rfl⟩ : syracuseStep 2327813 = 436465) (by norm_num)
theorem B2950469 : Blo 1032607 2950469 := bbase (se 4 (by rfl) ⟨276606, by rfl⟩ : syracuseStep 2950469 = 553213) (by norm_num)
theorem B2327885 : Blo 1032607 2327885 := bbase (se 3 (by rfl) ⟨436478, by rfl⟩ : syracuseStep 2327885 = 872957) (by norm_num)
theorem B2327957 : Blo 1032607 2327957 := bbase (se 6 (by rfl) ⟨54561, by rfl⟩ : syracuseStep 2327957 = 109123) (by norm_num)
theorem B2622901 : Blo 1032607 2622901 := bbase (se 5 (by rfl) ⟨122948, by rfl⟩ : syracuseStep 2622901 = 245897) (by norm_num)
theorem B2328029 : Blo 1032607 2328029 := bbase (se 3 (by rfl) ⟨436505, by rfl⟩ : syracuseStep 2328029 = 873011) (by norm_num)
theorem B3311077 : Blo 1032607 3311077 := bbase (se 4 (by rfl) ⟨310413, by rfl⟩ : syracuseStep 3311077 = 620827) (by norm_num)
theorem B2328101 : Blo 1032607 2328101 := bbase (se 4 (by rfl) ⟨218259, by rfl⟩ : syracuseStep 2328101 = 436519) (by norm_num)
theorem B2623013 : Blo 1032607 2623013 := bbase (se 4 (by rfl) ⟨245907, by rfl⟩ : syracuseStep 2623013 = 491815) (by norm_num)
theorem B7865909 : Blo 1032607 7865909 := bbase (se 5 (by rfl) ⟨368714, by rfl⟩ : syracuseStep 7865909 = 737429) (by norm_num)
theorem B2328173 : Blo 1032607 2328173 := bbase (se 3 (by rfl) ⟨436532, by rfl⟩ : syracuseStep 2328173 = 873065) (by norm_num)
theorem B2328245 : Blo 1032607 2328245 := bbase (se 5 (by rfl) ⟨109136, by rfl⟩ : syracuseStep 2328245 = 218273) (by norm_num)
theorem B2623205 : Blo 1032607 2623205 := bbase (se 4 (by rfl) ⟨245925, by rfl⟩ : syracuseStep 2623205 = 491851) (by norm_num)
theorem B2950901 : Blo 1032607 2950901 := bbase (se 5 (by rfl) ⟨138323, by rfl⟩ : syracuseStep 2950901 = 276647) (by norm_num)
theorem B2328317 : Blo 1032607 2328317 := bbase (se 3 (by rfl) ⟨436559, by rfl⟩ : syracuseStep 2328317 = 873119) (by norm_num)
theorem B2361125 : Blo 1032607 2361125 := bbase (se 4 (by rfl) ⟨221355, by rfl⟩ : syracuseStep 2361125 = 442711) (by norm_num)
theorem B2328389 : Blo 1032607 2328389 := bbase (se 4 (by rfl) ⟨218286, by rfl⟩ : syracuseStep 2328389 = 436573) (by norm_num)
theorem B2328461 : Blo 1032607 2328461 := bbase (se 3 (by rfl) ⟨436586, by rfl⟩ : syracuseStep 2328461 = 873173) (by norm_num)
theorem B1181621 : Blo 1032607 1181621 := bbase (se 5 (by rfl) ⟨55388, by rfl⟩ : syracuseStep 1181621 = 110777) (by norm_num)
theorem B2328533 : Blo 1032607 2328533 := bbase (se 7 (by rfl) ⟨27287, by rfl⟩ : syracuseStep 2328533 = 54575) (by norm_num)
theorem B2328605 : Blo 1032607 2328605 := bbase (se 3 (by rfl) ⟨436613, by rfl⟩ : syracuseStep 2328605 = 873227) (by norm_num)
theorem B2623549 : Blo 1032607 2623549 := bbase (se 3 (by rfl) ⟨491915, by rfl⟩ : syracuseStep 2623549 = 983831) (by norm_num)
theorem B3934277 : Blo 1032607 3934277 := bbase (se 4 (by rfl) ⟨368838, by rfl⟩ : syracuseStep 3934277 = 737677) (by norm_num)
theorem B2328677 : Blo 1032607 2328677 := bbase (se 4 (by rfl) ⟨218313, by rfl⟩ : syracuseStep 2328677 = 436627) (by norm_num)
theorem B2328749 : Blo 1032607 2328749 := bbase (se 3 (by rfl) ⟨436640, by rfl⟩ : syracuseStep 2328749 = 873281) (by norm_num)
theorem B2623661 : Blo 1032607 2623661 := bbase (se 3 (by rfl) ⟨491936, by rfl⟩ : syracuseStep 2623661 = 983873) (by norm_num)
theorem B4425941 : Blo 1032607 4425941 := bbase (se 7 (by rfl) ⟨51866, by rfl⟩ : syracuseStep 4425941 = 103733) (by norm_num)
theorem B2328821 : Blo 1032607 2328821 := bbase (se 5 (by rfl) ⟨109163, by rfl⟩ : syracuseStep 2328821 = 218327) (by norm_num)
theorem B2328893 : Blo 1032607 2328893 := bbase (se 3 (by rfl) ⟨436667, by rfl⟩ : syracuseStep 2328893 = 873335) (by norm_num)
theorem B3934565 : Blo 1032607 3934565 := bbase (se 4 (by rfl) ⟨368865, by rfl⟩ : syracuseStep 3934565 = 737731) (by norm_num)
theorem B2623853 : Blo 1032607 2623853 := bbase (se 3 (by rfl) ⟨491972, by rfl⟩ : syracuseStep 2623853 = 983945) (by norm_num)
theorem B2328965 : Blo 1032607 2328965 := bbase (se 4 (by rfl) ⟨218340, by rfl⟩ : syracuseStep 2328965 = 436681) (by norm_num)
theorem B1575301 : Blo 1032607 1575301 := bbase (se 4 (by rfl) ⟨147684, by rfl⟩ : syracuseStep 1575301 = 295369) (by norm_num)
theorem B2099621 : Blo 1032607 2099621 := bbase (se 4 (by rfl) ⟨196839, by rfl⟩ : syracuseStep 2099621 = 393679) (by norm_num)
theorem B2329037 : Blo 1032607 2329037 := bbase (se 3 (by rfl) ⟨436694, by rfl⟩ : syracuseStep 2329037 = 873389) (by norm_num)
theorem B5245397 : Blo 1032607 5245397 := bbase (se 7 (by rfl) ⟨61469, by rfl⟩ : syracuseStep 5245397 = 122939) (by norm_num)
theorem B2951653 : Blo 1032607 2951653 := bbase (se 4 (by rfl) ⟨276717, by rfl⟩ : syracuseStep 2951653 = 553435) (by norm_num)
theorem B2329109 : Blo 1032607 2329109 := bbase (se 6 (by rfl) ⟨54588, by rfl⟩ : syracuseStep 2329109 = 109177) (by norm_num)
theorem B2329181 : Blo 1032607 2329181 := bbase (se 3 (by rfl) ⟨436721, by rfl⟩ : syracuseStep 2329181 = 873443) (by norm_num)
theorem B2329253 : Blo 1032607 2329253 := bbase (se 4 (by rfl) ⟨218367, by rfl⟩ : syracuseStep 2329253 = 436735) (by norm_num)
theorem B2329325 : Blo 1032607 2329325 := bbase (se 3 (by rfl) ⟨436748, by rfl⟩ : syracuseStep 2329325 = 873497) (by norm_num)
theorem B2394917 : Blo 1032607 2394917 := bbase (se 4 (by rfl) ⟨224523, by rfl⟩ : syracuseStep 2394917 = 449047) (by norm_num)
theorem B2329397 : Blo 1032607 2329397 := bbase (se 5 (by rfl) ⟨109190, by rfl⟩ : syracuseStep 2329397 = 218381) (by norm_num)
theorem B2329469 : Blo 1032607 2329469 := bbase (se 3 (by rfl) ⟨436775, by rfl⟩ : syracuseStep 2329469 = 873551) (by norm_num)
theorem B2329541 : Blo 1032607 2329541 := bbase (se 4 (by rfl) ⟨218394, by rfl⟩ : syracuseStep 2329541 = 436789) (by norm_num)
theorem B2100205 : Blo 1032607 2100205 := bbase (se 3 (by rfl) ⟨393788, by rfl⟩ : syracuseStep 2100205 = 787577) (by norm_num)
theorem B2329613 : Blo 1032607 2329613 := bbase (se 3 (by rfl) ⟨436802, by rfl⟩ : syracuseStep 2329613 = 873605) (by norm_num)
theorem B2329685 : Blo 1032607 2329685 := bbase (se 8 (by rfl) ⟨13650, by rfl⟩ : syracuseStep 2329685 = 27301) (by norm_num)
theorem B6622357 : Blo 1032607 6622357 := bbase (se 6 (by rfl) ⟨155211, by rfl⟩ : syracuseStep 6622357 = 310423) (by norm_num)
theorem B2329757 : Blo 1032607 2329757 := bbase (se 3 (by rfl) ⟨436829, by rfl⟩ : syracuseStep 2329757 = 873659) (by norm_num)
theorem B4426933 : Blo 1032607 4426933 := bbase (se 5 (by rfl) ⟨207512, by rfl⟩ : syracuseStep 4426933 = 415025) (by norm_num)
theorem B2329829 : Blo 1032607 2329829 := bbase (se 4 (by rfl) ⟨218421, by rfl⟩ : syracuseStep 2329829 = 436843) (by norm_num)
theorem B3149093 : Blo 1032607 3149093 := bbase (se 4 (by rfl) ⟨295227, by rfl⟩ : syracuseStep 3149093 = 590455) (by norm_num)
theorem B2329901 : Blo 1032607 2329901 := bbase (se 3 (by rfl) ⟨436856, by rfl⟩ : syracuseStep 2329901 = 873713) (by norm_num)
theorem B4197685 : Blo 1032607 4197685 := bbase (se 5 (by rfl) ⟨196766, by rfl⟩ : syracuseStep 4197685 = 393533) (by norm_num)
theorem B22646101 : Blo 1032607 22646101 := bbase (se 11 (by rfl) ⟨16586, by rfl⟩ : syracuseStep 22646101 = 33173) (by norm_num)
theorem B2329973 : Blo 1032607 2329973 := bbase (se 5 (by rfl) ⟨109217, by rfl⟩ : syracuseStep 2329973 = 218435) (by norm_num)
theorem B2330045 : Blo 1032607 2330045 := bbase (se 3 (by rfl) ⟨436883, by rfl⟩ : syracuseStep 2330045 = 873767) (by norm_num)
theorem B2362877 : Blo 1032607 2362877 := bbase (se 3 (by rfl) ⟨443039, by rfl⟩ : syracuseStep 2362877 = 886079) (by norm_num)
theorem B2330117 : Blo 1032607 2330117 := bbase (se 4 (by rfl) ⟨218448, by rfl⟩ : syracuseStep 2330117 = 436897) (by norm_num)
theorem B3935749 : Blo 1032607 3935749 := bbase (se 4 (by rfl) ⟨368976, by rfl⟩ : syracuseStep 3935749 = 737953) (by norm_num)
theorem B2330189 : Blo 1032607 2330189 := bbase (se 3 (by rfl) ⟨436910, by rfl⟩ : syracuseStep 2330189 = 873821) (by norm_num)
theorem B2330261 : Blo 1032607 2330261 := bbase (se 6 (by rfl) ⟨54615, by rfl⟩ : syracuseStep 2330261 = 109231) (by norm_num)
theorem B2657981 : Blo 1032607 2657981 := bbase (se 3 (by rfl) ⟨498371, by rfl⟩ : syracuseStep 2657981 = 996743) (by norm_num)
theorem B2330333 : Blo 1032607 2330333 := bbase (se 3 (by rfl) ⟨436937, by rfl⟩ : syracuseStep 2330333 = 873875) (by norm_num)
theorem B5246693 : Blo 1032607 5246693 := bbase (se 4 (by rfl) ⟨491877, by rfl⟩ : syracuseStep 5246693 = 983755) (by norm_num)
theorem B2330405 : Blo 1032607 2330405 := bbase (se 4 (by rfl) ⟨218475, by rfl⟩ : syracuseStep 2330405 = 436951) (by norm_num)
theorem B2330477 : Blo 1032607 2330477 := bbase (se 3 (by rfl) ⟨436964, by rfl⟩ : syracuseStep 2330477 = 873929) (by norm_num)
theorem B2658197 : Blo 1032607 2658197 := bbase (se 6 (by rfl) ⟨62301, by rfl⟩ : syracuseStep 2658197 = 124603) (by norm_num)
theorem B2330549 : Blo 1032607 2330549 := bbase (se 5 (by rfl) ⟨109244, by rfl⟩ : syracuseStep 2330549 = 218489) (by norm_num)
theorem B2330621 : Blo 1032607 2330621 := bbase (se 3 (by rfl) ⟨436991, by rfl⟩ : syracuseStep 2330621 = 873983) (by norm_num)
theorem B2101277 : Blo 1032607 2101277 := bbase (se 3 (by rfl) ⟨393989, by rfl⟩ : syracuseStep 2101277 = 787979) (by norm_num)
theorem B2330693 : Blo 1032607 2330693 := bbase (se 4 (by rfl) ⟨218502, by rfl⟩ : syracuseStep 2330693 = 437005) (by norm_num)
theorem B2101373 : Blo 1032607 2101373 := bbase (se 3 (by rfl) ⟨394007, by rfl⟩ : syracuseStep 2101373 = 788015) (by norm_num)
theorem B2330765 : Blo 1032607 2330765 := bbase (se 3 (by rfl) ⟨437018, by rfl⟩ : syracuseStep 2330765 = 874037) (by norm_num)
theorem B2330837 : Blo 1032607 2330837 := bbase (se 7 (by rfl) ⟨27314, by rfl⟩ : syracuseStep 2330837 = 54629) (by norm_num)
theorem B2330909 : Blo 1032607 2330909 := bbase (se 3 (by rfl) ⟨437045, by rfl⟩ : syracuseStep 2330909 = 874091) (by norm_num)
theorem B3313973 : Blo 1032607 3313973 := bbase (se 5 (by rfl) ⟨155342, by rfl⟩ : syracuseStep 3313973 = 310685) (by norm_num)
theorem B2363717 : Blo 1032607 2363717 := bbase (se 4 (by rfl) ⟨221598, by rfl⟩ : syracuseStep 2363717 = 443197) (by norm_num)
theorem B2330981 : Blo 1032607 2330981 := bbase (se 4 (by rfl) ⟨218529, by rfl⟩ : syracuseStep 2330981 = 437059) (by norm_num)
theorem B10097045 : Blo 1032607 10097045 := bbase (se 6 (by rfl) ⟨236649, by rfl⟩ : syracuseStep 10097045 = 473299) (by norm_num)
theorem B2331053 : Blo 1032607 2331053 := bbase (se 3 (by rfl) ⟨437072, by rfl⟩ : syracuseStep 2331053 = 874145) (by norm_num)
theorem B4198853 : Blo 1032607 4198853 := bbase (se 4 (by rfl) ⟨393642, by rfl⟩ : syracuseStep 4198853 = 787285) (by norm_num)
theorem B2331125 : Blo 1032607 2331125 := bbase (se 5 (by rfl) ⟨109271, by rfl⟩ : syracuseStep 2331125 = 218543) (by norm_num)
theorem B2331197 : Blo 1032607 2331197 := bbase (se 3 (by rfl) ⟨437099, by rfl⟩ : syracuseStep 2331197 = 874199) (by norm_num)
theorem B2331269 : Blo 1032607 2331269 := bbase (se 4 (by rfl) ⟨218556, by rfl⟩ : syracuseStep 2331269 = 437113) (by norm_num)
theorem B2331341 : Blo 1032607 2331341 := bbase (se 3 (by rfl) ⟨437126, by rfl⟩ : syracuseStep 2331341 = 874253) (by norm_num)
theorem B2331413 : Blo 1032607 2331413 := bbase (se 6 (by rfl) ⟨54642, by rfl⟩ : syracuseStep 2331413 = 109285) (by norm_num)
theorem B2331485 : Blo 1032607 2331485 := bbase (se 3 (by rfl) ⟨437153, by rfl⟩ : syracuseStep 2331485 = 874307) (by norm_num)
theorem B2331557 : Blo 1032607 2331557 := bbase (se 4 (by rfl) ⟨218583, by rfl⟩ : syracuseStep 2331557 = 437167) (by norm_num)
theorem B2331629 : Blo 1032607 2331629 := bbase (se 3 (by rfl) ⟨437180, by rfl⟩ : syracuseStep 2331629 = 874361) (by norm_num)
theorem B2331701 : Blo 1032607 2331701 := bbase (se 5 (by rfl) ⟨109298, by rfl⟩ : syracuseStep 2331701 = 218597) (by norm_num)
theorem B4035701 : Blo 1032607 4035701 := bbase (se 5 (by rfl) ⟨189173, by rfl⟩ : syracuseStep 4035701 = 378347) (by norm_num)
theorem B2331773 : Blo 1032607 2331773 := bbase (se 3 (by rfl) ⟨437207, by rfl⟩ : syracuseStep 2331773 = 874415) (by norm_num)
theorem B2331845 : Blo 1032607 2331845 := bbase (se 4 (by rfl) ⟨218610, by rfl⟩ : syracuseStep 2331845 = 437221) (by norm_num)
theorem B2331917 : Blo 1032607 2331917 := bbase (se 3 (by rfl) ⟨437234, by rfl⟩ : syracuseStep 2331917 = 874469) (by norm_num)
theorem B2331989 : Blo 1032607 2331989 := bbase (se 14 (by rfl) ⟨213, by rfl⟩ : syracuseStep 2331989 = 427) (by norm_num)
theorem B2332061 : Blo 1032607 2332061 := bbase (se 3 (by rfl) ⟨437261, by rfl⟩ : syracuseStep 2332061 = 874523) (by norm_num)
theorem B2332133 : Blo 1032607 2332133 := bbase (se 4 (by rfl) ⟨218637, by rfl⟩ : syracuseStep 2332133 = 437275) (by norm_num)
theorem B2332205 : Blo 1032607 2332205 := bbase (se 3 (by rfl) ⟨437288, by rfl⟩ : syracuseStep 2332205 = 874577) (by norm_num)
theorem B14161493 : Blo 1032607 14161493 := bbase (se 8 (by rfl) ⟨82977, by rfl⟩ : syracuseStep 14161493 = 165955) (by norm_num)
theorem B2332277 : Blo 1032607 2332277 := bbase (se 5 (by rfl) ⟨109325, by rfl⟩ : syracuseStep 2332277 = 218651) (by norm_num)
theorem B2332349 : Blo 1032607 2332349 := bbase (se 3 (by rfl) ⟨437315, by rfl⟩ : syracuseStep 2332349 = 874631) (by norm_num)
theorem B1742573 : Blo 1032607 1742573 := bbase (se 3 (by rfl) ⟨326732, by rfl⟩ : syracuseStep 1742573 = 653465) (by norm_num)
theorem B1742701 : Blo 1032607 1742701 := bbase (se 3 (by rfl) ⟨326756, by rfl⟩ : syracuseStep 1742701 = 653513) (by norm_num)
theorem B1742789 : Blo 1032607 1742789 := bbase (se 4 (by rfl) ⟨163386, by rfl⟩ : syracuseStep 1742789 = 326773) (by norm_num)
theorem B1742917 : Blo 1032607 1742917 := bbase (se 4 (by rfl) ⟨163398, by rfl⟩ : syracuseStep 1742917 = 326797) (by norm_num)
theorem B3545189 : Blo 1032607 3545189 := bbase (se 4 (by rfl) ⟨332361, by rfl⟩ : syracuseStep 3545189 = 664723) (by norm_num)
theorem B6297749 : Blo 1032607 6297749 := bbase (se 6 (by rfl) ⟨147603, by rfl⟩ : syracuseStep 6297749 = 295207) (by norm_num)
theorem B1743005 : Blo 1032607 1743005 := bbase (se 3 (by rfl) ⟨326813, by rfl⟩ : syracuseStep 1743005 = 653627) (by norm_num)
theorem B1743133 : Blo 1032607 1743133 := bbase (se 3 (by rfl) ⟨326837, by rfl⟩ : syracuseStep 1743133 = 653675) (by norm_num)
theorem B1743221 : Blo 1032607 1743221 := bbase (se 5 (by rfl) ⟨81713, by rfl⟩ : syracuseStep 1743221 = 163427) (by norm_num)
theorem B1743349 : Blo 1032607 1743349 := bbase (se 5 (by rfl) ⟨81719, by rfl⟩ : syracuseStep 1743349 = 163439) (by norm_num)
theorem B8854069 : Blo 1032607 8854069 := bbase (se 5 (by rfl) ⟨415034, by rfl⟩ : syracuseStep 8854069 = 830069) (by norm_num)
theorem B4725317 : Blo 1032607 4725317 := bbase (se 4 (by rfl) ⟨442998, by rfl⟩ : syracuseStep 4725317 = 885997) (by norm_num)
theorem B1743437 : Blo 1032607 1743437 := bbase (se 3 (by rfl) ⟨326894, by rfl⟩ : syracuseStep 1743437 = 653789) (by norm_num)
theorem B1743565 : Blo 1032607 1743565 := bbase (se 3 (by rfl) ⟨326918, by rfl⟩ : syracuseStep 1743565 = 653837) (by norm_num)
theorem B1743653 : Blo 1032607 1743653 := bbase (se 4 (by rfl) ⟨163467, by rfl⟩ : syracuseStep 1743653 = 326935) (by norm_num)
theorem B1743781 : Blo 1032607 1743781 := bbase (se 4 (by rfl) ⟨163479, by rfl⟩ : syracuseStep 1743781 = 326959) (by norm_num)
theorem B20126677 : Blo 1032607 20126677 := bbase (se 7 (by rfl) ⟨235859, by rfl⟩ : syracuseStep 20126677 = 471719) (by norm_num)
theorem B1743869 : Blo 1032607 1743869 := bbase (se 3 (by rfl) ⟨326975, by rfl⟩ : syracuseStep 1743869 = 653951) (by norm_num)
theorem B1743997 : Blo 1032607 1743997 := bbase (se 3 (by rfl) ⟨326999, by rfl⟩ : syracuseStep 1743997 = 653999) (by norm_num)
theorem B1744085 : Blo 1032607 1744085 := bbase (se 7 (by rfl) ⟨20438, by rfl⟩ : syracuseStep 1744085 = 40877) (by norm_num)
theorem B2268397 : Blo 1032607 2268397 := bbase (se 3 (by rfl) ⟨425324, by rfl⟩ : syracuseStep 2268397 = 850649) (by norm_num)
theorem B1744213 : Blo 1032607 1744213 := bbase (se 11 (by rfl) ⟨1277, by rfl⟩ : syracuseStep 1744213 = 2555) (by norm_num)
theorem B3317125 : Blo 1032607 3317125 := bbase (se 4 (by rfl) ⟨310980, by rfl⟩ : syracuseStep 3317125 = 621961) (by norm_num)
theorem B10624405 : Blo 1032607 10624405 := bbase (se 6 (by rfl) ⟨249009, by rfl⟩ : syracuseStep 10624405 = 498019) (by norm_num)
theorem B9444757 : Blo 1032607 9444757 := bbase (se 6 (by rfl) ⟨221361, by rfl⟩ : syracuseStep 9444757 = 442723) (by norm_num)
theorem B1744301 : Blo 1032607 1744301 := bbase (se 3 (by rfl) ⟨327056, by rfl⟩ : syracuseStep 1744301 = 654113) (by norm_num)
theorem B1744429 : Blo 1032607 1744429 := bbase (se 3 (by rfl) ⟨327080, by rfl⟩ : syracuseStep 1744429 = 654161) (by norm_num)
theorem B1744517 : Blo 1032607 1744517 := bbase (se 4 (by rfl) ⟨163548, by rfl⟩ : syracuseStep 1744517 = 327097) (by norm_num)
theorem B9936533 : Blo 1032607 9936533 := bbase (se 6 (by rfl) ⟨232887, by rfl⟩ : syracuseStep 9936533 = 465775) (by norm_num)
theorem B1744645 : Blo 1032607 1744645 := bbase (se 4 (by rfl) ⟨163560, by rfl⟩ : syracuseStep 1744645 = 327121) (by norm_num)
theorem B1744733 : Blo 1032607 1744733 := bbase (se 3 (by rfl) ⟨327137, by rfl⟩ : syracuseStep 1744733 = 654275) (by norm_num)
theorem B4202389 : Blo 1032607 4202389 := bbase (se 6 (by rfl) ⟨98493, by rfl⟩ : syracuseStep 4202389 = 196987) (by norm_num)
theorem B1744861 : Blo 1032607 1744861 := bbase (se 3 (by rfl) ⟨327161, by rfl⟩ : syracuseStep 1744861 = 654323) (by norm_num)
theorem B1744949 : Blo 1032607 1744949 := bbase (se 5 (by rfl) ⟨81794, by rfl⟩ : syracuseStep 1744949 = 163589) (by norm_num)
theorem B1745077 : Blo 1032607 1745077 := bbase (se 5 (by rfl) ⟨81800, by rfl⟩ : syracuseStep 1745077 = 163601) (by norm_num)
theorem B1745165 : Blo 1032607 1745165 := bbase (se 3 (by rfl) ⟨327218, by rfl⟩ : syracuseStep 1745165 = 654437) (by norm_num)
theorem B1745293 : Blo 1032607 1745293 := bbase (se 3 (by rfl) ⟨327242, by rfl⟩ : syracuseStep 1745293 = 654485) (by norm_num)
theorem B1745381 : Blo 1032607 1745381 := bbase (se 4 (by rfl) ⟨163629, by rfl⟩ : syracuseStep 1745381 = 327259) (by norm_num)
theorem B1679933 : Blo 1032607 1679933 := bbase (se 3 (by rfl) ⟨314987, by rfl⟩ : syracuseStep 1679933 = 629975) (by norm_num)
theorem B1745509 : Blo 1032607 1745509 := bbase (se 4 (by rfl) ⟨163641, by rfl⟩ : syracuseStep 1745509 = 327283) (by norm_num)
theorem B1548917 : Blo 1032607 1548917 := bbase (se 5 (by rfl) ⟨72605, by rfl⟩ : syracuseStep 1548917 = 145211) (by norm_num)
theorem B1548941 : Blo 1032607 1548941 := bbase (se 3 (by rfl) ⟨290426, by rfl⟩ : syracuseStep 1548941 = 580853) (by norm_num)
theorem B1548965 : Blo 1032607 1548965 := bbase (se 4 (by rfl) ⟨145215, by rfl⟩ : syracuseStep 1548965 = 290431) (by norm_num)
theorem B1548989 : Blo 1032607 1548989 := bbase (se 3 (by rfl) ⟨290435, by rfl⟩ : syracuseStep 1548989 = 580871) (by norm_num)
theorem B1745597 : Blo 1032607 1745597 := bbase (se 3 (by rfl) ⟨327299, by rfl⟩ : syracuseStep 1745597 = 654599) (by norm_num)
theorem B1549013 : Blo 1032607 1549013 := bbase (se 7 (by rfl) ⟨18152, by rfl⟩ : syracuseStep 1549013 = 36305) (by norm_num)
theorem B1549037 : Blo 1032607 1549037 := bbase (se 3 (by rfl) ⟨290444, by rfl⟩ : syracuseStep 1549037 = 580889) (by norm_num)
theorem B1549061 : Blo 1032607 1549061 := bbase (se 4 (by rfl) ⟨145224, by rfl⟩ : syracuseStep 1549061 = 290449) (by norm_num)
theorem B1549085 : Blo 1032607 1549085 := bbase (se 3 (by rfl) ⟨290453, by rfl⟩ : syracuseStep 1549085 = 580907) (by norm_num)
theorem B1549109 : Blo 1032607 1549109 := bbase (se 5 (by rfl) ⟨72614, by rfl⟩ : syracuseStep 1549109 = 145229) (by norm_num)
theorem B1745725 : Blo 1032607 1745725 := bbase (se 3 (by rfl) ⟨327323, by rfl⟩ : syracuseStep 1745725 = 654647) (by norm_num)
theorem B1549133 : Blo 1032607 1549133 := bbase (se 3 (by rfl) ⟨290462, by rfl⟩ : syracuseStep 1549133 = 580925) (by norm_num)
theorem B1549157 : Blo 1032607 1549157 := bbase (se 4 (by rfl) ⟨145233, by rfl⟩ : syracuseStep 1549157 = 290467) (by norm_num)
theorem B1549181 : Blo 1032607 1549181 := bbase (se 3 (by rfl) ⟨290471, by rfl⟩ : syracuseStep 1549181 = 580943) (by norm_num)
theorem B1549205 : Blo 1032607 1549205 := bbase (se 6 (by rfl) ⟨36309, by rfl⟩ : syracuseStep 1549205 = 72619) (by norm_num)
theorem B1745813 : Blo 1032607 1745813 := bbase (se 6 (by rfl) ⟨40917, by rfl⟩ : syracuseStep 1745813 = 81835) (by norm_num)
theorem B1549229 : Blo 1032607 1549229 := bbase (se 3 (by rfl) ⟨290480, by rfl⟩ : syracuseStep 1549229 = 580961) (by norm_num)
theorem B1549253 : Blo 1032607 1549253 := bbase (se 4 (by rfl) ⟨145242, by rfl⟩ : syracuseStep 1549253 = 290485) (by norm_num)
theorem B1549277 : Blo 1032607 1549277 := bbase (se 3 (by rfl) ⟨290489, by rfl⟩ : syracuseStep 1549277 = 580979) (by norm_num)
theorem B1549301 : Blo 1032607 1549301 := bbase (se 5 (by rfl) ⟨72623, by rfl⟩ : syracuseStep 1549301 = 145247) (by norm_num)
theorem B1549325 : Blo 1032607 1549325 := bbase (se 3 (by rfl) ⟨290498, by rfl⟩ : syracuseStep 1549325 = 580997) (by norm_num)
theorem B1745941 : Blo 1032607 1745941 := bbase (se 6 (by rfl) ⟨40920, by rfl⟩ : syracuseStep 1745941 = 81841) (by norm_num)
theorem B1549349 : Blo 1032607 1549349 := bbase (se 4 (by rfl) ⟨145251, by rfl⟩ : syracuseStep 1549349 = 290503) (by norm_num)
theorem B1549373 : Blo 1032607 1549373 := bbase (se 3 (by rfl) ⟨290507, by rfl⟩ : syracuseStep 1549373 = 581015) (by norm_num)
theorem B1549397 : Blo 1032607 1549397 := bbase (se 8 (by rfl) ⟨9078, by rfl⟩ : syracuseStep 1549397 = 18157) (by norm_num)
theorem B1549421 : Blo 1032607 1549421 := bbase (se 3 (by rfl) ⟨290516, by rfl⟩ : syracuseStep 1549421 = 581033) (by norm_num)
theorem B1746029 : Blo 1032607 1746029 := bbase (se 3 (by rfl) ⟨327380, by rfl⟩ : syracuseStep 1746029 = 654761) (by norm_num)
theorem B1549445 : Blo 1032607 1549445 := bbase (se 4 (by rfl) ⟨145260, by rfl⟩ : syracuseStep 1549445 = 290521) (by norm_num)
theorem B1549469 : Blo 1032607 1549469 := bbase (se 3 (by rfl) ⟨290525, by rfl⟩ : syracuseStep 1549469 = 581051) (by norm_num)
theorem B1549493 : Blo 1032607 1549493 := bbase (se 5 (by rfl) ⟨72632, by rfl⟩ : syracuseStep 1549493 = 145265) (by norm_num)
theorem B1549517 : Blo 1032607 1549517 := bbase (se 3 (by rfl) ⟨290534, by rfl⟩ : syracuseStep 1549517 = 581069) (by norm_num)
theorem B1549541 : Blo 1032607 1549541 := bbase (se 4 (by rfl) ⟨145269, by rfl⟩ : syracuseStep 1549541 = 290539) (by norm_num)
theorem B1746157 : Blo 1032607 1746157 := bbase (se 3 (by rfl) ⟨327404, by rfl⟩ : syracuseStep 1746157 = 654809) (by norm_num)
theorem B1549565 : Blo 1032607 1549565 := bbase (se 3 (by rfl) ⟨290543, by rfl⟩ : syracuseStep 1549565 = 581087) (by norm_num)
theorem B1549589 : Blo 1032607 1549589 := bbase (se 6 (by rfl) ⟨36318, by rfl⟩ : syracuseStep 1549589 = 72637) (by norm_num)
theorem B1549613 : Blo 1032607 1549613 := bbase (se 3 (by rfl) ⟨290552, by rfl⟩ : syracuseStep 1549613 = 581105) (by norm_num)
theorem B6628661 : Blo 1032607 6628661 := bbase (se 5 (by rfl) ⟨310718, by rfl⟩ : syracuseStep 6628661 = 621437) (by norm_num)
theorem B1549637 : Blo 1032607 1549637 := bbase (se 4 (by rfl) ⟨145278, by rfl⟩ : syracuseStep 1549637 = 290557) (by norm_num)
theorem B1746245 : Blo 1032607 1746245 := bbase (se 4 (by rfl) ⟨163710, by rfl⟩ : syracuseStep 1746245 = 327421) (by norm_num)
theorem B1549661 : Blo 1032607 1549661 := bbase (se 3 (by rfl) ⟨290561, by rfl⟩ : syracuseStep 1549661 = 581123) (by norm_num)
theorem B1549685 : Blo 1032607 1549685 := bbase (se 5 (by rfl) ⟨72641, by rfl⟩ : syracuseStep 1549685 = 145283) (by norm_num)
theorem B1549709 : Blo 1032607 1549709 := bbase (se 3 (by rfl) ⟨290570, by rfl⟩ : syracuseStep 1549709 = 581141) (by norm_num)
theorem B1549733 : Blo 1032607 1549733 := bbase (se 4 (by rfl) ⟨145287, by rfl⟩ : syracuseStep 1549733 = 290575) (by norm_num)
theorem B1549757 : Blo 1032607 1549757 := bbase (se 3 (by rfl) ⟨290579, by rfl⟩ : syracuseStep 1549757 = 581159) (by norm_num)
theorem B1746373 : Blo 1032607 1746373 := bbase (se 4 (by rfl) ⟨163722, by rfl⟩ : syracuseStep 1746373 = 327445) (by norm_num)
theorem B1549781 : Blo 1032607 1549781 := bbase (se 7 (by rfl) ⟨18161, by rfl⟩ : syracuseStep 1549781 = 36323) (by norm_num)
theorem B1549805 : Blo 1032607 1549805 := bbase (se 3 (by rfl) ⟨290588, by rfl⟩ : syracuseStep 1549805 = 581177) (by norm_num)
theorem B1549829 : Blo 1032607 1549829 := bbase (se 4 (by rfl) ⟨145296, by rfl⟩ : syracuseStep 1549829 = 290593) (by norm_num)
theorem B1549853 : Blo 1032607 1549853 := bbase (se 3 (by rfl) ⟨290597, by rfl⟩ : syracuseStep 1549853 = 581195) (by norm_num)
theorem B1746461 : Blo 1032607 1746461 := bbase (se 3 (by rfl) ⟨327461, by rfl⟩ : syracuseStep 1746461 = 654923) (by norm_num)
theorem B1549877 : Blo 1032607 1549877 := bbase (se 5 (by rfl) ⟨72650, by rfl⟩ : syracuseStep 1549877 = 145301) (by norm_num)
theorem B1549901 : Blo 1032607 1549901 := bbase (se 3 (by rfl) ⟨290606, by rfl⟩ : syracuseStep 1549901 = 581213) (by norm_num)
theorem B1549925 : Blo 1032607 1549925 := bbase (se 4 (by rfl) ⟨145305, by rfl⟩ : syracuseStep 1549925 = 290611) (by norm_num)
theorem B1549949 : Blo 1032607 1549949 := bbase (se 3 (by rfl) ⟨290615, by rfl⟩ : syracuseStep 1549949 = 581231) (by norm_num)
theorem B1549973 : Blo 1032607 1549973 := bbase (se 6 (by rfl) ⟨36327, by rfl⟩ : syracuseStep 1549973 = 72655) (by norm_num)
theorem B1746589 : Blo 1032607 1746589 := bbase (se 3 (by rfl) ⟨327485, by rfl⟩ : syracuseStep 1746589 = 654971) (by norm_num)
theorem B1549997 : Blo 1032607 1549997 := bbase (se 3 (by rfl) ⟨290624, by rfl⟩ : syracuseStep 1549997 = 581249) (by norm_num)
theorem B1550021 : Blo 1032607 1550021 := bbase (se 4 (by rfl) ⟨145314, by rfl⟩ : syracuseStep 1550021 = 290629) (by norm_num)
theorem B7186133 : Blo 1032607 7186133 := bbase (se 7 (by rfl) ⟨84212, by rfl⟩ : syracuseStep 7186133 = 168425) (by norm_num)
theorem B1550045 : Blo 1032607 1550045 := bbase (se 3 (by rfl) ⟨290633, by rfl⟩ : syracuseStep 1550045 = 581267) (by norm_num)
theorem B1550069 : Blo 1032607 1550069 := bbase (se 5 (by rfl) ⟨72659, by rfl⟩ : syracuseStep 1550069 = 145319) (by norm_num)
theorem B1746677 : Blo 1032607 1746677 := bbase (se 5 (by rfl) ⟨81875, by rfl⟩ : syracuseStep 1746677 = 163751) (by norm_num)
theorem B1550093 : Blo 1032607 1550093 := bbase (se 3 (by rfl) ⟨290642, by rfl⟩ : syracuseStep 1550093 = 581285) (by norm_num)
theorem B1550117 : Blo 1032607 1550117 := bbase (se 4 (by rfl) ⟨145323, by rfl⟩ : syracuseStep 1550117 = 290647) (by norm_num)
theorem B1550141 : Blo 1032607 1550141 := bbase (se 3 (by rfl) ⟨290651, by rfl⟩ : syracuseStep 1550141 = 581303) (by norm_num)
theorem B1550165 : Blo 1032607 1550165 := bbase (se 9 (by rfl) ⟨4541, by rfl⟩ : syracuseStep 1550165 = 9083) (by norm_num)
theorem B1550189 : Blo 1032607 1550189 := bbase (se 3 (by rfl) ⟨290660, by rfl⟩ : syracuseStep 1550189 = 581321) (by norm_num)
theorem B1746805 : Blo 1032607 1746805 := bbase (se 5 (by rfl) ⟨81881, by rfl⟩ : syracuseStep 1746805 = 163763) (by norm_num)
theorem B1550213 : Blo 1032607 1550213 := bbase (se 4 (by rfl) ⟨145332, by rfl⟩ : syracuseStep 1550213 = 290665) (by norm_num)
theorem B8398741 : Blo 1032607 8398741 := bbase (se 6 (by rfl) ⟨196845, by rfl⟩ : syracuseStep 8398741 = 393691) (by norm_num)
theorem B1550237 : Blo 1032607 1550237 := bbase (se 3 (by rfl) ⟨290669, by rfl⟩ : syracuseStep 1550237 = 581339) (by norm_num)
theorem B1550261 : Blo 1032607 1550261 := bbase (se 5 (by rfl) ⟨72668, by rfl⟩ : syracuseStep 1550261 = 145337) (by norm_num)
theorem B1550285 : Blo 1032607 1550285 := bbase (se 3 (by rfl) ⟨290678, by rfl⟩ : syracuseStep 1550285 = 581357) (by norm_num)
theorem B1746893 : Blo 1032607 1746893 := bbase (se 3 (by rfl) ⟨327542, by rfl⟩ : syracuseStep 1746893 = 655085) (by norm_num)
theorem B1550309 : Blo 1032607 1550309 := bbase (se 4 (by rfl) ⟨145341, by rfl⟩ : syracuseStep 1550309 = 290683) (by norm_num)
theorem B1550333 : Blo 1032607 1550333 := bbase (se 3 (by rfl) ⟨290687, by rfl⟩ : syracuseStep 1550333 = 581375) (by norm_num)
theorem B1550357 : Blo 1032607 1550357 := bbase (se 6 (by rfl) ⟨36336, by rfl⟩ : syracuseStep 1550357 = 72673) (by norm_num)
theorem B1550381 : Blo 1032607 1550381 := bbase (se 3 (by rfl) ⟨290696, by rfl⟩ : syracuseStep 1550381 = 581393) (by norm_num)
theorem B1550405 : Blo 1032607 1550405 := bbase (se 4 (by rfl) ⟨145350, by rfl⟩ : syracuseStep 1550405 = 290701) (by norm_num)
theorem B1747021 : Blo 1032607 1747021 := bbase (se 3 (by rfl) ⟨327566, by rfl⟩ : syracuseStep 1747021 = 655133) (by norm_num)
theorem B1550429 : Blo 1032607 1550429 := bbase (se 3 (by rfl) ⟨290705, by rfl⟩ : syracuseStep 1550429 = 581411) (by norm_num)
theorem B1550453 : Blo 1032607 1550453 := bbase (se 5 (by rfl) ⟨72677, by rfl⟩ : syracuseStep 1550453 = 145355) (by norm_num)
theorem B2205829 : Blo 1032607 2205829 := bbase (se 4 (by rfl) ⟨206796, by rfl⟩ : syracuseStep 2205829 = 413593) (by norm_num)
theorem B1550477 : Blo 1032607 1550477 := bbase (se 3 (by rfl) ⟨290714, by rfl⟩ : syracuseStep 1550477 = 581429) (by norm_num)
theorem B3319957 : Blo 1032607 3319957 := bbase (se 6 (by rfl) ⟨77811, by rfl⟩ : syracuseStep 3319957 = 155623) (by norm_num)
theorem B1550501 : Blo 1032607 1550501 := bbase (se 4 (by rfl) ⟨145359, by rfl⟩ : syracuseStep 1550501 = 290719) (by norm_num)
theorem B1747109 : Blo 1032607 1747109 := bbase (se 4 (by rfl) ⟨163791, by rfl⟩ : syracuseStep 1747109 = 327583) (by norm_num)
theorem B1550525 : Blo 1032607 1550525 := bbase (se 3 (by rfl) ⟨290723, by rfl⟩ : syracuseStep 1550525 = 581447) (by norm_num)
theorem B1550549 : Blo 1032607 1550549 := bbase (se 7 (by rfl) ⟨18170, by rfl⟩ : syracuseStep 1550549 = 36341) (by norm_num)
theorem B3320021 : Blo 1032607 3320021 := bbase (se 7 (by rfl) ⟨38906, by rfl⟩ : syracuseStep 3320021 = 77813) (by norm_num)
theorem B1550573 : Blo 1032607 1550573 := bbase (se 3 (by rfl) ⟨290732, by rfl⟩ : syracuseStep 1550573 = 581465) (by norm_num)
theorem B2205949 : Blo 1032607 2205949 := bbase (se 3 (by rfl) ⟨413615, by rfl⟩ : syracuseStep 2205949 = 827231) (by norm_num)
theorem B1550597 : Blo 1032607 1550597 := bbase (se 4 (by rfl) ⟨145368, by rfl⟩ : syracuseStep 1550597 = 290737) (by norm_num)
theorem B1550621 : Blo 1032607 1550621 := bbase (se 3 (by rfl) ⟨290741, by rfl⟩ : syracuseStep 1550621 = 581483) (by norm_num)
theorem B1747237 : Blo 1032607 1747237 := bbase (se 4 (by rfl) ⟨163803, by rfl⟩ : syracuseStep 1747237 = 327607) (by norm_num)
theorem B1550645 : Blo 1032607 1550645 := bbase (se 5 (by rfl) ⟨72686, by rfl⟩ : syracuseStep 1550645 = 145373) (by norm_num)
theorem B1550669 : Blo 1032607 1550669 := bbase (se 3 (by rfl) ⟨290750, by rfl⟩ : syracuseStep 1550669 = 581501) (by norm_num)
theorem B1091917 : Blo 1032607 1091917 := bbase (se 3 (by rfl) ⟨204734, by rfl⟩ : syracuseStep 1091917 = 409469) (by norm_num)
theorem B1550693 : Blo 1032607 1550693 := bbase (se 4 (by rfl) ⟨145377, by rfl⟩ : syracuseStep 1550693 = 290755) (by norm_num)
theorem B1550717 : Blo 1032607 1550717 := bbase (se 3 (by rfl) ⟨290759, by rfl⟩ : syracuseStep 1550717 = 581519) (by norm_num)
theorem B1747325 : Blo 1032607 1747325 := bbase (se 3 (by rfl) ⟨327623, by rfl⟩ : syracuseStep 1747325 = 655247) (by norm_num)
theorem B1550741 : Blo 1032607 1550741 := bbase (se 6 (by rfl) ⟨36345, by rfl⟩ : syracuseStep 1550741 = 72691) (by norm_num)
theorem B1550765 : Blo 1032607 1550765 := bbase (se 3 (by rfl) ⟨290768, by rfl⟩ : syracuseStep 1550765 = 581537) (by norm_num)
theorem B1550789 : Blo 1032607 1550789 := bbase (se 4 (by rfl) ⟨145386, by rfl⟩ : syracuseStep 1550789 = 290773) (by norm_num)
theorem B1550813 : Blo 1032607 1550813 := bbase (se 3 (by rfl) ⟨290777, by rfl⟩ : syracuseStep 1550813 = 581555) (by norm_num)
theorem B1550837 : Blo 1032607 1550837 := bbase (se 5 (by rfl) ⟨72695, by rfl⟩ : syracuseStep 1550837 = 145391) (by norm_num)
theorem B2206205 : Blo 1032607 2206205 := bbase (se 3 (by rfl) ⟨413663, by rfl⟩ : syracuseStep 2206205 = 827327) (by norm_num)
theorem B1747453 : Blo 1032607 1747453 := bbase (se 3 (by rfl) ⟨327647, by rfl⟩ : syracuseStep 1747453 = 655295) (by norm_num)
theorem B1550861 : Blo 1032607 1550861 := bbase (se 3 (by rfl) ⟨290786, by rfl⟩ : syracuseStep 1550861 = 581573) (by norm_num)
theorem B1550885 : Blo 1032607 1550885 := bbase (se 4 (by rfl) ⟨145395, by rfl⟩ : syracuseStep 1550885 = 290791) (by norm_num)
theorem B1681957 : Blo 1032607 1681957 := bbase (se 4 (by rfl) ⟨157683, by rfl⟩ : syracuseStep 1681957 = 315367) (by norm_num)
theorem B1550909 : Blo 1032607 1550909 := bbase (se 3 (by rfl) ⟨290795, by rfl⟩ : syracuseStep 1550909 = 581591) (by norm_num)
theorem B1550933 : Blo 1032607 1550933 := bbase (se 8 (by rfl) ⟨9087, by rfl⟩ : syracuseStep 1550933 = 18175) (by norm_num)
theorem B1747541 : Blo 1032607 1747541 := bbase (se 8 (by rfl) ⟨10239, by rfl⟩ : syracuseStep 1747541 = 20479) (by norm_num)
theorem B1550957 : Blo 1032607 1550957 := bbase (se 3 (by rfl) ⟨290804, by rfl⟩ : syracuseStep 1550957 = 581609) (by norm_num)
theorem B1550981 : Blo 1032607 1550981 := bbase (se 4 (by rfl) ⟨145404, by rfl⟩ : syracuseStep 1550981 = 290809) (by norm_num)
theorem B1551005 : Blo 1032607 1551005 := bbase (se 3 (by rfl) ⟨290813, by rfl⟩ : syracuseStep 1551005 = 581627) (by norm_num)
theorem B1551029 : Blo 1032607 1551029 := bbase (se 5 (by rfl) ⟨72704, by rfl⟩ : syracuseStep 1551029 = 145409) (by norm_num)
theorem B1551053 : Blo 1032607 1551053 := bbase (se 3 (by rfl) ⟨290822, by rfl⟩ : syracuseStep 1551053 = 581645) (by norm_num)
theorem B1747669 : Blo 1032607 1747669 := bbase (se 7 (by rfl) ⟨20480, by rfl⟩ : syracuseStep 1747669 = 40961) (by norm_num)
theorem B1551077 : Blo 1032607 1551077 := bbase (se 4 (by rfl) ⟨145413, by rfl⟩ : syracuseStep 1551077 = 290827) (by norm_num)
theorem B1551101 : Blo 1032607 1551101 := bbase (se 3 (by rfl) ⟨290831, by rfl⟩ : syracuseStep 1551101 = 581663) (by norm_num)
theorem B7842581 : Blo 1032607 7842581 := bbase (se 6 (by rfl) ⟨183810, by rfl⟩ : syracuseStep 7842581 = 367621) (by norm_num)
theorem B1551125 : Blo 1032607 1551125 := bbase (se 6 (by rfl) ⟨36354, by rfl⟩ : syracuseStep 1551125 = 72709) (by norm_num)
theorem B1551149 : Blo 1032607 1551149 := bbase (se 3 (by rfl) ⟨290840, by rfl⟩ : syracuseStep 1551149 = 581681) (by norm_num)
theorem B1747757 : Blo 1032607 1747757 := bbase (se 3 (by rfl) ⟨327704, by rfl⟩ : syracuseStep 1747757 = 655409) (by norm_num)
theorem B1551173 : Blo 1032607 1551173 := bbase (se 4 (by rfl) ⟨145422, by rfl⟩ : syracuseStep 1551173 = 290845) (by norm_num)
theorem B1551197 : Blo 1032607 1551197 := bbase (se 3 (by rfl) ⟨290849, by rfl⟩ : syracuseStep 1551197 = 581699) (by norm_num)
theorem B1551221 : Blo 1032607 1551221 := bbase (se 5 (by rfl) ⟨72713, by rfl⟩ : syracuseStep 1551221 = 145427) (by norm_num)
theorem B1551245 : Blo 1032607 1551245 := bbase (se 3 (by rfl) ⟨290858, by rfl⟩ : syracuseStep 1551245 = 581717) (by norm_num)
theorem B1551269 : Blo 1032607 1551269 := bbase (se 4 (by rfl) ⟨145431, by rfl⟩ : syracuseStep 1551269 = 290863) (by norm_num)
theorem B1747885 : Blo 1032607 1747885 := bbase (se 3 (by rfl) ⟨327728, by rfl⟩ : syracuseStep 1747885 = 655457) (by norm_num)
theorem B1551293 : Blo 1032607 1551293 := bbase (se 3 (by rfl) ⟨290867, by rfl⟩ : syracuseStep 1551293 = 581735) (by norm_num)
theorem B1551317 : Blo 1032607 1551317 := bbase (se 7 (by rfl) ⟨18179, by rfl⟩ : syracuseStep 1551317 = 36359) (by norm_num)
theorem B1551341 : Blo 1032607 1551341 := bbase (se 3 (by rfl) ⟨290876, by rfl⟩ : syracuseStep 1551341 = 581753) (by norm_num)
theorem B1551365 : Blo 1032607 1551365 := bbase (se 4 (by rfl) ⟨145440, by rfl⟩ : syracuseStep 1551365 = 290881) (by norm_num)
theorem B1747973 : Blo 1032607 1747973 := bbase (se 4 (by rfl) ⟨163872, by rfl⟩ : syracuseStep 1747973 = 327745) (by norm_num)
theorem B1551389 : Blo 1032607 1551389 := bbase (se 3 (by rfl) ⟨290885, by rfl⟩ : syracuseStep 1551389 = 581771) (by norm_num)
theorem B1551413 : Blo 1032607 1551413 := bbase (se 5 (by rfl) ⟨72722, by rfl⟩ : syracuseStep 1551413 = 145445) (by norm_num)
theorem B1551437 : Blo 1032607 1551437 := bbase (se 3 (by rfl) ⟨290894, by rfl⟩ : syracuseStep 1551437 = 581789) (by norm_num)
theorem B1551461 : Blo 1032607 1551461 := bbase (se 4 (by rfl) ⟨145449, by rfl⟩ : syracuseStep 1551461 = 290899) (by norm_num)
theorem B1551485 : Blo 1032607 1551485 := bbase (se 3 (by rfl) ⟨290903, by rfl⟩ : syracuseStep 1551485 = 581807) (by norm_num)
theorem B1748101 : Blo 1032607 1748101 := bbase (se 4 (by rfl) ⟨163884, by rfl⟩ : syracuseStep 1748101 = 327769) (by norm_num)
theorem B1551509 : Blo 1032607 1551509 := bbase (se 6 (by rfl) ⟨36363, by rfl⟩ : syracuseStep 1551509 = 72727) (by norm_num)
theorem B5680277 : Blo 1032607 5680277 := bbase (se 6 (by rfl) ⟨133131, by rfl⟩ : syracuseStep 5680277 = 266263) (by norm_num)
theorem B1551533 : Blo 1032607 1551533 := bbase (se 3 (by rfl) ⟨290912, by rfl⟩ : syracuseStep 1551533 = 581825) (by norm_num)
theorem B1551557 : Blo 1032607 1551557 := bbase (se 4 (by rfl) ⟨145458, by rfl⟩ : syracuseStep 1551557 = 290917) (by norm_num)
theorem B1551581 : Blo 1032607 1551581 := bbase (se 3 (by rfl) ⟨290921, by rfl⟩ : syracuseStep 1551581 = 581843) (by norm_num)
theorem B1748189 : Blo 1032607 1748189 := bbase (se 3 (by rfl) ⟨327785, by rfl⟩ : syracuseStep 1748189 = 655571) (by norm_num)
theorem B1551605 : Blo 1032607 1551605 := bbase (se 5 (by rfl) ⟨72731, by rfl⟩ : syracuseStep 1551605 = 145463) (by norm_num)
theorem B1551629 : Blo 1032607 1551629 := bbase (se 3 (by rfl) ⟨290930, by rfl⟩ : syracuseStep 1551629 = 581861) (by norm_num)
theorem B1551653 : Blo 1032607 1551653 := bbase (se 4 (by rfl) ⟨145467, by rfl⟩ : syracuseStep 1551653 = 290935) (by norm_num)
theorem B1551677 : Blo 1032607 1551677 := bbase (se 3 (by rfl) ⟨290939, by rfl⟩ : syracuseStep 1551677 = 581879) (by norm_num)
theorem B1551701 : Blo 1032607 1551701 := bbase (se 11 (by rfl) ⟨1136, by rfl⟩ : syracuseStep 1551701 = 2273) (by norm_num)
theorem B5680469 : Blo 1032607 5680469 := bbase (se 11 (by rfl) ⟨4160, by rfl⟩ : syracuseStep 5680469 = 8321) (by norm_num)
theorem B1748317 : Blo 1032607 1748317 := bbase (se 3 (by rfl) ⟨327809, by rfl⟩ : syracuseStep 1748317 = 655619) (by norm_num)
theorem B1551725 : Blo 1032607 1551725 := bbase (se 3 (by rfl) ⟨290948, by rfl⟩ : syracuseStep 1551725 = 581897) (by norm_num)
theorem B2207093 : Blo 1032607 2207093 := bbase (se 5 (by rfl) ⟨103457, by rfl⟩ : syracuseStep 2207093 = 206915) (by norm_num)
theorem B1551749 : Blo 1032607 1551749 := bbase (se 4 (by rfl) ⟨145476, by rfl⟩ : syracuseStep 1551749 = 290953) (by norm_num)
theorem B1551773 : Blo 1032607 1551773 := bbase (se 3 (by rfl) ⟨290957, by rfl⟩ : syracuseStep 1551773 = 581915) (by norm_num)
theorem B1551797 : Blo 1032607 1551797 := bbase (se 5 (by rfl) ⟨72740, by rfl⟩ : syracuseStep 1551797 = 145481) (by norm_num)
theorem B1748405 : Blo 1032607 1748405 := bbase (se 5 (by rfl) ⟨81956, by rfl⟩ : syracuseStep 1748405 = 163913) (by norm_num)
theorem B1551821 : Blo 1032607 1551821 := bbase (se 3 (by rfl) ⟨290966, by rfl⟩ : syracuseStep 1551821 = 581933) (by norm_num)
theorem B1551845 : Blo 1032607 1551845 := bbase (se 4 (by rfl) ⟨145485, by rfl⟩ : syracuseStep 1551845 = 290971) (by norm_num)
theorem B1551869 : Blo 1032607 1551869 := bbase (se 3 (by rfl) ⟨290975, by rfl⟩ : syracuseStep 1551869 = 581951) (by norm_num)
theorem B1551893 : Blo 1032607 1551893 := bbase (se 6 (by rfl) ⟨36372, by rfl⟩ : syracuseStep 1551893 = 72745) (by norm_num)
theorem B1551917 : Blo 1032607 1551917 := bbase (se 3 (by rfl) ⟨290984, by rfl⟩ : syracuseStep 1551917 = 581969) (by norm_num)
theorem B1748533 : Blo 1032607 1748533 := bbase (se 5 (by rfl) ⟨81962, by rfl⟩ : syracuseStep 1748533 = 163925) (by norm_num)
theorem B1551941 : Blo 1032607 1551941 := bbase (se 4 (by rfl) ⟨145494, by rfl⟩ : syracuseStep 1551941 = 290989) (by norm_num)
theorem B1551965 : Blo 1032607 1551965 := bbase (se 3 (by rfl) ⟨290993, by rfl⟩ : syracuseStep 1551965 = 581987) (by norm_num)
theorem B2207333 : Blo 1032607 2207333 := bbase (se 4 (by rfl) ⟨206937, by rfl⟩ : syracuseStep 2207333 = 413875) (by norm_num)
theorem B1551989 : Blo 1032607 1551989 := bbase (se 5 (by rfl) ⟨72749, by rfl⟩ : syracuseStep 1551989 = 145499) (by norm_num)
theorem B1552013 : Blo 1032607 1552013 := bbase (se 3 (by rfl) ⟨291002, by rfl⟩ : syracuseStep 1552013 = 582005) (by norm_num)
theorem B1748621 : Blo 1032607 1748621 := bbase (se 3 (by rfl) ⟨327866, by rfl⟩ : syracuseStep 1748621 = 655733) (by norm_num)
theorem B1552037 : Blo 1032607 1552037 := bbase (se 4 (by rfl) ⟨145503, by rfl⟩ : syracuseStep 1552037 = 291007) (by norm_num)
theorem B1552061 : Blo 1032607 1552061 := bbase (se 3 (by rfl) ⟨291011, by rfl⟩ : syracuseStep 1552061 = 582023) (by norm_num)
theorem B7450325 : Blo 1032607 7450325 := bbase (se 7 (by rfl) ⟨87308, by rfl⟩ : syracuseStep 7450325 = 174617) (by norm_num)
theorem B1552085 : Blo 1032607 1552085 := bbase (se 7 (by rfl) ⟨18188, by rfl⟩ : syracuseStep 1552085 = 36377) (by norm_num)
theorem B1552109 : Blo 1032607 1552109 := bbase (se 3 (by rfl) ⟨291020, by rfl⟩ : syracuseStep 1552109 = 582041) (by norm_num)
theorem B3485429 : Blo 1032607 3485429 := bbase (se 5 (by rfl) ⟨163379, by rfl⟩ : syracuseStep 3485429 = 326759) (by norm_num)
theorem B1552133 : Blo 1032607 1552133 := bbase (se 4 (by rfl) ⟨145512, by rfl⟩ : syracuseStep 1552133 = 291025) (by norm_num)
theorem B1748749 : Blo 1032607 1748749 := bbase (se 3 (by rfl) ⟨327890, by rfl⟩ : syracuseStep 1748749 = 655781) (by norm_num)
theorem B1552157 : Blo 1032607 1552157 := bbase (se 3 (by rfl) ⟨291029, by rfl⟩ : syracuseStep 1552157 = 582059) (by norm_num)
theorem B1552181 : Blo 1032607 1552181 := bbase (se 5 (by rfl) ⟨72758, by rfl⟩ : syracuseStep 1552181 = 145517) (by norm_num)
theorem B1552205 : Blo 1032607 1552205 := bbase (se 3 (by rfl) ⟨291038, by rfl⟩ : syracuseStep 1552205 = 582077) (by norm_num)
theorem B1552229 : Blo 1032607 1552229 := bbase (se 4 (by rfl) ⟨145521, by rfl⟩ : syracuseStep 1552229 = 291043) (by norm_num)
theorem B1748837 : Blo 1032607 1748837 := bbase (se 4 (by rfl) ⟨163953, by rfl⟩ : syracuseStep 1748837 = 327907) (by norm_num)
theorem B1552253 : Blo 1032607 1552253 := bbase (se 3 (by rfl) ⟨291047, by rfl⟩ : syracuseStep 1552253 = 582095) (by norm_num)
theorem B1093505 : Blo 1032607 1093505 := bbase (se 2 (by rfl) ⟨410064, by rfl⟩ : syracuseStep 1093505 = 820129) (by norm_num)
theorem B1552277 : Blo 1032607 1552277 := bbase (se 6 (by rfl) ⟨36381, by rfl⟩ : syracuseStep 1552277 = 72763) (by norm_num)
theorem B1552301 : Blo 1032607 1552301 := bbase (se 3 (by rfl) ⟨291056, by rfl⟩ : syracuseStep 1552301 = 582113) (by norm_num)
theorem B1552325 : Blo 1032607 1552325 := bbase (se 4 (by rfl) ⟨145530, by rfl⟩ : syracuseStep 1552325 = 291061) (by norm_num)
theorem B1552349 : Blo 1032607 1552349 := bbase (se 3 (by rfl) ⟨291065, by rfl⟩ : syracuseStep 1552349 = 582131) (by norm_num)
theorem B1748965 : Blo 1032607 1748965 := bbase (se 4 (by rfl) ⟨163965, by rfl⟩ : syracuseStep 1748965 = 327931) (by norm_num)
theorem B1552373 : Blo 1032607 1552373 := bbase (se 5 (by rfl) ⟨72767, by rfl⟩ : syracuseStep 1552373 = 145535) (by norm_num)
theorem B1552397 : Blo 1032607 1552397 := bbase (se 3 (by rfl) ⟨291074, by rfl⟩ : syracuseStep 1552397 = 582149) (by norm_num)
theorem B1552421 : Blo 1032607 1552421 := bbase (se 4 (by rfl) ⟨145539, by rfl⟩ : syracuseStep 1552421 = 291079) (by norm_num)
theorem B1552445 : Blo 1032607 1552445 := bbase (se 3 (by rfl) ⟨291083, by rfl⟩ : syracuseStep 1552445 = 582167) (by norm_num)
theorem B1749053 : Blo 1032607 1749053 := bbase (se 3 (by rfl) ⟨327947, by rfl⟩ : syracuseStep 1749053 = 655895) (by norm_num)
theorem B1552469 : Blo 1032607 1552469 := bbase (se 8 (by rfl) ⟨9096, by rfl⟩ : syracuseStep 1552469 = 18193) (by norm_num)
theorem B2207837 : Blo 1032607 2207837 := bbase (se 3 (by rfl) ⟨413969, by rfl⟩ : syracuseStep 2207837 = 827939) (by norm_num)
theorem B2207845 : Blo 1032607 2207845 := bbase (se 4 (by rfl) ⟨206985, by rfl⟩ : syracuseStep 2207845 = 413971) (by norm_num)
theorem B2797669 : Blo 1032607 2797669 := bbase (se 4 (by rfl) ⟨262281, by rfl⟩ : syracuseStep 2797669 = 524563) (by norm_num)
theorem B1552493 : Blo 1032607 1552493 := bbase (se 3 (by rfl) ⟨291092, by rfl⟩ : syracuseStep 1552493 = 582185) (by norm_num)
theorem B1552517 : Blo 1032607 1552517 := bbase (se 4 (by rfl) ⟨145548, by rfl⟩ : syracuseStep 1552517 = 291097) (by norm_num)
theorem B1552541 : Blo 1032607 1552541 := bbase (se 3 (by rfl) ⟨291101, by rfl⟩ : syracuseStep 1552541 = 582203) (by norm_num)
theorem B3485861 : Blo 1032607 3485861 := bbase (se 4 (by rfl) ⟨326799, by rfl⟩ : syracuseStep 3485861 = 653599) (by norm_num)
theorem B1552565 : Blo 1032607 1552565 := bbase (se 5 (by rfl) ⟨72776, by rfl⟩ : syracuseStep 1552565 = 145553) (by norm_num)
theorem B1749181 : Blo 1032607 1749181 := bbase (se 3 (by rfl) ⟨327971, by rfl⟩ : syracuseStep 1749181 = 655943) (by norm_num)
theorem B1552589 : Blo 1032607 1552589 := bbase (se 3 (by rfl) ⟨291110, by rfl⟩ : syracuseStep 1552589 = 582221) (by norm_num)
theorem B1552613 : Blo 1032607 1552613 := bbase (se 4 (by rfl) ⟨145557, by rfl⟩ : syracuseStep 1552613 = 291115) (by norm_num)
theorem B1552637 : Blo 1032607 1552637 := bbase (se 3 (by rfl) ⟨291119, by rfl⟩ : syracuseStep 1552637 = 582239) (by norm_num)
theorem B1913101 : Blo 1032607 1913101 := bbase (se 3 (by rfl) ⟨358706, by rfl⟩ : syracuseStep 1913101 = 717413) (by norm_num)
theorem B1552661 : Blo 1032607 1552661 := bbase (se 6 (by rfl) ⟨36390, by rfl⟩ : syracuseStep 1552661 = 72781) (by norm_num)
theorem B1749269 : Blo 1032607 1749269 := bbase (se 6 (by rfl) ⟨40998, by rfl⟩ : syracuseStep 1749269 = 81997) (by norm_num)
theorem B1552685 : Blo 1032607 1552685 := bbase (se 3 (by rfl) ⟨291128, by rfl⟩ : syracuseStep 1552685 = 582257) (by norm_num)
theorem B1552709 : Blo 1032607 1552709 := bbase (se 4 (by rfl) ⟨145566, by rfl⟩ : syracuseStep 1552709 = 291133) (by norm_num)
theorem B1552733 : Blo 1032607 1552733 := bbase (se 3 (by rfl) ⟨291137, by rfl⟩ : syracuseStep 1552733 = 582275) (by norm_num)
theorem B1552757 : Blo 1032607 1552757 := bbase (se 5 (by rfl) ⟨72785, by rfl⟩ : syracuseStep 1552757 = 145571) (by norm_num)
theorem B1552781 : Blo 1032607 1552781 := bbase (se 3 (by rfl) ⟨291146, by rfl⟩ : syracuseStep 1552781 = 582293) (by norm_num)
theorem B1552805 : Blo 1032607 1552805 := bbase (se 4 (by rfl) ⟨145575, by rfl⟩ : syracuseStep 1552805 = 291151) (by norm_num)
theorem B1552829 : Blo 1032607 1552829 := bbase (se 3 (by rfl) ⟨291155, by rfl⟩ : syracuseStep 1552829 = 582311) (by norm_num)
theorem B1552853 : Blo 1032607 1552853 := bbase (se 7 (by rfl) ⟨18197, by rfl⟩ : syracuseStep 1552853 = 36395) (by norm_num)
theorem B1552877 : Blo 1032607 1552877 := bbase (se 3 (by rfl) ⟨291164, by rfl⟩ : syracuseStep 1552877 = 582329) (by norm_num)
theorem B1552901 : Blo 1032607 1552901 := bbase (se 4 (by rfl) ⟨145584, by rfl⟩ : syracuseStep 1552901 = 291169) (by norm_num)
theorem B2241037 : Blo 1032607 2241037 := bbase (se 3 (by rfl) ⟨420194, by rfl⟩ : syracuseStep 2241037 = 840389) (by norm_num)
theorem B1552925 : Blo 1032607 1552925 := bbase (se 3 (by rfl) ⟨291173, by rfl⟩ : syracuseStep 1552925 = 582347) (by norm_num)
theorem B1552949 : Blo 1032607 1552949 := bbase (se 5 (by rfl) ⟨72794, by rfl⟩ : syracuseStep 1552949 = 145589) (by norm_num)
theorem B1552973 : Blo 1032607 1552973 := bbase (se 3 (by rfl) ⟨291182, by rfl⟩ : syracuseStep 1552973 = 582365) (by norm_num)
theorem B3486293 : Blo 1032607 3486293 := bbase (se 8 (by rfl) ⟨20427, by rfl⟩ : syracuseStep 3486293 = 40855) (by norm_num)
theorem B1552997 : Blo 1032607 1552997 := bbase (se 4 (by rfl) ⟨145593, by rfl⟩ : syracuseStep 1552997 = 291187) (by norm_num)
theorem B1553021 : Blo 1032607 1553021 := bbase (se 3 (by rfl) ⟨291191, by rfl⟩ : syracuseStep 1553021 = 582383) (by norm_num)
theorem B1553045 : Blo 1032607 1553045 := bbase (se 6 (by rfl) ⟨36399, by rfl⟩ : syracuseStep 1553045 = 72799) (by norm_num)
theorem B1553069 : Blo 1032607 1553069 := bbase (se 3 (by rfl) ⟨291200, by rfl⟩ : syracuseStep 1553069 = 582401) (by norm_num)
theorem B1553093 : Blo 1032607 1553093 := bbase (se 4 (by rfl) ⟨145602, by rfl⟩ : syracuseStep 1553093 = 291205) (by norm_num)
theorem B1553117 : Blo 1032607 1553117 := bbase (se 3 (by rfl) ⟨291209, by rfl⟩ : syracuseStep 1553117 = 582419) (by norm_num)
theorem B1553141 : Blo 1032607 1553141 := bbase (se 5 (by rfl) ⟨72803, by rfl⟩ : syracuseStep 1553141 = 145607) (by norm_num)
theorem B1553165 : Blo 1032607 1553165 := bbase (se 3 (by rfl) ⟨291218, by rfl⟩ : syracuseStep 1553165 = 582437) (by norm_num)
theorem B1553189 : Blo 1032607 1553189 := bbase (se 4 (by rfl) ⟨145611, by rfl⟩ : syracuseStep 1553189 = 291223) (by norm_num)
theorem B1553213 : Blo 1032607 1553213 := bbase (se 3 (by rfl) ⟨291227, by rfl⟩ : syracuseStep 1553213 = 582455) (by norm_num)
theorem B1553237 : Blo 1032607 1553237 := bbase (se 9 (by rfl) ⟨4550, by rfl⟩ : syracuseStep 1553237 = 9101) (by norm_num)
theorem B1553261 : Blo 1032607 1553261 := bbase (se 3 (by rfl) ⟨291236, by rfl⟩ : syracuseStep 1553261 = 582473) (by norm_num)
theorem B1553285 : Blo 1032607 1553285 := bbase (se 4 (by rfl) ⟨145620, by rfl⟩ : syracuseStep 1553285 = 291241) (by norm_num)
theorem B1553309 : Blo 1032607 1553309 := bbase (se 3 (by rfl) ⟨291245, by rfl⟩ : syracuseStep 1553309 = 582491) (by norm_num)
theorem B1553333 : Blo 1032607 1553333 := bbase (se 5 (by rfl) ⟨72812, by rfl⟩ : syracuseStep 1553333 = 145625) (by norm_num)
theorem B1553357 : Blo 1032607 1553357 := bbase (se 3 (by rfl) ⟨291254, by rfl⟩ : syracuseStep 1553357 = 582509) (by norm_num)
theorem B1553381 : Blo 1032607 1553381 := bbase (se 4 (by rfl) ⟨145629, by rfl⟩ : syracuseStep 1553381 = 291259) (by norm_num)
theorem B1553405 : Blo 1032607 1553405 := bbase (se 3 (by rfl) ⟨291263, by rfl⟩ : syracuseStep 1553405 = 582527) (by norm_num)
theorem B3486725 : Blo 1032607 3486725 := bbase (se 4 (by rfl) ⟨326880, by rfl⟩ : syracuseStep 3486725 = 653761) (by norm_num)
theorem B1553429 : Blo 1032607 1553429 := bbase (se 6 (by rfl) ⟨36408, by rfl⟩ : syracuseStep 1553429 = 72817) (by norm_num)
theorem B1553453 : Blo 1032607 1553453 := bbase (se 3 (by rfl) ⟨291272, by rfl⟩ : syracuseStep 1553453 = 582545) (by norm_num)
theorem B1553477 : Blo 1032607 1553477 := bbase (se 4 (by rfl) ⟨145638, by rfl⟩ : syracuseStep 1553477 = 291277) (by norm_num)
theorem B1553501 : Blo 1032607 1553501 := bbase (se 3 (by rfl) ⟨291281, by rfl⟩ : syracuseStep 1553501 = 582563) (by norm_num)
theorem B1553525 : Blo 1032607 1553525 := bbase (se 5 (by rfl) ⟨72821, by rfl⟩ : syracuseStep 1553525 = 145643) (by norm_num)
theorem B1553549 : Blo 1032607 1553549 := bbase (se 3 (by rfl) ⟨291290, by rfl⟩ : syracuseStep 1553549 = 582581) (by norm_num)
theorem B1553573 : Blo 1032607 1553573 := bbase (se 4 (by rfl) ⟨145647, by rfl⟩ : syracuseStep 1553573 = 291295) (by norm_num)
theorem B1553597 : Blo 1032607 1553597 := bbase (se 3 (by rfl) ⟨291299, by rfl⟩ : syracuseStep 1553597 = 582599) (by norm_num)
theorem B2208973 : Blo 1032607 2208973 := bbase (se 3 (by rfl) ⟨414182, by rfl⟩ : syracuseStep 2208973 = 828365) (by norm_num)
theorem B1553621 : Blo 1032607 1553621 := bbase (se 7 (by rfl) ⟨18206, by rfl⟩ : syracuseStep 1553621 = 36413) (by norm_num)
theorem B1553645 : Blo 1032607 1553645 := bbase (se 3 (by rfl) ⟨291308, by rfl⟩ : syracuseStep 1553645 = 582617) (by norm_num)
theorem B1553669 : Blo 1032607 1553669 := bbase (se 4 (by rfl) ⟨145656, by rfl⟩ : syracuseStep 1553669 = 291313) (by norm_num)
theorem B1553693 : Blo 1032607 1553693 := bbase (se 3 (by rfl) ⟨291317, by rfl⟩ : syracuseStep 1553693 = 582635) (by norm_num)
theorem B1553717 : Blo 1032607 1553717 := bbase (se 5 (by rfl) ⟨72830, by rfl⟩ : syracuseStep 1553717 = 145661) (by norm_num)
theorem B1553741 : Blo 1032607 1553741 := bbase (se 3 (by rfl) ⟨291326, by rfl⟩ : syracuseStep 1553741 = 582653) (by norm_num)
theorem B1553765 : Blo 1032607 1553765 := bbase (se 4 (by rfl) ⟨145665, by rfl⟩ : syracuseStep 1553765 = 291331) (by norm_num)
theorem B1553789 : Blo 1032607 1553789 := bbase (se 3 (by rfl) ⟨291335, by rfl⟩ : syracuseStep 1553789 = 582671) (by norm_num)
theorem B1553813 : Blo 1032607 1553813 := bbase (se 6 (by rfl) ⟨36417, by rfl⟩ : syracuseStep 1553813 = 72835) (by norm_num)
theorem B1553837 : Blo 1032607 1553837 := bbase (se 3 (by rfl) ⟨291344, by rfl⟩ : syracuseStep 1553837 = 582689) (by norm_num)
theorem B3487157 : Blo 1032607 3487157 := bbase (se 5 (by rfl) ⟨163460, by rfl⟩ : syracuseStep 3487157 = 326921) (by norm_num)
theorem B1553861 : Blo 1032607 1553861 := bbase (se 4 (by rfl) ⟨145674, by rfl⟩ : syracuseStep 1553861 = 291349) (by norm_num)
theorem B1553885 : Blo 1032607 1553885 := bbase (se 3 (by rfl) ⟨291353, by rfl⟩ : syracuseStep 1553885 = 582707) (by norm_num)
theorem B1553909 : Blo 1032607 1553909 := bbase (se 5 (by rfl) ⟨72839, by rfl⟩ : syracuseStep 1553909 = 145679) (by norm_num)
theorem B1553933 : Blo 1032607 1553933 := bbase (se 3 (by rfl) ⟨291362, by rfl⟩ : syracuseStep 1553933 = 582725) (by norm_num)
theorem B1553957 : Blo 1032607 1553957 := bbase (se 4 (by rfl) ⟨145683, by rfl⟩ : syracuseStep 1553957 = 291367) (by norm_num)
theorem B1553981 : Blo 1032607 1553981 := bbase (se 3 (by rfl) ⟨291371, by rfl⟩ : syracuseStep 1553981 = 582743) (by norm_num)
theorem B2209349 : Blo 1032607 2209349 := bbase (se 4 (by rfl) ⟨207126, by rfl⟩ : syracuseStep 2209349 = 414253) (by norm_num)
theorem B1554005 : Blo 1032607 1554005 := bbase (se 8 (by rfl) ⟨9105, by rfl⟩ : syracuseStep 1554005 = 18211) (by norm_num)
theorem B1554029 : Blo 1032607 1554029 := bbase (se 3 (by rfl) ⟨291380, by rfl⟩ : syracuseStep 1554029 = 582761) (by norm_num)
theorem B1554053 : Blo 1032607 1554053 := bbase (se 4 (by rfl) ⟨145692, by rfl⟩ : syracuseStep 1554053 = 291385) (by norm_num)
theorem B1554077 : Blo 1032607 1554077 := bbase (se 3 (by rfl) ⟨291389, by rfl⟩ : syracuseStep 1554077 = 582779) (by norm_num)
theorem B1554101 : Blo 1032607 1554101 := bbase (se 5 (by rfl) ⟨72848, by rfl⟩ : syracuseStep 1554101 = 145697) (by norm_num)
theorem B1554125 : Blo 1032607 1554125 := bbase (se 3 (by rfl) ⟨291398, by rfl⟩ : syracuseStep 1554125 = 582797) (by norm_num)
theorem B1554149 : Blo 1032607 1554149 := bbase (se 4 (by rfl) ⟨145701, by rfl⟩ : syracuseStep 1554149 = 291403) (by norm_num)
theorem B1554173 : Blo 1032607 1554173 := bbase (se 3 (by rfl) ⟨291407, by rfl⟩ : syracuseStep 1554173 = 582815) (by norm_num)
theorem B1554197 : Blo 1032607 1554197 := bbase (se 6 (by rfl) ⟨36426, by rfl⟩ : syracuseStep 1554197 = 72853) (by norm_num)
theorem B1554221 : Blo 1032607 1554221 := bbase (se 3 (by rfl) ⟨291416, by rfl⟩ : syracuseStep 1554221 = 582833) (by norm_num)
theorem B1324849 : Blo 1032607 1324849 := bbase (se 2 (by rfl) ⟨496818, by rfl⟩ : syracuseStep 1324849 = 993637) (by norm_num)
theorem B1554245 : Blo 1032607 1554245 := bbase (se 4 (by rfl) ⟨145710, by rfl⟩ : syracuseStep 1554245 = 291421) (by norm_num)
theorem B1554269 : Blo 1032607 1554269 := bbase (se 3 (by rfl) ⟨291425, by rfl⟩ : syracuseStep 1554269 = 582851) (by norm_num)
theorem B3487589 : Blo 1032607 3487589 := bbase (se 4 (by rfl) ⟨326961, by rfl⟩ : syracuseStep 3487589 = 653923) (by norm_num)
theorem B1554293 : Blo 1032607 1554293 := bbase (se 5 (by rfl) ⟨72857, by rfl⟩ : syracuseStep 1554293 = 145715) (by norm_num)
theorem B1554317 : Blo 1032607 1554317 := bbase (se 3 (by rfl) ⟨291434, by rfl⟩ : syracuseStep 1554317 = 582869) (by norm_num)
theorem B1554341 : Blo 1032607 1554341 := bbase (se 4 (by rfl) ⟨145719, by rfl⟩ : syracuseStep 1554341 = 291439) (by norm_num)
theorem B1554365 : Blo 1032607 1554365 := bbase (se 3 (by rfl) ⟨291443, by rfl⟩ : syracuseStep 1554365 = 582887) (by norm_num)
theorem B1554389 : Blo 1032607 1554389 := bbase (se 7 (by rfl) ⟨18215, by rfl⟩ : syracuseStep 1554389 = 36431) (by norm_num)
theorem B1554413 : Blo 1032607 1554413 := bbase (se 3 (by rfl) ⟨291452, by rfl⟩ : syracuseStep 1554413 = 582905) (by norm_num)
theorem B1554437 : Blo 1032607 1554437 := bbase (se 4 (by rfl) ⟨145728, by rfl⟩ : syracuseStep 1554437 = 291457) (by norm_num)
theorem B1554461 : Blo 1032607 1554461 := bbase (se 3 (by rfl) ⟨291461, by rfl⟩ : syracuseStep 1554461 = 582923) (by norm_num)
theorem B1554485 : Blo 1032607 1554485 := bbase (se 5 (by rfl) ⟨72866, by rfl⟩ : syracuseStep 1554485 = 145733) (by norm_num)
theorem B1554509 : Blo 1032607 1554509 := bbase (se 3 (by rfl) ⟨291470, by rfl⟩ : syracuseStep 1554509 = 582941) (by norm_num)
theorem B1554533 : Blo 1032607 1554533 := bbase (se 4 (by rfl) ⟨145737, by rfl⟩ : syracuseStep 1554533 = 291475) (by norm_num)
theorem B1554557 : Blo 1032607 1554557 := bbase (se 3 (by rfl) ⟨291479, by rfl⟩ : syracuseStep 1554557 = 582959) (by norm_num)
theorem B1554581 : Blo 1032607 1554581 := bbase (se 6 (by rfl) ⟨36435, by rfl⟩ : syracuseStep 1554581 = 72871) (by norm_num)
theorem B1554605 : Blo 1032607 1554605 := bbase (se 3 (by rfl) ⟨291488, by rfl⟩ : syracuseStep 1554605 = 582977) (by norm_num)
theorem B1554629 : Blo 1032607 1554629 := bbase (se 4 (by rfl) ⟨145746, by rfl⟩ : syracuseStep 1554629 = 291493) (by norm_num)
theorem B1554653 : Blo 1032607 1554653 := bbase (se 3 (by rfl) ⟨291497, by rfl⟩ : syracuseStep 1554653 = 582995) (by norm_num)
theorem B1554677 : Blo 1032607 1554677 := bbase (se 5 (by rfl) ⟨72875, by rfl⟩ : syracuseStep 1554677 = 145751) (by norm_num)
theorem B1554701 : Blo 1032607 1554701 := bbase (se 3 (by rfl) ⟨291506, by rfl⟩ : syracuseStep 1554701 = 583013) (by norm_num)
theorem B3488021 : Blo 1032607 3488021 := bbase (se 6 (by rfl) ⟨81750, by rfl⟩ : syracuseStep 3488021 = 163501) (by norm_num)
theorem B1554725 : Blo 1032607 1554725 := bbase (se 4 (by rfl) ⟨145755, by rfl⟩ : syracuseStep 1554725 = 291511) (by norm_num)
theorem B1554749 : Blo 1032607 1554749 := bbase (se 3 (by rfl) ⟨291515, by rfl⟩ : syracuseStep 1554749 = 583031) (by norm_num)
theorem B1554773 : Blo 1032607 1554773 := bbase (se 10 (by rfl) ⟨2277, by rfl⟩ : syracuseStep 1554773 = 4555) (by norm_num)
theorem B1554797 : Blo 1032607 1554797 := bbase (se 3 (by rfl) ⟨291524, by rfl⟩ : syracuseStep 1554797 = 583049) (by norm_num)
theorem B1554821 : Blo 1032607 1554821 := bbase (se 4 (by rfl) ⟨145764, by rfl⟩ : syracuseStep 1554821 = 291529) (by norm_num)
theorem B1554845 : Blo 1032607 1554845 := bbase (se 3 (by rfl) ⟨291533, by rfl⟩ : syracuseStep 1554845 = 583067) (by norm_num)
theorem B1554869 : Blo 1032607 1554869 := bbase (se 5 (by rfl) ⟨72884, by rfl⟩ : syracuseStep 1554869 = 145769) (by norm_num)
theorem B1554893 : Blo 1032607 1554893 := bbase (se 3 (by rfl) ⟨291542, by rfl⟩ : syracuseStep 1554893 = 583085) (by norm_num)
theorem B1161697 : Blo 1032607 1161697 := bbase (se 2 (by rfl) ⟨435636, by rfl⟩ : syracuseStep 1161697 = 871273) (by norm_num)
theorem B1161733 : Blo 1032607 1161733 := bbase (se 4 (by rfl) ⟨108912, by rfl⟩ : syracuseStep 1161733 = 217825) (by norm_num)
theorem B1161769 : Blo 1032607 1161769 := bbase (se 2 (by rfl) ⟨435663, by rfl⟩ : syracuseStep 1161769 = 871327) (by norm_num)
theorem B1161805 : Blo 1032607 1161805 := bbase (se 3 (by rfl) ⟨217838, by rfl⟩ : syracuseStep 1161805 = 435677) (by norm_num)
theorem B1161841 : Blo 1032607 1161841 := bbase (se 2 (by rfl) ⟨435690, by rfl⟩ : syracuseStep 1161841 = 871381) (by norm_num)
theorem B1161877 : Blo 1032607 1161877 := bbase (se 6 (by rfl) ⟨27231, by rfl⟩ : syracuseStep 1161877 = 54463) (by norm_num)
theorem B1161913 : Blo 1032607 1161913 := bbase (se 2 (by rfl) ⟨435717, by rfl⟩ : syracuseStep 1161913 = 871435) (by norm_num)
theorem B3488453 : Blo 1032607 3488453 := bbase (se 4 (by rfl) ⟨327042, by rfl⟩ : syracuseStep 3488453 = 654085) (by norm_num)
theorem B1161949 : Blo 1032607 1161949 := bbase (se 3 (by rfl) ⟨217865, by rfl⟩ : syracuseStep 1161949 = 435731) (by norm_num)
theorem B1260257 : Blo 1032607 1260257 := bbase (se 2 (by rfl) ⟨472596, by rfl⟩ : syracuseStep 1260257 = 945193) (by norm_num)
theorem B1161985 : Blo 1032607 1161985 := bbase (se 2 (by rfl) ⟨435744, by rfl⟩ : syracuseStep 1161985 = 871489) (by norm_num)
theorem B1162021 : Blo 1032607 1162021 := bbase (se 4 (by rfl) ⟨108939, by rfl⟩ : syracuseStep 1162021 = 217879) (by norm_num)
theorem B1162057 : Blo 1032607 1162057 := bbase (se 2 (by rfl) ⟨435771, by rfl⟩ : syracuseStep 1162057 = 871543) (by norm_num)
theorem B1162093 : Blo 1032607 1162093 := bbase (se 3 (by rfl) ⟨217892, by rfl⟩ : syracuseStep 1162093 = 435785) (by norm_num)
theorem B1162129 : Blo 1032607 1162129 := bbase (se 2 (by rfl) ⟨435798, by rfl⟩ : syracuseStep 1162129 = 871597) (by norm_num)
theorem B1162165 : Blo 1032607 1162165 := bbase (se 5 (by rfl) ⟨54476, by rfl⟩ : syracuseStep 1162165 = 108953) (by norm_num)
theorem B1162201 : Blo 1032607 1162201 := bbase (se 2 (by rfl) ⟨435825, by rfl⟩ : syracuseStep 1162201 = 871651) (by norm_num)
theorem B1260533 : Blo 1032607 1260533 := bbase (se 5 (by rfl) ⟨59087, by rfl⟩ : syracuseStep 1260533 = 118175) (by norm_num)
theorem B1162237 : Blo 1032607 1162237 := bbase (se 3 (by rfl) ⟨217919, by rfl⟩ : syracuseStep 1162237 = 435839) (by norm_num)
theorem B1162273 : Blo 1032607 1162273 := bbase (se 2 (by rfl) ⟨435852, by rfl⟩ : syracuseStep 1162273 = 871705) (by norm_num)
theorem B1162309 : Blo 1032607 1162309 := bbase (se 4 (by rfl) ⟨108966, by rfl⟩ : syracuseStep 1162309 = 217933) (by norm_num)
theorem B1162345 : Blo 1032607 1162345 := bbase (se 2 (by rfl) ⟨435879, by rfl⟩ : syracuseStep 1162345 = 871759) (by norm_num)
theorem B3488885 : Blo 1032607 3488885 := bbase (se 5 (by rfl) ⟨163541, by rfl⟩ : syracuseStep 3488885 = 327083) (by norm_num)
theorem B1162381 : Blo 1032607 1162381 := bbase (se 3 (by rfl) ⟨217946, by rfl⟩ : syracuseStep 1162381 = 435893) (by norm_num)
theorem B2210989 : Blo 1032607 2210989 := bbase (se 3 (by rfl) ⟨414560, by rfl⟩ : syracuseStep 2210989 = 829121) (by norm_num)
theorem B1162417 : Blo 1032607 1162417 := bbase (se 2 (by rfl) ⟨435906, by rfl⟩ : syracuseStep 1162417 = 871813) (by norm_num)
theorem B1162453 : Blo 1032607 1162453 := bbase (se 7 (by rfl) ⟨13622, by rfl⟩ : syracuseStep 1162453 = 27245) (by norm_num)
theorem B1162489 : Blo 1032607 1162489 := bbase (se 2 (by rfl) ⟨435933, by rfl⟩ : syracuseStep 1162489 = 871867) (by norm_num)
theorem B1162525 : Blo 1032607 1162525 := bbase (se 3 (by rfl) ⟨217973, by rfl⟩ : syracuseStep 1162525 = 435947) (by norm_num)
theorem B1162561 : Blo 1032607 1162561 := bbase (se 2 (by rfl) ⟨435960, by rfl⟩ : syracuseStep 1162561 = 871921) (by norm_num)
theorem B1162597 : Blo 1032607 1162597 := bbase (se 4 (by rfl) ⟨108993, by rfl⟩ : syracuseStep 1162597 = 217987) (by norm_num)
theorem B1326461 : Blo 1032607 1326461 := bbase (se 3 (by rfl) ⟨248711, by rfl⟩ : syracuseStep 1326461 = 497423) (by norm_num)
theorem B1162633 : Blo 1032607 1162633 := bbase (se 2 (by rfl) ⟨435987, by rfl⟩ : syracuseStep 1162633 = 871975) (by norm_num)
theorem B2014637 : Blo 1032607 2014637 := bbase (se 3 (by rfl) ⟨377744, by rfl⟩ : syracuseStep 2014637 = 755489) (by norm_num)
theorem B1162669 : Blo 1032607 1162669 := bbase (se 3 (by rfl) ⟨218000, by rfl⟩ : syracuseStep 1162669 = 436001) (by norm_num)
theorem B1162705 : Blo 1032607 1162705 := bbase (se 2 (by rfl) ⟨436014, by rfl⟩ : syracuseStep 1162705 = 872029) (by norm_num)
theorem B1162741 : Blo 1032607 1162741 := bbase (se 5 (by rfl) ⟨54503, by rfl⟩ : syracuseStep 1162741 = 109007) (by norm_num)
theorem B1162777 : Blo 1032607 1162777 := bbase (se 2 (by rfl) ⟨436041, by rfl⟩ : syracuseStep 1162777 = 872083) (by norm_num)
theorem B3489317 : Blo 1032607 3489317 := bbase (se 4 (by rfl) ⟨327123, by rfl⟩ : syracuseStep 3489317 = 654247) (by norm_num)
theorem B1162813 : Blo 1032607 1162813 := bbase (se 3 (by rfl) ⟨218027, by rfl⟩ : syracuseStep 1162813 = 436055) (by norm_num)
theorem B1162849 : Blo 1032607 1162849 := bbase (se 2 (by rfl) ⟨436068, by rfl⟩ : syracuseStep 1162849 = 872137) (by norm_num)
theorem B1162885 : Blo 1032607 1162885 := bbase (se 4 (by rfl) ⟨109020, by rfl⟩ : syracuseStep 1162885 = 218041) (by norm_num)
theorem B1162921 : Blo 1032607 1162921 := bbase (se 2 (by rfl) ⟨436095, by rfl⟩ : syracuseStep 1162921 = 872191) (by norm_num)
theorem B1162957 : Blo 1032607 1162957 := bbase (se 3 (by rfl) ⟨218054, by rfl⟩ : syracuseStep 1162957 = 436109) (by norm_num)
theorem B1162993 : Blo 1032607 1162993 := bbase (se 2 (by rfl) ⟨436122, by rfl⟩ : syracuseStep 1162993 = 872245) (by norm_num)
theorem B1163029 : Blo 1032607 1163029 := bbase (se 6 (by rfl) ⟨27258, by rfl⟩ : syracuseStep 1163029 = 54517) (by norm_num)
theorem B1163065 : Blo 1032607 1163065 := bbase (se 2 (by rfl) ⟨436149, by rfl⟩ : syracuseStep 1163065 = 872299) (by norm_num)
theorem B1654597 : Blo 1032607 1654597 := bbase (se 4 (by rfl) ⟨155118, by rfl⟩ : syracuseStep 1654597 = 310237) (by norm_num)
theorem B1163101 : Blo 1032607 1163101 := bbase (se 3 (by rfl) ⟨218081, by rfl⟩ : syracuseStep 1163101 = 436163) (by norm_num)
theorem B1326953 : Blo 1032607 1326953 := bbase (se 2 (by rfl) ⟨497607, by rfl⟩ : syracuseStep 1326953 = 995215) (by norm_num)
theorem B1163137 : Blo 1032607 1163137 := bbase (se 2 (by rfl) ⟨436176, by rfl⟩ : syracuseStep 1163137 = 872353) (by norm_num)
theorem B1163173 : Blo 1032607 1163173 := bbase (se 4 (by rfl) ⟨109047, by rfl⟩ : syracuseStep 1163173 = 218095) (by norm_num)
theorem B1163209 : Blo 1032607 1163209 := bbase (se 2 (by rfl) ⟨436203, by rfl⟩ : syracuseStep 1163209 = 872407) (by norm_num)
theorem B3489749 : Blo 1032607 3489749 := bbase (se 7 (by rfl) ⟨40895, by rfl⟩ : syracuseStep 3489749 = 81791) (by norm_num)
theorem B1163245 : Blo 1032607 1163245 := bbase (se 3 (by rfl) ⟨218108, by rfl⟩ : syracuseStep 1163245 = 436217) (by norm_num)
theorem B1163281 : Blo 1032607 1163281 := bbase (se 2 (by rfl) ⟨436230, by rfl⟩ : syracuseStep 1163281 = 872461) (by norm_num)
theorem B2211877 : Blo 1032607 2211877 := bbase (se 4 (by rfl) ⟨207363, by rfl⟩ : syracuseStep 2211877 = 414727) (by norm_num)
theorem B1163317 : Blo 1032607 1163317 := bbase (se 5 (by rfl) ⟨54530, by rfl⟩ : syracuseStep 1163317 = 109061) (by norm_num)
theorem B1163353 : Blo 1032607 1163353 := bbase (se 2 (by rfl) ⟨436257, by rfl⟩ : syracuseStep 1163353 = 872515) (by norm_num)
theorem B1163389 : Blo 1032607 1163389 := bbase (se 3 (by rfl) ⟨218135, by rfl⟩ : syracuseStep 1163389 = 436271) (by norm_num)
theorem B1163425 : Blo 1032607 1163425 := bbase (se 2 (by rfl) ⟨436284, by rfl⟩ : syracuseStep 1163425 = 872569) (by norm_num)
theorem B4538549 : Blo 1032607 4538549 := bbase (se 5 (by rfl) ⟨212744, by rfl⟩ : syracuseStep 4538549 = 425489) (by norm_num)
theorem B1163461 : Blo 1032607 1163461 := bbase (se 4 (by rfl) ⟨109074, by rfl⟩ : syracuseStep 1163461 = 218149) (by norm_num)
theorem B1163497 : Blo 1032607 1163497 := bbase (se 2 (by rfl) ⟨436311, by rfl⟩ : syracuseStep 1163497 = 872623) (by norm_num)
theorem B1163533 : Blo 1032607 1163533 := bbase (se 3 (by rfl) ⟨218162, by rfl⟩ : syracuseStep 1163533 = 436325) (by norm_num)
theorem B1163569 : Blo 1032607 1163569 := bbase (se 2 (by rfl) ⟨436338, by rfl⟩ : syracuseStep 1163569 = 872677) (by norm_num)
theorem B5882165 : Blo 1032607 5882165 := bbase (se 5 (by rfl) ⟨275726, by rfl⟩ : syracuseStep 5882165 = 551453) (by norm_num)
theorem B1163605 : Blo 1032607 1163605 := bbase (se 10 (by rfl) ⟨1704, by rfl⟩ : syracuseStep 1163605 = 3409) (by norm_num)
theorem B1163641 : Blo 1032607 1163641 := bbase (se 2 (by rfl) ⟨436365, by rfl⟩ : syracuseStep 1163641 = 872731) (by norm_num)
theorem B3490181 : Blo 1032607 3490181 := bbase (se 4 (by rfl) ⟨327204, by rfl⟩ : syracuseStep 3490181 = 654409) (by norm_num)
theorem B1163677 : Blo 1032607 1163677 := bbase (se 3 (by rfl) ⟨218189, by rfl⟩ : syracuseStep 1163677 = 436379) (by norm_num)
theorem B1163713 : Blo 1032607 1163713 := bbase (se 2 (by rfl) ⟨436392, by rfl⟩ : syracuseStep 1163713 = 872785) (by norm_num)
theorem B8405461 : Blo 1032607 8405461 := bbase (se 7 (by rfl) ⟨98501, by rfl⟩ : syracuseStep 8405461 = 197003) (by norm_num)
theorem B1163749 : Blo 1032607 1163749 := bbase (se 4 (by rfl) ⟨109101, by rfl⟩ : syracuseStep 1163749 = 218203) (by norm_num)
theorem B1163785 : Blo 1032607 1163785 := bbase (se 2 (by rfl) ⟨436419, by rfl⟩ : syracuseStep 1163785 = 872839) (by norm_num)
theorem B4964885 : Blo 1032607 4964885 := bbase (se 6 (by rfl) ⟨116364, by rfl⟩ : syracuseStep 4964885 = 232729) (by norm_num)
theorem B2212373 : Blo 1032607 2212373 := bbase (se 6 (by rfl) ⟨51852, by rfl⟩ : syracuseStep 2212373 = 103705) (by norm_num)
theorem B3031589 : Blo 1032607 3031589 := bbase (se 4 (by rfl) ⟨284211, by rfl⟩ : syracuseStep 3031589 = 568423) (by norm_num)
theorem B1163821 : Blo 1032607 1163821 := bbase (se 3 (by rfl) ⟨218216, by rfl⟩ : syracuseStep 1163821 = 436433) (by norm_num)
theorem B1163857 : Blo 1032607 1163857 := bbase (se 2 (by rfl) ⟨436446, by rfl⟩ : syracuseStep 1163857 = 872893) (by norm_num)
theorem B1163893 : Blo 1032607 1163893 := bbase (se 5 (by rfl) ⟨54557, by rfl⟩ : syracuseStep 1163893 = 109115) (by norm_num)
theorem B1163929 : Blo 1032607 1163929 := bbase (se 2 (by rfl) ⟨436473, by rfl⟩ : syracuseStep 1163929 = 872947) (by norm_num)
theorem B1163965 : Blo 1032607 1163965 := bbase (se 3 (by rfl) ⟨218243, by rfl⟩ : syracuseStep 1163965 = 436487) (by norm_num)
theorem B1164001 : Blo 1032607 1164001 := bbase (se 2 (by rfl) ⟨436500, by rfl⟩ : syracuseStep 1164001 = 873001) (by norm_num)
theorem B1655525 : Blo 1032607 1655525 := bbase (se 4 (by rfl) ⟨155205, by rfl⟩ : syracuseStep 1655525 = 310411) (by norm_num)
theorem B1164037 : Blo 1032607 1164037 := bbase (se 4 (by rfl) ⟨109128, by rfl⟩ : syracuseStep 1164037 = 218257) (by norm_num)
theorem B1164073 : Blo 1032607 1164073 := bbase (se 2 (by rfl) ⟨436527, by rfl⟩ : syracuseStep 1164073 = 873055) (by norm_num)
theorem B3490613 : Blo 1032607 3490613 := bbase (se 5 (by rfl) ⟨163622, by rfl⟩ : syracuseStep 3490613 = 327245) (by norm_num)
theorem B1164109 : Blo 1032607 1164109 := bbase (se 3 (by rfl) ⟨218270, by rfl⟩ : syracuseStep 1164109 = 436541) (by norm_num)
theorem B1164145 : Blo 1032607 1164145 := bbase (se 2 (by rfl) ⟨436554, by rfl⟩ : syracuseStep 1164145 = 873109) (by norm_num)
theorem B1164181 : Blo 1032607 1164181 := bbase (se 6 (by rfl) ⟨27285, by rfl⟩ : syracuseStep 1164181 = 54571) (by norm_num)
theorem B1164217 : Blo 1032607 1164217 := bbase (se 2 (by rfl) ⟨436581, by rfl⟩ : syracuseStep 1164217 = 873163) (by norm_num)
theorem B1164253 : Blo 1032607 1164253 := bbase (se 3 (by rfl) ⟨218297, by rfl⟩ : syracuseStep 1164253 = 436595) (by norm_num)
theorem B1328113 : Blo 1032607 1328113 := bbase (se 2 (by rfl) ⟨498042, by rfl⟩ : syracuseStep 1328113 = 996085) (by norm_num)
theorem B1164289 : Blo 1032607 1164289 := bbase (se 2 (by rfl) ⟨436608, by rfl⟩ : syracuseStep 1164289 = 873217) (by norm_num)
theorem B1164325 : Blo 1032607 1164325 := bbase (se 4 (by rfl) ⟨109155, by rfl⟩ : syracuseStep 1164325 = 218311) (by norm_num)
theorem B1164361 : Blo 1032607 1164361 := bbase (se 2 (by rfl) ⟨436635, by rfl⟩ : syracuseStep 1164361 = 873271) (by norm_num)
theorem B1164397 : Blo 1032607 1164397 := bbase (se 3 (by rfl) ⟨218324, by rfl⟩ : syracuseStep 1164397 = 436649) (by norm_num)
theorem B1164433 : Blo 1032607 1164433 := bbase (se 2 (by rfl) ⟨436662, by rfl⟩ : syracuseStep 1164433 = 873325) (by norm_num)
theorem B1328297 : Blo 1032607 1328297 := bbase (se 2 (by rfl) ⟨498111, by rfl⟩ : syracuseStep 1328297 = 996223) (by norm_num)
theorem B1655981 : Blo 1032607 1655981 := bbase (se 3 (by rfl) ⟨310496, by rfl⟩ : syracuseStep 1655981 = 620993) (by norm_num)
theorem B1164469 : Blo 1032607 1164469 := bbase (se 5 (by rfl) ⟨54584, by rfl⟩ : syracuseStep 1164469 = 109169) (by norm_num)
theorem B27280597 : Blo 1032607 27280597 := bbase (se 7 (by rfl) ⟨319694, by rfl⟩ : syracuseStep 27280597 = 639389) (by norm_num)
theorem B1164505 : Blo 1032607 1164505 := bbase (se 2 (by rfl) ⟨436689, by rfl⟩ : syracuseStep 1164505 = 873379) (by norm_num)
theorem B3491045 : Blo 1032607 3491045 := bbase (se 4 (by rfl) ⟨327285, by rfl⟩ : syracuseStep 3491045 = 654571) (by norm_num)
theorem B1164541 : Blo 1032607 1164541 := bbase (se 3 (by rfl) ⟨218351, by rfl⟩ : syracuseStep 1164541 = 436703) (by norm_num)
theorem B1164577 : Blo 1032607 1164577 := bbase (se 2 (by rfl) ⟨436716, by rfl⟩ : syracuseStep 1164577 = 873433) (by norm_num)
theorem B1164613 : Blo 1032607 1164613 := bbase (se 4 (by rfl) ⟨109182, by rfl⟩ : syracuseStep 1164613 = 218365) (by norm_num)
theorem B1164649 : Blo 1032607 1164649 := bbase (se 2 (by rfl) ⟨436743, by rfl⟩ : syracuseStep 1164649 = 873487) (by norm_num)
theorem B2213237 : Blo 1032607 2213237 := bbase (se 5 (by rfl) ⟨103745, by rfl⟩ : syracuseStep 2213237 = 207491) (by norm_num)
theorem B1164685 : Blo 1032607 1164685 := bbase (se 3 (by rfl) ⟨218378, by rfl⟩ : syracuseStep 1164685 = 436757) (by norm_num)
theorem B1164721 : Blo 1032607 1164721 := bbase (se 2 (by rfl) ⟨436770, by rfl⟩ : syracuseStep 1164721 = 873541) (by norm_num)
theorem B1164757 : Blo 1032607 1164757 := bbase (se 7 (by rfl) ⟨13649, by rfl⟩ : syracuseStep 1164757 = 27299) (by norm_num)
theorem B1492453 : Blo 1032607 1492453 := bbase (se 4 (by rfl) ⟨139917, by rfl⟩ : syracuseStep 1492453 = 279835) (by norm_num)
theorem B1164793 : Blo 1032607 1164793 := bbase (se 2 (by rfl) ⟨436797, by rfl⟩ : syracuseStep 1164793 = 873595) (by norm_num)
theorem B2213381 : Blo 1032607 2213381 := bbase (se 4 (by rfl) ⟨207504, by rfl⟩ : syracuseStep 2213381 = 415009) (by norm_num)
theorem B1164829 : Blo 1032607 1164829 := bbase (se 3 (by rfl) ⟨218405, by rfl⟩ : syracuseStep 1164829 = 436811) (by norm_num)
theorem B1164865 : Blo 1032607 1164865 := bbase (se 2 (by rfl) ⟨436824, by rfl⟩ : syracuseStep 1164865 = 873649) (by norm_num)
theorem B1164901 : Blo 1032607 1164901 := bbase (se 4 (by rfl) ⟨109209, by rfl⟩ : syracuseStep 1164901 = 218419) (by norm_num)
theorem B1164937 : Blo 1032607 1164937 := bbase (se 2 (by rfl) ⟨436851, by rfl⟩ : syracuseStep 1164937 = 873703) (by norm_num)
theorem B3491477 : Blo 1032607 3491477 := bbase (se 6 (by rfl) ⟨81831, by rfl⟩ : syracuseStep 3491477 = 163663) (by norm_num)
theorem B1164973 : Blo 1032607 1164973 := bbase (se 3 (by rfl) ⟨218432, by rfl⟩ : syracuseStep 1164973 = 436865) (by norm_num)
theorem B1165009 : Blo 1032607 1165009 := bbase (se 2 (by rfl) ⟨436878, by rfl⟩ : syracuseStep 1165009 = 873757) (by norm_num)
theorem B1165045 : Blo 1032607 1165045 := bbase (se 5 (by rfl) ⟨54611, by rfl⟩ : syracuseStep 1165045 = 109223) (by norm_num)
theorem B1165081 : Blo 1032607 1165081 := bbase (se 2 (by rfl) ⟨436905, by rfl⟩ : syracuseStep 1165081 = 873811) (by norm_num)
theorem B1165117 : Blo 1032607 1165117 := bbase (se 3 (by rfl) ⟨218459, by rfl⟩ : syracuseStep 1165117 = 436919) (by norm_num)
theorem B1165153 : Blo 1032607 1165153 := bbase (se 2 (by rfl) ⟨436932, by rfl⟩ : syracuseStep 1165153 = 873865) (by norm_num)
theorem B1165189 : Blo 1032607 1165189 := bbase (se 4 (by rfl) ⟨109236, by rfl⟩ : syracuseStep 1165189 = 218473) (by norm_num)
theorem B2869141 : Blo 1032607 2869141 := bbase (se 6 (by rfl) ⟨67245, by rfl⟩ : syracuseStep 2869141 = 134491) (by norm_num)
theorem B1165225 : Blo 1032607 1165225 := bbase (se 2 (by rfl) ⟨436959, by rfl⟩ : syracuseStep 1165225 = 873919) (by norm_num)
theorem B1165261 : Blo 1032607 1165261 := bbase (se 3 (by rfl) ⟨218486, by rfl⟩ : syracuseStep 1165261 = 436973) (by norm_num)
theorem B1165297 : Blo 1032607 1165297 := bbase (se 2 (by rfl) ⟨436986, by rfl⟩ : syracuseStep 1165297 = 873973) (by norm_num)
theorem B5228549 : Blo 1032607 5228549 := bbase (se 4 (by rfl) ⟨490176, by rfl⟩ : syracuseStep 5228549 = 980353) (by norm_num)
theorem B1165333 : Blo 1032607 1165333 := bbase (se 6 (by rfl) ⟨27312, by rfl⟩ : syracuseStep 1165333 = 54625) (by norm_num)
theorem B1165369 : Blo 1032607 1165369 := bbase (se 2 (by rfl) ⟨437013, by rfl⟩ : syracuseStep 1165369 = 874027) (by norm_num)
theorem B3491909 : Blo 1032607 3491909 := bbase (se 4 (by rfl) ⟨327366, by rfl⟩ : syracuseStep 3491909 = 654733) (by norm_num)
theorem B1165405 : Blo 1032607 1165405 := bbase (se 3 (by rfl) ⟨218513, by rfl⟩ : syracuseStep 1165405 = 437027) (by norm_num)
theorem B1165441 : Blo 1032607 1165441 := bbase (se 2 (by rfl) ⟨437040, by rfl⟩ : syracuseStep 1165441 = 874081) (by norm_num)
theorem B20400277 : Blo 1032607 20400277 := bbase (se 6 (by rfl) ⟨478131, by rfl⟩ : syracuseStep 20400277 = 956263) (by norm_num)
theorem B1165477 : Blo 1032607 1165477 := bbase (se 4 (by rfl) ⟨109263, by rfl⟩ : syracuseStep 1165477 = 218527) (by norm_num)
theorem B1165513 : Blo 1032607 1165513 := bbase (se 2 (by rfl) ⟨437067, by rfl⟩ : syracuseStep 1165513 = 874135) (by norm_num)
theorem B1165549 : Blo 1032607 1165549 := bbase (se 3 (by rfl) ⟨218540, by rfl⟩ : syracuseStep 1165549 = 437081) (by norm_num)
theorem B1165585 : Blo 1032607 1165585 := bbase (se 2 (by rfl) ⟨437094, by rfl⟩ : syracuseStep 1165585 = 874189) (by norm_num)
theorem B1165621 : Blo 1032607 1165621 := bbase (se 5 (by rfl) ⟨54638, by rfl⟩ : syracuseStep 1165621 = 109277) (by norm_num)
theorem B1165657 : Blo 1032607 1165657 := bbase (se 2 (by rfl) ⟨437121, by rfl⟩ : syracuseStep 1165657 = 874243) (by norm_num)
theorem B7850357 : Blo 1032607 7850357 := bbase (se 5 (by rfl) ⟨367985, by rfl⟩ : syracuseStep 7850357 = 735971) (by norm_num)
theorem B1493365 : Blo 1032607 1493365 := bbase (se 5 (by rfl) ⟨70001, by rfl⟩ : syracuseStep 1493365 = 140003) (by norm_num)
theorem B1165693 : Blo 1032607 1165693 := bbase (se 3 (by rfl) ⟨218567, by rfl⟩ : syracuseStep 1165693 = 437135) (by norm_num)
theorem B1165729 : Blo 1032607 1165729 := bbase (se 2 (by rfl) ⟨437148, by rfl⟩ : syracuseStep 1165729 = 874297) (by norm_num)
theorem B1886645 : Blo 1032607 1886645 := bbase (se 5 (by rfl) ⟨88436, by rfl⟩ : syracuseStep 1886645 = 176873) (by norm_num)
theorem B1165765 : Blo 1032607 1165765 := bbase (se 4 (by rfl) ⟨109290, by rfl⟩ : syracuseStep 1165765 = 218581) (by norm_num)
theorem B1165801 : Blo 1032607 1165801 := bbase (se 2 (by rfl) ⟨437175, by rfl⟩ : syracuseStep 1165801 = 874351) (by norm_num)
theorem B6375925 : Blo 1032607 6375925 := bbase (se 5 (by rfl) ⟨298871, by rfl⟩ : syracuseStep 6375925 = 597743) (by norm_num)
theorem B3492341 : Blo 1032607 3492341 := bbase (se 5 (by rfl) ⟨163703, by rfl⟩ : syracuseStep 3492341 = 327407) (by norm_num)
theorem B1165837 : Blo 1032607 1165837 := bbase (se 3 (by rfl) ⟨218594, by rfl⟩ : syracuseStep 1165837 = 437189) (by norm_num)
theorem B1165873 : Blo 1032607 1165873 := bbase (se 2 (by rfl) ⟨437202, by rfl⟩ : syracuseStep 1165873 = 874405) (by norm_num)
theorem B1657397 : Blo 1032607 1657397 := bbase (se 5 (by rfl) ⟨77690, by rfl⟩ : syracuseStep 1657397 = 155381) (by norm_num)
theorem B1493573 : Blo 1032607 1493573 := bbase (se 4 (by rfl) ⟨140022, by rfl⟩ : syracuseStep 1493573 = 280045) (by norm_num)
theorem B1165909 : Blo 1032607 1165909 := bbase (se 8 (by rfl) ⟨6831, by rfl⟩ : syracuseStep 1165909 = 13663) (by norm_num)
theorem B1165945 : Blo 1032607 1165945 := bbase (se 2 (by rfl) ⟨437229, by rfl⟩ : syracuseStep 1165945 = 874459) (by norm_num)
theorem B1165981 : Blo 1032607 1165981 := bbase (se 3 (by rfl) ⟨218621, by rfl⟩ : syracuseStep 1165981 = 437243) (by norm_num)
theorem B1166017 : Blo 1032607 1166017 := bbase (se 2 (by rfl) ⟨437256, by rfl⟩ : syracuseStep 1166017 = 874513) (by norm_num)
theorem B1166053 : Blo 1032607 1166053 := bbase (se 4 (by rfl) ⟨109317, by rfl⟩ : syracuseStep 1166053 = 218635) (by norm_num)
theorem B1166089 : Blo 1032607 1166089 := bbase (se 2 (by rfl) ⟨437283, by rfl⟩ : syracuseStep 1166089 = 874567) (by norm_num)
theorem B1657621 : Blo 1032607 1657621 := bbase (se 6 (by rfl) ⟨38850, by rfl⟩ : syracuseStep 1657621 = 77701) (by norm_num)
theorem B1166125 : Blo 1032607 1166125 := bbase (se 3 (by rfl) ⟨218648, by rfl⟩ : syracuseStep 1166125 = 437297) (by norm_num)
theorem B1166161 : Blo 1032607 1166161 := bbase (se 2 (by rfl) ⟨437310, by rfl⟩ : syracuseStep 1166161 = 874621) (by norm_num)
theorem B3492773 : Blo 1032607 3492773 := bbase (se 4 (by rfl) ⟨327447, by rfl⟩ : syracuseStep 3492773 = 654895) (by norm_num)
theorem B5229845 : Blo 1032607 5229845 := bbase (se 6 (by rfl) ⟨122574, by rfl⟩ : syracuseStep 5229845 = 245149) (by norm_num)
theorem B3493205 : Blo 1032607 3493205 := bbase (se 11 (by rfl) ⟨2558, by rfl⟩ : syracuseStep 3493205 = 5117) (by norm_num)
theorem B4148597 : Blo 1032607 4148597 := bbase (se 5 (by rfl) ⟨194465, by rfl⟩ : syracuseStep 4148597 = 388931) (by norm_num)
theorem B2837909 : Blo 1032607 2837909 := bbase (se 6 (by rfl) ⟨66513, by rfl⟩ : syracuseStep 2837909 = 133027) (by norm_num)
theorem B3493637 : Blo 1032607 3493637 := bbase (se 4 (by rfl) ⟨327528, by rfl⟩ : syracuseStep 3493637 = 655057) (by norm_num)
theorem B8834933 : Blo 1032607 8834933 := bbase (se 5 (by rfl) ⟨414137, by rfl⟩ : syracuseStep 8834933 = 828275) (by norm_num)
theorem B3723317 : Blo 1032607 3723317 := bbase (se 5 (by rfl) ⟨174530, by rfl⟩ : syracuseStep 3723317 = 349061) (by norm_num)
theorem B7065749 : Blo 1032607 7065749 := bbase (se 6 (by rfl) ⟨165603, by rfl⟩ : syracuseStep 7065749 = 331207) (by norm_num)
theorem B1659037 : Blo 1032607 1659037 := bbase (se 3 (by rfl) ⟨311069, by rfl⟩ : syracuseStep 1659037 = 622139) (by norm_num)
theorem B3494069 : Blo 1032607 3494069 := bbase (se 5 (by rfl) ⟨163784, by rfl⟩ : syracuseStep 3494069 = 327569) (by norm_num)
theorem B1593589 : Blo 1032607 1593589 := bbase (se 5 (by rfl) ⟨74699, by rfl⟩ : syracuseStep 1593589 = 149399) (by norm_num)
theorem B1397045 : Blo 1032607 1397045 := bbase (se 5 (by rfl) ⟨65486, by rfl⟩ : syracuseStep 1397045 = 130973) (by norm_num)
theorem B1659293 : Blo 1032607 1659293 := bbase (se 3 (by rfl) ⟨311117, by rfl⟩ : syracuseStep 1659293 = 622235) (by norm_num)
theorem B5231141 : Blo 1032607 5231141 := bbase (se 4 (by rfl) ⟨490419, by rfl⟩ : syracuseStep 5231141 = 980839) (by norm_num)
theorem B1659485 : Blo 1032607 1659485 := bbase (se 3 (by rfl) ⟨311153, by rfl⟩ : syracuseStep 1659485 = 622307) (by norm_num)
theorem B3494501 : Blo 1032607 3494501 := bbase (se 4 (by rfl) ⟨327609, by rfl⟩ : syracuseStep 3494501 = 655219) (by norm_num)
theorem B4412069 : Blo 1032607 4412069 := bbase (se 4 (by rfl) ⟨413631, by rfl⟩ : syracuseStep 4412069 = 827263) (by norm_num)
theorem B7951061 : Blo 1032607 7951061 := bbase (se 7 (by rfl) ⟨93176, by rfl⟩ : syracuseStep 7951061 = 186353) (by norm_num)
theorem B1102825 : Blo 1032607 1102825 := bbase (se 2 (by rfl) ⟨413559, by rfl⟩ : syracuseStep 1102825 = 827119) (by norm_num)
theorem B1102829 : Blo 1032607 1102829 := bbase (se 3 (by rfl) ⟨206780, by rfl⟩ : syracuseStep 1102829 = 413561) (by norm_num)
theorem B3494933 : Blo 1032607 3494933 := bbase (se 6 (by rfl) ⟨81912, by rfl⟩ : syracuseStep 3494933 = 163825) (by norm_num)
theorem B10605653 : Blo 1032607 10605653 := bbase (se 8 (by rfl) ⟨62142, by rfl⟩ : syracuseStep 10605653 = 124285) (by norm_num)
theorem B1135745 : Blo 1032607 1135745 := bbase (se 2 (by rfl) ⟨425904, by rfl⟩ : syracuseStep 1135745 = 851809) (by norm_num)
theorem B3495365 : Blo 1032607 3495365 := bbase (se 4 (by rfl) ⟨327690, by rfl⟩ : syracuseStep 3495365 = 655381) (by norm_num)
theorem B1660421 : Blo 1032607 1660421 := bbase (se 4 (by rfl) ⟨155664, by rfl⟩ : syracuseStep 1660421 = 311329) (by norm_num)
theorem B1103393 : Blo 1032607 1103393 := bbase (se 2 (by rfl) ⟨413772, by rfl⟩ : syracuseStep 1103393 = 827545) (by norm_num)
theorem B1103581 : Blo 1032607 1103581 := bbase (se 3 (by rfl) ⟨206921, by rfl⟩ : syracuseStep 1103581 = 413843) (by norm_num)
theorem B5232437 : Blo 1032607 5232437 := bbase (se 5 (by rfl) ⟨245270, by rfl⟩ : syracuseStep 5232437 = 490541) (by norm_num)
theorem B11196245 : Blo 1032607 11196245 := bbase (se 9 (by rfl) ⟨32801, by rfl⟩ : syracuseStep 11196245 = 65603) (by norm_num)
theorem B3495797 : Blo 1032607 3495797 := bbase (se 5 (by rfl) ⟨163865, by rfl⟩ : syracuseStep 3495797 = 327731) (by norm_num)
theorem B1398877 : Blo 1032607 1398877 := bbase (se 3 (by rfl) ⟨262289, by rfl⟩ : syracuseStep 1398877 = 524579) (by norm_num)
theorem B3725509 : Blo 1032607 3725509 := bbase (se 4 (by rfl) ⟨349266, by rfl⟩ : syracuseStep 3725509 = 698533) (by norm_num)
theorem B3496229 : Blo 1032607 3496229 := bbase (se 4 (by rfl) ⟨327771, by rfl⟩ : syracuseStep 3496229 = 655543) (by norm_num)
theorem B4413845 : Blo 1032607 4413845 := bbase (se 6 (by rfl) ⟨103449, by rfl⟩ : syracuseStep 4413845 = 206899) (by norm_num)
theorem B1104401 : Blo 1032607 1104401 := bbase (se 2 (by rfl) ⟨414150, by rfl⟩ : syracuseStep 1104401 = 828301) (by norm_num)
theorem B4414085 : Blo 1032607 4414085 := bbase (se 4 (by rfl) ⟨413820, by rfl⟩ : syracuseStep 4414085 = 827641) (by norm_num)
theorem B3922613 : Blo 1032607 3922613 := bbase (se 5 (by rfl) ⟨183872, by rfl⟩ : syracuseStep 3922613 = 367745) (by norm_num)
theorem B3496661 : Blo 1032607 3496661 := bbase (se 7 (by rfl) ⟨40976, by rfl⟩ : syracuseStep 3496661 = 81953) (by norm_num)
theorem B8837909 : Blo 1032607 8837909 := bbase (se 6 (by rfl) ⟨207138, by rfl⟩ : syracuseStep 8837909 = 414277) (by norm_num)
theorem B1104845 : Blo 1032607 1104845 := bbase (se 3 (by rfl) ⟨207158, by rfl⟩ : syracuseStep 1104845 = 414317) (by norm_num)
theorem B3922901 : Blo 1032607 3922901 := bbase (se 7 (by rfl) ⟨45971, by rfl⟩ : syracuseStep 3922901 = 91943) (by norm_num)
theorem B5233733 : Blo 1032607 5233733 := bbase (se 4 (by rfl) ⟨490662, by rfl⟩ : syracuseStep 5233733 = 981325) (by norm_num)
theorem B3497093 : Blo 1032607 3497093 := bbase (se 4 (by rfl) ⟨327852, by rfl⟩ : syracuseStep 3497093 = 655705) (by norm_num)
theorem B1105093 : Blo 1032607 1105093 := bbase (se 4 (by rfl) ⟨103602, by rfl⟩ : syracuseStep 1105093 = 207205) (by norm_num)
theorem B14736725 : Blo 1032607 14736725 := bbase (se 11 (by rfl) ⟨10793, by rfl⟩ : syracuseStep 14736725 = 21587) (by norm_num)
theorem B4971941 : Blo 1032607 4971941 := bbase (se 4 (by rfl) ⟨466119, by rfl⟩ : syracuseStep 4971941 = 932239) (by norm_num)
theorem B1400261 : Blo 1032607 1400261 := bbase (se 4 (by rfl) ⟨131274, by rfl⟩ : syracuseStep 1400261 = 262549) (by norm_num)
theorem B3497525 : Blo 1032607 3497525 := bbase (se 5 (by rfl) ⟨163946, by rfl⟩ : syracuseStep 3497525 = 327893) (by norm_num)
theorem B1105525 : Blo 1032607 1105525 := bbase (se 5 (by rfl) ⟨51821, by rfl⟩ : syracuseStep 1105525 = 103643) (by norm_num)
theorem B1105597 : Blo 1032607 1105597 := bbase (se 3 (by rfl) ⟨207299, by rfl⟩ : syracuseStep 1105597 = 414599) (by norm_num)
theorem B3497957 : Blo 1032607 3497957 := bbase (se 4 (by rfl) ⟨327933, by rfl⟩ : syracuseStep 3497957 = 655867) (by norm_num)
theorem B1105969 : Blo 1032607 1105969 := bbase (se 2 (by rfl) ⟨414738, by rfl⟩ : syracuseStep 1105969 = 829477) (by norm_num)
theorem B3924085 : Blo 1032607 3924085 := bbase (se 5 (by rfl) ⟨183941, by rfl⟩ : syracuseStep 3924085 = 367883) (by norm_num)
theorem B5890229 : Blo 1032607 5890229 := bbase (se 5 (by rfl) ⟨276104, by rfl⟩ : syracuseStep 5890229 = 552209) (by norm_num)
theorem B13263061 : Blo 1032607 13263061 := bbase (se 7 (by rfl) ⟨155426, by rfl⟩ : syracuseStep 13263061 = 310853) (by norm_num)
theorem B2515261 : Blo 1032607 2515261 := bbase (se 3 (by rfl) ⟨471611, by rfl⟩ : syracuseStep 2515261 = 943223) (by norm_num)
theorem B5235029 : Blo 1032607 5235029 := bbase (se 10 (by rfl) ⟨7668, by rfl⟩ : syracuseStep 5235029 = 15337) (by norm_num)
theorem B3498389 : Blo 1032607 3498389 := bbase (se 6 (by rfl) ⟨81993, by rfl⟩ : syracuseStep 3498389 = 163987) (by norm_num)
theorem B3924389 : Blo 1032607 3924389 := bbase (se 4 (by rfl) ⟨367911, by rfl⟩ : syracuseStep 3924389 = 735823) (by norm_num)
theorem B1106345 : Blo 1032607 1106345 := bbase (se 2 (by rfl) ⟨414879, by rfl⟩ : syracuseStep 1106345 = 829759) (by norm_num)
theorem B1106417 : Blo 1032607 1106417 := bbase (se 2 (by rfl) ⟨414906, by rfl⟩ : syracuseStep 1106417 = 829813) (by norm_num)
theorem B2482741 : Blo 1032607 2482741 := bbase (se 5 (by rfl) ⟨116378, by rfl⟩ : syracuseStep 2482741 = 232757) (by norm_num)
theorem B2613829 : Blo 1032607 2613829 := bbase (se 4 (by rfl) ⟨245046, by rfl⟩ : syracuseStep 2613829 = 490093) (by norm_num)
theorem B1892965 : Blo 1032607 1892965 := bbase (se 4 (by rfl) ⟨177465, by rfl⟩ : syracuseStep 1892965 = 354931) (by norm_num)
theorem B1106605 : Blo 1032607 1106605 := bbase (se 3 (by rfl) ⟨207488, by rfl⟩ : syracuseStep 1106605 = 414977) (by norm_num)
theorem B2613941 : Blo 1032607 2613941 := bbase (se 5 (by rfl) ⟨122528, by rfl⟩ : syracuseStep 2613941 = 245057) (by norm_num)
theorem B1106789 : Blo 1032607 1106789 := bbase (se 4 (by rfl) ⟨103761, by rfl⟩ : syracuseStep 1106789 = 207523) (by norm_num)
theorem B2614133 : Blo 1032607 2614133 := bbase (se 5 (by rfl) ⟨122537, by rfl⟩ : syracuseStep 2614133 = 245075) (by norm_num)
theorem B4416373 : Blo 1032607 4416373 := bbase (se 5 (by rfl) ⟨207017, by rfl⟩ : syracuseStep 4416373 = 414035) (by norm_num)
theorem B2483077 : Blo 1032607 2483077 := bbase (se 4 (by rfl) ⟨232788, by rfl⟩ : syracuseStep 2483077 = 465577) (by norm_num)
theorem B2614477 : Blo 1032607 2614477 := bbase (se 3 (by rfl) ⟨490214, by rfl⟩ : syracuseStep 2614477 = 980429) (by norm_num)
theorem B2614589 : Blo 1032607 2614589 := bbase (se 3 (by rfl) ⟨490235, by rfl⟩ : syracuseStep 2614589 = 980471) (by norm_num)
theorem B5891413 : Blo 1032607 5891413 := bbase (se 12 (by rfl) ⟨2157, by rfl⟩ : syracuseStep 5891413 = 4315) (by norm_num)
theorem B1795421 : Blo 1032607 1795421 := bbase (se 3 (by rfl) ⟨336641, by rfl⟩ : syracuseStep 1795421 = 673283) (by norm_num)
theorem B9954677 : Blo 1032607 9954677 := bbase (se 5 (by rfl) ⟨466625, by rfl⟩ : syracuseStep 9954677 = 933251) (by norm_num)
theorem B4973957 : Blo 1032607 4973957 := bbase (se 4 (by rfl) ⟨466308, by rfl⟩ : syracuseStep 4973957 = 932617) (by norm_num)
theorem B2483693 : Blo 1032607 2483693 := bbase (se 3 (by rfl) ⟨465692, by rfl⟩ : syracuseStep 2483693 = 931385) (by norm_num)
theorem B2614781 : Blo 1032607 2614781 := bbase (se 3 (by rfl) ⟨490271, by rfl⟩ : syracuseStep 2614781 = 980543) (by norm_num)
theorem B4974149 : Blo 1032607 4974149 := bbase (se 4 (by rfl) ⟨466326, by rfl⟩ : syracuseStep 4974149 = 932653) (by norm_num)
theorem B5236325 : Blo 1032607 5236325 := bbase (se 4 (by rfl) ⟨490905, by rfl⟩ : syracuseStep 5236325 = 981811) (by norm_num)
theorem B8382133 : Blo 1032607 8382133 := bbase (se 5 (by rfl) ⟨392912, by rfl⟩ : syracuseStep 8382133 = 785825) (by norm_num)
theorem B4712165 : Blo 1032607 4712165 := bbase (se 4 (by rfl) ⟨441765, by rfl⟩ : syracuseStep 4712165 = 883531) (by norm_num)
theorem B2615125 : Blo 1032607 2615125 := bbase (se 9 (by rfl) ⟨7661, by rfl⟩ : syracuseStep 2615125 = 15323) (by norm_num)
theorem B2942837 : Blo 1032607 2942837 := bbase (se 5 (by rfl) ⟨137945, by rfl⟩ : syracuseStep 2942837 = 275891) (by norm_num)
theorem B11495317 : Blo 1032607 11495317 := bbase (se 6 (by rfl) ⟨269421, by rfl⟩ : syracuseStep 11495317 = 538843) (by norm_num)
theorem B14903189 : Blo 1032607 14903189 := bbase (se 6 (by rfl) ⟨349293, by rfl⟩ : syracuseStep 14903189 = 698587) (by norm_num)
theorem B2484125 : Blo 1032607 2484125 := bbase (se 3 (by rfl) ⟨465773, by rfl⟩ : syracuseStep 2484125 = 931547) (by norm_num)
theorem B2615237 : Blo 1032607 2615237 := bbase (se 4 (by rfl) ⟨245178, by rfl⟩ : syracuseStep 2615237 = 490357) (by norm_num)
theorem B7858133 : Blo 1032607 7858133 := bbase (se 7 (by rfl) ⟨92087, by rfl⟩ : syracuseStep 7858133 = 184175) (by norm_num)
theorem B4188149 : Blo 1032607 4188149 := bbase (se 5 (by rfl) ⟨196319, by rfl⟩ : syracuseStep 4188149 = 392639) (by norm_num)
theorem B2517013 : Blo 1032607 2517013 := bbase (se 6 (by rfl) ⟨58992, by rfl⟩ : syracuseStep 2517013 = 117985) (by norm_num)
theorem B1861717 : Blo 1032607 1861717 := bbase (se 8 (by rfl) ⟨10908, by rfl⟩ : syracuseStep 1861717 = 21817) (by norm_num)
theorem B2615429 : Blo 1032607 2615429 := bbase (se 4 (by rfl) ⟨245196, by rfl⟩ : syracuseStep 2615429 = 490393) (by norm_num)
theorem B23914709 : Blo 1032607 23914709 := bbase (se 7 (by rfl) ⟨280250, by rfl⟩ : syracuseStep 23914709 = 560501) (by norm_num)
theorem B1861861 : Blo 1032607 1861861 := bbase (se 4 (by rfl) ⟨174549, by rfl⟩ : syracuseStep 1861861 = 349099) (by norm_num)
theorem B4417861 : Blo 1032607 4417861 := bbase (se 4 (by rfl) ⟨414174, by rfl⟩ : syracuseStep 4417861 = 828349) (by norm_num)
theorem B4417877 : Blo 1032607 4417877 := bbase (se 10 (by rfl) ⟨6471, by rfl⟩ : syracuseStep 4417877 = 12943) (by norm_num)
theorem B1862021 : Blo 1032607 1862021 := bbase (se 4 (by rfl) ⟨174564, by rfl⟩ : syracuseStep 1862021 = 349129) (by norm_num)
theorem B1960357 : Blo 1032607 1960357 := bbase (se 4 (by rfl) ⟨183783, by rfl⟩ : syracuseStep 1960357 = 367567) (by norm_num)
theorem B1862077 : Blo 1032607 1862077 := bbase (se 3 (by rfl) ⟨349139, by rfl⟩ : syracuseStep 1862077 = 698279) (by norm_num)
theorem B2615773 : Blo 1032607 2615773 := bbase (se 3 (by rfl) ⟨490457, by rfl⟩ : syracuseStep 2615773 = 980915) (by norm_num)
theorem B3926501 : Blo 1032607 3926501 := bbase (se 4 (by rfl) ⟨368109, by rfl⟩ : syracuseStep 3926501 = 736219) (by norm_num)
theorem B2484749 : Blo 1032607 2484749 := bbase (se 3 (by rfl) ⟨465890, by rfl⟩ : syracuseStep 2484749 = 931781) (by norm_num)
theorem B1960517 : Blo 1032607 1960517 := bbase (se 4 (by rfl) ⟨183798, by rfl⟩ : syracuseStep 1960517 = 367597) (by norm_num)
theorem B2615885 : Blo 1032607 2615885 := bbase (se 3 (by rfl) ⟨490478, by rfl⟩ : syracuseStep 2615885 = 980957) (by norm_num)
theorem B2517637 : Blo 1032607 2517637 := bbase (se 4 (by rfl) ⟨236028, by rfl⟩ : syracuseStep 2517637 = 472057) (by norm_num)
theorem B1960661 : Blo 1032607 1960661 := bbase (se 7 (by rfl) ⟨22976, by rfl⟩ : syracuseStep 1960661 = 45953) (by norm_num)
theorem B3926789 : Blo 1032607 3926789 := bbase (se 4 (by rfl) ⟨368136, by rfl⟩ : syracuseStep 3926789 = 736273) (by norm_num)
theorem B2616077 : Blo 1032607 2616077 := bbase (se 3 (by rfl) ⟨490514, by rfl⟩ : syracuseStep 2616077 = 981029) (by norm_num)
theorem B5237621 : Blo 1032607 5237621 := bbase (se 5 (by rfl) ⟨245513, by rfl⟩ : syracuseStep 5237621 = 491027) (by norm_num)
theorem B1960949 : Blo 1032607 1960949 := bbase (se 5 (by rfl) ⟨91919, by rfl⟩ : syracuseStep 1960949 = 183839) (by norm_num)
theorem B2944021 : Blo 1032607 2944021 := bbase (se 6 (by rfl) ⟨69000, by rfl⟩ : syracuseStep 2944021 = 138001) (by norm_num)
theorem B2616421 : Blo 1032607 2616421 := bbase (se 4 (by rfl) ⟨245289, by rfl⟩ : syracuseStep 2616421 = 490579) (by norm_num)
theorem B1961101 : Blo 1032607 1961101 := bbase (se 3 (by rfl) ⟨367706, by rfl⟩ : syracuseStep 1961101 = 735413) (by norm_num)
theorem B1993877 : Blo 1032607 1993877 := bbase (se 6 (by rfl) ⟨46731, by rfl⟩ : syracuseStep 1993877 = 93463) (by norm_num)
theorem B2944181 : Blo 1032607 2944181 := bbase (se 5 (by rfl) ⟨138008, by rfl⟩ : syracuseStep 2944181 = 276017) (by norm_num)
theorem B2616533 : Blo 1032607 2616533 := bbase (se 7 (by rfl) ⟨30662, by rfl⟩ : syracuseStep 2616533 = 61325) (by norm_num)
theorem B3140869 : Blo 1032607 3140869 := bbase (se 4 (by rfl) ⟨294456, by rfl⟩ : syracuseStep 3140869 = 588913) (by norm_num)
theorem B5893397 : Blo 1032607 5893397 := bbase (se 6 (by rfl) ⟨138126, by rfl⟩ : syracuseStep 5893397 = 276253) (by norm_num)
theorem B3140965 : Blo 1032607 3140965 := bbase (se 4 (by rfl) ⟨294465, by rfl⟩ : syracuseStep 3140965 = 588931) (by norm_num)
theorem B7466357 : Blo 1032607 7466357 := bbase (se 5 (by rfl) ⟨349985, by rfl⟩ : syracuseStep 7466357 = 699971) (by norm_num)
theorem B2616725 : Blo 1032607 2616725 := bbase (se 6 (by rfl) ⟨61329, by rfl⟩ : syracuseStep 2616725 = 122659) (by norm_num)
theorem B2944421 : Blo 1032607 2944421 := bbase (se 4 (by rfl) ⟨276039, by rfl⟩ : syracuseStep 2944421 = 552079) (by norm_num)
theorem B1961405 : Blo 1032607 1961405 := bbase (se 3 (by rfl) ⟨367763, by rfl⟩ : syracuseStep 1961405 = 735527) (by norm_num)
theorem B1240529 : Blo 1032607 1240529 := bbase (se 2 (by rfl) ⟨465198, by rfl⟩ : syracuseStep 1240529 = 930397) (by norm_num)
theorem B1863245 : Blo 1032607 1863245 := bbase (se 3 (by rfl) ⟨349358, by rfl⟩ : syracuseStep 1863245 = 698717) (by norm_num)
theorem B2944613 : Blo 1032607 2944613 := bbase (se 4 (by rfl) ⟨276057, by rfl⟩ : syracuseStep 2944613 = 552115) (by norm_num)
theorem B4976245 : Blo 1032607 4976245 := bbase (se 5 (by rfl) ⟨233261, by rfl⟩ : syracuseStep 4976245 = 466523) (by norm_num)
theorem B2617069 : Blo 1032607 2617069 := bbase (se 3 (by rfl) ⟨490700, by rfl⟩ : syracuseStep 2617069 = 981401) (by norm_num)
theorem B2617181 : Blo 1032607 2617181 := bbase (se 3 (by rfl) ⟨490721, by rfl⟩ : syracuseStep 2617181 = 981443) (by norm_num)
theorem B1470325 : Blo 1032607 1470325 := bbase (se 5 (by rfl) ⟨68921, by rfl⟩ : syracuseStep 1470325 = 137843) (by norm_num)
theorem B3927973 : Blo 1032607 3927973 := bbase (se 4 (by rfl) ⟨368247, by rfl⟩ : syracuseStep 3927973 = 736495) (by norm_num)
theorem B1241029 : Blo 1032607 1241029 := bbase (se 4 (by rfl) ⟨116346, by rfl⟩ : syracuseStep 1241029 = 232693) (by norm_num)
theorem B2617373 : Blo 1032607 2617373 := bbase (se 3 (by rfl) ⟨490757, by rfl⟩ : syracuseStep 2617373 = 981515) (by norm_num)
theorem B5238917 : Blo 1032607 5238917 := bbase (se 4 (by rfl) ⟨491148, by rfl⟩ : syracuseStep 5238917 = 982297) (by norm_num)
theorem B1962157 : Blo 1032607 1962157 := bbase (se 3 (by rfl) ⟨367904, by rfl⟩ : syracuseStep 1962157 = 735809) (by norm_num)
theorem B3928277 : Blo 1032607 3928277 := bbase (se 7 (by rfl) ⟨46034, by rfl⟩ : syracuseStep 3928277 = 92069) (by norm_num)
theorem B1863901 : Blo 1032607 1863901 := bbase (se 3 (by rfl) ⟨349481, by rfl⟩ : syracuseStep 1863901 = 698963) (by norm_num)
theorem B1863965 : Blo 1032607 1863965 := bbase (se 3 (by rfl) ⟨349493, by rfl⟩ : syracuseStep 1863965 = 698987) (by norm_num)
theorem B4714805 : Blo 1032607 4714805 := bbase (se 5 (by rfl) ⟨221006, by rfl⟩ : syracuseStep 4714805 = 442013) (by norm_num)
theorem B1962301 : Blo 1032607 1962301 := bbase (se 3 (by rfl) ⟨367931, by rfl⟩ : syracuseStep 1962301 = 735863) (by norm_num)
theorem B1306945 : Blo 1032607 1306945 := bbase (se 2 (by rfl) ⟨490104, by rfl⟩ : syracuseStep 1306945 = 980209) (by norm_num)
theorem B1241413 : Blo 1032607 1241413 := bbase (se 4 (by rfl) ⟨116382, by rfl⟩ : syracuseStep 1241413 = 232765) (by norm_num)
theorem B2617717 : Blo 1032607 2617717 := bbase (se 5 (by rfl) ⟨122705, by rfl⟩ : syracuseStep 2617717 = 245411) (by norm_num)
theorem B1470917 : Blo 1032607 1470917 := bbase (se 4 (by rfl) ⟨137898, by rfl⟩ : syracuseStep 1470917 = 275797) (by norm_num)
theorem B1962461 : Blo 1032607 1962461 := bbase (se 3 (by rfl) ⟨367961, by rfl⟩ : syracuseStep 1962461 = 735923) (by norm_num)
theorem B2617829 : Blo 1032607 2617829 := bbase (se 4 (by rfl) ⟨245421, by rfl⟩ : syracuseStep 2617829 = 490843) (by norm_num)
theorem B1307117 : Blo 1032607 1307117 := bbase (se 3 (by rfl) ⟨245084, by rfl⟩ : syracuseStep 1307117 = 490169) (by norm_num)
theorem B1470997 : Blo 1032607 1470997 := bbase (se 6 (by rfl) ⟨34476, by rfl⟩ : syracuseStep 1470997 = 68953) (by norm_num)
theorem B1307173 : Blo 1032607 1307173 := bbase (se 4 (by rfl) ⟨122547, by rfl⟩ : syracuseStep 1307173 = 245095) (by norm_num)
theorem B4420133 : Blo 1032607 4420133 := bbase (se 4 (by rfl) ⟨414387, by rfl⟩ : syracuseStep 4420133 = 828775) (by norm_num)
theorem B2945605 : Blo 1032607 2945605 := bbase (se 4 (by rfl) ⟨276150, by rfl⟩ : syracuseStep 2945605 = 552301) (by norm_num)
theorem B1962605 : Blo 1032607 1962605 := bbase (se 3 (by rfl) ⟨367988, by rfl⟩ : syracuseStep 1962605 = 735977) (by norm_num)
theorem B1307269 : Blo 1032607 1307269 := bbase (se 4 (by rfl) ⟨122556, by rfl⟩ : syracuseStep 1307269 = 245113) (by norm_num)
theorem B1471117 : Blo 1032607 1471117 := bbase (se 3 (by rfl) ⟨275834, by rfl⟩ : syracuseStep 1471117 = 551669) (by norm_num)
theorem B2618021 : Blo 1032607 2618021 := bbase (se 4 (by rfl) ⟨245439, by rfl⟩ : syracuseStep 2618021 = 490879) (by norm_num)
theorem B1471213 : Blo 1032607 1471213 := bbase (se 3 (by rfl) ⟨275852, by rfl⟩ : syracuseStep 1471213 = 551705) (by norm_num)
theorem B1307441 : Blo 1032607 1307441 := bbase (se 2 (by rfl) ⟨490290, by rfl⟩ : syracuseStep 1307441 = 980581) (by norm_num)
theorem B2356037 : Blo 1032607 2356037 := bbase (se 4 (by rfl) ⟨220878, by rfl⟩ : syracuseStep 2356037 = 441757) (by norm_num)
theorem B1307497 : Blo 1032607 1307497 := bbase (se 2 (by rfl) ⟨490311, by rfl⟩ : syracuseStep 1307497 = 980623) (by norm_num)
theorem B1962893 : Blo 1032607 1962893 := bbase (se 3 (by rfl) ⟨368042, by rfl⟩ : syracuseStep 1962893 = 736085) (by norm_num)
theorem B1307593 : Blo 1032607 1307593 := bbase (se 2 (by rfl) ⟨490347, by rfl⟩ : syracuseStep 1307593 = 980695) (by norm_num)
theorem B2323421 : Blo 1032607 2323421 := bbase (se 3 (by rfl) ⟨435641, by rfl⟩ : syracuseStep 2323421 = 871283) (by norm_num)
theorem B2618365 : Blo 1032607 2618365 := bbase (se 3 (by rfl) ⟨490943, by rfl⟩ : syracuseStep 2618365 = 981887) (by norm_num)
theorem B2323493 : Blo 1032607 2323493 := bbase (se 4 (by rfl) ⟨217827, by rfl⟩ : syracuseStep 2323493 = 435655) (by norm_num)
theorem B1963045 : Blo 1032607 1963045 := bbase (se 4 (by rfl) ⟨184035, by rfl⟩ : syracuseStep 1963045 = 368071) (by norm_num)
theorem B3142709 : Blo 1032607 3142709 := bbase (se 5 (by rfl) ⟨147314, by rfl⟩ : syracuseStep 3142709 = 294629) (by norm_num)
theorem B2323565 : Blo 1032607 2323565 := bbase (se 3 (by rfl) ⟨435668, by rfl⟩ : syracuseStep 2323565 = 871337) (by norm_num)
theorem B2618477 : Blo 1032607 2618477 := bbase (se 3 (by rfl) ⟨490964, by rfl⟩ : syracuseStep 2618477 = 981929) (by norm_num)
theorem B1307765 : Blo 1032607 1307765 := bbase (se 5 (by rfl) ⟨61301, by rfl⟩ : syracuseStep 1307765 = 122603) (by norm_num)
theorem B1307821 : Blo 1032607 1307821 := bbase (se 3 (by rfl) ⟨245216, by rfl⟩ : syracuseStep 1307821 = 490433) (by norm_num)
theorem B2323637 : Blo 1032607 2323637 := bbase (se 5 (by rfl) ⟨108920, by rfl⟩ : syracuseStep 2323637 = 217841) (by norm_num)
theorem B1242317 : Blo 1032607 1242317 := bbase (se 3 (by rfl) ⟨232934, by rfl⟩ : syracuseStep 1242317 = 465869) (by norm_num)
theorem B1471709 : Blo 1032607 1471709 := bbase (se 3 (by rfl) ⟨275945, by rfl⟩ : syracuseStep 1471709 = 551891) (by norm_num)
theorem B2323709 : Blo 1032607 2323709 := bbase (se 3 (by rfl) ⟨435695, by rfl⟩ : syracuseStep 2323709 = 871391) (by norm_num)
theorem B1307917 : Blo 1032607 1307917 := bbase (se 3 (by rfl) ⟨245234, by rfl⟩ : syracuseStep 1307917 = 490469) (by norm_num)
theorem B2618669 : Blo 1032607 2618669 := bbase (se 3 (by rfl) ⟨491000, by rfl⟩ : syracuseStep 2618669 = 982001) (by norm_num)
theorem B2323781 : Blo 1032607 2323781 := bbase (se 4 (by rfl) ⟨217854, by rfl⟩ : syracuseStep 2323781 = 435709) (by norm_num)
theorem B1963349 : Blo 1032607 1963349 := bbase (se 13 (by rfl) ⟨359, by rfl⟩ : syracuseStep 1963349 = 719) (by norm_num)
theorem B2323853 : Blo 1032607 2323853 := bbase (se 3 (by rfl) ⟨435722, by rfl⟩ : syracuseStep 2323853 = 871445) (by norm_num)
theorem B5240213 : Blo 1032607 5240213 := bbase (se 6 (by rfl) ⟨122817, by rfl⟩ : syracuseStep 5240213 = 245635) (by norm_num)
theorem B2553245 : Blo 1032607 2553245 := bbase (se 3 (by rfl) ⟨478733, by rfl⟩ : syracuseStep 2553245 = 957467) (by norm_num)
theorem B2487709 : Blo 1032607 2487709 := bbase (se 3 (by rfl) ⟨466445, by rfl⟩ : syracuseStep 2487709 = 932891) (by norm_num)
theorem B5895605 : Blo 1032607 5895605 := bbase (se 5 (by rfl) ⟨276356, by rfl⟩ : syracuseStep 5895605 = 552713) (by norm_num)
theorem B1308089 : Blo 1032607 1308089 := bbase (se 2 (by rfl) ⟨490533, by rfl⟩ : syracuseStep 1308089 = 981067) (by norm_num)
theorem B1242577 : Blo 1032607 1242577 := bbase (se 2 (by rfl) ⟨465966, by rfl⟩ : syracuseStep 1242577 = 931933) (by norm_num)
theorem B2323925 : Blo 1032607 2323925 := bbase (se 7 (by rfl) ⟨27233, by rfl⟩ : syracuseStep 2323925 = 54467) (by norm_num)
theorem B1308145 : Blo 1032607 1308145 := bbase (se 2 (by rfl) ⟨490554, by rfl⟩ : syracuseStep 1308145 = 981109) (by norm_num)
theorem B6616565 : Blo 1032607 6616565 := bbase (se 5 (by rfl) ⟨310151, by rfl⟩ : syracuseStep 6616565 = 620303) (by norm_num)
theorem B2323997 : Blo 1032607 2323997 := bbase (se 3 (by rfl) ⟨435749, by rfl⟩ : syracuseStep 2323997 = 871499) (by norm_num)
theorem B1308241 : Blo 1032607 1308241 := bbase (se 2 (by rfl) ⟨490590, by rfl⟩ : syracuseStep 1308241 = 981181) (by norm_num)
theorem B2651741 : Blo 1032607 2651741 := bbase (se 3 (by rfl) ⟨497201, by rfl⟩ : syracuseStep 2651741 = 994403) (by norm_num)
theorem B2487901 : Blo 1032607 2487901 := bbase (se 3 (by rfl) ⟨466481, by rfl⟩ : syracuseStep 2487901 = 932963) (by norm_num)
theorem B2324069 : Blo 1032607 2324069 := bbase (se 4 (by rfl) ⟨217881, by rfl⟩ : syracuseStep 2324069 = 435763) (by norm_num)
theorem B4191845 : Blo 1032607 4191845 := bbase (se 4 (by rfl) ⟨392985, by rfl⟩ : syracuseStep 4191845 = 785971) (by norm_num)
theorem B2619013 : Blo 1032607 2619013 := bbase (se 4 (by rfl) ⟨245532, by rfl⟩ : syracuseStep 2619013 = 491065) (by norm_num)
theorem B2487941 : Blo 1032607 2487941 := bbase (se 4 (by rfl) ⟨233244, by rfl⟩ : syracuseStep 2487941 = 466489) (by norm_num)
theorem B1242769 : Blo 1032607 1242769 := bbase (se 2 (by rfl) ⟨466038, by rfl⟩ : syracuseStep 1242769 = 932077) (by norm_num)
theorem B2946709 : Blo 1032607 2946709 := bbase (se 6 (by rfl) ⟨69063, by rfl⟩ : syracuseStep 2946709 = 138127) (by norm_num)
theorem B1242793 : Blo 1032607 1242793 := bbase (se 2 (by rfl) ⟨466047, by rfl⟩ : syracuseStep 1242793 = 932095) (by norm_num)
theorem B2324141 : Blo 1032607 2324141 := bbase (se 3 (by rfl) ⟨435776, by rfl⟩ : syracuseStep 2324141 = 871553) (by norm_num)
theorem B1242797 : Blo 1032607 1242797 := bbase (se 3 (by rfl) ⟨233024, by rfl⟩ : syracuseStep 1242797 = 466049) (by norm_num)
theorem B2324213 : Blo 1032607 2324213 := bbase (se 5 (by rfl) ⟨108947, by rfl⟩ : syracuseStep 2324213 = 217895) (by norm_num)
theorem B2619125 : Blo 1032607 2619125 := bbase (se 5 (by rfl) ⟨122771, by rfl⟩ : syracuseStep 2619125 = 245543) (by norm_num)
theorem B1308413 : Blo 1032607 1308413 := bbase (se 3 (by rfl) ⟨245327, by rfl⟩ : syracuseStep 1308413 = 490655) (by norm_num)
theorem B1472261 : Blo 1032607 1472261 := bbase (se 4 (by rfl) ⟨138024, by rfl⟩ : syracuseStep 1472261 = 276049) (by norm_num)
theorem B1308469 : Blo 1032607 1308469 := bbase (se 5 (by rfl) ⟨61334, by rfl⟩ : syracuseStep 1308469 = 122669) (by norm_num)
theorem B2324285 : Blo 1032607 2324285 := bbase (se 3 (by rfl) ⟨435803, by rfl⟩ : syracuseStep 2324285 = 871607) (by norm_num)
theorem B2324357 : Blo 1032607 2324357 := bbase (se 4 (by rfl) ⟨217908, by rfl⟩ : syracuseStep 2324357 = 435817) (by norm_num)
theorem B3536789 : Blo 1032607 3536789 := bbase (se 6 (by rfl) ⟨82893, by rfl⟩ : syracuseStep 3536789 = 165787) (by norm_num)
theorem B1308565 : Blo 1032607 1308565 := bbase (se 6 (by rfl) ⟨30669, by rfl⟩ : syracuseStep 1308565 = 61339) (by norm_num)
theorem B2488229 : Blo 1032607 2488229 := bbase (se 4 (by rfl) ⟨233271, by rfl⟩ : syracuseStep 2488229 = 466543) (by norm_num)
theorem B1767341 : Blo 1032607 1767341 := bbase (se 3 (by rfl) ⟨331376, by rfl⟩ : syracuseStep 1767341 = 662753) (by norm_num)
theorem B2619317 : Blo 1032607 2619317 := bbase (se 5 (by rfl) ⟨122780, by rfl⟩ : syracuseStep 2619317 = 245561) (by norm_num)
theorem B2324429 : Blo 1032607 2324429 := bbase (se 3 (by rfl) ⟨435830, by rfl⟩ : syracuseStep 2324429 = 871661) (by norm_num)
theorem B2324501 : Blo 1032607 2324501 := bbase (se 6 (by rfl) ⟨54480, by rfl⟩ : syracuseStep 2324501 = 108961) (by norm_num)
theorem B1308737 : Blo 1032607 1308737 := bbase (se 2 (by rfl) ⟨490776, by rfl⟩ : syracuseStep 1308737 = 981553) (by norm_num)
theorem B1964101 : Blo 1032607 1964101 := bbase (se 4 (by rfl) ⟨184134, by rfl⟩ : syracuseStep 1964101 = 368269) (by norm_num)
theorem B2324573 : Blo 1032607 2324573 := bbase (se 3 (by rfl) ⟨435857, by rfl⟩ : syracuseStep 2324573 = 871715) (by norm_num)
theorem B1308793 : Blo 1032607 1308793 := bbase (se 2 (by rfl) ⟨490797, by rfl⟩ : syracuseStep 1308793 = 981595) (by norm_num)
theorem B1243297 : Blo 1032607 1243297 := bbase (se 2 (by rfl) ⟨466236, by rfl⟩ : syracuseStep 1243297 = 932473) (by norm_num)
theorem B2324645 : Blo 1032607 2324645 := bbase (se 4 (by rfl) ⟨217935, by rfl⟩ : syracuseStep 2324645 = 435871) (by norm_num)
theorem B1046729 : Blo 1032607 1046729 := bbase (se 2 (by rfl) ⟨392523, by rfl⟩ : syracuseStep 1046729 = 785047) (by norm_num)
theorem B1964245 : Blo 1032607 1964245 := bbase (se 7 (by rfl) ⟨23018, by rfl⟩ : syracuseStep 1964245 = 46037) (by norm_num)
theorem B1308889 : Blo 1032607 1308889 := bbase (se 2 (by rfl) ⟨490833, by rfl⟩ : syracuseStep 1308889 = 981667) (by norm_num)
theorem B2324717 : Blo 1032607 2324717 := bbase (se 3 (by rfl) ⟨435884, by rfl⟩ : syracuseStep 2324717 = 871769) (by norm_num)
theorem B1243393 : Blo 1032607 1243393 := bbase (se 2 (by rfl) ⟨466272, by rfl⟩ : syracuseStep 1243393 = 932545) (by norm_num)
theorem B2619661 : Blo 1032607 2619661 := bbase (se 3 (by rfl) ⟨491186, by rfl⟩ : syracuseStep 2619661 = 982373) (by norm_num)
theorem B3930389 : Blo 1032607 3930389 := bbase (se 6 (by rfl) ⟨92118, by rfl⟩ : syracuseStep 3930389 = 184237) (by norm_num)
theorem B2324789 : Blo 1032607 2324789 := bbase (se 5 (by rfl) ⟨108974, by rfl⟩ : syracuseStep 2324789 = 217949) (by norm_num)
theorem B1964405 : Blo 1032607 1964405 := bbase (se 5 (by rfl) ⟨92081, by rfl⟩ : syracuseStep 1964405 = 184163) (by norm_num)
theorem B2324861 : Blo 1032607 2324861 := bbase (se 3 (by rfl) ⟨435911, by rfl⟩ : syracuseStep 2324861 = 871823) (by norm_num)
theorem B2619773 : Blo 1032607 2619773 := bbase (se 3 (by rfl) ⟨491207, by rfl⟩ : syracuseStep 2619773 = 982415) (by norm_num)
theorem B1309061 : Blo 1032607 1309061 := bbase (se 4 (by rfl) ⟨122724, by rfl⟩ : syracuseStep 1309061 = 245449) (by norm_num)
theorem B1571213 : Blo 1032607 1571213 := bbase (se 3 (by rfl) ⟨294602, by rfl⟩ : syracuseStep 1571213 = 589205) (by norm_num)
theorem B4192661 : Blo 1032607 4192661 := bbase (se 6 (by rfl) ⟨98265, by rfl⟩ : syracuseStep 4192661 = 196531) (by norm_num)
theorem B1309117 : Blo 1032607 1309117 := bbase (se 3 (by rfl) ⟨245459, by rfl⟩ : syracuseStep 1309117 = 490919) (by norm_num)
theorem B2324933 : Blo 1032607 2324933 := bbase (se 4 (by rfl) ⟨217962, by rfl⟩ : syracuseStep 2324933 = 435925) (by norm_num)
theorem B1473013 : Blo 1032607 1473013 := bbase (se 5 (by rfl) ⟨69047, by rfl⟩ : syracuseStep 1473013 = 138095) (by norm_num)
theorem B1964549 : Blo 1032607 1964549 := bbase (se 4 (by rfl) ⟨184176, by rfl⟩ : syracuseStep 1964549 = 368353) (by norm_num)
theorem B2325005 : Blo 1032607 2325005 := bbase (se 3 (by rfl) ⟨435938, by rfl⟩ : syracuseStep 2325005 = 871877) (by norm_num)
theorem B1309213 : Blo 1032607 1309213 := bbase (se 3 (by rfl) ⟨245477, by rfl⟩ : syracuseStep 1309213 = 490955) (by norm_num)
theorem B3930677 : Blo 1032607 3930677 := bbase (se 5 (by rfl) ⟨184250, by rfl⟩ : syracuseStep 3930677 = 368501) (by norm_num)
theorem B2619965 : Blo 1032607 2619965 := bbase (se 3 (by rfl) ⟨491243, by rfl⟩ : syracuseStep 2619965 = 982487) (by norm_num)
theorem B2325077 : Blo 1032607 2325077 := bbase (se 8 (by rfl) ⟨13623, by rfl⟩ : syracuseStep 2325077 = 27247) (by norm_num)
theorem B2325149 : Blo 1032607 2325149 := bbase (se 3 (by rfl) ⟨435965, by rfl⟩ : syracuseStep 2325149 = 871931) (by norm_num)
theorem B5241509 : Blo 1032607 5241509 := bbase (se 4 (by rfl) ⟨491391, by rfl⟩ : syracuseStep 5241509 = 982783) (by norm_num)
theorem B1309385 : Blo 1032607 1309385 := bbase (se 2 (by rfl) ⟨491019, by rfl⟩ : syracuseStep 1309385 = 982039) (by norm_num)
theorem B2325221 : Blo 1032607 2325221 := bbase (se 4 (by rfl) ⟨217989, by rfl⟩ : syracuseStep 2325221 = 435979) (by norm_num)
theorem B1309441 : Blo 1032607 1309441 := bbase (se 2 (by rfl) ⟨491040, by rfl⟩ : syracuseStep 1309441 = 982081) (by norm_num)
theorem B3308309 : Blo 1032607 3308309 := bbase (se 6 (by rfl) ⟨77538, by rfl⟩ : syracuseStep 3308309 = 155077) (by norm_num)
theorem B1964837 : Blo 1032607 1964837 := bbase (se 4 (by rfl) ⟨184203, by rfl⟩ : syracuseStep 1964837 = 368407) (by norm_num)
theorem B2325293 : Blo 1032607 2325293 := bbase (se 3 (by rfl) ⟨435992, by rfl⟩ : syracuseStep 2325293 = 871985) (by norm_num)
theorem B1309537 : Blo 1032607 1309537 := bbase (se 2 (by rfl) ⟨491076, by rfl⟩ : syracuseStep 1309537 = 982153) (by norm_num)
theorem B2325365 : Blo 1032607 2325365 := bbase (se 5 (by rfl) ⟨109001, by rfl⟩ : syracuseStep 2325365 = 218003) (by norm_num)
theorem B2620309 : Blo 1032607 2620309 := bbase (se 6 (by rfl) ⟨61413, by rfl⟩ : syracuseStep 2620309 = 122827) (by norm_num)
theorem B2325437 : Blo 1032607 2325437 := bbase (se 3 (by rfl) ⟨436019, by rfl⟩ : syracuseStep 2325437 = 872039) (by norm_num)
theorem B1964989 : Blo 1032607 1964989 := bbase (se 3 (by rfl) ⟨368435, by rfl⟩ : syracuseStep 1964989 = 736871) (by norm_num)
theorem B2325509 : Blo 1032607 2325509 := bbase (se 4 (by rfl) ⟨218016, by rfl⟩ : syracuseStep 2325509 = 436033) (by norm_num)
theorem B2620421 : Blo 1032607 2620421 := bbase (se 4 (by rfl) ⟨245664, by rfl⟩ : syracuseStep 2620421 = 491329) (by norm_num)
theorem B1309709 : Blo 1032607 1309709 := bbase (se 3 (by rfl) ⟨245570, by rfl⟩ : syracuseStep 1309709 = 491141) (by norm_num)
theorem B1309765 : Blo 1032607 1309765 := bbase (se 4 (by rfl) ⟨122790, by rfl⟩ : syracuseStep 1309765 = 245581) (by norm_num)
theorem B2325581 : Blo 1032607 2325581 := bbase (se 3 (by rfl) ⟨436046, by rfl⟩ : syracuseStep 2325581 = 872093) (by norm_num)
theorem B2948213 : Blo 1032607 2948213 := bbase (se 5 (by rfl) ⟨138197, by rfl⟩ : syracuseStep 2948213 = 276395) (by norm_num)
theorem B2325653 : Blo 1032607 2325653 := bbase (se 6 (by rfl) ⟨54507, by rfl⟩ : syracuseStep 2325653 = 109015) (by norm_num)
theorem B16776341 : Blo 1032607 16776341 := bbase (se 6 (by rfl) ⟨393195, by rfl⟩ : syracuseStep 16776341 = 786391) (by norm_num)
theorem B1309861 : Blo 1032607 1309861 := bbase (se 4 (by rfl) ⟨122799, by rfl⟩ : syracuseStep 1309861 = 245599) (by norm_num)
theorem B2620613 : Blo 1032607 2620613 := bbase (se 4 (by rfl) ⟨245682, by rfl⟩ : syracuseStep 2620613 = 491365) (by norm_num)
theorem B1244369 : Blo 1032607 1244369 := bbase (se 2 (by rfl) ⟨466638, by rfl⟩ : syracuseStep 1244369 = 933277) (by norm_num)
theorem B2325725 : Blo 1032607 2325725 := bbase (se 3 (by rfl) ⟨436073, by rfl⟩ : syracuseStep 2325725 = 872147) (by norm_num)
theorem B1965293 : Blo 1032607 1965293 := bbase (se 3 (by rfl) ⟨368492, by rfl⟩ : syracuseStep 1965293 = 736985) (by norm_num)
theorem B1473805 : Blo 1032607 1473805 := bbase (se 3 (by rfl) ⟨276338, by rfl⟩ : syracuseStep 1473805 = 552677) (by norm_num)
theorem B2325797 : Blo 1032607 2325797 := bbase (se 4 (by rfl) ⟨218043, by rfl⟩ : syracuseStep 2325797 = 436087) (by norm_num)
theorem B1310033 : Blo 1032607 1310033 := bbase (se 2 (by rfl) ⟨491262, by rfl⟩ : syracuseStep 1310033 = 982525) (by norm_num)
theorem B2325869 : Blo 1032607 2325869 := bbase (se 3 (by rfl) ⟨436100, by rfl⟩ : syracuseStep 2325869 = 872201) (by norm_num)
theorem B1310089 : Blo 1032607 1310089 := bbase (se 2 (by rfl) ⟨491283, by rfl⟩ : syracuseStep 1310089 = 982567) (by norm_num)
theorem B2096525 : Blo 1032607 2096525 := bbase (se 3 (by rfl) ⟨393098, by rfl⟩ : syracuseStep 2096525 = 786197) (by norm_num)
theorem B1179049 : Blo 1032607 1179049 := bbase (se 2 (by rfl) ⟨442143, by rfl⟩ : syracuseStep 1179049 = 884287) (by norm_num)
theorem B2325941 : Blo 1032607 2325941 := bbase (se 5 (by rfl) ⟨109028, by rfl⟩ : syracuseStep 2325941 = 218057) (by norm_num)
theorem B4980149 : Blo 1032607 4980149 := bbase (se 5 (by rfl) ⟨233444, by rfl⟩ : syracuseStep 4980149 = 466889) (by norm_num)
theorem B1310185 : Blo 1032607 1310185 := bbase (se 2 (by rfl) ⟨491319, by rfl⟩ : syracuseStep 1310185 = 982639) (by norm_num)
theorem B2326013 : Blo 1032607 2326013 := bbase (se 3 (by rfl) ⟨436127, by rfl⟩ : syracuseStep 2326013 = 872255) (by norm_num)
theorem B2620957 : Blo 1032607 2620957 := bbase (se 3 (by rfl) ⟨491429, by rfl⟩ : syracuseStep 2620957 = 982859) (by norm_num)
theorem B1343045 : Blo 1032607 1343045 := bbase (se 4 (by rfl) ⟨125910, by rfl⟩ : syracuseStep 1343045 = 251821) (by norm_num)
theorem B2326085 : Blo 1032607 2326085 := bbase (se 4 (by rfl) ⟨218070, by rfl⟩ : syracuseStep 2326085 = 436141) (by norm_num)
theorem B1179209 : Blo 1032607 1179209 := bbase (se 2 (by rfl) ⟨442203, by rfl⟩ : syracuseStep 1179209 = 884407) (by norm_num)
theorem B7077461 : Blo 1032607 7077461 := bbase (se 8 (by rfl) ⟨41469, by rfl⟩ : syracuseStep 7077461 = 82939) (by norm_num)
theorem B1474141 : Blo 1032607 1474141 := bbase (se 3 (by rfl) ⟨276401, by rfl⟩ : syracuseStep 1474141 = 552803) (by norm_num)
theorem B2326157 : Blo 1032607 2326157 := bbase (se 3 (by rfl) ⟨436154, by rfl⟩ : syracuseStep 2326157 = 872309) (by norm_num)
theorem B2621069 : Blo 1032607 2621069 := bbase (se 3 (by rfl) ⟨491450, by rfl⟩ : syracuseStep 2621069 = 982901) (by norm_num)
theorem B1310357 : Blo 1032607 1310357 := bbase (se 6 (by rfl) ⟨30711, by rfl⟩ : syracuseStep 1310357 = 61423) (by norm_num)
theorem B1244845 : Blo 1032607 1244845 := bbase (se 3 (by rfl) ⟨233408, by rfl⟩ : syracuseStep 1244845 = 466817) (by norm_num)
theorem B1244873 : Blo 1032607 1244873 := bbase (se 2 (by rfl) ⟨466827, by rfl⟩ : syracuseStep 1244873 = 933655) (by norm_num)
theorem B1310413 : Blo 1032607 1310413 := bbase (se 3 (by rfl) ⟨245702, by rfl⟩ : syracuseStep 1310413 = 491405) (by norm_num)
theorem B40271573 : Blo 1032607 40271573 := bbase (se 7 (by rfl) ⟨471932, by rfl⟩ : syracuseStep 40271573 = 943865) (by norm_num)
theorem B2326229 : Blo 1032607 2326229 := bbase (se 7 (by rfl) ⟨27260, by rfl⟩ : syracuseStep 2326229 = 54521) (by norm_num)
theorem B3931861 : Blo 1032607 3931861 := bbase (se 7 (by rfl) ⟨46076, by rfl⟩ : syracuseStep 3931861 = 92153) (by norm_num)
theorem B2391805 : Blo 1032607 2391805 := bbase (se 3 (by rfl) ⟨448463, by rfl⟩ : syracuseStep 2391805 = 896927) (by norm_num)
theorem B2326301 : Blo 1032607 2326301 := bbase (se 3 (by rfl) ⟨436181, by rfl⟩ : syracuseStep 2326301 = 872363) (by norm_num)
theorem B1310509 : Blo 1032607 1310509 := bbase (se 3 (by rfl) ⟨245720, by rfl⟩ : syracuseStep 1310509 = 491441) (by norm_num)
theorem B1474357 : Blo 1032607 1474357 := bbase (se 5 (by rfl) ⟨69110, by rfl⟩ : syracuseStep 1474357 = 138221) (by norm_num)
theorem B1769285 : Blo 1032607 1769285 := bbase (se 4 (by rfl) ⟨165870, by rfl⟩ : syracuseStep 1769285 = 331741) (by norm_num)
theorem B2621261 : Blo 1032607 2621261 := bbase (se 3 (by rfl) ⟨491486, by rfl⟩ : syracuseStep 2621261 = 982973) (by norm_num)
theorem B2326373 : Blo 1032607 2326373 := bbase (se 4 (by rfl) ⟨218097, by rfl⟩ : syracuseStep 2326373 = 436195) (by norm_num)
theorem B1245061 : Blo 1032607 1245061 := bbase (se 4 (by rfl) ⟨116724, by rfl⟩ : syracuseStep 1245061 = 233449) (by norm_num)
theorem B2326445 : Blo 1032607 2326445 := bbase (se 3 (by rfl) ⟨436208, by rfl⟩ : syracuseStep 2326445 = 872417) (by norm_num)
theorem B5242805 : Blo 1032607 5242805 := bbase (se 5 (by rfl) ⟨245756, by rfl⟩ : syracuseStep 5242805 = 491513) (by norm_num)
theorem B1310681 : Blo 1032607 1310681 := bbase (se 2 (by rfl) ⟨491505, by rfl⟩ : syracuseStep 1310681 = 983011) (by norm_num)
theorem B1966045 : Blo 1032607 1966045 := bbase (se 3 (by rfl) ⟨368633, by rfl⟩ : syracuseStep 1966045 = 737267) (by norm_num)
theorem B2326517 : Blo 1032607 2326517 := bbase (se 5 (by rfl) ⟨109055, by rfl⟩ : syracuseStep 2326517 = 218111) (by norm_num)
theorem B1245181 : Blo 1032607 1245181 := bbase (se 3 (by rfl) ⟨233471, by rfl⟩ : syracuseStep 1245181 = 466943) (by norm_num)
theorem B2621443 : Blo 1032607 2621443 := bstep (se 1 (by rfl) ⟨1966082, by rfl⟩ : syracuseStep 2621443 = 3932165) B3932165
theorem B1474625 : Blo 1032607 1474625 := bstep (se 2 (by rfl) ⟨552984, by rfl⟩ : syracuseStep 1474625 = 1105969) B1105969
theorem B2621585 : Blo 1032607 2621585 := bstep (se 2 (by rfl) ⟨983094, by rfl⟩ : syracuseStep 2621585 = 1966189) B1966189
theorem B3735715 : Blo 1032607 3735715 := bstep (se 1 (by rfl) ⟨2801786, by rfl⟩ : syracuseStep 3735715 = 5603573) B5603573
theorem B1310899 : Blo 1032607 1310899 := bstep (se 1 (by rfl) ⟨983174, by rfl⟩ : syracuseStep 1310899 = 1966349) B1966349
theorem B11796677 : Blo 1032607 11796677 := bstep (se 4 (by rfl) ⟨1105938, by rfl⟩ : syracuseStep 11796677 = 2211877) B2211877
theorem B2326769 : Blo 1032607 2326769 := bstep (se 2 (by rfl) ⟨872538, by rfl⟩ : syracuseStep 2326769 = 1745077) B1745077
theorem B2326787 : Blo 1032607 2326787 := bstep (se 1 (by rfl) ⟨1745090, by rfl⟩ : syracuseStep 2326787 = 3490181) B3490181
theorem B1310995 : Blo 1032607 1310995 := bstep (se 1 (by rfl) ⟨983246, by rfl⟩ : syracuseStep 1310995 = 1966493) B1966493
theorem B3146051 : Blo 1032607 3146051 := bstep (se 1 (by rfl) ⟨2359538, by rfl⟩ : syracuseStep 3146051 = 4719077) B4719077
theorem B2949443 : Blo 1032607 2949443 := bstep (se 1 (by rfl) ⟨2212082, by rfl⟩ : syracuseStep 2949443 = 4424165) B4424165
theorem B3309923 : Blo 1032607 3309923 := bstep (se 1 (by rfl) ⟨2482442, by rfl⟩ : syracuseStep 3309923 = 4964885) B4964885
theorem B18841997 : Blo 1032607 18841997 := bstep (se 3 (by rfl) ⟨3532874, by rfl⟩ : syracuseStep 18841997 = 7065749) B7065749
theorem B1966531 : Blo 1032607 1966531 := bstep (se 1 (by rfl) ⟨1474898, by rfl⟩ : syracuseStep 1966531 = 2949797) B2949797
theorem B3932621 : Blo 1032607 3932621 := bstep (se 3 (by rfl) ⟨737366, by rfl⟩ : syracuseStep 3932621 = 1474733) B1474733
theorem B2359811 : Blo 1032607 2359811 := bstep (se 1 (by rfl) ⟨1769858, by rfl⟩ : syracuseStep 2359811 = 3539717) B3539717
theorem B2327057 : Blo 1032607 2327057 := bstep (se 2 (by rfl) ⟨872646, by rfl⟩ : syracuseStep 2327057 = 1745293) B1745293
theorem B2327075 : Blo 1032607 2327075 := bstep (se 1 (by rfl) ⟨1745306, by rfl⟩ : syracuseStep 2327075 = 3490613) B3490613
theorem B11207281 : Blo 1032607 11207281 := bstep (se 2 (by rfl) ⟨4202730, by rfl⟩ : syracuseStep 11207281 = 8405461) B8405461
theorem B1049203 : Blo 1032607 1049203 := bstep (se 1 (by rfl) ⟨786902, by rfl⟩ : syracuseStep 1049203 = 1573805) B1573805
theorem B3310321 : Blo 1032607 3310321 := bstep (se 2 (by rfl) ⟨1241370, by rfl⟩ : syracuseStep 3310321 = 2482741) B2482741
theorem B1311491 : Blo 1032607 1311491 := bstep (se 1 (by rfl) ⟨983618, by rfl⟩ : syracuseStep 1311491 = 1967237) B1967237
theorem B2327345 : Blo 1032607 2327345 := bstep (se 2 (by rfl) ⟨872754, by rfl⟩ : syracuseStep 2327345 = 1745509) B1745509
theorem B2523953 : Blo 1032607 2523953 := bstep (se 2 (by rfl) ⟨946482, by rfl⟩ : syracuseStep 2523953 = 1892965) B1892965
theorem B2327363 : Blo 1032607 2327363 := bstep (se 1 (by rfl) ⟨1745522, by rfl⟩ : syracuseStep 2327363 = 3491045) B3491045
theorem B1966979 : Blo 1032607 1966979 := bstep (se 1 (by rfl) ⟨1475234, by rfl⟩ : syracuseStep 1966979 = 2950469) B2950469
theorem B3539857 : Blo 1032607 3539857 := bstep (se 2 (by rfl) ⟨1327446, by rfl⟩ : syracuseStep 3539857 = 2654893) B2654893
theorem B1475491 : Blo 1032607 1475491 := bstep (se 1 (by rfl) ⟨1106618, by rfl⟩ : syracuseStep 1475491 = 2213237) B2213237
theorem B2098129 : Blo 1032607 2098129 := bstep (se 2 (by rfl) ⟨786798, by rfl⟩ : syracuseStep 2098129 = 1573597) B1573597
theorem B1475587 : Blo 1032607 1475587 := bstep (se 1 (by rfl) ⟨1106690, by rfl⟩ : syracuseStep 1475587 = 2213381) B2213381
theorem B5243939 : Blo 1032607 5243939 := bstep (se 1 (by rfl) ⟨3932954, by rfl⟩ : syracuseStep 5243939 = 7865909) B7865909
theorem B37815349 : Blo 1032607 37815349 := bstep (se 5 (by rfl) ⟨1772594, by rfl⟩ : syracuseStep 37815349 = 3545189) B3545189
theorem B2327633 : Blo 1032607 2327633 := bstep (se 2 (by rfl) ⟨872862, by rfl⟩ : syracuseStep 2327633 = 1745725) B1745725
theorem B2327651 : Blo 1032607 2327651 := bstep (se 1 (by rfl) ⟨1745738, by rfl⟩ : syracuseStep 2327651 = 3491477) B3491477
theorem B2950253 : Blo 1032607 2950253 := bstep (se 3 (by rfl) ⟨553172, by rfl⟩ : syracuseStep 2950253 = 1106345) B1106345
theorem B2622577 : Blo 1032607 2622577 := bstep (se 2 (by rfl) ⟨983466, by rfl⟩ : syracuseStep 2622577 = 1966933) B1966933
theorem B1967267 : Blo 1032607 1967267 := bstep (se 1 (by rfl) ⟨1475450, by rfl⟩ : syracuseStep 1967267 = 2950901) B2950901
theorem B3310769 : Blo 1032607 3310769 := bstep (se 2 (by rfl) ⟨1241538, by rfl⟩ : syracuseStep 3310769 = 2483077) B2483077
theorem B1574083 : Blo 1032607 1574083 := bstep (se 1 (by rfl) ⟨1180562, by rfl⟩ : syracuseStep 1574083 = 2361125) B2361125
theorem B2950445 : Blo 1032607 2950445 := bstep (se 3 (by rfl) ⟨553208, by rfl⟩ : syracuseStep 2950445 = 1106417) B1106417
theorem B1770817 : Blo 1032607 1770817 := bstep (se 2 (by rfl) ⟨664056, by rfl⟩ : syracuseStep 1770817 = 1328113) B1328113
theorem B1574225 : Blo 1032607 1574225 := bstep (se 2 (by rfl) ⟨590334, by rfl⟩ : syracuseStep 1574225 = 1180669) B1180669
theorem B2327921 : Blo 1032607 2327921 := bstep (se 2 (by rfl) ⟨872970, by rfl⟩ : syracuseStep 2327921 = 1745941) B1745941
theorem B2327939 : Blo 1032607 2327939 := bstep (se 1 (by rfl) ⟨1745954, by rfl⟩ : syracuseStep 2327939 = 3491909) B3491909
theorem B2622851 : Blo 1032607 2622851 := bstep (se 1 (by rfl) ⟨1967138, by rfl⟩ : syracuseStep 2622851 = 3934277) B3934277
theorem B5899661 : Blo 1032607 5899661 := bstep (se 3 (by rfl) ⟨1106186, by rfl⟩ : syracuseStep 5899661 = 2212373) B2212373
theorem B1574321 : Blo 1032607 1574321 := bstep (se 2 (by rfl) ⟨590370, by rfl⟩ : syracuseStep 1574321 = 1180741) B1180741
theorem B3147245 : Blo 1032607 3147245 := bstep (se 3 (by rfl) ⟨590108, by rfl⟩ : syracuseStep 3147245 = 1180217) B1180217
theorem B21268021 : Blo 1032607 21268021 := bstep (se 5 (by rfl) ⟨996938, by rfl⟩ : syracuseStep 21268021 = 1993877) B1993877
theorem B2623043 : Blo 1032607 2623043 := bstep (se 1 (by rfl) ⟨1967282, by rfl⟩ : syracuseStep 2623043 = 3934565) B3934565
theorem B4425293 : Blo 1032607 4425293 := bstep (se 3 (by rfl) ⟨829742, by rfl⟩ : syracuseStep 4425293 = 1659485) B1659485
theorem B36374129 : Blo 1032607 36374129 := bstep (se 2 (by rfl) ⟨13640298, by rfl⟩ : syracuseStep 36374129 = 27280597) B27280597
theorem B2328209 : Blo 1032607 2328209 := bstep (se 2 (by rfl) ⟨873078, by rfl⟩ : syracuseStep 2328209 = 1746157) B1746157
theorem B2328227 : Blo 1032607 2328227 := bstep (se 1 (by rfl) ⟨1746170, by rfl⟩ : syracuseStep 2328227 = 3492341) B3492341
theorem B6620869 : Blo 1032607 6620869 := bstep (se 4 (by rfl) ⟨620706, by rfl⟩ : syracuseStep 6620869 = 1241413) B1241413
theorem B5244749 : Blo 1032607 5244749 := bstep (se 3 (by rfl) ⟨983390, by rfl⟩ : syracuseStep 5244749 = 1966781) B1966781
theorem B21202829 : Blo 1032607 21202829 := bstep (se 3 (by rfl) ⟨3975530, by rfl⟩ : syracuseStep 21202829 = 7951061) B7951061
theorem B2328497 : Blo 1032607 2328497 := bstep (se 2 (by rfl) ⟨873186, by rfl⟩ : syracuseStep 2328497 = 1746373) B1746373
theorem B2328515 : Blo 1032607 2328515 := bstep (se 1 (by rfl) ⟨1746386, by rfl⟩ : syracuseStep 2328515 = 3492773) B3492773
theorem B2099395 : Blo 1032607 2099395 := bstep (se 1 (by rfl) ⟨1574546, by rfl⟩ : syracuseStep 2099395 = 3149093) B3149093
theorem B2328785 : Blo 1032607 2328785 := bstep (se 2 (by rfl) ⟨873294, by rfl⟩ : syracuseStep 2328785 = 1746589) B1746589
theorem B2328803 : Blo 1032607 2328803 := bstep (se 1 (by rfl) ⟨1746602, by rfl⟩ : syracuseStep 2328803 = 3493205) B3493205
theorem B2951437 : Blo 1032607 2951437 := bstep (se 3 (by rfl) ⟨553394, by rfl⟩ : syracuseStep 2951437 = 1106789) B1106789
theorem B1575251 : Blo 1032607 1575251 := bstep (se 1 (by rfl) ⟨1181438, by rfl⟩ : syracuseStep 1575251 = 2362877) B2362877
theorem B9439685 : Blo 1032607 9439685 := bstep (se 4 (by rfl) ⟨884970, by rfl⟩ : syracuseStep 9439685 = 1769941) B1769941
theorem B2329073 : Blo 1032607 2329073 := bstep (se 2 (by rfl) ⟨873402, by rfl⟩ : syracuseStep 2329073 = 1746805) B1746805
theorem B2329091 : Blo 1032607 2329091 := bstep (se 1 (by rfl) ⟨1746818, by rfl⟩ : syracuseStep 2329091 = 3493637) B3493637
theorem B1772131 : Blo 1032607 1772131 := bstep (se 1 (by rfl) ⟨1329098, by rfl⟩ : syracuseStep 1772131 = 2658197) B2658197
theorem B2329361 : Blo 1032607 2329361 := bstep (se 2 (by rfl) ⟨873510, by rfl⟩ : syracuseStep 2329361 = 1747021) B1747021
theorem B2329379 : Blo 1032607 2329379 := bstep (se 1 (by rfl) ⟨1747034, by rfl⟩ : syracuseStep 2329379 = 3494069) B3494069
theorem B27200369 : Blo 1032607 27200369 := bstep (se 2 (by rfl) ⟨10200138, by rfl⟩ : syracuseStep 27200369 = 20400277) B20400277
theorem B4426609 : Blo 1032607 4426609 := bstep (se 2 (by rfl) ⟨1659978, by rfl⟩ : syracuseStep 4426609 = 3319957) B3319957
theorem B1575811 : Blo 1032607 1575811 := bstep (se 1 (by rfl) ⟨1181858, by rfl⟩ : syracuseStep 1575811 = 2363717) B2363717
theorem B2329649 : Blo 1032607 2329649 := bstep (se 2 (by rfl) ⟨873618, by rfl⟩ : syracuseStep 2329649 = 1747237) B1747237
theorem B2329667 : Blo 1032607 2329667 := bstep (se 1 (by rfl) ⟨1747250, by rfl⟩ : syracuseStep 2329667 = 3494501) B3494501
theorem B3542125 : Blo 1032607 3542125 := bstep (se 3 (by rfl) ⟨664148, by rfl⟩ : syracuseStep 3542125 = 1328297) B1328297
theorem B2100401 : Blo 1032607 2100401 := bstep (se 2 (by rfl) ⟨787650, by rfl⟩ : syracuseStep 2100401 = 1575301) B1575301
theorem B3312845 : Blo 1032607 3312845 := bstep (se 3 (by rfl) ⟨621158, by rfl⟩ : syracuseStep 3312845 = 1242317) B1242317
theorem B3935537 : Blo 1032607 3935537 := bstep (se 2 (by rfl) ⟨1475826, by rfl⟩ : syracuseStep 3935537 = 2951653) B2951653
theorem B2329937 : Blo 1032607 2329937 := bstep (se 2 (by rfl) ⟨873726, by rfl⟩ : syracuseStep 2329937 = 1747453) B1747453
theorem B2329955 : Blo 1032607 2329955 := bstep (se 1 (by rfl) ⟨1747466, by rfl⟩ : syracuseStep 2329955 = 3494933) B3494933
theorem B5901893 : Blo 1032607 5901893 := bstep (se 4 (by rfl) ⟨553302, by rfl⟩ : syracuseStep 5901893 = 1106605) B1106605
theorem B2330225 : Blo 1032607 2330225 := bstep (se 2 (by rfl) ⟨873834, by rfl⟩ : syracuseStep 2330225 = 1747669) B1747669
theorem B2330243 : Blo 1032607 2330243 := bstep (se 1 (by rfl) ⟨1747682, by rfl⟩ : syracuseStep 2330243 = 3495365) B3495365
theorem B26545805 : Blo 1032607 26545805 := bstep (se 3 (by rfl) ⟨4977338, by rfl⟩ : syracuseStep 26545805 = 9954677) B9954677
theorem B9440995 : Blo 1032607 9440995 := bstep (se 1 (by rfl) ⟨7080746, by rfl⟩ : syracuseStep 9440995 = 14161493) B14161493
theorem B2330513 : Blo 1032607 2330513 := bstep (se 2 (by rfl) ⟨873942, by rfl⟩ : syracuseStep 2330513 = 1747885) B1747885
theorem B2330531 : Blo 1032607 2330531 := bstep (se 1 (by rfl) ⟨1747898, by rfl⟩ : syracuseStep 2330531 = 3495797) B3495797
theorem B4198499 : Blo 1032607 4198499 := bstep (se 1 (by rfl) ⟨3148874, by rfl⟩ : syracuseStep 4198499 = 6297749) B6297749
theorem B2330801 : Blo 1032607 2330801 := bstep (se 2 (by rfl) ⟨874050, by rfl⟩ : syracuseStep 2330801 = 1748101) B1748101
theorem B2330819 : Blo 1032607 2330819 := bstep (se 1 (by rfl) ⟨1748114, by rfl⟩ : syracuseStep 2330819 = 3496229) B3496229
theorem B5902577 : Blo 1032607 5902577 := bstep (se 2 (by rfl) ⟨2213466, by rfl⟩ : syracuseStep 5902577 = 4426933) B4426933
theorem B11178253 : Blo 1032607 11178253 := bstep (se 3 (by rfl) ⟨2095922, by rfl⟩ : syracuseStep 11178253 = 4191845) B4191845
theorem B3150211 : Blo 1032607 3150211 := bstep (se 1 (by rfl) ⟨2362658, by rfl⟩ : syracuseStep 3150211 = 4725317) B4725317
theorem B3314125 : Blo 1032607 3314125 := bstep (se 3 (by rfl) ⟨621398, by rfl⟩ : syracuseStep 3314125 = 1242797) B1242797
theorem B2331089 : Blo 1032607 2331089 := bstep (se 2 (by rfl) ⟨874158, by rfl⟩ : syracuseStep 2331089 = 1748317) B1748317
theorem B2331107 : Blo 1032607 2331107 := bstep (se 1 (by rfl) ⟨1748330, by rfl⟩ : syracuseStep 2331107 = 3496661) B3496661
theorem B5247665 : Blo 1032607 5247665 := bstep (se 2 (by rfl) ⟨1967874, by rfl⟩ : syracuseStep 5247665 = 3935749) B3935749
theorem B2331377 : Blo 1032607 2331377 := bstep (se 2 (by rfl) ⟨874266, by rfl⟩ : syracuseStep 2331377 = 1748533) B1748533
theorem B2331395 : Blo 1032607 2331395 := bstep (se 1 (by rfl) ⟨1748546, by rfl⟩ : syracuseStep 2331395 = 3497093) B3497093
theorem B3314627 : Blo 1032607 3314627 := bstep (se 1 (by rfl) ⟨2485970, by rfl⟩ : syracuseStep 3314627 = 4971941) B4971941
theorem B2331665 : Blo 1032607 2331665 := bstep (se 2 (by rfl) ⟨874374, by rfl⟩ : syracuseStep 2331665 = 1748749) B1748749
theorem B2331683 : Blo 1032607 2331683 := bstep (se 1 (by rfl) ⟨1748762, by rfl⟩ : syracuseStep 2331683 = 3497525) B3497525
theorem B6624355 : Blo 1032607 6624355 := bstep (se 1 (by rfl) ⟨4968266, by rfl⟩ : syracuseStep 6624355 = 9936533) B9936533
theorem B3150989 : Blo 1032607 3150989 := bstep (se 3 (by rfl) ⟨590810, by rfl⟩ : syracuseStep 3150989 = 1181621) B1181621
theorem B2331953 : Blo 1032607 2331953 := bstep (se 2 (by rfl) ⟨874482, by rfl⟩ : syracuseStep 2331953 = 1748965) B1748965
theorem B2331971 : Blo 1032607 2331971 := bstep (se 1 (by rfl) ⟨1748978, by rfl⟩ : syracuseStep 2331971 = 3497957) B3497957
theorem B2332241 : Blo 1032607 2332241 := bstep (se 2 (by rfl) ⟨874590, by rfl⟩ : syracuseStep 2332241 = 1749181) B1749181
theorem B2332259 : Blo 1032607 2332259 := bstep (se 1 (by rfl) ⟨1749194, by rfl⟩ : syracuseStep 2332259 = 3498389) B3498389
theorem B1119955 : Blo 1032607 1119955 := bstep (se 1 (by rfl) ⟨839966, by rfl⟩ : syracuseStep 1119955 = 1679933) B1679933
theorem B1742593 : Blo 1032607 1742593 := bstep (se 2 (by rfl) ⟨653472, by rfl⟩ : syracuseStep 1742593 = 1306945) B1306945
theorem B1742627 : Blo 1032607 1742627 := bstep (se 1 (by rfl) ⟨1306970, by rfl⟩ : syracuseStep 1742627 = 2613941) B2613941
theorem B2791277 : Blo 1032607 2791277 := bstep (se 3 (by rfl) ⟨523364, by rfl⟩ : syracuseStep 2791277 = 1046729) B1046729
theorem B11802509 : Blo 1032607 11802509 := bstep (se 3 (by rfl) ⟨2212970, by rfl⟩ : syracuseStep 11802509 = 4425941) B4425941
theorem B1742755 : Blo 1032607 1742755 := bstep (se 1 (by rfl) ⟨1307066, by rfl⟩ : syracuseStep 1742755 = 2614133) B2614133
theorem B1742897 : Blo 1032607 1742897 := bstep (se 2 (by rfl) ⟨653586, by rfl⟩ : syracuseStep 1742897 = 1307173) B1307173
theorem B1743025 : Blo 1032607 1743025 := bstep (se 2 (by rfl) ⟨653634, by rfl⟩ : syracuseStep 1743025 = 1307269) B1307269
theorem B1743059 : Blo 1032607 1743059 := bstep (se 1 (by rfl) ⟨1307294, by rfl⟩ : syracuseStep 1743059 = 2614589) B2614589
theorem B3315971 : Blo 1032607 3315971 := bstep (se 1 (by rfl) ⟨2486978, by rfl⟩ : syracuseStep 3315971 = 4973957) B4973957
theorem B1743187 : Blo 1032607 1743187 := bstep (se 1 (by rfl) ⟨1307390, by rfl⟩ : syracuseStep 1743187 = 2614781) B2614781
theorem B1743329 : Blo 1032607 1743329 := bstep (se 2 (by rfl) ⟨653748, by rfl⟩ : syracuseStep 1743329 = 1307497) B1307497
theorem B4790755 : Blo 1032607 4790755 := bstep (se 1 (by rfl) ⟨3593066, by rfl⟩ : syracuseStep 4790755 = 7186133) B7186133
theorem B12098117 : Blo 1032607 12098117 := bstep (se 4 (by rfl) ⟨1134198, by rfl⟩ : syracuseStep 12098117 = 2268397) B2268397
theorem B1743457 : Blo 1032607 1743457 := bstep (se 2 (by rfl) ⟨653796, by rfl⟩ : syracuseStep 1743457 = 1307593) B1307593
theorem B9935459 : Blo 1032607 9935459 := bstep (se 1 (by rfl) ⟨7451594, by rfl⟩ : syracuseStep 9935459 = 14903189) B14903189
theorem B1743491 : Blo 1032607 1743491 := bstep (se 1 (by rfl) ⟨1307618, by rfl⟩ : syracuseStep 1743491 = 2615237) B2615237
theorem B2792099 : Blo 1032607 2792099 := bstep (se 1 (by rfl) ⟨2094074, by rfl⟩ : syracuseStep 2792099 = 4188149) B4188149
theorem B1743619 : Blo 1032607 1743619 := bstep (se 1 (by rfl) ⟨1307714, by rfl⟩ : syracuseStep 1743619 = 2615429) B2615429
theorem B1743761 : Blo 1032607 1743761 := bstep (se 2 (by rfl) ⟨653910, by rfl⟩ : syracuseStep 1743761 = 1307821) B1307821
theorem B1743889 : Blo 1032607 1743889 := bstep (se 2 (by rfl) ⟨653958, by rfl⟩ : syracuseStep 1743889 = 1307917) B1307917
theorem B1743923 : Blo 1032607 1743923 := bstep (se 1 (by rfl) ⟨1307942, by rfl⟩ : syracuseStep 1743923 = 2615885) B2615885
theorem B1744051 : Blo 1032607 1744051 := bstep (se 1 (by rfl) ⟨1308038, by rfl⟩ : syracuseStep 1744051 = 2616077) B2616077
theorem B3316945 : Blo 1032607 3316945 := bstep (se 2 (by rfl) ⟨1243854, by rfl⟩ : syracuseStep 3316945 = 2487709) B2487709
theorem B1744193 : Blo 1032607 1744193 := bstep (se 2 (by rfl) ⟨654072, by rfl⟩ : syracuseStep 1744193 = 1308145) B1308145
theorem B1744321 : Blo 1032607 1744321 := bstep (se 2 (by rfl) ⟨654120, by rfl⟩ : syracuseStep 1744321 = 1308241) B1308241
theorem B3317201 : Blo 1032607 3317201 := bstep (se 2 (by rfl) ⟨1243950, by rfl⟩ : syracuseStep 3317201 = 2487901) B2487901
theorem B1744355 : Blo 1032607 1744355 := bstep (se 1 (by rfl) ⟨1308266, by rfl⟩ : syracuseStep 1744355 = 2616533) B2616533
theorem B1744483 : Blo 1032607 1744483 := bstep (se 1 (by rfl) ⟨1308362, by rfl⟩ : syracuseStep 1744483 = 2616725) B2616725
theorem B1744625 : Blo 1032607 1744625 := bstep (se 2 (by rfl) ⟨654234, by rfl⟩ : syracuseStep 1744625 = 1308469) B1308469
theorem B1744753 : Blo 1032607 1744753 := bstep (se 2 (by rfl) ⟨654282, by rfl⟩ : syracuseStep 1744753 = 1308565) B1308565
theorem B1744787 : Blo 1032607 1744787 := bstep (se 1 (by rfl) ⟨1308590, by rfl⟩ : syracuseStep 1744787 = 2617181) B2617181
theorem B1744915 : Blo 1032607 1744915 := bstep (se 1 (by rfl) ⟨1308686, by rfl⟩ : syracuseStep 1744915 = 2617373) B2617373
theorem B1745057 : Blo 1032607 1745057 := bstep (se 2 (by rfl) ⟨654396, by rfl⟩ : syracuseStep 1745057 = 1308793) B1308793
theorem B1745185 : Blo 1032607 1745185 := bstep (se 2 (by rfl) ⟨654444, by rfl⟩ : syracuseStep 1745185 = 1308889) B1308889
theorem B1745219 : Blo 1032607 1745219 := bstep (se 1 (by rfl) ⟨1308914, by rfl⟩ : syracuseStep 1745219 = 2617829) B2617829
theorem B1745347 : Blo 1032607 1745347 := bstep (se 1 (by rfl) ⟨1309010, by rfl⟩ : syracuseStep 1745347 = 2618021) B2618021
theorem B3318317 : Blo 1032607 3318317 := bstep (se 3 (by rfl) ⟨622184, by rfl⟩ : syracuseStep 3318317 = 1244369) B1244369
theorem B1745489 : Blo 1032607 1745489 := bstep (se 2 (by rfl) ⟨654558, by rfl⟩ : syracuseStep 1745489 = 1309117) B1309117
theorem B1548929 : Blo 1032607 1548929 := bstep (se 2 (by rfl) ⟨580848, by rfl⟩ : syracuseStep 1548929 = 1161697) B1161697
theorem B1548947 : Blo 1032607 1548947 := bstep (se 1 (by rfl) ⟨1161710, by rfl⟩ : syracuseStep 1548947 = 2323421) B2323421
theorem B1548977 : Blo 1032607 1548977 := bstep (se 2 (by rfl) ⟨580866, by rfl⟩ : syracuseStep 1548977 = 1161733) B1161733
theorem B1548995 : Blo 1032607 1548995 := bstep (se 1 (by rfl) ⟨1161746, by rfl⟩ : syracuseStep 1548995 = 2323493) B2323493
theorem B1745617 : Blo 1032607 1745617 := bstep (se 2 (by rfl) ⟨654606, by rfl⟩ : syracuseStep 1745617 = 1309213) B1309213
theorem B1549025 : Blo 1032607 1549025 := bstep (se 2 (by rfl) ⟨580884, by rfl⟩ : syracuseStep 1549025 = 1161769) B1161769
theorem B11805425 : Blo 1032607 11805425 := bstep (se 2 (by rfl) ⟨4427034, by rfl⟩ : syracuseStep 11805425 = 8854069) B8854069
theorem B1549043 : Blo 1032607 1549043 := bstep (se 1 (by rfl) ⟨1161782, by rfl⟩ : syracuseStep 1549043 = 2323565) B2323565
theorem B1745651 : Blo 1032607 1745651 := bstep (se 1 (by rfl) ⟨1309238, by rfl⟩ : syracuseStep 1745651 = 2618477) B2618477
theorem B1549073 : Blo 1032607 1549073 := bstep (se 2 (by rfl) ⟨580902, by rfl⟩ : syracuseStep 1549073 = 1161805) B1161805
theorem B1549091 : Blo 1032607 1549091 := bstep (se 1 (by rfl) ⟨1161818, by rfl⟩ : syracuseStep 1549091 = 2323637) B2323637
theorem B1549121 : Blo 1032607 1549121 := bstep (se 2 (by rfl) ⟨580920, by rfl⟩ : syracuseStep 1549121 = 1161841) B1161841
theorem B1549139 : Blo 1032607 1549139 := bstep (se 1 (by rfl) ⟨1161854, by rfl⟩ : syracuseStep 1549139 = 2323709) B2323709
theorem B1549169 : Blo 1032607 1549169 := bstep (se 2 (by rfl) ⟨580938, by rfl⟩ : syracuseStep 1549169 = 1161877) B1161877
theorem B1745779 : Blo 1032607 1745779 := bstep (se 1 (by rfl) ⟨1309334, by rfl⟩ : syracuseStep 1745779 = 2618669) B2618669
theorem B1549187 : Blo 1032607 1549187 := bstep (se 1 (by rfl) ⟨1161890, by rfl⟩ : syracuseStep 1549187 = 2323781) B2323781
theorem B6628229 : Blo 1032607 6628229 := bstep (se 4 (by rfl) ⟨621396, by rfl⟩ : syracuseStep 6628229 = 1242793) B1242793
theorem B1549217 : Blo 1032607 1549217 := bstep (se 2 (by rfl) ⟨580956, by rfl⟩ : syracuseStep 1549217 = 1161913) B1161913
theorem B1549235 : Blo 1032607 1549235 := bstep (se 1 (by rfl) ⟨1161926, by rfl⟩ : syracuseStep 1549235 = 2323853) B2323853
theorem B44704709 : Blo 1032607 44704709 := bstep (se 4 (by rfl) ⟨4191066, by rfl⟩ : syracuseStep 44704709 = 8382133) B8382133
theorem B1549265 : Blo 1032607 1549265 := bstep (se 2 (by rfl) ⟨580974, by rfl⟩ : syracuseStep 1549265 = 1161949) B1161949
theorem B1549283 : Blo 1032607 1549283 := bstep (se 1 (by rfl) ⟨1161962, by rfl⟩ : syracuseStep 1549283 = 2323925) B2323925
theorem B1549313 : Blo 1032607 1549313 := bstep (se 2 (by rfl) ⟨580992, by rfl⟩ : syracuseStep 1549313 = 1161985) B1161985
theorem B1745921 : Blo 1032607 1745921 := bstep (se 2 (by rfl) ⟨654720, by rfl⟩ : syracuseStep 1745921 = 1309441) B1309441
theorem B1549331 : Blo 1032607 1549331 := bstep (se 1 (by rfl) ⟨1161998, by rfl⟩ : syracuseStep 1549331 = 2323997) B2323997
theorem B1549361 : Blo 1032607 1549361 := bstep (se 2 (by rfl) ⟨581010, by rfl⟩ : syracuseStep 1549361 = 1162021) B1162021
theorem B1549379 : Blo 1032607 1549379 := bstep (se 1 (by rfl) ⟨1162034, by rfl⟩ : syracuseStep 1549379 = 2324069) B2324069
theorem B1549409 : Blo 1032607 1549409 := bstep (se 2 (by rfl) ⟨581028, by rfl⟩ : syracuseStep 1549409 = 1162057) B1162057
theorem B1549427 : Blo 1032607 1549427 := bstep (se 1 (by rfl) ⟨1162070, by rfl⟩ : syracuseStep 1549427 = 2324141) B2324141
theorem B1746049 : Blo 1032607 1746049 := bstep (se 2 (by rfl) ⟨654768, by rfl⟩ : syracuseStep 1746049 = 1309537) B1309537
theorem B1549457 : Blo 1032607 1549457 := bstep (se 2 (by rfl) ⟨581046, by rfl⟩ : syracuseStep 1549457 = 1162093) B1162093
theorem B1549475 : Blo 1032607 1549475 := bstep (se 1 (by rfl) ⟨1162106, by rfl⟩ : syracuseStep 1549475 = 2324213) B2324213
theorem B1746083 : Blo 1032607 1746083 := bstep (se 1 (by rfl) ⟨1309562, by rfl⟩ : syracuseStep 1746083 = 2619125) B2619125
theorem B1549505 : Blo 1032607 1549505 := bstep (se 2 (by rfl) ⟨581064, by rfl⟩ : syracuseStep 1549505 = 1162129) B1162129
theorem B1549523 : Blo 1032607 1549523 := bstep (se 1 (by rfl) ⟨1162142, by rfl⟩ : syracuseStep 1549523 = 2324285) B2324285
theorem B1549553 : Blo 1032607 1549553 := bstep (se 2 (by rfl) ⟨581082, by rfl⟩ : syracuseStep 1549553 = 1162165) B1162165
theorem B1549571 : Blo 1032607 1549571 := bstep (se 1 (by rfl) ⟨1162178, by rfl⟩ : syracuseStep 1549571 = 2324357) B2324357
theorem B1549601 : Blo 1032607 1549601 := bstep (se 2 (by rfl) ⟨581100, by rfl⟩ : syracuseStep 1549601 = 1162201) B1162201
theorem B1746211 : Blo 1032607 1746211 := bstep (se 1 (by rfl) ⟨1309658, by rfl⟩ : syracuseStep 1746211 = 2619317) B2619317
theorem B1549619 : Blo 1032607 1549619 := bstep (se 1 (by rfl) ⟨1162214, by rfl⟩ : syracuseStep 1549619 = 2324429) B2324429
theorem B1549649 : Blo 1032607 1549649 := bstep (se 2 (by rfl) ⟨581118, by rfl⟩ : syracuseStep 1549649 = 1162237) B1162237
theorem B1549667 : Blo 1032607 1549667 := bstep (se 1 (by rfl) ⟨1162250, by rfl⟩ : syracuseStep 1549667 = 2324501) B2324501
theorem B1549697 : Blo 1032607 1549697 := bstep (se 2 (by rfl) ⟨581136, by rfl⟩ : syracuseStep 1549697 = 1162273) B1162273
theorem B1549715 : Blo 1032607 1549715 := bstep (se 1 (by rfl) ⟨1162286, by rfl⟩ : syracuseStep 1549715 = 2324573) B2324573
theorem B1549745 : Blo 1032607 1549745 := bstep (se 2 (by rfl) ⟨581154, by rfl⟩ : syracuseStep 1549745 = 1162309) B1162309
theorem B1746353 : Blo 1032607 1746353 := bstep (se 2 (by rfl) ⟨654882, by rfl⟩ : syracuseStep 1746353 = 1309765) B1309765
theorem B1549763 : Blo 1032607 1549763 := bstep (se 1 (by rfl) ⟨1162322, by rfl⟩ : syracuseStep 1549763 = 2324645) B2324645
theorem B1549793 : Blo 1032607 1549793 := bstep (se 2 (by rfl) ⟨581172, by rfl⟩ : syracuseStep 1549793 = 1162345) B1162345
theorem B1549811 : Blo 1032607 1549811 := bstep (se 1 (by rfl) ⟨1162358, by rfl⟩ : syracuseStep 1549811 = 2324717) B2324717
theorem B3581453 : Blo 1032607 3581453 := bstep (se 3 (by rfl) ⟨671522, by rfl⟩ : syracuseStep 3581453 = 1343045) B1343045
theorem B1549841 : Blo 1032607 1549841 := bstep (se 2 (by rfl) ⟨581190, by rfl⟩ : syracuseStep 1549841 = 1162381) B1162381
theorem B1549859 : Blo 1032607 1549859 := bstep (se 1 (by rfl) ⟨1162394, by rfl⟩ : syracuseStep 1549859 = 2324789) B2324789
theorem B1746481 : Blo 1032607 1746481 := bstep (se 2 (by rfl) ⟨654930, by rfl⟩ : syracuseStep 1746481 = 1309861) B1309861
theorem B37725749 : Blo 1032607 37725749 := bstep (se 5 (by rfl) ⟨1768394, by rfl⟩ : syracuseStep 37725749 = 3536789) B3536789
theorem B1549889 : Blo 1032607 1549889 := bstep (se 2 (by rfl) ⟨581208, by rfl⟩ : syracuseStep 1549889 = 1162417) B1162417
theorem B1549907 : Blo 1032607 1549907 := bstep (se 1 (by rfl) ⟨1162430, by rfl⟩ : syracuseStep 1549907 = 2324861) B2324861
theorem B1746515 : Blo 1032607 1746515 := bstep (se 1 (by rfl) ⟨1309886, by rfl⟩ : syracuseStep 1746515 = 2619773) B2619773
theorem B2795107 : Blo 1032607 2795107 := bstep (se 1 (by rfl) ⟨2096330, by rfl⟩ : syracuseStep 2795107 = 4192661) B4192661
theorem B1549937 : Blo 1032607 1549937 := bstep (se 2 (by rfl) ⟨581226, by rfl⟩ : syracuseStep 1549937 = 1162453) B1162453
theorem B1549955 : Blo 1032607 1549955 := bstep (se 1 (by rfl) ⟨1162466, by rfl⟩ : syracuseStep 1549955 = 2324933) B2324933
theorem B1549985 : Blo 1032607 1549985 := bstep (se 2 (by rfl) ⟨581244, by rfl⟩ : syracuseStep 1549985 = 1162489) B1162489
theorem B1550003 : Blo 1032607 1550003 := bstep (se 1 (by rfl) ⟨1162502, by rfl⟩ : syracuseStep 1550003 = 2325005) B2325005
theorem B1550033 : Blo 1032607 1550033 := bstep (se 2 (by rfl) ⟨581262, by rfl⟩ : syracuseStep 1550033 = 1162525) B1162525
theorem B1746643 : Blo 1032607 1746643 := bstep (se 1 (by rfl) ⟨1309982, by rfl⟩ : syracuseStep 1746643 = 2619965) B2619965
theorem B1550051 : Blo 1032607 1550051 := bstep (se 1 (by rfl) ⟨1162538, by rfl⟩ : syracuseStep 1550051 = 2325077) B2325077
theorem B1550081 : Blo 1032607 1550081 := bstep (se 2 (by rfl) ⟨581280, by rfl⟩ : syracuseStep 1550081 = 1162561) B1162561
theorem B1550099 : Blo 1032607 1550099 := bstep (se 1 (by rfl) ⟨1162574, by rfl⟩ : syracuseStep 1550099 = 2325149) B2325149
theorem B1550129 : Blo 1032607 1550129 := bstep (se 2 (by rfl) ⟨581298, by rfl⟩ : syracuseStep 1550129 = 1162597) B1162597
theorem B1550147 : Blo 1032607 1550147 := bstep (se 1 (by rfl) ⟨1162610, by rfl⟩ : syracuseStep 1550147 = 2325221) B2325221
theorem B7087949 : Blo 1032607 7087949 := bstep (se 3 (by rfl) ⟨1328990, by rfl⟩ : syracuseStep 7087949 = 2657981) B2657981
theorem B1550177 : Blo 1032607 1550177 := bstep (se 2 (by rfl) ⟨581316, by rfl⟩ : syracuseStep 1550177 = 1162633) B1162633
theorem B1746785 : Blo 1032607 1746785 := bstep (se 2 (by rfl) ⟨655044, by rfl⟩ : syracuseStep 1746785 = 1310089) B1310089
theorem B2205539 : Blo 1032607 2205539 := bstep (se 1 (by rfl) ⟨1654154, by rfl⟩ : syracuseStep 2205539 = 3308309) B3308309
theorem B3319661 : Blo 1032607 3319661 := bstep (se 3 (by rfl) ⟨622436, by rfl⟩ : syracuseStep 3319661 = 1244873) B1244873
theorem B14165873 : Blo 1032607 14165873 := bstep (se 2 (by rfl) ⟨5312202, by rfl⟩ : syracuseStep 14165873 = 10624405) B10624405
theorem B12593009 : Blo 1032607 12593009 := bstep (se 2 (by rfl) ⟨4722378, by rfl⟩ : syracuseStep 12593009 = 9444757) B9444757
theorem B1550195 : Blo 1032607 1550195 := bstep (se 1 (by rfl) ⟨1162646, by rfl⟩ : syracuseStep 1550195 = 2325293) B2325293
theorem B1550225 : Blo 1032607 1550225 := bstep (se 2 (by rfl) ⟨581334, by rfl⟩ : syracuseStep 1550225 = 1162669) B1162669
theorem B1550243 : Blo 1032607 1550243 := bstep (se 1 (by rfl) ⟨1162682, by rfl⟩ : syracuseStep 1550243 = 2325365) B2325365
theorem B1550273 : Blo 1032607 1550273 := bstep (se 2 (by rfl) ⟨581352, by rfl⟩ : syracuseStep 1550273 = 1162705) B1162705
theorem B1550291 : Blo 1032607 1550291 := bstep (se 1 (by rfl) ⟨1162718, by rfl⟩ : syracuseStep 1550291 = 2325437) B2325437
theorem B1746913 : Blo 1032607 1746913 := bstep (se 2 (by rfl) ⟨655092, by rfl⟩ : syracuseStep 1746913 = 1310185) B1310185
theorem B1550321 : Blo 1032607 1550321 := bstep (se 2 (by rfl) ⟨581370, by rfl⟩ : syracuseStep 1550321 = 1162741) B1162741
theorem B1550339 : Blo 1032607 1550339 := bstep (se 1 (by rfl) ⟨1162754, by rfl⟩ : syracuseStep 1550339 = 2325509) B2325509
theorem B1746947 : Blo 1032607 1746947 := bstep (se 1 (by rfl) ⟨1310210, by rfl⟩ : syracuseStep 1746947 = 2620421) B2620421
theorem B1550369 : Blo 1032607 1550369 := bstep (se 2 (by rfl) ⟨581388, by rfl⟩ : syracuseStep 1550369 = 1162777) B1162777
theorem B1550387 : Blo 1032607 1550387 := bstep (se 1 (by rfl) ⟨1162790, by rfl⟩ : syracuseStep 1550387 = 2325581) B2325581
theorem B1550417 : Blo 1032607 1550417 := bstep (se 2 (by rfl) ⟨581406, by rfl⟩ : syracuseStep 1550417 = 1162813) B1162813
theorem B1550435 : Blo 1032607 1550435 := bstep (se 1 (by rfl) ⟨1162826, by rfl⟩ : syracuseStep 1550435 = 2325653) B2325653
theorem B11184227 : Blo 1032607 11184227 := bstep (se 1 (by rfl) ⟨8388170, by rfl⟩ : syracuseStep 11184227 = 16776341) B16776341
theorem B1550465 : Blo 1032607 1550465 := bstep (se 2 (by rfl) ⟨581424, by rfl⟩ : syracuseStep 1550465 = 1162849) B1162849
theorem B1747075 : Blo 1032607 1747075 := bstep (se 1 (by rfl) ⟨1310306, by rfl⟩ : syracuseStep 1747075 = 2620613) B2620613
theorem B1550483 : Blo 1032607 1550483 := bstep (se 1 (by rfl) ⟨1162862, by rfl⟩ : syracuseStep 1550483 = 2325725) B2325725
theorem B1550513 : Blo 1032607 1550513 := bstep (se 2 (by rfl) ⟨581442, by rfl⟩ : syracuseStep 1550513 = 1162885) B1162885
theorem B1550531 : Blo 1032607 1550531 := bstep (se 1 (by rfl) ⟨1162898, by rfl⟩ : syracuseStep 1550531 = 2325797) B2325797
theorem B1550561 : Blo 1032607 1550561 := bstep (se 2 (by rfl) ⟨581460, by rfl⟩ : syracuseStep 1550561 = 1162921) B1162921
theorem B1550579 : Blo 1032607 1550579 := bstep (se 1 (by rfl) ⟨1162934, by rfl⟩ : syracuseStep 1550579 = 2325869) B2325869
theorem B1550609 : Blo 1032607 1550609 := bstep (se 2 (by rfl) ⟨581478, by rfl⟩ : syracuseStep 1550609 = 1162957) B1162957
theorem B1747217 : Blo 1032607 1747217 := bstep (se 2 (by rfl) ⟨655206, by rfl⟩ : syracuseStep 1747217 = 1310413) B1310413
theorem B1550627 : Blo 1032607 1550627 := bstep (se 1 (by rfl) ⟨1162970, by rfl⟩ : syracuseStep 1550627 = 2325941) B2325941
theorem B3320099 : Blo 1032607 3320099 := bstep (se 1 (by rfl) ⟨2490074, by rfl⟩ : syracuseStep 3320099 = 4980149) B4980149
theorem B1550657 : Blo 1032607 1550657 := bstep (se 2 (by rfl) ⟨581496, by rfl⟩ : syracuseStep 1550657 = 1162993) B1162993
theorem B3189073 : Blo 1032607 3189073 := bstep (se 2 (by rfl) ⟨1195902, by rfl⟩ : syracuseStep 3189073 = 2391805) B2391805
theorem B1550675 : Blo 1032607 1550675 := bstep (se 1 (by rfl) ⟨1163006, by rfl⟩ : syracuseStep 1550675 = 2326013) B2326013
theorem B1550705 : Blo 1032607 1550705 := bstep (se 2 (by rfl) ⟨581514, by rfl⟩ : syracuseStep 1550705 = 1163029) B1163029
theorem B1550723 : Blo 1032607 1550723 := bstep (se 1 (by rfl) ⟨1163042, by rfl⟩ : syracuseStep 1550723 = 2326085) B2326085
theorem B1747345 : Blo 1032607 1747345 := bstep (se 2 (by rfl) ⟨655254, by rfl⟩ : syracuseStep 1747345 = 1310509) B1310509
theorem B1550753 : Blo 1032607 1550753 := bstep (se 2 (by rfl) ⟨581532, by rfl⟩ : syracuseStep 1550753 = 1163065) B1163065
theorem B2206129 : Blo 1032607 2206129 := bstep (se 2 (by rfl) ⟨827298, by rfl⟩ : syracuseStep 2206129 = 1654597) B1654597
theorem B1550771 : Blo 1032607 1550771 := bstep (se 1 (by rfl) ⟨1163078, by rfl⟩ : syracuseStep 1550771 = 2326157) B2326157
theorem B1747379 : Blo 1032607 1747379 := bstep (se 1 (by rfl) ⟨1310534, by rfl⟩ : syracuseStep 1747379 = 2621069) B2621069
theorem B1550801 : Blo 1032607 1550801 := bstep (se 2 (by rfl) ⟨581550, by rfl⟩ : syracuseStep 1550801 = 1163101) B1163101
theorem B26847715 : Blo 1032607 26847715 := bstep (se 1 (by rfl) ⟨20135786, by rfl⟩ : syracuseStep 26847715 = 40271573) B40271573
theorem B1550819 : Blo 1032607 1550819 := bstep (se 1 (by rfl) ⟨1163114, by rfl⟩ : syracuseStep 1550819 = 2326229) B2326229
theorem B1550849 : Blo 1032607 1550849 := bstep (se 2 (by rfl) ⟨581568, by rfl⟩ : syracuseStep 1550849 = 1163137) B1163137
theorem B1550867 : Blo 1032607 1550867 := bstep (se 1 (by rfl) ⟨1163150, by rfl⟩ : syracuseStep 1550867 = 2326301) B2326301
theorem B1550897 : Blo 1032607 1550897 := bstep (se 2 (by rfl) ⟨581586, by rfl⟩ : syracuseStep 1550897 = 1163173) B1163173
theorem B1747507 : Blo 1032607 1747507 := bstep (se 1 (by rfl) ⟨1310630, by rfl⟩ : syracuseStep 1747507 = 2621261) B2621261
theorem B1550915 : Blo 1032607 1550915 := bstep (se 1 (by rfl) ⟨1163186, by rfl⟩ : syracuseStep 1550915 = 2326373) B2326373
theorem B1550945 : Blo 1032607 1550945 := bstep (se 2 (by rfl) ⟨581604, by rfl⟩ : syracuseStep 1550945 = 1163209) B1163209
theorem B1550963 : Blo 1032607 1550963 := bstep (se 1 (by rfl) ⟨1163222, by rfl⟩ : syracuseStep 1550963 = 2326445) B2326445
theorem B1550993 : Blo 1032607 1550993 := bstep (se 2 (by rfl) ⟨581622, by rfl⟩ : syracuseStep 1550993 = 1163245) B1163245
theorem B1551011 : Blo 1032607 1551011 := bstep (se 1 (by rfl) ⟨1163258, by rfl⟩ : syracuseStep 1551011 = 2326517) B2326517
theorem B1551041 : Blo 1032607 1551041 := bstep (se 2 (by rfl) ⟨581640, by rfl⟩ : syracuseStep 1551041 = 1163281) B1163281
theorem B1747649 : Blo 1032607 1747649 := bstep (se 2 (by rfl) ⟨655368, by rfl⟩ : syracuseStep 1747649 = 1310737) B1310737
theorem B1551059 : Blo 1032607 1551059 := bstep (se 1 (by rfl) ⟨1163294, by rfl⟩ : syracuseStep 1551059 = 2326589) B2326589
theorem B1551089 : Blo 1032607 1551089 := bstep (se 2 (by rfl) ⟨581658, by rfl⟩ : syracuseStep 1551089 = 1163317) B1163317
theorem B1551107 : Blo 1032607 1551107 := bstep (se 1 (by rfl) ⟨1163330, by rfl⟩ : syracuseStep 1551107 = 2326661) B2326661
theorem B1551137 : Blo 1032607 1551137 := bstep (se 2 (by rfl) ⟨581676, by rfl⟩ : syracuseStep 1551137 = 1163353) B1163353
theorem B1551155 : Blo 1032607 1551155 := bstep (se 1 (by rfl) ⟨1163366, by rfl⟩ : syracuseStep 1551155 = 2326733) B2326733
theorem B1747777 : Blo 1032607 1747777 := bstep (se 2 (by rfl) ⟨655416, by rfl⟩ : syracuseStep 1747777 = 1310833) B1310833
theorem B1551185 : Blo 1032607 1551185 := bstep (se 2 (by rfl) ⟨581694, by rfl⟩ : syracuseStep 1551185 = 1163389) B1163389
theorem B1551203 : Blo 1032607 1551203 := bstep (se 1 (by rfl) ⟨1163402, by rfl⟩ : syracuseStep 1551203 = 2326805) B2326805
theorem B1747811 : Blo 1032607 1747811 := bstep (se 1 (by rfl) ⟨1310858, by rfl⟩ : syracuseStep 1747811 = 2621717) B2621717
theorem B1551233 : Blo 1032607 1551233 := bstep (se 2 (by rfl) ⟨581712, by rfl⟩ : syracuseStep 1551233 = 1163425) B1163425
theorem B1551251 : Blo 1032607 1551251 := bstep (se 1 (by rfl) ⟨1163438, by rfl⟩ : syracuseStep 1551251 = 2326877) B2326877
theorem B1551281 : Blo 1032607 1551281 := bstep (se 2 (by rfl) ⟨581730, by rfl⟩ : syracuseStep 1551281 = 1163461) B1163461
theorem B1551299 : Blo 1032607 1551299 := bstep (se 1 (by rfl) ⟨1163474, by rfl⟩ : syracuseStep 1551299 = 2326949) B2326949
theorem B1551329 : Blo 1032607 1551329 := bstep (se 2 (by rfl) ⟨581748, by rfl⟩ : syracuseStep 1551329 = 1163497) B1163497
theorem B1747939 : Blo 1032607 1747939 := bstep (se 1 (by rfl) ⟨1310954, by rfl⟩ : syracuseStep 1747939 = 2621909) B2621909
theorem B1551347 : Blo 1032607 1551347 := bstep (se 1 (by rfl) ⟨1163510, by rfl⟩ : syracuseStep 1551347 = 2327021) B2327021
theorem B1551377 : Blo 1032607 1551377 := bstep (se 2 (by rfl) ⟨581766, by rfl⟩ : syracuseStep 1551377 = 1163533) B1163533
theorem B1551395 : Blo 1032607 1551395 := bstep (se 1 (by rfl) ⟨1163546, by rfl⟩ : syracuseStep 1551395 = 2327093) B2327093
theorem B1551425 : Blo 1032607 1551425 := bstep (se 2 (by rfl) ⟨581784, by rfl⟩ : syracuseStep 1551425 = 1163569) B1163569
theorem B3353681 : Blo 1032607 3353681 := bstep (se 2 (by rfl) ⟨1257630, by rfl⟩ : syracuseStep 3353681 = 2515261) B2515261
theorem B1551443 : Blo 1032607 1551443 := bstep (se 1 (by rfl) ⟨1163582, by rfl⟩ : syracuseStep 1551443 = 2327165) B2327165
theorem B1551473 : Blo 1032607 1551473 := bstep (se 2 (by rfl) ⟨581802, by rfl⟩ : syracuseStep 1551473 = 1163605) B1163605
theorem B1748081 : Blo 1032607 1748081 := bstep (se 2 (by rfl) ⟨655530, by rfl⟩ : syracuseStep 1748081 = 1311061) B1311061
theorem B1551491 : Blo 1032607 1551491 := bstep (se 1 (by rfl) ⟨1163618, by rfl⟩ : syracuseStep 1551491 = 2327237) B2327237
theorem B12102797 : Blo 1032607 12102797 := bstep (se 3 (by rfl) ⟨2269274, by rfl⟩ : syracuseStep 12102797 = 4538549) B4538549
theorem B1551521 : Blo 1032607 1551521 := bstep (se 2 (by rfl) ⟨581820, by rfl⟩ : syracuseStep 1551521 = 1163641) B1163641
theorem B1551539 : Blo 1032607 1551539 := bstep (se 1 (by rfl) ⟨1163654, by rfl⟩ : syracuseStep 1551539 = 2327309) B2327309
theorem B1551569 : Blo 1032607 1551569 := bstep (se 2 (by rfl) ⟨581838, by rfl⟩ : syracuseStep 1551569 = 1163677) B1163677
theorem B1551587 : Blo 1032607 1551587 := bstep (se 1 (by rfl) ⟨1163690, by rfl⟩ : syracuseStep 1551587 = 2327381) B2327381
theorem B1748209 : Blo 1032607 1748209 := bstep (se 2 (by rfl) ⟨655578, by rfl⟩ : syracuseStep 1748209 = 1311157) B1311157
theorem B1551617 : Blo 1032607 1551617 := bstep (se 2 (by rfl) ⟨581856, by rfl⟩ : syracuseStep 1551617 = 1163713) B1163713
theorem B1551635 : Blo 1032607 1551635 := bstep (se 1 (by rfl) ⟨1163726, by rfl⟩ : syracuseStep 1551635 = 2327453) B2327453
theorem B1748243 : Blo 1032607 1748243 := bstep (se 1 (by rfl) ⟨1311182, by rfl⟩ : syracuseStep 1748243 = 2622365) B2622365
theorem B1551665 : Blo 1032607 1551665 := bstep (se 2 (by rfl) ⟨581874, by rfl⟩ : syracuseStep 1551665 = 1163749) B1163749
theorem B1551683 : Blo 1032607 1551683 := bstep (se 1 (by rfl) ⟨1163762, by rfl⟩ : syracuseStep 1551683 = 2327525) B2327525
theorem B1551713 : Blo 1032607 1551713 := bstep (se 2 (by rfl) ⟨581892, by rfl⟩ : syracuseStep 1551713 = 1163785) B1163785
theorem B1551731 : Blo 1032607 1551731 := bstep (se 1 (by rfl) ⟨1163798, by rfl⟩ : syracuseStep 1551731 = 2327597) B2327597
theorem B1551761 : Blo 1032607 1551761 := bstep (se 2 (by rfl) ⟨581910, by rfl⟩ : syracuseStep 1551761 = 1163821) B1163821
theorem B1748371 : Blo 1032607 1748371 := bstep (se 1 (by rfl) ⟨1311278, by rfl⟩ : syracuseStep 1748371 = 2622557) B2622557
theorem B1551779 : Blo 1032607 1551779 := bstep (se 1 (by rfl) ⟨1163834, by rfl⟩ : syracuseStep 1551779 = 2327669) B2327669
theorem B3485105 : Blo 1032607 3485105 := bstep (se 2 (by rfl) ⟨1306914, by rfl⟩ : syracuseStep 3485105 = 2613829) B2613829
theorem B3976625 : Blo 1032607 3976625 := bstep (se 2 (by rfl) ⟨1491234, by rfl⟩ : syracuseStep 3976625 = 2982469) B2982469
theorem B1551809 : Blo 1032607 1551809 := bstep (se 2 (by rfl) ⟨581928, by rfl⟩ : syracuseStep 1551809 = 1163857) B1163857
theorem B1551827 : Blo 1032607 1551827 := bstep (se 1 (by rfl) ⟨1163870, by rfl⟩ : syracuseStep 1551827 = 2327741) B2327741
theorem B1551857 : Blo 1032607 1551857 := bstep (se 2 (by rfl) ⟨581946, by rfl⟩ : syracuseStep 1551857 = 1163893) B1163893
theorem B1551875 : Blo 1032607 1551875 := bstep (se 1 (by rfl) ⟨1163906, by rfl⟩ : syracuseStep 1551875 = 2327813) B2327813
theorem B1551905 : Blo 1032607 1551905 := bstep (se 2 (by rfl) ⟨581964, by rfl⟩ : syracuseStep 1551905 = 1163929) B1163929
theorem B1748513 : Blo 1032607 1748513 := bstep (se 2 (by rfl) ⟨655692, by rfl⟩ : syracuseStep 1748513 = 1311385) B1311385
theorem B1551923 : Blo 1032607 1551923 := bstep (se 1 (by rfl) ⟨1163942, by rfl⟩ : syracuseStep 1551923 = 2327885) B2327885
theorem B1551953 : Blo 1032607 1551953 := bstep (se 2 (by rfl) ⟨581982, by rfl⟩ : syracuseStep 1551953 = 1163965) B1163965
theorem B1551971 : Blo 1032607 1551971 := bstep (se 1 (by rfl) ⟨1163978, by rfl⟩ : syracuseStep 1551971 = 2327957) B2327957
theorem B1552001 : Blo 1032607 1552001 := bstep (se 2 (by rfl) ⟨582000, by rfl⟩ : syracuseStep 1552001 = 1164001) B1164001
theorem B1552019 : Blo 1032607 1552019 := bstep (se 1 (by rfl) ⟨1164014, by rfl⟩ : syracuseStep 1552019 = 2328029) B2328029
theorem B1748641 : Blo 1032607 1748641 := bstep (se 2 (by rfl) ⟨655740, by rfl⟩ : syracuseStep 1748641 = 1311481) B1311481
theorem B1552049 : Blo 1032607 1552049 := bstep (se 2 (by rfl) ⟨582018, by rfl⟩ : syracuseStep 1552049 = 1164037) B1164037
theorem B1552067 : Blo 1032607 1552067 := bstep (se 1 (by rfl) ⟨1164050, by rfl⟩ : syracuseStep 1552067 = 2328101) B2328101
theorem B1748675 : Blo 1032607 1748675 := bstep (se 1 (by rfl) ⟨1311506, by rfl⟩ : syracuseStep 1748675 = 2623013) B2623013
theorem B1552097 : Blo 1032607 1552097 := bstep (se 2 (by rfl) ⟨582036, by rfl⟩ : syracuseStep 1552097 = 1164073) B1164073
theorem B1552115 : Blo 1032607 1552115 := bstep (se 1 (by rfl) ⟨1164086, by rfl⟩ : syracuseStep 1552115 = 2328173) B2328173
theorem B1552145 : Blo 1032607 1552145 := bstep (se 2 (by rfl) ⟨582054, by rfl⟩ : syracuseStep 1552145 = 1164109) B1164109
theorem B1552163 : Blo 1032607 1552163 := bstep (se 1 (by rfl) ⟨1164122, by rfl⟩ : syracuseStep 1552163 = 2328245) B2328245
theorem B1552193 : Blo 1032607 1552193 := bstep (se 2 (by rfl) ⟨582072, by rfl⟩ : syracuseStep 1552193 = 1164145) B1164145
theorem B1748803 : Blo 1032607 1748803 := bstep (se 1 (by rfl) ⟨1311602, by rfl⟩ : syracuseStep 1748803 = 2623205) B2623205
theorem B9940805 : Blo 1032607 9940805 := bstep (se 4 (by rfl) ⟨931950, by rfl⟩ : syracuseStep 9940805 = 1863901) B1863901
theorem B1552211 : Blo 1032607 1552211 := bstep (se 1 (by rfl) ⟨1164158, by rfl⟩ : syracuseStep 1552211 = 2328317) B2328317
theorem B1552241 : Blo 1032607 1552241 := bstep (se 2 (by rfl) ⟨582090, by rfl⟩ : syracuseStep 1552241 = 1164181) B1164181
theorem B1552259 : Blo 1032607 1552259 := bstep (se 1 (by rfl) ⟨1164194, by rfl⟩ : syracuseStep 1552259 = 2328389) B2328389
theorem B1552289 : Blo 1032607 1552289 := bstep (se 2 (by rfl) ⟨582108, by rfl⟩ : syracuseStep 1552289 = 1164217) B1164217
theorem B1552307 : Blo 1032607 1552307 := bstep (se 1 (by rfl) ⟨1164230, by rfl⟩ : syracuseStep 1552307 = 2328461) B2328461
theorem B3485645 : Blo 1032607 3485645 := bstep (se 3 (by rfl) ⟨653558, by rfl⟩ : syracuseStep 3485645 = 1307117) B1307117
theorem B1552337 : Blo 1032607 1552337 := bstep (se 2 (by rfl) ⟨582126, by rfl⟩ : syracuseStep 1552337 = 1164253) B1164253
theorem B1748945 : Blo 1032607 1748945 := bstep (se 2 (by rfl) ⟨655854, by rfl⟩ : syracuseStep 1748945 = 1311709) B1311709
theorem B1552355 : Blo 1032607 1552355 := bstep (se 1 (by rfl) ⟨1164266, by rfl⟩ : syracuseStep 1552355 = 2328533) B2328533
theorem B1552385 : Blo 1032607 1552385 := bstep (se 2 (by rfl) ⟨582144, by rfl⟩ : syracuseStep 1552385 = 1164289) B1164289
theorem B3485699 : Blo 1032607 3485699 := bstep (se 1 (by rfl) ⟨2614274, by rfl⟩ : syracuseStep 3485699 = 5228549) B5228549
theorem B6631429 : Blo 1032607 6631429 := bstep (se 4 (by rfl) ⟨621696, by rfl⟩ : syracuseStep 6631429 = 1243393) B1243393
theorem B1552403 : Blo 1032607 1552403 := bstep (se 1 (by rfl) ⟨1164302, by rfl⟩ : syracuseStep 1552403 = 2328605) B2328605
theorem B1552433 : Blo 1032607 1552433 := bstep (se 2 (by rfl) ⟨582162, by rfl⟩ : syracuseStep 1552433 = 1164325) B1164325
theorem B1552451 : Blo 1032607 1552451 := bstep (se 1 (by rfl) ⟨1164338, by rfl⟩ : syracuseStep 1552451 = 2328677) B2328677
theorem B10203205 : Blo 1032607 10203205 := bstep (se 4 (by rfl) ⟨956550, by rfl⟩ : syracuseStep 10203205 = 1913101) B1913101
theorem B1749073 : Blo 1032607 1749073 := bstep (se 2 (by rfl) ⟨655902, by rfl⟩ : syracuseStep 1749073 = 1311805) B1311805
theorem B1552481 : Blo 1032607 1552481 := bstep (se 2 (by rfl) ⟨582180, by rfl⟩ : syracuseStep 1552481 = 1164361) B1164361
theorem B1552499 : Blo 1032607 1552499 := bstep (se 1 (by rfl) ⟨1164374, by rfl⟩ : syracuseStep 1552499 = 2328749) B2328749
theorem B1749107 : Blo 1032607 1749107 := bstep (se 1 (by rfl) ⟨1311830, by rfl⟩ : syracuseStep 1749107 = 2623661) B2623661
theorem B1552529 : Blo 1032607 1552529 := bstep (se 2 (by rfl) ⟨582198, by rfl⟩ : syracuseStep 1552529 = 1164397) B1164397
theorem B1552547 : Blo 1032607 1552547 := bstep (se 1 (by rfl) ⟨1164410, by rfl⟩ : syracuseStep 1552547 = 2328821) B2328821
theorem B1552577 : Blo 1032607 1552577 := bstep (se 2 (by rfl) ⟨582216, by rfl⟩ : syracuseStep 1552577 = 1164433) B1164433
theorem B1552595 : Blo 1032607 1552595 := bstep (se 1 (by rfl) ⟨1164446, by rfl⟩ : syracuseStep 1552595 = 2328893) B2328893
theorem B1552625 : Blo 1032607 1552625 := bstep (se 2 (by rfl) ⟨582234, by rfl⟩ : syracuseStep 1552625 = 1164469) B1164469
theorem B1749235 : Blo 1032607 1749235 := bstep (se 1 (by rfl) ⟨1311926, by rfl⟩ : syracuseStep 1749235 = 2623853) B2623853
theorem B1552643 : Blo 1032607 1552643 := bstep (se 1 (by rfl) ⟨1164482, by rfl⟩ : syracuseStep 1552643 = 2328965) B2328965
theorem B3485969 : Blo 1032607 3485969 := bstep (se 2 (by rfl) ⟨1307238, by rfl⟩ : syracuseStep 3485969 = 2614477) B2614477
theorem B1552673 : Blo 1032607 1552673 := bstep (se 2 (by rfl) ⟨582252, by rfl⟩ : syracuseStep 1552673 = 1164505) B1164505
theorem B1257763 : Blo 1032607 1257763 := bstep (se 1 (by rfl) ⟨943322, by rfl⟩ : syracuseStep 1257763 = 1886645) B1886645
theorem B1552691 : Blo 1032607 1552691 := bstep (se 1 (by rfl) ⟨1164518, by rfl⟩ : syracuseStep 1552691 = 2329037) B2329037
theorem B1552721 : Blo 1032607 1552721 := bstep (se 2 (by rfl) ⟨582270, by rfl⟩ : syracuseStep 1552721 = 1164541) B1164541
theorem B1552739 : Blo 1032607 1552739 := bstep (se 1 (by rfl) ⟨1164554, by rfl⟩ : syracuseStep 1552739 = 2329109) B2329109
theorem B1552769 : Blo 1032607 1552769 := bstep (se 2 (by rfl) ⟨582288, by rfl⟩ : syracuseStep 1552769 = 1164577) B1164577
theorem B1552787 : Blo 1032607 1552787 := bstep (se 1 (by rfl) ⟨1164590, by rfl⟩ : syracuseStep 1552787 = 2329181) B2329181
theorem B1552817 : Blo 1032607 1552817 := bstep (se 2 (by rfl) ⟨582306, by rfl⟩ : syracuseStep 1552817 = 1164613) B1164613
theorem B1552835 : Blo 1032607 1552835 := bstep (se 1 (by rfl) ⟨1164626, by rfl⟩ : syracuseStep 1552835 = 2329253) B2329253
theorem B1552865 : Blo 1032607 1552865 := bstep (se 2 (by rfl) ⟨582324, by rfl⟩ : syracuseStep 1552865 = 1164649) B1164649
theorem B1552883 : Blo 1032607 1552883 := bstep (se 1 (by rfl) ⟨1164662, by rfl⟩ : syracuseStep 1552883 = 2329325) B2329325
theorem B1552913 : Blo 1032607 1552913 := bstep (se 2 (by rfl) ⟨582342, by rfl⟩ : syracuseStep 1552913 = 1164685) B1164685
theorem B1552931 : Blo 1032607 1552931 := bstep (se 1 (by rfl) ⟨1164698, by rfl⟩ : syracuseStep 1552931 = 2329397) B2329397
theorem B1552961 : Blo 1032607 1552961 := bstep (se 2 (by rfl) ⟨582360, by rfl⟩ : syracuseStep 1552961 = 1164721) B1164721
theorem B1552979 : Blo 1032607 1552979 := bstep (se 1 (by rfl) ⟨1164734, by rfl⟩ : syracuseStep 1552979 = 2329469) B2329469
theorem B1553009 : Blo 1032607 1553009 := bstep (se 2 (by rfl) ⟨582378, by rfl⟩ : syracuseStep 1553009 = 1164757) B1164757
theorem B1553027 : Blo 1032607 1553027 := bstep (se 1 (by rfl) ⟨1164770, by rfl⟩ : syracuseStep 1553027 = 2329541) B2329541
theorem B1553057 : Blo 1032607 1553057 := bstep (se 2 (by rfl) ⟨582396, by rfl⟩ : syracuseStep 1553057 = 1164793) B1164793
theorem B1553075 : Blo 1032607 1553075 := bstep (se 1 (by rfl) ⟨1164806, by rfl⟩ : syracuseStep 1553075 = 2329613) B2329613
theorem B1553105 : Blo 1032607 1553105 := bstep (se 2 (by rfl) ⟨582414, by rfl⟩ : syracuseStep 1553105 = 1164829) B1164829
theorem B1553123 : Blo 1032607 1553123 := bstep (se 1 (by rfl) ⟨1164842, by rfl⟩ : syracuseStep 1553123 = 2329685) B2329685
theorem B1553153 : Blo 1032607 1553153 := bstep (se 2 (by rfl) ⟨582432, by rfl⟩ : syracuseStep 1553153 = 1164865) B1164865
theorem B1553171 : Blo 1032607 1553171 := bstep (se 1 (by rfl) ⟨1164878, by rfl⟩ : syracuseStep 1553171 = 2329757) B2329757
theorem B3486509 : Blo 1032607 3486509 := bstep (se 3 (by rfl) ⟨653720, by rfl⟩ : syracuseStep 3486509 = 1307441) B1307441
theorem B1553201 : Blo 1032607 1553201 := bstep (se 2 (by rfl) ⟨582450, by rfl⟩ : syracuseStep 1553201 = 1164901) B1164901
theorem B1553219 : Blo 1032607 1553219 := bstep (se 1 (by rfl) ⟨1164914, by rfl⟩ : syracuseStep 1553219 = 2329829) B2329829
theorem B1553249 : Blo 1032607 1553249 := bstep (se 2 (by rfl) ⟨582468, by rfl⟩ : syracuseStep 1553249 = 1164937) B1164937
theorem B3486563 : Blo 1032607 3486563 := bstep (se 1 (by rfl) ⟨2614922, by rfl⟩ : syracuseStep 3486563 = 5229845) B5229845
theorem B1553267 : Blo 1032607 1553267 := bstep (se 1 (by rfl) ⟨1164950, by rfl⟩ : syracuseStep 1553267 = 2329901) B2329901
theorem B1553297 : Blo 1032607 1553297 := bstep (se 2 (by rfl) ⟨582486, by rfl⟩ : syracuseStep 1553297 = 1164973) B1164973
theorem B1553315 : Blo 1032607 1553315 := bstep (se 1 (by rfl) ⟨1164986, by rfl⟩ : syracuseStep 1553315 = 2329973) B2329973
theorem B1553345 : Blo 1032607 1553345 := bstep (se 2 (by rfl) ⟨582504, by rfl⟩ : syracuseStep 1553345 = 1165009) B1165009
theorem B1553363 : Blo 1032607 1553363 := bstep (se 1 (by rfl) ⟨1165022, by rfl⟩ : syracuseStep 1553363 = 2330045) B2330045
theorem B1553393 : Blo 1032607 1553393 := bstep (se 2 (by rfl) ⟨582522, by rfl⟩ : syracuseStep 1553393 = 1165045) B1165045
theorem B1553411 : Blo 1032607 1553411 := bstep (se 1 (by rfl) ⟨1165058, by rfl⟩ : syracuseStep 1553411 = 2330117) B2330117
theorem B1553441 : Blo 1032607 1553441 := bstep (se 2 (by rfl) ⟨582540, by rfl⟩ : syracuseStep 1553441 = 1165081) B1165081
theorem B1553459 : Blo 1032607 1553459 := bstep (se 1 (by rfl) ⟨1165094, by rfl⟩ : syracuseStep 1553459 = 2330189) B2330189
theorem B1553489 : Blo 1032607 1553489 := bstep (se 2 (by rfl) ⟨582558, by rfl⟩ : syracuseStep 1553489 = 1165117) B1165117
theorem B1553507 : Blo 1032607 1553507 := bstep (se 1 (by rfl) ⟨1165130, by rfl⟩ : syracuseStep 1553507 = 2330261) B2330261
theorem B3486833 : Blo 1032607 3486833 := bstep (se 2 (by rfl) ⟨1307562, by rfl⟩ : syracuseStep 3486833 = 2615125) B2615125
theorem B1553537 : Blo 1032607 1553537 := bstep (se 2 (by rfl) ⟨582576, by rfl⟩ : syracuseStep 1553537 = 1165153) B1165153
theorem B1553555 : Blo 1032607 1553555 := bstep (se 1 (by rfl) ⟨1165166, by rfl⟩ : syracuseStep 1553555 = 2330333) B2330333
theorem B1553585 : Blo 1032607 1553585 := bstep (se 2 (by rfl) ⟨582594, by rfl⟩ : syracuseStep 1553585 = 1165189) B1165189
theorem B1553603 : Blo 1032607 1553603 := bstep (se 1 (by rfl) ⟨1165202, by rfl⟩ : syracuseStep 1553603 = 2330405) B2330405
theorem B1553633 : Blo 1032607 1553633 := bstep (se 2 (by rfl) ⟨582612, by rfl⟩ : syracuseStep 1553633 = 1165225) B1165225
theorem B1553651 : Blo 1032607 1553651 := bstep (se 1 (by rfl) ⟨1165238, by rfl⟩ : syracuseStep 1553651 = 2330477) B2330477
theorem B1553681 : Blo 1032607 1553681 := bstep (se 2 (by rfl) ⟨582630, by rfl⟩ : syracuseStep 1553681 = 1165261) B1165261
theorem B1553699 : Blo 1032607 1553699 := bstep (se 1 (by rfl) ⟨1165274, by rfl⟩ : syracuseStep 1553699 = 2330549) B2330549
theorem B1553729 : Blo 1032607 1553729 := bstep (se 2 (by rfl) ⟨582648, by rfl⟩ : syracuseStep 1553729 = 1165297) B1165297
theorem B1553747 : Blo 1032607 1553747 := bstep (se 1 (by rfl) ⟨1165310, by rfl⟩ : syracuseStep 1553747 = 2330621) B2330621
theorem B1553777 : Blo 1032607 1553777 := bstep (se 2 (by rfl) ⟨582666, by rfl⟩ : syracuseStep 1553777 = 1165333) B1165333
theorem B1553795 : Blo 1032607 1553795 := bstep (se 1 (by rfl) ⟨1165346, by rfl⟩ : syracuseStep 1553795 = 2330693) B2330693
theorem B1553825 : Blo 1032607 1553825 := bstep (se 2 (by rfl) ⟨582684, by rfl⟩ : syracuseStep 1553825 = 1165369) B1165369
theorem B1553843 : Blo 1032607 1553843 := bstep (se 1 (by rfl) ⟨1165382, by rfl⟩ : syracuseStep 1553843 = 2330765) B2330765
theorem B2799053 : Blo 1032607 2799053 := bstep (se 3 (by rfl) ⟨524822, by rfl⟩ : syracuseStep 2799053 = 1049645) B1049645
theorem B1553873 : Blo 1032607 1553873 := bstep (se 2 (by rfl) ⟨582702, by rfl⟩ : syracuseStep 1553873 = 1165405) B1165405
theorem B1553891 : Blo 1032607 1553891 := bstep (se 1 (by rfl) ⟨1165418, by rfl⟩ : syracuseStep 1553891 = 2330837) B2330837
theorem B1553921 : Blo 1032607 1553921 := bstep (se 2 (by rfl) ⟨582720, by rfl⟩ : syracuseStep 1553921 = 1165441) B1165441
theorem B1553939 : Blo 1032607 1553939 := bstep (se 1 (by rfl) ⟨1165454, by rfl⟩ : syracuseStep 1553939 = 2330909) B2330909
theorem B2209315 : Blo 1032607 2209315 := bstep (se 1 (by rfl) ⟨1656986, by rfl⟩ : syracuseStep 2209315 = 3313973) B3313973
theorem B1553969 : Blo 1032607 1553969 := bstep (se 2 (by rfl) ⟨582738, by rfl⟩ : syracuseStep 1553969 = 1165477) B1165477
theorem B1553987 : Blo 1032607 1553987 := bstep (se 1 (by rfl) ⟨1165490, by rfl⟩ : syracuseStep 1553987 = 2330981) B2330981
theorem B1554017 : Blo 1032607 1554017 := bstep (se 2 (by rfl) ⟨582756, by rfl⟩ : syracuseStep 1554017 = 1165513) B1165513
theorem B6731363 : Blo 1032607 6731363 := bstep (se 1 (by rfl) ⟨5048522, by rfl⟩ : syracuseStep 6731363 = 10097045) B10097045
theorem B1554035 : Blo 1032607 1554035 := bstep (se 1 (by rfl) ⟨1165526, by rfl⟩ : syracuseStep 1554035 = 2331053) B2331053
theorem B2799235 : Blo 1032607 2799235 := bstep (se 1 (by rfl) ⟨2099426, by rfl⟩ : syracuseStep 2799235 = 4198853) B4198853
theorem B3487373 : Blo 1032607 3487373 := bstep (se 3 (by rfl) ⟨653882, by rfl⟩ : syracuseStep 3487373 = 1307765) B1307765
theorem B10761869 : Blo 1032607 10761869 := bstep (se 3 (by rfl) ⟨2017850, by rfl⟩ : syracuseStep 10761869 = 4035701) B4035701
theorem B1554065 : Blo 1032607 1554065 := bstep (se 2 (by rfl) ⟨582774, by rfl⟩ : syracuseStep 1554065 = 1165549) B1165549
theorem B1554083 : Blo 1032607 1554083 := bstep (se 1 (by rfl) ⟨1165562, by rfl⟩ : syracuseStep 1554083 = 2331125) B2331125
theorem B1554113 : Blo 1032607 1554113 := bstep (se 2 (by rfl) ⟨582792, by rfl⟩ : syracuseStep 1554113 = 1165585) B1165585
theorem B3487427 : Blo 1032607 3487427 := bstep (se 1 (by rfl) ⟨2615570, by rfl⟩ : syracuseStep 3487427 = 5231141) B5231141
theorem B1554131 : Blo 1032607 1554131 := bstep (se 1 (by rfl) ⟨1165598, by rfl⟩ : syracuseStep 1554131 = 2331197) B2331197
theorem B1554161 : Blo 1032607 1554161 := bstep (se 2 (by rfl) ⟨582810, by rfl⟩ : syracuseStep 1554161 = 1165621) B1165621
theorem B1554179 : Blo 1032607 1554179 := bstep (se 1 (by rfl) ⟨1165634, by rfl⟩ : syracuseStep 1554179 = 2331269) B2331269
theorem B1455889 : Blo 1032607 1455889 := bstep (se 2 (by rfl) ⟨545958, by rfl⟩ : syracuseStep 1455889 = 1091917) B1091917
theorem B1554209 : Blo 1032607 1554209 := bstep (se 2 (by rfl) ⟨582828, by rfl⟩ : syracuseStep 1554209 = 1165657) B1165657
theorem B1554227 : Blo 1032607 1554227 := bstep (se 1 (by rfl) ⟨1165670, by rfl⟩ : syracuseStep 1554227 = 2331341) B2331341
theorem B1554257 : Blo 1032607 1554257 := bstep (se 2 (by rfl) ⟨582846, by rfl⟩ : syracuseStep 1554257 = 1165693) B1165693
theorem B1554275 : Blo 1032607 1554275 := bstep (se 1 (by rfl) ⟨1165706, by rfl⟩ : syracuseStep 1554275 = 2331413) B2331413
theorem B1554305 : Blo 1032607 1554305 := bstep (se 2 (by rfl) ⟨582864, by rfl⟩ : syracuseStep 1554305 = 1165729) B1165729
theorem B1554323 : Blo 1032607 1554323 := bstep (se 1 (by rfl) ⟨1165742, by rfl⟩ : syracuseStep 1554323 = 2331485) B2331485
theorem B1554353 : Blo 1032607 1554353 := bstep (se 2 (by rfl) ⟨582882, by rfl⟩ : syracuseStep 1554353 = 1165765) B1165765
theorem B1554371 : Blo 1032607 1554371 := bstep (se 1 (by rfl) ⟨1165778, by rfl⟩ : syracuseStep 1554371 = 2331557) B2331557
theorem B3487697 : Blo 1032607 3487697 := bstep (se 2 (by rfl) ⟨1307886, by rfl⟩ : syracuseStep 3487697 = 2615773) B2615773
theorem B1554401 : Blo 1032607 1554401 := bstep (se 2 (by rfl) ⟨582900, by rfl⟩ : syracuseStep 1554401 = 1165801) B1165801
theorem B8501233 : Blo 1032607 8501233 := bstep (se 2 (by rfl) ⟨3187962, by rfl⟩ : syracuseStep 8501233 = 6375925) B6375925
theorem B1554419 : Blo 1032607 1554419 := bstep (se 1 (by rfl) ⟨1165814, by rfl⟩ : syracuseStep 1554419 = 2331629) B2331629
theorem B1554449 : Blo 1032607 1554449 := bstep (se 2 (by rfl) ⟨582918, by rfl⟩ : syracuseStep 1554449 = 1165837) B1165837
theorem B1554467 : Blo 1032607 1554467 := bstep (se 1 (by rfl) ⟨1165850, by rfl⟩ : syracuseStep 1554467 = 2331701) B2331701
theorem B2242609 : Blo 1032607 2242609 := bstep (se 2 (by rfl) ⟨840978, by rfl⟩ : syracuseStep 2242609 = 1681957) B1681957
theorem B1554497 : Blo 1032607 1554497 := bstep (se 2 (by rfl) ⟨582936, by rfl⟩ : syracuseStep 1554497 = 1165873) B1165873
theorem B1554515 : Blo 1032607 1554515 := bstep (se 1 (by rfl) ⟨1165886, by rfl⟩ : syracuseStep 1554515 = 2331773) B2331773
theorem B1554545 : Blo 1032607 1554545 := bstep (se 2 (by rfl) ⟨582954, by rfl⟩ : syracuseStep 1554545 = 1165909) B1165909
theorem B1554563 : Blo 1032607 1554563 := bstep (se 1 (by rfl) ⟨1165922, by rfl⟩ : syracuseStep 1554563 = 2331845) B2331845
theorem B1554593 : Blo 1032607 1554593 := bstep (se 2 (by rfl) ⟨582972, by rfl⟩ : syracuseStep 1554593 = 1165945) B1165945
theorem B3356849 : Blo 1032607 3356849 := bstep (se 2 (by rfl) ⟨1258818, by rfl⟩ : syracuseStep 3356849 = 2517637) B2517637
theorem B1554611 : Blo 1032607 1554611 := bstep (se 1 (by rfl) ⟨1165958, by rfl⟩ : syracuseStep 1554611 = 2331917) B2331917
theorem B1554641 : Blo 1032607 1554641 := bstep (se 2 (by rfl) ⟨582990, by rfl⟩ : syracuseStep 1554641 = 1165981) B1165981
theorem B1554659 : Blo 1032607 1554659 := bstep (se 1 (by rfl) ⟨1165994, by rfl⟩ : syracuseStep 1554659 = 2331989) B2331989
theorem B1554689 : Blo 1032607 1554689 := bstep (se 2 (by rfl) ⟨583008, by rfl⟩ : syracuseStep 1554689 = 1166017) B1166017
theorem B1554707 : Blo 1032607 1554707 := bstep (se 1 (by rfl) ⟨1166030, by rfl⟩ : syracuseStep 1554707 = 2332061) B2332061
theorem B1554737 : Blo 1032607 1554737 := bstep (se 2 (by rfl) ⟨583026, by rfl⟩ : syracuseStep 1554737 = 1166053) B1166053
theorem B1554755 : Blo 1032607 1554755 := bstep (se 1 (by rfl) ⟨1166066, by rfl⟩ : syracuseStep 1554755 = 2332133) B2332133
theorem B1554785 : Blo 1032607 1554785 := bstep (se 2 (by rfl) ⟨583044, by rfl⟩ : syracuseStep 1554785 = 1166089) B1166089
theorem B2210161 : Blo 1032607 2210161 := bstep (se 2 (by rfl) ⟨828810, by rfl⟩ : syracuseStep 2210161 = 1657621) B1657621
theorem B1554803 : Blo 1032607 1554803 := bstep (se 1 (by rfl) ⟨1166102, by rfl⟩ : syracuseStep 1554803 = 2332205) B2332205
theorem B1554833 : Blo 1032607 1554833 := bstep (se 2 (by rfl) ⟨583062, by rfl⟩ : syracuseStep 1554833 = 1166125) B1166125
theorem B1554851 : Blo 1032607 1554851 := bstep (se 1 (by rfl) ⟨1166138, by rfl⟩ : syracuseStep 1554851 = 2332277) B2332277
theorem B1554881 : Blo 1032607 1554881 := bstep (se 2 (by rfl) ⟨583080, by rfl⟩ : syracuseStep 1554881 = 1166161) B1166161
theorem B1554899 : Blo 1032607 1554899 := bstep (se 1 (by rfl) ⟨1166174, by rfl⟩ : syracuseStep 1554899 = 2332349) B2332349
theorem B3488237 : Blo 1032607 3488237 := bstep (se 3 (by rfl) ⟨654044, by rfl⟩ : syracuseStep 3488237 = 1308089) B1308089
theorem B1161715 : Blo 1032607 1161715 := bstep (se 1 (by rfl) ⟨871286, by rfl⟩ : syracuseStep 1161715 = 1742573) B1742573
theorem B3488291 : Blo 1032607 3488291 := bstep (se 1 (by rfl) ⟨2616218, by rfl⟩ : syracuseStep 3488291 = 5232437) B5232437
theorem B7846469 : Blo 1032607 7846469 := bstep (se 4 (by rfl) ⟨735606, by rfl⟩ : syracuseStep 7846469 = 1471213) B1471213
theorem B1161859 : Blo 1032607 1161859 := bstep (se 1 (by rfl) ⟨871394, by rfl⟩ : syracuseStep 1161859 = 1742789) B1742789
theorem B2800273 : Blo 1032607 2800273 := bstep (se 2 (by rfl) ⟨1050102, by rfl⟩ : syracuseStep 2800273 = 2100205) B2100205
theorem B1162003 : Blo 1032607 1162003 := bstep (se 1 (by rfl) ⟨871502, by rfl⟩ : syracuseStep 1162003 = 1743005) B1743005
theorem B3488561 : Blo 1032607 3488561 := bstep (se 2 (by rfl) ⟨1308210, by rfl⟩ : syracuseStep 3488561 = 2616421) B2616421
theorem B8829809 : Blo 1032607 8829809 := bstep (se 2 (by rfl) ⟨3311178, by rfl⟩ : syracuseStep 8829809 = 6622357) B6622357
theorem B1162147 : Blo 1032607 1162147 := bstep (se 1 (by rfl) ⟨871610, by rfl⟩ : syracuseStep 1162147 = 1743221) B1743221
theorem B1162291 : Blo 1032607 1162291 := bstep (se 1 (by rfl) ⟨871718, by rfl⟩ : syracuseStep 1162291 = 1743437) B1743437
theorem B30194801 : Blo 1032607 30194801 := bstep (se 2 (by rfl) ⟨11323050, by rfl⟩ : syracuseStep 30194801 = 22646101) B22646101
theorem B1162435 : Blo 1032607 1162435 := bstep (se 1 (by rfl) ⟨871826, by rfl⟩ : syracuseStep 1162435 = 1743653) B1743653
theorem B3489101 : Blo 1032607 3489101 := bstep (se 3 (by rfl) ⟨654206, by rfl⟩ : syracuseStep 3489101 = 1308413) B1308413
theorem B1162579 : Blo 1032607 1162579 := bstep (se 1 (by rfl) ⟨871934, by rfl⟩ : syracuseStep 1162579 = 1743869) B1743869
theorem B3489155 : Blo 1032607 3489155 := bstep (se 1 (by rfl) ⟨2616866, by rfl⟩ : syracuseStep 3489155 = 5233733) B5233733
theorem B1162723 : Blo 1032607 1162723 := bstep (se 1 (by rfl) ⟨872042, by rfl⟩ : syracuseStep 1162723 = 1744085) B1744085
theorem B6634993 : Blo 1032607 6634993 := bstep (se 2 (by rfl) ⟨2488122, by rfl⟩ : syracuseStep 6634993 = 4976245) B4976245
theorem B1162867 : Blo 1032607 1162867 := bstep (se 1 (by rfl) ⟨872150, by rfl⟩ : syracuseStep 1162867 = 1744301) B1744301
theorem B3489425 : Blo 1032607 3489425 := bstep (se 2 (by rfl) ⟨1308534, by rfl⟩ : syracuseStep 3489425 = 2617069) B2617069
theorem B1163011 : Blo 1032607 1163011 := bstep (se 1 (by rfl) ⟨872258, by rfl⟩ : syracuseStep 1163011 = 1744517) B1744517
theorem B5881733 : Blo 1032607 5881733 := bstep (se 4 (by rfl) ⟨551412, by rfl⟩ : syracuseStep 5881733 = 1102825) B1102825
theorem B1163155 : Blo 1032607 1163155 := bstep (se 1 (by rfl) ⟨872366, by rfl⟩ : syracuseStep 1163155 = 1744733) B1744733
theorem B1654705 : Blo 1032607 1654705 := bstep (se 2 (by rfl) ⟨620514, by rfl⟩ : syracuseStep 1654705 = 1241029) B1241029
theorem B1163299 : Blo 1032607 1163299 := bstep (se 1 (by rfl) ⟨872474, by rfl⟩ : syracuseStep 1163299 = 1744949) B1744949
theorem B3489965 : Blo 1032607 3489965 := bstep (se 3 (by rfl) ⟨654368, by rfl⟩ : syracuseStep 3489965 = 1308737) B1308737
theorem B1163443 : Blo 1032607 1163443 := bstep (se 1 (by rfl) ⟨872582, by rfl⟩ : syracuseStep 1163443 = 1745165) B1745165
theorem B2212049 : Blo 1032607 2212049 := bstep (se 2 (by rfl) ⟨829518, by rfl⟩ : syracuseStep 2212049 = 1659037) B1659037
theorem B3490019 : Blo 1032607 3490019 := bstep (se 1 (by rfl) ⟨2617514, by rfl⟩ : syracuseStep 3490019 = 5235029) B5235029
theorem B1163587 : Blo 1032607 1163587 := bstep (se 1 (by rfl) ⟨872690, by rfl⟩ : syracuseStep 1163587 = 1745381) B1745381
theorem B1032611 : Blo 1032607 1032611 := bstep (se 1 (by rfl) ⟨774458, by rfl⟩ : syracuseStep 1032611 = 1548917) B1548917
theorem B1032627 : Blo 1032607 1032627 := bstep (se 1 (by rfl) ⟨774470, by rfl⟩ : syracuseStep 1032627 = 1548941) B1548941
theorem B1032643 : Blo 1032607 1032643 := bstep (se 1 (by rfl) ⟨774482, by rfl⟩ : syracuseStep 1032643 = 1548965) B1548965
theorem B1032659 : Blo 1032607 1032659 := bstep (se 1 (by rfl) ⟨774494, by rfl⟩ : syracuseStep 1032659 = 1548989) B1548989
theorem B1163731 : Blo 1032607 1163731 := bstep (se 1 (by rfl) ⟨872798, by rfl⟩ : syracuseStep 1163731 = 1745597) B1745597
theorem B1032675 : Blo 1032607 1032675 := bstep (se 1 (by rfl) ⟨774506, by rfl⟩ : syracuseStep 1032675 = 1549013) B1549013
theorem B3490289 : Blo 1032607 3490289 := bstep (se 2 (by rfl) ⟨1308858, by rfl⟩ : syracuseStep 3490289 = 2617717) B2617717
theorem B1032691 : Blo 1032607 1032691 := bstep (se 1 (by rfl) ⟨774518, by rfl⟩ : syracuseStep 1032691 = 1549037) B1549037
theorem B1032707 : Blo 1032607 1032707 := bstep (se 1 (by rfl) ⟨774530, by rfl⟩ : syracuseStep 1032707 = 1549061) B1549061
theorem B1032723 : Blo 1032607 1032723 := bstep (se 1 (by rfl) ⟨774542, by rfl⟩ : syracuseStep 1032723 = 1549085) B1549085
theorem B1032739 : Blo 1032607 1032739 := bstep (se 1 (by rfl) ⟨774554, by rfl⟩ : syracuseStep 1032739 = 1549109) B1549109
theorem B1032755 : Blo 1032607 1032755 := bstep (se 1 (by rfl) ⟨774566, by rfl⟩ : syracuseStep 1032755 = 1549133) B1549133
theorem B1032771 : Blo 1032607 1032771 := bstep (se 1 (by rfl) ⟨774578, by rfl⟩ : syracuseStep 1032771 = 1549157) B1549157
theorem B1032787 : Blo 1032607 1032787 := bstep (se 1 (by rfl) ⟨774590, by rfl⟩ : syracuseStep 1032787 = 1549181) B1549181
theorem B1032803 : Blo 1032607 1032803 := bstep (se 1 (by rfl) ⟨774602, by rfl⟩ : syracuseStep 1032803 = 1549205) B1549205
theorem B1163875 : Blo 1032607 1163875 := bstep (se 1 (by rfl) ⟨872906, by rfl⟩ : syracuseStep 1163875 = 1745813) B1745813
theorem B1032819 : Blo 1032607 1032819 := bstep (se 1 (by rfl) ⟨774614, by rfl⟩ : syracuseStep 1032819 = 1549229) B1549229
theorem B1032835 : Blo 1032607 1032835 := bstep (se 1 (by rfl) ⟨774626, by rfl⟩ : syracuseStep 1032835 = 1549253) B1549253
theorem B1032851 : Blo 1032607 1032851 := bstep (se 1 (by rfl) ⟨774638, by rfl⟩ : syracuseStep 1032851 = 1549277) B1549277
theorem B1032867 : Blo 1032607 1032867 := bstep (se 1 (by rfl) ⟨774650, by rfl⟩ : syracuseStep 1032867 = 1549301) B1549301
theorem B1032883 : Blo 1032607 1032883 := bstep (se 1 (by rfl) ⟨774662, by rfl⟩ : syracuseStep 1032883 = 1549325) B1549325
theorem B1032899 : Blo 1032607 1032899 := bstep (se 1 (by rfl) ⟨774674, by rfl⟩ : syracuseStep 1032899 = 1549349) B1549349
theorem B1032915 : Blo 1032607 1032915 := bstep (se 1 (by rfl) ⟨774686, by rfl⟩ : syracuseStep 1032915 = 1549373) B1549373
theorem B1032931 : Blo 1032607 1032931 := bstep (se 1 (by rfl) ⟨774698, by rfl⟩ : syracuseStep 1032931 = 1549397) B1549397
theorem B1032947 : Blo 1032607 1032947 := bstep (se 1 (by rfl) ⟨774710, by rfl⟩ : syracuseStep 1032947 = 1549421) B1549421
theorem B1164019 : Blo 1032607 1164019 := bstep (se 1 (by rfl) ⟨873014, by rfl⟩ : syracuseStep 1164019 = 1746029) B1746029
theorem B1032963 : Blo 1032607 1032963 := bstep (se 1 (by rfl) ⟨774722, by rfl⟩ : syracuseStep 1032963 = 1549445) B1549445
theorem B1032979 : Blo 1032607 1032979 := bstep (se 1 (by rfl) ⟨774734, by rfl⟩ : syracuseStep 1032979 = 1549469) B1549469
theorem B1032995 : Blo 1032607 1032995 := bstep (se 1 (by rfl) ⟨774746, by rfl⟩ : syracuseStep 1032995 = 1549493) B1549493
theorem B1033011 : Blo 1032607 1033011 := bstep (se 1 (by rfl) ⟨774758, by rfl⟩ : syracuseStep 1033011 = 1549517) B1549517
theorem B1033027 : Blo 1032607 1033027 := bstep (se 1 (by rfl) ⟨774770, by rfl⟩ : syracuseStep 1033027 = 1549541) B1549541
theorem B1033043 : Blo 1032607 1033043 := bstep (se 1 (by rfl) ⟨774782, by rfl⟩ : syracuseStep 1033043 = 1549565) B1549565
theorem B1033059 : Blo 1032607 1033059 := bstep (se 1 (by rfl) ⟨774794, by rfl⟩ : syracuseStep 1033059 = 1549589) B1549589
theorem B1033075 : Blo 1032607 1033075 := bstep (se 1 (by rfl) ⟨774806, by rfl⟩ : syracuseStep 1033075 = 1549613) B1549613
theorem B1033091 : Blo 1032607 1033091 := bstep (se 1 (by rfl) ⟨774818, by rfl⟩ : syracuseStep 1033091 = 1549637) B1549637
theorem B1164163 : Blo 1032607 1164163 := bstep (se 1 (by rfl) ⟨873122, by rfl⟩ : syracuseStep 1164163 = 1746245) B1746245
theorem B1033107 : Blo 1032607 1033107 := bstep (se 1 (by rfl) ⟨774830, by rfl⟩ : syracuseStep 1033107 = 1549661) B1549661
theorem B1196947 : Blo 1032607 1196947 := bstep (se 1 (by rfl) ⟨897710, by rfl⟩ : syracuseStep 1196947 = 1795421) B1795421
theorem B1033123 : Blo 1032607 1033123 := bstep (se 1 (by rfl) ⟨774842, by rfl⟩ : syracuseStep 1033123 = 1549685) B1549685
theorem B1033139 : Blo 1032607 1033139 := bstep (se 1 (by rfl) ⟨774854, by rfl⟩ : syracuseStep 1033139 = 1549709) B1549709
theorem B1033155 : Blo 1032607 1033155 := bstep (se 1 (by rfl) ⟨774866, by rfl⟩ : syracuseStep 1033155 = 1549733) B1549733
theorem B1033171 : Blo 1032607 1033171 := bstep (se 1 (by rfl) ⟨774878, by rfl⟩ : syracuseStep 1033171 = 1549757) B1549757
theorem B1033187 : Blo 1032607 1033187 := bstep (se 1 (by rfl) ⟨774890, by rfl⟩ : syracuseStep 1033187 = 1549781) B1549781
theorem B1033203 : Blo 1032607 1033203 := bstep (se 1 (by rfl) ⟨774902, by rfl⟩ : syracuseStep 1033203 = 1549805) B1549805
theorem B1655795 : Blo 1032607 1655795 := bstep (se 1 (by rfl) ⟨1241846, by rfl⟩ : syracuseStep 1655795 = 2483693) B2483693
theorem B1033219 : Blo 1032607 1033219 := bstep (se 1 (by rfl) ⟨774914, by rfl⟩ : syracuseStep 1033219 = 1549829) B1549829
theorem B3490829 : Blo 1032607 3490829 := bstep (se 3 (by rfl) ⟨654530, by rfl⟩ : syracuseStep 3490829 = 1309061) B1309061
theorem B1033235 : Blo 1032607 1033235 := bstep (se 1 (by rfl) ⟨774926, by rfl⟩ : syracuseStep 1033235 = 1549853) B1549853
theorem B1164307 : Blo 1032607 1164307 := bstep (se 1 (by rfl) ⟨873230, by rfl⟩ : syracuseStep 1164307 = 1746461) B1746461
theorem B1033251 : Blo 1032607 1033251 := bstep (se 1 (by rfl) ⟨774938, by rfl⟩ : syracuseStep 1033251 = 1549877) B1549877
theorem B1033267 : Blo 1032607 1033267 := bstep (se 1 (by rfl) ⟨774950, by rfl⟩ : syracuseStep 1033267 = 1549901) B1549901
theorem B1033283 : Blo 1032607 1033283 := bstep (se 1 (by rfl) ⟨774962, by rfl⟩ : syracuseStep 1033283 = 1549925) B1549925
theorem B3490883 : Blo 1032607 3490883 := bstep (se 1 (by rfl) ⟨2618162, by rfl⟩ : syracuseStep 3490883 = 5236325) B5236325
theorem B1033299 : Blo 1032607 1033299 := bstep (se 1 (by rfl) ⟨774974, by rfl⟩ : syracuseStep 1033299 = 1549949) B1549949
theorem B1033315 : Blo 1032607 1033315 := bstep (se 1 (by rfl) ⟨774986, by rfl⟩ : syracuseStep 1033315 = 1549973) B1549973
theorem B1033331 : Blo 1032607 1033331 := bstep (se 1 (by rfl) ⟨774998, by rfl⟩ : syracuseStep 1033331 = 1549997) B1549997
theorem B1033347 : Blo 1032607 1033347 := bstep (se 1 (by rfl) ⟨775010, by rfl⟩ : syracuseStep 1033347 = 1550021) B1550021
theorem B1033363 : Blo 1032607 1033363 := bstep (se 1 (by rfl) ⟨775022, by rfl⟩ : syracuseStep 1033363 = 1550045) B1550045
theorem B1033379 : Blo 1032607 1033379 := bstep (se 1 (by rfl) ⟨775034, by rfl⟩ : syracuseStep 1033379 = 1550069) B1550069
theorem B1164451 : Blo 1032607 1164451 := bstep (se 1 (by rfl) ⟨873338, by rfl⟩ : syracuseStep 1164451 = 1746677) B1746677
theorem B1033395 : Blo 1032607 1033395 := bstep (se 1 (by rfl) ⟨775046, by rfl⟩ : syracuseStep 1033395 = 1550093) B1550093
theorem B1033411 : Blo 1032607 1033411 := bstep (se 1 (by rfl) ⟨775058, by rfl⟩ : syracuseStep 1033411 = 1550117) B1550117
theorem B1033427 : Blo 1032607 1033427 := bstep (se 1 (by rfl) ⟨775070, by rfl⟩ : syracuseStep 1033427 = 1550141) B1550141
theorem B1033443 : Blo 1032607 1033443 := bstep (se 1 (by rfl) ⟨775082, by rfl⟩ : syracuseStep 1033443 = 1550165) B1550165
theorem B1033459 : Blo 1032607 1033459 := bstep (se 1 (by rfl) ⟨775094, by rfl⟩ : syracuseStep 1033459 = 1550189) B1550189
theorem B1033475 : Blo 1032607 1033475 := bstep (se 1 (by rfl) ⟨775106, by rfl⟩ : syracuseStep 1033475 = 1550213) B1550213
theorem B1033491 : Blo 1032607 1033491 := bstep (se 1 (by rfl) ⟨775118, by rfl⟩ : syracuseStep 1033491 = 1550237) B1550237
theorem B1656083 : Blo 1032607 1656083 := bstep (se 1 (by rfl) ⟨1242062, by rfl⟩ : syracuseStep 1656083 = 2484125) B2484125
theorem B1033507 : Blo 1032607 1033507 := bstep (se 1 (by rfl) ⟨775130, by rfl⟩ : syracuseStep 1033507 = 1550261) B1550261
theorem B1033523 : Blo 1032607 1033523 := bstep (se 1 (by rfl) ⟨775142, by rfl⟩ : syracuseStep 1033523 = 1550285) B1550285
theorem B1164595 : Blo 1032607 1164595 := bstep (se 1 (by rfl) ⟨873446, by rfl⟩ : syracuseStep 1164595 = 1746893) B1746893
theorem B1033539 : Blo 1032607 1033539 := bstep (se 1 (by rfl) ⟨775154, by rfl⟩ : syracuseStep 1033539 = 1550309) B1550309
theorem B3491153 : Blo 1032607 3491153 := bstep (se 2 (by rfl) ⟨1309182, by rfl⟩ : syracuseStep 3491153 = 2618365) B2618365
theorem B1033555 : Blo 1032607 1033555 := bstep (se 1 (by rfl) ⟨775166, by rfl⟩ : syracuseStep 1033555 = 1550333) B1550333
theorem B1033571 : Blo 1032607 1033571 := bstep (se 1 (by rfl) ⟨775178, by rfl⟩ : syracuseStep 1033571 = 1550357) B1550357
theorem B1033587 : Blo 1032607 1033587 := bstep (se 1 (by rfl) ⟨775190, by rfl⟩ : syracuseStep 1033587 = 1550381) B1550381
theorem B1033603 : Blo 1032607 1033603 := bstep (se 1 (by rfl) ⟨775202, by rfl⟩ : syracuseStep 1033603 = 1550405) B1550405
theorem B1033619 : Blo 1032607 1033619 := bstep (se 1 (by rfl) ⟨775214, by rfl⟩ : syracuseStep 1033619 = 1550429) B1550429
theorem B1033635 : Blo 1032607 1033635 := bstep (se 1 (by rfl) ⟨775226, by rfl⟩ : syracuseStep 1033635 = 1550453) B1550453
theorem B1033651 : Blo 1032607 1033651 := bstep (se 1 (by rfl) ⟨775238, by rfl⟩ : syracuseStep 1033651 = 1550477) B1550477
theorem B1033667 : Blo 1032607 1033667 := bstep (se 1 (by rfl) ⟨775250, by rfl⟩ : syracuseStep 1033667 = 1550501) B1550501
theorem B1164739 : Blo 1032607 1164739 := bstep (se 1 (by rfl) ⟨873554, by rfl⟩ : syracuseStep 1164739 = 1747109) B1747109
theorem B1033683 : Blo 1032607 1033683 := bstep (se 1 (by rfl) ⟨775262, by rfl⟩ : syracuseStep 1033683 = 1550525) B1550525
theorem B1033699 : Blo 1032607 1033699 := bstep (se 1 (by rfl) ⟨775274, by rfl⟩ : syracuseStep 1033699 = 1550549) B1550549
theorem B15943139 : Blo 1032607 15943139 := bstep (se 1 (by rfl) ⟨11957354, by rfl⟩ : syracuseStep 15943139 = 23914709) B23914709
theorem B2213347 : Blo 1032607 2213347 := bstep (se 1 (by rfl) ⟨1660010, by rfl⟩ : syracuseStep 2213347 = 3320021) B3320021
theorem B1033715 : Blo 1032607 1033715 := bstep (se 1 (by rfl) ⟨775286, by rfl⟩ : syracuseStep 1033715 = 1550573) B1550573
theorem B1033731 : Blo 1032607 1033731 := bstep (se 1 (by rfl) ⟨775298, by rfl⟩ : syracuseStep 1033731 = 1550597) B1550597
theorem B3982861 : Blo 1032607 3982861 := bstep (se 3 (by rfl) ⟨746786, by rfl⟩ : syracuseStep 3982861 = 1493573) B1493573
theorem B1033747 : Blo 1032607 1033747 := bstep (se 1 (by rfl) ⟨775310, by rfl⟩ : syracuseStep 1033747 = 1550621) B1550621
theorem B1033763 : Blo 1032607 1033763 := bstep (se 1 (by rfl) ⟨775322, by rfl⟩ : syracuseStep 1033763 = 1550645) B1550645
theorem B1033779 : Blo 1032607 1033779 := bstep (se 1 (by rfl) ⟨775334, by rfl⟩ : syracuseStep 1033779 = 1550669) B1550669
theorem B1033795 : Blo 1032607 1033795 := bstep (se 1 (by rfl) ⟨775346, by rfl⟩ : syracuseStep 1033795 = 1550693) B1550693
theorem B1033811 : Blo 1032607 1033811 := bstep (se 1 (by rfl) ⟨775358, by rfl⟩ : syracuseStep 1033811 = 1550717) B1550717
theorem B1164883 : Blo 1032607 1164883 := bstep (se 1 (by rfl) ⟨873662, by rfl⟩ : syracuseStep 1164883 = 1747325) B1747325
theorem B1033827 : Blo 1032607 1033827 := bstep (se 1 (by rfl) ⟨775370, by rfl⟩ : syracuseStep 1033827 = 1550741) B1550741
theorem B1033843 : Blo 1032607 1033843 := bstep (se 1 (by rfl) ⟨775382, by rfl⟩ : syracuseStep 1033843 = 1550765) B1550765
theorem B1033859 : Blo 1032607 1033859 := bstep (se 1 (by rfl) ⟨775394, by rfl⟩ : syracuseStep 1033859 = 1550789) B1550789
theorem B1033875 : Blo 1032607 1033875 := bstep (se 1 (by rfl) ⟨775406, by rfl⟩ : syracuseStep 1033875 = 1550813) B1550813
theorem B1033891 : Blo 1032607 1033891 := bstep (se 1 (by rfl) ⟨775418, by rfl⟩ : syracuseStep 1033891 = 1550837) B1550837
theorem B1033907 : Blo 1032607 1033907 := bstep (se 1 (by rfl) ⟨775430, by rfl⟩ : syracuseStep 1033907 = 1550861) B1550861
theorem B1656499 : Blo 1032607 1656499 := bstep (se 1 (by rfl) ⟨1242374, by rfl⟩ : syracuseStep 1656499 = 2484749) B2484749
theorem B1033923 : Blo 1032607 1033923 := bstep (se 1 (by rfl) ⟨775442, by rfl⟩ : syracuseStep 1033923 = 1550885) B1550885
theorem B1033939 : Blo 1032607 1033939 := bstep (se 1 (by rfl) ⟨775454, by rfl⟩ : syracuseStep 1033939 = 1550909) B1550909
theorem B1033955 : Blo 1032607 1033955 := bstep (se 1 (by rfl) ⟨775466, by rfl⟩ : syracuseStep 1033955 = 1550933) B1550933
theorem B1165027 : Blo 1032607 1165027 := bstep (se 1 (by rfl) ⟨873770, by rfl⟩ : syracuseStep 1165027 = 1747541) B1747541
theorem B1033971 : Blo 1032607 1033971 := bstep (se 1 (by rfl) ⟨775478, by rfl⟩ : syracuseStep 1033971 = 1550957) B1550957
theorem B1033987 : Blo 1032607 1033987 := bstep (se 1 (by rfl) ⟨775490, by rfl⟩ : syracuseStep 1033987 = 1550981) B1550981
theorem B1034003 : Blo 1032607 1034003 := bstep (se 1 (by rfl) ⟨775502, by rfl⟩ : syracuseStep 1034003 = 1551005) B1551005
theorem B1034019 : Blo 1032607 1034019 := bstep (se 1 (by rfl) ⟨775514, by rfl⟩ : syracuseStep 1034019 = 1551029) B1551029
theorem B1034035 : Blo 1032607 1034035 := bstep (se 1 (by rfl) ⟨775526, by rfl⟩ : syracuseStep 1034035 = 1551053) B1551053
theorem B1034051 : Blo 1032607 1034051 := bstep (se 1 (by rfl) ⟨775538, by rfl⟩ : syracuseStep 1034051 = 1551077) B1551077
theorem B1034067 : Blo 1032607 1034067 := bstep (se 1 (by rfl) ⟨775550, by rfl⟩ : syracuseStep 1034067 = 1551101) B1551101
theorem B5228387 : Blo 1032607 5228387 := bstep (se 1 (by rfl) ⟨3921290, by rfl⟩ : syracuseStep 5228387 = 7842581) B7842581
theorem B1034083 : Blo 1032607 1034083 := bstep (se 1 (by rfl) ⟨775562, by rfl⟩ : syracuseStep 1034083 = 1551125) B1551125
theorem B3491693 : Blo 1032607 3491693 := bstep (se 3 (by rfl) ⟨654692, by rfl⟩ : syracuseStep 3491693 = 1309385) B1309385
theorem B1034099 : Blo 1032607 1034099 := bstep (se 1 (by rfl) ⟨775574, by rfl⟩ : syracuseStep 1034099 = 1551149) B1551149
theorem B1165171 : Blo 1032607 1165171 := bstep (se 1 (by rfl) ⟨873878, by rfl⟩ : syracuseStep 1165171 = 1747757) B1747757
theorem B1034115 : Blo 1032607 1034115 := bstep (se 1 (by rfl) ⟨775586, by rfl⟩ : syracuseStep 1034115 = 1551173) B1551173
theorem B1034131 : Blo 1032607 1034131 := bstep (se 1 (by rfl) ⟨775598, by rfl⟩ : syracuseStep 1034131 = 1551197) B1551197
theorem B1034147 : Blo 1032607 1034147 := bstep (se 1 (by rfl) ⟨775610, by rfl⟩ : syracuseStep 1034147 = 1551221) B1551221
theorem B3491747 : Blo 1032607 3491747 := bstep (se 1 (by rfl) ⟨2618810, by rfl⟩ : syracuseStep 3491747 = 5237621) B5237621
theorem B3360685 : Blo 1032607 3360685 := bstep (se 3 (by rfl) ⟨630128, by rfl⟩ : syracuseStep 3360685 = 1260257) B1260257
theorem B1034163 : Blo 1032607 1034163 := bstep (se 1 (by rfl) ⟨775622, by rfl⟩ : syracuseStep 1034163 = 1551245) B1551245
theorem B1656769 : Blo 1032607 1656769 := bstep (se 2 (by rfl) ⟨621288, by rfl⟩ : syracuseStep 1656769 = 1242577) B1242577
theorem B1034179 : Blo 1032607 1034179 := bstep (se 1 (by rfl) ⟨775634, by rfl⟩ : syracuseStep 1034179 = 1551269) B1551269
theorem B1034195 : Blo 1032607 1034195 := bstep (se 1 (by rfl) ⟨775646, by rfl⟩ : syracuseStep 1034195 = 1551293) B1551293
theorem B1034211 : Blo 1032607 1034211 := bstep (se 1 (by rfl) ⟨775658, by rfl⟩ : syracuseStep 1034211 = 1551317) B1551317
theorem B1034227 : Blo 1032607 1034227 := bstep (se 1 (by rfl) ⟨775670, by rfl⟩ : syracuseStep 1034227 = 1551341) B1551341
theorem B1034243 : Blo 1032607 1034243 := bstep (se 1 (by rfl) ⟨775682, by rfl⟩ : syracuseStep 1034243 = 1551365) B1551365
theorem B1165315 : Blo 1032607 1165315 := bstep (se 1 (by rfl) ⟨873986, by rfl⟩ : syracuseStep 1165315 = 1747973) B1747973
theorem B1034259 : Blo 1032607 1034259 := bstep (se 1 (by rfl) ⟨775694, by rfl⟩ : syracuseStep 1034259 = 1551389) B1551389
theorem B1034275 : Blo 1032607 1034275 := bstep (se 1 (by rfl) ⟨775706, by rfl⟩ : syracuseStep 1034275 = 1551413) B1551413
theorem B1034291 : Blo 1032607 1034291 := bstep (se 1 (by rfl) ⟨775718, by rfl⟩ : syracuseStep 1034291 = 1551437) B1551437
theorem B1034307 : Blo 1032607 1034307 := bstep (se 1 (by rfl) ⟨775730, by rfl⟩ : syracuseStep 1034307 = 1551461) B1551461
theorem B1034323 : Blo 1032607 1034323 := bstep (se 1 (by rfl) ⟨775742, by rfl⟩ : syracuseStep 1034323 = 1551485) B1551485
theorem B1034339 : Blo 1032607 1034339 := bstep (se 1 (by rfl) ⟨775754, by rfl⟩ : syracuseStep 1034339 = 1551509) B1551509
theorem B3786851 : Blo 1032607 3786851 := bstep (se 1 (by rfl) ⟨2840138, by rfl⟩ : syracuseStep 3786851 = 5680277) B5680277
theorem B1034355 : Blo 1032607 1034355 := bstep (se 1 (by rfl) ⟨775766, by rfl⟩ : syracuseStep 1034355 = 1551533) B1551533
theorem B1034371 : Blo 1032607 1034371 := bstep (se 1 (by rfl) ⟨775778, by rfl⟩ : syracuseStep 1034371 = 1551557) B1551557
theorem B1034387 : Blo 1032607 1034387 := bstep (se 1 (by rfl) ⟨775790, by rfl⟩ : syracuseStep 1034387 = 1551581) B1551581
theorem B1165459 : Blo 1032607 1165459 := bstep (se 1 (by rfl) ⟨874094, by rfl⟩ : syracuseStep 1165459 = 1748189) B1748189
theorem B1034403 : Blo 1032607 1034403 := bstep (se 1 (by rfl) ⟨775802, by rfl⟩ : syracuseStep 1034403 = 1551605) B1551605
theorem B3492017 : Blo 1032607 3492017 := bstep (se 2 (by rfl) ⟨1309506, by rfl⟩ : syracuseStep 3492017 = 2619013) B2619013
theorem B1034419 : Blo 1032607 1034419 := bstep (se 1 (by rfl) ⟨775814, by rfl⟩ : syracuseStep 1034419 = 1551629) B1551629
theorem B1657025 : Blo 1032607 1657025 := bstep (se 2 (by rfl) ⟨621384, by rfl⟩ : syracuseStep 1657025 = 1242769) B1242769
theorem B1034435 : Blo 1032607 1034435 := bstep (se 1 (by rfl) ⟨775826, by rfl⟩ : syracuseStep 1034435 = 1551653) B1551653
theorem B1034451 : Blo 1032607 1034451 := bstep (se 1 (by rfl) ⟨775838, by rfl⟩ : syracuseStep 1034451 = 1551677) B1551677
theorem B1034467 : Blo 1032607 1034467 := bstep (se 1 (by rfl) ⟨775850, by rfl⟩ : syracuseStep 1034467 = 1551701) B1551701
theorem B3786979 : Blo 1032607 3786979 := bstep (se 1 (by rfl) ⟨2840234, by rfl⟩ : syracuseStep 3786979 = 5680469) B5680469
theorem B1034483 : Blo 1032607 1034483 := bstep (se 1 (by rfl) ⟨775862, by rfl⟩ : syracuseStep 1034483 = 1551725) B1551725
theorem B1034499 : Blo 1032607 1034499 := bstep (se 1 (by rfl) ⟨775874, by rfl⟩ : syracuseStep 1034499 = 1551749) B1551749
theorem B1034515 : Blo 1032607 1034515 := bstep (se 1 (by rfl) ⟨775886, by rfl⟩ : syracuseStep 1034515 = 1551773) B1551773
theorem B1034531 : Blo 1032607 1034531 := bstep (se 1 (by rfl) ⟨775898, by rfl⟩ : syracuseStep 1034531 = 1551797) B1551797
theorem B1165603 : Blo 1032607 1165603 := bstep (se 1 (by rfl) ⟨874202, by rfl⟩ : syracuseStep 1165603 = 1748405) B1748405
theorem B1034547 : Blo 1032607 1034547 := bstep (se 1 (by rfl) ⟨775910, by rfl⟩ : syracuseStep 1034547 = 1551821) B1551821
theorem B1034563 : Blo 1032607 1034563 := bstep (se 1 (by rfl) ⟨775922, by rfl⟩ : syracuseStep 1034563 = 1551845) B1551845
theorem B1034579 : Blo 1032607 1034579 := bstep (se 1 (by rfl) ⟨775934, by rfl⟩ : syracuseStep 1034579 = 1551869) B1551869
theorem B1034595 : Blo 1032607 1034595 := bstep (se 1 (by rfl) ⟨775946, by rfl⟩ : syracuseStep 1034595 = 1551893) B1551893
theorem B1034611 : Blo 1032607 1034611 := bstep (se 1 (by rfl) ⟨775958, by rfl⟩ : syracuseStep 1034611 = 1551917) B1551917
theorem B1034627 : Blo 1032607 1034627 := bstep (se 1 (by rfl) ⟨775970, by rfl⟩ : syracuseStep 1034627 = 1551941) B1551941
theorem B1034643 : Blo 1032607 1034643 := bstep (se 1 (by rfl) ⟨775982, by rfl⟩ : syracuseStep 1034643 = 1551965) B1551965
theorem B1034659 : Blo 1032607 1034659 := bstep (se 1 (by rfl) ⟨775994, by rfl⟩ : syracuseStep 1034659 = 1551989) B1551989
theorem B1034675 : Blo 1032607 1034675 := bstep (se 1 (by rfl) ⟨776006, by rfl⟩ : syracuseStep 1034675 = 1552013) B1552013
theorem B1165747 : Blo 1032607 1165747 := bstep (se 1 (by rfl) ⟨874310, by rfl⟩ : syracuseStep 1165747 = 1748621) B1748621
theorem B1034691 : Blo 1032607 1034691 := bstep (se 1 (by rfl) ⟨776018, by rfl⟩ : syracuseStep 1034691 = 1552037) B1552037
theorem B1034707 : Blo 1032607 1034707 := bstep (se 1 (by rfl) ⟨776030, by rfl⟩ : syracuseStep 1034707 = 1552061) B1552061
theorem B4966883 : Blo 1032607 4966883 := bstep (se 1 (by rfl) ⟨3725162, by rfl⟩ : syracuseStep 4966883 = 7450325) B7450325
theorem B1034723 : Blo 1032607 1034723 := bstep (se 1 (by rfl) ⟨776042, by rfl⟩ : syracuseStep 1034723 = 1552085) B1552085
theorem B1034739 : Blo 1032607 1034739 := bstep (se 1 (by rfl) ⟨776054, by rfl⟩ : syracuseStep 1034739 = 1552109) B1552109
theorem B1034755 : Blo 1032607 1034755 := bstep (se 1 (by rfl) ⟨776066, by rfl⟩ : syracuseStep 1034755 = 1552133) B1552133
theorem B1034771 : Blo 1032607 1034771 := bstep (se 1 (by rfl) ⟨776078, by rfl⟩ : syracuseStep 1034771 = 1552157) B1552157
theorem B1034787 : Blo 1032607 1034787 := bstep (se 1 (by rfl) ⟨776090, by rfl⟩ : syracuseStep 1034787 = 1552181) B1552181
theorem B1034803 : Blo 1032607 1034803 := bstep (se 1 (by rfl) ⟨776102, by rfl⟩ : syracuseStep 1034803 = 1552205) B1552205
theorem B1034819 : Blo 1032607 1034819 := bstep (se 1 (by rfl) ⟨776114, by rfl⟩ : syracuseStep 1034819 = 1552229) B1552229
theorem B1165891 : Blo 1032607 1165891 := bstep (se 1 (by rfl) ⟨874418, by rfl⟩ : syracuseStep 1165891 = 1748837) B1748837
theorem B1034835 : Blo 1032607 1034835 := bstep (se 1 (by rfl) ⟨776126, by rfl⟩ : syracuseStep 1034835 = 1552253) B1552253
theorem B1034851 : Blo 1032607 1034851 := bstep (se 1 (by rfl) ⟨776138, by rfl⟩ : syracuseStep 1034851 = 1552277) B1552277
theorem B1034867 : Blo 1032607 1034867 := bstep (se 1 (by rfl) ⟨776150, by rfl⟩ : syracuseStep 1034867 = 1552301) B1552301
theorem B1034883 : Blo 1032607 1034883 := bstep (se 1 (by rfl) ⟨776162, by rfl⟩ : syracuseStep 1034883 = 1552325) B1552325
theorem B5229197 : Blo 1032607 5229197 := bstep (se 3 (by rfl) ⟨980474, by rfl⟩ : syracuseStep 5229197 = 1960949) B1960949
theorem B3361421 : Blo 1032607 3361421 := bstep (se 3 (by rfl) ⟨630266, by rfl⟩ : syracuseStep 3361421 = 1260533) B1260533
theorem B1034899 : Blo 1032607 1034899 := bstep (se 1 (by rfl) ⟨776174, by rfl⟩ : syracuseStep 1034899 = 1552349) B1552349
theorem B1034915 : Blo 1032607 1034915 := bstep (se 1 (by rfl) ⟨776186, by rfl⟩ : syracuseStep 1034915 = 1552373) B1552373
theorem B1034931 : Blo 1032607 1034931 := bstep (se 1 (by rfl) ⟨776198, by rfl⟩ : syracuseStep 1034931 = 1552397) B1552397
theorem B1034947 : Blo 1032607 1034947 := bstep (se 1 (by rfl) ⟨776210, by rfl⟩ : syracuseStep 1034947 = 1552421) B1552421
theorem B3492557 : Blo 1032607 3492557 := bstep (se 3 (by rfl) ⟨654854, by rfl⟩ : syracuseStep 3492557 = 1309709) B1309709
theorem B1034963 : Blo 1032607 1034963 := bstep (se 1 (by rfl) ⟨776222, by rfl⟩ : syracuseStep 1034963 = 1552445) B1552445
theorem B1166035 : Blo 1032607 1166035 := bstep (se 1 (by rfl) ⟨874526, by rfl⟩ : syracuseStep 1166035 = 1749053) B1749053
theorem B1034979 : Blo 1032607 1034979 := bstep (se 1 (by rfl) ⟨776234, by rfl⟩ : syracuseStep 1034979 = 1552469) B1552469
theorem B1034995 : Blo 1032607 1034995 := bstep (se 1 (by rfl) ⟨776246, by rfl⟩ : syracuseStep 1034995 = 1552493) B1552493
theorem B3492611 : Blo 1032607 3492611 := bstep (se 1 (by rfl) ⟨2619458, by rfl⟩ : syracuseStep 3492611 = 5238917) B5238917
theorem B1035011 : Blo 1032607 1035011 := bstep (se 1 (by rfl) ⟨776258, by rfl⟩ : syracuseStep 1035011 = 1552517) B1552517
theorem B1035027 : Blo 1032607 1035027 := bstep (se 1 (by rfl) ⟨776270, by rfl⟩ : syracuseStep 1035027 = 1552541) B1552541
theorem B1035043 : Blo 1032607 1035043 := bstep (se 1 (by rfl) ⟨776282, by rfl⟩ : syracuseStep 1035043 = 1552565) B1552565
theorem B1035059 : Blo 1032607 1035059 := bstep (se 1 (by rfl) ⟨776294, by rfl⟩ : syracuseStep 1035059 = 1552589) B1552589
theorem B1035075 : Blo 1032607 1035075 := bstep (se 1 (by rfl) ⟨776306, by rfl⟩ : syracuseStep 1035075 = 1552613) B1552613
theorem B1035091 : Blo 1032607 1035091 := bstep (se 1 (by rfl) ⟨776318, by rfl⟩ : syracuseStep 1035091 = 1552637) B1552637
theorem B1035107 : Blo 1032607 1035107 := bstep (se 1 (by rfl) ⟨776330, by rfl⟩ : syracuseStep 1035107 = 1552661) B1552661
theorem B1166179 : Blo 1032607 1166179 := bstep (se 1 (by rfl) ⟨874634, by rfl⟩ : syracuseStep 1166179 = 1749269) B1749269
theorem B1035123 : Blo 1032607 1035123 := bstep (se 1 (by rfl) ⟨776342, by rfl⟩ : syracuseStep 1035123 = 1552685) B1552685
theorem B1657729 : Blo 1032607 1657729 := bstep (se 2 (by rfl) ⟨621648, by rfl⟩ : syracuseStep 1657729 = 1243297) B1243297
theorem B1035139 : Blo 1032607 1035139 := bstep (se 1 (by rfl) ⟨776354, by rfl⟩ : syracuseStep 1035139 = 1552709) B1552709
theorem B1035155 : Blo 1032607 1035155 := bstep (se 1 (by rfl) ⟨776366, by rfl⟩ : syracuseStep 1035155 = 1552733) B1552733
theorem B1035171 : Blo 1032607 1035171 := bstep (se 1 (by rfl) ⟨776378, by rfl⟩ : syracuseStep 1035171 = 1552757) B1552757
theorem B4967345 : Blo 1032607 4967345 := bstep (se 2 (by rfl) ⟨1862754, by rfl⟩ : syracuseStep 4967345 = 3725509) B3725509
theorem B1035187 : Blo 1032607 1035187 := bstep (se 1 (by rfl) ⟨776390, by rfl⟩ : syracuseStep 1035187 = 1552781) B1552781
theorem B1035203 : Blo 1032607 1035203 := bstep (se 1 (by rfl) ⟨776402, by rfl⟩ : syracuseStep 1035203 = 1552805) B1552805
theorem B1035219 : Blo 1032607 1035219 := bstep (se 1 (by rfl) ⟨776414, by rfl⟩ : syracuseStep 1035219 = 1552829) B1552829
theorem B1035235 : Blo 1032607 1035235 := bstep (se 1 (by rfl) ⟨776426, by rfl⟩ : syracuseStep 1035235 = 1552853) B1552853
theorem B1035251 : Blo 1032607 1035251 := bstep (se 1 (by rfl) ⟨776438, by rfl⟩ : syracuseStep 1035251 = 1552877) B1552877
theorem B1035267 : Blo 1032607 1035267 := bstep (se 1 (by rfl) ⟨776450, by rfl⟩ : syracuseStep 1035267 = 1552901) B1552901
theorem B3492881 : Blo 1032607 3492881 := bstep (se 2 (by rfl) ⟨1309830, by rfl⟩ : syracuseStep 3492881 = 2619661) B2619661
theorem B1035283 : Blo 1032607 1035283 := bstep (se 1 (by rfl) ⟨776462, by rfl⟩ : syracuseStep 1035283 = 1552925) B1552925
theorem B1035299 : Blo 1032607 1035299 := bstep (se 1 (by rfl) ⟨776474, by rfl⟩ : syracuseStep 1035299 = 1552949) B1552949
theorem B1035315 : Blo 1032607 1035315 := bstep (se 1 (by rfl) ⟨776486, by rfl⟩ : syracuseStep 1035315 = 1552973) B1552973
theorem B1035331 : Blo 1032607 1035331 := bstep (se 1 (by rfl) ⟨776498, by rfl⟩ : syracuseStep 1035331 = 1552997) B1552997
theorem B1035347 : Blo 1032607 1035347 := bstep (se 1 (by rfl) ⟨776510, by rfl⟩ : syracuseStep 1035347 = 1553021) B1553021
theorem B1035363 : Blo 1032607 1035363 := bstep (se 1 (by rfl) ⟨776522, by rfl⟩ : syracuseStep 1035363 = 1553045) B1553045
theorem B1035379 : Blo 1032607 1035379 := bstep (se 1 (by rfl) ⟨776534, by rfl⟩ : syracuseStep 1035379 = 1553069) B1553069
theorem B1035395 : Blo 1032607 1035395 := bstep (se 1 (by rfl) ⟨776546, by rfl⟩ : syracuseStep 1035395 = 1553093) B1553093
theorem B1035411 : Blo 1032607 1035411 := bstep (se 1 (by rfl) ⟨776558, by rfl⟩ : syracuseStep 1035411 = 1553117) B1553117
theorem B1035427 : Blo 1032607 1035427 := bstep (se 1 (by rfl) ⟨776570, by rfl⟩ : syracuseStep 1035427 = 1553141) B1553141
theorem B1035443 : Blo 1032607 1035443 := bstep (se 1 (by rfl) ⟨776582, by rfl⟩ : syracuseStep 1035443 = 1553165) B1553165
theorem B1035459 : Blo 1032607 1035459 := bstep (se 1 (by rfl) ⟨776594, by rfl⟩ : syracuseStep 1035459 = 1553189) B1553189
theorem B1035475 : Blo 1032607 1035475 := bstep (se 1 (by rfl) ⟨776606, by rfl⟩ : syracuseStep 1035475 = 1553213) B1553213
theorem B1035491 : Blo 1032607 1035491 := bstep (se 1 (by rfl) ⟨776618, by rfl⟩ : syracuseStep 1035491 = 1553237) B1553237
theorem B1035507 : Blo 1032607 1035507 := bstep (se 1 (by rfl) ⟨776630, by rfl⟩ : syracuseStep 1035507 = 1553261) B1553261
theorem B1035523 : Blo 1032607 1035523 := bstep (se 1 (by rfl) ⟨776642, by rfl⟩ : syracuseStep 1035523 = 1553285) B1553285
theorem B1035539 : Blo 1032607 1035539 := bstep (se 1 (by rfl) ⟨776654, by rfl⟩ : syracuseStep 1035539 = 1553309) B1553309
theorem B1035555 : Blo 1032607 1035555 := bstep (se 1 (by rfl) ⟨776666, by rfl⟩ : syracuseStep 1035555 = 1553333) B1553333
theorem B1035571 : Blo 1032607 1035571 := bstep (se 1 (by rfl) ⟨776678, by rfl⟩ : syracuseStep 1035571 = 1553357) B1553357
theorem B1035587 : Blo 1032607 1035587 := bstep (se 1 (by rfl) ⟨776690, by rfl⟩ : syracuseStep 1035587 = 1553381) B1553381
theorem B1035603 : Blo 1032607 1035603 := bstep (se 1 (by rfl) ⟨776702, by rfl⟩ : syracuseStep 1035603 = 1553405) B1553405
theorem B1035619 : Blo 1032607 1035619 := bstep (se 1 (by rfl) ⟨776714, by rfl⟩ : syracuseStep 1035619 = 1553429) B1553429
theorem B1035635 : Blo 1032607 1035635 := bstep (se 1 (by rfl) ⟨776726, by rfl⟩ : syracuseStep 1035635 = 1553453) B1553453
theorem B1035651 : Blo 1032607 1035651 := bstep (se 1 (by rfl) ⟨776738, by rfl⟩ : syracuseStep 1035651 = 1553477) B1553477
theorem B1035667 : Blo 1032607 1035667 := bstep (se 1 (by rfl) ⟨776750, by rfl⟩ : syracuseStep 1035667 = 1553501) B1553501
theorem B1035683 : Blo 1032607 1035683 := bstep (se 1 (by rfl) ⟨776762, by rfl⟩ : syracuseStep 1035683 = 1553525) B1553525
theorem B1035699 : Blo 1032607 1035699 := bstep (se 1 (by rfl) ⟨776774, by rfl⟩ : syracuseStep 1035699 = 1553549) B1553549
theorem B1035715 : Blo 1032607 1035715 := bstep (se 1 (by rfl) ⟨776786, by rfl⟩ : syracuseStep 1035715 = 1553573) B1553573
theorem B1035731 : Blo 1032607 1035731 := bstep (se 1 (by rfl) ⟨776798, by rfl⟩ : syracuseStep 1035731 = 1553597) B1553597
theorem B1035747 : Blo 1032607 1035747 := bstep (se 1 (by rfl) ⟨776810, by rfl⟩ : syracuseStep 1035747 = 1553621) B1553621
theorem B1035763 : Blo 1032607 1035763 := bstep (se 1 (by rfl) ⟨776822, by rfl⟩ : syracuseStep 1035763 = 1553645) B1553645
theorem B1035779 : Blo 1032607 1035779 := bstep (se 1 (by rfl) ⟨776834, by rfl⟩ : syracuseStep 1035779 = 1553669) B1553669
theorem B1035795 : Blo 1032607 1035795 := bstep (se 1 (by rfl) ⟨776846, by rfl⟩ : syracuseStep 1035795 = 1553693) B1553693
theorem B1035811 : Blo 1032607 1035811 := bstep (se 1 (by rfl) ⟨776858, by rfl⟩ : syracuseStep 1035811 = 1553717) B1553717
theorem B3493421 : Blo 1032607 3493421 := bstep (se 3 (by rfl) ⟨655016, by rfl⟩ : syracuseStep 3493421 = 1310033) B1310033
theorem B1035827 : Blo 1032607 1035827 := bstep (se 1 (by rfl) ⟨776870, by rfl⟩ : syracuseStep 1035827 = 1553741) B1553741
theorem B1035843 : Blo 1032607 1035843 := bstep (se 1 (by rfl) ⟨776882, by rfl⟩ : syracuseStep 1035843 = 1553765) B1553765
theorem B1035859 : Blo 1032607 1035859 := bstep (se 1 (by rfl) ⟨776894, by rfl⟩ : syracuseStep 1035859 = 1553789) B1553789
theorem B3493475 : Blo 1032607 3493475 := bstep (se 1 (by rfl) ⟨2620106, by rfl⟩ : syracuseStep 3493475 = 5240213) B5240213
theorem B1035875 : Blo 1032607 1035875 := bstep (se 1 (by rfl) ⟨776906, by rfl⟩ : syracuseStep 1035875 = 1553813) B1553813
theorem B1035891 : Blo 1032607 1035891 := bstep (se 1 (by rfl) ⟨776918, by rfl⟩ : syracuseStep 1035891 = 1553837) B1553837
theorem B1035907 : Blo 1032607 1035907 := bstep (se 1 (by rfl) ⟨776930, by rfl⟩ : syracuseStep 1035907 = 1553861) B1553861
theorem B5885581 : Blo 1032607 5885581 := bstep (se 3 (by rfl) ⟨1103546, by rfl⟩ : syracuseStep 5885581 = 2207093) B2207093
theorem B11062925 : Blo 1032607 11062925 := bstep (se 3 (by rfl) ⟨2074298, by rfl⟩ : syracuseStep 11062925 = 4148597) B4148597
theorem B1035923 : Blo 1032607 1035923 := bstep (se 1 (by rfl) ⟨776942, by rfl⟩ : syracuseStep 1035923 = 1553885) B1553885
theorem B4411043 : Blo 1032607 4411043 := bstep (se 1 (by rfl) ⟨3308282, by rfl⟩ : syracuseStep 4411043 = 6616565) B6616565
theorem B1035939 : Blo 1032607 1035939 := bstep (se 1 (by rfl) ⟨776954, by rfl⟩ : syracuseStep 1035939 = 1553909) B1553909
theorem B1035955 : Blo 1032607 1035955 := bstep (se 1 (by rfl) ⟨776966, by rfl⟩ : syracuseStep 1035955 = 1553933) B1553933
theorem B1035971 : Blo 1032607 1035971 := bstep (se 1 (by rfl) ⟨776978, by rfl⟩ : syracuseStep 1035971 = 1553957) B1553957
theorem B1035987 : Blo 1032607 1035987 := bstep (se 1 (by rfl) ⟨776990, by rfl⟩ : syracuseStep 1035987 = 1553981) B1553981
theorem B1036003 : Blo 1032607 1036003 := bstep (se 1 (by rfl) ⟨777002, by rfl⟩ : syracuseStep 1036003 = 1554005) B1554005
theorem B1036019 : Blo 1032607 1036019 := bstep (se 1 (by rfl) ⟨777014, by rfl⟩ : syracuseStep 1036019 = 1554029) B1554029
theorem B1658627 : Blo 1032607 1658627 := bstep (se 1 (by rfl) ⟨1243970, by rfl⟩ : syracuseStep 1658627 = 2487941) B2487941
theorem B1036035 : Blo 1032607 1036035 := bstep (se 1 (by rfl) ⟨777026, by rfl⟩ : syracuseStep 1036035 = 1554053) B1554053
theorem B1036051 : Blo 1032607 1036051 := bstep (se 1 (by rfl) ⟨777038, by rfl⟩ : syracuseStep 1036051 = 1554077) B1554077
theorem B1036067 : Blo 1032607 1036067 := bstep (se 1 (by rfl) ⟨777050, by rfl⟩ : syracuseStep 1036067 = 1554101) B1554101
theorem B1036083 : Blo 1032607 1036083 := bstep (se 1 (by rfl) ⟨777062, by rfl⟩ : syracuseStep 1036083 = 1554125) B1554125
theorem B1036099 : Blo 1032607 1036099 := bstep (se 1 (by rfl) ⟨777074, by rfl⟩ : syracuseStep 1036099 = 1554149) B1554149
theorem B1036115 : Blo 1032607 1036115 := bstep (se 1 (by rfl) ⟨777086, by rfl⟩ : syracuseStep 1036115 = 1554173) B1554173
theorem B1036131 : Blo 1032607 1036131 := bstep (se 1 (by rfl) ⟨777098, by rfl⟩ : syracuseStep 1036131 = 1554197) B1554197
theorem B3493745 : Blo 1032607 3493745 := bstep (se 2 (by rfl) ⟨1310154, by rfl⟩ : syracuseStep 3493745 = 2620309) B2620309
theorem B1036147 : Blo 1032607 1036147 := bstep (se 1 (by rfl) ⟨777110, by rfl⟩ : syracuseStep 1036147 = 1554221) B1554221
theorem B1036163 : Blo 1032607 1036163 := bstep (se 1 (by rfl) ⟨777122, by rfl⟩ : syracuseStep 1036163 = 1554245) B1554245
theorem B1036179 : Blo 1032607 1036179 := bstep (se 1 (by rfl) ⟨777134, by rfl⟩ : syracuseStep 1036179 = 1554269) B1554269
theorem B1036195 : Blo 1032607 1036195 := bstep (se 1 (by rfl) ⟨777146, by rfl⟩ : syracuseStep 1036195 = 1554293) B1554293
theorem B1036211 : Blo 1032607 1036211 := bstep (se 1 (by rfl) ⟨777158, by rfl⟩ : syracuseStep 1036211 = 1554317) B1554317
theorem B1658819 : Blo 1032607 1658819 := bstep (se 1 (by rfl) ⟨1244114, by rfl⟩ : syracuseStep 1658819 = 2488229) B2488229
theorem B1036227 : Blo 1032607 1036227 := bstep (se 1 (by rfl) ⟨777170, by rfl⟩ : syracuseStep 1036227 = 1554341) B1554341
theorem B1036243 : Blo 1032607 1036243 := bstep (se 1 (by rfl) ⟨777182, by rfl⟩ : syracuseStep 1036243 = 1554365) B1554365
theorem B1036259 : Blo 1032607 1036259 := bstep (se 1 (by rfl) ⟨777194, by rfl⟩ : syracuseStep 1036259 = 1554389) B1554389
theorem B1036275 : Blo 1032607 1036275 := bstep (se 1 (by rfl) ⟨777206, by rfl⟩ : syracuseStep 1036275 = 1554413) B1554413
theorem B1036291 : Blo 1032607 1036291 := bstep (se 1 (by rfl) ⟨777218, by rfl⟩ : syracuseStep 1036291 = 1554437) B1554437
theorem B1036307 : Blo 1032607 1036307 := bstep (se 1 (by rfl) ⟨777230, by rfl⟩ : syracuseStep 1036307 = 1554461) B1554461
theorem B1036323 : Blo 1032607 1036323 := bstep (se 1 (by rfl) ⟨777242, by rfl⟩ : syracuseStep 1036323 = 1554485) B1554485
theorem B1036339 : Blo 1032607 1036339 := bstep (se 1 (by rfl) ⟨777254, by rfl⟩ : syracuseStep 1036339 = 1554509) B1554509
theorem B1036355 : Blo 1032607 1036355 := bstep (se 1 (by rfl) ⟨777266, by rfl⟩ : syracuseStep 1036355 = 1554533) B1554533
theorem B1036371 : Blo 1032607 1036371 := bstep (se 1 (by rfl) ⟨777278, by rfl⟩ : syracuseStep 1036371 = 1554557) B1554557
theorem B1036387 : Blo 1032607 1036387 := bstep (se 1 (by rfl) ⟨777290, by rfl⟩ : syracuseStep 1036387 = 1554581) B1554581
theorem B1036403 : Blo 1032607 1036403 := bstep (se 1 (by rfl) ⟨777302, by rfl⟩ : syracuseStep 1036403 = 1554605) B1554605
theorem B1036419 : Blo 1032607 1036419 := bstep (se 1 (by rfl) ⟨777314, by rfl⟩ : syracuseStep 1036419 = 1554629) B1554629
theorem B1036435 : Blo 1032607 1036435 := bstep (se 1 (by rfl) ⟨777326, by rfl⟩ : syracuseStep 1036435 = 1554653) B1554653
theorem B1036451 : Blo 1032607 1036451 := bstep (se 1 (by rfl) ⟨777338, by rfl⟩ : syracuseStep 1036451 = 1554677) B1554677
theorem B1036467 : Blo 1032607 1036467 := bstep (se 1 (by rfl) ⟨777350, by rfl⟩ : syracuseStep 1036467 = 1554701) B1554701
theorem B1036483 : Blo 1032607 1036483 := bstep (se 1 (by rfl) ⟨777362, by rfl⟩ : syracuseStep 1036483 = 1554725) B1554725
theorem B1036499 : Blo 1032607 1036499 := bstep (se 1 (by rfl) ⟨777374, by rfl⟩ : syracuseStep 1036499 = 1554749) B1554749
theorem B1036515 : Blo 1032607 1036515 := bstep (se 1 (by rfl) ⟨777386, by rfl⟩ : syracuseStep 1036515 = 1554773) B1554773
theorem B1036531 : Blo 1032607 1036531 := bstep (se 1 (by rfl) ⟨777398, by rfl⟩ : syracuseStep 1036531 = 1554797) B1554797
theorem B1036547 : Blo 1032607 1036547 := bstep (se 1 (by rfl) ⟨777410, by rfl⟩ : syracuseStep 1036547 = 1554821) B1554821
theorem B7852301 : Blo 1032607 7852301 := bstep (se 3 (by rfl) ⟨1472306, by rfl⟩ : syracuseStep 7852301 = 2944613) B2944613
theorem B1036563 : Blo 1032607 1036563 := bstep (se 1 (by rfl) ⟨777422, by rfl⟩ : syracuseStep 1036563 = 1554845) B1554845
theorem B1036579 : Blo 1032607 1036579 := bstep (se 1 (by rfl) ⟨777434, by rfl⟩ : syracuseStep 1036579 = 1554869) B1554869
theorem B1036595 : Blo 1032607 1036595 := bstep (se 1 (by rfl) ⟨777446, by rfl⟩ : syracuseStep 1036595 = 1554893) B1554893
theorem B3494285 : Blo 1032607 3494285 := bstep (se 3 (by rfl) ⟨655178, by rfl⟩ : syracuseStep 3494285 = 1310357) B1310357
theorem B3494339 : Blo 1032607 3494339 := bstep (se 1 (by rfl) ⟨2620754, by rfl⟩ : syracuseStep 3494339 = 5241509) B5241509
theorem B6640325 : Blo 1032607 6640325 := bstep (se 4 (by rfl) ⟨622530, by rfl⟩ : syracuseStep 6640325 = 1245061) B1245061
theorem B3494609 : Blo 1032607 3494609 := bstep (se 2 (by rfl) ⟨1310478, by rfl⟩ : syracuseStep 3494609 = 2620957) B2620957
theorem B11785013 : Blo 1032607 11785013 := bstep (se 5 (by rfl) ⟨552422, by rfl⟩ : syracuseStep 11785013 = 1104845) B1104845
theorem B1659793 : Blo 1032607 1659793 := bstep (se 2 (by rfl) ⟨622422, by rfl⟩ : syracuseStep 1659793 = 1244845) B1244845
theorem B1397683 : Blo 1032607 1397683 := bstep (se 1 (by rfl) ⟨1048262, by rfl⟩ : syracuseStep 1397683 = 2096525) B2096525
theorem B3495149 : Blo 1032607 3495149 := bstep (se 3 (by rfl) ⟨655340, by rfl⟩ : syracuseStep 3495149 = 1310681) B1310681
theorem B3495203 : Blo 1032607 3495203 := bstep (se 1 (by rfl) ⟨2621402, by rfl⟩ : syracuseStep 3495203 = 5242805) B5242805
theorem B1660241 : Blo 1032607 1660241 := bstep (se 2 (by rfl) ⟨622590, by rfl⟩ : syracuseStep 1660241 = 1245181) B1245181
theorem B13424069 : Blo 1032607 13424069 := bstep (se 4 (by rfl) ⟨1258506, by rfl⟩ : syracuseStep 13424069 = 2517013) B2517013
theorem B5232113 : Blo 1032607 5232113 := bstep (se 2 (by rfl) ⟨1962042, by rfl⟩ : syracuseStep 5232113 = 3924085) B3924085
theorem B25187861 : Blo 1032607 25187861 := bstep (se 6 (by rfl) ⟨590340, by rfl⟩ : syracuseStep 25187861 = 1180681) B1180681
theorem B3921443 : Blo 1032607 3921443 := bstep (se 1 (by rfl) ⟨2941082, by rfl⟩ : syracuseStep 3921443 = 5882165) B5882165
theorem B3495473 : Blo 1032607 3495473 := bstep (se 2 (by rfl) ⟨1310802, by rfl⟩ : syracuseStep 3495473 = 2621605) B2621605
theorem B5887565 : Blo 1032607 5887565 := bstep (se 3 (by rfl) ⟨1103918, by rfl⟩ : syracuseStep 5887565 = 2207837) B2207837
theorem B17684081 : Blo 1032607 17684081 := bstep (se 2 (by rfl) ⟨6631530, by rfl⟩ : syracuseStep 17684081 = 13263061) B13263061
theorem B2021059 : Blo 1032607 2021059 := bstep (se 1 (by rfl) ⟨1515794, by rfl⟩ : syracuseStep 2021059 = 3031589) B3031589
theorem B4544305 : Blo 1032607 4544305 := bstep (se 2 (by rfl) ⟨1704114, by rfl⟩ : syracuseStep 4544305 = 3408229) B3408229
theorem B7460677 : Blo 1032607 7460677 := bstep (se 4 (by rfl) ⟨699438, by rfl⟩ : syracuseStep 7460677 = 1398877) B1398877
theorem B1398721 : Blo 1032607 1398721 := bstep (se 2 (by rfl) ⟨524520, by rfl⟩ : syracuseStep 1398721 = 1049041) B1049041
theorem B4970573 : Blo 1032607 4970573 := bstep (se 3 (by rfl) ⟨931982, by rfl⟩ : syracuseStep 4970573 = 1863965) B1863965
theorem B3496013 : Blo 1032607 3496013 := bstep (se 3 (by rfl) ⟨655502, by rfl⟩ : syracuseStep 3496013 = 1311005) B1311005
theorem B1398883 : Blo 1032607 1398883 := bstep (se 1 (by rfl) ⟨1049162, by rfl⟩ : syracuseStep 1398883 = 2098325) B2098325
theorem B1103987 : Blo 1032607 1103987 := bstep (se 1 (by rfl) ⟨827990, by rfl⟩ : syracuseStep 1103987 = 1655981) B1655981
theorem B3496067 : Blo 1032607 3496067 := bstep (se 1 (by rfl) ⟨2622050, by rfl⟩ : syracuseStep 3496067 = 5244101) B5244101
theorem B12572813 : Blo 1032607 12572813 := bstep (se 3 (by rfl) ⟨2357402, by rfl⟩ : syracuseStep 12572813 = 4714805) B4714805
theorem B3725453 : Blo 1032607 3725453 := bstep (se 3 (by rfl) ⟨698522, by rfl⟩ : syracuseStep 3725453 = 1397045) B1397045
theorem B3496337 : Blo 1032607 3496337 := bstep (se 2 (by rfl) ⟨1311126, by rfl⟩ : syracuseStep 3496337 = 2622253) B2622253
theorem B5888497 : Blo 1032607 5888497 := bstep (se 2 (by rfl) ⟨2208186, by rfl⟩ : syracuseStep 5888497 = 4416373) B4416373
theorem B3922445 : Blo 1032607 3922445 := bstep (se 3 (by rfl) ⟨735458, by rfl⟩ : syracuseStep 3922445 = 1470917) B1470917
theorem B45439541 : Blo 1032607 45439541 := bstep (se 5 (by rfl) ⟨2129978, by rfl⟩ : syracuseStep 45439541 = 4259957) B4259957
theorem B12114613 : Blo 1032607 12114613 := bstep (se 5 (by rfl) ⟨567872, by rfl⟩ : syracuseStep 12114613 = 1135745) B1135745
theorem B5233571 : Blo 1032607 5233571 := bstep (se 1 (by rfl) ⟨3925178, by rfl⟩ : syracuseStep 5233571 = 7850357) B7850357
theorem B3496877 : Blo 1032607 3496877 := bstep (se 3 (by rfl) ⟨655664, by rfl⟩ : syracuseStep 3496877 = 1311329) B1311329
theorem B3496931 : Blo 1032607 3496931 := bstep (se 1 (by rfl) ⟨2622698, by rfl⟩ : syracuseStep 3496931 = 5245397) B5245397
theorem B1104931 : Blo 1032607 1104931 := bstep (se 1 (by rfl) ⟨828698, by rfl⟩ : syracuseStep 1104931 = 1657397) B1657397
theorem B7855217 : Blo 1032607 7855217 := bstep (se 2 (by rfl) ⟨2945706, by rfl⟩ : syracuseStep 7855217 = 5891413) B5891413
theorem B1596611 : Blo 1032607 1596611 := bstep (se 1 (by rfl) ⟨1197458, by rfl⟩ : syracuseStep 1596611 = 2394917) B2394917
theorem B3497201 : Blo 1032607 3497201 := bstep (se 2 (by rfl) ⟨1311450, by rfl⟩ : syracuseStep 3497201 = 2622901) B2622901
theorem B4414733 : Blo 1032607 4414733 := bstep (se 3 (by rfl) ⟨827762, by rfl⟩ : syracuseStep 4414733 = 1655525) B1655525
theorem B4414769 : Blo 1032607 4414769 := bstep (se 2 (by rfl) ⟨1655538, by rfl⟩ : syracuseStep 4414769 = 3311077) B3311077
theorem B1989937 : Blo 1032607 1989937 := bstep (se 2 (by rfl) ⟨746226, by rfl⟩ : syracuseStep 1989937 = 1492453) B1492453
theorem B5234381 : Blo 1032607 5234381 := bstep (se 3 (by rfl) ⟨981446, by rfl⟩ : syracuseStep 5234381 = 1962893) B1962893
theorem B3497741 : Blo 1032607 3497741 := bstep (se 3 (by rfl) ⟨655826, by rfl⟩ : syracuseStep 3497741 = 1311653) B1311653
theorem B3497795 : Blo 1032607 3497795 := bstep (se 1 (by rfl) ⟨2623346, by rfl⟩ : syracuseStep 3497795 = 5246693) B5246693
theorem B3825521 : Blo 1032607 3825521 := bstep (se 2 (by rfl) ⟨1434570, by rfl⟩ : syracuseStep 3825521 = 2869141) B2869141
theorem B15327089 : Blo 1032607 15327089 := bstep (se 2 (by rfl) ⟨5747658, by rfl⟩ : syracuseStep 15327089 = 11495317) B11495317
theorem B11198321 : Blo 1032607 11198321 := bstep (se 2 (by rfl) ⟨4199370, by rfl⟩ : syracuseStep 11198321 = 8398741) B8398741
theorem B5889955 : Blo 1032607 5889955 := bstep (se 1 (by rfl) ⟨4417466, by rfl⟩ : syracuseStep 5889955 = 8834933) B8834933
theorem B2940877 : Blo 1032607 2940877 := bstep (se 3 (by rfl) ⟨551414, by rfl⟩ : syracuseStep 2940877 = 1102829) B1102829
theorem B1400851 : Blo 1032607 1400851 := bstep (se 1 (by rfl) ⟨1050638, by rfl⟩ : syracuseStep 1400851 = 2101277) B2101277
theorem B2482211 : Blo 1032607 2482211 := bstep (se 1 (by rfl) ⟨1861658, by rfl⟩ : syracuseStep 2482211 = 3723317) B3723317
theorem B11952197 : Blo 1032607 11952197 := bstep (se 4 (by rfl) ⟨1120518, by rfl⟩ : syracuseStep 11952197 = 2241037) B2241037
theorem B3498065 : Blo 1032607 3498065 := bstep (se 2 (by rfl) ⟨1311774, by rfl⟩ : syracuseStep 3498065 = 2623549) B2623549
theorem B1400915 : Blo 1032607 1400915 := bstep (se 1 (by rfl) ⟨1050686, by rfl⟩ : syracuseStep 1400915 = 2101373) B2101373
theorem B2482289 : Blo 1032607 2482289 := bstep (se 2 (by rfl) ⟨930858, by rfl⟩ : syracuseStep 2482289 = 1861717) B1861717
theorem B2941105 : Blo 1032607 2941105 := bstep (se 2 (by rfl) ⟨1102914, by rfl⟩ : syracuseStep 2941105 = 2205829) B2205829
theorem B1106195 : Blo 1032607 1106195 := bstep (se 1 (by rfl) ⟨829646, by rfl⟩ : syracuseStep 1106195 = 1659293) B1659293
theorem B2482481 : Blo 1032607 2482481 := bstep (se 2 (by rfl) ⟨930930, by rfl⟩ : syracuseStep 2482481 = 1861861) B1861861
theorem B2941265 : Blo 1032607 2941265 := bstep (se 2 (by rfl) ⟨1102974, by rfl⟩ : syracuseStep 2941265 = 2205949) B2205949
theorem B5890481 : Blo 1032607 5890481 := bstep (se 2 (by rfl) ⟨2208930, by rfl⟩ : syracuseStep 5890481 = 4417861) B4417861
theorem B2941379 : Blo 1032607 2941379 := bstep (se 1 (by rfl) ⟨2206034, by rfl⟩ : syracuseStep 2941379 = 4412069) B4412069
theorem B1991153 : Blo 1032607 1991153 := bstep (se 2 (by rfl) ⟨746682, by rfl⟩ : syracuseStep 1991153 = 1493365) B1493365
theorem B2613809 : Blo 1032607 2613809 := bstep (se 2 (by rfl) ⟨980178, by rfl⟩ : syracuseStep 2613809 = 1960357) B1960357
theorem B3924557 : Blo 1032607 3924557 := bstep (se 3 (by rfl) ⟨735854, by rfl⟩ : syracuseStep 3924557 = 1471709) B1471709
theorem B2482769 : Blo 1032607 2482769 := bstep (se 2 (by rfl) ⟨931038, by rfl⟩ : syracuseStep 2482769 = 1862077) B1862077
theorem B7070435 : Blo 1032607 7070435 := bstep (se 1 (by rfl) ⟨5302826, by rfl⟩ : syracuseStep 7070435 = 10605653) B10605653
theorem B1106947 : Blo 1032607 1106947 := bstep (se 1 (by rfl) ⟨830210, by rfl⟩ : syracuseStep 1106947 = 1660421) B1660421
theorem B7464163 : Blo 1032607 7464163 := bstep (se 1 (by rfl) ⟨5598122, by rfl⟩ : syracuseStep 7464163 = 11196245) B11196245
theorem B3925361 : Blo 1032607 3925361 := bstep (se 2 (by rfl) ⟨1472010, by rfl⟩ : syracuseStep 3925361 = 2944021) B2944021
theorem B2942381 : Blo 1032607 2942381 := bstep (se 3 (by rfl) ⟨551696, by rfl⟩ : syracuseStep 2942381 = 1103393) B1103393
theorem B13264397 : Blo 1032607 13264397 := bstep (se 3 (by rfl) ⟨2487074, by rfl⟩ : syracuseStep 13264397 = 4974149) B4974149
theorem B2614801 : Blo 1032607 2614801 := bstep (se 2 (by rfl) ⟨980550, by rfl⟩ : syracuseStep 2614801 = 1961101) B1961101
theorem B2942563 : Blo 1032607 2942563 := bstep (se 1 (by rfl) ⟨2206922, by rfl⟩ : syracuseStep 2942563 = 4413845) B4413845
theorem B4187825 : Blo 1032607 4187825 := bstep (se 2 (by rfl) ⟨1570434, by rfl⟩ : syracuseStep 4187825 = 3140869) B3140869
theorem B5596913 : Blo 1032607 5596913 := bstep (se 2 (by rfl) ⟨2098842, by rfl⟩ : syracuseStep 5596913 = 4197685) B4197685
theorem B2942723 : Blo 1032607 2942723 := bstep (se 1 (by rfl) ⟨2207042, by rfl⟩ : syracuseStep 2942723 = 4414085) B4414085
theorem B2615075 : Blo 1032607 2615075 := bstep (se 1 (by rfl) ⟨1961306, by rfl⟩ : syracuseStep 2615075 = 3922613) B3922613
theorem B4187953 : Blo 1032607 4187953 := bstep (se 2 (by rfl) ⟨1570482, by rfl⟩ : syracuseStep 4187953 = 3140965) B3140965
theorem B21489461 : Blo 1032607 21489461 := bstep (se 5 (by rfl) ⟨1007318, by rfl⟩ : syracuseStep 21489461 = 2014637) B2014637
theorem B5891939 : Blo 1032607 5891939 := bstep (se 1 (by rfl) ⟨4418954, by rfl⟩ : syracuseStep 5891939 = 8837909) B8837909
theorem B2615267 : Blo 1032607 2615267 := bstep (se 1 (by rfl) ⟨1961450, by rfl⟩ : syracuseStep 2615267 = 3922901) B3922901
theorem B3926029 : Blo 1032607 3926029 := bstep (se 3 (by rfl) ⟨736130, by rfl⟩ : syracuseStep 3926029 = 1472261) B1472261
theorem B9824483 : Blo 1032607 9824483 := bstep (se 1 (by rfl) ⟨7368362, by rfl⟩ : syracuseStep 9824483 = 14736725) B14736725
theorem B1960433 : Blo 1032607 1960433 := bstep (se 2 (by rfl) ⟨735162, by rfl⟩ : syracuseStep 1960433 = 1470325) B1470325
theorem B5237297 : Blo 1032607 5237297 := bstep (se 2 (by rfl) ⟨1963986, by rfl⟩ : syracuseStep 5237297 = 3927973) B3927973
theorem B3926819 : Blo 1032607 3926819 := bstep (se 1 (by rfl) ⟨2945114, by rfl⟩ : syracuseStep 3926819 = 5890229) B5890229
theorem B2943793 : Blo 1032607 2943793 := bstep (se 2 (by rfl) ⟨1103922, by rfl⟩ : syracuseStep 2943793 = 2207845) B2207845
theorem B3730225 : Blo 1032607 3730225 := bstep (se 2 (by rfl) ⟨1398834, by rfl⟩ : syracuseStep 3730225 = 2797669) B2797669
theorem B2616209 : Blo 1032607 2616209 := bstep (se 2 (by rfl) ⟨981078, by rfl⟩ : syracuseStep 2616209 = 1962157) B1962157
theorem B2616259 : Blo 1032607 2616259 := bstep (se 1 (by rfl) ⟨1962194, by rfl⟩ : syracuseStep 2616259 = 3924389) B3924389
theorem B2124785 : Blo 1032607 2124785 := bstep (se 2 (by rfl) ⟨796794, by rfl⟩ : syracuseStep 2124785 = 1593589) B1593589
theorem B2616401 : Blo 1032607 2616401 := bstep (se 2 (by rfl) ⟨981150, by rfl⟩ : syracuseStep 2616401 = 1962301) B1962301
theorem B1961329 : Blo 1032607 1961329 := bstep (se 2 (by rfl) ⟨735498, by rfl⟩ : syracuseStep 1961329 = 1470997) B1470997
theorem B3927473 : Blo 1032607 3927473 := bstep (se 2 (by rfl) ⟨1472802, by rfl⟩ : syracuseStep 3927473 = 2945605) B2945605
theorem B1961489 : Blo 1032607 1961489 := bstep (se 2 (by rfl) ⟨735558, by rfl⟩ : syracuseStep 1961489 = 1471117) B1471117
theorem B4419107 : Blo 1032607 4419107 := bstep (se 1 (by rfl) ⟨3314330, by rfl⟩ : syracuseStep 4419107 = 6628661) B6628661
theorem B75492917 : Blo 1032607 75492917 := bstep (se 5 (by rfl) ⟨3538730, by rfl⟩ : syracuseStep 75492917 = 7077461) B7077461
theorem B5893829 : Blo 1032607 5893829 := bstep (se 4 (by rfl) ⟨552546, by rfl⟩ : syracuseStep 5893829 = 1105093) B1105093
theorem B5598989 : Blo 1032607 5598989 := bstep (se 3 (by rfl) ⟨1049810, by rfl⟩ : syracuseStep 5598989 = 2099621) B2099621
theorem B3141443 : Blo 1032607 3141443 := bstep (se 1 (by rfl) ⟨2356082, by rfl⟩ : syracuseStep 3141443 = 4712165) B4712165
theorem B1961891 : Blo 1032607 1961891 := bstep (se 1 (by rfl) ⟨1471418, by rfl⟩ : syracuseStep 1961891 = 2942837) B2942837
theorem B5238755 : Blo 1032607 5238755 := bstep (se 1 (by rfl) ⟨3929066, by rfl⟩ : syracuseStep 5238755 = 7858133) B7858133
theorem B2945069 : Blo 1032607 2945069 := bstep (se 3 (by rfl) ⟨552200, by rfl⟩ : syracuseStep 2945069 = 1104401) B1104401
theorem B2617393 : Blo 1032607 2617393 := bstep (se 2 (by rfl) ⟨981522, by rfl⟩ : syracuseStep 2617393 = 1963045) B1963045
theorem B2945251 : Blo 1032607 2945251 := bstep (se 1 (by rfl) ⟨2208938, by rfl⟩ : syracuseStep 2945251 = 4417877) B4417877
theorem B1241347 : Blo 1032607 1241347 := bstep (se 1 (by rfl) ⟨931010, by rfl⟩ : syracuseStep 1241347 = 1862021) B1862021
theorem B2945297 : Blo 1032607 2945297 := bstep (se 2 (by rfl) ⟨1104486, by rfl⟩ : syracuseStep 2945297 = 2208973) B2208973
theorem B2617667 : Blo 1032607 2617667 := bstep (se 1 (by rfl) ⟨1963250, by rfl⟩ : syracuseStep 2617667 = 3926501) B3926501
theorem B1470803 : Blo 1032607 1470803 := bstep (se 1 (by rfl) ⟨1103102, by rfl⟩ : syracuseStep 1470803 = 2206205) B2206205
theorem B1307011 : Blo 1032607 1307011 := bstep (se 1 (by rfl) ⟨980258, by rfl⟩ : syracuseStep 1307011 = 1960517) B1960517
theorem B1307107 : Blo 1032607 1307107 := bstep (se 1 (by rfl) ⟨980330, by rfl⟩ : syracuseStep 1307107 = 1960661) B1960661
theorem B2617859 : Blo 1032607 2617859 := bstep (se 1 (by rfl) ⟨1963394, by rfl⟩ : syracuseStep 2617859 = 3926789) B3926789
theorem B5239565 : Blo 1032607 5239565 := bstep (se 3 (by rfl) ⟨982418, by rfl⟩ : syracuseStep 5239565 = 1964837) B1964837
theorem B1962787 : Blo 1032607 1962787 := bstep (se 1 (by rfl) ⟨1472090, by rfl⟩ : syracuseStep 1962787 = 2944181) B2944181
theorem B3928931 : Blo 1032607 3928931 := bstep (se 1 (by rfl) ⟨2946698, by rfl⟩ : syracuseStep 3928931 = 5893397) B5893397
theorem B3928945 : Blo 1032607 3928945 := bstep (se 2 (by rfl) ⟨1473354, by rfl⟩ : syracuseStep 3928945 = 2946709) B2946709
theorem B4977571 : Blo 1032607 4977571 := bstep (se 1 (by rfl) ⟨3733178, by rfl⟩ : syracuseStep 4977571 = 7466357) B7466357
theorem B1962947 : Blo 1032607 1962947 := bstep (se 1 (by rfl) ⟨1472210, by rfl⟩ : syracuseStep 1962947 = 2944421) B2944421
theorem B1471441 : Blo 1032607 1471441 := bstep (se 2 (by rfl) ⟨551790, by rfl⟩ : syracuseStep 1471441 = 1103581) B1103581
theorem B1307603 : Blo 1032607 1307603 := bstep (se 1 (by rfl) ⟨980702, by rfl⟩ : syracuseStep 1307603 = 1961405) B1961405
theorem B1242163 : Blo 1032607 1242163 := bstep (se 1 (by rfl) ⟨931622, by rfl⟩ : syracuseStep 1242163 = 1863245) B1863245
theorem B1766465 : Blo 1032607 1766465 := bstep (se 2 (by rfl) ⟨662424, by rfl⟩ : syracuseStep 1766465 = 1324849) B1324849
theorem B1471555 : Blo 1032607 1471555 := bstep (se 1 (by rfl) ⟨1103666, by rfl⟩ : syracuseStep 1471555 = 2207333) B2207333
theorem B2323601 : Blo 1032607 2323601 := bstep (se 2 (by rfl) ⟨871350, by rfl⟩ : syracuseStep 2323601 = 1742701) B1742701
theorem B2323619 : Blo 1032607 2323619 := bstep (se 1 (by rfl) ⟨1742714, by rfl⟩ : syracuseStep 2323619 = 3485429) B3485429
theorem B2323889 : Blo 1032607 2323889 := bstep (se 2 (by rfl) ⟨871458, by rfl⟩ : syracuseStep 2323889 = 1742917) B1742917
theorem B2618801 : Blo 1032607 2618801 := bstep (se 2 (by rfl) ⟨982050, by rfl⟩ : syracuseStep 2618801 = 1964101) B1964101
theorem B2323907 : Blo 1032607 2323907 := bstep (se 1 (by rfl) ⟨1742930, by rfl⟩ : syracuseStep 2323907 = 3485861) B3485861
theorem B2618851 : Blo 1032607 2618851 := bstep (se 1 (by rfl) ⟨1964138, by rfl⟩ : syracuseStep 2618851 = 3928277) B3928277
theorem B2618993 : Blo 1032607 2618993 := bstep (se 2 (by rfl) ⟨982122, by rfl⟩ : syracuseStep 2618993 = 1964245) B1964245
theorem B1308307 : Blo 1032607 1308307 := bstep (se 1 (by rfl) ⟨981230, by rfl⟩ : syracuseStep 1308307 = 1962461) B1962461
theorem B2946755 : Blo 1032607 2946755 := bstep (se 1 (by rfl) ⟨2210066, by rfl⟩ : syracuseStep 2946755 = 4420133) B4420133
theorem B2324177 : Blo 1032607 2324177 := bstep (se 2 (by rfl) ⟨871566, by rfl⟩ : syracuseStep 2324177 = 1743133) B1743133
theorem B2324195 : Blo 1032607 2324195 := bstep (se 1 (by rfl) ⟨1743146, by rfl⟩ : syracuseStep 2324195 = 3486293) B3486293
theorem B1308403 : Blo 1032607 1308403 := bstep (se 1 (by rfl) ⟨981302, by rfl⟩ : syracuseStep 1308403 = 1962605) B1962605
theorem B1570691 : Blo 1032607 1570691 := bstep (se 1 (by rfl) ⟨1178018, by rfl⟩ : syracuseStep 1570691 = 2356037) B2356037
theorem B2324465 : Blo 1032607 2324465 := bstep (se 2 (by rfl) ⟨871674, by rfl⟩ : syracuseStep 2324465 = 1743349) B1743349
theorem B1964017 : Blo 1032607 1964017 := bstep (se 2 (by rfl) ⟨736506, by rfl⟩ : syracuseStep 1964017 = 1473013) B1473013
theorem B2324483 : Blo 1032607 2324483 := bstep (se 1 (by rfl) ⟨1743362, by rfl⟩ : syracuseStep 2324483 = 3486725) B3486725
theorem B2095139 : Blo 1032607 2095139 := bstep (se 1 (by rfl) ⟨1571354, by rfl⟩ : syracuseStep 2095139 = 3142709) B3142709
theorem B1308899 : Blo 1032607 1308899 := bstep (se 1 (by rfl) ⟨981674, by rfl⟩ : syracuseStep 1308899 = 1963349) B1963349
theorem B2324753 : Blo 1032607 2324753 := bstep (se 2 (by rfl) ⟨871782, by rfl⟩ : syracuseStep 2324753 = 1743565) B1743565
theorem B1702163 : Blo 1032607 1702163 := bstep (se 1 (by rfl) ⟨1276622, by rfl⟩ : syracuseStep 1702163 = 2553245) B2553245
theorem B2324771 : Blo 1032607 2324771 := bstep (se 1 (by rfl) ⟨1743578, by rfl⟩ : syracuseStep 2324771 = 3487157) B3487157
theorem B3930403 : Blo 1032607 3930403 := bstep (se 1 (by rfl) ⟨2947802, by rfl⟩ : syracuseStep 3930403 = 5895605) B5895605
theorem B3537229 : Blo 1032607 3537229 := bstep (se 3 (by rfl) ⟨663230, by rfl⟩ : syracuseStep 3537229 = 1326461) B1326461
theorem B1472899 : Blo 1032607 1472899 := bstep (se 1 (by rfl) ⟨1104674, by rfl⟩ : syracuseStep 1472899 = 2209349) B2209349
theorem B7567757 : Blo 1032607 7567757 := bstep (se 3 (by rfl) ⟨1418954, by rfl⟩ : syracuseStep 7567757 = 2837909) B2837909
theorem B1767827 : Blo 1032607 1767827 := bstep (se 1 (by rfl) ⟨1325870, by rfl⟩ : syracuseStep 1767827 = 2651741) B2651741
theorem B3734029 : Blo 1032607 3734029 := bstep (se 3 (by rfl) ⟨700130, by rfl⟩ : syracuseStep 3734029 = 1400261) B1400261
theorem B3308077 : Blo 1032607 3308077 := bstep (se 3 (by rfl) ⟨620264, by rfl⟩ : syracuseStep 3308077 = 1240529) B1240529
theorem B2325041 : Blo 1032607 2325041 := bstep (se 2 (by rfl) ⟨871890, by rfl⟩ : syracuseStep 2325041 = 1743781) B1743781
theorem B2325059 : Blo 1032607 2325059 := bstep (se 1 (by rfl) ⟨1743794, by rfl⟩ : syracuseStep 2325059 = 3487589) B3487589
theorem B2619985 : Blo 1032607 2619985 := bstep (se 2 (by rfl) ⟨982494, by rfl⟩ : syracuseStep 2619985 = 1964989) B1964989
theorem B26835569 : Blo 1032607 26835569 := bstep (se 2 (by rfl) ⟨10063338, by rfl⟩ : syracuseStep 26835569 = 20126677) B20126677
theorem B1178227 : Blo 1032607 1178227 := bstep (se 1 (by rfl) ⟨883670, by rfl⟩ : syracuseStep 1178227 = 1767341) B1767341
theorem B2325329 : Blo 1032607 2325329 := bstep (se 2 (by rfl) ⟨871998, by rfl⟩ : syracuseStep 2325329 = 1743997) B1743997
theorem B2325347 : Blo 1032607 2325347 := bstep (se 1 (by rfl) ⟨1744010, by rfl⟩ : syracuseStep 2325347 = 3488021) B3488021
theorem B2620259 : Blo 1032607 2620259 := bstep (se 1 (by rfl) ⟨1965194, by rfl⟩ : syracuseStep 2620259 = 3930389) B3930389
theorem B3144557 : Blo 1032607 3144557 := bstep (se 3 (by rfl) ⟨589604, by rfl⟩ : syracuseStep 3144557 = 1179209) B1179209
theorem B2947985 : Blo 1032607 2947985 := bstep (se 2 (by rfl) ⟨1105494, by rfl⟩ : syracuseStep 2947985 = 2210989) B2210989
theorem B1309603 : Blo 1032607 1309603 := bstep (se 1 (by rfl) ⟨982202, by rfl⟩ : syracuseStep 1309603 = 1964405) B1964405
theorem B1047475 : Blo 1032607 1047475 := bstep (se 1 (by rfl) ⟨785606, by rfl⟩ : syracuseStep 1047475 = 1571213) B1571213
theorem B1309699 : Blo 1032607 1309699 := bstep (se 1 (by rfl) ⟨982274, by rfl⟩ : syracuseStep 1309699 = 1964549) B1964549
theorem B1965073 : Blo 1032607 1965073 := bstep (se 2 (by rfl) ⟨736902, by rfl⟩ : syracuseStep 1965073 = 1473805) B1473805
theorem B2620451 : Blo 1032607 2620451 := bstep (se 1 (by rfl) ⟨1965338, by rfl⟩ : syracuseStep 2620451 = 3930677) B3930677
theorem B2325617 : Blo 1032607 2325617 := bstep (se 2 (by rfl) ⟨872106, by rfl⟩ : syracuseStep 2325617 = 1744213) B1744213
theorem B2325635 : Blo 1032607 2325635 := bstep (se 1 (by rfl) ⟨1744226, by rfl⟩ : syracuseStep 2325635 = 3488453) B3488453
theorem B4422833 : Blo 1032607 4422833 := bstep (se 2 (by rfl) ⟨1658562, by rfl⟩ : syracuseStep 4422833 = 3317125) B3317125
theorem B1572065 : Blo 1032607 1572065 := bstep (se 2 (by rfl) ⟨589524, by rfl⟩ : syracuseStep 1572065 = 1179049) B1179049
theorem B2325905 : Blo 1032607 2325905 := bstep (se 2 (by rfl) ⟨872214, by rfl⟩ : syracuseStep 2325905 = 1744429) B1744429
theorem B2325923 : Blo 1032607 2325923 := bstep (se 1 (by rfl) ⟨1744442, by rfl⟩ : syracuseStep 2325923 = 3488885) B3488885
theorem B1965475 : Blo 1032607 1965475 := bstep (se 1 (by rfl) ⟨1474106, by rfl⟩ : syracuseStep 1965475 = 2948213) B2948213
theorem B1965521 : Blo 1032607 1965521 := bstep (se 2 (by rfl) ⟨737070, by rfl⟩ : syracuseStep 1965521 = 1474141) B1474141
theorem B1474033 : Blo 1032607 1474033 := bstep (se 2 (by rfl) ⟨552762, by rfl⟩ : syracuseStep 1474033 = 1105525) B1105525
theorem B1310195 : Blo 1032607 1310195 := bstep (se 1 (by rfl) ⟨982646, by rfl⟩ : syracuseStep 1310195 = 1965293) B1965293
theorem B1474129 : Blo 1032607 1474129 := bstep (se 2 (by rfl) ⟨552798, by rfl⟩ : syracuseStep 1474129 = 1105597) B1105597
theorem B3538541 : Blo 1032607 3538541 := bstep (se 3 (by rfl) ⟨663476, by rfl⟩ : syracuseStep 3538541 = 1326953) B1326953
theorem B5242481 : Blo 1032607 5242481 := bstep (se 2 (by rfl) ⟨1965930, by rfl⟩ : syracuseStep 5242481 = 3931861) B3931861
theorem B2916013 : Blo 1032607 2916013 := bstep (se 3 (by rfl) ⟨546752, by rfl⟩ : syracuseStep 2916013 = 1093505) B1093505
theorem B2326193 : Blo 1032607 2326193 := bstep (se 2 (by rfl) ⟨872322, by rfl⟩ : syracuseStep 2326193 = 1744645) B1744645
theorem B2326211 : Blo 1032607 2326211 := bstep (se 1 (by rfl) ⟨1744658, by rfl⟩ : syracuseStep 2326211 = 3489317) B3489317
theorem B1965809 : Blo 1032607 1965809 := bstep (se 2 (by rfl) ⟨737178, by rfl⟩ : syracuseStep 1965809 = 1474357) B1474357
theorem B5603185 : Blo 1032607 5603185 := bstep (se 2 (by rfl) ⟨2101194, by rfl⟩ : syracuseStep 5603185 = 4202389) B4202389
theorem B1179523 : Blo 1032607 1179523 := bstep (se 1 (by rfl) ⟨884642, by rfl⟩ : syracuseStep 1179523 = 1769285) B1769285
theorem B2326481 : Blo 1032607 2326481 := bstep (se 2 (by rfl) ⟨872430, by rfl⟩ : syracuseStep 2326481 = 1744861) B1744861
theorem B2621393 : Blo 1032607 2621393 := bstep (se 2 (by rfl) ⟨983022, by rfl⟩ : syracuseStep 2621393 = 1966045) B1966045
theorem B2326499 : Blo 1032607 2326499 := bstep (se 1 (by rfl) ⟨1744874, by rfl⟩ : syracuseStep 2326499 = 3489749) B3489749
theorem B2326553 : Blo 1032607 2326553 := bstep (se 2 (by rfl) ⟨872457, by rfl⟩ : syracuseStep 2326553 = 1744915) B1744915
theorem B1867801 : Blo 1032607 1867801 := bstep (se 2 (by rfl) ⟨700425, by rfl⟩ : syracuseStep 1867801 = 1400851) B1400851
theorem B6619229 : Blo 1032607 6619229 := bstep (se 3 (by rfl) ⟨1241105, by rfl⟩ : syracuseStep 6619229 = 2482211) B2482211
theorem B2326643 : Blo 1032607 2326643 := bstep (se 1 (by rfl) ⟨1744982, by rfl⟩ : syracuseStep 2326643 = 3489965) B3489965
theorem B7864451 : Blo 1032607 7864451 := bstep (se 1 (by rfl) ⟨5898338, by rfl⟩ : syracuseStep 7864451 = 11796677) B11796677
theorem B1474699 : Blo 1032607 1474699 := bstep (se 1 (by rfl) ⟨1106024, by rfl⟩ : syracuseStep 1474699 = 2212049) B2212049
theorem B2326679 : Blo 1032607 2326679 := bstep (se 1 (by rfl) ⟨1745009, by rfl⟩ : syracuseStep 2326679 = 3490019) B3490019
theorem B3932333 : Blo 1032607 3932333 := bstep (se 3 (by rfl) ⟨737312, by rfl⟩ : syracuseStep 3932333 = 1474625) B1474625
theorem B1966295 : Blo 1032607 1966295 := bstep (se 1 (by rfl) ⟨1474721, by rfl⟩ : syracuseStep 1966295 = 2949443) B2949443
theorem B4980953 : Blo 1032607 4980953 := bstep (se 2 (by rfl) ⟨1867857, by rfl⟩ : syracuseStep 4980953 = 3735715) B3735715
theorem B3735773 : Blo 1032607 3735773 := bstep (se 3 (by rfl) ⟨700457, by rfl⟩ : syracuseStep 3735773 = 1400915) B1400915
theorem B2621747 : Blo 1032607 2621747 := bstep (se 1 (by rfl) ⟨1966310, by rfl⟩ : syracuseStep 2621747 = 3932621) B3932621
theorem B2326859 : Blo 1032607 2326859 := bstep (se 1 (by rfl) ⟨1745144, by rfl⟩ : syracuseStep 2326859 = 3490289) B3490289
theorem B2326913 : Blo 1032607 2326913 := bstep (se 2 (by rfl) ⟨872592, by rfl⟩ : syracuseStep 2326913 = 1745185) B1745185
theorem B1311319 : Blo 1032607 1311319 := bstep (se 1 (by rfl) ⟨983489, by rfl⟩ : syracuseStep 1311319 = 1966979) B1966979
theorem B2327129 : Blo 1032607 2327129 := bstep (se 2 (by rfl) ⟨872673, by rfl⟩ : syracuseStep 2327129 = 1745347) B1745347
theorem B2622041 : Blo 1032607 2622041 := bstep (se 2 (by rfl) ⟨983265, by rfl⟩ : syracuseStep 2622041 = 1966531) B1966531
theorem B2327219 : Blo 1032607 2327219 := bstep (se 1 (by rfl) ⟨1745414, by rfl⟩ : syracuseStep 2327219 = 3490829) B3490829
theorem B2327255 : Blo 1032607 2327255 := bstep (se 1 (by rfl) ⟨1745441, by rfl⟩ : syracuseStep 2327255 = 3490883) B3490883
theorem B2949853 : Blo 1032607 2949853 := bstep (se 3 (by rfl) ⟨553097, by rfl⟩ : syracuseStep 2949853 = 1106195) B1106195
theorem B1966835 : Blo 1032607 1966835 := bstep (se 1 (by rfl) ⟨1475126, by rfl⟩ : syracuseStep 1966835 = 2950253) B2950253
theorem B14943041 : Blo 1032607 14943041 := bstep (se 2 (by rfl) ⟨5603640, by rfl⟩ : syracuseStep 14943041 = 11207281) B11207281
theorem B8389469 : Blo 1032607 8389469 := bstep (se 3 (by rfl) ⟨1573025, by rfl⟩ : syracuseStep 8389469 = 3146051) B3146051
theorem B2327435 : Blo 1032607 2327435 := bstep (se 1 (by rfl) ⟨1745576, by rfl⟩ : syracuseStep 2327435 = 3491153) B3491153
theorem B1049483 : Blo 1032607 1049483 := bstep (se 1 (by rfl) ⟨787112, by rfl⟩ : syracuseStep 1049483 = 1574225) B1574225
theorem B3933107 : Blo 1032607 3933107 := bstep (se 1 (by rfl) ⟨2949830, by rfl⟩ : syracuseStep 3933107 = 5899661) B5899661
theorem B2327489 : Blo 1032607 2327489 := bstep (se 2 (by rfl) ⟨872808, by rfl⟩ : syracuseStep 2327489 = 1745617) B1745617
theorem B2098163 : Blo 1032607 2098163 := bstep (se 1 (by rfl) ⟨1573622, by rfl⟩ : syracuseStep 2098163 = 3147245) B3147245
theorem B47842325 : Blo 1032607 47842325 := bstep (se 6 (by rfl) ⟨1121304, by rfl⟩ : syracuseStep 47842325 = 2242609) B2242609
theorem B2950195 : Blo 1032607 2950195 := bstep (se 1 (by rfl) ⟨2212646, by rfl⟩ : syracuseStep 2950195 = 4425293) B4425293
theorem B24249419 : Blo 1032607 24249419 := bstep (se 1 (by rfl) ⟨18187064, by rfl⟩ : syracuseStep 24249419 = 36374129) B36374129
theorem B2327705 : Blo 1032607 2327705 := bstep (se 2 (by rfl) ⟨872889, by rfl⟩ : syracuseStep 2327705 = 1745779) B1745779
theorem B4719809 : Blo 1032607 4719809 := bstep (se 2 (by rfl) ⟨1769928, by rfl⟩ : syracuseStep 4719809 = 3539857) B3539857
theorem B1967321 : Blo 1032607 1967321 := bstep (se 2 (by rfl) ⟨737745, by rfl⟩ : syracuseStep 1967321 = 1475491) B1475491
theorem B2327795 : Blo 1032607 2327795 := bstep (se 1 (by rfl) ⟨1745846, by rfl⟩ : syracuseStep 2327795 = 3491693) B3491693
theorem B2327831 : Blo 1032607 2327831 := bstep (se 1 (by rfl) ⟨1745873, by rfl⟩ : syracuseStep 2327831 = 3491747) B3491747
theorem B1475929 : Blo 1032607 1475929 := bstep (se 2 (by rfl) ⟨553473, by rfl⟩ : syracuseStep 1475929 = 1106947) B1106947
theorem B6292829 : Blo 1032607 6292829 := bstep (se 3 (by rfl) ⟨1179905, by rfl⟩ : syracuseStep 6292829 = 2359811) B2359811
theorem B2328011 : Blo 1032607 2328011 := bstep (se 1 (by rfl) ⟨1746008, by rfl⟩ : syracuseStep 2328011 = 3492017) B3492017
theorem B2328065 : Blo 1032607 2328065 := bstep (se 2 (by rfl) ⟨873024, by rfl⟩ : syracuseStep 2328065 = 1746049) B1746049
theorem B6620717 : Blo 1032607 6620717 := bstep (se 3 (by rfl) ⟨1241384, by rfl⟩ : syracuseStep 6620717 = 2482769) B2482769
theorem B1050167 : Blo 1032607 1050167 := bstep (se 1 (by rfl) ⟨787625, by rfl⟩ : syracuseStep 1050167 = 1575251) B1575251
theorem B2098777 : Blo 1032607 2098777 := bstep (se 2 (by rfl) ⟨787041, by rfl⟩ : syracuseStep 2098777 = 1574083) B1574083
theorem B6293123 : Blo 1032607 6293123 := bstep (se 1 (by rfl) ⟨4719842, by rfl⟩ : syracuseStep 6293123 = 9439685) B9439685
theorem B3311255 : Blo 1032607 3311255 := bstep (se 1 (by rfl) ⟨2483441, by rfl⟩ : syracuseStep 3311255 = 4966883) B4966883
theorem B2328281 : Blo 1032607 2328281 := bstep (se 2 (by rfl) ⟨873105, by rfl⟩ : syracuseStep 2328281 = 1746211) B1746211
theorem B2361089 : Blo 1032607 2361089 := bstep (se 2 (by rfl) ⟨885408, by rfl⟩ : syracuseStep 2361089 = 1770817) B1770817
theorem B2328371 : Blo 1032607 2328371 := bstep (se 1 (by rfl) ⟨1746278, by rfl⟩ : syracuseStep 2328371 = 3492557) B3492557
theorem B2328407 : Blo 1032607 2328407 := bstep (se 1 (by rfl) ⟨1746305, by rfl⟩ : syracuseStep 2328407 = 3492611) B3492611
theorem B3311563 : Blo 1032607 3311563 := bstep (se 1 (by rfl) ⟨2483672, by rfl⟩ : syracuseStep 3311563 = 4967345) B4967345
theorem B2951129 : Blo 1032607 2951129 := bstep (se 2 (by rfl) ⟨1106673, by rfl⟩ : syracuseStep 2951129 = 2213347) B2213347
theorem B2328587 : Blo 1032607 2328587 := bstep (se 1 (by rfl) ⟨1746440, by rfl⟩ : syracuseStep 2328587 = 3492881) B3492881
theorem B5310481 : Blo 1032607 5310481 := bstep (se 2 (by rfl) ⟨1991430, by rfl⟩ : syracuseStep 5310481 = 3982861) B3982861
theorem B2328641 : Blo 1032607 2328641 := bstep (se 2 (by rfl) ⟨873240, by rfl⟩ : syracuseStep 2328641 = 1746481) B1746481
theorem B2623691 : Blo 1032607 2623691 := bstep (se 1 (by rfl) ⟨1967768, by rfl⟩ : syracuseStep 2623691 = 3935537) B3935537
theorem B2328857 : Blo 1032607 2328857 := bstep (se 2 (by rfl) ⟨873321, by rfl⟩ : syracuseStep 2328857 = 1746643) B1746643
theorem B2328947 : Blo 1032607 2328947 := bstep (se 1 (by rfl) ⟨1746710, by rfl⟩ : syracuseStep 2328947 = 3493421) B3493421
theorem B3934595 : Blo 1032607 3934595 := bstep (se 1 (by rfl) ⟨2950946, by rfl⟩ : syracuseStep 3934595 = 5901893) B5901893
theorem B2328983 : Blo 1032607 2328983 := bstep (se 1 (by rfl) ⟨1746737, by rfl⟩ : syracuseStep 2328983 = 3493475) B3493475
theorem B17697203 : Blo 1032607 17697203 := bstep (se 1 (by rfl) ⟨13272902, by rfl⟩ : syracuseStep 17697203 = 26545805) B26545805
theorem B7375283 : Blo 1032607 7375283 := bstep (se 1 (by rfl) ⟨5531462, by rfl⟩ : syracuseStep 7375283 = 11062925) B11062925
theorem B2329163 : Blo 1032607 2329163 := bstep (se 1 (by rfl) ⟨1746872, by rfl⟩ : syracuseStep 2329163 = 3493745) B3493745
theorem B2329217 : Blo 1032607 2329217 := bstep (se 2 (by rfl) ⟨873456, by rfl⟩ : syracuseStep 2329217 = 1746913) B1746913
theorem B3935051 : Blo 1032607 3935051 := bstep (se 1 (by rfl) ⟨2951288, by rfl⟩ : syracuseStep 3935051 = 5902577) B5902577
theorem B2329433 : Blo 1032607 2329433 := bstep (se 2 (by rfl) ⟨873537, by rfl⟩ : syracuseStep 2329433 = 1747075) B1747075
theorem B2329523 : Blo 1032607 2329523 := bstep (se 1 (by rfl) ⟨1747142, by rfl⟩ : syracuseStep 2329523 = 3494285) B3494285
theorem B2329559 : Blo 1032607 2329559 := bstep (se 1 (by rfl) ⟨1747169, by rfl⟩ : syracuseStep 2329559 = 3494339) B3494339
theorem B5049305 : Blo 1032607 5049305 := bstep (se 2 (by rfl) ⟨1893489, by rfl⟩ : syracuseStep 5049305 = 3786979) B3786979
theorem B3935249 : Blo 1032607 3935249 := bstep (se 2 (by rfl) ⟨1475718, by rfl⟩ : syracuseStep 3935249 = 2951437) B2951437
theorem B5246045 : Blo 1032607 5246045 := bstep (se 3 (by rfl) ⟨983633, by rfl⟩ : syracuseStep 5246045 = 1967267) B1967267
theorem B4426883 : Blo 1032607 4426883 := bstep (se 1 (by rfl) ⟨3320162, by rfl⟩ : syracuseStep 4426883 = 6640325) B6640325
theorem B2329739 : Blo 1032607 2329739 := bstep (se 1 (by rfl) ⟨1747304, by rfl⟩ : syracuseStep 2329739 = 3494609) B3494609
theorem B2329793 : Blo 1032607 2329793 := bstep (se 2 (by rfl) ⟨873672, by rfl⟩ : syracuseStep 2329793 = 1747345) B1747345
theorem B2330009 : Blo 1032607 2330009 := bstep (se 2 (by rfl) ⟨873753, by rfl⟩ : syracuseStep 2330009 = 1747507) B1747507
theorem B2100659 : Blo 1032607 2100659 := bstep (se 1 (by rfl) ⟨1575494, by rfl⟩ : syracuseStep 2100659 = 3150989) B3150989
theorem B7867853 : Blo 1032607 7867853 := bstep (se 3 (by rfl) ⟨1475222, by rfl⟩ : syracuseStep 7867853 = 2950445) B2950445
theorem B2362841 : Blo 1032607 2362841 := bstep (se 2 (by rfl) ⟨886065, by rfl⟩ : syracuseStep 2362841 = 1772131) B1772131
theorem B2330099 : Blo 1032607 2330099 := bstep (se 1 (by rfl) ⟨1747574, by rfl⟩ : syracuseStep 2330099 = 3495149) B3495149
theorem B2330135 : Blo 1032607 2330135 := bstep (se 1 (by rfl) ⟨1747601, by rfl⟩ : syracuseStep 2330135 = 3495203) B3495203
theorem B8949379 : Blo 1032607 8949379 := bstep (se 1 (by rfl) ⟨6712034, by rfl⟩ : syracuseStep 8949379 = 13424069) B13424069
theorem B2330315 : Blo 1032607 2330315 := bstep (se 1 (by rfl) ⟨1747736, by rfl⟩ : syracuseStep 2330315 = 3495473) B3495473
theorem B2330369 : Blo 1032607 2330369 := bstep (se 2 (by rfl) ⟨873888, by rfl⟩ : syracuseStep 2330369 = 1747777) B1747777
theorem B5902145 : Blo 1032607 5902145 := bstep (se 2 (by rfl) ⟨2213304, by rfl⟩ : syracuseStep 5902145 = 4426609) B4426609
theorem B2101081 : Blo 1032607 2101081 := bstep (se 2 (by rfl) ⟨787905, by rfl⟩ : syracuseStep 2101081 = 1575811) B1575811
theorem B7868339 : Blo 1032607 7868339 := bstep (se 1 (by rfl) ⟨5901254, by rfl⟩ : syracuseStep 7868339 = 11802509) B11802509
theorem B2330585 : Blo 1032607 2330585 := bstep (se 2 (by rfl) ⟨873969, by rfl⟩ : syracuseStep 2330585 = 1747939) B1747939
theorem B3313715 : Blo 1032607 3313715 := bstep (se 1 (by rfl) ⟨2485286, by rfl⟩ : syracuseStep 3313715 = 4970573) B4970573
theorem B2330675 : Blo 1032607 2330675 := bstep (se 1 (by rfl) ⟨1748006, by rfl⟩ : syracuseStep 2330675 = 3496013) B3496013
theorem B2330711 : Blo 1032607 2330711 := bstep (se 1 (by rfl) ⟨1748033, by rfl⟩ : syracuseStep 2330711 = 3496067) B3496067
theorem B4722833 : Blo 1032607 4722833 := bstep (se 2 (by rfl) ⟨1771062, by rfl⟩ : syracuseStep 4722833 = 3542125) B3542125
theorem B2330891 : Blo 1032607 2330891 := bstep (se 1 (by rfl) ⟨1748168, by rfl⟩ : syracuseStep 2330891 = 3496337) B3496337
theorem B2330945 : Blo 1032607 2330945 := bstep (se 2 (by rfl) ⟨874104, by rfl⟩ : syracuseStep 2330945 = 1748209) B1748209
theorem B6623639 : Blo 1032607 6623639 := bstep (se 1 (by rfl) ⟨4967729, by rfl⟩ : syracuseStep 6623639 = 9935459) B9935459
theorem B2331161 : Blo 1032607 2331161 := bstep (se 2 (by rfl) ⟨874185, by rfl⟩ : syracuseStep 2331161 = 1748371) B1748371
theorem B2331251 : Blo 1032607 2331251 := bstep (se 1 (by rfl) ⟨1748438, by rfl⟩ : syracuseStep 2331251 = 3496877) B3496877
theorem B2331287 : Blo 1032607 2331287 := bstep (se 1 (by rfl) ⟨1748465, by rfl⟩ : syracuseStep 2331287 = 3496931) B3496931
theorem B2331467 : Blo 1032607 2331467 := bstep (se 1 (by rfl) ⟨1748600, by rfl⟩ : syracuseStep 2331467 = 3497201) B3497201
theorem B2331521 : Blo 1032607 2331521 := bstep (se 2 (by rfl) ⟨874320, by rfl⟩ : syracuseStep 2331521 = 1748641) B1748641
theorem B8852429 : Blo 1032607 8852429 := bstep (se 3 (by rfl) ⟨1659830, by rfl⟩ : syracuseStep 8852429 = 3319661) B3319661
theorem B12587993 : Blo 1032607 12587993 := bstep (se 2 (by rfl) ⟨4720497, by rfl⟩ : syracuseStep 12587993 = 9440995) B9440995
theorem B2331737 : Blo 1032607 2331737 := bstep (se 2 (by rfl) ⟨874401, by rfl⟩ : syracuseStep 2331737 = 1748803) B1748803
theorem B2331827 : Blo 1032607 2331827 := bstep (se 1 (by rfl) ⟨1748870, by rfl⟩ : syracuseStep 2331827 = 3497741) B3497741
theorem B2331863 : Blo 1032607 2331863 := bstep (se 1 (by rfl) ⟨1748897, by rfl⟩ : syracuseStep 2331863 = 3497795) B3497795
theorem B7869797 : Blo 1032607 7869797 := bstep (se 4 (by rfl) ⟨737793, by rfl⟩ : syracuseStep 7869797 = 1475587) B1475587
theorem B7968131 : Blo 1032607 7968131 := bstep (se 1 (by rfl) ⟨5976098, by rfl⟩ : syracuseStep 7968131 = 11952197) B11952197
theorem B2332043 : Blo 1032607 2332043 := bstep (se 1 (by rfl) ⟨1749032, by rfl⟩ : syracuseStep 2332043 = 3498065) B3498065
theorem B13604273 : Blo 1032607 13604273 := bstep (se 2 (by rfl) ⟨5101602, by rfl⟩ : syracuseStep 13604273 = 10203205) B10203205
theorem B2332097 : Blo 1032607 2332097 := bstep (se 2 (by rfl) ⟨874536, by rfl⟩ : syracuseStep 2332097 = 1749073) B1749073
theorem B10098269 : Blo 1032607 10098269 := bstep (se 3 (by rfl) ⟨1893425, by rfl⟩ : syracuseStep 10098269 = 3786851) B3786851
theorem B2332313 : Blo 1032607 2332313 := bstep (se 2 (by rfl) ⟨874617, by rfl⟩ : syracuseStep 2332313 = 1749235) B1749235
theorem B1742539 : Blo 1032607 1742539 := bstep (se 1 (by rfl) ⟨1306904, by rfl⟩ : syracuseStep 1742539 = 2613809) B2613809
theorem B1677017 : Blo 1032607 1677017 := bstep (se 2 (by rfl) ⟨628881, by rfl⟩ : syracuseStep 1677017 = 1257763) B1257763
theorem B8951597 : Blo 1032607 8951597 := bstep (se 3 (by rfl) ⟨1678424, by rfl⟩ : syracuseStep 8951597 = 3356849) B3356849
theorem B7870283 : Blo 1032607 7870283 := bstep (se 1 (by rfl) ⟨5902712, by rfl⟩ : syracuseStep 7870283 = 11805425) B11805425
theorem B1742681 : Blo 1032607 1742681 := bstep (se 2 (by rfl) ⟨653505, by rfl⟩ : syracuseStep 1742681 = 1307011) B1307011
theorem B4200281 : Blo 1032607 4200281 := bstep (se 2 (by rfl) ⟨1575105, by rfl⟩ : syracuseStep 4200281 = 3150211) B3150211
theorem B1742809 : Blo 1032607 1742809 := bstep (se 2 (by rfl) ⟨653553, by rfl⟩ : syracuseStep 1742809 = 1307107) B1307107
theorem B2791883 : Blo 1032607 2791883 := bstep (se 1 (by rfl) ⟨2093912, by rfl⟩ : syracuseStep 2791883 = 4187825) B4187825
theorem B1743383 : Blo 1032607 1743383 := bstep (se 1 (by rfl) ⟨1307537, by rfl⟩ : syracuseStep 1743383 = 2615075) B2615075
theorem B14326307 : Blo 1032607 14326307 := bstep (se 1 (by rfl) ⟨10744730, by rfl⟩ : syracuseStep 14326307 = 21489461) B21489461
theorem B4725299 : Blo 1032607 4725299 := bstep (se 1 (by rfl) ⟨3543974, by rfl⟩ : syracuseStep 4725299 = 7087949) B7087949
theorem B9443915 : Blo 1032607 9443915 := bstep (se 1 (by rfl) ⟨7082936, by rfl⟩ : syracuseStep 9443915 = 14165873) B14165873
theorem B8395339 : Blo 1032607 8395339 := bstep (se 1 (by rfl) ⟨6296504, by rfl⟩ : syracuseStep 8395339 = 12593009) B12593009
theorem B1743511 : Blo 1032607 1743511 := bstep (se 1 (by rfl) ⟨1307633, by rfl⟩ : syracuseStep 1743511 = 2615267) B2615267
theorem B1744139 : Blo 1032607 1744139 := bstep (se 1 (by rfl) ⟨1308104, by rfl⟩ : syracuseStep 1744139 = 2616209) B2616209
theorem B1416523 : Blo 1032607 1416523 := bstep (se 1 (by rfl) ⟨1062392, by rfl⟩ : syracuseStep 1416523 = 2124785) B2124785
theorem B1744267 : Blo 1032607 1744267 := bstep (se 1 (by rfl) ⟨1308200, by rfl⟩ : syracuseStep 1744267 = 2616401) B2616401
theorem B8068531 : Blo 1032607 8068531 := bstep (se 1 (by rfl) ⟨6051398, by rfl⟩ : syracuseStep 8068531 = 12102797) B12102797
theorem B1744409 : Blo 1032607 1744409 := bstep (se 2 (by rfl) ⟨654153, by rfl⟩ : syracuseStep 1744409 = 1308307) B1308307
theorem B2694745 : Blo 1032607 2694745 := bstep (se 2 (by rfl) ⟨1010529, by rfl⟩ : syracuseStep 2694745 = 2021059) B2021059
theorem B1744537 : Blo 1032607 1744537 := bstep (se 2 (by rfl) ⟨654201, by rfl⟩ : syracuseStep 1744537 = 1308403) B1308403
theorem B1941185 : Blo 1032607 1941185 := bstep (se 2 (by rfl) ⟨727944, by rfl⟩ : syracuseStep 1941185 = 1455889) B1455889
theorem B6627203 : Blo 1032607 6627203 := bstep (se 1 (by rfl) ⟨4970402, by rfl⟩ : syracuseStep 6627203 = 9940805) B9940805
theorem B1745111 : Blo 1032607 1745111 := bstep (se 1 (by rfl) ⟨1308833, by rfl⟩ : syracuseStep 1745111 = 2617667) B2617667
theorem B1745239 : Blo 1032607 1745239 := bstep (se 1 (by rfl) ⟨1308929, by rfl⟩ : syracuseStep 1745239 = 2617859) B2617859
theorem B1548953 : Blo 1032607 1548953 := bstep (se 2 (by rfl) ⟨580857, by rfl⟩ : syracuseStep 1548953 = 1161715) B1161715
theorem B1549067 : Blo 1032607 1549067 := bstep (se 1 (by rfl) ⟨1161800, by rfl⟩ : syracuseStep 1549067 = 2323601) B2323601
theorem B1549079 : Blo 1032607 1549079 := bstep (se 1 (by rfl) ⟨1161809, by rfl⟩ : syracuseStep 1549079 = 2323619) B2323619
theorem B1549145 : Blo 1032607 1549145 := bstep (se 2 (by rfl) ⟨580929, by rfl⟩ : syracuseStep 1549145 = 1161859) B1161859
theorem B1549259 : Blo 1032607 1549259 := bstep (se 1 (by rfl) ⟨1161944, by rfl⟩ : syracuseStep 1549259 = 2323889) B2323889
theorem B1745867 : Blo 1032607 1745867 := bstep (se 1 (by rfl) ⟨1309400, by rfl⟩ : syracuseStep 1745867 = 2618801) B2618801
theorem B1549271 : Blo 1032607 1549271 := bstep (se 1 (by rfl) ⟨1161953, by rfl⟩ : syracuseStep 1549271 = 2323907) B2323907
theorem B1549337 : Blo 1032607 1549337 := bstep (se 2 (by rfl) ⟨581001, by rfl⟩ : syracuseStep 1549337 = 1162003) B1162003
theorem B1745995 : Blo 1032607 1745995 := bstep (se 1 (by rfl) ⟨1309496, by rfl⟩ : syracuseStep 1745995 = 2618993) B2618993
theorem B1549451 : Blo 1032607 1549451 := bstep (se 1 (by rfl) ⟨1162088, by rfl⟩ : syracuseStep 1549451 = 2324177) B2324177
theorem B1549463 : Blo 1032607 1549463 := bstep (se 1 (by rfl) ⟨1162097, by rfl⟩ : syracuseStep 1549463 = 2324195) B2324195
theorem B1549529 : Blo 1032607 1549529 := bstep (se 2 (by rfl) ⟨581073, by rfl⟩ : syracuseStep 1549529 = 1162147) B1162147
theorem B1746137 : Blo 1032607 1746137 := bstep (se 2 (by rfl) ⟨654801, by rfl⟩ : syracuseStep 1746137 = 1309603) B1309603
theorem B1549643 : Blo 1032607 1549643 := bstep (se 1 (by rfl) ⟨1162232, by rfl⟩ : syracuseStep 1549643 = 2324465) B2324465
theorem B1549655 : Blo 1032607 1549655 := bstep (se 1 (by rfl) ⟨1162241, by rfl⟩ : syracuseStep 1549655 = 2324483) B2324483
theorem B1746265 : Blo 1032607 1746265 := bstep (se 2 (by rfl) ⟨654849, by rfl⟩ : syracuseStep 1746265 = 1309699) B1309699
theorem B1549721 : Blo 1032607 1549721 := bstep (se 2 (by rfl) ⟨581145, by rfl⟩ : syracuseStep 1549721 = 1162291) B1162291
theorem B1549835 : Blo 1032607 1549835 := bstep (se 1 (by rfl) ⟨1162376, by rfl⟩ : syracuseStep 1549835 = 2324753) B2324753
theorem B1549847 : Blo 1032607 1549847 := bstep (se 1 (by rfl) ⟨1162385, by rfl⟩ : syracuseStep 1549847 = 2324771) B2324771
theorem B1549913 : Blo 1032607 1549913 := bstep (se 2 (by rfl) ⟨581217, by rfl⟩ : syracuseStep 1549913 = 1162435) B1162435
theorem B1550027 : Blo 1032607 1550027 := bstep (se 1 (by rfl) ⟨1162520, by rfl⟩ : syracuseStep 1550027 = 2325041) B2325041
theorem B1550039 : Blo 1032607 1550039 := bstep (se 1 (by rfl) ⟨1162529, by rfl⟩ : syracuseStep 1550039 = 2325059) B2325059
theorem B1550105 : Blo 1032607 1550105 := bstep (se 2 (by rfl) ⟨581289, by rfl⟩ : syracuseStep 1550105 = 1162579) B1162579
theorem B1550219 : Blo 1032607 1550219 := bstep (se 1 (by rfl) ⟨1162664, by rfl⟩ : syracuseStep 1550219 = 2325329) B2325329
theorem B1550231 : Blo 1032607 1550231 := bstep (se 1 (by rfl) ⟨1162673, by rfl⟩ : syracuseStep 1550231 = 2325347) B2325347
theorem B1746839 : Blo 1032607 1746839 := bstep (se 1 (by rfl) ⟨1310129, by rfl⟩ : syracuseStep 1746839 = 2620259) B2620259
theorem B1550297 : Blo 1032607 1550297 := bstep (se 2 (by rfl) ⟨581361, by rfl⟩ : syracuseStep 1550297 = 1162723) B1162723
theorem B1746967 : Blo 1032607 1746967 := bstep (se 1 (by rfl) ⟨1310225, by rfl⟩ : syracuseStep 1746967 = 2620451) B2620451
theorem B20129867 : Blo 1032607 20129867 := bstep (se 1 (by rfl) ⟨15097400, by rfl⟩ : syracuseStep 20129867 = 30194801) B30194801
theorem B1550411 : Blo 1032607 1550411 := bstep (se 1 (by rfl) ⟨1162808, by rfl⟩ : syracuseStep 1550411 = 2325617) B2325617
theorem B1550423 : Blo 1032607 1550423 := bstep (se 1 (by rfl) ⟨1162817, by rfl⟩ : syracuseStep 1550423 = 2325635) B2325635
theorem B1550489 : Blo 1032607 1550489 := bstep (se 2 (by rfl) ⟨581433, by rfl⟩ : syracuseStep 1550489 = 1162867) B1162867
theorem B1550603 : Blo 1032607 1550603 := bstep (se 1 (by rfl) ⟨1162952, by rfl⟩ : syracuseStep 1550603 = 2325905) B2325905
theorem B1550615 : Blo 1032607 1550615 := bstep (se 1 (by rfl) ⟨1162961, by rfl⟩ : syracuseStep 1550615 = 2325923) B2325923
theorem B1550681 : Blo 1032607 1550681 := bstep (se 2 (by rfl) ⟨581505, by rfl⟩ : syracuseStep 1550681 = 1163011) B1163011
theorem B1550795 : Blo 1032607 1550795 := bstep (se 1 (by rfl) ⟨1163096, by rfl⟩ : syracuseStep 1550795 = 2326193) B2326193
theorem B1550807 : Blo 1032607 1550807 := bstep (se 1 (by rfl) ⟨1163105, by rfl⟩ : syracuseStep 1550807 = 2326211) B2326211
theorem B1550873 : Blo 1032607 1550873 := bstep (se 2 (by rfl) ⟨581577, by rfl⟩ : syracuseStep 1550873 = 1163155) B1163155
theorem B2206273 : Blo 1032607 2206273 := bstep (se 2 (by rfl) ⟨827352, by rfl⟩ : syracuseStep 2206273 = 1654705) B1654705
theorem B1747595 : Blo 1032607 1747595 := bstep (se 1 (by rfl) ⟨1310696, by rfl⟩ : syracuseStep 1747595 = 2621393) B2621393
theorem B1550987 : Blo 1032607 1550987 := bstep (se 1 (by rfl) ⟨1163240, by rfl⟩ : syracuseStep 1550987 = 2326481) B2326481
theorem B1550999 : Blo 1032607 1550999 := bstep (se 1 (by rfl) ⟨1163249, by rfl⟩ : syracuseStep 1550999 = 2326499) B2326499
theorem B1551065 : Blo 1032607 1551065 := bstep (se 2 (by rfl) ⟨581649, by rfl⟩ : syracuseStep 1551065 = 1163299) B1163299
theorem B1747723 : Blo 1032607 1747723 := bstep (se 1 (by rfl) ⟨1310792, by rfl⟩ : syracuseStep 1747723 = 2621585) B2621585
theorem B1551179 : Blo 1032607 1551179 := bstep (se 1 (by rfl) ⟨1163384, by rfl⟩ : syracuseStep 1551179 = 2326769) B2326769
theorem B1551191 : Blo 1032607 1551191 := bstep (se 1 (by rfl) ⟨1163393, by rfl⟩ : syracuseStep 1551191 = 2326787) B2326787
theorem B2206615 : Blo 1032607 2206615 := bstep (se 1 (by rfl) ⟨1654961, by rfl⟩ : syracuseStep 2206615 = 3309923) B3309923
theorem B1551257 : Blo 1032607 1551257 := bstep (se 2 (by rfl) ⟨581721, by rfl⟩ : syracuseStep 1551257 = 1163443) B1163443
theorem B1747865 : Blo 1032607 1747865 := bstep (se 2 (by rfl) ⟨655449, by rfl⟩ : syracuseStep 1747865 = 1310899) B1310899
theorem B12561331 : Blo 1032607 12561331 := bstep (se 1 (by rfl) ⟨9420998, by rfl⟩ : syracuseStep 12561331 = 18841997) B18841997
theorem B1551371 : Blo 1032607 1551371 := bstep (se 1 (by rfl) ⟨1163528, by rfl⟩ : syracuseStep 1551371 = 2327057) B2327057
theorem B1551383 : Blo 1032607 1551383 := bstep (se 1 (by rfl) ⟨1163537, by rfl⟩ : syracuseStep 1551383 = 2327075) B2327075
theorem B1747993 : Blo 1032607 1747993 := bstep (se 2 (by rfl) ⟨655497, by rfl⟩ : syracuseStep 1747993 = 1310995) B1310995
theorem B1551449 : Blo 1032607 1551449 := bstep (se 2 (by rfl) ⟨581793, by rfl⟩ : syracuseStep 1551449 = 1163587) B1163587
theorem B1551563 : Blo 1032607 1551563 := bstep (se 1 (by rfl) ⟨1163672, by rfl⟩ : syracuseStep 1551563 = 2327345) B2327345
theorem B1682635 : Blo 1032607 1682635 := bstep (se 1 (by rfl) ⟨1261976, by rfl⟩ : syracuseStep 1682635 = 2523953) B2523953
theorem B1551575 : Blo 1032607 1551575 := bstep (se 1 (by rfl) ⟨1163681, by rfl⟩ : syracuseStep 1551575 = 2327363) B2327363
theorem B1551641 : Blo 1032607 1551641 := bstep (se 2 (by rfl) ⟨581865, by rfl⟩ : syracuseStep 1551641 = 1163731) B1163731
theorem B1551755 : Blo 1032607 1551755 := bstep (se 1 (by rfl) ⟨1163816, by rfl⟩ : syracuseStep 1551755 = 2327633) B2327633
theorem B1551767 : Blo 1032607 1551767 := bstep (se 1 (by rfl) ⟨1163825, by rfl⟩ : syracuseStep 1551767 = 2327651) B2327651
theorem B2207179 : Blo 1032607 2207179 := bstep (se 1 (by rfl) ⟨1655384, by rfl⟩ : syracuseStep 2207179 = 3310769) B3310769
theorem B1551833 : Blo 1032607 1551833 := bstep (se 2 (by rfl) ⟨581937, by rfl⟩ : syracuseStep 1551833 = 1163875) B1163875
theorem B1551947 : Blo 1032607 1551947 := bstep (se 1 (by rfl) ⟨1163960, by rfl⟩ : syracuseStep 1551947 = 2327921) B2327921
theorem B1551959 : Blo 1032607 1551959 := bstep (se 1 (by rfl) ⟨1163969, by rfl⟩ : syracuseStep 1551959 = 2327939) B2327939
theorem B1748567 : Blo 1032607 1748567 := bstep (se 1 (by rfl) ⟨1311425, by rfl⟩ : syracuseStep 1748567 = 2622851) B2622851
theorem B10628759 : Blo 1032607 10628759 := bstep (se 1 (by rfl) ⟨7971569, by rfl⟩ : syracuseStep 10628759 = 15943139) B15943139
theorem B1552025 : Blo 1032607 1552025 := bstep (se 2 (by rfl) ⟨582009, by rfl⟩ : syracuseStep 1552025 = 1164019) B1164019
theorem B1748695 : Blo 1032607 1748695 := bstep (se 1 (by rfl) ⟨1311521, by rfl⟩ : syracuseStep 1748695 = 2623043) B2623043
theorem B1552139 : Blo 1032607 1552139 := bstep (se 1 (by rfl) ⟨1164104, by rfl⟩ : syracuseStep 1552139 = 2328209) B2328209
theorem B1552151 : Blo 1032607 1552151 := bstep (se 1 (by rfl) ⟨1164113, by rfl⟩ : syracuseStep 1552151 = 2328227) B2328227
theorem B1552217 : Blo 1032607 1552217 := bstep (se 2 (by rfl) ⟨582081, by rfl⟩ : syracuseStep 1552217 = 1164163) B1164163
theorem B3485591 : Blo 1032607 3485591 := bstep (se 1 (by rfl) ⟨2614193, by rfl⟩ : syracuseStep 3485591 = 5228387) B5228387
theorem B14135219 : Blo 1032607 14135219 := bstep (se 1 (by rfl) ⟨10601414, by rfl⟩ : syracuseStep 14135219 = 21202829) B21202829
theorem B2797505 : Blo 1032607 2797505 := bstep (se 2 (by rfl) ⟨1049064, by rfl⟩ : syracuseStep 2797505 = 2098129) B2098129
theorem B1552331 : Blo 1032607 1552331 := bstep (se 1 (by rfl) ⟨1164248, by rfl⟩ : syracuseStep 1552331 = 2328497) B2328497
theorem B1552343 : Blo 1032607 1552343 := bstep (se 1 (by rfl) ⟨1164257, by rfl⟩ : syracuseStep 1552343 = 2328515) B2328515
theorem B1552409 : Blo 1032607 1552409 := bstep (se 2 (by rfl) ⟨582153, by rfl⟩ : syracuseStep 1552409 = 1164307) B1164307
theorem B1552523 : Blo 1032607 1552523 := bstep (se 1 (by rfl) ⟨1164392, by rfl⟩ : syracuseStep 1552523 = 2328785) B2328785
theorem B1552535 : Blo 1032607 1552535 := bstep (se 1 (by rfl) ⟨1164401, by rfl⟩ : syracuseStep 1552535 = 2328803) B2328803
theorem B1552601 : Blo 1032607 1552601 := bstep (se 2 (by rfl) ⟨582225, by rfl⟩ : syracuseStep 1552601 = 1164451) B1164451
theorem B1552715 : Blo 1032607 1552715 := bstep (se 1 (by rfl) ⟨1164536, by rfl⟩ : syracuseStep 1552715 = 2329073) B2329073
theorem B1552727 : Blo 1032607 1552727 := bstep (se 1 (by rfl) ⟨1164545, by rfl⟩ : syracuseStep 1552727 = 2329091) B2329091
theorem B1552793 : Blo 1032607 1552793 := bstep (se 2 (by rfl) ⟨582297, by rfl⟩ : syracuseStep 1552793 = 1164595) B1164595
theorem B3486131 : Blo 1032607 3486131 := bstep (se 1 (by rfl) ⟨2614598, by rfl⟩ : syracuseStep 3486131 = 5229197) B5229197
theorem B2240947 : Blo 1032607 2240947 := bstep (se 1 (by rfl) ⟨1680710, by rfl⟩ : syracuseStep 2240947 = 3361421) B3361421
theorem B1552907 : Blo 1032607 1552907 := bstep (se 1 (by rfl) ⟨1164680, by rfl⟩ : syracuseStep 1552907 = 2329361) B2329361
theorem B1552919 : Blo 1032607 1552919 := bstep (se 1 (by rfl) ⟨1164689, by rfl⟩ : syracuseStep 1552919 = 2329379) B2329379
theorem B18133579 : Blo 1032607 18133579 := bstep (se 1 (by rfl) ⟨13600184, by rfl⟩ : syracuseStep 18133579 = 27200369) B27200369
theorem B1552985 : Blo 1032607 1552985 := bstep (se 2 (by rfl) ⟨582369, by rfl⟩ : syracuseStep 1552985 = 1164739) B1164739
theorem B3486401 : Blo 1032607 3486401 := bstep (se 2 (by rfl) ⟨1307400, by rfl⟩ : syracuseStep 3486401 = 2614801) B2614801
theorem B1553099 : Blo 1032607 1553099 := bstep (se 1 (by rfl) ⟨1164824, by rfl⟩ : syracuseStep 1553099 = 2329649) B2329649
theorem B1553111 : Blo 1032607 1553111 := bstep (se 1 (by rfl) ⟨1164833, by rfl⟩ : syracuseStep 1553111 = 2329667) B2329667
theorem B28357361 : Blo 1032607 28357361 := bstep (se 2 (by rfl) ⟨10634010, by rfl⟩ : syracuseStep 28357361 = 21268021) B21268021
theorem B1553177 : Blo 1032607 1553177 := bstep (se 2 (by rfl) ⟨582441, by rfl⟩ : syracuseStep 1553177 = 1164883) B1164883
theorem B2208563 : Blo 1032607 2208563 := bstep (se 1 (by rfl) ⟨1656422, by rfl⟩ : syracuseStep 2208563 = 3312845) B3312845
theorem B1553291 : Blo 1032607 1553291 := bstep (se 1 (by rfl) ⟨1164968, by rfl⟩ : syracuseStep 1553291 = 2329937) B2329937
theorem B1553303 : Blo 1032607 1553303 := bstep (se 1 (by rfl) ⟨1164977, by rfl⟩ : syracuseStep 1553303 = 2329955) B2329955
theorem B2208665 : Blo 1032607 2208665 := bstep (se 2 (by rfl) ⟨828249, by rfl⟩ : syracuseStep 2208665 = 1656499) B1656499
theorem B8827825 : Blo 1032607 8827825 := bstep (se 2 (by rfl) ⟨3310434, by rfl⟩ : syracuseStep 8827825 = 6620869) B6620869
theorem B1553369 : Blo 1032607 1553369 := bstep (se 2 (by rfl) ⟨582513, by rfl⟩ : syracuseStep 1553369 = 1165027) B1165027
theorem B17675333 : Blo 1032607 17675333 := bstep (se 4 (by rfl) ⟨1657062, by rfl⟩ : syracuseStep 17675333 = 3314125) B3314125
theorem B1553483 : Blo 1032607 1553483 := bstep (se 1 (by rfl) ⟨1165112, by rfl⟩ : syracuseStep 1553483 = 2330225) B2330225
theorem B1553495 : Blo 1032607 1553495 := bstep (se 1 (by rfl) ⟨1165121, by rfl⟩ : syracuseStep 1553495 = 2330243) B2330243
theorem B1553561 : Blo 1032607 1553561 := bstep (se 2 (by rfl) ⟨582585, by rfl⟩ : syracuseStep 1553561 = 1165171) B1165171
theorem B3486941 : Blo 1032607 3486941 := bstep (se 3 (by rfl) ⟨653801, by rfl⟩ : syracuseStep 3486941 = 1307603) B1307603
theorem B2209025 : Blo 1032607 2209025 := bstep (se 2 (by rfl) ⟨828384, by rfl⟩ : syracuseStep 2209025 = 1656769) B1656769
theorem B1553675 : Blo 1032607 1553675 := bstep (se 1 (by rfl) ⟨1165256, by rfl⟩ : syracuseStep 1553675 = 2330513) B2330513
theorem B1553687 : Blo 1032607 1553687 := bstep (se 1 (by rfl) ⟨1165265, by rfl⟩ : syracuseStep 1553687 = 2330531) B2330531
theorem B1553753 : Blo 1032607 1553753 := bstep (se 2 (by rfl) ⟨582657, by rfl⟩ : syracuseStep 1553753 = 1165315) B1165315
theorem B2798999 : Blo 1032607 2798999 := bstep (se 1 (by rfl) ⟨2099249, by rfl⟩ : syracuseStep 2798999 = 4198499) B4198499
theorem B1553867 : Blo 1032607 1553867 := bstep (se 1 (by rfl) ⟨1165400, by rfl⟩ : syracuseStep 1553867 = 2330801) B2330801
theorem B1553879 : Blo 1032607 1553879 := bstep (se 1 (by rfl) ⟨1165409, by rfl⟩ : syracuseStep 1553879 = 2330819) B2330819
theorem B1553945 : Blo 1032607 1553945 := bstep (se 2 (by rfl) ⟨582729, by rfl⟩ : syracuseStep 1553945 = 1165459) B1165459
theorem B2799193 : Blo 1032607 2799193 := bstep (se 2 (by rfl) ⟨1049697, by rfl⟩ : syracuseStep 2799193 = 2099395) B2099395
theorem B1554059 : Blo 1032607 1554059 := bstep (se 1 (by rfl) ⟨1165544, by rfl⟩ : syracuseStep 1554059 = 2331089) B2331089
theorem B1554071 : Blo 1032607 1554071 := bstep (se 1 (by rfl) ⟨1165553, by rfl⟩ : syracuseStep 1554071 = 2331107) B2331107
theorem B1554137 : Blo 1032607 1554137 := bstep (se 2 (by rfl) ⟨582801, by rfl⟩ : syracuseStep 1554137 = 1165603) B1165603
theorem B1554251 : Blo 1032607 1554251 := bstep (se 1 (by rfl) ⟨1165688, by rfl⟩ : syracuseStep 1554251 = 2331377) B2331377
theorem B1554263 : Blo 1032607 1554263 := bstep (se 1 (by rfl) ⟨1165697, by rfl⟩ : syracuseStep 1554263 = 2331395) B2331395
theorem B1554329 : Blo 1032607 1554329 := bstep (se 2 (by rfl) ⟨582873, by rfl⟩ : syracuseStep 1554329 = 1165747) B1165747
theorem B2209751 : Blo 1032607 2209751 := bstep (se 1 (by rfl) ⟨1657313, by rfl⟩ : syracuseStep 2209751 = 3314627) B3314627
theorem B35796953 : Blo 1032607 35796953 := bstep (se 2 (by rfl) ⟨13423857, by rfl⟩ : syracuseStep 35796953 = 26847715) B26847715
theorem B1554443 : Blo 1032607 1554443 := bstep (se 1 (by rfl) ⟨1165832, by rfl⟩ : syracuseStep 1554443 = 2331665) B2331665
theorem B1554455 : Blo 1032607 1554455 := bstep (se 1 (by rfl) ⟨1165841, by rfl⟩ : syracuseStep 1554455 = 2331683) B2331683
theorem B1554521 : Blo 1032607 1554521 := bstep (se 2 (by rfl) ⟨582945, by rfl⟩ : syracuseStep 1554521 = 1165891) B1165891
theorem B1554635 : Blo 1032607 1554635 := bstep (se 1 (by rfl) ⟨1165976, by rfl⟩ : syracuseStep 1554635 = 2331953) B2331953
theorem B1554647 : Blo 1032607 1554647 := bstep (se 1 (by rfl) ⟨1165985, by rfl⟩ : syracuseStep 1554647 = 2331971) B2331971
theorem B1554713 : Blo 1032607 1554713 := bstep (se 2 (by rfl) ⟨583017, by rfl⟩ : syracuseStep 1554713 = 1166035) B1166035
theorem B3488075 : Blo 1032607 3488075 := bstep (se 1 (by rfl) ⟨2616056, by rfl⟩ : syracuseStep 3488075 = 5232113) B5232113
theorem B16791907 : Blo 1032607 16791907 := bstep (se 1 (by rfl) ⟨12593930, by rfl⟩ : syracuseStep 16791907 = 25187861) B25187861
theorem B1554827 : Blo 1032607 1554827 := bstep (se 1 (by rfl) ⟨1166120, by rfl⟩ : syracuseStep 1554827 = 2332241) B2332241
theorem B1554839 : Blo 1032607 1554839 := bstep (se 1 (by rfl) ⟨1166129, by rfl⟩ : syracuseStep 1554839 = 2332259) B2332259
theorem B1554905 : Blo 1032607 1554905 := bstep (se 2 (by rfl) ⟨583089, by rfl⟩ : syracuseStep 1554905 = 1166179) B1166179
theorem B1161751 : Blo 1032607 1161751 := bstep (se 1 (by rfl) ⟨871313, by rfl⟩ : syracuseStep 1161751 = 1742627) B1742627
theorem B3488345 : Blo 1032607 3488345 := bstep (se 2 (by rfl) ⟨1308129, by rfl⟩ : syracuseStep 3488345 = 2616259) B2616259
theorem B1161931 : Blo 1032607 1161931 := bstep (se 1 (by rfl) ⟨871448, by rfl⟩ : syracuseStep 1161931 = 1742897) B1742897
theorem B9550541 : Blo 1032607 9550541 := bstep (se 3 (by rfl) ⟨1790726, by rfl⟩ : syracuseStep 9550541 = 3581453) B3581453
theorem B1162039 : Blo 1032607 1162039 := bstep (se 1 (by rfl) ⟨871529, by rfl⟩ : syracuseStep 1162039 = 1743059) B1743059
theorem B2210647 : Blo 1032607 2210647 := bstep (se 1 (by rfl) ⟨1657985, by rfl⟩ : syracuseStep 2210647 = 3315971) B3315971
theorem B1162219 : Blo 1032607 1162219 := bstep (se 1 (by rfl) ⟨871664, by rfl⟩ : syracuseStep 1162219 = 1743329) B1743329
theorem B30293027 : Blo 1032607 30293027 := bstep (se 1 (by rfl) ⟨22719770, by rfl⟩ : syracuseStep 30293027 = 45439541) B45439541
theorem B1162327 : Blo 1032607 1162327 := bstep (se 1 (by rfl) ⟨871745, by rfl⟩ : syracuseStep 1162327 = 1743491) B1743491
theorem B16792757 : Blo 1032607 16792757 := bstep (se 5 (by rfl) ⟨787160, by rfl⟩ : syracuseStep 16792757 = 1574321) B1574321
theorem B1162507 : Blo 1032607 1162507 := bstep (se 1 (by rfl) ⟨871880, by rfl⟩ : syracuseStep 1162507 = 1743761) B1743761
theorem B3489047 : Blo 1032607 3489047 := bstep (se 1 (by rfl) ⟨2616785, by rfl⟩ : syracuseStep 3489047 = 5233571) B5233571
theorem B1162615 : Blo 1032607 1162615 := bstep (se 1 (by rfl) ⟨871961, by rfl⟩ : syracuseStep 1162615 = 1743923) B1743923
theorem B7847441 : Blo 1032607 7847441 := bstep (se 2 (by rfl) ⟨2942790, by rfl⟩ : syracuseStep 7847441 = 5885581) B5885581
theorem B1162795 : Blo 1032607 1162795 := bstep (se 1 (by rfl) ⟨872096, by rfl⟩ : syracuseStep 1162795 = 1744193) B1744193
theorem B5586533 : Blo 1032607 5586533 := bstep (se 4 (by rfl) ⟨523737, by rfl⟩ : syracuseStep 5586533 = 1047475) B1047475
theorem B2211467 : Blo 1032607 2211467 := bstep (se 1 (by rfl) ⟨1658600, by rfl⟩ : syracuseStep 2211467 = 3317201) B3317201
theorem B1162903 : Blo 1032607 1162903 := bstep (se 1 (by rfl) ⟨872177, by rfl⟩ : syracuseStep 1162903 = 1744355) B1744355
theorem B3489587 : Blo 1032607 3489587 := bstep (se 1 (by rfl) ⟨2617190, by rfl⟩ : syracuseStep 3489587 = 5234381) B5234381
theorem B1163083 : Blo 1032607 1163083 := bstep (se 1 (by rfl) ⟨872312, by rfl⟩ : syracuseStep 1163083 = 1744625) B1744625
theorem B1163191 : Blo 1032607 1163191 := bstep (se 1 (by rfl) ⟨872393, by rfl⟩ : syracuseStep 1163191 = 1744787) B1744787
theorem B3489857 : Blo 1032607 3489857 := bstep (se 2 (by rfl) ⟨1308696, by rfl⟩ : syracuseStep 3489857 = 2617393) B2617393
theorem B1654859 : Blo 1032607 1654859 := bstep (se 1 (by rfl) ⟨1241144, by rfl⟩ : syracuseStep 1654859 = 2482289) B2482289
theorem B1163371 : Blo 1032607 1163371 := bstep (se 1 (by rfl) ⟨872528, by rfl⟩ : syracuseStep 1163371 = 1745057) B1745057
theorem B1654987 : Blo 1032607 1654987 := bstep (se 1 (by rfl) ⟨1241240, by rfl⟩ : syracuseStep 1654987 = 2482481) B2482481
theorem B1163479 : Blo 1032607 1163479 := bstep (se 1 (by rfl) ⟨872609, by rfl⟩ : syracuseStep 1163479 = 1745219) B1745219
theorem B1327435 : Blo 1032607 1327435 := bstep (se 1 (by rfl) ⟨995576, by rfl⟩ : syracuseStep 1327435 = 1991153) B1991153
theorem B1655129 : Blo 1032607 1655129 := bstep (se 2 (by rfl) ⟨620673, by rfl⟩ : syracuseStep 1655129 = 1241347) B1241347
theorem B2212211 : Blo 1032607 2212211 := bstep (se 1 (by rfl) ⟨1659158, by rfl⟩ : syracuseStep 2212211 = 3318317) B3318317
theorem B1163659 : Blo 1032607 1163659 := bstep (se 1 (by rfl) ⟨872744, by rfl⟩ : syracuseStep 1163659 = 1745489) B1745489
theorem B1032619 : Blo 1032607 1032619 := bstep (se 1 (by rfl) ⟨774464, by rfl⟩ : syracuseStep 1032619 = 1548929) B1548929
theorem B1032631 : Blo 1032607 1032631 := bstep (se 1 (by rfl) ⟨774473, by rfl⟩ : syracuseStep 1032631 = 1548947) B1548947
theorem B1032651 : Blo 1032607 1032651 := bstep (se 1 (by rfl) ⟨774488, by rfl⟩ : syracuseStep 1032651 = 1548977) B1548977
theorem B1032663 : Blo 1032607 1032663 := bstep (se 1 (by rfl) ⟨774497, by rfl⟩ : syracuseStep 1032663 = 1548995) B1548995
theorem B1032683 : Blo 1032607 1032683 := bstep (se 1 (by rfl) ⟨774512, by rfl⟩ : syracuseStep 1032683 = 1549025) B1549025
theorem B1032695 : Blo 1032607 1032695 := bstep (se 1 (by rfl) ⟨774521, by rfl⟩ : syracuseStep 1032695 = 1549043) B1549043
theorem B1163767 : Blo 1032607 1163767 := bstep (se 1 (by rfl) ⟨872825, by rfl⟩ : syracuseStep 1163767 = 1745651) B1745651
theorem B1032715 : Blo 1032607 1032715 := bstep (se 1 (by rfl) ⟨774536, by rfl⟩ : syracuseStep 1032715 = 1549073) B1549073
theorem B1032727 : Blo 1032607 1032727 := bstep (se 1 (by rfl) ⟨774545, by rfl⟩ : syracuseStep 1032727 = 1549091) B1549091
theorem B1032747 : Blo 1032607 1032747 := bstep (se 1 (by rfl) ⟨774560, by rfl⟩ : syracuseStep 1032747 = 1549121) B1549121
theorem B1032759 : Blo 1032607 1032759 := bstep (se 1 (by rfl) ⟨774569, by rfl⟩ : syracuseStep 1032759 = 1549139) B1549139
theorem B1032779 : Blo 1032607 1032779 := bstep (se 1 (by rfl) ⟨774584, by rfl⟩ : syracuseStep 1032779 = 1549169) B1549169
theorem B1032791 : Blo 1032607 1032791 := bstep (se 1 (by rfl) ⟨774593, by rfl⟩ : syracuseStep 1032791 = 1549187) B1549187
theorem B3490397 : Blo 1032607 3490397 := bstep (se 3 (by rfl) ⟨654449, by rfl⟩ : syracuseStep 3490397 = 1308899) B1308899
theorem B1032811 : Blo 1032607 1032811 := bstep (se 1 (by rfl) ⟨774608, by rfl⟩ : syracuseStep 1032811 = 1549217) B1549217
theorem B1032823 : Blo 1032607 1032823 := bstep (se 1 (by rfl) ⟨774617, by rfl⟩ : syracuseStep 1032823 = 1549235) B1549235
theorem B29803139 : Blo 1032607 29803139 := bstep (se 1 (by rfl) ⟨22352354, by rfl⟩ : syracuseStep 29803139 = 44704709) B44704709
theorem B1032843 : Blo 1032607 1032843 := bstep (se 1 (by rfl) ⟨774632, by rfl⟩ : syracuseStep 1032843 = 1549265) B1549265
theorem B1032855 : Blo 1032607 1032855 := bstep (se 1 (by rfl) ⟨774641, by rfl⟩ : syracuseStep 1032855 = 1549283) B1549283
theorem B1032875 : Blo 1032607 1032875 := bstep (se 1 (by rfl) ⟨774656, by rfl⟩ : syracuseStep 1032875 = 1549313) B1549313
theorem B1163947 : Blo 1032607 1163947 := bstep (se 1 (by rfl) ⟨872960, by rfl⟩ : syracuseStep 1163947 = 1745921) B1745921
theorem B1032887 : Blo 1032607 1032887 := bstep (se 1 (by rfl) ⟨774665, by rfl⟩ : syracuseStep 1032887 = 1549331) B1549331
theorem B1032907 : Blo 1032607 1032907 := bstep (se 1 (by rfl) ⟨774680, by rfl⟩ : syracuseStep 1032907 = 1549361) B1549361
theorem B1032919 : Blo 1032607 1032919 := bstep (se 1 (by rfl) ⟨774689, by rfl⟩ : syracuseStep 1032919 = 1549379) B1549379
theorem B1032939 : Blo 1032607 1032939 := bstep (se 1 (by rfl) ⟨774704, by rfl⟩ : syracuseStep 1032939 = 1549409) B1549409
theorem B1032951 : Blo 1032607 1032951 := bstep (se 1 (by rfl) ⟨774713, by rfl⟩ : syracuseStep 1032951 = 1549427) B1549427
theorem B1032971 : Blo 1032607 1032971 := bstep (se 1 (by rfl) ⟨774728, by rfl⟩ : syracuseStep 1032971 = 1549457) B1549457
theorem B1032983 : Blo 1032607 1032983 := bstep (se 1 (by rfl) ⟨774737, by rfl⟩ : syracuseStep 1032983 = 1549475) B1549475
theorem B1164055 : Blo 1032607 1164055 := bstep (se 1 (by rfl) ⟨873041, by rfl⟩ : syracuseStep 1164055 = 1746083) B1746083
theorem B1033003 : Blo 1032607 1033003 := bstep (se 1 (by rfl) ⟨774752, by rfl⟩ : syracuseStep 1033003 = 1549505) B1549505
theorem B1033015 : Blo 1032607 1033015 := bstep (se 1 (by rfl) ⟨774761, by rfl⟩ : syracuseStep 1033015 = 1549523) B1549523
theorem B1033035 : Blo 1032607 1033035 := bstep (se 1 (by rfl) ⟨774776, by rfl⟩ : syracuseStep 1033035 = 1549553) B1549553
theorem B1033047 : Blo 1032607 1033047 := bstep (se 1 (by rfl) ⟨774785, by rfl⟩ : syracuseStep 1033047 = 1549571) B1549571
theorem B1033067 : Blo 1032607 1033067 := bstep (se 1 (by rfl) ⟨774800, by rfl⟩ : syracuseStep 1033067 = 1549601) B1549601
theorem B1033079 : Blo 1032607 1033079 := bstep (se 1 (by rfl) ⟨774809, by rfl⟩ : syracuseStep 1033079 = 1549619) B1549619
theorem B1033099 : Blo 1032607 1033099 := bstep (se 1 (by rfl) ⟨774824, by rfl⟩ : syracuseStep 1033099 = 1549649) B1549649
theorem B1033111 : Blo 1032607 1033111 := bstep (se 1 (by rfl) ⟨774833, by rfl⟩ : syracuseStep 1033111 = 1549667) B1549667
theorem B1033131 : Blo 1032607 1033131 := bstep (se 1 (by rfl) ⟨774848, by rfl⟩ : syracuseStep 1033131 = 1549697) B1549697
theorem B1033143 : Blo 1032607 1033143 := bstep (se 1 (by rfl) ⟨774857, by rfl⟩ : syracuseStep 1033143 = 1549715) B1549715
theorem B1033163 : Blo 1032607 1033163 := bstep (se 1 (by rfl) ⟨774872, by rfl⟩ : syracuseStep 1033163 = 1549745) B1549745
theorem B1164235 : Blo 1032607 1164235 := bstep (se 1 (by rfl) ⟨873176, by rfl⟩ : syracuseStep 1164235 = 1746353) B1746353
theorem B1033175 : Blo 1032607 1033175 := bstep (se 1 (by rfl) ⟨774881, by rfl⟩ : syracuseStep 1033175 = 1549763) B1549763
theorem B1033195 : Blo 1032607 1033195 := bstep (se 1 (by rfl) ⟨774896, by rfl⟩ : syracuseStep 1033195 = 1549793) B1549793
theorem B1033207 : Blo 1032607 1033207 := bstep (se 1 (by rfl) ⟨774905, by rfl⟩ : syracuseStep 1033207 = 1549811) B1549811
theorem B1033227 : Blo 1032607 1033227 := bstep (se 1 (by rfl) ⟨774920, by rfl⟩ : syracuseStep 1033227 = 1549841) B1549841
theorem B1033239 : Blo 1032607 1033239 := bstep (se 1 (by rfl) ⟨774929, by rfl⟩ : syracuseStep 1033239 = 1549859) B1549859
theorem B25150499 : Blo 1032607 25150499 := bstep (se 1 (by rfl) ⟨18862874, by rfl⟩ : syracuseStep 25150499 = 37725749) B37725749
theorem B1033259 : Blo 1032607 1033259 := bstep (se 1 (by rfl) ⟨774944, by rfl⟩ : syracuseStep 1033259 = 1549889) B1549889
theorem B1164343 : Blo 1032607 1164343 := bstep (se 1 (by rfl) ⟨873257, by rfl⟩ : syracuseStep 1164343 = 1746515) B1746515
theorem B1033271 : Blo 1032607 1033271 := bstep (se 1 (by rfl) ⟨774953, by rfl⟩ : syracuseStep 1033271 = 1549907) B1549907
theorem B1033291 : Blo 1032607 1033291 := bstep (se 1 (by rfl) ⟨774968, by rfl⟩ : syracuseStep 1033291 = 1549937) B1549937
theorem B1033303 : Blo 1032607 1033303 := bstep (se 1 (by rfl) ⟨774977, by rfl⟩ : syracuseStep 1033303 = 1549955) B1549955
theorem B1033323 : Blo 1032607 1033323 := bstep (se 1 (by rfl) ⟨774992, by rfl⟩ : syracuseStep 1033323 = 1549985) B1549985
theorem B1033335 : Blo 1032607 1033335 := bstep (se 1 (by rfl) ⟨775001, by rfl⟩ : syracuseStep 1033335 = 1550003) B1550003
theorem B1033355 : Blo 1032607 1033355 := bstep (se 1 (by rfl) ⟨775016, by rfl⟩ : syracuseStep 1033355 = 1550033) B1550033
theorem B1033367 : Blo 1032607 1033367 := bstep (se 1 (by rfl) ⟨775025, by rfl⟩ : syracuseStep 1033367 = 1550051) B1550051
theorem B1033387 : Blo 1032607 1033387 := bstep (se 1 (by rfl) ⟨775040, by rfl⟩ : syracuseStep 1033387 = 1550081) B1550081
theorem B1033399 : Blo 1032607 1033399 := bstep (se 1 (by rfl) ⟨775049, by rfl⟩ : syracuseStep 1033399 = 1550099) B1550099
theorem B2213057 : Blo 1032607 2213057 := bstep (se 2 (by rfl) ⟨829896, by rfl⟩ : syracuseStep 2213057 = 1659793) B1659793
theorem B1033419 : Blo 1032607 1033419 := bstep (se 1 (by rfl) ⟨775064, by rfl⟩ : syracuseStep 1033419 = 1550129) B1550129
theorem B1033431 : Blo 1032607 1033431 := bstep (se 1 (by rfl) ⟨775073, by rfl⟩ : syracuseStep 1033431 = 1550147) B1550147
theorem B6636761 : Blo 1032607 6636761 := bstep (se 2 (by rfl) ⟨2488785, by rfl⟩ : syracuseStep 6636761 = 4977571) B4977571
theorem B1033451 : Blo 1032607 1033451 := bstep (se 1 (by rfl) ⟨775088, by rfl⟩ : syracuseStep 1033451 = 1550177) B1550177
theorem B1164523 : Blo 1032607 1164523 := bstep (se 1 (by rfl) ⟨873392, by rfl⟩ : syracuseStep 1164523 = 1746785) B1746785
theorem B1033463 : Blo 1032607 1033463 := bstep (se 1 (by rfl) ⟨775097, by rfl⟩ : syracuseStep 1033463 = 1550195) B1550195
theorem B1033483 : Blo 1032607 1033483 := bstep (se 1 (by rfl) ⟨775112, by rfl⟩ : syracuseStep 1033483 = 1550225) B1550225
theorem B1033495 : Blo 1032607 1033495 := bstep (se 1 (by rfl) ⟨775121, by rfl⟩ : syracuseStep 1033495 = 1550243) B1550243
theorem B1033515 : Blo 1032607 1033515 := bstep (se 1 (by rfl) ⟨775136, by rfl⟩ : syracuseStep 1033515 = 1550273) B1550273
theorem B1033527 : Blo 1032607 1033527 := bstep (se 1 (by rfl) ⟨775145, by rfl⟩ : syracuseStep 1033527 = 1550291) B1550291
theorem B1033547 : Blo 1032607 1033547 := bstep (se 1 (by rfl) ⟨775160, by rfl⟩ : syracuseStep 1033547 = 1550321) B1550321
theorem B1033559 : Blo 1032607 1033559 := bstep (se 1 (by rfl) ⟨775169, by rfl⟩ : syracuseStep 1033559 = 1550339) B1550339
theorem B1164631 : Blo 1032607 1164631 := bstep (se 1 (by rfl) ⟨873473, by rfl⟩ : syracuseStep 1164631 = 1746947) B1746947
theorem B1033579 : Blo 1032607 1033579 := bstep (se 1 (by rfl) ⟨775184, by rfl⟩ : syracuseStep 1033579 = 1550369) B1550369
theorem B1033591 : Blo 1032607 1033591 := bstep (se 1 (by rfl) ⟨775193, by rfl⟩ : syracuseStep 1033591 = 1550387) B1550387
theorem B1033611 : Blo 1032607 1033611 := bstep (se 1 (by rfl) ⟨775208, by rfl⟩ : syracuseStep 1033611 = 1550417) B1550417
theorem B1033623 : Blo 1032607 1033623 := bstep (se 1 (by rfl) ⟨775217, by rfl⟩ : syracuseStep 1033623 = 1550435) B1550435
theorem B7456151 : Blo 1032607 7456151 := bstep (se 1 (by rfl) ⟨5592113, by rfl⟩ : syracuseStep 7456151 = 11184227) B11184227
theorem B1656217 : Blo 1032607 1656217 := bstep (se 2 (by rfl) ⟨621081, by rfl⟩ : syracuseStep 1656217 = 1242163) B1242163
theorem B1033643 : Blo 1032607 1033643 := bstep (se 1 (by rfl) ⟨775232, by rfl⟩ : syracuseStep 1033643 = 1550465) B1550465
theorem B1033655 : Blo 1032607 1033655 := bstep (se 1 (by rfl) ⟨775241, by rfl⟩ : syracuseStep 1033655 = 1550483) B1550483
theorem B1033675 : Blo 1032607 1033675 := bstep (se 1 (by rfl) ⟨775256, by rfl⟩ : syracuseStep 1033675 = 1550513) B1550513
theorem B1033687 : Blo 1032607 1033687 := bstep (se 1 (by rfl) ⟨775265, by rfl⟩ : syracuseStep 1033687 = 1550531) B1550531
theorem B8832473 : Blo 1032607 8832473 := bstep (se 2 (by rfl) ⟨3312177, by rfl⟩ : syracuseStep 8832473 = 6624355) B6624355
theorem B1033707 : Blo 1032607 1033707 := bstep (se 1 (by rfl) ⟨775280, by rfl⟩ : syracuseStep 1033707 = 1550561) B1550561
theorem B1033719 : Blo 1032607 1033719 := bstep (se 1 (by rfl) ⟨775289, by rfl⟩ : syracuseStep 1033719 = 1550579) B1550579
theorem B1033739 : Blo 1032607 1033739 := bstep (se 1 (by rfl) ⟨775304, by rfl⟩ : syracuseStep 1033739 = 1550609) B1550609
theorem B1164811 : Blo 1032607 1164811 := bstep (se 1 (by rfl) ⟨873608, by rfl⟩ : syracuseStep 1164811 = 1747217) B1747217
theorem B32261645 : Blo 1032607 32261645 := bstep (se 3 (by rfl) ⟨6049058, by rfl⟩ : syracuseStep 32261645 = 12098117) B12098117
theorem B1033751 : Blo 1032607 1033751 := bstep (se 1 (by rfl) ⟨775313, by rfl⟩ : syracuseStep 1033751 = 1550627) B1550627
theorem B2213399 : Blo 1032607 2213399 := bstep (se 1 (by rfl) ⟨1660049, by rfl⟩ : syracuseStep 2213399 = 3320099) B3320099
theorem B1033771 : Blo 1032607 1033771 := bstep (se 1 (by rfl) ⟨775328, by rfl⟩ : syracuseStep 1033771 = 1550657) B1550657
theorem B1033783 : Blo 1032607 1033783 := bstep (se 1 (by rfl) ⟨775337, by rfl⟩ : syracuseStep 1033783 = 1550675) B1550675
theorem B1033803 : Blo 1032607 1033803 := bstep (se 1 (by rfl) ⟨775352, by rfl⟩ : syracuseStep 1033803 = 1550705) B1550705
theorem B1033815 : Blo 1032607 1033815 := bstep (se 1 (by rfl) ⟨775361, by rfl⟩ : syracuseStep 1033815 = 1550723) B1550723
theorem B1033835 : Blo 1032607 1033835 := bstep (se 1 (by rfl) ⟨775376, by rfl⟩ : syracuseStep 1033835 = 1550753) B1550753
theorem B1033847 : Blo 1032607 1033847 := bstep (se 1 (by rfl) ⟨775385, by rfl⟩ : syracuseStep 1033847 = 1550771) B1550771
theorem B1164919 : Blo 1032607 1164919 := bstep (se 1 (by rfl) ⟨873689, by rfl⟩ : syracuseStep 1164919 = 1747379) B1747379
theorem B1033867 : Blo 1032607 1033867 := bstep (se 1 (by rfl) ⟨775400, by rfl⟩ : syracuseStep 1033867 = 1550801) B1550801
theorem B1033879 : Blo 1032607 1033879 := bstep (se 1 (by rfl) ⟨775409, by rfl⟩ : syracuseStep 1033879 = 1550819) B1550819
theorem B1033899 : Blo 1032607 1033899 := bstep (se 1 (by rfl) ⟨775424, by rfl⟩ : syracuseStep 1033899 = 1550849) B1550849
theorem B1033911 : Blo 1032607 1033911 := bstep (se 1 (by rfl) ⟨775433, by rfl⟩ : syracuseStep 1033911 = 1550867) B1550867
theorem B1033931 : Blo 1032607 1033931 := bstep (se 1 (by rfl) ⟨775448, by rfl⟩ : syracuseStep 1033931 = 1550897) B1550897
theorem B3491531 : Blo 1032607 3491531 := bstep (se 1 (by rfl) ⟨2618648, by rfl⟩ : syracuseStep 3491531 = 5237297) B5237297
theorem B1033943 : Blo 1032607 1033943 := bstep (se 1 (by rfl) ⟨775457, by rfl⟩ : syracuseStep 1033943 = 1550915) B1550915
theorem B1033963 : Blo 1032607 1033963 := bstep (se 1 (by rfl) ⟨775472, by rfl⟩ : syracuseStep 1033963 = 1550945) B1550945
theorem B1033975 : Blo 1032607 1033975 := bstep (se 1 (by rfl) ⟨775481, by rfl⟩ : syracuseStep 1033975 = 1550963) B1550963
theorem B1033995 : Blo 1032607 1033995 := bstep (se 1 (by rfl) ⟨775496, by rfl⟩ : syracuseStep 1033995 = 1550993) B1550993
theorem B1034007 : Blo 1032607 1034007 := bstep (se 1 (by rfl) ⟨775505, by rfl⟩ : syracuseStep 1034007 = 1551011) B1551011
theorem B1034027 : Blo 1032607 1034027 := bstep (se 1 (by rfl) ⟨775520, by rfl⟩ : syracuseStep 1034027 = 1551041) B1551041
theorem B1165099 : Blo 1032607 1165099 := bstep (se 1 (by rfl) ⟨873824, by rfl⟩ : syracuseStep 1165099 = 1747649) B1747649
theorem B1034039 : Blo 1032607 1034039 := bstep (se 1 (by rfl) ⟨775529, by rfl⟩ : syracuseStep 1034039 = 1551059) B1551059
theorem B1034059 : Blo 1032607 1034059 := bstep (se 1 (by rfl) ⟨775544, by rfl⟩ : syracuseStep 1034059 = 1551089) B1551089
theorem B1034071 : Blo 1032607 1034071 := bstep (se 1 (by rfl) ⟨775553, by rfl⟩ : syracuseStep 1034071 = 1551107) B1551107
theorem B1034091 : Blo 1032607 1034091 := bstep (se 1 (by rfl) ⟨775568, by rfl⟩ : syracuseStep 1034091 = 1551137) B1551137
theorem B1034103 : Blo 1032607 1034103 := bstep (se 1 (by rfl) ⟨775577, by rfl⟩ : syracuseStep 1034103 = 1551155) B1551155
theorem B1034123 : Blo 1032607 1034123 := bstep (se 1 (by rfl) ⟨775592, by rfl⟩ : syracuseStep 1034123 = 1551185) B1551185
theorem B1034135 : Blo 1032607 1034135 := bstep (se 1 (by rfl) ⟨775601, by rfl⟩ : syracuseStep 1034135 = 1551203) B1551203
theorem B1165207 : Blo 1032607 1165207 := bstep (se 1 (by rfl) ⟨873905, by rfl⟩ : syracuseStep 1165207 = 1747811) B1747811
theorem B1034155 : Blo 1032607 1034155 := bstep (se 1 (by rfl) ⟨775616, by rfl⟩ : syracuseStep 1034155 = 1551233) B1551233
theorem B1034167 : Blo 1032607 1034167 := bstep (se 1 (by rfl) ⟨775625, by rfl⟩ : syracuseStep 1034167 = 1551251) B1551251
theorem B1034187 : Blo 1032607 1034187 := bstep (se 1 (by rfl) ⟨775640, by rfl⟩ : syracuseStep 1034187 = 1551281) B1551281
theorem B1034199 : Blo 1032607 1034199 := bstep (se 1 (by rfl) ⟨775649, by rfl⟩ : syracuseStep 1034199 = 1551299) B1551299
theorem B3491801 : Blo 1032607 3491801 := bstep (se 2 (by rfl) ⟨1309425, by rfl⟩ : syracuseStep 3491801 = 2618851) B2618851
theorem B1034219 : Blo 1032607 1034219 := bstep (se 1 (by rfl) ⟨775664, by rfl⟩ : syracuseStep 1034219 = 1551329) B1551329
theorem B1034231 : Blo 1032607 1034231 := bstep (se 1 (by rfl) ⟨775673, by rfl⟩ : syracuseStep 1034231 = 1551347) B1551347
theorem B1034251 : Blo 1032607 1034251 := bstep (se 1 (by rfl) ⟨775688, by rfl⟩ : syracuseStep 1034251 = 1551377) B1551377
theorem B1034263 : Blo 1032607 1034263 := bstep (se 1 (by rfl) ⟨775697, by rfl⟩ : syracuseStep 1034263 = 1551395) B1551395
theorem B1034283 : Blo 1032607 1034283 := bstep (se 1 (by rfl) ⟨775712, by rfl⟩ : syracuseStep 1034283 = 1551425) B1551425
theorem B1034295 : Blo 1032607 1034295 := bstep (se 1 (by rfl) ⟨775721, by rfl⟩ : syracuseStep 1034295 = 1551443) B1551443
theorem B1034315 : Blo 1032607 1034315 := bstep (se 1 (by rfl) ⟨775736, by rfl⟩ : syracuseStep 1034315 = 1551473) B1551473
theorem B1165387 : Blo 1032607 1165387 := bstep (se 1 (by rfl) ⟨874040, by rfl⟩ : syracuseStep 1165387 = 1748081) B1748081
theorem B1034327 : Blo 1032607 1034327 := bstep (se 1 (by rfl) ⟨775745, by rfl⟩ : syracuseStep 1034327 = 1551491) B1551491
theorem B1034347 : Blo 1032607 1034347 := bstep (se 1 (by rfl) ⟨775760, by rfl⟩ : syracuseStep 1034347 = 1551521) B1551521
theorem B1034359 : Blo 1032607 1034359 := bstep (se 1 (by rfl) ⟨775769, by rfl⟩ : syracuseStep 1034359 = 1551539) B1551539
theorem B1034379 : Blo 1032607 1034379 := bstep (se 1 (by rfl) ⟨775784, by rfl⟩ : syracuseStep 1034379 = 1551569) B1551569
theorem B1034391 : Blo 1032607 1034391 := bstep (se 1 (by rfl) ⟨775793, by rfl⟩ : syracuseStep 1034391 = 1551587) B1551587
theorem B1034411 : Blo 1032607 1034411 := bstep (se 1 (by rfl) ⟨775808, by rfl⟩ : syracuseStep 1034411 = 1551617) B1551617
theorem B1034423 : Blo 1032607 1034423 := bstep (se 1 (by rfl) ⟨775817, by rfl⟩ : syracuseStep 1034423 = 1551635) B1551635
theorem B1165495 : Blo 1032607 1165495 := bstep (se 1 (by rfl) ⟨874121, by rfl⟩ : syracuseStep 1165495 = 1748243) B1748243
theorem B1034443 : Blo 1032607 1034443 := bstep (se 1 (by rfl) ⟨775832, by rfl⟩ : syracuseStep 1034443 = 1551665) B1551665
theorem B1034455 : Blo 1032607 1034455 := bstep (se 1 (by rfl) ⟨775841, by rfl⟩ : syracuseStep 1034455 = 1551683) B1551683
theorem B1034475 : Blo 1032607 1034475 := bstep (se 1 (by rfl) ⟨775856, by rfl⟩ : syracuseStep 1034475 = 1551713) B1551713
theorem B1034487 : Blo 1032607 1034487 := bstep (se 1 (by rfl) ⟨775865, by rfl⟩ : syracuseStep 1034487 = 1551731) B1551731
theorem B1034507 : Blo 1032607 1034507 := bstep (se 1 (by rfl) ⟨775880, by rfl⟩ : syracuseStep 1034507 = 1551761) B1551761
theorem B1034519 : Blo 1032607 1034519 := bstep (se 1 (by rfl) ⟨775889, by rfl⟩ : syracuseStep 1034519 = 1551779) B1551779
theorem B1493273 : Blo 1032607 1493273 := bstep (se 2 (by rfl) ⟨559977, by rfl⟩ : syracuseStep 1493273 = 1119955) B1119955
theorem B1034539 : Blo 1032607 1034539 := bstep (se 1 (by rfl) ⟨775904, by rfl⟩ : syracuseStep 1034539 = 1551809) B1551809
theorem B1034551 : Blo 1032607 1034551 := bstep (se 1 (by rfl) ⟨775913, by rfl⟩ : syracuseStep 1034551 = 1551827) B1551827
theorem B1034571 : Blo 1032607 1034571 := bstep (se 1 (by rfl) ⟨775928, by rfl⟩ : syracuseStep 1034571 = 1551857) B1551857
theorem B1034583 : Blo 1032607 1034583 := bstep (se 1 (by rfl) ⟨775937, by rfl⟩ : syracuseStep 1034583 = 1551875) B1551875
theorem B1034603 : Blo 1032607 1034603 := bstep (se 1 (by rfl) ⟨775952, by rfl⟩ : syracuseStep 1034603 = 1551905) B1551905
theorem B1165675 : Blo 1032607 1165675 := bstep (se 1 (by rfl) ⟨874256, by rfl⟩ : syracuseStep 1165675 = 1748513) B1748513
theorem B1034615 : Blo 1032607 1034615 := bstep (se 1 (by rfl) ⟨775961, by rfl⟩ : syracuseStep 1034615 = 1551923) B1551923
theorem B1034635 : Blo 1032607 1034635 := bstep (se 1 (by rfl) ⟨775976, by rfl⟩ : syracuseStep 1034635 = 1551953) B1551953
theorem B1034647 : Blo 1032607 1034647 := bstep (se 1 (by rfl) ⟨775985, by rfl⟩ : syracuseStep 1034647 = 1551971) B1551971
theorem B1034667 : Blo 1032607 1034667 := bstep (se 1 (by rfl) ⟨776000, by rfl⟩ : syracuseStep 1034667 = 1552001) B1552001
theorem B9947569 : Blo 1032607 9947569 := bstep (se 2 (by rfl) ⟨3730338, by rfl⟩ : syracuseStep 9947569 = 7460677) B7460677
theorem B1034679 : Blo 1032607 1034679 := bstep (se 1 (by rfl) ⟨776009, by rfl⟩ : syracuseStep 1034679 = 1552019) B1552019
theorem B1034699 : Blo 1032607 1034699 := bstep (se 1 (by rfl) ⟨776024, by rfl⟩ : syracuseStep 1034699 = 1552049) B1552049
theorem B1034711 : Blo 1032607 1034711 := bstep (se 1 (by rfl) ⟨776033, by rfl⟩ : syracuseStep 1034711 = 1552067) B1552067
theorem B1165783 : Blo 1032607 1165783 := bstep (se 1 (by rfl) ⟨874337, by rfl⟩ : syracuseStep 1165783 = 1748675) B1748675
theorem B1034731 : Blo 1032607 1034731 := bstep (se 1 (by rfl) ⟨776048, by rfl⟩ : syracuseStep 1034731 = 1552097) B1552097
theorem B1034743 : Blo 1032607 1034743 := bstep (se 1 (by rfl) ⟨776057, by rfl⟩ : syracuseStep 1034743 = 1552115) B1552115
theorem B1034763 : Blo 1032607 1034763 := bstep (se 1 (by rfl) ⟨776072, by rfl⟩ : syracuseStep 1034763 = 1552145) B1552145
theorem B1034775 : Blo 1032607 1034775 := bstep (se 1 (by rfl) ⟨776081, by rfl⟩ : syracuseStep 1034775 = 1552163) B1552163
theorem B1034795 : Blo 1032607 1034795 := bstep (se 1 (by rfl) ⟨776096, by rfl⟩ : syracuseStep 1034795 = 1552193) B1552193
theorem B1034807 : Blo 1032607 1034807 := bstep (se 1 (by rfl) ⟨776105, by rfl⟩ : syracuseStep 1034807 = 1552211) B1552211
theorem B1034827 : Blo 1032607 1034827 := bstep (se 1 (by rfl) ⟨776120, by rfl⟩ : syracuseStep 1034827 = 1552241) B1552241
theorem B1034839 : Blo 1032607 1034839 := bstep (se 1 (by rfl) ⟨776129, by rfl⟩ : syracuseStep 1034839 = 1552259) B1552259
theorem B1034859 : Blo 1032607 1034859 := bstep (se 1 (by rfl) ⟨776144, by rfl⟩ : syracuseStep 1034859 = 1552289) B1552289
theorem B1034871 : Blo 1032607 1034871 := bstep (se 1 (by rfl) ⟨776153, by rfl⟩ : syracuseStep 1034871 = 1552307) B1552307
theorem B1034891 : Blo 1032607 1034891 := bstep (se 1 (by rfl) ⟨776168, by rfl⟩ : syracuseStep 1034891 = 1552337) B1552337
theorem B1165963 : Blo 1032607 1165963 := bstep (se 1 (by rfl) ⟨874472, by rfl⟩ : syracuseStep 1165963 = 1748945) B1748945
theorem B3492503 : Blo 1032607 3492503 := bstep (se 1 (by rfl) ⟨2619377, by rfl⟩ : syracuseStep 3492503 = 5238755) B5238755
theorem B1034903 : Blo 1032607 1034903 := bstep (se 1 (by rfl) ⟨776177, by rfl⟩ : syracuseStep 1034903 = 1552355) B1552355
theorem B1034923 : Blo 1032607 1034923 := bstep (se 1 (by rfl) ⟨776192, by rfl⟩ : syracuseStep 1034923 = 1552385) B1552385
theorem B1034935 : Blo 1032607 1034935 := bstep (se 1 (by rfl) ⟨776201, by rfl⟩ : syracuseStep 1034935 = 1552403) B1552403
theorem B1034955 : Blo 1032607 1034955 := bstep (se 1 (by rfl) ⟨776216, by rfl⟩ : syracuseStep 1034955 = 1552433) B1552433
theorem B1034967 : Blo 1032607 1034967 := bstep (se 1 (by rfl) ⟨776225, by rfl⟩ : syracuseStep 1034967 = 1552451) B1552451
theorem B1034987 : Blo 1032607 1034987 := bstep (se 1 (by rfl) ⟨776240, by rfl⟩ : syracuseStep 1034987 = 1552481) B1552481
theorem B1034999 : Blo 1032607 1034999 := bstep (se 1 (by rfl) ⟨776249, by rfl⟩ : syracuseStep 1034999 = 1552499) B1552499
theorem B1166071 : Blo 1032607 1166071 := bstep (se 1 (by rfl) ⟨874553, by rfl⟩ : syracuseStep 1166071 = 1749107) B1749107
theorem B1035019 : Blo 1032607 1035019 := bstep (se 1 (by rfl) ⟨776264, by rfl⟩ : syracuseStep 1035019 = 1552529) B1552529
theorem B1035031 : Blo 1032607 1035031 := bstep (se 1 (by rfl) ⟨776273, by rfl⟩ : syracuseStep 1035031 = 1552547) B1552547
theorem B1035051 : Blo 1032607 1035051 := bstep (se 1 (by rfl) ⟨776288, by rfl⟩ : syracuseStep 1035051 = 1552577) B1552577
theorem B1035063 : Blo 1032607 1035063 := bstep (se 1 (by rfl) ⟨776297, by rfl⟩ : syracuseStep 1035063 = 1552595) B1552595
theorem B1035083 : Blo 1032607 1035083 := bstep (se 1 (by rfl) ⟨776312, by rfl⟩ : syracuseStep 1035083 = 1552625) B1552625
theorem B1035095 : Blo 1032607 1035095 := bstep (se 1 (by rfl) ⟨776321, by rfl⟩ : syracuseStep 1035095 = 1552643) B1552643
theorem B1035115 : Blo 1032607 1035115 := bstep (se 1 (by rfl) ⟨776336, by rfl⟩ : syracuseStep 1035115 = 1552673) B1552673
theorem B1035127 : Blo 1032607 1035127 := bstep (se 1 (by rfl) ⟨776345, by rfl⟩ : syracuseStep 1035127 = 1552691) B1552691
theorem B1035147 : Blo 1032607 1035147 := bstep (se 1 (by rfl) ⟨776360, by rfl⟩ : syracuseStep 1035147 = 1552721) B1552721
theorem B1035159 : Blo 1032607 1035159 := bstep (se 1 (by rfl) ⟨776369, by rfl⟩ : syracuseStep 1035159 = 1552739) B1552739
theorem B1035179 : Blo 1032607 1035179 := bstep (se 1 (by rfl) ⟨776384, by rfl⟩ : syracuseStep 1035179 = 1552769) B1552769
theorem B1035191 : Blo 1032607 1035191 := bstep (se 1 (by rfl) ⟨776393, by rfl⟩ : syracuseStep 1035191 = 1552787) B1552787
theorem B1035211 : Blo 1032607 1035211 := bstep (se 1 (by rfl) ⟨776408, by rfl⟩ : syracuseStep 1035211 = 1552817) B1552817
theorem B1035223 : Blo 1032607 1035223 := bstep (se 1 (by rfl) ⟨776417, by rfl⟩ : syracuseStep 1035223 = 1552835) B1552835
theorem B1035243 : Blo 1032607 1035243 := bstep (se 1 (by rfl) ⟨776432, by rfl⟩ : syracuseStep 1035243 = 1552865) B1552865
theorem B1035255 : Blo 1032607 1035255 := bstep (se 1 (by rfl) ⟨776441, by rfl⟩ : syracuseStep 1035255 = 1552883) B1552883
theorem B1035275 : Blo 1032607 1035275 := bstep (se 1 (by rfl) ⟨776456, by rfl⟩ : syracuseStep 1035275 = 1552913) B1552913
theorem B1035287 : Blo 1032607 1035287 := bstep (se 1 (by rfl) ⟨776465, by rfl⟩ : syracuseStep 1035287 = 1552931) B1552931
theorem B1035307 : Blo 1032607 1035307 := bstep (se 1 (by rfl) ⟨776480, by rfl⟩ : syracuseStep 1035307 = 1552961) B1552961
theorem B1035319 : Blo 1032607 1035319 := bstep (se 1 (by rfl) ⟨776489, by rfl⟩ : syracuseStep 1035319 = 1552979) B1552979
theorem B1035339 : Blo 1032607 1035339 := bstep (se 1 (by rfl) ⟨776504, by rfl⟩ : syracuseStep 1035339 = 1553009) B1553009
theorem B1035351 : Blo 1032607 1035351 := bstep (se 1 (by rfl) ⟨776513, by rfl⟩ : syracuseStep 1035351 = 1553027) B1553027
theorem B1035371 : Blo 1032607 1035371 := bstep (se 1 (by rfl) ⟨776528, by rfl⟩ : syracuseStep 1035371 = 1553057) B1553057
theorem B1035383 : Blo 1032607 1035383 := bstep (se 1 (by rfl) ⟨776537, by rfl⟩ : syracuseStep 1035383 = 1553075) B1553075
theorem B1035403 : Blo 1032607 1035403 := bstep (se 1 (by rfl) ⟨776552, by rfl⟩ : syracuseStep 1035403 = 1553105) B1553105
theorem B1035415 : Blo 1032607 1035415 := bstep (se 1 (by rfl) ⟨776561, by rfl⟩ : syracuseStep 1035415 = 1553123) B1553123
theorem B1035435 : Blo 1032607 1035435 := bstep (se 1 (by rfl) ⟨776576, by rfl⟩ : syracuseStep 1035435 = 1553153) B1553153
theorem B3493043 : Blo 1032607 3493043 := bstep (se 1 (by rfl) ⟨2619782, by rfl⟩ : syracuseStep 3493043 = 5239565) B5239565
theorem B1035447 : Blo 1032607 1035447 := bstep (se 1 (by rfl) ⟨776585, by rfl⟩ : syracuseStep 1035447 = 1553171) B1553171
theorem B1035467 : Blo 1032607 1035467 := bstep (se 1 (by rfl) ⟨776600, by rfl⟩ : syracuseStep 1035467 = 1553201) B1553201
theorem B1035479 : Blo 1032607 1035479 := bstep (se 1 (by rfl) ⟨776609, by rfl⟩ : syracuseStep 1035479 = 1553219) B1553219
theorem B1035499 : Blo 1032607 1035499 := bstep (se 1 (by rfl) ⟨776624, by rfl⟩ : syracuseStep 1035499 = 1553249) B1553249
theorem B1035511 : Blo 1032607 1035511 := bstep (se 1 (by rfl) ⟨776633, by rfl⟩ : syracuseStep 1035511 = 1553267) B1553267
theorem B1035531 : Blo 1032607 1035531 := bstep (se 1 (by rfl) ⟨776648, by rfl⟩ : syracuseStep 1035531 = 1553297) B1553297
theorem B1035543 : Blo 1032607 1035543 := bstep (se 1 (by rfl) ⟨776657, by rfl⟩ : syracuseStep 1035543 = 1553315) B1553315
theorem B1035563 : Blo 1032607 1035563 := bstep (se 1 (by rfl) ⟨776672, by rfl⟩ : syracuseStep 1035563 = 1553345) B1553345
theorem B1035575 : Blo 1032607 1035575 := bstep (se 1 (by rfl) ⟨776681, by rfl⟩ : syracuseStep 1035575 = 1553363) B1553363
theorem B7851329 : Blo 1032607 7851329 := bstep (se 2 (by rfl) ⟨2944248, by rfl⟩ : syracuseStep 7851329 = 5888497) B5888497
theorem B1035595 : Blo 1032607 1035595 := bstep (se 1 (by rfl) ⟨776696, by rfl⟩ : syracuseStep 1035595 = 1553393) B1553393
theorem B1035607 : Blo 1032607 1035607 := bstep (se 1 (by rfl) ⟨776705, by rfl⟩ : syracuseStep 1035607 = 1553411) B1553411
theorem B1035627 : Blo 1032607 1035627 := bstep (se 1 (by rfl) ⟨776720, by rfl⟩ : syracuseStep 1035627 = 1553441) B1553441
theorem B1035639 : Blo 1032607 1035639 := bstep (se 1 (by rfl) ⟨776729, by rfl⟩ : syracuseStep 1035639 = 1553459) B1553459
theorem B1035659 : Blo 1032607 1035659 := bstep (se 1 (by rfl) ⟨776744, by rfl⟩ : syracuseStep 1035659 = 1553489) B1553489
theorem B4410769 : Blo 1032607 4410769 := bstep (se 2 (by rfl) ⟨1654038, by rfl⟩ : syracuseStep 4410769 = 3308077) B3308077
theorem B1035671 : Blo 1032607 1035671 := bstep (se 1 (by rfl) ⟨776753, by rfl⟩ : syracuseStep 1035671 = 1553507) B1553507
theorem B1035691 : Blo 1032607 1035691 := bstep (se 1 (by rfl) ⟨776768, by rfl⟩ : syracuseStep 1035691 = 1553537) B1553537
theorem B1035703 : Blo 1032607 1035703 := bstep (se 1 (by rfl) ⟨776777, by rfl⟩ : syracuseStep 1035703 = 1553555) B1553555
theorem B3493313 : Blo 1032607 3493313 := bstep (se 2 (by rfl) ⟨1309992, by rfl⟩ : syracuseStep 3493313 = 2619985) B2619985
theorem B1035723 : Blo 1032607 1035723 := bstep (se 1 (by rfl) ⟨776792, by rfl⟩ : syracuseStep 1035723 = 1553585) B1553585
theorem B1035735 : Blo 1032607 1035735 := bstep (se 1 (by rfl) ⟨776801, by rfl⟩ : syracuseStep 1035735 = 1553603) B1553603
theorem B1035755 : Blo 1032607 1035755 := bstep (se 1 (by rfl) ⟨776816, by rfl⟩ : syracuseStep 1035755 = 1553633) B1553633
theorem B1035767 : Blo 1032607 1035767 := bstep (se 1 (by rfl) ⟨776825, by rfl⟩ : syracuseStep 1035767 = 1553651) B1553651
theorem B1035787 : Blo 1032607 1035787 := bstep (se 1 (by rfl) ⟨776840, by rfl⟩ : syracuseStep 1035787 = 1553681) B1553681
theorem B1035799 : Blo 1032607 1035799 := bstep (se 1 (by rfl) ⟨776849, by rfl⟩ : syracuseStep 1035799 = 1553699) B1553699
theorem B1035819 : Blo 1032607 1035819 := bstep (se 1 (by rfl) ⟨776864, by rfl⟩ : syracuseStep 1035819 = 1553729) B1553729
theorem B1035831 : Blo 1032607 1035831 := bstep (se 1 (by rfl) ⟨776873, by rfl⟩ : syracuseStep 1035831 = 1553747) B1553747
theorem B1035851 : Blo 1032607 1035851 := bstep (se 1 (by rfl) ⟨776888, by rfl⟩ : syracuseStep 1035851 = 1553777) B1553777
theorem B1035863 : Blo 1032607 1035863 := bstep (se 1 (by rfl) ⟨776897, by rfl⟩ : syracuseStep 1035863 = 1553795) B1553795
theorem B1035883 : Blo 1032607 1035883 := bstep (se 1 (by rfl) ⟨776912, by rfl⟩ : syracuseStep 1035883 = 1553825) B1553825
theorem B1035895 : Blo 1032607 1035895 := bstep (se 1 (by rfl) ⟨776921, by rfl⟩ : syracuseStep 1035895 = 1553843) B1553843
theorem B1035915 : Blo 1032607 1035915 := bstep (se 1 (by rfl) ⟨776936, by rfl⟩ : syracuseStep 1035915 = 1553873) B1553873
theorem B1035927 : Blo 1032607 1035927 := bstep (se 1 (by rfl) ⟨776945, by rfl⟩ : syracuseStep 1035927 = 1553891) B1553891
theorem B1035947 : Blo 1032607 1035947 := bstep (se 1 (by rfl) ⟨776960, by rfl⟩ : syracuseStep 1035947 = 1553921) B1553921
theorem B1035959 : Blo 1032607 1035959 := bstep (se 1 (by rfl) ⟨776969, by rfl⟩ : syracuseStep 1035959 = 1553939) B1553939
theorem B1035979 : Blo 1032607 1035979 := bstep (se 1 (by rfl) ⟨776984, by rfl⟩ : syracuseStep 1035979 = 1553969) B1553969
theorem B1035991 : Blo 1032607 1035991 := bstep (se 1 (by rfl) ⟨776993, by rfl⟩ : syracuseStep 1035991 = 1553987) B1553987
theorem B1036011 : Blo 1032607 1036011 := bstep (se 1 (by rfl) ⟨777008, by rfl⟩ : syracuseStep 1036011 = 1554017) B1554017
theorem B1036023 : Blo 1032607 1036023 := bstep (se 1 (by rfl) ⟨777017, by rfl⟩ : syracuseStep 1036023 = 1554035) B1554035
theorem B1036043 : Blo 1032607 1036043 := bstep (se 1 (by rfl) ⟨777032, by rfl⟩ : syracuseStep 1036043 = 1554065) B1554065
theorem B1036055 : Blo 1032607 1036055 := bstep (se 1 (by rfl) ⟨777041, by rfl⟩ : syracuseStep 1036055 = 1554083) B1554083
theorem B1036075 : Blo 1032607 1036075 := bstep (se 1 (by rfl) ⟨777056, by rfl⟩ : syracuseStep 1036075 = 1554113) B1554113
theorem B10604333 : Blo 1032607 10604333 := bstep (se 3 (by rfl) ⟨1988312, by rfl⟩ : syracuseStep 10604333 = 3976625) B3976625
theorem B1036087 : Blo 1032607 1036087 := bstep (se 1 (by rfl) ⟨777065, by rfl⟩ : syracuseStep 1036087 = 1554131) B1554131
theorem B1036107 : Blo 1032607 1036107 := bstep (se 1 (by rfl) ⟨777080, by rfl⟩ : syracuseStep 1036107 = 1554161) B1554161
theorem B1036119 : Blo 1032607 1036119 := bstep (se 1 (by rfl) ⟨777089, by rfl⟩ : syracuseStep 1036119 = 1554179) B1554179
theorem B1036139 : Blo 1032607 1036139 := bstep (se 1 (by rfl) ⟨777104, by rfl⟩ : syracuseStep 1036139 = 1554209) B1554209
theorem B1036151 : Blo 1032607 1036151 := bstep (se 1 (by rfl) ⟨777113, by rfl⟩ : syracuseStep 1036151 = 1554227) B1554227
theorem B1036171 : Blo 1032607 1036171 := bstep (se 1 (by rfl) ⟨777128, by rfl⟩ : syracuseStep 1036171 = 1554257) B1554257
theorem B1036183 : Blo 1032607 1036183 := bstep (se 1 (by rfl) ⟨777137, by rfl⟩ : syracuseStep 1036183 = 1554275) B1554275
theorem B1036203 : Blo 1032607 1036203 := bstep (se 1 (by rfl) ⟨777152, by rfl⟩ : syracuseStep 1036203 = 1554305) B1554305
theorem B1036215 : Blo 1032607 1036215 := bstep (se 1 (by rfl) ⟨777161, by rfl⟩ : syracuseStep 1036215 = 1554323) B1554323
theorem B1036235 : Blo 1032607 1036235 := bstep (se 1 (by rfl) ⟨777176, by rfl⟩ : syracuseStep 1036235 = 1554353) B1554353
theorem B1036247 : Blo 1032607 1036247 := bstep (se 1 (by rfl) ⟨777185, by rfl⟩ : syracuseStep 1036247 = 1554371) B1554371
theorem B3493853 : Blo 1032607 3493853 := bstep (se 3 (by rfl) ⟨655097, by rfl⟩ : syracuseStep 3493853 = 1310195) B1310195
theorem B1036267 : Blo 1032607 1036267 := bstep (se 1 (by rfl) ⟨777200, by rfl⟩ : syracuseStep 1036267 = 1554401) B1554401
theorem B1036279 : Blo 1032607 1036279 := bstep (se 1 (by rfl) ⟨777209, by rfl⟩ : syracuseStep 1036279 = 1554419) B1554419
theorem B1036299 : Blo 1032607 1036299 := bstep (se 1 (by rfl) ⟨777224, by rfl⟩ : syracuseStep 1036299 = 1554449) B1554449
theorem B1396759 : Blo 1032607 1396759 := bstep (se 1 (by rfl) ⟨1047569, by rfl⟩ : syracuseStep 1396759 = 2095139) B2095139
theorem B1036311 : Blo 1032607 1036311 := bstep (se 1 (by rfl) ⟨777233, by rfl⟩ : syracuseStep 1036311 = 1554467) B1554467
theorem B1036331 : Blo 1032607 1036331 := bstep (se 1 (by rfl) ⟨777248, by rfl⟩ : syracuseStep 1036331 = 1554497) B1554497
theorem B1036343 : Blo 1032607 1036343 := bstep (se 1 (by rfl) ⟨777257, by rfl⟩ : syracuseStep 1036343 = 1554515) B1554515
theorem B1036363 : Blo 1032607 1036363 := bstep (se 1 (by rfl) ⟨777272, by rfl⟩ : syracuseStep 1036363 = 1554545) B1554545
theorem B1036375 : Blo 1032607 1036375 := bstep (se 1 (by rfl) ⟨777281, by rfl⟩ : syracuseStep 1036375 = 1554563) B1554563
theorem B1036395 : Blo 1032607 1036395 := bstep (se 1 (by rfl) ⟨777296, by rfl⟩ : syracuseStep 1036395 = 1554593) B1554593
theorem B1036407 : Blo 1032607 1036407 := bstep (se 1 (by rfl) ⟨777305, by rfl⟩ : syracuseStep 1036407 = 1554611) B1554611
theorem B1036427 : Blo 1032607 1036427 := bstep (se 1 (by rfl) ⟨777320, by rfl⟩ : syracuseStep 1036427 = 1554641) B1554641
theorem B1036439 : Blo 1032607 1036439 := bstep (se 1 (by rfl) ⟨777329, by rfl⟩ : syracuseStep 1036439 = 1554659) B1554659
theorem B1036459 : Blo 1032607 1036459 := bstep (se 1 (by rfl) ⟨777344, by rfl⟩ : syracuseStep 1036459 = 1554689) B1554689
theorem B1134775 : Blo 1032607 1134775 := bstep (se 1 (by rfl) ⟨851081, by rfl⟩ : syracuseStep 1134775 = 1702163) B1702163
theorem B1036471 : Blo 1032607 1036471 := bstep (se 1 (by rfl) ⟨777353, by rfl⟩ : syracuseStep 1036471 = 1554707) B1554707
theorem B1036491 : Blo 1032607 1036491 := bstep (se 1 (by rfl) ⟨777368, by rfl⟩ : syracuseStep 1036491 = 1554737) B1554737
theorem B1036503 : Blo 1032607 1036503 := bstep (se 1 (by rfl) ⟨777377, by rfl⟩ : syracuseStep 1036503 = 1554755) B1554755
theorem B1036523 : Blo 1032607 1036523 := bstep (se 1 (by rfl) ⟨777392, by rfl⟩ : syracuseStep 1036523 = 1554785) B1554785
theorem B1036535 : Blo 1032607 1036535 := bstep (se 1 (by rfl) ⟨777401, by rfl⟩ : syracuseStep 1036535 = 1554803) B1554803
theorem B22335749 : Blo 1032607 22335749 := bstep (se 4 (by rfl) ⟨2093976, by rfl⟩ : syracuseStep 22335749 = 4187953) B4187953
theorem B24236293 : Blo 1032607 24236293 := bstep (se 4 (by rfl) ⟨2272152, by rfl⟩ : syracuseStep 24236293 = 4544305) B4544305
theorem B1036555 : Blo 1032607 1036555 := bstep (se 1 (by rfl) ⟨777416, by rfl⟩ : syracuseStep 1036555 = 1554833) B1554833
theorem B1036567 : Blo 1032607 1036567 := bstep (se 1 (by rfl) ⟨777425, by rfl⟩ : syracuseStep 1036567 = 1554851) B1554851
theorem B1036587 : Blo 1032607 1036587 := bstep (se 1 (by rfl) ⟨777440, by rfl⟩ : syracuseStep 1036587 = 1554881) B1554881
theorem B1036599 : Blo 1032607 1036599 := bstep (se 1 (by rfl) ⟨777449, by rfl⟩ : syracuseStep 1036599 = 1554899) B1554899
theorem B5230979 : Blo 1032607 5230979 := bstep (se 1 (by rfl) ⟨3923234, by rfl⟩ : syracuseStep 5230979 = 7846469) B7846469
theorem B5886539 : Blo 1032607 5886539 := bstep (se 1 (by rfl) ⟨4414904, by rfl⟩ : syracuseStep 5886539 = 8829809) B8829809
theorem B8377181 : Blo 1032607 8377181 := bstep (se 3 (by rfl) ⟨1570721, by rfl⟩ : syracuseStep 8377181 = 3141443) B3141443
theorem B3888017 : Blo 1032607 3888017 := bstep (se 2 (by rfl) ⟨1458006, by rfl⟩ : syracuseStep 3888017 = 2916013) B2916013
theorem B3494987 : Blo 1032607 3494987 := bstep (se 1 (by rfl) ⟨2621240, by rfl⟩ : syracuseStep 3494987 = 5242481) B5242481
theorem B7853273 : Blo 1032607 7853273 := bstep (se 2 (by rfl) ⟨2944977, by rfl⟩ : syracuseStep 7853273 = 5889955) B5889955
theorem B3921155 : Blo 1032607 3921155 := bstep (se 1 (by rfl) ⟨2940866, by rfl⟩ : syracuseStep 3921155 = 5881733) B5881733
theorem B3921169 : Blo 1032607 3921169 := bstep (se 2 (by rfl) ⟨1470438, by rfl⟩ : syracuseStep 3921169 = 2940877) B2940877
theorem B3495257 : Blo 1032607 3495257 := bstep (se 2 (by rfl) ⟨1310721, by rfl⟩ : syracuseStep 3495257 = 2621443) B2621443
theorem B3921473 : Blo 1032607 3921473 := bstep (se 2 (by rfl) ⟨1470552, by rfl⟩ : syracuseStep 3921473 = 2941105) B2941105
theorem B1103863 : Blo 1032607 1103863 := bstep (se 1 (by rfl) ⟨827897, by rfl⟩ : syracuseStep 1103863 = 1655795) B1655795
theorem B3495959 : Blo 1032607 3495959 := bstep (se 1 (by rfl) ⟨2621969, by rfl⟩ : syracuseStep 3495959 = 5243939) B5243939
theorem B3922141 : Blo 1032607 3922141 := bstep (se 3 (by rfl) ⟨735401, by rfl⟩ : syracuseStep 3922141 = 1470803) B1470803
theorem B4413761 : Blo 1032607 4413761 := bstep (se 2 (by rfl) ⟨1655160, by rfl⟩ : syracuseStep 4413761 = 3310321) B3310321
theorem B3496499 : Blo 1032607 3496499 := bstep (se 1 (by rfl) ⟨2622374, by rfl⟩ : syracuseStep 3496499 = 5244749) B5244749
theorem B50420465 : Blo 1032607 50420465 := bstep (se 2 (by rfl) ⟨18907674, by rfl⟩ : syracuseStep 50420465 = 37815349) B37815349
theorem B1104683 : Blo 1032607 1104683 := bstep (se 1 (by rfl) ⟨828512, by rfl⟩ : syracuseStep 1104683 = 1657025) B1657025
theorem B3496769 : Blo 1032607 3496769 := bstep (se 2 (by rfl) ⟨1311288, by rfl⟩ : syracuseStep 3496769 = 2622577) B2622577
theorem B9952217 : Blo 1032607 9952217 := bstep (se 2 (by rfl) ⟨3732081, by rfl⟩ : syracuseStep 9952217 = 7464163) B7464163
theorem B3497309 : Blo 1032607 3497309 := bstep (se 3 (by rfl) ⟨655745, by rfl⟩ : syracuseStep 3497309 = 1311491) B1311491
theorem B1400267 : Blo 1032607 1400267 := bstep (se 1 (by rfl) ⟨1050200, by rfl⟩ : syracuseStep 1400267 = 2100401) B2100401
theorem B3923417 : Blo 1032607 3923417 := bstep (se 2 (by rfl) ⟨1471281, by rfl⟩ : syracuseStep 3923417 = 2942563) B2942563
theorem B3726809 : Blo 1032607 3726809 := bstep (se 2 (by rfl) ⟨1397553, by rfl⟩ : syracuseStep 3726809 = 2795107) B2795107
theorem B2940695 : Blo 1032607 2940695 := bstep (se 1 (by rfl) ⟨2205521, by rfl⟩ : syracuseStep 2940695 = 4411043) B4411043
theorem B1105751 : Blo 1032607 1105751 := bstep (se 1 (by rfl) ⟨829313, by rfl⟩ : syracuseStep 1105751 = 1658627) B1658627
theorem B4480913 : Blo 1032607 4480913 := bstep (se 2 (by rfl) ⟨1680342, by rfl⟩ : syracuseStep 4480913 = 3360685) B3360685
theorem B5234705 : Blo 1032607 5234705 := bstep (se 2 (by rfl) ⟨1963014, by rfl⟩ : syracuseStep 5234705 = 3926029) B3926029
theorem B19914821 : Blo 1032607 19914821 := bstep (se 4 (by rfl) ⟨1867014, by rfl⟩ : syracuseStep 19914821 = 3734029) B3734029
theorem B5234867 : Blo 1032607 5234867 := bstep (se 1 (by rfl) ⟨3926150, by rfl⟩ : syracuseStep 5234867 = 7852301) B7852301
theorem B4252097 : Blo 1032607 4252097 := bstep (se 2 (by rfl) ⟨1594536, by rfl⟩ : syracuseStep 4252097 = 3189073) B3189073
theorem B3498443 : Blo 1032607 3498443 := bstep (se 1 (by rfl) ⟨2623832, by rfl⟩ : syracuseStep 3498443 = 5247665) B5247665
theorem B7856675 : Blo 1032607 7856675 := bstep (se 1 (by rfl) ⟨5892506, by rfl⟩ : syracuseStep 7856675 = 11785013) B11785013
theorem B2941505 : Blo 1032607 2941505 := bstep (se 2 (by rfl) ⟨1103064, by rfl⟩ : syracuseStep 2941505 = 2206129) B2206129
theorem B5595749 : Blo 1032607 5595749 := bstep (se 4 (by rfl) ⟨524601, by rfl⟩ : syracuseStep 5595749 = 1049203) B1049203
theorem B4416221 : Blo 1032607 4416221 := bstep (se 3 (by rfl) ⟨828041, by rfl⟩ : syracuseStep 4416221 = 1656083) B1656083
theorem B1106827 : Blo 1032607 1106827 := bstep (se 1 (by rfl) ⟨830120, by rfl⟩ : syracuseStep 1106827 = 1660241) B1660241
theorem B2614295 : Blo 1032607 2614295 := bstep (se 1 (by rfl) ⟨1960721, by rfl⟩ : syracuseStep 2614295 = 3921443) B3921443
theorem B3925043 : Blo 1032607 3925043 := bstep (se 1 (by rfl) ⟨2943782, by rfl⟩ : syracuseStep 3925043 = 5887565) B5887565
theorem B3925057 : Blo 1032607 3925057 := bstep (se 2 (by rfl) ⟨1471896, by rfl⟩ : syracuseStep 3925057 = 2943793) B2943793
theorem B4973633 : Blo 1032607 4973633 := bstep (se 2 (by rfl) ⟨1865112, by rfl⟩ : syracuseStep 4973633 = 3730225) B3730225
theorem B11789387 : Blo 1032607 11789387 := bstep (se 1 (by rfl) ⟨8842040, by rfl⟩ : syracuseStep 11789387 = 17684081) B17684081
theorem B1860851 : Blo 1032607 1860851 := bstep (se 1 (by rfl) ⟨1395638, by rfl⟩ : syracuseStep 1860851 = 2791277) B2791277
theorem B8381875 : Blo 1032607 8381875 := bstep (se 1 (by rfl) ⟨6286406, by rfl⟩ : syracuseStep 8381875 = 12572813) B12572813
theorem B2483635 : Blo 1032607 2483635 := bstep (se 1 (by rfl) ⟨1862726, by rfl⟩ : syracuseStep 2483635 = 3725453) B3725453
theorem B2614963 : Blo 1032607 2614963 := bstep (se 1 (by rfl) ⟨1961222, by rfl⟩ : syracuseStep 2614963 = 3922445) B3922445
theorem B1861399 : Blo 1032607 1861399 := bstep (se 1 (by rfl) ⟨1396049, by rfl⟩ : syracuseStep 1861399 = 2792099) B2792099
theorem B2615105 : Blo 1032607 2615105 := bstep (se 2 (by rfl) ⟨980664, by rfl⟩ : syracuseStep 2615105 = 1961329) B1961329
theorem B8841221 : Blo 1032607 8841221 := bstep (se 4 (by rfl) ⟨828864, by rfl⟩ : syracuseStep 8841221 = 1657729) B1657729
theorem B5236811 : Blo 1032607 5236811 := bstep (se 1 (by rfl) ⟨3927608, by rfl⟩ : syracuseStep 5236811 = 7855217) B7855217
theorem B6383717 : Blo 1032607 6383717 := bstep (se 4 (by rfl) ⟨598473, by rfl⟩ : syracuseStep 6383717 = 1196947) B1196947
theorem B2943155 : Blo 1032607 2943155 := bstep (se 1 (by rfl) ⟨2207366, by rfl⟩ : syracuseStep 2943155 = 4414733) B4414733
theorem B2943179 : Blo 1032607 2943179 := bstep (se 1 (by rfl) ⟨2207384, by rfl⟩ : syracuseStep 2943179 = 4414769) B4414769
theorem B4188509 : Blo 1032607 4188509 := bstep (se 3 (by rfl) ⟨785345, by rfl⟩ : syracuseStep 4188509 = 1570691) B1570691
theorem B7465547 : Blo 1032607 7465547 := bstep (se 1 (by rfl) ⟨5599160, by rfl⟩ : syracuseStep 7465547 = 11198321) B11198321
theorem B2550347 : Blo 1032607 2550347 := bstep (se 1 (by rfl) ⟨1912760, by rfl⟩ : syracuseStep 2550347 = 3825521) B3825521
theorem B10218059 : Blo 1032607 10218059 := bstep (se 1 (by rfl) ⟨7663544, by rfl⟩ : syracuseStep 10218059 = 15327089) B15327089
theorem B8841905 : Blo 1032607 8841905 := bstep (se 2 (by rfl) ⟨3315714, by rfl⟩ : syracuseStep 8841905 = 6631429) B6631429
theorem B1960843 : Blo 1032607 1960843 := bstep (se 1 (by rfl) ⟨1470632, by rfl⟩ : syracuseStep 1960843 = 2941265) B2941265
theorem B3926987 : Blo 1032607 3926987 := bstep (se 1 (by rfl) ⟨2945240, by rfl⟩ : syracuseStep 3926987 = 5890481) B5890481
theorem B1960919 : Blo 1032607 1960919 := bstep (se 1 (by rfl) ⟨1470689, by rfl⟩ : syracuseStep 1960919 = 2941379) B2941379
theorem B3927001 : Blo 1032607 3927001 := bstep (se 2 (by rfl) ⟨1472625, by rfl⟩ : syracuseStep 3927001 = 2945251) B2945251
theorem B2943965 : Blo 1032607 2943965 := bstep (se 3 (by rfl) ⟨551993, by rfl⟩ : syracuseStep 2943965 = 1103987) B1103987
theorem B14904337 : Blo 1032607 14904337 := bstep (se 2 (by rfl) ⟨5589126, by rfl⟩ : syracuseStep 14904337 = 11178253) B11178253
theorem B2616371 : Blo 1032607 2616371 := bstep (se 1 (by rfl) ⟨1962278, by rfl⟩ : syracuseStep 2616371 = 3924557) B3924557
theorem B4713623 : Blo 1032607 4713623 := bstep (se 1 (by rfl) ⟨3535217, by rfl⟩ : syracuseStep 4713623 = 7070435) B7070435
theorem B4418819 : Blo 1032607 4418819 := bstep (se 1 (by rfl) ⟨3314114, by rfl⟩ : syracuseStep 4418819 = 6628229) B6628229
theorem B2616907 : Blo 1032607 2616907 := bstep (se 1 (by rfl) ⟨1962680, by rfl⟩ : syracuseStep 2616907 = 3925361) B3925361
theorem B1961587 : Blo 1032607 1961587 := bstep (se 1 (by rfl) ⟨1471190, by rfl⟩ : syracuseStep 1961587 = 2942381) B2942381
theorem B8842931 : Blo 1032607 8842931 := bstep (se 1 (by rfl) ⟨6632198, by rfl⟩ : syracuseStep 8842931 = 13264397) B13264397
theorem B2617049 : Blo 1032607 2617049 := bstep (se 2 (by rfl) ⟨981393, by rfl⟩ : syracuseStep 2617049 = 1962787) B1962787
theorem B5238593 : Blo 1032607 5238593 := bstep (se 2 (by rfl) ⟨1964472, by rfl⟩ : syracuseStep 5238593 = 3928945) B3928945
theorem B3731275 : Blo 1032607 3731275 := bstep (se 1 (by rfl) ⟨2798456, by rfl⟩ : syracuseStep 3731275 = 5596913) B5596913
theorem B1961815 : Blo 1032607 1961815 := bstep (se 1 (by rfl) ⟨1471361, by rfl⟩ : syracuseStep 1961815 = 2942723) B2942723
theorem B1470359 : Blo 1032607 1470359 := bstep (se 1 (by rfl) ⟨1102769, by rfl⟩ : syracuseStep 1470359 = 2205539) B2205539
theorem B3927959 : Blo 1032607 3927959 := bstep (se 1 (by rfl) ⟨2945969, by rfl⟩ : syracuseStep 3927959 = 5891939) B5891939
theorem B1863577 : Blo 1032607 1863577 := bstep (se 2 (by rfl) ⟨698841, by rfl⟩ : syracuseStep 1863577 = 1397683) B1397683
theorem B1961921 : Blo 1032607 1961921 := bstep (se 2 (by rfl) ⟨735720, by rfl⟩ : syracuseStep 1961921 = 1471441) B1471441
theorem B1962073 : Blo 1032607 1962073 := bstep (se 2 (by rfl) ⟨735777, by rfl⟩ : syracuseStep 1962073 = 1471555) B1471555
theorem B6549655 : Blo 1032607 6549655 := bstep (se 1 (by rfl) ⟨4912241, by rfl⟩ : syracuseStep 6549655 = 9824483) B9824483
theorem B1306955 : Blo 1032607 1306955 := bstep (se 1 (by rfl) ⟨980216, by rfl⟩ : syracuseStep 1306955 = 1960433) B1960433
theorem B2617879 : Blo 1032607 2617879 := bstep (se 1 (by rfl) ⟨1963409, by rfl⟩ : syracuseStep 2617879 = 3926819) B3926819
theorem B2945753 : Blo 1032607 2945753 := bstep (se 2 (by rfl) ⟨1104657, by rfl⟩ : syracuseStep 2945753 = 2209315) B2209315
theorem B3732313 : Blo 1032607 3732313 := bstep (se 2 (by rfl) ⟨1399617, by rfl⟩ : syracuseStep 3732313 = 2799235) B2799235
theorem B2323403 : Blo 1032607 2323403 := bstep (se 1 (by rfl) ⟨1742552, by rfl⟩ : syracuseStep 2323403 = 3485105) B3485105
theorem B2618315 : Blo 1032607 2618315 := bstep (se 1 (by rfl) ⟨1963736, by rfl⟩ : syracuseStep 2618315 = 3927473) B3927473
theorem B2323457 : Blo 1032607 2323457 := bstep (se 2 (by rfl) ⟨871296, by rfl⟩ : syracuseStep 2323457 = 1742593) B1742593
theorem B1307659 : Blo 1032607 1307659 := bstep (se 1 (by rfl) ⟨980744, by rfl⟩ : syracuseStep 1307659 = 1961489) B1961489
theorem B2946071 : Blo 1032607 2946071 := bstep (se 1 (by rfl) ⟨2209553, by rfl⟩ : syracuseStep 2946071 = 4419107) B4419107
theorem B50328611 : Blo 1032607 50328611 := bstep (se 1 (by rfl) ⟨37746458, by rfl⟩ : syracuseStep 50328611 = 75492917) B75492917
theorem B3929219 : Blo 1032607 3929219 := bstep (se 1 (by rfl) ⟨2946914, by rfl⟩ : syracuseStep 3929219 = 5893829) B5893829
theorem B3732659 : Blo 1032607 3732659 := bstep (se 1 (by rfl) ⟨2799494, by rfl⟩ : syracuseStep 3732659 = 5598989) B5598989
theorem B2323673 : Blo 1032607 2323673 := bstep (se 2 (by rfl) ⟨871377, by rfl⟩ : syracuseStep 2323673 = 1742755) B1742755
theorem B1864961 : Blo 1032607 1864961 := bstep (se 2 (by rfl) ⟨699360, by rfl⟩ : syracuseStep 1864961 = 1398721) B1398721
theorem B1307927 : Blo 1032607 1307927 := bstep (se 1 (by rfl) ⟨980945, by rfl⟩ : syracuseStep 1307927 = 1961891) B1961891
theorem B2323763 : Blo 1032607 2323763 := bstep (se 1 (by rfl) ⟨1742822, by rfl⟩ : syracuseStep 2323763 = 3485645) B3485645
theorem B11334977 : Blo 1032607 11334977 := bstep (se 2 (by rfl) ⟨4250616, by rfl⟩ : syracuseStep 11334977 = 8501233) B8501233
theorem B2618689 : Blo 1032607 2618689 := bstep (se 2 (by rfl) ⟨982008, by rfl⟩ : syracuseStep 2618689 = 1964017) B1964017
theorem B2323799 : Blo 1032607 2323799 := bstep (se 1 (by rfl) ⟨1742849, by rfl⟩ : syracuseStep 2323799 = 3485699) B3485699
theorem B1963379 : Blo 1032607 1963379 := bstep (se 1 (by rfl) ⟨1472534, by rfl⟩ : syracuseStep 1963379 = 2945069) B2945069
theorem B1865177 : Blo 1032607 1865177 := bstep (se 2 (by rfl) ⟨699441, by rfl⟩ : syracuseStep 1865177 = 1398883) B1398883
theorem B2323979 : Blo 1032607 2323979 := bstep (se 1 (by rfl) ⟨1742984, by rfl⟩ : syracuseStep 2323979 = 3485969) B3485969
theorem B1963531 : Blo 1032607 1963531 := bstep (se 1 (by rfl) ⟨1472648, by rfl⟩ : syracuseStep 1963531 = 2945297) B2945297
theorem B8943149 : Blo 1032607 8943149 := bstep (se 3 (by rfl) ⟨1676840, by rfl⟩ : syracuseStep 8943149 = 3353681) B3353681
theorem B2324033 : Blo 1032607 2324033 := bstep (se 2 (by rfl) ⟨871512, by rfl⟩ : syracuseStep 2324033 = 1743025) B1743025
theorem B5240537 : Blo 1032607 5240537 := bstep (se 2 (by rfl) ⟨1965201, by rfl⟩ : syracuseStep 5240537 = 3930403) B3930403
theorem B7862021 : Blo 1032607 7862021 := bstep (se 4 (by rfl) ⟨737064, by rfl⟩ : syracuseStep 7862021 = 1474129) B1474129
theorem B4716305 : Blo 1032607 4716305 := bstep (se 2 (by rfl) ⟨1768614, by rfl⟩ : syracuseStep 4716305 = 3537229) B3537229
theorem B2324249 : Blo 1032607 2324249 := bstep (se 2 (by rfl) ⟨871593, by rfl⟩ : syracuseStep 2324249 = 1743187) B1743187
theorem B2946881 : Blo 1032607 2946881 := bstep (se 2 (by rfl) ⟨1105080, by rfl⟩ : syracuseStep 2946881 = 2210161) B2210161
theorem B1963865 : Blo 1032607 1963865 := bstep (se 2 (by rfl) ⟨736449, by rfl⟩ : syracuseStep 1963865 = 1472899) B1472899
theorem B4257629 : Blo 1032607 4257629 := bstep (se 3 (by rfl) ⟨798305, by rfl⟩ : syracuseStep 4257629 = 1596611) B1596611
theorem B2324339 : Blo 1032607 2324339 := bstep (se 1 (by rfl) ⟨1743254, by rfl⟩ : syracuseStep 2324339 = 3486509) B3486509
theorem B2324375 : Blo 1032607 2324375 := bstep (se 1 (by rfl) ⟨1743281, by rfl⟩ : syracuseStep 2324375 = 3486563) B3486563
theorem B2619287 : Blo 1032607 2619287 := bstep (se 1 (by rfl) ⟨1964465, by rfl⟩ : syracuseStep 2619287 = 3928931) B3928931
theorem B1308631 : Blo 1032607 1308631 := bstep (se 1 (by rfl) ⟨981473, by rfl⟩ : syracuseStep 1308631 = 1962947) B1962947
theorem B6387673 : Blo 1032607 6387673 := bstep (se 2 (by rfl) ⟨2395377, by rfl⟩ : syracuseStep 6387673 = 4790755) B4790755
theorem B1177643 : Blo 1032607 1177643 := bstep (se 1 (by rfl) ⟨883232, by rfl⟩ : syracuseStep 1177643 = 1766465) B1766465
theorem B2324555 : Blo 1032607 2324555 := bstep (se 1 (by rfl) ⟨1743416, by rfl⟩ : syracuseStep 2324555 = 3486833) B3486833
theorem B2324609 : Blo 1032607 2324609 := bstep (se 2 (by rfl) ⟨871728, by rfl⟩ : syracuseStep 2324609 = 1743457) B1743457
theorem B1570969 : Blo 1032607 1570969 := bstep (se 2 (by rfl) ⟨589113, by rfl⟩ : syracuseStep 1570969 = 1178227) B1178227
theorem B3733697 : Blo 1032607 3733697 := bstep (se 2 (by rfl) ⟨1400136, by rfl⟩ : syracuseStep 3733697 = 2800273) B2800273
theorem B16152817 : Blo 1032607 16152817 := bstep (se 2 (by rfl) ⟨6057306, by rfl⟩ : syracuseStep 16152817 = 12114613) B12114613
theorem B1866035 : Blo 1032607 1866035 := bstep (se 1 (by rfl) ⟨1399526, by rfl⟩ : syracuseStep 1866035 = 2799053) B2799053
theorem B2324825 : Blo 1032607 2324825 := bstep (se 2 (by rfl) ⟨871809, by rfl⟩ : syracuseStep 2324825 = 1743619) B1743619
theorem B4487575 : Blo 1032607 4487575 := bstep (se 1 (by rfl) ⟨3365681, by rfl⟩ : syracuseStep 4487575 = 6731363) B6731363
theorem B2324915 : Blo 1032607 2324915 := bstep (se 1 (by rfl) ⟨1743686, by rfl⟩ : syracuseStep 2324915 = 3487373) B3487373
theorem B7174579 : Blo 1032607 7174579 := bstep (se 1 (by rfl) ⟨5380934, by rfl⟩ : syracuseStep 7174579 = 10761869) B10761869
theorem B2324951 : Blo 1032607 2324951 := bstep (se 1 (by rfl) ⟨1743713, by rfl⟩ : syracuseStep 2324951 = 3487427) B3487427
theorem B1964503 : Blo 1032607 1964503 := bstep (se 1 (by rfl) ⟨1473377, by rfl⟩ : syracuseStep 1964503 = 2946755) B2946755
theorem B2325131 : Blo 1032607 2325131 := bstep (se 1 (by rfl) ⟨1743848, by rfl⟩ : syracuseStep 2325131 = 3487697) B3487697
theorem B2325185 : Blo 1032607 2325185 := bstep (se 2 (by rfl) ⟨871944, by rfl⟩ : syracuseStep 2325185 = 1743889) B1743889
theorem B2620097 : Blo 1032607 2620097 := bstep (se 2 (by rfl) ⟨982536, by rfl⟩ : syracuseStep 2620097 = 1965073) B1965073
theorem B1473241 : Blo 1032607 1473241 := bstep (se 2 (by rfl) ⟨552465, by rfl⟩ : syracuseStep 1473241 = 1104931) B1104931
theorem B2325401 : Blo 1032607 2325401 := bstep (se 2 (by rfl) ⟨872025, by rfl⟩ : syracuseStep 2325401 = 1744051) B1744051
theorem B5045171 : Blo 1032607 5045171 := bstep (se 1 (by rfl) ⟨3783878, by rfl⟩ : syracuseStep 5045171 = 7567757) B7567757
theorem B1178551 : Blo 1032607 1178551 := bstep (se 1 (by rfl) ⟨883913, by rfl⟩ : syracuseStep 1178551 = 1767827) B1767827
theorem B4422593 : Blo 1032607 4422593 := bstep (se 2 (by rfl) ⟨1658472, by rfl⟩ : syracuseStep 4422593 = 3316945) B3316945
theorem B2325491 : Blo 1032607 2325491 := bstep (se 1 (by rfl) ⟨1744118, by rfl⟩ : syracuseStep 2325491 = 3488237) B3488237
theorem B2325527 : Blo 1032607 2325527 := bstep (se 1 (by rfl) ⟨1744145, by rfl⟩ : syracuseStep 2325527 = 3488291) B3488291
theorem B2653249 : Blo 1032607 2653249 := bstep (se 2 (by rfl) ⟨994968, by rfl⟩ : syracuseStep 2653249 = 1989937) B1989937
theorem B17890379 : Blo 1032607 17890379 := bstep (se 1 (by rfl) ⟨13417784, by rfl⟩ : syracuseStep 17890379 = 26835569) B26835569
theorem B2325707 : Blo 1032607 2325707 := bstep (se 1 (by rfl) ⟨1744280, by rfl⟩ : syracuseStep 2325707 = 3488561) B3488561
theorem B2620633 : Blo 1032607 2620633 := bstep (se 2 (by rfl) ⟨982737, by rfl⟩ : syracuseStep 2620633 = 1965475) B1965475
theorem B2096371 : Blo 1032607 2096371 := bstep (se 1 (by rfl) ⟨1572278, by rfl⟩ : syracuseStep 2096371 = 3144557) B3144557
theorem B2325761 : Blo 1032607 2325761 := bstep (se 2 (by rfl) ⟨872160, by rfl⟩ : syracuseStep 2325761 = 1744321) B1744321
theorem B1965323 : Blo 1032607 1965323 := bstep (se 1 (by rfl) ⟨1473992, by rfl⟩ : syracuseStep 1965323 = 2947985) B2947985
theorem B5242157 : Blo 1032607 5242157 := bstep (se 3 (by rfl) ⟨982904, by rfl⟩ : syracuseStep 5242157 = 1965809) B1965809
theorem B1965377 : Blo 1032607 1965377 := bstep (se 2 (by rfl) ⟨737016, by rfl⟩ : syracuseStep 1965377 = 1474033) B1474033
theorem B8846657 : Blo 1032607 8846657 := bstep (se 2 (by rfl) ⟨3317496, by rfl⟩ : syracuseStep 8846657 = 6634993) B6634993
theorem B2948555 : Blo 1032607 2948555 := bstep (se 1 (by rfl) ⟨2211416, by rfl⟩ : syracuseStep 2948555 = 4422833) B4422833
theorem B2325977 : Blo 1032607 2325977 := bstep (se 2 (by rfl) ⟨872241, by rfl⟩ : syracuseStep 2325977 = 1744483) B1744483
theorem B1048043 : Blo 1032607 1048043 := bstep (se 1 (by rfl) ⟨786032, by rfl⟩ : syracuseStep 1048043 = 1572065) B1572065
theorem B2326067 : Blo 1032607 2326067 := bstep (se 1 (by rfl) ⟨1744550, by rfl⟩ : syracuseStep 2326067 = 3489101) B3489101
theorem B2326103 : Blo 1032607 2326103 := bstep (se 1 (by rfl) ⟨1744577, by rfl⟩ : syracuseStep 2326103 = 3489155) B3489155
theorem B1310347 : Blo 1032607 1310347 := bstep (se 1 (by rfl) ⟨982760, by rfl⟩ : syracuseStep 1310347 = 1965521) B1965521
theorem B2359027 : Blo 1032607 2359027 := bstep (se 1 (by rfl) ⟨1769270, by rfl⟩ : syracuseStep 2359027 = 3538541) B3538541
theorem B2326283 : Blo 1032607 2326283 := bstep (se 1 (by rfl) ⟨1744712, by rfl⟩ : syracuseStep 2326283 = 3489425) B3489425
theorem B2326337 : Blo 1032607 2326337 := bstep (se 2 (by rfl) ⟨872376, by rfl⟩ : syracuseStep 2326337 = 1744753) B1744753
theorem B7470913 : Blo 1032607 7470913 := bstep (se 2 (by rfl) ⟨2801592, by rfl⟩ : syracuseStep 7470913 = 5603185) B5603185
theorem B1572697 : Blo 1032607 1572697 := bstep (se 2 (by rfl) ⟨589761, by rfl⟩ : syracuseStep 1572697 = 1179523) B1179523
theorem B4423517 : Blo 1032607 4423517 := bstep (se 3 (by rfl) ⟨829409, by rfl⟩ : syracuseStep 4423517 = 1658819) B1658819
theorem B2490401 : Blo 1032607 2490401 := bstep (se 2 (by rfl) ⟨933900, by rfl⟩ : syracuseStep 2490401 = 1867801) B1867801
theorem B2326571 : Blo 1032607 2326571 := bstep (se 1 (by rfl) ⟨1744928, by rfl⟩ : syracuseStep 2326571 = 3489857) B3489857
theorem B5242967 : Blo 1032607 5242967 := bstep (se 1 (by rfl) ⟨3932225, by rfl⟩ : syracuseStep 5242967 = 7864451) B7864451
theorem B2621555 : Blo 1032607 2621555 := bstep (se 1 (by rfl) ⟨1966166, by rfl⟩ : syracuseStep 2621555 = 3932333) B3932333
theorem B2490515 : Blo 1032607 2490515 := bstep (se 1 (by rfl) ⟨1867886, by rfl⟩ : syracuseStep 2490515 = 3735773) B3735773
theorem B1966265 : Blo 1032607 1966265 := bstep (se 2 (by rfl) ⟨737349, by rfl⟩ : syracuseStep 1966265 = 1474699) B1474699
theorem B2326931 : Blo 1032607 2326931 := bstep (se 1 (by rfl) ⟨1745198, by rfl⟩ : syracuseStep 2326931 = 3490397) B3490397
theorem B2326985 : Blo 1032607 2326985 := bstep (se 2 (by rfl) ⟨872619, by rfl⟩ : syracuseStep 2326985 = 1745239) B1745239
theorem B1311223 : Blo 1032607 1311223 := bstep (se 1 (by rfl) ⟨983417, by rfl⟩ : syracuseStep 1311223 = 1966835) B1966835
theorem B9962027 : Blo 1032607 9962027 := bstep (se 1 (by rfl) ⟨7471520, by rfl⟩ : syracuseStep 9962027 = 14943041) B14943041
theorem B5243453 : Blo 1032607 5243453 := bstep (se 3 (by rfl) ⟨983147, by rfl⟩ : syracuseStep 5243453 = 1966295) B1966295
theorem B2622071 : Blo 1032607 2622071 := bstep (se 1 (by rfl) ⟨1966553, by rfl⟩ : syracuseStep 2622071 = 3933107) B3933107
theorem B3146539 : Blo 1032607 3146539 := bstep (se 1 (by rfl) ⟨2359904, by rfl⟩ : syracuseStep 3146539 = 4719809) B4719809
theorem B1475371 : Blo 1032607 1475371 := bstep (se 1 (by rfl) ⟨1106528, by rfl⟩ : syracuseStep 1475371 = 2213057) B2213057
theorem B4424507 : Blo 1032607 4424507 := bstep (se 1 (by rfl) ⟨3318380, by rfl⟩ : syracuseStep 4424507 = 6636761) B6636761
theorem B1311547 : Blo 1032607 1311547 := bstep (se 1 (by rfl) ⟨983660, by rfl⟩ : syracuseStep 1311547 = 1967321) B1967321
theorem B4195219 : Blo 1032607 4195219 := bstep (se 1 (by rfl) ⟨3146414, by rfl⟩ : syracuseStep 4195219 = 6292829) B6292829
theorem B3933137 : Blo 1032607 3933137 := bstep (se 2 (by rfl) ⟨1474926, by rfl⟩ : syracuseStep 3933137 = 2949853) B2949853
theorem B5899229 : Blo 1032607 5899229 := bstep (se 3 (by rfl) ⟨1106105, by rfl⟩ : syracuseStep 5899229 = 2212211) B2212211
theorem B1475599 : Blo 1032607 1475599 := bstep (se 1 (by rfl) ⟨1106699, by rfl⟩ : syracuseStep 1475599 = 2213399) B2213399
theorem B4195415 : Blo 1032607 4195415 := bstep (se 1 (by rfl) ⟨3146561, by rfl⟩ : syracuseStep 4195415 = 6293123) B6293123
theorem B2327687 : Blo 1032607 2327687 := bstep (se 1 (by rfl) ⟨1745765, by rfl⟩ : syracuseStep 2327687 = 3491531) B3491531
theorem B2327867 : Blo 1032607 2327867 := bstep (se 1 (by rfl) ⟨1745900, by rfl⟩ : syracuseStep 2327867 = 3491801) B3491801
theorem B1967419 : Blo 1032607 1967419 := bstep (se 1 (by rfl) ⟨1475564, by rfl⟩ : syracuseStep 1967419 = 2951129) B2951129
theorem B3933593 : Blo 1032607 3933593 := bstep (se 2 (by rfl) ⟨1475097, by rfl⟩ : syracuseStep 3933593 = 2950195) B2950195
theorem B2327993 : Blo 1032607 2327993 := bstep (se 2 (by rfl) ⟨872997, by rfl⟩ : syracuseStep 2327993 = 1745995) B1745995
theorem B2623063 : Blo 1032607 2623063 := bstep (se 1 (by rfl) ⟨1967297, by rfl⟩ : syracuseStep 2623063 = 3934595) B3934595
theorem B4916855 : Blo 1032607 4916855 := bstep (se 1 (by rfl) ⟨3687641, by rfl⟩ : syracuseStep 4916855 = 7375283) B7375283
theorem B11798135 : Blo 1032607 11798135 := bstep (se 1 (by rfl) ⟨8848601, by rfl⟩ : syracuseStep 11798135 = 17697203) B17697203
theorem B7079653 : Blo 1032607 7079653 := bstep (se 4 (by rfl) ⟨663717, by rfl⟩ : syracuseStep 7079653 = 1327435) B1327435
theorem B2328335 : Blo 1032607 2328335 := bstep (se 1 (by rfl) ⟨1746251, by rfl⟩ : syracuseStep 2328335 = 3492503) B3492503
theorem B2328353 : Blo 1032607 2328353 := bstep (se 2 (by rfl) ⟨873132, by rfl⟩ : syracuseStep 2328353 = 1746265) B1746265
theorem B1967905 : Blo 1032607 1967905 := bstep (se 2 (by rfl) ⟨737964, by rfl⟩ : syracuseStep 1967905 = 1475929) B1475929
theorem B2623367 : Blo 1032607 2623367 := bstep (se 1 (by rfl) ⟨1967525, by rfl⟩ : syracuseStep 2623367 = 3935051) B3935051
theorem B11175833 : Blo 1032607 11175833 := bstep (se 2 (by rfl) ⟨4190937, by rfl⟩ : syracuseStep 11175833 = 8381875) B8381875
theorem B3311513 : Blo 1032607 3311513 := bstep (se 2 (by rfl) ⟨1241817, by rfl⟩ : syracuseStep 3311513 = 2483635) B2483635
theorem B2623499 : Blo 1032607 2623499 := bstep (se 1 (by rfl) ⟨1967624, by rfl⟩ : syracuseStep 2623499 = 3935249) B3935249
theorem B2951255 : Blo 1032607 2951255 := bstep (se 1 (by rfl) ⟨2213441, by rfl⟩ : syracuseStep 2951255 = 4426883) B4426883
theorem B2328695 : Blo 1032607 2328695 := bstep (se 1 (by rfl) ⟨1746521, by rfl⟩ : syracuseStep 2328695 = 3493043) B3493043
theorem B2328875 : Blo 1032607 2328875 := bstep (se 1 (by rfl) ⟨1746656, by rfl⟩ : syracuseStep 2328875 = 3493313) B3493313
theorem B5245235 : Blo 1032607 5245235 := bstep (se 1 (by rfl) ⟨3933926, by rfl⟩ : syracuseStep 5245235 = 7867853) B7867853
theorem B1575227 : Blo 1032607 1575227 := bstep (se 1 (by rfl) ⟨1181420, by rfl⟩ : syracuseStep 1575227 = 2362841) B2362841
theorem B3934763 : Blo 1032607 3934763 := bstep (se 1 (by rfl) ⟨2951072, by rfl⟩ : syracuseStep 3934763 = 5902145) B5902145
theorem B5245559 : Blo 1032607 5245559 := bstep (se 1 (by rfl) ⟨3934169, by rfl⟩ : syracuseStep 5245559 = 7868339) B7868339
theorem B2329235 : Blo 1032607 2329235 := bstep (se 1 (by rfl) ⟨1746926, by rfl⟩ : syracuseStep 2329235 = 3493853) B3493853
theorem B7080641 : Blo 1032607 7080641 := bstep (se 2 (by rfl) ⟨2655240, by rfl⟩ : syracuseStep 7080641 = 5310481) B5310481
theorem B2329289 : Blo 1032607 2329289 := bstep (se 2 (by rfl) ⟨873483, by rfl⟩ : syracuseStep 2329289 = 1746967) B1746967
theorem B3148555 : Blo 1032607 3148555 := bstep (se 1 (by rfl) ⟨2361416, by rfl⟩ : syracuseStep 3148555 = 4722833) B4722833
theorem B2592011 : Blo 1032607 2592011 := bstep (se 1 (by rfl) ⟨1944008, by rfl⟩ : syracuseStep 2592011 = 3888017) B3888017
theorem B5901619 : Blo 1032607 5901619 := bstep (se 1 (by rfl) ⟨4426214, by rfl⟩ : syracuseStep 5901619 = 8852429) B8852429
theorem B8391995 : Blo 1032607 8391995 := bstep (se 1 (by rfl) ⟨6293996, by rfl⟩ : syracuseStep 8391995 = 12587993) B12587993
theorem B2329991 : Blo 1032607 2329991 := bstep (se 1 (by rfl) ⟨1747493, by rfl⟩ : syracuseStep 2329991 = 3494987) B3494987
theorem B2330171 : Blo 1032607 2330171 := bstep (se 1 (by rfl) ⟨1747628, by rfl⟩ : syracuseStep 2330171 = 3495257) B3495257
theorem B5246531 : Blo 1032607 5246531 := bstep (se 1 (by rfl) ⟨3934898, by rfl⟩ : syracuseStep 5246531 = 7869797) B7869797
theorem B5312087 : Blo 1032607 5312087 := bstep (se 1 (by rfl) ⟨3984065, by rfl⟩ : syracuseStep 5312087 = 7968131) B7968131
theorem B2330297 : Blo 1032607 2330297 := bstep (se 2 (by rfl) ⟨873861, by rfl⟩ : syracuseStep 2330297 = 1747723) B1747723
theorem B1118011 : Blo 1032607 1118011 := bstep (se 1 (by rfl) ⟨838508, by rfl⟩ : syracuseStep 1118011 = 1677017) B1677017
theorem B5967731 : Blo 1032607 5967731 := bstep (se 1 (by rfl) ⟨4475798, by rfl⟩ : syracuseStep 5967731 = 8951597) B8951597
theorem B5246855 : Blo 1032607 5246855 := bstep (se 1 (by rfl) ⟨3935141, by rfl⟩ : syracuseStep 5246855 = 7870283) B7870283
theorem B16748441 : Blo 1032607 16748441 := bstep (se 2 (by rfl) ⟨6280665, by rfl⟩ : syracuseStep 16748441 = 12561331) B12561331
theorem B2330639 : Blo 1032607 2330639 := bstep (se 1 (by rfl) ⟨1747979, by rfl⟩ : syracuseStep 2330639 = 3495959) B3495959
theorem B2330657 : Blo 1032607 2330657 := bstep (se 2 (by rfl) ⟨873996, by rfl⟩ : syracuseStep 2330657 = 1747993) B1747993
theorem B3150199 : Blo 1032607 3150199 := bstep (se 1 (by rfl) ⟨2362649, by rfl⟩ : syracuseStep 3150199 = 4725299) B4725299
theorem B2330999 : Blo 1032607 2330999 := bstep (se 1 (by rfl) ⟨1748249, by rfl⟩ : syracuseStep 2330999 = 3496499) B3496499
theorem B6295943 : Blo 1032607 6295943 := bstep (se 1 (by rfl) ⟨4721957, by rfl⟩ : syracuseStep 6295943 = 9443915) B9443915
theorem B2331179 : Blo 1032607 2331179 := bstep (se 1 (by rfl) ⟨1748384, by rfl⟩ : syracuseStep 2331179 = 3496769) B3496769
theorem B6296237 : Blo 1032607 6296237 := bstep (se 3 (by rfl) ⟨1180544, by rfl⟩ : syracuseStep 6296237 = 2361089) B2361089
theorem B5903077 : Blo 1032607 5903077 := bstep (se 4 (by rfl) ⟨553413, by rfl⟩ : syracuseStep 5903077 = 1106827) B1106827
theorem B11932505 : Blo 1032607 11932505 := bstep (se 2 (by rfl) ⟨4474689, by rfl⟩ : syracuseStep 11932505 = 8949379) B8949379
theorem B2331539 : Blo 1032607 2331539 := bstep (se 1 (by rfl) ⟨1748654, by rfl⟩ : syracuseStep 2331539 = 3497309) B3497309
theorem B2331593 : Blo 1032607 2331593 := bstep (se 2 (by rfl) ⟨874347, by rfl⟩ : syracuseStep 2331593 = 1748695) B1748695
theorem B2987275 : Blo 1032607 2987275 := bstep (se 1 (by rfl) ⟨2240456, by rfl⟩ : syracuseStep 2987275 = 4480913) B4480913
theorem B13276547 : Blo 1032607 13276547 := bstep (se 1 (by rfl) ⟨9957410, by rfl⟩ : syracuseStep 13276547 = 19914821) B19914821
theorem B1513033 : Blo 1032607 1513033 := bstep (se 2 (by rfl) ⟨567387, by rfl⟩ : syracuseStep 1513033 = 1134775) B1134775
theorem B2332295 : Blo 1032607 2332295 := bstep (se 1 (by rfl) ⟨1749221, by rfl⟩ : syracuseStep 2332295 = 3498443) B3498443
theorem B32315057 : Blo 1032607 32315057 := bstep (se 2 (by rfl) ⟨12118146, by rfl⟩ : syracuseStep 32315057 = 24236293) B24236293
theorem B2987929 : Blo 1032607 2987929 := bstep (se 2 (by rfl) ⟨1120473, by rfl⟩ : syracuseStep 2987929 = 2240947) B2240947
theorem B1742863 : Blo 1032607 1742863 := bstep (se 1 (by rfl) ⟨1307147, by rfl⟩ : syracuseStep 1742863 = 2614295) B2614295
theorem B3315755 : Blo 1032607 3315755 := bstep (se 1 (by rfl) ⟨2486816, by rfl⟩ : syracuseStep 3315755 = 4973633) B4973633
theorem B27203701 : Blo 1032607 27203701 := bstep (se 5 (by rfl) ⟨1275173, by rfl⟩ : syracuseStep 27203701 = 2550347) B2550347
theorem B1743403 : Blo 1032607 1743403 := bstep (se 1 (by rfl) ⟨1307552, by rfl⟩ : syracuseStep 1743403 = 2615105) B2615105
theorem B11770433 : Blo 1032607 11770433 := bstep (se 2 (by rfl) ⟨4413912, by rfl⟩ : syracuseStep 11770433 = 8827825) B8827825
theorem B1743545 : Blo 1032607 1743545 := bstep (se 2 (by rfl) ⟨653829, by rfl⟩ : syracuseStep 1743545 = 1307659) B1307659
theorem B2792339 : Blo 1032607 2792339 := bstep (se 1 (by rfl) ⟨2094254, by rfl⟩ : syracuseStep 2792339 = 4188509) B4188509
theorem B1744247 : Blo 1032607 1744247 := bstep (se 1 (by rfl) ⟨1308185, by rfl⟩ : syracuseStep 1744247 = 2616371) B2616371
theorem B7085839 : Blo 1032607 7085839 := bstep (se 1 (by rfl) ⟨5314379, by rfl⟩ : syracuseStep 7085839 = 10628759) B10628759
theorem B1744699 : Blo 1032607 1744699 := bstep (se 1 (by rfl) ⟨1308524, by rfl⟩ : syracuseStep 1744699 = 2617049) B2617049
theorem B1744841 : Blo 1032607 1744841 := bstep (se 2 (by rfl) ⟨654315, by rfl⟩ : syracuseStep 1744841 = 1308631) B1308631
theorem B21537089 : Blo 1032607 21537089 := bstep (se 2 (by rfl) ⟨8076408, by rfl⟩ : syracuseStep 21537089 = 16152817) B16152817
theorem B22389209 : Blo 1032607 22389209 := bstep (se 2 (by rfl) ⟨8395953, by rfl⟩ : syracuseStep 22389209 = 16791907) B16791907
theorem B1548935 : Blo 1032607 1548935 := bstep (se 1 (by rfl) ⟨1161701, by rfl⟩ : syracuseStep 1548935 = 2323403) B2323403
theorem B1745543 : Blo 1032607 1745543 := bstep (se 1 (by rfl) ⟨1309157, by rfl⟩ : syracuseStep 1745543 = 2618315) B2618315
theorem B1548971 : Blo 1032607 1548971 := bstep (se 1 (by rfl) ⟨1161728, by rfl⟩ : syracuseStep 1548971 = 2323457) B2323457
theorem B1549001 : Blo 1032607 1549001 := bstep (se 2 (by rfl) ⟨580875, by rfl⟩ : syracuseStep 1549001 = 1161751) B1161751
theorem B1549115 : Blo 1032607 1549115 := bstep (se 1 (by rfl) ⟨1161836, by rfl⟩ : syracuseStep 1549115 = 2323673) B2323673
theorem B1549175 : Blo 1032607 1549175 := bstep (se 1 (by rfl) ⟨1161881, by rfl⟩ : syracuseStep 1549175 = 2323763) B2323763
theorem B1549199 : Blo 1032607 1549199 := bstep (se 1 (by rfl) ⟨1161899, by rfl⟩ : syracuseStep 1549199 = 2323799) B2323799
theorem B1549241 : Blo 1032607 1549241 := bstep (se 2 (by rfl) ⟨580965, by rfl⟩ : syracuseStep 1549241 = 1161931) B1161931
theorem B1549319 : Blo 1032607 1549319 := bstep (se 1 (by rfl) ⟨1161989, by rfl⟩ : syracuseStep 1549319 = 2323979) B2323979
theorem B1549355 : Blo 1032607 1549355 := bstep (se 1 (by rfl) ⟨1162016, by rfl⟩ : syracuseStep 1549355 = 2324033) B2324033
theorem B1549385 : Blo 1032607 1549385 := bstep (se 2 (by rfl) ⟨581019, by rfl⟩ : syracuseStep 1549385 = 1162039) B1162039
theorem B1549499 : Blo 1032607 1549499 := bstep (se 1 (by rfl) ⟨1162124, by rfl⟩ : syracuseStep 1549499 = 2324249) B2324249
theorem B1549559 : Blo 1032607 1549559 := bstep (se 1 (by rfl) ⟨1162169, by rfl⟩ : syracuseStep 1549559 = 2324339) B2324339
theorem B1549583 : Blo 1032607 1549583 := bstep (se 1 (by rfl) ⟨1162187, by rfl⟩ : syracuseStep 1549583 = 2324375) B2324375
theorem B1746191 : Blo 1032607 1746191 := bstep (se 1 (by rfl) ⟨1309643, by rfl⟩ : syracuseStep 1746191 = 2619287) B2619287
theorem B2794781 : Blo 1032607 2794781 := bstep (se 3 (by rfl) ⟨524021, by rfl⟩ : syracuseStep 2794781 = 1048043) B1048043
theorem B1549625 : Blo 1032607 1549625 := bstep (se 2 (by rfl) ⟨581109, by rfl⟩ : syracuseStep 1549625 = 1162219) B1162219
theorem B23864635 : Blo 1032607 23864635 := bstep (se 1 (by rfl) ⟨17898476, by rfl⟩ : syracuseStep 23864635 = 35796953) B35796953
theorem B1549703 : Blo 1032607 1549703 := bstep (se 1 (by rfl) ⟨1162277, by rfl⟩ : syracuseStep 1549703 = 2324555) B2324555
theorem B1549739 : Blo 1032607 1549739 := bstep (se 1 (by rfl) ⟨1162304, by rfl⟩ : syracuseStep 1549739 = 2324609) B2324609
theorem B1549769 : Blo 1032607 1549769 := bstep (se 2 (by rfl) ⟨581163, by rfl⟩ : syracuseStep 1549769 = 1162327) B1162327
theorem B1549883 : Blo 1032607 1549883 := bstep (se 1 (by rfl) ⟨1162412, by rfl⟩ : syracuseStep 1549883 = 2324825) B2324825
theorem B1549943 : Blo 1032607 1549943 := bstep (se 1 (by rfl) ⟨1162457, by rfl⟩ : syracuseStep 1549943 = 2324915) B2324915
theorem B1549967 : Blo 1032607 1549967 := bstep (se 1 (by rfl) ⟨1162475, by rfl⟩ : syracuseStep 1549967 = 2324951) B2324951
theorem B2795161 : Blo 1032607 2795161 := bstep (se 2 (by rfl) ⟨1048185, by rfl⟩ : syracuseStep 2795161 = 2096371) B2096371
theorem B1550009 : Blo 1032607 1550009 := bstep (se 2 (by rfl) ⟨581253, by rfl⟩ : syracuseStep 1550009 = 1162507) B1162507
theorem B1550087 : Blo 1032607 1550087 := bstep (se 1 (by rfl) ⟨1162565, by rfl⟩ : syracuseStep 1550087 = 2325131) B2325131
theorem B1550123 : Blo 1032607 1550123 := bstep (se 1 (by rfl) ⟨1162592, by rfl⟩ : syracuseStep 1550123 = 2325185) B2325185
theorem B1746731 : Blo 1032607 1746731 := bstep (se 1 (by rfl) ⟨1310048, by rfl⟩ : syracuseStep 1746731 = 2620097) B2620097
theorem B6367027 : Blo 1032607 6367027 := bstep (se 1 (by rfl) ⟨4775270, by rfl⟩ : syracuseStep 6367027 = 9550541) B9550541
theorem B1550153 : Blo 1032607 1550153 := bstep (se 2 (by rfl) ⟨581307, by rfl⟩ : syracuseStep 1550153 = 1162615) B1162615
theorem B10758041 : Blo 1032607 10758041 := bstep (se 2 (by rfl) ⟨4034265, by rfl⟩ : syracuseStep 10758041 = 8068531) B8068531
theorem B1550267 : Blo 1032607 1550267 := bstep (se 1 (by rfl) ⟨1162700, by rfl⟩ : syracuseStep 1550267 = 2325401) B2325401
theorem B1550327 : Blo 1032607 1550327 := bstep (se 1 (by rfl) ⟨1162745, by rfl⟩ : syracuseStep 1550327 = 2325491) B2325491
theorem B1550351 : Blo 1032607 1550351 := bstep (se 1 (by rfl) ⟨1162763, by rfl⟩ : syracuseStep 1550351 = 2325527) B2325527
theorem B20195351 : Blo 1032607 20195351 := bstep (se 1 (by rfl) ⟨15146513, by rfl⟩ : syracuseStep 20195351 = 30293027) B30293027
theorem B1550393 : Blo 1032607 1550393 := bstep (se 2 (by rfl) ⟨581397, by rfl⟩ : syracuseStep 1550393 = 1162795) B1162795
theorem B1550471 : Blo 1032607 1550471 := bstep (se 1 (by rfl) ⟨1162853, by rfl⟩ : syracuseStep 1550471 = 2325707) B2325707
theorem B1550507 : Blo 1032607 1550507 := bstep (se 1 (by rfl) ⟨1162880, by rfl⟩ : syracuseStep 1550507 = 2325761) B2325761
theorem B1747129 : Blo 1032607 1747129 := bstep (se 2 (by rfl) ⟨655173, by rfl⟩ : syracuseStep 1747129 = 1310347) B1310347
theorem B1550537 : Blo 1032607 1550537 := bstep (se 2 (by rfl) ⟨581451, by rfl⟩ : syracuseStep 1550537 = 1162903) B1162903
theorem B1550651 : Blo 1032607 1550651 := bstep (se 1 (by rfl) ⟨1162988, by rfl⟩ : syracuseStep 1550651 = 2325977) B2325977
theorem B1550711 : Blo 1032607 1550711 := bstep (se 1 (by rfl) ⟨1163033, by rfl⟩ : syracuseStep 1550711 = 2326067) B2326067
theorem B1550735 : Blo 1032607 1550735 := bstep (se 1 (by rfl) ⟨1163051, by rfl⟩ : syracuseStep 1550735 = 2326103) B2326103
theorem B1550777 : Blo 1032607 1550777 := bstep (se 2 (by rfl) ⟨581541, by rfl⟩ : syracuseStep 1550777 = 1163083) B1163083
theorem B1550855 : Blo 1032607 1550855 := bstep (se 1 (by rfl) ⟨1163141, by rfl⟩ : syracuseStep 1550855 = 2326283) B2326283
theorem B1550891 : Blo 1032607 1550891 := bstep (se 1 (by rfl) ⟨1163168, by rfl⟩ : syracuseStep 1550891 = 2326337) B2326337
theorem B1550921 : Blo 1032607 1550921 := bstep (se 2 (by rfl) ⟨581595, by rfl⟩ : syracuseStep 1550921 = 1163191) B1163191
theorem B1551035 : Blo 1032607 1551035 := bstep (se 1 (by rfl) ⟨1163276, by rfl⟩ : syracuseStep 1551035 = 2326553) B2326553
theorem B1551095 : Blo 1032607 1551095 := bstep (se 1 (by rfl) ⟨1163321, by rfl⟩ : syracuseStep 1551095 = 2326643) B2326643
theorem B1551119 : Blo 1032607 1551119 := bstep (se 1 (by rfl) ⟨1163339, by rfl⟩ : syracuseStep 1551119 = 2326679) B2326679
theorem B1551161 : Blo 1032607 1551161 := bstep (se 2 (by rfl) ⟨581685, by rfl⟩ : syracuseStep 1551161 = 1163371) B1163371
theorem B1747831 : Blo 1032607 1747831 := bstep (se 1 (by rfl) ⟨1310873, by rfl⟩ : syracuseStep 1747831 = 2621747) B2621747
theorem B1551239 : Blo 1032607 1551239 := bstep (se 1 (by rfl) ⟨1163429, by rfl⟩ : syracuseStep 1551239 = 2326859) B2326859
theorem B1551275 : Blo 1032607 1551275 := bstep (se 1 (by rfl) ⟨1163456, by rfl⟩ : syracuseStep 1551275 = 2326913) B2326913
theorem B2206649 : Blo 1032607 2206649 := bstep (se 2 (by rfl) ⟨827493, by rfl⟩ : syracuseStep 2206649 = 1654987) B1654987
theorem B1551305 : Blo 1032607 1551305 := bstep (se 2 (by rfl) ⟨581739, by rfl⟩ : syracuseStep 1551305 = 1163479) B1163479
theorem B1551419 : Blo 1032607 1551419 := bstep (se 1 (by rfl) ⟨1163564, by rfl⟩ : syracuseStep 1551419 = 2327129) B2327129
theorem B1748027 : Blo 1032607 1748027 := bstep (se 1 (by rfl) ⟨1311020, by rfl⟩ : syracuseStep 1748027 = 2622041) B2622041
theorem B19868759 : Blo 1032607 19868759 := bstep (se 1 (by rfl) ⟨14901569, by rfl⟩ : syracuseStep 19868759 = 29803139) B29803139
theorem B1551479 : Blo 1032607 1551479 := bstep (se 1 (by rfl) ⟨1163609, by rfl⟩ : syracuseStep 1551479 = 2327219) B2327219
theorem B1551503 : Blo 1032607 1551503 := bstep (se 1 (by rfl) ⟨1163627, by rfl⟩ : syracuseStep 1551503 = 2327255) B2327255
theorem B1551545 : Blo 1032607 1551545 := bstep (se 2 (by rfl) ⟨581829, by rfl⟩ : syracuseStep 1551545 = 1163659) B1163659
theorem B13282541 : Blo 1032607 13282541 := bstep (se 3 (by rfl) ⟨2490476, by rfl⟩ : syracuseStep 13282541 = 4980953) B4980953
theorem B1551623 : Blo 1032607 1551623 := bstep (se 1 (by rfl) ⟨1163717, by rfl⟩ : syracuseStep 1551623 = 2327435) B2327435
theorem B1551659 : Blo 1032607 1551659 := bstep (se 1 (by rfl) ⟨1163744, by rfl⟩ : syracuseStep 1551659 = 2327489) B2327489
theorem B1551689 : Blo 1032607 1551689 := bstep (se 2 (by rfl) ⟨581883, by rfl⟩ : syracuseStep 1551689 = 1163767) B1163767
theorem B31894883 : Blo 1032607 31894883 := bstep (se 1 (by rfl) ⟨23921162, by rfl⟩ : syracuseStep 31894883 = 47842325) B47842325
theorem B16166279 : Blo 1032607 16166279 := bstep (se 1 (by rfl) ⟨12124709, by rfl⟩ : syracuseStep 16166279 = 24249419) B24249419
theorem B1551803 : Blo 1032607 1551803 := bstep (se 1 (by rfl) ⟨1163852, by rfl⟩ : syracuseStep 1551803 = 2327705) B2327705
theorem B1748425 : Blo 1032607 1748425 := bstep (se 2 (by rfl) ⟨655659, by rfl⟩ : syracuseStep 1748425 = 1311319) B1311319
theorem B1551863 : Blo 1032607 1551863 := bstep (se 1 (by rfl) ⟨1163897, by rfl⟩ : syracuseStep 1551863 = 2327795) B2327795
theorem B1551887 : Blo 1032607 1551887 := bstep (se 1 (by rfl) ⟨1163915, by rfl⟩ : syracuseStep 1551887 = 2327831) B2327831
theorem B3485213 : Blo 1032607 3485213 := bstep (se 3 (by rfl) ⟨653477, by rfl⟩ : syracuseStep 3485213 = 1306955) B1306955
theorem B1551929 : Blo 1032607 1551929 := bstep (se 2 (by rfl) ⟨581973, by rfl⟩ : syracuseStep 1551929 = 1163947) B1163947
theorem B1552007 : Blo 1032607 1552007 := bstep (se 1 (by rfl) ⟨1164005, by rfl⟩ : syracuseStep 1552007 = 2328011) B2328011
theorem B1552043 : Blo 1032607 1552043 := bstep (se 1 (by rfl) ⟨1164032, by rfl⟩ : syracuseStep 1552043 = 2328065) B2328065
theorem B21507763 : Blo 1032607 21507763 := bstep (se 1 (by rfl) ⟨16130822, by rfl⟩ : syracuseStep 21507763 = 32261645) B32261645
theorem B1552073 : Blo 1032607 1552073 := bstep (se 2 (by rfl) ⟨582027, by rfl⟩ : syracuseStep 1552073 = 1164055) B1164055
theorem B2207503 : Blo 1032607 2207503 := bstep (se 1 (by rfl) ⟨1655627, by rfl⟩ : syracuseStep 2207503 = 3311255) B3311255
theorem B1552187 : Blo 1032607 1552187 := bstep (se 1 (by rfl) ⟨1164140, by rfl⟩ : syracuseStep 1552187 = 2328281) B2328281
theorem B1552247 : Blo 1032607 1552247 := bstep (se 1 (by rfl) ⟨1164185, by rfl⟩ : syracuseStep 1552247 = 2328371) B2328371
theorem B1552271 : Blo 1032607 1552271 := bstep (se 1 (by rfl) ⟨1164203, by rfl⟩ : syracuseStep 1552271 = 2328407) B2328407
theorem B1552313 : Blo 1032607 1552313 := bstep (se 2 (by rfl) ⟨582117, by rfl⟩ : syracuseStep 1552313 = 1164235) B1164235
theorem B1552391 : Blo 1032607 1552391 := bstep (se 1 (by rfl) ⟨1164293, by rfl⟩ : syracuseStep 1552391 = 2328587) B2328587
theorem B1552427 : Blo 1032607 1552427 := bstep (se 1 (by rfl) ⟨1164320, by rfl⟩ : syracuseStep 1552427 = 2328641) B2328641
theorem B1552457 : Blo 1032607 1552457 := bstep (se 2 (by rfl) ⟨582171, by rfl⟩ : syracuseStep 1552457 = 1164343) B1164343
theorem B1749127 : Blo 1032607 1749127 := bstep (se 1 (by rfl) ⟨1311845, by rfl⟩ : syracuseStep 1749127 = 2623691) B2623691
theorem B1552571 : Blo 1032607 1552571 := bstep (se 1 (by rfl) ⟨1164428, by rfl⟩ : syracuseStep 1552571 = 2328857) B2328857
theorem B1552631 : Blo 1032607 1552631 := bstep (se 1 (by rfl) ⟨1164473, by rfl⟩ : syracuseStep 1552631 = 2328947) B2328947
theorem B1552655 : Blo 1032607 1552655 := bstep (se 1 (by rfl) ⟨1164491, by rfl⟩ : syracuseStep 1552655 = 2328983) B2328983
theorem B1552697 : Blo 1032607 1552697 := bstep (se 2 (by rfl) ⟨582261, by rfl⟩ : syracuseStep 1552697 = 1164523) B1164523
theorem B1552775 : Blo 1032607 1552775 := bstep (se 1 (by rfl) ⟨1164581, by rfl⟩ : syracuseStep 1552775 = 2329163) B2329163
theorem B1552811 : Blo 1032607 1552811 := bstep (se 1 (by rfl) ⟨1164608, by rfl⟩ : syracuseStep 1552811 = 2329217) B2329217
theorem B1552841 : Blo 1032607 1552841 := bstep (se 2 (by rfl) ⟨582315, by rfl⟩ : syracuseStep 1552841 = 1164631) B1164631
theorem B1552955 : Blo 1032607 1552955 := bstep (se 1 (by rfl) ⟨1164716, by rfl⟩ : syracuseStep 1552955 = 2329433) B2329433
theorem B1553015 : Blo 1032607 1553015 := bstep (se 1 (by rfl) ⟨1164761, by rfl⟩ : syracuseStep 1553015 = 2329523) B2329523
theorem B1553039 : Blo 1032607 1553039 := bstep (se 1 (by rfl) ⟨1164779, by rfl⟩ : syracuseStep 1553039 = 2329559) B2329559
theorem B1553081 : Blo 1032607 1553081 := bstep (se 2 (by rfl) ⟨582405, by rfl⟩ : syracuseStep 1553081 = 1164811) B1164811
theorem B1553159 : Blo 1032607 1553159 := bstep (se 1 (by rfl) ⟨1164869, by rfl⟩ : syracuseStep 1553159 = 2329739) B2329739
theorem B2798369 : Blo 1032607 2798369 := bstep (se 2 (by rfl) ⟨1049388, by rfl⟩ : syracuseStep 2798369 = 2098777) B2098777
theorem B1553195 : Blo 1032607 1553195 := bstep (se 1 (by rfl) ⟨1164896, by rfl⟩ : syracuseStep 1553195 = 2329793) B2329793
theorem B1553225 : Blo 1032607 1553225 := bstep (se 2 (by rfl) ⟨582459, by rfl⟩ : syracuseStep 1553225 = 1164919) B1164919
theorem B3486617 : Blo 1032607 3486617 := bstep (se 2 (by rfl) ⟨1307481, by rfl⟩ : syracuseStep 3486617 = 2614963) B2614963
theorem B1553339 : Blo 1032607 1553339 := bstep (se 1 (by rfl) ⟨1165004, by rfl⟩ : syracuseStep 1553339 = 2330009) B2330009
theorem B1553399 : Blo 1032607 1553399 := bstep (se 1 (by rfl) ⟨1165049, by rfl⟩ : syracuseStep 1553399 = 2330099) B2330099
theorem B1553423 : Blo 1032607 1553423 := bstep (se 1 (by rfl) ⟨1165067, by rfl⟩ : syracuseStep 1553423 = 2330135) B2330135
theorem B2798621 : Blo 1032607 2798621 := bstep (se 3 (by rfl) ⟨524741, by rfl⟩ : syracuseStep 2798621 = 1049483) B1049483
theorem B1553465 : Blo 1032607 1553465 := bstep (se 2 (by rfl) ⟨582549, by rfl⟩ : syracuseStep 1553465 = 1165099) B1165099
theorem B1553543 : Blo 1032607 1553543 := bstep (se 1 (by rfl) ⟨1165157, by rfl⟩ : syracuseStep 1553543 = 2330315) B2330315
theorem B1553579 : Blo 1032607 1553579 := bstep (se 1 (by rfl) ⟨1165184, by rfl⟩ : syracuseStep 1553579 = 2330369) B2330369
theorem B1553609 : Blo 1032607 1553609 := bstep (se 2 (by rfl) ⟨582603, by rfl⟩ : syracuseStep 1553609 = 1165207) B1165207
theorem B1553723 : Blo 1032607 1553723 := bstep (se 1 (by rfl) ⟨1165292, by rfl⟩ : syracuseStep 1553723 = 2330585) B2330585
theorem B1553783 : Blo 1032607 1553783 := bstep (se 1 (by rfl) ⟨1165337, by rfl⟩ : syracuseStep 1553783 = 2330675) B2330675
theorem B1553807 : Blo 1032607 1553807 := bstep (se 1 (by rfl) ⟨1165355, by rfl⟩ : syracuseStep 1553807 = 2330711) B2330711
theorem B1553849 : Blo 1032607 1553849 := bstep (se 2 (by rfl) ⟨582693, by rfl⟩ : syracuseStep 1553849 = 1165387) B1165387
theorem B14890499 : Blo 1032607 14890499 := bstep (se 1 (by rfl) ⟨11167874, by rfl⟩ : syracuseStep 14890499 = 22335749) B22335749
theorem B1553927 : Blo 1032607 1553927 := bstep (se 1 (by rfl) ⟨1165445, by rfl⟩ : syracuseStep 1553927 = 2330891) B2330891
theorem B1553963 : Blo 1032607 1553963 := bstep (se 1 (by rfl) ⟨1165472, by rfl⟩ : syracuseStep 1553963 = 2330945) B2330945
theorem B1553993 : Blo 1032607 1553993 := bstep (se 2 (by rfl) ⟨582747, by rfl⟩ : syracuseStep 1553993 = 1165495) B1165495
theorem B3487319 : Blo 1032607 3487319 := bstep (se 1 (by rfl) ⟨2615489, by rfl⟩ : syracuseStep 3487319 = 5230979) B5230979
theorem B1554107 : Blo 1032607 1554107 := bstep (se 1 (by rfl) ⟨1165580, by rfl⟩ : syracuseStep 1554107 = 2331161) B2331161
theorem B1554167 : Blo 1032607 1554167 := bstep (se 1 (by rfl) ⟨1165625, by rfl⟩ : syracuseStep 1554167 = 2331251) B2331251
theorem B1554191 : Blo 1032607 1554191 := bstep (se 1 (by rfl) ⟨1165643, by rfl⟩ : syracuseStep 1554191 = 2331287) B2331287
theorem B1554233 : Blo 1032607 1554233 := bstep (se 2 (by rfl) ⟨582837, by rfl⟩ : syracuseStep 1554233 = 1165675) B1165675
theorem B1554311 : Blo 1032607 1554311 := bstep (se 1 (by rfl) ⟨1165733, by rfl⟩ : syracuseStep 1554311 = 2331467) B2331467
theorem B5584787 : Blo 1032607 5584787 := bstep (se 1 (by rfl) ⟨4188590, by rfl⟩ : syracuseStep 5584787 = 8377181) B8377181
theorem B1554347 : Blo 1032607 1554347 := bstep (se 1 (by rfl) ⟨1165760, by rfl⟩ : syracuseStep 1554347 = 2331521) B2331521
theorem B1554377 : Blo 1032607 1554377 := bstep (se 2 (by rfl) ⟨582891, by rfl⟩ : syracuseStep 1554377 = 1165783) B1165783
theorem B4962269 : Blo 1032607 4962269 := bstep (se 3 (by rfl) ⟨930425, by rfl⟩ : syracuseStep 4962269 = 1860851) B1860851
theorem B1554491 : Blo 1032607 1554491 := bstep (se 1 (by rfl) ⟨1165868, by rfl⟩ : syracuseStep 1554491 = 2331737) B2331737
theorem B3487805 : Blo 1032607 3487805 := bstep (se 3 (by rfl) ⟨653963, by rfl⟩ : syracuseStep 3487805 = 1307927) B1307927
theorem B1554551 : Blo 1032607 1554551 := bstep (se 1 (by rfl) ⟨1165913, by rfl⟩ : syracuseStep 1554551 = 2331827) B2331827
theorem B1554575 : Blo 1032607 1554575 := bstep (se 1 (by rfl) ⟨1165931, by rfl⟩ : syracuseStep 1554575 = 2331863) B2331863
theorem B1554617 : Blo 1032607 1554617 := bstep (se 2 (by rfl) ⟨582981, by rfl⟩ : syracuseStep 1554617 = 1165963) B1165963
theorem B1554695 : Blo 1032607 1554695 := bstep (se 1 (by rfl) ⟨1166021, by rfl⟩ : syracuseStep 1554695 = 2332043) B2332043
theorem B1554731 : Blo 1032607 1554731 := bstep (se 1 (by rfl) ⟨1166048, by rfl⟩ : syracuseStep 1554731 = 2332097) B2332097
theorem B1554761 : Blo 1032607 1554761 := bstep (se 2 (by rfl) ⟨583035, by rfl⟩ : syracuseStep 1554761 = 1166071) B1166071
theorem B6732179 : Blo 1032607 6732179 := bstep (se 1 (by rfl) ⟨5049134, by rfl⟩ : syracuseStep 6732179 = 10098269) B10098269
theorem B1554875 : Blo 1032607 1554875 := bstep (se 1 (by rfl) ⟨1166156, by rfl⟩ : syracuseStep 1554875 = 2332313) B2332313
theorem B1161787 : Blo 1032607 1161787 := bstep (se 1 (by rfl) ⟨871340, by rfl⟩ : syracuseStep 1161787 = 1742681) B1742681
theorem B2800187 : Blo 1032607 2800187 := bstep (se 1 (by rfl) ⟨2100140, by rfl⟩ : syracuseStep 2800187 = 4200281) B4200281
theorem B19872449 : Blo 1032607 19872449 := bstep (se 2 (by rfl) ⟨7452168, by rfl⟩ : syracuseStep 19872449 = 14904337) B14904337
theorem B2800445 : Blo 1032607 2800445 := bstep (se 3 (by rfl) ⟨525083, by rfl⟩ : syracuseStep 2800445 = 1050167) B1050167
theorem B2243513 : Blo 1032607 2243513 := bstep (se 2 (by rfl) ⟨841317, by rfl⟩ : syracuseStep 2243513 = 1682635) B1682635
theorem B1162255 : Blo 1032607 1162255 := bstep (se 1 (by rfl) ⟨871691, by rfl⟩ : syracuseStep 1162255 = 1743383) B1743383
theorem B9550871 : Blo 1032607 9550871 := bstep (se 1 (by rfl) ⟨7163153, by rfl⟩ : syracuseStep 9550871 = 14326307) B14326307
theorem B5881025 : Blo 1032607 5881025 := bstep (se 2 (by rfl) ⟨2205384, by rfl⟩ : syracuseStep 5881025 = 4410769) B4410769
theorem B6634811 : Blo 1032607 6634811 := bstep (se 1 (by rfl) ⟨4976108, by rfl⟩ : syracuseStep 6634811 = 9952217) B9952217
theorem B3489209 : Blo 1032607 3489209 := bstep (se 2 (by rfl) ⟨1308453, by rfl⟩ : syracuseStep 3489209 = 2616907) B2616907
theorem B1162759 : Blo 1032607 1162759 := bstep (se 1 (by rfl) ⟨872069, by rfl⟩ : syracuseStep 1162759 = 1744139) B1744139
theorem B1162939 : Blo 1032607 1162939 := bstep (se 1 (by rfl) ⟨872204, by rfl⟩ : syracuseStep 1162939 = 1744409) B1744409
theorem B2801441 : Blo 1032607 2801441 := bstep (se 2 (by rfl) ⟨1050540, by rfl⟩ : syracuseStep 2801441 = 2101081) B2101081
theorem B1294123 : Blo 1032607 1294123 := bstep (se 1 (by rfl) ⟨970592, by rfl⟩ : syracuseStep 1294123 = 1941185) B1941185
theorem B3489803 : Blo 1032607 3489803 := bstep (se 1 (by rfl) ⟨2617352, by rfl⟩ : syracuseStep 3489803 = 5234705) B5234705
theorem B3489911 : Blo 1032607 3489911 := bstep (se 1 (by rfl) ⟨2617433, by rfl⟩ : syracuseStep 3489911 = 5234867) B5234867
theorem B1163407 : Blo 1032607 1163407 := bstep (se 1 (by rfl) ⟨872555, by rfl⟩ : syracuseStep 1163407 = 1745111) B1745111
theorem B8732873 : Blo 1032607 8732873 := bstep (se 2 (by rfl) ⟨3274827, by rfl⟩ : syracuseStep 8732873 = 6549655) B6549655
theorem B2834731 : Blo 1032607 2834731 := bstep (se 1 (by rfl) ⟨2126048, by rfl⟩ : syracuseStep 2834731 = 4252097) B4252097
theorem B1032635 : Blo 1032607 1032635 := bstep (se 1 (by rfl) ⟨774476, by rfl⟩ : syracuseStep 1032635 = 1548953) B1548953
theorem B7848413 : Blo 1032607 7848413 := bstep (se 3 (by rfl) ⟨1471577, by rfl⟩ : syracuseStep 7848413 = 2943155) B2943155
theorem B1032711 : Blo 1032607 1032711 := bstep (se 1 (by rfl) ⟨774533, by rfl⟩ : syracuseStep 1032711 = 1549067) B1549067
theorem B1032719 : Blo 1032607 1032719 := bstep (se 1 (by rfl) ⟨774539, by rfl⟩ : syracuseStep 1032719 = 1549079) B1549079
theorem B1032763 : Blo 1032607 1032763 := bstep (se 1 (by rfl) ⟨774572, by rfl⟩ : syracuseStep 1032763 = 1549145) B1549145
theorem B1032839 : Blo 1032607 1032839 := bstep (se 1 (by rfl) ⟨774629, by rfl⟩ : syracuseStep 1032839 = 1549259) B1549259
theorem B1163911 : Blo 1032607 1163911 := bstep (se 1 (by rfl) ⟨872933, by rfl⟩ : syracuseStep 1163911 = 1745867) B1745867
theorem B1032847 : Blo 1032607 1032847 := bstep (se 1 (by rfl) ⟨774635, by rfl⟩ : syracuseStep 1032847 = 1549271) B1549271
theorem B1032891 : Blo 1032607 1032891 := bstep (se 1 (by rfl) ⟨774668, by rfl⟩ : syracuseStep 1032891 = 1549337) B1549337
theorem B3490505 : Blo 1032607 3490505 := bstep (se 2 (by rfl) ⟨1308939, by rfl⟩ : syracuseStep 3490505 = 2617879) B2617879
theorem B3982061 : Blo 1032607 3982061 := bstep (se 3 (by rfl) ⟨746636, by rfl⟩ : syracuseStep 3982061 = 1493273) B1493273
theorem B1032967 : Blo 1032607 1032967 := bstep (se 1 (by rfl) ⟨774725, by rfl⟩ : syracuseStep 1032967 = 1549451) B1549451
theorem B1032975 : Blo 1032607 1032975 := bstep (se 1 (by rfl) ⟨774731, by rfl⟩ : syracuseStep 1032975 = 1549463) B1549463
theorem B1033019 : Blo 1032607 1033019 := bstep (se 1 (by rfl) ⟨774764, by rfl⟩ : syracuseStep 1033019 = 1549529) B1549529
theorem B1164091 : Blo 1032607 1164091 := bstep (se 1 (by rfl) ⟨873068, by rfl⟩ : syracuseStep 1164091 = 1746137) B1746137
theorem B1033095 : Blo 1032607 1033095 := bstep (se 1 (by rfl) ⟨774821, by rfl⟩ : syracuseStep 1033095 = 1549643) B1549643
theorem B1033103 : Blo 1032607 1033103 := bstep (se 1 (by rfl) ⟨774827, by rfl⟩ : syracuseStep 1033103 = 1549655) B1549655
theorem B1033147 : Blo 1032607 1033147 := bstep (se 1 (by rfl) ⟨774860, by rfl⟩ : syracuseStep 1033147 = 1549721) B1549721
theorem B1033223 : Blo 1032607 1033223 := bstep (se 1 (by rfl) ⟨774917, by rfl⟩ : syracuseStep 1033223 = 1549835) B1549835
theorem B1033231 : Blo 1032607 1033231 := bstep (se 1 (by rfl) ⟨774923, by rfl⟩ : syracuseStep 1033231 = 1549847) B1549847
theorem B1033275 : Blo 1032607 1033275 := bstep (se 1 (by rfl) ⟨774956, by rfl⟩ : syracuseStep 1033275 = 1549913) B1549913
theorem B1033351 : Blo 1032607 1033351 := bstep (se 1 (by rfl) ⟨775013, by rfl⟩ : syracuseStep 1033351 = 1550027) B1550027
theorem B1033359 : Blo 1032607 1033359 := bstep (se 1 (by rfl) ⟨775019, by rfl⟩ : syracuseStep 1033359 = 1550039) B1550039
theorem B1033403 : Blo 1032607 1033403 := bstep (se 1 (by rfl) ⟨775052, by rfl⟩ : syracuseStep 1033403 = 1550105) B1550105
theorem B1033479 : Blo 1032607 1033479 := bstep (se 1 (by rfl) ⟨775109, by rfl⟩ : syracuseStep 1033479 = 1550219) B1550219
theorem B1033487 : Blo 1032607 1033487 := bstep (se 1 (by rfl) ⟨775115, by rfl⟩ : syracuseStep 1033487 = 1550231) B1550231
theorem B1164559 : Blo 1032607 1164559 := bstep (se 1 (by rfl) ⟨873419, by rfl⟩ : syracuseStep 1164559 = 1746839) B1746839
theorem B1033531 : Blo 1032607 1033531 := bstep (se 1 (by rfl) ⟨775148, by rfl⟩ : syracuseStep 1033531 = 1550297) B1550297
theorem B13419911 : Blo 1032607 13419911 := bstep (se 1 (by rfl) ⟨10064933, by rfl⟩ : syracuseStep 13419911 = 20129867) B20129867
theorem B1033607 : Blo 1032607 1033607 := bstep (se 1 (by rfl) ⟨775205, by rfl⟩ : syracuseStep 1033607 = 1550411) B1550411
theorem B3491207 : Blo 1032607 3491207 := bstep (se 1 (by rfl) ⟨2618405, by rfl⟩ : syracuseStep 3491207 = 5236811) B5236811
theorem B1033615 : Blo 1032607 1033615 := bstep (se 1 (by rfl) ⟨775211, by rfl⟩ : syracuseStep 1033615 = 1550423) B1550423
theorem B1033659 : Blo 1032607 1033659 := bstep (se 1 (by rfl) ⟨775244, by rfl⟩ : syracuseStep 1033659 = 1550489) B1550489
theorem B1033735 : Blo 1032607 1033735 := bstep (se 1 (by rfl) ⟨775301, by rfl⟩ : syracuseStep 1033735 = 1550603) B1550603
theorem B1033743 : Blo 1032607 1033743 := bstep (se 1 (by rfl) ⟨775307, by rfl⟩ : syracuseStep 1033743 = 1550615) B1550615
theorem B19908125 : Blo 1032607 19908125 := bstep (se 3 (by rfl) ⟨3732773, by rfl⟩ : syracuseStep 19908125 = 7465547) B7465547
theorem B1033787 : Blo 1032607 1033787 := bstep (se 1 (by rfl) ⟨775340, by rfl⟩ : syracuseStep 1033787 = 1550681) B1550681
theorem B1033863 : Blo 1032607 1033863 := bstep (se 1 (by rfl) ⟨775397, by rfl⟩ : syracuseStep 1033863 = 1550795) B1550795
theorem B1033871 : Blo 1032607 1033871 := bstep (se 1 (by rfl) ⟨775403, by rfl⟩ : syracuseStep 1033871 = 1550807) B1550807
theorem B1033915 : Blo 1032607 1033915 := bstep (se 1 (by rfl) ⟨775436, by rfl⟩ : syracuseStep 1033915 = 1550873) B1550873
theorem B5228225 : Blo 1032607 5228225 := bstep (se 2 (by rfl) ⟨1960584, by rfl⟩ : syracuseStep 5228225 = 3921169) B3921169
theorem B3491585 : Blo 1032607 3491585 := bstep (se 2 (by rfl) ⟨1309344, by rfl⟩ : syracuseStep 3491585 = 2618689) B2618689
theorem B1033991 : Blo 1032607 1033991 := bstep (se 1 (by rfl) ⟨775493, by rfl⟩ : syracuseStep 1033991 = 1550987) B1550987
theorem B1165063 : Blo 1032607 1165063 := bstep (se 1 (by rfl) ⟨873797, by rfl⟩ : syracuseStep 1165063 = 1747595) B1747595
theorem B1033999 : Blo 1032607 1033999 := bstep (se 1 (by rfl) ⟨775499, by rfl⟩ : syracuseStep 1033999 = 1550999) B1550999
theorem B1034043 : Blo 1032607 1034043 := bstep (se 1 (by rfl) ⟨775532, by rfl⟩ : syracuseStep 1034043 = 1551065) B1551065
theorem B1034119 : Blo 1032607 1034119 := bstep (se 1 (by rfl) ⟨775589, by rfl⟩ : syracuseStep 1034119 = 1551179) B1551179
theorem B1034127 : Blo 1032607 1034127 := bstep (se 1 (by rfl) ⟨775595, by rfl⟩ : syracuseStep 1034127 = 1551191) B1551191
theorem B1034171 : Blo 1032607 1034171 := bstep (se 1 (by rfl) ⟨775628, by rfl⟩ : syracuseStep 1034171 = 1551257) B1551257
theorem B1165243 : Blo 1032607 1165243 := bstep (se 1 (by rfl) ⟨873932, by rfl⟩ : syracuseStep 1165243 = 1747865) B1747865
theorem B1034247 : Blo 1032607 1034247 := bstep (se 1 (by rfl) ⟨775685, by rfl⟩ : syracuseStep 1034247 = 1551371) B1551371
theorem B1034255 : Blo 1032607 1034255 := bstep (se 1 (by rfl) ⟨775691, by rfl⟩ : syracuseStep 1034255 = 1551383) B1551383
theorem B1034299 : Blo 1032607 1034299 := bstep (se 1 (by rfl) ⟨775724, by rfl⟩ : syracuseStep 1034299 = 1551449) B1551449
theorem B8833157 : Blo 1032607 8833157 := bstep (se 4 (by rfl) ⟨828108, by rfl⟩ : syracuseStep 8833157 = 1656217) B1656217
theorem B1034375 : Blo 1032607 1034375 := bstep (se 1 (by rfl) ⟨775781, by rfl⟩ : syracuseStep 1034375 = 1551563) B1551563
theorem B1034383 : Blo 1032607 1034383 := bstep (se 1 (by rfl) ⟨775787, by rfl⟩ : syracuseStep 1034383 = 1551575) B1551575
theorem B1034427 : Blo 1032607 1034427 := bstep (se 1 (by rfl) ⟨775820, by rfl⟩ : syracuseStep 1034427 = 1551641) B1551641
theorem B1034503 : Blo 1032607 1034503 := bstep (se 1 (by rfl) ⟨775877, by rfl⟩ : syracuseStep 1034503 = 1551755) B1551755
theorem B1034511 : Blo 1032607 1034511 := bstep (se 1 (by rfl) ⟨775883, by rfl⟩ : syracuseStep 1034511 = 1551767) B1551767
theorem B1034555 : Blo 1032607 1034555 := bstep (se 1 (by rfl) ⟨775916, by rfl⟩ : syracuseStep 1034555 = 1551833) B1551833
theorem B1034631 : Blo 1032607 1034631 := bstep (se 1 (by rfl) ⟨775973, by rfl⟩ : syracuseStep 1034631 = 1551947) B1551947
theorem B1034639 : Blo 1032607 1034639 := bstep (se 1 (by rfl) ⟨775979, by rfl⟩ : syracuseStep 1034639 = 1551959) B1551959
theorem B1165711 : Blo 1032607 1165711 := bstep (se 1 (by rfl) ⟨874283, by rfl⟩ : syracuseStep 1165711 = 1748567) B1748567
theorem B1034683 : Blo 1032607 1034683 := bstep (se 1 (by rfl) ⟨776012, by rfl⟩ : syracuseStep 1034683 = 1552025) B1552025
theorem B13453789 : Blo 1032607 13453789 := bstep (se 3 (by rfl) ⟨2522585, by rfl⟩ : syracuseStep 13453789 = 5045171) B5045171
theorem B1034759 : Blo 1032607 1034759 := bstep (se 1 (by rfl) ⟨776069, by rfl⟩ : syracuseStep 1034759 = 1552139) B1552139
theorem B1034767 : Blo 1032607 1034767 := bstep (se 1 (by rfl) ⟨776075, by rfl⟩ : syracuseStep 1034767 = 1552151) B1552151
theorem B3492395 : Blo 1032607 3492395 := bstep (se 1 (by rfl) ⟨2619296, by rfl⟩ : syracuseStep 3492395 = 5238593) B5238593
theorem B1034811 : Blo 1032607 1034811 := bstep (se 1 (by rfl) ⟨776108, by rfl⟩ : syracuseStep 1034811 = 1552217) B1552217
theorem B9423479 : Blo 1032607 9423479 := bstep (se 1 (by rfl) ⟨7067609, by rfl⟩ : syracuseStep 9423479 = 14135219) B14135219
theorem B1034887 : Blo 1032607 1034887 := bstep (se 1 (by rfl) ⟨776165, by rfl⟩ : syracuseStep 1034887 = 1552331) B1552331
theorem B1034895 : Blo 1032607 1034895 := bstep (se 1 (by rfl) ⟨776171, by rfl⟩ : syracuseStep 1034895 = 1552343) B1552343
theorem B1034939 : Blo 1032607 1034939 := bstep (se 1 (by rfl) ⟨776204, by rfl⟩ : syracuseStep 1034939 = 1552409) B1552409
theorem B1035015 : Blo 1032607 1035015 := bstep (se 1 (by rfl) ⟨776261, by rfl⟩ : syracuseStep 1035015 = 1552523) B1552523
theorem B1035023 : Blo 1032607 1035023 := bstep (se 1 (by rfl) ⟨776267, by rfl⟩ : syracuseStep 1035023 = 1552535) B1552535
theorem B1035067 : Blo 1032607 1035067 := bstep (se 1 (by rfl) ⟨776300, by rfl⟩ : syracuseStep 1035067 = 1552601) B1552601
theorem B1035143 : Blo 1032607 1035143 := bstep (se 1 (by rfl) ⟨776357, by rfl⟩ : syracuseStep 1035143 = 1552715) B1552715
theorem B1035151 : Blo 1032607 1035151 := bstep (se 1 (by rfl) ⟨776363, by rfl⟩ : syracuseStep 1035151 = 1552727) B1552727
theorem B1035195 : Blo 1032607 1035195 := bstep (se 1 (by rfl) ⟨776396, by rfl⟩ : syracuseStep 1035195 = 1552793) B1552793
theorem B5229521 : Blo 1032607 5229521 := bstep (se 2 (by rfl) ⟨1961070, by rfl⟩ : syracuseStep 5229521 = 3922141) B3922141
theorem B1035271 : Blo 1032607 1035271 := bstep (se 1 (by rfl) ⟨776453, by rfl⟩ : syracuseStep 1035271 = 1552907) B1552907
theorem B1035279 : Blo 1032607 1035279 := bstep (se 1 (by rfl) ⟨776459, by rfl⟩ : syracuseStep 1035279 = 1552919) B1552919
theorem B1035323 : Blo 1032607 1035323 := bstep (se 1 (by rfl) ⟨776492, by rfl⟩ : syracuseStep 1035323 = 1552985) B1552985
theorem B1035399 : Blo 1032607 1035399 := bstep (se 1 (by rfl) ⟨776549, by rfl⟩ : syracuseStep 1035399 = 1553099) B1553099
theorem B1035407 : Blo 1032607 1035407 := bstep (se 1 (by rfl) ⟨776555, by rfl⟩ : syracuseStep 1035407 = 1553111) B1553111
theorem B1035451 : Blo 1032607 1035451 := bstep (se 1 (by rfl) ⟨776588, by rfl⟩ : syracuseStep 1035451 = 1553177) B1553177
theorem B5983433 : Blo 1032607 5983433 := bstep (se 2 (by rfl) ⟨2243787, by rfl⟩ : syracuseStep 5983433 = 4487575) B4487575
theorem B1035527 : Blo 1032607 1035527 := bstep (se 1 (by rfl) ⟨776645, by rfl⟩ : syracuseStep 1035527 = 1553291) B1553291
theorem B1035535 : Blo 1032607 1035535 := bstep (se 1 (by rfl) ⟨776651, by rfl⟩ : syracuseStep 1035535 = 1553303) B1553303
theorem B1035579 : Blo 1032607 1035579 := bstep (se 1 (by rfl) ⟨776684, by rfl⟩ : syracuseStep 1035579 = 1553369) B1553369
theorem B11783555 : Blo 1032607 11783555 := bstep (se 1 (by rfl) ⟨8837666, by rfl⟩ : syracuseStep 11783555 = 17675333) B17675333
theorem B1035655 : Blo 1032607 1035655 := bstep (se 1 (by rfl) ⟨776741, by rfl⟩ : syracuseStep 1035655 = 1553483) B1553483
theorem B1035663 : Blo 1032607 1035663 := bstep (se 1 (by rfl) ⟨776747, by rfl⟩ : syracuseStep 1035663 = 1553495) B1553495
theorem B11193785 : Blo 1032607 11193785 := bstep (se 2 (by rfl) ⟨4197669, by rfl⟩ : syracuseStep 11193785 = 8395339) B8395339
theorem B1035707 : Blo 1032607 1035707 := bstep (se 1 (by rfl) ⟨776780, by rfl⟩ : syracuseStep 1035707 = 1553561) B1553561
theorem B1035783 : Blo 1032607 1035783 := bstep (se 1 (by rfl) ⟨776837, by rfl⟩ : syracuseStep 1035783 = 1553675) B1553675
theorem B1035791 : Blo 1032607 1035791 := bstep (se 1 (by rfl) ⟨776843, by rfl⟩ : syracuseStep 1035791 = 1553687) B1553687
theorem B7556651 : Blo 1032607 7556651 := bstep (se 1 (by rfl) ⟨5667488, by rfl⟩ : syracuseStep 7556651 = 11334977) B11334977
theorem B1035835 : Blo 1032607 1035835 := bstep (se 1 (by rfl) ⟨776876, by rfl⟩ : syracuseStep 1035835 = 1553753) B1553753
theorem B1035911 : Blo 1032607 1035911 := bstep (se 1 (by rfl) ⟨776933, by rfl⟩ : syracuseStep 1035911 = 1553867) B1553867
theorem B1035919 : Blo 1032607 1035919 := bstep (se 1 (by rfl) ⟨776939, by rfl⟩ : syracuseStep 1035919 = 1553879) B1553879
theorem B1035963 : Blo 1032607 1035963 := bstep (se 1 (by rfl) ⟨776972, by rfl⟩ : syracuseStep 1035963 = 1553945) B1553945
theorem B1036039 : Blo 1032607 1036039 := bstep (se 1 (by rfl) ⟨777029, by rfl⟩ : syracuseStep 1036039 = 1554059) B1554059
theorem B1036047 : Blo 1032607 1036047 := bstep (se 1 (by rfl) ⟨777035, by rfl⟩ : syracuseStep 1036047 = 1554071) B1554071
theorem B3493691 : Blo 1032607 3493691 := bstep (se 1 (by rfl) ⟨2620268, by rfl⟩ : syracuseStep 3493691 = 5240537) B5240537
theorem B1036091 : Blo 1032607 1036091 := bstep (se 1 (by rfl) ⟨777068, by rfl⟩ : syracuseStep 1036091 = 1554137) B1554137
theorem B1036167 : Blo 1032607 1036167 := bstep (se 1 (by rfl) ⟨777125, by rfl⟩ : syracuseStep 1036167 = 1554251) B1554251
theorem B1036175 : Blo 1032607 1036175 := bstep (se 1 (by rfl) ⟨777131, by rfl⟩ : syracuseStep 1036175 = 1554263) B1554263
theorem B2838419 : Blo 1032607 2838419 := bstep (se 1 (by rfl) ⟨2128814, by rfl⟩ : syracuseStep 2838419 = 4257629) B4257629
theorem B1036219 : Blo 1032607 1036219 := bstep (se 1 (by rfl) ⟨777164, by rfl⟩ : syracuseStep 1036219 = 1554329) B1554329
theorem B1036295 : Blo 1032607 1036295 := bstep (se 1 (by rfl) ⟨777221, by rfl⟩ : syracuseStep 1036295 = 1554443) B1554443
theorem B1036303 : Blo 1032607 1036303 := bstep (se 1 (by rfl) ⟨777227, by rfl⟩ : syracuseStep 1036303 = 1554455) B1554455
theorem B1036347 : Blo 1032607 1036347 := bstep (se 1 (by rfl) ⟨777260, by rfl⟩ : syracuseStep 1036347 = 1554521) B1554521
theorem B1036423 : Blo 1032607 1036423 := bstep (se 1 (by rfl) ⟨777317, by rfl⟩ : syracuseStep 1036423 = 1554635) B1554635
theorem B1036431 : Blo 1032607 1036431 := bstep (se 1 (by rfl) ⟨777323, by rfl⟩ : syracuseStep 1036431 = 1554647) B1554647
theorem B1036475 : Blo 1032607 1036475 := bstep (se 1 (by rfl) ⟨777356, by rfl⟩ : syracuseStep 1036475 = 1554713) B1554713
theorem B1036551 : Blo 1032607 1036551 := bstep (se 1 (by rfl) ⟨777413, by rfl⟩ : syracuseStep 1036551 = 1554827) B1554827
theorem B1036559 : Blo 1032607 1036559 := bstep (se 1 (by rfl) ⟨777419, by rfl⟩ : syracuseStep 1036559 = 1554839) B1554839
theorem B3494177 : Blo 1032607 3494177 := bstep (se 2 (by rfl) ⟨1310316, by rfl⟩ : syracuseStep 3494177 = 2620633) B2620633
theorem B1036603 : Blo 1032607 1036603 := bstep (se 1 (by rfl) ⟨777452, by rfl⟩ : syracuseStep 1036603 = 1554905) B1554905
theorem B1888697 : Blo 1032607 1888697 := bstep (se 2 (by rfl) ⟨708261, by rfl⟩ : syracuseStep 1888697 = 1416523) B1416523
theorem B3592993 : Blo 1032607 3592993 := bstep (se 2 (by rfl) ⟨1347372, by rfl⟩ : syracuseStep 3592993 = 2694745) B2694745
theorem B11195171 : Blo 1032607 11195171 := bstep (se 1 (by rfl) ⟨8396378, by rfl⟩ : syracuseStep 11195171 = 16792757) B16792757
theorem B3494771 : Blo 1032607 3494771 := bstep (se 1 (by rfl) ⟨2621078, by rfl⟩ : syracuseStep 3494771 = 5242157) B5242157
theorem B5231627 : Blo 1032607 5231627 := bstep (se 1 (by rfl) ⟨3923720, by rfl⟩ : syracuseStep 5231627 = 7847441) B7847441
theorem B3920957 : Blo 1032607 3920957 := bstep (se 3 (by rfl) ⟨735179, by rfl⟩ : syracuseStep 3920957 = 1470359) B1470359
theorem B3724355 : Blo 1032607 3724355 := bstep (se 1 (by rfl) ⟨2793266, by rfl⟩ : syracuseStep 3724355 = 5586533) B5586533
theorem B5231789 : Blo 1032607 5231789 := bstep (se 3 (by rfl) ⟨980960, by rfl⟩ : syracuseStep 5231789 = 1961921) B1961921
theorem B1103239 : Blo 1032607 1103239 := bstep (se 1 (by rfl) ⟨827429, by rfl⟩ : syracuseStep 1103239 = 1654859) B1654859
theorem B4412819 : Blo 1032607 4412819 := bstep (se 1 (by rfl) ⟨3309614, by rfl⟩ : syracuseStep 4412819 = 6619229) B6619229
theorem B8836573 : Blo 1032607 8836573 := bstep (se 3 (by rfl) ⟨1656857, by rfl⟩ : syracuseStep 8836573 = 3313715) B3313715
theorem B1103419 : Blo 1032607 1103419 := bstep (se 1 (by rfl) ⟨827564, by rfl⟩ : syracuseStep 1103419 = 1655129) B1655129
theorem B5592979 : Blo 1032607 5592979 := bstep (se 1 (by rfl) ⟨4194734, by rfl⟩ : syracuseStep 5592979 = 8389469) B8389469
theorem B1398775 : Blo 1032607 1398775 := bstep (se 1 (by rfl) ⟨1049081, by rfl⟩ : syracuseStep 1398775 = 2098163) B2098163
theorem B16766999 : Blo 1032607 16766999 := bstep (se 1 (by rfl) ⟨12575249, by rfl⟩ : syracuseStep 16766999 = 25150499) B25150499
theorem B4970767 : Blo 1032607 4970767 := bstep (se 1 (by rfl) ⟨3728075, by rfl⟩ : syracuseStep 4970767 = 7456151) B7456151
theorem B5888315 : Blo 1032607 5888315 := bstep (se 1 (by rfl) ⟨4416236, by rfl⟩ : syracuseStep 5888315 = 8832473) B8832473
theorem B4413811 : Blo 1032607 4413811 := bstep (se 1 (by rfl) ⟨3310358, by rfl⟩ : syracuseStep 4413811 = 6620717) B6620717
theorem B5233409 : Blo 1032607 5233409 := bstep (se 2 (by rfl) ⟨1962528, by rfl⟩ : syracuseStep 5233409 = 3925057) B3925057
theorem B3366203 : Blo 1032607 3366203 := bstep (se 1 (by rfl) ⟨2524652, by rfl⟩ : syracuseStep 3366203 = 5049305) B5049305
theorem B3497363 : Blo 1032607 3497363 := bstep (se 1 (by rfl) ⟨2623022, by rfl⟩ : syracuseStep 3497363 = 5246045) B5246045
theorem B5234219 : Blo 1032607 5234219 := bstep (se 1 (by rfl) ⟨3925664, by rfl⟩ : syracuseStep 5234219 = 7851329) B7851329
theorem B5889773 : Blo 1032607 5889773 := bstep (se 3 (by rfl) ⟨1104332, by rfl⟩ : syracuseStep 5889773 = 2208665) B2208665
theorem B7069555 : Blo 1032607 7069555 := bstep (se 1 (by rfl) ⟨5302166, by rfl⟩ : syracuseStep 7069555 = 10604333) B10604333
theorem B4415417 : Blo 1032607 4415417 := bstep (se 2 (by rfl) ⟨1655781, by rfl⟩ : syracuseStep 4415417 = 3311563) B3311563
theorem B7856189 : Blo 1032607 7856189 := bstep (se 3 (by rfl) ⟨1473035, by rfl⟩ : syracuseStep 7856189 = 2946071) B2946071
theorem B4415759 : Blo 1032607 4415759 := bstep (se 1 (by rfl) ⟨3311819, by rfl⟩ : syracuseStep 4415759 = 6623639) B6623639
theorem B3924359 : Blo 1032607 3924359 := bstep (se 1 (by rfl) ⟨2943269, by rfl⟩ : syracuseStep 3924359 = 5886539) B5886539
theorem B13263425 : Blo 1032607 13263425 := bstep (se 2 (by rfl) ⟨4973784, by rfl⟩ : syracuseStep 13263425 = 9947569) B9947569
theorem B2941697 : Blo 1032607 2941697 := bstep (se 2 (by rfl) ⟨1103136, by rfl⟩ : syracuseStep 2941697 = 2206273) B2206273
theorem B5235515 : Blo 1032607 5235515 := bstep (se 1 (by rfl) ⟨3926636, by rfl⟩ : syracuseStep 5235515 = 7853273) B7853273
theorem B2614103 : Blo 1032607 2614103 := bstep (se 1 (by rfl) ⟨1960577, by rfl⟩ : syracuseStep 2614103 = 3921155) B3921155
theorem B9069515 : Blo 1032607 9069515 := bstep (se 1 (by rfl) ⟨6802136, by rfl⟩ : syracuseStep 9069515 = 13604273) B13604273
theorem B5235677 : Blo 1032607 5235677 := bstep (se 3 (by rfl) ⟨981689, by rfl⟩ : syracuseStep 5235677 = 1963379) B1963379
theorem B2614315 : Blo 1032607 2614315 := bstep (se 1 (by rfl) ⟨1960736, by rfl⟩ : syracuseStep 2614315 = 3921473) B3921473
theorem B2614457 : Blo 1032607 2614457 := bstep (se 2 (by rfl) ⟨980421, by rfl⟩ : syracuseStep 2614457 = 1960843) B1960843
theorem B2942153 : Blo 1032607 2942153 := bstep (se 2 (by rfl) ⟨1103307, by rfl⟩ : syracuseStep 2942153 = 2206615) B2206615
theorem B5236001 : Blo 1032607 5236001 := bstep (se 2 (by rfl) ⟨1963500, by rfl⟩ : syracuseStep 5236001 = 3927001) B3927001
theorem B2942507 : Blo 1032607 2942507 := bstep (se 1 (by rfl) ⟨2206880, by rfl⟩ : syracuseStep 2942507 = 4413761) B4413761
theorem B1861255 : Blo 1032607 1861255 := bstep (se 1 (by rfl) ⟨1395941, by rfl⟩ : syracuseStep 1861255 = 2791883) B2791883
theorem B33613643 : Blo 1032607 33613643 := bstep (se 1 (by rfl) ⟨25210232, by rfl⟩ : syracuseStep 33613643 = 50420465) B50420465
theorem B2942905 : Blo 1032607 2942905 := bstep (se 2 (by rfl) ⟨1103589, by rfl⟩ : syracuseStep 2942905 = 2207179) B2207179
theorem B2615449 : Blo 1032607 2615449 := bstep (se 2 (by rfl) ⟨980793, by rfl⟩ : syracuseStep 2615449 = 1961587) B1961587
theorem B5236973 : Blo 1032607 5236973 := bstep (se 3 (by rfl) ⟨981932, by rfl⟩ : syracuseStep 5236973 = 1963865) B1963865
theorem B6285605 : Blo 1032607 6285605 := bstep (se 4 (by rfl) ⟨589275, by rfl⟩ : syracuseStep 6285605 = 1178551) B1178551
theorem B2615611 : Blo 1032607 2615611 := bstep (se 1 (by rfl) ⟨1961708, by rfl⟩ : syracuseStep 2615611 = 3923417) B3923417
theorem B2484539 : Blo 1032607 2484539 := bstep (se 1 (by rfl) ⟨1863404, by rfl⟩ : syracuseStep 2484539 = 3726809) B3726809
theorem B4975033 : Blo 1032607 4975033 := bstep (se 2 (by rfl) ⟨1865637, by rfl⟩ : syracuseStep 4975033 = 3731275) B3731275
theorem B2615753 : Blo 1032607 2615753 := bstep (se 2 (by rfl) ⟨980907, by rfl⟩ : syracuseStep 2615753 = 1961815) B1961815
theorem B1960463 : Blo 1032607 1960463 := bstep (se 1 (by rfl) ⟨1470347, by rfl⟩ : syracuseStep 1960463 = 2940695) B2940695
theorem B2484769 : Blo 1032607 2484769 := bstep (se 2 (by rfl) ⟨931788, by rfl⟩ : syracuseStep 2484769 = 1863577) B1863577
theorem B4418135 : Blo 1032607 4418135 := bstep (se 1 (by rfl) ⟨3313601, by rfl⟩ : syracuseStep 4418135 = 6627203) B6627203
theorem B1862345 : Blo 1032607 1862345 := bstep (se 2 (by rfl) ⟨698379, by rfl⟩ : syracuseStep 1862345 = 1396759) B1396759
theorem B3140381 : Blo 1032607 3140381 := bstep (se 3 (by rfl) ⟨588821, by rfl⟩ : syracuseStep 3140381 = 1177643) B1177643
theorem B2616097 : Blo 1032607 2616097 := bstep (se 2 (by rfl) ⟨981036, by rfl⟩ : syracuseStep 2616097 = 1962073) B1962073
theorem B5237783 : Blo 1032607 5237783 := bstep (se 1 (by rfl) ⟨3928337, by rfl⟩ : syracuseStep 5237783 = 7856675) B7856675
theorem B1961003 : Blo 1032607 1961003 := bstep (se 1 (by rfl) ⟨1470752, by rfl⟩ : syracuseStep 1961003 = 2941505) B2941505
theorem B3730499 : Blo 1032607 3730499 := bstep (se 1 (by rfl) ⟨2797874, by rfl⟩ : syracuseStep 3730499 = 5595749) B5595749
theorem B2944147 : Blo 1032607 2944147 := bstep (se 1 (by rfl) ⟨2208110, by rfl⟩ : syracuseStep 2944147 = 4416221) B4416221
theorem B2616695 : Blo 1032607 2616695 := bstep (se 1 (by rfl) ⟨1962521, by rfl⟩ : syracuseStep 2616695 = 3925043) B3925043
theorem B7859591 : Blo 1032607 7859591 := bstep (se 1 (by rfl) ⟨5894693, by rfl⟩ : syracuseStep 7859591 = 11789387) B11789387
theorem B24178105 : Blo 1032607 24178105 := bstep (se 2 (by rfl) ⟨9066789, by rfl⟩ : syracuseStep 24178105 = 18133579) B18133579
theorem B4976093 : Blo 1032607 4976093 := bstep (se 3 (by rfl) ⟨933017, by rfl⟩ : syracuseStep 4976093 = 1866035) B1866035
theorem B4976417 : Blo 1032607 4976417 := bstep (se 2 (by rfl) ⟨1866156, by rfl⟩ : syracuseStep 4976417 = 3732313) B3732313
theorem B5894147 : Blo 1032607 5894147 := bstep (se 1 (by rfl) ⟨4420610, by rfl⟩ : syracuseStep 5894147 = 8841221) B8841221
theorem B4255811 : Blo 1032607 4255811 := bstep (se 1 (by rfl) ⟨3191858, by rfl⟩ : syracuseStep 4255811 = 6383717) B6383717
theorem B1962119 : Blo 1032607 1962119 := bstep (se 1 (by rfl) ⟨1471589, by rfl⟩ : syracuseStep 1962119 = 2943179) B2943179
theorem B6812039 : Blo 1032607 6812039 := bstep (se 1 (by rfl) ⟨5109029, by rfl⟩ : syracuseStep 6812039 = 10218059) B10218059
theorem B5894603 : Blo 1032607 5894603 := bstep (se 1 (by rfl) ⟨4420952, by rfl⟩ : syracuseStep 5894603 = 8841905) B8841905
theorem B2617991 : Blo 1032607 2617991 := bstep (se 1 (by rfl) ⟨1963493, by rfl⟩ : syracuseStep 2617991 = 3926987) B3926987
theorem B1307279 : Blo 1032607 1307279 := bstep (se 1 (by rfl) ⟨980459, by rfl⟩ : syracuseStep 1307279 = 1960919) B1960919
theorem B1962643 : Blo 1032607 1962643 := bstep (se 1 (by rfl) ⟨1471982, by rfl⟩ : syracuseStep 1962643 = 2943965) B2943965
theorem B2618041 : Blo 1032607 2618041 := bstep (se 2 (by rfl) ⟨981765, by rfl⟩ : syracuseStep 2618041 = 1963531) B1963531
theorem B3142415 : Blo 1032607 3142415 := bstep (se 1 (by rfl) ⟨2356811, by rfl⟩ : syracuseStep 3142415 = 4713623) B4713623
theorem B2945821 : Blo 1032607 2945821 := bstep (se 3 (by rfl) ⟨552341, by rfl⟩ : syracuseStep 2945821 = 1104683) B1104683
theorem B3732257 : Blo 1032607 3732257 := bstep (se 2 (by rfl) ⟨1399596, by rfl⟩ : syracuseStep 3732257 = 2799193) B2799193
theorem B2945879 : Blo 1032607 2945879 := bstep (se 1 (by rfl) ⟨2209409, by rfl⟩ : syracuseStep 2945879 = 4418819) B4418819
theorem B2323385 : Blo 1032607 2323385 := bstep (se 2 (by rfl) ⟨871269, by rfl⟩ : syracuseStep 2323385 = 1742539) B1742539
theorem B5895287 : Blo 1032607 5895287 := bstep (se 1 (by rfl) ⟨4421465, by rfl⟩ : syracuseStep 5895287 = 8842931) B8842931
theorem B2323727 : Blo 1032607 2323727 := bstep (se 1 (by rfl) ⟨1742795, by rfl⟩ : syracuseStep 2323727 = 3485591) B3485591
theorem B2618639 : Blo 1032607 2618639 := bstep (se 1 (by rfl) ⟨1963979, by rfl⟩ : syracuseStep 2618639 = 3927959) B3927959
theorem B2323745 : Blo 1032607 2323745 := bstep (se 2 (by rfl) ⟨871404, by rfl⟩ : syracuseStep 2323745 = 1742809) B1742809
theorem B8516897 : Blo 1032607 8516897 := bstep (se 2 (by rfl) ⟨3193836, by rfl⟩ : syracuseStep 8516897 = 6387673) B6387673
theorem B1865003 : Blo 1032607 1865003 := bstep (se 1 (by rfl) ⟨1398752, by rfl⟩ : syracuseStep 1865003 = 2797505) B2797505
theorem B1471817 : Blo 1032607 1471817 := bstep (se 2 (by rfl) ⟨551931, by rfl⟩ : syracuseStep 1471817 = 1103863) B1103863
theorem B2094625 : Blo 1032607 2094625 := bstep (se 2 (by rfl) ⟨785484, by rfl⟩ : syracuseStep 2094625 = 1570969) B1570969
theorem B2324087 : Blo 1032607 2324087 := bstep (se 1 (by rfl) ⟨1743065, by rfl⟩ : syracuseStep 2324087 = 3486131) B3486131
theorem B2324267 : Blo 1032607 2324267 := bstep (se 1 (by rfl) ⟨1743200, by rfl⟩ : syracuseStep 2324267 = 3486401) B3486401
theorem B1963835 : Blo 1032607 1963835 := bstep (se 1 (by rfl) ⟨1472876, by rfl⟩ : syracuseStep 1963835 = 2945753) B2945753
theorem B18904907 : Blo 1032607 18904907 := bstep (se 1 (by rfl) ⟨14178680, by rfl⟩ : syracuseStep 18904907 = 28357361) B28357361
theorem B1472375 : Blo 1032607 1472375 := bstep (se 1 (by rfl) ⟨1104281, by rfl⟩ : syracuseStep 1472375 = 2208563) B2208563
theorem B9566105 : Blo 1032607 9566105 := bstep (se 2 (by rfl) ⟨3587289, by rfl⟩ : syracuseStep 9566105 = 7174579) B7174579
theorem B2619337 : Blo 1032607 2619337 := bstep (se 2 (by rfl) ⟨982251, by rfl⟩ : syracuseStep 2619337 = 1964503) B1964503
theorem B33552407 : Blo 1032607 33552407 := bstep (se 1 (by rfl) ⟨25164305, by rfl⟩ : syracuseStep 33552407 = 50328611) B50328611
theorem B5240861 : Blo 1032607 5240861 := bstep (se 3 (by rfl) ⟨982661, by rfl⟩ : syracuseStep 5240861 = 1965323) B1965323
theorem B2619479 : Blo 1032607 2619479 := bstep (se 1 (by rfl) ⟨1964609, by rfl⟩ : syracuseStep 2619479 = 3929219) B3929219
theorem B2488439 : Blo 1032607 2488439 := bstep (se 1 (by rfl) ⟨1866329, by rfl⟩ : syracuseStep 2488439 = 3732659) B3732659
theorem B2324627 : Blo 1032607 2324627 := bstep (se 1 (by rfl) ⟨1743470, by rfl⟩ : syracuseStep 2324627 = 3486941) B3486941
theorem B1472683 : Blo 1032607 1472683 := bstep (se 1 (by rfl) ⟨1104512, by rfl⟩ : syracuseStep 1472683 = 2209025) B2209025
theorem B1243307 : Blo 1032607 1243307 := bstep (se 1 (by rfl) ⟨932480, by rfl⟩ : syracuseStep 1243307 = 1864961) B1864961
theorem B2324681 : Blo 1032607 2324681 := bstep (se 2 (by rfl) ⟨871755, by rfl⟩ : syracuseStep 2324681 = 1743511) B1743511
theorem B1865999 : Blo 1032607 1865999 := bstep (se 1 (by rfl) ⟨1399499, by rfl⟩ : syracuseStep 1865999 = 2798999) B2798999
theorem B1964321 : Blo 1032607 1964321 := bstep (se 2 (by rfl) ⟨736620, by rfl⟩ : syracuseStep 1964321 = 1473241) B1473241
theorem B1243451 : Blo 1032607 1243451 := bstep (se 1 (by rfl) ⟨932588, by rfl⟩ : syracuseStep 1243451 = 1865177) B1865177
theorem B5962099 : Blo 1032607 5962099 := bstep (se 1 (by rfl) ⟨4471574, by rfl⟩ : syracuseStep 5962099 = 8943149) B8943149
theorem B2947529 : Blo 1032607 2947529 := bstep (se 2 (by rfl) ⟨1105323, by rfl⟩ : syracuseStep 2947529 = 2210647) B2210647
theorem B5601757 : Blo 1032607 5601757 := bstep (se 3 (by rfl) ⟨1050329, by rfl⟩ : syracuseStep 5601757 = 2100659) B2100659
theorem B5241347 : Blo 1032607 5241347 := bstep (se 1 (by rfl) ⟨3931010, by rfl⟩ : syracuseStep 5241347 = 7862021) B7862021
theorem B3144203 : Blo 1032607 3144203 := bstep (se 1 (by rfl) ⟨2358152, by rfl⟩ : syracuseStep 3144203 = 4716305) B4716305
theorem B3734045 : Blo 1032607 3734045 := bstep (se 3 (by rfl) ⟨700133, by rfl⟩ : syracuseStep 3734045 = 1400267) B1400267
theorem B1964587 : Blo 1032607 1964587 := bstep (se 1 (by rfl) ⟨1473440, by rfl⟩ : syracuseStep 1964587 = 2946881) B2946881
theorem B12581477 : Blo 1032607 12581477 := bstep (se 4 (by rfl) ⟨1179513, by rfl⟩ : syracuseStep 12581477 = 2359027) B2359027
theorem B1473167 : Blo 1032607 1473167 := bstep (se 1 (by rfl) ⟨1104875, by rfl⟩ : syracuseStep 1473167 = 2209751) B2209751
theorem B3537665 : Blo 1032607 3537665 := bstep (se 2 (by rfl) ⟨1326624, by rfl⟩ : syracuseStep 3537665 = 2653249) B2653249
theorem B9927461 : Blo 1032607 9927461 := bstep (se 4 (by rfl) ⟨930699, by rfl⟩ : syracuseStep 9927461 = 1861399) B1861399
theorem B2489131 : Blo 1032607 2489131 := bstep (se 1 (by rfl) ⟨1866848, by rfl⟩ : syracuseStep 2489131 = 3733697) B3733697
theorem B2325383 : Blo 1032607 2325383 := bstep (se 1 (by rfl) ⟨1744037, by rfl⟩ : syracuseStep 2325383 = 3488075) B3488075
theorem B5897245 : Blo 1032607 5897245 := bstep (se 3 (by rfl) ⟨1105733, by rfl⟩ : syracuseStep 5897245 = 2211467) B2211467
theorem B2325563 : Blo 1032607 2325563 := bstep (se 1 (by rfl) ⟨1744172, by rfl⟩ : syracuseStep 2325563 = 3488345) B3488345
theorem B2325689 : Blo 1032607 2325689 := bstep (se 2 (by rfl) ⟨872133, by rfl⟩ : syracuseStep 2325689 = 1744267) B1744267
theorem B2948395 : Blo 1032607 2948395 := bstep (se 1 (by rfl) ⟨2211296, by rfl⟩ : syracuseStep 2948395 = 4422593) B4422593
theorem B11926919 : Blo 1032607 11926919 := bstep (se 1 (by rfl) ⟨8945189, by rfl⟩ : syracuseStep 11926919 = 17890379) B17890379
theorem B2326031 : Blo 1032607 2326031 := bstep (se 1 (by rfl) ⟨1744523, by rfl⟩ : syracuseStep 2326031 = 3489047) B3489047
theorem B2326049 : Blo 1032607 2326049 := bstep (se 2 (by rfl) ⟨872268, by rfl⟩ : syracuseStep 2326049 = 1744537) B1744537
theorem B1310251 : Blo 1032607 1310251 := bstep (se 1 (by rfl) ⟨982688, by rfl⟩ : syracuseStep 1310251 = 1965377) B1965377
theorem B5897771 : Blo 1032607 5897771 := bstep (se 1 (by rfl) ⟨4423328, by rfl⟩ : syracuseStep 5897771 = 8846657) B8846657
theorem B2948669 : Blo 1032607 2948669 := bstep (se 3 (by rfl) ⟨552875, by rfl⟩ : syracuseStep 2948669 = 1105751) B1105751
theorem B1965703 : Blo 1032607 1965703 := bstep (se 1 (by rfl) ⟨1474277, by rfl⟩ : syracuseStep 1965703 = 2948555) B2948555
theorem B9961217 : Blo 1032607 9961217 := bstep (se 2 (by rfl) ⟨3735456, by rfl⟩ : syracuseStep 9961217 = 7470913) B7470913
theorem B2096929 : Blo 1032607 2096929 := bstep (se 2 (by rfl) ⟨786348, by rfl⟩ : syracuseStep 2096929 = 1572697) B1572697
theorem B2326391 : Blo 1032607 2326391 := bstep (se 1 (by rfl) ⟨1744793, by rfl⟩ : syracuseStep 2326391 = 3489587) B3489587
theorem B2949011 : Blo 1032607 2949011 := bstep (se 1 (by rfl) ⟨2211758, by rfl⟩ : syracuseStep 2949011 = 4423517) B4423517
theorem B2326535 : Blo 1032607 2326535 := bstep (se 1 (by rfl) ⟨1744901, by rfl⟩ : syracuseStep 2326535 = 3489803) B3489803
theorem B2326607 : Blo 1032607 2326607 := bstep (se 1 (by rfl) ⟨1744955, by rfl⟩ : syracuseStep 2326607 = 3489911) B3489911
theorem B1310843 : Blo 1032607 1310843 := bstep (se 1 (by rfl) ⟨983132, by rfl⟩ : syracuseStep 1310843 = 1966265) B1966265
theorem B2327003 : Blo 1032607 2327003 := bstep (se 1 (by rfl) ⟨1745252, by rfl⟩ : syracuseStep 2327003 = 3490505) B3490505
theorem B2654707 : Blo 1032607 2654707 := bstep (se 1 (by rfl) ⟨1991030, by rfl⟩ : syracuseStep 2654707 = 3982061) B3982061
theorem B2949671 : Blo 1032607 2949671 := bstep (se 1 (by rfl) ⟨2212253, by rfl⟩ : syracuseStep 2949671 = 4424507) B4424507
theorem B2622091 : Blo 1032607 2622091 := bstep (se 1 (by rfl) ⟨1966568, by rfl⟩ : syracuseStep 2622091 = 3933137) B3933137
theorem B3932819 : Blo 1032607 3932819 := bstep (se 1 (by rfl) ⟨2949614, by rfl⟩ : syracuseStep 3932819 = 5899229) B5899229
theorem B8946607 : Blo 1032607 8946607 := bstep (se 1 (by rfl) ⟨6709955, by rfl⟩ : syracuseStep 8946607 = 13419911) B13419911
theorem B2327471 : Blo 1032607 2327471 := bstep (se 1 (by rfl) ⟨1745603, by rfl⟩ : syracuseStep 2327471 = 3491207) B3491207
theorem B2622395 : Blo 1032607 2622395 := bstep (se 1 (by rfl) ⟨1966796, by rfl⟩ : syracuseStep 2622395 = 3933593) B3933593
theorem B13272083 : Blo 1032607 13272083 := bstep (se 1 (by rfl) ⟨9954062, by rfl⟩ : syracuseStep 13272083 = 19908125) B19908125
theorem B4195385 : Blo 1032607 4195385 := bstep (se 2 (by rfl) ⟨1573269, by rfl⟩ : syracuseStep 4195385 = 3146539) B3146539
theorem B1967161 : Blo 1032607 1967161 := bstep (se 2 (by rfl) ⟨737685, by rfl⟩ : syracuseStep 1967161 = 1475371) B1475371
theorem B3277903 : Blo 1032607 3277903 := bstep (se 1 (by rfl) ⟨2458427, by rfl⟩ : syracuseStep 3277903 = 4916855) B4916855
theorem B7865423 : Blo 1032607 7865423 := bstep (se 1 (by rfl) ⟨5899067, by rfl⟩ : syracuseStep 7865423 = 11798135) B11798135
theorem B2327723 : Blo 1032607 2327723 := bstep (se 1 (by rfl) ⟨1745792, by rfl⟩ : syracuseStep 2327723 = 3491585) B3491585
theorem B1967465 : Blo 1032607 1967465 := bstep (se 2 (by rfl) ⟨737799, by rfl⟩ : syracuseStep 1967465 = 1475599) B1475599
theorem B1967503 : Blo 1032607 1967503 := bstep (se 1 (by rfl) ⟨1475627, by rfl⟩ : syracuseStep 1967503 = 2951255) B2951255
theorem B2328263 : Blo 1032607 2328263 := bstep (se 1 (by rfl) ⟨1746197, by rfl⟩ : syracuseStep 2328263 = 3492395) B3492395
theorem B2623175 : Blo 1032607 2623175 := bstep (se 1 (by rfl) ⟨1967381, by rfl⟩ : syracuseStep 2623175 = 3934763) B3934763
theorem B31819513 : Blo 1032607 31819513 := bstep (se 2 (by rfl) ⟨11932317, by rfl⟩ : syracuseStep 31819513 = 23864635) B23864635
theorem B2623225 : Blo 1032607 2623225 := bstep (se 2 (by rfl) ⟨983709, by rfl⟩ : syracuseStep 2623225 = 1967419) B1967419
theorem B4720427 : Blo 1032607 4720427 := bstep (se 1 (by rfl) ⟨3540320, by rfl⟩ : syracuseStep 4720427 = 7080641) B7080641
theorem B9439537 : Blo 1032607 9439537 := bstep (se 2 (by rfl) ⟨3539826, by rfl⟩ : syracuseStep 9439537 = 7079653) B7079653
theorem B2623873 : Blo 1032607 2623873 := bstep (se 2 (by rfl) ⟨983952, by rfl⟩ : syracuseStep 2623873 = 1967905) B1967905
theorem B3541391 : Blo 1032607 3541391 := bstep (se 1 (by rfl) ⟨2656043, by rfl⟩ : syracuseStep 3541391 = 5312087) B5312087
theorem B8489369 : Blo 1032607 8489369 := bstep (se 2 (by rfl) ⟨3183513, by rfl⟩ : syracuseStep 8489369 = 6367027) B6367027
theorem B2329127 : Blo 1032607 2329127 := bstep (se 1 (by rfl) ⟨1746845, by rfl⟩ : syracuseStep 2329127 = 3493691) B3493691
theorem B2329451 : Blo 1032607 2329451 := bstep (se 1 (by rfl) ⟨1747088, by rfl⟩ : syracuseStep 2329451 = 3494177) B3494177
theorem B2329505 : Blo 1032607 2329505 := bstep (se 2 (by rfl) ⟨873564, by rfl⟩ : syracuseStep 2329505 = 1747129) B1747129
theorem B4197295 : Blo 1032607 4197295 := bstep (se 1 (by rfl) ⟨3147971, by rfl⟩ : syracuseStep 4197295 = 6295943) B6295943
theorem B4197491 : Blo 1032607 4197491 := bstep (se 1 (by rfl) ⟨3148118, by rfl⟩ : syracuseStep 4197491 = 6296237) B6296237
theorem B2329847 : Blo 1032607 2329847 := bstep (se 1 (by rfl) ⟨1747385, by rfl⟩ : syracuseStep 2329847 = 3494771) B3494771
theorem B3313025 : Blo 1032607 3313025 := bstep (se 2 (by rfl) ⟨1242384, by rfl⟩ : syracuseStep 3313025 = 2484769) B2484769
theorem B8851031 : Blo 1032607 8851031 := bstep (se 1 (by rfl) ⟨6638273, by rfl⟩ : syracuseStep 8851031 = 13276547) B13276547
theorem B4198073 : Blo 1032607 4198073 := bstep (se 2 (by rfl) ⟨1574277, by rfl⟩ : syracuseStep 4198073 = 3148555) B3148555
theorem B11767517 : Blo 1032607 11767517 := bstep (se 3 (by rfl) ⟨2206409, by rfl⟩ : syracuseStep 11767517 = 4412819) B4412819
theorem B2330441 : Blo 1032607 2330441 := bstep (se 2 (by rfl) ⟨873915, by rfl⟩ : syracuseStep 2330441 = 1747831) B1747831
theorem B11177999 : Blo 1032607 11177999 := bstep (se 1 (by rfl) ⟨8383499, by rfl⟩ : syracuseStep 11177999 = 16766999) B16766999
theorem B7868825 : Blo 1032607 7868825 := bstep (se 2 (by rfl) ⟨2950809, by rfl⟩ : syracuseStep 7868825 = 5901619) B5901619
theorem B2331233 : Blo 1032607 2331233 := bstep (se 2 (by rfl) ⟨874212, by rfl⟩ : syracuseStep 2331233 = 1748425) B1748425
theorem B28677017 : Blo 1032607 28677017 := bstep (se 2 (by rfl) ⟨10753881, by rfl⟩ : syracuseStep 28677017 = 21507763) B21507763
theorem B2331575 : Blo 1032607 2331575 := bstep (se 1 (by rfl) ⟨1748681, by rfl⟩ : syracuseStep 2331575 = 3497363) B3497363
theorem B2332169 : Blo 1032607 2332169 := bstep (se 2 (by rfl) ⟨874563, by rfl⟩ : syracuseStep 2332169 = 1749127) B1749127
theorem B14358059 : Blo 1032607 14358059 := bstep (se 1 (by rfl) ⟨10768544, by rfl⟩ : syracuseStep 14358059 = 21537089) B21537089
theorem B3315485 : Blo 1032607 3315485 := bstep (se 3 (by rfl) ⟨621653, by rfl⟩ : syracuseStep 3315485 = 1243307) B1243307
theorem B4200265 : Blo 1032607 4200265 := bstep (se 2 (by rfl) ⟨1575099, by rfl⟩ : syracuseStep 4200265 = 3150199) B3150199
theorem B1742735 : Blo 1032607 1742735 := bstep (se 1 (by rfl) ⟨1307051, by rfl⟩ : syracuseStep 1742735 = 2614103) B2614103
theorem B1742971 : Blo 1032607 1742971 := bstep (se 1 (by rfl) ⟨1307228, by rfl⟩ : syracuseStep 1742971 = 2614457) B2614457
theorem B3315869 : Blo 1032607 3315869 := bstep (se 3 (by rfl) ⟨621725, by rfl⟩ : syracuseStep 3315869 = 1243451) B1243451
theorem B4200605 : Blo 1032607 4200605 := bstep (se 3 (by rfl) ⟨787613, by rfl⟩ : syracuseStep 4200605 = 1575227) B1575227
theorem B7870769 : Blo 1032607 7870769 := bstep (se 2 (by rfl) ⟨2951538, by rfl⟩ : syracuseStep 7870769 = 5903077) B5903077
theorem B4790657 : Blo 1032607 4790657 := bstep (se 2 (by rfl) ⟨1796496, by rfl⟩ : syracuseStep 4790657 = 3592993) B3592993
theorem B1743835 : Blo 1032607 1743835 := bstep (se 1 (by rfl) ⟨1307876, by rfl⟩ : syracuseStep 1743835 = 2615753) B2615753
theorem B13245839 : Blo 1032607 13245839 := bstep (se 1 (by rfl) ⟨9934379, by rfl⟩ : syracuseStep 13245839 = 19868759) B19868759
theorem B8855027 : Blo 1032607 8855027 := bstep (se 1 (by rfl) ⟨6641270, by rfl⟩ : syracuseStep 8855027 = 13282541) B13282541
theorem B1744463 : Blo 1032607 1744463 := bstep (se 1 (by rfl) ⟨1308347, by rfl⟩ : syracuseStep 1744463 = 2616695) B2616695
theorem B3317395 : Blo 1032607 3317395 := bstep (se 1 (by rfl) ⟨2488046, by rfl⟩ : syracuseStep 3317395 = 4976093) B4976093
theorem B3317611 : Blo 1032607 3317611 := bstep (se 1 (by rfl) ⟨2488208, by rfl⟩ : syracuseStep 3317611 = 4976417) B4976417
theorem B6627689 : Blo 1032607 6627689 := bstep (se 2 (by rfl) ⟨2485383, by rfl⟩ : syracuseStep 6627689 = 4970767) B4970767
theorem B8069509 : Blo 1032607 8069509 := bstep (se 4 (by rfl) ⟨756516, by rfl⟩ : syracuseStep 8069509 = 1513033) B1513033
theorem B1745327 : Blo 1032607 1745327 := bstep (se 1 (by rfl) ⟨1308995, by rfl⟩ : syracuseStep 1745327 = 2617991) B2617991
theorem B1548923 : Blo 1032607 1548923 := bstep (se 1 (by rfl) ⟨1161692, by rfl⟩ : syracuseStep 1548923 = 2323385) B2323385
theorem B1549049 : Blo 1032607 1549049 := bstep (se 2 (by rfl) ⟨580893, by rfl⟩ : syracuseStep 1549049 = 1161787) B1161787
theorem B1549151 : Blo 1032607 1549151 := bstep (se 1 (by rfl) ⟨1161863, by rfl⟩ : syracuseStep 1549151 = 2323727) B2323727
theorem B1745759 : Blo 1032607 1745759 := bstep (se 1 (by rfl) ⟨1309319, by rfl⟩ : syracuseStep 1745759 = 2618639) B2618639
theorem B1549163 : Blo 1032607 1549163 := bstep (se 1 (by rfl) ⟨1161872, by rfl⟩ : syracuseStep 1549163 = 2323745) B2323745
theorem B5677931 : Blo 1032607 5677931 := bstep (se 1 (by rfl) ⟨4258448, by rfl⟩ : syracuseStep 5677931 = 8516897) B8516897
theorem B3318841 : Blo 1032607 3318841 := bstep (se 2 (by rfl) ⟨1244565, by rfl⟩ : syracuseStep 3318841 = 2489131) B2489131
theorem B1549391 : Blo 1032607 1549391 := bstep (se 1 (by rfl) ⟨1162043, by rfl⟩ : syracuseStep 1549391 = 2324087) B2324087
theorem B1549511 : Blo 1032607 1549511 := bstep (se 1 (by rfl) ⟨1162133, by rfl⟩ : syracuseStep 1549511 = 2324267) B2324267
theorem B1549673 : Blo 1032607 1549673 := bstep (se 2 (by rfl) ⟨581127, by rfl⟩ : syracuseStep 1549673 = 1162255) B1162255
theorem B1746319 : Blo 1032607 1746319 := bstep (se 1 (by rfl) ⟨1309739, by rfl⟩ : syracuseStep 1746319 = 2619479) B2619479
theorem B11773349 : Blo 1032607 11773349 := bstep (se 4 (by rfl) ⟨1103751, by rfl⟩ : syracuseStep 11773349 = 2207503) B2207503
theorem B1549751 : Blo 1032607 1549751 := bstep (se 1 (by rfl) ⟨1162313, by rfl⟩ : syracuseStep 1549751 = 2324627) B2324627
theorem B1549787 : Blo 1032607 1549787 := bstep (se 1 (by rfl) ⟨1162340, by rfl⟩ : syracuseStep 1549787 = 2324681) B2324681
theorem B13248299 : Blo 1032607 13248299 := bstep (se 1 (by rfl) ⟨9936224, by rfl⟩ : syracuseStep 13248299 = 19872449) B19872449
theorem B1550255 : Blo 1032607 1550255 := bstep (se 1 (by rfl) ⟨1162691, by rfl⟩ : syracuseStep 1550255 = 2325383) B2325383
theorem B1550345 : Blo 1032607 1550345 := bstep (se 2 (by rfl) ⟨581379, by rfl⟩ : syracuseStep 1550345 = 1162759) B1162759
theorem B6367247 : Blo 1032607 6367247 := bstep (se 1 (by rfl) ⟨4775435, by rfl⟩ : syracuseStep 6367247 = 9550871) B9550871
theorem B1550375 : Blo 1032607 1550375 := bstep (se 1 (by rfl) ⟨1162781, by rfl⟩ : syracuseStep 1550375 = 2325563) B2325563
theorem B1747001 : Blo 1032607 1747001 := bstep (se 2 (by rfl) ⟨655125, by rfl⟩ : syracuseStep 1747001 = 1310251) B1310251
theorem B1550459 : Blo 1032607 1550459 := bstep (se 1 (by rfl) ⟨1162844, by rfl⟩ : syracuseStep 1550459 = 2325689) B2325689
theorem B1550585 : Blo 1032607 1550585 := bstep (se 2 (by rfl) ⟨581469, by rfl⟩ : syracuseStep 1550585 = 1162939) B1162939
theorem B1550687 : Blo 1032607 1550687 := bstep (se 1 (by rfl) ⟨1163015, by rfl⟩ : syracuseStep 1550687 = 2326031) B2326031
theorem B9447785 : Blo 1032607 9447785 := bstep (se 2 (by rfl) ⟨3542919, by rfl⟩ : syracuseStep 9447785 = 7085839) B7085839
theorem B1550699 : Blo 1032607 1550699 := bstep (se 1 (by rfl) ⟨1163024, by rfl⟩ : syracuseStep 1550699 = 2326049) B2326049
theorem B2795905 : Blo 1032607 2795905 := bstep (se 2 (by rfl) ⟨1048464, by rfl⟩ : syracuseStep 2795905 = 2096929) B2096929
theorem B1550927 : Blo 1032607 1550927 := bstep (se 1 (by rfl) ⟨1163195, by rfl⟩ : syracuseStep 1550927 = 2326391) B2326391
theorem B1551047 : Blo 1032607 1551047 := bstep (se 1 (by rfl) ⟨1163285, by rfl⟩ : syracuseStep 1551047 = 2326571) B2326571
theorem B1747703 : Blo 1032607 1747703 := bstep (se 1 (by rfl) ⟨1310777, by rfl⟩ : syracuseStep 1747703 = 2621555) B2621555
theorem B1551209 : Blo 1032607 1551209 := bstep (se 2 (by rfl) ⟨581703, by rfl⟩ : syracuseStep 1551209 = 1163407) B1163407
theorem B1551287 : Blo 1032607 1551287 := bstep (se 1 (by rfl) ⟨1163465, by rfl⟩ : syracuseStep 1551287 = 2326931) B2326931
theorem B1551323 : Blo 1032607 1551323 := bstep (se 1 (by rfl) ⟨1163492, by rfl⟩ : syracuseStep 1551323 = 2326985) B2326985
theorem B3779641 : Blo 1032607 3779641 := bstep (se 2 (by rfl) ⟨1417365, by rfl⟩ : syracuseStep 3779641 = 2834731) B2834731
theorem B1748047 : Blo 1032607 1748047 := bstep (se 1 (by rfl) ⟨1311035, by rfl⟩ : syracuseStep 1748047 = 2622071) B2622071
theorem B1748297 : Blo 1032607 1748297 := bstep (se 2 (by rfl) ⟨655611, by rfl⟩ : syracuseStep 1748297 = 1311223) B1311223
theorem B2796943 : Blo 1032607 2796943 := bstep (se 1 (by rfl) ⟨2097707, by rfl⟩ : syracuseStep 2796943 = 4195415) B4195415
theorem B1551791 : Blo 1032607 1551791 := bstep (se 1 (by rfl) ⟨1163843, by rfl⟩ : syracuseStep 1551791 = 2327687) B2327687
theorem B1551881 : Blo 1032607 1551881 := bstep (se 2 (by rfl) ⟨581955, by rfl⟩ : syracuseStep 1551881 = 1163911) B1163911
theorem B1551911 : Blo 1032607 1551911 := bstep (se 1 (by rfl) ⟨1163933, by rfl⟩ : syracuseStep 1551911 = 2327867) B2327867
theorem B1551995 : Blo 1032607 1551995 := bstep (se 1 (by rfl) ⟨1163996, by rfl⟩ : syracuseStep 1551995 = 2327993) B2327993
theorem B1552121 : Blo 1032607 1552121 := bstep (se 2 (by rfl) ⟨582045, by rfl⟩ : syracuseStep 1552121 = 1164091) B1164091
theorem B1748729 : Blo 1032607 1748729 := bstep (se 2 (by rfl) ⟨655773, by rfl⟩ : syracuseStep 1748729 = 1311547) B1311547
theorem B3485483 : Blo 1032607 3485483 := bstep (se 1 (by rfl) ⟨2614112, by rfl⟩ : syracuseStep 3485483 = 5228225) B5228225
theorem B1552223 : Blo 1032607 1552223 := bstep (se 1 (by rfl) ⟨1164167, by rfl⟩ : syracuseStep 1552223 = 2328335) B2328335
theorem B1552235 : Blo 1032607 1552235 := bstep (se 1 (by rfl) ⟨1164176, by rfl⟩ : syracuseStep 1552235 = 2328353) B2328353
theorem B1748911 : Blo 1032607 1748911 := bstep (se 1 (by rfl) ⟨1311683, by rfl⟩ : syracuseStep 1748911 = 2623367) B2623367
theorem B7450555 : Blo 1032607 7450555 := bstep (se 1 (by rfl) ⟨5587916, by rfl⟩ : syracuseStep 7450555 = 11175833) B11175833
theorem B2207675 : Blo 1032607 2207675 := bstep (se 1 (by rfl) ⟨1655756, by rfl⟩ : syracuseStep 2207675 = 3311513) B3311513
theorem B1748999 : Blo 1032607 1748999 := bstep (se 1 (by rfl) ⟨1311749, by rfl⟩ : syracuseStep 1748999 = 2623499) B2623499
theorem B3485753 : Blo 1032607 3485753 := bstep (se 2 (by rfl) ⟨1307157, by rfl⟩ : syracuseStep 3485753 = 2614315) B2614315
theorem B1552463 : Blo 1032607 1552463 := bstep (se 1 (by rfl) ⟨1164347, by rfl⟩ : syracuseStep 1552463 = 2328695) B2328695
theorem B1552583 : Blo 1032607 1552583 := bstep (se 1 (by rfl) ⟨1164437, by rfl⟩ : syracuseStep 1552583 = 2328875) B2328875
theorem B1552745 : Blo 1032607 1552745 := bstep (se 2 (by rfl) ⟨582279, by rfl⟩ : syracuseStep 1552745 = 1164559) B1164559
theorem B3486077 : Blo 1032607 3486077 := bstep (se 3 (by rfl) ⟨653639, by rfl⟩ : syracuseStep 3486077 = 1307279) B1307279
theorem B1552823 : Blo 1032607 1552823 := bstep (se 1 (by rfl) ⟨1164617, by rfl⟩ : syracuseStep 1552823 = 2329235) B2329235
theorem B1552859 : Blo 1032607 1552859 := bstep (se 1 (by rfl) ⟨1164644, by rfl⟩ : syracuseStep 1552859 = 2329289) B2329289
theorem B3486347 : Blo 1032607 3486347 := bstep (se 1 (by rfl) ⟨2614760, by rfl⟩ : syracuseStep 3486347 = 5229521) B5229521
theorem B7844525 : Blo 1032607 7844525 := bstep (se 3 (by rfl) ⟨1470848, by rfl⟩ : syracuseStep 7844525 = 2941697) B2941697
theorem B1553327 : Blo 1032607 1553327 := bstep (se 1 (by rfl) ⟨1164995, by rfl⟩ : syracuseStep 1553327 = 2329991) B2329991
theorem B1553417 : Blo 1032607 1553417 := bstep (se 2 (by rfl) ⟨582531, by rfl⟩ : syracuseStep 1553417 = 1165063) B1165063
theorem B1553447 : Blo 1032607 1553447 := bstep (se 1 (by rfl) ⟨1165085, by rfl⟩ : syracuseStep 1553447 = 2330171) B2330171
theorem B1553531 : Blo 1032607 1553531 := bstep (se 1 (by rfl) ⟨1165148, by rfl⟩ : syracuseStep 1553531 = 2330297) B2330297
theorem B3978487 : Blo 1032607 3978487 := bstep (se 1 (by rfl) ⟨2983865, by rfl⟩ : syracuseStep 3978487 = 5967731) B5967731
theorem B1553657 : Blo 1032607 1553657 := bstep (se 2 (by rfl) ⟨582621, by rfl⟩ : syracuseStep 1553657 = 1165243) B1165243
theorem B1553759 : Blo 1032607 1553759 := bstep (se 1 (by rfl) ⟨1165319, by rfl⟩ : syracuseStep 1553759 = 2330639) B2330639
theorem B1553771 : Blo 1032607 1553771 := bstep (se 1 (by rfl) ⟨1165328, by rfl⟩ : syracuseStep 1553771 = 2330657) B2330657
theorem B3487265 : Blo 1032607 3487265 := bstep (se 2 (by rfl) ⟨1307724, by rfl⟩ : syracuseStep 3487265 = 2615449) B2615449
theorem B1553999 : Blo 1032607 1553999 := bstep (se 1 (by rfl) ⟨1165499, by rfl⟩ : syracuseStep 1553999 = 2330999) B2330999
theorem B1554119 : Blo 1032607 1554119 := bstep (se 1 (by rfl) ⟨1165589, by rfl⟩ : syracuseStep 1554119 = 2331179) B2331179
theorem B3487481 : Blo 1032607 3487481 := bstep (se 2 (by rfl) ⟨1307805, by rfl⟩ : syracuseStep 3487481 = 2615611) B2615611
theorem B1554281 : Blo 1032607 1554281 := bstep (se 2 (by rfl) ⟨582855, by rfl⟩ : syracuseStep 1554281 = 1165711) B1165711
theorem B6633377 : Blo 1032607 6633377 := bstep (se 2 (by rfl) ⟨2487516, by rfl⟩ : syracuseStep 6633377 = 4975033) B4975033
theorem B1554359 : Blo 1032607 1554359 := bstep (se 1 (by rfl) ⟨1165769, by rfl⟩ : syracuseStep 1554359 = 2331539) B2331539
theorem B17938385 : Blo 1032607 17938385 := bstep (se 2 (by rfl) ⟨6726894, by rfl⟩ : syracuseStep 17938385 = 13453789) B13453789
theorem B1554395 : Blo 1032607 1554395 := bstep (se 1 (by rfl) ⟨1165796, by rfl⟩ : syracuseStep 1554395 = 2331593) B2331593
theorem B3487751 : Blo 1032607 3487751 := bstep (se 1 (by rfl) ⟨2615813, by rfl⟩ : syracuseStep 3487751 = 5231627) B5231627
theorem B7452749 : Blo 1032607 7452749 := bstep (se 3 (by rfl) ⟨1397390, by rfl⟩ : syracuseStep 7452749 = 2794781) B2794781
theorem B3487859 : Blo 1032607 3487859 := bstep (se 1 (by rfl) ⟨2615894, by rfl⟩ : syracuseStep 3487859 = 5231789) B5231789
theorem B3488129 : Blo 1032607 3488129 := bstep (se 2 (by rfl) ⟨1308048, by rfl⟩ : syracuseStep 3488129 = 2616097) B2616097
theorem B1554863 : Blo 1032607 1554863 := bstep (se 1 (by rfl) ⟨1166147, by rfl⟩ : syracuseStep 1554863 = 2332295) B2332295
theorem B21543371 : Blo 1032607 21543371 := bstep (se 1 (by rfl) ⟨16157528, by rfl⟩ : syracuseStep 21543371 = 32315057) B32315057
theorem B2210503 : Blo 1032607 2210503 := bstep (se 1 (by rfl) ⟨1657877, by rfl⟩ : syracuseStep 2210503 = 3315755) B3315755
theorem B7846955 : Blo 1032607 7846955 := bstep (se 1 (by rfl) ⟨5885216, by rfl⟩ : syracuseStep 7846955 = 11770433) B11770433
theorem B1162363 : Blo 1032607 1162363 := bstep (se 1 (by rfl) ⟨871772, by rfl⟩ : syracuseStep 1162363 = 1743545) B1743545
theorem B3488939 : Blo 1032607 3488939 := bstep (se 1 (by rfl) ⟨2616704, by rfl⟩ : syracuseStep 3488939 = 5233409) B5233409
theorem B89636381 : Blo 1032607 89636381 := bstep (se 3 (by rfl) ⟨16806821, by rfl⟩ : syracuseStep 89636381 = 33613643) B33613643
theorem B1162831 : Blo 1032607 1162831 := bstep (se 1 (by rfl) ⟨872123, by rfl⟩ : syracuseStep 1162831 = 1744247) B1744247
theorem B3489479 : Blo 1032607 3489479 := bstep (se 1 (by rfl) ⟨2617109, by rfl⟩ : syracuseStep 3489479 = 5234219) B5234219
theorem B25509613 : Blo 1032607 25509613 := bstep (se 3 (by rfl) ⟨4783052, by rfl⟩ : syracuseStep 25509613 = 9566105) B9566105
theorem B1490681 : Blo 1032607 1490681 := bstep (se 2 (by rfl) ⟨559005, by rfl⟩ : syracuseStep 1490681 = 1118011) B1118011
theorem B1163227 : Blo 1032607 1163227 := bstep (se 1 (by rfl) ⟨872420, by rfl⟩ : syracuseStep 1163227 = 1744841) B1744841
theorem B14926139 : Blo 1032607 14926139 := bstep (se 1 (by rfl) ⟨11194604, by rfl⟩ : syracuseStep 14926139 = 22389209) B22389209
theorem B6635837 : Blo 1032607 6635837 := bstep (se 3 (by rfl) ⟨1244219, by rfl⟩ : syracuseStep 6635837 = 2488439) B2488439
theorem B1032623 : Blo 1032607 1032623 := bstep (se 1 (by rfl) ⟨774467, by rfl⟩ : syracuseStep 1032623 = 1548935) B1548935
theorem B1163695 : Blo 1032607 1163695 := bstep (se 1 (by rfl) ⟨872771, by rfl⟩ : syracuseStep 1163695 = 1745543) B1745543
theorem B1032647 : Blo 1032607 1032647 := bstep (se 1 (by rfl) ⟨774485, by rfl⟩ : syracuseStep 1032647 = 1548971) B1548971
theorem B1032667 : Blo 1032607 1032667 := bstep (se 1 (by rfl) ⟨774500, by rfl⟩ : syracuseStep 1032667 = 1549001) B1549001
theorem B1032743 : Blo 1032607 1032743 := bstep (se 1 (by rfl) ⟨774557, by rfl⟩ : syracuseStep 1032743 = 1549115) B1549115
theorem B3490343 : Blo 1032607 3490343 := bstep (se 1 (by rfl) ⟨2617757, by rfl⟩ : syracuseStep 3490343 = 5235515) B5235515
theorem B1032783 : Blo 1032607 1032783 := bstep (se 1 (by rfl) ⟨774587, by rfl⟩ : syracuseStep 1032783 = 1549175) B1549175
theorem B1032799 : Blo 1032607 1032799 := bstep (se 1 (by rfl) ⟨774599, by rfl⟩ : syracuseStep 1032799 = 1549199) B1549199
theorem B1032827 : Blo 1032607 1032827 := bstep (se 1 (by rfl) ⟨774620, by rfl⟩ : syracuseStep 1032827 = 1549241) B1549241
theorem B6046343 : Blo 1032607 6046343 := bstep (se 1 (by rfl) ⟨4534757, by rfl⟩ : syracuseStep 6046343 = 9069515) B9069515
theorem B3490451 : Blo 1032607 3490451 := bstep (se 1 (by rfl) ⟨2617838, by rfl⟩ : syracuseStep 3490451 = 5235677) B5235677
theorem B1032879 : Blo 1032607 1032879 := bstep (se 1 (by rfl) ⟨774659, by rfl⟩ : syracuseStep 1032879 = 1549319) B1549319
theorem B1032903 : Blo 1032607 1032903 := bstep (se 1 (by rfl) ⟨774677, by rfl⟩ : syracuseStep 1032903 = 1549355) B1549355
theorem B1032923 : Blo 1032607 1032923 := bstep (se 1 (by rfl) ⟨774692, by rfl⟩ : syracuseStep 1032923 = 1549385) B1549385
theorem B16761613 : Blo 1032607 16761613 := bstep (se 3 (by rfl) ⟨3142802, by rfl⟩ : syracuseStep 16761613 = 6285605) B6285605
theorem B1032999 : Blo 1032607 1032999 := bstep (se 1 (by rfl) ⟨774749, by rfl⟩ : syracuseStep 1032999 = 1549499) B1549499
theorem B1033039 : Blo 1032607 1033039 := bstep (se 1 (by rfl) ⟨774779, by rfl⟩ : syracuseStep 1033039 = 1549559) B1549559
theorem B1033055 : Blo 1032607 1033055 := bstep (se 1 (by rfl) ⟨774791, by rfl⟩ : syracuseStep 1033055 = 1549583) B1549583
theorem B1164127 : Blo 1032607 1164127 := bstep (se 1 (by rfl) ⟨873095, by rfl⟩ : syracuseStep 1164127 = 1746191) B1746191
theorem B3490667 : Blo 1032607 3490667 := bstep (se 1 (by rfl) ⟨2618000, by rfl⟩ : syracuseStep 3490667 = 5236001) B5236001
theorem B1033083 : Blo 1032607 1033083 := bstep (se 1 (by rfl) ⟨774812, by rfl⟩ : syracuseStep 1033083 = 1549625) B1549625
theorem B3490721 : Blo 1032607 3490721 := bstep (se 2 (by rfl) ⟨1309020, by rfl⟩ : syracuseStep 3490721 = 2618041) B2618041
theorem B1033135 : Blo 1032607 1033135 := bstep (se 1 (by rfl) ⟨774851, by rfl⟩ : syracuseStep 1033135 = 1549703) B1549703
theorem B1033159 : Blo 1032607 1033159 := bstep (se 1 (by rfl) ⟨774869, by rfl⟩ : syracuseStep 1033159 = 1549739) B1549739
theorem B1033179 : Blo 1032607 1033179 := bstep (se 1 (by rfl) ⟨774884, by rfl⟩ : syracuseStep 1033179 = 1549769) B1549769
theorem B1033255 : Blo 1032607 1033255 := bstep (se 1 (by rfl) ⟨774941, by rfl⟩ : syracuseStep 1033255 = 1549883) B1549883
theorem B1033295 : Blo 1032607 1033295 := bstep (se 1 (by rfl) ⟨774971, by rfl⟩ : syracuseStep 1033295 = 1549943) B1549943
theorem B1033311 : Blo 1032607 1033311 := bstep (se 1 (by rfl) ⟨774983, by rfl⟩ : syracuseStep 1033311 = 1549967) B1549967
theorem B1033339 : Blo 1032607 1033339 := bstep (se 1 (by rfl) ⟨775004, by rfl⟩ : syracuseStep 1033339 = 1550009) B1550009
theorem B1033391 : Blo 1032607 1033391 := bstep (se 1 (by rfl) ⟨775043, by rfl⟩ : syracuseStep 1033391 = 1550087) B1550087
theorem B1033415 : Blo 1032607 1033415 := bstep (se 1 (by rfl) ⟨775061, by rfl⟩ : syracuseStep 1033415 = 1550123) B1550123
theorem B1164487 : Blo 1032607 1164487 := bstep (se 1 (by rfl) ⟨873365, by rfl⟩ : syracuseStep 1164487 = 1746731) B1746731
theorem B1033435 : Blo 1032607 1033435 := bstep (se 1 (by rfl) ⟨775076, by rfl⟩ : syracuseStep 1033435 = 1550153) B1550153
theorem B1033511 : Blo 1032607 1033511 := bstep (se 1 (by rfl) ⟨775133, by rfl⟩ : syracuseStep 1033511 = 1550267) B1550267
theorem B1033551 : Blo 1032607 1033551 := bstep (se 1 (by rfl) ⟨775163, by rfl⟩ : syracuseStep 1033551 = 1550327) B1550327
theorem B1033567 : Blo 1032607 1033567 := bstep (se 1 (by rfl) ⟨775175, by rfl⟩ : syracuseStep 1033567 = 1550351) B1550351
theorem B1033595 : Blo 1032607 1033595 := bstep (se 1 (by rfl) ⟨775196, by rfl⟩ : syracuseStep 1033595 = 1550393) B1550393
theorem B5227901 : Blo 1032607 5227901 := bstep (se 3 (by rfl) ⟨980231, by rfl⟩ : syracuseStep 5227901 = 1960463) B1960463
theorem B1033647 : Blo 1032607 1033647 := bstep (se 1 (by rfl) ⟨775235, by rfl⟩ : syracuseStep 1033647 = 1550471) B1550471
theorem B1033671 : Blo 1032607 1033671 := bstep (se 1 (by rfl) ⟨775253, by rfl⟩ : syracuseStep 1033671 = 1550507) B1550507
theorem B1033691 : Blo 1032607 1033691 := bstep (se 1 (by rfl) ⟨775268, by rfl⟩ : syracuseStep 1033691 = 1550537) B1550537
theorem B3491315 : Blo 1032607 3491315 := bstep (se 1 (by rfl) ⟨2618486, by rfl⟩ : syracuseStep 3491315 = 5236973) B5236973
theorem B1033767 : Blo 1032607 1033767 := bstep (se 1 (by rfl) ⟨775325, by rfl⟩ : syracuseStep 1033767 = 1550651) B1550651
theorem B1656359 : Blo 1032607 1656359 := bstep (se 1 (by rfl) ⟨1242269, by rfl⟩ : syracuseStep 1656359 = 2484539) B2484539
theorem B1033807 : Blo 1032607 1033807 := bstep (se 1 (by rfl) ⟨775355, by rfl⟩ : syracuseStep 1033807 = 1550711) B1550711
theorem B1033823 : Blo 1032607 1033823 := bstep (se 1 (by rfl) ⟨775367, by rfl⟩ : syracuseStep 1033823 = 1550735) B1550735
theorem B1033851 : Blo 1032607 1033851 := bstep (se 1 (by rfl) ⟨775388, by rfl⟩ : syracuseStep 1033851 = 1550777) B1550777
theorem B1033903 : Blo 1032607 1033903 := bstep (se 1 (by rfl) ⟨775427, by rfl⟩ : syracuseStep 1033903 = 1550855) B1550855
theorem B3983033 : Blo 1032607 3983033 := bstep (se 2 (by rfl) ⟨1493637, by rfl⟩ : syracuseStep 3983033 = 2987275) B2987275
theorem B1033927 : Blo 1032607 1033927 := bstep (se 1 (by rfl) ⟨775445, by rfl⟩ : syracuseStep 1033927 = 1550891) B1550891
theorem B1033947 : Blo 1032607 1033947 := bstep (se 1 (by rfl) ⟨775460, by rfl⟩ : syracuseStep 1033947 = 1550921) B1550921
theorem B1034023 : Blo 1032607 1034023 := bstep (se 1 (by rfl) ⟨775517, by rfl⟩ : syracuseStep 1034023 = 1551035) B1551035
theorem B1034063 : Blo 1032607 1034063 := bstep (se 1 (by rfl) ⟨775547, by rfl⟩ : syracuseStep 1034063 = 1551095) B1551095
theorem B1034079 : Blo 1032607 1034079 := bstep (se 1 (by rfl) ⟨775559, by rfl⟩ : syracuseStep 1034079 = 1551119) B1551119
theorem B1034107 : Blo 1032607 1034107 := bstep (se 1 (by rfl) ⟨775580, by rfl⟩ : syracuseStep 1034107 = 1551161) B1551161
theorem B1034159 : Blo 1032607 1034159 := bstep (se 1 (by rfl) ⟨775619, by rfl⟩ : syracuseStep 1034159 = 1551239) B1551239
theorem B1034183 : Blo 1032607 1034183 := bstep (se 1 (by rfl) ⟨775637, by rfl⟩ : syracuseStep 1034183 = 1551275) B1551275
theorem B11782097 : Blo 1032607 11782097 := bstep (se 2 (by rfl) ⟨4418286, by rfl⟩ : syracuseStep 11782097 = 8836573) B8836573
theorem B1034203 : Blo 1032607 1034203 := bstep (se 1 (by rfl) ⟨775652, by rfl⟩ : syracuseStep 1034203 = 1551305) B1551305
theorem B3491855 : Blo 1032607 3491855 := bstep (se 1 (by rfl) ⟨2618891, by rfl⟩ : syracuseStep 3491855 = 5237783) B5237783
theorem B5883941 : Blo 1032607 5883941 := bstep (se 4 (by rfl) ⟨551619, by rfl⟩ : syracuseStep 5883941 = 1103239) B1103239
theorem B1034279 : Blo 1032607 1034279 := bstep (se 1 (by rfl) ⟨775709, by rfl⟩ : syracuseStep 1034279 = 1551419) B1551419
theorem B1165351 : Blo 1032607 1165351 := bstep (se 1 (by rfl) ⟨874013, by rfl⟩ : syracuseStep 1165351 = 1748027) B1748027
theorem B1034319 : Blo 1032607 1034319 := bstep (se 1 (by rfl) ⟨775739, by rfl⟩ : syracuseStep 1034319 = 1551479) B1551479
theorem B1034335 : Blo 1032607 1034335 := bstep (se 1 (by rfl) ⟨775751, by rfl⟩ : syracuseStep 1034335 = 1551503) B1551503
theorem B1034363 : Blo 1032607 1034363 := bstep (se 1 (by rfl) ⟨775772, by rfl⟩ : syracuseStep 1034363 = 1551545) B1551545
theorem B1034415 : Blo 1032607 1034415 := bstep (se 1 (by rfl) ⟨775811, by rfl⟩ : syracuseStep 1034415 = 1551623) B1551623
theorem B1034439 : Blo 1032607 1034439 := bstep (se 1 (by rfl) ⟨775829, by rfl⟩ : syracuseStep 1034439 = 1551659) B1551659
theorem B1034459 : Blo 1032607 1034459 := bstep (se 1 (by rfl) ⟨775844, by rfl⟩ : syracuseStep 1034459 = 1551689) B1551689
theorem B1034535 : Blo 1032607 1034535 := bstep (se 1 (by rfl) ⟨775901, by rfl⟩ : syracuseStep 1034535 = 1551803) B1551803
theorem B1034575 : Blo 1032607 1034575 := bstep (se 1 (by rfl) ⟨775931, by rfl⟩ : syracuseStep 1034575 = 1551863) B1551863
theorem B1034591 : Blo 1032607 1034591 := bstep (se 1 (by rfl) ⟨775943, by rfl⟩ : syracuseStep 1034591 = 1551887) B1551887
theorem B1034619 : Blo 1032607 1034619 := bstep (se 1 (by rfl) ⟨775964, by rfl⟩ : syracuseStep 1034619 = 1551929) B1551929
theorem B1034671 : Blo 1032607 1034671 := bstep (se 1 (by rfl) ⟨776003, by rfl⟩ : syracuseStep 1034671 = 1552007) B1552007
theorem B1034695 : Blo 1032607 1034695 := bstep (se 1 (by rfl) ⟨776021, by rfl⟩ : syracuseStep 1034695 = 1552043) B1552043
theorem B1034715 : Blo 1032607 1034715 := bstep (se 1 (by rfl) ⟨776036, by rfl⟩ : syracuseStep 1034715 = 1552073) B1552073
theorem B5884397 : Blo 1032607 5884397 := bstep (se 3 (by rfl) ⟨1103324, by rfl⟩ : syracuseStep 5884397 = 2206649) B2206649
theorem B7457305 : Blo 1032607 7457305 := bstep (se 2 (by rfl) ⟨2796489, by rfl⟩ : syracuseStep 7457305 = 5592979) B5592979
theorem B3983905 : Blo 1032607 3983905 := bstep (se 2 (by rfl) ⟨1493964, by rfl⟩ : syracuseStep 3983905 = 2987929) B2987929
theorem B1034791 : Blo 1032607 1034791 := bstep (se 1 (by rfl) ⟨776093, by rfl⟩ : syracuseStep 1034791 = 1552187) B1552187
theorem B1034831 : Blo 1032607 1034831 := bstep (se 1 (by rfl) ⟨776123, by rfl⟩ : syracuseStep 1034831 = 1552247) B1552247
theorem B1034847 : Blo 1032607 1034847 := bstep (se 1 (by rfl) ⟨776135, by rfl⟩ : syracuseStep 1034847 = 1552271) B1552271
theorem B3492449 : Blo 1032607 3492449 := bstep (se 2 (by rfl) ⟨1309668, by rfl⟩ : syracuseStep 3492449 = 2619337) B2619337
theorem B1034875 : Blo 1032607 1034875 := bstep (se 1 (by rfl) ⟨776156, by rfl⟩ : syracuseStep 1034875 = 1552313) B1552313
theorem B1034927 : Blo 1032607 1034927 := bstep (se 1 (by rfl) ⟨776195, by rfl⟩ : syracuseStep 1034927 = 1552391) B1552391
theorem B1034951 : Blo 1032607 1034951 := bstep (se 1 (by rfl) ⟨776213, by rfl⟩ : syracuseStep 1034951 = 1552427) B1552427
theorem B2837207 : Blo 1032607 2837207 := bstep (se 1 (by rfl) ⟨2127905, by rfl⟩ : syracuseStep 2837207 = 4255811) B4255811
theorem B1034971 : Blo 1032607 1034971 := bstep (se 1 (by rfl) ⟨776228, by rfl⟩ : syracuseStep 1034971 = 1552457) B1552457
theorem B1035047 : Blo 1032607 1035047 := bstep (se 1 (by rfl) ⟨776285, by rfl⟩ : syracuseStep 1035047 = 1552571) B1552571
theorem B1035087 : Blo 1032607 1035087 := bstep (se 1 (by rfl) ⟨776315, by rfl⟩ : syracuseStep 1035087 = 1552631) B1552631
theorem B1035103 : Blo 1032607 1035103 := bstep (se 1 (by rfl) ⟨776327, by rfl⟩ : syracuseStep 1035103 = 1552655) B1552655
theorem B1035131 : Blo 1032607 1035131 := bstep (se 1 (by rfl) ⟨776348, by rfl⟩ : syracuseStep 1035131 = 1552697) B1552697
theorem B4541359 : Blo 1032607 4541359 := bstep (se 1 (by rfl) ⟨3406019, by rfl⟩ : syracuseStep 4541359 = 6812039) B6812039
theorem B1035183 : Blo 1032607 1035183 := bstep (se 1 (by rfl) ⟨776387, by rfl⟩ : syracuseStep 1035183 = 1552775) B1552775
theorem B1035207 : Blo 1032607 1035207 := bstep (se 1 (by rfl) ⟨776405, by rfl⟩ : syracuseStep 1035207 = 1552811) B1552811
theorem B1035227 : Blo 1032607 1035227 := bstep (se 1 (by rfl) ⟨776420, by rfl⟩ : syracuseStep 1035227 = 1552841) B1552841
theorem B1035303 : Blo 1032607 1035303 := bstep (se 1 (by rfl) ⟨776477, by rfl⟩ : syracuseStep 1035303 = 1552955) B1552955
theorem B1035343 : Blo 1032607 1035343 := bstep (se 1 (by rfl) ⟨776507, by rfl⟩ : syracuseStep 1035343 = 1553015) B1553015
theorem B1035359 : Blo 1032607 1035359 := bstep (se 1 (by rfl) ⟨776519, by rfl⟩ : syracuseStep 1035359 = 1553039) B1553039
theorem B1035387 : Blo 1032607 1035387 := bstep (se 1 (by rfl) ⟨776540, by rfl⟩ : syracuseStep 1035387 = 1553081) B1553081
theorem B7949465 : Blo 1032607 7949465 := bstep (se 2 (by rfl) ⟨2981049, by rfl⟩ : syracuseStep 7949465 = 5962099) B5962099
theorem B5885081 : Blo 1032607 5885081 := bstep (se 2 (by rfl) ⟨2206905, by rfl⟩ : syracuseStep 5885081 = 4413811) B4413811
theorem B1035439 : Blo 1032607 1035439 := bstep (se 1 (by rfl) ⟨776579, by rfl⟩ : syracuseStep 1035439 = 1553159) B1553159
theorem B1035463 : Blo 1032607 1035463 := bstep (se 1 (by rfl) ⟨776597, by rfl⟩ : syracuseStep 1035463 = 1553195) B1553195
theorem B1035483 : Blo 1032607 1035483 := bstep (se 1 (by rfl) ⟨776612, by rfl⟩ : syracuseStep 1035483 = 1553225) B1553225
theorem B1035559 : Blo 1032607 1035559 := bstep (se 1 (by rfl) ⟨776669, by rfl⟩ : syracuseStep 1035559 = 1553339) B1553339
theorem B29871413 : Blo 1032607 29871413 := bstep (se 5 (by rfl) ⟨1400222, by rfl⟩ : syracuseStep 29871413 = 2800445) B2800445
theorem B1035599 : Blo 1032607 1035599 := bstep (se 1 (by rfl) ⟨776699, by rfl⟩ : syracuseStep 1035599 = 1553399) B1553399
theorem B1035615 : Blo 1032607 1035615 := bstep (se 1 (by rfl) ⟨776711, by rfl⟩ : syracuseStep 1035615 = 1553423) B1553423
theorem B1035643 : Blo 1032607 1035643 := bstep (se 1 (by rfl) ⟨776732, by rfl⟩ : syracuseStep 1035643 = 1553465) B1553465
theorem B1035695 : Blo 1032607 1035695 := bstep (se 1 (by rfl) ⟨776771, by rfl⟩ : syracuseStep 1035695 = 1553543) B1553543
theorem B1035719 : Blo 1032607 1035719 := bstep (se 1 (by rfl) ⟨776789, by rfl⟩ : syracuseStep 1035719 = 1553579) B1553579
theorem B1035739 : Blo 1032607 1035739 := bstep (se 1 (by rfl) ⟨776804, by rfl⟩ : syracuseStep 1035739 = 1553609) B1553609
theorem B1035815 : Blo 1032607 1035815 := bstep (se 1 (by rfl) ⟨776861, by rfl⟩ : syracuseStep 1035815 = 1553723) B1553723
theorem B1035855 : Blo 1032607 1035855 := bstep (se 1 (by rfl) ⟨776891, by rfl⟩ : syracuseStep 1035855 = 1553783) B1553783
theorem B1035871 : Blo 1032607 1035871 := bstep (se 1 (by rfl) ⟨776903, by rfl⟩ : syracuseStep 1035871 = 1553807) B1553807
theorem B1035899 : Blo 1032607 1035899 := bstep (se 1 (by rfl) ⟨776924, by rfl⟩ : syracuseStep 1035899 = 1553849) B1553849
theorem B1035951 : Blo 1032607 1035951 := bstep (se 1 (by rfl) ⟨776963, by rfl⟩ : syracuseStep 1035951 = 1553927) B1553927
theorem B1035975 : Blo 1032607 1035975 := bstep (se 1 (by rfl) ⟨776981, by rfl⟩ : syracuseStep 1035975 = 1553963) B1553963
theorem B1035995 : Blo 1032607 1035995 := bstep (se 1 (by rfl) ⟨776996, by rfl⟩ : syracuseStep 1035995 = 1553993) B1553993
theorem B1036071 : Blo 1032607 1036071 := bstep (se 1 (by rfl) ⟨777053, by rfl⟩ : syracuseStep 1036071 = 1554107) B1554107
theorem B1036111 : Blo 1032607 1036111 := bstep (se 1 (by rfl) ⟨777083, by rfl⟩ : syracuseStep 1036111 = 1554167) B1554167
theorem B1036127 : Blo 1032607 1036127 := bstep (se 1 (by rfl) ⟨777095, by rfl⟩ : syracuseStep 1036127 = 1554191) B1554191
theorem B1036155 : Blo 1032607 1036155 := bstep (se 1 (by rfl) ⟨777116, by rfl⟩ : syracuseStep 1036155 = 1554233) B1554233
theorem B12603271 : Blo 1032607 12603271 := bstep (se 1 (by rfl) ⟨9452453, by rfl⟩ : syracuseStep 12603271 = 18904907) B18904907
theorem B1036207 : Blo 1032607 1036207 := bstep (se 1 (by rfl) ⟨777155, by rfl⟩ : syracuseStep 1036207 = 1554311) B1554311
theorem B3723191 : Blo 1032607 3723191 := bstep (se 1 (by rfl) ⟨2792393, by rfl⟩ : syracuseStep 3723191 = 5584787) B5584787
theorem B1036231 : Blo 1032607 1036231 := bstep (se 1 (by rfl) ⟨777173, by rfl⟩ : syracuseStep 1036231 = 1554347) B1554347
theorem B1036251 : Blo 1032607 1036251 := bstep (se 1 (by rfl) ⟨777188, by rfl⟩ : syracuseStep 1036251 = 1554377) B1554377
theorem B22368271 : Blo 1032607 22368271 := bstep (se 1 (by rfl) ⟨16776203, by rfl⟩ : syracuseStep 22368271 = 33552407) B33552407
theorem B3493907 : Blo 1032607 3493907 := bstep (se 1 (by rfl) ⟨2620430, by rfl⟩ : syracuseStep 3493907 = 5240861) B5240861
theorem B1036327 : Blo 1032607 1036327 := bstep (se 1 (by rfl) ⟨777245, by rfl⟩ : syracuseStep 1036327 = 1554491) B1554491
theorem B1036367 : Blo 1032607 1036367 := bstep (se 1 (by rfl) ⟨777275, by rfl⟩ : syracuseStep 1036367 = 1554551) B1554551
theorem B1036383 : Blo 1032607 1036383 := bstep (se 1 (by rfl) ⟨777287, by rfl⟩ : syracuseStep 1036383 = 1554575) B1554575
theorem B1036411 : Blo 1032607 1036411 := bstep (se 1 (by rfl) ⟨777308, by rfl⟩ : syracuseStep 1036411 = 1554617) B1554617
theorem B1036463 : Blo 1032607 1036463 := bstep (se 1 (by rfl) ⟨777347, by rfl⟩ : syracuseStep 1036463 = 1554695) B1554695
theorem B1036487 : Blo 1032607 1036487 := bstep (se 1 (by rfl) ⟨777365, by rfl⟩ : syracuseStep 1036487 = 1554731) B1554731
theorem B1036507 : Blo 1032607 1036507 := bstep (se 1 (by rfl) ⟨777380, by rfl⟩ : syracuseStep 1036507 = 1554761) B1554761
theorem B1036583 : Blo 1032607 1036583 := bstep (se 1 (by rfl) ⟨777437, by rfl⟩ : syracuseStep 1036583 = 1554875) B1554875
theorem B3494231 : Blo 1032607 3494231 := bstep (se 1 (by rfl) ⟨2620673, by rfl⟩ : syracuseStep 3494231 = 5241347) B5241347
theorem B1495675 : Blo 1032607 1495675 := bstep (se 1 (by rfl) ⟨1121756, by rfl⟩ : syracuseStep 1495675 = 2243513) B2243513
theorem B3920683 : Blo 1032607 3920683 := bstep (se 1 (by rfl) ⟨2940512, by rfl⟩ : syracuseStep 3920683 = 5881025) B5881025
theorem B7951279 : Blo 1032607 7951279 := bstep (se 1 (by rfl) ⟨5963459, by rfl⟩ : syracuseStep 7951279 = 11926919) B11926919
theorem B1725497 : Blo 1032607 1725497 := bstep (se 2 (by rfl) ⟨647061, by rfl⟩ : syracuseStep 1725497 = 1294123) B1294123
theorem B9426073 : Blo 1032607 9426073 := bstep (se 2 (by rfl) ⟨3534777, by rfl⟩ : syracuseStep 9426073 = 7069555) B7069555
theorem B6640811 : Blo 1032607 6640811 := bstep (se 1 (by rfl) ⟨4980608, by rfl⟩ : syracuseStep 6640811 = 9961217) B9961217
theorem B1660267 : Blo 1032607 1660267 := bstep (se 1 (by rfl) ⟨1245200, by rfl⟩ : syracuseStep 1660267 = 2490401) B2490401
theorem B3495311 : Blo 1032607 3495311 := bstep (se 1 (by rfl) ⟨2621483, by rfl⟩ : syracuseStep 3495311 = 5242967) B5242967
theorem B1660343 : Blo 1032607 1660343 := bstep (se 1 (by rfl) ⟨1245257, by rfl⟩ : syracuseStep 1660343 = 2490515) B2490515
theorem B5821915 : Blo 1032607 5821915 := bstep (se 1 (by rfl) ⟨4366436, by rfl⟩ : syracuseStep 5821915 = 8732873) B8732873
theorem B5232275 : Blo 1032607 5232275 := bstep (se 1 (by rfl) ⟨3924206, by rfl⟩ : syracuseStep 5232275 = 7848413) B7848413
theorem B6641351 : Blo 1032607 6641351 := bstep (se 1 (by rfl) ⟨4981013, by rfl⟩ : syracuseStep 6641351 = 9962027) B9962027
theorem B3495635 : Blo 1032607 3495635 := bstep (se 1 (by rfl) ⟨2621726, by rfl⟩ : syracuseStep 3495635 = 5243453) B5243453
theorem B5036525 : Blo 1032607 5036525 := bstep (se 3 (by rfl) ⟨944348, by rfl⟩ : syracuseStep 5036525 = 1888697) B1888697
theorem B5593625 : Blo 1032607 5593625 := bstep (se 2 (by rfl) ⟨2097609, by rfl⟩ : syracuseStep 5593625 = 4195219) B4195219
theorem B5888771 : Blo 1032607 5888771 := bstep (se 1 (by rfl) ⟨4416578, by rfl⟩ : syracuseStep 5888771 = 8833157) B8833157
theorem B3496823 : Blo 1032607 3496823 := bstep (se 1 (by rfl) ⟨2622617, by rfl⟩ : syracuseStep 3496823 = 5245235) B5245235
theorem B6282319 : Blo 1032607 6282319 := bstep (se 1 (by rfl) ⟨4711739, by rfl⟩ : syracuseStep 6282319 = 9423479) B9423479
theorem B3497039 : Blo 1032607 3497039 := bstep (se 1 (by rfl) ⟨2622779, by rfl⟩ : syracuseStep 3497039 = 5245559) B5245559
theorem B8379773 : Blo 1032607 8379773 := bstep (se 3 (by rfl) ⟨1571207, by rfl⟩ : syracuseStep 8379773 = 3142415) B3142415
theorem B3497417 : Blo 1032607 3497417 := bstep (se 2 (by rfl) ⟨1311531, by rfl⟩ : syracuseStep 3497417 = 2623063) B2623063
theorem B3988955 : Blo 1032607 3988955 := bstep (se 1 (by rfl) ⟨2991716, by rfl⟩ : syracuseStep 3988955 = 5983433) B5983433
theorem B2481673 : Blo 1032607 2481673 := bstep (se 2 (by rfl) ⟨930627, by rfl⟩ : syracuseStep 2481673 = 1861255) B1861255
theorem B3726881 : Blo 1032607 3726881 := bstep (se 2 (by rfl) ⟨1397580, by rfl⟩ : syracuseStep 3726881 = 2795161) B2795161
theorem B5594663 : Blo 1032607 5594663 := bstep (se 1 (by rfl) ⟨4195997, by rfl⟩ : syracuseStep 5594663 = 8391995) B8391995
theorem B7855703 : Blo 1032607 7855703 := bstep (se 1 (by rfl) ⟨5891777, by rfl⟩ : syracuseStep 7855703 = 11783555) B11783555
theorem B7462523 : Blo 1032607 7462523 := bstep (se 1 (by rfl) ⟨5596892, by rfl⟩ : syracuseStep 7462523 = 11193785) B11193785
theorem B5037767 : Blo 1032607 5037767 := bstep (se 1 (by rfl) ⟨3778325, by rfl⟩ : syracuseStep 5037767 = 7556651) B7556651
theorem B3497687 : Blo 1032607 3497687 := bstep (se 1 (by rfl) ⟨2623265, by rfl⟩ : syracuseStep 3497687 = 5246531) B5246531
theorem B3923873 : Blo 1032607 3923873 := bstep (se 2 (by rfl) ⟨1471452, by rfl⟩ : syracuseStep 3923873 = 2942905) B2942905
theorem B3497903 : Blo 1032607 3497903 := bstep (se 1 (by rfl) ⟨2623427, by rfl⟩ : syracuseStep 3497903 = 5246855) B5246855
theorem B1892279 : Blo 1032607 1892279 := bstep (se 1 (by rfl) ⟨1419209, by rfl⟩ : syracuseStep 1892279 = 2838419) B2838419
theorem B11165627 : Blo 1032607 11165627 := bstep (se 1 (by rfl) ⟨8374220, by rfl⟩ : syracuseStep 11165627 = 16748441) B16748441
theorem B7463447 : Blo 1032607 7463447 := bstep (se 1 (by rfl) ⟨5597585, by rfl⟩ : syracuseStep 7463447 = 11195171) B11195171
theorem B7955003 : Blo 1032607 7955003 := bstep (se 1 (by rfl) ⟨5966252, by rfl⟩ : syracuseStep 7955003 = 11932505) B11932505
theorem B2613971 : Blo 1032607 2613971 := bstep (se 1 (by rfl) ⟨1960478, by rfl⟩ : syracuseStep 2613971 = 3920957) B3920957
theorem B2482903 : Blo 1032607 2482903 := bstep (se 1 (by rfl) ⟨1862177, by rfl⟩ : syracuseStep 2482903 = 3724355) B3724355
theorem B4973341 : Blo 1032607 4973341 := bstep (se 3 (by rfl) ⟨932501, by rfl⟩ : syracuseStep 4973341 = 1865003) B1865003
theorem B3924845 : Blo 1032607 3924845 := bstep (se 3 (by rfl) ⟨735908, by rfl⟩ : syracuseStep 3924845 = 1471817) B1471817
theorem B3925529 : Blo 1032607 3925529 := bstep (se 2 (by rfl) ⟨1472073, by rfl⟩ : syracuseStep 3925529 = 2944147) B2944147
theorem B3925543 : Blo 1032607 3925543 := bstep (se 1 (by rfl) ⟨2944157, by rfl⟩ : syracuseStep 3925543 = 5888315) B5888315
theorem B32237473 : Blo 1032607 32237473 := bstep (se 2 (by rfl) ⟨12089052, by rfl⟩ : syracuseStep 32237473 = 24178105) B24178105
theorem B1861559 : Blo 1032607 1861559 := bstep (se 1 (by rfl) ⟨1396169, by rfl⟩ : syracuseStep 1861559 = 2792339) B2792339
theorem B3926333 : Blo 1032607 3926333 := bstep (se 3 (by rfl) ⟨736187, by rfl⟩ : syracuseStep 3926333 = 1472375) B1472375
theorem B3926515 : Blo 1032607 3926515 := bstep (se 1 (by rfl) ⟨2944886, by rfl⟩ : syracuseStep 3926515 = 5889773) B5889773
theorem B13232717 : Blo 1032607 13232717 := bstep (se 3 (by rfl) ⟨2481134, by rfl⟩ : syracuseStep 13232717 = 4962269) B4962269
theorem B2943611 : Blo 1032607 2943611 := bstep (se 1 (by rfl) ⟨2207708, by rfl⟩ : syracuseStep 2943611 = 4415417) B4415417
theorem B5237459 : Blo 1032607 5237459 := bstep (se 1 (by rfl) ⟨3928094, by rfl⟩ : syracuseStep 5237459 = 7856189) B7856189
theorem B2943839 : Blo 1032607 2943839 := bstep (se 1 (by rfl) ⟨2207879, by rfl⟩ : syracuseStep 2943839 = 4415759) B4415759
theorem B2616239 : Blo 1032607 2616239 := bstep (se 1 (by rfl) ⟨1962179, by rfl⟩ : syracuseStep 2616239 = 3924359) B3924359
theorem B8842283 : Blo 1032607 8842283 := bstep (se 1 (by rfl) ⟨6631712, by rfl⟩ : syracuseStep 8842283 = 13263425) B13263425
theorem B1961435 : Blo 1032607 1961435 := bstep (se 1 (by rfl) ⟨1471076, by rfl⟩ : syracuseStep 1961435 = 2942153) B2942153
theorem B2616857 : Blo 1032607 2616857 := bstep (se 2 (by rfl) ⟨981321, by rfl⟩ : syracuseStep 2616857 = 1962643) B1962643
theorem B1961671 : Blo 1032607 1961671 := bstep (se 1 (by rfl) ⟨1471253, by rfl⟩ : syracuseStep 1961671 = 2942507) B2942507
theorem B3927761 : Blo 1032607 3927761 := bstep (se 2 (by rfl) ⟨1472910, by rfl⟩ : syracuseStep 3927761 = 2945821) B2945821
theorem B7860077 : Blo 1032607 7860077 := bstep (se 3 (by rfl) ⟨1473764, by rfl⟩ : syracuseStep 7860077 = 2947529) B2947529
theorem B7172027 : Blo 1032607 7172027 := bstep (se 1 (by rfl) ⟨5379020, by rfl⟩ : syracuseStep 7172027 = 10758041) B10758041
theorem B13463567 : Blo 1032607 13463567 := bstep (se 1 (by rfl) ⟨10097675, by rfl⟩ : syracuseStep 13463567 = 20195351) B20195351
theorem B3928445 : Blo 1032607 3928445 := bstep (se 3 (by rfl) ⟨736583, by rfl⟩ : syracuseStep 3928445 = 1473167) B1473167
theorem B2945423 : Blo 1032607 2945423 := bstep (se 1 (by rfl) ⟨2209067, by rfl⟩ : syracuseStep 2945423 = 4418135) B4418135
theorem B1241563 : Blo 1032607 1241563 := bstep (se 1 (by rfl) ⟨931172, by rfl⟩ : syracuseStep 1241563 = 1862345) B1862345
theorem B2093587 : Blo 1032607 2093587 := bstep (se 1 (by rfl) ⟨1570190, by rfl⟩ : syracuseStep 2093587 = 3140381) B3140381
theorem B1307335 : Blo 1032607 1307335 := bstep (se 1 (by rfl) ⟨980501, by rfl⟩ : syracuseStep 1307335 = 1961003) B1961003
theorem B2486999 : Blo 1032607 2486999 := bstep (se 1 (by rfl) ⟨1865249, by rfl⟩ : syracuseStep 2486999 = 3730499) B3730499
theorem B1471225 : Blo 1032607 1471225 := bstep (se 2 (by rfl) ⟨551709, by rfl⟩ : syracuseStep 1471225 = 1103419) B1103419
theorem B21263255 : Blo 1032607 21263255 := bstep (se 1 (by rfl) ⟨15947441, by rfl⟩ : syracuseStep 21263255 = 31894883) B31894883
theorem B5239727 : Blo 1032607 5239727 := bstep (se 1 (by rfl) ⟨3929795, by rfl⟩ : syracuseStep 5239727 = 7859591) B7859591
theorem B10777519 : Blo 1032607 10777519 := bstep (se 1 (by rfl) ⟨8083139, by rfl⟩ : syracuseStep 10777519 = 16166279) B16166279
theorem B2323475 : Blo 1032607 2323475 := bstep (se 1 (by rfl) ⟨1742606, by rfl⟩ : syracuseStep 2323475 = 3485213) B3485213
theorem B1865033 : Blo 1032607 1865033 := bstep (se 2 (by rfl) ⟨699387, by rfl⟩ : syracuseStep 1865033 = 1398775) B1398775
theorem B3929431 : Blo 1032607 3929431 := bstep (se 1 (by rfl) ⟨2947073, by rfl⟩ : syracuseStep 3929431 = 5894147) B5894147
theorem B2323817 : Blo 1032607 2323817 := bstep (se 2 (by rfl) ⟨871431, by rfl⟩ : syracuseStep 2323817 = 1742863) B1742863
theorem B1308079 : Blo 1032607 1308079 := bstep (se 1 (by rfl) ⟨981059, by rfl⟩ : syracuseStep 1308079 = 1962119) B1962119
theorem B36271601 : Blo 1032607 36271601 := bstep (se 2 (by rfl) ⟨13601850, by rfl⟩ : syracuseStep 36271601 = 27203701) B27203701
theorem B11171333 : Blo 1032607 11171333 := bstep (se 4 (by rfl) ⟨1047312, by rfl⟩ : syracuseStep 11171333 = 2094625) B2094625
theorem B1963577 : Blo 1032607 1963577 := bstep (se 2 (by rfl) ⟨736341, by rfl⟩ : syracuseStep 1963577 = 1472683) B1472683
theorem B3929735 : Blo 1032607 3929735 := bstep (se 1 (by rfl) ⟨2947301, by rfl⟩ : syracuseStep 3929735 = 5894603) B5894603
theorem B29849269 : Blo 1032607 29849269 := bstep (se 5 (by rfl) ⟨1399184, by rfl⟩ : syracuseStep 29849269 = 2798369) B2798369
theorem B2488171 : Blo 1032607 2488171 := bstep (se 1 (by rfl) ⟨1866128, by rfl⟩ : syracuseStep 2488171 = 3732257) B3732257
theorem B1963919 : Blo 1032607 1963919 := bstep (se 1 (by rfl) ⟨1472939, by rfl⟩ : syracuseStep 1963919 = 2945879) B2945879
theorem B2324411 : Blo 1032607 2324411 := bstep (se 1 (by rfl) ⟨1743308, by rfl⟩ : syracuseStep 2324411 = 3486617) B3486617
theorem B7469009 : Blo 1032607 7469009 := bstep (se 2 (by rfl) ⟨2800878, by rfl⟩ : syracuseStep 7469009 = 5601757) B5601757
theorem B1865747 : Blo 1032607 1865747 := bstep (se 1 (by rfl) ⟨1399310, by rfl⟩ : syracuseStep 1865747 = 2798621) B2798621
theorem B6912029 : Blo 1032607 6912029 := bstep (se 3 (by rfl) ⟨1296005, by rfl⟩ : syracuseStep 6912029 = 2592011) B2592011
theorem B2324537 : Blo 1032607 2324537 := bstep (se 2 (by rfl) ⟨871701, by rfl⟩ : syracuseStep 2324537 = 1743403) B1743403
theorem B2619449 : Blo 1032607 2619449 := bstep (se 2 (by rfl) ⟨982293, by rfl⟩ : syracuseStep 2619449 = 1964587) B1964587
theorem B3930191 : Blo 1032607 3930191 := bstep (se 1 (by rfl) ⟨2947643, by rfl⟩ : syracuseStep 3930191 = 5895287) B5895287
theorem B17692829 : Blo 1032607 17692829 := bstep (se 3 (by rfl) ⟨3317405, by rfl⟩ : syracuseStep 17692829 = 6634811) B6634811
theorem B8976541 : Blo 1032607 8976541 := bstep (se 3 (by rfl) ⟨1683101, by rfl⟩ : syracuseStep 8976541 = 3366203) B3366203
theorem B9926999 : Blo 1032607 9926999 := bstep (se 1 (by rfl) ⟨7445249, by rfl⟩ : syracuseStep 9926999 = 14890499) B14890499
theorem B2324879 : Blo 1032607 2324879 := bstep (se 1 (by rfl) ⟨1743659, by rfl⟩ : syracuseStep 2324879 = 3487319) B3487319
theorem B1309223 : Blo 1032607 1309223 := bstep (se 1 (by rfl) ⟨981917, by rfl⟩ : syracuseStep 1309223 = 1963835) B1963835
theorem B7862993 : Blo 1032607 7862993 := bstep (se 2 (by rfl) ⟨2948622, by rfl⟩ : syracuseStep 7862993 = 5897245) B5897245
theorem B2325203 : Blo 1032607 2325203 := bstep (se 1 (by rfl) ⟨1743902, by rfl⟩ : syracuseStep 2325203 = 3487805) B3487805
theorem B1243999 : Blo 1032607 1243999 := bstep (se 1 (by rfl) ⟨932999, by rfl⟩ : syracuseStep 1243999 = 1865999) B1865999
theorem B1309547 : Blo 1032607 1309547 := bstep (se 1 (by rfl) ⟨982160, by rfl⟩ : syracuseStep 1309547 = 1964321) B1964321
theorem B4488119 : Blo 1032607 4488119 := bstep (se 1 (by rfl) ⟨3366089, by rfl⟩ : syracuseStep 4488119 = 6732179) B6732179
theorem B2096135 : Blo 1032607 2096135 := bstep (se 1 (by rfl) ⟨1572101, by rfl⟩ : syracuseStep 2096135 = 3144203) B3144203
theorem B2489363 : Blo 1032607 2489363 := bstep (se 1 (by rfl) ⟨1867022, by rfl⟩ : syracuseStep 2489363 = 3734045) B3734045
theorem B1866791 : Blo 1032607 1866791 := bstep (se 1 (by rfl) ⟨1400093, by rfl⟩ : syracuseStep 1866791 = 2800187) B2800187
theorem B3931193 : Blo 1032607 3931193 := bstep (se 2 (by rfl) ⟨1474197, by rfl⟩ : syracuseStep 3931193 = 2948395) B2948395
theorem B8387651 : Blo 1032607 8387651 := bstep (se 1 (by rfl) ⟨6290738, by rfl⟩ : syracuseStep 8387651 = 12581477) B12581477
theorem B2358443 : Blo 1032607 2358443 := bstep (se 1 (by rfl) ⟨1768832, by rfl⟩ : syracuseStep 2358443 = 3537665) B3537665
theorem B6618307 : Blo 1032607 6618307 := bstep (se 1 (by rfl) ⟨4963730, by rfl⟩ : syracuseStep 6618307 = 9927461) B9927461
theorem B2620937 : Blo 1032607 2620937 := bstep (se 2 (by rfl) ⟨982851, by rfl⟩ : syracuseStep 2620937 = 1965703) B1965703
theorem B2326139 : Blo 1032607 2326139 := bstep (se 1 (by rfl) ⟨1744604, by rfl⟩ : syracuseStep 2326139 = 3489209) B3489209
theorem B3931847 : Blo 1032607 3931847 := bstep (se 1 (by rfl) ⟨2948885, by rfl⟩ : syracuseStep 3931847 = 5897771) B5897771
theorem B1965779 : Blo 1032607 1965779 := bstep (se 1 (by rfl) ⟨1474334, by rfl⟩ : syracuseStep 1965779 = 2948669) B2948669
theorem B2326265 : Blo 1032607 2326265 := bstep (se 2 (by rfl) ⟨872349, by rfl⟩ : syracuseStep 2326265 = 1744699) B1744699
theorem B1867627 : Blo 1032607 1867627 := bstep (se 1 (by rfl) ⟨1400720, by rfl⟩ : syracuseStep 1867627 = 2801441) B2801441
theorem B1966007 : Blo 1032607 1966007 := bstep (se 1 (by rfl) ⟨1474505, by rfl⟩ : syracuseStep 1966007 = 2949011) B2949011
theorem B4423891 : Blo 1032607 4423891 := bstep (se 1 (by rfl) ⟨3317918, by rfl⟩ : syracuseStep 4423891 = 6635837) B6635837
theorem B2326895 : Blo 1032607 2326895 := bstep (se 1 (by rfl) ⟨1745171, by rfl⟩ : syracuseStep 2326895 = 3490343) B3490343
theorem B1966447 : Blo 1032607 1966447 := bstep (se 1 (by rfl) ⟨1474835, by rfl⟩ : syracuseStep 1966447 = 2949671) B2949671
theorem B4030895 : Blo 1032607 4030895 := bstep (se 1 (by rfl) ⟨3023171, by rfl⟩ : syracuseStep 4030895 = 6046343) B6046343
theorem B2326967 : Blo 1032607 2326967 := bstep (se 1 (by rfl) ⟨1745225, by rfl⟩ : syracuseStep 2326967 = 3490451) B3490451
theorem B2621879 : Blo 1032607 2621879 := bstep (se 1 (by rfl) ⟨1966409, by rfl⟩ : syracuseStep 2621879 = 3932819) B3932819
theorem B2327111 : Blo 1032607 2327111 := bstep (se 1 (by rfl) ⟨1745333, by rfl⟩ : syracuseStep 2327111 = 3490667) B3490667
theorem B2327147 : Blo 1032607 2327147 := bstep (se 1 (by rfl) ⟨1745360, by rfl⟩ : syracuseStep 2327147 = 3490721) B3490721
theorem B3539609 : Blo 1032607 3539609 := bstep (se 2 (by rfl) ⟨1327353, by rfl⟩ : syracuseStep 3539609 = 2654707) B2654707
theorem B8848055 : Blo 1032607 8848055 := bstep (se 1 (by rfl) ⟨6636041, by rfl⟩ : syracuseStep 8848055 = 13272083) B13272083
theorem B5243615 : Blo 1032607 5243615 := bstep (se 1 (by rfl) ⟨3932711, by rfl⟩ : syracuseStep 5243615 = 7865423) B7865423
theorem B1311643 : Blo 1032607 1311643 := bstep (se 1 (by rfl) ⟨983732, by rfl⟩ : syracuseStep 1311643 = 1967465) B1967465
theorem B2327543 : Blo 1032607 2327543 := bstep (se 1 (by rfl) ⟨1745657, by rfl⟩ : syracuseStep 2327543 = 3491315) B3491315
theorem B22348817 : Blo 1032607 22348817 := bstep (se 2 (by rfl) ⟨8380806, by rfl⟩ : syracuseStep 22348817 = 16761613) B16761613
theorem B2655355 : Blo 1032607 2655355 := bstep (se 1 (by rfl) ⟨1991516, by rfl⟩ : syracuseStep 2655355 = 3983033) B3983033
theorem B3146951 : Blo 1032607 3146951 := bstep (se 1 (by rfl) ⟨2360213, by rfl⟩ : syracuseStep 3146951 = 4720427) B4720427
theorem B11928809 : Blo 1032607 11928809 := bstep (se 2 (by rfl) ⟨4473303, by rfl⟩ : syracuseStep 11928809 = 8946607) B8946607
theorem B2327903 : Blo 1032607 2327903 := bstep (se 1 (by rfl) ⟨1745927, by rfl⟩ : syracuseStep 2327903 = 3491855) B3491855
theorem B4425121 : Blo 1032607 4425121 := bstep (se 2 (by rfl) ⟨1659420, by rfl⟩ : syracuseStep 4425121 = 3318841) B3318841
theorem B2622881 : Blo 1032607 2622881 := bstep (se 2 (by rfl) ⟨983580, by rfl⟩ : syracuseStep 2622881 = 1967161) B1967161
theorem B2360927 : Blo 1032607 2360927 := bstep (se 1 (by rfl) ⟨1770695, by rfl⟩ : syracuseStep 2360927 = 3541391) B3541391
theorem B2328299 : Blo 1032607 2328299 := bstep (se 1 (by rfl) ⟨1746224, by rfl⟩ : syracuseStep 2328299 = 3492449) B3492449
theorem B2328425 : Blo 1032607 2328425 := bstep (se 2 (by rfl) ⟨873159, by rfl⟩ : syracuseStep 2328425 = 1746319) B1746319
theorem B2623337 : Blo 1032607 2623337 := bstep (se 2 (by rfl) ⟨983751, by rfl⟩ : syracuseStep 2623337 = 1967503) B1967503
theorem B5900687 : Blo 1032607 5900687 := bstep (se 1 (by rfl) ⟨4425515, by rfl⟩ : syracuseStep 5900687 = 8851031) B8851031
theorem B2329271 : Blo 1032607 2329271 := bstep (se 1 (by rfl) ⟨1746953, by rfl⟩ : syracuseStep 2329271 = 3493907) B3493907
theorem B2329487 : Blo 1032607 2329487 := bstep (se 1 (by rfl) ⟨1747115, by rfl⟩ : syracuseStep 2329487 = 3494231) B3494231
theorem B5245883 : Blo 1032607 5245883 := bstep (se 1 (by rfl) ⟨3934412, by rfl⟩ : syracuseStep 5245883 = 7868825) B7868825
theorem B12586049 : Blo 1032607 12586049 := bstep (se 2 (by rfl) ⟨4719768, by rfl⟩ : syracuseStep 12586049 = 9439537) B9439537
theorem B1150331 : Blo 1032607 1150331 := bstep (se 1 (by rfl) ⟨862748, by rfl⟩ : syracuseStep 1150331 = 1725497) B1725497
theorem B5311873 : Blo 1032607 5311873 := bstep (se 2 (by rfl) ⟨1991952, by rfl⟩ : syracuseStep 5311873 = 3983905) B3983905
theorem B4427207 : Blo 1032607 4427207 := bstep (se 1 (by rfl) ⟨3320405, by rfl⟩ : syracuseStep 4427207 = 6640811) B6640811
theorem B2330207 : Blo 1032607 2330207 := bstep (se 1 (by rfl) ⟨1747655, by rfl⟩ : syracuseStep 2330207 = 3495311) B3495311
theorem B9572039 : Blo 1032607 9572039 := bstep (se 1 (by rfl) ⟨7179029, by rfl⟩ : syracuseStep 9572039 = 14358059) B14358059
theorem B13242149 : Blo 1032607 13242149 := bstep (se 4 (by rfl) ⟨1241451, by rfl⟩ : syracuseStep 13242149 = 2482903) B2482903
theorem B4427567 : Blo 1032607 4427567 := bstep (se 1 (by rfl) ⟨3320675, by rfl⟩ : syracuseStep 4427567 = 6641351) B6641351
theorem B2330423 : Blo 1032607 2330423 := bstep (se 1 (by rfl) ⟨1747817, by rfl⟩ : syracuseStep 2330423 = 3495635) B3495635
theorem B2330729 : Blo 1032607 2330729 := bstep (se 2 (by rfl) ⟨874023, by rfl⟩ : syracuseStep 2330729 = 1748047) B1748047
theorem B5247179 : Blo 1032607 5247179 := bstep (se 1 (by rfl) ⟨3935384, by rfl⟩ : syracuseStep 5247179 = 7870769) B7870769
theorem B2331215 : Blo 1032607 2331215 := bstep (se 1 (by rfl) ⟨1748411, by rfl⟩ : syracuseStep 2331215 = 3496823) B3496823
theorem B2331359 : Blo 1032607 2331359 := bstep (se 1 (by rfl) ⟨1748519, by rfl⟩ : syracuseStep 2331359 = 3497039) B3497039
theorem B57480101 : Blo 1032607 57480101 := bstep (se 4 (by rfl) ⟨5388759, by rfl⟩ : syracuseStep 57480101 = 10777519) B10777519
theorem B2331611 : Blo 1032607 2331611 := bstep (se 1 (by rfl) ⟨1748708, by rfl⟩ : syracuseStep 2331611 = 3497417) B3497417
theorem B2659303 : Blo 1032607 2659303 := bstep (se 1 (by rfl) ⟨1994477, by rfl⟩ : syracuseStep 2659303 = 3988955) B3988955
theorem B5903351 : Blo 1032607 5903351 := bstep (se 1 (by rfl) ⟨4427513, by rfl⟩ : syracuseStep 5903351 = 8855027) B8855027
theorem B2331791 : Blo 1032607 2331791 := bstep (se 1 (by rfl) ⟨1748843, by rfl⟩ : syracuseStep 2331791 = 3497687) B3497687
theorem B2331881 : Blo 1032607 2331881 := bstep (se 2 (by rfl) ⟨874455, by rfl⟩ : syracuseStep 2331881 = 1748911) B1748911
theorem B9934073 : Blo 1032607 9934073 := bstep (se 2 (by rfl) ⟨3725277, by rfl⟩ : syracuseStep 9934073 = 7450555) B7450555
theorem B2331935 : Blo 1032607 2331935 := bstep (se 1 (by rfl) ⟨1748951, by rfl⟩ : syracuseStep 2331935 = 3497903) B3497903
theorem B7443751 : Blo 1032607 7443751 := bstep (se 1 (by rfl) ⟨5582813, by rfl⟩ : syracuseStep 7443751 = 11165627) B11165627
theorem B29824361 : Blo 1032607 29824361 := bstep (se 2 (by rfl) ⟨11184135, by rfl⟩ : syracuseStep 29824361 = 22368271) B22368271
theorem B20158085 : Blo 1032607 20158085 := bstep (se 4 (by rfl) ⟨1889820, by rfl⟩ : syracuseStep 20158085 = 3779641) B3779641
theorem B1742647 : Blo 1032607 1742647 := bstep (se 1 (by rfl) ⟨1306985, by rfl⟩ : syracuseStep 1742647 = 2613971) B2613971
theorem B1743113 : Blo 1032607 1743113 := bstep (se 2 (by rfl) ⟨653667, by rfl⟩ : syracuseStep 1743113 = 1307335) B1307335
theorem B6298523 : Blo 1032607 6298523 := bstep (se 1 (by rfl) ⟨4723892, by rfl⟩ : syracuseStep 6298523 = 9447785) B9447785
theorem B8821811 : Blo 1032607 8821811 := bstep (se 1 (by rfl) ⟨6616358, by rfl⟩ : syracuseStep 8821811 = 13232717) B13232717
theorem B1744105 : Blo 1032607 1744105 := bstep (se 2 (by rfl) ⟨654039, by rfl⟩ : syracuseStep 1744105 = 1308079) B1308079
theorem B1744159 : Blo 1032607 1744159 := bstep (se 1 (by rfl) ⟨1308119, by rfl⟩ : syracuseStep 1744159 = 2616239) B2616239
theorem B1744571 : Blo 1032607 1744571 := bstep (se 1 (by rfl) ⟨1308428, by rfl⟩ : syracuseStep 1744571 = 2616857) B2616857
theorem B3317561 : Blo 1032607 3317561 := bstep (se 2 (by rfl) ⟨1244085, by rfl⟩ : syracuseStep 3317561 = 2488171) B2488171
theorem B11968721 : Blo 1032607 11968721 := bstep (se 2 (by rfl) ⟨4488270, by rfl⟩ : syracuseStep 11968721 = 8976541) B8976541
theorem B1548983 : Blo 1032607 1548983 := bstep (se 1 (by rfl) ⟨1161737, by rfl⟩ : syracuseStep 1548983 = 2323475) B2323475
theorem B1549211 : Blo 1032607 1549211 := bstep (se 1 (by rfl) ⟨1161908, by rfl⟩ : syracuseStep 1549211 = 2323817) B2323817
theorem B7447555 : Blo 1032607 7447555 := bstep (se 1 (by rfl) ⟨5585666, by rfl⟩ : syracuseStep 7447555 = 11171333) B11171333
theorem B1549607 : Blo 1032607 1549607 := bstep (se 1 (by rfl) ⟨1162205, by rfl⟩ : syracuseStep 1549607 = 2324411) B2324411
theorem B1549691 : Blo 1032607 1549691 := bstep (se 1 (by rfl) ⟨1162268, by rfl⟩ : syracuseStep 1549691 = 2324537) B2324537
theorem B1746299 : Blo 1032607 1746299 := bstep (se 1 (by rfl) ⟨1309724, by rfl⟩ : syracuseStep 1746299 = 2619449) B2619449
theorem B1549817 : Blo 1032607 1549817 := bstep (se 2 (by rfl) ⟨581181, by rfl⟩ : syracuseStep 1549817 = 1162363) B1162363
theorem B8824409 : Blo 1032607 8824409 := bstep (se 2 (by rfl) ⟨3309153, by rfl⟩ : syracuseStep 8824409 = 6618307) B6618307
theorem B1549919 : Blo 1032607 1549919 := bstep (se 1 (by rfl) ⟨1162439, by rfl⟩ : syracuseStep 1549919 = 2324879) B2324879
theorem B14362247 : Blo 1032607 14362247 := bstep (se 1 (by rfl) ⟨10771685, by rfl⟩ : syracuseStep 14362247 = 21543371) B21543371
theorem B1550135 : Blo 1032607 1550135 := bstep (se 1 (by rfl) ⟨1162601, by rfl⟩ : syracuseStep 1550135 = 2325203) B2325203
theorem B2992079 : Blo 1032607 2992079 := bstep (se 1 (by rfl) ⟨2244059, by rfl⟩ : syracuseStep 2992079 = 4488119) B4488119
theorem B3975149 : Blo 1032607 3975149 := bstep (se 3 (by rfl) ⟨745340, by rfl⟩ : syracuseStep 3975149 = 1490681) B1490681
theorem B1550441 : Blo 1032607 1550441 := bstep (se 2 (by rfl) ⟨581415, by rfl⟩ : syracuseStep 1550441 = 1162831) B1162831
theorem B1747291 : Blo 1032607 1747291 := bstep (se 1 (by rfl) ⟨1310468, by rfl⟩ : syracuseStep 1747291 = 2620937) B2620937
theorem B1550759 : Blo 1032607 1550759 := bstep (se 1 (by rfl) ⟨1163069, by rfl⟩ : syracuseStep 1550759 = 2326139) B2326139
theorem B1550843 : Blo 1032607 1550843 := bstep (se 1 (by rfl) ⟨1163132, by rfl⟩ : syracuseStep 1550843 = 2326265) B2326265
theorem B1550969 : Blo 1032607 1550969 := bstep (se 2 (by rfl) ⟨581613, by rfl⟩ : syracuseStep 1550969 = 1163227) B1163227
theorem B1551023 : Blo 1032607 1551023 := bstep (se 1 (by rfl) ⟨1163267, by rfl⟩ : syracuseStep 1551023 = 2326535) B2326535
theorem B1551071 : Blo 1032607 1551071 := bstep (se 1 (by rfl) ⟨1163303, by rfl⟩ : syracuseStep 1551071 = 2326607) B2326607
theorem B1551335 : Blo 1032607 1551335 := bstep (se 1 (by rfl) ⟨1163501, by rfl⟩ : syracuseStep 1551335 = 2327003) B2327003
theorem B1551593 : Blo 1032607 1551593 := bstep (se 2 (by rfl) ⟨581847, by rfl⟩ : syracuseStep 1551593 = 1163695) B1163695
theorem B1551647 : Blo 1032607 1551647 := bstep (se 1 (by rfl) ⟨1163735, by rfl⟩ : syracuseStep 1551647 = 2327471) B2327471
theorem B1748263 : Blo 1032607 1748263 := bstep (se 1 (by rfl) ⟨1311197, by rfl⟩ : syracuseStep 1748263 = 2622395) B2622395
theorem B2796923 : Blo 1032607 2796923 := bstep (se 1 (by rfl) ⟨2097692, by rfl⟩ : syracuseStep 2796923 = 4195385) B4195385
theorem B1551815 : Blo 1032607 1551815 := bstep (se 1 (by rfl) ⟨1163861, by rfl⟩ : syracuseStep 1551815 = 2327723) B2327723
theorem B3485267 : Blo 1032607 3485267 := bstep (se 1 (by rfl) ⟨2613950, by rfl⟩ : syracuseStep 3485267 = 5227901) B5227901
theorem B6631121 : Blo 1032607 6631121 := bstep (se 2 (by rfl) ⟨2486670, by rfl⟩ : syracuseStep 6631121 = 4973341) B4973341
theorem B1552169 : Blo 1032607 1552169 := bstep (se 2 (by rfl) ⟨582063, by rfl⟩ : syracuseStep 1552169 = 1164127) B1164127
theorem B1552175 : Blo 1032607 1552175 := bstep (se 1 (by rfl) ⟨1164131, by rfl⟩ : syracuseStep 1552175 = 2328263) B2328263
theorem B1748783 : Blo 1032607 1748783 := bstep (se 1 (by rfl) ⟨1311587, by rfl⟩ : syracuseStep 1748783 = 2623175) B2623175
theorem B4370537 : Blo 1032607 4370537 := bstep (se 2 (by rfl) ⟨1638951, by rfl⟩ : syracuseStep 4370537 = 3277903) B3277903
theorem B1552649 : Blo 1032607 1552649 := bstep (se 2 (by rfl) ⟨582243, by rfl⟩ : syracuseStep 1552649 = 1164487) B1164487
theorem B1552751 : Blo 1032607 1552751 := bstep (se 1 (by rfl) ⟨1164563, by rfl⟩ : syracuseStep 1552751 = 2329127) B2329127
theorem B1552967 : Blo 1032607 1552967 := bstep (se 1 (by rfl) ⟨1164725, by rfl⟩ : syracuseStep 1552967 = 2329451) B2329451
theorem B1553003 : Blo 1032607 1553003 := bstep (se 1 (by rfl) ⟨1164752, by rfl⟩ : syracuseStep 1553003 = 2329505) B2329505
theorem B43037381 : Blo 1032607 43037381 := bstep (se 4 (by rfl) ⟨4034754, by rfl⟩ : syracuseStep 43037381 = 8069509) B8069509
theorem B2798327 : Blo 1032607 2798327 := bstep (se 1 (by rfl) ⟨2098745, by rfl⟩ : syracuseStep 2798327 = 4197491) B4197491
theorem B1553231 : Blo 1032607 1553231 := bstep (se 1 (by rfl) ⟨1164923, by rfl⟩ : syracuseStep 1553231 = 2329847) B2329847
theorem B2208683 : Blo 1032607 2208683 := bstep (se 1 (by rfl) ⟨1656512, by rfl⟩ : syracuseStep 2208683 = 3313025) B3313025
theorem B7845011 : Blo 1032607 7845011 := bstep (se 1 (by rfl) ⟨5883758, by rfl⟩ : syracuseStep 7845011 = 11767517) B11767517
theorem B1553627 : Blo 1032607 1553627 := bstep (se 1 (by rfl) ⟨1165220, by rfl⟩ : syracuseStep 1553627 = 2330441) B2330441
theorem B7451999 : Blo 1032607 7451999 := bstep (se 1 (by rfl) ⟨5588999, by rfl⟩ : syracuseStep 7451999 = 11177999) B11177999
theorem B1553801 : Blo 1032607 1553801 := bstep (se 2 (by rfl) ⟨582675, by rfl⟩ : syracuseStep 1553801 = 1165351) B1165351
theorem B1554155 : Blo 1032607 1554155 := bstep (se 1 (by rfl) ⟨1165616, by rfl⟩ : syracuseStep 1554155 = 2331233) B2331233
theorem B1554383 : Blo 1032607 1554383 := bstep (se 1 (by rfl) ⟨1165787, by rfl⟩ : syracuseStep 1554383 = 2331575) B2331575
theorem B9943073 : Blo 1032607 9943073 := bstep (se 2 (by rfl) ⟨3728652, by rfl⟩ : syracuseStep 9943073 = 7457305) B7457305
theorem B1554779 : Blo 1032607 1554779 := bstep (se 1 (by rfl) ⟨1166084, by rfl⟩ : syracuseStep 1554779 = 2332169) B2332169
theorem B3488183 : Blo 1032607 3488183 := bstep (se 1 (by rfl) ⟨2616137, by rfl⟩ : syracuseStep 3488183 = 5232275) B5232275
theorem B2210323 : Blo 1032607 2210323 := bstep (se 1 (by rfl) ⟨1657742, by rfl⟩ : syracuseStep 2210323 = 3315485) B3315485
theorem B1161823 : Blo 1032607 1161823 := bstep (se 1 (by rfl) ⟨871367, by rfl⟩ : syracuseStep 1161823 = 1742735) B1742735
theorem B2210579 : Blo 1032607 2210579 := bstep (se 1 (by rfl) ⟨1657934, by rfl⟩ : syracuseStep 2210579 = 3315869) B3315869
theorem B2800403 : Blo 1032607 2800403 := bstep (se 1 (by rfl) ⟨2100302, by rfl⟩ : syracuseStep 2800403 = 4200605) B4200605
theorem B3357683 : Blo 1032607 3357683 := bstep (se 1 (by rfl) ⟨2518262, by rfl⟩ : syracuseStep 3357683 = 5036525) B5036525
theorem B17710325 : Blo 1032607 17710325 := bstep (se 5 (by rfl) ⟨830171, by rfl⟩ : syracuseStep 17710325 = 1660343) B1660343
theorem B5586515 : Blo 1032607 5586515 := bstep (se 1 (by rfl) ⟨4189886, by rfl⟩ : syracuseStep 5586515 = 8379773) B8379773
theorem B8830559 : Blo 1032607 8830559 := bstep (se 1 (by rfl) ⟨6622919, by rfl⟩ : syracuseStep 8830559 = 13245839) B13245839
theorem B1162975 : Blo 1032607 1162975 := bstep (se 1 (by rfl) ⟨872231, by rfl⟩ : syracuseStep 1162975 = 1744463) B1744463
theorem B3358511 : Blo 1032607 3358511 := bstep (se 1 (by rfl) ⟨2518883, by rfl⟩ : syracuseStep 3358511 = 5037767) B5037767
theorem B1163551 : Blo 1032607 1163551 := bstep (se 1 (by rfl) ⟨872663, by rfl⟩ : syracuseStep 1163551 = 1745327) B1745327
theorem B1032615 : Blo 1032607 1032615 := bstep (se 1 (by rfl) ⟨774461, by rfl⟩ : syracuseStep 1032615 = 1548923) B1548923
theorem B1032699 : Blo 1032607 1032699 := bstep (se 1 (by rfl) ⟨774524, by rfl⟩ : syracuseStep 1032699 = 1549049) B1549049
theorem B1032767 : Blo 1032607 1032767 := bstep (se 1 (by rfl) ⟨774575, by rfl⟩ : syracuseStep 1032767 = 1549151) B1549151
theorem B1163839 : Blo 1032607 1163839 := bstep (se 1 (by rfl) ⟨872879, by rfl⟩ : syracuseStep 1163839 = 1745759) B1745759
theorem B1032775 : Blo 1032607 1032775 := bstep (se 1 (by rfl) ⟨774581, by rfl⟩ : syracuseStep 1032775 = 1549163) B1549163
theorem B3785287 : Blo 1032607 3785287 := bstep (se 1 (by rfl) ⟨2838965, by rfl⟩ : syracuseStep 3785287 = 5677931) B5677931
theorem B1655417 : Blo 1032607 1655417 := bstep (se 2 (by rfl) ⟨620781, by rfl⟩ : syracuseStep 1655417 = 1241563) B1241563
theorem B1032927 : Blo 1032607 1032927 := bstep (se 1 (by rfl) ⟨774695, by rfl⟩ : syracuseStep 1032927 = 1549391) B1549391
theorem B1033007 : Blo 1032607 1033007 := bstep (se 1 (by rfl) ⟨774755, by rfl⟩ : syracuseStep 1033007 = 1549511) B1549511
theorem B1033115 : Blo 1032607 1033115 := bstep (se 1 (by rfl) ⟨774836, by rfl⟩ : syracuseStep 1033115 = 1549673) B1549673
theorem B7848899 : Blo 1032607 7848899 := bstep (se 1 (by rfl) ⟨5886674, by rfl⟩ : syracuseStep 7848899 = 11773349) B11773349
theorem B1033167 : Blo 1032607 1033167 := bstep (se 1 (by rfl) ⟨774875, by rfl⟩ : syracuseStep 1033167 = 1549751) B1549751
theorem B1033191 : Blo 1032607 1033191 := bstep (se 1 (by rfl) ⟨774893, by rfl⟩ : syracuseStep 1033191 = 1549787) B1549787
theorem B5227577 : Blo 1032607 5227577 := bstep (se 2 (by rfl) ⟨1960341, by rfl⟩ : syracuseStep 5227577 = 3920683) B3920683
theorem B8832199 : Blo 1032607 8832199 := bstep (se 1 (by rfl) ⟨6624149, by rfl⟩ : syracuseStep 8832199 = 13248299) B13248299
theorem B10601705 : Blo 1032607 10601705 := bstep (se 2 (by rfl) ⟨3975639, by rfl⟩ : syracuseStep 10601705 = 7951279) B7951279
theorem B1033503 : Blo 1032607 1033503 := bstep (se 1 (by rfl) ⟨775127, by rfl⟩ : syracuseStep 1033503 = 1550255) B1550255
theorem B1033563 : Blo 1032607 1033563 := bstep (se 1 (by rfl) ⟨775172, by rfl⟩ : syracuseStep 1033563 = 1550345) B1550345
theorem B4244831 : Blo 1032607 4244831 := bstep (se 1 (by rfl) ⟨3183623, by rfl⟩ : syracuseStep 4244831 = 6367247) B6367247
theorem B1033583 : Blo 1032607 1033583 := bstep (se 1 (by rfl) ⟨775187, by rfl⟩ : syracuseStep 1033583 = 1550375) B1550375
theorem B1164667 : Blo 1032607 1164667 := bstep (se 1 (by rfl) ⟨873500, by rfl⟩ : syracuseStep 1164667 = 1747001) B1747001
theorem B1033639 : Blo 1032607 1033639 := bstep (se 1 (by rfl) ⟨775229, by rfl⟩ : syracuseStep 1033639 = 1550459) B1550459
theorem B3491261 : Blo 1032607 3491261 := bstep (se 3 (by rfl) ⟨654611, by rfl⟩ : syracuseStep 3491261 = 1309223) B1309223
theorem B1033723 : Blo 1032607 1033723 := bstep (se 1 (by rfl) ⟨775292, by rfl⟩ : syracuseStep 1033723 = 1550585) B1550585
theorem B12568097 : Blo 1032607 12568097 := bstep (se 2 (by rfl) ⟨4713036, by rfl⟩ : syracuseStep 12568097 = 9426073) B9426073
theorem B1033791 : Blo 1032607 1033791 := bstep (se 1 (by rfl) ⟨775343, by rfl⟩ : syracuseStep 1033791 = 1550687) B1550687
theorem B1033799 : Blo 1032607 1033799 := bstep (se 1 (by rfl) ⟨775349, by rfl⟩ : syracuseStep 1033799 = 1550699) B1550699
theorem B1033951 : Blo 1032607 1033951 := bstep (se 1 (by rfl) ⟨775463, by rfl⟩ : syracuseStep 1033951 = 1550927) B1550927
theorem B1034031 : Blo 1032607 1034031 := bstep (se 1 (by rfl) ⟨775523, by rfl⟩ : syracuseStep 1034031 = 1551047) B1551047
theorem B3491639 : Blo 1032607 3491639 := bstep (se 1 (by rfl) ⟨2618729, by rfl⟩ : syracuseStep 3491639 = 5237459) B5237459
theorem B2213689 : Blo 1032607 2213689 := bstep (se 2 (by rfl) ⟨830133, by rfl⟩ : syracuseStep 2213689 = 1660267) B1660267
theorem B1165135 : Blo 1032607 1165135 := bstep (se 1 (by rfl) ⟨873851, by rfl⟩ : syracuseStep 1165135 = 1747703) B1747703
theorem B1034139 : Blo 1032607 1034139 := bstep (se 1 (by rfl) ⟨775604, by rfl⟩ : syracuseStep 1034139 = 1551209) B1551209
theorem B1034191 : Blo 1032607 1034191 := bstep (se 1 (by rfl) ⟨775643, by rfl⟩ : syracuseStep 1034191 = 1551287) B1551287
theorem B1034215 : Blo 1032607 1034215 := bstep (se 1 (by rfl) ⟨775661, by rfl⟩ : syracuseStep 1034215 = 1551323) B1551323
theorem B1165531 : Blo 1032607 1165531 := bstep (se 1 (by rfl) ⟨874148, by rfl⟩ : syracuseStep 1165531 = 1748297) B1748297
theorem B39799025 : Blo 1032607 39799025 := bstep (se 2 (by rfl) ⟨14924634, by rfl⟩ : syracuseStep 39799025 = 29849269) B29849269
theorem B3492125 : Blo 1032607 3492125 := bstep (se 3 (by rfl) ⟨654773, by rfl⟩ : syracuseStep 3492125 = 1309547) B1309547
theorem B1034527 : Blo 1032607 1034527 := bstep (se 1 (by rfl) ⟨775895, by rfl⟩ : syracuseStep 1034527 = 1551791) B1551791
theorem B1034587 : Blo 1032607 1034587 := bstep (se 1 (by rfl) ⟨775940, by rfl⟩ : syracuseStep 1034587 = 1551881) B1551881
theorem B1034607 : Blo 1032607 1034607 := bstep (se 1 (by rfl) ⟨775955, by rfl⟩ : syracuseStep 1034607 = 1551911) B1551911
theorem B1034663 : Blo 1032607 1034663 := bstep (se 1 (by rfl) ⟨775997, by rfl⟩ : syracuseStep 1034663 = 1551995) B1551995
theorem B1034747 : Blo 1032607 1034747 := bstep (se 1 (by rfl) ⟨776060, by rfl⟩ : syracuseStep 1034747 = 1552121) B1552121
theorem B1165819 : Blo 1032607 1165819 := bstep (se 1 (by rfl) ⟨874364, by rfl⟩ : syracuseStep 1165819 = 1748729) B1748729
theorem B1034815 : Blo 1032607 1034815 := bstep (se 1 (by rfl) ⟨776111, by rfl⟩ : syracuseStep 1034815 = 1552223) B1552223
theorem B1034823 : Blo 1032607 1034823 := bstep (se 1 (by rfl) ⟨776117, by rfl⟩ : syracuseStep 1034823 = 1552235) B1552235
theorem B1165999 : Blo 1032607 1165999 := bstep (se 1 (by rfl) ⟨874499, by rfl⟩ : syracuseStep 1165999 = 1748999) B1748999
theorem B1034975 : Blo 1032607 1034975 := bstep (se 1 (by rfl) ⟨776231, by rfl⟩ : syracuseStep 1034975 = 1552463) B1552463
theorem B1035055 : Blo 1032607 1035055 := bstep (se 1 (by rfl) ⟨776291, by rfl⟩ : syracuseStep 1035055 = 1552583) B1552583
theorem B1035163 : Blo 1032607 1035163 := bstep (se 1 (by rfl) ⟨776372, by rfl⟩ : syracuseStep 1035163 = 1552745) B1552745
theorem B1035215 : Blo 1032607 1035215 := bstep (se 1 (by rfl) ⟨776411, by rfl⟩ : syracuseStep 1035215 = 1552823) B1552823
theorem B1035239 : Blo 1032607 1035239 := bstep (se 1 (by rfl) ⟨776429, by rfl⟩ : syracuseStep 1035239 = 1552859) B1552859
theorem B5229683 : Blo 1032607 5229683 := bstep (se 1 (by rfl) ⟨3922262, by rfl⟩ : syracuseStep 5229683 = 7844525) B7844525
theorem B1657999 : Blo 1032607 1657999 := bstep (se 1 (by rfl) ⟨1243499, by rfl⟩ : syracuseStep 1657999 = 2486999) B2486999
theorem B14175503 : Blo 1032607 14175503 := bstep (se 1 (by rfl) ⟨10631627, by rfl⟩ : syracuseStep 14175503 = 21263255) B21263255
theorem B3493151 : Blo 1032607 3493151 := bstep (se 1 (by rfl) ⟨2619863, by rfl⟩ : syracuseStep 3493151 = 5239727) B5239727
theorem B1035551 : Blo 1032607 1035551 := bstep (se 1 (by rfl) ⟨776663, by rfl⟩ : syracuseStep 1035551 = 1553327) B1553327
theorem B1035611 : Blo 1032607 1035611 := bstep (se 1 (by rfl) ⟨776708, by rfl⟩ : syracuseStep 1035611 = 1553417) B1553417
theorem B1035631 : Blo 1032607 1035631 := bstep (se 1 (by rfl) ⟨776723, by rfl⟩ : syracuseStep 1035631 = 1553447) B1553447
theorem B1035687 : Blo 1032607 1035687 := bstep (se 1 (by rfl) ⟨776765, by rfl⟩ : syracuseStep 1035687 = 1553531) B1553531
theorem B1035771 : Blo 1032607 1035771 := bstep (se 1 (by rfl) ⟨776828, by rfl⟩ : syracuseStep 1035771 = 1553657) B1553657
theorem B1035839 : Blo 1032607 1035839 := bstep (se 1 (by rfl) ⟨776879, by rfl⟩ : syracuseStep 1035839 = 1553759) B1553759
theorem B1035847 : Blo 1032607 1035847 := bstep (se 1 (by rfl) ⟨776885, by rfl⟩ : syracuseStep 1035847 = 1553771) B1553771
theorem B1035999 : Blo 1032607 1035999 := bstep (se 1 (by rfl) ⟨776999, by rfl⟩ : syracuseStep 1035999 = 1553999) B1553999
theorem B1658665 : Blo 1032607 1658665 := bstep (se 2 (by rfl) ⟨621999, by rfl⟩ : syracuseStep 1658665 = 1243999) B1243999
theorem B1036079 : Blo 1032607 1036079 := bstep (se 1 (by rfl) ⟨777059, by rfl⟩ : syracuseStep 1036079 = 1554119) B1554119
theorem B1036187 : Blo 1032607 1036187 := bstep (se 1 (by rfl) ⟨777140, by rfl⟩ : syracuseStep 1036187 = 1554281) B1554281
theorem B5230493 : Blo 1032607 5230493 := bstep (se 3 (by rfl) ⟨980717, by rfl⟩ : syracuseStep 5230493 = 1961435) B1961435
theorem B1036239 : Blo 1032607 1036239 := bstep (se 1 (by rfl) ⟨777179, by rfl⟩ : syracuseStep 1036239 = 1554359) B1554359
theorem B1036263 : Blo 1032607 1036263 := bstep (se 1 (by rfl) ⟨777197, by rfl⟩ : syracuseStep 1036263 = 1554395) B1554395
theorem B4608019 : Blo 1032607 4608019 := bstep (se 1 (by rfl) ⟨3456014, by rfl⟩ : syracuseStep 4608019 = 6912029) B6912029
theorem B4968499 : Blo 1032607 4968499 := bstep (se 1 (by rfl) ⟨3726374, by rfl⟩ : syracuseStep 4968499 = 7452749) B7452749
theorem B8376425 : Blo 1032607 8376425 := bstep (se 2 (by rfl) ⟨3141159, by rfl⟩ : syracuseStep 8376425 = 6282319) B6282319
theorem B1036575 : Blo 1032607 1036575 := bstep (se 1 (by rfl) ⟨777431, by rfl⟩ : syracuseStep 1036575 = 1554863) B1554863
theorem B11194861 : Blo 1032607 11194861 := bstep (se 3 (by rfl) ⟨2099036, by rfl⟩ : syracuseStep 11194861 = 4198073) B4198073
theorem B1397423 : Blo 1032607 1397423 := bstep (se 1 (by rfl) ⟨1048067, by rfl⟩ : syracuseStep 1397423 = 2096135) B2096135
theorem B1659575 : Blo 1032607 1659575 := bstep (se 1 (by rfl) ⟨1244681, by rfl⟩ : syracuseStep 1659575 = 2489363) B2489363
theorem B5231303 : Blo 1032607 5231303 := bstep (se 1 (by rfl) ⟨3923477, by rfl⟩ : syracuseStep 5231303 = 7846955) B7846955
theorem B5591767 : Blo 1032607 5591767 := bstep (se 1 (by rfl) ⟨4193825, by rfl⟩ : syracuseStep 5591767 = 8387651) B8387651
theorem B59757587 : Blo 1032607 59757587 := bstep (se 1 (by rfl) ⟨44818190, by rfl⟩ : syracuseStep 59757587 = 89636381) B89636381
theorem B9950759 : Blo 1032607 9950759 := bstep (se 1 (by rfl) ⟨7463069, by rfl⟩ : syracuseStep 9950759 = 14926139) B14926139
theorem B3495581 : Blo 1032607 3495581 := bstep (se 3 (by rfl) ⟨655421, by rfl⟩ : syracuseStep 3495581 = 1310843) B1310843
theorem B3496121 : Blo 1032607 3496121 := bstep (se 2 (by rfl) ⟨1311045, by rfl⟩ : syracuseStep 3496121 = 2622091) B2622091
theorem B1104239 : Blo 1032607 1104239 := bstep (se 1 (by rfl) ⟨828179, by rfl⟩ : syracuseStep 1104239 = 1656359) B1656359
theorem B7854731 : Blo 1032607 7854731 := bstep (se 1 (by rfl) ⟨5891048, by rfl⟩ : syracuseStep 7854731 = 11782097) B11782097
theorem B3922627 : Blo 1032607 3922627 := bstep (se 1 (by rfl) ⟨2941970, by rfl⟩ : syracuseStep 3922627 = 5883941) B5883941
theorem B5659579 : Blo 1032607 5659579 := bstep (se 1 (by rfl) ⟨4244684, by rfl⟩ : syracuseStep 5659579 = 8489369) B8489369
theorem B3922931 : Blo 1032607 3922931 := bstep (se 1 (by rfl) ⟨2942198, by rfl⟩ : syracuseStep 3922931 = 5884397) B5884397
theorem B5234057 : Blo 1032607 5234057 := bstep (se 2 (by rfl) ⟨1962771, by rfl⟩ : syracuseStep 5234057 = 3925543) B3925543
theorem B5299643 : Blo 1032607 5299643 := bstep (se 1 (by rfl) ⟨3974732, by rfl⟩ : syracuseStep 5299643 = 7949465) B7949465
theorem B3923387 : Blo 1032607 3923387 := bstep (se 1 (by rfl) ⟨2942540, by rfl⟩ : syracuseStep 3923387 = 5885081) B5885081
theorem B19914275 : Blo 1032607 19914275 := bstep (se 1 (by rfl) ⟨14935706, by rfl⟩ : syracuseStep 19914275 = 29871413) B29871413
theorem B42426017 : Blo 1032607 42426017 := bstep (se 2 (by rfl) ⟨15909756, by rfl⟩ : syracuseStep 42426017 = 31819513) B31819513
theorem B3497633 : Blo 1032607 3497633 := bstep (se 2 (by rfl) ⟨1311612, by rfl⟩ : syracuseStep 3497633 = 2623225) B2623225
theorem B76472045 : Blo 1032607 76472045 := bstep (se 3 (by rfl) ⟨14338508, by rfl⟩ : syracuseStep 76472045 = 28677017) B28677017
theorem B42983297 : Blo 1032607 42983297 := bstep (se 2 (by rfl) ⟨16118736, by rfl⟩ : syracuseStep 42983297 = 32237473) B32237473
theorem B2482127 : Blo 1032607 2482127 := bstep (se 1 (by rfl) ⟨1861595, by rfl⟩ : syracuseStep 2482127 = 3723191) B3723191
theorem B11165797 : Blo 1032607 11165797 := bstep (se 4 (by rfl) ⟨1046793, by rfl⟩ : syracuseStep 11165797 = 2093587) B2093587
theorem B3727873 : Blo 1032607 3727873 := bstep (se 2 (by rfl) ⟨1397952, by rfl⟩ : syracuseStep 3727873 = 2795905) B2795905
theorem B3498497 : Blo 1032607 3498497 := bstep (se 2 (by rfl) ⟨1311936, by rfl⟩ : syracuseStep 3498497 = 2623873) B2623873
theorem B5235353 : Blo 1032607 5235353 := bstep (se 2 (by rfl) ⟨1963257, by rfl⟩ : syracuseStep 5235353 = 3926515) B3926515
theorem B5596393 : Blo 1032607 5596393 := bstep (se 2 (by rfl) ⟨2098647, by rfl⟩ : syracuseStep 5596393 = 4197295) B4197295
theorem B6055145 : Blo 1032607 6055145 := bstep (se 2 (by rfl) ⟨2270679, by rfl⟩ : syracuseStep 6055145 = 4541359) B4541359
theorem B3729083 : Blo 1032607 3729083 := bstep (se 1 (by rfl) ⟨2796812, by rfl⟩ : syracuseStep 3729083 = 5593625) B5593625
theorem B3925847 : Blo 1032607 3925847 := bstep (se 1 (by rfl) ⟨2944385, by rfl⟩ : syracuseStep 3925847 = 5888771) B5888771
theorem B3729257 : Blo 1032607 3729257 := bstep (se 2 (by rfl) ⟨1398471, by rfl⟩ : syracuseStep 3729257 = 2796943) B2796943
theorem B2615561 : Blo 1032607 2615561 := bstep (se 2 (by rfl) ⟨980835, by rfl⟩ : syracuseStep 2615561 = 1961671) B1961671
theorem B2484587 : Blo 1032607 2484587 := bstep (se 1 (by rfl) ⟨1863440, by rfl⟩ : syracuseStep 2484587 = 3726881) B3726881
theorem B3729775 : Blo 1032607 3729775 := bstep (se 1 (by rfl) ⟨2797331, by rfl⟩ : syracuseStep 3729775 = 5594663) B5594663
theorem B5237135 : Blo 1032607 5237135 := bstep (se 1 (by rfl) ⟨3927851, by rfl⟩ : syracuseStep 5237135 = 7855703) B7855703
theorem B4975015 : Blo 1032607 4975015 := bstep (se 1 (by rfl) ⟨3731261, by rfl⟩ : syracuseStep 4975015 = 7462523) B7462523
theorem B16804361 : Blo 1032607 16804361 := bstep (se 2 (by rfl) ⟨6301635, by rfl⟩ : syracuseStep 16804361 = 12603271) B12603271
theorem B2615915 : Blo 1032607 2615915 := bstep (se 1 (by rfl) ⟨1961936, by rfl⟩ : syracuseStep 2615915 = 3923873) B3923873
theorem B4418459 : Blo 1032607 4418459 := bstep (se 1 (by rfl) ⟨3313844, by rfl⟩ : syracuseStep 4418459 = 6627689) B6627689
theorem B4975631 : Blo 1032607 4975631 := bstep (se 1 (by rfl) ⟨3731723, by rfl⟩ : syracuseStep 4975631 = 7463447) B7463447
theorem B5303335 : Blo 1032607 5303335 := bstep (se 1 (by rfl) ⟨3977501, by rfl⟩ : syracuseStep 5303335 = 7955003) B7955003
theorem B2616563 : Blo 1032607 2616563 := bstep (se 1 (by rfl) ⟨1962422, by rfl⟩ : syracuseStep 2616563 = 3924845) B3924845
theorem B1994233 : Blo 1032607 1994233 := bstep (se 2 (by rfl) ⟨747837, by rfl⟩ : syracuseStep 1994233 = 1495675) B1495675
theorem B1961633 : Blo 1032607 1961633 := bstep (se 2 (by rfl) ⟨735612, by rfl⟩ : syracuseStep 1961633 = 1471225) B1471225
theorem B12775085 : Blo 1032607 12775085 := bstep (se 3 (by rfl) ⟨2395328, by rfl⟩ : syracuseStep 12775085 = 4790657) B4790657
theorem B2617019 : Blo 1032607 2617019 := bstep (se 1 (by rfl) ⟨1962764, by rfl⟩ : syracuseStep 2617019 = 3925529) B3925529
theorem B1241039 : Blo 1032607 1241039 := bstep (se 1 (by rfl) ⟨930779, by rfl⟩ : syracuseStep 1241039 = 1861559) B1861559
theorem B2617555 : Blo 1032607 2617555 := bstep (se 1 (by rfl) ⟨1963166, by rfl⟩ : syracuseStep 2617555 = 3926333) B3926333
theorem B5304649 : Blo 1032607 5304649 := bstep (se 2 (by rfl) ⟨1989243, by rfl⟩ : syracuseStep 5304649 = 3978487) B3978487
theorem B1962407 : Blo 1032607 1962407 := bstep (se 1 (by rfl) ⟨1471805, by rfl⟩ : syracuseStep 1962407 = 2943611) B2943611
theorem B5239241 : Blo 1032607 5239241 := bstep (se 2 (by rfl) ⟨1964715, by rfl⟩ : syracuseStep 5239241 = 3929431) B3929431
theorem B7565885 : Blo 1032607 7565885 := bstep (se 3 (by rfl) ⟨1418603, by rfl⟩ : syracuseStep 7565885 = 2837207) B2837207
theorem B1962559 : Blo 1032607 1962559 := bstep (se 1 (by rfl) ⟨1471919, by rfl⟩ : syracuseStep 1962559 = 2943839) B2943839
theorem B7762553 : Blo 1032607 7762553 := bstep (se 2 (by rfl) ⟨2910957, by rfl⟩ : syracuseStep 7762553 = 5821915) B5821915
theorem B5894855 : Blo 1032607 5894855 := bstep (se 1 (by rfl) ⟨4421141, by rfl⟩ : syracuseStep 5894855 = 8842283) B8842283
theorem B5600353 : Blo 1032607 5600353 := bstep (se 2 (by rfl) ⟨2100132, by rfl⟩ : syracuseStep 5600353 = 4200265) B4200265
theorem B2618507 : Blo 1032607 2618507 := bstep (se 1 (by rfl) ⟨1963880, by rfl⟩ : syracuseStep 2618507 = 3927761) B3927761
theorem B2323655 : Blo 1032607 2323655 := bstep (se 1 (by rfl) ⟨1742741, by rfl⟩ : syracuseStep 2323655 = 3485483) B3485483
theorem B5240051 : Blo 1032607 5240051 := bstep (se 1 (by rfl) ⟨3930038, by rfl⟩ : syracuseStep 5240051 = 7860077) B7860077
theorem B1471783 : Blo 1032607 1471783 := bstep (se 1 (by rfl) ⟨1103837, by rfl⟩ : syracuseStep 1471783 = 2207675) B2207675
theorem B4781351 : Blo 1032607 4781351 := bstep (se 1 (by rfl) ⟨3586013, by rfl⟩ : syracuseStep 4781351 = 7172027) B7172027
theorem B8975711 : Blo 1032607 8975711 := bstep (se 1 (by rfl) ⟨6731783, by rfl⟩ : syracuseStep 8975711 = 13463567) B13463567
theorem B2323835 : Blo 1032607 2323835 := bstep (se 1 (by rfl) ⟨1742876, by rfl⟩ : syracuseStep 2323835 = 3485753) B3485753
theorem B2323961 : Blo 1032607 2323961 := bstep (se 2 (by rfl) ⟨871485, by rfl⟩ : syracuseStep 2323961 = 1742971) B1742971
theorem B2324051 : Blo 1032607 2324051 := bstep (se 1 (by rfl) ⟨1743038, by rfl⟩ : syracuseStep 2324051 = 3486077) B3486077
theorem B2618963 : Blo 1032607 2618963 := bstep (se 1 (by rfl) ⟨1964222, by rfl⟩ : syracuseStep 2618963 = 3928445) B3928445
theorem B1963615 : Blo 1032607 1963615 := bstep (se 1 (by rfl) ⟨1472711, by rfl⟩ : syracuseStep 1963615 = 2945423) B2945423
theorem B2324231 : Blo 1032607 2324231 := bstep (se 1 (by rfl) ⟨1743173, by rfl⟩ : syracuseStep 2324231 = 3486347) B3486347
theorem B6289181 : Blo 1032607 6289181 := bstep (se 3 (by rfl) ⟨1179221, by rfl⟩ : syracuseStep 6289181 = 2358443) B2358443
theorem B1243355 : Blo 1032607 1243355 := bstep (se 1 (by rfl) ⟨932516, by rfl⟩ : syracuseStep 1243355 = 1865033) B1865033
theorem B2947337 : Blo 1032607 2947337 := bstep (se 2 (by rfl) ⟨1105251, by rfl⟩ : syracuseStep 2947337 = 2210503) B2210503
theorem B24181067 : Blo 1032607 24181067 := bstep (se 1 (by rfl) ⟨18135800, by rfl⟩ : syracuseStep 24181067 = 36271601) B36271601
theorem B2324843 : Blo 1032607 2324843 := bstep (se 1 (by rfl) ⟨1743632, by rfl⟩ : syracuseStep 2324843 = 3487265) B3487265
theorem B1309051 : Blo 1032607 1309051 := bstep (se 1 (by rfl) ⟨981788, by rfl⟩ : syracuseStep 1309051 = 1963577) B1963577
theorem B2619823 : Blo 1032607 2619823 := bstep (se 1 (by rfl) ⟨1964867, by rfl⟩ : syracuseStep 2619823 = 3929735) B3929735
theorem B2324987 : Blo 1032607 2324987 := bstep (se 1 (by rfl) ⟨1743740, by rfl⟩ : syracuseStep 2324987 = 3487481) B3487481
theorem B1309279 : Blo 1032607 1309279 := bstep (se 1 (by rfl) ⟨981959, by rfl⟩ : syracuseStep 1309279 = 1963919) B1963919
theorem B4422251 : Blo 1032607 4422251 := bstep (se 1 (by rfl) ⟨3316688, by rfl⟩ : syracuseStep 4422251 = 6633377) B6633377
theorem B2325113 : Blo 1032607 2325113 := bstep (se 2 (by rfl) ⟨871917, by rfl⟩ : syracuseStep 2325113 = 1743835) B1743835
theorem B11958923 : Blo 1032607 11958923 := bstep (se 1 (by rfl) ⟨8969192, by rfl⟩ : syracuseStep 11958923 = 17938385) B17938385
theorem B4979339 : Blo 1032607 4979339 := bstep (se 1 (by rfl) ⟨3734504, by rfl⟩ : syracuseStep 4979339 = 7469009) B7469009
theorem B2325167 : Blo 1032607 2325167 := bstep (se 1 (by rfl) ⟨1743875, by rfl⟩ : syracuseStep 2325167 = 3487751) B3487751
theorem B1243831 : Blo 1032607 1243831 := bstep (se 1 (by rfl) ⟨932873, by rfl⟩ : syracuseStep 1243831 = 1865747) B1865747
theorem B2620127 : Blo 1032607 2620127 := bstep (se 1 (by rfl) ⟨1965095, by rfl⟩ : syracuseStep 2620127 = 3930191) B3930191
theorem B2325239 : Blo 1032607 2325239 := bstep (se 1 (by rfl) ⟨1743929, by rfl⟩ : syracuseStep 2325239 = 3487859) B3487859
theorem B11795219 : Blo 1032607 11795219 := bstep (se 1 (by rfl) ⟨8846414, by rfl⟩ : syracuseStep 11795219 = 17692829) B17692829
theorem B6617999 : Blo 1032607 6617999 := bstep (se 1 (by rfl) ⟨4963499, by rfl⟩ : syracuseStep 6617999 = 9926999) B9926999
theorem B2325419 : Blo 1032607 2325419 := bstep (se 1 (by rfl) ⟨1744064, by rfl⟩ : syracuseStep 2325419 = 3488129) B3488129
theorem B5241995 : Blo 1032607 5241995 := bstep (se 1 (by rfl) ⟨3931496, by rfl⟩ : syracuseStep 5241995 = 7862993) B7862993
theorem B9960677 : Blo 1032607 9960677 := bstep (se 4 (by rfl) ⟨933813, by rfl⟩ : syracuseStep 9960677 = 1867627) B1867627
theorem B3308897 : Blo 1032607 3308897 := bstep (se 2 (by rfl) ⟨1240836, by rfl⟩ : syracuseStep 3308897 = 2481673) B2481673
theorem B1244527 : Blo 1032607 1244527 := bstep (se 1 (by rfl) ⟨933395, by rfl⟩ : syracuseStep 1244527 = 1866791) B1866791
theorem B2620795 : Blo 1032607 2620795 := bstep (se 1 (by rfl) ⟨1965596, by rfl⟩ : syracuseStep 2620795 = 3931193) B3931193
theorem B2325959 : Blo 1032607 2325959 := bstep (se 1 (by rfl) ⟨1744469, by rfl⟩ : syracuseStep 2325959 = 3488939) B3488939
theorem B4423193 : Blo 1032607 4423193 := bstep (se 2 (by rfl) ⟨1658697, by rfl⟩ : syracuseStep 4423193 = 3317395) B3317395
theorem B34012817 : Blo 1032607 34012817 := bstep (se 2 (by rfl) ⟨12754806, by rfl⟩ : syracuseStep 34012817 = 25509613) B25509613
theorem B2326319 : Blo 1032607 2326319 := bstep (se 1 (by rfl) ⟨1744739, by rfl⟩ : syracuseStep 2326319 = 3489479) B3489479
theorem B2621231 : Blo 1032607 2621231 := bstep (se 1 (by rfl) ⟨1965923, by rfl⟩ : syracuseStep 2621231 = 3931847) B3931847
theorem B1310519 : Blo 1032607 1310519 := bstep (se 1 (by rfl) ⟨982889, by rfl⟩ : syracuseStep 1310519 = 1965779) B1965779
theorem B4423481 : Blo 1032607 4423481 := bstep (se 2 (by rfl) ⟨1658805, by rfl⟩ : syracuseStep 4423481 = 3317611) B3317611
theorem B5046077 : Blo 1032607 5046077 := bstep (se 3 (by rfl) ⟨946139, by rfl⟩ : syracuseStep 5046077 = 1892279) B1892279
theorem B1310671 : Blo 1032607 1310671 := bstep (se 1 (by rfl) ⟨983003, by rfl⟩ : syracuseStep 1310671 = 1966007) B1966007
theorem B5898521 : Blo 1032607 5898521 := bstep (se 2 (by rfl) ⟨2211945, by rfl⟩ : syracuseStep 5898521 = 4423891) B4423891
theorem B2687263 : Blo 1032607 2687263 := bstep (se 1 (by rfl) ⟨2015447, by rfl⟩ : syracuseStep 2687263 = 4030895) B4030895
theorem B2359739 : Blo 1032607 2359739 := bstep (se 1 (by rfl) ⟨1769804, by rfl⟩ : syracuseStep 2359739 = 3539609) B3539609
theorem B5898703 : Blo 1032607 5898703 := bstep (se 1 (by rfl) ⟨4424027, by rfl⟩ : syracuseStep 5898703 = 8848055) B8848055
theorem B2621929 : Blo 1032607 2621929 := bstep (se 2 (by rfl) ⟨983223, by rfl⟩ : syracuseStep 2621929 = 1966447) B1966447
theorem B5047049 : Blo 1032607 5047049 := bstep (se 2 (by rfl) ⟨1892643, by rfl⟩ : syracuseStep 5047049 = 3785287) B3785287
theorem B2327507 : Blo 1032607 2327507 := bstep (se 1 (by rfl) ⟨1745630, by rfl⟩ : syracuseStep 2327507 = 3491261) B3491261
theorem B2327759 : Blo 1032607 2327759 := bstep (se 1 (by rfl) ⟨1745819, by rfl⟩ : syracuseStep 2327759 = 3491639) B3491639
theorem B3540473 : Blo 1032607 3540473 := bstep (se 2 (by rfl) ⟨1327677, by rfl⟩ : syracuseStep 3540473 = 2655355) B2655355
theorem B2328083 : Blo 1032607 2328083 := bstep (se 1 (by rfl) ⟨1746062, by rfl⟩ : syracuseStep 2328083 = 3492125) B3492125
theorem B3933791 : Blo 1032607 3933791 := bstep (se 1 (by rfl) ⟨2950343, by rfl⟩ : syracuseStep 3933791 = 5900687) B5900687
theorem B5900161 : Blo 1032607 5900161 := bstep (se 2 (by rfl) ⟨2212560, by rfl⟩ : syracuseStep 5900161 = 4425121) B4425121
theorem B8390699 : Blo 1032607 8390699 := bstep (se 1 (by rfl) ⟨6293024, by rfl⟩ : syracuseStep 8390699 = 12586049) B12586049
theorem B2328767 : Blo 1032607 2328767 := bstep (se 1 (by rfl) ⟨1746575, by rfl⟩ : syracuseStep 2328767 = 3493151) B3493151
theorem B2951471 : Blo 1032607 2951471 := bstep (se 1 (by rfl) ⟨2213603, by rfl⟩ : syracuseStep 2951471 = 4427207) B4427207
theorem B2951585 : Blo 1032607 2951585 := bstep (se 2 (by rfl) ⟨1106844, by rfl⟩ : syracuseStep 2951585 = 2213689) B2213689
theorem B2951711 : Blo 1032607 2951711 := bstep (se 1 (by rfl) ⟨2213783, by rfl⟩ : syracuseStep 2951711 = 4427567) B4427567
theorem B2329721 : Blo 1032607 2329721 := bstep (se 2 (by rfl) ⟨873645, by rfl⟩ : syracuseStep 2329721 = 1747291) B1747291
theorem B8391869 : Blo 1032607 8391869 := bstep (se 3 (by rfl) ⟨1573475, by rfl⟩ : syracuseStep 8391869 = 3146951) B3146951
theorem B3935567 : Blo 1032607 3935567 := bstep (se 1 (by rfl) ⟨2951675, by rfl⟩ : syracuseStep 3935567 = 5903351) B5903351
theorem B6622715 : Blo 1032607 6622715 := bstep (se 1 (by rfl) ⟨4967036, by rfl⟩ : syracuseStep 6622715 = 9934073) B9934073
theorem B13438723 : Blo 1032607 13438723 := bstep (se 1 (by rfl) ⟨10079042, by rfl⟩ : syracuseStep 13438723 = 20158085) B20158085
theorem B2330387 : Blo 1032607 2330387 := bstep (se 1 (by rfl) ⟨1747790, by rfl⟩ : syracuseStep 2330387 = 3495581) B3495581
theorem B2330747 : Blo 1032607 2330747 := bstep (se 1 (by rfl) ⟨1748060, by rfl⟩ : syracuseStep 2330747 = 3496121) B3496121
theorem B6295805 : Blo 1032607 6295805 := bstep (se 3 (by rfl) ⟨1180463, by rfl⟩ : syracuseStep 6295805 = 2360927) B2360927
theorem B2331017 : Blo 1032607 2331017 := bstep (se 2 (by rfl) ⟨874131, by rfl⟩ : syracuseStep 2331017 = 1748263) B1748263
theorem B7082497 : Blo 1032607 7082497 := bstep (se 2 (by rfl) ⟨2655936, by rfl⟩ : syracuseStep 7082497 = 5311873) B5311873
theorem B4199015 : Blo 1032607 4199015 := bstep (se 1 (by rfl) ⟨3149261, by rfl⟩ : syracuseStep 4199015 = 6298523) B6298523
theorem B2658977 : Blo 1032607 2658977 := bstep (se 2 (by rfl) ⟨997116, by rfl⟩ : syracuseStep 2658977 = 1994233) B1994233
theorem B13276183 : Blo 1032607 13276183 := bstep (se 1 (by rfl) ⟨9957137, by rfl⟩ : syracuseStep 13276183 = 19914275) B19914275
theorem B28284011 : Blo 1032607 28284011 := bstep (se 1 (by rfl) ⟨21213008, by rfl⟩ : syracuseStep 28284011 = 42426017) B42426017
theorem B2331755 : Blo 1032607 2331755 := bstep (se 1 (by rfl) ⟨1748816, by rfl⟩ : syracuseStep 2331755 = 3497633) B3497633
theorem B39720293 : Blo 1032607 39720293 := bstep (se 4 (by rfl) ⟨3723777, by rfl⟩ : syracuseStep 39720293 = 7447555) B7447555
theorem B6624665 : Blo 1032607 6624665 := bstep (se 2 (by rfl) ⟨2484249, by rfl⟩ : syracuseStep 6624665 = 4968499) B4968499
theorem B2332331 : Blo 1032607 2332331 := bstep (se 1 (by rfl) ⟨1749248, by rfl⟩ : syracuseStep 2332331 = 3498497) B3498497
theorem B3315613 : Blo 1032607 3315613 := bstep (se 3 (by rfl) ⟨621677, by rfl⟩ : syracuseStep 3315613 = 1243355) B1243355
theorem B4036763 : Blo 1032607 4036763 := bstep (se 1 (by rfl) ⟨3027572, by rfl⟩ : syracuseStep 4036763 = 6055145) B6055145
theorem B3545737 : Blo 1032607 3545737 := bstep (se 2 (by rfl) ⟨1329651, by rfl⟩ : syracuseStep 3545737 = 2659303) B2659303
theorem B1743707 : Blo 1032607 1743707 := bstep (se 1 (by rfl) ⟨1307780, by rfl⟩ : syracuseStep 1743707 = 2615561) B2615561
theorem B1743943 : Blo 1032607 1743943 := bstep (se 1 (by rfl) ⟨1307957, by rfl⟩ : syracuseStep 1743943 = 2615915) B2615915
theorem B3317087 : Blo 1032607 3317087 := bstep (se 1 (by rfl) ⟨2487815, by rfl⟩ : syracuseStep 3317087 = 4975631) B4975631
theorem B1744375 : Blo 1032607 1744375 := bstep (se 1 (by rfl) ⟨1308281, by rfl⟩ : syracuseStep 1744375 = 2616563) B2616563
theorem B1744679 : Blo 1032607 1744679 := bstep (se 1 (by rfl) ⟨1308509, by rfl⟩ : syracuseStep 1744679 = 2617019) B2617019
theorem B1745401 : Blo 1032607 1745401 := bstep (se 2 (by rfl) ⟨654525, by rfl⟩ : syracuseStep 1745401 = 1309051) B1309051
theorem B1745671 : Blo 1032607 1745671 := bstep (se 1 (by rfl) ⟨1309253, by rfl⟩ : syracuseStep 1745671 = 2618507) B2618507
theorem B1549097 : Blo 1032607 1549097 := bstep (se 2 (by rfl) ⟨580911, by rfl⟩ : syracuseStep 1549097 = 1161823) B1161823
theorem B1745705 : Blo 1032607 1745705 := bstep (se 2 (by rfl) ⟨654639, by rfl⟩ : syracuseStep 1745705 = 1309279) B1309279
theorem B1549103 : Blo 1032607 1549103 := bstep (se 1 (by rfl) ⟨1161827, by rfl⟩ : syracuseStep 1549103 = 2323655) B2323655
theorem B3187567 : Blo 1032607 3187567 := bstep (se 1 (by rfl) ⟨2390675, by rfl⟩ : syracuseStep 3187567 = 4781351) B4781351
theorem B1549223 : Blo 1032607 1549223 := bstep (se 1 (by rfl) ⟨1161917, by rfl⟩ : syracuseStep 1549223 = 2323835) B2323835
theorem B8823725 : Blo 1032607 8823725 := bstep (se 3 (by rfl) ⟨1654448, by rfl⟩ : syracuseStep 8823725 = 3308897) B3308897
theorem B1549307 : Blo 1032607 1549307 := bstep (se 1 (by rfl) ⟨1161980, by rfl⟩ : syracuseStep 1549307 = 2323961) B2323961
theorem B1549367 : Blo 1032607 1549367 := bstep (se 1 (by rfl) ⟨1162025, by rfl⟩ : syracuseStep 1549367 = 2324051) B2324051
theorem B1745975 : Blo 1032607 1745975 := bstep (se 1 (by rfl) ⟨1309481, by rfl⟩ : syracuseStep 1745975 = 2618963) B2618963
theorem B1549487 : Blo 1032607 1549487 := bstep (se 1 (by rfl) ⟨1162115, by rfl⟩ : syracuseStep 1549487 = 2324231) B2324231
theorem B7546105 : Blo 1032607 7546105 := bstep (se 2 (by rfl) ⟨2829789, by rfl⟩ : syracuseStep 7546105 = 5659579) B5659579
theorem B6628715 : Blo 1032607 6628715 := bstep (se 1 (by rfl) ⟨4971536, by rfl⟩ : syracuseStep 6628715 = 9943073) B9943073
theorem B1549895 : Blo 1032607 1549895 := bstep (se 1 (by rfl) ⟨1162421, by rfl⟩ : syracuseStep 1549895 = 2324843) B2324843
theorem B1549991 : Blo 1032607 1549991 := bstep (se 1 (by rfl) ⟨1162493, by rfl⟩ : syracuseStep 1549991 = 2324987) B2324987
theorem B1550075 : Blo 1032607 1550075 := bstep (se 1 (by rfl) ⟨1162556, by rfl⟩ : syracuseStep 1550075 = 2325113) B2325113
theorem B7972615 : Blo 1032607 7972615 := bstep (se 1 (by rfl) ⟨5979461, by rfl⟩ : syracuseStep 7972615 = 11958923) B11958923
theorem B3319559 : Blo 1032607 3319559 := bstep (se 1 (by rfl) ⟨2489669, by rfl⟩ : syracuseStep 3319559 = 4979339) B4979339
theorem B1550111 : Blo 1032607 1550111 := bstep (se 1 (by rfl) ⟨1162583, by rfl⟩ : syracuseStep 1550111 = 2325167) B2325167
theorem B1746751 : Blo 1032607 1746751 := bstep (se 1 (by rfl) ⟨1310063, by rfl⟩ : syracuseStep 1746751 = 2620127) B2620127
theorem B1550159 : Blo 1032607 1550159 := bstep (se 1 (by rfl) ⟨1162619, by rfl⟩ : syracuseStep 1550159 = 2325239) B2325239
theorem B1550279 : Blo 1032607 1550279 := bstep (se 1 (by rfl) ⟨1162709, by rfl⟩ : syracuseStep 1550279 = 2325419) B2325419
theorem B2238455 : Blo 1032607 2238455 := bstep (se 1 (by rfl) ⟨1678841, by rfl⟩ : syracuseStep 2238455 = 3357683) B3357683
theorem B11806883 : Blo 1032607 11806883 := bstep (se 1 (by rfl) ⟨8855162, by rfl⟩ : syracuseStep 11806883 = 17710325) B17710325
theorem B1550633 : Blo 1032607 1550633 := bstep (se 2 (by rfl) ⟨581487, by rfl⟩ : syracuseStep 1550633 = 1162975) B1162975
theorem B1550639 : Blo 1032607 1550639 := bstep (se 1 (by rfl) ⟨1162979, by rfl⟩ : syracuseStep 1550639 = 2325959) B2325959
theorem B1747487 : Blo 1032607 1747487 := bstep (se 1 (by rfl) ⟨1310615, by rfl⟩ : syracuseStep 1747487 = 2621231) B2621231
theorem B1550879 : Blo 1032607 1550879 := bstep (se 1 (by rfl) ⟨1163159, by rfl⟩ : syracuseStep 1550879 = 2326319) B2326319
theorem B2239007 : Blo 1032607 2239007 := bstep (se 1 (by rfl) ⟨1679255, by rfl⟩ : syracuseStep 2239007 = 3358511) B3358511
theorem B1747561 : Blo 1032607 1747561 := bstep (se 2 (by rfl) ⟨655335, by rfl⟩ : syracuseStep 1747561 = 1310671) B1310671
theorem B14887729 : Blo 1032607 14887729 := bstep (se 2 (by rfl) ⟨5582898, by rfl⟩ : syracuseStep 14887729 = 11165797) B11165797
theorem B1551263 : Blo 1032607 1551263 := bstep (se 1 (by rfl) ⟨1163447, by rfl⟩ : syracuseStep 1551263 = 2326895) B2326895
theorem B1551311 : Blo 1032607 1551311 := bstep (se 1 (by rfl) ⟨1163483, by rfl⟩ : syracuseStep 1551311 = 2326967) B2326967
theorem B1747919 : Blo 1032607 1747919 := bstep (se 1 (by rfl) ⟨1310939, by rfl⟩ : syracuseStep 1747919 = 2621879) B2621879
theorem B1551401 : Blo 1032607 1551401 := bstep (se 2 (by rfl) ⟨581775, by rfl⟩ : syracuseStep 1551401 = 1163551) B1163551
theorem B1551407 : Blo 1032607 1551407 := bstep (se 1 (by rfl) ⟨1163555, by rfl⟩ : syracuseStep 1551407 = 2327111) B2327111
theorem B1551431 : Blo 1032607 1551431 := bstep (se 1 (by rfl) ⟨1163573, by rfl⟩ : syracuseStep 1551431 = 2327147) B2327147
theorem B1551695 : Blo 1032607 1551695 := bstep (se 1 (by rfl) ⟨1163771, by rfl⟩ : syracuseStep 1551695 = 2327543) B2327543
theorem B3485051 : Blo 1032607 3485051 := bstep (se 1 (by rfl) ⟨2613788, by rfl⟩ : syracuseStep 3485051 = 5227577) B5227577
theorem B1551785 : Blo 1032607 1551785 := bstep (se 2 (by rfl) ⟨581919, by rfl⟩ : syracuseStep 1551785 = 1163839) B1163839
theorem B2829887 : Blo 1032607 2829887 := bstep (se 1 (by rfl) ⟨2122415, by rfl⟩ : syracuseStep 2829887 = 4244831) B4244831
theorem B1551935 : Blo 1032607 1551935 := bstep (se 1 (by rfl) ⟨1163951, by rfl⟩ : syracuseStep 1551935 = 2327903) B2327903
theorem B1748587 : Blo 1032607 1748587 := bstep (se 1 (by rfl) ⟨1311440, by rfl⟩ : syracuseStep 1748587 = 2622881) B2622881
theorem B1552199 : Blo 1032607 1552199 := bstep (se 1 (by rfl) ⟨1164149, by rfl⟩ : syracuseStep 1552199 = 2328299) B2328299
theorem B1748857 : Blo 1032607 1748857 := bstep (se 2 (by rfl) ⟨655821, by rfl⟩ : syracuseStep 1748857 = 1311643) B1311643
theorem B1552283 : Blo 1032607 1552283 := bstep (se 1 (by rfl) ⟨1164212, by rfl⟩ : syracuseStep 1552283 = 2328425) B2328425
theorem B1748891 : Blo 1032607 1748891 := bstep (se 1 (by rfl) ⟨1311668, by rfl⟩ : syracuseStep 1748891 = 2623337) B2623337
theorem B11776265 : Blo 1032607 11776265 := bstep (se 2 (by rfl) ⟨4416099, by rfl⟩ : syracuseStep 11776265 = 8832199) B8832199
theorem B1552847 : Blo 1032607 1552847 := bstep (se 1 (by rfl) ⟨1164635, by rfl⟩ : syracuseStep 1552847 = 2329271) B2329271
theorem B1552889 : Blo 1032607 1552889 := bstep (se 2 (by rfl) ⟨582333, by rfl⟩ : syracuseStep 1552889 = 1164667) B1164667
theorem B1552991 : Blo 1032607 1552991 := bstep (se 1 (by rfl) ⟨1164743, by rfl⟩ : syracuseStep 1552991 = 2329487) B2329487
theorem B3486455 : Blo 1032607 3486455 := bstep (se 1 (by rfl) ⟨2614841, by rfl⟩ : syracuseStep 3486455 = 5229683) B5229683
theorem B9450335 : Blo 1032607 9450335 := bstep (se 1 (by rfl) ⟨7087751, by rfl⟩ : syracuseStep 9450335 = 14175503) B14175503
theorem B1553471 : Blo 1032607 1553471 := bstep (se 1 (by rfl) ⟨1165103, by rfl⟩ : syracuseStep 1553471 = 2330207) B2330207
theorem B1553513 : Blo 1032607 1553513 := bstep (se 2 (by rfl) ⟨582567, by rfl⟩ : syracuseStep 1553513 = 1165135) B1165135
theorem B8828099 : Blo 1032607 8828099 := bstep (se 1 (by rfl) ⟨6621074, by rfl⟩ : syracuseStep 8828099 = 13242149) B13242149
theorem B1553615 : Blo 1032607 1553615 := bstep (se 1 (by rfl) ⟨1165211, by rfl⟩ : syracuseStep 1553615 = 2330423) B2330423
theorem B3486995 : Blo 1032607 3486995 := bstep (se 1 (by rfl) ⟨2615246, by rfl⟩ : syracuseStep 3486995 = 5230493) B5230493
theorem B5584283 : Blo 1032607 5584283 := bstep (se 1 (by rfl) ⟨4188212, by rfl⟩ : syracuseStep 5584283 = 8376425) B8376425
theorem B1553819 : Blo 1032607 1553819 := bstep (se 1 (by rfl) ⟨1165364, by rfl⟩ : syracuseStep 1553819 = 2330729) B2330729
theorem B1554041 : Blo 1032607 1554041 := bstep (se 2 (by rfl) ⟨582765, by rfl⟩ : syracuseStep 1554041 = 1165531) B1165531
theorem B1554143 : Blo 1032607 1554143 := bstep (se 1 (by rfl) ⟨1165607, by rfl⟩ : syracuseStep 1554143 = 2331215) B2331215
theorem B3487535 : Blo 1032607 3487535 := bstep (se 1 (by rfl) ⟨2615651, by rfl⟩ : syracuseStep 3487535 = 5231303) B5231303
theorem B1554239 : Blo 1032607 1554239 := bstep (se 1 (by rfl) ⟨1165679, by rfl⟩ : syracuseStep 1554239 = 2331359) B2331359
theorem B6633353 : Blo 1032607 6633353 := bstep (se 2 (by rfl) ⟨2487507, by rfl⟩ : syracuseStep 6633353 = 4975015) B4975015
theorem B38320067 : Blo 1032607 38320067 := bstep (se 1 (by rfl) ⟨28740050, by rfl⟩ : syracuseStep 38320067 = 57480101) B57480101
theorem B1554407 : Blo 1032607 1554407 := bstep (se 1 (by rfl) ⟨1165805, by rfl⟩ : syracuseStep 1554407 = 2331611) B2331611
theorem B1554425 : Blo 1032607 1554425 := bstep (se 2 (by rfl) ⟨582909, by rfl⟩ : syracuseStep 1554425 = 1165819) B1165819
theorem B1554527 : Blo 1032607 1554527 := bstep (se 1 (by rfl) ⟨1165895, by rfl⟩ : syracuseStep 1554527 = 2331791) B2331791
theorem B1554587 : Blo 1032607 1554587 := bstep (se 1 (by rfl) ⟨1165940, by rfl⟩ : syracuseStep 1554587 = 2331881) B2331881
theorem B1554623 : Blo 1032607 1554623 := bstep (se 1 (by rfl) ⟨1165967, by rfl⟩ : syracuseStep 1554623 = 2331935) B2331935
theorem B1554665 : Blo 1032607 1554665 := bstep (se 2 (by rfl) ⟨582999, by rfl⟩ : syracuseStep 1554665 = 1165999) B1165999
theorem B6633839 : Blo 1032607 6633839 := bstep (se 1 (by rfl) ⟨4975379, by rfl⟩ : syracuseStep 6633839 = 9950759) B9950759
theorem B12270197 : Blo 1032607 12270197 := bstep (se 5 (by rfl) ⟨575165, by rfl⟩ : syracuseStep 12270197 = 1150331) B1150331
theorem B1162075 : Blo 1032607 1162075 := bstep (se 1 (by rfl) ⟨871556, by rfl⟩ : syracuseStep 1162075 = 1743113) B1743113
theorem B2210665 : Blo 1032607 2210665 := bstep (se 2 (by rfl) ⟨828999, by rfl⟩ : syracuseStep 2210665 = 1657999) B1657999
theorem B9944221 : Blo 1032607 9944221 := bstep (se 3 (by rfl) ⟨1864541, by rfl⟩ : syracuseStep 9944221 = 3729083) B3729083
theorem B5881207 : Blo 1032607 5881207 := bstep (se 1 (by rfl) ⟨4410905, by rfl⟩ : syracuseStep 5881207 = 8821811) B8821811
theorem B3489371 : Blo 1032607 3489371 := bstep (se 1 (by rfl) ⟨2617028, by rfl⟩ : syracuseStep 3489371 = 5234057) B5234057
theorem B2211553 : Blo 1032607 2211553 := bstep (se 2 (by rfl) ⟨829332, by rfl⟩ : syracuseStep 2211553 = 1658665) B1658665
theorem B1163047 : Blo 1032607 1163047 := bstep (se 1 (by rfl) ⟨872285, by rfl⟩ : syracuseStep 1163047 = 1744571) B1744571
theorem B2211707 : Blo 1032607 2211707 := bstep (se 1 (by rfl) ⟨1658780, by rfl⟩ : syracuseStep 2211707 = 3317561) B3317561
theorem B28655531 : Blo 1032607 28655531 := bstep (se 1 (by rfl) ⟨21491648, by rfl⟩ : syracuseStep 28655531 = 42983297) B42983297
theorem B1654751 : Blo 1032607 1654751 := bstep (se 1 (by rfl) ⟨1241063, by rfl⟩ : syracuseStep 1654751 = 2482127) B2482127
theorem B6144025 : Blo 1032607 6144025 := bstep (se 2 (by rfl) ⟨2304009, by rfl⟩ : syracuseStep 6144025 = 4608019) B4608019
theorem B7979147 : Blo 1032607 7979147 := bstep (se 1 (by rfl) ⟨5984360, by rfl⟩ : syracuseStep 7979147 = 11968721) B11968721
theorem B3490073 : Blo 1032607 3490073 := bstep (se 2 (by rfl) ⟨1308777, by rfl⟩ : syracuseStep 3490073 = 2617555) B2617555
theorem B3490235 : Blo 1032607 3490235 := bstep (se 1 (by rfl) ⟨2617676, by rfl⟩ : syracuseStep 3490235 = 5235353) B5235353
theorem B1032655 : Blo 1032607 1032655 := bstep (se 1 (by rfl) ⟨774491, by rfl⟩ : syracuseStep 1032655 = 1548983) B1548983
theorem B1032807 : Blo 1032607 1032807 := bstep (se 1 (by rfl) ⟨774605, by rfl⟩ : syracuseStep 1032807 = 1549211) B1549211
theorem B14926481 : Blo 1032607 14926481 := bstep (se 2 (by rfl) ⟨5597430, by rfl⟩ : syracuseStep 14926481 = 11194861) B11194861
theorem B1033071 : Blo 1032607 1033071 := bstep (se 1 (by rfl) ⟨774803, by rfl⟩ : syracuseStep 1033071 = 1549607) B1549607
theorem B1033127 : Blo 1032607 1033127 := bstep (se 1 (by rfl) ⟨774845, by rfl⟩ : syracuseStep 1033127 = 1549691) B1549691
theorem B1164199 : Blo 1032607 1164199 := bstep (se 1 (by rfl) ⟨873149, by rfl⟩ : syracuseStep 1164199 = 1746299) B1746299
theorem B7455689 : Blo 1032607 7455689 := bstep (se 2 (by rfl) ⟨2795883, by rfl⟩ : syracuseStep 7455689 = 5591767) B5591767
theorem B1033211 : Blo 1032607 1033211 := bstep (se 1 (by rfl) ⟨774908, by rfl⟩ : syracuseStep 1033211 = 1549817) B1549817
theorem B5882939 : Blo 1032607 5882939 := bstep (se 1 (by rfl) ⟨4412204, by rfl⟩ : syracuseStep 5882939 = 8824409) B8824409
theorem B1033279 : Blo 1032607 1033279 := bstep (se 1 (by rfl) ⟨774959, by rfl⟩ : syracuseStep 1033279 = 1549919) B1549919
theorem B1033423 : Blo 1032607 1033423 := bstep (se 1 (by rfl) ⟨775067, by rfl⟩ : syracuseStep 1033423 = 1550135) B1550135
theorem B44811629 : Blo 1032607 44811629 := bstep (se 3 (by rfl) ⟨8402180, by rfl⟩ : syracuseStep 44811629 = 16804361) B16804361
theorem B1033627 : Blo 1032607 1033627 := bstep (se 1 (by rfl) ⟨775220, by rfl⟩ : syracuseStep 1033627 = 1550441) B1550441
theorem B1656391 : Blo 1032607 1656391 := bstep (se 1 (by rfl) ⟨1242293, by rfl⟩ : syracuseStep 1656391 = 2484587) B2484587
theorem B3491423 : Blo 1032607 3491423 := bstep (se 1 (by rfl) ⟨2618567, by rfl⟩ : syracuseStep 3491423 = 5237135) B5237135
theorem B1033839 : Blo 1032607 1033839 := bstep (se 1 (by rfl) ⟨775379, by rfl⟩ : syracuseStep 1033839 = 1550759) B1550759
theorem B1033895 : Blo 1032607 1033895 := bstep (se 1 (by rfl) ⟨775421, by rfl⟩ : syracuseStep 1033895 = 1550843) B1550843
theorem B1033979 : Blo 1032607 1033979 := bstep (se 1 (by rfl) ⟨775484, by rfl⟩ : syracuseStep 1033979 = 1550969) B1550969
theorem B1034015 : Blo 1032607 1034015 := bstep (se 1 (by rfl) ⟨775511, by rfl⟩ : syracuseStep 1034015 = 1551023) B1551023
theorem B1034047 : Blo 1032607 1034047 := bstep (se 1 (by rfl) ⟨775535, by rfl⟩ : syracuseStep 1034047 = 1551071) B1551071
theorem B6637477 : Blo 1032607 6637477 := bstep (se 4 (by rfl) ⟨622263, by rfl⟩ : syracuseStep 6637477 = 1244527) B1244527
theorem B1034223 : Blo 1032607 1034223 := bstep (se 1 (by rfl) ⟨775667, by rfl⟩ : syracuseStep 1034223 = 1551335) B1551335
theorem B1034395 : Blo 1032607 1034395 := bstep (se 1 (by rfl) ⟨775796, by rfl⟩ : syracuseStep 1034395 = 1551593) B1551593
theorem B1034431 : Blo 1032607 1034431 := bstep (se 1 (by rfl) ⟨775823, by rfl⟩ : syracuseStep 1034431 = 1551647) B1551647
theorem B1034543 : Blo 1032607 1034543 := bstep (se 1 (by rfl) ⟨775907, by rfl⟩ : syracuseStep 1034543 = 1551815) B1551815
theorem B1034779 : Blo 1032607 1034779 := bstep (se 1 (by rfl) ⟨776084, by rfl⟩ : syracuseStep 1034779 = 1552169) B1552169
theorem B1034783 : Blo 1032607 1034783 := bstep (se 1 (by rfl) ⟨776087, by rfl⟩ : syracuseStep 1034783 = 1552175) B1552175
theorem B1165855 : Blo 1032607 1165855 := bstep (se 1 (by rfl) ⟨874391, by rfl⟩ : syracuseStep 1165855 = 1748783) B1748783
theorem B1035099 : Blo 1032607 1035099 := bstep (se 1 (by rfl) ⟨776324, by rfl⟩ : syracuseStep 1035099 = 1552649) B1552649
theorem B1035167 : Blo 1032607 1035167 := bstep (se 1 (by rfl) ⟨776375, by rfl⟩ : syracuseStep 1035167 = 1552751) B1552751
theorem B3492827 : Blo 1032607 3492827 := bstep (se 1 (by rfl) ⟨2619620, by rfl⟩ : syracuseStep 3492827 = 5239241) B5239241
theorem B1035311 : Blo 1032607 1035311 := bstep (se 1 (by rfl) ⟨776483, by rfl⟩ : syracuseStep 1035311 = 1552967) B1552967
theorem B1035335 : Blo 1032607 1035335 := bstep (se 1 (by rfl) ⟨776501, by rfl⟩ : syracuseStep 1035335 = 1553003) B1553003
theorem B28691587 : Blo 1032607 28691587 := bstep (se 1 (by rfl) ⟨21518690, by rfl⟩ : syracuseStep 28691587 = 43037381) B43037381
theorem B1035487 : Blo 1032607 1035487 := bstep (se 1 (by rfl) ⟨776615, by rfl⟩ : syracuseStep 1035487 = 1553231) B1553231
theorem B3493097 : Blo 1032607 3493097 := bstep (se 2 (by rfl) ⟨1309911, by rfl⟩ : syracuseStep 3493097 = 2619823) B2619823
theorem B5230007 : Blo 1032607 5230007 := bstep (se 1 (by rfl) ⟨3922505, by rfl⟩ : syracuseStep 5230007 = 7845011) B7845011
theorem B1035751 : Blo 1032607 1035751 := bstep (se 1 (by rfl) ⟨776813, by rfl⟩ : syracuseStep 1035751 = 1553627) B1553627
theorem B3493367 : Blo 1032607 3493367 := bstep (se 1 (by rfl) ⟨2620025, by rfl⟩ : syracuseStep 3493367 = 5240051) B5240051
theorem B4967999 : Blo 1032607 4967999 := bstep (se 1 (by rfl) ⟨3725999, by rfl⟩ : syracuseStep 4967999 = 7451999) B7451999
theorem B5983807 : Blo 1032607 5983807 := bstep (se 1 (by rfl) ⟨4487855, by rfl⟩ : syracuseStep 5983807 = 8975711) B8975711
theorem B1658441 : Blo 1032607 1658441 := bstep (se 2 (by rfl) ⟨621915, by rfl⟩ : syracuseStep 1658441 = 1243831) B1243831
theorem B5230169 : Blo 1032607 5230169 := bstep (se 2 (by rfl) ⟨1961313, by rfl⟩ : syracuseStep 5230169 = 3922627) B3922627
theorem B1035867 : Blo 1032607 1035867 := bstep (se 1 (by rfl) ⟨776900, by rfl⟩ : syracuseStep 1035867 = 1553801) B1553801
theorem B1036103 : Blo 1032607 1036103 := bstep (se 1 (by rfl) ⟨777077, by rfl⟩ : syracuseStep 1036103 = 1554155) B1554155
theorem B1036255 : Blo 1032607 1036255 := bstep (se 1 (by rfl) ⟨777191, by rfl⟩ : syracuseStep 1036255 = 1554383) B1554383
theorem B1036519 : Blo 1032607 1036519 := bstep (se 1 (by rfl) ⟨777389, by rfl⟩ : syracuseStep 1036519 = 1554779) B1554779
theorem B3494393 : Blo 1032607 3494393 := bstep (se 2 (by rfl) ⟨1310397, by rfl⟩ : syracuseStep 3494393 = 2620795) B2620795
theorem B4411999 : Blo 1032607 4411999 := bstep (se 1 (by rfl) ⟨3308999, by rfl⟩ : syracuseStep 4411999 = 6617999) B6617999
theorem B3494663 : Blo 1032607 3494663 := bstep (se 1 (by rfl) ⟨2620997, by rfl⟩ : syracuseStep 3494663 = 5241995) B5241995
theorem B3494717 : Blo 1032607 3494717 := bstep (se 3 (by rfl) ⟨655259, by rfl⟩ : syracuseStep 3494717 = 1310519) B1310519
theorem B6640451 : Blo 1032607 6640451 := bstep (se 1 (by rfl) ⟨4980338, by rfl⟩ : syracuseStep 6640451 = 9960677) B9960677
theorem B3724343 : Blo 1032607 3724343 := bstep (se 1 (by rfl) ⟨2793257, by rfl⟩ : syracuseStep 3724343 = 5586515) B5586515
theorem B5887039 : Blo 1032607 5887039 := bstep (se 1 (by rfl) ⟨4415279, by rfl⟩ : syracuseStep 5887039 = 8830559) B8830559
theorem B3364051 : Blo 1032607 3364051 := bstep (se 1 (by rfl) ⟨2523038, by rfl⟩ : syracuseStep 3364051 = 5046077) B5046077
theorem B11654765 : Blo 1032607 11654765 := bstep (se 3 (by rfl) ⟨2185268, by rfl⟩ : syracuseStep 11654765 = 4370537) B4370537
theorem B3495743 : Blo 1032607 3495743 := bstep (se 1 (by rfl) ⟨2621807, by rfl⟩ : syracuseStep 3495743 = 5243615) B5243615
theorem B5232599 : Blo 1032607 5232599 := bstep (se 1 (by rfl) ⟨3924449, by rfl⟩ : syracuseStep 5232599 = 7848899) B7848899
theorem B4970497 : Blo 1032607 4970497 := bstep (se 2 (by rfl) ⟨1863936, by rfl⟩ : syracuseStep 4970497 = 3727873) B3727873
theorem B14899211 : Blo 1032607 14899211 := bstep (se 1 (by rfl) ⟨11174408, by rfl⟩ : syracuseStep 14899211 = 22348817) B22348817
theorem B8378731 : Blo 1032607 8378731 := bstep (se 1 (by rfl) ⟨6284048, by rfl⟩ : syracuseStep 8378731 = 12568097) B12568097
theorem B5233085 : Blo 1032607 5233085 := bstep (se 3 (by rfl) ⟨981203, by rfl⟩ : syracuseStep 5233085 = 1962407) B1962407
theorem B26532683 : Blo 1032607 26532683 := bstep (se 1 (by rfl) ⟨19899512, by rfl⟩ : syracuseStep 26532683 = 39799025) B39799025
theorem B7461857 : Blo 1032607 7461857 := bstep (se 2 (by rfl) ⟨2798196, by rfl⟩ : syracuseStep 7461857 = 5596393) B5596393
theorem B4414445 : Blo 1032607 4414445 := bstep (se 3 (by rfl) ⟨827708, by rfl⟩ : syracuseStep 4414445 = 1655417) B1655417
theorem B3726461 : Blo 1032607 3726461 := bstep (se 3 (by rfl) ⟨698711, by rfl⟩ : syracuseStep 3726461 = 1397423) B1397423
theorem B3497255 : Blo 1032607 3497255 := bstep (se 1 (by rfl) ⟨2622941, by rfl⟩ : syracuseStep 3497255 = 5245883) B5245883
theorem B7462205 : Blo 1032607 7462205 := bstep (se 3 (by rfl) ⟨1399163, by rfl⟩ : syracuseStep 7462205 = 2798327) B2798327
theorem B6381359 : Blo 1032607 6381359 := bstep (se 1 (by rfl) ⟨4786019, by rfl⟩ : syracuseStep 6381359 = 9572039) B9572039
theorem B3498119 : Blo 1032607 3498119 := bstep (se 1 (by rfl) ⟨2623589, by rfl⟩ : syracuseStep 3498119 = 5247179) B5247179
theorem B1106383 : Blo 1032607 1106383 := bstep (se 1 (by rfl) ⟨829787, by rfl⟩ : syracuseStep 1106383 = 1659575) B1659575
theorem B4973033 : Blo 1032607 4973033 := bstep (se 2 (by rfl) ⟨1864887, by rfl⟩ : syracuseStep 4973033 = 3729775) B3729775
theorem B28271213 : Blo 1032607 28271213 := bstep (se 3 (by rfl) ⟨5300852, by rfl⟩ : syracuseStep 28271213 = 10601705) B10601705
theorem B31810157 : Blo 1032607 31810157 := bstep (se 3 (by rfl) ⟨5964404, by rfl⟩ : syracuseStep 31810157 = 11928809) B11928809
theorem B39838391 : Blo 1032607 39838391 := bstep (se 1 (by rfl) ⟨29878793, by rfl⟩ : syracuseStep 39838391 = 59757587) B59757587
theorem B19882907 : Blo 1032607 19882907 := bstep (se 1 (by rfl) ⟨14912180, by rfl⟩ : syracuseStep 19882907 = 29824361) B29824361
theorem B7071113 : Blo 1032607 7071113 := bstep (se 2 (by rfl) ⟨2651667, by rfl⟩ : syracuseStep 7071113 = 5303335) B5303335
theorem B38299325 : Blo 1032607 38299325 := bstep (se 3 (by rfl) ⟨7181123, by rfl⟩ : syracuseStep 38299325 = 14362247) B14362247
theorem B5236487 : Blo 1032607 5236487 := bstep (se 1 (by rfl) ⟨3927365, by rfl⟩ : syracuseStep 5236487 = 7854731) B7854731
theorem B2615287 : Blo 1032607 2615287 := bstep (se 1 (by rfl) ⟨1961465, by rfl⟩ : syracuseStep 2615287 = 3922931) B3922931
theorem B3533095 : Blo 1032607 3533095 := bstep (se 1 (by rfl) ⟨2649821, by rfl⟩ : syracuseStep 3533095 = 5299643) B5299643
theorem B2615591 : Blo 1032607 2615591 := bstep (se 1 (by rfl) ⟨1961693, by rfl⟩ : syracuseStep 2615591 = 3923387) B3923387
theorem B50981363 : Blo 1032607 50981363 := bstep (se 1 (by rfl) ⟨38236022, by rfl⟩ : syracuseStep 50981363 = 76472045) B76472045
theorem B7072865 : Blo 1032607 7072865 := bstep (se 2 (by rfl) ⟨2652324, by rfl⟩ : syracuseStep 7072865 = 5304649) B5304649
theorem B2616745 : Blo 1032607 2616745 := bstep (se 2 (by rfl) ⟨981279, by rfl⟩ : syracuseStep 2616745 = 1962559) B1962559
theorem B2944637 : Blo 1032607 2944637 := bstep (se 3 (by rfl) ⟨552119, by rfl⟩ : syracuseStep 2944637 = 1104239) B1104239
theorem B2617231 : Blo 1032607 2617231 := bstep (se 1 (by rfl) ⟨1962923, by rfl⟩ : syracuseStep 2617231 = 3925847) B3925847
theorem B2486171 : Blo 1032607 2486171 := bstep (se 1 (by rfl) ⟨1864628, by rfl⟩ : syracuseStep 2486171 = 3729257) B3729257
theorem B1994719 : Blo 1032607 1994719 := bstep (se 1 (by rfl) ⟨1496039, by rfl⟩ : syracuseStep 1994719 = 2992079) B2992079
theorem B2650099 : Blo 1032607 2650099 := bstep (se 1 (by rfl) ⟨1987574, by rfl⟩ : syracuseStep 2650099 = 3975149) B3975149
theorem B7467137 : Blo 1032607 7467137 := bstep (se 2 (by rfl) ⟨2800176, by rfl⟩ : syracuseStep 7467137 = 5600353) B5600353
theorem B9925001 : Blo 1032607 9925001 := bstep (se 2 (by rfl) ⟨3721875, by rfl⟩ : syracuseStep 9925001 = 7443751) B7443751
theorem B1962377 : Blo 1032607 1962377 := bstep (se 2 (by rfl) ⟨735891, by rfl⟩ : syracuseStep 1962377 = 1471783) B1471783
theorem B2945639 : Blo 1032607 2945639 := bstep (se 1 (by rfl) ⟨2209229, by rfl⟩ : syracuseStep 2945639 = 4418459) B4418459
theorem B2618153 : Blo 1032607 2618153 := bstep (se 2 (by rfl) ⟨981807, by rfl⟩ : syracuseStep 2618153 = 1963615) B1963615
theorem B1864615 : Blo 1032607 1864615 := bstep (se 1 (by rfl) ⟨1398461, by rfl⟩ : syracuseStep 1864615 = 2796923) B2796923
theorem B2323511 : Blo 1032607 2323511 := bstep (se 1 (by rfl) ⟨1742633, by rfl⟩ : syracuseStep 2323511 = 3485267) B3485267
theorem B2323529 : Blo 1032607 2323529 := bstep (se 2 (by rfl) ⟨871323, by rfl⟩ : syracuseStep 2323529 = 1742647) B1742647
theorem B1307755 : Blo 1032607 1307755 := bstep (se 1 (by rfl) ⟨980816, by rfl⟩ : syracuseStep 1307755 = 1961633) B1961633
theorem B8516723 : Blo 1032607 8516723 := bstep (se 1 (by rfl) ⟨6387542, by rfl⟩ : syracuseStep 8516723 = 12775085) B12775085
theorem B4420747 : Blo 1032607 4420747 := bstep (se 1 (by rfl) ⟨3315560, by rfl⟩ : syracuseStep 4420747 = 6631121) B6631121
theorem B5043923 : Blo 1032607 5043923 := bstep (se 1 (by rfl) ⟨3782942, by rfl⟩ : syracuseStep 5043923 = 7565885) B7565885
theorem B5175035 : Blo 1032607 5175035 := bstep (se 1 (by rfl) ⟨3881276, by rfl⟩ : syracuseStep 5175035 = 7762553) B7762553
theorem B3929903 : Blo 1032607 3929903 := bstep (se 1 (by rfl) ⟨2947427, by rfl⟩ : syracuseStep 3929903 = 5894855) B5894855
theorem B1472455 : Blo 1032607 1472455 := bstep (se 1 (by rfl) ⟨1104341, by rfl⟩ : syracuseStep 1472455 = 2208683) B2208683
theorem B2947097 : Blo 1032607 2947097 := bstep (se 2 (by rfl) ⟨1105161, by rfl⟩ : syracuseStep 2947097 = 2210323) B2210323
theorem B4192787 : Blo 1032607 4192787 := bstep (se 1 (by rfl) ⟨3144590, by rfl⟩ : syracuseStep 4192787 = 6289181) B6289181
theorem B1964891 : Blo 1032607 1964891 := bstep (se 1 (by rfl) ⟨1473668, by rfl⟩ : syracuseStep 1964891 = 2947337) B2947337
theorem B16120711 : Blo 1032607 16120711 := bstep (se 1 (by rfl) ⟨12090533, by rfl⟩ : syracuseStep 16120711 = 24181067) B24181067
theorem B2325455 : Blo 1032607 2325455 := bstep (se 1 (by rfl) ⟨1744091, by rfl⟩ : syracuseStep 2325455 = 3488183) B3488183
theorem B2325473 : Blo 1032607 2325473 := bstep (se 2 (by rfl) ⟨872052, by rfl⟩ : syracuseStep 2325473 = 1744105) B1744105
theorem B2325545 : Blo 1032607 2325545 := bstep (se 2 (by rfl) ⟨872079, by rfl⟩ : syracuseStep 2325545 = 1744159) B1744159
theorem B2948167 : Blo 1032607 2948167 := bstep (se 1 (by rfl) ⟨2211125, by rfl⟩ : syracuseStep 2948167 = 4422251) B4422251
theorem B1473719 : Blo 1032607 1473719 := bstep (se 1 (by rfl) ⟨1105289, by rfl⟩ : syracuseStep 1473719 = 2210579) B2210579
theorem B7863479 : Blo 1032607 7863479 := bstep (se 1 (by rfl) ⟨5897609, by rfl⟩ : syracuseStep 7863479 = 11795219) B11795219
theorem B1866935 : Blo 1032607 1866935 := bstep (se 1 (by rfl) ⟨1400201, by rfl⟩ : syracuseStep 1866935 = 2800403) B2800403
theorem B2948795 : Blo 1032607 2948795 := bstep (se 1 (by rfl) ⟨2211596, by rfl⟩ : syracuseStep 2948795 = 4423193) B4423193
theorem B22675211 : Blo 1032607 22675211 := bstep (se 1 (by rfl) ⟨17006408, by rfl⟩ : syracuseStep 22675211 = 34012817) B34012817
theorem B2948987 : Blo 1032607 2948987 := bstep (se 1 (by rfl) ⟨2211740, by rfl⟩ : syracuseStep 2948987 = 4423481) B4423481
theorem B3309437 : Blo 1032607 3309437 := bstep (se 3 (by rfl) ⟨620519, by rfl⟩ : syracuseStep 3309437 = 1241039) B1241039
theorem B8192033 : Blo 1032607 8192033 := bstep (se 2 (by rfl) ⟨3072012, by rfl⟩ : syracuseStep 8192033 = 6144025) B6144025
theorem B2326715 : Blo 1032607 2326715 := bstep (se 1 (by rfl) ⟨1745036, by rfl⟩ : syracuseStep 2326715 = 3490073) B3490073
theorem B3932347 : Blo 1032607 3932347 := bstep (se 1 (by rfl) ⟨2949260, by rfl⟩ : syracuseStep 3932347 = 5898521) B5898521
theorem B2326823 : Blo 1032607 2326823 := bstep (se 1 (by rfl) ⟨1745117, by rfl⟩ : syracuseStep 2326823 = 3490235) B3490235
theorem B7864937 : Blo 1032607 7864937 := bstep (se 2 (by rfl) ⟨2949351, by rfl⟩ : syracuseStep 7864937 = 5898703) B5898703
theorem B1475177 : Blo 1032607 1475177 := bstep (se 2 (by rfl) ⟨553191, by rfl⟩ : syracuseStep 1475177 = 1106383) B1106383
theorem B2327201 : Blo 1032607 2327201 := bstep (se 2 (by rfl) ⟨872700, by rfl⟩ : syracuseStep 2327201 = 1745401) B1745401
theorem B2360315 : Blo 1032607 2360315 := bstep (se 1 (by rfl) ⟨1770236, by rfl⟩ : syracuseStep 2360315 = 3540473) B3540473
theorem B2327561 : Blo 1032607 2327561 := bstep (se 2 (by rfl) ⟨872835, by rfl⟩ : syracuseStep 2327561 = 1745671) B1745671
theorem B2327615 : Blo 1032607 2327615 := bstep (se 1 (by rfl) ⟨1745711, by rfl⟩ : syracuseStep 2327615 = 3491423) B3491423
theorem B2622527 : Blo 1032607 2622527 := bstep (se 1 (by rfl) ⟨1966895, by rfl⟩ : syracuseStep 2622527 = 3933791) B3933791
theorem B6292637 : Blo 1032607 6292637 := bstep (se 3 (by rfl) ⟨1179869, by rfl⟩ : syracuseStep 6292637 = 2359739) B2359739
theorem B1967647 : Blo 1032607 1967647 := bstep (se 1 (by rfl) ⟨1475735, by rfl⟩ : syracuseStep 1967647 = 2951471) B2951471
theorem B1967723 : Blo 1032607 1967723 := bstep (se 1 (by rfl) ⟨1475792, by rfl⟩ : syracuseStep 1967723 = 2951585) B2951585
theorem B1967807 : Blo 1032607 1967807 := bstep (se 1 (by rfl) ⟨1475855, by rfl⟩ : syracuseStep 1967807 = 2951711) B2951711
theorem B2328551 : Blo 1032607 2328551 := bstep (se 1 (by rfl) ⟨1746413, by rfl⟩ : syracuseStep 2328551 = 3492827) B3492827
theorem B2328731 : Blo 1032607 2328731 := bstep (se 1 (by rfl) ⟨1746548, by rfl⟩ : syracuseStep 2328731 = 3493097) B3493097
theorem B2623711 : Blo 1032607 2623711 := bstep (se 1 (by rfl) ⟨1967783, by rfl⟩ : syracuseStep 2623711 = 3935567) B3935567
theorem B2328911 : Blo 1032607 2328911 := bstep (se 1 (by rfl) ⟨1746683, by rfl⟩ : syracuseStep 2328911 = 3493367) B3493367
theorem B3311999 : Blo 1032607 3311999 := bstep (se 1 (by rfl) ⟨2483999, by rfl⟩ : syracuseStep 3311999 = 4967999) B4967999
theorem B2329001 : Blo 1032607 2329001 := bstep (se 2 (by rfl) ⟨873375, by rfl⟩ : syracuseStep 2329001 = 1746751) B1746751
theorem B7866881 : Blo 1032607 7866881 := bstep (se 2 (by rfl) ⟨2950080, by rfl⟩ : syracuseStep 7866881 = 5900161) B5900161
theorem B8849969 : Blo 1032607 8849969 := bstep (se 2 (by rfl) ⟨3318738, by rfl⟩ : syracuseStep 8849969 = 6637477) B6637477
theorem B4197203 : Blo 1032607 4197203 := bstep (se 1 (by rfl) ⟨3147902, by rfl⟩ : syracuseStep 4197203 = 6295805) B6295805
theorem B22711261 : Blo 1032607 22711261 := bstep (se 3 (by rfl) ⟨4258361, by rfl⟩ : syracuseStep 22711261 = 8516723) B8516723
theorem B2329595 : Blo 1032607 2329595 := bstep (se 1 (by rfl) ⟨1747196, by rfl⟩ : syracuseStep 2329595 = 3494393) B3494393
theorem B1772651 : Blo 1032607 1772651 := bstep (se 1 (by rfl) ⟨1329488, by rfl⟩ : syracuseStep 1772651 = 2658977) B2658977
theorem B2329775 : Blo 1032607 2329775 := bstep (se 1 (by rfl) ⟨1747331, by rfl⟩ : syracuseStep 2329775 = 3494663) B3494663
theorem B2329811 : Blo 1032607 2329811 := bstep (se 1 (by rfl) ⟨1747358, by rfl⟩ : syracuseStep 2329811 = 3494717) B3494717
theorem B4426967 : Blo 1032607 4426967 := bstep (se 1 (by rfl) ⟨3320225, by rfl⟩ : syracuseStep 4426967 = 6640451) B6640451
theorem B18910597 : Blo 1032607 18910597 := bstep (se 4 (by rfl) ⟨1772868, by rfl⟩ : syracuseStep 18910597 = 3545737) B3545737
theorem B2330081 : Blo 1032607 2330081 := bstep (se 2 (by rfl) ⟨873780, by rfl⟩ : syracuseStep 2330081 = 1747561) B1747561
theorem B26480195 : Blo 1032607 26480195 := bstep (se 1 (by rfl) ⟨19860146, by rfl⟩ : syracuseStep 26480195 = 39720293) B39720293
theorem B7769843 : Blo 1032607 7769843 := bstep (se 1 (by rfl) ⟨5827382, by rfl⟩ : syracuseStep 7769843 = 11654765) B11654765
theorem B2330495 : Blo 1032607 2330495 := bstep (se 1 (by rfl) ⟨1747871, by rfl⟩ : syracuseStep 2330495 = 3495743) B3495743
theorem B9932807 : Blo 1032607 9932807 := bstep (se 1 (by rfl) ⟨7449605, by rfl⟩ : syracuseStep 9932807 = 14899211) B14899211
theorem B2691175 : Blo 1032607 2691175 := bstep (se 1 (by rfl) ⟨2018381, by rfl⟩ : syracuseStep 2691175 = 4036763) B4036763
theorem B2331449 : Blo 1032607 2331449 := bstep (se 2 (by rfl) ⟨874293, by rfl⟩ : syracuseStep 2331449 = 1748587) B1748587
theorem B2331503 : Blo 1032607 2331503 := bstep (se 1 (by rfl) ⟨1748627, by rfl⟩ : syracuseStep 2331503 = 3497255) B3497255
theorem B2331809 : Blo 1032607 2331809 := bstep (se 2 (by rfl) ⟨874428, by rfl⟩ : syracuseStep 2331809 = 1748857) B1748857
theorem B2659625 : Blo 1032607 2659625 := bstep (se 2 (by rfl) ⟨997359, by rfl⟩ : syracuseStep 2659625 = 1994719) B1994719
theorem B5969213 : Blo 1032607 5969213 := bstep (se 3 (by rfl) ⟨1119227, by rfl⟩ : syracuseStep 5969213 = 2238455) B2238455
theorem B2332079 : Blo 1032607 2332079 := bstep (se 1 (by rfl) ⟨1749059, by rfl⟩ : syracuseStep 2332079 = 3498119) B3498119
theorem B18847475 : Blo 1032607 18847475 := bstep (se 1 (by rfl) ⟨14135606, by rfl⟩ : syracuseStep 18847475 = 28271213) B28271213
theorem B21206771 : Blo 1032607 21206771 := bstep (se 1 (by rfl) ⟨15905078, by rfl⟩ : syracuseStep 21206771 = 31810157) B31810157
theorem B40245893 : Blo 1032607 40245893 := bstep (se 4 (by rfl) ⟨3773052, by rfl⟩ : syracuseStep 40245893 = 7546105) B7546105
theorem B17701577 : Blo 1032607 17701577 := bstep (se 2 (by rfl) ⟨6638091, by rfl⟩ : syracuseStep 17701577 = 13276183) B13276183
theorem B5970685 : Blo 1032607 5970685 := bstep (se 3 (by rfl) ⟨1119503, by rfl⟩ : syracuseStep 5970685 = 2239007) B2239007
theorem B7871255 : Blo 1032607 7871255 := bstep (se 1 (by rfl) ⟨5903441, by rfl⟩ : syracuseStep 7871255 = 11806883) B11806883
theorem B1743673 : Blo 1032607 1743673 := bstep (se 2 (by rfl) ⟨653877, by rfl⟩ : syracuseStep 1743673 = 1307755) B1307755
theorem B1743727 : Blo 1032607 1743727 := bstep (se 1 (by rfl) ⟨1307795, by rfl⟩ : syracuseStep 1743727 = 2615591) B2615591
theorem B33987575 : Blo 1032607 33987575 := bstep (se 1 (by rfl) ⟨25490681, by rfl⟩ : syracuseStep 33987575 = 50981363) B50981363
theorem B6627329 : Blo 1032607 6627329 := bstep (se 2 (by rfl) ⟨2485248, by rfl⟩ : syracuseStep 6627329 = 4970497) B4970497
theorem B1745435 : Blo 1032607 1745435 := bstep (se 1 (by rfl) ⟨1309076, by rfl⟩ : syracuseStep 1745435 = 2618153) B2618153
theorem B6300223 : Blo 1032607 6300223 := bstep (se 1 (by rfl) ⟨4725167, by rfl⟩ : syracuseStep 6300223 = 9450335) B9450335
theorem B1549007 : Blo 1032607 1549007 := bstep (se 1 (by rfl) ⟨1161755, by rfl⟩ : syracuseStep 1549007 = 2323511) B2323511
theorem B1549019 : Blo 1032607 1549019 := bstep (se 1 (by rfl) ⟨1161764, by rfl⟩ : syracuseStep 1549019 = 2323529) B2323529
theorem B1549433 : Blo 1032607 1549433 := bstep (se 2 (by rfl) ⟨581037, by rfl⟩ : syracuseStep 1549433 = 1162075) B1162075
theorem B3450023 : Blo 1032607 3450023 := bstep (se 1 (by rfl) ⟨2587517, by rfl⟩ : syracuseStep 3450023 = 5175035) B5175035
theorem B2795191 : Blo 1032607 2795191 := bstep (se 1 (by rfl) ⟨2096393, by rfl⟩ : syracuseStep 2795191 = 4192787) B4192787
theorem B7841609 : Blo 1032607 7841609 := bstep (se 2 (by rfl) ⟨2940603, by rfl⟩ : syracuseStep 7841609 = 5881207) B5881207
theorem B1550303 : Blo 1032607 1550303 := bstep (se 1 (by rfl) ⟨1162727, by rfl⟩ : syracuseStep 1550303 = 2325455) B2325455
theorem B1550315 : Blo 1032607 1550315 := bstep (se 1 (by rfl) ⟨1162736, by rfl⟩ : syracuseStep 1550315 = 2325473) B2325473
theorem B1550363 : Blo 1032607 1550363 := bstep (se 1 (by rfl) ⟨1162772, by rfl⟩ : syracuseStep 1550363 = 2325545) B2325545
theorem B1550729 : Blo 1032607 1550729 := bstep (se 2 (by rfl) ⟨581523, by rfl⟩ : syracuseStep 1550729 = 1163047) B1163047
theorem B6629789 : Blo 1032607 6629789 := bstep (se 3 (by rfl) ⟨1243085, by rfl⟩ : syracuseStep 6629789 = 2486171) B2486171
theorem B15116807 : Blo 1032607 15116807 := bstep (se 1 (by rfl) ⟨11337605, by rfl⟩ : syracuseStep 15116807 = 22675211) B22675211
theorem B2206291 : Blo 1032607 2206291 := bstep (se 1 (by rfl) ⟨1654718, by rfl⟩ : syracuseStep 2206291 = 3309437) B3309437
theorem B5319431 : Blo 1032607 5319431 := bstep (se 1 (by rfl) ⟨3989573, by rfl⟩ : syracuseStep 5319431 = 7979147) B7979147
theorem B1551671 : Blo 1032607 1551671 := bstep (se 1 (by rfl) ⟨1163753, by rfl⟩ : syracuseStep 1551671 = 2327507) B2327507
theorem B1551839 : Blo 1032607 1551839 := bstep (se 1 (by rfl) ⟨1163879, by rfl⟩ : syracuseStep 1551839 = 2327759) B2327759
theorem B1552055 : Blo 1032607 1552055 := bstep (se 1 (by rfl) ⟨1164041, by rfl⟩ : syracuseStep 1552055 = 2328083) B2328083
theorem B1552265 : Blo 1032607 1552265 := bstep (se 2 (by rfl) ⟨582099, by rfl⟩ : syracuseStep 1552265 = 1164199) B1164199
theorem B1552511 : Blo 1032607 1552511 := bstep (se 1 (by rfl) ⟨1164383, by rfl⟩ : syracuseStep 1552511 = 2328767) B2328767
theorem B14332069 : Blo 1032607 14332069 := bstep (se 4 (by rfl) ⟨1343631, by rfl⟩ : syracuseStep 14332069 = 2687263) B2687263
theorem B1553147 : Blo 1032607 1553147 := bstep (se 1 (by rfl) ⟨1164860, by rfl⟩ : syracuseStep 1553147 = 2329721) B2329721
theorem B2208521 : Blo 1032607 2208521 := bstep (se 2 (by rfl) ⟨828195, by rfl⟩ : syracuseStep 2208521 = 1656391) B1656391
theorem B3486671 : Blo 1032607 3486671 := bstep (se 1 (by rfl) ⟨2615003, by rfl⟩ : syracuseStep 3486671 = 5230007) B5230007
theorem B10630153 : Blo 1032607 10630153 := bstep (se 2 (by rfl) ⟨3986307, by rfl⟩ : syracuseStep 10630153 = 7972615) B7972615
theorem B3486779 : Blo 1032607 3486779 := bstep (se 1 (by rfl) ⟨2615084, by rfl⟩ : syracuseStep 3486779 = 5230169) B5230169
theorem B1553591 : Blo 1032607 1553591 := bstep (se 1 (by rfl) ⟨1165193, by rfl⟩ : syracuseStep 1553591 = 2330387) B2330387
theorem B3487049 : Blo 1032607 3487049 := bstep (se 2 (by rfl) ⟨1307643, by rfl⟩ : syracuseStep 3487049 = 2615287) B2615287
theorem B1553831 : Blo 1032607 1553831 := bstep (se 1 (by rfl) ⟨1165373, by rfl⟩ : syracuseStep 1553831 = 2330747) B2330747
theorem B1554011 : Blo 1032607 1554011 := bstep (se 1 (by rfl) ⟨1165508, by rfl⟩ : syracuseStep 1554011 = 2331017) B2331017
theorem B2799343 : Blo 1032607 2799343 := bstep (se 1 (by rfl) ⟨2099507, by rfl⟩ : syracuseStep 2799343 = 4199015) B4199015
theorem B1554473 : Blo 1032607 1554473 := bstep (se 2 (by rfl) ⟨582927, by rfl⟩ : syracuseStep 1554473 = 1165855) B1165855
theorem B18856007 : Blo 1032607 18856007 := bstep (se 1 (by rfl) ⟨14142005, by rfl⟩ : syracuseStep 18856007 = 28284011) B28284011
theorem B1554503 : Blo 1032607 1554503 := bstep (se 1 (by rfl) ⟨1165877, by rfl⟩ : syracuseStep 1554503 = 2331755) B2331755
theorem B1554887 : Blo 1032607 1554887 := bstep (se 1 (by rfl) ⟨1166165, by rfl⟩ : syracuseStep 1554887 = 2332331) B2332331
theorem B3488399 : Blo 1032607 3488399 := bstep (se 1 (by rfl) ⟨2616299, by rfl⟩ : syracuseStep 3488399 = 5232599) B5232599
theorem B38255449 : Blo 1032607 38255449 := bstep (se 2 (by rfl) ⟨14345793, by rfl⟩ : syracuseStep 38255449 = 28691587) B28691587
theorem B3488723 : Blo 1032607 3488723 := bstep (se 1 (by rfl) ⟨2616542, by rfl⟩ : syracuseStep 3488723 = 5233085) B5233085
theorem B3488993 : Blo 1032607 3488993 := bstep (se 2 (by rfl) ⟨1308372, by rfl⟩ : syracuseStep 3488993 = 2616745) B2616745
theorem B1162471 : Blo 1032607 1162471 := bstep (se 1 (by rfl) ⟨871853, by rfl⟩ : syracuseStep 1162471 = 1743707) B1743707
theorem B7978409 : Blo 1032607 7978409 := bstep (se 2 (by rfl) ⟨2991903, by rfl⟩ : syracuseStep 7978409 = 5983807) B5983807
theorem B2211391 : Blo 1032607 2211391 := bstep (se 1 (by rfl) ⟨1658543, by rfl⟩ : syracuseStep 2211391 = 3317087) B3317087
theorem B3489641 : Blo 1032607 3489641 := bstep (se 2 (by rfl) ⟨1308615, by rfl⟩ : syracuseStep 3489641 = 2617231) B2617231
theorem B1163119 : Blo 1032607 1163119 := bstep (se 1 (by rfl) ⟨872339, by rfl⟩ : syracuseStep 1163119 = 1744679) B1744679
theorem B26558927 : Blo 1032607 26558927 := bstep (se 1 (by rfl) ⟨19919195, by rfl⟩ : syracuseStep 26558927 = 39838391) B39838391
theorem B1032731 : Blo 1032607 1032731 := bstep (se 1 (by rfl) ⟨774548, by rfl⟩ : syracuseStep 1032731 = 1549097) B1549097
theorem B1163803 : Blo 1032607 1163803 := bstep (se 1 (by rfl) ⟨872852, by rfl⟩ : syracuseStep 1163803 = 1745705) B1745705
theorem B1032735 : Blo 1032607 1032735 := bstep (se 1 (by rfl) ⟨774551, by rfl⟩ : syracuseStep 1032735 = 1549103) B1549103
theorem B13255271 : Blo 1032607 13255271 := bstep (se 1 (by rfl) ⟨9941453, by rfl⟩ : syracuseStep 13255271 = 19882907) B19882907
theorem B1032815 : Blo 1032607 1032815 := bstep (se 1 (by rfl) ⟨774611, by rfl⟩ : syracuseStep 1032815 = 1549223) B1549223
theorem B5882483 : Blo 1032607 5882483 := bstep (se 1 (by rfl) ⟨4411862, by rfl⟩ : syracuseStep 5882483 = 8823725) B8823725
theorem B1032871 : Blo 1032607 1032871 := bstep (se 1 (by rfl) ⟨774653, by rfl⟩ : syracuseStep 1032871 = 1549307) B1549307
theorem B1032911 : Blo 1032607 1032911 := bstep (se 1 (by rfl) ⟨774683, by rfl⟩ : syracuseStep 1032911 = 1549367) B1549367
theorem B1163983 : Blo 1032607 1163983 := bstep (se 1 (by rfl) ⟨872987, by rfl⟩ : syracuseStep 1163983 = 1745975) B1745975
theorem B1032991 : Blo 1032607 1032991 := bstep (se 1 (by rfl) ⟨774743, by rfl⟩ : syracuseStep 1032991 = 1549487) B1549487
theorem B5882665 : Blo 1032607 5882665 := bstep (se 2 (by rfl) ⟨2205999, by rfl⟩ : syracuseStep 5882665 = 4411999) B4411999
theorem B1033263 : Blo 1032607 1033263 := bstep (se 1 (by rfl) ⟨774947, by rfl⟩ : syracuseStep 1033263 = 1549895) B1549895
theorem B1033327 : Blo 1032607 1033327 := bstep (se 1 (by rfl) ⟨774995, by rfl⟩ : syracuseStep 1033327 = 1549991) B1549991
theorem B1033383 : Blo 1032607 1033383 := bstep (se 1 (by rfl) ⟨775037, by rfl⟩ : syracuseStep 1033383 = 1550075) B1550075
theorem B3490991 : Blo 1032607 3490991 := bstep (se 1 (by rfl) ⟨2618243, by rfl⟩ : syracuseStep 3490991 = 5236487) B5236487
theorem B2213039 : Blo 1032607 2213039 := bstep (se 1 (by rfl) ⟨1659779, by rfl⟩ : syracuseStep 2213039 = 3319559) B3319559
theorem B1033407 : Blo 1032607 1033407 := bstep (se 1 (by rfl) ⟨775055, by rfl⟩ : syracuseStep 1033407 = 1550111) B1550111
theorem B1033439 : Blo 1032607 1033439 := bstep (se 1 (by rfl) ⟨775079, by rfl⟩ : syracuseStep 1033439 = 1550159) B1550159
theorem B1033519 : Blo 1032607 1033519 := bstep (se 1 (by rfl) ⟨775139, by rfl⟩ : syracuseStep 1033519 = 1550279) B1550279
theorem B7849385 : Blo 1032607 7849385 := bstep (se 2 (by rfl) ⟨2943519, by rfl⟩ : syracuseStep 7849385 = 5887039) B5887039
theorem B1033755 : Blo 1032607 1033755 := bstep (se 1 (by rfl) ⟨775316, by rfl⟩ : syracuseStep 1033755 = 1550633) B1550633
theorem B1033759 : Blo 1032607 1033759 := bstep (se 1 (by rfl) ⟨775319, by rfl⟩ : syracuseStep 1033759 = 1550639) B1550639
theorem B32720525 : Blo 1032607 32720525 := bstep (se 3 (by rfl) ⟨6135098, by rfl⟩ : syracuseStep 32720525 = 12270197) B12270197
theorem B1033919 : Blo 1032607 1033919 := bstep (se 1 (by rfl) ⟨775439, by rfl⟩ : syracuseStep 1033919 = 1550879) B1550879
theorem B1164991 : Blo 1032607 1164991 := bstep (se 1 (by rfl) ⟨873743, by rfl⟩ : syracuseStep 1164991 = 1747487) B1747487
theorem B1034175 : Blo 1032607 1034175 := bstep (se 1 (by rfl) ⟨775631, by rfl⟩ : syracuseStep 1034175 = 1551263) B1551263
theorem B1034207 : Blo 1032607 1034207 := bstep (se 1 (by rfl) ⟨775655, by rfl⟩ : syracuseStep 1034207 = 1551311) B1551311
theorem B1165279 : Blo 1032607 1165279 := bstep (se 1 (by rfl) ⟨873959, by rfl⟩ : syracuseStep 1165279 = 1747919) B1747919
theorem B1034267 : Blo 1032607 1034267 := bstep (se 1 (by rfl) ⟨775700, by rfl⟩ : syracuseStep 1034267 = 1551401) B1551401
theorem B1034271 : Blo 1032607 1034271 := bstep (se 1 (by rfl) ⟨775703, by rfl⟩ : syracuseStep 1034271 = 1551407) B1551407
theorem B1034287 : Blo 1032607 1034287 := bstep (se 1 (by rfl) ⟨775715, by rfl⟩ : syracuseStep 1034287 = 1551431) B1551431
theorem B1034463 : Blo 1032607 1034463 := bstep (se 1 (by rfl) ⟨775847, by rfl⟩ : syracuseStep 1034463 = 1551695) B1551695
theorem B1034523 : Blo 1032607 1034523 := bstep (se 1 (by rfl) ⟨775892, by rfl⟩ : syracuseStep 1034523 = 1551785) B1551785
theorem B1886591 : Blo 1032607 1886591 := bstep (se 1 (by rfl) ⟨1414943, by rfl⟩ : syracuseStep 1886591 = 2829887) B2829887
theorem B1034623 : Blo 1032607 1034623 := bstep (se 1 (by rfl) ⟨775967, by rfl⟩ : syracuseStep 1034623 = 1551935) B1551935
theorem B1034799 : Blo 1032607 1034799 := bstep (se 1 (by rfl) ⟨776099, by rfl⟩ : syracuseStep 1034799 = 1552199) B1552199
theorem B1034855 : Blo 1032607 1034855 := bstep (se 1 (by rfl) ⟨776141, by rfl⟩ : syracuseStep 1034855 = 1552283) B1552283
theorem B1165927 : Blo 1032607 1165927 := bstep (se 1 (by rfl) ⟨874445, by rfl⟩ : syracuseStep 1165927 = 1748891) B1748891
theorem B7850843 : Blo 1032607 7850843 := bstep (se 1 (by rfl) ⟨5888132, by rfl⟩ : syracuseStep 7850843 = 11776265) B11776265
theorem B1035231 : Blo 1032607 1035231 := bstep (se 1 (by rfl) ⟨776423, by rfl⟩ : syracuseStep 1035231 = 1552847) B1552847
theorem B1035259 : Blo 1032607 1035259 := bstep (se 1 (by rfl) ⟨776444, by rfl⟩ : syracuseStep 1035259 = 1552889) B1552889
theorem B1035327 : Blo 1032607 1035327 := bstep (se 1 (by rfl) ⟨776495, by rfl⟩ : syracuseStep 1035327 = 1552991) B1552991
theorem B1035647 : Blo 1032607 1035647 := bstep (se 1 (by rfl) ⟨776735, by rfl⟩ : syracuseStep 1035647 = 1553471) B1553471
theorem B1035675 : Blo 1032607 1035675 := bstep (se 1 (by rfl) ⟨776756, by rfl⟩ : syracuseStep 1035675 = 1553513) B1553513
theorem B5885399 : Blo 1032607 5885399 := bstep (se 1 (by rfl) ⟨4414049, by rfl⟩ : syracuseStep 5885399 = 8828099) B8828099
theorem B1035743 : Blo 1032607 1035743 := bstep (se 1 (by rfl) ⟨776807, by rfl⟩ : syracuseStep 1035743 = 1553615) B1553615
theorem B3722855 : Blo 1032607 3722855 := bstep (se 1 (by rfl) ⟨2792141, by rfl⟩ : syracuseStep 3722855 = 5584283) B5584283
theorem B1035879 : Blo 1032607 1035879 := bstep (se 1 (by rfl) ⟨776909, by rfl⟩ : syracuseStep 1035879 = 1553819) B1553819
theorem B1036027 : Blo 1032607 1036027 := bstep (se 1 (by rfl) ⟨777020, by rfl⟩ : syracuseStep 1036027 = 1554041) B1554041
theorem B3362615 : Blo 1032607 3362615 := bstep (se 1 (by rfl) ⟨2521961, by rfl⟩ : syracuseStep 3362615 = 5043923) B5043923
theorem B1036095 : Blo 1032607 1036095 := bstep (se 1 (by rfl) ⟨777071, by rfl⟩ : syracuseStep 1036095 = 1554143) B1554143
theorem B1036159 : Blo 1032607 1036159 := bstep (se 1 (by rfl) ⟨777119, by rfl⟩ : syracuseStep 1036159 = 1554239) B1554239
theorem B25546711 : Blo 1032607 25546711 := bstep (se 1 (by rfl) ⟨19160033, by rfl⟩ : syracuseStep 25546711 = 38320067) B38320067
theorem B1036271 : Blo 1032607 1036271 := bstep (se 1 (by rfl) ⟨777203, by rfl⟩ : syracuseStep 1036271 = 1554407) B1554407
theorem B1036283 : Blo 1032607 1036283 := bstep (se 1 (by rfl) ⟨777212, by rfl⟩ : syracuseStep 1036283 = 1554425) B1554425
theorem B1036351 : Blo 1032607 1036351 := bstep (se 1 (by rfl) ⟨777263, by rfl⟩ : syracuseStep 1036351 = 1554527) B1554527
theorem B1036391 : Blo 1032607 1036391 := bstep (se 1 (by rfl) ⟨777293, by rfl⟩ : syracuseStep 1036391 = 1554587) B1554587
theorem B1036415 : Blo 1032607 1036415 := bstep (se 1 (by rfl) ⟨777311, by rfl⟩ : syracuseStep 1036415 = 1554623) B1554623
theorem B1036443 : Blo 1032607 1036443 := bstep (se 1 (by rfl) ⟨777332, by rfl⟩ : syracuseStep 1036443 = 1554665) B1554665
theorem B13258961 : Blo 1032607 13258961 := bstep (se 2 (by rfl) ⟨4972110, by rfl⟩ : syracuseStep 13258961 = 9944221) B9944221
theorem B1103167 : Blo 1032607 1103167 := bstep (se 1 (by rfl) ⟨827375, by rfl⟩ : syracuseStep 1103167 = 1654751) B1654751
theorem B9950987 : Blo 1032607 9950987 := bstep (se 1 (by rfl) ⟨7463240, by rfl⟩ : syracuseStep 9950987 = 14926481) B14926481
theorem B4970459 : Blo 1032607 4970459 := bstep (se 1 (by rfl) ⟨3727844, by rfl⟩ : syracuseStep 4970459 = 7455689) B7455689
theorem B3495905 : Blo 1032607 3495905 := bstep (se 2 (by rfl) ⟨1310964, by rfl⟩ : syracuseStep 3495905 = 2621929) B2621929
theorem B3921959 : Blo 1032607 3921959 := bstep (se 1 (by rfl) ⟨2941469, by rfl⟩ : syracuseStep 3921959 = 5882939) B5882939
theorem B29874419 : Blo 1032607 29874419 := bstep (se 1 (by rfl) ⟨22405814, by rfl⟩ : syracuseStep 29874419 = 44811629) B44811629
theorem B4250089 : Blo 1032607 4250089 := bstep (se 2 (by rfl) ⟨1593783, by rfl⟩ : syracuseStep 4250089 = 3187567) B3187567
theorem B13261421 : Blo 1032607 13261421 := bstep (se 3 (by rfl) ⟨2486516, by rfl⟩ : syracuseStep 13261421 = 4973033) B4973033
theorem B5593799 : Blo 1032607 5593799 := bstep (se 1 (by rfl) ⟨4195349, by rfl⟩ : syracuseStep 5593799 = 8390699) B8390699
theorem B13458797 : Blo 1032607 13458797 := bstep (se 3 (by rfl) ⟨2523524, by rfl⟩ : syracuseStep 13458797 = 5047049) B5047049
theorem B5594579 : Blo 1032607 5594579 := bstep (se 1 (by rfl) ⟨4195934, by rfl⟩ : syracuseStep 5594579 = 8391869) B8391869
theorem B4415143 : Blo 1032607 4415143 := bstep (se 1 (by rfl) ⟨3311357, by rfl⟩ : syracuseStep 4415143 = 6622715) B6622715
theorem B37773317 : Blo 1032607 37773317 := bstep (se 4 (by rfl) ⟨3541248, by rfl⟩ : syracuseStep 37773317 = 7082497) B7082497
theorem B4710793 : Blo 1032607 4710793 := bstep (se 2 (by rfl) ⟨1766547, by rfl⟩ : syracuseStep 4710793 = 3533095) B3533095
theorem B2482895 : Blo 1032607 2482895 := bstep (se 1 (by rfl) ⟨1862171, by rfl⟩ : syracuseStep 2482895 = 3724343) B3724343
theorem B4416443 : Blo 1032607 4416443 := bstep (se 1 (by rfl) ⟨3312332, by rfl⟩ : syracuseStep 4416443 = 6624665) B6624665
theorem B19850305 : Blo 1032607 19850305 := bstep (se 2 (by rfl) ⟨7443864, by rfl⟩ : syracuseStep 19850305 = 14887729) B14887729
theorem B102131533 : Blo 1032607 102131533 := bstep (se 3 (by rfl) ⟨19149662, by rfl⟩ : syracuseStep 102131533 = 38299325) B38299325
theorem B17688455 : Blo 1032607 17688455 := bstep (se 1 (by rfl) ⟨13266341, by rfl⟩ : syracuseStep 17688455 = 26532683) B26532683
theorem B4974571 : Blo 1032607 4974571 := bstep (se 1 (by rfl) ⟨3730928, by rfl⟩ : syracuseStep 4974571 = 7461857) B7461857
theorem B2942963 : Blo 1032607 2942963 := bstep (se 1 (by rfl) ⟨2207222, by rfl⟩ : syracuseStep 2942963 = 4414445) B4414445
theorem B2484307 : Blo 1032607 2484307 := bstep (se 1 (by rfl) ⟨1863230, by rfl⟩ : syracuseStep 2484307 = 3726461) B3726461
theorem B4974803 : Blo 1032607 4974803 := bstep (se 1 (by rfl) ⟨3731102, by rfl⟩ : syracuseStep 4974803 = 7462205) B7462205
theorem B17918297 : Blo 1032607 17918297 := bstep (se 2 (by rfl) ⟨6719361, by rfl⟩ : syracuseStep 17918297 = 13438723) B13438723
theorem B4254239 : Blo 1032607 4254239 := bstep (se 1 (by rfl) ⟨3190679, by rfl⟩ : syracuseStep 4254239 = 6381359) B6381359
theorem B3533465 : Blo 1032607 3533465 := bstep (se 2 (by rfl) ⟨1325049, by rfl⟩ : syracuseStep 3533465 = 2650099) B2650099
theorem B4419143 : Blo 1032607 4419143 := bstep (se 1 (by rfl) ⟨3314357, by rfl⟩ : syracuseStep 4419143 = 6628715) B6628715
theorem B4714075 : Blo 1032607 4714075 := bstep (se 1 (by rfl) ⟨3535556, by rfl⟩ : syracuseStep 4714075 = 7071113) B7071113
theorem B2486153 : Blo 1032607 2486153 := bstep (se 2 (by rfl) ⟨932307, by rfl⟩ : syracuseStep 2486153 = 1864615) B1864615
theorem B5894329 : Blo 1032607 5894329 := bstep (se 2 (by rfl) ⟨2210373, by rfl⟩ : syracuseStep 5894329 = 4420747) B4420747
theorem B4485401 : Blo 1032607 4485401 := bstep (se 2 (by rfl) ⟨1682025, by rfl⟩ : syracuseStep 4485401 = 3364051) B3364051
theorem B4715243 : Blo 1032607 4715243 := bstep (se 1 (by rfl) ⟨3536432, by rfl⟩ : syracuseStep 4715243 = 7072865) B7072865
theorem B2323367 : Blo 1032607 2323367 := bstep (se 1 (by rfl) ⟨1742525, by rfl⟩ : syracuseStep 2323367 = 3485051) B3485051
theorem B1963091 : Blo 1032607 1963091 := bstep (se 1 (by rfl) ⟨1472318, by rfl⟩ : syracuseStep 1963091 = 2944637) B2944637
theorem B4420817 : Blo 1032607 4420817 := bstep (se 2 (by rfl) ⟨1657806, by rfl⟩ : syracuseStep 4420817 = 3315613) B3315613
theorem B1963273 : Blo 1032607 1963273 := bstep (se 2 (by rfl) ⟨736227, by rfl⟩ : syracuseStep 1963273 = 1472455) B1472455
theorem B4978091 : Blo 1032607 4978091 := bstep (se 1 (by rfl) ⟨3733568, by rfl⟩ : syracuseStep 4978091 = 7467137) B7467137
theorem B6616667 : Blo 1032607 6616667 := bstep (se 1 (by rfl) ⟨4962500, by rfl⟩ : syracuseStep 6616667 = 9925001) B9925001
theorem B1308251 : Blo 1032607 1308251 := bstep (se 1 (by rfl) ⟨981188, by rfl⟩ : syracuseStep 1308251 = 1962377) B1962377
theorem B1963759 : Blo 1032607 1963759 := bstep (se 1 (by rfl) ⟨1472819, by rfl⟩ : syracuseStep 1963759 = 2945639) B2945639
theorem B11171641 : Blo 1032607 11171641 := bstep (se 2 (by rfl) ⟨4189365, by rfl⟩ : syracuseStep 11171641 = 8378731) B8378731
theorem B3929917 : Blo 1032607 3929917 := bstep (se 3 (by rfl) ⟨736859, by rfl⟩ : syracuseStep 3929917 = 1473719) B1473719
theorem B4978493 : Blo 1032607 4978493 := bstep (se 3 (by rfl) ⟨933467, by rfl⟩ : syracuseStep 4978493 = 1866935) B1866935
theorem B2324303 : Blo 1032607 2324303 := bstep (se 1 (by rfl) ⟨1743227, by rfl⟩ : syracuseStep 2324303 = 3486455) B3486455
theorem B2324663 : Blo 1032607 2324663 := bstep (se 1 (by rfl) ⟨1743497, by rfl⟩ : syracuseStep 2324663 = 3486995) B3486995
theorem B2947553 : Blo 1032607 2947553 := bstep (se 2 (by rfl) ⟨1105332, by rfl⟩ : syracuseStep 2947553 = 2210665) B2210665
theorem B21494281 : Blo 1032607 21494281 := bstep (se 2 (by rfl) ⟨8060355, by rfl⟩ : syracuseStep 21494281 = 16120711) B16120711
theorem B2325023 : Blo 1032607 2325023 := bstep (se 1 (by rfl) ⟨1743767, by rfl⟩ : syracuseStep 2325023 = 3487535) B3487535
theorem B2619935 : Blo 1032607 2619935 := bstep (se 1 (by rfl) ⟨1964951, by rfl⟩ : syracuseStep 2619935 = 3929903) B3929903
theorem B4422235 : Blo 1032607 4422235 := bstep (se 1 (by rfl) ⟨3316676, by rfl⟩ : syracuseStep 4422235 = 6633353) B6633353
theorem B1964731 : Blo 1032607 1964731 := bstep (se 1 (by rfl) ⟨1473548, by rfl⟩ : syracuseStep 1964731 = 2947097) B2947097
theorem B2325257 : Blo 1032607 2325257 := bstep (se 2 (by rfl) ⟨871971, by rfl⟩ : syracuseStep 2325257 = 1743943) B1743943
theorem B3930889 : Blo 1032607 3930889 := bstep (se 2 (by rfl) ⟨1474083, by rfl⟩ : syracuseStep 3930889 = 2948167) B2948167
theorem B4422509 : Blo 1032607 4422509 := bstep (se 3 (by rfl) ⟨829220, by rfl⟩ : syracuseStep 4422509 = 1658441) B1658441
theorem B4422559 : Blo 1032607 4422559 := bstep (se 1 (by rfl) ⟨3316919, by rfl⟩ : syracuseStep 4422559 = 6633839) B6633839
theorem B1309927 : Blo 1032607 1309927 := bstep (se 1 (by rfl) ⟨982445, by rfl⟩ : syracuseStep 1309927 = 1964891) B1964891
theorem B2325833 : Blo 1032607 2325833 := bstep (se 2 (by rfl) ⟨872187, by rfl⟩ : syracuseStep 2325833 = 1744375) B1744375
theorem B5242319 : Blo 1032607 5242319 := bstep (se 1 (by rfl) ⟨3931739, by rfl⟩ : syracuseStep 5242319 = 7863479) B7863479
theorem B2948737 : Blo 1032607 2948737 := bstep (se 2 (by rfl) ⟨1105776, by rfl⟩ : syracuseStep 2948737 = 2211553) B2211553
theorem B7863965 : Blo 1032607 7863965 := bstep (se 3 (by rfl) ⟨1474493, by rfl⟩ : syracuseStep 7863965 = 2948987) B2948987
theorem B2326247 : Blo 1032607 2326247 := bstep (se 1 (by rfl) ⟨1744685, by rfl⟩ : syracuseStep 2326247 = 3489371) B3489371
theorem B1965863 : Blo 1032607 1965863 := bstep (se 1 (by rfl) ⟨1474397, by rfl⟩ : syracuseStep 1965863 = 2948795) B2948795
theorem B1474471 : Blo 1032607 1474471 := bstep (se 1 (by rfl) ⟨1105853, by rfl⟩ : syracuseStep 1474471 = 2211707) B2211707
theorem B19103687 : Blo 1032607 19103687 := bstep (se 1 (by rfl) ⟨14327765, by rfl⟩ : syracuseStep 19103687 = 28655531) B28655531
theorem B5243129 : Blo 1032607 5243129 := bstep (se 2 (by rfl) ⟨1966173, by rfl⟩ : syracuseStep 5243129 = 3932347) B3932347
theorem B5243291 : Blo 1032607 5243291 := bstep (se 1 (by rfl) ⟨3932468, by rfl⟩ : syracuseStep 5243291 = 7864937) B7864937
theorem B1573543 : Blo 1032607 1573543 := bstep (se 1 (by rfl) ⟨1180157, by rfl⟩ : syracuseStep 1573543 = 2360315) B2360315
theorem B4195091 : Blo 1032607 4195091 := bstep (se 1 (by rfl) ⟨3146318, by rfl⟩ : syracuseStep 4195091 = 6292637) B6292637
theorem B2327327 : Blo 1032607 2327327 := bstep (se 1 (by rfl) ⟨1745495, by rfl⟩ : syracuseStep 2327327 = 3490991) B3490991
theorem B1311815 : Blo 1032607 1311815 := bstep (se 1 (by rfl) ⟨983861, by rfl⟩ : syracuseStep 1311815 = 1967723) B1967723
theorem B1311871 : Blo 1032607 1311871 := bstep (se 1 (by rfl) ⟨983903, by rfl⟩ : syracuseStep 1311871 = 1967807) B1967807
theorem B3933805 : Blo 1032607 3933805 := bstep (se 3 (by rfl) ⟨737588, by rfl⟩ : syracuseStep 3933805 = 1475177) B1475177
theorem B5244587 : Blo 1032607 5244587 := bstep (se 1 (by rfl) ⟨3933440, by rfl⟩ : syracuseStep 5244587 = 7866881) B7866881
theorem B5899979 : Blo 1032607 5899979 := bstep (se 1 (by rfl) ⟨4424984, by rfl⟩ : syracuseStep 5899979 = 8849969) B8849969
theorem B2623529 : Blo 1032607 2623529 := bstep (se 2 (by rfl) ⟨983823, by rfl⟩ : syracuseStep 2623529 = 1967647) B1967647
theorem B2951311 : Blo 1032607 2951311 := bstep (se 1 (by rfl) ⟨2213483, by rfl⟩ : syracuseStep 2951311 = 4426967) B4426967
theorem B5179895 : Blo 1032607 5179895 := bstep (se 1 (by rfl) ⟨3884921, by rfl⟩ : syracuseStep 5179895 = 7769843) B7769843
theorem B6621871 : Blo 1032607 6621871 := bstep (se 1 (by rfl) ⟨4966403, by rfl⟩ : syracuseStep 6621871 = 9932807) B9932807
theorem B3312409 : Blo 1032607 3312409 := bstep (se 2 (by rfl) ⟨1242153, by rfl⟩ : syracuseStep 3312409 = 2484307) B2484307
theorem B5901437 : Blo 1032607 5901437 := bstep (se 3 (by rfl) ⟨1106519, by rfl⟩ : syracuseStep 5901437 = 2213039) B2213039
theorem B1773083 : Blo 1032607 1773083 := bstep (se 1 (by rfl) ⟨1329812, by rfl⟩ : syracuseStep 1773083 = 2659625) B2659625
theorem B30281681 : Blo 1032607 30281681 := bstep (se 2 (by rfl) ⟨11355630, by rfl⟩ : syracuseStep 30281681 = 22711261) B22711261
theorem B3313639 : Blo 1032607 3313639 := bstep (se 1 (by rfl) ⟨2485229, by rfl⟩ : syracuseStep 3313639 = 4970459) B4970459
theorem B2330603 : Blo 1032607 2330603 := bstep (se 1 (by rfl) ⟨1747952, by rfl⟩ : syracuseStep 2330603 = 3495905) B3495905
theorem B11801051 : Blo 1032607 11801051 := bstep (se 1 (by rfl) ⟨8850788, by rfl⟩ : syracuseStep 11801051 = 17701577) B17701577
theorem B5247503 : Blo 1032607 5247503 := bstep (se 1 (by rfl) ⟨3935627, by rfl⟩ : syracuseStep 5247503 = 7871255) B7871255
theorem B2300015 : Blo 1032607 2300015 := bstep (se 1 (by rfl) ⟨1725011, by rfl⟩ : syracuseStep 2300015 = 3450023) B3450023
theorem B11344637 : Blo 1032607 11344637 := bstep (se 3 (by rfl) ⟨2127119, by rfl⟩ : syracuseStep 11344637 = 4254239) B4254239
theorem B3316535 : Blo 1032607 3316535 := bstep (se 1 (by rfl) ⟨2487401, by rfl⟩ : syracuseStep 3316535 = 4974803) B4974803
theorem B3546287 : Blo 1032607 3546287 := bstep (se 1 (by rfl) ⟨2659715, by rfl⟩ : syracuseStep 3546287 = 5319431) B5319431
theorem B14916797 : Blo 1032607 14916797 := bstep (se 3 (by rfl) ⟨2796899, by rfl⟩ : syracuseStep 14916797 = 5593799) B5593799
theorem B2990267 : Blo 1032607 2990267 := bstep (se 1 (by rfl) ⟨2242700, by rfl⟩ : syracuseStep 2990267 = 4485401) B4485401
theorem B4727069 : Blo 1032607 4727069 := bstep (se 3 (by rfl) ⟨886325, by rfl⟩ : syracuseStep 4727069 = 1772651) B1772651
theorem B1548911 : Blo 1032607 1548911 := bstep (se 1 (by rfl) ⟨1161683, by rfl⟩ : syracuseStep 1548911 = 2323367) B2323367
theorem B3318727 : Blo 1032607 3318727 := bstep (se 1 (by rfl) ⟨2489045, by rfl⟩ : syracuseStep 3318727 = 4978091) B4978091
theorem B3318995 : Blo 1032607 3318995 := bstep (se 1 (by rfl) ⟨2489246, by rfl⟩ : syracuseStep 3318995 = 4978493) B4978493
theorem B1549535 : Blo 1032607 1549535 := bstep (se 1 (by rfl) ⟨1162151, by rfl⟩ : syracuseStep 1549535 = 2324303) B2324303
theorem B1549775 : Blo 1032607 1549775 := bstep (se 1 (by rfl) ⟨1162331, by rfl⟩ : syracuseStep 1549775 = 2324663) B2324663
theorem B1549961 : Blo 1032607 1549961 := bstep (se 2 (by rfl) ⟨581235, by rfl⟩ : syracuseStep 1549961 = 1162471) B1162471
theorem B1746569 : Blo 1032607 1746569 := bstep (se 2 (by rfl) ⟨654963, by rfl⟩ : syracuseStep 1746569 = 1309927) B1309927
theorem B1550015 : Blo 1032607 1550015 := bstep (se 1 (by rfl) ⟨1162511, by rfl⟩ : syracuseStep 1550015 = 2325023) B2325023
theorem B1746623 : Blo 1032607 1746623 := bstep (se 1 (by rfl) ⟨1309967, by rfl⟩ : syracuseStep 1746623 = 2619935) B2619935
theorem B1550171 : Blo 1032607 1550171 := bstep (se 1 (by rfl) ⟨1162628, by rfl⟩ : syracuseStep 1550171 = 2325257) B2325257
theorem B1550555 : Blo 1032607 1550555 := bstep (se 1 (by rfl) ⟨1162916, by rfl⟩ : syracuseStep 1550555 = 2325833) B2325833
theorem B5318939 : Blo 1032607 5318939 := bstep (se 1 (by rfl) ⟨3989204, by rfl⟩ : syracuseStep 5318939 = 7978409) B7978409
theorem B1550825 : Blo 1032607 1550825 := bstep (se 2 (by rfl) ⟨581559, by rfl⟩ : syracuseStep 1550825 = 1163119) B1163119
theorem B1550831 : Blo 1032607 1550831 := bstep (se 1 (by rfl) ⟨1163123, by rfl⟩ : syracuseStep 1550831 = 2326247) B2326247
theorem B1551143 : Blo 1032607 1551143 := bstep (se 1 (by rfl) ⟨1163357, by rfl⟩ : syracuseStep 1551143 = 2326715) B2326715
theorem B1551215 : Blo 1032607 1551215 := bstep (se 1 (by rfl) ⟨1163411, by rfl⟩ : syracuseStep 1551215 = 2326823) B2326823
theorem B17705951 : Blo 1032607 17705951 := bstep (se 1 (by rfl) ⟨13279463, by rfl⟩ : syracuseStep 17705951 = 26558927) B26558927
theorem B1551467 : Blo 1032607 1551467 := bstep (se 1 (by rfl) ⟨1163600, by rfl⟩ : syracuseStep 1551467 = 2327201) B2327201
theorem B1551707 : Blo 1032607 1551707 := bstep (se 1 (by rfl) ⟨1163780, by rfl⟩ : syracuseStep 1551707 = 2327561) B2327561
theorem B1551737 : Blo 1032607 1551737 := bstep (se 2 (by rfl) ⟨581901, by rfl⟩ : syracuseStep 1551737 = 1163803) B1163803
theorem B1551743 : Blo 1032607 1551743 := bstep (se 1 (by rfl) ⟨1163807, by rfl⟩ : syracuseStep 1551743 = 2327615) B2327615
theorem B1748351 : Blo 1032607 1748351 := bstep (se 1 (by rfl) ⟨1311263, by rfl⟩ : syracuseStep 1748351 = 2622527) B2622527
theorem B1551977 : Blo 1032607 1551977 := bstep (se 2 (by rfl) ⟨581991, by rfl⟩ : syracuseStep 1551977 = 1163983) B1163983
theorem B7843553 : Blo 1032607 7843553 := bstep (se 2 (by rfl) ⟨2941332, by rfl⟩ : syracuseStep 7843553 = 5882665) B5882665
theorem B1552367 : Blo 1032607 1552367 := bstep (se 1 (by rfl) ⟨1164275, by rfl⟩ : syracuseStep 1552367 = 2328551) B2328551
theorem B1552487 : Blo 1032607 1552487 := bstep (se 1 (by rfl) ⟨1164365, by rfl⟩ : syracuseStep 1552487 = 2328731) B2328731
theorem B1552607 : Blo 1032607 1552607 := bstep (se 1 (by rfl) ⟨1164455, by rfl⟩ : syracuseStep 1552607 = 2328911) B2328911
theorem B2207999 : Blo 1032607 2207999 := bstep (se 1 (by rfl) ⟨1655999, by rfl⟩ : syracuseStep 2207999 = 3311999) B3311999
theorem B1552667 : Blo 1032607 1552667 := bstep (se 1 (by rfl) ⟨1164500, by rfl⟩ : syracuseStep 1552667 = 2329001) B2329001
theorem B2798135 : Blo 1032607 2798135 := bstep (se 1 (by rfl) ⟨2098601, by rfl⟩ : syracuseStep 2798135 = 4197203) B4197203
theorem B1553063 : Blo 1032607 1553063 := bstep (se 1 (by rfl) ⟨1164797, by rfl⟩ : syracuseStep 1553063 = 2329595) B2329595
theorem B1553183 : Blo 1032607 1553183 := bstep (se 1 (by rfl) ⟨1164887, by rfl⟩ : syracuseStep 1553183 = 2329775) B2329775
theorem B1553207 : Blo 1032607 1553207 := bstep (se 1 (by rfl) ⟨1164905, by rfl⟩ : syracuseStep 1553207 = 2329811) B2329811
theorem B1553321 : Blo 1032607 1553321 := bstep (se 2 (by rfl) ⟨582495, by rfl⟩ : syracuseStep 1553321 = 1164991) B1164991
theorem B143471573 : Blo 1032607 143471573 := bstep (se 7 (by rfl) ⟨1681307, by rfl⟩ : syracuseStep 143471573 = 3362615) B3362615
theorem B1553387 : Blo 1032607 1553387 := bstep (se 1 (by rfl) ⟨1165040, by rfl⟩ : syracuseStep 1553387 = 2330081) B2330081
theorem B1553663 : Blo 1032607 1553663 := bstep (se 1 (by rfl) ⟨1165247, by rfl⟩ : syracuseStep 1553663 = 2330495) B2330495
theorem B1553705 : Blo 1032607 1553705 := bstep (se 2 (by rfl) ⟨582639, by rfl⟩ : syracuseStep 1553705 = 1165279) B1165279
theorem B6632761 : Blo 1032607 6632761 := bstep (se 2 (by rfl) ⟨2487285, by rfl⟩ : syracuseStep 6632761 = 4974571) B4974571
theorem B33601189 : Blo 1032607 33601189 := bstep (se 4 (by rfl) ⟨3150111, by rfl⟩ : syracuseStep 33601189 = 6300223) B6300223
theorem B1554299 : Blo 1032607 1554299 := bstep (se 1 (by rfl) ⟨1165724, by rfl⟩ : syracuseStep 1554299 = 2331449) B2331449
theorem B1554335 : Blo 1032607 1554335 := bstep (se 1 (by rfl) ⟨1165751, by rfl⟩ : syracuseStep 1554335 = 2331503) B2331503
theorem B1554539 : Blo 1032607 1554539 := bstep (se 1 (by rfl) ⟨1165904, by rfl⟩ : syracuseStep 1554539 = 2331809) B2331809
theorem B1554569 : Blo 1032607 1554569 := bstep (se 2 (by rfl) ⟨582963, by rfl⟩ : syracuseStep 1554569 = 1165927) B1165927
theorem B3979475 : Blo 1032607 3979475 := bstep (se 1 (by rfl) ⟨2984606, by rfl⟩ : syracuseStep 3979475 = 5969213) B5969213
theorem B1554719 : Blo 1032607 1554719 := bstep (se 1 (by rfl) ⟨1166039, by rfl⟩ : syracuseStep 1554719 = 2332079) B2332079
theorem B12564983 : Blo 1032607 12564983 := bstep (se 1 (by rfl) ⟨9423737, by rfl⟩ : syracuseStep 12564983 = 18847475) B18847475
theorem B14137847 : Blo 1032607 14137847 := bstep (se 1 (by rfl) ⟨10603385, by rfl⟩ : syracuseStep 14137847 = 21206771) B21206771
theorem B6633991 : Blo 1032607 6633991 := bstep (se 1 (by rfl) ⟨4975493, by rfl⟩ : syracuseStep 6633991 = 9950987) B9950987
theorem B3488669 : Blo 1032607 3488669 := bstep (se 3 (by rfl) ⟨654125, by rfl⟩ : syracuseStep 3488669 = 1308251) B1308251
theorem B25214129 : Blo 1032607 25214129 := bstep (se 2 (by rfl) ⟨9455298, by rfl⟩ : syracuseStep 25214129 = 18910597) B18910597
theorem B22658383 : Blo 1032607 22658383 := bstep (se 1 (by rfl) ⟨16993787, by rfl⟩ : syracuseStep 22658383 = 33987575) B33987575
theorem B34062281 : Blo 1032607 34062281 := bstep (se 2 (by rfl) ⟨12773355, by rfl⟩ : syracuseStep 34062281 = 25546711) B25546711
theorem B25182211 : Blo 1032607 25182211 := bstep (se 1 (by rfl) ⟨18886658, by rfl⟩ : syracuseStep 25182211 = 37773317) B37773317
theorem B3588233 : Blo 1032607 3588233 := bstep (se 2 (by rfl) ⟨1345587, by rfl⟩ : syracuseStep 3588233 = 2691175) B2691175
theorem B1163623 : Blo 1032607 1163623 := bstep (se 1 (by rfl) ⟨872717, by rfl⟩ : syracuseStep 1163623 = 1745435) B1745435
theorem B1032671 : Blo 1032607 1032671 := bstep (se 1 (by rfl) ⟨774503, by rfl⟩ : syracuseStep 1032671 = 1549007) B1549007
theorem B1655263 : Blo 1032607 1655263 := bstep (se 1 (by rfl) ⟨1241447, by rfl⟩ : syracuseStep 1655263 = 2482895) B2482895
theorem B1032679 : Blo 1032607 1032679 := bstep (se 1 (by rfl) ⟨774509, by rfl⟩ : syracuseStep 1032679 = 1549019) B1549019
theorem B1032955 : Blo 1032607 1032955 := bstep (se 1 (by rfl) ⟨774716, by rfl⟩ : syracuseStep 1032955 = 1549433) B1549433
theorem B5030909 : Blo 1032607 5030909 := bstep (se 3 (by rfl) ⟨943295, by rfl⟩ : syracuseStep 5030909 = 1886591) B1886591
theorem B5227739 : Blo 1032607 5227739 := bstep (se 1 (by rfl) ⟨3920804, by rfl⟩ : syracuseStep 5227739 = 7841609) B7841609
theorem B1033535 : Blo 1032607 1033535 := bstep (se 1 (by rfl) ⟨775151, by rfl⟩ : syracuseStep 1033535 = 1550303) B1550303
theorem B1033543 : Blo 1032607 1033543 := bstep (se 1 (by rfl) ⟨775157, by rfl⟩ : syracuseStep 1033543 = 1550315) B1550315
theorem B14173537 : Blo 1032607 14173537 := bstep (se 2 (by rfl) ⟨5315076, by rfl⟩ : syracuseStep 14173537 = 10630153) B10630153
theorem B1033575 : Blo 1032607 1033575 := bstep (se 1 (by rfl) ⟨775181, by rfl⟩ : syracuseStep 1033575 = 1550363) B1550363
theorem B11945531 : Blo 1032607 11945531 := bstep (se 1 (by rfl) ⟨8959148, by rfl⟩ : syracuseStep 11945531 = 17918297) B17918297
theorem B1033819 : Blo 1032607 1033819 := bstep (se 1 (by rfl) ⟨775364, by rfl⟩ : syracuseStep 1033819 = 1550729) B1550729
theorem B10077871 : Blo 1032607 10077871 := bstep (se 1 (by rfl) ⟨7558403, by rfl⟩ : syracuseStep 10077871 = 15116807) B15116807
theorem B1034447 : Blo 1032607 1034447 := bstep (se 1 (by rfl) ⟨775835, by rfl⟩ : syracuseStep 1034447 = 1551671) B1551671
theorem B1034559 : Blo 1032607 1034559 := bstep (se 1 (by rfl) ⟨775919, by rfl⟩ : syracuseStep 1034559 = 1551839) B1551839
theorem B14895521 : Blo 1032607 14895521 := bstep (se 2 (by rfl) ⟨5585820, by rfl⟩ : syracuseStep 14895521 = 11171641) B11171641
theorem B1034703 : Blo 1032607 1034703 := bstep (se 1 (by rfl) ⟨776027, by rfl⟩ : syracuseStep 1034703 = 1552055) B1552055
theorem B1657435 : Blo 1032607 1657435 := bstep (se 1 (by rfl) ⟨1243076, by rfl⟩ : syracuseStep 1657435 = 2486153) B2486153
theorem B1034843 : Blo 1032607 1034843 := bstep (se 1 (by rfl) ⟨776132, by rfl⟩ : syracuseStep 1034843 = 1552265) B1552265
theorem B1035007 : Blo 1032607 1035007 := bstep (se 1 (by rfl) ⟨776255, by rfl⟩ : syracuseStep 1035007 = 1552511) B1552511
theorem B1035431 : Blo 1032607 1035431 := bstep (se 1 (by rfl) ⟨776573, by rfl⟩ : syracuseStep 1035431 = 1553147) B1553147
theorem B28659041 : Blo 1032607 28659041 := bstep (se 2 (by rfl) ⟨10747140, by rfl⟩ : syracuseStep 28659041 = 21494281) B21494281
theorem B1035727 : Blo 1032607 1035727 := bstep (se 1 (by rfl) ⟨776795, by rfl⟩ : syracuseStep 1035727 = 1553591) B1553591
theorem B1035887 : Blo 1032607 1035887 := bstep (se 1 (by rfl) ⟨776915, by rfl⟩ : syracuseStep 1035887 = 1553831) B1553831
theorem B4411111 : Blo 1032607 4411111 := bstep (se 1 (by rfl) ⟨3308333, by rfl⟩ : syracuseStep 4411111 = 6616667) B6616667
theorem B1036007 : Blo 1032607 1036007 := bstep (se 1 (by rfl) ⟨777005, by rfl⟩ : syracuseStep 1036007 = 1554011) B1554011
theorem B51007265 : Blo 1032607 51007265 := bstep (se 2 (by rfl) ⟨19127724, by rfl⟩ : syracuseStep 51007265 = 38255449) B38255449
theorem B14929829 : Blo 1032607 14929829 := bstep (se 4 (by rfl) ⟨1399671, by rfl⟩ : syracuseStep 14929829 = 2799343) B2799343
theorem B1036315 : Blo 1032607 1036315 := bstep (se 1 (by rfl) ⟨777236, by rfl⟩ : syracuseStep 1036315 = 1554473) B1554473
theorem B12570671 : Blo 1032607 12570671 := bstep (se 1 (by rfl) ⟨9428003, by rfl⟩ : syracuseStep 12570671 = 18856007) B18856007
theorem B1036335 : Blo 1032607 1036335 := bstep (se 1 (by rfl) ⟨777251, by rfl⟩ : syracuseStep 1036335 = 1554503) B1554503
theorem B1036591 : Blo 1032607 1036591 := bstep (se 1 (by rfl) ⟨777443, by rfl⟩ : syracuseStep 1036591 = 1554887) B1554887
theorem B5886857 : Blo 1032607 5886857 := bstep (se 2 (by rfl) ⟨2207571, by rfl⟩ : syracuseStep 5886857 = 4415143) B4415143
theorem B3494879 : Blo 1032607 3494879 := bstep (se 1 (by rfl) ⟨2621159, by rfl⟩ : syracuseStep 3494879 = 5242319) B5242319
theorem B12735791 : Blo 1032607 12735791 := bstep (se 1 (by rfl) ⟨9551843, by rfl⟩ : syracuseStep 12735791 = 19103687) B19103687
theorem B5461355 : Blo 1032607 5461355 := bstep (se 1 (by rfl) ⟨4096016, by rfl⟩ : syracuseStep 5461355 = 8192033) B8192033
theorem B8836847 : Blo 1032607 8836847 := bstep (se 1 (by rfl) ⟨6627635, by rfl⟩ : syracuseStep 8836847 = 13255271) B13255271
theorem B3921655 : Blo 1032607 3921655 := bstep (se 1 (by rfl) ⟨2941241, by rfl⟩ : syracuseStep 3921655 = 5882483) B5882483
theorem B6281057 : Blo 1032607 6281057 := bstep (se 2 (by rfl) ⟨2355396, by rfl⟩ : syracuseStep 6281057 = 4710793) B4710793
theorem B76437701 : Blo 1032607 76437701 := bstep (se 4 (by rfl) ⟨7166034, by rfl⟩ : syracuseStep 76437701 = 14332069) B14332069
theorem B5232923 : Blo 1032607 5232923 := bstep (se 1 (by rfl) ⟨3924692, by rfl⟩ : syracuseStep 5232923 = 7849385) B7849385
theorem B21813683 : Blo 1032607 21813683 := bstep (se 1 (by rfl) ⟨16360262, by rfl⟩ : syracuseStep 21813683 = 32720525) B32720525
theorem B26467073 : Blo 1032607 26467073 := bstep (se 2 (by rfl) ⟨9925152, by rfl⟩ : syracuseStep 26467073 = 19850305) B19850305
theorem B5233895 : Blo 1032607 5233895 := bstep (se 1 (by rfl) ⟨3925421, by rfl⟩ : syracuseStep 5233895 = 7850843) B7850843
theorem B3923599 : Blo 1032607 3923599 := bstep (se 1 (by rfl) ⟨2942699, by rfl⟩ : syracuseStep 3923599 = 5885399) B5885399
theorem B17653463 : Blo 1032607 17653463 := bstep (se 1 (by rfl) ⟨13240097, by rfl⟩ : syracuseStep 17653463 = 26480195) B26480195
theorem B136175377 : Blo 1032607 136175377 := bstep (se 2 (by rfl) ⟨51065766, by rfl⟩ : syracuseStep 136175377 = 102131533) B102131533
theorem B22667141 : Blo 1032607 22667141 := bstep (se 4 (by rfl) ⟨2125044, by rfl⟩ : syracuseStep 22667141 = 4250089) B4250089
theorem B8839307 : Blo 1032607 8839307 := bstep (se 1 (by rfl) ⟨6629480, by rfl⟩ : syracuseStep 8839307 = 13258961) B13258961
theorem B3498281 : Blo 1032607 3498281 := bstep (se 2 (by rfl) ⟨1311855, by rfl⟩ : syracuseStep 3498281 = 2623711) B2623711
theorem B2941721 : Blo 1032607 2941721 := bstep (se 2 (by rfl) ⟨1103145, by rfl⟩ : syracuseStep 2941721 = 2206291) B2206291
theorem B2614639 : Blo 1032607 2614639 := bstep (se 1 (by rfl) ⟨1960979, by rfl⟩ : syracuseStep 2614639 = 3921959) B3921959
theorem B19916279 : Blo 1032607 19916279 := bstep (se 1 (by rfl) ⟨14937209, by rfl⟩ : syracuseStep 19916279 = 29874419) B29874419
theorem B8840947 : Blo 1032607 8840947 := bstep (se 1 (by rfl) ⟨6630710, by rfl⟩ : syracuseStep 8840947 = 13261421) B13261421
theorem B26830595 : Blo 1032607 26830595 := bstep (se 1 (by rfl) ⟨20122946, by rfl⟩ : syracuseStep 26830595 = 40245893) B40245893
theorem B6285433 : Blo 1032607 6285433 := bstep (se 2 (by rfl) ⟨2357037, by rfl⟩ : syracuseStep 6285433 = 4714075) B4714075
theorem B8972531 : Blo 1032607 8972531 := bstep (se 1 (by rfl) ⟨6729398, by rfl⟩ : syracuseStep 8972531 = 13458797) B13458797
theorem B3729719 : Blo 1032607 3729719 := bstep (se 1 (by rfl) ⟨2797289, by rfl⟩ : syracuseStep 3729719 = 5594579) B5594579
theorem B4418219 : Blo 1032607 4418219 := bstep (se 1 (by rfl) ⟨3313664, by rfl⟩ : syracuseStep 4418219 = 6627329) B6627329
theorem B7859105 : Blo 1032607 7859105 := bstep (se 2 (by rfl) ⟨2947164, by rfl⟩ : syracuseStep 7859105 = 5894329) B5894329
theorem B2944295 : Blo 1032607 2944295 := bstep (se 1 (by rfl) ⟨2208221, by rfl⟩ : syracuseStep 2944295 = 4416443) B4416443
theorem B11792303 : Blo 1032607 11792303 := bstep (se 1 (by rfl) ⟨8844227, by rfl⟩ : syracuseStep 11792303 = 17688455) B17688455
theorem B1961975 : Blo 1032607 1961975 := bstep (se 1 (by rfl) ⟨1471481, by rfl⟩ : syracuseStep 1961975 = 2942963) B2942963
theorem B4419859 : Blo 1032607 4419859 := bstep (se 1 (by rfl) ⟨3314894, by rfl⟩ : syracuseStep 4419859 = 6629789) B6629789
theorem B2617697 : Blo 1032607 2617697 := bstep (se 2 (by rfl) ⟨981636, by rfl⟩ : syracuseStep 2617697 = 1963273) B1963273
theorem B1470889 : Blo 1032607 1470889 := bstep (se 2 (by rfl) ⟨551583, by rfl⟩ : syracuseStep 1470889 = 1103167) B1103167
theorem B2355643 : Blo 1032607 2355643 := bstep (se 1 (by rfl) ⟨1766732, by rfl⟩ : syracuseStep 2355643 = 3533465) B3533465
theorem B2618345 : Blo 1032607 2618345 := bstep (se 2 (by rfl) ⟨981879, by rfl⟩ : syracuseStep 2618345 = 1963759) B1963759
theorem B2946095 : Blo 1032607 2946095 := bstep (se 1 (by rfl) ⟨2209571, by rfl⟩ : syracuseStep 2946095 = 4419143) B4419143
theorem B5239889 : Blo 1032607 5239889 := bstep (se 2 (by rfl) ⟨1964958, by rfl⟩ : syracuseStep 5239889 = 3929917) B3929917
theorem B3143495 : Blo 1032607 3143495 := bstep (se 1 (by rfl) ⟨2357621, by rfl⟩ : syracuseStep 3143495 = 4715243) B4715243
theorem B1472347 : Blo 1032607 1472347 := bstep (se 1 (by rfl) ⟨1104260, by rfl⟩ : syracuseStep 1472347 = 2208521) B2208521
theorem B2324447 : Blo 1032607 2324447 := bstep (se 1 (by rfl) ⟨1743335, by rfl⟩ : syracuseStep 2324447 = 3486671) B3486671
theorem B2324519 : Blo 1032607 2324519 := bstep (se 1 (by rfl) ⟨1743389, by rfl⟩ : syracuseStep 2324519 = 3486779) B3486779
theorem B1308727 : Blo 1032607 1308727 := bstep (se 1 (by rfl) ⟨981545, by rfl⟩ : syracuseStep 1308727 = 1963091) B1963091
theorem B5896313 : Blo 1032607 5896313 := bstep (se 2 (by rfl) ⟨2211117, by rfl⟩ : syracuseStep 5896313 = 4422235) B4422235
theorem B2947211 : Blo 1032607 2947211 := bstep (se 1 (by rfl) ⟨2210408, by rfl⟩ : syracuseStep 2947211 = 4420817) B4420817
theorem B2324699 : Blo 1032607 2324699 := bstep (se 1 (by rfl) ⟨1743524, by rfl⟩ : syracuseStep 2324699 = 3487049) B3487049
theorem B2619641 : Blo 1032607 2619641 := bstep (se 2 (by rfl) ⟨982365, by rfl⟩ : syracuseStep 2619641 = 1964731) B1964731
theorem B14907685 : Blo 1032607 14907685 := bstep (se 4 (by rfl) ⟨1397595, by rfl⟩ : syracuseStep 14907685 = 2795191) B2795191
theorem B7960913 : Blo 1032607 7960913 := bstep (se 2 (by rfl) ⟨2985342, by rfl⟩ : syracuseStep 7960913 = 5970685) B5970685
theorem B5241185 : Blo 1032607 5241185 := bstep (se 2 (by rfl) ⟨1965444, by rfl⟩ : syracuseStep 5241185 = 3930889) B3930889
theorem B2324897 : Blo 1032607 2324897 := bstep (se 2 (by rfl) ⟨871836, by rfl⟩ : syracuseStep 2324897 = 1743673) B1743673
theorem B2324969 : Blo 1032607 2324969 := bstep (se 2 (by rfl) ⟨871863, by rfl⟩ : syracuseStep 2324969 = 1743727) B1743727
theorem B5896745 : Blo 1032607 5896745 := bstep (se 2 (by rfl) ⟨2211279, by rfl⟩ : syracuseStep 5896745 = 4422559) B4422559
theorem B9927613 : Blo 1032607 9927613 := bstep (se 3 (by rfl) ⟨1861427, by rfl⟩ : syracuseStep 9927613 = 3722855) B3722855
theorem B1965035 : Blo 1032607 1965035 := bstep (se 1 (by rfl) ⟨1473776, by rfl⟩ : syracuseStep 1965035 = 2947553) B2947553
theorem B2325599 : Blo 1032607 2325599 := bstep (se 1 (by rfl) ⟨1744199, by rfl⟩ : syracuseStep 2325599 = 3488399) B3488399
theorem B2948339 : Blo 1032607 2948339 := bstep (se 1 (by rfl) ⟨2211254, by rfl⟩ : syracuseStep 2948339 = 4422509) B4422509
theorem B2325815 : Blo 1032607 2325815 := bstep (se 1 (by rfl) ⟨1744361, by rfl⟩ : syracuseStep 2325815 = 3488723) B3488723
theorem B2948521 : Blo 1032607 2948521 := bstep (se 2 (by rfl) ⟨1105695, by rfl⟩ : syracuseStep 2948521 = 2211391) B2211391
theorem B2325995 : Blo 1032607 2325995 := bstep (se 1 (by rfl) ⟨1744496, by rfl⟩ : syracuseStep 2325995 = 3488993) B3488993
theorem B3931649 : Blo 1032607 3931649 := bstep (se 2 (by rfl) ⟨1474368, by rfl⟩ : syracuseStep 3931649 = 2948737) B2948737
theorem B5242643 : Blo 1032607 5242643 := bstep (se 1 (by rfl) ⟨3931982, by rfl⟩ : syracuseStep 5242643 = 7863965) B7863965
theorem B1310575 : Blo 1032607 1310575 := bstep (se 1 (by rfl) ⟨982931, by rfl⟩ : syracuseStep 1310575 = 1965863) B1965863
theorem B1965961 : Blo 1032607 1965961 := bstep (se 2 (by rfl) ⟨737235, by rfl⟩ : syracuseStep 1965961 = 1474471) B1474471
theorem B2326427 : Blo 1032607 2326427 := bstep (se 1 (by rfl) ⟨1744820, by rfl⟩ : syracuseStep 2326427 = 3489641) B3489641
theorem B33521789 : Blo 1032607 33521789 := bstep (se 3 (by rfl) ⟨6285335, by rfl⟩ : syracuseStep 33521789 = 12570671) B12570671
theorem B9568621 : Blo 1032607 9568621 := bstep (se 3 (by rfl) ⟨1794116, by rfl⟩ : syracuseStep 9568621 = 3588233) B3588233
theorem B2098057 : Blo 1032607 2098057 := bstep (se 2 (by rfl) ⟨786771, by rfl⟩ : syracuseStep 2098057 = 1573543) B1573543
theorem B7963687 : Blo 1032607 7963687 := bstep (se 1 (by rfl) ⟨5972765, by rfl⟩ : syracuseStep 7963687 = 11945531) B11945531
theorem B3933319 : Blo 1032607 3933319 := bstep (se 1 (by rfl) ⟨2949989, by rfl⟩ : syracuseStep 3933319 = 5899979) B5899979
theorem B4424969 : Blo 1032607 4424969 := bstep (se 2 (by rfl) ⟨1659363, by rfl⟩ : syracuseStep 4424969 = 3318727) B3318727
theorem B9930347 : Blo 1032607 9930347 := bstep (se 1 (by rfl) ⟨7447760, by rfl⟩ : syracuseStep 9930347 = 14895521) B14895521
theorem B3934291 : Blo 1032607 3934291 := bstep (se 1 (by rfl) ⟨2950718, by rfl⟩ : syracuseStep 3934291 = 5901437) B5901437
theorem B5245073 : Blo 1032607 5245073 := bstep (se 2 (by rfl) ⟨1966902, by rfl⟩ : syracuseStep 5245073 = 3933805) B3933805
theorem B13437161 : Blo 1032607 13437161 := bstep (se 2 (by rfl) ⟨5038935, by rfl⟩ : syracuseStep 13437161 = 10077871) B10077871
theorem B19106027 : Blo 1032607 19106027 := bstep (se 1 (by rfl) ⟨14329520, by rfl⟩ : syracuseStep 19106027 = 28659041) B28659041
theorem B1182055 : Blo 1032607 1182055 := bstep (se 1 (by rfl) ⟨886541, by rfl⟩ : syracuseStep 1182055 = 1773083) B1773083
theorem B20187787 : Blo 1032607 20187787 := bstep (se 1 (by rfl) ⟨15140840, by rfl⟩ : syracuseStep 20187787 = 30281681) B30281681
theorem B3935081 : Blo 1032607 3935081 := bstep (se 2 (by rfl) ⟨1475655, by rfl⟩ : syracuseStep 3935081 = 2951311) B2951311
theorem B7867367 : Blo 1032607 7867367 := bstep (se 1 (by rfl) ⟨5900525, by rfl⟩ : syracuseStep 7867367 = 11801051) B11801051
theorem B8850653 : Blo 1032607 8850653 := bstep (se 3 (by rfl) ⟨1659497, by rfl⟩ : syracuseStep 8850653 = 3318995) B3318995
theorem B2329919 : Blo 1032607 2329919 := bstep (se 1 (by rfl) ⟨1747439, by rfl⟩ : syracuseStep 2329919 = 3494879) B3494879
theorem B8490527 : Blo 1032607 8490527 := bstep (se 1 (by rfl) ⟨6367895, by rfl⟩ : syracuseStep 8490527 = 12735791) B12735791
theorem B50958467 : Blo 1032607 50958467 := bstep (se 1 (by rfl) ⟨38218850, by rfl⟩ : syracuseStep 50958467 = 76437701) B76437701
theorem B2364191 : Blo 1032607 2364191 := bstep (se 1 (by rfl) ⟨1773143, by rfl⟩ : syracuseStep 2364191 = 3546287) B3546287
theorem B11768975 : Blo 1032607 11768975 := bstep (se 1 (by rfl) ⟨8826731, by rfl⟩ : syracuseStep 11768975 = 17653463) B17653463
theorem B3151379 : Blo 1032607 3151379 := bstep (se 1 (by rfl) ⟨2363534, by rfl⟩ : syracuseStep 3151379 = 4727069) B4727069
theorem B2332187 : Blo 1032607 2332187 := bstep (se 1 (by rfl) ⟨1749140, by rfl⟩ : syracuseStep 2332187 = 3498281) B3498281
theorem B13277519 : Blo 1032607 13277519 := bstep (se 1 (by rfl) ⟨9958139, by rfl⟩ : syracuseStep 13277519 = 19916279) B19916279
theorem B58169821 : Blo 1032607 58169821 := bstep (se 3 (by rfl) ⟨10906841, by rfl⟩ : syracuseStep 58169821 = 21813683) B21813683
theorem B3545959 : Blo 1032607 3545959 := bstep (se 1 (by rfl) ⟨2659469, by rfl⟩ : syracuseStep 3545959 = 5318939) B5318939
theorem B11803967 : Blo 1032607 11803967 := bstep (se 1 (by rfl) ⟨8852975, by rfl⟩ : syracuseStep 11803967 = 17705951) B17705951
theorem B44801585 : Blo 1032607 44801585 := bstep (se 2 (by rfl) ⟨16800594, by rfl⟩ : syracuseStep 44801585 = 33601189) B33601189
theorem B1744969 : Blo 1032607 1744969 := bstep (se 2 (by rfl) ⟨654363, by rfl⟩ : syracuseStep 1744969 = 1308727) B1308727
theorem B1745131 : Blo 1032607 1745131 := bstep (se 1 (by rfl) ⟨1308848, by rfl⟩ : syracuseStep 1745131 = 2617697) B2617697
theorem B1745563 : Blo 1032607 1745563 := bstep (se 1 (by rfl) ⟨1309172, by rfl⟩ : syracuseStep 1745563 = 2618345) B2618345
theorem B1549631 : Blo 1032607 1549631 := bstep (se 1 (by rfl) ⟨1162223, by rfl⟩ : syracuseStep 1549631 = 2324447) B2324447
theorem B1549679 : Blo 1032607 1549679 := bstep (se 1 (by rfl) ⟨1162259, by rfl⟩ : syracuseStep 1549679 = 2324519) B2324519
theorem B1549799 : Blo 1032607 1549799 := bstep (se 1 (by rfl) ⟨1162349, by rfl⟩ : syracuseStep 1549799 = 2324699) B2324699
theorem B1746427 : Blo 1032607 1746427 := bstep (se 1 (by rfl) ⟨1309820, by rfl⟩ : syracuseStep 1746427 = 2619641) B2619641
theorem B1549931 : Blo 1032607 1549931 := bstep (se 1 (by rfl) ⟨1162448, by rfl⟩ : syracuseStep 1549931 = 2324897) B2324897
theorem B1549979 : Blo 1032607 1549979 := bstep (se 1 (by rfl) ⟨1162484, by rfl⟩ : syracuseStep 1549979 = 2324969) B2324969
theorem B1550399 : Blo 1032607 1550399 := bstep (se 1 (by rfl) ⟨1162799, by rfl⟩ : syracuseStep 1550399 = 2325599) B2325599
theorem B1550543 : Blo 1032607 1550543 := bstep (se 1 (by rfl) ⟨1162907, by rfl⟩ : syracuseStep 1550543 = 2325815) B2325815
theorem B1550663 : Blo 1032607 1550663 := bstep (se 1 (by rfl) ⟨1162997, by rfl⟩ : syracuseStep 1550663 = 2325995) B2325995
theorem B1747433 : Blo 1032607 1747433 := bstep (se 2 (by rfl) ⟨655287, by rfl⟩ : syracuseStep 1747433 = 1310575) B1310575
theorem B1550951 : Blo 1032607 1550951 := bstep (se 1 (by rfl) ⟨1163213, by rfl⟩ : syracuseStep 1550951 = 2326427) B2326427
theorem B1551497 : Blo 1032607 1551497 := bstep (se 2 (by rfl) ⟨581811, by rfl⟩ : syracuseStep 1551497 = 1163623) B1163623
theorem B2796727 : Blo 1032607 2796727 := bstep (se 1 (by rfl) ⟨2097545, by rfl⟩ : syracuseStep 2796727 = 4195091) B4195091
theorem B1551551 : Blo 1032607 1551551 := bstep (se 1 (by rfl) ⟨1163663, by rfl⟩ : syracuseStep 1551551 = 2327327) B2327327
theorem B2207017 : Blo 1032607 2207017 := bstep (se 2 (by rfl) ⟨827631, by rfl⟩ : syracuseStep 2207017 = 1655263) B1655263
theorem B3353939 : Blo 1032607 3353939 := bstep (se 1 (by rfl) ⟨2515454, by rfl⟩ : syracuseStep 3353939 = 5030909) B5030909
theorem B3485159 : Blo 1032607 3485159 := bstep (se 1 (by rfl) ⟨2613869, by rfl⟩ : syracuseStep 3485159 = 5227739) B5227739
theorem B1749019 : Blo 1032607 1749019 := bstep (se 1 (by rfl) ⟨1311764, by rfl⟩ : syracuseStep 1749019 = 2623529) B2623529
theorem B1749161 : Blo 1032607 1749161 := bstep (se 2 (by rfl) ⟨655935, by rfl⟩ : syracuseStep 1749161 = 1311871) B1311871
theorem B3453263 : Blo 1032607 3453263 := bstep (se 1 (by rfl) ⟨2589947, by rfl⟩ : syracuseStep 3453263 = 5179895) B5179895
theorem B3486185 : Blo 1032607 3486185 := bstep (se 2 (by rfl) ⟨1307319, by rfl⟩ : syracuseStep 3486185 = 2614639) B2614639
theorem B1553735 : Blo 1032607 1553735 := bstep (se 1 (by rfl) ⟨1165301, by rfl⟩ : syracuseStep 1553735 = 2330603) B2330603
theorem B2209913 : Blo 1032607 2209913 := bstep (se 2 (by rfl) ⟨828717, by rfl⟩ : syracuseStep 2209913 = 1657435) B1657435
theorem B8829161 : Blo 1032607 8829161 := bstep (se 2 (by rfl) ⟨3310935, by rfl⟩ : syracuseStep 8829161 = 6621871) B6621871
theorem B14563613 : Blo 1032607 14563613 := bstep (se 3 (by rfl) ⟨2730677, by rfl⟩ : syracuseStep 14563613 = 5461355) B5461355
theorem B3488615 : Blo 1032607 3488615 := bstep (se 1 (by rfl) ⟨2616461, by rfl⟩ : syracuseStep 3488615 = 5232923) B5232923
theorem B17644715 : Blo 1032607 17644715 := bstep (se 1 (by rfl) ⟨13233536, by rfl⟩ : syracuseStep 17644715 = 26467073) B26467073
theorem B2211023 : Blo 1032607 2211023 := bstep (se 1 (by rfl) ⟨1658267, by rfl⟩ : syracuseStep 2211023 = 3316535) B3316535
theorem B9944531 : Blo 1032607 9944531 := bstep (se 1 (by rfl) ⟨7458398, by rfl⟩ : syracuseStep 9944531 = 14916797) B14916797
theorem B3489263 : Blo 1032607 3489263 := bstep (se 1 (by rfl) ⟨2616947, by rfl⟩ : syracuseStep 3489263 = 5233895) B5233895
theorem B5881481 : Blo 1032607 5881481 := bstep (se 2 (by rfl) ⟨2205555, by rfl⟩ : syracuseStep 5881481 = 4411111) B4411111
theorem B1032607 : Blo 1032607 1032607 := bstep (se 1 (by rfl) ⟨774455, by rfl⟩ : syracuseStep 1032607 = 1548911) B1548911
theorem B1033023 : Blo 1032607 1033023 := bstep (se 1 (by rfl) ⟨774767, by rfl⟩ : syracuseStep 1033023 = 1549535) B1549535
theorem B1033183 : Blo 1032607 1033183 := bstep (se 1 (by rfl) ⟨774887, by rfl⟩ : syracuseStep 1033183 = 1549775) B1549775
theorem B1164379 : Blo 1032607 1164379 := bstep (se 1 (by rfl) ⟨873284, by rfl⟩ : syracuseStep 1164379 = 1746569) B1746569
theorem B1033307 : Blo 1032607 1033307 := bstep (se 1 (by rfl) ⟨774980, by rfl⟩ : syracuseStep 1033307 = 1549961) B1549961
theorem B1033343 : Blo 1032607 1033343 := bstep (se 1 (by rfl) ⟨775007, by rfl⟩ : syracuseStep 1033343 = 1550015) B1550015
theorem B1164415 : Blo 1032607 1164415 := bstep (se 1 (by rfl) ⟨873311, by rfl⟩ : syracuseStep 1164415 = 1746623) B1746623
theorem B1033447 : Blo 1032607 1033447 := bstep (se 1 (by rfl) ⟨775085, by rfl⟩ : syracuseStep 1033447 = 1550171) B1550171
theorem B1033703 : Blo 1032607 1033703 := bstep (se 1 (by rfl) ⟨775277, by rfl⟩ : syracuseStep 1033703 = 1550555) B1550555
theorem B5981687 : Blo 1032607 5981687 := bstep (se 1 (by rfl) ⟨4486265, by rfl⟩ : syracuseStep 5981687 = 8972531) B8972531
theorem B1033883 : Blo 1032607 1033883 := bstep (se 1 (by rfl) ⟨775412, by rfl⟩ : syracuseStep 1033883 = 1550825) B1550825
theorem B1033887 : Blo 1032607 1033887 := bstep (se 1 (by rfl) ⟨775415, by rfl⟩ : syracuseStep 1033887 = 1550831) B1550831
theorem B1034095 : Blo 1032607 1034095 := bstep (se 1 (by rfl) ⟨775571, by rfl⟩ : syracuseStep 1034095 = 1551143) B1551143
theorem B1034143 : Blo 1032607 1034143 := bstep (se 1 (by rfl) ⟨775607, by rfl⟩ : syracuseStep 1034143 = 1551215) B1551215
theorem B1034311 : Blo 1032607 1034311 := bstep (se 1 (by rfl) ⟨775733, by rfl⟩ : syracuseStep 1034311 = 1551467) B1551467
theorem B1034471 : Blo 1032607 1034471 := bstep (se 1 (by rfl) ⟨775853, by rfl⟩ : syracuseStep 1034471 = 1551707) B1551707
theorem B1034491 : Blo 1032607 1034491 := bstep (se 1 (by rfl) ⟨775868, by rfl⟩ : syracuseStep 1034491 = 1551737) B1551737
theorem B1034495 : Blo 1032607 1034495 := bstep (se 1 (by rfl) ⟨775871, by rfl⟩ : syracuseStep 1034495 = 1551743) B1551743
theorem B1165567 : Blo 1032607 1165567 := bstep (se 1 (by rfl) ⟨874175, by rfl⟩ : syracuseStep 1165567 = 1748351) B1748351
theorem B5228873 : Blo 1032607 5228873 := bstep (se 2 (by rfl) ⟨1960827, by rfl⟩ : syracuseStep 5228873 = 3921655) B3921655
theorem B1034651 : Blo 1032607 1034651 := bstep (se 1 (by rfl) ⟨775988, by rfl⟩ : syracuseStep 1034651 = 1551977) B1551977
theorem B5229035 : Blo 1032607 5229035 := bstep (se 1 (by rfl) ⟨3921776, by rfl⟩ : syracuseStep 5229035 = 7843553) B7843553
theorem B1034911 : Blo 1032607 1034911 := bstep (se 1 (by rfl) ⟨776183, by rfl⟩ : syracuseStep 1034911 = 1552367) B1552367
theorem B1034991 : Blo 1032607 1034991 := bstep (se 1 (by rfl) ⟨776243, by rfl⟩ : syracuseStep 1034991 = 1552487) B1552487
theorem B1035071 : Blo 1032607 1035071 := bstep (se 1 (by rfl) ⟨776303, by rfl⟩ : syracuseStep 1035071 = 1552607) B1552607
theorem B1035111 : Blo 1032607 1035111 := bstep (se 1 (by rfl) ⟨776333, by rfl⟩ : syracuseStep 1035111 = 1552667) B1552667
theorem B19876913 : Blo 1032607 19876913 := bstep (se 2 (by rfl) ⟨7453842, by rfl⟩ : syracuseStep 19876913 = 14907685) B14907685
theorem B1035375 : Blo 1032607 1035375 := bstep (se 1 (by rfl) ⟨776531, by rfl⟩ : syracuseStep 1035375 = 1553063) B1553063
theorem B1035455 : Blo 1032607 1035455 := bstep (se 1 (by rfl) ⟨776591, by rfl⟩ : syracuseStep 1035455 = 1553183) B1553183
theorem B1035471 : Blo 1032607 1035471 := bstep (se 1 (by rfl) ⟨776603, by rfl⟩ : syracuseStep 1035471 = 1553207) B1553207
theorem B1035547 : Blo 1032607 1035547 := bstep (se 1 (by rfl) ⟨776660, by rfl⟩ : syracuseStep 1035547 = 1553321) B1553321
theorem B1035591 : Blo 1032607 1035591 := bstep (se 1 (by rfl) ⟨776693, by rfl⟩ : syracuseStep 1035591 = 1553387) B1553387
theorem B3493259 : Blo 1032607 3493259 := bstep (se 1 (by rfl) ⟨2619944, by rfl⟩ : syracuseStep 3493259 = 5239889) B5239889
theorem B1035775 : Blo 1032607 1035775 := bstep (se 1 (by rfl) ⟨776831, by rfl⟩ : syracuseStep 1035775 = 1553663) B1553663
theorem B1035803 : Blo 1032607 1035803 := bstep (se 1 (by rfl) ⟨776852, by rfl⟩ : syracuseStep 1035803 = 1553705) B1553705
theorem B1036199 : Blo 1032607 1036199 := bstep (se 1 (by rfl) ⟨777149, by rfl⟩ : syracuseStep 1036199 = 1554299) B1554299
theorem B1036223 : Blo 1032607 1036223 := bstep (se 1 (by rfl) ⟨777167, by rfl⟩ : syracuseStep 1036223 = 1554335) B1554335
theorem B1036359 : Blo 1032607 1036359 := bstep (se 1 (by rfl) ⟨777269, by rfl⟩ : syracuseStep 1036359 = 1554539) B1554539
theorem B1036379 : Blo 1032607 1036379 := bstep (se 1 (by rfl) ⟨777284, by rfl⟩ : syracuseStep 1036379 = 1554569) B1554569
theorem B1036479 : Blo 1032607 1036479 := bstep (se 1 (by rfl) ⟨777359, by rfl⟩ : syracuseStep 1036479 = 1554719) B1554719
theorem B3494123 : Blo 1032607 3494123 := bstep (se 1 (by rfl) ⟨2620592, by rfl⟩ : syracuseStep 3494123 = 5241185) B5241185
theorem B8376655 : Blo 1032607 8376655 := bstep (se 1 (by rfl) ⟨6282491, by rfl⟩ : syracuseStep 8376655 = 12564983) B12564983
theorem B9425231 : Blo 1032607 9425231 := bstep (se 1 (by rfl) ⟨7068923, by rfl⟩ : syracuseStep 9425231 = 14137847) B14137847
theorem B5231465 : Blo 1032607 5231465 := bstep (se 2 (by rfl) ⟨1961799, by rfl⟩ : syracuseStep 5231465 = 3923599) B3923599
theorem B60445709 : Blo 1032607 60445709 := bstep (se 3 (by rfl) ⟨11333570, by rfl⟩ : syracuseStep 60445709 = 22667141) B22667141
theorem B3495095 : Blo 1032607 3495095 := bstep (se 1 (by rfl) ⟨2621321, by rfl⟩ : syracuseStep 3495095 = 5242643) B5242643
theorem B33576281 : Blo 1032607 33576281 := bstep (se 2 (by rfl) ⟨12591105, by rfl⟩ : syracuseStep 33576281 = 25182211) B25182211
theorem B3495419 : Blo 1032607 3495419 := bstep (se 1 (by rfl) ⟨2621564, by rfl⟩ : syracuseStep 3495419 = 5243129) B5243129
theorem B3495527 : Blo 1032607 3495527 := bstep (se 1 (by rfl) ⟨2621645, by rfl⟩ : syracuseStep 3495527 = 5243291) B5243291
theorem B5887997 : Blo 1032607 5887997 := bstep (se 3 (by rfl) ⟨1103999, by rfl⟩ : syracuseStep 5887997 = 2207999) B2207999
theorem B3496391 : Blo 1032607 3496391 := bstep (se 1 (by rfl) ⟨2622293, by rfl⟩ : syracuseStep 3496391 = 5244587) B5244587
theorem B18898049 : Blo 1032607 18898049 := bstep (se 2 (by rfl) ⟨7086768, by rfl⟩ : syracuseStep 18898049 = 14173537) B14173537
theorem B11787929 : Blo 1032607 11787929 := bstep (se 2 (by rfl) ⟨4420473, by rfl⟩ : syracuseStep 11787929 = 8840947) B8840947
theorem B34004843 : Blo 1032607 34004843 := bstep (se 1 (by rfl) ⟨25503632, by rfl⟩ : syracuseStep 34004843 = 51007265) B51007265
theorem B9953219 : Blo 1032607 9953219 := bstep (se 1 (by rfl) ⟨7464914, by rfl⟩ : syracuseStep 9953219 = 14929829) B14929829
theorem B8380577 : Blo 1032607 8380577 := bstep (se 2 (by rfl) ⟨3142716, by rfl⟩ : syracuseStep 8380577 = 6285433) B6285433
theorem B3498173 : Blo 1032607 3498173 := bstep (se 3 (by rfl) ⟨655907, by rfl⟩ : syracuseStep 3498173 = 1311815) B1311815
theorem B3498335 : Blo 1032607 3498335 := bstep (se 1 (by rfl) ⟨2623751, by rfl⟩ : syracuseStep 3498335 = 5247503) B5247503
theorem B3924571 : Blo 1032607 3924571 := bstep (se 1 (by rfl) ⟨2943428, by rfl⟩ : syracuseStep 3924571 = 5886857) B5886857
theorem B4416545 : Blo 1032607 4416545 := bstep (se 2 (by rfl) ⟨1656204, by rfl⟩ : syracuseStep 4416545 = 3312409) B3312409
theorem B5891231 : Blo 1032607 5891231 := bstep (se 1 (by rfl) ⟨4418423, by rfl⟩ : syracuseStep 5891231 = 8836847) B8836847
theorem B4187371 : Blo 1032607 4187371 := bstep (se 1 (by rfl) ⟨3140528, by rfl⟩ : syracuseStep 4187371 = 6281057) B6281057
theorem B1533343 : Blo 1032607 1533343 := bstep (se 1 (by rfl) ⟨1150007, by rfl⟩ : syracuseStep 1533343 = 2300015) B2300015
theorem B7563091 : Blo 1032607 7563091 := bstep (se 1 (by rfl) ⟨5672318, by rfl⟩ : syracuseStep 7563091 = 11344637) B11344637
theorem B8382653 : Blo 1032607 8382653 := bstep (se 3 (by rfl) ⟨1571747, by rfl⟩ : syracuseStep 8382653 = 3143495) B3143495
theorem B4418185 : Blo 1032607 4418185 := bstep (se 2 (by rfl) ⟨1656819, by rfl⟩ : syracuseStep 4418185 = 3313639) B3313639
theorem B5892871 : Blo 1032607 5892871 := bstep (se 1 (by rfl) ⟨4419653, by rfl⟩ : syracuseStep 5892871 = 8839307) B8839307
theorem B1993511 : Blo 1032607 1993511 := bstep (se 1 (by rfl) ⟨1495133, by rfl⟩ : syracuseStep 1993511 = 2990267) B2990267
theorem B5893145 : Blo 1032607 5893145 := bstep (se 2 (by rfl) ⟨2209929, by rfl⟩ : syracuseStep 5893145 = 4419859) B4419859
theorem B1961147 : Blo 1032607 1961147 := bstep (se 1 (by rfl) ⟨1470860, by rfl⟩ : syracuseStep 1961147 = 2941721) B2941721
theorem B1961185 : Blo 1032607 1961185 := bstep (se 2 (by rfl) ⟨735444, by rfl⟩ : syracuseStep 1961185 = 1470889) B1470889
theorem B3140857 : Blo 1032607 3140857 := bstep (se 2 (by rfl) ⟨1177821, by rfl⟩ : syracuseStep 3140857 = 2355643) B2355643
theorem B17887063 : Blo 1032607 17887063 := bstep (se 1 (by rfl) ⟨13415297, by rfl⟩ : syracuseStep 17887063 = 26830595) B26830595
theorem B2486479 : Blo 1032607 2486479 := bstep (se 1 (by rfl) ⟨1864859, by rfl⟩ : syracuseStep 2486479 = 3729719) B3729719
theorem B8843681 : Blo 1032607 8843681 := bstep (se 2 (by rfl) ⟨3316380, by rfl⟩ : syracuseStep 8843681 = 6632761) B6632761
theorem B2945479 : Blo 1032607 2945479 := bstep (se 1 (by rfl) ⟨2209109, by rfl⟩ : syracuseStep 2945479 = 4418219) B4418219
theorem B5239403 : Blo 1032607 5239403 := bstep (se 1 (by rfl) ⟨3929552, by rfl⟩ : syracuseStep 5239403 = 7859105) B7859105
theorem B1962863 : Blo 1032607 1962863 := bstep (se 1 (by rfl) ⟨1472147, by rfl⟩ : syracuseStep 1962863 = 2944295) B2944295
theorem B1963129 : Blo 1032607 1963129 := bstep (se 2 (by rfl) ⟨736173, by rfl⟩ : syracuseStep 1963129 = 1472347) B1472347
theorem B7861535 : Blo 1032607 7861535 := bstep (se 1 (by rfl) ⟨5896151, by rfl⟩ : syracuseStep 7861535 = 11792303) B11792303
theorem B1307983 : Blo 1032607 1307983 := bstep (se 1 (by rfl) ⟨980987, by rfl⟩ : syracuseStep 1307983 = 1961975) B1961975
theorem B1865423 : Blo 1032607 1865423 := bstep (se 1 (by rfl) ⟨1399067, by rfl⟩ : syracuseStep 1865423 = 2798135) B2798135
theorem B95647715 : Blo 1032607 95647715 := bstep (se 1 (by rfl) ⟨71735786, by rfl⟩ : syracuseStep 95647715 = 143471573) B143471573
theorem B8845321 : Blo 1032607 8845321 := bstep (se 2 (by rfl) ⟨3316995, by rfl⟩ : syracuseStep 8845321 = 6633991) B6633991
theorem B1964063 : Blo 1032607 1964063 := bstep (se 1 (by rfl) ⟨1473047, by rfl⟩ : syracuseStep 1964063 = 2946095) B2946095
theorem B13236817 : Blo 1032607 13236817 := bstep (se 2 (by rfl) ⟨4963806, by rfl⟩ : syracuseStep 13236817 = 9927613) B9927613
theorem B3930875 : Blo 1032607 3930875 := bstep (se 1 (by rfl) ⟨2948156, by rfl⟩ : syracuseStep 3930875 = 5896313) B5896313
theorem B1964807 : Blo 1032607 1964807 := bstep (se 1 (by rfl) ⟨1473605, by rfl⟩ : syracuseStep 1964807 = 2947211) B2947211
theorem B2652983 : Blo 1032607 2652983 := bstep (se 1 (by rfl) ⟨1989737, by rfl⟩ : syracuseStep 2652983 = 3979475) B3979475
theorem B5307275 : Blo 1032607 5307275 := bstep (se 1 (by rfl) ⟨3980456, by rfl⟩ : syracuseStep 5307275 = 7960913) B7960913
theorem B3931163 : Blo 1032607 3931163 := bstep (se 1 (by rfl) ⟨2948372, by rfl⟩ : syracuseStep 3931163 = 5896745) B5896745
theorem B30211177 : Blo 1032607 30211177 := bstep (se 2 (by rfl) ⟨11329191, by rfl⟩ : syracuseStep 30211177 = 22658383) B22658383
theorem B3931361 : Blo 1032607 3931361 := bstep (se 2 (by rfl) ⟨1474260, by rfl⟩ : syracuseStep 3931361 = 2948521) B2948521
theorem B2325779 : Blo 1032607 2325779 := bstep (se 1 (by rfl) ⟨1744334, by rfl⟩ : syracuseStep 2325779 = 3488669) B3488669
theorem B1310023 : Blo 1032607 1310023 := bstep (se 1 (by rfl) ⟨982517, by rfl⟩ : syracuseStep 1310023 = 1965035) B1965035
theorem B16809419 : Blo 1032607 16809419 := bstep (se 1 (by rfl) ⟨12607064, by rfl⟩ : syracuseStep 16809419 = 25214129) B25214129
theorem B1965559 : Blo 1032607 1965559 := bstep (se 1 (by rfl) ⟨1474169, by rfl⟩ : syracuseStep 1965559 = 2948339) B2948339
theorem B2621099 : Blo 1032607 2621099 := bstep (se 1 (by rfl) ⟨1965824, by rfl⟩ : syracuseStep 2621099 = 3931649) B3931649
theorem B181567169 : Blo 1032607 181567169 := bstep (se 2 (by rfl) ⟨68087688, by rfl⟩ : syracuseStep 181567169 = 136175377) B136175377
theorem B2621281 : Blo 1032607 2621281 := bstep (se 2 (by rfl) ⟨982980, by rfl⟩ : syracuseStep 2621281 = 1965961) B1965961
theorem B22708187 : Blo 1032607 22708187 := bstep (se 1 (by rfl) ⟨17031140, by rfl⟩ : syracuseStep 22708187 = 34062281) B34062281
theorem B22347859 : Blo 1032607 22347859 := bstep (se 1 (by rfl) ⟨16760894, by rfl⟩ : syracuseStep 22347859 = 33521789) B33521789
theorem B2326625 : Blo 1032607 2326625 := bstep (se 2 (by rfl) ⟨872484, by rfl⟩ : syracuseStep 2326625 = 1744969) B1744969
theorem B2326841 : Blo 1032607 2326841 := bstep (se 2 (by rfl) ⟨872565, by rfl⟩ : syracuseStep 2326841 = 1745131) B1745131
theorem B2949979 : Blo 1032607 2949979 := bstep (se 1 (by rfl) ⟨2212484, by rfl⟩ : syracuseStep 2949979 = 4424969) B4424969
theorem B2327417 : Blo 1032607 2327417 := bstep (se 2 (by rfl) ⟨872781, by rfl⟩ : syracuseStep 2327417 = 1745563) B1745563
theorem B6620231 : Blo 1032607 6620231 := bstep (se 1 (by rfl) ⟨4965173, by rfl⟩ : syracuseStep 6620231 = 9930347) B9930347
theorem B5244425 : Blo 1032607 5244425 := bstep (se 2 (by rfl) ⟨1966659, by rfl⟩ : syracuseStep 5244425 = 3933319) B3933319
theorem B2623387 : Blo 1032607 2623387 := bstep (se 1 (by rfl) ⟨1967540, by rfl⟩ : syracuseStep 2623387 = 3935081) B3935081
theorem B5244911 : Blo 1032607 5244911 := bstep (se 1 (by rfl) ⟨3933683, by rfl⟩ : syracuseStep 5244911 = 7867367) B7867367
theorem B2328569 : Blo 1032607 2328569 := bstep (se 2 (by rfl) ⟨873213, by rfl⟩ : syracuseStep 2328569 = 1746427) B1746427
theorem B5900435 : Blo 1032607 5900435 := bstep (se 1 (by rfl) ⟨4425326, by rfl⟩ : syracuseStep 5900435 = 8850653) B8850653
theorem B2328839 : Blo 1032607 2328839 := bstep (se 1 (by rfl) ⟨1746629, by rfl⟩ : syracuseStep 2328839 = 3493259) B3493259
theorem B5245721 : Blo 1032607 5245721 := bstep (se 2 (by rfl) ⟨1967145, by rfl⟩ : syracuseStep 5245721 = 3934291) B3934291
theorem B2329415 : Blo 1032607 2329415 := bstep (se 1 (by rfl) ⟨1747061, by rfl⟩ : syracuseStep 2329415 = 3494123) B3494123
theorem B1576073 : Blo 1032607 1576073 := bstep (se 2 (by rfl) ⟨591027, by rfl⟩ : syracuseStep 1576073 = 1182055) B1182055
theorem B1576127 : Blo 1032607 1576127 := bstep (se 1 (by rfl) ⟨1182095, by rfl⟩ : syracuseStep 1576127 = 2364191) B2364191
theorem B2330063 : Blo 1032607 2330063 := bstep (se 1 (by rfl) ⟨1747547, by rfl⟩ : syracuseStep 2330063 = 3495095) B3495095
theorem B22384187 : Blo 1032607 22384187 := bstep (se 1 (by rfl) ⟨16788140, by rfl⟩ : syracuseStep 22384187 = 33576281) B33576281
theorem B2330279 : Blo 1032607 2330279 := bstep (se 1 (by rfl) ⟨1747709, by rfl⟩ : syracuseStep 2330279 = 3495419) B3495419
theorem B2100919 : Blo 1032607 2100919 := bstep (se 1 (by rfl) ⟨1575689, by rfl⟩ : syracuseStep 2100919 = 3151379) B3151379
theorem B2330351 : Blo 1032607 2330351 := bstep (se 1 (by rfl) ⟨1747763, by rfl⟩ : syracuseStep 2330351 = 3495527) B3495527
theorem B8851679 : Blo 1032607 8851679 := bstep (se 1 (by rfl) ⟨6638759, by rfl⟩ : syracuseStep 8851679 = 13277519) B13277519
theorem B2330927 : Blo 1032607 2330927 := bstep (se 1 (by rfl) ⟨1748195, by rfl⟩ : syracuseStep 2330927 = 3496391) B3496391
theorem B7869311 : Blo 1032607 7869311 := bstep (se 1 (by rfl) ⟨5901983, by rfl⟩ : syracuseStep 7869311 = 11803967) B11803967
theorem B2332025 : Blo 1032607 2332025 := bstep (se 2 (by rfl) ⟨874509, by rfl⟩ : syracuseStep 2332025 = 1749019) B1749019
theorem B2332115 : Blo 1032607 2332115 := bstep (se 1 (by rfl) ⟨1749086, by rfl⟩ : syracuseStep 2332115 = 3498173) B3498173
theorem B42472997 : Blo 1032607 42472997 := bstep (se 4 (by rfl) ⟨3981843, by rfl⟩ : syracuseStep 42472997 = 7963687) B7963687
theorem B2332223 : Blo 1032607 2332223 := bstep (se 1 (by rfl) ⟨1749167, by rfl⟩ : syracuseStep 2332223 = 3498335) B3498335
theorem B3315305 : Blo 1032607 3315305 := bstep (se 2 (by rfl) ⟨1243239, by rfl⟩ : syracuseStep 3315305 = 2486479) B2486479
theorem B1743977 : Blo 1032607 1743977 := bstep (se 2 (by rfl) ⟨653991, by rfl⟩ : syracuseStep 1743977 = 1307983) B1307983
theorem B5316029 : Blo 1032607 5316029 := bstep (se 3 (by rfl) ⟨996755, by rfl⟩ : syracuseStep 5316029 = 1993511) B1993511
theorem B2235959 : Blo 1032607 2235959 := bstep (se 1 (by rfl) ⟨1676969, by rfl⟩ : syracuseStep 2235959 = 3353939) B3353939
theorem B2302175 : Blo 1032607 2302175 := bstep (se 1 (by rfl) ⟨1726631, by rfl⟩ : syracuseStep 2302175 = 3453263) B3453263
theorem B4727945 : Blo 1032607 4727945 := bstep (se 2 (by rfl) ⟨1772979, by rfl⟩ : syracuseStep 4727945 = 3545959) B3545959
theorem B40281569 : Blo 1032607 40281569 := bstep (se 2 (by rfl) ⟨15105588, by rfl⟩ : syracuseStep 40281569 = 30211177) B30211177
theorem B9709075 : Blo 1032607 9709075 := bstep (se 1 (by rfl) ⟨7281806, by rfl⟩ : syracuseStep 9709075 = 14563613) B14563613
theorem B1746697 : Blo 1032607 1746697 := bstep (se 2 (by rfl) ⟨655011, by rfl⟩ : syracuseStep 1746697 = 1310023) B1310023
theorem B1550519 : Blo 1032607 1550519 := bstep (se 1 (by rfl) ⟨1162889, by rfl⟩ : syracuseStep 1550519 = 2325779) B2325779
theorem B6629687 : Blo 1032607 6629687 := bstep (se 1 (by rfl) ⟨4972265, by rfl⟩ : syracuseStep 6629687 = 9944531) B9944531
theorem B1747399 : Blo 1032607 1747399 := bstep (se 1 (by rfl) ⟨1310549, by rfl⟩ : syracuseStep 1747399 = 2621099) B2621099
theorem B12758161 : Blo 1032607 12758161 := bstep (se 2 (by rfl) ⟨4784310, by rfl⟩ : syracuseStep 12758161 = 9568621) B9568621
theorem B2797409 : Blo 1032607 2797409 := bstep (se 2 (by rfl) ⟨1049028, by rfl⟩ : syracuseStep 2797409 = 2098057) B2098057
theorem B1552505 : Blo 1032607 1552505 := bstep (se 2 (by rfl) ⟨582189, by rfl⟩ : syracuseStep 1552505 = 1164379) B1164379
theorem B8958107 : Blo 1032607 8958107 := bstep (se 1 (by rfl) ⟨6718580, by rfl⟩ : syracuseStep 8958107 = 13437161) B13437161
theorem B1552553 : Blo 1032607 1552553 := bstep (se 2 (by rfl) ⟨582207, by rfl⟩ : syracuseStep 1552553 = 1164415) B1164415
theorem B3485915 : Blo 1032607 3485915 := bstep (se 1 (by rfl) ⟨2614436, by rfl⟩ : syracuseStep 3485915 = 5228873) B5228873
theorem B5583161 : Blo 1032607 5583161 := bstep (se 2 (by rfl) ⟨2093685, by rfl⟩ : syracuseStep 5583161 = 4187371) B4187371
theorem B3486023 : Blo 1032607 3486023 := bstep (se 1 (by rfl) ⟨2614517, by rfl⟩ : syracuseStep 3486023 = 5229035) B5229035
theorem B2044457 : Blo 1032607 2044457 := bstep (se 2 (by rfl) ⟨766671, by rfl⟩ : syracuseStep 2044457 = 1533343) B1533343
theorem B13251275 : Blo 1032607 13251275 := bstep (se 1 (by rfl) ⟨9938456, by rfl⟩ : syracuseStep 13251275 = 19876913) B19876913
theorem B1553279 : Blo 1032607 1553279 := bstep (se 1 (by rfl) ⟨1164959, by rfl⟩ : syracuseStep 1553279 = 2329919) B2329919
theorem B1554089 : Blo 1032607 1554089 := bstep (se 2 (by rfl) ⟨582783, by rfl⟩ : syracuseStep 1554089 = 1165567) B1165567
theorem B3487643 : Blo 1032607 3487643 := bstep (se 1 (by rfl) ⟨2615732, by rfl⟩ : syracuseStep 3487643 = 5231465) B5231465
theorem B7845983 : Blo 1032607 7845983 := bstep (se 1 (by rfl) ⟨5884487, by rfl⟩ : syracuseStep 7845983 = 11768975) B11768975
theorem B26917049 : Blo 1032607 26917049 := bstep (se 2 (by rfl) ⟨10093893, by rfl⟩ : syracuseStep 26917049 = 20187787) B20187787
theorem B1554791 : Blo 1032607 1554791 := bstep (se 1 (by rfl) ⟨1166093, by rfl⟩ : syracuseStep 1554791 = 2332187) B2332187
theorem B12598699 : Blo 1032607 12598699 := bstep (se 1 (by rfl) ⟨9449024, by rfl⟩ : syracuseStep 12598699 = 18898049) B18898049
theorem B29867723 : Blo 1032607 29867723 := bstep (se 1 (by rfl) ⟨22400792, by rfl⟩ : syracuseStep 29867723 = 44801585) B44801585
theorem B6635479 : Blo 1032607 6635479 := bstep (se 1 (by rfl) ⟨4976609, by rfl⟩ : syracuseStep 6635479 = 9953219) B9953219
theorem B5587051 : Blo 1032607 5587051 := bstep (se 1 (by rfl) ⟨4190288, by rfl⟩ : syracuseStep 5587051 = 8380577) B8380577
theorem B1033087 : Blo 1032607 1033087 := bstep (se 1 (by rfl) ⟨774815, by rfl⟩ : syracuseStep 1033087 = 1549631) B1549631
theorem B1033119 : Blo 1032607 1033119 := bstep (se 1 (by rfl) ⟨774839, by rfl⟩ : syracuseStep 1033119 = 1549679) B1549679
theorem B1033199 : Blo 1032607 1033199 := bstep (se 1 (by rfl) ⟨774899, by rfl⟩ : syracuseStep 1033199 = 1549799) B1549799
theorem B1033287 : Blo 1032607 1033287 := bstep (se 1 (by rfl) ⟨774965, by rfl⟩ : syracuseStep 1033287 = 1549931) B1549931
theorem B1033319 : Blo 1032607 1033319 := bstep (se 1 (by rfl) ⟨774989, by rfl⟩ : syracuseStep 1033319 = 1549979) B1549979
theorem B1033599 : Blo 1032607 1033599 := bstep (se 1 (by rfl) ⟨775199, by rfl⟩ : syracuseStep 1033599 = 1550399) B1550399
theorem B5588435 : Blo 1032607 5588435 := bstep (se 1 (by rfl) ⟨4191326, by rfl⟩ : syracuseStep 5588435 = 8382653) B8382653
theorem B1033695 : Blo 1032607 1033695 := bstep (se 1 (by rfl) ⟨775271, by rfl⟩ : syracuseStep 1033695 = 1550543) B1550543
theorem B1033775 : Blo 1032607 1033775 := bstep (se 1 (by rfl) ⟨775331, by rfl⟩ : syracuseStep 1033775 = 1550663) B1550663
theorem B1164955 : Blo 1032607 1164955 := bstep (se 1 (by rfl) ⟨873716, by rfl⟩ : syracuseStep 1164955 = 1747433) B1747433
theorem B1033967 : Blo 1032607 1033967 := bstep (se 1 (by rfl) ⟨775475, by rfl⟩ : syracuseStep 1033967 = 1550951) B1550951
theorem B1034331 : Blo 1032607 1034331 := bstep (se 1 (by rfl) ⟨775748, by rfl⟩ : syracuseStep 1034331 = 1551497) B1551497
theorem B1034367 : Blo 1032607 1034367 := bstep (se 1 (by rfl) ⟨775775, by rfl⟩ : syracuseStep 1034367 = 1551551) B1551551
theorem B1166107 : Blo 1032607 1166107 := bstep (se 1 (by rfl) ⟨874580, by rfl⟩ : syracuseStep 1166107 = 1749161) B1749161
theorem B3492935 : Blo 1032607 3492935 := bstep (se 1 (by rfl) ⟨2619701, by rfl⟩ : syracuseStep 3492935 = 5239403) B5239403
theorem B17649089 : Blo 1032607 17649089 := bstep (se 2 (by rfl) ⟨6618408, by rfl⟩ : syracuseStep 17649089 = 13236817) B13236817
theorem B1035823 : Blo 1032607 1035823 := bstep (se 1 (by rfl) ⟨776867, by rfl⟩ : syracuseStep 1035823 = 1553735) B1553735
theorem B5886107 : Blo 1032607 5886107 := bstep (se 1 (by rfl) ⟨4414580, by rfl⟩ : syracuseStep 5886107 = 8829161) B8829161
theorem B3920987 : Blo 1032607 3920987 := bstep (se 1 (by rfl) ⟨2940740, by rfl⟩ : syracuseStep 3920987 = 5881481) B5881481
theorem B3495041 : Blo 1032607 3495041 := bstep (se 2 (by rfl) ⟨1310640, by rfl⟩ : syracuseStep 3495041 = 2621281) B2621281
theorem B5232761 : Blo 1032607 5232761 := bstep (se 2 (by rfl) ⟨1962285, by rfl⟩ : syracuseStep 5232761 = 3924571) B3924571
theorem B3987791 : Blo 1032607 3987791 := bstep (se 1 (by rfl) ⟨2990843, by rfl⟩ : syracuseStep 3987791 = 5981687) B5981687
theorem B3496715 : Blo 1032607 3496715 := bstep (se 1 (by rfl) ⟨2622536, by rfl⟩ : syracuseStep 3496715 = 5245073) B5245073
theorem B12737351 : Blo 1032607 12737351 := bstep (se 1 (by rfl) ⟨9553013, by rfl⟩ : syracuseStep 12737351 = 19106027) B19106027
theorem B5660351 : Blo 1032607 5660351 := bstep (se 1 (by rfl) ⟨4245263, by rfl⟩ : syracuseStep 5660351 = 8490527) B8490527
theorem B10084121 : Blo 1032607 10084121 := bstep (se 2 (by rfl) ⟨3781545, by rfl⟩ : syracuseStep 10084121 = 7563091) B7563091
theorem B33972311 : Blo 1032607 33972311 := bstep (se 1 (by rfl) ⟨25479233, by rfl⟩ : syracuseStep 33972311 = 50958467) B50958467
theorem B6283487 : Blo 1032607 6283487 := bstep (se 1 (by rfl) ⟨4712615, by rfl⟩ : syracuseStep 6283487 = 9425231) B9425231
theorem B40297139 : Blo 1032607 40297139 := bstep (se 1 (by rfl) ⟨30222854, by rfl⟩ : syracuseStep 40297139 = 60445709) B60445709
theorem B5890913 : Blo 1032607 5890913 := bstep (se 2 (by rfl) ⟨2209092, by rfl⟩ : syracuseStep 5890913 = 4418185) B4418185
theorem B7857161 : Blo 1032607 7857161 := bstep (se 2 (by rfl) ⟨2946435, by rfl⟩ : syracuseStep 7857161 = 5892871) B5892871
theorem B3925331 : Blo 1032607 3925331 := bstep (se 1 (by rfl) ⟨2943998, by rfl⟩ : syracuseStep 3925331 = 5887997) B5887997
theorem B3728969 : Blo 1032607 3728969 := bstep (se 2 (by rfl) ⟨1398363, by rfl⟩ : syracuseStep 3728969 = 2796727) B2796727
theorem B2614913 : Blo 1032607 2614913 := bstep (se 2 (by rfl) ⟨980592, by rfl⟩ : syracuseStep 2614913 = 1961185) B1961185
theorem B4187809 : Blo 1032607 4187809 := bstep (se 2 (by rfl) ⟨1570428, by rfl⟩ : syracuseStep 4187809 = 3140857) B3140857
theorem B2942689 : Blo 1032607 2942689 := bstep (se 2 (by rfl) ⟨1103508, by rfl⟩ : syracuseStep 2942689 = 2207017) B2207017
theorem B7858619 : Blo 1032607 7858619 := bstep (se 1 (by rfl) ⟨5893964, by rfl⟩ : syracuseStep 7858619 = 11787929) B11787929
theorem B23849417 : Blo 1032607 23849417 := bstep (se 2 (by rfl) ⟨8943531, by rfl⟩ : syracuseStep 23849417 = 17887063) B17887063
theorem B22669895 : Blo 1032607 22669895 := bstep (se 1 (by rfl) ⟨17002421, by rfl⟩ : syracuseStep 22669895 = 34004843) B34004843
theorem B11168873 : Blo 1032607 11168873 := bstep (se 2 (by rfl) ⟨4188327, by rfl⟩ : syracuseStep 11168873 = 8376655) B8376655
theorem B3927305 : Blo 1032607 3927305 := bstep (se 2 (by rfl) ⟨1472739, by rfl⟩ : syracuseStep 3927305 = 2945479) B2945479
theorem B2944363 : Blo 1032607 2944363 := bstep (se 1 (by rfl) ⟨2208272, by rfl⟩ : syracuseStep 2944363 = 4416545) B4416545
theorem B3927487 : Blo 1032607 3927487 := bstep (se 1 (by rfl) ⟨2945615, by rfl⟩ : syracuseStep 3927487 = 5891231) B5891231
theorem B2617505 : Blo 1032607 2617505 := bstep (se 2 (by rfl) ⟨981564, by rfl⟩ : syracuseStep 2617505 = 1963129) B1963129
theorem B3928763 : Blo 1032607 3928763 := bstep (se 1 (by rfl) ⟨2946572, by rfl⟩ : syracuseStep 3928763 = 5893145) B5893145
theorem B1307431 : Blo 1032607 1307431 := bstep (se 1 (by rfl) ⟨980573, by rfl⟩ : syracuseStep 1307431 = 1961147) B1961147
theorem B2323439 : Blo 1032607 2323439 := bstep (se 1 (by rfl) ⟨1742579, by rfl⟩ : syracuseStep 2323439 = 3485159) B3485159
theorem B11793761 : Blo 1032607 11793761 := bstep (se 2 (by rfl) ⟨4422660, by rfl⟩ : syracuseStep 11793761 = 8845321) B8845321
theorem B5895787 : Blo 1032607 5895787 := bstep (se 1 (by rfl) ⟨4421840, by rfl⟩ : syracuseStep 5895787 = 8843681) B8843681
theorem B2324123 : Blo 1032607 2324123 := bstep (se 1 (by rfl) ⟨1743092, by rfl⟩ : syracuseStep 2324123 = 3486185) B3486185
theorem B5896061 : Blo 1032607 5896061 := bstep (se 3 (by rfl) ⟨1105511, by rfl⟩ : syracuseStep 5896061 = 2211023) B2211023
theorem B1308575 : Blo 1032607 1308575 := bstep (se 1 (by rfl) ⟨981431, by rfl⟩ : syracuseStep 1308575 = 1962863) B1962863
theorem B77559761 : Blo 1032607 77559761 := bstep (se 2 (by rfl) ⟨29084910, by rfl⟩ : syracuseStep 77559761 = 58169821) B58169821
theorem B5241023 : Blo 1032607 5241023 := bstep (se 1 (by rfl) ⟨3930767, by rfl⟩ : syracuseStep 5241023 = 7861535) B7861535
theorem B1243615 : Blo 1032607 1243615 := bstep (se 1 (by rfl) ⟨932711, by rfl⟩ : syracuseStep 1243615 = 1865423) B1865423
theorem B63765143 : Blo 1032607 63765143 := bstep (se 1 (by rfl) ⟨47823857, by rfl⟩ : syracuseStep 63765143 = 95647715) B95647715
theorem B1309375 : Blo 1032607 1309375 := bstep (se 1 (by rfl) ⟨982031, by rfl⟩ : syracuseStep 1309375 = 1964063) B1964063
theorem B1473275 : Blo 1032607 1473275 := bstep (se 1 (by rfl) ⟨1104956, by rfl⟩ : syracuseStep 1473275 = 2209913) B2209913
theorem B2620583 : Blo 1032607 2620583 := bstep (se 1 (by rfl) ⟨1965437, by rfl⟩ : syracuseStep 2620583 = 3930875) B3930875
theorem B1309871 : Blo 1032607 1309871 := bstep (se 1 (by rfl) ⟨982403, by rfl⟩ : syracuseStep 1309871 = 1964807) B1964807
theorem B1768655 : Blo 1032607 1768655 := bstep (se 1 (by rfl) ⟨1326491, by rfl⟩ : syracuseStep 1768655 = 2652983) B2652983
theorem B2325743 : Blo 1032607 2325743 := bstep (se 1 (by rfl) ⟨1744307, by rfl⟩ : syracuseStep 2325743 = 3488615) B3488615
theorem B3538183 : Blo 1032607 3538183 := bstep (se 1 (by rfl) ⟨2653637, by rfl⟩ : syracuseStep 3538183 = 5307275) B5307275
theorem B2620745 : Blo 1032607 2620745 := bstep (se 2 (by rfl) ⟨982779, by rfl⟩ : syracuseStep 2620745 = 1965559) B1965559
theorem B2620775 : Blo 1032607 2620775 := bstep (se 1 (by rfl) ⟨1965581, by rfl⟩ : syracuseStep 2620775 = 3931163) B3931163
theorem B11763143 : Blo 1032607 11763143 := bstep (se 1 (by rfl) ⟨8822357, by rfl⟩ : syracuseStep 11763143 = 17644715) B17644715
theorem B2620907 : Blo 1032607 2620907 := bstep (se 1 (by rfl) ⟨1965680, by rfl⟩ : syracuseStep 2620907 = 3931361) B3931361
theorem B11206279 : Blo 1032607 11206279 := bstep (se 1 (by rfl) ⟨8404709, by rfl⟩ : syracuseStep 11206279 = 16809419) B16809419
theorem B2326175 : Blo 1032607 2326175 := bstep (se 1 (by rfl) ⟨1744631, by rfl⟩ : syracuseStep 2326175 = 3489263) B3489263
theorem B121044779 : Blo 1032607 121044779 := bstep (se 1 (by rfl) ⟨90783584, by rfl⟩ : syracuseStep 121044779 = 181567169) B181567169
theorem B15138791 : Blo 1032607 15138791 := bstep (se 1 (by rfl) ⟨11354093, by rfl⟩ : syracuseStep 15138791 = 22708187) B22708187
theorem B3933305 : Blo 1032607 3933305 := bstep (se 2 (by rfl) ⟨1474989, by rfl⟩ : syracuseStep 3933305 = 2949979) B2949979
theorem B3933623 : Blo 1032607 3933623 := bstep (se 1 (by rfl) ⟨2950217, by rfl⟩ : syracuseStep 3933623 = 5900435) B5900435
theorem B2328623 : Blo 1032607 2328623 := bstep (se 1 (by rfl) ⟨1746467, by rfl⟩ : syracuseStep 2328623 = 3492935) B3492935
theorem B1050715 : Blo 1032607 1050715 := bstep (se 1 (by rfl) ⟨788036, by rfl⟩ : syracuseStep 1050715 = 1576073) B1576073
theorem B1050751 : Blo 1032607 1050751 := bstep (se 1 (by rfl) ⟨788063, by rfl⟩ : syracuseStep 1050751 = 1576127) B1576127
theorem B11766059 : Blo 1032607 11766059 := bstep (se 1 (by rfl) ⟨8824544, by rfl⟩ : syracuseStep 11766059 = 17649089) B17649089
theorem B2328929 : Blo 1032607 2328929 := bstep (se 2 (by rfl) ⟨873348, by rfl⟩ : syracuseStep 2328929 = 1746697) B1746697
theorem B5901119 : Blo 1032607 5901119 := bstep (se 1 (by rfl) ⟨4425839, by rfl⟩ : syracuseStep 5901119 = 8851679) B8851679
theorem B5246207 : Blo 1032607 5246207 := bstep (se 1 (by rfl) ⟨3934655, by rfl⟩ : syracuseStep 5246207 = 7869311) B7869311
theorem B2329865 : Blo 1032607 2329865 := bstep (se 2 (by rfl) ⟨873699, by rfl⟩ : syracuseStep 2329865 = 1747399) B1747399
theorem B2330027 : Blo 1032607 2330027 := bstep (se 1 (by rfl) ⟨1747520, by rfl⟩ : syracuseStep 2330027 = 3495041) B3495041
theorem B28315331 : Blo 1032607 28315331 := bstep (se 1 (by rfl) ⟨21236498, by rfl⟩ : syracuseStep 28315331 = 42472997) B42472997
theorem B17010881 : Blo 1032607 17010881 := bstep (se 2 (by rfl) ⟨6379080, by rfl⟩ : syracuseStep 17010881 = 12758161) B12758161
theorem B2658527 : Blo 1032607 2658527 := bstep (se 1 (by rfl) ⟨1993895, by rfl⟩ : syracuseStep 2658527 = 3987791) B3987791
theorem B2331143 : Blo 1032607 2331143 := bstep (se 1 (by rfl) ⟨1748357, by rfl⟩ : syracuseStep 2331143 = 3496715) B3496715
theorem B8491567 : Blo 1032607 8491567 := bstep (se 1 (by rfl) ⟨6368675, by rfl⟩ : syracuseStep 8491567 = 12737351) B12737351
theorem B3544019 : Blo 1032607 3544019 := bstep (se 1 (by rfl) ⟨2658014, by rfl⟩ : syracuseStep 3544019 = 5316029) B5316029
theorem B3773567 : Blo 1032607 3773567 := bstep (se 1 (by rfl) ⟨2830175, by rfl⟩ : syracuseStep 3773567 = 5660351) B5660351
theorem B6722747 : Blo 1032607 6722747 := bstep (se 1 (by rfl) ⟨5042060, by rfl⟩ : syracuseStep 6722747 = 10084121) B10084121
theorem B22648207 : Blo 1032607 22648207 := bstep (se 1 (by rfl) ⟨16986155, by rfl⟩ : syracuseStep 22648207 = 33972311) B33972311
theorem B3151963 : Blo 1032607 3151963 := bstep (se 1 (by rfl) ⟨2363972, by rfl⟩ : syracuseStep 3151963 = 4727945) B4727945
theorem B1743241 : Blo 1032607 1743241 := bstep (se 2 (by rfl) ⟨653715, by rfl⟩ : syracuseStep 1743241 = 1307431) B1307431
theorem B1743275 : Blo 1032607 1743275 := bstep (se 1 (by rfl) ⟨1307456, by rfl⟩ : syracuseStep 1743275 = 2614913) B2614913
theorem B15899611 : Blo 1032607 15899611 := bstep (se 1 (by rfl) ⟨11924708, by rfl⟩ : syracuseStep 15899611 = 23849417) B23849417
theorem B15113263 : Blo 1032607 15113263 := bstep (se 1 (by rfl) ⟨11334947, by rfl⟩ : syracuseStep 15113263 = 22669895) B22669895
theorem B7445915 : Blo 1032607 7445915 := bstep (se 1 (by rfl) ⟨5584436, by rfl⟩ : syracuseStep 7445915 = 11168873) B11168873
theorem B51781733 : Blo 1032607 51781733 := bstep (se 4 (by rfl) ⟨4854537, by rfl⟩ : syracuseStep 51781733 = 9709075) B9709075
theorem B5972071 : Blo 1032607 5972071 := bstep (se 1 (by rfl) ⟨4479053, by rfl⟩ : syracuseStep 5972071 = 8958107) B8958107
theorem B1745003 : Blo 1032607 1745003 := bstep (se 1 (by rfl) ⟨1308752, by rfl⟩ : syracuseStep 1745003 = 2617505) B2617505
theorem B1548959 : Blo 1032607 1548959 := bstep (se 1 (by rfl) ⟨1161719, by rfl⟩ : syracuseStep 1548959 = 2323439) B2323439
theorem B1745833 : Blo 1032607 1745833 := bstep (se 2 (by rfl) ⟨654687, by rfl⟩ : syracuseStep 1745833 = 1309375) B1309375
theorem B1549415 : Blo 1032607 1549415 := bstep (se 1 (by rfl) ⟨1162061, by rfl⟩ : syracuseStep 1549415 = 2324123) B2324123
theorem B42510095 : Blo 1032607 42510095 := bstep (se 1 (by rfl) ⟨31882571, by rfl⟩ : syracuseStep 42510095 = 63765143) B63765143
theorem B1747055 : Blo 1032607 1747055 := bstep (se 1 (by rfl) ⟨1310291, by rfl⟩ : syracuseStep 1747055 = 2620583) B2620583
theorem B1550495 : Blo 1032607 1550495 := bstep (se 1 (by rfl) ⟨1162871, by rfl⟩ : syracuseStep 1550495 = 2325743) B2325743
theorem B1747163 : Blo 1032607 1747163 := bstep (se 1 (by rfl) ⟨1310372, by rfl⟩ : syracuseStep 1747163 = 2620745) B2620745
theorem B1747183 : Blo 1032607 1747183 := bstep (se 1 (by rfl) ⟨1310387, by rfl⟩ : syracuseStep 1747183 = 2620775) B2620775
theorem B7842095 : Blo 1032607 7842095 := bstep (se 1 (by rfl) ⟨5881571, by rfl⟩ : syracuseStep 7842095 = 11763143) B11763143
theorem B1747271 : Blo 1032607 1747271 := bstep (se 1 (by rfl) ⟨1310453, by rfl⟩ : syracuseStep 1747271 = 2620907) B2620907
theorem B1550783 : Blo 1032607 1550783 := bstep (se 1 (by rfl) ⟨1163087, by rfl⟩ : syracuseStep 1550783 = 2326175) B2326175
theorem B1551083 : Blo 1032607 1551083 := bstep (se 1 (by rfl) ⟨1163312, by rfl⟩ : syracuseStep 1551083 = 2326625) B2326625
theorem B29797145 : Blo 1032607 29797145 := bstep (se 2 (by rfl) ⟨11173929, by rfl⟩ : syracuseStep 29797145 = 22347859) B22347859
theorem B7449401 : Blo 1032607 7449401 := bstep (se 2 (by rfl) ⟨2793525, by rfl⟩ : syracuseStep 7449401 = 5587051) B5587051
theorem B1551227 : Blo 1032607 1551227 := bstep (se 1 (by rfl) ⟨1163420, by rfl⟩ : syracuseStep 1551227 = 2326841) B2326841
theorem B1551611 : Blo 1032607 1551611 := bstep (se 1 (by rfl) ⟨1163708, by rfl⟩ : syracuseStep 1551611 = 2327417) B2327417
theorem B6139133 : Blo 1032607 6139133 := bstep (se 3 (by rfl) ⟨1151087, by rfl⟩ : syracuseStep 6139133 = 2302175) B2302175
theorem B1552379 : Blo 1032607 1552379 := bstep (se 1 (by rfl) ⟨1164284, by rfl⟩ : syracuseStep 1552379 = 2328569) B2328569
theorem B1552559 : Blo 1032607 1552559 := bstep (se 1 (by rfl) ⟨1164419, by rfl⟩ : syracuseStep 1552559 = 2328839) B2328839
theorem B1552943 : Blo 1032607 1552943 := bstep (se 1 (by rfl) ⟨1164707, by rfl⟩ : syracuseStep 1552943 = 2329415) B2329415
theorem B1553273 : Blo 1032607 1553273 := bstep (se 2 (by rfl) ⟨582477, by rfl⟩ : syracuseStep 1553273 = 1164955) B1164955
theorem B5583745 : Blo 1032607 5583745 := bstep (se 2 (by rfl) ⟨2093904, by rfl⟩ : syracuseStep 5583745 = 4187809) B4187809
theorem B1553375 : Blo 1032607 1553375 := bstep (se 1 (by rfl) ⟨1165031, by rfl⟩ : syracuseStep 1553375 = 2330063) B2330063
theorem B14922791 : Blo 1032607 14922791 := bstep (se 1 (by rfl) ⟨11192093, by rfl⟩ : syracuseStep 14922791 = 22384187) B22384187
theorem B1553519 : Blo 1032607 1553519 := bstep (se 1 (by rfl) ⟨1165139, by rfl⟩ : syracuseStep 1553519 = 2330279) B2330279
theorem B1553567 : Blo 1032607 1553567 := bstep (se 1 (by rfl) ⟨1165175, by rfl⟩ : syracuseStep 1553567 = 2330351) B2330351
theorem B1553951 : Blo 1032607 1553951 := bstep (se 1 (by rfl) ⟨1165463, by rfl⟩ : syracuseStep 1553951 = 2330927) B2330927
theorem B1554683 : Blo 1032607 1554683 := bstep (se 1 (by rfl) ⟨1166012, by rfl⟩ : syracuseStep 1554683 = 2332025) B2332025
theorem B1554743 : Blo 1032607 1554743 := bstep (se 1 (by rfl) ⟨1166057, by rfl⟩ : syracuseStep 1554743 = 2332115) B2332115
theorem B1554809 : Blo 1032607 1554809 := bstep (se 2 (by rfl) ⟨583053, by rfl⟩ : syracuseStep 1554809 = 1166107) B1166107
theorem B1554815 : Blo 1032607 1554815 := bstep (se 1 (by rfl) ⟨1166111, by rfl⟩ : syracuseStep 1554815 = 2332223) B2332223
theorem B2210203 : Blo 1032607 2210203 := bstep (se 1 (by rfl) ⟨1657652, by rfl⟩ : syracuseStep 2210203 = 3315305) B3315305
theorem B3488507 : Blo 1032607 3488507 := bstep (se 1 (by rfl) ⟨2616380, by rfl⟩ : syracuseStep 3488507 = 5232761) B5232761
theorem B1162651 : Blo 1032607 1162651 := bstep (se 1 (by rfl) ⟨871988, by rfl⟩ : syracuseStep 1162651 = 1743977) B1743977
theorem B2801225 : Blo 1032607 2801225 := bstep (se 2 (by rfl) ⟨1050459, by rfl⟩ : syracuseStep 2801225 = 2100919) B2100919
theorem B1490639 : Blo 1032607 1490639 := bstep (se 1 (by rfl) ⟨1117979, by rfl⟩ : syracuseStep 1490639 = 2235959) B2235959
theorem B3489533 : Blo 1032607 3489533 := bstep (se 3 (by rfl) ⟨654287, by rfl⟩ : syracuseStep 3489533 = 1308575) B1308575
theorem B71778797 : Blo 1032607 71778797 := bstep (se 3 (by rfl) ⟨13458524, by rfl⟩ : syracuseStep 71778797 = 26917049) B26917049
theorem B26854379 : Blo 1032607 26854379 := bstep (se 1 (by rfl) ⟨20140784, by rfl⟩ : syracuseStep 26854379 = 40281569) B40281569
theorem B1033679 : Blo 1032607 1033679 := bstep (se 1 (by rfl) ⟨775259, by rfl⟩ : syracuseStep 1033679 = 1550519) B1550519
theorem B1035003 : Blo 1032607 1035003 := bstep (se 1 (by rfl) ⟨776252, by rfl⟩ : syracuseStep 1035003 = 1552505) B1552505
theorem B1035035 : Blo 1032607 1035035 := bstep (se 1 (by rfl) ⟨776276, by rfl⟩ : syracuseStep 1035035 = 1552553) B1552553
theorem B3722107 : Blo 1032607 3722107 := bstep (se 1 (by rfl) ⟨2791580, by rfl⟩ : syracuseStep 3722107 = 5583161) B5583161
theorem B1362971 : Blo 1032607 1362971 := bstep (se 1 (by rfl) ⟨1022228, by rfl⟩ : syracuseStep 1362971 = 2044457) B2044457
theorem B3492989 : Blo 1032607 3492989 := bstep (se 3 (by rfl) ⟨654935, by rfl⟩ : syracuseStep 3492989 = 1309871) B1309871
theorem B8834183 : Blo 1032607 8834183 := bstep (se 1 (by rfl) ⟨6625637, by rfl⟩ : syracuseStep 8834183 = 13251275) B13251275
theorem B1035519 : Blo 1032607 1035519 := bstep (se 1 (by rfl) ⟨776639, by rfl⟩ : syracuseStep 1035519 = 1553279) B1553279
theorem B1658153 : Blo 1032607 1658153 := bstep (se 2 (by rfl) ⟨621807, by rfl⟩ : syracuseStep 1658153 = 1243615) B1243615
theorem B1036059 : Blo 1032607 1036059 := bstep (se 1 (by rfl) ⟨777044, by rfl⟩ : syracuseStep 1036059 = 1554089) B1554089
theorem B5230655 : Blo 1032607 5230655 := bstep (se 1 (by rfl) ⟨3922991, by rfl⟩ : syracuseStep 5230655 = 7845983) B7845983
theorem B3494015 : Blo 1032607 3494015 := bstep (se 1 (by rfl) ⟨2620511, by rfl⟩ : syracuseStep 3494015 = 5241023) B5241023
theorem B1036527 : Blo 1032607 1036527 := bstep (se 1 (by rfl) ⟨777395, by rfl⟩ : syracuseStep 1036527 = 1554791) B1554791
theorem B16798265 : Blo 1032607 16798265 := bstep (se 2 (by rfl) ⟨6299349, by rfl⟩ : syracuseStep 16798265 = 12598699) B12598699
theorem B19911815 : Blo 1032607 19911815 := bstep (se 1 (by rfl) ⟨14933861, by rfl⟩ : syracuseStep 19911815 = 29867723) B29867723
theorem B80696519 : Blo 1032607 80696519 := bstep (se 1 (by rfl) ⟨60522389, by rfl⟩ : syracuseStep 80696519 = 121044779) B121044779
theorem B4413487 : Blo 1032607 4413487 := bstep (se 1 (by rfl) ⟨3310115, by rfl⟩ : syracuseStep 4413487 = 6620231) B6620231
theorem B3725623 : Blo 1032607 3725623 := bstep (se 1 (by rfl) ⟨2794217, by rfl⟩ : syracuseStep 3725623 = 5588435) B5588435
theorem B3496283 : Blo 1032607 3496283 := bstep (se 1 (by rfl) ⟨2622212, by rfl⟩ : syracuseStep 3496283 = 5244425) B5244425
theorem B3496607 : Blo 1032607 3496607 := bstep (se 1 (by rfl) ⟨2622455, by rfl⟩ : syracuseStep 3496607 = 5244911) B5244911
theorem B3497147 : Blo 1032607 3497147 := bstep (se 1 (by rfl) ⟨2622860, by rfl⟩ : syracuseStep 3497147 = 5245721) B5245721
theorem B3923585 : Blo 1032607 3923585 := bstep (se 2 (by rfl) ⟨1471344, by rfl⟩ : syracuseStep 3923585 = 2942689) B2942689
theorem B3497849 : Blo 1032607 3497849 := bstep (se 2 (by rfl) ⟨1311693, by rfl⟩ : syracuseStep 3497849 = 2623387) B2623387
theorem B3924071 : Blo 1032607 3924071 := bstep (se 1 (by rfl) ⟨2943053, by rfl⟩ : syracuseStep 3924071 = 5886107) B5886107
theorem B2613991 : Blo 1032607 2613991 := bstep (se 1 (by rfl) ⟨1960493, by rfl⟩ : syracuseStep 2613991 = 3920987) B3920987
theorem B3925817 : Blo 1032607 3925817 := bstep (se 2 (by rfl) ⟨1472181, by rfl⟩ : syracuseStep 3925817 = 2944363) B2944363
theorem B5236649 : Blo 1032607 5236649 := bstep (se 2 (by rfl) ⟨1963743, by rfl⟩ : syracuseStep 5236649 = 3927487) B3927487
theorem B4188991 : Blo 1032607 4188991 := bstep (se 1 (by rfl) ⟨3141743, by rfl⟩ : syracuseStep 4188991 = 6283487) B6283487
theorem B26864759 : Blo 1032607 26864759 := bstep (se 1 (by rfl) ⟨20148569, by rfl⟩ : syracuseStep 26864759 = 40297139) B40297139
theorem B3927275 : Blo 1032607 3927275 := bstep (se 1 (by rfl) ⟨2945456, by rfl⟩ : syracuseStep 3927275 = 5890913) B5890913
theorem B5238107 : Blo 1032607 5238107 := bstep (se 1 (by rfl) ⟨3928580, by rfl⟩ : syracuseStep 5238107 = 7857161) B7857161
theorem B2616887 : Blo 1032607 2616887 := bstep (se 1 (by rfl) ⟨1962665, by rfl⟩ : syracuseStep 2616887 = 3925331) B3925331
theorem B2485979 : Blo 1032607 2485979 := bstep (se 1 (by rfl) ⟨1864484, by rfl⟩ : syracuseStep 2485979 = 3728969) B3728969
theorem B4419791 : Blo 1032607 4419791 := bstep (se 1 (by rfl) ⟨3314843, by rfl⟩ : syracuseStep 4419791 = 6629687) B6629687
theorem B5239079 : Blo 1032607 5239079 := bstep (se 1 (by rfl) ⟨3929309, by rfl⟩ : syracuseStep 5239079 = 7858619) B7858619
theorem B3928733 : Blo 1032607 3928733 := bstep (se 3 (by rfl) ⟨736637, by rfl⟩ : syracuseStep 3928733 = 1473275) B1473275
theorem B7861049 : Blo 1032607 7861049 := bstep (se 2 (by rfl) ⟨2947893, by rfl⟩ : syracuseStep 7861049 = 5895787) B5895787
theorem B2618203 : Blo 1032607 2618203 := bstep (se 1 (by rfl) ⟨1963652, by rfl⟩ : syracuseStep 2618203 = 3927305) B3927305
theorem B1864939 : Blo 1032607 1864939 := bstep (se 1 (by rfl) ⟨1398704, by rfl⟩ : syracuseStep 1864939 = 2797409) B2797409
theorem B2323943 : Blo 1032607 2323943 := bstep (se 1 (by rfl) ⟨1742957, by rfl⟩ : syracuseStep 2323943 = 3485915) B3485915
theorem B2324015 : Blo 1032607 2324015 := bstep (se 1 (by rfl) ⟨1743011, by rfl⟩ : syracuseStep 2324015 = 3486023) B3486023
theorem B2619175 : Blo 1032607 2619175 := bstep (se 1 (by rfl) ⟨1964381, by rfl⟩ : syracuseStep 2619175 = 3928763) B3928763
theorem B7862507 : Blo 1032607 7862507 := bstep (se 1 (by rfl) ⟨5896880, by rfl⟩ : syracuseStep 7862507 = 11793761) B11793761
theorem B3930707 : Blo 1032607 3930707 := bstep (se 1 (by rfl) ⟨2948030, by rfl⟩ : syracuseStep 3930707 = 5896061) B5896061
theorem B2325095 : Blo 1032607 2325095 := bstep (se 1 (by rfl) ⟨1743821, by rfl⟩ : syracuseStep 2325095 = 3487643) B3487643
theorem B51706507 : Blo 1032607 51706507 := bstep (se 1 (by rfl) ⟨38779880, by rfl⟩ : syracuseStep 51706507 = 77559761) B77559761
theorem B4717577 : Blo 1032607 4717577 := bstep (se 2 (by rfl) ⟨1769091, by rfl⟩ : syracuseStep 4717577 = 3538183) B3538183
theorem B1179103 : Blo 1032607 1179103 := bstep (se 1 (by rfl) ⟨884327, by rfl⟩ : syracuseStep 1179103 = 1768655) B1768655
theorem B14941705 : Blo 1032607 14941705 := bstep (se 2 (by rfl) ⟨5603139, by rfl⟩ : syracuseStep 14941705 = 11206279) B11206279
theorem B8847305 : Blo 1032607 8847305 := bstep (se 2 (by rfl) ⟨3317739, by rfl⟩ : syracuseStep 8847305 = 6635479) B6635479
theorem B10092527 : Blo 1032607 10092527 := bstep (se 1 (by rfl) ⟨7569395, by rfl⟩ : syracuseStep 10092527 = 15138791) B15138791
theorem B7962761 : Blo 1032607 7962761 := bstep (se 2 (by rfl) ⟨2986035, by rfl⟩ : syracuseStep 7962761 = 5972071) B5972071
theorem B5603813 : Blo 1032607 5603813 := bstep (se 4 (by rfl) ⟨525357, by rfl⟩ : syracuseStep 5603813 = 1050715) B1050715
theorem B5604005 : Blo 1032607 5604005 := bstep (se 4 (by rfl) ⟨525375, by rfl⟩ : syracuseStep 5604005 = 1050751) B1050751
theorem B2622203 : Blo 1032607 2622203 := bstep (se 1 (by rfl) ⟨1966652, by rfl⟩ : syracuseStep 2622203 = 3933305) B3933305
theorem B2622415 : Blo 1032607 2622415 := bstep (se 1 (by rfl) ⟨1966811, by rfl⟩ : syracuseStep 2622415 = 3933623) B3933623
theorem B2327777 : Blo 1032607 2327777 := bstep (se 2 (by rfl) ⟨872916, by rfl⟩ : syracuseStep 2327777 = 1745833) B1745833
theorem B3934079 : Blo 1032607 3934079 := bstep (se 1 (by rfl) ⟨2950559, by rfl⟩ : syracuseStep 3934079 = 5901119) B5901119
theorem B2328659 : Blo 1032607 2328659 := bstep (se 1 (by rfl) ⟨1746494, by rfl⟩ : syracuseStep 2328659 = 3492989) B3492989
theorem B18876887 : Blo 1032607 18876887 := bstep (se 1 (by rfl) ⟨14157665, by rfl⟩ : syracuseStep 18876887 = 28315331) B28315331
theorem B2329343 : Blo 1032607 2329343 := bstep (se 1 (by rfl) ⟨1747007, by rfl⟩ : syracuseStep 2329343 = 3494015) B3494015
theorem B11340587 : Blo 1032607 11340587 := bstep (se 1 (by rfl) ⟨8505440, by rfl⟩ : syracuseStep 11340587 = 17010881) B17010881
theorem B1772351 : Blo 1032607 1772351 := bstep (se 1 (by rfl) ⟨1329263, by rfl⟩ : syracuseStep 1772351 = 2658527) B2658527
theorem B2329577 : Blo 1032607 2329577 := bstep (se 2 (by rfl) ⟨873591, by rfl⟩ : syracuseStep 2329577 = 1747183) B1747183
theorem B2362679 : Blo 1032607 2362679 := bstep (se 1 (by rfl) ⟨1772009, by rfl⟩ : syracuseStep 2362679 = 3544019) B3544019
theorem B13274543 : Blo 1032607 13274543 := bstep (se 1 (by rfl) ⟨9955907, by rfl⟩ : syracuseStep 13274543 = 19911815) B19911815
theorem B2330855 : Blo 1032607 2330855 := bstep (se 1 (by rfl) ⟨1748141, by rfl⟩ : syracuseStep 2330855 = 3496283) B3496283
theorem B2331071 : Blo 1032607 2331071 := bstep (se 1 (by rfl) ⟨1748303, by rfl⟩ : syracuseStep 2331071 = 3496607) B3496607
theorem B2331431 : Blo 1032607 2331431 := bstep (se 1 (by rfl) ⟨1748573, by rfl⟩ : syracuseStep 2331431 = 3497147) B3497147
theorem B2331899 : Blo 1032607 2331899 := bstep (se 1 (by rfl) ⟨1748924, by rfl⟩ : syracuseStep 2331899 = 3497849) B3497849
theorem B7444993 : Blo 1032607 7444993 := bstep (se 2 (by rfl) ⟨2791872, by rfl⟩ : syracuseStep 7444993 = 5583745) B5583745
theorem B19864763 : Blo 1032607 19864763 := bstep (se 1 (by rfl) ⟨14898572, by rfl⟩ : syracuseStep 19864763 = 29797145) B29797145
theorem B1744591 : Blo 1032607 1744591 := bstep (se 1 (by rfl) ⟨1308443, by rfl⟩ : syracuseStep 1744591 = 2616887) B2616887
theorem B4202617 : Blo 1032607 4202617 := bstep (se 2 (by rfl) ⟨1575981, by rfl⟩ : syracuseStep 4202617 = 3151963) B3151963
theorem B1549295 : Blo 1032607 1549295 := bstep (se 1 (by rfl) ⟨1161971, by rfl⟩ : syracuseStep 1549295 = 2323943) B2323943
theorem B1549343 : Blo 1032607 1549343 := bstep (se 1 (by rfl) ⟨1162007, by rfl⟩ : syracuseStep 1549343 = 2324015) B2324015
theorem B1550063 : Blo 1032607 1550063 := bstep (se 1 (by rfl) ⟨1162547, by rfl⟩ : syracuseStep 1550063 = 2325095) B2325095
theorem B1550201 : Blo 1032607 1550201 := bstep (se 2 (by rfl) ⟨581325, by rfl⟩ : syracuseStep 1550201 = 1162651) B1162651
theorem B3975037 : Blo 1032607 3975037 := bstep (se 3 (by rfl) ⟨745319, by rfl⟩ : syracuseStep 3975037 = 1490639) B1490639
theorem B6728351 : Blo 1032607 6728351 := bstep (se 1 (by rfl) ⟨5046263, by rfl⟩ : syracuseStep 6728351 = 10092527) B10092527
theorem B47852531 : Blo 1032607 47852531 := bstep (se 1 (by rfl) ⟨35889398, by rfl⟩ : syracuseStep 47852531 = 71778797) B71778797
theorem B17902919 : Blo 1032607 17902919 := bstep (se 1 (by rfl) ⟨13427189, by rfl⟩ : syracuseStep 17902919 = 26854379) B26854379
theorem B3485321 : Blo 1032607 3485321 := bstep (se 2 (by rfl) ⟨1306995, by rfl⟩ : syracuseStep 3485321 = 2613991) B2613991
theorem B1552415 : Blo 1032607 1552415 := bstep (se 1 (by rfl) ⟨1164311, by rfl⟩ : syracuseStep 1552415 = 2328623) B2328623
theorem B7844039 : Blo 1032607 7844039 := bstep (se 1 (by rfl) ⟨5883029, by rfl⟩ : syracuseStep 7844039 = 11766059) B11766059
theorem B1552619 : Blo 1032607 1552619 := bstep (se 1 (by rfl) ⟨1164464, by rfl⟩ : syracuseStep 1552619 = 2328929) B2328929
theorem B1553243 : Blo 1032607 1553243 := bstep (se 1 (by rfl) ⟨1164932, by rfl⟩ : syracuseStep 1553243 = 2329865) B2329865
theorem B1553351 : Blo 1032607 1553351 := bstep (se 1 (by rfl) ⟨1165013, by rfl⟩ : syracuseStep 1553351 = 2330027) B2330027
theorem B3487103 : Blo 1032607 3487103 := bstep (se 1 (by rfl) ⟨2615327, by rfl⟩ : syracuseStep 3487103 = 5230655) B5230655
theorem B1554095 : Blo 1032607 1554095 := bstep (se 1 (by rfl) ⟨1165571, by rfl⟩ : syracuseStep 1554095 = 2331143) B2331143
theorem B5585321 : Blo 1032607 5585321 := bstep (se 2 (by rfl) ⟨2094495, by rfl⟩ : syracuseStep 5585321 = 4188991) B4188991
theorem B4962809 : Blo 1032607 4962809 := bstep (se 2 (by rfl) ⟨1861053, by rfl⟩ : syracuseStep 4962809 = 3722107) B3722107
theorem B1162183 : Blo 1032607 1162183 := bstep (se 1 (by rfl) ⟨871637, by rfl⟩ : syracuseStep 1162183 = 1743275) B1743275
theorem B4963943 : Blo 1032607 4963943 := bstep (se 1 (by rfl) ⟨3722957, by rfl⟩ : syracuseStep 4963943 = 7445915) B7445915
theorem B34521155 : Blo 1032607 34521155 := bstep (se 1 (by rfl) ⟨25890866, by rfl⟩ : syracuseStep 34521155 = 51781733) B51781733
theorem B1163335 : Blo 1032607 1163335 := bstep (se 1 (by rfl) ⟨872501, by rfl⟩ : syracuseStep 1163335 = 1745003) B1745003
theorem B1032639 : Blo 1032607 1032639 := bstep (se 1 (by rfl) ⟨774479, by rfl⟩ : syracuseStep 1032639 = 1548959) B1548959
theorem B11322089 : Blo 1032607 11322089 := bstep (se 2 (by rfl) ⟨4245783, by rfl⟩ : syracuseStep 11322089 = 8491567) B8491567
theorem B1032943 : Blo 1032607 1032943 := bstep (se 1 (by rfl) ⟨774707, by rfl⟩ : syracuseStep 1032943 = 1549415) B1549415
theorem B3490937 : Blo 1032607 3490937 := bstep (se 2 (by rfl) ⟨1309101, by rfl⟩ : syracuseStep 3490937 = 2618203) B2618203
theorem B3491099 : Blo 1032607 3491099 := bstep (se 1 (by rfl) ⟨2618324, by rfl⟩ : syracuseStep 3491099 = 5236649) B5236649
theorem B1164703 : Blo 1032607 1164703 := bstep (se 1 (by rfl) ⟨873527, by rfl⟩ : syracuseStep 1164703 = 1747055) B1747055
theorem B1033663 : Blo 1032607 1033663 := bstep (se 1 (by rfl) ⟨775247, by rfl⟩ : syracuseStep 1033663 = 1550495) B1550495
theorem B1164775 : Blo 1032607 1164775 := bstep (se 1 (by rfl) ⟨873581, by rfl⟩ : syracuseStep 1164775 = 1747163) B1747163
theorem B5228063 : Blo 1032607 5228063 := bstep (se 1 (by rfl) ⟨3921047, by rfl⟩ : syracuseStep 5228063 = 7842095) B7842095
theorem B1164847 : Blo 1032607 1164847 := bstep (se 1 (by rfl) ⟨873635, by rfl⟩ : syracuseStep 1164847 = 1747271) B1747271
theorem B1033855 : Blo 1032607 1033855 := bstep (se 1 (by rfl) ⟨775391, by rfl⟩ : syracuseStep 1033855 = 1550783) B1550783
theorem B1034055 : Blo 1032607 1034055 := bstep (se 1 (by rfl) ⟨775541, by rfl⟩ : syracuseStep 1034055 = 1551083) B1551083
theorem B30197609 : Blo 1032607 30197609 := bstep (se 2 (by rfl) ⟨11324103, by rfl⟩ : syracuseStep 30197609 = 22648207) B22648207
theorem B4966267 : Blo 1032607 4966267 := bstep (se 1 (by rfl) ⟨3724700, by rfl⟩ : syracuseStep 4966267 = 7449401) B7449401
theorem B1034151 : Blo 1032607 1034151 := bstep (se 1 (by rfl) ⟨775613, by rfl⟩ : syracuseStep 1034151 = 1551227) B1551227
theorem B17909839 : Blo 1032607 17909839 := bstep (se 1 (by rfl) ⟨13432379, by rfl⟩ : syracuseStep 17909839 = 26864759) B26864759
theorem B1034407 : Blo 1032607 1034407 := bstep (se 1 (by rfl) ⟨775805, by rfl⟩ : syracuseStep 1034407 = 1551611) B1551611
theorem B3492071 : Blo 1032607 3492071 := bstep (se 1 (by rfl) ⟨2619053, by rfl⟩ : syracuseStep 3492071 = 5238107) B5238107
theorem B3492233 : Blo 1032607 3492233 := bstep (se 2 (by rfl) ⟨1309587, by rfl⟩ : syracuseStep 3492233 = 2619175) B2619175
theorem B1657319 : Blo 1032607 1657319 := bstep (se 1 (by rfl) ⟨1242989, by rfl⟩ : syracuseStep 1657319 = 2485979) B2485979
theorem B1034919 : Blo 1032607 1034919 := bstep (se 1 (by rfl) ⟨776189, by rfl⟩ : syracuseStep 1034919 = 1552379) B1552379
theorem B5884649 : Blo 1032607 5884649 := bstep (se 2 (by rfl) ⟨2206743, by rfl⟩ : syracuseStep 5884649 = 4413487) B4413487
theorem B1035039 : Blo 1032607 1035039 := bstep (se 1 (by rfl) ⟨776279, by rfl⟩ : syracuseStep 1035039 = 1552559) B1552559
theorem B3492719 : Blo 1032607 3492719 := bstep (se 1 (by rfl) ⟨2619539, by rfl⟩ : syracuseStep 3492719 = 5239079) B5239079
theorem B1035295 : Blo 1032607 1035295 := bstep (se 1 (by rfl) ⟨776471, by rfl⟩ : syracuseStep 1035295 = 1552943) B1552943
theorem B4967497 : Blo 1032607 4967497 := bstep (se 2 (by rfl) ⟨1862811, by rfl⟩ : syracuseStep 4967497 = 3725623) B3725623
theorem B1035515 : Blo 1032607 1035515 := bstep (se 1 (by rfl) ⟨776636, by rfl⟩ : syracuseStep 1035515 = 1553273) B1553273
theorem B1035583 : Blo 1032607 1035583 := bstep (se 1 (by rfl) ⟨776687, by rfl⟩ : syracuseStep 1035583 = 1553375) B1553375
theorem B9948527 : Blo 1032607 9948527 := bstep (se 1 (by rfl) ⟨7461395, by rfl⟩ : syracuseStep 9948527 = 14922791) B14922791
theorem B1035679 : Blo 1032607 1035679 := bstep (se 1 (by rfl) ⟨776759, by rfl⟩ : syracuseStep 1035679 = 1553519) B1553519
theorem B1035711 : Blo 1032607 1035711 := bstep (se 1 (by rfl) ⟨776783, by rfl⟩ : syracuseStep 1035711 = 1553567) B1553567
theorem B1035967 : Blo 1032607 1035967 := bstep (se 1 (by rfl) ⟨776975, by rfl⟩ : syracuseStep 1035967 = 1553951) B1553951
theorem B1036455 : Blo 1032607 1036455 := bstep (se 1 (by rfl) ⟨777341, by rfl⟩ : syracuseStep 1036455 = 1554683) B1554683
theorem B1036495 : Blo 1032607 1036495 := bstep (se 1 (by rfl) ⟨777371, by rfl⟩ : syracuseStep 1036495 = 1554743) B1554743
theorem B1036539 : Blo 1032607 1036539 := bstep (se 1 (by rfl) ⟨777404, by rfl⟩ : syracuseStep 1036539 = 1554809) B1554809
theorem B1036543 : Blo 1032607 1036543 := bstep (se 1 (by rfl) ⟨777407, by rfl⟩ : syracuseStep 1036543 = 1554815) B1554815
theorem B5889455 : Blo 1032607 5889455 := bstep (se 1 (by rfl) ⟨4417091, by rfl⟩ : syracuseStep 5889455 = 8834183) B8834183
theorem B3497471 : Blo 1032607 3497471 := bstep (se 1 (by rfl) ⟨2623103, by rfl⟩ : syracuseStep 3497471 = 5246207) B5246207
theorem B1105435 : Blo 1032607 1105435 := bstep (se 1 (by rfl) ⟨829076, by rfl⟩ : syracuseStep 1105435 = 1658153) B1658153
theorem B11198843 : Blo 1032607 11198843 := bstep (se 1 (by rfl) ⟨8399132, by rfl⟩ : syracuseStep 11198843 = 16798265) B16798265
theorem B2515711 : Blo 1032607 2515711 := bstep (se 1 (by rfl) ⟨1886783, by rfl⟩ : syracuseStep 2515711 = 3773567) B3773567
theorem B4481831 : Blo 1032607 4481831 := bstep (se 1 (by rfl) ⟨3361373, by rfl⟩ : syracuseStep 4481831 = 6722747) B6722747
theorem B53797679 : Blo 1032607 53797679 := bstep (se 1 (by rfl) ⟨40348259, by rfl⟩ : syracuseStep 53797679 = 80696519) B80696519
theorem B2615723 : Blo 1032607 2615723 := bstep (se 1 (by rfl) ⟨1961792, by rfl⟩ : syracuseStep 2615723 = 3923585) B3923585
theorem B2616047 : Blo 1032607 2616047 := bstep (se 1 (by rfl) ⟨1962035, by rfl⟩ : syracuseStep 2616047 = 3924071) B3924071
theorem B28340063 : Blo 1032607 28340063 := bstep (se 1 (by rfl) ⟨21255047, by rfl⟩ : syracuseStep 28340063 = 42510095) B42510095
theorem B2617211 : Blo 1032607 2617211 := bstep (se 1 (by rfl) ⟨1962908, by rfl⟩ : syracuseStep 2617211 = 3925817) B3925817
theorem B2486585 : Blo 1032607 2486585 := bstep (se 2 (by rfl) ⟨932469, by rfl⟩ : syracuseStep 2486585 = 1864939) B1864939
theorem B2618183 : Blo 1032607 2618183 := bstep (se 1 (by rfl) ⟨1963637, by rfl⟩ : syracuseStep 2618183 = 3927275) B3927275
theorem B4092755 : Blo 1032607 4092755 := bstep (se 1 (by rfl) ⟨3069566, by rfl⟩ : syracuseStep 4092755 = 6139133) B6139133
theorem B12580205 : Blo 1032607 12580205 := bstep (se 3 (by rfl) ⟨2358788, by rfl⟩ : syracuseStep 12580205 = 4717577) B4717577
theorem B3634589 : Blo 1032607 3634589 := bstep (se 3 (by rfl) ⟨681485, by rfl⟩ : syracuseStep 3634589 = 1362971) B1362971
theorem B2946527 : Blo 1032607 2946527 := bstep (se 1 (by rfl) ⟨2209895, by rfl⟩ : syracuseStep 2946527 = 4419791) B4419791
theorem B2619155 : Blo 1032607 2619155 := bstep (se 1 (by rfl) ⟨1964366, by rfl⟩ : syracuseStep 2619155 = 3928733) B3928733
theorem B2324321 : Blo 1032607 2324321 := bstep (se 2 (by rfl) ⟨871620, by rfl⟩ : syracuseStep 2324321 = 1743241) B1743241
theorem B2946937 : Blo 1032607 2946937 := bstep (se 2 (by rfl) ⟨1105101, by rfl⟩ : syracuseStep 2946937 = 2210203) B2210203
theorem B5240699 : Blo 1032607 5240699 := bstep (se 1 (by rfl) ⟨3930524, by rfl⟩ : syracuseStep 5240699 = 7861049) B7861049
theorem B68942009 : Blo 1032607 68942009 := bstep (se 2 (by rfl) ⟨25853253, by rfl⟩ : syracuseStep 68942009 = 51706507) B51706507
theorem B21199481 : Blo 1032607 21199481 := bstep (se 2 (by rfl) ⟨7949805, by rfl⟩ : syracuseStep 21199481 = 15899611) B15899611
theorem B20151017 : Blo 1032607 20151017 := bstep (se 2 (by rfl) ⟨7556631, by rfl⟩ : syracuseStep 20151017 = 15113263) B15113263
theorem B5241671 : Blo 1032607 5241671 := bstep (se 1 (by rfl) ⟨3931253, by rfl⟩ : syracuseStep 5241671 = 7862507) B7862507
theorem B2620471 : Blo 1032607 2620471 := bstep (se 1 (by rfl) ⟨1965353, by rfl⟩ : syracuseStep 2620471 = 3930707) B3930707
theorem B2325671 : Blo 1032607 2325671 := bstep (se 1 (by rfl) ⟨1744253, by rfl⟩ : syracuseStep 2325671 = 3488507) B3488507
theorem B1572137 : Blo 1032607 1572137 := bstep (se 2 (by rfl) ⟨589551, by rfl⟩ : syracuseStep 1572137 = 1179103) B1179103
theorem B19922273 : Blo 1032607 19922273 := bstep (se 2 (by rfl) ⟨7470852, by rfl⟩ : syracuseStep 19922273 = 14941705) B14941705
theorem B1867483 : Blo 1032607 1867483 := bstep (se 1 (by rfl) ⟨1400612, by rfl⟩ : syracuseStep 1867483 = 2801225) B2801225
theorem B2326355 : Blo 1032607 2326355 := bstep (se 1 (by rfl) ⟨1744766, by rfl⟩ : syracuseStep 2326355 = 3489533) B3489533
theorem B5898203 : Blo 1032607 5898203 := bstep (se 1 (by rfl) ⟨4423652, by rfl⟩ : syracuseStep 5898203 = 8847305) B8847305
theorem B5308507 : Blo 1032607 5308507 := bstep (se 1 (by rfl) ⟨3981380, by rfl⟩ : syracuseStep 5308507 = 7962761) B7962761
theorem B5603489 : Blo 1032607 5603489 := bstep (se 2 (by rfl) ⟨2101308, by rfl⟩ : syracuseStep 5603489 = 4202617) B4202617
theorem B3735875 : Blo 1032607 3735875 := bstep (se 1 (by rfl) ⟨2801906, by rfl⟩ : syracuseStep 3735875 = 5603813) B5603813
theorem B2327291 : Blo 1032607 2327291 := bstep (se 1 (by rfl) ⟨1745468, by rfl⟩ : syracuseStep 2327291 = 3490937) B3490937
theorem B2327399 : Blo 1032607 2327399 := bstep (se 1 (by rfl) ⟨1745549, by rfl⟩ : syracuseStep 2327399 = 3491099) B3491099
theorem B2622719 : Blo 1032607 2622719 := bstep (se 1 (by rfl) ⟨1967039, by rfl⟩ : syracuseStep 2622719 = 3934079) B3934079
theorem B2328047 : Blo 1032607 2328047 := bstep (se 1 (by rfl) ⟨1746035, by rfl⟩ : syracuseStep 2328047 = 3492071) B3492071
theorem B2328155 : Blo 1032607 2328155 := bstep (se 1 (by rfl) ⟨1746116, by rfl⟩ : syracuseStep 2328155 = 3492233) B3492233
theorem B12584591 : Blo 1032607 12584591 := bstep (se 1 (by rfl) ⟨9438443, by rfl⟩ : syracuseStep 12584591 = 18876887) B18876887
theorem B14944013 : Blo 1032607 14944013 := bstep (se 3 (by rfl) ⟨2802002, by rfl⟩ : syracuseStep 14944013 = 5604005) B5604005
theorem B1181567 : Blo 1032607 1181567 := bstep (se 1 (by rfl) ⟨886175, by rfl⟩ : syracuseStep 1181567 = 1772351) B1772351
theorem B2328479 : Blo 1032607 2328479 := bstep (se 1 (by rfl) ⟨1746359, by rfl⟩ : syracuseStep 2328479 = 3492719) B3492719
theorem B1575119 : Blo 1032607 1575119 := bstep (se 1 (by rfl) ⟨1181339, by rfl⟩ : syracuseStep 1575119 = 2362679) B2362679
theorem B10914013 : Blo 1032607 10914013 := bstep (se 3 (by rfl) ⟨2046377, by rfl⟩ : syracuseStep 10914013 = 4092755) B4092755
theorem B8849695 : Blo 1032607 8849695 := bstep (se 1 (by rfl) ⟨6637271, by rfl⟩ : syracuseStep 8849695 = 13274543) B13274543
theorem B6621689 : Blo 1032607 6621689 := bstep (se 2 (by rfl) ⟨2483133, by rfl⟩ : syracuseStep 6621689 = 4966267) B4966267
theorem B13243175 : Blo 1032607 13243175 := bstep (se 1 (by rfl) ⟨9932381, by rfl⟩ : syracuseStep 13243175 = 19864763) B19864763
theorem B2331647 : Blo 1032607 2331647 := bstep (se 1 (by rfl) ⟨1748735, by rfl⟩ : syracuseStep 2331647 = 3497471) B3497471
theorem B2987887 : Blo 1032607 2987887 := bstep (se 1 (by rfl) ⟨2240915, by rfl⟩ : syracuseStep 2987887 = 4481831) B4481831
theorem B1743815 : Blo 1032607 1743815 := bstep (se 1 (by rfl) ⟨1307861, by rfl⟩ : syracuseStep 1743815 = 2615723) B2615723
theorem B1744031 : Blo 1032607 1744031 := bstep (se 1 (by rfl) ⟨1308023, by rfl⟩ : syracuseStep 1744031 = 2616047) B2616047
theorem B11935279 : Blo 1032607 11935279 := bstep (se 1 (by rfl) ⟨8951459, by rfl⟩ : syracuseStep 11935279 = 17902919) B17902919
theorem B1744807 : Blo 1032607 1744807 := bstep (se 1 (by rfl) ⟨1308605, by rfl⟩ : syracuseStep 1744807 = 2617211) B2617211
theorem B1745455 : Blo 1032607 1745455 := bstep (se 1 (by rfl) ⟨1309091, by rfl⟩ : syracuseStep 1745455 = 2618183) B2618183
theorem B1746103 : Blo 1032607 1746103 := bstep (se 1 (by rfl) ⟨1309577, by rfl⟩ : syracuseStep 1746103 = 2619155) B2619155
theorem B1549547 : Blo 1032607 1549547 := bstep (se 1 (by rfl) ⟨1162160, by rfl⟩ : syracuseStep 1549547 = 2324321) B2324321
theorem B1549577 : Blo 1032607 1549577 := bstep (se 2 (by rfl) ⟨581091, by rfl⟩ : syracuseStep 1549577 = 1162183) B1162183
theorem B14132987 : Blo 1032607 14132987 := bstep (se 1 (by rfl) ⟨10599740, by rfl⟩ : syracuseStep 14132987 = 21199481) B21199481
theorem B1550447 : Blo 1032607 1550447 := bstep (se 1 (by rfl) ⟨1162835, by rfl⟩ : syracuseStep 1550447 = 2325671) B2325671
theorem B13281515 : Blo 1032607 13281515 := bstep (se 1 (by rfl) ⟨9961136, by rfl⟩ : syracuseStep 13281515 = 19922273) B19922273
theorem B1550903 : Blo 1032607 1550903 := bstep (se 1 (by rfl) ⟨1163177, by rfl⟩ : syracuseStep 1550903 = 2326355) B2326355
theorem B23014103 : Blo 1032607 23014103 := bstep (se 1 (by rfl) ⟨17260577, by rfl⟩ : syracuseStep 23014103 = 34521155) B34521155
theorem B1551113 : Blo 1032607 1551113 := bstep (se 2 (by rfl) ⟨581667, by rfl⟩ : syracuseStep 1551113 = 1163335) B1163335
theorem B7548059 : Blo 1032607 7548059 := bstep (se 1 (by rfl) ⟨5661044, by rfl⟩ : syracuseStep 7548059 = 11322089) B11322089
theorem B1748135 : Blo 1032607 1748135 := bstep (se 1 (by rfl) ⟨1311101, by rfl⟩ : syracuseStep 1748135 = 2622203) B2622203
theorem B1551851 : Blo 1032607 1551851 := bstep (se 1 (by rfl) ⟨1163888, by rfl⟩ : syracuseStep 1551851 = 2327777) B2327777
theorem B6630893 : Blo 1032607 6630893 := bstep (se 3 (by rfl) ⟨1243292, by rfl⟩ : syracuseStep 6630893 = 2486585) B2486585
theorem B3354281 : Blo 1032607 3354281 := bstep (se 2 (by rfl) ⟨1257855, by rfl⟩ : syracuseStep 3354281 = 2515711) B2515711
theorem B3485375 : Blo 1032607 3485375 := bstep (se 1 (by rfl) ⟨2614031, by rfl⟩ : syracuseStep 3485375 = 5228063) B5228063
theorem B20131739 : Blo 1032607 20131739 := bstep (se 1 (by rfl) ⟨15098804, by rfl⟩ : syracuseStep 20131739 = 30197609) B30197609
theorem B1552439 : Blo 1032607 1552439 := bstep (se 1 (by rfl) ⟨1164329, by rfl⟩ : syracuseStep 1552439 = 2328659) B2328659
theorem B1552895 : Blo 1032607 1552895 := bstep (se 1 (by rfl) ⟨1164671, by rfl⟩ : syracuseStep 1552895 = 2329343) B2329343
theorem B1552937 : Blo 1032607 1552937 := bstep (se 2 (by rfl) ⟨582351, by rfl⟩ : syracuseStep 1552937 = 1164703) B1164703
theorem B1553033 : Blo 1032607 1553033 := bstep (se 2 (by rfl) ⟨582387, by rfl⟩ : syracuseStep 1553033 = 1164775) B1164775
theorem B1553051 : Blo 1032607 1553051 := bstep (se 1 (by rfl) ⟨1164788, by rfl⟩ : syracuseStep 1553051 = 2329577) B2329577
theorem B1553129 : Blo 1032607 1553129 := bstep (se 2 (by rfl) ⟨582423, by rfl⟩ : syracuseStep 1553129 = 1164847) B1164847
theorem B6632351 : Blo 1032607 6632351 := bstep (se 1 (by rfl) ⟨4974263, by rfl⟩ : syracuseStep 6632351 = 9948527) B9948527
theorem B1553903 : Blo 1032607 1553903 := bstep (se 1 (by rfl) ⟨1165427, by rfl⟩ : syracuseStep 1553903 = 2330855) B2330855
theorem B1554047 : Blo 1032607 1554047 := bstep (se 1 (by rfl) ⟨1165535, by rfl⟩ : syracuseStep 1554047 = 2331071) B2331071
theorem B1554287 : Blo 1032607 1554287 := bstep (se 1 (by rfl) ⟨1165715, by rfl⟩ : syracuseStep 1554287 = 2331431) B2331431
theorem B1554599 : Blo 1032607 1554599 := bstep (se 1 (by rfl) ⟨1165949, by rfl⟩ : syracuseStep 1554599 = 2331899) B2331899
theorem B26493317 : Blo 1032607 26493317 := bstep (se 4 (by rfl) ⟨2483748, by rfl⟩ : syracuseStep 26493317 = 4967497) B4967497
theorem B35865119 : Blo 1032607 35865119 := bstep (se 1 (by rfl) ⟨26898839, by rfl⟩ : syracuseStep 35865119 = 53797679) B53797679
theorem B1032863 : Blo 1032607 1032863 := bstep (se 1 (by rfl) ⟨774647, by rfl⟩ : syracuseStep 1032863 = 1549295) B1549295
theorem B1032895 : Blo 1032607 1032895 := bstep (se 1 (by rfl) ⟨774671, by rfl⟩ : syracuseStep 1032895 = 1549343) B1549343
theorem B14894189 : Blo 1032607 14894189 := bstep (se 3 (by rfl) ⟨2792660, by rfl⟩ : syracuseStep 14894189 = 5585321) B5585321
theorem B1033375 : Blo 1032607 1033375 := bstep (se 1 (by rfl) ⟨775031, by rfl⟩ : syracuseStep 1033375 = 1550063) B1550063
theorem B1033467 : Blo 1032607 1033467 := bstep (se 1 (by rfl) ⟨775100, by rfl⟩ : syracuseStep 1033467 = 1550201) B1550201
theorem B17942269 : Blo 1032607 17942269 := bstep (se 3 (by rfl) ⟨3364175, by rfl⟩ : syracuseStep 17942269 = 6728351) B6728351
theorem B31901687 : Blo 1032607 31901687 := bstep (se 1 (by rfl) ⟨23926265, by rfl⟩ : syracuseStep 31901687 = 47852531) B47852531
theorem B18893375 : Blo 1032607 18893375 := bstep (se 1 (by rfl) ⟨14170031, by rfl⟩ : syracuseStep 18893375 = 28340063) B28340063
theorem B1034943 : Blo 1032607 1034943 := bstep (se 1 (by rfl) ⟨776207, by rfl⟩ : syracuseStep 1034943 = 1552415) B1552415
theorem B5229359 : Blo 1032607 5229359 := bstep (se 1 (by rfl) ⟨3922019, by rfl⟩ : syracuseStep 5229359 = 7844039) B7844039
theorem B1035079 : Blo 1032607 1035079 := bstep (se 1 (by rfl) ⟨776309, by rfl⟩ : syracuseStep 1035079 = 1552619) B1552619
theorem B1035495 : Blo 1032607 1035495 := bstep (se 1 (by rfl) ⟨776621, by rfl⟩ : syracuseStep 1035495 = 1553243) B1553243
theorem B1035567 : Blo 1032607 1035567 := bstep (se 1 (by rfl) ⟨776675, by rfl⟩ : syracuseStep 1035567 = 1553351) B1553351
theorem B1036063 : Blo 1032607 1036063 := bstep (se 1 (by rfl) ⟨777047, by rfl⟩ : syracuseStep 1036063 = 1554095) B1554095
theorem B3493799 : Blo 1032607 3493799 := bstep (se 1 (by rfl) ⟨2620349, by rfl⟩ : syracuseStep 3493799 = 5240699) B5240699
theorem B3493961 : Blo 1032607 3493961 := bstep (se 2 (by rfl) ⟨1310235, by rfl⟩ : syracuseStep 3493961 = 2620471) B2620471
theorem B45961339 : Blo 1032607 45961339 := bstep (se 1 (by rfl) ⟨34471004, by rfl⟩ : syracuseStep 45961339 = 68942009) B68942009
theorem B3494447 : Blo 1032607 3494447 := bstep (se 1 (by rfl) ⟨2620835, by rfl⟩ : syracuseStep 3494447 = 5241671) B5241671
theorem B3496553 : Blo 1032607 3496553 := bstep (se 2 (by rfl) ⟨1311207, by rfl⟩ : syracuseStep 3496553 = 2622415) B2622415
theorem B3923099 : Blo 1032607 3923099 := bstep (se 1 (by rfl) ⟨2942324, by rfl⟩ : syracuseStep 3923099 = 5884649) B5884649
theorem B7560391 : Blo 1032607 7560391 := bstep (se 1 (by rfl) ⟨5670293, by rfl⟩ : syracuseStep 7560391 = 11340587) B11340587
theorem B23879785 : Blo 1032607 23879785 := bstep (se 2 (by rfl) ⟨8954919, by rfl⟩ : syracuseStep 23879785 = 17909839) B17909839
theorem B33547213 : Blo 1032607 33547213 := bstep (se 3 (by rfl) ⟨6290102, by rfl⟩ : syracuseStep 33547213 = 12580205) B12580205
theorem B9692237 : Blo 1032607 9692237 := bstep (se 3 (by rfl) ⟨1817294, by rfl⟩ : syracuseStep 9692237 = 3634589) B3634589
theorem B3926303 : Blo 1032607 3926303 := bstep (se 1 (by rfl) ⟨2944727, by rfl⟩ : syracuseStep 3926303 = 5889455) B5889455
theorem B7465895 : Blo 1032607 7465895 := bstep (se 1 (by rfl) ⟨5599421, by rfl⟩ : syracuseStep 7465895 = 11198843) B11198843
theorem B4419517 : Blo 1032607 4419517 := bstep (se 3 (by rfl) ⟨828659, by rfl⟩ : syracuseStep 4419517 = 1657319) B1657319
theorem B2323547 : Blo 1032607 2323547 := bstep (se 1 (by rfl) ⟨1742660, by rfl⟩ : syracuseStep 2323547 = 3485321) B3485321
theorem B3929249 : Blo 1032607 3929249 := bstep (se 2 (by rfl) ⟨1473468, by rfl⟩ : syracuseStep 3929249 = 2946937) B2946937
theorem B84800789 : Blo 1032607 84800789 := bstep (se 6 (by rfl) ⟨1987518, by rfl⟩ : syracuseStep 84800789 = 3975037) B3975037
theorem B9926657 : Blo 1032607 9926657 := bstep (se 2 (by rfl) ⟨3722496, by rfl⟩ : syracuseStep 9926657 = 7444993) B7444993
theorem B2324735 : Blo 1032607 2324735 := bstep (se 1 (by rfl) ⟨1743551, by rfl⟩ : syracuseStep 2324735 = 3487103) B3487103
theorem B1964351 : Blo 1032607 1964351 := bstep (se 1 (by rfl) ⟨1473263, by rfl⟩ : syracuseStep 1964351 = 2946527) B2946527
theorem B13237181 : Blo 1032607 13237181 := bstep (se 3 (by rfl) ⟨2481971, by rfl⟩ : syracuseStep 13237181 = 4963943) B4963943
theorem B3308539 : Blo 1032607 3308539 := bstep (se 1 (by rfl) ⟨2481404, by rfl⟩ : syracuseStep 3308539 = 4962809) B4962809
theorem B13434011 : Blo 1032607 13434011 := bstep (se 1 (by rfl) ⟨10075508, by rfl⟩ : syracuseStep 13434011 = 20151017) B20151017
theorem B1473913 : Blo 1032607 1473913 := bstep (se 2 (by rfl) ⟨552717, by rfl⟩ : syracuseStep 1473913 = 1105435) B1105435
theorem B1048091 : Blo 1032607 1048091 := bstep (se 1 (by rfl) ⟨786068, by rfl⟩ : syracuseStep 1048091 = 1572137) B1572137
theorem B2326121 : Blo 1032607 2326121 := bstep (se 2 (by rfl) ⟨872295, by rfl⟩ : syracuseStep 2326121 = 1744591) B1744591
theorem B2489977 : Blo 1032607 2489977 := bstep (se 2 (by rfl) ⟨933741, by rfl⟩ : syracuseStep 2489977 = 1867483) B1867483
theorem B3932135 : Blo 1032607 3932135 := bstep (se 1 (by rfl) ⟨2949101, by rfl⟩ : syracuseStep 3932135 = 5898203) B5898203
theorem B3735659 : Blo 1032607 3735659 := bstep (se 1 (by rfl) ⟨2801744, by rfl⟩ : syracuseStep 3735659 = 5603489) B5603489
theorem B2490583 : Blo 1032607 2490583 := bstep (se 1 (by rfl) ⟨1867937, by rfl⟩ : syracuseStep 2490583 = 3735875) B3735875
theorem B17662211 : Blo 1032607 17662211 := bstep (se 1 (by rfl) ⟨13246658, by rfl⟩ : syracuseStep 17662211 = 26493317) B26493317
theorem B28312037 : Blo 1032607 28312037 := bstep (se 4 (by rfl) ⟨2654253, by rfl⟩ : syracuseStep 28312037 = 5308507) B5308507
theorem B2327273 : Blo 1032607 2327273 := bstep (se 2 (by rfl) ⟨872727, by rfl⟩ : syracuseStep 2327273 = 1745455) B1745455
theorem B9929459 : Blo 1032607 9929459 := bstep (se 1 (by rfl) ⟨7447094, by rfl⟩ : syracuseStep 9929459 = 14894189) B14894189
theorem B8389727 : Blo 1032607 8389727 := bstep (se 1 (by rfl) ⟨6292295, by rfl⟩ : syracuseStep 8389727 = 12584591) B12584591
theorem B9962675 : Blo 1032607 9962675 := bstep (se 1 (by rfl) ⟨7472006, by rfl⟩ : syracuseStep 9962675 = 14944013) B14944013
theorem B44729617 : Blo 1032607 44729617 := bstep (se 2 (by rfl) ⟨16773606, by rfl⟩ : syracuseStep 44729617 = 33547213) B33547213
theorem B21267791 : Blo 1032607 21267791 := bstep (se 1 (by rfl) ⟨15950843, by rfl⟩ : syracuseStep 21267791 = 31901687) B31901687
theorem B1050079 : Blo 1032607 1050079 := bstep (se 1 (by rfl) ⟨787559, by rfl⟩ : syracuseStep 1050079 = 1575119) B1575119
theorem B2328137 : Blo 1032607 2328137 := bstep (se 2 (by rfl) ⟨873051, by rfl⟩ : syracuseStep 2328137 = 1746103) B1746103
theorem B23923025 : Blo 1032607 23923025 := bstep (se 2 (by rfl) ⟨8971134, by rfl⟩ : syracuseStep 23923025 = 17942269) B17942269
theorem B2329199 : Blo 1032607 2329199 := bstep (se 1 (by rfl) ⟨1746899, by rfl⟩ : syracuseStep 2329199 = 3493799) B3493799
theorem B2329307 : Blo 1032607 2329307 := bstep (se 1 (by rfl) ⟨1746980, by rfl⟩ : syracuseStep 2329307 = 3493961) B3493961
theorem B14552017 : Blo 1032607 14552017 := bstep (se 2 (by rfl) ⟨5457006, by rfl⟩ : syracuseStep 14552017 = 10914013) B10914013
theorem B2329631 : Blo 1032607 2329631 := bstep (se 1 (by rfl) ⟨1747223, by rfl⟩ : syracuseStep 2329631 = 3494447) B3494447
theorem B11799593 : Blo 1032607 11799593 := bstep (se 2 (by rfl) ⟨4424847, by rfl⟩ : syracuseStep 11799593 = 8849695) B8849695
theorem B2331035 : Blo 1032607 2331035 := bstep (se 1 (by rfl) ⟨1748276, by rfl⟩ : syracuseStep 2331035 = 3496553) B3496553
theorem B3150845 : Blo 1032607 3150845 := bstep (se 3 (by rfl) ⟨590783, by rfl⟩ : syracuseStep 3150845 = 1181567) B1181567
theorem B61281785 : Blo 1032607 61281785 := bstep (se 2 (by rfl) ⟨22980669, by rfl⟩ : syracuseStep 61281785 = 45961339) B45961339
theorem B11179637 : Blo 1032607 11179637 := bstep (se 5 (by rfl) ⟨524045, by rfl⟩ : syracuseStep 11179637 = 1048091) B1048091
theorem B6461491 : Blo 1032607 6461491 := bstep (se 1 (by rfl) ⟨4846118, by rfl⟩ : syracuseStep 6461491 = 9692237) B9692237
theorem B8854343 : Blo 1032607 8854343 := bstep (se 1 (by rfl) ⟨6640757, by rfl⟩ : syracuseStep 8854343 = 13281515) B13281515
theorem B2236187 : Blo 1032607 2236187 := bstep (se 1 (by rfl) ⟨1677140, by rfl⟩ : syracuseStep 2236187 = 3354281) B3354281
theorem B1549031 : Blo 1032607 1549031 := bstep (se 1 (by rfl) ⟨1161773, by rfl⟩ : syracuseStep 1549031 = 2323547) B2323547
theorem B56533859 : Blo 1032607 56533859 := bstep (se 1 (by rfl) ⟨42400394, by rfl⟩ : syracuseStep 56533859 = 84800789) B84800789
theorem B1549823 : Blo 1032607 1549823 := bstep (se 1 (by rfl) ⟨1162367, by rfl⟩ : syracuseStep 1549823 = 2324735) B2324735
theorem B8824787 : Blo 1032607 8824787 := bstep (se 1 (by rfl) ⟨6618590, by rfl⟩ : syracuseStep 8824787 = 13237181) B13237181
theorem B8956007 : Blo 1032607 8956007 := bstep (se 1 (by rfl) ⟨6717005, by rfl⟩ : syracuseStep 8956007 = 13434011) B13434011
theorem B3319969 : Blo 1032607 3319969 := bstep (se 2 (by rfl) ⟨1244988, by rfl⟩ : syracuseStep 3319969 = 2489977) B2489977
theorem B1550747 : Blo 1032607 1550747 := bstep (se 1 (by rfl) ⟨1163060, by rfl⟩ : syracuseStep 1550747 = 2326121) B2326121
theorem B1551527 : Blo 1032607 1551527 := bstep (se 1 (by rfl) ⟨1163645, by rfl⟩ : syracuseStep 1551527 = 2327291) B2327291
theorem B1551599 : Blo 1032607 1551599 := bstep (se 1 (by rfl) ⟨1163699, by rfl⟩ : syracuseStep 1551599 = 2327399) B2327399
theorem B1748479 : Blo 1032607 1748479 := bstep (se 1 (by rfl) ⟨1311359, by rfl⟩ : syracuseStep 1748479 = 2622719) B2622719
theorem B1552031 : Blo 1032607 1552031 := bstep (se 1 (by rfl) ⟨1164023, by rfl⟩ : syracuseStep 1552031 = 2328047) B2328047
theorem B1552103 : Blo 1032607 1552103 := bstep (se 1 (by rfl) ⟨1164077, by rfl⟩ : syracuseStep 1552103 = 2328155) B2328155
theorem B1552319 : Blo 1032607 1552319 := bstep (se 1 (by rfl) ⟨1164239, by rfl⟩ : syracuseStep 1552319 = 2328479) B2328479
theorem B12595583 : Blo 1032607 12595583 := bstep (se 1 (by rfl) ⟨9446687, by rfl⟩ : syracuseStep 12595583 = 18893375) B18893375
theorem B3486239 : Blo 1032607 3486239 := bstep (se 1 (by rfl) ⟨2614679, by rfl⟩ : syracuseStep 3486239 = 5229359) B5229359
theorem B8828783 : Blo 1032607 8828783 := bstep (se 1 (by rfl) ⟨6621587, by rfl⟩ : syracuseStep 8828783 = 13243175) B13243175
theorem B1554431 : Blo 1032607 1554431 := bstep (se 1 (by rfl) ⟨1165823, by rfl⟩ : syracuseStep 1554431 = 2331647) B2331647
theorem B1162543 : Blo 1032607 1162543 := bstep (se 1 (by rfl) ⟨871907, by rfl⟩ : syracuseStep 1162543 = 1743815) B1743815
theorem B1162687 : Blo 1032607 1162687 := bstep (se 1 (by rfl) ⟨872015, by rfl⟩ : syracuseStep 1162687 = 1744031) B1744031
theorem B1033031 : Blo 1032607 1033031 := bstep (se 1 (by rfl) ⟨774773, by rfl⟩ : syracuseStep 1033031 = 1549547) B1549547
theorem B1033051 : Blo 1032607 1033051 := bstep (se 1 (by rfl) ⟨774788, by rfl⟩ : syracuseStep 1033051 = 1549577) B1549577
theorem B9421991 : Blo 1032607 9421991 := bstep (se 1 (by rfl) ⟨7066493, by rfl⟩ : syracuseStep 9421991 = 14132987) B14132987
theorem B1033631 : Blo 1032607 1033631 := bstep (se 1 (by rfl) ⟨775223, by rfl⟩ : syracuseStep 1033631 = 1550447) B1550447
theorem B1033935 : Blo 1032607 1033935 := bstep (se 1 (by rfl) ⟨775451, by rfl⟩ : syracuseStep 1033935 = 1550903) B1550903
theorem B1034075 : Blo 1032607 1034075 := bstep (se 1 (by rfl) ⟨775556, by rfl⟩ : syracuseStep 1034075 = 1551113) B1551113
theorem B5032039 : Blo 1032607 5032039 := bstep (se 1 (by rfl) ⟨3774029, by rfl⟩ : syracuseStep 5032039 = 7548059) B7548059
theorem B1165423 : Blo 1032607 1165423 := bstep (se 1 (by rfl) ⟨874067, by rfl⟩ : syracuseStep 1165423 = 1748135) B1748135
theorem B1034567 : Blo 1032607 1034567 := bstep (se 1 (by rfl) ⟨775925, by rfl⟩ : syracuseStep 1034567 = 1551851) B1551851
theorem B3983849 : Blo 1032607 3983849 := bstep (se 2 (by rfl) ⟨1493943, by rfl⟩ : syracuseStep 3983849 = 2987887) B2987887
theorem B13421159 : Blo 1032607 13421159 := bstep (se 1 (by rfl) ⟨10065869, by rfl⟩ : syracuseStep 13421159 = 20131739) B20131739
theorem B1034959 : Blo 1032607 1034959 := bstep (se 1 (by rfl) ⟨776219, by rfl⟩ : syracuseStep 1034959 = 1552439) B1552439
theorem B63654821 : Blo 1032607 63654821 := bstep (se 4 (by rfl) ⟨5967639, by rfl⟩ : syracuseStep 63654821 = 11935279) B11935279
theorem B1035263 : Blo 1032607 1035263 := bstep (se 1 (by rfl) ⟨776447, by rfl⟩ : syracuseStep 1035263 = 1552895) B1552895
theorem B1035291 : Blo 1032607 1035291 := bstep (se 1 (by rfl) ⟨776468, by rfl⟩ : syracuseStep 1035291 = 1552937) B1552937
theorem B1035355 : Blo 1032607 1035355 := bstep (se 1 (by rfl) ⟨776516, by rfl⟩ : syracuseStep 1035355 = 1553033) B1553033
theorem B1035367 : Blo 1032607 1035367 := bstep (se 1 (by rfl) ⟨776525, by rfl⟩ : syracuseStep 1035367 = 1553051) B1553051
theorem B1035419 : Blo 1032607 1035419 := bstep (se 1 (by rfl) ⟨776564, by rfl⟩ : syracuseStep 1035419 = 1553129) B1553129
theorem B1035935 : Blo 1032607 1035935 := bstep (se 1 (by rfl) ⟨776951, by rfl⟩ : syracuseStep 1035935 = 1553903) B1553903
theorem B1036031 : Blo 1032607 1036031 := bstep (se 1 (by rfl) ⟨777023, by rfl⟩ : syracuseStep 1036031 = 1554047) B1554047
theorem B1036191 : Blo 1032607 1036191 := bstep (se 1 (by rfl) ⟨777143, by rfl⟩ : syracuseStep 1036191 = 1554287) B1554287
theorem B4411385 : Blo 1032607 4411385 := bstep (se 2 (by rfl) ⟨1654269, by rfl⟩ : syracuseStep 4411385 = 3308539) B3308539
theorem B1036399 : Blo 1032607 1036399 := bstep (se 1 (by rfl) ⟨777299, by rfl⟩ : syracuseStep 1036399 = 1554599) B1554599
theorem B10080521 : Blo 1032607 10080521 := bstep (se 2 (by rfl) ⟨3780195, by rfl⟩ : syracuseStep 10080521 = 7560391) B7560391
theorem B31839713 : Blo 1032607 31839713 := bstep (se 2 (by rfl) ⟨11939892, by rfl⟩ : syracuseStep 31839713 = 23879785) B23879785
theorem B23910079 : Blo 1032607 23910079 := bstep (se 1 (by rfl) ⟨17932559, by rfl⟩ : syracuseStep 23910079 = 35865119) B35865119
theorem B2615399 : Blo 1032607 2615399 := bstep (se 1 (by rfl) ⟨1961549, by rfl⟩ : syracuseStep 2615399 = 3923099) B3923099
theorem B5892689 : Blo 1032607 5892689 := bstep (se 2 (by rfl) ⟨2209758, by rfl⟩ : syracuseStep 5892689 = 4419517) B4419517
theorem B5238269 : Blo 1032607 5238269 := bstep (se 3 (by rfl) ⟨982175, by rfl⟩ : syracuseStep 5238269 = 1964351) B1964351
theorem B17657837 : Blo 1032607 17657837 := bstep (se 3 (by rfl) ⟨3310844, by rfl⟩ : syracuseStep 17657837 = 6621689) B6621689
theorem B2617535 : Blo 1032607 2617535 := bstep (se 1 (by rfl) ⟨1963151, by rfl⟩ : syracuseStep 2617535 = 3926303) B3926303
theorem B61370941 : Blo 1032607 61370941 := bstep (se 3 (by rfl) ⟨11507051, by rfl⟩ : syracuseStep 61370941 = 23014103) B23014103
theorem B4977263 : Blo 1032607 4977263 := bstep (se 1 (by rfl) ⟨3732947, by rfl⟩ : syracuseStep 4977263 = 7465895) B7465895
theorem B4420595 : Blo 1032607 4420595 := bstep (se 1 (by rfl) ⟨3315446, by rfl⟩ : syracuseStep 4420595 = 6630893) B6630893
theorem B2323583 : Blo 1032607 2323583 := bstep (se 1 (by rfl) ⟨1742687, by rfl⟩ : syracuseStep 2323583 = 3485375) B3485375
theorem B4421567 : Blo 1032607 4421567 := bstep (se 1 (by rfl) ⟨3316175, by rfl⟩ : syracuseStep 4421567 = 6632351) B6632351
theorem B2619499 : Blo 1032607 2619499 := bstep (se 1 (by rfl) ⟨1964624, by rfl⟩ : syracuseStep 2619499 = 3929249) B3929249
theorem B6617771 : Blo 1032607 6617771 := bstep (se 1 (by rfl) ⟨4963328, by rfl⟩ : syracuseStep 6617771 = 9926657) B9926657
theorem B1965217 : Blo 1032607 1965217 := bstep (se 2 (by rfl) ⟨736956, by rfl⟩ : syracuseStep 1965217 = 1473913) B1473913
theorem B2326409 : Blo 1032607 2326409 := bstep (se 2 (by rfl) ⟨872403, by rfl⟩ : syracuseStep 2326409 = 1744807) B1744807
theorem B2621423 : Blo 1032607 2621423 := bstep (se 1 (by rfl) ⟨1966067, by rfl⟩ : syracuseStep 2621423 = 3932135) B3932135
theorem B2490439 : Blo 1032607 2490439 := bstep (se 1 (by rfl) ⟨1867829, by rfl⟩ : syracuseStep 2490439 = 3735659) B3735659
theorem B18874691 : Blo 1032607 18874691 := bstep (se 1 (by rfl) ⟨14156018, by rfl⟩ : syracuseStep 18874691 = 28312037) B28312037
theorem B6619639 : Blo 1032607 6619639 := bstep (se 1 (by rfl) ⟨4964729, by rfl⟩ : syracuseStep 6619639 = 9929459) B9929459
theorem B2655899 : Blo 1032607 2655899 := bstep (se 1 (by rfl) ⟨1991924, by rfl⟩ : syracuseStep 2655899 = 3983849) B3983849
theorem B59639489 : Blo 1032607 59639489 := bstep (se 2 (by rfl) ⟨22364808, by rfl⟩ : syracuseStep 59639489 = 44729617) B44729617
theorem B8947439 : Blo 1032607 8947439 := bstep (se 1 (by rfl) ⟨6710579, by rfl⟩ : syracuseStep 8947439 = 13421159) B13421159
theorem B42436547 : Blo 1032607 42436547 := bstep (se 1 (by rfl) ⟨31827410, by rfl⟩ : syracuseStep 42436547 = 63654821) B63654821
theorem B7866395 : Blo 1032607 7866395 := bstep (se 1 (by rfl) ⟨5899796, by rfl⟩ : syracuseStep 7866395 = 11799593) B11799593
theorem B6720347 : Blo 1032607 6720347 := bstep (se 1 (by rfl) ⟨5040260, by rfl⟩ : syracuseStep 6720347 = 10080521) B10080521
theorem B4426625 : Blo 1032607 4426625 := bstep (se 2 (by rfl) ⟨1659984, by rfl⟩ : syracuseStep 4426625 = 3319969) B3319969
theorem B2100563 : Blo 1032607 2100563 := bstep (se 1 (by rfl) ⟨1575422, by rfl⟩ : syracuseStep 2100563 = 3150845) B3150845
theorem B163418093 : Blo 1032607 163418093 := bstep (se 3 (by rfl) ⟨30640892, by rfl⟩ : syracuseStep 163418093 = 61281785) B61281785
theorem B5902895 : Blo 1032607 5902895 := bstep (se 1 (by rfl) ⟨4427171, by rfl⟩ : syracuseStep 5902895 = 8854343) B8854343
theorem B2331305 : Blo 1032607 2331305 := bstep (se 2 (by rfl) ⟨874239, by rfl⟩ : syracuseStep 2331305 = 1748479) B1748479
theorem B37689239 : Blo 1032607 37689239 := bstep (se 1 (by rfl) ⟨28266929, by rfl⟩ : syracuseStep 37689239 = 56533859) B56533859
theorem B81827921 : Blo 1032607 81827921 := bstep (se 2 (by rfl) ⟨30685470, by rfl⟩ : syracuseStep 81827921 = 61370941) B61370941
theorem B1743599 : Blo 1032607 1743599 := bstep (se 1 (by rfl) ⟨1307699, by rfl⟩ : syracuseStep 1743599 = 2615399) B2615399
theorem B5970671 : Blo 1032607 5970671 := bstep (se 1 (by rfl) ⟨4478003, by rfl⟩ : syracuseStep 5970671 = 8956007) B8956007
theorem B11771891 : Blo 1032607 11771891 := bstep (se 1 (by rfl) ⟨8828918, by rfl⟩ : syracuseStep 11771891 = 17657837) B17657837
theorem B1745023 : Blo 1032607 1745023 := bstep (se 1 (by rfl) ⟨1308767, by rfl⟩ : syracuseStep 1745023 = 2617535) B2617535
theorem B8397055 : Blo 1032607 8397055 := bstep (se 1 (by rfl) ⟨6297791, by rfl⟩ : syracuseStep 8397055 = 12595583) B12595583
theorem B3318175 : Blo 1032607 3318175 := bstep (se 1 (by rfl) ⟨2488631, by rfl⟩ : syracuseStep 3318175 = 4977263) B4977263
theorem B1549055 : Blo 1032607 1549055 := bstep (se 1 (by rfl) ⟨1161791, by rfl⟩ : syracuseStep 1549055 = 2323583) B2323583
theorem B1550057 : Blo 1032607 1550057 := bstep (se 2 (by rfl) ⟨581271, by rfl⟩ : syracuseStep 1550057 = 1162543) B1162543
theorem B1550249 : Blo 1032607 1550249 := bstep (se 2 (by rfl) ⟨581343, by rfl⟩ : syracuseStep 1550249 = 1162687) B1162687
theorem B1550939 : Blo 1032607 1550939 := bstep (se 1 (by rfl) ⟨1163204, by rfl⟩ : syracuseStep 1550939 = 2326409) B2326409
theorem B1747615 : Blo 1032607 1747615 := bstep (se 1 (by rfl) ⟨1310711, by rfl⟩ : syracuseStep 1747615 = 2621423) B2621423
theorem B11774807 : Blo 1032607 11774807 := bstep (se 1 (by rfl) ⟨8831105, by rfl⟩ : syracuseStep 11774807 = 17662211) B17662211
theorem B3320777 : Blo 1032607 3320777 := bstep (se 2 (by rfl) ⟨1245291, by rfl⟩ : syracuseStep 3320777 = 2490583) B2490583
theorem B1551515 : Blo 1032607 1551515 := bstep (se 1 (by rfl) ⟨1163636, by rfl⟩ : syracuseStep 1551515 = 2327273) B2327273
theorem B1552091 : Blo 1032607 1552091 := bstep (se 1 (by rfl) ⟨1164068, by rfl⟩ : syracuseStep 1552091 = 2328137) B2328137
theorem B1552799 : Blo 1032607 1552799 := bstep (se 1 (by rfl) ⟨1164599, by rfl⟩ : syracuseStep 1552799 = 2329199) B2329199
theorem B1552871 : Blo 1032607 1552871 := bstep (se 1 (by rfl) ⟨1164653, by rfl⟩ : syracuseStep 1552871 = 2329307) B2329307
theorem B1553087 : Blo 1032607 1553087 := bstep (se 1 (by rfl) ⟨1164815, by rfl⟩ : syracuseStep 1553087 = 2329631) B2329631
theorem B1553897 : Blo 1032607 1553897 := bstep (se 2 (by rfl) ⟨582711, by rfl⟩ : syracuseStep 1553897 = 1165423) B1165423
theorem B1554023 : Blo 1032607 1554023 := bstep (se 1 (by rfl) ⟨1165517, by rfl⟩ : syracuseStep 1554023 = 2331035) B2331035
theorem B7453091 : Blo 1032607 7453091 := bstep (se 1 (by rfl) ⟨5589818, by rfl⟩ : syracuseStep 7453091 = 11179637) B11179637
theorem B77610757 : Blo 1032607 77610757 := bstep (se 4 (by rfl) ⟨7276008, by rfl⟩ : syracuseStep 77610757 = 14552017) B14552017
theorem B1032687 : Blo 1032607 1032687 := bstep (se 1 (by rfl) ⟨774515, by rfl⟩ : syracuseStep 1032687 = 1549031) B1549031
theorem B1033215 : Blo 1032607 1033215 := bstep (se 1 (by rfl) ⟨774911, by rfl⟩ : syracuseStep 1033215 = 1549823) B1549823
theorem B5883191 : Blo 1032607 5883191 := bstep (se 1 (by rfl) ⟨4412393, by rfl⟩ : syracuseStep 5883191 = 8824787) B8824787
theorem B1033831 : Blo 1032607 1033831 := bstep (se 1 (by rfl) ⟨775373, by rfl⟩ : syracuseStep 1033831 = 1550747) B1550747
theorem B1034351 : Blo 1032607 1034351 := bstep (se 1 (by rfl) ⟨775763, by rfl⟩ : syracuseStep 1034351 = 1551527) B1551527
theorem B1034399 : Blo 1032607 1034399 := bstep (se 1 (by rfl) ⟨775799, by rfl⟩ : syracuseStep 1034399 = 1551599) B1551599
theorem B3492179 : Blo 1032607 3492179 := bstep (se 1 (by rfl) ⟨2619134, by rfl⟩ : syracuseStep 3492179 = 5238269) B5238269
theorem B1034687 : Blo 1032607 1034687 := bstep (se 1 (by rfl) ⟨776015, by rfl⟩ : syracuseStep 1034687 = 1552031) B1552031
theorem B1034735 : Blo 1032607 1034735 := bstep (se 1 (by rfl) ⟨776051, by rfl⟩ : syracuseStep 1034735 = 1552103) B1552103
theorem B1034879 : Blo 1032607 1034879 := bstep (se 1 (by rfl) ⟨776159, by rfl⟩ : syracuseStep 1034879 = 1552319) B1552319
theorem B3492665 : Blo 1032607 3492665 := bstep (se 2 (by rfl) ⟨1309749, by rfl⟩ : syracuseStep 3492665 = 2619499) B2619499
theorem B5885855 : Blo 1032607 5885855 := bstep (se 1 (by rfl) ⟨4414391, by rfl⟩ : syracuseStep 5885855 = 8828783) B8828783
theorem B1036287 : Blo 1032607 1036287 := bstep (se 1 (by rfl) ⟨777215, by rfl⟩ : syracuseStep 1036287 = 1554431) B1554431
theorem B4411847 : Blo 1032607 4411847 := bstep (se 1 (by rfl) ⟨3308885, by rfl⟩ : syracuseStep 4411847 = 6617771) B6617771
theorem B5593151 : Blo 1032607 5593151 := bstep (se 1 (by rfl) ⟨4194863, by rfl⟩ : syracuseStep 5593151 = 8389727) B8389727
theorem B6281327 : Blo 1032607 6281327 := bstep (se 1 (by rfl) ⟨4710995, by rfl⟩ : syracuseStep 6281327 = 9421991) B9421991
theorem B6641783 : Blo 1032607 6641783 := bstep (se 1 (by rfl) ⟨4981337, by rfl⟩ : syracuseStep 6641783 = 9962675) B9962675
theorem B14178527 : Blo 1032607 14178527 := bstep (se 1 (by rfl) ⟨10633895, by rfl⟩ : syracuseStep 14178527 = 21267791) B21267791
theorem B15948683 : Blo 1032607 15948683 := bstep (se 1 (by rfl) ⟨11961512, by rfl⟩ : syracuseStep 15948683 = 23923025) B23923025
theorem B1400105 : Blo 1032607 1400105 := bstep (se 2 (by rfl) ⟨525039, by rfl⟩ : syracuseStep 1400105 = 1050079) B1050079
theorem B2940923 : Blo 1032607 2940923 := bstep (se 1 (by rfl) ⟨2205692, by rfl⟩ : syracuseStep 2940923 = 4411385) B4411385
theorem B6709385 : Blo 1032607 6709385 := bstep (se 2 (by rfl) ⟨2516019, by rfl⟩ : syracuseStep 6709385 = 5032039) B5032039
theorem B21226475 : Blo 1032607 21226475 := bstep (se 1 (by rfl) ⟨15919856, by rfl⟩ : syracuseStep 21226475 = 31839713) B31839713
theorem B11790845 : Blo 1032607 11790845 := bstep (se 3 (by rfl) ⟨2210783, by rfl⟩ : syracuseStep 11790845 = 4421567) B4421567
theorem B3928459 : Blo 1032607 3928459 := bstep (se 1 (by rfl) ⟨2946344, by rfl⟩ : syracuseStep 3928459 = 5892689) B5892689
theorem B31880105 : Blo 1032607 31880105 := bstep (se 2 (by rfl) ⟨11955039, by rfl⟩ : syracuseStep 31880105 = 23910079) B23910079
theorem B8615321 : Blo 1032607 8615321 := bstep (se 2 (by rfl) ⟨3230745, by rfl⟩ : syracuseStep 8615321 = 6461491) B6461491
theorem B2324159 : Blo 1032607 2324159 := bstep (se 1 (by rfl) ⟨1743119, by rfl⟩ : syracuseStep 2324159 = 3486239) B3486239
theorem B2947063 : Blo 1032607 2947063 := bstep (se 1 (by rfl) ⟨2210297, by rfl⟩ : syracuseStep 2947063 = 4420595) B4420595
theorem B2620289 : Blo 1032607 2620289 := bstep (se 2 (by rfl) ⟨982608, by rfl⟩ : syracuseStep 2620289 = 1965217) B1965217
theorem B5963165 : Blo 1032607 5963165 := bstep (se 3 (by rfl) ⟨1118093, by rfl⟩ : syracuseStep 5963165 = 2236187) B2236187
theorem B2326697 : Blo 1032607 2326697 := bstep (se 2 (by rfl) ⟨872511, by rfl⟩ : syracuseStep 2326697 = 1745023) B1745023
theorem B12583127 : Blo 1032607 12583127 := bstep (se 1 (by rfl) ⟨9437345, by rfl⟩ : syracuseStep 12583127 = 18874691) B18874691
theorem B4424233 : Blo 1032607 4424233 := bstep (se 2 (by rfl) ⟨1659087, by rfl⟩ : syracuseStep 4424233 = 3318175) B3318175
theorem B1770599 : Blo 1032607 1770599 := bstep (se 1 (by rfl) ⟨1327949, by rfl⟩ : syracuseStep 1770599 = 2655899) B2655899
theorem B5964959 : Blo 1032607 5964959 := bstep (se 1 (by rfl) ⟨4473719, by rfl⟩ : syracuseStep 5964959 = 8947439) B8947439
theorem B5244263 : Blo 1032607 5244263 := bstep (se 1 (by rfl) ⟨3933197, by rfl⟩ : syracuseStep 5244263 = 7866395) B7866395
theorem B2328119 : Blo 1032607 2328119 := bstep (se 1 (by rfl) ⟨1746089, by rfl⟩ : syracuseStep 2328119 = 3492179) B3492179
theorem B2328443 : Blo 1032607 2328443 := bstep (se 1 (by rfl) ⟨1746332, by rfl⟩ : syracuseStep 2328443 = 3492665) B3492665
theorem B2951083 : Blo 1032607 2951083 := bstep (se 1 (by rfl) ⟨2213312, by rfl⟩ : syracuseStep 2951083 = 4426625) B4426625
theorem B3935263 : Blo 1032607 3935263 := bstep (se 1 (by rfl) ⟨2951447, by rfl⟩ : syracuseStep 3935263 = 5902895) B5902895
theorem B2330153 : Blo 1032607 2330153 := bstep (se 2 (by rfl) ⟨873807, by rfl⟩ : syracuseStep 2330153 = 1747615) B1747615
theorem B4427855 : Blo 1032607 4427855 := bstep (se 1 (by rfl) ⟨3320891, by rfl⟩ : syracuseStep 4427855 = 6641783) B6641783
theorem B218207789 : Blo 1032607 218207789 := bstep (se 3 (by rfl) ⟨40913960, by rfl⟩ : syracuseStep 218207789 = 81827921) B81827921
theorem B8855405 : Blo 1032607 8855405 := bstep (se 3 (by rfl) ⟨1660388, by rfl⟩ : syracuseStep 8855405 = 3320777) B3320777
theorem B5743547 : Blo 1032607 5743547 := bstep (se 1 (by rfl) ⟨4307660, by rfl⟩ : syracuseStep 5743547 = 8615321) B8615321
theorem B1549439 : Blo 1032607 1549439 := bstep (se 1 (by rfl) ⟨1162079, by rfl⟩ : syracuseStep 1549439 = 2324159) B2324159
theorem B1746859 : Blo 1032607 1746859 := bstep (se 1 (by rfl) ⟨1310144, by rfl⟩ : syracuseStep 1746859 = 2620289) B2620289
theorem B3975443 : Blo 1032607 3975443 := bstep (se 1 (by rfl) ⟨2981582, by rfl⟩ : syracuseStep 3975443 = 5963165) B5963165
theorem B3320585 : Blo 1032607 3320585 := bstep (se 2 (by rfl) ⟨1245219, by rfl⟩ : syracuseStep 3320585 = 2490439) B2490439
theorem B8826185 : Blo 1032607 8826185 := bstep (se 2 (by rfl) ⟨3309819, by rfl⟩ : syracuseStep 8826185 = 6619639) B6619639
theorem B39759659 : Blo 1032607 39759659 := bstep (se 1 (by rfl) ⟨29819744, by rfl⟩ : syracuseStep 39759659 = 59639489) B59639489
theorem B28291031 : Blo 1032607 28291031 := bstep (se 1 (by rfl) ⟨21218273, by rfl⟩ : syracuseStep 28291031 = 42436547) B42436547
theorem B56603933 : Blo 1032607 56603933 := bstep (se 3 (by rfl) ⟨10613237, by rfl⟩ : syracuseStep 56603933 = 21226475) B21226475
theorem B1554203 : Blo 1032607 1554203 := bstep (se 1 (by rfl) ⟨1165652, by rfl⟩ : syracuseStep 1554203 = 2331305) B2331305
theorem B9452351 : Blo 1032607 9452351 := bstep (se 1 (by rfl) ⟨7089263, by rfl⟩ : syracuseStep 9452351 = 14178527) B14178527
theorem B1162399 : Blo 1032607 1162399 := bstep (se 1 (by rfl) ⟨871799, by rfl⟩ : syracuseStep 1162399 = 1743599) B1743599
theorem B3980447 : Blo 1032607 3980447 := bstep (se 1 (by rfl) ⟨2985335, by rfl⟩ : syracuseStep 3980447 = 5970671) B5970671
theorem B10632455 : Blo 1032607 10632455 := bstep (se 1 (by rfl) ⟨7974341, by rfl⟩ : syracuseStep 10632455 = 15948683) B15948683
theorem B7847927 : Blo 1032607 7847927 := bstep (se 1 (by rfl) ⟨5885945, by rfl⟩ : syracuseStep 7847927 = 11771891) B11771891
theorem B4472923 : Blo 1032607 4472923 := bstep (se 1 (by rfl) ⟨3354692, by rfl⟩ : syracuseStep 4472923 = 6709385) B6709385
theorem B1032703 : Blo 1032607 1032703 := bstep (se 1 (by rfl) ⟨774527, by rfl⟩ : syracuseStep 1032703 = 1549055) B1549055
theorem B19874909 : Blo 1032607 19874909 := bstep (se 3 (by rfl) ⟨3726545, by rfl⟩ : syracuseStep 19874909 = 7453091) B7453091
theorem B1033371 : Blo 1032607 1033371 := bstep (se 1 (by rfl) ⟨775028, by rfl⟩ : syracuseStep 1033371 = 1550057) B1550057
theorem B1033499 : Blo 1032607 1033499 := bstep (se 1 (by rfl) ⟨775124, by rfl⟩ : syracuseStep 1033499 = 1550249) B1550249
theorem B1033959 : Blo 1032607 1033959 := bstep (se 1 (by rfl) ⟨775469, by rfl⟩ : syracuseStep 1033959 = 1550939) B1550939
theorem B7849871 : Blo 1032607 7849871 := bstep (se 1 (by rfl) ⟨5887403, by rfl⟩ : syracuseStep 7849871 = 11774807) B11774807
theorem B1034343 : Blo 1032607 1034343 := bstep (se 1 (by rfl) ⟨775757, by rfl⟩ : syracuseStep 1034343 = 1551515) B1551515
theorem B1034727 : Blo 1032607 1034727 := bstep (se 1 (by rfl) ⟨776045, by rfl⟩ : syracuseStep 1034727 = 1552091) B1552091
theorem B1035199 : Blo 1032607 1035199 := bstep (se 1 (by rfl) ⟨776399, by rfl⟩ : syracuseStep 1035199 = 1552799) B1552799
theorem B1035247 : Blo 1032607 1035247 := bstep (se 1 (by rfl) ⟨776435, by rfl⟩ : syracuseStep 1035247 = 1552871) B1552871
theorem B1035391 : Blo 1032607 1035391 := bstep (se 1 (by rfl) ⟨776543, by rfl⟩ : syracuseStep 1035391 = 1553087) B1553087
theorem B21253403 : Blo 1032607 21253403 := bstep (se 1 (by rfl) ⟨15940052, by rfl⟩ : syracuseStep 21253403 = 31880105) B31880105
theorem B1035931 : Blo 1032607 1035931 := bstep (se 1 (by rfl) ⟨776948, by rfl⟩ : syracuseStep 1035931 = 1553897) B1553897
theorem B1036015 : Blo 1032607 1036015 := bstep (se 1 (by rfl) ⟨777011, by rfl⟩ : syracuseStep 1036015 = 1554023) B1554023
theorem B11196073 : Blo 1032607 11196073 := bstep (se 2 (by rfl) ⟨4198527, by rfl⟩ : syracuseStep 11196073 = 8397055) B8397055
theorem B3922127 : Blo 1032607 3922127 := bstep (se 1 (by rfl) ⟨2941595, by rfl⟩ : syracuseStep 3922127 = 5883191) B5883191
theorem B4480231 : Blo 1032607 4480231 := bstep (se 1 (by rfl) ⟨3360173, by rfl⟩ : syracuseStep 4480231 = 6720347) B6720347
theorem B1400375 : Blo 1032607 1400375 := bstep (se 1 (by rfl) ⟨1050281, by rfl⟩ : syracuseStep 1400375 = 2100563) B2100563
theorem B3923903 : Blo 1032607 3923903 := bstep (se 1 (by rfl) ⟨2942927, by rfl⟩ : syracuseStep 3923903 = 5885855) B5885855
theorem B108945395 : Blo 1032607 108945395 := bstep (se 1 (by rfl) ⟨81709046, by rfl⟩ : syracuseStep 108945395 = 163418093) B163418093
theorem B2941231 : Blo 1032607 2941231 := bstep (se 1 (by rfl) ⟨2205923, by rfl⟩ : syracuseStep 2941231 = 4411847) B4411847
theorem B25126159 : Blo 1032607 25126159 := bstep (se 1 (by rfl) ⟨18844619, by rfl⟩ : syracuseStep 25126159 = 37689239) B37689239
theorem B3728767 : Blo 1032607 3728767 := bstep (se 1 (by rfl) ⟨2796575, by rfl⟩ : syracuseStep 3728767 = 5593151) B5593151
theorem B4187551 : Blo 1032607 4187551 := bstep (se 1 (by rfl) ⟨3140663, by rfl⟩ : syracuseStep 4187551 = 6281327) B6281327
theorem B1960615 : Blo 1032607 1960615 := bstep (se 1 (by rfl) ⟨1470461, by rfl⟩ : syracuseStep 1960615 = 2940923) B2940923
theorem B5237945 : Blo 1032607 5237945 := bstep (se 2 (by rfl) ⟨1964229, by rfl⟩ : syracuseStep 5237945 = 3928459) B3928459
theorem B7860563 : Blo 1032607 7860563 := bstep (se 1 (by rfl) ⟨5895422, by rfl⟩ : syracuseStep 7860563 = 11790845) B11790845
theorem B3929417 : Blo 1032607 3929417 := bstep (se 2 (by rfl) ⟨1473531, by rfl⟩ : syracuseStep 3929417 = 2947063) B2947063
theorem B3733613 : Blo 1032607 3733613 := bstep (se 3 (by rfl) ⟨700052, by rfl⟩ : syracuseStep 3733613 = 1400105) B1400105
theorem B103481009 : Blo 1032607 103481009 := bstep (se 2 (by rfl) ⟨38805378, by rfl⟩ : syracuseStep 103481009 = 77610757) B77610757
theorem B5963897 : Blo 1032607 5963897 := bstep (se 2 (by rfl) ⟨2236461, by rfl⟩ : syracuseStep 5963897 = 4472923) B4472923
theorem B33555005 : Blo 1032607 33555005 := bstep (se 3 (by rfl) ⟨6291563, by rfl⟩ : syracuseStep 33555005 = 12583127) B12583127
theorem B5898977 : Blo 1032607 5898977 := bstep (se 2 (by rfl) ⟨2212116, by rfl⟩ : syracuseStep 5898977 = 4424233) B4424233
theorem B2329145 : Blo 1032607 2329145 := bstep (se 2 (by rfl) ⟨873429, by rfl⟩ : syracuseStep 2329145 = 1746859) B1746859
theorem B3934777 : Blo 1032607 3934777 := bstep (se 2 (by rfl) ⟨1475541, by rfl⟩ : syracuseStep 3934777 = 2951083) B2951083
theorem B2951903 : Blo 1032607 2951903 := bstep (se 1 (by rfl) ⟨2213927, by rfl⟩ : syracuseStep 2951903 = 4427855) B4427855
theorem B4721597 : Blo 1032607 4721597 := bstep (se 3 (by rfl) ⟨885299, by rfl⟩ : syracuseStep 4721597 = 1770599) B1770599
theorem B5247017 : Blo 1032607 5247017 := bstep (se 2 (by rfl) ⟨1967631, by rfl⟩ : syracuseStep 5247017 = 3935263) B3935263
theorem B5903603 : Blo 1032607 5903603 := bstep (se 1 (by rfl) ⟨4427702, by rfl⟩ : syracuseStep 5903603 = 8855405) B8855405
theorem B1549865 : Blo 1032607 1549865 := bstep (se 2 (by rfl) ⟨581199, by rfl⟩ : syracuseStep 1549865 = 1162399) B1162399
theorem B5973641 : Blo 1032607 5973641 := bstep (se 2 (by rfl) ⟨2240115, by rfl⟩ : syracuseStep 5973641 = 4480231) B4480231
theorem B6301567 : Blo 1032607 6301567 := bstep (se 1 (by rfl) ⟨4726175, by rfl⟩ : syracuseStep 6301567 = 9452351) B9452351
theorem B7088303 : Blo 1032607 7088303 := bstep (se 1 (by rfl) ⟨5316227, by rfl⟩ : syracuseStep 7088303 = 10632455) B10632455
theorem B68987339 : Blo 1032607 68987339 := bstep (se 1 (by rfl) ⟨51740504, by rfl⟩ : syracuseStep 68987339 = 103481009) B103481009
theorem B1551131 : Blo 1032607 1551131 := bstep (se 1 (by rfl) ⟨1163348, by rfl⟩ : syracuseStep 1551131 = 2326697) B2326697
theorem B13249939 : Blo 1032607 13249939 := bstep (se 1 (by rfl) ⟨9937454, by rfl⟩ : syracuseStep 13249939 = 19874909) B19874909
theorem B1552079 : Blo 1032607 1552079 := bstep (se 1 (by rfl) ⟨1164059, by rfl⟩ : syracuseStep 1552079 = 2328119) B2328119
theorem B1552295 : Blo 1032607 1552295 := bstep (se 1 (by rfl) ⟨1164221, by rfl⟩ : syracuseStep 1552295 = 2328443) B2328443
theorem B33501545 : Blo 1032607 33501545 := bstep (se 2 (by rfl) ⟨12563079, by rfl⟩ : syracuseStep 33501545 = 25126159) B25126159
theorem B5583401 : Blo 1032607 5583401 := bstep (se 2 (by rfl) ⟨2093775, by rfl⟩ : syracuseStep 5583401 = 4187551) B4187551
theorem B14168935 : Blo 1032607 14168935 := bstep (se 1 (by rfl) ⟨10626701, by rfl⟩ : syracuseStep 14168935 = 21253403) B21253403
theorem B1553435 : Blo 1032607 1553435 := bstep (se 1 (by rfl) ⟨1165076, by rfl⟩ : syracuseStep 1553435 = 2330153) B2330153
theorem B15906557 : Blo 1032607 15906557 := bstep (se 3 (by rfl) ⟨2982479, by rfl⟩ : syracuseStep 15906557 = 5964959) B5964959
theorem B145471859 : Blo 1032607 145471859 := bstep (se 1 (by rfl) ⟨109103894, by rfl⟩ : syracuseStep 145471859 = 218207789) B218207789
theorem B72630263 : Blo 1032607 72630263 := bstep (se 1 (by rfl) ⟨54472697, by rfl⟩ : syracuseStep 72630263 = 108945395) B108945395
theorem B1032959 : Blo 1032607 1032959 := bstep (se 1 (by rfl) ⟨774719, by rfl⟩ : syracuseStep 1032959 = 1549439) B1549439
theorem B2213723 : Blo 1032607 2213723 := bstep (se 1 (by rfl) ⟨1660292, by rfl⟩ : syracuseStep 2213723 = 3320585) B3320585
theorem B3491963 : Blo 1032607 3491963 := bstep (se 1 (by rfl) ⟨2618972, by rfl⟩ : syracuseStep 3491963 = 5237945) B5237945
theorem B5884123 : Blo 1032607 5884123 := bstep (se 1 (by rfl) ⟨4413092, by rfl⟩ : syracuseStep 5884123 = 8826185) B8826185
theorem B14928097 : Blo 1032607 14928097 := bstep (se 2 (by rfl) ⟨5598036, by rfl⟩ : syracuseStep 14928097 = 11196073) B11196073
theorem B18860687 : Blo 1032607 18860687 := bstep (se 1 (by rfl) ⟨14145515, by rfl⟩ : syracuseStep 18860687 = 28291031) B28291031
theorem B37735955 : Blo 1032607 37735955 := bstep (se 1 (by rfl) ⟨28301966, by rfl⟩ : syracuseStep 37735955 = 56603933) B56603933
theorem B1036135 : Blo 1032607 1036135 := bstep (se 1 (by rfl) ⟨777101, by rfl⟩ : syracuseStep 1036135 = 1554203) B1554203
theorem B5231951 : Blo 1032607 5231951 := bstep (se 1 (by rfl) ⟨3923963, by rfl⟩ : syracuseStep 5231951 = 7847927) B7847927
theorem B3921641 : Blo 1032607 3921641 := bstep (se 2 (by rfl) ⟨1470615, by rfl⟩ : syracuseStep 3921641 = 2941231) B2941231
theorem B3496175 : Blo 1032607 3496175 := bstep (se 1 (by rfl) ⟨2622131, by rfl⟩ : syracuseStep 3496175 = 5244263) B5244263
theorem B5233247 : Blo 1032607 5233247 := bstep (se 1 (by rfl) ⟨3924935, by rfl⟩ : syracuseStep 5233247 = 7849871) B7849871
theorem B4971689 : Blo 1032607 4971689 := bstep (se 2 (by rfl) ⟨1864383, by rfl⟩ : syracuseStep 4971689 = 3728767) B3728767
theorem B2614153 : Blo 1032607 2614153 := bstep (se 2 (by rfl) ⟨980307, by rfl⟩ : syracuseStep 2614153 = 1960615) B1960615
theorem B2614751 : Blo 1032607 2614751 := bstep (se 1 (by rfl) ⟨1961063, by rfl⟩ : syracuseStep 2614751 = 3922127) B3922127
theorem B2615935 : Blo 1032607 2615935 := bstep (se 1 (by rfl) ⟨1961951, by rfl⟩ : syracuseStep 2615935 = 3923903) B3923903
theorem B3829031 : Blo 1032607 3829031 := bstep (se 1 (by rfl) ⟨2871773, by rfl⟩ : syracuseStep 3829031 = 5743547) B5743547
theorem B2650295 : Blo 1032607 2650295 := bstep (se 1 (by rfl) ⟨1987721, by rfl⟩ : syracuseStep 2650295 = 3975443) B3975443
theorem B26506439 : Blo 1032607 26506439 := bstep (se 1 (by rfl) ⟨19879829, by rfl⟩ : syracuseStep 26506439 = 39759659) B39759659
theorem B5240375 : Blo 1032607 5240375 := bstep (se 1 (by rfl) ⟨3930281, by rfl⟩ : syracuseStep 5240375 = 7860563) B7860563
theorem B2619611 : Blo 1032607 2619611 := bstep (se 1 (by rfl) ⟨1964708, by rfl⟩ : syracuseStep 2619611 = 3929417) B3929417
theorem B2489075 : Blo 1032607 2489075 := bstep (se 1 (by rfl) ⟨1866806, by rfl⟩ : syracuseStep 2489075 = 3733613) B3733613
theorem B3734333 : Blo 1032607 3734333 := bstep (se 3 (by rfl) ⟨700187, by rfl⟩ : syracuseStep 3734333 = 1400375) B1400375
theorem B2653631 : Blo 1032607 2653631 := bstep (se 1 (by rfl) ⟨1990223, by rfl⟩ : syracuseStep 2653631 = 3980447) B3980447
theorem B3932651 : Blo 1032607 3932651 := bstep (se 1 (by rfl) ⟨2949488, by rfl⟩ : syracuseStep 3932651 = 5898977) B5898977
theorem B1475815 : Blo 1032607 1475815 := bstep (se 1 (by rfl) ⟨1106861, by rfl⟩ : syracuseStep 1475815 = 2213723) B2213723
theorem B2327975 : Blo 1032607 2327975 := bstep (se 1 (by rfl) ⟨1745981, by rfl⟩ : syracuseStep 2327975 = 3491963) B3491963
theorem B3147731 : Blo 1032607 3147731 := bstep (se 1 (by rfl) ⟨2360798, by rfl⟩ : syracuseStep 3147731 = 4721597) B4721597
theorem B5246369 : Blo 1032607 5246369 := bstep (se 2 (by rfl) ⟨1967388, by rfl⟩ : syracuseStep 5246369 = 3934777) B3934777
theorem B3935735 : Blo 1032607 3935735 := bstep (se 1 (by rfl) ⟨2951801, by rfl⟩ : syracuseStep 3935735 = 5903603) B5903603
theorem B2330783 : Blo 1032607 2330783 := bstep (se 1 (by rfl) ⟨1748087, by rfl⟩ : syracuseStep 2330783 = 3496175) B3496175
theorem B17666585 : Blo 1032607 17666585 := bstep (se 2 (by rfl) ⟨6624969, by rfl⟩ : syracuseStep 17666585 = 13249939) B13249939
theorem B75567653 : Blo 1032607 75567653 := bstep (se 4 (by rfl) ⟨7084467, by rfl⟩ : syracuseStep 75567653 = 14168935) B14168935
theorem B3314459 : Blo 1032607 3314459 := bstep (se 1 (by rfl) ⟨2485844, by rfl⟩ : syracuseStep 3314459 = 4971689) B4971689
theorem B1743167 : Blo 1032607 1743167 := bstep (se 1 (by rfl) ⟨1307375, by rfl⟩ : syracuseStep 1743167 = 2614751) B2614751
theorem B4725535 : Blo 1032607 4725535 := bstep (se 1 (by rfl) ⟨3544151, by rfl⟩ : syracuseStep 4725535 = 7088303) B7088303
theorem B7871741 : Blo 1032607 7871741 := bstep (se 3 (by rfl) ⟨1475951, by rfl⟩ : syracuseStep 7871741 = 2951903) B2951903
theorem B17670959 : Blo 1032607 17670959 := bstep (se 1 (by rfl) ⟨13253219, by rfl⟩ : syracuseStep 17670959 = 26506439) B26506439
theorem B1746407 : Blo 1032607 1746407 := bstep (se 1 (by rfl) ⟨1309805, by rfl⟩ : syracuseStep 1746407 = 2619611) B2619611
theorem B3975931 : Blo 1032607 3975931 := bstep (se 1 (by rfl) ⟨2981948, by rfl⟩ : syracuseStep 3975931 = 5963897) B5963897
theorem B3485537 : Blo 1032607 3485537 := bstep (se 2 (by rfl) ⟨1307076, by rfl⟩ : syracuseStep 3485537 = 2614153) B2614153
theorem B1552763 : Blo 1032607 1552763 := bstep (se 1 (by rfl) ⟨1164572, by rfl⟩ : syracuseStep 1552763 = 2329145) B2329145
theorem B8402089 : Blo 1032607 8402089 := bstep (se 2 (by rfl) ⟨3150783, by rfl⟩ : syracuseStep 8402089 = 6301567) B6301567
theorem B7845497 : Blo 1032607 7845497 := bstep (se 2 (by rfl) ⟨2942061, by rfl⟩ : syracuseStep 7845497 = 5884123) B5884123
theorem B19904129 : Blo 1032607 19904129 := bstep (se 2 (by rfl) ⟨7464048, by rfl⟩ : syracuseStep 19904129 = 14928097) B14928097
theorem B3487913 : Blo 1032607 3487913 := bstep (se 2 (by rfl) ⟨1307967, by rfl⟩ : syracuseStep 3487913 = 2615935) B2615935
theorem B3487967 : Blo 1032607 3487967 := bstep (se 1 (by rfl) ⟨2615975, by rfl⟩ : syracuseStep 3487967 = 5231951) B5231951
theorem B3488831 : Blo 1032607 3488831 := bstep (se 1 (by rfl) ⟨2616623, by rfl⟩ : syracuseStep 3488831 = 5233247) B5233247
theorem B1033243 : Blo 1032607 1033243 := bstep (se 1 (by rfl) ⟨774932, by rfl⟩ : syracuseStep 1033243 = 1549865) B1549865
theorem B3982427 : Blo 1032607 3982427 := bstep (se 1 (by rfl) ⟨2986820, by rfl⟩ : syracuseStep 3982427 = 5973641) B5973641
theorem B45991559 : Blo 1032607 45991559 := bstep (se 1 (by rfl) ⟨34493669, by rfl⟩ : syracuseStep 45991559 = 68987339) B68987339
theorem B1034087 : Blo 1032607 1034087 := bstep (se 1 (by rfl) ⟨775565, by rfl⟩ : syracuseStep 1034087 = 1551131) B1551131
theorem B1034719 : Blo 1032607 1034719 := bstep (se 1 (by rfl) ⟨776039, by rfl⟩ : syracuseStep 1034719 = 1552079) B1552079
theorem B1034863 : Blo 1032607 1034863 := bstep (se 1 (by rfl) ⟨776147, by rfl⟩ : syracuseStep 1034863 = 1552295) B1552295
theorem B22334363 : Blo 1032607 22334363 := bstep (se 1 (by rfl) ⟨16750772, by rfl⟩ : syracuseStep 22334363 = 33501545) B33501545
theorem B3722267 : Blo 1032607 3722267 := bstep (se 1 (by rfl) ⟨2791700, by rfl⟩ : syracuseStep 3722267 = 5583401) B5583401
theorem B1035623 : Blo 1032607 1035623 := bstep (se 1 (by rfl) ⟨776717, by rfl⟩ : syracuseStep 1035623 = 1553435) B1553435
theorem B3493583 : Blo 1032607 3493583 := bstep (se 1 (by rfl) ⟨2620187, by rfl⟩ : syracuseStep 3493583 = 5240375) B5240375
theorem B10604371 : Blo 1032607 10604371 := bstep (se 1 (by rfl) ⟨7953278, by rfl⟩ : syracuseStep 10604371 = 15906557) B15906557
theorem B96981239 : Blo 1032607 96981239 := bstep (se 1 (by rfl) ⟨72735929, by rfl⟩ : syracuseStep 96981239 = 145471859) B145471859
theorem B1659383 : Blo 1032607 1659383 := bstep (se 1 (by rfl) ⟨1244537, by rfl⟩ : syracuseStep 1659383 = 2489075) B2489075
theorem B48420175 : Blo 1032607 48420175 := bstep (se 1 (by rfl) ⟨36315131, by rfl⟩ : syracuseStep 48420175 = 72630263) B72630263
theorem B22370003 : Blo 1032607 22370003 := bstep (se 1 (by rfl) ⟨16777502, by rfl⟩ : syracuseStep 22370003 = 33555005) B33555005
theorem B12573791 : Blo 1032607 12573791 := bstep (se 1 (by rfl) ⟨9430343, by rfl⟩ : syracuseStep 12573791 = 18860687) B18860687
theorem B25157303 : Blo 1032607 25157303 := bstep (se 1 (by rfl) ⟨18867977, by rfl⟩ : syracuseStep 25157303 = 37735955) B37735955
theorem B3498011 : Blo 1032607 3498011 := bstep (se 1 (by rfl) ⟨2623508, by rfl⟩ : syracuseStep 3498011 = 5247017) B5247017
theorem B2614427 : Blo 1032607 2614427 := bstep (se 1 (by rfl) ⟨1960820, by rfl⟩ : syracuseStep 2614427 = 3921641) B3921641
theorem B2552687 : Blo 1032607 2552687 := bstep (se 1 (by rfl) ⟨1914515, by rfl⟩ : syracuseStep 2552687 = 3829031) B3829031
theorem B1766863 : Blo 1032607 1766863 := bstep (se 1 (by rfl) ⟨1325147, by rfl⟩ : syracuseStep 1766863 = 2650295) B2650295
theorem B2489555 : Blo 1032607 2489555 := bstep (se 1 (by rfl) ⟨1867166, by rfl⟩ : syracuseStep 2489555 = 3734333) B3734333
theorem B1769087 : Blo 1032607 1769087 := bstep (se 1 (by rfl) ⟨1326815, by rfl⟩ : syracuseStep 1769087 = 2653631) B2653631
theorem B2621767 : Blo 1032607 2621767 := bstep (se 1 (by rfl) ⟨1966325, by rfl⟩ : syracuseStep 2621767 = 3932651) B3932651
theorem B2654951 : Blo 1032607 2654951 := bstep (se 1 (by rfl) ⟨1991213, by rfl⟩ : syracuseStep 2654951 = 3982427) B3982427
theorem B2098487 : Blo 1032607 2098487 := bstep (se 1 (by rfl) ⟨1573865, by rfl⟩ : syracuseStep 2098487 = 3147731) B3147731
theorem B1967753 : Blo 1032607 1967753 := bstep (se 2 (by rfl) ⟨737907, by rfl⟩ : syracuseStep 1967753 = 1475815) B1475815
theorem B2623823 : Blo 1032607 2623823 := bstep (se 1 (by rfl) ⟨1967867, by rfl⟩ : syracuseStep 2623823 = 3935735) B3935735
theorem B2329055 : Blo 1032607 2329055 := bstep (se 1 (by rfl) ⟨1746791, by rfl⟩ : syracuseStep 2329055 = 3493583) B3493583
theorem B64654159 : Blo 1032607 64654159 := bstep (se 1 (by rfl) ⟨48490619, by rfl⟩ : syracuseStep 64654159 = 96981239) B96981239
theorem B14913335 : Blo 1032607 14913335 := bstep (se 1 (by rfl) ⟨11185001, by rfl⟩ : syracuseStep 14913335 = 22370003) B22370003
theorem B21204965 : Blo 1032607 21204965 := bstep (se 4 (by rfl) ⟨1987965, by rfl⟩ : syracuseStep 21204965 = 3975931) B3975931
theorem B5247827 : Blo 1032607 5247827 := bstep (se 1 (by rfl) ⟨3935870, by rfl⟩ : syracuseStep 5247827 = 7871741) B7871741
theorem B2332007 : Blo 1032607 2332007 := bstep (se 1 (by rfl) ⟨1749005, by rfl⟩ : syracuseStep 2332007 = 3498011) B3498011
theorem B1742951 : Blo 1032607 1742951 := bstep (se 1 (by rfl) ⟨1307213, by rfl⟩ : syracuseStep 1742951 = 2614427) B2614427
theorem B64560233 : Blo 1032607 64560233 := bstep (se 2 (by rfl) ⟨24210087, by rfl⟩ : syracuseStep 64560233 = 48420175) B48420175
theorem B6300713 : Blo 1032607 6300713 := bstep (se 2 (by rfl) ⟨2362767, by rfl⟩ : syracuseStep 6300713 = 4725535) B4725535
theorem B1551983 : Blo 1032607 1551983 := bstep (se 1 (by rfl) ⟨1163987, by rfl⟩ : syracuseStep 1551983 = 2327975) B2327975
theorem B14889575 : Blo 1032607 14889575 := bstep (se 1 (by rfl) ⟨11167181, by rfl⟩ : syracuseStep 14889575 = 22334363) B22334363
theorem B1553855 : Blo 1032607 1553855 := bstep (se 1 (by rfl) ⟨1165391, by rfl⟩ : syracuseStep 1553855 = 2330783) B2330783
theorem B11777723 : Blo 1032607 11777723 := bstep (se 1 (by rfl) ⟨8833292, by rfl⟩ : syracuseStep 11777723 = 17666585) B17666585
theorem B50378435 : Blo 1032607 50378435 := bstep (se 1 (by rfl) ⟨37783826, by rfl⟩ : syracuseStep 50378435 = 75567653) B75567653
theorem B1162111 : Blo 1032607 1162111 := bstep (se 1 (by rfl) ⟨871583, by rfl⟩ : syracuseStep 1162111 = 1743167) B1743167
theorem B14139161 : Blo 1032607 14139161 := bstep (se 2 (by rfl) ⟨5302185, by rfl⟩ : syracuseStep 14139161 = 10604371) B10604371
theorem B11780639 : Blo 1032607 11780639 := bstep (se 1 (by rfl) ⟨8835479, by rfl⟩ : syracuseStep 11780639 = 17670959) B17670959
theorem B1164271 : Blo 1032607 1164271 := bstep (se 1 (by rfl) ⟨873203, by rfl⟩ : syracuseStep 1164271 = 1746407) B1746407
theorem B1035175 : Blo 1032607 1035175 := bstep (se 1 (by rfl) ⟨776381, by rfl⟩ : syracuseStep 1035175 = 1552763) B1552763
theorem B5230331 : Blo 1032607 5230331 := bstep (se 1 (by rfl) ⟨3922748, by rfl⟩ : syracuseStep 5230331 = 7845497) B7845497
theorem B1659703 : Blo 1032607 1659703 := bstep (se 1 (by rfl) ⟨1244777, by rfl⟩ : syracuseStep 1659703 = 2489555) B2489555
theorem B30661039 : Blo 1032607 30661039 := bstep (se 1 (by rfl) ⟨22995779, by rfl⟩ : syracuseStep 30661039 = 45991559) B45991559
theorem B2481511 : Blo 1032607 2481511 := bstep (se 1 (by rfl) ⟨1861133, by rfl⟩ : syracuseStep 2481511 = 3722267) B3722267
theorem B8838557 : Blo 1032607 8838557 := bstep (se 3 (by rfl) ⟨1657229, by rfl⟩ : syracuseStep 8838557 = 3314459) B3314459
theorem B3497579 : Blo 1032607 3497579 := bstep (se 1 (by rfl) ⟨2623184, by rfl⟩ : syracuseStep 3497579 = 5246369) B5246369
theorem B1106255 : Blo 1032607 1106255 := bstep (se 1 (by rfl) ⟨829691, by rfl⟩ : syracuseStep 1106255 = 1659383) B1659383
theorem B8382527 : Blo 1032607 8382527 := bstep (se 1 (by rfl) ⟨6286895, by rfl⟩ : syracuseStep 8382527 = 12573791) B12573791
theorem B16771535 : Blo 1032607 16771535 := bstep (se 1 (by rfl) ⟨12578651, by rfl⟩ : syracuseStep 16771535 = 25157303) B25157303
theorem B11202785 : Blo 1032607 11202785 := bstep (se 2 (by rfl) ⟨4201044, by rfl⟩ : syracuseStep 11202785 = 8402089) B8402089
theorem B2355817 : Blo 1032607 2355817 := bstep (se 2 (by rfl) ⟨883431, by rfl⟩ : syracuseStep 2355817 = 1766863) B1766863
theorem B2323691 : Blo 1032607 2323691 := bstep (se 1 (by rfl) ⟨1742768, by rfl⟩ : syracuseStep 2323691 = 3485537) B3485537
theorem B1701791 : Blo 1032607 1701791 := bstep (se 1 (by rfl) ⟨1276343, by rfl⟩ : syracuseStep 1701791 = 2552687) B2552687
theorem B13269419 : Blo 1032607 13269419 := bstep (se 1 (by rfl) ⟨9952064, by rfl⟩ : syracuseStep 13269419 = 19904129) B19904129
theorem B2325275 : Blo 1032607 2325275 := bstep (se 1 (by rfl) ⟨1743956, by rfl⟩ : syracuseStep 2325275 = 3487913) B3487913
theorem B2325311 : Blo 1032607 2325311 := bstep (se 1 (by rfl) ⟨1743983, by rfl⟩ : syracuseStep 2325311 = 3487967) B3487967
theorem B4717565 : Blo 1032607 4717565 := bstep (se 3 (by rfl) ⟨884543, by rfl⟩ : syracuseStep 4717565 = 1769087) B1769087
theorem B2325887 : Blo 1032607 2325887 := bstep (se 1 (by rfl) ⟨1744415, by rfl⟩ : syracuseStep 2325887 = 3488831) B3488831
theorem B2950013 : Blo 1032607 2950013 := bstep (se 3 (by rfl) ⟨553127, by rfl⟩ : syracuseStep 2950013 = 1106255) B1106255
theorem B7079869 : Blo 1032607 7079869 := bstep (se 3 (by rfl) ⟨1327475, by rfl⟩ : syracuseStep 7079869 = 2654951) B2654951
theorem B5247341 : Blo 1032607 5247341 := bstep (se 3 (by rfl) ⟨983876, by rfl⟩ : syracuseStep 5247341 = 1967753) B1967753
theorem B2331719 : Blo 1032607 2331719 := bstep (se 1 (by rfl) ⟨1748789, by rfl⟩ : syracuseStep 2331719 = 3497579) B3497579
theorem B11181023 : Blo 1032607 11181023 := bstep (se 1 (by rfl) ⟨8385767, by rfl⟩ : syracuseStep 11181023 = 16771535) B16771535
theorem B1549127 : Blo 1032607 1549127 := bstep (se 1 (by rfl) ⟨1161845, by rfl⟩ : syracuseStep 1549127 = 2323691) B2323691
theorem B1549481 : Blo 1032607 1549481 := bstep (se 2 (by rfl) ⟨581055, by rfl⟩ : syracuseStep 1549481 = 1162111) B1162111
theorem B1550183 : Blo 1032607 1550183 := bstep (se 1 (by rfl) ⟨1162637, by rfl⟩ : syracuseStep 1550183 = 2325275) B2325275
theorem B1550207 : Blo 1032607 1550207 := bstep (se 1 (by rfl) ⟨1162655, by rfl⟩ : syracuseStep 1550207 = 2325311) B2325311
theorem B1550591 : Blo 1032607 1550591 := bstep (se 1 (by rfl) ⟨1162943, by rfl⟩ : syracuseStep 1550591 = 2325887) B2325887
theorem B1552361 : Blo 1032607 1552361 := bstep (se 2 (by rfl) ⟨582135, by rfl⟩ : syracuseStep 1552361 = 1164271) B1164271
theorem B1749215 : Blo 1032607 1749215 := bstep (se 1 (by rfl) ⟨1311911, by rfl⟩ : syracuseStep 1749215 = 2623823) B2623823
theorem B1552703 : Blo 1032607 1552703 := bstep (se 1 (by rfl) ⟨1164527, by rfl⟩ : syracuseStep 1552703 = 2329055) B2329055
theorem B3486887 : Blo 1032607 3486887 := bstep (se 1 (by rfl) ⟨2615165, by rfl⟩ : syracuseStep 3486887 = 5230331) B5230331
theorem B9942223 : Blo 1032607 9942223 := bstep (se 1 (by rfl) ⟨7456667, by rfl⟩ : syracuseStep 9942223 = 14913335) B14913335
theorem B14136643 : Blo 1032607 14136643 := bstep (se 1 (by rfl) ⟨10602482, by rfl⟩ : syracuseStep 14136643 = 21204965) B21204965
theorem B1554671 : Blo 1032607 1554671 := bstep (se 1 (by rfl) ⟨1166003, by rfl⟩ : syracuseStep 1554671 = 2332007) B2332007
theorem B1161967 : Blo 1032607 1161967 := bstep (se 1 (by rfl) ⟨871475, by rfl⟩ : syracuseStep 1161967 = 1742951) B1742951
theorem B43040155 : Blo 1032607 43040155 := bstep (se 1 (by rfl) ⟨32280116, by rfl⟩ : syracuseStep 43040155 = 64560233) B64560233
theorem B2212937 : Blo 1032607 2212937 := bstep (se 2 (by rfl) ⟨829851, by rfl⟩ : syracuseStep 2212937 = 1659703) B1659703
theorem B5588351 : Blo 1032607 5588351 := bstep (se 1 (by rfl) ⟨4191263, by rfl⟩ : syracuseStep 5588351 = 8382527) B8382527
theorem B1034655 : Blo 1032607 1034655 := bstep (se 1 (by rfl) ⟨775991, by rfl⟩ : syracuseStep 1034655 = 1551983) B1551983
theorem B40881385 : Blo 1032607 40881385 := bstep (se 2 (by rfl) ⟨15330519, by rfl⟩ : syracuseStep 40881385 = 30661039) B30661039
theorem B1035903 : Blo 1032607 1035903 := bstep (se 1 (by rfl) ⟨776927, by rfl⟩ : syracuseStep 1035903 = 1553855) B1553855
theorem B7851815 : Blo 1032607 7851815 := bstep (se 1 (by rfl) ⟨5888861, by rfl⟩ : syracuseStep 7851815 = 11777723) B11777723
theorem B9426107 : Blo 1032607 9426107 := bstep (se 1 (by rfl) ⟨7069580, by rfl⟩ : syracuseStep 9426107 = 14139161) B14139161
theorem B7853759 : Blo 1032607 7853759 := bstep (se 1 (by rfl) ⟨5890319, by rfl⟩ : syracuseStep 7853759 = 11780639) B11780639
theorem B3495689 : Blo 1032607 3495689 := bstep (se 2 (by rfl) ⟨1310883, by rfl⟩ : syracuseStep 3495689 = 2621767) B2621767
theorem B16801901 : Blo 1032607 16801901 := bstep (se 3 (by rfl) ⟨3150356, by rfl⟩ : syracuseStep 16801901 = 6300713) B6300713
theorem B3498551 : Blo 1032607 3498551 := bstep (se 1 (by rfl) ⟨2623913, by rfl⟩ : syracuseStep 3498551 = 5247827) B5247827
theorem B5595965 : Blo 1032607 5595965 := bstep (se 3 (by rfl) ⟨1049243, by rfl⟩ : syracuseStep 5595965 = 2098487) B2098487
theorem B86205545 : Blo 1032607 86205545 := bstep (se 2 (by rfl) ⟨32327079, by rfl⟩ : syracuseStep 86205545 = 64654159) B64654159
theorem B5892371 : Blo 1032607 5892371 := bstep (se 1 (by rfl) ⟨4419278, by rfl⟩ : syracuseStep 5892371 = 8838557) B8838557
theorem B3141089 : Blo 1032607 3141089 := bstep (se 2 (by rfl) ⟨1177908, by rfl⟩ : syracuseStep 3141089 = 2355817) B2355817
theorem B7468523 : Blo 1032607 7468523 := bstep (se 1 (by rfl) ⟨5601392, by rfl⟩ : syracuseStep 7468523 = 11202785) B11202785
theorem B9926383 : Blo 1032607 9926383 := bstep (se 1 (by rfl) ⟨7444787, by rfl⟩ : syracuseStep 9926383 = 14889575) B14889575
theorem B33585623 : Blo 1032607 33585623 := bstep (se 1 (by rfl) ⟨25189217, by rfl⟩ : syracuseStep 33585623 = 50378435) B50378435
theorem B8846279 : Blo 1032607 8846279 := bstep (se 1 (by rfl) ⟨6634709, by rfl⟩ : syracuseStep 8846279 = 13269419) B13269419
theorem B18152437 : Blo 1032607 18152437 := bstep (se 5 (by rfl) ⟨850895, by rfl⟩ : syracuseStep 18152437 = 1701791) B1701791
theorem B3308681 : Blo 1032607 3308681 := bstep (se 2 (by rfl) ⟨1240755, by rfl⟩ : syracuseStep 3308681 = 2481511) B2481511
theorem B3145043 : Blo 1032607 3145043 := bstep (se 1 (by rfl) ⟨2358782, by rfl⟩ : syracuseStep 3145043 = 4717565) B4717565
theorem B1966675 : Blo 1032607 1966675 := bstep (se 1 (by rfl) ⟨1475006, by rfl⟩ : syracuseStep 1966675 = 2950013) B2950013
theorem B1475291 : Blo 1032607 1475291 := bstep (se 1 (by rfl) ⟨1106468, by rfl⟩ : syracuseStep 1475291 = 2212937) B2212937
theorem B9439825 : Blo 1032607 9439825 := bstep (se 2 (by rfl) ⟨3539934, by rfl⟩ : syracuseStep 9439825 = 7079869) B7079869
theorem B2330459 : Blo 1032607 2330459 := bstep (se 1 (by rfl) ⟨1747844, by rfl⟩ : syracuseStep 2330459 = 3495689) B3495689
theorem B2332367 : Blo 1032607 2332367 := bstep (se 1 (by rfl) ⟨1749275, by rfl⟩ : syracuseStep 2332367 = 3498551) B3498551
theorem B18848857 : Blo 1032607 18848857 := bstep (se 2 (by rfl) ⟨7068321, by rfl⟩ : syracuseStep 18848857 = 14136643) B14136643
theorem B1549289 : Blo 1032607 1549289 := bstep (se 2 (by rfl) ⟨580983, by rfl⟩ : syracuseStep 1549289 = 1161967) B1161967
theorem B22390415 : Blo 1032607 22390415 := bstep (se 1 (by rfl) ⟨16792811, by rfl⟩ : syracuseStep 22390415 = 33585623) B33585623
theorem B57386873 : Blo 1032607 57386873 := bstep (se 2 (by rfl) ⟨21520077, by rfl⟩ : syracuseStep 57386873 = 43040155) B43040155
theorem B2205787 : Blo 1032607 2205787 := bstep (se 1 (by rfl) ⟨1654340, by rfl⟩ : syracuseStep 2205787 = 3308681) B3308681
theorem B1554479 : Blo 1032607 1554479 := bstep (se 1 (by rfl) ⟨1165859, by rfl⟩ : syracuseStep 1554479 = 2331719) B2331719
theorem B54508513 : Blo 1032607 54508513 := bstep (se 2 (by rfl) ⟨20440692, by rfl⟩ : syracuseStep 54508513 = 40881385) B40881385
theorem B7454015 : Blo 1032607 7454015 := bstep (se 1 (by rfl) ⟨5590511, by rfl⟩ : syracuseStep 7454015 = 11181023) B11181023
theorem B1032751 : Blo 1032607 1032751 := bstep (se 1 (by rfl) ⟨774563, by rfl⟩ : syracuseStep 1032751 = 1549127) B1549127
theorem B1032987 : Blo 1032607 1032987 := bstep (se 1 (by rfl) ⟨774740, by rfl⟩ : syracuseStep 1032987 = 1549481) B1549481
theorem B1033455 : Blo 1032607 1033455 := bstep (se 1 (by rfl) ⟨775091, by rfl⟩ : syracuseStep 1033455 = 1550183) B1550183
theorem B1033471 : Blo 1032607 1033471 := bstep (se 1 (by rfl) ⟨775103, by rfl⟩ : syracuseStep 1033471 = 1550207) B1550207
theorem B1033727 : Blo 1032607 1033727 := bstep (se 1 (by rfl) ⟨775295, by rfl⟩ : syracuseStep 1033727 = 1550591) B1550591
theorem B13256297 : Blo 1032607 13256297 := bstep (se 2 (by rfl) ⟨4971111, by rfl⟩ : syracuseStep 13256297 = 9942223) B9942223
theorem B1034907 : Blo 1032607 1034907 := bstep (se 1 (by rfl) ⟨776180, by rfl⟩ : syracuseStep 1034907 = 1552361) B1552361
theorem B1166143 : Blo 1032607 1166143 := bstep (se 1 (by rfl) ⟨874607, by rfl⟩ : syracuseStep 1166143 = 1749215) B1749215
theorem B1035135 : Blo 1032607 1035135 := bstep (se 1 (by rfl) ⟨776351, by rfl⟩ : syracuseStep 1035135 = 1552703) B1552703
theorem B24203249 : Blo 1032607 24203249 := bstep (se 2 (by rfl) ⟨9076218, by rfl⟩ : syracuseStep 24203249 = 18152437) B18152437
theorem B1036447 : Blo 1032607 1036447 := bstep (se 1 (by rfl) ⟨777335, by rfl⟩ : syracuseStep 1036447 = 1554671) B1554671
theorem B3725567 : Blo 1032607 3725567 := bstep (se 1 (by rfl) ⟨2794175, by rfl⟩ : syracuseStep 3725567 = 5588351) B5588351
theorem B5234543 : Blo 1032607 5234543 := bstep (se 1 (by rfl) ⟨3925907, by rfl⟩ : syracuseStep 5234543 = 7851815) B7851815
theorem B3498227 : Blo 1032607 3498227 := bstep (se 1 (by rfl) ⟨2623670, by rfl⟩ : syracuseStep 3498227 = 5247341) B5247341
theorem B6284071 : Blo 1032607 6284071 := bstep (se 1 (by rfl) ⟨4713053, by rfl⟩ : syracuseStep 6284071 = 9426107) B9426107
theorem B5235839 : Blo 1032607 5235839 := bstep (se 1 (by rfl) ⟨3926879, by rfl⟩ : syracuseStep 5235839 = 7853759) B7853759
theorem B11201267 : Blo 1032607 11201267 := bstep (se 1 (by rfl) ⟨8400950, by rfl⟩ : syracuseStep 11201267 = 16801901) B16801901
theorem B3730643 : Blo 1032607 3730643 := bstep (se 1 (by rfl) ⟨2797982, by rfl⟩ : syracuseStep 3730643 = 5595965) B5595965
theorem B57470363 : Blo 1032607 57470363 := bstep (se 1 (by rfl) ⟨43102772, by rfl⟩ : syracuseStep 57470363 = 86205545) B86205545
theorem B3928247 : Blo 1032607 3928247 := bstep (se 1 (by rfl) ⟨2946185, by rfl⟩ : syracuseStep 3928247 = 5892371) B5892371
theorem B13235177 : Blo 1032607 13235177 := bstep (se 2 (by rfl) ⟨4963191, by rfl⟩ : syracuseStep 13235177 = 9926383) B9926383
theorem B2094059 : Blo 1032607 2094059 := bstep (se 1 (by rfl) ⟨1570544, by rfl⟩ : syracuseStep 2094059 = 3141089) B3141089
theorem B2324591 : Blo 1032607 2324591 := bstep (se 1 (by rfl) ⟨1743443, by rfl⟩ : syracuseStep 2324591 = 3486887) B3486887
theorem B4979015 : Blo 1032607 4979015 := bstep (se 1 (by rfl) ⟨3734261, by rfl⟩ : syracuseStep 4979015 = 7468523) B7468523
theorem B5897519 : Blo 1032607 5897519 := bstep (se 1 (by rfl) ⟨4423139, by rfl⟩ : syracuseStep 5897519 = 8846279) B8846279
theorem B2096695 : Blo 1032607 2096695 := bstep (se 1 (by rfl) ⟨1572521, by rfl⟩ : syracuseStep 2096695 = 3145043) B3145043
theorem B2622233 : Blo 1032607 2622233 := bstep (se 2 (by rfl) ⟨983337, by rfl⟩ : syracuseStep 2622233 = 1966675) B1966675
theorem B3934109 : Blo 1032607 3934109 := bstep (se 3 (by rfl) ⟨737645, by rfl⟩ : syracuseStep 3934109 = 1475291) B1475291
theorem B12586433 : Blo 1032607 12586433 := bstep (se 2 (by rfl) ⟨4719912, by rfl⟩ : syracuseStep 12586433 = 9439825) B9439825
theorem B2332151 : Blo 1032607 2332151 := bstep (se 1 (by rfl) ⟨1749113, by rfl⟩ : syracuseStep 2332151 = 3498227) B3498227
theorem B38313575 : Blo 1032607 38313575 := bstep (se 1 (by rfl) ⟨28735181, by rfl⟩ : syracuseStep 38313575 = 57470363) B57470363
theorem B11182373 : Blo 1032607 11182373 := bstep (se 4 (by rfl) ⟨1048347, by rfl⟩ : syracuseStep 11182373 = 2096695) B2096695
theorem B8823451 : Blo 1032607 8823451 := bstep (se 1 (by rfl) ⟨6617588, by rfl⟩ : syracuseStep 8823451 = 13235177) B13235177
theorem B1549727 : Blo 1032607 1549727 := bstep (se 1 (by rfl) ⟨1162295, by rfl⟩ : syracuseStep 1549727 = 2324591) B2324591
theorem B3319343 : Blo 1032607 3319343 := bstep (se 1 (by rfl) ⟨2489507, by rfl⟩ : syracuseStep 3319343 = 4979015) B4979015
theorem B1553639 : Blo 1032607 1553639 := bstep (se 1 (by rfl) ⟨1165229, by rfl⟩ : syracuseStep 1553639 = 2330459) B2330459
theorem B16135499 : Blo 1032607 16135499 := bstep (se 1 (by rfl) ⟨12101624, by rfl⟩ : syracuseStep 16135499 = 24203249) B24203249
theorem B1554857 : Blo 1032607 1554857 := bstep (se 2 (by rfl) ⟨583071, by rfl⟩ : syracuseStep 1554857 = 1166143) B1166143
theorem B1554911 : Blo 1032607 1554911 := bstep (se 1 (by rfl) ⟨1166183, by rfl⟩ : syracuseStep 1554911 = 2332367) B2332367
theorem B3489695 : Blo 1032607 3489695 := bstep (se 1 (by rfl) ⟨2617271, by rfl⟩ : syracuseStep 3489695 = 5234543) B5234543
theorem B1032859 : Blo 1032607 1032859 := bstep (se 1 (by rfl) ⟨774644, by rfl⟩ : syracuseStep 1032859 = 1549289) B1549289
theorem B3490559 : Blo 1032607 3490559 := bstep (se 1 (by rfl) ⟨2617919, by rfl⟩ : syracuseStep 3490559 = 5235839) B5235839
theorem B14926943 : Blo 1032607 14926943 := bstep (se 1 (by rfl) ⟨11195207, by rfl⟩ : syracuseStep 14926943 = 22390415) B22390415
theorem B38257915 : Blo 1032607 38257915 := bstep (se 1 (by rfl) ⟨28693436, by rfl⟩ : syracuseStep 38257915 = 57386873) B57386873
theorem B1396039 : Blo 1032607 1396039 := bstep (se 1 (by rfl) ⟨1047029, by rfl⟩ : syracuseStep 1396039 = 2094059) B2094059
theorem B1036319 : Blo 1032607 1036319 := bstep (se 1 (by rfl) ⟨777239, by rfl⟩ : syracuseStep 1036319 = 1554479) B1554479
theorem B4969343 : Blo 1032607 4969343 := bstep (se 1 (by rfl) ⟨3727007, by rfl⟩ : syracuseStep 4969343 = 7454015) B7454015
theorem B8837531 : Blo 1032607 8837531 := bstep (se 1 (by rfl) ⟨6628148, by rfl⟩ : syracuseStep 8837531 = 13256297) B13256297
theorem B2941049 : Blo 1032607 2941049 := bstep (se 2 (by rfl) ⟨1102893, by rfl⟩ : syracuseStep 2941049 = 2205787) B2205787
theorem B2483711 : Blo 1032607 2483711 := bstep (se 1 (by rfl) ⟨1862783, by rfl⟩ : syracuseStep 2483711 = 3725567) B3725567
theorem B33515045 : Blo 1032607 33515045 := bstep (se 4 (by rfl) ⟨3142035, by rfl⟩ : syracuseStep 33515045 = 6284071) B6284071
theorem B7467511 : Blo 1032607 7467511 := bstep (se 1 (by rfl) ⟨5600633, by rfl⟩ : syracuseStep 7467511 = 11201267) B11201267
theorem B2487095 : Blo 1032607 2487095 := bstep (se 1 (by rfl) ⟨1865321, by rfl⟩ : syracuseStep 2487095 = 3730643) B3730643
theorem B2618831 : Blo 1032607 2618831 := bstep (se 1 (by rfl) ⟨1964123, by rfl⟩ : syracuseStep 2618831 = 3928247) B3928247
theorem B72678017 : Blo 1032607 72678017 := bstep (se 2 (by rfl) ⟨27254256, by rfl⟩ : syracuseStep 72678017 = 54508513) B54508513
theorem B25131809 : Blo 1032607 25131809 := bstep (se 2 (by rfl) ⟨9424428, by rfl⟩ : syracuseStep 25131809 = 18848857) B18848857
theorem B3931679 : Blo 1032607 3931679 := bstep (se 1 (by rfl) ⟨2948759, by rfl⟩ : syracuseStep 3931679 = 5897519) B5897519
theorem B2327039 : Blo 1032607 2327039 := bstep (se 1 (by rfl) ⟨1745279, by rfl⟩ : syracuseStep 2327039 = 3490559) B3490559
theorem B11764601 : Blo 1032607 11764601 := bstep (se 2 (by rfl) ⟨4411725, by rfl⟩ : syracuseStep 11764601 = 8823451) B8823451
theorem B2622739 : Blo 1032607 2622739 := bstep (se 1 (by rfl) ⟨1967054, by rfl⟩ : syracuseStep 2622739 = 3934109) B3934109
theorem B3312895 : Blo 1032607 3312895 := bstep (se 1 (by rfl) ⟨2484671, by rfl⟩ : syracuseStep 3312895 = 4969343) B4969343
theorem B10756999 : Blo 1032607 10756999 := bstep (se 1 (by rfl) ⟨8067749, by rfl⟩ : syracuseStep 10756999 = 16135499) B16135499
theorem B1745887 : Blo 1032607 1745887 := bstep (se 1 (by rfl) ⟨1309415, by rfl⟩ : syracuseStep 1745887 = 2618831) B2618831
theorem B33563821 : Blo 1032607 33563821 := bstep (se 3 (by rfl) ⟨6293216, by rfl⟩ : syracuseStep 33563821 = 12586433) B12586433
theorem B16754539 : Blo 1032607 16754539 := bstep (se 1 (by rfl) ⟨12565904, by rfl⟩ : syracuseStep 16754539 = 25131809) B25131809
theorem B1748155 : Blo 1032607 1748155 := bstep (se 1 (by rfl) ⟨1311116, by rfl⟩ : syracuseStep 1748155 = 2622233) B2622233
theorem B1554767 : Blo 1032607 1554767 := bstep (se 1 (by rfl) ⟨1166075, by rfl⟩ : syracuseStep 1554767 = 2332151) B2332151
theorem B25542383 : Blo 1032607 25542383 := bstep (se 1 (by rfl) ⟨19156787, by rfl⟩ : syracuseStep 25542383 = 38313575) B38313575
theorem B7454915 : Blo 1032607 7454915 := bstep (se 1 (by rfl) ⟨5591186, by rfl⟩ : syracuseStep 7454915 = 11182373) B11182373
theorem B1033151 : Blo 1032607 1033151 := bstep (se 1 (by rfl) ⟨774863, by rfl⟩ : syracuseStep 1033151 = 1549727) B1549727
theorem B1655807 : Blo 1032607 1655807 := bstep (se 1 (by rfl) ⟨1241855, by rfl⟩ : syracuseStep 1655807 = 2483711) B2483711
theorem B2212895 : Blo 1032607 2212895 := bstep (se 1 (by rfl) ⟨1659671, by rfl⟩ : syracuseStep 2212895 = 3319343) B3319343
theorem B193808045 : Blo 1032607 193808045 := bstep (se 3 (by rfl) ⟨36339008, by rfl⟩ : syracuseStep 193808045 = 72678017) B72678017
theorem B1658063 : Blo 1032607 1658063 := bstep (se 1 (by rfl) ⟨1243547, by rfl⟩ : syracuseStep 1658063 = 2487095) B2487095
theorem B1035759 : Blo 1032607 1035759 := bstep (se 1 (by rfl) ⟨776819, by rfl⟩ : syracuseStep 1035759 = 1553639) B1553639
theorem B1036571 : Blo 1032607 1036571 := bstep (se 1 (by rfl) ⟨777428, by rfl⟩ : syracuseStep 1036571 = 1554857) B1554857
theorem B1036607 : Blo 1032607 1036607 := bstep (se 1 (by rfl) ⟨777455, by rfl⟩ : syracuseStep 1036607 = 1554911) B1554911
theorem B9951295 : Blo 1032607 9951295 := bstep (se 1 (by rfl) ⟨7463471, by rfl⟩ : syracuseStep 9951295 = 14926943) B14926943
theorem B51010553 : Blo 1032607 51010553 := bstep (se 2 (by rfl) ⟨19128957, by rfl⟩ : syracuseStep 51010553 = 38257915) B38257915
theorem B5891687 : Blo 1032607 5891687 := bstep (se 1 (by rfl) ⟨4418765, by rfl⟩ : syracuseStep 5891687 = 8837531) B8837531
theorem B1861385 : Blo 1032607 1861385 := bstep (se 2 (by rfl) ⟨698019, by rfl⟩ : syracuseStep 1861385 = 1396039) B1396039
theorem B1960699 : Blo 1032607 1960699 := bstep (se 1 (by rfl) ⟨1470524, by rfl⟩ : syracuseStep 1960699 = 2941049) B2941049
theorem B9956681 : Blo 1032607 9956681 := bstep (se 2 (by rfl) ⟨3733755, by rfl⟩ : syracuseStep 9956681 = 7467511) B7467511
theorem B22343363 : Blo 1032607 22343363 := bstep (se 1 (by rfl) ⟨16757522, by rfl⟩ : syracuseStep 22343363 = 33515045) B33515045
theorem B2621119 : Blo 1032607 2621119 := bstep (se 1 (by rfl) ⟨1965839, by rfl⟩ : syracuseStep 2621119 = 3931679) B3931679
theorem B2326463 : Blo 1032607 2326463 := bstep (se 1 (by rfl) ⟨1744847, by rfl⟩ : syracuseStep 2326463 = 3489695) B3489695
theorem B1475263 : Blo 1032607 1475263 := bstep (se 1 (by rfl) ⟨1106447, by rfl⟩ : syracuseStep 1475263 = 2212895) B2212895
theorem B129205363 : Blo 1032607 129205363 := bstep (se 1 (by rfl) ⟨96904022, by rfl⟩ : syracuseStep 129205363 = 193808045) B193808045
theorem B2327849 : Blo 1032607 2327849 := bstep (se 2 (by rfl) ⟨872943, by rfl⟩ : syracuseStep 2327849 = 1745887) B1745887
theorem B2330873 : Blo 1032607 2330873 := bstep (se 2 (by rfl) ⟨874077, by rfl⟩ : syracuseStep 2330873 = 1748155) B1748155
theorem B1550975 : Blo 1032607 1550975 := bstep (se 1 (by rfl) ⟨1163231, by rfl⟩ : syracuseStep 1550975 = 2326463) B2326463
theorem B1551359 : Blo 1032607 1551359 := bstep (se 1 (by rfl) ⟨1163519, by rfl⟩ : syracuseStep 1551359 = 2327039) B2327039
theorem B7843067 : Blo 1032607 7843067 := bstep (se 1 (by rfl) ⟨5882300, by rfl⟩ : syracuseStep 7843067 = 11764601) B11764601
theorem B4963693 : Blo 1032607 4963693 := bstep (se 3 (by rfl) ⟨930692, by rfl⟩ : syracuseStep 4963693 = 1861385) B1861385
theorem B6637787 : Blo 1032607 6637787 := bstep (se 1 (by rfl) ⟨4978340, by rfl⟩ : syracuseStep 6637787 = 9956681) B9956681
theorem B14895575 : Blo 1032607 14895575 := bstep (se 1 (by rfl) ⟨11171681, by rfl⟩ : syracuseStep 14895575 = 22343363) B22343363
theorem B1036511 : Blo 1032607 1036511 := bstep (se 1 (by rfl) ⟨777383, by rfl⟩ : syracuseStep 1036511 = 1554767) B1554767
theorem B68113021 : Blo 1032607 68113021 := bstep (se 3 (by rfl) ⟨12771191, by rfl⟩ : syracuseStep 68113021 = 25542383) B25542383
theorem B3494825 : Blo 1032607 3494825 := bstep (se 2 (by rfl) ⟨1310559, by rfl⟩ : syracuseStep 3494825 = 2621119) B2621119
theorem B4969943 : Blo 1032607 4969943 := bstep (se 1 (by rfl) ⟨3727457, by rfl⟩ : syracuseStep 4969943 = 7454915) B7454915
theorem B14342665 : Blo 1032607 14342665 := bstep (se 2 (by rfl) ⟨5378499, by rfl⟩ : syracuseStep 14342665 = 10756999) B10756999
theorem B44751761 : Blo 1032607 44751761 := bstep (se 2 (by rfl) ⟨16781910, by rfl⟩ : syracuseStep 44751761 = 33563821) B33563821
theorem B3496985 : Blo 1032607 3496985 := bstep (se 2 (by rfl) ⟨1311369, by rfl⟩ : syracuseStep 3496985 = 2622739) B2622739
theorem B1105375 : Blo 1032607 1105375 := bstep (se 1 (by rfl) ⟨829031, by rfl⟩ : syracuseStep 1105375 = 1658063) B1658063
theorem B22339385 : Blo 1032607 22339385 := bstep (se 2 (by rfl) ⟨8377269, by rfl⟩ : syracuseStep 22339385 = 16754539) B16754539
theorem B4415485 : Blo 1032607 4415485 := bstep (se 3 (by rfl) ⟨827903, by rfl⟩ : syracuseStep 4415485 = 1655807) B1655807
theorem B2614265 : Blo 1032607 2614265 := bstep (se 2 (by rfl) ⟨980349, by rfl⟩ : syracuseStep 2614265 = 1960699) B1960699
theorem B4417193 : Blo 1032607 4417193 := bstep (se 2 (by rfl) ⟨1656447, by rfl⟩ : syracuseStep 4417193 = 3312895) B3312895
theorem B34007035 : Blo 1032607 34007035 := bstep (se 1 (by rfl) ⟨25505276, by rfl⟩ : syracuseStep 34007035 = 51010553) B51010553
theorem B3927791 : Blo 1032607 3927791 := bstep (se 1 (by rfl) ⟨2945843, by rfl⟩ : syracuseStep 3927791 = 5891687) B5891687
theorem B13268393 : Blo 1032607 13268393 := bstep (se 2 (by rfl) ⟨4975647, by rfl⟩ : syracuseStep 13268393 = 9951295) B9951295
theorem B1967017 : Blo 1032607 1967017 := bstep (se 2 (by rfl) ⟨737631, by rfl⟩ : syracuseStep 1967017 = 1475263) B1475263
theorem B4425191 : Blo 1032607 4425191 := bstep (se 1 (by rfl) ⟨3318893, by rfl⟩ : syracuseStep 4425191 = 6637787) B6637787
theorem B9930383 : Blo 1032607 9930383 := bstep (se 1 (by rfl) ⟨7447787, by rfl⟩ : syracuseStep 9930383 = 14895575) B14895575
theorem B2329883 : Blo 1032607 2329883 := bstep (se 1 (by rfl) ⟨1747412, by rfl⟩ : syracuseStep 2329883 = 3494825) B3494825
theorem B3313295 : Blo 1032607 3313295 := bstep (se 1 (by rfl) ⟨2484971, by rfl⟩ : syracuseStep 3313295 = 4969943) B4969943
theorem B2331323 : Blo 1032607 2331323 := bstep (se 1 (by rfl) ⟨1748492, by rfl⟩ : syracuseStep 2331323 = 3496985) B3496985
theorem B1742843 : Blo 1032607 1742843 := bstep (se 1 (by rfl) ⟨1307132, by rfl⟩ : syracuseStep 1742843 = 2614265) B2614265
theorem B1551899 : Blo 1032607 1551899 := bstep (se 1 (by rfl) ⟨1163924, by rfl⟩ : syracuseStep 1551899 = 2327849) B2327849
theorem B172273817 : Blo 1032607 172273817 := bstep (se 2 (by rfl) ⟨64602681, by rfl⟩ : syracuseStep 172273817 = 129205363) B129205363
theorem B1553915 : Blo 1032607 1553915 := bstep (se 1 (by rfl) ⟨1165436, by rfl⟩ : syracuseStep 1553915 = 2330873) B2330873
theorem B11779181 : Blo 1032607 11779181 := bstep (se 3 (by rfl) ⟨2208596, by rfl⟩ : syracuseStep 11779181 = 4417193) B4417193
theorem B29834507 : Blo 1032607 29834507 := bstep (se 1 (by rfl) ⟨22375880, by rfl⟩ : syracuseStep 29834507 = 44751761) B44751761
theorem B14892923 : Blo 1032607 14892923 := bstep (se 1 (by rfl) ⟨11169692, by rfl⟩ : syracuseStep 14892923 = 22339385) B22339385
theorem B90817361 : Blo 1032607 90817361 := bstep (se 2 (by rfl) ⟨34056510, by rfl⟩ : syracuseStep 90817361 = 68113021) B68113021
theorem B1033983 : Blo 1032607 1033983 := bstep (se 1 (by rfl) ⟨775487, by rfl⟩ : syracuseStep 1033983 = 1550975) B1550975
theorem B1034239 : Blo 1032607 1034239 := bstep (se 1 (by rfl) ⟨775679, by rfl⟩ : syracuseStep 1034239 = 1551359) B1551359
theorem B5228711 : Blo 1032607 5228711 := bstep (se 1 (by rfl) ⟨3921533, by rfl⟩ : syracuseStep 5228711 = 7843067) B7843067
theorem B19123553 : Blo 1032607 19123553 := bstep (se 2 (by rfl) ⟨7171332, by rfl⟩ : syracuseStep 19123553 = 14342665) B14342665
theorem B5887313 : Blo 1032607 5887313 := bstep (se 2 (by rfl) ⟨2207742, by rfl⟩ : syracuseStep 5887313 = 4415485) B4415485
theorem B45342713 : Blo 1032607 45342713 := bstep (se 2 (by rfl) ⟨17003517, by rfl⟩ : syracuseStep 45342713 = 34007035) B34007035
theorem B2618527 : Blo 1032607 2618527 := bstep (se 1 (by rfl) ⟨1963895, by rfl⟩ : syracuseStep 2618527 = 3927791) B3927791
theorem B8845595 : Blo 1032607 8845595 := bstep (se 1 (by rfl) ⟨6634196, by rfl⟩ : syracuseStep 8845595 = 13268393) B13268393
theorem B6618257 : Blo 1032607 6618257 := bstep (se 2 (by rfl) ⟨2481846, by rfl⟩ : syracuseStep 6618257 = 4963693) B4963693
theorem B1473833 : Blo 1032607 1473833 := bstep (se 2 (by rfl) ⟨552687, by rfl⟩ : syracuseStep 1473833 = 1105375) B1105375
theorem B2950127 : Blo 1032607 2950127 := bstep (se 1 (by rfl) ⟨2212595, by rfl⟩ : syracuseStep 2950127 = 4425191) B4425191
theorem B6620255 : Blo 1032607 6620255 := bstep (se 1 (by rfl) ⟨4965191, by rfl⟩ : syracuseStep 6620255 = 9930383) B9930383
theorem B2622689 : Blo 1032607 2622689 := bstep (se 2 (by rfl) ⟨983508, by rfl⟩ : syracuseStep 2622689 = 1967017) B1967017
theorem B12749035 : Blo 1032607 12749035 := bstep (se 1 (by rfl) ⟨9561776, by rfl⟩ : syracuseStep 12749035 = 19123553) B19123553
theorem B3485807 : Blo 1032607 3485807 := bstep (se 1 (by rfl) ⟨2614355, by rfl⟩ : syracuseStep 3485807 = 5228711) B5228711
theorem B1553255 : Blo 1032607 1553255 := bstep (se 1 (by rfl) ⟨1164941, by rfl⟩ : syracuseStep 1553255 = 2329883) B2329883
theorem B2208863 : Blo 1032607 2208863 := bstep (se 1 (by rfl) ⟨1656647, by rfl⟩ : syracuseStep 2208863 = 3313295) B3313295
theorem B1554215 : Blo 1032607 1554215 := bstep (se 1 (by rfl) ⟨1165661, by rfl⟩ : syracuseStep 1554215 = 2331323) B2331323
theorem B1161895 : Blo 1032607 1161895 := bstep (se 1 (by rfl) ⟨871421, by rfl⟩ : syracuseStep 1161895 = 1742843) B1742843
theorem B30228475 : Blo 1032607 30228475 := bstep (se 1 (by rfl) ⟨22671356, by rfl⟩ : syracuseStep 30228475 = 45342713) B45342713
theorem B3491369 : Blo 1032607 3491369 := bstep (se 2 (by rfl) ⟨1309263, by rfl⟩ : syracuseStep 3491369 = 2618527) B2618527
theorem B1034599 : Blo 1032607 1034599 := bstep (se 1 (by rfl) ⟨775949, by rfl⟩ : syracuseStep 1034599 = 1551899) B1551899
theorem B1035943 : Blo 1032607 1035943 := bstep (se 1 (by rfl) ⟨776957, by rfl⟩ : syracuseStep 1035943 = 1553915) B1553915
theorem B7852787 : Blo 1032607 7852787 := bstep (se 1 (by rfl) ⟨5889590, by rfl⟩ : syracuseStep 7852787 = 11779181) B11779181
theorem B4412171 : Blo 1032607 4412171 := bstep (se 1 (by rfl) ⟨3309128, by rfl⟩ : syracuseStep 4412171 = 6618257) B6618257
theorem B459396845 : Blo 1032607 459396845 := bstep (se 3 (by rfl) ⟨86136908, by rfl⟩ : syracuseStep 459396845 = 172273817) B172273817
theorem B60544907 : Blo 1032607 60544907 := bstep (se 1 (by rfl) ⟨45408680, by rfl⟩ : syracuseStep 60544907 = 90817361) B90817361
theorem B3924875 : Blo 1032607 3924875 := bstep (se 1 (by rfl) ⟨2943656, by rfl⟩ : syracuseStep 3924875 = 5887313) B5887313
theorem B3930221 : Blo 1032607 3930221 := bstep (se 3 (by rfl) ⟨736916, by rfl⟩ : syracuseStep 3930221 = 1473833) B1473833
theorem B5897063 : Blo 1032607 5897063 := bstep (se 1 (by rfl) ⟨4422797, by rfl⟩ : syracuseStep 5897063 = 8845595) B8845595
theorem B19889671 : Blo 1032607 19889671 := bstep (se 1 (by rfl) ⟨14917253, by rfl⟩ : syracuseStep 19889671 = 29834507) B29834507
theorem B9928615 : Blo 1032607 9928615 := bstep (se 1 (by rfl) ⟨7446461, by rfl⟩ : syracuseStep 9928615 = 14892923) B14892923
theorem B1966751 : Blo 1032607 1966751 := bstep (se 1 (by rfl) ⟨1475063, by rfl⟩ : syracuseStep 1966751 = 2950127) B2950127
theorem B2327579 : Blo 1032607 2327579 := bstep (se 1 (by rfl) ⟨1745684, by rfl⟩ : syracuseStep 2327579 = 3491369) B3491369
theorem B1549193 : Blo 1032607 1549193 := bstep (se 2 (by rfl) ⟨580947, by rfl⟩ : syracuseStep 1549193 = 1161895) B1161895
theorem B26519561 : Blo 1032607 26519561 := bstep (se 2 (by rfl) ⟨9944835, by rfl⟩ : syracuseStep 26519561 = 19889671) B19889671
theorem B1748459 : Blo 1032607 1748459 := bstep (se 1 (by rfl) ⟨1311344, by rfl⟩ : syracuseStep 1748459 = 2622689) B2622689
theorem B306264563 : Blo 1032607 306264563 := bstep (se 1 (by rfl) ⟨229698422, by rfl⟩ : syracuseStep 306264563 = 459396845) B459396845
theorem B1035503 : Blo 1032607 1035503 := bstep (se 1 (by rfl) ⟨776627, by rfl⟩ : syracuseStep 1035503 = 1553255) B1553255
theorem B1036143 : Blo 1032607 1036143 := bstep (se 1 (by rfl) ⟨777107, by rfl⟩ : syracuseStep 1036143 = 1554215) B1554215
theorem B4413503 : Blo 1032607 4413503 := bstep (se 1 (by rfl) ⟨3310127, by rfl⟩ : syracuseStep 4413503 = 6620255) B6620255
theorem B16998713 : Blo 1032607 16998713 := bstep (se 2 (by rfl) ⟨6374517, by rfl⟩ : syracuseStep 16998713 = 12749035) B12749035
theorem B5235191 : Blo 1032607 5235191 := bstep (se 1 (by rfl) ⟨3926393, by rfl⟩ : syracuseStep 5235191 = 7852787) B7852787
theorem B2941447 : Blo 1032607 2941447 := bstep (se 1 (by rfl) ⟨2206085, by rfl⟩ : syracuseStep 2941447 = 4412171) B4412171
theorem B40363271 : Blo 1032607 40363271 := bstep (se 1 (by rfl) ⟨30272453, by rfl⟩ : syracuseStep 40363271 = 60544907) B60544907
theorem B2616583 : Blo 1032607 2616583 := bstep (se 1 (by rfl) ⟨1962437, by rfl⟩ : syracuseStep 2616583 = 3924875) B3924875
theorem B2323871 : Blo 1032607 2323871 := bstep (se 1 (by rfl) ⟨1742903, by rfl⟩ : syracuseStep 2323871 = 3485807) B3485807
theorem B1472575 : Blo 1032607 1472575 := bstep (se 1 (by rfl) ⟨1104431, by rfl⟩ : syracuseStep 1472575 = 2208863) B2208863
theorem B2620147 : Blo 1032607 2620147 := bstep (se 1 (by rfl) ⟨1965110, by rfl⟩ : syracuseStep 2620147 = 3930221) B3930221
theorem B3931375 : Blo 1032607 3931375 := bstep (se 1 (by rfl) ⟨2948531, by rfl⟩ : syracuseStep 3931375 = 5897063) B5897063
theorem B13238153 : Blo 1032607 13238153 := bstep (se 2 (by rfl) ⟨4964307, by rfl⟩ : syracuseStep 13238153 = 9928615) B9928615
theorem B40304633 : Blo 1032607 40304633 := bstep (se 2 (by rfl) ⟨15114237, by rfl⟩ : syracuseStep 40304633 = 30228475) B30228475
theorem B1311167 : Blo 1032607 1311167 := bstep (se 1 (by rfl) ⟨983375, by rfl⟩ : syracuseStep 1311167 = 1966751) B1966751
theorem B26908847 : Blo 1032607 26908847 := bstep (se 1 (by rfl) ⟨20181635, by rfl⟩ : syracuseStep 26908847 = 40363271) B40363271
theorem B1549247 : Blo 1032607 1549247 := bstep (se 1 (by rfl) ⟨1161935, by rfl⟩ : syracuseStep 1549247 = 2323871) B2323871
theorem B8825435 : Blo 1032607 8825435 := bstep (se 1 (by rfl) ⟨6619076, by rfl⟩ : syracuseStep 8825435 = 13238153) B13238153
theorem B1551719 : Blo 1032607 1551719 := bstep (se 1 (by rfl) ⟨1163789, by rfl⟩ : syracuseStep 1551719 = 2327579) B2327579
theorem B3488777 : Blo 1032607 3488777 := bstep (se 2 (by rfl) ⟨1308291, by rfl⟩ : syracuseStep 3488777 = 2616583) B2616583
theorem B3490127 : Blo 1032607 3490127 := bstep (se 1 (by rfl) ⟨2617595, by rfl⟩ : syracuseStep 3490127 = 5235191) B5235191
theorem B1032795 : Blo 1032607 1032795 := bstep (se 1 (by rfl) ⟨774596, by rfl⟩ : syracuseStep 1032795 = 1549193) B1549193
theorem B17679707 : Blo 1032607 17679707 := bstep (se 1 (by rfl) ⟨13259780, by rfl⟩ : syracuseStep 17679707 = 26519561) B26519561
theorem B1165639 : Blo 1032607 1165639 := bstep (se 1 (by rfl) ⟨874229, by rfl⟩ : syracuseStep 1165639 = 1748459) B1748459
theorem B3493529 : Blo 1032607 3493529 := bstep (se 2 (by rfl) ⟨1310073, by rfl⟩ : syracuseStep 3493529 = 2620147) B2620147
theorem B3921929 : Blo 1032607 3921929 := bstep (se 2 (by rfl) ⟨1470723, by rfl⟩ : syracuseStep 3921929 = 2941447) B2941447
theorem B2942335 : Blo 1032607 2942335 := bstep (se 1 (by rfl) ⟨2206751, by rfl⟩ : syracuseStep 2942335 = 4413503) B4413503
theorem B11332475 : Blo 1032607 11332475 := bstep (se 1 (by rfl) ⟨8499356, by rfl⟩ : syracuseStep 11332475 = 16998713) B16998713
theorem B1963433 : Blo 1032607 1963433 := bstep (se 2 (by rfl) ⟨736287, by rfl⟩ : syracuseStep 1963433 = 1472575) B1472575
theorem B5241833 : Blo 1032607 5241833 := bstep (se 2 (by rfl) ⟨1965687, by rfl⟩ : syracuseStep 5241833 = 3931375) B3931375
theorem B204176375 : Blo 1032607 204176375 := bstep (se 1 (by rfl) ⟨153132281, by rfl⟩ : syracuseStep 204176375 = 306264563) B306264563
theorem B107479021 : Blo 1032607 107479021 := bstep (se 3 (by rfl) ⟨20152316, by rfl⟩ : syracuseStep 107479021 = 40304633) B40304633
theorem B2326751 : Blo 1032607 2326751 := bstep (se 1 (by rfl) ⟨1745063, by rfl⟩ : syracuseStep 2326751 = 3490127) B3490127
theorem B2329019 : Blo 1032607 2329019 := bstep (se 1 (by rfl) ⟨1746764, by rfl⟩ : syracuseStep 2329019 = 3493529) B3493529
theorem B143305361 : Blo 1032607 143305361 := bstep (se 2 (by rfl) ⟨53739510, by rfl⟩ : syracuseStep 143305361 = 107479021) B107479021
theorem B1554185 : Blo 1032607 1554185 := bstep (se 2 (by rfl) ⟨582819, by rfl⟩ : syracuseStep 1554185 = 1165639) B1165639
theorem B17939231 : Blo 1032607 17939231 := bstep (se 1 (by rfl) ⟨13454423, by rfl⟩ : syracuseStep 17939231 = 26908847) B26908847
theorem B1032831 : Blo 1032607 1032831 := bstep (se 1 (by rfl) ⟨774623, by rfl⟩ : syracuseStep 1032831 = 1549247) B1549247
theorem B5883623 : Blo 1032607 5883623 := bstep (se 1 (by rfl) ⟨4412717, by rfl⟩ : syracuseStep 5883623 = 8825435) B8825435
theorem B1034479 : Blo 1032607 1034479 := bstep (se 1 (by rfl) ⟨775859, by rfl⟩ : syracuseStep 1034479 = 1551719) B1551719
theorem B3494555 : Blo 1032607 3494555 := bstep (se 1 (by rfl) ⟨2620916, by rfl⟩ : syracuseStep 3494555 = 5241833) B5241833
theorem B11786471 : Blo 1032607 11786471 := bstep (se 1 (by rfl) ⟨8839853, by rfl⟩ : syracuseStep 11786471 = 17679707) B17679707
theorem B3496445 : Blo 1032607 3496445 := bstep (se 3 (by rfl) ⟨655583, by rfl⟩ : syracuseStep 3496445 = 1311167) B1311167
theorem B3923113 : Blo 1032607 3923113 := bstep (se 2 (by rfl) ⟨1471167, by rfl⟩ : syracuseStep 3923113 = 2942335) B2942335
theorem B2614619 : Blo 1032607 2614619 := bstep (se 1 (by rfl) ⟨1960964, by rfl⟩ : syracuseStep 2614619 = 3921929) B3921929
theorem B483518933 : Blo 1032607 483518933 := bstep (se 7 (by rfl) ⟨5666237, by rfl⟩ : syracuseStep 483518933 = 11332475) B11332475
theorem B1308955 : Blo 1032607 1308955 := bstep (se 1 (by rfl) ⟨981716, by rfl⟩ : syracuseStep 1308955 = 1963433) B1963433
theorem B136117583 : Blo 1032607 136117583 := bstep (se 1 (by rfl) ⟨102088187, by rfl⟩ : syracuseStep 136117583 = 204176375) B204176375
theorem B2325851 : Blo 1032607 2325851 := bstep (se 1 (by rfl) ⟨1744388, by rfl⟩ : syracuseStep 2325851 = 3488777) B3488777
theorem B2329703 : Blo 1032607 2329703 := bstep (se 1 (by rfl) ⟨1747277, by rfl⟩ : syracuseStep 2329703 = 3494555) B3494555
theorem B2330963 : Blo 1032607 2330963 := bstep (se 1 (by rfl) ⟨1748222, by rfl⟩ : syracuseStep 2330963 = 3496445) B3496445
theorem B1743079 : Blo 1032607 1743079 := bstep (se 1 (by rfl) ⟨1307309, by rfl⟩ : syracuseStep 1743079 = 2614619) B2614619
theorem B322345955 : Blo 1032607 322345955 := bstep (se 1 (by rfl) ⟨241759466, by rfl⟩ : syracuseStep 322345955 = 483518933) B483518933
theorem B1745273 : Blo 1032607 1745273 := bstep (se 2 (by rfl) ⟨654477, by rfl⟩ : syracuseStep 1745273 = 1308955) B1308955
theorem B90745055 : Blo 1032607 90745055 := bstep (se 1 (by rfl) ⟨68058791, by rfl⟩ : syracuseStep 90745055 = 136117583) B136117583
theorem B1550567 : Blo 1032607 1550567 := bstep (se 1 (by rfl) ⟨1162925, by rfl⟩ : syracuseStep 1550567 = 2325851) B2325851
theorem B1551167 : Blo 1032607 1551167 := bstep (se 1 (by rfl) ⟨1163375, by rfl⟩ : syracuseStep 1551167 = 2326751) B2326751
theorem B1552679 : Blo 1032607 1552679 := bstep (se 1 (by rfl) ⟨1164509, by rfl⟩ : syracuseStep 1552679 = 2329019) B2329019
theorem B95536907 : Blo 1032607 95536907 := bstep (se 1 (by rfl) ⟨71652680, by rfl⟩ : syracuseStep 95536907 = 143305361) B143305361
theorem B1036123 : Blo 1032607 1036123 := bstep (se 1 (by rfl) ⟨777092, by rfl⟩ : syracuseStep 1036123 = 1554185) B1554185
theorem B5230817 : Blo 1032607 5230817 := bstep (se 2 (by rfl) ⟨1961556, by rfl⟩ : syracuseStep 5230817 = 3923113) B3923113
theorem B3922415 : Blo 1032607 3922415 := bstep (se 1 (by rfl) ⟨2941811, by rfl⟩ : syracuseStep 3922415 = 5883623) B5883623
theorem B7857647 : Blo 1032607 7857647 := bstep (se 1 (by rfl) ⟨5893235, by rfl⟩ : syracuseStep 7857647 = 11786471) B11786471
theorem B11959487 : Blo 1032607 11959487 := bstep (se 1 (by rfl) ⟨8969615, by rfl⟩ : syracuseStep 11959487 = 17939231) B17939231
theorem B214897303 : Blo 1032607 214897303 := bstep (se 1 (by rfl) ⟨161172977, by rfl⟩ : syracuseStep 214897303 = 322345955) B322345955
theorem B60496703 : Blo 1032607 60496703 := bstep (se 1 (by rfl) ⟨45372527, by rfl⟩ : syracuseStep 60496703 = 90745055) B90745055
theorem B7972991 : Blo 1032607 7972991 := bstep (se 1 (by rfl) ⟨5979743, by rfl⟩ : syracuseStep 7972991 = 11959487) B11959487
theorem B1553135 : Blo 1032607 1553135 := bstep (se 1 (by rfl) ⟨1164851, by rfl⟩ : syracuseStep 1553135 = 2329703) B2329703
theorem B3487211 : Blo 1032607 3487211 := bstep (se 1 (by rfl) ⟨2615408, by rfl⟩ : syracuseStep 3487211 = 5230817) B5230817
theorem B1553975 : Blo 1032607 1553975 := bstep (se 1 (by rfl) ⟨1165481, by rfl⟩ : syracuseStep 1553975 = 2330963) B2330963
theorem B1163515 : Blo 1032607 1163515 := bstep (se 1 (by rfl) ⟨872636, by rfl⟩ : syracuseStep 1163515 = 1745273) B1745273
theorem B1033711 : Blo 1032607 1033711 := bstep (se 1 (by rfl) ⟨775283, by rfl⟩ : syracuseStep 1033711 = 1550567) B1550567
theorem B1034111 : Blo 1032607 1034111 := bstep (se 1 (by rfl) ⟨775583, by rfl⟩ : syracuseStep 1034111 = 1551167) B1551167
theorem B1035119 : Blo 1032607 1035119 := bstep (se 1 (by rfl) ⟨776339, by rfl⟩ : syracuseStep 1035119 = 1552679) B1552679
theorem B63691271 : Blo 1032607 63691271 := bstep (se 1 (by rfl) ⟨47768453, by rfl⟩ : syracuseStep 63691271 = 95536907) B95536907
theorem B2614943 : Blo 1032607 2614943 := bstep (se 1 (by rfl) ⟨1961207, by rfl⟩ : syracuseStep 2614943 = 3922415) B3922415
theorem B5238431 : Blo 1032607 5238431 := bstep (se 1 (by rfl) ⟨3928823, by rfl⟩ : syracuseStep 5238431 = 7857647) B7857647
theorem B2324105 : Blo 1032607 2324105 := bstep (se 2 (by rfl) ⟨871539, by rfl⟩ : syracuseStep 2324105 = 1743079) B1743079
theorem B286529737 : Blo 1032607 286529737 := bstep (se 2 (by rfl) ⟨107448651, by rfl⟩ : syracuseStep 286529737 = 214897303) B214897303
theorem B1743295 : Blo 1032607 1743295 := bstep (se 1 (by rfl) ⟨1307471, by rfl⟩ : syracuseStep 1743295 = 2614943) B2614943
theorem B5315327 : Blo 1032607 5315327 := bstep (se 1 (by rfl) ⟨3986495, by rfl⟩ : syracuseStep 5315327 = 7972991) B7972991
theorem B1549403 : Blo 1032607 1549403 := bstep (se 1 (by rfl) ⟨1162052, by rfl⟩ : syracuseStep 1549403 = 2324105) B2324105
theorem B1551353 : Blo 1032607 1551353 := bstep (se 2 (by rfl) ⟨581757, by rfl⟩ : syracuseStep 1551353 = 1163515) B1163515
theorem B3492287 : Blo 1032607 3492287 := bstep (se 1 (by rfl) ⟨2619215, by rfl⟩ : syracuseStep 3492287 = 5238431) B5238431
theorem B1035423 : Blo 1032607 1035423 := bstep (se 1 (by rfl) ⟨776567, by rfl⟩ : syracuseStep 1035423 = 1553135) B1553135
theorem B1035983 : Blo 1032607 1035983 := bstep (se 1 (by rfl) ⟨776987, by rfl⟩ : syracuseStep 1035983 = 1553975) B1553975
theorem B42460847 : Blo 1032607 42460847 := bstep (se 1 (by rfl) ⟨31845635, by rfl⟩ : syracuseStep 42460847 = 63691271) B63691271
theorem B40331135 : Blo 1032607 40331135 := bstep (se 1 (by rfl) ⟨30248351, by rfl⟩ : syracuseStep 40331135 = 60496703) B60496703
theorem B2324807 : Blo 1032607 2324807 := bstep (se 1 (by rfl) ⟨1743605, by rfl⟩ : syracuseStep 2324807 = 3487211) B3487211
theorem B2328191 : Blo 1032607 2328191 := bstep (se 1 (by rfl) ⟨1746143, by rfl⟩ : syracuseStep 2328191 = 3492287) B3492287
theorem B3543551 : Blo 1032607 3543551 := bstep (se 1 (by rfl) ⟨2657663, by rfl⟩ : syracuseStep 3543551 = 5315327) B5315327
theorem B1549871 : Blo 1032607 1549871 := bstep (se 1 (by rfl) ⟨1162403, by rfl⟩ : syracuseStep 1549871 = 2324807) B2324807
theorem B1032935 : Blo 1032607 1032935 := bstep (se 1 (by rfl) ⟨774701, by rfl⟩ : syracuseStep 1032935 = 1549403) B1549403
theorem B26887423 : Blo 1032607 26887423 := bstep (se 1 (by rfl) ⟨20165567, by rfl⟩ : syracuseStep 26887423 = 40331135) B40331135
theorem B1034235 : Blo 1032607 1034235 := bstep (se 1 (by rfl) ⟨775676, by rfl⟩ : syracuseStep 1034235 = 1551353) B1551353
theorem B28307231 : Blo 1032607 28307231 := bstep (se 1 (by rfl) ⟨21230423, by rfl⟩ : syracuseStep 28307231 = 42460847) B42460847
theorem B382039649 : Blo 1032607 382039649 := bstep (se 2 (by rfl) ⟨143264868, by rfl⟩ : syracuseStep 382039649 = 286529737) B286529737
theorem B2324393 : Blo 1032607 2324393 := bstep (se 2 (by rfl) ⟨871647, by rfl⟩ : syracuseStep 2324393 = 1743295) B1743295
theorem B35849897 : Blo 1032607 35849897 := bstep (se 2 (by rfl) ⟨13443711, by rfl⟩ : syracuseStep 35849897 = 26887423) B26887423
theorem B2362367 : Blo 1032607 2362367 := bstep (se 1 (by rfl) ⟨1771775, by rfl⟩ : syracuseStep 2362367 = 3543551) B3543551
theorem B1549595 : Blo 1032607 1549595 := bstep (se 1 (by rfl) ⟨1162196, by rfl⟩ : syracuseStep 1549595 = 2324393) B2324393
theorem B1552127 : Blo 1032607 1552127 := bstep (se 1 (by rfl) ⟨1164095, by rfl⟩ : syracuseStep 1552127 = 2328191) B2328191
theorem B1033247 : Blo 1032607 1033247 := bstep (se 1 (by rfl) ⟨774935, by rfl⟩ : syracuseStep 1033247 = 1549871) B1549871
theorem B254693099 : Blo 1032607 254693099 := bstep (se 1 (by rfl) ⟨191019824, by rfl⟩ : syracuseStep 254693099 = 382039649) B382039649
theorem B18871487 : Blo 1032607 18871487 := bstep (se 1 (by rfl) ⟨14153615, by rfl⟩ : syracuseStep 18871487 = 28307231) B28307231
theorem B1574911 : Blo 1032607 1574911 := bstep (se 1 (by rfl) ⟨1181183, by rfl⟩ : syracuseStep 1574911 = 2362367) B2362367
theorem B23899931 : Blo 1032607 23899931 := bstep (se 1 (by rfl) ⟨17924948, by rfl⟩ : syracuseStep 23899931 = 35849897) B35849897
theorem B1033063 : Blo 1032607 1033063 := bstep (se 1 (by rfl) ⟨774797, by rfl⟩ : syracuseStep 1033063 = 1549595) B1549595
theorem B1034751 : Blo 1032607 1034751 := bstep (se 1 (by rfl) ⟨776063, by rfl⟩ : syracuseStep 1034751 = 1552127) B1552127
theorem B169795399 : Blo 1032607 169795399 := bstep (se 1 (by rfl) ⟨127346549, by rfl⟩ : syracuseStep 169795399 = 254693099) B254693099
theorem B12580991 : Blo 1032607 12580991 := bstep (se 1 (by rfl) ⟨9435743, by rfl⟩ : syracuseStep 12580991 = 18871487) B18871487
theorem B2099881 : Blo 1032607 2099881 := bstep (se 2 (by rfl) ⟨787455, by rfl⟩ : syracuseStep 2099881 = 1574911) B1574911
theorem B15933287 : Blo 1032607 15933287 := bstep (se 1 (by rfl) ⟨11949965, by rfl⟩ : syracuseStep 15933287 = 23899931) B23899931
theorem B8387327 : Blo 1032607 8387327 := bstep (se 1 (by rfl) ⟨6290495, by rfl⟩ : syracuseStep 8387327 = 12580991) B12580991
theorem B226393865 : Blo 1032607 226393865 := bstep (se 2 (by rfl) ⟨84897699, by rfl⟩ : syracuseStep 226393865 = 169795399) B169795399
theorem B10622191 : Blo 1032607 10622191 := bstep (se 1 (by rfl) ⟨7966643, by rfl⟩ : syracuseStep 10622191 = 15933287) B15933287
theorem B2799841 : Blo 1032607 2799841 := bstep (se 2 (by rfl) ⟨1049940, by rfl⟩ : syracuseStep 2799841 = 2099881) B2099881
theorem B5591551 : Blo 1032607 5591551 := bstep (se 1 (by rfl) ⟨4193663, by rfl⟩ : syracuseStep 5591551 = 8387327) B8387327
theorem B150929243 : Blo 1032607 150929243 := bstep (se 1 (by rfl) ⟨113196932, by rfl⟩ : syracuseStep 150929243 = 226393865) B226393865
theorem B14162921 : Blo 1032607 14162921 := bstep (se 2 (by rfl) ⟨5311095, by rfl⟩ : syracuseStep 14162921 = 10622191) B10622191
theorem B7455401 : Blo 1032607 7455401 := bstep (se 2 (by rfl) ⟨2795775, by rfl⟩ : syracuseStep 7455401 = 5591551) B5591551
theorem B100619495 : Blo 1032607 100619495 := bstep (se 1 (by rfl) ⟨75464621, by rfl⟩ : syracuseStep 100619495 = 150929243) B150929243
theorem B3733121 : Blo 1032607 3733121 := bstep (se 2 (by rfl) ⟨1399920, by rfl⟩ : syracuseStep 3733121 = 2799841) B2799841
theorem B67079663 : Blo 1032607 67079663 := bstep (se 1 (by rfl) ⟨50309747, by rfl⟩ : syracuseStep 67079663 = 100619495) B100619495
theorem B9441947 : Blo 1032607 9441947 := bstep (se 1 (by rfl) ⟨7081460, by rfl⟩ : syracuseStep 9441947 = 14162921) B14162921
theorem B4970267 : Blo 1032607 4970267 := bstep (se 1 (by rfl) ⟨3727700, by rfl⟩ : syracuseStep 4970267 = 7455401) B7455401
theorem B2488747 : Blo 1032607 2488747 := bstep (se 1 (by rfl) ⟨1866560, by rfl⟩ : syracuseStep 2488747 = 3733121) B3733121
theorem B6294631 : Blo 1032607 6294631 := bstep (se 1 (by rfl) ⟨4720973, by rfl⟩ : syracuseStep 6294631 = 9441947) B9441947
theorem B3313511 : Blo 1032607 3313511 := bstep (se 1 (by rfl) ⟨2485133, by rfl⟩ : syracuseStep 3313511 = 4970267) B4970267
theorem B3318329 : Blo 1032607 3318329 := bstep (se 2 (by rfl) ⟨1244373, by rfl⟩ : syracuseStep 3318329 = 2488747) B2488747
theorem B44719775 : Blo 1032607 44719775 := bstep (se 1 (by rfl) ⟨33539831, by rfl⟩ : syracuseStep 44719775 = 67079663) B67079663
theorem B8392841 : Blo 1032607 8392841 := bstep (se 2 (by rfl) ⟨3147315, by rfl⟩ : syracuseStep 8392841 = 6294631) B6294631
theorem B2209007 : Blo 1032607 2209007 := bstep (se 1 (by rfl) ⟨1656755, by rfl⟩ : syracuseStep 2209007 = 3313511) B3313511
theorem B2212219 : Blo 1032607 2212219 := bstep (se 1 (by rfl) ⟨1659164, by rfl⟩ : syracuseStep 2212219 = 3318329) B3318329
theorem B29813183 : Blo 1032607 29813183 := bstep (se 1 (by rfl) ⟨22359887, by rfl⟩ : syracuseStep 29813183 = 44719775) B44719775
theorem B2949625 : Blo 1032607 2949625 := bstep (se 2 (by rfl) ⟨1106109, by rfl⟩ : syracuseStep 2949625 = 2212219) B2212219
theorem B19875455 : Blo 1032607 19875455 := bstep (se 1 (by rfl) ⟨14906591, by rfl⟩ : syracuseStep 19875455 = 29813183) B29813183
theorem B5595227 : Blo 1032607 5595227 := bstep (se 1 (by rfl) ⟨4196420, by rfl⟩ : syracuseStep 5595227 = 8392841) B8392841
theorem B1472671 : Blo 1032607 1472671 := bstep (se 1 (by rfl) ⟨1104503, by rfl⟩ : syracuseStep 1472671 = 2209007) B2209007
theorem B3932833 : Blo 1032607 3932833 := bstep (se 2 (by rfl) ⟨1474812, by rfl⟩ : syracuseStep 3932833 = 2949625) B2949625
theorem B13250303 : Blo 1032607 13250303 := bstep (se 1 (by rfl) ⟨9937727, by rfl⟩ : syracuseStep 13250303 = 19875455) B19875455
theorem B7854245 : Blo 1032607 7854245 := bstep (se 4 (by rfl) ⟨736335, by rfl⟩ : syracuseStep 7854245 = 1472671) B1472671
theorem B3730151 : Blo 1032607 3730151 := bstep (se 1 (by rfl) ⟨2797613, by rfl⟩ : syracuseStep 3730151 = 5595227) B5595227
theorem B5243777 : Blo 1032607 5243777 := bstep (se 2 (by rfl) ⟨1966416, by rfl⟩ : syracuseStep 5243777 = 3932833) B3932833
theorem B9947069 : Blo 1032607 9947069 := bstep (se 3 (by rfl) ⟨1865075, by rfl⟩ : syracuseStep 9947069 = 3730151) B3730151
theorem B8833535 : Blo 1032607 8833535 := bstep (se 1 (by rfl) ⟨6625151, by rfl⟩ : syracuseStep 8833535 = 13250303) B13250303
theorem B5236163 : Blo 1032607 5236163 := bstep (se 1 (by rfl) ⟨3927122, by rfl⟩ : syracuseStep 5236163 = 7854245) B7854245
theorem B6631379 : Blo 1032607 6631379 := bstep (se 1 (by rfl) ⟨4973534, by rfl⟩ : syracuseStep 6631379 = 9947069) B9947069
theorem B3490775 : Blo 1032607 3490775 := bstep (se 1 (by rfl) ⟨2618081, by rfl⟩ : syracuseStep 3490775 = 5236163) B5236163
theorem B3495851 : Blo 1032607 3495851 := bstep (se 1 (by rfl) ⟨2621888, by rfl⟩ : syracuseStep 3495851 = 5243777) B5243777
theorem B5889023 : Blo 1032607 5889023 := bstep (se 1 (by rfl) ⟨4416767, by rfl⟩ : syracuseStep 5889023 = 8833535) B8833535
theorem B2327183 : Blo 1032607 2327183 := bstep (se 1 (by rfl) ⟨1745387, by rfl⟩ : syracuseStep 2327183 = 3490775) B3490775
theorem B2330567 : Blo 1032607 2330567 := bstep (se 1 (by rfl) ⟨1747925, by rfl⟩ : syracuseStep 2330567 = 3495851) B3495851
theorem B3926015 : Blo 1032607 3926015 := bstep (se 1 (by rfl) ⟨2944511, by rfl⟩ : syracuseStep 3926015 = 5889023) B5889023
theorem B4420919 : Blo 1032607 4420919 := bstep (se 1 (by rfl) ⟨3315689, by rfl⟩ : syracuseStep 4420919 = 6631379) B6631379
theorem B1551455 : Blo 1032607 1551455 := bstep (se 1 (by rfl) ⟨1163591, by rfl⟩ : syracuseStep 1551455 = 2327183) B2327183
theorem B1553711 : Blo 1032607 1553711 := bstep (se 1 (by rfl) ⟨1165283, by rfl⟩ : syracuseStep 1553711 = 2330567) B2330567
theorem B2617343 : Blo 1032607 2617343 := bstep (se 1 (by rfl) ⟨1963007, by rfl⟩ : syracuseStep 2617343 = 3926015) B3926015
theorem B2947279 : Blo 1032607 2947279 := bstep (se 1 (by rfl) ⟨2210459, by rfl⟩ : syracuseStep 2947279 = 4420919) B4420919
theorem B1744895 : Blo 1032607 1744895 := bstep (se 1 (by rfl) ⟨1308671, by rfl⟩ : syracuseStep 1744895 = 2617343) B2617343
theorem B1034303 : Blo 1032607 1034303 := bstep (se 1 (by rfl) ⟨775727, by rfl⟩ : syracuseStep 1034303 = 1551455) B1551455
theorem B1035807 : Blo 1032607 1035807 := bstep (se 1 (by rfl) ⟨776855, by rfl⟩ : syracuseStep 1035807 = 1553711) B1553711
theorem B3929705 : Blo 1032607 3929705 := bstep (se 2 (by rfl) ⟨1473639, by rfl⟩ : syracuseStep 3929705 = 2947279) B2947279
theorem B1163263 : Blo 1032607 1163263 := bstep (se 1 (by rfl) ⟨872447, by rfl⟩ : syracuseStep 1163263 = 1744895) B1744895
theorem B2619803 : Blo 1032607 2619803 := bstep (se 1 (by rfl) ⟨1964852, by rfl⟩ : syracuseStep 2619803 = 3929705) B3929705
theorem B1746535 : Blo 1032607 1746535 := bstep (se 1 (by rfl) ⟨1309901, by rfl⟩ : syracuseStep 1746535 = 2619803) B2619803
theorem B1551017 : Blo 1032607 1551017 := bstep (se 2 (by rfl) ⟨581631, by rfl⟩ : syracuseStep 1551017 = 1163263) B1163263
theorem B2328713 : Blo 1032607 2328713 := bstep (se 2 (by rfl) ⟨873267, by rfl⟩ : syracuseStep 2328713 = 1746535) B1746535
theorem B1034011 : Blo 1032607 1034011 := bstep (se 1 (by rfl) ⟨775508, by rfl⟩ : syracuseStep 1034011 = 1551017) B1551017
theorem B1552475 : Blo 1032607 1552475 := bstep (se 1 (by rfl) ⟨1164356, by rfl⟩ : syracuseStep 1552475 = 2328713) B2328713
theorem B1034983 : Blo 1032607 1034983 := bstep (se 1 (by rfl) ⟨776237, by rfl⟩ : syracuseStep 1034983 = 1552475) B1552475

theorem C0 (j : ℕ) (h1 : 258151 ≤ j) (h2 : j ≤ 258850) : Blo 1032607 (4 * j + 3) := by
  interval_cases j
  · exact B1032607
  · exact B1032611
  · exact B1032615
  · exact B1032619
  · exact B1032623
  · exact B1032627
  · exact B1032631
  · exact B1032635
  · exact B1032639
  · exact B1032643
  · exact B1032647
  · exact B1032651
  · exact B1032655
  · exact B1032659
  · exact B1032663
  · exact B1032667
  · exact B1032671
  · exact B1032675
  · exact B1032679
  · exact B1032683
  · exact B1032687
  · exact B1032691
  · exact B1032695
  · exact B1032699
  · exact B1032703
  · exact B1032707
  · exact B1032711
  · exact B1032715
  · exact B1032719
  · exact B1032723
  · exact B1032727
  · exact B1032731
  · exact B1032735
  · exact B1032739
  · exact B1032743
  · exact B1032747
  · exact B1032751
  · exact B1032755
  · exact B1032759
  · exact B1032763
  · exact B1032767
  · exact B1032771
  · exact B1032775
  · exact B1032779
  · exact B1032783
  · exact B1032787
  · exact B1032791
  · exact B1032795
  · exact B1032799
  · exact B1032803
  · exact B1032807
  · exact B1032811
  · exact B1032815
  · exact B1032819
  · exact B1032823
  · exact B1032827
  · exact B1032831
  · exact B1032835
  · exact B1032839
  · exact B1032843
  · exact B1032847
  · exact B1032851
  · exact B1032855
  · exact B1032859
  · exact B1032863
  · exact B1032867
  · exact B1032871
  · exact B1032875
  · exact B1032879
  · exact B1032883
  · exact B1032887
  · exact B1032891
  · exact B1032895
  · exact B1032899
  · exact B1032903
  · exact B1032907
  · exact B1032911
  · exact B1032915
  · exact B1032919
  · exact B1032923
  · exact B1032927
  · exact B1032931
  · exact B1032935
  · exact B1032939
  · exact B1032943
  · exact B1032947
  · exact B1032951
  · exact B1032955
  · exact B1032959
  · exact B1032963
  · exact B1032967
  · exact B1032971
  · exact B1032975
  · exact B1032979
  · exact B1032983
  · exact B1032987
  · exact B1032991
  · exact B1032995
  · exact B1032999
  · exact B1033003
  · exact B1033007
  · exact B1033011
  · exact B1033015
  · exact B1033019
  · exact B1033023
  · exact B1033027
  · exact B1033031
  · exact B1033035
  · exact B1033039
  · exact B1033043
  · exact B1033047
  · exact B1033051
  · exact B1033055
  · exact B1033059
  · exact B1033063
  · exact B1033067
  · exact B1033071
  · exact B1033075
  · exact B1033079
  · exact B1033083
  · exact B1033087
  · exact B1033091
  · exact B1033095
  · exact B1033099
  · exact B1033103
  · exact B1033107
  · exact B1033111
  · exact B1033115
  · exact B1033119
  · exact B1033123
  · exact B1033127
  · exact B1033131
  · exact B1033135
  · exact B1033139
  · exact B1033143
  · exact B1033147
  · exact B1033151
  · exact B1033155
  · exact B1033159
  · exact B1033163
  · exact B1033167
  · exact B1033171
  · exact B1033175
  · exact B1033179
  · exact B1033183
  · exact B1033187
  · exact B1033191
  · exact B1033195
  · exact B1033199
  · exact B1033203
  · exact B1033207
  · exact B1033211
  · exact B1033215
  · exact B1033219
  · exact B1033223
  · exact B1033227
  · exact B1033231
  · exact B1033235
  · exact B1033239
  · exact B1033243
  · exact B1033247
  · exact B1033251
  · exact B1033255
  · exact B1033259
  · exact B1033263
  · exact B1033267
  · exact B1033271
  · exact B1033275
  · exact B1033279
  · exact B1033283
  · exact B1033287
  · exact B1033291
  · exact B1033295
  · exact B1033299
  · exact B1033303
  · exact B1033307
  · exact B1033311
  · exact B1033315
  · exact B1033319
  · exact B1033323
  · exact B1033327
  · exact B1033331
  · exact B1033335
  · exact B1033339
  · exact B1033343
  · exact B1033347
  · exact B1033351
  · exact B1033355
  · exact B1033359
  · exact B1033363
  · exact B1033367
  · exact B1033371
  · exact B1033375
  · exact B1033379
  · exact B1033383
  · exact B1033387
  · exact B1033391
  · exact B1033395
  · exact B1033399
  · exact B1033403
  · exact B1033407
  · exact B1033411
  · exact B1033415
  · exact B1033419
  · exact B1033423
  · exact B1033427
  · exact B1033431
  · exact B1033435
  · exact B1033439
  · exact B1033443
  · exact B1033447
  · exact B1033451
  · exact B1033455
  · exact B1033459
  · exact B1033463
  · exact B1033467
  · exact B1033471
  · exact B1033475
  · exact B1033479
  · exact B1033483
  · exact B1033487
  · exact B1033491
  · exact B1033495
  · exact B1033499
  · exact B1033503
  · exact B1033507
  · exact B1033511
  · exact B1033515
  · exact B1033519
  · exact B1033523
  · exact B1033527
  · exact B1033531
  · exact B1033535
  · exact B1033539
  · exact B1033543
  · exact B1033547
  · exact B1033551
  · exact B1033555
  · exact B1033559
  · exact B1033563
  · exact B1033567
  · exact B1033571
  · exact B1033575
  · exact B1033579
  · exact B1033583
  · exact B1033587
  · exact B1033591
  · exact B1033595
  · exact B1033599
  · exact B1033603
  · exact B1033607
  · exact B1033611
  · exact B1033615
  · exact B1033619
  · exact B1033623
  · exact B1033627
  · exact B1033631
  · exact B1033635
  · exact B1033639
  · exact B1033643
  · exact B1033647
  · exact B1033651
  · exact B1033655
  · exact B1033659
  · exact B1033663
  · exact B1033667
  · exact B1033671
  · exact B1033675
  · exact B1033679
  · exact B1033683
  · exact B1033687
  · exact B1033691
  · exact B1033695
  · exact B1033699
  · exact B1033703
  · exact B1033707
  · exact B1033711
  · exact B1033715
  · exact B1033719
  · exact B1033723
  · exact B1033727
  · exact B1033731
  · exact B1033735
  · exact B1033739
  · exact B1033743
  · exact B1033747
  · exact B1033751
  · exact B1033755
  · exact B1033759
  · exact B1033763
  · exact B1033767
  · exact B1033771
  · exact B1033775
  · exact B1033779
  · exact B1033783
  · exact B1033787
  · exact B1033791
  · exact B1033795
  · exact B1033799
  · exact B1033803
  · exact B1033807
  · exact B1033811
  · exact B1033815
  · exact B1033819
  · exact B1033823
  · exact B1033827
  · exact B1033831
  · exact B1033835
  · exact B1033839
  · exact B1033843
  · exact B1033847
  · exact B1033851
  · exact B1033855
  · exact B1033859
  · exact B1033863
  · exact B1033867
  · exact B1033871
  · exact B1033875
  · exact B1033879
  · exact B1033883
  · exact B1033887
  · exact B1033891
  · exact B1033895
  · exact B1033899
  · exact B1033903
  · exact B1033907
  · exact B1033911
  · exact B1033915
  · exact B1033919
  · exact B1033923
  · exact B1033927
  · exact B1033931
  · exact B1033935
  · exact B1033939
  · exact B1033943
  · exact B1033947
  · exact B1033951
  · exact B1033955
  · exact B1033959
  · exact B1033963
  · exact B1033967
  · exact B1033971
  · exact B1033975
  · exact B1033979
  · exact B1033983
  · exact B1033987
  · exact B1033991
  · exact B1033995
  · exact B1033999
  · exact B1034003
  · exact B1034007
  · exact B1034011
  · exact B1034015
  · exact B1034019
  · exact B1034023
  · exact B1034027
  · exact B1034031
  · exact B1034035
  · exact B1034039
  · exact B1034043
  · exact B1034047
  · exact B1034051
  · exact B1034055
  · exact B1034059
  · exact B1034063
  · exact B1034067
  · exact B1034071
  · exact B1034075
  · exact B1034079
  · exact B1034083
  · exact B1034087
  · exact B1034091
  · exact B1034095
  · exact B1034099
  · exact B1034103
  · exact B1034107
  · exact B1034111
  · exact B1034115
  · exact B1034119
  · exact B1034123
  · exact B1034127
  · exact B1034131
  · exact B1034135
  · exact B1034139
  · exact B1034143
  · exact B1034147
  · exact B1034151
  · exact B1034155
  · exact B1034159
  · exact B1034163
  · exact B1034167
  · exact B1034171
  · exact B1034175
  · exact B1034179
  · exact B1034183
  · exact B1034187
  · exact B1034191
  · exact B1034195
  · exact B1034199
  · exact B1034203
  · exact B1034207
  · exact B1034211
  · exact B1034215
  · exact B1034219
  · exact B1034223
  · exact B1034227
  · exact B1034231
  · exact B1034235
  · exact B1034239
  · exact B1034243
  · exact B1034247
  · exact B1034251
  · exact B1034255
  · exact B1034259
  · exact B1034263
  · exact B1034267
  · exact B1034271
  · exact B1034275
  · exact B1034279
  · exact B1034283
  · exact B1034287
  · exact B1034291
  · exact B1034295
  · exact B1034299
  · exact B1034303
  · exact B1034307
  · exact B1034311
  · exact B1034315
  · exact B1034319
  · exact B1034323
  · exact B1034327
  · exact B1034331
  · exact B1034335
  · exact B1034339
  · exact B1034343
  · exact B1034347
  · exact B1034351
  · exact B1034355
  · exact B1034359
  · exact B1034363
  · exact B1034367
  · exact B1034371
  · exact B1034375
  · exact B1034379
  · exact B1034383
  · exact B1034387
  · exact B1034391
  · exact B1034395
  · exact B1034399
  · exact B1034403
  · exact B1034407
  · exact B1034411
  · exact B1034415
  · exact B1034419
  · exact B1034423
  · exact B1034427
  · exact B1034431
  · exact B1034435
  · exact B1034439
  · exact B1034443
  · exact B1034447
  · exact B1034451
  · exact B1034455
  · exact B1034459
  · exact B1034463
  · exact B1034467
  · exact B1034471
  · exact B1034475
  · exact B1034479
  · exact B1034483
  · exact B1034487
  · exact B1034491
  · exact B1034495
  · exact B1034499
  · exact B1034503
  · exact B1034507
  · exact B1034511
  · exact B1034515
  · exact B1034519
  · exact B1034523
  · exact B1034527
  · exact B1034531
  · exact B1034535
  · exact B1034539
  · exact B1034543
  · exact B1034547
  · exact B1034551
  · exact B1034555
  · exact B1034559
  · exact B1034563
  · exact B1034567
  · exact B1034571
  · exact B1034575
  · exact B1034579
  · exact B1034583
  · exact B1034587
  · exact B1034591
  · exact B1034595
  · exact B1034599
  · exact B1034603
  · exact B1034607
  · exact B1034611
  · exact B1034615
  · exact B1034619
  · exact B1034623
  · exact B1034627
  · exact B1034631
  · exact B1034635
  · exact B1034639
  · exact B1034643
  · exact B1034647
  · exact B1034651
  · exact B1034655
  · exact B1034659
  · exact B1034663
  · exact B1034667
  · exact B1034671
  · exact B1034675
  · exact B1034679
  · exact B1034683
  · exact B1034687
  · exact B1034691
  · exact B1034695
  · exact B1034699
  · exact B1034703
  · exact B1034707
  · exact B1034711
  · exact B1034715
  · exact B1034719
  · exact B1034723
  · exact B1034727
  · exact B1034731
  · exact B1034735
  · exact B1034739
  · exact B1034743
  · exact B1034747
  · exact B1034751
  · exact B1034755
  · exact B1034759
  · exact B1034763
  · exact B1034767
  · exact B1034771
  · exact B1034775
  · exact B1034779
  · exact B1034783
  · exact B1034787
  · exact B1034791
  · exact B1034795
  · exact B1034799
  · exact B1034803
  · exact B1034807
  · exact B1034811
  · exact B1034815
  · exact B1034819
  · exact B1034823
  · exact B1034827
  · exact B1034831
  · exact B1034835
  · exact B1034839
  · exact B1034843
  · exact B1034847
  · exact B1034851
  · exact B1034855
  · exact B1034859
  · exact B1034863
  · exact B1034867
  · exact B1034871
  · exact B1034875
  · exact B1034879
  · exact B1034883
  · exact B1034887
  · exact B1034891
  · exact B1034895
  · exact B1034899
  · exact B1034903
  · exact B1034907
  · exact B1034911
  · exact B1034915
  · exact B1034919
  · exact B1034923
  · exact B1034927
  · exact B1034931
  · exact B1034935
  · exact B1034939
  · exact B1034943
  · exact B1034947
  · exact B1034951
  · exact B1034955
  · exact B1034959
  · exact B1034963
  · exact B1034967
  · exact B1034971
  · exact B1034975
  · exact B1034979
  · exact B1034983
  · exact B1034987
  · exact B1034991
  · exact B1034995
  · exact B1034999
  · exact B1035003
  · exact B1035007
  · exact B1035011
  · exact B1035015
  · exact B1035019
  · exact B1035023
  · exact B1035027
  · exact B1035031
  · exact B1035035
  · exact B1035039
  · exact B1035043
  · exact B1035047
  · exact B1035051
  · exact B1035055
  · exact B1035059
  · exact B1035063
  · exact B1035067
  · exact B1035071
  · exact B1035075
  · exact B1035079
  · exact B1035083
  · exact B1035087
  · exact B1035091
  · exact B1035095
  · exact B1035099
  · exact B1035103
  · exact B1035107
  · exact B1035111
  · exact B1035115
  · exact B1035119
  · exact B1035123
  · exact B1035127
  · exact B1035131
  · exact B1035135
  · exact B1035139
  · exact B1035143
  · exact B1035147
  · exact B1035151
  · exact B1035155
  · exact B1035159
  · exact B1035163
  · exact B1035167
  · exact B1035171
  · exact B1035175
  · exact B1035179
  · exact B1035183
  · exact B1035187
  · exact B1035191
  · exact B1035195
  · exact B1035199
  · exact B1035203
  · exact B1035207
  · exact B1035211
  · exact B1035215
  · exact B1035219
  · exact B1035223
  · exact B1035227
  · exact B1035231
  · exact B1035235
  · exact B1035239
  · exact B1035243
  · exact B1035247
  · exact B1035251
  · exact B1035255
  · exact B1035259
  · exact B1035263
  · exact B1035267
  · exact B1035271
  · exact B1035275
  · exact B1035279
  · exact B1035283
  · exact B1035287
  · exact B1035291
  · exact B1035295
  · exact B1035299
  · exact B1035303
  · exact B1035307
  · exact B1035311
  · exact B1035315
  · exact B1035319
  · exact B1035323
  · exact B1035327
  · exact B1035331
  · exact B1035335
  · exact B1035339
  · exact B1035343
  · exact B1035347
  · exact B1035351
  · exact B1035355
  · exact B1035359
  · exact B1035363
  · exact B1035367
  · exact B1035371
  · exact B1035375
  · exact B1035379
  · exact B1035383
  · exact B1035387
  · exact B1035391
  · exact B1035395
  · exact B1035399
  · exact B1035403

theorem C1 (j : ℕ) (h1 : 258851 ≤ j) (h2 : j ≤ 259151) : Blo 1032607 (4 * j + 3) := by
  interval_cases j
  · exact B1035407
  · exact B1035411
  · exact B1035415
  · exact B1035419
  · exact B1035423
  · exact B1035427
  · exact B1035431
  · exact B1035435
  · exact B1035439
  · exact B1035443
  · exact B1035447
  · exact B1035451
  · exact B1035455
  · exact B1035459
  · exact B1035463
  · exact B1035467
  · exact B1035471
  · exact B1035475
  · exact B1035479
  · exact B1035483
  · exact B1035487
  · exact B1035491
  · exact B1035495
  · exact B1035499
  · exact B1035503
  · exact B1035507
  · exact B1035511
  · exact B1035515
  · exact B1035519
  · exact B1035523
  · exact B1035527
  · exact B1035531
  · exact B1035535
  · exact B1035539
  · exact B1035543
  · exact B1035547
  · exact B1035551
  · exact B1035555
  · exact B1035559
  · exact B1035563
  · exact B1035567
  · exact B1035571
  · exact B1035575
  · exact B1035579
  · exact B1035583
  · exact B1035587
  · exact B1035591
  · exact B1035595
  · exact B1035599
  · exact B1035603
  · exact B1035607
  · exact B1035611
  · exact B1035615
  · exact B1035619
  · exact B1035623
  · exact B1035627
  · exact B1035631
  · exact B1035635
  · exact B1035639
  · exact B1035643
  · exact B1035647
  · exact B1035651
  · exact B1035655
  · exact B1035659
  · exact B1035663
  · exact B1035667
  · exact B1035671
  · exact B1035675
  · exact B1035679
  · exact B1035683
  · exact B1035687
  · exact B1035691
  · exact B1035695
  · exact B1035699
  · exact B1035703
  · exact B1035707
  · exact B1035711
  · exact B1035715
  · exact B1035719
  · exact B1035723
  · exact B1035727
  · exact B1035731
  · exact B1035735
  · exact B1035739
  · exact B1035743
  · exact B1035747
  · exact B1035751
  · exact B1035755
  · exact B1035759
  · exact B1035763
  · exact B1035767
  · exact B1035771
  · exact B1035775
  · exact B1035779
  · exact B1035783
  · exact B1035787
  · exact B1035791
  · exact B1035795
  · exact B1035799
  · exact B1035803
  · exact B1035807
  · exact B1035811
  · exact B1035815
  · exact B1035819
  · exact B1035823
  · exact B1035827
  · exact B1035831
  · exact B1035835
  · exact B1035839
  · exact B1035843
  · exact B1035847
  · exact B1035851
  · exact B1035855
  · exact B1035859
  · exact B1035863
  · exact B1035867
  · exact B1035871
  · exact B1035875
  · exact B1035879
  · exact B1035883
  · exact B1035887
  · exact B1035891
  · exact B1035895
  · exact B1035899
  · exact B1035903
  · exact B1035907
  · exact B1035911
  · exact B1035915
  · exact B1035919
  · exact B1035923
  · exact B1035927
  · exact B1035931
  · exact B1035935
  · exact B1035939
  · exact B1035943
  · exact B1035947
  · exact B1035951
  · exact B1035955
  · exact B1035959
  · exact B1035963
  · exact B1035967
  · exact B1035971
  · exact B1035975
  · exact B1035979
  · exact B1035983
  · exact B1035987
  · exact B1035991
  · exact B1035995
  · exact B1035999
  · exact B1036003
  · exact B1036007
  · exact B1036011
  · exact B1036015
  · exact B1036019
  · exact B1036023
  · exact B1036027
  · exact B1036031
  · exact B1036035
  · exact B1036039
  · exact B1036043
  · exact B1036047
  · exact B1036051
  · exact B1036055
  · exact B1036059
  · exact B1036063
  · exact B1036067
  · exact B1036071
  · exact B1036075
  · exact B1036079
  · exact B1036083
  · exact B1036087
  · exact B1036091
  · exact B1036095
  · exact B1036099
  · exact B1036103
  · exact B1036107
  · exact B1036111
  · exact B1036115
  · exact B1036119
  · exact B1036123
  · exact B1036127
  · exact B1036131
  · exact B1036135
  · exact B1036139
  · exact B1036143
  · exact B1036147
  · exact B1036151
  · exact B1036155
  · exact B1036159
  · exact B1036163
  · exact B1036167
  · exact B1036171
  · exact B1036175
  · exact B1036179
  · exact B1036183
  · exact B1036187
  · exact B1036191
  · exact B1036195
  · exact B1036199
  · exact B1036203
  · exact B1036207
  · exact B1036211
  · exact B1036215
  · exact B1036219
  · exact B1036223
  · exact B1036227
  · exact B1036231
  · exact B1036235
  · exact B1036239
  · exact B1036243
  · exact B1036247
  · exact B1036251
  · exact B1036255
  · exact B1036259
  · exact B1036263
  · exact B1036267
  · exact B1036271
  · exact B1036275
  · exact B1036279
  · exact B1036283
  · exact B1036287
  · exact B1036291
  · exact B1036295
  · exact B1036299
  · exact B1036303
  · exact B1036307
  · exact B1036311
  · exact B1036315
  · exact B1036319
  · exact B1036323
  · exact B1036327
  · exact B1036331
  · exact B1036335
  · exact B1036339
  · exact B1036343
  · exact B1036347
  · exact B1036351
  · exact B1036355
  · exact B1036359
  · exact B1036363
  · exact B1036367
  · exact B1036371
  · exact B1036375
  · exact B1036379
  · exact B1036383
  · exact B1036387
  · exact B1036391
  · exact B1036395
  · exact B1036399
  · exact B1036403
  · exact B1036407
  · exact B1036411
  · exact B1036415
  · exact B1036419
  · exact B1036423
  · exact B1036427
  · exact B1036431
  · exact B1036435
  · exact B1036439
  · exact B1036443
  · exact B1036447
  · exact B1036451
  · exact B1036455
  · exact B1036459
  · exact B1036463
  · exact B1036467
  · exact B1036471
  · exact B1036475
  · exact B1036479
  · exact B1036483
  · exact B1036487
  · exact B1036491
  · exact B1036495
  · exact B1036499
  · exact B1036503
  · exact B1036507
  · exact B1036511
  · exact B1036515
  · exact B1036519
  · exact B1036523
  · exact B1036527
  · exact B1036531
  · exact B1036535
  · exact B1036539
  · exact B1036543
  · exact B1036547
  · exact B1036551
  · exact B1036555
  · exact B1036559
  · exact B1036563
  · exact B1036567
  · exact B1036571
  · exact B1036575
  · exact B1036579
  · exact B1036583
  · exact B1036587
  · exact B1036591
  · exact B1036595
  · exact B1036599
  · exact B1036603
  · exact B1036607

theorem solution (m : ℕ) (hlo : 1032607 ≤ m) (hhi : m ≤ 1036607) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 258151 ≤ j := by omega
    have hj2 : j ≤ 259151 := by omega
    have hb : Blo 1032607 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 258851 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
