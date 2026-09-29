-- Prove2me | solution 1 for syracuse_descends_range_1490065_1492065
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:46:44.845237+00:00
-- url     : https://prove2.me/submissions/a3a7018f-321c-48c7-95a0-48ef9cc541fe

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


theorem B2236421 : Blo 1490065 2236421 := bbase (se 4 (by rfl) ⟨209664, by rfl⟩ : syracuseStep 2236421 = 419329) (by norm_num)
theorem B2236445 : Blo 1490065 2236445 := bbase (se 3 (by rfl) ⟨419333, by rfl⟩ : syracuseStep 2236445 = 838667) (by norm_num)
theorem B2514989 : Blo 1490065 2514989 := bbase (se 3 (by rfl) ⟨471560, by rfl⟩ : syracuseStep 2514989 = 943121) (by norm_num)
theorem B2236469 : Blo 1490065 2236469 := bbase (se 5 (by rfl) ⟨104834, by rfl⟩ : syracuseStep 2236469 = 209669) (by norm_num)
theorem B2236493 : Blo 1490065 2236493 := bbase (se 3 (by rfl) ⟨419342, by rfl⟩ : syracuseStep 2236493 = 838685) (by norm_num)
theorem B2236517 : Blo 1490065 2236517 := bbase (se 4 (by rfl) ⟨209673, by rfl⟩ : syracuseStep 2236517 = 419347) (by norm_num)
theorem B2236541 : Blo 1490065 2236541 := bbase (se 3 (by rfl) ⟨419351, by rfl⟩ : syracuseStep 2236541 = 838703) (by norm_num)
theorem B3776645 : Blo 1490065 3776645 := bbase (se 4 (by rfl) ⟨354060, by rfl⟩ : syracuseStep 3776645 = 708121) (by norm_num)
theorem B2236565 : Blo 1490065 2236565 := bbase (se 6 (by rfl) ⟨52419, by rfl⟩ : syracuseStep 2236565 = 104839) (by norm_num)
theorem B2015389 : Blo 1490065 2015389 := bbase (se 3 (by rfl) ⟨377885, by rfl⟩ : syracuseStep 2015389 = 755771) (by norm_num)
theorem B4776101 : Blo 1490065 4776101 := bbase (se 4 (by rfl) ⟨447759, by rfl⟩ : syracuseStep 4776101 = 895519) (by norm_num)
theorem B5660837 : Blo 1490065 5660837 := bbase (se 4 (by rfl) ⟨530703, by rfl⟩ : syracuseStep 5660837 = 1061407) (by norm_num)
theorem B4087973 : Blo 1490065 4087973 := bbase (se 4 (by rfl) ⟨383247, by rfl⟩ : syracuseStep 4087973 = 766495) (by norm_num)
theorem B2515117 : Blo 1490065 2515117 := bbase (se 3 (by rfl) ⟨471584, by rfl⟩ : syracuseStep 2515117 = 943169) (by norm_num)
theorem B2236589 : Blo 1490065 2236589 := bbase (se 3 (by rfl) ⟨419360, by rfl⟩ : syracuseStep 2236589 = 838721) (by norm_num)
theorem B2236613 : Blo 1490065 2236613 := bbase (se 4 (by rfl) ⟨209682, by rfl⟩ : syracuseStep 2236613 = 419365) (by norm_num)
theorem B30613717 : Blo 1490065 30613717 := bbase (se 7 (by rfl) ⟨358754, by rfl⟩ : syracuseStep 30613717 = 717509) (by norm_num)
theorem B2236637 : Blo 1490065 2236637 := bbase (se 3 (by rfl) ⟨419369, by rfl⟩ : syracuseStep 2236637 = 838739) (by norm_num)
theorem B2236661 : Blo 1490065 2236661 := bbase (se 5 (by rfl) ⟨104843, by rfl⟩ : syracuseStep 2236661 = 209687) (by norm_num)
theorem B2515205 : Blo 1490065 2515205 := bbase (se 4 (by rfl) ⟨235800, by rfl⟩ : syracuseStep 2515205 = 471601) (by norm_num)
theorem B2236685 : Blo 1490065 2236685 := bbase (se 3 (by rfl) ⟨419378, by rfl⟩ : syracuseStep 2236685 = 838757) (by norm_num)
theorem B2236709 : Blo 1490065 2236709 := bbase (se 4 (by rfl) ⟨209691, by rfl⟩ : syracuseStep 2236709 = 419383) (by norm_num)
theorem B2236733 : Blo 1490065 2236733 := bbase (se 3 (by rfl) ⟨419387, by rfl⟩ : syracuseStep 2236733 = 838775) (by norm_num)
theorem B2236757 : Blo 1490065 2236757 := bbase (se 10 (by rfl) ⟨3276, by rfl⟩ : syracuseStep 2236757 = 6553) (by norm_num)
theorem B2122085 : Blo 1490065 2122085 := bbase (se 4 (by rfl) ⟨198945, by rfl⟩ : syracuseStep 2122085 = 397891) (by norm_num)
theorem B2236781 : Blo 1490065 2236781 := bbase (se 3 (by rfl) ⟨419396, by rfl⟩ : syracuseStep 2236781 = 838793) (by norm_num)
theorem B5030261 : Blo 1490065 5030261 := bbase (se 5 (by rfl) ⟨235793, by rfl⟩ : syracuseStep 5030261 = 471587) (by norm_num)
theorem B5374325 : Blo 1490065 5374325 := bbase (se 5 (by rfl) ⟨251921, by rfl⟩ : syracuseStep 5374325 = 503843) (by norm_num)
theorem B6365573 : Blo 1490065 6365573 := bbase (se 4 (by rfl) ⟨596772, by rfl⟩ : syracuseStep 6365573 = 1193545) (by norm_num)
theorem B2515333 : Blo 1490065 2515333 := bbase (se 4 (by rfl) ⟨235812, by rfl⟩ : syracuseStep 2515333 = 471625) (by norm_num)
theorem B2236805 : Blo 1490065 2236805 := bbase (se 4 (by rfl) ⟨209700, by rfl⟩ : syracuseStep 2236805 = 419401) (by norm_num)
theorem B2236829 : Blo 1490065 2236829 := bbase (se 3 (by rfl) ⟨419405, by rfl⟩ : syracuseStep 2236829 = 838811) (by norm_num)
theorem B2015653 : Blo 1490065 2015653 := bbase (se 4 (by rfl) ⟨188967, by rfl⟩ : syracuseStep 2015653 = 377935) (by norm_num)
theorem B2236853 : Blo 1490065 2236853 := bbase (se 5 (by rfl) ⟨104852, by rfl⟩ : syracuseStep 2236853 = 209705) (by norm_num)
theorem B2236877 : Blo 1490065 2236877 := bbase (se 3 (by rfl) ⟨419414, by rfl⟩ : syracuseStep 2236877 = 838829) (by norm_num)
theorem B2515421 : Blo 1490065 2515421 := bbase (se 3 (by rfl) ⟨471641, by rfl⟩ : syracuseStep 2515421 = 943283) (by norm_num)
theorem B2236901 : Blo 1490065 2236901 := bbase (se 4 (by rfl) ⟨209709, by rfl⟩ : syracuseStep 2236901 = 419419) (by norm_num)
theorem B2236925 : Blo 1490065 2236925 := bbase (se 3 (by rfl) ⟨419423, by rfl⟩ : syracuseStep 2236925 = 838847) (by norm_num)
theorem B2236949 : Blo 1490065 2236949 := bbase (se 6 (by rfl) ⟨52428, by rfl⟩ : syracuseStep 2236949 = 104857) (by norm_num)
theorem B3580453 : Blo 1490065 3580453 := bbase (se 4 (by rfl) ⟨335667, by rfl⟩ : syracuseStep 3580453 = 671335) (by norm_num)
theorem B7553573 : Blo 1490065 7553573 := bbase (se 4 (by rfl) ⟨708147, by rfl⟩ : syracuseStep 7553573 = 1416295) (by norm_num)
theorem B2236973 : Blo 1490065 2236973 := bbase (se 3 (by rfl) ⟨419432, by rfl⟩ : syracuseStep 2236973 = 838865) (by norm_num)
theorem B3875381 : Blo 1490065 3875381 := bbase (se 5 (by rfl) ⟨181658, by rfl⟩ : syracuseStep 3875381 = 363317) (by norm_num)
theorem B2236997 : Blo 1490065 2236997 := bbase (se 4 (by rfl) ⟨209718, by rfl⟩ : syracuseStep 2236997 = 419437) (by norm_num)
theorem B2515549 : Blo 1490065 2515549 := bbase (se 3 (by rfl) ⟨471665, by rfl⟩ : syracuseStep 2515549 = 943331) (by norm_num)
theorem B2237021 : Blo 1490065 2237021 := bbase (se 3 (by rfl) ⟨419441, by rfl⟩ : syracuseStep 2237021 = 838883) (by norm_num)
theorem B2237045 : Blo 1490065 2237045 := bbase (se 5 (by rfl) ⟨104861, by rfl⟩ : syracuseStep 2237045 = 209723) (by norm_num)
theorem B2237069 : Blo 1490065 2237069 := bbase (se 3 (by rfl) ⟨419450, by rfl⟩ : syracuseStep 2237069 = 838901) (by norm_num)
theorem B5374613 : Blo 1490065 5374613 := bbase (se 6 (by rfl) ⟨125967, by rfl⟩ : syracuseStep 5374613 = 251935) (by norm_num)
theorem B2237093 : Blo 1490065 2237093 := bbase (se 4 (by rfl) ⟨209727, by rfl⟩ : syracuseStep 2237093 = 419455) (by norm_num)
theorem B7160501 : Blo 1490065 7160501 := bbase (se 5 (by rfl) ⟨335648, by rfl⟩ : syracuseStep 7160501 = 671297) (by norm_num)
theorem B2515637 : Blo 1490065 2515637 := bbase (se 5 (by rfl) ⟨117920, by rfl⟩ : syracuseStep 2515637 = 235841) (by norm_num)
theorem B2237117 : Blo 1490065 2237117 := bbase (se 3 (by rfl) ⟨419459, by rfl⟩ : syracuseStep 2237117 = 838919) (by norm_num)
theorem B2237141 : Blo 1490065 2237141 := bbase (se 7 (by rfl) ⟨26216, by rfl⟩ : syracuseStep 2237141 = 52433) (by norm_num)
theorem B1532629 : Blo 1490065 1532629 := bbase (se 7 (by rfl) ⟨17960, by rfl⟩ : syracuseStep 1532629 = 35921) (by norm_num)
theorem B2237165 : Blo 1490065 2237165 := bbase (se 3 (by rfl) ⟨419468, by rfl⟩ : syracuseStep 2237165 = 838937) (by norm_num)
theorem B13607669 : Blo 1490065 13607669 := bbase (se 5 (by rfl) ⟨637859, by rfl⟩ : syracuseStep 13607669 = 1275719) (by norm_num)
theorem B2237189 : Blo 1490065 2237189 := bbase (se 4 (by rfl) ⟨209736, by rfl⟩ : syracuseStep 2237189 = 419473) (by norm_num)
theorem B2237213 : Blo 1490065 2237213 := bbase (se 3 (by rfl) ⟨419477, by rfl⟩ : syracuseStep 2237213 = 838955) (by norm_num)
theorem B5030693 : Blo 1490065 5030693 := bbase (se 4 (by rfl) ⟨471627, by rfl⟩ : syracuseStep 5030693 = 943255) (by norm_num)
theorem B2515765 : Blo 1490065 2515765 := bbase (se 5 (by rfl) ⟨117926, by rfl⟩ : syracuseStep 2515765 = 235853) (by norm_num)
theorem B2237237 : Blo 1490065 2237237 := bbase (se 5 (by rfl) ⟨104870, by rfl⟩ : syracuseStep 2237237 = 209741) (by norm_num)
theorem B1614665 : Blo 1490065 1614665 := bbase (se 2 (by rfl) ⟨605499, by rfl⟩ : syracuseStep 1614665 = 1210999) (by norm_num)
theorem B2237261 : Blo 1490065 2237261 := bbase (se 3 (by rfl) ⟨419486, by rfl⟩ : syracuseStep 2237261 = 838973) (by norm_num)
theorem B2237285 : Blo 1490065 2237285 := bbase (se 4 (by rfl) ⟨209745, by rfl⟩ : syracuseStep 2237285 = 419491) (by norm_num)
theorem B2237309 : Blo 1490065 2237309 := bbase (se 3 (by rfl) ⟨419495, by rfl⟩ : syracuseStep 2237309 = 838991) (by norm_num)
theorem B2515853 : Blo 1490065 2515853 := bbase (se 3 (by rfl) ⟨471722, by rfl⟩ : syracuseStep 2515853 = 943445) (by norm_num)
theorem B2237333 : Blo 1490065 2237333 := bbase (se 6 (by rfl) ⟨52437, by rfl⟩ : syracuseStep 2237333 = 104875) (by norm_num)
theorem B2237357 : Blo 1490065 2237357 := bbase (se 3 (by rfl) ⟨419504, by rfl⟩ : syracuseStep 2237357 = 839009) (by norm_num)
theorem B7545797 : Blo 1490065 7545797 := bbase (se 4 (by rfl) ⟨707418, by rfl⟩ : syracuseStep 7545797 = 1414837) (by norm_num)
theorem B2237381 : Blo 1490065 2237381 := bbase (se 4 (by rfl) ⟨209754, by rfl⟩ : syracuseStep 2237381 = 419509) (by norm_num)
theorem B2687941 : Blo 1490065 2687941 := bbase (se 4 (by rfl) ⟨251994, by rfl⟩ : syracuseStep 2687941 = 503989) (by norm_num)
theorem B3146701 : Blo 1490065 3146701 := bbase (se 3 (by rfl) ⟨590006, by rfl⟩ : syracuseStep 3146701 = 1180013) (by norm_num)
theorem B2237405 : Blo 1490065 2237405 := bbase (se 3 (by rfl) ⟨419513, by rfl⟩ : syracuseStep 2237405 = 839027) (by norm_num)
theorem B2237429 : Blo 1490065 2237429 := bbase (se 5 (by rfl) ⟨104879, by rfl⟩ : syracuseStep 2237429 = 209759) (by norm_num)
theorem B2515981 : Blo 1490065 2515981 := bbase (se 3 (by rfl) ⟨471746, by rfl⟩ : syracuseStep 2515981 = 943493) (by norm_num)
theorem B2237453 : Blo 1490065 2237453 := bbase (se 3 (by rfl) ⟨419522, by rfl⟩ : syracuseStep 2237453 = 839045) (by norm_num)
theorem B4244501 : Blo 1490065 4244501 := bbase (se 6 (by rfl) ⟨99480, by rfl⟩ : syracuseStep 4244501 = 198961) (by norm_num)
theorem B2237477 : Blo 1490065 2237477 := bbase (se 4 (by rfl) ⟨209763, by rfl⟩ : syracuseStep 2237477 = 419527) (by norm_num)
theorem B2237501 : Blo 1490065 2237501 := bbase (se 3 (by rfl) ⟨419531, by rfl⟩ : syracuseStep 2237501 = 839063) (by norm_num)
theorem B2237525 : Blo 1490065 2237525 := bbase (se 8 (by rfl) ⟨13110, by rfl⟩ : syracuseStep 2237525 = 26221) (by norm_num)
theorem B2688085 : Blo 1490065 2688085 := bbase (se 8 (by rfl) ⟨15750, by rfl⟩ : syracuseStep 2688085 = 31501) (by norm_num)
theorem B2516069 : Blo 1490065 2516069 := bbase (se 4 (by rfl) ⟨235881, by rfl⟩ : syracuseStep 2516069 = 471763) (by norm_num)
theorem B2237549 : Blo 1490065 2237549 := bbase (se 3 (by rfl) ⟨419540, by rfl⟩ : syracuseStep 2237549 = 839081) (by norm_num)
theorem B2237573 : Blo 1490065 2237573 := bbase (se 4 (by rfl) ⟨209772, by rfl⟩ : syracuseStep 2237573 = 419545) (by norm_num)
theorem B2237597 : Blo 1490065 2237597 := bbase (se 3 (by rfl) ⟨419549, by rfl⟩ : syracuseStep 2237597 = 839099) (by norm_num)
theorem B2237621 : Blo 1490065 2237621 := bbase (se 5 (by rfl) ⟨104888, by rfl⟩ : syracuseStep 2237621 = 209777) (by norm_num)
theorem B2237645 : Blo 1490065 2237645 := bbase (se 3 (by rfl) ⟨419558, by rfl⟩ : syracuseStep 2237645 = 839117) (by norm_num)
theorem B5031125 : Blo 1490065 5031125 := bbase (se 7 (by rfl) ⟨58958, by rfl⟩ : syracuseStep 5031125 = 117917) (by norm_num)
theorem B2516197 : Blo 1490065 2516197 := bbase (se 4 (by rfl) ⟨235893, by rfl⟩ : syracuseStep 2516197 = 471787) (by norm_num)
theorem B2237669 : Blo 1490065 2237669 := bbase (se 4 (by rfl) ⟨209781, by rfl⟩ : syracuseStep 2237669 = 419563) (by norm_num)
theorem B2688245 : Blo 1490065 2688245 := bbase (se 5 (by rfl) ⟨126011, by rfl⟩ : syracuseStep 2688245 = 252023) (by norm_num)
theorem B2237693 : Blo 1490065 2237693 := bbase (se 3 (by rfl) ⟨419567, by rfl⟩ : syracuseStep 2237693 = 839135) (by norm_num)
theorem B2237717 : Blo 1490065 2237717 := bbase (se 6 (by rfl) ⟨52446, by rfl⟩ : syracuseStep 2237717 = 104893) (by norm_num)
theorem B2237741 : Blo 1490065 2237741 := bbase (se 3 (by rfl) ⟨419576, by rfl⟩ : syracuseStep 2237741 = 839153) (by norm_num)
theorem B2516285 : Blo 1490065 2516285 := bbase (se 3 (by rfl) ⟨471803, by rfl⟩ : syracuseStep 2516285 = 943607) (by norm_num)
theorem B5662021 : Blo 1490065 5662021 := bbase (se 4 (by rfl) ⟨530814, by rfl⟩ : syracuseStep 5662021 = 1061629) (by norm_num)
theorem B2237765 : Blo 1490065 2237765 := bbase (se 4 (by rfl) ⟨209790, by rfl⟩ : syracuseStep 2237765 = 419581) (by norm_num)
theorem B2237789 : Blo 1490065 2237789 := bbase (se 3 (by rfl) ⟨419585, by rfl⟩ : syracuseStep 2237789 = 839171) (by norm_num)
theorem B7169381 : Blo 1490065 7169381 := bbase (se 4 (by rfl) ⟨672129, by rfl⟩ : syracuseStep 7169381 = 1344259) (by norm_num)
theorem B2237813 : Blo 1490065 2237813 := bbase (se 5 (by rfl) ⟨104897, by rfl⟩ : syracuseStep 2237813 = 209795) (by norm_num)
theorem B6800773 : Blo 1490065 6800773 := bbase (se 4 (by rfl) ⟨637572, by rfl⟩ : syracuseStep 6800773 = 1275145) (by norm_num)
theorem B2237837 : Blo 1490065 2237837 := bbase (se 3 (by rfl) ⟨419594, by rfl⟩ : syracuseStep 2237837 = 839189) (by norm_num)
theorem B25478549 : Blo 1490065 25478549 := bbase (se 6 (by rfl) ⟨597153, by rfl⟩ : syracuseStep 25478549 = 1194307) (by norm_num)
theorem B2237861 : Blo 1490065 2237861 := bbase (se 4 (by rfl) ⟨209799, by rfl⟩ : syracuseStep 2237861 = 419599) (by norm_num)
theorem B2516413 : Blo 1490065 2516413 := bbase (se 3 (by rfl) ⟨471827, by rfl⟩ : syracuseStep 2516413 = 943655) (by norm_num)
theorem B3024317 : Blo 1490065 3024317 := bbase (se 3 (by rfl) ⟨567059, by rfl⟩ : syracuseStep 3024317 = 1134119) (by norm_num)
theorem B2237885 : Blo 1490065 2237885 := bbase (se 3 (by rfl) ⟨419603, by rfl⟩ : syracuseStep 2237885 = 839207) (by norm_num)
theorem B2237909 : Blo 1490065 2237909 := bbase (se 7 (by rfl) ⟨26225, by rfl⟩ : syracuseStep 2237909 = 52451) (by norm_num)
theorem B2237933 : Blo 1490065 2237933 := bbase (se 3 (by rfl) ⟨419612, by rfl⟩ : syracuseStep 2237933 = 839225) (by norm_num)
theorem B4531717 : Blo 1490065 4531717 := bbase (se 4 (by rfl) ⟨424848, by rfl⟩ : syracuseStep 4531717 = 849697) (by norm_num)
theorem B2237957 : Blo 1490065 2237957 := bbase (se 4 (by rfl) ⟨209808, by rfl⟩ : syracuseStep 2237957 = 419617) (by norm_num)
theorem B2041357 : Blo 1490065 2041357 := bbase (se 3 (by rfl) ⟨382754, by rfl⟩ : syracuseStep 2041357 = 765509) (by norm_num)
theorem B2516501 : Blo 1490065 2516501 := bbase (se 6 (by rfl) ⟨58980, by rfl⟩ : syracuseStep 2516501 = 117961) (by norm_num)
theorem B2237981 : Blo 1490065 2237981 := bbase (se 3 (by rfl) ⟨419621, by rfl⟩ : syracuseStep 2237981 = 839243) (by norm_num)
theorem B2238005 : Blo 1490065 2238005 := bbase (se 5 (by rfl) ⟨104906, by rfl⟩ : syracuseStep 2238005 = 209813) (by norm_num)
theorem B2238029 : Blo 1490065 2238029 := bbase (se 3 (by rfl) ⟨419630, by rfl⟩ : syracuseStep 2238029 = 839261) (by norm_num)
theorem B2238053 : Blo 1490065 2238053 := bbase (se 4 (by rfl) ⟨209817, by rfl⟩ : syracuseStep 2238053 = 419635) (by norm_num)
theorem B5662325 : Blo 1490065 5662325 := bbase (se 5 (by rfl) ⟨265421, by rfl⟩ : syracuseStep 5662325 = 530843) (by norm_num)
theorem B2238077 : Blo 1490065 2238077 := bbase (se 3 (by rfl) ⟨419639, by rfl⟩ : syracuseStep 2238077 = 839279) (by norm_num)
theorem B5031557 : Blo 1490065 5031557 := bbase (se 4 (by rfl) ⟨471708, by rfl⟩ : syracuseStep 5031557 = 943417) (by norm_num)
theorem B2516629 : Blo 1490065 2516629 := bbase (se 6 (by rfl) ⟨58983, by rfl⟩ : syracuseStep 2516629 = 117967) (by norm_num)
theorem B4245173 : Blo 1490065 4245173 := bbase (se 5 (by rfl) ⟨198992, by rfl⟩ : syracuseStep 4245173 = 397985) (by norm_num)
theorem B3581653 : Blo 1490065 3581653 := bbase (se 7 (by rfl) ⟨41972, by rfl⟩ : syracuseStep 3581653 = 83945) (by norm_num)
theorem B1885933 : Blo 1490065 1885933 := bbase (se 3 (by rfl) ⟨353612, by rfl⟩ : syracuseStep 1885933 = 707225) (by norm_num)
theorem B2516717 : Blo 1490065 2516717 := bbase (se 3 (by rfl) ⟨471884, by rfl⟩ : syracuseStep 2516717 = 943769) (by norm_num)
theorem B2123509 : Blo 1490065 2123509 := bbase (se 5 (by rfl) ⟨99539, by rfl⟩ : syracuseStep 2123509 = 199079) (by norm_num)
theorem B2516845 : Blo 1490065 2516845 := bbase (se 3 (by rfl) ⟨471908, by rfl⟩ : syracuseStep 2516845 = 943817) (by norm_num)
theorem B4843397 : Blo 1490065 4843397 := bbase (se 4 (by rfl) ⟨454068, by rfl⟩ : syracuseStep 4843397 = 908137) (by norm_num)
theorem B1886105 : Blo 1490065 1886105 := bbase (se 2 (by rfl) ⟨707289, by rfl⟩ : syracuseStep 1886105 = 1414579) (by norm_num)
theorem B2516933 : Blo 1490065 2516933 := bbase (se 4 (by rfl) ⟨235962, by rfl⟩ : syracuseStep 2516933 = 471925) (by norm_num)
theorem B1886161 : Blo 1490065 1886161 := bbase (se 2 (by rfl) ⟨707310, by rfl⟩ : syracuseStep 1886161 = 1414621) (by norm_num)
theorem B1591265 : Blo 1490065 1591265 := bbase (se 2 (by rfl) ⟨596724, by rfl⟩ : syracuseStep 1591265 = 1193449) (by norm_num)
theorem B4777973 : Blo 1490065 4777973 := bbase (se 5 (by rfl) ⟨223967, by rfl⟩ : syracuseStep 4777973 = 447935) (by norm_num)
theorem B4032517 : Blo 1490065 4032517 := bbase (se 4 (by rfl) ⟨378048, by rfl⟩ : syracuseStep 4032517 = 756097) (by norm_num)
theorem B1886257 : Blo 1490065 1886257 := bbase (se 2 (by rfl) ⟨707346, by rfl⟩ : syracuseStep 1886257 = 1414693) (by norm_num)
theorem B5031989 : Blo 1490065 5031989 := bbase (se 5 (by rfl) ⟨235874, by rfl⟩ : syracuseStep 5031989 = 471749) (by norm_num)
theorem B2517061 : Blo 1490065 2517061 := bbase (se 4 (by rfl) ⟨235974, by rfl⟩ : syracuseStep 2517061 = 471949) (by norm_num)
theorem B3352661 : Blo 1490065 3352661 := bbase (se 8 (by rfl) ⟨19644, by rfl⟩ : syracuseStep 3352661 = 39289) (by norm_num)
theorem B4245605 : Blo 1490065 4245605 := bbase (se 4 (by rfl) ⟨398025, by rfl⟩ : syracuseStep 4245605 = 796051) (by norm_num)
theorem B6367349 : Blo 1490065 6367349 := bbase (se 5 (by rfl) ⟨298469, by rfl⟩ : syracuseStep 6367349 = 596939) (by norm_num)
theorem B20400277 : Blo 1490065 20400277 := bbase (se 6 (by rfl) ⟨478131, by rfl⟩ : syracuseStep 20400277 = 956263) (by norm_num)
theorem B3352733 : Blo 1490065 3352733 := bbase (se 3 (by rfl) ⟨628637, by rfl⟩ : syracuseStep 3352733 = 1257275) (by norm_num)
theorem B2517149 : Blo 1490065 2517149 := bbase (se 3 (by rfl) ⟨471965, by rfl⟩ : syracuseStep 2517149 = 943931) (by norm_num)
theorem B7547093 : Blo 1490065 7547093 := bbase (se 7 (by rfl) ⟨88442, by rfl⟩ : syracuseStep 7547093 = 176885) (by norm_num)
theorem B1886429 : Blo 1490065 1886429 := bbase (se 3 (by rfl) ⟨353705, by rfl⟩ : syracuseStep 1886429 = 707411) (by norm_num)
theorem B3352805 : Blo 1490065 3352805 := bbase (se 4 (by rfl) ⟨314325, by rfl⟩ : syracuseStep 3352805 = 628651) (by norm_num)
theorem B1886485 : Blo 1490065 1886485 := bbase (se 6 (by rfl) ⟨44214, by rfl⟩ : syracuseStep 1886485 = 88429) (by norm_num)
theorem B2517277 : Blo 1490065 2517277 := bbase (se 3 (by rfl) ⟨471989, by rfl⟩ : syracuseStep 2517277 = 943979) (by norm_num)
theorem B3352877 : Blo 1490065 3352877 := bbase (se 3 (by rfl) ⟨628664, by rfl⟩ : syracuseStep 3352877 = 1257329) (by norm_num)
theorem B4032821 : Blo 1490065 4032821 := bbase (se 5 (by rfl) ⟨189038, by rfl⟩ : syracuseStep 4032821 = 378077) (by norm_num)
theorem B3582269 : Blo 1490065 3582269 := bbase (se 3 (by rfl) ⟨671675, by rfl⟩ : syracuseStep 3582269 = 1343351) (by norm_num)
theorem B2124101 : Blo 1490065 2124101 := bbase (se 4 (by rfl) ⟨199134, by rfl⟩ : syracuseStep 2124101 = 398269) (by norm_num)
theorem B3352949 : Blo 1490065 3352949 := bbase (se 5 (by rfl) ⟨157169, by rfl⟩ : syracuseStep 3352949 = 314339) (by norm_num)
theorem B1886581 : Blo 1490065 1886581 := bbase (se 5 (by rfl) ⟨88433, by rfl⟩ : syracuseStep 1886581 = 176867) (by norm_num)
theorem B2517365 : Blo 1490065 2517365 := bbase (se 5 (by rfl) ⟨118001, by rfl⟩ : syracuseStep 2517365 = 236003) (by norm_num)
theorem B2124181 : Blo 1490065 2124181 := bbase (se 6 (by rfl) ⟨49785, by rfl⟩ : syracuseStep 2124181 = 99571) (by norm_num)
theorem B1591709 : Blo 1490065 1591709 := bbase (se 3 (by rfl) ⟨298445, by rfl⟩ : syracuseStep 1591709 = 596891) (by norm_num)
theorem B3353021 : Blo 1490065 3353021 := bbase (se 3 (by rfl) ⟨628691, by rfl⟩ : syracuseStep 3353021 = 1257383) (by norm_num)
theorem B3631565 : Blo 1490065 3631565 := bbase (se 3 (by rfl) ⟨680918, by rfl⟩ : syracuseStep 3631565 = 1361837) (by norm_num)
theorem B1591769 : Blo 1490065 1591769 := bbase (se 2 (by rfl) ⟨596913, by rfl⟩ : syracuseStep 1591769 = 1193827) (by norm_num)
theorem B5032421 : Blo 1490065 5032421 := bbase (se 4 (by rfl) ⟨471789, by rfl⟩ : syracuseStep 5032421 = 943579) (by norm_num)
theorem B2517493 : Blo 1490065 2517493 := bbase (se 5 (by rfl) ⟨118007, by rfl⟩ : syracuseStep 2517493 = 236015) (by norm_num)
theorem B3582461 : Blo 1490065 3582461 := bbase (se 3 (by rfl) ⟨671711, by rfl⟩ : syracuseStep 3582461 = 1343423) (by norm_num)
theorem B3353093 : Blo 1490065 3353093 := bbase (se 4 (by rfl) ⟨314352, by rfl⟩ : syracuseStep 3353093 = 628705) (by norm_num)
theorem B2124301 : Blo 1490065 2124301 := bbase (se 3 (by rfl) ⟨398306, by rfl⟩ : syracuseStep 2124301 = 796613) (by norm_num)
theorem B1886753 : Blo 1490065 1886753 := bbase (se 2 (by rfl) ⟨707532, by rfl⟩ : syracuseStep 1886753 = 1415065) (by norm_num)
theorem B4033061 : Blo 1490065 4033061 := bbase (se 4 (by rfl) ⟨378099, by rfl⟩ : syracuseStep 4033061 = 756199) (by norm_num)
theorem B3353165 : Blo 1490065 3353165 := bbase (se 3 (by rfl) ⟨628718, by rfl⟩ : syracuseStep 3353165 = 1257437) (by norm_num)
theorem B2517581 : Blo 1490065 2517581 := bbase (se 3 (by rfl) ⟨472046, by rfl⟩ : syracuseStep 2517581 = 944093) (by norm_num)
theorem B1591897 : Blo 1490065 1591897 := bbase (se 2 (by rfl) ⟨596961, by rfl⟩ : syracuseStep 1591897 = 1193923) (by norm_num)
theorem B1886809 : Blo 1490065 1886809 := bbase (se 2 (by rfl) ⟨707553, by rfl⟩ : syracuseStep 1886809 = 1415107) (by norm_num)
theorem B3582557 : Blo 1490065 3582557 := bbase (se 3 (by rfl) ⟨671729, by rfl⟩ : syracuseStep 3582557 = 1343459) (by norm_num)
theorem B2124397 : Blo 1490065 2124397 := bbase (se 3 (by rfl) ⟨398324, by rfl⟩ : syracuseStep 2124397 = 796649) (by norm_num)
theorem B3353237 : Blo 1490065 3353237 := bbase (se 6 (by rfl) ⟨78591, by rfl⟩ : syracuseStep 3353237 = 157183) (by norm_num)
theorem B4532885 : Blo 1490065 4532885 := bbase (se 6 (by rfl) ⟨106239, by rfl⟩ : syracuseStep 4532885 = 212479) (by norm_num)
theorem B1886905 : Blo 1490065 1886905 := bbase (se 2 (by rfl) ⟨707589, by rfl⟩ : syracuseStep 1886905 = 1415179) (by norm_num)
theorem B2517709 : Blo 1490065 2517709 := bbase (se 3 (by rfl) ⟨472070, by rfl⟩ : syracuseStep 2517709 = 944141) (by norm_num)
theorem B3353309 : Blo 1490065 3353309 := bbase (se 3 (by rfl) ⟨628745, by rfl⟩ : syracuseStep 3353309 = 1257491) (by norm_num)
theorem B3353381 : Blo 1490065 3353381 := bbase (se 4 (by rfl) ⟨314379, by rfl⟩ : syracuseStep 3353381 = 628759) (by norm_num)
theorem B2517797 : Blo 1490065 2517797 := bbase (se 4 (by rfl) ⟨236043, by rfl⟩ : syracuseStep 2517797 = 472087) (by norm_num)
theorem B2042693 : Blo 1490065 2042693 := bbase (se 4 (by rfl) ⟨191502, by rfl⟩ : syracuseStep 2042693 = 383005) (by norm_num)
theorem B4246357 : Blo 1490065 4246357 := bbase (se 9 (by rfl) ⟨12440, by rfl⟩ : syracuseStep 4246357 = 24881) (by norm_num)
theorem B1887077 : Blo 1490065 1887077 := bbase (se 4 (by rfl) ⟨176913, by rfl⟩ : syracuseStep 1887077 = 353827) (by norm_num)
theorem B3353453 : Blo 1490065 3353453 := bbase (se 3 (by rfl) ⟨628772, by rfl⟩ : syracuseStep 3353453 = 1257545) (by norm_num)
theorem B2829181 : Blo 1490065 2829181 := bbase (se 3 (by rfl) ⟨530471, by rfl⟩ : syracuseStep 2829181 = 1060943) (by norm_num)
theorem B5032853 : Blo 1490065 5032853 := bbase (se 6 (by rfl) ⟨117957, by rfl⟩ : syracuseStep 5032853 = 235915) (by norm_num)
theorem B1887133 : Blo 1490065 1887133 := bbase (se 3 (by rfl) ⟨353837, by rfl⟩ : syracuseStep 1887133 = 707675) (by norm_num)
theorem B3353525 : Blo 1490065 3353525 := bbase (se 5 (by rfl) ⟨157196, by rfl⟩ : syracuseStep 3353525 = 314393) (by norm_num)
theorem B9071605 : Blo 1490065 9071605 := bbase (se 5 (by rfl) ⟨425231, by rfl⟩ : syracuseStep 9071605 = 850463) (by norm_num)
theorem B3353597 : Blo 1490065 3353597 := bbase (se 3 (by rfl) ⟨628799, by rfl⟩ : syracuseStep 3353597 = 1257599) (by norm_num)
theorem B1887229 : Blo 1490065 1887229 := bbase (se 3 (by rfl) ⟨353855, by rfl⟩ : syracuseStep 1887229 = 707711) (by norm_num)
theorem B2829325 : Blo 1490065 2829325 := bbase (se 3 (by rfl) ⟨530498, by rfl⟩ : syracuseStep 2829325 = 1060997) (by norm_num)
theorem B1592341 : Blo 1490065 1592341 := bbase (se 6 (by rfl) ⟨37320, by rfl⟩ : syracuseStep 1592341 = 74641) (by norm_num)
theorem B5237797 : Blo 1490065 5237797 := bbase (se 4 (by rfl) ⟨491043, by rfl⟩ : syracuseStep 5237797 = 982087) (by norm_num)
theorem B3353669 : Blo 1490065 3353669 := bbase (se 4 (by rfl) ⟨314406, by rfl⟩ : syracuseStep 3353669 = 628813) (by norm_num)
theorem B2419853 : Blo 1490065 2419853 := bbase (se 3 (by rfl) ⟨453722, by rfl⟩ : syracuseStep 2419853 = 907445) (by norm_num)
theorem B3353741 : Blo 1490065 3353741 := bbase (se 3 (by rfl) ⟨628826, by rfl⟩ : syracuseStep 3353741 = 1257653) (by norm_num)
theorem B1592461 : Blo 1490065 1592461 := bbase (se 3 (by rfl) ⟨298586, by rfl⟩ : syracuseStep 1592461 = 597173) (by norm_num)
theorem B1887401 : Blo 1490065 1887401 := bbase (se 2 (by rfl) ⟨707775, by rfl⟩ : syracuseStep 1887401 = 1415551) (by norm_num)
theorem B2829485 : Blo 1490065 2829485 := bbase (se 3 (by rfl) ⟨530528, by rfl⟩ : syracuseStep 2829485 = 1061057) (by norm_num)
theorem B3353813 : Blo 1490065 3353813 := bbase (se 7 (by rfl) ⟨39302, by rfl⟩ : syracuseStep 3353813 = 78605) (by norm_num)
theorem B1887457 : Blo 1490065 1887457 := bbase (se 2 (by rfl) ⟨707796, by rfl⟩ : syracuseStep 1887457 = 1415593) (by norm_num)
theorem B3353885 : Blo 1490065 3353885 := bbase (se 3 (by rfl) ⟨628853, by rfl⟩ : syracuseStep 3353885 = 1257707) (by norm_num)
theorem B2829629 : Blo 1490065 2829629 := bbase (se 3 (by rfl) ⟨530555, by rfl⟩ : syracuseStep 2829629 = 1061111) (by norm_num)
theorem B1887553 : Blo 1490065 1887553 := bbase (se 2 (by rfl) ⟨707832, by rfl⟩ : syracuseStep 1887553 = 1415665) (by norm_num)
theorem B5033285 : Blo 1490065 5033285 := bbase (se 4 (by rfl) ⟨471870, by rfl⟩ : syracuseStep 5033285 = 943741) (by norm_num)
theorem B5098837 : Blo 1490065 5098837 := bbase (se 11 (by rfl) ⟨3734, by rfl⟩ : syracuseStep 5098837 = 7469) (by norm_num)
theorem B8064341 : Blo 1490065 8064341 := bbase (se 11 (by rfl) ⟨5906, by rfl⟩ : syracuseStep 8064341 = 11813) (by norm_num)
theorem B3353957 : Blo 1490065 3353957 := bbase (se 4 (by rfl) ⟨314433, by rfl⟩ : syracuseStep 3353957 = 628867) (by norm_num)
theorem B2387333 : Blo 1490065 2387333 := bbase (se 4 (by rfl) ⟨223812, by rfl⟩ : syracuseStep 2387333 = 447625) (by norm_num)
theorem B1592713 : Blo 1490065 1592713 := bbase (se 2 (by rfl) ⟨597267, by rfl⟩ : syracuseStep 1592713 = 1194535) (by norm_num)
theorem B1592717 : Blo 1490065 1592717 := bbase (se 3 (by rfl) ⟨298634, by rfl⟩ : syracuseStep 1592717 = 597269) (by norm_num)
theorem B3771805 : Blo 1490065 3771805 := bbase (se 3 (by rfl) ⟨707213, by rfl⟩ : syracuseStep 3771805 = 1414427) (by norm_num)
theorem B3354029 : Blo 1490065 3354029 := bbase (se 3 (by rfl) ⟨628880, by rfl⟩ : syracuseStep 3354029 = 1257761) (by norm_num)
theorem B2420165 : Blo 1490065 2420165 := bbase (se 4 (by rfl) ⟨226890, by rfl⟩ : syracuseStep 2420165 = 453781) (by norm_num)
theorem B7548389 : Blo 1490065 7548389 := bbase (se 4 (by rfl) ⟨707661, by rfl⟩ : syracuseStep 7548389 = 1415323) (by norm_num)
theorem B1887725 : Blo 1490065 1887725 := bbase (se 3 (by rfl) ⟨353948, by rfl⟩ : syracuseStep 1887725 = 707897) (by norm_num)
theorem B3354101 : Blo 1490065 3354101 := bbase (se 5 (by rfl) ⟨157223, by rfl⟩ : syracuseStep 3354101 = 314447) (by norm_num)
theorem B1699321 : Blo 1490065 1699321 := bbase (se 2 (by rfl) ⟨637245, by rfl⟩ : syracuseStep 1699321 = 1274491) (by norm_num)
theorem B6458885 : Blo 1490065 6458885 := bbase (se 4 (by rfl) ⟨605520, by rfl⟩ : syracuseStep 6458885 = 1211041) (by norm_num)
theorem B3771917 : Blo 1490065 3771917 := bbase (se 3 (by rfl) ⟨707234, by rfl⟩ : syracuseStep 3771917 = 1414469) (by norm_num)
theorem B1887781 : Blo 1490065 1887781 := bbase (se 4 (by rfl) ⟨176979, by rfl⟩ : syracuseStep 1887781 = 353959) (by norm_num)
theorem B3354173 : Blo 1490065 3354173 := bbase (se 3 (by rfl) ⟨628907, by rfl⟩ : syracuseStep 3354173 = 1257815) (by norm_num)
theorem B2829917 : Blo 1490065 2829917 := bbase (se 3 (by rfl) ⟨530609, by rfl⟩ : syracuseStep 2829917 = 1061219) (by norm_num)
theorem B3354245 : Blo 1490065 3354245 := bbase (se 4 (by rfl) ⟨314460, by rfl⟩ : syracuseStep 3354245 = 628921) (by norm_num)
theorem B1887877 : Blo 1490065 1887877 := bbase (se 4 (by rfl) ⟨176988, by rfl⟩ : syracuseStep 1887877 = 353977) (by norm_num)
theorem B5664437 : Blo 1490065 5664437 := bbase (se 5 (by rfl) ⟨265520, by rfl⟩ : syracuseStep 5664437 = 531041) (by norm_num)
theorem B3772109 : Blo 1490065 3772109 := bbase (se 3 (by rfl) ⟨707270, by rfl⟩ : syracuseStep 3772109 = 1414541) (by norm_num)
theorem B3354317 : Blo 1490065 3354317 := bbase (se 3 (by rfl) ⟨628934, by rfl⟩ : syracuseStep 3354317 = 1257869) (by norm_num)
theorem B12095189 : Blo 1490065 12095189 := bbase (se 7 (by rfl) ⟨141740, by rfl⟩ : syracuseStep 12095189 = 283481) (by norm_num)
theorem B2723557 : Blo 1490065 2723557 := bbase (se 4 (by rfl) ⟨255333, by rfl⟩ : syracuseStep 2723557 = 510667) (by norm_num)
theorem B2830069 : Blo 1490065 2830069 := bbase (se 5 (by rfl) ⟨132659, by rfl⟩ : syracuseStep 2830069 = 265319) (by norm_num)
theorem B5033717 : Blo 1490065 5033717 := bbase (se 5 (by rfl) ⟨235955, by rfl⟩ : syracuseStep 5033717 = 471911) (by norm_num)
theorem B3354389 : Blo 1490065 3354389 := bbase (se 6 (by rfl) ⟨78618, by rfl⟩ : syracuseStep 3354389 = 157237) (by norm_num)
theorem B1888049 : Blo 1490065 1888049 := bbase (se 2 (by rfl) ⟨708018, by rfl⟩ : syracuseStep 1888049 = 1416037) (by norm_num)
theorem B1511221 : Blo 1490065 1511221 := bbase (se 5 (by rfl) ⟨70838, by rfl⟩ : syracuseStep 1511221 = 141677) (by norm_num)
theorem B2387789 : Blo 1490065 2387789 := bbase (se 3 (by rfl) ⟨447710, by rfl⟩ : syracuseStep 2387789 = 895421) (by norm_num)
theorem B3354461 : Blo 1490065 3354461 := bbase (se 3 (by rfl) ⟨628961, by rfl⟩ : syracuseStep 3354461 = 1257923) (by norm_num)
theorem B1888105 : Blo 1490065 1888105 := bbase (se 2 (by rfl) ⟨708039, by rfl⟩ : syracuseStep 1888105 = 1416079) (by norm_num)
theorem B3354533 : Blo 1490065 3354533 := bbase (se 4 (by rfl) ⟨314487, by rfl⟩ : syracuseStep 3354533 = 628975) (by norm_num)
theorem B9555893 : Blo 1490065 9555893 := bbase (se 5 (by rfl) ⟨447932, by rfl⟩ : syracuseStep 9555893 = 895865) (by norm_num)
theorem B1593281 : Blo 1490065 1593281 := bbase (se 2 (by rfl) ⟨597480, by rfl⟩ : syracuseStep 1593281 = 1194961) (by norm_num)
theorem B1888201 : Blo 1490065 1888201 := bbase (se 2 (by rfl) ⟨708075, by rfl⟩ : syracuseStep 1888201 = 1416151) (by norm_num)
theorem B5664725 : Blo 1490065 5664725 := bbase (se 7 (by rfl) ⟨66383, by rfl⟩ : syracuseStep 5664725 = 132767) (by norm_num)
theorem B3354605 : Blo 1490065 3354605 := bbase (se 3 (by rfl) ⟨628988, by rfl⟩ : syracuseStep 3354605 = 1257977) (by norm_num)
theorem B1724401 : Blo 1490065 1724401 := bbase (se 2 (by rfl) ⟨646650, by rfl⟩ : syracuseStep 1724401 = 1293301) (by norm_num)
theorem B3182581 : Blo 1490065 3182581 := bbase (se 5 (by rfl) ⟨149183, by rfl⟩ : syracuseStep 3182581 = 298367) (by norm_num)
theorem B3772453 : Blo 1490065 3772453 := bbase (se 4 (by rfl) ⟨353667, by rfl⟩ : syracuseStep 3772453 = 707335) (by norm_num)
theorem B2830373 : Blo 1490065 2830373 := bbase (se 4 (by rfl) ⟨265347, by rfl⟩ : syracuseStep 2830373 = 530695) (by norm_num)
theorem B3354677 : Blo 1490065 3354677 := bbase (se 5 (by rfl) ⟨157250, by rfl⟩ : syracuseStep 3354677 = 314501) (by norm_num)
theorem B1912937 : Blo 1490065 1912937 := bbase (se 2 (by rfl) ⟨717351, by rfl⟩ : syracuseStep 1912937 = 1434703) (by norm_num)
theorem B1888373 : Blo 1490065 1888373 := bbase (se 5 (by rfl) ⟨88517, by rfl⟩ : syracuseStep 1888373 = 177035) (by norm_num)
theorem B3354749 : Blo 1490065 3354749 := bbase (se 3 (by rfl) ⟨629015, by rfl⟩ : syracuseStep 3354749 = 1258031) (by norm_num)
theorem B2420869 : Blo 1490065 2420869 := bbase (se 4 (by rfl) ⟨226956, by rfl⟩ : syracuseStep 2420869 = 453913) (by norm_num)
theorem B3772565 : Blo 1490065 3772565 := bbase (se 6 (by rfl) ⟨88419, by rfl⟩ : syracuseStep 3772565 = 176839) (by norm_num)
theorem B5034149 : Blo 1490065 5034149 := bbase (se 4 (by rfl) ⟨471951, by rfl⟩ : syracuseStep 5034149 = 943903) (by norm_num)
theorem B1913009 : Blo 1490065 1913009 := bbase (se 2 (by rfl) ⟨717378, by rfl⟩ : syracuseStep 1913009 = 1434757) (by norm_num)
theorem B3354821 : Blo 1490065 3354821 := bbase (se 4 (by rfl) ⟨314514, by rfl⟩ : syracuseStep 3354821 = 629029) (by norm_num)
theorem B3354893 : Blo 1490065 3354893 := bbase (se 3 (by rfl) ⟨629042, by rfl⟩ : syracuseStep 3354893 = 1258085) (by norm_num)
theorem B3772757 : Blo 1490065 3772757 := bbase (se 10 (by rfl) ⟨5526, by rfl⟩ : syracuseStep 3772757 = 11053) (by norm_num)
theorem B3354965 : Blo 1490065 3354965 := bbase (se 10 (by rfl) ⟨4914, by rfl⟩ : syracuseStep 3354965 = 9829) (by norm_num)
theorem B7647605 : Blo 1490065 7647605 := bbase (se 5 (by rfl) ⟨358481, by rfl⟩ : syracuseStep 7647605 = 716963) (by norm_num)
theorem B1700233 : Blo 1490065 1700233 := bbase (se 2 (by rfl) ⟨637587, by rfl⟩ : syracuseStep 1700233 = 1275175) (by norm_num)
theorem B3355037 : Blo 1490065 3355037 := bbase (se 3 (by rfl) ⟨629069, by rfl⟩ : syracuseStep 3355037 = 1258139) (by norm_num)
theorem B18141653 : Blo 1490065 18141653 := bbase (se 7 (by rfl) ⟨212597, by rfl⟩ : syracuseStep 18141653 = 425195) (by norm_num)
theorem B3183077 : Blo 1490065 3183077 := bbase (se 4 (by rfl) ⟨298413, by rfl⟩ : syracuseStep 3183077 = 596827) (by norm_num)
theorem B3355109 : Blo 1490065 3355109 := bbase (se 4 (by rfl) ⟨314541, by rfl⟩ : syracuseStep 3355109 = 629083) (by norm_num)
theorem B3355181 : Blo 1490065 3355181 := bbase (se 3 (by rfl) ⟨629096, by rfl⟩ : syracuseStep 3355181 = 1258193) (by norm_num)
theorem B5034581 : Blo 1490065 5034581 := bbase (se 8 (by rfl) ⟨29499, by rfl⟩ : syracuseStep 5034581 = 58999) (by norm_num)
theorem B3355253 : Blo 1490065 3355253 := bbase (se 5 (by rfl) ⟨157277, by rfl⟩ : syracuseStep 3355253 = 314555) (by norm_num)
theorem B3773101 : Blo 1490065 3773101 := bbase (se 3 (by rfl) ⟨707456, by rfl⟩ : syracuseStep 3773101 = 1414913) (by norm_num)
theorem B3355325 : Blo 1490065 3355325 := bbase (se 3 (by rfl) ⟨629123, by rfl⟩ : syracuseStep 3355325 = 1258247) (by norm_num)
theorem B7549685 : Blo 1490065 7549685 := bbase (se 5 (by rfl) ⟨353891, by rfl⟩ : syracuseStep 7549685 = 707783) (by norm_num)
theorem B3355397 : Blo 1490065 3355397 := bbase (se 4 (by rfl) ⟨314568, by rfl⟩ : syracuseStep 3355397 = 629137) (by norm_num)
theorem B2831125 : Blo 1490065 2831125 := bbase (se 6 (by rfl) ⟨66354, by rfl⟩ : syracuseStep 2831125 = 132709) (by norm_num)
theorem B11326229 : Blo 1490065 11326229 := bbase (se 6 (by rfl) ⟨265458, by rfl⟩ : syracuseStep 11326229 = 530917) (by norm_num)
theorem B3773213 : Blo 1490065 3773213 := bbase (se 3 (by rfl) ⟨707477, by rfl⟩ : syracuseStep 3773213 = 1414955) (by norm_num)
theorem B2388781 : Blo 1490065 2388781 := bbase (se 3 (by rfl) ⟨447896, by rfl⟩ : syracuseStep 2388781 = 895793) (by norm_num)
theorem B3355469 : Blo 1490065 3355469 := bbase (se 3 (by rfl) ⟨629150, by rfl⟩ : syracuseStep 3355469 = 1258301) (by norm_num)
theorem B3355541 : Blo 1490065 3355541 := bbase (se 6 (by rfl) ⟨78645, by rfl⟩ : syracuseStep 3355541 = 157291) (by norm_num)
theorem B2831269 : Blo 1490065 2831269 := bbase (se 4 (by rfl) ⟨265431, by rfl⟩ : syracuseStep 2831269 = 530863) (by norm_num)
theorem B7648181 : Blo 1490065 7648181 := bbase (se 5 (by rfl) ⟨358508, by rfl⟩ : syracuseStep 7648181 = 717017) (by norm_num)
theorem B1840081 : Blo 1490065 1840081 := bbase (se 2 (by rfl) ⟨690030, by rfl⟩ : syracuseStep 1840081 = 1380061) (by norm_num)
theorem B14521301 : Blo 1490065 14521301 := bbase (se 7 (by rfl) ⟨170171, by rfl⟩ : syracuseStep 14521301 = 340343) (by norm_num)
theorem B3773405 : Blo 1490065 3773405 := bbase (se 3 (by rfl) ⟨707513, by rfl⟩ : syracuseStep 3773405 = 1415027) (by norm_num)
theorem B3355613 : Blo 1490065 3355613 := bbase (se 3 (by rfl) ⟨629177, by rfl⟩ : syracuseStep 3355613 = 1258355) (by norm_num)
theorem B3584989 : Blo 1490065 3584989 := bbase (se 3 (by rfl) ⟨672185, by rfl⟩ : syracuseStep 3584989 = 1344371) (by norm_num)
theorem B1790957 : Blo 1490065 1790957 := bbase (se 3 (by rfl) ⟨335804, by rfl⟩ : syracuseStep 1790957 = 671609) (by norm_num)
theorem B5035013 : Blo 1490065 5035013 := bbase (se 4 (by rfl) ⟨472032, by rfl⟩ : syracuseStep 5035013 = 944065) (by norm_num)
theorem B16987157 : Blo 1490065 16987157 := bbase (se 6 (by rfl) ⟨398136, by rfl⟩ : syracuseStep 16987157 = 796273) (by norm_num)
theorem B4363301 : Blo 1490065 4363301 := bbase (se 4 (by rfl) ⟨409059, by rfl⟩ : syracuseStep 4363301 = 818119) (by norm_num)
theorem B3355685 : Blo 1490065 3355685 := bbase (se 4 (by rfl) ⟨314595, by rfl⟩ : syracuseStep 3355685 = 629191) (by norm_num)
theorem B1676353 : Blo 1490065 1676353 := bbase (se 2 (by rfl) ⟨628632, by rfl⟩ : syracuseStep 1676353 = 1257265) (by norm_num)
theorem B2831429 : Blo 1490065 2831429 := bbase (se 4 (by rfl) ⟨265446, by rfl⟩ : syracuseStep 2831429 = 530893) (by norm_num)
theorem B1676389 : Blo 1490065 1676389 := bbase (se 4 (by rfl) ⟨157161, by rfl⟩ : syracuseStep 1676389 = 314323) (by norm_num)
theorem B3355757 : Blo 1490065 3355757 := bbase (se 3 (by rfl) ⟨629204, by rfl⟩ : syracuseStep 3355757 = 1258409) (by norm_num)
theorem B1676425 : Blo 1490065 1676425 := bbase (se 2 (by rfl) ⟨628659, by rfl⟩ : syracuseStep 1676425 = 1257319) (by norm_num)
theorem B1676461 : Blo 1490065 1676461 := bbase (se 3 (by rfl) ⟨314336, by rfl⟩ : syracuseStep 1676461 = 628673) (by norm_num)
theorem B11318453 : Blo 1490065 11318453 := bbase (se 5 (by rfl) ⟨530552, by rfl⟩ : syracuseStep 11318453 = 1061105) (by norm_num)
theorem B3355829 : Blo 1490065 3355829 := bbase (se 5 (by rfl) ⟨157304, by rfl⟩ : syracuseStep 3355829 = 314609) (by norm_num)
theorem B2266309 : Blo 1490065 2266309 := bbase (se 4 (by rfl) ⟨212466, by rfl⟩ : syracuseStep 2266309 = 424933) (by norm_num)
theorem B1676497 : Blo 1490065 1676497 := bbase (se 2 (by rfl) ⟨628686, by rfl⟩ : syracuseStep 1676497 = 1257373) (by norm_num)
theorem B2831573 : Blo 1490065 2831573 := bbase (se 7 (by rfl) ⟨33182, by rfl⟩ : syracuseStep 2831573 = 66365) (by norm_num)
theorem B1676533 : Blo 1490065 1676533 := bbase (se 5 (by rfl) ⟨78587, by rfl⟩ : syracuseStep 1676533 = 157175) (by norm_num)
theorem B3355901 : Blo 1490065 3355901 := bbase (se 3 (by rfl) ⟨629231, by rfl⟩ : syracuseStep 3355901 = 1258463) (by norm_num)
theorem B1676569 : Blo 1490065 1676569 := bbase (se 2 (by rfl) ⟨628713, by rfl⟩ : syracuseStep 1676569 = 1257427) (by norm_num)
theorem B3773749 : Blo 1490065 3773749 := bbase (se 5 (by rfl) ⟨176894, by rfl⟩ : syracuseStep 3773749 = 353789) (by norm_num)
theorem B1676605 : Blo 1490065 1676605 := bbase (se 3 (by rfl) ⟨314363, by rfl⟩ : syracuseStep 1676605 = 628727) (by norm_num)
theorem B3355973 : Blo 1490065 3355973 := bbase (se 4 (by rfl) ⟨314622, by rfl⟩ : syracuseStep 3355973 = 629245) (by norm_num)
theorem B3183965 : Blo 1490065 3183965 := bbase (se 3 (by rfl) ⟨596993, by rfl⟩ : syracuseStep 3183965 = 1193987) (by norm_num)
theorem B1676641 : Blo 1490065 1676641 := bbase (se 2 (by rfl) ⟨628740, by rfl⟩ : syracuseStep 1676641 = 1257481) (by norm_num)
theorem B1676677 : Blo 1490065 1676677 := bbase (se 4 (by rfl) ⟨157188, by rfl⟩ : syracuseStep 1676677 = 314377) (by norm_num)
theorem B3356045 : Blo 1490065 3356045 := bbase (se 3 (by rfl) ⟨629258, by rfl⟩ : syracuseStep 3356045 = 1258517) (by norm_num)
theorem B3773861 : Blo 1490065 3773861 := bbase (se 4 (by rfl) ⟨353799, by rfl⟩ : syracuseStep 3773861 = 707599) (by norm_num)
theorem B1676713 : Blo 1490065 1676713 := bbase (se 2 (by rfl) ⟨628767, by rfl⟩ : syracuseStep 1676713 = 1257535) (by norm_num)
theorem B2389429 : Blo 1490065 2389429 := bbase (se 5 (by rfl) ⟨112004, by rfl⟩ : syracuseStep 2389429 = 224009) (by norm_num)
theorem B5035445 : Blo 1490065 5035445 := bbase (se 5 (by rfl) ⟨236036, by rfl⟩ : syracuseStep 5035445 = 472073) (by norm_num)
theorem B1676749 : Blo 1490065 1676749 := bbase (se 3 (by rfl) ⟨314390, by rfl⟩ : syracuseStep 1676749 = 628781) (by norm_num)
theorem B3184085 : Blo 1490065 3184085 := bbase (se 7 (by rfl) ⟨37313, by rfl⟩ : syracuseStep 3184085 = 74627) (by norm_num)
theorem B3356117 : Blo 1490065 3356117 := bbase (se 7 (by rfl) ⟨39329, by rfl⟩ : syracuseStep 3356117 = 78659) (by norm_num)
theorem B1676785 : Blo 1490065 1676785 := bbase (se 2 (by rfl) ⟨628794, by rfl⟩ : syracuseStep 1676785 = 1257589) (by norm_num)
theorem B2831861 : Blo 1490065 2831861 := bbase (se 5 (by rfl) ⟨132743, by rfl⟩ : syracuseStep 2831861 = 265487) (by norm_num)
theorem B7263749 : Blo 1490065 7263749 := bbase (se 4 (by rfl) ⟨680976, by rfl⟩ : syracuseStep 7263749 = 1361953) (by norm_num)
theorem B5658133 : Blo 1490065 5658133 := bbase (se 6 (by rfl) ⟨132612, by rfl⟩ : syracuseStep 5658133 = 265225) (by norm_num)
theorem B1676821 : Blo 1490065 1676821 := bbase (se 6 (by rfl) ⟨39300, by rfl⟩ : syracuseStep 1676821 = 78601) (by norm_num)
theorem B3356189 : Blo 1490065 3356189 := bbase (se 3 (by rfl) ⟨629285, by rfl⟩ : syracuseStep 3356189 = 1258571) (by norm_num)
theorem B1635877 : Blo 1490065 1635877 := bbase (se 4 (by rfl) ⟨153363, by rfl⟩ : syracuseStep 1635877 = 306727) (by norm_num)
theorem B1676857 : Blo 1490065 1676857 := bbase (se 2 (by rfl) ⟨628821, by rfl⟩ : syracuseStep 1676857 = 1257643) (by norm_num)
theorem B1676893 : Blo 1490065 1676893 := bbase (se 3 (by rfl) ⟨314417, by rfl⟩ : syracuseStep 1676893 = 628835) (by norm_num)
theorem B3774053 : Blo 1490065 3774053 := bbase (se 4 (by rfl) ⟨353817, by rfl⟩ : syracuseStep 3774053 = 707635) (by norm_num)
theorem B3356261 : Blo 1490065 3356261 := bbase (se 4 (by rfl) ⟨314649, by rfl⟩ : syracuseStep 3356261 = 629299) (by norm_num)
theorem B1676929 : Blo 1490065 1676929 := bbase (se 2 (by rfl) ⟨628848, by rfl⟩ : syracuseStep 1676929 = 1257697) (by norm_num)
theorem B2832013 : Blo 1490065 2832013 := bbase (se 3 (by rfl) ⟨531002, by rfl⟩ : syracuseStep 2832013 = 1062005) (by norm_num)
theorem B1791649 : Blo 1490065 1791649 := bbase (se 2 (by rfl) ⟨671868, by rfl⟩ : syracuseStep 1791649 = 1343737) (by norm_num)
theorem B6985381 : Blo 1490065 6985381 := bbase (se 4 (by rfl) ⟨654879, by rfl⟩ : syracuseStep 6985381 = 1309759) (by norm_num)
theorem B1676965 : Blo 1490065 1676965 := bbase (se 4 (by rfl) ⟨157215, by rfl⟩ : syracuseStep 1676965 = 314431) (by norm_num)
theorem B1791653 : Blo 1490065 1791653 := bbase (se 4 (by rfl) ⟨167967, by rfl⟩ : syracuseStep 1791653 = 335935) (by norm_num)
theorem B3356333 : Blo 1490065 3356333 := bbase (se 3 (by rfl) ⟨629312, by rfl⟩ : syracuseStep 3356333 = 1258625) (by norm_num)
theorem B1677001 : Blo 1490065 1677001 := bbase (se 2 (by rfl) ⟨628875, by rfl⟩ : syracuseStep 1677001 = 1257751) (by norm_num)
theorem B1677037 : Blo 1490065 1677037 := bbase (se 3 (by rfl) ⟨314444, by rfl⟩ : syracuseStep 1677037 = 628889) (by norm_num)
theorem B3356405 : Blo 1490065 3356405 := bbase (se 5 (by rfl) ⟨157331, by rfl⟩ : syracuseStep 3356405 = 314663) (by norm_num)
theorem B1677073 : Blo 1490065 1677073 := bbase (se 2 (by rfl) ⟨628902, by rfl⟩ : syracuseStep 1677073 = 1257805) (by norm_num)
theorem B28661525 : Blo 1490065 28661525 := bbase (se 6 (by rfl) ⟨671754, by rfl⟩ : syracuseStep 28661525 = 1343509) (by norm_num)
theorem B1677109 : Blo 1490065 1677109 := bbase (se 5 (by rfl) ⟨78614, by rfl⟩ : syracuseStep 1677109 = 157229) (by norm_num)
theorem B3356477 : Blo 1490065 3356477 := bbase (se 3 (by rfl) ⟨629339, by rfl⟩ : syracuseStep 3356477 = 1258679) (by norm_num)
theorem B5658437 : Blo 1490065 5658437 := bbase (se 4 (by rfl) ⟨530478, by rfl⟩ : syracuseStep 5658437 = 1060957) (by norm_num)
theorem B5371717 : Blo 1490065 5371717 := bbase (se 4 (by rfl) ⟨503598, by rfl⟩ : syracuseStep 5371717 = 1007197) (by norm_num)
theorem B1677145 : Blo 1490065 1677145 := bbase (se 2 (by rfl) ⟨628929, by rfl⟩ : syracuseStep 1677145 = 1257859) (by norm_num)
theorem B1677181 : Blo 1490065 1677181 := bbase (se 3 (by rfl) ⟨314471, by rfl⟩ : syracuseStep 1677181 = 628943) (by norm_num)
theorem B3356549 : Blo 1490065 3356549 := bbase (se 4 (by rfl) ⟨314676, by rfl⟩ : syracuseStep 3356549 = 629353) (by norm_num)
theorem B1677217 : Blo 1490065 1677217 := bbase (se 2 (by rfl) ⟨628956, by rfl⟩ : syracuseStep 1677217 = 1257913) (by norm_num)
theorem B3774397 : Blo 1490065 3774397 := bbase (se 3 (by rfl) ⟨707699, by rfl⟩ : syracuseStep 3774397 = 1415399) (by norm_num)
theorem B2832317 : Blo 1490065 2832317 := bbase (se 3 (by rfl) ⟨531059, by rfl⟩ : syracuseStep 2832317 = 1062119) (by norm_num)
theorem B1677253 : Blo 1490065 1677253 := bbase (se 4 (by rfl) ⟨157242, by rfl⟩ : syracuseStep 1677253 = 314485) (by norm_num)
theorem B3356621 : Blo 1490065 3356621 := bbase (se 3 (by rfl) ⟨629366, by rfl⟩ : syracuseStep 3356621 = 1258733) (by norm_num)
theorem B1677289 : Blo 1490065 1677289 := bbase (se 2 (by rfl) ⟨628983, by rfl⟩ : syracuseStep 1677289 = 1257967) (by norm_num)
theorem B7550981 : Blo 1490065 7550981 := bbase (se 4 (by rfl) ⟨707904, by rfl⟩ : syracuseStep 7550981 = 1415809) (by norm_num)
theorem B1677325 : Blo 1490065 1677325 := bbase (se 3 (by rfl) ⟨314498, by rfl⟩ : syracuseStep 1677325 = 628997) (by norm_num)
theorem B9549845 : Blo 1490065 9549845 := bbase (se 6 (by rfl) ⟨223824, by rfl⟩ : syracuseStep 9549845 = 447649) (by norm_num)
theorem B3356693 : Blo 1490065 3356693 := bbase (se 6 (by rfl) ⟨78672, by rfl⟩ : syracuseStep 3356693 = 157345) (by norm_num)
theorem B3774509 : Blo 1490065 3774509 := bbase (se 3 (by rfl) ⟨707720, by rfl⟩ : syracuseStep 3774509 = 1415441) (by norm_num)
theorem B1677361 : Blo 1490065 1677361 := bbase (se 2 (by rfl) ⟨629010, by rfl⟩ : syracuseStep 1677361 = 1258021) (by norm_num)
theorem B3184717 : Blo 1490065 3184717 := bbase (se 3 (by rfl) ⟨597134, by rfl⟩ : syracuseStep 3184717 = 1194269) (by norm_num)
theorem B1677397 : Blo 1490065 1677397 := bbase (se 8 (by rfl) ⟨9828, by rfl⟩ : syracuseStep 1677397 = 19657) (by norm_num)
theorem B3356765 : Blo 1490065 3356765 := bbase (se 3 (by rfl) ⟨629393, by rfl⟩ : syracuseStep 3356765 = 1258787) (by norm_num)
theorem B1677433 : Blo 1490065 1677433 := bbase (se 2 (by rfl) ⟨629037, by rfl⟩ : syracuseStep 1677433 = 1258075) (by norm_num)
theorem B1792153 : Blo 1490065 1792153 := bbase (se 2 (by rfl) ⟨672057, by rfl⟩ : syracuseStep 1792153 = 1344115) (by norm_num)
theorem B1677469 : Blo 1490065 1677469 := bbase (se 3 (by rfl) ⟨314525, by rfl⟩ : syracuseStep 1677469 = 629051) (by norm_num)
theorem B3356837 : Blo 1490065 3356837 := bbase (se 4 (by rfl) ⟨314703, by rfl⟩ : syracuseStep 3356837 = 629407) (by norm_num)
theorem B1677505 : Blo 1490065 1677505 := bbase (se 2 (by rfl) ⟨629064, by rfl⟩ : syracuseStep 1677505 = 1258129) (by norm_num)
theorem B1677541 : Blo 1490065 1677541 := bbase (se 4 (by rfl) ⟨157269, by rfl⟩ : syracuseStep 1677541 = 314539) (by norm_num)
theorem B3774701 : Blo 1490065 3774701 := bbase (se 3 (by rfl) ⟨707756, by rfl⟩ : syracuseStep 3774701 = 1415513) (by norm_num)
theorem B3356909 : Blo 1490065 3356909 := bbase (se 3 (by rfl) ⟨629420, by rfl⟩ : syracuseStep 3356909 = 1258841) (by norm_num)
theorem B1677577 : Blo 1490065 1677577 := bbase (se 2 (by rfl) ⟨629091, by rfl⟩ : syracuseStep 1677577 = 1258183) (by norm_num)
theorem B6371621 : Blo 1490065 6371621 := bbase (se 4 (by rfl) ⟨597339, by rfl⟩ : syracuseStep 6371621 = 1194679) (by norm_num)
theorem B1816873 : Blo 1490065 1816873 := bbase (se 2 (by rfl) ⟨681327, by rfl⟩ : syracuseStep 1816873 = 1362655) (by norm_num)
theorem B1677613 : Blo 1490065 1677613 := bbase (se 3 (by rfl) ⟨314552, by rfl⟩ : syracuseStep 1677613 = 629105) (by norm_num)
theorem B3356981 : Blo 1490065 3356981 := bbase (se 5 (by rfl) ⟨157358, by rfl⟩ : syracuseStep 3356981 = 314717) (by norm_num)
theorem B1677649 : Blo 1490065 1677649 := bbase (se 2 (by rfl) ⟨629118, by rfl⟩ : syracuseStep 1677649 = 1258237) (by norm_num)
theorem B1677685 : Blo 1490065 1677685 := bbase (se 5 (by rfl) ⟨78641, by rfl⟩ : syracuseStep 1677685 = 157283) (by norm_num)
theorem B3357053 : Blo 1490065 3357053 := bbase (se 3 (by rfl) ⟨629447, by rfl⟩ : syracuseStep 3357053 = 1258895) (by norm_num)
theorem B2685317 : Blo 1490065 2685317 := bbase (se 4 (by rfl) ⟨251748, by rfl⟩ : syracuseStep 2685317 = 503497) (by norm_num)
theorem B1677721 : Blo 1490065 1677721 := bbase (se 2 (by rfl) ⟨629145, by rfl⟩ : syracuseStep 1677721 = 1258291) (by norm_num)
theorem B1677757 : Blo 1490065 1677757 := bbase (se 3 (by rfl) ⟨314579, by rfl⟩ : syracuseStep 1677757 = 629159) (by norm_num)
theorem B3357125 : Blo 1490065 3357125 := bbase (se 4 (by rfl) ⟨314730, by rfl⟩ : syracuseStep 3357125 = 629461) (by norm_num)
theorem B2685397 : Blo 1490065 2685397 := bbase (se 7 (by rfl) ⟨31469, by rfl⟩ : syracuseStep 2685397 = 62939) (by norm_num)
theorem B1677793 : Blo 1490065 1677793 := bbase (se 2 (by rfl) ⟨629172, by rfl⟩ : syracuseStep 1677793 = 1258345) (by norm_num)
theorem B1677829 : Blo 1490065 1677829 := bbase (se 4 (by rfl) ⟨157296, by rfl⟩ : syracuseStep 1677829 = 314593) (by norm_num)
theorem B12098069 : Blo 1490065 12098069 := bbase (se 6 (by rfl) ⟨283548, by rfl⟩ : syracuseStep 12098069 = 567097) (by norm_num)
theorem B1677865 : Blo 1490065 1677865 := bbase (se 2 (by rfl) ⟨629199, by rfl⟩ : syracuseStep 1677865 = 1258399) (by norm_num)
theorem B3775045 : Blo 1490065 3775045 := bbase (se 4 (by rfl) ⟨353910, by rfl⟩ : syracuseStep 3775045 = 707821) (by norm_num)
theorem B1677901 : Blo 1490065 1677901 := bbase (se 3 (by rfl) ⟨314606, by rfl⟩ : syracuseStep 1677901 = 629213) (by norm_num)
theorem B1677937 : Blo 1490065 1677937 := bbase (se 2 (by rfl) ⟨629226, by rfl⟩ : syracuseStep 1677937 = 1258453) (by norm_num)
theorem B1677973 : Blo 1490065 1677973 := bbase (se 6 (by rfl) ⟨39327, by rfl⟩ : syracuseStep 1677973 = 78655) (by norm_num)
theorem B3775157 : Blo 1490065 3775157 := bbase (se 5 (by rfl) ⟨176960, by rfl⟩ : syracuseStep 3775157 = 353921) (by norm_num)
theorem B1940149 : Blo 1490065 1940149 := bbase (se 5 (by rfl) ⟨90944, by rfl⟩ : syracuseStep 1940149 = 181889) (by norm_num)
theorem B1678009 : Blo 1490065 1678009 := bbase (se 2 (by rfl) ⟨629253, by rfl⟩ : syracuseStep 1678009 = 1258507) (by norm_num)
theorem B2685629 : Blo 1490065 2685629 := bbase (se 3 (by rfl) ⟨503555, by rfl⟩ : syracuseStep 2685629 = 1007111) (by norm_num)
theorem B2235101 : Blo 1490065 2235101 := bbase (se 3 (by rfl) ⟨419081, by rfl⟩ : syracuseStep 2235101 = 838163) (by norm_num)
theorem B1678045 : Blo 1490065 1678045 := bbase (se 3 (by rfl) ⟨314633, by rfl⟩ : syracuseStep 1678045 = 629267) (by norm_num)
theorem B2235125 : Blo 1490065 2235125 := bbase (se 5 (by rfl) ⟨104771, by rfl⟩ : syracuseStep 2235125 = 209543) (by norm_num)
theorem B1678081 : Blo 1490065 1678081 := bbase (se 2 (by rfl) ⟨629280, by rfl⟩ : syracuseStep 1678081 = 1258561) (by norm_num)
theorem B2235149 : Blo 1490065 2235149 := bbase (se 3 (by rfl) ⟨419090, by rfl⟩ : syracuseStep 2235149 = 838181) (by norm_num)
theorem B2235173 : Blo 1490065 2235173 := bbase (se 4 (by rfl) ⟨209547, by rfl⟩ : syracuseStep 2235173 = 419095) (by norm_num)
theorem B1678117 : Blo 1490065 1678117 := bbase (se 4 (by rfl) ⟨157323, by rfl⟩ : syracuseStep 1678117 = 314647) (by norm_num)
theorem B2906933 : Blo 1490065 2906933 := bbase (se 5 (by rfl) ⟨136262, by rfl⟩ : syracuseStep 2906933 = 272525) (by norm_num)
theorem B2235197 : Blo 1490065 2235197 := bbase (se 3 (by rfl) ⟨419099, by rfl⟩ : syracuseStep 2235197 = 838199) (by norm_num)
theorem B1678153 : Blo 1490065 1678153 := bbase (se 2 (by rfl) ⟨629307, by rfl⟩ : syracuseStep 1678153 = 1258615) (by norm_num)
theorem B2235221 : Blo 1490065 2235221 := bbase (se 9 (by rfl) ⟨6548, by rfl⟩ : syracuseStep 2235221 = 13097) (by norm_num)
theorem B2235245 : Blo 1490065 2235245 := bbase (se 3 (by rfl) ⟨419108, by rfl⟩ : syracuseStep 2235245 = 838217) (by norm_num)
theorem B1678189 : Blo 1490065 1678189 := bbase (se 3 (by rfl) ⟨314660, by rfl⟩ : syracuseStep 1678189 = 629321) (by norm_num)
theorem B3775349 : Blo 1490065 3775349 := bbase (se 5 (by rfl) ⟨176969, by rfl⟩ : syracuseStep 3775349 = 353939) (by norm_num)
theorem B2235269 : Blo 1490065 2235269 := bbase (se 4 (by rfl) ⟨209556, by rfl⟩ : syracuseStep 2235269 = 419113) (by norm_num)
theorem B1678225 : Blo 1490065 1678225 := bbase (se 2 (by rfl) ⟨629334, by rfl⟩ : syracuseStep 1678225 = 1258669) (by norm_num)
theorem B2235293 : Blo 1490065 2235293 := bbase (se 3 (by rfl) ⟨419117, by rfl⟩ : syracuseStep 2235293 = 838235) (by norm_num)
theorem B2235317 : Blo 1490065 2235317 := bbase (se 5 (by rfl) ⟨104780, by rfl⟩ : syracuseStep 2235317 = 209561) (by norm_num)
theorem B7650229 : Blo 1490065 7650229 := bbase (se 5 (by rfl) ⟨358604, by rfl⟩ : syracuseStep 7650229 = 717209) (by norm_num)
theorem B1678261 : Blo 1490065 1678261 := bbase (se 5 (by rfl) ⟨78668, by rfl⟩ : syracuseStep 1678261 = 157337) (by norm_num)
theorem B3185605 : Blo 1490065 3185605 := bbase (se 4 (by rfl) ⟨298650, by rfl⟩ : syracuseStep 3185605 = 597301) (by norm_num)
theorem B2235341 : Blo 1490065 2235341 := bbase (se 3 (by rfl) ⟨419126, by rfl⟩ : syracuseStep 2235341 = 838253) (by norm_num)
theorem B1678297 : Blo 1490065 1678297 := bbase (se 2 (by rfl) ⟨629361, by rfl⟩ : syracuseStep 1678297 = 1258723) (by norm_num)
theorem B2235365 : Blo 1490065 2235365 := bbase (se 4 (by rfl) ⟨209565, by rfl⟩ : syracuseStep 2235365 = 419131) (by norm_num)
theorem B2235389 : Blo 1490065 2235389 := bbase (se 3 (by rfl) ⟨419135, by rfl⟩ : syracuseStep 2235389 = 838271) (by norm_num)
theorem B1678333 : Blo 1490065 1678333 := bbase (se 3 (by rfl) ⟨314687, by rfl⟩ : syracuseStep 1678333 = 629375) (by norm_num)
theorem B2235413 : Blo 1490065 2235413 := bbase (se 6 (by rfl) ⟨52392, by rfl⟩ : syracuseStep 2235413 = 104785) (by norm_num)
theorem B1678369 : Blo 1490065 1678369 := bbase (se 2 (by rfl) ⟨629388, by rfl⟩ : syracuseStep 1678369 = 1258777) (by norm_num)
theorem B2235437 : Blo 1490065 2235437 := bbase (se 3 (by rfl) ⟨419144, by rfl⟩ : syracuseStep 2235437 = 838289) (by norm_num)
theorem B6454325 : Blo 1490065 6454325 := bbase (se 5 (by rfl) ⟨302546, by rfl⟩ : syracuseStep 6454325 = 605093) (by norm_num)
theorem B3185725 : Blo 1490065 3185725 := bbase (se 3 (by rfl) ⟨597323, by rfl⟩ : syracuseStep 3185725 = 1194647) (by norm_num)
theorem B2235461 : Blo 1490065 2235461 := bbase (se 4 (by rfl) ⟨209574, by rfl⟩ : syracuseStep 2235461 = 419149) (by norm_num)
theorem B1678405 : Blo 1490065 1678405 := bbase (se 4 (by rfl) ⟨157350, by rfl⟩ : syracuseStep 1678405 = 314701) (by norm_num)
theorem B2235485 : Blo 1490065 2235485 := bbase (se 3 (by rfl) ⟨419153, by rfl⟩ : syracuseStep 2235485 = 838307) (by norm_num)
theorem B1678441 : Blo 1490065 1678441 := bbase (se 2 (by rfl) ⟨629415, by rfl⟩ : syracuseStep 1678441 = 1258831) (by norm_num)
theorem B2235509 : Blo 1490065 2235509 := bbase (se 5 (by rfl) ⟨104789, by rfl⟩ : syracuseStep 2235509 = 209579) (by norm_num)
theorem B2235533 : Blo 1490065 2235533 := bbase (se 3 (by rfl) ⟨419162, by rfl⟩ : syracuseStep 2235533 = 838325) (by norm_num)
theorem B1678477 : Blo 1490065 1678477 := bbase (se 3 (by rfl) ⟨314714, by rfl⟩ : syracuseStep 1678477 = 629429) (by norm_num)
theorem B2235557 : Blo 1490065 2235557 := bbase (se 4 (by rfl) ⟨209583, by rfl⟩ : syracuseStep 2235557 = 419167) (by norm_num)
theorem B1678513 : Blo 1490065 1678513 := bbase (se 2 (by rfl) ⟨629442, by rfl⟩ : syracuseStep 1678513 = 1258885) (by norm_num)
theorem B2268341 : Blo 1490065 2268341 := bbase (se 5 (by rfl) ⟨106328, by rfl⟩ : syracuseStep 2268341 = 212657) (by norm_num)
theorem B2235581 : Blo 1490065 2235581 := bbase (se 3 (by rfl) ⟨419171, by rfl⟩ : syracuseStep 2235581 = 838343) (by norm_num)
theorem B3775693 : Blo 1490065 3775693 := bbase (se 3 (by rfl) ⟨707942, by rfl⟩ : syracuseStep 3775693 = 1415885) (by norm_num)
theorem B2235605 : Blo 1490065 2235605 := bbase (se 7 (by rfl) ⟨26198, by rfl⟩ : syracuseStep 2235605 = 52397) (by norm_num)
theorem B1678549 : Blo 1490065 1678549 := bbase (se 7 (by rfl) ⟨19670, by rfl⟩ : syracuseStep 1678549 = 39341) (by norm_num)
theorem B2235629 : Blo 1490065 2235629 := bbase (se 3 (by rfl) ⟨419180, by rfl⟩ : syracuseStep 2235629 = 838361) (by norm_num)
theorem B2235653 : Blo 1490065 2235653 := bbase (se 4 (by rfl) ⟨209592, by rfl⟩ : syracuseStep 2235653 = 419185) (by norm_num)
theorem B7552277 : Blo 1490065 7552277 := bbase (se 6 (by rfl) ⟨177006, by rfl⟩ : syracuseStep 7552277 = 354013) (by norm_num)
theorem B1613081 : Blo 1490065 1613081 := bbase (se 2 (by rfl) ⟨604905, by rfl⟩ : syracuseStep 1613081 = 1209811) (by norm_num)
theorem B2235677 : Blo 1490065 2235677 := bbase (se 3 (by rfl) ⟨419189, by rfl⟩ : syracuseStep 2235677 = 838379) (by norm_num)
theorem B2235701 : Blo 1490065 2235701 := bbase (se 5 (by rfl) ⟨104798, by rfl⟩ : syracuseStep 2235701 = 209597) (by norm_num)
theorem B3775805 : Blo 1490065 3775805 := bbase (se 3 (by rfl) ⟨707963, by rfl⟩ : syracuseStep 3775805 = 1415927) (by norm_num)
theorem B3185981 : Blo 1490065 3185981 := bbase (se 3 (by rfl) ⟨597371, by rfl⟩ : syracuseStep 3185981 = 1194743) (by norm_num)
theorem B2235725 : Blo 1490065 2235725 := bbase (se 3 (by rfl) ⟨419198, by rfl⟩ : syracuseStep 2235725 = 838397) (by norm_num)
theorem B4775269 : Blo 1490065 4775269 := bbase (se 4 (by rfl) ⟨447681, by rfl⟩ : syracuseStep 4775269 = 895363) (by norm_num)
theorem B2235749 : Blo 1490065 2235749 := bbase (se 4 (by rfl) ⟨209601, by rfl⟩ : syracuseStep 2235749 = 419203) (by norm_num)
theorem B2235773 : Blo 1490065 2235773 := bbase (se 3 (by rfl) ⟨419207, by rfl⟩ : syracuseStep 2235773 = 838415) (by norm_num)
theorem B2235797 : Blo 1490065 2235797 := bbase (se 6 (by rfl) ⟨52401, by rfl⟩ : syracuseStep 2235797 = 104803) (by norm_num)
theorem B2235821 : Blo 1490065 2235821 := bbase (se 3 (by rfl) ⟨419216, by rfl⟩ : syracuseStep 2235821 = 838433) (by norm_num)
theorem B2014637 : Blo 1490065 2014637 := bbase (se 3 (by rfl) ⟨377744, by rfl⟩ : syracuseStep 2014637 = 755489) (by norm_num)
theorem B2235845 : Blo 1490065 2235845 := bbase (se 4 (by rfl) ⟨209610, by rfl⟩ : syracuseStep 2235845 = 419221) (by norm_num)
theorem B2235869 : Blo 1490065 2235869 := bbase (se 3 (by rfl) ⟨419225, by rfl⟩ : syracuseStep 2235869 = 838451) (by norm_num)
theorem B2235893 : Blo 1490065 2235893 := bbase (se 5 (by rfl) ⟨104807, by rfl⟩ : syracuseStep 2235893 = 209615) (by norm_num)
theorem B3775997 : Blo 1490065 3775997 := bbase (se 3 (by rfl) ⟨707999, by rfl⟩ : syracuseStep 3775997 = 1415999) (by norm_num)
theorem B2235917 : Blo 1490065 2235917 := bbase (se 3 (by rfl) ⟨419234, by rfl⟩ : syracuseStep 2235917 = 838469) (by norm_num)
theorem B5029397 : Blo 1490065 5029397 := bbase (se 6 (by rfl) ⟨117876, by rfl⟩ : syracuseStep 5029397 = 235753) (by norm_num)
theorem B2235941 : Blo 1490065 2235941 := bbase (se 4 (by rfl) ⟨209619, by rfl⟩ : syracuseStep 2235941 = 419239) (by norm_num)
theorem B2235965 : Blo 1490065 2235965 := bbase (se 3 (by rfl) ⟨419243, by rfl⟩ : syracuseStep 2235965 = 838487) (by norm_num)
theorem B2014789 : Blo 1490065 2014789 := bbase (se 4 (by rfl) ⟨188886, by rfl⟩ : syracuseStep 2014789 = 377773) (by norm_num)
theorem B2235989 : Blo 1490065 2235989 := bbase (se 8 (by rfl) ⟨13101, by rfl⟩ : syracuseStep 2235989 = 26203) (by norm_num)
theorem B2236013 : Blo 1490065 2236013 := bbase (se 3 (by rfl) ⟨419252, by rfl⟩ : syracuseStep 2236013 = 838505) (by norm_num)
theorem B2514557 : Blo 1490065 2514557 := bbase (se 3 (by rfl) ⟨471479, by rfl⟩ : syracuseStep 2514557 = 942959) (by norm_num)
theorem B2236037 : Blo 1490065 2236037 := bbase (se 4 (by rfl) ⟨209628, by rfl⟩ : syracuseStep 2236037 = 419257) (by norm_num)
theorem B2236061 : Blo 1490065 2236061 := bbase (se 3 (by rfl) ⟨419261, by rfl⟩ : syracuseStep 2236061 = 838523) (by norm_num)
theorem B7544501 : Blo 1490065 7544501 := bbase (se 5 (by rfl) ⟨353648, by rfl⟩ : syracuseStep 7544501 = 707297) (by norm_num)
theorem B2236085 : Blo 1490065 2236085 := bbase (se 5 (by rfl) ⟨104816, by rfl⟩ : syracuseStep 2236085 = 209633) (by norm_num)
theorem B2236109 : Blo 1490065 2236109 := bbase (se 3 (by rfl) ⟨419270, by rfl⟩ : syracuseStep 2236109 = 838541) (by norm_num)
theorem B2236133 : Blo 1490065 2236133 := bbase (se 4 (by rfl) ⟨209637, by rfl⟩ : syracuseStep 2236133 = 419275) (by norm_num)
theorem B2514685 : Blo 1490065 2514685 := bbase (se 3 (by rfl) ⟨471503, by rfl⟩ : syracuseStep 2514685 = 943007) (by norm_num)
theorem B2236157 : Blo 1490065 2236157 := bbase (se 3 (by rfl) ⟨419279, by rfl⟩ : syracuseStep 2236157 = 838559) (by norm_num)
theorem B2236181 : Blo 1490065 2236181 := bbase (se 6 (by rfl) ⟨52410, by rfl⟩ : syracuseStep 2236181 = 104821) (by norm_num)
theorem B2236205 : Blo 1490065 2236205 := bbase (se 3 (by rfl) ⟨419288, by rfl⟩ : syracuseStep 2236205 = 838577) (by norm_num)
theorem B8494901 : Blo 1490065 8494901 := bbase (se 5 (by rfl) ⟨398198, by rfl⟩ : syracuseStep 8494901 = 796397) (by norm_num)
theorem B2686781 : Blo 1490065 2686781 := bbase (se 3 (by rfl) ⟨503771, by rfl⟩ : syracuseStep 2686781 = 1007543) (by norm_num)
theorem B2236229 : Blo 1490065 2236229 := bbase (se 4 (by rfl) ⟨209646, by rfl⟩ : syracuseStep 2236229 = 419293) (by norm_num)
theorem B2514773 : Blo 1490065 2514773 := bbase (se 9 (by rfl) ⟨7367, by rfl⟩ : syracuseStep 2514773 = 14735) (by norm_num)
theorem B3776341 : Blo 1490065 3776341 := bbase (se 9 (by rfl) ⟨11063, by rfl⟩ : syracuseStep 3776341 = 22127) (by norm_num)
theorem B2236253 : Blo 1490065 2236253 := bbase (se 3 (by rfl) ⟨419297, by rfl⟩ : syracuseStep 2236253 = 838595) (by norm_num)
theorem B2236277 : Blo 1490065 2236277 := bbase (se 5 (by rfl) ⟨104825, by rfl⟩ : syracuseStep 2236277 = 209651) (by norm_num)
theorem B5660549 : Blo 1490065 5660549 := bbase (se 4 (by rfl) ⟨530676, by rfl⟩ : syracuseStep 5660549 = 1061353) (by norm_num)
theorem B2236301 : Blo 1490065 2236301 := bbase (se 3 (by rfl) ⟨419306, by rfl⟩ : syracuseStep 2236301 = 838613) (by norm_num)
theorem B2686861 : Blo 1490065 2686861 := bbase (se 3 (by rfl) ⟨503786, by rfl⟩ : syracuseStep 2686861 = 1007573) (by norm_num)
theorem B2236325 : Blo 1490065 2236325 := bbase (se 4 (by rfl) ⟨209655, by rfl⟩ : syracuseStep 2236325 = 419311) (by norm_num)
theorem B2236349 : Blo 1490065 2236349 := bbase (se 3 (by rfl) ⟨419315, by rfl⟩ : syracuseStep 2236349 = 838631) (by norm_num)
theorem B5029829 : Blo 1490065 5029829 := bbase (se 4 (by rfl) ⟨471546, by rfl⟩ : syracuseStep 5029829 = 943093) (by norm_num)
theorem B3776453 : Blo 1490065 3776453 := bbase (se 4 (by rfl) ⟨354042, by rfl⟩ : syracuseStep 3776453 = 708085) (by norm_num)
theorem B2514901 : Blo 1490065 2514901 := bbase (se 7 (by rfl) ⟨29471, by rfl⟩ : syracuseStep 2514901 = 58943) (by norm_num)
theorem B2236373 : Blo 1490065 2236373 := bbase (se 7 (by rfl) ⟨26207, by rfl⟩ : syracuseStep 2236373 = 52415) (by norm_num)
theorem B2121709 : Blo 1490065 2121709 := bbase (se 3 (by rfl) ⟨397820, by rfl⟩ : syracuseStep 2121709 = 795641) (by norm_num)
theorem B2236397 : Blo 1490065 2236397 := bbase (se 3 (by rfl) ⟨419324, by rfl⟩ : syracuseStep 2236397 = 838649) (by norm_num)
theorem B2015221 : Blo 1490065 2015221 := bbase (se 5 (by rfl) ⟨94463, by rfl⟩ : syracuseStep 2015221 = 188927) (by norm_num)
theorem B1490947 : Blo 1490065 1490947 := bstep (se 1 (by rfl) ⟨1118210, by rfl⟩ : syracuseStep 1490947 = 2236421) B2236421
theorem B2236433 : Blo 1490065 2236433 := bstep (se 2 (by rfl) ⟨838662, by rfl⟩ : syracuseStep 2236433 = 1677325) B1677325
theorem B1490963 : Blo 1490065 1490963 := bstep (se 1 (by rfl) ⟨1118222, by rfl⟩ : syracuseStep 1490963 = 2236445) B2236445
theorem B2236451 : Blo 1490065 2236451 := bstep (se 1 (by rfl) ⟨1677338, by rfl⟩ : syracuseStep 2236451 = 3354677) B3354677
theorem B1490979 : Blo 1490065 1490979 := bstep (se 1 (by rfl) ⟨1118234, by rfl⟩ : syracuseStep 1490979 = 2236469) B2236469
theorem B5029937 : Blo 1490065 5029937 := bstep (se 2 (by rfl) ⟨1886226, by rfl⟩ : syracuseStep 5029937 = 3772453) B3772453
theorem B1490995 : Blo 1490065 1490995 := bstep (se 1 (by rfl) ⟨1118246, by rfl⟩ : syracuseStep 1490995 = 2236493) B2236493
theorem B2515009 : Blo 1490065 2515009 := bstep (se 2 (by rfl) ⟨943128, by rfl⟩ : syracuseStep 2515009 = 1886257) B1886257
theorem B2236481 : Blo 1490065 2236481 := bstep (se 2 (by rfl) ⟨838680, by rfl⟩ : syracuseStep 2236481 = 1677361) B1677361
theorem B1491011 : Blo 1490065 1491011 := bstep (se 1 (by rfl) ⟨1118258, by rfl⟩ : syracuseStep 1491011 = 2236517) B2236517
theorem B2236499 : Blo 1490065 2236499 := bstep (se 1 (by rfl) ⟨1677374, by rfl⟩ : syracuseStep 2236499 = 3354749) B3354749
theorem B1491027 : Blo 1490065 1491027 := bstep (se 1 (by rfl) ⟨1118270, by rfl⟩ : syracuseStep 1491027 = 2236541) B2236541
theorem B2515043 : Blo 1490065 2515043 := bstep (se 1 (by rfl) ⟨1886282, by rfl⟩ : syracuseStep 2515043 = 3772565) B3772565
theorem B1491043 : Blo 1490065 1491043 := bstep (se 1 (by rfl) ⟨1118282, by rfl⟩ : syracuseStep 1491043 = 2236565) B2236565
theorem B2236529 : Blo 1490065 2236529 := bstep (se 2 (by rfl) ⟨838698, by rfl⟩ : syracuseStep 2236529 = 1677397) B1677397
theorem B1491059 : Blo 1490065 1491059 := bstep (se 1 (by rfl) ⟨1118294, by rfl⟩ : syracuseStep 1491059 = 2236589) B2236589
theorem B2236547 : Blo 1490065 2236547 := bstep (se 1 (by rfl) ⟨1677410, by rfl⟩ : syracuseStep 2236547 = 3354821) B3354821
theorem B1491075 : Blo 1490065 1491075 := bstep (se 1 (by rfl) ⟨1118306, by rfl⟩ : syracuseStep 1491075 = 2236613) B2236613
theorem B1491091 : Blo 1490065 1491091 := bstep (se 1 (by rfl) ⟨1118318, by rfl⟩ : syracuseStep 1491091 = 2236637) B2236637
theorem B2236577 : Blo 1490065 2236577 := bstep (se 2 (by rfl) ⟨838716, by rfl⟩ : syracuseStep 2236577 = 1677433) B1677433
theorem B1491107 : Blo 1490065 1491107 := bstep (se 1 (by rfl) ⟨1118330, by rfl⟩ : syracuseStep 1491107 = 2236661) B2236661
theorem B3227825 : Blo 1490065 3227825 := bstep (se 2 (by rfl) ⟨1210434, by rfl⟩ : syracuseStep 3227825 = 2420869) B2420869
theorem B2236595 : Blo 1490065 2236595 := bstep (se 1 (by rfl) ⟨1677446, by rfl⟩ : syracuseStep 2236595 = 3354893) B3354893
theorem B1491123 : Blo 1490065 1491123 := bstep (se 1 (by rfl) ⟨1118342, by rfl⟩ : syracuseStep 1491123 = 2236685) B2236685
theorem B1491139 : Blo 1490065 1491139 := bstep (se 1 (by rfl) ⟨1118354, by rfl⟩ : syracuseStep 1491139 = 2236709) B2236709
theorem B2236625 : Blo 1490065 2236625 := bstep (se 2 (by rfl) ⟨838734, by rfl⟩ : syracuseStep 2236625 = 1677469) B1677469
theorem B2687185 : Blo 1490065 2687185 := bstep (se 2 (by rfl) ⟨1007694, by rfl⟩ : syracuseStep 2687185 = 2015389) B2015389
theorem B1491155 : Blo 1490065 1491155 := bstep (se 1 (by rfl) ⟨1118366, by rfl⟩ : syracuseStep 1491155 = 2236733) B2236733
theorem B2515171 : Blo 1490065 2515171 := bstep (se 1 (by rfl) ⟨1886378, by rfl⟩ : syracuseStep 2515171 = 3772757) B3772757
theorem B2236643 : Blo 1490065 2236643 := bstep (se 1 (by rfl) ⟨1677482, by rfl⟩ : syracuseStep 2236643 = 3354965) B3354965
theorem B1491171 : Blo 1490065 1491171 := bstep (se 1 (by rfl) ⟨1118378, by rfl⟩ : syracuseStep 1491171 = 2236757) B2236757
theorem B1491187 : Blo 1490065 1491187 := bstep (se 1 (by rfl) ⟨1118390, by rfl⟩ : syracuseStep 1491187 = 2236781) B2236781
theorem B2236673 : Blo 1490065 2236673 := bstep (se 2 (by rfl) ⟨838752, by rfl⟩ : syracuseStep 2236673 = 1677505) B1677505
theorem B4243715 : Blo 1490065 4243715 := bstep (se 1 (by rfl) ⟨3182786, by rfl⟩ : syracuseStep 4243715 = 6365573) B6365573
theorem B1491203 : Blo 1490065 1491203 := bstep (se 1 (by rfl) ⟨1118402, by rfl⟩ : syracuseStep 1491203 = 2236805) B2236805
theorem B2236691 : Blo 1490065 2236691 := bstep (se 1 (by rfl) ⟨1677518, by rfl⟩ : syracuseStep 2236691 = 3355037) B3355037
theorem B1491219 : Blo 1490065 1491219 := bstep (se 1 (by rfl) ⟨1118414, by rfl⟩ : syracuseStep 1491219 = 2236829) B2236829
theorem B1491235 : Blo 1490065 1491235 := bstep (se 1 (by rfl) ⟨1118426, by rfl⟩ : syracuseStep 1491235 = 2236853) B2236853
theorem B2236721 : Blo 1490065 2236721 := bstep (se 2 (by rfl) ⟨838770, by rfl⟩ : syracuseStep 2236721 = 1677541) B1677541
theorem B1491251 : Blo 1490065 1491251 := bstep (se 1 (by rfl) ⟨1118438, by rfl⟩ : syracuseStep 1491251 = 2236877) B2236877
theorem B2122051 : Blo 1490065 2122051 := bstep (se 1 (by rfl) ⟨1591538, by rfl⟩ : syracuseStep 2122051 = 3183077) B3183077
theorem B2236739 : Blo 1490065 2236739 := bstep (se 1 (by rfl) ⟨1677554, by rfl⟩ : syracuseStep 2236739 = 3355109) B3355109
theorem B1491267 : Blo 1490065 1491267 := bstep (se 1 (by rfl) ⟨1118450, by rfl⟩ : syracuseStep 1491267 = 2236901) B2236901
theorem B1491283 : Blo 1490065 1491283 := bstep (se 1 (by rfl) ⟨1118462, by rfl⟩ : syracuseStep 1491283 = 2236925) B2236925
theorem B2236769 : Blo 1490065 2236769 := bstep (se 2 (by rfl) ⟨838788, by rfl⟩ : syracuseStep 2236769 = 1677577) B1677577
theorem B1491299 : Blo 1490065 1491299 := bstep (se 1 (by rfl) ⟨1118474, by rfl⟩ : syracuseStep 1491299 = 2236949) B2236949
theorem B2515313 : Blo 1490065 2515313 := bstep (se 2 (by rfl) ⟨943242, by rfl⟩ : syracuseStep 2515313 = 1886485) B1886485
theorem B2236787 : Blo 1490065 2236787 := bstep (se 1 (by rfl) ⟨1677590, by rfl⟩ : syracuseStep 2236787 = 3355181) B3355181
theorem B1491315 : Blo 1490065 1491315 := bstep (se 1 (by rfl) ⟨1118486, by rfl⟩ : syracuseStep 1491315 = 2236973) B2236973
theorem B1491331 : Blo 1490065 1491331 := bstep (se 1 (by rfl) ⟨1118498, by rfl⟩ : syracuseStep 1491331 = 2236997) B2236997
theorem B2236817 : Blo 1490065 2236817 := bstep (se 2 (by rfl) ⟨838806, by rfl⟩ : syracuseStep 2236817 = 1677613) B1677613
theorem B1491347 : Blo 1490065 1491347 := bstep (se 1 (by rfl) ⟨1118510, by rfl⟩ : syracuseStep 1491347 = 2237021) B2237021
theorem B2236835 : Blo 1490065 2236835 := bstep (se 1 (by rfl) ⟨1677626, by rfl⟩ : syracuseStep 2236835 = 3355253) B3355253
theorem B1491363 : Blo 1490065 1491363 := bstep (se 1 (by rfl) ⟨1118522, by rfl⟩ : syracuseStep 1491363 = 2237045) B2237045
theorem B1491379 : Blo 1490065 1491379 := bstep (se 1 (by rfl) ⟨1118534, by rfl⟩ : syracuseStep 1491379 = 2237069) B2237069
theorem B2236865 : Blo 1490065 2236865 := bstep (se 2 (by rfl) ⟨838824, by rfl⟩ : syracuseStep 2236865 = 1677649) B1677649
theorem B1491395 : Blo 1490065 1491395 := bstep (se 1 (by rfl) ⟨1118546, by rfl⟩ : syracuseStep 1491395 = 2237093) B2237093
theorem B14336453 : Blo 1490065 14336453 := bstep (se 4 (by rfl) ⟨1344042, by rfl⟩ : syracuseStep 14336453 = 2688085) B2688085
theorem B2236883 : Blo 1490065 2236883 := bstep (se 1 (by rfl) ⟨1677662, by rfl⟩ : syracuseStep 2236883 = 3355325) B3355325
theorem B1491411 : Blo 1490065 1491411 := bstep (se 1 (by rfl) ⟨1118558, by rfl⟩ : syracuseStep 1491411 = 2237117) B2237117
theorem B1491427 : Blo 1490065 1491427 := bstep (se 1 (by rfl) ⟨1118570, by rfl⟩ : syracuseStep 1491427 = 2237141) B2237141
theorem B2515441 : Blo 1490065 2515441 := bstep (se 2 (by rfl) ⟨943290, by rfl⟩ : syracuseStep 2515441 = 1886581) B1886581
theorem B2236913 : Blo 1490065 2236913 := bstep (se 2 (by rfl) ⟨838842, by rfl⟩ : syracuseStep 2236913 = 1677685) B1677685
theorem B1491443 : Blo 1490065 1491443 := bstep (se 1 (by rfl) ⟨1118582, by rfl⟩ : syracuseStep 1491443 = 2237165) B2237165
theorem B2236931 : Blo 1490065 2236931 := bstep (se 1 (by rfl) ⟨1677698, by rfl⟩ : syracuseStep 2236931 = 3355397) B3355397
theorem B1491459 : Blo 1490065 1491459 := bstep (se 1 (by rfl) ⟨1118594, by rfl⟩ : syracuseStep 1491459 = 2237189) B2237189
theorem B2515475 : Blo 1490065 2515475 := bstep (se 1 (by rfl) ⟨1886606, by rfl⟩ : syracuseStep 2515475 = 3773213) B3773213
theorem B1491475 : Blo 1490065 1491475 := bstep (se 1 (by rfl) ⟨1118606, by rfl⟩ : syracuseStep 1491475 = 2237213) B2237213
theorem B2236961 : Blo 1490065 2236961 := bstep (se 2 (by rfl) ⟨838860, by rfl⟩ : syracuseStep 2236961 = 1677721) B1677721
theorem B1491491 : Blo 1490065 1491491 := bstep (se 1 (by rfl) ⟨1118618, by rfl⟩ : syracuseStep 1491491 = 2237237) B2237237
theorem B2687537 : Blo 1490065 2687537 := bstep (se 2 (by rfl) ⟨1007826, by rfl⟩ : syracuseStep 2687537 = 2015653) B2015653
theorem B2236979 : Blo 1490065 2236979 := bstep (se 1 (by rfl) ⟨1677734, by rfl⟩ : syracuseStep 2236979 = 3355469) B3355469
theorem B31007285 : Blo 1490065 31007285 := bstep (se 5 (by rfl) ⟨1453466, by rfl⟩ : syracuseStep 31007285 = 2906933) B2906933
theorem B1491507 : Blo 1490065 1491507 := bstep (se 1 (by rfl) ⟨1118630, by rfl⟩ : syracuseStep 1491507 = 2237261) B2237261
theorem B1491523 : Blo 1490065 1491523 := bstep (se 1 (by rfl) ⟨1118642, by rfl⟩ : syracuseStep 1491523 = 2237285) B2237285
theorem B11330117 : Blo 1490065 11330117 := bstep (se 4 (by rfl) ⟨1062198, by rfl⟩ : syracuseStep 11330117 = 2124397) B2124397
theorem B5030477 : Blo 1490065 5030477 := bstep (se 3 (by rfl) ⟨943214, by rfl⟩ : syracuseStep 5030477 = 1886429) B1886429
theorem B2237009 : Blo 1490065 2237009 := bstep (se 2 (by rfl) ⟨838878, by rfl⟩ : syracuseStep 2237009 = 1677757) B1677757
theorem B1491539 : Blo 1490065 1491539 := bstep (se 1 (by rfl) ⟨1118654, by rfl⟩ : syracuseStep 1491539 = 2237309) B2237309
theorem B2237027 : Blo 1490065 2237027 := bstep (se 1 (by rfl) ⟨1677770, by rfl⟩ : syracuseStep 2237027 = 3355541) B3355541
theorem B1491555 : Blo 1490065 1491555 := bstep (se 1 (by rfl) ⟨1118666, by rfl⟩ : syracuseStep 1491555 = 2237333) B2237333
theorem B3580529 : Blo 1490065 3580529 := bstep (se 2 (by rfl) ⟨1342698, by rfl⟩ : syracuseStep 3580529 = 2685397) B2685397
theorem B1491571 : Blo 1490065 1491571 := bstep (se 1 (by rfl) ⟨1118678, by rfl⟩ : syracuseStep 1491571 = 2237357) B2237357
theorem B2237057 : Blo 1490065 2237057 := bstep (se 2 (by rfl) ⟨838896, by rfl⟩ : syracuseStep 2237057 = 1677793) B1677793
theorem B5030531 : Blo 1490065 5030531 := bstep (se 1 (by rfl) ⟨3772898, by rfl⟩ : syracuseStep 5030531 = 7545797) B7545797
theorem B1491587 : Blo 1490065 1491587 := bstep (se 1 (by rfl) ⟨1118690, by rfl⟩ : syracuseStep 1491587 = 2237381) B2237381
theorem B2515603 : Blo 1490065 2515603 := bstep (se 1 (by rfl) ⟨1886702, by rfl⟩ : syracuseStep 2515603 = 3773405) B3773405
theorem B2237075 : Blo 1490065 2237075 := bstep (se 1 (by rfl) ⟨1677806, by rfl⟩ : syracuseStep 2237075 = 3355613) B3355613
theorem B1491603 : Blo 1490065 1491603 := bstep (se 1 (by rfl) ⟨1118702, by rfl⟩ : syracuseStep 1491603 = 2237405) B2237405
theorem B1491619 : Blo 1490065 1491619 := bstep (se 1 (by rfl) ⟨1118714, by rfl⟩ : syracuseStep 1491619 = 2237429) B2237429
theorem B2237105 : Blo 1490065 2237105 := bstep (se 2 (by rfl) ⟨838914, by rfl⟩ : syracuseStep 2237105 = 1677829) B1677829
theorem B1491635 : Blo 1490065 1491635 := bstep (se 1 (by rfl) ⟨1118726, by rfl⟩ : syracuseStep 1491635 = 2237453) B2237453
theorem B2908867 : Blo 1490065 2908867 := bstep (se 1 (by rfl) ⟨2181650, by rfl⟩ : syracuseStep 2908867 = 4363301) B4363301
theorem B2237123 : Blo 1490065 2237123 := bstep (se 1 (by rfl) ⟨1677842, by rfl⟩ : syracuseStep 2237123 = 3355685) B3355685
theorem B1491651 : Blo 1490065 1491651 := bstep (se 1 (by rfl) ⟨1118738, by rfl⟩ : syracuseStep 1491651 = 2237477) B2237477
theorem B1491667 : Blo 1490065 1491667 := bstep (se 1 (by rfl) ⟨1118750, by rfl⟩ : syracuseStep 1491667 = 2237501) B2237501
theorem B2237153 : Blo 1490065 2237153 := bstep (se 2 (by rfl) ⟨838932, by rfl⟩ : syracuseStep 2237153 = 1677865) B1677865
theorem B1491683 : Blo 1490065 1491683 := bstep (se 1 (by rfl) ⟨1118762, by rfl⟩ : syracuseStep 1491683 = 2237525) B2237525
theorem B4301549 : Blo 1490065 4301549 := bstep (se 3 (by rfl) ⟨806540, by rfl⟩ : syracuseStep 4301549 = 1613081) B1613081
theorem B2237171 : Blo 1490065 2237171 := bstep (se 1 (by rfl) ⟨1677878, by rfl⟩ : syracuseStep 2237171 = 3355757) B3355757
theorem B1491699 : Blo 1490065 1491699 := bstep (se 1 (by rfl) ⟨1118774, by rfl⟩ : syracuseStep 1491699 = 2237549) B2237549
theorem B1491715 : Blo 1490065 1491715 := bstep (se 1 (by rfl) ⟨1118786, by rfl⟩ : syracuseStep 1491715 = 2237573) B2237573
theorem B2237201 : Blo 1490065 2237201 := bstep (se 2 (by rfl) ⟨838950, by rfl⟩ : syracuseStep 2237201 = 1677901) B1677901
theorem B1491731 : Blo 1490065 1491731 := bstep (se 1 (by rfl) ⟨1118798, by rfl⟩ : syracuseStep 1491731 = 2237597) B2237597
theorem B2122529 : Blo 1490065 2122529 := bstep (se 2 (by rfl) ⟨795948, by rfl⟩ : syracuseStep 2122529 = 1591897) B1591897
theorem B2515745 : Blo 1490065 2515745 := bstep (se 2 (by rfl) ⟨943404, by rfl⟩ : syracuseStep 2515745 = 1886809) B1886809
theorem B7545635 : Blo 1490065 7545635 := bstep (se 1 (by rfl) ⟨5659226, by rfl⟩ : syracuseStep 7545635 = 11318453) B11318453
theorem B2237219 : Blo 1490065 2237219 := bstep (se 1 (by rfl) ⟨1677914, by rfl⟩ : syracuseStep 2237219 = 3355829) B3355829
theorem B1491747 : Blo 1490065 1491747 := bstep (se 1 (by rfl) ⟨1118810, by rfl⟩ : syracuseStep 1491747 = 2237621) B2237621
theorem B1491763 : Blo 1490065 1491763 := bstep (se 1 (by rfl) ⟨1118822, by rfl⟩ : syracuseStep 1491763 = 2237645) B2237645
theorem B2237249 : Blo 1490065 2237249 := bstep (se 2 (by rfl) ⟨838968, by rfl⟩ : syracuseStep 2237249 = 1677937) B1677937
theorem B1491779 : Blo 1490065 1491779 := bstep (se 1 (by rfl) ⟨1118834, by rfl⟩ : syracuseStep 1491779 = 2237669) B2237669
theorem B2237267 : Blo 1490065 2237267 := bstep (se 1 (by rfl) ⟨1677950, by rfl⟩ : syracuseStep 2237267 = 3355901) B3355901
theorem B1491795 : Blo 1490065 1491795 := bstep (se 1 (by rfl) ⟨1118846, by rfl⟩ : syracuseStep 1491795 = 2237693) B2237693
theorem B1491811 : Blo 1490065 1491811 := bstep (se 1 (by rfl) ⟨1118858, by rfl⟩ : syracuseStep 1491811 = 2237717) B2237717
theorem B2237297 : Blo 1490065 2237297 := bstep (se 2 (by rfl) ⟨838986, by rfl⟩ : syracuseStep 2237297 = 1677973) B1677973
theorem B1491827 : Blo 1490065 1491827 := bstep (se 1 (by rfl) ⟨1118870, by rfl⟩ : syracuseStep 1491827 = 2237741) B2237741
theorem B2237315 : Blo 1490065 2237315 := bstep (se 1 (by rfl) ⟨1677986, by rfl⟩ : syracuseStep 2237315 = 3355973) B3355973
theorem B1491843 : Blo 1490065 1491843 := bstep (se 1 (by rfl) ⟨1118882, by rfl⟩ : syracuseStep 1491843 = 2237765) B2237765
theorem B5030801 : Blo 1490065 5030801 := bstep (se 2 (by rfl) ⟨1886550, by rfl⟩ : syracuseStep 5030801 = 3773101) B3773101
theorem B2122643 : Blo 1490065 2122643 := bstep (se 1 (by rfl) ⟨1591982, by rfl⟩ : syracuseStep 2122643 = 3183965) B3183965
theorem B1491859 : Blo 1490065 1491859 := bstep (se 1 (by rfl) ⟨1118894, by rfl⟩ : syracuseStep 1491859 = 2237789) B2237789
theorem B2515873 : Blo 1490065 2515873 := bstep (se 2 (by rfl) ⟨943452, by rfl⟩ : syracuseStep 2515873 = 1886905) B1886905
theorem B2237345 : Blo 1490065 2237345 := bstep (se 2 (by rfl) ⟨839004, by rfl⟩ : syracuseStep 2237345 = 1678009) B1678009
theorem B1491875 : Blo 1490065 1491875 := bstep (se 1 (by rfl) ⟨1118906, by rfl⟩ : syracuseStep 1491875 = 2237813) B2237813
theorem B2237363 : Blo 1490065 2237363 := bstep (se 1 (by rfl) ⟨1678022, by rfl⟩ : syracuseStep 2237363 = 3356045) B3356045
theorem B1491891 : Blo 1490065 1491891 := bstep (se 1 (by rfl) ⟨1118918, by rfl⟩ : syracuseStep 1491891 = 2237837) B2237837
theorem B2515907 : Blo 1490065 2515907 := bstep (se 1 (by rfl) ⟨1886930, by rfl⟩ : syracuseStep 2515907 = 3773861) B3773861
theorem B1491907 : Blo 1490065 1491907 := bstep (se 1 (by rfl) ⟨1118930, by rfl⟩ : syracuseStep 1491907 = 2237861) B2237861
theorem B2237393 : Blo 1490065 2237393 := bstep (se 2 (by rfl) ⟨839022, by rfl⟩ : syracuseStep 2237393 = 1678045) B1678045
theorem B1491923 : Blo 1490065 1491923 := bstep (se 1 (by rfl) ⟨1118942, by rfl⟩ : syracuseStep 1491923 = 2237885) B2237885
theorem B2122723 : Blo 1490065 2122723 := bstep (se 1 (by rfl) ⟨1592042, by rfl⟩ : syracuseStep 2122723 = 3184085) B3184085
theorem B2237411 : Blo 1490065 2237411 := bstep (se 1 (by rfl) ⟨1678058, by rfl⟩ : syracuseStep 2237411 = 3356117) B3356117
theorem B1491939 : Blo 1490065 1491939 := bstep (se 1 (by rfl) ⟨1118954, by rfl⟩ : syracuseStep 1491939 = 2237909) B2237909
theorem B1491955 : Blo 1490065 1491955 := bstep (se 1 (by rfl) ⟨1118966, by rfl⟩ : syracuseStep 1491955 = 2237933) B2237933
theorem B2237441 : Blo 1490065 2237441 := bstep (se 2 (by rfl) ⟨839040, by rfl⟩ : syracuseStep 2237441 = 1678081) B1678081
theorem B4842499 : Blo 1490065 4842499 := bstep (se 1 (by rfl) ⟨3631874, by rfl⟩ : syracuseStep 4842499 = 7263749) B7263749
theorem B1491971 : Blo 1490065 1491971 := bstep (se 1 (by rfl) ⟨1118978, by rfl⟩ : syracuseStep 1491971 = 2237957) B2237957
theorem B6366221 : Blo 1490065 6366221 := bstep (se 3 (by rfl) ⟨1193666, by rfl⟩ : syracuseStep 6366221 = 2387333) B2387333
theorem B2237459 : Blo 1490065 2237459 := bstep (se 1 (by rfl) ⟨1678094, by rfl⟩ : syracuseStep 2237459 = 3356189) B3356189
theorem B1491987 : Blo 1490065 1491987 := bstep (se 1 (by rfl) ⟨1118990, by rfl⟩ : syracuseStep 1491987 = 2237981) B2237981
theorem B1492003 : Blo 1490065 1492003 := bstep (se 1 (by rfl) ⟨1119002, by rfl⟩ : syracuseStep 1492003 = 2238005) B2238005
theorem B2237489 : Blo 1490065 2237489 := bstep (se 2 (by rfl) ⟨839058, by rfl⟩ : syracuseStep 2237489 = 1678117) B1678117
theorem B1492019 : Blo 1490065 1492019 := bstep (se 1 (by rfl) ⟨1119014, by rfl⟩ : syracuseStep 1492019 = 2238029) B2238029
theorem B2516035 : Blo 1490065 2516035 := bstep (se 1 (by rfl) ⟨1887026, by rfl⟩ : syracuseStep 2516035 = 3774053) B3774053
theorem B2237507 : Blo 1490065 2237507 := bstep (se 1 (by rfl) ⟨1678130, by rfl⟩ : syracuseStep 2237507 = 3356261) B3356261
theorem B1492035 : Blo 1490065 1492035 := bstep (se 1 (by rfl) ⟨1119026, by rfl⟩ : syracuseStep 1492035 = 2238053) B2238053
theorem B4244557 : Blo 1490065 4244557 := bstep (se 3 (by rfl) ⟨795854, by rfl⟩ : syracuseStep 4244557 = 1591709) B1591709
theorem B1492051 : Blo 1490065 1492051 := bstep (se 1 (by rfl) ⟨1119038, by rfl⟩ : syracuseStep 1492051 = 2238077) B2238077
theorem B2237537 : Blo 1490065 2237537 := bstep (se 2 (by rfl) ⟨839076, by rfl⟩ : syracuseStep 2237537 = 1678153) B1678153
theorem B5661809 : Blo 1490065 5661809 := bstep (se 2 (by rfl) ⟨2123178, by rfl⟩ : syracuseStep 5661809 = 4246357) B4246357
theorem B2237555 : Blo 1490065 2237555 := bstep (se 1 (by rfl) ⟨1678166, by rfl⟩ : syracuseStep 2237555 = 3356333) B3356333
theorem B2237585 : Blo 1490065 2237585 := bstep (se 2 (by rfl) ⟨839094, by rfl⟩ : syracuseStep 2237585 = 1678189) B1678189
theorem B2237603 : Blo 1490065 2237603 := bstep (se 1 (by rfl) ⟨1678202, by rfl⟩ : syracuseStep 2237603 = 3356405) B3356405
theorem B2237633 : Blo 1490065 2237633 := bstep (se 2 (by rfl) ⟨839112, by rfl⟩ : syracuseStep 2237633 = 1678225) B1678225
theorem B9684173 : Blo 1490065 9684173 := bstep (se 3 (by rfl) ⟨1815782, by rfl⟩ : syracuseStep 9684173 = 3631565) B3631565
theorem B2516177 : Blo 1490065 2516177 := bstep (se 2 (by rfl) ⟨943566, by rfl⟩ : syracuseStep 2516177 = 1887133) B1887133
theorem B2237651 : Blo 1490065 2237651 := bstep (se 1 (by rfl) ⟨1678238, by rfl⟩ : syracuseStep 2237651 = 3356477) B3356477
theorem B4244717 : Blo 1490065 4244717 := bstep (se 3 (by rfl) ⟨795884, by rfl⟩ : syracuseStep 4244717 = 1591769) B1591769
theorem B10200305 : Blo 1490065 10200305 := bstep (se 2 (by rfl) ⟨3825114, by rfl⟩ : syracuseStep 10200305 = 7650229) B7650229
theorem B2237681 : Blo 1490065 2237681 := bstep (se 2 (by rfl) ⟨839130, by rfl⟩ : syracuseStep 2237681 = 1678261) B1678261
theorem B3228931 : Blo 1490065 3228931 := bstep (se 1 (by rfl) ⟨2421698, by rfl⟩ : syracuseStep 3228931 = 4843397) B4843397
theorem B2237699 : Blo 1490065 2237699 := bstep (se 1 (by rfl) ⟨1678274, by rfl⟩ : syracuseStep 2237699 = 3356549) B3356549
theorem B4195601 : Blo 1490065 4195601 := bstep (se 2 (by rfl) ⟨1573350, by rfl⟩ : syracuseStep 4195601 = 3146701) B3146701
theorem B2237729 : Blo 1490065 2237729 := bstep (se 2 (by rfl) ⟨839148, by rfl⟩ : syracuseStep 2237729 = 1678297) B1678297
theorem B2237747 : Blo 1490065 2237747 := bstep (se 1 (by rfl) ⟨1678310, by rfl⟩ : syracuseStep 2237747 = 3356621) B3356621
theorem B2516305 : Blo 1490065 2516305 := bstep (se 2 (by rfl) ⟨943614, by rfl⟩ : syracuseStep 2516305 = 1887229) B1887229
theorem B2237777 : Blo 1490065 2237777 := bstep (se 2 (by rfl) ⟨839166, by rfl⟩ : syracuseStep 2237777 = 1678333) B1678333
theorem B6366563 : Blo 1490065 6366563 := bstep (se 1 (by rfl) ⟨4774922, by rfl⟩ : syracuseStep 6366563 = 9549845) B9549845
theorem B2237795 : Blo 1490065 2237795 := bstep (se 1 (by rfl) ⟨1678346, by rfl⟩ : syracuseStep 2237795 = 3356693) B3356693
theorem B2516339 : Blo 1490065 2516339 := bstep (se 1 (by rfl) ⟨1887254, by rfl⟩ : syracuseStep 2516339 = 3774509) B3774509
theorem B2237825 : Blo 1490065 2237825 := bstep (se 2 (by rfl) ⟨839184, by rfl⟩ : syracuseStep 2237825 = 1678369) B1678369
theorem B2237843 : Blo 1490065 2237843 := bstep (se 1 (by rfl) ⟨1678382, by rfl⟩ : syracuseStep 2237843 = 3356765) B3356765
theorem B4244899 : Blo 1490065 4244899 := bstep (se 1 (by rfl) ⟨3183674, by rfl⟩ : syracuseStep 4244899 = 6367349) B6367349
theorem B5031341 : Blo 1490065 5031341 := bstep (se 3 (by rfl) ⟨943376, by rfl⟩ : syracuseStep 5031341 = 1886753) B1886753
theorem B2237873 : Blo 1490065 2237873 := bstep (se 2 (by rfl) ⟨839202, by rfl⟩ : syracuseStep 2237873 = 1678405) B1678405
theorem B2237891 : Blo 1490065 2237891 := bstep (se 1 (by rfl) ⟨1678418, by rfl⟩ : syracuseStep 2237891 = 3356837) B3356837
theorem B2237921 : Blo 1490065 2237921 := bstep (se 2 (by rfl) ⟨839220, by rfl⟩ : syracuseStep 2237921 = 1678441) B1678441
theorem B5031395 : Blo 1490065 5031395 := bstep (se 1 (by rfl) ⟨3773546, by rfl⟩ : syracuseStep 5031395 = 7547093) B7547093
theorem B2516467 : Blo 1490065 2516467 := bstep (se 1 (by rfl) ⟨1887350, by rfl⟩ : syracuseStep 2516467 = 3774701) B3774701
theorem B2237939 : Blo 1490065 2237939 := bstep (se 1 (by rfl) ⟨1678454, by rfl⟩ : syracuseStep 2237939 = 3356909) B3356909
theorem B2123281 : Blo 1490065 2123281 := bstep (se 2 (by rfl) ⟨796230, by rfl⟩ : syracuseStep 2123281 = 1592461) B1592461
theorem B2237969 : Blo 1490065 2237969 := bstep (se 2 (by rfl) ⟨839238, by rfl⟩ : syracuseStep 2237969 = 1678477) B1678477
theorem B2688547 : Blo 1490065 2688547 := bstep (se 1 (by rfl) ⟨2016410, by rfl⟩ : syracuseStep 2688547 = 4032821) B4032821
theorem B2237987 : Blo 1490065 2237987 := bstep (se 1 (by rfl) ⟨1678490, by rfl⟩ : syracuseStep 2237987 = 3356981) B3356981
theorem B2238017 : Blo 1490065 2238017 := bstep (se 2 (by rfl) ⟨839256, by rfl⟩ : syracuseStep 2238017 = 1678513) B1678513
theorem B12740165 : Blo 1490065 12740165 := bstep (se 4 (by rfl) ⟨1194390, by rfl⟩ : syracuseStep 12740165 = 2388781) B2388781
theorem B7546445 : Blo 1490065 7546445 := bstep (se 3 (by rfl) ⟨1414958, by rfl⟩ : syracuseStep 7546445 = 2829917) B2829917
theorem B2238035 : Blo 1490065 2238035 := bstep (se 1 (by rfl) ⟨1678526, by rfl⟩ : syracuseStep 2238035 = 3357053) B3357053
theorem B2238065 : Blo 1490065 2238065 := bstep (se 2 (by rfl) ⟨839274, by rfl⟩ : syracuseStep 2238065 = 1678549) B1678549
theorem B2516609 : Blo 1490065 2516609 := bstep (se 2 (by rfl) ⟨943728, by rfl⟩ : syracuseStep 2516609 = 1887457) B1887457
theorem B2238083 : Blo 1490065 2238083 := bstep (se 1 (by rfl) ⟨1678562, by rfl⟩ : syracuseStep 2238083 = 3357125) B3357125
theorem B2688707 : Blo 1490065 2688707 := bstep (se 1 (by rfl) ⟨2016530, by rfl⟩ : syracuseStep 2688707 = 4033061) B4033061
theorem B5031665 : Blo 1490065 5031665 := bstep (se 2 (by rfl) ⟨1886874, by rfl⟩ : syracuseStep 5031665 = 3773749) B3773749
theorem B2516737 : Blo 1490065 2516737 := bstep (se 2 (by rfl) ⟨943776, by rfl⟩ : syracuseStep 2516737 = 1887553) B1887553
theorem B4777741 : Blo 1490065 4777741 := bstep (se 3 (by rfl) ⟨895826, by rfl⟩ : syracuseStep 4777741 = 1791653) B1791653
theorem B2516771 : Blo 1490065 2516771 := bstep (se 1 (by rfl) ⟨1887578, by rfl⟩ : syracuseStep 2516771 = 3775157) B3775157
theorem B6367025 : Blo 1490065 6367025 := bstep (se 2 (by rfl) ⟨2387634, by rfl⟩ : syracuseStep 6367025 = 4775269) B4775269
theorem B21489461 : Blo 1490065 21489461 := bstep (se 5 (by rfl) ⟨1007318, by rfl⟩ : syracuseStep 21489461 = 2014637) B2014637
theorem B2516899 : Blo 1490065 2516899 := bstep (se 1 (by rfl) ⟨1887674, by rfl⟩ : syracuseStep 2516899 = 3775349) B3775349
theorem B2721809 : Blo 1490065 2721809 := bstep (se 2 (by rfl) ⟨1020678, by rfl⟩ : syracuseStep 2721809 = 2041357) B2041357
theorem B4302883 : Blo 1490065 4302883 := bstep (se 1 (by rfl) ⟨3227162, by rfl⟩ : syracuseStep 4302883 = 6454325) B6454325
theorem B2181169 : Blo 1490065 2181169 := bstep (se 2 (by rfl) ⟨817938, by rfl⟩ : syracuseStep 2181169 = 1635877) B1635877
theorem B2517041 : Blo 1490065 2517041 := bstep (se 2 (by rfl) ⟨943890, by rfl⟩ : syracuseStep 2517041 = 1887781) B1887781
theorem B1886323 : Blo 1490065 1886323 := bstep (se 1 (by rfl) ⟨1414742, by rfl⟩ : syracuseStep 1886323 = 2829485) B2829485
theorem B2517169 : Blo 1490065 2517169 := bstep (se 2 (by rfl) ⟨943938, by rfl⟩ : syracuseStep 2517169 = 1887877) B1887877
theorem B1886419 : Blo 1490065 1886419 := bstep (se 1 (by rfl) ⟨1414814, by rfl⟩ : syracuseStep 1886419 = 2829629) B2829629
theorem B2517203 : Blo 1490065 2517203 := bstep (se 1 (by rfl) ⟨1887902, by rfl⟩ : syracuseStep 2517203 = 3775805) B3775805
theorem B2123987 : Blo 1490065 2123987 := bstep (se 1 (by rfl) ⟨1592990, by rfl⟩ : syracuseStep 2123987 = 3185981) B3185981
theorem B5376227 : Blo 1490065 5376227 := bstep (se 1 (by rfl) ⟨4032170, by rfl⟩ : syracuseStep 5376227 = 8064341) B8064341
theorem B5032205 : Blo 1490065 5032205 := bstep (se 3 (by rfl) ⟨943538, by rfl⟩ : syracuseStep 5032205 = 1887077) B1887077
theorem B3631409 : Blo 1490065 3631409 := bstep (se 2 (by rfl) ⟨1361778, by rfl⟩ : syracuseStep 3631409 = 2723557) B2723557
theorem B5032259 : Blo 1490065 5032259 := bstep (se 1 (by rfl) ⟨3774194, by rfl⟩ : syracuseStep 5032259 = 7548389) B7548389
theorem B3352913 : Blo 1490065 3352913 := bstep (se 2 (by rfl) ⟨1257342, by rfl⟩ : syracuseStep 3352913 = 2514685) B2514685
theorem B2517331 : Blo 1490065 2517331 := bstep (se 1 (by rfl) ⟨1887998, by rfl⟩ : syracuseStep 2517331 = 3775997) B3775997
theorem B3352931 : Blo 1490065 3352931 := bstep (se 1 (by rfl) ⟨2514698, by rfl⟩ : syracuseStep 3352931 = 5029397) B5029397
theorem B7162289 : Blo 1490065 7162289 := bstep (se 2 (by rfl) ⟨2685858, by rfl⟩ : syracuseStep 7162289 = 5371717) B5371717
theorem B8063459 : Blo 1490065 8063459 := bstep (se 1 (by rfl) ⟨6047594, by rfl⟩ : syracuseStep 8063459 = 12095189) B12095189
theorem B2517473 : Blo 1490065 2517473 := bstep (se 2 (by rfl) ⟨944052, by rfl⟩ : syracuseStep 2517473 = 1888105) B1888105
theorem B3582481 : Blo 1490065 3582481 := bstep (se 2 (by rfl) ⟨1343430, by rfl⟩ : syracuseStep 3582481 = 2686861) B2686861
theorem B5663267 : Blo 1490065 5663267 := bstep (se 1 (by rfl) ⟨4247450, by rfl⟩ : syracuseStep 5663267 = 8494901) B8494901
theorem B1591859 : Blo 1490065 1591859 := bstep (se 1 (by rfl) ⟨1193894, by rfl⟩ : syracuseStep 1591859 = 2387789) B2387789
theorem B5032529 : Blo 1490065 5032529 := bstep (se 2 (by rfl) ⟨1887198, by rfl⟩ : syracuseStep 5032529 = 3774397) B3774397
theorem B2517601 : Blo 1490065 2517601 := bstep (se 2 (by rfl) ⟨944100, by rfl⟩ : syracuseStep 2517601 = 1888201) B1888201
theorem B3353201 : Blo 1490065 3353201 := bstep (se 2 (by rfl) ⟨1257450, by rfl⟩ : syracuseStep 3353201 = 2514901) B2514901
theorem B3353219 : Blo 1490065 3353219 := bstep (se 1 (by rfl) ⟨2514914, by rfl⟩ : syracuseStep 3353219 = 5029829) B5029829
theorem B2517635 : Blo 1490065 2517635 := bstep (se 1 (by rfl) ⟨1888226, by rfl⟩ : syracuseStep 2517635 = 3776453) B3776453
theorem B2828945 : Blo 1490065 2828945 := bstep (se 2 (by rfl) ⟨1060854, by rfl⟩ : syracuseStep 2828945 = 2121709) B2121709
theorem B5376689 : Blo 1490065 5376689 := bstep (se 2 (by rfl) ⟨2016258, by rfl⟩ : syracuseStep 5376689 = 4032517) B4032517
theorem B1886915 : Blo 1490065 1886915 := bstep (se 1 (by rfl) ⟨1415186, by rfl⟩ : syracuseStep 1886915 = 2830373) B2830373
theorem B2517763 : Blo 1490065 2517763 := bstep (se 1 (by rfl) ⟨1888322, by rfl⟩ : syracuseStep 2517763 = 3776645) B3776645
theorem B4246289 : Blo 1490065 4246289 := bstep (se 2 (by rfl) ⟨1592358, by rfl⟩ : syracuseStep 4246289 = 3184717) B3184717
theorem B27200369 : Blo 1490065 27200369 := bstep (se 2 (by rfl) ⟨10200138, by rfl⟩ : syracuseStep 27200369 = 20400277) B20400277
theorem B3353489 : Blo 1490065 3353489 := bstep (se 2 (by rfl) ⟨1257558, by rfl⟩ : syracuseStep 3353489 = 2515117) B2515117
theorem B5098403 : Blo 1490065 5098403 := bstep (se 1 (by rfl) ⟨3823802, by rfl⟩ : syracuseStep 5098403 = 7647605) B7647605
theorem B3353507 : Blo 1490065 3353507 := bstep (se 1 (by rfl) ⟨2515130, by rfl⟩ : syracuseStep 3353507 = 5030261) B5030261
theorem B3582883 : Blo 1490065 3582883 := bstep (se 1 (by rfl) ⟨2687162, by rfl⟩ : syracuseStep 3582883 = 5374325) B5374325
theorem B12094435 : Blo 1490065 12094435 := bstep (se 1 (by rfl) ⟨9070826, by rfl⟩ : syracuseStep 12094435 = 18141653) B18141653
theorem B2583587 : Blo 1490065 2583587 := bstep (se 1 (by rfl) ⟨1937690, by rfl⟩ : syracuseStep 2583587 = 3875381) B3875381
theorem B5033069 : Blo 1490065 5033069 := bstep (se 3 (by rfl) ⟨943700, by rfl⟩ : syracuseStep 5033069 = 1887401) B1887401
theorem B5033123 : Blo 1490065 5033123 := bstep (se 1 (by rfl) ⟨3774842, by rfl⟩ : syracuseStep 5033123 = 7549685) B7549685
theorem B9071779 : Blo 1490065 9071779 := bstep (se 1 (by rfl) ⟨6803834, by rfl⟩ : syracuseStep 9071779 = 13607669) B13607669
theorem B3353777 : Blo 1490065 3353777 := bstep (se 2 (by rfl) ⟨1257666, by rfl⟩ : syracuseStep 3353777 = 2515333) B2515333
theorem B3353795 : Blo 1490065 3353795 := bstep (se 1 (by rfl) ⟨2515346, by rfl⟩ : syracuseStep 3353795 = 5030693) B5030693
theorem B5098787 : Blo 1490065 5098787 := bstep (se 1 (by rfl) ⟨3824090, by rfl⟩ : syracuseStep 5098787 = 7648181) B7648181
theorem B2829667 : Blo 1490065 2829667 := bstep (se 1 (by rfl) ⟨2122250, by rfl⟩ : syracuseStep 2829667 = 4244501) B4244501
theorem B11324771 : Blo 1490065 11324771 := bstep (se 1 (by rfl) ⟨8493578, by rfl⟩ : syracuseStep 11324771 = 16987157) B16987157
theorem B1887619 : Blo 1490065 1887619 := bstep (se 1 (by rfl) ⟨1415714, by rfl⟩ : syracuseStep 1887619 = 2831429) B2831429
theorem B5033393 : Blo 1490065 5033393 := bstep (se 2 (by rfl) ⟨1887522, by rfl⟩ : syracuseStep 5033393 = 3775045) B3775045
theorem B3354065 : Blo 1490065 3354065 := bstep (se 2 (by rfl) ⟨1257774, by rfl⟩ : syracuseStep 3354065 = 2515549) B2515549
theorem B3354083 : Blo 1490065 3354083 := bstep (se 1 (by rfl) ⟨2515562, by rfl⟩ : syracuseStep 3354083 = 5031125) B5031125
theorem B1887715 : Blo 1490065 1887715 := bstep (se 1 (by rfl) ⟨1415786, by rfl⟩ : syracuseStep 1887715 = 2831573) B2831573
theorem B5664269 : Blo 1490065 5664269 := bstep (se 3 (by rfl) ⟨1062050, by rfl⟩ : syracuseStep 5664269 = 2124101) B2124101
theorem B4779587 : Blo 1490065 4779587 := bstep (se 1 (by rfl) ⟨3584690, by rfl⟩ : syracuseStep 4779587 = 7169381) B7169381
theorem B16985699 : Blo 1490065 16985699 := bstep (se 1 (by rfl) ⟨12739274, by rfl⟩ : syracuseStep 16985699 = 25478549) B25478549
theorem B2043505 : Blo 1490065 2043505 := bstep (se 2 (by rfl) ⟨766314, by rfl⟩ : syracuseStep 2043505 = 1532629) B1532629
theorem B12086981 : Blo 1490065 12086981 := bstep (se 4 (by rfl) ⟨1133154, by rfl⟩ : syracuseStep 12086981 = 2266309) B2266309
theorem B4247245 : Blo 1490065 4247245 := bstep (se 3 (by rfl) ⟨796358, by rfl⟩ : syracuseStep 4247245 = 1592717) B1592717
theorem B3354353 : Blo 1490065 3354353 := bstep (se 2 (by rfl) ⟨1257882, by rfl⟩ : syracuseStep 3354353 = 2515765) B2515765
theorem B3354371 : Blo 1490065 3354371 := bstep (se 1 (by rfl) ⟨2515778, by rfl⟩ : syracuseStep 3354371 = 5031557) B5031557
theorem B2830115 : Blo 1490065 2830115 := bstep (se 1 (by rfl) ⟨2122586, by rfl⟩ : syracuseStep 2830115 = 4245173) B4245173
theorem B8064845 : Blo 1490065 8064845 := bstep (se 3 (by rfl) ⟨1512158, by rfl⟩ : syracuseStep 8064845 = 3024317) B3024317
theorem B3772241 : Blo 1490065 3772241 := bstep (se 2 (by rfl) ⟨1414590, by rfl⟩ : syracuseStep 3772241 = 2829181) B2829181
theorem B19107683 : Blo 1490065 19107683 := bstep (se 1 (by rfl) ⟨14330762, by rfl⟩ : syracuseStep 19107683 = 28661525) B28661525
theorem B3772291 : Blo 1490065 3772291 := bstep (se 1 (by rfl) ⟨2829218, by rfl⟩ : syracuseStep 3772291 = 5658437) B5658437
theorem B4247473 : Blo 1490065 4247473 := bstep (se 2 (by rfl) ⟨1592802, by rfl⟩ : syracuseStep 4247473 = 3185605) B3185605
theorem B3583921 : Blo 1490065 3583921 := bstep (se 2 (by rfl) ⟨1343970, by rfl⟩ : syracuseStep 3583921 = 2687941) B2687941
theorem B2453441 : Blo 1490065 2453441 := bstep (se 2 (by rfl) ⟨920040, by rfl⟩ : syracuseStep 2453441 = 1840081) B1840081
theorem B5033933 : Blo 1490065 5033933 := bstep (se 3 (by rfl) ⟨943862, by rfl⟩ : syracuseStep 5033933 = 1887725) B1887725
theorem B4779985 : Blo 1490065 4779985 := bstep (se 2 (by rfl) ⟨1792494, by rfl⟩ : syracuseStep 4779985 = 3584989) B3584989
theorem B1888211 : Blo 1490065 1888211 := bstep (se 1 (by rfl) ⟨1416158, by rfl⟩ : syracuseStep 1888211 = 2832317) B2832317
theorem B5033987 : Blo 1490065 5033987 := bstep (se 1 (by rfl) ⟨3775490, by rfl⟩ : syracuseStep 5033987 = 7550981) B7550981
theorem B3772433 : Blo 1490065 3772433 := bstep (se 2 (by rfl) ⟨1414662, by rfl⟩ : syracuseStep 3772433 = 2829325) B2829325
theorem B3354641 : Blo 1490065 3354641 := bstep (se 2 (by rfl) ⟨1257990, by rfl⟩ : syracuseStep 3354641 = 2515981) B2515981
theorem B3354659 : Blo 1490065 3354659 := bstep (se 1 (by rfl) ⟨2515994, by rfl⟩ : syracuseStep 3354659 = 5031989) B5031989
theorem B6983729 : Blo 1490065 6983729 := bstep (se 2 (by rfl) ⟨2618898, by rfl⟩ : syracuseStep 6983729 = 5237797) B5237797
theorem B28643381 : Blo 1490065 28643381 := bstep (se 5 (by rfl) ⟨1342658, by rfl⟩ : syracuseStep 28643381 = 2685317) B2685317
theorem B2830403 : Blo 1490065 2830403 := bstep (se 1 (by rfl) ⟨2122802, by rfl⟩ : syracuseStep 2830403 = 4245605) B4245605
theorem B4247633 : Blo 1490065 4247633 := bstep (se 2 (by rfl) ⟨1592862, by rfl⟩ : syracuseStep 4247633 = 3185725) B3185725
theorem B4247747 : Blo 1490065 4247747 := bstep (se 1 (by rfl) ⟨3185810, by rfl⟩ : syracuseStep 4247747 = 6371621) B6371621
theorem B2388179 : Blo 1490065 2388179 := bstep (se 1 (by rfl) ⟨1791134, by rfl⟩ : syracuseStep 2388179 = 3582269) B3582269
theorem B5034257 : Blo 1490065 5034257 := bstep (se 2 (by rfl) ⟨1887846, by rfl⟩ : syracuseStep 5034257 = 3775693) B3775693
theorem B3354929 : Blo 1490065 3354929 := bstep (se 2 (by rfl) ⟨1258098, by rfl⟩ : syracuseStep 3354929 = 2516197) B2516197
theorem B3354947 : Blo 1490065 3354947 := bstep (se 1 (by rfl) ⟨2516210, by rfl⟩ : syracuseStep 3354947 = 5032421) B5032421
theorem B2388307 : Blo 1490065 2388307 := bstep (se 1 (by rfl) ⟨1791230, by rfl⟩ : syracuseStep 2388307 = 3582461) B3582461
theorem B8065379 : Blo 1490065 8065379 := bstep (se 1 (by rfl) ⟨6049034, by rfl⟩ : syracuseStep 8065379 = 12098069) B12098069
theorem B14332301 : Blo 1490065 14332301 := bstep (se 3 (by rfl) ⟨2687306, by rfl⟩ : syracuseStep 14332301 = 5374613) B5374613
theorem B2388371 : Blo 1490065 2388371 := bstep (se 1 (by rfl) ⟨1791278, by rfl⟩ : syracuseStep 2388371 = 3582557) B3582557
theorem B7549361 : Blo 1490065 7549361 := bstep (se 2 (by rfl) ⟨2831010, by rfl⟩ : syracuseStep 7549361 = 5662021) B5662021
theorem B1790419 : Blo 1490065 1790419 := bstep (se 1 (by rfl) ⟨1342814, by rfl⟩ : syracuseStep 1790419 = 2685629) B2685629
theorem B3355217 : Blo 1490065 3355217 := bstep (se 2 (by rfl) ⟨1258206, by rfl⟩ : syracuseStep 3355217 = 2516413) B2516413
theorem B3355235 : Blo 1490065 3355235 := bstep (se 1 (by rfl) ⟨2516426, by rfl⟩ : syracuseStep 3355235 = 5032853) B5032853
theorem B2265761 : Blo 1490065 2265761 := bstep (se 2 (by rfl) ⟨849660, by rfl⟩ : syracuseStep 2265761 = 1699321) B1699321
theorem B6042289 : Blo 1490065 6042289 := bstep (se 2 (by rfl) ⟨2265858, by rfl⟩ : syracuseStep 6042289 = 4531717) B4531717
theorem B1512227 : Blo 1490065 1512227 := bstep (se 1 (by rfl) ⟨1134170, by rfl⟩ : syracuseStep 1512227 = 2268341) B2268341
theorem B5034797 : Blo 1490065 5034797 := bstep (se 3 (by rfl) ⟨944024, by rfl⟩ : syracuseStep 5034797 = 1888049) B1888049
theorem B7164749 : Blo 1490065 7164749 := bstep (se 3 (by rfl) ⟨1343390, by rfl⟩ : syracuseStep 7164749 = 2686781) B2686781
theorem B5034851 : Blo 1490065 5034851 := bstep (se 1 (by rfl) ⟨3776138, by rfl⟩ : syracuseStep 5034851 = 7552277) B7552277
theorem B4305773 : Blo 1490065 4305773 := bstep (se 3 (by rfl) ⟨807332, by rfl⟩ : syracuseStep 4305773 = 1614665) B1614665
theorem B3355505 : Blo 1490065 3355505 := bstep (se 2 (by rfl) ⟨1258314, by rfl⟩ : syracuseStep 3355505 = 2516629) B2516629
theorem B2388865 : Blo 1490065 2388865 := bstep (se 2 (by rfl) ⟨895824, by rfl⟩ : syracuseStep 2388865 = 1791649) B1791649
theorem B3355523 : Blo 1490065 3355523 := bstep (se 1 (by rfl) ⟨2516642, by rfl⟩ : syracuseStep 3355523 = 5033285) B5033285
theorem B3773425 : Blo 1490065 3773425 := bstep (se 2 (by rfl) ⟨1415034, by rfl⟩ : syracuseStep 3773425 = 2830069) B2830069
theorem B2831345 : Blo 1490065 2831345 := bstep (se 2 (by rfl) ⟨1061754, by rfl⟩ : syracuseStep 2831345 = 2123509) B2123509
theorem B4305923 : Blo 1490065 4305923 := bstep (se 1 (by rfl) ⟨3229442, by rfl⟩ : syracuseStep 4305923 = 6458885) B6458885
theorem B1676371 : Blo 1490065 1676371 := bstep (se 1 (by rfl) ⟨1257278, by rfl⟩ : syracuseStep 1676371 = 2514557) B2514557
theorem B5035121 : Blo 1490065 5035121 := bstep (se 2 (by rfl) ⟨1888170, by rfl⟩ : syracuseStep 5035121 = 3776341) B3776341
theorem B3355793 : Blo 1490065 3355793 := bstep (se 2 (by rfl) ⟨1258422, by rfl⟩ : syracuseStep 3355793 = 2516845) B2516845
theorem B3355811 : Blo 1490065 3355811 := bstep (se 1 (by rfl) ⟨2516858, by rfl⟩ : syracuseStep 3355811 = 5033717) B5033717
theorem B4248749 : Blo 1490065 4248749 := bstep (se 3 (by rfl) ⟨796640, by rfl⟩ : syracuseStep 4248749 = 1593281) B1593281
theorem B1676515 : Blo 1490065 1676515 := bstep (se 1 (by rfl) ⟨1257386, by rfl⟩ : syracuseStep 1676515 = 2514773) B2514773
theorem B3773699 : Blo 1490065 3773699 := bstep (se 1 (by rfl) ⟨2830274, by rfl⟩ : syracuseStep 3773699 = 5660549) B5660549
theorem B9196805 : Blo 1490065 9196805 := bstep (se 4 (by rfl) ⟨862200, by rfl⟩ : syracuseStep 9196805 = 1724401) B1724401
theorem B6370595 : Blo 1490065 6370595 := bstep (se 1 (by rfl) ⟨4777946, by rfl⟩ : syracuseStep 6370595 = 9555893) B9555893
theorem B1676659 : Blo 1490065 1676659 := bstep (se 1 (by rfl) ⟨1257494, by rfl⟩ : syracuseStep 1676659 = 2514989) B2514989
theorem B3356081 : Blo 1490065 3356081 := bstep (se 2 (by rfl) ⟨1258530, by rfl⟩ : syracuseStep 3356081 = 2517061) B2517061
theorem B3184067 : Blo 1490065 3184067 := bstep (se 1 (by rfl) ⟨2388050, by rfl⟩ : syracuseStep 3184067 = 4776101) B4776101
theorem B3773891 : Blo 1490065 3773891 := bstep (se 1 (by rfl) ⟨2830418, by rfl⟩ : syracuseStep 3773891 = 5660837) B5660837
theorem B8492485 : Blo 1490065 8492485 := bstep (se 4 (by rfl) ⟨796170, by rfl⟩ : syracuseStep 8492485 = 1592341) B1592341
theorem B3356099 : Blo 1490065 3356099 := bstep (se 1 (by rfl) ⟨2517074, by rfl⟩ : syracuseStep 3356099 = 5034149) B5034149
theorem B2725315 : Blo 1490065 2725315 := bstep (se 1 (by rfl) ⟨2043986, by rfl⟩ : syracuseStep 2725315 = 4087973) B4087973
theorem B1676803 : Blo 1490065 1676803 := bstep (se 1 (by rfl) ⟨1257602, by rfl⟩ : syracuseStep 1676803 = 2515205) B2515205
theorem B36271637 : Blo 1490065 36271637 := bstep (se 6 (by rfl) ⟨850116, by rfl⟩ : syracuseStep 36271637 = 1700233) B1700233
theorem B2389537 : Blo 1490065 2389537 := bstep (se 2 (by rfl) ⟨896076, by rfl⟩ : syracuseStep 2389537 = 1792153) B1792153
theorem B5101165 : Blo 1490065 5101165 := bstep (se 3 (by rfl) ⟨956468, by rfl⟩ : syracuseStep 5101165 = 1912937) B1912937
theorem B40818289 : Blo 1490065 40818289 := bstep (se 2 (by rfl) ⟨15306858, by rfl⟩ : syracuseStep 40818289 = 30613717) B30613717
theorem B5035661 : Blo 1490065 5035661 := bstep (se 3 (by rfl) ⟨944186, by rfl⟩ : syracuseStep 5035661 = 1888373) B1888373
theorem B1676947 : Blo 1490065 1676947 := bstep (se 1 (by rfl) ⟨1257710, by rfl⟩ : syracuseStep 1676947 = 2515421) B2515421
theorem B5035715 : Blo 1490065 5035715 := bstep (se 1 (by rfl) ⟨3776786, by rfl⟩ : syracuseStep 5035715 = 7553573) B7553573
theorem B6452941 : Blo 1490065 6452941 := bstep (se 3 (by rfl) ⟨1209926, by rfl⟩ : syracuseStep 6452941 = 2419853) B2419853
theorem B3356369 : Blo 1490065 3356369 := bstep (se 2 (by rfl) ⟨1258638, by rfl⟩ : syracuseStep 3356369 = 2517277) B2517277
theorem B3356387 : Blo 1490065 3356387 := bstep (se 1 (by rfl) ⟨2517290, by rfl⟩ : syracuseStep 3356387 = 5034581) B5034581
theorem B4773667 : Blo 1490065 4773667 := bstep (se 1 (by rfl) ⟨3580250, by rfl⟩ : syracuseStep 4773667 = 7160501) B7160501
theorem B1677091 : Blo 1490065 1677091 := bstep (se 1 (by rfl) ⟨1257818, by rfl⟩ : syracuseStep 1677091 = 2515637) B2515637
theorem B7550819 : Blo 1490065 7550819 := bstep (se 1 (by rfl) ⟨5663114, by rfl⟩ : syracuseStep 7550819 = 11326229) B11326229
theorem B2832241 : Blo 1490065 2832241 := bstep (se 2 (by rfl) ⟨1062090, by rfl⟩ : syracuseStep 2832241 = 2124181) B2124181
theorem B1677235 : Blo 1490065 1677235 := bstep (se 1 (by rfl) ⟨1257926, by rfl⟩ : syracuseStep 1677235 = 2515853) B2515853
theorem B9680867 : Blo 1490065 9680867 := bstep (se 1 (by rfl) ⟨7260650, by rfl⟩ : syracuseStep 9680867 = 14521301) B14521301
theorem B3356657 : Blo 1490065 3356657 := bstep (se 2 (by rfl) ⟨1258746, by rfl⟩ : syracuseStep 3356657 = 2517493) B2517493
theorem B3356675 : Blo 1490065 3356675 := bstep (se 1 (by rfl) ⟨2517506, by rfl⟩ : syracuseStep 3356675 = 5035013) B5035013
theorem B2832401 : Blo 1490065 2832401 := bstep (se 2 (by rfl) ⟨1062150, by rfl⟩ : syracuseStep 2832401 = 2124301) B2124301
theorem B4773937 : Blo 1490065 4773937 := bstep (se 2 (by rfl) ⟨1790226, by rfl⟩ : syracuseStep 4773937 = 3580453) B3580453
theorem B21788725 : Blo 1490065 21788725 := bstep (se 5 (by rfl) ⟨1021346, by rfl⟩ : syracuseStep 21788725 = 2042693) B2042693
theorem B1677379 : Blo 1490065 1677379 := bstep (se 1 (by rfl) ⟨1258034, by rfl⟩ : syracuseStep 1677379 = 2516069) B2516069
theorem B1792163 : Blo 1490065 1792163 := bstep (se 1 (by rfl) ⟨1344122, by rfl⟩ : syracuseStep 1792163 = 2688245) B2688245
theorem B1677523 : Blo 1490065 1677523 := bstep (se 1 (by rfl) ⟨1258142, by rfl⟩ : syracuseStep 1677523 = 2516285) B2516285
theorem B2586865 : Blo 1490065 2586865 := bstep (se 2 (by rfl) ⟨970074, by rfl⟩ : syracuseStep 2586865 = 1940149) B1940149
theorem B5658893 : Blo 1490065 5658893 := bstep (se 3 (by rfl) ⟨1061042, by rfl⟩ : syracuseStep 5658893 = 2122085) B2122085
theorem B3356945 : Blo 1490065 3356945 := bstep (se 2 (by rfl) ⟨1258854, by rfl⟩ : syracuseStep 3356945 = 2517709) B2517709
theorem B3356963 : Blo 1490065 3356963 := bstep (se 1 (by rfl) ⟨2517722, by rfl⟩ : syracuseStep 3356963 = 5035445) B5035445
theorem B1677667 : Blo 1490065 1677667 := bstep (se 1 (by rfl) ⟨1258250, by rfl⟩ : syracuseStep 1677667 = 2516501) B2516501
theorem B3774833 : Blo 1490065 3774833 := bstep (se 2 (by rfl) ⟨1415562, by rfl⟩ : syracuseStep 3774833 = 2831125) B2831125
theorem B3774883 : Blo 1490065 3774883 := bstep (se 1 (by rfl) ⟨2831162, by rfl⟩ : syracuseStep 3774883 = 5662325) B5662325
theorem B1677811 : Blo 1490065 1677811 := bstep (se 1 (by rfl) ⟨1258358, by rfl⟩ : syracuseStep 1677811 = 2516717) B2516717
theorem B3775025 : Blo 1490065 3775025 := bstep (se 2 (by rfl) ⟨1415634, by rfl⟩ : syracuseStep 3775025 = 2831269) B2831269
theorem B1677955 : Blo 1490065 1677955 := bstep (se 1 (by rfl) ⟨1258466, by rfl⟩ : syracuseStep 1677955 = 2516933) B2516933
theorem B7551629 : Blo 1490065 7551629 := bstep (se 3 (by rfl) ⟨1415930, by rfl⟩ : syracuseStep 7551629 = 2831861) B2831861
theorem B3185315 : Blo 1490065 3185315 := bstep (se 1 (by rfl) ⟨2388986, by rfl⟩ : syracuseStep 3185315 = 4777973) B4777973
theorem B2235107 : Blo 1490065 2235107 := bstep (se 1 (by rfl) ⟨1676330, by rfl⟩ : syracuseStep 2235107 = 3352661) B3352661
theorem B2235137 : Blo 1490065 2235137 := bstep (se 2 (by rfl) ⟨838176, by rfl⟩ : syracuseStep 2235137 = 1676353) B1676353
theorem B2235155 : Blo 1490065 2235155 := bstep (se 1 (by rfl) ⟨1676366, by rfl⟩ : syracuseStep 2235155 = 3352733) B3352733
theorem B1678099 : Blo 1490065 1678099 := bstep (se 1 (by rfl) ⟨1258574, by rfl⟩ : syracuseStep 1678099 = 2517149) B2517149
theorem B2235185 : Blo 1490065 2235185 := bstep (se 2 (by rfl) ⟨838194, by rfl⟩ : syracuseStep 2235185 = 1676389) B1676389
theorem B2235203 : Blo 1490065 2235203 := bstep (se 1 (by rfl) ⟨1676402, by rfl⟩ : syracuseStep 2235203 = 3352805) B3352805
theorem B2235233 : Blo 1490065 2235233 := bstep (se 2 (by rfl) ⟨838212, by rfl⟩ : syracuseStep 2235233 = 1676425) B1676425
theorem B2235251 : Blo 1490065 2235251 := bstep (se 1 (by rfl) ⟨1676438, by rfl⟩ : syracuseStep 2235251 = 3352877) B3352877
theorem B9689989 : Blo 1490065 9689989 := bstep (se 4 (by rfl) ⟨908436, by rfl⟩ : syracuseStep 9689989 = 1816873) B1816873
theorem B2235281 : Blo 1490065 2235281 := bstep (se 2 (by rfl) ⟨838230, by rfl⟩ : syracuseStep 2235281 = 1676461) B1676461
theorem B2235299 : Blo 1490065 2235299 := bstep (se 1 (by rfl) ⟨1676474, by rfl⟩ : syracuseStep 2235299 = 3352949) B3352949
theorem B1678243 : Blo 1490065 1678243 := bstep (se 1 (by rfl) ⟨1258682, by rfl⟩ : syracuseStep 1678243 = 2517365) B2517365
theorem B2235329 : Blo 1490065 2235329 := bstep (se 2 (by rfl) ⟨838248, by rfl⟩ : syracuseStep 2235329 = 1676497) B1676497
theorem B2235347 : Blo 1490065 2235347 := bstep (se 1 (by rfl) ⟨1676510, by rfl⟩ : syracuseStep 2235347 = 3353021) B3353021
theorem B2235377 : Blo 1490065 2235377 := bstep (se 2 (by rfl) ⟨838266, by rfl⟩ : syracuseStep 2235377 = 1676533) B1676533
theorem B2235395 : Blo 1490065 2235395 := bstep (se 1 (by rfl) ⟨1676546, by rfl⟩ : syracuseStep 2235395 = 3353093) B3353093
theorem B2235425 : Blo 1490065 2235425 := bstep (se 2 (by rfl) ⟨838284, by rfl⟩ : syracuseStep 2235425 = 1676569) B1676569
theorem B2235443 : Blo 1490065 2235443 := bstep (se 1 (by rfl) ⟨1676582, by rfl⟩ : syracuseStep 2235443 = 3353165) B3353165
theorem B1678387 : Blo 1490065 1678387 := bstep (se 1 (by rfl) ⟨1258790, by rfl⟩ : syracuseStep 1678387 = 2517581) B2517581
theorem B2235473 : Blo 1490065 2235473 := bstep (se 2 (by rfl) ⟨838302, by rfl⟩ : syracuseStep 2235473 = 1676605) B1676605
theorem B2235491 : Blo 1490065 2235491 := bstep (se 1 (by rfl) ⟨1676618, by rfl⟩ : syracuseStep 2235491 = 3353237) B3353237
theorem B3021923 : Blo 1490065 3021923 := bstep (se 1 (by rfl) ⟨2266442, by rfl⟩ : syracuseStep 3021923 = 4532885) B4532885
theorem B6798449 : Blo 1490065 6798449 := bstep (se 2 (by rfl) ⟨2549418, by rfl⟩ : syracuseStep 6798449 = 5098837) B5098837
theorem B2235521 : Blo 1490065 2235521 := bstep (se 2 (by rfl) ⟨838320, by rfl⟩ : syracuseStep 2235521 = 1676641) B1676641
theorem B1490067 : Blo 1490065 1490067 := bstep (se 1 (by rfl) ⟨1117550, by rfl⟩ : syracuseStep 1490067 = 2235101) B2235101
theorem B2235539 : Blo 1490065 2235539 := bstep (se 1 (by rfl) ⟨1676654, by rfl⟩ : syracuseStep 2235539 = 3353309) B3353309
theorem B1490083 : Blo 1490065 1490083 := bstep (se 1 (by rfl) ⟨1117562, by rfl⟩ : syracuseStep 1490083 = 2235125) B2235125
theorem B2235569 : Blo 1490065 2235569 := bstep (se 2 (by rfl) ⟨838338, by rfl⟩ : syracuseStep 2235569 = 1676677) B1676677
theorem B9067697 : Blo 1490065 9067697 := bstep (se 2 (by rfl) ⟨3400386, by rfl⟩ : syracuseStep 9067697 = 6800773) B6800773
theorem B1490099 : Blo 1490065 1490099 := bstep (se 1 (by rfl) ⟨1117574, by rfl⟩ : syracuseStep 1490099 = 2235149) B2235149
theorem B20405429 : Blo 1490065 20405429 := bstep (se 5 (by rfl) ⟨956504, by rfl⟩ : syracuseStep 20405429 = 1913009) B1913009
theorem B1490115 : Blo 1490065 1490115 := bstep (se 1 (by rfl) ⟨1117586, by rfl⟩ : syracuseStep 1490115 = 2235173) B2235173
theorem B2235587 : Blo 1490065 2235587 := bstep (se 1 (by rfl) ⟨1676690, by rfl⟩ : syracuseStep 2235587 = 3353381) B3353381
theorem B1678531 : Blo 1490065 1678531 := bstep (se 1 (by rfl) ⟨1258898, by rfl⟩ : syracuseStep 1678531 = 2517797) B2517797
theorem B5029073 : Blo 1490065 5029073 := bstep (se 2 (by rfl) ⟨1885902, by rfl⟩ : syracuseStep 5029073 = 3771805) B3771805
theorem B1490131 : Blo 1490065 1490131 := bstep (se 1 (by rfl) ⟨1117598, by rfl⟩ : syracuseStep 1490131 = 2235197) B2235197
theorem B2235617 : Blo 1490065 2235617 := bstep (se 2 (by rfl) ⟨838356, by rfl⟩ : syracuseStep 2235617 = 1676713) B1676713
theorem B1490147 : Blo 1490065 1490147 := bstep (se 1 (by rfl) ⟨1117610, by rfl⟩ : syracuseStep 1490147 = 2235221) B2235221
theorem B3185905 : Blo 1490065 3185905 := bstep (se 2 (by rfl) ⟨1194714, by rfl⟩ : syracuseStep 3185905 = 2389429) B2389429
theorem B1490163 : Blo 1490065 1490163 := bstep (se 1 (by rfl) ⟨1117622, by rfl⟩ : syracuseStep 1490163 = 2235245) B2235245
theorem B2235635 : Blo 1490065 2235635 := bstep (se 1 (by rfl) ⟨1676726, by rfl⟩ : syracuseStep 2235635 = 3353453) B3353453
theorem B1490179 : Blo 1490065 1490179 := bstep (se 1 (by rfl) ⟨1117634, by rfl⟩ : syracuseStep 1490179 = 2235269) B2235269
theorem B2235665 : Blo 1490065 2235665 := bstep (se 2 (by rfl) ⟨838374, by rfl⟩ : syracuseStep 2235665 = 1676749) B1676749
theorem B1490195 : Blo 1490065 1490195 := bstep (se 1 (by rfl) ⟨1117646, by rfl⟩ : syracuseStep 1490195 = 2235293) B2235293
theorem B1490211 : Blo 1490065 1490211 := bstep (se 1 (by rfl) ⟨1117658, by rfl⟩ : syracuseStep 1490211 = 2235317) B2235317
theorem B2235683 : Blo 1490065 2235683 := bstep (se 1 (by rfl) ⟨1676762, by rfl⟩ : syracuseStep 2235683 = 3353525) B3353525
theorem B1490227 : Blo 1490065 1490227 := bstep (se 1 (by rfl) ⟨1117670, by rfl⟩ : syracuseStep 1490227 = 2235341) B2235341
theorem B2235713 : Blo 1490065 2235713 := bstep (se 2 (by rfl) ⟨838392, by rfl⟩ : syracuseStep 2235713 = 1676785) B1676785
theorem B1490243 : Blo 1490065 1490243 := bstep (se 1 (by rfl) ⟨1117682, by rfl⟩ : syracuseStep 1490243 = 2235365) B2235365
theorem B1490259 : Blo 1490065 1490259 := bstep (se 1 (by rfl) ⟨1117694, by rfl⟩ : syracuseStep 1490259 = 2235389) B2235389
theorem B2235731 : Blo 1490065 2235731 := bstep (se 1 (by rfl) ⟨1676798, by rfl⟩ : syracuseStep 2235731 = 3353597) B3353597
theorem B1490275 : Blo 1490065 1490275 := bstep (se 1 (by rfl) ⟨1117706, by rfl⟩ : syracuseStep 1490275 = 2235413) B2235413
theorem B7544177 : Blo 1490065 7544177 := bstep (se 2 (by rfl) ⟨2829066, by rfl⟩ : syracuseStep 7544177 = 5658133) B5658133
theorem B2235761 : Blo 1490065 2235761 := bstep (se 2 (by rfl) ⟨838410, by rfl⟩ : syracuseStep 2235761 = 1676821) B1676821
theorem B1490291 : Blo 1490065 1490291 := bstep (se 1 (by rfl) ⟨1117718, by rfl⟩ : syracuseStep 1490291 = 2235437) B2235437
theorem B1490307 : Blo 1490065 1490307 := bstep (se 1 (by rfl) ⟨1117730, by rfl⟩ : syracuseStep 1490307 = 2235461) B2235461
theorem B2235779 : Blo 1490065 2235779 := bstep (se 1 (by rfl) ⟨1676834, by rfl⟩ : syracuseStep 2235779 = 3353669) B3353669
theorem B8494469 : Blo 1490065 8494469 := bstep (se 4 (by rfl) ⟨796356, by rfl⟩ : syracuseStep 8494469 = 1592713) B1592713
theorem B1490323 : Blo 1490065 1490323 := bstep (se 1 (by rfl) ⟨1117742, by rfl⟩ : syracuseStep 1490323 = 2235485) B2235485
theorem B2235809 : Blo 1490065 2235809 := bstep (se 2 (by rfl) ⟨838428, by rfl⟩ : syracuseStep 2235809 = 1676857) B1676857
theorem B1490339 : Blo 1490065 1490339 := bstep (se 1 (by rfl) ⟨1117754, by rfl⟩ : syracuseStep 1490339 = 2235509) B2235509
theorem B2686385 : Blo 1490065 2686385 := bstep (se 2 (by rfl) ⟨1007394, by rfl⟩ : syracuseStep 2686385 = 2014789) B2014789
theorem B1490355 : Blo 1490065 1490355 := bstep (se 1 (by rfl) ⟨1117766, by rfl⟩ : syracuseStep 1490355 = 2235533) B2235533
theorem B2235827 : Blo 1490065 2235827 := bstep (se 1 (by rfl) ⟨1676870, by rfl⟩ : syracuseStep 2235827 = 3353741) B3353741
theorem B1490371 : Blo 1490065 1490371 := bstep (se 1 (by rfl) ⟨1117778, by rfl⟩ : syracuseStep 1490371 = 2235557) B2235557
theorem B2235857 : Blo 1490065 2235857 := bstep (se 2 (by rfl) ⟨838446, by rfl⟩ : syracuseStep 2235857 = 1676893) B1676893
theorem B1490387 : Blo 1490065 1490387 := bstep (se 1 (by rfl) ⟨1117790, by rfl⟩ : syracuseStep 1490387 = 2235581) B2235581
theorem B1490403 : Blo 1490065 1490403 := bstep (se 1 (by rfl) ⟨1117802, by rfl⟩ : syracuseStep 1490403 = 2235605) B2235605
theorem B2235875 : Blo 1490065 2235875 := bstep (se 1 (by rfl) ⟨1676906, by rfl⟩ : syracuseStep 2235875 = 3353813) B3353813
theorem B1490419 : Blo 1490065 1490419 := bstep (se 1 (by rfl) ⟨1117814, by rfl⟩ : syracuseStep 1490419 = 2235629) B2235629
theorem B2235905 : Blo 1490065 2235905 := bstep (se 2 (by rfl) ⟨838464, by rfl⟩ : syracuseStep 2235905 = 1676929) B1676929
theorem B1490435 : Blo 1490065 1490435 := bstep (se 1 (by rfl) ⟨1117826, by rfl⟩ : syracuseStep 1490435 = 2235653) B2235653
theorem B3776017 : Blo 1490065 3776017 := bstep (se 2 (by rfl) ⟨1416006, by rfl⟩ : syracuseStep 3776017 = 2832013) B2832013
theorem B1490451 : Blo 1490065 1490451 := bstep (se 1 (by rfl) ⟨1117838, by rfl⟩ : syracuseStep 1490451 = 2235677) B2235677
theorem B2235923 : Blo 1490065 2235923 := bstep (se 1 (by rfl) ⟨1676942, by rfl⟩ : syracuseStep 2235923 = 3353885) B3353885
theorem B1490467 : Blo 1490065 1490467 := bstep (se 1 (by rfl) ⟨1117850, by rfl⟩ : syracuseStep 1490467 = 2235701) B2235701
theorem B9313841 : Blo 1490065 9313841 := bstep (se 2 (by rfl) ⟨3492690, by rfl⟩ : syracuseStep 9313841 = 6985381) B6985381
theorem B2235953 : Blo 1490065 2235953 := bstep (se 2 (by rfl) ⟨838482, by rfl⟩ : syracuseStep 2235953 = 1676965) B1676965
theorem B1490483 : Blo 1490065 1490483 := bstep (se 1 (by rfl) ⟨1117862, by rfl⟩ : syracuseStep 1490483 = 2235725) B2235725
theorem B1490499 : Blo 1490065 1490499 := bstep (se 1 (by rfl) ⟨1117874, by rfl⟩ : syracuseStep 1490499 = 2235749) B2235749
theorem B2235971 : Blo 1490065 2235971 := bstep (se 1 (by rfl) ⟨1676978, by rfl⟩ : syracuseStep 2235971 = 3353957) B3353957
theorem B1490515 : Blo 1490065 1490515 := bstep (se 1 (by rfl) ⟨1117886, by rfl⟩ : syracuseStep 1490515 = 2235773) B2235773
theorem B2236001 : Blo 1490065 2236001 := bstep (se 2 (by rfl) ⟨838500, by rfl⟩ : syracuseStep 2236001 = 1677001) B1677001
theorem B1490531 : Blo 1490065 1490531 := bstep (se 1 (by rfl) ⟨1117898, by rfl⟩ : syracuseStep 1490531 = 2235797) B2235797
theorem B4775537 : Blo 1490065 4775537 := bstep (se 2 (by rfl) ⟨1790826, by rfl⟩ : syracuseStep 4775537 = 3581653) B3581653
theorem B1490547 : Blo 1490065 1490547 := bstep (se 1 (by rfl) ⟨1117910, by rfl⟩ : syracuseStep 1490547 = 2235821) B2235821
theorem B2236019 : Blo 1490065 2236019 := bstep (se 1 (by rfl) ⟨1677014, by rfl⟩ : syracuseStep 2236019 = 3354029) B3354029
theorem B1613443 : Blo 1490065 1613443 := bstep (se 1 (by rfl) ⟨1210082, by rfl⟩ : syracuseStep 1613443 = 2420165) B2420165
theorem B1490563 : Blo 1490065 1490563 := bstep (se 1 (by rfl) ⟨1117922, by rfl⟩ : syracuseStep 1490563 = 2235845) B2235845
theorem B2514577 : Blo 1490065 2514577 := bstep (se 2 (by rfl) ⟨942966, by rfl⟩ : syracuseStep 2514577 = 1885933) B1885933
theorem B2236049 : Blo 1490065 2236049 := bstep (se 2 (by rfl) ⟨838518, by rfl⟩ : syracuseStep 2236049 = 1677037) B1677037
theorem B1490579 : Blo 1490065 1490579 := bstep (se 1 (by rfl) ⟨1117934, by rfl⟩ : syracuseStep 1490579 = 2235869) B2235869
theorem B1490595 : Blo 1490065 1490595 := bstep (se 1 (by rfl) ⟨1117946, by rfl⟩ : syracuseStep 1490595 = 2235893) B2235893
theorem B2236067 : Blo 1490065 2236067 := bstep (se 1 (by rfl) ⟨1677050, by rfl⟩ : syracuseStep 2236067 = 3354101) B3354101
theorem B2514611 : Blo 1490065 2514611 := bstep (se 1 (by rfl) ⟨1885958, by rfl⟩ : syracuseStep 2514611 = 3771917) B3771917
theorem B1490611 : Blo 1490065 1490611 := bstep (se 1 (by rfl) ⟨1117958, by rfl⟩ : syracuseStep 1490611 = 2235917) B2235917
theorem B2236097 : Blo 1490065 2236097 := bstep (se 2 (by rfl) ⟨838536, by rfl⟩ : syracuseStep 2236097 = 1677073) B1677073
theorem B1490627 : Blo 1490065 1490627 := bstep (se 1 (by rfl) ⟨1117970, by rfl⟩ : syracuseStep 1490627 = 2235941) B2235941
theorem B1490643 : Blo 1490065 1490643 := bstep (se 1 (by rfl) ⟨1117982, by rfl⟩ : syracuseStep 1490643 = 2235965) B2235965
theorem B2236115 : Blo 1490065 2236115 := bstep (se 1 (by rfl) ⟨1677086, by rfl⟩ : syracuseStep 2236115 = 3354173) B3354173
theorem B1490659 : Blo 1490065 1490659 := bstep (se 1 (by rfl) ⟨1117994, by rfl⟩ : syracuseStep 1490659 = 2235989) B2235989
theorem B5029613 : Blo 1490065 5029613 := bstep (se 3 (by rfl) ⟨943052, by rfl⟩ : syracuseStep 5029613 = 1886105) B1886105
theorem B2236145 : Blo 1490065 2236145 := bstep (se 2 (by rfl) ⟨838554, by rfl⟩ : syracuseStep 2236145 = 1677109) B1677109
theorem B2014961 : Blo 1490065 2014961 := bstep (se 2 (by rfl) ⟨755610, by rfl⟩ : syracuseStep 2014961 = 1511221) B1511221
theorem B1490675 : Blo 1490065 1490675 := bstep (se 1 (by rfl) ⟨1118006, by rfl⟩ : syracuseStep 1490675 = 2236013) B2236013
theorem B1490691 : Blo 1490065 1490691 := bstep (se 1 (by rfl) ⟨1118018, by rfl⟩ : syracuseStep 1490691 = 2236037) B2236037
theorem B2236163 : Blo 1490065 2236163 := bstep (se 1 (by rfl) ⟨1677122, by rfl⟩ : syracuseStep 2236163 = 3354245) B3354245
theorem B1490707 : Blo 1490065 1490707 := bstep (se 1 (by rfl) ⟨1118030, by rfl⟩ : syracuseStep 1490707 = 2236061) B2236061
theorem B2236193 : Blo 1490065 2236193 := bstep (se 2 (by rfl) ⟨838572, by rfl⟩ : syracuseStep 2236193 = 1677145) B1677145
theorem B5029667 : Blo 1490065 5029667 := bstep (se 1 (by rfl) ⟨3772250, by rfl⟩ : syracuseStep 5029667 = 7544501) B7544501
theorem B1490723 : Blo 1490065 1490723 := bstep (se 1 (by rfl) ⟨1118042, by rfl⟩ : syracuseStep 1490723 = 2236085) B2236085
theorem B3776291 : Blo 1490065 3776291 := bstep (se 1 (by rfl) ⟨2832218, by rfl⟩ : syracuseStep 3776291 = 5664437) B5664437
theorem B2514739 : Blo 1490065 2514739 := bstep (se 1 (by rfl) ⟨1886054, by rfl⟩ : syracuseStep 2514739 = 3772109) B3772109
theorem B1490739 : Blo 1490065 1490739 := bstep (se 1 (by rfl) ⟨1118054, by rfl⟩ : syracuseStep 1490739 = 2236109) B2236109
theorem B2236211 : Blo 1490065 2236211 := bstep (se 1 (by rfl) ⟨1677158, by rfl⟩ : syracuseStep 2236211 = 3354317) B3354317
theorem B1490755 : Blo 1490065 1490755 := bstep (se 1 (by rfl) ⟨1118066, by rfl⟩ : syracuseStep 1490755 = 2236133) B2236133
theorem B2236241 : Blo 1490065 2236241 := bstep (se 2 (by rfl) ⟨838590, by rfl⟩ : syracuseStep 2236241 = 1677181) B1677181
theorem B1490771 : Blo 1490065 1490771 := bstep (se 1 (by rfl) ⟨1118078, by rfl⟩ : syracuseStep 1490771 = 2236157) B2236157
theorem B1490787 : Blo 1490065 1490787 := bstep (se 1 (by rfl) ⟨1118090, by rfl⟩ : syracuseStep 1490787 = 2236181) B2236181
theorem B2236259 : Blo 1490065 2236259 := bstep (se 1 (by rfl) ⟨1677194, by rfl⟩ : syracuseStep 2236259 = 3354389) B3354389
theorem B1490803 : Blo 1490065 1490803 := bstep (se 1 (by rfl) ⟨1118102, by rfl⟩ : syracuseStep 1490803 = 2236205) B2236205
theorem B2236289 : Blo 1490065 2236289 := bstep (se 2 (by rfl) ⟨838608, by rfl⟩ : syracuseStep 2236289 = 1677217) B1677217
theorem B1490819 : Blo 1490065 1490819 := bstep (se 1 (by rfl) ⟨1118114, by rfl⟩ : syracuseStep 1490819 = 2236229) B2236229
theorem B1490835 : Blo 1490065 1490835 := bstep (se 1 (by rfl) ⟨1118126, by rfl⟩ : syracuseStep 1490835 = 2236253) B2236253
theorem B2236307 : Blo 1490065 2236307 := bstep (se 1 (by rfl) ⟨1677230, by rfl⟩ : syracuseStep 2236307 = 3354461) B3354461
theorem B1490851 : Blo 1490065 1490851 := bstep (se 1 (by rfl) ⟨1118138, by rfl⟩ : syracuseStep 1490851 = 2236277) B2236277
theorem B4243373 : Blo 1490065 4243373 := bstep (se 3 (by rfl) ⟨795632, by rfl⟩ : syracuseStep 4243373 = 1591265) B1591265
theorem B2236337 : Blo 1490065 2236337 := bstep (se 2 (by rfl) ⟨838626, by rfl⟩ : syracuseStep 2236337 = 1677253) B1677253
theorem B1490867 : Blo 1490065 1490867 := bstep (se 1 (by rfl) ⟨1118150, by rfl⟩ : syracuseStep 1490867 = 2236301) B2236301
theorem B2514881 : Blo 1490065 2514881 := bstep (se 2 (by rfl) ⟨943080, by rfl⟩ : syracuseStep 2514881 = 1886161) B1886161
theorem B1490883 : Blo 1490065 1490883 := bstep (se 1 (by rfl) ⟨1118162, by rfl⟩ : syracuseStep 1490883 = 2236325) B2236325
theorem B2236355 : Blo 1490065 2236355 := bstep (se 1 (by rfl) ⟨1677266, by rfl⟩ : syracuseStep 2236355 = 3354533) B3354533
theorem B48381893 : Blo 1490065 48381893 := bstep (se 4 (by rfl) ⟨4535802, by rfl⟩ : syracuseStep 48381893 = 9071605) B9071605
theorem B4775885 : Blo 1490065 4775885 := bstep (se 3 (by rfl) ⟨895478, by rfl⟩ : syracuseStep 4775885 = 1790957) B1790957
theorem B1490899 : Blo 1490065 1490899 := bstep (se 1 (by rfl) ⟨1118174, by rfl⟩ : syracuseStep 1490899 = 2236349) B2236349
theorem B2236385 : Blo 1490065 2236385 := bstep (se 2 (by rfl) ⟨838644, by rfl⟩ : syracuseStep 2236385 = 1677289) B1677289
theorem B1490915 : Blo 1490065 1490915 := bstep (se 1 (by rfl) ⟨1118186, by rfl⟩ : syracuseStep 1490915 = 2236373) B2236373
theorem B3776483 : Blo 1490065 3776483 := bstep (se 1 (by rfl) ⟨2832362, by rfl⟩ : syracuseStep 3776483 = 5664725) B5664725
theorem B4243441 : Blo 1490065 4243441 := bstep (se 2 (by rfl) ⟨1591290, by rfl⟩ : syracuseStep 4243441 = 3182581) B3182581
theorem B2686961 : Blo 1490065 2686961 := bstep (se 2 (by rfl) ⟨1007610, by rfl⟩ : syracuseStep 2686961 = 2015221) B2015221
theorem B1490931 : Blo 1490065 1490931 := bstep (se 1 (by rfl) ⟨1118198, by rfl⟩ : syracuseStep 1490931 = 2236397) B2236397
theorem B2236403 : Blo 1490065 2236403 := bstep (se 1 (by rfl) ⟨1677302, by rfl⟩ : syracuseStep 2236403 = 3354605) B3354605
theorem B2514955 : Blo 1490065 2514955 := bstep (se 1 (by rfl) ⟨1886216, by rfl⟩ : syracuseStep 2514955 = 3772433) B3772433
theorem B2236427 : Blo 1490065 2236427 := bstep (se 1 (by rfl) ⟨1677320, by rfl⟩ : syracuseStep 2236427 = 3354641) B3354641
theorem B1490955 : Blo 1490065 1490955 := bstep (se 1 (by rfl) ⟨1118216, by rfl⟩ : syracuseStep 1490955 = 2236433) B2236433
theorem B2236439 : Blo 1490065 2236439 := bstep (se 1 (by rfl) ⟨1677329, by rfl⟩ : syracuseStep 2236439 = 3354659) B3354659
theorem B1490967 : Blo 1490065 1490967 := bstep (se 1 (by rfl) ⟨1118225, by rfl⟩ : syracuseStep 1490967 = 2236451) B2236451
theorem B19095587 : Blo 1490065 19095587 := bstep (se 1 (by rfl) ⟨14321690, by rfl⟩ : syracuseStep 19095587 = 28643381) B28643381
theorem B7258157 : Blo 1490065 7258157 := bstep (se 3 (by rfl) ⟨1360904, by rfl⟩ : syracuseStep 7258157 = 2721809) B2721809
theorem B1490987 : Blo 1490065 1490987 := bstep (se 1 (by rfl) ⟨1118240, by rfl⟩ : syracuseStep 1490987 = 2236481) B2236481
theorem B1490999 : Blo 1490065 1490999 := bstep (se 1 (by rfl) ⟨1118249, by rfl⟩ : syracuseStep 1490999 = 2236499) B2236499
theorem B6365249 : Blo 1490065 6365249 := bstep (se 2 (by rfl) ⟨2386968, by rfl⟩ : syracuseStep 6365249 = 4773937) B4773937
theorem B2908225 : Blo 1490065 2908225 := bstep (se 2 (by rfl) ⟨1090584, by rfl⟩ : syracuseStep 2908225 = 2181169) B2181169
theorem B1491019 : Blo 1490065 1491019 := bstep (se 1 (by rfl) ⟨1118264, by rfl⟩ : syracuseStep 1491019 = 2236529) B2236529
theorem B1491031 : Blo 1490065 1491031 := bstep (se 1 (by rfl) ⟨1118273, by rfl⟩ : syracuseStep 1491031 = 2236547) B2236547
theorem B2236505 : Blo 1490065 2236505 := bstep (se 2 (by rfl) ⟨838689, by rfl⟩ : syracuseStep 2236505 = 1677379) B1677379
theorem B1491051 : Blo 1490065 1491051 := bstep (se 1 (by rfl) ⟨1118288, by rfl⟩ : syracuseStep 1491051 = 2236577) B2236577
theorem B1491063 : Blo 1490065 1491063 := bstep (se 1 (by rfl) ⟨1118297, by rfl⟩ : syracuseStep 1491063 = 2236595) B2236595
theorem B1491083 : Blo 1490065 1491083 := bstep (se 1 (by rfl) ⟨1118312, by rfl⟩ : syracuseStep 1491083 = 2236625) B2236625
theorem B1491095 : Blo 1490065 1491095 := bstep (se 1 (by rfl) ⟨1118321, by rfl⟩ : syracuseStep 1491095 = 2236643) B2236643
theorem B2515097 : Blo 1490065 2515097 := bstep (se 2 (by rfl) ⟨943161, by rfl⟩ : syracuseStep 2515097 = 1886323) B1886323
theorem B1491115 : Blo 1490065 1491115 := bstep (se 1 (by rfl) ⟨1118336, by rfl⟩ : syracuseStep 1491115 = 2236673) B2236673
theorem B1491127 : Blo 1490065 1491127 := bstep (se 1 (by rfl) ⟨1118345, by rfl⟩ : syracuseStep 1491127 = 2236691) B2236691
theorem B2236619 : Blo 1490065 2236619 := bstep (se 1 (by rfl) ⟨1677464, by rfl⟩ : syracuseStep 2236619 = 3354929) B3354929
theorem B1491147 : Blo 1490065 1491147 := bstep (se 1 (by rfl) ⟨1118360, by rfl⟩ : syracuseStep 1491147 = 2236721) B2236721
theorem B2236631 : Blo 1490065 2236631 := bstep (se 1 (by rfl) ⟨1677473, by rfl⟩ : syracuseStep 2236631 = 3354947) B3354947
theorem B1491159 : Blo 1490065 1491159 := bstep (se 1 (by rfl) ⟨1118369, by rfl⟩ : syracuseStep 1491159 = 2236739) B2236739
theorem B1491179 : Blo 1490065 1491179 := bstep (se 1 (by rfl) ⟨1118384, by rfl⟩ : syracuseStep 1491179 = 2236769) B2236769
theorem B1491191 : Blo 1490065 1491191 := bstep (se 1 (by rfl) ⟨1118393, by rfl⟩ : syracuseStep 1491191 = 2236787) B2236787
theorem B1491211 : Blo 1490065 1491211 := bstep (se 1 (by rfl) ⟨1118408, by rfl⟩ : syracuseStep 1491211 = 2236817) B2236817
theorem B1491223 : Blo 1490065 1491223 := bstep (se 1 (by rfl) ⟨1118417, by rfl⟩ : syracuseStep 1491223 = 2236835) B2236835
theorem B2515225 : Blo 1490065 2515225 := bstep (se 2 (by rfl) ⟨943209, by rfl⟩ : syracuseStep 2515225 = 1886419) B1886419
theorem B2236697 : Blo 1490065 2236697 := bstep (se 2 (by rfl) ⟨838761, by rfl⟩ : syracuseStep 2236697 = 1677523) B1677523
theorem B18129197 : Blo 1490065 18129197 := bstep (se 3 (by rfl) ⟨3399224, by rfl⟩ : syracuseStep 18129197 = 6798449) B6798449
theorem B1491243 : Blo 1490065 1491243 := bstep (se 1 (by rfl) ⟨1118432, by rfl⟩ : syracuseStep 1491243 = 2236865) B2236865
theorem B1491255 : Blo 1490065 1491255 := bstep (se 1 (by rfl) ⟨1118441, by rfl⟩ : syracuseStep 1491255 = 2236883) B2236883
theorem B3449153 : Blo 1490065 3449153 := bstep (se 2 (by rfl) ⟨1293432, by rfl⟩ : syracuseStep 3449153 = 2586865) B2586865
theorem B1491275 : Blo 1490065 1491275 := bstep (se 1 (by rfl) ⟨1118456, by rfl⟩ : syracuseStep 1491275 = 2236913) B2236913
theorem B1491287 : Blo 1490065 1491287 := bstep (se 1 (by rfl) ⟨1118465, by rfl⟩ : syracuseStep 1491287 = 2236931) B2236931
theorem B1491307 : Blo 1490065 1491307 := bstep (se 1 (by rfl) ⟨1118480, by rfl⟩ : syracuseStep 1491307 = 2236961) B2236961
theorem B1491319 : Blo 1490065 1491319 := bstep (se 1 (by rfl) ⟨1118489, by rfl⟩ : syracuseStep 1491319 = 2236979) B2236979
theorem B7553411 : Blo 1490065 7553411 := bstep (se 1 (by rfl) ⟨5665058, by rfl⟩ : syracuseStep 7553411 = 11330117) B11330117
theorem B2236811 : Blo 1490065 2236811 := bstep (se 1 (by rfl) ⟨1677608, by rfl⟩ : syracuseStep 2236811 = 3355217) B3355217
theorem B1491339 : Blo 1490065 1491339 := bstep (se 1 (by rfl) ⟨1118504, by rfl⟩ : syracuseStep 1491339 = 2237009) B2237009
theorem B2236823 : Blo 1490065 2236823 := bstep (se 1 (by rfl) ⟨1677617, by rfl⟩ : syracuseStep 2236823 = 3355235) B3355235
theorem B1491351 : Blo 1490065 1491351 := bstep (se 1 (by rfl) ⟨1118513, by rfl⟩ : syracuseStep 1491351 = 2237027) B2237027
theorem B1491371 : Blo 1490065 1491371 := bstep (se 1 (by rfl) ⟨1118528, by rfl⟩ : syracuseStep 1491371 = 2237057) B2237057
theorem B1491383 : Blo 1490065 1491383 := bstep (se 1 (by rfl) ⟨1118537, by rfl⟩ : syracuseStep 1491383 = 2237075) B2237075
theorem B1491403 : Blo 1490065 1491403 := bstep (se 1 (by rfl) ⟨1118552, by rfl⟩ : syracuseStep 1491403 = 2237105) B2237105
theorem B1491415 : Blo 1490065 1491415 := bstep (se 1 (by rfl) ⟨1118561, by rfl⟩ : syracuseStep 1491415 = 2237123) B2237123
theorem B2236889 : Blo 1490065 2236889 := bstep (se 2 (by rfl) ⟨838833, by rfl⟩ : syracuseStep 2236889 = 1677667) B1677667
theorem B1491435 : Blo 1490065 1491435 := bstep (se 1 (by rfl) ⟨1118576, by rfl⟩ : syracuseStep 1491435 = 2237153) B2237153
theorem B2867699 : Blo 1490065 2867699 := bstep (se 1 (by rfl) ⟨2150774, by rfl⟩ : syracuseStep 2867699 = 4301549) B4301549
theorem B1491447 : Blo 1490065 1491447 := bstep (se 1 (by rfl) ⟨1118585, by rfl⟩ : syracuseStep 1491447 = 2237171) B2237171
theorem B1491467 : Blo 1490065 1491467 := bstep (se 1 (by rfl) ⟨1118600, by rfl⟩ : syracuseStep 1491467 = 2237201) B2237201
theorem B5030423 : Blo 1490065 5030423 := bstep (se 1 (by rfl) ⟨3772817, by rfl⟩ : syracuseStep 5030423 = 7545635) B7545635
theorem B1491479 : Blo 1490065 1491479 := bstep (se 1 (by rfl) ⟨1118609, by rfl⟩ : syracuseStep 1491479 = 2237219) B2237219
theorem B1491499 : Blo 1490065 1491499 := bstep (se 1 (by rfl) ⟨1118624, by rfl⟩ : syracuseStep 1491499 = 2237249) B2237249
theorem B4776499 : Blo 1490065 4776499 := bstep (se 1 (by rfl) ⟨3582374, by rfl⟩ : syracuseStep 4776499 = 7164749) B7164749
theorem B1491511 : Blo 1490065 1491511 := bstep (se 1 (by rfl) ⟨1118633, by rfl⟩ : syracuseStep 1491511 = 2237267) B2237267
theorem B2237003 : Blo 1490065 2237003 := bstep (se 1 (by rfl) ⟨1677752, by rfl⟩ : syracuseStep 2237003 = 3355505) B3355505
theorem B1491531 : Blo 1490065 1491531 := bstep (se 1 (by rfl) ⟨1118648, by rfl⟩ : syracuseStep 1491531 = 2237297) B2237297
theorem B2237015 : Blo 1490065 2237015 := bstep (se 1 (by rfl) ⟨1677761, by rfl⟩ : syracuseStep 2237015 = 3355523) B3355523
theorem B1491543 : Blo 1490065 1491543 := bstep (se 1 (by rfl) ⟨1118657, by rfl⟩ : syracuseStep 1491543 = 2237315) B2237315
theorem B14336605 : Blo 1490065 14336605 := bstep (se 3 (by rfl) ⟨2688113, by rfl⟩ : syracuseStep 14336605 = 5376227) B5376227
theorem B1491563 : Blo 1490065 1491563 := bstep (se 1 (by rfl) ⟨1118672, by rfl⟩ : syracuseStep 1491563 = 2237345) B2237345
theorem B1491575 : Blo 1490065 1491575 := bstep (se 1 (by rfl) ⟨1118681, by rfl⟩ : syracuseStep 1491575 = 2237363) B2237363
theorem B1491595 : Blo 1490065 1491595 := bstep (se 1 (by rfl) ⟨1118696, by rfl⟩ : syracuseStep 1491595 = 2237393) B2237393
theorem B1491607 : Blo 1490065 1491607 := bstep (se 1 (by rfl) ⟨1118705, by rfl⟩ : syracuseStep 1491607 = 2237411) B2237411
theorem B2237081 : Blo 1490065 2237081 := bstep (se 2 (by rfl) ⟨838905, by rfl⟩ : syracuseStep 2237081 = 1677811) B1677811
theorem B1491627 : Blo 1490065 1491627 := bstep (se 1 (by rfl) ⟨1118720, by rfl⟩ : syracuseStep 1491627 = 2237441) B2237441
theorem B4244147 : Blo 1490065 4244147 := bstep (se 1 (by rfl) ⟨3183110, by rfl⟩ : syracuseStep 4244147 = 6366221) B6366221
theorem B1491639 : Blo 1490065 1491639 := bstep (se 1 (by rfl) ⟨1118729, by rfl⟩ : syracuseStep 1491639 = 2237459) B2237459
theorem B4776641 : Blo 1490065 4776641 := bstep (se 2 (by rfl) ⟨1791240, by rfl⟩ : syracuseStep 4776641 = 3582481) B3582481
theorem B1491659 : Blo 1490065 1491659 := bstep (se 1 (by rfl) ⟨1118744, by rfl⟩ : syracuseStep 1491659 = 2237489) B2237489
theorem B1491671 : Blo 1490065 1491671 := bstep (se 1 (by rfl) ⟨1118753, by rfl⟩ : syracuseStep 1491671 = 2237507) B2237507
theorem B1491691 : Blo 1490065 1491691 := bstep (se 1 (by rfl) ⟨1118768, by rfl⟩ : syracuseStep 1491691 = 2237537) B2237537
theorem B1491703 : Blo 1490065 1491703 := bstep (se 1 (by rfl) ⟨1118777, by rfl⟩ : syracuseStep 1491703 = 2237555) B2237555
theorem B2237195 : Blo 1490065 2237195 := bstep (se 1 (by rfl) ⟨1677896, by rfl⟩ : syracuseStep 2237195 = 3355793) B3355793
theorem B1491723 : Blo 1490065 1491723 := bstep (se 1 (by rfl) ⟨1118792, by rfl⟩ : syracuseStep 1491723 = 2237585) B2237585
theorem B2237207 : Blo 1490065 2237207 := bstep (se 1 (by rfl) ⟨1677905, by rfl⟩ : syracuseStep 2237207 = 3355811) B3355811
theorem B1491735 : Blo 1490065 1491735 := bstep (se 1 (by rfl) ⟨1118801, by rfl⟩ : syracuseStep 1491735 = 2237603) B2237603
theorem B1491755 : Blo 1490065 1491755 := bstep (se 1 (by rfl) ⟨1118816, by rfl⟩ : syracuseStep 1491755 = 2237633) B2237633
theorem B6456115 : Blo 1490065 6456115 := bstep (se 1 (by rfl) ⟨4842086, by rfl⟩ : syracuseStep 6456115 = 9684173) B9684173
theorem B1491767 : Blo 1490065 1491767 := bstep (se 1 (by rfl) ⟨1118825, by rfl⟩ : syracuseStep 1491767 = 2237651) B2237651
theorem B6800203 : Blo 1490065 6800203 := bstep (se 1 (by rfl) ⟨5100152, by rfl⟩ : syracuseStep 6800203 = 10200305) B10200305
theorem B1491787 : Blo 1490065 1491787 := bstep (se 1 (by rfl) ⟨1118840, by rfl⟩ : syracuseStep 1491787 = 2237681) B2237681
theorem B2515799 : Blo 1490065 2515799 := bstep (se 1 (by rfl) ⟨1886849, by rfl⟩ : syracuseStep 2515799 = 3773699) B3773699
theorem B1491799 : Blo 1490065 1491799 := bstep (se 1 (by rfl) ⟨1118849, by rfl⟩ : syracuseStep 1491799 = 2237699) B2237699
theorem B2237273 : Blo 1490065 2237273 := bstep (se 2 (by rfl) ⟨838977, by rfl⟩ : syracuseStep 2237273 = 1677955) B1677955
theorem B1491819 : Blo 1490065 1491819 := bstep (se 1 (by rfl) ⟨1118864, by rfl⟩ : syracuseStep 1491819 = 2237729) B2237729
theorem B1491831 : Blo 1490065 1491831 := bstep (se 1 (by rfl) ⟨1118873, by rfl⟩ : syracuseStep 1491831 = 2237747) B2237747
theorem B1491851 : Blo 1490065 1491851 := bstep (se 1 (by rfl) ⟨1118888, by rfl⟩ : syracuseStep 1491851 = 2237777) B2237777
theorem B4244375 : Blo 1490065 4244375 := bstep (se 1 (by rfl) ⟨3183281, by rfl⟩ : syracuseStep 4244375 = 6366563) B6366563
theorem B1491863 : Blo 1490065 1491863 := bstep (se 1 (by rfl) ⟨1118897, by rfl⟩ : syracuseStep 1491863 = 2237795) B2237795
theorem B1491883 : Blo 1490065 1491883 := bstep (se 1 (by rfl) ⟨1118912, by rfl⟩ : syracuseStep 1491883 = 2237825) B2237825
theorem B1491895 : Blo 1490065 1491895 := bstep (se 1 (by rfl) ⟨1118921, by rfl⟩ : syracuseStep 1491895 = 2237843) B2237843
theorem B2237387 : Blo 1490065 2237387 := bstep (se 1 (by rfl) ⟨1678040, by rfl⟩ : syracuseStep 2237387 = 3356081) B3356081
theorem B1491915 : Blo 1490065 1491915 := bstep (se 1 (by rfl) ⟨1118936, by rfl⟩ : syracuseStep 1491915 = 2237873) B2237873
theorem B2515927 : Blo 1490065 2515927 := bstep (se 1 (by rfl) ⟨1886945, by rfl⟩ : syracuseStep 2515927 = 3773891) B3773891
theorem B2237399 : Blo 1490065 2237399 := bstep (se 1 (by rfl) ⟨1678049, by rfl⟩ : syracuseStep 2237399 = 3356099) B3356099
theorem B1491927 : Blo 1490065 1491927 := bstep (se 1 (by rfl) ⟨1118945, by rfl⟩ : syracuseStep 1491927 = 2237891) B2237891
theorem B1491947 : Blo 1490065 1491947 := bstep (se 1 (by rfl) ⟨1118960, by rfl⟩ : syracuseStep 1491947 = 2237921) B2237921
theorem B1491959 : Blo 1490065 1491959 := bstep (se 1 (by rfl) ⟨1118969, by rfl⟩ : syracuseStep 1491959 = 2237939) B2237939
theorem B1491979 : Blo 1490065 1491979 := bstep (se 1 (by rfl) ⟨1118984, by rfl⟩ : syracuseStep 1491979 = 2237969) B2237969
theorem B1491991 : Blo 1490065 1491991 := bstep (se 1 (by rfl) ⟨1118993, by rfl⟩ : syracuseStep 1491991 = 2237987) B2237987
theorem B2237465 : Blo 1490065 2237465 := bstep (se 2 (by rfl) ⟨839049, by rfl⟩ : syracuseStep 2237465 = 1678099) B1678099
theorem B1492011 : Blo 1490065 1492011 := bstep (se 1 (by rfl) ⟨1119008, by rfl⟩ : syracuseStep 1492011 = 2238017) B2238017
theorem B5030963 : Blo 1490065 5030963 := bstep (se 1 (by rfl) ⟨3773222, by rfl⟩ : syracuseStep 5030963 = 7546445) B7546445
theorem B1492023 : Blo 1490065 1492023 := bstep (se 1 (by rfl) ⟨1119017, by rfl⟩ : syracuseStep 1492023 = 2238035) B2238035
theorem B1492043 : Blo 1490065 1492043 := bstep (se 1 (by rfl) ⟨1119032, by rfl⟩ : syracuseStep 1492043 = 2238065) B2238065
theorem B1492055 : Blo 1490065 1492055 := bstep (se 1 (by rfl) ⟨1119041, by rfl⟩ : syracuseStep 1492055 = 2238083) B2238083
theorem B2237579 : Blo 1490065 2237579 := bstep (se 1 (by rfl) ⟨1678184, by rfl⟩ : syracuseStep 2237579 = 3356369) B3356369
theorem B2237591 : Blo 1490065 2237591 := bstep (se 1 (by rfl) ⟨1678193, by rfl⟩ : syracuseStep 2237591 = 3356387) B3356387
theorem B12919985 : Blo 1490065 12919985 := bstep (se 2 (by rfl) ⟨4844994, by rfl⟩ : syracuseStep 12919985 = 9689989) B9689989
theorem B4244683 : Blo 1490065 4244683 := bstep (se 1 (by rfl) ⟨3183512, by rfl⟩ : syracuseStep 4244683 = 6367025) B6367025
theorem B2237657 : Blo 1490065 2237657 := bstep (se 2 (by rfl) ⟨839121, by rfl⟩ : syracuseStep 2237657 = 1678243) B1678243
theorem B5031233 : Blo 1490065 5031233 := bstep (se 2 (by rfl) ⟨1886712, by rfl⟩ : syracuseStep 5031233 = 3773425) B3773425
theorem B2237771 : Blo 1490065 2237771 := bstep (se 1 (by rfl) ⟨1678328, by rfl⟩ : syracuseStep 2237771 = 3356657) B3356657
theorem B2237783 : Blo 1490065 2237783 := bstep (se 1 (by rfl) ⟨1678337, by rfl⟩ : syracuseStep 2237783 = 3356675) B3356675
theorem B6456665 : Blo 1490065 6456665 := bstep (se 2 (by rfl) ⟨2421249, by rfl⟩ : syracuseStep 6456665 = 4842499) B4842499
theorem B2237849 : Blo 1490065 2237849 := bstep (se 2 (by rfl) ⟨839193, by rfl⟩ : syracuseStep 2237849 = 1678387) B1678387
theorem B4244957 : Blo 1490065 4244957 := bstep (se 3 (by rfl) ⟨795929, by rfl⟩ : syracuseStep 4244957 = 1591859) B1591859
theorem B2237963 : Blo 1490065 2237963 := bstep (se 1 (by rfl) ⟨1678472, by rfl⟩ : syracuseStep 2237963 = 3356945) B3356945
theorem B2237975 : Blo 1490065 2237975 := bstep (se 1 (by rfl) ⟨1678481, by rfl⟩ : syracuseStep 2237975 = 3356963) B3356963
theorem B2516555 : Blo 1490065 2516555 := bstep (se 1 (by rfl) ⟨1887416, by rfl⟩ : syracuseStep 2516555 = 3774833) B3774833
theorem B2238041 : Blo 1490065 2238041 := bstep (se 2 (by rfl) ⟨839265, by rfl⟩ : syracuseStep 2238041 = 1678531) B1678531
theorem B5375639 : Blo 1490065 5375639 := bstep (se 1 (by rfl) ⟨4031729, by rfl⟩ : syracuseStep 5375639 = 8063459) B8063459
theorem B2516683 : Blo 1490065 2516683 := bstep (se 1 (by rfl) ⟨1887512, by rfl⟩ : syracuseStep 2516683 = 3775025) B3775025
theorem B2123543 : Blo 1490065 2123543 := bstep (se 1 (by rfl) ⟨1592657, by rfl⟩ : syracuseStep 2123543 = 3185315) B3185315
theorem B2516825 : Blo 1490065 2516825 := bstep (se 2 (by rfl) ⟨943809, by rfl⟩ : syracuseStep 2516825 = 1887619) B1887619
theorem B5031773 : Blo 1490065 5031773 := bstep (se 3 (by rfl) ⟨943457, by rfl⟩ : syracuseStep 5031773 = 1886915) B1886915
theorem B11323313 : Blo 1490065 11323313 := bstep (se 2 (by rfl) ⟨4246242, by rfl⟩ : syracuseStep 11323313 = 8492485) B8492485
theorem B2516953 : Blo 1490065 2516953 := bstep (se 2 (by rfl) ⟨943857, by rfl⟩ : syracuseStep 2516953 = 1887715) B1887715
theorem B1722391 : Blo 1490065 1722391 := bstep (se 1 (by rfl) ⟨1291793, by rfl⟩ : syracuseStep 1722391 = 2583587) B2583587
theorem B4032605 : Blo 1490065 4032605 := bstep (se 3 (by rfl) ⟨756113, by rfl⟩ : syracuseStep 4032605 = 1512227) B1512227
theorem B3352715 : Blo 1490065 3352715 := bstep (se 1 (by rfl) ⟨2514536, by rfl⟩ : syracuseStep 3352715 = 5029073) B5029073
theorem B6801553 : Blo 1490065 6801553 := bstep (se 2 (by rfl) ⟨2550582, by rfl⟩ : syracuseStep 6801553 = 5101165) B5101165
theorem B3352769 : Blo 1490065 3352769 := bstep (se 2 (by rfl) ⟨1257288, by rfl⟩ : syracuseStep 3352769 = 2514577) B2514577
theorem B5662979 : Blo 1490065 5662979 := bstep (se 1 (by rfl) ⟨4247234, by rfl⟩ : syracuseStep 5662979 = 8494469) B8494469
theorem B8603921 : Blo 1490065 8603921 := bstep (se 2 (by rfl) ⟨3226470, by rfl⟩ : syracuseStep 8603921 = 6452941) B6452941
theorem B5662993 : Blo 1490065 5662993 := bstep (se 2 (by rfl) ⟨2123622, by rfl⟩ : syracuseStep 5662993 = 4247245) B4247245
theorem B14535013 : Blo 1490065 14535013 := bstep (se 4 (by rfl) ⟨1362657, by rfl⟩ : syracuseStep 14535013 = 2725315) B2725315
theorem B11323799 : Blo 1490065 11323799 := bstep (se 1 (by rfl) ⟨8492849, by rfl⟩ : syracuseStep 11323799 = 16985699) B16985699
theorem B3352985 : Blo 1490065 3352985 := bstep (se 2 (by rfl) ⟨1257369, by rfl⟩ : syracuseStep 3352985 = 2514739) B2514739
theorem B3353075 : Blo 1490065 3353075 := bstep (se 1 (by rfl) ⟨2514806, by rfl⟩ : syracuseStep 3353075 = 5029613) B5029613
theorem B3353111 : Blo 1490065 3353111 := bstep (se 1 (by rfl) ⟨2514833, by rfl⟩ : syracuseStep 3353111 = 5029667) B5029667
theorem B1886743 : Blo 1490065 1886743 := bstep (se 1 (by rfl) ⟨1415057, by rfl⟩ : syracuseStep 1886743 = 2830115) B2830115
theorem B2517527 : Blo 1490065 2517527 := bstep (se 1 (by rfl) ⟨1888145, by rfl⟩ : syracuseStep 2517527 = 3776291) B3776291
theorem B5376563 : Blo 1490065 5376563 := bstep (se 1 (by rfl) ⟨4032422, by rfl⟩ : syracuseStep 5376563 = 8064845) B8064845
theorem B5663297 : Blo 1490065 5663297 := bstep (se 2 (by rfl) ⟨2123736, by rfl⟩ : syracuseStep 5663297 = 4247473) B4247473
theorem B4778561 : Blo 1490065 4778561 := bstep (se 2 (by rfl) ⟨1791960, by rfl⟩ : syracuseStep 4778561 = 3583921) B3583921
theorem B2828915 : Blo 1490065 2828915 := bstep (se 1 (by rfl) ⟨2121686, by rfl⟩ : syracuseStep 2828915 = 4243373) B4243373
theorem B32254595 : Blo 1490065 32254595 := bstep (se 1 (by rfl) ⟨24190946, by rfl⟩ : syracuseStep 32254595 = 48381893) B48381893
theorem B2517655 : Blo 1490065 2517655 := bstep (se 1 (by rfl) ⟨1888241, by rfl⟩ : syracuseStep 2517655 = 3776483) B3776483
theorem B4655819 : Blo 1490065 4655819 := bstep (se 1 (by rfl) ⟨3491864, by rfl⟩ : syracuseStep 4655819 = 6983729) B6983729
theorem B3353291 : Blo 1490065 3353291 := bstep (se 1 (by rfl) ⟨2514968, by rfl⟩ : syracuseStep 3353291 = 5029937) B5029937
theorem B5737177 : Blo 1490065 5737177 := bstep (se 2 (by rfl) ⟨2151441, by rfl⟩ : syracuseStep 5737177 = 4302883) B4302883
theorem B29051633 : Blo 1490065 29051633 := bstep (se 2 (by rfl) ⟨10894362, by rfl⟩ : syracuseStep 29051633 = 21788725) B21788725
theorem B3353345 : Blo 1490065 3353345 := bstep (se 2 (by rfl) ⟨1257504, by rfl⟩ : syracuseStep 3353345 = 2515009) B2515009
theorem B1592119 : Blo 1490065 1592119 := bstep (se 1 (by rfl) ⟨1194089, by rfl⟩ : syracuseStep 1592119 = 2388179) B2388179
theorem B2829143 : Blo 1490065 2829143 := bstep (se 1 (by rfl) ⟨2121857, by rfl⟩ : syracuseStep 2829143 = 4243715) B4243715
theorem B7547741 : Blo 1490065 7547741 := bstep (se 3 (by rfl) ⟨1415201, by rfl⟩ : syracuseStep 7547741 = 2830403) B2830403
theorem B9554867 : Blo 1490065 9554867 := bstep (se 1 (by rfl) ⟨7166150, by rfl⟩ : syracuseStep 9554867 = 14332301) B14332301
theorem B5032907 : Blo 1490065 5032907 := bstep (se 1 (by rfl) ⟨3774680, by rfl⟩ : syracuseStep 5032907 = 7549361) B7549361
theorem B3353561 : Blo 1490065 3353561 := bstep (se 2 (by rfl) ⟨1257585, by rfl⟩ : syracuseStep 3353561 = 2515171) B2515171
theorem B20671523 : Blo 1490065 20671523 := bstep (se 1 (by rfl) ⟨15503642, by rfl⟩ : syracuseStep 20671523 = 31007285) B31007285
theorem B3353651 : Blo 1490065 3353651 := bstep (se 1 (by rfl) ⟨2515238, by rfl⟩ : syracuseStep 3353651 = 5030477) B5030477
theorem B3353687 : Blo 1490065 3353687 := bstep (se 1 (by rfl) ⟨2515265, by rfl⟩ : syracuseStep 3353687 = 5030531) B5030531
theorem B2829401 : Blo 1490065 2829401 := bstep (se 2 (by rfl) ⟨1061025, by rfl⟩ : syracuseStep 2829401 = 2122051) B2122051
theorem B4779101 : Blo 1490065 4779101 := bstep (se 3 (by rfl) ⟨896081, by rfl⟩ : syracuseStep 4779101 = 1792163) B1792163
theorem B1510507 : Blo 1490065 1510507 := bstep (se 1 (by rfl) ⟨1132880, by rfl⟩ : syracuseStep 1510507 = 2265761) B2265761
theorem B5033177 : Blo 1490065 5033177 := bstep (se 2 (by rfl) ⟨1887441, by rfl⟩ : syracuseStep 5033177 = 3774883) B3774883
theorem B5663965 : Blo 1490065 5663965 := bstep (se 3 (by rfl) ⟨1061993, by rfl⟩ : syracuseStep 5663965 = 2123987) B2123987
theorem B2870515 : Blo 1490065 2870515 := bstep (se 1 (by rfl) ⟨2152886, by rfl⟩ : syracuseStep 2870515 = 4305773) B4305773
theorem B3353867 : Blo 1490065 3353867 := bstep (se 1 (by rfl) ⟨2515400, by rfl⟩ : syracuseStep 3353867 = 5030801) B5030801
theorem B2387225 : Blo 1490065 2387225 := bstep (se 2 (by rfl) ⟨895209, by rfl⟩ : syracuseStep 2387225 = 1790419) B1790419
theorem B3353921 : Blo 1490065 3353921 := bstep (se 2 (by rfl) ⟨1257720, by rfl⟩ : syracuseStep 3353921 = 2515441) B2515441
theorem B1887563 : Blo 1490065 1887563 := bstep (se 1 (by rfl) ⟨1415672, by rfl⟩ : syracuseStep 1887563 = 2831345) B2831345
theorem B2870615 : Blo 1490065 2870615 := bstep (se 1 (by rfl) ⟨2152961, by rfl⟩ : syracuseStep 2870615 = 4305923) B4305923
theorem B2829811 : Blo 1490065 2829811 := bstep (se 1 (by rfl) ⟨2122358, by rfl⟩ : syracuseStep 2829811 = 4244717) B4244717
theorem B2797067 : Blo 1490065 2797067 := bstep (se 1 (by rfl) ⟨2097800, by rfl⟩ : syracuseStep 2797067 = 4195601) B4195601
theorem B4247063 : Blo 1490065 4247063 := bstep (se 1 (by rfl) ⟨3185297, by rfl⟩ : syracuseStep 4247063 = 6370595) B6370595
theorem B3354137 : Blo 1490065 3354137 := bstep (se 2 (by rfl) ⟨1257801, by rfl⟩ : syracuseStep 3354137 = 2515603) B2515603
theorem B8056385 : Blo 1490065 8056385 := bstep (se 2 (by rfl) ⟨3021144, by rfl⟩ : syracuseStep 8056385 = 6042289) B6042289
theorem B3878489 : Blo 1490065 3878489 := bstep (se 2 (by rfl) ⟨1454433, by rfl⟩ : syracuseStep 3878489 = 2908867) B2908867
theorem B21507677 : Blo 1490065 21507677 := bstep (se 3 (by rfl) ⟨4032689, by rfl⟩ : syracuseStep 21507677 = 8065379) B8065379
theorem B3354227 : Blo 1490065 3354227 := bstep (se 1 (by rfl) ⟨2515670, by rfl⟩ : syracuseStep 3354227 = 5031341) B5031341
theorem B3354263 : Blo 1490065 3354263 := bstep (se 1 (by rfl) ⟨2515697, by rfl⟩ : syracuseStep 3354263 = 5031395) B5031395
theorem B6368989 : Blo 1490065 6368989 := bstep (se 3 (by rfl) ⟨1194185, by rfl⟩ : syracuseStep 6368989 = 2388371) B2388371
theorem B14331653 : Blo 1490065 14331653 := bstep (se 4 (by rfl) ⟨1343592, by rfl⟩ : syracuseStep 14331653 = 2687185) B2687185
theorem B3354443 : Blo 1490065 3354443 := bstep (se 1 (by rfl) ⟨2515832, by rfl⟩ : syracuseStep 3354443 = 5031665) B5031665
theorem B8490845 : Blo 1490065 8490845 := bstep (se 3 (by rfl) ⟨1592033, by rfl⟩ : syracuseStep 8490845 = 3184067) B3184067
theorem B3354497 : Blo 1490065 3354497 := bstep (se 2 (by rfl) ⟨1257936, by rfl⟩ : syracuseStep 3354497 = 2515873) B2515873
theorem B5033879 : Blo 1490065 5033879 := bstep (se 1 (by rfl) ⟨3775409, by rfl⟩ : syracuseStep 5033879 = 7550819) B7550819
theorem B2830297 : Blo 1490065 2830297 := bstep (se 2 (by rfl) ⟨1061361, by rfl⟩ : syracuseStep 2830297 = 2122723) B2122723
theorem B16125913 : Blo 1490065 16125913 := bstep (se 2 (by rfl) ⟨6047217, by rfl⟩ : syracuseStep 16125913 = 12094435) B12094435
theorem B1888267 : Blo 1490065 1888267 := bstep (se 1 (by rfl) ⟨1416200, by rfl⟩ : syracuseStep 1888267 = 2832401) B2832401
theorem B3354713 : Blo 1490065 3354713 := bstep (se 2 (by rfl) ⟨1258017, by rfl⟩ : syracuseStep 3354713 = 2516035) B2516035
theorem B3772595 : Blo 1490065 3772595 := bstep (se 1 (by rfl) ⟨2829446, by rfl⟩ : syracuseStep 3772595 = 5658893) B5658893
theorem B3354803 : Blo 1490065 3354803 := bstep (se 1 (by rfl) ⟨2516102, by rfl⟩ : syracuseStep 3354803 = 5032205) B5032205
theorem B2420939 : Blo 1490065 2420939 := bstep (se 1 (by rfl) ⟨1815704, by rfl⟩ : syracuseStep 2420939 = 3631409) B3631409
theorem B3354839 : Blo 1490065 3354839 := bstep (se 1 (by rfl) ⟨2516129, by rfl⟩ : syracuseStep 3354839 = 5032259) B5032259
theorem B12095705 : Blo 1490065 12095705 := bstep (se 2 (by rfl) ⟨4535889, by rfl⟩ : syracuseStep 12095705 = 9071779) B9071779
theorem B9548077 : Blo 1490065 9548077 := bstep (se 3 (by rfl) ⟨1790264, by rfl⟩ : syracuseStep 9548077 = 3580529) B3580529
theorem B12734765 : Blo 1490065 12734765 := bstep (se 3 (by rfl) ⟨2387768, by rfl⟩ : syracuseStep 12734765 = 4775537) B4775537
theorem B4247873 : Blo 1490065 4247873 := bstep (se 2 (by rfl) ⟨1592952, by rfl⟩ : syracuseStep 4247873 = 3185905) B3185905
theorem B4305241 : Blo 1490065 4305241 := bstep (se 2 (by rfl) ⟨1614465, by rfl⟩ : syracuseStep 4305241 = 3228931) B3228931
theorem B3355019 : Blo 1490065 3355019 := bstep (se 1 (by rfl) ⟨2516264, by rfl⟩ : syracuseStep 3355019 = 5032529) B5032529
theorem B5034419 : Blo 1490065 5034419 := bstep (se 1 (by rfl) ⟨3775814, by rfl⟩ : syracuseStep 5034419 = 7551629) B7551629
theorem B3355073 : Blo 1490065 3355073 := bstep (se 2 (by rfl) ⟨1258152, by rfl⟩ : syracuseStep 3355073 = 2516305) B2516305
theorem B3584459 : Blo 1490065 3584459 := bstep (se 1 (by rfl) ⟨2688344, by rfl⟩ : syracuseStep 3584459 = 5376689) B5376689
theorem B3772889 : Blo 1490065 3772889 := bstep (se 2 (by rfl) ⟨1414833, by rfl⟩ : syracuseStep 3772889 = 2829667) B2829667
theorem B2830859 : Blo 1490065 2830859 := bstep (se 1 (by rfl) ⟨2123144, by rfl⟩ : syracuseStep 2830859 = 4246289) B4246289
theorem B18133579 : Blo 1490065 18133579 := bstep (se 1 (by rfl) ⟨13600184, by rfl⟩ : syracuseStep 18133579 = 27200369) B27200369
theorem B3355289 : Blo 1490065 3355289 := bstep (se 2 (by rfl) ⟨1258233, by rfl⟩ : syracuseStep 3355289 = 2516467) B2516467
theorem B26170037 : Blo 1490065 26170037 := bstep (se 5 (by rfl) ⟨1226720, by rfl⟩ : syracuseStep 26170037 = 2453441) B2453441
theorem B2831041 : Blo 1490065 2831041 := bstep (se 2 (by rfl) ⟨1061640, by rfl⟩ : syracuseStep 2831041 = 2123281) B2123281
theorem B5034689 : Blo 1490065 5034689 := bstep (se 2 (by rfl) ⟨1888008, by rfl⟩ : syracuseStep 5034689 = 3776017) B3776017
theorem B3584729 : Blo 1490065 3584729 := bstep (se 2 (by rfl) ⟨1344273, by rfl⟩ : syracuseStep 3584729 = 2688547) B2688547
theorem B3355379 : Blo 1490065 3355379 := bstep (se 1 (by rfl) ⟨2516534, by rfl⟩ : syracuseStep 3355379 = 5033069) B5033069
theorem B3355415 : Blo 1490065 3355415 := bstep (se 1 (by rfl) ⟨2516561, by rfl⟩ : syracuseStep 3355415 = 5033123) B5033123
theorem B13603619 : Blo 1490065 13603619 := bstep (se 1 (by rfl) ⟨10202714, by rfl⟩ : syracuseStep 13603619 = 20405429) B20405429
theorem B54424385 : Blo 1490065 54424385 := bstep (se 2 (by rfl) ⟨20409144, by rfl⟩ : syracuseStep 54424385 = 40818289) B40818289
theorem B2724673 : Blo 1490065 2724673 := bstep (se 2 (by rfl) ⟨1021752, by rfl⟩ : syracuseStep 2724673 = 2043505) B2043505
theorem B2151257 : Blo 1490065 2151257 := bstep (se 2 (by rfl) ⟨806721, by rfl⟩ : syracuseStep 2151257 = 1613443) B1613443
theorem B19108709 : Blo 1490065 19108709 := bstep (se 4 (by rfl) ⟨1791441, by rfl⟩ : syracuseStep 19108709 = 3582883) B3582883
theorem B7549847 : Blo 1490065 7549847 := bstep (se 1 (by rfl) ⟨5662385, by rfl⟩ : syracuseStep 7549847 = 11324771) B11324771
theorem B1790923 : Blo 1490065 1790923 := bstep (se 1 (by rfl) ⟨1343192, by rfl⟩ : syracuseStep 1790923 = 2686385) B2686385
theorem B3355595 : Blo 1490065 3355595 := bstep (se 1 (by rfl) ⟨2516696, by rfl⟩ : syracuseStep 3355595 = 5033393) B5033393
theorem B3355649 : Blo 1490065 3355649 := bstep (se 2 (by rfl) ⟨1258368, by rfl⟩ : syracuseStep 3355649 = 2516737) B2516737
theorem B6370321 : Blo 1490065 6370321 := bstep (se 2 (by rfl) ⟨2388870, by rfl⟩ : syracuseStep 6370321 = 4777741) B4777741
theorem B1676407 : Blo 1490065 1676407 := bstep (se 1 (by rfl) ⟨1257305, by rfl⟩ : syracuseStep 1676407 = 2514611) B2514611
theorem B8057987 : Blo 1490065 8057987 := bstep (se 1 (by rfl) ⟨6043490, by rfl⟩ : syracuseStep 8057987 = 12086981) B12086981
theorem B3355865 : Blo 1490065 3355865 := bstep (se 2 (by rfl) ⟨1258449, by rfl⟩ : syracuseStep 3355865 = 2516899) B2516899
theorem B5035229 : Blo 1490065 5035229 := bstep (se 3 (by rfl) ⟨944105, by rfl⟩ : syracuseStep 5035229 = 1888211) B1888211
theorem B1676587 : Blo 1490065 1676587 := bstep (se 1 (by rfl) ⟨1257440, by rfl⟩ : syracuseStep 1676587 = 2514881) B2514881
theorem B3183923 : Blo 1490065 3183923 := bstep (se 1 (by rfl) ⟨2387942, by rfl⟩ : syracuseStep 3183923 = 4775885) B4775885
theorem B3355955 : Blo 1490065 3355955 := bstep (se 1 (by rfl) ⟨2516966, by rfl⟩ : syracuseStep 3355955 = 5033933) B5033933
theorem B5657921 : Blo 1490065 5657921 := bstep (se 2 (by rfl) ⟨2121720, by rfl⟩ : syracuseStep 5657921 = 4243441) B4243441
theorem B1791307 : Blo 1490065 1791307 := bstep (se 1 (by rfl) ⟨1343480, by rfl⟩ : syracuseStep 1791307 = 2686961) B2686961
theorem B3355991 : Blo 1490065 3355991 := bstep (se 1 (by rfl) ⟨2516993, by rfl⟩ : syracuseStep 3355991 = 5033987) B5033987
theorem B2831755 : Blo 1490065 2831755 := bstep (se 1 (by rfl) ⟨2123816, by rfl⟩ : syracuseStep 2831755 = 4247633) B4247633
theorem B1676695 : Blo 1490065 1676695 := bstep (se 1 (by rfl) ⟨1257521, by rfl⟩ : syracuseStep 1676695 = 2515043) B2515043
theorem B2151883 : Blo 1490065 2151883 := bstep (se 1 (by rfl) ⟨1613912, by rfl⟩ : syracuseStep 2151883 = 3227825) B3227825
theorem B1490935 : Blo 1490065 1490935 := bstep (se 1 (by rfl) ⟨1118201, by rfl⟩ : syracuseStep 1490935 = 2236403) B2236403
theorem B2831831 : Blo 1490065 2831831 := bstep (se 1 (by rfl) ⟨2123873, by rfl⟩ : syracuseStep 2831831 = 4247747) B4247747
theorem B3356171 : Blo 1490065 3356171 := bstep (se 1 (by rfl) ⟨2517128, by rfl⟩ : syracuseStep 3356171 = 5034257) B5034257
theorem B3356225 : Blo 1490065 3356225 := bstep (se 2 (by rfl) ⟨1258584, by rfl⟩ : syracuseStep 3356225 = 2517169) B2517169
theorem B1676875 : Blo 1490065 1676875 := bstep (se 1 (by rfl) ⟨1257656, by rfl⟩ : syracuseStep 1676875 = 2515313) B2515313
theorem B9557635 : Blo 1490065 9557635 := bstep (se 1 (by rfl) ⟨7168226, by rfl⟩ : syracuseStep 9557635 = 14336453) B14336453
theorem B1676983 : Blo 1490065 1676983 := bstep (se 1 (by rfl) ⟨1257737, by rfl⟩ : syracuseStep 1676983 = 2515475) B2515475
theorem B3184409 : Blo 1490065 3184409 := bstep (se 2 (by rfl) ⟨1194153, by rfl⟩ : syracuseStep 3184409 = 2388307) B2388307
theorem B3356441 : Blo 1490065 3356441 := bstep (se 2 (by rfl) ⟨1258665, by rfl⟩ : syracuseStep 3356441 = 2517331) B2517331
theorem B1677163 : Blo 1490065 1677163 := bstep (se 1 (by rfl) ⟨1257872, by rfl⟩ : syracuseStep 1677163 = 2515745) B2515745
theorem B3356531 : Blo 1490065 3356531 := bstep (se 1 (by rfl) ⟨2517398, by rfl⟩ : syracuseStep 3356531 = 5034797) B5034797
theorem B3356567 : Blo 1490065 3356567 := bstep (se 1 (by rfl) ⟨2517425, by rfl⟩ : syracuseStep 3356567 = 5034851) B5034851
theorem B1677271 : Blo 1490065 1677271 := bstep (se 1 (by rfl) ⟨1257953, by rfl⟩ : syracuseStep 1677271 = 2515907) B2515907
theorem B24524813 : Blo 1490065 24524813 := bstep (se 3 (by rfl) ⟨4598402, by rfl⟩ : syracuseStep 24524813 = 9196805) B9196805
theorem B3774539 : Blo 1490065 3774539 := bstep (se 1 (by rfl) ⟨2830904, by rfl⟩ : syracuseStep 3774539 = 5661809) B5661809
theorem B3356747 : Blo 1490065 3356747 := bstep (se 1 (by rfl) ⟨2517560, by rfl⟩ : syracuseStep 3356747 = 5035121) B5035121
theorem B2832499 : Blo 1490065 2832499 := bstep (se 1 (by rfl) ⟨2124374, by rfl⟩ : syracuseStep 2832499 = 4248749) B4248749
theorem B3356801 : Blo 1490065 3356801 := bstep (se 2 (by rfl) ⟨1258800, by rfl⟩ : syracuseStep 3356801 = 2517601) B2517601
theorem B1677451 : Blo 1490065 1677451 := bstep (se 1 (by rfl) ⟨1258088, by rfl⟩ : syracuseStep 1677451 = 2516177) B2516177
theorem B1677559 : Blo 1490065 1677559 := bstep (se 1 (by rfl) ⟨1258169, by rfl⟩ : syracuseStep 1677559 = 2516339) B2516339
theorem B3357017 : Blo 1490065 3357017 := bstep (se 2 (by rfl) ⟨1258881, by rfl⟩ : syracuseStep 3357017 = 2517763) B2517763
theorem B24181091 : Blo 1490065 24181091 := bstep (se 1 (by rfl) ⟨18135818, by rfl⟩ : syracuseStep 24181091 = 36271637) B36271637
theorem B8493443 : Blo 1490065 8493443 := bstep (se 1 (by rfl) ⟨6370082, by rfl⟩ : syracuseStep 8493443 = 12740165) B12740165
theorem B1677739 : Blo 1490065 1677739 := bstep (se 1 (by rfl) ⟨1258304, by rfl⟩ : syracuseStep 1677739 = 2516609) B2516609
theorem B3357107 : Blo 1490065 3357107 := bstep (se 1 (by rfl) ⟨2517830, by rfl⟩ : syracuseStep 3357107 = 5035661) B5035661
theorem B1792471 : Blo 1490065 1792471 := bstep (se 1 (by rfl) ⟨1344353, by rfl⟩ : syracuseStep 1792471 = 2688707) B2688707
theorem B3357143 : Blo 1490065 3357143 := bstep (se 1 (by rfl) ⟨2517857, by rfl⟩ : syracuseStep 3357143 = 5035715) B5035715
theorem B3185153 : Blo 1490065 3185153 := bstep (se 2 (by rfl) ⟨1194432, by rfl⟩ : syracuseStep 3185153 = 2388865) B2388865
theorem B1677847 : Blo 1490065 1677847 := bstep (se 1 (by rfl) ⟨1258385, by rfl⟩ : syracuseStep 1677847 = 2516771) B2516771
theorem B14326307 : Blo 1490065 14326307 := bstep (se 1 (by rfl) ⟨10744730, by rfl⟩ : syracuseStep 14326307 = 21489461) B21489461
theorem B6453911 : Blo 1490065 6453911 := bstep (se 1 (by rfl) ⟨4840433, by rfl⟩ : syracuseStep 6453911 = 9680867) B9680867
theorem B1678027 : Blo 1490065 1678027 := bstep (se 1 (by rfl) ⟨1258520, by rfl⟩ : syracuseStep 1678027 = 2517041) B2517041
theorem B5659409 : Blo 1490065 5659409 := bstep (se 2 (by rfl) ⟨2122278, by rfl⟩ : syracuseStep 5659409 = 4244557) B4244557
theorem B2235161 : Blo 1490065 2235161 := bstep (se 2 (by rfl) ⟨838185, by rfl⟩ : syracuseStep 2235161 = 1676371) B1676371
theorem B7166765 : Blo 1490065 7166765 := bstep (se 3 (by rfl) ⟨1343768, by rfl⟩ : syracuseStep 7166765 = 2687537) B2687537
theorem B1678135 : Blo 1490065 1678135 := bstep (se 1 (by rfl) ⟨1258601, by rfl⟩ : syracuseStep 1678135 = 2517203) B2517203
theorem B2235275 : Blo 1490065 2235275 := bstep (se 1 (by rfl) ⟨1676456, by rfl⟩ : syracuseStep 2235275 = 3352913) B3352913
theorem B2235287 : Blo 1490065 2235287 := bstep (se 1 (by rfl) ⟨1676465, by rfl⟩ : syracuseStep 2235287 = 3352931) B3352931
theorem B4774859 : Blo 1490065 4774859 := bstep (se 1 (by rfl) ⟨3581144, by rfl⟩ : syracuseStep 4774859 = 7162289) B7162289
theorem B2235353 : Blo 1490065 2235353 := bstep (se 2 (by rfl) ⟨838257, by rfl⟩ : syracuseStep 2235353 = 1676515) B1676515
theorem B1678315 : Blo 1490065 1678315 := bstep (se 1 (by rfl) ⟨1258736, by rfl⟩ : syracuseStep 1678315 = 2517473) B2517473
theorem B3775511 : Blo 1490065 3775511 := bstep (se 1 (by rfl) ⟨2831633, by rfl⟩ : syracuseStep 3775511 = 5663267) B5663267
theorem B7543853 : Blo 1490065 7543853 := bstep (se 3 (by rfl) ⟨1414472, by rfl⟩ : syracuseStep 7543853 = 2828945) B2828945
theorem B2235467 : Blo 1490065 2235467 := bstep (se 1 (by rfl) ⟨1676600, by rfl⟩ : syracuseStep 2235467 = 3353201) B3353201
theorem B2235479 : Blo 1490065 2235479 := bstep (se 1 (by rfl) ⟨1676609, by rfl⟩ : syracuseStep 2235479 = 3353219) B3353219
theorem B1678423 : Blo 1490065 1678423 := bstep (se 1 (by rfl) ⟨1258817, by rfl⟩ : syracuseStep 1678423 = 2517635) B2517635
theorem B1490071 : Blo 1490065 1490071 := bstep (se 1 (by rfl) ⟨1117553, by rfl⟩ : syracuseStep 1490071 = 2235107) B2235107
theorem B2235545 : Blo 1490065 2235545 := bstep (se 2 (by rfl) ⟨838329, by rfl⟩ : syracuseStep 2235545 = 1676659) B1676659
theorem B1490091 : Blo 1490065 1490091 := bstep (se 1 (by rfl) ⟨1117568, by rfl⟩ : syracuseStep 1490091 = 2235137) B2235137
theorem B1490103 : Blo 1490065 1490103 := bstep (se 1 (by rfl) ⟨1117577, by rfl⟩ : syracuseStep 1490103 = 2235155) B2235155
theorem B1490123 : Blo 1490065 1490123 := bstep (se 1 (by rfl) ⟨1117592, by rfl⟩ : syracuseStep 1490123 = 2235185) B2235185
theorem B1490135 : Blo 1490065 1490135 := bstep (se 1 (by rfl) ⟨1117601, by rfl⟩ : syracuseStep 1490135 = 2235203) B2235203
theorem B5659865 : Blo 1490065 5659865 := bstep (se 2 (by rfl) ⟨2122449, by rfl⟩ : syracuseStep 5659865 = 4244899) B4244899
theorem B1490155 : Blo 1490065 1490155 := bstep (se 1 (by rfl) ⟨1117616, by rfl⟩ : syracuseStep 1490155 = 2235233) B2235233
theorem B1490167 : Blo 1490065 1490167 := bstep (se 1 (by rfl) ⟨1117625, by rfl⟩ : syracuseStep 1490167 = 2235251) B2235251
theorem B1490187 : Blo 1490065 1490187 := bstep (se 1 (by rfl) ⟨1117640, by rfl⟩ : syracuseStep 1490187 = 2235281) B2235281
theorem B2235659 : Blo 1490065 2235659 := bstep (se 1 (by rfl) ⟨1676744, by rfl⟩ : syracuseStep 2235659 = 3353489) B3353489
theorem B2235671 : Blo 1490065 2235671 := bstep (se 1 (by rfl) ⟨1676753, by rfl⟩ : syracuseStep 2235671 = 3353507) B3353507
theorem B1490199 : Blo 1490065 1490199 := bstep (se 1 (by rfl) ⟨1117649, by rfl⟩ : syracuseStep 1490199 = 2235299) B2235299
theorem B3398935 : Blo 1490065 3398935 := bstep (se 1 (by rfl) ⟨2549201, by rfl⟩ : syracuseStep 3398935 = 5098403) B5098403
theorem B1490219 : Blo 1490065 1490219 := bstep (se 1 (by rfl) ⟨1117664, by rfl⟩ : syracuseStep 1490219 = 2235329) B2235329
theorem B5373229 : Blo 1490065 5373229 := bstep (se 3 (by rfl) ⟨1007480, by rfl⟩ : syracuseStep 5373229 = 2014961) B2014961
theorem B1490231 : Blo 1490065 1490231 := bstep (se 1 (by rfl) ⟨1117673, by rfl⟩ : syracuseStep 1490231 = 2235347) B2235347
theorem B1490251 : Blo 1490065 1490251 := bstep (se 1 (by rfl) ⟨1117688, by rfl⟩ : syracuseStep 1490251 = 2235377) B2235377
theorem B1490263 : Blo 1490065 1490263 := bstep (se 1 (by rfl) ⟨1117697, by rfl⟩ : syracuseStep 1490263 = 2235395) B2235395
theorem B2235737 : Blo 1490065 2235737 := bstep (se 2 (by rfl) ⟨838401, by rfl⟩ : syracuseStep 2235737 = 1676803) B1676803
theorem B1490283 : Blo 1490065 1490283 := bstep (se 1 (by rfl) ⟨1117712, by rfl⟩ : syracuseStep 1490283 = 2235425) B2235425
theorem B1490295 : Blo 1490065 1490295 := bstep (se 1 (by rfl) ⟨1117721, by rfl⟩ : syracuseStep 1490295 = 2235443) B2235443
theorem B3186049 : Blo 1490065 3186049 := bstep (se 2 (by rfl) ⟨1194768, by rfl⟩ : syracuseStep 3186049 = 2389537) B2389537
theorem B1490315 : Blo 1490065 1490315 := bstep (se 1 (by rfl) ⟨1117736, by rfl⟩ : syracuseStep 1490315 = 2235473) B2235473
theorem B1490327 : Blo 1490065 1490327 := bstep (se 1 (by rfl) ⟨1117745, by rfl⟩ : syracuseStep 1490327 = 2235491) B2235491
theorem B2014615 : Blo 1490065 2014615 := bstep (se 1 (by rfl) ⟨1510961, by rfl⟩ : syracuseStep 2014615 = 3021923) B3021923
theorem B1490347 : Blo 1490065 1490347 := bstep (se 1 (by rfl) ⟨1117760, by rfl⟩ : syracuseStep 1490347 = 2235521) B2235521
theorem B5660077 : Blo 1490065 5660077 := bstep (se 3 (by rfl) ⟨1061264, by rfl⟩ : syracuseStep 5660077 = 2122529) B2122529
theorem B1490359 : Blo 1490065 1490359 := bstep (se 1 (by rfl) ⟨1117769, by rfl⟩ : syracuseStep 1490359 = 2235539) B2235539
theorem B1490379 : Blo 1490065 1490379 := bstep (se 1 (by rfl) ⟨1117784, by rfl⟩ : syracuseStep 1490379 = 2235569) B2235569
theorem B2235851 : Blo 1490065 2235851 := bstep (se 1 (by rfl) ⟨1676888, by rfl⟩ : syracuseStep 2235851 = 3353777) B3353777
theorem B6045131 : Blo 1490065 6045131 := bstep (se 1 (by rfl) ⟨4533848, by rfl⟩ : syracuseStep 6045131 = 9067697) B9067697
theorem B1490391 : Blo 1490065 1490391 := bstep (se 1 (by rfl) ⟨1117793, by rfl⟩ : syracuseStep 1490391 = 2235587) B2235587
theorem B2235863 : Blo 1490065 2235863 := bstep (se 1 (by rfl) ⟨1676897, by rfl⟩ : syracuseStep 2235863 = 3353795) B3353795
theorem B1490411 : Blo 1490065 1490411 := bstep (se 1 (by rfl) ⟨1117808, by rfl⟩ : syracuseStep 1490411 = 2235617) B2235617
theorem B1490423 : Blo 1490065 1490423 := bstep (se 1 (by rfl) ⟨1117817, by rfl⟩ : syracuseStep 1490423 = 2235635) B2235635
theorem B1490443 : Blo 1490065 1490443 := bstep (se 1 (by rfl) ⟨1117832, by rfl⟩ : syracuseStep 1490443 = 2235665) B2235665
theorem B3399191 : Blo 1490065 3399191 := bstep (se 1 (by rfl) ⟨2549393, by rfl⟩ : syracuseStep 3399191 = 5098787) B5098787
theorem B1490455 : Blo 1490065 1490455 := bstep (se 1 (by rfl) ⟨1117841, by rfl⟩ : syracuseStep 1490455 = 2235683) B2235683
theorem B2235929 : Blo 1490065 2235929 := bstep (se 2 (by rfl) ⟨838473, by rfl⟩ : syracuseStep 2235929 = 1676947) B1676947
theorem B1490475 : Blo 1490065 1490475 := bstep (se 1 (by rfl) ⟨1117856, by rfl⟩ : syracuseStep 1490475 = 2235713) B2235713
theorem B1490487 : Blo 1490065 1490487 := bstep (se 1 (by rfl) ⟨1117865, by rfl⟩ : syracuseStep 1490487 = 2235731) B2235731
theorem B5029451 : Blo 1490065 5029451 := bstep (se 1 (by rfl) ⟨3772088, by rfl⟩ : syracuseStep 5029451 = 7544177) B7544177
theorem B1490507 : Blo 1490065 1490507 := bstep (se 1 (by rfl) ⟨1117880, by rfl⟩ : syracuseStep 1490507 = 2235761) B2235761
theorem B1490519 : Blo 1490065 1490519 := bstep (se 1 (by rfl) ⟨1117889, by rfl⟩ : syracuseStep 1490519 = 2235779) B2235779
theorem B1490539 : Blo 1490065 1490539 := bstep (se 1 (by rfl) ⟨1117904, by rfl⟩ : syracuseStep 1490539 = 2235809) B2235809
theorem B1490551 : Blo 1490065 1490551 := bstep (se 1 (by rfl) ⟨1117913, by rfl⟩ : syracuseStep 1490551 = 2235827) B2235827
theorem B1490571 : Blo 1490065 1490571 := bstep (se 1 (by rfl) ⟨1117928, by rfl⟩ : syracuseStep 1490571 = 2235857) B2235857
theorem B2236043 : Blo 1490065 2236043 := bstep (se 1 (by rfl) ⟨1677032, by rfl⟩ : syracuseStep 2236043 = 3354065) B3354065
theorem B1490583 : Blo 1490065 1490583 := bstep (se 1 (by rfl) ⟨1117937, by rfl⟩ : syracuseStep 1490583 = 2235875) B2235875
theorem B2236055 : Blo 1490065 2236055 := bstep (se 1 (by rfl) ⟨1677041, by rfl⟩ : syracuseStep 2236055 = 3354083) B3354083
theorem B1490603 : Blo 1490065 1490603 := bstep (se 1 (by rfl) ⟨1117952, by rfl⟩ : syracuseStep 1490603 = 2235905) B2235905
theorem B1490615 : Blo 1490065 1490615 := bstep (se 1 (by rfl) ⟨1117961, by rfl⟩ : syracuseStep 1490615 = 2235923) B2235923
theorem B3776179 : Blo 1490065 3776179 := bstep (se 1 (by rfl) ⟨2832134, by rfl⟩ : syracuseStep 3776179 = 5664269) B5664269
theorem B6209227 : Blo 1490065 6209227 := bstep (se 1 (by rfl) ⟨4656920, by rfl⟩ : syracuseStep 6209227 = 9313841) B9313841
theorem B1490635 : Blo 1490065 1490635 := bstep (se 1 (by rfl) ⟨1117976, by rfl⟩ : syracuseStep 1490635 = 2235953) B2235953
theorem B1490647 : Blo 1490065 1490647 := bstep (se 1 (by rfl) ⟨1117985, by rfl⟩ : syracuseStep 1490647 = 2235971) B2235971
theorem B3186391 : Blo 1490065 3186391 := bstep (se 1 (by rfl) ⟨2389793, by rfl⟩ : syracuseStep 3186391 = 4779587) B4779587
theorem B6364889 : Blo 1490065 6364889 := bstep (se 2 (by rfl) ⟨2386833, by rfl⟩ : syracuseStep 6364889 = 4773667) B4773667
theorem B2236121 : Blo 1490065 2236121 := bstep (se 2 (by rfl) ⟨838545, by rfl⟩ : syracuseStep 2236121 = 1677091) B1677091
theorem B5660381 : Blo 1490065 5660381 := bstep (se 3 (by rfl) ⟨1061321, by rfl⟩ : syracuseStep 5660381 = 2122643) B2122643
theorem B1490667 : Blo 1490065 1490667 := bstep (se 1 (by rfl) ⟨1118000, by rfl⟩ : syracuseStep 1490667 = 2236001) B2236001
theorem B1490679 : Blo 1490065 1490679 := bstep (se 1 (by rfl) ⟨1118009, by rfl⟩ : syracuseStep 1490679 = 2236019) B2236019
theorem B1490699 : Blo 1490065 1490699 := bstep (se 1 (by rfl) ⟨1118024, by rfl⟩ : syracuseStep 1490699 = 2236049) B2236049
theorem B1490711 : Blo 1490065 1490711 := bstep (se 1 (by rfl) ⟨1118033, by rfl⟩ : syracuseStep 1490711 = 2236067) B2236067
theorem B1490731 : Blo 1490065 1490731 := bstep (se 1 (by rfl) ⟨1118048, by rfl⟩ : syracuseStep 1490731 = 2236097) B2236097
theorem B1490743 : Blo 1490065 1490743 := bstep (se 1 (by rfl) ⟨1118057, by rfl⟩ : syracuseStep 1490743 = 2236115) B2236115
theorem B3776321 : Blo 1490065 3776321 := bstep (se 2 (by rfl) ⟨1416120, by rfl⟩ : syracuseStep 3776321 = 2832241) B2832241
theorem B1490763 : Blo 1490065 1490763 := bstep (se 1 (by rfl) ⟨1118072, by rfl⟩ : syracuseStep 1490763 = 2236145) B2236145
theorem B2236235 : Blo 1490065 2236235 := bstep (se 1 (by rfl) ⟨1677176, by rfl⟩ : syracuseStep 2236235 = 3354353) B3354353
theorem B1490775 : Blo 1490065 1490775 := bstep (se 1 (by rfl) ⟨1118081, by rfl⟩ : syracuseStep 1490775 = 2236163) B2236163
theorem B5029721 : Blo 1490065 5029721 := bstep (se 2 (by rfl) ⟨1886145, by rfl⟩ : syracuseStep 5029721 = 3772291) B3772291
theorem B2236247 : Blo 1490065 2236247 := bstep (se 1 (by rfl) ⟨1677185, by rfl⟩ : syracuseStep 2236247 = 3354371) B3354371
theorem B1490795 : Blo 1490065 1490795 := bstep (se 1 (by rfl) ⟨1118096, by rfl⟩ : syracuseStep 1490795 = 2236193) B2236193
theorem B1490807 : Blo 1490065 1490807 := bstep (se 1 (by rfl) ⟨1118105, by rfl⟩ : syracuseStep 1490807 = 2236211) B2236211
theorem B2514827 : Blo 1490065 2514827 := bstep (se 1 (by rfl) ⟨1886120, by rfl⟩ : syracuseStep 2514827 = 3772241) B3772241
theorem B1490827 : Blo 1490065 1490827 := bstep (se 1 (by rfl) ⟨1118120, by rfl⟩ : syracuseStep 1490827 = 2236241) B2236241
theorem B1490839 : Blo 1490065 1490839 := bstep (se 1 (by rfl) ⟨1118129, by rfl⟩ : syracuseStep 1490839 = 2236259) B2236259
theorem B12738455 : Blo 1490065 12738455 := bstep (se 1 (by rfl) ⟨9553841, by rfl⟩ : syracuseStep 12738455 = 19107683) B19107683
theorem B2236313 : Blo 1490065 2236313 := bstep (se 2 (by rfl) ⟨838617, by rfl⟩ : syracuseStep 2236313 = 1677235) B1677235
theorem B1490859 : Blo 1490065 1490859 := bstep (se 1 (by rfl) ⟨1118144, by rfl⟩ : syracuseStep 1490859 = 2236289) B2236289
theorem B1490871 : Blo 1490065 1490871 := bstep (se 1 (by rfl) ⟨1118153, by rfl⟩ : syracuseStep 1490871 = 2236307) B2236307
theorem B6373313 : Blo 1490065 6373313 := bstep (se 2 (by rfl) ⟨2389992, by rfl⟩ : syracuseStep 6373313 = 4779985) B4779985
theorem B1490891 : Blo 1490065 1490891 := bstep (se 1 (by rfl) ⟨1118168, by rfl⟩ : syracuseStep 1490891 = 2236337) B2236337
theorem B1490903 : Blo 1490065 1490903 := bstep (se 1 (by rfl) ⟨1118177, by rfl⟩ : syracuseStep 1490903 = 2236355) B2236355
theorem B1490923 : Blo 1490065 1490923 := bstep (se 1 (by rfl) ⟨1118192, by rfl⟩ : syracuseStep 1490923 = 2236385) B2236385
theorem B1490951 : Blo 1490065 1490951 := bstep (se 1 (by rfl) ⟨1118213, by rfl⟩ : syracuseStep 1490951 = 2236427) B2236427
theorem B1490959 : Blo 1490065 1490959 := bstep (se 1 (by rfl) ⟨1118219, by rfl⟩ : syracuseStep 1490959 = 2236439) B2236439
theorem B12730391 : Blo 1490065 12730391 := bstep (se 1 (by rfl) ⟨9547793, by rfl⟩ : syracuseStep 12730391 = 19095587) B19095587
theorem B4243499 : Blo 1490065 4243499 := bstep (se 1 (by rfl) ⟨3182624, by rfl⟩ : syracuseStep 4243499 = 6365249) B6365249
theorem B2236475 : Blo 1490065 2236475 := bstep (se 1 (by rfl) ⟨1677356, by rfl⟩ : syracuseStep 2236475 = 3354713) B3354713
theorem B1491003 : Blo 1490065 1491003 := bstep (se 1 (by rfl) ⟨1118252, by rfl⟩ : syracuseStep 1491003 = 2236505) B2236505
theorem B2515063 : Blo 1490065 2515063 := bstep (se 1 (by rfl) ⟨1886297, by rfl⟩ : syracuseStep 2515063 = 3772595) B3772595
theorem B2236535 : Blo 1490065 2236535 := bstep (se 1 (by rfl) ⟨1677401, by rfl⟩ : syracuseStep 2236535 = 3354803) B3354803
theorem B1491079 : Blo 1490065 1491079 := bstep (se 1 (by rfl) ⟨1118309, by rfl⟩ : syracuseStep 1491079 = 2236619) B2236619
theorem B2236559 : Blo 1490065 2236559 := bstep (se 1 (by rfl) ⟨1677419, by rfl⟩ : syracuseStep 2236559 = 3354839) B3354839
theorem B1491087 : Blo 1490065 1491087 := bstep (se 1 (by rfl) ⟨1118315, by rfl⟩ : syracuseStep 1491087 = 2236631) B2236631
theorem B3776665 : Blo 1490065 3776665 := bstep (se 2 (by rfl) ⟨1416249, by rfl⟩ : syracuseStep 3776665 = 2832499) B2832499
theorem B2236601 : Blo 1490065 2236601 := bstep (se 2 (by rfl) ⟨838725, by rfl⟩ : syracuseStep 2236601 = 1677451) B1677451
theorem B1491131 : Blo 1490065 1491131 := bstep (se 1 (by rfl) ⟨1118348, by rfl⟩ : syracuseStep 1491131 = 2236697) B2236697
theorem B2236679 : Blo 1490065 2236679 := bstep (se 1 (by rfl) ⟨1677509, by rfl⟩ : syracuseStep 2236679 = 3355019) B3355019
theorem B1491207 : Blo 1490065 1491207 := bstep (se 1 (by rfl) ⟨1118405, by rfl⟩ : syracuseStep 1491207 = 2236811) B2236811
theorem B1491215 : Blo 1490065 1491215 := bstep (se 1 (by rfl) ⟨1118411, by rfl⟩ : syracuseStep 1491215 = 2236823) B2236823
theorem B2236715 : Blo 1490065 2236715 := bstep (se 1 (by rfl) ⟨1677536, by rfl⟩ : syracuseStep 2236715 = 3355073) B3355073
theorem B2515259 : Blo 1490065 2515259 := bstep (se 1 (by rfl) ⟨1886444, by rfl⟩ : syracuseStep 2515259 = 3772889) B3772889
theorem B1491259 : Blo 1490065 1491259 := bstep (se 1 (by rfl) ⟨1118444, by rfl⟩ : syracuseStep 1491259 = 2236889) B2236889
theorem B2236745 : Blo 1490065 2236745 := bstep (se 2 (by rfl) ⟨838779, by rfl⟩ : syracuseStep 2236745 = 1677559) B1677559
theorem B1491335 : Blo 1490065 1491335 := bstep (se 1 (by rfl) ⟨1118501, by rfl⟩ : syracuseStep 1491335 = 2237003) B2237003
theorem B1491343 : Blo 1490065 1491343 := bstep (se 1 (by rfl) ⟨1118507, by rfl⟩ : syracuseStep 1491343 = 2237015) B2237015
theorem B12730769 : Blo 1490065 12730769 := bstep (se 2 (by rfl) ⟨4774038, by rfl⟩ : syracuseStep 12730769 = 9548077) B9548077
theorem B2236859 : Blo 1490065 2236859 := bstep (se 1 (by rfl) ⟨1677644, by rfl⟩ : syracuseStep 2236859 = 3355289) B3355289
theorem B1491387 : Blo 1490065 1491387 := bstep (se 1 (by rfl) ⟨1118540, by rfl⟩ : syracuseStep 1491387 = 2237081) B2237081
theorem B2236919 : Blo 1490065 2236919 := bstep (se 1 (by rfl) ⟨1677689, by rfl⟩ : syracuseStep 2236919 = 3355379) B3355379
theorem B1491463 : Blo 1490065 1491463 := bstep (se 1 (by rfl) ⟨1118597, by rfl⟩ : syracuseStep 1491463 = 2237195) B2237195
theorem B2236943 : Blo 1490065 2236943 := bstep (se 1 (by rfl) ⟨1677707, by rfl⟩ : syracuseStep 2236943 = 3355415) B3355415
theorem B1491471 : Blo 1490065 1491471 := bstep (se 1 (by rfl) ⟨1118603, by rfl⟩ : syracuseStep 1491471 = 2237207) B2237207
theorem B9069079 : Blo 1490065 9069079 := bstep (se 1 (by rfl) ⟨6801809, by rfl⟩ : syracuseStep 9069079 = 13603619) B13603619
theorem B6455837 : Blo 1490065 6455837 := bstep (se 3 (by rfl) ⟨1210469, by rfl⟩ : syracuseStep 6455837 = 2420939) B2420939
theorem B36282923 : Blo 1490065 36282923 := bstep (se 1 (by rfl) ⟨27212192, by rfl⟩ : syracuseStep 36282923 = 54424385) B54424385
theorem B2236985 : Blo 1490065 2236985 := bstep (se 2 (by rfl) ⟨838869, by rfl⟩ : syracuseStep 2236985 = 1677739) B1677739
theorem B1491515 : Blo 1490065 1491515 := bstep (se 1 (by rfl) ⟨1118636, by rfl⟩ : syracuseStep 1491515 = 2237273) B2237273
theorem B12739139 : Blo 1490065 12739139 := bstep (se 1 (by rfl) ⟨9554354, by rfl⟩ : syracuseStep 12739139 = 19108709) B19108709
theorem B2237063 : Blo 1490065 2237063 := bstep (se 1 (by rfl) ⟨1677797, by rfl⟩ : syracuseStep 2237063 = 3355595) B3355595
theorem B1491591 : Blo 1490065 1491591 := bstep (se 1 (by rfl) ⟨1118693, by rfl⟩ : syracuseStep 1491591 = 2237387) B2237387
theorem B1491599 : Blo 1490065 1491599 := bstep (se 1 (by rfl) ⟨1118699, by rfl⟩ : syracuseStep 1491599 = 2237399) B2237399
theorem B2237099 : Blo 1490065 2237099 := bstep (se 1 (by rfl) ⟨1677824, by rfl⟩ : syracuseStep 2237099 = 3355649) B3355649
theorem B1491643 : Blo 1490065 1491643 := bstep (se 1 (by rfl) ⟨1118732, by rfl⟩ : syracuseStep 1491643 = 2237465) B2237465
theorem B2515657 : Blo 1490065 2515657 := bstep (se 2 (by rfl) ⟨943371, by rfl⟩ : syracuseStep 2515657 = 1886743) B1886743
theorem B2237129 : Blo 1490065 2237129 := bstep (se 2 (by rfl) ⟨838923, by rfl⟩ : syracuseStep 2237129 = 1677847) B1677847
theorem B36274949 : Blo 1490065 36274949 := bstep (se 4 (by rfl) ⟨3400776, by rfl⟩ : syracuseStep 36274949 = 6801553) B6801553
theorem B1491719 : Blo 1490065 1491719 := bstep (se 1 (by rfl) ⟨1118789, by rfl⟩ : syracuseStep 1491719 = 2237579) B2237579
theorem B1491727 : Blo 1490065 1491727 := bstep (se 1 (by rfl) ⟨1118795, by rfl⟩ : syracuseStep 1491727 = 2237591) B2237591
theorem B2237243 : Blo 1490065 2237243 := bstep (se 1 (by rfl) ⟨1677932, by rfl⟩ : syracuseStep 2237243 = 3355865) B3355865
theorem B1491771 : Blo 1490065 1491771 := bstep (se 1 (by rfl) ⟨1118828, by rfl⟩ : syracuseStep 1491771 = 2237657) B2237657
theorem B2122615 : Blo 1490065 2122615 := bstep (se 1 (by rfl) ⟨1591961, by rfl⟩ : syracuseStep 2122615 = 3183923) B3183923
theorem B2237303 : Blo 1490065 2237303 := bstep (se 1 (by rfl) ⟨1677977, by rfl⟩ : syracuseStep 2237303 = 3355955) B3355955
theorem B1491847 : Blo 1490065 1491847 := bstep (se 1 (by rfl) ⟨1118885, by rfl⟩ : syracuseStep 1491847 = 2237771) B2237771
theorem B2237327 : Blo 1490065 2237327 := bstep (se 1 (by rfl) ⟨1677995, by rfl⟩ : syracuseStep 2237327 = 3355991) B3355991
theorem B1491855 : Blo 1490065 1491855 := bstep (se 1 (by rfl) ⟨1118891, by rfl⟩ : syracuseStep 1491855 = 2237783) B2237783
theorem B2237369 : Blo 1490065 2237369 := bstep (se 2 (by rfl) ⟨839013, by rfl⟩ : syracuseStep 2237369 = 1678027) B1678027
theorem B1491899 : Blo 1490065 1491899 := bstep (se 1 (by rfl) ⟨1118924, by rfl⟩ : syracuseStep 1491899 = 2237849) B2237849
theorem B2237447 : Blo 1490065 2237447 := bstep (se 1 (by rfl) ⟨1678085, by rfl⟩ : syracuseStep 2237447 = 3356171) B3356171
theorem B1491975 : Blo 1490065 1491975 := bstep (se 1 (by rfl) ⟨1118981, by rfl⟩ : syracuseStep 1491975 = 2237963) B2237963
theorem B1491983 : Blo 1490065 1491983 := bstep (se 1 (by rfl) ⟨1118987, by rfl⟩ : syracuseStep 1491983 = 2237975) B2237975
theorem B2237483 : Blo 1490065 2237483 := bstep (se 1 (by rfl) ⟨1678112, by rfl⟩ : syracuseStep 2237483 = 3356225) B3356225
theorem B1492027 : Blo 1490065 1492027 := bstep (se 1 (by rfl) ⟨1119020, by rfl⟩ : syracuseStep 1492027 = 2238041) B2238041
theorem B2237513 : Blo 1490065 2237513 := bstep (se 2 (by rfl) ⟨839067, by rfl⟩ : syracuseStep 2237513 = 1678135) B1678135
theorem B2122939 : Blo 1490065 2122939 := bstep (se 1 (by rfl) ⟨1592204, by rfl⟩ : syracuseStep 2122939 = 3184409) B3184409
theorem B2237627 : Blo 1490065 2237627 := bstep (se 1 (by rfl) ⟨1678220, by rfl⟩ : syracuseStep 2237627 = 3356441) B3356441
theorem B2237687 : Blo 1490065 2237687 := bstep (se 1 (by rfl) ⟨1678265, by rfl⟩ : syracuseStep 2237687 = 3356531) B3356531
theorem B2237711 : Blo 1490065 2237711 := bstep (se 1 (by rfl) ⟨1678283, by rfl⟩ : syracuseStep 2237711 = 3356567) B3356567
theorem B2237753 : Blo 1490065 2237753 := bstep (se 2 (by rfl) ⟨839157, by rfl⟩ : syracuseStep 2237753 = 1678315) B1678315
theorem B2516359 : Blo 1490065 2516359 := bstep (se 1 (by rfl) ⟨1887269, by rfl⟩ : syracuseStep 2516359 = 3774539) B3774539
theorem B2237831 : Blo 1490065 2237831 := bstep (se 1 (by rfl) ⟨1678373, by rfl⟩ : syracuseStep 2237831 = 3356747) B3356747
theorem B2688403 : Blo 1490065 2688403 := bstep (se 1 (by rfl) ⟨2016302, by rfl⟩ : syracuseStep 2688403 = 4032605) B4032605
theorem B2237867 : Blo 1490065 2237867 := bstep (se 1 (by rfl) ⟨1678400, by rfl⟩ : syracuseStep 2237867 = 3356801) B3356801
theorem B2237897 : Blo 1490065 2237897 := bstep (se 2 (by rfl) ⟨839211, by rfl⟩ : syracuseStep 2237897 = 1678423) B1678423
theorem B5735947 : Blo 1490065 5735947 := bstep (se 1 (by rfl) ⟨4301960, by rfl⟩ : syracuseStep 5735947 = 8603921) B8603921
theorem B2238011 : Blo 1490065 2238011 := bstep (se 1 (by rfl) ⟨1678508, by rfl⟩ : syracuseStep 2238011 = 3357017) B3357017
theorem B5662295 : Blo 1490065 5662295 := bstep (se 1 (by rfl) ⟨4246721, by rfl⟩ : syracuseStep 5662295 = 8493443) B8493443
theorem B2238071 : Blo 1490065 2238071 := bstep (se 1 (by rfl) ⟨1678553, by rfl⟩ : syracuseStep 2238071 = 3357107) B3357107
theorem B2238095 : Blo 1490065 2238095 := bstep (se 1 (by rfl) ⟨1678571, by rfl⟩ : syracuseStep 2238095 = 3357143) B3357143
theorem B3827353 : Blo 1490065 3827353 := bstep (se 2 (by rfl) ⟨1435257, by rfl⟩ : syracuseStep 3827353 = 2870515) B2870515
theorem B2123435 : Blo 1490065 2123435 := bstep (se 1 (by rfl) ⟨1592576, by rfl⟩ : syracuseStep 2123435 = 3185153) B3185153
theorem B4531913 : Blo 1490065 4531913 := bstep (se 2 (by rfl) ⟨1699467, by rfl⟩ : syracuseStep 4531913 = 3398935) B3398935
theorem B1885943 : Blo 1490065 1885943 := bstep (se 1 (by rfl) ⟨1414457, by rfl⟩ : syracuseStep 1885943 = 2828915) B2828915
theorem B4302607 : Blo 1490065 4302607 := bstep (se 1 (by rfl) ⟨3226955, by rfl⟩ : syracuseStep 4302607 = 6453911) B6453911
theorem B19367755 : Blo 1490065 19367755 := bstep (se 1 (by rfl) ⟨14525816, by rfl⟩ : syracuseStep 19367755 = 29051633) B29051633
theorem B1886095 : Blo 1490065 1886095 := bstep (se 1 (by rfl) ⟨1414571, by rfl⟩ : syracuseStep 1886095 = 2829143) B2829143
theorem B7546769 : Blo 1490065 7546769 := bstep (se 2 (by rfl) ⟨2830038, by rfl⟩ : syracuseStep 7546769 = 5660077) B5660077
theorem B5031827 : Blo 1490065 5031827 := bstep (se 1 (by rfl) ⟨3773870, by rfl⟩ : syracuseStep 5031827 = 7547741) B7547741
theorem B2869177 : Blo 1490065 2869177 := bstep (se 2 (by rfl) ⟨1075941, by rfl⟩ : syracuseStep 2869177 = 2151883) B2151883
theorem B2517007 : Blo 1490065 2517007 := bstep (se 1 (by rfl) ⟨1887755, by rfl⟩ : syracuseStep 2517007 = 3775511) B3775511
theorem B13781015 : Blo 1490065 13781015 := bstep (se 1 (by rfl) ⟨10335761, by rfl⟩ : syracuseStep 13781015 = 20671523) B20671523
theorem B1886267 : Blo 1490065 1886267 := bstep (se 1 (by rfl) ⟨1414700, by rfl⟩ : syracuseStep 1886267 = 2829401) B2829401
theorem B5662781 : Blo 1490065 5662781 := bstep (se 3 (by rfl) ⟨1061771, by rfl⟩ : syracuseStep 5662781 = 2123543) B2123543
theorem B1591483 : Blo 1490065 1591483 := bstep (se 1 (by rfl) ⟨1193612, by rfl⟩ : syracuseStep 1591483 = 2387225) B2387225
theorem B5736685 : Blo 1490065 5736685 := bstep (se 3 (by rfl) ⟨1075628, by rfl⟩ : syracuseStep 5736685 = 2151257) B2151257
theorem B3352967 : Blo 1490065 3352967 := bstep (se 1 (by rfl) ⟨2514725, by rfl⟩ : syracuseStep 3352967 = 5029451) B5029451
theorem B14338451 : Blo 1490065 14338451 := bstep (se 1 (by rfl) ⟨10753838, by rfl⟩ : syracuseStep 14338451 = 21507677) B21507677
theorem B9554435 : Blo 1490065 9554435 := bstep (se 1 (by rfl) ⟨7165826, by rfl⟩ : syracuseStep 9554435 = 14331653) B14331653
theorem B2517547 : Blo 1490065 2517547 := bstep (se 1 (by rfl) ⟨1888160, by rfl⟩ : syracuseStep 2517547 = 3776321) B3776321
theorem B3353147 : Blo 1490065 3353147 := bstep (se 1 (by rfl) ⟨2514860, by rfl⟩ : syracuseStep 3353147 = 5029721) B5029721
theorem B3353273 : Blo 1490065 3353273 := bstep (se 2 (by rfl) ⟨1257477, by rfl⟩ : syracuseStep 3353273 = 2514955) B2514955
theorem B2517689 : Blo 1490065 2517689 := bstep (se 2 (by rfl) ⟨944133, by rfl⟩ : syracuseStep 2517689 = 1888267) B1888267
theorem B65399501 : Blo 1490065 65399501 := bstep (se 3 (by rfl) ⟨12262406, by rfl⟩ : syracuseStep 65399501 = 24524813) B24524813
theorem B3877633 : Blo 1490065 3877633 := bstep (se 2 (by rfl) ⟨1454112, by rfl⟩ : syracuseStep 3877633 = 2908225) B2908225
theorem B9186085 : Blo 1490065 9186085 := bstep (se 4 (by rfl) ⟨861195, by rfl⟩ : syracuseStep 9186085 = 1722391) B1722391
theorem B8063803 : Blo 1490065 8063803 := bstep (se 1 (by rfl) ⟨6047852, by rfl⟩ : syracuseStep 8063803 = 12095705) B12095705
theorem B8489843 : Blo 1490065 8489843 := bstep (se 1 (by rfl) ⟨6367382, by rfl⟩ : syracuseStep 8489843 = 12734765) B12734765
theorem B1911799 : Blo 1490065 1911799 := bstep (se 1 (by rfl) ⟨1433849, by rfl⟩ : syracuseStep 1911799 = 2867699) B2867699
theorem B1887239 : Blo 1490065 1887239 := bstep (se 1 (by rfl) ⟨1415429, by rfl⟩ : syracuseStep 1887239 = 2830859) B2830859
theorem B3353615 : Blo 1490065 3353615 := bstep (se 1 (by rfl) ⟨2515211, by rfl⟩ : syracuseStep 3353615 = 5030423) B5030423
theorem B3353633 : Blo 1490065 3353633 := bstep (se 2 (by rfl) ⟨1257612, by rfl⟩ : syracuseStep 3353633 = 2515225) B2515225
theorem B2829431 : Blo 1490065 2829431 := bstep (se 1 (by rfl) ⟨2122073, by rfl⟩ : syracuseStep 2829431 = 4244147) B4244147
theorem B8056037 : Blo 1490065 8056037 := bstep (se 4 (by rfl) ⟨755253, by rfl⟩ : syracuseStep 8056037 = 1510507) B1510507
theorem B2829583 : Blo 1490065 2829583 := bstep (se 1 (by rfl) ⟨2122187, by rfl⟩ : syracuseStep 2829583 = 4244375) B4244375
theorem B5033231 : Blo 1490065 5033231 := bstep (se 1 (by rfl) ⟨3774923, by rfl⟩ : syracuseStep 5033231 = 7549847) B7549847
theorem B3353975 : Blo 1490065 3353975 := bstep (se 1 (by rfl) ⟨2515481, by rfl⟩ : syracuseStep 3353975 = 5030963) B5030963
theorem B6368665 : Blo 1490065 6368665 := bstep (se 2 (by rfl) ⟨2388249, by rfl⟩ : syracuseStep 6368665 = 4776499) B4776499
theorem B24178105 : Blo 1490065 24178105 := bstep (se 2 (by rfl) ⟨9066789, by rfl⟩ : syracuseStep 24178105 = 18133579) B18133579
theorem B8613323 : Blo 1490065 8613323 := bstep (se 1 (by rfl) ⟨6459992, by rfl⟩ : syracuseStep 8613323 = 12919985) B12919985
theorem B48344525 : Blo 1490065 48344525 := bstep (se 3 (by rfl) ⟨9064598, by rfl⟩ : syracuseStep 48344525 = 18129197) B18129197
theorem B19115473 : Blo 1490065 19115473 := bstep (se 2 (by rfl) ⟨7168302, by rfl⟩ : syracuseStep 19115473 = 14336605) B14336605
theorem B5033501 : Blo 1490065 5033501 := bstep (se 3 (by rfl) ⟨943781, by rfl⟩ : syracuseStep 5033501 = 1887563) B1887563
theorem B3771947 : Blo 1490065 3771947 := bstep (se 1 (by rfl) ⟨2828960, by rfl⟩ : syracuseStep 3771947 = 5657921) B5657921
theorem B3354155 : Blo 1490065 3354155 := bstep (se 1 (by rfl) ⟨2515616, by rfl⟩ : syracuseStep 3354155 = 5031233) B5031233
theorem B1887887 : Blo 1490065 1887887 := bstep (se 1 (by rfl) ⟨1415915, by rfl⟩ : syracuseStep 1887887 = 2831831) B2831831
theorem B2829971 : Blo 1490065 2829971 := bstep (se 1 (by rfl) ⟨2122478, by rfl⟩ : syracuseStep 2829971 = 4244957) B4244957
theorem B3632897 : Blo 1490065 3632897 := bstep (se 2 (by rfl) ⟨1362336, by rfl⟩ : syracuseStep 3632897 = 2724673) B2724673
theorem B3583759 : Blo 1490065 3583759 := bstep (se 1 (by rfl) ⟨2687819, by rfl⟩ : syracuseStep 3583759 = 5375639) B5375639
theorem B3354515 : Blo 1490065 3354515 := bstep (se 1 (by rfl) ⟨2515886, by rfl⟩ : syracuseStep 3354515 = 5031773) B5031773
theorem B2387897 : Blo 1490065 2387897 := bstep (se 2 (by rfl) ⟨895461, by rfl⟩ : syracuseStep 2387897 = 1790923) B1790923
theorem B3354569 : Blo 1490065 3354569 := bstep (se 2 (by rfl) ⟨1257963, by rfl⟩ : syracuseStep 3354569 = 2515927) B2515927
theorem B7548875 : Blo 1490065 7548875 := bstep (se 1 (by rfl) ⟨5661656, by rfl⟩ : syracuseStep 7548875 = 11323313) B11323313
theorem B12742829 : Blo 1490065 12742829 := bstep (se 3 (by rfl) ⟨2389280, by rfl⟩ : syracuseStep 12742829 = 4778561) B4778561
theorem B7549199 : Blo 1490065 7549199 := bstep (se 1 (by rfl) ⟨5661899, by rfl⟩ : syracuseStep 7549199 = 11323799) B11323799
theorem B8491301 : Blo 1490065 8491301 := bstep (se 4 (by rfl) ⟨796059, by rfl⟩ : syracuseStep 8491301 = 1592119) B1592119
theorem B3584375 : Blo 1490065 3584375 := bstep (se 1 (by rfl) ⟨2688281, by rfl⟩ : syracuseStep 3584375 = 5376563) B5376563
theorem B7164305 : Blo 1490065 7164305 := bstep (se 2 (by rfl) ⟨2686614, by rfl⟩ : syracuseStep 7164305 = 5373229) B5373229
theorem B2388409 : Blo 1490065 2388409 := bstep (se 2 (by rfl) ⟨895653, by rfl⟩ : syracuseStep 2388409 = 1791307) B1791307
theorem B4248065 : Blo 1490065 4248065 := bstep (se 2 (by rfl) ⟨1593024, by rfl⟩ : syracuseStep 4248065 = 3186049) B3186049
theorem B3772939 : Blo 1490065 3772939 := bstep (se 1 (by rfl) ⟨2829704, by rfl⟩ : syracuseStep 3772939 = 5659409) B5659409
theorem B6369911 : Blo 1490065 6369911 := bstep (se 1 (by rfl) ⟨4777433, by rfl⟩ : syracuseStep 6369911 = 9554867) B9554867
theorem B3183239 : Blo 1490065 3183239 := bstep (se 1 (by rfl) ⟨2387429, by rfl⟩ : syracuseStep 3183239 = 4774859) B4774859
theorem B3355271 : Blo 1490065 3355271 := bstep (se 1 (by rfl) ⟨2516453, by rfl⟩ : syracuseStep 3355271 = 5032907) B5032907
theorem B3773081 : Blo 1490065 3773081 := bstep (se 2 (by rfl) ⟨1414905, by rfl⟩ : syracuseStep 3773081 = 2829811) B2829811
theorem B10744613 : Blo 1490065 10744613 := bstep (se 4 (by rfl) ⟨1007307, by rfl⟩ : syracuseStep 10744613 = 2014615) B2014615
theorem B3773243 : Blo 1490065 3773243 := bstep (se 1 (by rfl) ⟨2829932, by rfl⟩ : syracuseStep 3773243 = 5659865) B5659865
theorem B3355451 : Blo 1490065 3355451 := bstep (se 1 (by rfl) ⟨2516588, by rfl⟩ : syracuseStep 3355451 = 5033177) B5033177
theorem B12743513 : Blo 1490065 12743513 := bstep (se 2 (by rfl) ⟨4778817, by rfl⟩ : syracuseStep 12743513 = 9557635) B9557635
theorem B1913743 : Blo 1490065 1913743 := bstep (se 1 (by rfl) ⟨1435307, by rfl⟩ : syracuseStep 1913743 = 2870615) B2870615
theorem B5034905 : Blo 1490065 5034905 := bstep (se 2 (by rfl) ⟨1888089, by rfl⟩ : syracuseStep 5034905 = 3776179) B3776179
theorem B8278969 : Blo 1490065 8278969 := bstep (se 2 (by rfl) ⟨3104613, by rfl⟩ : syracuseStep 8278969 = 6209227) B6209227
theorem B3355577 : Blo 1490065 3355577 := bstep (se 2 (by rfl) ⟨1258341, by rfl⟩ : syracuseStep 3355577 = 2516683) B2516683
theorem B4248521 : Blo 1490065 4248521 := bstep (se 2 (by rfl) ⟨1593195, by rfl⟩ : syracuseStep 4248521 = 3186391) B3186391
theorem B8491985 : Blo 1490065 8491985 := bstep (se 2 (by rfl) ⟨3184494, by rfl⟩ : syracuseStep 8491985 = 6368989) B6368989
theorem B1864711 : Blo 1490065 1864711 := bstep (se 1 (by rfl) ⟨1398533, by rfl⟩ : syracuseStep 1864711 = 2797067) B2797067
theorem B2266127 : Blo 1490065 2266127 := bstep (se 1 (by rfl) ⟨1699595, by rfl⟩ : syracuseStep 2266127 = 3399191) B3399191
theorem B2831375 : Blo 1490065 2831375 := bstep (se 1 (by rfl) ⟨2123531, by rfl⟩ : syracuseStep 2831375 = 4247063) B4247063
theorem B5370923 : Blo 1490065 5370923 := bstep (se 1 (by rfl) ⟨4028192, by rfl⟩ : syracuseStep 5370923 = 8056385) B8056385
theorem B2585659 : Blo 1490065 2585659 := bstep (se 1 (by rfl) ⟨1939244, by rfl⟩ : syracuseStep 2585659 = 3878489) B3878489
theorem B3773587 : Blo 1490065 3773587 := bstep (se 1 (by rfl) ⟨2830190, by rfl⟩ : syracuseStep 3773587 = 5660381) B5660381
theorem B1676551 : Blo 1490065 1676551 := bstep (se 1 (by rfl) ⟨1257413, by rfl⟩ : syracuseStep 1676551 = 2514827) B2514827
theorem B8492303 : Blo 1490065 8492303 := bstep (se 1 (by rfl) ⟨6369227, by rfl⟩ : syracuseStep 8492303 = 12738455) B12738455
theorem B3355919 : Blo 1490065 3355919 := bstep (se 1 (by rfl) ⟨2516939, by rfl⟩ : syracuseStep 3355919 = 5033879) B5033879
theorem B3773729 : Blo 1490065 3773729 := bstep (se 2 (by rfl) ⟨1415148, by rfl⟩ : syracuseStep 3773729 = 2830297) B2830297
theorem B21501217 : Blo 1490065 21501217 := bstep (se 2 (by rfl) ⟨8062956, by rfl⟩ : syracuseStep 21501217 = 16125913) B16125913
theorem B3355937 : Blo 1490065 3355937 := bstep (se 2 (by rfl) ⟨1258476, by rfl⟩ : syracuseStep 3355937 = 2516953) B2516953
theorem B4248875 : Blo 1490065 4248875 := bstep (se 1 (by rfl) ⟨3186656, by rfl⟩ : syracuseStep 4248875 = 6373313) B6373313
theorem B4838771 : Blo 1490065 4838771 := bstep (se 1 (by rfl) ⟨3629078, by rfl⟩ : syracuseStep 4838771 = 7258157) B7258157
theorem B1676731 : Blo 1490065 1676731 := bstep (se 1 (by rfl) ⟨1257548, by rfl⟩ : syracuseStep 1676731 = 2515097) B2515097
theorem B2831915 : Blo 1490065 2831915 := bstep (se 1 (by rfl) ⟨2123936, by rfl⟩ : syracuseStep 2831915 = 4247873) B4247873
theorem B2299435 : Blo 1490065 2299435 := bstep (se 1 (by rfl) ⟨1724576, by rfl⟩ : syracuseStep 2299435 = 3449153) B3449153
theorem B5035607 : Blo 1490065 5035607 := bstep (se 1 (by rfl) ⟨3776705, by rfl⟩ : syracuseStep 5035607 = 7553411) B7553411
theorem B3356279 : Blo 1490065 3356279 := bstep (se 1 (by rfl) ⟨2517209, by rfl⟩ : syracuseStep 3356279 = 5034419) B5034419
theorem B7550657 : Blo 1490065 7550657 := bstep (se 2 (by rfl) ⟨2831496, by rfl⟩ : syracuseStep 7550657 = 5662993) B5662993
theorem B5740321 : Blo 1490065 5740321 := bstep (se 2 (by rfl) ⟨2152620, by rfl⟩ : syracuseStep 5740321 = 4305241) B4305241
theorem B17446691 : Blo 1490065 17446691 := bstep (se 1 (by rfl) ⟨13085018, by rfl⟩ : syracuseStep 17446691 = 26170037) B26170037
theorem B3184427 : Blo 1490065 3184427 := bstep (se 1 (by rfl) ⟨2388320, by rfl⟩ : syracuseStep 3184427 = 4776641) B4776641
theorem B3356459 : Blo 1490065 3356459 := bstep (se 1 (by rfl) ⟨2517344, by rfl⟩ : syracuseStep 3356459 = 5034689) B5034689
theorem B19380017 : Blo 1490065 19380017 := bstep (se 2 (by rfl) ⟨7267506, by rfl⟩ : syracuseStep 19380017 = 14535013) B14535013
theorem B2389819 : Blo 1490065 2389819 := bstep (se 1 (by rfl) ⟨1792364, by rfl⟩ : syracuseStep 2389819 = 3584729) B3584729
theorem B1677199 : Blo 1490065 1677199 := bstep (se 1 (by rfl) ⟨1257899, by rfl⟩ : syracuseStep 1677199 = 2515799) B2515799
theorem B2389961 : Blo 1490065 2389961 := bstep (se 2 (by rfl) ⟨896235, by rfl⟩ : syracuseStep 2389961 = 1792471) B1792471
theorem B5371991 : Blo 1490065 5371991 := bstep (se 1 (by rfl) ⟨4028993, by rfl⟩ : syracuseStep 5371991 = 8057987) B8057987
theorem B3356819 : Blo 1490065 3356819 := bstep (se 1 (by rfl) ⟨2517614, by rfl⟩ : syracuseStep 3356819 = 5035229) B5035229
theorem B3356873 : Blo 1490065 3356873 := bstep (se 2 (by rfl) ⟨1258827, by rfl⟩ : syracuseStep 3356873 = 2517655) B2517655
theorem B17217773 : Blo 1490065 17217773 := bstep (se 3 (by rfl) ⟨3228332, by rfl⟩ : syracuseStep 17217773 = 6456665) B6456665
theorem B3774721 : Blo 1490065 3774721 := bstep (se 2 (by rfl) ⟨1415520, by rfl⟩ : syracuseStep 3774721 = 2831041) B2831041
theorem B7649569 : Blo 1490065 7649569 := bstep (se 2 (by rfl) ⟨2868588, by rfl⟩ : syracuseStep 7649569 = 5737177) B5737177
theorem B1677703 : Blo 1490065 1677703 := bstep (se 1 (by rfl) ⟨1258277, by rfl⟩ : syracuseStep 1677703 = 2516555) B2516555
theorem B8608153 : Blo 1490065 8608153 := bstep (se 2 (by rfl) ⟨3228057, by rfl⟩ : syracuseStep 8608153 = 6456115) B6456115
theorem B9066937 : Blo 1490065 9066937 := bstep (se 2 (by rfl) ⟨3400101, by rfl⟩ : syracuseStep 9066937 = 6800203) B6800203
theorem B9558557 : Blo 1490065 9558557 := bstep (se 3 (by rfl) ⟨1792229, by rfl⟩ : syracuseStep 9558557 = 3584459) B3584459
theorem B1677883 : Blo 1490065 1677883 := bstep (se 1 (by rfl) ⟨1258412, by rfl⟩ : syracuseStep 1677883 = 2516825) B2516825
theorem B8493761 : Blo 1490065 8493761 := bstep (se 2 (by rfl) ⟨3185160, by rfl⟩ : syracuseStep 8493761 = 6370321) B6370321
theorem B2235143 : Blo 1490065 2235143 := bstep (se 1 (by rfl) ⟨1676357, by rfl⟩ : syracuseStep 2235143 = 3352715) B3352715
theorem B2235179 : Blo 1490065 2235179 := bstep (se 1 (by rfl) ⟨1676384, by rfl⟩ : syracuseStep 2235179 = 3352769) B3352769
theorem B2235209 : Blo 1490065 2235209 := bstep (se 2 (by rfl) ⟨838203, by rfl⟩ : syracuseStep 2235209 = 1676407) B1676407
theorem B3775319 : Blo 1490065 3775319 := bstep (se 1 (by rfl) ⟨2831489, by rfl⟩ : syracuseStep 3775319 = 5662979) B5662979
theorem B16120727 : Blo 1490065 16120727 := bstep (se 1 (by rfl) ⟨12090545, by rfl⟩ : syracuseStep 16120727 = 24181091) B24181091
theorem B5659577 : Blo 1490065 5659577 := bstep (se 2 (by rfl) ⟨2122341, by rfl⟩ : syracuseStep 5659577 = 4244683) B4244683
theorem B2235323 : Blo 1490065 2235323 := bstep (se 1 (by rfl) ⟨1676492, by rfl⟩ : syracuseStep 2235323 = 3352985) B3352985
theorem B7551953 : Blo 1490065 7551953 := bstep (se 2 (by rfl) ⟨2831982, by rfl⟩ : syracuseStep 7551953 = 5663965) B5663965
theorem B2235383 : Blo 1490065 2235383 := bstep (se 1 (by rfl) ⟨1676537, by rfl⟩ : syracuseStep 2235383 = 3353075) B3353075
theorem B2235407 : Blo 1490065 2235407 := bstep (se 1 (by rfl) ⟨1676555, by rfl⟩ : syracuseStep 2235407 = 3353111) B3353111
theorem B1678351 : Blo 1490065 1678351 := bstep (se 1 (by rfl) ⟨1258763, by rfl⟩ : syracuseStep 1678351 = 2517527) B2517527
theorem B9550871 : Blo 1490065 9550871 := bstep (se 1 (by rfl) ⟨7163153, by rfl⟩ : syracuseStep 9550871 = 14326307) B14326307
theorem B3775531 : Blo 1490065 3775531 := bstep (se 1 (by rfl) ⟨2831648, by rfl⟩ : syracuseStep 3775531 = 5663297) B5663297
theorem B2235449 : Blo 1490065 2235449 := bstep (se 2 (by rfl) ⟨838293, by rfl⟩ : syracuseStep 2235449 = 1676587) B1676587
theorem B21503063 : Blo 1490065 21503063 := bstep (se 1 (by rfl) ⟨16127297, by rfl⟩ : syracuseStep 21503063 = 32254595) B32254595
theorem B3103879 : Blo 1490065 3103879 := bstep (se 1 (by rfl) ⟨2327909, by rfl⟩ : syracuseStep 3103879 = 4655819) B4655819
theorem B2235527 : Blo 1490065 2235527 := bstep (se 1 (by rfl) ⟨1676645, by rfl⟩ : syracuseStep 2235527 = 3353291) B3353291
theorem B2235563 : Blo 1490065 2235563 := bstep (se 1 (by rfl) ⟨1676672, by rfl⟩ : syracuseStep 2235563 = 3353345) B3353345
theorem B3775673 : Blo 1490065 3775673 := bstep (se 2 (by rfl) ⟨1415877, by rfl⟩ : syracuseStep 3775673 = 2831755) B2831755
theorem B1490107 : Blo 1490065 1490107 := bstep (se 1 (by rfl) ⟨1117580, by rfl⟩ : syracuseStep 1490107 = 2235161) B2235161
theorem B2235593 : Blo 1490065 2235593 := bstep (se 2 (by rfl) ⟨838347, by rfl⟩ : syracuseStep 2235593 = 1676695) B1676695
theorem B1490183 : Blo 1490065 1490183 := bstep (se 1 (by rfl) ⟨1117637, by rfl⟩ : syracuseStep 1490183 = 2235275) B2235275
theorem B1490191 : Blo 1490065 1490191 := bstep (se 1 (by rfl) ⟨1117643, by rfl⟩ : syracuseStep 1490191 = 2235287) B2235287
theorem B1490235 : Blo 1490065 1490235 := bstep (se 1 (by rfl) ⟨1117676, by rfl⟩ : syracuseStep 1490235 = 2235353) B2235353
theorem B2235707 : Blo 1490065 2235707 := bstep (se 1 (by rfl) ⟨1676780, by rfl⟩ : syracuseStep 2235707 = 3353561) B3353561
theorem B5029235 : Blo 1490065 5029235 := bstep (se 1 (by rfl) ⟨3771926, by rfl⟩ : syracuseStep 5029235 = 7543853) B7543853
theorem B2235767 : Blo 1490065 2235767 := bstep (se 1 (by rfl) ⟨1676825, by rfl⟩ : syracuseStep 2235767 = 3353651) B3353651
theorem B1490311 : Blo 1490065 1490311 := bstep (se 1 (by rfl) ⟨1117733, by rfl⟩ : syracuseStep 1490311 = 2235467) B2235467
theorem B1490319 : Blo 1490065 1490319 := bstep (se 1 (by rfl) ⟨1117739, by rfl⟩ : syracuseStep 1490319 = 2235479) B2235479
theorem B2235791 : Blo 1490065 2235791 := bstep (se 1 (by rfl) ⟨1676843, by rfl⟩ : syracuseStep 2235791 = 3353687) B3353687
theorem B3186067 : Blo 1490065 3186067 := bstep (se 1 (by rfl) ⟨2389550, by rfl⟩ : syracuseStep 3186067 = 4779101) B4779101
theorem B2235833 : Blo 1490065 2235833 := bstep (se 2 (by rfl) ⟨838437, by rfl⟩ : syracuseStep 2235833 = 1676875) B1676875
theorem B1490363 : Blo 1490065 1490363 := bstep (se 1 (by rfl) ⟨1117772, by rfl⟩ : syracuseStep 1490363 = 2235545) B2235545
theorem B19111373 : Blo 1490065 19111373 := bstep (se 3 (by rfl) ⟨3583382, by rfl⟩ : syracuseStep 19111373 = 7166765) B7166765
theorem B1490439 : Blo 1490065 1490439 := bstep (se 1 (by rfl) ⟨1117829, by rfl⟩ : syracuseStep 1490439 = 2235659) B2235659
theorem B2235911 : Blo 1490065 2235911 := bstep (se 1 (by rfl) ⟨1676933, by rfl⟩ : syracuseStep 2235911 = 3353867) B3353867
theorem B1490447 : Blo 1490065 1490447 := bstep (se 1 (by rfl) ⟨1117835, by rfl⟩ : syracuseStep 1490447 = 2235671) B2235671
theorem B2235947 : Blo 1490065 2235947 := bstep (se 1 (by rfl) ⟨1676960, by rfl⟩ : syracuseStep 2235947 = 3353921) B3353921
theorem B1490491 : Blo 1490065 1490491 := bstep (se 1 (by rfl) ⟨1117868, by rfl⟩ : syracuseStep 1490491 = 2235737) B2235737
theorem B2235977 : Blo 1490065 2235977 := bstep (se 2 (by rfl) ⟨838491, by rfl⟩ : syracuseStep 2235977 = 1676983) B1676983
theorem B1490567 : Blo 1490065 1490567 := bstep (se 1 (by rfl) ⟨1117925, by rfl⟩ : syracuseStep 1490567 = 2235851) B2235851
theorem B4030087 : Blo 1490065 4030087 := bstep (se 1 (by rfl) ⟨3022565, by rfl⟩ : syracuseStep 4030087 = 6045131) B6045131
theorem B1490575 : Blo 1490065 1490575 := bstep (se 1 (by rfl) ⟨1117931, by rfl⟩ : syracuseStep 1490575 = 2235863) B2235863
theorem B1490619 : Blo 1490065 1490619 := bstep (se 1 (by rfl) ⟨1117964, by rfl⟩ : syracuseStep 1490619 = 2235929) B2235929
theorem B2236091 : Blo 1490065 2236091 := bstep (se 1 (by rfl) ⟨1677068, by rfl⟩ : syracuseStep 2236091 = 3354137) B3354137
theorem B2236151 : Blo 1490065 2236151 := bstep (se 1 (by rfl) ⟨1677113, by rfl⟩ : syracuseStep 2236151 = 3354227) B3354227
theorem B1490695 : Blo 1490065 1490695 := bstep (se 1 (by rfl) ⟨1118021, by rfl⟩ : syracuseStep 1490695 = 2236043) B2236043
theorem B1490703 : Blo 1490065 1490703 := bstep (se 1 (by rfl) ⟨1118027, by rfl⟩ : syracuseStep 1490703 = 2236055) B2236055
theorem B2236175 : Blo 1490065 2236175 := bstep (se 1 (by rfl) ⟨1677131, by rfl⟩ : syracuseStep 2236175 = 3354263) B3354263
theorem B2236217 : Blo 1490065 2236217 := bstep (se 2 (by rfl) ⟨838581, by rfl⟩ : syracuseStep 2236217 = 1677163) B1677163
theorem B4243259 : Blo 1490065 4243259 := bstep (se 1 (by rfl) ⟨3182444, by rfl⟩ : syracuseStep 4243259 = 6364889) B6364889
theorem B1490747 : Blo 1490065 1490747 := bstep (se 1 (by rfl) ⟨1118060, by rfl⟩ : syracuseStep 1490747 = 2236121) B2236121
theorem B1490823 : Blo 1490065 1490823 := bstep (se 1 (by rfl) ⟨1118117, by rfl⟩ : syracuseStep 1490823 = 2236235) B2236235
theorem B2236295 : Blo 1490065 2236295 := bstep (se 1 (by rfl) ⟨1677221, by rfl⟩ : syracuseStep 2236295 = 3354443) B3354443
theorem B1490831 : Blo 1490065 1490831 := bstep (se 1 (by rfl) ⟨1118123, by rfl⟩ : syracuseStep 1490831 = 2236247) B2236247
theorem B5660563 : Blo 1490065 5660563 := bstep (se 1 (by rfl) ⟨4245422, by rfl⟩ : syracuseStep 5660563 = 8490845) B8490845
theorem B2236331 : Blo 1490065 2236331 := bstep (se 1 (by rfl) ⟨1677248, by rfl⟩ : syracuseStep 2236331 = 3354497) B3354497
theorem B1490875 : Blo 1490065 1490875 := bstep (se 1 (by rfl) ⟨1118156, by rfl⟩ : syracuseStep 1490875 = 2236313) B2236313
theorem B2236361 : Blo 1490065 2236361 := bstep (se 2 (by rfl) ⟨838635, by rfl⟩ : syracuseStep 2236361 = 1677271) B1677271
theorem B8486927 : Blo 1490065 8486927 := bstep (se 1 (by rfl) ⟨6365195, by rfl⟩ : syracuseStep 8486927 = 12730391) B12730391
theorem B9945125 : Blo 1490065 9945125 := bstep (se 4 (by rfl) ⟨932355, by rfl⟩ : syracuseStep 9945125 = 1864711) B1864711
theorem B1490983 : Blo 1490065 1490983 := bstep (se 1 (by rfl) ⟨1118237, by rfl⟩ : syracuseStep 1490983 = 2236475) B2236475
theorem B1491023 : Blo 1490065 1491023 := bstep (se 1 (by rfl) ⟨1118267, by rfl⟩ : syracuseStep 1491023 = 2236535) B2236535
theorem B1491039 : Blo 1490065 1491039 := bstep (se 1 (by rfl) ⟨1118279, by rfl⟩ : syracuseStep 1491039 = 2236559) B2236559
theorem B8495219 : Blo 1490065 8495219 := bstep (se 1 (by rfl) ⟨6371414, by rfl⟩ : syracuseStep 8495219 = 12742829) B12742829
theorem B1491067 : Blo 1490065 1491067 := bstep (se 1 (by rfl) ⟨1118300, by rfl⟩ : syracuseStep 1491067 = 2236601) B2236601
theorem B5030045 : Blo 1490065 5030045 := bstep (se 3 (by rfl) ⟨943133, by rfl⟩ : syracuseStep 5030045 = 1886267) B1886267
theorem B1491119 : Blo 1490065 1491119 := bstep (se 1 (by rfl) ⟨1118339, by rfl⟩ : syracuseStep 1491119 = 2236679) B2236679
theorem B5660867 : Blo 1490065 5660867 := bstep (se 1 (by rfl) ⟨4245650, by rfl⟩ : syracuseStep 5660867 = 8491301) B8491301
theorem B1491143 : Blo 1490065 1491143 := bstep (se 1 (by rfl) ⟨1118357, by rfl⟩ : syracuseStep 1491143 = 2236715) B2236715
theorem B1491163 : Blo 1490065 1491163 := bstep (se 1 (by rfl) ⟨1118372, by rfl⟩ : syracuseStep 1491163 = 2236745) B2236745
theorem B12263653 : Blo 1490065 12263653 := bstep (se 4 (by rfl) ⟨1149717, by rfl⟩ : syracuseStep 12263653 = 2299435) B2299435
theorem B2121977 : Blo 1490065 2121977 := bstep (se 2 (by rfl) ⟨795741, by rfl⟩ : syracuseStep 2121977 = 1591483) B1591483
theorem B8487179 : Blo 1490065 8487179 := bstep (se 1 (by rfl) ⟨6365384, by rfl⟩ : syracuseStep 8487179 = 12730769) B12730769
theorem B4776203 : Blo 1490065 4776203 := bstep (se 1 (by rfl) ⟨3582152, by rfl⟩ : syracuseStep 4776203 = 7164305) B7164305
theorem B1491239 : Blo 1490065 1491239 := bstep (se 1 (by rfl) ⟨1118429, by rfl⟩ : syracuseStep 1491239 = 2236859) B2236859
theorem B7545149 : Blo 1490065 7545149 := bstep (se 3 (by rfl) ⟨1414715, by rfl⟩ : syracuseStep 7545149 = 2829431) B2829431
theorem B1491279 : Blo 1490065 1491279 := bstep (se 1 (by rfl) ⟨1118459, by rfl⟩ : syracuseStep 1491279 = 2236919) B2236919
theorem B1491295 : Blo 1490065 1491295 := bstep (se 1 (by rfl) ⟨1118471, by rfl⟩ : syracuseStep 1491295 = 2236943) B2236943
theorem B1491323 : Blo 1490065 1491323 := bstep (se 1 (by rfl) ⟨1118492, by rfl⟩ : syracuseStep 1491323 = 2236985) B2236985
theorem B2236847 : Blo 1490065 2236847 := bstep (se 1 (by rfl) ⟨1677635, by rfl⟩ : syracuseStep 2236847 = 3355271) B3355271
theorem B1491375 : Blo 1490065 1491375 := bstep (se 1 (by rfl) ⟨1118531, by rfl⟩ : syracuseStep 1491375 = 2237063) B2237063
theorem B2515387 : Blo 1490065 2515387 := bstep (se 1 (by rfl) ⟨1886540, by rfl⟩ : syracuseStep 2515387 = 3773081) B3773081
theorem B1491399 : Blo 1490065 1491399 := bstep (se 1 (by rfl) ⟨1118549, by rfl⟩ : syracuseStep 1491399 = 2237099) B2237099
theorem B1491419 : Blo 1490065 1491419 := bstep (se 1 (by rfl) ⟨1118564, by rfl⟩ : syracuseStep 1491419 = 2237129) B2237129
theorem B24183299 : Blo 1490065 24183299 := bstep (se 1 (by rfl) ⟨18137474, by rfl⟩ : syracuseStep 24183299 = 36274949) B36274949
theorem B2236937 : Blo 1490065 2236937 := bstep (se 2 (by rfl) ⟨838851, by rfl⟩ : syracuseStep 2236937 = 1677703) B1677703
theorem B11477537 : Blo 1490065 11477537 := bstep (se 2 (by rfl) ⟨4304076, by rfl⟩ : syracuseStep 11477537 = 8608153) B8608153
theorem B2515495 : Blo 1490065 2515495 := bstep (se 1 (by rfl) ⟨1886621, by rfl⟩ : syracuseStep 2515495 = 3773243) B3773243
theorem B2236967 : Blo 1490065 2236967 := bstep (se 1 (by rfl) ⟨1677725, by rfl⟩ : syracuseStep 2236967 = 3355451) B3355451
theorem B1491495 : Blo 1490065 1491495 := bstep (se 1 (by rfl) ⟨1118621, by rfl⟩ : syracuseStep 1491495 = 2237243) B2237243
theorem B8495675 : Blo 1490065 8495675 := bstep (se 1 (by rfl) ⟨6371756, by rfl⟩ : syracuseStep 8495675 = 12743513) B12743513
theorem B1491535 : Blo 1490065 1491535 := bstep (se 1 (by rfl) ⟨1118651, by rfl⟩ : syracuseStep 1491535 = 2237303) B2237303
theorem B1491551 : Blo 1490065 1491551 := bstep (se 1 (by rfl) ⟨1118663, by rfl⟩ : syracuseStep 1491551 = 2237327) B2237327
theorem B2237051 : Blo 1490065 2237051 := bstep (se 1 (by rfl) ⟨1677788, by rfl⟩ : syracuseStep 2237051 = 3355577) B3355577
theorem B1491579 : Blo 1490065 1491579 := bstep (se 1 (by rfl) ⟨1118684, by rfl⟩ : syracuseStep 1491579 = 2237369) B2237369
theorem B5661323 : Blo 1490065 5661323 := bstep (se 1 (by rfl) ⟨4245992, by rfl⟩ : syracuseStep 5661323 = 8491985) B8491985
theorem B1491631 : Blo 1490065 1491631 := bstep (se 1 (by rfl) ⟨1118723, by rfl⟩ : syracuseStep 1491631 = 2237447) B2237447
theorem B5030585 : Blo 1490065 5030585 := bstep (se 2 (by rfl) ⟨1886469, by rfl⟩ : syracuseStep 5030585 = 3772939) B3772939
theorem B3580615 : Blo 1490065 3580615 := bstep (se 1 (by rfl) ⟨2685461, by rfl⟩ : syracuseStep 3580615 = 5370923) B5370923
theorem B1491655 : Blo 1490065 1491655 := bstep (se 1 (by rfl) ⟨1118741, by rfl⟩ : syracuseStep 1491655 = 2237483) B2237483
theorem B12092105 : Blo 1490065 12092105 := bstep (se 2 (by rfl) ⟨4534539, by rfl⟩ : syracuseStep 12092105 = 9069079) B9069079
theorem B1491675 : Blo 1490065 1491675 := bstep (se 1 (by rfl) ⟨1118756, by rfl⟩ : syracuseStep 1491675 = 2237513) B2237513
theorem B2237177 : Blo 1490065 2237177 := bstep (se 2 (by rfl) ⟨838941, by rfl⟩ : syracuseStep 2237177 = 1677883) B1677883
theorem B1491751 : Blo 1490065 1491751 := bstep (se 1 (by rfl) ⟨1118813, by rfl⟩ : syracuseStep 1491751 = 2237627) B2237627
theorem B1491791 : Blo 1490065 1491791 := bstep (se 1 (by rfl) ⟨1118843, by rfl⟩ : syracuseStep 1491791 = 2237687) B2237687
theorem B5661535 : Blo 1490065 5661535 := bstep (se 1 (by rfl) ⟨4246151, by rfl⟩ : syracuseStep 5661535 = 8492303) B8492303
theorem B2237279 : Blo 1490065 2237279 := bstep (se 1 (by rfl) ⟨1677959, by rfl⟩ : syracuseStep 2237279 = 3355919) B3355919
theorem B1491807 : Blo 1490065 1491807 := bstep (se 1 (by rfl) ⟨1118855, by rfl⟩ : syracuseStep 1491807 = 2237711) B2237711
theorem B2515819 : Blo 1490065 2515819 := bstep (se 1 (by rfl) ⟨1886864, by rfl⟩ : syracuseStep 2515819 = 3773729) B3773729
theorem B2237291 : Blo 1490065 2237291 := bstep (se 1 (by rfl) ⟨1677968, by rfl⟩ : syracuseStep 2237291 = 3355937) B3355937
theorem B1491835 : Blo 1490065 1491835 := bstep (se 1 (by rfl) ⟨1118876, by rfl⟩ : syracuseStep 1491835 = 2237753) B2237753
theorem B1491887 : Blo 1490065 1491887 := bstep (se 1 (by rfl) ⟨1118915, by rfl⟩ : syracuseStep 1491887 = 2237831) B2237831
theorem B1491911 : Blo 1490065 1491911 := bstep (se 1 (by rfl) ⟨1118933, by rfl⟩ : syracuseStep 1491911 = 2237867) B2237867
theorem B1491931 : Blo 1490065 1491931 := bstep (se 1 (by rfl) ⟨1118948, by rfl⟩ : syracuseStep 1491931 = 2237897) B2237897
theorem B11322341 : Blo 1490065 11322341 := bstep (se 4 (by rfl) ⟨1061469, by rfl⟩ : syracuseStep 11322341 = 2122939) B2122939
theorem B5170177 : Blo 1490065 5170177 := bstep (se 2 (by rfl) ⟨1938816, by rfl⟩ : syracuseStep 5170177 = 3877633) B3877633
theorem B1492007 : Blo 1490065 1492007 := bstep (se 1 (by rfl) ⟨1119005, by rfl⟩ : syracuseStep 1492007 = 2238011) B2238011
theorem B12248113 : Blo 1490065 12248113 := bstep (se 2 (by rfl) ⟨4593042, by rfl⟩ : syracuseStep 12248113 = 9186085) B9186085
theorem B2237519 : Blo 1490065 2237519 := bstep (se 1 (by rfl) ⟨1678139, by rfl⟩ : syracuseStep 2237519 = 3356279) B3356279
theorem B1492047 : Blo 1490065 1492047 := bstep (se 1 (by rfl) ⟨1119035, by rfl⟩ : syracuseStep 1492047 = 2238071) B2238071
theorem B1492063 : Blo 1490065 1492063 := bstep (se 1 (by rfl) ⟨1119047, by rfl⟩ : syracuseStep 1492063 = 2238095) B2238095
theorem B2122951 : Blo 1490065 2122951 := bstep (se 1 (by rfl) ⟨1592213, by rfl⟩ : syracuseStep 2122951 = 3184427) B3184427
theorem B2237639 : Blo 1490065 2237639 := bstep (se 1 (by rfl) ⟨1678229, by rfl⟩ : syracuseStep 2237639 = 3356459) B3356459
theorem B5031179 : Blo 1490065 5031179 := bstep (se 1 (by rfl) ⟨3773384, by rfl⟩ : syracuseStep 5031179 = 7546769) B7546769
theorem B2549065 : Blo 1490065 2549065 := bstep (se 2 (by rfl) ⟨955899, by rfl⟩ : syracuseStep 2549065 = 1911799) B1911799
theorem B2237801 : Blo 1490065 2237801 := bstep (se 2 (by rfl) ⟨839175, by rfl⟩ : syracuseStep 2237801 = 1678351) B1678351
theorem B3581327 : Blo 1490065 3581327 := bstep (se 1 (by rfl) ⟨2685995, by rfl⟩ : syracuseStep 3581327 = 5371991) B5371991
theorem B2237879 : Blo 1490065 2237879 := bstep (se 1 (by rfl) ⟨1678409, by rfl⟩ : syracuseStep 2237879 = 3356819) B3356819
theorem B2237915 : Blo 1490065 2237915 := bstep (se 1 (by rfl) ⟨1678436, by rfl⟩ : syracuseStep 2237915 = 3356873) B3356873
theorem B11478515 : Blo 1490065 11478515 := bstep (se 1 (by rfl) ⟨8608886, by rfl⟩ : syracuseStep 11478515 = 17217773) B17217773
theorem B40797701 : Blo 1490065 40797701 := bstep (se 4 (by rfl) ⟨3824784, by rfl⟩ : syracuseStep 40797701 = 7649569) B7649569
theorem B4138505 : Blo 1490065 4138505 := bstep (se 2 (by rfl) ⟨1551939, by rfl⟩ : syracuseStep 4138505 = 3103879) B3103879
theorem B5031449 : Blo 1490065 5031449 := bstep (se 2 (by rfl) ⟨1886793, by rfl⟩ : syracuseStep 5031449 = 3773587) B3773587
theorem B8488637 : Blo 1490065 8488637 := bstep (se 3 (by rfl) ⟨1591619, by rfl⟩ : syracuseStep 8488637 = 3183239) B3183239
theorem B103294693 : Blo 1490065 103294693 := bstep (se 4 (by rfl) ⟨9683877, by rfl⟩ : syracuseStep 103294693 = 19367755) B19367755
theorem B5662493 : Blo 1490065 5662493 := bstep (se 3 (by rfl) ⟨1061717, by rfl⟩ : syracuseStep 5662493 = 2123435) B2123435
theorem B5662507 : Blo 1490065 5662507 := bstep (se 1 (by rfl) ⟨4246880, by rfl⟩ : syracuseStep 5662507 = 8493761) B8493761
theorem B43599667 : Blo 1490065 43599667 := bstep (se 1 (by rfl) ⟨32699750, by rfl⟩ : syracuseStep 43599667 = 65399501) B65399501
theorem B2516879 : Blo 1490065 2516879 := bstep (se 1 (by rfl) ⟨1887659, by rfl⟩ : syracuseStep 2516879 = 3775319) B3775319
theorem B32237473 : Blo 1490065 32237473 := bstep (se 2 (by rfl) ⟨12089052, by rfl⟩ : syracuseStep 32237473 = 24178105) B24178105
theorem B25487297 : Blo 1490065 25487297 := bstep (se 2 (by rfl) ⟨9557736, by rfl⟩ : syracuseStep 25487297 = 19115473) B19115473
theorem B6367247 : Blo 1490065 6367247 := bstep (se 1 (by rfl) ⟨4775435, by rfl⟩ : syracuseStep 6367247 = 9550871) B9550871
theorem B2517115 : Blo 1490065 2517115 := bstep (se 1 (by rfl) ⟨1887836, by rfl⟩ : syracuseStep 2517115 = 3775673) B3775673
theorem B3352823 : Blo 1490065 3352823 := bstep (se 1 (by rfl) ⟨2514617, by rfl⟩ : syracuseStep 3352823 = 5029235) B5029235
theorem B32229683 : Blo 1490065 32229683 := bstep (se 1 (by rfl) ⟨24172262, by rfl⟩ : syracuseStep 32229683 = 48344525) B48344525
theorem B12740915 : Blo 1490065 12740915 := bstep (se 1 (by rfl) ⟨9555686, by rfl⟩ : syracuseStep 12740915 = 19111373) B19111373
theorem B5736809 : Blo 1490065 5736809 := bstep (se 2 (by rfl) ⟨2151303, by rfl⟩ : syracuseStep 5736809 = 4302607) B4302607
theorem B4778345 : Blo 1490065 4778345 := bstep (se 2 (by rfl) ⟨1791879, by rfl⟩ : syracuseStep 4778345 = 3583759) B3583759
theorem B7653761 : Blo 1490065 7653761 := bstep (se 2 (by rfl) ⟨2870160, by rfl⟩ : syracuseStep 7653761 = 5740321) B5740321
theorem B1886647 : Blo 1490065 1886647 := bstep (se 1 (by rfl) ⟨1414985, by rfl⟩ : syracuseStep 1886647 = 2829971) B2829971
theorem B7547417 : Blo 1490065 7547417 := bstep (se 2 (by rfl) ⟨2830281, by rfl⟩ : syracuseStep 7547417 = 5660563) B5660563
theorem B2828839 : Blo 1490065 2828839 := bstep (se 1 (by rfl) ⟨2121629, by rfl⟩ : syracuseStep 2828839 = 4243259) B4243259
theorem B1591931 : Blo 1490065 1591931 := bstep (se 1 (by rfl) ⟨1193948, by rfl⟩ : syracuseStep 1591931 = 2387897) B2387897
theorem B5032583 : Blo 1490065 5032583 := bstep (se 1 (by rfl) ⟨3774437, by rfl⟩ : syracuseStep 5032583 = 7548875) B7548875
theorem B5032637 : Blo 1490065 5032637 := bstep (se 3 (by rfl) ⟨943619, by rfl⟩ : syracuseStep 5032637 = 1887239) B1887239
theorem B2828999 : Blo 1490065 2828999 := bstep (se 1 (by rfl) ⟨2121749, by rfl⟩ : syracuseStep 2828999 = 4243499) B4243499
theorem B3353417 : Blo 1490065 3353417 := bstep (se 2 (by rfl) ⟨1257531, by rfl⟩ : syracuseStep 3353417 = 2515063) B2515063
theorem B5032799 : Blo 1490065 5032799 := bstep (se 1 (by rfl) ⟨3774599, by rfl⟩ : syracuseStep 5032799 = 7549199) B7549199
theorem B5032961 : Blo 1490065 5032961 := bstep (se 2 (by rfl) ⟨1887360, by rfl⟩ : syracuseStep 5032961 = 3774721) B3774721
theorem B4303891 : Blo 1490065 4303891 := bstep (se 1 (by rfl) ⟨3227918, by rfl⟩ : syracuseStep 4303891 = 6455837) B6455837
theorem B4246607 : Blo 1490065 4246607 := bstep (se 1 (by rfl) ⟨3184955, by rfl⟩ : syracuseStep 4246607 = 6369911) B6369911
theorem B7163075 : Blo 1490065 7163075 := bstep (se 1 (by rfl) ⟨5372306, by rfl⟩ : syracuseStep 7163075 = 10744613) B10744613
theorem B21482765 : Blo 1490065 21482765 := bstep (se 3 (by rfl) ⟨4028018, by rfl⟩ : syracuseStep 21482765 = 8056037) B8056037
theorem B1510751 : Blo 1490065 1510751 := bstep (se 1 (by rfl) ⟨1133063, by rfl⟩ : syracuseStep 1510751 = 2266127) B2266127
theorem B3354209 : Blo 1490065 3354209 := bstep (se 2 (by rfl) ⟨1257828, by rfl⟩ : syracuseStep 3354209 = 2515657) B2515657
theorem B1887943 : Blo 1490065 1887943 := bstep (se 1 (by rfl) ⟨1415957, by rfl⟩ : syracuseStep 1887943 = 2831915) B2831915
theorem B10751737 : Blo 1490065 10751737 := bstep (se 2 (by rfl) ⟨4031901, by rfl⟩ : syracuseStep 10751737 = 8063803) B8063803
theorem B5033771 : Blo 1490065 5033771 := bstep (se 1 (by rfl) ⟨3775328, by rfl⟩ : syracuseStep 5033771 = 7550657) B7550657
theorem B2830153 : Blo 1490065 2830153 := bstep (se 2 (by rfl) ⟨1061307, by rfl⟩ : syracuseStep 2830153 = 2122615) B2122615
theorem B2551657 : Blo 1490065 2551657 := bstep (se 2 (by rfl) ⟨956871, by rfl⟩ : syracuseStep 2551657 = 1913743) B1913743
theorem B11038625 : Blo 1490065 11038625 := bstep (se 2 (by rfl) ⟨4139484, by rfl⟩ : syracuseStep 11038625 = 8278969) B8278969
theorem B3354551 : Blo 1490065 3354551 := bstep (se 1 (by rfl) ⟨2515913, by rfl⟩ : syracuseStep 3354551 = 5031827) B5031827
theorem B1593307 : Blo 1490065 1593307 := bstep (se 1 (by rfl) ⟨1194980, by rfl⟩ : syracuseStep 1593307 = 2389961) B2389961
theorem B9187343 : Blo 1490065 9187343 := bstep (se 1 (by rfl) ⟨6890507, by rfl⟩ : syracuseStep 9187343 = 13781015) B13781015
theorem B5034041 : Blo 1490065 5034041 := bstep (se 2 (by rfl) ⟨1887765, by rfl⟩ : syracuseStep 5034041 = 3775531) B3775531
theorem B6369623 : Blo 1490065 6369623 := bstep (se 1 (by rfl) ⟨4777217, by rfl⟩ : syracuseStep 6369623 = 9554435) B9554435
theorem B3772777 : Blo 1490065 3772777 := bstep (se 2 (by rfl) ⟨1414791, by rfl⟩ : syracuseStep 3772777 = 2829583) B2829583
theorem B5034365 : Blo 1490065 5034365 := bstep (se 3 (by rfl) ⟨943943, by rfl⟩ : syracuseStep 5034365 = 1887887) B1887887
theorem B28668289 : Blo 1490065 28668289 := bstep (se 2 (by rfl) ⟨10750608, by rfl⟩ : syracuseStep 28668289 = 21501217) B21501217
theorem B3355145 : Blo 1490065 3355145 := bstep (se 2 (by rfl) ⟨1258179, by rfl⟩ : syracuseStep 3355145 = 2516359) B2516359
theorem B4248089 : Blo 1490065 4248089 := bstep (se 2 (by rfl) ⟨1593033, by rfl⟩ : syracuseStep 4248089 = 3186067) B3186067
theorem B3584537 : Blo 1490065 3584537 := bstep (se 2 (by rfl) ⟨1344201, by rfl⟩ : syracuseStep 3584537 = 2688403) B2688403
theorem B8491553 : Blo 1490065 8491553 := bstep (se 2 (by rfl) ⟨3184332, by rfl⟩ : syracuseStep 8491553 = 6368665) B6368665
theorem B3773051 : Blo 1490065 3773051 := bstep (se 1 (by rfl) ⟨2829788, by rfl⟩ : syracuseStep 3773051 = 5659577) B5659577
theorem B5034635 : Blo 1490065 5034635 := bstep (se 1 (by rfl) ⟨3775976, by rfl⟩ : syracuseStep 5034635 = 7551953) B7551953
theorem B7647929 : Blo 1490065 7647929 := bstep (se 2 (by rfl) ⟨2867973, by rfl⟩ : syracuseStep 7647929 = 5735947) B5735947
theorem B51680045 : Blo 1490065 51680045 := bstep (se 3 (by rfl) ⟨9690008, by rfl⟩ : syracuseStep 51680045 = 19380017) B19380017
theorem B3355487 : Blo 1490065 3355487 := bstep (se 1 (by rfl) ⟨2516615, by rfl⟩ : syracuseStep 3355487 = 5033231) B5033231
theorem B3355667 : Blo 1490065 3355667 := bstep (se 1 (by rfl) ⟨2516750, by rfl⟩ : syracuseStep 3355667 = 5033501) B5033501
theorem B2421931 : Blo 1490065 2421931 := bstep (se 1 (by rfl) ⟨1816448, by rfl⟩ : syracuseStep 2421931 = 3632897) B3632897
theorem B3356009 : Blo 1490065 3356009 := bstep (se 2 (by rfl) ⟨1258503, by rfl⟩ : syracuseStep 3356009 = 2517007) B2517007
theorem B7550333 : Blo 1490065 7550333 := bstep (se 3 (by rfl) ⟨1415687, by rfl⟩ : syracuseStep 7550333 = 2831375) B2831375
theorem B5035553 : Blo 1490065 5035553 := bstep (se 2 (by rfl) ⟨1888332, by rfl⟩ : syracuseStep 5035553 = 3776665) B3776665
theorem B1676839 : Blo 1490065 1676839 := bstep (se 1 (by rfl) ⟨1257629, by rfl⟩ : syracuseStep 1676839 = 2515259) B2515259
theorem B2389583 : Blo 1490065 2389583 := bstep (se 1 (by rfl) ⟨1792187, by rfl⟩ : syracuseStep 2389583 = 3584375) B3584375
theorem B7648913 : Blo 1490065 7648913 := bstep (se 2 (by rfl) ⟨2868342, by rfl⟩ : syracuseStep 7648913 = 5736685) B5736685
theorem B24188615 : Blo 1490065 24188615 := bstep (se 1 (by rfl) ⟨18141461, by rfl⟩ : syracuseStep 24188615 = 36282923) B36282923
theorem B8492759 : Blo 1490065 8492759 := bstep (se 1 (by rfl) ⟨6369569, by rfl⟩ : syracuseStep 8492759 = 12739139) B12739139
theorem B12089249 : Blo 1490065 12089249 := bstep (se 2 (by rfl) ⟨4533468, by rfl⟩ : syracuseStep 12089249 = 9066937) B9066937
theorem B3356603 : Blo 1490065 3356603 := bstep (se 1 (by rfl) ⟨2517452, by rfl⟩ : syracuseStep 3356603 = 5034905) B5034905
theorem B2832347 : Blo 1490065 2832347 := bstep (se 1 (by rfl) ⟨2124260, by rfl⟩ : syracuseStep 2832347 = 4248521) B4248521
theorem B3356729 : Blo 1490065 3356729 := bstep (se 2 (by rfl) ⟨1258773, by rfl⟩ : syracuseStep 3356729 = 2517547) B2517547
theorem B2832583 : Blo 1490065 2832583 := bstep (se 1 (by rfl) ⟨2124437, by rfl⟩ : syracuseStep 2832583 = 4248875) B4248875
theorem B3225847 : Blo 1490065 3225847 := bstep (se 1 (by rfl) ⟨2419385, by rfl⟩ : syracuseStep 3225847 = 4838771) B4838771
theorem B3774863 : Blo 1490065 3774863 := bstep (se 1 (by rfl) ⟨2831147, by rfl⟩ : syracuseStep 3774863 = 5662295) B5662295
theorem B3357071 : Blo 1490065 3357071 := bstep (se 1 (by rfl) ⟨2517803, by rfl⟩ : syracuseStep 3357071 = 5035607) B5035607
theorem B3021275 : Blo 1490065 3021275 := bstep (se 1 (by rfl) ⟨2265956, by rfl⟩ : syracuseStep 3021275 = 4531913) B4531913
theorem B11631127 : Blo 1490065 11631127 := bstep (se 1 (by rfl) ⟨8723345, by rfl⟩ : syracuseStep 11631127 = 17446691) B17446691
theorem B11328173 : Blo 1490065 11328173 := bstep (se 3 (by rfl) ⟨2124032, by rfl⟩ : syracuseStep 11328173 = 4248065) B4248065
theorem B3775187 : Blo 1490065 3775187 := bstep (se 1 (by rfl) ⟨2831390, by rfl⟩ : syracuseStep 3775187 = 5662781) B5662781
theorem B3447545 : Blo 1490065 3447545 := bstep (se 2 (by rfl) ⟨1292829, by rfl⟩ : syracuseStep 3447545 = 2585659) B2585659
theorem B2235311 : Blo 1490065 2235311 := bstep (se 1 (by rfl) ⟨1676483, by rfl⟩ : syracuseStep 2235311 = 3352967) B3352967
theorem B9558967 : Blo 1490065 9558967 := bstep (se 1 (by rfl) ⟨7169225, by rfl⟩ : syracuseStep 9558967 = 14338451) B14338451
theorem B2235401 : Blo 1490065 2235401 := bstep (se 2 (by rfl) ⟨838275, by rfl⟩ : syracuseStep 2235401 = 1676551) B1676551
theorem B6372371 : Blo 1490065 6372371 := bstep (se 1 (by rfl) ⟨4779278, by rfl⟩ : syracuseStep 6372371 = 9558557) B9558557
theorem B2235431 : Blo 1490065 2235431 := bstep (se 1 (by rfl) ⟨1676573, by rfl⟩ : syracuseStep 2235431 = 3353147) B3353147
theorem B2235515 : Blo 1490065 2235515 := bstep (se 1 (by rfl) ⟨1676636, by rfl⟩ : syracuseStep 2235515 = 3353273) B3353273
theorem B1678459 : Blo 1490065 1678459 := bstep (se 1 (by rfl) ⟨1258844, by rfl⟩ : syracuseStep 1678459 = 2517689) B2517689
theorem B1490095 : Blo 1490065 1490095 := bstep (se 1 (by rfl) ⟨1117571, by rfl⟩ : syracuseStep 1490095 = 2235143) B2235143
theorem B1490119 : Blo 1490065 1490119 := bstep (se 1 (by rfl) ⟨1117589, by rfl⟩ : syracuseStep 1490119 = 2235179) B2235179
theorem B1490139 : Blo 1490065 1490139 := bstep (se 1 (by rfl) ⟨1117604, by rfl⟩ : syracuseStep 1490139 = 2235209) B2235209
theorem B5659895 : Blo 1490065 5659895 := bstep (se 1 (by rfl) ⟨4244921, by rfl⟩ : syracuseStep 5659895 = 8489843) B8489843
theorem B2235641 : Blo 1490065 2235641 := bstep (se 2 (by rfl) ⟨838365, by rfl⟩ : syracuseStep 2235641 = 1676731) B1676731
theorem B10747151 : Blo 1490065 10747151 := bstep (se 1 (by rfl) ⟨8060363, by rfl⟩ : syracuseStep 10747151 = 16120727) B16120727
theorem B1490215 : Blo 1490065 1490215 := bstep (se 1 (by rfl) ⟨1117661, by rfl⟩ : syracuseStep 1490215 = 2235323) B2235323
theorem B5029181 : Blo 1490065 5029181 := bstep (se 3 (by rfl) ⟨942971, by rfl⟩ : syracuseStep 5029181 = 1885943) B1885943
theorem B1490255 : Blo 1490065 1490255 := bstep (se 1 (by rfl) ⟨1117691, by rfl⟩ : syracuseStep 1490255 = 2235383) B2235383
theorem B1490271 : Blo 1490065 1490271 := bstep (se 1 (by rfl) ⟨1117703, by rfl⟩ : syracuseStep 1490271 = 2235407) B2235407
theorem B2235743 : Blo 1490065 2235743 := bstep (se 1 (by rfl) ⟨1676807, by rfl⟩ : syracuseStep 2235743 = 3353615) B3353615
theorem B2235755 : Blo 1490065 2235755 := bstep (se 1 (by rfl) ⟨1676816, by rfl⟩ : syracuseStep 2235755 = 3353633) B3353633
theorem B1490299 : Blo 1490065 1490299 := bstep (se 1 (by rfl) ⟨1117724, by rfl⟩ : syracuseStep 1490299 = 2235449) B2235449
theorem B14335375 : Blo 1490065 14335375 := bstep (se 1 (by rfl) ⟨10751531, by rfl⟩ : syracuseStep 14335375 = 21503063) B21503063
theorem B1490351 : Blo 1490065 1490351 := bstep (se 1 (by rfl) ⟨1117763, by rfl⟩ : syracuseStep 1490351 = 2235527) B2235527
theorem B1490375 : Blo 1490065 1490375 := bstep (se 1 (by rfl) ⟨1117781, by rfl⟩ : syracuseStep 1490375 = 2235563) B2235563
theorem B1490395 : Blo 1490065 1490395 := bstep (se 1 (by rfl) ⟨1117796, by rfl⟩ : syracuseStep 1490395 = 2235593) B2235593
theorem B5373449 : Blo 1490065 5373449 := bstep (se 2 (by rfl) ⟨2015043, by rfl⟩ : syracuseStep 5373449 = 4030087) B4030087
theorem B5103137 : Blo 1490065 5103137 := bstep (se 2 (by rfl) ⟨1913676, by rfl⟩ : syracuseStep 5103137 = 3827353) B3827353
theorem B1490471 : Blo 1490065 1490471 := bstep (se 1 (by rfl) ⟨1117853, by rfl⟩ : syracuseStep 1490471 = 2235707) B2235707
theorem B1490511 : Blo 1490065 1490511 := bstep (se 1 (by rfl) ⟨1117883, by rfl⟩ : syracuseStep 1490511 = 2235767) B2235767
theorem B2235983 : Blo 1490065 2235983 := bstep (se 1 (by rfl) ⟨1676987, by rfl⟩ : syracuseStep 2235983 = 3353975) B3353975
theorem B1490527 : Blo 1490065 1490527 := bstep (se 1 (by rfl) ⟨1117895, by rfl⟩ : syracuseStep 1490527 = 2235791) B2235791
theorem B1490555 : Blo 1490065 1490555 := bstep (se 1 (by rfl) ⟨1117916, by rfl⟩ : syracuseStep 1490555 = 2235833) B2235833
theorem B12738181 : Blo 1490065 12738181 := bstep (se 4 (by rfl) ⟨1194204, by rfl⟩ : syracuseStep 12738181 = 2388409) B2388409
theorem B5742215 : Blo 1490065 5742215 := bstep (se 1 (by rfl) ⟨4306661, by rfl⟩ : syracuseStep 5742215 = 8613323) B8613323
theorem B1490607 : Blo 1490065 1490607 := bstep (se 1 (by rfl) ⟨1117955, by rfl⟩ : syracuseStep 1490607 = 2235911) B2235911
theorem B2236103 : Blo 1490065 2236103 := bstep (se 1 (by rfl) ⟨1677077, by rfl⟩ : syracuseStep 2236103 = 3354155) B3354155
theorem B2514631 : Blo 1490065 2514631 := bstep (se 1 (by rfl) ⟨1885973, by rfl⟩ : syracuseStep 2514631 = 3771947) B3771947
theorem B1490631 : Blo 1490065 1490631 := bstep (se 1 (by rfl) ⟨1117973, by rfl⟩ : syracuseStep 1490631 = 2235947) B2235947
theorem B1490651 : Blo 1490065 1490651 := bstep (se 1 (by rfl) ⟨1117988, by rfl⟩ : syracuseStep 1490651 = 2235977) B2235977
theorem B3186425 : Blo 1490065 3186425 := bstep (se 2 (by rfl) ⟨1194909, by rfl⟩ : syracuseStep 3186425 = 2389819) B2389819
theorem B1490727 : Blo 1490065 1490727 := bstep (se 1 (by rfl) ⟨1118045, by rfl⟩ : syracuseStep 1490727 = 2236091) B2236091
theorem B1490767 : Blo 1490065 1490767 := bstep (se 1 (by rfl) ⟨1118075, by rfl⟩ : syracuseStep 1490767 = 2236151) B2236151
theorem B1490783 : Blo 1490065 1490783 := bstep (se 1 (by rfl) ⟨1118087, by rfl⟩ : syracuseStep 1490783 = 2236175) B2236175
theorem B2514793 : Blo 1490065 2514793 := bstep (se 2 (by rfl) ⟨943047, by rfl⟩ : syracuseStep 2514793 = 1886095) B1886095
theorem B2236265 : Blo 1490065 2236265 := bstep (se 2 (by rfl) ⟨838599, by rfl⟩ : syracuseStep 2236265 = 1677199) B1677199
theorem B1490811 : Blo 1490065 1490811 := bstep (se 1 (by rfl) ⟨1118108, by rfl⟩ : syracuseStep 1490811 = 2236217) B2236217
theorem B3825569 : Blo 1490065 3825569 := bstep (se 2 (by rfl) ⟨1434588, by rfl⟩ : syracuseStep 3825569 = 2869177) B2869177
theorem B1490863 : Blo 1490065 1490863 := bstep (se 1 (by rfl) ⟨1118147, by rfl⟩ : syracuseStep 1490863 = 2236295) B2236295
theorem B2236343 : Blo 1490065 2236343 := bstep (se 1 (by rfl) ⟨1677257, by rfl⟩ : syracuseStep 2236343 = 3354515) B3354515
theorem B1490887 : Blo 1490065 1490887 := bstep (se 1 (by rfl) ⟨1118165, by rfl⟩ : syracuseStep 1490887 = 2236331) B2236331
theorem B1490907 : Blo 1490065 1490907 := bstep (se 1 (by rfl) ⟨1118180, by rfl⟩ : syracuseStep 1490907 = 2236361) B2236361
theorem B2236379 : Blo 1490065 2236379 := bstep (se 1 (by rfl) ⟨1677284, by rfl⟩ : syracuseStep 2236379 = 3354569) B3354569
theorem B27574277 : Blo 1490065 27574277 := bstep (se 4 (by rfl) ⟨2585088, by rfl⟩ : syracuseStep 27574277 = 5170177) B5170177
theorem B5030099 : Blo 1490065 5030099 := bstep (se 1 (by rfl) ⟨3772574, by rfl⟩ : syracuseStep 5030099 = 7545149) B7545149
theorem B3776777 : Blo 1490065 3776777 := bstep (se 2 (by rfl) ⟨1416291, by rfl⟩ : syracuseStep 3776777 = 2832583) B2832583
theorem B1491231 : Blo 1490065 1491231 := bstep (se 1 (by rfl) ⟨1118423, by rfl⟩ : syracuseStep 1491231 = 2236847) B2236847
theorem B4301129 : Blo 1490065 4301129 := bstep (se 2 (by rfl) ⟨1612923, by rfl⟩ : syracuseStep 4301129 = 3225847) B3225847
theorem B16122199 : Blo 1490065 16122199 := bstep (se 1 (by rfl) ⟨12091649, by rfl⟩ : syracuseStep 16122199 = 24183299) B24183299
theorem B2236763 : Blo 1490065 2236763 := bstep (se 1 (by rfl) ⟨1677572, by rfl⟩ : syracuseStep 2236763 = 3355145) B3355145
theorem B1491291 : Blo 1490065 1491291 := bstep (se 1 (by rfl) ⟨1118468, by rfl⟩ : syracuseStep 1491291 = 2236937) B2236937
theorem B5661035 : Blo 1490065 5661035 := bstep (se 1 (by rfl) ⟨4245776, by rfl⟩ : syracuseStep 5661035 = 8491553) B8491553
theorem B7651691 : Blo 1490065 7651691 := bstep (se 1 (by rfl) ⟨5738768, by rfl⟩ : syracuseStep 7651691 = 11477537) B11477537
theorem B1491311 : Blo 1490065 1491311 := bstep (se 1 (by rfl) ⟨1118483, by rfl⟩ : syracuseStep 1491311 = 2236967) B2236967
theorem B2515367 : Blo 1490065 2515367 := bstep (se 1 (by rfl) ⟨1886525, by rfl⟩ : syracuseStep 2515367 = 3773051) B3773051
theorem B1491367 : Blo 1490065 1491367 := bstep (se 1 (by rfl) ⟨1118525, by rfl⟩ : syracuseStep 1491367 = 2237051) B2237051
theorem B8061403 : Blo 1490065 8061403 := bstep (se 1 (by rfl) ⟨6046052, by rfl⟩ : syracuseStep 8061403 = 12092105) B12092105
theorem B5030369 : Blo 1490065 5030369 := bstep (se 2 (by rfl) ⟨1886388, by rfl⟩ : syracuseStep 5030369 = 3772777) B3772777
theorem B1491451 : Blo 1490065 1491451 := bstep (se 1 (by rfl) ⟨1118588, by rfl⟩ : syracuseStep 1491451 = 2237177) B2237177
theorem B38224385 : Blo 1490065 38224385 := bstep (se 2 (by rfl) ⟨14334144, by rfl⟩ : syracuseStep 38224385 = 28668289) B28668289
theorem B2236991 : Blo 1490065 2236991 := bstep (se 1 (by rfl) ⟨1677743, by rfl⟩ : syracuseStep 2236991 = 3355487) B3355487
theorem B1491519 : Blo 1490065 1491519 := bstep (se 1 (by rfl) ⟨1118639, by rfl⟩ : syracuseStep 1491519 = 2237279) B2237279
theorem B1491527 : Blo 1490065 1491527 := bstep (se 1 (by rfl) ⟨1118645, by rfl⟩ : syracuseStep 1491527 = 2237291) B2237291
theorem B2515529 : Blo 1490065 2515529 := bstep (se 2 (by rfl) ⟨943323, by rfl⟩ : syracuseStep 2515529 = 1886647) B1886647
theorem B2237111 : Blo 1490065 2237111 := bstep (se 1 (by rfl) ⟨1677833, by rfl⟩ : syracuseStep 2237111 = 3355667) B3355667
theorem B15508169 : Blo 1490065 15508169 := bstep (se 2 (by rfl) ⟨5815563, by rfl⟩ : syracuseStep 15508169 = 11631127) B11631127
theorem B1491679 : Blo 1490065 1491679 := bstep (se 1 (by rfl) ⟨1118759, by rfl⟩ : syracuseStep 1491679 = 2237519) B2237519
theorem B1491759 : Blo 1490065 1491759 := bstep (se 1 (by rfl) ⟨1118819, by rfl⟩ : syracuseStep 1491759 = 2237639) B2237639
theorem B2237339 : Blo 1490065 2237339 := bstep (se 1 (by rfl) ⟨1678004, by rfl⟩ : syracuseStep 2237339 = 3356009) B3356009
theorem B1491867 : Blo 1490065 1491867 := bstep (se 1 (by rfl) ⟨1118900, by rfl⟩ : syracuseStep 1491867 = 2237801) B2237801
theorem B1491919 : Blo 1490065 1491919 := bstep (se 1 (by rfl) ⟨1118939, by rfl⟩ : syracuseStep 1491919 = 2237879) B2237879
theorem B1491943 : Blo 1490065 1491943 := bstep (se 1 (by rfl) ⟨1118957, by rfl⟩ : syracuseStep 1491943 = 2237915) B2237915
theorem B27198467 : Blo 1490065 27198467 := bstep (se 1 (by rfl) ⟨20398850, by rfl⟩ : syracuseStep 27198467 = 40797701) B40797701
theorem B5661839 : Blo 1490065 5661839 := bstep (se 1 (by rfl) ⟨4246379, by rfl⟩ : syracuseStep 5661839 = 8492759) B8492759
theorem B65406149 : Blo 1490065 65406149 := bstep (se 4 (by rfl) ⟨6131826, by rfl⟩ : syracuseStep 65406149 = 12263653) B12263653
theorem B2237735 : Blo 1490065 2237735 := bstep (se 1 (by rfl) ⟨1678301, by rfl⟩ : syracuseStep 2237735 = 3356603) B3356603
theorem B16991531 : Blo 1490065 16991531 := bstep (se 1 (by rfl) ⟨12743648, by rfl⟩ : syracuseStep 16991531 = 25487297) B25487297
theorem B4244831 : Blo 1490065 4244831 := bstep (se 1 (by rfl) ⟨3183623, by rfl⟩ : syracuseStep 4244831 = 6367247) B6367247
theorem B2237819 : Blo 1490065 2237819 := bstep (se 1 (by rfl) ⟨1678364, by rfl⟩ : syracuseStep 2237819 = 3356729) B3356729
theorem B2237945 : Blo 1490065 2237945 := bstep (se 2 (by rfl) ⟨839229, by rfl⟩ : syracuseStep 2237945 = 1678459) B1678459
theorem B3229241 : Blo 1490065 3229241 := bstep (se 2 (by rfl) ⟨1210965, by rfl⟩ : syracuseStep 3229241 = 2421931) B2421931
theorem B2516575 : Blo 1490065 2516575 := bstep (se 1 (by rfl) ⟨1887431, by rfl⟩ : syracuseStep 2516575 = 3774863) B3774863
theorem B2238047 : Blo 1490065 2238047 := bstep (se 1 (by rfl) ⟨1678535, by rfl⟩ : syracuseStep 2238047 = 3357071) B3357071
theorem B4245149 : Blo 1490065 4245149 := bstep (se 3 (by rfl) ⟨795965, by rfl⟩ : syracuseStep 4245149 = 1591931) B1591931
theorem B5031611 : Blo 1490065 5031611 := bstep (se 1 (by rfl) ⟨3773708, by rfl⟩ : syracuseStep 5031611 = 7547417) B7547417
theorem B1885999 : Blo 1490065 1885999 := bstep (se 1 (by rfl) ⟨1414499, by rfl⟩ : syracuseStep 1885999 = 2828999) B2828999
theorem B2516791 : Blo 1490065 2516791 := bstep (se 1 (by rfl) ⟨1887593, by rfl⟩ : syracuseStep 2516791 = 3775187) B3775187
theorem B19113833 : Blo 1490065 19113833 := bstep (se 2 (by rfl) ⟨7167687, by rfl⟩ : syracuseStep 19113833 = 14335375) B14335375
theorem B8497133 : Blo 1490065 8497133 := bstep (se 3 (by rfl) ⟨1593212, by rfl⟩ : syracuseStep 8497133 = 3186425) B3186425
theorem B16984241 : Blo 1490065 16984241 := bstep (se 2 (by rfl) ⟨6369090, by rfl⟩ : syracuseStep 16984241 = 12738181) B12738181
theorem B14321843 : Blo 1490065 14321843 := bstep (se 1 (by rfl) ⟨10741382, by rfl⟩ : syracuseStep 14321843 = 21482765) B21482765
theorem B3352787 : Blo 1490065 3352787 := bstep (se 1 (by rfl) ⟨2514590, by rfl⟩ : syracuseStep 3352787 = 5029181) B5029181
theorem B3352841 : Blo 1490065 3352841 := bstep (se 2 (by rfl) ⟨1257315, by rfl⟩ : syracuseStep 3352841 = 2514631) B2514631
theorem B2517257 : Blo 1490065 2517257 := bstep (se 2 (by rfl) ⟨943971, by rfl⟩ : syracuseStep 2517257 = 1887943) B1887943
theorem B137726257 : Blo 1490065 137726257 := bstep (se 2 (by rfl) ⟨51647346, by rfl⟩ : syracuseStep 137726257 = 103294693) B103294693
theorem B3582299 : Blo 1490065 3582299 := bstep (se 1 (by rfl) ⟨2686724, by rfl⟩ : syracuseStep 3582299 = 5373449) B5373449
theorem B3402091 : Blo 1490065 3402091 := bstep (se 1 (by rfl) ⟨2551568, by rfl⟩ : syracuseStep 3402091 = 5103137) B5103137
theorem B58132889 : Blo 1490065 58132889 := bstep (se 2 (by rfl) ⟨21799833, by rfl⟩ : syracuseStep 58132889 = 43599667) B43599667
theorem B3828143 : Blo 1490065 3828143 := bstep (se 1 (by rfl) ⟨2871107, by rfl⟩ : syracuseStep 3828143 = 5742215) B5742215
theorem B3353057 : Blo 1490065 3353057 := bstep (se 2 (by rfl) ⟨1257396, by rfl⟩ : syracuseStep 3353057 = 2514793) B2514793
theorem B3402209 : Blo 1490065 3402209 := bstep (se 2 (by rfl) ⟨1275828, by rfl⟩ : syracuseStep 3402209 = 2551657) B2551657
theorem B7359083 : Blo 1490065 7359083 := bstep (se 1 (by rfl) ⟨5519312, by rfl⟩ : syracuseStep 7359083 = 11038625) B11038625
theorem B2550379 : Blo 1490065 2550379 := bstep (se 1 (by rfl) ⟨1912784, by rfl⟩ : syracuseStep 2550379 = 3825569) B3825569
theorem B2124409 : Blo 1490065 2124409 := bstep (se 2 (by rfl) ⟨796653, by rfl⟩ : syracuseStep 2124409 = 1593307) B1593307
theorem B6630083 : Blo 1490065 6630083 := bstep (se 1 (by rfl) ⟨4972562, by rfl⟩ : syracuseStep 6630083 = 9945125) B9945125
theorem B16992989 : Blo 1490065 16992989 := bstep (se 3 (by rfl) ⟨3186185, by rfl⟩ : syracuseStep 16992989 = 6372371) B6372371
theorem B5663479 : Blo 1490065 5663479 := bstep (se 1 (by rfl) ⟨4247609, by rfl⟩ : syracuseStep 5663479 = 8495219) B8495219
theorem B3353363 : Blo 1490065 3353363 := bstep (se 1 (by rfl) ⟨2515022, by rfl⟩ : syracuseStep 3353363 = 5030045) B5030045
theorem B11324285 : Blo 1490065 11324285 := bstep (se 3 (by rfl) ⟨2123303, by rfl⟩ : syracuseStep 11324285 = 4246607) B4246607
theorem B4246415 : Blo 1490065 4246415 := bstep (se 1 (by rfl) ⟨3184811, by rfl⟩ : syracuseStep 4246415 = 6369623) B6369623
theorem B5663783 : Blo 1490065 5663783 := bstep (se 1 (by rfl) ⟨4247837, by rfl⟩ : syracuseStep 5663783 = 8495675) B8495675
theorem B5098619 : Blo 1490065 5098619 := bstep (se 1 (by rfl) ⟨3823964, by rfl⟩ : syracuseStep 5098619 = 7647929) B7647929
theorem B3353723 : Blo 1490065 3353723 := bstep (se 1 (by rfl) ⟨2515292, by rfl⟩ : syracuseStep 3353723 = 5030585) B5030585
theorem B3353849 : Blo 1490065 3353849 := bstep (se 2 (by rfl) ⟨1257693, by rfl⟩ : syracuseStep 3353849 = 2515387) B2515387
theorem B7548227 : Blo 1490065 7548227 := bstep (se 1 (by rfl) ⟨5661170, by rfl⟩ : syracuseStep 7548227 = 11322341) B11322341
theorem B3771785 : Blo 1490065 3771785 := bstep (se 2 (by rfl) ⟨1414419, by rfl⟩ : syracuseStep 3771785 = 2828839) B2828839
theorem B3353993 : Blo 1490065 3353993 := bstep (se 2 (by rfl) ⟨1257747, by rfl⟩ : syracuseStep 3353993 = 2515495) B2515495
theorem B3354119 : Blo 1490065 3354119 := bstep (se 1 (by rfl) ⟨2515589, by rfl⟩ : syracuseStep 3354119 = 5031179) B5031179
theorem B5033555 : Blo 1490065 5033555 := bstep (se 1 (by rfl) ⟨3775166, by rfl⟩ : syracuseStep 5033555 = 7550333) B7550333
theorem B2387551 : Blo 1490065 2387551 := bstep (se 1 (by rfl) ⟨1790663, by rfl⟩ : syracuseStep 2387551 = 3581327) B3581327
theorem B3354299 : Blo 1490065 3354299 := bstep (se 1 (by rfl) ⟨2515724, by rfl⟩ : syracuseStep 3354299 = 5031449) B5031449
theorem B1593055 : Blo 1490065 1593055 := bstep (se 1 (by rfl) ⟨1194791, by rfl⟩ : syracuseStep 1593055 = 2389583) B2389583
theorem B5099275 : Blo 1490065 5099275 := bstep (se 1 (by rfl) ⟨3824456, by rfl⟩ : syracuseStep 5099275 = 7648913) B7648913
theorem B7548713 : Blo 1490065 7548713 := bstep (se 2 (by rfl) ⟨2830767, by rfl⟩ : syracuseStep 7548713 = 5661535) B5661535
theorem B16125743 : Blo 1490065 16125743 := bstep (se 1 (by rfl) ⟨12094307, by rfl⟩ : syracuseStep 16125743 = 24188615) B24188615
theorem B3354425 : Blo 1490065 3354425 := bstep (se 2 (by rfl) ⟨1257909, by rfl⟩ : syracuseStep 3354425 = 2515819) B2515819
theorem B30609373 : Blo 1490065 30609373 := bstep (se 3 (by rfl) ⟨5739257, by rfl⟩ : syracuseStep 30609373 = 11478515) B11478515
theorem B5738521 : Blo 1490065 5738521 := bstep (se 2 (by rfl) ⟨2151945, by rfl⟩ : syracuseStep 5738521 = 4303891) B4303891
theorem B16330817 : Blo 1490065 16330817 := bstep (se 2 (by rfl) ⟨6124056, by rfl⟩ : syracuseStep 16330817 = 12248113) B12248113
theorem B2830601 : Blo 1490065 2830601 := bstep (se 2 (by rfl) ⟨1061475, by rfl⟩ : syracuseStep 2830601 = 2122951) B2122951
theorem B3355055 : Blo 1490065 3355055 := bstep (se 1 (by rfl) ⟨2516291, by rfl⟩ : syracuseStep 3355055 = 5032583) B5032583
theorem B3355091 : Blo 1490065 3355091 := bstep (se 1 (by rfl) ⟨2516318, by rfl⟩ : syracuseStep 3355091 = 5032637) B5032637
theorem B3355199 : Blo 1490065 3355199 := bstep (se 1 (by rfl) ⟨2516399, by rfl⟩ : syracuseStep 3355199 = 5032799) B5032799
theorem B3355307 : Blo 1490065 3355307 := bstep (se 1 (by rfl) ⟨2516480, by rfl⟩ : syracuseStep 3355307 = 5032961) B5032961
theorem B3773263 : Blo 1490065 3773263 := bstep (se 1 (by rfl) ⟨2829947, by rfl⟩ : syracuseStep 3773263 = 5659895) B5659895
theorem B7164767 : Blo 1490065 7164767 := bstep (se 1 (by rfl) ⟨5373575, by rfl⟩ : syracuseStep 7164767 = 10747151) B10747151
theorem B7550009 : Blo 1490065 7550009 := bstep (se 2 (by rfl) ⟨2831253, by rfl⟩ : syracuseStep 7550009 = 5662507) B5662507
theorem B3773537 : Blo 1490065 3773537 := bstep (se 2 (by rfl) ⟨1415076, by rfl⟩ : syracuseStep 3773537 = 2830153) B2830153
theorem B3355847 : Blo 1490065 3355847 := bstep (se 1 (by rfl) ⟨2516885, by rfl⟩ : syracuseStep 3355847 = 5033771) B5033771
theorem B5657951 : Blo 1490065 5657951 := bstep (se 1 (by rfl) ⟨4243463, by rfl⟩ : syracuseStep 5657951 = 8486927) B8486927
theorem B6124895 : Blo 1490065 6124895 := bstep (se 1 (by rfl) ⟨4593671, by rfl⟩ : syracuseStep 6124895 = 9187343) B9187343
theorem B3356027 : Blo 1490065 3356027 := bstep (se 1 (by rfl) ⟨2517020, by rfl⟩ : syracuseStep 3356027 = 5034041) B5034041
theorem B3773911 : Blo 1490065 3773911 := bstep (se 1 (by rfl) ⟨2830433, by rfl⟩ : syracuseStep 3773911 = 5660867) B5660867
theorem B3356153 : Blo 1490065 3356153 := bstep (se 2 (by rfl) ⟨1258557, by rfl⟩ : syracuseStep 3356153 = 2517115) B2517115
theorem B5658119 : Blo 1490065 5658119 := bstep (se 1 (by rfl) ⟨4243589, by rfl⟩ : syracuseStep 5658119 = 8487179) B8487179
theorem B3356243 : Blo 1490065 3356243 := bstep (se 1 (by rfl) ⟨2517182, by rfl⟩ : syracuseStep 3356243 = 5034365) B5034365
theorem B2832059 : Blo 1490065 2832059 := bstep (se 1 (by rfl) ⟨2124044, by rfl⟩ : syracuseStep 2832059 = 4248089) B4248089
theorem B2389691 : Blo 1490065 2389691 := bstep (se 1 (by rfl) ⟨1792268, by rfl⟩ : syracuseStep 2389691 = 3584537) B3584537
theorem B3774215 : Blo 1490065 3774215 := bstep (se 1 (by rfl) ⟨2830661, by rfl⟩ : syracuseStep 3774215 = 5661323) B5661323
theorem B3356423 : Blo 1490065 3356423 := bstep (se 1 (by rfl) ⟨2517317, by rfl⟩ : syracuseStep 3356423 = 5034635) B5034635
theorem B34453363 : Blo 1490065 34453363 := bstep (se 1 (by rfl) ⟨25840022, by rfl⟩ : syracuseStep 34453363 = 51680045) B51680045
theorem B5658605 : Blo 1490065 5658605 := bstep (se 3 (by rfl) ⟨1060988, by rfl⟩ : syracuseStep 5658605 = 2121977) B2121977
theorem B12736541 : Blo 1490065 12736541 := bstep (se 3 (by rfl) ⟨2388101, by rfl⟩ : syracuseStep 12736541 = 4776203) B4776203
theorem B4028669 : Blo 1490065 4028669 := bstep (se 3 (by rfl) ⟨755375, by rfl⟩ : syracuseStep 4028669 = 1510751) B1510751
theorem B4774153 : Blo 1490065 4774153 := bstep (se 2 (by rfl) ⟨1790307, by rfl⟩ : syracuseStep 4774153 = 3580615) B3580615
theorem B2759003 : Blo 1490065 2759003 := bstep (se 1 (by rfl) ⟨2069252, by rfl⟩ : syracuseStep 2759003 = 4138505) B4138505
theorem B3357035 : Blo 1490065 3357035 := bstep (se 1 (by rfl) ⟨2517776, by rfl⟩ : syracuseStep 3357035 = 5035553) B5035553
theorem B5659091 : Blo 1490065 5659091 := bstep (se 1 (by rfl) ⟨4244318, by rfl⟩ : syracuseStep 5659091 = 8488637) B8488637
theorem B3774995 : Blo 1490065 3774995 := bstep (se 1 (by rfl) ⟨2831246, by rfl⟩ : syracuseStep 3774995 = 5662493) B5662493
theorem B12745289 : Blo 1490065 12745289 := bstep (se 2 (by rfl) ⟨4779483, by rfl⟩ : syracuseStep 12745289 = 9558967) B9558967
theorem B1677919 : Blo 1490065 1677919 := bstep (se 1 (by rfl) ⟨1258439, by rfl⟩ : syracuseStep 1677919 = 2516879) B2516879
theorem B8059499 : Blo 1490065 8059499 := bstep (se 1 (by rfl) ⟨6044624, by rfl⟩ : syracuseStep 8059499 = 12089249) B12089249
theorem B2235215 : Blo 1490065 2235215 := bstep (se 1 (by rfl) ⟨1676411, by rfl⟩ : syracuseStep 2235215 = 3352823) B3352823
theorem B21486455 : Blo 1490065 21486455 := bstep (se 1 (by rfl) ⟨16114841, by rfl⟩ : syracuseStep 21486455 = 32229683) B32229683
theorem B8493943 : Blo 1490065 8493943 := bstep (se 1 (by rfl) ⟨6370457, by rfl⟩ : syracuseStep 8493943 = 12740915) B12740915
theorem B3824539 : Blo 1490065 3824539 := bstep (se 1 (by rfl) ⟨2868404, by rfl⟩ : syracuseStep 3824539 = 5736809) B5736809
theorem B3185563 : Blo 1490065 3185563 := bstep (se 1 (by rfl) ⟨2389172, by rfl⟩ : syracuseStep 3185563 = 4778345) B4778345
theorem B5102507 : Blo 1490065 5102507 := bstep (se 1 (by rfl) ⟨3826880, by rfl⟩ : syracuseStep 5102507 = 7653761) B7653761
theorem B2014183 : Blo 1490065 2014183 := bstep (se 1 (by rfl) ⟨1510637, by rfl⟩ : syracuseStep 2014183 = 3021275) B3021275
theorem B3398753 : Blo 1490065 3398753 := bstep (se 2 (by rfl) ⟨1274532, by rfl⟩ : syracuseStep 3398753 = 2549065) B2549065
theorem B7552115 : Blo 1490065 7552115 := bstep (se 1 (by rfl) ⟨5664086, by rfl⟩ : syracuseStep 7552115 = 11328173) B11328173
theorem B2235611 : Blo 1490065 2235611 := bstep (se 1 (by rfl) ⟨1676708, by rfl⟩ : syracuseStep 2235611 = 3353417) B3353417
theorem B1490207 : Blo 1490065 1490207 := bstep (se 1 (by rfl) ⟨1117655, by rfl⟩ : syracuseStep 1490207 = 2235311) B2235311
theorem B1490267 : Blo 1490065 1490267 := bstep (se 1 (by rfl) ⟨1117700, by rfl⟩ : syracuseStep 1490267 = 2235401) B2235401
theorem B1490287 : Blo 1490065 1490287 := bstep (se 1 (by rfl) ⟨1117715, by rfl⟩ : syracuseStep 1490287 = 2235431) B2235431
theorem B2235785 : Blo 1490065 2235785 := bstep (se 2 (by rfl) ⟨838419, by rfl⟩ : syracuseStep 2235785 = 1676839) B1676839
theorem B1490343 : Blo 1490065 1490343 := bstep (se 1 (by rfl) ⟨1117757, by rfl⟩ : syracuseStep 1490343 = 2235515) B2235515
theorem B4775383 : Blo 1490065 4775383 := bstep (se 1 (by rfl) ⟨3581537, by rfl⟩ : syracuseStep 4775383 = 7163075) B7163075
theorem B1490427 : Blo 1490065 1490427 := bstep (se 1 (by rfl) ⟨1117820, by rfl⟩ : syracuseStep 1490427 = 2235641) B2235641
theorem B1490495 : Blo 1490065 1490495 := bstep (se 1 (by rfl) ⟨1117871, by rfl⟩ : syracuseStep 1490495 = 2235743) B2235743
theorem B1490503 : Blo 1490065 1490503 := bstep (se 1 (by rfl) ⟨1117877, by rfl⟩ : syracuseStep 1490503 = 2235755) B2235755
theorem B14335649 : Blo 1490065 14335649 := bstep (se 2 (by rfl) ⟨5375868, by rfl⟩ : syracuseStep 14335649 = 10751737) B10751737
theorem B1490655 : Blo 1490065 1490655 := bstep (se 1 (by rfl) ⟨1117991, by rfl⟩ : syracuseStep 1490655 = 2235983) B2235983
theorem B2236139 : Blo 1490065 2236139 := bstep (se 1 (by rfl) ⟨1677104, by rfl⟩ : syracuseStep 2236139 = 3354209) B3354209
theorem B1490735 : Blo 1490065 1490735 := bstep (se 1 (by rfl) ⟨1118051, by rfl⟩ : syracuseStep 1490735 = 2236103) B2236103
theorem B42983297 : Blo 1490065 42983297 := bstep (se 2 (by rfl) ⟨16118736, by rfl⟩ : syracuseStep 42983297 = 32237473) B32237473
theorem B1490843 : Blo 1490065 1490843 := bstep (se 1 (by rfl) ⟨1118132, by rfl⟩ : syracuseStep 1490843 = 2236265) B2236265
theorem B7552925 : Blo 1490065 7552925 := bstep (se 3 (by rfl) ⟨1416173, by rfl⟩ : syracuseStep 7552925 = 2832347) B2832347
theorem B36773813 : Blo 1490065 36773813 := bstep (se 5 (by rfl) ⟨1723772, by rfl⟩ : syracuseStep 36773813 = 3447545) B3447545
theorem B1490895 : Blo 1490065 1490895 := bstep (se 1 (by rfl) ⟨1118171, by rfl⟩ : syracuseStep 1490895 = 2236343) B2236343
theorem B2236367 : Blo 1490065 2236367 := bstep (se 1 (by rfl) ⟨1677275, by rfl⟩ : syracuseStep 2236367 = 3354551) B3354551
theorem B1490919 : Blo 1490065 1490919 := bstep (se 1 (by rfl) ⟨1118189, by rfl⟩ : syracuseStep 1490919 = 2236379) B2236379
theorem B73531405 : Blo 1490065 73531405 := bstep (se 3 (by rfl) ⟨13787138, by rfl⟩ : syracuseStep 73531405 = 27574277) B27574277
theorem B7651361 : Blo 1490065 7651361 := bstep (se 2 (by rfl) ⟨2869260, by rfl⟩ : syracuseStep 7651361 = 5738521) B5738521
theorem B10887211 : Blo 1490065 10887211 := bstep (se 1 (by rfl) ⟨8165408, by rfl⟩ : syracuseStep 10887211 = 16330817) B16330817
theorem B2867419 : Blo 1490065 2867419 := bstep (se 1 (by rfl) ⟨2150564, by rfl⟩ : syracuseStep 2867419 = 4301129) B4301129
theorem B1491175 : Blo 1490065 1491175 := bstep (se 1 (by rfl) ⟨1118381, by rfl⟩ : syracuseStep 1491175 = 2236763) B2236763
theorem B2236703 : Blo 1490065 2236703 := bstep (se 1 (by rfl) ⟨1677527, by rfl⟩ : syracuseStep 2236703 = 3355055) B3355055
theorem B2236727 : Blo 1490065 2236727 := bstep (se 1 (by rfl) ⟨1677545, by rfl⟩ : syracuseStep 2236727 = 3355091) B3355091
theorem B6365537 : Blo 1490065 6365537 := bstep (se 2 (by rfl) ⟨2387076, by rfl⟩ : syracuseStep 6365537 = 4774153) B4774153
theorem B2236799 : Blo 1490065 2236799 := bstep (se 1 (by rfl) ⟨1677599, by rfl⟩ : syracuseStep 2236799 = 3355199) B3355199
theorem B1491327 : Blo 1490065 1491327 := bstep (se 1 (by rfl) ⟨1118495, by rfl⟩ : syracuseStep 1491327 = 2236991) B2236991
theorem B2236871 : Blo 1490065 2236871 := bstep (se 1 (by rfl) ⟨1677653, by rfl⟩ : syracuseStep 2236871 = 3355307) B3355307
theorem B21496265 : Blo 1490065 21496265 := bstep (se 2 (by rfl) ⟨8061099, by rfl⟩ : syracuseStep 21496265 = 16122199) B16122199
theorem B1491407 : Blo 1490065 1491407 := bstep (se 1 (by rfl) ⟨1118555, by rfl⟩ : syracuseStep 1491407 = 2237111) B2237111
theorem B10338779 : Blo 1490065 10338779 := bstep (se 1 (by rfl) ⟨7754084, by rfl⟩ : syracuseStep 10338779 = 15508169) B15508169
theorem B4776511 : Blo 1490065 4776511 := bstep (se 1 (by rfl) ⟨3582383, by rfl⟩ : syracuseStep 4776511 = 7164767) B7164767
theorem B1491559 : Blo 1490065 1491559 := bstep (se 1 (by rfl) ⟨1118669, by rfl⟩ : syracuseStep 1491559 = 2237339) B2237339
theorem B10748537 : Blo 1490065 10748537 := bstep (se 2 (by rfl) ⟨4030701, by rfl⟩ : syracuseStep 10748537 = 8061403) B8061403
theorem B2515691 : Blo 1490065 2515691 := bstep (se 1 (by rfl) ⟨1886768, by rfl⟩ : syracuseStep 2515691 = 3773537) B3773537
theorem B2237225 : Blo 1490065 2237225 := bstep (se 2 (by rfl) ⟨838959, by rfl⟩ : syracuseStep 2237225 = 1677919) B1677919
theorem B2237231 : Blo 1490065 2237231 := bstep (se 1 (by rfl) ⟨1677923, by rfl⟩ : syracuseStep 2237231 = 3355847) B3355847
theorem B3400505 : Blo 1490065 3400505 := bstep (se 2 (by rfl) ⟨1275189, by rfl⟩ : syracuseStep 3400505 = 2550379) B2550379
theorem B1491823 : Blo 1490065 1491823 := bstep (se 1 (by rfl) ⟨1118867, by rfl⟩ : syracuseStep 1491823 = 2237735) B2237735
theorem B2237351 : Blo 1490065 2237351 := bstep (se 1 (by rfl) ⟨1678013, by rfl⟩ : syracuseStep 2237351 = 3356027) B3356027
theorem B1491879 : Blo 1490065 1491879 := bstep (se 1 (by rfl) ⟨1118909, by rfl⟩ : syracuseStep 1491879 = 2237819) B2237819
theorem B2237435 : Blo 1490065 2237435 := bstep (se 1 (by rfl) ⟨1678076, by rfl⟩ : syracuseStep 2237435 = 3356153) B3356153
theorem B1491963 : Blo 1490065 1491963 := bstep (se 1 (by rfl) ⟨1118972, by rfl⟩ : syracuseStep 1491963 = 2237945) B2237945
theorem B2237495 : Blo 1490065 2237495 := bstep (se 1 (by rfl) ⟨1678121, by rfl⟩ : syracuseStep 2237495 = 3356243) B3356243
theorem B1492031 : Blo 1490065 1492031 := bstep (se 1 (by rfl) ⟨1119023, by rfl⟩ : syracuseStep 1492031 = 2238047) B2238047
theorem B5031017 : Blo 1490065 5031017 := bstep (se 2 (by rfl) ⟨1886631, by rfl⟩ : syracuseStep 5031017 = 3773263) B3773263
theorem B2516143 : Blo 1490065 2516143 := bstep (se 1 (by rfl) ⟨1887107, by rfl⟩ : syracuseStep 2516143 = 3774215) B3774215
theorem B2237615 : Blo 1490065 2237615 := bstep (se 1 (by rfl) ⟨1678211, by rfl⟩ : syracuseStep 2237615 = 3356423) B3356423
theorem B11322827 : Blo 1490065 11322827 := bstep (se 1 (by rfl) ⟨8492120, by rfl⟩ : syracuseStep 11322827 = 16984241) B16984241
theorem B8611309 : Blo 1490065 8611309 := bstep (se 3 (by rfl) ⟨1614620, by rfl⟩ : syracuseStep 8611309 = 3229241) B3229241
theorem B2238023 : Blo 1490065 2238023 := bstep (se 1 (by rfl) ⟨1678517, by rfl⟩ : syracuseStep 2238023 = 3357035) B3357035
theorem B2516663 : Blo 1490065 2516663 := bstep (se 1 (by rfl) ⟨1887497, by rfl⟩ : syracuseStep 2516663 = 3774995) B3774995
theorem B8496859 : Blo 1490065 8496859 := bstep (se 1 (by rfl) ⟨6372644, by rfl⟩ : syracuseStep 8496859 = 12745289) B12745289
theorem B3401671 : Blo 1490065 3401671 := bstep (se 1 (by rfl) ⟨2551253, by rfl⟩ : syracuseStep 3401671 = 5102507) B5102507
theorem B6367177 : Blo 1490065 6367177 := bstep (se 2 (by rfl) ⟨2387691, by rfl⟩ : syracuseStep 6367177 = 4775383) B4775383
theorem B5031881 : Blo 1490065 5031881 := bstep (se 2 (by rfl) ⟨1886955, by rfl⟩ : syracuseStep 5031881 = 3773911) B3773911
theorem B5032151 : Blo 1490065 5032151 := bstep (se 1 (by rfl) ⟨3774113, by rfl⟩ : syracuseStep 5032151 = 7548227) B7548227
theorem B2124073 : Blo 1490065 2124073 := bstep (se 2 (by rfl) ⟨796527, by rfl⟩ : syracuseStep 2124073 = 1593055) B1593055
theorem B5032475 : Blo 1490065 5032475 := bstep (se 1 (by rfl) ⟨3774356, by rfl⟩ : syracuseStep 5032475 = 7548713) B7548713
theorem B10750495 : Blo 1490065 10750495 := bstep (se 1 (by rfl) ⟨8062871, by rfl⟩ : syracuseStep 10750495 = 16125743) B16125743
theorem B3353399 : Blo 1490065 3353399 := bstep (se 1 (by rfl) ⟨2515049, by rfl⟩ : syracuseStep 3353399 = 5030099) B5030099
theorem B1887067 : Blo 1490065 1887067 := bstep (se 1 (by rfl) ⟨1415300, by rfl⟩ : syracuseStep 1887067 = 2830601) B2830601
theorem B2517851 : Blo 1490065 2517851 := bstep (se 1 (by rfl) ⟨1888388, by rfl⟩ : syracuseStep 2517851 = 3776777) B3776777
theorem B3353579 : Blo 1490065 3353579 := bstep (se 1 (by rfl) ⟨2515184, by rfl⟩ : syracuseStep 3353579 = 5030369) B5030369
theorem B183635009 : Blo 1490065 183635009 := bstep (se 2 (by rfl) ⟨68863128, by rfl⟩ : syracuseStep 183635009 = 137726257) B137726257
theorem B18132311 : Blo 1490065 18132311 := bstep (se 1 (by rfl) ⟨13599233, by rfl⟩ : syracuseStep 18132311 = 27198467) B27198467
theorem B5033339 : Blo 1490065 5033339 := bstep (se 1 (by rfl) ⟨3775004, by rfl⟩ : syracuseStep 5033339 = 7550009) B7550009
theorem B3771967 : Blo 1490065 3771967 := bstep (se 1 (by rfl) ⟨2828975, by rfl⟩ : syracuseStep 3771967 = 5657951) B5657951
theorem B4083263 : Blo 1490065 4083263 := bstep (se 1 (by rfl) ⟨3062447, by rfl⟩ : syracuseStep 4083263 = 6124895) B6124895
theorem B2829887 : Blo 1490065 2829887 := bstep (se 1 (by rfl) ⟨2122415, by rfl⟩ : syracuseStep 2829887 = 4244831) B4244831
theorem B29429365 : Blo 1490065 29429365 := bstep (se 5 (by rfl) ⟨1379501, by rfl⟩ : syracuseStep 29429365 = 2759003) B2759003
theorem B3772079 : Blo 1490065 3772079 := bstep (se 1 (by rfl) ⟨2829059, by rfl⟩ : syracuseStep 3772079 = 5658119) B5658119
theorem B3354407 : Blo 1490065 3354407 := bstep (se 1 (by rfl) ⟨2515805, by rfl⟩ : syracuseStep 3354407 = 5031611) B5031611
theorem B1888039 : Blo 1490065 1888039 := bstep (se 1 (by rfl) ⟨1416029, by rfl⟩ : syracuseStep 1888039 = 2832059) B2832059
theorem B1593127 : Blo 1490065 1593127 := bstep (se 1 (by rfl) ⟨1194845, by rfl⟩ : syracuseStep 1593127 = 2389691) B2389691
theorem B11325257 : Blo 1490065 11325257 := bstep (se 2 (by rfl) ⟨4246971, by rfl⟩ : syracuseStep 11325257 = 8493943) B8493943
theorem B4247417 : Blo 1490065 4247417 := bstep (se 2 (by rfl) ⟨1592781, by rfl⟩ : syracuseStep 4247417 = 3185563) B3185563
theorem B12742555 : Blo 1490065 12742555 := bstep (se 1 (by rfl) ⟨9556916, by rfl⟩ : syracuseStep 12742555 = 19113833) B19113833
theorem B9072557 : Blo 1490065 9072557 := bstep (se 3 (by rfl) ⟨1701104, by rfl⟩ : syracuseStep 9072557 = 3402209) B3402209
theorem B3772403 : Blo 1490065 3772403 := bstep (se 1 (by rfl) ⟨2829302, by rfl⟩ : syracuseStep 3772403 = 5658605) B5658605
theorem B5664755 : Blo 1490065 5664755 := bstep (se 1 (by rfl) ⟨4248566, by rfl⟩ : syracuseStep 5664755 = 8497133) B8497133
theorem B8491027 : Blo 1490065 8491027 := bstep (se 1 (by rfl) ⟨6368270, by rfl⟩ : syracuseStep 8491027 = 12736541) B12736541
theorem B9547895 : Blo 1490065 9547895 := bstep (se 1 (by rfl) ⟨7160921, by rfl⟩ : syracuseStep 9547895 = 14321843) B14321843
theorem B2388199 : Blo 1490065 2388199 := bstep (se 1 (by rfl) ⟨1791149, by rfl⟩ : syracuseStep 2388199 = 3582299) B3582299
theorem B2552095 : Blo 1490065 2552095 := bstep (se 1 (by rfl) ⟨1914071, by rfl⟩ : syracuseStep 2552095 = 3828143) B3828143
theorem B3772727 : Blo 1490065 3772727 := bstep (se 1 (by rfl) ⟨2829545, by rfl⟩ : syracuseStep 3772727 = 5659091) B5659091
theorem B4420055 : Blo 1490065 4420055 := bstep (se 1 (by rfl) ⟨3315041, by rfl⟩ : syracuseStep 4420055 = 6630083) B6630083
theorem B14324303 : Blo 1490065 14324303 := bstep (se 1 (by rfl) ⟨10743227, by rfl⟩ : syracuseStep 14324303 = 21486455) B21486455
theorem B7549523 : Blo 1490065 7549523 := bstep (se 1 (by rfl) ⟨5662142, by rfl⟩ : syracuseStep 7549523 = 11324285) B11324285
theorem B2830943 : Blo 1490065 2830943 := bstep (se 1 (by rfl) ⟨2123207, by rfl⟩ : syracuseStep 2830943 = 4246415) B4246415
theorem B2265835 : Blo 1490065 2265835 := bstep (se 1 (by rfl) ⟨1699376, by rfl⟩ : syracuseStep 2265835 = 3398753) B3398753
theorem B5034743 : Blo 1490065 5034743 := bstep (se 1 (by rfl) ⟨3776057, by rfl⟩ : syracuseStep 5034743 = 7552115) B7552115
theorem B3183401 : Blo 1490065 3183401 := bstep (se 2 (by rfl) ⟨1193775, by rfl⟩ : syracuseStep 3183401 = 2387551) B2387551
theorem B3355433 : Blo 1490065 3355433 := bstep (se 2 (by rfl) ⟨1258287, by rfl⟩ : syracuseStep 3355433 = 2516575) B2516575
theorem B3355703 : Blo 1490065 3355703 := bstep (se 1 (by rfl) ⟨2516777, by rfl⟩ : syracuseStep 3355703 = 5033555) B5033555
theorem B3355721 : Blo 1490065 3355721 := bstep (se 2 (by rfl) ⟨1258395, by rfl⟩ : syracuseStep 3355721 = 2516791) B2516791
theorem B9557099 : Blo 1490065 9557099 := bstep (se 1 (by rfl) ⟨7167824, by rfl⟩ : syracuseStep 9557099 = 14335649) B14335649
theorem B45937817 : Blo 1490065 45937817 := bstep (se 2 (by rfl) ⟨17226681, by rfl⟩ : syracuseStep 45937817 = 34453363) B34453363
theorem B5035283 : Blo 1490065 5035283 := bstep (se 1 (by rfl) ⟨3776462, by rfl⟩ : syracuseStep 5035283 = 7552925) B7552925
theorem B24515875 : Blo 1490065 24515875 := bstep (se 1 (by rfl) ⟨18386906, by rfl⟩ : syracuseStep 24515875 = 36773813) B36773813
theorem B3774023 : Blo 1490065 3774023 := bstep (se 1 (by rfl) ⟨2830517, by rfl⟩ : syracuseStep 3774023 = 5661035) B5661035
theorem B5101127 : Blo 1490065 5101127 := bstep (se 1 (by rfl) ⟨3825845, by rfl⟩ : syracuseStep 5101127 = 7651691) B7651691
theorem B1676911 : Blo 1490065 1676911 := bstep (se 1 (by rfl) ⟨1257683, by rfl⟩ : syracuseStep 1676911 = 2515367) B2515367
theorem B25482923 : Blo 1490065 25482923 := bstep (se 1 (by rfl) ⟨19112192, by rfl⟩ : syracuseStep 25482923 = 38224385) B38224385
theorem B1677019 : Blo 1490065 1677019 := bstep (se 1 (by rfl) ⟨1257764, by rfl⟩ : syracuseStep 1677019 = 2515529) B2515529
theorem B4536121 : Blo 1490065 4536121 := bstep (se 2 (by rfl) ⟨1701045, by rfl⟩ : syracuseStep 4536121 = 3402091) B3402091
theorem B3774559 : Blo 1490065 3774559 := bstep (se 1 (by rfl) ⟨2830919, by rfl⟩ : syracuseStep 3774559 = 5661839) B5661839
theorem B43604099 : Blo 1490065 43604099 := bstep (se 1 (by rfl) ⟨32703074, by rfl⟩ : syracuseStep 43604099 = 65406149) B65406149
theorem B2832545 : Blo 1490065 2832545 := bstep (se 2 (by rfl) ⟨1062204, by rfl⟩ : syracuseStep 2832545 = 2124409) B2124409
theorem B11327687 : Blo 1490065 11327687 := bstep (se 1 (by rfl) ⟨8495765, by rfl⟩ : syracuseStep 11327687 = 16991531) B16991531
theorem B7551305 : Blo 1490065 7551305 := bstep (se 2 (by rfl) ⟨2831739, by rfl⟩ : syracuseStep 7551305 = 5663479) B5663479
theorem B2685577 : Blo 1490065 2685577 := bstep (se 2 (by rfl) ⟨1007091, by rfl⟩ : syracuseStep 2685577 = 2014183) B2014183
theorem B2235191 : Blo 1490065 2235191 := bstep (se 1 (by rfl) ⟨1676393, by rfl⟩ : syracuseStep 2235191 = 3352787) B3352787
theorem B2685779 : Blo 1490065 2685779 := bstep (se 1 (by rfl) ⟨2014334, by rfl⟩ : syracuseStep 2685779 = 4028669) B4028669
theorem B2235227 : Blo 1490065 2235227 := bstep (se 1 (by rfl) ⟨1676420, by rfl⟩ : syracuseStep 2235227 = 3352841) B3352841
theorem B1678171 : Blo 1490065 1678171 := bstep (se 1 (by rfl) ⟨1258628, by rfl⟩ : syracuseStep 1678171 = 2517257) B2517257
theorem B38755259 : Blo 1490065 38755259 := bstep (se 1 (by rfl) ⟨29066444, by rfl⟩ : syracuseStep 38755259 = 58132889) B58132889
theorem B2235371 : Blo 1490065 2235371 := bstep (se 1 (by rfl) ⟨1676528, by rfl⟩ : syracuseStep 2235371 = 3353057) B3353057
theorem B4906055 : Blo 1490065 4906055 := bstep (se 1 (by rfl) ⟨3679541, by rfl⟩ : syracuseStep 4906055 = 7359083) B7359083
theorem B5372999 : Blo 1490065 5372999 := bstep (se 1 (by rfl) ⟨4029749, by rfl⟩ : syracuseStep 5372999 = 8059499) B8059499
theorem B11320397 : Blo 1490065 11320397 := bstep (se 3 (by rfl) ⟨2122574, by rfl⟩ : syracuseStep 11320397 = 4245149) B4245149
theorem B11328659 : Blo 1490065 11328659 := bstep (se 1 (by rfl) ⟨8496494, by rfl⟩ : syracuseStep 11328659 = 16992989) B16992989
theorem B2235575 : Blo 1490065 2235575 := bstep (se 1 (by rfl) ⟨1676681, by rfl⟩ : syracuseStep 2235575 = 3353363) B3353363
theorem B1490143 : Blo 1490065 1490143 := bstep (se 1 (by rfl) ⟨1117607, by rfl⟩ : syracuseStep 1490143 = 2235215) B2235215
theorem B3775855 : Blo 1490065 3775855 := bstep (se 1 (by rfl) ⟨2831891, by rfl⟩ : syracuseStep 3775855 = 5663783) B5663783
theorem B3399079 : Blo 1490065 3399079 := bstep (se 1 (by rfl) ⟨2549309, by rfl⟩ : syracuseStep 3399079 = 5098619) B5098619
theorem B2235815 : Blo 1490065 2235815 := bstep (se 1 (by rfl) ⟨1676861, by rfl⟩ : syracuseStep 2235815 = 3353723) B3353723
theorem B20397541 : Blo 1490065 20397541 := bstep (se 4 (by rfl) ⟨1912269, by rfl⟩ : syracuseStep 20397541 = 3824539) B3824539
theorem B1490407 : Blo 1490065 1490407 := bstep (se 1 (by rfl) ⟨1117805, by rfl⟩ : syracuseStep 1490407 = 2235611) B2235611
theorem B2235899 : Blo 1490065 2235899 := bstep (se 1 (by rfl) ⟨1676924, by rfl⟩ : syracuseStep 2235899 = 3353849) B3353849
theorem B2514523 : Blo 1490065 2514523 := bstep (se 1 (by rfl) ⟨1885892, by rfl⟩ : syracuseStep 2514523 = 3771785) B3771785
theorem B1490523 : Blo 1490065 1490523 := bstep (se 1 (by rfl) ⟨1117892, by rfl⟩ : syracuseStep 1490523 = 2235785) B2235785
theorem B2235995 : Blo 1490065 2235995 := bstep (se 1 (by rfl) ⟨1676996, by rfl⟩ : syracuseStep 2235995 = 3353993) B3353993
theorem B2236079 : Blo 1490065 2236079 := bstep (se 1 (by rfl) ⟨1677059, by rfl⟩ : syracuseStep 2236079 = 3354119) B3354119
theorem B6799033 : Blo 1490065 6799033 := bstep (se 2 (by rfl) ⟨2549637, by rfl⟩ : syracuseStep 6799033 = 5099275) B5099275
theorem B2514665 : Blo 1490065 2514665 := bstep (se 2 (by rfl) ⟨942999, by rfl⟩ : syracuseStep 2514665 = 1885999) B1885999
theorem B2236199 : Blo 1490065 2236199 := bstep (se 1 (by rfl) ⟨1677149, by rfl⟩ : syracuseStep 2236199 = 3354299) B3354299
theorem B1490759 : Blo 1490065 1490759 := bstep (se 1 (by rfl) ⟨1118069, by rfl⟩ : syracuseStep 1490759 = 2236139) B2236139
theorem B2236283 : Blo 1490065 2236283 := bstep (se 1 (by rfl) ⟨1677212, by rfl⟩ : syracuseStep 2236283 = 3354425) B3354425
theorem B28655531 : Blo 1490065 28655531 := bstep (se 1 (by rfl) ⟨21491648, by rfl⟩ : syracuseStep 28655531 = 42983297) B42983297
theorem B40812497 : Blo 1490065 40812497 := bstep (se 2 (by rfl) ⟨15304686, by rfl⟩ : syracuseStep 40812497 = 30609373) B30609373
theorem B1490911 : Blo 1490065 1490911 := bstep (se 1 (by rfl) ⟨1118183, by rfl⟩ : syracuseStep 1490911 = 2236367) B2236367
theorem B98041873 : Blo 1490065 98041873 := bstep (se 2 (by rfl) ⟨36765702, by rfl⟩ : syracuseStep 98041873 = 73531405) B73531405
theorem B11321369 : Blo 1490065 11321369 := bstep (se 2 (by rfl) ⟨4245513, by rfl⟩ : syracuseStep 11321369 = 8491027) B8491027
theorem B14516281 : Blo 1490065 14516281 := bstep (se 2 (by rfl) ⟨5443605, by rfl⟩ : syracuseStep 14516281 = 10887211) B10887211
theorem B1491135 : Blo 1490065 1491135 := bstep (se 1 (by rfl) ⟨1118351, by rfl⟩ : syracuseStep 1491135 = 2236703) B2236703
theorem B2515151 : Blo 1490065 2515151 := bstep (se 1 (by rfl) ⟨1886363, by rfl⟩ : syracuseStep 2515151 = 3772727) B3772727
theorem B1491151 : Blo 1490065 1491151 := bstep (se 1 (by rfl) ⟨1118363, by rfl⟩ : syracuseStep 1491151 = 2236727) B2236727
theorem B4243691 : Blo 1490065 4243691 := bstep (se 1 (by rfl) ⟨3182768, by rfl⟩ : syracuseStep 4243691 = 6365537) B6365537
theorem B1491199 : Blo 1490065 1491199 := bstep (se 1 (by rfl) ⟨1118399, by rfl⟩ : syracuseStep 1491199 = 2236799) B2236799
theorem B1491247 : Blo 1490065 1491247 := bstep (se 1 (by rfl) ⟨1118435, by rfl⟩ : syracuseStep 1491247 = 2236871) B2236871
theorem B25461053 : Blo 1490065 25461053 := bstep (se 3 (by rfl) ⟨4773947, by rfl⟩ : syracuseStep 25461053 = 9547895) B9547895
theorem B2236955 : Blo 1490065 2236955 := bstep (se 1 (by rfl) ⟨1677716, by rfl⟩ : syracuseStep 2236955 = 3355433) B3355433
theorem B1491483 : Blo 1490065 1491483 := bstep (se 1 (by rfl) ⟨1118612, by rfl⟩ : syracuseStep 1491483 = 2237225) B2237225
theorem B1491487 : Blo 1490065 1491487 := bstep (se 1 (by rfl) ⟨1118615, by rfl⟩ : syracuseStep 1491487 = 2237231) B2237231
theorem B1491567 : Blo 1490065 1491567 := bstep (se 1 (by rfl) ⟨1118675, by rfl⟩ : syracuseStep 1491567 = 2237351) B2237351
theorem B1491623 : Blo 1490065 1491623 := bstep (se 1 (by rfl) ⟨1118717, by rfl⟩ : syracuseStep 1491623 = 2237435) B2237435
theorem B2237135 : Blo 1490065 2237135 := bstep (se 1 (by rfl) ⟨1677851, by rfl⟩ : syracuseStep 2237135 = 3355703) B3355703
theorem B1491663 : Blo 1490065 1491663 := bstep (se 1 (by rfl) ⟨1118747, by rfl⟩ : syracuseStep 1491663 = 2237495) B2237495
theorem B2237147 : Blo 1490065 2237147 := bstep (se 1 (by rfl) ⟨1677860, by rfl⟩ : syracuseStep 2237147 = 3355721) B3355721
theorem B1491743 : Blo 1490065 1491743 := bstep (se 1 (by rfl) ⟨1118807, by rfl⟩ : syracuseStep 1491743 = 2237615) B2237615
theorem B3580769 : Blo 1490065 3580769 := bstep (se 2 (by rfl) ⟨1342788, by rfl⟩ : syracuseStep 3580769 = 2685577) B2685577
theorem B2516015 : Blo 1490065 2516015 := bstep (se 1 (by rfl) ⟨1887011, by rfl⟩ : syracuseStep 2516015 = 3774023) B3774023
theorem B3400751 : Blo 1490065 3400751 := bstep (se 1 (by rfl) ⟨2550563, by rfl⟩ : syracuseStep 3400751 = 5101127) B5101127
theorem B1492015 : Blo 1490065 1492015 := bstep (se 1 (by rfl) ⟨1119011, by rfl⟩ : syracuseStep 1492015 = 2238023) B2238023
theorem B2516089 : Blo 1490065 2516089 := bstep (se 2 (by rfl) ⟨943533, by rfl⟩ : syracuseStep 2516089 = 1887067) B1887067
theorem B2237561 : Blo 1490065 2237561 := bstep (se 2 (by rfl) ⟨839085, by rfl⟩ : syracuseStep 2237561 = 1678171) B1678171
theorem B8496677 : Blo 1490065 8496677 := bstep (se 4 (by rfl) ⟨796563, by rfl⟩ : syracuseStep 8496677 = 1593127) B1593127
theorem B32687833 : Blo 1490065 32687833 := bstep (se 2 (by rfl) ⟨12257937, by rfl⟩ : syracuseStep 32687833 = 24515875) B24515875
theorem B4532105 : Blo 1490065 4532105 := bstep (se 2 (by rfl) ⟨1699539, by rfl⟩ : syracuseStep 4532105 = 3399079) B3399079
theorem B122423339 : Blo 1490065 122423339 := bstep (se 1 (by rfl) ⟨91817504, by rfl⟩ : syracuseStep 122423339 = 183635009) B183635009
theorem B3270703 : Blo 1490065 3270703 := bstep (se 1 (by rfl) ⟨2453027, by rfl⟩ : syracuseStep 3270703 = 4906055) B4906055
theorem B3581999 : Blo 1490065 3581999 := bstep (se 1 (by rfl) ⟨2686499, by rfl⟩ : syracuseStep 3581999 = 5372999) B5372999
theorem B7546931 : Blo 1490065 7546931 := bstep (se 1 (by rfl) ⟨5660198, by rfl⟩ : syracuseStep 7546931 = 11320397) B11320397
theorem B8489069 : Blo 1490065 8489069 := bstep (se 3 (by rfl) ⟨1591700, by rfl⟩ : syracuseStep 8489069 = 3183401) B3183401
theorem B3352697 : Blo 1490065 3352697 := bstep (se 2 (by rfl) ⟨1257261, by rfl⟩ : syracuseStep 3352697 = 2514523) B2514523
theorem B2722175 : Blo 1490065 2722175 := bstep (se 1 (by rfl) ⟨2041631, by rfl⟩ : syracuseStep 2722175 = 4083263) B4083263
theorem B1886591 : Blo 1490065 1886591 := bstep (se 1 (by rfl) ⟨1414943, by rfl⟩ : syracuseStep 1886591 = 2829887) B2829887
theorem B2517385 : Blo 1490065 2517385 := bstep (se 2 (by rfl) ⟨944019, by rfl⟩ : syracuseStep 2517385 = 1888039) B1888039
theorem B6048161 : Blo 1490065 6048161 := bstep (se 2 (by rfl) ⟨2268060, by rfl⟩ : syracuseStep 6048161 = 4536121) B4536121
theorem B8489569 : Blo 1490065 8489569 := bstep (se 2 (by rfl) ⟨3183588, by rfl⟩ : syracuseStep 8489569 = 6367177) B6367177
theorem B6048371 : Blo 1490065 6048371 := bstep (se 1 (by rfl) ⟨4536278, by rfl⟩ : syracuseStep 6048371 = 9072557) B9072557
theorem B27208331 : Blo 1490065 27208331 := bstep (se 1 (by rfl) ⟨20406248, by rfl⟩ : syracuseStep 27208331 = 40812497) B40812497
theorem B5032745 : Blo 1490065 5032745 := bstep (se 2 (by rfl) ⟨1887279, by rfl⟩ : syracuseStep 5032745 = 3774559) B3774559
theorem B14330843 : Blo 1490065 14330843 := bstep (se 1 (by rfl) ⟨10748132, by rfl⟩ : syracuseStep 14330843 = 21496265) B21496265
theorem B6892519 : Blo 1490065 6892519 := bstep (se 1 (by rfl) ⟨5169389, by rfl⟩ : syracuseStep 6892519 = 10338779) B10338779
theorem B3402793 : Blo 1490065 3402793 := bstep (se 2 (by rfl) ⟨1276047, by rfl⟩ : syracuseStep 3402793 = 2552095) B2552095
theorem B5033015 : Blo 1490065 5033015 := bstep (se 1 (by rfl) ⟨3774761, by rfl⟩ : syracuseStep 5033015 = 7549523) B7549523
theorem B1887295 : Blo 1490065 1887295 := bstep (se 1 (by rfl) ⟨1415471, by rfl⟩ : syracuseStep 1887295 = 2830943) B2830943
theorem B3776503 : Blo 1490065 3776503 := bstep (se 1 (by rfl) ⟨2832377, by rfl⟩ : syracuseStep 3776503 = 5664755) B5664755
theorem B3354011 : Blo 1490065 3354011 := bstep (se 1 (by rfl) ⟨2515508, by rfl⟩ : syracuseStep 3354011 = 5031017) B5031017
theorem B6368681 : Blo 1490065 6368681 := bstep (se 2 (by rfl) ⟨2388255, by rfl⟩ : syracuseStep 6368681 = 4776511) B4776511
theorem B30625211 : Blo 1490065 30625211 := bstep (se 1 (by rfl) ⟨22968908, by rfl⟩ : syracuseStep 30625211 = 45937817) B45937817
theorem B7548551 : Blo 1490065 7548551 := bstep (se 1 (by rfl) ⟨5661413, by rfl⟩ : syracuseStep 7548551 = 11322827) B11322827
theorem B3354587 : Blo 1490065 3354587 := bstep (se 1 (by rfl) ⟨2515940, by rfl⟩ : syracuseStep 3354587 = 5031881) B5031881
theorem B29069399 : Blo 1490065 29069399 := bstep (se 1 (by rfl) ⟨21802049, by rfl⟩ : syracuseStep 29069399 = 43604099) B43604099
theorem B1888363 : Blo 1490065 1888363 := bstep (se 1 (by rfl) ⟨1416272, by rfl⟩ : syracuseStep 1888363 = 2832545) B2832545
theorem B3354767 : Blo 1490065 3354767 := bstep (se 1 (by rfl) ⟨2516075, by rfl⟩ : syracuseStep 3354767 = 5032151) B5032151
theorem B5034203 : Blo 1490065 5034203 := bstep (se 1 (by rfl) ⟨3775652, by rfl⟩ : syracuseStep 5034203 = 7551305) B7551305
theorem B3354857 : Blo 1490065 3354857 := bstep (se 2 (by rfl) ⟨1258071, by rfl⟩ : syracuseStep 3354857 = 2516143) B2516143
theorem B3354983 : Blo 1490065 3354983 := bstep (se 1 (by rfl) ⟨2516237, by rfl⟩ : syracuseStep 3354983 = 5032475) B5032475
theorem B5034473 : Blo 1490065 5034473 := bstep (se 2 (by rfl) ⟨1887927, by rfl⟩ : syracuseStep 5034473 = 3775855) B3775855
theorem B1790519 : Blo 1490065 1790519 := bstep (se 1 (by rfl) ⟨1342889, by rfl⟩ : syracuseStep 1790519 = 2685779) B2685779
theorem B11481745 : Blo 1490065 11481745 := bstep (se 2 (by rfl) ⟨4305654, by rfl⟩ : syracuseStep 11481745 = 8611309) B8611309
theorem B12088207 : Blo 1490065 12088207 := bstep (se 1 (by rfl) ⟨9066155, by rfl⟩ : syracuseStep 12088207 = 18132311) B18132311
theorem B9065377 : Blo 1490065 9065377 := bstep (se 2 (by rfl) ⟨3399516, by rfl⟩ : syracuseStep 9065377 = 6799033) B6799033
theorem B3355559 : Blo 1490065 3355559 := bstep (se 1 (by rfl) ⟨2516669, by rfl⟩ : syracuseStep 3355559 = 5033339) B5033339
theorem B1676443 : Blo 1490065 1676443 := bstep (se 1 (by rfl) ⟨1257332, by rfl⟩ : syracuseStep 1676443 = 2514665) B2514665
theorem B7550171 : Blo 1490065 7550171 := bstep (se 1 (by rfl) ⟨5662628, by rfl⟩ : syracuseStep 7550171 = 11325257) B11325257
theorem B2831611 : Blo 1490065 2831611 := bstep (se 1 (by rfl) ⟨2123708, by rfl⟩ : syracuseStep 2831611 = 4247417) B4247417
theorem B4535561 : Blo 1490065 4535561 := bstep (se 2 (by rfl) ⟨1700835, by rfl⟩ : syracuseStep 4535561 = 3401671) B3401671
theorem B5100907 : Blo 1490065 5100907 := bstep (se 1 (by rfl) ⟨3825680, by rfl⟩ : syracuseStep 5100907 = 7651361) B7651361
theorem B3184265 : Blo 1490065 3184265 := bstep (se 2 (by rfl) ⟨1194099, by rfl⟩ : syracuseStep 3184265 = 2388199) B2388199
theorem B2946703 : Blo 1490065 2946703 := bstep (se 1 (by rfl) ⟨2210027, by rfl⟩ : syracuseStep 2946703 = 4420055) B4420055
theorem B2832097 : Blo 1490065 2832097 := bstep (se 2 (by rfl) ⟨1062036, by rfl⟩ : syracuseStep 2832097 = 2124073) B2124073
theorem B7165691 : Blo 1490065 7165691 := bstep (se 1 (by rfl) ⟨5374268, by rfl⟩ : syracuseStep 7165691 = 10748537) B10748537
theorem B1677127 : Blo 1490065 1677127 := bstep (se 1 (by rfl) ⟨1257845, by rfl⟩ : syracuseStep 1677127 = 2515691) B2515691
theorem B3356495 : Blo 1490065 3356495 := bstep (se 1 (by rfl) ⟨2517371, by rfl⟩ : syracuseStep 3356495 = 5034743) B5034743
theorem B2267003 : Blo 1490065 2267003 := bstep (se 1 (by rfl) ⟨1700252, by rfl⟩ : syracuseStep 2267003 = 3400505) B3400505
theorem B14333993 : Blo 1490065 14333993 := bstep (se 2 (by rfl) ⟨5375247, by rfl⟩ : syracuseStep 14333993 = 10750495) B10750495
theorem B6371399 : Blo 1490065 6371399 := bstep (se 1 (by rfl) ⟨4778549, by rfl⟩ : syracuseStep 6371399 = 9557099) B9557099
theorem B3356855 : Blo 1490065 3356855 := bstep (se 1 (by rfl) ⟨2517641, by rfl⟩ : syracuseStep 3356855 = 5035283) B5035283
theorem B3021113 : Blo 1490065 3021113 := bstep (se 2 (by rfl) ⟨1132917, by rfl⟩ : syracuseStep 3021113 = 2265835) B2265835
theorem B16988615 : Blo 1490065 16988615 := bstep (se 1 (by rfl) ⟨12741461, by rfl⟩ : syracuseStep 16988615 = 25482923) B25482923
theorem B1677775 : Blo 1490065 1677775 := bstep (se 1 (by rfl) ⟨1258331, by rfl⟩ : syracuseStep 1677775 = 2516663) B2516663
theorem B15292901 : Blo 1490065 15292901 := bstep (se 4 (by rfl) ⟨1433709, by rfl⟩ : syracuseStep 15292901 = 2867419) B2867419
theorem B7551791 : Blo 1490065 7551791 := bstep (se 1 (by rfl) ⟨5663843, by rfl⟩ : syracuseStep 7551791 = 11327687) B11327687
theorem B38198141 : Blo 1490065 38198141 := bstep (se 3 (by rfl) ⟨7162151, by rfl⟩ : syracuseStep 38198141 = 14324303) B14324303
theorem B1490127 : Blo 1490065 1490127 := bstep (se 1 (by rfl) ⟨1117595, by rfl⟩ : syracuseStep 1490127 = 2235191) B2235191
theorem B2235599 : Blo 1490065 2235599 := bstep (se 1 (by rfl) ⟨1676699, by rfl⟩ : syracuseStep 2235599 = 3353399) B3353399
theorem B1490151 : Blo 1490065 1490151 := bstep (se 1 (by rfl) ⟨1117613, by rfl⟩ : syracuseStep 1490151 = 2235227) B2235227
theorem B1678567 : Blo 1490065 1678567 := bstep (se 1 (by rfl) ⟨1258925, by rfl⟩ : syracuseStep 1678567 = 2517851) B2517851
theorem B25836839 : Blo 1490065 25836839 := bstep (se 1 (by rfl) ⟨19377629, by rfl⟩ : syracuseStep 25836839 = 38755259) B38755259
theorem B27196721 : Blo 1490065 27196721 := bstep (se 2 (by rfl) ⟨10198770, by rfl⟩ : syracuseStep 27196721 = 20397541) B20397541
theorem B1490247 : Blo 1490065 1490247 := bstep (se 1 (by rfl) ⟨1117685, by rfl⟩ : syracuseStep 1490247 = 2235371) B2235371
theorem B2235719 : Blo 1490065 2235719 := bstep (se 1 (by rfl) ⟨1676789, by rfl⟩ : syracuseStep 2235719 = 3353579) B3353579
theorem B5029289 : Blo 1490065 5029289 := bstep (se 2 (by rfl) ⟨1885983, by rfl⟩ : syracuseStep 5029289 = 3771967) B3771967
theorem B7552439 : Blo 1490065 7552439 := bstep (se 1 (by rfl) ⟨5664329, by rfl⟩ : syracuseStep 7552439 = 11328659) B11328659
theorem B1490383 : Blo 1490065 1490383 := bstep (se 1 (by rfl) ⟨1117787, by rfl⟩ : syracuseStep 1490383 = 2235575) B2235575
theorem B2235881 : Blo 1490065 2235881 := bstep (se 2 (by rfl) ⟨838455, by rfl⟩ : syracuseStep 2235881 = 1676911) B1676911
theorem B39239153 : Blo 1490065 39239153 := bstep (se 2 (by rfl) ⟨14714682, by rfl⟩ : syracuseStep 39239153 = 29429365) B29429365
theorem B1490543 : Blo 1490065 1490543 := bstep (se 1 (by rfl) ⟨1117907, by rfl⟩ : syracuseStep 1490543 = 2235815) B2235815
theorem B2236025 : Blo 1490065 2236025 := bstep (se 2 (by rfl) ⟨838509, by rfl⟩ : syracuseStep 2236025 = 1677019) B1677019
theorem B11329145 : Blo 1490065 11329145 := bstep (se 2 (by rfl) ⟨4248429, by rfl⟩ : syracuseStep 11329145 = 8496859) B8496859
theorem B1490599 : Blo 1490065 1490599 := bstep (se 1 (by rfl) ⟨1117949, by rfl⟩ : syracuseStep 1490599 = 2235899) B2235899
theorem B1490663 : Blo 1490065 1490663 := bstep (se 1 (by rfl) ⟨1117997, by rfl⟩ : syracuseStep 1490663 = 2235995) B2235995
theorem B2514719 : Blo 1490065 2514719 := bstep (se 1 (by rfl) ⟨1886039, by rfl⟩ : syracuseStep 2514719 = 3772079) B3772079
theorem B1490719 : Blo 1490065 1490719 := bstep (se 1 (by rfl) ⟨1118039, by rfl⟩ : syracuseStep 1490719 = 2236079) B2236079
theorem B1490799 : Blo 1490065 1490799 := bstep (se 1 (by rfl) ⟨1118099, by rfl⟩ : syracuseStep 1490799 = 2236199) B2236199
theorem B2236271 : Blo 1490065 2236271 := bstep (se 1 (by rfl) ⟨1677203, by rfl⟩ : syracuseStep 2236271 = 3354407) B3354407
theorem B16990073 : Blo 1490065 16990073 := bstep (se 2 (by rfl) ⟨6371277, by rfl⟩ : syracuseStep 16990073 = 12742555) B12742555
theorem B1490855 : Blo 1490065 1490855 := bstep (se 1 (by rfl) ⟨1118141, by rfl⟩ : syracuseStep 1490855 = 2236283) B2236283
theorem B19103687 : Blo 1490065 19103687 := bstep (se 1 (by rfl) ⟨14327765, by rfl⟩ : syracuseStep 19103687 = 28655531) B28655531
theorem B2514935 : Blo 1490065 2514935 := bstep (se 1 (by rfl) ⟨1886201, by rfl⟩ : syracuseStep 2514935 = 3772403) B3772403
theorem B2236511 : Blo 1490065 2236511 := bstep (se 1 (by rfl) ⟨1677383, by rfl⟩ : syracuseStep 2236511 = 3354767) B3354767
theorem B9068669 : Blo 1490065 9068669 := bstep (se 3 (by rfl) ⟨1700375, by rfl⟩ : syracuseStep 9068669 = 3400751) B3400751
theorem B2236571 : Blo 1490065 2236571 := bstep (se 1 (by rfl) ⟨1677428, by rfl⟩ : syracuseStep 2236571 = 3354857) B3354857
theorem B16974035 : Blo 1490065 16974035 := bstep (se 1 (by rfl) ⟨12730526, by rfl⟩ : syracuseStep 16974035 = 25461053) B25461053
theorem B2236655 : Blo 1490065 2236655 := bstep (se 1 (by rfl) ⟨1677491, by rfl⟩ : syracuseStep 2236655 = 3354983) B3354983
theorem B1491303 : Blo 1490065 1491303 := bstep (se 1 (by rfl) ⟨1118477, by rfl⟩ : syracuseStep 1491303 = 2236955) B2236955
theorem B1491423 : Blo 1490065 1491423 := bstep (se 1 (by rfl) ⟨1118567, by rfl⟩ : syracuseStep 1491423 = 2237135) B2237135
theorem B1491431 : Blo 1490065 1491431 := bstep (se 1 (by rfl) ⟨1118573, by rfl⟩ : syracuseStep 1491431 = 2237147) B2237147
theorem B2237033 : Blo 1490065 2237033 := bstep (se 2 (by rfl) ⟨838887, by rfl⟩ : syracuseStep 2237033 = 1677775) B1677775
theorem B2237039 : Blo 1490065 2237039 := bstep (se 1 (by rfl) ⟨1677779, by rfl⟩ : syracuseStep 2237039 = 3355559) B3355559
theorem B1491707 : Blo 1490065 1491707 := bstep (se 1 (by rfl) ⟨1118780, by rfl⟩ : syracuseStep 1491707 = 2237561) B2237561
theorem B5030909 : Blo 1490065 5030909 := bstep (se 3 (by rfl) ⟨943295, by rfl⟩ : syracuseStep 5030909 = 1886591) B1886591
theorem B2122843 : Blo 1490065 2122843 := bstep (se 1 (by rfl) ⟨1592132, by rfl⟩ : syracuseStep 2122843 = 3184265) B3184265
theorem B4777127 : Blo 1490065 4777127 := bstep (se 1 (by rfl) ⟨3582845, by rfl⟩ : syracuseStep 4777127 = 7165691) B7165691
theorem B2237663 : Blo 1490065 2237663 := bstep (se 1 (by rfl) ⟨1678247, by rfl⟩ : syracuseStep 2237663 = 3356495) B3356495
theorem B5031287 : Blo 1490065 5031287 := bstep (se 1 (by rfl) ⟨3773465, by rfl⟩ : syracuseStep 5031287 = 7546931) B7546931
theorem B2516393 : Blo 1490065 2516393 := bstep (se 2 (by rfl) ⟨943647, by rfl⟩ : syracuseStep 2516393 = 1887295) B1887295
theorem B2237903 : Blo 1490065 2237903 := bstep (se 1 (by rfl) ⟨1678427, by rfl⟩ : syracuseStep 2237903 = 3356855) B3356855
theorem B4032107 : Blo 1490065 4032107 := bstep (se 1 (by rfl) ⟨3024080, by rfl⟩ : syracuseStep 4032107 = 6048161) B6048161
theorem B2238089 : Blo 1490065 2238089 := bstep (se 2 (by rfl) ⟨839283, by rfl⟩ : syracuseStep 2238089 = 1678567) B1678567
theorem B18138887 : Blo 1490065 18138887 := bstep (se 1 (by rfl) ⟨13604165, by rfl⟩ : syracuseStep 18138887 = 27208331) B27208331
theorem B6801209 : Blo 1490065 6801209 := bstep (se 2 (by rfl) ⟨2550453, by rfl⟩ : syracuseStep 6801209 = 5100907) B5100907
theorem B9553895 : Blo 1490065 9553895 := bstep (se 1 (by rfl) ⟨7165421, by rfl⟩ : syracuseStep 9553895 = 14330843) B14330843
theorem B18131147 : Blo 1490065 18131147 := bstep (se 1 (by rfl) ⟨13598360, by rfl⟩ : syracuseStep 18131147 = 27196721) B27196721
theorem B3352859 : Blo 1490065 3352859 := bstep (se 1 (by rfl) ⟨2514644, by rfl⟩ : syracuseStep 3352859 = 5029289) B5029289
theorem B4245787 : Blo 1490065 4245787 := bstep (se 1 (by rfl) ⟨3184340, by rfl⟩ : syracuseStep 4245787 = 6368681) B6368681
theorem B43583777 : Blo 1490065 43583777 := bstep (se 2 (by rfl) ⟨16343916, by rfl⟩ : syracuseStep 43583777 = 32687833) B32687833
theorem B20416807 : Blo 1490065 20416807 := bstep (se 1 (by rfl) ⟨15312605, by rfl⟩ : syracuseStep 20416807 = 30625211) B30625211
theorem B26159435 : Blo 1490065 26159435 := bstep (se 1 (by rfl) ⟨19619576, by rfl⟩ : syracuseStep 26159435 = 39239153) B39239153
theorem B12085613 : Blo 1490065 12085613 := bstep (se 3 (by rfl) ⟨2266052, by rfl⟩ : syracuseStep 12085613 = 4532105) B4532105
theorem B5032367 : Blo 1490065 5032367 := bstep (se 1 (by rfl) ⟨3774275, by rfl⟩ : syracuseStep 5032367 = 7548551) B7548551
theorem B7547579 : Blo 1490065 7547579 := bstep (se 1 (by rfl) ⟨5660684, by rfl⟩ : syracuseStep 7547579 = 11321369) B11321369
theorem B130722497 : Blo 1490065 130722497 := bstep (se 2 (by rfl) ⟨49020936, by rfl⟩ : syracuseStep 130722497 = 98041873) B98041873
theorem B4360937 : Blo 1490065 4360937 := bstep (se 2 (by rfl) ⟨1635351, by rfl⟩ : syracuseStep 4360937 = 3270703) B3270703
theorem B2517817 : Blo 1490065 2517817 := bstep (se 2 (by rfl) ⟨944181, by rfl⟩ : syracuseStep 2517817 = 1888363) B1888363
theorem B2387179 : Blo 1490065 2387179 := bstep (se 1 (by rfl) ⟨1790384, by rfl⟩ : syracuseStep 2387179 = 3580769) B3580769
theorem B11316509 : Blo 1490065 11316509 := bstep (se 3 (by rfl) ⟨2121845, by rfl⟩ : syracuseStep 11316509 = 4243691) B4243691
theorem B12094829 : Blo 1490065 12094829 := bstep (se 3 (by rfl) ⟨2267780, by rfl⟩ : syracuseStep 12094829 = 4535561) B4535561
theorem B5033447 : Blo 1490065 5033447 := bstep (se 1 (by rfl) ⟨3775085, by rfl⟩ : syracuseStep 5033447 = 7550171) B7550171
theorem B5664451 : Blo 1490065 5664451 := bstep (se 1 (by rfl) ⟨4248338, by rfl⟩ : syracuseStep 5664451 = 8496677) B8496677
theorem B1511335 : Blo 1490065 1511335 := bstep (se 1 (by rfl) ⟨1133501, by rfl⟩ : syracuseStep 1511335 = 2267003) B2267003
theorem B9555995 : Blo 1490065 9555995 := bstep (se 1 (by rfl) ⟨7166996, by rfl⟩ : syracuseStep 9555995 = 14333993) B14333993
theorem B2387999 : Blo 1490065 2387999 := bstep (se 1 (by rfl) ⟨1790999, by rfl⟩ : syracuseStep 2387999 = 3581999) B3581999
theorem B4247599 : Blo 1490065 4247599 := bstep (se 1 (by rfl) ⟨3185699, by rfl⟩ : syracuseStep 4247599 = 6371399) B6371399
theorem B3354785 : Blo 1490065 3354785 := bstep (se 2 (by rfl) ⟨1258044, by rfl⟩ : syracuseStep 3354785 = 2516089) B2516089
theorem B1814783 : Blo 1490065 1814783 := bstep (se 1 (by rfl) ⟨1361087, by rfl⟩ : syracuseStep 1814783 = 2722175) B2722175
theorem B11325743 : Blo 1490065 11325743 := bstep (se 1 (by rfl) ⟨8494307, by rfl⟩ : syracuseStep 11325743 = 16988615) B16988615
theorem B10195267 : Blo 1490065 10195267 := bstep (se 1 (by rfl) ⟨7646450, by rfl⟩ : syracuseStep 10195267 = 15292901) B15292901
theorem B3355163 : Blo 1490065 3355163 := bstep (se 1 (by rfl) ⟨2516372, by rfl⟩ : syracuseStep 3355163 = 5032745) B5032745
theorem B5034527 : Blo 1490065 5034527 := bstep (se 1 (by rfl) ⟨3775895, by rfl⟩ : syracuseStep 5034527 = 7551791) B7551791
theorem B25465427 : Blo 1490065 25465427 := bstep (se 1 (by rfl) ⟨19099070, by rfl⟩ : syracuseStep 25465427 = 38198141) B38198141
theorem B3355343 : Blo 1490065 3355343 := bstep (se 1 (by rfl) ⟨2516507, by rfl⟩ : syracuseStep 3355343 = 5033015) B5033015
theorem B3928937 : Blo 1490065 3928937 := bstep (se 2 (by rfl) ⟨1473351, by rfl⟩ : syracuseStep 3928937 = 2946703) B2946703
theorem B17224559 : Blo 1490065 17224559 := bstep (se 1 (by rfl) ⟨12918419, by rfl⟩ : syracuseStep 17224559 = 25836839) B25836839
theorem B5034959 : Blo 1490065 5034959 := bstep (se 1 (by rfl) ⟨3776219, by rfl⟩ : syracuseStep 5034959 = 7552439) B7552439
theorem B1676479 : Blo 1490065 1676479 := bstep (se 1 (by rfl) ⟨1257359, by rfl⟩ : syracuseStep 1676479 = 2514719) B2514719
theorem B11326715 : Blo 1490065 11326715 := bstep (se 1 (by rfl) ⟨8495036, by rfl⟩ : syracuseStep 11326715 = 16990073) B16990073
theorem B12735791 : Blo 1490065 12735791 := bstep (se 1 (by rfl) ⟨9551843, by rfl⟩ : syracuseStep 12735791 = 19103687) B19103687
theorem B5035337 : Blo 1490065 5035337 := bstep (se 2 (by rfl) ⟨1888251, by rfl⟩ : syracuseStep 5035337 = 3776503) B3776503
theorem B1676623 : Blo 1490065 1676623 := bstep (se 1 (by rfl) ⟨1257467, by rfl⟩ : syracuseStep 1676623 = 2514935) B2514935
theorem B19355041 : Blo 1490065 19355041 := bstep (se 2 (by rfl) ⟨7258140, by rfl⟩ : syracuseStep 19355041 = 14516281) B14516281
theorem B1676767 : Blo 1490065 1676767 := bstep (se 1 (by rfl) ⟨1257575, by rfl⟩ : syracuseStep 1676767 = 2515151) B2515151
theorem B3356135 : Blo 1490065 3356135 := bstep (se 1 (by rfl) ⟨2517101, by rfl⟩ : syracuseStep 3356135 = 5034203) B5034203
theorem B77518397 : Blo 1490065 77518397 := bstep (se 3 (by rfl) ⟨14534699, by rfl⟩ : syracuseStep 77518397 = 29069399) B29069399
theorem B3356315 : Blo 1490065 3356315 := bstep (se 1 (by rfl) ⟨2517236, by rfl⟩ : syracuseStep 3356315 = 5034473) B5034473
theorem B3356513 : Blo 1490065 3356513 := bstep (se 2 (by rfl) ⟨1258692, by rfl⟩ : syracuseStep 3356513 = 2517385) B2517385
theorem B1677343 : Blo 1490065 1677343 := bstep (se 1 (by rfl) ⟨1258007, by rfl⟩ : syracuseStep 1677343 = 2516015) B2516015
theorem B11319425 : Blo 1490065 11319425 := bstep (se 2 (by rfl) ⟨4244784, by rfl⟩ : syracuseStep 11319425 = 8489569) B8489569
theorem B15308993 : Blo 1490065 15308993 := bstep (se 2 (by rfl) ⟨5740872, by rfl⟩ : syracuseStep 15308993 = 11481745) B11481745
theorem B9190025 : Blo 1490065 9190025 := bstep (se 2 (by rfl) ⟨3446259, by rfl⟩ : syracuseStep 9190025 = 6892519) B6892519
theorem B81615559 : Blo 1490065 81615559 := bstep (se 1 (by rfl) ⟨61211669, by rfl⟩ : syracuseStep 81615559 = 122423339) B122423339
theorem B4537057 : Blo 1490065 4537057 := bstep (se 2 (by rfl) ⟨1701396, by rfl⟩ : syracuseStep 4537057 = 3402793) B3402793
theorem B5659379 : Blo 1490065 5659379 := bstep (se 1 (by rfl) ⟨4244534, by rfl⟩ : syracuseStep 5659379 = 8489069) B8489069
theorem B2235131 : Blo 1490065 2235131 := bstep (se 1 (by rfl) ⟨1676348, by rfl⟩ : syracuseStep 2235131 = 3352697) B3352697
theorem B4774717 : Blo 1490065 4774717 := bstep (se 3 (by rfl) ⟨895259, by rfl⟩ : syracuseStep 4774717 = 1790519) B1790519
theorem B2235257 : Blo 1490065 2235257 := bstep (se 2 (by rfl) ⟨838221, by rfl⟩ : syracuseStep 2235257 = 1676443) B1676443
theorem B2014075 : Blo 1490065 2014075 := bstep (se 1 (by rfl) ⟨1510556, by rfl⟩ : syracuseStep 2014075 = 3021113) B3021113
theorem B16128989 : Blo 1490065 16128989 := bstep (se 3 (by rfl) ⟨3024185, by rfl⟩ : syracuseStep 16128989 = 6048371) B6048371
theorem B3775481 : Blo 1490065 3775481 := bstep (se 2 (by rfl) ⟨1415805, by rfl⟩ : syracuseStep 3775481 = 2831611) B2831611
theorem B64470437 : Blo 1490065 64470437 := bstep (se 4 (by rfl) ⟨6044103, by rfl⟩ : syracuseStep 64470437 = 12088207) B12088207
theorem B1490399 : Blo 1490065 1490399 := bstep (se 1 (by rfl) ⟨1117799, by rfl⟩ : syracuseStep 1490399 = 2235599) B2235599
theorem B48348677 : Blo 1490065 48348677 := bstep (se 4 (by rfl) ⟨4532688, by rfl⟩ : syracuseStep 48348677 = 9065377) B9065377
theorem B1490479 : Blo 1490065 1490479 := bstep (se 1 (by rfl) ⟨1117859, by rfl⟩ : syracuseStep 1490479 = 2235719) B2235719
theorem B2236007 : Blo 1490065 2236007 := bstep (se 1 (by rfl) ⟨1677005, by rfl⟩ : syracuseStep 2236007 = 3354011) B3354011
theorem B3776129 : Blo 1490065 3776129 := bstep (se 2 (by rfl) ⟨1416048, by rfl⟩ : syracuseStep 3776129 = 2832097) B2832097
theorem B1490587 : Blo 1490065 1490587 := bstep (se 1 (by rfl) ⟨1117940, by rfl⟩ : syracuseStep 1490587 = 2235881) B2235881
theorem B1490683 : Blo 1490065 1490683 := bstep (se 1 (by rfl) ⟨1118012, by rfl⟩ : syracuseStep 1490683 = 2236025) B2236025
theorem B7552763 : Blo 1490065 7552763 := bstep (se 1 (by rfl) ⟨5664572, by rfl⟩ : syracuseStep 7552763 = 11329145) B11329145
theorem B2236169 : Blo 1490065 2236169 := bstep (se 2 (by rfl) ⟨838563, by rfl⟩ : syracuseStep 2236169 = 1677127) B1677127
theorem B1490847 : Blo 1490065 1490847 := bstep (se 1 (by rfl) ⟨1118135, by rfl⟩ : syracuseStep 1490847 = 2236271) B2236271
theorem B2236391 : Blo 1490065 2236391 := bstep (se 1 (by rfl) ⟨1677293, by rfl⟩ : syracuseStep 2236391 = 3354587) B3354587
theorem B2236457 : Blo 1490065 2236457 := bstep (se 2 (by rfl) ⟨838671, by rfl⟩ : syracuseStep 2236457 = 1677343) B1677343
theorem B1491007 : Blo 1490065 1491007 := bstep (se 1 (by rfl) ⟨1118255, by rfl⟩ : syracuseStep 1491007 = 2236511) B2236511
theorem B6045779 : Blo 1490065 6045779 := bstep (se 1 (by rfl) ⟨4534334, by rfl⟩ : syracuseStep 6045779 = 9068669) B9068669
theorem B1491047 : Blo 1490065 1491047 := bstep (se 1 (by rfl) ⟨1118285, by rfl⟩ : syracuseStep 1491047 = 2236571) B2236571
theorem B2236523 : Blo 1490065 2236523 := bstep (se 1 (by rfl) ⟨1677392, by rfl⟩ : syracuseStep 2236523 = 3354785) B3354785
theorem B1491103 : Blo 1490065 1491103 := bstep (se 1 (by rfl) ⟨1118327, by rfl⟩ : syracuseStep 1491103 = 2236655) B2236655
theorem B2236775 : Blo 1490065 2236775 := bstep (se 1 (by rfl) ⟨1677581, by rfl⟩ : syracuseStep 2236775 = 3355163) B3355163
theorem B5661049 : Blo 1490065 5661049 := bstep (se 2 (by rfl) ⟨2122893, by rfl⟩ : syracuseStep 5661049 = 4245787) B4245787
theorem B27222409 : Blo 1490065 27222409 := bstep (se 2 (by rfl) ⟨10208403, by rfl⟩ : syracuseStep 27222409 = 20416807) B20416807
theorem B1491355 : Blo 1490065 1491355 := bstep (se 1 (by rfl) ⟨1118516, by rfl⟩ : syracuseStep 1491355 = 2237033) B2237033
theorem B1491359 : Blo 1490065 1491359 := bstep (se 1 (by rfl) ⟨1118519, by rfl⟩ : syracuseStep 1491359 = 2237039) B2237039
theorem B2236895 : Blo 1490065 2236895 := bstep (se 1 (by rfl) ⟨1677671, by rfl⟩ : syracuseStep 2236895 = 3355343) B3355343
theorem B1491775 : Blo 1490065 1491775 := bstep (se 1 (by rfl) ⟨1118831, by rfl⟩ : syracuseStep 1491775 = 2237663) B2237663
theorem B1491935 : Blo 1490065 1491935 := bstep (se 1 (by rfl) ⟨1118951, by rfl⟩ : syracuseStep 1491935 = 2237903) B2237903
theorem B2237423 : Blo 1490065 2237423 := bstep (se 1 (by rfl) ⟨1678067, by rfl⟩ : syracuseStep 2237423 = 3356135) B3356135
theorem B2688071 : Blo 1490065 2688071 := bstep (se 1 (by rfl) ⟨2016053, by rfl⟩ : syracuseStep 2688071 = 4032107) B4032107
theorem B6366289 : Blo 1490065 6366289 := bstep (se 2 (by rfl) ⟨2387358, by rfl⟩ : syracuseStep 6366289 = 4774717) B4774717
theorem B1492059 : Blo 1490065 1492059 := bstep (se 1 (by rfl) ⟨1119044, by rfl⟩ : syracuseStep 1492059 = 2238089) B2238089
theorem B2237543 : Blo 1490065 2237543 := bstep (se 1 (by rfl) ⟨1678157, by rfl⟩ : syracuseStep 2237543 = 3356315) B3356315
theorem B12092591 : Blo 1490065 12092591 := bstep (se 1 (by rfl) ⟨9069443, by rfl⟩ : syracuseStep 12092591 = 18138887) B18138887
theorem B2237675 : Blo 1490065 2237675 := bstep (se 1 (by rfl) ⟨1678256, by rfl⟩ : syracuseStep 2237675 = 3356513) B3356513
theorem B7546283 : Blo 1490065 7546283 := bstep (se 1 (by rfl) ⟨5659712, by rfl⟩ : syracuseStep 7546283 = 11319425) B11319425
theorem B5031719 : Blo 1490065 5031719 := bstep (se 1 (by rfl) ⟨3773789, by rfl⟩ : syracuseStep 5031719 = 7547579) B7547579
theorem B87148331 : Blo 1490065 87148331 := bstep (se 1 (by rfl) ⟨65361248, by rfl⟩ : syracuseStep 87148331 = 130722497) B130722497
theorem B25806721 : Blo 1490065 25806721 := bstep (se 2 (by rfl) ⟨9677520, by rfl⟩ : syracuseStep 25806721 = 19355041) B19355041
theorem B10741733 : Blo 1490065 10741733 := bstep (se 4 (by rfl) ⟨1007037, by rfl⟩ : syracuseStep 10741733 = 2014075) B2014075
theorem B2516987 : Blo 1490065 2516987 := bstep (se 1 (by rfl) ⟨1887740, by rfl⟩ : syracuseStep 2516987 = 3775481) B3775481
theorem B8063219 : Blo 1490065 8063219 := bstep (se 1 (by rfl) ⟨6047414, by rfl⟩ : syracuseStep 8063219 = 12094829) B12094829
theorem B2517419 : Blo 1490065 2517419 := bstep (se 1 (by rfl) ⟨1888064, by rfl⟩ : syracuseStep 2517419 = 3776129) B3776129
theorem B5663465 : Blo 1490065 5663465 := bstep (se 2 (by rfl) ⟨2123799, by rfl⟩ : syracuseStep 5663465 = 4247599) B4247599
theorem B6367997 : Blo 1490065 6367997 := bstep (se 3 (by rfl) ⟨1193999, by rfl⟩ : syracuseStep 6367997 = 2387999) B2387999
theorem B11316023 : Blo 1490065 11316023 := bstep (se 1 (by rfl) ⟨8487017, by rfl⟩ : syracuseStep 11316023 = 16974035) B16974035
theorem B16976951 : Blo 1490065 16976951 := bstep (se 1 (by rfl) ⟨12732713, by rfl⟩ : syracuseStep 16976951 = 25465427) B25465427
theorem B13593689 : Blo 1490065 13593689 := bstep (se 2 (by rfl) ⟨5097633, by rfl⟩ : syracuseStep 13593689 = 10195267) B10195267
theorem B3353939 : Blo 1490065 3353939 := bstep (se 1 (by rfl) ⟨2515454, by rfl⟩ : syracuseStep 3353939 = 5030909) B5030909
theorem B8490527 : Blo 1490065 8490527 := bstep (se 1 (by rfl) ⟨6367895, by rfl⟩ : syracuseStep 8490527 = 12735791) B12735791
theorem B3354191 : Blo 1490065 3354191 := bstep (se 1 (by rfl) ⟨2515643, by rfl⟩ : syracuseStep 3354191 = 5031287) B5031287
theorem B6049409 : Blo 1490065 6049409 := bstep (se 2 (by rfl) ⟨2268528, by rfl⟩ : syracuseStep 6049409 = 4537057) B4537057
theorem B51678931 : Blo 1490065 51678931 := bstep (se 1 (by rfl) ⟨38759198, by rfl⟩ : syracuseStep 51678931 = 77518397) B77518397
theorem B4534139 : Blo 1490065 4534139 := bstep (se 1 (by rfl) ⟨3400604, by rfl⟩ : syracuseStep 4534139 = 6801209) B6801209
theorem B6369263 : Blo 1490065 6369263 := bstep (se 1 (by rfl) ⟨4776947, by rfl⟩ : syracuseStep 6369263 = 9553895) B9553895
theorem B2830457 : Blo 1490065 2830457 := bstep (se 2 (by rfl) ⟨1061421, by rfl⟩ : syracuseStep 2830457 = 2122843) B2122843
theorem B12087431 : Blo 1490065 12087431 := bstep (se 1 (by rfl) ⟨9065573, by rfl⟩ : syracuseStep 12087431 = 18131147) B18131147
theorem B8057075 : Blo 1490065 8057075 := bstep (se 1 (by rfl) ⟨6042806, by rfl⟩ : syracuseStep 8057075 = 12085613) B12085613
theorem B3354911 : Blo 1490065 3354911 := bstep (se 1 (by rfl) ⟨2516183, by rfl⟩ : syracuseStep 3354911 = 5032367) B5032367
theorem B3182905 : Blo 1490065 3182905 := bstep (se 2 (by rfl) ⟨1193589, by rfl⟩ : syracuseStep 3182905 = 2387179) B2387179
theorem B3772919 : Blo 1490065 3772919 := bstep (se 1 (by rfl) ⟨2829689, by rfl⟩ : syracuseStep 3772919 = 5659379) B5659379
theorem B11629165 : Blo 1490065 11629165 := bstep (se 3 (by rfl) ⟨2180468, by rfl⟩ : syracuseStep 11629165 = 4360937) B4360937
theorem B10752659 : Blo 1490065 10752659 := bstep (se 1 (by rfl) ⟨8064494, by rfl⟩ : syracuseStep 10752659 = 16128989) B16128989
theorem B42980291 : Blo 1490065 42980291 := bstep (se 1 (by rfl) ⟨32235218, by rfl⟩ : syracuseStep 42980291 = 64470437) B64470437
theorem B3355631 : Blo 1490065 3355631 := bstep (se 1 (by rfl) ⟨2516723, by rfl⟩ : syracuseStep 3355631 = 5033447) B5033447
theorem B32232451 : Blo 1490065 32232451 := bstep (se 1 (by rfl) ⟨24174338, by rfl⟩ : syracuseStep 32232451 = 48348677) B48348677
theorem B5035175 : Blo 1490065 5035175 := bstep (se 1 (by rfl) ⟨3776381, by rfl⟩ : syracuseStep 5035175 = 7552763) B7552763
theorem B6370663 : Blo 1490065 6370663 := bstep (se 1 (by rfl) ⟨4777997, by rfl⟩ : syracuseStep 6370663 = 9555995) B9555995
theorem B7550495 : Blo 1490065 7550495 := bstep (se 1 (by rfl) ⟨5662871, by rfl⟩ : syracuseStep 7550495 = 11325743) B11325743
theorem B3356351 : Blo 1490065 3356351 := bstep (se 1 (by rfl) ⟨2517263, by rfl⟩ : syracuseStep 3356351 = 5034527) B5034527
theorem B11483039 : Blo 1490065 11483039 := bstep (se 1 (by rfl) ⟨8612279, by rfl⟩ : syracuseStep 11483039 = 17224559) B17224559
theorem B3356639 : Blo 1490065 3356639 := bstep (se 1 (by rfl) ⟨2517479, by rfl⟩ : syracuseStep 3356639 = 5034959) B5034959
theorem B4839421 : Blo 1490065 4839421 := bstep (se 3 (by rfl) ⟨907391, by rfl⟩ : syracuseStep 4839421 = 1814783) B1814783
theorem B3184751 : Blo 1490065 3184751 := bstep (se 1 (by rfl) ⟨2388563, by rfl⟩ : syracuseStep 3184751 = 4777127) B4777127
theorem B7551143 : Blo 1490065 7551143 := bstep (se 1 (by rfl) ⟨5663357, by rfl⟩ : syracuseStep 7551143 = 11326715) B11326715
theorem B3356891 : Blo 1490065 3356891 := bstep (se 1 (by rfl) ⟨2517668, by rfl⟩ : syracuseStep 3356891 = 5035337) B5035337
theorem B108820745 : Blo 1490065 108820745 := bstep (se 2 (by rfl) ⟨40807779, by rfl⟩ : syracuseStep 108820745 = 81615559) B81615559
theorem B1677595 : Blo 1490065 1677595 := bstep (se 1 (by rfl) ⟨1258196, by rfl⟩ : syracuseStep 1677595 = 2516393) B2516393
theorem B3357089 : Blo 1490065 3357089 := bstep (se 2 (by rfl) ⟨1258908, by rfl⟩ : syracuseStep 3357089 = 2517817) B2517817
theorem B41908661 : Blo 1490065 41908661 := bstep (se 5 (by rfl) ⟨1964468, by rfl⟩ : syracuseStep 41908661 = 3928937) B3928937
theorem B10205995 : Blo 1490065 10205995 := bstep (se 1 (by rfl) ⟨7654496, by rfl⟩ : syracuseStep 10205995 = 15308993) B15308993
theorem B2235239 : Blo 1490065 2235239 := bstep (se 1 (by rfl) ⟨1676429, by rfl⟩ : syracuseStep 2235239 = 3352859) B3352859
theorem B29055851 : Blo 1490065 29055851 := bstep (se 1 (by rfl) ⟨21791888, by rfl⟩ : syracuseStep 29055851 = 43583777) B43583777
theorem B17439623 : Blo 1490065 17439623 := bstep (se 1 (by rfl) ⟨13079717, by rfl⟩ : syracuseStep 17439623 = 26159435) B26159435
theorem B2235305 : Blo 1490065 2235305 := bstep (se 2 (by rfl) ⟨838239, by rfl⟩ : syracuseStep 2235305 = 1676479) B1676479
theorem B6126683 : Blo 1490065 6126683 := bstep (se 1 (by rfl) ⟨4595012, by rfl⟩ : syracuseStep 6126683 = 9190025) B9190025
theorem B2235497 : Blo 1490065 2235497 := bstep (se 2 (by rfl) ⟨838311, by rfl⟩ : syracuseStep 2235497 = 1676623) B1676623
theorem B1490087 : Blo 1490065 1490087 := bstep (se 1 (by rfl) ⟨1117565, by rfl⟩ : syracuseStep 1490087 = 2235131) B2235131
theorem B1490171 : Blo 1490065 1490171 := bstep (se 1 (by rfl) ⟨1117628, by rfl⟩ : syracuseStep 1490171 = 2235257) B2235257
theorem B2235689 : Blo 1490065 2235689 := bstep (se 2 (by rfl) ⟨838383, by rfl⟩ : syracuseStep 2235689 = 1676767) B1676767
theorem B7544339 : Blo 1490065 7544339 := bstep (se 1 (by rfl) ⟨5658254, by rfl⟩ : syracuseStep 7544339 = 11316509) B11316509
theorem B7552601 : Blo 1490065 7552601 := bstep (se 2 (by rfl) ⟨2832225, by rfl⟩ : syracuseStep 7552601 = 5664451) B5664451
theorem B1490671 : Blo 1490065 1490671 := bstep (se 1 (by rfl) ⟨1118003, by rfl⟩ : syracuseStep 1490671 = 2236007) B2236007
theorem B1490779 : Blo 1490065 1490779 := bstep (se 1 (by rfl) ⟨1118084, by rfl⟩ : syracuseStep 1490779 = 2236169) B2236169
theorem B2015113 : Blo 1490065 2015113 := bstep (se 2 (by rfl) ⟨755667, by rfl⟩ : syracuseStep 2015113 = 1511335) B1511335
theorem B1490927 : Blo 1490065 1490927 := bstep (se 1 (by rfl) ⟨1118195, by rfl⟩ : syracuseStep 1490927 = 2236391) B2236391
theorem B1490971 : Blo 1490065 1490971 := bstep (se 1 (by rfl) ⟨1118228, by rfl⟩ : syracuseStep 1490971 = 2236457) B2236457
theorem B4030519 : Blo 1490065 4030519 := bstep (se 1 (by rfl) ⟨3022889, by rfl⟩ : syracuseStep 4030519 = 6045779) B6045779
theorem B1491015 : Blo 1490065 1491015 := bstep (se 1 (by rfl) ⟨1118261, by rfl⟩ : syracuseStep 1491015 = 2236523) B2236523
theorem B7168189 : Blo 1490065 7168189 := bstep (se 3 (by rfl) ⟨1344035, by rfl⟩ : syracuseStep 7168189 = 2688071) B2688071
theorem B2236607 : Blo 1490065 2236607 := bstep (se 1 (by rfl) ⟨1677455, by rfl⟩ : syracuseStep 2236607 = 3354911) B3354911
theorem B1491183 : Blo 1490065 1491183 := bstep (se 1 (by rfl) ⟨1118387, by rfl⟩ : syracuseStep 1491183 = 2236775) B2236775
theorem B1491263 : Blo 1490065 1491263 := bstep (se 1 (by rfl) ⟨1118447, by rfl⟩ : syracuseStep 1491263 = 2236895) B2236895
theorem B2515279 : Blo 1490065 2515279 := bstep (se 1 (by rfl) ⟨1886459, by rfl⟩ : syracuseStep 2515279 = 3772919) B3772919
theorem B2236793 : Blo 1490065 2236793 := bstep (se 2 (by rfl) ⟨838797, by rfl⟩ : syracuseStep 2236793 = 1677595) B1677595
theorem B7168439 : Blo 1490065 7168439 := bstep (se 1 (by rfl) ⟨5376329, by rfl⟩ : syracuseStep 7168439 = 10752659) B10752659
theorem B2237087 : Blo 1490065 2237087 := bstep (se 1 (by rfl) ⟨1677815, by rfl⟩ : syracuseStep 2237087 = 3355631) B3355631
theorem B1491615 : Blo 1490065 1491615 := bstep (se 1 (by rfl) ⟨1118711, by rfl⟩ : syracuseStep 1491615 = 2237423) B2237423
theorem B1491695 : Blo 1490065 1491695 := bstep (se 1 (by rfl) ⟨1118771, by rfl⟩ : syracuseStep 1491695 = 2237543) B2237543
theorem B8061727 : Blo 1490065 8061727 := bstep (se 1 (by rfl) ⟨6046295, by rfl⟩ : syracuseStep 8061727 = 12092591) B12092591
theorem B1491783 : Blo 1490065 1491783 := bstep (se 1 (by rfl) ⟨1118837, by rfl⟩ : syracuseStep 1491783 = 2237675) B2237675
theorem B5030855 : Blo 1490065 5030855 := bstep (se 1 (by rfl) ⟨3773141, by rfl⟩ : syracuseStep 5030855 = 7546283) B7546283
theorem B13607993 : Blo 1490065 13607993 := bstep (se 2 (by rfl) ⟨5102997, by rfl⟩ : syracuseStep 13607993 = 10205995) B10205995
theorem B2237567 : Blo 1490065 2237567 := bstep (se 1 (by rfl) ⟨1678175, by rfl⟩ : syracuseStep 2237567 = 3356351) B3356351
theorem B58098887 : Blo 1490065 58098887 := bstep (se 1 (by rfl) ⟨43574165, by rfl⟩ : syracuseStep 58098887 = 87148331) B87148331
theorem B2237759 : Blo 1490065 2237759 := bstep (se 1 (by rfl) ⟨1678319, by rfl⟩ : syracuseStep 2237759 = 3356639) B3356639
theorem B7161155 : Blo 1490065 7161155 := bstep (se 1 (by rfl) ⟨5370866, by rfl⟩ : syracuseStep 7161155 = 10741733) B10741733
theorem B42976601 : Blo 1490065 42976601 := bstep (se 2 (by rfl) ⟨16116225, by rfl⟩ : syracuseStep 42976601 = 32232451) B32232451
theorem B2123167 : Blo 1490065 2123167 := bstep (se 1 (by rfl) ⟨1592375, by rfl⟩ : syracuseStep 2123167 = 3184751) B3184751
theorem B8488385 : Blo 1490065 8488385 := bstep (se 2 (by rfl) ⟨3183144, by rfl⟩ : syracuseStep 8488385 = 6366289) B6366289
theorem B2237927 : Blo 1490065 2237927 := bstep (se 1 (by rfl) ⟨1678445, by rfl⟩ : syracuseStep 2237927 = 3356891) B3356891
theorem B5375479 : Blo 1490065 5375479 := bstep (se 1 (by rfl) ⟨4031609, by rfl⟩ : syracuseStep 5375479 = 8063219) B8063219
theorem B2238059 : Blo 1490065 2238059 := bstep (se 1 (by rfl) ⟨1678544, by rfl⟩ : syracuseStep 2238059 = 3357089) B3357089
theorem B16975493 : Blo 1490065 16975493 := bstep (se 4 (by rfl) ⟨1591452, by rfl⟩ : syracuseStep 16975493 = 3182905) B3182905
theorem B16131757 : Blo 1490065 16131757 := bstep (se 3 (by rfl) ⟨3024704, by rfl⟩ : syracuseStep 16131757 = 6049409) B6049409
theorem B11626415 : Blo 1490065 11626415 := bstep (se 1 (by rfl) ⟨8719811, by rfl⟩ : syracuseStep 11626415 = 17439623) B17439623
theorem B9062459 : Blo 1490065 9062459 := bstep (se 1 (by rfl) ⟨6796844, by rfl⟩ : syracuseStep 9062459 = 13593689) B13593689
theorem B68905241 : Blo 1490065 68905241 := bstep (se 2 (by rfl) ⟨25839465, by rfl⟩ : syracuseStep 68905241 = 51678931) B51678931
theorem B34408961 : Blo 1490065 34408961 := bstep (se 2 (by rfl) ⟨12903360, by rfl⟩ : syracuseStep 34408961 = 25806721) B25806721
theorem B4246175 : Blo 1490065 4246175 := bstep (se 1 (by rfl) ⟨3184631, by rfl⟩ : syracuseStep 4246175 = 6369263) B6369263
theorem B1886971 : Blo 1490065 1886971 := bstep (se 1 (by rfl) ⟨1415228, by rfl⟩ : syracuseStep 1886971 = 2830457) B2830457
theorem B16337821 : Blo 1490065 16337821 := bstep (se 3 (by rfl) ⟨3063341, by rfl⟩ : syracuseStep 16337821 = 6126683) B6126683
theorem B7548065 : Blo 1490065 7548065 := bstep (se 2 (by rfl) ⟨2830524, by rfl⟩ : syracuseStep 7548065 = 5661049) B5661049
theorem B5033663 : Blo 1490065 5033663 := bstep (se 1 (by rfl) ⟨3775247, by rfl⟩ : syracuseStep 5033663 = 7550495) B7550495
theorem B3354479 : Blo 1490065 3354479 := bstep (se 1 (by rfl) ⟨2515859, by rfl⟩ : syracuseStep 3354479 = 5031719) B5031719
theorem B7655359 : Blo 1490065 7655359 := bstep (se 1 (by rfl) ⟨5741519, by rfl⟩ : syracuseStep 7655359 = 11483039) B11483039
theorem B5034095 : Blo 1490065 5034095 := bstep (se 1 (by rfl) ⟨3775571, by rfl⟩ : syracuseStep 5034095 = 7551143) B7551143
theorem B27939107 : Blo 1490065 27939107 := bstep (se 1 (by rfl) ⟨20954330, by rfl⟩ : syracuseStep 27939107 = 41908661) B41908661
theorem B19370567 : Blo 1490065 19370567 := bstep (se 1 (by rfl) ⟨14527925, by rfl⟩ : syracuseStep 19370567 = 29055851) B29055851
theorem B11317967 : Blo 1490065 11317967 := bstep (se 1 (by rfl) ⟨8488475, by rfl⟩ : syracuseStep 11317967 = 16976951) B16976951
theorem B5035067 : Blo 1490065 5035067 := bstep (se 1 (by rfl) ⟨3776300, by rfl⟩ : syracuseStep 5035067 = 7552601) B7552601
theorem B6452561 : Blo 1490065 6452561 := bstep (se 2 (by rfl) ⟨2419710, by rfl⟩ : syracuseStep 6452561 = 4839421) B4839421
theorem B8058287 : Blo 1490065 8058287 := bstep (se 1 (by rfl) ⟨6043715, by rfl⟩ : syracuseStep 8058287 = 12087431) B12087431
theorem B36296545 : Blo 1490065 36296545 := bstep (se 2 (by rfl) ⟨13611204, by rfl⟩ : syracuseStep 36296545 = 27222409) B27222409
theorem B28653527 : Blo 1490065 28653527 := bstep (se 1 (by rfl) ⟨21490145, by rfl⟩ : syracuseStep 28653527 = 42980291) B42980291
theorem B21485533 : Blo 1490065 21485533 := bstep (se 3 (by rfl) ⟨4028537, by rfl⟩ : syracuseStep 21485533 = 8057075) B8057075
theorem B3356783 : Blo 1490065 3356783 := bstep (se 1 (by rfl) ⟨2517587, by rfl⟩ : syracuseStep 3356783 = 5035175) B5035175
theorem B15505553 : Blo 1490065 15505553 := bstep (se 2 (by rfl) ⟨5814582, by rfl⟩ : syracuseStep 15505553 = 11629165) B11629165
theorem B1677991 : Blo 1490065 1677991 := bstep (se 1 (by rfl) ⟨1258493, by rfl⟩ : syracuseStep 1677991 = 2516987) B2516987
theorem B72547163 : Blo 1490065 72547163 := bstep (se 1 (by rfl) ⟨54410372, by rfl⟩ : syracuseStep 72547163 = 108820745) B108820745
theorem B1678279 : Blo 1490065 1678279 := bstep (se 1 (by rfl) ⟨1258709, by rfl⟩ : syracuseStep 1678279 = 2517419) B2517419
theorem B8494217 : Blo 1490065 8494217 := bstep (se 2 (by rfl) ⟨3185331, by rfl⟩ : syracuseStep 8494217 = 6370663) B6370663
theorem B3775643 : Blo 1490065 3775643 := bstep (se 1 (by rfl) ⟨2831732, by rfl⟩ : syracuseStep 3775643 = 5663465) B5663465
theorem B7544015 : Blo 1490065 7544015 := bstep (se 1 (by rfl) ⟨5658011, by rfl⟩ : syracuseStep 7544015 = 11316023) B11316023
theorem B1490159 : Blo 1490065 1490159 := bstep (se 1 (by rfl) ⟨1117619, by rfl⟩ : syracuseStep 1490159 = 2235239) B2235239
theorem B1490203 : Blo 1490065 1490203 := bstep (se 1 (by rfl) ⟨1117652, by rfl⟩ : syracuseStep 1490203 = 2235305) B2235305
theorem B16981325 : Blo 1490065 16981325 := bstep (se 3 (by rfl) ⟨3183998, by rfl⟩ : syracuseStep 16981325 = 6367997) B6367997
theorem B1490331 : Blo 1490065 1490331 := bstep (se 1 (by rfl) ⟨1117748, by rfl⟩ : syracuseStep 1490331 = 2235497) B2235497
theorem B1490459 : Blo 1490065 1490459 := bstep (se 1 (by rfl) ⟨1117844, by rfl⟩ : syracuseStep 1490459 = 2235689) B2235689
theorem B2235959 : Blo 1490065 2235959 := bstep (se 1 (by rfl) ⟨1676969, by rfl⟩ : syracuseStep 2235959 = 3353939) B3353939
theorem B5029559 : Blo 1490065 5029559 := bstep (se 1 (by rfl) ⟨3772169, by rfl⟩ : syracuseStep 5029559 = 7544339) B7544339
theorem B5660351 : Blo 1490065 5660351 := bstep (se 1 (by rfl) ⟨4245263, by rfl⟩ : syracuseStep 5660351 = 8490527) B8490527
theorem B2236127 : Blo 1490065 2236127 := bstep (se 1 (by rfl) ⟨1677095, by rfl⟩ : syracuseStep 2236127 = 3354191) B3354191
theorem B2686817 : Blo 1490065 2686817 := bstep (se 2 (by rfl) ⟨1007556, by rfl⟩ : syracuseStep 2686817 = 2015113) B2015113
theorem B3022759 : Blo 1490065 3022759 := bstep (se 1 (by rfl) ⟨2267069, by rfl⟩ : syracuseStep 3022759 = 4534139) B4534139
theorem B5374025 : Blo 1490065 5374025 := bstep (se 2 (by rfl) ⟨2015259, by rfl⟩ : syracuseStep 5374025 = 4030519) B4030519
theorem B1491071 : Blo 1490065 1491071 := bstep (se 1 (by rfl) ⟨1118303, by rfl⟩ : syracuseStep 1491071 = 2236607) B2236607
theorem B1491195 : Blo 1490065 1491195 := bstep (se 1 (by rfl) ⟨1118396, by rfl⟩ : syracuseStep 1491195 = 2236793) B2236793
theorem B1491391 : Blo 1490065 1491391 := bstep (se 1 (by rfl) ⟨1118543, by rfl⟩ : syracuseStep 1491391 = 2237087) B2237087
theorem B7545311 : Blo 1490065 7545311 := bstep (se 1 (by rfl) ⟨5658983, by rfl⟩ : syracuseStep 7545311 = 11317967) B11317967
theorem B1491711 : Blo 1490065 1491711 := bstep (se 1 (by rfl) ⟨1118783, by rfl⟩ : syracuseStep 1491711 = 2237567) B2237567
theorem B38732591 : Blo 1490065 38732591 := bstep (se 1 (by rfl) ⟨29049443, by rfl⟩ : syracuseStep 38732591 = 58098887) B58098887
theorem B1491839 : Blo 1490065 1491839 := bstep (se 1 (by rfl) ⟨1118879, by rfl⟩ : syracuseStep 1491839 = 2237759) B2237759
theorem B2237321 : Blo 1490065 2237321 := bstep (se 2 (by rfl) ⟨838995, by rfl⟩ : syracuseStep 2237321 = 1677991) B1677991
theorem B1491951 : Blo 1490065 1491951 := bstep (se 1 (by rfl) ⟨1118963, by rfl⟩ : syracuseStep 1491951 = 2237927) B2237927
theorem B2515961 : Blo 1490065 2515961 := bstep (se 2 (by rfl) ⟨943485, by rfl⟩ : syracuseStep 2515961 = 1886971) B1886971
theorem B10748969 : Blo 1490065 10748969 := bstep (se 2 (by rfl) ⟨4030863, by rfl⟩ : syracuseStep 10748969 = 8061727) B8061727
theorem B1492039 : Blo 1490065 1492039 := bstep (se 1 (by rfl) ⟨1119029, by rfl⟩ : syracuseStep 1492039 = 2238059) B2238059
theorem B21783761 : Blo 1490065 21783761 := bstep (se 2 (by rfl) ⟨8168910, by rfl⟩ : syracuseStep 21783761 = 16337821) B16337821
theorem B2237705 : Blo 1490065 2237705 := bstep (se 2 (by rfl) ⟨839139, by rfl⟩ : syracuseStep 2237705 = 1678279) B1678279
theorem B7750943 : Blo 1490065 7750943 := bstep (se 1 (by rfl) ⟨5813207, by rfl⟩ : syracuseStep 7750943 = 11626415) B11626415
theorem B2237855 : Blo 1490065 2237855 := bstep (se 1 (by rfl) ⟨1678391, by rfl⟩ : syracuseStep 2237855 = 3356783) B3356783
theorem B22939307 : Blo 1490065 22939307 := bstep (se 1 (by rfl) ⟨17204480, by rfl⟩ : syracuseStep 22939307 = 34408961) B34408961
theorem B5662811 : Blo 1490065 5662811 := bstep (se 1 (by rfl) ⟨4247108, by rfl⟩ : syracuseStep 5662811 = 8494217) B8494217
theorem B2517095 : Blo 1490065 2517095 := bstep (se 1 (by rfl) ⟨1887821, by rfl⟩ : syracuseStep 2517095 = 3775643) B3775643
theorem B5032043 : Blo 1490065 5032043 := bstep (se 1 (by rfl) ⟨3774032, by rfl⟩ : syracuseStep 5032043 = 7548065) B7548065
theorem B3353039 : Blo 1490065 3353039 := bstep (se 1 (by rfl) ⟨2514779, by rfl⟩ : syracuseStep 3353039 = 5029559) B5029559
theorem B41348141 : Blo 1490065 41348141 := bstep (se 3 (by rfl) ⟨7752776, by rfl⟩ : syracuseStep 41348141 = 15505553) B15505553
theorem B12913711 : Blo 1490065 12913711 := bstep (se 1 (by rfl) ⟨9685283, by rfl⟩ : syracuseStep 12913711 = 19370567) B19370567
theorem B3353705 : Blo 1490065 3353705 := bstep (se 2 (by rfl) ⟨1257639, by rfl⟩ : syracuseStep 3353705 = 2515279) B2515279
theorem B3353903 : Blo 1490065 3353903 := bstep (se 1 (by rfl) ⟨2515427, by rfl⟩ : syracuseStep 3353903 = 5030855) B5030855
theorem B9071995 : Blo 1490065 9071995 := bstep (se 1 (by rfl) ⟨6803996, by rfl⟩ : syracuseStep 9071995 = 13607993) B13607993
theorem B17206829 : Blo 1490065 17206829 := bstep (se 3 (by rfl) ⟨3226280, by rfl⟩ : syracuseStep 17206829 = 6452561) B6452561
theorem B28651067 : Blo 1490065 28651067 := bstep (se 1 (by rfl) ⟨21488300, by rfl⟩ : syracuseStep 28651067 = 42976601) B42976601
theorem B11316995 : Blo 1490065 11316995 := bstep (se 1 (by rfl) ⟨8487746, by rfl⟩ : syracuseStep 11316995 = 16975493) B16975493
theorem B19115837 : Blo 1490065 19115837 := bstep (se 3 (by rfl) ⟨3584219, by rfl⟩ : syracuseStep 19115837 = 7168439) B7168439
theorem B6041639 : Blo 1490065 6041639 := bstep (se 1 (by rfl) ⟨4531229, by rfl⟩ : syracuseStep 6041639 = 9062459) B9062459
theorem B45936827 : Blo 1490065 45936827 := bstep (se 1 (by rfl) ⟨34452620, by rfl⟩ : syracuseStep 45936827 = 68905241) B68905241
theorem B2830783 : Blo 1490065 2830783 := bstep (se 1 (by rfl) ⟨2123087, by rfl⟩ : syracuseStep 2830783 = 4246175) B4246175
theorem B2830889 : Blo 1490065 2830889 := bstep (se 2 (by rfl) ⟨1061583, by rfl⟩ : syracuseStep 2830889 = 2123167) B2123167
theorem B21509009 : Blo 1490065 21509009 := bstep (se 2 (by rfl) ⟨8065878, by rfl⟩ : syracuseStep 21509009 = 16131757) B16131757
theorem B7164845 : Blo 1490065 7164845 := bstep (se 3 (by rfl) ⟨1343408, by rfl⟩ : syracuseStep 7164845 = 2686817) B2686817
theorem B3773567 : Blo 1490065 3773567 := bstep (se 1 (by rfl) ⟨2830175, by rfl⟩ : syracuseStep 3773567 = 5660351) B5660351
theorem B3355775 : Blo 1490065 3355775 := bstep (se 1 (by rfl) ⟨2516831, by rfl⟩ : syracuseStep 3355775 = 5033663) B5033663
theorem B48395393 : Blo 1490065 48395393 := bstep (se 2 (by rfl) ⟨18148272, by rfl⟩ : syracuseStep 48395393 = 36296545) B36296545
theorem B3356063 : Blo 1490065 3356063 := bstep (se 1 (by rfl) ⟨2517047, by rfl⟩ : syracuseStep 3356063 = 5034095) B5034095
theorem B18626071 : Blo 1490065 18626071 := bstep (se 1 (by rfl) ⟨13969553, by rfl⟩ : syracuseStep 18626071 = 27939107) B27939107
theorem B9557585 : Blo 1490065 9557585 := bstep (se 2 (by rfl) ⟨3584094, by rfl⟩ : syracuseStep 9557585 = 7168189) B7168189
theorem B3356711 : Blo 1490065 3356711 := bstep (se 1 (by rfl) ⟨2517533, by rfl⟩ : syracuseStep 3356711 = 5035067) B5035067
theorem B4774103 : Blo 1490065 4774103 := bstep (se 1 (by rfl) ⟨3580577, by rfl⟩ : syracuseStep 4774103 = 7161155) B7161155
theorem B5372191 : Blo 1490065 5372191 := bstep (se 1 (by rfl) ⟨4029143, by rfl⟩ : syracuseStep 5372191 = 8058287) B8058287
theorem B5658923 : Blo 1490065 5658923 := bstep (se 1 (by rfl) ⟨4244192, by rfl⟩ : syracuseStep 5658923 = 8488385) B8488385
theorem B19102351 : Blo 1490065 19102351 := bstep (se 1 (by rfl) ⟨14326763, by rfl⟩ : syracuseStep 19102351 = 28653527) B28653527
theorem B48364775 : Blo 1490065 48364775 := bstep (se 1 (by rfl) ⟨36273581, by rfl⟩ : syracuseStep 48364775 = 72547163) B72547163
theorem B7167305 : Blo 1490065 7167305 := bstep (se 2 (by rfl) ⟨2687739, by rfl⟩ : syracuseStep 7167305 = 5375479) B5375479
theorem B5029343 : Blo 1490065 5029343 := bstep (se 1 (by rfl) ⟨3772007, by rfl⟩ : syracuseStep 5029343 = 7544015) B7544015
theorem B11320883 : Blo 1490065 11320883 := bstep (se 1 (by rfl) ⟨8490662, by rfl⟩ : syracuseStep 11320883 = 16981325) B16981325
theorem B1490639 : Blo 1490065 1490639 := bstep (se 1 (by rfl) ⟨1117979, by rfl⟩ : syracuseStep 1490639 = 2235959) B2235959
theorem B1490751 : Blo 1490065 1490751 := bstep (se 1 (by rfl) ⟨1118063, by rfl⟩ : syracuseStep 1490751 = 2236127) B2236127
theorem B4030345 : Blo 1490065 4030345 := bstep (se 2 (by rfl) ⟨1511379, by rfl⟩ : syracuseStep 4030345 = 3022759) B3022759
theorem B2236319 : Blo 1490065 2236319 := bstep (se 1 (by rfl) ⟨1677239, by rfl⟩ : syracuseStep 2236319 = 3354479) B3354479
theorem B10207145 : Blo 1490065 10207145 := bstep (se 2 (by rfl) ⟨3827679, by rfl⟩ : syracuseStep 10207145 = 7655359) B7655359
theorem B28647377 : Blo 1490065 28647377 := bstep (se 2 (by rfl) ⟨10742766, by rfl⟩ : syracuseStep 28647377 = 21485533) B21485533
theorem B5030207 : Blo 1490065 5030207 := bstep (se 1 (by rfl) ⟨3772655, by rfl⟩ : syracuseStep 5030207 = 7545311) B7545311
theorem B1491547 : Blo 1490065 1491547 := bstep (se 1 (by rfl) ⟨1118660, by rfl⟩ : syracuseStep 1491547 = 2237321) B2237321
theorem B4776563 : Blo 1490065 4776563 := bstep (se 1 (by rfl) ⟨3582422, by rfl⟩ : syracuseStep 4776563 = 7164845) B7164845
theorem B2515711 : Blo 1490065 2515711 := bstep (se 1 (by rfl) ⟨1886783, by rfl⟩ : syracuseStep 2515711 = 3773567) B3773567
theorem B2237183 : Blo 1490065 2237183 := bstep (se 1 (by rfl) ⟨1677887, by rfl⟩ : syracuseStep 2237183 = 3355775) B3355775
theorem B1491803 : Blo 1490065 1491803 := bstep (se 1 (by rfl) ⟨1118852, by rfl⟩ : syracuseStep 1491803 = 2237705) B2237705
theorem B25469801 : Blo 1490065 25469801 := bstep (se 2 (by rfl) ⟨9551175, by rfl⟩ : syracuseStep 25469801 = 19102351) B19102351
theorem B2237375 : Blo 1490065 2237375 := bstep (se 1 (by rfl) ⟨1678031, by rfl⟩ : syracuseStep 2237375 = 3356063) B3356063
theorem B1491903 : Blo 1490065 1491903 := bstep (se 1 (by rfl) ⟨1118927, by rfl⟩ : syracuseStep 1491903 = 2237855) B2237855
theorem B2237807 : Blo 1490065 2237807 := bstep (se 1 (by rfl) ⟨1678355, by rfl⟩ : syracuseStep 2237807 = 3356711) B3356711
theorem B103286909 : Blo 1490065 103286909 := bstep (se 3 (by rfl) ⟨19366295, by rfl⟩ : syracuseStep 103286909 = 38732591) B38732591
theorem B4778203 : Blo 1490065 4778203 := bstep (se 1 (by rfl) ⟨3583652, by rfl⟩ : syracuseStep 4778203 = 7167305) B7167305
theorem B3352895 : Blo 1490065 3352895 := bstep (se 1 (by rfl) ⟨2514671, by rfl⟩ : syracuseStep 3352895 = 5029343) B5029343
theorem B11471219 : Blo 1490065 11471219 := bstep (se 1 (by rfl) ⟨8603414, by rfl⟩ : syracuseStep 11471219 = 17206829) B17206829
theorem B7547255 : Blo 1490065 7547255 := bstep (se 1 (by rfl) ⟨5660441, by rfl⟩ : syracuseStep 7547255 = 11320883) B11320883
theorem B19098251 : Blo 1490065 19098251 := bstep (se 1 (by rfl) ⟨14323688, by rfl⟩ : syracuseStep 19098251 = 28647377) B28647377
theorem B3582683 : Blo 1490065 3582683 := bstep (se 1 (by rfl) ⟨2687012, by rfl⟩ : syracuseStep 3582683 = 5374025) B5374025
theorem B30624551 : Blo 1490065 30624551 := bstep (se 1 (by rfl) ⟨22968413, by rfl⟩ : syracuseStep 30624551 = 45936827) B45936827
theorem B68873125 : Blo 1490065 68873125 := bstep (se 4 (by rfl) ⟨6456855, by rfl⟩ : syracuseStep 68873125 = 12913711) B12913711
theorem B7162921 : Blo 1490065 7162921 := bstep (se 2 (by rfl) ⟨2686095, by rfl⟩ : syracuseStep 7162921 = 5372191) B5372191
theorem B14339339 : Blo 1490065 14339339 := bstep (se 1 (by rfl) ⟨10754504, by rfl⟩ : syracuseStep 14339339 = 21509009) B21509009
theorem B32263595 : Blo 1490065 32263595 := bstep (se 1 (by rfl) ⟨24197696, by rfl⟩ : syracuseStep 32263595 = 48395393) B48395393
theorem B3354695 : Blo 1490065 3354695 := bstep (se 1 (by rfl) ⟨2516021, by rfl⟩ : syracuseStep 3354695 = 5032043) B5032043
theorem B7549037 : Blo 1490065 7549037 := bstep (se 3 (by rfl) ⟨1415444, by rfl⟩ : syracuseStep 7549037 = 2830889) B2830889
theorem B3182735 : Blo 1490065 3182735 := bstep (se 1 (by rfl) ⟨2387051, by rfl⟩ : syracuseStep 3182735 = 4774103) B4774103
theorem B3772615 : Blo 1490065 3772615 := bstep (se 1 (by rfl) ⟨2829461, by rfl⟩ : syracuseStep 3772615 = 5658923) B5658923
theorem B12095993 : Blo 1490065 12095993 := bstep (se 2 (by rfl) ⟨4535997, by rfl⟩ : syracuseStep 12095993 = 9071995) B9071995
theorem B24834761 : Blo 1490065 24834761 := bstep (se 2 (by rfl) ⟨9313035, by rfl⟩ : syracuseStep 24834761 = 18626071) B18626071
theorem B19100711 : Blo 1490065 19100711 := bstep (se 1 (by rfl) ⟨14325533, by rfl⟩ : syracuseStep 19100711 = 28651067) B28651067
theorem B27219053 : Blo 1490065 27219053 := bstep (se 3 (by rfl) ⟨5103572, by rfl⟩ : syracuseStep 27219053 = 10207145) B10207145
theorem B12743891 : Blo 1490065 12743891 := bstep (se 1 (by rfl) ⟨9557918, by rfl⟩ : syracuseStep 12743891 = 19115837) B19115837
theorem B16111037 : Blo 1490065 16111037 := bstep (se 3 (by rfl) ⟨3020819, by rfl⟩ : syracuseStep 16111037 = 6041639) B6041639
theorem B3774377 : Blo 1490065 3774377 := bstep (se 2 (by rfl) ⟨1415391, by rfl⟩ : syracuseStep 3774377 = 2830783) B2830783
theorem B1677307 : Blo 1490065 1677307 := bstep (se 1 (by rfl) ⟨1257980, by rfl⟩ : syracuseStep 1677307 = 2515961) B2515961
theorem B7165979 : Blo 1490065 7165979 := bstep (se 1 (by rfl) ⟨5374484, by rfl⟩ : syracuseStep 7165979 = 10748969) B10748969
theorem B14522507 : Blo 1490065 14522507 := bstep (se 1 (by rfl) ⟨10891880, by rfl⟩ : syracuseStep 14522507 = 21783761) B21783761
theorem B5167295 : Blo 1490065 5167295 := bstep (se 1 (by rfl) ⟨3875471, by rfl⟩ : syracuseStep 5167295 = 7750943) B7750943
theorem B6371723 : Blo 1490065 6371723 := bstep (se 1 (by rfl) ⟨4778792, by rfl⟩ : syracuseStep 6371723 = 9557585) B9557585
theorem B15292871 : Blo 1490065 15292871 := bstep (se 1 (by rfl) ⟨11469653, by rfl⟩ : syracuseStep 15292871 = 22939307) B22939307
theorem B3775207 : Blo 1490065 3775207 := bstep (se 1 (by rfl) ⟨2831405, by rfl⟩ : syracuseStep 3775207 = 5662811) B5662811
theorem B1678063 : Blo 1490065 1678063 := bstep (se 1 (by rfl) ⟨1258547, by rfl⟩ : syracuseStep 1678063 = 2517095) B2517095
theorem B2235359 : Blo 1490065 2235359 := bstep (se 1 (by rfl) ⟨1676519, by rfl⟩ : syracuseStep 2235359 = 3353039) B3353039
theorem B27565427 : Blo 1490065 27565427 := bstep (se 1 (by rfl) ⟨20674070, by rfl⟩ : syracuseStep 27565427 = 41348141) B41348141
theorem B2235803 : Blo 1490065 2235803 := bstep (se 1 (by rfl) ⟨1676852, by rfl⟩ : syracuseStep 2235803 = 3353705) B3353705
theorem B32243183 : Blo 1490065 32243183 := bstep (se 1 (by rfl) ⟨24182387, by rfl⟩ : syracuseStep 32243183 = 48364775) B48364775
theorem B2235935 : Blo 1490065 2235935 := bstep (se 1 (by rfl) ⟨1676951, by rfl⟩ : syracuseStep 2235935 = 3353903) B3353903
theorem B7544663 : Blo 1490065 7544663 := bstep (se 1 (by rfl) ⟨5658497, by rfl⟩ : syracuseStep 7544663 = 11316995) B11316995
theorem B5373793 : Blo 1490065 5373793 := bstep (se 2 (by rfl) ⟨2015172, by rfl⟩ : syracuseStep 5373793 = 4030345) B4030345
theorem B1490879 : Blo 1490065 1490879 := bstep (se 1 (by rfl) ⟨1118159, by rfl⟩ : syracuseStep 1490879 = 2236319) B2236319
theorem B2236463 : Blo 1490065 2236463 := bstep (se 1 (by rfl) ⟨1677347, by rfl⟩ : syracuseStep 2236463 = 3354695) B3354695
theorem B2121823 : Blo 1490065 2121823 := bstep (se 1 (by rfl) ⟨1591367, by rfl⟩ : syracuseStep 2121823 = 3182735) B3182735
theorem B5030153 : Blo 1490065 5030153 := bstep (se 2 (by rfl) ⟨1886307, by rfl⟩ : syracuseStep 5030153 = 3772615) B3772615
theorem B16556507 : Blo 1490065 16556507 := bstep (se 1 (by rfl) ⟨12417380, by rfl⟩ : syracuseStep 16556507 = 24834761) B24834761
theorem B1491455 : Blo 1490065 1491455 := bstep (se 1 (by rfl) ⟨1118591, by rfl⟩ : syracuseStep 1491455 = 2237183) B2237183
theorem B1491583 : Blo 1490065 1491583 := bstep (se 1 (by rfl) ⟨1118687, by rfl⟩ : syracuseStep 1491583 = 2237375) B2237375
theorem B18146035 : Blo 1490065 18146035 := bstep (se 1 (by rfl) ⟨13609526, by rfl⟩ : syracuseStep 18146035 = 27219053) B27219053
theorem B8495927 : Blo 1490065 8495927 := bstep (se 1 (by rfl) ⟨6371945, by rfl⟩ : syracuseStep 8495927 = 12743891) B12743891
theorem B1491871 : Blo 1490065 1491871 := bstep (se 1 (by rfl) ⟨1118903, by rfl⟩ : syracuseStep 1491871 = 2237807) B2237807
theorem B10740691 : Blo 1490065 10740691 := bstep (se 1 (by rfl) ⟨8055518, by rfl⟩ : syracuseStep 10740691 = 16111037) B16111037
theorem B2237417 : Blo 1490065 2237417 := bstep (se 2 (by rfl) ⟨839031, by rfl⟩ : syracuseStep 2237417 = 1678063) B1678063
theorem B2516251 : Blo 1490065 2516251 := bstep (se 1 (by rfl) ⟨1887188, by rfl⟩ : syracuseStep 2516251 = 3774377) B3774377
theorem B4777319 : Blo 1490065 4777319 := bstep (se 1 (by rfl) ⟨3582989, by rfl⟩ : syracuseStep 4777319 = 7165979) B7165979
theorem B5031503 : Blo 1490065 5031503 := bstep (se 1 (by rfl) ⟨3773627, by rfl⟩ : syracuseStep 5031503 = 7547255) B7547255
theorem B12732167 : Blo 1490065 12732167 := bstep (se 1 (by rfl) ⟨9549125, by rfl⟩ : syracuseStep 12732167 = 19098251) B19098251
theorem B20416367 : Blo 1490065 20416367 := bstep (se 1 (by rfl) ⟨15312275, by rfl⟩ : syracuseStep 20416367 = 30624551) B30624551
theorem B18376951 : Blo 1490065 18376951 := bstep (se 1 (by rfl) ⟨13782713, by rfl⟩ : syracuseStep 18376951 = 27565427) B27565427
theorem B5032691 : Blo 1490065 5032691 := bstep (se 1 (by rfl) ⟨3774518, by rfl⟩ : syracuseStep 5032691 = 7549037) B7549037
theorem B3353471 : Blo 1490065 3353471 := bstep (se 1 (by rfl) ⟨2515103, by rfl⟩ : syracuseStep 3353471 = 5030207) B5030207
theorem B12733807 : Blo 1490065 12733807 := bstep (se 1 (by rfl) ⟨9550355, by rfl⟩ : syracuseStep 12733807 = 19100711) B19100711
theorem B5033609 : Blo 1490065 5033609 := bstep (se 2 (by rfl) ⟨1887603, by rfl⟩ : syracuseStep 5033609 = 3775207) B3775207
theorem B3354281 : Blo 1490065 3354281 := bstep (se 2 (by rfl) ⟨1257855, by rfl⟩ : syracuseStep 3354281 = 2515711) B2515711
theorem B32255981 : Blo 1490065 32255981 := bstep (se 3 (by rfl) ⟨6047996, by rfl⟩ : syracuseStep 32255981 = 12095993) B12095993
theorem B68857939 : Blo 1490065 68857939 := bstep (se 1 (by rfl) ⟨51643454, by rfl⟩ : syracuseStep 68857939 = 103286909) B103286909
theorem B3444863 : Blo 1490065 3444863 := bstep (se 1 (by rfl) ⟨2583647, by rfl⟩ : syracuseStep 3444863 = 5167295) B5167295
theorem B2236409 : Blo 1490065 2236409 := bstep (se 2 (by rfl) ⟨838653, by rfl⟩ : syracuseStep 2236409 = 1677307) B1677307
theorem B7647479 : Blo 1490065 7647479 := bstep (se 1 (by rfl) ⟨5735609, by rfl⟩ : syracuseStep 7647479 = 11471219) B11471219
theorem B4247815 : Blo 1490065 4247815 := bstep (se 1 (by rfl) ⟨3185861, by rfl⟩ : syracuseStep 4247815 = 6371723) B6371723
theorem B10195247 : Blo 1490065 10195247 := bstep (se 1 (by rfl) ⟨7646435, by rfl⟩ : syracuseStep 10195247 = 15292871) B15292871
theorem B2388455 : Blo 1490065 2388455 := bstep (se 1 (by rfl) ⟨1791341, by rfl⟩ : syracuseStep 2388455 = 3582683) B3582683
theorem B21509063 : Blo 1490065 21509063 := bstep (se 1 (by rfl) ⟨16131797, by rfl⟩ : syracuseStep 21509063 = 32263595) B32263595
theorem B7165057 : Blo 1490065 7165057 := bstep (se 2 (by rfl) ⟨2686896, by rfl⟩ : syracuseStep 7165057 = 5373793) B5373793
theorem B6370937 : Blo 1490065 6370937 := bstep (se 2 (by rfl) ⟨2389101, by rfl⟩ : syracuseStep 6370937 = 4778203) B4778203
theorem B3184375 : Blo 1490065 3184375 := bstep (se 1 (by rfl) ⟨2388281, by rfl⟩ : syracuseStep 3184375 = 4776563) B4776563
theorem B16979867 : Blo 1490065 16979867 := bstep (se 1 (by rfl) ⟨12734900, by rfl⟩ : syracuseStep 16979867 = 25469801) B25469801
theorem B91830833 : Blo 1490065 91830833 := bstep (se 2 (by rfl) ⟨34436562, by rfl⟩ : syracuseStep 91830833 = 68873125) B68873125
theorem B9550561 : Blo 1490065 9550561 := bstep (se 2 (by rfl) ⟨3581460, by rfl⟩ : syracuseStep 9550561 = 7162921) B7162921
theorem B9681671 : Blo 1490065 9681671 := bstep (se 1 (by rfl) ⟨7261253, by rfl⟩ : syracuseStep 9681671 = 14522507) B14522507
theorem B2235263 : Blo 1490065 2235263 := bstep (se 1 (by rfl) ⟨1676447, by rfl⟩ : syracuseStep 2235263 = 3352895) B3352895
theorem B1490239 : Blo 1490065 1490239 := bstep (se 1 (by rfl) ⟨1117679, by rfl⟩ : syracuseStep 1490239 = 2235359) B2235359
theorem B9559559 : Blo 1490065 9559559 := bstep (se 1 (by rfl) ⟨7169669, by rfl⟩ : syracuseStep 9559559 = 14339339) B14339339
theorem B1490535 : Blo 1490065 1490535 := bstep (se 1 (by rfl) ⟨1117901, by rfl⟩ : syracuseStep 1490535 = 2235803) B2235803
theorem B21495455 : Blo 1490065 21495455 := bstep (se 1 (by rfl) ⟨16121591, by rfl⟩ : syracuseStep 21495455 = 32243183) B32243183
theorem B1490623 : Blo 1490065 1490623 := bstep (se 1 (by rfl) ⟨1117967, by rfl⟩ : syracuseStep 1490623 = 2235935) B2235935
theorem B5029775 : Blo 1490065 5029775 := bstep (se 1 (by rfl) ⟨3772331, by rfl⟩ : syracuseStep 5029775 = 7544663) B7544663
theorem B1490975 : Blo 1490065 1490975 := bstep (se 1 (by rfl) ⟨1118231, by rfl⟩ : syracuseStep 1490975 = 2236463) B2236463
theorem B24502601 : Blo 1490065 24502601 := bstep (se 2 (by rfl) ⟨9188475, by rfl⟩ : syracuseStep 24502601 = 18376951) B18376951
theorem B1491611 : Blo 1490065 1491611 := bstep (se 1 (by rfl) ⟨1118708, by rfl⟩ : syracuseStep 1491611 = 2237417) B2237417
theorem B12739517 : Blo 1490065 12739517 := bstep (se 3 (by rfl) ⟨2388659, by rfl⟩ : syracuseStep 12739517 = 4777319) B4777319
theorem B8488111 : Blo 1490065 8488111 := bstep (se 1 (by rfl) ⟨6366083, by rfl⟩ : syracuseStep 8488111 = 12732167) B12732167
theorem B14320921 : Blo 1490065 14320921 := bstep (se 2 (by rfl) ⟨5370345, by rfl⟩ : syracuseStep 14320921 = 10740691) B10740691
theorem B9553409 : Blo 1490065 9553409 := bstep (se 2 (by rfl) ⟨3582528, by rfl⟩ : syracuseStep 9553409 = 7165057) B7165057
theorem B61220555 : Blo 1490065 61220555 := bstep (se 1 (by rfl) ⟨45915416, by rfl⟩ : syracuseStep 61220555 = 91830833) B91830833
theorem B4245833 : Blo 1490065 4245833 := bstep (se 2 (by rfl) ⟨1592187, by rfl⟩ : syracuseStep 4245833 = 3184375) B3184375
theorem B14330303 : Blo 1490065 14330303 := bstep (se 1 (by rfl) ⟨10747727, by rfl⟩ : syracuseStep 14330303 = 21495455) B21495455
theorem B3353183 : Blo 1490065 3353183 := bstep (se 1 (by rfl) ⟨2514887, by rfl⟩ : syracuseStep 3353183 = 5029775) B5029775
theorem B91810585 : Blo 1490065 91810585 := bstep (se 2 (by rfl) ⟨34428969, by rfl⟩ : syracuseStep 91810585 = 68857939) B68857939
theorem B2829097 : Blo 1490065 2829097 := bstep (se 2 (by rfl) ⟨1060911, by rfl⟩ : syracuseStep 2829097 = 2121823) B2121823
theorem B5098319 : Blo 1490065 5098319 := bstep (se 1 (by rfl) ⟨3823739, by rfl⟩ : syracuseStep 5098319 = 7647479) B7647479
theorem B3353435 : Blo 1490065 3353435 := bstep (se 1 (by rfl) ⟨2515076, by rfl⟩ : syracuseStep 3353435 = 5030153) B5030153
theorem B11037671 : Blo 1490065 11037671 := bstep (se 1 (by rfl) ⟨8278253, by rfl⟩ : syracuseStep 11037671 = 16556507) B16556507
theorem B1592303 : Blo 1490065 1592303 := bstep (se 1 (by rfl) ⟨1194227, by rfl⟩ : syracuseStep 1592303 = 2388455) B2388455
theorem B9186301 : Blo 1490065 9186301 := bstep (se 3 (by rfl) ⟨1722431, by rfl⟩ : syracuseStep 9186301 = 3444863) B3444863
theorem B5663753 : Blo 1490065 5663753 := bstep (se 2 (by rfl) ⟨2123907, by rfl⟩ : syracuseStep 5663753 = 4247815) B4247815
theorem B5663951 : Blo 1490065 5663951 := bstep (se 1 (by rfl) ⟨4247963, by rfl⟩ : syracuseStep 5663951 = 8495927) B8495927
theorem B14339375 : Blo 1490065 14339375 := bstep (se 1 (by rfl) ⟨10754531, by rfl⟩ : syracuseStep 14339375 = 21509063) B21509063
theorem B12734081 : Blo 1490065 12734081 := bstep (se 2 (by rfl) ⟨4775280, by rfl⟩ : syracuseStep 12734081 = 9550561) B9550561
theorem B24194713 : Blo 1490065 24194713 := bstep (se 2 (by rfl) ⟨9073017, by rfl⟩ : syracuseStep 24194713 = 18146035) B18146035
theorem B3354335 : Blo 1490065 3354335 := bstep (se 1 (by rfl) ⟨2515751, by rfl⟩ : syracuseStep 3354335 = 5031503) B5031503
theorem B4247291 : Blo 1490065 4247291 := bstep (se 1 (by rfl) ⟨3185468, by rfl⟩ : syracuseStep 4247291 = 6370937) B6370937
theorem B13610911 : Blo 1490065 13610911 := bstep (se 1 (by rfl) ⟨10208183, by rfl⟩ : syracuseStep 13610911 = 20416367) B20416367
theorem B3355001 : Blo 1490065 3355001 := bstep (se 2 (by rfl) ⟨1258125, by rfl⟩ : syracuseStep 3355001 = 2516251) B2516251
theorem B16978409 : Blo 1490065 16978409 := bstep (se 2 (by rfl) ⟨6366903, by rfl⟩ : syracuseStep 16978409 = 12733807) B12733807
theorem B3355127 : Blo 1490065 3355127 := bstep (se 1 (by rfl) ⟨2516345, by rfl⟩ : syracuseStep 3355127 = 5032691) B5032691
theorem B3355739 : Blo 1490065 3355739 := bstep (se 1 (by rfl) ⟨2516804, by rfl⟩ : syracuseStep 3355739 = 5033609) B5033609
theorem B1490939 : Blo 1490065 1490939 := bstep (se 1 (by rfl) ⟨1118204, by rfl⟩ : syracuseStep 1490939 = 2236409) B2236409
theorem B6796831 : Blo 1490065 6796831 := bstep (se 1 (by rfl) ⟨5097623, by rfl⟩ : syracuseStep 6796831 = 10195247) B10195247
theorem B11319911 : Blo 1490065 11319911 := bstep (se 1 (by rfl) ⟨8489933, by rfl⟩ : syracuseStep 11319911 = 16979867) B16979867
theorem B6454447 : Blo 1490065 6454447 := bstep (se 1 (by rfl) ⟨4840835, by rfl⟩ : syracuseStep 6454447 = 9681671) B9681671
theorem B1490175 : Blo 1490065 1490175 := bstep (se 1 (by rfl) ⟨1117631, by rfl⟩ : syracuseStep 1490175 = 2235263) B2235263
theorem B2235647 : Blo 1490065 2235647 := bstep (se 1 (by rfl) ⟨1676735, by rfl⟩ : syracuseStep 2235647 = 3353471) B3353471
theorem B6373039 : Blo 1490065 6373039 := bstep (se 1 (by rfl) ⟨4779779, by rfl⟩ : syracuseStep 6373039 = 9559559) B9559559
theorem B2236187 : Blo 1490065 2236187 := bstep (se 1 (by rfl) ⟨1677140, by rfl⟩ : syracuseStep 2236187 = 3354281) B3354281
theorem B21503987 : Blo 1490065 21503987 := bstep (se 1 (by rfl) ⟨16127990, by rfl⟩ : syracuseStep 21503987 = 32255981) B32255981
theorem B16335067 : Blo 1490065 16335067 := bstep (se 1 (by rfl) ⟨12251300, by rfl⟩ : syracuseStep 16335067 = 24502601) B24502601
theorem B2236667 : Blo 1490065 2236667 := bstep (se 1 (by rfl) ⟨1677500, by rfl⟩ : syracuseStep 2236667 = 3355001) B3355001
theorem B2236751 : Blo 1490065 2236751 := bstep (se 1 (by rfl) ⟨1677563, by rfl⟩ : syracuseStep 2236751 = 3355127) B3355127
theorem B2237159 : Blo 1490065 2237159 := bstep (se 1 (by rfl) ⟨1677869, by rfl⟩ : syracuseStep 2237159 = 3355739) B3355739
theorem B34423717 : Blo 1490065 34423717 := bstep (se 4 (by rfl) ⟨3227223, by rfl⟩ : syracuseStep 34423717 = 6454447) B6454447
theorem B122414113 : Blo 1490065 122414113 := bstep (se 2 (by rfl) ⟨45905292, by rfl⟩ : syracuseStep 122414113 = 91810585) B91810585
theorem B40813703 : Blo 1490065 40813703 := bstep (se 1 (by rfl) ⟨30610277, by rfl⟩ : syracuseStep 40813703 = 61220555) B61220555
theorem B12248401 : Blo 1490065 12248401 := bstep (se 2 (by rfl) ⟨4593150, by rfl⟩ : syracuseStep 12248401 = 9186301) B9186301
theorem B9553535 : Blo 1490065 9553535 := bstep (se 1 (by rfl) ⟨7165151, by rfl⟩ : syracuseStep 9553535 = 14330303) B14330303
theorem B7546607 : Blo 1490065 7546607 := bstep (se 1 (by rfl) ⟨5659955, by rfl⟩ : syracuseStep 7546607 = 11319911) B11319911
theorem B7358447 : Blo 1490065 7358447 := bstep (se 1 (by rfl) ⟨5518835, by rfl⟩ : syracuseStep 7358447 = 11037671) B11037671
theorem B9062441 : Blo 1490065 9062441 := bstep (se 2 (by rfl) ⟨3398415, by rfl⟩ : syracuseStep 9062441 = 6796831) B6796831
theorem B8497385 : Blo 1490065 8497385 := bstep (se 2 (by rfl) ⟨3186519, by rfl⟩ : syracuseStep 8497385 = 6373039) B6373039
theorem B8489387 : Blo 1490065 8489387 := bstep (se 1 (by rfl) ⟨6367040, by rfl⟩ : syracuseStep 8489387 = 12734081) B12734081
theorem B18147881 : Blo 1490065 18147881 := bstep (se 2 (by rfl) ⟨6805455, by rfl⟩ : syracuseStep 18147881 = 13610911) B13610911
theorem B4246141 : Blo 1490065 4246141 := bstep (se 3 (by rfl) ⟨796151, by rfl⟩ : syracuseStep 4246141 = 1592303) B1592303
theorem B6368939 : Blo 1490065 6368939 := bstep (se 1 (by rfl) ⟨4776704, by rfl⟩ : syracuseStep 6368939 = 9553409) B9553409
theorem B3772129 : Blo 1490065 3772129 := bstep (se 2 (by rfl) ⟨1414548, by rfl⟩ : syracuseStep 3772129 = 2829097) B2829097
theorem B2830555 : Blo 1490065 2830555 := bstep (se 1 (by rfl) ⟨2122916, by rfl⟩ : syracuseStep 2830555 = 4245833) B4245833
theorem B11317481 : Blo 1490065 11317481 := bstep (se 2 (by rfl) ⟨4244055, by rfl⟩ : syracuseStep 11317481 = 8488111) B8488111
theorem B2831527 : Blo 1490065 2831527 := bstep (se 1 (by rfl) ⟨2123645, by rfl⟩ : syracuseStep 2831527 = 4247291) B4247291
theorem B14335991 : Blo 1490065 14335991 := bstep (se 1 (by rfl) ⟨10751993, by rfl⟩ : syracuseStep 14335991 = 21503987) B21503987
theorem B11318939 : Blo 1490065 11318939 := bstep (se 1 (by rfl) ⟨8489204, by rfl⟩ : syracuseStep 11318939 = 16978409) B16978409
theorem B8493011 : Blo 1490065 8493011 := bstep (se 1 (by rfl) ⟨6369758, by rfl⟩ : syracuseStep 8493011 = 12739517) B12739517
theorem B19094561 : Blo 1490065 19094561 := bstep (se 2 (by rfl) ⟨7160460, by rfl⟩ : syracuseStep 19094561 = 14320921) B14320921
theorem B2235455 : Blo 1490065 2235455 := bstep (se 1 (by rfl) ⟨1676591, by rfl⟩ : syracuseStep 2235455 = 3353183) B3353183
theorem B3398879 : Blo 1490065 3398879 := bstep (se 1 (by rfl) ⟨2549159, by rfl⟩ : syracuseStep 3398879 = 5098319) B5098319
theorem B2235623 : Blo 1490065 2235623 := bstep (se 1 (by rfl) ⟨1676717, by rfl⟩ : syracuseStep 2235623 = 3353435) B3353435
theorem B3775835 : Blo 1490065 3775835 := bstep (se 1 (by rfl) ⟨2831876, by rfl⟩ : syracuseStep 3775835 = 5663753) B5663753
theorem B3775967 : Blo 1490065 3775967 := bstep (se 1 (by rfl) ⟨2831975, by rfl⟩ : syracuseStep 3775967 = 5663951) B5663951
theorem B1490431 : Blo 1490065 1490431 := bstep (se 1 (by rfl) ⟨1117823, by rfl⟩ : syracuseStep 1490431 = 2235647) B2235647
theorem B32259617 : Blo 1490065 32259617 := bstep (se 2 (by rfl) ⟨12097356, by rfl⟩ : syracuseStep 32259617 = 24194713) B24194713
theorem B9559583 : Blo 1490065 9559583 := bstep (se 1 (by rfl) ⟨7169687, by rfl⟩ : syracuseStep 9559583 = 14339375) B14339375
theorem B2236223 : Blo 1490065 2236223 := bstep (se 1 (by rfl) ⟨1677167, by rfl⟩ : syracuseStep 2236223 = 3354335) B3354335
theorem B1490791 : Blo 1490065 1490791 := bstep (se 1 (by rfl) ⟨1118093, by rfl⟩ : syracuseStep 1490791 = 2236187) B2236187
theorem B7544987 : Blo 1490065 7544987 := bstep (se 1 (by rfl) ⟨5658740, by rfl⟩ : syracuseStep 7544987 = 11317481) B11317481
theorem B1491111 : Blo 1490065 1491111 := bstep (se 1 (by rfl) ⟨1118333, by rfl⟩ : syracuseStep 1491111 = 2236667) B2236667
theorem B1491167 : Blo 1490065 1491167 := bstep (se 1 (by rfl) ⟨1118375, by rfl⟩ : syracuseStep 1491167 = 2236751) B2236751
theorem B1491439 : Blo 1490065 1491439 := bstep (se 1 (by rfl) ⟨1118579, by rfl⟩ : syracuseStep 1491439 = 2237159) B2237159
theorem B5661521 : Blo 1490065 5661521 := bstep (se 2 (by rfl) ⟨2123070, by rfl⟩ : syracuseStep 5661521 = 4246141) B4246141
theorem B7545959 : Blo 1490065 7545959 := bstep (se 1 (by rfl) ⟨5659469, by rfl⟩ : syracuseStep 7545959 = 11318939) B11318939
theorem B5031071 : Blo 1490065 5031071 := bstep (se 1 (by rfl) ⟨3773303, by rfl⟩ : syracuseStep 5031071 = 7546607) B7546607
theorem B5662007 : Blo 1490065 5662007 := bstep (se 1 (by rfl) ⟨4246505, by rfl⟩ : syracuseStep 5662007 = 8493011) B8493011
theorem B163218817 : Blo 1490065 163218817 := bstep (se 2 (by rfl) ⟨61207056, by rfl⟩ : syracuseStep 163218817 = 122414113) B122414113
theorem B2517223 : Blo 1490065 2517223 := bstep (se 1 (by rfl) ⟨1887917, by rfl⟩ : syracuseStep 2517223 = 3775835) B3775835
theorem B2517311 : Blo 1490065 2517311 := bstep (se 1 (by rfl) ⟨1887983, by rfl⟩ : syracuseStep 2517311 = 3775967) B3775967
theorem B21506411 : Blo 1490065 21506411 := bstep (se 1 (by rfl) ⟨16129808, by rfl⟩ : syracuseStep 21506411 = 32259617) B32259617
theorem B4245959 : Blo 1490065 4245959 := bstep (se 1 (by rfl) ⟨3184469, by rfl⟩ : syracuseStep 4245959 = 6368939) B6368939
theorem B9063677 : Blo 1490065 9063677 := bstep (se 3 (by rfl) ⟨1699439, by rfl⟩ : syracuseStep 9063677 = 3398879) B3398879
theorem B27209135 : Blo 1490065 27209135 := bstep (se 1 (by rfl) ⟨20406851, by rfl⟩ : syracuseStep 27209135 = 40813703) B40813703
theorem B6369023 : Blo 1490065 6369023 := bstep (se 1 (by rfl) ⟨4776767, by rfl⟩ : syracuseStep 6369023 = 9553535) B9553535
theorem B6041627 : Blo 1490065 6041627 := bstep (se 1 (by rfl) ⟨4531220, by rfl⟩ : syracuseStep 6041627 = 9062441) B9062441
theorem B5664923 : Blo 1490065 5664923 := bstep (se 1 (by rfl) ⟨4248692, by rfl⟩ : syracuseStep 5664923 = 8497385) B8497385
theorem B16331201 : Blo 1490065 16331201 := bstep (se 2 (by rfl) ⟨6124200, by rfl⟩ : syracuseStep 16331201 = 12248401) B12248401
theorem B9557327 : Blo 1490065 9557327 := bstep (se 1 (by rfl) ⟨7167995, by rfl⟩ : syracuseStep 9557327 = 14335991) B14335991
theorem B21780089 : Blo 1490065 21780089 := bstep (se 2 (by rfl) ⟨8167533, by rfl⟩ : syracuseStep 21780089 = 16335067) B16335067
theorem B3774073 : Blo 1490065 3774073 := bstep (se 2 (by rfl) ⟨1415277, by rfl⟩ : syracuseStep 3774073 = 2830555) B2830555
theorem B45898289 : Blo 1490065 45898289 := bstep (se 2 (by rfl) ⟨17211858, by rfl⟩ : syracuseStep 45898289 = 34423717) B34423717
theorem B4905631 : Blo 1490065 4905631 := bstep (se 1 (by rfl) ⟨3679223, by rfl⟩ : syracuseStep 4905631 = 7358447) B7358447
theorem B3775369 : Blo 1490065 3775369 := bstep (se 2 (by rfl) ⟨1415763, by rfl⟩ : syracuseStep 3775369 = 2831527) B2831527
theorem B5659591 : Blo 1490065 5659591 := bstep (se 1 (by rfl) ⟨4244693, by rfl⟩ : syracuseStep 5659591 = 8489387) B8489387
theorem B12098587 : Blo 1490065 12098587 := bstep (se 1 (by rfl) ⟨9073940, by rfl⟩ : syracuseStep 12098587 = 18147881) B18147881
theorem B12729707 : Blo 1490065 12729707 := bstep (se 1 (by rfl) ⟨9547280, by rfl⟩ : syracuseStep 12729707 = 19094561) B19094561
theorem B1490303 : Blo 1490065 1490303 := bstep (se 1 (by rfl) ⟨1117727, by rfl⟩ : syracuseStep 1490303 = 2235455) B2235455
theorem B1490415 : Blo 1490065 1490415 := bstep (se 1 (by rfl) ⟨1117811, by rfl⟩ : syracuseStep 1490415 = 2235623) B2235623
theorem B5029505 : Blo 1490065 5029505 := bstep (se 2 (by rfl) ⟨1886064, by rfl⟩ : syracuseStep 5029505 = 3772129) B3772129
theorem B6373055 : Blo 1490065 6373055 := bstep (se 1 (by rfl) ⟨4779791, by rfl⟩ : syracuseStep 6373055 = 9559583) B9559583
theorem B1490815 : Blo 1490065 1490815 := bstep (se 1 (by rfl) ⟨1118111, by rfl⟩ : syracuseStep 1490815 = 2236223) B2236223
theorem B5029991 : Blo 1490065 5029991 := bstep (se 1 (by rfl) ⟨3772493, by rfl⟩ : syracuseStep 5029991 = 7544987) B7544987
theorem B3776615 : Blo 1490065 3776615 := bstep (se 1 (by rfl) ⟨2832461, by rfl⟩ : syracuseStep 3776615 = 5664923) B5664923
theorem B10887467 : Blo 1490065 10887467 := bstep (se 1 (by rfl) ⟨8165600, by rfl⟩ : syracuseStep 10887467 = 16331201) B16331201
theorem B5030639 : Blo 1490065 5030639 := bstep (se 1 (by rfl) ⟨3772979, by rfl⟩ : syracuseStep 5030639 = 7545959) B7545959
theorem B7546121 : Blo 1490065 7546121 := bstep (se 2 (by rfl) ⟨2829795, by rfl⟩ : syracuseStep 7546121 = 5659591) B5659591
theorem B16131449 : Blo 1490065 16131449 := bstep (se 2 (by rfl) ⟨6049293, by rfl⟩ : syracuseStep 16131449 = 12098587) B12098587
theorem B14337607 : Blo 1490065 14337607 := bstep (se 1 (by rfl) ⟨10753205, by rfl⟩ : syracuseStep 14337607 = 21506411) B21506411
theorem B30598859 : Blo 1490065 30598859 := bstep (se 1 (by rfl) ⟨22949144, by rfl⟩ : syracuseStep 30598859 = 45898289) B45898289
theorem B5032097 : Blo 1490065 5032097 := bstep (se 2 (by rfl) ⟨1887036, by rfl⟩ : syracuseStep 5032097 = 3774073) B3774073
theorem B18139423 : Blo 1490065 18139423 := bstep (se 1 (by rfl) ⟨13604567, by rfl⟩ : syracuseStep 18139423 = 27209135) B27209135
theorem B3353003 : Blo 1490065 3353003 := bstep (se 1 (by rfl) ⟨2514752, by rfl⟩ : syracuseStep 3353003 = 5029505) B5029505
theorem B4246015 : Blo 1490065 4246015 := bstep (se 1 (by rfl) ⟨3184511, by rfl⟩ : syracuseStep 4246015 = 6369023) B6369023
theorem B3354047 : Blo 1490065 3354047 := bstep (se 1 (by rfl) ⟨2515535, by rfl⟩ : syracuseStep 3354047 = 5031071) B5031071
theorem B6540841 : Blo 1490065 6540841 := bstep (se 2 (by rfl) ⟨2452815, by rfl⟩ : syracuseStep 6540841 = 4905631) B4905631
theorem B14520059 : Blo 1490065 14520059 := bstep (se 1 (by rfl) ⟨10890044, by rfl⟩ : syracuseStep 14520059 = 21780089) B21780089
theorem B5033825 : Blo 1490065 5033825 := bstep (se 2 (by rfl) ⟨1887684, by rfl⟩ : syracuseStep 5033825 = 3775369) B3775369
theorem B2830639 : Blo 1490065 2830639 := bstep (se 1 (by rfl) ⟨2122979, by rfl⟩ : syracuseStep 2830639 = 4245959) B4245959
theorem B217625089 : Blo 1490065 217625089 := bstep (se 2 (by rfl) ⟨81609408, by rfl⟩ : syracuseStep 217625089 = 163218817) B163218817
theorem B6042451 : Blo 1490065 6042451 := bstep (se 1 (by rfl) ⟨4531838, by rfl⟩ : syracuseStep 6042451 = 9063677) B9063677
theorem B4248703 : Blo 1490065 4248703 := bstep (se 1 (by rfl) ⟨3186527, by rfl⟩ : syracuseStep 4248703 = 6373055) B6373055
theorem B4027751 : Blo 1490065 4027751 := bstep (se 1 (by rfl) ⟨3020813, by rfl⟩ : syracuseStep 4027751 = 6041627) B6041627
theorem B3356297 : Blo 1490065 3356297 := bstep (se 2 (by rfl) ⟨1258611, by rfl⟩ : syracuseStep 3356297 = 2517223) B2517223
theorem B3774347 : Blo 1490065 3774347 := bstep (se 1 (by rfl) ⟨2830760, by rfl⟩ : syracuseStep 3774347 = 5661521) B5661521
theorem B3774671 : Blo 1490065 3774671 := bstep (se 1 (by rfl) ⟨2831003, by rfl⟩ : syracuseStep 3774671 = 5662007) B5662007
theorem B6371551 : Blo 1490065 6371551 := bstep (se 1 (by rfl) ⟨4778663, by rfl⟩ : syracuseStep 6371551 = 9557327) B9557327
theorem B1678207 : Blo 1490065 1678207 := bstep (se 1 (by rfl) ⟨1258655, by rfl⟩ : syracuseStep 1678207 = 2517311) B2517311
theorem B8486471 : Blo 1490065 8486471 := bstep (se 1 (by rfl) ⟨6364853, by rfl⟩ : syracuseStep 8486471 = 12729707) B12729707
theorem B8495401 : Blo 1490065 8495401 := bstep (se 2 (by rfl) ⟨3185775, by rfl⟩ : syracuseStep 8495401 = 6371551) B6371551
theorem B5661353 : Blo 1490065 5661353 := bstep (se 2 (by rfl) ⟨2123007, by rfl⟩ : syracuseStep 5661353 = 4246015) B4246015
theorem B29033245 : Blo 1490065 29033245 := bstep (se 3 (by rfl) ⟨5443733, by rfl⟩ : syracuseStep 29033245 = 10887467) B10887467
theorem B5030747 : Blo 1490065 5030747 := bstep (se 1 (by rfl) ⟨3773060, by rfl⟩ : syracuseStep 5030747 = 7546121) B7546121
theorem B2237531 : Blo 1490065 2237531 := bstep (se 1 (by rfl) ⟨1678148, by rfl⟩ : syracuseStep 2237531 = 3356297) B3356297
theorem B20399239 : Blo 1490065 20399239 := bstep (se 1 (by rfl) ⟨15299429, by rfl⟩ : syracuseStep 20399239 = 30598859) B30598859
theorem B2237609 : Blo 1490065 2237609 := bstep (se 2 (by rfl) ⟨839103, by rfl⟩ : syracuseStep 2237609 = 1678207) B1678207
theorem B2516231 : Blo 1490065 2516231 := bstep (se 1 (by rfl) ⟨1887173, by rfl⟩ : syracuseStep 2516231 = 3774347) B3774347
theorem B2516447 : Blo 1490065 2516447 := bstep (se 1 (by rfl) ⟨1887335, by rfl⟩ : syracuseStep 2516447 = 3774671) B3774671
theorem B3353327 : Blo 1490065 3353327 := bstep (se 1 (by rfl) ⟨2514995, by rfl⟩ : syracuseStep 3353327 = 5029991) B5029991
theorem B2517743 : Blo 1490065 2517743 := bstep (se 1 (by rfl) ⟨1888307, by rfl⟩ : syracuseStep 2517743 = 3776615) B3776615
theorem B24185897 : Blo 1490065 24185897 := bstep (se 2 (by rfl) ⟨9069711, by rfl⟩ : syracuseStep 24185897 = 18139423) B18139423
theorem B3353759 : Blo 1490065 3353759 := bstep (se 1 (by rfl) ⟨2515319, by rfl⟩ : syracuseStep 3353759 = 5030639) B5030639
theorem B8056601 : Blo 1490065 8056601 := bstep (se 2 (by rfl) ⟨3021225, by rfl⟩ : syracuseStep 8056601 = 6042451) B6042451
theorem B3354731 : Blo 1490065 3354731 := bstep (se 1 (by rfl) ⟨2516048, by rfl⟩ : syracuseStep 3354731 = 5032097) B5032097
theorem B5664937 : Blo 1490065 5664937 := bstep (se 2 (by rfl) ⟨2124351, by rfl⟩ : syracuseStep 5664937 = 4248703) B4248703
theorem B8721121 : Blo 1490065 8721121 := bstep (se 2 (by rfl) ⟨3270420, by rfl⟩ : syracuseStep 8721121 = 6540841) B6540841
theorem B19116809 : Blo 1490065 19116809 := bstep (se 2 (by rfl) ⟨7168803, by rfl⟩ : syracuseStep 19116809 = 14337607) B14337607
theorem B5657647 : Blo 1490065 5657647 := bstep (se 1 (by rfl) ⟨4243235, by rfl⟩ : syracuseStep 5657647 = 8486471) B8486471
theorem B9680039 : Blo 1490065 9680039 := bstep (se 1 (by rfl) ⟨7260029, by rfl⟩ : syracuseStep 9680039 = 14520059) B14520059
theorem B3355883 : Blo 1490065 3355883 := bstep (se 1 (by rfl) ⟨2516912, by rfl⟩ : syracuseStep 3355883 = 5033825) B5033825
theorem B3774185 : Blo 1490065 3774185 := bstep (se 2 (by rfl) ⟨1415319, by rfl⟩ : syracuseStep 3774185 = 2830639) B2830639
theorem B290166785 : Blo 1490065 290166785 := bstep (se 2 (by rfl) ⟨108812544, by rfl⟩ : syracuseStep 290166785 = 217625089) B217625089
theorem B2685167 : Blo 1490065 2685167 := bstep (se 1 (by rfl) ⟨2013875, by rfl⟩ : syracuseStep 2685167 = 4027751) B4027751
theorem B10754299 : Blo 1490065 10754299 := bstep (se 1 (by rfl) ⟨8065724, by rfl⟩ : syracuseStep 10754299 = 16131449) B16131449
theorem B2235335 : Blo 1490065 2235335 := bstep (se 1 (by rfl) ⟨1676501, by rfl⟩ : syracuseStep 2235335 = 3353003) B3353003
theorem B2236031 : Blo 1490065 2236031 := bstep (se 1 (by rfl) ⟨1677023, by rfl⟩ : syracuseStep 2236031 = 3354047) B3354047
theorem B2236487 : Blo 1490065 2236487 := bstep (se 1 (by rfl) ⟨1677365, by rfl⟩ : syracuseStep 2236487 = 3354731) B3354731
theorem B7553249 : Blo 1490065 7553249 := bstep (se 2 (by rfl) ⟨2832468, by rfl⟩ : syracuseStep 7553249 = 5664937) B5664937
theorem B1491687 : Blo 1490065 1491687 := bstep (se 1 (by rfl) ⟨1118765, by rfl⟩ : syracuseStep 1491687 = 2237531) B2237531
theorem B1491739 : Blo 1490065 1491739 := bstep (se 1 (by rfl) ⟨1118804, by rfl⟩ : syracuseStep 1491739 = 2237609) B2237609
theorem B2237255 : Blo 1490065 2237255 := bstep (se 1 (by rfl) ⟨1677941, by rfl⟩ : syracuseStep 2237255 = 3355883) B3355883
theorem B2516123 : Blo 1490065 2516123 := bstep (se 1 (by rfl) ⟨1887092, by rfl⟩ : syracuseStep 2516123 = 3774185) B3774185
theorem B27198985 : Blo 1490065 27198985 := bstep (se 2 (by rfl) ⟨10199619, by rfl⟩ : syracuseStep 27198985 = 20399239) B20399239
theorem B16123931 : Blo 1490065 16123931 := bstep (se 1 (by rfl) ⟨12092948, by rfl⟩ : syracuseStep 16123931 = 24185897) B24185897
theorem B3353831 : Blo 1490065 3353831 := bstep (se 1 (by rfl) ⟨2515373, by rfl⟩ : syracuseStep 3353831 = 5030747) B5030747
theorem B11628161 : Blo 1490065 11628161 := bstep (se 2 (by rfl) ⟨4360560, by rfl⟩ : syracuseStep 11628161 = 8721121) B8721121
theorem B38710993 : Blo 1490065 38710993 := bstep (se 2 (by rfl) ⟨14516622, by rfl⟩ : syracuseStep 38710993 = 29033245) B29033245
theorem B57356261 : Blo 1490065 57356261 := bstep (se 4 (by rfl) ⟨5377149, by rfl⟩ : syracuseStep 57356261 = 10754299) B10754299
theorem B1790111 : Blo 1490065 1790111 := bstep (se 1 (by rfl) ⟨1342583, by rfl⟩ : syracuseStep 1790111 = 2685167) B2685167
theorem B5371067 : Blo 1490065 5371067 := bstep (se 1 (by rfl) ⟨4028300, by rfl⟩ : syracuseStep 5371067 = 8056601) B8056601
theorem B11327201 : Blo 1490065 11327201 := bstep (se 2 (by rfl) ⟨4247700, by rfl⟩ : syracuseStep 11327201 = 8495401) B8495401
theorem B3774235 : Blo 1490065 3774235 := bstep (se 1 (by rfl) ⟨2830676, by rfl⟩ : syracuseStep 3774235 = 5661353) B5661353
theorem B12744539 : Blo 1490065 12744539 := bstep (se 1 (by rfl) ⟨9558404, by rfl⟩ : syracuseStep 12744539 = 19116809) B19116809
theorem B6453359 : Blo 1490065 6453359 := bstep (se 1 (by rfl) ⟨4840019, by rfl⟩ : syracuseStep 6453359 = 9680039) B9680039
theorem B1677487 : Blo 1490065 1677487 := bstep (se 1 (by rfl) ⟨1258115, by rfl⟩ : syracuseStep 1677487 = 2516231) B2516231
theorem B1677631 : Blo 1490065 1677631 := bstep (se 1 (by rfl) ⟨1258223, by rfl⟩ : syracuseStep 1677631 = 2516447) B2516447
theorem B193444523 : Blo 1490065 193444523 := bstep (se 1 (by rfl) ⟨145083392, by rfl⟩ : syracuseStep 193444523 = 290166785) B290166785
theorem B7543529 : Blo 1490065 7543529 := bstep (se 2 (by rfl) ⟨2828823, by rfl⟩ : syracuseStep 7543529 = 5657647) B5657647
theorem B2235551 : Blo 1490065 2235551 := bstep (se 1 (by rfl) ⟨1676663, by rfl⟩ : syracuseStep 2235551 = 3353327) B3353327
theorem B1678495 : Blo 1490065 1678495 := bstep (se 1 (by rfl) ⟨1258871, by rfl⟩ : syracuseStep 1678495 = 2517743) B2517743
theorem B1490223 : Blo 1490065 1490223 := bstep (se 1 (by rfl) ⟨1117667, by rfl⟩ : syracuseStep 1490223 = 2235335) B2235335
theorem B2235839 : Blo 1490065 2235839 := bstep (se 1 (by rfl) ⟨1676879, by rfl⟩ : syracuseStep 2235839 = 3353759) B3353759
theorem B1490687 : Blo 1490065 1490687 := bstep (se 1 (by rfl) ⟨1118015, by rfl⟩ : syracuseStep 1490687 = 2236031) B2236031
theorem B1490991 : Blo 1490065 1490991 := bstep (se 1 (by rfl) ⟨1118243, by rfl⟩ : syracuseStep 1490991 = 2236487) B2236487
theorem B2236649 : Blo 1490065 2236649 := bstep (se 2 (by rfl) ⟨838743, by rfl⟩ : syracuseStep 2236649 = 1677487) B1677487
theorem B2236841 : Blo 1490065 2236841 := bstep (se 2 (by rfl) ⟨838815, by rfl⟩ : syracuseStep 2236841 = 1677631) B1677631
theorem B1491503 : Blo 1490065 1491503 := bstep (se 1 (by rfl) ⟨1118627, by rfl⟩ : syracuseStep 1491503 = 2237255) B2237255
theorem B8496359 : Blo 1490065 8496359 := bstep (se 1 (by rfl) ⟨6372269, by rfl⟩ : syracuseStep 8496359 = 12744539) B12744539
theorem B10749287 : Blo 1490065 10749287 := bstep (se 1 (by rfl) ⟨8061965, by rfl⟩ : syracuseStep 10749287 = 16123931) B16123931
theorem B4302239 : Blo 1490065 4302239 := bstep (se 1 (by rfl) ⟨3226679, by rfl⟩ : syracuseStep 4302239 = 6453359) B6453359
theorem B2237993 : Blo 1490065 2237993 := bstep (se 2 (by rfl) ⟨839247, by rfl⟩ : syracuseStep 2237993 = 1678495) B1678495
theorem B5032313 : Blo 1490065 5032313 := bstep (se 2 (by rfl) ⟨1887117, by rfl⟩ : syracuseStep 5032313 = 3774235) B3774235
theorem B7752107 : Blo 1490065 7752107 := bstep (se 1 (by rfl) ⟨5814080, by rfl⟩ : syracuseStep 7752107 = 11628161) B11628161
theorem B14322845 : Blo 1490065 14322845 := bstep (se 3 (by rfl) ⟨2685533, by rfl⟩ : syracuseStep 14322845 = 5371067) B5371067
theorem B128963015 : Blo 1490065 128963015 := bstep (se 1 (by rfl) ⟨96722261, by rfl⟩ : syracuseStep 128963015 = 193444523) B193444523
theorem B51614657 : Blo 1490065 51614657 := bstep (se 2 (by rfl) ⟨19355496, by rfl⟩ : syracuseStep 51614657 = 38710993) B38710993
theorem B38237507 : Blo 1490065 38237507 := bstep (se 1 (by rfl) ⟨28678130, by rfl⟩ : syracuseStep 38237507 = 57356261) B57356261
theorem B5035499 : Blo 1490065 5035499 := bstep (se 1 (by rfl) ⟨3776624, by rfl⟩ : syracuseStep 5035499 = 7553249) B7553249
theorem B4773629 : Blo 1490065 4773629 := bstep (se 3 (by rfl) ⟨895055, by rfl⟩ : syracuseStep 4773629 = 1790111) B1790111
theorem B1677415 : Blo 1490065 1677415 := bstep (se 1 (by rfl) ⟨1258061, by rfl⟩ : syracuseStep 1677415 = 2516123) B2516123
theorem B7551467 : Blo 1490065 7551467 := bstep (se 1 (by rfl) ⟨5663600, by rfl⟩ : syracuseStep 7551467 = 11327201) B11327201
theorem B5029019 : Blo 1490065 5029019 := bstep (se 1 (by rfl) ⟨3771764, by rfl⟩ : syracuseStep 5029019 = 7543529) B7543529
theorem B36265313 : Blo 1490065 36265313 := bstep (se 2 (by rfl) ⟨13599492, by rfl⟩ : syracuseStep 36265313 = 27198985) B27198985
theorem B1490367 : Blo 1490065 1490367 := bstep (se 1 (by rfl) ⟨1117775, by rfl⟩ : syracuseStep 1490367 = 2235551) B2235551
theorem B2235887 : Blo 1490065 2235887 := bstep (se 1 (by rfl) ⟨1676915, by rfl⟩ : syracuseStep 2235887 = 3353831) B3353831
theorem B1490559 : Blo 1490065 1490559 := bstep (se 1 (by rfl) ⟨1117919, by rfl⟩ : syracuseStep 1490559 = 2235839) B2235839
theorem B2236553 : Blo 1490065 2236553 := bstep (se 2 (by rfl) ⟨838707, by rfl⟩ : syracuseStep 2236553 = 1677415) B1677415
theorem B1491099 : Blo 1490065 1491099 := bstep (se 1 (by rfl) ⟨1118324, by rfl⟩ : syracuseStep 1491099 = 2236649) B2236649
theorem B1491227 : Blo 1490065 1491227 := bstep (se 1 (by rfl) ⟨1118420, by rfl⟩ : syracuseStep 1491227 = 2236841) B2236841
theorem B85975343 : Blo 1490065 85975343 := bstep (se 1 (by rfl) ⟨64481507, by rfl⟩ : syracuseStep 85975343 = 128963015) B128963015
theorem B1491995 : Blo 1490065 1491995 := bstep (se 1 (by rfl) ⟨1118996, by rfl⟩ : syracuseStep 1491995 = 2237993) B2237993
theorem B3352679 : Blo 1490065 3352679 := bstep (se 1 (by rfl) ⟨2514509, by rfl⟩ : syracuseStep 3352679 = 5029019) B5029019
theorem B24176875 : Blo 1490065 24176875 := bstep (se 1 (by rfl) ⟨18132656, by rfl⟩ : syracuseStep 24176875 = 36265313) B36265313
theorem B34409771 : Blo 1490065 34409771 := bstep (se 1 (by rfl) ⟨25807328, by rfl⟩ : syracuseStep 34409771 = 51614657) B51614657
theorem B5664239 : Blo 1490065 5664239 := bstep (se 1 (by rfl) ⟨4248179, by rfl⟩ : syracuseStep 5664239 = 8496359) B8496359
theorem B11472637 : Blo 1490065 11472637 := bstep (se 3 (by rfl) ⟨2151119, by rfl⟩ : syracuseStep 11472637 = 4302239) B4302239
theorem B3182419 : Blo 1490065 3182419 := bstep (se 1 (by rfl) ⟨2386814, by rfl⟩ : syracuseStep 3182419 = 4773629) B4773629
theorem B3354875 : Blo 1490065 3354875 := bstep (se 1 (by rfl) ⟨2516156, by rfl⟩ : syracuseStep 3354875 = 5032313) B5032313
theorem B5034311 : Blo 1490065 5034311 := bstep (se 1 (by rfl) ⟨3775733, by rfl⟩ : syracuseStep 5034311 = 7551467) B7551467
theorem B9548563 : Blo 1490065 9548563 := bstep (se 1 (by rfl) ⟨7161422, by rfl⟩ : syracuseStep 9548563 = 14322845) B14322845
theorem B25491671 : Blo 1490065 25491671 := bstep (se 1 (by rfl) ⟨19118753, by rfl⟩ : syracuseStep 25491671 = 38237507) B38237507
theorem B7166191 : Blo 1490065 7166191 := bstep (se 1 (by rfl) ⟨5374643, by rfl⟩ : syracuseStep 7166191 = 10749287) B10749287
theorem B3356999 : Blo 1490065 3356999 := bstep (se 1 (by rfl) ⟨2517749, by rfl⟩ : syracuseStep 3356999 = 5035499) B5035499
theorem B5168071 : Blo 1490065 5168071 := bstep (se 1 (by rfl) ⟨3876053, by rfl⟩ : syracuseStep 5168071 = 7752107) B7752107
theorem B1490591 : Blo 1490065 1490591 := bstep (se 1 (by rfl) ⟨1117943, by rfl⟩ : syracuseStep 1490591 = 2235887) B2235887
theorem B1491035 : Blo 1490065 1491035 := bstep (se 1 (by rfl) ⟨1118276, by rfl⟩ : syracuseStep 1491035 = 2236553) B2236553
theorem B2236583 : Blo 1490065 2236583 := bstep (se 1 (by rfl) ⟨1677437, by rfl⟩ : syracuseStep 2236583 = 3354875) B3354875
theorem B32235833 : Blo 1490065 32235833 := bstep (se 2 (by rfl) ⟨12088437, by rfl⟩ : syracuseStep 32235833 = 24176875) B24176875
theorem B12731417 : Blo 1490065 12731417 := bstep (se 2 (by rfl) ⟨4774281, by rfl⟩ : syracuseStep 12731417 = 9548563) B9548563
theorem B6890761 : Blo 1490065 6890761 := bstep (se 2 (by rfl) ⟨2584035, by rfl⟩ : syracuseStep 6890761 = 5168071) B5168071
theorem B2237999 : Blo 1490065 2237999 := bstep (se 1 (by rfl) ⟨1678499, by rfl⟩ : syracuseStep 2237999 = 3356999) B3356999
theorem B22939847 : Blo 1490065 22939847 := bstep (se 1 (by rfl) ⟨17204885, by rfl⟩ : syracuseStep 22939847 = 34409771) B34409771
theorem B15296849 : Blo 1490065 15296849 := bstep (se 2 (by rfl) ⟨5736318, by rfl⟩ : syracuseStep 15296849 = 11472637) B11472637
theorem B9554921 : Blo 1490065 9554921 := bstep (se 2 (by rfl) ⟨3583095, by rfl⟩ : syracuseStep 9554921 = 7166191) B7166191
theorem B16994447 : Blo 1490065 16994447 := bstep (se 1 (by rfl) ⟨12745835, by rfl⟩ : syracuseStep 16994447 = 25491671) B25491671
theorem B57316895 : Blo 1490065 57316895 := bstep (se 1 (by rfl) ⟨42987671, by rfl⟩ : syracuseStep 57316895 = 85975343) B85975343
theorem B3356207 : Blo 1490065 3356207 := bstep (se 1 (by rfl) ⟨2517155, by rfl⟩ : syracuseStep 3356207 = 5034311) B5034311
theorem B2235119 : Blo 1490065 2235119 := bstep (se 1 (by rfl) ⟨1676339, by rfl⟩ : syracuseStep 2235119 = 3352679) B3352679
theorem B3776159 : Blo 1490065 3776159 := bstep (se 1 (by rfl) ⟨2832119, by rfl⟩ : syracuseStep 3776159 = 5664239) B5664239
theorem B4243225 : Blo 1490065 4243225 := bstep (se 2 (by rfl) ⟨1591209, by rfl⟩ : syracuseStep 4243225 = 3182419) B3182419
theorem B11329631 : Blo 1490065 11329631 := bstep (se 1 (by rfl) ⟨8497223, by rfl⟩ : syracuseStep 11329631 = 16994447) B16994447
theorem B1491055 : Blo 1490065 1491055 := bstep (se 1 (by rfl) ⟨1118291, by rfl⟩ : syracuseStep 1491055 = 2236583) B2236583
theorem B8487611 : Blo 1490065 8487611 := bstep (se 1 (by rfl) ⟨6365708, by rfl⟩ : syracuseStep 8487611 = 12731417) B12731417
theorem B2237471 : Blo 1490065 2237471 := bstep (se 1 (by rfl) ⟨1678103, by rfl⟩ : syracuseStep 2237471 = 3356207) B3356207
theorem B1491999 : Blo 1490065 1491999 := bstep (se 1 (by rfl) ⟨1118999, by rfl⟩ : syracuseStep 1491999 = 2237999) B2237999
theorem B36750725 : Blo 1490065 36750725 := bstep (se 4 (by rfl) ⟨3445380, by rfl⟩ : syracuseStep 36750725 = 6890761) B6890761
theorem B2517439 : Blo 1490065 2517439 := bstep (se 1 (by rfl) ⟨1888079, by rfl⟩ : syracuseStep 2517439 = 3776159) B3776159
theorem B21490555 : Blo 1490065 21490555 := bstep (se 1 (by rfl) ⟨16117916, by rfl⟩ : syracuseStep 21490555 = 32235833) B32235833
theorem B38211263 : Blo 1490065 38211263 := bstep (se 1 (by rfl) ⟨28658447, by rfl⟩ : syracuseStep 38211263 = 57316895) B57316895
theorem B6369947 : Blo 1490065 6369947 := bstep (se 1 (by rfl) ⟨4777460, by rfl⟩ : syracuseStep 6369947 = 9554921) B9554921
theorem B5657633 : Blo 1490065 5657633 := bstep (se 2 (by rfl) ⟨2121612, by rfl⟩ : syracuseStep 5657633 = 4243225) B4243225
theorem B15293231 : Blo 1490065 15293231 := bstep (se 1 (by rfl) ⟨11469923, by rfl⟩ : syracuseStep 15293231 = 22939847) B22939847
theorem B10197899 : Blo 1490065 10197899 := bstep (se 1 (by rfl) ⟨7648424, by rfl⟩ : syracuseStep 10197899 = 15296849) B15296849
theorem B1490079 : Blo 1490065 1490079 := bstep (se 1 (by rfl) ⟨1117559, by rfl⟩ : syracuseStep 1490079 = 2235119) B2235119
theorem B7553087 : Blo 1490065 7553087 := bstep (se 1 (by rfl) ⟨5664815, by rfl⟩ : syracuseStep 7553087 = 11329631) B11329631
theorem B1491647 : Blo 1490065 1491647 := bstep (se 1 (by rfl) ⟨1118735, by rfl⟩ : syracuseStep 1491647 = 2237471) B2237471
theorem B4246631 : Blo 1490065 4246631 := bstep (se 1 (by rfl) ⟨3184973, by rfl⟩ : syracuseStep 4246631 = 6369947) B6369947
theorem B3771755 : Blo 1490065 3771755 := bstep (se 1 (by rfl) ⟨2828816, by rfl⟩ : syracuseStep 3771755 = 5657633) B5657633
theorem B10195487 : Blo 1490065 10195487 := bstep (se 1 (by rfl) ⟨7646615, by rfl⟩ : syracuseStep 10195487 = 15293231) B15293231
theorem B25474175 : Blo 1490065 25474175 := bstep (se 1 (by rfl) ⟨19105631, by rfl⟩ : syracuseStep 25474175 = 38211263) B38211263
theorem B5658407 : Blo 1490065 5658407 := bstep (se 1 (by rfl) ⟨4243805, by rfl⟩ : syracuseStep 5658407 = 8487611) B8487611
theorem B3356585 : Blo 1490065 3356585 := bstep (se 2 (by rfl) ⟨1258719, by rfl⟩ : syracuseStep 3356585 = 2517439) B2517439
theorem B24500483 : Blo 1490065 24500483 := bstep (se 1 (by rfl) ⟨18375362, by rfl⟩ : syracuseStep 24500483 = 36750725) B36750725
theorem B28654073 : Blo 1490065 28654073 := bstep (se 2 (by rfl) ⟨10745277, by rfl⟩ : syracuseStep 28654073 = 21490555) B21490555
theorem B6798599 : Blo 1490065 6798599 := bstep (se 1 (by rfl) ⟨5098949, by rfl⟩ : syracuseStep 6798599 = 10197899) B10197899
theorem B16982783 : Blo 1490065 16982783 := bstep (se 1 (by rfl) ⟨12737087, by rfl⟩ : syracuseStep 16982783 = 25474175) B25474175
theorem B2237723 : Blo 1490065 2237723 := bstep (se 1 (by rfl) ⟨1678292, by rfl⟩ : syracuseStep 2237723 = 3356585) B3356585
theorem B4532399 : Blo 1490065 4532399 := bstep (se 1 (by rfl) ⟨3399299, by rfl⟩ : syracuseStep 4532399 = 6798599) B6798599
theorem B3772271 : Blo 1490065 3772271 := bstep (se 1 (by rfl) ⟨2829203, by rfl⟩ : syracuseStep 3772271 = 5658407) B5658407
theorem B2831087 : Blo 1490065 2831087 := bstep (se 1 (by rfl) ⟨2123315, by rfl⟩ : syracuseStep 2831087 = 4246631) B4246631
theorem B5035391 : Blo 1490065 5035391 := bstep (se 1 (by rfl) ⟨3776543, by rfl⟩ : syracuseStep 5035391 = 7553087) B7553087
theorem B6796991 : Blo 1490065 6796991 := bstep (se 1 (by rfl) ⟨5097743, by rfl⟩ : syracuseStep 6796991 = 10195487) B10195487
theorem B16333655 : Blo 1490065 16333655 := bstep (se 1 (by rfl) ⟨12250241, by rfl⟩ : syracuseStep 16333655 = 24500483) B24500483
theorem B19102715 : Blo 1490065 19102715 := bstep (se 1 (by rfl) ⟨14327036, by rfl⟩ : syracuseStep 19102715 = 28654073) B28654073
theorem B2514503 : Blo 1490065 2514503 := bstep (se 1 (by rfl) ⟨1885877, by rfl⟩ : syracuseStep 2514503 = 3771755) B3771755
theorem B11321855 : Blo 1490065 11321855 := bstep (se 1 (by rfl) ⟨8491391, by rfl⟩ : syracuseStep 11321855 = 16982783) B16982783
theorem B1491815 : Blo 1490065 1491815 := bstep (se 1 (by rfl) ⟨1118861, by rfl⟩ : syracuseStep 1491815 = 2237723) B2237723
theorem B1887391 : Blo 1490065 1887391 := bstep (se 1 (by rfl) ⟨1415543, by rfl⟩ : syracuseStep 1887391 = 2831087) B2831087
theorem B18125309 : Blo 1490065 18125309 := bstep (se 3 (by rfl) ⟨3398495, by rfl⟩ : syracuseStep 18125309 = 6796991) B6796991
theorem B12735143 : Blo 1490065 12735143 := bstep (se 1 (by rfl) ⟨9551357, by rfl⟩ : syracuseStep 12735143 = 19102715) B19102715
theorem B1676335 : Blo 1490065 1676335 := bstep (se 1 (by rfl) ⟨1257251, by rfl⟩ : syracuseStep 1676335 = 2514503) B2514503
theorem B3356927 : Blo 1490065 3356927 := bstep (se 1 (by rfl) ⟨2517695, by rfl⟩ : syracuseStep 3356927 = 5035391) B5035391
theorem B3021599 : Blo 1490065 3021599 := bstep (se 1 (by rfl) ⟨2266199, by rfl⟩ : syracuseStep 3021599 = 4532399) B4532399
theorem B43556413 : Blo 1490065 43556413 := bstep (se 3 (by rfl) ⟨8166827, by rfl⟩ : syracuseStep 43556413 = 16333655) B16333655
theorem B2514847 : Blo 1490065 2514847 := bstep (se 1 (by rfl) ⟨1886135, by rfl⟩ : syracuseStep 2514847 = 3772271) B3772271
theorem B12083539 : Blo 1490065 12083539 := bstep (se 1 (by rfl) ⟨9062654, by rfl⟩ : syracuseStep 12083539 = 18125309) B18125309
theorem B2237951 : Blo 1490065 2237951 := bstep (se 1 (by rfl) ⟨1678463, by rfl⟩ : syracuseStep 2237951 = 3356927) B3356927
theorem B2516521 : Blo 1490065 2516521 := bstep (se 2 (by rfl) ⟨943695, by rfl⟩ : syracuseStep 2516521 = 1887391) B1887391
theorem B58075217 : Blo 1490065 58075217 := bstep (se 2 (by rfl) ⟨21778206, by rfl⟩ : syracuseStep 58075217 = 43556413) B43556413
theorem B3353129 : Blo 1490065 3353129 := bstep (se 2 (by rfl) ⟨1257423, by rfl⟩ : syracuseStep 3353129 = 2514847) B2514847
theorem B7547903 : Blo 1490065 7547903 := bstep (se 1 (by rfl) ⟨5660927, by rfl⟩ : syracuseStep 7547903 = 11321855) B11321855
theorem B8490095 : Blo 1490065 8490095 := bstep (se 1 (by rfl) ⟨6367571, by rfl⟩ : syracuseStep 8490095 = 12735143) B12735143
theorem B2235113 : Blo 1490065 2235113 := bstep (se 2 (by rfl) ⟨838167, by rfl⟩ : syracuseStep 2235113 = 1676335) B1676335
theorem B2014399 : Blo 1490065 2014399 := bstep (se 1 (by rfl) ⟨1510799, by rfl⟩ : syracuseStep 2014399 = 3021599) B3021599
theorem B1491967 : Blo 1490065 1491967 := bstep (se 1 (by rfl) ⟨1118975, by rfl⟩ : syracuseStep 1491967 = 2237951) B2237951
theorem B38716811 : Blo 1490065 38716811 := bstep (se 1 (by rfl) ⟨29037608, by rfl⟩ : syracuseStep 38716811 = 58075217) B58075217
theorem B5031935 : Blo 1490065 5031935 := bstep (se 1 (by rfl) ⟨3773951, by rfl⟩ : syracuseStep 5031935 = 7547903) B7547903
theorem B10743461 : Blo 1490065 10743461 := bstep (se 4 (by rfl) ⟨1007199, by rfl⟩ : syracuseStep 10743461 = 2014399) B2014399
theorem B3355361 : Blo 1490065 3355361 := bstep (se 2 (by rfl) ⟨1258260, by rfl⟩ : syracuseStep 3355361 = 2516521) B2516521
theorem B16111385 : Blo 1490065 16111385 := bstep (se 2 (by rfl) ⟨6041769, by rfl⟩ : syracuseStep 16111385 = 12083539) B12083539
theorem B2235419 : Blo 1490065 2235419 := bstep (se 1 (by rfl) ⟨1676564, by rfl⟩ : syracuseStep 2235419 = 3353129) B3353129
theorem B1490075 : Blo 1490065 1490075 := bstep (se 1 (by rfl) ⟨1117556, by rfl⟩ : syracuseStep 1490075 = 2235113) B2235113
theorem B5660063 : Blo 1490065 5660063 := bstep (se 1 (by rfl) ⟨4245047, by rfl⟩ : syracuseStep 5660063 = 8490095) B8490095
theorem B2236907 : Blo 1490065 2236907 := bstep (se 1 (by rfl) ⟨1677680, by rfl⟩ : syracuseStep 2236907 = 3355361) B3355361
theorem B10740923 : Blo 1490065 10740923 := bstep (se 1 (by rfl) ⟨8055692, by rfl⟩ : syracuseStep 10740923 = 16111385) B16111385
theorem B7162307 : Blo 1490065 7162307 := bstep (se 1 (by rfl) ⟨5371730, by rfl⟩ : syracuseStep 7162307 = 10743461) B10743461
theorem B3354623 : Blo 1490065 3354623 := bstep (se 1 (by rfl) ⟨2515967, by rfl⟩ : syracuseStep 3354623 = 5031935) B5031935
theorem B3773375 : Blo 1490065 3773375 := bstep (se 1 (by rfl) ⟨2830031, by rfl⟩ : syracuseStep 3773375 = 5660063) B5660063
theorem B25811207 : Blo 1490065 25811207 := bstep (se 1 (by rfl) ⟨19358405, by rfl⟩ : syracuseStep 25811207 = 38716811) B38716811
theorem B1490279 : Blo 1490065 1490279 := bstep (se 1 (by rfl) ⟨1117709, by rfl⟩ : syracuseStep 1490279 = 2235419) B2235419
theorem B1491271 : Blo 1490065 1491271 := bstep (se 1 (by rfl) ⟨1118453, by rfl⟩ : syracuseStep 1491271 = 2236907) B2236907
theorem B2515583 : Blo 1490065 2515583 := bstep (se 1 (by rfl) ⟨1886687, by rfl⟩ : syracuseStep 2515583 = 3773375) B3773375
theorem B7160615 : Blo 1490065 7160615 := bstep (se 1 (by rfl) ⟨5370461, by rfl⟩ : syracuseStep 7160615 = 10740923) B10740923
theorem B17207471 : Blo 1490065 17207471 := bstep (se 1 (by rfl) ⟨12905603, by rfl⟩ : syracuseStep 17207471 = 25811207) B25811207
theorem B2236415 : Blo 1490065 2236415 := bstep (se 1 (by rfl) ⟨1677311, by rfl⟩ : syracuseStep 2236415 = 3354623) B3354623
theorem B4774871 : Blo 1490065 4774871 := bstep (se 1 (by rfl) ⟨3581153, by rfl⟩ : syracuseStep 4774871 = 7162307) B7162307
theorem B11471647 : Blo 1490065 11471647 := bstep (se 1 (by rfl) ⟨8603735, by rfl⟩ : syracuseStep 11471647 = 17207471) B17207471
theorem B3183247 : Blo 1490065 3183247 := bstep (se 1 (by rfl) ⟨2387435, by rfl⟩ : syracuseStep 3183247 = 4774871) B4774871
theorem B1677055 : Blo 1490065 1677055 := bstep (se 1 (by rfl) ⟨1257791, by rfl⟩ : syracuseStep 1677055 = 2515583) B2515583
theorem B4773743 : Blo 1490065 4773743 := bstep (se 1 (by rfl) ⟨3580307, by rfl⟩ : syracuseStep 4773743 = 7160615) B7160615
theorem B1490943 : Blo 1490065 1490943 := bstep (se 1 (by rfl) ⟨1118207, by rfl⟩ : syracuseStep 1490943 = 2236415) B2236415
theorem B4244329 : Blo 1490065 4244329 := bstep (se 2 (by rfl) ⟨1591623, by rfl⟩ : syracuseStep 4244329 = 3183247) B3183247
theorem B15295529 : Blo 1490065 15295529 := bstep (se 2 (by rfl) ⟨5735823, by rfl⟩ : syracuseStep 15295529 = 11471647) B11471647
theorem B3182495 : Blo 1490065 3182495 := bstep (se 1 (by rfl) ⟨2386871, by rfl⟩ : syracuseStep 3182495 = 4773743) B4773743
theorem B2236073 : Blo 1490065 2236073 := bstep (se 2 (by rfl) ⟨838527, by rfl⟩ : syracuseStep 2236073 = 1677055) B1677055
theorem B10197019 : Blo 1490065 10197019 := bstep (se 1 (by rfl) ⟨7647764, by rfl⟩ : syracuseStep 10197019 = 15295529) B15295529
theorem B5659105 : Blo 1490065 5659105 := bstep (se 2 (by rfl) ⟨2122164, by rfl⟩ : syracuseStep 5659105 = 4244329) B4244329
theorem B8486653 : Blo 1490065 8486653 := bstep (se 3 (by rfl) ⟨1591247, by rfl⟩ : syracuseStep 8486653 = 3182495) B3182495
theorem B1490715 : Blo 1490065 1490715 := bstep (se 1 (by rfl) ⟨1118036, by rfl⟩ : syracuseStep 1490715 = 2236073) B2236073
theorem B7545473 : Blo 1490065 7545473 := bstep (se 2 (by rfl) ⟨2829552, by rfl⟩ : syracuseStep 7545473 = 5659105) B5659105
theorem B11315537 : Blo 1490065 11315537 := bstep (se 2 (by rfl) ⟨4243326, by rfl⟩ : syracuseStep 11315537 = 8486653) B8486653
theorem B13596025 : Blo 1490065 13596025 := bstep (se 2 (by rfl) ⟨5098509, by rfl⟩ : syracuseStep 13596025 = 10197019) B10197019
theorem B5030315 : Blo 1490065 5030315 := bstep (se 1 (by rfl) ⟨3772736, by rfl⟩ : syracuseStep 5030315 = 7545473) B7545473
theorem B7543691 : Blo 1490065 7543691 := bstep (se 1 (by rfl) ⟨5657768, by rfl⟩ : syracuseStep 7543691 = 11315537) B11315537
theorem B18128033 : Blo 1490065 18128033 := bstep (se 2 (by rfl) ⟨6798012, by rfl⟩ : syracuseStep 18128033 = 13596025) B13596025
theorem B12085355 : Blo 1490065 12085355 := bstep (se 1 (by rfl) ⟨9064016, by rfl⟩ : syracuseStep 12085355 = 18128033) B18128033
theorem B3353543 : Blo 1490065 3353543 := bstep (se 1 (by rfl) ⟨2515157, by rfl⟩ : syracuseStep 3353543 = 5030315) B5030315
theorem B5029127 : Blo 1490065 5029127 := bstep (se 1 (by rfl) ⟨3771845, by rfl⟩ : syracuseStep 5029127 = 7543691) B7543691
theorem B3352751 : Blo 1490065 3352751 := bstep (se 1 (by rfl) ⟨2514563, by rfl⟩ : syracuseStep 3352751 = 5029127) B5029127
theorem B8056903 : Blo 1490065 8056903 := bstep (se 1 (by rfl) ⟨6042677, by rfl⟩ : syracuseStep 8056903 = 12085355) B12085355
theorem B2235695 : Blo 1490065 2235695 := bstep (se 1 (by rfl) ⟨1676771, by rfl⟩ : syracuseStep 2235695 = 3353543) B3353543
theorem B10742537 : Blo 1490065 10742537 := bstep (se 2 (by rfl) ⟨4028451, by rfl⟩ : syracuseStep 10742537 = 8056903) B8056903
theorem B2235167 : Blo 1490065 2235167 := bstep (se 1 (by rfl) ⟨1676375, by rfl⟩ : syracuseStep 2235167 = 3352751) B3352751
theorem B1490463 : Blo 1490065 1490463 := bstep (se 1 (by rfl) ⟨1117847, by rfl⟩ : syracuseStep 1490463 = 2235695) B2235695
theorem B7161691 : Blo 1490065 7161691 := bstep (se 1 (by rfl) ⟨5371268, by rfl⟩ : syracuseStep 7161691 = 10742537) B10742537
theorem B1490111 : Blo 1490065 1490111 := bstep (se 1 (by rfl) ⟨1117583, by rfl⟩ : syracuseStep 1490111 = 2235167) B2235167
theorem B9548921 : Blo 1490065 9548921 := bstep (se 2 (by rfl) ⟨3580845, by rfl⟩ : syracuseStep 9548921 = 7161691) B7161691
theorem B6365947 : Blo 1490065 6365947 := bstep (se 1 (by rfl) ⟨4774460, by rfl⟩ : syracuseStep 6365947 = 9548921) B9548921
theorem B8487929 : Blo 1490065 8487929 := bstep (se 2 (by rfl) ⟨3182973, by rfl⟩ : syracuseStep 8487929 = 6365947) B6365947
theorem B5658619 : Blo 1490065 5658619 := bstep (se 1 (by rfl) ⟨4243964, by rfl⟩ : syracuseStep 5658619 = 8487929) B8487929
theorem B7544825 : Blo 1490065 7544825 := bstep (se 2 (by rfl) ⟨2829309, by rfl⟩ : syracuseStep 7544825 = 5658619) B5658619
theorem B5029883 : Blo 1490065 5029883 := bstep (se 1 (by rfl) ⟨3772412, by rfl⟩ : syracuseStep 5029883 = 7544825) B7544825
theorem B3353255 : Blo 1490065 3353255 := bstep (se 1 (by rfl) ⟨2514941, by rfl⟩ : syracuseStep 3353255 = 5029883) B5029883
theorem B2235503 : Blo 1490065 2235503 := bstep (se 1 (by rfl) ⟨1676627, by rfl⟩ : syracuseStep 2235503 = 3353255) B3353255
theorem B1490335 : Blo 1490065 1490335 := bstep (se 1 (by rfl) ⟨1117751, by rfl⟩ : syracuseStep 1490335 = 2235503) B2235503

theorem C0 (j : ℕ) (h1 : 372516 ≤ j) (h2 : j ≤ 373015) : Blo 1490065 (4 * j + 3) := by
  interval_cases j
  · exact B1490067
  · exact B1490071
  · exact B1490075
  · exact B1490079
  · exact B1490083
  · exact B1490087
  · exact B1490091
  · exact B1490095
  · exact B1490099
  · exact B1490103
  · exact B1490107
  · exact B1490111
  · exact B1490115
  · exact B1490119
  · exact B1490123
  · exact B1490127
  · exact B1490131
  · exact B1490135
  · exact B1490139
  · exact B1490143
  · exact B1490147
  · exact B1490151
  · exact B1490155
  · exact B1490159
  · exact B1490163
  · exact B1490167
  · exact B1490171
  · exact B1490175
  · exact B1490179
  · exact B1490183
  · exact B1490187
  · exact B1490191
  · exact B1490195
  · exact B1490199
  · exact B1490203
  · exact B1490207
  · exact B1490211
  · exact B1490215
  · exact B1490219
  · exact B1490223
  · exact B1490227
  · exact B1490231
  · exact B1490235
  · exact B1490239
  · exact B1490243
  · exact B1490247
  · exact B1490251
  · exact B1490255
  · exact B1490259
  · exact B1490263
  · exact B1490267
  · exact B1490271
  · exact B1490275
  · exact B1490279
  · exact B1490283
  · exact B1490287
  · exact B1490291
  · exact B1490295
  · exact B1490299
  · exact B1490303
  · exact B1490307
  · exact B1490311
  · exact B1490315
  · exact B1490319
  · exact B1490323
  · exact B1490327
  · exact B1490331
  · exact B1490335
  · exact B1490339
  · exact B1490343
  · exact B1490347
  · exact B1490351
  · exact B1490355
  · exact B1490359
  · exact B1490363
  · exact B1490367
  · exact B1490371
  · exact B1490375
  · exact B1490379
  · exact B1490383
  · exact B1490387
  · exact B1490391
  · exact B1490395
  · exact B1490399
  · exact B1490403
  · exact B1490407
  · exact B1490411
  · exact B1490415
  · exact B1490419
  · exact B1490423
  · exact B1490427
  · exact B1490431
  · exact B1490435
  · exact B1490439
  · exact B1490443
  · exact B1490447
  · exact B1490451
  · exact B1490455
  · exact B1490459
  · exact B1490463
  · exact B1490467
  · exact B1490471
  · exact B1490475
  · exact B1490479
  · exact B1490483
  · exact B1490487
  · exact B1490491
  · exact B1490495
  · exact B1490499
  · exact B1490503
  · exact B1490507
  · exact B1490511
  · exact B1490515
  · exact B1490519
  · exact B1490523
  · exact B1490527
  · exact B1490531
  · exact B1490535
  · exact B1490539
  · exact B1490543
  · exact B1490547
  · exact B1490551
  · exact B1490555
  · exact B1490559
  · exact B1490563
  · exact B1490567
  · exact B1490571
  · exact B1490575
  · exact B1490579
  · exact B1490583
  · exact B1490587
  · exact B1490591
  · exact B1490595
  · exact B1490599
  · exact B1490603
  · exact B1490607
  · exact B1490611
  · exact B1490615
  · exact B1490619
  · exact B1490623
  · exact B1490627
  · exact B1490631
  · exact B1490635
  · exact B1490639
  · exact B1490643
  · exact B1490647
  · exact B1490651
  · exact B1490655
  · exact B1490659
  · exact B1490663
  · exact B1490667
  · exact B1490671
  · exact B1490675
  · exact B1490679
  · exact B1490683
  · exact B1490687
  · exact B1490691
  · exact B1490695
  · exact B1490699
  · exact B1490703
  · exact B1490707
  · exact B1490711
  · exact B1490715
  · exact B1490719
  · exact B1490723
  · exact B1490727
  · exact B1490731
  · exact B1490735
  · exact B1490739
  · exact B1490743
  · exact B1490747
  · exact B1490751
  · exact B1490755
  · exact B1490759
  · exact B1490763
  · exact B1490767
  · exact B1490771
  · exact B1490775
  · exact B1490779
  · exact B1490783
  · exact B1490787
  · exact B1490791
  · exact B1490795
  · exact B1490799
  · exact B1490803
  · exact B1490807
  · exact B1490811
  · exact B1490815
  · exact B1490819
  · exact B1490823
  · exact B1490827
  · exact B1490831
  · exact B1490835
  · exact B1490839
  · exact B1490843
  · exact B1490847
  · exact B1490851
  · exact B1490855
  · exact B1490859
  · exact B1490863
  · exact B1490867
  · exact B1490871
  · exact B1490875
  · exact B1490879
  · exact B1490883
  · exact B1490887
  · exact B1490891
  · exact B1490895
  · exact B1490899
  · exact B1490903
  · exact B1490907
  · exact B1490911
  · exact B1490915
  · exact B1490919
  · exact B1490923
  · exact B1490927
  · exact B1490931
  · exact B1490935
  · exact B1490939
  · exact B1490943
  · exact B1490947
  · exact B1490951
  · exact B1490955
  · exact B1490959
  · exact B1490963
  · exact B1490967
  · exact B1490971
  · exact B1490975
  · exact B1490979
  · exact B1490983
  · exact B1490987
  · exact B1490991
  · exact B1490995
  · exact B1490999
  · exact B1491003
  · exact B1491007
  · exact B1491011
  · exact B1491015
  · exact B1491019
  · exact B1491023
  · exact B1491027
  · exact B1491031
  · exact B1491035
  · exact B1491039
  · exact B1491043
  · exact B1491047
  · exact B1491051
  · exact B1491055
  · exact B1491059
  · exact B1491063
  · exact B1491067
  · exact B1491071
  · exact B1491075
  · exact B1491079
  · exact B1491083
  · exact B1491087
  · exact B1491091
  · exact B1491095
  · exact B1491099
  · exact B1491103
  · exact B1491107
  · exact B1491111
  · exact B1491115
  · exact B1491119
  · exact B1491123
  · exact B1491127
  · exact B1491131
  · exact B1491135
  · exact B1491139
  · exact B1491143
  · exact B1491147
  · exact B1491151
  · exact B1491155
  · exact B1491159
  · exact B1491163
  · exact B1491167
  · exact B1491171
  · exact B1491175
  · exact B1491179
  · exact B1491183
  · exact B1491187
  · exact B1491191
  · exact B1491195
  · exact B1491199
  · exact B1491203
  · exact B1491207
  · exact B1491211
  · exact B1491215
  · exact B1491219
  · exact B1491223
  · exact B1491227
  · exact B1491231
  · exact B1491235
  · exact B1491239
  · exact B1491243
  · exact B1491247
  · exact B1491251
  · exact B1491255
  · exact B1491259
  · exact B1491263
  · exact B1491267
  · exact B1491271
  · exact B1491275
  · exact B1491279
  · exact B1491283
  · exact B1491287
  · exact B1491291
  · exact B1491295
  · exact B1491299
  · exact B1491303
  · exact B1491307
  · exact B1491311
  · exact B1491315
  · exact B1491319
  · exact B1491323
  · exact B1491327
  · exact B1491331
  · exact B1491335
  · exact B1491339
  · exact B1491343
  · exact B1491347
  · exact B1491351
  · exact B1491355
  · exact B1491359
  · exact B1491363
  · exact B1491367
  · exact B1491371
  · exact B1491375
  · exact B1491379
  · exact B1491383
  · exact B1491387
  · exact B1491391
  · exact B1491395
  · exact B1491399
  · exact B1491403
  · exact B1491407
  · exact B1491411
  · exact B1491415
  · exact B1491419
  · exact B1491423
  · exact B1491427
  · exact B1491431
  · exact B1491435
  · exact B1491439
  · exact B1491443
  · exact B1491447
  · exact B1491451
  · exact B1491455
  · exact B1491459
  · exact B1491463
  · exact B1491467
  · exact B1491471
  · exact B1491475
  · exact B1491479
  · exact B1491483
  · exact B1491487
  · exact B1491491
  · exact B1491495
  · exact B1491499
  · exact B1491503
  · exact B1491507
  · exact B1491511
  · exact B1491515
  · exact B1491519
  · exact B1491523
  · exact B1491527
  · exact B1491531
  · exact B1491535
  · exact B1491539
  · exact B1491543
  · exact B1491547
  · exact B1491551
  · exact B1491555
  · exact B1491559
  · exact B1491563
  · exact B1491567
  · exact B1491571
  · exact B1491575
  · exact B1491579
  · exact B1491583
  · exact B1491587
  · exact B1491591
  · exact B1491595
  · exact B1491599
  · exact B1491603
  · exact B1491607
  · exact B1491611
  · exact B1491615
  · exact B1491619
  · exact B1491623
  · exact B1491627
  · exact B1491631
  · exact B1491635
  · exact B1491639
  · exact B1491643
  · exact B1491647
  · exact B1491651
  · exact B1491655
  · exact B1491659
  · exact B1491663
  · exact B1491667
  · exact B1491671
  · exact B1491675
  · exact B1491679
  · exact B1491683
  · exact B1491687
  · exact B1491691
  · exact B1491695
  · exact B1491699
  · exact B1491703
  · exact B1491707
  · exact B1491711
  · exact B1491715
  · exact B1491719
  · exact B1491723
  · exact B1491727
  · exact B1491731
  · exact B1491735
  · exact B1491739
  · exact B1491743
  · exact B1491747
  · exact B1491751
  · exact B1491755
  · exact B1491759
  · exact B1491763
  · exact B1491767
  · exact B1491771
  · exact B1491775
  · exact B1491779
  · exact B1491783
  · exact B1491787
  · exact B1491791
  · exact B1491795
  · exact B1491799
  · exact B1491803
  · exact B1491807
  · exact B1491811
  · exact B1491815
  · exact B1491819
  · exact B1491823
  · exact B1491827
  · exact B1491831
  · exact B1491835
  · exact B1491839
  · exact B1491843
  · exact B1491847
  · exact B1491851
  · exact B1491855
  · exact B1491859
  · exact B1491863
  · exact B1491867
  · exact B1491871
  · exact B1491875
  · exact B1491879
  · exact B1491883
  · exact B1491887
  · exact B1491891
  · exact B1491895
  · exact B1491899
  · exact B1491903
  · exact B1491907
  · exact B1491911
  · exact B1491915
  · exact B1491919
  · exact B1491923
  · exact B1491927
  · exact B1491931
  · exact B1491935
  · exact B1491939
  · exact B1491943
  · exact B1491947
  · exact B1491951
  · exact B1491955
  · exact B1491959
  · exact B1491963
  · exact B1491967
  · exact B1491971
  · exact B1491975
  · exact B1491979
  · exact B1491983
  · exact B1491987
  · exact B1491991
  · exact B1491995
  · exact B1491999
  · exact B1492003
  · exact B1492007
  · exact B1492011
  · exact B1492015
  · exact B1492019
  · exact B1492023
  · exact B1492027
  · exact B1492031
  · exact B1492035
  · exact B1492039
  · exact B1492043
  · exact B1492047
  · exact B1492051
  · exact B1492055
  · exact B1492059
  · exact B1492063

theorem solution (m : ℕ) (hlo : 1490065 ≤ m) (hhi : m ≤ 1492065) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 372516 ≤ j := by omega
    have hj2 : j ≤ 373015 := by omega
    have hb : Blo 1490065 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
