-- Prove2me | solution 1 for syracuse_descends_range_1407523_1409523
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:40:57.109984+00:00
-- url     : https://prove2.me/submissions/ba85db10-7373-4395-b66f-463433c37918

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


theorem B2113541 : Blo 1407523 2113541 := bbase (se 4 (by rfl) ⟨198144, by rfl⟩ : syracuseStep 2113541 = 396289) (by norm_num)
theorem B2113565 : Blo 1407523 2113565 := bbase (se 3 (by rfl) ⟨396293, by rfl⟩ : syracuseStep 2113565 = 792587) (by norm_num)
theorem B3170357 : Blo 1407523 3170357 := bbase (se 5 (by rfl) ⟨148610, by rfl⟩ : syracuseStep 3170357 = 297221) (by norm_num)
theorem B2113589 : Blo 1407523 2113589 := bbase (se 5 (by rfl) ⟨99074, by rfl⟩ : syracuseStep 2113589 = 198149) (by norm_num)
theorem B2113613 : Blo 1407523 2113613 := bbase (se 3 (by rfl) ⟨396302, by rfl⟩ : syracuseStep 2113613 = 792605) (by norm_num)
theorem B5079125 : Blo 1407523 5079125 := bbase (se 8 (by rfl) ⟨29760, by rfl⟩ : syracuseStep 5079125 = 59521) (by norm_num)
theorem B2113637 : Blo 1407523 2113637 := bbase (se 4 (by rfl) ⟨198153, by rfl⟩ : syracuseStep 2113637 = 396307) (by norm_num)
theorem B2375797 : Blo 1407523 2375797 := bbase (se 5 (by rfl) ⟨111365, by rfl⟩ : syracuseStep 2375797 = 222731) (by norm_num)
theorem B3170429 : Blo 1407523 3170429 := bbase (se 3 (by rfl) ⟨594455, by rfl⟩ : syracuseStep 3170429 = 1188911) (by norm_num)
theorem B2113661 : Blo 1407523 2113661 := bbase (se 3 (by rfl) ⟨396311, by rfl⟩ : syracuseStep 2113661 = 792623) (by norm_num)
theorem B5349509 : Blo 1407523 5349509 := bbase (se 4 (by rfl) ⟨501516, by rfl⟩ : syracuseStep 5349509 = 1003033) (by norm_num)
theorem B7127189 : Blo 1407523 7127189 := bbase (se 6 (by rfl) ⟨167043, by rfl⟩ : syracuseStep 7127189 = 334087) (by norm_num)
theorem B2113685 : Blo 1407523 2113685 := bbase (se 6 (by rfl) ⟨49539, by rfl⟩ : syracuseStep 2113685 = 99079) (by norm_num)
theorem B2113709 : Blo 1407523 2113709 := bbase (se 3 (by rfl) ⟨396320, by rfl⟩ : syracuseStep 2113709 = 792641) (by norm_num)
theorem B3170501 : Blo 1407523 3170501 := bbase (se 4 (by rfl) ⟨297234, by rfl⟩ : syracuseStep 3170501 = 594469) (by norm_num)
theorem B2113733 : Blo 1407523 2113733 := bbase (se 4 (by rfl) ⟨198162, by rfl⟩ : syracuseStep 2113733 = 396325) (by norm_num)
theorem B2375885 : Blo 1407523 2375885 := bbase (se 3 (by rfl) ⟨445478, by rfl⟩ : syracuseStep 2375885 = 890957) (by norm_num)
theorem B9396437 : Blo 1407523 9396437 := bbase (se 7 (by rfl) ⟨110114, by rfl⟩ : syracuseStep 9396437 = 220229) (by norm_num)
theorem B22839509 : Blo 1407523 22839509 := bbase (se 7 (by rfl) ⟨267650, by rfl⟩ : syracuseStep 22839509 = 535301) (by norm_num)
theorem B2113757 : Blo 1407523 2113757 := bbase (se 3 (by rfl) ⟨396329, by rfl⟩ : syracuseStep 2113757 = 792659) (by norm_num)
theorem B2539757 : Blo 1407523 2539757 := bbase (se 3 (by rfl) ⟨476204, by rfl⟩ : syracuseStep 2539757 = 952409) (by norm_num)
theorem B2113781 : Blo 1407523 2113781 := bbase (se 5 (by rfl) ⟨99083, by rfl⟩ : syracuseStep 2113781 = 198167) (by norm_num)
theorem B4751621 : Blo 1407523 4751621 := bbase (se 4 (by rfl) ⟨445464, by rfl⟩ : syracuseStep 4751621 = 890929) (by norm_num)
theorem B3006733 : Blo 1407523 3006733 := bbase (se 3 (by rfl) ⟨563762, by rfl⟩ : syracuseStep 3006733 = 1127525) (by norm_num)
theorem B3170573 : Blo 1407523 3170573 := bbase (se 3 (by rfl) ⟨594482, by rfl⟩ : syracuseStep 3170573 = 1188965) (by norm_num)
theorem B2113805 : Blo 1407523 2113805 := bbase (se 3 (by rfl) ⟨396338, by rfl⟩ : syracuseStep 2113805 = 792677) (by norm_num)
theorem B3563797 : Blo 1407523 3563797 := bbase (se 6 (by rfl) ⟨83526, by rfl⟩ : syracuseStep 3563797 = 167053) (by norm_num)
theorem B2113829 : Blo 1407523 2113829 := bbase (se 4 (by rfl) ⟨198171, by rfl⟩ : syracuseStep 2113829 = 396343) (by norm_num)
theorem B2113853 : Blo 1407523 2113853 := bbase (se 3 (by rfl) ⟨396347, by rfl⟩ : syracuseStep 2113853 = 792695) (by norm_num)
theorem B2376013 : Blo 1407523 2376013 := bbase (se 3 (by rfl) ⟨445502, by rfl⟩ : syracuseStep 2376013 = 891005) (by norm_num)
theorem B3170645 : Blo 1407523 3170645 := bbase (se 10 (by rfl) ⟨4644, by rfl⟩ : syracuseStep 3170645 = 9289) (by norm_num)
theorem B2113877 : Blo 1407523 2113877 := bbase (se 10 (by rfl) ⟨3096, by rfl⟩ : syracuseStep 2113877 = 6193) (by norm_num)
theorem B2113901 : Blo 1407523 2113901 := bbase (se 3 (by rfl) ⟨396356, by rfl⟩ : syracuseStep 2113901 = 792713) (by norm_num)
theorem B3563909 : Blo 1407523 3563909 := bbase (se 4 (by rfl) ⟨334116, by rfl⟩ : syracuseStep 3563909 = 668233) (by norm_num)
theorem B2113925 : Blo 1407523 2113925 := bbase (se 4 (by rfl) ⟨198180, by rfl⟩ : syracuseStep 2113925 = 396361) (by norm_num)
theorem B3211661 : Blo 1407523 3211661 := bbase (se 3 (by rfl) ⟨602186, by rfl⟩ : syracuseStep 3211661 = 1204373) (by norm_num)
theorem B3170717 : Blo 1407523 3170717 := bbase (se 3 (by rfl) ⟨594509, by rfl⟩ : syracuseStep 3170717 = 1189019) (by norm_num)
theorem B2113949 : Blo 1407523 2113949 := bbase (se 3 (by rfl) ⟨396365, by rfl⟩ : syracuseStep 2113949 = 792731) (by norm_num)
theorem B2376101 : Blo 1407523 2376101 := bbase (se 4 (by rfl) ⟨222759, by rfl⟩ : syracuseStep 2376101 = 445519) (by norm_num)
theorem B5349797 : Blo 1407523 5349797 := bbase (se 4 (by rfl) ⟨501543, by rfl⟩ : syracuseStep 5349797 = 1003087) (by norm_num)
theorem B2113973 : Blo 1407523 2113973 := bbase (se 5 (by rfl) ⟨99092, by rfl⟩ : syracuseStep 2113973 = 198185) (by norm_num)
theorem B2539973 : Blo 1407523 2539973 := bbase (se 4 (by rfl) ⟨238122, by rfl⟩ : syracuseStep 2539973 = 476245) (by norm_num)
theorem B2113997 : Blo 1407523 2113997 := bbase (se 3 (by rfl) ⟨396374, by rfl⟩ : syracuseStep 2113997 = 792749) (by norm_num)
theorem B3170789 : Blo 1407523 3170789 := bbase (se 4 (by rfl) ⟨297261, by rfl⟩ : syracuseStep 3170789 = 594523) (by norm_num)
theorem B2114021 : Blo 1407523 2114021 := bbase (se 4 (by rfl) ⟨198189, by rfl⟩ : syracuseStep 2114021 = 396379) (by norm_num)
theorem B11420149 : Blo 1407523 11420149 := bbase (se 5 (by rfl) ⟨535319, by rfl⟩ : syracuseStep 11420149 = 1070639) (by norm_num)
theorem B2114045 : Blo 1407523 2114045 := bbase (se 3 (by rfl) ⟨396383, by rfl⟩ : syracuseStep 2114045 = 792767) (by norm_num)
theorem B6857237 : Blo 1407523 6857237 := bbase (se 6 (by rfl) ⟨160716, by rfl⟩ : syracuseStep 6857237 = 321433) (by norm_num)
theorem B2114069 : Blo 1407523 2114069 := bbase (se 6 (by rfl) ⟨49548, by rfl⟩ : syracuseStep 2114069 = 99097) (by norm_num)
theorem B2376229 : Blo 1407523 2376229 := bbase (se 4 (by rfl) ⟨222771, by rfl⟩ : syracuseStep 2376229 = 445543) (by norm_num)
theorem B3170861 : Blo 1407523 3170861 := bbase (se 3 (by rfl) ⟨594536, by rfl⟩ : syracuseStep 3170861 = 1189073) (by norm_num)
theorem B2114093 : Blo 1407523 2114093 := bbase (se 3 (by rfl) ⟨396392, by rfl⟩ : syracuseStep 2114093 = 792785) (by norm_num)
theorem B3564101 : Blo 1407523 3564101 := bbase (se 4 (by rfl) ⟨334134, by rfl⟩ : syracuseStep 3564101 = 668269) (by norm_num)
theorem B2114117 : Blo 1407523 2114117 := bbase (se 4 (by rfl) ⟨198198, by rfl⟩ : syracuseStep 2114117 = 396397) (by norm_num)
theorem B2114141 : Blo 1407523 2114141 := bbase (se 3 (by rfl) ⟨396401, by rfl⟩ : syracuseStep 2114141 = 792803) (by norm_num)
theorem B6095477 : Blo 1407523 6095477 := bbase (se 5 (by rfl) ⟨285725, by rfl⟩ : syracuseStep 6095477 = 571451) (by norm_num)
theorem B3170933 : Blo 1407523 3170933 := bbase (se 5 (by rfl) ⟨148637, by rfl⟩ : syracuseStep 3170933 = 297275) (by norm_num)
theorem B2114165 : Blo 1407523 2114165 := bbase (se 5 (by rfl) ⟨99101, by rfl⟩ : syracuseStep 2114165 = 198203) (by norm_num)
theorem B2376317 : Blo 1407523 2376317 := bbase (se 3 (by rfl) ⟨445559, by rfl⟩ : syracuseStep 2376317 = 891119) (by norm_num)
theorem B2114189 : Blo 1407523 2114189 := bbase (se 3 (by rfl) ⟨396410, by rfl⟩ : syracuseStep 2114189 = 792821) (by norm_num)
theorem B2114213 : Blo 1407523 2114213 := bbase (se 4 (by rfl) ⟨198207, by rfl⟩ : syracuseStep 2114213 = 396415) (by norm_num)
theorem B4752053 : Blo 1407523 4752053 := bbase (se 5 (by rfl) ⟨222752, by rfl⟩ : syracuseStep 4752053 = 445505) (by norm_num)
theorem B3171005 : Blo 1407523 3171005 := bbase (se 3 (by rfl) ⟨594563, by rfl⟩ : syracuseStep 3171005 = 1189127) (by norm_num)
theorem B2114237 : Blo 1407523 2114237 := bbase (se 3 (by rfl) ⟨396419, by rfl⟩ : syracuseStep 2114237 = 792839) (by norm_num)
theorem B2032333 : Blo 1407523 2032333 := bbase (se 3 (by rfl) ⟨381062, by rfl⟩ : syracuseStep 2032333 = 762125) (by norm_num)
theorem B2114261 : Blo 1407523 2114261 := bbase (se 7 (by rfl) ⟨24776, by rfl⟩ : syracuseStep 2114261 = 49553) (by norm_num)
theorem B2114285 : Blo 1407523 2114285 := bbase (se 3 (by rfl) ⟨396428, by rfl⟩ : syracuseStep 2114285 = 792857) (by norm_num)
theorem B2376445 : Blo 1407523 2376445 := bbase (se 3 (by rfl) ⟨445583, by rfl⟩ : syracuseStep 2376445 = 891167) (by norm_num)
theorem B7226117 : Blo 1407523 7226117 := bbase (se 4 (by rfl) ⟨677448, by rfl⟩ : syracuseStep 7226117 = 1354897) (by norm_num)
theorem B3171077 : Blo 1407523 3171077 := bbase (se 4 (by rfl) ⟨297288, by rfl⟩ : syracuseStep 3171077 = 594577) (by norm_num)
theorem B3212045 : Blo 1407523 3212045 := bbase (se 3 (by rfl) ⟨602258, by rfl⟩ : syracuseStep 3212045 = 1204517) (by norm_num)
theorem B5079829 : Blo 1407523 5079829 := bbase (se 6 (by rfl) ⟨119058, by rfl⟩ : syracuseStep 5079829 = 238117) (by norm_num)
theorem B2409293 : Blo 1407523 2409293 := bbase (se 3 (by rfl) ⟨451742, by rfl⟩ : syracuseStep 2409293 = 903485) (by norm_num)
theorem B3171149 : Blo 1407523 3171149 := bbase (se 3 (by rfl) ⟨594590, by rfl⟩ : syracuseStep 3171149 = 1189181) (by norm_num)
theorem B2376533 : Blo 1407523 2376533 := bbase (se 9 (by rfl) ⟨6962, by rfl⟩ : syracuseStep 2376533 = 13925) (by norm_num)
theorem B3171221 : Blo 1407523 3171221 := bbase (se 6 (by rfl) ⟨74325, by rfl⟩ : syracuseStep 3171221 = 148651) (by norm_num)
theorem B3564445 : Blo 1407523 3564445 := bbase (se 3 (by rfl) ⟨668333, by rfl⟩ : syracuseStep 3564445 = 1336667) (by norm_num)
theorem B2376661 : Blo 1407523 2376661 := bbase (se 7 (by rfl) ⟨27851, by rfl⟩ : syracuseStep 2376661 = 55703) (by norm_num)
theorem B3171293 : Blo 1407523 3171293 := bbase (se 3 (by rfl) ⟨594617, by rfl⟩ : syracuseStep 3171293 = 1189235) (by norm_num)
theorem B3564557 : Blo 1407523 3564557 := bbase (se 3 (by rfl) ⟨668354, by rfl⟩ : syracuseStep 3564557 = 1336709) (by norm_num)
theorem B3171365 : Blo 1407523 3171365 := bbase (se 4 (by rfl) ⟨297315, by rfl⟩ : syracuseStep 3171365 = 594631) (by norm_num)
theorem B2376749 : Blo 1407523 2376749 := bbase (se 3 (by rfl) ⟨445640, by rfl⟩ : syracuseStep 2376749 = 891281) (by norm_num)
theorem B4752485 : Blo 1407523 4752485 := bbase (se 4 (by rfl) ⟨445545, by rfl⟩ : syracuseStep 4752485 = 891091) (by norm_num)
theorem B3007621 : Blo 1407523 3007621 := bbase (se 4 (by rfl) ⟨281964, by rfl⟩ : syracuseStep 3007621 = 563929) (by norm_num)
theorem B2376877 : Blo 1407523 2376877 := bbase (se 3 (by rfl) ⟨445664, by rfl⟩ : syracuseStep 2376877 = 891329) (by norm_num)
theorem B3564749 : Blo 1407523 3564749 := bbase (se 3 (by rfl) ⟨668390, by rfl⟩ : syracuseStep 3564749 = 1336781) (by norm_num)
theorem B2376965 : Blo 1407523 2376965 := bbase (se 4 (by rfl) ⟨222840, by rfl⟩ : syracuseStep 2376965 = 445681) (by norm_num)
theorem B2377093 : Blo 1407523 2377093 := bbase (se 4 (by rfl) ⟨222852, by rfl⟩ : syracuseStep 2377093 = 445705) (by norm_num)
theorem B7128485 : Blo 1407523 7128485 := bbase (se 4 (by rfl) ⟨668295, by rfl⟩ : syracuseStep 7128485 = 1336591) (by norm_num)
theorem B1525169 : Blo 1407523 1525169 := bbase (se 2 (by rfl) ⟨571938, by rfl⟩ : syracuseStep 1525169 = 1143877) (by norm_num)
theorem B2377181 : Blo 1407523 2377181 := bbase (se 3 (by rfl) ⟨445721, by rfl⟩ : syracuseStep 2377181 = 891443) (by norm_num)
theorem B4515301 : Blo 1407523 4515301 := bbase (se 4 (by rfl) ⟨423309, by rfl⟩ : syracuseStep 4515301 = 846619) (by norm_num)
theorem B4752917 : Blo 1407523 4752917 := bbase (se 6 (by rfl) ⟨111396, by rfl⟩ : syracuseStep 4752917 = 222793) (by norm_num)
theorem B2672165 : Blo 1407523 2672165 := bbase (se 4 (by rfl) ⟨250515, by rfl⟩ : syracuseStep 2672165 = 501031) (by norm_num)
theorem B2745893 : Blo 1407523 2745893 := bbase (se 4 (by rfl) ⟨257427, by rfl⟩ : syracuseStep 2745893 = 514855) (by norm_num)
theorem B3565093 : Blo 1407523 3565093 := bbase (se 4 (by rfl) ⟨334227, by rfl⟩ : syracuseStep 3565093 = 668455) (by norm_num)
theorem B2573869 : Blo 1407523 2573869 := bbase (se 3 (by rfl) ⟨482600, by rfl⟩ : syracuseStep 2573869 = 965201) (by norm_num)
theorem B5350981 : Blo 1407523 5350981 := bbase (se 4 (by rfl) ⟨501654, by rfl⟩ : syracuseStep 5350981 = 1003309) (by norm_num)
theorem B2377309 : Blo 1407523 2377309 := bbase (se 3 (by rfl) ⟨445745, by rfl⟩ : syracuseStep 2377309 = 891491) (by norm_num)
theorem B3008117 : Blo 1407523 3008117 := bbase (se 5 (by rfl) ⟨141005, by rfl⟩ : syracuseStep 3008117 = 282011) (by norm_num)
theorem B3565205 : Blo 1407523 3565205 := bbase (se 6 (by rfl) ⟨83559, by rfl⟩ : syracuseStep 3565205 = 167119) (by norm_num)
theorem B6014645 : Blo 1407523 6014645 := bbase (se 5 (by rfl) ⟨281936, by rfl⟩ : syracuseStep 6014645 = 563873) (by norm_num)
theorem B2377397 : Blo 1407523 2377397 := bbase (se 5 (by rfl) ⟨111440, by rfl⟩ : syracuseStep 2377397 = 222881) (by norm_num)
theorem B2377525 : Blo 1407523 2377525 := bbase (se 5 (by rfl) ⟨111446, by rfl⟩ : syracuseStep 2377525 = 222893) (by norm_num)
theorem B2672453 : Blo 1407523 2672453 := bbase (se 4 (by rfl) ⟨250542, by rfl⟩ : syracuseStep 2672453 = 501085) (by norm_num)
theorem B3565397 : Blo 1407523 3565397 := bbase (se 9 (by rfl) ⟨10445, by rfl⟩ : syracuseStep 3565397 = 20891) (by norm_num)
theorem B3614557 : Blo 1407523 3614557 := bbase (se 3 (by rfl) ⟨677729, by rfl⟩ : syracuseStep 3614557 = 1355459) (by norm_num)
theorem B6096757 : Blo 1407523 6096757 := bbase (se 5 (by rfl) ⟨285785, by rfl⟩ : syracuseStep 6096757 = 571571) (by norm_num)
theorem B5351285 : Blo 1407523 5351285 := bbase (se 5 (by rfl) ⟨250841, by rfl⟩ : syracuseStep 5351285 = 501683) (by norm_num)
theorem B3663749 : Blo 1407523 3663749 := bbase (se 4 (by rfl) ⟨343476, by rfl⟩ : syracuseStep 3663749 = 686953) (by norm_num)
theorem B2377613 : Blo 1407523 2377613 := bbase (se 3 (by rfl) ⟨445802, by rfl⟩ : syracuseStep 2377613 = 891605) (by norm_num)
theorem B4753349 : Blo 1407523 4753349 := bbase (se 4 (by rfl) ⟨445626, by rfl⟩ : syracuseStep 4753349 = 891253) (by norm_num)
theorem B2672605 : Blo 1407523 2672605 := bbase (se 3 (by rfl) ⟨501113, by rfl⟩ : syracuseStep 2672605 = 1002227) (by norm_num)
theorem B6768629 : Blo 1407523 6768629 := bbase (se 5 (by rfl) ⟨317279, by rfl⟩ : syracuseStep 6768629 = 634559) (by norm_num)
theorem B2377741 : Blo 1407523 2377741 := bbase (se 3 (by rfl) ⟨445826, by rfl⟩ : syracuseStep 2377741 = 891653) (by norm_num)
theorem B9635861 : Blo 1407523 9635861 := bbase (se 6 (by rfl) ⟨225840, by rfl⟩ : syracuseStep 9635861 = 451681) (by norm_num)
theorem B3213341 : Blo 1407523 3213341 := bbase (se 3 (by rfl) ⟨602501, by rfl⟩ : syracuseStep 3213341 = 1205003) (by norm_num)
theorem B2377829 : Blo 1407523 2377829 := bbase (se 4 (by rfl) ⟨222921, by rfl⟩ : syracuseStep 2377829 = 445843) (by norm_num)
theorem B9021557 : Blo 1407523 9021557 := bbase (se 5 (by rfl) ⟨422885, by rfl⟩ : syracuseStep 9021557 = 845771) (by norm_num)
theorem B3385469 : Blo 1407523 3385469 := bbase (se 3 (by rfl) ⟨634775, by rfl⟩ : syracuseStep 3385469 = 1269551) (by norm_num)
theorem B3565741 : Blo 1407523 3565741 := bbase (se 3 (by rfl) ⟨668576, by rfl⟩ : syracuseStep 3565741 = 1337153) (by norm_num)
theorem B2377957 : Blo 1407523 2377957 := bbase (se 4 (by rfl) ⟨222933, by rfl⟩ : syracuseStep 2377957 = 445867) (by norm_num)
theorem B2672909 : Blo 1407523 2672909 := bbase (se 3 (by rfl) ⟨501170, by rfl⟩ : syracuseStep 2672909 = 1002341) (by norm_num)
theorem B3565853 : Blo 1407523 3565853 := bbase (se 3 (by rfl) ⟨668597, by rfl⟩ : syracuseStep 3565853 = 1337195) (by norm_num)
theorem B2378045 : Blo 1407523 2378045 := bbase (se 3 (by rfl) ⟨445883, by rfl⟩ : syracuseStep 2378045 = 891767) (by norm_num)
theorem B1583473 : Blo 1407523 1583473 := bbase (se 2 (by rfl) ⟨593802, by rfl⟩ : syracuseStep 1583473 = 1187605) (by norm_num)
theorem B4753781 : Blo 1407523 4753781 := bbase (se 5 (by rfl) ⟨222833, by rfl⟩ : syracuseStep 4753781 = 445667) (by norm_num)
theorem B1583509 : Blo 1407523 1583509 := bbase (se 6 (by rfl) ⟨37113, by rfl⟩ : syracuseStep 1583509 = 74227) (by norm_num)
theorem B3049877 : Blo 1407523 3049877 := bbase (se 6 (by rfl) ⟨71481, by rfl⟩ : syracuseStep 3049877 = 142963) (by norm_num)
theorem B1583545 : Blo 1407523 1583545 := bbase (se 2 (by rfl) ⟨593829, by rfl⟩ : syracuseStep 1583545 = 1187659) (by norm_num)
theorem B2255293 : Blo 1407523 2255293 := bbase (se 3 (by rfl) ⟨422867, by rfl⟩ : syracuseStep 2255293 = 845735) (by norm_num)
theorem B2378173 : Blo 1407523 2378173 := bbase (se 3 (by rfl) ⟨445907, by rfl⟩ : syracuseStep 2378173 = 891815) (by norm_num)
theorem B6097349 : Blo 1407523 6097349 := bbase (se 4 (by rfl) ⟨571626, by rfl⟩ : syracuseStep 6097349 = 1143253) (by norm_num)
theorem B1583581 : Blo 1407523 1583581 := bbase (se 3 (by rfl) ⟨296921, by rfl⟩ : syracuseStep 1583581 = 593843) (by norm_num)
theorem B3566045 : Blo 1407523 3566045 := bbase (se 3 (by rfl) ⟨668633, by rfl⟩ : syracuseStep 3566045 = 1337267) (by norm_num)
theorem B3009005 : Blo 1407523 3009005 := bbase (se 3 (by rfl) ⟨564188, by rfl⟩ : syracuseStep 3009005 = 1128377) (by norm_num)
theorem B3385853 : Blo 1407523 3385853 := bbase (se 3 (by rfl) ⟨634847, by rfl⟩ : syracuseStep 3385853 = 1269695) (by norm_num)
theorem B1583617 : Blo 1407523 1583617 := bbase (se 2 (by rfl) ⟨593856, by rfl⟩ : syracuseStep 1583617 = 1187713) (by norm_num)
theorem B24078869 : Blo 1407523 24078869 := bbase (se 6 (by rfl) ⟨564348, by rfl⟩ : syracuseStep 24078869 = 1128697) (by norm_num)
theorem B2378261 : Blo 1407523 2378261 := bbase (se 6 (by rfl) ⟨55740, by rfl⟩ : syracuseStep 2378261 = 111481) (by norm_num)
theorem B1583653 : Blo 1407523 1583653 := bbase (se 4 (by rfl) ⟨148467, by rfl⟩ : syracuseStep 1583653 = 296935) (by norm_num)
theorem B1583689 : Blo 1407523 1583689 := bbase (se 2 (by rfl) ⟨593883, by rfl⟩ : syracuseStep 1583689 = 1187767) (by norm_num)
theorem B3009125 : Blo 1407523 3009125 := bbase (se 4 (by rfl) ⟨282105, by rfl⟩ : syracuseStep 3009125 = 564211) (by norm_num)
theorem B1583725 : Blo 1407523 1583725 := bbase (se 3 (by rfl) ⟨296948, by rfl⟩ : syracuseStep 1583725 = 593897) (by norm_num)
theorem B1583761 : Blo 1407523 1583761 := bbase (se 2 (by rfl) ⟨593910, by rfl⟩ : syracuseStep 1583761 = 1187821) (by norm_num)
theorem B2378389 : Blo 1407523 2378389 := bbase (se 6 (by rfl) ⟨55743, by rfl⟩ : syracuseStep 2378389 = 111487) (by norm_num)
theorem B6015653 : Blo 1407523 6015653 := bbase (se 4 (by rfl) ⟨563967, by rfl⟩ : syracuseStep 6015653 = 1127935) (by norm_num)
theorem B1583797 : Blo 1407523 1583797 := bbase (se 5 (by rfl) ⟨74240, by rfl⟩ : syracuseStep 1583797 = 148481) (by norm_num)
theorem B7129781 : Blo 1407523 7129781 := bbase (se 5 (by rfl) ⟨334208, by rfl⟩ : syracuseStep 7129781 = 668417) (by norm_num)
theorem B3386053 : Blo 1407523 3386053 := bbase (se 4 (by rfl) ⟨317442, by rfl⟩ : syracuseStep 3386053 = 634885) (by norm_num)
theorem B1583833 : Blo 1407523 1583833 := bbase (se 2 (by rfl) ⟨593937, by rfl⟩ : syracuseStep 1583833 = 1187875) (by norm_num)
theorem B2378477 : Blo 1407523 2378477 := bbase (se 3 (by rfl) ⟨445964, by rfl⟩ : syracuseStep 2378477 = 891929) (by norm_num)
theorem B1583869 : Blo 1407523 1583869 := bbase (se 3 (by rfl) ⟨296975, by rfl⟩ : syracuseStep 1583869 = 593951) (by norm_num)
theorem B1583905 : Blo 1407523 1583905 := bbase (se 2 (by rfl) ⟨593964, by rfl⟩ : syracuseStep 1583905 = 1187929) (by norm_num)
theorem B4754213 : Blo 1407523 4754213 := bbase (se 4 (by rfl) ⟨445707, by rfl⟩ : syracuseStep 4754213 = 891415) (by norm_num)
theorem B3566389 : Blo 1407523 3566389 := bbase (se 5 (by rfl) ⟨167174, by rfl⟩ : syracuseStep 3566389 = 334349) (by norm_num)
theorem B1428277 : Blo 1407523 1428277 := bbase (se 5 (by rfl) ⟨66950, by rfl⟩ : syracuseStep 1428277 = 133901) (by norm_num)
theorem B1583941 : Blo 1407523 1583941 := bbase (se 4 (by rfl) ⟨148494, by rfl⟩ : syracuseStep 1583941 = 296989) (by norm_num)
theorem B1583977 : Blo 1407523 1583977 := bbase (se 2 (by rfl) ⟨593991, by rfl⟩ : syracuseStep 1583977 = 1187983) (by norm_num)
theorem B1584013 : Blo 1407523 1584013 := bbase (se 3 (by rfl) ⟨297002, by rfl⟩ : syracuseStep 1584013 = 594005) (by norm_num)
theorem B3566501 : Blo 1407523 3566501 := bbase (se 4 (by rfl) ⟨334359, by rfl⟩ : syracuseStep 3566501 = 668719) (by norm_num)
theorem B2853805 : Blo 1407523 2853805 := bbase (se 3 (by rfl) ⟨535088, by rfl⟩ : syracuseStep 2853805 = 1070177) (by norm_num)
theorem B1584049 : Blo 1407523 1584049 := bbase (se 2 (by rfl) ⟨594018, by rfl⟩ : syracuseStep 1584049 = 1188037) (by norm_num)
theorem B1584085 : Blo 1407523 1584085 := bbase (se 7 (by rfl) ⟨18563, by rfl⟩ : syracuseStep 1584085 = 37127) (by norm_num)
theorem B1584121 : Blo 1407523 1584121 := bbase (se 2 (by rfl) ⟨594045, by rfl⟩ : syracuseStep 1584121 = 1188091) (by norm_num)
theorem B2673661 : Blo 1407523 2673661 := bbase (se 3 (by rfl) ⟨501311, by rfl⟩ : syracuseStep 2673661 = 1002623) (by norm_num)
theorem B2853901 : Blo 1407523 2853901 := bbase (se 3 (by rfl) ⟨535106, by rfl⟩ : syracuseStep 2853901 = 1070213) (by norm_num)
theorem B1584157 : Blo 1407523 1584157 := bbase (se 3 (by rfl) ⟨297029, by rfl⟩ : syracuseStep 1584157 = 594059) (by norm_num)
theorem B9767989 : Blo 1407523 9767989 := bbase (se 5 (by rfl) ⟨457874, by rfl⟩ : syracuseStep 9767989 = 915749) (by norm_num)
theorem B1584193 : Blo 1407523 1584193 := bbase (se 2 (by rfl) ⟨594072, by rfl⟩ : syracuseStep 1584193 = 1188145) (by norm_num)
theorem B1584229 : Blo 1407523 1584229 := bbase (se 4 (by rfl) ⟨148521, by rfl⟩ : syracuseStep 1584229 = 297043) (by norm_num)
theorem B3566693 : Blo 1407523 3566693 := bbase (se 4 (by rfl) ⟨334377, by rfl⟩ : syracuseStep 3566693 = 668755) (by norm_num)
theorem B3050597 : Blo 1407523 3050597 := bbase (se 4 (by rfl) ⟨285993, by rfl⟩ : syracuseStep 3050597 = 571987) (by norm_num)
theorem B1428581 : Blo 1407523 1428581 := bbase (se 4 (by rfl) ⟨133929, by rfl⟩ : syracuseStep 1428581 = 267859) (by norm_num)
theorem B2256005 : Blo 1407523 2256005 := bbase (se 4 (by rfl) ⟨211500, by rfl⟩ : syracuseStep 2256005 = 423001) (by norm_num)
theorem B1584265 : Blo 1407523 1584265 := bbase (se 2 (by rfl) ⟨594099, by rfl⟩ : syracuseStep 1584265 = 1188199) (by norm_num)
theorem B2673805 : Blo 1407523 2673805 := bbase (se 3 (by rfl) ⟨501338, by rfl⟩ : syracuseStep 2673805 = 1002677) (by norm_num)
theorem B1584301 : Blo 1407523 1584301 := bbase (se 3 (by rfl) ⟨297056, by rfl⟩ : syracuseStep 1584301 = 594113) (by norm_num)
theorem B1584337 : Blo 1407523 1584337 := bbase (se 2 (by rfl) ⟨594126, by rfl⟩ : syracuseStep 1584337 = 1188253) (by norm_num)
theorem B18541781 : Blo 1407523 18541781 := bbase (se 7 (by rfl) ⟨217286, by rfl⟩ : syracuseStep 18541781 = 434573) (by norm_num)
theorem B27446485 : Blo 1407523 27446485 := bbase (se 7 (by rfl) ⟨321638, by rfl⟩ : syracuseStep 27446485 = 643277) (by norm_num)
theorem B4754645 : Blo 1407523 4754645 := bbase (se 7 (by rfl) ⟨55718, by rfl⟩ : syracuseStep 4754645 = 111437) (by norm_num)
theorem B3009757 : Blo 1407523 3009757 := bbase (se 3 (by rfl) ⟨564329, by rfl⟩ : syracuseStep 3009757 = 1128659) (by norm_num)
theorem B1584373 : Blo 1407523 1584373 := bbase (se 5 (by rfl) ⟨74267, by rfl⟩ : syracuseStep 1584373 = 148535) (by norm_num)
theorem B1584409 : Blo 1407523 1584409 := bbase (se 2 (by rfl) ⟨594153, by rfl⟩ : syracuseStep 1584409 = 1188307) (by norm_num)
theorem B2673965 : Blo 1407523 2673965 := bbase (se 3 (by rfl) ⟨501368, by rfl⟩ : syracuseStep 2673965 = 1002737) (by norm_num)
theorem B1584445 : Blo 1407523 1584445 := bbase (se 3 (by rfl) ⟨297083, by rfl⟩ : syracuseStep 1584445 = 594167) (by norm_num)
theorem B1584481 : Blo 1407523 1584481 := bbase (se 2 (by rfl) ⟨594180, by rfl⟩ : syracuseStep 1584481 = 1188361) (by norm_num)
theorem B1903981 : Blo 1407523 1903981 := bbase (se 3 (by rfl) ⟨356996, by rfl⟩ : syracuseStep 1903981 = 713993) (by norm_num)
theorem B1584517 : Blo 1407523 1584517 := bbase (se 4 (by rfl) ⟨148548, by rfl⟩ : syracuseStep 1584517 = 297097) (by norm_num)
theorem B1584553 : Blo 1407523 1584553 := bbase (se 2 (by rfl) ⟨594207, by rfl⟩ : syracuseStep 1584553 = 1188415) (by norm_num)
theorem B2674109 : Blo 1407523 2674109 := bbase (se 3 (by rfl) ⟨501395, by rfl⟩ : syracuseStep 2674109 = 1002791) (by norm_num)
theorem B3567037 : Blo 1407523 3567037 := bbase (se 3 (by rfl) ⟨668819, by rfl⟩ : syracuseStep 3567037 = 1337639) (by norm_num)
theorem B1584589 : Blo 1407523 1584589 := bbase (se 3 (by rfl) ⟨297110, by rfl⟩ : syracuseStep 1584589 = 594221) (by norm_num)
theorem B1584625 : Blo 1407523 1584625 := bbase (se 2 (by rfl) ⟨594234, by rfl⟩ : syracuseStep 1584625 = 1188469) (by norm_num)
theorem B1584661 : Blo 1407523 1584661 := bbase (se 6 (by rfl) ⟨37140, by rfl⟩ : syracuseStep 1584661 = 74281) (by norm_num)
theorem B13544981 : Blo 1407523 13544981 := bbase (se 6 (by rfl) ⟨317460, by rfl⟩ : syracuseStep 13544981 = 634921) (by norm_num)
theorem B3567149 : Blo 1407523 3567149 := bbase (se 3 (by rfl) ⟨668840, by rfl⟩ : syracuseStep 3567149 = 1337681) (by norm_num)
theorem B1584697 : Blo 1407523 1584697 := bbase (se 2 (by rfl) ⟨594261, by rfl⟩ : syracuseStep 1584697 = 1188523) (by norm_num)
theorem B1584733 : Blo 1407523 1584733 := bbase (se 3 (by rfl) ⟨297137, by rfl⟩ : syracuseStep 1584733 = 594275) (by norm_num)
theorem B1584769 : Blo 1407523 1584769 := bbase (se 2 (by rfl) ⟨594288, by rfl⟩ : syracuseStep 1584769 = 1188577) (by norm_num)
theorem B4755077 : Blo 1407523 4755077 := bbase (se 4 (by rfl) ⟨445788, by rfl⟩ : syracuseStep 4755077 = 891577) (by norm_num)
theorem B1805981 : Blo 1407523 1805981 := bbase (se 3 (by rfl) ⟨338621, by rfl⟩ : syracuseStep 1805981 = 677243) (by norm_num)
theorem B4009637 : Blo 1407523 4009637 := bbase (se 4 (by rfl) ⟨375903, by rfl⟩ : syracuseStep 4009637 = 751807) (by norm_num)
theorem B1584805 : Blo 1407523 1584805 := bbase (se 4 (by rfl) ⟨148575, by rfl⟩ : syracuseStep 1584805 = 297151) (by norm_num)
theorem B1584841 : Blo 1407523 1584841 := bbase (se 2 (by rfl) ⟨594315, by rfl⟩ : syracuseStep 1584841 = 1188631) (by norm_num)
theorem B1781453 : Blo 1407523 1781453 := bbase (se 3 (by rfl) ⟨334022, by rfl⟩ : syracuseStep 1781453 = 668045) (by norm_num)
theorem B1928909 : Blo 1407523 1928909 := bbase (se 3 (by rfl) ⟨361670, by rfl⟩ : syracuseStep 1928909 = 723341) (by norm_num)
theorem B2674397 : Blo 1407523 2674397 := bbase (se 3 (by rfl) ⟨501449, by rfl⟩ : syracuseStep 2674397 = 1002899) (by norm_num)
theorem B1584877 : Blo 1407523 1584877 := bbase (se 3 (by rfl) ⟨297164, by rfl⟩ : syracuseStep 1584877 = 594329) (by norm_num)
theorem B3567341 : Blo 1407523 3567341 := bbase (se 3 (by rfl) ⟨668876, by rfl⟩ : syracuseStep 3567341 = 1337753) (by norm_num)
theorem B1781509 : Blo 1407523 1781509 := bbase (se 4 (by rfl) ⟨167016, by rfl⟩ : syracuseStep 1781509 = 334033) (by norm_num)
theorem B1584913 : Blo 1407523 1584913 := bbase (se 2 (by rfl) ⟨594342, by rfl⟩ : syracuseStep 1584913 = 1188685) (by norm_num)
theorem B3804965 : Blo 1407523 3804965 := bbase (se 4 (by rfl) ⟨356715, by rfl⟩ : syracuseStep 3804965 = 713431) (by norm_num)
theorem B2256677 : Blo 1407523 2256677 := bbase (se 4 (by rfl) ⟨211563, by rfl⟩ : syracuseStep 2256677 = 423127) (by norm_num)
theorem B1904429 : Blo 1407523 1904429 := bbase (se 3 (by rfl) ⟨357080, by rfl⟩ : syracuseStep 1904429 = 714161) (by norm_num)
theorem B1584949 : Blo 1407523 1584949 := bbase (se 5 (by rfl) ⟨74294, by rfl⟩ : syracuseStep 1584949 = 148589) (by norm_num)
theorem B1806149 : Blo 1407523 1806149 := bbase (se 4 (by rfl) ⟨169326, by rfl⟩ : syracuseStep 1806149 = 338653) (by norm_num)
theorem B5074757 : Blo 1407523 5074757 := bbase (se 4 (by rfl) ⟨475758, by rfl⟩ : syracuseStep 5074757 = 951517) (by norm_num)
theorem B4575061 : Blo 1407523 4575061 := bbase (se 9 (by rfl) ⟨13403, by rfl⟩ : syracuseStep 4575061 = 26807) (by norm_num)
theorem B1584985 : Blo 1407523 1584985 := bbase (se 2 (by rfl) ⟨594369, by rfl⟩ : syracuseStep 1584985 = 1188739) (by norm_num)
theorem B1691489 : Blo 1407523 1691489 := bbase (se 2 (by rfl) ⟨634308, by rfl⟩ : syracuseStep 1691489 = 1268617) (by norm_num)
theorem B1781605 : Blo 1407523 1781605 := bbase (se 4 (by rfl) ⟨167025, by rfl⟩ : syracuseStep 1781605 = 334051) (by norm_num)
theorem B2674549 : Blo 1407523 2674549 := bbase (se 5 (by rfl) ⟨125369, by rfl⟩ : syracuseStep 2674549 = 250739) (by norm_num)
theorem B1929085 : Blo 1407523 1929085 := bbase (se 3 (by rfl) ⟨361703, by rfl⟩ : syracuseStep 1929085 = 723407) (by norm_num)
theorem B1585021 : Blo 1407523 1585021 := bbase (se 3 (by rfl) ⟨297191, by rfl⟩ : syracuseStep 1585021 = 594383) (by norm_num)
theorem B4820885 : Blo 1407523 4820885 := bbase (se 6 (by rfl) ⟨112989, by rfl⟩ : syracuseStep 4820885 = 225979) (by norm_num)
theorem B1585057 : Blo 1407523 1585057 := bbase (se 2 (by rfl) ⟨594396, by rfl⟩ : syracuseStep 1585057 = 1188793) (by norm_num)
theorem B7131077 : Blo 1407523 7131077 := bbase (se 4 (by rfl) ⟨668538, by rfl⟩ : syracuseStep 7131077 = 1337077) (by norm_num)
theorem B1585093 : Blo 1407523 1585093 := bbase (se 4 (by rfl) ⟨148602, by rfl⟩ : syracuseStep 1585093 = 297205) (by norm_num)
theorem B6770645 : Blo 1407523 6770645 := bbase (se 7 (by rfl) ⟨79343, by rfl⟩ : syracuseStep 6770645 = 158687) (by norm_num)
theorem B1585129 : Blo 1407523 1585129 := bbase (se 2 (by rfl) ⟨594423, by rfl⟩ : syracuseStep 1585129 = 1188847) (by norm_num)
theorem B1585165 : Blo 1407523 1585165 := bbase (se 3 (by rfl) ⟨297218, by rfl⟩ : syracuseStep 1585165 = 594437) (by norm_num)
theorem B1781777 : Blo 1407523 1781777 := bbase (se 2 (by rfl) ⟨668166, by rfl⟩ : syracuseStep 1781777 = 1336333) (by norm_num)
theorem B1585201 : Blo 1407523 1585201 := bbase (se 2 (by rfl) ⟨594450, by rfl⟩ : syracuseStep 1585201 = 1188901) (by norm_num)
theorem B4755509 : Blo 1407523 4755509 := bbase (se 5 (by rfl) ⟨222914, by rfl⟩ : syracuseStep 4755509 = 445829) (by norm_num)
theorem B3567685 : Blo 1407523 3567685 := bbase (se 4 (by rfl) ⟨334470, by rfl⟩ : syracuseStep 3567685 = 668941) (by norm_num)
theorem B1781833 : Blo 1407523 1781833 := bbase (se 2 (by rfl) ⟨668187, by rfl⟩ : syracuseStep 1781833 = 1336375) (by norm_num)
theorem B2854997 : Blo 1407523 2854997 := bbase (se 8 (by rfl) ⟨16728, by rfl⟩ : syracuseStep 2854997 = 33457) (by norm_num)
theorem B1585237 : Blo 1407523 1585237 := bbase (se 8 (by rfl) ⟨9288, by rfl⟩ : syracuseStep 1585237 = 18577) (by norm_num)
theorem B1585273 : Blo 1407523 1585273 := bbase (se 2 (by rfl) ⟨594477, by rfl⟩ : syracuseStep 1585273 = 1188955) (by norm_num)
theorem B1585309 : Blo 1407523 1585309 := bbase (se 3 (by rfl) ⟨297245, by rfl⟩ : syracuseStep 1585309 = 594491) (by norm_num)
theorem B2674853 : Blo 1407523 2674853 := bbase (se 4 (by rfl) ⟨250767, by rfl⟩ : syracuseStep 2674853 = 501535) (by norm_num)
theorem B1781929 : Blo 1407523 1781929 := bbase (se 2 (by rfl) ⟨668223, by rfl⟩ : syracuseStep 1781929 = 1336447) (by norm_num)
theorem B1503409 : Blo 1407523 1503409 := bbase (se 2 (by rfl) ⟨563778, by rfl⟩ : syracuseStep 1503409 = 1127557) (by norm_num)
theorem B3567797 : Blo 1407523 3567797 := bbase (se 5 (by rfl) ⟨167240, by rfl⟩ : syracuseStep 3567797 = 334481) (by norm_num)
theorem B1585345 : Blo 1407523 1585345 := bbase (se 2 (by rfl) ⟨594504, by rfl⟩ : syracuseStep 1585345 = 1189009) (by norm_num)
theorem B1585381 : Blo 1407523 1585381 := bbase (se 4 (by rfl) ⟨148629, by rfl⟩ : syracuseStep 1585381 = 297259) (by norm_num)
theorem B1503469 : Blo 1407523 1503469 := bbase (se 3 (by rfl) ⟨281900, by rfl⟩ : syracuseStep 1503469 = 563801) (by norm_num)
theorem B1585417 : Blo 1407523 1585417 := bbase (se 2 (by rfl) ⟨594531, by rfl⟩ : syracuseStep 1585417 = 1189063) (by norm_num)
theorem B2257189 : Blo 1407523 2257189 := bbase (se 4 (by rfl) ⟨211611, by rfl⟩ : syracuseStep 2257189 = 423223) (by norm_num)
theorem B1585453 : Blo 1407523 1585453 := bbase (se 3 (by rfl) ⟨297272, by rfl⟩ : syracuseStep 1585453 = 594545) (by norm_num)
theorem B1585489 : Blo 1407523 1585489 := bbase (se 2 (by rfl) ⟨594558, by rfl⟩ : syracuseStep 1585489 = 1189117) (by norm_num)
theorem B5345621 : Blo 1407523 5345621 := bbase (se 10 (by rfl) ⟨7830, by rfl⟩ : syracuseStep 5345621 = 15661) (by norm_num)
theorem B1782101 : Blo 1407523 1782101 := bbase (se 10 (by rfl) ⟨2610, by rfl⟩ : syracuseStep 1782101 = 5221) (by norm_num)
theorem B1585525 : Blo 1407523 1585525 := bbase (se 5 (by rfl) ⟨74321, by rfl⟩ : syracuseStep 1585525 = 148643) (by norm_num)
theorem B1782157 : Blo 1407523 1782157 := bbase (se 3 (by rfl) ⟨334154, by rfl⟩ : syracuseStep 1782157 = 668309) (by norm_num)
theorem B6017429 : Blo 1407523 6017429 := bbase (se 6 (by rfl) ⟨141033, by rfl⟩ : syracuseStep 6017429 = 282067) (by norm_num)
theorem B1585561 : Blo 1407523 1585561 := bbase (se 2 (by rfl) ⟨594585, by rfl⟩ : syracuseStep 1585561 = 1189171) (by norm_num)
theorem B1692085 : Blo 1407523 1692085 := bbase (se 5 (by rfl) ⟨79316, by rfl⟩ : syracuseStep 1692085 = 158633) (by norm_num)
theorem B1585597 : Blo 1407523 1585597 := bbase (se 3 (by rfl) ⟨297299, by rfl⟩ : syracuseStep 1585597 = 594599) (by norm_num)
theorem B1585633 : Blo 1407523 1585633 := bbase (se 2 (by rfl) ⟨594612, by rfl⟩ : syracuseStep 1585633 = 1189225) (by norm_num)
theorem B4755941 : Blo 1407523 4755941 := bbase (se 4 (by rfl) ⟨445869, by rfl⟩ : syracuseStep 4755941 = 891739) (by norm_num)
theorem B1782253 : Blo 1407523 1782253 := bbase (se 3 (by rfl) ⟨334172, by rfl⟩ : syracuseStep 1782253 = 668345) (by norm_num)
theorem B1585669 : Blo 1407523 1585669 := bbase (se 4 (by rfl) ⟨148656, by rfl⟩ : syracuseStep 1585669 = 297313) (by norm_num)
theorem B1692181 : Blo 1407523 1692181 := bbase (se 6 (by rfl) ⟨39660, by rfl⟩ : syracuseStep 1692181 = 79321) (by norm_num)
theorem B1503785 : Blo 1407523 1503785 := bbase (se 2 (by rfl) ⟨563919, by rfl⟩ : syracuseStep 1503785 = 1127839) (by norm_num)
theorem B1585705 : Blo 1407523 1585705 := bbase (se 2 (by rfl) ⟨594639, by rfl⟩ : syracuseStep 1585705 = 1189279) (by norm_num)
theorem B6181445 : Blo 1407523 6181445 := bbase (se 4 (by rfl) ⟨579510, by rfl⟩ : syracuseStep 6181445 = 1159021) (by norm_num)
theorem B5345909 : Blo 1407523 5345909 := bbase (se 5 (by rfl) ⟨250589, by rfl⟩ : syracuseStep 5345909 = 501179) (by norm_num)
theorem B1782425 : Blo 1407523 1782425 := bbase (se 2 (by rfl) ⟨668409, by rfl⟩ : syracuseStep 1782425 = 1336819) (by norm_num)
theorem B10146485 : Blo 1407523 10146485 := bbase (se 5 (by rfl) ⟨475616, by rfl⟩ : syracuseStep 10146485 = 951233) (by norm_num)
theorem B6771397 : Blo 1407523 6771397 := bbase (se 4 (by rfl) ⟨634818, by rfl⟩ : syracuseStep 6771397 = 1269637) (by norm_num)
theorem B1782481 : Blo 1407523 1782481 := bbase (se 2 (by rfl) ⟨668430, by rfl⟩ : syracuseStep 1782481 = 1336861) (by norm_num)
theorem B3134173 : Blo 1407523 3134173 := bbase (se 3 (by rfl) ⟨587657, by rfl⟩ : syracuseStep 3134173 = 1175315) (by norm_num)
theorem B2257645 : Blo 1407523 2257645 := bbase (se 3 (by rfl) ⟨423308, by rfl⟩ : syracuseStep 2257645 = 846617) (by norm_num)
theorem B3166973 : Blo 1407523 3166973 := bbase (se 3 (by rfl) ⟨593807, by rfl⟩ : syracuseStep 3166973 = 1187615) (by norm_num)
theorem B2855717 : Blo 1407523 2855717 := bbase (se 4 (by rfl) ⟨267723, by rfl⟩ : syracuseStep 2855717 = 535447) (by norm_num)
theorem B1782577 : Blo 1407523 1782577 := bbase (se 2 (by rfl) ⟨668466, by rfl⟩ : syracuseStep 1782577 = 1336933) (by norm_num)
theorem B3167045 : Blo 1407523 3167045 := bbase (se 4 (by rfl) ⟨296910, by rfl⟩ : syracuseStep 3167045 = 593821) (by norm_num)
theorem B1807237 : Blo 1407523 1807237 := bbase (se 4 (by rfl) ⟨169428, by rfl⟩ : syracuseStep 1807237 = 338857) (by norm_num)
theorem B3167117 : Blo 1407523 3167117 := bbase (se 3 (by rfl) ⟨593834, by rfl⟩ : syracuseStep 3167117 = 1187669) (by norm_num)
theorem B4756373 : Blo 1407523 4756373 := bbase (se 6 (by rfl) ⟨111477, by rfl⟩ : syracuseStep 4756373 = 222955) (by norm_num)
theorem B2675605 : Blo 1407523 2675605 := bbase (se 6 (by rfl) ⟨62709, by rfl⟩ : syracuseStep 2675605 = 125419) (by norm_num)
theorem B13915061 : Blo 1407523 13915061 := bbase (se 5 (by rfl) ⟨652268, by rfl⟩ : syracuseStep 13915061 = 1304537) (by norm_num)
theorem B1487809 : Blo 1407523 1487809 := bbase (se 2 (by rfl) ⟨557928, by rfl⟩ : syracuseStep 1487809 = 1115857) (by norm_num)
theorem B5075909 : Blo 1407523 5075909 := bbase (se 4 (by rfl) ⟨475866, by rfl⟩ : syracuseStep 5075909 = 951733) (by norm_num)
theorem B3167189 : Blo 1407523 3167189 := bbase (se 7 (by rfl) ⟨37115, by rfl⟩ : syracuseStep 3167189 = 74231) (by norm_num)
theorem B1782749 : Blo 1407523 1782749 := bbase (se 3 (by rfl) ⟨334265, by rfl⟩ : syracuseStep 1782749 = 668531) (by norm_num)
theorem B1504229 : Blo 1407523 1504229 := bbase (se 4 (by rfl) ⟨141021, by rfl⟩ : syracuseStep 1504229 = 282043) (by norm_num)
theorem B12841973 : Blo 1407523 12841973 := bbase (se 5 (by rfl) ⟨601967, by rfl⟩ : syracuseStep 12841973 = 1203935) (by norm_num)
theorem B1782805 : Blo 1407523 1782805 := bbase (se 6 (by rfl) ⟨41784, by rfl⟩ : syracuseStep 1782805 = 83569) (by norm_num)
theorem B4822037 : Blo 1407523 4822037 := bbase (se 6 (by rfl) ⟨113016, by rfl⟩ : syracuseStep 4822037 = 226033) (by norm_num)
theorem B3167261 : Blo 1407523 3167261 := bbase (se 3 (by rfl) ⟨593861, by rfl⟩ : syracuseStep 3167261 = 1187723) (by norm_num)
theorem B1504289 : Blo 1407523 1504289 := bbase (se 2 (by rfl) ⟨564108, by rfl⟩ : syracuseStep 1504289 = 1128217) (by norm_num)
theorem B2675749 : Blo 1407523 2675749 := bbase (se 4 (by rfl) ⟨250851, by rfl⟩ : syracuseStep 2675749 = 501703) (by norm_num)
theorem B3167333 : Blo 1407523 3167333 := bbase (se 4 (by rfl) ⟨296937, by rfl⟩ : syracuseStep 3167333 = 593875) (by norm_num)
theorem B1782901 : Blo 1407523 1782901 := bbase (se 5 (by rfl) ⟨83573, by rfl⟩ : syracuseStep 1782901 = 167147) (by norm_num)
theorem B1504417 : Blo 1407523 1504417 := bbase (se 2 (by rfl) ⟨564156, by rfl⟩ : syracuseStep 1504417 = 1128313) (by norm_num)
theorem B3167405 : Blo 1407523 3167405 := bbase (se 3 (by rfl) ⟨593888, by rfl⟩ : syracuseStep 3167405 = 1187777) (by norm_num)
theorem B4011221 : Blo 1407523 4011221 := bbase (se 7 (by rfl) ⟨47006, by rfl⟩ : syracuseStep 4011221 = 94013) (by norm_num)
theorem B7132373 : Blo 1407523 7132373 := bbase (se 7 (by rfl) ⟨83582, by rfl⟩ : syracuseStep 7132373 = 167165) (by norm_num)
theorem B3167477 : Blo 1407523 3167477 := bbase (se 5 (by rfl) ⟨148475, by rfl⟩ : syracuseStep 3167477 = 296951) (by norm_num)
theorem B1783073 : Blo 1407523 1783073 := bbase (se 2 (by rfl) ⟨668652, by rfl⟩ : syracuseStep 1783073 = 1337305) (by norm_num)
theorem B3167549 : Blo 1407523 3167549 := bbase (se 3 (by rfl) ⟨593915, by rfl⟩ : syracuseStep 3167549 = 1187831) (by norm_num)
theorem B4756805 : Blo 1407523 4756805 := bbase (se 4 (by rfl) ⟨445950, by rfl⟩ : syracuseStep 4756805 = 891901) (by norm_num)
theorem B1783129 : Blo 1407523 1783129 := bbase (se 2 (by rfl) ⟨668673, by rfl⟩ : syracuseStep 1783129 = 1337347) (by norm_num)
theorem B3167621 : Blo 1407523 3167621 := bbase (se 4 (by rfl) ⟨296964, by rfl⟩ : syracuseStep 3167621 = 593929) (by norm_num)
theorem B1783225 : Blo 1407523 1783225 := bbase (se 2 (by rfl) ⟨668709, by rfl⟩ : syracuseStep 1783225 = 1337419) (by norm_num)
theorem B3167693 : Blo 1407523 3167693 := bbase (se 3 (by rfl) ⟨593942, by rfl⟩ : syracuseStep 3167693 = 1187885) (by norm_num)
theorem B4511189 : Blo 1407523 4511189 := bbase (se 7 (by rfl) ⟨52865, by rfl⟩ : syracuseStep 4511189 = 105731) (by norm_num)
theorem B3167765 : Blo 1407523 3167765 := bbase (se 6 (by rfl) ⟨74244, by rfl⟩ : syracuseStep 3167765 = 148489) (by norm_num)
theorem B2004517 : Blo 1407523 2004517 := bbase (se 4 (by rfl) ⟨187923, by rfl⟩ : syracuseStep 2004517 = 375847) (by norm_num)
theorem B3167837 : Blo 1407523 3167837 := bbase (se 3 (by rfl) ⟨593969, by rfl⟩ : syracuseStep 3167837 = 1187939) (by norm_num)
theorem B1504861 : Blo 1407523 1504861 := bbase (se 3 (by rfl) ⟨282161, by rfl⟩ : syracuseStep 1504861 = 564323) (by norm_num)
theorem B1783397 : Blo 1407523 1783397 := bbase (se 4 (by rfl) ⟨167193, by rfl⟩ : syracuseStep 1783397 = 334387) (by norm_num)
theorem B1693325 : Blo 1407523 1693325 := bbase (se 3 (by rfl) ⟨317498, by rfl⟩ : syracuseStep 1693325 = 634997) (by norm_num)
theorem B1783453 : Blo 1407523 1783453 := bbase (se 3 (by rfl) ⟨334397, by rfl⟩ : syracuseStep 1783453 = 668795) (by norm_num)
theorem B3167909 : Blo 1407523 3167909 := bbase (se 4 (by rfl) ⟨296991, by rfl⟩ : syracuseStep 3167909 = 593983) (by norm_num)
theorem B10696373 : Blo 1407523 10696373 := bbase (se 5 (by rfl) ⟨501392, by rfl⟩ : syracuseStep 10696373 = 1002785) (by norm_num)
theorem B1504981 : Blo 1407523 1504981 := bbase (se 7 (by rfl) ⟨17636, by rfl⟩ : syracuseStep 1504981 = 35273) (by norm_num)
theorem B3167981 : Blo 1407523 3167981 := bbase (se 3 (by rfl) ⟨593996, by rfl⟩ : syracuseStep 3167981 = 1187993) (by norm_num)
theorem B1783549 : Blo 1407523 1783549 := bbase (se 3 (by rfl) ⟨334415, by rfl⟩ : syracuseStep 1783549 = 668831) (by norm_num)
theorem B5347093 : Blo 1407523 5347093 := bbase (se 6 (by rfl) ⟨125322, by rfl⟩ : syracuseStep 5347093 = 250645) (by norm_num)
theorem B16054037 : Blo 1407523 16054037 := bbase (se 6 (by rfl) ⟨376266, by rfl⟩ : syracuseStep 16054037 = 752533) (by norm_num)
theorem B2111285 : Blo 1407523 2111285 := bbase (se 5 (by rfl) ⟨98966, by rfl⟩ : syracuseStep 2111285 = 197933) (by norm_num)
theorem B3168053 : Blo 1407523 3168053 := bbase (se 5 (by rfl) ⟨148502, by rfl⟩ : syracuseStep 3168053 = 297005) (by norm_num)
theorem B2111309 : Blo 1407523 2111309 := bbase (se 3 (by rfl) ⟨395870, by rfl⟩ : syracuseStep 2111309 = 791741) (by norm_num)
theorem B2111333 : Blo 1407523 2111333 := bbase (se 4 (by rfl) ⟨197937, by rfl⟩ : syracuseStep 2111333 = 395875) (by norm_num)
theorem B2004853 : Blo 1407523 2004853 := bbase (se 5 (by rfl) ⟨93977, by rfl⟩ : syracuseStep 2004853 = 187955) (by norm_num)
theorem B4011893 : Blo 1407523 4011893 := bbase (se 5 (by rfl) ⟨188057, by rfl⟩ : syracuseStep 4011893 = 376115) (by norm_num)
theorem B2111357 : Blo 1407523 2111357 := bbase (se 3 (by rfl) ⟨395879, by rfl⟩ : syracuseStep 2111357 = 791759) (by norm_num)
theorem B3168125 : Blo 1407523 3168125 := bbase (se 3 (by rfl) ⟨594023, by rfl⟩ : syracuseStep 3168125 = 1188047) (by norm_num)
theorem B2111381 : Blo 1407523 2111381 := bbase (se 6 (by rfl) ⟨49485, by rfl⟩ : syracuseStep 2111381 = 98971) (by norm_num)
theorem B1783721 : Blo 1407523 1783721 := bbase (se 2 (by rfl) ⟨668895, by rfl⟩ : syracuseStep 1783721 = 1337791) (by norm_num)
theorem B2111405 : Blo 1407523 2111405 := bbase (se 3 (by rfl) ⟨395888, by rfl⟩ : syracuseStep 2111405 = 791777) (by norm_num)
theorem B2111429 : Blo 1407523 2111429 := bbase (se 4 (by rfl) ⟨197946, by rfl⟩ : syracuseStep 2111429 = 395893) (by norm_num)
theorem B3168197 : Blo 1407523 3168197 := bbase (se 4 (by rfl) ⟨297018, by rfl⟩ : syracuseStep 3168197 = 594037) (by norm_num)
theorem B2111453 : Blo 1407523 2111453 := bbase (se 3 (by rfl) ⟨395897, by rfl⟩ : syracuseStep 2111453 = 791795) (by norm_num)
theorem B1783777 : Blo 1407523 1783777 := bbase (se 2 (by rfl) ⟨668916, by rfl⟩ : syracuseStep 1783777 = 1337833) (by norm_num)
theorem B2111477 : Blo 1407523 2111477 := bbase (se 5 (by rfl) ⟨98975, by rfl⟩ : syracuseStep 2111477 = 197951) (by norm_num)
theorem B2111501 : Blo 1407523 2111501 := bbase (se 3 (by rfl) ⟨395906, by rfl⟩ : syracuseStep 2111501 = 791813) (by norm_num)
theorem B3168269 : Blo 1407523 3168269 := bbase (se 3 (by rfl) ⟨594050, by rfl⟩ : syracuseStep 3168269 = 1188101) (by norm_num)
theorem B2111525 : Blo 1407523 2111525 := bbase (se 4 (by rfl) ⟨197955, by rfl⟩ : syracuseStep 2111525 = 395911) (by norm_num)
theorem B2111549 : Blo 1407523 2111549 := bbase (se 3 (by rfl) ⟨395915, by rfl⟩ : syracuseStep 2111549 = 791831) (by norm_num)
theorem B1783873 : Blo 1407523 1783873 := bbase (se 2 (by rfl) ⟨668952, by rfl⟩ : syracuseStep 1783873 = 1337905) (by norm_num)
theorem B5347397 : Blo 1407523 5347397 := bbase (se 4 (by rfl) ⟨501318, by rfl⟩ : syracuseStep 5347397 = 1002637) (by norm_num)
theorem B2005069 : Blo 1407523 2005069 := bbase (se 3 (by rfl) ⟨375950, by rfl⟩ : syracuseStep 2005069 = 751901) (by norm_num)
theorem B10688597 : Blo 1407523 10688597 := bbase (se 8 (by rfl) ⟨62628, by rfl⟩ : syracuseStep 10688597 = 125257) (by norm_num)
theorem B2111573 : Blo 1407523 2111573 := bbase (se 8 (by rfl) ⟨12372, by rfl⟩ : syracuseStep 2111573 = 24745) (by norm_num)
theorem B3168341 : Blo 1407523 3168341 := bbase (se 8 (by rfl) ⟨18564, by rfl⟩ : syracuseStep 3168341 = 37129) (by norm_num)
theorem B2111597 : Blo 1407523 2111597 := bbase (se 3 (by rfl) ⟨395924, by rfl⟩ : syracuseStep 2111597 = 791849) (by norm_num)
theorem B2111621 : Blo 1407523 2111621 := bbase (se 4 (by rfl) ⟨197964, by rfl⟩ : syracuseStep 2111621 = 395929) (by norm_num)
theorem B2111645 : Blo 1407523 2111645 := bbase (se 3 (by rfl) ⟨395933, by rfl⟩ : syracuseStep 2111645 = 791867) (by norm_num)
theorem B3168413 : Blo 1407523 3168413 := bbase (se 3 (by rfl) ⟨594077, by rfl⟩ : syracuseStep 3168413 = 1188155) (by norm_num)
theorem B6764725 : Blo 1407523 6764725 := bbase (se 5 (by rfl) ⟨317096, by rfl⟩ : syracuseStep 6764725 = 634193) (by norm_num)
theorem B2111669 : Blo 1407523 2111669 := bbase (se 5 (by rfl) ⟨98984, by rfl⟩ : syracuseStep 2111669 = 197969) (by norm_num)
theorem B2111693 : Blo 1407523 2111693 := bbase (se 3 (by rfl) ⟨395942, by rfl⟩ : syracuseStep 2111693 = 791885) (by norm_num)
theorem B2111717 : Blo 1407523 2111717 := bbase (se 4 (by rfl) ⟨197973, by rfl⟩ : syracuseStep 2111717 = 395947) (by norm_num)
theorem B3168485 : Blo 1407523 3168485 := bbase (se 4 (by rfl) ⟨297045, by rfl⟩ : syracuseStep 3168485 = 594091) (by norm_num)
theorem B2111741 : Blo 1407523 2111741 := bbase (se 3 (by rfl) ⟨395951, by rfl⟩ : syracuseStep 2111741 = 791903) (by norm_num)
theorem B2111765 : Blo 1407523 2111765 := bbase (se 6 (by rfl) ⟨49494, by rfl⟩ : syracuseStep 2111765 = 98989) (by norm_num)
theorem B4012325 : Blo 1407523 4012325 := bbase (se 4 (by rfl) ⟨376155, by rfl⟩ : syracuseStep 4012325 = 752311) (by norm_num)
theorem B2111789 : Blo 1407523 2111789 := bbase (se 3 (by rfl) ⟨395960, by rfl⟩ : syracuseStep 2111789 = 791921) (by norm_num)
theorem B3168557 : Blo 1407523 3168557 := bbase (se 3 (by rfl) ⟨594104, by rfl⟩ : syracuseStep 3168557 = 1188209) (by norm_num)
theorem B2111813 : Blo 1407523 2111813 := bbase (se 4 (by rfl) ⟨197982, by rfl⟩ : syracuseStep 2111813 = 395965) (by norm_num)
theorem B2111837 : Blo 1407523 2111837 := bbase (se 3 (by rfl) ⟨395969, by rfl⟩ : syracuseStep 2111837 = 791939) (by norm_num)
theorem B2111861 : Blo 1407523 2111861 := bbase (se 5 (by rfl) ⟨98993, by rfl⟩ : syracuseStep 2111861 = 197987) (by norm_num)
theorem B3168629 : Blo 1407523 3168629 := bbase (se 5 (by rfl) ⟨148529, by rfl⟩ : syracuseStep 3168629 = 297059) (by norm_num)
theorem B2111885 : Blo 1407523 2111885 := bbase (se 3 (by rfl) ⟨395978, by rfl⟩ : syracuseStep 2111885 = 791957) (by norm_num)
theorem B2111909 : Blo 1407523 2111909 := bbase (se 4 (by rfl) ⟨197991, by rfl⟩ : syracuseStep 2111909 = 395983) (by norm_num)
theorem B2111933 : Blo 1407523 2111933 := bbase (se 3 (by rfl) ⟨395987, by rfl⟩ : syracuseStep 2111933 = 791975) (by norm_num)
theorem B3168701 : Blo 1407523 3168701 := bbase (se 3 (by rfl) ⟨594131, by rfl⟩ : syracuseStep 3168701 = 1188263) (by norm_num)
theorem B2005445 : Blo 1407523 2005445 := bbase (se 4 (by rfl) ⟨188010, by rfl⟩ : syracuseStep 2005445 = 376021) (by norm_num)
theorem B2111957 : Blo 1407523 2111957 := bbase (se 7 (by rfl) ⟨24749, by rfl⟩ : syracuseStep 2111957 = 49499) (by norm_num)
theorem B3807701 : Blo 1407523 3807701 := bbase (se 7 (by rfl) ⟨44621, by rfl⟩ : syracuseStep 3807701 = 89243) (by norm_num)
theorem B7133669 : Blo 1407523 7133669 := bbase (se 4 (by rfl) ⟨668781, by rfl⟩ : syracuseStep 7133669 = 1337563) (by norm_num)
theorem B2111981 : Blo 1407523 2111981 := bbase (se 3 (by rfl) ⟨395996, by rfl⟩ : syracuseStep 2111981 = 791993) (by norm_num)
theorem B2112005 : Blo 1407523 2112005 := bbase (se 4 (by rfl) ⟨198000, by rfl⟩ : syracuseStep 2112005 = 396001) (by norm_num)
theorem B3168773 : Blo 1407523 3168773 := bbase (se 4 (by rfl) ⟨297072, by rfl⟩ : syracuseStep 3168773 = 594145) (by norm_num)
theorem B8018453 : Blo 1407523 8018453 := bbase (se 6 (by rfl) ⟨187932, by rfl⟩ : syracuseStep 8018453 = 375865) (by norm_num)
theorem B4512277 : Blo 1407523 4512277 := bbase (se 6 (by rfl) ⟨105756, by rfl⟩ : syracuseStep 4512277 = 211513) (by norm_num)
theorem B2112029 : Blo 1407523 2112029 := bbase (se 3 (by rfl) ⟨396005, by rfl⟩ : syracuseStep 2112029 = 792011) (by norm_num)
theorem B2112053 : Blo 1407523 2112053 := bbase (se 5 (by rfl) ⟨99002, by rfl⟩ : syracuseStep 2112053 = 198005) (by norm_num)
theorem B2112077 : Blo 1407523 2112077 := bbase (se 3 (by rfl) ⟨396014, by rfl⟩ : syracuseStep 2112077 = 792029) (by norm_num)
theorem B3168845 : Blo 1407523 3168845 := bbase (se 3 (by rfl) ⟨594158, by rfl⟩ : syracuseStep 3168845 = 1188317) (by norm_num)
theorem B2112101 : Blo 1407523 2112101 := bbase (se 4 (by rfl) ⟨198009, by rfl⟩ : syracuseStep 2112101 = 396019) (by norm_num)
theorem B10156661 : Blo 1407523 10156661 := bbase (se 5 (by rfl) ⟨476093, by rfl⟩ : syracuseStep 10156661 = 952187) (by norm_num)
theorem B2112125 : Blo 1407523 2112125 := bbase (se 3 (by rfl) ⟨396023, by rfl⟩ : syracuseStep 2112125 = 792047) (by norm_num)
theorem B2112149 : Blo 1407523 2112149 := bbase (se 6 (by rfl) ⟨49503, by rfl⟩ : syracuseStep 2112149 = 99007) (by norm_num)
theorem B3168917 : Blo 1407523 3168917 := bbase (se 6 (by rfl) ⟨74271, by rfl⟩ : syracuseStep 3168917 = 148543) (by norm_num)
theorem B2112173 : Blo 1407523 2112173 := bbase (se 3 (by rfl) ⟨396032, by rfl⟩ : syracuseStep 2112173 = 792065) (by norm_num)
theorem B2112197 : Blo 1407523 2112197 := bbase (se 4 (by rfl) ⟨198018, by rfl⟩ : syracuseStep 2112197 = 396037) (by norm_num)
theorem B2112221 : Blo 1407523 2112221 := bbase (se 3 (by rfl) ⟨396041, by rfl⟩ : syracuseStep 2112221 = 792083) (by norm_num)
theorem B3168989 : Blo 1407523 3168989 := bbase (se 3 (by rfl) ⟨594185, by rfl⟩ : syracuseStep 3168989 = 1188371) (by norm_num)
theorem B2112245 : Blo 1407523 2112245 := bbase (se 5 (by rfl) ⟨99011, by rfl⟩ : syracuseStep 2112245 = 198023) (by norm_num)
theorem B2112269 : Blo 1407523 2112269 := bbase (se 3 (by rfl) ⟨396050, by rfl⟩ : syracuseStep 2112269 = 792101) (by norm_num)
theorem B3382037 : Blo 1407523 3382037 := bbase (se 6 (by rfl) ⟨79266, by rfl⟩ : syracuseStep 3382037 = 158533) (by norm_num)
theorem B2112293 : Blo 1407523 2112293 := bbase (se 4 (by rfl) ⟨198027, by rfl⟩ : syracuseStep 2112293 = 396055) (by norm_num)
theorem B3169061 : Blo 1407523 3169061 := bbase (se 4 (by rfl) ⟨297099, by rfl⟩ : syracuseStep 3169061 = 594199) (by norm_num)
theorem B2112317 : Blo 1407523 2112317 := bbase (se 3 (by rfl) ⟨396059, by rfl⟩ : syracuseStep 2112317 = 792119) (by norm_num)
theorem B5421893 : Blo 1407523 5421893 := bbase (se 4 (by rfl) ⟨508302, by rfl⟩ : syracuseStep 5421893 = 1016605) (by norm_num)
theorem B3382093 : Blo 1407523 3382093 := bbase (se 3 (by rfl) ⟨634142, by rfl⟩ : syracuseStep 3382093 = 1268285) (by norm_num)
theorem B2112341 : Blo 1407523 2112341 := bbase (se 9 (by rfl) ⟨6188, by rfl⟩ : syracuseStep 2112341 = 12377) (by norm_num)
theorem B2112365 : Blo 1407523 2112365 := bbase (se 3 (by rfl) ⟨396068, by rfl⟩ : syracuseStep 2112365 = 792137) (by norm_num)
theorem B3169133 : Blo 1407523 3169133 := bbase (se 3 (by rfl) ⟨594212, by rfl⟩ : syracuseStep 3169133 = 1188425) (by norm_num)
theorem B7125893 : Blo 1407523 7125893 := bbase (se 4 (by rfl) ⟨668052, by rfl⟩ : syracuseStep 7125893 = 1336105) (by norm_num)
theorem B2112389 : Blo 1407523 2112389 := bbase (se 4 (by rfl) ⟨198036, by rfl⟩ : syracuseStep 2112389 = 396073) (by norm_num)
theorem B2538373 : Blo 1407523 2538373 := bbase (se 4 (by rfl) ⟨237972, by rfl⟩ : syracuseStep 2538373 = 475945) (by norm_num)
theorem B4283285 : Blo 1407523 4283285 := bbase (se 6 (by rfl) ⟨100389, by rfl⟩ : syracuseStep 4283285 = 200779) (by norm_num)
theorem B2112413 : Blo 1407523 2112413 := bbase (se 3 (by rfl) ⟨396077, by rfl⟩ : syracuseStep 2112413 = 792155) (by norm_num)
theorem B2112437 : Blo 1407523 2112437 := bbase (se 5 (by rfl) ⟨99020, by rfl⟩ : syracuseStep 2112437 = 198041) (by norm_num)
theorem B3169205 : Blo 1407523 3169205 := bbase (se 5 (by rfl) ⟨148556, by rfl⟩ : syracuseStep 3169205 = 297113) (by norm_num)
theorem B2112461 : Blo 1407523 2112461 := bbase (se 3 (by rfl) ⟨396086, by rfl⟩ : syracuseStep 2112461 = 792173) (by norm_num)
theorem B2112485 : Blo 1407523 2112485 := bbase (se 4 (by rfl) ⟨198045, by rfl⟩ : syracuseStep 2112485 = 396091) (by norm_num)
theorem B2112509 : Blo 1407523 2112509 := bbase (se 3 (by rfl) ⟨396095, by rfl⟩ : syracuseStep 2112509 = 792191) (by norm_num)
theorem B3169277 : Blo 1407523 3169277 := bbase (se 3 (by rfl) ⟨594239, by rfl⟩ : syracuseStep 3169277 = 1188479) (by norm_num)
theorem B2112533 : Blo 1407523 2112533 := bbase (se 6 (by rfl) ⟨49512, by rfl⟩ : syracuseStep 2112533 = 99025) (by norm_num)
theorem B4013077 : Blo 1407523 4013077 := bbase (se 6 (by rfl) ⟨94056, by rfl⟩ : syracuseStep 4013077 = 188113) (by norm_num)
theorem B2112557 : Blo 1407523 2112557 := bbase (se 3 (by rfl) ⟨396104, by rfl⟩ : syracuseStep 2112557 = 792209) (by norm_num)
theorem B2112581 : Blo 1407523 2112581 := bbase (se 4 (by rfl) ⟨198054, by rfl⟩ : syracuseStep 2112581 = 396109) (by norm_num)
theorem B3169349 : Blo 1407523 3169349 := bbase (se 4 (by rfl) ⟨297126, by rfl⟩ : syracuseStep 3169349 = 594253) (by norm_num)
theorem B2112605 : Blo 1407523 2112605 := bbase (se 3 (by rfl) ⟨396113, by rfl⟩ : syracuseStep 2112605 = 792227) (by norm_num)
theorem B2112629 : Blo 1407523 2112629 := bbase (se 5 (by rfl) ⟨99029, by rfl⟩ : syracuseStep 2112629 = 198059) (by norm_num)
theorem B2112653 : Blo 1407523 2112653 := bbase (se 3 (by rfl) ⟨396122, by rfl⟩ : syracuseStep 2112653 = 792245) (by norm_num)
theorem B3169421 : Blo 1407523 3169421 := bbase (se 3 (by rfl) ⟨594266, by rfl⟩ : syracuseStep 3169421 = 1188533) (by norm_num)
theorem B20315285 : Blo 1407523 20315285 := bbase (se 6 (by rfl) ⟨476139, by rfl⟩ : syracuseStep 20315285 = 952279) (by norm_num)
theorem B2112677 : Blo 1407523 2112677 := bbase (se 4 (by rfl) ⟨198063, by rfl⟩ : syracuseStep 2112677 = 396127) (by norm_num)
theorem B2112701 : Blo 1407523 2112701 := bbase (se 3 (by rfl) ⟨396131, by rfl⟩ : syracuseStep 2112701 = 792263) (by norm_num)
theorem B2112725 : Blo 1407523 2112725 := bbase (se 7 (by rfl) ⟨24758, by rfl⟩ : syracuseStep 2112725 = 49517) (by norm_num)
theorem B3169493 : Blo 1407523 3169493 := bbase (se 7 (by rfl) ⟨37142, by rfl⟩ : syracuseStep 3169493 = 74285) (by norm_num)
theorem B2112749 : Blo 1407523 2112749 := bbase (se 3 (by rfl) ⟨396140, by rfl⟩ : syracuseStep 2112749 = 792281) (by norm_num)
theorem B2112773 : Blo 1407523 2112773 := bbase (se 4 (by rfl) ⟨198072, by rfl⟩ : syracuseStep 2112773 = 396145) (by norm_num)
theorem B2112797 : Blo 1407523 2112797 := bbase (se 3 (by rfl) ⟨396149, by rfl⟩ : syracuseStep 2112797 = 792299) (by norm_num)
theorem B3169565 : Blo 1407523 3169565 := bbase (se 3 (by rfl) ⟨594293, by rfl⟩ : syracuseStep 3169565 = 1188587) (by norm_num)
theorem B3562805 : Blo 1407523 3562805 := bbase (se 5 (by rfl) ⟨167006, by rfl⟩ : syracuseStep 3562805 = 334013) (by norm_num)
theorem B2112821 : Blo 1407523 2112821 := bbase (se 5 (by rfl) ⟨99038, by rfl⟩ : syracuseStep 2112821 = 198077) (by norm_num)
theorem B2112845 : Blo 1407523 2112845 := bbase (se 3 (by rfl) ⟨396158, by rfl⟩ : syracuseStep 2112845 = 792317) (by norm_num)
theorem B2112869 : Blo 1407523 2112869 := bbase (se 4 (by rfl) ⟨198081, by rfl⟩ : syracuseStep 2112869 = 396163) (by norm_num)
theorem B3169637 : Blo 1407523 3169637 := bbase (se 4 (by rfl) ⟨297153, by rfl⟩ : syracuseStep 3169637 = 594307) (by norm_num)
theorem B5078389 : Blo 1407523 5078389 := bbase (se 5 (by rfl) ⟨238049, by rfl⟩ : syracuseStep 5078389 = 476099) (by norm_num)
theorem B2112893 : Blo 1407523 2112893 := bbase (se 3 (by rfl) ⟨396167, by rfl⟩ : syracuseStep 2112893 = 792335) (by norm_num)
theorem B2538877 : Blo 1407523 2538877 := bbase (se 3 (by rfl) ⟨476039, by rfl⟩ : syracuseStep 2538877 = 952079) (by norm_num)
theorem B3612053 : Blo 1407523 3612053 := bbase (se 6 (by rfl) ⟨84657, by rfl⟩ : syracuseStep 3612053 = 169315) (by norm_num)
theorem B2112917 : Blo 1407523 2112917 := bbase (se 6 (by rfl) ⟨49521, by rfl⟩ : syracuseStep 2112917 = 99043) (by norm_num)
theorem B4750757 : Blo 1407523 4750757 := bbase (se 4 (by rfl) ⟨445383, by rfl⟩ : syracuseStep 4750757 = 890767) (by norm_num)
theorem B2112941 : Blo 1407523 2112941 := bbase (se 3 (by rfl) ⟨396176, by rfl⟩ : syracuseStep 2112941 = 792353) (by norm_num)
theorem B3169709 : Blo 1407523 3169709 := bbase (se 3 (by rfl) ⟨594320, by rfl⟩ : syracuseStep 3169709 = 1188641) (by norm_num)
theorem B2112965 : Blo 1407523 2112965 := bbase (se 4 (by rfl) ⟨198090, by rfl⟩ : syracuseStep 2112965 = 396181) (by norm_num)
theorem B2112989 : Blo 1407523 2112989 := bbase (se 3 (by rfl) ⟨396185, by rfl⟩ : syracuseStep 2112989 = 792371) (by norm_num)
theorem B2113013 : Blo 1407523 2113013 := bbase (se 5 (by rfl) ⟨99047, by rfl⟩ : syracuseStep 2113013 = 198095) (by norm_num)
theorem B3169781 : Blo 1407523 3169781 := bbase (se 5 (by rfl) ⟨148583, by rfl⟩ : syracuseStep 3169781 = 297167) (by norm_num)
theorem B2113037 : Blo 1407523 2113037 := bbase (se 3 (by rfl) ⟨396194, by rfl⟩ : syracuseStep 2113037 = 792389) (by norm_num)
theorem B2113061 : Blo 1407523 2113061 := bbase (se 4 (by rfl) ⟨198099, by rfl⟩ : syracuseStep 2113061 = 396199) (by norm_num)
theorem B2113085 : Blo 1407523 2113085 := bbase (se 3 (by rfl) ⟨396203, by rfl⟩ : syracuseStep 2113085 = 792407) (by norm_num)
theorem B3169853 : Blo 1407523 3169853 := bbase (se 3 (by rfl) ⟨594347, by rfl⟩ : syracuseStep 3169853 = 1188695) (by norm_num)
theorem B2375237 : Blo 1407523 2375237 := bbase (se 4 (by rfl) ⟨222678, by rfl⟩ : syracuseStep 2375237 = 445357) (by norm_num)
theorem B2113109 : Blo 1407523 2113109 := bbase (se 8 (by rfl) ⟨12381, by rfl⟩ : syracuseStep 2113109 = 24763) (by norm_num)
theorem B2113133 : Blo 1407523 2113133 := bbase (se 3 (by rfl) ⟨396212, by rfl⟩ : syracuseStep 2113133 = 792425) (by norm_num)
theorem B3210877 : Blo 1407523 3210877 := bbase (se 3 (by rfl) ⟨602039, by rfl⟩ : syracuseStep 3210877 = 1204079) (by norm_num)
theorem B2113157 : Blo 1407523 2113157 := bbase (se 4 (by rfl) ⟨198108, by rfl⟩ : syracuseStep 2113157 = 396217) (by norm_num)
theorem B3169925 : Blo 1407523 3169925 := bbase (se 4 (by rfl) ⟨297180, by rfl⟩ : syracuseStep 3169925 = 594361) (by norm_num)
theorem B3563149 : Blo 1407523 3563149 := bbase (se 3 (by rfl) ⟨668090, by rfl⟩ : syracuseStep 3563149 = 1336181) (by norm_num)
theorem B4062869 : Blo 1407523 4062869 := bbase (se 6 (by rfl) ⟨95223, by rfl⟩ : syracuseStep 4062869 = 190447) (by norm_num)
theorem B12025493 : Blo 1407523 12025493 := bbase (se 6 (by rfl) ⟨281847, by rfl⟩ : syracuseStep 12025493 = 563695) (by norm_num)
theorem B2113181 : Blo 1407523 2113181 := bbase (se 3 (by rfl) ⟨396221, by rfl⟩ : syracuseStep 2113181 = 792443) (by norm_num)
theorem B4513445 : Blo 1407523 4513445 := bbase (se 4 (by rfl) ⟨423135, by rfl⟩ : syracuseStep 4513445 = 846271) (by norm_num)
theorem B2113205 : Blo 1407523 2113205 := bbase (se 5 (by rfl) ⟨99056, by rfl⟩ : syracuseStep 2113205 = 198113) (by norm_num)
theorem B2375365 : Blo 1407523 2375365 := bbase (se 4 (by rfl) ⟨222690, by rfl⟩ : syracuseStep 2375365 = 445381) (by norm_num)
theorem B2113229 : Blo 1407523 2113229 := bbase (se 3 (by rfl) ⟨396230, by rfl⟩ : syracuseStep 2113229 = 792461) (by norm_num)
theorem B3169997 : Blo 1407523 3169997 := bbase (se 3 (by rfl) ⟨594374, by rfl⟩ : syracuseStep 3169997 = 1188749) (by norm_num)
theorem B2113253 : Blo 1407523 2113253 := bbase (se 4 (by rfl) ⟨198117, by rfl⟩ : syracuseStep 2113253 = 396235) (by norm_num)
theorem B7134965 : Blo 1407523 7134965 := bbase (se 5 (by rfl) ⟨334451, by rfl⟩ : syracuseStep 7134965 = 668903) (by norm_num)
theorem B3563261 : Blo 1407523 3563261 := bbase (se 3 (by rfl) ⟨668111, by rfl⟩ : syracuseStep 3563261 = 1336223) (by norm_num)
theorem B2113277 : Blo 1407523 2113277 := bbase (se 3 (by rfl) ⟨396239, by rfl⟩ : syracuseStep 2113277 = 792479) (by norm_num)
theorem B3006229 : Blo 1407523 3006229 := bbase (se 6 (by rfl) ⟨70458, by rfl⟩ : syracuseStep 3006229 = 140917) (by norm_num)
theorem B2113301 : Blo 1407523 2113301 := bbase (se 6 (by rfl) ⟨49530, by rfl⟩ : syracuseStep 2113301 = 99061) (by norm_num)
theorem B3170069 : Blo 1407523 3170069 := bbase (se 6 (by rfl) ⟨74298, by rfl⟩ : syracuseStep 3170069 = 148597) (by norm_num)
theorem B2375453 : Blo 1407523 2375453 := bbase (se 3 (by rfl) ⟨445397, by rfl⟩ : syracuseStep 2375453 = 890795) (by norm_num)
theorem B2113325 : Blo 1407523 2113325 := bbase (se 3 (by rfl) ⟨396248, by rfl⟩ : syracuseStep 2113325 = 792497) (by norm_num)
theorem B4570933 : Blo 1407523 4570933 := bbase (se 5 (by rfl) ⟨214262, by rfl⟩ : syracuseStep 4570933 = 428525) (by norm_num)
theorem B3383093 : Blo 1407523 3383093 := bbase (se 5 (by rfl) ⟨158582, by rfl⟩ : syracuseStep 3383093 = 317165) (by norm_num)
theorem B2113349 : Blo 1407523 2113349 := bbase (se 4 (by rfl) ⟨198126, by rfl⟩ : syracuseStep 2113349 = 396253) (by norm_num)
theorem B4751189 : Blo 1407523 4751189 := bbase (se 9 (by rfl) ⟨13919, by rfl⟩ : syracuseStep 4751189 = 27839) (by norm_num)
theorem B2006869 : Blo 1407523 2006869 := bbase (se 9 (by rfl) ⟨5879, by rfl⟩ : syracuseStep 2006869 = 11759) (by norm_num)
theorem B2113373 : Blo 1407523 2113373 := bbase (se 3 (by rfl) ⟨396257, by rfl⟩ : syracuseStep 2113373 = 792515) (by norm_num)
theorem B3170141 : Blo 1407523 3170141 := bbase (se 3 (by rfl) ⟨594401, by rfl⟩ : syracuseStep 3170141 = 1188803) (by norm_num)
theorem B2408309 : Blo 1407523 2408309 := bbase (se 5 (by rfl) ⟨112889, by rfl⟩ : syracuseStep 2408309 = 225779) (by norm_num)
theorem B9633653 : Blo 1407523 9633653 := bbase (se 5 (by rfl) ⟨451577, by rfl⟩ : syracuseStep 9633653 = 903155) (by norm_num)
theorem B2113397 : Blo 1407523 2113397 := bbase (se 5 (by rfl) ⟨99065, by rfl⟩ : syracuseStep 2113397 = 198131) (by norm_num)
theorem B2236285 : Blo 1407523 2236285 := bbase (se 3 (by rfl) ⟨419303, by rfl⟩ : syracuseStep 2236285 = 838607) (by norm_num)
theorem B2113421 : Blo 1407523 2113421 := bbase (se 3 (by rfl) ⟨396266, by rfl⟩ : syracuseStep 2113421 = 792533) (by norm_num)
theorem B2375581 : Blo 1407523 2375581 := bbase (se 3 (by rfl) ⟨445421, by rfl⟩ : syracuseStep 2375581 = 890843) (by norm_num)
theorem B2113445 : Blo 1407523 2113445 := bbase (se 4 (by rfl) ⟨198135, by rfl⟩ : syracuseStep 2113445 = 396271) (by norm_num)
theorem B3170213 : Blo 1407523 3170213 := bbase (se 4 (by rfl) ⟨297207, by rfl⟩ : syracuseStep 3170213 = 594415) (by norm_num)
theorem B3563453 : Blo 1407523 3563453 := bbase (se 3 (by rfl) ⟨668147, by rfl⟩ : syracuseStep 3563453 = 1336295) (by norm_num)
theorem B2113469 : Blo 1407523 2113469 := bbase (se 3 (by rfl) ⟨396275, by rfl⟩ : syracuseStep 2113469 = 792551) (by norm_num)
theorem B2113493 : Blo 1407523 2113493 := bbase (se 7 (by rfl) ⟨24767, by rfl⟩ : syracuseStep 2113493 = 49535) (by norm_num)
theorem B2113517 : Blo 1407523 2113517 := bbase (se 3 (by rfl) ⟨396284, by rfl⟩ : syracuseStep 2113517 = 792569) (by norm_num)
theorem B3170285 : Blo 1407523 3170285 := bbase (se 3 (by rfl) ⟨594428, by rfl⟩ : syracuseStep 3170285 = 1188857) (by norm_num)
theorem B2375669 : Blo 1407523 2375669 := bbase (se 5 (by rfl) ⟨111359, by rfl⟩ : syracuseStep 2375669 = 222719) (by norm_num)
theorem B1409027 : Blo 1407523 1409027 := bstep (se 1 (by rfl) ⟨1056770, by rfl⟩ : syracuseStep 1409027 = 2113541) B2113541
theorem B3170321 : Blo 1407523 3170321 := bstep (se 2 (by rfl) ⟨1188870, by rfl⟩ : syracuseStep 3170321 = 2377741) B2377741
theorem B2113553 : Blo 1407523 2113553 := bstep (se 2 (by rfl) ⟨792582, by rfl⟩ : syracuseStep 2113553 = 1585165) B1585165
theorem B1409043 : Blo 1407523 1409043 := bstep (se 1 (by rfl) ⟨1056782, by rfl⟩ : syracuseStep 1409043 = 2113565) B2113565
theorem B3170339 : Blo 1407523 3170339 := bstep (se 1 (by rfl) ⟨2377754, by rfl⟩ : syracuseStep 3170339 = 4755509) B4755509
theorem B2113571 : Blo 1407523 2113571 := bstep (se 1 (by rfl) ⟨1585178, by rfl⟩ : syracuseStep 2113571 = 3170357) B3170357
theorem B1409059 : Blo 1407523 1409059 := bstep (se 1 (by rfl) ⟨1056794, by rfl⟩ : syracuseStep 1409059 = 2113589) B2113589
theorem B4751405 : Blo 1407523 4751405 := bstep (se 3 (by rfl) ⟨890888, by rfl⟩ : syracuseStep 4751405 = 1781777) B1781777
theorem B1409075 : Blo 1407523 1409075 := bstep (se 1 (by rfl) ⟨1056806, by rfl⟩ : syracuseStep 1409075 = 2113613) B2113613
theorem B2113601 : Blo 1407523 2113601 := bstep (se 2 (by rfl) ⟨792600, by rfl⟩ : syracuseStep 2113601 = 1585201) B1585201
theorem B1409091 : Blo 1407523 1409091 := bstep (se 1 (by rfl) ⟨1056818, by rfl⟩ : syracuseStep 1409091 = 2113637) B2113637
theorem B2113619 : Blo 1407523 2113619 := bstep (se 1 (by rfl) ⟨1585214, by rfl⟩ : syracuseStep 2113619 = 3170429) B3170429
theorem B1409107 : Blo 1407523 1409107 := bstep (se 1 (by rfl) ⟨1056830, by rfl⟩ : syracuseStep 1409107 = 2113661) B2113661
theorem B2375777 : Blo 1407523 2375777 := bstep (se 2 (by rfl) ⟨890916, by rfl⟩ : syracuseStep 2375777 = 1781833) B1781833
theorem B4751459 : Blo 1407523 4751459 := bstep (se 1 (by rfl) ⟨3563594, by rfl⟩ : syracuseStep 4751459 = 7127189) B7127189
theorem B1409123 : Blo 1407523 1409123 := bstep (se 1 (by rfl) ⟨1056842, by rfl⟩ : syracuseStep 1409123 = 2113685) B2113685
theorem B2113649 : Blo 1407523 2113649 := bstep (se 2 (by rfl) ⟨792618, by rfl⟩ : syracuseStep 2113649 = 1585237) B1585237
theorem B1409139 : Blo 1407523 1409139 := bstep (se 1 (by rfl) ⟨1056854, by rfl⟩ : syracuseStep 1409139 = 2113709) B2113709
theorem B2113667 : Blo 1407523 2113667 := bstep (se 1 (by rfl) ⟨1585250, by rfl⟩ : syracuseStep 2113667 = 3170501) B3170501
theorem B1409155 : Blo 1407523 1409155 := bstep (se 1 (by rfl) ⟨1056866, by rfl⟩ : syracuseStep 1409155 = 2113733) B2113733
theorem B1409171 : Blo 1407523 1409171 := bstep (se 1 (by rfl) ⟨1056878, by rfl⟩ : syracuseStep 1409171 = 2113757) B2113757
theorem B2113697 : Blo 1407523 2113697 := bstep (se 2 (by rfl) ⟨792636, by rfl⟩ : syracuseStep 2113697 = 1585273) B1585273
theorem B1409187 : Blo 1407523 1409187 := bstep (se 1 (by rfl) ⟨1056890, by rfl⟩ : syracuseStep 1409187 = 2113781) B2113781
theorem B2113715 : Blo 1407523 2113715 := bstep (se 1 (by rfl) ⟨1585286, by rfl⟩ : syracuseStep 2113715 = 3170573) B3170573
theorem B1409203 : Blo 1407523 1409203 := bstep (se 1 (by rfl) ⟨1056902, by rfl⟩ : syracuseStep 1409203 = 2113805) B2113805
theorem B1409219 : Blo 1407523 1409219 := bstep (se 1 (by rfl) ⟨1056914, by rfl⟩ : syracuseStep 1409219 = 2113829) B2113829
theorem B2113745 : Blo 1407523 2113745 := bstep (se 2 (by rfl) ⟨792654, by rfl⟩ : syracuseStep 2113745 = 1585309) B1585309
theorem B1409235 : Blo 1407523 1409235 := bstep (se 1 (by rfl) ⟨1056926, by rfl⟩ : syracuseStep 1409235 = 2113853) B2113853
theorem B2375905 : Blo 1407523 2375905 := bstep (se 2 (by rfl) ⟨890964, by rfl⟩ : syracuseStep 2375905 = 1781929) B1781929
theorem B3563747 : Blo 1407523 3563747 := bstep (se 1 (by rfl) ⟨2672810, by rfl⟩ : syracuseStep 3563747 = 5345621) B5345621
theorem B2113763 : Blo 1407523 2113763 := bstep (se 1 (by rfl) ⟨1585322, by rfl⟩ : syracuseStep 2113763 = 3170645) B3170645
theorem B1409251 : Blo 1407523 1409251 := bstep (se 1 (by rfl) ⟨1056938, by rfl⟩ : syracuseStep 1409251 = 2113877) B2113877
theorem B9019633 : Blo 1407523 9019633 := bstep (se 2 (by rfl) ⟨3382362, by rfl⟩ : syracuseStep 9019633 = 6764725) B6764725
theorem B1409267 : Blo 1407523 1409267 := bstep (se 1 (by rfl) ⟨1056950, by rfl⟩ : syracuseStep 1409267 = 2113901) B2113901
theorem B2113793 : Blo 1407523 2113793 := bstep (se 2 (by rfl) ⟨792672, by rfl⟩ : syracuseStep 2113793 = 1585345) B1585345
theorem B2375939 : Blo 1407523 2375939 := bstep (se 1 (by rfl) ⟨1781954, by rfl⟩ : syracuseStep 2375939 = 3563909) B3563909
theorem B1409283 : Blo 1407523 1409283 := bstep (se 1 (by rfl) ⟨1056962, by rfl⟩ : syracuseStep 1409283 = 2113925) B2113925
theorem B3809549 : Blo 1407523 3809549 := bstep (se 3 (by rfl) ⟨714290, by rfl⟩ : syracuseStep 3809549 = 1428581) B1428581
theorem B2113811 : Blo 1407523 2113811 := bstep (se 1 (by rfl) ⟨1585358, by rfl⟩ : syracuseStep 2113811 = 3170717) B3170717
theorem B1409299 : Blo 1407523 1409299 := bstep (se 1 (by rfl) ⟨1056974, by rfl⟩ : syracuseStep 1409299 = 2113949) B2113949
theorem B1409315 : Blo 1407523 1409315 := bstep (se 1 (by rfl) ⟨1056986, by rfl⟩ : syracuseStep 1409315 = 2113973) B2113973
theorem B3170609 : Blo 1407523 3170609 := bstep (se 2 (by rfl) ⟨1188978, by rfl⟩ : syracuseStep 3170609 = 2377957) B2377957
theorem B2113841 : Blo 1407523 2113841 := bstep (se 2 (by rfl) ⟨792690, by rfl⟩ : syracuseStep 2113841 = 1585381) B1585381
theorem B1409331 : Blo 1407523 1409331 := bstep (se 1 (by rfl) ⟨1056998, by rfl⟩ : syracuseStep 1409331 = 2113997) B2113997
theorem B3170627 : Blo 1407523 3170627 := bstep (se 1 (by rfl) ⟨2377970, by rfl⟩ : syracuseStep 3170627 = 4755941) B4755941
theorem B2113859 : Blo 1407523 2113859 := bstep (se 1 (by rfl) ⟨1585394, by rfl⟩ : syracuseStep 2113859 = 3170789) B3170789
theorem B1409347 : Blo 1407523 1409347 := bstep (se 1 (by rfl) ⟨1057010, by rfl⟩ : syracuseStep 1409347 = 2114021) B2114021
theorem B1409363 : Blo 1407523 1409363 := bstep (se 1 (by rfl) ⟨1057022, by rfl⟩ : syracuseStep 1409363 = 2114045) B2114045
theorem B2113889 : Blo 1407523 2113889 := bstep (se 2 (by rfl) ⟨792708, by rfl⟩ : syracuseStep 2113889 = 1585417) B1585417
theorem B4571491 : Blo 1407523 4571491 := bstep (se 1 (by rfl) ⟨3428618, by rfl⟩ : syracuseStep 4571491 = 6857237) B6857237
theorem B1409379 : Blo 1407523 1409379 := bstep (se 1 (by rfl) ⟨1057034, by rfl⟩ : syracuseStep 1409379 = 2114069) B2114069
theorem B4751729 : Blo 1407523 4751729 := bstep (se 2 (by rfl) ⟨1781898, by rfl⟩ : syracuseStep 4751729 = 3563797) B3563797
theorem B2113907 : Blo 1407523 2113907 := bstep (se 1 (by rfl) ⟨1585430, by rfl⟩ : syracuseStep 2113907 = 3170861) B3170861
theorem B1409395 : Blo 1407523 1409395 := bstep (se 1 (by rfl) ⟨1057046, by rfl⟩ : syracuseStep 1409395 = 2114093) B2114093
theorem B2376067 : Blo 1407523 2376067 := bstep (se 1 (by rfl) ⟨1782050, by rfl⟩ : syracuseStep 2376067 = 3564101) B3564101
theorem B1409411 : Blo 1407523 1409411 := bstep (se 1 (by rfl) ⟨1057058, by rfl⟩ : syracuseStep 1409411 = 2114117) B2114117
theorem B2113937 : Blo 1407523 2113937 := bstep (se 2 (by rfl) ⟨792726, by rfl⟩ : syracuseStep 2113937 = 1585453) B1585453
theorem B1409427 : Blo 1407523 1409427 := bstep (se 1 (by rfl) ⟨1057070, by rfl⟩ : syracuseStep 1409427 = 2114141) B2114141
theorem B4063651 : Blo 1407523 4063651 := bstep (se 1 (by rfl) ⟨3047738, by rfl⟩ : syracuseStep 4063651 = 6095477) B6095477
theorem B3563939 : Blo 1407523 3563939 := bstep (se 1 (by rfl) ⟨2672954, by rfl⟩ : syracuseStep 3563939 = 5345909) B5345909
theorem B2113955 : Blo 1407523 2113955 := bstep (se 1 (by rfl) ⟨1585466, by rfl⟩ : syracuseStep 2113955 = 3170933) B3170933
theorem B1409443 : Blo 1407523 1409443 := bstep (se 1 (by rfl) ⟨1057082, by rfl⟩ : syracuseStep 1409443 = 2114165) B2114165
theorem B1409459 : Blo 1407523 1409459 := bstep (se 1 (by rfl) ⟨1057094, by rfl⟩ : syracuseStep 1409459 = 2114189) B2114189
theorem B2113985 : Blo 1407523 2113985 := bstep (se 2 (by rfl) ⟨792744, by rfl⟩ : syracuseStep 2113985 = 1585489) B1585489
theorem B1409475 : Blo 1407523 1409475 := bstep (se 1 (by rfl) ⟨1057106, by rfl⟩ : syracuseStep 1409475 = 2114213) B2114213
theorem B2114003 : Blo 1407523 2114003 := bstep (se 1 (by rfl) ⟨1585502, by rfl⟩ : syracuseStep 2114003 = 3171005) B3171005
theorem B1409491 : Blo 1407523 1409491 := bstep (se 1 (by rfl) ⟨1057118, by rfl⟩ : syracuseStep 1409491 = 2114237) B2114237
theorem B1409507 : Blo 1407523 1409507 := bstep (se 1 (by rfl) ⟨1057130, by rfl⟩ : syracuseStep 1409507 = 2114261) B2114261
theorem B2114033 : Blo 1407523 2114033 := bstep (se 2 (by rfl) ⟨792762, by rfl⟩ : syracuseStep 2114033 = 1585525) B1585525
theorem B1409523 : Blo 1407523 1409523 := bstep (se 1 (by rfl) ⟨1057142, by rfl⟩ : syracuseStep 1409523 = 2114285) B2114285
theorem B4817411 : Blo 1407523 4817411 := bstep (se 1 (by rfl) ⟨3613058, by rfl⟩ : syracuseStep 4817411 = 7226117) B7226117
theorem B2114051 : Blo 1407523 2114051 := bstep (se 1 (by rfl) ⟨1585538, by rfl⟩ : syracuseStep 2114051 = 3171077) B3171077
theorem B2376209 : Blo 1407523 2376209 := bstep (se 2 (by rfl) ⟨891078, by rfl⟩ : syracuseStep 2376209 = 1782157) B1782157
theorem B2114081 : Blo 1407523 2114081 := bstep (se 2 (by rfl) ⟨792780, by rfl⟩ : syracuseStep 2114081 = 1585561) B1585561
theorem B1606195 : Blo 1407523 1606195 := bstep (se 1 (by rfl) ⟨1204646, by rfl⟩ : syracuseStep 1606195 = 2409293) B2409293
theorem B2114099 : Blo 1407523 2114099 := bstep (se 1 (by rfl) ⟨1585574, by rfl⟩ : syracuseStep 2114099 = 3171149) B3171149
theorem B3007057 : Blo 1407523 3007057 := bstep (se 2 (by rfl) ⟨1127646, by rfl⟩ : syracuseStep 3007057 = 2255293) B2255293
theorem B3170897 : Blo 1407523 3170897 := bstep (se 2 (by rfl) ⟨1189086, by rfl⟩ : syracuseStep 3170897 = 2378173) B2378173
theorem B2114129 : Blo 1407523 2114129 := bstep (se 2 (by rfl) ⟨792798, by rfl⟩ : syracuseStep 2114129 = 1585597) B1585597
theorem B3170915 : Blo 1407523 3170915 := bstep (se 1 (by rfl) ⟨2378186, by rfl⟩ : syracuseStep 3170915 = 4756373) B4756373
theorem B2114147 : Blo 1407523 2114147 := bstep (se 1 (by rfl) ⟨1585610, by rfl⟩ : syracuseStep 2114147 = 3171221) B3171221
theorem B2114177 : Blo 1407523 2114177 := bstep (se 2 (by rfl) ⟨792816, by rfl⟩ : syracuseStep 2114177 = 1585633) B1585633
theorem B3383939 : Blo 1407523 3383939 := bstep (se 1 (by rfl) ⟨2537954, by rfl⟩ : syracuseStep 3383939 = 5075909) B5075909
theorem B2376337 : Blo 1407523 2376337 := bstep (se 2 (by rfl) ⟨891126, by rfl⟩ : syracuseStep 2376337 = 1782253) B1782253
theorem B2114195 : Blo 1407523 2114195 := bstep (se 1 (by rfl) ⟨1585646, by rfl⟩ : syracuseStep 2114195 = 3171293) B3171293
theorem B8561315 : Blo 1407523 8561315 := bstep (se 1 (by rfl) ⟨6420986, by rfl⟩ : syracuseStep 8561315 = 12841973) B12841973
theorem B2114225 : Blo 1407523 2114225 := bstep (se 2 (by rfl) ⟨792834, by rfl⟩ : syracuseStep 2114225 = 1585669) B1585669
theorem B2376371 : Blo 1407523 2376371 := bstep (se 1 (by rfl) ⟨1782278, by rfl⟩ : syracuseStep 2376371 = 3564557) B3564557
theorem B2114243 : Blo 1407523 2114243 := bstep (se 1 (by rfl) ⟨1585682, by rfl⟩ : syracuseStep 2114243 = 3171365) B3171365
theorem B2114273 : Blo 1407523 2114273 := bstep (se 2 (by rfl) ⟨792852, by rfl⟩ : syracuseStep 2114273 = 1585705) B1585705
theorem B2376499 : Blo 1407523 2376499 := bstep (se 1 (by rfl) ⟨1782374, by rfl⟩ : syracuseStep 2376499 = 3564749) B3564749
theorem B3171185 : Blo 1407523 3171185 := bstep (se 2 (by rfl) ⟨1189194, by rfl⟩ : syracuseStep 3171185 = 2378389) B2378389
theorem B3171203 : Blo 1407523 3171203 := bstep (se 1 (by rfl) ⟨2378402, by rfl⟩ : syracuseStep 3171203 = 4756805) B4756805
theorem B4752269 : Blo 1407523 4752269 := bstep (se 3 (by rfl) ⟨891050, by rfl⟩ : syracuseStep 4752269 = 1782101) B1782101
theorem B9028529 : Blo 1407523 9028529 := bstep (se 2 (by rfl) ⟨3385698, by rfl⟩ : syracuseStep 9028529 = 6771397) B6771397
theorem B2376641 : Blo 1407523 2376641 := bstep (se 2 (by rfl) ⟨891240, by rfl⟩ : syracuseStep 2376641 = 1782481) B1782481
theorem B4752323 : Blo 1407523 4752323 := bstep (se 1 (by rfl) ⟨3564242, by rfl⟩ : syracuseStep 4752323 = 7128485) B7128485
theorem B4178897 : Blo 1407523 4178897 := bstep (se 2 (by rfl) ⟨1567086, by rfl⟩ : syracuseStep 4178897 = 3134173) B3134173
theorem B3007459 : Blo 1407523 3007459 := bstep (se 1 (by rfl) ⟨2255594, by rfl⟩ : syracuseStep 3007459 = 4511189) B4511189
theorem B2376769 : Blo 1407523 2376769 := bstep (se 2 (by rfl) ⟨891288, by rfl⟩ : syracuseStep 2376769 = 1782577) B1782577
theorem B10839109 : Blo 1407523 10839109 := bstep (se 4 (by rfl) ⟨1016166, by rfl⟩ : syracuseStep 10839109 = 2032333) B2032333
theorem B2376803 : Blo 1407523 2376803 := bstep (se 1 (by rfl) ⟨1782602, by rfl⟩ : syracuseStep 2376803 = 3565205) B3565205
theorem B3384497 : Blo 1407523 3384497 := bstep (se 2 (by rfl) ⟨1269186, by rfl⟩ : syracuseStep 3384497 = 2538373) B2538373
theorem B4752593 : Blo 1407523 4752593 := bstep (se 2 (by rfl) ⟨1782222, by rfl⟩ : syracuseStep 4752593 = 3564445) B3564445
theorem B2376931 : Blo 1407523 2376931 := bstep (se 1 (by rfl) ⟨1782698, by rfl⟩ : syracuseStep 2376931 = 3565397) B3565397
theorem B1983745 : Blo 1407523 1983745 := bstep (se 2 (by rfl) ⟨743904, by rfl⟩ : syracuseStep 1983745 = 1487809) B1487809
theorem B3564881 : Blo 1407523 3564881 := bstep (se 2 (by rfl) ⟨1336830, by rfl⟩ : syracuseStep 3564881 = 2673661) B2673661
theorem B6423907 : Blo 1407523 6423907 := bstep (se 1 (by rfl) ⟨4817930, by rfl⟩ : syracuseStep 6423907 = 9635861) B9635861
theorem B2377073 : Blo 1407523 2377073 := bstep (se 2 (by rfl) ⟨891402, by rfl⟩ : syracuseStep 2377073 = 1782805) B1782805
theorem B5350769 : Blo 1407523 5350769 := bstep (se 2 (by rfl) ⟨2006538, by rfl⟩ : syracuseStep 5350769 = 4013077) B4013077
theorem B3564931 : Blo 1407523 3564931 := bstep (se 1 (by rfl) ⟨2673698, by rfl⟩ : syracuseStep 3564931 = 5347397) B5347397
theorem B6014371 : Blo 1407523 6014371 := bstep (se 1 (by rfl) ⟨4510778, by rfl⟩ : syracuseStep 6014371 = 9021557) B9021557
theorem B2377201 : Blo 1407523 2377201 := bstep (se 2 (by rfl) ⟨891450, by rfl⟩ : syracuseStep 2377201 = 1782901) B1782901
theorem B16483853 : Blo 1407523 16483853 := bstep (se 3 (by rfl) ⟨3090722, by rfl⟩ : syracuseStep 16483853 = 6181445) B6181445
theorem B3565073 : Blo 1407523 3565073 := bstep (se 2 (by rfl) ⟨1336902, by rfl⟩ : syracuseStep 3565073 = 2673805) B2673805
theorem B2377235 : Blo 1407523 2377235 := bstep (se 1 (by rfl) ⟨1782926, by rfl⟩ : syracuseStep 2377235 = 3565853) B3565853
theorem B2033251 : Blo 1407523 2033251 := bstep (se 1 (by rfl) ⟨1524938, by rfl⟩ : syracuseStep 2033251 = 3049877) B3049877
theorem B36595313 : Blo 1407523 36595313 := bstep (se 2 (by rfl) ⟨13723242, by rfl⟩ : syracuseStep 36595313 = 27446485) B27446485
theorem B4064899 : Blo 1407523 4064899 := bstep (se 1 (by rfl) ⟨3048674, by rfl⟩ : syracuseStep 4064899 = 6097349) B6097349
theorem B2377363 : Blo 1407523 2377363 := bstep (se 1 (by rfl) ⟨1783022, by rfl⟩ : syracuseStep 2377363 = 3566045) B3566045
theorem B4515533 : Blo 1407523 4515533 := bstep (se 3 (by rfl) ⟨846662, by rfl⟩ : syracuseStep 4515533 = 1693325) B1693325
theorem B4753133 : Blo 1407523 4753133 := bstep (se 3 (by rfl) ⟨891212, by rfl⟩ : syracuseStep 4753133 = 1782425) B1782425
theorem B2377505 : Blo 1407523 2377505 := bstep (se 2 (by rfl) ⟨891564, by rfl⟩ : syracuseStep 2377505 = 1783129) B1783129
theorem B4753187 : Blo 1407523 4753187 := bstep (se 1 (by rfl) ⟨3564890, by rfl⟩ : syracuseStep 4753187 = 7129781) B7129781
theorem B3385169 : Blo 1407523 3385169 := bstep (se 2 (by rfl) ⟨1269438, by rfl⟩ : syracuseStep 3385169 = 2538877) B2538877
theorem B2254691 : Blo 1407523 2254691 := bstep (se 1 (by rfl) ⟨1691018, by rfl⟩ : syracuseStep 2254691 = 3382037) B3382037
theorem B2377633 : Blo 1407523 2377633 := bstep (se 2 (by rfl) ⟨891612, by rfl⟩ : syracuseStep 2377633 = 1783225) B1783225
theorem B2377667 : Blo 1407523 2377667 := bstep (se 1 (by rfl) ⟨1783250, by rfl⟩ : syracuseStep 2377667 = 3566501) B3566501
theorem B2672689 : Blo 1407523 2672689 := bstep (se 2 (by rfl) ⟨1002258, by rfl⟩ : syracuseStep 2672689 = 2004517) B2004517
theorem B4753457 : Blo 1407523 4753457 := bstep (se 2 (by rfl) ⟨1782546, by rfl⟩ : syracuseStep 4753457 = 3565093) B3565093
theorem B2377795 : Blo 1407523 2377795 := bstep (se 1 (by rfl) ⟨1783346, by rfl⟩ : syracuseStep 2377795 = 3566693) B3566693
theorem B2033731 : Blo 1407523 2033731 := bstep (se 1 (by rfl) ⟨1525298, by rfl⟩ : syracuseStep 2033731 = 3050597) B3050597
theorem B13543523 : Blo 1407523 13543523 := bstep (se 1 (by rfl) ⟨10157642, by rfl⟩ : syracuseStep 13543523 = 20315285) B20315285
theorem B9021581 : Blo 1407523 9021581 := bstep (se 3 (by rfl) ⟨1691546, by rfl⟩ : syracuseStep 9021581 = 3383093) B3383093
theorem B2377937 : Blo 1407523 2377937 := bstep (se 2 (by rfl) ⟨891726, by rfl⟩ : syracuseStep 2377937 = 1783453) B1783453
theorem B2378065 : Blo 1407523 2378065 := bstep (se 2 (by rfl) ⟨891774, by rfl⟩ : syracuseStep 2378065 = 1783549) B1783549
theorem B9029987 : Blo 1407523 9029987 := bstep (se 1 (by rfl) ⟨6772490, by rfl⟩ : syracuseStep 9029987 = 13544981) B13544981
theorem B4008305 : Blo 1407523 4008305 := bstep (se 2 (by rfl) ⟨1503114, by rfl⟩ : syracuseStep 4008305 = 3006229) B3006229
theorem B7129457 : Blo 1407523 7129457 := bstep (se 2 (by rfl) ⟨2673546, by rfl⟩ : syracuseStep 7129457 = 5347093) B5347093
theorem B2378099 : Blo 1407523 2378099 := bstep (se 1 (by rfl) ⟨1783574, by rfl⟩ : syracuseStep 2378099 = 3567149) B3567149
theorem B1583491 : Blo 1407523 1583491 := bstep (se 1 (by rfl) ⟨1187618, by rfl⟩ : syracuseStep 1583491 = 2375237) B2375237
theorem B11422093 : Blo 1407523 11422093 := bstep (se 3 (by rfl) ⟨2141642, by rfl⟩ : syracuseStep 11422093 = 4283285) B4283285
theorem B2673091 : Blo 1407523 2673091 := bstep (se 1 (by rfl) ⟨2004818, by rfl⟩ : syracuseStep 2673091 = 4009637) B4009637
theorem B3008963 : Blo 1407523 3008963 := bstep (se 1 (by rfl) ⟨2256722, by rfl⟩ : syracuseStep 3008963 = 4513445) B4513445
theorem B4819409 : Blo 1407523 4819409 := bstep (se 2 (by rfl) ⟨1807278, by rfl⟩ : syracuseStep 4819409 = 3614557) B3614557
theorem B2673137 : Blo 1407523 2673137 := bstep (se 2 (by rfl) ⟨1002426, by rfl⟩ : syracuseStep 2673137 = 2004853) B2004853
theorem B8129009 : Blo 1407523 8129009 := bstep (se 2 (by rfl) ⟨3048378, by rfl⟩ : syracuseStep 8129009 = 6096757) B6096757
theorem B3566065 : Blo 1407523 3566065 := bstep (se 2 (by rfl) ⟨1337274, by rfl⟩ : syracuseStep 3566065 = 2674549) B2674549
theorem B2378227 : Blo 1407523 2378227 := bstep (se 1 (by rfl) ⟨1783670, by rfl⟩ : syracuseStep 2378227 = 3567341) B3567341
theorem B1583635 : Blo 1407523 1583635 := bstep (se 1 (by rfl) ⟨1187726, by rfl⟩ : syracuseStep 1583635 = 2375453) B2375453
theorem B4753997 : Blo 1407523 4753997 := bstep (se 3 (by rfl) ⟨891374, by rfl⟩ : syracuseStep 4753997 = 1782749) B1782749
theorem B3213923 : Blo 1407523 3213923 := bstep (se 1 (by rfl) ⟨2410442, by rfl⟩ : syracuseStep 3213923 = 4820885) B4820885
theorem B2378369 : Blo 1407523 2378369 := bstep (se 2 (by rfl) ⟨891888, by rfl⟩ : syracuseStep 2378369 = 1783777) B1783777
theorem B4754051 : Blo 1407523 4754051 := bstep (se 1 (by rfl) ⟨3565538, by rfl⟩ : syracuseStep 4754051 = 7131077) B7131077
theorem B1583779 : Blo 1407523 1583779 := bstep (se 1 (by rfl) ⟨1187834, by rfl⟩ : syracuseStep 1583779 = 2375669) B2375669
theorem B1903331 : Blo 1407523 1903331 := bstep (se 1 (by rfl) ⟨1427498, by rfl⟩ : syracuseStep 1903331 = 2854997) B2854997
theorem B2378497 : Blo 1407523 2378497 := bstep (se 2 (by rfl) ⟨891936, by rfl⟩ : syracuseStep 2378497 = 1783873) B1783873
theorem B3566339 : Blo 1407523 3566339 := bstep (se 1 (by rfl) ⟨2674754, by rfl⟩ : syracuseStep 3566339 = 5349509) B5349509
theorem B2673425 : Blo 1407523 2673425 := bstep (se 2 (by rfl) ⟨1002534, by rfl⟩ : syracuseStep 2673425 = 2005069) B2005069
theorem B2378531 : Blo 1407523 2378531 := bstep (se 1 (by rfl) ⟨1783898, by rfl⟩ : syracuseStep 2378531 = 3567797) B3567797
theorem B1583923 : Blo 1407523 1583923 := bstep (se 1 (by rfl) ⟨1187942, by rfl⟩ : syracuseStep 1583923 = 2375885) B2375885
theorem B13544333 : Blo 1407523 13544333 := bstep (se 3 (by rfl) ⟨2539562, by rfl⟩ : syracuseStep 13544333 = 5079125) B5079125
theorem B4754321 : Blo 1407523 4754321 := bstep (se 2 (by rfl) ⟨1782870, by rfl⟩ : syracuseStep 4754321 = 3565741) B3565741
theorem B1584067 : Blo 1407523 1584067 := bstep (se 1 (by rfl) ⟨1188050, by rfl⟩ : syracuseStep 1584067 = 2376101) B2376101
theorem B3566531 : Blo 1407523 3566531 := bstep (se 1 (by rfl) ⟨2674898, by rfl⟩ : syracuseStep 3566531 = 5349797) B5349797
theorem B4008977 : Blo 1407523 4008977 := bstep (se 2 (by rfl) ⟨1503366, by rfl⟩ : syracuseStep 4008977 = 3006733) B3006733
theorem B30460981 : Blo 1407523 30460981 := bstep (se 5 (by rfl) ⟨1427858, by rfl⟩ : syracuseStep 30460981 = 2855717) B2855717
theorem B1584211 : Blo 1407523 1584211 := bstep (se 1 (by rfl) ⟨1188158, by rfl⟩ : syracuseStep 1584211 = 2376317) B2376317
theorem B2141363 : Blo 1407523 2141363 := bstep (se 1 (by rfl) ⟨1606022, by rfl⟩ : syracuseStep 2141363 = 3212045) B3212045
theorem B1584355 : Blo 1407523 1584355 := bstep (se 1 (by rfl) ⟨1188266, by rfl⟩ : syracuseStep 1584355 = 2376533) B2376533
theorem B2256113 : Blo 1407523 2256113 := bstep (se 2 (by rfl) ⟨846042, by rfl⟩ : syracuseStep 2256113 = 1692085) B1692085
theorem B9276707 : Blo 1407523 9276707 := bstep (se 1 (by rfl) ⟨6957530, by rfl⟩ : syracuseStep 9276707 = 13915061) B13915061
theorem B3214691 : Blo 1407523 3214691 := bstep (se 1 (by rfl) ⟨2411018, by rfl⟩ : syracuseStep 3214691 = 4822037) B4822037
theorem B6016369 : Blo 1407523 6016369 := bstep (se 2 (by rfl) ⟨2256138, by rfl⟩ : syracuseStep 6016369 = 4512277) B4512277
theorem B1584499 : Blo 1407523 1584499 := bstep (se 1 (by rfl) ⟨1188374, by rfl⟩ : syracuseStep 1584499 = 2376749) B2376749
theorem B4754861 : Blo 1407523 4754861 := bstep (se 3 (by rfl) ⟨891536, by rfl⟩ : syracuseStep 4754861 = 1783073) B1783073
theorem B2674147 : Blo 1407523 2674147 := bstep (se 1 (by rfl) ⟨2005610, by rfl⟩ : syracuseStep 2674147 = 4011221) B4011221
theorem B4754915 : Blo 1407523 4754915 := bstep (se 1 (by rfl) ⟨3566186, by rfl⟩ : syracuseStep 4754915 = 7132373) B7132373
theorem B1584643 : Blo 1407523 1584643 := bstep (se 1 (by rfl) ⟨1188482, by rfl⟩ : syracuseStep 1584643 = 2376965) B2376965
theorem B3010193 : Blo 1407523 3010193 := bstep (se 2 (by rfl) ⟨1128822, by rfl⟩ : syracuseStep 3010193 = 2257645) B2257645
theorem B1584787 : Blo 1407523 1584787 := bstep (se 1 (by rfl) ⟨1188590, by rfl⟩ : syracuseStep 1584787 = 2377181) B2377181
theorem B1781443 : Blo 1407523 1781443 := bstep (se 1 (by rfl) ⟨1336082, by rfl⟩ : syracuseStep 1781443 = 2672165) B2672165
theorem B1830595 : Blo 1407523 1830595 := bstep (se 1 (by rfl) ⟨1372946, by rfl⟩ : syracuseStep 1830595 = 2745893) B2745893
theorem B18058949 : Blo 1407523 18058949 := bstep (se 4 (by rfl) ⟨1693026, by rfl⟩ : syracuseStep 18058949 = 3386053) B3386053
theorem B8564429 : Blo 1407523 8564429 := bstep (se 3 (by rfl) ⟨1605830, by rfl⟩ : syracuseStep 8564429 = 3211661) B3211661
theorem B4755185 : Blo 1407523 4755185 := bstep (se 2 (by rfl) ⟨1783194, by rfl⟩ : syracuseStep 4755185 = 3566389) B3566389
theorem B1904369 : Blo 1407523 1904369 := bstep (se 2 (by rfl) ⟨714138, by rfl⟩ : syracuseStep 1904369 = 1428277) B1428277
theorem B4009763 : Blo 1407523 4009763 := bstep (se 1 (by rfl) ⟨3007322, by rfl⟩ : syracuseStep 4009763 = 6014645) B6014645
theorem B7130915 : Blo 1407523 7130915 := bstep (se 1 (by rfl) ⟨5348186, by rfl⟩ : syracuseStep 7130915 = 10696373) B10696373
theorem B1584931 : Blo 1407523 1584931 := bstep (se 1 (by rfl) ⟨1188698, by rfl⟩ : syracuseStep 1584931 = 2377397) B2377397
theorem B4067117 : Blo 1407523 4067117 := bstep (se 3 (by rfl) ⟨762584, by rfl⟩ : syracuseStep 4067117 = 1525169) B1525169
theorem B10702691 : Blo 1407523 10702691 := bstep (se 1 (by rfl) ⟨8027018, by rfl⟩ : syracuseStep 10702691 = 16054037) B16054037
theorem B3567473 : Blo 1407523 3567473 := bstep (se 2 (by rfl) ⟨1337802, by rfl⟩ : syracuseStep 3567473 = 2675605) B2675605
theorem B3805073 : Blo 1407523 3805073 := bstep (se 2 (by rfl) ⟨1426902, by rfl⟩ : syracuseStep 3805073 = 2853805) B2853805
theorem B2674595 : Blo 1407523 2674595 := bstep (se 1 (by rfl) ⟨2005946, by rfl⟩ : syracuseStep 2674595 = 4011893) B4011893
theorem B3567523 : Blo 1407523 3567523 := bstep (se 1 (by rfl) ⟨2675642, by rfl⟩ : syracuseStep 3567523 = 5351285) B5351285
theorem B1585075 : Blo 1407523 1585075 := bstep (se 1 (by rfl) ⟨1188806, by rfl⟩ : syracuseStep 1585075 = 2377613) B2377613
theorem B3805201 : Blo 1407523 3805201 := bstep (se 2 (by rfl) ⟨1426950, by rfl⟩ : syracuseStep 3805201 = 2853901) B2853901
theorem B2142227 : Blo 1407523 2142227 := bstep (se 1 (by rfl) ⟨1606670, by rfl⟩ : syracuseStep 2142227 = 3213341) B3213341
theorem B3567665 : Blo 1407523 3567665 := bstep (se 2 (by rfl) ⟨1337874, by rfl⟩ : syracuseStep 3567665 = 2675749) B2675749
theorem B1585219 : Blo 1407523 1585219 := bstep (se 1 (by rfl) ⟨1188914, by rfl⟩ : syracuseStep 1585219 = 2377829) B2377829
theorem B2256979 : Blo 1407523 2256979 := bstep (se 1 (by rfl) ⟨1692734, by rfl⟩ : syracuseStep 2256979 = 3385469) B3385469
theorem B4010093 : Blo 1407523 4010093 := bstep (se 3 (by rfl) ⟨751892, by rfl⟩ : syracuseStep 4010093 = 1503785) B1503785
theorem B4010161 : Blo 1407523 4010161 := bstep (se 2 (by rfl) ⟨1503810, by rfl⟩ : syracuseStep 4010161 = 3007621) B3007621
theorem B1781939 : Blo 1407523 1781939 := bstep (se 1 (by rfl) ⟨1336454, by rfl⟩ : syracuseStep 1781939 = 2672909) B2672909
theorem B2674883 : Blo 1407523 2674883 := bstep (se 1 (by rfl) ⟨2006162, by rfl⟩ : syracuseStep 2674883 = 4012325) B4012325
theorem B12038341 : Blo 1407523 12038341 := bstep (se 4 (by rfl) ⟨1128594, by rfl⟩ : syracuseStep 12038341 = 2257189) B2257189
theorem B1585363 : Blo 1407523 1585363 := bstep (se 1 (by rfl) ⟨1189022, by rfl⟩ : syracuseStep 1585363 = 2378045) B2378045
theorem B4755725 : Blo 1407523 4755725 := bstep (se 3 (by rfl) ⟨891698, by rfl⟩ : syracuseStep 4755725 = 1783397) B1783397
theorem B4755779 : Blo 1407523 4755779 := bstep (se 1 (by rfl) ⟨3566834, by rfl⟩ : syracuseStep 4755779 = 7133669) B7133669
theorem B2257235 : Blo 1407523 2257235 := bstep (se 1 (by rfl) ⟨1692926, by rfl⟩ : syracuseStep 2257235 = 3385853) B3385853
theorem B5345635 : Blo 1407523 5345635 := bstep (se 1 (by rfl) ⟨4009226, by rfl⟩ : syracuseStep 5345635 = 8018453) B8018453
theorem B16052579 : Blo 1407523 16052579 := bstep (se 1 (by rfl) ⟨12039434, by rfl⟩ : syracuseStep 16052579 = 24078869) B24078869
theorem B1585507 : Blo 1407523 1585507 := bstep (se 1 (by rfl) ⟨1189130, by rfl⟩ : syracuseStep 1585507 = 2378261) B2378261
theorem B6771107 : Blo 1407523 6771107 := bstep (se 1 (by rfl) ⟨5078330, by rfl⟩ : syracuseStep 6771107 = 10156661) B10156661
theorem B4010435 : Blo 1407523 4010435 := bstep (se 1 (by rfl) ⟨3007826, by rfl⟩ : syracuseStep 4010435 = 6015653) B6015653
theorem B24400325 : Blo 1407523 24400325 := bstep (se 4 (by rfl) ⟨2287530, by rfl⟩ : syracuseStep 24400325 = 4575061) B4575061
theorem B6771185 : Blo 1407523 6771185 := bstep (se 2 (by rfl) ⟨2539194, by rfl⟩ : syracuseStep 6771185 = 5078389) B5078389
theorem B1585651 : Blo 1407523 1585651 := bstep (se 1 (by rfl) ⟨1189238, by rfl⟩ : syracuseStep 1585651 = 2378477) B2378477
theorem B7131725 : Blo 1407523 7131725 := bstep (se 3 (by rfl) ⟨1337198, by rfl⟩ : syracuseStep 7131725 = 2674397) B2674397
theorem B4756049 : Blo 1407523 4756049 := bstep (se 2 (by rfl) ⟨1783518, by rfl⟩ : syracuseStep 4756049 = 3567037) B3567037
theorem B9638597 : Blo 1407523 9638597 := bstep (se 4 (by rfl) ⟨903618, by rfl⟩ : syracuseStep 9638597 = 1807237) B1807237
theorem B1504003 : Blo 1407523 1504003 := bstep (se 1 (by rfl) ⟨1128002, by rfl⟩ : syracuseStep 1504003 = 2256005) B2256005
theorem B4281169 : Blo 1407523 4281169 := bstep (se 2 (by rfl) ⟨1605438, by rfl⟩ : syracuseStep 4281169 = 3210877) B3210877
theorem B1782643 : Blo 1407523 1782643 := bstep (se 1 (by rfl) ⟨1336982, by rfl⟩ : syracuseStep 1782643 = 2673965) B2673965
theorem B4510637 : Blo 1407523 4510637 := bstep (se 3 (by rfl) ⟨845744, by rfl⟩ : syracuseStep 4510637 = 1691489) B1691489
theorem B3167153 : Blo 1407523 3167153 := bstep (se 2 (by rfl) ⟨1187682, by rfl⟩ : syracuseStep 3167153 = 2375365) B2375365
theorem B3167171 : Blo 1407523 3167171 := bstep (se 1 (by rfl) ⟨2375378, by rfl⟩ : syracuseStep 3167171 = 4750757) B4750757
theorem B1782739 : Blo 1407523 1782739 := bstep (se 1 (by rfl) ⟨1337054, by rfl⟩ : syracuseStep 1782739 = 2674109) B2674109
theorem B9769997 : Blo 1407523 9769997 := bstep (se 3 (by rfl) ⟨1831874, by rfl⟩ : syracuseStep 9769997 = 3663749) B3663749
theorem B2708579 : Blo 1407523 2708579 := bstep (se 1 (by rfl) ⟨2031434, by rfl⟩ : syracuseStep 2708579 = 4062869) B4062869
theorem B8016995 : Blo 1407523 8016995 := bstep (se 1 (by rfl) ⟨6012746, by rfl⟩ : syracuseStep 8016995 = 12025493) B12025493
theorem B4756589 : Blo 1407523 4756589 := bstep (se 3 (by rfl) ⟨891860, by rfl⟩ : syracuseStep 4756589 = 1783721) B1783721
theorem B2675825 : Blo 1407523 2675825 := bstep (se 2 (by rfl) ⟨1003434, by rfl⟩ : syracuseStep 2675825 = 2006869) B2006869
theorem B4756643 : Blo 1407523 4756643 := bstep (se 1 (by rfl) ⟨3567482, by rfl⟩ : syracuseStep 4756643 = 7134965) B7134965
theorem B2536643 : Blo 1407523 2536643 := bstep (se 1 (by rfl) ⟨1902482, by rfl⟩ : syracuseStep 2536643 = 3804965) B3804965
theorem B1504451 : Blo 1407523 1504451 := bstep (se 1 (by rfl) ⟨1128338, by rfl⟩ : syracuseStep 1504451 = 2256677) B2256677
theorem B3167441 : Blo 1407523 3167441 := bstep (se 2 (by rfl) ⟨1187790, by rfl⟩ : syracuseStep 3167441 = 2375581) B2375581
theorem B3167459 : Blo 1407523 3167459 := bstep (se 1 (by rfl) ⟨2375594, by rfl⟩ : syracuseStep 3167459 = 4751189) B4751189
theorem B4011277 : Blo 1407523 4011277 := bstep (se 3 (by rfl) ⟨752114, by rfl⟩ : syracuseStep 4011277 = 1504229) B1504229
theorem B4011437 : Blo 1407523 4011437 := bstep (se 3 (by rfl) ⟨752144, by rfl⟩ : syracuseStep 4011437 = 1504289) B1504289
theorem B4756913 : Blo 1407523 4756913 := bstep (se 2 (by rfl) ⟨1783842, by rfl⟩ : syracuseStep 4756913 = 3567685) B3567685
theorem B1783235 : Blo 1407523 1783235 := bstep (se 1 (by rfl) ⟨1337426, by rfl⟩ : syracuseStep 1783235 = 2674853) B2674853
theorem B9024965 : Blo 1407523 9024965 := bstep (se 4 (by rfl) ⟨846090, by rfl⟩ : syracuseStep 9024965 = 1692181) B1692181
theorem B15226339 : Blo 1407523 15226339 := bstep (se 1 (by rfl) ⟨11419754, by rfl⟩ : syracuseStep 15226339 = 22839509) B22839509
theorem B3167729 : Blo 1407523 3167729 := bstep (se 2 (by rfl) ⟨1187898, by rfl⟩ : syracuseStep 3167729 = 2375797) B2375797
theorem B1693171 : Blo 1407523 1693171 := bstep (se 1 (by rfl) ⟨1269878, by rfl⟩ : syracuseStep 1693171 = 2539757) B2539757
theorem B3167747 : Blo 1407523 3167747 := bstep (se 1 (by rfl) ⟨2375810, by rfl⟩ : syracuseStep 3167747 = 4751621) B4751621
theorem B2004545 : Blo 1407523 2004545 := bstep (se 2 (by rfl) ⟨751704, by rfl⟩ : syracuseStep 2004545 = 1503409) B1503409
theorem B4011619 : Blo 1407523 4011619 := bstep (se 1 (by rfl) ⟨3008714, by rfl⟩ : syracuseStep 4011619 = 6017429) B6017429
theorem B1693315 : Blo 1407523 1693315 := bstep (se 1 (by rfl) ⟨1269986, by rfl⟩ : syracuseStep 1693315 = 2539973) B2539973
theorem B2004625 : Blo 1407523 2004625 := bstep (se 2 (by rfl) ⟨751734, by rfl⟩ : syracuseStep 2004625 = 1503469) B1503469
theorem B3168017 : Blo 1407523 3168017 := bstep (se 2 (by rfl) ⟨1188006, by rfl⟩ : syracuseStep 3168017 = 2376013) B2376013
theorem B6764323 : Blo 1407523 6764323 := bstep (se 1 (by rfl) ⟨5073242, by rfl⟩ : syracuseStep 6764323 = 10146485) B10146485
theorem B3168035 : Blo 1407523 3168035 := bstep (se 1 (by rfl) ⟨2376026, by rfl⟩ : syracuseStep 3168035 = 4752053) B4752053
theorem B2111297 : Blo 1407523 2111297 := bstep (se 2 (by rfl) ⟨791736, by rfl⟩ : syracuseStep 2111297 = 1583473) B1583473
theorem B8025925 : Blo 1407523 8025925 := bstep (se 4 (by rfl) ⟨752430, by rfl⟩ : syracuseStep 8025925 = 1504861) B1504861
theorem B2111315 : Blo 1407523 2111315 := bstep (se 1 (by rfl) ⟨1583486, by rfl⟩ : syracuseStep 2111315 = 3166973) B3166973
theorem B2111345 : Blo 1407523 2111345 := bstep (se 2 (by rfl) ⟨791754, by rfl⟩ : syracuseStep 2111345 = 1583509) B1583509
theorem B2111363 : Blo 1407523 2111363 := bstep (se 1 (by rfl) ⟨1583522, by rfl⟩ : syracuseStep 2111363 = 3167045) B3167045
theorem B2111393 : Blo 1407523 2111393 := bstep (se 2 (by rfl) ⟨791772, by rfl⟩ : syracuseStep 2111393 = 1583545) B1583545
theorem B2111411 : Blo 1407523 2111411 := bstep (se 1 (by rfl) ⟨1583558, by rfl⟩ : syracuseStep 2111411 = 3167117) B3167117
theorem B2111441 : Blo 1407523 2111441 := bstep (se 2 (by rfl) ⟨791790, by rfl⟩ : syracuseStep 2111441 = 1583581) B1583581
theorem B2111459 : Blo 1407523 2111459 := bstep (se 1 (by rfl) ⟨1583594, by rfl⟩ : syracuseStep 2111459 = 3167189) B3167189
theorem B15226865 : Blo 1407523 15226865 := bstep (se 2 (by rfl) ⟨5710074, by rfl⟩ : syracuseStep 15226865 = 11420149) B11420149
theorem B2111489 : Blo 1407523 2111489 := bstep (se 2 (by rfl) ⟨791808, by rfl⟩ : syracuseStep 2111489 = 1583617) B1583617
theorem B2111507 : Blo 1407523 2111507 := bstep (se 1 (by rfl) ⟨1583630, by rfl⟩ : syracuseStep 2111507 = 3167261) B3167261
theorem B2111537 : Blo 1407523 2111537 := bstep (se 2 (by rfl) ⟨791826, by rfl⟩ : syracuseStep 2111537 = 1583653) B1583653
theorem B3168305 : Blo 1407523 3168305 := bstep (se 2 (by rfl) ⟨1188114, by rfl⟩ : syracuseStep 3168305 = 2376229) B2376229
theorem B2111555 : Blo 1407523 2111555 := bstep (se 1 (by rfl) ⟨1583666, by rfl⟩ : syracuseStep 2111555 = 3167333) B3167333
theorem B3168323 : Blo 1407523 3168323 := bstep (se 1 (by rfl) ⟨2376242, by rfl⟩ : syracuseStep 3168323 = 4752485) B4752485
theorem B2111585 : Blo 1407523 2111585 := bstep (se 2 (by rfl) ⟨791844, by rfl⟩ : syracuseStep 2111585 = 1583689) B1583689
theorem B2111603 : Blo 1407523 2111603 := bstep (se 1 (by rfl) ⟨1583702, by rfl⟩ : syracuseStep 2111603 = 3167405) B3167405
theorem B2111633 : Blo 1407523 2111633 := bstep (se 2 (by rfl) ⟨791862, by rfl⟩ : syracuseStep 2111633 = 1583725) B1583725
theorem B2111651 : Blo 1407523 2111651 := bstep (se 1 (by rfl) ⟨1583738, by rfl⟩ : syracuseStep 2111651 = 3167477) B3167477
theorem B2111681 : Blo 1407523 2111681 := bstep (se 2 (by rfl) ⟨791880, by rfl⟩ : syracuseStep 2111681 = 1583761) B1583761
theorem B2111699 : Blo 1407523 2111699 := bstep (se 1 (by rfl) ⟨1583774, by rfl⟩ : syracuseStep 2111699 = 3167549) B3167549
theorem B2111729 : Blo 1407523 2111729 := bstep (se 2 (by rfl) ⟨791898, by rfl⟩ : syracuseStep 2111729 = 1583797) B1583797
theorem B2111747 : Blo 1407523 2111747 := bstep (se 1 (by rfl) ⟨1583810, by rfl⟩ : syracuseStep 2111747 = 3167621) B3167621
theorem B2111777 : Blo 1407523 2111777 := bstep (se 2 (by rfl) ⟨791916, by rfl⟩ : syracuseStep 2111777 = 1583833) B1583833
theorem B2111795 : Blo 1407523 2111795 := bstep (se 1 (by rfl) ⟨1583846, by rfl⟩ : syracuseStep 2111795 = 3167693) B3167693
theorem B2111825 : Blo 1407523 2111825 := bstep (se 2 (by rfl) ⟨791934, by rfl⟩ : syracuseStep 2111825 = 1583869) B1583869
theorem B3168593 : Blo 1407523 3168593 := bstep (se 2 (by rfl) ⟨1188222, by rfl⟩ : syracuseStep 3168593 = 2376445) B2376445
theorem B2111843 : Blo 1407523 2111843 := bstep (se 1 (by rfl) ⟨1583882, by rfl⟩ : syracuseStep 2111843 = 3167765) B3167765
theorem B3168611 : Blo 1407523 3168611 := bstep (se 1 (by rfl) ⟨2376458, by rfl⟩ : syracuseStep 3168611 = 4752917) B4752917
theorem B6773105 : Blo 1407523 6773105 := bstep (se 2 (by rfl) ⟨2539914, by rfl⟩ : syracuseStep 6773105 = 5079829) B5079829
theorem B2111873 : Blo 1407523 2111873 := bstep (se 2 (by rfl) ⟨791952, by rfl⟩ : syracuseStep 2111873 = 1583905) B1583905
theorem B9632141 : Blo 1407523 9632141 := bstep (se 3 (by rfl) ⟨1806026, by rfl⟩ : syracuseStep 9632141 = 3612053) B3612053
theorem B2111891 : Blo 1407523 2111891 := bstep (se 1 (by rfl) ⟨1583918, by rfl⟩ : syracuseStep 2111891 = 3167837) B3167837
theorem B2005411 : Blo 1407523 2005411 := bstep (se 1 (by rfl) ⟨1504058, by rfl⟩ : syracuseStep 2005411 = 3008117) B3008117
theorem B2111921 : Blo 1407523 2111921 := bstep (se 2 (by rfl) ⟨791970, by rfl⟩ : syracuseStep 2111921 = 1583941) B1583941
theorem B2111939 : Blo 1407523 2111939 := bstep (se 1 (by rfl) ⟨1583954, by rfl⟩ : syracuseStep 2111939 = 3167909) B3167909
theorem B2111969 : Blo 1407523 2111969 := bstep (se 2 (by rfl) ⟨791988, by rfl⟩ : syracuseStep 2111969 = 1583977) B1583977
theorem B2111987 : Blo 1407523 2111987 := bstep (se 1 (by rfl) ⟨1583990, by rfl⟩ : syracuseStep 2111987 = 3167981) B3167981
theorem B5347853 : Blo 1407523 5347853 := bstep (se 3 (by rfl) ⟨1002722, by rfl⟩ : syracuseStep 5347853 = 2005445) B2005445
theorem B2112017 : Blo 1407523 2112017 := bstep (se 2 (by rfl) ⟨792006, by rfl⟩ : syracuseStep 2112017 = 1584013) B1584013
theorem B1407523 : Blo 1407523 1407523 := bstep (se 1 (by rfl) ⟨1055642, by rfl⟩ : syracuseStep 1407523 = 2111285) B2111285
theorem B2112035 : Blo 1407523 2112035 := bstep (se 1 (by rfl) ⟨1584026, by rfl⟩ : syracuseStep 2112035 = 3168053) B3168053
theorem B1407539 : Blo 1407523 1407539 := bstep (se 1 (by rfl) ⟨1055654, by rfl⟩ : syracuseStep 1407539 = 2111309) B2111309
theorem B2112065 : Blo 1407523 2112065 := bstep (se 2 (by rfl) ⟨792024, by rfl⟩ : syracuseStep 2112065 = 1584049) B1584049
theorem B1407555 : Blo 1407523 1407555 := bstep (se 1 (by rfl) ⟨1055666, by rfl⟩ : syracuseStep 1407555 = 2111333) B2111333
theorem B1407571 : Blo 1407523 1407571 := bstep (se 1 (by rfl) ⟨1055678, by rfl⟩ : syracuseStep 1407571 = 2111357) B2111357
theorem B2112083 : Blo 1407523 2112083 := bstep (se 1 (by rfl) ⟨1584062, by rfl⟩ : syracuseStep 2112083 = 3168125) B3168125
theorem B1407587 : Blo 1407523 1407587 := bstep (se 1 (by rfl) ⟨1055690, by rfl⟩ : syracuseStep 1407587 = 2111381) B2111381
theorem B2112113 : Blo 1407523 2112113 := bstep (se 2 (by rfl) ⟨792042, by rfl⟩ : syracuseStep 2112113 = 1584085) B1584085
theorem B3168881 : Blo 1407523 3168881 := bstep (se 2 (by rfl) ⟨1188330, by rfl⟩ : syracuseStep 3168881 = 2376661) B2376661
theorem B1407603 : Blo 1407523 1407603 := bstep (se 1 (by rfl) ⟨1055702, by rfl⟩ : syracuseStep 1407603 = 2111405) B2111405
theorem B1407619 : Blo 1407523 1407619 := bstep (se 1 (by rfl) ⟨1055714, by rfl⟩ : syracuseStep 1407619 = 2111429) B2111429
theorem B2112131 : Blo 1407523 2112131 := bstep (se 1 (by rfl) ⟨1584098, by rfl⟩ : syracuseStep 2112131 = 3168197) B3168197
theorem B3168899 : Blo 1407523 3168899 := bstep (se 1 (by rfl) ⟨2376674, by rfl⟩ : syracuseStep 3168899 = 4753349) B4753349
theorem B1407635 : Blo 1407523 1407635 := bstep (se 1 (by rfl) ⟨1055726, by rfl⟩ : syracuseStep 1407635 = 2111453) B2111453
theorem B2112161 : Blo 1407523 2112161 := bstep (se 2 (by rfl) ⟨792060, by rfl⟩ : syracuseStep 2112161 = 1584121) B1584121
theorem B1407651 : Blo 1407523 1407651 := bstep (se 1 (by rfl) ⟨1055738, by rfl⟩ : syracuseStep 1407651 = 2111477) B2111477
theorem B4512419 : Blo 1407523 4512419 := bstep (se 1 (by rfl) ⟨3384314, by rfl⟩ : syracuseStep 4512419 = 6768629) B6768629
theorem B1407667 : Blo 1407523 1407667 := bstep (se 1 (by rfl) ⟨1055750, by rfl⟩ : syracuseStep 1407667 = 2111501) B2111501
theorem B2112179 : Blo 1407523 2112179 := bstep (se 1 (by rfl) ⟨1584134, by rfl⟩ : syracuseStep 2112179 = 3168269) B3168269
theorem B1407683 : Blo 1407523 1407683 := bstep (se 1 (by rfl) ⟨1055762, by rfl⟩ : syracuseStep 1407683 = 2111525) B2111525
theorem B2112209 : Blo 1407523 2112209 := bstep (se 2 (by rfl) ⟨792078, by rfl⟩ : syracuseStep 2112209 = 1584157) B1584157
theorem B1407699 : Blo 1407523 1407699 := bstep (se 1 (by rfl) ⟨1055774, by rfl⟩ : syracuseStep 1407699 = 2111549) B2111549
theorem B7125731 : Blo 1407523 7125731 := bstep (se 1 (by rfl) ⟨5344298, by rfl⟩ : syracuseStep 7125731 = 10688597) B10688597
theorem B1407715 : Blo 1407523 1407715 := bstep (se 1 (by rfl) ⟨1055786, by rfl⟩ : syracuseStep 1407715 = 2111573) B2111573
theorem B2112227 : Blo 1407523 2112227 := bstep (se 1 (by rfl) ⟨1584170, by rfl⟩ : syracuseStep 2112227 = 3168341) B3168341
theorem B13023985 : Blo 1407523 13023985 := bstep (se 2 (by rfl) ⟨4883994, by rfl⟩ : syracuseStep 13023985 = 9767989) B9767989
theorem B1407731 : Blo 1407523 1407731 := bstep (se 1 (by rfl) ⟨1055798, by rfl⟩ : syracuseStep 1407731 = 2111597) B2111597
theorem B2112257 : Blo 1407523 2112257 := bstep (se 2 (by rfl) ⟨792096, by rfl⟩ : syracuseStep 2112257 = 1584193) B1584193
theorem B1407747 : Blo 1407523 1407747 := bstep (se 1 (by rfl) ⟨1055810, by rfl⟩ : syracuseStep 1407747 = 2111621) B2111621
theorem B1407763 : Blo 1407523 1407763 := bstep (se 1 (by rfl) ⟨1055822, by rfl⟩ : syracuseStep 1407763 = 2111645) B2111645
theorem B2112275 : Blo 1407523 2112275 := bstep (se 1 (by rfl) ⟨1584206, by rfl⟩ : syracuseStep 2112275 = 3168413) B3168413
theorem B1407779 : Blo 1407523 1407779 := bstep (se 1 (by rfl) ⟨1055834, by rfl⟩ : syracuseStep 1407779 = 2111669) B2111669
theorem B2112305 : Blo 1407523 2112305 := bstep (se 2 (by rfl) ⟨792114, by rfl⟩ : syracuseStep 2112305 = 1584229) B1584229
theorem B1407795 : Blo 1407523 1407795 := bstep (se 1 (by rfl) ⟨1055846, by rfl⟩ : syracuseStep 1407795 = 2111693) B2111693
theorem B1407811 : Blo 1407523 1407811 := bstep (se 1 (by rfl) ⟨1055858, by rfl⟩ : syracuseStep 1407811 = 2111717) B2111717
theorem B2112323 : Blo 1407523 2112323 := bstep (se 1 (by rfl) ⟨1584242, by rfl⟩ : syracuseStep 2112323 = 3168485) B3168485
theorem B1407827 : Blo 1407523 1407827 := bstep (se 1 (by rfl) ⟨1055870, by rfl⟩ : syracuseStep 1407827 = 2111741) B2111741
theorem B2112353 : Blo 1407523 2112353 := bstep (se 2 (by rfl) ⟨792132, by rfl⟩ : syracuseStep 2112353 = 1584265) B1584265
theorem B1407843 : Blo 1407523 1407843 := bstep (se 1 (by rfl) ⟨1055882, by rfl⟩ : syracuseStep 1407843 = 2111765) B2111765
theorem B1407859 : Blo 1407523 1407859 := bstep (se 1 (by rfl) ⟨1055894, by rfl⟩ : syracuseStep 1407859 = 2111789) B2111789
theorem B2112371 : Blo 1407523 2112371 := bstep (se 1 (by rfl) ⟨1584278, by rfl⟩ : syracuseStep 2112371 = 3168557) B3168557
theorem B2005889 : Blo 1407523 2005889 := bstep (se 2 (by rfl) ⟨752208, by rfl⟩ : syracuseStep 2005889 = 1504417) B1504417
theorem B1407875 : Blo 1407523 1407875 := bstep (se 1 (by rfl) ⟨1055906, by rfl⟩ : syracuseStep 1407875 = 2111813) B2111813
theorem B2112401 : Blo 1407523 2112401 := bstep (se 2 (by rfl) ⟨792150, by rfl⟩ : syracuseStep 2112401 = 1584301) B1584301
theorem B1407891 : Blo 1407523 1407891 := bstep (se 1 (by rfl) ⟨1055918, by rfl⟩ : syracuseStep 1407891 = 2111837) B2111837
theorem B3169169 : Blo 1407523 3169169 := bstep (se 2 (by rfl) ⟨1188438, by rfl⟩ : syracuseStep 3169169 = 2376877) B2376877
theorem B1407907 : Blo 1407523 1407907 := bstep (se 1 (by rfl) ⟨1055930, by rfl⟩ : syracuseStep 1407907 = 2111861) B2111861
theorem B2112419 : Blo 1407523 2112419 := bstep (se 1 (by rfl) ⟨1584314, by rfl⟩ : syracuseStep 2112419 = 3168629) B3168629
theorem B3169187 : Blo 1407523 3169187 := bstep (se 1 (by rfl) ⟨2376890, by rfl⟩ : syracuseStep 3169187 = 4753781) B4753781
theorem B1407923 : Blo 1407523 1407923 := bstep (se 1 (by rfl) ⟨1055942, by rfl⟩ : syracuseStep 1407923 = 2111885) B2111885
theorem B2112449 : Blo 1407523 2112449 := bstep (se 2 (by rfl) ⟨792168, by rfl⟩ : syracuseStep 2112449 = 1584337) B1584337
theorem B1407939 : Blo 1407523 1407939 := bstep (se 1 (by rfl) ⟨1055954, by rfl⟩ : syracuseStep 1407939 = 2111909) B2111909
theorem B4013009 : Blo 1407523 4013009 := bstep (se 2 (by rfl) ⟨1504878, by rfl⟩ : syracuseStep 4013009 = 3009757) B3009757
theorem B1407955 : Blo 1407523 1407955 := bstep (se 1 (by rfl) ⟨1055966, by rfl⟩ : syracuseStep 1407955 = 2111933) B2111933
theorem B2112467 : Blo 1407523 2112467 := bstep (se 1 (by rfl) ⟨1584350, by rfl⟩ : syracuseStep 2112467 = 3168701) B3168701
theorem B1407971 : Blo 1407523 1407971 := bstep (se 1 (by rfl) ⟨1055978, by rfl⟩ : syracuseStep 1407971 = 2111957) B2111957
theorem B2538467 : Blo 1407523 2538467 := bstep (se 1 (by rfl) ⟨1903850, by rfl⟩ : syracuseStep 2538467 = 3807701) B3807701
theorem B2112497 : Blo 1407523 2112497 := bstep (se 2 (by rfl) ⟨792186, by rfl⟩ : syracuseStep 2112497 = 1584373) B1584373
theorem B1407987 : Blo 1407523 1407987 := bstep (se 1 (by rfl) ⟨1055990, by rfl⟩ : syracuseStep 1407987 = 2111981) B2111981
theorem B2006003 : Blo 1407523 2006003 := bstep (se 1 (by rfl) ⟨1504502, by rfl⟩ : syracuseStep 2006003 = 3009005) B3009005
theorem B1408003 : Blo 1407523 1408003 := bstep (se 1 (by rfl) ⟨1056002, by rfl⟩ : syracuseStep 1408003 = 2112005) B2112005
theorem B2112515 : Blo 1407523 2112515 := bstep (se 1 (by rfl) ⟨1584386, by rfl⟩ : syracuseStep 2112515 = 3168773) B3168773
theorem B1408019 : Blo 1407523 1408019 := bstep (se 1 (by rfl) ⟨1056014, by rfl⟩ : syracuseStep 1408019 = 2112029) B2112029
theorem B2112545 : Blo 1407523 2112545 := bstep (se 2 (by rfl) ⟨792204, by rfl⟩ : syracuseStep 2112545 = 1584409) B1584409
theorem B1408035 : Blo 1407523 1408035 := bstep (se 1 (by rfl) ⟨1056026, by rfl⟩ : syracuseStep 1408035 = 2112053) B2112053
theorem B1408051 : Blo 1407523 1408051 := bstep (se 1 (by rfl) ⟨1056038, by rfl⟩ : syracuseStep 1408051 = 2112077) B2112077
theorem B2112563 : Blo 1407523 2112563 := bstep (se 1 (by rfl) ⟨1584422, by rfl⟩ : syracuseStep 2112563 = 3168845) B3168845
theorem B1408067 : Blo 1407523 1408067 := bstep (se 1 (by rfl) ⟨1056050, by rfl⟩ : syracuseStep 1408067 = 2112101) B2112101
theorem B2006083 : Blo 1407523 2006083 := bstep (se 1 (by rfl) ⟨1504562, by rfl⟩ : syracuseStep 2006083 = 3009125) B3009125
theorem B18037829 : Blo 1407523 18037829 := bstep (se 4 (by rfl) ⟨1691046, by rfl⟩ : syracuseStep 18037829 = 3382093) B3382093
theorem B4815949 : Blo 1407523 4815949 := bstep (se 3 (by rfl) ⟨902990, by rfl⟩ : syracuseStep 4815949 = 1805981) B1805981
theorem B2112593 : Blo 1407523 2112593 := bstep (se 2 (by rfl) ⟨792222, by rfl⟩ : syracuseStep 2112593 = 1584445) B1584445
theorem B1408083 : Blo 1407523 1408083 := bstep (se 1 (by rfl) ⟨1056062, by rfl⟩ : syracuseStep 1408083 = 2112125) B2112125
theorem B1408099 : Blo 1407523 1408099 := bstep (se 1 (by rfl) ⟨1056074, by rfl⟩ : syracuseStep 1408099 = 2112149) B2112149
theorem B2112611 : Blo 1407523 2112611 := bstep (se 1 (by rfl) ⟨1584458, by rfl⟩ : syracuseStep 2112611 = 3168917) B3168917
theorem B1408115 : Blo 1407523 1408115 := bstep (se 1 (by rfl) ⟨1056086, by rfl⟩ : syracuseStep 1408115 = 2112173) B2112173
theorem B2112641 : Blo 1407523 2112641 := bstep (se 2 (by rfl) ⟨792240, by rfl⟩ : syracuseStep 2112641 = 1584481) B1584481
theorem B1408131 : Blo 1407523 1408131 := bstep (se 1 (by rfl) ⟨1056098, by rfl⟩ : syracuseStep 1408131 = 2112197) B2112197
theorem B2538641 : Blo 1407523 2538641 := bstep (se 2 (by rfl) ⟨951990, by rfl⟩ : syracuseStep 2538641 = 1903981) B1903981
theorem B1408147 : Blo 1407523 1408147 := bstep (se 1 (by rfl) ⟨1056110, by rfl⟩ : syracuseStep 1408147 = 2112221) B2112221
theorem B2112659 : Blo 1407523 2112659 := bstep (se 1 (by rfl) ⟨1584494, by rfl⟩ : syracuseStep 2112659 = 3168989) B3168989
theorem B1408163 : Blo 1407523 1408163 := bstep (se 1 (by rfl) ⟨1056122, by rfl⟩ : syracuseStep 1408163 = 2112245) B2112245
theorem B2112689 : Blo 1407523 2112689 := bstep (se 2 (by rfl) ⟨792258, by rfl⟩ : syracuseStep 2112689 = 1584517) B1584517
theorem B1408179 : Blo 1407523 1408179 := bstep (se 1 (by rfl) ⟨1056134, by rfl⟩ : syracuseStep 1408179 = 2112269) B2112269
theorem B3169457 : Blo 1407523 3169457 := bstep (se 2 (by rfl) ⟨1188546, by rfl⟩ : syracuseStep 3169457 = 2377093) B2377093
theorem B1408195 : Blo 1407523 1408195 := bstep (se 1 (by rfl) ⟨1056146, by rfl⟩ : syracuseStep 1408195 = 2112293) B2112293
theorem B2112707 : Blo 1407523 2112707 := bstep (se 1 (by rfl) ⟨1584530, by rfl⟩ : syracuseStep 2112707 = 3169061) B3169061
theorem B3169475 : Blo 1407523 3169475 := bstep (se 1 (by rfl) ⟨2377106, by rfl⟩ : syracuseStep 3169475 = 4754213) B4754213
theorem B4750541 : Blo 1407523 4750541 := bstep (se 3 (by rfl) ⟨890726, by rfl⟩ : syracuseStep 4750541 = 1781453) B1781453
theorem B5143757 : Blo 1407523 5143757 := bstep (se 3 (by rfl) ⟨964454, by rfl⟩ : syracuseStep 5143757 = 1928909) B1928909
theorem B1408211 : Blo 1407523 1408211 := bstep (se 1 (by rfl) ⟨1056158, by rfl⟩ : syracuseStep 1408211 = 2112317) B2112317
theorem B2112737 : Blo 1407523 2112737 := bstep (se 2 (by rfl) ⟨792276, by rfl⟩ : syracuseStep 2112737 = 1584553) B1584553
theorem B1408227 : Blo 1407523 1408227 := bstep (se 1 (by rfl) ⟨1056170, by rfl⟩ : syracuseStep 1408227 = 2112341) B2112341
theorem B1408243 : Blo 1407523 1408243 := bstep (se 1 (by rfl) ⟨1056182, by rfl⟩ : syracuseStep 1408243 = 2112365) B2112365
theorem B2112755 : Blo 1407523 2112755 := bstep (se 1 (by rfl) ⟨1584566, by rfl⟩ : syracuseStep 2112755 = 3169133) B3169133
theorem B4750595 : Blo 1407523 4750595 := bstep (se 1 (by rfl) ⟨3562946, by rfl⟩ : syracuseStep 4750595 = 7125893) B7125893
theorem B1408259 : Blo 1407523 1408259 := bstep (se 1 (by rfl) ⟨1056194, by rfl⟩ : syracuseStep 1408259 = 2112389) B2112389
theorem B2112785 : Blo 1407523 2112785 := bstep (se 2 (by rfl) ⟨792294, by rfl⟩ : syracuseStep 2112785 = 1584589) B1584589
theorem B1408275 : Blo 1407523 1408275 := bstep (se 1 (by rfl) ⟨1056206, by rfl⟩ : syracuseStep 1408275 = 2112413) B2112413
theorem B1408291 : Blo 1407523 1408291 := bstep (se 1 (by rfl) ⟨1056218, by rfl⟩ : syracuseStep 1408291 = 2112437) B2112437
theorem B2112803 : Blo 1407523 2112803 := bstep (se 1 (by rfl) ⟨1584602, by rfl⟩ : syracuseStep 2112803 = 3169205) B3169205
theorem B6020401 : Blo 1407523 6020401 := bstep (se 2 (by rfl) ⟨2257650, by rfl⟩ : syracuseStep 6020401 = 4515301) B4515301
theorem B1408307 : Blo 1407523 1408307 := bstep (se 1 (by rfl) ⟨1056230, by rfl⟩ : syracuseStep 1408307 = 2112461) B2112461
theorem B2112833 : Blo 1407523 2112833 := bstep (se 2 (by rfl) ⟨792312, by rfl⟩ : syracuseStep 2112833 = 1584625) B1584625
theorem B1408323 : Blo 1407523 1408323 := bstep (se 1 (by rfl) ⟨1056242, by rfl⟩ : syracuseStep 1408323 = 2112485) B2112485
theorem B10288453 : Blo 1407523 10288453 := bstep (se 4 (by rfl) ⟨964542, by rfl⟩ : syracuseStep 10288453 = 1929085) B1929085
theorem B1408339 : Blo 1407523 1408339 := bstep (se 1 (by rfl) ⟨1056254, by rfl⟩ : syracuseStep 1408339 = 2112509) B2112509
theorem B2112851 : Blo 1407523 2112851 := bstep (se 1 (by rfl) ⟨1584638, by rfl⟩ : syracuseStep 2112851 = 3169277) B3169277
theorem B1408355 : Blo 1407523 1408355 := bstep (se 1 (by rfl) ⟨1056266, by rfl⟩ : syracuseStep 1408355 = 2112533) B2112533
theorem B2112881 : Blo 1407523 2112881 := bstep (se 2 (by rfl) ⟨792330, by rfl⟩ : syracuseStep 2112881 = 1584661) B1584661
theorem B1408371 : Blo 1407523 1408371 := bstep (se 1 (by rfl) ⟨1056278, by rfl⟩ : syracuseStep 1408371 = 2112557) B2112557
theorem B1408387 : Blo 1407523 1408387 := bstep (se 1 (by rfl) ⟨1056290, by rfl⟩ : syracuseStep 1408387 = 2112581) B2112581
theorem B2112899 : Blo 1407523 2112899 := bstep (se 1 (by rfl) ⟨1584674, by rfl⟩ : syracuseStep 2112899 = 3169349) B3169349
theorem B3431825 : Blo 1407523 3431825 := bstep (se 2 (by rfl) ⟨1286934, by rfl⟩ : syracuseStep 3431825 = 2573869) B2573869
theorem B1408403 : Blo 1407523 1408403 := bstep (se 1 (by rfl) ⟨1056302, by rfl⟩ : syracuseStep 1408403 = 2112605) B2112605
theorem B2112929 : Blo 1407523 2112929 := bstep (se 2 (by rfl) ⟨792348, by rfl⟩ : syracuseStep 2112929 = 1584697) B1584697
theorem B1408419 : Blo 1407523 1408419 := bstep (se 1 (by rfl) ⟨1056314, by rfl⟩ : syracuseStep 1408419 = 2112629) B2112629
theorem B7134641 : Blo 1407523 7134641 := bstep (se 2 (by rfl) ⟨2675490, by rfl⟩ : syracuseStep 7134641 = 5350981) B5350981
theorem B1408435 : Blo 1407523 1408435 := bstep (se 1 (by rfl) ⟨1056326, by rfl⟩ : syracuseStep 1408435 = 2112653) B2112653
theorem B2112947 : Blo 1407523 2112947 := bstep (se 1 (by rfl) ⟨1584710, by rfl⟩ : syracuseStep 2112947 = 3169421) B3169421
theorem B1408451 : Blo 1407523 1408451 := bstep (se 1 (by rfl) ⟨1056338, by rfl⟩ : syracuseStep 1408451 = 2112677) B2112677
theorem B5078477 : Blo 1407523 5078477 := bstep (se 3 (by rfl) ⟨952214, by rfl⟩ : syracuseStep 5078477 = 1904429) B1904429
theorem B2112977 : Blo 1407523 2112977 := bstep (se 2 (by rfl) ⟨792366, by rfl⟩ : syracuseStep 2112977 = 1584733) B1584733
theorem B3169745 : Blo 1407523 3169745 := bstep (se 2 (by rfl) ⟨1188654, by rfl⟩ : syracuseStep 3169745 = 2377309) B2377309
theorem B1408467 : Blo 1407523 1408467 := bstep (se 1 (by rfl) ⟨1056350, by rfl⟩ : syracuseStep 1408467 = 2112701) B2112701
theorem B12361187 : Blo 1407523 12361187 := bstep (se 1 (by rfl) ⟨9270890, by rfl⟩ : syracuseStep 12361187 = 18541781) B18541781
theorem B1408483 : Blo 1407523 1408483 := bstep (se 1 (by rfl) ⟨1056362, by rfl⟩ : syracuseStep 1408483 = 2112725) B2112725
theorem B2112995 : Blo 1407523 2112995 := bstep (se 1 (by rfl) ⟨1584746, by rfl⟩ : syracuseStep 2112995 = 3169493) B3169493
theorem B3169763 : Blo 1407523 3169763 := bstep (se 1 (by rfl) ⟨2377322, by rfl⟩ : syracuseStep 3169763 = 4754645) B4754645
theorem B1408499 : Blo 1407523 1408499 := bstep (se 1 (by rfl) ⟨1056374, by rfl⟩ : syracuseStep 1408499 = 2112749) B2112749
theorem B2113025 : Blo 1407523 2113025 := bstep (se 2 (by rfl) ⟨792384, by rfl⟩ : syracuseStep 2113025 = 1584769) B1584769
theorem B1408515 : Blo 1407523 1408515 := bstep (se 1 (by rfl) ⟨1056386, by rfl⟩ : syracuseStep 1408515 = 2112773) B2112773
theorem B7126541 : Blo 1407523 7126541 := bstep (se 3 (by rfl) ⟨1336226, by rfl⟩ : syracuseStep 7126541 = 2672453) B2672453
theorem B4816397 : Blo 1407523 4816397 := bstep (se 3 (by rfl) ⟨903074, by rfl⟩ : syracuseStep 4816397 = 1806149) B1806149
theorem B4750865 : Blo 1407523 4750865 := bstep (se 2 (by rfl) ⟨1781574, by rfl⟩ : syracuseStep 4750865 = 3563149) B3563149
theorem B14458381 : Blo 1407523 14458381 := bstep (se 3 (by rfl) ⟨2710946, by rfl⟩ : syracuseStep 14458381 = 5421893) B5421893
theorem B1408531 : Blo 1407523 1408531 := bstep (se 1 (by rfl) ⟨1056398, by rfl⟩ : syracuseStep 1408531 = 2112797) B2112797
theorem B2113043 : Blo 1407523 2113043 := bstep (se 1 (by rfl) ⟨1584782, by rfl⟩ : syracuseStep 2113043 = 3169565) B3169565
theorem B2375203 : Blo 1407523 2375203 := bstep (se 1 (by rfl) ⟨1781402, by rfl⟩ : syracuseStep 2375203 = 3562805) B3562805
theorem B1408547 : Blo 1407523 1408547 := bstep (se 1 (by rfl) ⟨1056410, by rfl⟩ : syracuseStep 1408547 = 2112821) B2112821
theorem B2113073 : Blo 1407523 2113073 := bstep (se 2 (by rfl) ⟨792402, by rfl⟩ : syracuseStep 2113073 = 1584805) B1584805
theorem B1408563 : Blo 1407523 1408563 := bstep (se 1 (by rfl) ⟨1056422, by rfl⟩ : syracuseStep 1408563 = 2112845) B2112845
theorem B100228661 : Blo 1407523 100228661 := bstep (se 5 (by rfl) ⟨4698218, by rfl⟩ : syracuseStep 100228661 = 9396437) B9396437
theorem B1408579 : Blo 1407523 1408579 := bstep (se 1 (by rfl) ⟨1056434, by rfl⟩ : syracuseStep 1408579 = 2112869) B2112869
theorem B2113091 : Blo 1407523 2113091 := bstep (se 1 (by rfl) ⟨1584818, by rfl⟩ : syracuseStep 2113091 = 3169637) B3169637
theorem B1408595 : Blo 1407523 1408595 := bstep (se 1 (by rfl) ⟨1056446, by rfl⟩ : syracuseStep 1408595 = 2112893) B2112893
theorem B2113121 : Blo 1407523 2113121 := bstep (se 2 (by rfl) ⟨792420, by rfl⟩ : syracuseStep 2113121 = 1584841) B1584841
theorem B1408611 : Blo 1407523 1408611 := bstep (se 1 (by rfl) ⟨1056458, by rfl⟩ : syracuseStep 1408611 = 2112917) B2112917
theorem B2006641 : Blo 1407523 2006641 := bstep (se 2 (by rfl) ⟨752490, by rfl⟩ : syracuseStep 2006641 = 1504981) B1504981
theorem B1408627 : Blo 1407523 1408627 := bstep (se 1 (by rfl) ⟨1056470, by rfl⟩ : syracuseStep 1408627 = 2112941) B2112941
theorem B2113139 : Blo 1407523 2113139 := bstep (se 1 (by rfl) ⟨1584854, by rfl⟩ : syracuseStep 2113139 = 3169709) B3169709
theorem B1408643 : Blo 1407523 1408643 := bstep (se 1 (by rfl) ⟨1056482, by rfl⟩ : syracuseStep 1408643 = 2112965) B2112965
theorem B2113169 : Blo 1407523 2113169 := bstep (se 2 (by rfl) ⟨792438, by rfl⟩ : syracuseStep 2113169 = 1584877) B1584877
theorem B1408659 : Blo 1407523 1408659 := bstep (se 1 (by rfl) ⟨1056494, by rfl⟩ : syracuseStep 1408659 = 2112989) B2112989
theorem B1408675 : Blo 1407523 1408675 := bstep (se 1 (by rfl) ⟨1056506, by rfl⟩ : syracuseStep 1408675 = 2113013) B2113013
theorem B2113187 : Blo 1407523 2113187 := bstep (se 1 (by rfl) ⟨1584890, by rfl⟩ : syracuseStep 2113187 = 3169781) B3169781
theorem B2375345 : Blo 1407523 2375345 := bstep (se 2 (by rfl) ⟨890754, by rfl⟩ : syracuseStep 2375345 = 1781509) B1781509
theorem B1408691 : Blo 1407523 1408691 := bstep (se 1 (by rfl) ⟨1056518, by rfl⟩ : syracuseStep 1408691 = 2113037) B2113037
theorem B2113217 : Blo 1407523 2113217 := bstep (se 2 (by rfl) ⟨792456, by rfl⟩ : syracuseStep 2113217 = 1584913) B1584913
theorem B1408707 : Blo 1407523 1408707 := bstep (se 1 (by rfl) ⟨1056530, by rfl⟩ : syracuseStep 1408707 = 2113061) B2113061
theorem B1408723 : Blo 1407523 1408723 := bstep (se 1 (by rfl) ⟨1056542, by rfl⟩ : syracuseStep 1408723 = 2113085) B2113085
theorem B2113235 : Blo 1407523 2113235 := bstep (se 1 (by rfl) ⟨1584926, by rfl⟩ : syracuseStep 2113235 = 3169853) B3169853
theorem B1408739 : Blo 1407523 1408739 := bstep (se 1 (by rfl) ⟨1056554, by rfl⟩ : syracuseStep 1408739 = 2113109) B2113109
theorem B6094577 : Blo 1407523 6094577 := bstep (se 2 (by rfl) ⟨2285466, by rfl⟩ : syracuseStep 6094577 = 4570933) B4570933
theorem B2113265 : Blo 1407523 2113265 := bstep (se 2 (by rfl) ⟨792474, by rfl⟩ : syracuseStep 2113265 = 1584949) B1584949
theorem B1408755 : Blo 1407523 1408755 := bstep (se 1 (by rfl) ⟨1056566, by rfl⟩ : syracuseStep 1408755 = 2113133) B2113133
theorem B3170033 : Blo 1407523 3170033 := bstep (se 2 (by rfl) ⟨1188762, by rfl⟩ : syracuseStep 3170033 = 2377525) B2377525
theorem B1408771 : Blo 1407523 1408771 := bstep (se 1 (by rfl) ⟨1056578, by rfl⟩ : syracuseStep 1408771 = 2113157) B2113157
theorem B2113283 : Blo 1407523 2113283 := bstep (se 1 (by rfl) ⟨1584962, by rfl⟩ : syracuseStep 2113283 = 3169925) B3169925
theorem B3170051 : Blo 1407523 3170051 := bstep (se 1 (by rfl) ⟨2377538, by rfl⟩ : syracuseStep 3170051 = 4755077) B4755077
theorem B1408787 : Blo 1407523 1408787 := bstep (se 1 (by rfl) ⟨1056590, by rfl⟩ : syracuseStep 1408787 = 2113181) B2113181
theorem B2113313 : Blo 1407523 2113313 := bstep (se 2 (by rfl) ⟨792492, by rfl⟩ : syracuseStep 2113313 = 1584985) B1584985
theorem B1408803 : Blo 1407523 1408803 := bstep (se 1 (by rfl) ⟨1056602, by rfl⟩ : syracuseStep 1408803 = 2113205) B2113205
theorem B2375473 : Blo 1407523 2375473 := bstep (se 2 (by rfl) ⟨890802, by rfl⟩ : syracuseStep 2375473 = 1781605) B1781605
theorem B1408819 : Blo 1407523 1408819 := bstep (se 1 (by rfl) ⟨1056614, by rfl⟩ : syracuseStep 1408819 = 2113229) B2113229
theorem B2113331 : Blo 1407523 2113331 := bstep (se 1 (by rfl) ⟨1584998, by rfl⟩ : syracuseStep 2113331 = 3169997) B3169997
theorem B1408835 : Blo 1407523 1408835 := bstep (se 1 (by rfl) ⟨1056626, by rfl⟩ : syracuseStep 1408835 = 2113253) B2113253
theorem B2113361 : Blo 1407523 2113361 := bstep (se 2 (by rfl) ⟨792510, by rfl⟩ : syracuseStep 2113361 = 1585021) B1585021
theorem B2375507 : Blo 1407523 2375507 := bstep (se 1 (by rfl) ⟨1781630, by rfl⟩ : syracuseStep 2375507 = 3563261) B3563261
theorem B1408851 : Blo 1407523 1408851 := bstep (se 1 (by rfl) ⟨1056638, by rfl⟩ : syracuseStep 1408851 = 2113277) B2113277
theorem B2981713 : Blo 1407523 2981713 := bstep (se 2 (by rfl) ⟨1118142, by rfl⟩ : syracuseStep 2981713 = 2236285) B2236285
theorem B1408867 : Blo 1407523 1408867 := bstep (se 1 (by rfl) ⟨1056650, by rfl⟩ : syracuseStep 1408867 = 2113301) B2113301
theorem B2113379 : Blo 1407523 2113379 := bstep (se 1 (by rfl) ⟨1585034, by rfl⟩ : syracuseStep 2113379 = 3170069) B3170069
theorem B1408883 : Blo 1407523 1408883 := bstep (se 1 (by rfl) ⟨1056662, by rfl⟩ : syracuseStep 1408883 = 2113325) B2113325
theorem B2113409 : Blo 1407523 2113409 := bstep (se 2 (by rfl) ⟨792528, by rfl⟩ : syracuseStep 2113409 = 1585057) B1585057
theorem B3383171 : Blo 1407523 3383171 := bstep (se 1 (by rfl) ⟨2537378, by rfl⟩ : syracuseStep 3383171 = 5074757) B5074757
theorem B1408899 : Blo 1407523 1408899 := bstep (se 1 (by rfl) ⟨1056674, by rfl⟩ : syracuseStep 1408899 = 2113349) B2113349
theorem B1408915 : Blo 1407523 1408915 := bstep (se 1 (by rfl) ⟨1056686, by rfl⟩ : syracuseStep 1408915 = 2113373) B2113373
theorem B2113427 : Blo 1407523 2113427 := bstep (se 1 (by rfl) ⟨1585070, by rfl⟩ : syracuseStep 2113427 = 3170141) B3170141
theorem B1605539 : Blo 1407523 1605539 := bstep (se 1 (by rfl) ⟨1204154, by rfl⟩ : syracuseStep 1605539 = 2408309) B2408309
theorem B6422435 : Blo 1407523 6422435 := bstep (se 1 (by rfl) ⟨4816826, by rfl⟩ : syracuseStep 6422435 = 9633653) B9633653
theorem B1408931 : Blo 1407523 1408931 := bstep (se 1 (by rfl) ⟨1056698, by rfl⟩ : syracuseStep 1408931 = 2113397) B2113397
theorem B2113457 : Blo 1407523 2113457 := bstep (se 2 (by rfl) ⟨792546, by rfl⟩ : syracuseStep 2113457 = 1585093) B1585093
theorem B1408947 : Blo 1407523 1408947 := bstep (se 1 (by rfl) ⟨1056710, by rfl⟩ : syracuseStep 1408947 = 2113421) B2113421
theorem B1408963 : Blo 1407523 1408963 := bstep (se 1 (by rfl) ⟨1056722, by rfl⟩ : syracuseStep 1408963 = 2113445) B2113445
theorem B2113475 : Blo 1407523 2113475 := bstep (se 1 (by rfl) ⟨1585106, by rfl⟩ : syracuseStep 2113475 = 3170213) B3170213
theorem B3563473 : Blo 1407523 3563473 := bstep (se 2 (by rfl) ⟨1336302, by rfl⟩ : syracuseStep 3563473 = 2672605) B2672605
theorem B2375635 : Blo 1407523 2375635 := bstep (se 1 (by rfl) ⟨1781726, by rfl⟩ : syracuseStep 2375635 = 3563453) B3563453
theorem B1408979 : Blo 1407523 1408979 := bstep (se 1 (by rfl) ⟨1056734, by rfl⟩ : syracuseStep 1408979 = 2113469) B2113469
theorem B2113505 : Blo 1407523 2113505 := bstep (se 2 (by rfl) ⟨792564, by rfl⟩ : syracuseStep 2113505 = 1585129) B1585129
theorem B4513763 : Blo 1407523 4513763 := bstep (se 1 (by rfl) ⟨3385322, by rfl⟩ : syracuseStep 4513763 = 6770645) B6770645
theorem B1408995 : Blo 1407523 1408995 := bstep (se 1 (by rfl) ⟨1056746, by rfl⟩ : syracuseStep 1408995 = 2113493) B2113493
theorem B1409011 : Blo 1407523 1409011 := bstep (se 1 (by rfl) ⟨1056758, by rfl⟩ : syracuseStep 1409011 = 2113517) B2113517
theorem B2113523 : Blo 1407523 2113523 := bstep (se 1 (by rfl) ⟨1585142, by rfl⟩ : syracuseStep 2113523 = 3170285) B3170285
theorem B2113547 : Blo 1407523 2113547 := bstep (se 1 (by rfl) ⟨1585160, by rfl⟩ : syracuseStep 2113547 = 3170321) B3170321
theorem B1409035 : Blo 1407523 1409035 := bstep (se 1 (by rfl) ⟨1056776, by rfl⟩ : syracuseStep 1409035 = 2113553) B2113553
theorem B2113559 : Blo 1407523 2113559 := bstep (se 1 (by rfl) ⟨1585169, by rfl⟩ : syracuseStep 2113559 = 3170339) B3170339
theorem B1409047 : Blo 1407523 1409047 := bstep (se 1 (by rfl) ⟨1056785, by rfl⟩ : syracuseStep 1409047 = 2113571) B2113571
theorem B1409067 : Blo 1407523 1409067 := bstep (se 1 (by rfl) ⟨1056800, by rfl⟩ : syracuseStep 1409067 = 2113601) B2113601
theorem B1409079 : Blo 1407523 1409079 := bstep (se 1 (by rfl) ⟨1056809, by rfl⟩ : syracuseStep 1409079 = 2113619) B2113619
theorem B3563585 : Blo 1407523 3563585 := bstep (se 2 (by rfl) ⟨1336344, by rfl⟩ : syracuseStep 3563585 = 2672689) B2672689
theorem B77111365 : Blo 1407523 77111365 := bstep (se 4 (by rfl) ⟨7229190, by rfl⟩ : syracuseStep 77111365 = 14458381) B14458381
theorem B1409099 : Blo 1407523 1409099 := bstep (se 1 (by rfl) ⟨1056824, by rfl⟩ : syracuseStep 1409099 = 2113649) B2113649
theorem B1409111 : Blo 1407523 1409111 := bstep (se 1 (by rfl) ⟨1056833, by rfl⟩ : syracuseStep 1409111 = 2113667) B2113667
theorem B3170393 : Blo 1407523 3170393 := bstep (se 2 (by rfl) ⟨1188897, by rfl⟩ : syracuseStep 3170393 = 2377795) B2377795
theorem B2113625 : Blo 1407523 2113625 := bstep (se 2 (by rfl) ⟨792609, by rfl⟩ : syracuseStep 2113625 = 1585219) B1585219
theorem B2711641 : Blo 1407523 2711641 := bstep (se 2 (by rfl) ⟨1016865, by rfl⟩ : syracuseStep 2711641 = 2033731) B2033731
theorem B1409131 : Blo 1407523 1409131 := bstep (se 1 (by rfl) ⟨1056848, by rfl⟩ : syracuseStep 1409131 = 2113697) B2113697
theorem B1409143 : Blo 1407523 1409143 := bstep (se 1 (by rfl) ⟨1056857, by rfl⟩ : syracuseStep 1409143 = 2113715) B2113715
theorem B1409163 : Blo 1407523 1409163 := bstep (se 1 (by rfl) ⟨1056872, by rfl⟩ : syracuseStep 1409163 = 2113745) B2113745
theorem B2375831 : Blo 1407523 2375831 := bstep (se 1 (by rfl) ⟨1781873, by rfl⟩ : syracuseStep 2375831 = 3563747) B3563747
theorem B1409175 : Blo 1407523 1409175 := bstep (se 1 (by rfl) ⟨1056881, by rfl⟩ : syracuseStep 1409175 = 2113763) B2113763
theorem B1409195 : Blo 1407523 1409195 := bstep (se 1 (by rfl) ⟨1056896, by rfl⟩ : syracuseStep 1409195 = 2113793) B2113793
theorem B3170483 : Blo 1407523 3170483 := bstep (se 1 (by rfl) ⟨2377862, by rfl⟩ : syracuseStep 3170483 = 4755725) B4755725
theorem B1409207 : Blo 1407523 1409207 := bstep (se 1 (by rfl) ⟨1056905, by rfl⟩ : syracuseStep 1409207 = 2113811) B2113811
theorem B2113739 : Blo 1407523 2113739 := bstep (se 1 (by rfl) ⟨1585304, by rfl⟩ : syracuseStep 2113739 = 3170609) B3170609
theorem B1409227 : Blo 1407523 1409227 := bstep (se 1 (by rfl) ⟨1056920, by rfl⟩ : syracuseStep 1409227 = 2113841) B2113841
theorem B3170519 : Blo 1407523 3170519 := bstep (se 1 (by rfl) ⟨2377889, by rfl⟩ : syracuseStep 3170519 = 4755779) B4755779
theorem B2113751 : Blo 1407523 2113751 := bstep (se 1 (by rfl) ⟨1585313, by rfl⟩ : syracuseStep 2113751 = 3170627) B3170627
theorem B1409239 : Blo 1407523 1409239 := bstep (se 1 (by rfl) ⟨1056929, by rfl⟩ : syracuseStep 1409239 = 2113859) B2113859
theorem B1409259 : Blo 1407523 1409259 := bstep (se 1 (by rfl) ⟨1056944, by rfl⟩ : syracuseStep 1409259 = 2113889) B2113889
theorem B1409271 : Blo 1407523 1409271 := bstep (se 1 (by rfl) ⟨1056953, by rfl⟩ : syracuseStep 1409271 = 2113907) B2113907
theorem B1409291 : Blo 1407523 1409291 := bstep (se 1 (by rfl) ⟨1056968, by rfl⟩ : syracuseStep 1409291 = 2113937) B2113937
theorem B2375959 : Blo 1407523 2375959 := bstep (se 1 (by rfl) ⟨1781969, by rfl⟩ : syracuseStep 2375959 = 3563939) B3563939
theorem B4514071 : Blo 1407523 4514071 := bstep (se 1 (by rfl) ⟨3385553, by rfl⟩ : syracuseStep 4514071 = 6771107) B6771107
theorem B2113817 : Blo 1407523 2113817 := bstep (se 2 (by rfl) ⟨792681, by rfl⟩ : syracuseStep 2113817 = 1585363) B1585363
theorem B1409303 : Blo 1407523 1409303 := bstep (se 1 (by rfl) ⟨1056977, by rfl⟩ : syracuseStep 1409303 = 2113955) B2113955
theorem B1409323 : Blo 1407523 1409323 := bstep (se 1 (by rfl) ⟨1056992, by rfl⟩ : syracuseStep 1409323 = 2113985) B2113985
theorem B12026177 : Blo 1407523 12026177 := bstep (se 2 (by rfl) ⟨4509816, by rfl⟩ : syracuseStep 12026177 = 9019633) B9019633
theorem B4514123 : Blo 1407523 4514123 := bstep (se 1 (by rfl) ⟨3385592, by rfl⟩ : syracuseStep 4514123 = 6771185) B6771185
theorem B1409355 : Blo 1407523 1409355 := bstep (se 1 (by rfl) ⟨1057016, by rfl⟩ : syracuseStep 1409355 = 2114033) B2114033
theorem B3211607 : Blo 1407523 3211607 := bstep (se 1 (by rfl) ⟨2408705, by rfl⟩ : syracuseStep 3211607 = 4817411) B4817411
theorem B1409367 : Blo 1407523 1409367 := bstep (se 1 (by rfl) ⟨1057025, by rfl⟩ : syracuseStep 1409367 = 2114051) B2114051
theorem B1409387 : Blo 1407523 1409387 := bstep (se 1 (by rfl) ⟨1057040, by rfl⟩ : syracuseStep 1409387 = 2114081) B2114081
theorem B1409399 : Blo 1407523 1409399 := bstep (se 1 (by rfl) ⟨1057049, by rfl⟩ : syracuseStep 1409399 = 2114099) B2114099
theorem B3170699 : Blo 1407523 3170699 := bstep (se 1 (by rfl) ⟨2378024, by rfl⟩ : syracuseStep 3170699 = 4756049) B4756049
theorem B2113931 : Blo 1407523 2113931 := bstep (se 1 (by rfl) ⟨1585448, by rfl⟩ : syracuseStep 2113931 = 3170897) B3170897
theorem B1409419 : Blo 1407523 1409419 := bstep (se 1 (by rfl) ⟨1057064, by rfl⟩ : syracuseStep 1409419 = 2114129) B2114129
theorem B2113943 : Blo 1407523 2113943 := bstep (se 1 (by rfl) ⟨1585457, by rfl⟩ : syracuseStep 2113943 = 3170915) B3170915
theorem B1409431 : Blo 1407523 1409431 := bstep (se 1 (by rfl) ⟨1057073, by rfl⟩ : syracuseStep 1409431 = 2114147) B2114147
theorem B1409451 : Blo 1407523 1409451 := bstep (se 1 (by rfl) ⟨1057088, by rfl⟩ : syracuseStep 1409451 = 2114177) B2114177
theorem B1409463 : Blo 1407523 1409463 := bstep (se 1 (by rfl) ⟨1057097, by rfl⟩ : syracuseStep 1409463 = 2114195) B2114195
theorem B3170753 : Blo 1407523 3170753 := bstep (se 2 (by rfl) ⟨1189032, by rfl⟩ : syracuseStep 3170753 = 2378065) B2378065
theorem B1409483 : Blo 1407523 1409483 := bstep (se 1 (by rfl) ⟨1057112, by rfl⟩ : syracuseStep 1409483 = 2114225) B2114225
theorem B1409495 : Blo 1407523 1409495 := bstep (se 1 (by rfl) ⟨1057121, by rfl⟩ : syracuseStep 1409495 = 2114243) B2114243
theorem B6095321 : Blo 1407523 6095321 := bstep (se 2 (by rfl) ⟨2285745, by rfl⟩ : syracuseStep 6095321 = 4571491) B4571491
theorem B7127513 : Blo 1407523 7127513 := bstep (se 2 (by rfl) ⟨2672817, by rfl⟩ : syracuseStep 7127513 = 5345635) B5345635
theorem B4751837 : Blo 1407523 4751837 := bstep (se 3 (by rfl) ⟨890969, by rfl⟩ : syracuseStep 4751837 = 1781939) B1781939
theorem B5710301 : Blo 1407523 5710301 := bstep (se 3 (by rfl) ⟨1070681, by rfl⟩ : syracuseStep 5710301 = 2141363) B2141363
theorem B2114009 : Blo 1407523 2114009 := bstep (se 2 (by rfl) ⟨792753, by rfl⟩ : syracuseStep 2114009 = 1585507) B1585507
theorem B1409515 : Blo 1407523 1409515 := bstep (se 1 (by rfl) ⟨1057136, by rfl⟩ : syracuseStep 1409515 = 2114273) B2114273
theorem B15229457 : Blo 1407523 15229457 := bstep (se 2 (by rfl) ⟨5711046, by rfl⟩ : syracuseStep 15229457 = 11422093) B11422093
theorem B2114123 : Blo 1407523 2114123 := bstep (se 1 (by rfl) ⟨1585592, by rfl⟩ : syracuseStep 2114123 = 3171185) B3171185
theorem B2114135 : Blo 1407523 2114135 := bstep (se 1 (by rfl) ⟨1585601, by rfl⟩ : syracuseStep 2114135 = 3171203) B3171203
theorem B3564121 : Blo 1407523 3564121 := bstep (se 2 (by rfl) ⟨1336545, by rfl⟩ : syracuseStep 3564121 = 2673091) B2673091
theorem B3007091 : Blo 1407523 3007091 := bstep (se 1 (by rfl) ⟨2255318, by rfl⟩ : syracuseStep 3007091 = 4510637) B4510637
theorem B2785931 : Blo 1407523 2785931 := bstep (se 1 (by rfl) ⟨2089448, by rfl⟩ : syracuseStep 2785931 = 4178897) B4178897
theorem B3170969 : Blo 1407523 3170969 := bstep (se 2 (by rfl) ⟨1189113, by rfl⟩ : syracuseStep 3170969 = 2378227) B2378227
theorem B2114201 : Blo 1407523 2114201 := bstep (se 2 (by rfl) ⟨792825, by rfl⟩ : syracuseStep 2114201 = 1585651) B1585651
theorem B6513331 : Blo 1407523 6513331 := bstep (se 1 (by rfl) ⟨4884998, by rfl⟩ : syracuseStep 6513331 = 9769997) B9769997
theorem B10158797 : Blo 1407523 10158797 := bstep (se 3 (by rfl) ⟨1904774, by rfl⟩ : syracuseStep 10158797 = 3809549) B3809549
theorem B3171059 : Blo 1407523 3171059 := bstep (se 1 (by rfl) ⟨2378294, by rfl⟩ : syracuseStep 3171059 = 4756589) B4756589
theorem B3171095 : Blo 1407523 3171095 := bstep (se 1 (by rfl) ⟨2378321, by rfl⟩ : syracuseStep 3171095 = 4756643) B4756643
theorem B2376587 : Blo 1407523 2376587 := bstep (se 1 (by rfl) ⟨1782440, by rfl⟩ : syracuseStep 2376587 = 3564881) B3564881
theorem B3171275 : Blo 1407523 3171275 := bstep (se 1 (by rfl) ⟨2378456, by rfl⟩ : syracuseStep 3171275 = 4756913) B4756913
theorem B3171329 : Blo 1407523 3171329 := bstep (se 2 (by rfl) ⟨1189248, by rfl⟩ : syracuseStep 3171329 = 2378497) B2378497
theorem B2376715 : Blo 1407523 2376715 := bstep (se 1 (by rfl) ⟨1782536, by rfl⟩ : syracuseStep 2376715 = 3565073) B3565073
theorem B24396875 : Blo 1407523 24396875 := bstep (se 1 (by rfl) ⟨18297656, by rfl⟩ : syracuseStep 24396875 = 36595313) B36595313
theorem B2376857 : Blo 1407523 2376857 := bstep (se 2 (by rfl) ⟨891321, by rfl⟩ : syracuseStep 2376857 = 1782643) B1782643
theorem B2376985 : Blo 1407523 2376985 := bstep (se 2 (by rfl) ⟨891369, by rfl⟩ : syracuseStep 2376985 = 1782739) B1782739
theorem B21677357 : Blo 1407523 21677357 := bstep (se 3 (by rfl) ⟨4064504, by rfl⟩ : syracuseStep 21677357 = 8129009) B8129009
theorem B10151243 : Blo 1407523 10151243 := bstep (se 1 (by rfl) ⟨7613432, by rfl⟩ : syracuseStep 10151243 = 15226865) B15226865
theorem B9029015 : Blo 1407523 9029015 := bstep (se 1 (by rfl) ⟨6771761, by rfl⟩ : syracuseStep 9029015 = 13543523) B13543523
theorem B14452145 : Blo 1407523 14452145 := bstep (se 2 (by rfl) ⟨5419554, by rfl⟩ : syracuseStep 14452145 = 10839109) B10839109
theorem B6014387 : Blo 1407523 6014387 := bstep (se 1 (by rfl) ⟨4510790, by rfl⟩ : syracuseStep 6014387 = 9021581) B9021581
theorem B2672203 : Blo 1407523 2672203 := bstep (se 1 (by rfl) ⟨2004152, by rfl⟩ : syracuseStep 2672203 = 4008305) B4008305
theorem B4752971 : Blo 1407523 4752971 := bstep (se 1 (by rfl) ⟨3564728, by rfl⟩ : syracuseStep 4752971 = 7129457) B7129457
theorem B8570461 : Blo 1407523 8570461 := bstep (se 3 (by rfl) ⟨1606961, by rfl⟩ : syracuseStep 8570461 = 3213923) B3213923
theorem B3212939 : Blo 1407523 3212939 := bstep (se 1 (by rfl) ⟨2409704, by rfl⟩ : syracuseStep 3212939 = 4819409) B4819409
theorem B3565235 : Blo 1407523 3565235 := bstep (se 1 (by rfl) ⟨2673926, by rfl⟩ : syracuseStep 3565235 = 5347853) B5347853
theorem B3008279 : Blo 1407523 3008279 := bstep (se 1 (by rfl) ⟨2256209, by rfl⟩ : syracuseStep 3008279 = 4512419) B4512419
theorem B8021825 : Blo 1407523 8021825 := bstep (se 2 (by rfl) ⟨3008184, by rfl⟩ : syracuseStep 8021825 = 6016369) B6016369
theorem B2377559 : Blo 1407523 2377559 := bstep (se 1 (by rfl) ⟨1783169, by rfl⟩ : syracuseStep 2377559 = 3566339) B3566339
theorem B4753241 : Blo 1407523 4753241 := bstep (se 2 (by rfl) ⟨1782465, by rfl⟩ : syracuseStep 4753241 = 3564931) B3564931
theorem B9029555 : Blo 1407523 9029555 := bstep (se 1 (by rfl) ⟨6772166, by rfl⟩ : syracuseStep 9029555 = 13544333) B13544333
theorem B2377687 : Blo 1407523 2377687 := bstep (se 1 (by rfl) ⟨1783265, by rfl⟩ : syracuseStep 2377687 = 3566531) B3566531
theorem B20301785 : Blo 1407523 20301785 := bstep (se 2 (by rfl) ⟨7613169, by rfl⟩ : syracuseStep 20301785 = 15226339) B15226339
theorem B3565529 : Blo 1407523 3565529 := bstep (se 2 (by rfl) ⟨1337073, by rfl⟩ : syracuseStep 3565529 = 2674147) B2674147
theorem B2672651 : Blo 1407523 2672651 := bstep (se 1 (by rfl) ⟨2004488, by rfl⟩ : syracuseStep 2672651 = 4008977) B4008977
theorem B7129133 : Blo 1407523 7129133 := bstep (se 3 (by rfl) ⟨1336712, by rfl⟩ : syracuseStep 7129133 = 2673425) B2673425
theorem B2672833 : Blo 1407523 2672833 := bstep (se 2 (by rfl) ⟨1002312, by rfl⟩ : syracuseStep 2672833 = 2004625) B2004625
theorem B2287883 : Blo 1407523 2287883 := bstep (se 1 (by rfl) ⟨1715912, by rfl⟩ : syracuseStep 2287883 = 3431825) B3431825
theorem B3385651 : Blo 1407523 3385651 := bstep (se 1 (by rfl) ⟨2539238, by rfl⟩ : syracuseStep 3385651 = 5078477) B5078477
theorem B10701233 : Blo 1407523 10701233 := bstep (se 2 (by rfl) ⟨4012962, by rfl⟩ : syracuseStep 10701233 = 8025925) B8025925
theorem B3975617 : Blo 1407523 3975617 := bstep (se 2 (by rfl) ⟨1490856, by rfl⟩ : syracuseStep 3975617 = 2981713) B2981713
theorem B1583563 : Blo 1407523 1583563 := bstep (se 1 (by rfl) ⟨1187672, by rfl⟩ : syracuseStep 1583563 = 2375345) B2375345
theorem B2673175 : Blo 1407523 2673175 := bstep (se 1 (by rfl) ⟨2004881, by rfl⟩ : syracuseStep 2673175 = 4009763) B4009763
theorem B4753943 : Blo 1407523 4753943 := bstep (se 1 (by rfl) ⟨3565457, by rfl⟩ : syracuseStep 4753943 = 7130915) B7130915
theorem B1583671 : Blo 1407523 1583671 := bstep (se 1 (by rfl) ⟨1187753, by rfl⟩ : syracuseStep 1583671 = 2375507) B2375507
theorem B2378315 : Blo 1407523 2378315 := bstep (se 1 (by rfl) ⟨1783736, by rfl⟩ : syracuseStep 2378315 = 3567473) B3567473
theorem B2255447 : Blo 1407523 2255447 := bstep (se 1 (by rfl) ⟨1691585, by rfl⟩ : syracuseStep 2255447 = 3383171) B3383171
theorem B12036701 : Blo 1407523 12036701 := bstep (se 3 (by rfl) ⟨2256881, by rfl⟩ : syracuseStep 12036701 = 4513763) B4513763
theorem B5073601 : Blo 1407523 5073601 := bstep (se 2 (by rfl) ⟨1902600, by rfl⟩ : syracuseStep 5073601 = 3805201) B3805201
theorem B2378443 : Blo 1407523 2378443 := bstep (se 1 (by rfl) ⟨1783832, by rfl⟩ : syracuseStep 2378443 = 3567665) B3567665
theorem B5712605 : Blo 1407523 5712605 := bstep (se 3 (by rfl) ⟨1071113, by rfl⟩ : syracuseStep 5712605 = 2142227) B2142227
theorem B1583851 : Blo 1407523 1583851 := bstep (se 1 (by rfl) ⟨1187888, by rfl⟩ : syracuseStep 1583851 = 2375777) B2375777
theorem B2673395 : Blo 1407523 2673395 := bstep (se 1 (by rfl) ⟨2005046, by rfl⟩ : syracuseStep 2673395 = 4010093) B4010093
theorem B3009305 : Blo 1407523 3009305 := bstep (se 2 (by rfl) ⟨1128489, by rfl⟩ : syracuseStep 3009305 = 2256979) B2256979
theorem B1583959 : Blo 1407523 1583959 := bstep (se 1 (by rfl) ⟨1187969, by rfl⟩ : syracuseStep 1583959 = 2375939) B2375939
theorem B10701719 : Blo 1407523 10701719 := bstep (se 1 (by rfl) ⟨8026289, by rfl⟩ : syracuseStep 10701719 = 16052579) B16052579
theorem B16051121 : Blo 1407523 16051121 := bstep (se 2 (by rfl) ⟨6019170, by rfl⟩ : syracuseStep 16051121 = 12038341) B12038341
theorem B1409015 : Blo 1407523 1409015 := bstep (se 1 (by rfl) ⟨1056761, by rfl⟩ : syracuseStep 1409015 = 2113523) B2113523
theorem B2673623 : Blo 1407523 2673623 := bstep (se 1 (by rfl) ⟨2005217, by rfl⟩ : syracuseStep 2673623 = 4010435) B4010435
theorem B1584139 : Blo 1407523 1584139 := bstep (se 1 (by rfl) ⟨1188104, by rfl⟩ : syracuseStep 1584139 = 2376209) B2376209
theorem B4754483 : Blo 1407523 4754483 := bstep (se 1 (by rfl) ⟨3565862, by rfl⟩ : syracuseStep 4754483 = 7131725) B7131725
theorem B2255959 : Blo 1407523 2255959 := bstep (se 1 (by rfl) ⟨1691969, by rfl⟩ : syracuseStep 2255959 = 3383939) B3383939
theorem B1584247 : Blo 1407523 1584247 := bstep (se 1 (by rfl) ⟨1188185, by rfl⟩ : syracuseStep 1584247 = 2376371) B2376371
theorem B6425731 : Blo 1407523 6425731 := bstep (se 1 (by rfl) ⟨4819298, by rfl⟩ : syracuseStep 6425731 = 9638597) B9638597
theorem B13716685 : Blo 1407523 13716685 := bstep (se 3 (by rfl) ⟨2571878, by rfl⟩ : syracuseStep 13716685 = 5143757) B5143757
theorem B2673881 : Blo 1407523 2673881 := bstep (se 2 (by rfl) ⟨1002705, by rfl⟩ : syracuseStep 2673881 = 2005411) B2005411
theorem B1584427 : Blo 1407523 1584427 := bstep (se 1 (by rfl) ⟨1188320, by rfl⟩ : syracuseStep 1584427 = 2376641) B2376641
theorem B6016301 : Blo 1407523 6016301 := bstep (se 3 (by rfl) ⟨1128056, by rfl⟩ : syracuseStep 6016301 = 2256113) B2256113
theorem B4754753 : Blo 1407523 4754753 := bstep (se 2 (by rfl) ⟨1783032, by rfl⟩ : syracuseStep 4754753 = 3566065) B3566065
theorem B9031013 : Blo 1407523 9031013 := bstep (se 4 (by rfl) ⟨846657, by rfl⟩ : syracuseStep 9031013 = 1693315) B1693315
theorem B5344663 : Blo 1407523 5344663 := bstep (se 1 (by rfl) ⟨4008497, by rfl⟩ : syracuseStep 5344663 = 8016995) B8016995
theorem B1584535 : Blo 1407523 1584535 := bstep (se 1 (by rfl) ⟨1188401, by rfl⟩ : syracuseStep 1584535 = 2376803) B2376803
theorem B4009409 : Blo 1407523 4009409 := bstep (se 2 (by rfl) ⟨1503528, by rfl⟩ : syracuseStep 4009409 = 3007057) B3007057
theorem B2256331 : Blo 1407523 2256331 := bstep (se 1 (by rfl) ⟨1692248, by rfl⟩ : syracuseStep 2256331 = 3384497) B3384497
theorem B1584715 : Blo 1407523 1584715 := bstep (se 1 (by rfl) ⟨1188536, by rfl⟩ : syracuseStep 1584715 = 2377073) B2377073
theorem B3567179 : Blo 1407523 3567179 := bstep (se 1 (by rfl) ⟨2675384, by rfl⟩ : syracuseStep 3567179 = 5350769) B5350769
theorem B2674291 : Blo 1407523 2674291 := bstep (se 1 (by rfl) ⟨2005718, by rfl⟩ : syracuseStep 2674291 = 4011437) B4011437
theorem B6016643 : Blo 1407523 6016643 := bstep (se 1 (by rfl) ⟨4512482, by rfl⟩ : syracuseStep 6016643 = 9024965) B9024965
theorem B10989235 : Blo 1407523 10989235 := bstep (se 1 (by rfl) ⟨8241926, by rfl⟩ : syracuseStep 10989235 = 16483853) B16483853
theorem B1584823 : Blo 1407523 1584823 := bstep (se 1 (by rfl) ⟨1188617, by rfl⟩ : syracuseStep 1584823 = 2377235) B2377235
theorem B3010355 : Blo 1407523 3010355 := bstep (se 1 (by rfl) ⟨2257766, by rfl⟩ : syracuseStep 3010355 = 4515533) B4515533
theorem B4755293 : Blo 1407523 4755293 := bstep (se 3 (by rfl) ⟨891617, by rfl⟩ : syracuseStep 4755293 = 1783235) B1783235
theorem B1585003 : Blo 1407523 1585003 := bstep (se 1 (by rfl) ⟨1188752, by rfl⟩ : syracuseStep 1585003 = 2377505) B2377505
theorem B2256779 : Blo 1407523 2256779 := bstep (se 1 (by rfl) ⟨1692584, by rfl⟩ : syracuseStep 2256779 = 3385169) B3385169
theorem B1503127 : Blo 1407523 1503127 := bstep (se 1 (by rfl) ⟨1127345, by rfl⟩ : syracuseStep 1503127 = 2254691) B2254691
theorem B1585111 : Blo 1407523 1585111 := bstep (se 1 (by rfl) ⟨1188833, by rfl⟩ : syracuseStep 1585111 = 2377667) B2377667
theorem B4009945 : Blo 1407523 4009945 := bstep (se 2 (by rfl) ⟨1503729, by rfl⟩ : syracuseStep 4009945 = 3007459) B3007459
theorem B2674777 : Blo 1407523 2674777 := bstep (se 2 (by rfl) ⟨1003041, by rfl⟩ : syracuseStep 2674777 = 2006083) B2006083
theorem B1585291 : Blo 1407523 1585291 := bstep (se 1 (by rfl) ⟨1188968, by rfl⟩ : syracuseStep 1585291 = 2377937) B2377937
theorem B5345453 : Blo 1407523 5345453 := bstep (se 3 (by rfl) ⟨1002272, by rfl⟩ : syracuseStep 5345453 = 2004545) B2004545
theorem B1585399 : Blo 1407523 1585399 := bstep (se 1 (by rfl) ⟨1189049, by rfl⟩ : syracuseStep 1585399 = 2378099) B2378099
theorem B1782091 : Blo 1407523 1782091 := bstep (se 1 (by rfl) ⟨1336568, by rfl⟩ : syracuseStep 1782091 = 2673137) B2673137
theorem B1585579 : Blo 1407523 1585579 := bstep (se 1 (by rfl) ⟨1189184, by rfl⟩ : syracuseStep 1585579 = 2378369) B2378369
theorem B13717937 : Blo 1407523 13717937 := bstep (se 2 (by rfl) ⟨5144226, by rfl⟩ : syracuseStep 13717937 = 10288453) B10288453
theorem B8565209 : Blo 1407523 8565209 := bstep (se 2 (by rfl) ⟨3211953, by rfl⟩ : syracuseStep 8565209 = 6423907) B6423907
theorem B1585687 : Blo 1407523 1585687 := bstep (se 1 (by rfl) ⟨1189265, by rfl⟩ : syracuseStep 1585687 = 2378531) B2378531
theorem B1409335 : Blo 1407523 1409335 := bstep (se 1 (by rfl) ⟨1057001, by rfl⟩ : syracuseStep 1409335 = 2114003) B2114003
theorem B5075549 : Blo 1407523 5075549 := bstep (se 3 (by rfl) ⟨951665, by rfl⟩ : syracuseStep 5075549 = 1903331) B1903331
theorem B2675339 : Blo 1407523 2675339 := bstep (se 1 (by rfl) ⟨2006504, by rfl⟩ : syracuseStep 2675339 = 4013009) B4013009
theorem B1692311 : Blo 1407523 1692311 := bstep (se 1 (by rfl) ⟨1269233, by rfl⟩ : syracuseStep 1692311 = 2538467) B2538467
theorem B2257561 : Blo 1407523 2257561 := bstep (se 2 (by rfl) ⟨846585, by rfl⟩ : syracuseStep 2257561 = 1693171) B1693171
theorem B3166937 : Blo 1407523 3166937 := bstep (se 2 (by rfl) ⟨1187601, by rfl⟩ : syracuseStep 3166937 = 2375203) B2375203
theorem B1692427 : Blo 1407523 1692427 := bstep (se 1 (by rfl) ⟨1269320, by rfl⟩ : syracuseStep 1692427 = 2538641) B2538641
theorem B3167027 : Blo 1407523 3167027 := bstep (se 1 (by rfl) ⟨2375270, by rfl⟩ : syracuseStep 3167027 = 4750541) B4750541
theorem B2675521 : Blo 1407523 2675521 := bstep (se 2 (by rfl) ⟨1003320, by rfl⟩ : syracuseStep 2675521 = 2006641) B2006641
theorem B3167063 : Blo 1407523 3167063 := bstep (se 1 (by rfl) ⟨2375297, by rfl⟩ : syracuseStep 3167063 = 4750595) B4750595
theorem B5419865 : Blo 1407523 5419865 := bstep (se 2 (by rfl) ⟨2032449, by rfl⟩ : syracuseStep 5419865 = 4064899) B4064899
theorem B21672805 : Blo 1407523 21672805 := bstep (se 4 (by rfl) ⟨2031825, by rfl⟩ : syracuseStep 21672805 = 4063651) B4063651
theorem B2143127 : Blo 1407523 2143127 := bstep (se 1 (by rfl) ⟨1607345, by rfl⟩ : syracuseStep 2143127 = 3214691) B3214691
theorem B4756427 : Blo 1407523 4756427 := bstep (se 1 (by rfl) ⟨3567320, by rfl⟩ : syracuseStep 4756427 = 7134641) B7134641
theorem B3167243 : Blo 1407523 3167243 := bstep (se 1 (by rfl) ⟨2375432, by rfl⟩ : syracuseStep 3167243 = 4750865) B4750865
theorem B66819107 : Blo 1407523 66819107 := bstep (se 1 (by rfl) ⟨50114330, by rfl⟩ : syracuseStep 66819107 = 100228661) B100228661
theorem B3167297 : Blo 1407523 3167297 := bstep (se 2 (by rfl) ⟨1187736, by rfl⟩ : syracuseStep 3167297 = 2375473) B2375473
theorem B4281437 : Blo 1407523 4281437 := bstep (se 3 (by rfl) ⟨802769, by rfl⟩ : syracuseStep 4281437 = 1605539) B1605539
theorem B12039299 : Blo 1407523 12039299 := bstep (se 1 (by rfl) ⟨9029474, by rfl⟩ : syracuseStep 12039299 = 18058949) B18058949
theorem B4756697 : Blo 1407523 4756697 := bstep (se 2 (by rfl) ⟨1783761, by rfl⟩ : syracuseStep 4756697 = 3567523) B3567523
theorem B2536715 : Blo 1407523 2536715 := bstep (se 1 (by rfl) ⟨1902536, by rfl⟩ : syracuseStep 2536715 = 3805073) B3805073
theorem B4281623 : Blo 1407523 4281623 := bstep (se 1 (by rfl) ⟨3211217, by rfl⟩ : syracuseStep 4281623 = 6422435) B6422435
theorem B1783063 : Blo 1407523 1783063 := bstep (se 1 (by rfl) ⟨1337297, by rfl⟩ : syracuseStep 1783063 = 2674595) B2674595
theorem B3167513 : Blo 1407523 3167513 := bstep (se 2 (by rfl) ⟨1187817, by rfl⟩ : syracuseStep 3167513 = 2375635) B2375635
theorem B3167603 : Blo 1407523 3167603 := bstep (se 1 (by rfl) ⟨2375702, by rfl⟩ : syracuseStep 3167603 = 4751405) B4751405
theorem B3167639 : Blo 1407523 3167639 := bstep (se 1 (by rfl) ⟨2375729, by rfl⟩ : syracuseStep 3167639 = 4751459) B4751459
theorem B1504823 : Blo 1407523 1504823 := bstep (se 1 (by rfl) ⟨1128617, by rfl⟩ : syracuseStep 1504823 = 2257235) B2257235
theorem B5346881 : Blo 1407523 5346881 := bstep (se 2 (by rfl) ⟨2005080, by rfl⟩ : syracuseStep 5346881 = 4010161) B4010161
theorem B3167819 : Blo 1407523 3167819 := bstep (se 1 (by rfl) ⟨2375864, by rfl⟩ : syracuseStep 3167819 = 4751729) B4751729
theorem B7222877 : Blo 1407523 7222877 := bstep (se 3 (by rfl) ⟨1354289, by rfl⟩ : syracuseStep 7222877 = 2708579) B2708579
theorem B8566373 : Blo 1407523 8566373 := bstep (se 4 (by rfl) ⟨803097, by rfl⟩ : syracuseStep 8566373 = 1606195) B1606195
theorem B3167873 : Blo 1407523 3167873 := bstep (se 2 (by rfl) ⟨1187952, by rfl⟩ : syracuseStep 3167873 = 2375905) B2375905
theorem B5707543 : Blo 1407523 5707543 := bstep (se 1 (by rfl) ⟨4280657, by rfl⟩ : syracuseStep 5707543 = 8561315) B8561315
theorem B2111321 : Blo 1407523 2111321 := bstep (se 2 (by rfl) ⟨791745, by rfl⟩ : syracuseStep 2111321 = 1583491) B1583491
theorem B3168089 : Blo 1407523 3168089 := bstep (se 2 (by rfl) ⟨1188033, by rfl⟩ : syracuseStep 3168089 = 2376067) B2376067
theorem B6764381 : Blo 1407523 6764381 := bstep (se 3 (by rfl) ⟨1268321, by rfl⟩ : syracuseStep 6764381 = 2536643) B2536643
theorem B4011869 : Blo 1407523 4011869 := bstep (se 3 (by rfl) ⟨752225, by rfl⟩ : syracuseStep 4011869 = 1504451) B1504451
theorem B7133021 : Blo 1407523 7133021 := bstep (se 3 (by rfl) ⟨1337441, by rfl⟩ : syracuseStep 7133021 = 2674883) B2674883
theorem B10844005 : Blo 1407523 10844005 := bstep (se 4 (by rfl) ⟨1016625, by rfl⟩ : syracuseStep 10844005 = 2033251) B2033251
theorem B3168179 : Blo 1407523 3168179 := bstep (se 1 (by rfl) ⟨2376134, by rfl⟩ : syracuseStep 3168179 = 4752269) B4752269
theorem B2111435 : Blo 1407523 2111435 := bstep (se 1 (by rfl) ⟨1583576, by rfl⟩ : syracuseStep 2111435 = 3167153) B3167153
theorem B6019019 : Blo 1407523 6019019 := bstep (se 1 (by rfl) ⟨4514264, by rfl⟩ : syracuseStep 6019019 = 9028529) B9028529
theorem B2111447 : Blo 1407523 2111447 := bstep (se 1 (by rfl) ⟨1583585, by rfl⟩ : syracuseStep 2111447 = 3167171) B3167171
theorem B3168215 : Blo 1407523 3168215 := bstep (se 1 (by rfl) ⟨2376161, by rfl⟩ : syracuseStep 3168215 = 4752323) B4752323
theorem B2111513 : Blo 1407523 2111513 := bstep (se 2 (by rfl) ⟨791817, by rfl⟩ : syracuseStep 2111513 = 1583635) B1583635
theorem B1783883 : Blo 1407523 1783883 := bstep (se 1 (by rfl) ⟨1337912, by rfl⟩ : syracuseStep 1783883 = 2675825) B2675825
theorem B2111627 : Blo 1407523 2111627 := bstep (se 1 (by rfl) ⟨1583720, by rfl⟩ : syracuseStep 2111627 = 3167441) B3167441
theorem B3168395 : Blo 1407523 3168395 := bstep (se 1 (by rfl) ⟨2376296, by rfl⟩ : syracuseStep 3168395 = 4752593) B4752593
theorem B2111639 : Blo 1407523 2111639 := bstep (se 1 (by rfl) ⟨1583729, by rfl⟩ : syracuseStep 2111639 = 3167459) B3167459
theorem B3168449 : Blo 1407523 3168449 := bstep (se 2 (by rfl) ⟨1188168, by rfl⟩ : syracuseStep 3168449 = 2376337) B2376337
theorem B2111705 : Blo 1407523 2111705 := bstep (se 2 (by rfl) ⟨791889, by rfl⟩ : syracuseStep 2111705 = 1583779) B1583779
theorem B18061613 : Blo 1407523 18061613 := bstep (se 3 (by rfl) ⟨3386552, by rfl⟩ : syracuseStep 18061613 = 6773105) B6773105
theorem B17365313 : Blo 1407523 17365313 := bstep (se 2 (by rfl) ⟨6511992, by rfl⟩ : syracuseStep 17365313 = 13023985) B13023985
theorem B2111819 : Blo 1407523 2111819 := bstep (se 1 (by rfl) ⟨1583864, by rfl⟩ : syracuseStep 2111819 = 3167729) B3167729
theorem B2111831 : Blo 1407523 2111831 := bstep (se 1 (by rfl) ⟨1583873, by rfl⟩ : syracuseStep 2111831 = 3167747) B3167747
theorem B2005337 : Blo 1407523 2005337 := bstep (se 2 (by rfl) ⟨752001, by rfl⟩ : syracuseStep 2005337 = 1504003) B1504003
theorem B2111897 : Blo 1407523 2111897 := bstep (se 2 (by rfl) ⟨791961, by rfl⟩ : syracuseStep 2111897 = 1583923) B1583923
theorem B3168665 : Blo 1407523 3168665 := bstep (se 2 (by rfl) ⟨1188249, by rfl⟩ : syracuseStep 3168665 = 2376499) B2376499
theorem B5708225 : Blo 1407523 5708225 := bstep (se 2 (by rfl) ⟨2140584, by rfl⟩ : syracuseStep 5708225 = 4281169) B4281169
theorem B3168755 : Blo 1407523 3168755 := bstep (se 1 (by rfl) ⟨2376566, by rfl⟩ : syracuseStep 3168755 = 4753133) B4753133
theorem B2112011 : Blo 1407523 2112011 := bstep (se 1 (by rfl) ⟨1584008, by rfl⟩ : syracuseStep 2112011 = 3168017) B3168017
theorem B65067533 : Blo 1407523 65067533 := bstep (se 3 (by rfl) ⟨12200162, by rfl⟩ : syracuseStep 65067533 = 24400325) B24400325
theorem B2112023 : Blo 1407523 2112023 := bstep (se 1 (by rfl) ⟨1584017, by rfl⟩ : syracuseStep 2112023 = 3168035) B3168035
theorem B3168791 : Blo 1407523 3168791 := bstep (se 1 (by rfl) ⟨2376593, by rfl⟩ : syracuseStep 3168791 = 4753187) B4753187
theorem B1407531 : Blo 1407523 1407531 := bstep (se 1 (by rfl) ⟨1055648, by rfl⟩ : syracuseStep 1407531 = 2111297) B2111297
theorem B1407543 : Blo 1407523 1407543 := bstep (se 1 (by rfl) ⟨1055657, by rfl⟩ : syracuseStep 1407543 = 2111315) B2111315
theorem B1407563 : Blo 1407523 1407563 := bstep (se 1 (by rfl) ⟨1055672, by rfl⟩ : syracuseStep 1407563 = 2111345) B2111345
theorem B1407575 : Blo 1407523 1407575 := bstep (se 1 (by rfl) ⟨1055681, by rfl⟩ : syracuseStep 1407575 = 2111363) B2111363
theorem B2112089 : Blo 1407523 2112089 := bstep (se 2 (by rfl) ⟨792033, by rfl⟩ : syracuseStep 2112089 = 1584067) B1584067
theorem B1407595 : Blo 1407523 1407595 := bstep (se 1 (by rfl) ⟨1055696, by rfl⟩ : syracuseStep 1407595 = 2111393) B2111393
theorem B1407607 : Blo 1407523 1407607 := bstep (se 1 (by rfl) ⟨1055705, by rfl⟩ : syracuseStep 1407607 = 2111411) B2111411
theorem B1407627 : Blo 1407523 1407627 := bstep (se 1 (by rfl) ⟨1055720, by rfl⟩ : syracuseStep 1407627 = 2111441) B2111441
theorem B1407639 : Blo 1407523 1407639 := bstep (se 1 (by rfl) ⟨1055729, by rfl⟩ : syracuseStep 1407639 = 2111459) B2111459
theorem B1407659 : Blo 1407523 1407659 := bstep (se 1 (by rfl) ⟨1055744, by rfl⟩ : syracuseStep 1407659 = 2111489) B2111489
theorem B1407671 : Blo 1407523 1407671 := bstep (se 1 (by rfl) ⟨1055753, by rfl⟩ : syracuseStep 1407671 = 2111507) B2111507
theorem B1407691 : Blo 1407523 1407691 := bstep (se 1 (by rfl) ⟨1055768, by rfl⟩ : syracuseStep 1407691 = 2111537) B2111537
theorem B2112203 : Blo 1407523 2112203 := bstep (se 1 (by rfl) ⟨1584152, by rfl⟩ : syracuseStep 2112203 = 3168305) B3168305
theorem B3168971 : Blo 1407523 3168971 := bstep (se 1 (by rfl) ⟨2376728, by rfl⟩ : syracuseStep 3168971 = 4753457) B4753457
theorem B1407703 : Blo 1407523 1407703 := bstep (se 1 (by rfl) ⟨1055777, by rfl⟩ : syracuseStep 1407703 = 2111555) B2111555
theorem B2112215 : Blo 1407523 2112215 := bstep (se 1 (by rfl) ⟨1584161, by rfl⟩ : syracuseStep 2112215 = 3168323) B3168323
theorem B1407723 : Blo 1407523 1407723 := bstep (se 1 (by rfl) ⟨1055792, by rfl⟩ : syracuseStep 1407723 = 2111585) B2111585
theorem B40614641 : Blo 1407523 40614641 := bstep (se 2 (by rfl) ⟨15230490, by rfl⟩ : syracuseStep 40614641 = 30460981) B30460981
theorem B1407735 : Blo 1407523 1407735 := bstep (se 1 (by rfl) ⟨1055801, by rfl⟩ : syracuseStep 1407735 = 2111603) B2111603
theorem B3169025 : Blo 1407523 3169025 := bstep (se 2 (by rfl) ⟨1188384, by rfl⟩ : syracuseStep 3169025 = 2376769) B2376769
theorem B1407755 : Blo 1407523 1407755 := bstep (se 1 (by rfl) ⟨1055816, by rfl⟩ : syracuseStep 1407755 = 2111633) B2111633
theorem B6421265 : Blo 1407523 6421265 := bstep (se 2 (by rfl) ⟨2407974, by rfl⟩ : syracuseStep 6421265 = 4815949) B4815949
theorem B1407767 : Blo 1407523 1407767 := bstep (se 1 (by rfl) ⟨1055825, by rfl⟩ : syracuseStep 1407767 = 2111651) B2111651
theorem B2112281 : Blo 1407523 2112281 := bstep (se 2 (by rfl) ⟨792105, by rfl⟩ : syracuseStep 2112281 = 1584211) B1584211
theorem B1407787 : Blo 1407523 1407787 := bstep (se 1 (by rfl) ⟨1055840, by rfl⟩ : syracuseStep 1407787 = 2111681) B2111681
theorem B1407799 : Blo 1407523 1407799 := bstep (se 1 (by rfl) ⟨1055849, by rfl⟩ : syracuseStep 1407799 = 2111699) B2111699
theorem B1407819 : Blo 1407523 1407819 := bstep (se 1 (by rfl) ⟨1055864, by rfl⟩ : syracuseStep 1407819 = 2111729) B2111729
theorem B1407831 : Blo 1407523 1407831 := bstep (se 1 (by rfl) ⟨1055873, by rfl⟩ : syracuseStep 1407831 = 2111747) B2111747
theorem B1407851 : Blo 1407523 1407851 := bstep (se 1 (by rfl) ⟨1055888, by rfl⟩ : syracuseStep 1407851 = 2111777) B2111777
theorem B1407863 : Blo 1407523 1407863 := bstep (se 1 (by rfl) ⟨1055897, by rfl⟩ : syracuseStep 1407863 = 2111795) B2111795
theorem B1407883 : Blo 1407523 1407883 := bstep (se 1 (by rfl) ⟨1055912, by rfl⟩ : syracuseStep 1407883 = 2111825) B2111825
theorem B2112395 : Blo 1407523 2112395 := bstep (se 1 (by rfl) ⟨1584296, by rfl⟩ : syracuseStep 2112395 = 3168593) B3168593
theorem B1407895 : Blo 1407523 1407895 := bstep (se 1 (by rfl) ⟨1055921, by rfl⟩ : syracuseStep 1407895 = 2111843) B2111843
theorem B2112407 : Blo 1407523 2112407 := bstep (se 1 (by rfl) ⟨1584305, by rfl⟩ : syracuseStep 2112407 = 3168611) B3168611
theorem B6019991 : Blo 1407523 6019991 := bstep (se 1 (by rfl) ⟨4514993, by rfl⟩ : syracuseStep 6019991 = 9029987) B9029987
theorem B1407915 : Blo 1407523 1407915 := bstep (se 1 (by rfl) ⟨1055936, by rfl⟩ : syracuseStep 1407915 = 2111873) B2111873
theorem B6421427 : Blo 1407523 6421427 := bstep (se 1 (by rfl) ⟨4816070, by rfl⟩ : syracuseStep 6421427 = 9632141) B9632141
theorem B1407927 : Blo 1407523 1407927 := bstep (se 1 (by rfl) ⟨1055945, by rfl⟩ : syracuseStep 1407927 = 2111891) B2111891
theorem B1407947 : Blo 1407523 1407947 := bstep (se 1 (by rfl) ⟨1055960, by rfl⟩ : syracuseStep 1407947 = 2111921) B2111921
theorem B1407959 : Blo 1407523 1407959 := bstep (se 1 (by rfl) ⟨1055969, by rfl⟩ : syracuseStep 1407959 = 2111939) B2111939
theorem B2005975 : Blo 1407523 2005975 := bstep (se 1 (by rfl) ⟨1504481, by rfl⟩ : syracuseStep 2005975 = 3008963) B3008963
theorem B2112473 : Blo 1407523 2112473 := bstep (se 2 (by rfl) ⟨792177, by rfl⟩ : syracuseStep 2112473 = 1584355) B1584355
theorem B3169241 : Blo 1407523 3169241 := bstep (se 2 (by rfl) ⟨1188465, by rfl⟩ : syracuseStep 3169241 = 2376931) B2376931
theorem B1407979 : Blo 1407523 1407979 := bstep (se 1 (by rfl) ⟨1055984, by rfl⟩ : syracuseStep 1407979 = 2111969) B2111969
theorem B1407991 : Blo 1407523 1407991 := bstep (se 1 (by rfl) ⟨1055993, by rfl⟩ : syracuseStep 1407991 = 2111987) B2111987
theorem B2644993 : Blo 1407523 2644993 := bstep (se 2 (by rfl) ⟨991872, by rfl⟩ : syracuseStep 2644993 = 1983745) B1983745
theorem B1408011 : Blo 1407523 1408011 := bstep (se 1 (by rfl) ⟨1056008, by rfl⟩ : syracuseStep 1408011 = 2112017) B2112017
theorem B5348369 : Blo 1407523 5348369 := bstep (se 2 (by rfl) ⟨2005638, by rfl⟩ : syracuseStep 5348369 = 4011277) B4011277
theorem B1408023 : Blo 1407523 1408023 := bstep (se 1 (by rfl) ⟨1056017, by rfl⟩ : syracuseStep 1408023 = 2112035) B2112035
theorem B1408043 : Blo 1407523 1408043 := bstep (se 1 (by rfl) ⟨1056032, by rfl⟩ : syracuseStep 1408043 = 2112065) B2112065
theorem B3169331 : Blo 1407523 3169331 := bstep (se 1 (by rfl) ⟨2376998, by rfl⟩ : syracuseStep 3169331 = 4753997) B4753997
theorem B1408055 : Blo 1407523 1408055 := bstep (se 1 (by rfl) ⟨1056041, by rfl⟩ : syracuseStep 1408055 = 2112083) B2112083
theorem B8027201 : Blo 1407523 8027201 := bstep (se 2 (by rfl) ⟨3010200, by rfl⟩ : syracuseStep 8027201 = 6020401) B6020401
theorem B1408075 : Blo 1407523 1408075 := bstep (se 1 (by rfl) ⟨1056056, by rfl⟩ : syracuseStep 1408075 = 2112113) B2112113
theorem B2112587 : Blo 1407523 2112587 := bstep (se 1 (by rfl) ⟨1584440, by rfl⟩ : syracuseStep 2112587 = 3168881) B3168881
theorem B1408087 : Blo 1407523 1408087 := bstep (se 1 (by rfl) ⟨1056065, by rfl⟩ : syracuseStep 1408087 = 2112131) B2112131
theorem B2112599 : Blo 1407523 2112599 := bstep (se 1 (by rfl) ⟨1584449, by rfl⟩ : syracuseStep 2112599 = 3168899) B3168899
theorem B3169367 : Blo 1407523 3169367 := bstep (se 1 (by rfl) ⟨2377025, by rfl⟩ : syracuseStep 3169367 = 4754051) B4754051
theorem B1408107 : Blo 1407523 1408107 := bstep (se 1 (by rfl) ⟨1056080, by rfl⟩ : syracuseStep 1408107 = 2112161) B2112161
theorem B1408119 : Blo 1407523 1408119 := bstep (se 1 (by rfl) ⟨1056089, by rfl⟩ : syracuseStep 1408119 = 2112179) B2112179
theorem B1408139 : Blo 1407523 1408139 := bstep (se 1 (by rfl) ⟨1056104, by rfl⟩ : syracuseStep 1408139 = 2112209) B2112209
theorem B4750487 : Blo 1407523 4750487 := bstep (se 1 (by rfl) ⟨3562865, by rfl⟩ : syracuseStep 4750487 = 7125731) B7125731
theorem B1408151 : Blo 1407523 1408151 := bstep (se 1 (by rfl) ⟨1056113, by rfl⟩ : syracuseStep 1408151 = 2112227) B2112227
theorem B2112665 : Blo 1407523 2112665 := bstep (se 2 (by rfl) ⟨792249, by rfl⟩ : syracuseStep 2112665 = 1584499) B1584499
theorem B1408171 : Blo 1407523 1408171 := bstep (se 1 (by rfl) ⟨1056128, by rfl⟩ : syracuseStep 1408171 = 2112257) B2112257
theorem B1408183 : Blo 1407523 1408183 := bstep (se 1 (by rfl) ⟨1056137, by rfl⟩ : syracuseStep 1408183 = 2112275) B2112275
theorem B1408203 : Blo 1407523 1408203 := bstep (se 1 (by rfl) ⟨1056152, by rfl⟩ : syracuseStep 1408203 = 2112305) B2112305
theorem B1408215 : Blo 1407523 1408215 := bstep (se 1 (by rfl) ⟨1056161, by rfl⟩ : syracuseStep 1408215 = 2112323) B2112323
theorem B8019161 : Blo 1407523 8019161 := bstep (se 2 (by rfl) ⟨3007185, by rfl⟩ : syracuseStep 8019161 = 6014371) B6014371
theorem B1408235 : Blo 1407523 1408235 := bstep (se 1 (by rfl) ⟨1056176, by rfl⟩ : syracuseStep 1408235 = 2112353) B2112353
theorem B1408247 : Blo 1407523 1408247 := bstep (se 1 (by rfl) ⟨1056185, by rfl⟩ : syracuseStep 1408247 = 2112371) B2112371
theorem B1408267 : Blo 1407523 1408267 := bstep (se 1 (by rfl) ⟨1056200, by rfl⟩ : syracuseStep 1408267 = 2112401) B2112401
theorem B2112779 : Blo 1407523 2112779 := bstep (se 1 (by rfl) ⟨1584584, by rfl⟩ : syracuseStep 2112779 = 3169169) B3169169
theorem B3169547 : Blo 1407523 3169547 := bstep (se 1 (by rfl) ⟨2377160, by rfl⟩ : syracuseStep 3169547 = 4754321) B4754321
theorem B1408279 : Blo 1407523 1408279 := bstep (se 1 (by rfl) ⟨1056209, by rfl⟩ : syracuseStep 1408279 = 2112419) B2112419
theorem B2112791 : Blo 1407523 2112791 := bstep (se 1 (by rfl) ⟨1584593, by rfl⟩ : syracuseStep 2112791 = 3169187) B3169187
theorem B1408299 : Blo 1407523 1408299 := bstep (se 1 (by rfl) ⟨1056224, by rfl⟩ : syracuseStep 1408299 = 2112449) B2112449
theorem B5078317 : Blo 1407523 5078317 := bstep (se 3 (by rfl) ⟨952184, by rfl⟩ : syracuseStep 5078317 = 1904369) B1904369
theorem B1408311 : Blo 1407523 1408311 := bstep (se 1 (by rfl) ⟨1056233, by rfl⟩ : syracuseStep 1408311 = 2112467) B2112467
theorem B3169601 : Blo 1407523 3169601 := bstep (se 2 (by rfl) ⟨1188600, by rfl⟩ : syracuseStep 3169601 = 2377201) B2377201
theorem B1408331 : Blo 1407523 1408331 := bstep (se 1 (by rfl) ⟨1056248, by rfl⟩ : syracuseStep 1408331 = 2112497) B2112497
theorem B1408343 : Blo 1407523 1408343 := bstep (se 1 (by rfl) ⟨1056257, by rfl⟩ : syracuseStep 1408343 = 2112515) B2112515
theorem B2112857 : Blo 1407523 2112857 := bstep (se 2 (by rfl) ⟨792321, by rfl⟩ : syracuseStep 2112857 = 1584643) B1584643
theorem B1408363 : Blo 1407523 1408363 := bstep (se 1 (by rfl) ⟨1056272, by rfl⟩ : syracuseStep 1408363 = 2112545) B2112545
theorem B1408375 : Blo 1407523 1408375 := bstep (se 1 (by rfl) ⟨1056281, by rfl⟩ : syracuseStep 1408375 = 2112563) B2112563
theorem B12025219 : Blo 1407523 12025219 := bstep (se 1 (by rfl) ⟨9018914, by rfl⟩ : syracuseStep 12025219 = 18037829) B18037829
theorem B1408395 : Blo 1407523 1408395 := bstep (se 1 (by rfl) ⟨1056296, by rfl⟩ : syracuseStep 1408395 = 2112593) B2112593
theorem B1408407 : Blo 1407523 1408407 := bstep (se 1 (by rfl) ⟨1056305, by rfl⟩ : syracuseStep 1408407 = 2112611) B2112611
theorem B1408427 : Blo 1407523 1408427 := bstep (se 1 (by rfl) ⟨1056320, by rfl⟩ : syracuseStep 1408427 = 2112641) B2112641
theorem B1408439 : Blo 1407523 1408439 := bstep (se 1 (by rfl) ⟨1056329, by rfl⟩ : syracuseStep 1408439 = 2112659) B2112659
theorem B1408459 : Blo 1407523 1408459 := bstep (se 1 (by rfl) ⟨1056344, by rfl⟩ : syracuseStep 1408459 = 2112689) B2112689
theorem B2112971 : Blo 1407523 2112971 := bstep (se 1 (by rfl) ⟨1584728, by rfl⟩ : syracuseStep 2112971 = 3169457) B3169457
theorem B1408471 : Blo 1407523 1408471 := bstep (se 1 (by rfl) ⟨1056353, by rfl⟩ : syracuseStep 1408471 = 2112707) B2112707
theorem B2112983 : Blo 1407523 2112983 := bstep (se 1 (by rfl) ⟨1584737, by rfl⟩ : syracuseStep 2112983 = 3169475) B3169475
theorem B5348825 : Blo 1407523 5348825 := bstep (se 2 (by rfl) ⟨2005809, by rfl⟩ : syracuseStep 5348825 = 4011619) B4011619
theorem B1408491 : Blo 1407523 1408491 := bstep (se 1 (by rfl) ⟨1056368, by rfl⟩ : syracuseStep 1408491 = 2112737) B2112737
theorem B1408503 : Blo 1407523 1408503 := bstep (se 1 (by rfl) ⟨1056377, by rfl⟩ : syracuseStep 1408503 = 2112755) B2112755
theorem B1408523 : Blo 1407523 1408523 := bstep (se 1 (by rfl) ⟨1056392, by rfl⟩ : syracuseStep 1408523 = 2112785) B2112785
theorem B1408535 : Blo 1407523 1408535 := bstep (se 1 (by rfl) ⟨1056401, by rfl⟩ : syracuseStep 1408535 = 2112803) B2112803
theorem B6184471 : Blo 1407523 6184471 := bstep (se 1 (by rfl) ⟨4638353, by rfl⟩ : syracuseStep 6184471 = 9276707) B9276707
theorem B2113049 : Blo 1407523 2113049 := bstep (se 2 (by rfl) ⟨792393, by rfl⟩ : syracuseStep 2113049 = 1584787) B1584787
theorem B3169817 : Blo 1407523 3169817 := bstep (se 2 (by rfl) ⟨1188681, by rfl⟩ : syracuseStep 3169817 = 2377363) B2377363
theorem B1408555 : Blo 1407523 1408555 := bstep (se 1 (by rfl) ⟨1056416, by rfl⟩ : syracuseStep 1408555 = 2112833) B2112833
theorem B1408567 : Blo 1407523 1408567 := bstep (se 1 (by rfl) ⟨1056425, by rfl⟩ : syracuseStep 1408567 = 2112851) B2112851
theorem B1408587 : Blo 1407523 1408587 := bstep (se 1 (by rfl) ⟨1056440, by rfl⟩ : syracuseStep 1408587 = 2112881) B2112881
theorem B1408599 : Blo 1407523 1408599 := bstep (se 1 (by rfl) ⟨1056449, by rfl⟩ : syracuseStep 1408599 = 2112899) B2112899
theorem B2375257 : Blo 1407523 2375257 := bstep (se 2 (by rfl) ⟨890721, by rfl⟩ : syracuseStep 2375257 = 1781443) B1781443
theorem B2440793 : Blo 1407523 2440793 := bstep (se 2 (by rfl) ⟨915297, by rfl⟩ : syracuseStep 2440793 = 1830595) B1830595
theorem B1408619 : Blo 1407523 1408619 := bstep (se 1 (by rfl) ⟨1056464, by rfl⟩ : syracuseStep 1408619 = 2112929) B2112929
theorem B3169907 : Blo 1407523 3169907 := bstep (se 1 (by rfl) ⟨2377430, by rfl⟩ : syracuseStep 3169907 = 4754861) B4754861
theorem B1408631 : Blo 1407523 1408631 := bstep (se 1 (by rfl) ⟨1056473, by rfl⟩ : syracuseStep 1408631 = 2112947) B2112947
theorem B1408651 : Blo 1407523 1408651 := bstep (se 1 (by rfl) ⟨1056488, by rfl⟩ : syracuseStep 1408651 = 2112977) B2112977
theorem B2113163 : Blo 1407523 2113163 := bstep (se 1 (by rfl) ⟨1584872, by rfl⟩ : syracuseStep 2113163 = 3169745) B3169745
theorem B8240791 : Blo 1407523 8240791 := bstep (se 1 (by rfl) ⟨6180593, by rfl⟩ : syracuseStep 8240791 = 12361187) B12361187
theorem B1408663 : Blo 1407523 1408663 := bstep (se 1 (by rfl) ⟨1056497, by rfl⟩ : syracuseStep 1408663 = 2112995) B2112995
theorem B2113175 : Blo 1407523 2113175 := bstep (se 1 (by rfl) ⟨1584881, by rfl⟩ : syracuseStep 2113175 = 3169763) B3169763
theorem B3169943 : Blo 1407523 3169943 := bstep (se 1 (by rfl) ⟨2377457, by rfl⟩ : syracuseStep 3169943 = 4754915) B4754915
theorem B1408683 : Blo 1407523 1408683 := bstep (se 1 (by rfl) ⟨1056512, by rfl⟩ : syracuseStep 1408683 = 2113025) B2113025
theorem B5349037 : Blo 1407523 5349037 := bstep (se 3 (by rfl) ⟨1002944, by rfl⟩ : syracuseStep 5349037 = 2005889) B2005889
theorem B4751027 : Blo 1407523 4751027 := bstep (se 1 (by rfl) ⟨3563270, by rfl⟩ : syracuseStep 4751027 = 7126541) B7126541
theorem B3210931 : Blo 1407523 3210931 := bstep (se 1 (by rfl) ⟨2408198, by rfl⟩ : syracuseStep 3210931 = 4816397) B4816397
theorem B1408695 : Blo 1407523 1408695 := bstep (se 1 (by rfl) ⟨1056521, by rfl⟩ : syracuseStep 1408695 = 2113043) B2113043
theorem B1408715 : Blo 1407523 1408715 := bstep (se 1 (by rfl) ⟨1056536, by rfl⟩ : syracuseStep 1408715 = 2113073) B2113073
theorem B1408727 : Blo 1407523 1408727 := bstep (se 1 (by rfl) ⟨1056545, by rfl⟩ : syracuseStep 1408727 = 2113091) B2113091
theorem B9019097 : Blo 1407523 9019097 := bstep (se 2 (by rfl) ⟨3382161, by rfl⟩ : syracuseStep 9019097 = 6764323) B6764323
theorem B2113241 : Blo 1407523 2113241 := bstep (se 2 (by rfl) ⟨792465, by rfl⟩ : syracuseStep 2113241 = 1584931) B1584931
theorem B1408747 : Blo 1407523 1408747 := bstep (se 1 (by rfl) ⟨1056560, by rfl⟩ : syracuseStep 1408747 = 2113121) B2113121
theorem B1408759 : Blo 1407523 1408759 := bstep (se 1 (by rfl) ⟨1056569, by rfl⟩ : syracuseStep 1408759 = 2113139) B2113139
theorem B1408779 : Blo 1407523 1408779 := bstep (se 1 (by rfl) ⟨1056584, by rfl⟩ : syracuseStep 1408779 = 2113169) B2113169
theorem B2006795 : Blo 1407523 2006795 := bstep (se 1 (by rfl) ⟨1505096, by rfl⟩ : syracuseStep 2006795 = 3010193) B3010193
theorem B1408791 : Blo 1407523 1408791 := bstep (se 1 (by rfl) ⟨1056593, by rfl⟩ : syracuseStep 1408791 = 2113187) B2113187
theorem B1408811 : Blo 1407523 1408811 := bstep (se 1 (by rfl) ⟨1056608, by rfl⟩ : syracuseStep 1408811 = 2113217) B2113217
theorem B5709619 : Blo 1407523 5709619 := bstep (se 1 (by rfl) ⟨4282214, by rfl⟩ : syracuseStep 5709619 = 8564429) B8564429
theorem B1408823 : Blo 1407523 1408823 := bstep (se 1 (by rfl) ⟨1056617, by rfl⟩ : syracuseStep 1408823 = 2113235) B2113235
theorem B4063051 : Blo 1407523 4063051 := bstep (se 1 (by rfl) ⟨3047288, by rfl⟩ : syracuseStep 4063051 = 6094577) B6094577
theorem B1408843 : Blo 1407523 1408843 := bstep (se 1 (by rfl) ⟨1056632, by rfl⟩ : syracuseStep 1408843 = 2113265) B2113265
theorem B2113355 : Blo 1407523 2113355 := bstep (se 1 (by rfl) ⟨1585016, by rfl⟩ : syracuseStep 2113355 = 3170033) B3170033
theorem B3170123 : Blo 1407523 3170123 := bstep (se 1 (by rfl) ⟨2377592, by rfl⟩ : syracuseStep 3170123 = 4755185) B4755185
theorem B1408855 : Blo 1407523 1408855 := bstep (se 1 (by rfl) ⟨1056641, by rfl⟩ : syracuseStep 1408855 = 2113283) B2113283
theorem B2113367 : Blo 1407523 2113367 := bstep (se 1 (by rfl) ⟨1585025, by rfl⟩ : syracuseStep 2113367 = 3170051) B3170051
theorem B1408875 : Blo 1407523 1408875 := bstep (se 1 (by rfl) ⟨1056656, by rfl⟩ : syracuseStep 1408875 = 2113313) B2113313
theorem B1408887 : Blo 1407523 1408887 := bstep (se 1 (by rfl) ⟨1056665, by rfl⟩ : syracuseStep 1408887 = 2113331) B2113331
theorem B2711411 : Blo 1407523 2711411 := bstep (se 1 (by rfl) ⟨2033558, by rfl⟩ : syracuseStep 2711411 = 4067117) B4067117
theorem B3170177 : Blo 1407523 3170177 := bstep (se 2 (by rfl) ⟨1188816, by rfl⟩ : syracuseStep 3170177 = 2377633) B2377633
theorem B1408907 : Blo 1407523 1408907 := bstep (se 1 (by rfl) ⟨1056680, by rfl⟩ : syracuseStep 1408907 = 2113361) B2113361
theorem B1408919 : Blo 1407523 1408919 := bstep (se 1 (by rfl) ⟨1056689, by rfl⟩ : syracuseStep 1408919 = 2113379) B2113379
theorem B7135127 : Blo 1407523 7135127 := bstep (se 1 (by rfl) ⟨5351345, by rfl⟩ : syracuseStep 7135127 = 10702691) B10702691
theorem B2113433 : Blo 1407523 2113433 := bstep (se 2 (by rfl) ⟨792537, by rfl⟩ : syracuseStep 2113433 = 1585075) B1585075
theorem B1408939 : Blo 1407523 1408939 := bstep (se 1 (by rfl) ⟨1056704, by rfl⟩ : syracuseStep 1408939 = 2113409) B2113409
theorem B1408951 : Blo 1407523 1408951 := bstep (se 1 (by rfl) ⟨1056713, by rfl⟩ : syracuseStep 1408951 = 2113427) B2113427
theorem B4751297 : Blo 1407523 4751297 := bstep (se 2 (by rfl) ⟨1781736, by rfl⟩ : syracuseStep 4751297 = 3563473) B3563473
theorem B1408971 : Blo 1407523 1408971 := bstep (se 1 (by rfl) ⟨1056728, by rfl⟩ : syracuseStep 1408971 = 2113457) B2113457
theorem B1408983 : Blo 1407523 1408983 := bstep (se 1 (by rfl) ⟨1056737, by rfl⟩ : syracuseStep 1408983 = 2113475) B2113475
theorem B5349341 : Blo 1407523 5349341 := bstep (se 3 (by rfl) ⟨1003001, by rfl⟩ : syracuseStep 5349341 = 2006003) B2006003
theorem B1409003 : Blo 1407523 1409003 := bstep (se 1 (by rfl) ⟨1056752, by rfl⟩ : syracuseStep 1409003 = 2113505) B2113505
theorem B14106629 : Blo 1407523 14106629 := bstep (se 4 (by rfl) ⟨1322496, by rfl⟩ : syracuseStep 14106629 = 2644993) B2644993
theorem B1409031 : Blo 1407523 1409031 := bstep (se 1 (by rfl) ⟨1056773, by rfl⟩ : syracuseStep 1409031 = 2113547) B2113547
theorem B1409039 : Blo 1407523 1409039 := bstep (se 1 (by rfl) ⟨1056779, by rfl⟩ : syracuseStep 1409039 = 2113559) B2113559
theorem B2375723 : Blo 1407523 2375723 := bstep (se 1 (by rfl) ⟨1781792, by rfl⟩ : syracuseStep 2375723 = 3563585) B3563585
theorem B2113595 : Blo 1407523 2113595 := bstep (se 1 (by rfl) ⟨1585196, by rfl⟩ : syracuseStep 2113595 = 3170393) B3170393
theorem B1409083 : Blo 1407523 1409083 := bstep (se 1 (by rfl) ⟨1056812, by rfl⟩ : syracuseStep 1409083 = 2113625) B2113625
theorem B3563635 : Blo 1407523 3563635 := bstep (se 1 (by rfl) ⟨2672726, by rfl⟩ : syracuseStep 3563635 = 5345453) B5345453
theorem B2113655 : Blo 1407523 2113655 := bstep (se 1 (by rfl) ⟨1585241, by rfl⟩ : syracuseStep 2113655 = 3170483) B3170483
theorem B1409159 : Blo 1407523 1409159 := bstep (se 1 (by rfl) ⟨1056869, by rfl⟩ : syracuseStep 1409159 = 2113739) B2113739
theorem B2113679 : Blo 1407523 2113679 := bstep (se 1 (by rfl) ⟨1585259, by rfl⟩ : syracuseStep 2113679 = 3170519) B3170519
theorem B1409167 : Blo 1407523 1409167 := bstep (se 1 (by rfl) ⟨1056875, by rfl⟩ : syracuseStep 1409167 = 2113751) B2113751
theorem B2113721 : Blo 1407523 2113721 := bstep (se 2 (by rfl) ⟨792645, by rfl⟩ : syracuseStep 2113721 = 1585291) B1585291
theorem B1409211 : Blo 1407523 1409211 := bstep (se 1 (by rfl) ⟨1056908, by rfl⟩ : syracuseStep 1409211 = 2113817) B2113817
theorem B3563777 : Blo 1407523 3563777 := bstep (se 2 (by rfl) ⟨1336416, by rfl⟩ : syracuseStep 3563777 = 2672833) B2672833
theorem B2113799 : Blo 1407523 2113799 := bstep (se 1 (by rfl) ⟨1585349, by rfl⟩ : syracuseStep 2113799 = 3170699) B3170699
theorem B1409287 : Blo 1407523 1409287 := bstep (se 1 (by rfl) ⟨1056965, by rfl⟩ : syracuseStep 1409287 = 2113931) B2113931
theorem B1409295 : Blo 1407523 1409295 := bstep (se 1 (by rfl) ⟨1056971, by rfl⟩ : syracuseStep 1409295 = 2113943) B2113943
theorem B2113835 : Blo 1407523 2113835 := bstep (se 1 (by rfl) ⟨1585376, by rfl⟩ : syracuseStep 2113835 = 3170753) B3170753
theorem B4063547 : Blo 1407523 4063547 := bstep (se 1 (by rfl) ⟨3047660, by rfl⟩ : syracuseStep 4063547 = 6095321) B6095321
theorem B4751675 : Blo 1407523 4751675 := bstep (se 1 (by rfl) ⟨3563756, by rfl⟩ : syracuseStep 4751675 = 7127513) B7127513
theorem B5710139 : Blo 1407523 5710139 := bstep (se 1 (by rfl) ⟨4282604, by rfl⟩ : syracuseStep 5710139 = 8565209) B8565209
theorem B1409339 : Blo 1407523 1409339 := bstep (se 1 (by rfl) ⟨1057004, by rfl⟩ : syracuseStep 1409339 = 2114009) B2114009
theorem B2113865 : Blo 1407523 2113865 := bstep (se 2 (by rfl) ⟨792699, by rfl⟩ : syracuseStep 2113865 = 1585399) B1585399
theorem B1409415 : Blo 1407523 1409415 := bstep (se 1 (by rfl) ⟨1057061, by rfl⟩ : syracuseStep 1409415 = 2114123) B2114123
theorem B1409423 : Blo 1407523 1409423 := bstep (se 1 (by rfl) ⟨1057067, by rfl⟩ : syracuseStep 1409423 = 2114135) B2114135
theorem B3383699 : Blo 1407523 3383699 := bstep (se 1 (by rfl) ⟨2537774, by rfl⟩ : syracuseStep 3383699 = 5075549) B5075549
theorem B4514201 : Blo 1407523 4514201 := bstep (se 2 (by rfl) ⟨1692825, by rfl⟩ : syracuseStep 4514201 = 3385651) B3385651
theorem B2376121 : Blo 1407523 2376121 := bstep (se 2 (by rfl) ⟨891045, by rfl⟩ : syracuseStep 2376121 = 1782091) B1782091
theorem B2113979 : Blo 1407523 2113979 := bstep (se 1 (by rfl) ⟨1585484, by rfl⟩ : syracuseStep 2113979 = 3170969) B3170969
theorem B1409467 : Blo 1407523 1409467 := bstep (se 1 (by rfl) ⟨1057100, by rfl⟩ : syracuseStep 1409467 = 2114201) B2114201
theorem B2114039 : Blo 1407523 2114039 := bstep (se 1 (by rfl) ⟨1585529, by rfl⟩ : syracuseStep 2114039 = 3171059) B3171059
theorem B2114063 : Blo 1407523 2114063 := bstep (se 1 (by rfl) ⟨1585547, by rfl⟩ : syracuseStep 2114063 = 3171095) B3171095
theorem B2114105 : Blo 1407523 2114105 := bstep (se 2 (by rfl) ⟨792789, by rfl⟩ : syracuseStep 2114105 = 1585579) B1585579
theorem B3613243 : Blo 1407523 3613243 := bstep (se 1 (by rfl) ⟨2709932, by rfl⟩ : syracuseStep 3613243 = 5419865) B5419865
theorem B3170951 : Blo 1407523 3170951 := bstep (se 1 (by rfl) ⟨2378213, by rfl⟩ : syracuseStep 3170951 = 4756427) B4756427
theorem B2114183 : Blo 1407523 2114183 := bstep (se 1 (by rfl) ⟨1585637, by rfl⟩ : syracuseStep 2114183 = 3171275) B3171275
theorem B2114219 : Blo 1407523 2114219 := bstep (se 1 (by rfl) ⟨1585664, by rfl⟩ : syracuseStep 2114219 = 3171329) B3171329
theorem B3564233 : Blo 1407523 3564233 := bstep (se 2 (by rfl) ⟨1336587, by rfl⟩ : syracuseStep 3564233 = 2673175) B2673175
theorem B2114249 : Blo 1407523 2114249 := bstep (se 2 (by rfl) ⟨792843, by rfl⟩ : syracuseStep 2114249 = 1585687) B1585687
theorem B4752161 : Blo 1407523 4752161 := bstep (se 2 (by rfl) ⟨1782060, by rfl⟩ : syracuseStep 4752161 = 3564121) B3564121
theorem B3171131 : Blo 1407523 3171131 := bstep (se 1 (by rfl) ⟨2378348, by rfl⟩ : syracuseStep 3171131 = 4756697) B4756697
theorem B14451571 : Blo 1407523 14451571 := bstep (se 1 (by rfl) ⟨10838678, by rfl⟩ : syracuseStep 14451571 = 21677357) B21677357
theorem B6767495 : Blo 1407523 6767495 := bstep (se 1 (by rfl) ⟨5075621, by rfl⟩ : syracuseStep 6767495 = 10151243) B10151243
theorem B8684441 : Blo 1407523 8684441 := bstep (se 2 (by rfl) ⟨3256665, by rfl⟩ : syracuseStep 8684441 = 6513331) B6513331
theorem B3171257 : Blo 1407523 3171257 := bstep (se 2 (by rfl) ⟨1189221, by rfl⟩ : syracuseStep 3171257 = 2378443) B2378443
theorem B9634763 : Blo 1407523 9634763 := bstep (se 1 (by rfl) ⟨7226072, by rfl⟩ : syracuseStep 9634763 = 14452145) B14452145
theorem B3564587 : Blo 1407523 3564587 := bstep (se 1 (by rfl) ⟨2673440, by rfl⟩ : syracuseStep 3564587 = 5346881) B5346881
theorem B5710915 : Blo 1407523 5710915 := bstep (se 1 (by rfl) ⟨4283186, by rfl⟩ : syracuseStep 5710915 = 8566373) B8566373
theorem B2376823 : Blo 1407523 2376823 := bstep (se 1 (by rfl) ⟨1782617, by rfl⟩ : syracuseStep 2376823 = 3565235) B3565235
theorem B13534523 : Blo 1407523 13534523 := bstep (se 1 (by rfl) ⟨10150892, by rfl⟩ : syracuseStep 13534523 = 20301785) B20301785
theorem B2377019 : Blo 1407523 2377019 := bstep (se 1 (by rfl) ⟨1782764, by rfl⟩ : syracuseStep 2377019 = 3565529) B3565529
theorem B4752755 : Blo 1407523 4752755 := bstep (se 1 (by rfl) ⟨3564566, by rfl⟩ : syracuseStep 4752755 = 7129133) B7129133
theorem B3007945 : Blo 1407523 3007945 := bstep (se 2 (by rfl) ⟨1127979, by rfl⟩ : syracuseStep 3007945 = 2255959) B2255959
theorem B43378355 : Blo 1407523 43378355 := bstep (se 1 (by rfl) ⟨32533766, by rfl⟩ : syracuseStep 43378355 = 65067533) B65067533
theorem B2377417 : Blo 1407523 2377417 := bstep (se 2 (by rfl) ⟨891531, by rfl⟩ : syracuseStep 2377417 = 1783063) B1783063
theorem B27076427 : Blo 1407523 27076427 := bstep (se 1 (by rfl) ⟨20307320, by rfl⟩ : syracuseStep 27076427 = 40614641) B40614641
theorem B16033625 : Blo 1407523 16033625 := bstep (se 2 (by rfl) ⟨6012609, by rfl⟩ : syracuseStep 16033625 = 12025219) B12025219
theorem B3008441 : Blo 1407523 3008441 := bstep (se 2 (by rfl) ⟨1128165, by rfl⟩ : syracuseStep 3008441 = 2256331) B2256331
theorem B10700747 : Blo 1407523 10700747 := bstep (se 1 (by rfl) ⟨8025560, by rfl⟩ : syracuseStep 10700747 = 16051121) B16051121
theorem B3565579 : Blo 1407523 3565579 := bstep (se 1 (by rfl) ⟨2674184, by rfl⟩ : syracuseStep 3565579 = 5348369) B5348369
theorem B5351453 : Blo 1407523 5351453 := bstep (se 3 (by rfl) ⟨1003397, by rfl⟩ : syracuseStep 5351453 = 2006795) B2006795
theorem B5351467 : Blo 1407523 5351467 := bstep (se 1 (by rfl) ⟨4013600, by rfl⟩ : syracuseStep 5351467 = 8027201) B8027201
theorem B8022077 : Blo 1407523 8022077 := bstep (se 3 (by rfl) ⟨1504139, by rfl⟩ : syracuseStep 8022077 = 3008279) B3008279
theorem B3565721 : Blo 1407523 3565721 := bstep (se 2 (by rfl) ⟨1337145, by rfl⟩ : syracuseStep 3565721 = 2674291) B2674291
theorem B10987721 : Blo 1407523 10987721 := bstep (se 2 (by rfl) ⟨4120395, by rfl⟩ : syracuseStep 10987721 = 8240791) B8240791
theorem B2672939 : Blo 1407523 2672939 := bstep (se 1 (by rfl) ⟨2004704, by rfl⟩ : syracuseStep 2672939 = 4009409) B4009409
theorem B3565883 : Blo 1407523 3565883 := bstep (se 1 (by rfl) ⟨2674412, by rfl⟩ : syracuseStep 3565883 = 5348825) B5348825
theorem B2378119 : Blo 1407523 2378119 := bstep (se 1 (by rfl) ⟨1783589, by rfl⟩ : syracuseStep 2378119 = 3567179) B3567179
theorem B7612825 : Blo 1407523 7612825 := bstep (se 2 (by rfl) ⟨2854809, by rfl⟩ : syracuseStep 7612825 = 5709619) B5709619
theorem B5417401 : Blo 1407523 5417401 := bstep (se 2 (by rfl) ⟨2031525, by rfl⟩ : syracuseStep 5417401 = 4063051) B4063051
theorem B3566227 : Blo 1407523 3566227 := bstep (se 1 (by rfl) ⟨2674670, by rfl⟩ : syracuseStep 3566227 = 5349341) B5349341
theorem B1583887 : Blo 1407523 1583887 := bstep (se 1 (by rfl) ⟨1187915, by rfl⟩ : syracuseStep 1583887 = 2375831) B2375831
theorem B3566369 : Blo 1407523 3566369 := bstep (se 2 (by rfl) ⟨1337388, by rfl⟩ : syracuseStep 3566369 = 2674777) B2674777
theorem B3615521 : Blo 1407523 3615521 := bstep (se 2 (by rfl) ⟨1355820, by rfl⟩ : syracuseStep 3615521 = 2711641) B2711641
theorem B3009415 : Blo 1407523 3009415 := bstep (se 1 (by rfl) ⟨2257061, by rfl⟩ : syracuseStep 3009415 = 4514123) B4514123
theorem B10152971 : Blo 1407523 10152971 := bstep (se 1 (by rfl) ⟨7614728, by rfl⟩ : syracuseStep 10152971 = 15229457) B15229457
theorem B1584391 : Blo 1407523 1584391 := bstep (se 1 (by rfl) ⟨1188293, by rfl⟩ : syracuseStep 1584391 = 2376587) B2376587
theorem B1428751 : Blo 1407523 1428751 := bstep (se 1 (by rfl) ⟨1071563, by rfl⟩ : syracuseStep 1428751 = 2143127) B2143127
theorem B16264583 : Blo 1407523 16264583 := bstep (se 1 (by rfl) ⟨12198437, by rfl⟩ : syracuseStep 16264583 = 24396875) B24396875
theorem B2854291 : Blo 1407523 2854291 := bstep (se 1 (by rfl) ⟨2140718, by rfl⟩ : syracuseStep 2854291 = 4281437) B4281437
theorem B1584571 : Blo 1407523 1584571 := bstep (se 1 (by rfl) ⟨1188428, by rfl⟩ : syracuseStep 1584571 = 2376857) B2376857
theorem B2854415 : Blo 1407523 2854415 := bstep (se 1 (by rfl) ⟨2140811, by rfl⟩ : syracuseStep 2854415 = 4281623) B4281623
theorem B8564285 : Blo 1407523 8564285 := bstep (se 3 (by rfl) ⟨1605803, by rfl⟩ : syracuseStep 8564285 = 3211607) B3211607
theorem B4009591 : Blo 1407523 4009591 := bstep (se 1 (by rfl) ⟨3007193, by rfl⟩ : syracuseStep 4009591 = 6014387) B6014387
theorem B2256569 : Blo 1407523 2256569 := bstep (se 2 (by rfl) ⟨846213, by rfl⟩ : syracuseStep 2256569 = 1692427) B1692427
theorem B3567361 : Blo 1407523 3567361 := bstep (se 2 (by rfl) ⟨1337760, by rfl⟩ : syracuseStep 3567361 = 2675521) B2675521
theorem B2141959 : Blo 1407523 2141959 := bstep (se 1 (by rfl) ⟨1606469, by rfl⟩ : syracuseStep 2141959 = 3212939) B3212939
theorem B36581165 : Blo 1407523 36581165 := bstep (se 3 (by rfl) ⟨6858968, by rfl⟩ : syracuseStep 36581165 = 13717937) B13717937
theorem B28897073 : Blo 1407523 28897073 := bstep (se 2 (by rfl) ⟨10836402, by rfl⟩ : syracuseStep 28897073 = 21672805) B21672805
theorem B1585039 : Blo 1407523 1585039 := bstep (se 1 (by rfl) ⟨1188779, by rfl⟩ : syracuseStep 1585039 = 2377559) B2377559
theorem B4509587 : Blo 1407523 4509587 := bstep (se 1 (by rfl) ⟨3382190, by rfl⟩ : syracuseStep 4509587 = 6764381) B6764381
theorem B4755347 : Blo 1407523 4755347 := bstep (se 1 (by rfl) ⟨3566510, by rfl⟩ : syracuseStep 4755347 = 7133021) B7133021
theorem B2674633 : Blo 1407523 2674633 := bstep (se 2 (by rfl) ⟨1002987, by rfl⟩ : syracuseStep 2674633 = 2005975) B2005975
theorem B1781767 : Blo 1407523 1781767 := bstep (se 1 (by rfl) ⟨1336325, by rfl⟩ : syracuseStep 1781767 = 2672651) B2672651
theorem B18288913 : Blo 1407523 18288913 := bstep (se 2 (by rfl) ⟨6858342, by rfl⟩ : syracuseStep 18288913 = 13716685) B13716685
theorem B3805483 : Blo 1407523 3805483 := bstep (se 1 (by rfl) ⟨2854112, by rfl⟩ : syracuseStep 3805483 = 5708225) B5708225
theorem B2650411 : Blo 1407523 2650411 := bstep (se 1 (by rfl) ⟨1987808, by rfl⟩ : syracuseStep 2650411 = 3975617) B3975617
theorem B1585543 : Blo 1407523 1585543 := bstep (se 1 (by rfl) ⟨1189157, by rfl⟩ : syracuseStep 1585543 = 2378315) B2378315
theorem B1503631 : Blo 1407523 1503631 := bstep (se 1 (by rfl) ⟨1127723, by rfl⟩ : syracuseStep 1503631 = 2255447) B2255447
theorem B6771089 : Blo 1407523 6771089 := bstep (se 2 (by rfl) ⟨2539158, by rfl⟩ : syracuseStep 6771089 = 5078317) B5078317
theorem B8024467 : Blo 1407523 8024467 := bstep (se 1 (by rfl) ⟨6018350, by rfl⟩ : syracuseStep 8024467 = 12036701) B12036701
theorem B1782263 : Blo 1407523 1782263 := bstep (se 1 (by rfl) ⟨1336697, by rfl⟩ : syracuseStep 1782263 = 2673395) B2673395
theorem B4280843 : Blo 1407523 4280843 := bstep (se 1 (by rfl) ⟨3210632, by rfl⟩ : syracuseStep 4280843 = 6421265) B6421265
theorem B4280951 : Blo 1407523 4280951 := bstep (se 1 (by rfl) ⟨3210713, by rfl⟩ : syracuseStep 4280951 = 6421427) B6421427
theorem B1782415 : Blo 1407523 1782415 := bstep (se 1 (by rfl) ⟨1336811, by rfl⟩ : syracuseStep 1782415 = 2673623) B2673623
theorem B8245961 : Blo 1407523 8245961 := bstep (se 2 (by rfl) ⟨3092235, by rfl⟩ : syracuseStep 8245961 = 6184471) B6184471
theorem B3166991 : Blo 1407523 3166991 := bstep (se 1 (by rfl) ⟨2375243, by rfl⟩ : syracuseStep 3166991 = 4750487) B4750487
theorem B3167009 : Blo 1407523 3167009 := bstep (se 2 (by rfl) ⟨1187628, by rfl⟩ : syracuseStep 3167009 = 2375257) B2375257
theorem B8016677 : Blo 1407523 8016677 := bstep (se 4 (by rfl) ⟨751563, by rfl⟩ : syracuseStep 8016677 = 1503127) B1503127
theorem B5346107 : Blo 1407523 5346107 := bstep (se 1 (by rfl) ⟨4009580, by rfl⟩ : syracuseStep 5346107 = 8019161) B8019161
theorem B1782587 : Blo 1407523 1782587 := bstep (se 1 (by rfl) ⟨1336940, by rfl⟩ : syracuseStep 1782587 = 2673881) B2673881
theorem B4010867 : Blo 1407523 4010867 := bstep (se 1 (by rfl) ⟨3008150, by rfl⟩ : syracuseStep 4010867 = 6016301) B6016301
theorem B7132049 : Blo 1407523 7132049 := bstep (se 2 (by rfl) ⟨2674518, by rfl⟩ : syracuseStep 7132049 = 5349037) B5349037
theorem B4281241 : Blo 1407523 4281241 := bstep (se 2 (by rfl) ⟨1605465, by rfl⟩ : syracuseStep 4281241 = 3210931) B3210931
theorem B14652313 : Blo 1407523 14652313 := bstep (se 2 (by rfl) ⟨5494617, by rfl⟩ : syracuseStep 14652313 = 10989235) B10989235
theorem B6018077 : Blo 1407523 6018077 := bstep (se 3 (by rfl) ⟨1128389, by rfl⟩ : syracuseStep 6018077 = 2256779) B2256779
theorem B1627195 : Blo 1407523 1627195 := bstep (se 1 (by rfl) ⟨1220396, by rfl⟩ : syracuseStep 1627195 = 2440793) B2440793
theorem B4011095 : Blo 1407523 4011095 := bstep (se 1 (by rfl) ⟨3008321, by rfl⟩ : syracuseStep 4011095 = 6016643) B6016643
theorem B3167351 : Blo 1407523 3167351 := bstep (se 1 (by rfl) ⟨2375513, by rfl⟩ : syracuseStep 3167351 = 4751027) B4751027
theorem B1807607 : Blo 1407523 1807607 := bstep (se 1 (by rfl) ⟨1355705, by rfl⟩ : syracuseStep 1807607 = 2711411) B2711411
theorem B4756751 : Blo 1407523 4756751 := bstep (se 1 (by rfl) ⟨3567563, by rfl⟩ : syracuseStep 4756751 = 7135127) B7135127
theorem B5346593 : Blo 1407523 5346593 := bstep (se 2 (by rfl) ⟨2004972, by rfl⟩ : syracuseStep 5346593 = 4009945) B4009945
theorem B3167531 : Blo 1407523 3167531 := bstep (se 1 (by rfl) ⟨2375648, by rfl⟩ : syracuseStep 3167531 = 4751297) B4751297
theorem B102815153 : Blo 1407523 102815153 := bstep (se 2 (by rfl) ⟨38555682, by rfl⟩ : syracuseStep 102815153 = 77111365) B77111365
theorem B4757021 : Blo 1407523 4757021 := bstep (se 3 (by rfl) ⟨891941, by rfl⟩ : syracuseStep 4757021 = 1783883) B1783883
theorem B8017451 : Blo 1407523 8017451 := bstep (se 1 (by rfl) ⟨6013088, by rfl⟩ : syracuseStep 8017451 = 12026177) B12026177
theorem B3167891 : Blo 1407523 3167891 := bstep (se 1 (by rfl) ⟨2375918, by rfl⟩ : syracuseStep 3167891 = 4751837) B4751837
theorem B3806867 : Blo 1407523 3806867 := bstep (se 1 (by rfl) ⟨2855150, by rfl⟩ : syracuseStep 3806867 = 5710301) B5710301
theorem B3167945 : Blo 1407523 3167945 := bstep (se 2 (by rfl) ⟨1187979, by rfl⟩ : syracuseStep 3167945 = 2375959) B2375959
theorem B6018761 : Blo 1407523 6018761 := bstep (se 2 (by rfl) ⟨2257035, by rfl⟩ : syracuseStep 6018761 = 4514071) B4514071
theorem B1857287 : Blo 1407523 1857287 := bstep (se 1 (by rfl) ⟨1392965, by rfl⟩ : syracuseStep 1857287 = 2785931) B2785931
theorem B1783559 : Blo 1407523 1783559 := bstep (se 1 (by rfl) ⟨1337669, by rfl⟩ : syracuseStep 1783559 = 2675339) B2675339
theorem B6772531 : Blo 1407523 6772531 := bstep (se 1 (by rfl) ⟨5079398, by rfl⟩ : syracuseStep 6772531 = 10158797) B10158797
theorem B2111291 : Blo 1407523 2111291 := bstep (se 1 (by rfl) ⟨1583468, by rfl⟩ : syracuseStep 2111291 = 3166937) B3166937
theorem B2111351 : Blo 1407523 2111351 := bstep (se 1 (by rfl) ⟨1583513, by rfl⟩ : syracuseStep 2111351 = 3167027) B3167027
theorem B2111375 : Blo 1407523 2111375 := bstep (se 1 (by rfl) ⟨1583531, by rfl⟩ : syracuseStep 2111375 = 3167063) B3167063
theorem B2111417 : Blo 1407523 2111417 := bstep (se 2 (by rfl) ⟨791781, by rfl⟩ : syracuseStep 2111417 = 1583563) B1583563
theorem B2111495 : Blo 1407523 2111495 := bstep (se 1 (by rfl) ⟨1583621, by rfl⟩ : syracuseStep 2111495 = 3167243) B3167243
theorem B44546071 : Blo 1407523 44546071 := bstep (se 1 (by rfl) ⟨33409553, by rfl⟩ : syracuseStep 44546071 = 66819107) B66819107
theorem B6764573 : Blo 1407523 6764573 := bstep (se 3 (by rfl) ⟨1268357, by rfl⟩ : syracuseStep 6764573 = 2536715) B2536715
theorem B6101021 : Blo 1407523 6101021 := bstep (se 3 (by rfl) ⟨1143941, by rfl⟩ : syracuseStep 6101021 = 2287883) B2287883
theorem B2111531 : Blo 1407523 2111531 := bstep (se 1 (by rfl) ⟨1583648, by rfl⟩ : syracuseStep 2111531 = 3167297) B3167297
theorem B2111561 : Blo 1407523 2111561 := bstep (se 2 (by rfl) ⟨791835, by rfl⟩ : syracuseStep 2111561 = 1583671) B1583671
theorem B8026199 : Blo 1407523 8026199 := bstep (se 1 (by rfl) ⟨6019649, by rfl⟩ : syracuseStep 8026199 = 12039299) B12039299
theorem B12040325 : Blo 1407523 12040325 := bstep (se 4 (by rfl) ⟨1128780, by rfl⟩ : syracuseStep 12040325 = 2257561) B2257561
theorem B46307501 : Blo 1407523 46307501 := bstep (se 3 (by rfl) ⟨8682656, by rfl⟩ : syracuseStep 46307501 = 17365313) B17365313
theorem B2111675 : Blo 1407523 2111675 := bstep (se 1 (by rfl) ⟨1583756, by rfl⟩ : syracuseStep 2111675 = 3167513) B3167513
theorem B5347565 : Blo 1407523 5347565 := bstep (se 3 (by rfl) ⟨1002668, by rfl⟩ : syracuseStep 5347565 = 2005337) B2005337
theorem B2111735 : Blo 1407523 2111735 := bstep (se 1 (by rfl) ⟨1583801, by rfl⟩ : syracuseStep 2111735 = 3167603) B3167603
theorem B6764801 : Blo 1407523 6764801 := bstep (se 2 (by rfl) ⟨2536800, by rfl⟩ : syracuseStep 6764801 = 5073601) B5073601
theorem B2111759 : Blo 1407523 2111759 := bstep (se 1 (by rfl) ⟨1583819, by rfl⟩ : syracuseStep 2111759 = 3167639) B3167639
theorem B6019343 : Blo 1407523 6019343 := bstep (se 1 (by rfl) ⟨4514507, by rfl⟩ : syracuseStep 6019343 = 9029015) B9029015
theorem B2111801 : Blo 1407523 2111801 := bstep (se 2 (by rfl) ⟨791925, by rfl⟩ : syracuseStep 2111801 = 1583851) B1583851
theorem B2111879 : Blo 1407523 2111879 := bstep (se 1 (by rfl) ⟨1583909, by rfl⟩ : syracuseStep 2111879 = 3167819) B3167819
theorem B3168647 : Blo 1407523 3168647 := bstep (se 1 (by rfl) ⟨2376485, by rfl⟩ : syracuseStep 3168647 = 4752971) B4752971
theorem B4815251 : Blo 1407523 4815251 := bstep (se 1 (by rfl) ⟨3611438, by rfl⟩ : syracuseStep 4815251 = 7222877) B7222877
theorem B2111915 : Blo 1407523 2111915 := bstep (se 1 (by rfl) ⟨1583936, by rfl⟩ : syracuseStep 2111915 = 3167873) B3167873
theorem B2111945 : Blo 1407523 2111945 := bstep (se 2 (by rfl) ⟨791979, by rfl⟩ : syracuseStep 2111945 = 1583959) B1583959
theorem B5347883 : Blo 1407523 5347883 := bstep (se 1 (by rfl) ⟨4010912, by rfl⟩ : syracuseStep 5347883 = 8021825) B8021825
theorem B1407547 : Blo 1407523 1407547 := bstep (se 1 (by rfl) ⟨1055660, by rfl⟩ : syracuseStep 1407547 = 2111321) B2111321
theorem B2112059 : Blo 1407523 2112059 := bstep (se 1 (by rfl) ⟨1584044, by rfl⟩ : syracuseStep 2112059 = 3168089) B3168089
theorem B3168827 : Blo 1407523 3168827 := bstep (se 1 (by rfl) ⟨2376620, by rfl⟩ : syracuseStep 3168827 = 4753241) B4753241
theorem B2112119 : Blo 1407523 2112119 := bstep (se 1 (by rfl) ⟨1584089, by rfl⟩ : syracuseStep 2112119 = 3168179) B3168179
theorem B6019703 : Blo 1407523 6019703 := bstep (se 1 (by rfl) ⟨4514777, by rfl⟩ : syracuseStep 6019703 = 9029555) B9029555
theorem B1407623 : Blo 1407523 1407623 := bstep (se 1 (by rfl) ⟨1055717, by rfl⟩ : syracuseStep 1407623 = 2111435) B2111435
theorem B4012679 : Blo 1407523 4012679 := bstep (se 1 (by rfl) ⟨3009509, by rfl⟩ : syracuseStep 4012679 = 6019019) B6019019
theorem B1407631 : Blo 1407523 1407631 := bstep (se 1 (by rfl) ⟨1055723, by rfl⟩ : syracuseStep 1407631 = 2111447) B2111447
theorem B2112143 : Blo 1407523 2112143 := bstep (se 1 (by rfl) ⟨1584107, by rfl⟩ : syracuseStep 2112143 = 3168215) B3168215
theorem B2112185 : Blo 1407523 2112185 := bstep (se 2 (by rfl) ⟨792069, by rfl⟩ : syracuseStep 2112185 = 1584139) B1584139
theorem B3168953 : Blo 1407523 3168953 := bstep (se 2 (by rfl) ⟨1188357, by rfl⟩ : syracuseStep 3168953 = 2376715) B2376715
theorem B1407675 : Blo 1407523 1407675 := bstep (se 1 (by rfl) ⟨1055756, by rfl⟩ : syracuseStep 1407675 = 2111513) B2111513
theorem B1407751 : Blo 1407523 1407751 := bstep (se 1 (by rfl) ⟨1055813, by rfl⟩ : syracuseStep 1407751 = 2111627) B2111627
theorem B2112263 : Blo 1407523 2112263 := bstep (se 1 (by rfl) ⟨1584197, by rfl⟩ : syracuseStep 2112263 = 3168395) B3168395
theorem B1407759 : Blo 1407523 1407759 := bstep (se 1 (by rfl) ⟨1055819, by rfl⟩ : syracuseStep 1407759 = 2111639) B2111639
theorem B2112299 : Blo 1407523 2112299 := bstep (se 1 (by rfl) ⟨1584224, by rfl⟩ : syracuseStep 2112299 = 3168449) B3168449
theorem B1407803 : Blo 1407523 1407803 := bstep (se 1 (by rfl) ⟨1055852, by rfl⟩ : syracuseStep 1407803 = 2111705) B2111705
theorem B4012861 : Blo 1407523 4012861 := bstep (se 3 (by rfl) ⟨752411, by rfl⟩ : syracuseStep 4012861 = 1504823) B1504823
theorem B2112329 : Blo 1407523 2112329 := bstep (se 2 (by rfl) ⟨792123, by rfl⟩ : syracuseStep 2112329 = 1584247) B1584247
theorem B8567641 : Blo 1407523 8567641 := bstep (se 2 (by rfl) ⟨3212865, by rfl⟩ : syracuseStep 8567641 = 6425731) B6425731
theorem B12041075 : Blo 1407523 12041075 := bstep (se 1 (by rfl) ⟨9030806, by rfl⟩ : syracuseStep 12041075 = 18061613) B18061613
theorem B1407879 : Blo 1407523 1407879 := bstep (se 1 (by rfl) ⟨1055909, by rfl⟩ : syracuseStep 1407879 = 2111819) B2111819
theorem B1407887 : Blo 1407523 1407887 := bstep (se 1 (by rfl) ⟨1055915, by rfl⟩ : syracuseStep 1407887 = 2111831) B2111831
theorem B1407931 : Blo 1407523 1407931 := bstep (se 1 (by rfl) ⟨1055948, by rfl⟩ : syracuseStep 1407931 = 2111897) B2111897
theorem B2112443 : Blo 1407523 2112443 := bstep (se 1 (by rfl) ⟨1584332, by rfl⟩ : syracuseStep 2112443 = 3168665) B3168665
theorem B7134155 : Blo 1407523 7134155 := bstep (se 1 (by rfl) ⟨5350616, by rfl⟩ : syracuseStep 7134155 = 10701233) B10701233
theorem B8018909 : Blo 1407523 8018909 := bstep (se 3 (by rfl) ⟨1503545, by rfl⟩ : syracuseStep 8018909 = 3007091) B3007091
theorem B2112503 : Blo 1407523 2112503 := bstep (se 1 (by rfl) ⟨1584377, by rfl⟩ : syracuseStep 2112503 = 3168755) B3168755
theorem B1408007 : Blo 1407523 1408007 := bstep (se 1 (by rfl) ⟨1056005, by rfl⟩ : syracuseStep 1408007 = 2112011) B2112011
theorem B1408015 : Blo 1407523 1408015 := bstep (se 1 (by rfl) ⟨1056011, by rfl⟩ : syracuseStep 1408015 = 2112023) B2112023
theorem B2112527 : Blo 1407523 2112527 := bstep (se 1 (by rfl) ⟨1584395, by rfl⟩ : syracuseStep 2112527 = 3168791) B3168791
theorem B3169295 : Blo 1407523 3169295 := bstep (se 1 (by rfl) ⟨2376971, by rfl⟩ : syracuseStep 3169295 = 4753943) B4753943
theorem B3169313 : Blo 1407523 3169313 := bstep (se 2 (by rfl) ⟨1188492, by rfl⟩ : syracuseStep 3169313 = 2376985) B2376985
theorem B2112569 : Blo 1407523 2112569 := bstep (se 2 (by rfl) ⟨792213, by rfl⟩ : syracuseStep 2112569 = 1584427) B1584427
theorem B1408059 : Blo 1407523 1408059 := bstep (se 1 (by rfl) ⟨1056044, by rfl⟩ : syracuseStep 1408059 = 2112089) B2112089
theorem B4512829 : Blo 1407523 4512829 := bstep (se 3 (by rfl) ⟨846155, by rfl⟩ : syracuseStep 4512829 = 1692311) B1692311
theorem B1408135 : Blo 1407523 1408135 := bstep (se 1 (by rfl) ⟨1056101, by rfl⟩ : syracuseStep 1408135 = 2112203) B2112203
theorem B2112647 : Blo 1407523 2112647 := bstep (se 1 (by rfl) ⟨1584485, by rfl⟩ : syracuseStep 2112647 = 3168971) B3168971
theorem B1408143 : Blo 1407523 1408143 := bstep (se 1 (by rfl) ⟨1056107, by rfl⟩ : syracuseStep 1408143 = 2112215) B2112215
theorem B3808403 : Blo 1407523 3808403 := bstep (se 1 (by rfl) ⟨2856302, by rfl⟩ : syracuseStep 3808403 = 5712605) B5712605
theorem B2112683 : Blo 1407523 2112683 := bstep (se 1 (by rfl) ⟨1584512, by rfl⟩ : syracuseStep 2112683 = 3169025) B3169025
theorem B1408187 : Blo 1407523 1408187 := bstep (se 1 (by rfl) ⟨1056140, by rfl⟩ : syracuseStep 1408187 = 2112281) B2112281
theorem B2006203 : Blo 1407523 2006203 := bstep (se 1 (by rfl) ⟨1504652, by rfl⟩ : syracuseStep 2006203 = 3009305) B3009305
theorem B7126217 : Blo 1407523 7126217 := bstep (se 2 (by rfl) ⟨2672331, by rfl⟩ : syracuseStep 7126217 = 5344663) B5344663
theorem B2112713 : Blo 1407523 2112713 := bstep (se 2 (by rfl) ⟨792267, by rfl⟩ : syracuseStep 2112713 = 1584535) B1584535
theorem B1408263 : Blo 1407523 1408263 := bstep (se 1 (by rfl) ⟨1056197, by rfl⟩ : syracuseStep 1408263 = 2112395) B2112395
theorem B1408271 : Blo 1407523 1408271 := bstep (se 1 (by rfl) ⟨1056203, by rfl⟩ : syracuseStep 1408271 = 2112407) B2112407
theorem B7134479 : Blo 1407523 7134479 := bstep (se 1 (by rfl) ⟨5350859, by rfl⟩ : syracuseStep 7134479 = 10701719) B10701719
theorem B4013327 : Blo 1407523 4013327 := bstep (se 1 (by rfl) ⟨3009995, by rfl⟩ : syracuseStep 4013327 = 6019991) B6019991
theorem B1408315 : Blo 1407523 1408315 := bstep (se 1 (by rfl) ⟨1056236, by rfl⟩ : syracuseStep 1408315 = 2112473) B2112473
theorem B2112827 : Blo 1407523 2112827 := bstep (se 1 (by rfl) ⟨1584620, by rfl⟩ : syracuseStep 2112827 = 3169241) B3169241
theorem B2112887 : Blo 1407523 2112887 := bstep (se 1 (by rfl) ⟨1584665, by rfl⟩ : syracuseStep 2112887 = 3169331) B3169331
theorem B3169655 : Blo 1407523 3169655 := bstep (se 1 (by rfl) ⟨2377241, by rfl⟩ : syracuseStep 3169655 = 4754483) B4754483
theorem B1408391 : Blo 1407523 1408391 := bstep (se 1 (by rfl) ⟨1056293, by rfl⟩ : syracuseStep 1408391 = 2112587) B2112587
theorem B1408399 : Blo 1407523 1408399 := bstep (se 1 (by rfl) ⟨1056299, by rfl⟩ : syracuseStep 1408399 = 2112599) B2112599
theorem B2112911 : Blo 1407523 2112911 := bstep (se 1 (by rfl) ⟨1584683, by rfl⟩ : syracuseStep 2112911 = 3169367) B3169367
theorem B3562937 : Blo 1407523 3562937 := bstep (se 2 (by rfl) ⟨1336101, by rfl⟩ : syracuseStep 3562937 = 2672203) B2672203
theorem B2112953 : Blo 1407523 2112953 := bstep (se 2 (by rfl) ⟨792357, by rfl⟩ : syracuseStep 2112953 = 1584715) B1584715
theorem B1408443 : Blo 1407523 1408443 := bstep (se 1 (by rfl) ⟨1056332, by rfl⟩ : syracuseStep 1408443 = 2112665) B2112665
theorem B11427281 : Blo 1407523 11427281 := bstep (se 2 (by rfl) ⟨4285230, by rfl⟩ : syracuseStep 11427281 = 8570461) B8570461
theorem B1408519 : Blo 1407523 1408519 := bstep (se 1 (by rfl) ⟨1056389, by rfl⟩ : syracuseStep 1408519 = 2112779) B2112779
theorem B2113031 : Blo 1407523 2113031 := bstep (se 1 (by rfl) ⟨1584773, by rfl⟩ : syracuseStep 2113031 = 3169547) B3169547
theorem B1408527 : Blo 1407523 1408527 := bstep (se 1 (by rfl) ⟨1056395, by rfl⟩ : syracuseStep 1408527 = 2112791) B2112791
theorem B2113067 : Blo 1407523 2113067 := bstep (se 1 (by rfl) ⟨1584800, by rfl⟩ : syracuseStep 2113067 = 3169601) B3169601
theorem B3169835 : Blo 1407523 3169835 := bstep (se 1 (by rfl) ⟨2377376, by rfl⟩ : syracuseStep 3169835 = 4754753) B4754753
theorem B1408571 : Blo 1407523 1408571 := bstep (se 1 (by rfl) ⟨1056428, by rfl⟩ : syracuseStep 1408571 = 2112857) B2112857
theorem B6020675 : Blo 1407523 6020675 := bstep (se 1 (by rfl) ⟨4515506, by rfl⟩ : syracuseStep 6020675 = 9031013) B9031013
theorem B2113097 : Blo 1407523 2113097 := bstep (se 2 (by rfl) ⟨792411, by rfl⟩ : syracuseStep 2113097 = 1584823) B1584823
theorem B10698317 : Blo 1407523 10698317 := bstep (se 3 (by rfl) ⟨2005934, by rfl⟩ : syracuseStep 10698317 = 4011869) B4011869
theorem B1408647 : Blo 1407523 1408647 := bstep (se 1 (by rfl) ⟨1056485, by rfl⟩ : syracuseStep 1408647 = 2112971) B2112971
theorem B1408655 : Blo 1407523 1408655 := bstep (se 1 (by rfl) ⟨1056491, by rfl⟩ : syracuseStep 1408655 = 2112983) B2112983
theorem B1408699 : Blo 1407523 1408699 := bstep (se 1 (by rfl) ⟨1056524, by rfl⟩ : syracuseStep 1408699 = 2113049) B2113049
theorem B2113211 : Blo 1407523 2113211 := bstep (se 1 (by rfl) ⟨1584908, by rfl⟩ : syracuseStep 2113211 = 3169817) B3169817
theorem B7610057 : Blo 1407523 7610057 := bstep (se 2 (by rfl) ⟨2853771, by rfl⟩ : syracuseStep 7610057 = 5707543) B5707543
theorem B2113271 : Blo 1407523 2113271 := bstep (se 1 (by rfl) ⟨1584953, by rfl⟩ : syracuseStep 2113271 = 3169907) B3169907
theorem B1408775 : Blo 1407523 1408775 := bstep (se 1 (by rfl) ⟨1056581, by rfl⟩ : syracuseStep 1408775 = 2113163) B2113163
theorem B1408783 : Blo 1407523 1408783 := bstep (se 1 (by rfl) ⟨1056587, by rfl⟩ : syracuseStep 1408783 = 2113175) B2113175
theorem B2113295 : Blo 1407523 2113295 := bstep (se 1 (by rfl) ⟨1584971, by rfl⟩ : syracuseStep 2113295 = 3169943) B3169943
theorem B14458673 : Blo 1407523 14458673 := bstep (se 2 (by rfl) ⟨5422002, by rfl⟩ : syracuseStep 14458673 = 10844005) B10844005
theorem B2113337 : Blo 1407523 2113337 := bstep (se 2 (by rfl) ⟨792501, by rfl⟩ : syracuseStep 2113337 = 1585003) B1585003
theorem B6012731 : Blo 1407523 6012731 := bstep (se 1 (by rfl) ⟨4509548, by rfl⟩ : syracuseStep 6012731 = 9019097) B9019097
theorem B1408827 : Blo 1407523 1408827 := bstep (se 1 (by rfl) ⟨1056620, by rfl⟩ : syracuseStep 1408827 = 2113241) B2113241
theorem B2006903 : Blo 1407523 2006903 := bstep (se 1 (by rfl) ⟨1505177, by rfl⟩ : syracuseStep 2006903 = 3010355) B3010355
theorem B1408903 : Blo 1407523 1408903 := bstep (se 1 (by rfl) ⟨1056677, by rfl⟩ : syracuseStep 1408903 = 2113355) B2113355
theorem B2113415 : Blo 1407523 2113415 := bstep (se 1 (by rfl) ⟨1585061, by rfl⟩ : syracuseStep 2113415 = 3170123) B3170123
theorem B1408911 : Blo 1407523 1408911 := bstep (se 1 (by rfl) ⟨1056683, by rfl⟩ : syracuseStep 1408911 = 2113367) B2113367
theorem B3170195 : Blo 1407523 3170195 := bstep (se 1 (by rfl) ⟨2377646, by rfl⟩ : syracuseStep 3170195 = 4755293) B4755293
theorem B2113451 : Blo 1407523 2113451 := bstep (se 1 (by rfl) ⟨1585088, by rfl⟩ : syracuseStep 2113451 = 3170177) B3170177
theorem B1408955 : Blo 1407523 1408955 := bstep (se 1 (by rfl) ⟨1056716, by rfl⟩ : syracuseStep 1408955 = 2113433) B2113433
theorem B2113481 : Blo 1407523 2113481 := bstep (se 2 (by rfl) ⟨792555, by rfl⟩ : syracuseStep 2113481 = 1585111) B1585111
theorem B3170249 : Blo 1407523 3170249 := bstep (se 2 (by rfl) ⟨1188843, by rfl⟩ : syracuseStep 3170249 = 2377687) B2377687
theorem B9404419 : Blo 1407523 9404419 := bstep (se 1 (by rfl) ⟨7053314, by rfl⟩ : syracuseStep 9404419 = 14106629) B14106629
theorem B2375689 : Blo 1407523 2375689 := bstep (se 2 (by rfl) ⟨890883, by rfl⟩ : syracuseStep 2375689 = 1781767) B1781767
theorem B1409063 : Blo 1407523 1409063 := bstep (se 1 (by rfl) ⟨1056797, by rfl⟩ : syracuseStep 1409063 = 2113595) B2113595
theorem B7135289 : Blo 1407523 7135289 := bstep (se 2 (by rfl) ⟨2675733, by rfl⟩ : syracuseStep 7135289 = 5351467) B5351467
theorem B16048205 : Blo 1407523 16048205 := bstep (se 3 (by rfl) ⟨3009038, by rfl⟩ : syracuseStep 16048205 = 6018077) B6018077
theorem B1409103 : Blo 1407523 1409103 := bstep (se 1 (by rfl) ⟨1056827, by rfl⟩ : syracuseStep 1409103 = 2113655) B2113655
theorem B1409119 : Blo 1407523 1409119 := bstep (se 1 (by rfl) ⟨1056839, by rfl⟩ : syracuseStep 1409119 = 2113679) B2113679
theorem B1409147 : Blo 1407523 1409147 := bstep (se 1 (by rfl) ⟨1056860, by rfl⟩ : syracuseStep 1409147 = 2113721) B2113721
theorem B4751513 : Blo 1407523 4751513 := bstep (se 2 (by rfl) ⟨1781817, by rfl⟩ : syracuseStep 4751513 = 3563635) B3563635
theorem B2375851 : Blo 1407523 2375851 := bstep (se 1 (by rfl) ⟨1781888, by rfl⟩ : syracuseStep 2375851 = 3563777) B3563777
theorem B1409199 : Blo 1407523 1409199 := bstep (se 1 (by rfl) ⟨1056899, by rfl⟩ : syracuseStep 1409199 = 2113799) B2113799
theorem B1409223 : Blo 1407523 1409223 := bstep (se 1 (by rfl) ⟨1056917, by rfl⟩ : syracuseStep 1409223 = 2113835) B2113835
theorem B1409243 : Blo 1407523 1409243 := bstep (se 1 (by rfl) ⟨1056932, by rfl⟩ : syracuseStep 1409243 = 2113865) B2113865
theorem B4514059 : Blo 1407523 4514059 := bstep (se 1 (by rfl) ⟨3385544, by rfl⟩ : syracuseStep 4514059 = 6771089) B6771089
theorem B1409319 : Blo 1407523 1409319 := bstep (se 1 (by rfl) ⟨1056989, by rfl⟩ : syracuseStep 1409319 = 2113979) B2113979
theorem B1409359 : Blo 1407523 1409359 := bstep (se 1 (by rfl) ⟨1057019, by rfl⟩ : syracuseStep 1409359 = 2114039) B2114039
theorem B1409375 : Blo 1407523 1409375 := bstep (se 1 (by rfl) ⟨1057031, by rfl⟩ : syracuseStep 1409375 = 2114063) B2114063
theorem B30458213 : Blo 1407523 30458213 := bstep (se 4 (by rfl) ⟨2855457, by rfl⟩ : syracuseStep 30458213 = 5710915) B5710915
theorem B1409403 : Blo 1407523 1409403 := bstep (se 1 (by rfl) ⟨1057052, by rfl⟩ : syracuseStep 1409403 = 2114105) B2114105
theorem B2113967 : Blo 1407523 2113967 := bstep (se 1 (by rfl) ⟨1585475, by rfl⟩ : syracuseStep 2113967 = 3170951) B3170951
theorem B1409455 : Blo 1407523 1409455 := bstep (se 1 (by rfl) ⟨1057091, by rfl⟩ : syracuseStep 1409455 = 2114183) B2114183
theorem B1409479 : Blo 1407523 1409479 := bstep (se 1 (by rfl) ⟨1057109, by rfl⟩ : syracuseStep 1409479 = 2114219) B2114219
theorem B2376155 : Blo 1407523 2376155 := bstep (se 1 (by rfl) ⟨1782116, by rfl⟩ : syracuseStep 2376155 = 3564233) B3564233
theorem B5497307 : Blo 1407523 5497307 := bstep (se 1 (by rfl) ⟨4122980, by rfl⟩ : syracuseStep 5497307 = 8245961) B8245961
theorem B1409499 : Blo 1407523 1409499 := bstep (se 1 (by rfl) ⟨1057124, by rfl⟩ : syracuseStep 1409499 = 2114249) B2114249
theorem B3170825 : Blo 1407523 3170825 := bstep (se 2 (by rfl) ⟨1189059, by rfl⟩ : syracuseStep 3170825 = 2378119) B2378119
theorem B2114057 : Blo 1407523 2114057 := bstep (se 2 (by rfl) ⟨792771, by rfl⟩ : syracuseStep 2114057 = 1585543) B1585543
theorem B10699289 : Blo 1407523 10699289 := bstep (se 2 (by rfl) ⟨4012233, by rfl⟩ : syracuseStep 10699289 = 8024467) B8024467
theorem B10150433 : Blo 1407523 10150433 := bstep (se 2 (by rfl) ⟨3806412, by rfl⟩ : syracuseStep 10150433 = 7612825) B7612825
theorem B3564071 : Blo 1407523 3564071 := bstep (se 1 (by rfl) ⟨2673053, by rfl⟩ : syracuseStep 3564071 = 5346107) B5346107
theorem B2114087 : Blo 1407523 2114087 := bstep (se 1 (by rfl) ⟨1585565, by rfl⟩ : syracuseStep 2114087 = 3171131) B3171131
theorem B2114171 : Blo 1407523 2114171 := bstep (se 1 (by rfl) ⟨1585628, by rfl⟩ : syracuseStep 2114171 = 3171257) B3171257
theorem B6423175 : Blo 1407523 6423175 := bstep (se 1 (by rfl) ⟨4817381, by rfl⟩ : syracuseStep 6423175 = 9634763) B9634763
theorem B18039469 : Blo 1407523 18039469 := bstep (se 3 (by rfl) ⟨3382400, by rfl⟩ : syracuseStep 18039469 = 6764801) B6764801
theorem B2376391 : Blo 1407523 2376391 := bstep (se 1 (by rfl) ⟨1782293, by rfl⟩ : syracuseStep 2376391 = 3564587) B3564587
theorem B4817657 : Blo 1407523 4817657 := bstep (se 2 (by rfl) ⟨1806621, by rfl⟩ : syracuseStep 4817657 = 3613243) B3613243
theorem B7127837 : Blo 1407523 7127837 := bstep (se 3 (by rfl) ⟨1336469, by rfl⟩ : syracuseStep 7127837 = 2672939) B2672939
theorem B3171167 : Blo 1407523 3171167 := bstep (se 1 (by rfl) ⟨2378375, by rfl⟩ : syracuseStep 3171167 = 4756751) B4756751
theorem B2376553 : Blo 1407523 2376553 := bstep (se 2 (by rfl) ⟨891207, by rfl⟩ : syracuseStep 2376553 = 1782415) B1782415
theorem B3564395 : Blo 1407523 3564395 := bstep (se 1 (by rfl) ⟨2673296, by rfl⟩ : syracuseStep 3564395 = 5346593) B5346593
theorem B68543435 : Blo 1407523 68543435 := bstep (se 1 (by rfl) ⟨51407576, by rfl⟩ : syracuseStep 68543435 = 102815153) B102815153
theorem B3171347 : Blo 1407523 3171347 := bstep (se 1 (by rfl) ⟨2378510, by rfl⟩ : syracuseStep 3171347 = 4757021) B4757021
theorem B5350481 : Blo 1407523 5350481 := bstep (se 2 (by rfl) ⟨2006430, by rfl⟩ : syracuseStep 5350481 = 4012861) B4012861
theorem B28918903 : Blo 1407523 28918903 := bstep (se 1 (by rfl) ⟨21689177, by rfl⟩ : syracuseStep 28918903 = 43378355) B43378355
theorem B19268761 : Blo 1407523 19268761 := bstep (se 2 (by rfl) ⟨7225785, by rfl⟩ : syracuseStep 19268761 = 14451571) B14451571
theorem B4752701 : Blo 1407523 4752701 := bstep (se 3 (by rfl) ⟨891131, by rfl⟩ : syracuseStep 4752701 = 1782263) B1782263
theorem B5350799 : Blo 1407523 5350799 := bstep (se 1 (by rfl) ⟨4013099, by rfl⟩ : syracuseStep 5350799 = 8026199) B8026199
theorem B2377147 : Blo 1407523 2377147 := bstep (se 1 (by rfl) ⟨1782860, by rfl⟩ : syracuseStep 2377147 = 3565721) B3565721
theorem B7325147 : Blo 1407523 7325147 := bstep (se 1 (by rfl) ⟨5493860, by rfl⟩ : syracuseStep 7325147 = 10987721) B10987721
theorem B3565043 : Blo 1407523 3565043 := bstep (se 1 (by rfl) ⟨2673782, by rfl⟩ : syracuseStep 3565043 = 5347565) B5347565
theorem B2377255 : Blo 1407523 2377255 := bstep (se 1 (by rfl) ⟨1782941, by rfl⟩ : syracuseStep 2377255 = 3565883) B3565883
theorem B3565255 : Blo 1407523 3565255 := bstep (se 1 (by rfl) ⟨2673941, by rfl⟩ : syracuseStep 3565255 = 5347883) B5347883
theorem B2377579 : Blo 1407523 2377579 := bstep (se 1 (by rfl) ⟨1783184, by rfl⟩ : syracuseStep 2377579 = 3566369) B3566369
theorem B6768647 : Blo 1407523 6768647 := bstep (se 1 (by rfl) ⟨5076485, by rfl⟩ : syracuseStep 6768647 = 10152971) B10152971
theorem B78145669 : Blo 1407523 78145669 := bstep (se 4 (by rfl) ⟨7326156, by rfl⟩ : syracuseStep 78145669 = 14652313) B14652313
theorem B4753565 : Blo 1407523 4753565 := bstep (se 3 (by rfl) ⟨891293, by rfl⟩ : syracuseStep 4753565 = 1782587) B1782587
theorem B5351741 : Blo 1407523 5351741 := bstep (se 3 (by rfl) ⟨1003451, by rfl⟩ : syracuseStep 5351741 = 2006903) B2006903
theorem B1902943 : Blo 1407523 1902943 := bstep (se 1 (by rfl) ⟨1427207, by rfl⟩ : syracuseStep 1902943 = 2854415) B2854415
theorem B16042373 : Blo 1407523 16042373 := bstep (se 4 (by rfl) ⟨1503972, by rfl⟩ : syracuseStep 16042373 = 3007945) B3007945
theorem B9030041 : Blo 1407523 9030041 := bstep (se 2 (by rfl) ⟨3386265, by rfl⟩ : syracuseStep 9030041 = 6772531) B6772531
theorem B5073371 : Blo 1407523 5073371 := bstep (se 1 (by rfl) ⟨3805028, by rfl⟩ : syracuseStep 5073371 = 7610057) B7610057
theorem B8022509 : Blo 1407523 8022509 := bstep (se 3 (by rfl) ⟨1504220, by rfl⟩ : syracuseStep 8022509 = 3008441) B3008441
theorem B4008487 : Blo 1407523 4008487 := bstep (se 1 (by rfl) ⟨3006365, by rfl⟩ : syracuseStep 4008487 = 6012731) B6012731
theorem B3566177 : Blo 1407523 3566177 := bstep (se 2 (by rfl) ⟨1337316, by rfl⟩ : syracuseStep 3566177 = 2674633) B2674633
theorem B4754105 : Blo 1407523 4754105 := bstep (se 2 (by rfl) ⟨1782789, by rfl⟩ : syracuseStep 4754105 = 3565579) B3565579
theorem B1583815 : Blo 1407523 1583815 := bstep (se 1 (by rfl) ⟨1187861, by rfl⟩ : syracuseStep 1583815 = 2375723) B2375723
theorem B59394761 : Blo 1407523 59394761 := bstep (se 2 (by rfl) ⟨22273035, by rfl⟩ : syracuseStep 59394761 = 44546071) B44546071
theorem B3009467 : Blo 1407523 3009467 := bstep (se 1 (by rfl) ⟨2257100, by rfl⟩ : syracuseStep 3009467 = 4514201) B4514201
theorem B2853895 : Blo 1407523 2853895 := bstep (se 1 (by rfl) ⟨2140421, by rfl⟩ : syracuseStep 2853895 = 4280843) B4280843
theorem B5073977 : Blo 1407523 5073977 := bstep (se 2 (by rfl) ⟨1902741, by rfl⟩ : syracuseStep 5073977 = 3805483) B3805483
theorem B3533881 : Blo 1407523 3533881 := bstep (se 2 (by rfl) ⟨1325205, by rfl⟩ : syracuseStep 3533881 = 2650411) B2650411
theorem B2853967 : Blo 1407523 2853967 := bstep (se 1 (by rfl) ⟨2140475, by rfl⟩ : syracuseStep 2853967 = 4280951) B4280951
theorem B5344451 : Blo 1407523 5344451 := bstep (se 1 (by rfl) ⟨4008338, by rfl⟩ : syracuseStep 5344451 = 8016677) B8016677
theorem B2673911 : Blo 1407523 2673911 := bstep (se 1 (by rfl) ⟨2005433, by rfl⟩ : syracuseStep 2673911 = 4010867) B4010867
theorem B4754699 : Blo 1407523 4754699 := bstep (se 1 (by rfl) ⟨3566024, by rfl⟩ : syracuseStep 4754699 = 7132049) B7132049
theorem B4820285 : Blo 1407523 4820285 := bstep (se 3 (by rfl) ⟨903803, by rfl⟩ : syracuseStep 4820285 = 1807607) B1807607
theorem B10702205 : Blo 1407523 10702205 := bstep (se 3 (by rfl) ⟨2006663, by rfl⟩ : syracuseStep 10702205 = 4013327) B4013327
theorem B2674063 : Blo 1407523 2674063 := bstep (se 1 (by rfl) ⟨2005547, by rfl⟩ : syracuseStep 2674063 = 4011095) B4011095
theorem B4754969 : Blo 1407523 4754969 := bstep (se 2 (by rfl) ⟨1783113, by rfl⟩ : syracuseStep 4754969 = 3566227) B3566227
theorem B9023015 : Blo 1407523 9023015 := bstep (se 1 (by rfl) ⟨6767261, by rfl⟩ : syracuseStep 9023015 = 13534523) B13534523
theorem B1584679 : Blo 1407523 1584679 := bstep (se 1 (by rfl) ⟨1188509, by rfl⟩ : syracuseStep 1584679 = 2377019) B2377019
theorem B5344967 : Blo 1407523 5344967 := bstep (se 1 (by rfl) ⟨4008725, by rfl⟩ : syracuseStep 5344967 = 8017451) B8017451
theorem B9023197 : Blo 1407523 9023197 := bstep (se 3 (by rfl) ⟨1691849, by rfl⟩ : syracuseStep 9023197 = 3383699) B3383699
theorem B11423521 : Blo 1407523 11423521 := bstep (se 2 (by rfl) ⟨4283820, by rfl⟩ : syracuseStep 11423521 = 8567641) B8567641
theorem B18050951 : Blo 1407523 18050951 := bstep (se 1 (by rfl) ⟨13538213, by rfl⟩ : syracuseStep 18050951 = 27076427) B27076427
theorem B4509715 : Blo 1407523 4509715 := bstep (se 1 (by rfl) ⟨3382286, by rfl⟩ : syracuseStep 4509715 = 6764573) B6764573
theorem B4067347 : Blo 1407523 4067347 := bstep (se 1 (by rfl) ⟨3050510, by rfl⟩ : syracuseStep 4067347 = 6101021) B6101021
theorem B3567635 : Blo 1407523 3567635 := bstep (se 1 (by rfl) ⟨2675726, by rfl⟩ : syracuseStep 3567635 = 5351453) B5351453
theorem B6017105 : Blo 1407523 6017105 := bstep (se 2 (by rfl) ⟨2256414, by rfl⟩ : syracuseStep 6017105 = 4512829) B4512829
theorem B30871667 : Blo 1407523 30871667 := bstep (se 1 (by rfl) ⟨23153750, by rfl⟩ : syracuseStep 30871667 = 46307501) B46307501
theorem B2674937 : Blo 1407523 2674937 := bstep (se 2 (by rfl) ⟨1003101, by rfl⟩ : syracuseStep 2674937 = 2006203) B2006203
theorem B1905001 : Blo 1407523 1905001 := bstep (se 2 (by rfl) ⟨714375, by rfl⟩ : syracuseStep 1905001 = 1428751) B1428751
theorem B2675119 : Blo 1407523 2675119 := bstep (se 1 (by rfl) ⟨2006339, by rfl⟩ : syracuseStep 2675119 = 4012679) B4012679
theorem B3805721 : Blo 1407523 3805721 := bstep (se 2 (by rfl) ⟨1427145, by rfl⟩ : syracuseStep 3805721 = 2854291) B2854291
theorem B4756103 : Blo 1407523 4756103 := bstep (se 1 (by rfl) ⟨3567077, by rfl⟩ : syracuseStep 4756103 = 7134155) B7134155
theorem B5345939 : Blo 1407523 5345939 := bstep (se 1 (by rfl) ⟨4009454, by rfl⟩ : syracuseStep 5345939 = 8018909) B8018909
theorem B4952765 : Blo 1407523 4952765 := bstep (se 3 (by rfl) ⟨928643, by rfl⟩ : syracuseStep 4952765 = 1857287) B1857287
theorem B4756157 : Blo 1407523 4756157 := bstep (se 3 (by rfl) ⟨891779, by rfl⟩ : syracuseStep 4756157 = 1783559) B1783559
theorem B38556461 : Blo 1407523 38556461 := bstep (se 3 (by rfl) ⟨7229336, by rfl⟩ : syracuseStep 38556461 = 14458673) B14458673
theorem B5346121 : Blo 1407523 5346121 := bstep (se 2 (by rfl) ⟨2004795, by rfl⟩ : syracuseStep 5346121 = 4009591) B4009591
theorem B4756319 : Blo 1407523 4756319 := bstep (se 1 (by rfl) ⟨3567239, by rfl⟩ : syracuseStep 4756319 = 7134479) B7134479
theorem B10843055 : Blo 1407523 10843055 := bstep (se 1 (by rfl) ⟨8132291, by rfl⟩ : syracuseStep 10843055 = 16264583) B16264583
theorem B4756481 : Blo 1407523 4756481 := bstep (se 2 (by rfl) ⟨1783680, by rfl⟩ : syracuseStep 4756481 = 3567361) B3567361
theorem B2855945 : Blo 1407523 2855945 := bstep (se 2 (by rfl) ⟨1070979, by rfl⟩ : syracuseStep 2855945 = 2141959) B2141959
theorem B7132211 : Blo 1407523 7132211 := bstep (se 1 (by rfl) ⟨5349158, by rfl⟩ : syracuseStep 7132211 = 10698317) B10698317
theorem B1504379 : Blo 1407523 1504379 := bstep (se 1 (by rfl) ⟨1128284, by rfl⟩ : syracuseStep 1504379 = 2256569) B2256569
theorem B19264715 : Blo 1407523 19264715 := bstep (se 1 (by rfl) ⟨14448536, by rfl⟩ : syracuseStep 19264715 = 28897073) B28897073
theorem B3167783 : Blo 1407523 3167783 := bstep (se 1 (by rfl) ⟨2375837, by rfl⟩ : syracuseStep 3167783 = 4751675) B4751675
theorem B3806759 : Blo 1407523 3806759 := bstep (se 1 (by rfl) ⟨2855069, by rfl⟩ : syracuseStep 3806759 = 5710139) B5710139
theorem B38565557 : Blo 1407523 38565557 := bstep (se 5 (by rfl) ⟨1807760, by rfl⟩ : syracuseStep 38565557 = 3615521) B3615521
theorem B24385217 : Blo 1407523 24385217 := bstep (se 2 (by rfl) ⟨9144456, by rfl⟩ : syracuseStep 24385217 = 18288913) B18288913
theorem B2111327 : Blo 1407523 2111327 := bstep (se 1 (by rfl) ⟨1583495, by rfl⟩ : syracuseStep 2111327 = 3166991) B3166991
theorem B2004841 : Blo 1407523 2004841 := bstep (se 2 (by rfl) ⟨751815, by rfl⟩ : syracuseStep 2004841 = 1503631) B1503631
theorem B2111339 : Blo 1407523 2111339 := bstep (se 1 (by rfl) ⟨1583504, by rfl⟩ : syracuseStep 2111339 = 3167009) B3167009
theorem B3168107 : Blo 1407523 3168107 := bstep (se 1 (by rfl) ⟨2376080, by rfl⟩ : syracuseStep 3168107 = 4752161) B4752161
theorem B7223201 : Blo 1407523 7223201 := bstep (se 2 (by rfl) ⟨2708700, by rfl⟩ : syracuseStep 7223201 = 5417401) B5417401
theorem B3168161 : Blo 1407523 3168161 := bstep (se 2 (by rfl) ⟨1188060, by rfl⟩ : syracuseStep 3168161 = 2376121) B2376121
theorem B4511663 : Blo 1407523 4511663 := bstep (se 1 (by rfl) ⟨3383747, by rfl⟩ : syracuseStep 4511663 = 6767495) B6767495
theorem B5789627 : Blo 1407523 5789627 := bstep (se 1 (by rfl) ⟨4342220, by rfl⟩ : syracuseStep 5789627 = 8684441) B8684441
theorem B2111567 : Blo 1407523 2111567 := bstep (se 1 (by rfl) ⟨1583675, by rfl⟩ : syracuseStep 2111567 = 3167351) B3167351
theorem B10836125 : Blo 1407523 10836125 := bstep (se 3 (by rfl) ⟨2031773, by rfl⟩ : syracuseStep 10836125 = 4063547) B4063547
theorem B2111687 : Blo 1407523 2111687 := bstep (se 1 (by rfl) ⟨1583765, by rfl⟩ : syracuseStep 2111687 = 3167531) B3167531
theorem B3168503 : Blo 1407523 3168503 := bstep (se 1 (by rfl) ⟨2376377, by rfl⟩ : syracuseStep 3168503 = 4752755) B4752755
theorem B2111849 : Blo 1407523 2111849 := bstep (se 2 (by rfl) ⟨791943, by rfl⟩ : syracuseStep 2111849 = 1583887) B1583887
theorem B2111927 : Blo 1407523 2111927 := bstep (se 1 (by rfl) ⟨1583945, by rfl⟩ : syracuseStep 2111927 = 3167891) B3167891
theorem B2537911 : Blo 1407523 2537911 := bstep (se 1 (by rfl) ⟨1903433, by rfl⟩ : syracuseStep 2537911 = 3806867) B3806867
theorem B2111963 : Blo 1407523 2111963 := bstep (se 1 (by rfl) ⟨1583972, by rfl⟩ : syracuseStep 2111963 = 3167945) B3167945
theorem B4012507 : Blo 1407523 4012507 := bstep (se 1 (by rfl) ⟨3009380, by rfl⟩ : syracuseStep 4012507 = 6018761) B6018761
theorem B4012553 : Blo 1407523 4012553 := bstep (se 2 (by rfl) ⟨1504707, by rfl⟩ : syracuseStep 4012553 = 3009415) B3009415
theorem B5708321 : Blo 1407523 5708321 := bstep (se 2 (by rfl) ⟨2140620, by rfl⟩ : syracuseStep 5708321 = 4281241) B4281241
theorem B1407527 : Blo 1407523 1407527 := bstep (se 1 (by rfl) ⟨1055645, by rfl⟩ : syracuseStep 1407527 = 2111291) B2111291
theorem B10689083 : Blo 1407523 10689083 := bstep (se 1 (by rfl) ⟨8016812, by rfl⟩ : syracuseStep 10689083 = 16033625) B16033625
theorem B1407567 : Blo 1407523 1407567 := bstep (se 1 (by rfl) ⟨1055675, by rfl⟩ : syracuseStep 1407567 = 2111351) B2111351
theorem B1407583 : Blo 1407523 1407583 := bstep (se 1 (by rfl) ⟨1055687, by rfl⟩ : syracuseStep 1407583 = 2111375) B2111375
theorem B1407611 : Blo 1407523 1407611 := bstep (se 1 (by rfl) ⟨1055708, by rfl⟩ : syracuseStep 1407611 = 2111417) B2111417
theorem B7133831 : Blo 1407523 7133831 := bstep (se 1 (by rfl) ⟨5350373, by rfl⟩ : syracuseStep 7133831 = 10700747) B10700747
theorem B1407663 : Blo 1407523 1407663 := bstep (se 1 (by rfl) ⟨1055747, by rfl⟩ : syracuseStep 1407663 = 2111495) B2111495
theorem B1407687 : Blo 1407523 1407687 := bstep (se 1 (by rfl) ⟨1055765, by rfl⟩ : syracuseStep 1407687 = 2111531) B2111531
theorem B5348051 : Blo 1407523 5348051 := bstep (se 1 (by rfl) ⟨4011038, by rfl⟩ : syracuseStep 5348051 = 8022077) B8022077
theorem B1407707 : Blo 1407523 1407707 := bstep (se 1 (by rfl) ⟨1055780, by rfl⟩ : syracuseStep 1407707 = 2111561) B2111561
theorem B2169593 : Blo 1407523 2169593 := bstep (se 2 (by rfl) ⟨813597, by rfl⟩ : syracuseStep 2169593 = 1627195) B1627195
theorem B8026883 : Blo 1407523 8026883 := bstep (se 1 (by rfl) ⟨6020162, by rfl⟩ : syracuseStep 8026883 = 12040325) B12040325
theorem B1407783 : Blo 1407523 1407783 := bstep (se 1 (by rfl) ⟨1055837, by rfl⟩ : syracuseStep 1407783 = 2111675) B2111675
theorem B3169097 : Blo 1407523 3169097 := bstep (se 2 (by rfl) ⟨1188411, by rfl⟩ : syracuseStep 3169097 = 2376823) B2376823
theorem B1407823 : Blo 1407523 1407823 := bstep (se 1 (by rfl) ⟨1055867, by rfl⟩ : syracuseStep 1407823 = 2111735) B2111735
theorem B1407839 : Blo 1407523 1407839 := bstep (se 1 (by rfl) ⟨1055879, by rfl⟩ : syracuseStep 1407839 = 2111759) B2111759
theorem B4012895 : Blo 1407523 4012895 := bstep (se 1 (by rfl) ⟨3009671, by rfl⟩ : syracuseStep 4012895 = 6019343) B6019343
theorem B1407867 : Blo 1407523 1407867 := bstep (se 1 (by rfl) ⟨1055900, by rfl⟩ : syracuseStep 1407867 = 2111801) B2111801
theorem B1407919 : Blo 1407523 1407919 := bstep (se 1 (by rfl) ⟨1055939, by rfl⟩ : syracuseStep 1407919 = 2111879) B2111879
theorem B2112431 : Blo 1407523 2112431 := bstep (se 1 (by rfl) ⟨1584323, by rfl⟩ : syracuseStep 2112431 = 3168647) B3168647
theorem B3210167 : Blo 1407523 3210167 := bstep (se 1 (by rfl) ⟨2407625, by rfl⟩ : syracuseStep 3210167 = 4815251) B4815251
theorem B1407943 : Blo 1407523 1407943 := bstep (se 1 (by rfl) ⟨1055957, by rfl⟩ : syracuseStep 1407943 = 2111915) B2111915
theorem B1407963 : Blo 1407523 1407963 := bstep (se 1 (by rfl) ⟨1055972, by rfl⟩ : syracuseStep 1407963 = 2111945) B2111945
theorem B2112521 : Blo 1407523 2112521 := bstep (se 2 (by rfl) ⟨792195, by rfl⟩ : syracuseStep 2112521 = 1584391) B1584391
theorem B1408039 : Blo 1407523 1408039 := bstep (se 1 (by rfl) ⟨1056029, by rfl⟩ : syracuseStep 1408039 = 2112059) B2112059
theorem B2112551 : Blo 1407523 2112551 := bstep (se 1 (by rfl) ⟨1584413, by rfl⟩ : syracuseStep 2112551 = 3168827) B3168827
theorem B1408079 : Blo 1407523 1408079 := bstep (se 1 (by rfl) ⟨1056059, by rfl⟩ : syracuseStep 1408079 = 2112119) B2112119
theorem B4013135 : Blo 1407523 4013135 := bstep (se 1 (by rfl) ⟨3009851, by rfl⟩ : syracuseStep 4013135 = 6019703) B6019703
theorem B1408095 : Blo 1407523 1408095 := bstep (se 1 (by rfl) ⟨1056071, by rfl⟩ : syracuseStep 1408095 = 2112143) B2112143
theorem B1408123 : Blo 1407523 1408123 := bstep (se 1 (by rfl) ⟨1056092, by rfl⟩ : syracuseStep 1408123 = 2112185) B2112185
theorem B2112635 : Blo 1407523 2112635 := bstep (se 1 (by rfl) ⟨1584476, by rfl⟩ : syracuseStep 2112635 = 3168953) B3168953
theorem B1408175 : Blo 1407523 1408175 := bstep (se 1 (by rfl) ⟨1056131, by rfl⟩ : syracuseStep 1408175 = 2112263) B2112263
theorem B1408199 : Blo 1407523 1408199 := bstep (se 1 (by rfl) ⟨1056149, by rfl⟩ : syracuseStep 1408199 = 2112299) B2112299
theorem B1408219 : Blo 1407523 1408219 := bstep (se 1 (by rfl) ⟨1056164, by rfl⟩ : syracuseStep 1408219 = 2112329) B2112329
theorem B8027383 : Blo 1407523 8027383 := bstep (se 1 (by rfl) ⟨6020537, by rfl⟩ : syracuseStep 8027383 = 12041075) B12041075
theorem B2112761 : Blo 1407523 2112761 := bstep (se 2 (by rfl) ⟨792285, by rfl⟩ : syracuseStep 2112761 = 1584571) B1584571
theorem B1408295 : Blo 1407523 1408295 := bstep (se 1 (by rfl) ⟨1056221, by rfl⟩ : syracuseStep 1408295 = 2112443) B2112443
theorem B1408335 : Blo 1407523 1408335 := bstep (se 1 (by rfl) ⟨1056251, by rfl⟩ : syracuseStep 1408335 = 2112503) B2112503
theorem B1408351 : Blo 1407523 1408351 := bstep (se 1 (by rfl) ⟨1056263, by rfl⟩ : syracuseStep 1408351 = 2112527) B2112527
theorem B2112863 : Blo 1407523 2112863 := bstep (se 1 (by rfl) ⟨1584647, by rfl⟩ : syracuseStep 2112863 = 3169295) B3169295
theorem B2112875 : Blo 1407523 2112875 := bstep (se 1 (by rfl) ⟨1584656, by rfl⟩ : syracuseStep 2112875 = 3169313) B3169313
theorem B1408379 : Blo 1407523 1408379 := bstep (se 1 (by rfl) ⟨1056284, by rfl⟩ : syracuseStep 1408379 = 2112569) B2112569
theorem B1408431 : Blo 1407523 1408431 := bstep (se 1 (by rfl) ⟨1056323, by rfl⟩ : syracuseStep 1408431 = 2112647) B2112647
theorem B2538935 : Blo 1407523 2538935 := bstep (se 1 (by rfl) ⟨1904201, by rfl⟩ : syracuseStep 2538935 = 3808403) B3808403
theorem B1408455 : Blo 1407523 1408455 := bstep (se 1 (by rfl) ⟨1056341, by rfl⟩ : syracuseStep 1408455 = 2112683) B2112683
theorem B4750811 : Blo 1407523 4750811 := bstep (se 1 (by rfl) ⟨3563108, by rfl⟩ : syracuseStep 4750811 = 7126217) B7126217
theorem B1408475 : Blo 1407523 1408475 := bstep (se 1 (by rfl) ⟨1056356, by rfl⟩ : syracuseStep 1408475 = 2112713) B2112713
theorem B1408551 : Blo 1407523 1408551 := bstep (se 1 (by rfl) ⟨1056413, by rfl⟩ : syracuseStep 1408551 = 2112827) B2112827
theorem B1408591 : Blo 1407523 1408591 := bstep (se 1 (by rfl) ⟨1056443, by rfl⟩ : syracuseStep 1408591 = 2112887) B2112887
theorem B2113103 : Blo 1407523 2113103 := bstep (se 1 (by rfl) ⟨1584827, by rfl⟩ : syracuseStep 2113103 = 3169655) B3169655
theorem B1408607 : Blo 1407523 1408607 := bstep (se 1 (by rfl) ⟨1056455, by rfl⟩ : syracuseStep 1408607 = 2112911) B2112911
theorem B3169889 : Blo 1407523 3169889 := bstep (se 2 (by rfl) ⟨1188708, by rfl⟩ : syracuseStep 3169889 = 2377417) B2377417
theorem B2375291 : Blo 1407523 2375291 := bstep (se 1 (by rfl) ⟨1781468, by rfl⟩ : syracuseStep 2375291 = 3562937) B3562937
theorem B1408635 : Blo 1407523 1408635 := bstep (se 1 (by rfl) ⟨1056476, by rfl⟩ : syracuseStep 1408635 = 2112953) B2112953
theorem B7618187 : Blo 1407523 7618187 := bstep (se 1 (by rfl) ⟨5713640, by rfl⟩ : syracuseStep 7618187 = 11427281) B11427281
theorem B1408687 : Blo 1407523 1408687 := bstep (se 1 (by rfl) ⟨1056515, by rfl⟩ : syracuseStep 1408687 = 2113031) B2113031
theorem B1408711 : Blo 1407523 1408711 := bstep (se 1 (by rfl) ⟨1056533, by rfl⟩ : syracuseStep 1408711 = 2113067) B2113067
theorem B2113223 : Blo 1407523 2113223 := bstep (se 1 (by rfl) ⟨1584917, by rfl⟩ : syracuseStep 2113223 = 3169835) B3169835
theorem B5709523 : Blo 1407523 5709523 := bstep (se 1 (by rfl) ⟨4282142, by rfl⟩ : syracuseStep 5709523 = 8564285) B8564285
theorem B4013783 : Blo 1407523 4013783 := bstep (se 1 (by rfl) ⟨3010337, by rfl⟩ : syracuseStep 4013783 = 6020675) B6020675
theorem B1408731 : Blo 1407523 1408731 := bstep (se 1 (by rfl) ⟨1056548, by rfl⟩ : syracuseStep 1408731 = 2113097) B2113097
theorem B1408807 : Blo 1407523 1408807 := bstep (se 1 (by rfl) ⟨1056605, by rfl⟩ : syracuseStep 1408807 = 2113211) B2113211
theorem B1408847 : Blo 1407523 1408847 := bstep (se 1 (by rfl) ⟨1056635, by rfl⟩ : syracuseStep 1408847 = 2113271) B2113271
theorem B1408863 : Blo 1407523 1408863 := bstep (se 1 (by rfl) ⟨1056647, by rfl⟩ : syracuseStep 1408863 = 2113295) B2113295
theorem B2113385 : Blo 1407523 2113385 := bstep (se 2 (by rfl) ⟨792519, by rfl⟩ : syracuseStep 2113385 = 1585039) B1585039
theorem B24387443 : Blo 1407523 24387443 := bstep (se 1 (by rfl) ⟨18290582, by rfl⟩ : syracuseStep 24387443 = 36581165) B36581165
theorem B1408891 : Blo 1407523 1408891 := bstep (se 1 (by rfl) ⟨1056668, by rfl⟩ : syracuseStep 1408891 = 2113337) B2113337
theorem B1408943 : Blo 1407523 1408943 := bstep (se 1 (by rfl) ⟨1056707, by rfl⟩ : syracuseStep 1408943 = 2113415) B2113415
theorem B3006391 : Blo 1407523 3006391 := bstep (se 1 (by rfl) ⟨2254793, by rfl⟩ : syracuseStep 3006391 = 4509587) B4509587
theorem B2113463 : Blo 1407523 2113463 := bstep (se 1 (by rfl) ⟨1585097, by rfl⟩ : syracuseStep 2113463 = 3170195) B3170195
theorem B3170231 : Blo 1407523 3170231 := bstep (se 1 (by rfl) ⟨2377673, by rfl⟩ : syracuseStep 3170231 = 4755347) B4755347
theorem B1408967 : Blo 1407523 1408967 := bstep (se 1 (by rfl) ⟨1056725, by rfl⟩ : syracuseStep 1408967 = 2113451) B2113451
theorem B1408987 : Blo 1407523 1408987 := bstep (se 1 (by rfl) ⟨1056740, by rfl⟩ : syracuseStep 1408987 = 2113481) B2113481
theorem B2113499 : Blo 1407523 2113499 := bstep (se 1 (by rfl) ⟨1585124, by rfl⟩ : syracuseStep 2113499 = 3170249) B3170249
theorem B6012953 : Blo 1407523 6012953 := bstep (se 2 (by rfl) ⟨2254857, by rfl⟩ : syracuseStep 6012953 = 4509715) B4509715
theorem B5423129 : Blo 1407523 5423129 := bstep (se 2 (by rfl) ⟨2033673, by rfl⟩ : syracuseStep 5423129 = 4067347) B4067347
theorem B10698803 : Blo 1407523 10698803 := bstep (se 1 (by rfl) ⟨8024102, by rfl⟩ : syracuseStep 10698803 = 16048205) B16048205
theorem B104194225 : Blo 1407523 104194225 := bstep (se 2 (by rfl) ⟨39072834, by rfl⟩ : syracuseStep 104194225 = 78145669) B78145669
theorem B1409311 : Blo 1407523 1409311 := bstep (se 1 (by rfl) ⟨1056983, by rfl⟩ : syracuseStep 1409311 = 2113967) B2113967
theorem B2113883 : Blo 1407523 2113883 := bstep (se 1 (by rfl) ⟨1585412, by rfl⟩ : syracuseStep 2113883 = 3170825) B3170825
theorem B1409371 : Blo 1407523 1409371 := bstep (se 1 (by rfl) ⟨1057028, by rfl⟩ : syracuseStep 1409371 = 2114057) B2114057
theorem B6766955 : Blo 1407523 6766955 := bstep (se 1 (by rfl) ⟨5075216, by rfl⟩ : syracuseStep 6766955 = 10150433) B10150433
theorem B2376047 : Blo 1407523 2376047 := bstep (se 1 (by rfl) ⟨1782035, by rfl⟩ : syracuseStep 2376047 = 3564071) B3564071
theorem B1409391 : Blo 1407523 1409391 := bstep (se 1 (by rfl) ⟨1057043, by rfl⟩ : syracuseStep 1409391 = 2114087) B2114087
theorem B1409447 : Blo 1407523 1409447 := bstep (se 1 (by rfl) ⟨1057085, by rfl⟩ : syracuseStep 1409447 = 2114171) B2114171
theorem B3170735 : Blo 1407523 3170735 := bstep (se 1 (by rfl) ⟨2378051, by rfl⟩ : syracuseStep 3170735 = 4756103) B4756103
theorem B3563959 : Blo 1407523 3563959 := bstep (se 1 (by rfl) ⟨2672969, by rfl⟩ : syracuseStep 3563959 = 5345939) B5345939
theorem B3301843 : Blo 1407523 3301843 := bstep (se 1 (by rfl) ⟨2476382, by rfl⟩ : syracuseStep 3301843 = 4952765) B4952765
theorem B3170771 : Blo 1407523 3170771 := bstep (se 1 (by rfl) ⟨2378078, by rfl⟩ : syracuseStep 3170771 = 4756157) B4756157
theorem B3211771 : Blo 1407523 3211771 := bstep (se 1 (by rfl) ⟨2408828, by rfl⟩ : syracuseStep 3211771 = 4817657) B4817657
theorem B4751891 : Blo 1407523 4751891 := bstep (se 1 (by rfl) ⟨3563918, by rfl⟩ : syracuseStep 4751891 = 7127837) B7127837
theorem B3170879 : Blo 1407523 3170879 := bstep (se 1 (by rfl) ⟨2378159, by rfl⟩ : syracuseStep 3170879 = 4756319) B4756319
theorem B2114111 : Blo 1407523 2114111 := bstep (se 1 (by rfl) ⟨1585583, by rfl⟩ : syracuseStep 2114111 = 3171167) B3171167
theorem B2376263 : Blo 1407523 2376263 := bstep (se 1 (by rfl) ⟨1782197, by rfl⟩ : syracuseStep 2376263 = 3564395) B3564395
theorem B5350009 : Blo 1407523 5350009 := bstep (se 2 (by rfl) ⟨2006253, by rfl⟩ : syracuseStep 5350009 = 4012507) B4012507
theorem B45695623 : Blo 1407523 45695623 := bstep (se 1 (by rfl) ⟨34271717, by rfl⟩ : syracuseStep 45695623 = 68543435) B68543435
theorem B3170987 : Blo 1407523 3170987 := bstep (se 1 (by rfl) ⟨2378240, by rfl⟩ : syracuseStep 3170987 = 4756481) B4756481
theorem B2114231 : Blo 1407523 2114231 := bstep (se 1 (by rfl) ⟨1585673, by rfl⟩ : syracuseStep 2114231 = 3171347) B3171347
theorem B24052625 : Blo 1407523 24052625 := bstep (se 2 (by rfl) ⟨9019734, by rfl⟩ : syracuseStep 24052625 = 18039469) B18039469
theorem B4883431 : Blo 1407523 4883431 := bstep (se 1 (by rfl) ⟨3662573, by rfl⟩ : syracuseStep 4883431 = 7325147) B7325147
theorem B2376695 : Blo 1407523 2376695 := bstep (se 1 (by rfl) ⟨1782521, by rfl⟩ : syracuseStep 2376695 = 3565043) B3565043
theorem B7128161 : Blo 1407523 7128161 := bstep (se 2 (by rfl) ⟨2673060, by rfl⟩ : syracuseStep 7128161 = 5346121) B5346121
theorem B3007775 : Blo 1407523 3007775 := bstep (se 1 (by rfl) ⟨2255831, by rfl⟩ : syracuseStep 3007775 = 4511663) B4511663
theorem B3859751 : Blo 1407523 3859751 := bstep (se 1 (by rfl) ⟨2894813, by rfl⟩ : syracuseStep 3859751 = 5789627) B5789627
theorem B4711841 : Blo 1407523 4711841 := bstep (se 2 (by rfl) ⟨1766940, by rfl⟩ : syracuseStep 4711841 = 3533881) B3533881
theorem B24061373 : Blo 1407523 24061373 := bstep (se 3 (by rfl) ⟨4511507, by rfl⟩ : syracuseStep 24061373 = 9023015) B9023015
theorem B25691681 : Blo 1407523 25691681 := bstep (se 2 (by rfl) ⟨9634380, by rfl⟩ : syracuseStep 25691681 = 19268761) B19268761
theorem B2377451 : Blo 1407523 2377451 := bstep (se 1 (by rfl) ⟨1783088, by rfl⟩ : syracuseStep 2377451 = 3566177) B3566177
theorem B3565367 : Blo 1407523 3565367 := bstep (se 1 (by rfl) ⟨2674025, by rfl⟩ : syracuseStep 3565367 = 5348051) B5348051
theorem B5351255 : Blo 1407523 5351255 := bstep (se 1 (by rfl) ⟨4013441, by rfl⟩ : syracuseStep 5351255 = 8026883) B8026883
theorem B3565417 : Blo 1407523 3565417 := bstep (se 2 (by rfl) ⟨1337031, by rfl⟩ : syracuseStep 3565417 = 2674063) B2674063
theorem B10692485 : Blo 1407523 10692485 := bstep (se 4 (by rfl) ⟨1002420, by rfl⟩ : syracuseStep 10692485 = 2004841) B2004841
theorem B10160005 : Blo 1407523 10160005 := bstep (se 4 (by rfl) ⟨952500, by rfl⟩ : syracuseStep 10160005 = 1905001) B1905001
theorem B2140111 : Blo 1407523 2140111 := bstep (se 1 (by rfl) ⟨1605083, by rfl⟩ : syracuseStep 2140111 = 3210167) B3210167
theorem B3213523 : Blo 1407523 3213523 := bstep (se 1 (by rfl) ⟨2410142, by rfl⟩ : syracuseStep 3213523 = 4820285) B4820285
theorem B4753673 : Blo 1407523 4753673 := bstep (se 2 (by rfl) ⟨1782627, by rfl⟩ : syracuseStep 4753673 = 3565255) B3565255
theorem B7612697 : Blo 1407523 7612697 := bstep (se 2 (by rfl) ⟨2854761, by rfl⟩ : syracuseStep 7612697 = 5709523) B5709523
theorem B13535525 : Blo 1407523 13535525 := bstep (se 4 (by rfl) ⟨1268955, by rfl⟩ : syracuseStep 13535525 = 2537911) B2537911
theorem B15231361 : Blo 1407523 15231361 := bstep (se 2 (by rfl) ⟨5711760, by rfl⟩ : syracuseStep 15231361 = 11423521) B11423521
theorem B1583527 : Blo 1407523 1583527 := bstep (se 1 (by rfl) ⟨1187645, by rfl⟩ : syracuseStep 1583527 = 2375291) B2375291
theorem B4008521 : Blo 1407523 4008521 := bstep (se 2 (by rfl) ⟨1503195, by rfl⟩ : syracuseStep 4008521 = 3006391) B3006391
theorem B2378423 : Blo 1407523 2378423 := bstep (se 1 (by rfl) ⟨1783817, by rfl⟩ : syracuseStep 2378423 = 3567635) B3567635
theorem B20581111 : Blo 1407523 20581111 := bstep (se 1 (by rfl) ⟨15435833, by rfl⟩ : syracuseStep 20581111 = 30871667) B30871667
theorem B1584103 : Blo 1407523 1584103 := bstep (se 1 (by rfl) ⟨1188077, by rfl⟩ : syracuseStep 1584103 = 2376155) B2376155
theorem B3664871 : Blo 1407523 3664871 := bstep (se 1 (by rfl) ⟨2748653, by rfl⟩ : syracuseStep 3664871 = 5497307) B5497307
theorem B3566825 : Blo 1407523 3566825 := bstep (se 2 (by rfl) ⟨1337559, by rfl⟩ : syracuseStep 3566825 = 2675119) B2675119
theorem B7228703 : Blo 1407523 7228703 := bstep (se 1 (by rfl) ⟨5421527, by rfl⟩ : syracuseStep 7228703 = 10843055) B10843055
theorem B7130429 : Blo 1407523 7130429 := bstep (se 3 (by rfl) ⟨1336955, by rfl⟩ : syracuseStep 7130429 = 2673911) B2673911
theorem B4754807 : Blo 1407523 4754807 := bstep (se 1 (by rfl) ⟨3566105, by rfl⟩ : syracuseStep 4754807 = 7132211) B7132211
theorem B5344649 : Blo 1407523 5344649 := bstep (se 2 (by rfl) ⟨2004243, by rfl⟩ : syracuseStep 5344649 = 4008487) B4008487
theorem B3566987 : Blo 1407523 3566987 := bstep (se 1 (by rfl) ⟨2675240, by rfl⟩ : syracuseStep 3566987 = 5350481) B5350481
theorem B8564233 : Blo 1407523 8564233 := bstep (se 2 (by rfl) ⟨3211587, by rfl⟩ : syracuseStep 8564233 = 6423175) B6423175
theorem B3567199 : Blo 1407523 3567199 := bstep (se 1 (by rfl) ⟨2675399, by rfl⟩ : syracuseStep 3567199 = 5350799) B5350799
theorem B25710371 : Blo 1407523 25710371 := bstep (se 1 (by rfl) ⟨19282778, by rfl⟩ : syracuseStep 25710371 = 38565557) B38565557
theorem B3805193 : Blo 1407523 3805193 := bstep (se 2 (by rfl) ⟨1426947, by rfl⟩ : syracuseStep 3805193 = 2853895) B2853895
theorem B3805289 : Blo 1407523 3805289 := bstep (se 2 (by rfl) ⟨1426983, by rfl⟩ : syracuseStep 3805289 = 2853967) B2853967
theorem B3567827 : Blo 1407523 3567827 := bstep (se 1 (by rfl) ⟨2675870, by rfl⟩ : syracuseStep 3567827 = 5351741) B5351741
theorem B10694915 : Blo 1407523 10694915 := bstep (se 1 (by rfl) ⟨8021186, by rfl⟩ : syracuseStep 10694915 = 16042373) B16042373
theorem B10703177 : Blo 1407523 10703177 := bstep (se 2 (by rfl) ⟨4013691, by rfl⟩ : syracuseStep 10703177 = 8027383) B8027383
theorem B2675035 : Blo 1407523 2675035 := bstep (se 1 (by rfl) ⟨2006276, by rfl⟩ : syracuseStep 2675035 = 4012553) B4012553
theorem B3805547 : Blo 1407523 3805547 := bstep (se 1 (by rfl) ⟨2854160, by rfl⟩ : syracuseStep 3805547 = 5708321) B5708321
theorem B4755887 : Blo 1407523 4755887 := bstep (se 1 (by rfl) ⟨3566915, by rfl⟩ : syracuseStep 4755887 = 7133831) B7133831
theorem B39596507 : Blo 1407523 39596507 := bstep (se 1 (by rfl) ⟨29697380, by rfl⟩ : syracuseStep 39596507 = 59394761) B59394761
theorem B1446395 : Blo 1407523 1446395 := bstep (se 1 (by rfl) ⟨1084796, by rfl⟩ : syracuseStep 1446395 = 2169593) B2169593
theorem B2675263 : Blo 1407523 2675263 := bstep (se 1 (by rfl) ⟨2006447, by rfl⟩ : syracuseStep 2675263 = 4012895) B4012895
theorem B2675423 : Blo 1407523 2675423 := bstep (se 1 (by rfl) ⟨2006567, by rfl⟩ : syracuseStep 2675423 = 4013135) B4013135
theorem B1692623 : Blo 1407523 1692623 := bstep (se 1 (by rfl) ⟨1269467, by rfl⟩ : syracuseStep 1692623 = 2538935) B2538935
theorem B12030929 : Blo 1407523 12030929 := bstep (se 2 (by rfl) ⟨4511598, by rfl⟩ : syracuseStep 12030929 = 9023197) B9023197
theorem B3167207 : Blo 1407523 3167207 := bstep (se 1 (by rfl) ⟨2375405, by rfl⟩ : syracuseStep 3167207 = 4750811) B4750811
theorem B2675855 : Blo 1407523 2675855 := bstep (se 1 (by rfl) ⟨2006891, by rfl⟩ : syracuseStep 2675855 = 4013783) B4013783
theorem B16258295 : Blo 1407523 16258295 := bstep (se 1 (by rfl) ⟨12193721, by rfl⟩ : syracuseStep 16258295 = 24387443) B24387443
theorem B12539225 : Blo 1407523 12539225 := bstep (se 2 (by rfl) ⟨4702209, by rfl⟩ : syracuseStep 12539225 = 9404419) B9404419
theorem B3167585 : Blo 1407523 3167585 := bstep (se 2 (by rfl) ⟨1187844, by rfl⟩ : syracuseStep 3167585 = 2375689) B2375689
theorem B7615853 : Blo 1407523 7615853 := bstep (se 3 (by rfl) ⟨1427972, by rfl⟩ : syracuseStep 7615853 = 2855945) B2855945
theorem B4756859 : Blo 1407523 4756859 := bstep (se 1 (by rfl) ⟨3567644, by rfl⟩ : syracuseStep 4756859 = 7135289) B7135289
theorem B4011403 : Blo 1407523 4011403 := bstep (se 1 (by rfl) ⟨3008552, by rfl⟩ : syracuseStep 4011403 = 6017105) B6017105
theorem B3167675 : Blo 1407523 3167675 := bstep (se 1 (by rfl) ⟨2375756, by rfl⟩ : syracuseStep 3167675 = 4751513) B4751513
theorem B1783291 : Blo 1407523 1783291 := bstep (se 1 (by rfl) ⟨1337468, by rfl⟩ : syracuseStep 1783291 = 2674937) B2674937
theorem B3167801 : Blo 1407523 3167801 := bstep (se 2 (by rfl) ⟨1187925, by rfl⟩ : syracuseStep 3167801 = 2375851) B2375851
theorem B20305475 : Blo 1407523 20305475 := bstep (se 1 (by rfl) ⟨15229106, by rfl⟩ : syracuseStep 20305475 = 30458213) B30458213
theorem B4011677 : Blo 1407523 4011677 := bstep (se 3 (by rfl) ⟨752189, by rfl⟩ : syracuseStep 4011677 = 1504379) B1504379
theorem B6018745 : Blo 1407523 6018745 := bstep (se 2 (by rfl) ⟨2257029, by rfl⟩ : syracuseStep 6018745 = 4514059) B4514059
theorem B2537147 : Blo 1407523 2537147 := bstep (se 1 (by rfl) ⟨1902860, by rfl⟩ : syracuseStep 2537147 = 3805721) B3805721
theorem B7132859 : Blo 1407523 7132859 := bstep (se 1 (by rfl) ⟨5349644, by rfl⟩ : syracuseStep 7132859 = 10699289) B10699289
theorem B2537257 : Blo 1407523 2537257 := bstep (se 2 (by rfl) ⟨951471, by rfl⟩ : syracuseStep 2537257 = 1902943) B1902943
theorem B25704307 : Blo 1407523 25704307 := bstep (se 1 (by rfl) ⟨19278230, by rfl⟩ : syracuseStep 25704307 = 38556461) B38556461
theorem B12843143 : Blo 1407523 12843143 := bstep (se 1 (by rfl) ⟨9632357, by rfl⟩ : syracuseStep 12843143 = 19264715) B19264715
theorem B3168467 : Blo 1407523 3168467 := bstep (se 1 (by rfl) ⟨2376350, by rfl⟩ : syracuseStep 3168467 = 4752701) B4752701
theorem B2111753 : Blo 1407523 2111753 := bstep (se 2 (by rfl) ⟨791907, by rfl⟩ : syracuseStep 2111753 = 1583815) B1583815
theorem B3168521 : Blo 1407523 3168521 := bstep (se 2 (by rfl) ⟨1188195, by rfl⟩ : syracuseStep 3168521 = 2376391) B2376391
theorem B2111855 : Blo 1407523 2111855 := bstep (se 1 (by rfl) ⟨1583891, by rfl⟩ : syracuseStep 2111855 = 3167783) B3167783
theorem B2537839 : Blo 1407523 2537839 := bstep (se 1 (by rfl) ⟨1903379, by rfl⟩ : syracuseStep 2537839 = 3806759) B3806759
theorem B3168737 : Blo 1407523 3168737 := bstep (se 2 (by rfl) ⟨1188276, by rfl⟩ : syracuseStep 3168737 = 2376553) B2376553
theorem B1407551 : Blo 1407523 1407551 := bstep (se 1 (by rfl) ⟨1055663, by rfl⟩ : syracuseStep 1407551 = 2111327) B2111327
theorem B1407559 : Blo 1407523 1407559 := bstep (se 1 (by rfl) ⟨1055669, by rfl⟩ : syracuseStep 1407559 = 2111339) B2111339
theorem B2112071 : Blo 1407523 2112071 := bstep (se 1 (by rfl) ⟨1584053, by rfl⟩ : syracuseStep 2112071 = 3168107) B3168107
theorem B4815467 : Blo 1407523 4815467 := bstep (se 1 (by rfl) ⟨3611600, by rfl⟩ : syracuseStep 4815467 = 7223201) B7223201
theorem B2112107 : Blo 1407523 2112107 := bstep (se 1 (by rfl) ⟨1584080, by rfl⟩ : syracuseStep 2112107 = 3168161) B3168161
theorem B4512431 : Blo 1407523 4512431 := bstep (se 1 (by rfl) ⟨3384323, by rfl⟩ : syracuseStep 4512431 = 6768647) B6768647
theorem B1407711 : Blo 1407523 1407711 := bstep (se 1 (by rfl) ⟨1055783, by rfl⟩ : syracuseStep 1407711 = 2111567) B2111567
theorem B7224083 : Blo 1407523 7224083 := bstep (se 1 (by rfl) ⟨5418062, by rfl⟩ : syracuseStep 7224083 = 10836125) B10836125
theorem B3169043 : Blo 1407523 3169043 := bstep (se 1 (by rfl) ⟨2376782, by rfl⟩ : syracuseStep 3169043 = 4753565) B4753565
theorem B1407791 : Blo 1407523 1407791 := bstep (se 1 (by rfl) ⟨1055843, by rfl⟩ : syracuseStep 1407791 = 2111687) B2111687
theorem B38558537 : Blo 1407523 38558537 := bstep (se 2 (by rfl) ⟨14459451, by rfl⟩ : syracuseStep 38558537 = 28918903) B28918903
theorem B2112335 : Blo 1407523 2112335 := bstep (se 1 (by rfl) ⟨1584251, by rfl⟩ : syracuseStep 2112335 = 3168503) B3168503
theorem B1407899 : Blo 1407523 1407899 := bstep (se 1 (by rfl) ⟨1055924, by rfl⟩ : syracuseStep 1407899 = 2111849) B2111849
theorem B6020027 : Blo 1407523 6020027 := bstep (se 1 (by rfl) ⟨4515020, by rfl⟩ : syracuseStep 6020027 = 9030041) B9030041
theorem B1407951 : Blo 1407523 1407951 := bstep (se 1 (by rfl) ⟨1055963, by rfl⟩ : syracuseStep 1407951 = 2111927) B2111927
theorem B3382247 : Blo 1407523 3382247 := bstep (se 1 (by rfl) ⟨2536685, by rfl⟩ : syracuseStep 3382247 = 5073371) B5073371
theorem B1407975 : Blo 1407523 1407975 := bstep (se 1 (by rfl) ⟨1055981, by rfl⟩ : syracuseStep 1407975 = 2111963) B2111963
theorem B5348339 : Blo 1407523 5348339 := bstep (se 1 (by rfl) ⟨4011254, by rfl⟩ : syracuseStep 5348339 = 8022509) B8022509
theorem B7126055 : Blo 1407523 7126055 := bstep (se 1 (by rfl) ⟨5344541, by rfl⟩ : syracuseStep 7126055 = 10689083) B10689083
theorem B3169403 : Blo 1407523 3169403 := bstep (se 1 (by rfl) ⟨2377052, by rfl⟩ : syracuseStep 3169403 = 4754105) B4754105
theorem B65027245 : Blo 1407523 65027245 := bstep (se 3 (by rfl) ⟨12192608, by rfl⟩ : syracuseStep 65027245 = 24385217) B24385217
theorem B2112731 : Blo 1407523 2112731 := bstep (se 1 (by rfl) ⟨1584548, by rfl⟩ : syracuseStep 2112731 = 3169097) B3169097
theorem B3169529 : Blo 1407523 3169529 := bstep (se 2 (by rfl) ⟨1188573, by rfl⟩ : syracuseStep 3169529 = 2377147) B2377147
theorem B1408287 : Blo 1407523 1408287 := bstep (se 1 (by rfl) ⟨1056215, by rfl⟩ : syracuseStep 1408287 = 2112431) B2112431
theorem B2006311 : Blo 1407523 2006311 := bstep (se 1 (by rfl) ⟨1504733, by rfl⟩ : syracuseStep 2006311 = 3009467) B3009467
theorem B1408347 : Blo 1407523 1408347 := bstep (se 1 (by rfl) ⟨1056260, by rfl⟩ : syracuseStep 1408347 = 2112521) B2112521
theorem B1408367 : Blo 1407523 1408367 := bstep (se 1 (by rfl) ⟨1056275, by rfl⟩ : syracuseStep 1408367 = 2112551) B2112551
theorem B3382651 : Blo 1407523 3382651 := bstep (se 1 (by rfl) ⟨2536988, by rfl⟩ : syracuseStep 3382651 = 5073977) B5073977
theorem B2112905 : Blo 1407523 2112905 := bstep (se 2 (by rfl) ⟨792339, by rfl⟩ : syracuseStep 2112905 = 1584679) B1584679
theorem B3169673 : Blo 1407523 3169673 := bstep (se 2 (by rfl) ⟨1188627, by rfl⟩ : syracuseStep 3169673 = 2377255) B2377255
theorem B1408423 : Blo 1407523 1408423 := bstep (se 1 (by rfl) ⟨1056317, by rfl⟩ : syracuseStep 1408423 = 2112635) B2112635
theorem B3562967 : Blo 1407523 3562967 := bstep (se 1 (by rfl) ⟨2672225, by rfl⟩ : syracuseStep 3562967 = 5344451) B5344451
theorem B1408507 : Blo 1407523 1408507 := bstep (se 1 (by rfl) ⟨1056380, by rfl⟩ : syracuseStep 1408507 = 2112761) B2112761
theorem B3169799 : Blo 1407523 3169799 := bstep (se 1 (by rfl) ⟨2377349, by rfl⟩ : syracuseStep 3169799 = 4754699) B4754699
theorem B1408575 : Blo 1407523 1408575 := bstep (se 1 (by rfl) ⟨1056431, by rfl⟩ : syracuseStep 1408575 = 2112863) B2112863
theorem B1408583 : Blo 1407523 1408583 := bstep (se 1 (by rfl) ⟨1056437, by rfl⟩ : syracuseStep 1408583 = 2112875) B2112875
theorem B7134803 : Blo 1407523 7134803 := bstep (se 1 (by rfl) ⟨5351102, by rfl⟩ : syracuseStep 7134803 = 10702205) B10702205
theorem B3169979 : Blo 1407523 3169979 := bstep (se 1 (by rfl) ⟨2377484, by rfl⟩ : syracuseStep 3169979 = 4754969) B4754969
theorem B1408735 : Blo 1407523 1408735 := bstep (se 1 (by rfl) ⟨1056551, by rfl⟩ : syracuseStep 1408735 = 2113103) B2113103
theorem B2113259 : Blo 1407523 2113259 := bstep (se 1 (by rfl) ⟨1584944, by rfl⟩ : syracuseStep 2113259 = 3169889) B3169889
theorem B5078791 : Blo 1407523 5078791 := bstep (se 1 (by rfl) ⟨3809093, by rfl⟩ : syracuseStep 5078791 = 7618187) B7618187
theorem B3563311 : Blo 1407523 3563311 := bstep (se 1 (by rfl) ⟨2672483, by rfl⟩ : syracuseStep 3563311 = 5344967) B5344967
theorem B1408815 : Blo 1407523 1408815 := bstep (se 1 (by rfl) ⟨1056611, by rfl⟩ : syracuseStep 1408815 = 2113223) B2113223
theorem B3170105 : Blo 1407523 3170105 := bstep (se 2 (by rfl) ⟨1188789, by rfl⟩ : syracuseStep 3170105 = 2377579) B2377579
theorem B1408923 : Blo 1407523 1408923 := bstep (se 1 (by rfl) ⟨1056692, by rfl⟩ : syracuseStep 1408923 = 2113385) B2113385
theorem B12033967 : Blo 1407523 12033967 := bstep (se 1 (by rfl) ⟨9025475, by rfl⟩ : syracuseStep 12033967 = 18050951) B18050951
theorem B1408975 : Blo 1407523 1408975 := bstep (se 1 (by rfl) ⟨1056731, by rfl⟩ : syracuseStep 1408975 = 2113463) B2113463
theorem B2113487 : Blo 1407523 2113487 := bstep (se 1 (by rfl) ⟨1585115, by rfl⟩ : syracuseStep 2113487 = 3170231) B3170231
theorem B1408999 : Blo 1407523 1408999 := bstep (se 1 (by rfl) ⟨1056749, by rfl⟩ : syracuseStep 1408999 = 2113499) B2113499
theorem B7135451 : Blo 1407523 7135451 := bstep (se 1 (by rfl) ⟨5351588, by rfl⟩ : syracuseStep 7135451 = 10703177) B10703177
theorem B1409255 : Blo 1407523 1409255 := bstep (se 1 (by rfl) ⟨1056941, by rfl⟩ : syracuseStep 1409255 = 2113883) B2113883
theorem B3170591 : Blo 1407523 3170591 := bstep (se 1 (by rfl) ⟨2377943, by rfl⟩ : syracuseStep 3170591 = 4755887) B4755887
theorem B2113823 : Blo 1407523 2113823 := bstep (se 1 (by rfl) ⟨1585367, by rfl⟩ : syracuseStep 2113823 = 3170735) B3170735
theorem B2113847 : Blo 1407523 2113847 := bstep (se 1 (by rfl) ⟨1585385, by rfl⟩ : syracuseStep 2113847 = 3170771) B3170771
theorem B7135613 : Blo 1407523 7135613 := bstep (se 3 (by rfl) ⟨1337927, by rfl⟩ : syracuseStep 7135613 = 2675855) B2675855
theorem B2113919 : Blo 1407523 2113919 := bstep (se 1 (by rfl) ⟨1585439, by rfl⟩ : syracuseStep 2113919 = 3170879) B3170879
theorem B1409407 : Blo 1407523 1409407 := bstep (se 1 (by rfl) ⟨1057055, by rfl⟩ : syracuseStep 1409407 = 2114111) B2114111
theorem B2113991 : Blo 1407523 2113991 := bstep (se 1 (by rfl) ⟨1585493, by rfl⟩ : syracuseStep 2113991 = 3170987) B3170987
theorem B1409487 : Blo 1407523 1409487 := bstep (se 1 (by rfl) ⟨1057115, by rfl⟩ : syracuseStep 1409487 = 2114231) B2114231
theorem B3383785 : Blo 1407523 3383785 := bstep (se 2 (by rfl) ⟨1268919, by rfl⟩ : syracuseStep 3383785 = 2537839) B2537839
theorem B20308481 : Blo 1407523 20308481 := bstep (se 2 (by rfl) ⟨7615680, by rfl⟩ : syracuseStep 20308481 = 15231361) B15231361
theorem B4751945 : Blo 1407523 4751945 := bstep (se 2 (by rfl) ⟨1781979, by rfl⟩ : syracuseStep 4751945 = 3563959) B3563959
theorem B8020619 : Blo 1407523 8020619 := bstep (se 1 (by rfl) ⟨6015464, by rfl⟩ : syracuseStep 8020619 = 12030929) B12030929
theorem B4752107 : Blo 1407523 4752107 := bstep (se 1 (by rfl) ⟨3564080, by rfl⟩ : syracuseStep 4752107 = 7128161) B7128161
theorem B10838863 : Blo 1407523 10838863 := bstep (se 1 (by rfl) ⟨8129147, by rfl⟩ : syracuseStep 10838863 = 16258295) B16258295
theorem B2573167 : Blo 1407523 2573167 := bstep (se 1 (by rfl) ⟨1929875, by rfl⟩ : syracuseStep 2573167 = 3859751) B3859751
theorem B3171239 : Blo 1407523 3171239 := bstep (se 1 (by rfl) ⟨2378429, by rfl⟩ : syracuseStep 3171239 = 4756859) B4756859
theorem B16040915 : Blo 1407523 16040915 := bstep (se 1 (by rfl) ⟨12030686, by rfl⟩ : syracuseStep 16040915 = 24061373) B24061373
theorem B17138789 : Blo 1407523 17138789 := bstep (se 4 (by rfl) ⟨1606761, by rfl⟩ : syracuseStep 17138789 = 3213523) B3213523
theorem B2376911 : Blo 1407523 2376911 := bstep (se 1 (by rfl) ⟨1782683, by rfl⟩ : syracuseStep 2376911 = 3565367) B3565367
theorem B7128323 : Blo 1407523 7128323 := bstep (se 1 (by rfl) ⟨5346242, by rfl⟩ : syracuseStep 7128323 = 10692485) B10692485
theorem B109765925 : Blo 1407523 109765925 := bstep (se 4 (by rfl) ⟨10290555, by rfl⟩ : syracuseStep 109765925 = 20581111) B20581111
theorem B8562095 : Blo 1407523 8562095 := bstep (se 1 (by rfl) ⟨6421571, by rfl⟩ : syracuseStep 8562095 = 12843143) B12843143
theorem B2672347 : Blo 1407523 2672347 := bstep (se 1 (by rfl) ⟨2004260, by rfl⟩ : syracuseStep 2672347 = 4008521) B4008521
theorem B3008287 : Blo 1407523 3008287 := bstep (se 1 (by rfl) ⟨2256215, by rfl⟩ : syracuseStep 3008287 = 4512431) B4512431
theorem B18040805 : Blo 1407523 18040805 := bstep (se 4 (by rfl) ⟨1691325, by rfl⟩ : syracuseStep 18040805 = 3382651) B3382651
theorem B2443247 : Blo 1407523 2443247 := bstep (se 1 (by rfl) ⟨1832435, by rfl⟩ : syracuseStep 2443247 = 3664871) B3664871
theorem B3565559 : Blo 1407523 3565559 := bstep (se 1 (by rfl) ⟨2674169, by rfl⟩ : syracuseStep 3565559 = 5348339) B5348339
theorem B2377721 : Blo 1407523 2377721 := bstep (se 2 (by rfl) ⟨891645, by rfl⟩ : syracuseStep 2377721 = 1783291) B1783291
theorem B2377883 : Blo 1407523 2377883 := bstep (se 1 (by rfl) ⟨1783412, by rfl⟩ : syracuseStep 2377883 = 3566825) B3566825
theorem B4819135 : Blo 1407523 4819135 := bstep (se 1 (by rfl) ⟨3614351, by rfl⟩ : syracuseStep 4819135 = 7228703) B7228703
theorem B4753619 : Blo 1407523 4753619 := bstep (se 1 (by rfl) ⟨3565214, by rfl⟩ : syracuseStep 4753619 = 7130429) B7130429
theorem B2377991 : Blo 1407523 2377991 := bstep (se 1 (by rfl) ⟨1783493, by rfl⟩ : syracuseStep 2377991 = 3566987) B3566987
theorem B4753889 : Blo 1407523 4753889 := bstep (se 2 (by rfl) ⟨1782708, by rfl⟩ : syracuseStep 4753889 = 3565417) B3565417
theorem B17140247 : Blo 1407523 17140247 := bstep (se 1 (by rfl) ⟨12855185, by rfl⟩ : syracuseStep 17140247 = 25710371) B25710371
theorem B2853481 : Blo 1407523 2853481 := bstep (se 2 (by rfl) ⟨1070055, by rfl⟩ : syracuseStep 2853481 = 2140111) B2140111
theorem B4008635 : Blo 1407523 4008635 := bstep (se 1 (by rfl) ⟨3006476, by rfl⟩ : syracuseStep 4008635 = 6012953) B6012953
theorem B3615419 : Blo 1407523 3615419 := bstep (se 1 (by rfl) ⟨2711564, by rfl⟩ : syracuseStep 3615419 = 5423129) B5423129
theorem B2378551 : Blo 1407523 2378551 := bstep (se 1 (by rfl) ⟨1783913, by rfl⟩ : syracuseStep 2378551 = 3567827) B3567827
theorem B7129943 : Blo 1407523 7129943 := bstep (se 1 (by rfl) ⟨5347457, by rfl⟩ : syracuseStep 7129943 = 10694915) B10694915
theorem B1584031 : Blo 1407523 1584031 := bstep (se 1 (by rfl) ⟨1188023, by rfl⟩ : syracuseStep 1584031 = 2376047) B2376047
theorem B26397671 : Blo 1407523 26397671 := bstep (se 1 (by rfl) ⟨19798253, by rfl⟩ : syracuseStep 26397671 = 39596507) B39596507
theorem B1584175 : Blo 1407523 1584175 := bstep (se 1 (by rfl) ⟨1188131, by rfl⟩ : syracuseStep 1584175 = 2376263) B2376263
theorem B3566713 : Blo 1407523 3566713 := bstep (se 2 (by rfl) ⟨1337517, by rfl⟩ : syracuseStep 3566713 = 2675035) B2675035
theorem B16035083 : Blo 1407523 16035083 := bstep (se 1 (by rfl) ⟨12026312, by rfl⟩ : syracuseStep 16035083 = 24052625) B24052625
theorem B4402457 : Blo 1407523 4402457 := bstep (se 2 (by rfl) ⟨1650921, by rfl⟩ : syracuseStep 4402457 = 3301843) B3301843
theorem B1584463 : Blo 1407523 1584463 := bstep (se 1 (by rfl) ⟨1188347, by rfl⟩ : syracuseStep 1584463 = 2376695) B2376695
theorem B3567017 : Blo 1407523 3567017 := bstep (se 2 (by rfl) ⟨1337631, by rfl⟩ : syracuseStep 3567017 = 2675263) B2675263
theorem B60927497 : Blo 1407523 60927497 := bstep (se 2 (by rfl) ⟨22847811, by rfl⟩ : syracuseStep 60927497 = 45695623) B45695623
theorem B3141227 : Blo 1407523 3141227 := bstep (se 1 (by rfl) ⟨2355920, by rfl⟩ : syracuseStep 3141227 = 4711841) B4711841
theorem B13536983 : Blo 1407523 13536983 := bstep (se 1 (by rfl) ⟨10152737, by rfl⟩ : syracuseStep 13536983 = 20305475) B20305475
theorem B2674451 : Blo 1407523 2674451 := bstep (se 1 (by rfl) ⟨2005838, by rfl⟩ : syracuseStep 2674451 = 4011677) B4011677
theorem B1691431 : Blo 1407523 1691431 := bstep (se 1 (by rfl) ⟨1268573, by rfl⟩ : syracuseStep 1691431 = 2537147) B2537147
theorem B4755239 : Blo 1407523 4755239 := bstep (se 1 (by rfl) ⟨3566429, by rfl⟩ : syracuseStep 4755239 = 7132859) B7132859
theorem B1584967 : Blo 1407523 1584967 := bstep (se 1 (by rfl) ⟨1188725, by rfl⟩ : syracuseStep 1584967 = 2377451) B2377451
theorem B3567503 : Blo 1407523 3567503 := bstep (se 1 (by rfl) ⟨2675627, by rfl⟩ : syracuseStep 3567503 = 5351255) B5351255
theorem B27086885 : Blo 1407523 27086885 := bstep (se 4 (by rfl) ⟨2539395, by rfl⟩ : syracuseStep 27086885 = 5078791) B5078791
theorem B5075131 : Blo 1407523 5075131 := bstep (se 1 (by rfl) ⟨3806348, by rfl⟩ : syracuseStep 5075131 = 7612697) B7612697
theorem B9023683 : Blo 1407523 9023683 := bstep (se 1 (by rfl) ⟨6767762, by rfl⟩ : syracuseStep 9023683 = 13535525) B13535525
theorem B2675081 : Blo 1407523 2675081 := bstep (se 2 (by rfl) ⟨1003155, by rfl⟩ : syracuseStep 2675081 = 2006311) B2006311
theorem B1585615 : Blo 1407523 1585615 := bstep (se 1 (by rfl) ⟨1189211, by rfl⟩ : syracuseStep 1585615 = 2378423) B2378423
theorem B4756265 : Blo 1407523 4756265 := bstep (se 2 (by rfl) ⟨1783599, by rfl⟩ : syracuseStep 4756265 = 3567199) B3567199
theorem B8024993 : Blo 1407523 8024993 := bstep (se 2 (by rfl) ⟨3009372, by rfl⟩ : syracuseStep 8024993 = 6018745) B6018745
theorem B4756535 : Blo 1407523 4756535 := bstep (se 1 (by rfl) ⟨3567401, by rfl⟩ : syracuseStep 4756535 = 7134803) B7134803
theorem B34272409 : Blo 1407523 34272409 := bstep (se 2 (by rfl) ⟨12852153, by rfl⟩ : syracuseStep 34272409 = 25704307) B25704307
theorem B13546673 : Blo 1407523 13546673 := bstep (se 2 (by rfl) ⟨5080002, by rfl⟩ : syracuseStep 13546673 = 10160005) B10160005
theorem B16045289 : Blo 1407523 16045289 := bstep (se 2 (by rfl) ⟨6016983, by rfl⟩ : syracuseStep 16045289 = 12033967) B12033967
theorem B2536795 : Blo 1407523 2536795 := bstep (se 1 (by rfl) ⟨1902596, by rfl⟩ : syracuseStep 2536795 = 3805193) B3805193
theorem B7132535 : Blo 1407523 7132535 := bstep (se 1 (by rfl) ⟨5349401, by rfl⟩ : syracuseStep 7132535 = 10698803) B10698803
theorem B2536859 : Blo 1407523 2536859 := bstep (se 1 (by rfl) ⟨1902644, by rfl⟩ : syracuseStep 2536859 = 3805289) B3805289
theorem B138925633 : Blo 1407523 138925633 := bstep (se 2 (by rfl) ⟨52097112, by rfl⟩ : syracuseStep 138925633 = 104194225) B104194225
theorem B4511303 : Blo 1407523 4511303 := bstep (se 1 (by rfl) ⟨3383477, by rfl⟩ : syracuseStep 4511303 = 6766955) B6766955
theorem B3167927 : Blo 1407523 3167927 := bstep (se 1 (by rfl) ⟨2375945, by rfl⟩ : syracuseStep 3167927 = 4751891) B4751891
theorem B1783615 : Blo 1407523 1783615 := bstep (se 1 (by rfl) ⟨1337711, by rfl⟩ : syracuseStep 1783615 = 2675423) B2675423
theorem B2111369 : Blo 1407523 2111369 := bstep (se 2 (by rfl) ⟨791763, by rfl⟩ : syracuseStep 2111369 = 1583527) B1583527
theorem B2111471 : Blo 1407523 2111471 := bstep (se 1 (by rfl) ⟨1583603, by rfl⟩ : syracuseStep 2111471 = 3167207) B3167207
theorem B4282361 : Blo 1407523 4282361 := bstep (se 2 (by rfl) ⟨1605885, by rfl⟩ : syracuseStep 4282361 = 3211771) B3211771
theorem B7133345 : Blo 1407523 7133345 := bstep (se 2 (by rfl) ⟨2675004, by rfl⟩ : syracuseStep 7133345 = 5350009) B5350009
theorem B2005183 : Blo 1407523 2005183 := bstep (se 1 (by rfl) ⟨1503887, by rfl⟩ : syracuseStep 2005183 = 3007775) B3007775
theorem B2111723 : Blo 1407523 2111723 := bstep (se 1 (by rfl) ⟨1583792, by rfl⟩ : syracuseStep 2111723 = 3167585) B3167585
theorem B33437933 : Blo 1407523 33437933 := bstep (se 3 (by rfl) ⟨6269612, by rfl⟩ : syracuseStep 33437933 = 12539225) B12539225
theorem B5077235 : Blo 1407523 5077235 := bstep (se 1 (by rfl) ⟨3807926, by rfl⟩ : syracuseStep 5077235 = 7615853) B7615853
theorem B10148125 : Blo 1407523 10148125 := bstep (se 3 (by rfl) ⟨1902773, by rfl⟩ : syracuseStep 10148125 = 3805547) B3805547
theorem B2111783 : Blo 1407523 2111783 := bstep (se 1 (by rfl) ⟨1583837, by rfl⟩ : syracuseStep 2111783 = 3167675) B3167675
theorem B17127787 : Blo 1407523 17127787 := bstep (se 1 (by rfl) ⟨12845840, by rfl⟩ : syracuseStep 17127787 = 25691681) B25691681
theorem B2111867 : Blo 1407523 2111867 := bstep (se 1 (by rfl) ⟨1583900, by rfl⟩ : syracuseStep 2111867 = 3167801) B3167801
theorem B2112137 : Blo 1407523 2112137 := bstep (se 2 (by rfl) ⟨792051, by rfl⟩ : syracuseStep 2112137 = 1584103) B1584103
theorem B6511241 : Blo 1407523 6511241 := bstep (se 2 (by rfl) ⟨2441715, by rfl⟩ : syracuseStep 6511241 = 4883431) B4883431
theorem B3857053 : Blo 1407523 3857053 := bstep (se 3 (by rfl) ⟨723197, by rfl⟩ : syracuseStep 3857053 = 1446395) B1446395
theorem B2112311 : Blo 1407523 2112311 := bstep (se 1 (by rfl) ⟨1584233, by rfl⟩ : syracuseStep 2112311 = 3168467) B3168467
theorem B1407835 : Blo 1407523 1407835 := bstep (se 1 (by rfl) ⟨1055876, by rfl⟩ : syracuseStep 1407835 = 2111753) B2111753
theorem B2112347 : Blo 1407523 2112347 := bstep (se 1 (by rfl) ⟨1584260, by rfl⟩ : syracuseStep 2112347 = 3168521) B3168521
theorem B3169115 : Blo 1407523 3169115 := bstep (se 1 (by rfl) ⟨2376836, by rfl⟩ : syracuseStep 3169115 = 4753673) B4753673
theorem B86702993 : Blo 1407523 86702993 := bstep (se 2 (by rfl) ⟨32513622, by rfl⟩ : syracuseStep 86702993 = 65027245) B65027245
theorem B1407903 : Blo 1407523 1407903 := bstep (se 1 (by rfl) ⟨1055927, by rfl⟩ : syracuseStep 1407903 = 2111855) B2111855
theorem B2112491 : Blo 1407523 2112491 := bstep (se 1 (by rfl) ⟨1584368, by rfl⟩ : syracuseStep 2112491 = 3168737) B3168737
theorem B1408047 : Blo 1407523 1408047 := bstep (se 1 (by rfl) ⟨1056035, by rfl⟩ : syracuseStep 1408047 = 2112071) B2112071
theorem B3210311 : Blo 1407523 3210311 := bstep (se 1 (by rfl) ⟨2407733, by rfl⟩ : syracuseStep 3210311 = 4815467) B4815467
theorem B1408071 : Blo 1407523 1408071 := bstep (se 1 (by rfl) ⟨1056053, by rfl⟩ : syracuseStep 1408071 = 2112107) B2112107
theorem B4816055 : Blo 1407523 4816055 := bstep (se 1 (by rfl) ⟨3612041, by rfl⟩ : syracuseStep 4816055 = 7224083) B7224083
theorem B2112695 : Blo 1407523 2112695 := bstep (se 1 (by rfl) ⟨1584521, by rfl⟩ : syracuseStep 2112695 = 3169043) B3169043
theorem B5348537 : Blo 1407523 5348537 := bstep (se 2 (by rfl) ⟨2005701, by rfl⟩ : syracuseStep 5348537 = 4011403) B4011403
theorem B25705691 : Blo 1407523 25705691 := bstep (se 1 (by rfl) ⟨19279268, by rfl⟩ : syracuseStep 25705691 = 38558537) B38558537
theorem B1408223 : Blo 1407523 1408223 := bstep (se 1 (by rfl) ⟨1056167, by rfl⟩ : syracuseStep 1408223 = 2112335) B2112335
theorem B4013351 : Blo 1407523 4013351 := bstep (se 1 (by rfl) ⟨3010013, by rfl⟩ : syracuseStep 4013351 = 6020027) B6020027
theorem B11418977 : Blo 1407523 11418977 := bstep (se 2 (by rfl) ⟨4282116, by rfl⟩ : syracuseStep 11418977 = 8564233) B8564233
theorem B4750703 : Blo 1407523 4750703 := bstep (se 1 (by rfl) ⟨3563027, by rfl⟩ : syracuseStep 4750703 = 7126055) B7126055
theorem B2112935 : Blo 1407523 2112935 := bstep (se 1 (by rfl) ⟨1584701, by rfl⟩ : syracuseStep 2112935 = 3169403) B3169403
theorem B1408487 : Blo 1407523 1408487 := bstep (se 1 (by rfl) ⟨1056365, by rfl⟩ : syracuseStep 1408487 = 2112731) B2112731
theorem B2113019 : Blo 1407523 2113019 := bstep (se 1 (by rfl) ⟨1584764, by rfl⟩ : syracuseStep 2113019 = 3169529) B3169529
theorem B3169871 : Blo 1407523 3169871 := bstep (se 1 (by rfl) ⟨2377403, by rfl⟩ : syracuseStep 3169871 = 4754807) B4754807
theorem B3563099 : Blo 1407523 3563099 := bstep (se 1 (by rfl) ⟨2672324, by rfl⟩ : syracuseStep 3563099 = 5344649) B5344649
theorem B1408603 : Blo 1407523 1408603 := bstep (se 1 (by rfl) ⟨1056452, by rfl⟩ : syracuseStep 1408603 = 2112905) B2112905
theorem B2113115 : Blo 1407523 2113115 := bstep (se 1 (by rfl) ⟨1584836, by rfl⟩ : syracuseStep 2113115 = 3169673) B3169673
theorem B2375311 : Blo 1407523 2375311 := bstep (se 1 (by rfl) ⟨1781483, by rfl⟩ : syracuseStep 2375311 = 3562967) B3562967
theorem B2113199 : Blo 1407523 2113199 := bstep (se 1 (by rfl) ⟨1584899, by rfl⟩ : syracuseStep 2113199 = 3169799) B3169799
theorem B3383009 : Blo 1407523 3383009 := bstep (se 2 (by rfl) ⟨1268628, by rfl⟩ : syracuseStep 3383009 = 2537257) B2537257
theorem B4751081 : Blo 1407523 4751081 := bstep (se 2 (by rfl) ⟨1781655, by rfl⟩ : syracuseStep 4751081 = 3563311) B3563311
theorem B2113319 : Blo 1407523 2113319 := bstep (se 1 (by rfl) ⟨1584989, by rfl⟩ : syracuseStep 2113319 = 3169979) B3169979
theorem B1408839 : Blo 1407523 1408839 := bstep (se 1 (by rfl) ⟨1056629, by rfl⟩ : syracuseStep 1408839 = 2113259) B2113259
theorem B2113403 : Blo 1407523 2113403 := bstep (se 1 (by rfl) ⟨1585052, by rfl⟩ : syracuseStep 2113403 = 3170105) B3170105
theorem B4513661 : Blo 1407523 4513661 := bstep (se 3 (by rfl) ⟨846311, by rfl⟩ : syracuseStep 4513661 = 1692623) B1692623
theorem B9019325 : Blo 1407523 9019325 := bstep (se 3 (by rfl) ⟨1691123, by rfl⟩ : syracuseStep 9019325 = 3382247) B3382247
theorem B1408991 : Blo 1407523 1408991 := bstep (se 1 (by rfl) ⟨1056743, by rfl⟩ : syracuseStep 1408991 = 2113487) B2113487
theorem B8560829 : Blo 1407523 8560829 := bstep (se 3 (by rfl) ⟨1605155, by rfl⟩ : syracuseStep 8560829 = 3210311) B3210311
theorem B2113727 : Blo 1407523 2113727 := bstep (se 1 (by rfl) ⟨1585295, by rfl⟩ : syracuseStep 2113727 = 3170591) B3170591
theorem B1409215 : Blo 1407523 1409215 := bstep (se 1 (by rfl) ⟨1056911, by rfl⟩ : syracuseStep 1409215 = 2113823) B2113823
theorem B1409231 : Blo 1407523 1409231 := bstep (se 1 (by rfl) ⟨1056923, by rfl⟩ : syracuseStep 1409231 = 2113847) B2113847
theorem B6766841 : Blo 1407523 6766841 := bstep (se 2 (by rfl) ⟨2537565, by rfl⟩ : syracuseStep 6766841 = 5075131) B5075131
theorem B1409279 : Blo 1407523 1409279 := bstep (se 1 (by rfl) ⟨1056959, by rfl⟩ : syracuseStep 1409279 = 2113919) B2113919
theorem B1409327 : Blo 1407523 1409327 := bstep (se 1 (by rfl) ⟨1056995, by rfl⟩ : syracuseStep 1409327 = 2113991) B2113991
theorem B3170843 : Blo 1407523 3170843 := bstep (se 1 (by rfl) ⟨2378132, by rfl⟩ : syracuseStep 3170843 = 4756265) B4756265
theorem B2114153 : Blo 1407523 2114153 := bstep (se 2 (by rfl) ⟨792807, by rfl⟩ : syracuseStep 2114153 = 1585615) B1585615
theorem B5349995 : Blo 1407523 5349995 := bstep (se 1 (by rfl) ⟨4012496, by rfl⟩ : syracuseStep 5349995 = 8024993) B8024993
theorem B2114159 : Blo 1407523 2114159 := bstep (se 1 (by rfl) ⟨1585619, by rfl⟩ : syracuseStep 2114159 = 3171239) B3171239
theorem B3171023 : Blo 1407523 3171023 := bstep (se 1 (by rfl) ⟨2378267, by rfl⟩ : syracuseStep 3171023 = 4756535) B4756535
theorem B4752215 : Blo 1407523 4752215 := bstep (se 1 (by rfl) ⟨3564161, by rfl⟩ : syracuseStep 4752215 = 7128323) B7128323
theorem B3007535 : Blo 1407523 3007535 := bstep (se 1 (by rfl) ⟨2255651, by rfl⟩ : syracuseStep 3007535 = 4511303) B4511303
theorem B3171401 : Blo 1407523 3171401 := bstep (se 2 (by rfl) ⟨1189275, by rfl⟩ : syracuseStep 3171401 = 2378551) B2378551
theorem B14451817 : Blo 1407523 14451817 := bstep (se 2 (by rfl) ⟨5419431, by rfl⟩ : syracuseStep 14451817 = 10838863) B10838863
theorem B12027203 : Blo 1407523 12027203 := bstep (se 1 (by rfl) ⟨9020402, by rfl⟩ : syracuseStep 12027203 = 18040805) B18040805
theorem B2377039 : Blo 1407523 2377039 := bstep (se 1 (by rfl) ⟨1782779, by rfl⟩ : syracuseStep 2377039 = 3565559) B3565559
theorem B22291955 : Blo 1407523 22291955 := bstep (se 1 (by rfl) ⟨16718966, by rfl⟩ : syracuseStep 22291955 = 33437933) B33437933
theorem B3384823 : Blo 1407523 3384823 := bstep (se 1 (by rfl) ⟨2538617, by rfl⟩ : syracuseStep 3384823 = 5077235) B5077235
theorem B45696545 : Blo 1407523 45696545 := bstep (se 2 (by rfl) ⟨17136204, by rfl⟩ : syracuseStep 45696545 = 34272409) B34272409
theorem B9020965 : Blo 1407523 9020965 := bstep (se 4 (by rfl) ⟨845715, by rfl⟩ : syracuseStep 9020965 = 1691431) B1691431
theorem B2672423 : Blo 1407523 2672423 := bstep (se 1 (by rfl) ⟨2004317, by rfl⟩ : syracuseStep 2672423 = 4008635) B4008635
theorem B2410279 : Blo 1407523 2410279 := bstep (se 1 (by rfl) ⟨1807709, by rfl⟩ : syracuseStep 2410279 = 3615419) B3615419
theorem B4753295 : Blo 1407523 4753295 := bstep (se 1 (by rfl) ⟨3564971, by rfl⟩ : syracuseStep 4753295 = 7129943) B7129943
theorem B3565691 : Blo 1407523 3565691 := bstep (se 1 (by rfl) ⟨2674268, by rfl⟩ : syracuseStep 3565691 = 5348537) B5348537
theorem B2934971 : Blo 1407523 2934971 := bstep (se 1 (by rfl) ⟨2201228, by rfl⟩ : syracuseStep 2934971 = 4402457) B4402457
theorem B7612651 : Blo 1407523 7612651 := bstep (se 1 (by rfl) ⟨5709488, by rfl⟩ : syracuseStep 7612651 = 11418977) B11418977
theorem B2378011 : Blo 1407523 2378011 := bstep (se 1 (by rfl) ⟨1783508, by rfl⟩ : syracuseStep 2378011 = 3567017) B3567017
theorem B40618331 : Blo 1407523 40618331 := bstep (se 1 (by rfl) ⟨30463748, by rfl⟩ : syracuseStep 40618331 = 60927497) B60927497
theorem B2378153 : Blo 1407523 2378153 := bstep (se 2 (by rfl) ⟨891807, by rfl⟩ : syracuseStep 2378153 = 1783615) B1783615
theorem B2255339 : Blo 1407523 2255339 := bstep (se 1 (by rfl) ⟨1691504, by rfl⟩ : syracuseStep 2255339 = 3383009) B3383009
theorem B3009107 : Blo 1407523 3009107 := bstep (se 1 (by rfl) ⟨2256830, by rfl⟩ : syracuseStep 3009107 = 4513661) B4513661
theorem B2378335 : Blo 1407523 2378335 := bstep (se 1 (by rfl) ⟨1783751, by rfl⟩ : syracuseStep 2378335 = 3567503) B3567503
theorem B18057923 : Blo 1407523 18057923 := bstep (se 1 (by rfl) ⟨13543442, by rfl⟩ : syracuseStep 18057923 = 27086885) B27086885
theorem B2673577 : Blo 1407523 2673577 := bstep (se 2 (by rfl) ⟨1002591, by rfl⟩ : syracuseStep 2673577 = 2005183) B2005183
theorem B6425513 : Blo 1407523 6425513 := bstep (se 2 (by rfl) ⟨2409567, by rfl⟩ : syracuseStep 6425513 = 4819135) B4819135
theorem B10693943 : Blo 1407523 10693943 := bstep (se 1 (by rfl) ⟨8020457, by rfl⟩ : syracuseStep 10693943 = 16040915) B16040915
theorem B9031115 : Blo 1407523 9031115 := bstep (se 1 (by rfl) ⟨6773336, by rfl⟩ : syracuseStep 9031115 = 13546673) B13546673
theorem B1584607 : Blo 1407523 1584607 := bstep (se 1 (by rfl) ⟨1188455, by rfl⟩ : syracuseStep 1584607 = 2376911) B2376911
theorem B3804641 : Blo 1407523 3804641 := bstep (se 2 (by rfl) ⟨1426740, by rfl⟩ : syracuseStep 3804641 = 2853481) B2853481
theorem B4755023 : Blo 1407523 4755023 := bstep (se 1 (by rfl) ⟨3566267, by rfl⟩ : syracuseStep 4755023 = 7132535) B7132535
theorem B2854907 : Blo 1407523 2854907 := bstep (se 1 (by rfl) ⟨2141180, by rfl⟩ : syracuseStep 2854907 = 4282361) B4282361
theorem B1585147 : Blo 1407523 1585147 := bstep (se 1 (by rfl) ⟨1188860, by rfl⟩ : syracuseStep 1585147 = 2377721) B2377721
theorem B1585255 : Blo 1407523 1585255 := bstep (se 1 (by rfl) ⟨1188941, by rfl⟩ : syracuseStep 1585255 = 2377883) B2377883
theorem B4755563 : Blo 1407523 4755563 := bstep (se 1 (by rfl) ⟨3566672, by rfl⟩ : syracuseStep 4755563 = 7133345) B7133345
theorem B4755617 : Blo 1407523 4755617 := bstep (se 2 (by rfl) ⟨1783356, by rfl⟩ : syracuseStep 4755617 = 3566713) B3566713
theorem B1585327 : Blo 1407523 1585327 := bstep (se 1 (by rfl) ⟨1188995, by rfl⟩ : syracuseStep 1585327 = 2377991) B2377991
theorem B8376605 : Blo 1407523 8376605 := bstep (se 3 (by rfl) ⟨1570613, by rfl⟩ : syracuseStep 8376605 = 3141227) B3141227
theorem B36098621 : Blo 1407523 36098621 := bstep (se 3 (by rfl) ⟨6768491, by rfl⟩ : syracuseStep 36098621 = 13536983) B13536983
theorem B185234177 : Blo 1407523 185234177 := bstep (se 2 (by rfl) ⟨69462816, by rfl⟩ : syracuseStep 185234177 = 138925633) B138925633
theorem B3167081 : Blo 1407523 3167081 := bstep (se 2 (by rfl) ⟨1187655, by rfl⟩ : syracuseStep 3167081 = 2375311) B2375311
theorem B2675567 : Blo 1407523 2675567 := bstep (se 1 (by rfl) ⟨2006675, by rfl⟩ : syracuseStep 2675567 = 4013351) B4013351
theorem B3167135 : Blo 1407523 3167135 := bstep (se 1 (by rfl) ⟨2375351, by rfl⟩ : syracuseStep 3167135 = 4750703) B4750703
theorem B4011049 : Blo 1407523 4011049 := bstep (se 2 (by rfl) ⟨1504143, by rfl⟩ : syracuseStep 4011049 = 3008287) B3008287
theorem B3167387 : Blo 1407523 3167387 := bstep (se 1 (by rfl) ⟨2375540, by rfl⟩ : syracuseStep 3167387 = 4751081) B4751081
theorem B1782967 : Blo 1407523 1782967 := bstep (se 1 (by rfl) ⟨1337225, by rfl⟩ : syracuseStep 1782967 = 2674451) B2674451
theorem B4756967 : Blo 1407523 4756967 := bstep (se 1 (by rfl) ⟨3567725, by rfl⟩ : syracuseStep 4756967 = 7135451) B7135451
theorem B4757075 : Blo 1407523 4757075 := bstep (se 1 (by rfl) ⟨3567806, by rfl⟩ : syracuseStep 4757075 = 7135613) B7135613
theorem B12031577 : Blo 1407523 12031577 := bstep (se 2 (by rfl) ⟨4511841, by rfl⟩ : syracuseStep 12031577 = 9023683) B9023683
theorem B1783387 : Blo 1407523 1783387 := bstep (se 1 (by rfl) ⟨1337540, by rfl⟩ : syracuseStep 1783387 = 2675081) B2675081
theorem B13538987 : Blo 1407523 13538987 := bstep (se 1 (by rfl) ⟨10154240, by rfl⟩ : syracuseStep 13538987 = 20308481) B20308481
theorem B13530833 : Blo 1407523 13530833 := bstep (se 2 (by rfl) ⟨5074062, by rfl⟩ : syracuseStep 13530833 = 10148125) B10148125
theorem B3167963 : Blo 1407523 3167963 := bstep (se 1 (by rfl) ⟨2375972, by rfl⟩ : syracuseStep 3167963 = 4751945) B4751945
theorem B5347079 : Blo 1407523 5347079 := bstep (se 1 (by rfl) ⟨4010309, by rfl⟩ : syracuseStep 5347079 = 8020619) B8020619
theorem B22837049 : Blo 1407523 22837049 := bstep (se 2 (by rfl) ⟨8563893, by rfl⟩ : syracuseStep 22837049 = 17127787) B17127787
theorem B12842813 : Blo 1407523 12842813 := bstep (se 3 (by rfl) ⟨2408027, by rfl⟩ : syracuseStep 12842813 = 4816055) B4816055
theorem B3168071 : Blo 1407523 3168071 := bstep (se 1 (by rfl) ⟨2376053, by rfl⟩ : syracuseStep 3168071 = 4752107) B4752107
theorem B4511713 : Blo 1407523 4511713 := bstep (se 2 (by rfl) ⟨1691892, by rfl⟩ : syracuseStep 4511713 = 3383785) B3383785
theorem B11425859 : Blo 1407523 11425859 := bstep (se 1 (by rfl) ⟨8569394, by rfl⟩ : syracuseStep 11425859 = 17138789) B17138789
theorem B10696859 : Blo 1407523 10696859 := bstep (se 1 (by rfl) ⟨8022644, by rfl⟩ : syracuseStep 10696859 = 16045289) B16045289
theorem B73177283 : Blo 1407523 73177283 := bstep (se 1 (by rfl) ⟨54882962, by rfl⟩ : syracuseStep 73177283 = 109765925) B109765925
theorem B5142737 : Blo 1407523 5142737 := bstep (se 2 (by rfl) ⟨1928526, by rfl⟩ : syracuseStep 5142737 = 3857053) B3857053
theorem B5708063 : Blo 1407523 5708063 := bstep (se 1 (by rfl) ⟨4281047, by rfl⟩ : syracuseStep 5708063 = 8562095) B8562095
theorem B6764957 : Blo 1407523 6764957 := bstep (se 3 (by rfl) ⟨1268429, by rfl⟩ : syracuseStep 6764957 = 2536859) B2536859
theorem B2111951 : Blo 1407523 2111951 := bstep (se 1 (by rfl) ⟨1583963, by rfl⟩ : syracuseStep 2111951 = 3167927) B3167927
theorem B3430889 : Blo 1407523 3430889 := bstep (se 2 (by rfl) ⟨1286583, by rfl⟩ : syracuseStep 3430889 = 2573167) B2573167
theorem B2112041 : Blo 1407523 2112041 := bstep (se 2 (by rfl) ⟨792015, by rfl⟩ : syracuseStep 2112041 = 1584031) B1584031
theorem B1407579 : Blo 1407523 1407579 := bstep (se 1 (by rfl) ⟨1055684, by rfl⟩ : syracuseStep 1407579 = 2111369) B2111369
theorem B1407647 : Blo 1407523 1407647 := bstep (se 1 (by rfl) ⟨1055735, by rfl⟩ : syracuseStep 1407647 = 2111471) B2111471
theorem B1628831 : Blo 1407523 1628831 := bstep (se 1 (by rfl) ⟨1221623, by rfl⟩ : syracuseStep 1628831 = 2443247) B2443247
theorem B2112233 : Blo 1407523 2112233 := bstep (se 2 (by rfl) ⟨792087, by rfl⟩ : syracuseStep 2112233 = 1584175) B1584175
theorem B3169079 : Blo 1407523 3169079 := bstep (se 1 (by rfl) ⟨2376809, by rfl⟩ : syracuseStep 3169079 = 4753619) B4753619
theorem B1407815 : Blo 1407523 1407815 := bstep (se 1 (by rfl) ⟨1055861, by rfl⟩ : syracuseStep 1407815 = 2111723) B2111723
theorem B1407855 : Blo 1407523 1407855 := bstep (se 1 (by rfl) ⟨1055891, by rfl⟩ : syracuseStep 1407855 = 2111783) B2111783
theorem B1407911 : Blo 1407523 1407911 := bstep (se 1 (by rfl) ⟨1055933, by rfl⟩ : syracuseStep 1407911 = 2111867) B2111867
theorem B3169259 : Blo 1407523 3169259 := bstep (se 1 (by rfl) ⟨2376944, by rfl⟩ : syracuseStep 3169259 = 4753889) B4753889
theorem B11426831 : Blo 1407523 11426831 := bstep (se 1 (by rfl) ⟨8570123, by rfl⟩ : syracuseStep 11426831 = 17140247) B17140247
theorem B1408091 : Blo 1407523 1408091 := bstep (se 1 (by rfl) ⟨1056068, by rfl⟩ : syracuseStep 1408091 = 2112137) B2112137
theorem B4340827 : Blo 1407523 4340827 := bstep (se 1 (by rfl) ⟨3255620, by rfl⟩ : syracuseStep 4340827 = 6511241) B6511241
theorem B2112617 : Blo 1407523 2112617 := bstep (se 2 (by rfl) ⟨792231, by rfl⟩ : syracuseStep 2112617 = 1584463) B1584463
theorem B3382393 : Blo 1407523 3382393 := bstep (se 2 (by rfl) ⟨1268397, by rfl⟩ : syracuseStep 3382393 = 2536795) B2536795
theorem B1408207 : Blo 1407523 1408207 := bstep (se 1 (by rfl) ⟨1056155, by rfl⟩ : syracuseStep 1408207 = 2112311) B2112311
theorem B1408231 : Blo 1407523 1408231 := bstep (se 1 (by rfl) ⟨1056173, by rfl⟩ : syracuseStep 1408231 = 2112347) B2112347
theorem B2112743 : Blo 1407523 2112743 := bstep (se 1 (by rfl) ⟨1584557, by rfl⟩ : syracuseStep 2112743 = 3169115) B3169115
theorem B57801995 : Blo 1407523 57801995 := bstep (se 1 (by rfl) ⟨43351496, by rfl⟩ : syracuseStep 57801995 = 86702993) B86702993
theorem B1408327 : Blo 1407523 1408327 := bstep (se 1 (by rfl) ⟨1056245, by rfl⟩ : syracuseStep 1408327 = 2112491) B2112491
theorem B1408463 : Blo 1407523 1408463 := bstep (se 1 (by rfl) ⟨1056347, by rfl⟩ : syracuseStep 1408463 = 2112695) B2112695
theorem B17137127 : Blo 1407523 17137127 := bstep (se 1 (by rfl) ⟨12852845, by rfl⟩ : syracuseStep 17137127 = 25705691) B25705691
theorem B10690055 : Blo 1407523 10690055 := bstep (se 1 (by rfl) ⟨8017541, by rfl⟩ : syracuseStep 10690055 = 16035083) B16035083
theorem B1408623 : Blo 1407523 1408623 := bstep (se 1 (by rfl) ⟨1056467, by rfl⟩ : syracuseStep 1408623 = 2112935) B2112935
theorem B3563129 : Blo 1407523 3563129 := bstep (se 2 (by rfl) ⟨1336173, by rfl⟩ : syracuseStep 3563129 = 2672347) B2672347
theorem B1408679 : Blo 1407523 1408679 := bstep (se 1 (by rfl) ⟨1056509, by rfl⟩ : syracuseStep 1408679 = 2113019) B2113019
theorem B2113247 : Blo 1407523 2113247 := bstep (se 1 (by rfl) ⟨1584935, by rfl⟩ : syracuseStep 2113247 = 3169871) B3169871
theorem B2375399 : Blo 1407523 2375399 := bstep (se 1 (by rfl) ⟨1781549, by rfl⟩ : syracuseStep 2375399 = 3563099) B3563099
theorem B1408743 : Blo 1407523 1408743 := bstep (se 1 (by rfl) ⟨1056557, by rfl⟩ : syracuseStep 1408743 = 2113115) B2113115
theorem B2113289 : Blo 1407523 2113289 := bstep (se 2 (by rfl) ⟨792483, by rfl⟩ : syracuseStep 2113289 = 1584967) B1584967
theorem B1408799 : Blo 1407523 1408799 := bstep (se 1 (by rfl) ⟨1056599, by rfl⟩ : syracuseStep 1408799 = 2113199) B2113199
theorem B1408879 : Blo 1407523 1408879 := bstep (se 1 (by rfl) ⟨1056659, by rfl⟩ : syracuseStep 1408879 = 2113319) B2113319
theorem B3170159 : Blo 1407523 3170159 := bstep (se 1 (by rfl) ⟨2377619, by rfl⟩ : syracuseStep 3170159 = 4755239) B4755239
theorem B1408935 : Blo 1407523 1408935 := bstep (se 1 (by rfl) ⟨1056701, by rfl⟩ : syracuseStep 1408935 = 2113403) B2113403
theorem B70393789 : Blo 1407523 70393789 := bstep (se 3 (by rfl) ⟨13198835, by rfl⟩ : syracuseStep 70393789 = 26397671) B26397671
theorem B6012883 : Blo 1407523 6012883 := bstep (se 1 (by rfl) ⟨4509662, by rfl⟩ : syracuseStep 6012883 = 9019325) B9019325
theorem B3170375 : Blo 1407523 3170375 := bstep (se 1 (by rfl) ⟨2377781, by rfl⟩ : syracuseStep 3170375 = 4755563) B4755563
theorem B3170411 : Blo 1407523 3170411 := bstep (se 1 (by rfl) ⟨2377808, by rfl⟩ : syracuseStep 3170411 = 4755617) B4755617
theorem B8020093 : Blo 1407523 8020093 := bstep (se 3 (by rfl) ⟨1503767, by rfl⟩ : syracuseStep 8020093 = 3007535) B3007535
theorem B1409151 : Blo 1407523 1409151 := bstep (se 1 (by rfl) ⟨1056863, by rfl⟩ : syracuseStep 1409151 = 2113727) B2113727
theorem B2113673 : Blo 1407523 2113673 := bstep (se 2 (by rfl) ⟨792627, by rfl⟩ : syracuseStep 2113673 = 1585255) B1585255
theorem B2113769 : Blo 1407523 2113769 := bstep (se 2 (by rfl) ⟨792663, by rfl⟩ : syracuseStep 2113769 = 1585327) B1585327
theorem B10150201 : Blo 1407523 10150201 := bstep (se 2 (by rfl) ⟨3806325, by rfl⟩ : syracuseStep 10150201 = 7612651) B7612651
theorem B2113895 : Blo 1407523 2113895 := bstep (se 1 (by rfl) ⟨1585421, by rfl⟩ : syracuseStep 2113895 = 3170843) B3170843
theorem B3170681 : Blo 1407523 3170681 := bstep (se 2 (by rfl) ⟨1189005, by rfl⟩ : syracuseStep 3170681 = 2378011) B2378011
theorem B1409435 : Blo 1407523 1409435 := bstep (se 1 (by rfl) ⟨1057076, by rfl⟩ : syracuseStep 1409435 = 2114153) B2114153
theorem B1409439 : Blo 1407523 1409439 := bstep (se 1 (by rfl) ⟨1057079, by rfl⟩ : syracuseStep 1409439 = 2114159) B2114159
theorem B2114015 : Blo 1407523 2114015 := bstep (se 1 (by rfl) ⟨1585511, by rfl⟩ : syracuseStep 2114015 = 3171023) B3171023
theorem B2114267 : Blo 1407523 2114267 := bstep (se 1 (by rfl) ⟨1585700, by rfl⟩ : syracuseStep 2114267 = 3171401) B3171401
theorem B3171113 : Blo 1407523 3171113 := bstep (se 2 (by rfl) ⟨1189167, by rfl⟩ : syracuseStep 3171113 = 2378335) B2378335
theorem B3171311 : Blo 1407523 3171311 := bstep (se 1 (by rfl) ⟨2378483, by rfl⟩ : syracuseStep 3171311 = 4756967) B4756967
theorem B14861303 : Blo 1407523 14861303 := bstep (se 1 (by rfl) ⟨11145977, by rfl⟩ : syracuseStep 14861303 = 22291955) B22291955
theorem B3171383 : Blo 1407523 3171383 := bstep (se 1 (by rfl) ⟨2378537, by rfl⟩ : syracuseStep 3171383 = 4757075) B4757075
theorem B8021051 : Blo 1407523 8021051 := bstep (se 1 (by rfl) ⟨6015788, by rfl⟩ : syracuseStep 8021051 = 12031577) B12031577
theorem B9020555 : Blo 1407523 9020555 := bstep (se 1 (by rfl) ⟨6765416, by rfl⟩ : syracuseStep 9020555 = 13530833) B13530833
theorem B3564719 : Blo 1407523 3564719 := bstep (se 1 (by rfl) ⟨2673539, by rfl⟩ : syracuseStep 3564719 = 5347079) B5347079
theorem B8561875 : Blo 1407523 8561875 := bstep (se 1 (by rfl) ⟨6421406, by rfl⟩ : syracuseStep 8561875 = 12842813) B12842813
theorem B3564769 : Blo 1407523 3564769 := bstep (se 2 (by rfl) ⟨1336788, by rfl⟩ : syracuseStep 3564769 = 2673577) B2673577
theorem B2377127 : Blo 1407523 2377127 := bstep (se 1 (by rfl) ⟨1782845, by rfl⟩ : syracuseStep 2377127 = 3565691) B3565691
theorem B48784855 : Blo 1407523 48784855 := bstep (se 1 (by rfl) ⟨36588641, by rfl⟩ : syracuseStep 48784855 = 73177283) B73177283
theorem B19269089 : Blo 1407523 19269089 := bstep (se 2 (by rfl) ⟨7225908, by rfl⟩ : syracuseStep 19269089 = 14451817) B14451817
theorem B12854821 : Blo 1407523 12854821 := bstep (se 4 (by rfl) ⟨1205139, by rfl⟩ : syracuseStep 12854821 = 2410279) B2410279
theorem B2377289 : Blo 1407523 2377289 := bstep (se 2 (by rfl) ⟨891483, by rfl⟩ : syracuseStep 2377289 = 1782967) B1782967
theorem B2287259 : Blo 1407523 2287259 := bstep (se 1 (by rfl) ⟨1715444, by rfl⟩ : syracuseStep 2287259 = 3430889) B3430889
theorem B4343549 : Blo 1407523 4343549 := bstep (se 3 (by rfl) ⟨814415, by rfl⟩ : syracuseStep 4343549 = 1628831) B1628831
theorem B12027953 : Blo 1407523 12027953 := bstep (se 2 (by rfl) ⟨4510482, by rfl⟩ : syracuseStep 12027953 = 9020965) B9020965
theorem B2377849 : Blo 1407523 2377849 := bstep (se 2 (by rfl) ⟨891693, by rfl⟩ : syracuseStep 2377849 = 1783387) B1783387
theorem B7129295 : Blo 1407523 7129295 := bstep (se 1 (by rfl) ⟨5346971, by rfl⟩ : syracuseStep 7129295 = 10693943) B10693943
theorem B1583599 : Blo 1407523 1583599 := bstep (se 1 (by rfl) ⟨1187699, by rfl⟩ : syracuseStep 1583599 = 2375399) B2375399
theorem B93858385 : Blo 1407523 93858385 := bstep (se 2 (by rfl) ⟨35196894, by rfl⟩ : syracuseStep 93858385 = 70393789) B70393789
theorem B6015617 : Blo 1407523 6015617 := bstep (se 2 (by rfl) ⟨2255856, by rfl⟩ : syracuseStep 6015617 = 4511713) B4511713
theorem B1903271 : Blo 1407523 1903271 := bstep (se 1 (by rfl) ⟨1427453, by rfl⟩ : syracuseStep 1903271 = 2854907) B2854907
theorem B3566663 : Blo 1407523 3566663 := bstep (se 1 (by rfl) ⟨2674997, by rfl⟩ : syracuseStep 3566663 = 5349995) B5349995
theorem B123489451 : Blo 1407523 123489451 := bstep (se 1 (by rfl) ⟨92617088, by rfl⟩ : syracuseStep 123489451 = 185234177) B185234177
theorem B1781615 : Blo 1407523 1781615 := bstep (se 1 (by rfl) ⟨1336211, by rfl⟩ : syracuseStep 1781615 = 2672423) B2672423
theorem B15224699 : Blo 1407523 15224699 := bstep (se 1 (by rfl) ⟨11418524, by rfl⟩ : syracuseStep 15224699 = 22837049) B22837049
theorem B45699005 : Blo 1407523 45699005 := bstep (se 3 (by rfl) ⟨8568563, by rfl⟩ : syracuseStep 45699005 = 17137127) B17137127
theorem B7131239 : Blo 1407523 7131239 := bstep (se 1 (by rfl) ⟨5348429, by rfl⟩ : syracuseStep 7131239 = 10696859) B10696859
theorem B5787769 : Blo 1407523 5787769 := bstep (se 2 (by rfl) ⟨2170413, by rfl⟩ : syracuseStep 5787769 = 4340827) B4340827
theorem B3428491 : Blo 1407523 3428491 := bstep (se 1 (by rfl) ⟨2571368, by rfl⟩ : syracuseStep 3428491 = 5142737) B5142737
theorem B4509857 : Blo 1407523 4509857 := bstep (se 2 (by rfl) ⟨1691196, by rfl⟩ : syracuseStep 4509857 = 3382393) B3382393
theorem B3805375 : Blo 1407523 3805375 := bstep (se 1 (by rfl) ⟨2854031, by rfl⟩ : syracuseStep 3805375 = 5708063) B5708063
theorem B8024285 : Blo 1407523 8024285 := bstep (se 3 (by rfl) ⟨1504553, by rfl⟩ : syracuseStep 8024285 = 3009107) B3009107
theorem B27078887 : Blo 1407523 27078887 := bstep (se 1 (by rfl) ⟨20309165, by rfl⟩ : syracuseStep 27078887 = 40618331) B40618331
theorem B4509971 : Blo 1407523 4509971 := bstep (se 1 (by rfl) ⟨3382478, by rfl⟩ : syracuseStep 4509971 = 6764957) B6764957
theorem B1585435 : Blo 1407523 1585435 := bstep (se 1 (by rfl) ⟨1189076, by rfl⟩ : syracuseStep 1585435 = 2378153) B2378153
theorem B1503559 : Blo 1407523 1503559 := bstep (se 1 (by rfl) ⟨1127669, by rfl⟩ : syracuseStep 1503559 = 2255339) B2255339
theorem B12038615 : Blo 1407523 12038615 := bstep (se 1 (by rfl) ⟨9028961, by rfl⟩ : syracuseStep 12038615 = 18057923) B18057923
theorem B31306357 : Blo 1407523 31306357 := bstep (se 5 (by rfl) ⟨1467485, by rfl⟩ : syracuseStep 31306357 = 2934971) B2934971
theorem B2536427 : Blo 1407523 2536427 := bstep (se 1 (by rfl) ⟨1902320, by rfl⟩ : syracuseStep 2536427 = 3804641) B3804641
theorem B8017177 : Blo 1407523 8017177 := bstep (se 2 (by rfl) ⟨3006441, by rfl⟩ : syracuseStep 8017177 = 6012883) B6012883
theorem B4511227 : Blo 1407523 4511227 := bstep (se 1 (by rfl) ⟨3383420, by rfl⟩ : syracuseStep 4511227 = 6766841) B6766841
theorem B5584403 : Blo 1407523 5584403 := bstep (se 1 (by rfl) ⟨4188302, by rfl⟩ : syracuseStep 5584403 = 8376605) B8376605
theorem B24065747 : Blo 1407523 24065747 := bstep (se 1 (by rfl) ⟨18049310, by rfl⟩ : syracuseStep 24065747 = 36098621) B36098621
theorem B22828877 : Blo 1407523 22828877 := bstep (se 3 (by rfl) ⟨4280414, by rfl⟩ : syracuseStep 22828877 = 8560829) B8560829
theorem B3168143 : Blo 1407523 3168143 := bstep (se 1 (by rfl) ⟨2376107, by rfl⟩ : syracuseStep 3168143 = 4752215) B4752215
theorem B2111387 : Blo 1407523 2111387 := bstep (se 1 (by rfl) ⟨1583540, by rfl⟩ : syracuseStep 2111387 = 3167081) B3167081
theorem B1783711 : Blo 1407523 1783711 := bstep (se 1 (by rfl) ⟨1337783, by rfl⟩ : syracuseStep 1783711 = 2675567) B2675567
theorem B2111423 : Blo 1407523 2111423 := bstep (se 1 (by rfl) ⟨1583567, by rfl⟩ : syracuseStep 2111423 = 3167135) B3167135
theorem B2111591 : Blo 1407523 2111591 := bstep (se 1 (by rfl) ⟨1583693, by rfl⟩ : syracuseStep 2111591 = 3167387) B3167387
theorem B8018135 : Blo 1407523 8018135 := bstep (se 1 (by rfl) ⟨6013601, by rfl⟩ : syracuseStep 8018135 = 12027203) B12027203
theorem B30464363 : Blo 1407523 30464363 := bstep (se 1 (by rfl) ⟨22848272, by rfl⟩ : syracuseStep 30464363 = 45696545) B45696545
theorem B9025991 : Blo 1407523 9025991 := bstep (se 1 (by rfl) ⟨6769493, by rfl⟩ : syracuseStep 9025991 = 13538987) B13538987
theorem B2111975 : Blo 1407523 2111975 := bstep (se 1 (by rfl) ⟨1583981, by rfl⟩ : syracuseStep 2111975 = 3167963) B3167963
theorem B2112047 : Blo 1407523 2112047 := bstep (se 1 (by rfl) ⟨1584035, by rfl⟩ : syracuseStep 2112047 = 3168071) B3168071
theorem B3168863 : Blo 1407523 3168863 := bstep (se 1 (by rfl) ⟨2376647, by rfl⟩ : syracuseStep 3168863 = 4753295) B4753295
theorem B7617239 : Blo 1407523 7617239 := bstep (se 1 (by rfl) ⟨5712929, by rfl⟩ : syracuseStep 7617239 = 11425859) B11425859
theorem B5348065 : Blo 1407523 5348065 := bstep (se 2 (by rfl) ⟨2005524, by rfl⟩ : syracuseStep 5348065 = 4011049) B4011049
theorem B1407967 : Blo 1407523 1407967 := bstep (se 1 (by rfl) ⟨1055975, by rfl⟩ : syracuseStep 1407967 = 2111951) B2111951
theorem B1408027 : Blo 1407523 1408027 := bstep (se 1 (by rfl) ⟨1056020, by rfl⟩ : syracuseStep 1408027 = 2112041) B2112041
theorem B3169385 : Blo 1407523 3169385 := bstep (se 2 (by rfl) ⟨1188519, by rfl⟩ : syracuseStep 3169385 = 2377039) B2377039
theorem B1408155 : Blo 1407523 1408155 := bstep (se 1 (by rfl) ⟨1056116, by rfl⟩ : syracuseStep 1408155 = 2112233) B2112233
theorem B2112719 : Blo 1407523 2112719 := bstep (se 1 (by rfl) ⟨1584539, by rfl⟩ : syracuseStep 2112719 = 3169079) B3169079
theorem B4283675 : Blo 1407523 4283675 := bstep (se 1 (by rfl) ⟨3212756, by rfl⟩ : syracuseStep 4283675 = 6425513) B6425513
theorem B2112809 : Blo 1407523 2112809 := bstep (se 2 (by rfl) ⟨792303, by rfl⟩ : syracuseStep 2112809 = 1584607) B1584607
theorem B2112839 : Blo 1407523 2112839 := bstep (se 1 (by rfl) ⟨1584629, by rfl⟩ : syracuseStep 2112839 = 3169259) B3169259
theorem B4513097 : Blo 1407523 4513097 := bstep (se 2 (by rfl) ⟨1692411, by rfl⟩ : syracuseStep 4513097 = 3384823) B3384823
theorem B7617887 : Blo 1407523 7617887 := bstep (se 1 (by rfl) ⟨5713415, by rfl⟩ : syracuseStep 7617887 = 11426831) B11426831
theorem B1408411 : Blo 1407523 1408411 := bstep (se 1 (by rfl) ⟨1056308, by rfl⟩ : syracuseStep 1408411 = 2112617) B2112617
theorem B1408495 : Blo 1407523 1408495 := bstep (se 1 (by rfl) ⟨1056371, by rfl⟩ : syracuseStep 1408495 = 2112743) B2112743
theorem B38534663 : Blo 1407523 38534663 := bstep (se 1 (by rfl) ⟨28900997, by rfl⟩ : syracuseStep 38534663 = 57801995) B57801995
theorem B6020743 : Blo 1407523 6020743 := bstep (se 1 (by rfl) ⟨4515557, by rfl⟩ : syracuseStep 6020743 = 9031115) B9031115
theorem B7126703 : Blo 1407523 7126703 := bstep (se 1 (by rfl) ⟨5345027, by rfl⟩ : syracuseStep 7126703 = 10690055) B10690055
theorem B3170015 : Blo 1407523 3170015 := bstep (se 1 (by rfl) ⟨2377511, by rfl⟩ : syracuseStep 3170015 = 4755023) B4755023
theorem B2375419 : Blo 1407523 2375419 := bstep (se 1 (by rfl) ⟨1781564, by rfl⟩ : syracuseStep 2375419 = 3563129) B3563129
theorem B1408831 : Blo 1407523 1408831 := bstep (se 1 (by rfl) ⟨1056623, by rfl⟩ : syracuseStep 1408831 = 2113247) B2113247
theorem B1408859 : Blo 1407523 1408859 := bstep (se 1 (by rfl) ⟨1056644, by rfl⟩ : syracuseStep 1408859 = 2113289) B2113289
theorem B2113439 : Blo 1407523 2113439 := bstep (se 1 (by rfl) ⟨1585079, by rfl⟩ : syracuseStep 2113439 = 3170159) B3170159
theorem B2113529 : Blo 1407523 2113529 := bstep (se 2 (by rfl) ⟨792573, by rfl⟩ : syracuseStep 2113529 = 1585147) B1585147
theorem B2113583 : Blo 1407523 2113583 := bstep (se 1 (by rfl) ⟨1585187, by rfl⟩ : syracuseStep 2113583 = 3170375) B3170375
theorem B2113607 : Blo 1407523 2113607 := bstep (se 1 (by rfl) ⟨1585205, by rfl⟩ : syracuseStep 2113607 = 3170411) B3170411
theorem B1409115 : Blo 1407523 1409115 := bstep (se 1 (by rfl) ⟨1056836, by rfl⟩ : syracuseStep 1409115 = 2113673) B2113673
theorem B3006571 : Blo 1407523 3006571 := bstep (se 1 (by rfl) ⟨2254928, by rfl⟩ : syracuseStep 3006571 = 4509857) B4509857
theorem B5349523 : Blo 1407523 5349523 := bstep (se 1 (by rfl) ⟨4012142, by rfl⟩ : syracuseStep 5349523 = 8024285) B8024285
theorem B1409179 : Blo 1407523 1409179 := bstep (se 1 (by rfl) ⟨1056884, by rfl⟩ : syracuseStep 1409179 = 2113769) B2113769
theorem B7717025 : Blo 1407523 7717025 := bstep (se 2 (by rfl) ⟨2893884, by rfl⟩ : syracuseStep 7717025 = 5787769) B5787769
theorem B3170465 : Blo 1407523 3170465 := bstep (se 2 (by rfl) ⟨1188924, by rfl⟩ : syracuseStep 3170465 = 2377849) B2377849
theorem B3006647 : Blo 1407523 3006647 := bstep (se 1 (by rfl) ⟨2254985, by rfl⟩ : syracuseStep 3006647 = 4509971) B4509971
theorem B4571321 : Blo 1407523 4571321 := bstep (se 2 (by rfl) ⟨1714245, by rfl⟩ : syracuseStep 4571321 = 3428491) B3428491
theorem B1409263 : Blo 1407523 1409263 := bstep (se 1 (by rfl) ⟨1056947, by rfl⟩ : syracuseStep 1409263 = 2113895) B2113895
theorem B2113787 : Blo 1407523 2113787 := bstep (se 1 (by rfl) ⟨1585340, by rfl⟩ : syracuseStep 2113787 = 3170681) B3170681
theorem B1409343 : Blo 1407523 1409343 := bstep (se 1 (by rfl) ⟨1057007, by rfl⟩ : syracuseStep 1409343 = 2114015) B2114015
theorem B2113913 : Blo 1407523 2113913 := bstep (se 2 (by rfl) ⟨792717, by rfl⟩ : syracuseStep 2113913 = 1585435) B1585435
theorem B13533601 : Blo 1407523 13533601 := bstep (se 2 (by rfl) ⟨5075100, by rfl⟩ : syracuseStep 13533601 = 10150201) B10150201
theorem B1409511 : Blo 1407523 1409511 := bstep (se 1 (by rfl) ⟨1057133, by rfl⟩ : syracuseStep 1409511 = 2114267) B2114267
theorem B2114075 : Blo 1407523 2114075 := bstep (se 1 (by rfl) ⟨1585556, by rfl⟩ : syracuseStep 2114075 = 3171113) B3171113
theorem B2114207 : Blo 1407523 2114207 := bstep (se 1 (by rfl) ⟨1585655, by rfl⟩ : syracuseStep 2114207 = 3171311) B3171311
theorem B2114255 : Blo 1407523 2114255 := bstep (se 1 (by rfl) ⟨1585691, by rfl⟩ : syracuseStep 2114255 = 3171383) B3171383
theorem B6013703 : Blo 1407523 6013703 := bstep (se 1 (by rfl) ⟨4510277, by rfl⟩ : syracuseStep 6013703 = 9020555) B9020555
theorem B2376479 : Blo 1407523 2376479 := bstep (se 1 (by rfl) ⟨1782359, by rfl⟩ : syracuseStep 2376479 = 3564719) B3564719
theorem B12034925 : Blo 1407523 12034925 := bstep (se 3 (by rfl) ⟨2256548, by rfl⟩ : syracuseStep 12034925 = 4513097) B4513097
theorem B12846059 : Blo 1407523 12846059 := bstep (se 1 (by rfl) ⟨9634544, by rfl⟩ : syracuseStep 12846059 = 19269089) B19269089
theorem B1524839 : Blo 1407523 1524839 := bstep (se 1 (by rfl) ⟨1143629, by rfl⟩ : syracuseStep 1524839 = 2287259) B2287259
theorem B4752863 : Blo 1407523 4752863 := bstep (se 1 (by rfl) ⟨3564647, by rfl⟩ : syracuseStep 4752863 = 7129295) B7129295
theorem B164652601 : Blo 1407523 164652601 := bstep (se 2 (by rfl) ⟨61744725, by rfl⟩ : syracuseStep 164652601 = 123489451) B123489451
theorem B20309575 : Blo 1407523 20309575 := bstep (se 1 (by rfl) ⟨15232181, by rfl⟩ : syracuseStep 20309575 = 30464363) B30464363
theorem B4753025 : Blo 1407523 4753025 := bstep (se 2 (by rfl) ⟨1782384, by rfl⟩ : syracuseStep 4753025 = 3564769) B3564769
theorem B65046473 : Blo 1407523 65046473 := bstep (se 2 (by rfl) ⟨24392427, by rfl⟩ : syracuseStep 65046473 = 48784855) B48784855
theorem B6014969 : Blo 1407523 6014969 := bstep (se 2 (by rfl) ⟨2255613, by rfl⟩ : syracuseStep 6014969 = 4511227) B4511227
theorem B2377775 : Blo 1407523 2377775 := bstep (se 1 (by rfl) ⟨1783331, by rfl⟩ : syracuseStep 2377775 = 3566663) B3566663
theorem B17139761 : Blo 1407523 17139761 := bstep (se 2 (by rfl) ⟨6427410, by rfl⟩ : syracuseStep 17139761 = 12854821) B12854821
theorem B8027657 : Blo 1407523 8027657 := bstep (se 2 (by rfl) ⟨3010371, by rfl⟩ : syracuseStep 8027657 = 6020743) B6020743
theorem B2378281 : Blo 1407523 2378281 := bstep (se 2 (by rfl) ⟨891855, by rfl⟩ : syracuseStep 2378281 = 1783711) B1783711
theorem B4754159 : Blo 1407523 4754159 := bstep (se 1 (by rfl) ⟨3565619, by rfl⟩ : syracuseStep 4754159 = 7131239) B7131239
theorem B10693457 : Blo 1407523 10693457 := bstep (se 2 (by rfl) ⟨4010046, by rfl⟩ : syracuseStep 10693457 = 8020093) B8020093
theorem B5073833 : Blo 1407523 5073833 := bstep (se 2 (by rfl) ⟨1902687, by rfl⟩ : syracuseStep 5073833 = 3805375) B3805375
theorem B1690951 : Blo 1407523 1690951 := bstep (se 1 (by rfl) ⟨1268213, by rfl⟩ : syracuseStep 1690951 = 2536427) B2536427
theorem B9907535 : Blo 1407523 9907535 := bstep (se 1 (by rfl) ⟨7430651, by rfl⟩ : syracuseStep 9907535 = 14861303) B14861303
theorem B125144513 : Blo 1407523 125144513 := bstep (se 2 (by rfl) ⟨46929192, by rfl⟩ : syracuseStep 125144513 = 93858385) B93858385
theorem B1584751 : Blo 1407523 1584751 := bstep (se 1 (by rfl) ⟨1188563, by rfl⟩ : syracuseStep 1584751 = 2377127) B2377127
theorem B7130753 : Blo 1407523 7130753 := bstep (se 2 (by rfl) ⟨2674032, by rfl⟩ : syracuseStep 7130753 = 5348065) B5348065
theorem B3722935 : Blo 1407523 3722935 := bstep (se 1 (by rfl) ⟨2792201, by rfl⟩ : syracuseStep 3722935 = 5584403) B5584403
theorem B1584859 : Blo 1407523 1584859 := bstep (se 1 (by rfl) ⟨1188644, by rfl⟩ : syracuseStep 1584859 = 2377289) B2377289
theorem B16043831 : Blo 1407523 16043831 := bstep (se 1 (by rfl) ⟨12032873, by rfl⟩ : syracuseStep 16043831 = 24065747) B24065747
theorem B5345423 : Blo 1407523 5345423 := bstep (se 1 (by rfl) ⟨4009067, by rfl⟩ : syracuseStep 5345423 = 8018135) B8018135
theorem B11415833 : Blo 1407523 11415833 := bstep (se 2 (by rfl) ⟨4280937, by rfl⟩ : syracuseStep 11415833 = 8561875) B8561875
theorem B6017327 : Blo 1407523 6017327 := bstep (se 1 (by rfl) ⟨4512995, by rfl⟩ : syracuseStep 6017327 = 9025991) B9025991
theorem B4010411 : Blo 1407523 4010411 := bstep (se 1 (by rfl) ⟨3007808, by rfl⟩ : syracuseStep 4010411 = 6015617) B6015617
theorem B5075389 : Blo 1407523 5075389 := bstep (se 3 (by rfl) ⟨951635, by rfl⟩ : syracuseStep 5075389 = 1903271) B1903271
theorem B2855783 : Blo 1407523 2855783 := bstep (se 1 (by rfl) ⟨2141837, by rfl⟩ : syracuseStep 2855783 = 4283675) B4283675
theorem B3167225 : Blo 1407523 3167225 := bstep (se 2 (by rfl) ⟨1187709, by rfl⟩ : syracuseStep 3167225 = 2375419) B2375419
theorem B18052591 : Blo 1407523 18052591 := bstep (se 1 (by rfl) ⟨13539443, by rfl⟩ : syracuseStep 18052591 = 27078887) B27078887
theorem B8025743 : Blo 1407523 8025743 := bstep (se 1 (by rfl) ⟨6019307, by rfl⟩ : syracuseStep 8025743 = 12038615) B12038615
theorem B2004745 : Blo 1407523 2004745 := bstep (se 2 (by rfl) ⟨751779, by rfl⟩ : syracuseStep 2004745 = 1503559) B1503559
theorem B166967237 : Blo 1407523 166967237 := bstep (se 4 (by rfl) ⟨15653178, by rfl⟩ : syracuseStep 166967237 = 31306357) B31306357
theorem B2111465 : Blo 1407523 2111465 := bstep (se 2 (by rfl) ⟨791799, by rfl⟩ : syracuseStep 2111465 = 1583599) B1583599
theorem B5347367 : Blo 1407523 5347367 := bstep (se 1 (by rfl) ⟨4010525, by rfl⟩ : syracuseStep 5347367 = 8021051) B8021051
theorem B15219251 : Blo 1407523 15219251 := bstep (se 1 (by rfl) ⟨11414438, by rfl⟩ : syracuseStep 15219251 = 22828877) B22828877
theorem B2112095 : Blo 1407523 2112095 := bstep (se 1 (by rfl) ⟨1584071, by rfl⟩ : syracuseStep 2112095 = 3168143) B3168143
theorem B1407591 : Blo 1407523 1407591 := bstep (se 1 (by rfl) ⟨1055693, by rfl⟩ : syracuseStep 1407591 = 2111387) B2111387
theorem B1407615 : Blo 1407523 1407615 := bstep (se 1 (by rfl) ⟨1055711, by rfl⟩ : syracuseStep 1407615 = 2111423) B2111423
theorem B102759101 : Blo 1407523 102759101 := bstep (se 3 (by rfl) ⟨19267331, by rfl⟩ : syracuseStep 102759101 = 38534663) B38534663
theorem B8018635 : Blo 1407523 8018635 := bstep (se 1 (by rfl) ⟨6013976, by rfl⟩ : syracuseStep 8018635 = 12027953) B12027953
theorem B1407727 : Blo 1407523 1407727 := bstep (se 1 (by rfl) ⟨1055795, by rfl⟩ : syracuseStep 1407727 = 2111591) B2111591
theorem B1407983 : Blo 1407523 1407983 := bstep (se 1 (by rfl) ⟨1055987, by rfl⟩ : syracuseStep 1407983 = 2111975) B2111975
theorem B1408031 : Blo 1407523 1408031 := bstep (se 1 (by rfl) ⟨1056023, by rfl⟩ : syracuseStep 1408031 = 2112047) B2112047
theorem B10689569 : Blo 1407523 10689569 := bstep (se 2 (by rfl) ⟨4008588, by rfl⟩ : syracuseStep 10689569 = 8017177) B8017177
theorem B2112575 : Blo 1407523 2112575 := bstep (se 1 (by rfl) ⟨1584431, by rfl⟩ : syracuseStep 2112575 = 3168863) B3168863
theorem B5078159 : Blo 1407523 5078159 := bstep (se 1 (by rfl) ⟨3808619, by rfl⟩ : syracuseStep 5078159 = 7617239) B7617239
theorem B11582797 : Blo 1407523 11582797 := bstep (se 3 (by rfl) ⟨2171774, by rfl⟩ : syracuseStep 11582797 = 4343549) B4343549
theorem B2112923 : Blo 1407523 2112923 := bstep (se 1 (by rfl) ⟨1584692, by rfl⟩ : syracuseStep 2112923 = 3169385) B3169385
theorem B1408479 : Blo 1407523 1408479 := bstep (se 1 (by rfl) ⟨1056359, by rfl⟩ : syracuseStep 1408479 = 2112719) B2112719
theorem B1408539 : Blo 1407523 1408539 := bstep (se 1 (by rfl) ⟨1056404, by rfl⟩ : syracuseStep 1408539 = 2112809) B2112809
theorem B1408559 : Blo 1407523 1408559 := bstep (se 1 (by rfl) ⟨1056419, by rfl⟩ : syracuseStep 1408559 = 2112839) B2112839
theorem B5078591 : Blo 1407523 5078591 := bstep (se 1 (by rfl) ⟨3808943, by rfl⟩ : syracuseStep 5078591 = 7617887) B7617887
theorem B4750973 : Blo 1407523 4750973 := bstep (se 3 (by rfl) ⟨890807, by rfl⟩ : syracuseStep 4750973 = 1781615) B1781615
theorem B4751135 : Blo 1407523 4751135 := bstep (se 1 (by rfl) ⟨3563351, by rfl⟩ : syracuseStep 4751135 = 7126703) B7126703
theorem B2113343 : Blo 1407523 2113343 := bstep (se 1 (by rfl) ⟨1585007, by rfl⟩ : syracuseStep 2113343 = 3170015) B3170015
theorem B10149799 : Blo 1407523 10149799 := bstep (se 1 (by rfl) ⟨7612349, by rfl⟩ : syracuseStep 10149799 = 15224699) B15224699
theorem B1408959 : Blo 1407523 1408959 := bstep (se 1 (by rfl) ⟨1056719, by rfl⟩ : syracuseStep 1408959 = 2113439) B2113439
theorem B30466003 : Blo 1407523 30466003 := bstep (se 1 (by rfl) ⟨22849502, by rfl⟩ : syracuseStep 30466003 = 45699005) B45699005
theorem B1409019 : Blo 1407523 1409019 := bstep (se 1 (by rfl) ⟨1056764, by rfl⟩ : syracuseStep 1409019 = 2113529) B2113529
theorem B1409055 : Blo 1407523 1409055 := bstep (se 1 (by rfl) ⟨1056791, by rfl⟩ : syracuseStep 1409055 = 2113583) B2113583
theorem B1409071 : Blo 1407523 1409071 := bstep (se 1 (by rfl) ⟨1056803, by rfl⟩ : syracuseStep 1409071 = 2113607) B2113607
theorem B3563615 : Blo 1407523 3563615 := bstep (se 1 (by rfl) ⟨2672711, by rfl⟩ : syracuseStep 3563615 = 5345423) B5345423
theorem B5144683 : Blo 1407523 5144683 := bstep (se 1 (by rfl) ⟨3858512, by rfl⟩ : syracuseStep 5144683 = 7717025) B7717025
theorem B2113643 : Blo 1407523 2113643 := bstep (se 1 (by rfl) ⟨1585232, by rfl⟩ : syracuseStep 2113643 = 3170465) B3170465
theorem B1409191 : Blo 1407523 1409191 := bstep (se 1 (by rfl) ⟨1056893, by rfl⟩ : syracuseStep 1409191 = 2113787) B2113787
theorem B7610555 : Blo 1407523 7610555 := bstep (se 1 (by rfl) ⟨5707916, by rfl⟩ : syracuseStep 7610555 = 11415833) B11415833
theorem B1409275 : Blo 1407523 1409275 := bstep (se 1 (by rfl) ⟨1056956, by rfl⟩ : syracuseStep 1409275 = 2113913) B2113913
theorem B1409383 : Blo 1407523 1409383 := bstep (se 1 (by rfl) ⟨1057037, by rfl⟩ : syracuseStep 1409383 = 2114075) B2114075
theorem B1409471 : Blo 1407523 1409471 := bstep (se 1 (by rfl) ⟨1057103, by rfl⟩ : syracuseStep 1409471 = 2114207) B2114207
theorem B1409503 : Blo 1407523 1409503 := bstep (se 1 (by rfl) ⟨1057127, by rfl⟩ : syracuseStep 1409503 = 2114255) B2114255
theorem B12190189 : Blo 1407523 12190189 := bstep (se 3 (by rfl) ⟨2285660, by rfl⟩ : syracuseStep 12190189 = 4571321) B4571321
theorem B3171041 : Blo 1407523 3171041 := bstep (se 2 (by rfl) ⟨1189140, by rfl⟩ : syracuseStep 3171041 = 2378281) B2378281
theorem B26420093 : Blo 1407523 26420093 := bstep (se 3 (by rfl) ⟨4953767, by rfl⟩ : syracuseStep 26420093 = 9907535) B9907535
theorem B10691513 : Blo 1407523 10691513 := bstep (se 2 (by rfl) ⟨4009317, by rfl⟩ : syracuseStep 10691513 = 8018635) B8018635
theorem B5350495 : Blo 1407523 5350495 := bstep (se 1 (by rfl) ⟨4012871, by rfl⟩ : syracuseStep 5350495 = 8025743) B8025743
theorem B3564911 : Blo 1407523 3564911 := bstep (se 1 (by rfl) ⟨2673683, by rfl⟩ : syracuseStep 3564911 = 5347367) B5347367
theorem B2254601 : Blo 1407523 2254601 := bstep (se 2 (by rfl) ⟨845475, by rfl⟩ : syracuseStep 2254601 = 1690951) B1690951
theorem B15443729 : Blo 1407523 15443729 := bstep (se 2 (by rfl) ⟨5791398, by rfl⟩ : syracuseStep 15443729 = 11582797) B11582797
theorem B7128971 : Blo 1407523 7128971 := bstep (se 1 (by rfl) ⟨5346728, by rfl⟩ : syracuseStep 7128971 = 10693457) B10693457
theorem B24070121 : Blo 1407523 24070121 := bstep (se 2 (by rfl) ⟨9026295, by rfl⟩ : syracuseStep 24070121 = 18052591) B18052591
theorem B3385439 : Blo 1407523 3385439 := bstep (se 1 (by rfl) ⟨2539079, by rfl⟩ : syracuseStep 3385439 = 5078159) B5078159
theorem B83429675 : Blo 1407523 83429675 := bstep (se 1 (by rfl) ⟨62572256, by rfl⟩ : syracuseStep 83429675 = 125144513) B125144513
theorem B27068741 : Blo 1407523 27068741 := bstep (se 4 (by rfl) ⟨2537694, by rfl⟩ : syracuseStep 27068741 = 5075389) B5075389
theorem B5351771 : Blo 1407523 5351771 := bstep (se 1 (by rfl) ⟨4013828, by rfl⟩ : syracuseStep 5351771 = 8027657) B8027657
theorem B2672993 : Blo 1407523 2672993 := bstep (se 2 (by rfl) ⟨1002372, by rfl⟩ : syracuseStep 2672993 = 2004745) B2004745
theorem B3385727 : Blo 1407523 3385727 := bstep (se 1 (by rfl) ⟨2539295, by rfl⟩ : syracuseStep 3385727 = 5078591) B5078591
theorem B4753835 : Blo 1407523 4753835 := bstep (se 1 (by rfl) ⟨3565376, by rfl⟩ : syracuseStep 4753835 = 7130753) B7130753
theorem B445245965 : Blo 1407523 445245965 := bstep (se 3 (by rfl) ⟨83483618, by rfl⟩ : syracuseStep 445245965 = 166967237) B166967237
theorem B4008761 : Blo 1407523 4008761 := bstep (se 2 (by rfl) ⟨1503285, by rfl⟩ : syracuseStep 4008761 = 3006571) B3006571
theorem B4066237 : Blo 1407523 4066237 := bstep (se 3 (by rfl) ⟨762419, by rfl⟩ : syracuseStep 4066237 = 1524839) B1524839
theorem B1584319 : Blo 1407523 1584319 := bstep (se 1 (by rfl) ⟨1188239, by rfl⟩ : syracuseStep 1584319 = 2376479) B2376479
theorem B1903855 : Blo 1407523 1903855 := bstep (se 1 (by rfl) ⟨1427891, by rfl⟩ : syracuseStep 1903855 = 2855783) B2855783
theorem B8023283 : Blo 1407523 8023283 := bstep (se 1 (by rfl) ⟨6017462, by rfl⟩ : syracuseStep 8023283 = 12034925) B12034925
theorem B8564039 : Blo 1407523 8564039 := bstep (se 1 (by rfl) ⟨6423029, by rfl⟩ : syracuseStep 8564039 = 12846059) B12846059
theorem B10694429 : Blo 1407523 10694429 := bstep (se 3 (by rfl) ⟨2005205, by rfl⟩ : syracuseStep 10694429 = 4010411) B4010411
theorem B43364315 : Blo 1407523 43364315 := bstep (se 1 (by rfl) ⟨32523236, by rfl⟩ : syracuseStep 43364315 = 65046473) B65046473
theorem B4009979 : Blo 1407523 4009979 := bstep (se 1 (by rfl) ⟨3007484, by rfl⟩ : syracuseStep 4009979 = 6014969) B6014969
theorem B1585183 : Blo 1407523 1585183 := bstep (se 1 (by rfl) ⟨1188887, by rfl⟩ : syracuseStep 1585183 = 2377775) B2377775
theorem B10146167 : Blo 1407523 10146167 := bstep (se 1 (by rfl) ⟨7609625, by rfl⟩ : syracuseStep 10146167 = 15219251) B15219251
theorem B68506067 : Blo 1407523 68506067 := bstep (se 1 (by rfl) ⟨51379550, by rfl⟩ : syracuseStep 68506067 = 102759101) B102759101
theorem B16036541 : Blo 1407523 16036541 := bstep (se 3 (by rfl) ⟨3006851, by rfl⟩ : syracuseStep 16036541 = 6013703) B6013703
theorem B27079433 : Blo 1407523 27079433 := bstep (se 2 (by rfl) ⟨10154787, by rfl⟩ : syracuseStep 27079433 = 20309575) B20309575
theorem B3167315 : Blo 1407523 3167315 := bstep (se 1 (by rfl) ⟨2375486, by rfl⟩ : syracuseStep 3167315 = 4750973) B4750973
theorem B3167423 : Blo 1407523 3167423 := bstep (se 1 (by rfl) ⟨2375567, by rfl⟩ : syracuseStep 3167423 = 4751135) B4751135
theorem B10695887 : Blo 1407523 10695887 := bstep (se 1 (by rfl) ⟨8021915, by rfl⟩ : syracuseStep 10695887 = 16043831) B16043831
theorem B40621337 : Blo 1407523 40621337 := bstep (se 2 (by rfl) ⟨15233001, by rfl⟩ : syracuseStep 40621337 = 30466003) B30466003
theorem B2004431 : Blo 1407523 2004431 := bstep (se 1 (by rfl) ⟨1503323, by rfl⟩ : syracuseStep 2004431 = 3006647) B3006647
theorem B7132697 : Blo 1407523 7132697 := bstep (se 2 (by rfl) ⟨2674761, by rfl⟩ : syracuseStep 7132697 = 5349523) B5349523
theorem B4011551 : Blo 1407523 4011551 := bstep (se 1 (by rfl) ⟨3008663, by rfl⟩ : syracuseStep 4011551 = 6017327) B6017327
theorem B18044801 : Blo 1407523 18044801 := bstep (se 2 (by rfl) ⟨6766800, by rfl⟩ : syracuseStep 18044801 = 13533601) B13533601
theorem B2111483 : Blo 1407523 2111483 := bstep (se 1 (by rfl) ⟨1583612, by rfl⟩ : syracuseStep 2111483 = 3167225) B3167225
theorem B3168575 : Blo 1407523 3168575 := bstep (se 1 (by rfl) ⟨2376431, by rfl⟩ : syracuseStep 3168575 = 4752863) B4752863
theorem B3168683 : Blo 1407523 3168683 := bstep (se 1 (by rfl) ⟨2376512, by rfl⟩ : syracuseStep 3168683 = 4753025) B4753025
theorem B1407643 : Blo 1407523 1407643 := bstep (se 1 (by rfl) ⟨1055732, by rfl⟩ : syracuseStep 1407643 = 2111465) B2111465
theorem B11426507 : Blo 1407523 11426507 := bstep (se 1 (by rfl) ⟨8569880, by rfl⟩ : syracuseStep 11426507 = 17139761) B17139761
theorem B1408063 : Blo 1407523 1408063 := bstep (se 1 (by rfl) ⟨1056047, by rfl⟩ : syracuseStep 1408063 = 2112095) B2112095
theorem B3169439 : Blo 1407523 3169439 := bstep (se 1 (by rfl) ⟨2377079, by rfl⟩ : syracuseStep 3169439 = 4754159) B4754159
theorem B3382555 : Blo 1407523 3382555 := bstep (se 1 (by rfl) ⟨2536916, by rfl⟩ : syracuseStep 3382555 = 5073833) B5073833
theorem B7126379 : Blo 1407523 7126379 := bstep (se 1 (by rfl) ⟨5344784, by rfl⟩ : syracuseStep 7126379 = 10689569) B10689569
theorem B1408383 : Blo 1407523 1408383 := bstep (se 1 (by rfl) ⟨1056287, by rfl⟩ : syracuseStep 1408383 = 2112575) B2112575
theorem B219536801 : Blo 1407523 219536801 := bstep (se 2 (by rfl) ⟨82326300, by rfl⟩ : syracuseStep 219536801 = 164652601) B164652601
theorem B2113001 : Blo 1407523 2113001 := bstep (se 2 (by rfl) ⟨792375, by rfl⟩ : syracuseStep 2113001 = 1584751) B1584751
theorem B4963913 : Blo 1407523 4963913 := bstep (se 2 (by rfl) ⟨1861467, by rfl⟩ : syracuseStep 4963913 = 3722935) B3722935
theorem B1408615 : Blo 1407523 1408615 := bstep (se 1 (by rfl) ⟨1056461, by rfl⟩ : syracuseStep 1408615 = 2112923) B2112923
theorem B2113145 : Blo 1407523 2113145 := bstep (se 2 (by rfl) ⟨792429, by rfl⟩ : syracuseStep 2113145 = 1584859) B1584859
theorem B1408895 : Blo 1407523 1408895 := bstep (se 1 (by rfl) ⟨1056671, by rfl⟩ : syracuseStep 1408895 = 2113343) B2113343
theorem B13533065 : Blo 1407523 13533065 := bstep (se 2 (by rfl) ⟨5074899, by rfl⟩ : syracuseStep 13533065 = 10149799) B10149799
theorem B2113577 : Blo 1407523 2113577 := bstep (se 2 (by rfl) ⟨792591, by rfl⟩ : syracuseStep 2113577 = 1585183) B1585183
theorem B2375743 : Blo 1407523 2375743 := bstep (se 1 (by rfl) ⟨1781807, by rfl⟩ : syracuseStep 2375743 = 3563615) B3563615
theorem B1409095 : Blo 1407523 1409095 := bstep (se 1 (by rfl) ⟨1056821, by rfl⟩ : syracuseStep 1409095 = 2113643) B2113643
theorem B45670711 : Blo 1407523 45670711 := bstep (se 1 (by rfl) ⟨34253033, by rfl⟩ : syracuseStep 45670711 = 68506067) B68506067
theorem B10691027 : Blo 1407523 10691027 := bstep (se 1 (by rfl) ⟨8018270, by rfl⟩ : syracuseStep 10691027 = 16036541) B16036541
theorem B2114027 : Blo 1407523 2114027 := bstep (se 1 (by rfl) ⟨1585520, by rfl⟩ : syracuseStep 2114027 = 3171041) B3171041
theorem B17613395 : Blo 1407523 17613395 := bstep (se 1 (by rfl) ⟨13210046, by rfl⟩ : syracuseStep 17613395 = 26420093) B26420093
theorem B7127675 : Blo 1407523 7127675 := bstep (se 1 (by rfl) ⟨5345756, by rfl⟩ : syracuseStep 7127675 = 10691513) B10691513
theorem B16253585 : Blo 1407523 16253585 := bstep (se 2 (by rfl) ⟨6095094, by rfl⟩ : syracuseStep 16253585 = 12190189) B12190189
theorem B2376607 : Blo 1407523 2376607 := bstep (se 1 (by rfl) ⟨1782455, by rfl⟩ : syracuseStep 2376607 = 3564911) B3564911
theorem B4752647 : Blo 1407523 4752647 := bstep (se 1 (by rfl) ⟨3564485, by rfl⟩ : syracuseStep 4752647 = 7128971) B7128971
theorem B2672507 : Blo 1407523 2672507 := bstep (se 1 (by rfl) ⟨2004380, by rfl⟩ : syracuseStep 2672507 = 4008761) B4008761
theorem B7129619 : Blo 1407523 7129619 := bstep (se 1 (by rfl) ⟨5347214, by rfl⟩ : syracuseStep 7129619 = 10694429) B10694429
theorem B9022043 : Blo 1407523 9022043 := bstep (se 1 (by rfl) ⟨6766532, by rfl⟩ : syracuseStep 9022043 = 13533065) B13533065
theorem B2673319 : Blo 1407523 2673319 := bstep (se 1 (by rfl) ⟨2004989, by rfl⟩ : syracuseStep 2673319 = 4009979) B4009979
theorem B6859577 : Blo 1407523 6859577 := bstep (se 2 (by rfl) ⟨2572341, by rfl⟩ : syracuseStep 6859577 = 5144683) B5144683
theorem B20294813 : Blo 1407523 20294813 := bstep (se 3 (by rfl) ⟨3805277, by rfl⟩ : syracuseStep 20294813 = 7610555) B7610555
theorem B18997161173 : Blo 1407523 18997161173 := bstep (se 7 (by rfl) ⟨222622982, by rfl⟩ : syracuseStep 18997161173 = 445245965) B445245965
theorem B7130591 : Blo 1407523 7130591 := bstep (se 1 (by rfl) ⟨5347943, by rfl⟩ : syracuseStep 7130591 = 10695887) B10695887
theorem B4755131 : Blo 1407523 4755131 := bstep (se 1 (by rfl) ⟨3566348, by rfl⟩ : syracuseStep 4755131 = 7132697) B7132697
theorem B2674367 : Blo 1407523 2674367 := bstep (se 1 (by rfl) ⟨2005775, by rfl⟩ : syracuseStep 2674367 = 4011551) B4011551
theorem B5345149 : Blo 1407523 5345149 := bstep (se 3 (by rfl) ⟨1002215, by rfl⟩ : syracuseStep 5345149 = 2004431) B2004431
theorem B12029867 : Blo 1407523 12029867 := bstep (se 1 (by rfl) ⟨9022400, by rfl⟩ : syracuseStep 12029867 = 18044801) B18044801
theorem B2256959 : Blo 1407523 2256959 := bstep (se 1 (by rfl) ⟨1692719, by rfl⟩ : syracuseStep 2256959 = 3385439) B3385439
theorem B55619783 : Blo 1407523 55619783 := bstep (se 1 (by rfl) ⟨41714837, by rfl⟩ : syracuseStep 55619783 = 83429675) B83429675
theorem B3567847 : Blo 1407523 3567847 := bstep (se 1 (by rfl) ⟨2675885, by rfl⟩ : syracuseStep 3567847 = 5351771) B5351771
theorem B1781995 : Blo 1407523 1781995 := bstep (se 1 (by rfl) ⟨1336496, by rfl⟩ : syracuseStep 1781995 = 2672993) B2672993
theorem B2257151 : Blo 1407523 2257151 := bstep (se 1 (by rfl) ⟨1692863, by rfl⟩ : syracuseStep 2257151 = 3385727) B3385727
theorem B4510073 : Blo 1407523 4510073 := bstep (se 2 (by rfl) ⟨1691277, by rfl⟩ : syracuseStep 4510073 = 3382555) B3382555
theorem B6764111 : Blo 1407523 6764111 := bstep (se 1 (by rfl) ⟨5073083, by rfl⟩ : syracuseStep 6764111 = 10146167) B10146167
theorem B18052955 : Blo 1407523 18052955 := bstep (se 1 (by rfl) ⟨13539716, by rfl⟩ : syracuseStep 18052955 = 27079433) B27079433
theorem B2111543 : Blo 1407523 2111543 := bstep (se 1 (by rfl) ⟨1583657, by rfl⟩ : syracuseStep 2111543 = 3167315) B3167315
theorem B2111615 : Blo 1407523 2111615 := bstep (se 1 (by rfl) ⟨1583711, by rfl⟩ : syracuseStep 2111615 = 3167423) B3167423
theorem B27080891 : Blo 1407523 27080891 := bstep (se 1 (by rfl) ⟨20310668, by rfl⟩ : syracuseStep 27080891 = 40621337) B40621337
theorem B10295819 : Blo 1407523 10295819 := bstep (se 1 (by rfl) ⟨7721864, by rfl⟩ : syracuseStep 10295819 = 15443729) B15443729
theorem B5421649 : Blo 1407523 5421649 := bstep (se 2 (by rfl) ⟨2033118, by rfl⟩ : syracuseStep 5421649 = 4066237) B4066237
theorem B16046747 : Blo 1407523 16046747 := bstep (se 1 (by rfl) ⟨12035060, by rfl⟩ : syracuseStep 16046747 = 24070121) B24070121
theorem B1407655 : Blo 1407523 1407655 := bstep (se 1 (by rfl) ⟨1055741, by rfl⟩ : syracuseStep 1407655 = 2111483) B2111483
theorem B7133993 : Blo 1407523 7133993 := bstep (se 2 (by rfl) ⟨2675247, by rfl⟩ : syracuseStep 7133993 = 5350495) B5350495
theorem B2112383 : Blo 1407523 2112383 := bstep (se 1 (by rfl) ⟨1584287, by rfl⟩ : syracuseStep 2112383 = 3168575) B3168575
theorem B18045827 : Blo 1407523 18045827 := bstep (se 1 (by rfl) ⟨13534370, by rfl⟩ : syracuseStep 18045827 = 27068741) B27068741
theorem B2112425 : Blo 1407523 2112425 := bstep (se 2 (by rfl) ⟨792159, by rfl⟩ : syracuseStep 2112425 = 1584319) B1584319
theorem B2112455 : Blo 1407523 2112455 := bstep (se 1 (by rfl) ⟨1584341, by rfl⟩ : syracuseStep 2112455 = 3168683) B3168683
theorem B3169223 : Blo 1407523 3169223 := bstep (se 1 (by rfl) ⟨2376917, by rfl⟩ : syracuseStep 3169223 = 4753835) B4753835
theorem B2538473 : Blo 1407523 2538473 := bstep (se 2 (by rfl) ⟨951927, by rfl⟩ : syracuseStep 2538473 = 1903855) B1903855
theorem B7617671 : Blo 1407523 7617671 := bstep (se 1 (by rfl) ⟨5713253, by rfl⟩ : syracuseStep 7617671 = 11426507) B11426507
theorem B6012269 : Blo 1407523 6012269 := bstep (se 3 (by rfl) ⟨1127300, by rfl⟩ : syracuseStep 6012269 = 2254601) B2254601
theorem B2112959 : Blo 1407523 2112959 := bstep (se 1 (by rfl) ⟨1584719, by rfl⟩ : syracuseStep 2112959 = 3169439) B3169439
theorem B5348855 : Blo 1407523 5348855 := bstep (se 1 (by rfl) ⟨4011641, by rfl⟩ : syracuseStep 5348855 = 8023283) B8023283
theorem B5709359 : Blo 1407523 5709359 := bstep (se 1 (by rfl) ⟨4282019, by rfl⟩ : syracuseStep 5709359 = 8564039) B8564039
theorem B4750919 : Blo 1407523 4750919 := bstep (se 1 (by rfl) ⟨3563189, by rfl⟩ : syracuseStep 4750919 = 7126379) B7126379
theorem B146357867 : Blo 1407523 146357867 := bstep (se 1 (by rfl) ⟨109768400, by rfl⟩ : syracuseStep 146357867 = 219536801) B219536801
theorem B1408667 : Blo 1407523 1408667 := bstep (se 1 (by rfl) ⟨1056500, by rfl⟩ : syracuseStep 1408667 = 2113001) B2113001
theorem B3309275 : Blo 1407523 3309275 := bstep (se 1 (by rfl) ⟨2481956, by rfl⟩ : syracuseStep 3309275 = 4963913) B4963913
theorem B1408763 : Blo 1407523 1408763 := bstep (se 1 (by rfl) ⟨1056572, by rfl⟩ : syracuseStep 1408763 = 2113145) B2113145
theorem B28909543 : Blo 1407523 28909543 := bstep (se 1 (by rfl) ⟨21682157, by rfl⟩ : syracuseStep 28909543 = 43364315) B43364315
theorem B1409051 : Blo 1407523 1409051 := bstep (se 1 (by rfl) ⟨1056788, by rfl⟩ : syracuseStep 1409051 = 2113577) B2113577
theorem B3006715 : Blo 1407523 3006715 := bstep (se 1 (by rfl) ⟨2255036, by rfl⟩ : syracuseStep 3006715 = 4510073) B4510073
theorem B7127351 : Blo 1407523 7127351 := bstep (se 1 (by rfl) ⟨5345513, by rfl⟩ : syracuseStep 7127351 = 10691027) B10691027
theorem B2375993 : Blo 1407523 2375993 := bstep (se 2 (by rfl) ⟨890997, by rfl⟩ : syracuseStep 2375993 = 1781995) B1781995
theorem B1409351 : Blo 1407523 1409351 := bstep (se 1 (by rfl) ⟨1057013, by rfl⟩ : syracuseStep 1409351 = 2114027) B2114027
theorem B4751783 : Blo 1407523 4751783 := bstep (se 1 (by rfl) ⟨3563837, by rfl⟩ : syracuseStep 4751783 = 7127675) B7127675
theorem B3564425 : Blo 1407523 3564425 := bstep (se 2 (by rfl) ⟨1336659, by rfl⟩ : syracuseStep 3564425 = 2673319) B2673319
theorem B12035303 : Blo 1407523 12035303 := bstep (se 1 (by rfl) ⟨9026477, by rfl⟩ : syracuseStep 12035303 = 18052955) B18052955
theorem B4753079 : Blo 1407523 4753079 := bstep (se 1 (by rfl) ⟨3564809, by rfl⟩ : syracuseStep 4753079 = 7129619) B7129619
theorem B6014695 : Blo 1407523 6014695 := bstep (se 1 (by rfl) ⟨4511021, by rfl⟩ : syracuseStep 6014695 = 9022043) B9022043
theorem B8824733 : Blo 1407523 8824733 := bstep (se 3 (by rfl) ⟨1654637, by rfl⟩ : syracuseStep 8824733 = 3309275) B3309275
theorem B4008179 : Blo 1407523 4008179 := bstep (se 1 (by rfl) ⟨3006134, by rfl⟩ : syracuseStep 4008179 = 6012269) B6012269
theorem B4753727 : Blo 1407523 4753727 := bstep (se 1 (by rfl) ⟨3565295, by rfl⟩ : syracuseStep 4753727 = 7130591) B7130591
theorem B3565903 : Blo 1407523 3565903 := bstep (se 1 (by rfl) ⟨2674427, by rfl⟩ : syracuseStep 3565903 = 5348855) B5348855
theorem B6769261 : Blo 1407523 6769261 := bstep (se 3 (by rfl) ⟨1269236, by rfl⟩ : syracuseStep 6769261 = 2538473) B2538473
theorem B38546057 : Blo 1407523 38546057 := bstep (se 2 (by rfl) ⟨14454771, by rfl⟩ : syracuseStep 38546057 = 28909543) B28909543
theorem B37079855 : Blo 1407523 37079855 := bstep (se 1 (by rfl) ⟨27809891, by rfl⟩ : syracuseStep 37079855 = 55619783) B55619783
theorem B11742263 : Blo 1407523 11742263 := bstep (se 1 (by rfl) ⟨8806697, by rfl⟩ : syracuseStep 11742263 = 17613395) B17613395
theorem B60894281 : Blo 1407523 60894281 := bstep (se 2 (by rfl) ⟨22835355, by rfl⟩ : syracuseStep 60894281 = 45670711) B45670711
theorem B7228865 : Blo 1407523 7228865 := bstep (se 2 (by rfl) ⟨2710824, by rfl⟩ : syracuseStep 7228865 = 5421649) B5421649
theorem B4509407 : Blo 1407523 4509407 := bstep (se 1 (by rfl) ⟨3382055, by rfl⟩ : syracuseStep 4509407 = 6764111) B6764111
theorem B1781671 : Blo 1407523 1781671 := bstep (se 1 (by rfl) ⟨1336253, by rfl⟩ : syracuseStep 1781671 = 2672507) B2672507
theorem B390287645 : Blo 1407523 390287645 := bstep (se 3 (by rfl) ⟨73178933, by rfl⟩ : syracuseStep 390287645 = 146357867) B146357867
theorem B4755995 : Blo 1407523 4755995 := bstep (se 1 (by rfl) ⟨3566996, by rfl⟩ : syracuseStep 4755995 = 7133993) B7133993
theorem B12030551 : Blo 1407523 12030551 := bstep (se 1 (by rfl) ⟨9022913, by rfl⟩ : syracuseStep 12030551 = 18045827) B18045827
theorem B13529875 : Blo 1407523 13529875 := bstep (se 1 (by rfl) ⟨10147406, by rfl⟩ : syracuseStep 13529875 = 20294813) B20294813
theorem B3806239 : Blo 1407523 3806239 := bstep (se 1 (by rfl) ⟨2854679, by rfl⟩ : syracuseStep 3806239 = 5709359) B5709359
theorem B3167279 : Blo 1407523 3167279 := bstep (se 1 (by rfl) ⟨2375459, by rfl⟩ : syracuseStep 3167279 = 4750919) B4750919
theorem B1782911 : Blo 1407523 1782911 := bstep (se 1 (by rfl) ⟨1337183, by rfl⟩ : syracuseStep 1782911 = 2674367) B2674367
theorem B1504639 : Blo 1407523 1504639 := bstep (se 1 (by rfl) ⟨1128479, by rfl⟩ : syracuseStep 1504639 = 2256959) B2256959
theorem B3167657 : Blo 1407523 3167657 := bstep (se 2 (by rfl) ⟨1187871, by rfl⟩ : syracuseStep 3167657 = 2375743) B2375743
theorem B4757129 : Blo 1407523 4757129 := bstep (se 2 (by rfl) ⟨1783923, by rfl⟩ : syracuseStep 4757129 = 3567847) B3567847
theorem B10835723 : Blo 1407523 10835723 := bstep (se 1 (by rfl) ⟨8126792, by rfl⟩ : syracuseStep 10835723 = 16253585) B16253585
theorem B6019069 : Blo 1407523 6019069 := bstep (se 3 (by rfl) ⟨1128575, by rfl⟩ : syracuseStep 6019069 = 2257151) B2257151
theorem B3168431 : Blo 1407523 3168431 := bstep (se 1 (by rfl) ⟨2376323, by rfl⟩ : syracuseStep 3168431 = 4752647) B4752647
theorem B3168809 : Blo 1407523 3168809 := bstep (se 2 (by rfl) ⟨1188303, by rfl⟩ : syracuseStep 3168809 = 2376607) B2376607
theorem B1407695 : Blo 1407523 1407695 := bstep (se 1 (by rfl) ⟨1055771, by rfl⟩ : syracuseStep 1407695 = 2111543) B2111543
theorem B1407743 : Blo 1407523 1407743 := bstep (se 1 (by rfl) ⟨1055807, by rfl⟩ : syracuseStep 1407743 = 2111615) B2111615
theorem B18053927 : Blo 1407523 18053927 := bstep (se 1 (by rfl) ⟨13540445, by rfl⟩ : syracuseStep 18053927 = 27080891) B27080891
theorem B6863879 : Blo 1407523 6863879 := bstep (se 1 (by rfl) ⟨5147909, by rfl⟩ : syracuseStep 6863879 = 10295819) B10295819
theorem B10697831 : Blo 1407523 10697831 := bstep (se 1 (by rfl) ⟨8023373, by rfl⟩ : syracuseStep 10697831 = 16046747) B16046747
theorem B1408255 : Blo 1407523 1408255 := bstep (se 1 (by rfl) ⟨1056191, by rfl⟩ : syracuseStep 1408255 = 2112383) B2112383
theorem B1408283 : Blo 1407523 1408283 := bstep (se 1 (by rfl) ⟨1056212, by rfl⟩ : syracuseStep 1408283 = 2112425) B2112425
theorem B1408303 : Blo 1407523 1408303 := bstep (se 1 (by rfl) ⟨1056227, by rfl⟩ : syracuseStep 1408303 = 2112455) B2112455
theorem B2112815 : Blo 1407523 2112815 := bstep (se 1 (by rfl) ⟨1584611, by rfl⟩ : syracuseStep 2112815 = 3169223) B3169223
theorem B5078447 : Blo 1407523 5078447 := bstep (se 1 (by rfl) ⟨3808835, by rfl⟩ : syracuseStep 5078447 = 7617671) B7617671
theorem B12664774115 : Blo 1407523 12664774115 := bstep (se 1 (by rfl) ⟨9498580586, by rfl⟩ : syracuseStep 12664774115 = 18997161173) B18997161173
theorem B18292205 : Blo 1407523 18292205 := bstep (se 3 (by rfl) ⟨3429788, by rfl⟩ : syracuseStep 18292205 = 6859577) B6859577
theorem B1408639 : Blo 1407523 1408639 := bstep (se 1 (by rfl) ⟨1056479, by rfl⟩ : syracuseStep 1408639 = 2112959) B2112959
theorem B3170087 : Blo 1407523 3170087 := bstep (se 1 (by rfl) ⟨2377565, by rfl⟩ : syracuseStep 3170087 = 4755131) B4755131
theorem B7126865 : Blo 1407523 7126865 := bstep (se 2 (by rfl) ⟨2672574, by rfl⟩ : syracuseStep 7126865 = 5345149) B5345149
theorem B8019911 : Blo 1407523 8019911 := bstep (se 1 (by rfl) ⟨6014933, by rfl⟩ : syracuseStep 8019911 = 12029867) B12029867
theorem B4751567 : Blo 1407523 4751567 := bstep (se 1 (by rfl) ⟨3563675, by rfl⟩ : syracuseStep 4751567 = 7127351) B7127351
theorem B3170663 : Blo 1407523 3170663 := bstep (se 1 (by rfl) ⟨2377997, by rfl⟩ : syracuseStep 3170663 = 4755995) B4755995
theorem B8020367 : Blo 1407523 8020367 := bstep (se 1 (by rfl) ⟨6015275, by rfl⟩ : syracuseStep 8020367 = 12030551) B12030551
theorem B2376283 : Blo 1407523 2376283 := bstep (se 1 (by rfl) ⟨1782212, by rfl⟩ : syracuseStep 2376283 = 3564425) B3564425
theorem B18039833 : Blo 1407523 18039833 := bstep (se 2 (by rfl) ⟨6764937, by rfl⟩ : syracuseStep 18039833 = 13529875) B13529875
theorem B3171419 : Blo 1407523 3171419 := bstep (se 1 (by rfl) ⟨2378564, by rfl⟩ : syracuseStep 3171419 = 4757129) B4757129
theorem B5883155 : Blo 1407523 5883155 := bstep (se 1 (by rfl) ⟨4412366, by rfl⟩ : syracuseStep 5883155 = 8824733) B8824733
theorem B2672119 : Blo 1407523 2672119 := bstep (se 1 (by rfl) ⟨2004089, by rfl⟩ : syracuseStep 2672119 = 4008179) B4008179
theorem B12035951 : Blo 1407523 12035951 := bstep (se 1 (by rfl) ⟨9026963, by rfl⟩ : syracuseStep 12035951 = 18053927) B18053927
theorem B3385631 : Blo 1407523 3385631 := bstep (se 1 (by rfl) ⟨2539223, by rfl⟩ : syracuseStep 3385631 = 5078447) B5078447
theorem B4819243 : Blo 1407523 4819243 := bstep (se 1 (by rfl) ⟨3614432, by rfl⟩ : syracuseStep 4819243 = 7228865) B7228865
theorem B18303677 : Blo 1407523 18303677 := bstep (se 3 (by rfl) ⟨3431939, by rfl⟩ : syracuseStep 18303677 = 6863879) B6863879
theorem B1583995 : Blo 1407523 1583995 := bstep (se 1 (by rfl) ⟨1187996, by rfl⟩ : syracuseStep 1583995 = 2375993) B2375993
theorem B4008953 : Blo 1407523 4008953 := bstep (se 2 (by rfl) ⟨1503357, by rfl⟩ : syracuseStep 4008953 = 3006715) B3006715
theorem B4754429 : Blo 1407523 4754429 := bstep (se 3 (by rfl) ⟨891455, by rfl⟩ : syracuseStep 4754429 = 1782911) B1782911
theorem B4754537 : Blo 1407523 4754537 := bstep (se 2 (by rfl) ⟨1782951, by rfl⟩ : syracuseStep 4754537 = 3565903) B3565903
theorem B8023535 : Blo 1407523 8023535 := bstep (se 1 (by rfl) ⟨6017651, by rfl⟩ : syracuseStep 8023535 = 12035303) B12035303
theorem B5074985 : Blo 1407523 5074985 := bstep (se 2 (by rfl) ⟨1903119, by rfl⟩ : syracuseStep 5074985 = 3806239) B3806239
theorem B24719903 : Blo 1407523 24719903 := bstep (se 1 (by rfl) ⟨18539927, by rfl⟩ : syracuseStep 24719903 = 37079855) B37079855
theorem B8024741 : Blo 1407523 8024741 := bstep (se 4 (by rfl) ⟨752319, by rfl⟩ : syracuseStep 8024741 = 1504639) B1504639
theorem B7828175 : Blo 1407523 7828175 := bstep (se 1 (by rfl) ⟨5871131, by rfl⟩ : syracuseStep 7828175 = 11742263) B11742263
theorem B40596187 : Blo 1407523 40596187 := bstep (se 1 (by rfl) ⟨30447140, by rfl⟩ : syracuseStep 40596187 = 60894281) B60894281
theorem B7131887 : Blo 1407523 7131887 := bstep (se 1 (by rfl) ⟨5348915, by rfl⟩ : syracuseStep 7131887 = 10697831) B10697831
theorem B12194803 : Blo 1407523 12194803 := bstep (se 1 (by rfl) ⟨9146102, by rfl⟩ : syracuseStep 12194803 = 18292205) B18292205
theorem B5346607 : Blo 1407523 5346607 := bstep (se 1 (by rfl) ⟨4009955, by rfl⟩ : syracuseStep 5346607 = 8019911) B8019911
theorem B8025425 : Blo 1407523 8025425 := bstep (se 2 (by rfl) ⟨3009534, by rfl⟩ : syracuseStep 8025425 = 6019069) B6019069
theorem B260191763 : Blo 1407523 260191763 := bstep (se 1 (by rfl) ⟨195143822, by rfl⟩ : syracuseStep 260191763 = 390287645) B390287645
theorem B3167855 : Blo 1407523 3167855 := bstep (se 1 (by rfl) ⟨2375891, by rfl⟩ : syracuseStep 3167855 = 4751783) B4751783
theorem B2111519 : Blo 1407523 2111519 := bstep (se 1 (by rfl) ⟨1583639, by rfl⟩ : syracuseStep 2111519 = 3167279) B3167279
theorem B9025681 : Blo 1407523 9025681 := bstep (se 2 (by rfl) ⟨3384630, by rfl⟩ : syracuseStep 9025681 = 6769261) B6769261
theorem B2111771 : Blo 1407523 2111771 := bstep (se 1 (by rfl) ⟨1583828, by rfl⟩ : syracuseStep 2111771 = 3167657) B3167657
theorem B3168719 : Blo 1407523 3168719 := bstep (se 1 (by rfl) ⟨2376539, by rfl⟩ : syracuseStep 3168719 = 4753079) B4753079
theorem B7223815 : Blo 1407523 7223815 := bstep (se 1 (by rfl) ⟨5417861, by rfl⟩ : syracuseStep 7223815 = 10835723) B10835723
theorem B2112287 : Blo 1407523 2112287 := bstep (se 1 (by rfl) ⟨1584215, by rfl⟩ : syracuseStep 2112287 = 3168431) B3168431
theorem B3169151 : Blo 1407523 3169151 := bstep (se 1 (by rfl) ⟨2376863, by rfl⟩ : syracuseStep 3169151 = 4753727) B4753727
theorem B2112539 : Blo 1407523 2112539 := bstep (se 1 (by rfl) ⟨1584404, by rfl⟩ : syracuseStep 2112539 = 3168809) B3168809
theorem B25697371 : Blo 1407523 25697371 := bstep (se 1 (by rfl) ⟨19273028, by rfl⟩ : syracuseStep 25697371 = 38546057) B38546057
theorem B1408543 : Blo 1407523 1408543 := bstep (se 1 (by rfl) ⟨1056407, by rfl⟩ : syracuseStep 1408543 = 2112815) B2112815
theorem B8019593 : Blo 1407523 8019593 := bstep (se 2 (by rfl) ⟨3007347, by rfl⟩ : syracuseStep 8019593 = 6014695) B6014695
theorem B8443182743 : Blo 1407523 8443182743 := bstep (se 1 (by rfl) ⟨6332387057, by rfl⟩ : syracuseStep 8443182743 = 12664774115) B12664774115
theorem B3006271 : Blo 1407523 3006271 := bstep (se 1 (by rfl) ⟨2254703, by rfl⟩ : syracuseStep 3006271 = 4509407) B4509407
theorem B2113391 : Blo 1407523 2113391 := bstep (se 1 (by rfl) ⟨1585043, by rfl⟩ : syracuseStep 2113391 = 3170087) B3170087
theorem B2375561 : Blo 1407523 2375561 := bstep (se 2 (by rfl) ⟨890835, by rfl⟩ : syracuseStep 2375561 = 1781671) B1781671
theorem B4751243 : Blo 1407523 4751243 := bstep (se 1 (by rfl) ⟨3563432, by rfl⟩ : syracuseStep 4751243 = 7126865) B7126865
theorem B13533293 : Blo 1407523 13533293 := bstep (se 3 (by rfl) ⟨2537492, by rfl⟩ : syracuseStep 13533293 = 5074985) B5074985
theorem B12034241 : Blo 1407523 12034241 := bstep (se 2 (by rfl) ⟨4512840, by rfl⟩ : syracuseStep 12034241 = 9025681) B9025681
theorem B2113775 : Blo 1407523 2113775 := bstep (se 1 (by rfl) ⟨1585331, by rfl⟩ : syracuseStep 2113775 = 3170663) B3170663
theorem B5349827 : Blo 1407523 5349827 := bstep (se 1 (by rfl) ⟨4012370, by rfl⟩ : syracuseStep 5349827 = 8024741) B8024741
theorem B12026555 : Blo 1407523 12026555 := bstep (se 1 (by rfl) ⟨9019916, by rfl⟩ : syracuseStep 12026555 = 18039833) B18039833
theorem B2114279 : Blo 1407523 2114279 := bstep (se 1 (by rfl) ⟨1585709, by rfl⟩ : syracuseStep 2114279 = 3171419) B3171419
theorem B5350283 : Blo 1407523 5350283 := bstep (se 1 (by rfl) ⟨4012712, by rfl⟩ : syracuseStep 5350283 = 8025425) B8025425
theorem B7128809 : Blo 1407523 7128809 := bstep (se 2 (by rfl) ⟨2673303, by rfl⟩ : syracuseStep 7128809 = 5346607) B5346607
theorem B20875133 : Blo 1407523 20875133 := bstep (se 3 (by rfl) ⟨3914087, by rfl⟩ : syracuseStep 20875133 = 7828175) B7828175
theorem B4008361 : Blo 1407523 4008361 := bstep (se 2 (by rfl) ⟨1503135, by rfl⟩ : syracuseStep 4008361 = 3006271) B3006271
theorem B1583707 : Blo 1407523 1583707 := bstep (se 1 (by rfl) ⟨1187780, by rfl⟩ : syracuseStep 1583707 = 2375561) B2375561
theorem B6425657 : Blo 1407523 6425657 := bstep (se 2 (by rfl) ⟨2409621, by rfl⟩ : syracuseStep 6425657 = 4819243) B4819243
theorem B4754591 : Blo 1407523 4754591 := bstep (se 1 (by rfl) ⟨3565943, by rfl⟩ : syracuseStep 4754591 = 7131887) B7131887
theorem B54128249 : Blo 1407523 54128249 := bstep (se 2 (by rfl) ⟨20298093, by rfl⟩ : syracuseStep 54128249 = 40596187) B40596187
theorem B173461175 : Blo 1407523 173461175 := bstep (se 1 (by rfl) ⟨130095881, by rfl⟩ : syracuseStep 173461175 = 260191763) B260191763
theorem B8023967 : Blo 1407523 8023967 := bstep (se 1 (by rfl) ⟨6017975, by rfl⟩ : syracuseStep 8023967 = 12035951) B12035951
theorem B34263161 : Blo 1407523 34263161 := bstep (se 2 (by rfl) ⟨12848685, by rfl⟩ : syracuseStep 34263161 = 25697371) B25697371
theorem B2257087 : Blo 1407523 2257087 := bstep (se 1 (by rfl) ⟨1692815, by rfl⟩ : syracuseStep 2257087 = 3385631) B3385631
theorem B12202451 : Blo 1407523 12202451 := bstep (se 1 (by rfl) ⟨9151838, by rfl⟩ : syracuseStep 12202451 = 18303677) B18303677
theorem B5346395 : Blo 1407523 5346395 := bstep (se 1 (by rfl) ⟨4009796, by rfl⟩ : syracuseStep 5346395 = 8019593) B8019593
theorem B3167495 : Blo 1407523 3167495 := bstep (se 1 (by rfl) ⟨2375621, by rfl⟩ : syracuseStep 3167495 = 4751243) B4751243
theorem B3167711 : Blo 1407523 3167711 := bstep (se 1 (by rfl) ⟨2375783, by rfl⟩ : syracuseStep 3167711 = 4751567) B4751567
theorem B5346911 : Blo 1407523 5346911 := bstep (se 1 (by rfl) ⟨4010183, by rfl⟩ : syracuseStep 5346911 = 8020367) B8020367
theorem B16479935 : Blo 1407523 16479935 := bstep (se 1 (by rfl) ⟨12359951, by rfl⟩ : syracuseStep 16479935 = 24719903) B24719903
theorem B9631753 : Blo 1407523 9631753 := bstep (se 2 (by rfl) ⟨3611907, by rfl⟩ : syracuseStep 9631753 = 7223815) B7223815
theorem B3168377 : Blo 1407523 3168377 := bstep (se 2 (by rfl) ⟨1188141, by rfl⟩ : syracuseStep 3168377 = 2376283) B2376283
theorem B3922103 : Blo 1407523 3922103 := bstep (se 1 (by rfl) ⟨2941577, by rfl⟩ : syracuseStep 3922103 = 5883155) B5883155
theorem B2111903 : Blo 1407523 2111903 := bstep (se 1 (by rfl) ⟨1583927, by rfl⟩ : syracuseStep 2111903 = 3167855) B3167855
theorem B2111993 : Blo 1407523 2111993 := bstep (se 2 (by rfl) ⟨791997, by rfl⟩ : syracuseStep 2111993 = 1583995) B1583995
theorem B16259737 : Blo 1407523 16259737 := bstep (se 2 (by rfl) ⟨6097401, by rfl⟩ : syracuseStep 16259737 = 12194803) B12194803
theorem B1407679 : Blo 1407523 1407679 := bstep (se 1 (by rfl) ⟨1055759, by rfl⟩ : syracuseStep 1407679 = 2111519) B2111519
theorem B1407847 : Blo 1407523 1407847 := bstep (se 1 (by rfl) ⟨1055885, by rfl⟩ : syracuseStep 1407847 = 2111771) B2111771
theorem B2112479 : Blo 1407523 2112479 := bstep (se 1 (by rfl) ⟨1584359, by rfl⟩ : syracuseStep 2112479 = 3168719) B3168719
theorem B1408191 : Blo 1407523 1408191 := bstep (se 1 (by rfl) ⟨1056143, by rfl⟩ : syracuseStep 1408191 = 2112287) B2112287
theorem B2112767 : Blo 1407523 2112767 := bstep (se 1 (by rfl) ⟨1584575, by rfl⟩ : syracuseStep 2112767 = 3169151) B3169151
theorem B3562825 : Blo 1407523 3562825 := bstep (se 2 (by rfl) ⟨1336059, by rfl⟩ : syracuseStep 3562825 = 2672119) B2672119
theorem B3169619 : Blo 1407523 3169619 := bstep (se 1 (by rfl) ⟨2377214, by rfl⟩ : syracuseStep 3169619 = 4754429) B4754429
theorem B1408359 : Blo 1407523 1408359 := bstep (se 1 (by rfl) ⟨1056269, by rfl⟩ : syracuseStep 1408359 = 2112539) B2112539
theorem B3169691 : Blo 1407523 3169691 := bstep (se 1 (by rfl) ⟨2377268, by rfl⟩ : syracuseStep 3169691 = 4754537) B4754537
theorem B5349023 : Blo 1407523 5349023 := bstep (se 1 (by rfl) ⟨4011767, by rfl⟩ : syracuseStep 5349023 = 8023535) B8023535
theorem B5628788495 : Blo 1407523 5628788495 := bstep (se 1 (by rfl) ⟨4221591371, by rfl⟩ : syracuseStep 5628788495 = 8443182743) B8443182743
theorem B1408927 : Blo 1407523 1408927 := bstep (se 1 (by rfl) ⟨1056695, by rfl⟩ : syracuseStep 1408927 = 2113391) B2113391
theorem B10690541 : Blo 1407523 10690541 := bstep (se 3 (by rfl) ⟨2004476, by rfl⟩ : syracuseStep 10690541 = 4008953) B4008953
theorem B1409183 : Blo 1407523 1409183 := bstep (se 1 (by rfl) ⟨1056887, by rfl⟩ : syracuseStep 1409183 = 2113775) B2113775
theorem B8134967 : Blo 1407523 8134967 := bstep (se 1 (by rfl) ⟨6101225, by rfl⟩ : syracuseStep 8134967 = 12202451) B12202451
theorem B1409519 : Blo 1407523 1409519 := bstep (se 1 (by rfl) ⟨1057139, by rfl⟩ : syracuseStep 1409519 = 2114279) B2114279
theorem B3564263 : Blo 1407523 3564263 := bstep (se 1 (by rfl) ⟨2673197, by rfl⟩ : syracuseStep 3564263 = 5346395) B5346395
theorem B3564607 : Blo 1407523 3564607 := bstep (se 1 (by rfl) ⟨2673455, by rfl⟩ : syracuseStep 3564607 = 5346911) B5346911
theorem B10986623 : Blo 1407523 10986623 := bstep (se 1 (by rfl) ⟨8239967, by rfl⟩ : syracuseStep 10986623 = 16479935) B16479935
theorem B4752539 : Blo 1407523 4752539 := bstep (se 1 (by rfl) ⟨3564404, by rfl⟩ : syracuseStep 4752539 = 7128809) B7128809
theorem B2614735 : Blo 1407523 2614735 := bstep (se 1 (by rfl) ⟨1961051, by rfl⟩ : syracuseStep 2614735 = 3922103) B3922103
theorem B3566015 : Blo 1407523 3566015 := bstep (se 1 (by rfl) ⟨2674511, by rfl⟩ : syracuseStep 3566015 = 5349023) B5349023
theorem B115640783 : Blo 1407523 115640783 := bstep (se 1 (by rfl) ⟨86730587, by rfl⟩ : syracuseStep 115640783 = 173461175) B173461175
theorem B9022195 : Blo 1407523 9022195 := bstep (se 1 (by rfl) ⟨6766646, by rfl⟩ : syracuseStep 9022195 = 13533293) B13533293
theorem B22842107 : Blo 1407523 22842107 := bstep (se 1 (by rfl) ⟨17131580, by rfl⟩ : syracuseStep 22842107 = 34263161) B34263161
theorem B8022827 : Blo 1407523 8022827 := bstep (se 1 (by rfl) ⟨6017120, by rfl⟩ : syracuseStep 8022827 = 12034241) B12034241
theorem B3009449 : Blo 1407523 3009449 := bstep (se 2 (by rfl) ⟨1128543, by rfl⟩ : syracuseStep 3009449 = 2257087) B2257087
theorem B3566551 : Blo 1407523 3566551 := bstep (se 1 (by rfl) ⟨2674913, by rfl⟩ : syracuseStep 3566551 = 5349827) B5349827
theorem B5344481 : Blo 1407523 5344481 := bstep (se 2 (by rfl) ⟨2004180, by rfl⟩ : syracuseStep 5344481 = 4008361) B4008361
theorem B3566855 : Blo 1407523 3566855 := bstep (se 1 (by rfl) ⟨2675141, by rfl⟩ : syracuseStep 3566855 = 5350283) B5350283
theorem B21679649 : Blo 1407523 21679649 := bstep (se 2 (by rfl) ⟨8129868, by rfl⟩ : syracuseStep 21679649 = 16259737) B16259737
theorem B51369349 : Blo 1407523 51369349 := bstep (se 4 (by rfl) ⟨4815876, by rfl⟩ : syracuseStep 51369349 = 9631753) B9631753
theorem B8017703 : Blo 1407523 8017703 := bstep (se 1 (by rfl) ⟨6013277, by rfl⟩ : syracuseStep 8017703 = 12026555) B12026555
theorem B2111609 : Blo 1407523 2111609 := bstep (se 2 (by rfl) ⟨791853, by rfl⟩ : syracuseStep 2111609 = 1583707) B1583707
theorem B2111663 : Blo 1407523 2111663 := bstep (se 1 (by rfl) ⟨1583747, by rfl⟩ : syracuseStep 2111663 = 3167495) B3167495
theorem B2111807 : Blo 1407523 2111807 := bstep (se 1 (by rfl) ⟨1583855, by rfl⟩ : syracuseStep 2111807 = 3167711) B3167711
theorem B13916755 : Blo 1407523 13916755 := bstep (se 1 (by rfl) ⟨10437566, by rfl⟩ : syracuseStep 13916755 = 20875133) B20875133
theorem B2112251 : Blo 1407523 2112251 := bstep (se 1 (by rfl) ⟨1584188, by rfl⟩ : syracuseStep 2112251 = 3168377) B3168377
theorem B1407935 : Blo 1407523 1407935 := bstep (se 1 (by rfl) ⟨1055951, by rfl⟩ : syracuseStep 1407935 = 2111903) B2111903
theorem B1407995 : Blo 1407523 1407995 := bstep (se 1 (by rfl) ⟨1055996, by rfl⟩ : syracuseStep 1407995 = 2111993) B2111993
theorem B4750433 : Blo 1407523 4750433 := bstep (se 2 (by rfl) ⟨1781412, by rfl⟩ : syracuseStep 4750433 = 3562825) B3562825
theorem B1408319 : Blo 1407523 1408319 := bstep (se 1 (by rfl) ⟨1056239, by rfl⟩ : syracuseStep 1408319 = 2112479) B2112479
theorem B4283771 : Blo 1407523 4283771 := bstep (se 1 (by rfl) ⟨3212828, by rfl⟩ : syracuseStep 4283771 = 6425657) B6425657
theorem B3169727 : Blo 1407523 3169727 := bstep (se 1 (by rfl) ⟨2377295, by rfl⟩ : syracuseStep 3169727 = 4754591) B4754591
theorem B1408511 : Blo 1407523 1408511 := bstep (se 1 (by rfl) ⟨1056383, by rfl⟩ : syracuseStep 1408511 = 2112767) B2112767
theorem B2113079 : Blo 1407523 2113079 := bstep (se 1 (by rfl) ⟨1584809, by rfl⟩ : syracuseStep 2113079 = 3169619) B3169619
theorem B2113127 : Blo 1407523 2113127 := bstep (se 1 (by rfl) ⟨1584845, by rfl⟩ : syracuseStep 2113127 = 3169691) B3169691
theorem B36085499 : Blo 1407523 36085499 := bstep (se 1 (by rfl) ⟨27064124, by rfl⟩ : syracuseStep 36085499 = 54128249) B54128249
theorem B3752525663 : Blo 1407523 3752525663 := bstep (se 1 (by rfl) ⟨2814394247, by rfl⟩ : syracuseStep 3752525663 = 5628788495) B5628788495
theorem B5349311 : Blo 1407523 5349311 := bstep (se 1 (by rfl) ⟨4011983, by rfl⟩ : syracuseStep 5349311 = 8023967) B8023967
theorem B7127027 : Blo 1407523 7127027 := bstep (se 1 (by rfl) ⟨5345270, by rfl⟩ : syracuseStep 7127027 = 10690541) B10690541
theorem B5423311 : Blo 1407523 5423311 := bstep (se 1 (by rfl) ⟨4067483, by rfl⟩ : syracuseStep 5423311 = 8134967) B8134967
theorem B2376175 : Blo 1407523 2376175 := bstep (se 1 (by rfl) ⟨1782131, by rfl⟩ : syracuseStep 2376175 = 3564263) B3564263
theorem B7324415 : Blo 1407523 7324415 := bstep (se 1 (by rfl) ⟨5493311, by rfl⟩ : syracuseStep 7324415 = 10986623) B10986623
theorem B18555673 : Blo 1407523 18555673 := bstep (se 2 (by rfl) ⟨6958377, by rfl⟩ : syracuseStep 18555673 = 13916755) B13916755
theorem B4752809 : Blo 1407523 4752809 := bstep (se 2 (by rfl) ⟨1782303, by rfl⟩ : syracuseStep 4752809 = 3564607) B3564607
theorem B2377343 : Blo 1407523 2377343 := bstep (se 1 (by rfl) ⟨1783007, by rfl⟩ : syracuseStep 2377343 = 3566015) B3566015
theorem B2377903 : Blo 1407523 2377903 := bstep (se 1 (by rfl) ⟨1783427, by rfl⟩ : syracuseStep 2377903 = 3566855) B3566855
theorem B14453099 : Blo 1407523 14453099 := bstep (se 1 (by rfl) ⟨10839824, by rfl⟩ : syracuseStep 14453099 = 21679649) B21679649
theorem B2501683775 : Blo 1407523 2501683775 := bstep (se 1 (by rfl) ⟨1876262831, by rfl⟩ : syracuseStep 2501683775 = 3752525663) B3752525663
theorem B3566207 : Blo 1407523 3566207 := bstep (se 1 (by rfl) ⟨2674655, by rfl⟩ : syracuseStep 3566207 = 5349311) B5349311
theorem B12029593 : Blo 1407523 12029593 := bstep (se 2 (by rfl) ⟨4511097, by rfl⟩ : syracuseStep 12029593 = 9022195) B9022195
theorem B11423389 : Blo 1407523 11423389 := bstep (se 3 (by rfl) ⟨2141885, by rfl⟩ : syracuseStep 11423389 = 4283771) B4283771
theorem B5345135 : Blo 1407523 5345135 := bstep (se 1 (by rfl) ⟨4008851, by rfl⟩ : syracuseStep 5345135 = 8017703) B8017703
theorem B4755401 : Blo 1407523 4755401 := bstep (se 2 (by rfl) ⟨1783275, by rfl⟩ : syracuseStep 4755401 = 3566551) B3566551
theorem B3486313 : Blo 1407523 3486313 := bstep (se 2 (by rfl) ⟨1307367, by rfl⟩ : syracuseStep 3486313 = 2614735) B2614735
theorem B3166955 : Blo 1407523 3166955 := bstep (se 1 (by rfl) ⟨2375216, by rfl⟩ : syracuseStep 3166955 = 4750433) B4750433
theorem B24056999 : Blo 1407523 24056999 := bstep (se 1 (by rfl) ⟨18042749, by rfl⟩ : syracuseStep 24056999 = 36085499) B36085499
theorem B3168359 : Blo 1407523 3168359 := bstep (se 1 (by rfl) ⟨2376269, by rfl⟩ : syracuseStep 3168359 = 4752539) B4752539
theorem B1407739 : Blo 1407523 1407739 := bstep (se 1 (by rfl) ⟨1055804, by rfl⟩ : syracuseStep 1407739 = 2111609) B2111609
theorem B1407775 : Blo 1407523 1407775 := bstep (se 1 (by rfl) ⟨1055831, by rfl⟩ : syracuseStep 1407775 = 2111663) B2111663
theorem B1407871 : Blo 1407523 1407871 := bstep (se 1 (by rfl) ⟨1055903, by rfl⟩ : syracuseStep 1407871 = 2111807) B2111807
theorem B77093855 : Blo 1407523 77093855 := bstep (se 1 (by rfl) ⟨57820391, by rfl⟩ : syracuseStep 77093855 = 115640783) B115640783
theorem B1408167 : Blo 1407523 1408167 := bstep (se 1 (by rfl) ⟨1056125, by rfl⟩ : syracuseStep 1408167 = 2112251) B2112251
theorem B15228071 : Blo 1407523 15228071 := bstep (se 1 (by rfl) ⟨11421053, by rfl⟩ : syracuseStep 15228071 = 22842107) B22842107
theorem B68492465 : Blo 1407523 68492465 := bstep (se 2 (by rfl) ⟨25684674, by rfl⟩ : syracuseStep 68492465 = 51369349) B51369349
theorem B5348551 : Blo 1407523 5348551 := bstep (se 1 (by rfl) ⟨4011413, by rfl⟩ : syracuseStep 5348551 = 8022827) B8022827
theorem B2006299 : Blo 1407523 2006299 := bstep (se 1 (by rfl) ⟨1504724, by rfl⟩ : syracuseStep 2006299 = 3009449) B3009449
theorem B3562987 : Blo 1407523 3562987 := bstep (se 1 (by rfl) ⟨2672240, by rfl⟩ : syracuseStep 3562987 = 5344481) B5344481
theorem B2113151 : Blo 1407523 2113151 := bstep (se 1 (by rfl) ⟨1584863, by rfl⟩ : syracuseStep 2113151 = 3169727) B3169727
theorem B1408719 : Blo 1407523 1408719 := bstep (se 1 (by rfl) ⟨1056539, by rfl⟩ : syracuseStep 1408719 = 2113079) B2113079
theorem B1408751 : Blo 1407523 1408751 := bstep (se 1 (by rfl) ⟨1056563, by rfl⟩ : syracuseStep 1408751 = 2113127) B2113127
theorem B4751351 : Blo 1407523 4751351 := bstep (se 1 (by rfl) ⟨3563513, by rfl⟩ : syracuseStep 4751351 = 7127027) B7127027
theorem B3170537 : Blo 1407523 3170537 := bstep (se 2 (by rfl) ⟨1188951, by rfl⟩ : syracuseStep 3170537 = 2377903) B2377903
theorem B4882943 : Blo 1407523 4882943 := bstep (se 1 (by rfl) ⟨3662207, by rfl⟩ : syracuseStep 4882943 = 7324415) B7324415
theorem B24740897 : Blo 1407523 24740897 := bstep (se 2 (by rfl) ⟨9277836, by rfl⟩ : syracuseStep 24740897 = 18555673) B18555673
theorem B10700261 : Blo 1407523 10700261 := bstep (se 4 (by rfl) ⟨1003149, by rfl⟩ : syracuseStep 10700261 = 2006299) B2006299
theorem B9635399 : Blo 1407523 9635399 := bstep (se 1 (by rfl) ⟨7226549, by rfl⟩ : syracuseStep 9635399 = 14453099) B14453099
theorem B2377471 : Blo 1407523 2377471 := bstep (se 1 (by rfl) ⟨1783103, by rfl⟩ : syracuseStep 2377471 = 3566207) B3566207
theorem B10152047 : Blo 1407523 10152047 := bstep (se 1 (by rfl) ⟨7614035, by rfl⟩ : syracuseStep 10152047 = 15228071) B15228071
theorem B15231185 : Blo 1407523 15231185 := bstep (se 2 (by rfl) ⟨5711694, by rfl⟩ : syracuseStep 15231185 = 11423389) B11423389
theorem B4648417 : Blo 1407523 4648417 := bstep (se 2 (by rfl) ⟨1743156, by rfl⟩ : syracuseStep 4648417 = 3486313) B3486313
theorem B1584895 : Blo 1407523 1584895 := bstep (se 1 (by rfl) ⟨1188671, by rfl⟩ : syracuseStep 1584895 = 2377343) B2377343
theorem B7131401 : Blo 1407523 7131401 := bstep (se 2 (by rfl) ⟨2674275, by rfl⟩ : syracuseStep 7131401 = 5348551) B5348551
theorem B1667789183 : Blo 1407523 1667789183 := bstep (se 1 (by rfl) ⟨1250841887, by rfl⟩ : syracuseStep 1667789183 = 2501683775) B2501683775
theorem B3167567 : Blo 1407523 3167567 := bstep (se 1 (by rfl) ⟨2375675, by rfl⟩ : syracuseStep 3167567 = 4751351) B4751351
theorem B7231081 : Blo 1407523 7231081 := bstep (se 2 (by rfl) ⟨2711655, by rfl⟩ : syracuseStep 7231081 = 5423311) B5423311
theorem B2111303 : Blo 1407523 2111303 := bstep (se 1 (by rfl) ⟨1583477, by rfl⟩ : syracuseStep 2111303 = 3166955) B3166955
theorem B3168233 : Blo 1407523 3168233 := bstep (se 2 (by rfl) ⟨1188087, by rfl⟩ : syracuseStep 3168233 = 2376175) B2376175
theorem B16037999 : Blo 1407523 16037999 := bstep (se 1 (by rfl) ⟨12028499, by rfl⟩ : syracuseStep 16037999 = 24056999) B24056999
theorem B3168539 : Blo 1407523 3168539 := bstep (se 1 (by rfl) ⟨2376404, by rfl⟩ : syracuseStep 3168539 = 4752809) B4752809
theorem B2112239 : Blo 1407523 2112239 := bstep (se 1 (by rfl) ⟨1584179, by rfl⟩ : syracuseStep 2112239 = 3168359) B3168359
theorem B4750649 : Blo 1407523 4750649 := bstep (se 2 (by rfl) ⟨1781493, by rfl⟩ : syracuseStep 4750649 = 3562987) B3562987
theorem B51395903 : Blo 1407523 51395903 := bstep (se 1 (by rfl) ⟨38546927, by rfl⟩ : syracuseStep 51395903 = 77093855) B77093855
theorem B45661643 : Blo 1407523 45661643 := bstep (se 1 (by rfl) ⟨34246232, by rfl⟩ : syracuseStep 45661643 = 68492465) B68492465
theorem B16039457 : Blo 1407523 16039457 := bstep (se 2 (by rfl) ⟨6014796, by rfl⟩ : syracuseStep 16039457 = 12029593) B12029593
theorem B1408767 : Blo 1407523 1408767 := bstep (se 1 (by rfl) ⟨1056575, by rfl⟩ : syracuseStep 1408767 = 2113151) B2113151
theorem B3563423 : Blo 1407523 3563423 := bstep (se 1 (by rfl) ⟨2672567, by rfl⟩ : syracuseStep 3563423 = 5345135) B5345135
theorem B3170267 : Blo 1407523 3170267 := bstep (se 1 (by rfl) ⟨2377700, by rfl⟩ : syracuseStep 3170267 = 4755401) B4755401
theorem B2113691 : Blo 1407523 2113691 := bstep (se 1 (by rfl) ⟨1585268, by rfl⟩ : syracuseStep 2113691 = 3170537) B3170537
theorem B1111859455 : Blo 1407523 1111859455 := bstep (se 1 (by rfl) ⟨833894591, by rfl⟩ : syracuseStep 1111859455 = 1667789183) B1667789183
theorem B6423599 : Blo 1407523 6423599 := bstep (se 1 (by rfl) ⟨4817699, by rfl⟩ : syracuseStep 6423599 = 9635399) B9635399
theorem B10691999 : Blo 1407523 10691999 := bstep (se 1 (by rfl) ⟨8018999, by rfl⟩ : syracuseStep 10691999 = 16037999) B16037999
theorem B6768031 : Blo 1407523 6768031 := bstep (se 1 (by rfl) ⟨5076023, by rfl⟩ : syracuseStep 6768031 = 10152047) B10152047
theorem B10692971 : Blo 1407523 10692971 := bstep (se 1 (by rfl) ⟨8019728, by rfl⟩ : syracuseStep 10692971 = 16039457) B16039457
theorem B24791557 : Blo 1407523 24791557 := bstep (se 4 (by rfl) ⟨2324208, by rfl⟩ : syracuseStep 24791557 = 4648417) B4648417
theorem B4754267 : Blo 1407523 4754267 := bstep (se 1 (by rfl) ⟨3565700, by rfl⟩ : syracuseStep 4754267 = 7131401) B7131401
theorem B3255295 : Blo 1407523 3255295 := bstep (se 1 (by rfl) ⟨2441471, by rfl⟩ : syracuseStep 3255295 = 4882943) B4882943
theorem B10154123 : Blo 1407523 10154123 := bstep (se 1 (by rfl) ⟨7615592, by rfl⟩ : syracuseStep 10154123 = 15231185) B15231185
theorem B3167099 : Blo 1407523 3167099 := bstep (se 1 (by rfl) ⟨2375324, by rfl⟩ : syracuseStep 3167099 = 4750649) B4750649
theorem B34263935 : Blo 1407523 34263935 := bstep (se 1 (by rfl) ⟨25697951, by rfl⟩ : syracuseStep 34263935 = 51395903) B51395903
theorem B65975725 : Blo 1407523 65975725 := bstep (se 3 (by rfl) ⟨12370448, by rfl⟩ : syracuseStep 65975725 = 24740897) B24740897
theorem B2111711 : Blo 1407523 2111711 := bstep (se 1 (by rfl) ⟨1583783, by rfl⟩ : syracuseStep 2111711 = 3167567) B3167567
theorem B7133507 : Blo 1407523 7133507 := bstep (se 1 (by rfl) ⟨5350130, by rfl⟩ : syracuseStep 7133507 = 10700261) B10700261
theorem B1407535 : Blo 1407523 1407535 := bstep (se 1 (by rfl) ⟨1055651, by rfl⟩ : syracuseStep 1407535 = 2111303) B2111303
theorem B2112155 : Blo 1407523 2112155 := bstep (se 1 (by rfl) ⟨1584116, by rfl⟩ : syracuseStep 2112155 = 3168233) B3168233
theorem B2112359 : Blo 1407523 2112359 := bstep (se 1 (by rfl) ⟨1584269, by rfl⟩ : syracuseStep 2112359 = 3168539) B3168539
theorem B1408159 : Blo 1407523 1408159 := bstep (se 1 (by rfl) ⟨1056119, by rfl⟩ : syracuseStep 1408159 = 2112239) B2112239
theorem B9641441 : Blo 1407523 9641441 := bstep (se 2 (by rfl) ⟨3615540, by rfl⟩ : syracuseStep 9641441 = 7231081) B7231081
theorem B30441095 : Blo 1407523 30441095 := bstep (se 1 (by rfl) ⟨22830821, by rfl⟩ : syracuseStep 30441095 = 45661643) B45661643
theorem B2113193 : Blo 1407523 2113193 := bstep (se 2 (by rfl) ⟨792447, by rfl⟩ : syracuseStep 2113193 = 1584895) B1584895
theorem B3169961 : Blo 1407523 3169961 := bstep (se 2 (by rfl) ⟨1188735, by rfl⟩ : syracuseStep 3169961 = 2377471) B2377471
theorem B2375615 : Blo 1407523 2375615 := bstep (se 1 (by rfl) ⟨1781711, by rfl⟩ : syracuseStep 2375615 = 3563423) B3563423
theorem B2113511 : Blo 1407523 2113511 := bstep (se 1 (by rfl) ⟨1585133, by rfl⟩ : syracuseStep 2113511 = 3170267) B3170267
theorem B1409127 : Blo 1407523 1409127 := bstep (se 1 (by rfl) ⟨1056845, by rfl⟩ : syracuseStep 1409127 = 2113691) B2113691
theorem B33055409 : Blo 1407523 33055409 := bstep (se 2 (by rfl) ⟨12395778, by rfl⟩ : syracuseStep 33055409 = 24791557) B24791557
theorem B7127999 : Blo 1407523 7127999 := bstep (se 1 (by rfl) ⟨5345999, by rfl⟩ : syracuseStep 7127999 = 10691999) B10691999
theorem B7128647 : Blo 1407523 7128647 := bstep (se 1 (by rfl) ⟨5346485, by rfl⟩ : syracuseStep 7128647 = 10692971) B10692971
theorem B87967633 : Blo 1407523 87967633 := bstep (se 2 (by rfl) ⟨32987862, by rfl⟩ : syracuseStep 87967633 = 65975725) B65975725
theorem B20294063 : Blo 1407523 20294063 := bstep (se 1 (by rfl) ⟨15220547, by rfl⟩ : syracuseStep 20294063 = 30441095) B30441095
theorem B1583743 : Blo 1407523 1583743 := bstep (se 1 (by rfl) ⟨1187807, by rfl⟩ : syracuseStep 1583743 = 2375615) B2375615
theorem B6769415 : Blo 1407523 6769415 := bstep (se 1 (by rfl) ⟨5077061, by rfl⟩ : syracuseStep 6769415 = 10154123) B10154123
theorem B22842623 : Blo 1407523 22842623 := bstep (se 1 (by rfl) ⟨17131967, by rfl⟩ : syracuseStep 22842623 = 34263935) B34263935
theorem B25710509 : Blo 1407523 25710509 := bstep (se 3 (by rfl) ⟨4820720, by rfl⟩ : syracuseStep 25710509 = 9641441) B9641441
theorem B4755671 : Blo 1407523 4755671 := bstep (se 1 (by rfl) ⟨3566753, by rfl⟩ : syracuseStep 4755671 = 7133507) B7133507
theorem B9024041 : Blo 1407523 9024041 := bstep (se 2 (by rfl) ⟨3384015, by rfl⟩ : syracuseStep 9024041 = 6768031) B6768031
theorem B1482479273 : Blo 1407523 1482479273 := bstep (se 2 (by rfl) ⟨555929727, by rfl⟩ : syracuseStep 1482479273 = 1111859455) B1111859455
theorem B2111399 : Blo 1407523 2111399 := bstep (se 1 (by rfl) ⟨1583549, by rfl⟩ : syracuseStep 2111399 = 3167099) B3167099
theorem B4282399 : Blo 1407523 4282399 := bstep (se 1 (by rfl) ⟨3211799, by rfl⟩ : syracuseStep 4282399 = 6423599) B6423599
theorem B4340393 : Blo 1407523 4340393 := bstep (se 2 (by rfl) ⟨1627647, by rfl⟩ : syracuseStep 4340393 = 3255295) B3255295
theorem B1407807 : Blo 1407523 1407807 := bstep (se 1 (by rfl) ⟨1055855, by rfl⟩ : syracuseStep 1407807 = 2111711) B2111711
theorem B1408103 : Blo 1407523 1408103 := bstep (se 1 (by rfl) ⟨1056077, by rfl⟩ : syracuseStep 1408103 = 2112155) B2112155
theorem B3169511 : Blo 1407523 3169511 := bstep (se 1 (by rfl) ⟨2377133, by rfl⟩ : syracuseStep 3169511 = 4754267) B4754267
theorem B1408239 : Blo 1407523 1408239 := bstep (se 1 (by rfl) ⟨1056179, by rfl⟩ : syracuseStep 1408239 = 2112359) B2112359
theorem B1408795 : Blo 1407523 1408795 := bstep (se 1 (by rfl) ⟨1056596, by rfl⟩ : syracuseStep 1408795 = 2113193) B2113193
theorem B2113307 : Blo 1407523 2113307 := bstep (se 1 (by rfl) ⟨1584980, by rfl⟩ : syracuseStep 2113307 = 3169961) B3169961
theorem B1409007 : Blo 1407523 1409007 := bstep (se 1 (by rfl) ⟨1056755, by rfl⟩ : syracuseStep 1409007 = 2113511) B2113511
theorem B5709865 : Blo 1407523 5709865 := bstep (se 2 (by rfl) ⟨2141199, by rfl⟩ : syracuseStep 5709865 = 4282399) B4282399
theorem B3170447 : Blo 1407523 3170447 := bstep (se 1 (by rfl) ⟨2377835, by rfl⟩ : syracuseStep 3170447 = 4755671) B4755671
theorem B4751999 : Blo 1407523 4751999 := bstep (se 1 (by rfl) ⟨3563999, by rfl⟩ : syracuseStep 4751999 = 7127999) B7127999
theorem B4752431 : Blo 1407523 4752431 := bstep (se 1 (by rfl) ⟨3564323, by rfl⟩ : syracuseStep 4752431 = 7128647) B7128647
theorem B2893595 : Blo 1407523 2893595 := bstep (se 1 (by rfl) ⟨2170196, by rfl⟩ : syracuseStep 2893595 = 4340393) B4340393
theorem B88147757 : Blo 1407523 88147757 := bstep (se 3 (by rfl) ⟨16527704, by rfl⟩ : syracuseStep 88147757 = 33055409) B33055409
theorem B17140339 : Blo 1407523 17140339 := bstep (se 1 (by rfl) ⟨12855254, by rfl⟩ : syracuseStep 17140339 = 25710509) B25710509
theorem B6016027 : Blo 1407523 6016027 := bstep (se 1 (by rfl) ⟨4512020, by rfl⟩ : syracuseStep 6016027 = 9024041) B9024041
theorem B988319515 : Blo 1407523 988319515 := bstep (se 1 (by rfl) ⟨741239636, by rfl⟩ : syracuseStep 988319515 = 1482479273) B1482479273
theorem B13529375 : Blo 1407523 13529375 := bstep (se 1 (by rfl) ⟨10147031, by rfl⟩ : syracuseStep 13529375 = 20294063) B20294063
theorem B117290177 : Blo 1407523 117290177 := bstep (se 2 (by rfl) ⟨43983816, by rfl⟩ : syracuseStep 117290177 = 87967633) B87967633
theorem B2111657 : Blo 1407523 2111657 := bstep (se 2 (by rfl) ⟨791871, by rfl⟩ : syracuseStep 2111657 = 1583743) B1583743
theorem B1407599 : Blo 1407523 1407599 := bstep (se 1 (by rfl) ⟨1055699, by rfl⟩ : syracuseStep 1407599 = 2111399) B2111399
theorem B4512943 : Blo 1407523 4512943 := bstep (se 1 (by rfl) ⟨3384707, by rfl⟩ : syracuseStep 4512943 = 6769415) B6769415
theorem B2113007 : Blo 1407523 2113007 := bstep (se 1 (by rfl) ⟨1584755, by rfl⟩ : syracuseStep 2113007 = 3169511) B3169511
theorem B15228415 : Blo 1407523 15228415 := bstep (se 1 (by rfl) ⟨11421311, by rfl⟩ : syracuseStep 15228415 = 22842623) B22842623
theorem B1408871 : Blo 1407523 1408871 := bstep (se 1 (by rfl) ⟨1056653, by rfl⟩ : syracuseStep 1408871 = 2113307) B2113307
theorem B2113631 : Blo 1407523 2113631 := bstep (se 1 (by rfl) ⟨1585223, by rfl⟩ : syracuseStep 2113631 = 3170447) B3170447
theorem B9019583 : Blo 1407523 9019583 := bstep (se 1 (by rfl) ⟨6764687, by rfl⟩ : syracuseStep 9019583 = 13529375) B13529375
theorem B78193451 : Blo 1407523 78193451 := bstep (se 1 (by rfl) ⟨58645088, by rfl⟩ : syracuseStep 78193451 = 117290177) B117290177
theorem B8021369 : Blo 1407523 8021369 := bstep (se 2 (by rfl) ⟨3008013, by rfl⟩ : syracuseStep 8021369 = 6016027) B6016027
theorem B1317759353 : Blo 1407523 1317759353 := bstep (se 2 (by rfl) ⟨494159757, by rfl⟩ : syracuseStep 1317759353 = 988319515) B988319515
theorem B7613153 : Blo 1407523 7613153 := bstep (se 2 (by rfl) ⟨2854932, by rfl⟩ : syracuseStep 7613153 = 5709865) B5709865
theorem B58765171 : Blo 1407523 58765171 := bstep (se 1 (by rfl) ⟨44073878, by rfl⟩ : syracuseStep 58765171 = 88147757) B88147757
theorem B6017257 : Blo 1407523 6017257 := bstep (se 2 (by rfl) ⟨2256471, by rfl⟩ : syracuseStep 6017257 = 4512943) B4512943
theorem B20304553 : Blo 1407523 20304553 := bstep (se 2 (by rfl) ⟨7614207, by rfl⟩ : syracuseStep 20304553 = 15228415) B15228415
theorem B30865013 : Blo 1407523 30865013 := bstep (se 5 (by rfl) ⟨1446797, by rfl⟩ : syracuseStep 30865013 = 2893595) B2893595
theorem B3167999 : Blo 1407523 3167999 := bstep (se 1 (by rfl) ⟨2375999, by rfl⟩ : syracuseStep 3167999 = 4751999) B4751999
theorem B3168287 : Blo 1407523 3168287 := bstep (se 1 (by rfl) ⟨2376215, by rfl⟩ : syracuseStep 3168287 = 4752431) B4752431
theorem B22853785 : Blo 1407523 22853785 := bstep (se 2 (by rfl) ⟨8570169, by rfl⟩ : syracuseStep 22853785 = 17140339) B17140339
theorem B1407771 : Blo 1407523 1407771 := bstep (se 1 (by rfl) ⟨1055828, by rfl⟩ : syracuseStep 1407771 = 2111657) B2111657
theorem B1408671 : Blo 1407523 1408671 := bstep (se 1 (by rfl) ⟨1056503, by rfl⟩ : syracuseStep 1408671 = 2113007) B2113007
theorem B1409087 : Blo 1407523 1409087 := bstep (se 1 (by rfl) ⟨1056815, by rfl⟩ : syracuseStep 1409087 = 2113631) B2113631
theorem B6013055 : Blo 1407523 6013055 := bstep (se 1 (by rfl) ⟨4509791, by rfl⟩ : syracuseStep 6013055 = 9019583) B9019583
theorem B8023009 : Blo 1407523 8023009 := bstep (se 2 (by rfl) ⟨3008628, by rfl⟩ : syracuseStep 8023009 = 6017257) B6017257
theorem B52128967 : Blo 1407523 52128967 := bstep (se 1 (by rfl) ⟨39096725, by rfl⟩ : syracuseStep 52128967 = 78193451) B78193451
theorem B878506235 : Blo 1407523 878506235 := bstep (se 1 (by rfl) ⟨658879676, by rfl⟩ : syracuseStep 878506235 = 1317759353) B1317759353
theorem B5075435 : Blo 1407523 5075435 := bstep (se 1 (by rfl) ⟨3806576, by rfl⟩ : syracuseStep 5075435 = 7613153) B7613153
theorem B78353561 : Blo 1407523 78353561 := bstep (se 2 (by rfl) ⟨29382585, by rfl⟩ : syracuseStep 78353561 = 58765171) B58765171
theorem B30471713 : Blo 1407523 30471713 := bstep (se 2 (by rfl) ⟨11426892, by rfl⟩ : syracuseStep 30471713 = 22853785) B22853785
theorem B27072737 : Blo 1407523 27072737 := bstep (se 2 (by rfl) ⟨10152276, by rfl⟩ : syracuseStep 27072737 = 20304553) B20304553
theorem B5347579 : Blo 1407523 5347579 := bstep (se 1 (by rfl) ⟨4010684, by rfl⟩ : syracuseStep 5347579 = 8021369) B8021369
theorem B20576675 : Blo 1407523 20576675 := bstep (se 1 (by rfl) ⟨15432506, by rfl⟩ : syracuseStep 20576675 = 30865013) B30865013
theorem B2111999 : Blo 1407523 2111999 := bstep (se 1 (by rfl) ⟨1583999, by rfl⟩ : syracuseStep 2111999 = 3167999) B3167999
theorem B2112191 : Blo 1407523 2112191 := bstep (se 1 (by rfl) ⟨1584143, by rfl⟩ : syracuseStep 2112191 = 3168287) B3168287
theorem B585670823 : Blo 1407523 585670823 := bstep (se 1 (by rfl) ⟨439253117, by rfl⟩ : syracuseStep 585670823 = 878506235) B878506235
theorem B3383623 : Blo 1407523 3383623 := bstep (se 1 (by rfl) ⟨2537717, by rfl⟩ : syracuseStep 3383623 = 5075435) B5075435
theorem B18048491 : Blo 1407523 18048491 := bstep (se 1 (by rfl) ⟨13536368, by rfl⟩ : syracuseStep 18048491 = 27072737) B27072737
theorem B4008703 : Blo 1407523 4008703 := bstep (se 1 (by rfl) ⟨3006527, by rfl⟩ : syracuseStep 4008703 = 6013055) B6013055
theorem B7130105 : Blo 1407523 7130105 := bstep (se 2 (by rfl) ⟨2673789, by rfl⟩ : syracuseStep 7130105 = 5347579) B5347579
theorem B52235707 : Blo 1407523 52235707 := bstep (se 1 (by rfl) ⟨39176780, by rfl⟩ : syracuseStep 52235707 = 78353561) B78353561
theorem B69505289 : Blo 1407523 69505289 := bstep (se 2 (by rfl) ⟨26064483, by rfl⟩ : syracuseStep 69505289 = 52128967) B52128967
theorem B13717783 : Blo 1407523 13717783 := bstep (se 1 (by rfl) ⟨10288337, by rfl⟩ : syracuseStep 13717783 = 20576675) B20576675
theorem B20314475 : Blo 1407523 20314475 := bstep (se 1 (by rfl) ⟨15235856, by rfl⟩ : syracuseStep 20314475 = 30471713) B30471713
theorem B10697345 : Blo 1407523 10697345 := bstep (se 2 (by rfl) ⟨4011504, by rfl⟩ : syracuseStep 10697345 = 8023009) B8023009
theorem B1407999 : Blo 1407523 1407999 := bstep (se 1 (by rfl) ⟨1055999, by rfl⟩ : syracuseStep 1407999 = 2111999) B2111999
theorem B1408127 : Blo 1407523 1408127 := bstep (se 1 (by rfl) ⟨1056095, by rfl⟩ : syracuseStep 1408127 = 2112191) B2112191
theorem B390447215 : Blo 1407523 390447215 := bstep (se 1 (by rfl) ⟨292835411, by rfl⟩ : syracuseStep 390447215 = 585670823) B585670823
theorem B13542983 : Blo 1407523 13542983 := bstep (se 1 (by rfl) ⟨10157237, by rfl⟩ : syracuseStep 13542983 = 20314475) B20314475
theorem B4753403 : Blo 1407523 4753403 := bstep (se 1 (by rfl) ⟨3565052, by rfl⟩ : syracuseStep 4753403 = 7130105) B7130105
theorem B46336859 : Blo 1407523 46336859 := bstep (se 1 (by rfl) ⟨34752644, by rfl⟩ : syracuseStep 46336859 = 69505289) B69505289
theorem B5344937 : Blo 1407523 5344937 := bstep (se 2 (by rfl) ⟨2004351, by rfl⟩ : syracuseStep 5344937 = 4008703) B4008703
theorem B7131563 : Blo 1407523 7131563 := bstep (se 1 (by rfl) ⟨5348672, by rfl⟩ : syracuseStep 7131563 = 10697345) B10697345
theorem B18290377 : Blo 1407523 18290377 := bstep (se 2 (by rfl) ⟨6858891, by rfl⟩ : syracuseStep 18290377 = 13717783) B13717783
theorem B4511497 : Blo 1407523 4511497 := bstep (se 2 (by rfl) ⟨1691811, by rfl⟩ : syracuseStep 4511497 = 3383623) B3383623
theorem B12032327 : Blo 1407523 12032327 := bstep (se 1 (by rfl) ⟨9024245, by rfl⟩ : syracuseStep 12032327 = 18048491) B18048491
theorem B69647609 : Blo 1407523 69647609 := bstep (se 2 (by rfl) ⟨26117853, by rfl⟩ : syracuseStep 69647609 = 52235707) B52235707
theorem B9028655 : Blo 1407523 9028655 := bstep (se 1 (by rfl) ⟨6771491, by rfl⟩ : syracuseStep 9028655 = 13542983) B13542983
theorem B8021551 : Blo 1407523 8021551 := bstep (se 1 (by rfl) ⟨6016163, by rfl⟩ : syracuseStep 8021551 = 12032327) B12032327
theorem B6015329 : Blo 1407523 6015329 := bstep (se 2 (by rfl) ⟨2255748, by rfl⟩ : syracuseStep 6015329 = 4511497) B4511497
theorem B4754375 : Blo 1407523 4754375 := bstep (se 1 (by rfl) ⟨3565781, by rfl⟩ : syracuseStep 4754375 = 7131563) B7131563
theorem B260298143 : Blo 1407523 260298143 := bstep (se 1 (by rfl) ⟨195223607, by rfl⟩ : syracuseStep 260298143 = 390447215) B390447215
theorem B3168935 : Blo 1407523 3168935 := bstep (se 1 (by rfl) ⟨2376701, by rfl⟩ : syracuseStep 3168935 = 4753403) B4753403
theorem B30891239 : Blo 1407523 30891239 := bstep (se 1 (by rfl) ⟨23168429, by rfl⟩ : syracuseStep 30891239 = 46336859) B46336859
theorem B46431739 : Blo 1407523 46431739 := bstep (se 1 (by rfl) ⟨34823804, by rfl⟩ : syracuseStep 46431739 = 69647609) B69647609
theorem B24387169 : Blo 1407523 24387169 := bstep (se 2 (by rfl) ⟨9145188, by rfl⟩ : syracuseStep 24387169 = 18290377) B18290377
theorem B3563291 : Blo 1407523 3563291 := bstep (se 1 (by rfl) ⟨2672468, by rfl⟩ : syracuseStep 3563291 = 5344937) B5344937
theorem B173532095 : Blo 1407523 173532095 := bstep (se 1 (by rfl) ⟨130149071, by rfl⟩ : syracuseStep 173532095 = 260298143) B260298143
theorem B61908985 : Blo 1407523 61908985 := bstep (se 2 (by rfl) ⟨23215869, by rfl⟩ : syracuseStep 61908985 = 46431739) B46431739
theorem B32516225 : Blo 1407523 32516225 := bstep (se 2 (by rfl) ⟨12193584, by rfl⟩ : syracuseStep 32516225 = 24387169) B24387169
theorem B4010219 : Blo 1407523 4010219 := bstep (se 1 (by rfl) ⟨3007664, by rfl⟩ : syracuseStep 4010219 = 6015329) B6015329
theorem B10695401 : Blo 1407523 10695401 := bstep (se 2 (by rfl) ⟨4010775, by rfl⟩ : syracuseStep 10695401 = 8021551) B8021551
theorem B6019103 : Blo 1407523 6019103 := bstep (se 1 (by rfl) ⟨4514327, by rfl⟩ : syracuseStep 6019103 = 9028655) B9028655
theorem B2112623 : Blo 1407523 2112623 := bstep (se 1 (by rfl) ⟨1584467, by rfl⟩ : syracuseStep 2112623 = 3168935) B3168935
theorem B3169583 : Blo 1407523 3169583 := bstep (se 1 (by rfl) ⟨2377187, by rfl⟩ : syracuseStep 3169583 = 4754375) B4754375
theorem B20594159 : Blo 1407523 20594159 := bstep (se 1 (by rfl) ⟨15445619, by rfl⟩ : syracuseStep 20594159 = 30891239) B30891239
theorem B2375527 : Blo 1407523 2375527 := bstep (se 1 (by rfl) ⟨1781645, by rfl⟩ : syracuseStep 2375527 = 3563291) B3563291
theorem B115688063 : Blo 1407523 115688063 := bstep (se 1 (by rfl) ⟨86766047, by rfl⟩ : syracuseStep 115688063 = 173532095) B173532095
theorem B21677483 : Blo 1407523 21677483 := bstep (se 1 (by rfl) ⟨16258112, by rfl⟩ : syracuseStep 21677483 = 32516225) B32516225
theorem B82545313 : Blo 1407523 82545313 := bstep (se 2 (by rfl) ⟨30954492, by rfl⟩ : syracuseStep 82545313 = 61908985) B61908985
theorem B2673479 : Blo 1407523 2673479 := bstep (se 1 (by rfl) ⟨2005109, by rfl⟩ : syracuseStep 2673479 = 4010219) B4010219
theorem B7130267 : Blo 1407523 7130267 := bstep (se 1 (by rfl) ⟨5347700, by rfl⟩ : syracuseStep 7130267 = 10695401) B10695401
theorem B3167369 : Blo 1407523 3167369 := bstep (se 2 (by rfl) ⟨1187763, by rfl⟩ : syracuseStep 3167369 = 2375527) B2375527
theorem B4012735 : Blo 1407523 4012735 := bstep (se 1 (by rfl) ⟨3009551, by rfl⟩ : syracuseStep 4012735 = 6019103) B6019103
theorem B1408415 : Blo 1407523 1408415 := bstep (se 1 (by rfl) ⟨1056311, by rfl⟩ : syracuseStep 1408415 = 2112623) B2112623
theorem B2113055 : Blo 1407523 2113055 := bstep (se 1 (by rfl) ⟨1584791, by rfl⟩ : syracuseStep 2113055 = 3169583) B3169583
theorem B13729439 : Blo 1407523 13729439 := bstep (se 1 (by rfl) ⟨10297079, by rfl⟩ : syracuseStep 13729439 = 20594159) B20594159
theorem B110060417 : Blo 1407523 110060417 := bstep (se 2 (by rfl) ⟨41272656, by rfl⟩ : syracuseStep 110060417 = 82545313) B82545313
theorem B5350313 : Blo 1407523 5350313 := bstep (se 2 (by rfl) ⟨2006367, by rfl⟩ : syracuseStep 5350313 = 4012735) B4012735
theorem B14451655 : Blo 1407523 14451655 := bstep (se 1 (by rfl) ⟨10838741, by rfl⟩ : syracuseStep 14451655 = 21677483) B21677483
theorem B4753511 : Blo 1407523 4753511 := bstep (se 1 (by rfl) ⟨3565133, by rfl⟩ : syracuseStep 4753511 = 7130267) B7130267
theorem B9152959 : Blo 1407523 9152959 := bstep (se 1 (by rfl) ⟨6864719, by rfl⟩ : syracuseStep 9152959 = 13729439) B13729439
theorem B1782319 : Blo 1407523 1782319 := bstep (se 1 (by rfl) ⟨1336739, by rfl⟩ : syracuseStep 1782319 = 2673479) B2673479
theorem B77125375 : Blo 1407523 77125375 := bstep (se 1 (by rfl) ⟨57844031, by rfl⟩ : syracuseStep 77125375 = 115688063) B115688063
theorem B2111579 : Blo 1407523 2111579 := bstep (se 1 (by rfl) ⟨1583684, by rfl⟩ : syracuseStep 2111579 = 3167369) B3167369
theorem B1408703 : Blo 1407523 1408703 := bstep (se 1 (by rfl) ⟨1056527, by rfl⟩ : syracuseStep 1408703 = 2113055) B2113055
theorem B2376425 : Blo 1407523 2376425 := bstep (se 2 (by rfl) ⟨891159, by rfl⟩ : syracuseStep 2376425 = 1782319) B1782319
theorem B19268873 : Blo 1407523 19268873 := bstep (se 2 (by rfl) ⟨7225827, by rfl⟩ : syracuseStep 19268873 = 14451655) B14451655
theorem B3566875 : Blo 1407523 3566875 := bstep (se 1 (by rfl) ⟨2675156, by rfl⟩ : syracuseStep 3566875 = 5350313) B5350313
theorem B12203945 : Blo 1407523 12203945 := bstep (se 2 (by rfl) ⟨4576479, by rfl⟩ : syracuseStep 12203945 = 9152959) B9152959
theorem B73373611 : Blo 1407523 73373611 := bstep (se 1 (by rfl) ⟨55030208, by rfl⟩ : syracuseStep 73373611 = 110060417) B110060417
theorem B411335333 : Blo 1407523 411335333 := bstep (se 4 (by rfl) ⟨38562687, by rfl⟩ : syracuseStep 411335333 = 77125375) B77125375
theorem B1407719 : Blo 1407523 1407719 := bstep (se 1 (by rfl) ⟨1055789, by rfl⟩ : syracuseStep 1407719 = 2111579) B2111579
theorem B3169007 : Blo 1407523 3169007 := bstep (se 1 (by rfl) ⟨2376755, by rfl⟩ : syracuseStep 3169007 = 4753511) B4753511
theorem B12845915 : Blo 1407523 12845915 := bstep (se 1 (by rfl) ⟨9634436, by rfl⟩ : syracuseStep 12845915 = 19268873) B19268873
theorem B8135963 : Blo 1407523 8135963 := bstep (se 1 (by rfl) ⟨6101972, by rfl⟩ : syracuseStep 8135963 = 12203945) B12203945
theorem B97831481 : Blo 1407523 97831481 := bstep (se 2 (by rfl) ⟨36686805, by rfl⟩ : syracuseStep 97831481 = 73373611) B73373611
theorem B1584283 : Blo 1407523 1584283 := bstep (se 1 (by rfl) ⟨1188212, by rfl⟩ : syracuseStep 1584283 = 2376425) B2376425
theorem B4755833 : Blo 1407523 4755833 := bstep (se 2 (by rfl) ⟨1783437, by rfl⟩ : syracuseStep 4755833 = 3566875) B3566875
theorem B274223555 : Blo 1407523 274223555 := bstep (se 1 (by rfl) ⟨205667666, by rfl⟩ : syracuseStep 274223555 = 411335333) B411335333
theorem B2112671 : Blo 1407523 2112671 := bstep (se 1 (by rfl) ⟨1584503, by rfl⟩ : syracuseStep 2112671 = 3169007) B3169007
theorem B3170555 : Blo 1407523 3170555 := bstep (se 1 (by rfl) ⟨2377916, by rfl⟩ : syracuseStep 3170555 = 4755833) B4755833
theorem B5423975 : Blo 1407523 5423975 := bstep (se 1 (by rfl) ⟨4067981, by rfl⟩ : syracuseStep 5423975 = 8135963) B8135963
theorem B182815703 : Blo 1407523 182815703 := bstep (se 1 (by rfl) ⟨137111777, by rfl⟩ : syracuseStep 182815703 = 274223555) B274223555
theorem B8563943 : Blo 1407523 8563943 := bstep (se 1 (by rfl) ⟨6422957, by rfl⟩ : syracuseStep 8563943 = 12845915) B12845915
theorem B1043535797 : Blo 1407523 1043535797 := bstep (se 5 (by rfl) ⟨48915740, by rfl⟩ : syracuseStep 1043535797 = 97831481) B97831481
theorem B2112377 : Blo 1407523 2112377 := bstep (se 2 (by rfl) ⟨792141, by rfl⟩ : syracuseStep 2112377 = 1584283) B1584283
theorem B1408447 : Blo 1407523 1408447 := bstep (se 1 (by rfl) ⟨1056335, by rfl⟩ : syracuseStep 1408447 = 2112671) B2112671
theorem B2113703 : Blo 1407523 2113703 := bstep (se 1 (by rfl) ⟨1585277, by rfl⟩ : syracuseStep 2113703 = 3170555) B3170555
theorem B695690531 : Blo 1407523 695690531 := bstep (se 1 (by rfl) ⟨521767898, by rfl⟩ : syracuseStep 695690531 = 1043535797) B1043535797
theorem B3615983 : Blo 1407523 3615983 := bstep (se 1 (by rfl) ⟨2711987, by rfl⟩ : syracuseStep 3615983 = 5423975) B5423975
theorem B121877135 : Blo 1407523 121877135 := bstep (se 1 (by rfl) ⟨91407851, by rfl⟩ : syracuseStep 121877135 = 182815703) B182815703
theorem B1408251 : Blo 1407523 1408251 := bstep (se 1 (by rfl) ⟨1056188, by rfl⟩ : syracuseStep 1408251 = 2112377) B2112377
theorem B5709295 : Blo 1407523 5709295 := bstep (se 1 (by rfl) ⟨4281971, by rfl⟩ : syracuseStep 5709295 = 8563943) B8563943
theorem B1409135 : Blo 1407523 1409135 := bstep (se 1 (by rfl) ⟨1056851, by rfl⟩ : syracuseStep 1409135 = 2113703) B2113703
theorem B7612393 : Blo 1407523 7612393 := bstep (se 2 (by rfl) ⟨2854647, by rfl⟩ : syracuseStep 7612393 = 5709295) B5709295
theorem B2410655 : Blo 1407523 2410655 := bstep (se 1 (by rfl) ⟨1807991, by rfl⟩ : syracuseStep 2410655 = 3615983) B3615983
theorem B81251423 : Blo 1407523 81251423 := bstep (se 1 (by rfl) ⟨60938567, by rfl⟩ : syracuseStep 81251423 = 121877135) B121877135
theorem B463793687 : Blo 1407523 463793687 := bstep (se 1 (by rfl) ⟨347845265, by rfl⟩ : syracuseStep 463793687 = 695690531) B695690531
theorem B54167615 : Blo 1407523 54167615 := bstep (se 1 (by rfl) ⟨40625711, by rfl⟩ : syracuseStep 54167615 = 81251423) B81251423
theorem B309195791 : Blo 1407523 309195791 := bstep (se 1 (by rfl) ⟨231896843, by rfl⟩ : syracuseStep 309195791 = 463793687) B463793687
theorem B6428413 : Blo 1407523 6428413 := bstep (se 3 (by rfl) ⟨1205327, by rfl⟩ : syracuseStep 6428413 = 2410655) B2410655
theorem B10149857 : Blo 1407523 10149857 := bstep (se 2 (by rfl) ⟨3806196, by rfl⟩ : syracuseStep 10149857 = 7612393) B7612393
theorem B34284869 : Blo 1407523 34284869 := bstep (se 4 (by rfl) ⟨3214206, by rfl⟩ : syracuseStep 34284869 = 6428413) B6428413
theorem B36111743 : Blo 1407523 36111743 := bstep (se 1 (by rfl) ⟨27083807, by rfl⟩ : syracuseStep 36111743 = 54167615) B54167615
theorem B206130527 : Blo 1407523 206130527 := bstep (se 1 (by rfl) ⟨154597895, by rfl⟩ : syracuseStep 206130527 = 309195791) B309195791
theorem B6766571 : Blo 1407523 6766571 := bstep (se 1 (by rfl) ⟨5074928, by rfl⟩ : syracuseStep 6766571 = 10149857) B10149857
theorem B22856579 : Blo 1407523 22856579 := bstep (se 1 (by rfl) ⟨17142434, by rfl⟩ : syracuseStep 22856579 = 34284869) B34284869
theorem B4511047 : Blo 1407523 4511047 := bstep (se 1 (by rfl) ⟨3383285, by rfl⟩ : syracuseStep 4511047 = 6766571) B6766571
theorem B24074495 : Blo 1407523 24074495 := bstep (se 1 (by rfl) ⟨18055871, by rfl⟩ : syracuseStep 24074495 = 36111743) B36111743
theorem B137420351 : Blo 1407523 137420351 := bstep (se 1 (by rfl) ⟨103065263, by rfl⟩ : syracuseStep 137420351 = 206130527) B206130527
theorem B15237719 : Blo 1407523 15237719 := bstep (se 1 (by rfl) ⟨11428289, by rfl⟩ : syracuseStep 15237719 = 22856579) B22856579
theorem B16049663 : Blo 1407523 16049663 := bstep (se 1 (by rfl) ⟨12037247, by rfl⟩ : syracuseStep 16049663 = 24074495) B24074495
theorem B6014729 : Blo 1407523 6014729 := bstep (se 2 (by rfl) ⟨2255523, by rfl⟩ : syracuseStep 6014729 = 4511047) B4511047
theorem B91613567 : Blo 1407523 91613567 := bstep (se 1 (by rfl) ⟨68710175, by rfl⟩ : syracuseStep 91613567 = 137420351) B137420351
theorem B10158479 : Blo 1407523 10158479 := bstep (se 1 (by rfl) ⟨7618859, by rfl⟩ : syracuseStep 10158479 = 15237719) B15237719
theorem B10699775 : Blo 1407523 10699775 := bstep (se 1 (by rfl) ⟨8024831, by rfl⟩ : syracuseStep 10699775 = 16049663) B16049663
theorem B4009819 : Blo 1407523 4009819 := bstep (se 1 (by rfl) ⟨3007364, by rfl⟩ : syracuseStep 4009819 = 6014729) B6014729
theorem B61075711 : Blo 1407523 61075711 := bstep (se 1 (by rfl) ⟨45806783, by rfl⟩ : syracuseStep 61075711 = 91613567) B91613567
theorem B5346425 : Blo 1407523 5346425 := bstep (se 2 (by rfl) ⟨2004909, by rfl⟩ : syracuseStep 5346425 = 4009819) B4009819
theorem B6772319 : Blo 1407523 6772319 := bstep (se 1 (by rfl) ⟨5079239, by rfl⟩ : syracuseStep 6772319 = 10158479) B10158479
theorem B81434281 : Blo 1407523 81434281 := bstep (se 2 (by rfl) ⟨30537855, by rfl⟩ : syracuseStep 81434281 = 61075711) B61075711
theorem B7133183 : Blo 1407523 7133183 := bstep (se 1 (by rfl) ⟨5349887, by rfl⟩ : syracuseStep 7133183 = 10699775) B10699775
theorem B3564283 : Blo 1407523 3564283 := bstep (se 1 (by rfl) ⟨2673212, by rfl⟩ : syracuseStep 3564283 = 5346425) B5346425
theorem B4514879 : Blo 1407523 4514879 := bstep (se 1 (by rfl) ⟨3386159, by rfl⟩ : syracuseStep 4514879 = 6772319) B6772319
theorem B108579041 : Blo 1407523 108579041 := bstep (se 2 (by rfl) ⟨40717140, by rfl⟩ : syracuseStep 108579041 = 81434281) B81434281
theorem B4755455 : Blo 1407523 4755455 := bstep (se 1 (by rfl) ⟨3566591, by rfl⟩ : syracuseStep 4755455 = 7133183) B7133183
theorem B3170303 : Blo 1407523 3170303 := bstep (se 1 (by rfl) ⟨2377727, by rfl⟩ : syracuseStep 3170303 = 4755455) B4755455
theorem B4752377 : Blo 1407523 4752377 := bstep (se 2 (by rfl) ⟨1782141, by rfl⟩ : syracuseStep 4752377 = 3564283) B3564283
theorem B72386027 : Blo 1407523 72386027 := bstep (se 1 (by rfl) ⟨54289520, by rfl⟩ : syracuseStep 72386027 = 108579041) B108579041
theorem B12039677 : Blo 1407523 12039677 := bstep (se 3 (by rfl) ⟨2257439, by rfl⟩ : syracuseStep 12039677 = 4514879) B4514879
theorem B2113535 : Blo 1407523 2113535 := bstep (se 1 (by rfl) ⟨1585151, by rfl⟩ : syracuseStep 2113535 = 3170303) B3170303
theorem B3168251 : Blo 1407523 3168251 := bstep (se 1 (by rfl) ⟨2376188, by rfl⟩ : syracuseStep 3168251 = 4752377) B4752377
theorem B48257351 : Blo 1407523 48257351 := bstep (se 1 (by rfl) ⟨36193013, by rfl⟩ : syracuseStep 48257351 = 72386027) B72386027
theorem B8026451 : Blo 1407523 8026451 := bstep (se 1 (by rfl) ⟨6019838, by rfl⟩ : syracuseStep 8026451 = 12039677) B12039677
theorem B32171567 : Blo 1407523 32171567 := bstep (se 1 (by rfl) ⟨24128675, by rfl⟩ : syracuseStep 32171567 = 48257351) B48257351
theorem B5350967 : Blo 1407523 5350967 := bstep (se 1 (by rfl) ⟨4013225, by rfl⟩ : syracuseStep 5350967 = 8026451) B8026451
theorem B2112167 : Blo 1407523 2112167 := bstep (se 1 (by rfl) ⟨1584125, by rfl⟩ : syracuseStep 2112167 = 3168251) B3168251
theorem B1409023 : Blo 1407523 1409023 := bstep (se 1 (by rfl) ⟨1056767, by rfl⟩ : syracuseStep 1409023 = 2113535) B2113535
theorem B3567311 : Blo 1407523 3567311 := bstep (se 1 (by rfl) ⟨2675483, by rfl⟩ : syracuseStep 3567311 = 5350967) B5350967
theorem B85790845 : Blo 1407523 85790845 := bstep (se 3 (by rfl) ⟨16085783, by rfl⟩ : syracuseStep 85790845 = 32171567) B32171567
theorem B1408111 : Blo 1407523 1408111 := bstep (se 1 (by rfl) ⟨1056083, by rfl⟩ : syracuseStep 1408111 = 2112167) B2112167
theorem B2378207 : Blo 1407523 2378207 := bstep (se 1 (by rfl) ⟨1783655, by rfl⟩ : syracuseStep 2378207 = 3567311) B3567311
theorem B457551173 : Blo 1407523 457551173 := bstep (se 4 (by rfl) ⟨42895422, by rfl⟩ : syracuseStep 457551173 = 85790845) B85790845
theorem B1585471 : Blo 1407523 1585471 := bstep (se 1 (by rfl) ⟨1189103, by rfl⟩ : syracuseStep 1585471 = 2378207) B2378207
theorem B305034115 : Blo 1407523 305034115 := bstep (se 1 (by rfl) ⟨228775586, by rfl⟩ : syracuseStep 305034115 = 457551173) B457551173
theorem B2113961 : Blo 1407523 2113961 := bstep (se 2 (by rfl) ⟨792735, by rfl⟩ : syracuseStep 2113961 = 1585471) B1585471
theorem B406712153 : Blo 1407523 406712153 := bstep (se 2 (by rfl) ⟨152517057, by rfl⟩ : syracuseStep 406712153 = 305034115) B305034115
theorem B1409307 : Blo 1407523 1409307 := bstep (se 1 (by rfl) ⟨1056980, by rfl⟩ : syracuseStep 1409307 = 2113961) B2113961
theorem B271141435 : Blo 1407523 271141435 := bstep (se 1 (by rfl) ⟨203356076, by rfl⟩ : syracuseStep 271141435 = 406712153) B406712153
theorem B1446087653 : Blo 1407523 1446087653 := bstep (se 4 (by rfl) ⟨135570717, by rfl⟩ : syracuseStep 1446087653 = 271141435) B271141435
theorem B964058435 : Blo 1407523 964058435 := bstep (se 1 (by rfl) ⟨723043826, by rfl⟩ : syracuseStep 964058435 = 1446087653) B1446087653
theorem B642705623 : Blo 1407523 642705623 := bstep (se 1 (by rfl) ⟨482029217, by rfl⟩ : syracuseStep 642705623 = 964058435) B964058435
theorem B428470415 : Blo 1407523 428470415 := bstep (se 1 (by rfl) ⟨321352811, by rfl⟩ : syracuseStep 428470415 = 642705623) B642705623
theorem B285646943 : Blo 1407523 285646943 := bstep (se 1 (by rfl) ⟨214235207, by rfl⟩ : syracuseStep 285646943 = 428470415) B428470415
theorem B761725181 : Blo 1407523 761725181 := bstep (se 3 (by rfl) ⟨142823471, by rfl⟩ : syracuseStep 761725181 = 285646943) B285646943
theorem B507816787 : Blo 1407523 507816787 := bstep (se 1 (by rfl) ⟨380862590, by rfl⟩ : syracuseStep 507816787 = 761725181) B761725181
theorem B677089049 : Blo 1407523 677089049 := bstep (se 2 (by rfl) ⟨253908393, by rfl⟩ : syracuseStep 677089049 = 507816787) B507816787
theorem B1805570797 : Blo 1407523 1805570797 := bstep (se 3 (by rfl) ⟨338544524, by rfl⟩ : syracuseStep 1805570797 = 677089049) B677089049
theorem B2407427729 : Blo 1407523 2407427729 := bstep (se 2 (by rfl) ⟨902785398, by rfl⟩ : syracuseStep 2407427729 = 1805570797) B1805570797
theorem B1604951819 : Blo 1407523 1604951819 := bstep (se 1 (by rfl) ⟨1203713864, by rfl⟩ : syracuseStep 1604951819 = 2407427729) B2407427729
theorem B1069967879 : Blo 1407523 1069967879 := bstep (se 1 (by rfl) ⟨802475909, by rfl⟩ : syracuseStep 1069967879 = 1604951819) B1604951819
theorem B713311919 : Blo 1407523 713311919 := bstep (se 1 (by rfl) ⟨534983939, by rfl⟩ : syracuseStep 713311919 = 1069967879) B1069967879
theorem B475541279 : Blo 1407523 475541279 := bstep (se 1 (by rfl) ⟨356655959, by rfl⟩ : syracuseStep 475541279 = 713311919) B713311919
theorem B317027519 : Blo 1407523 317027519 := bstep (se 1 (by rfl) ⟨237770639, by rfl⟩ : syracuseStep 317027519 = 475541279) B475541279
theorem B211351679 : Blo 1407523 211351679 := bstep (se 1 (by rfl) ⟨158513759, by rfl⟩ : syracuseStep 211351679 = 317027519) B317027519
theorem B140901119 : Blo 1407523 140901119 := bstep (se 1 (by rfl) ⟨105675839, by rfl⟩ : syracuseStep 140901119 = 211351679) B211351679
theorem B93934079 : Blo 1407523 93934079 := bstep (se 1 (by rfl) ⟨70450559, by rfl⟩ : syracuseStep 93934079 = 140901119) B140901119
theorem B62622719 : Blo 1407523 62622719 := bstep (se 1 (by rfl) ⟨46967039, by rfl⟩ : syracuseStep 62622719 = 93934079) B93934079
theorem B41748479 : Blo 1407523 41748479 := bstep (se 1 (by rfl) ⟨31311359, by rfl⟩ : syracuseStep 41748479 = 62622719) B62622719
theorem B27832319 : Blo 1407523 27832319 := bstep (se 1 (by rfl) ⟨20874239, by rfl⟩ : syracuseStep 27832319 = 41748479) B41748479
theorem B18554879 : Blo 1407523 18554879 := bstep (se 1 (by rfl) ⟨13916159, by rfl⟩ : syracuseStep 18554879 = 27832319) B27832319
theorem B12369919 : Blo 1407523 12369919 := bstep (se 1 (by rfl) ⟨9277439, by rfl⟩ : syracuseStep 12369919 = 18554879) B18554879
theorem B16493225 : Blo 1407523 16493225 := bstep (se 2 (by rfl) ⟨6184959, by rfl⟩ : syracuseStep 16493225 = 12369919) B12369919
theorem B175927733 : Blo 1407523 175927733 := bstep (se 5 (by rfl) ⟨8246612, by rfl⟩ : syracuseStep 175927733 = 16493225) B16493225
theorem B117285155 : Blo 1407523 117285155 := bstep (se 1 (by rfl) ⟨87963866, by rfl⟩ : syracuseStep 117285155 = 175927733) B175927733
theorem B78190103 : Blo 1407523 78190103 := bstep (se 1 (by rfl) ⟨58642577, by rfl⟩ : syracuseStep 78190103 = 117285155) B117285155
theorem B52126735 : Blo 1407523 52126735 := bstep (se 1 (by rfl) ⟨39095051, by rfl⟩ : syracuseStep 52126735 = 78190103) B78190103
theorem B69502313 : Blo 1407523 69502313 := bstep (se 2 (by rfl) ⟨26063367, by rfl⟩ : syracuseStep 69502313 = 52126735) B52126735
theorem B46334875 : Blo 1407523 46334875 := bstep (se 1 (by rfl) ⟨34751156, by rfl⟩ : syracuseStep 46334875 = 69502313) B69502313
theorem B61779833 : Blo 1407523 61779833 := bstep (se 2 (by rfl) ⟨23167437, by rfl⟩ : syracuseStep 61779833 = 46334875) B46334875
theorem B41186555 : Blo 1407523 41186555 := bstep (se 1 (by rfl) ⟨30889916, by rfl⟩ : syracuseStep 41186555 = 61779833) B61779833
theorem B27457703 : Blo 1407523 27457703 := bstep (se 1 (by rfl) ⟨20593277, by rfl⟩ : syracuseStep 27457703 = 41186555) B41186555
theorem B18305135 : Blo 1407523 18305135 := bstep (se 1 (by rfl) ⟨13728851, by rfl⟩ : syracuseStep 18305135 = 27457703) B27457703
theorem B12203423 : Blo 1407523 12203423 := bstep (se 1 (by rfl) ⟨9152567, by rfl⟩ : syracuseStep 12203423 = 18305135) B18305135
theorem B8135615 : Blo 1407523 8135615 := bstep (se 1 (by rfl) ⟨6101711, by rfl⟩ : syracuseStep 8135615 = 12203423) B12203423
theorem B5423743 : Blo 1407523 5423743 := bstep (se 1 (by rfl) ⟨4067807, by rfl⟩ : syracuseStep 5423743 = 8135615) B8135615
theorem B28926629 : Blo 1407523 28926629 := bstep (se 4 (by rfl) ⟨2711871, by rfl⟩ : syracuseStep 28926629 = 5423743) B5423743
theorem B19284419 : Blo 1407523 19284419 := bstep (se 1 (by rfl) ⟨14463314, by rfl⟩ : syracuseStep 19284419 = 28926629) B28926629
theorem B51425117 : Blo 1407523 51425117 := bstep (se 3 (by rfl) ⟨9642209, by rfl⟩ : syracuseStep 51425117 = 19284419) B19284419
theorem B34283411 : Blo 1407523 34283411 := bstep (se 1 (by rfl) ⟨25712558, by rfl⟩ : syracuseStep 34283411 = 51425117) B51425117
theorem B22855607 : Blo 1407523 22855607 := bstep (se 1 (by rfl) ⟨17141705, by rfl⟩ : syracuseStep 22855607 = 34283411) B34283411
theorem B15237071 : Blo 1407523 15237071 := bstep (se 1 (by rfl) ⟨11427803, by rfl⟩ : syracuseStep 15237071 = 22855607) B22855607
theorem B10158047 : Blo 1407523 10158047 := bstep (se 1 (by rfl) ⟨7618535, by rfl⟩ : syracuseStep 10158047 = 15237071) B15237071
theorem B6772031 : Blo 1407523 6772031 := bstep (se 1 (by rfl) ⟨5079023, by rfl⟩ : syracuseStep 6772031 = 10158047) B10158047
theorem B4514687 : Blo 1407523 4514687 := bstep (se 1 (by rfl) ⟨3386015, by rfl⟩ : syracuseStep 4514687 = 6772031) B6772031
theorem B3009791 : Blo 1407523 3009791 := bstep (se 1 (by rfl) ⟨2257343, by rfl⟩ : syracuseStep 3009791 = 4514687) B4514687
theorem B2006527 : Blo 1407523 2006527 := bstep (se 1 (by rfl) ⟨1504895, by rfl⟩ : syracuseStep 2006527 = 3009791) B3009791
theorem B2675369 : Blo 1407523 2675369 := bstep (se 2 (by rfl) ⟨1003263, by rfl⟩ : syracuseStep 2675369 = 2006527) B2006527
theorem B7134317 : Blo 1407523 7134317 := bstep (se 3 (by rfl) ⟨1337684, by rfl⟩ : syracuseStep 7134317 = 2675369) B2675369
theorem B4756211 : Blo 1407523 4756211 := bstep (se 1 (by rfl) ⟨3567158, by rfl⟩ : syracuseStep 4756211 = 7134317) B7134317
theorem B3170807 : Blo 1407523 3170807 := bstep (se 1 (by rfl) ⟨2378105, by rfl⟩ : syracuseStep 3170807 = 4756211) B4756211
theorem B2113871 : Blo 1407523 2113871 := bstep (se 1 (by rfl) ⟨1585403, by rfl⟩ : syracuseStep 2113871 = 3170807) B3170807
theorem B1409247 : Blo 1407523 1409247 := bstep (se 1 (by rfl) ⟨1056935, by rfl⟩ : syracuseStep 1409247 = 2113871) B2113871

theorem C0 (j : ℕ) (h1 : 351880 ≤ j) (h2 : j ≤ 352380) : Blo 1407523 (4 * j + 3) := by
  interval_cases j
  · exact B1407523
  · exact B1407527
  · exact B1407531
  · exact B1407535
  · exact B1407539
  · exact B1407543
  · exact B1407547
  · exact B1407551
  · exact B1407555
  · exact B1407559
  · exact B1407563
  · exact B1407567
  · exact B1407571
  · exact B1407575
  · exact B1407579
  · exact B1407583
  · exact B1407587
  · exact B1407591
  · exact B1407595
  · exact B1407599
  · exact B1407603
  · exact B1407607
  · exact B1407611
  · exact B1407615
  · exact B1407619
  · exact B1407623
  · exact B1407627
  · exact B1407631
  · exact B1407635
  · exact B1407639
  · exact B1407643
  · exact B1407647
  · exact B1407651
  · exact B1407655
  · exact B1407659
  · exact B1407663
  · exact B1407667
  · exact B1407671
  · exact B1407675
  · exact B1407679
  · exact B1407683
  · exact B1407687
  · exact B1407691
  · exact B1407695
  · exact B1407699
  · exact B1407703
  · exact B1407707
  · exact B1407711
  · exact B1407715
  · exact B1407719
  · exact B1407723
  · exact B1407727
  · exact B1407731
  · exact B1407735
  · exact B1407739
  · exact B1407743
  · exact B1407747
  · exact B1407751
  · exact B1407755
  · exact B1407759
  · exact B1407763
  · exact B1407767
  · exact B1407771
  · exact B1407775
  · exact B1407779
  · exact B1407783
  · exact B1407787
  · exact B1407791
  · exact B1407795
  · exact B1407799
  · exact B1407803
  · exact B1407807
  · exact B1407811
  · exact B1407815
  · exact B1407819
  · exact B1407823
  · exact B1407827
  · exact B1407831
  · exact B1407835
  · exact B1407839
  · exact B1407843
  · exact B1407847
  · exact B1407851
  · exact B1407855
  · exact B1407859
  · exact B1407863
  · exact B1407867
  · exact B1407871
  · exact B1407875
  · exact B1407879
  · exact B1407883
  · exact B1407887
  · exact B1407891
  · exact B1407895
  · exact B1407899
  · exact B1407903
  · exact B1407907
  · exact B1407911
  · exact B1407915
  · exact B1407919
  · exact B1407923
  · exact B1407927
  · exact B1407931
  · exact B1407935
  · exact B1407939
  · exact B1407943
  · exact B1407947
  · exact B1407951
  · exact B1407955
  · exact B1407959
  · exact B1407963
  · exact B1407967
  · exact B1407971
  · exact B1407975
  · exact B1407979
  · exact B1407983
  · exact B1407987
  · exact B1407991
  · exact B1407995
  · exact B1407999
  · exact B1408003
  · exact B1408007
  · exact B1408011
  · exact B1408015
  · exact B1408019
  · exact B1408023
  · exact B1408027
  · exact B1408031
  · exact B1408035
  · exact B1408039
  · exact B1408043
  · exact B1408047
  · exact B1408051
  · exact B1408055
  · exact B1408059
  · exact B1408063
  · exact B1408067
  · exact B1408071
  · exact B1408075
  · exact B1408079
  · exact B1408083
  · exact B1408087
  · exact B1408091
  · exact B1408095
  · exact B1408099
  · exact B1408103
  · exact B1408107
  · exact B1408111
  · exact B1408115
  · exact B1408119
  · exact B1408123
  · exact B1408127
  · exact B1408131
  · exact B1408135
  · exact B1408139
  · exact B1408143
  · exact B1408147
  · exact B1408151
  · exact B1408155
  · exact B1408159
  · exact B1408163
  · exact B1408167
  · exact B1408171
  · exact B1408175
  · exact B1408179
  · exact B1408183
  · exact B1408187
  · exact B1408191
  · exact B1408195
  · exact B1408199
  · exact B1408203
  · exact B1408207
  · exact B1408211
  · exact B1408215
  · exact B1408219
  · exact B1408223
  · exact B1408227
  · exact B1408231
  · exact B1408235
  · exact B1408239
  · exact B1408243
  · exact B1408247
  · exact B1408251
  · exact B1408255
  · exact B1408259
  · exact B1408263
  · exact B1408267
  · exact B1408271
  · exact B1408275
  · exact B1408279
  · exact B1408283
  · exact B1408287
  · exact B1408291
  · exact B1408295
  · exact B1408299
  · exact B1408303
  · exact B1408307
  · exact B1408311
  · exact B1408315
  · exact B1408319
  · exact B1408323
  · exact B1408327
  · exact B1408331
  · exact B1408335
  · exact B1408339
  · exact B1408343
  · exact B1408347
  · exact B1408351
  · exact B1408355
  · exact B1408359
  · exact B1408363
  · exact B1408367
  · exact B1408371
  · exact B1408375
  · exact B1408379
  · exact B1408383
  · exact B1408387
  · exact B1408391
  · exact B1408395
  · exact B1408399
  · exact B1408403
  · exact B1408407
  · exact B1408411
  · exact B1408415
  · exact B1408419
  · exact B1408423
  · exact B1408427
  · exact B1408431
  · exact B1408435
  · exact B1408439
  · exact B1408443
  · exact B1408447
  · exact B1408451
  · exact B1408455
  · exact B1408459
  · exact B1408463
  · exact B1408467
  · exact B1408471
  · exact B1408475
  · exact B1408479
  · exact B1408483
  · exact B1408487
  · exact B1408491
  · exact B1408495
  · exact B1408499
  · exact B1408503
  · exact B1408507
  · exact B1408511
  · exact B1408515
  · exact B1408519
  · exact B1408523
  · exact B1408527
  · exact B1408531
  · exact B1408535
  · exact B1408539
  · exact B1408543
  · exact B1408547
  · exact B1408551
  · exact B1408555
  · exact B1408559
  · exact B1408563
  · exact B1408567
  · exact B1408571
  · exact B1408575
  · exact B1408579
  · exact B1408583
  · exact B1408587
  · exact B1408591
  · exact B1408595
  · exact B1408599
  · exact B1408603
  · exact B1408607
  · exact B1408611
  · exact B1408615
  · exact B1408619
  · exact B1408623
  · exact B1408627
  · exact B1408631
  · exact B1408635
  · exact B1408639
  · exact B1408643
  · exact B1408647
  · exact B1408651
  · exact B1408655
  · exact B1408659
  · exact B1408663
  · exact B1408667
  · exact B1408671
  · exact B1408675
  · exact B1408679
  · exact B1408683
  · exact B1408687
  · exact B1408691
  · exact B1408695
  · exact B1408699
  · exact B1408703
  · exact B1408707
  · exact B1408711
  · exact B1408715
  · exact B1408719
  · exact B1408723
  · exact B1408727
  · exact B1408731
  · exact B1408735
  · exact B1408739
  · exact B1408743
  · exact B1408747
  · exact B1408751
  · exact B1408755
  · exact B1408759
  · exact B1408763
  · exact B1408767
  · exact B1408771
  · exact B1408775
  · exact B1408779
  · exact B1408783
  · exact B1408787
  · exact B1408791
  · exact B1408795
  · exact B1408799
  · exact B1408803
  · exact B1408807
  · exact B1408811
  · exact B1408815
  · exact B1408819
  · exact B1408823
  · exact B1408827
  · exact B1408831
  · exact B1408835
  · exact B1408839
  · exact B1408843
  · exact B1408847
  · exact B1408851
  · exact B1408855
  · exact B1408859
  · exact B1408863
  · exact B1408867
  · exact B1408871
  · exact B1408875
  · exact B1408879
  · exact B1408883
  · exact B1408887
  · exact B1408891
  · exact B1408895
  · exact B1408899
  · exact B1408903
  · exact B1408907
  · exact B1408911
  · exact B1408915
  · exact B1408919
  · exact B1408923
  · exact B1408927
  · exact B1408931
  · exact B1408935
  · exact B1408939
  · exact B1408943
  · exact B1408947
  · exact B1408951
  · exact B1408955
  · exact B1408959
  · exact B1408963
  · exact B1408967
  · exact B1408971
  · exact B1408975
  · exact B1408979
  · exact B1408983
  · exact B1408987
  · exact B1408991
  · exact B1408995
  · exact B1408999
  · exact B1409003
  · exact B1409007
  · exact B1409011
  · exact B1409015
  · exact B1409019
  · exact B1409023
  · exact B1409027
  · exact B1409031
  · exact B1409035
  · exact B1409039
  · exact B1409043
  · exact B1409047
  · exact B1409051
  · exact B1409055
  · exact B1409059
  · exact B1409063
  · exact B1409067
  · exact B1409071
  · exact B1409075
  · exact B1409079
  · exact B1409083
  · exact B1409087
  · exact B1409091
  · exact B1409095
  · exact B1409099
  · exact B1409103
  · exact B1409107
  · exact B1409111
  · exact B1409115
  · exact B1409119
  · exact B1409123
  · exact B1409127
  · exact B1409131
  · exact B1409135
  · exact B1409139
  · exact B1409143
  · exact B1409147
  · exact B1409151
  · exact B1409155
  · exact B1409159
  · exact B1409163
  · exact B1409167
  · exact B1409171
  · exact B1409175
  · exact B1409179
  · exact B1409183
  · exact B1409187
  · exact B1409191
  · exact B1409195
  · exact B1409199
  · exact B1409203
  · exact B1409207
  · exact B1409211
  · exact B1409215
  · exact B1409219
  · exact B1409223
  · exact B1409227
  · exact B1409231
  · exact B1409235
  · exact B1409239
  · exact B1409243
  · exact B1409247
  · exact B1409251
  · exact B1409255
  · exact B1409259
  · exact B1409263
  · exact B1409267
  · exact B1409271
  · exact B1409275
  · exact B1409279
  · exact B1409283
  · exact B1409287
  · exact B1409291
  · exact B1409295
  · exact B1409299
  · exact B1409303
  · exact B1409307
  · exact B1409311
  · exact B1409315
  · exact B1409319
  · exact B1409323
  · exact B1409327
  · exact B1409331
  · exact B1409335
  · exact B1409339
  · exact B1409343
  · exact B1409347
  · exact B1409351
  · exact B1409355
  · exact B1409359
  · exact B1409363
  · exact B1409367
  · exact B1409371
  · exact B1409375
  · exact B1409379
  · exact B1409383
  · exact B1409387
  · exact B1409391
  · exact B1409395
  · exact B1409399
  · exact B1409403
  · exact B1409407
  · exact B1409411
  · exact B1409415
  · exact B1409419
  · exact B1409423
  · exact B1409427
  · exact B1409431
  · exact B1409435
  · exact B1409439
  · exact B1409443
  · exact B1409447
  · exact B1409451
  · exact B1409455
  · exact B1409459
  · exact B1409463
  · exact B1409467
  · exact B1409471
  · exact B1409475
  · exact B1409479
  · exact B1409483
  · exact B1409487
  · exact B1409491
  · exact B1409495
  · exact B1409499
  · exact B1409503
  · exact B1409507
  · exact B1409511
  · exact B1409515
  · exact B1409519
  · exact B1409523

theorem solution (m : ℕ) (hlo : 1407523 ≤ m) (hhi : m ≤ 1409523) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 351880 ≤ j := by omega
    have hj2 : j ≤ 352380 := by omega
    have hb : Blo 1407523 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
