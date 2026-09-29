-- Prove2me | solution 1 for syracuse_descends_range_1532463_1534463
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:04:47.588017+00:00
-- url     : https://prove2.me/submissions/745c18e9-4ca3-49cf-aa34-463011e83505

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


theorem B1941509 : Blo 1532463 1941509 := bbase (se 4 (by rfl) ⟨182016, by rfl⟩ : syracuseStep 1941509 = 364033) (by norm_num)
theorem B3448853 : Blo 1532463 3448853 := bbase (se 6 (by rfl) ⟨80832, by rfl⟩ : syracuseStep 3448853 = 161665) (by norm_num)
theorem B1941565 : Blo 1532463 1941565 := bbase (se 3 (by rfl) ⟨364043, by rfl⟩ : syracuseStep 1941565 = 728087) (by norm_num)
theorem B1638473 : Blo 1532463 1638473 := bbase (se 2 (by rfl) ⟨614427, by rfl⟩ : syracuseStep 1638473 = 1228855) (by norm_num)
theorem B3448925 : Blo 1532463 3448925 := bbase (se 3 (by rfl) ⟨646673, by rfl⟩ : syracuseStep 3448925 = 1293347) (by norm_num)
theorem B7766117 : Blo 1532463 7766117 := bbase (se 4 (by rfl) ⟨728073, by rfl⟩ : syracuseStep 7766117 = 1456147) (by norm_num)
theorem B2588773 : Blo 1532463 2588773 := bbase (se 4 (by rfl) ⟨242697, by rfl⟩ : syracuseStep 2588773 = 485395) (by norm_num)
theorem B1843321 : Blo 1532463 1843321 := bbase (se 2 (by rfl) ⟨691245, by rfl⟩ : syracuseStep 1843321 = 1382491) (by norm_num)
theorem B7471237 : Blo 1532463 7471237 := bbase (se 4 (by rfl) ⟨700428, by rfl⟩ : syracuseStep 7471237 = 1400857) (by norm_num)
theorem B15949973 : Blo 1532463 15949973 := bbase (se 6 (by rfl) ⟨373827, by rfl⟩ : syracuseStep 15949973 = 747655) (by norm_num)
theorem B1941661 : Blo 1532463 1941661 := bbase (se 3 (by rfl) ⟨364061, by rfl⟩ : syracuseStep 1941661 = 728123) (by norm_num)
theorem B3448997 : Blo 1532463 3448997 := bbase (se 4 (by rfl) ⟨323343, by rfl⟩ : syracuseStep 3448997 = 646687) (by norm_num)
theorem B2588861 : Blo 1532463 2588861 := bbase (se 3 (by rfl) ⟨485411, by rfl⟩ : syracuseStep 2588861 = 970823) (by norm_num)
theorem B1843417 : Blo 1532463 1843417 := bbase (se 2 (by rfl) ⟨691281, by rfl⟩ : syracuseStep 1843417 = 1382563) (by norm_num)
theorem B5177573 : Blo 1532463 5177573 := bbase (se 4 (by rfl) ⟨485397, by rfl⟩ : syracuseStep 5177573 = 970795) (by norm_num)
theorem B3449069 : Blo 1532463 3449069 := bbase (se 3 (by rfl) ⟨646700, by rfl⟩ : syracuseStep 3449069 = 1293401) (by norm_num)
theorem B3883261 : Blo 1532463 3883261 := bbase (se 3 (by rfl) ⟨728111, by rfl⟩ : syracuseStep 3883261 = 1456223) (by norm_num)
theorem B9822485 : Blo 1532463 9822485 := bbase (se 6 (by rfl) ⟨230214, by rfl⟩ : syracuseStep 9822485 = 460429) (by norm_num)
theorem B2457877 : Blo 1532463 2457877 := bbase (se 6 (by rfl) ⟨57606, by rfl⟩ : syracuseStep 2457877 = 115213) (by norm_num)
theorem B3449141 : Blo 1532463 3449141 := bbase (se 5 (by rfl) ⟨161678, by rfl⟩ : syracuseStep 3449141 = 323357) (by norm_num)
theorem B2588989 : Blo 1532463 2588989 := bbase (se 3 (by rfl) ⟨485435, by rfl⟩ : syracuseStep 2588989 = 970871) (by norm_num)
theorem B1941833 : Blo 1532463 1941833 := bbase (se 2 (by rfl) ⟨728187, by rfl⟩ : syracuseStep 1941833 = 1456375) (by norm_num)
theorem B3883373 : Blo 1532463 3883373 := bbase (se 3 (by rfl) ⟨728132, by rfl⟩ : syracuseStep 3883373 = 1456265) (by norm_num)
theorem B3449213 : Blo 1532463 3449213 := bbase (se 3 (by rfl) ⟨646727, by rfl⟩ : syracuseStep 3449213 = 1293455) (by norm_num)
theorem B1941889 : Blo 1532463 1941889 := bbase (se 2 (by rfl) ⟨728208, by rfl⟩ : syracuseStep 1941889 = 1456417) (by norm_num)
theorem B2589077 : Blo 1532463 2589077 := bbase (se 6 (by rfl) ⟨60681, by rfl⟩ : syracuseStep 2589077 = 121363) (by norm_num)
theorem B3449285 : Blo 1532463 3449285 := bbase (se 4 (by rfl) ⟨323370, by rfl⟩ : syracuseStep 3449285 = 646741) (by norm_num)
theorem B1941985 : Blo 1532463 1941985 := bbase (se 2 (by rfl) ⟨728244, by rfl⟩ : syracuseStep 1941985 = 1456489) (by norm_num)
theorem B7758341 : Blo 1532463 7758341 := bbase (se 4 (by rfl) ⟨727344, by rfl⟩ : syracuseStep 7758341 = 1454689) (by norm_num)
theorem B3449357 : Blo 1532463 3449357 := bbase (se 3 (by rfl) ⟨646754, by rfl⟩ : syracuseStep 3449357 = 1293509) (by norm_num)
theorem B2589205 : Blo 1532463 2589205 := bbase (se 6 (by rfl) ⟨60684, by rfl⟩ : syracuseStep 2589205 = 121369) (by norm_num)
theorem B3883565 : Blo 1532463 3883565 := bbase (se 3 (by rfl) ⟨728168, by rfl⟩ : syracuseStep 3883565 = 1456337) (by norm_num)
theorem B3449429 : Blo 1532463 3449429 := bbase (se 8 (by rfl) ⟨20211, by rfl⟩ : syracuseStep 3449429 = 40423) (by norm_num)
theorem B7864933 : Blo 1532463 7864933 := bbase (se 4 (by rfl) ⟨737337, by rfl⟩ : syracuseStep 7864933 = 1474675) (by norm_num)
theorem B2589293 : Blo 1532463 2589293 := bbase (se 3 (by rfl) ⟨485492, by rfl⟩ : syracuseStep 2589293 = 970985) (by norm_num)
theorem B7365269 : Blo 1532463 7365269 := bbase (se 6 (by rfl) ⟨172623, by rfl⟩ : syracuseStep 7365269 = 345247) (by norm_num)
theorem B5178005 : Blo 1532463 5178005 := bbase (se 6 (by rfl) ⟨121359, by rfl⟩ : syracuseStep 5178005 = 242719) (by norm_num)
theorem B3449501 : Blo 1532463 3449501 := bbase (se 3 (by rfl) ⟨646781, by rfl⟩ : syracuseStep 3449501 = 1293563) (by norm_num)
theorem B4367029 : Blo 1532463 4367029 := bbase (se 5 (by rfl) ⟨204704, by rfl⟩ : syracuseStep 4367029 = 409409) (by norm_num)
theorem B3449573 : Blo 1532463 3449573 := bbase (se 4 (by rfl) ⟨323397, by rfl⟩ : syracuseStep 3449573 = 646795) (by norm_num)
theorem B5899013 : Blo 1532463 5899013 := bbase (se 4 (by rfl) ⟨553032, by rfl⟩ : syracuseStep 5899013 = 1106065) (by norm_num)
theorem B3498773 : Blo 1532463 3498773 := bbase (se 6 (by rfl) ⟨82002, by rfl⟩ : syracuseStep 3498773 = 164005) (by norm_num)
theorem B5825317 : Blo 1532463 5825317 := bbase (se 4 (by rfl) ⟨546123, by rfl⟩ : syracuseStep 5825317 = 1092247) (by norm_num)
theorem B3449645 : Blo 1532463 3449645 := bbase (se 3 (by rfl) ⟨646808, by rfl⟩ : syracuseStep 3449645 = 1293617) (by norm_num)
theorem B4367189 : Blo 1532463 4367189 := bbase (se 9 (by rfl) ⟨12794, by rfl⟩ : syracuseStep 4367189 = 25589) (by norm_num)
theorem B3449717 : Blo 1532463 3449717 := bbase (se 5 (by rfl) ⟨161705, by rfl⟩ : syracuseStep 3449717 = 323411) (by norm_num)
theorem B3883909 : Blo 1532463 3883909 := bbase (se 4 (by rfl) ⟨364116, by rfl⟩ : syracuseStep 3883909 = 728233) (by norm_num)
theorem B1966993 : Blo 1532463 1966993 := bbase (se 2 (by rfl) ⟨737622, by rfl⟩ : syracuseStep 1966993 = 1475245) (by norm_num)
theorem B3449789 : Blo 1532463 3449789 := bbase (se 3 (by rfl) ⟨646835, by rfl⟩ : syracuseStep 3449789 = 1293671) (by norm_num)
theorem B3884021 : Blo 1532463 3884021 := bbase (se 5 (by rfl) ⟨182063, by rfl⟩ : syracuseStep 3884021 = 364127) (by norm_num)
theorem B3449861 : Blo 1532463 3449861 := bbase (se 4 (by rfl) ⟨323424, by rfl⟩ : syracuseStep 3449861 = 646849) (by norm_num)
theorem B3499013 : Blo 1532463 3499013 := bbase (se 4 (by rfl) ⟨328032, by rfl⟩ : syracuseStep 3499013 = 656065) (by norm_num)
theorem B2802701 : Blo 1532463 2802701 := bbase (se 3 (by rfl) ⟨525506, by rfl⟩ : syracuseStep 2802701 = 1051013) (by norm_num)
theorem B2212925 : Blo 1532463 2212925 := bbase (se 3 (by rfl) ⟨414923, by rfl⟩ : syracuseStep 2212925 = 829847) (by norm_num)
theorem B4367429 : Blo 1532463 4367429 := bbase (se 4 (by rfl) ⟨409446, by rfl⟩ : syracuseStep 4367429 = 818893) (by norm_num)
theorem B5178437 : Blo 1532463 5178437 := bbase (se 4 (by rfl) ⟨485478, by rfl⟩ : syracuseStep 5178437 = 970957) (by norm_num)
theorem B3449933 : Blo 1532463 3449933 := bbase (se 3 (by rfl) ⟨646862, by rfl⟩ : syracuseStep 3449933 = 1293725) (by norm_num)
theorem B5825621 : Blo 1532463 5825621 := bbase (se 8 (by rfl) ⟨34134, by rfl⟩ : syracuseStep 5825621 = 68269) (by norm_num)
theorem B2909333 : Blo 1532463 2909333 := bbase (se 6 (by rfl) ⟨68187, by rfl⟩ : syracuseStep 2909333 = 136375) (by norm_num)
theorem B6546581 : Blo 1532463 6546581 := bbase (se 6 (by rfl) ⟨153435, by rfl⟩ : syracuseStep 6546581 = 306871) (by norm_num)
theorem B22103189 : Blo 1532463 22103189 := bbase (se 6 (by rfl) ⟨518043, by rfl⟩ : syracuseStep 22103189 = 1036087) (by norm_num)
theorem B3450005 : Blo 1532463 3450005 := bbase (se 6 (by rfl) ⟨80859, by rfl⟩ : syracuseStep 3450005 = 161719) (by norm_num)
theorem B3450077 : Blo 1532463 3450077 := bbase (se 3 (by rfl) ⟨646889, by rfl⟩ : syracuseStep 3450077 = 1293779) (by norm_num)
theorem B4367621 : Blo 1532463 4367621 := bbase (se 4 (by rfl) ⟨409464, by rfl⟩ : syracuseStep 4367621 = 818929) (by norm_num)
theorem B3450149 : Blo 1532463 3450149 := bbase (se 4 (by rfl) ⟨323451, by rfl⟩ : syracuseStep 3450149 = 646903) (by norm_num)
theorem B62956885 : Blo 1532463 62956885 := bbase (se 12 (by rfl) ⟨23055, by rfl⟩ : syracuseStep 62956885 = 46111) (by norm_num)
theorem B2762093 : Blo 1532463 2762093 := bbase (se 3 (by rfl) ⟨517892, by rfl⟩ : syracuseStep 2762093 = 1035785) (by norm_num)
theorem B3450221 : Blo 1532463 3450221 := bbase (se 3 (by rfl) ⟨646916, by rfl⟩ : syracuseStep 3450221 = 1293833) (by norm_num)
theorem B7767413 : Blo 1532463 7767413 := bbase (se 5 (by rfl) ⟨364097, by rfl⟩ : syracuseStep 7767413 = 728195) (by norm_num)
theorem B2909621 : Blo 1532463 2909621 := bbase (se 5 (by rfl) ⟨136388, by rfl⟩ : syracuseStep 2909621 = 272777) (by norm_num)
theorem B3450293 : Blo 1532463 3450293 := bbase (se 5 (by rfl) ⟨161732, by rfl⟩ : syracuseStep 3450293 = 323465) (by norm_num)
theorem B3450365 : Blo 1532463 3450365 := bbase (se 3 (by rfl) ⟨646943, by rfl⟩ : syracuseStep 3450365 = 1293887) (by norm_num)
theorem B5678629 : Blo 1532463 5678629 := bbase (se 4 (by rfl) ⟨532371, by rfl⟩ : syracuseStep 5678629 = 1064743) (by norm_num)
theorem B3450437 : Blo 1532463 3450437 := bbase (se 4 (by rfl) ⟨323478, by rfl⟩ : syracuseStep 3450437 = 646957) (by norm_num)
theorem B2909773 : Blo 1532463 2909773 := bbase (se 3 (by rfl) ⟨545582, by rfl⟩ : syracuseStep 2909773 = 1091165) (by norm_num)
theorem B3450509 : Blo 1532463 3450509 := bbase (se 3 (by rfl) ⟨646970, by rfl⟩ : syracuseStep 3450509 = 1293941) (by norm_num)
theorem B3450581 : Blo 1532463 3450581 := bbase (se 7 (by rfl) ⟨40436, by rfl⟩ : syracuseStep 3450581 = 80873) (by norm_num)
theorem B7759637 : Blo 1532463 7759637 := bbase (se 6 (by rfl) ⟨181866, by rfl⟩ : syracuseStep 7759637 = 363733) (by norm_num)
theorem B3450653 : Blo 1532463 3450653 := bbase (se 3 (by rfl) ⟨646997, by rfl⟩ : syracuseStep 3450653 = 1293995) (by norm_num)
theorem B3450725 : Blo 1532463 3450725 := bbase (se 4 (by rfl) ⟨323505, by rfl⟩ : syracuseStep 3450725 = 647011) (by norm_num)
theorem B2910077 : Blo 1532463 2910077 := bbase (se 3 (by rfl) ⟨545639, by rfl⟩ : syracuseStep 2910077 = 1091279) (by norm_num)
theorem B2762669 : Blo 1532463 2762669 := bbase (se 3 (by rfl) ⟨518000, by rfl⟩ : syracuseStep 2762669 = 1036001) (by norm_num)
theorem B3450797 : Blo 1532463 3450797 := bbase (se 3 (by rfl) ⟨647024, by rfl⟩ : syracuseStep 3450797 = 1294049) (by norm_num)
theorem B8521685 : Blo 1532463 8521685 := bbase (se 7 (by rfl) ⟨99863, by rfl⟩ : syracuseStep 8521685 = 199727) (by norm_num)
theorem B3450869 : Blo 1532463 3450869 := bbase (se 5 (by rfl) ⟨161759, by rfl⟩ : syracuseStep 3450869 = 323519) (by norm_num)
theorem B3450941 : Blo 1532463 3450941 := bbase (se 3 (by rfl) ⟨647051, by rfl⟩ : syracuseStep 3450941 = 1294103) (by norm_num)
theorem B3451013 : Blo 1532463 3451013 := bbase (se 4 (by rfl) ⟨323532, by rfl⟩ : syracuseStep 3451013 = 647065) (by norm_num)
theorem B3451085 : Blo 1532463 3451085 := bbase (se 3 (by rfl) ⟨647078, by rfl⟩ : syracuseStep 3451085 = 1294157) (by norm_num)
theorem B27969749 : Blo 1532463 27969749 := bbase (se 7 (by rfl) ⟨327770, by rfl⟩ : syracuseStep 27969749 = 655541) (by norm_num)
theorem B4368613 : Blo 1532463 4368613 := bbase (se 4 (by rfl) ⟨409557, by rfl⟩ : syracuseStep 4368613 = 819115) (by norm_num)
theorem B3451157 : Blo 1532463 3451157 := bbase (se 6 (by rfl) ⟨80886, by rfl⟩ : syracuseStep 3451157 = 161773) (by norm_num)
theorem B1771849 : Blo 1532463 1771849 := bbase (se 2 (by rfl) ⟨664443, by rfl⟩ : syracuseStep 1771849 = 1328887) (by norm_num)
theorem B3451229 : Blo 1532463 3451229 := bbase (se 3 (by rfl) ⟨647105, by rfl⟩ : syracuseStep 3451229 = 1294211) (by norm_num)
theorem B3451301 : Blo 1532463 3451301 := bbase (se 4 (by rfl) ⟨323559, by rfl⟩ : syracuseStep 3451301 = 647119) (by norm_num)
theorem B3451373 : Blo 1532463 3451373 := bbase (se 3 (by rfl) ⟨647132, by rfl⟩ : syracuseStep 3451373 = 1294265) (by norm_num)
theorem B3451445 : Blo 1532463 3451445 := bbase (se 5 (by rfl) ⟨161786, by rfl⟩ : syracuseStep 3451445 = 323573) (by norm_num)
theorem B2910829 : Blo 1532463 2910829 := bbase (se 3 (by rfl) ⟨545780, by rfl⟩ : syracuseStep 2910829 = 1091561) (by norm_num)
theorem B3451517 : Blo 1532463 3451517 := bbase (se 3 (by rfl) ⟨647159, by rfl⟩ : syracuseStep 3451517 = 1294319) (by norm_num)
theorem B7465621 : Blo 1532463 7465621 := bbase (se 6 (by rfl) ⟨174975, by rfl⟩ : syracuseStep 7465621 = 349951) (by norm_num)
theorem B3451589 : Blo 1532463 3451589 := bbase (se 4 (by rfl) ⟨323586, by rfl⟩ : syracuseStep 3451589 = 647173) (by norm_num)
theorem B4909781 : Blo 1532463 4909781 := bbase (se 7 (by rfl) ⟨57536, by rfl⟩ : syracuseStep 4909781 = 115073) (by norm_num)
theorem B2910973 : Blo 1532463 2910973 := bbase (se 3 (by rfl) ⟨545807, by rfl⟩ : syracuseStep 2910973 = 1091615) (by norm_num)
theorem B3451661 : Blo 1532463 3451661 := bbase (se 3 (by rfl) ⟨647186, by rfl⟩ : syracuseStep 3451661 = 1294373) (by norm_num)
theorem B3107621 : Blo 1532463 3107621 := bbase (se 4 (by rfl) ⟨291339, by rfl⟩ : syracuseStep 3107621 = 582679) (by norm_num)
theorem B2362165 : Blo 1532463 2362165 := bbase (se 5 (by rfl) ⟨110726, by rfl⟩ : syracuseStep 2362165 = 221453) (by norm_num)
theorem B3451733 : Blo 1532463 3451733 := bbase (se 9 (by rfl) ⟨10112, by rfl⟩ : syracuseStep 3451733 = 20225) (by norm_num)
theorem B6548357 : Blo 1532463 6548357 := bbase (se 4 (by rfl) ⟨613908, by rfl⟩ : syracuseStep 6548357 = 1227817) (by norm_num)
theorem B2911133 : Blo 1532463 2911133 := bbase (se 3 (by rfl) ⟨545837, by rfl⟩ : syracuseStep 2911133 = 1091675) (by norm_num)
theorem B3451805 : Blo 1532463 3451805 := bbase (se 3 (by rfl) ⟨647213, by rfl⟩ : syracuseStep 3451805 = 1294427) (by norm_num)
theorem B3787709 : Blo 1532463 3787709 := bbase (se 3 (by rfl) ⟨710195, by rfl⟩ : syracuseStep 3787709 = 1420391) (by norm_num)
theorem B3451877 : Blo 1532463 3451877 := bbase (se 4 (by rfl) ⟨323613, by rfl⟩ : syracuseStep 3451877 = 647227) (by norm_num)
theorem B7760933 : Blo 1532463 7760933 := bbase (se 4 (by rfl) ⟨727587, by rfl⟩ : syracuseStep 7760933 = 1455175) (by norm_num)
theorem B2911277 : Blo 1532463 2911277 := bbase (se 3 (by rfl) ⟨545864, by rfl⟩ : syracuseStep 2911277 = 1091729) (by norm_num)
theorem B3451949 : Blo 1532463 3451949 := bbase (se 3 (by rfl) ⟨647240, by rfl⟩ : syracuseStep 3451949 = 1294481) (by norm_num)
theorem B8285237 : Blo 1532463 8285237 := bbase (se 5 (by rfl) ⟨388370, by rfl⟩ : syracuseStep 8285237 = 776741) (by norm_num)
theorem B6548597 : Blo 1532463 6548597 := bbase (se 5 (by rfl) ⟨306965, by rfl⟩ : syracuseStep 6548597 = 613931) (by norm_num)
theorem B3452021 : Blo 1532463 3452021 := bbase (se 5 (by rfl) ⟨161813, by rfl⟩ : syracuseStep 3452021 = 323627) (by norm_num)
theorem B1748105 : Blo 1532463 1748105 := bbase (se 2 (by rfl) ⟨655539, by rfl⟩ : syracuseStep 1748105 = 1311079) (by norm_num)
theorem B5172389 : Blo 1532463 5172389 := bbase (se 4 (by rfl) ⟨484911, by rfl⟩ : syracuseStep 5172389 = 969823) (by norm_num)
theorem B3452093 : Blo 1532463 3452093 := bbase (se 3 (by rfl) ⟨647267, by rfl⟩ : syracuseStep 3452093 = 1294535) (by norm_num)
theorem B2763973 : Blo 1532463 2763973 := bbase (se 4 (by rfl) ⟨259122, by rfl⟩ : syracuseStep 2763973 = 518245) (by norm_num)
theorem B5115109 : Blo 1532463 5115109 := bbase (se 4 (by rfl) ⟨479541, by rfl⟩ : syracuseStep 5115109 = 959083) (by norm_num)
theorem B8285429 : Blo 1532463 8285429 := bbase (se 5 (by rfl) ⟨388379, by rfl⟩ : syracuseStep 8285429 = 776759) (by norm_num)
theorem B3452165 : Blo 1532463 3452165 := bbase (se 4 (by rfl) ⟨323640, by rfl⟩ : syracuseStep 3452165 = 647281) (by norm_num)
theorem B2182421 : Blo 1532463 2182421 := bbase (se 6 (by rfl) ⟨51150, by rfl⟩ : syracuseStep 2182421 = 102301) (by norm_num)
theorem B11054389 : Blo 1532463 11054389 := bbase (se 5 (by rfl) ⟨518174, by rfl⟩ : syracuseStep 11054389 = 1036349) (by norm_num)
theorem B5918005 : Blo 1532463 5918005 := bbase (se 5 (by rfl) ⟨277406, by rfl⟩ : syracuseStep 5918005 = 554813) (by norm_num)
theorem B2911565 : Blo 1532463 2911565 := bbase (se 3 (by rfl) ⟨545918, by rfl⟩ : syracuseStep 2911565 = 1091837) (by norm_num)
theorem B3452237 : Blo 1532463 3452237 := bbase (se 3 (by rfl) ⟨647294, by rfl⟩ : syracuseStep 3452237 = 1294589) (by norm_num)
theorem B2182501 : Blo 1532463 2182501 := bbase (se 4 (by rfl) ⟨204609, by rfl⟩ : syracuseStep 2182501 = 409219) (by norm_num)
theorem B3452309 : Blo 1532463 3452309 := bbase (se 6 (by rfl) ⟨80913, by rfl⟩ : syracuseStep 3452309 = 161827) (by norm_num)
theorem B2182621 : Blo 1532463 2182621 := bbase (se 3 (by rfl) ⟨409241, by rfl⟩ : syracuseStep 2182621 = 818483) (by norm_num)
theorem B3452381 : Blo 1532463 3452381 := bbase (se 3 (by rfl) ⟨647321, by rfl⟩ : syracuseStep 3452381 = 1294643) (by norm_num)
theorem B2911717 : Blo 1532463 2911717 := bbase (se 4 (by rfl) ⟨272973, by rfl⟩ : syracuseStep 2911717 = 545947) (by norm_num)
theorem B8736245 : Blo 1532463 8736245 := bbase (se 5 (by rfl) ⟨409511, by rfl⟩ : syracuseStep 8736245 = 819023) (by norm_num)
theorem B4664837 : Blo 1532463 4664837 := bbase (se 4 (by rfl) ⟨437328, by rfl⟩ : syracuseStep 4664837 = 874657) (by norm_num)
theorem B3452453 : Blo 1532463 3452453 := bbase (se 4 (by rfl) ⟨323667, by rfl⟩ : syracuseStep 3452453 = 647335) (by norm_num)
theorem B5819957 : Blo 1532463 5819957 := bbase (se 5 (by rfl) ⟨272810, by rfl⟩ : syracuseStep 5819957 = 545621) (by norm_num)
theorem B2182717 : Blo 1532463 2182717 := bbase (se 3 (by rfl) ⟨409259, by rfl⟩ : syracuseStep 2182717 = 818519) (by norm_num)
theorem B18640469 : Blo 1532463 18640469 := bbase (se 8 (by rfl) ⟨109221, by rfl⟩ : syracuseStep 18640469 = 218443) (by norm_num)
theorem B5172821 : Blo 1532463 5172821 := bbase (se 8 (by rfl) ⟨30309, by rfl⟩ : syracuseStep 5172821 = 60619) (by norm_num)
theorem B3452525 : Blo 1532463 3452525 := bbase (se 3 (by rfl) ⟨647348, by rfl⟩ : syracuseStep 3452525 = 1294697) (by norm_num)
theorem B8728181 : Blo 1532463 8728181 := bbase (se 5 (by rfl) ⟨409133, by rfl⟩ : syracuseStep 8728181 = 818267) (by norm_num)
theorem B1724053 : Blo 1532463 1724053 := bbase (se 6 (by rfl) ⟨40407, by rfl⟩ : syracuseStep 1724053 = 80815) (by norm_num)
theorem B20983445 : Blo 1532463 20983445 := bbase (se 6 (by rfl) ⟨491799, by rfl⟩ : syracuseStep 20983445 = 983599) (by norm_num)
theorem B1724089 : Blo 1532463 1724089 := bbase (se 2 (by rfl) ⟨646533, by rfl⟩ : syracuseStep 1724089 = 1293067) (by norm_num)
theorem B1724125 : Blo 1532463 1724125 := bbase (se 3 (by rfl) ⟨323273, by rfl⟩ : syracuseStep 1724125 = 646547) (by norm_num)
theorem B1724161 : Blo 1532463 1724161 := bbase (se 2 (by rfl) ⟨646560, by rfl⟩ : syracuseStep 1724161 = 1293121) (by norm_num)
theorem B3321605 : Blo 1532463 3321605 := bbase (se 4 (by rfl) ⟨311400, by rfl⟩ : syracuseStep 3321605 = 622801) (by norm_num)
theorem B2912021 : Blo 1532463 2912021 := bbase (se 6 (by rfl) ⟨68250, by rfl⟩ : syracuseStep 2912021 = 136501) (by norm_num)
theorem B1724197 : Blo 1532463 1724197 := bbase (se 4 (by rfl) ⟨161643, by rfl⟩ : syracuseStep 1724197 = 323287) (by norm_num)
theorem B1724233 : Blo 1532463 1724233 := bbase (se 2 (by rfl) ⟨646587, by rfl⟩ : syracuseStep 1724233 = 1293175) (by norm_num)
theorem B5820245 : Blo 1532463 5820245 := bbase (se 9 (by rfl) ⟨17051, by rfl⟩ : syracuseStep 5820245 = 34103) (by norm_num)
theorem B1724269 : Blo 1532463 1724269 := bbase (se 3 (by rfl) ⟨323300, by rfl⟩ : syracuseStep 1724269 = 646601) (by norm_num)
theorem B1724305 : Blo 1532463 1724305 := bbase (se 2 (by rfl) ⟨646614, by rfl⟩ : syracuseStep 1724305 = 1293229) (by norm_num)
theorem B2764693 : Blo 1532463 2764693 := bbase (se 6 (by rfl) ⟨64797, by rfl⟩ : syracuseStep 2764693 = 129595) (by norm_num)
theorem B2330533 : Blo 1532463 2330533 := bbase (se 4 (by rfl) ⟨218487, by rfl⟩ : syracuseStep 2330533 = 436975) (by norm_num)
theorem B1724341 : Blo 1532463 1724341 := bbase (se 5 (by rfl) ⟨80828, by rfl⟩ : syracuseStep 1724341 = 161657) (by norm_num)
theorem B1724377 : Blo 1532463 1724377 := bbase (se 2 (by rfl) ⟨646641, by rfl⟩ : syracuseStep 1724377 = 1293283) (by norm_num)
theorem B1724413 : Blo 1532463 1724413 := bbase (se 3 (by rfl) ⟨323327, by rfl⟩ : syracuseStep 1724413 = 646655) (by norm_num)
theorem B5173253 : Blo 1532463 5173253 := bbase (se 4 (by rfl) ⟨484992, by rfl⟩ : syracuseStep 5173253 = 969985) (by norm_num)
theorem B1724449 : Blo 1532463 1724449 := bbase (se 2 (by rfl) ⟨646668, by rfl⟩ : syracuseStep 1724449 = 1293337) (by norm_num)
theorem B2183213 : Blo 1532463 2183213 := bbase (se 3 (by rfl) ⟨409352, by rfl⟩ : syracuseStep 2183213 = 818705) (by norm_num)
theorem B1724485 : Blo 1532463 1724485 := bbase (se 4 (by rfl) ⟨161670, by rfl⟩ : syracuseStep 1724485 = 323341) (by norm_num)
theorem B4911205 : Blo 1532463 4911205 := bbase (se 4 (by rfl) ⟨460425, by rfl⟩ : syracuseStep 4911205 = 920851) (by norm_num)
theorem B1724521 : Blo 1532463 1724521 := bbase (se 2 (by rfl) ⟨646695, by rfl⟩ : syracuseStep 1724521 = 1293391) (by norm_num)
theorem B11645045 : Blo 1532463 11645045 := bbase (se 5 (by rfl) ⟨545861, by rfl⟩ : syracuseStep 11645045 = 1091723) (by norm_num)
theorem B1724557 : Blo 1532463 1724557 := bbase (se 3 (by rfl) ⟨323354, by rfl⟩ : syracuseStep 1724557 = 646709) (by norm_num)
theorem B1724593 : Blo 1532463 1724593 := bbase (se 2 (by rfl) ⟨646722, by rfl⟩ : syracuseStep 1724593 = 1293445) (by norm_num)
theorem B1724629 : Blo 1532463 1724629 := bbase (se 7 (by rfl) ⟨20210, by rfl⟩ : syracuseStep 1724629 = 40421) (by norm_num)
theorem B1724665 : Blo 1532463 1724665 := bbase (se 2 (by rfl) ⟨646749, by rfl⟩ : syracuseStep 1724665 = 1293499) (by norm_num)
theorem B1724701 : Blo 1532463 1724701 := bbase (se 3 (by rfl) ⟨323381, by rfl⟩ : syracuseStep 1724701 = 646763) (by norm_num)
theorem B7762229 : Blo 1532463 7762229 := bbase (se 5 (by rfl) ⟨363854, by rfl⟩ : syracuseStep 7762229 = 727709) (by norm_num)
theorem B1724737 : Blo 1532463 1724737 := bbase (se 2 (by rfl) ⟨646776, by rfl⟩ : syracuseStep 1724737 = 1293553) (by norm_num)
theorem B1724773 : Blo 1532463 1724773 := bbase (se 4 (by rfl) ⟨161697, by rfl⟩ : syracuseStep 1724773 = 323395) (by norm_num)
theorem B3273085 : Blo 1532463 3273085 := bbase (se 3 (by rfl) ⟨613703, by rfl⟩ : syracuseStep 3273085 = 1227407) (by norm_num)
theorem B1724809 : Blo 1532463 1724809 := bbase (se 2 (by rfl) ⟨646803, by rfl⟩ : syracuseStep 1724809 = 1293607) (by norm_num)
theorem B22409621 : Blo 1532463 22409621 := bbase (se 6 (by rfl) ⟨525225, by rfl⟩ : syracuseStep 22409621 = 1050451) (by norm_num)
theorem B1724845 : Blo 1532463 1724845 := bbase (se 3 (by rfl) ⟨323408, by rfl⟩ : syracuseStep 1724845 = 646817) (by norm_num)
theorem B3682741 : Blo 1532463 3682741 := bbase (se 5 (by rfl) ⟨172628, by rfl⟩ : syracuseStep 3682741 = 345257) (by norm_num)
theorem B5173685 : Blo 1532463 5173685 := bbase (se 5 (by rfl) ⟨242516, by rfl⟩ : syracuseStep 5173685 = 485033) (by norm_num)
theorem B1749433 : Blo 1532463 1749433 := bbase (se 2 (by rfl) ⟨656037, by rfl⟩ : syracuseStep 1749433 = 1312075) (by norm_num)
theorem B5525957 : Blo 1532463 5525957 := bbase (se 4 (by rfl) ⟨518058, by rfl⟩ : syracuseStep 5525957 = 1036117) (by norm_num)
theorem B3879373 : Blo 1532463 3879373 := bbase (se 3 (by rfl) ⟨727382, by rfl⟩ : syracuseStep 3879373 = 1454765) (by norm_num)
theorem B1724881 : Blo 1532463 1724881 := bbase (se 2 (by rfl) ⟨646830, by rfl⟩ : syracuseStep 1724881 = 1293661) (by norm_num)
theorem B3273205 : Blo 1532463 3273205 := bbase (se 5 (by rfl) ⟨153431, by rfl⟩ : syracuseStep 3273205 = 306863) (by norm_num)
theorem B1724917 : Blo 1532463 1724917 := bbase (se 5 (by rfl) ⟨80855, by rfl⟩ : syracuseStep 1724917 = 161711) (by norm_num)
theorem B2912773 : Blo 1532463 2912773 := bbase (se 4 (by rfl) ⟨273072, by rfl⟩ : syracuseStep 2912773 = 546145) (by norm_num)
theorem B11637269 : Blo 1532463 11637269 := bbase (se 6 (by rfl) ⟨272748, by rfl⟩ : syracuseStep 11637269 = 545497) (by norm_num)
theorem B1724953 : Blo 1532463 1724953 := bbase (se 2 (by rfl) ⟨646857, by rfl⟩ : syracuseStep 1724953 = 1293715) (by norm_num)
theorem B1749529 : Blo 1532463 1749529 := bbase (se 2 (by rfl) ⟨656073, by rfl⟩ : syracuseStep 1749529 = 1312147) (by norm_num)
theorem B4911653 : Blo 1532463 4911653 := bbase (se 4 (by rfl) ⟨460467, by rfl⟩ : syracuseStep 4911653 = 920935) (by norm_num)
theorem B3879485 : Blo 1532463 3879485 := bbase (se 3 (by rfl) ⟨727403, by rfl⟩ : syracuseStep 3879485 = 1454807) (by norm_num)
theorem B1724989 : Blo 1532463 1724989 := bbase (se 3 (by rfl) ⟨323435, by rfl⟩ : syracuseStep 1724989 = 646871) (by norm_num)
theorem B2183765 : Blo 1532463 2183765 := bbase (se 8 (by rfl) ⟨12795, by rfl⟩ : syracuseStep 2183765 = 25591) (by norm_num)
theorem B1725025 : Blo 1532463 1725025 := bbase (se 2 (by rfl) ⟨646884, by rfl⟩ : syracuseStep 1725025 = 1293769) (by norm_num)
theorem B1725061 : Blo 1532463 1725061 := bbase (se 4 (by rfl) ⟨161724, by rfl⟩ : syracuseStep 1725061 = 323449) (by norm_num)
theorem B8737429 : Blo 1532463 8737429 := bbase (se 6 (by rfl) ⟨204783, by rfl⟩ : syracuseStep 8737429 = 409567) (by norm_num)
theorem B2912917 : Blo 1532463 2912917 := bbase (se 6 (by rfl) ⟨68271, by rfl⟩ : syracuseStep 2912917 = 136543) (by norm_num)
theorem B1725097 : Blo 1532463 1725097 := bbase (se 2 (by rfl) ⟨646911, by rfl⟩ : syracuseStep 1725097 = 1293823) (by norm_num)
theorem B3936941 : Blo 1532463 3936941 := bbase (se 3 (by rfl) ⟨738176, by rfl⟩ : syracuseStep 3936941 = 1476353) (by norm_num)
theorem B1725133 : Blo 1532463 1725133 := bbase (se 3 (by rfl) ⟨323462, by rfl⟩ : syracuseStep 1725133 = 646925) (by norm_num)
theorem B1725169 : Blo 1532463 1725169 := bbase (se 2 (by rfl) ⟨646938, by rfl⟩ : syracuseStep 1725169 = 1293877) (by norm_num)
theorem B3273461 : Blo 1532463 3273461 := bbase (se 5 (by rfl) ⟨153443, by rfl⟩ : syracuseStep 3273461 = 306887) (by norm_num)
theorem B3879677 : Blo 1532463 3879677 := bbase (se 3 (by rfl) ⟨727439, by rfl⟩ : syracuseStep 3879677 = 1454879) (by norm_num)
theorem B1725205 : Blo 1532463 1725205 := bbase (se 6 (by rfl) ⟨40434, by rfl⟩ : syracuseStep 1725205 = 80869) (by norm_num)
theorem B2913077 : Blo 1532463 2913077 := bbase (se 5 (by rfl) ⟨136550, by rfl⟩ : syracuseStep 2913077 = 273101) (by norm_num)
theorem B1725241 : Blo 1532463 1725241 := bbase (se 2 (by rfl) ⟨646965, by rfl⟩ : syracuseStep 1725241 = 1293931) (by norm_num)
theorem B2298701 : Blo 1532463 2298701 := bbase (se 3 (by rfl) ⟨431006, by rfl⟩ : syracuseStep 2298701 = 862013) (by norm_num)
theorem B13103957 : Blo 1532463 13103957 := bbase (se 9 (by rfl) ⟨38390, by rfl⟩ : syracuseStep 13103957 = 76781) (by norm_num)
theorem B1725277 : Blo 1532463 1725277 := bbase (se 3 (by rfl) ⟨323489, by rfl⟩ : syracuseStep 1725277 = 646979) (by norm_num)
theorem B2298725 : Blo 1532463 2298725 := bbase (se 4 (by rfl) ⟨215505, by rfl⟩ : syracuseStep 2298725 = 431011) (by norm_num)
theorem B5174117 : Blo 1532463 5174117 := bbase (se 4 (by rfl) ⟨485073, by rfl⟩ : syracuseStep 5174117 = 970147) (by norm_num)
theorem B2298749 : Blo 1532463 2298749 := bbase (se 3 (by rfl) ⟨431015, by rfl⟩ : syracuseStep 2298749 = 862031) (by norm_num)
theorem B1725313 : Blo 1532463 1725313 := bbase (se 2 (by rfl) ⟨646992, by rfl⟩ : syracuseStep 1725313 = 1293985) (by norm_num)
theorem B2298773 : Blo 1532463 2298773 := bbase (se 6 (by rfl) ⟨53877, by rfl⟩ : syracuseStep 2298773 = 107755) (by norm_num)
theorem B1725349 : Blo 1532463 1725349 := bbase (se 4 (by rfl) ⟨161751, by rfl⟩ : syracuseStep 1725349 = 323503) (by norm_num)
theorem B2298797 : Blo 1532463 2298797 := bbase (se 3 (by rfl) ⟨431024, by rfl⟩ : syracuseStep 2298797 = 862049) (by norm_num)
theorem B2298821 : Blo 1532463 2298821 := bbase (se 4 (by rfl) ⟨215514, by rfl⟩ : syracuseStep 2298821 = 431029) (by norm_num)
theorem B1725385 : Blo 1532463 1725385 := bbase (se 2 (by rfl) ⟨647019, by rfl⟩ : syracuseStep 1725385 = 1294039) (by norm_num)
theorem B2298845 : Blo 1532463 2298845 := bbase (se 3 (by rfl) ⟨431033, by rfl⟩ : syracuseStep 2298845 = 862067) (by norm_num)
theorem B1725421 : Blo 1532463 1725421 := bbase (se 3 (by rfl) ⟨323516, by rfl⟩ : syracuseStep 1725421 = 647033) (by norm_num)
theorem B2298869 : Blo 1532463 2298869 := bbase (se 5 (by rfl) ⟨107759, by rfl⟩ : syracuseStep 2298869 = 215519) (by norm_num)
theorem B5821429 : Blo 1532463 5821429 := bbase (se 5 (by rfl) ⟨272879, by rfl⟩ : syracuseStep 5821429 = 545759) (by norm_num)
theorem B2298893 : Blo 1532463 2298893 := bbase (se 3 (by rfl) ⟨431042, by rfl⟩ : syracuseStep 2298893 = 862085) (by norm_num)
theorem B1725457 : Blo 1532463 1725457 := bbase (se 2 (by rfl) ⟨647046, by rfl⟩ : syracuseStep 1725457 = 1294093) (by norm_num)
theorem B3109909 : Blo 1532463 3109909 := bbase (se 6 (by rfl) ⟨72888, by rfl⟩ : syracuseStep 3109909 = 145777) (by norm_num)
theorem B3683357 : Blo 1532463 3683357 := bbase (se 3 (by rfl) ⟨690629, by rfl⟩ : syracuseStep 3683357 = 1381259) (by norm_num)
theorem B2298917 : Blo 1532463 2298917 := bbase (se 4 (by rfl) ⟨215523, by rfl⟩ : syracuseStep 2298917 = 431047) (by norm_num)
theorem B1553453 : Blo 1532463 1553453 := bbase (se 3 (by rfl) ⟨291272, by rfl⟩ : syracuseStep 1553453 = 582545) (by norm_num)
theorem B1725493 : Blo 1532463 1725493 := bbase (se 5 (by rfl) ⟨80882, by rfl⟩ : syracuseStep 1725493 = 161765) (by norm_num)
theorem B2298941 : Blo 1532463 2298941 := bbase (se 3 (by rfl) ⟨431051, by rfl⟩ : syracuseStep 2298941 = 862103) (by norm_num)
theorem B2298965 : Blo 1532463 2298965 := bbase (se 8 (by rfl) ⟨13470, by rfl⟩ : syracuseStep 2298965 = 26941) (by norm_num)
theorem B3880021 : Blo 1532463 3880021 := bbase (se 8 (by rfl) ⟨22734, by rfl⟩ : syracuseStep 3880021 = 45469) (by norm_num)
theorem B1725529 : Blo 1532463 1725529 := bbase (se 2 (by rfl) ⟨647073, by rfl⟩ : syracuseStep 1725529 = 1294147) (by norm_num)
theorem B2298989 : Blo 1532463 2298989 := bbase (se 3 (by rfl) ⟨431060, by rfl⟩ : syracuseStep 2298989 = 862121) (by norm_num)
theorem B1725565 : Blo 1532463 1725565 := bbase (se 3 (by rfl) ⟨323543, by rfl⟩ : syracuseStep 1725565 = 647087) (by norm_num)
theorem B2299013 : Blo 1532463 2299013 := bbase (se 4 (by rfl) ⟨215532, by rfl⟩ : syracuseStep 2299013 = 431065) (by norm_num)
theorem B3413125 : Blo 1532463 3413125 := bbase (se 4 (by rfl) ⟨319980, by rfl⟩ : syracuseStep 3413125 = 639961) (by norm_num)
theorem B2299037 : Blo 1532463 2299037 := bbase (se 3 (by rfl) ⟨431069, by rfl⟩ : syracuseStep 2299037 = 862139) (by norm_num)
theorem B1725601 : Blo 1532463 1725601 := bbase (se 2 (by rfl) ⟨647100, by rfl⟩ : syracuseStep 1725601 = 1294201) (by norm_num)
theorem B2299061 : Blo 1532463 2299061 := bbase (se 5 (by rfl) ⟨107768, by rfl⟩ : syracuseStep 2299061 = 215537) (by norm_num)
theorem B3880133 : Blo 1532463 3880133 := bbase (se 4 (by rfl) ⟨363762, by rfl⟩ : syracuseStep 3880133 = 727525) (by norm_num)
theorem B1725637 : Blo 1532463 1725637 := bbase (se 4 (by rfl) ⟨161778, by rfl⟩ : syracuseStep 1725637 = 323557) (by norm_num)
theorem B2299085 : Blo 1532463 2299085 := bbase (se 3 (by rfl) ⟨431078, by rfl⟩ : syracuseStep 2299085 = 862157) (by norm_num)
theorem B2299109 : Blo 1532463 2299109 := bbase (se 4 (by rfl) ⟨215541, by rfl⟩ : syracuseStep 2299109 = 431083) (by norm_num)
theorem B1725673 : Blo 1532463 1725673 := bbase (se 2 (by rfl) ⟨647127, by rfl⟩ : syracuseStep 1725673 = 1294255) (by norm_num)
theorem B2299133 : Blo 1532463 2299133 := bbase (se 3 (by rfl) ⟨431087, by rfl⟩ : syracuseStep 2299133 = 862175) (by norm_num)
theorem B1725709 : Blo 1532463 1725709 := bbase (se 3 (by rfl) ⟨323570, by rfl⟩ : syracuseStep 1725709 = 647141) (by norm_num)
theorem B2299157 : Blo 1532463 2299157 := bbase (se 6 (by rfl) ⟨53886, by rfl⟩ : syracuseStep 2299157 = 107773) (by norm_num)
theorem B5174549 : Blo 1532463 5174549 := bbase (se 6 (by rfl) ⟨121278, by rfl⟩ : syracuseStep 5174549 = 242557) (by norm_num)
theorem B29480213 : Blo 1532463 29480213 := bbase (se 6 (by rfl) ⟨690942, by rfl⟩ : syracuseStep 29480213 = 1381885) (by norm_num)
theorem B5821733 : Blo 1532463 5821733 := bbase (se 4 (by rfl) ⟨545787, by rfl⟩ : syracuseStep 5821733 = 1091575) (by norm_num)
theorem B2299181 : Blo 1532463 2299181 := bbase (se 3 (by rfl) ⟨431096, by rfl⟩ : syracuseStep 2299181 = 862193) (by norm_num)
theorem B1725745 : Blo 1532463 1725745 := bbase (se 2 (by rfl) ⟨647154, by rfl⟩ : syracuseStep 1725745 = 1294309) (by norm_num)
theorem B2299205 : Blo 1532463 2299205 := bbase (se 4 (by rfl) ⟨215550, by rfl⟩ : syracuseStep 2299205 = 431101) (by norm_num)
theorem B2184517 : Blo 1532463 2184517 := bbase (se 4 (by rfl) ⟨204798, by rfl⟩ : syracuseStep 2184517 = 409597) (by norm_num)
theorem B1725781 : Blo 1532463 1725781 := bbase (se 16 (by rfl) ⟨39, by rfl⟩ : syracuseStep 1725781 = 79) (by norm_num)
theorem B2299229 : Blo 1532463 2299229 := bbase (se 3 (by rfl) ⟨431105, by rfl⟩ : syracuseStep 2299229 = 862211) (by norm_num)
theorem B6550885 : Blo 1532463 6550885 := bbase (se 4 (by rfl) ⟨614145, by rfl⟩ : syracuseStep 6550885 = 1228291) (by norm_num)
theorem B2299253 : Blo 1532463 2299253 := bbase (se 5 (by rfl) ⟨107777, by rfl⟩ : syracuseStep 2299253 = 215555) (by norm_num)
theorem B1725817 : Blo 1532463 1725817 := bbase (se 2 (by rfl) ⟨647181, by rfl⟩ : syracuseStep 1725817 = 1294363) (by norm_num)
theorem B3880325 : Blo 1532463 3880325 := bbase (se 4 (by rfl) ⟨363780, by rfl⟩ : syracuseStep 3880325 = 727561) (by norm_num)
theorem B2299277 : Blo 1532463 2299277 := bbase (se 3 (by rfl) ⟨431114, by rfl⟩ : syracuseStep 2299277 = 862229) (by norm_num)
theorem B1725853 : Blo 1532463 1725853 := bbase (se 3 (by rfl) ⟨323597, by rfl⟩ : syracuseStep 1725853 = 647195) (by norm_num)
theorem B2299301 : Blo 1532463 2299301 := bbase (se 4 (by rfl) ⟨215559, by rfl⟩ : syracuseStep 2299301 = 431119) (by norm_num)
theorem B2299325 : Blo 1532463 2299325 := bbase (se 3 (by rfl) ⟨431123, by rfl⟩ : syracuseStep 2299325 = 862247) (by norm_num)
theorem B1725889 : Blo 1532463 1725889 := bbase (se 2 (by rfl) ⟨647208, by rfl⟩ : syracuseStep 1725889 = 1294417) (by norm_num)
theorem B2586053 : Blo 1532463 2586053 := bbase (se 4 (by rfl) ⟨242442, by rfl⟩ : syracuseStep 2586053 = 484885) (by norm_num)
theorem B3683789 : Blo 1532463 3683789 := bbase (se 3 (by rfl) ⟨690710, by rfl⟩ : syracuseStep 3683789 = 1381421) (by norm_num)
theorem B2299349 : Blo 1532463 2299349 := bbase (se 7 (by rfl) ⟨26945, by rfl⟩ : syracuseStep 2299349 = 53891) (by norm_num)
theorem B1725925 : Blo 1532463 1725925 := bbase (se 4 (by rfl) ⟨161805, by rfl⟩ : syracuseStep 1725925 = 323611) (by norm_num)
theorem B2299373 : Blo 1532463 2299373 := bbase (se 3 (by rfl) ⟨431132, by rfl⟩ : syracuseStep 2299373 = 862265) (by norm_num)
theorem B2299397 : Blo 1532463 2299397 := bbase (se 4 (by rfl) ⟨215568, by rfl⟩ : syracuseStep 2299397 = 431137) (by norm_num)
theorem B1725961 : Blo 1532463 1725961 := bbase (se 2 (by rfl) ⟨647235, by rfl⟩ : syracuseStep 1725961 = 1294471) (by norm_num)
theorem B2299421 : Blo 1532463 2299421 := bbase (se 3 (by rfl) ⟨431141, by rfl⟩ : syracuseStep 2299421 = 862283) (by norm_num)
theorem B1725997 : Blo 1532463 1725997 := bbase (se 3 (by rfl) ⟨323624, by rfl⟩ : syracuseStep 1725997 = 647249) (by norm_num)
theorem B2299445 : Blo 1532463 2299445 := bbase (se 5 (by rfl) ⟨107786, by rfl⟩ : syracuseStep 2299445 = 215573) (by norm_num)
theorem B2586181 : Blo 1532463 2586181 := bbase (se 4 (by rfl) ⟨242454, by rfl⟩ : syracuseStep 2586181 = 484909) (by norm_num)
theorem B7763525 : Blo 1532463 7763525 := bbase (se 4 (by rfl) ⟨727830, by rfl⟩ : syracuseStep 7763525 = 1455661) (by norm_num)
theorem B2299469 : Blo 1532463 2299469 := bbase (se 3 (by rfl) ⟨431150, by rfl⟩ : syracuseStep 2299469 = 862301) (by norm_num)
theorem B1726033 : Blo 1532463 1726033 := bbase (se 2 (by rfl) ⟨647262, by rfl⟩ : syracuseStep 1726033 = 1294525) (by norm_num)
theorem B1554005 : Blo 1532463 1554005 := bbase (se 8 (by rfl) ⟨9105, by rfl⟩ : syracuseStep 1554005 = 18211) (by norm_num)
theorem B6305365 : Blo 1532463 6305365 := bbase (se 8 (by rfl) ⟨36945, by rfl⟩ : syracuseStep 6305365 = 73891) (by norm_num)
theorem B2299493 : Blo 1532463 2299493 := bbase (se 4 (by rfl) ⟨215577, by rfl⟩ : syracuseStep 2299493 = 431155) (by norm_num)
theorem B3274349 : Blo 1532463 3274349 := bbase (se 3 (by rfl) ⟨613940, by rfl⟩ : syracuseStep 3274349 = 1227881) (by norm_num)
theorem B1726069 : Blo 1532463 1726069 := bbase (se 5 (by rfl) ⟨80909, by rfl⟩ : syracuseStep 1726069 = 161819) (by norm_num)
theorem B2299517 : Blo 1532463 2299517 := bbase (se 3 (by rfl) ⟨431159, by rfl⟩ : syracuseStep 2299517 = 862319) (by norm_num)
theorem B2242181 : Blo 1532463 2242181 := bbase (se 4 (by rfl) ⟨210204, by rfl⟩ : syracuseStep 2242181 = 420409) (by norm_num)
theorem B2299541 : Blo 1532463 2299541 := bbase (se 6 (by rfl) ⟨53895, by rfl⟩ : syracuseStep 2299541 = 107791) (by norm_num)
theorem B1726105 : Blo 1532463 1726105 := bbase (se 2 (by rfl) ⟨647289, by rfl⟩ : syracuseStep 1726105 = 1294579) (by norm_num)
theorem B2586269 : Blo 1532463 2586269 := bbase (se 3 (by rfl) ⟨484925, by rfl⟩ : syracuseStep 2586269 = 969851) (by norm_num)
theorem B2299565 : Blo 1532463 2299565 := bbase (se 3 (by rfl) ⟨431168, by rfl⟩ : syracuseStep 2299565 = 862337) (by norm_num)
theorem B1726141 : Blo 1532463 1726141 := bbase (se 3 (by rfl) ⟨323651, by rfl⟩ : syracuseStep 1726141 = 647303) (by norm_num)
theorem B2299589 : Blo 1532463 2299589 := bbase (se 4 (by rfl) ⟨215586, by rfl⟩ : syracuseStep 2299589 = 431173) (by norm_num)
theorem B5174981 : Blo 1532463 5174981 := bbase (se 4 (by rfl) ⟨485154, by rfl⟩ : syracuseStep 5174981 = 970309) (by norm_num)
theorem B58930901 : Blo 1532463 58930901 := bbase (se 7 (by rfl) ⟨690596, by rfl⟩ : syracuseStep 58930901 = 1381193) (by norm_num)
theorem B2299613 : Blo 1532463 2299613 := bbase (se 3 (by rfl) ⟨431177, by rfl⟩ : syracuseStep 2299613 = 862355) (by norm_num)
theorem B3880669 : Blo 1532463 3880669 := bbase (se 3 (by rfl) ⟨727625, by rfl⟩ : syracuseStep 3880669 = 1455251) (by norm_num)
theorem B1726177 : Blo 1532463 1726177 := bbase (se 2 (by rfl) ⟨647316, by rfl⟩ : syracuseStep 1726177 = 1294633) (by norm_num)
theorem B2299637 : Blo 1532463 2299637 := bbase (se 5 (by rfl) ⟨107795, by rfl⟩ : syracuseStep 2299637 = 215591) (by norm_num)
theorem B2455301 : Blo 1532463 2455301 := bbase (se 4 (by rfl) ⟨230184, by rfl⟩ : syracuseStep 2455301 = 460369) (by norm_num)
theorem B1726213 : Blo 1532463 1726213 := bbase (se 4 (by rfl) ⟨161832, by rfl⟩ : syracuseStep 1726213 = 323665) (by norm_num)
theorem B2299661 : Blo 1532463 2299661 := bbase (se 3 (by rfl) ⟨431186, by rfl⟩ : syracuseStep 2299661 = 862373) (by norm_num)
theorem B2586397 : Blo 1532463 2586397 := bbase (se 3 (by rfl) ⟨484949, by rfl⟩ : syracuseStep 2586397 = 969899) (by norm_num)
theorem B2299685 : Blo 1532463 2299685 := bbase (se 4 (by rfl) ⟨215595, by rfl⟩ : syracuseStep 2299685 = 431191) (by norm_num)
theorem B1726249 : Blo 1532463 1726249 := bbase (se 2 (by rfl) ⟨647343, by rfl⟩ : syracuseStep 1726249 = 1294687) (by norm_num)
theorem B2299709 : Blo 1532463 2299709 := bbase (se 3 (by rfl) ⟨431195, by rfl⟩ : syracuseStep 2299709 = 862391) (by norm_num)
theorem B3880781 : Blo 1532463 3880781 := bbase (se 3 (by rfl) ⟨727646, by rfl⟩ : syracuseStep 3880781 = 1455293) (by norm_num)
theorem B2299733 : Blo 1532463 2299733 := bbase (se 9 (by rfl) ⟨6737, by rfl⟩ : syracuseStep 2299733 = 13475) (by norm_num)
theorem B3274589 : Blo 1532463 3274589 := bbase (se 3 (by rfl) ⟨613985, by rfl⟩ : syracuseStep 3274589 = 1227971) (by norm_num)
theorem B2299757 : Blo 1532463 2299757 := bbase (se 3 (by rfl) ⟨431204, by rfl⟩ : syracuseStep 2299757 = 862409) (by norm_num)
theorem B2586485 : Blo 1532463 2586485 := bbase (se 5 (by rfl) ⟨121241, by rfl⟩ : syracuseStep 2586485 = 242483) (by norm_num)
theorem B2455429 : Blo 1532463 2455429 := bbase (se 4 (by rfl) ⟨230196, by rfl⟩ : syracuseStep 2455429 = 460393) (by norm_num)
theorem B2299781 : Blo 1532463 2299781 := bbase (se 4 (by rfl) ⟨215604, by rfl⟩ : syracuseStep 2299781 = 431209) (by norm_num)
theorem B2299805 : Blo 1532463 2299805 := bbase (se 3 (by rfl) ⟨431213, by rfl⟩ : syracuseStep 2299805 = 862427) (by norm_num)
theorem B2299829 : Blo 1532463 2299829 := bbase (se 5 (by rfl) ⟨107804, by rfl⟩ : syracuseStep 2299829 = 215609) (by norm_num)
theorem B2299853 : Blo 1532463 2299853 := bbase (se 3 (by rfl) ⟨431222, by rfl⟩ : syracuseStep 2299853 = 862445) (by norm_num)
theorem B2299877 : Blo 1532463 2299877 := bbase (se 4 (by rfl) ⟨215613, by rfl⟩ : syracuseStep 2299877 = 431227) (by norm_num)
theorem B2586613 : Blo 1532463 2586613 := bbase (se 5 (by rfl) ⟨121247, by rfl⟩ : syracuseStep 2586613 = 242495) (by norm_num)
theorem B2299901 : Blo 1532463 2299901 := bbase (se 3 (by rfl) ⟨431231, by rfl⟩ : syracuseStep 2299901 = 862463) (by norm_num)
theorem B3151877 : Blo 1532463 3151877 := bbase (se 4 (by rfl) ⟨295488, by rfl⟩ : syracuseStep 3151877 = 590977) (by norm_num)
theorem B3880973 : Blo 1532463 3880973 := bbase (se 3 (by rfl) ⟨727682, by rfl⟩ : syracuseStep 3880973 = 1455365) (by norm_num)
theorem B2299925 : Blo 1532463 2299925 := bbase (se 6 (by rfl) ⟨53904, by rfl⟩ : syracuseStep 2299925 = 107809) (by norm_num)
theorem B2299949 : Blo 1532463 2299949 := bbase (se 3 (by rfl) ⟨431240, by rfl⟩ : syracuseStep 2299949 = 862481) (by norm_num)
theorem B2299973 : Blo 1532463 2299973 := bbase (se 4 (by rfl) ⟨215622, by rfl⟩ : syracuseStep 2299973 = 431245) (by norm_num)
theorem B2586701 : Blo 1532463 2586701 := bbase (se 3 (by rfl) ⟨485006, by rfl⟩ : syracuseStep 2586701 = 970013) (by norm_num)
theorem B2299997 : Blo 1532463 2299997 := bbase (se 3 (by rfl) ⟨431249, by rfl⟩ : syracuseStep 2299997 = 862499) (by norm_num)
theorem B1939565 : Blo 1532463 1939565 := bbase (se 3 (by rfl) ⟨363668, by rfl⟩ : syracuseStep 1939565 = 727337) (by norm_num)
theorem B2300021 : Blo 1532463 2300021 := bbase (se 5 (by rfl) ⟨107813, by rfl⟩ : syracuseStep 2300021 = 215627) (by norm_num)
theorem B5175413 : Blo 1532463 5175413 := bbase (se 5 (by rfl) ⟨242597, by rfl⟩ : syracuseStep 5175413 = 485195) (by norm_num)
theorem B2300045 : Blo 1532463 2300045 := bbase (se 3 (by rfl) ⟨431258, by rfl⟩ : syracuseStep 2300045 = 862517) (by norm_num)
theorem B3545245 : Blo 1532463 3545245 := bbase (se 3 (by rfl) ⟨664733, by rfl⟩ : syracuseStep 3545245 = 1329467) (by norm_num)
theorem B1939621 : Blo 1532463 1939621 := bbase (se 4 (by rfl) ⟨181839, by rfl⟩ : syracuseStep 1939621 = 363679) (by norm_num)
theorem B2300069 : Blo 1532463 2300069 := bbase (se 4 (by rfl) ⟨215631, by rfl⟩ : syracuseStep 2300069 = 431263) (by norm_num)
theorem B2300093 : Blo 1532463 2300093 := bbase (se 3 (by rfl) ⟨431267, by rfl⟩ : syracuseStep 2300093 = 862535) (by norm_num)
theorem B2586829 : Blo 1532463 2586829 := bbase (se 3 (by rfl) ⟨485030, by rfl⟩ : syracuseStep 2586829 = 970061) (by norm_num)
theorem B2300117 : Blo 1532463 2300117 := bbase (se 7 (by rfl) ⟨26954, by rfl⟩ : syracuseStep 2300117 = 53909) (by norm_num)
theorem B2300141 : Blo 1532463 2300141 := bbase (se 3 (by rfl) ⟨431276, by rfl⟩ : syracuseStep 2300141 = 862553) (by norm_num)
theorem B1939717 : Blo 1532463 1939717 := bbase (se 4 (by rfl) ⟨181848, by rfl⟩ : syracuseStep 1939717 = 363697) (by norm_num)
theorem B2300165 : Blo 1532463 2300165 := bbase (se 4 (by rfl) ⟨215640, by rfl⟩ : syracuseStep 2300165 = 431281) (by norm_num)
theorem B1841437 : Blo 1532463 1841437 := bbase (se 3 (by rfl) ⟨345269, by rfl⟩ : syracuseStep 1841437 = 690539) (by norm_num)
theorem B2300189 : Blo 1532463 2300189 := bbase (se 3 (by rfl) ⟨431285, by rfl⟩ : syracuseStep 2300189 = 862571) (by norm_num)
theorem B2586917 : Blo 1532463 2586917 := bbase (se 4 (by rfl) ⟨242523, by rfl⟩ : syracuseStep 2586917 = 485047) (by norm_num)
theorem B2300213 : Blo 1532463 2300213 := bbase (se 5 (by rfl) ⟨107822, by rfl⟩ : syracuseStep 2300213 = 215645) (by norm_num)
theorem B3152189 : Blo 1532463 3152189 := bbase (se 3 (by rfl) ⟨591035, by rfl⟩ : syracuseStep 3152189 = 1182071) (by norm_num)
theorem B2300237 : Blo 1532463 2300237 := bbase (se 3 (by rfl) ⟨431294, by rfl⟩ : syracuseStep 2300237 = 862589) (by norm_num)
theorem B3275093 : Blo 1532463 3275093 := bbase (se 10 (by rfl) ⟨4797, by rfl⟩ : syracuseStep 3275093 = 9595) (by norm_num)
theorem B3275101 : Blo 1532463 3275101 := bbase (se 3 (by rfl) ⟨614081, by rfl⟩ : syracuseStep 3275101 = 1228163) (by norm_num)
theorem B3881317 : Blo 1532463 3881317 := bbase (se 4 (by rfl) ⟨363873, by rfl⟩ : syracuseStep 3881317 = 727747) (by norm_num)
theorem B2300261 : Blo 1532463 2300261 := bbase (se 4 (by rfl) ⟨215649, by rfl⟩ : syracuseStep 2300261 = 431299) (by norm_num)
theorem B2300285 : Blo 1532463 2300285 := bbase (se 3 (by rfl) ⟨431303, by rfl⟩ : syracuseStep 2300285 = 862607) (by norm_num)
theorem B2300309 : Blo 1532463 2300309 := bbase (se 6 (by rfl) ⟨53913, by rfl⟩ : syracuseStep 2300309 = 107827) (by norm_num)
theorem B2587045 : Blo 1532463 2587045 := bbase (se 4 (by rfl) ⟨242535, by rfl⟩ : syracuseStep 2587045 = 485071) (by norm_num)
theorem B2300333 : Blo 1532463 2300333 := bbase (se 3 (by rfl) ⟨431312, by rfl⟩ : syracuseStep 2300333 = 862625) (by norm_num)
theorem B1939889 : Blo 1532463 1939889 := bbase (se 2 (by rfl) ⟨727458, by rfl⟩ : syracuseStep 1939889 = 1454917) (by norm_num)
theorem B6642101 : Blo 1532463 6642101 := bbase (se 5 (by rfl) ⟨311348, by rfl⟩ : syracuseStep 6642101 = 622697) (by norm_num)
theorem B2300357 : Blo 1532463 2300357 := bbase (se 4 (by rfl) ⟨215658, by rfl⟩ : syracuseStep 2300357 = 431317) (by norm_num)
theorem B3881429 : Blo 1532463 3881429 := bbase (se 7 (by rfl) ⟨45485, by rfl⟩ : syracuseStep 3881429 = 90971) (by norm_num)
theorem B2300381 : Blo 1532463 2300381 := bbase (se 3 (by rfl) ⟨431321, by rfl⟩ : syracuseStep 2300381 = 862643) (by norm_num)
theorem B1939945 : Blo 1532463 1939945 := bbase (se 2 (by rfl) ⟨727479, by rfl⟩ : syracuseStep 1939945 = 1454959) (by norm_num)
theorem B2300405 : Blo 1532463 2300405 := bbase (se 5 (by rfl) ⟨107831, by rfl⟩ : syracuseStep 2300405 = 215663) (by norm_num)
theorem B2587133 : Blo 1532463 2587133 := bbase (se 3 (by rfl) ⟨485087, by rfl⟩ : syracuseStep 2587133 = 970175) (by norm_num)
theorem B7371269 : Blo 1532463 7371269 := bbase (se 4 (by rfl) ⟨691056, by rfl⟩ : syracuseStep 7371269 = 1382113) (by norm_num)
theorem B2300429 : Blo 1532463 2300429 := bbase (se 3 (by rfl) ⟨431330, by rfl⟩ : syracuseStep 2300429 = 862661) (by norm_num)
theorem B5175845 : Blo 1532463 5175845 := bbase (se 4 (by rfl) ⟨485235, by rfl⟩ : syracuseStep 5175845 = 970471) (by norm_num)
theorem B2300453 : Blo 1532463 2300453 := bbase (se 4 (by rfl) ⟨215667, by rfl⟩ : syracuseStep 2300453 = 431335) (by norm_num)
theorem B2300477 : Blo 1532463 2300477 := bbase (se 3 (by rfl) ⟨431339, by rfl⟩ : syracuseStep 2300477 = 862679) (by norm_num)
theorem B1940041 : Blo 1532463 1940041 := bbase (se 2 (by rfl) ⟨727515, by rfl⟩ : syracuseStep 1940041 = 1455031) (by norm_num)
theorem B2300501 : Blo 1532463 2300501 := bbase (se 8 (by rfl) ⟨13479, by rfl⟩ : syracuseStep 2300501 = 26959) (by norm_num)
theorem B2300525 : Blo 1532463 2300525 := bbase (se 3 (by rfl) ⟨431348, by rfl⟩ : syracuseStep 2300525 = 862697) (by norm_num)
theorem B8977013 : Blo 1532463 8977013 := bbase (se 5 (by rfl) ⟨420797, by rfl⟩ : syracuseStep 8977013 = 841595) (by norm_num)
theorem B2587261 : Blo 1532463 2587261 := bbase (se 3 (by rfl) ⟨485111, by rfl⟩ : syracuseStep 2587261 = 970223) (by norm_num)
theorem B3684989 : Blo 1532463 3684989 := bbase (se 3 (by rfl) ⟨690935, by rfl⟩ : syracuseStep 3684989 = 1381871) (by norm_num)
theorem B2300549 : Blo 1532463 2300549 := bbase (se 4 (by rfl) ⟨215676, by rfl⟩ : syracuseStep 2300549 = 431353) (by norm_num)
theorem B3881621 : Blo 1532463 3881621 := bbase (se 6 (by rfl) ⟨90975, by rfl⟩ : syracuseStep 3881621 = 181951) (by norm_num)
theorem B1637021 : Blo 1532463 1637021 := bbase (se 3 (by rfl) ⟨306941, by rfl⟩ : syracuseStep 1637021 = 613883) (by norm_num)
theorem B2300573 : Blo 1532463 2300573 := bbase (se 3 (by rfl) ⟨431357, by rfl⟩ : syracuseStep 2300573 = 862715) (by norm_num)
theorem B6642341 : Blo 1532463 6642341 := bbase (se 4 (by rfl) ⟨622719, by rfl⟩ : syracuseStep 6642341 = 1245439) (by norm_num)
theorem B2456237 : Blo 1532463 2456237 := bbase (se 3 (by rfl) ⟨460544, by rfl⟩ : syracuseStep 2456237 = 921089) (by norm_num)
theorem B2300597 : Blo 1532463 2300597 := bbase (se 5 (by rfl) ⟨107840, by rfl⟩ : syracuseStep 2300597 = 215681) (by norm_num)
theorem B2300621 : Blo 1532463 2300621 := bbase (se 3 (by rfl) ⟨431366, by rfl⟩ : syracuseStep 2300621 = 862733) (by norm_num)
theorem B2587349 : Blo 1532463 2587349 := bbase (se 7 (by rfl) ⟨30320, by rfl⟩ : syracuseStep 2587349 = 60641) (by norm_num)
theorem B2300645 : Blo 1532463 2300645 := bbase (se 4 (by rfl) ⟨215685, by rfl⟩ : syracuseStep 2300645 = 431371) (by norm_num)
theorem B1940213 : Blo 1532463 1940213 := bbase (se 5 (by rfl) ⟨90947, by rfl⟩ : syracuseStep 1940213 = 181895) (by norm_num)
theorem B3496693 : Blo 1532463 3496693 := bbase (se 5 (by rfl) ⟨163907, by rfl⟩ : syracuseStep 3496693 = 327815) (by norm_num)
theorem B4913909 : Blo 1532463 4913909 := bbase (se 5 (by rfl) ⟨230339, by rfl⟩ : syracuseStep 4913909 = 460679) (by norm_num)
theorem B2300669 : Blo 1532463 2300669 := bbase (se 3 (by rfl) ⟨431375, by rfl⟩ : syracuseStep 2300669 = 862751) (by norm_num)
theorem B1555205 : Blo 1532463 1555205 := bbase (se 4 (by rfl) ⟨145800, by rfl⟩ : syracuseStep 1555205 = 291601) (by norm_num)
theorem B2300693 : Blo 1532463 2300693 := bbase (se 6 (by rfl) ⟨53922, by rfl⟩ : syracuseStep 2300693 = 107845) (by norm_num)
theorem B1940269 : Blo 1532463 1940269 := bbase (se 3 (by rfl) ⟨363800, by rfl⟩ : syracuseStep 1940269 = 727601) (by norm_num)
theorem B2300717 : Blo 1532463 2300717 := bbase (se 3 (by rfl) ⟨431384, by rfl⟩ : syracuseStep 2300717 = 862769) (by norm_num)
theorem B6552373 : Blo 1532463 6552373 := bbase (se 5 (by rfl) ⟨307142, by rfl⟩ : syracuseStep 6552373 = 614285) (by norm_num)
theorem B2300741 : Blo 1532463 2300741 := bbase (se 4 (by rfl) ⟨215694, by rfl⟩ : syracuseStep 2300741 = 431389) (by norm_num)
theorem B6552389 : Blo 1532463 6552389 := bbase (se 4 (by rfl) ⟨614286, by rfl⟩ : syracuseStep 6552389 = 1228573) (by norm_num)
theorem B2587477 : Blo 1532463 2587477 := bbase (se 9 (by rfl) ⟨7580, by rfl⟩ : syracuseStep 2587477 = 15161) (by norm_num)
theorem B7764821 : Blo 1532463 7764821 := bbase (se 9 (by rfl) ⟨22748, by rfl⟩ : syracuseStep 7764821 = 45497) (by norm_num)
theorem B1637209 : Blo 1532463 1637209 := bbase (se 2 (by rfl) ⟨613953, by rfl⟩ : syracuseStep 1637209 = 1227907) (by norm_num)
theorem B2300765 : Blo 1532463 2300765 := bbase (se 3 (by rfl) ⟨431393, by rfl⟩ : syracuseStep 2300765 = 862787) (by norm_num)
theorem B2300789 : Blo 1532463 2300789 := bbase (se 5 (by rfl) ⟨107849, by rfl⟩ : syracuseStep 2300789 = 215699) (by norm_num)
theorem B1940365 : Blo 1532463 1940365 := bbase (se 3 (by rfl) ⟨363818, by rfl⟩ : syracuseStep 1940365 = 727637) (by norm_num)
theorem B2300813 : Blo 1532463 2300813 := bbase (se 3 (by rfl) ⟨431402, by rfl⟩ : syracuseStep 2300813 = 862805) (by norm_num)
theorem B2300837 : Blo 1532463 2300837 := bbase (se 4 (by rfl) ⟨215703, by rfl⟩ : syracuseStep 2300837 = 431407) (by norm_num)
theorem B2587565 : Blo 1532463 2587565 := bbase (se 3 (by rfl) ⟨485168, by rfl⟩ : syracuseStep 2587565 = 970337) (by norm_num)
theorem B2300861 : Blo 1532463 2300861 := bbase (se 3 (by rfl) ⟨431411, by rfl⟩ : syracuseStep 2300861 = 862823) (by norm_num)
theorem B2456525 : Blo 1532463 2456525 := bbase (se 3 (by rfl) ⟨460598, by rfl⟩ : syracuseStep 2456525 = 921197) (by norm_num)
theorem B5176277 : Blo 1532463 5176277 := bbase (se 7 (by rfl) ⟨60659, by rfl⟩ : syracuseStep 5176277 = 121319) (by norm_num)
theorem B2300885 : Blo 1532463 2300885 := bbase (se 7 (by rfl) ⟨26963, by rfl⟩ : syracuseStep 2300885 = 53927) (by norm_num)
theorem B1842149 : Blo 1532463 1842149 := bbase (se 4 (by rfl) ⟨172701, by rfl⟩ : syracuseStep 1842149 = 345403) (by norm_num)
theorem B3881965 : Blo 1532463 3881965 := bbase (se 3 (by rfl) ⟨727868, by rfl⟩ : syracuseStep 3881965 = 1455737) (by norm_num)
theorem B2300909 : Blo 1532463 2300909 := bbase (se 3 (by rfl) ⟨431420, by rfl⟩ : syracuseStep 2300909 = 862841) (by norm_num)
theorem B3734525 : Blo 1532463 3734525 := bbase (se 3 (by rfl) ⟨700223, by rfl⟩ : syracuseStep 3734525 = 1400447) (by norm_num)
theorem B2300933 : Blo 1532463 2300933 := bbase (se 4 (by rfl) ⟨215712, by rfl⟩ : syracuseStep 2300933 = 431425) (by norm_num)
theorem B2300957 : Blo 1532463 2300957 := bbase (se 3 (by rfl) ⟨431429, by rfl⟩ : syracuseStep 2300957 = 862859) (by norm_num)
theorem B2587693 : Blo 1532463 2587693 := bbase (se 3 (by rfl) ⟨485192, by rfl⟩ : syracuseStep 2587693 = 970385) (by norm_num)
theorem B2300981 : Blo 1532463 2300981 := bbase (se 5 (by rfl) ⟨107858, by rfl⟩ : syracuseStep 2300981 = 215717) (by norm_num)
theorem B1940537 : Blo 1532463 1940537 := bbase (se 2 (by rfl) ⟨727701, by rfl⟩ : syracuseStep 1940537 = 1455403) (by norm_num)
theorem B5905477 : Blo 1532463 5905477 := bbase (se 4 (by rfl) ⟨553638, by rfl⟩ : syracuseStep 5905477 = 1107277) (by norm_num)
theorem B2301005 : Blo 1532463 2301005 := bbase (se 3 (by rfl) ⟨431438, by rfl⟩ : syracuseStep 2301005 = 862877) (by norm_num)
theorem B3882077 : Blo 1532463 3882077 := bbase (se 3 (by rfl) ⟨727889, by rfl⟩ : syracuseStep 3882077 = 1455779) (by norm_num)
theorem B2301029 : Blo 1532463 2301029 := bbase (se 4 (by rfl) ⟨215721, by rfl⟩ : syracuseStep 2301029 = 431443) (by norm_num)
theorem B1940593 : Blo 1532463 1940593 := bbase (se 2 (by rfl) ⟨727722, by rfl⟩ : syracuseStep 1940593 = 1455445) (by norm_num)
theorem B2301053 : Blo 1532463 2301053 := bbase (se 3 (by rfl) ⟨431447, by rfl⟩ : syracuseStep 2301053 = 862895) (by norm_num)
theorem B2587781 : Blo 1532463 2587781 := bbase (se 4 (by rfl) ⟨242604, by rfl⟩ : syracuseStep 2587781 = 485209) (by norm_num)
theorem B2301077 : Blo 1532463 2301077 := bbase (se 6 (by rfl) ⟨53931, by rfl⟩ : syracuseStep 2301077 = 107863) (by norm_num)
theorem B2301101 : Blo 1532463 2301101 := bbase (se 3 (by rfl) ⟨431456, by rfl⟩ : syracuseStep 2301101 = 862913) (by norm_num)
theorem B9329845 : Blo 1532463 9329845 := bbase (se 5 (by rfl) ⟨437336, by rfl⟩ : syracuseStep 9329845 = 874673) (by norm_num)
theorem B2301125 : Blo 1532463 2301125 := bbase (se 4 (by rfl) ⟨215730, by rfl⟩ : syracuseStep 2301125 = 431461) (by norm_num)
theorem B1940689 : Blo 1532463 1940689 := bbase (se 2 (by rfl) ⟨727758, by rfl⟩ : syracuseStep 1940689 = 1455517) (by norm_num)
theorem B2301149 : Blo 1532463 2301149 := bbase (se 3 (by rfl) ⟨431465, by rfl⟩ : syracuseStep 2301149 = 862931) (by norm_num)
theorem B2301173 : Blo 1532463 2301173 := bbase (se 5 (by rfl) ⟨107867, by rfl⟩ : syracuseStep 2301173 = 215735) (by norm_num)
theorem B3448061 : Blo 1532463 3448061 := bbase (se 3 (by rfl) ⟨646511, by rfl⟩ : syracuseStep 3448061 = 1293023) (by norm_num)
theorem B2587909 : Blo 1532463 2587909 := bbase (se 4 (by rfl) ⟨242616, by rfl⟩ : syracuseStep 2587909 = 485233) (by norm_num)
theorem B2301197 : Blo 1532463 2301197 := bbase (se 3 (by rfl) ⟨431474, by rfl⟩ : syracuseStep 2301197 = 862949) (by norm_num)
theorem B3882269 : Blo 1532463 3882269 := bbase (se 3 (by rfl) ⟨727925, by rfl⟩ : syracuseStep 3882269 = 1455851) (by norm_num)
theorem B2301221 : Blo 1532463 2301221 := bbase (se 4 (by rfl) ⟨215739, by rfl⟩ : syracuseStep 2301221 = 431479) (by norm_num)
theorem B1842485 : Blo 1532463 1842485 := bbase (se 5 (by rfl) ⟨86366, by rfl⟩ : syracuseStep 1842485 = 172733) (by norm_num)
theorem B14941493 : Blo 1532463 14941493 := bbase (se 5 (by rfl) ⟨700382, by rfl⟩ : syracuseStep 14941493 = 1400765) (by norm_num)
theorem B2301245 : Blo 1532463 2301245 := bbase (se 3 (by rfl) ⟨431483, by rfl⟩ : syracuseStep 2301245 = 862967) (by norm_num)
theorem B3448133 : Blo 1532463 3448133 := bbase (se 4 (by rfl) ⟨323262, by rfl⟩ : syracuseStep 3448133 = 646525) (by norm_num)
theorem B14736725 : Blo 1532463 14736725 := bbase (se 11 (by rfl) ⟨10793, by rfl⟩ : syracuseStep 14736725 = 21587) (by norm_num)
theorem B2301269 : Blo 1532463 2301269 := bbase (se 11 (by rfl) ⟨1685, by rfl⟩ : syracuseStep 2301269 = 3371) (by norm_num)
theorem B2587997 : Blo 1532463 2587997 := bbase (se 3 (by rfl) ⟨485249, by rfl⟩ : syracuseStep 2587997 = 970499) (by norm_num)
theorem B5823845 : Blo 1532463 5823845 := bbase (se 4 (by rfl) ⟨545985, by rfl⟩ : syracuseStep 5823845 = 1091971) (by norm_num)
theorem B2456941 : Blo 1532463 2456941 := bbase (se 3 (by rfl) ⟨460676, by rfl⟩ : syracuseStep 2456941 = 921353) (by norm_num)
theorem B2301293 : Blo 1532463 2301293 := bbase (se 3 (by rfl) ⟨431492, by rfl⟩ : syracuseStep 2301293 = 862985) (by norm_num)
theorem B1940861 : Blo 1532463 1940861 := bbase (se 3 (by rfl) ⟨363911, by rfl⟩ : syracuseStep 1940861 = 727823) (by norm_num)
theorem B5176709 : Blo 1532463 5176709 := bbase (se 4 (by rfl) ⟨485316, by rfl⟩ : syracuseStep 5176709 = 970633) (by norm_num)
theorem B2301317 : Blo 1532463 2301317 := bbase (se 4 (by rfl) ⟨215748, by rfl⟩ : syracuseStep 2301317 = 431497) (by norm_num)
theorem B3448205 : Blo 1532463 3448205 := bbase (se 3 (by rfl) ⟨646538, by rfl⟩ : syracuseStep 3448205 = 1293077) (by norm_num)
theorem B2301341 : Blo 1532463 2301341 := bbase (se 3 (by rfl) ⟨431501, by rfl⟩ : syracuseStep 2301341 = 863003) (by norm_num)
theorem B1842601 : Blo 1532463 1842601 := bbase (se 2 (by rfl) ⟨690975, by rfl⟩ : syracuseStep 1842601 = 1381951) (by norm_num)
theorem B1940917 : Blo 1532463 1940917 := bbase (se 5 (by rfl) ⟨90980, by rfl⟩ : syracuseStep 1940917 = 181961) (by norm_num)
theorem B2301365 : Blo 1532463 2301365 := bbase (se 5 (by rfl) ⟨107876, by rfl⟩ : syracuseStep 2301365 = 215753) (by norm_num)
theorem B1842625 : Blo 1532463 1842625 := bbase (se 2 (by rfl) ⟨690984, by rfl⟩ : syracuseStep 1842625 = 1381969) (by norm_num)
theorem B3276229 : Blo 1532463 3276229 := bbase (se 4 (by rfl) ⟨307146, by rfl⟩ : syracuseStep 3276229 = 614293) (by norm_num)
theorem B2301389 : Blo 1532463 2301389 := bbase (se 3 (by rfl) ⟨431510, by rfl⟩ : syracuseStep 2301389 = 863021) (by norm_num)
theorem B3448277 : Blo 1532463 3448277 := bbase (se 7 (by rfl) ⟨40409, by rfl⟩ : syracuseStep 3448277 = 80819) (by norm_num)
theorem B2588125 : Blo 1532463 2588125 := bbase (se 3 (by rfl) ⟨485273, by rfl⟩ : syracuseStep 2588125 = 970547) (by norm_num)
theorem B2301413 : Blo 1532463 2301413 := bbase (se 4 (by rfl) ⟨215757, by rfl⟩ : syracuseStep 2301413 = 431515) (by norm_num)
theorem B2301437 : Blo 1532463 2301437 := bbase (se 3 (by rfl) ⟨431519, by rfl⟩ : syracuseStep 2301437 = 863039) (by norm_num)
theorem B4365845 : Blo 1532463 4365845 := bbase (se 6 (by rfl) ⟨102324, by rfl⟩ : syracuseStep 4365845 = 204649) (by norm_num)
theorem B1941013 : Blo 1532463 1941013 := bbase (se 6 (by rfl) ⟨45492, by rfl⟩ : syracuseStep 1941013 = 90985) (by norm_num)
theorem B2301461 : Blo 1532463 2301461 := bbase (se 6 (by rfl) ⟨53940, by rfl⟩ : syracuseStep 2301461 = 107881) (by norm_num)
theorem B3448349 : Blo 1532463 3448349 := bbase (se 3 (by rfl) ⟨646565, by rfl⟩ : syracuseStep 3448349 = 1293131) (by norm_num)
theorem B2301485 : Blo 1532463 2301485 := bbase (se 3 (by rfl) ⟨431528, by rfl⟩ : syracuseStep 2301485 = 863057) (by norm_num)
theorem B2588213 : Blo 1532463 2588213 := bbase (se 5 (by rfl) ⟨121322, by rfl⟩ : syracuseStep 2588213 = 242645) (by norm_num)
theorem B2301509 : Blo 1532463 2301509 := bbase (se 4 (by rfl) ⟨215766, by rfl⟩ : syracuseStep 2301509 = 431533) (by norm_num)
theorem B2301533 : Blo 1532463 2301533 := bbase (se 3 (by rfl) ⟨431537, by rfl⟩ : syracuseStep 2301533 = 863075) (by norm_num)
theorem B3448421 : Blo 1532463 3448421 := bbase (se 4 (by rfl) ⟨323289, by rfl⟩ : syracuseStep 3448421 = 646579) (by norm_num)
theorem B3882613 : Blo 1532463 3882613 := bbase (se 5 (by rfl) ⟨181997, by rfl⟩ : syracuseStep 3882613 = 363995) (by norm_num)
theorem B2301557 : Blo 1532463 2301557 := bbase (se 5 (by rfl) ⟨107885, by rfl⟩ : syracuseStep 2301557 = 215771) (by norm_num)
theorem B5824133 : Blo 1532463 5824133 := bbase (se 4 (by rfl) ⟨546012, by rfl⟩ : syracuseStep 5824133 = 1092025) (by norm_num)
theorem B1638029 : Blo 1532463 1638029 := bbase (se 3 (by rfl) ⟨307130, by rfl⟩ : syracuseStep 1638029 = 614261) (by norm_num)
theorem B2301581 : Blo 1532463 2301581 := bbase (se 3 (by rfl) ⟨431546, by rfl⟩ : syracuseStep 2301581 = 863093) (by norm_num)
theorem B2301605 : Blo 1532463 2301605 := bbase (se 4 (by rfl) ⟨215775, by rfl⟩ : syracuseStep 2301605 = 431551) (by norm_num)
theorem B3448493 : Blo 1532463 3448493 := bbase (se 3 (by rfl) ⟨646592, by rfl⟩ : syracuseStep 3448493 = 1293185) (by norm_num)
theorem B2588341 : Blo 1532463 2588341 := bbase (se 5 (by rfl) ⟨121328, by rfl⟩ : syracuseStep 2588341 = 242657) (by norm_num)
theorem B2301629 : Blo 1532463 2301629 := bbase (se 3 (by rfl) ⟨431555, by rfl⟩ : syracuseStep 2301629 = 863111) (by norm_num)
theorem B1941185 : Blo 1532463 1941185 := bbase (se 2 (by rfl) ⟨727944, by rfl⟩ : syracuseStep 1941185 = 1455889) (by norm_num)
theorem B2301653 : Blo 1532463 2301653 := bbase (se 7 (by rfl) ⟨26972, by rfl⟩ : syracuseStep 2301653 = 53945) (by norm_num)
theorem B6217445 : Blo 1532463 6217445 := bbase (se 4 (by rfl) ⟨582885, by rfl⟩ : syracuseStep 6217445 = 1165771) (by norm_num)
theorem B3882725 : Blo 1532463 3882725 := bbase (se 4 (by rfl) ⟨364005, by rfl⟩ : syracuseStep 3882725 = 728011) (by norm_num)
theorem B2301677 : Blo 1532463 2301677 := bbase (se 3 (by rfl) ⟨431564, by rfl⟩ : syracuseStep 2301677 = 863129) (by norm_num)
theorem B3448565 : Blo 1532463 3448565 := bbase (se 5 (by rfl) ⟨161651, by rfl⟩ : syracuseStep 3448565 = 323303) (by norm_num)
theorem B2072309 : Blo 1532463 2072309 := bbase (se 5 (by rfl) ⟨97139, by rfl⟩ : syracuseStep 2072309 = 194279) (by norm_num)
theorem B13106933 : Blo 1532463 13106933 := bbase (se 5 (by rfl) ⟨614387, by rfl⟩ : syracuseStep 13106933 = 1228775) (by norm_num)
theorem B1941241 : Blo 1532463 1941241 := bbase (se 2 (by rfl) ⟨727965, by rfl⟩ : syracuseStep 1941241 = 1455931) (by norm_num)
theorem B2588429 : Blo 1532463 2588429 := bbase (se 3 (by rfl) ⟨485330, by rfl⟩ : syracuseStep 2588429 = 970661) (by norm_num)
theorem B5177141 : Blo 1532463 5177141 := bbase (se 5 (by rfl) ⟨242678, by rfl⟩ : syracuseStep 5177141 = 485357) (by norm_num)
theorem B3448637 : Blo 1532463 3448637 := bbase (se 3 (by rfl) ⟨646619, by rfl⟩ : syracuseStep 3448637 = 1293239) (by norm_num)
theorem B3497789 : Blo 1532463 3497789 := bbase (se 3 (by rfl) ⟨655835, by rfl⟩ : syracuseStep 3497789 = 1311671) (by norm_num)
theorem B3276605 : Blo 1532463 3276605 := bbase (se 3 (by rfl) ⟨614363, by rfl⟩ : syracuseStep 3276605 = 1228727) (by norm_num)
theorem B1941337 : Blo 1532463 1941337 := bbase (se 2 (by rfl) ⟨728001, by rfl⟩ : syracuseStep 1941337 = 1456003) (by norm_num)
theorem B3448709 : Blo 1532463 3448709 := bbase (se 4 (by rfl) ⟨323316, by rfl⟩ : syracuseStep 3448709 = 646633) (by norm_num)
theorem B2072461 : Blo 1532463 2072461 := bbase (se 3 (by rfl) ⟨388586, by rfl⟩ : syracuseStep 2072461 = 777173) (by norm_num)
theorem B2588557 : Blo 1532463 2588557 := bbase (se 3 (by rfl) ⟨485354, by rfl⟩ : syracuseStep 2588557 = 970709) (by norm_num)
theorem B3882917 : Blo 1532463 3882917 := bbase (se 4 (by rfl) ⟨364023, by rfl⟩ : syracuseStep 3882917 = 728047) (by norm_num)
theorem B3317701 : Blo 1532463 3317701 := bbase (se 4 (by rfl) ⟨311034, by rfl⟩ : syracuseStep 3317701 = 622069) (by norm_num)
theorem B3448781 : Blo 1532463 3448781 := bbase (se 3 (by rfl) ⟨646646, by rfl⟩ : syracuseStep 3448781 = 1293293) (by norm_num)
theorem B2588645 : Blo 1532463 2588645 := bbase (se 4 (by rfl) ⟨242685, by rfl⟩ : syracuseStep 2588645 = 485371) (by norm_num)
theorem B3448835 : Blo 1532463 3448835 := bstep (se 1 (by rfl) ⟨2586626, by rfl⟩ : syracuseStep 3448835 = 5173253) B5173253
theorem B5177357 : Blo 1532463 5177357 := bstep (se 3 (by rfl) ⟨970754, by rfl⟩ : syracuseStep 5177357 = 1941509) B1941509
theorem B33620021 : Blo 1532463 33620021 := bstep (se 5 (by rfl) ⟨1575938, by rfl⟩ : syracuseStep 33620021 = 3151877) B3151877
theorem B5177411 : Blo 1532463 5177411 := bstep (se 1 (by rfl) ⟨3883058, by rfl⟩ : syracuseStep 5177411 = 7766117) B7766117
theorem B2588753 : Blo 1532463 2588753 := bstep (se 2 (by rfl) ⟨970782, by rfl⟩ : syracuseStep 2588753 = 1941565) B1941565
theorem B10633315 : Blo 1532463 10633315 := bstep (se 1 (by rfl) ⟨7974986, by rfl⟩ : syracuseStep 10633315 = 15949973) B15949973
theorem B9330821 : Blo 1532463 9330821 := bstep (se 4 (by rfl) ⟨874764, by rfl⟩ : syracuseStep 9330821 = 1749529) B1749529
theorem B2457761 : Blo 1532463 2457761 := bstep (se 2 (by rfl) ⟨921660, by rfl⟩ : syracuseStep 2457761 = 1843321) B1843321
theorem B9961649 : Blo 1532463 9961649 := bstep (se 2 (by rfl) ⟨3735618, by rfl⟩ : syracuseStep 9961649 = 7471237) B7471237
theorem B30286021 : Blo 1532463 30286021 := bstep (se 4 (by rfl) ⟨2839314, by rfl⟩ : syracuseStep 30286021 = 5678629) B5678629
theorem B4726993 : Blo 1532463 4726993 := bstep (se 2 (by rfl) ⟨1772622, by rfl⟩ : syracuseStep 4726993 = 3545245) B3545245
theorem B2588881 : Blo 1532463 2588881 := bstep (se 2 (by rfl) ⟨970830, by rfl⟩ : syracuseStep 2588881 = 1941661) B1941661
theorem B2588915 : Blo 1532463 2588915 := bstep (se 1 (by rfl) ⟨1941686, by rfl⟩ : syracuseStep 2588915 = 3883373) B3883373
theorem B3449105 : Blo 1532463 3449105 := bstep (se 2 (by rfl) ⟨1293414, by rfl⟩ : syracuseStep 3449105 = 2586829) B2586829
theorem B3449123 : Blo 1532463 3449123 := bstep (se 1 (by rfl) ⟨2586842, by rfl⟩ : syracuseStep 3449123 = 5173685) B5173685
theorem B5824817 : Blo 1532463 5824817 := bstep (se 2 (by rfl) ⟨2184306, by rfl⟩ : syracuseStep 5824817 = 4368613) B4368613
theorem B11641157 : Blo 1532463 11641157 := bstep (se 4 (by rfl) ⟨1091358, by rfl⟩ : syracuseStep 11641157 = 2182717) B2182717
theorem B5177681 : Blo 1532463 5177681 := bstep (se 2 (by rfl) ⟨1941630, by rfl⟩ : syracuseStep 5177681 = 3883261) B3883261
theorem B7758179 : Blo 1532463 7758179 := bstep (se 1 (by rfl) ⟨5818634, by rfl⟩ : syracuseStep 7758179 = 11637269) B11637269
theorem B3277169 : Blo 1532463 3277169 := bstep (se 2 (by rfl) ⟨1228938, by rfl⟩ : syracuseStep 3277169 = 2457877) B2457877
theorem B2589043 : Blo 1532463 2589043 := bstep (se 1 (by rfl) ⟨1941782, by rfl⟩ : syracuseStep 2589043 = 3883565) B3883565
theorem B4366801 : Blo 1532463 4366801 := bstep (se 2 (by rfl) ⟨1637550, by rfl⟩ : syracuseStep 4366801 = 3275101) B3275101
theorem B2589185 : Blo 1532463 2589185 := bstep (se 2 (by rfl) ⟨970944, by rfl⟩ : syracuseStep 2589185 = 1941889) B1941889
theorem B3932675 : Blo 1532463 3932675 := bstep (se 1 (by rfl) ⟨2949506, by rfl⟩ : syracuseStep 3932675 = 5899013) B5899013
theorem B1942051 : Blo 1532463 1942051 := bstep (se 1 (by rfl) ⟨1456538, by rfl⟩ : syracuseStep 1942051 = 2913077) B2913077
theorem B3449393 : Blo 1532463 3449393 := bstep (se 2 (by rfl) ⟨1293522, by rfl⟩ : syracuseStep 3449393 = 2587045) B2587045
theorem B1532467 : Blo 1532463 1532467 := bstep (se 1 (by rfl) ⟨1149350, by rfl⟩ : syracuseStep 1532467 = 2298701) B2298701
theorem B1532483 : Blo 1532463 1532483 := bstep (se 1 (by rfl) ⟨1149362, by rfl⟩ : syracuseStep 1532483 = 2298725) B2298725
theorem B3449411 : Blo 1532463 3449411 := bstep (se 1 (by rfl) ⟨2587058, by rfl⟩ : syracuseStep 3449411 = 5174117) B5174117
theorem B1532499 : Blo 1532463 1532499 := bstep (se 1 (by rfl) ⟨1149374, by rfl⟩ : syracuseStep 1532499 = 2298749) B2298749
theorem B1532515 : Blo 1532463 1532515 := bstep (se 1 (by rfl) ⟨1149386, by rfl⟩ : syracuseStep 1532515 = 2298773) B2298773
theorem B1532531 : Blo 1532463 1532531 := bstep (se 1 (by rfl) ⟨1149398, by rfl⟩ : syracuseStep 1532531 = 2298797) B2298797
theorem B2589313 : Blo 1532463 2589313 := bstep (se 2 (by rfl) ⟨970992, by rfl⟩ : syracuseStep 2589313 = 1941985) B1941985
theorem B1532547 : Blo 1532463 1532547 := bstep (se 1 (by rfl) ⟨1149410, by rfl⟩ : syracuseStep 1532547 = 2298821) B2298821
theorem B22094477 : Blo 1532463 22094477 := bstep (se 3 (by rfl) ⟨4142714, by rfl⟩ : syracuseStep 22094477 = 8285429) B8285429
theorem B1532563 : Blo 1532463 1532563 := bstep (se 1 (by rfl) ⟨1149422, by rfl⟩ : syracuseStep 1532563 = 2298845) B2298845
theorem B1532579 : Blo 1532463 1532579 := bstep (se 1 (by rfl) ⟨1149434, by rfl⟩ : syracuseStep 1532579 = 2298869) B2298869
theorem B2589347 : Blo 1532463 2589347 := bstep (se 1 (by rfl) ⟨1942010, by rfl⟩ : syracuseStep 2589347 = 3884021) B3884021
theorem B3883697 : Blo 1532463 3883697 := bstep (se 2 (by rfl) ⟨1456386, by rfl⟩ : syracuseStep 3883697 = 2912773) B2912773
theorem B1532595 : Blo 1532463 1532595 := bstep (se 1 (by rfl) ⟨1149446, by rfl⟩ : syracuseStep 1532595 = 2298893) B2298893
theorem B1532611 : Blo 1532463 1532611 := bstep (se 1 (by rfl) ⟨1149458, by rfl⟩ : syracuseStep 1532611 = 2298917) B2298917
theorem B1532627 : Blo 1532463 1532627 := bstep (se 1 (by rfl) ⟨1149470, by rfl⟩ : syracuseStep 1532627 = 2298941) B2298941
theorem B1532643 : Blo 1532463 1532643 := bstep (se 1 (by rfl) ⟨1149482, by rfl⟩ : syracuseStep 1532643 = 2298965) B2298965
theorem B3883747 : Blo 1532463 3883747 := bstep (se 1 (by rfl) ⟨2912810, by rfl⟩ : syracuseStep 3883747 = 5825621) B5825621
theorem B1532659 : Blo 1532463 1532659 := bstep (se 1 (by rfl) ⟨1149494, by rfl⟩ : syracuseStep 1532659 = 2298989) B2298989
theorem B1532675 : Blo 1532463 1532675 := bstep (se 1 (by rfl) ⟨1149506, by rfl⟩ : syracuseStep 1532675 = 2299013) B2299013
theorem B1532691 : Blo 1532463 1532691 := bstep (se 1 (by rfl) ⟨1149518, by rfl⟩ : syracuseStep 1532691 = 2299037) B2299037
theorem B1532707 : Blo 1532463 1532707 := bstep (se 1 (by rfl) ⟨1149530, by rfl⟩ : syracuseStep 1532707 = 2299061) B2299061
theorem B10486577 : Blo 1532463 10486577 := bstep (se 2 (by rfl) ⟨3932466, by rfl⟩ : syracuseStep 10486577 = 7864933) B7864933
theorem B1532723 : Blo 1532463 1532723 := bstep (se 1 (by rfl) ⟨1149542, by rfl⟩ : syracuseStep 1532723 = 2299085) B2299085
theorem B1532739 : Blo 1532463 1532739 := bstep (se 1 (by rfl) ⟨1149554, by rfl⟩ : syracuseStep 1532739 = 2299109) B2299109
theorem B3449681 : Blo 1532463 3449681 := bstep (se 2 (by rfl) ⟨1293630, by rfl⟩ : syracuseStep 3449681 = 2587261) B2587261
theorem B1532755 : Blo 1532463 1532755 := bstep (se 1 (by rfl) ⟨1149566, by rfl⟩ : syracuseStep 1532755 = 2299133) B2299133
theorem B1532771 : Blo 1532463 1532771 := bstep (se 1 (by rfl) ⟨1149578, by rfl⟩ : syracuseStep 1532771 = 2299157) B2299157
theorem B3449699 : Blo 1532463 3449699 := bstep (se 1 (by rfl) ⟨2587274, by rfl⟩ : syracuseStep 3449699 = 5174549) B5174549
theorem B19653475 : Blo 1532463 19653475 := bstep (se 1 (by rfl) ⟨14740106, by rfl⟩ : syracuseStep 19653475 = 29480213) B29480213
theorem B5178221 : Blo 1532463 5178221 := bstep (se 3 (by rfl) ⟨970916, by rfl⟩ : syracuseStep 5178221 = 1941833) B1941833
theorem B9954161 : Blo 1532463 9954161 := bstep (se 2 (by rfl) ⟨3732810, by rfl⟩ : syracuseStep 9954161 = 7465621) B7465621
theorem B11649905 : Blo 1532463 11649905 := bstep (se 2 (by rfl) ⟨4368714, by rfl⟩ : syracuseStep 11649905 = 8737429) B8737429
theorem B1532787 : Blo 1532463 1532787 := bstep (se 1 (by rfl) ⟨1149590, by rfl⟩ : syracuseStep 1532787 = 2299181) B2299181
theorem B3883889 : Blo 1532463 3883889 := bstep (se 2 (by rfl) ⟨1456458, by rfl⟩ : syracuseStep 3883889 = 2912917) B2912917
theorem B1532803 : Blo 1532463 1532803 := bstep (se 1 (by rfl) ⟨1149602, by rfl⟩ : syracuseStep 1532803 = 2299205) B2299205
theorem B8733581 : Blo 1532463 8733581 := bstep (se 3 (by rfl) ⟨1637546, by rfl⟩ : syracuseStep 8733581 = 3275093) B3275093
theorem B1532819 : Blo 1532463 1532819 := bstep (se 1 (by rfl) ⟨1149614, by rfl⟩ : syracuseStep 1532819 = 2299229) B2299229
theorem B1532835 : Blo 1532463 1532835 := bstep (se 1 (by rfl) ⟨1149626, by rfl⟩ : syracuseStep 1532835 = 2299253) B2299253
theorem B5178275 : Blo 1532463 5178275 := bstep (se 1 (by rfl) ⟨3883706, by rfl⟩ : syracuseStep 5178275 = 7767413) B7767413
theorem B1532851 : Blo 1532463 1532851 := bstep (se 1 (by rfl) ⟨1149638, by rfl⟩ : syracuseStep 1532851 = 2299277) B2299277
theorem B1532867 : Blo 1532463 1532867 := bstep (se 1 (by rfl) ⟨1149650, by rfl⟩ : syracuseStep 1532867 = 2299301) B2299301
theorem B1532883 : Blo 1532463 1532883 := bstep (se 1 (by rfl) ⟨1149662, by rfl⟩ : syracuseStep 1532883 = 2299325) B2299325
theorem B1532899 : Blo 1532463 1532899 := bstep (se 1 (by rfl) ⟨1149674, by rfl⟩ : syracuseStep 1532899 = 2299349) B2299349
theorem B4662257 : Blo 1532463 4662257 := bstep (se 2 (by rfl) ⟨1748346, by rfl⟩ : syracuseStep 4662257 = 3496693) B3496693
theorem B1532915 : Blo 1532463 1532915 := bstep (se 1 (by rfl) ⟨1149686, by rfl⟩ : syracuseStep 1532915 = 2299373) B2299373
theorem B1532931 : Blo 1532463 1532931 := bstep (se 1 (by rfl) ⟨1149698, by rfl⟩ : syracuseStep 1532931 = 2299397) B2299397
theorem B1532947 : Blo 1532463 1532947 := bstep (se 1 (by rfl) ⟨1149710, by rfl⟩ : syracuseStep 1532947 = 2299421) B2299421
theorem B1532963 : Blo 1532463 1532963 := bstep (se 1 (by rfl) ⟨1149722, by rfl⟩ : syracuseStep 1532963 = 2299445) B2299445
theorem B7767089 : Blo 1532463 7767089 := bstep (se 2 (by rfl) ⟨2912658, by rfl⟩ : syracuseStep 7767089 = 5825317) B5825317
theorem B1532979 : Blo 1532463 1532979 := bstep (se 1 (by rfl) ⟨1149734, by rfl⟩ : syracuseStep 1532979 = 2299469) B2299469
theorem B1532995 : Blo 1532463 1532995 := bstep (se 1 (by rfl) ⟨1149746, by rfl⟩ : syracuseStep 1532995 = 2299493) B2299493
theorem B1533011 : Blo 1532463 1533011 := bstep (se 1 (by rfl) ⟨1149758, by rfl⟩ : syracuseStep 1533011 = 2299517) B2299517
theorem B1533027 : Blo 1532463 1533027 := bstep (se 1 (by rfl) ⟨1149770, by rfl⟩ : syracuseStep 1533027 = 2299541) B2299541
theorem B3449969 : Blo 1532463 3449969 := bstep (se 2 (by rfl) ⟨1293738, by rfl⟩ : syracuseStep 3449969 = 2587477) B2587477
theorem B1533043 : Blo 1532463 1533043 := bstep (se 1 (by rfl) ⟨1149782, by rfl⟩ : syracuseStep 1533043 = 2299565) B2299565
theorem B1533059 : Blo 1532463 1533059 := bstep (se 1 (by rfl) ⟨1149794, by rfl⟩ : syracuseStep 1533059 = 2299589) B2299589
theorem B3449987 : Blo 1532463 3449987 := bstep (se 1 (by rfl) ⟨2587490, by rfl⟩ : syracuseStep 3449987 = 5174981) B5174981
theorem B9831557 : Blo 1532463 9831557 := bstep (se 4 (by rfl) ⟨921708, by rfl⟩ : syracuseStep 9831557 = 1843417) B1843417
theorem B7758989 : Blo 1532463 7758989 := bstep (se 3 (by rfl) ⟨1454810, by rfl⟩ : syracuseStep 7758989 = 2909621) B2909621
theorem B17712269 : Blo 1532463 17712269 := bstep (se 3 (by rfl) ⟨3321050, by rfl⟩ : syracuseStep 17712269 = 6642101) B6642101
theorem B1533075 : Blo 1532463 1533075 := bstep (se 1 (by rfl) ⟨1149806, by rfl⟩ : syracuseStep 1533075 = 2299613) B2299613
theorem B1533091 : Blo 1532463 1533091 := bstep (se 1 (by rfl) ⟨1149818, by rfl⟩ : syracuseStep 1533091 = 2299637) B2299637
theorem B5178545 : Blo 1532463 5178545 := bstep (se 2 (by rfl) ⟨1941954, by rfl⟩ : syracuseStep 5178545 = 3883909) B3883909
theorem B1533107 : Blo 1532463 1533107 := bstep (se 1 (by rfl) ⟨1149830, by rfl⟩ : syracuseStep 1533107 = 2299661) B2299661
theorem B1533123 : Blo 1532463 1533123 := bstep (se 1 (by rfl) ⟨1149842, by rfl⟩ : syracuseStep 1533123 = 2299685) B2299685
theorem B1533139 : Blo 1532463 1533139 := bstep (se 1 (by rfl) ⟨1149854, by rfl⟩ : syracuseStep 1533139 = 2299709) B2299709
theorem B1533155 : Blo 1532463 1533155 := bstep (se 1 (by rfl) ⟨1149866, by rfl⟩ : syracuseStep 1533155 = 2299733) B2299733
theorem B1533171 : Blo 1532463 1533171 := bstep (se 1 (by rfl) ⟨1149878, by rfl⟩ : syracuseStep 1533171 = 2299757) B2299757
theorem B1533187 : Blo 1532463 1533187 := bstep (se 1 (by rfl) ⟨1149890, by rfl⟩ : syracuseStep 1533187 = 2299781) B2299781
theorem B1533203 : Blo 1532463 1533203 := bstep (se 1 (by rfl) ⟨1149902, by rfl⟩ : syracuseStep 1533203 = 2299805) B2299805
theorem B1533219 : Blo 1532463 1533219 := bstep (se 1 (by rfl) ⟨1149914, by rfl⟩ : syracuseStep 1533219 = 2299829) B2299829
theorem B1533235 : Blo 1532463 1533235 := bstep (se 1 (by rfl) ⟨1149926, by rfl⟩ : syracuseStep 1533235 = 2299853) B2299853
theorem B1533251 : Blo 1532463 1533251 := bstep (se 1 (by rfl) ⟨1149938, by rfl⟩ : syracuseStep 1533251 = 2299877) B2299877
theorem B1533267 : Blo 1532463 1533267 := bstep (se 1 (by rfl) ⟨1149950, by rfl⟩ : syracuseStep 1533267 = 2299901) B2299901
theorem B1533283 : Blo 1532463 1533283 := bstep (se 1 (by rfl) ⟨1149962, by rfl⟩ : syracuseStep 1533283 = 2299925) B2299925
theorem B4146545 : Blo 1532463 4146545 := bstep (se 2 (by rfl) ⟨1554954, by rfl⟩ : syracuseStep 4146545 = 3109909) B3109909
theorem B1533299 : Blo 1532463 1533299 := bstep (se 1 (by rfl) ⟨1149974, by rfl⟩ : syracuseStep 1533299 = 2299949) B2299949
theorem B1533315 : Blo 1532463 1533315 := bstep (se 1 (by rfl) ⟨1149986, by rfl⟩ : syracuseStep 1533315 = 2299973) B2299973
theorem B3450257 : Blo 1532463 3450257 := bstep (se 2 (by rfl) ⟨1293846, by rfl⟩ : syracuseStep 3450257 = 2587693) B2587693
theorem B1533331 : Blo 1532463 1533331 := bstep (se 1 (by rfl) ⟨1149998, by rfl⟩ : syracuseStep 1533331 = 2299997) B2299997
theorem B1533347 : Blo 1532463 1533347 := bstep (se 1 (by rfl) ⟨1150010, by rfl⟩ : syracuseStep 1533347 = 2300021) B2300021
theorem B3450275 : Blo 1532463 3450275 := bstep (se 1 (by rfl) ⟨2587706, by rfl⟩ : syracuseStep 3450275 = 5175413) B5175413
theorem B1533363 : Blo 1532463 1533363 := bstep (se 1 (by rfl) ⟨1150022, by rfl⟩ : syracuseStep 1533363 = 2300045) B2300045
theorem B18646453 : Blo 1532463 18646453 := bstep (se 5 (by rfl) ⟨874052, by rfl⟩ : syracuseStep 18646453 = 1748105) B1748105
theorem B1533379 : Blo 1532463 1533379 := bstep (se 1 (by rfl) ⟨1150034, by rfl⟩ : syracuseStep 1533379 = 2300069) B2300069
theorem B1533395 : Blo 1532463 1533395 := bstep (se 1 (by rfl) ⟨1150046, by rfl⟩ : syracuseStep 1533395 = 2300093) B2300093
theorem B18646499 : Blo 1532463 18646499 := bstep (se 1 (by rfl) ⟨13984874, by rfl⟩ : syracuseStep 18646499 = 27969749) B27969749
theorem B1533411 : Blo 1532463 1533411 := bstep (se 1 (by rfl) ⟨1150058, by rfl⟩ : syracuseStep 1533411 = 2300117) B2300117
theorem B1533427 : Blo 1532463 1533427 := bstep (se 1 (by rfl) ⟨1150070, by rfl⟩ : syracuseStep 1533427 = 2300141) B2300141
theorem B1533443 : Blo 1532463 1533443 := bstep (se 1 (by rfl) ⟨1150082, by rfl⟩ : syracuseStep 1533443 = 2300165) B2300165
theorem B1533459 : Blo 1532463 1533459 := bstep (se 1 (by rfl) ⟨1150094, by rfl⟩ : syracuseStep 1533459 = 2300189) B2300189
theorem B1533475 : Blo 1532463 1533475 := bstep (se 1 (by rfl) ⟨1150106, by rfl⟩ : syracuseStep 1533475 = 2300213) B2300213
theorem B1533491 : Blo 1532463 1533491 := bstep (se 1 (by rfl) ⟨1150118, by rfl⟩ : syracuseStep 1533491 = 2300237) B2300237
theorem B1533507 : Blo 1532463 1533507 := bstep (se 1 (by rfl) ⟨1150130, by rfl⟩ : syracuseStep 1533507 = 2300261) B2300261
theorem B1533523 : Blo 1532463 1533523 := bstep (se 1 (by rfl) ⟨1150142, by rfl⟩ : syracuseStep 1533523 = 2300285) B2300285
theorem B1533539 : Blo 1532463 1533539 := bstep (se 1 (by rfl) ⟨1150154, by rfl⟩ : syracuseStep 1533539 = 2300309) B2300309
theorem B1533555 : Blo 1532463 1533555 := bstep (se 1 (by rfl) ⟨1150166, by rfl⟩ : syracuseStep 1533555 = 2300333) B2300333
theorem B1533571 : Blo 1532463 1533571 := bstep (se 1 (by rfl) ⟨1150178, by rfl⟩ : syracuseStep 1533571 = 2300357) B2300357
theorem B1533587 : Blo 1532463 1533587 := bstep (se 1 (by rfl) ⟨1150190, by rfl⟩ : syracuseStep 1533587 = 2300381) B2300381
theorem B1533603 : Blo 1532463 1533603 := bstep (se 1 (by rfl) ⟨1150202, by rfl⟩ : syracuseStep 1533603 = 2300405) B2300405
theorem B3450545 : Blo 1532463 3450545 := bstep (se 2 (by rfl) ⟨1293954, by rfl⟩ : syracuseStep 3450545 = 2587909) B2587909
theorem B1533619 : Blo 1532463 1533619 := bstep (se 1 (by rfl) ⟨1150214, by rfl⟩ : syracuseStep 1533619 = 2300429) B2300429
theorem B3450563 : Blo 1532463 3450563 := bstep (se 1 (by rfl) ⟨2587922, by rfl⟩ : syracuseStep 3450563 = 5175845) B5175845
theorem B1533635 : Blo 1532463 1533635 := bstep (se 1 (by rfl) ⟨1150226, by rfl⟩ : syracuseStep 1533635 = 2300453) B2300453
theorem B4368077 : Blo 1532463 4368077 := bstep (se 3 (by rfl) ⟨819014, by rfl⟩ : syracuseStep 4368077 = 1638029) B1638029
theorem B1533651 : Blo 1532463 1533651 := bstep (se 1 (by rfl) ⟨1150238, by rfl⟩ : syracuseStep 1533651 = 2300477) B2300477
theorem B1533667 : Blo 1532463 1533667 := bstep (se 1 (by rfl) ⟨1150250, by rfl⟩ : syracuseStep 1533667 = 2300501) B2300501
theorem B14739185 : Blo 1532463 14739185 := bstep (se 2 (by rfl) ⟨5527194, by rfl⟩ : syracuseStep 14739185 = 11054389) B11054389
theorem B1533683 : Blo 1532463 1533683 := bstep (se 1 (by rfl) ⟨1150262, by rfl⟩ : syracuseStep 1533683 = 2300525) B2300525
theorem B1533699 : Blo 1532463 1533699 := bstep (se 1 (by rfl) ⟨1150274, by rfl⟩ : syracuseStep 1533699 = 2300549) B2300549
theorem B1533715 : Blo 1532463 1533715 := bstep (se 1 (by rfl) ⟨1150286, by rfl⟩ : syracuseStep 1533715 = 2300573) B2300573
theorem B1533731 : Blo 1532463 1533731 := bstep (se 1 (by rfl) ⟨1150298, by rfl⟩ : syracuseStep 1533731 = 2300597) B2300597
theorem B2910001 : Blo 1532463 2910001 := bstep (se 2 (by rfl) ⟨1091250, by rfl⟩ : syracuseStep 2910001 = 2182501) B2182501
theorem B8734513 : Blo 1532463 8734513 := bstep (se 2 (by rfl) ⟨3275442, by rfl⟩ : syracuseStep 8734513 = 6550885) B6550885
theorem B1533747 : Blo 1532463 1533747 := bstep (se 1 (by rfl) ⟨1150310, by rfl⟩ : syracuseStep 1533747 = 2300621) B2300621
theorem B1533763 : Blo 1532463 1533763 := bstep (se 1 (by rfl) ⟨1150322, by rfl⟩ : syracuseStep 1533763 = 2300645) B2300645
theorem B1533779 : Blo 1532463 1533779 := bstep (se 1 (by rfl) ⟨1150334, by rfl⟩ : syracuseStep 1533779 = 2300669) B2300669
theorem B1533795 : Blo 1532463 1533795 := bstep (se 1 (by rfl) ⟨1150346, by rfl⟩ : syracuseStep 1533795 = 2300693) B2300693
theorem B1533811 : Blo 1532463 1533811 := bstep (se 1 (by rfl) ⟨1150358, by rfl⟩ : syracuseStep 1533811 = 2300717) B2300717
theorem B1533827 : Blo 1532463 1533827 := bstep (se 1 (by rfl) ⟨1150370, by rfl⟩ : syracuseStep 1533827 = 2300741) B2300741
theorem B4368259 : Blo 1532463 4368259 := bstep (se 1 (by rfl) ⟨3276194, by rfl⟩ : syracuseStep 4368259 = 6552389) B6552389
theorem B13092749 : Blo 1532463 13092749 := bstep (se 3 (by rfl) ⟨2454890, by rfl⟩ : syracuseStep 13092749 = 4909781) B4909781
theorem B1533843 : Blo 1532463 1533843 := bstep (se 1 (by rfl) ⟨1150382, by rfl⟩ : syracuseStep 1533843 = 2300765) B2300765
theorem B1533859 : Blo 1532463 1533859 := bstep (se 1 (by rfl) ⟨1150394, by rfl⟩ : syracuseStep 1533859 = 2300789) B2300789
theorem B4368305 : Blo 1532463 4368305 := bstep (se 2 (by rfl) ⟨1638114, by rfl⟩ : syracuseStep 4368305 = 3276229) B3276229
theorem B1533875 : Blo 1532463 1533875 := bstep (se 1 (by rfl) ⟨1150406, by rfl⟩ : syracuseStep 1533875 = 2300813) B2300813
theorem B1533891 : Blo 1532463 1533891 := bstep (se 1 (by rfl) ⟨1150418, by rfl⟩ : syracuseStep 1533891 = 2300837) B2300837
theorem B2910161 : Blo 1532463 2910161 := bstep (se 2 (by rfl) ⟨1091310, by rfl⟩ : syracuseStep 2910161 = 2182621) B2182621
theorem B3450833 : Blo 1532463 3450833 := bstep (se 2 (by rfl) ⟨1294062, by rfl⟩ : syracuseStep 3450833 = 2588125) B2588125
theorem B1533907 : Blo 1532463 1533907 := bstep (se 1 (by rfl) ⟨1150430, by rfl⟩ : syracuseStep 1533907 = 2300861) B2300861
theorem B3450851 : Blo 1532463 3450851 := bstep (se 1 (by rfl) ⟨2588138, by rfl⟩ : syracuseStep 3450851 = 5176277) B5176277
theorem B1533923 : Blo 1532463 1533923 := bstep (se 1 (by rfl) ⟨1150442, by rfl⟩ : syracuseStep 1533923 = 2300885) B2300885
theorem B1533939 : Blo 1532463 1533939 := bstep (se 1 (by rfl) ⟨1150454, by rfl⟩ : syracuseStep 1533939 = 2300909) B2300909
theorem B1533955 : Blo 1532463 1533955 := bstep (se 1 (by rfl) ⟨1150466, by rfl⟩ : syracuseStep 1533955 = 2300933) B2300933
theorem B4147213 : Blo 1532463 4147213 := bstep (se 3 (by rfl) ⟨777602, by rfl⟩ : syracuseStep 4147213 = 1555205) B1555205
theorem B8857613 : Blo 1532463 8857613 := bstep (se 3 (by rfl) ⟨1660802, by rfl⟩ : syracuseStep 8857613 = 3321605) B3321605
theorem B1533971 : Blo 1532463 1533971 := bstep (se 1 (by rfl) ⟨1150478, by rfl⟩ : syracuseStep 1533971 = 2300957) B2300957
theorem B5523491 : Blo 1532463 5523491 := bstep (se 1 (by rfl) ⟨4142618, by rfl⟩ : syracuseStep 5523491 = 8285237) B8285237
theorem B1533987 : Blo 1532463 1533987 := bstep (se 1 (by rfl) ⟨1150490, by rfl⟩ : syracuseStep 1533987 = 2300981) B2300981
theorem B1534003 : Blo 1532463 1534003 := bstep (se 1 (by rfl) ⟨1150502, by rfl⟩ : syracuseStep 1534003 = 2301005) B2301005
theorem B1534019 : Blo 1532463 1534019 := bstep (se 1 (by rfl) ⟨1150514, by rfl⟩ : syracuseStep 1534019 = 2301029) B2301029
theorem B1534035 : Blo 1532463 1534035 := bstep (se 1 (by rfl) ⟨1150526, by rfl⟩ : syracuseStep 1534035 = 2301053) B2301053
theorem B1534051 : Blo 1532463 1534051 := bstep (se 1 (by rfl) ⟨1150538, by rfl⟩ : syracuseStep 1534051 = 2301077) B2301077
theorem B8407153 : Blo 1532463 8407153 := bstep (se 2 (by rfl) ⟨3152682, by rfl⟩ : syracuseStep 8407153 = 6305365) B6305365
theorem B1534067 : Blo 1532463 1534067 := bstep (se 1 (by rfl) ⟨1150550, by rfl⟩ : syracuseStep 1534067 = 2301101) B2301101
theorem B1534083 : Blo 1532463 1534083 := bstep (se 1 (by rfl) ⟨1150562, by rfl⟩ : syracuseStep 1534083 = 2301125) B2301125
theorem B1534099 : Blo 1532463 1534099 := bstep (se 1 (by rfl) ⟨1150574, by rfl⟩ : syracuseStep 1534099 = 2301149) B2301149
theorem B1534115 : Blo 1532463 1534115 := bstep (se 1 (by rfl) ⟨1150586, by rfl⟩ : syracuseStep 1534115 = 2301173) B2301173
theorem B1534131 : Blo 1532463 1534131 := bstep (se 1 (by rfl) ⟨1150598, by rfl⟩ : syracuseStep 1534131 = 2301197) B2301197
theorem B1534147 : Blo 1532463 1534147 := bstep (se 1 (by rfl) ⟨1150610, by rfl⟩ : syracuseStep 1534147 = 2301221) B2301221
theorem B1534163 : Blo 1532463 1534163 := bstep (se 1 (by rfl) ⟨1150622, by rfl⟩ : syracuseStep 1534163 = 2301245) B2301245
theorem B9824483 : Blo 1532463 9824483 := bstep (se 1 (by rfl) ⟨7368362, by rfl⟩ : syracuseStep 9824483 = 14736725) B14736725
theorem B1534179 : Blo 1532463 1534179 := bstep (se 1 (by rfl) ⟨1150634, by rfl⟩ : syracuseStep 1534179 = 2301269) B2301269
theorem B3451121 : Blo 1532463 3451121 := bstep (se 2 (by rfl) ⟨1294170, by rfl⟩ : syracuseStep 3451121 = 2588341) B2588341
theorem B1534195 : Blo 1532463 1534195 := bstep (se 1 (by rfl) ⟨1150646, by rfl⟩ : syracuseStep 1534195 = 2301293) B2301293
theorem B3451139 : Blo 1532463 3451139 := bstep (se 1 (by rfl) ⟨2588354, by rfl⟩ : syracuseStep 3451139 = 5176709) B5176709
theorem B1534211 : Blo 1532463 1534211 := bstep (se 1 (by rfl) ⟨1150658, by rfl⟩ : syracuseStep 1534211 = 2301317) B2301317
theorem B1534227 : Blo 1532463 1534227 := bstep (se 1 (by rfl) ⟨1150670, by rfl⟩ : syracuseStep 1534227 = 2301341) B2301341
theorem B1534243 : Blo 1532463 1534243 := bstep (se 1 (by rfl) ⟨1150682, by rfl⟩ : syracuseStep 1534243 = 2301365) B2301365
theorem B1534259 : Blo 1532463 1534259 := bstep (se 1 (by rfl) ⟨1150694, by rfl⟩ : syracuseStep 1534259 = 2301389) B2301389
theorem B1534275 : Blo 1532463 1534275 := bstep (se 1 (by rfl) ⟨1150706, by rfl⟩ : syracuseStep 1534275 = 2301413) B2301413
theorem B1534291 : Blo 1532463 1534291 := bstep (se 1 (by rfl) ⟨1150718, by rfl⟩ : syracuseStep 1534291 = 2301437) B2301437
theorem B2910563 : Blo 1532463 2910563 := bstep (se 1 (by rfl) ⟨2182922, by rfl⟩ : syracuseStep 2910563 = 4365845) B4365845
theorem B1534307 : Blo 1532463 1534307 := bstep (se 1 (by rfl) ⟨1150730, by rfl⟩ : syracuseStep 1534307 = 2301461) B2301461
theorem B1534323 : Blo 1532463 1534323 := bstep (se 1 (by rfl) ⟨1150742, by rfl⟩ : syracuseStep 1534323 = 2301485) B2301485
theorem B1534339 : Blo 1532463 1534339 := bstep (se 1 (by rfl) ⟨1150754, by rfl⟩ : syracuseStep 1534339 = 2301509) B2301509
theorem B1534355 : Blo 1532463 1534355 := bstep (se 1 (by rfl) ⟨1150766, by rfl⟩ : syracuseStep 1534355 = 2301533) B2301533
theorem B5818787 : Blo 1532463 5818787 := bstep (se 1 (by rfl) ⟨4364090, by rfl⟩ : syracuseStep 5818787 = 8728181) B8728181
theorem B1534371 : Blo 1532463 1534371 := bstep (se 1 (by rfl) ⟨1150778, by rfl⟩ : syracuseStep 1534371 = 2301557) B2301557
theorem B1534387 : Blo 1532463 1534387 := bstep (se 1 (by rfl) ⟨1150790, by rfl⟩ : syracuseStep 1534387 = 2301581) B2301581
theorem B1534403 : Blo 1532463 1534403 := bstep (se 1 (by rfl) ⟨1150802, by rfl⟩ : syracuseStep 1534403 = 2301605) B2301605
theorem B1534419 : Blo 1532463 1534419 := bstep (se 1 (by rfl) ⟨1150814, by rfl⟩ : syracuseStep 1534419 = 2301629) B2301629
theorem B1534435 : Blo 1532463 1534435 := bstep (se 1 (by rfl) ⟨1150826, by rfl⟩ : syracuseStep 1534435 = 2301653) B2301653
theorem B1534451 : Blo 1532463 1534451 := bstep (se 1 (by rfl) ⟨1150838, by rfl⟩ : syracuseStep 1534451 = 2301677) B2301677
theorem B2763281 : Blo 1532463 2763281 := bstep (se 2 (by rfl) ⟨1036230, by rfl⟩ : syracuseStep 2763281 = 2072461) B2072461
theorem B3451409 : Blo 1532463 3451409 := bstep (se 2 (by rfl) ⟨1294278, by rfl⟩ : syracuseStep 3451409 = 2588557) B2588557
theorem B3451427 : Blo 1532463 3451427 := bstep (se 1 (by rfl) ⟨2588570, by rfl⟩ : syracuseStep 3451427 = 5177141) B5177141
theorem B3107377 : Blo 1532463 3107377 := bstep (se 2 (by rfl) ⟨1165266, by rfl⟩ : syracuseStep 3107377 = 2330533) B2330533
theorem B7473869 : Blo 1532463 7473869 := bstep (se 3 (by rfl) ⟨1401350, by rfl⟩ : syracuseStep 7473869 = 2802701) B2802701
theorem B6548273 : Blo 1532463 6548273 := bstep (se 2 (by rfl) ⟨2455602, by rfl⟩ : syracuseStep 6548273 = 4911205) B4911205
theorem B3451697 : Blo 1532463 3451697 := bstep (se 2 (by rfl) ⟨1294386, by rfl⟩ : syracuseStep 3451697 = 2588773) B2588773
theorem B3451715 : Blo 1532463 3451715 := bstep (se 1 (by rfl) ⟨2588786, by rfl⟩ : syracuseStep 3451715 = 5177573) B5177573
theorem B6548323 : Blo 1532463 6548323 := bstep (se 1 (by rfl) ⟨4911242, by rfl⟩ : syracuseStep 6548323 = 9822485) B9822485
theorem B5172173 : Blo 1532463 5172173 := bstep (se 3 (by rfl) ⟨969782, by rfl⟩ : syracuseStep 5172173 = 1939565) B1939565
theorem B5172227 : Blo 1532463 5172227 := bstep (se 1 (by rfl) ⟨3879170, by rfl⟩ : syracuseStep 5172227 = 7758341) B7758341
theorem B3451985 : Blo 1532463 3451985 := bstep (se 2 (by rfl) ⟨1294494, by rfl⟩ : syracuseStep 3451985 = 2588989) B2588989
theorem B2362465 : Blo 1532463 2362465 := bstep (se 2 (by rfl) ⟨885924, by rfl⟩ : syracuseStep 2362465 = 1771849) B1771849
theorem B3452003 : Blo 1532463 3452003 := bstep (se 1 (by rfl) ⟨2589002, by rfl⟩ : syracuseStep 3452003 = 5178005) B5178005
theorem B2624627 : Blo 1532463 2624627 := bstep (se 1 (by rfl) ⟨1968470, by rfl⟩ : syracuseStep 2624627 = 3936941) B3936941
theorem B2182307 : Blo 1532463 2182307 := bstep (se 1 (by rfl) ⟨1636730, by rfl⟩ : syracuseStep 2182307 = 3273461) B3273461
theorem B2911459 : Blo 1532463 2911459 := bstep (se 1 (by rfl) ⟨2183594, by rfl⟩ : syracuseStep 2911459 = 4367189) B4367189
theorem B8735971 : Blo 1532463 8735971 := bstep (se 1 (by rfl) ⟨6551978, by rfl⟩ : syracuseStep 8735971 = 13103957) B13103957
theorem B4910321 : Blo 1532463 4910321 := bstep (se 2 (by rfl) ⟨1841370, by rfl⟩ : syracuseStep 4910321 = 3682741) B3682741
theorem B5172497 : Blo 1532463 5172497 := bstep (se 2 (by rfl) ⟨1939686, by rfl⟩ : syracuseStep 5172497 = 3879373) B3879373
theorem B23604533 : Blo 1532463 23604533 := bstep (se 5 (by rfl) ⟨1106462, by rfl⟩ : syracuseStep 23604533 = 2212925) B2212925
theorem B3452273 : Blo 1532463 3452273 := bstep (se 2 (by rfl) ⟨1294602, by rfl⟩ : syracuseStep 3452273 = 2589205) B2589205
theorem B2911619 : Blo 1532463 2911619 := bstep (se 1 (by rfl) ⟨2183714, by rfl⟩ : syracuseStep 2911619 = 4367429) B4367429
theorem B3452291 : Blo 1532463 3452291 := bstep (se 1 (by rfl) ⟨2589218, by rfl⟩ : syracuseStep 3452291 = 5178437) B5178437
theorem B5819789 : Blo 1532463 5819789 := bstep (se 3 (by rfl) ⟨1091210, by rfl⟩ : syracuseStep 5819789 = 2182421) B2182421
theorem B17477045 : Blo 1532463 17477045 := bstep (se 5 (by rfl) ⟨819236, by rfl⟩ : syracuseStep 17477045 = 1638473) B1638473
theorem B1724035 : Blo 1532463 1724035 := bstep (se 1 (by rfl) ⟨1293026, by rfl⟩ : syracuseStep 1724035 = 2586053) B2586053
theorem B8736497 : Blo 1532463 8736497 := bstep (se 2 (by rfl) ⟨3276186, by rfl⟩ : syracuseStep 8736497 = 6552373) B6552373
theorem B1724179 : Blo 1532463 1724179 := bstep (se 1 (by rfl) ⟨1293134, by rfl⟩ : syracuseStep 1724179 = 2586269) B2586269
theorem B2182945 : Blo 1532463 2182945 := bstep (se 2 (by rfl) ⟨818604, by rfl⟩ : syracuseStep 2182945 = 1637209) B1637209
theorem B5173037 : Blo 1532463 5173037 := bstep (se 3 (by rfl) ⟨969944, by rfl⟩ : syracuseStep 5173037 = 1939889) B1939889
theorem B5173091 : Blo 1532463 5173091 := bstep (se 1 (by rfl) ⟨3879818, by rfl⟩ : syracuseStep 5173091 = 7759637) B7759637
theorem B2183059 : Blo 1532463 2183059 := bstep (se 1 (by rfl) ⟨1637294, by rfl⟩ : syracuseStep 2183059 = 3274589) B3274589
theorem B1724323 : Blo 1532463 1724323 := bstep (se 1 (by rfl) ⟨1293242, by rfl⟩ : syracuseStep 1724323 = 2586485) B2586485
theorem B5681123 : Blo 1532463 5681123 := bstep (se 1 (by rfl) ⟨4260842, by rfl⟩ : syracuseStep 5681123 = 8521685) B8521685
theorem B7761905 : Blo 1532463 7761905 := bstep (se 2 (by rfl) ⟨2910714, by rfl⟩ : syracuseStep 7761905 = 5821429) B5821429
theorem B12439565 : Blo 1532463 12439565 := bstep (se 3 (by rfl) ⟨2332418, by rfl⟩ : syracuseStep 12439565 = 4664837) B4664837
theorem B1724467 : Blo 1532463 1724467 := bstep (se 1 (by rfl) ⟨1293350, by rfl⟩ : syracuseStep 1724467 = 2586701) B2586701
theorem B5173361 : Blo 1532463 5173361 := bstep (se 2 (by rfl) ⟨1940010, by rfl⟩ : syracuseStep 5173361 = 3880021) B3880021
theorem B4550833 : Blo 1532463 4550833 := bstep (se 2 (by rfl) ⟨1706562, by rfl⟩ : syracuseStep 4550833 = 3413125) B3413125
theorem B1724611 : Blo 1532463 1724611 := bstep (se 1 (by rfl) ⟨1293458, by rfl⟩ : syracuseStep 1724611 = 2586917) B2586917
theorem B2101459 : Blo 1532463 2101459 := bstep (se 1 (by rfl) ⟨1576094, by rfl⟩ : syracuseStep 2101459 = 3152189) B3152189
theorem B12439793 : Blo 1532463 12439793 := bstep (se 2 (by rfl) ⟨4664922, by rfl⟩ : syracuseStep 12439793 = 9329845) B9329845
theorem B6820145 : Blo 1532463 6820145 := bstep (se 2 (by rfl) ⟨2557554, by rfl⟩ : syracuseStep 6820145 = 5115109) B5115109
theorem B1724755 : Blo 1532463 1724755 := bstep (se 1 (by rfl) ⟨1293566, by rfl⟩ : syracuseStep 1724755 = 2587133) B2587133
theorem B19640717 : Blo 1532463 19640717 := bstep (se 3 (by rfl) ⟨3682634, by rfl⟩ : syracuseStep 19640717 = 7365269) B7365269
theorem B5984675 : Blo 1532463 5984675 := bstep (se 1 (by rfl) ⟨4488506, by rfl⟩ : syracuseStep 5984675 = 8977013) B8977013
theorem B2912689 : Blo 1532463 2912689 := bstep (se 2 (by rfl) ⟨1092258, by rfl⟩ : syracuseStep 2912689 = 2184517) B2184517
theorem B4428227 : Blo 1532463 4428227 := bstep (se 1 (by rfl) ⟨3321170, by rfl⟩ : syracuseStep 4428227 = 6642341) B6642341
theorem B1724899 : Blo 1532463 1724899 := bstep (se 1 (by rfl) ⟨1293674, by rfl⟩ : syracuseStep 1724899 = 2587349) B2587349
theorem B1725043 : Blo 1532463 1725043 := bstep (se 1 (by rfl) ⟨1293782, by rfl⟩ : syracuseStep 1725043 = 2587565) B2587565
theorem B5173901 : Blo 1532463 5173901 := bstep (se 3 (by rfl) ⟨970106, by rfl⟩ : syracuseStep 5173901 = 1940213) B1940213
theorem B5526157 : Blo 1532463 5526157 := bstep (se 3 (by rfl) ⟨1036154, by rfl⟩ : syracuseStep 5526157 = 2072309) B2072309
theorem B5173955 : Blo 1532463 5173955 := bstep (se 1 (by rfl) ⟨3880466, by rfl⟩ : syracuseStep 5173955 = 7760933) B7760933
theorem B1725187 : Blo 1532463 1725187 := bstep (se 1 (by rfl) ⟨1293890, by rfl⟩ : syracuseStep 1725187 = 2587781) B2587781
theorem B10490629 : Blo 1532463 10490629 := bstep (se 4 (by rfl) ⟨983496, by rfl⟩ : syracuseStep 10490629 = 1966993) B1966993
theorem B3879697 : Blo 1532463 3879697 := bstep (se 2 (by rfl) ⟨1454886, by rfl⟩ : syracuseStep 3879697 = 2909773) B2909773
theorem B9327437 : Blo 1532463 9327437 := bstep (se 3 (by rfl) ⟨1748894, by rfl⟩ : syracuseStep 9327437 = 3497789) B3497789
theorem B2298707 : Blo 1532463 2298707 := bstep (se 1 (by rfl) ⟨1724030, by rfl⟩ : syracuseStep 2298707 = 3448061) B3448061
theorem B2298737 : Blo 1532463 2298737 := bstep (se 2 (by rfl) ⟨862026, by rfl⟩ : syracuseStep 2298737 = 1724053) B1724053
theorem B2298755 : Blo 1532463 2298755 := bstep (se 1 (by rfl) ⟨1724066, by rfl⟩ : syracuseStep 2298755 = 3448133) B3448133
theorem B1725331 : Blo 1532463 1725331 := bstep (se 1 (by rfl) ⟨1293998, by rfl⟩ : syracuseStep 1725331 = 2587997) B2587997
theorem B2298785 : Blo 1532463 2298785 := bstep (se 2 (by rfl) ⟨862044, by rfl⟩ : syracuseStep 2298785 = 1724089) B1724089
theorem B2298803 : Blo 1532463 2298803 := bstep (se 1 (by rfl) ⟨1724102, by rfl⟩ : syracuseStep 2298803 = 3448205) B3448205
theorem B2298833 : Blo 1532463 2298833 := bstep (se 2 (by rfl) ⟨862062, by rfl⟩ : syracuseStep 2298833 = 1724125) B1724125
theorem B5174225 : Blo 1532463 5174225 := bstep (se 2 (by rfl) ⟨1940334, by rfl⟩ : syracuseStep 5174225 = 3880669) B3880669
theorem B2298851 : Blo 1532463 2298851 := bstep (se 1 (by rfl) ⟨1724138, by rfl⟩ : syracuseStep 2298851 = 3448277) B3448277
theorem B2298881 : Blo 1532463 2298881 := bstep (se 2 (by rfl) ⟨862080, by rfl⟩ : syracuseStep 2298881 = 1724161) B1724161
theorem B2298899 : Blo 1532463 2298899 := bstep (se 1 (by rfl) ⟨1724174, by rfl⟩ : syracuseStep 2298899 = 3448349) B3448349
theorem B3879971 : Blo 1532463 3879971 := bstep (se 1 (by rfl) ⟨2909978, by rfl⟩ : syracuseStep 3879971 = 5819957) B5819957
theorem B1725475 : Blo 1532463 1725475 := bstep (se 1 (by rfl) ⟨1294106, by rfl⟩ : syracuseStep 1725475 = 2588213) B2588213
theorem B2298929 : Blo 1532463 2298929 := bstep (se 2 (by rfl) ⟨862098, by rfl⟩ : syracuseStep 2298929 = 1724197) B1724197
theorem B2298947 : Blo 1532463 2298947 := bstep (se 1 (by rfl) ⟨1724210, by rfl⟩ : syracuseStep 2298947 = 3448421) B3448421
theorem B2298977 : Blo 1532463 2298977 := bstep (se 2 (by rfl) ⟨862116, by rfl⟩ : syracuseStep 2298977 = 1724233) B1724233
theorem B13988963 : Blo 1532463 13988963 := bstep (se 1 (by rfl) ⟨10491722, by rfl⟩ : syracuseStep 13988963 = 20983445) B20983445
theorem B2298995 : Blo 1532463 2298995 := bstep (se 1 (by rfl) ⟨1724246, by rfl⟩ : syracuseStep 2298995 = 3448493) B3448493
theorem B2299025 : Blo 1532463 2299025 := bstep (se 2 (by rfl) ⟨862134, by rfl⟩ : syracuseStep 2299025 = 1724269) B1724269
theorem B2299043 : Blo 1532463 2299043 := bstep (se 1 (by rfl) ⟨1724282, by rfl⟩ : syracuseStep 2299043 = 3448565) B3448565
theorem B8737955 : Blo 1532463 8737955 := bstep (se 1 (by rfl) ⟨6553466, by rfl⟩ : syracuseStep 8737955 = 13106933) B13106933
theorem B3273905 : Blo 1532463 3273905 := bstep (se 2 (by rfl) ⟨1227714, by rfl⟩ : syracuseStep 3273905 = 2455429) B2455429
theorem B1725619 : Blo 1532463 1725619 := bstep (se 1 (by rfl) ⟨1294214, by rfl⟩ : syracuseStep 1725619 = 2588429) B2588429
theorem B2299073 : Blo 1532463 2299073 := bstep (se 2 (by rfl) ⟨862152, by rfl⟩ : syracuseStep 2299073 = 1724305) B1724305
theorem B6550733 : Blo 1532463 6550733 := bstep (se 3 (by rfl) ⟨1228262, by rfl⟩ : syracuseStep 6550733 = 2456525) B2456525
theorem B2299091 : Blo 1532463 2299091 := bstep (se 1 (by rfl) ⟨1724318, by rfl⟩ : syracuseStep 2299091 = 3448637) B3448637
theorem B2184403 : Blo 1532463 2184403 := bstep (se 1 (by rfl) ⟨1638302, by rfl⟩ : syracuseStep 2184403 = 3276605) B3276605
theorem B3880163 : Blo 1532463 3880163 := bstep (se 1 (by rfl) ⟨2910122, by rfl⟩ : syracuseStep 3880163 = 5820245) B5820245
theorem B2299121 : Blo 1532463 2299121 := bstep (se 2 (by rfl) ⟨862170, by rfl⟩ : syracuseStep 2299121 = 1724341) B1724341
theorem B2299139 : Blo 1532463 2299139 := bstep (se 1 (by rfl) ⟨1724354, by rfl⟩ : syracuseStep 2299139 = 3448709) B3448709
theorem B4912397 : Blo 1532463 4912397 := bstep (se 3 (by rfl) ⟨921074, by rfl⟩ : syracuseStep 4912397 = 1842149) B1842149
theorem B2299169 : Blo 1532463 2299169 := bstep (se 2 (by rfl) ⟨862188, by rfl⟩ : syracuseStep 2299169 = 1724377) B1724377
theorem B2299187 : Blo 1532463 2299187 := bstep (se 1 (by rfl) ⟨1724390, by rfl⟩ : syracuseStep 2299187 = 3448781) B3448781
theorem B1725763 : Blo 1532463 1725763 := bstep (se 1 (by rfl) ⟨1294322, by rfl⟩ : syracuseStep 1725763 = 2588645) B2588645
theorem B9958733 : Blo 1532463 9958733 := bstep (se 3 (by rfl) ⟨1867262, by rfl⟩ : syracuseStep 9958733 = 3734525) B3734525
theorem B2299217 : Blo 1532463 2299217 := bstep (se 2 (by rfl) ⟨862206, by rfl⟩ : syracuseStep 2299217 = 1724413) B1724413
theorem B2299235 : Blo 1532463 2299235 := bstep (se 1 (by rfl) ⟨1724426, by rfl⟩ : syracuseStep 2299235 = 3448853) B3448853
theorem B2299265 : Blo 1532463 2299265 := bstep (se 2 (by rfl) ⟨862224, by rfl⟩ : syracuseStep 2299265 = 1724449) B1724449
theorem B2299283 : Blo 1532463 2299283 := bstep (se 1 (by rfl) ⟨1724462, by rfl⟩ : syracuseStep 2299283 = 3448925) B3448925
theorem B7763363 : Blo 1532463 7763363 := bstep (se 1 (by rfl) ⟨5822522, by rfl⟩ : syracuseStep 7763363 = 11645045) B11645045
theorem B2299313 : Blo 1532463 2299313 := bstep (se 2 (by rfl) ⟨862242, by rfl⟩ : syracuseStep 2299313 = 1724485) B1724485
theorem B2299331 : Blo 1532463 2299331 := bstep (se 1 (by rfl) ⟨1724498, by rfl⟩ : syracuseStep 2299331 = 3448997) B3448997
theorem B5821901 : Blo 1532463 5821901 := bstep (se 3 (by rfl) ⟨1091606, by rfl⟩ : syracuseStep 5821901 = 2183213) B2183213
theorem B1725907 : Blo 1532463 1725907 := bstep (se 1 (by rfl) ⟨1294430, by rfl⟩ : syracuseStep 1725907 = 2588861) B2588861
theorem B2299361 : Blo 1532463 2299361 := bstep (se 2 (by rfl) ⟨862260, by rfl⟩ : syracuseStep 2299361 = 1724521) B1724521
theorem B5174765 : Blo 1532463 5174765 := bstep (se 3 (by rfl) ⟨970268, by rfl⟩ : syracuseStep 5174765 = 1940537) B1940537
theorem B2299379 : Blo 1532463 2299379 := bstep (se 1 (by rfl) ⟨1724534, by rfl⟩ : syracuseStep 2299379 = 3449069) B3449069
theorem B2299409 : Blo 1532463 2299409 := bstep (se 2 (by rfl) ⟨862278, by rfl⟩ : syracuseStep 2299409 = 1724557) B1724557
theorem B2299427 : Blo 1532463 2299427 := bstep (se 1 (by rfl) ⟨1724570, by rfl⟩ : syracuseStep 2299427 = 3449141) B3449141
theorem B5174819 : Blo 1532463 5174819 := bstep (se 1 (by rfl) ⟨3881114, by rfl⟩ : syracuseStep 5174819 = 7762229) B7762229
theorem B2586161 : Blo 1532463 2586161 := bstep (se 2 (by rfl) ⟨969810, by rfl⟩ : syracuseStep 2586161 = 1939621) B1939621
theorem B2299457 : Blo 1532463 2299457 := bstep (se 2 (by rfl) ⟨862296, by rfl⟩ : syracuseStep 2299457 = 1724593) B1724593
theorem B2299475 : Blo 1532463 2299475 := bstep (se 1 (by rfl) ⟨1724606, by rfl⟩ : syracuseStep 2299475 = 3449213) B3449213
theorem B14939747 : Blo 1532463 14939747 := bstep (se 1 (by rfl) ⟨11204810, by rfl⟩ : syracuseStep 14939747 = 22409621) B22409621
theorem B1726051 : Blo 1532463 1726051 := bstep (se 1 (by rfl) ⟨1294538, by rfl⟩ : syracuseStep 1726051 = 2589077) B2589077
theorem B2299505 : Blo 1532463 2299505 := bstep (se 2 (by rfl) ⟨862314, by rfl⟩ : syracuseStep 2299505 = 1724629) B1724629
theorem B2299523 : Blo 1532463 2299523 := bstep (se 1 (by rfl) ⟨1724642, by rfl⟩ : syracuseStep 2299523 = 3449285) B3449285
theorem B3683971 : Blo 1532463 3683971 := bstep (se 1 (by rfl) ⟨2762978, by rfl⟩ : syracuseStep 3683971 = 5525957) B5525957
theorem B2299553 : Blo 1532463 2299553 := bstep (se 2 (by rfl) ⟨862332, by rfl⟩ : syracuseStep 2299553 = 1724665) B1724665
theorem B2586289 : Blo 1532463 2586289 := bstep (se 2 (by rfl) ⟨969858, by rfl⟩ : syracuseStep 2586289 = 1939717) B1939717
theorem B2299571 : Blo 1532463 2299571 := bstep (se 1 (by rfl) ⟨1724678, by rfl⟩ : syracuseStep 2299571 = 3449357) B3449357
theorem B3274435 : Blo 1532463 3274435 := bstep (se 1 (by rfl) ⟨2455826, by rfl⟩ : syracuseStep 3274435 = 4911653) B4911653
theorem B31495877 : Blo 1532463 31495877 := bstep (se 4 (by rfl) ⟨2952738, by rfl⟩ : syracuseStep 31495877 = 5905477) B5905477
theorem B2299601 : Blo 1532463 2299601 := bstep (se 2 (by rfl) ⟨862350, by rfl⟩ : syracuseStep 2299601 = 1724701) B1724701
theorem B2586323 : Blo 1532463 2586323 := bstep (se 1 (by rfl) ⟨1939742, by rfl⟩ : syracuseStep 2586323 = 3879485) B3879485
theorem B2299619 : Blo 1532463 2299619 := bstep (se 1 (by rfl) ⟨1724714, by rfl⟩ : syracuseStep 2299619 = 3449429) B3449429
theorem B1726195 : Blo 1532463 1726195 := bstep (se 1 (by rfl) ⟨1294646, by rfl⟩ : syracuseStep 1726195 = 2589293) B2589293
theorem B2299649 : Blo 1532463 2299649 := bstep (se 2 (by rfl) ⟨862368, by rfl⟩ : syracuseStep 2299649 = 1724737) B1724737
theorem B2299667 : Blo 1532463 2299667 := bstep (se 1 (by rfl) ⟨1724750, by rfl⟩ : syracuseStep 2299667 = 3449501) B3449501
theorem B2299697 : Blo 1532463 2299697 := bstep (se 2 (by rfl) ⟨862386, by rfl⟩ : syracuseStep 2299697 = 1724773) B1724773
theorem B5175089 : Blo 1532463 5175089 := bstep (se 2 (by rfl) ⟨1940658, by rfl⟩ : syracuseStep 5175089 = 3881317) B3881317
theorem B16570165 : Blo 1532463 16570165 := bstep (se 5 (by rfl) ⟨776726, by rfl⟩ : syracuseStep 16570165 = 1553453) B1553453
theorem B2299715 : Blo 1532463 2299715 := bstep (se 1 (by rfl) ⟨1724786, by rfl⟩ : syracuseStep 2299715 = 3449573) B3449573
theorem B4364113 : Blo 1532463 4364113 := bstep (se 2 (by rfl) ⟨1636542, by rfl⟩ : syracuseStep 4364113 = 3273085) B3273085
theorem B2586451 : Blo 1532463 2586451 := bstep (se 1 (by rfl) ⟨1939838, by rfl⟩ : syracuseStep 2586451 = 3879677) B3879677
theorem B2299745 : Blo 1532463 2299745 := bstep (se 2 (by rfl) ⟨862404, by rfl⟩ : syracuseStep 2299745 = 1724809) B1724809
theorem B2299763 : Blo 1532463 2299763 := bstep (se 1 (by rfl) ⟨1724822, by rfl⟩ : syracuseStep 2299763 = 3449645) B3449645
theorem B2299793 : Blo 1532463 2299793 := bstep (se 2 (by rfl) ⟨862422, by rfl⟩ : syracuseStep 2299793 = 1724845) B1724845
theorem B2332577 : Blo 1532463 2332577 := bstep (se 2 (by rfl) ⟨874716, by rfl⟩ : syracuseStep 2332577 = 1749433) B1749433
theorem B2299811 : Blo 1532463 2299811 := bstep (se 1 (by rfl) ⟨1724858, by rfl⟩ : syracuseStep 2299811 = 3449717) B3449717
theorem B2299841 : Blo 1532463 2299841 := bstep (se 2 (by rfl) ⟨862440, by rfl⟩ : syracuseStep 2299841 = 1724881) B1724881
theorem B2299859 : Blo 1532463 2299859 := bstep (se 1 (by rfl) ⟨1724894, by rfl⟩ : syracuseStep 2299859 = 3449789) B3449789
theorem B2586593 : Blo 1532463 2586593 := bstep (se 2 (by rfl) ⟨969972, by rfl⟩ : syracuseStep 2586593 = 1939945) B1939945
theorem B4364273 : Blo 1532463 4364273 := bstep (se 2 (by rfl) ⟨1636602, by rfl⟩ : syracuseStep 4364273 = 3273205) B3273205
theorem B2299889 : Blo 1532463 2299889 := bstep (se 2 (by rfl) ⟨862458, by rfl⟩ : syracuseStep 2299889 = 1724917) B1724917
theorem B2299907 : Blo 1532463 2299907 := bstep (se 1 (by rfl) ⟨1724930, by rfl⟩ : syracuseStep 2299907 = 3449861) B3449861
theorem B2332675 : Blo 1532463 2332675 := bstep (se 1 (by rfl) ⟨1749506, by rfl⟩ : syracuseStep 2332675 = 3499013) B3499013
theorem B11646989 : Blo 1532463 11646989 := bstep (se 3 (by rfl) ⟨2183810, by rfl⟩ : syracuseStep 11646989 = 4367621) B4367621
theorem B2455571 : Blo 1532463 2455571 := bstep (se 1 (by rfl) ⟨1841678, by rfl⟩ : syracuseStep 2455571 = 3683357) B3683357
theorem B2299937 : Blo 1532463 2299937 := bstep (se 2 (by rfl) ⟨862476, by rfl⟩ : syracuseStep 2299937 = 1724953) B1724953
theorem B2299955 : Blo 1532463 2299955 := bstep (se 1 (by rfl) ⟨1724966, by rfl⟩ : syracuseStep 2299955 = 3449933) B3449933
theorem B2299985 : Blo 1532463 2299985 := bstep (se 2 (by rfl) ⟨862494, by rfl⟩ : syracuseStep 2299985 = 1724989) B1724989
theorem B2586721 : Blo 1532463 2586721 := bstep (se 2 (by rfl) ⟨970020, by rfl⟩ : syracuseStep 2586721 = 1940041) B1940041
theorem B1939555 : Blo 1532463 1939555 := bstep (se 1 (by rfl) ⟨1454666, by rfl⟩ : syracuseStep 1939555 = 2909333) B2909333
theorem B4364387 : Blo 1532463 4364387 := bstep (se 1 (by rfl) ⟨3273290, by rfl⟩ : syracuseStep 4364387 = 6546581) B6546581
theorem B14735459 : Blo 1532463 14735459 := bstep (se 1 (by rfl) ⟨11051594, by rfl⟩ : syracuseStep 14735459 = 22103189) B22103189
theorem B2300003 : Blo 1532463 2300003 := bstep (se 1 (by rfl) ⟨1725002, by rfl⟩ : syracuseStep 2300003 = 3450005) B3450005
theorem B2300033 : Blo 1532463 2300033 := bstep (se 2 (by rfl) ⟨862512, by rfl⟩ : syracuseStep 2300033 = 1725025) B1725025
theorem B2586755 : Blo 1532463 2586755 := bstep (se 1 (by rfl) ⟨1940066, by rfl⟩ : syracuseStep 2586755 = 3880133) B3880133
theorem B4913293 : Blo 1532463 4913293 := bstep (se 3 (by rfl) ⟨921242, by rfl⟩ : syracuseStep 4913293 = 1842485) B1842485
theorem B3881105 : Blo 1532463 3881105 := bstep (se 2 (by rfl) ⟨1455414, by rfl⟩ : syracuseStep 3881105 = 2910829) B2910829
theorem B2300051 : Blo 1532463 2300051 := bstep (se 1 (by rfl) ⟨1725038, by rfl⟩ : syracuseStep 2300051 = 3450077) B3450077
theorem B2300081 : Blo 1532463 2300081 := bstep (se 2 (by rfl) ⟨862530, by rfl⟩ : syracuseStep 2300081 = 1725061) B1725061
theorem B3881155 : Blo 1532463 3881155 := bstep (se 1 (by rfl) ⟨2910866, by rfl⟩ : syracuseStep 3881155 = 5821733) B5821733
theorem B2300099 : Blo 1532463 2300099 := bstep (se 1 (by rfl) ⟨1725074, by rfl⟩ : syracuseStep 2300099 = 3450149) B3450149
theorem B7764173 : Blo 1532463 7764173 := bstep (se 3 (by rfl) ⟨1455782, by rfl⟩ : syracuseStep 7764173 = 2911565) B2911565
theorem B2300129 : Blo 1532463 2300129 := bstep (se 2 (by rfl) ⟨862548, by rfl⟩ : syracuseStep 2300129 = 1725097) B1725097
theorem B5822705 : Blo 1532463 5822705 := bstep (se 2 (by rfl) ⟨2183514, by rfl⟩ : syracuseStep 5822705 = 4367029) B4367029
theorem B1841395 : Blo 1532463 1841395 := bstep (se 1 (by rfl) ⟨1381046, by rfl⟩ : syracuseStep 1841395 = 2762093) B2762093
theorem B2300147 : Blo 1532463 2300147 := bstep (se 1 (by rfl) ⟨1725110, by rfl⟩ : syracuseStep 2300147 = 3450221) B3450221
theorem B2586883 : Blo 1532463 2586883 := bstep (se 1 (by rfl) ⟨1940162, by rfl⟩ : syracuseStep 2586883 = 3880325) B3880325
theorem B2300177 : Blo 1532463 2300177 := bstep (se 2 (by rfl) ⟨862566, by rfl⟩ : syracuseStep 2300177 = 1725133) B1725133
theorem B2300195 : Blo 1532463 2300195 := bstep (se 1 (by rfl) ⟨1725146, by rfl⟩ : syracuseStep 2300195 = 3450293) B3450293
theorem B2455859 : Blo 1532463 2455859 := bstep (se 1 (by rfl) ⟨1841894, by rfl⟩ : syracuseStep 2455859 = 3683789) B3683789
theorem B2300225 : Blo 1532463 2300225 := bstep (se 2 (by rfl) ⟨862584, by rfl⟩ : syracuseStep 2300225 = 1725169) B1725169
theorem B5175629 : Blo 1532463 5175629 := bstep (se 3 (by rfl) ⟨970430, by rfl⟩ : syracuseStep 5175629 = 1940861) B1940861
theorem B3881297 : Blo 1532463 3881297 := bstep (se 2 (by rfl) ⟨1455486, by rfl⟩ : syracuseStep 3881297 = 2910973) B2910973
theorem B2300243 : Blo 1532463 2300243 := bstep (se 1 (by rfl) ⟨1725182, by rfl⟩ : syracuseStep 2300243 = 3450365) B3450365
theorem B2300273 : Blo 1532463 2300273 := bstep (se 2 (by rfl) ⟨862602, by rfl⟩ : syracuseStep 2300273 = 1725205) B1725205
theorem B2300291 : Blo 1532463 2300291 := bstep (se 1 (by rfl) ⟨1725218, by rfl⟩ : syracuseStep 2300291 = 3450437) B3450437
theorem B5175683 : Blo 1532463 5175683 := bstep (se 1 (by rfl) ⟨3881762, by rfl⟩ : syracuseStep 5175683 = 7763525) B7763525
theorem B2587025 : Blo 1532463 2587025 := bstep (se 2 (by rfl) ⟨970134, by rfl⟩ : syracuseStep 2587025 = 1940269) B1940269
theorem B2300321 : Blo 1532463 2300321 := bstep (se 2 (by rfl) ⟨862620, by rfl⟩ : syracuseStep 2300321 = 1725241) B1725241
theorem B2300339 : Blo 1532463 2300339 := bstep (se 1 (by rfl) ⟨1725254, by rfl⟩ : syracuseStep 2300339 = 3450509) B3450509
theorem B2300369 : Blo 1532463 2300369 := bstep (se 2 (by rfl) ⟨862638, by rfl⟩ : syracuseStep 2300369 = 1725277) B1725277
theorem B39287267 : Blo 1532463 39287267 := bstep (se 1 (by rfl) ⟨29465450, by rfl⟩ : syracuseStep 39287267 = 58930901) B58930901
theorem B2300387 : Blo 1532463 2300387 := bstep (se 1 (by rfl) ⟨1725290, by rfl⟩ : syracuseStep 2300387 = 3450581) B3450581
theorem B2300417 : Blo 1532463 2300417 := bstep (se 2 (by rfl) ⟨862656, by rfl⟩ : syracuseStep 2300417 = 1725313) B1725313
theorem B1636867 : Blo 1532463 1636867 := bstep (se 1 (by rfl) ⟨1227650, by rfl⟩ : syracuseStep 1636867 = 2455301) B2455301
theorem B2587153 : Blo 1532463 2587153 := bstep (se 2 (by rfl) ⟨970182, by rfl⟩ : syracuseStep 2587153 = 1940365) B1940365
theorem B2300435 : Blo 1532463 2300435 := bstep (se 1 (by rfl) ⟨1725326, by rfl⟩ : syracuseStep 2300435 = 3450653) B3450653
theorem B2300465 : Blo 1532463 2300465 := bstep (se 2 (by rfl) ⟨862674, by rfl⟩ : syracuseStep 2300465 = 1725349) B1725349
theorem B2587187 : Blo 1532463 2587187 := bstep (se 1 (by rfl) ⟨1940390, by rfl⟩ : syracuseStep 2587187 = 3880781) B3880781
theorem B2300483 : Blo 1532463 2300483 := bstep (se 1 (by rfl) ⟨1725362, by rfl⟩ : syracuseStep 2300483 = 3450725) B3450725
theorem B1940051 : Blo 1532463 1940051 := bstep (se 1 (by rfl) ⟨1455038, by rfl⟩ : syracuseStep 1940051 = 2910077) B2910077
theorem B2300513 : Blo 1532463 2300513 := bstep (se 2 (by rfl) ⟨862692, by rfl⟩ : syracuseStep 2300513 = 1725385) B1725385
theorem B1841779 : Blo 1532463 1841779 := bstep (se 1 (by rfl) ⟨1381334, by rfl⟩ : syracuseStep 1841779 = 2762669) B2762669
theorem B2300531 : Blo 1532463 2300531 := bstep (se 1 (by rfl) ⟨1725398, by rfl⟩ : syracuseStep 2300531 = 3450797) B3450797
theorem B5175953 : Blo 1532463 5175953 := bstep (se 2 (by rfl) ⟨1940982, by rfl⟩ : syracuseStep 5175953 = 3881965) B3881965
theorem B2300561 : Blo 1532463 2300561 := bstep (se 2 (by rfl) ⟨862710, by rfl⟩ : syracuseStep 2300561 = 1725421) B1725421
theorem B2300579 : Blo 1532463 2300579 := bstep (se 1 (by rfl) ⟨1725434, by rfl⟩ : syracuseStep 2300579 = 3450869) B3450869
theorem B2587315 : Blo 1532463 2587315 := bstep (se 1 (by rfl) ⟨1940486, by rfl⟩ : syracuseStep 2587315 = 3880973) B3880973
theorem B2300609 : Blo 1532463 2300609 := bstep (se 2 (by rfl) ⟨862728, by rfl⟩ : syracuseStep 2300609 = 1725457) B1725457
theorem B2300627 : Blo 1532463 2300627 := bstep (se 1 (by rfl) ⟨1725470, by rfl⟩ : syracuseStep 2300627 = 3450941) B3450941
theorem B2300657 : Blo 1532463 2300657 := bstep (se 2 (by rfl) ⟨862746, by rfl⟩ : syracuseStep 2300657 = 1725493) B1725493
theorem B2300675 : Blo 1532463 2300675 := bstep (se 1 (by rfl) ⟨1725506, by rfl⟩ : syracuseStep 2300675 = 3451013) B3451013
theorem B2300705 : Blo 1532463 2300705 := bstep (se 2 (by rfl) ⟨862764, by rfl⟩ : syracuseStep 2300705 = 1725529) B1725529
theorem B2300723 : Blo 1532463 2300723 := bstep (se 1 (by rfl) ⟨1725542, by rfl⟩ : syracuseStep 2300723 = 3451085) B3451085
theorem B2587457 : Blo 1532463 2587457 := bstep (se 2 (by rfl) ⟨970296, by rfl⟩ : syracuseStep 2587457 = 1940593) B1940593
theorem B9820997 : Blo 1532463 9820997 := bstep (se 4 (by rfl) ⟨920718, by rfl⟩ : syracuseStep 9820997 = 1841437) B1841437
theorem B2300753 : Blo 1532463 2300753 := bstep (se 2 (by rfl) ⟨862782, by rfl⟩ : syracuseStep 2300753 = 1725565) B1725565
theorem B2300771 : Blo 1532463 2300771 := bstep (se 1 (by rfl) ⟨1725578, by rfl⟩ : syracuseStep 2300771 = 3451157) B3451157
theorem B2300801 : Blo 1532463 2300801 := bstep (se 2 (by rfl) ⟨862800, by rfl⟩ : syracuseStep 2300801 = 1725601) B1725601
theorem B4144013 : Blo 1532463 4144013 := bstep (se 3 (by rfl) ⟨777002, by rfl⟩ : syracuseStep 4144013 = 1554005) B1554005
theorem B5823373 : Blo 1532463 5823373 := bstep (se 3 (by rfl) ⟨1091882, by rfl⟩ : syracuseStep 5823373 = 2183765) B2183765
theorem B2300819 : Blo 1532463 2300819 := bstep (se 1 (by rfl) ⟨1725614, by rfl⟩ : syracuseStep 2300819 = 3451229) B3451229
theorem B3685297 : Blo 1532463 3685297 := bstep (se 2 (by rfl) ⟨1381986, by rfl⟩ : syracuseStep 3685297 = 2763973) B2763973
theorem B2300849 : Blo 1532463 2300849 := bstep (se 2 (by rfl) ⟨862818, by rfl⟩ : syracuseStep 2300849 = 1725637) B1725637
theorem B2587585 : Blo 1532463 2587585 := bstep (se 2 (by rfl) ⟨970344, by rfl⟩ : syracuseStep 2587585 = 1940689) B1940689
theorem B2300867 : Blo 1532463 2300867 := bstep (se 1 (by rfl) ⟨1725650, by rfl⟩ : syracuseStep 2300867 = 3451301) B3451301
theorem B12598213 : Blo 1532463 12598213 := bstep (se 4 (by rfl) ⟨1181082, by rfl⟩ : syracuseStep 12598213 = 2362165) B2362165
theorem B31562693 : Blo 1532463 31562693 := bstep (se 4 (by rfl) ⟨2959002, by rfl⟩ : syracuseStep 31562693 = 5918005) B5918005
theorem B8731597 : Blo 1532463 8731597 := bstep (se 3 (by rfl) ⟨1637174, by rfl⟩ : syracuseStep 8731597 = 3274349) B3274349
theorem B2300897 : Blo 1532463 2300897 := bstep (se 2 (by rfl) ⟨862836, by rfl⟩ : syracuseStep 2300897 = 1725673) B1725673
theorem B2587619 : Blo 1532463 2587619 := bstep (se 1 (by rfl) ⟨1940714, by rfl⟩ : syracuseStep 2587619 = 3881429) B3881429
theorem B2300915 : Blo 1532463 2300915 := bstep (se 1 (by rfl) ⟨1725686, by rfl⟩ : syracuseStep 2300915 = 3451373) B3451373
theorem B4914179 : Blo 1532463 4914179 := bstep (se 1 (by rfl) ⟨3685634, by rfl⟩ : syracuseStep 4914179 = 7371269) B7371269
theorem B5979149 : Blo 1532463 5979149 := bstep (se 3 (by rfl) ⟨1121090, by rfl⟩ : syracuseStep 5979149 = 2242181) B2242181
theorem B2300945 : Blo 1532463 2300945 := bstep (se 2 (by rfl) ⟨862854, by rfl⟩ : syracuseStep 2300945 = 1725709) B1725709
theorem B2300963 : Blo 1532463 2300963 := bstep (se 1 (by rfl) ⟨1725722, by rfl⟩ : syracuseStep 2300963 = 3451445) B3451445
theorem B2300993 : Blo 1532463 2300993 := bstep (se 2 (by rfl) ⟨862872, by rfl⟩ : syracuseStep 2300993 = 1725745) B1725745
theorem B4365389 : Blo 1532463 4365389 := bstep (se 3 (by rfl) ⟨818510, by rfl⟩ : syracuseStep 4365389 = 1637021) B1637021
theorem B2456659 : Blo 1532463 2456659 := bstep (se 1 (by rfl) ⟨1842494, by rfl⟩ : syracuseStep 2456659 = 3684989) B3684989
theorem B2301011 : Blo 1532463 2301011 := bstep (se 1 (by rfl) ⟨1725758, by rfl⟩ : syracuseStep 2301011 = 3451517) B3451517
theorem B2587747 : Blo 1532463 2587747 := bstep (se 1 (by rfl) ⟨1940810, by rfl⟩ : syracuseStep 2587747 = 3881621) B3881621
theorem B83942513 : Blo 1532463 83942513 := bstep (se 2 (by rfl) ⟨31478442, by rfl⟩ : syracuseStep 83942513 = 62956885) B62956885
theorem B1637491 : Blo 1532463 1637491 := bstep (se 1 (by rfl) ⟨1228118, by rfl⟩ : syracuseStep 1637491 = 2456237) B2456237
theorem B2301041 : Blo 1532463 2301041 := bstep (se 2 (by rfl) ⟨862890, by rfl⟩ : syracuseStep 2301041 = 1725781) B1725781
theorem B2301059 : Blo 1532463 2301059 := bstep (se 1 (by rfl) ⟨1725794, by rfl⟩ : syracuseStep 2301059 = 3451589) B3451589
theorem B3275921 : Blo 1532463 3275921 := bstep (se 2 (by rfl) ⟨1228470, by rfl⟩ : syracuseStep 3275921 = 2456941) B2456941
theorem B2301089 : Blo 1532463 2301089 := bstep (se 2 (by rfl) ⟨862908, by rfl⟩ : syracuseStep 2301089 = 1725817) B1725817
theorem B3275939 : Blo 1532463 3275939 := bstep (se 1 (by rfl) ⟨2456954, by rfl⟩ : syracuseStep 3275939 = 4913909) B4913909
theorem B5176493 : Blo 1532463 5176493 := bstep (se 3 (by rfl) ⟨970592, by rfl⟩ : syracuseStep 5176493 = 1941185) B1941185
theorem B2301107 : Blo 1532463 2301107 := bstep (se 1 (by rfl) ⟨1725830, by rfl⟩ : syracuseStep 2301107 = 3451661) B3451661
theorem B2071747 : Blo 1532463 2071747 := bstep (se 1 (by rfl) ⟨1553810, by rfl⟩ : syracuseStep 2071747 = 3107621) B3107621
theorem B2301137 : Blo 1532463 2301137 := bstep (se 2 (by rfl) ⟨862926, by rfl⟩ : syracuseStep 2301137 = 1725853) B1725853
theorem B2456801 : Blo 1532463 2456801 := bstep (se 2 (by rfl) ⟨921300, by rfl⟩ : syracuseStep 2456801 = 1842601) B1842601
theorem B5176547 : Blo 1532463 5176547 := bstep (se 1 (by rfl) ⟨3882410, by rfl⟩ : syracuseStep 5176547 = 7764821) B7764821
theorem B2301155 : Blo 1532463 2301155 := bstep (se 1 (by rfl) ⟨1725866, by rfl⟩ : syracuseStep 2301155 = 3451733) B3451733
theorem B2587889 : Blo 1532463 2587889 := bstep (se 2 (by rfl) ⟨970458, by rfl⟩ : syracuseStep 2587889 = 1940917) B1940917
theorem B2456833 : Blo 1532463 2456833 := bstep (se 2 (by rfl) ⟨921312, by rfl⟩ : syracuseStep 2456833 = 1842625) B1842625
theorem B2301185 : Blo 1532463 2301185 := bstep (se 2 (by rfl) ⟨862944, by rfl⟩ : syracuseStep 2301185 = 1725889) B1725889
theorem B4365571 : Blo 1532463 4365571 := bstep (se 1 (by rfl) ⟨3274178, by rfl⟩ : syracuseStep 4365571 = 6548357) B6548357
theorem B16579853 : Blo 1532463 16579853 := bstep (se 3 (by rfl) ⟨3108722, by rfl⟩ : syracuseStep 16579853 = 6217445) B6217445
theorem B1940755 : Blo 1532463 1940755 := bstep (se 1 (by rfl) ⟨1455566, by rfl⟩ : syracuseStep 1940755 = 2911133) B2911133
theorem B2301203 : Blo 1532463 2301203 := bstep (se 1 (by rfl) ⟨1725902, by rfl⟩ : syracuseStep 2301203 = 3451805) B3451805
theorem B3882289 : Blo 1532463 3882289 := bstep (se 2 (by rfl) ⟨1455858, by rfl⟩ : syracuseStep 3882289 = 2911717) B2911717
theorem B2301233 : Blo 1532463 2301233 := bstep (se 2 (by rfl) ⟨862962, by rfl⟩ : syracuseStep 2301233 = 1725925) B1725925
theorem B2301251 : Blo 1532463 2301251 := bstep (se 1 (by rfl) ⟨1725938, by rfl⟩ : syracuseStep 2301251 = 3451877) B3451877
theorem B2301281 : Blo 1532463 2301281 := bstep (se 2 (by rfl) ⟨862980, by rfl⟩ : syracuseStep 2301281 = 1725961) B1725961
theorem B2588017 : Blo 1532463 2588017 := bstep (se 2 (by rfl) ⟨970506, by rfl⟩ : syracuseStep 2588017 = 1941013) B1941013
theorem B1940851 : Blo 1532463 1940851 := bstep (se 1 (by rfl) ⟨1455638, by rfl⟩ : syracuseStep 1940851 = 2911277) B2911277
theorem B2301299 : Blo 1532463 2301299 := bstep (se 1 (by rfl) ⟨1725974, by rfl⟩ : syracuseStep 2301299 = 3451949) B3451949
theorem B9330061 : Blo 1532463 9330061 := bstep (se 3 (by rfl) ⟨1749386, by rfl⟩ : syracuseStep 9330061 = 3498773) B3498773
theorem B2301329 : Blo 1532463 2301329 := bstep (se 2 (by rfl) ⟨862998, by rfl⟩ : syracuseStep 2301329 = 1725997) B1725997
theorem B2588051 : Blo 1532463 2588051 := bstep (se 1 (by rfl) ⟨1941038, by rfl⟩ : syracuseStep 2588051 = 3882077) B3882077
theorem B4365731 : Blo 1532463 4365731 := bstep (se 1 (by rfl) ⟨3274298, by rfl⟩ : syracuseStep 4365731 = 6548597) B6548597
theorem B2301347 : Blo 1532463 2301347 := bstep (se 1 (by rfl) ⟨1726010, by rfl⟩ : syracuseStep 2301347 = 3452021) B3452021
theorem B3448241 : Blo 1532463 3448241 := bstep (se 2 (by rfl) ⟨1293090, by rfl⟩ : syracuseStep 3448241 = 2586181) B2586181
theorem B2301377 : Blo 1532463 2301377 := bstep (se 2 (by rfl) ⟨863016, by rfl⟩ : syracuseStep 2301377 = 1726033) B1726033
theorem B3448259 : Blo 1532463 3448259 := bstep (se 1 (by rfl) ⟨2586194, by rfl⟩ : syracuseStep 3448259 = 5172389) B5172389
theorem B2301395 : Blo 1532463 2301395 := bstep (se 1 (by rfl) ⟨1726046, by rfl⟩ : syracuseStep 2301395 = 3452093) B3452093
theorem B5176817 : Blo 1532463 5176817 := bstep (se 2 (by rfl) ⟨1941306, by rfl⟩ : syracuseStep 5176817 = 3882613) B3882613
theorem B2301425 : Blo 1532463 2301425 := bstep (se 2 (by rfl) ⟨863034, by rfl⟩ : syracuseStep 2301425 = 1726069) B1726069
theorem B2301443 : Blo 1532463 2301443 := bstep (se 1 (by rfl) ⟨1726082, by rfl⟩ : syracuseStep 2301443 = 3452165) B3452165
theorem B2588179 : Blo 1532463 2588179 := bstep (se 1 (by rfl) ⟨1941134, by rfl⟩ : syracuseStep 2588179 = 3882269) B3882269
theorem B2301473 : Blo 1532463 2301473 := bstep (se 2 (by rfl) ⟨863052, by rfl⟩ : syracuseStep 2301473 = 1726105) B1726105
theorem B9960995 : Blo 1532463 9960995 := bstep (se 1 (by rfl) ⟨7470746, by rfl⟩ : syracuseStep 9960995 = 14941493) B14941493
theorem B2301491 : Blo 1532463 2301491 := bstep (se 1 (by rfl) ⟨1726118, by rfl⟩ : syracuseStep 2301491 = 3452237) B3452237
theorem B3882563 : Blo 1532463 3882563 := bstep (se 1 (by rfl) ⟨2911922, by rfl⟩ : syracuseStep 3882563 = 5823845) B5823845
theorem B2301521 : Blo 1532463 2301521 := bstep (se 2 (by rfl) ⟨863070, by rfl⟩ : syracuseStep 2301521 = 1726141) B1726141
theorem B2301539 : Blo 1532463 2301539 := bstep (se 1 (by rfl) ⟨1726154, by rfl⟩ : syracuseStep 2301539 = 3452309) B3452309
theorem B2301569 : Blo 1532463 2301569 := bstep (se 2 (by rfl) ⟨863088, by rfl⟩ : syracuseStep 2301569 = 1726177) B1726177
theorem B2301587 : Blo 1532463 2301587 := bstep (se 1 (by rfl) ⟨1726190, by rfl⟩ : syracuseStep 2301587 = 3452381) B3452381
theorem B2588321 : Blo 1532463 2588321 := bstep (se 2 (by rfl) ⟨970620, by rfl⟩ : syracuseStep 2588321 = 1941241) B1941241
theorem B5824163 : Blo 1532463 5824163 := bstep (se 1 (by rfl) ⟨4368122, by rfl⟩ : syracuseStep 5824163 = 8736245) B8736245
theorem B2301617 : Blo 1532463 2301617 := bstep (se 2 (by rfl) ⟨863106, by rfl⟩ : syracuseStep 2301617 = 1726213) B1726213
theorem B2301635 : Blo 1532463 2301635 := bstep (se 1 (by rfl) ⟨1726226, by rfl⟩ : syracuseStep 2301635 = 3452453) B3452453
theorem B3448529 : Blo 1532463 3448529 := bstep (se 2 (by rfl) ⟨1293198, by rfl⟩ : syracuseStep 3448529 = 2586397) B2586397
theorem B2301665 : Blo 1532463 2301665 := bstep (se 2 (by rfl) ⟨863124, by rfl⟩ : syracuseStep 2301665 = 1726249) B1726249
theorem B12426979 : Blo 1532463 12426979 := bstep (se 1 (by rfl) ⟨9320234, by rfl⟩ : syracuseStep 12426979 = 18640469) B18640469
theorem B3448547 : Blo 1532463 3448547 := bstep (se 1 (by rfl) ⟨2586410, by rfl⟩ : syracuseStep 3448547 = 5172821) B5172821
theorem B2301683 : Blo 1532463 2301683 := bstep (se 1 (by rfl) ⟨1726262, by rfl⟩ : syracuseStep 2301683 = 3452525) B3452525
theorem B3882755 : Blo 1532463 3882755 := bstep (se 1 (by rfl) ⟨2912066, by rfl⟩ : syracuseStep 3882755 = 5824133) B5824133
theorem B2588449 : Blo 1532463 2588449 := bstep (se 2 (by rfl) ⟨970668, by rfl⟩ : syracuseStep 2588449 = 1941337) B1941337
theorem B2588483 : Blo 1532463 2588483 := bstep (se 1 (by rfl) ⟨1941362, by rfl⟩ : syracuseStep 2588483 = 3882725) B3882725
theorem B10100557 : Blo 1532463 10100557 := bstep (se 3 (by rfl) ⟨1893854, by rfl⟩ : syracuseStep 10100557 = 3787709) B3787709
theorem B1941347 : Blo 1532463 1941347 := bstep (se 1 (by rfl) ⟨1456010, by rfl⟩ : syracuseStep 1941347 = 2912021) B2912021
theorem B3686257 : Blo 1532463 3686257 := bstep (se 2 (by rfl) ⟨1382346, by rfl⟩ : syracuseStep 3686257 = 2764693) B2764693
theorem B4423601 : Blo 1532463 4423601 := bstep (se 2 (by rfl) ⟨1658850, by rfl⟩ : syracuseStep 4423601 = 3317701) B3317701
theorem B2588611 : Blo 1532463 2588611 := bstep (se 1 (by rfl) ⟨1941458, by rfl⟩ : syracuseStep 2588611 = 3882917) B3882917
theorem B3448817 : Blo 1532463 3448817 := bstep (se 2 (by rfl) ⟨1293306, by rfl⟩ : syracuseStep 3448817 = 2586613) B2586613
theorem B5529617 : Blo 1532463 5529617 := bstep (se 2 (by rfl) ⟨2073606, by rfl⟩ : syracuseStep 5529617 = 4147213) B4147213
theorem B22413347 : Blo 1532463 22413347 := bstep (se 1 (by rfl) ⟨16810010, by rfl⟩ : syracuseStep 22413347 = 33620021) B33620021
theorem B3448907 : Blo 1532463 3448907 := bstep (se 1 (by rfl) ⟨2586680, by rfl⟩ : syracuseStep 3448907 = 5173361) B5173361
theorem B14729309 : Blo 1532463 14729309 := bstep (se 3 (by rfl) ⟨2761745, by rfl⟩ : syracuseStep 14729309 = 5523491) B5523491
theorem B3448961 : Blo 1532463 3448961 := bstep (se 2 (by rfl) ⟨1293360, by rfl⟩ : syracuseStep 3448961 = 2586721) B2586721
theorem B4546763 : Blo 1532463 4546763 := bstep (se 1 (by rfl) ⟨3410072, by rfl⟩ : syracuseStep 4546763 = 6820145) B6820145
theorem B3883211 : Blo 1532463 3883211 := bstep (se 1 (by rfl) ⟨2912408, by rfl⟩ : syracuseStep 3883211 = 5824817) B5824817
theorem B3989783 : Blo 1532463 3989783 := bstep (se 1 (by rfl) ⟨2992337, by rfl⟩ : syracuseStep 3989783 = 5984675) B5984675
theorem B2801945 : Blo 1532463 2801945 := bstep (se 2 (by rfl) ⟨1050729, by rfl⟩ : syracuseStep 2801945 = 2101459) B2101459
theorem B2621783 : Blo 1532463 2621783 := bstep (se 1 (by rfl) ⟨1966337, by rfl⟩ : syracuseStep 2621783 = 3932675) B3932675
theorem B3449177 : Blo 1532463 3449177 := bstep (se 2 (by rfl) ⟨1293441, by rfl⟩ : syracuseStep 3449177 = 2586883) B2586883
theorem B6554029 : Blo 1532463 6554029 := bstep (se 3 (by rfl) ⟨1228880, by rfl⟩ : syracuseStep 6554029 = 2457761) B2457761
theorem B14729651 : Blo 1532463 14729651 := bstep (se 1 (by rfl) ⟨11047238, by rfl⟩ : syracuseStep 14729651 = 22094477) B22094477
theorem B3449267 : Blo 1532463 3449267 := bstep (se 1 (by rfl) ⟨2586950, by rfl⟩ : syracuseStep 3449267 = 5173901) B5173901
theorem B2589131 : Blo 1532463 2589131 := bstep (se 1 (by rfl) ⟨1941848, by rfl⟩ : syracuseStep 2589131 = 3883697) B3883697
theorem B3449303 : Blo 1532463 3449303 := bstep (se 1 (by rfl) ⟨2586977, by rfl⟩ : syracuseStep 3449303 = 5173955) B5173955
theorem B12599813 : Blo 1532463 12599813 := bstep (se 4 (by rfl) ⟨1181232, by rfl⟩ : syracuseStep 12599813 = 2362465) B2362465
theorem B6218291 : Blo 1532463 6218291 := bstep (se 1 (by rfl) ⟨4663718, by rfl⟩ : syracuseStep 6218291 = 9327437) B9327437
theorem B1532471 : Blo 1532463 1532471 := bstep (se 1 (by rfl) ⟨1149353, by rfl⟩ : syracuseStep 1532471 = 2298707) B2298707
theorem B3883585 : Blo 1532463 3883585 := bstep (se 2 (by rfl) ⟨1456344, by rfl⟩ : syracuseStep 3883585 = 2912689) B2912689
theorem B1532491 : Blo 1532463 1532491 := bstep (se 1 (by rfl) ⟨1149368, by rfl⟩ : syracuseStep 1532491 = 2298737) B2298737
theorem B6636107 : Blo 1532463 6636107 := bstep (se 1 (by rfl) ⟨4977080, by rfl⟩ : syracuseStep 6636107 = 9954161) B9954161
theorem B7766603 : Blo 1532463 7766603 := bstep (se 1 (by rfl) ⟨5824952, by rfl⟩ : syracuseStep 7766603 = 11649905) B11649905
theorem B2589259 : Blo 1532463 2589259 := bstep (se 1 (by rfl) ⟨1941944, by rfl⟩ : syracuseStep 2589259 = 3883889) B3883889
theorem B1532503 : Blo 1532463 1532503 := bstep (se 1 (by rfl) ⟨1149377, by rfl⟩ : syracuseStep 1532503 = 2298755) B2298755
theorem B1532523 : Blo 1532463 1532523 := bstep (se 1 (by rfl) ⟨1149392, by rfl⟩ : syracuseStep 1532523 = 2298785) B2298785
theorem B1532535 : Blo 1532463 1532535 := bstep (se 1 (by rfl) ⟨1149401, by rfl⟩ : syracuseStep 1532535 = 2298803) B2298803
theorem B1532555 : Blo 1532463 1532555 := bstep (se 1 (by rfl) ⟨1149416, by rfl⟩ : syracuseStep 1532555 = 2298833) B2298833
theorem B3449483 : Blo 1532463 3449483 := bstep (se 1 (by rfl) ⟨2587112, by rfl⟩ : syracuseStep 3449483 = 5174225) B5174225
theorem B1532567 : Blo 1532463 1532567 := bstep (se 1 (by rfl) ⟨1149425, by rfl⟩ : syracuseStep 1532567 = 2298851) B2298851
theorem B1532587 : Blo 1532463 1532587 := bstep (se 1 (by rfl) ⟨1149440, by rfl⟩ : syracuseStep 1532587 = 2298881) B2298881
theorem B1532599 : Blo 1532463 1532599 := bstep (se 1 (by rfl) ⟨1149449, by rfl⟩ : syracuseStep 1532599 = 2298899) B2298899
theorem B3449537 : Blo 1532463 3449537 := bstep (se 2 (by rfl) ⟨1293576, by rfl⟩ : syracuseStep 3449537 = 2587153) B2587153
theorem B1532619 : Blo 1532463 1532619 := bstep (se 1 (by rfl) ⟨1149464, by rfl⟩ : syracuseStep 1532619 = 2298929) B2298929
theorem B5178059 : Blo 1532463 5178059 := bstep (se 1 (by rfl) ⟨3883544, by rfl⟩ : syracuseStep 5178059 = 7767089) B7767089
theorem B1532631 : Blo 1532463 1532631 := bstep (se 1 (by rfl) ⟨1149473, by rfl⟩ : syracuseStep 1532631 = 2298947) B2298947
theorem B2589401 : Blo 1532463 2589401 := bstep (se 2 (by rfl) ⟨971025, by rfl⟩ : syracuseStep 2589401 = 1942051) B1942051
theorem B1532651 : Blo 1532463 1532651 := bstep (se 1 (by rfl) ⟨1149488, by rfl⟩ : syracuseStep 1532651 = 2298977) B2298977
theorem B1532663 : Blo 1532463 1532663 := bstep (se 1 (by rfl) ⟨1149497, by rfl⟩ : syracuseStep 1532663 = 2298995) B2298995
theorem B6554371 : Blo 1532463 6554371 := bstep (se 1 (by rfl) ⟨4915778, by rfl⟩ : syracuseStep 6554371 = 9831557) B9831557
theorem B1532683 : Blo 1532463 1532683 := bstep (se 1 (by rfl) ⟨1149512, by rfl⟩ : syracuseStep 1532683 = 2299025) B2299025
theorem B1532695 : Blo 1532463 1532695 := bstep (se 1 (by rfl) ⟨1149521, by rfl⟩ : syracuseStep 1532695 = 2299043) B2299043
theorem B5825303 : Blo 1532463 5825303 := bstep (se 1 (by rfl) ⟨4368977, by rfl⟩ : syracuseStep 5825303 = 8737955) B8737955
theorem B1532715 : Blo 1532463 1532715 := bstep (se 1 (by rfl) ⟨1149536, by rfl⟩ : syracuseStep 1532715 = 2299073) B2299073
theorem B4367155 : Blo 1532463 4367155 := bstep (se 1 (by rfl) ⟨3275366, by rfl⟩ : syracuseStep 4367155 = 6550733) B6550733
theorem B1532727 : Blo 1532463 1532727 := bstep (se 1 (by rfl) ⟨1149545, by rfl⟩ : syracuseStep 1532727 = 2299091) B2299091
theorem B1532747 : Blo 1532463 1532747 := bstep (se 1 (by rfl) ⟨1149560, by rfl⟩ : syracuseStep 1532747 = 2299121) B2299121
theorem B1532759 : Blo 1532463 1532759 := bstep (se 1 (by rfl) ⟨1149569, by rfl⟩ : syracuseStep 1532759 = 2299139) B2299139
theorem B1532779 : Blo 1532463 1532779 := bstep (se 1 (by rfl) ⟨1149584, by rfl⟩ : syracuseStep 1532779 = 2299169) B2299169
theorem B1532791 : Blo 1532463 1532791 := bstep (se 1 (by rfl) ⟨1149593, by rfl⟩ : syracuseStep 1532791 = 2299187) B2299187
theorem B1532811 : Blo 1532463 1532811 := bstep (se 1 (by rfl) ⟨1149608, by rfl⟩ : syracuseStep 1532811 = 2299217) B2299217
theorem B1532823 : Blo 1532463 1532823 := bstep (se 1 (by rfl) ⟨1149617, by rfl⟩ : syracuseStep 1532823 = 2299235) B2299235
theorem B3449753 : Blo 1532463 3449753 := bstep (se 2 (by rfl) ⟨1293657, by rfl⟩ : syracuseStep 3449753 = 2587315) B2587315
theorem B1532843 : Blo 1532463 1532843 := bstep (se 1 (by rfl) ⟨1149632, by rfl⟩ : syracuseStep 1532843 = 2299265) B2299265
theorem B1532855 : Blo 1532463 1532855 := bstep (se 1 (by rfl) ⟨1149641, by rfl⟩ : syracuseStep 1532855 = 2299283) B2299283
theorem B1532875 : Blo 1532463 1532875 := bstep (se 1 (by rfl) ⟨1149656, by rfl⟩ : syracuseStep 1532875 = 2299313) B2299313
theorem B1532887 : Blo 1532463 1532887 := bstep (se 1 (by rfl) ⟨1149665, by rfl⟩ : syracuseStep 1532887 = 2299331) B2299331
theorem B5178329 : Blo 1532463 5178329 := bstep (se 2 (by rfl) ⟨1941873, by rfl⟩ : syracuseStep 5178329 = 3883747) B3883747
theorem B1532907 : Blo 1532463 1532907 := bstep (se 1 (by rfl) ⟨1149680, by rfl⟩ : syracuseStep 1532907 = 2299361) B2299361
theorem B3449843 : Blo 1532463 3449843 := bstep (se 1 (by rfl) ⟨2587382, by rfl⟩ : syracuseStep 3449843 = 5174765) B5174765
theorem B1532919 : Blo 1532463 1532919 := bstep (se 1 (by rfl) ⟨1149689, by rfl⟩ : syracuseStep 1532919 = 2299379) B2299379
theorem B1532939 : Blo 1532463 1532939 := bstep (se 1 (by rfl) ⟨1149704, by rfl⟩ : syracuseStep 1532939 = 2299409) B2299409
theorem B1532951 : Blo 1532463 1532951 := bstep (se 1 (by rfl) ⟨1149713, by rfl⟩ : syracuseStep 1532951 = 2299427) B2299427
theorem B3449879 : Blo 1532463 3449879 := bstep (se 1 (by rfl) ⟨2587409, by rfl⟩ : syracuseStep 3449879 = 5174819) B5174819
theorem B1532971 : Blo 1532463 1532971 := bstep (se 1 (by rfl) ⟨1149728, by rfl⟩ : syracuseStep 1532971 = 2299457) B2299457
theorem B1532983 : Blo 1532463 1532983 := bstep (se 1 (by rfl) ⟨1149737, by rfl⟩ : syracuseStep 1532983 = 2299475) B2299475
theorem B1533003 : Blo 1532463 1533003 := bstep (se 1 (by rfl) ⟨1149752, by rfl⟩ : syracuseStep 1533003 = 2299505) B2299505
theorem B1533015 : Blo 1532463 1533015 := bstep (se 1 (by rfl) ⟨1149761, by rfl⟩ : syracuseStep 1533015 = 2299523) B2299523
theorem B1533035 : Blo 1532463 1533035 := bstep (se 1 (by rfl) ⟨1149776, by rfl⟩ : syracuseStep 1533035 = 2299553) B2299553
theorem B1533047 : Blo 1532463 1533047 := bstep (se 1 (by rfl) ⟨1149785, by rfl⟩ : syracuseStep 1533047 = 2299571) B2299571
theorem B20997251 : Blo 1532463 20997251 := bstep (se 1 (by rfl) ⟨15747938, by rfl⟩ : syracuseStep 20997251 = 31495877) B31495877
theorem B1533067 : Blo 1532463 1533067 := bstep (se 1 (by rfl) ⟨1149800, by rfl⟩ : syracuseStep 1533067 = 2299601) B2299601
theorem B1533079 : Blo 1532463 1533079 := bstep (se 1 (by rfl) ⟨1149809, by rfl⟩ : syracuseStep 1533079 = 2299619) B2299619
theorem B1533099 : Blo 1532463 1533099 := bstep (se 1 (by rfl) ⟨1149824, by rfl⟩ : syracuseStep 1533099 = 2299649) B2299649
theorem B1533111 : Blo 1532463 1533111 := bstep (se 1 (by rfl) ⟨1149833, by rfl⟩ : syracuseStep 1533111 = 2299667) B2299667
theorem B1533131 : Blo 1532463 1533131 := bstep (se 1 (by rfl) ⟨1149848, by rfl⟩ : syracuseStep 1533131 = 2299697) B2299697
theorem B3450059 : Blo 1532463 3450059 := bstep (se 1 (by rfl) ⟨2587544, by rfl⟩ : syracuseStep 3450059 = 5175089) B5175089
theorem B1533143 : Blo 1532463 1533143 := bstep (se 1 (by rfl) ⟨1149857, by rfl⟩ : syracuseStep 1533143 = 2299715) B2299715
theorem B1533163 : Blo 1532463 1533163 := bstep (se 1 (by rfl) ⟨1149872, by rfl⟩ : syracuseStep 1533163 = 2299745) B2299745
theorem B1533175 : Blo 1532463 1533175 := bstep (se 1 (by rfl) ⟨1149881, by rfl⟩ : syracuseStep 1533175 = 2299763) B2299763
theorem B3450113 : Blo 1532463 3450113 := bstep (se 2 (by rfl) ⟨1293792, by rfl⟩ : syracuseStep 3450113 = 2587585) B2587585
theorem B1533195 : Blo 1532463 1533195 := bstep (se 1 (by rfl) ⟨1149896, by rfl⟩ : syracuseStep 1533195 = 2299793) B2299793
theorem B11642129 : Blo 1532463 11642129 := bstep (se 2 (by rfl) ⟨4365798, by rfl⟩ : syracuseStep 11642129 = 8731597) B8731597
theorem B1533207 : Blo 1532463 1533207 := bstep (se 1 (by rfl) ⟨1149905, by rfl⟩ : syracuseStep 1533207 = 2299811) B2299811
theorem B1533227 : Blo 1532463 1533227 := bstep (se 1 (by rfl) ⟨1149920, by rfl⟩ : syracuseStep 1533227 = 2299841) B2299841
theorem B1533239 : Blo 1532463 1533239 := bstep (se 1 (by rfl) ⟨1149929, by rfl⟩ : syracuseStep 1533239 = 2299859) B2299859
theorem B2909515 : Blo 1532463 2909515 := bstep (se 1 (by rfl) ⟨2182136, by rfl⟩ : syracuseStep 2909515 = 4364273) B4364273
theorem B1533259 : Blo 1532463 1533259 := bstep (se 1 (by rfl) ⟨1149944, by rfl⟩ : syracuseStep 1533259 = 2299889) B2299889
theorem B1533271 : Blo 1532463 1533271 := bstep (se 1 (by rfl) ⟨1149953, by rfl⟩ : syracuseStep 1533271 = 2299907) B2299907
theorem B1533291 : Blo 1532463 1533291 := bstep (se 1 (by rfl) ⟨1149968, by rfl⟩ : syracuseStep 1533291 = 2299937) B2299937
theorem B1533303 : Blo 1532463 1533303 := bstep (se 1 (by rfl) ⟨1149977, by rfl⟩ : syracuseStep 1533303 = 2299955) B2299955
theorem B1533323 : Blo 1532463 1533323 := bstep (se 1 (by rfl) ⟨1149992, by rfl⟩ : syracuseStep 1533323 = 2299985) B2299985
theorem B2909591 : Blo 1532463 2909591 := bstep (se 1 (by rfl) ⟨2182193, by rfl⟩ : syracuseStep 2909591 = 4364387) B4364387
theorem B9823639 : Blo 1532463 9823639 := bstep (se 1 (by rfl) ⟨7367729, by rfl⟩ : syracuseStep 9823639 = 14735459) B14735459
theorem B1533335 : Blo 1532463 1533335 := bstep (se 1 (by rfl) ⟨1150001, by rfl⟩ : syracuseStep 1533335 = 2300003) B2300003
theorem B1533355 : Blo 1532463 1533355 := bstep (se 1 (by rfl) ⟨1150016, by rfl⟩ : syracuseStep 1533355 = 2300033) B2300033
theorem B1533367 : Blo 1532463 1533367 := bstep (se 1 (by rfl) ⟨1150025, by rfl⟩ : syracuseStep 1533367 = 2300051) B2300051
theorem B1533387 : Blo 1532463 1533387 := bstep (se 1 (by rfl) ⟨1150040, by rfl⟩ : syracuseStep 1533387 = 2300081) B2300081
theorem B1533399 : Blo 1532463 1533399 := bstep (se 1 (by rfl) ⟨1150049, by rfl⟩ : syracuseStep 1533399 = 2300099) B2300099
theorem B3450329 : Blo 1532463 3450329 := bstep (se 2 (by rfl) ⟨1293873, by rfl⟩ : syracuseStep 3450329 = 2587747) B2587747
theorem B1533419 : Blo 1532463 1533419 := bstep (se 1 (by rfl) ⟨1150064, by rfl⟩ : syracuseStep 1533419 = 2300129) B2300129
theorem B1533431 : Blo 1532463 1533431 := bstep (se 1 (by rfl) ⟨1150073, by rfl⟩ : syracuseStep 1533431 = 2300147) B2300147
theorem B1533451 : Blo 1532463 1533451 := bstep (se 1 (by rfl) ⟨1150088, by rfl⟩ : syracuseStep 1533451 = 2300177) B2300177
theorem B1533463 : Blo 1532463 1533463 := bstep (se 1 (by rfl) ⟨1150097, by rfl⟩ : syracuseStep 1533463 = 2300195) B2300195
theorem B1533483 : Blo 1532463 1533483 := bstep (se 1 (by rfl) ⟨1150112, by rfl⟩ : syracuseStep 1533483 = 2300225) B2300225
theorem B3450419 : Blo 1532463 3450419 := bstep (se 1 (by rfl) ⟨2587814, by rfl⟩ : syracuseStep 3450419 = 5175629) B5175629
theorem B1533495 : Blo 1532463 1533495 := bstep (se 1 (by rfl) ⟨1150121, by rfl⟩ : syracuseStep 1533495 = 2300243) B2300243
theorem B1533515 : Blo 1532463 1533515 := bstep (se 1 (by rfl) ⟨1150136, by rfl⟩ : syracuseStep 1533515 = 2300273) B2300273
theorem B1533527 : Blo 1532463 1533527 := bstep (se 1 (by rfl) ⟨1150145, by rfl⟩ : syracuseStep 1533527 = 2300291) B2300291
theorem B3450455 : Blo 1532463 3450455 := bstep (se 1 (by rfl) ⟨2587841, by rfl⟩ : syracuseStep 3450455 = 5175683) B5175683
theorem B1533547 : Blo 1532463 1533547 := bstep (se 1 (by rfl) ⟨1150160, by rfl⟩ : syracuseStep 1533547 = 2300321) B2300321
theorem B1533559 : Blo 1532463 1533559 := bstep (se 1 (by rfl) ⟨1150169, by rfl⟩ : syracuseStep 1533559 = 2300339) B2300339
theorem B1533579 : Blo 1532463 1533579 := bstep (se 1 (by rfl) ⟨1150184, by rfl⟩ : syracuseStep 1533579 = 2300369) B2300369
theorem B26191511 : Blo 1532463 26191511 := bstep (se 1 (by rfl) ⟨19643633, by rfl⟩ : syracuseStep 26191511 = 39287267) B39287267
theorem B1533591 : Blo 1532463 1533591 := bstep (se 1 (by rfl) ⟨1150193, by rfl⟩ : syracuseStep 1533591 = 2300387) B2300387
theorem B1533611 : Blo 1532463 1533611 := bstep (se 1 (by rfl) ⟨1150208, by rfl⟩ : syracuseStep 1533611 = 2300417) B2300417
theorem B1533623 : Blo 1532463 1533623 := bstep (se 1 (by rfl) ⟨1150217, by rfl⟩ : syracuseStep 1533623 = 2300435) B2300435
theorem B1533643 : Blo 1532463 1533643 := bstep (se 1 (by rfl) ⟨1150232, by rfl⟩ : syracuseStep 1533643 = 2300465) B2300465
theorem B1533655 : Blo 1532463 1533655 := bstep (se 1 (by rfl) ⟨1150241, by rfl⟩ : syracuseStep 1533655 = 2300483) B2300483
theorem B1533675 : Blo 1532463 1533675 := bstep (se 1 (by rfl) ⟨1150256, by rfl⟩ : syracuseStep 1533675 = 2300513) B2300513
theorem B1533687 : Blo 1532463 1533687 := bstep (se 1 (by rfl) ⟨1150265, by rfl⟩ : syracuseStep 1533687 = 2300531) B2300531
theorem B3450635 : Blo 1532463 3450635 := bstep (se 1 (by rfl) ⟨2587976, by rfl⟩ : syracuseStep 3450635 = 5175953) B5175953
theorem B1533707 : Blo 1532463 1533707 := bstep (se 1 (by rfl) ⟨1150280, by rfl⟩ : syracuseStep 1533707 = 2300561) B2300561
theorem B1533719 : Blo 1532463 1533719 := bstep (se 1 (by rfl) ⟨1150289, by rfl⟩ : syracuseStep 1533719 = 2300579) B2300579
theorem B1533739 : Blo 1532463 1533739 := bstep (se 1 (by rfl) ⟨1150304, by rfl⟩ : syracuseStep 1533739 = 2300609) B2300609
theorem B4982579 : Blo 1532463 4982579 := bstep (se 1 (by rfl) ⟨3736934, by rfl⟩ : syracuseStep 4982579 = 7473869) B7473869
theorem B1533751 : Blo 1532463 1533751 := bstep (se 1 (by rfl) ⟨1150313, by rfl⟩ : syracuseStep 1533751 = 2300627) B2300627
theorem B3450689 : Blo 1532463 3450689 := bstep (se 2 (by rfl) ⟨1294008, by rfl⟩ : syracuseStep 3450689 = 2588017) B2588017
theorem B1533771 : Blo 1532463 1533771 := bstep (se 1 (by rfl) ⟨1150328, by rfl⟩ : syracuseStep 1533771 = 2300657) B2300657
theorem B1533783 : Blo 1532463 1533783 := bstep (se 1 (by rfl) ⟨1150337, by rfl⟩ : syracuseStep 1533783 = 2300675) B2300675
theorem B1533803 : Blo 1532463 1533803 := bstep (se 1 (by rfl) ⟨1150352, by rfl⟩ : syracuseStep 1533803 = 2300705) B2300705
theorem B1533815 : Blo 1532463 1533815 := bstep (se 1 (by rfl) ⟨1150361, by rfl⟩ : syracuseStep 1533815 = 2300723) B2300723
theorem B6547331 : Blo 1532463 6547331 := bstep (se 1 (by rfl) ⟨4910498, by rfl⟩ : syracuseStep 6547331 = 9820997) B9820997
theorem B1533835 : Blo 1532463 1533835 := bstep (se 1 (by rfl) ⟨1150376, by rfl⟩ : syracuseStep 1533835 = 2300753) B2300753
theorem B1533847 : Blo 1532463 1533847 := bstep (se 1 (by rfl) ⟨1150385, by rfl⟩ : syracuseStep 1533847 = 2300771) B2300771
theorem B1533867 : Blo 1532463 1533867 := bstep (se 1 (by rfl) ⟨1150400, by rfl⟩ : syracuseStep 1533867 = 2300801) B2300801
theorem B2762675 : Blo 1532463 2762675 := bstep (se 1 (by rfl) ⟨2072006, by rfl⟩ : syracuseStep 2762675 = 4144013) B4144013
theorem B1533879 : Blo 1532463 1533879 := bstep (se 1 (by rfl) ⟨1150409, by rfl⟩ : syracuseStep 1533879 = 2300819) B2300819
theorem B1533899 : Blo 1532463 1533899 := bstep (se 1 (by rfl) ⟨1150424, by rfl⟩ : syracuseStep 1533899 = 2300849) B2300849
theorem B1533911 : Blo 1532463 1533911 := bstep (se 1 (by rfl) ⟨1150433, by rfl⟩ : syracuseStep 1533911 = 2300867) B2300867
theorem B1533931 : Blo 1532463 1533931 := bstep (se 1 (by rfl) ⟨1150448, by rfl⟩ : syracuseStep 1533931 = 2300897) B2300897
theorem B1533943 : Blo 1532463 1533943 := bstep (se 1 (by rfl) ⟨1150457, by rfl⟩ : syracuseStep 1533943 = 2300915) B2300915
theorem B1533963 : Blo 1532463 1533963 := bstep (se 1 (by rfl) ⟨1150472, by rfl⟩ : syracuseStep 1533963 = 2300945) B2300945
theorem B1533975 : Blo 1532463 1533975 := bstep (se 1 (by rfl) ⟨1150481, by rfl⟩ : syracuseStep 1533975 = 2300963) B2300963
theorem B3450905 : Blo 1532463 3450905 := bstep (se 2 (by rfl) ⟨1294089, by rfl⟩ : syracuseStep 3450905 = 2588179) B2588179
theorem B1533995 : Blo 1532463 1533995 := bstep (se 1 (by rfl) ⟨1150496, by rfl⟩ : syracuseStep 1533995 = 2300993) B2300993
theorem B2910259 : Blo 1532463 2910259 := bstep (se 1 (by rfl) ⟨2182694, by rfl⟩ : syracuseStep 2910259 = 4365389) B4365389
theorem B1534007 : Blo 1532463 1534007 := bstep (se 1 (by rfl) ⟨1150505, by rfl⟩ : syracuseStep 1534007 = 2301011) B2301011
theorem B55961675 : Blo 1532463 55961675 := bstep (se 1 (by rfl) ⟨41971256, by rfl⟩ : syracuseStep 55961675 = 83942513) B83942513
theorem B1534027 : Blo 1532463 1534027 := bstep (se 1 (by rfl) ⟨1150520, by rfl⟩ : syracuseStep 1534027 = 2301041) B2301041
theorem B1534039 : Blo 1532463 1534039 := bstep (se 1 (by rfl) ⟨1150529, by rfl⟩ : syracuseStep 1534039 = 2301059) B2301059
theorem B1534059 : Blo 1532463 1534059 := bstep (se 1 (by rfl) ⟨1150544, by rfl⟩ : syracuseStep 1534059 = 2301089) B2301089
theorem B3450995 : Blo 1532463 3450995 := bstep (se 1 (by rfl) ⟨2588246, by rfl⟩ : syracuseStep 3450995 = 5176493) B5176493
theorem B1534071 : Blo 1532463 1534071 := bstep (se 1 (by rfl) ⟨1150553, by rfl⟩ : syracuseStep 1534071 = 2301107) B2301107
theorem B1534091 : Blo 1532463 1534091 := bstep (se 1 (by rfl) ⟨1150568, by rfl⟩ : syracuseStep 1534091 = 2301137) B2301137
theorem B3451031 : Blo 1532463 3451031 := bstep (se 1 (by rfl) ⟨2588273, by rfl⟩ : syracuseStep 3451031 = 5176547) B5176547
theorem B1534103 : Blo 1532463 1534103 := bstep (se 1 (by rfl) ⟨1150577, by rfl⟩ : syracuseStep 1534103 = 2301155) B2301155
theorem B1534123 : Blo 1532463 1534123 := bstep (se 1 (by rfl) ⟨1150592, by rfl⟩ : syracuseStep 1534123 = 2301185) B2301185
theorem B11053235 : Blo 1532463 11053235 := bstep (se 1 (by rfl) ⟨8289926, by rfl⟩ : syracuseStep 11053235 = 16579853) B16579853
theorem B1534135 : Blo 1532463 1534135 := bstep (se 1 (by rfl) ⟨1150601, by rfl⟩ : syracuseStep 1534135 = 2301203) B2301203
theorem B1534155 : Blo 1532463 1534155 := bstep (se 1 (by rfl) ⟨1150616, by rfl⟩ : syracuseStep 1534155 = 2301233) B2301233
theorem B1534167 : Blo 1532463 1534167 := bstep (se 1 (by rfl) ⟨1150625, by rfl⟩ : syracuseStep 1534167 = 2301251) B2301251
theorem B1534187 : Blo 1532463 1534187 := bstep (se 1 (by rfl) ⟨1150640, by rfl⟩ : syracuseStep 1534187 = 2301281) B2301281
theorem B1534199 : Blo 1532463 1534199 := bstep (se 1 (by rfl) ⟨1150649, by rfl⟩ : syracuseStep 1534199 = 2301299) B2301299
theorem B1534219 : Blo 1532463 1534219 := bstep (se 1 (by rfl) ⟨1150664, by rfl⟩ : syracuseStep 1534219 = 2301329) B2301329
theorem B2910487 : Blo 1532463 2910487 := bstep (se 1 (by rfl) ⟨2182865, by rfl⟩ : syracuseStep 2910487 = 4365731) B4365731
theorem B1534231 : Blo 1532463 1534231 := bstep (se 1 (by rfl) ⟨1150673, by rfl⟩ : syracuseStep 1534231 = 2301347) B2301347
theorem B11651363 : Blo 1532463 11651363 := bstep (se 1 (by rfl) ⟨8738522, by rfl⟩ : syracuseStep 11651363 = 17477045) B17477045
theorem B1534251 : Blo 1532463 1534251 := bstep (se 1 (by rfl) ⟨1150688, by rfl⟩ : syracuseStep 1534251 = 2301377) B2301377
theorem B1534263 : Blo 1532463 1534263 := bstep (se 1 (by rfl) ⟨1150697, by rfl⟩ : syracuseStep 1534263 = 2301395) B2301395
theorem B3451211 : Blo 1532463 3451211 := bstep (se 1 (by rfl) ⟨2588408, by rfl⟩ : syracuseStep 3451211 = 5176817) B5176817
theorem B1534283 : Blo 1532463 1534283 := bstep (se 1 (by rfl) ⟨1150712, by rfl⟩ : syracuseStep 1534283 = 2301425) B2301425
theorem B1534295 : Blo 1532463 1534295 := bstep (se 1 (by rfl) ⟨1150721, by rfl⟩ : syracuseStep 1534295 = 2301443) B2301443
theorem B1534315 : Blo 1532463 1534315 := bstep (se 1 (by rfl) ⟨1150736, by rfl⟩ : syracuseStep 1534315 = 2301473) B2301473
theorem B1534327 : Blo 1532463 1534327 := bstep (se 1 (by rfl) ⟨1150745, by rfl⟩ : syracuseStep 1534327 = 2301491) B2301491
theorem B2910593 : Blo 1532463 2910593 := bstep (se 2 (by rfl) ⟨1091472, by rfl⟩ : syracuseStep 2910593 = 2182945) B2182945
theorem B3451265 : Blo 1532463 3451265 := bstep (se 2 (by rfl) ⟨1294224, by rfl⟩ : syracuseStep 3451265 = 2588449) B2588449
theorem B1534347 : Blo 1532463 1534347 := bstep (se 1 (by rfl) ⟨1150760, by rfl⟩ : syracuseStep 1534347 = 2301521) B2301521
theorem B1534359 : Blo 1532463 1534359 := bstep (se 1 (by rfl) ⟨1150769, by rfl⟩ : syracuseStep 1534359 = 2301539) B2301539
theorem B1534379 : Blo 1532463 1534379 := bstep (se 1 (by rfl) ⟨1150784, by rfl⟩ : syracuseStep 1534379 = 2301569) B2301569
theorem B6220205 : Blo 1532463 6220205 := bstep (se 3 (by rfl) ⟨1166288, by rfl⟩ : syracuseStep 6220205 = 2332577) B2332577
theorem B1534391 : Blo 1532463 1534391 := bstep (se 1 (by rfl) ⟨1150793, by rfl⟩ : syracuseStep 1534391 = 2301587) B2301587
theorem B5818817 : Blo 1532463 5818817 := bstep (se 2 (by rfl) ⟨2182056, by rfl⟩ : syracuseStep 5818817 = 4364113) B4364113
theorem B1534411 : Blo 1532463 1534411 := bstep (se 1 (by rfl) ⟨1150808, by rfl⟩ : syracuseStep 1534411 = 2301617) B2301617
theorem B1534423 : Blo 1532463 1534423 := bstep (se 1 (by rfl) ⟨1150817, by rfl⟩ : syracuseStep 1534423 = 2301635) B2301635
theorem B1534443 : Blo 1532463 1534443 := bstep (se 1 (by rfl) ⟨1150832, by rfl⟩ : syracuseStep 1534443 = 2301665) B2301665
theorem B1534455 : Blo 1532463 1534455 := bstep (se 1 (by rfl) ⟨1150841, by rfl⟩ : syracuseStep 1534455 = 2301683) B2301683
theorem B2910745 : Blo 1532463 2910745 := bstep (se 2 (by rfl) ⟨1091529, by rfl⟩ : syracuseStep 2910745 = 2183059) B2183059
theorem B3451481 : Blo 1532463 3451481 := bstep (se 2 (by rfl) ⟨1294305, by rfl⟩ : syracuseStep 3451481 = 2588611) B2588611
theorem B3787415 : Blo 1532463 3787415 := bstep (se 1 (by rfl) ⟨2840561, by rfl⟩ : syracuseStep 3787415 = 5681123) B5681123
theorem B8293043 : Blo 1532463 8293043 := bstep (se 1 (by rfl) ⟨6219782, by rfl⟩ : syracuseStep 8293043 = 12439565) B12439565
theorem B3451571 : Blo 1532463 3451571 := bstep (se 1 (by rfl) ⟨2588678, by rfl⟩ : syracuseStep 3451571 = 5177357) B5177357
theorem B3451607 : Blo 1532463 3451607 := bstep (se 1 (by rfl) ⟨2588705, by rfl⟩ : syracuseStep 3451607 = 5177411) B5177411
theorem B6220547 : Blo 1532463 6220547 := bstep (se 1 (by rfl) ⟨4665410, by rfl⟩ : syracuseStep 6220547 = 9330821) B9330821
theorem B11209537 : Blo 1532463 11209537 := bstep (se 2 (by rfl) ⟨4203576, by rfl⟩ : syracuseStep 11209537 = 8407153) B8407153
theorem B8293195 : Blo 1532463 8293195 := bstep (se 1 (by rfl) ⟨6219896, by rfl⟩ : syracuseStep 8293195 = 12439793) B12439793
theorem B7760771 : Blo 1532463 7760771 := bstep (se 1 (by rfl) ⟨5820578, by rfl⟩ : syracuseStep 7760771 = 11641157) B11641157
theorem B3451787 : Blo 1532463 3451787 := bstep (se 1 (by rfl) ⟨2588840, by rfl⟩ : syracuseStep 3451787 = 5177681) B5177681
theorem B5172119 : Blo 1532463 5172119 := bstep (se 1 (by rfl) ⟨3879089, by rfl⟩ : syracuseStep 5172119 = 7758179) B7758179
theorem B40381361 : Blo 1532463 40381361 := bstep (se 2 (by rfl) ⟨15143010, by rfl⟩ : syracuseStep 40381361 = 30286021) B30286021
theorem B13093811 : Blo 1532463 13093811 := bstep (se 1 (by rfl) ⟨9820358, by rfl⟩ : syracuseStep 13093811 = 19640717) B19640717
theorem B6302657 : Blo 1532463 6302657 := bstep (se 2 (by rfl) ⟨2363496, by rfl⟩ : syracuseStep 6302657 = 4726993) B4726993
theorem B3451841 : Blo 1532463 3451841 := bstep (se 2 (by rfl) ⟨1294440, by rfl⟩ : syracuseStep 3451841 = 2588881) B2588881
theorem B2952151 : Blo 1532463 2952151 := bstep (se 1 (by rfl) ⟨2214113, by rfl⟩ : syracuseStep 2952151 = 4428227) B4428227
theorem B6999005 : Blo 1532463 6999005 := bstep (se 3 (by rfl) ⟨1312313, by rfl⟩ : syracuseStep 6999005 = 2624627) B2624627
theorem B8735789 : Blo 1532463 8735789 := bstep (se 3 (by rfl) ⟨1637960, by rfl⟩ : syracuseStep 8735789 = 3275921) B3275921
theorem B5819485 : Blo 1532463 5819485 := bstep (se 3 (by rfl) ⟨1091153, by rfl⟩ : syracuseStep 5819485 = 2182307) B2182307
theorem B13102181 : Blo 1532463 13102181 := bstep (se 4 (by rfl) ⟨1228329, by rfl⟩ : syracuseStep 13102181 = 2456659) B2456659
theorem B3452057 : Blo 1532463 3452057 := bstep (se 2 (by rfl) ⟨1294521, by rfl⟩ : syracuseStep 3452057 = 2589043) B2589043
theorem B6991051 : Blo 1532463 6991051 := bstep (se 1 (by rfl) ⟨5243288, by rfl⟩ : syracuseStep 6991051 = 10486577) B10486577
theorem B3452147 : Blo 1532463 3452147 := bstep (se 1 (by rfl) ⟨2589110, by rfl⟩ : syracuseStep 3452147 = 5178221) B5178221
theorem B3452183 : Blo 1532463 3452183 := bstep (se 1 (by rfl) ⟨2589137, by rfl⟩ : syracuseStep 3452183 = 5178275) B5178275
theorem B5172659 : Blo 1532463 5172659 := bstep (se 1 (by rfl) ⟨3879494, by rfl⟩ : syracuseStep 5172659 = 7758989) B7758989
theorem B11808179 : Blo 1532463 11808179 := bstep (se 1 (by rfl) ⟨8856134, by rfl⟩ : syracuseStep 11808179 = 17712269) B17712269
theorem B3452363 : Blo 1532463 3452363 := bstep (se 1 (by rfl) ⟨2589272, by rfl⟩ : syracuseStep 3452363 = 5178545) B5178545
theorem B6548957 : Blo 1532463 6548957 := bstep (se 3 (by rfl) ⟨1227929, by rfl⟩ : syracuseStep 6548957 = 2455859) B2455859
theorem B3452417 : Blo 1532463 3452417 := bstep (se 2 (by rfl) ⟨1294656, by rfl⟩ : syracuseStep 3452417 = 2589313) B2589313
theorem B7368209 : Blo 1532463 7368209 := bstep (se 2 (by rfl) ⟨2763078, by rfl⟩ : syracuseStep 7368209 = 5526157) B5526157
theorem B6639155 : Blo 1532463 6639155 := bstep (se 1 (by rfl) ⟨4979366, by rfl⟩ : syracuseStep 6639155 = 9958733) B9958733
theorem B2764363 : Blo 1532463 2764363 := bstep (se 1 (by rfl) ⟨2073272, by rfl⟩ : syracuseStep 2764363 = 4146545) B4146545
theorem B12430999 : Blo 1532463 12430999 := bstep (se 1 (by rfl) ⟨9323249, by rfl⟩ : syracuseStep 12430999 = 18646499) B18646499
theorem B13987505 : Blo 1532463 13987505 := bstep (se 2 (by rfl) ⟨5245314, by rfl⟩ : syracuseStep 13987505 = 10490629) B10490629
theorem B5172929 : Blo 1532463 5172929 := bstep (se 2 (by rfl) ⟨1939848, by rfl⟩ : syracuseStep 5172929 = 3879697) B3879697
theorem B1724107 : Blo 1532463 1724107 := bstep (se 1 (by rfl) ⟨1293080, by rfl⟩ : syracuseStep 1724107 = 2586161) B2586161
theorem B2912051 : Blo 1532463 2912051 := bstep (se 1 (by rfl) ⟨2184038, by rfl⟩ : syracuseStep 2912051 = 4368077) B4368077
theorem B1724215 : Blo 1532463 1724215 := bstep (se 1 (by rfl) ⟨1293161, by rfl⟩ : syracuseStep 1724215 = 2586323) B2586323
theorem B9826123 : Blo 1532463 9826123 := bstep (se 1 (by rfl) ⟨7369592, by rfl⟩ : syracuseStep 9826123 = 14739185) B14739185
theorem B16797617 : Blo 1532463 16797617 := bstep (se 2 (by rfl) ⟨6299106, by rfl⟩ : syracuseStep 16797617 = 12598213) B12598213
theorem B8728499 : Blo 1532463 8728499 := bstep (se 1 (by rfl) ⟨6546374, by rfl⟩ : syracuseStep 8728499 = 13092749) B13092749
theorem B2912203 : Blo 1532463 2912203 := bstep (se 1 (by rfl) ⟨2184152, by rfl⟩ : syracuseStep 2912203 = 4368305) B4368305
theorem B1724395 : Blo 1532463 1724395 := bstep (se 1 (by rfl) ⟨1293296, by rfl⟩ : syracuseStep 1724395 = 2586593) B2586593
theorem B1724503 : Blo 1532463 1724503 := bstep (se 1 (by rfl) ⟨1293377, by rfl⟩ : syracuseStep 1724503 = 2586755) B2586755
theorem B6549655 : Blo 1532463 6549655 := bstep (se 1 (by rfl) ⟨4912241, by rfl⟩ : syracuseStep 6549655 = 9824483) B9824483
theorem B2183321 : Blo 1532463 2183321 := bstep (se 2 (by rfl) ⟨818745, by rfl⟩ : syracuseStep 2183321 = 1637491) B1637491
theorem B5173469 : Blo 1532463 5173469 := bstep (se 3 (by rfl) ⟨970025, by rfl⟩ : syracuseStep 5173469 = 1940051) B1940051
theorem B1724683 : Blo 1532463 1724683 := bstep (se 1 (by rfl) ⟨1293512, by rfl⟩ : syracuseStep 1724683 = 2587025) B2587025
theorem B3879191 : Blo 1532463 3879191 := bstep (se 1 (by rfl) ⟨2909393, by rfl⟩ : syracuseStep 3879191 = 5818787) B5818787
theorem B2912537 : Blo 1532463 2912537 := bstep (se 2 (by rfl) ⟨1092201, by rfl⟩ : syracuseStep 2912537 = 2184403) B2184403
theorem B5820761 : Blo 1532463 5820761 := bstep (se 2 (by rfl) ⟨2182785, by rfl⟩ : syracuseStep 5820761 = 4365571) B4365571
theorem B1724791 : Blo 1532463 1724791 := bstep (se 1 (by rfl) ⟨1293593, by rfl⟩ : syracuseStep 1724791 = 2587187) B2587187
theorem B12440081 : Blo 1532463 12440081 := bstep (se 2 (by rfl) ⟨4665030, by rfl⟩ : syracuseStep 12440081 = 9330061) B9330061
theorem B1724971 : Blo 1532463 1724971 := bstep (se 1 (by rfl) ⟨1293728, by rfl⟩ : syracuseStep 1724971 = 2587457) B2587457
theorem B21041795 : Blo 1532463 21041795 := bstep (se 1 (by rfl) ⟨15781346, by rfl⟩ : syracuseStep 21041795 = 31562693) B31562693
theorem B1725079 : Blo 1532463 1725079 := bstep (se 1 (by rfl) ⟨1293809, by rfl⟩ : syracuseStep 1725079 = 2587619) B2587619
theorem B3986099 : Blo 1532463 3986099 := bstep (se 1 (by rfl) ⟨2989574, by rfl⟩ : syracuseStep 3986099 = 5979149) B5979149
theorem B2183959 : Blo 1532463 2183959 := bstep (se 1 (by rfl) ⟨1637969, by rfl⟩ : syracuseStep 2183959 = 3275939) B3275939
theorem B3273547 : Blo 1532463 3273547 := bstep (se 1 (by rfl) ⟨2455160, by rfl⟩ : syracuseStep 3273547 = 4910321) B4910321
theorem B1725259 : Blo 1532463 1725259 := bstep (se 1 (by rfl) ⟨1293944, by rfl⟩ : syracuseStep 1725259 = 2587889) B2587889
theorem B2298713 : Blo 1532463 2298713 := bstep (se 2 (by rfl) ⟨862017, by rfl⟩ : syracuseStep 2298713 = 1724035) B1724035
theorem B4911961 : Blo 1532463 4911961 := bstep (se 2 (by rfl) ⟨1841985, by rfl⟩ : syracuseStep 4911961 = 3683971) B3683971
theorem B3879859 : Blo 1532463 3879859 := bstep (se 1 (by rfl) ⟨2909894, by rfl⟩ : syracuseStep 3879859 = 5819789) B5819789
theorem B1725367 : Blo 1532463 1725367 := bstep (se 1 (by rfl) ⟨1294025, by rfl⟩ : syracuseStep 1725367 = 2588051) B2588051
theorem B2298827 : Blo 1532463 2298827 := bstep (se 1 (by rfl) ⟨1724120, by rfl⟩ : syracuseStep 2298827 = 3448241) B3448241
theorem B2298839 : Blo 1532463 2298839 := bstep (se 1 (by rfl) ⟨1724129, by rfl⟩ : syracuseStep 2298839 = 3448259) B3448259
theorem B16569305 : Blo 1532463 16569305 := bstep (se 2 (by rfl) ⟨6213489, by rfl⟩ : syracuseStep 16569305 = 12426979) B12426979
theorem B2298905 : Blo 1532463 2298905 := bstep (se 2 (by rfl) ⟨862089, by rfl⟩ : syracuseStep 2298905 = 1724179) B1724179
theorem B6640663 : Blo 1532463 6640663 := bstep (se 1 (by rfl) ⟨4980497, by rfl⟩ : syracuseStep 6640663 = 9960995) B9960995
theorem B3880001 : Blo 1532463 3880001 := bstep (se 2 (by rfl) ⟨1455000, by rfl⟩ : syracuseStep 3880001 = 2910001) B2910001
theorem B11646017 : Blo 1532463 11646017 := bstep (se 2 (by rfl) ⟨4367256, by rfl⟩ : syracuseStep 11646017 = 8734513) B8734513
theorem B1725547 : Blo 1532463 1725547 := bstep (se 1 (by rfl) ⟨1294160, by rfl⟩ : syracuseStep 1725547 = 2588321) B2588321
theorem B2299019 : Blo 1532463 2299019 := bstep (se 1 (by rfl) ⟨1724264, by rfl⟩ : syracuseStep 2299019 = 3448529) B3448529
theorem B2299031 : Blo 1532463 2299031 := bstep (se 1 (by rfl) ⟨1724273, by rfl⟩ : syracuseStep 2299031 = 3448547) B3448547
theorem B1725655 : Blo 1532463 1725655 := bstep (se 1 (by rfl) ⟨1294241, by rfl⟩ : syracuseStep 1725655 = 2588483) B2588483
theorem B2299097 : Blo 1532463 2299097 := bstep (se 2 (by rfl) ⟨862161, by rfl⟩ : syracuseStep 2299097 = 1724323) B1724323
theorem B12432685 : Blo 1532463 12432685 := bstep (se 3 (by rfl) ⟨2331128, by rfl⟩ : syracuseStep 12432685 = 4662257) B4662257
theorem B2299211 : Blo 1532463 2299211 := bstep (se 1 (by rfl) ⟨1724408, by rfl⟩ : syracuseStep 2299211 = 3448817) B3448817
theorem B5174603 : Blo 1532463 5174603 := bstep (se 1 (by rfl) ⟨3880952, by rfl⟩ : syracuseStep 5174603 = 7761905) B7761905
theorem B2299223 : Blo 1532463 2299223 := bstep (se 1 (by rfl) ⟨1724417, by rfl⟩ : syracuseStep 2299223 = 3448835) B3448835
theorem B3110233 : Blo 1532463 3110233 := bstep (se 2 (by rfl) ⟨1166337, by rfl⟩ : syracuseStep 3110233 = 2332675) B2332675
theorem B8729957 : Blo 1532463 8729957 := bstep (se 4 (by rfl) ⟨818433, by rfl⟩ : syracuseStep 8729957 = 1636867) B1636867
theorem B1725835 : Blo 1532463 1725835 := bstep (se 1 (by rfl) ⟨1294376, by rfl⟩ : syracuseStep 1725835 = 2588753) B2588753
theorem B2299289 : Blo 1532463 2299289 := bstep (se 2 (by rfl) ⟨862233, by rfl⟩ : syracuseStep 2299289 = 1724467) B1724467
theorem B6641099 : Blo 1532463 6641099 := bstep (se 1 (by rfl) ⟨4980824, by rfl⟩ : syracuseStep 6641099 = 9961649) B9961649
theorem B2586073 : Blo 1532463 2586073 := bstep (se 2 (by rfl) ⟨969777, by rfl⟩ : syracuseStep 2586073 = 1939555) B1939555
theorem B14177753 : Blo 1532463 14177753 := bstep (se 2 (by rfl) ⟨5316657, by rfl⟩ : syracuseStep 14177753 = 10633315) B10633315
theorem B1725943 : Blo 1532463 1725943 := bstep (se 1 (by rfl) ⟨1294457, by rfl⟩ : syracuseStep 1725943 = 2588915) B2588915
theorem B2299403 : Blo 1532463 2299403 := bstep (se 1 (by rfl) ⟨1724552, by rfl⟩ : syracuseStep 2299403 = 3449105) B3449105
theorem B6551057 : Blo 1532463 6551057 := bstep (se 2 (by rfl) ⟨2456646, by rfl⟩ : syracuseStep 6551057 = 4913293) B4913293
theorem B2299415 : Blo 1532463 2299415 := bstep (se 1 (by rfl) ⟨1724561, by rfl⟩ : syracuseStep 2299415 = 3449123) B3449123
theorem B6067777 : Blo 1532463 6067777 := bstep (se 2 (by rfl) ⟨2275416, by rfl⟩ : syracuseStep 6067777 = 4550833) B4550833
theorem B2184779 : Blo 1532463 2184779 := bstep (se 1 (by rfl) ⟨1638584, by rfl⟩ : syracuseStep 2184779 = 3277169) B3277169
theorem B2299481 : Blo 1532463 2299481 := bstep (se 2 (by rfl) ⟨862305, by rfl⟩ : syracuseStep 2299481 = 1724611) B1724611
theorem B5174873 : Blo 1532463 5174873 := bstep (se 2 (by rfl) ⟨1940577, by rfl⟩ : syracuseStep 5174873 = 3881155) B3881155
theorem B37303901 : Blo 1532463 37303901 := bstep (se 3 (by rfl) ⟨6994481, by rfl⟩ : syracuseStep 37303901 = 13988963) B13988963
theorem B2455193 : Blo 1532463 2455193 := bstep (se 2 (by rfl) ⟨920697, by rfl⟩ : syracuseStep 2455193 = 1841395) B1841395
theorem B1726123 : Blo 1532463 1726123 := bstep (se 1 (by rfl) ⟨1294592, by rfl⟩ : syracuseStep 1726123 = 2589185) B2589185
theorem B2299595 : Blo 1532463 2299595 := bstep (se 1 (by rfl) ⟨1724696, by rfl⟩ : syracuseStep 2299595 = 3449393) B3449393
theorem B2299607 : Blo 1532463 2299607 := bstep (se 1 (by rfl) ⟨1724705, by rfl⟩ : syracuseStep 2299607 = 3449411) B3449411
theorem B1726231 : Blo 1532463 1726231 := bstep (se 1 (by rfl) ⟨1294673, by rfl⟩ : syracuseStep 1726231 = 2589347) B2589347
theorem B2299673 : Blo 1532463 2299673 := bstep (se 2 (by rfl) ⟨862377, by rfl⟩ : syracuseStep 2299673 = 1724755) B1724755
theorem B8730413 : Blo 1532463 8730413 := bstep (se 3 (by rfl) ⟨1636952, by rfl⟩ : syracuseStep 8730413 = 3273905) B3273905
theorem B2299787 : Blo 1532463 2299787 := bstep (se 1 (by rfl) ⟨1724840, by rfl⟩ : syracuseStep 2299787 = 3449681) B3449681
theorem B2299799 : Blo 1532463 2299799 := bstep (se 1 (by rfl) ⟨1724849, by rfl⟩ : syracuseStep 2299799 = 3449699) B3449699
theorem B5822387 : Blo 1532463 5822387 := bstep (se 1 (by rfl) ⟨4366790, by rfl⟩ : syracuseStep 5822387 = 8733581) B8733581
theorem B5822401 : Blo 1532463 5822401 := bstep (se 2 (by rfl) ⟨2183400, by rfl⟩ : syracuseStep 5822401 = 4366801) B4366801
theorem B2299865 : Blo 1532463 2299865 := bstep (se 2 (by rfl) ⟨862449, by rfl⟩ : syracuseStep 2299865 = 1724899) B1724899
theorem B2586647 : Blo 1532463 2586647 := bstep (se 1 (by rfl) ⟨1939985, by rfl⟩ : syracuseStep 2586647 = 3879971) B3879971
theorem B4143169 : Blo 1532463 4143169 := bstep (se 2 (by rfl) ⟨1553688, by rfl⟩ : syracuseStep 4143169 = 3107377) B3107377
theorem B2299979 : Blo 1532463 2299979 := bstep (se 1 (by rfl) ⟨1724984, by rfl⟩ : syracuseStep 2299979 = 3449969) B3449969
theorem B2299991 : Blo 1532463 2299991 := bstep (se 1 (by rfl) ⟨1724993, by rfl⟩ : syracuseStep 2299991 = 3449987) B3449987
theorem B2586775 : Blo 1532463 2586775 := bstep (se 1 (by rfl) ⟨1940081, by rfl⟩ : syracuseStep 2586775 = 3880163) B3880163
theorem B2455705 : Blo 1532463 2455705 := bstep (se 2 (by rfl) ⟨920889, by rfl⟩ : syracuseStep 2455705 = 1841779) B1841779
theorem B2300057 : Blo 1532463 2300057 := bstep (se 2 (by rfl) ⟨862521, by rfl⟩ : syracuseStep 2300057 = 1725043) B1725043
theorem B3274931 : Blo 1532463 3274931 := bstep (se 1 (by rfl) ⟨2456198, by rfl⟩ : syracuseStep 3274931 = 4912397) B4912397
theorem B2300171 : Blo 1532463 2300171 := bstep (se 1 (by rfl) ⟨1725128, by rfl⟩ : syracuseStep 2300171 = 3450257) B3450257
theorem B2300183 : Blo 1532463 2300183 := bstep (se 1 (by rfl) ⟨1725137, by rfl⟩ : syracuseStep 2300183 = 3450275) B3450275
theorem B5175575 : Blo 1532463 5175575 := bstep (se 1 (by rfl) ⟨3881681, by rfl⟩ : syracuseStep 5175575 = 7763363) B7763363
theorem B3881267 : Blo 1532463 3881267 := bstep (se 1 (by rfl) ⟨2910950, by rfl⟩ : syracuseStep 3881267 = 5821901) B5821901
theorem B2300249 : Blo 1532463 2300249 := bstep (se 2 (by rfl) ⟨862593, by rfl⟩ : syracuseStep 2300249 = 1725187) B1725187
theorem B11049317 : Blo 1532463 11049317 := bstep (se 4 (by rfl) ⟨1035873, by rfl⟩ : syracuseStep 11049317 = 2071747) B2071747
theorem B9959831 : Blo 1532463 9959831 := bstep (se 1 (by rfl) ⟨7469873, by rfl⟩ : syracuseStep 9959831 = 14939747) B14939747
theorem B2300363 : Blo 1532463 2300363 := bstep (se 1 (by rfl) ⟨1725272, by rfl⟩ : syracuseStep 2300363 = 3450545) B3450545
theorem B2300375 : Blo 1532463 2300375 := bstep (se 1 (by rfl) ⟨1725281, by rfl⟩ : syracuseStep 2300375 = 3450563) B3450563
theorem B8731097 : Blo 1532463 8731097 := bstep (se 2 (by rfl) ⟨3274161, by rfl⟩ : syracuseStep 8731097 = 6548323) B6548323
theorem B26204633 : Blo 1532463 26204633 := bstep (se 2 (by rfl) ⟨9826737, by rfl⟩ : syracuseStep 26204633 = 19653475) B19653475
theorem B7764497 : Blo 1532463 7764497 := bstep (se 2 (by rfl) ⟨2911686, by rfl⟩ : syracuseStep 7764497 = 5823373) B5823373
theorem B2300441 : Blo 1532463 2300441 := bstep (se 2 (by rfl) ⟨862665, by rfl⟩ : syracuseStep 2300441 = 1725331) B1725331
theorem B4913729 : Blo 1532463 4913729 := bstep (se 2 (by rfl) ⟨1842648, by rfl⟩ : syracuseStep 4913729 = 3685297) B3685297
theorem B1940107 : Blo 1532463 1940107 := bstep (se 1 (by rfl) ⟨1455080, by rfl⟩ : syracuseStep 1940107 = 2910161) B2910161
theorem B2300555 : Blo 1532463 2300555 := bstep (se 1 (by rfl) ⟨1725416, by rfl⟩ : syracuseStep 2300555 = 3450833) B3450833
theorem B2300567 : Blo 1532463 2300567 := bstep (se 1 (by rfl) ⟨1725425, by rfl⟩ : syracuseStep 2300567 = 3450851) B3450851
theorem B7764659 : Blo 1532463 7764659 := bstep (se 1 (by rfl) ⟨5823494, by rfl⟩ : syracuseStep 7764659 = 11646989) B11646989
theorem B5905075 : Blo 1532463 5905075 := bstep (se 1 (by rfl) ⟨4428806, by rfl⟩ : syracuseStep 5905075 = 8857613) B8857613
theorem B1637047 : Blo 1532463 1637047 := bstep (se 1 (by rfl) ⟨1227785, by rfl⟩ : syracuseStep 1637047 = 2455571) B2455571
theorem B2300633 : Blo 1532463 2300633 := bstep (se 2 (by rfl) ⟨862737, by rfl⟩ : syracuseStep 2300633 = 1725475) B1725475
theorem B2587403 : Blo 1532463 2587403 := bstep (se 1 (by rfl) ⟨1940552, by rfl⟩ : syracuseStep 2587403 = 3881105) B3881105
theorem B5176115 : Blo 1532463 5176115 := bstep (se 1 (by rfl) ⟨3882086, by rfl⟩ : syracuseStep 5176115 = 7764173) B7764173
theorem B3881803 : Blo 1532463 3881803 := bstep (se 1 (by rfl) ⟨2911352, by rfl⟩ : syracuseStep 3881803 = 5822705) B5822705
theorem B2300747 : Blo 1532463 2300747 := bstep (se 1 (by rfl) ⟨1725560, by rfl⟩ : syracuseStep 2300747 = 3451121) B3451121
theorem B2300759 : Blo 1532463 2300759 := bstep (se 1 (by rfl) ⟨1725569, by rfl⟩ : syracuseStep 2300759 = 3451139) B3451139
theorem B2587531 : Blo 1532463 2587531 := bstep (se 1 (by rfl) ⟨1940648, by rfl⟩ : syracuseStep 2587531 = 3881297) B3881297
theorem B1940375 : Blo 1532463 1940375 := bstep (se 1 (by rfl) ⟨1455281, by rfl⟩ : syracuseStep 1940375 = 2910563) B2910563
theorem B2300825 : Blo 1532463 2300825 := bstep (se 2 (by rfl) ⟨862809, by rfl⟩ : syracuseStep 2300825 = 1725619) B1725619
theorem B3881945 : Blo 1532463 3881945 := bstep (se 2 (by rfl) ⟨1455729, by rfl⟩ : syracuseStep 3881945 = 2911459) B2911459
theorem B11647961 : Blo 1532463 11647961 := bstep (se 2 (by rfl) ⟨4367985, by rfl⟩ : syracuseStep 11647961 = 8735971) B8735971
theorem B3275777 : Blo 1532463 3275777 := bstep (se 2 (by rfl) ⟨1228416, by rfl⟩ : syracuseStep 3275777 = 2456833) B2456833
theorem B1842187 : Blo 1532463 1842187 := bstep (se 1 (by rfl) ⟨1381640, by rfl⟩ : syracuseStep 1842187 = 2763281) B2763281
theorem B2300939 : Blo 1532463 2300939 := bstep (se 1 (by rfl) ⟨1725704, by rfl⟩ : syracuseStep 2300939 = 3451409) B3451409
theorem B2300951 : Blo 1532463 2300951 := bstep (se 1 (by rfl) ⟨1725713, by rfl⟩ : syracuseStep 2300951 = 3451427) B3451427
theorem B2587673 : Blo 1532463 2587673 := bstep (se 2 (by rfl) ⟨970377, by rfl⟩ : syracuseStep 2587673 = 1940755) B1940755
theorem B5176385 : Blo 1532463 5176385 := bstep (se 2 (by rfl) ⟨1941144, by rfl⟩ : syracuseStep 5176385 = 3882289) B3882289
theorem B53869637 : Blo 1532463 53869637 := bstep (se 4 (by rfl) ⟨5050278, by rfl⟩ : syracuseStep 53869637 = 10100557) B10100557
theorem B2301017 : Blo 1532463 2301017 := bstep (se 2 (by rfl) ⟨862881, by rfl⟩ : syracuseStep 2301017 = 1725763) B1725763
theorem B2587801 : Blo 1532463 2587801 := bstep (se 2 (by rfl) ⟨970425, by rfl⟩ : syracuseStep 2587801 = 1940851) B1940851
theorem B4365515 : Blo 1532463 4365515 := bstep (se 1 (by rfl) ⟨3274136, by rfl⟩ : syracuseStep 4365515 = 6548273) B6548273
theorem B2301131 : Blo 1532463 2301131 := bstep (se 1 (by rfl) ⟨1725848, by rfl⟩ : syracuseStep 2301131 = 3451697) B3451697
theorem B2301143 : Blo 1532463 2301143 := bstep (se 1 (by rfl) ⟨1725857, by rfl⟩ : syracuseStep 2301143 = 3451715) B3451715
theorem B24861937 : Blo 1532463 24861937 := bstep (se 2 (by rfl) ⟨9323226, by rfl⟩ : syracuseStep 24861937 = 18646453) B18646453
theorem B2301209 : Blo 1532463 2301209 := bstep (se 2 (by rfl) ⟨862953, by rfl⟩ : syracuseStep 2301209 = 1725907) B1725907
theorem B3448115 : Blo 1532463 3448115 := bstep (se 1 (by rfl) ⟨2586086, by rfl⟩ : syracuseStep 3448115 = 5172173) B5172173
theorem B3448151 : Blo 1532463 3448151 := bstep (se 1 (by rfl) ⟨2586113, by rfl⟩ : syracuseStep 3448151 = 5172227) B5172227
theorem B3276119 : Blo 1532463 3276119 := bstep (se 1 (by rfl) ⟨2457089, by rfl⟩ : syracuseStep 3276119 = 4914179) B4914179
theorem B2301323 : Blo 1532463 2301323 := bstep (se 1 (by rfl) ⟨1725992, by rfl⟩ : syracuseStep 2301323 = 3451985) B3451985
theorem B2301335 : Blo 1532463 2301335 := bstep (se 1 (by rfl) ⟨1726001, by rfl⟩ : syracuseStep 2301335 = 3452003) B3452003
theorem B2301401 : Blo 1532463 2301401 := bstep (se 2 (by rfl) ⟨863025, by rfl⟩ : syracuseStep 2301401 = 1726051) B1726051
theorem B1637867 : Blo 1532463 1637867 := bstep (se 1 (by rfl) ⟨1228400, by rfl⟩ : syracuseStep 1637867 = 2456801) B2456801
theorem B3448331 : Blo 1532463 3448331 := bstep (se 1 (by rfl) ⟨2586248, by rfl⟩ : syracuseStep 3448331 = 5172497) B5172497
theorem B15736355 : Blo 1532463 15736355 := bstep (se 1 (by rfl) ⟨11802266, by rfl⟩ : syracuseStep 15736355 = 23604533) B23604533
theorem B3448385 : Blo 1532463 3448385 := bstep (se 2 (by rfl) ⟨1293144, by rfl⟩ : syracuseStep 3448385 = 2586289) B2586289
theorem B2301515 : Blo 1532463 2301515 := bstep (se 1 (by rfl) ⟨1726136, by rfl⟩ : syracuseStep 2301515 = 3452273) B3452273
theorem B1941079 : Blo 1532463 1941079 := bstep (se 1 (by rfl) ⟨1455809, by rfl⟩ : syracuseStep 1941079 = 2911619) B2911619
theorem B2301527 : Blo 1532463 2301527 := bstep (se 1 (by rfl) ⟨1726145, by rfl⟩ : syracuseStep 2301527 = 3452291) B3452291
theorem B4365913 : Blo 1532463 4365913 := bstep (se 2 (by rfl) ⟨1637217, by rfl⟩ : syracuseStep 4365913 = 3274435) B3274435
theorem B5176925 : Blo 1532463 5176925 := bstep (se 3 (by rfl) ⟨970673, by rfl⟩ : syracuseStep 5176925 = 1941347) B1941347
theorem B2301593 : Blo 1532463 2301593 := bstep (se 2 (by rfl) ⟨863097, by rfl⟩ : syracuseStep 2301593 = 1726195) B1726195
theorem B2588375 : Blo 1532463 2588375 := bstep (se 1 (by rfl) ⟨1941281, by rfl⟩ : syracuseStep 2588375 = 3882563) B3882563
theorem B22093553 : Blo 1532463 22093553 := bstep (se 2 (by rfl) ⟨8285082, by rfl⟩ : syracuseStep 22093553 = 16570165) B16570165
theorem B3882775 : Blo 1532463 3882775 := bstep (se 1 (by rfl) ⟨2912081, by rfl⟩ : syracuseStep 3882775 = 5824163) B5824163
theorem B3448601 : Blo 1532463 3448601 := bstep (se 2 (by rfl) ⟨1293225, by rfl⟩ : syracuseStep 3448601 = 2586451) B2586451
theorem B4915009 : Blo 1532463 4915009 := bstep (se 2 (by rfl) ⟨1843128, by rfl⟩ : syracuseStep 4915009 = 3686257) B3686257
theorem B5824331 : Blo 1532463 5824331 := bstep (se 1 (by rfl) ⟨4368248, by rfl⟩ : syracuseStep 5824331 = 8736497) B8736497
theorem B2588503 : Blo 1532463 2588503 := bstep (se 1 (by rfl) ⟨1941377, by rfl⟩ : syracuseStep 2588503 = 3882755) B3882755
theorem B5824345 : Blo 1532463 5824345 := bstep (se 2 (by rfl) ⟨2184129, by rfl⟩ : syracuseStep 5824345 = 4368259) B4368259
theorem B3448691 : Blo 1532463 3448691 := bstep (se 1 (by rfl) ⟨2586518, by rfl⟩ : syracuseStep 3448691 = 5173037) B5173037
theorem B3448727 : Blo 1532463 3448727 := bstep (se 1 (by rfl) ⟨2586545, by rfl⟩ : syracuseStep 3448727 = 5173091) B5173091
theorem B2949067 : Blo 1532463 2949067 := bstep (se 1 (by rfl) ⟨2211800, by rfl⟩ : syracuseStep 2949067 = 4423601) B4423601
theorem B3686411 : Blo 1532463 3686411 := bstep (se 1 (by rfl) ⟨2764808, by rfl⟩ : syracuseStep 3686411 = 5529617) B5529617
theorem B14942231 : Blo 1532463 14942231 := bstep (se 1 (by rfl) ⟨11206673, by rfl⟩ : syracuseStep 14942231 = 22413347) B22413347
theorem B3031175 : Blo 1532463 3031175 := bstep (se 1 (by rfl) ⟨2273381, by rfl⟩ : syracuseStep 3031175 = 4546763) B4546763
theorem B2588807 : Blo 1532463 2588807 := bstep (se 1 (by rfl) ⟨1941605, by rfl⟩ : syracuseStep 2588807 = 3883211) B3883211
theorem B3448979 : Blo 1532463 3448979 := bstep (se 1 (by rfl) ⟨2586734, by rfl⟩ : syracuseStep 3448979 = 5173469) B5173469
theorem B3449033 : Blo 1532463 3449033 := bstep (se 2 (by rfl) ⟨1293387, by rfl⟩ : syracuseStep 3449033 = 2586775) B2586775
theorem B8732873 : Blo 1532463 8732873 := bstep (se 2 (by rfl) ⟨3274827, by rfl⟩ : syracuseStep 8732873 = 6549655) B6549655
theorem B4145527 : Blo 1532463 4145527 := bstep (se 1 (by rfl) ⟨3109145, by rfl⟩ : syracuseStep 4145527 = 6218291) B6218291
theorem B4424071 : Blo 1532463 4424071 := bstep (se 1 (by rfl) ⟨3318053, by rfl⟩ : syracuseStep 4424071 = 6636107) B6636107
theorem B5177735 : Blo 1532463 5177735 := bstep (se 1 (by rfl) ⟨3883301, by rfl⟩ : syracuseStep 5177735 = 7766603) B7766603
theorem B3883535 : Blo 1532463 3883535 := bstep (se 1 (by rfl) ⟨2912651, by rfl⟩ : syracuseStep 3883535 = 5825303) B5825303
theorem B1532475 : Blo 1532463 1532475 := bstep (se 1 (by rfl) ⟨1149356, by rfl⟩ : syracuseStep 1532475 = 2298713) B2298713
theorem B1532551 : Blo 1532463 1532551 := bstep (se 1 (by rfl) ⟨1149413, by rfl⟩ : syracuseStep 1532551 = 2298827) B2298827
theorem B1532559 : Blo 1532463 1532559 := bstep (se 1 (by rfl) ⟨1149419, by rfl⟩ : syracuseStep 1532559 = 2298839) B2298839
theorem B1532603 : Blo 1532463 1532603 := bstep (se 1 (by rfl) ⟨1149452, by rfl⟩ : syracuseStep 1532603 = 2298905) B2298905
theorem B7471853 : Blo 1532463 7471853 := bstep (se 3 (by rfl) ⟨1400972, by rfl⟩ : syracuseStep 7471853 = 2801945) B2801945
theorem B7766765 : Blo 1532463 7766765 := bstep (se 3 (by rfl) ⟨1456268, by rfl⟩ : syracuseStep 7766765 = 2912537) B2912537
theorem B5178113 : Blo 1532463 5178113 := bstep (se 2 (by rfl) ⟨1941792, by rfl⟩ : syracuseStep 5178113 = 3883585) B3883585
theorem B1532679 : Blo 1532463 1532679 := bstep (se 1 (by rfl) ⟨1149509, by rfl⟩ : syracuseStep 1532679 = 2299019) B2299019
theorem B1532687 : Blo 1532463 1532687 := bstep (se 1 (by rfl) ⟨1149515, by rfl⟩ : syracuseStep 1532687 = 2299031) B2299031
theorem B1532731 : Blo 1532463 1532731 := bstep (se 1 (by rfl) ⟨1149548, by rfl⟩ : syracuseStep 1532731 = 2299097) B2299097
theorem B1532807 : Blo 1532463 1532807 := bstep (se 1 (by rfl) ⟨1149605, by rfl⟩ : syracuseStep 1532807 = 2299211) B2299211
theorem B3449735 : Blo 1532463 3449735 := bstep (se 1 (by rfl) ⟨2587301, by rfl⟩ : syracuseStep 3449735 = 5174603) B5174603
theorem B1532815 : Blo 1532463 1532815 := bstep (se 1 (by rfl) ⟨1149611, by rfl⟩ : syracuseStep 1532815 = 2299223) B2299223
theorem B7873433 : Blo 1532463 7873433 := bstep (se 2 (by rfl) ⟨2952537, by rfl⟩ : syracuseStep 7873433 = 5905075) B5905075
theorem B1532859 : Blo 1532463 1532859 := bstep (se 1 (by rfl) ⟨1149644, by rfl⟩ : syracuseStep 1532859 = 2299289) B2299289
theorem B1532935 : Blo 1532463 1532935 := bstep (se 1 (by rfl) ⟨1149701, by rfl⟩ : syracuseStep 1532935 = 2299403) B2299403
theorem B4367371 : Blo 1532463 4367371 := bstep (se 1 (by rfl) ⟨3275528, by rfl⟩ : syracuseStep 4367371 = 6551057) B6551057
theorem B1532943 : Blo 1532463 1532943 := bstep (se 1 (by rfl) ⟨1149707, by rfl⟩ : syracuseStep 1532943 = 2299415) B2299415
theorem B1532987 : Blo 1532463 1532987 := bstep (se 1 (by rfl) ⟨1149740, by rfl⟩ : syracuseStep 1532987 = 2299481) B2299481
theorem B3449915 : Blo 1532463 3449915 := bstep (se 1 (by rfl) ⟨2587436, by rfl⟩ : syracuseStep 3449915 = 5174873) B5174873
theorem B1533063 : Blo 1532463 1533063 := bstep (se 1 (by rfl) ⟨1149797, by rfl⟩ : syracuseStep 1533063 = 2299595) B2299595
theorem B1533071 : Blo 1532463 1533071 := bstep (se 1 (by rfl) ⟨1149803, by rfl⟩ : syracuseStep 1533071 = 2299607) B2299607
theorem B3450041 : Blo 1532463 3450041 := bstep (se 2 (by rfl) ⟨1293765, by rfl⟩ : syracuseStep 3450041 = 2587531) B2587531
theorem B1533115 : Blo 1532463 1533115 := bstep (se 1 (by rfl) ⟨1149836, by rfl⟩ : syracuseStep 1533115 = 2299673) B2299673
theorem B1533191 : Blo 1532463 1533191 := bstep (se 1 (by rfl) ⟨1149893, by rfl⟩ : syracuseStep 1533191 = 2299787) B2299787
theorem B1533199 : Blo 1532463 1533199 := bstep (se 1 (by rfl) ⟨1149899, by rfl⟩ : syracuseStep 1533199 = 2299799) B2299799
theorem B4367645 : Blo 1532463 4367645 := bstep (se 3 (by rfl) ⟨818933, by rfl⟩ : syracuseStep 4367645 = 1637867) B1637867
theorem B1533243 : Blo 1532463 1533243 := bstep (se 1 (by rfl) ⟨1149932, by rfl⟩ : syracuseStep 1533243 = 2299865) B2299865
theorem B1533319 : Blo 1532463 1533319 := bstep (se 1 (by rfl) ⟨1149989, by rfl⟩ : syracuseStep 1533319 = 2299979) B2299979
theorem B37307783 : Blo 1532463 37307783 := bstep (se 1 (by rfl) ⟨27980837, by rfl⟩ : syracuseStep 37307783 = 55961675) B55961675
theorem B1533327 : Blo 1532463 1533327 := bstep (se 1 (by rfl) ⟨1149995, by rfl⟩ : syracuseStep 1533327 = 2299991) B2299991
theorem B1533371 : Blo 1532463 1533371 := bstep (se 1 (by rfl) ⟨1150028, by rfl⟩ : syracuseStep 1533371 = 2300057) B2300057
theorem B7759313 : Blo 1532463 7759313 := bstep (se 2 (by rfl) ⟨2909742, by rfl⟩ : syracuseStep 7759313 = 5819485) B5819485
theorem B1533447 : Blo 1532463 1533447 := bstep (se 1 (by rfl) ⟨1150085, by rfl⟩ : syracuseStep 1533447 = 2300171) B2300171
theorem B1533455 : Blo 1532463 1533455 := bstep (se 1 (by rfl) ⟨1150091, by rfl⟩ : syracuseStep 1533455 = 2300183) B2300183
theorem B3450383 : Blo 1532463 3450383 := bstep (se 1 (by rfl) ⟨2587787, by rfl⟩ : syracuseStep 3450383 = 5175575) B5175575
theorem B7767575 : Blo 1532463 7767575 := bstep (se 1 (by rfl) ⟨5825681, by rfl⟩ : syracuseStep 7767575 = 11651363) B11651363
theorem B5826077 : Blo 1532463 5826077 := bstep (se 3 (by rfl) ⟨1092389, by rfl⟩ : syracuseStep 5826077 = 2184779) B2184779
theorem B3450401 : Blo 1532463 3450401 := bstep (se 2 (by rfl) ⟨1293900, by rfl⟩ : syracuseStep 3450401 = 2587801) B2587801
theorem B1533499 : Blo 1532463 1533499 := bstep (se 1 (by rfl) ⟨1150124, by rfl⟩ : syracuseStep 1533499 = 2300249) B2300249
theorem B7366211 : Blo 1532463 7366211 := bstep (se 1 (by rfl) ⟨5524658, by rfl⟩ : syracuseStep 7366211 = 11049317) B11049317
theorem B4146803 : Blo 1532463 4146803 := bstep (se 1 (by rfl) ⟨3110102, by rfl⟩ : syracuseStep 4146803 = 6220205) B6220205
theorem B1533575 : Blo 1532463 1533575 := bstep (se 1 (by rfl) ⟨1150181, by rfl⟩ : syracuseStep 1533575 = 2300363) B2300363
theorem B1533583 : Blo 1532463 1533583 := bstep (se 1 (by rfl) ⟨1150187, by rfl⟩ : syracuseStep 1533583 = 2300375) B2300375
theorem B1533627 : Blo 1532463 1533627 := bstep (se 1 (by rfl) ⟨1150220, by rfl⟩ : syracuseStep 1533627 = 2300441) B2300441
theorem B1533703 : Blo 1532463 1533703 := bstep (se 1 (by rfl) ⟨1150277, by rfl⟩ : syracuseStep 1533703 = 2300555) B2300555
theorem B1533711 : Blo 1532463 1533711 := bstep (se 1 (by rfl) ⟨1150283, by rfl⟩ : syracuseStep 1533711 = 2300567) B2300567
theorem B2524943 : Blo 1532463 2524943 := bstep (se 1 (by rfl) ⟨1893707, by rfl⟩ : syracuseStep 2524943 = 3787415) B3787415
theorem B4146977 : Blo 1532463 4146977 := bstep (se 2 (by rfl) ⟨1555116, by rfl⟩ : syracuseStep 4146977 = 3110233) B3110233
theorem B1533755 : Blo 1532463 1533755 := bstep (se 1 (by rfl) ⟨1150316, by rfl⟩ : syracuseStep 1533755 = 2300633) B2300633
theorem B4147031 : Blo 1532463 4147031 := bstep (se 1 (by rfl) ⟨3110273, by rfl⟩ : syracuseStep 4147031 = 6220547) B6220547
theorem B3450743 : Blo 1532463 3450743 := bstep (se 1 (by rfl) ⟨2588057, by rfl⟩ : syracuseStep 3450743 = 5176115) B5176115
theorem B1533831 : Blo 1532463 1533831 := bstep (se 1 (by rfl) ⟨1150373, by rfl⟩ : syracuseStep 1533831 = 2300747) B2300747
theorem B1533839 : Blo 1532463 1533839 := bstep (se 1 (by rfl) ⟨1150379, by rfl⟩ : syracuseStep 1533839 = 2300759) B2300759
theorem B1533883 : Blo 1532463 1533883 := bstep (se 1 (by rfl) ⟨1150412, by rfl⟩ : syracuseStep 1533883 = 2300825) B2300825
theorem B26920907 : Blo 1532463 26920907 := bstep (se 1 (by rfl) ⟨20190680, by rfl⟩ : syracuseStep 26920907 = 40381361) B40381361
theorem B1533959 : Blo 1532463 1533959 := bstep (se 1 (by rfl) ⟨1150469, by rfl⟩ : syracuseStep 1533959 = 2300939) B2300939
theorem B1533967 : Blo 1532463 1533967 := bstep (se 1 (by rfl) ⟨1150475, by rfl⟩ : syracuseStep 1533967 = 2300951) B2300951
theorem B3450923 : Blo 1532463 3450923 := bstep (se 1 (by rfl) ⟨2588192, by rfl⟩ : syracuseStep 3450923 = 5176385) B5176385
theorem B1534011 : Blo 1532463 1534011 := bstep (se 1 (by rfl) ⟨1150508, by rfl⟩ : syracuseStep 1534011 = 2301017) B2301017
theorem B8734787 : Blo 1532463 8734787 := bstep (se 1 (by rfl) ⟨6551090, by rfl⟩ : syracuseStep 8734787 = 13102181) B13102181
theorem B2910343 : Blo 1532463 2910343 := bstep (se 1 (by rfl) ⟨2182757, by rfl⟩ : syracuseStep 2910343 = 4365515) B4365515
theorem B1534087 : Blo 1532463 1534087 := bstep (se 1 (by rfl) ⟨1150565, by rfl⟩ : syracuseStep 1534087 = 2301131) B2301131
theorem B1534095 : Blo 1532463 1534095 := bstep (se 1 (by rfl) ⟨1150571, by rfl⟩ : syracuseStep 1534095 = 2301143) B2301143
theorem B1534139 : Blo 1532463 1534139 := bstep (se 1 (by rfl) ⟨1150604, by rfl⟩ : syracuseStep 1534139 = 2301209) B2301209
theorem B16574665 : Blo 1532463 16574665 := bstep (se 2 (by rfl) ⟨6215499, by rfl⟩ : syracuseStep 16574665 = 12430999) B12430999
theorem B1534215 : Blo 1532463 1534215 := bstep (se 1 (by rfl) ⟨1150661, by rfl⟩ : syracuseStep 1534215 = 2301323) B2301323
theorem B1534223 : Blo 1532463 1534223 := bstep (se 1 (by rfl) ⟨1150667, by rfl⟩ : syracuseStep 1534223 = 2301335) B2301335
theorem B1534267 : Blo 1532463 1534267 := bstep (se 1 (by rfl) ⟨1150700, by rfl⟩ : syracuseStep 1534267 = 2301401) B2301401
theorem B17459549 : Blo 1532463 17459549 := bstep (se 3 (by rfl) ⟨3273665, by rfl⟩ : syracuseStep 17459549 = 6547331) B6547331
theorem B4426103 : Blo 1532463 4426103 := bstep (se 1 (by rfl) ⟨3319577, by rfl⟩ : syracuseStep 4426103 = 6639155) B6639155
theorem B1534343 : Blo 1532463 1534343 := bstep (se 1 (by rfl) ⟨1150757, by rfl⟩ : syracuseStep 1534343 = 2301515) B2301515
theorem B1534351 : Blo 1532463 1534351 := bstep (se 1 (by rfl) ⟨1150763, by rfl⟩ : syracuseStep 1534351 = 2301527) B2301527
theorem B3451283 : Blo 1532463 3451283 := bstep (se 1 (by rfl) ⟨2588462, by rfl⟩ : syracuseStep 3451283 = 5176925) B5176925
theorem B13101497 : Blo 1532463 13101497 := bstep (se 2 (by rfl) ⟨4913061, by rfl⟩ : syracuseStep 13101497 = 9826123) B9826123
theorem B1534395 : Blo 1532463 1534395 := bstep (se 1 (by rfl) ⟨1150796, by rfl⟩ : syracuseStep 1534395 = 2301593) B2301593
theorem B3451337 : Blo 1532463 3451337 := bstep (se 2 (by rfl) ⟨1294251, by rfl⟩ : syracuseStep 3451337 = 2588503) B2588503
theorem B9325003 : Blo 1532463 9325003 := bstep (se 1 (by rfl) ⟨6993752, by rfl⟩ : syracuseStep 9325003 = 13987505) B13987505
theorem B18664013 : Blo 1532463 18664013 := bstep (se 3 (by rfl) ⟨3499502, by rfl⟩ : syracuseStep 18664013 = 6999005) B6999005
theorem B5818999 : Blo 1532463 5818999 := bstep (se 1 (by rfl) ⟨4364249, by rfl⟩ : syracuseStep 5818999 = 8728499) B8728499
theorem B1747855 : Blo 1532463 1747855 := bstep (se 1 (by rfl) ⟨1310891, by rfl⟩ : syracuseStep 1747855 = 2621783) B2621783
theorem B8399875 : Blo 1532463 8399875 := bstep (se 1 (by rfl) ⟨6299906, by rfl⟩ : syracuseStep 8399875 = 12599813) B12599813
theorem B22096901 : Blo 1532463 22096901 := bstep (se 4 (by rfl) ⟨2071584, by rfl⟩ : syracuseStep 22096901 = 4143169) B4143169
theorem B8293387 : Blo 1532463 8293387 := bstep (se 1 (by rfl) ⟨6220040, by rfl⟩ : syracuseStep 8293387 = 12440081) B12440081
theorem B14027863 : Blo 1532463 14027863 := bstep (se 1 (by rfl) ⟨10520897, by rfl⟩ : syracuseStep 14027863 = 21041795) B21041795
theorem B2657399 : Blo 1532463 2657399 := bstep (se 1 (by rfl) ⟨1993049, by rfl⟩ : syracuseStep 2657399 = 3986099) B3986099
theorem B3452039 : Blo 1532463 3452039 := bstep (se 1 (by rfl) ⟨2589029, by rfl⟩ : syracuseStep 3452039 = 5178059) B5178059
theorem B11046203 : Blo 1532463 11046203 := bstep (se 1 (by rfl) ⟨8284652, by rfl⟩ : syracuseStep 11046203 = 16569305) B16569305
theorem B3452219 : Blo 1532463 3452219 := bstep (se 1 (by rfl) ⟨2589164, by rfl⟩ : syracuseStep 3452219 = 5178329) B5178329
theorem B3452345 : Blo 1532463 3452345 := bstep (se 2 (by rfl) ⟨1294629, by rfl⟩ : syracuseStep 3452345 = 2589259) B2589259
theorem B7761419 : Blo 1532463 7761419 := bstep (se 1 (by rfl) ⟨5821064, by rfl⟩ : syracuseStep 7761419 = 11642129) B11642129
theorem B5819971 : Blo 1532463 5819971 := bstep (se 1 (by rfl) ⟨4364978, by rfl⟩ : syracuseStep 5819971 = 8729957) B8729957
theorem B2182729 : Blo 1532463 2182729 := bstep (se 2 (by rfl) ⟨818523, by rfl⟩ : syracuseStep 2182729 = 1637047) B1637047
theorem B4427399 : Blo 1532463 4427399 := bstep (se 1 (by rfl) ⟨3320549, by rfl⟩ : syracuseStep 4427399 = 6641099) B6641099
theorem B7761581 : Blo 1532463 7761581 := bstep (se 3 (by rfl) ⟨1455296, by rfl⟩ : syracuseStep 7761581 = 2910593) B2910593
theorem B2911945 : Blo 1532463 2911945 := bstep (se 2 (by rfl) ⟨1091979, by rfl⟩ : syracuseStep 2911945 = 2183959) B2183959
theorem B14946049 : Blo 1532463 14946049 := bstep (se 2 (by rfl) ⟨5604768, by rfl⟩ : syracuseStep 14946049 = 11209537) B11209537
theorem B17461007 : Blo 1532463 17461007 := bstep (se 1 (by rfl) ⟨13095755, by rfl⟩ : syracuseStep 17461007 = 26191511) B26191511
theorem B6549281 : Blo 1532463 6549281 := bstep (se 2 (by rfl) ⟨2455980, by rfl⟩ : syracuseStep 6549281 = 4911961) B4911961
theorem B5820275 : Blo 1532463 5820275 := bstep (se 1 (by rfl) ⟨4365206, by rfl⟩ : syracuseStep 5820275 = 8730413) B8730413
theorem B3321719 : Blo 1532463 3321719 := bstep (se 1 (by rfl) ⟨2491289, by rfl⟩ : syracuseStep 3321719 = 4982579) B4982579
theorem B5173145 : Blo 1532463 5173145 := bstep (se 2 (by rfl) ⟨1939929, by rfl⟩ : syracuseStep 5173145 = 3879859) B3879859
theorem B1724431 : Blo 1532463 1724431 := bstep (se 1 (by rfl) ⟨1293323, by rfl⟩ : syracuseStep 1724431 = 2586647) B2586647
theorem B2183287 : Blo 1532463 2183287 := bstep (se 1 (by rfl) ⟨1637465, by rfl⟩ : syracuseStep 2183287 = 3274931) B3274931
theorem B7368823 : Blo 1532463 7368823 := bstep (se 1 (by rfl) ⟨5526617, by rfl⟩ : syracuseStep 7368823 = 11053235) B11053235
theorem B6639887 : Blo 1532463 6639887 := bstep (se 1 (by rfl) ⟨4979915, by rfl⟩ : syracuseStep 6639887 = 9959831) B9959831
theorem B3879211 : Blo 1532463 3879211 := bstep (se 1 (by rfl) ⟨2909408, by rfl⟩ : syracuseStep 3879211 = 5818817) B5818817
theorem B5820731 : Blo 1532463 5820731 := bstep (se 1 (by rfl) ⟨4365548, by rfl⟩ : syracuseStep 5820731 = 8731097) B8731097
theorem B17469755 : Blo 1532463 17469755 := bstep (se 1 (by rfl) ⟨13102316, by rfl⟩ : syracuseStep 17469755 = 26204633) B26204633
theorem B33149249 : Blo 1532463 33149249 := bstep (se 2 (by rfl) ⟨12430968, by rfl⟩ : syracuseStep 33149249 = 24861937) B24861937
theorem B16576913 : Blo 1532463 16576913 := bstep (se 2 (by rfl) ⟨6216342, by rfl⟩ : syracuseStep 16576913 = 12432685) B12432685
theorem B3879353 : Blo 1532463 3879353 := bstep (se 2 (by rfl) ⟨1454757, by rfl⟩ : syracuseStep 3879353 = 2909515) B2909515
theorem B1724935 : Blo 1532463 1724935 := bstep (se 1 (by rfl) ⟨1293701, by rfl⟩ : syracuseStep 1724935 = 2587403) B2587403
theorem B5173847 : Blo 1532463 5173847 := bstep (se 1 (by rfl) ⟨3880385, by rfl⟩ : syracuseStep 5173847 = 7760771) B7760771
theorem B8729207 : Blo 1532463 8729207 := bstep (se 1 (by rfl) ⟨6546905, by rfl⟩ : syracuseStep 8729207 = 13093811) B13093811
theorem B2183851 : Blo 1532463 2183851 := bstep (se 1 (by rfl) ⟨1637888, by rfl⟩ : syracuseStep 2183851 = 3275777) B3275777
theorem B1725115 : Blo 1532463 1725115 := bstep (se 1 (by rfl) ⟨1293836, by rfl⟩ : syracuseStep 1725115 = 2587673) B2587673
theorem B8090369 : Blo 1532463 8090369 := bstep (se 2 (by rfl) ⟨3033888, by rfl⟩ : syracuseStep 8090369 = 6067777) B6067777
theorem B5821217 : Blo 1532463 5821217 := bstep (se 2 (by rfl) ⟨2182956, by rfl⟩ : syracuseStep 5821217 = 4365913) B4365913
theorem B2298743 : Blo 1532463 2298743 := bstep (se 1 (by rfl) ⟨1724057, by rfl⟩ : syracuseStep 2298743 = 3448115) B3448115
theorem B2298767 : Blo 1532463 2298767 := bstep (se 1 (by rfl) ⟨1724075, by rfl⟩ : syracuseStep 2298767 = 3448151) B3448151
theorem B2184079 : Blo 1532463 2184079 := bstep (se 1 (by rfl) ⟨1638059, by rfl⟩ : syracuseStep 2184079 = 3276119) B3276119
theorem B2298809 : Blo 1532463 2298809 := bstep (se 2 (by rfl) ⟨862053, by rfl⟩ : syracuseStep 2298809 = 1724107) B1724107
theorem B2298887 : Blo 1532463 2298887 := bstep (se 1 (by rfl) ⟨1724165, by rfl⟩ : syracuseStep 2298887 = 3448331) B3448331
theorem B4912139 : Blo 1532463 4912139 := bstep (se 1 (by rfl) ⟨3684104, by rfl⟩ : syracuseStep 4912139 = 7368209) B7368209
theorem B10490903 : Blo 1532463 10490903 := bstep (se 1 (by rfl) ⟨7868177, by rfl⟩ : syracuseStep 10490903 = 15736355) B15736355
theorem B2298923 : Blo 1532463 2298923 := bstep (se 1 (by rfl) ⟨1724192, by rfl⟩ : syracuseStep 2298923 = 3448385) B3448385
theorem B5174333 : Blo 1532463 5174333 := bstep (se 3 (by rfl) ⟨970187, by rfl⟩ : syracuseStep 5174333 = 1940375) B1940375
theorem B2298953 : Blo 1532463 2298953 := bstep (se 2 (by rfl) ⟨862107, by rfl⟩ : syracuseStep 2298953 = 1724215) B1724215
theorem B1725583 : Blo 1532463 1725583 := bstep (se 1 (by rfl) ⟨1294187, by rfl⟩ : syracuseStep 1725583 = 2588375) B2588375
theorem B16807085 : Blo 1532463 16807085 := bstep (se 3 (by rfl) ⟨3151328, by rfl⟩ : syracuseStep 16807085 = 6302657) B6302657
theorem B2299067 : Blo 1532463 2299067 := bstep (se 1 (by rfl) ⟨1724300, by rfl⟩ : syracuseStep 2299067 = 3448601) B3448601
theorem B2299127 : Blo 1532463 2299127 := bstep (se 1 (by rfl) ⟨1724345, by rfl⟩ : syracuseStep 2299127 = 3448691) B3448691
theorem B7763201 : Blo 1532463 7763201 := bstep (se 2 (by rfl) ⟨2911200, by rfl⟩ : syracuseStep 7763201 = 5822401) B5822401
theorem B2299151 : Blo 1532463 2299151 := bstep (se 1 (by rfl) ⟨1724363, by rfl⟩ : syracuseStep 2299151 = 3448727) B3448727
theorem B2299193 : Blo 1532463 2299193 := bstep (se 2 (by rfl) ⟨862197, by rfl⟩ : syracuseStep 2299193 = 1724395) B1724395
theorem B2299271 : Blo 1532463 2299271 := bstep (se 1 (by rfl) ⟨1724453, by rfl⟩ : syracuseStep 2299271 = 3448907) B3448907
theorem B9819539 : Blo 1532463 9819539 := bstep (se 1 (by rfl) ⟨7364654, by rfl⟩ : syracuseStep 9819539 = 14729309) B14729309
theorem B3880345 : Blo 1532463 3880345 := bstep (se 2 (by rfl) ⟨1455129, by rfl⟩ : syracuseStep 3880345 = 2910259) B2910259
theorem B2299307 : Blo 1532463 2299307 := bstep (se 1 (by rfl) ⟨1724480, by rfl⟩ : syracuseStep 2299307 = 3448961) B3448961
theorem B2299337 : Blo 1532463 2299337 := bstep (se 2 (by rfl) ⟨862251, by rfl⟩ : syracuseStep 2299337 = 1724503) B1724503
theorem B143652365 : Blo 1532463 143652365 := bstep (se 3 (by rfl) ⟨26934818, by rfl⟩ : syracuseStep 143652365 = 53869637) B53869637
theorem B2586127 : Blo 1532463 2586127 := bstep (se 1 (by rfl) ⟨1939595, by rfl⟩ : syracuseStep 2586127 = 3879191) B3879191
theorem B3274273 : Blo 1532463 3274273 := bstep (se 2 (by rfl) ⟨1227852, by rfl⟩ : syracuseStep 3274273 = 2455705) B2455705
theorem B2299451 : Blo 1532463 2299451 := bstep (se 1 (by rfl) ⟨1724588, by rfl⟩ : syracuseStep 2299451 = 3449177) B3449177
theorem B3880507 : Blo 1532463 3880507 := bstep (se 1 (by rfl) ⟨2910380, by rfl⟩ : syracuseStep 3880507 = 5820761) B5820761
theorem B9819767 : Blo 1532463 9819767 := bstep (se 1 (by rfl) ⟨7364825, by rfl⟩ : syracuseStep 9819767 = 14729651) B14729651
theorem B2299511 : Blo 1532463 2299511 := bstep (se 1 (by rfl) ⟨1724633, by rfl⟩ : syracuseStep 2299511 = 3449267) B3449267
theorem B1726087 : Blo 1532463 1726087 := bstep (se 1 (by rfl) ⟨1294565, by rfl⟩ : syracuseStep 1726087 = 2589131) B2589131
theorem B2299535 : Blo 1532463 2299535 := bstep (se 1 (by rfl) ⟨1724651, by rfl⟩ : syracuseStep 2299535 = 3449303) B3449303
theorem B2299577 : Blo 1532463 2299577 := bstep (se 2 (by rfl) ⟨862341, by rfl⟩ : syracuseStep 2299577 = 1724683) B1724683
theorem B3880649 : Blo 1532463 3880649 := bstep (se 2 (by rfl) ⟨1455243, by rfl⟩ : syracuseStep 3880649 = 2910487) B2910487
theorem B5822189 : Blo 1532463 5822189 := bstep (se 3 (by rfl) ⟨1091660, by rfl⟩ : syracuseStep 5822189 = 2183321) B2183321
theorem B2299655 : Blo 1532463 2299655 := bstep (se 1 (by rfl) ⟨1724741, by rfl⟩ : syracuseStep 2299655 = 3449483) B3449483
theorem B2299691 : Blo 1532463 2299691 := bstep (se 1 (by rfl) ⟨1724768, by rfl⟩ : syracuseStep 2299691 = 3449537) B3449537
theorem B1726267 : Blo 1532463 1726267 := bstep (se 1 (by rfl) ⟨1294700, by rfl⟩ : syracuseStep 1726267 = 2589401) B2589401
theorem B2299721 : Blo 1532463 2299721 := bstep (se 2 (by rfl) ⟨862395, by rfl⟩ : syracuseStep 2299721 = 1724791) B1724791
theorem B8738705 : Blo 1532463 8738705 := bstep (se 2 (by rfl) ⟨3277014, by rfl⟩ : syracuseStep 8738705 = 6554029) B6554029
theorem B2299835 : Blo 1532463 2299835 := bstep (se 1 (by rfl) ⟨1724876, by rfl⟩ : syracuseStep 2299835 = 3449753) B3449753
theorem B2299895 : Blo 1532463 2299895 := bstep (se 1 (by rfl) ⟨1724921, by rfl⟩ : syracuseStep 2299895 = 3449843) B3449843
theorem B2299919 : Blo 1532463 2299919 := bstep (se 1 (by rfl) ⟨1724939, by rfl⟩ : syracuseStep 2299919 = 3449879) B3449879
theorem B3880993 : Blo 1532463 3880993 := bstep (se 2 (by rfl) ⟨1455372, by rfl⟩ : syracuseStep 3880993 = 2910745) B2910745
theorem B2586667 : Blo 1532463 2586667 := bstep (se 1 (by rfl) ⟨1940000, by rfl⟩ : syracuseStep 2586667 = 3880001) B3880001
theorem B7764011 : Blo 1532463 7764011 := bstep (se 1 (by rfl) ⟨5823008, by rfl⟩ : syracuseStep 7764011 = 11646017) B11646017
theorem B2299961 : Blo 1532463 2299961 := bstep (se 2 (by rfl) ⟨862485, by rfl⟩ : syracuseStep 2299961 = 1724971) B1724971
theorem B10639421 : Blo 1532463 10639421 := bstep (se 3 (by rfl) ⟨1994891, by rfl⟩ : syracuseStep 10639421 = 3989783) B3989783
theorem B13998167 : Blo 1532463 13998167 := bstep (se 1 (by rfl) ⟨10498625, by rfl⟩ : syracuseStep 13998167 = 20997251) B20997251
theorem B2300039 : Blo 1532463 2300039 := bstep (se 1 (by rfl) ⟨1725029, by rfl⟩ : syracuseStep 2300039 = 3450059) B3450059
theorem B2300075 : Blo 1532463 2300075 := bstep (se 1 (by rfl) ⟨1725056, by rfl⟩ : syracuseStep 2300075 = 3450113) B3450113
theorem B2586809 : Blo 1532463 2586809 := bstep (se 2 (by rfl) ⟨970053, by rfl⟩ : syracuseStep 2586809 = 1940107) B1940107
theorem B2300105 : Blo 1532463 2300105 := bstep (se 2 (by rfl) ⟨862539, by rfl⟩ : syracuseStep 2300105 = 1725079) B1725079
theorem B1939727 : Blo 1532463 1939727 := bstep (se 1 (by rfl) ⟨1454795, by rfl⟩ : syracuseStep 1939727 = 2909591) B2909591
theorem B9451835 : Blo 1532463 9451835 := bstep (se 1 (by rfl) ⟨7088876, by rfl⟩ : syracuseStep 9451835 = 14177753) B14177753
theorem B2300219 : Blo 1532463 2300219 := bstep (se 1 (by rfl) ⟨1725164, by rfl⟩ : syracuseStep 2300219 = 3450329) B3450329
theorem B8739161 : Blo 1532463 8739161 := bstep (se 2 (by rfl) ⟨3277185, by rfl⟩ : syracuseStep 8739161 = 6554371) B6554371
theorem B2300279 : Blo 1532463 2300279 := bstep (se 1 (by rfl) ⟨1725209, by rfl⟩ : syracuseStep 2300279 = 3450419) B3450419
theorem B2300303 : Blo 1532463 2300303 := bstep (se 1 (by rfl) ⟨1725227, by rfl⟩ : syracuseStep 2300303 = 3450455) B3450455
theorem B24869267 : Blo 1532463 24869267 := bstep (se 1 (by rfl) ⟨18651950, by rfl⟩ : syracuseStep 24869267 = 37303901) B37303901
theorem B5822873 : Blo 1532463 5822873 := bstep (se 2 (by rfl) ⟨2183577, by rfl⟩ : syracuseStep 5822873 = 4367155) B4367155
theorem B4364729 : Blo 1532463 4364729 := bstep (se 2 (by rfl) ⟨1636773, by rfl⟩ : syracuseStep 4364729 = 3273547) B3273547
theorem B5175737 : Blo 1532463 5175737 := bstep (se 2 (by rfl) ⟨1940901, by rfl⟩ : syracuseStep 5175737 = 3881803) B3881803
theorem B1636795 : Blo 1532463 1636795 := bstep (se 1 (by rfl) ⟨1227596, by rfl⟩ : syracuseStep 1636795 = 2455193) B2455193
theorem B2300345 : Blo 1532463 2300345 := bstep (se 2 (by rfl) ⟨862629, by rfl⟩ : syracuseStep 2300345 = 1725259) B1725259
theorem B11057593 : Blo 1532463 11057593 := bstep (se 2 (by rfl) ⟨4146597, by rfl⟩ : syracuseStep 11057593 = 8293195) B8293195
theorem B2300423 : Blo 1532463 2300423 := bstep (se 1 (by rfl) ⟨1725317, by rfl⟩ : syracuseStep 2300423 = 3450635) B3450635
theorem B2300459 : Blo 1532463 2300459 := bstep (se 1 (by rfl) ⟨1725344, by rfl⟩ : syracuseStep 2300459 = 3450689) B3450689
theorem B2300489 : Blo 1532463 2300489 := bstep (se 2 (by rfl) ⟨862683, by rfl⟩ : syracuseStep 2300489 = 1725367) B1725367
theorem B1841783 : Blo 1532463 1841783 := bstep (se 1 (by rfl) ⟨1381337, by rfl⟩ : syracuseStep 1841783 = 2762675) B2762675
theorem B3881591 : Blo 1532463 3881591 := bstep (se 1 (by rfl) ⟨2911193, by rfl⟩ : syracuseStep 3881591 = 5822387) B5822387
theorem B2456249 : Blo 1532463 2456249 := bstep (se 2 (by rfl) ⟨921093, by rfl⟩ : syracuseStep 2456249 = 1842187) B1842187
theorem B2300603 : Blo 1532463 2300603 := bstep (se 1 (by rfl) ⟨1725452, by rfl⟩ : syracuseStep 2300603 = 3450905) B3450905
theorem B8854217 : Blo 1532463 8854217 := bstep (se 2 (by rfl) ⟨3320331, by rfl⟩ : syracuseStep 8854217 = 6640663) B6640663
theorem B2300663 : Blo 1532463 2300663 := bstep (se 1 (by rfl) ⟨1725497, by rfl⟩ : syracuseStep 2300663 = 3450995) B3450995
theorem B2300687 : Blo 1532463 2300687 := bstep (se 1 (by rfl) ⟨1725515, by rfl⟩ : syracuseStep 2300687 = 3451031) B3451031
theorem B2300729 : Blo 1532463 2300729 := bstep (se 2 (by rfl) ⟨862773, by rfl⟩ : syracuseStep 2300729 = 1725547) B1725547
theorem B2587511 : Blo 1532463 2587511 := bstep (se 1 (by rfl) ⟨1940633, by rfl⟩ : syracuseStep 2587511 = 3881267) B3881267
theorem B2300807 : Blo 1532463 2300807 := bstep (se 1 (by rfl) ⟨1725605, by rfl⟩ : syracuseStep 2300807 = 3451211) B3451211
theorem B2300843 : Blo 1532463 2300843 := bstep (se 1 (by rfl) ⟨1725632, by rfl⟩ : syracuseStep 2300843 = 3451265) B3451265
theorem B9321401 : Blo 1532463 9321401 := bstep (se 2 (by rfl) ⟨3495525, by rfl⟩ : syracuseStep 9321401 = 6991051) B6991051
theorem B2300873 : Blo 1532463 2300873 := bstep (se 2 (by rfl) ⟨862827, by rfl⟩ : syracuseStep 2300873 = 1725655) B1725655
theorem B26213381 : Blo 1532463 26213381 := bstep (se 4 (by rfl) ⟨2457504, by rfl⟩ : syracuseStep 26213381 = 4915009) B4915009
theorem B5176331 : Blo 1532463 5176331 := bstep (se 1 (by rfl) ⟨3882248, by rfl⟩ : syracuseStep 5176331 = 7764497) B7764497
theorem B3275819 : Blo 1532463 3275819 := bstep (se 1 (by rfl) ⟨2456864, by rfl⟩ : syracuseStep 3275819 = 4913729) B4913729
theorem B2300987 : Blo 1532463 2300987 := bstep (se 1 (by rfl) ⟨1725740, by rfl⟩ : syracuseStep 2300987 = 3451481) B3451481
theorem B5176439 : Blo 1532463 5176439 := bstep (se 1 (by rfl) ⟨3882329, by rfl⟩ : syracuseStep 5176439 = 7764659) B7764659
theorem B5528695 : Blo 1532463 5528695 := bstep (se 1 (by rfl) ⟨4146521, by rfl⟩ : syracuseStep 5528695 = 8293043) B8293043
theorem B2301047 : Blo 1532463 2301047 := bstep (se 1 (by rfl) ⟨1725785, by rfl⟩ : syracuseStep 2301047 = 3451571) B3451571
theorem B2301071 : Blo 1532463 2301071 := bstep (se 1 (by rfl) ⟨1725803, by rfl⟩ : syracuseStep 2301071 = 3451607) B3451607
theorem B62979221 : Blo 1532463 62979221 := bstep (se 6 (by rfl) ⟨1476075, by rfl⟩ : syracuseStep 62979221 = 2952151) B2952151
theorem B2301113 : Blo 1532463 2301113 := bstep (se 2 (by rfl) ⟨862917, by rfl⟩ : syracuseStep 2301113 = 1725835) B1725835
theorem B13098185 : Blo 1532463 13098185 := bstep (se 2 (by rfl) ⟨4911819, by rfl⟩ : syracuseStep 13098185 = 9823639) B9823639
theorem B2301191 : Blo 1532463 2301191 := bstep (se 1 (by rfl) ⟨1725893, by rfl⟩ : syracuseStep 2301191 = 3451787) B3451787
theorem B3448079 : Blo 1532463 3448079 := bstep (se 1 (by rfl) ⟨2586059, by rfl⟩ : syracuseStep 3448079 = 5172119) B5172119
theorem B3448097 : Blo 1532463 3448097 := bstep (se 2 (by rfl) ⟨1293036, by rfl⟩ : syracuseStep 3448097 = 2586073) B2586073
theorem B2301227 : Blo 1532463 2301227 := bstep (se 1 (by rfl) ⟨1725920, by rfl⟩ : syracuseStep 2301227 = 3451841) B3451841
theorem B2587963 : Blo 1532463 2587963 := bstep (se 1 (by rfl) ⟨1940972, by rfl⟩ : syracuseStep 2587963 = 3881945) B3881945
theorem B7765307 : Blo 1532463 7765307 := bstep (se 1 (by rfl) ⟨5823980, by rfl⟩ : syracuseStep 7765307 = 11647961) B11647961
theorem B2301257 : Blo 1532463 2301257 := bstep (se 2 (by rfl) ⟨862971, by rfl⟩ : syracuseStep 2301257 = 1725943) B1725943
theorem B5823859 : Blo 1532463 5823859 := bstep (se 1 (by rfl) ⟨4367894, by rfl⟩ : syracuseStep 5823859 = 8735789) B8735789
theorem B3685817 : Blo 1532463 3685817 := bstep (se 2 (by rfl) ⟨1382181, by rfl⟩ : syracuseStep 3685817 = 2764363) B2764363
theorem B2301371 : Blo 1532463 2301371 := bstep (se 1 (by rfl) ⟨1726028, by rfl⟩ : syracuseStep 2301371 = 3452057) B3452057
theorem B2588105 : Blo 1532463 2588105 := bstep (se 2 (by rfl) ⟨970539, by rfl⟩ : syracuseStep 2588105 = 1941079) B1941079
theorem B7765469 : Blo 1532463 7765469 := bstep (se 3 (by rfl) ⟨1456025, by rfl⟩ : syracuseStep 7765469 = 2912051) B2912051
theorem B2301431 : Blo 1532463 2301431 := bstep (se 1 (by rfl) ⟨1726073, by rfl⟩ : syracuseStep 2301431 = 3452147) B3452147
theorem B2301455 : Blo 1532463 2301455 := bstep (se 1 (by rfl) ⟨1726091, by rfl⟩ : syracuseStep 2301455 = 3452183) B3452183
theorem B2301497 : Blo 1532463 2301497 := bstep (se 2 (by rfl) ⟨863061, by rfl⟩ : syracuseStep 2301497 = 1726123) B1726123
theorem B3448439 : Blo 1532463 3448439 := bstep (se 1 (by rfl) ⟨2586329, by rfl⟩ : syracuseStep 3448439 = 5172659) B5172659
theorem B7872119 : Blo 1532463 7872119 := bstep (se 1 (by rfl) ⟨5904089, by rfl⟩ : syracuseStep 7872119 = 11808179) B11808179
theorem B2301575 : Blo 1532463 2301575 := bstep (se 1 (by rfl) ⟨1726181, by rfl⟩ : syracuseStep 2301575 = 3452363) B3452363
theorem B4365971 : Blo 1532463 4365971 := bstep (se 1 (by rfl) ⟨3274478, by rfl⟩ : syracuseStep 4365971 = 6548957) B6548957
theorem B2301611 : Blo 1532463 2301611 := bstep (se 1 (by rfl) ⟨1726208, by rfl⟩ : syracuseStep 2301611 = 3452417) B3452417
theorem B5177033 : Blo 1532463 5177033 := bstep (se 2 (by rfl) ⟨1941387, by rfl⟩ : syracuseStep 5177033 = 3882775) B3882775
theorem B2301641 : Blo 1532463 2301641 := bstep (se 2 (by rfl) ⟨863115, by rfl⟩ : syracuseStep 2301641 = 1726231) B1726231
theorem B15728357 : Blo 1532463 15728357 := bstep (se 4 (by rfl) ⟨1474533, by rfl⟩ : syracuseStep 15728357 = 2949067) B2949067
theorem B7765793 : Blo 1532463 7765793 := bstep (se 2 (by rfl) ⟨2912172, by rfl⟩ : syracuseStep 7765793 = 5824345) B5824345
theorem B3448619 : Blo 1532463 3448619 := bstep (se 1 (by rfl) ⟨2586464, by rfl⟩ : syracuseStep 3448619 = 5172929) B5172929
theorem B14729035 : Blo 1532463 14729035 := bstep (se 1 (by rfl) ⟨11046776, by rfl⟩ : syracuseStep 14729035 = 22093553) B22093553
theorem B3882887 : Blo 1532463 3882887 := bstep (se 1 (by rfl) ⟨2912165, by rfl⟩ : syracuseStep 3882887 = 5824331) B5824331
theorem B3882937 : Blo 1532463 3882937 := bstep (se 2 (by rfl) ⟨1456101, by rfl⟩ : syracuseStep 3882937 = 2912203) B2912203
theorem B11198411 : Blo 1532463 11198411 := bstep (se 1 (by rfl) ⟨8398808, by rfl⟩ : syracuseStep 11198411 = 16797617) B16797617
theorem B9961487 : Blo 1532463 9961487 := bstep (se 1 (by rfl) ⟨7471115, by rfl⟩ : syracuseStep 9961487 = 14942231) B14942231
theorem B9830429 : Blo 1532463 9830429 := bstep (se 3 (by rfl) ⟨1843205, by rfl⟩ : syracuseStep 9830429 = 3686411) B3686411
theorem B3448889 : Blo 1532463 3448889 := bstep (se 2 (by rfl) ⟨1293333, by rfl⟩ : syracuseStep 3448889 = 2586667) B2586667
theorem B2589023 : Blo 1532463 2589023 := bstep (se 1 (by rfl) ⟨1941767, by rfl⟩ : syracuseStep 2589023 = 3883535) B3883535
theorem B3449231 : Blo 1532463 3449231 := bstep (se 1 (by rfl) ⟨2586923, by rfl⟩ : syracuseStep 3449231 = 5173847) B5173847
theorem B4981235 : Blo 1532463 4981235 := bstep (se 1 (by rfl) ⟨3735926, by rfl⟩ : syracuseStep 4981235 = 7471853) B7471853
theorem B5177843 : Blo 1532463 5177843 := bstep (se 1 (by rfl) ⟨3883382, by rfl⟩ : syracuseStep 5177843 = 7766765) B7766765
theorem B5898761 : Blo 1532463 5898761 := bstep (se 2 (by rfl) ⟨2212035, by rfl⟩ : syracuseStep 5898761 = 4424071) B4424071
theorem B1532495 : Blo 1532463 1532495 := bstep (se 1 (by rfl) ⟨1149371, by rfl⟩ : syracuseStep 1532495 = 2298743) B2298743
theorem B1532511 : Blo 1532463 1532511 := bstep (se 1 (by rfl) ⟨1149383, by rfl⟩ : syracuseStep 1532511 = 2298767) B2298767
theorem B1532539 : Blo 1532463 1532539 := bstep (se 1 (by rfl) ⟨1149404, by rfl⟩ : syracuseStep 1532539 = 2298809) B2298809
theorem B1532591 : Blo 1532463 1532591 := bstep (se 1 (by rfl) ⟨1149443, by rfl⟩ : syracuseStep 1532591 = 2298887) B2298887
theorem B1532615 : Blo 1532463 1532615 := bstep (se 1 (by rfl) ⟨1149461, by rfl⟩ : syracuseStep 1532615 = 2298923) B2298923
theorem B3449555 : Blo 1532463 3449555 := bstep (se 1 (by rfl) ⟨2587166, by rfl⟩ : syracuseStep 3449555 = 5174333) B5174333
theorem B1532635 : Blo 1532463 1532635 := bstep (se 1 (by rfl) ⟨1149476, by rfl⟩ : syracuseStep 1532635 = 2298953) B2298953
theorem B1532711 : Blo 1532463 1532711 := bstep (se 1 (by rfl) ⟨1149533, by rfl⟩ : syracuseStep 1532711 = 2299067) B2299067
theorem B7758665 : Blo 1532463 7758665 := bstep (se 2 (by rfl) ⟨2909499, by rfl⟩ : syracuseStep 7758665 = 5818999) B5818999
theorem B1532751 : Blo 1532463 1532751 := bstep (se 1 (by rfl) ⟨1149563, by rfl⟩ : syracuseStep 1532751 = 2299127) B2299127
theorem B1532767 : Blo 1532463 1532767 := bstep (se 1 (by rfl) ⟨1149575, by rfl⟩ : syracuseStep 1532767 = 2299151) B2299151
theorem B1532795 : Blo 1532463 1532795 := bstep (se 1 (by rfl) ⟨1149596, by rfl⟩ : syracuseStep 1532795 = 2299193) B2299193
theorem B1532847 : Blo 1532463 1532847 := bstep (se 1 (by rfl) ⟨1149635, by rfl⟩ : syracuseStep 1532847 = 2299271) B2299271
theorem B24871855 : Blo 1532463 24871855 := bstep (se 1 (by rfl) ⟨18653891, by rfl⟩ : syracuseStep 24871855 = 37307783) B37307783
theorem B6546359 : Blo 1532463 6546359 := bstep (se 1 (by rfl) ⟨4909769, by rfl⟩ : syracuseStep 6546359 = 9819539) B9819539
theorem B1532871 : Blo 1532463 1532871 := bstep (se 1 (by rfl) ⟨1149653, by rfl⟩ : syracuseStep 1532871 = 2299307) B2299307
theorem B1532891 : Blo 1532463 1532891 := bstep (se 1 (by rfl) ⟨1149668, by rfl⟩ : syracuseStep 1532891 = 2299337) B2299337
theorem B5178383 : Blo 1532463 5178383 := bstep (se 1 (by rfl) ⟨3883787, by rfl⟩ : syracuseStep 5178383 = 7767575) B7767575
theorem B3884051 : Blo 1532463 3884051 := bstep (se 1 (by rfl) ⟨2913038, by rfl⟩ : syracuseStep 3884051 = 5826077) B5826077
theorem B1532967 : Blo 1532463 1532967 := bstep (se 1 (by rfl) ⟨1149725, by rfl⟩ : syracuseStep 1532967 = 2299451) B2299451
theorem B44205101 : Blo 1532463 44205101 := bstep (se 3 (by rfl) ⟨8288456, by rfl⟩ : syracuseStep 44205101 = 16576913) B16576913
theorem B6546511 : Blo 1532463 6546511 := bstep (se 1 (by rfl) ⟨4909883, by rfl⟩ : syracuseStep 6546511 = 9819767) B9819767
theorem B1533007 : Blo 1532463 1533007 := bstep (se 1 (by rfl) ⟨1149755, by rfl⟩ : syracuseStep 1533007 = 2299511) B2299511
theorem B1533023 : Blo 1532463 1533023 := bstep (se 1 (by rfl) ⟨1149767, by rfl⟩ : syracuseStep 1533023 = 2299535) B2299535
theorem B1533051 : Blo 1532463 1533051 := bstep (se 1 (by rfl) ⟨1149788, by rfl⟩ : syracuseStep 1533051 = 2299577) B2299577
theorem B1533103 : Blo 1532463 1533103 := bstep (se 1 (by rfl) ⟨1149827, by rfl⟩ : syracuseStep 1533103 = 2299655) B2299655
theorem B1533127 : Blo 1532463 1533127 := bstep (se 1 (by rfl) ⟨1149845, by rfl⟩ : syracuseStep 1533127 = 2299691) B2299691
theorem B1533147 : Blo 1532463 1533147 := bstep (se 1 (by rfl) ⟨1149860, by rfl⟩ : syracuseStep 1533147 = 2299721) B2299721
theorem B28345589 : Blo 1532463 28345589 := bstep (se 5 (by rfl) ⟨1328699, by rfl⟩ : syracuseStep 28345589 = 2657399) B2657399
theorem B19645685 : Blo 1532463 19645685 := bstep (se 5 (by rfl) ⟨920891, by rfl⟩ : syracuseStep 19645685 = 1841783) B1841783
theorem B5825803 : Blo 1532463 5825803 := bstep (se 1 (by rfl) ⟨4369352, by rfl⟩ : syracuseStep 5825803 = 8738705) B8738705
theorem B1533223 : Blo 1532463 1533223 := bstep (se 1 (by rfl) ⟨1149917, by rfl⟩ : syracuseStep 1533223 = 2299835) B2299835
theorem B1533263 : Blo 1532463 1533263 := bstep (se 1 (by rfl) ⟨1149947, by rfl⟩ : syracuseStep 1533263 = 2299895) B2299895
theorem B11199833 : Blo 1532463 11199833 := bstep (se 2 (by rfl) ⟨4199937, by rfl⟩ : syracuseStep 11199833 = 8399875) B8399875
theorem B1533279 : Blo 1532463 1533279 := bstep (se 1 (by rfl) ⟨1149959, by rfl⟩ : syracuseStep 1533279 = 2299919) B2299919
theorem B1533307 : Blo 1532463 1533307 := bstep (se 1 (by rfl) ⟨1149980, by rfl⟩ : syracuseStep 1533307 = 2299961) B2299961
theorem B9332111 : Blo 1532463 9332111 := bstep (se 1 (by rfl) ⟨6999083, by rfl⟩ : syracuseStep 9332111 = 13998167) B13998167
theorem B1533359 : Blo 1532463 1533359 := bstep (se 1 (by rfl) ⟨1150019, by rfl⟩ : syracuseStep 1533359 = 2300039) B2300039
theorem B1533383 : Blo 1532463 1533383 := bstep (se 1 (by rfl) ⟨1150037, by rfl⟩ : syracuseStep 1533383 = 2300075) B2300075
theorem B18703817 : Blo 1532463 18703817 := bstep (se 2 (by rfl) ⟨7013931, by rfl⟩ : syracuseStep 18703817 = 14027863) B14027863
theorem B1533403 : Blo 1532463 1533403 := bstep (se 1 (by rfl) ⟨1150052, by rfl⟩ : syracuseStep 1533403 = 2300105) B2300105
theorem B6301223 : Blo 1532463 6301223 := bstep (se 1 (by rfl) ⟨4725917, by rfl⟩ : syracuseStep 6301223 = 9451835) B9451835
theorem B1533479 : Blo 1532463 1533479 := bstep (se 1 (by rfl) ⟨1150109, by rfl⟩ : syracuseStep 1533479 = 2300219) B2300219
theorem B5826107 : Blo 1532463 5826107 := bstep (se 1 (by rfl) ⟨4369580, by rfl⟩ : syracuseStep 5826107 = 8739161) B8739161
theorem B1533519 : Blo 1532463 1533519 := bstep (se 1 (by rfl) ⟨1150139, by rfl⟩ : syracuseStep 1533519 = 2300279) B2300279
theorem B1533535 : Blo 1532463 1533535 := bstep (se 1 (by rfl) ⟨1150151, by rfl⟩ : syracuseStep 1533535 = 2300303) B2300303
theorem B2909819 : Blo 1532463 2909819 := bstep (se 1 (by rfl) ⟨2182364, by rfl⟩ : syracuseStep 2909819 = 4364729) B4364729
theorem B3450491 : Blo 1532463 3450491 := bstep (se 1 (by rfl) ⟨2587868, by rfl⟩ : syracuseStep 3450491 = 5175737) B5175737
theorem B1533563 : Blo 1532463 1533563 := bstep (se 1 (by rfl) ⟨1150172, by rfl⟩ : syracuseStep 1533563 = 2300345) B2300345
theorem B8734331 : Blo 1532463 8734331 := bstep (se 1 (by rfl) ⟨6550748, by rfl⟩ : syracuseStep 8734331 = 13101497) B13101497
theorem B1533615 : Blo 1532463 1533615 := bstep (se 1 (by rfl) ⟨1150211, by rfl⟩ : syracuseStep 1533615 = 2300423) B2300423
theorem B11806397 : Blo 1532463 11806397 := bstep (se 3 (by rfl) ⟨2213699, by rfl⟩ : syracuseStep 11806397 = 4427399) B4427399
theorem B1533639 : Blo 1532463 1533639 := bstep (se 1 (by rfl) ⟨1150229, by rfl⟩ : syracuseStep 1533639 = 2300459) B2300459
theorem B1533659 : Blo 1532463 1533659 := bstep (se 1 (by rfl) ⟨1150244, by rfl⟩ : syracuseStep 1533659 = 2300489) B2300489
theorem B3450617 : Blo 1532463 3450617 := bstep (se 2 (by rfl) ⟨1293981, by rfl⟩ : syracuseStep 3450617 = 2587963) B2587963
theorem B1533735 : Blo 1532463 1533735 := bstep (se 1 (by rfl) ⟨1150301, by rfl⟩ : syracuseStep 1533735 = 2300603) B2300603
theorem B1533775 : Blo 1532463 1533775 := bstep (se 1 (by rfl) ⟨1150331, by rfl⟩ : syracuseStep 1533775 = 2300663) B2300663
theorem B1533791 : Blo 1532463 1533791 := bstep (se 1 (by rfl) ⟨1150343, by rfl⟩ : syracuseStep 1533791 = 2300687) B2300687
theorem B1533819 : Blo 1532463 1533819 := bstep (se 1 (by rfl) ⟨1150364, by rfl⟩ : syracuseStep 1533819 = 2300729) B2300729
theorem B1533871 : Blo 1532463 1533871 := bstep (se 1 (by rfl) ⟨1150403, by rfl⟩ : syracuseStep 1533871 = 2300807) B2300807
theorem B1533895 : Blo 1532463 1533895 := bstep (se 1 (by rfl) ⟨1150421, by rfl⟩ : syracuseStep 1533895 = 2300843) B2300843
theorem B1533915 : Blo 1532463 1533915 := bstep (se 1 (by rfl) ⟨1150436, by rfl⟩ : syracuseStep 1533915 = 2300873) B2300873
theorem B14731267 : Blo 1532463 14731267 := bstep (se 1 (by rfl) ⟨11048450, by rfl⟩ : syracuseStep 14731267 = 22096901) B22096901
theorem B17475587 : Blo 1532463 17475587 := bstep (se 1 (by rfl) ⟨13106690, by rfl⟩ : syracuseStep 17475587 = 26213381) B26213381
theorem B3450887 : Blo 1532463 3450887 := bstep (se 1 (by rfl) ⟨2588165, by rfl⟩ : syracuseStep 3450887 = 5176331) B5176331
theorem B1533991 : Blo 1532463 1533991 := bstep (se 1 (by rfl) ⟨1150493, by rfl⟩ : syracuseStep 1533991 = 2300987) B2300987
theorem B3450959 : Blo 1532463 3450959 := bstep (se 1 (by rfl) ⟨2588219, by rfl⟩ : syracuseStep 3450959 = 5176439) B5176439
theorem B1534031 : Blo 1532463 1534031 := bstep (se 1 (by rfl) ⟨1150523, by rfl⟩ : syracuseStep 1534031 = 2301047) B2301047
theorem B7759961 : Blo 1532463 7759961 := bstep (se 2 (by rfl) ⟨2909985, by rfl⟩ : syracuseStep 7759961 = 5819971) B5819971
theorem B1534047 : Blo 1532463 1534047 := bstep (se 1 (by rfl) ⟨1150535, by rfl⟩ : syracuseStep 1534047 = 2301071) B2301071
theorem B2910305 : Blo 1532463 2910305 := bstep (se 2 (by rfl) ⟨1091364, by rfl⟩ : syracuseStep 2910305 = 2182729) B2182729
theorem B41986147 : Blo 1532463 41986147 := bstep (se 1 (by rfl) ⟨31489610, by rfl⟩ : syracuseStep 41986147 = 62979221) B62979221
theorem B1534075 : Blo 1532463 1534075 := bstep (se 1 (by rfl) ⟨1150556, by rfl⟩ : syracuseStep 1534075 = 2301113) B2301113
theorem B1534127 : Blo 1532463 1534127 := bstep (se 1 (by rfl) ⟨1150595, by rfl⟩ : syracuseStep 1534127 = 2301191) B2301191
theorem B1534151 : Blo 1532463 1534151 := bstep (se 1 (by rfl) ⟨1150613, by rfl⟩ : syracuseStep 1534151 = 2301227) B2301227
theorem B1534171 : Blo 1532463 1534171 := bstep (se 1 (by rfl) ⟨1150628, by rfl⟩ : syracuseStep 1534171 = 2301257) B2301257
theorem B1534247 : Blo 1532463 1534247 := bstep (se 1 (by rfl) ⟨1150685, by rfl⟩ : syracuseStep 1534247 = 2301371) B2301371
theorem B1534287 : Blo 1532463 1534287 := bstep (se 1 (by rfl) ⟨1150715, by rfl⟩ : syracuseStep 1534287 = 2301431) B2301431
theorem B1534303 : Blo 1532463 1534303 := bstep (se 1 (by rfl) ⟨1150727, by rfl⟩ : syracuseStep 1534303 = 2301455) B2301455
theorem B1534331 : Blo 1532463 1534331 := bstep (se 1 (by rfl) ⟨1150748, by rfl⟩ : syracuseStep 1534331 = 2301497) B2301497
theorem B1534383 : Blo 1532463 1534383 := bstep (se 1 (by rfl) ⟨1150787, by rfl⟩ : syracuseStep 1534383 = 2301575) B2301575
theorem B2910647 : Blo 1532463 2910647 := bstep (se 1 (by rfl) ⟨2182985, by rfl⟩ : syracuseStep 2910647 = 4365971) B4365971
theorem B19638713 : Blo 1532463 19638713 := bstep (se 2 (by rfl) ⟨7364517, by rfl⟩ : syracuseStep 19638713 = 14729035) B14729035
theorem B1534407 : Blo 1532463 1534407 := bstep (se 1 (by rfl) ⟨1150805, by rfl⟩ : syracuseStep 1534407 = 2301611) B2301611
theorem B3451355 : Blo 1532463 3451355 := bstep (se 1 (by rfl) ⟨2588516, by rfl⟩ : syracuseStep 3451355 = 5177033) B5177033
theorem B1534427 : Blo 1532463 1534427 := bstep (se 1 (by rfl) ⟨1150820, by rfl⟩ : syracuseStep 1534427 = 2301641) B2301641
theorem B2214479 : Blo 1532463 2214479 := bstep (se 1 (by rfl) ⟨1660859, by rfl⟩ : syracuseStep 2214479 = 3321719) B3321719
theorem B7465607 : Blo 1532463 7465607 := bstep (se 1 (by rfl) ⟨5599205, by rfl⟩ : syracuseStep 7465607 = 11198411) B11198411
theorem B2911049 : Blo 1532463 2911049 := bstep (se 2 (by rfl) ⟨1091643, by rfl⟩ : syracuseStep 2911049 = 2183287) B2183287
theorem B4426591 : Blo 1532463 4426591 := bstep (se 1 (by rfl) ⟨3319943, by rfl⟩ : syracuseStep 4426591 = 6639887) B6639887
theorem B3451823 : Blo 1532463 3451823 := bstep (se 1 (by rfl) ⟨2588867, by rfl⟩ : syracuseStep 3451823 = 5177735) B5177735
theorem B5172281 : Blo 1532463 5172281 := bstep (se 2 (by rfl) ⟨1939605, by rfl⟩ : syracuseStep 5172281 = 3879211) B3879211
theorem B5819471 : Blo 1532463 5819471 := bstep (se 1 (by rfl) ⟨4364603, by rfl⟩ : syracuseStep 5819471 = 8729207) B8729207
theorem B3452075 : Blo 1532463 3452075 := bstep (se 1 (by rfl) ⟨2589056, by rfl⟩ : syracuseStep 3452075 = 5178113) B5178113
theorem B5393579 : Blo 1532463 5393579 := bstep (se 1 (by rfl) ⟨4045184, by rfl⟩ : syracuseStep 5393579 = 8090369) B8090369
theorem B2182393 : Blo 1532463 2182393 := bstep (se 2 (by rfl) ⟨818397, by rfl⟩ : syracuseStep 2182393 = 1636795) B1636795
theorem B39300389 : Blo 1532463 39300389 := bstep (se 4 (by rfl) ⟨3684411, by rfl⟩ : syracuseStep 39300389 = 7368823) B7368823
theorem B5172605 : Blo 1532463 5172605 := bstep (se 3 (by rfl) ⟨969863, by rfl⟩ : syracuseStep 5172605 = 1939727) B1939727
theorem B2911763 : Blo 1532463 2911763 := bstep (se 1 (by rfl) ⟨2183822, by rfl⟩ : syracuseStep 2911763 = 4367645) B4367645
theorem B2911801 : Blo 1532463 2911801 := bstep (se 2 (by rfl) ⟨1091925, by rfl⟩ : syracuseStep 2911801 = 2183851) B2183851
theorem B5172875 : Blo 1532463 5172875 := bstep (se 1 (by rfl) ⟨3879656, by rfl⟩ : syracuseStep 5172875 = 7759313) B7759313
theorem B95768243 : Blo 1532463 95768243 := bstep (se 1 (by rfl) ⟨71826182, by rfl⟩ : syracuseStep 95768243 = 143652365) B143652365
theorem B4910807 : Blo 1532463 4910807 := bstep (se 1 (by rfl) ⟨3683105, by rfl⟩ : syracuseStep 4910807 = 7366211) B7366211
theorem B2764535 : Blo 1532463 2764535 := bstep (se 1 (by rfl) ⟨2073401, by rfl⟩ : syracuseStep 2764535 = 4146803) B4146803
theorem B2330473 : Blo 1532463 2330473 := bstep (se 2 (by rfl) ⟨873927, by rfl⟩ : syracuseStep 2330473 = 1747855) B1747855
theorem B2912105 : Blo 1532463 2912105 := bstep (se 2 (by rfl) ⟨1092039, by rfl⟩ : syracuseStep 2912105 = 2184079) B2184079
theorem B2764651 : Blo 1532463 2764651 := bstep (se 1 (by rfl) ⟨2073488, by rfl⟩ : syracuseStep 2764651 = 4146977) B4146977
theorem B2764687 : Blo 1532463 2764687 := bstep (se 1 (by rfl) ⟨2073515, by rfl⟩ : syracuseStep 2764687 = 4147031) B4147031
theorem B1724539 : Blo 1532463 1724539 := bstep (se 1 (by rfl) ⟨1293404, by rfl⟩ : syracuseStep 1724539 = 2586809) B2586809
theorem B5902811 : Blo 1532463 5902811 := bstep (se 1 (by rfl) ⟨4427108, by rfl⟩ : syracuseStep 5902811 = 8854217) B8854217
theorem B6549997 : Blo 1532463 6549997 := bstep (se 3 (by rfl) ⟨1228124, by rfl⟩ : syracuseStep 6549997 = 2456249) B2456249
theorem B5173793 : Blo 1532463 5173793 := bstep (se 2 (by rfl) ⟨1940172, by rfl⟩ : syracuseStep 5173793 = 3880345) B3880345
theorem B1725007 : Blo 1532463 1725007 := bstep (se 1 (by rfl) ⟨1293755, by rfl⟩ : syracuseStep 1725007 = 2587511) B2587511
theorem B6214267 : Blo 1532463 6214267 := bstep (se 1 (by rfl) ⟨4660700, by rfl⟩ : syracuseStep 6214267 = 9321401) B9321401
theorem B2183879 : Blo 1532463 2183879 := bstep (se 1 (by rfl) ⟨1637909, by rfl⟩ : syracuseStep 2183879 = 3275819) B3275819
theorem B5174009 : Blo 1532463 5174009 := bstep (se 2 (by rfl) ⟨1940253, by rfl⟩ : syracuseStep 5174009 = 3880507) B3880507
theorem B2298719 : Blo 1532463 2298719 := bstep (se 1 (by rfl) ⟨1724039, by rfl⟩ : syracuseStep 2298719 = 3448079) B3448079
theorem B2298731 : Blo 1532463 2298731 := bstep (se 1 (by rfl) ⟨1724048, by rfl⟩ : syracuseStep 2298731 = 3448097) B3448097
theorem B1725403 : Blo 1532463 1725403 := bstep (se 1 (by rfl) ⟨1294052, by rfl⟩ : syracuseStep 1725403 = 2588105) B2588105
theorem B19928065 : Blo 1532463 19928065 := bstep (se 2 (by rfl) ⟨7473024, by rfl⟩ : syracuseStep 19928065 = 14946049) B14946049
theorem B5174279 : Blo 1532463 5174279 := bstep (se 1 (by rfl) ⟨3880709, by rfl⟩ : syracuseStep 5174279 = 7761419) B7761419
theorem B2298959 : Blo 1532463 2298959 := bstep (se 1 (by rfl) ⟨1724219, by rfl⟩ : syracuseStep 2298959 = 3448439) B3448439
theorem B5248079 : Blo 1532463 5248079 := bstep (se 1 (by rfl) ⟨3936059, by rfl⟩ : syracuseStep 5248079 = 7872119) B7872119
theorem B5174387 : Blo 1532463 5174387 := bstep (se 1 (by rfl) ⟨3880790, by rfl⟩ : syracuseStep 5174387 = 7761581) B7761581
theorem B2299079 : Blo 1532463 2299079 := bstep (se 1 (by rfl) ⟨1724309, by rfl⟩ : syracuseStep 2299079 = 3448619) B3448619
theorem B3880183 : Blo 1532463 3880183 := bstep (se 1 (by rfl) ⟨2910137, by rfl⟩ : syracuseStep 3880183 = 5820275) B5820275
theorem B2299241 : Blo 1532463 2299241 := bstep (se 2 (by rfl) ⟨862215, by rfl⟩ : syracuseStep 2299241 = 1724431) B1724431
theorem B5174657 : Blo 1532463 5174657 := bstep (se 2 (by rfl) ⟨1940496, by rfl⟩ : syracuseStep 5174657 = 3880993) B3880993
theorem B2020783 : Blo 1532463 2020783 := bstep (se 1 (by rfl) ⟨1515587, by rfl⟩ : syracuseStep 2020783 = 3031175) B3031175
theorem B1725871 : Blo 1532463 1725871 := bstep (se 1 (by rfl) ⟨1294403, by rfl⟩ : syracuseStep 1725871 = 2588807) B2588807
theorem B2299319 : Blo 1532463 2299319 := bstep (se 1 (by rfl) ⟨1724489, by rfl⟩ : syracuseStep 2299319 = 3448979) B3448979
theorem B2299355 : Blo 1532463 2299355 := bstep (se 1 (by rfl) ⟨1724516, by rfl⟩ : syracuseStep 2299355 = 3449033) B3449033
theorem B5821915 : Blo 1532463 5821915 := bstep (se 1 (by rfl) ⟨4366436, by rfl⟩ : syracuseStep 5821915 = 8732873) B8732873
theorem B3880457 : Blo 1532463 3880457 := bstep (se 2 (by rfl) ⟨1455171, by rfl⟩ : syracuseStep 3880457 = 2910343) B2910343
theorem B3880487 : Blo 1532463 3880487 := bstep (se 1 (by rfl) ⟨2910365, by rfl⟩ : syracuseStep 3880487 = 5820731) B5820731
theorem B11646503 : Blo 1532463 11646503 := bstep (se 1 (by rfl) ⟨8734877, by rfl⟩ : syracuseStep 11646503 = 17469755) B17469755
theorem B22099499 : Blo 1532463 22099499 := bstep (se 1 (by rfl) ⟨16574624, by rfl⟩ : syracuseStep 22099499 = 33149249) B33149249
theorem B22099553 : Blo 1532463 22099553 := bstep (se 2 (by rfl) ⟨8287332, by rfl⟩ : syracuseStep 22099553 = 16574665) B16574665
theorem B2586235 : Blo 1532463 2586235 := bstep (se 1 (by rfl) ⟨1939676, by rfl⟩ : syracuseStep 2586235 = 3879353) B3879353
theorem B5527369 : Blo 1532463 5527369 := bstep (se 2 (by rfl) ⟨2072763, by rfl⟩ : syracuseStep 5527369 = 4145527) B4145527
theorem B3880811 : Blo 1532463 3880811 := bstep (se 1 (by rfl) ⟨2910608, by rfl⟩ : syracuseStep 3880811 = 5821217) B5821217
theorem B14743457 : Blo 1532463 14743457 := bstep (se 2 (by rfl) ⟨5528796, by rfl⟩ : syracuseStep 14743457 = 11057593) B11057593
theorem B2299823 : Blo 1532463 2299823 := bstep (se 1 (by rfl) ⟨1724867, by rfl⟩ : syracuseStep 2299823 = 3449735) B3449735
theorem B12433337 : Blo 1532463 12433337 := bstep (se 2 (by rfl) ⟨4662501, by rfl⟩ : syracuseStep 12433337 = 9325003) B9325003
theorem B5248955 : Blo 1532463 5248955 := bstep (se 1 (by rfl) ⟨3936716, by rfl⟩ : syracuseStep 5248955 = 7873433) B7873433
theorem B3274759 : Blo 1532463 3274759 := bstep (se 1 (by rfl) ⟨2456069, by rfl⟩ : syracuseStep 3274759 = 4912139) B4912139
theorem B2299913 : Blo 1532463 2299913 := bstep (se 2 (by rfl) ⟨862467, by rfl⟩ : syracuseStep 2299913 = 1724935) B1724935
theorem B6993935 : Blo 1532463 6993935 := bstep (se 1 (by rfl) ⟨5245451, by rfl⟩ : syracuseStep 6993935 = 10490903) B10490903
theorem B2299943 : Blo 1532463 2299943 := bstep (se 1 (by rfl) ⟨1724957, by rfl⟩ : syracuseStep 2299943 = 3449915) B3449915
theorem B11204723 : Blo 1532463 11204723 := bstep (se 1 (by rfl) ⟨8403542, by rfl⟩ : syracuseStep 11204723 = 16807085) B16807085
theorem B2300027 : Blo 1532463 2300027 := bstep (se 1 (by rfl) ⟨1725020, by rfl⟩ : syracuseStep 2300027 = 3450041) B3450041
theorem B5175467 : Blo 1532463 5175467 := bstep (se 1 (by rfl) ⟨3881600, by rfl⟩ : syracuseStep 5175467 = 7763201) B7763201
theorem B2300153 : Blo 1532463 2300153 := bstep (se 2 (by rfl) ⟨862557, by rfl⟩ : syracuseStep 2300153 = 1725115) B1725115
theorem B11802941 : Blo 1532463 11802941 := bstep (se 3 (by rfl) ⟨2213051, by rfl⟩ : syracuseStep 11802941 = 4426103) B4426103
theorem B2300255 : Blo 1532463 2300255 := bstep (se 1 (by rfl) ⟨1725191, by rfl⟩ : syracuseStep 2300255 = 3450383) B3450383
theorem B2300267 : Blo 1532463 2300267 := bstep (se 1 (by rfl) ⟨1725200, by rfl⟩ : syracuseStep 2300267 = 3450401) B3450401
theorem B2587099 : Blo 1532463 2587099 := bstep (se 1 (by rfl) ⟨1940324, by rfl⟩ : syracuseStep 2587099 = 3880649) B3880649
theorem B3881459 : Blo 1532463 3881459 := bstep (se 1 (by rfl) ⟨2911094, by rfl⟩ : syracuseStep 3881459 = 5822189) B5822189
theorem B2300495 : Blo 1532463 2300495 := bstep (se 1 (by rfl) ⟨1725371, by rfl⟩ : syracuseStep 2300495 = 3450743) B3450743
theorem B17947271 : Blo 1532463 17947271 := bstep (se 1 (by rfl) ⟨13460453, by rfl⟩ : syracuseStep 17947271 = 26920907) B26920907
theorem B5823161 : Blo 1532463 5823161 := bstep (se 2 (by rfl) ⟨2183685, by rfl⟩ : syracuseStep 5823161 = 4367371) B4367371
theorem B11057849 : Blo 1532463 11057849 := bstep (se 2 (by rfl) ⟨4146693, by rfl⟩ : syracuseStep 11057849 = 8293387) B8293387
theorem B5176007 : Blo 1532463 5176007 := bstep (se 1 (by rfl) ⟨3882005, by rfl⟩ : syracuseStep 5176007 = 7764011) B7764011
theorem B2300615 : Blo 1532463 2300615 := bstep (se 1 (by rfl) ⟨1725461, by rfl⟩ : syracuseStep 2300615 = 3450923) B3450923
theorem B7092947 : Blo 1532463 7092947 := bstep (se 1 (by rfl) ⟨5319710, by rfl⟩ : syracuseStep 7092947 = 10639421) B10639421
theorem B5823191 : Blo 1532463 5823191 := bstep (se 1 (by rfl) ⟨4367393, by rfl⟩ : syracuseStep 5823191 = 8734787) B8734787
theorem B7371593 : Blo 1532463 7371593 := bstep (se 2 (by rfl) ⟨2764347, by rfl⟩ : syracuseStep 7371593 = 5528695) B5528695
theorem B2300777 : Blo 1532463 2300777 := bstep (se 2 (by rfl) ⟨862791, by rfl⟩ : syracuseStep 2300777 = 1725583) B1725583
theorem B11639699 : Blo 1532463 11639699 := bstep (se 1 (by rfl) ⟨8729774, by rfl⟩ : syracuseStep 11639699 = 17459549) B17459549
theorem B16579511 : Blo 1532463 16579511 := bstep (se 1 (by rfl) ⟨12434633, by rfl⟩ : syracuseStep 16579511 = 24869267) B24869267
theorem B2300855 : Blo 1532463 2300855 := bstep (se 1 (by rfl) ⟨1725641, by rfl⟩ : syracuseStep 2300855 = 3451283) B3451283
theorem B3881915 : Blo 1532463 3881915 := bstep (se 1 (by rfl) ⟨2911436, by rfl⟩ : syracuseStep 3881915 = 5822873) B5822873
theorem B2300891 : Blo 1532463 2300891 := bstep (se 1 (by rfl) ⟨1725668, by rfl⟩ : syracuseStep 2300891 = 3451337) B3451337
theorem B12442675 : Blo 1532463 12442675 := bstep (se 1 (by rfl) ⟨9332006, by rfl⟩ : syracuseStep 12442675 = 18664013) B18664013
theorem B2587727 : Blo 1532463 2587727 := bstep (se 1 (by rfl) ⟨1940795, by rfl⟩ : syracuseStep 2587727 = 3881591) B3881591
theorem B7765145 : Blo 1532463 7765145 := bstep (se 2 (by rfl) ⟨2911929, by rfl⟩ : syracuseStep 7765145 = 5823859) B5823859
theorem B3448169 : Blo 1532463 3448169 := bstep (se 2 (by rfl) ⟨1293063, by rfl⟩ : syracuseStep 3448169 = 2586127) B2586127
theorem B6733181 : Blo 1532463 6733181 := bstep (se 3 (by rfl) ⟨1262471, by rfl⟩ : syracuseStep 6733181 = 2524943) B2524943
theorem B4365697 : Blo 1532463 4365697 := bstep (se 2 (by rfl) ⟨1637136, by rfl⟩ : syracuseStep 4365697 = 3274273) B3274273
theorem B2301359 : Blo 1532463 2301359 := bstep (se 1 (by rfl) ⟨1726019, by rfl⟩ : syracuseStep 2301359 = 3452039) B3452039
theorem B8732123 : Blo 1532463 8732123 := bstep (se 1 (by rfl) ⟨6549092, by rfl⟩ : syracuseStep 8732123 = 13098185) B13098185
theorem B2301449 : Blo 1532463 2301449 := bstep (se 2 (by rfl) ⟨863043, by rfl⟩ : syracuseStep 2301449 = 1726087) B1726087
theorem B7364135 : Blo 1532463 7364135 := bstep (se 1 (by rfl) ⟨5523101, by rfl⟩ : syracuseStep 7364135 = 11046203) B11046203
theorem B5176871 : Blo 1532463 5176871 := bstep (se 1 (by rfl) ⟨3882653, by rfl⟩ : syracuseStep 5176871 = 7765307) B7765307
theorem B2301479 : Blo 1532463 2301479 := bstep (se 1 (by rfl) ⟨1726109, by rfl⟩ : syracuseStep 2301479 = 3452219) B3452219
theorem B3882593 : Blo 1532463 3882593 := bstep (se 2 (by rfl) ⟨1455972, by rfl⟩ : syracuseStep 3882593 = 2911945) B2911945
theorem B2457211 : Blo 1532463 2457211 := bstep (se 1 (by rfl) ⟨1842908, by rfl⟩ : syracuseStep 2457211 = 3685817) B3685817
theorem B2301563 : Blo 1532463 2301563 := bstep (se 1 (by rfl) ⟨1726172, by rfl⟩ : syracuseStep 2301563 = 3452345) B3452345
theorem B5176979 : Blo 1532463 5176979 := bstep (se 1 (by rfl) ⟨3882734, by rfl⟩ : syracuseStep 5176979 = 7765469) B7765469
theorem B2301689 : Blo 1532463 2301689 := bstep (se 2 (by rfl) ⟨863133, by rfl⟩ : syracuseStep 2301689 = 1726267) B1726267
theorem B10485571 : Blo 1532463 10485571 := bstep (se 1 (by rfl) ⟨7864178, by rfl⟩ : syracuseStep 10485571 = 15728357) B15728357
theorem B11640671 : Blo 1532463 11640671 := bstep (se 1 (by rfl) ⟨8730503, by rfl⟩ : syracuseStep 11640671 = 17461007) B17461007
theorem B4366187 : Blo 1532463 4366187 := bstep (se 1 (by rfl) ⟨3274640, by rfl⟩ : syracuseStep 4366187 = 6549281) B6549281
theorem B5177195 : Blo 1532463 5177195 := bstep (se 1 (by rfl) ⟨3882896, by rfl⟩ : syracuseStep 5177195 = 7765793) B7765793
theorem B5177249 : Blo 1532463 5177249 := bstep (se 2 (by rfl) ⟨1941468, by rfl⟩ : syracuseStep 5177249 = 3882937) B3882937
theorem B2588591 : Blo 1532463 2588591 := bstep (se 1 (by rfl) ⟨1941443, by rfl⟩ : syracuseStep 2588591 = 3882887) B3882887
theorem B3448763 : Blo 1532463 3448763 := bstep (se 1 (by rfl) ⟨2586572, by rfl⟩ : syracuseStep 3448763 = 5173145) B5173145
theorem B6553619 : Blo 1532463 6553619 := bstep (se 1 (by rfl) ⟨4915214, by rfl⟩ : syracuseStep 6553619 = 9830429) B9830429
theorem B17465381 : Blo 1532463 17465381 := bstep (se 4 (by rfl) ⟨1637379, by rfl⟩ : syracuseStep 17465381 = 3274759) B3274759
theorem B3932507 : Blo 1532463 3932507 := bstep (se 1 (by rfl) ⟨2949380, by rfl⟩ : syracuseStep 3932507 = 5898761) B5898761
theorem B3449195 : Blo 1532463 3449195 := bstep (se 1 (by rfl) ⟨2586896, by rfl⟩ : syracuseStep 3449195 = 5173793) B5173793
theorem B3449339 : Blo 1532463 3449339 := bstep (se 1 (by rfl) ⟨2587004, by rfl⟩ : syracuseStep 3449339 = 5174009) B5174009
theorem B1532479 : Blo 1532463 1532479 := bstep (se 1 (by rfl) ⟨1149359, by rfl⟩ : syracuseStep 1532479 = 2298719) B2298719
theorem B1532487 : Blo 1532463 1532487 := bstep (se 1 (by rfl) ⟨1149365, by rfl⟩ : syracuseStep 1532487 = 2298731) B2298731
theorem B3449465 : Blo 1532463 3449465 := bstep (se 2 (by rfl) ⟨1293549, by rfl⟩ : syracuseStep 3449465 = 2587099) B2587099
theorem B8733329 : Blo 1532463 8733329 := bstep (se 2 (by rfl) ⟨3274998, by rfl⟩ : syracuseStep 8733329 = 6549997) B6549997
theorem B3449519 : Blo 1532463 3449519 := bstep (se 1 (by rfl) ⟨2587139, by rfl⟩ : syracuseStep 3449519 = 5174279) B5174279
theorem B2589367 : Blo 1532463 2589367 := bstep (se 1 (by rfl) ⟨1942025, by rfl⟩ : syracuseStep 2589367 = 3884051) B3884051
theorem B1532639 : Blo 1532463 1532639 := bstep (se 1 (by rfl) ⟨1149479, by rfl⟩ : syracuseStep 1532639 = 2298959) B2298959
theorem B3498719 : Blo 1532463 3498719 := bstep (se 1 (by rfl) ⟨2624039, by rfl⟩ : syracuseStep 3498719 = 5248079) B5248079
theorem B3449591 : Blo 1532463 3449591 := bstep (se 1 (by rfl) ⟨2587193, by rfl⟩ : syracuseStep 3449591 = 5174387) B5174387
theorem B1532719 : Blo 1532463 1532719 := bstep (se 1 (by rfl) ⟨1149539, by rfl⟩ : syracuseStep 1532719 = 2299079) B2299079
theorem B1532827 : Blo 1532463 1532827 := bstep (se 1 (by rfl) ⟨1149620, by rfl⟩ : syracuseStep 1532827 = 2299241) B2299241
theorem B3449771 : Blo 1532463 3449771 := bstep (se 1 (by rfl) ⟨2587328, by rfl⟩ : syracuseStep 3449771 = 5174657) B5174657
theorem B1532879 : Blo 1532463 1532879 := bstep (se 1 (by rfl) ⟨1149659, by rfl⟩ : syracuseStep 1532879 = 2299319) B2299319
theorem B12469211 : Blo 1532463 12469211 := bstep (se 1 (by rfl) ⟨9351908, by rfl⟩ : syracuseStep 12469211 = 18703817) B18703817
theorem B1532903 : Blo 1532463 1532903 := bstep (se 1 (by rfl) ⟨1149677, by rfl⟩ : syracuseStep 1532903 = 2299355) B2299355
theorem B3884071 : Blo 1532463 3884071 := bstep (se 1 (by rfl) ⟨2913053, by rfl⟩ : syracuseStep 3884071 = 5826107) B5826107
theorem B33162473 : Blo 1532463 33162473 := bstep (se 2 (by rfl) ⟨12435927, by rfl⟩ : syracuseStep 33162473 = 24871855) B24871855
theorem B1533215 : Blo 1532463 1533215 := bstep (se 1 (by rfl) ⟨1149911, by rfl⟩ : syracuseStep 1533215 = 2299823) B2299823
theorem B3499303 : Blo 1532463 3499303 := bstep (se 1 (by rfl) ⟨2624477, by rfl⟩ : syracuseStep 3499303 = 5248955) B5248955
theorem B11650391 : Blo 1532463 11650391 := bstep (se 1 (by rfl) ⟨8737793, by rfl⟩ : syracuseStep 11650391 = 17475587) B17475587
theorem B1533275 : Blo 1532463 1533275 := bstep (se 1 (by rfl) ⟨1149956, by rfl⟩ : syracuseStep 1533275 = 2299913) B2299913
theorem B4662623 : Blo 1532463 4662623 := bstep (se 1 (by rfl) ⟨3496967, by rfl⟩ : syracuseStep 4662623 = 6993935) B6993935
theorem B1533295 : Blo 1532463 1533295 := bstep (se 1 (by rfl) ⟨1149971, by rfl⟩ : syracuseStep 1533295 = 2299943) B2299943
theorem B16590233 : Blo 1532463 16590233 := bstep (se 2 (by rfl) ⟨6221337, by rfl⟩ : syracuseStep 16590233 = 12442675) B12442675
theorem B1533351 : Blo 1532463 1533351 := bstep (se 1 (by rfl) ⟨1150013, by rfl⟩ : syracuseStep 1533351 = 2300027) B2300027
theorem B3450311 : Blo 1532463 3450311 := bstep (se 1 (by rfl) ⟨2587733, by rfl⟩ : syracuseStep 3450311 = 5175467) B5175467
theorem B1533435 : Blo 1532463 1533435 := bstep (se 1 (by rfl) ⟨1150076, by rfl⟩ : syracuseStep 1533435 = 2300153) B2300153
theorem B1533503 : Blo 1532463 1533503 := bstep (se 1 (by rfl) ⟨1150127, by rfl⟩ : syracuseStep 1533503 = 2300255) B2300255
theorem B1533511 : Blo 1532463 1533511 := bstep (se 1 (by rfl) ⟨1150133, by rfl⟩ : syracuseStep 1533511 = 2300267) B2300267
theorem B13092475 : Blo 1532463 13092475 := bstep (se 1 (by rfl) ⟨9819356, by rfl⟩ : syracuseStep 13092475 = 19638713) B19638713
theorem B2909857 : Blo 1532463 2909857 := bstep (se 2 (by rfl) ⟨1091196, by rfl⟩ : syracuseStep 2909857 = 2182393) B2182393
theorem B7767737 : Blo 1532463 7767737 := bstep (se 2 (by rfl) ⟨2912901, by rfl⟩ : syracuseStep 7767737 = 5825803) B5825803
theorem B1533663 : Blo 1532463 1533663 := bstep (se 1 (by rfl) ⟨1150247, by rfl⟩ : syracuseStep 1533663 = 2300495) B2300495
theorem B3450671 : Blo 1532463 3450671 := bstep (se 1 (by rfl) ⟨2588003, by rfl⟩ : syracuseStep 3450671 = 5176007) B5176007
theorem B1533743 : Blo 1532463 1533743 := bstep (se 1 (by rfl) ⟨1150307, by rfl⟩ : syracuseStep 1533743 = 2300615) B2300615
theorem B4728631 : Blo 1532463 4728631 := bstep (se 1 (by rfl) ⟨3546473, by rfl⟩ : syracuseStep 4728631 = 7092947) B7092947
theorem B1533851 : Blo 1532463 1533851 := bstep (se 1 (by rfl) ⟨1150388, by rfl⟩ : syracuseStep 1533851 = 2300777) B2300777
theorem B7759799 : Blo 1532463 7759799 := bstep (se 1 (by rfl) ⟨5819849, by rfl⟩ : syracuseStep 7759799 = 11639699) B11639699
theorem B11053007 : Blo 1532463 11053007 := bstep (se 1 (by rfl) ⟨8289755, by rfl⟩ : syracuseStep 11053007 = 16579511) B16579511
theorem B1533903 : Blo 1532463 1533903 := bstep (se 1 (by rfl) ⟨1150427, by rfl⟩ : syracuseStep 1533903 = 2300855) B2300855
theorem B1533927 : Blo 1532463 1533927 := bstep (se 1 (by rfl) ⟨1150445, by rfl⟩ : syracuseStep 1533927 = 2300891) B2300891
theorem B26200259 : Blo 1532463 26200259 := bstep (se 1 (by rfl) ⟨19650194, by rfl⟩ : syracuseStep 26200259 = 39300389) B39300389
theorem B1534239 : Blo 1532463 1534239 := bstep (se 1 (by rfl) ⟨1150679, by rfl⟩ : syracuseStep 1534239 = 2301359) B2301359
theorem B1534299 : Blo 1532463 1534299 := bstep (se 1 (by rfl) ⟨1150724, by rfl⟩ : syracuseStep 1534299 = 2301449) B2301449
theorem B4909423 : Blo 1532463 4909423 := bstep (se 1 (by rfl) ⟨3682067, by rfl⟩ : syracuseStep 4909423 = 7364135) B7364135
theorem B3451247 : Blo 1532463 3451247 := bstep (se 1 (by rfl) ⟨2588435, by rfl⟩ : syracuseStep 3451247 = 5176871) B5176871
theorem B1534319 : Blo 1532463 1534319 := bstep (se 1 (by rfl) ⟨1150739, by rfl⟩ : syracuseStep 1534319 = 2301479) B2301479
theorem B1534375 : Blo 1532463 1534375 := bstep (se 1 (by rfl) ⟨1150781, by rfl⟩ : syracuseStep 1534375 = 2301563) B2301563
theorem B3451319 : Blo 1532463 3451319 := bstep (se 1 (by rfl) ⟨2588489, by rfl⟩ : syracuseStep 3451319 = 5176979) B5176979
theorem B3107297 : Blo 1532463 3107297 := bstep (se 2 (by rfl) ⟨1165236, by rfl⟩ : syracuseStep 3107297 = 2330473) B2330473
theorem B1534459 : Blo 1532463 1534459 := bstep (se 1 (by rfl) ⟨1150844, by rfl⟩ : syracuseStep 1534459 = 2301689) B2301689
theorem B7760447 : Blo 1532463 7760447 := bstep (se 1 (by rfl) ⟨5820335, by rfl⟩ : syracuseStep 7760447 = 11640671) B11640671
theorem B2910791 : Blo 1532463 2910791 := bstep (se 1 (by rfl) ⟨2183093, by rfl⟩ : syracuseStep 2910791 = 4366187) B4366187
theorem B3451463 : Blo 1532463 3451463 := bstep (se 1 (by rfl) ⟨2588597, by rfl⟩ : syracuseStep 3451463 = 5177195) B5177195
theorem B3451499 : Blo 1532463 3451499 := bstep (se 1 (by rfl) ⟨2588624, by rfl⟩ : syracuseStep 3451499 = 5177249) B5177249
theorem B3935207 : Blo 1532463 3935207 := bstep (se 1 (by rfl) ⟨2951405, by rfl⟩ : syracuseStep 3935207 = 5902811) B5902811
theorem B3451895 : Blo 1532463 3451895 := bstep (se 1 (by rfl) ⟨2588921, by rfl⟩ : syracuseStep 3451895 = 5177843) B5177843
theorem B5172443 : Blo 1532463 5172443 := bstep (se 1 (by rfl) ⟨3879332, by rfl⟩ : syracuseStep 5172443 = 7758665) B7758665
theorem B3452255 : Blo 1532463 3452255 := bstep (se 1 (by rfl) ⟨2589191, by rfl⟩ : syracuseStep 3452255 = 5178383) B5178383
theorem B29470067 : Blo 1532463 29470067 := bstep (se 1 (by rfl) ⟨22102550, by rfl⟩ : syracuseStep 29470067 = 44205101) B44205101
theorem B8285689 : Blo 1532463 8285689 := bstep (se 2 (by rfl) ⟨3107133, by rfl⟩ : syracuseStep 8285689 = 6214267) B6214267
theorem B7466555 : Blo 1532463 7466555 := bstep (se 1 (by rfl) ⟨5599916, by rfl⟩ : syracuseStep 7466555 = 11199833) B11199833
theorem B6221407 : Blo 1532463 6221407 := bstep (se 1 (by rfl) ⟨4666055, by rfl⟩ : syracuseStep 6221407 = 9332111) B9332111
theorem B14732999 : Blo 1532463 14732999 := bstep (se 1 (by rfl) ⟨11049749, by rfl⟩ : syracuseStep 14732999 = 22099499) B22099499
theorem B14733035 : Blo 1532463 14733035 := bstep (se 1 (by rfl) ⟨11049776, by rfl⟩ : syracuseStep 14733035 = 22099553) B22099553
theorem B5902121 : Blo 1532463 5902121 := bstep (se 2 (by rfl) ⟨2213295, by rfl⟩ : syracuseStep 5902121 = 4426591) B4426591
theorem B13283293 : Blo 1532463 13283293 := bstep (se 3 (by rfl) ⟨2490617, by rfl⟩ : syracuseStep 13283293 = 4981235) B4981235
theorem B26570753 : Blo 1532463 26570753 := bstep (se 2 (by rfl) ⟨9964032, by rfl⟩ : syracuseStep 26570753 = 19928065) B19928065
theorem B5173307 : Blo 1532463 5173307 := bstep (se 1 (by rfl) ⟨3879980, by rfl⟩ : syracuseStep 5173307 = 7759961) B7759961
theorem B8728681 : Blo 1532463 8728681 := bstep (se 2 (by rfl) ⟨3273255, by rfl⟩ : syracuseStep 8728681 = 6546511) B6546511
theorem B7868627 : Blo 1532463 7868627 := bstep (se 1 (by rfl) ⟨5901470, by rfl⟩ : syracuseStep 7868627 = 11802941) B11802941
theorem B5173577 : Blo 1532463 5173577 := bstep (se 2 (by rfl) ⟨1940091, by rfl⟩ : syracuseStep 5173577 = 3880183) B3880183
theorem B4977071 : Blo 1532463 4977071 := bstep (se 1 (by rfl) ⟨3732803, by rfl⟩ : syracuseStep 4977071 = 7465607) B7465607
theorem B11964847 : Blo 1532463 11964847 := bstep (se 1 (by rfl) ⟨8973635, by rfl⟩ : syracuseStep 11964847 = 17947271) B17947271
theorem B5820929 : Blo 1532463 5820929 := bstep (se 2 (by rfl) ⟨2182848, by rfl⟩ : syracuseStep 5820929 = 4365697) B4365697
theorem B7762553 : Blo 1532463 7762553 := bstep (se 2 (by rfl) ⟨2910957, by rfl⟩ : syracuseStep 7762553 = 5821915) B5821915
theorem B3879647 : Blo 1532463 3879647 := bstep (se 1 (by rfl) ⟨2909735, by rfl⟩ : syracuseStep 3879647 = 5819471) B5819471
theorem B1725151 : Blo 1532463 1725151 := bstep (se 1 (by rfl) ⟨1293863, by rfl⟩ : syracuseStep 1725151 = 2587727) B2587727
theorem B2298779 : Blo 1532463 2298779 := bstep (se 1 (by rfl) ⟨1724084, by rfl⟩ : syracuseStep 2298779 = 3448169) B3448169
theorem B5821415 : Blo 1532463 5821415 := bstep (se 1 (by rfl) ⟨4366061, by rfl⟩ : syracuseStep 5821415 = 8732123) B8732123
theorem B13980761 : Blo 1532463 13980761 := bstep (se 2 (by rfl) ⟨5242785, by rfl⟩ : syracuseStep 13980761 = 10485571) B10485571
theorem B7369825 : Blo 1532463 7369825 := bstep (se 2 (by rfl) ⟨2763684, by rfl⟩ : syracuseStep 7369825 = 5527369) B5527369
theorem B63845495 : Blo 1532463 63845495 := bstep (se 1 (by rfl) ⟨47884121, by rfl⟩ : syracuseStep 63845495 = 95768243) B95768243
theorem B3273871 : Blo 1532463 3273871 := bstep (se 1 (by rfl) ⟨2455403, by rfl⟩ : syracuseStep 3273871 = 4910807) B4910807
theorem B1725727 : Blo 1532463 1725727 := bstep (se 1 (by rfl) ⟨1294295, by rfl⟩ : syracuseStep 1725727 = 2588591) B2588591
theorem B2299175 : Blo 1532463 2299175 := bstep (se 1 (by rfl) ⟨1724381, by rfl⟩ : syracuseStep 2299175 = 3448763) B3448763
theorem B19641689 : Blo 1532463 19641689 := bstep (se 2 (by rfl) ⟨7365633, by rfl⟩ : syracuseStep 19641689 = 14731267) B14731267
theorem B6640991 : Blo 1532463 6640991 := bstep (se 1 (by rfl) ⟨4980743, by rfl⟩ : syracuseStep 6640991 = 9961487) B9961487
theorem B2299259 : Blo 1532463 2299259 := bstep (se 1 (by rfl) ⟨1724444, by rfl⟩ : syracuseStep 2299259 = 3448889) B3448889
theorem B55981529 : Blo 1532463 55981529 := bstep (se 2 (by rfl) ⟨20993073, by rfl⟩ : syracuseStep 55981529 = 41986147) B41986147
theorem B2299385 : Blo 1532463 2299385 := bstep (se 2 (by rfl) ⟨862269, by rfl⟩ : syracuseStep 2299385 = 1724539) B1724539
theorem B1726015 : Blo 1532463 1726015 := bstep (se 1 (by rfl) ⟨1294511, by rfl⟩ : syracuseStep 1726015 = 2589023) B2589023
theorem B2299487 : Blo 1532463 2299487 := bstep (se 1 (by rfl) ⟨1724615, by rfl⟩ : syracuseStep 2299487 = 3449231) B3449231
theorem B14382877 : Blo 1532463 14382877 := bstep (se 3 (by rfl) ⟨2696789, by rfl⟩ : syracuseStep 14382877 = 5393579) B5393579
theorem B2299703 : Blo 1532463 2299703 := bstep (se 1 (by rfl) ⟨1724777, by rfl⟩ : syracuseStep 2299703 = 3449555) B3449555
theorem B4364239 : Blo 1532463 4364239 := bstep (se 1 (by rfl) ⟨3273179, by rfl⟩ : syracuseStep 4364239 = 6546359) B6546359
theorem B2300009 : Blo 1532463 2300009 := bstep (se 2 (by rfl) ⟨862503, by rfl⟩ : syracuseStep 2300009 = 1725007) B1725007
theorem B18897059 : Blo 1532463 18897059 := bstep (se 1 (by rfl) ⟨14172794, by rfl⟩ : syracuseStep 18897059 = 28345589) B28345589
theorem B13097123 : Blo 1532463 13097123 := bstep (se 1 (by rfl) ⟨9822842, by rfl⟩ : syracuseStep 13097123 = 19645685) B19645685
theorem B2586971 : Blo 1532463 2586971 := bstep (se 1 (by rfl) ⟨1940228, by rfl⟩ : syracuseStep 2586971 = 3880457) B3880457
theorem B2586991 : Blo 1532463 2586991 := bstep (se 1 (by rfl) ⟨1940243, by rfl⟩ : syracuseStep 2586991 = 3880487) B3880487
theorem B4200815 : Blo 1532463 4200815 := bstep (se 1 (by rfl) ⟨3150611, by rfl⟩ : syracuseStep 4200815 = 6301223) B6301223
theorem B7764335 : Blo 1532463 7764335 := bstep (se 1 (by rfl) ⟨5823251, by rfl⟩ : syracuseStep 7764335 = 11646503) B11646503
theorem B1939879 : Blo 1532463 1939879 := bstep (se 1 (by rfl) ⟨1454909, by rfl⟩ : syracuseStep 1939879 = 2909819) B2909819
theorem B2300327 : Blo 1532463 2300327 := bstep (se 1 (by rfl) ⟨1725245, by rfl⟩ : syracuseStep 2300327 = 3450491) B3450491
theorem B5822887 : Blo 1532463 5822887 := bstep (se 1 (by rfl) ⟨4367165, by rfl⟩ : syracuseStep 5822887 = 8734331) B8734331
theorem B7870931 : Blo 1532463 7870931 := bstep (se 1 (by rfl) ⟨5903198, by rfl⟩ : syracuseStep 7870931 = 11806397) B11806397
theorem B2300411 : Blo 1532463 2300411 := bstep (se 1 (by rfl) ⟨1725308, by rfl⟩ : syracuseStep 2300411 = 3450617) B3450617
theorem B2587207 : Blo 1532463 2587207 := bstep (se 1 (by rfl) ⟨1940405, by rfl⟩ : syracuseStep 2587207 = 3880811) B3880811
theorem B9828971 : Blo 1532463 9828971 := bstep (se 1 (by rfl) ⟨7371728, by rfl⟩ : syracuseStep 9828971 = 14743457) B14743457
theorem B2300537 : Blo 1532463 2300537 := bstep (se 2 (by rfl) ⟨862701, by rfl⟩ : syracuseStep 2300537 = 1725403) B1725403
theorem B8288891 : Blo 1532463 8288891 := bstep (se 1 (by rfl) ⟨6216668, by rfl⟩ : syracuseStep 8288891 = 12433337) B12433337
theorem B2300591 : Blo 1532463 2300591 := bstep (se 1 (by rfl) ⟨1725443, by rfl⟩ : syracuseStep 2300591 = 3450887) B3450887
theorem B2300639 : Blo 1532463 2300639 := bstep (se 1 (by rfl) ⟨1725479, by rfl⟩ : syracuseStep 2300639 = 3450959) B3450959
theorem B1940203 : Blo 1532463 1940203 := bstep (se 1 (by rfl) ⟨1455152, by rfl⟩ : syracuseStep 1940203 = 2910305) B2910305
theorem B7469815 : Blo 1532463 7469815 := bstep (se 1 (by rfl) ⟨5602361, by rfl⟩ : syracuseStep 7469815 = 11204723) B11204723
theorem B5905277 : Blo 1532463 5905277 := bstep (se 3 (by rfl) ⟨1107239, by rfl⟩ : syracuseStep 5905277 = 2214479) B2214479
theorem B1940431 : Blo 1532463 1940431 := bstep (se 1 (by rfl) ⟨1455323, by rfl⟩ : syracuseStep 1940431 = 2910647) B2910647
theorem B2300903 : Blo 1532463 2300903 := bstep (se 1 (by rfl) ⟨1725677, by rfl⟩ : syracuseStep 2300903 = 3451355) B3451355
theorem B2587639 : Blo 1532463 2587639 := bstep (se 1 (by rfl) ⟨1940729, by rfl⟩ : syracuseStep 2587639 = 3881459) B3881459
theorem B3882107 : Blo 1532463 3882107 := bstep (se 1 (by rfl) ⟨2911580, by rfl⟩ : syracuseStep 3882107 = 5823161) B5823161
theorem B7371899 : Blo 1532463 7371899 := bstep (se 1 (by rfl) ⟨5528924, by rfl⟩ : syracuseStep 7371899 = 11057849) B11057849
theorem B3882127 : Blo 1532463 3882127 := bstep (se 1 (by rfl) ⟨2911595, by rfl⟩ : syracuseStep 3882127 = 5823191) B5823191
theorem B5823677 : Blo 1532463 5823677 := bstep (se 3 (by rfl) ⟨1091939, by rfl⟩ : syracuseStep 5823677 = 2183879) B2183879
theorem B1940699 : Blo 1532463 1940699 := bstep (se 1 (by rfl) ⟨1455524, by rfl⟩ : syracuseStep 1940699 = 2911049) B2911049
theorem B4914395 : Blo 1532463 4914395 := bstep (se 1 (by rfl) ⟨3685796, by rfl⟩ : syracuseStep 4914395 = 7371593) B7371593
theorem B2694377 : Blo 1532463 2694377 := bstep (se 2 (by rfl) ⟨1010391, by rfl⟩ : syracuseStep 2694377 = 2020783) B2020783
theorem B2301161 : Blo 1532463 2301161 := bstep (se 2 (by rfl) ⟨862935, by rfl⟩ : syracuseStep 2301161 = 1725871) B1725871
theorem B2301215 : Blo 1532463 2301215 := bstep (se 1 (by rfl) ⟨1725911, by rfl⟩ : syracuseStep 2301215 = 3451823) B3451823
theorem B2587943 : Blo 1532463 2587943 := bstep (se 1 (by rfl) ⟨1940957, by rfl⟩ : syracuseStep 2587943 = 3881915) B3881915
theorem B7372093 : Blo 1532463 7372093 := bstep (se 3 (by rfl) ⟨1382267, by rfl⟩ : syracuseStep 7372093 = 2764535) B2764535
theorem B3448187 : Blo 1532463 3448187 := bstep (se 1 (by rfl) ⟨2586140, by rfl⟩ : syracuseStep 3448187 = 5172281) B5172281
theorem B3882401 : Blo 1532463 3882401 := bstep (se 2 (by rfl) ⟨1455900, by rfl⟩ : syracuseStep 3882401 = 2911801) B2911801
theorem B5176763 : Blo 1532463 5176763 := bstep (se 1 (by rfl) ⟨3882572, by rfl⟩ : syracuseStep 5176763 = 7765145) B7765145
theorem B2301383 : Blo 1532463 2301383 := bstep (se 1 (by rfl) ⟨1726037, by rfl⟩ : syracuseStep 2301383 = 3452075) B3452075
theorem B3448313 : Blo 1532463 3448313 := bstep (se 2 (by rfl) ⟨1293117, by rfl⟩ : syracuseStep 3448313 = 2586235) B2586235
theorem B3276281 : Blo 1532463 3276281 := bstep (se 2 (by rfl) ⟨1228605, by rfl⟩ : syracuseStep 3276281 = 2457211) B2457211
theorem B3448403 : Blo 1532463 3448403 := bstep (se 1 (by rfl) ⟨2586302, by rfl⟩ : syracuseStep 3448403 = 5172605) B5172605
theorem B4488787 : Blo 1532463 4488787 := bstep (se 1 (by rfl) ⟨3366590, by rfl⟩ : syracuseStep 4488787 = 6733181) B6733181
theorem B1941175 : Blo 1532463 1941175 := bstep (se 1 (by rfl) ⟨1455881, by rfl⟩ : syracuseStep 1941175 = 2911763) B2911763
theorem B2588395 : Blo 1532463 2588395 := bstep (se 1 (by rfl) ⟨1941296, by rfl⟩ : syracuseStep 2588395 = 3882593) B3882593
theorem B3448583 : Blo 1532463 3448583 := bstep (se 1 (by rfl) ⟨2586437, by rfl⟩ : syracuseStep 3448583 = 5172875) B5172875
theorem B3686201 : Blo 1532463 3686201 := bstep (se 2 (by rfl) ⟨1382325, by rfl⟩ : syracuseStep 3686201 = 2764651) B2764651
theorem B3686249 : Blo 1532463 3686249 := bstep (se 2 (by rfl) ⟨1382343, by rfl⟩ : syracuseStep 3686249 = 2764687) B2764687
theorem B1941403 : Blo 1532463 1941403 := bstep (se 1 (by rfl) ⟨1456052, by rfl⟩ : syracuseStep 1941403 = 2912105) B2912105
theorem B3448871 : Blo 1532463 3448871 := bstep (se 1 (by rfl) ⟨2586653, by rfl⟩ : syracuseStep 3448871 = 5173307) B5173307
theorem B3449051 : Blo 1532463 3449051 := bstep (se 1 (by rfl) ⟨2586788, by rfl⟩ : syracuseStep 3449051 = 5173577) B5173577
theorem B3318047 : Blo 1532463 3318047 := bstep (se 1 (by rfl) ⟨2488535, by rfl⟩ : syracuseStep 3318047 = 4977071) B4977071
theorem B6545897 : Blo 1532463 6545897 := bstep (se 2 (by rfl) ⟨2454711, by rfl⟩ : syracuseStep 6545897 = 4909423) B4909423
theorem B3449321 : Blo 1532463 3449321 := bstep (se 2 (by rfl) ⟨1293495, by rfl⟩ : syracuseStep 3449321 = 2586991) B2586991
theorem B1532519 : Blo 1532463 1532519 := bstep (se 1 (by rfl) ⟨1149389, by rfl⟩ : syracuseStep 1532519 = 2298779) B2298779
theorem B3449609 : Blo 1532463 3449609 := bstep (se 2 (by rfl) ⟨1293603, by rfl⟩ : syracuseStep 3449609 = 2587207) B2587207
theorem B1532783 : Blo 1532463 1532783 := bstep (se 1 (by rfl) ⟨1149587, by rfl⟩ : syracuseStep 1532783 = 2299175) B2299175
theorem B7766927 : Blo 1532463 7766927 := bstep (se 1 (by rfl) ⟨5825195, by rfl⟩ : syracuseStep 7766927 = 11650391) B11650391
theorem B10486685 : Blo 1532463 10486685 := bstep (se 3 (by rfl) ⟨1966253, by rfl⟩ : syracuseStep 10486685 = 3932507) B3932507
theorem B1532839 : Blo 1532463 1532839 := bstep (se 1 (by rfl) ⟨1149629, by rfl⟩ : syracuseStep 1532839 = 2299259) B2299259
theorem B11060155 : Blo 1532463 11060155 := bstep (se 1 (by rfl) ⟨8295116, by rfl⟩ : syracuseStep 11060155 = 16590233) B16590233
theorem B1532923 : Blo 1532463 1532923 := bstep (se 1 (by rfl) ⟨1149692, by rfl⟩ : syracuseStep 1532923 = 2299385) B2299385
theorem B1532991 : Blo 1532463 1532991 := bstep (se 1 (by rfl) ⟨1149743, by rfl⟩ : syracuseStep 1532991 = 2299487) B2299487
theorem B5178491 : Blo 1532463 5178491 := bstep (se 1 (by rfl) ⟨3883868, by rfl⟩ : syracuseStep 5178491 = 7767737) B7767737
theorem B1533135 : Blo 1532463 1533135 := bstep (se 1 (by rfl) ⟨1149851, by rfl⟩ : syracuseStep 1533135 = 2299703) B2299703
theorem B3450185 : Blo 1532463 3450185 := bstep (se 2 (by rfl) ⟨1293819, by rfl⟩ : syracuseStep 3450185 = 2587639) B2587639
theorem B5178761 : Blo 1532463 5178761 := bstep (se 2 (by rfl) ⟨1942035, by rfl⟩ : syracuseStep 5178761 = 3884071) B3884071
theorem B1533339 : Blo 1532463 1533339 := bstep (se 1 (by rfl) ⟨1150004, by rfl⟩ : syracuseStep 1533339 = 2300009) B2300009
theorem B17466839 : Blo 1532463 17466839 := bstep (se 1 (by rfl) ⟨13100129, by rfl⟩ : syracuseStep 17466839 = 26200259) B26200259
theorem B1533551 : Blo 1532463 1533551 := bstep (se 1 (by rfl) ⟨1150163, by rfl⟩ : syracuseStep 1533551 = 2300327) B2300327
theorem B1533607 : Blo 1532463 1533607 := bstep (se 1 (by rfl) ⟨1150205, by rfl⟩ : syracuseStep 1533607 = 2300411) B2300411
theorem B1533691 : Blo 1532463 1533691 := bstep (se 1 (by rfl) ⟨1150268, by rfl⟩ : syracuseStep 1533691 = 2300537) B2300537
theorem B1533727 : Blo 1532463 1533727 := bstep (se 1 (by rfl) ⟨1150295, by rfl⟩ : syracuseStep 1533727 = 2300591) B2300591
theorem B1533759 : Blo 1532463 1533759 := bstep (se 1 (by rfl) ⟨1150319, by rfl⟩ : syracuseStep 1533759 = 2300639) B2300639
theorem B2623471 : Blo 1532463 2623471 := bstep (se 1 (by rfl) ⟨1967603, by rfl⟩ : syracuseStep 2623471 = 3935207) B3935207
theorem B1533935 : Blo 1532463 1533935 := bstep (se 1 (by rfl) ⟨1150451, by rfl⟩ : syracuseStep 1533935 = 2300903) B2300903
theorem B1796251 : Blo 1532463 1796251 := bstep (se 1 (by rfl) ⟨1347188, by rfl⟩ : syracuseStep 1796251 = 2694377) B2694377
theorem B1534107 : Blo 1532463 1534107 := bstep (se 1 (by rfl) ⟨1150580, by rfl⟩ : syracuseStep 1534107 = 2301161) B2301161
theorem B1534143 : Blo 1532463 1534143 := bstep (se 1 (by rfl) ⟨1150607, by rfl⟩ : syracuseStep 1534143 = 2301215) B2301215
theorem B19646711 : Blo 1532463 19646711 := bstep (se 1 (by rfl) ⟨14735033, by rfl⟩ : syracuseStep 19646711 = 29470067) B29470067
theorem B3451175 : Blo 1532463 3451175 := bstep (se 1 (by rfl) ⟨2588381, by rfl⟩ : syracuseStep 3451175 = 5176763) B5176763
theorem B1534255 : Blo 1532463 1534255 := bstep (se 1 (by rfl) ⟨1150691, by rfl⟩ : syracuseStep 1534255 = 2301383) B2301383
theorem B3451193 : Blo 1532463 3451193 := bstep (se 2 (by rfl) ⟨1294197, by rfl⟩ : syracuseStep 3451193 = 2588395) B2588395
theorem B3934747 : Blo 1532463 3934747 := bstep (se 1 (by rfl) ⟨2951060, by rfl⟩ : syracuseStep 3934747 = 5902121) B5902121
theorem B5818985 : Blo 1532463 5818985 := bstep (se 2 (by rfl) ⟨2182119, by rfl⟩ : syracuseStep 5818985 = 4364239) B4364239
theorem B17713835 : Blo 1532463 17713835 := bstep (se 1 (by rfl) ⟨13285376, by rfl⟩ : syracuseStep 17713835 = 26570753) B26570753
theorem B4369079 : Blo 1532463 4369079 := bstep (se 1 (by rfl) ⟨3276809, by rfl⟩ : syracuseStep 4369079 = 6553619) B6553619
theorem B11643587 : Blo 1532463 11643587 := bstep (se 1 (by rfl) ⟨8732690, by rfl⟩ : syracuseStep 11643587 = 17465381) B17465381
theorem B5245751 : Blo 1532463 5245751 := bstep (se 1 (by rfl) ⟨3934313, by rfl⟩ : syracuseStep 5245751 = 7868627) B7868627
theorem B15953129 : Blo 1532463 15953129 := bstep (se 2 (by rfl) ⟨5982423, by rfl⟩ : syracuseStep 15953129 = 11964847) B11964847
theorem B13094459 : Blo 1532463 13094459 := bstep (se 1 (by rfl) ⟨9820844, by rfl⟩ : syracuseStep 13094459 = 19641689) B19641689
theorem B4427327 : Blo 1532463 4427327 := bstep (se 1 (by rfl) ⟨3320495, by rfl⟩ : syracuseStep 4427327 = 6640991) B6640991
theorem B3452489 : Blo 1532463 3452489 := bstep (se 2 (by rfl) ⟨1294683, by rfl⟩ : syracuseStep 3452489 = 2589367) B2589367
theorem B5173199 : Blo 1532463 5173199 := bstep (se 1 (by rfl) ⟨3879899, by rfl⟩ : syracuseStep 5173199 = 7759799) B7759799
theorem B7368671 : Blo 1532463 7368671 := bstep (se 1 (by rfl) ⟨5526503, by rfl⟩ : syracuseStep 7368671 = 11053007) B11053007
theorem B9826433 : Blo 1532463 9826433 := bstep (se 2 (by rfl) ⟨3684912, by rfl⟩ : syracuseStep 9826433 = 7369825) B7369825
theorem B1724647 : Blo 1532463 1724647 := bstep (se 1 (by rfl) ⟨1293485, by rfl⟩ : syracuseStep 1724647 = 2586971) B2586971
theorem B5247287 : Blo 1532463 5247287 := bstep (se 1 (by rfl) ⟨3935465, by rfl⟩ : syracuseStep 5247287 = 7870931) B7870931
theorem B5173631 : Blo 1532463 5173631 := bstep (se 1 (by rfl) ⟨3880223, by rfl⟩ : syracuseStep 5173631 = 7760447) B7760447
theorem B4665737 : Blo 1532463 4665737 := bstep (se 2 (by rfl) ⟨1749651, by rfl⟩ : syracuseStep 4665737 = 3499303) B3499303
theorem B5525927 : Blo 1532463 5525927 := bstep (se 1 (by rfl) ⟨4144445, by rfl⟩ : syracuseStep 5525927 = 8288891) B8288891
theorem B3936851 : Blo 1532463 3936851 := bstep (se 1 (by rfl) ⟨2952638, by rfl⟩ : syracuseStep 3936851 = 5905277) B5905277
theorem B11047585 : Blo 1532463 11047585 := bstep (se 2 (by rfl) ⟨4142844, by rfl⟩ : syracuseStep 11047585 = 8285689) B8285689
theorem B5985049 : Blo 1532463 5985049 := bstep (se 2 (by rfl) ⟨2244393, by rfl⟩ : syracuseStep 5985049 = 4488787) B4488787
theorem B8295209 : Blo 1532463 8295209 := bstep (se 2 (by rfl) ⟨3110703, by rfl⟩ : syracuseStep 8295209 = 6221407) B6221407
theorem B1725295 : Blo 1532463 1725295 := bstep (se 1 (by rfl) ⟨1293971, by rfl⟩ : syracuseStep 1725295 = 2587943) B2587943
theorem B3879809 : Blo 1532463 3879809 := bstep (se 2 (by rfl) ⟨1454928, by rfl⟩ : syracuseStep 3879809 = 2909857) B2909857
theorem B2298791 : Blo 1532463 2298791 := bstep (se 1 (by rfl) ⟨1724093, by rfl⟩ : syracuseStep 2298791 = 3448187) B3448187
theorem B2298875 : Blo 1532463 2298875 := bstep (se 1 (by rfl) ⟨1724156, by rfl⟩ : syracuseStep 2298875 = 3448313) B3448313
theorem B2184187 : Blo 1532463 2184187 := bstep (se 1 (by rfl) ⟨1638140, by rfl⟩ : syracuseStep 2184187 = 3276281) B3276281
theorem B4977703 : Blo 1532463 4977703 := bstep (se 1 (by rfl) ⟨3733277, by rfl⟩ : syracuseStep 4977703 = 7466555) B7466555
theorem B2298935 : Blo 1532463 2298935 := bstep (se 1 (by rfl) ⟨1724201, by rfl⟩ : syracuseStep 2298935 = 3448403) B3448403
theorem B6304841 : Blo 1532463 6304841 := bstep (se 2 (by rfl) ⟨2364315, by rfl⟩ : syracuseStep 6304841 = 4728631) B4728631
theorem B2299055 : Blo 1532463 2299055 := bstep (se 1 (by rfl) ⟨1724291, by rfl⟩ : syracuseStep 2299055 = 3448583) B3448583
theorem B11638241 : Blo 1532463 11638241 := bstep (se 2 (by rfl) ⟨4364340, by rfl⟩ : syracuseStep 11638241 = 8728681) B8728681
theorem B2299463 : Blo 1532463 2299463 := bstep (se 1 (by rfl) ⟨1724597, by rfl⟩ : syracuseStep 2299463 = 3449195) B3449195
theorem B2299559 : Blo 1532463 2299559 := bstep (se 1 (by rfl) ⟨1724669, by rfl⟩ : syracuseStep 2299559 = 3449339) B3449339
theorem B3880619 : Blo 1532463 3880619 := bstep (se 1 (by rfl) ⟨2910464, by rfl⟩ : syracuseStep 3880619 = 5820929) B5820929
theorem B2299643 : Blo 1532463 2299643 := bstep (se 1 (by rfl) ⟨1724732, by rfl⟩ : syracuseStep 2299643 = 3449465) B3449465
theorem B5175035 : Blo 1532463 5175035 := bstep (se 1 (by rfl) ⟨3881276, by rfl⟩ : syracuseStep 5175035 = 7762553) B7762553
theorem B5822219 : Blo 1532463 5822219 := bstep (se 1 (by rfl) ⟨4366664, by rfl⟩ : syracuseStep 5822219 = 8733329) B8733329
theorem B2299679 : Blo 1532463 2299679 := bstep (se 1 (by rfl) ⟨1724759, by rfl⟩ : syracuseStep 2299679 = 3449519) B3449519
theorem B2586431 : Blo 1532463 2586431 := bstep (se 1 (by rfl) ⟨1939823, by rfl⟩ : syracuseStep 2586431 = 3879647) B3879647
theorem B2299727 : Blo 1532463 2299727 := bstep (se 1 (by rfl) ⟨1724795, by rfl⟩ : syracuseStep 2299727 = 3449591) B3449591
theorem B2586505 : Blo 1532463 2586505 := bstep (se 2 (by rfl) ⟨969939, by rfl⟩ : syracuseStep 2586505 = 1939879) B1939879
theorem B7763849 : Blo 1532463 7763849 := bstep (se 2 (by rfl) ⟨2911443, by rfl⟩ : syracuseStep 7763849 = 5822887) B5822887
theorem B5175197 : Blo 1532463 5175197 := bstep (se 3 (by rfl) ⟨970349, by rfl⟩ : syracuseStep 5175197 = 1940699) B1940699
theorem B2299847 : Blo 1532463 2299847 := bstep (se 1 (by rfl) ⟨1724885, by rfl⟩ : syracuseStep 2299847 = 3449771) B3449771
theorem B8312807 : Blo 1532463 8312807 := bstep (se 1 (by rfl) ⟨6234605, by rfl⟩ : syracuseStep 8312807 = 12469211) B12469211
theorem B3880943 : Blo 1532463 3880943 := bstep (se 1 (by rfl) ⟨2910707, by rfl⟩ : syracuseStep 3880943 = 5821415) B5821415
theorem B9320507 : Blo 1532463 9320507 := bstep (se 1 (by rfl) ⟨6990380, by rfl⟩ : syracuseStep 9320507 = 13980761) B13980761
theorem B42563663 : Blo 1532463 42563663 := bstep (se 1 (by rfl) ⟨31922747, by rfl⟩ : syracuseStep 42563663 = 63845495) B63845495
theorem B22108315 : Blo 1532463 22108315 := bstep (se 1 (by rfl) ⟨16581236, by rfl⟩ : syracuseStep 22108315 = 33162473) B33162473
theorem B12433661 : Blo 1532463 12433661 := bstep (se 3 (by rfl) ⟨2331311, by rfl⟩ : syracuseStep 12433661 = 4662623) B4662623
theorem B2300201 : Blo 1532463 2300201 := bstep (se 2 (by rfl) ⟨862575, by rfl⟩ : syracuseStep 2300201 = 1725151) B1725151
theorem B2300207 : Blo 1532463 2300207 := bstep (se 1 (by rfl) ⟨1725155, by rfl⟩ : syracuseStep 2300207 = 3450311) B3450311
theorem B2586937 : Blo 1532463 2586937 := bstep (se 2 (by rfl) ⟨970101, by rfl⟩ : syracuseStep 2586937 = 1940203) B1940203
theorem B37321019 : Blo 1532463 37321019 := bstep (se 1 (by rfl) ⟨27990764, by rfl⟩ : syracuseStep 37321019 = 55981529) B55981529
theorem B9959753 : Blo 1532463 9959753 := bstep (se 2 (by rfl) ⟨3734907, by rfl⟩ : syracuseStep 9959753 = 7469815) B7469815
theorem B2300447 : Blo 1532463 2300447 := bstep (se 1 (by rfl) ⟨1725335, by rfl⟩ : syracuseStep 2300447 = 3450671) B3450671
theorem B2587241 : Blo 1532463 2587241 := bstep (se 2 (by rfl) ⟨970215, by rfl⟩ : syracuseStep 2587241 = 1940431) B1940431
theorem B12598039 : Blo 1532463 12598039 := bstep (se 1 (by rfl) ⟨9448529, by rfl⟩ : syracuseStep 12598039 = 18897059) B18897059
theorem B8731415 : Blo 1532463 8731415 := bstep (se 1 (by rfl) ⟨6548561, by rfl⟩ : syracuseStep 8731415 = 13097123) B13097123
theorem B4365161 : Blo 1532463 4365161 := bstep (se 2 (by rfl) ⟨1636935, by rfl⟩ : syracuseStep 4365161 = 3273871) B3273871
theorem B5176169 : Blo 1532463 5176169 := bstep (se 2 (by rfl) ⟨1941063, by rfl⟩ : syracuseStep 5176169 = 3882127) B3882127
theorem B2800543 : Blo 1532463 2800543 := bstep (se 1 (by rfl) ⟨2100407, by rfl⟩ : syracuseStep 2800543 = 4200815) B4200815
theorem B5176223 : Blo 1532463 5176223 := bstep (se 1 (by rfl) ⟨3882167, by rfl⟩ : syracuseStep 5176223 = 7764335) B7764335
theorem B2300831 : Blo 1532463 2300831 := bstep (se 1 (by rfl) ⟨1725623, by rfl⟩ : syracuseStep 2300831 = 3451247) B3451247
theorem B2300879 : Blo 1532463 2300879 := bstep (se 1 (by rfl) ⟨1725659, by rfl⟩ : syracuseStep 2300879 = 3451319) B3451319
theorem B2071531 : Blo 1532463 2071531 := bstep (se 1 (by rfl) ⟨1553648, by rfl⟩ : syracuseStep 2071531 = 3107297) B3107297
theorem B2300969 : Blo 1532463 2300969 := bstep (se 2 (by rfl) ⟨862863, by rfl⟩ : syracuseStep 2300969 = 1725727) B1725727
theorem B1940527 : Blo 1532463 1940527 := bstep (se 1 (by rfl) ⟨1455395, by rfl⟩ : syracuseStep 1940527 = 2910791) B2910791
theorem B2300975 : Blo 1532463 2300975 := bstep (se 1 (by rfl) ⟨1725731, by rfl⟩ : syracuseStep 2300975 = 3451463) B3451463
theorem B2300999 : Blo 1532463 2300999 := bstep (se 1 (by rfl) ⟨1725749, by rfl⟩ : syracuseStep 2300999 = 3451499) B3451499
theorem B6552647 : Blo 1532463 6552647 := bstep (se 1 (by rfl) ⟨4914485, by rfl⟩ : syracuseStep 6552647 = 9828971) B9828971
theorem B9829457 : Blo 1532463 9829457 := bstep (se 2 (by rfl) ⟨3686046, by rfl⟩ : syracuseStep 9829457 = 7372093) B7372093
theorem B9329917 : Blo 1532463 9329917 := bstep (se 3 (by rfl) ⟨1749359, by rfl⟩ : syracuseStep 9329917 = 3498719) B3498719
theorem B2301263 : Blo 1532463 2301263 := bstep (se 1 (by rfl) ⟨1725947, by rfl⟩ : syracuseStep 2301263 = 3451895) B3451895
theorem B2588071 : Blo 1532463 2588071 := bstep (se 1 (by rfl) ⟨1941053, by rfl⟩ : syracuseStep 2588071 = 3882107) B3882107
theorem B4914599 : Blo 1532463 4914599 := bstep (se 1 (by rfl) ⟨3685949, by rfl⟩ : syracuseStep 4914599 = 7371899) B7371899
theorem B2301353 : Blo 1532463 2301353 := bstep (se 2 (by rfl) ⟨863007, by rfl⟩ : syracuseStep 2301353 = 1726015) B1726015
theorem B3882451 : Blo 1532463 3882451 := bstep (se 1 (by rfl) ⟨2911838, by rfl⟩ : syracuseStep 3882451 = 5823677) B5823677
theorem B3448295 : Blo 1532463 3448295 := bstep (se 1 (by rfl) ⟨2586221, by rfl⟩ : syracuseStep 3448295 = 5172443) B5172443
theorem B3276263 : Blo 1532463 3276263 := bstep (se 1 (by rfl) ⟨2457197, by rfl⟩ : syracuseStep 3276263 = 4914395) B4914395
theorem B17456633 : Blo 1532463 17456633 := bstep (se 2 (by rfl) ⟨6546237, by rfl⟩ : syracuseStep 17456633 = 13092475) B13092475
theorem B2301503 : Blo 1532463 2301503 := bstep (se 1 (by rfl) ⟨1726127, by rfl⟩ : syracuseStep 2301503 = 3452255) B3452255
theorem B2588233 : Blo 1532463 2588233 := bstep (se 2 (by rfl) ⟨970587, by rfl⟩ : syracuseStep 2588233 = 1941175) B1941175
theorem B2588267 : Blo 1532463 2588267 := bstep (se 1 (by rfl) ⟨1941200, by rfl⟩ : syracuseStep 2588267 = 3882401) B3882401
theorem B9829997 : Blo 1532463 9829997 := bstep (se 3 (by rfl) ⟨1843124, by rfl⟩ : syracuseStep 9829997 = 3686249) B3686249
theorem B19177169 : Blo 1532463 19177169 := bstep (se 2 (by rfl) ⟨7191438, by rfl⟩ : syracuseStep 19177169 = 14382877) B14382877
theorem B9821999 : Blo 1532463 9821999 := bstep (se 1 (by rfl) ⟨7366499, by rfl⟩ : syracuseStep 9821999 = 14732999) B14732999
theorem B9822023 : Blo 1532463 9822023 := bstep (se 1 (by rfl) ⟨7366517, by rfl⟩ : syracuseStep 9822023 = 14733035) B14733035
theorem B2588537 : Blo 1532463 2588537 := bstep (se 2 (by rfl) ⟨970701, by rfl⟩ : syracuseStep 2588537 = 1941403) B1941403
theorem B2457467 : Blo 1532463 2457467 := bstep (se 1 (by rfl) ⟨1843100, by rfl⟩ : syracuseStep 2457467 = 3686201) B3686201
theorem B17711057 : Blo 1532463 17711057 := bstep (se 2 (by rfl) ⟨6641646, by rfl⟩ : syracuseStep 17711057 = 13283293) B13283293
theorem B2212031 : Blo 1532463 2212031 := bstep (se 1 (by rfl) ⟨1659023, by rfl⟩ : syracuseStep 2212031 = 3318047) B3318047
theorem B3498191 : Blo 1532463 3498191 := bstep (se 1 (by rfl) ⟨2623643, by rfl⟩ : syracuseStep 3498191 = 5247287) B5247287
theorem B3449087 : Blo 1532463 3449087 := bstep (se 1 (by rfl) ⟨2586815, by rfl⟩ : syracuseStep 3449087 = 5173631) B5173631
theorem B3449249 : Blo 1532463 3449249 := bstep (se 2 (by rfl) ⟨1293468, by rfl⟩ : syracuseStep 3449249 = 2586937) B2586937
theorem B5530139 : Blo 1532463 5530139 := bstep (se 1 (by rfl) ⟨4147604, by rfl⟩ : syracuseStep 5530139 = 8295209) B8295209
theorem B5177951 : Blo 1532463 5177951 := bstep (se 1 (by rfl) ⟨3883463, by rfl⟩ : syracuseStep 5177951 = 7766927) B7766927
theorem B1532527 : Blo 1532463 1532527 := bstep (se 1 (by rfl) ⟨1149395, by rfl⟩ : syracuseStep 1532527 = 2298791) B2298791
theorem B1532583 : Blo 1532463 1532583 := bstep (se 1 (by rfl) ⟨1149437, by rfl⟩ : syracuseStep 1532583 = 2298875) B2298875
theorem B1532623 : Blo 1532463 1532623 := bstep (se 1 (by rfl) ⟨1149467, by rfl⟩ : syracuseStep 1532623 = 2298935) B2298935
theorem B4203227 : Blo 1532463 4203227 := bstep (se 1 (by rfl) ⟨3152420, by rfl⟩ : syracuseStep 4203227 = 6304841) B6304841
theorem B1532703 : Blo 1532463 1532703 := bstep (se 1 (by rfl) ⟨1149527, by rfl⟩ : syracuseStep 1532703 = 2299055) B2299055
theorem B14730113 : Blo 1532463 14730113 := bstep (se 2 (by rfl) ⟨5523792, by rfl⟩ : syracuseStep 14730113 = 11047585) B11047585
theorem B7758827 : Blo 1532463 7758827 := bstep (se 1 (by rfl) ⟨5819120, by rfl⟩ : syracuseStep 7758827 = 11638241) B11638241
theorem B7980065 : Blo 1532463 7980065 := bstep (se 2 (by rfl) ⟨2992524, by rfl⟩ : syracuseStep 7980065 = 5985049) B5985049
theorem B1532975 : Blo 1532463 1532975 := bstep (se 1 (by rfl) ⟨1149731, by rfl⟩ : syracuseStep 1532975 = 2299463) B2299463
theorem B1533039 : Blo 1532463 1533039 := bstep (se 1 (by rfl) ⟨1149779, by rfl⟩ : syracuseStep 1533039 = 2299559) B2299559
theorem B1533095 : Blo 1532463 1533095 := bstep (se 1 (by rfl) ⟨1149821, by rfl⟩ : syracuseStep 1533095 = 2299643) B2299643
theorem B3450023 : Blo 1532463 3450023 := bstep (se 1 (by rfl) ⟨2587517, by rfl⟩ : syracuseStep 3450023 = 5175035) B5175035
theorem B1533119 : Blo 1532463 1533119 := bstep (se 1 (by rfl) ⟨1149839, by rfl⟩ : syracuseStep 1533119 = 2299679) B2299679
theorem B1533151 : Blo 1532463 1533151 := bstep (se 1 (by rfl) ⟨1149863, by rfl⟩ : syracuseStep 1533151 = 2299727) B2299727
theorem B14746873 : Blo 1532463 14746873 := bstep (se 2 (by rfl) ⟨5530077, by rfl⟩ : syracuseStep 14746873 = 11060155) B11060155
theorem B3450131 : Blo 1532463 3450131 := bstep (se 1 (by rfl) ⟨2587598, by rfl⟩ : syracuseStep 3450131 = 5175197) B5175197
theorem B1533231 : Blo 1532463 1533231 := bstep (se 1 (by rfl) ⟨1149923, by rfl⟩ : syracuseStep 1533231 = 2299847) B2299847
theorem B2762041 : Blo 1532463 2762041 := bstep (se 2 (by rfl) ⟨1035765, by rfl⟩ : syracuseStep 2762041 = 2071531) B2071531
theorem B1533467 : Blo 1532463 1533467 := bstep (se 1 (by rfl) ⟨1150100, by rfl⟩ : syracuseStep 1533467 = 2300201) B2300201
theorem B1533471 : Blo 1532463 1533471 := bstep (se 1 (by rfl) ⟨1150103, by rfl⟩ : syracuseStep 1533471 = 2300207) B2300207
theorem B24880679 : Blo 1532463 24880679 := bstep (se 1 (by rfl) ⟨18660509, by rfl⟩ : syracuseStep 24880679 = 37321019) B37321019
theorem B1533631 : Blo 1532463 1533631 := bstep (se 1 (by rfl) ⟨1150223, by rfl⟩ : syracuseStep 1533631 = 2300447) B2300447
theorem B11650877 : Blo 1532463 11650877 := bstep (se 3 (by rfl) ⟨2184539, by rfl⟩ : syracuseStep 11650877 = 4369079) B4369079
theorem B3450761 : Blo 1532463 3450761 := bstep (se 2 (by rfl) ⟨1294035, by rfl⟩ : syracuseStep 3450761 = 2588071) B2588071
theorem B2910107 : Blo 1532463 2910107 := bstep (se 1 (by rfl) ⟨2182580, by rfl⟩ : syracuseStep 2910107 = 4365161) B4365161
theorem B3450779 : Blo 1532463 3450779 := bstep (se 1 (by rfl) ⟨2588084, by rfl⟩ : syracuseStep 3450779 = 5176169) B5176169
theorem B3450815 : Blo 1532463 3450815 := bstep (se 1 (by rfl) ⟨2588111, by rfl⟩ : syracuseStep 3450815 = 5176223) B5176223
theorem B1533887 : Blo 1532463 1533887 := bstep (se 1 (by rfl) ⟨1150415, by rfl⟩ : syracuseStep 1533887 = 2300831) B2300831
theorem B1533919 : Blo 1532463 1533919 := bstep (se 1 (by rfl) ⟨1150439, by rfl⟩ : syracuseStep 1533919 = 2300879) B2300879
theorem B1533979 : Blo 1532463 1533979 := bstep (se 1 (by rfl) ⟨1150484, by rfl⟩ : syracuseStep 1533979 = 2300969) B2300969
theorem B1533983 : Blo 1532463 1533983 := bstep (se 1 (by rfl) ⟨1150487, by rfl⟩ : syracuseStep 1533983 = 2300975) B2300975
theorem B1533999 : Blo 1532463 1533999 := bstep (se 1 (by rfl) ⟨1150499, by rfl⟩ : syracuseStep 1533999 = 2300999) B2300999
theorem B4368431 : Blo 1532463 4368431 := bstep (se 1 (by rfl) ⟨3276323, by rfl⟩ : syracuseStep 4368431 = 6552647) B6552647
theorem B3450977 : Blo 1532463 3450977 := bstep (se 2 (by rfl) ⟨1294116, by rfl⟩ : syracuseStep 3450977 = 2588233) B2588233
theorem B10635419 : Blo 1532463 10635419 := bstep (se 1 (by rfl) ⟨7976564, by rfl⟩ : syracuseStep 10635419 = 15953129) B15953129
theorem B1534175 : Blo 1532463 1534175 := bstep (se 1 (by rfl) ⟨1150631, by rfl⟩ : syracuseStep 1534175 = 2301263) B2301263
theorem B1534235 : Blo 1532463 1534235 := bstep (se 1 (by rfl) ⟨1150676, by rfl⟩ : syracuseStep 1534235 = 2301353) B2301353
theorem B2951551 : Blo 1532463 2951551 := bstep (se 1 (by rfl) ⟨2213663, by rfl⟩ : syracuseStep 2951551 = 4427327) B4427327
theorem B1534335 : Blo 1532463 1534335 := bstep (se 1 (by rfl) ⟨1150751, by rfl⟩ : syracuseStep 1534335 = 2301503) B2301503
theorem B6547999 : Blo 1532463 6547999 := bstep (se 1 (by rfl) ⟨4910999, by rfl⟩ : syracuseStep 6547999 = 9821999) B9821999
theorem B6548015 : Blo 1532463 6548015 := bstep (se 1 (by rfl) ⟨4911011, by rfl⟩ : syracuseStep 6548015 = 9822023) B9822023
theorem B11807371 : Blo 1532463 11807371 := bstep (se 1 (by rfl) ⟨8855528, by rfl⟩ : syracuseStep 11807371 = 17711057) B17711057
theorem B2395001 : Blo 1532463 2395001 := bstep (se 2 (by rfl) ⟨898125, by rfl⟩ : syracuseStep 2395001 = 1796251) B1796251
theorem B29477753 : Blo 1532463 29477753 := bstep (se 2 (by rfl) ⟨11054157, by rfl⟩ : syracuseStep 29477753 = 22108315) B22108315
theorem B2624567 : Blo 1532463 2624567 := bstep (se 1 (by rfl) ⟨1968425, by rfl⟩ : syracuseStep 2624567 = 3936851) B3936851
theorem B6991123 : Blo 1532463 6991123 := bstep (se 1 (by rfl) ⟨5243342, by rfl⟩ : syracuseStep 6991123 = 10486685) B10486685
theorem B5246329 : Blo 1532463 5246329 := bstep (se 2 (by rfl) ⟨1967373, by rfl⟩ : syracuseStep 5246329 = 3934747) B3934747
theorem B3452327 : Blo 1532463 3452327 := bstep (se 1 (by rfl) ⟨2589245, by rfl⟩ : syracuseStep 3452327 = 5178491) B5178491
theorem B3452507 : Blo 1532463 3452507 := bstep (se 1 (by rfl) ⟨2589380, by rfl⟩ : syracuseStep 3452507 = 5178761) B5178761
theorem B11644559 : Blo 1532463 11644559 := bstep (se 1 (by rfl) ⟨8733419, by rfl⟩ : syracuseStep 11644559 = 17466839) B17466839
theorem B16797385 : Blo 1532463 16797385 := bstep (se 2 (by rfl) ⟨6299019, by rfl⟩ : syracuseStep 16797385 = 12598039) B12598039
theorem B1724287 : Blo 1532463 1724287 := bstep (se 1 (by rfl) ⟨1293215, by rfl⟩ : syracuseStep 1724287 = 2586431) B2586431
theorem B5541871 : Blo 1532463 5541871 := bstep (se 1 (by rfl) ⟨4156403, by rfl⟩ : syracuseStep 5541871 = 8312807) B8312807
theorem B2912249 : Blo 1532463 2912249 := bstep (se 2 (by rfl) ⟨1092093, by rfl⟩ : syracuseStep 2912249 = 2184187) B2184187
theorem B6213671 : Blo 1532463 6213671 := bstep (se 1 (by rfl) ⟨4660253, by rfl⟩ : syracuseStep 6213671 = 9320507) B9320507
theorem B6639835 : Blo 1532463 6639835 := bstep (se 1 (by rfl) ⟨4979876, by rfl⟩ : syracuseStep 6639835 = 9959753) B9959753
theorem B12439889 : Blo 1532463 12439889 := bstep (se 2 (by rfl) ⟨4664958, by rfl⟩ : syracuseStep 12439889 = 9329917) B9329917
theorem B3879323 : Blo 1532463 3879323 := bstep (se 1 (by rfl) ⟨2909492, by rfl⟩ : syracuseStep 3879323 = 5818985) B5818985
theorem B1724827 : Blo 1532463 1724827 := bstep (se 1 (by rfl) ⟨1293620, by rfl⟩ : syracuseStep 1724827 = 2587241) B2587241
theorem B11809223 : Blo 1532463 11809223 := bstep (se 1 (by rfl) ⟨8856917, by rfl⟩ : syracuseStep 11809223 = 17713835) B17713835
theorem B7762391 : Blo 1532463 7762391 := bstep (se 1 (by rfl) ⟨5821793, by rfl⟩ : syracuseStep 7762391 = 11643587) B11643587
theorem B5820943 : Blo 1532463 5820943 := bstep (se 1 (by rfl) ⟨4365707, by rfl⟩ : syracuseStep 5820943 = 8731415) B8731415
theorem B51139117 : Blo 1532463 51139117 := bstep (se 3 (by rfl) ⟨9588584, by rfl⟩ : syracuseStep 51139117 = 19177169) B19177169
theorem B2298863 : Blo 1532463 2298863 := bstep (se 1 (by rfl) ⟨1724147, by rfl⟩ : syracuseStep 2298863 = 3448295) B3448295
theorem B2184175 : Blo 1532463 2184175 := bstep (se 1 (by rfl) ⟨1638131, by rfl⟩ : syracuseStep 2184175 = 3276263) B3276263
theorem B11637755 : Blo 1532463 11637755 := bstep (se 1 (by rfl) ⟨8728316, by rfl⟩ : syracuseStep 11637755 = 17456633) B17456633
theorem B8729639 : Blo 1532463 8729639 := bstep (se 1 (by rfl) ⟨6547229, by rfl⟩ : syracuseStep 8729639 = 13094459) B13094459
theorem B1725511 : Blo 1532463 1725511 := bstep (se 1 (by rfl) ⟨1294133, by rfl⟩ : syracuseStep 1725511 = 2588267) B2588267
theorem B1725691 : Blo 1532463 1725691 := bstep (se 1 (by rfl) ⟨1294268, by rfl⟩ : syracuseStep 1725691 = 2588537) B2588537
theorem B4912447 : Blo 1532463 4912447 := bstep (se 1 (by rfl) ⟨3684335, by rfl⟩ : syracuseStep 4912447 = 7368671) B7368671
theorem B2299247 : Blo 1532463 2299247 := bstep (se 1 (by rfl) ⟨1724435, by rfl⟩ : syracuseStep 2299247 = 3448871) B3448871
theorem B6550955 : Blo 1532463 6550955 := bstep (se 1 (by rfl) ⟨4913216, by rfl⟩ : syracuseStep 6550955 = 9826433) B9826433
theorem B2299367 : Blo 1532463 2299367 := bstep (se 1 (by rfl) ⟨1724525, by rfl⟩ : syracuseStep 2299367 = 3449051) B3449051
theorem B26547749 : Blo 1532463 26547749 := bstep (se 4 (by rfl) ⟨2488851, by rfl⟩ : syracuseStep 26547749 = 4977703) B4977703
theorem B3110491 : Blo 1532463 3110491 := bstep (se 1 (by rfl) ⟨2332868, by rfl⟩ : syracuseStep 3110491 = 4665737) B4665737
theorem B3683951 : Blo 1532463 3683951 := bstep (se 1 (by rfl) ⟨2762963, by rfl⟩ : syracuseStep 3683951 = 5525927) B5525927
theorem B2299529 : Blo 1532463 2299529 := bstep (se 2 (by rfl) ⟨862323, by rfl⟩ : syracuseStep 2299529 = 1724647) B1724647
theorem B4363931 : Blo 1532463 4363931 := bstep (se 1 (by rfl) ⟨3272948, by rfl⟩ : syracuseStep 4363931 = 6545897) B6545897
theorem B2299547 : Blo 1532463 2299547 := bstep (se 1 (by rfl) ⟨1724660, by rfl⟩ : syracuseStep 2299547 = 3449321) B3449321
theorem B2299739 : Blo 1532463 2299739 := bstep (se 1 (by rfl) ⟨1724804, by rfl⟩ : syracuseStep 2299739 = 3449609) B3449609
theorem B2586539 : Blo 1532463 2586539 := bstep (se 1 (by rfl) ⟨1939904, by rfl⟩ : syracuseStep 2586539 = 3879809) B3879809
theorem B2300123 : Blo 1532463 2300123 := bstep (se 1 (by rfl) ⟨1725092, by rfl⟩ : syracuseStep 2300123 = 3450185) B3450185
theorem B13105597 : Blo 1532463 13105597 := bstep (se 3 (by rfl) ⟨2457299, by rfl⟩ : syracuseStep 13105597 = 4914599) B4914599
theorem B2587079 : Blo 1532463 2587079 := bstep (se 1 (by rfl) ⟨1940309, by rfl⟩ : syracuseStep 2587079 = 3880619) B3880619
theorem B2300393 : Blo 1532463 2300393 := bstep (se 2 (by rfl) ⟨862647, by rfl⟩ : syracuseStep 2300393 = 1725295) B1725295
theorem B3881479 : Blo 1532463 3881479 := bstep (se 1 (by rfl) ⟨2911109, by rfl⟩ : syracuseStep 3881479 = 5822219) B5822219
theorem B3734057 : Blo 1532463 3734057 := bstep (se 2 (by rfl) ⟨1400271, by rfl⟩ : syracuseStep 3734057 = 2800543) B2800543
theorem B5175899 : Blo 1532463 5175899 := bstep (se 1 (by rfl) ⟨3881924, by rfl⟩ : syracuseStep 5175899 = 7763849) B7763849
theorem B2587295 : Blo 1532463 2587295 := bstep (se 1 (by rfl) ⟨1940471, by rfl⟩ : syracuseStep 2587295 = 3880943) B3880943
theorem B28375775 : Blo 1532463 28375775 := bstep (se 1 (by rfl) ⟨21281831, by rfl⟩ : syracuseStep 28375775 = 42563663) B42563663
theorem B2587369 : Blo 1532463 2587369 := bstep (se 2 (by rfl) ⟨970263, by rfl⟩ : syracuseStep 2587369 = 1940527) B1940527
theorem B13097807 : Blo 1532463 13097807 := bstep (se 1 (by rfl) ⟨9823355, by rfl⟩ : syracuseStep 13097807 = 19646711) B19646711
theorem B8289107 : Blo 1532463 8289107 := bstep (se 1 (by rfl) ⟨6216830, by rfl⟩ : syracuseStep 8289107 = 12433661) B12433661
theorem B2300783 : Blo 1532463 2300783 := bstep (se 1 (by rfl) ⟨1725587, by rfl⟩ : syracuseStep 2300783 = 3451175) B3451175
theorem B2300795 : Blo 1532463 2300795 := bstep (se 1 (by rfl) ⟨1725596, by rfl⟩ : syracuseStep 2300795 = 3451193) B3451193
theorem B3497167 : Blo 1532463 3497167 := bstep (se 1 (by rfl) ⟨2622875, by rfl⟩ : syracuseStep 3497167 = 5245751) B5245751
theorem B5176601 : Blo 1532463 5176601 := bstep (se 2 (by rfl) ⟨1941225, by rfl⟩ : syracuseStep 5176601 = 3882451) B3882451
theorem B6552971 : Blo 1532463 6552971 := bstep (se 1 (by rfl) ⟨4914728, by rfl⟩ : syracuseStep 6552971 = 9829457) B9829457
theorem B55967381 : Blo 1532463 55967381 := bstep (se 6 (by rfl) ⟨1311735, by rfl⟩ : syracuseStep 55967381 = 2623471) B2623471
theorem B2301659 : Blo 1532463 2301659 := bstep (se 1 (by rfl) ⟨1726244, by rfl⟩ : syracuseStep 2301659 = 3452489) B3452489
theorem B6553331 : Blo 1532463 6553331 := bstep (se 1 (by rfl) ⟨4914998, by rfl⟩ : syracuseStep 6553331 = 9829997) B9829997
theorem B3448673 : Blo 1532463 3448673 := bstep (se 2 (by rfl) ⟨1293252, by rfl⟩ : syracuseStep 3448673 = 2586505) B2586505
theorem B1638311 : Blo 1532463 1638311 := bstep (se 1 (by rfl) ⟨1228733, by rfl⟩ : syracuseStep 1638311 = 2457467) B2457467
theorem B3448799 : Blo 1532463 3448799 := bstep (se 1 (by rfl) ⟨2586599, by rfl⟩ : syracuseStep 3448799 = 5173199) B5173199
theorem B7872815 : Blo 1532463 7872815 := bstep (se 1 (by rfl) ⟨5904611, by rfl⟩ : syracuseStep 7872815 = 11809223) B11809223
theorem B3686759 : Blo 1532463 3686759 := bstep (se 1 (by rfl) ⟨2765069, by rfl⟩ : syracuseStep 3686759 = 5530139) B5530139
theorem B28361117 : Blo 1532463 28361117 := bstep (se 3 (by rfl) ⟨5317709, by rfl⟩ : syracuseStep 28361117 = 10635419) B10635419
theorem B16589285 : Blo 1532463 16589285 := bstep (se 4 (by rfl) ⟨1555245, by rfl⟩ : syracuseStep 16589285 = 3110491) B3110491
theorem B2802151 : Blo 1532463 2802151 := bstep (se 1 (by rfl) ⟨2101613, by rfl⟩ : syracuseStep 2802151 = 4203227) B4203227
theorem B5898749 : Blo 1532463 5898749 := bstep (se 3 (by rfl) ⟨1106015, by rfl⟩ : syracuseStep 5898749 = 2212031) B2212031
theorem B17474129 : Blo 1532463 17474129 := bstep (se 2 (by rfl) ⟨6552798, by rfl⟩ : syracuseStep 17474129 = 13105597) B13105597
theorem B1532575 : Blo 1532463 1532575 := bstep (se 1 (by rfl) ⟨1149431, by rfl⟩ : syracuseStep 1532575 = 2298863) B2298863
theorem B7758503 : Blo 1532463 7758503 := bstep (se 1 (by rfl) ⟨5818877, by rfl⟩ : syracuseStep 7758503 = 11637755) B11637755
theorem B62972645 : Blo 1532463 62972645 := bstep (se 4 (by rfl) ⟨5903685, by rfl⟩ : syracuseStep 62972645 = 11807371) B11807371
theorem B1532831 : Blo 1532463 1532831 := bstep (se 1 (by rfl) ⟨1149623, by rfl⟩ : syracuseStep 1532831 = 2299247) B2299247
theorem B4367303 : Blo 1532463 4367303 := bstep (se 1 (by rfl) ⟨3275477, by rfl⟩ : syracuseStep 4367303 = 6550955) B6550955
theorem B3449825 : Blo 1532463 3449825 := bstep (se 2 (by rfl) ⟨1293684, by rfl⟩ : syracuseStep 3449825 = 2587369) B2587369
theorem B1532911 : Blo 1532463 1532911 := bstep (se 1 (by rfl) ⟨1149683, by rfl⟩ : syracuseStep 1532911 = 2299367) B2299367
theorem B1533019 : Blo 1532463 1533019 := bstep (se 1 (by rfl) ⟨1149764, by rfl⟩ : syracuseStep 1533019 = 2299529) B2299529
theorem B2909287 : Blo 1532463 2909287 := bstep (se 1 (by rfl) ⟨2181965, by rfl⟩ : syracuseStep 2909287 = 4363931) B4363931
theorem B1533031 : Blo 1532463 1533031 := bstep (se 1 (by rfl) ⟨1149773, by rfl⟩ : syracuseStep 1533031 = 2299547) B2299547
theorem B7767251 : Blo 1532463 7767251 := bstep (se 1 (by rfl) ⟨5825438, by rfl⟩ : syracuseStep 7767251 = 11650877) B11650877
theorem B1533159 : Blo 1532463 1533159 := bstep (se 1 (by rfl) ⟨1149869, by rfl⟩ : syracuseStep 1533159 = 2299739) B2299739
theorem B1533415 : Blo 1532463 1533415 := bstep (se 1 (by rfl) ⟨1150061, by rfl⟩ : syracuseStep 1533415 = 2300123) B2300123
theorem B4662889 : Blo 1532463 4662889 := bstep (se 2 (by rfl) ⟨1748583, by rfl⟩ : syracuseStep 4662889 = 3497167) B3497167
theorem B1533595 : Blo 1532463 1533595 := bstep (se 1 (by rfl) ⟨1150196, by rfl⟩ : syracuseStep 1533595 = 2300393) B2300393
theorem B19662497 : Blo 1532463 19662497 := bstep (se 2 (by rfl) ⟨7373436, by rfl⟩ : syracuseStep 19662497 = 14746873) B14746873
theorem B3450599 : Blo 1532463 3450599 := bstep (se 1 (by rfl) ⟨2587949, by rfl⟩ : syracuseStep 3450599 = 5175899) B5175899
theorem B18917183 : Blo 1532463 18917183 := bstep (se 1 (by rfl) ⟨14187887, by rfl⟩ : syracuseStep 18917183 = 28375775) B28375775
theorem B1533855 : Blo 1532463 1533855 := bstep (se 1 (by rfl) ⟨1150391, by rfl⟩ : syracuseStep 1533855 = 2300783) B2300783
theorem B1533863 : Blo 1532463 1533863 := bstep (se 1 (by rfl) ⟨1150397, by rfl⟩ : syracuseStep 1533863 = 2300795) B2300795
theorem B3451067 : Blo 1532463 3451067 := bstep (se 1 (by rfl) ⟨2588300, by rfl⟩ : syracuseStep 3451067 = 5176601) B5176601
theorem B4368647 : Blo 1532463 4368647 := bstep (se 1 (by rfl) ⟨3276485, by rfl⟩ : syracuseStep 4368647 = 6552971) B6552971
theorem B7760285 : Blo 1532463 7760285 := bstep (se 3 (by rfl) ⟨1455053, by rfl⟩ : syracuseStep 7760285 = 2910107) B2910107
theorem B4368829 : Blo 1532463 4368829 := bstep (se 3 (by rfl) ⟨819155, by rfl⟩ : syracuseStep 4368829 = 1638311) B1638311
theorem B1534439 : Blo 1532463 1534439 := bstep (se 1 (by rfl) ⟨1150829, by rfl⟩ : syracuseStep 1534439 = 2301659) B2301659
theorem B4368887 : Blo 1532463 4368887 := bstep (se 1 (by rfl) ⟨3276665, by rfl⟩ : syracuseStep 4368887 = 6553331) B6553331
theorem B6998845 : Blo 1532463 6998845 := bstep (se 3 (by rfl) ⟨1312283, by rfl⟩ : syracuseStep 6998845 = 2624567) B2624567
theorem B8293259 : Blo 1532463 8293259 := bstep (se 1 (by rfl) ⟨6219944, by rfl⟩ : syracuseStep 8293259 = 12439889) B12439889
theorem B3451967 : Blo 1532463 3451967 := bstep (se 1 (by rfl) ⟨2588975, by rfl⟩ : syracuseStep 3451967 = 5177951) B5177951
theorem B5172551 : Blo 1532463 5172551 := bstep (se 1 (by rfl) ⟨3879413, by rfl⟩ : syracuseStep 5172551 = 7758827) B7758827
theorem B7761257 : Blo 1532463 7761257 := bstep (se 2 (by rfl) ⟨2910471, by rfl⟩ : syracuseStep 7761257 = 5820943) B5820943
theorem B5320043 : Blo 1532463 5320043 := bstep (se 1 (by rfl) ⟨3990032, by rfl⟩ : syracuseStep 5320043 = 7980065) B7980065
theorem B5819759 : Blo 1532463 5819759 := bstep (se 1 (by rfl) ⟨4364819, by rfl⟩ : syracuseStep 5819759 = 8729639) B8729639
theorem B68185489 : Blo 1532463 68185489 := bstep (se 2 (by rfl) ⟨25569558, by rfl⟩ : syracuseStep 68185489 = 51139117) B51139117
theorem B17698499 : Blo 1532463 17698499 := bstep (se 1 (by rfl) ⟨13273874, by rfl⟩ : syracuseStep 17698499 = 26547749) B26547749
theorem B1724359 : Blo 1532463 1724359 := bstep (se 1 (by rfl) ⟨1293269, by rfl⟩ : syracuseStep 1724359 = 2586539) B2586539
theorem B2912287 : Blo 1532463 2912287 := bstep (se 1 (by rfl) ⟨2184215, by rfl⟩ : syracuseStep 2912287 = 4368431) B4368431
theorem B9957485 : Blo 1532463 9957485 := bstep (se 3 (by rfl) ⟨1867028, by rfl⟩ : syracuseStep 9957485 = 3734057) B3734057
theorem B1724719 : Blo 1532463 1724719 := bstep (se 1 (by rfl) ⟨1293539, by rfl⟩ : syracuseStep 1724719 = 2587079) B2587079
theorem B3682721 : Blo 1532463 3682721 := bstep (se 2 (by rfl) ⟨1381020, by rfl⟩ : syracuseStep 3682721 = 2762041) B2762041
theorem B6549929 : Blo 1532463 6549929 := bstep (se 2 (by rfl) ⟨2456223, by rfl⟩ : syracuseStep 6549929 = 4912447) B4912447
theorem B1724863 : Blo 1532463 1724863 := bstep (se 1 (by rfl) ⟨1293647, by rfl⟩ : syracuseStep 1724863 = 2587295) B2587295
theorem B5526071 : Blo 1532463 5526071 := bstep (se 1 (by rfl) ⟨4144553, by rfl⟩ : syracuseStep 5526071 = 8289107) B8289107
theorem B15741605 : Blo 1532463 15741605 := bstep (se 4 (by rfl) ⟨1475775, by rfl⟩ : syracuseStep 15741605 = 2951551) B2951551
theorem B7763039 : Blo 1532463 7763039 := bstep (se 1 (by rfl) ⟨5822279, by rfl⟩ : syracuseStep 7763039 = 11644559) B11644559
theorem B37311587 : Blo 1532463 37311587 := bstep (se 1 (by rfl) ⟨27983690, by rfl⟩ : syracuseStep 37311587 = 55967381) B55967381
theorem B2299049 : Blo 1532463 2299049 := bstep (se 2 (by rfl) ⟨862143, by rfl⟩ : syracuseStep 2299049 = 1724287) B1724287
theorem B2299115 : Blo 1532463 2299115 := bstep (se 1 (by rfl) ⟨1724336, by rfl⟩ : syracuseStep 2299115 = 3448673) B3448673
theorem B2299199 : Blo 1532463 2299199 := bstep (se 1 (by rfl) ⟨1724399, by rfl⟩ : syracuseStep 2299199 = 3448799) B3448799
theorem B4142447 : Blo 1532463 4142447 := bstep (se 1 (by rfl) ⟨3106835, by rfl⟩ : syracuseStep 4142447 = 6213671) B6213671
theorem B2332127 : Blo 1532463 2332127 := bstep (se 1 (by rfl) ⟨1749095, by rfl⟩ : syracuseStep 2332127 = 3498191) B3498191
theorem B2299391 : Blo 1532463 2299391 := bstep (se 1 (by rfl) ⟨1724543, by rfl⟩ : syracuseStep 2299391 = 3449087) B3449087
theorem B2586215 : Blo 1532463 2586215 := bstep (se 1 (by rfl) ⟨1939661, by rfl⟩ : syracuseStep 2586215 = 3879323) B3879323
theorem B2299499 : Blo 1532463 2299499 := bstep (se 1 (by rfl) ⟨1724624, by rfl⟩ : syracuseStep 2299499 = 3449249) B3449249
theorem B8853113 : Blo 1532463 8853113 := bstep (se 2 (by rfl) ⟨3319917, by rfl⟩ : syracuseStep 8853113 = 6639835) B6639835
theorem B5174927 : Blo 1532463 5174927 := bstep (se 1 (by rfl) ⟨3881195, by rfl⟩ : syracuseStep 5174927 = 7762391) B7762391
theorem B2299769 : Blo 1532463 2299769 := bstep (se 2 (by rfl) ⟨862413, by rfl⟩ : syracuseStep 2299769 = 1724827) B1724827
theorem B9820075 : Blo 1532463 9820075 := bstep (se 1 (by rfl) ⟨7365056, by rfl⟩ : syracuseStep 9820075 = 14730113) B14730113
theorem B5175305 : Blo 1532463 5175305 := bstep (se 2 (by rfl) ⟨1940739, by rfl⟩ : syracuseStep 5175305 = 3881479) B3881479
theorem B8730665 : Blo 1532463 8730665 := bstep (se 2 (by rfl) ⟨3273999, by rfl⟩ : syracuseStep 8730665 = 6547999) B6547999
theorem B2300015 : Blo 1532463 2300015 := bstep (se 1 (by rfl) ⟨1725011, by rfl⟩ : syracuseStep 2300015 = 3450023) B3450023
theorem B2300087 : Blo 1532463 2300087 := bstep (se 1 (by rfl) ⟨1725065, by rfl⟩ : syracuseStep 2300087 = 3450131) B3450131
theorem B16587119 : Blo 1532463 16587119 := bstep (se 1 (by rfl) ⟨12440339, by rfl⟩ : syracuseStep 16587119 = 24880679) B24880679
theorem B2455967 : Blo 1532463 2455967 := bstep (se 1 (by rfl) ⟨1841975, by rfl⟩ : syracuseStep 2455967 = 3683951) B3683951
theorem B2300507 : Blo 1532463 2300507 := bstep (se 1 (by rfl) ⟨1725380, by rfl⟩ : syracuseStep 2300507 = 3450761) B3450761
theorem B2300519 : Blo 1532463 2300519 := bstep (se 1 (by rfl) ⟨1725389, by rfl⟩ : syracuseStep 2300519 = 3450779) B3450779
theorem B2300543 : Blo 1532463 2300543 := bstep (se 1 (by rfl) ⟨1725407, by rfl⟩ : syracuseStep 2300543 = 3450815) B3450815
theorem B2300651 : Blo 1532463 2300651 := bstep (se 1 (by rfl) ⟨1725488, by rfl⟩ : syracuseStep 2300651 = 3450977) B3450977
theorem B2300681 : Blo 1532463 2300681 := bstep (se 2 (by rfl) ⟨862755, by rfl⟩ : syracuseStep 2300681 = 1725511) B1725511
theorem B2300921 : Blo 1532463 2300921 := bstep (se 2 (by rfl) ⟨862845, by rfl⟩ : syracuseStep 2300921 = 1725691) B1725691
theorem B9321497 : Blo 1532463 9321497 := bstep (se 2 (by rfl) ⟨3495561, by rfl⟩ : syracuseStep 9321497 = 6991123) B6991123
theorem B4365343 : Blo 1532463 4365343 := bstep (se 1 (by rfl) ⟨3274007, by rfl⟩ : syracuseStep 4365343 = 6548015) B6548015
theorem B6995105 : Blo 1532463 6995105 := bstep (se 2 (by rfl) ⟨2623164, by rfl⟩ : syracuseStep 6995105 = 5246329) B5246329
theorem B8731871 : Blo 1532463 8731871 := bstep (se 1 (by rfl) ⟨6548903, by rfl⟩ : syracuseStep 8731871 = 13097807) B13097807
theorem B1596667 : Blo 1532463 1596667 := bstep (se 1 (by rfl) ⟨1197500, by rfl⟩ : syracuseStep 1596667 = 2395001) B2395001
theorem B19651835 : Blo 1532463 19651835 := bstep (se 1 (by rfl) ⟨14738876, by rfl⟩ : syracuseStep 19651835 = 29477753) B29477753
theorem B22396513 : Blo 1532463 22396513 := bstep (se 2 (by rfl) ⟨8398692, by rfl⟩ : syracuseStep 22396513 = 16797385) B16797385
theorem B2301551 : Blo 1532463 2301551 := bstep (se 1 (by rfl) ⟨1726163, by rfl⟩ : syracuseStep 2301551 = 3452327) B3452327
theorem B2301671 : Blo 1532463 2301671 := bstep (se 1 (by rfl) ⟨1726253, by rfl⟩ : syracuseStep 2301671 = 3452507) B3452507
theorem B11648933 : Blo 1532463 11648933 := bstep (se 4 (by rfl) ⟨1092087, by rfl⟩ : syracuseStep 11648933 = 2184175) B2184175
theorem B7389161 : Blo 1532463 7389161 := bstep (se 2 (by rfl) ⟨2770935, by rfl⟩ : syracuseStep 7389161 = 5541871) B5541871
theorem B1941499 : Blo 1532463 1941499 := bstep (se 1 (by rfl) ⟨1456124, by rfl⟩ : syracuseStep 1941499 = 2912249) B2912249
theorem B3883049 : Blo 1532463 3883049 := bstep (se 2 (by rfl) ⟨1456143, by rfl⟩ : syracuseStep 3883049 = 2912287) B2912287
theorem B2457839 : Blo 1532463 2457839 := bstep (se 1 (by rfl) ⟨1843379, by rfl⟩ : syracuseStep 2457839 = 3686759) B3686759
theorem B18907411 : Blo 1532463 18907411 := bstep (se 1 (by rfl) ⟨14180558, by rfl⟩ : syracuseStep 18907411 = 28361117) B28361117
theorem B4366619 : Blo 1532463 4366619 := bstep (se 1 (by rfl) ⟨3274964, by rfl⟩ : syracuseStep 4366619 = 6549929) B6549929
theorem B11059523 : Blo 1532463 11059523 := bstep (se 1 (by rfl) ⟨8294642, by rfl⟩ : syracuseStep 11059523 = 16589285) B16589285
theorem B11649419 : Blo 1532463 11649419 := bstep (se 1 (by rfl) ⟨8737064, by rfl⟩ : syracuseStep 11649419 = 17474129) B17474129
theorem B10494403 : Blo 1532463 10494403 := bstep (se 1 (by rfl) ⟨7870802, by rfl⟩ : syracuseStep 10494403 = 15741605) B15741605
theorem B5825105 : Blo 1532463 5825105 := bstep (se 2 (by rfl) ⟨2184414, by rfl⟩ : syracuseStep 5825105 = 4368829) B4368829
theorem B3736201 : Blo 1532463 3736201 := bstep (se 2 (by rfl) ⟨1401075, by rfl⟩ : syracuseStep 3736201 = 2802151) B2802151
theorem B1532699 : Blo 1532463 1532699 := bstep (se 1 (by rfl) ⟨1149524, by rfl⟩ : syracuseStep 1532699 = 2299049) B2299049
theorem B5178167 : Blo 1532463 5178167 := bstep (se 1 (by rfl) ⟨3883625, by rfl⟩ : syracuseStep 5178167 = 7767251) B7767251
theorem B1532743 : Blo 1532463 1532743 := bstep (se 1 (by rfl) ⟨1149557, by rfl⟩ : syracuseStep 1532743 = 2299115) B2299115
theorem B1532799 : Blo 1532463 1532799 := bstep (se 1 (by rfl) ⟨1149599, by rfl⟩ : syracuseStep 1532799 = 2299199) B2299199
theorem B2761631 : Blo 1532463 2761631 := bstep (se 1 (by rfl) ⟨2071223, by rfl⟩ : syracuseStep 2761631 = 4142447) B4142447
theorem B1532927 : Blo 1532463 1532927 := bstep (se 1 (by rfl) ⟨1149695, by rfl⟩ : syracuseStep 1532927 = 2299391) B2299391
theorem B1532999 : Blo 1532463 1532999 := bstep (se 1 (by rfl) ⟨1149749, by rfl⟩ : syracuseStep 1532999 = 2299499) B2299499
theorem B9331793 : Blo 1532463 9331793 := bstep (se 2 (by rfl) ⟨3499422, by rfl⟩ : syracuseStep 9331793 = 6998845) B6998845
theorem B3449951 : Blo 1532463 3449951 := bstep (se 1 (by rfl) ⟨2587463, by rfl⟩ : syracuseStep 3449951 = 5174927) B5174927
theorem B13108331 : Blo 1532463 13108331 := bstep (se 1 (by rfl) ⟨9831248, by rfl⟩ : syracuseStep 13108331 = 19662497) B19662497
theorem B1533179 : Blo 1532463 1533179 := bstep (se 1 (by rfl) ⟨1149884, by rfl⟩ : syracuseStep 1533179 = 2299769) B2299769
theorem B3450203 : Blo 1532463 3450203 := bstep (se 1 (by rfl) ⟨2587652, by rfl⟩ : syracuseStep 3450203 = 5175305) B5175305
theorem B1533343 : Blo 1532463 1533343 := bstep (se 1 (by rfl) ⟨1150007, by rfl⟩ : syracuseStep 1533343 = 2300015) B2300015
theorem B1533391 : Blo 1532463 1533391 := bstep (se 1 (by rfl) ⟨1150043, by rfl⟩ : syracuseStep 1533391 = 2300087) B2300087
theorem B1533671 : Blo 1532463 1533671 := bstep (se 1 (by rfl) ⟨1150253, by rfl⟩ : syracuseStep 1533671 = 2300507) B2300507
theorem B1533679 : Blo 1532463 1533679 := bstep (se 1 (by rfl) ⟨1150259, by rfl⟩ : syracuseStep 1533679 = 2300519) B2300519
theorem B1533695 : Blo 1532463 1533695 := bstep (se 1 (by rfl) ⟨1150271, by rfl⟩ : syracuseStep 1533695 = 2300543) B2300543
theorem B1533767 : Blo 1532463 1533767 := bstep (se 1 (by rfl) ⟨1150325, by rfl⟩ : syracuseStep 1533767 = 2300651) B2300651
theorem B1533787 : Blo 1532463 1533787 := bstep (se 1 (by rfl) ⟨1150340, by rfl⟩ : syracuseStep 1533787 = 2300681) B2300681
theorem B1533947 : Blo 1532463 1533947 := bstep (se 1 (by rfl) ⟨1150460, by rfl⟩ : syracuseStep 1533947 = 2300921) B2300921
theorem B4663403 : Blo 1532463 4663403 := bstep (se 1 (by rfl) ⟨3497552, by rfl⟩ : syracuseStep 4663403 = 6995105) B6995105
theorem B29862017 : Blo 1532463 29862017 := bstep (se 2 (by rfl) ⟨11198256, by rfl⟩ : syracuseStep 29862017 = 22396513) B22396513
theorem B13101223 : Blo 1532463 13101223 := bstep (se 1 (by rfl) ⟨9825917, by rfl⟩ : syracuseStep 13101223 = 19651835) B19651835
theorem B1534367 : Blo 1532463 1534367 := bstep (se 1 (by rfl) ⟨1150775, by rfl⟩ : syracuseStep 1534367 = 2301551) B2301551
theorem B11798999 : Blo 1532463 11798999 := bstep (se 1 (by rfl) ⟨8849249, by rfl⟩ : syracuseStep 11798999 = 17698499) B17698499
theorem B1534447 : Blo 1532463 1534447 := bstep (se 1 (by rfl) ⟨1150835, by rfl⟩ : syracuseStep 1534447 = 2301671) B2301671
theorem B13093433 : Blo 1532463 13093433 := bstep (se 2 (by rfl) ⟨4910037, by rfl⟩ : syracuseStep 13093433 = 9820075) B9820075
theorem B4926107 : Blo 1532463 4926107 := bstep (se 1 (by rfl) ⟨3694580, by rfl⟩ : syracuseStep 4926107 = 7389161) B7389161
theorem B6638323 : Blo 1532463 6638323 := bstep (se 1 (by rfl) ⟨4978742, by rfl⟩ : syracuseStep 6638323 = 9957485) B9957485
theorem B5172335 : Blo 1532463 5172335 := bstep (se 1 (by rfl) ⟨3879251, by rfl⟩ : syracuseStep 5172335 = 7758503) B7758503
theorem B2911535 : Blo 1532463 2911535 := bstep (se 1 (by rfl) ⟨2183651, by rfl⟩ : syracuseStep 2911535 = 4367303) B4367303
theorem B24874391 : Blo 1532463 24874391 := bstep (se 1 (by rfl) ⟨18655793, by rfl⟩ : syracuseStep 24874391 = 37311587) B37311587
theorem B44232317 : Blo 1532463 44232317 := bstep (se 3 (by rfl) ⟨8293559, by rfl⟩ : syracuseStep 44232317 = 16587119) B16587119
theorem B1724143 : Blo 1532463 1724143 := bstep (se 1 (by rfl) ⟨1293107, by rfl⟩ : syracuseStep 1724143 = 2586215) B2586215
theorem B5902075 : Blo 1532463 5902075 := bstep (se 1 (by rfl) ⟨4426556, by rfl⟩ : syracuseStep 5902075 = 8853113) B8853113
theorem B6549245 : Blo 1532463 6549245 := bstep (se 3 (by rfl) ⟨1227983, by rfl⟩ : syracuseStep 6549245 = 2455967) B2455967
theorem B5820443 : Blo 1532463 5820443 := bstep (se 1 (by rfl) ⟨4365332, by rfl⟩ : syracuseStep 5820443 = 8730665) B8730665
theorem B5820457 : Blo 1532463 5820457 := bstep (se 2 (by rfl) ⟨2182671, by rfl⟩ : syracuseStep 5820457 = 4365343) B4365343
theorem B3879049 : Blo 1532463 3879049 := bstep (se 2 (by rfl) ⟨1454643, by rfl⟩ : syracuseStep 3879049 = 2909287) B2909287
theorem B2912431 : Blo 1532463 2912431 := bstep (se 1 (by rfl) ⟨2184323, by rfl⟩ : syracuseStep 2912431 = 4368647) B4368647
theorem B5173523 : Blo 1532463 5173523 := bstep (se 1 (by rfl) ⟨3880142, by rfl⟩ : syracuseStep 5173523 = 7760285) B7760285
theorem B2912591 : Blo 1532463 2912591 := bstep (se 1 (by rfl) ⟨2184443, by rfl⟩ : syracuseStep 2912591 = 4368887) B4368887
theorem B6214331 : Blo 1532463 6214331 := bstep (se 1 (by rfl) ⟨4660748, by rfl⟩ : syracuseStep 6214331 = 9321497) B9321497
theorem B5821247 : Blo 1532463 5821247 := bstep (se 1 (by rfl) ⟨4365935, by rfl⟩ : syracuseStep 5821247 = 8731871) B8731871
theorem B5174171 : Blo 1532463 5174171 := bstep (se 1 (by rfl) ⟨3880628, by rfl⟩ : syracuseStep 5174171 = 7761257) B7761257
theorem B3879839 : Blo 1532463 3879839 := bstep (se 1 (by rfl) ⟨2909879, by rfl⟩ : syracuseStep 3879839 = 5819759) B5819759
theorem B2299145 : Blo 1532463 2299145 := bstep (se 2 (by rfl) ⟨862179, by rfl⟩ : syracuseStep 2299145 = 1724359) B1724359
theorem B62919989 : Blo 1532463 62919989 := bstep (se 5 (by rfl) ⟨2949374, by rfl⟩ : syracuseStep 62919989 = 5898749) B5898749
theorem B5248543 : Blo 1532463 5248543 := bstep (se 1 (by rfl) ⟨3936407, by rfl⟩ : syracuseStep 5248543 = 7872815) B7872815
theorem B2455147 : Blo 1532463 2455147 := bstep (se 1 (by rfl) ⟨1841360, by rfl⟩ : syracuseStep 2455147 = 3682721) B3682721
theorem B3684047 : Blo 1532463 3684047 := bstep (se 1 (by rfl) ⟨2763035, by rfl⟩ : syracuseStep 3684047 = 5526071) B5526071
theorem B2299625 : Blo 1532463 2299625 := bstep (se 2 (by rfl) ⟨862359, by rfl⟩ : syracuseStep 2299625 = 1724719) B1724719
theorem B2299817 : Blo 1532463 2299817 := bstep (se 2 (by rfl) ⟨862431, by rfl⟩ : syracuseStep 2299817 = 1724863) B1724863
theorem B2299883 : Blo 1532463 2299883 := bstep (se 1 (by rfl) ⟨1724912, by rfl⟩ : syracuseStep 2299883 = 3449825) B3449825
theorem B5175359 : Blo 1532463 5175359 := bstep (se 1 (by rfl) ⟨3881519, by rfl⟩ : syracuseStep 5175359 = 7763039) B7763039
theorem B1554751 : Blo 1532463 1554751 := bstep (se 1 (by rfl) ⟨1166063, by rfl⟩ : syracuseStep 1554751 = 2332127) B2332127
theorem B2300399 : Blo 1532463 2300399 := bstep (se 1 (by rfl) ⟨1725299, by rfl⟩ : syracuseStep 2300399 = 3450599) B3450599
theorem B2300711 : Blo 1532463 2300711 := bstep (se 1 (by rfl) ⟨1725533, by rfl⟩ : syracuseStep 2300711 = 3451067) B3451067
theorem B2128889 : Blo 1532463 2128889 := bstep (se 2 (by rfl) ⟨798333, by rfl⟩ : syracuseStep 2128889 = 1596667) B1596667
theorem B90913985 : Blo 1532463 90913985 := bstep (se 2 (by rfl) ⟨34092744, by rfl⟩ : syracuseStep 90913985 = 68185489) B68185489
theorem B5528839 : Blo 1532463 5528839 := bstep (se 1 (by rfl) ⟨4146629, by rfl⟩ : syracuseStep 5528839 = 8293259) B8293259
theorem B167927053 : Blo 1532463 167927053 := bstep (se 3 (by rfl) ⟨31486322, by rfl⟩ : syracuseStep 167927053 = 62972645) B62972645
theorem B2301311 : Blo 1532463 2301311 := bstep (se 1 (by rfl) ⟨1725983, by rfl⟩ : syracuseStep 2301311 = 3451967) B3451967
theorem B50445821 : Blo 1532463 50445821 := bstep (se 3 (by rfl) ⟨9458591, by rfl⟩ : syracuseStep 50445821 = 18917183) B18917183
theorem B99474965 : Blo 1532463 99474965 := bstep (se 6 (by rfl) ⟨2331444, by rfl⟩ : syracuseStep 99474965 = 4662889) B4662889
theorem B3448367 : Blo 1532463 3448367 := bstep (se 1 (by rfl) ⟨2586275, by rfl⟩ : syracuseStep 3448367 = 5172551) B5172551
theorem B3546695 : Blo 1532463 3546695 := bstep (se 1 (by rfl) ⟨2660021, by rfl⟩ : syracuseStep 3546695 = 5320043) B5320043
theorem B7765955 : Blo 1532463 7765955 := bstep (se 1 (by rfl) ⟨5824466, by rfl⟩ : syracuseStep 7765955 = 11648933) B11648933
theorem B2588665 : Blo 1532463 2588665 := bstep (se 2 (by rfl) ⟨970749, by rfl⟩ : syracuseStep 2588665 = 1941499) B1941499
theorem B2588699 : Blo 1532463 2588699 := bstep (se 1 (by rfl) ⟨1941524, by rfl⟩ : syracuseStep 2588699 = 3883049) B3883049
theorem B1638559 : Blo 1532463 1638559 := bstep (se 1 (by rfl) ⟨1228919, by rfl⟩ : syracuseStep 1638559 = 2457839) B2457839
theorem B3449015 : Blo 1532463 3449015 := bstep (se 1 (by rfl) ⟨2586761, by rfl⟩ : syracuseStep 3449015 = 5173523) B5173523
theorem B7373015 : Blo 1532463 7373015 := bstep (se 1 (by rfl) ⟨5529761, by rfl⟩ : syracuseStep 7373015 = 11059523) B11059523
theorem B1941727 : Blo 1532463 1941727 := bstep (se 1 (by rfl) ⟨1456295, by rfl⟩ : syracuseStep 1941727 = 2912591) B2912591
theorem B3883241 : Blo 1532463 3883241 := bstep (se 2 (by rfl) ⟨1456215, by rfl⟩ : syracuseStep 3883241 = 2912431) B2912431
theorem B7766279 : Blo 1532463 7766279 := bstep (se 1 (by rfl) ⟨5824709, by rfl⟩ : syracuseStep 7766279 = 11649419) B11649419
theorem B3883403 : Blo 1532463 3883403 := bstep (se 1 (by rfl) ⟨2912552, by rfl⟩ : syracuseStep 3883403 = 5825105) B5825105
theorem B2073001 : Blo 1532463 2073001 := bstep (se 2 (by rfl) ⟨777375, by rfl⟩ : syracuseStep 2073001 = 1554751) B1554751
theorem B3449447 : Blo 1532463 3449447 := bstep (se 1 (by rfl) ⟨2587085, by rfl⟩ : syracuseStep 3449447 = 5174171) B5174171
theorem B1532763 : Blo 1532463 1532763 := bstep (se 1 (by rfl) ⟨1149572, by rfl⟩ : syracuseStep 1532763 = 2299145) B2299145
theorem B4981601 : Blo 1532463 4981601 := bstep (se 2 (by rfl) ⟨1868100, by rfl⟩ : syracuseStep 4981601 = 3736201) B3736201
theorem B66331709 : Blo 1532463 66331709 := bstep (se 3 (by rfl) ⟨12437195, by rfl⟩ : syracuseStep 66331709 = 24874391) B24874391
theorem B1533083 : Blo 1532463 1533083 := bstep (se 1 (by rfl) ⟨1149812, by rfl⟩ : syracuseStep 1533083 = 2299625) B2299625
theorem B1533211 : Blo 1532463 1533211 := bstep (se 1 (by rfl) ⟨1149908, by rfl⟩ : syracuseStep 1533211 = 2299817) B2299817
theorem B1533255 : Blo 1532463 1533255 := bstep (se 1 (by rfl) ⟨1149941, by rfl⟩ : syracuseStep 1533255 = 2299883) B2299883
theorem B3450239 : Blo 1532463 3450239 := bstep (se 1 (by rfl) ⟨2587679, by rfl⟩ : syracuseStep 3450239 = 5175359) B5175359
theorem B19908011 : Blo 1532463 19908011 := bstep (se 1 (by rfl) ⟨14931008, by rfl⟩ : syracuseStep 19908011 = 29862017) B29862017
theorem B7865999 : Blo 1532463 7865999 := bstep (se 1 (by rfl) ⟨5899499, by rfl⟩ : syracuseStep 7865999 = 11798999) B11798999
theorem B1533599 : Blo 1532463 1533599 := bstep (se 1 (by rfl) ⟨1150199, by rfl⟩ : syracuseStep 1533599 = 2300399) B2300399
theorem B1533807 : Blo 1532463 1533807 := bstep (se 1 (by rfl) ⟨1150355, by rfl⟩ : syracuseStep 1533807 = 2300711) B2300711
theorem B9824125 : Blo 1532463 9824125 := bstep (se 3 (by rfl) ⟨1842023, by rfl⟩ : syracuseStep 9824125 = 3684047) B3684047
theorem B6998057 : Blo 1532463 6998057 := bstep (se 2 (by rfl) ⟨2624271, by rfl⟩ : syracuseStep 6998057 = 5248543) B5248543
theorem B1534207 : Blo 1532463 1534207 := bstep (se 1 (by rfl) ⟨1150655, by rfl⟩ : syracuseStep 1534207 = 2301311) B2301311
theorem B33630547 : Blo 1532463 33630547 := bstep (se 1 (by rfl) ⟨25222910, by rfl⟩ : syracuseStep 33630547 = 50445821) B50445821
theorem B66316643 : Blo 1532463 66316643 := bstep (se 1 (by rfl) ⟨49737482, by rfl⟩ : syracuseStep 66316643 = 99474965) B99474965
theorem B55970149 : Blo 1532463 55970149 := bstep (se 4 (by rfl) ⟨5247201, by rfl⟩ : syracuseStep 55970149 = 10494403) B10494403
theorem B3451553 : Blo 1532463 3451553 := bstep (se 2 (by rfl) ⟨1294332, by rfl⟩ : syracuseStep 3451553 = 2588665) B2588665
theorem B7760609 : Blo 1532463 7760609 := bstep (se 2 (by rfl) ⟨2910228, by rfl⟩ : syracuseStep 7760609 = 5820457) B5820457
theorem B5172065 : Blo 1532463 5172065 := bstep (se 2 (by rfl) ⟨1939524, by rfl⟩ : syracuseStep 5172065 = 3879049) B3879049
theorem B2911079 : Blo 1532463 2911079 := bstep (se 1 (by rfl) ⟨2183309, by rfl⟩ : syracuseStep 2911079 = 4366619) B4366619
theorem B17468297 : Blo 1532463 17468297 := bstep (se 2 (by rfl) ⟨6550611, by rfl⟩ : syracuseStep 17468297 = 13101223) B13101223
theorem B25209881 : Blo 1532463 25209881 := bstep (se 2 (by rfl) ⟨9453705, by rfl⟩ : syracuseStep 25209881 = 18907411) B18907411
theorem B3452111 : Blo 1532463 3452111 := bstep (se 1 (by rfl) ⟨2589083, by rfl⟩ : syracuseStep 3452111 = 5178167) B5178167
theorem B6221195 : Blo 1532463 6221195 := bstep (se 1 (by rfl) ⟨4665896, by rfl⟩ : syracuseStep 6221195 = 9331793) B9331793
theorem B41946659 : Blo 1532463 41946659 := bstep (se 1 (by rfl) ⟨31459994, by rfl⟩ : syracuseStep 41946659 = 62919989) B62919989
theorem B8851097 : Blo 1532463 8851097 := bstep (se 2 (by rfl) ⟨3319161, by rfl⟩ : syracuseStep 8851097 = 6638323) B6638323
theorem B31477733 : Blo 1532463 31477733 := bstep (se 4 (by rfl) ⟨2951037, by rfl⟩ : syracuseStep 31477733 = 5902075) B5902075
theorem B3108935 : Blo 1532463 3108935 := bstep (se 1 (by rfl) ⟨2331701, by rfl⟩ : syracuseStep 3108935 = 4663403) B4663403
theorem B8728955 : Blo 1532463 8728955 := bstep (se 1 (by rfl) ⟨6546716, by rfl⟩ : syracuseStep 8728955 = 13093433) B13093433
theorem B60609323 : Blo 1532463 60609323 := bstep (se 1 (by rfl) ⟨45456992, by rfl⟩ : syracuseStep 60609323 = 90913985) B90913985
theorem B3273529 : Blo 1532463 3273529 := bstep (se 2 (by rfl) ⟨1227573, by rfl⟩ : syracuseStep 3273529 = 2455147) B2455147
theorem B2298857 : Blo 1532463 2298857 := bstep (se 2 (by rfl) ⟨862071, by rfl⟩ : syracuseStep 2298857 = 1724143) B1724143
theorem B2298911 : Blo 1532463 2298911 := bstep (se 1 (by rfl) ⟨1724183, by rfl⟩ : syracuseStep 2298911 = 3448367) B3448367
theorem B2364463 : Blo 1532463 2364463 := bstep (se 1 (by rfl) ⟨1773347, by rfl⟩ : syracuseStep 2364463 = 3546695) B3546695
theorem B29488211 : Blo 1532463 29488211 := bstep (se 1 (by rfl) ⟨22116158, by rfl⟩ : syracuseStep 29488211 = 44232317) B44232317
theorem B3880295 : Blo 1532463 3880295 := bstep (se 1 (by rfl) ⟨2910221, by rfl⟩ : syracuseStep 3880295 = 5820443) B5820443
theorem B3880831 : Blo 1532463 3880831 := bstep (se 1 (by rfl) ⟨2910623, by rfl⟩ : syracuseStep 3880831 = 5821247) B5821247
theorem B1841087 : Blo 1532463 1841087 := bstep (se 1 (by rfl) ⟨1380815, by rfl⟩ : syracuseStep 1841087 = 2761631) B2761631
theorem B2586559 : Blo 1532463 2586559 := bstep (se 1 (by rfl) ⟨1939919, by rfl⟩ : syracuseStep 2586559 = 3879839) B3879839
theorem B2299967 : Blo 1532463 2299967 := bstep (se 1 (by rfl) ⟨1724975, by rfl⟩ : syracuseStep 2299967 = 3449951) B3449951
theorem B8738887 : Blo 1532463 8738887 := bstep (se 1 (by rfl) ⟨6554165, by rfl⟩ : syracuseStep 8738887 = 13108331) B13108331
theorem B2300135 : Blo 1532463 2300135 := bstep (se 1 (by rfl) ⟨1725101, by rfl⟩ : syracuseStep 2300135 = 3450203) B3450203
theorem B7371785 : Blo 1532463 7371785 := bstep (se 2 (by rfl) ⟨2764419, by rfl⟩ : syracuseStep 7371785 = 5528839) B5528839
theorem B223902737 : Blo 1532463 223902737 := bstep (se 2 (by rfl) ⟨83963526, by rfl⟩ : syracuseStep 223902737 = 167927053) B167927053
theorem B3284071 : Blo 1532463 3284071 := bstep (se 1 (by rfl) ⟨2463053, by rfl⟩ : syracuseStep 3284071 = 4926107) B4926107
theorem B16571549 : Blo 1532463 16571549 := bstep (se 3 (by rfl) ⟨3107165, by rfl⟩ : syracuseStep 16571549 = 6214331) B6214331
theorem B3448223 : Blo 1532463 3448223 := bstep (se 1 (by rfl) ⟨2586167, by rfl⟩ : syracuseStep 3448223 = 5172335) B5172335
theorem B1941023 : Blo 1532463 1941023 := bstep (se 1 (by rfl) ⟨1455767, by rfl⟩ : syracuseStep 1941023 = 2911535) B2911535
theorem B4366163 : Blo 1532463 4366163 := bstep (se 1 (by rfl) ⟨3274622, by rfl⟩ : syracuseStep 4366163 = 6549245) B6549245
theorem B5177303 : Blo 1532463 5177303 := bstep (se 1 (by rfl) ⟨3882977, by rfl⟩ : syracuseStep 5177303 = 7765955) B7765955
theorem B5677037 : Blo 1532463 5677037 := bstep (se 3 (by rfl) ⟨1064444, by rfl⟩ : syracuseStep 5677037 = 2128889) B2128889
theorem B2072623 : Blo 1532463 2072623 := bstep (se 1 (by rfl) ⟨1554467, by rfl⟩ : syracuseStep 2072623 = 3108935) B3108935
theorem B4915343 : Blo 1532463 4915343 := bstep (se 1 (by rfl) ⟨3686507, by rfl⟩ : syracuseStep 4915343 = 7373015) B7373015
theorem B2588827 : Blo 1532463 2588827 := bstep (se 1 (by rfl) ⟨1941620, by rfl⟩ : syracuseStep 2588827 = 3883241) B3883241
theorem B5177519 : Blo 1532463 5177519 := bstep (se 1 (by rfl) ⟨3883139, by rfl⟩ : syracuseStep 5177519 = 7766279) B7766279
theorem B2588935 : Blo 1532463 2588935 := bstep (se 1 (by rfl) ⟨1941701, by rfl⟩ : syracuseStep 2588935 = 3883403) B3883403
theorem B2588969 : Blo 1532463 2588969 := bstep (se 2 (by rfl) ⟨970863, by rfl⟩ : syracuseStep 2588969 = 1941727) B1941727
theorem B17515045 : Blo 1532463 17515045 := bstep (se 4 (by rfl) ⟨1642035, by rfl⟩ : syracuseStep 17515045 = 3284071) B3284071
theorem B1532571 : Blo 1532463 1532571 := bstep (se 1 (by rfl) ⟨1149428, by rfl⟩ : syracuseStep 1532571 = 2298857) B2298857
theorem B1532607 : Blo 1532463 1532607 := bstep (se 1 (by rfl) ⟨1149455, by rfl⟩ : syracuseStep 1532607 = 2298911) B2298911
theorem B44221139 : Blo 1532463 44221139 := bstep (se 1 (by rfl) ⟨33165854, by rfl⟩ : syracuseStep 44221139 = 66331709) B66331709
theorem B13272007 : Blo 1532463 13272007 := bstep (se 1 (by rfl) ⟨9954005, by rfl⟩ : syracuseStep 13272007 = 19908011) B19908011
theorem B5243999 : Blo 1532463 5243999 := bstep (se 1 (by rfl) ⟨3932999, by rfl⟩ : syracuseStep 5243999 = 7865999) B7865999
theorem B1533311 : Blo 1532463 1533311 := bstep (se 1 (by rfl) ⟨1149983, by rfl⟩ : syracuseStep 1533311 = 2299967) B2299967
theorem B1533423 : Blo 1532463 1533423 := bstep (se 1 (by rfl) ⟨1150067, by rfl⟩ : syracuseStep 1533423 = 2300135) B2300135
theorem B149268491 : Blo 1532463 149268491 := bstep (se 1 (by rfl) ⟨111951368, by rfl⟩ : syracuseStep 149268491 = 223902737) B223902737
theorem B11643101 : Blo 1532463 11643101 := bstep (se 3 (by rfl) ⟨2183081, by rfl⟩ : syracuseStep 11643101 = 4366163) B4366163
theorem B4147463 : Blo 1532463 4147463 := bstep (se 1 (by rfl) ⟨3110597, by rfl⟩ : syracuseStep 4147463 = 6221195) B6221195
theorem B5900731 : Blo 1532463 5900731 := bstep (se 1 (by rfl) ⟨4425548, by rfl⟩ : syracuseStep 5900731 = 8851097) B8851097
theorem B4909565 : Blo 1532463 4909565 := bstep (se 3 (by rfl) ⟨920543, by rfl⟩ : syracuseStep 4909565 = 1841087) B1841087
theorem B3451535 : Blo 1532463 3451535 := bstep (se 1 (by rfl) ⟨2588651, by rfl⟩ : syracuseStep 3451535 = 5177303) B5177303
theorem B11651849 : Blo 1532463 11651849 := bstep (se 2 (by rfl) ⟨4369443, by rfl⟩ : syracuseStep 11651849 = 8738887) B8738887
theorem B12610469 : Blo 1532463 12610469 := bstep (se 4 (by rfl) ⟨1182231, by rfl⟩ : syracuseStep 12610469 = 2364463) B2364463
theorem B5819303 : Blo 1532463 5819303 := bstep (se 1 (by rfl) ⟨4364477, by rfl⟩ : syracuseStep 5819303 = 8728955) B8728955
theorem B40406215 : Blo 1532463 40406215 := bstep (se 1 (by rfl) ⟨30304661, by rfl⟩ : syracuseStep 40406215 = 60609323) B60609323
theorem B2764001 : Blo 1532463 2764001 := bstep (se 2 (by rfl) ⟨1036500, by rfl⟩ : syracuseStep 2764001 = 2073001) B2073001
theorem B4665371 : Blo 1532463 4665371 := bstep (se 1 (by rfl) ⟨3499028, by rfl⟩ : syracuseStep 4665371 = 6998057) B6998057
theorem B5173739 : Blo 1532463 5173739 := bstep (se 1 (by rfl) ⟨3880304, by rfl⟩ : syracuseStep 5173739 = 7760609) B7760609
theorem B11645531 : Blo 1532463 11645531 := bstep (se 1 (by rfl) ⟨8734148, by rfl⟩ : syracuseStep 11645531 = 17468297) B17468297
theorem B16806587 : Blo 1532463 16806587 := bstep (se 1 (by rfl) ⟨12604940, by rfl⟩ : syracuseStep 16806587 = 25209881) B25209881
theorem B11047699 : Blo 1532463 11047699 := bstep (se 1 (by rfl) ⟨8285774, by rfl⟩ : syracuseStep 11047699 = 16571549) B16571549
theorem B13284269 : Blo 1532463 13284269 := bstep (se 3 (by rfl) ⟨2490800, by rfl⟩ : syracuseStep 13284269 = 4981601) B4981601
theorem B7762877 : Blo 1532463 7762877 := bstep (se 3 (by rfl) ⟨1455539, by rfl⟩ : syracuseStep 7762877 = 2911079) B2911079
theorem B2298815 : Blo 1532463 2298815 := bstep (se 1 (by rfl) ⟨1724111, by rfl⟩ : syracuseStep 2298815 = 3448223) B3448223
theorem B27964439 : Blo 1532463 27964439 := bstep (se 1 (by rfl) ⟨20973329, by rfl⟩ : syracuseStep 27964439 = 41946659) B41946659
theorem B5174441 : Blo 1532463 5174441 := bstep (se 2 (by rfl) ⟨1940415, by rfl⟩ : syracuseStep 5174441 = 3880831) B3880831
theorem B20985155 : Blo 1532463 20985155 := bstep (se 1 (by rfl) ⟨15738866, by rfl⟩ : syracuseStep 20985155 = 31477733) B31477733
theorem B1725799 : Blo 1532463 1725799 := bstep (se 1 (by rfl) ⟨1294349, by rfl⟩ : syracuseStep 1725799 = 2588699) B2588699
theorem B2299343 : Blo 1532463 2299343 := bstep (se 1 (by rfl) ⟨1724507, by rfl⟩ : syracuseStep 2299343 = 3449015) B3449015
theorem B2184745 : Blo 1532463 2184745 := bstep (se 2 (by rfl) ⟨819279, by rfl⟩ : syracuseStep 2184745 = 1638559) B1638559
theorem B2299631 : Blo 1532463 2299631 := bstep (se 1 (by rfl) ⟨1724723, by rfl⟩ : syracuseStep 2299631 = 3449447) B3449447
theorem B44840729 : Blo 1532463 44840729 := bstep (se 2 (by rfl) ⟨16815273, by rfl⟩ : syracuseStep 44840729 = 33630547) B33630547
theorem B74626865 : Blo 1532463 74626865 := bstep (se 2 (by rfl) ⟨27985074, by rfl⟩ : syracuseStep 74626865 = 55970149) B55970149
theorem B19658807 : Blo 1532463 19658807 := bstep (se 1 (by rfl) ⟨14744105, by rfl⟩ : syracuseStep 19658807 = 29488211) B29488211
theorem B2586863 : Blo 1532463 2586863 := bstep (se 1 (by rfl) ⟨1940147, by rfl⟩ : syracuseStep 2586863 = 3880295) B3880295
theorem B2300159 : Blo 1532463 2300159 := bstep (se 1 (by rfl) ⟨1725119, by rfl⟩ : syracuseStep 2300159 = 3450239) B3450239
theorem B4364705 : Blo 1532463 4364705 := bstep (se 2 (by rfl) ⟨1636764, by rfl⟩ : syracuseStep 4364705 = 3273529) B3273529
theorem B5176061 : Blo 1532463 5176061 := bstep (se 3 (by rfl) ⟨970511, by rfl⟩ : syracuseStep 5176061 = 1941023) B1941023
theorem B44211095 : Blo 1532463 44211095 := bstep (se 1 (by rfl) ⟨33158321, by rfl⟩ : syracuseStep 44211095 = 66316643) B66316643
theorem B2301035 : Blo 1532463 2301035 := bstep (se 1 (by rfl) ⟨1725776, by rfl⟩ : syracuseStep 2301035 = 3451553) B3451553
theorem B3448043 : Blo 1532463 3448043 := bstep (se 1 (by rfl) ⟨2586032, by rfl⟩ : syracuseStep 3448043 = 5172065) B5172065
theorem B4914523 : Blo 1532463 4914523 := bstep (se 1 (by rfl) ⟨3685892, by rfl⟩ : syracuseStep 4914523 = 7371785) B7371785
theorem B2301407 : Blo 1532463 2301407 := bstep (se 1 (by rfl) ⟨1726055, by rfl⟩ : syracuseStep 2301407 = 3452111) B3452111
theorem B13098833 : Blo 1532463 13098833 := bstep (se 2 (by rfl) ⟨4912062, by rfl⟩ : syracuseStep 13098833 = 9824125) B9824125
theorem B3448745 : Blo 1532463 3448745 := bstep (se 2 (by rfl) ⟨1293279, by rfl⟩ : syracuseStep 3448745 = 2586559) B2586559
theorem B3784691 : Blo 1532463 3784691 := bstep (se 1 (by rfl) ⟨2838518, by rfl⟩ : syracuseStep 3784691 = 5677037) B5677037
theorem B93413573 : Blo 1532463 93413573 := bstep (se 4 (by rfl) ⟨8757522, by rfl⟩ : syracuseStep 93413573 = 17515045) B17515045
theorem B13983997 : Blo 1532463 13983997 := bstep (se 3 (by rfl) ⟨2621999, by rfl⟩ : syracuseStep 13983997 = 5243999) B5243999
theorem B3449159 : Blo 1532463 3449159 := bstep (se 1 (by rfl) ⟨2586869, by rfl⟩ : syracuseStep 3449159 = 5173739) B5173739
theorem B13107581 : Blo 1532463 13107581 := bstep (se 3 (by rfl) ⟨2457671, by rfl⟩ : syracuseStep 13107581 = 4915343) B4915343
theorem B8856179 : Blo 1532463 8856179 := bstep (se 1 (by rfl) ⟨6642134, by rfl⟩ : syracuseStep 8856179 = 13284269) B13284269
theorem B1532543 : Blo 1532463 1532543 := bstep (se 1 (by rfl) ⟨1149407, by rfl⟩ : syracuseStep 1532543 = 2298815) B2298815
theorem B11059901 : Blo 1532463 11059901 := bstep (se 3 (by rfl) ⟨2073731, by rfl⟩ : syracuseStep 11059901 = 4147463) B4147463
theorem B3449627 : Blo 1532463 3449627 := bstep (se 1 (by rfl) ⟨2587220, by rfl⟩ : syracuseStep 3449627 = 5174441) B5174441
theorem B1532895 : Blo 1532463 1532895 := bstep (se 1 (by rfl) ⟨1149671, by rfl⟩ : syracuseStep 1532895 = 2299343) B2299343
theorem B14730265 : Blo 1532463 14730265 := bstep (se 2 (by rfl) ⟨5523849, by rfl⟩ : syracuseStep 14730265 = 11047699) B11047699
theorem B1533087 : Blo 1532463 1533087 := bstep (se 1 (by rfl) ⟨1149815, by rfl⟩ : syracuseStep 1533087 = 2299631) B2299631
theorem B29893819 : Blo 1532463 29893819 := bstep (se 1 (by rfl) ⟨22420364, by rfl⟩ : syracuseStep 29893819 = 44840729) B44840729
theorem B49751243 : Blo 1532463 49751243 := bstep (se 1 (by rfl) ⟨37313432, by rfl⟩ : syracuseStep 49751243 = 74626865) B74626865
theorem B17696009 : Blo 1532463 17696009 := bstep (se 2 (by rfl) ⟨6636003, by rfl⟩ : syracuseStep 17696009 = 13272007) B13272007
theorem B1533439 : Blo 1532463 1533439 := bstep (se 1 (by rfl) ⟨1150079, by rfl⟩ : syracuseStep 1533439 = 2300159) B2300159
theorem B3450707 : Blo 1532463 3450707 := bstep (se 1 (by rfl) ⟨2588030, by rfl⟩ : syracuseStep 3450707 = 5176061) B5176061
theorem B7767899 : Blo 1532463 7767899 := bstep (se 1 (by rfl) ⟨5825924, by rfl⟩ : syracuseStep 7767899 = 11651849) B11651849
theorem B8406979 : Blo 1532463 8406979 := bstep (se 1 (by rfl) ⟨6305234, by rfl⟩ : syracuseStep 8406979 = 12610469) B12610469
theorem B1534023 : Blo 1532463 1534023 := bstep (se 1 (by rfl) ⟨1150517, by rfl⟩ : syracuseStep 1534023 = 2301035) B2301035
theorem B1534271 : Blo 1532463 1534271 := bstep (se 1 (by rfl) ⟨1150703, by rfl⟩ : syracuseStep 1534271 = 2301407) B2301407
theorem B2763497 : Blo 1532463 2763497 := bstep (se 2 (by rfl) ⟨1036311, by rfl⟩ : syracuseStep 2763497 = 2072623) B2072623
theorem B3451679 : Blo 1532463 3451679 := bstep (se 1 (by rfl) ⟨2588759, by rfl⟩ : syracuseStep 3451679 = 5177519) B5177519
theorem B3451769 : Blo 1532463 3451769 := bstep (se 2 (by rfl) ⟨1294413, by rfl⟩ : syracuseStep 3451769 = 2588827) B2588827
theorem B3451913 : Blo 1532463 3451913 := bstep (se 2 (by rfl) ⟨1294467, by rfl⟩ : syracuseStep 3451913 = 2588935) B2588935
theorem B99512327 : Blo 1532463 99512327 := bstep (se 1 (by rfl) ⟨74634245, by rfl⟩ : syracuseStep 99512327 = 149268491) B149268491
theorem B7762067 : Blo 1532463 7762067 := bstep (se 1 (by rfl) ⟨5821550, by rfl⟩ : syracuseStep 7762067 = 11643101) B11643101
theorem B1724575 : Blo 1532463 1724575 := bstep (se 1 (by rfl) ⟨1293431, by rfl⟩ : syracuseStep 1724575 = 2586863) B2586863
theorem B53874953 : Blo 1532463 53874953 := bstep (se 2 (by rfl) ⟨20203107, by rfl⟩ : syracuseStep 53874953 = 40406215) B40406215
theorem B3273043 : Blo 1532463 3273043 := bstep (se 1 (by rfl) ⟨2454782, by rfl⟩ : syracuseStep 3273043 = 4909565) B4909565
theorem B3879535 : Blo 1532463 3879535 := bstep (se 1 (by rfl) ⟨2909651, by rfl⟩ : syracuseStep 3879535 = 5819303) B5819303
theorem B2912993 : Blo 1532463 2912993 := bstep (se 2 (by rfl) ⟨1092372, by rfl⟩ : syracuseStep 2912993 = 2184745) B2184745
theorem B2298695 : Blo 1532463 2298695 := bstep (se 1 (by rfl) ⟨1724021, by rfl⟩ : syracuseStep 2298695 = 3448043) B3448043
theorem B31470565 : Blo 1532463 31470565 := bstep (se 4 (by rfl) ⟨2950365, by rfl⟩ : syracuseStep 31470565 = 5900731) B5900731
theorem B2299163 : Blo 1532463 2299163 := bstep (se 1 (by rfl) ⟨1724372, by rfl⟩ : syracuseStep 2299163 = 3448745) B3448745
theorem B12440989 : Blo 1532463 12440989 := bstep (se 3 (by rfl) ⟨2332685, by rfl⟩ : syracuseStep 12440989 = 4665371) B4665371
theorem B1725979 : Blo 1532463 1725979 := bstep (se 1 (by rfl) ⟨1294484, by rfl⟩ : syracuseStep 1725979 = 2588969) B2588969
theorem B7763687 : Blo 1532463 7763687 := bstep (se 1 (by rfl) ⟨5822765, by rfl⟩ : syracuseStep 7763687 = 11645531) B11645531
theorem B29480759 : Blo 1532463 29480759 := bstep (se 1 (by rfl) ⟨22110569, by rfl⟩ : syracuseStep 29480759 = 44221139) B44221139
theorem B7370669 : Blo 1532463 7370669 := bstep (se 3 (by rfl) ⟨1382000, by rfl⟩ : syracuseStep 7370669 = 2764001) B2764001
theorem B5175251 : Blo 1532463 5175251 := bstep (se 1 (by rfl) ⟨3881438, by rfl⟩ : syracuseStep 5175251 = 7762877) B7762877
theorem B18642959 : Blo 1532463 18642959 := bstep (se 1 (by rfl) ⟨13982219, by rfl⟩ : syracuseStep 18642959 = 27964439) B27964439
theorem B13990103 : Blo 1532463 13990103 := bstep (se 1 (by rfl) ⟨10492577, by rfl⟩ : syracuseStep 13990103 = 20985155) B20985155
theorem B11639213 : Blo 1532463 11639213 := bstep (se 3 (by rfl) ⟨2182352, by rfl⟩ : syracuseStep 11639213 = 4364705) B4364705
theorem B13105871 : Blo 1532463 13105871 := bstep (se 1 (by rfl) ⟨9829403, by rfl⟩ : syracuseStep 13105871 = 19658807) B19658807
theorem B2301023 : Blo 1532463 2301023 := bstep (se 1 (by rfl) ⟨1725767, by rfl⟩ : syracuseStep 2301023 = 3451535) B3451535
theorem B6552697 : Blo 1532463 6552697 := bstep (se 2 (by rfl) ⟨2457261, by rfl⟩ : syracuseStep 6552697 = 4914523) B4914523
theorem B2301065 : Blo 1532463 2301065 := bstep (se 2 (by rfl) ⟨862899, by rfl⟩ : syracuseStep 2301065 = 1725799) B1725799
theorem B44817565 : Blo 1532463 44817565 := bstep (se 3 (by rfl) ⟨8403293, by rfl⟩ : syracuseStep 44817565 = 16806587) B16806587
theorem B29474063 : Blo 1532463 29474063 := bstep (se 1 (by rfl) ⟨22105547, by rfl⟩ : syracuseStep 29474063 = 44211095) B44211095
theorem B8732555 : Blo 1532463 8732555 := bstep (se 1 (by rfl) ⟨6549416, by rfl⟩ : syracuseStep 8732555 = 13098833) B13098833
theorem B10092509 : Blo 1532463 10092509 := bstep (se 3 (by rfl) ⟨1892345, by rfl⟩ : syracuseStep 10092509 = 3784691) B3784691
theorem B62275715 : Blo 1532463 62275715 := bstep (se 1 (by rfl) ⟨46706786, by rfl⟩ : syracuseStep 62275715 = 93413573) B93413573
theorem B18645329 : Blo 1532463 18645329 := bstep (se 2 (by rfl) ⟨6991998, by rfl⟩ : syracuseStep 18645329 = 13983997) B13983997
theorem B7373267 : Blo 1532463 7373267 := bstep (se 1 (by rfl) ⟨5529950, by rfl⟩ : syracuseStep 7373267 = 11059901) B11059901
theorem B1941995 : Blo 1532463 1941995 := bstep (se 1 (by rfl) ⟨1456496, by rfl⟩ : syracuseStep 1941995 = 2912993) B2912993
theorem B1532463 : Blo 1532463 1532463 := bstep (se 1 (by rfl) ⟨1149347, by rfl⟩ : syracuseStep 1532463 = 2298695) B2298695
theorem B11797339 : Blo 1532463 11797339 := bstep (se 1 (by rfl) ⟨8848004, by rfl⟩ : syracuseStep 11797339 = 17696009) B17696009
theorem B1532775 : Blo 1532463 1532775 := bstep (se 1 (by rfl) ⟨1149581, by rfl⟩ : syracuseStep 1532775 = 2299163) B2299163
theorem B19653839 : Blo 1532463 19653839 := bstep (se 1 (by rfl) ⟨14740379, by rfl⟩ : syracuseStep 19653839 = 29480759) B29480759
theorem B5178599 : Blo 1532463 5178599 := bstep (se 1 (by rfl) ⟨3883949, by rfl⟩ : syracuseStep 5178599 = 7767899) B7767899
theorem B41960753 : Blo 1532463 41960753 := bstep (se 2 (by rfl) ⟨15735282, by rfl⟩ : syracuseStep 41960753 = 31470565) B31470565
theorem B3450167 : Blo 1532463 3450167 := bstep (se 1 (by rfl) ⟨2587625, by rfl⟩ : syracuseStep 3450167 = 5175251) B5175251
theorem B12428639 : Blo 1532463 12428639 := bstep (se 1 (by rfl) ⟨9321479, by rfl⟩ : syracuseStep 12428639 = 18642959) B18642959
theorem B7759475 : Blo 1532463 7759475 := bstep (se 1 (by rfl) ⟨5819606, by rfl⟩ : syracuseStep 7759475 = 11639213) B11639213
theorem B1534015 : Blo 1532463 1534015 := bstep (se 1 (by rfl) ⟨1150511, by rfl⟩ : syracuseStep 1534015 = 2301023) B2301023
theorem B1534043 : Blo 1532463 1534043 := bstep (se 1 (by rfl) ⟨1150532, by rfl⟩ : syracuseStep 1534043 = 2301065) B2301065
theorem B44837221 : Blo 1532463 44837221 := bstep (se 4 (by rfl) ⟨4203489, by rfl⟩ : syracuseStep 44837221 = 8406979) B8406979
theorem B6728339 : Blo 1532463 6728339 := bstep (se 1 (by rfl) ⟨5046254, by rfl⟩ : syracuseStep 6728339 = 10092509) B10092509
theorem B66341551 : Blo 1532463 66341551 := bstep (se 1 (by rfl) ⟨49756163, by rfl⟩ : syracuseStep 66341551 = 99512327) B99512327
theorem B35916635 : Blo 1532463 35916635 := bstep (se 1 (by rfl) ⟨26937476, by rfl⟩ : syracuseStep 35916635 = 53874953) B53874953
theorem B5172713 : Blo 1532463 5172713 := bstep (se 2 (by rfl) ⟨1939767, by rfl⟩ : syracuseStep 5172713 = 3879535) B3879535
theorem B19640353 : Blo 1532463 19640353 := bstep (se 2 (by rfl) ⟨7365132, by rfl⟩ : syracuseStep 19640353 = 14730265) B14730265
theorem B9326735 : Blo 1532463 9326735 := bstep (se 1 (by rfl) ⟨6995051, by rfl⟩ : syracuseStep 9326735 = 13990103) B13990103
theorem B8736929 : Blo 1532463 8736929 := bstep (se 2 (by rfl) ⟨3276348, by rfl⟩ : syracuseStep 8736929 = 6552697) B6552697
theorem B59756753 : Blo 1532463 59756753 := bstep (se 2 (by rfl) ⟨22408782, by rfl⟩ : syracuseStep 59756753 = 44817565) B44817565
theorem B39858425 : Blo 1532463 39858425 := bstep (se 2 (by rfl) ⟨14946909, by rfl⟩ : syracuseStep 39858425 = 29893819) B29893819
theorem B8737247 : Blo 1532463 8737247 := bstep (se 1 (by rfl) ⟨6552935, by rfl⟩ : syracuseStep 8737247 = 13105871) B13105871
theorem B7369325 : Blo 1532463 7369325 := bstep (se 3 (by rfl) ⟨1381748, by rfl⟩ : syracuseStep 7369325 = 2763497) B2763497
theorem B19649375 : Blo 1532463 19649375 := bstep (se 1 (by rfl) ⟨14737031, by rfl⟩ : syracuseStep 19649375 = 29474063) B29474063
theorem B5821703 : Blo 1532463 5821703 := bstep (se 1 (by rfl) ⟨4366277, by rfl⟩ : syracuseStep 5821703 = 8732555) B8732555
theorem B5174711 : Blo 1532463 5174711 := bstep (se 1 (by rfl) ⟨3881033, by rfl⟩ : syracuseStep 5174711 = 7762067) B7762067
theorem B2299433 : Blo 1532463 2299433 := bstep (se 2 (by rfl) ⟨862287, by rfl⟩ : syracuseStep 2299433 = 1724575) B1724575
theorem B2299439 : Blo 1532463 2299439 := bstep (se 1 (by rfl) ⟨1724579, by rfl⟩ : syracuseStep 2299439 = 3449159) B3449159
theorem B8738387 : Blo 1532463 8738387 := bstep (se 1 (by rfl) ⟨6553790, by rfl⟩ : syracuseStep 8738387 = 13107581) B13107581
theorem B5904119 : Blo 1532463 5904119 := bstep (se 1 (by rfl) ⟨4428089, by rfl⟩ : syracuseStep 5904119 = 8856179) B8856179
theorem B4364057 : Blo 1532463 4364057 := bstep (se 2 (by rfl) ⟨1636521, by rfl⟩ : syracuseStep 4364057 = 3273043) B3273043
theorem B2299751 : Blo 1532463 2299751 := bstep (se 1 (by rfl) ⟨1724813, by rfl⟩ : syracuseStep 2299751 = 3449627) B3449627
theorem B33167495 : Blo 1532463 33167495 := bstep (se 1 (by rfl) ⟨24875621, by rfl⟩ : syracuseStep 33167495 = 49751243) B49751243
theorem B5175791 : Blo 1532463 5175791 := bstep (se 1 (by rfl) ⟨3881843, by rfl⟩ : syracuseStep 5175791 = 7763687) B7763687
theorem B2300471 : Blo 1532463 2300471 := bstep (se 1 (by rfl) ⟨1725353, by rfl⟩ : syracuseStep 2300471 = 3450707) B3450707
theorem B4913779 : Blo 1532463 4913779 := bstep (se 1 (by rfl) ⟨3685334, by rfl⟩ : syracuseStep 4913779 = 7370669) B7370669
theorem B2301119 : Blo 1532463 2301119 := bstep (se 1 (by rfl) ⟨1725839, by rfl⟩ : syracuseStep 2301119 = 3451679) B3451679
theorem B16587985 : Blo 1532463 16587985 := bstep (se 2 (by rfl) ⟨6220494, by rfl⟩ : syracuseStep 16587985 = 12440989) B12440989
theorem B2301179 : Blo 1532463 2301179 := bstep (se 1 (by rfl) ⟨1725884, by rfl⟩ : syracuseStep 2301179 = 3451769) B3451769
theorem B2301275 : Blo 1532463 2301275 := bstep (se 1 (by rfl) ⟨1725956, by rfl⟩ : syracuseStep 2301275 = 3451913) B3451913
theorem B2301305 : Blo 1532463 2301305 := bstep (se 2 (by rfl) ⟨862989, by rfl⟩ : syracuseStep 2301305 = 1725979) B1725979
theorem B41517143 : Blo 1532463 41517143 := bstep (se 1 (by rfl) ⟨31137857, by rfl⟩ : syracuseStep 41517143 = 62275715) B62275715
theorem B6217823 : Blo 1532463 6217823 := bstep (se 1 (by rfl) ⟨4663367, by rfl⟩ : syracuseStep 6217823 = 9326735) B9326735
theorem B5824619 : Blo 1532463 5824619 := bstep (se 1 (by rfl) ⟨4368464, by rfl⟩ : syracuseStep 5824619 = 8736929) B8736929
theorem B39837835 : Blo 1532463 39837835 := bstep (se 1 (by rfl) ⟨29878376, by rfl⟩ : syracuseStep 39837835 = 59756753) B59756753
theorem B4915511 : Blo 1532463 4915511 := bstep (se 1 (by rfl) ⟨3686633, by rfl⟩ : syracuseStep 4915511 = 7373267) B7373267
theorem B5824831 : Blo 1532463 5824831 := bstep (se 1 (by rfl) ⟨4368623, by rfl⟩ : syracuseStep 5824831 = 8737247) B8737247
theorem B13099583 : Blo 1532463 13099583 := bstep (se 1 (by rfl) ⟨9824687, by rfl⟩ : syracuseStep 13099583 = 19649375) B19649375
theorem B3449807 : Blo 1532463 3449807 := bstep (se 1 (by rfl) ⟨2587355, by rfl⟩ : syracuseStep 3449807 = 5174711) B5174711
theorem B1532955 : Blo 1532463 1532955 := bstep (se 1 (by rfl) ⟨1149716, by rfl⟩ : syracuseStep 1532955 = 2299433) B2299433
theorem B1532959 : Blo 1532463 1532959 := bstep (se 1 (by rfl) ⟨1149719, by rfl⟩ : syracuseStep 1532959 = 2299439) B2299439
theorem B5825591 : Blo 1532463 5825591 := bstep (se 1 (by rfl) ⟨4369193, by rfl⟩ : syracuseStep 5825591 = 8738387) B8738387
theorem B15729785 : Blo 1532463 15729785 := bstep (se 2 (by rfl) ⟨5898669, by rfl⟩ : syracuseStep 15729785 = 11797339) B11797339
theorem B2909371 : Blo 1532463 2909371 := bstep (se 1 (by rfl) ⟨2182028, by rfl⟩ : syracuseStep 2909371 = 4364057) B4364057
theorem B1533167 : Blo 1532463 1533167 := bstep (se 1 (by rfl) ⟨1149875, by rfl⟩ : syracuseStep 1533167 = 2299751) B2299751
theorem B5178653 : Blo 1532463 5178653 := bstep (se 3 (by rfl) ⟨970997, by rfl⟩ : syracuseStep 5178653 = 1941995) B1941995
theorem B22111663 : Blo 1532463 22111663 := bstep (se 1 (by rfl) ⟨16583747, by rfl⟩ : syracuseStep 22111663 = 33167495) B33167495
theorem B3450527 : Blo 1532463 3450527 := bstep (se 1 (by rfl) ⟨2587895, by rfl⟩ : syracuseStep 3450527 = 5175791) B5175791
theorem B1533647 : Blo 1532463 1533647 := bstep (se 1 (by rfl) ⟨1150235, by rfl⟩ : syracuseStep 1533647 = 2300471) B2300471
theorem B1534079 : Blo 1532463 1534079 := bstep (se 1 (by rfl) ⟨1150559, by rfl⟩ : syracuseStep 1534079 = 2301119) B2301119
theorem B1534119 : Blo 1532463 1534119 := bstep (se 1 (by rfl) ⟨1150589, by rfl⟩ : syracuseStep 1534119 = 2301179) B2301179
theorem B1534183 : Blo 1532463 1534183 := bstep (se 1 (by rfl) ⟨1150637, by rfl⟩ : syracuseStep 1534183 = 2301275) B2301275
theorem B1534203 : Blo 1532463 1534203 := bstep (se 1 (by rfl) ⟨1150652, by rfl⟩ : syracuseStep 1534203 = 2301305) B2301305
theorem B13102559 : Blo 1532463 13102559 := bstep (se 1 (by rfl) ⟨9826919, by rfl⟩ : syracuseStep 13102559 = 19653839) B19653839
theorem B3452399 : Blo 1532463 3452399 := bstep (se 1 (by rfl) ⟨2589299, by rfl⟩ : syracuseStep 3452399 = 5178599) B5178599
theorem B49720877 : Blo 1532463 49720877 := bstep (se 3 (by rfl) ⟨9322664, by rfl⟩ : syracuseStep 49720877 = 18645329) B18645329
theorem B8285759 : Blo 1532463 8285759 := bstep (se 1 (by rfl) ⟨6214319, by rfl⟩ : syracuseStep 8285759 = 12428639) B12428639
theorem B5172983 : Blo 1532463 5172983 := bstep (se 1 (by rfl) ⟨3879737, by rfl⟩ : syracuseStep 5172983 = 7759475) B7759475
theorem B3936079 : Blo 1532463 3936079 := bstep (se 1 (by rfl) ⟨2952059, by rfl⟩ : syracuseStep 3936079 = 5904119) B5904119
theorem B4485559 : Blo 1532463 4485559 := bstep (se 1 (by rfl) ⟨3364169, by rfl⟩ : syracuseStep 4485559 = 6728339) B6728339
theorem B26187137 : Blo 1532463 26187137 := bstep (se 2 (by rfl) ⟨9820176, by rfl⟩ : syracuseStep 26187137 = 19640353) B19640353
theorem B26572283 : Blo 1532463 26572283 := bstep (se 1 (by rfl) ⟨19929212, by rfl⟩ : syracuseStep 26572283 = 39858425) B39858425
theorem B4912883 : Blo 1532463 4912883 := bstep (se 1 (by rfl) ⟨3684662, by rfl⟩ : syracuseStep 4912883 = 7369325) B7369325
theorem B59782961 : Blo 1532463 59782961 := bstep (se 2 (by rfl) ⟨22418610, by rfl⟩ : syracuseStep 59782961 = 44837221) B44837221
theorem B6551705 : Blo 1532463 6551705 := bstep (se 2 (by rfl) ⟨2456889, by rfl⟩ : syracuseStep 6551705 = 4913779) B4913779
theorem B3881135 : Blo 1532463 3881135 := bstep (se 1 (by rfl) ⟨2910851, by rfl⟩ : syracuseStep 3881135 = 5821703) B5821703
theorem B27973835 : Blo 1532463 27973835 := bstep (se 1 (by rfl) ⟨20980376, by rfl⟩ : syracuseStep 27973835 = 41960753) B41960753
theorem B2300111 : Blo 1532463 2300111 := bstep (se 1 (by rfl) ⟨1725083, by rfl⟩ : syracuseStep 2300111 = 3450167) B3450167
theorem B88455401 : Blo 1532463 88455401 := bstep (se 2 (by rfl) ⟨33170775, by rfl⟩ : syracuseStep 88455401 = 66341551) B66341551
theorem B22117313 : Blo 1532463 22117313 := bstep (se 2 (by rfl) ⟨8293992, by rfl⟩ : syracuseStep 22117313 = 16587985) B16587985
theorem B23944423 : Blo 1532463 23944423 := bstep (se 1 (by rfl) ⟨17958317, by rfl⟩ : syracuseStep 23944423 = 35916635) B35916635
theorem B3448475 : Blo 1532463 3448475 := bstep (se 1 (by rfl) ⟨2586356, by rfl⟩ : syracuseStep 3448475 = 5172713) B5172713
theorem B4145215 : Blo 1532463 4145215 := bstep (se 1 (by rfl) ⟨3108911, by rfl⟩ : syracuseStep 4145215 = 6217823) B6217823
theorem B3883079 : Blo 1532463 3883079 := bstep (se 1 (by rfl) ⟨2912309, by rfl⟩ : syracuseStep 3883079 = 5824619) B5824619
theorem B3277007 : Blo 1532463 3277007 := bstep (se 1 (by rfl) ⟨2457755, by rfl⟩ : syracuseStep 3277007 = 4915511) B4915511
theorem B8733055 : Blo 1532463 8733055 := bstep (se 1 (by rfl) ⟨6549791, by rfl⟩ : syracuseStep 8733055 = 13099583) B13099583
theorem B7766441 : Blo 1532463 7766441 := bstep (se 2 (by rfl) ⟨2912415, by rfl⟩ : syracuseStep 7766441 = 5824831) B5824831
theorem B5980745 : Blo 1532463 5980745 := bstep (se 2 (by rfl) ⟨2242779, by rfl⟩ : syracuseStep 5980745 = 4485559) B4485559
theorem B3883727 : Blo 1532463 3883727 := bstep (se 1 (by rfl) ⟨2912795, by rfl⟩ : syracuseStep 3883727 = 5825591) B5825591
theorem B212468453 : Blo 1532463 212468453 := bstep (se 4 (by rfl) ⟨19918917, by rfl⟩ : syracuseStep 212468453 = 39837835) B39837835
theorem B10486523 : Blo 1532463 10486523 := bstep (se 1 (by rfl) ⟨7864892, by rfl⟩ : syracuseStep 10486523 = 15729785) B15729785
theorem B17458091 : Blo 1532463 17458091 := bstep (se 1 (by rfl) ⟨13093568, by rfl⟩ : syracuseStep 17458091 = 26187137) B26187137
theorem B1533407 : Blo 1532463 1533407 := bstep (se 1 (by rfl) ⟨1150055, by rfl⟩ : syracuseStep 1533407 = 2300111) B2300111
theorem B31925897 : Blo 1532463 31925897 := bstep (se 2 (by rfl) ⟨11972211, by rfl⟩ : syracuseStep 31925897 = 23944423) B23944423
theorem B8735039 : Blo 1532463 8735039 := bstep (se 1 (by rfl) ⟨6551279, by rfl⟩ : syracuseStep 8735039 = 13102559) B13102559
theorem B33147251 : Blo 1532463 33147251 := bstep (se 1 (by rfl) ⟨24860438, by rfl⟩ : syracuseStep 33147251 = 49720877) B49720877
theorem B5523839 : Blo 1532463 5523839 := bstep (se 1 (by rfl) ⟨4142879, by rfl⟩ : syracuseStep 5523839 = 8285759) B8285759
theorem B3452435 : Blo 1532463 3452435 := bstep (se 1 (by rfl) ⟨2589326, by rfl⟩ : syracuseStep 3452435 = 5178653) B5178653
theorem B17714855 : Blo 1532463 17714855 := bstep (se 1 (by rfl) ⟨13286141, by rfl⟩ : syracuseStep 17714855 = 26572283) B26572283
theorem B18649223 : Blo 1532463 18649223 := bstep (se 1 (by rfl) ⟨13986917, by rfl⟩ : syracuseStep 18649223 = 27973835) B27973835
theorem B58970267 : Blo 1532463 58970267 := bstep (se 1 (by rfl) ⟨44227700, by rfl⟩ : syracuseStep 58970267 = 88455401) B88455401
theorem B3879161 : Blo 1532463 3879161 := bstep (se 2 (by rfl) ⟨1454685, by rfl⟩ : syracuseStep 3879161 = 2909371) B2909371
theorem B20992421 : Blo 1532463 20992421 := bstep (se 4 (by rfl) ⟨1968039, by rfl⟩ : syracuseStep 20992421 = 3936079) B3936079
theorem B159421229 : Blo 1532463 159421229 := bstep (se 3 (by rfl) ⟨29891480, by rfl⟩ : syracuseStep 159421229 = 59782961) B59782961
theorem B2298983 : Blo 1532463 2298983 := bstep (se 1 (by rfl) ⟨1724237, by rfl⟩ : syracuseStep 2298983 = 3448475) B3448475
theorem B27678095 : Blo 1532463 27678095 := bstep (se 1 (by rfl) ⟨20758571, by rfl⟩ : syracuseStep 27678095 = 41517143) B41517143
theorem B17471213 : Blo 1532463 17471213 := bstep (se 3 (by rfl) ⟨3275852, by rfl⟩ : syracuseStep 17471213 = 6551705) B6551705
theorem B2299871 : Blo 1532463 2299871 := bstep (se 1 (by rfl) ⟨1724903, by rfl⟩ : syracuseStep 2299871 = 3449807) B3449807
theorem B2300351 : Blo 1532463 2300351 := bstep (se 1 (by rfl) ⟨1725263, by rfl⟩ : syracuseStep 2300351 = 3450527) B3450527
theorem B3275255 : Blo 1532463 3275255 := bstep (se 1 (by rfl) ⟨2456441, by rfl⟩ : syracuseStep 3275255 = 4912883) B4912883
theorem B2587423 : Blo 1532463 2587423 := bstep (se 1 (by rfl) ⟨1940567, by rfl⟩ : syracuseStep 2587423 = 3881135) B3881135
theorem B29482217 : Blo 1532463 29482217 := bstep (se 2 (by rfl) ⟨11055831, by rfl⟩ : syracuseStep 29482217 = 22111663) B22111663
theorem B14744875 : Blo 1532463 14744875 := bstep (se 1 (by rfl) ⟨11058656, by rfl⟩ : syracuseStep 14744875 = 22117313) B22117313
theorem B2301599 : Blo 1532463 2301599 := bstep (se 1 (by rfl) ⟨1726199, by rfl⟩ : syracuseStep 2301599 = 3452399) B3452399
theorem B3448655 : Blo 1532463 3448655 := bstep (se 1 (by rfl) ⟨2586491, by rfl⟩ : syracuseStep 3448655 = 5172983) B5172983
theorem B2588719 : Blo 1532463 2588719 := bstep (se 1 (by rfl) ⟨1941539, by rfl⟩ : syracuseStep 2588719 = 3883079) B3883079
theorem B39313511 : Blo 1532463 39313511 := bstep (se 1 (by rfl) ⟨29485133, by rfl⟩ : syracuseStep 39313511 = 58970267) B58970267
theorem B5177627 : Blo 1532463 5177627 := bstep (se 1 (by rfl) ⟨3883220, by rfl⟩ : syracuseStep 5177627 = 7766441) B7766441
theorem B2589151 : Blo 1532463 2589151 := bstep (se 1 (by rfl) ⟨1941863, by rfl⟩ : syracuseStep 2589151 = 3883727) B3883727
theorem B1532655 : Blo 1532463 1532655 := bstep (se 1 (by rfl) ⟨1149491, by rfl⟩ : syracuseStep 1532655 = 2298983) B2298983
theorem B3449897 : Blo 1532463 3449897 := bstep (se 2 (by rfl) ⟨1293711, by rfl⟩ : syracuseStep 3449897 = 2587423) B2587423
theorem B21283931 : Blo 1532463 21283931 := bstep (se 1 (by rfl) ⟨15962948, by rfl⟩ : syracuseStep 21283931 = 31925897) B31925897
theorem B8734013 : Blo 1532463 8734013 := bstep (se 3 (by rfl) ⟨1637627, by rfl⟩ : syracuseStep 8734013 = 3275255) B3275255
theorem B1533247 : Blo 1532463 1533247 := bstep (se 1 (by rfl) ⟨1149935, by rfl⟩ : syracuseStep 1533247 = 2299871) B2299871
theorem B1533567 : Blo 1532463 1533567 := bstep (se 1 (by rfl) ⟨1150175, by rfl⟩ : syracuseStep 1533567 = 2300351) B2300351
theorem B19654811 : Blo 1532463 19654811 := bstep (se 1 (by rfl) ⟨14741108, by rfl⟩ : syracuseStep 19654811 = 29482217) B29482217
theorem B1534399 : Blo 1532463 1534399 := bstep (se 1 (by rfl) ⟨1150799, by rfl⟩ : syracuseStep 1534399 = 2301599) B2301599
theorem B13994947 : Blo 1532463 13994947 := bstep (se 1 (by rfl) ⟨10496210, by rfl⟩ : syracuseStep 13994947 = 20992421) B20992421
theorem B11644073 : Blo 1532463 11644073 := bstep (se 2 (by rfl) ⟨4366527, by rfl⟩ : syracuseStep 11644073 = 8733055) B8733055
theorem B18452063 : Blo 1532463 18452063 := bstep (se 1 (by rfl) ⟨13839047, by rfl⟩ : syracuseStep 18452063 = 27678095) B27678095
theorem B22098167 : Blo 1532463 22098167 := bstep (se 1 (by rfl) ⟨16573625, by rfl⟩ : syracuseStep 22098167 = 33147251) B33147251
theorem B3682559 : Blo 1532463 3682559 := bstep (se 1 (by rfl) ⟨2761919, by rfl⟩ : syracuseStep 3682559 = 5523839) B5523839
theorem B27964061 : Blo 1532463 27964061 := bstep (se 3 (by rfl) ⟨5243261, by rfl⟩ : syracuseStep 27964061 = 10486523) B10486523
theorem B11809903 : Blo 1532463 11809903 := bstep (se 1 (by rfl) ⟨8857427, by rfl⟩ : syracuseStep 11809903 = 17714855) B17714855
theorem B2299103 : Blo 1532463 2299103 := bstep (se 1 (by rfl) ⟨1724327, by rfl⟩ : syracuseStep 2299103 = 3448655) B3448655
theorem B5526953 : Blo 1532463 5526953 := bstep (se 2 (by rfl) ⟨2072607, by rfl⟩ : syracuseStep 5526953 = 4145215) B4145215
theorem B12432815 : Blo 1532463 12432815 := bstep (se 1 (by rfl) ⟨9324611, by rfl⟩ : syracuseStep 12432815 = 18649223) B18649223
theorem B2184671 : Blo 1532463 2184671 := bstep (se 1 (by rfl) ⟨1638503, by rfl⟩ : syracuseStep 2184671 = 3277007) B3277007
theorem B2586107 : Blo 1532463 2586107 := bstep (se 1 (by rfl) ⟨1939580, by rfl⟩ : syracuseStep 2586107 = 3879161) B3879161
theorem B3987163 : Blo 1532463 3987163 := bstep (se 1 (by rfl) ⟨2990372, by rfl⟩ : syracuseStep 3987163 = 5980745) B5980745
theorem B141645635 : Blo 1532463 141645635 := bstep (se 1 (by rfl) ⟨106234226, by rfl⟩ : syracuseStep 141645635 = 212468453) B212468453
theorem B106280819 : Blo 1532463 106280819 := bstep (se 1 (by rfl) ⟨79710614, by rfl⟩ : syracuseStep 106280819 = 159421229) B159421229
theorem B11638727 : Blo 1532463 11638727 := bstep (se 1 (by rfl) ⟨8729045, by rfl⟩ : syracuseStep 11638727 = 17458091) B17458091
theorem B11647475 : Blo 1532463 11647475 := bstep (se 1 (by rfl) ⟨8735606, by rfl⟩ : syracuseStep 11647475 = 17471213) B17471213
theorem B5823359 : Blo 1532463 5823359 := bstep (se 1 (by rfl) ⟨4367519, by rfl⟩ : syracuseStep 5823359 = 8735039) B8735039
theorem B19659833 : Blo 1532463 19659833 := bstep (se 2 (by rfl) ⟨7372437, by rfl⟩ : syracuseStep 19659833 = 14744875) B14744875
theorem B2301623 : Blo 1532463 2301623 := bstep (se 1 (by rfl) ⟨1726217, by rfl⟩ : syracuseStep 2301623 = 3452435) B3452435
theorem B14189287 : Blo 1532463 14189287 := bstep (se 1 (by rfl) ⟨10641965, by rfl⟩ : syracuseStep 14189287 = 21283931) B21283931
theorem B1532735 : Blo 1532463 1532735 := bstep (se 1 (by rfl) ⟨1149551, by rfl⟩ : syracuseStep 1532735 = 2299103) B2299103
theorem B94430423 : Blo 1532463 94430423 := bstep (se 1 (by rfl) ⟨70822817, by rfl⟩ : syracuseStep 94430423 = 141645635) B141645635
theorem B70853879 : Blo 1532463 70853879 := bstep (se 1 (by rfl) ⟨53140409, by rfl⟩ : syracuseStep 70853879 = 106280819) B106280819
theorem B5825789 : Blo 1532463 5825789 := bstep (se 3 (by rfl) ⟨1092335, by rfl⟩ : syracuseStep 5825789 = 2184671) B2184671
theorem B7759151 : Blo 1532463 7759151 := bstep (se 1 (by rfl) ⟨5819363, by rfl⟩ : syracuseStep 7759151 = 11638727) B11638727
theorem B15746537 : Blo 1532463 15746537 := bstep (se 2 (by rfl) ⟨5904951, by rfl⟩ : syracuseStep 15746537 = 11809903) B11809903
theorem B1534415 : Blo 1532463 1534415 := bstep (se 1 (by rfl) ⟨1150811, by rfl⟩ : syracuseStep 1534415 = 2301623) B2301623
theorem B3451625 : Blo 1532463 3451625 := bstep (se 2 (by rfl) ⟨1294359, by rfl⟩ : syracuseStep 3451625 = 2588719) B2588719
theorem B26209007 : Blo 1532463 26209007 := bstep (se 1 (by rfl) ⟨19656755, by rfl⟩ : syracuseStep 26209007 = 39313511) B39313511
theorem B14732111 : Blo 1532463 14732111 := bstep (se 1 (by rfl) ⟨11049083, by rfl⟩ : syracuseStep 14732111 = 22098167) B22098167
theorem B3451751 : Blo 1532463 3451751 := bstep (se 1 (by rfl) ⟨2588813, by rfl⟩ : syracuseStep 3451751 = 5177627) B5177627
theorem B3452201 : Blo 1532463 3452201 := bstep (se 2 (by rfl) ⟨1294575, by rfl⟩ : syracuseStep 3452201 = 2589151) B2589151
theorem B1724071 : Blo 1532463 1724071 := bstep (se 1 (by rfl) ⟨1293053, by rfl⟩ : syracuseStep 1724071 = 2586107) B2586107
theorem B13103207 : Blo 1532463 13103207 := bstep (se 1 (by rfl) ⟨9827405, by rfl⟩ : syracuseStep 13103207 = 19654811) B19654811
theorem B7762715 : Blo 1532463 7762715 := bstep (se 1 (by rfl) ⟨5822036, by rfl⟩ : syracuseStep 7762715 = 11644073) B11644073
theorem B12301375 : Blo 1532463 12301375 := bstep (se 1 (by rfl) ⟨9226031, by rfl⟩ : syracuseStep 12301375 = 18452063) B18452063
theorem B2455039 : Blo 1532463 2455039 := bstep (se 1 (by rfl) ⟨1841279, by rfl⟩ : syracuseStep 2455039 = 3682559) B3682559
theorem B18642707 : Blo 1532463 18642707 := bstep (se 1 (by rfl) ⟨13982030, by rfl⟩ : syracuseStep 18642707 = 27964061) B27964061
theorem B2299931 : Blo 1532463 2299931 := bstep (se 1 (by rfl) ⟨1724948, by rfl⟩ : syracuseStep 2299931 = 3449897) B3449897
theorem B5822675 : Blo 1532463 5822675 := bstep (se 1 (by rfl) ⟨4367006, by rfl⟩ : syracuseStep 5822675 = 8734013) B8734013
theorem B3684635 : Blo 1532463 3684635 := bstep (se 1 (by rfl) ⟨2763476, by rfl⟩ : syracuseStep 3684635 = 5526953) B5526953
theorem B8288543 : Blo 1532463 8288543 := bstep (se 1 (by rfl) ⟨6216407, by rfl⟩ : syracuseStep 8288543 = 12432815) B12432815
theorem B21264869 : Blo 1532463 21264869 := bstep (se 4 (by rfl) ⟨1993581, by rfl⟩ : syracuseStep 21264869 = 3987163) B3987163
theorem B18659929 : Blo 1532463 18659929 := bstep (se 2 (by rfl) ⟨6997473, by rfl⟩ : syracuseStep 18659929 = 13994947) B13994947
theorem B7764983 : Blo 1532463 7764983 := bstep (se 1 (by rfl) ⟨5823737, by rfl⟩ : syracuseStep 7764983 = 11647475) B11647475
theorem B3882239 : Blo 1532463 3882239 := bstep (se 1 (by rfl) ⟨2911679, by rfl⟩ : syracuseStep 3882239 = 5823359) B5823359
theorem B13106555 : Blo 1532463 13106555 := bstep (se 1 (by rfl) ⟨9829916, by rfl⟩ : syracuseStep 13106555 = 19659833) B19659833
theorem B24879905 : Blo 1532463 24879905 := bstep (se 2 (by rfl) ⟨9329964, by rfl⟩ : syracuseStep 24879905 = 18659929) B18659929
theorem B47235919 : Blo 1532463 47235919 := bstep (se 1 (by rfl) ⟨35426939, by rfl⟩ : syracuseStep 47235919 = 70853879) B70853879
theorem B3883859 : Blo 1532463 3883859 := bstep (se 1 (by rfl) ⟨2912894, by rfl⟩ : syracuseStep 3883859 = 5825789) B5825789
theorem B12428471 : Blo 1532463 12428471 := bstep (se 1 (by rfl) ⟨9321353, by rfl⟩ : syracuseStep 12428471 = 18642707) B18642707
theorem B1533287 : Blo 1532463 1533287 := bstep (se 1 (by rfl) ⟨1149965, by rfl⟩ : syracuseStep 1533287 = 2299931) B2299931
theorem B16401833 : Blo 1532463 16401833 := bstep (se 2 (by rfl) ⟨6150687, by rfl⟩ : syracuseStep 16401833 = 12301375) B12301375
theorem B8735471 : Blo 1532463 8735471 := bstep (se 1 (by rfl) ⟨6551603, by rfl⟩ : syracuseStep 8735471 = 13103207) B13103207
theorem B5172767 : Blo 1532463 5172767 := bstep (se 1 (by rfl) ⟨3879575, by rfl⟩ : syracuseStep 5172767 = 7759151) B7759151
theorem B18919049 : Blo 1532463 18919049 := bstep (se 2 (by rfl) ⟨7094643, by rfl⟩ : syracuseStep 18919049 = 14189287) B14189287
theorem B10497691 : Blo 1532463 10497691 := bstep (se 1 (by rfl) ⟨7873268, by rfl⟩ : syracuseStep 10497691 = 15746537) B15746537
theorem B5525695 : Blo 1532463 5525695 := bstep (se 1 (by rfl) ⟨4144271, by rfl⟩ : syracuseStep 5525695 = 8288543) B8288543
theorem B14176579 : Blo 1532463 14176579 := bstep (se 1 (by rfl) ⟨10632434, by rfl⟩ : syracuseStep 14176579 = 21264869) B21264869
theorem B3273385 : Blo 1532463 3273385 := bstep (se 2 (by rfl) ⟨1227519, by rfl⟩ : syracuseStep 3273385 = 2455039) B2455039
theorem B2298761 : Blo 1532463 2298761 := bstep (se 2 (by rfl) ⟨862035, by rfl⟩ : syracuseStep 2298761 = 1724071) B1724071
theorem B8737703 : Blo 1532463 8737703 := bstep (se 1 (by rfl) ⟨6553277, by rfl⟩ : syracuseStep 8737703 = 13106555) B13106555
theorem B5175143 : Blo 1532463 5175143 := bstep (se 1 (by rfl) ⟨3881357, by rfl⟩ : syracuseStep 5175143 = 7762715) B7762715
theorem B62953615 : Blo 1532463 62953615 := bstep (se 1 (by rfl) ⟨47215211, by rfl⟩ : syracuseStep 62953615 = 94430423) B94430423
theorem B3881783 : Blo 1532463 3881783 := bstep (se 1 (by rfl) ⟨2911337, by rfl⟩ : syracuseStep 3881783 = 5822675) B5822675
theorem B2456423 : Blo 1532463 2456423 := bstep (se 1 (by rfl) ⟨1842317, by rfl⟩ : syracuseStep 2456423 = 3684635) B3684635
theorem B2301083 : Blo 1532463 2301083 := bstep (se 1 (by rfl) ⟨1725812, by rfl⟩ : syracuseStep 2301083 = 3451625) B3451625
theorem B17472671 : Blo 1532463 17472671 := bstep (se 1 (by rfl) ⟨13104503, by rfl⟩ : syracuseStep 17472671 = 26209007) B26209007
theorem B9821407 : Blo 1532463 9821407 := bstep (se 1 (by rfl) ⟨7366055, by rfl⟩ : syracuseStep 9821407 = 14732111) B14732111
theorem B2301167 : Blo 1532463 2301167 := bstep (se 1 (by rfl) ⟨1725875, by rfl⟩ : syracuseStep 2301167 = 3451751) B3451751
theorem B5176655 : Blo 1532463 5176655 := bstep (se 1 (by rfl) ⟨3882491, by rfl⟩ : syracuseStep 5176655 = 7764983) B7764983
theorem B2588159 : Blo 1532463 2588159 := bstep (se 1 (by rfl) ⟨1941119, by rfl⟩ : syracuseStep 2588159 = 3882239) B3882239
theorem B2301467 : Blo 1532463 2301467 := bstep (se 1 (by rfl) ⟨1726100, by rfl⟩ : syracuseStep 2301467 = 3452201) B3452201
theorem B2589239 : Blo 1532463 2589239 := bstep (se 1 (by rfl) ⟨1941929, by rfl⟩ : syracuseStep 2589239 = 3883859) B3883859
theorem B1532507 : Blo 1532463 1532507 := bstep (se 1 (by rfl) ⟨1149380, by rfl⟩ : syracuseStep 1532507 = 2298761) B2298761
theorem B5825135 : Blo 1532463 5825135 := bstep (se 1 (by rfl) ⟨4368851, by rfl⟩ : syracuseStep 5825135 = 8737703) B8737703
theorem B62981225 : Blo 1532463 62981225 := bstep (se 2 (by rfl) ⟨23617959, by rfl⟩ : syracuseStep 62981225 = 47235919) B47235919
theorem B3450095 : Blo 1532463 3450095 := bstep (se 1 (by rfl) ⟨2587571, by rfl⟩ : syracuseStep 3450095 = 5175143) B5175143
theorem B1534055 : Blo 1532463 1534055 := bstep (se 1 (by rfl) ⟨1150541, by rfl⟩ : syracuseStep 1534055 = 2301083) B2301083
theorem B1534111 : Blo 1532463 1534111 := bstep (se 1 (by rfl) ⟨1150583, by rfl⟩ : syracuseStep 1534111 = 2301167) B2301167
theorem B3451103 : Blo 1532463 3451103 := bstep (se 1 (by rfl) ⟨2588327, by rfl⟩ : syracuseStep 3451103 = 5176655) B5176655
theorem B1534311 : Blo 1532463 1534311 := bstep (se 1 (by rfl) ⟨1150733, by rfl⟩ : syracuseStep 1534311 = 2301467) B2301467
theorem B83938153 : Blo 1532463 83938153 := bstep (se 2 (by rfl) ⟨31476807, by rfl⟩ : syracuseStep 83938153 = 62953615) B62953615
theorem B7367593 : Blo 1532463 7367593 := bstep (se 2 (by rfl) ⟨2762847, by rfl⟩ : syracuseStep 7367593 = 5525695) B5525695
theorem B18902105 : Blo 1532463 18902105 := bstep (se 2 (by rfl) ⟨7088289, by rfl⟩ : syracuseStep 18902105 = 14176579) B14176579
theorem B8285647 : Blo 1532463 8285647 := bstep (se 1 (by rfl) ⟨6214235, by rfl⟩ : syracuseStep 8285647 = 12428471) B12428471
theorem B13095209 : Blo 1532463 13095209 := bstep (se 2 (by rfl) ⟨4910703, by rfl⟩ : syracuseStep 13095209 = 9821407) B9821407
theorem B50450797 : Blo 1532463 50450797 := bstep (se 3 (by rfl) ⟨9459524, by rfl⟩ : syracuseStep 50450797 = 18919049) B18919049
theorem B174952885 : Blo 1532463 174952885 := bstep (se 5 (by rfl) ⟨8200916, by rfl⟩ : syracuseStep 174952885 = 16401833) B16401833
theorem B13996921 : Blo 1532463 13996921 := bstep (se 2 (by rfl) ⟨5248845, by rfl⟩ : syracuseStep 13996921 = 10497691) B10497691
theorem B1725439 : Blo 1532463 1725439 := bstep (se 1 (by rfl) ⟨1294079, by rfl⟩ : syracuseStep 1725439 = 2588159) B2588159
theorem B16586603 : Blo 1532463 16586603 := bstep (se 1 (by rfl) ⟨12439952, by rfl⟩ : syracuseStep 16586603 = 24879905) B24879905
theorem B4364513 : Blo 1532463 4364513 := bstep (se 2 (by rfl) ⟨1636692, by rfl⟩ : syracuseStep 4364513 = 3273385) B3273385
theorem B5823647 : Blo 1532463 5823647 := bstep (se 1 (by rfl) ⟨4367735, by rfl⟩ : syracuseStep 5823647 = 8735471) B8735471
theorem B2587855 : Blo 1532463 2587855 := bstep (se 1 (by rfl) ⟨1940891, by rfl⟩ : syracuseStep 2587855 = 3881783) B3881783
theorem B1637615 : Blo 1532463 1637615 := bstep (se 1 (by rfl) ⟨1228211, by rfl⟩ : syracuseStep 1637615 = 2456423) B2456423
theorem B11648447 : Blo 1532463 11648447 := bstep (se 1 (by rfl) ⟨8736335, by rfl⟩ : syracuseStep 11648447 = 17472671) B17472671
theorem B3448511 : Blo 1532463 3448511 := bstep (se 1 (by rfl) ⟨2586383, by rfl⟩ : syracuseStep 3448511 = 5172767) B5172767
theorem B3883423 : Blo 1532463 3883423 := bstep (se 1 (by rfl) ⟨2912567, by rfl⟩ : syracuseStep 3883423 = 5825135) B5825135
theorem B4366973 : Blo 1532463 4366973 := bstep (se 3 (by rfl) ⟨818807, by rfl⟩ : syracuseStep 4366973 = 1637615) B1637615
theorem B18662561 : Blo 1532463 18662561 := bstep (se 2 (by rfl) ⟨6998460, by rfl⟩ : syracuseStep 18662561 = 13996921) B13996921
theorem B9823457 : Blo 1532463 9823457 := bstep (se 2 (by rfl) ⟨3683796, by rfl⟩ : syracuseStep 9823457 = 7367593) B7367593
theorem B2909675 : Blo 1532463 2909675 := bstep (se 1 (by rfl) ⟨2182256, by rfl⟩ : syracuseStep 2909675 = 4364513) B4364513
theorem B3450473 : Blo 1532463 3450473 := bstep (se 2 (by rfl) ⟨1293927, by rfl⟩ : syracuseStep 3450473 = 2587855) B2587855
theorem B12601403 : Blo 1532463 12601403 := bstep (se 1 (by rfl) ⟨9451052, by rfl⟩ : syracuseStep 12601403 = 18902105) B18902105
theorem B67267729 : Blo 1532463 67267729 := bstep (se 2 (by rfl) ⟨25225398, by rfl⟩ : syracuseStep 67267729 = 50450797) B50450797
theorem B233270513 : Blo 1532463 233270513 := bstep (se 2 (by rfl) ⟨87476442, by rfl⟩ : syracuseStep 233270513 = 174952885) B174952885
theorem B41987483 : Blo 1532463 41987483 := bstep (se 1 (by rfl) ⟨31490612, by rfl⟩ : syracuseStep 41987483 = 62981225) B62981225
theorem B11047529 : Blo 1532463 11047529 := bstep (se 2 (by rfl) ⟨4142823, by rfl⟩ : syracuseStep 11047529 = 8285647) B8285647
theorem B2299007 : Blo 1532463 2299007 := bstep (se 1 (by rfl) ⟨1724255, by rfl⟩ : syracuseStep 2299007 = 3448511) B3448511
theorem B8730139 : Blo 1532463 8730139 := bstep (se 1 (by rfl) ⟨6547604, by rfl⟩ : syracuseStep 8730139 = 13095209) B13095209
theorem B1726159 : Blo 1532463 1726159 := bstep (se 1 (by rfl) ⟨1294619, by rfl⟩ : syracuseStep 1726159 = 2589239) B2589239
theorem B2300063 : Blo 1532463 2300063 := bstep (se 1 (by rfl) ⟨1725047, by rfl⟩ : syracuseStep 2300063 = 3450095) B3450095
theorem B111917537 : Blo 1532463 111917537 := bstep (se 2 (by rfl) ⟨41969076, by rfl⟩ : syracuseStep 111917537 = 83938153) B83938153
theorem B11057735 : Blo 1532463 11057735 := bstep (se 1 (by rfl) ⟨8293301, by rfl⟩ : syracuseStep 11057735 = 16586603) B16586603
theorem B2300585 : Blo 1532463 2300585 := bstep (se 2 (by rfl) ⟨862719, by rfl⟩ : syracuseStep 2300585 = 1725439) B1725439
theorem B2300735 : Blo 1532463 2300735 := bstep (se 1 (by rfl) ⟨1725551, by rfl⟩ : syracuseStep 2300735 = 3451103) B3451103
theorem B3882431 : Blo 1532463 3882431 := bstep (se 1 (by rfl) ⟨2911823, by rfl⟩ : syracuseStep 3882431 = 5823647) B5823647
theorem B7765631 : Blo 1532463 7765631 := bstep (se 1 (by rfl) ⟨5824223, by rfl⟩ : syracuseStep 7765631 = 11648447) B11648447
theorem B7365019 : Blo 1532463 7365019 := bstep (se 1 (by rfl) ⟨5523764, by rfl⟩ : syracuseStep 7365019 = 11047529) B11047529
theorem B5177897 : Blo 1532463 5177897 := bstep (se 2 (by rfl) ⟨1941711, by rfl⟩ : syracuseStep 5177897 = 3883423) B3883423
theorem B1532671 : Blo 1532463 1532671 := bstep (se 1 (by rfl) ⟨1149503, by rfl⟩ : syracuseStep 1532671 = 2299007) B2299007
theorem B358761221 : Blo 1532463 358761221 := bstep (se 4 (by rfl) ⟨33633864, by rfl⟩ : syracuseStep 358761221 = 67267729) B67267729
theorem B1533375 : Blo 1532463 1533375 := bstep (se 1 (by rfl) ⟨1150031, by rfl⟩ : syracuseStep 1533375 = 2300063) B2300063
theorem B1533723 : Blo 1532463 1533723 := bstep (se 1 (by rfl) ⟨1150292, by rfl⟩ : syracuseStep 1533723 = 2300585) B2300585
theorem B1533823 : Blo 1532463 1533823 := bstep (se 1 (by rfl) ⟨1150367, by rfl⟩ : syracuseStep 1533823 = 2300735) B2300735
theorem B2911315 : Blo 1532463 2911315 := bstep (se 1 (by rfl) ⟨2183486, by rfl⟩ : syracuseStep 2911315 = 4366973) B4366973
theorem B8400935 : Blo 1532463 8400935 := bstep (se 1 (by rfl) ⟨6300701, by rfl⟩ : syracuseStep 8400935 = 12601403) B12601403
theorem B155513675 : Blo 1532463 155513675 := bstep (se 1 (by rfl) ⟨116635256, by rfl⟩ : syracuseStep 155513675 = 233270513) B233270513
theorem B26195885 : Blo 1532463 26195885 := bstep (se 3 (by rfl) ⟨4911728, by rfl⟩ : syracuseStep 26195885 = 9823457) B9823457
theorem B12441707 : Blo 1532463 12441707 := bstep (se 1 (by rfl) ⟨9331280, by rfl⟩ : syracuseStep 12441707 = 18662561) B18662561
theorem B1939783 : Blo 1532463 1939783 := bstep (se 1 (by rfl) ⟨1454837, by rfl⟩ : syracuseStep 1939783 = 2909675) B2909675
theorem B2300315 : Blo 1532463 2300315 := bstep (se 1 (by rfl) ⟨1725236, by rfl⟩ : syracuseStep 2300315 = 3450473) B3450473
theorem B74611691 : Blo 1532463 74611691 := bstep (se 1 (by rfl) ⟨55958768, by rfl⟩ : syracuseStep 74611691 = 111917537) B111917537
theorem B7371823 : Blo 1532463 7371823 := bstep (se 1 (by rfl) ⟨5528867, by rfl⟩ : syracuseStep 7371823 = 11057735) B11057735
theorem B11640185 : Blo 1532463 11640185 := bstep (se 2 (by rfl) ⟨4365069, by rfl⟩ : syracuseStep 11640185 = 8730139) B8730139
theorem B27991655 : Blo 1532463 27991655 := bstep (se 1 (by rfl) ⟨20993741, by rfl⟩ : syracuseStep 27991655 = 41987483) B41987483
theorem B2301545 : Blo 1532463 2301545 := bstep (se 2 (by rfl) ⟨863079, by rfl⟩ : syracuseStep 2301545 = 1726159) B1726159
theorem B2588287 : Blo 1532463 2588287 := bstep (se 1 (by rfl) ⟨1941215, by rfl⟩ : syracuseStep 2588287 = 3882431) B3882431
theorem B5177087 : Blo 1532463 5177087 := bstep (se 1 (by rfl) ⟨3882815, by rfl⟩ : syracuseStep 5177087 = 7765631) B7765631
theorem B239174147 : Blo 1532463 239174147 := bstep (se 1 (by rfl) ⟨179380610, by rfl⟩ : syracuseStep 239174147 = 358761221) B358761221
theorem B1533543 : Blo 1532463 1533543 := bstep (se 1 (by rfl) ⟨1150157, by rfl⟩ : syracuseStep 1533543 = 2300315) B2300315
theorem B3451049 : Blo 1532463 3451049 := bstep (se 2 (by rfl) ⟨1294143, by rfl⟩ : syracuseStep 3451049 = 2588287) B2588287
theorem B7760123 : Blo 1532463 7760123 := bstep (se 1 (by rfl) ⟨5820092, by rfl⟩ : syracuseStep 7760123 = 11640185) B11640185
theorem B1534363 : Blo 1532463 1534363 := bstep (se 1 (by rfl) ⟨1150772, by rfl⟩ : syracuseStep 1534363 = 2301545) B2301545
theorem B3451391 : Blo 1532463 3451391 := bstep (se 1 (by rfl) ⟨2588543, by rfl⟩ : syracuseStep 3451391 = 5177087) B5177087
theorem B3451931 : Blo 1532463 3451931 := bstep (se 1 (by rfl) ⟨2588948, by rfl⟩ : syracuseStep 3451931 = 5177897) B5177897
theorem B8294471 : Blo 1532463 8294471 := bstep (se 1 (by rfl) ⟨6220853, by rfl⟩ : syracuseStep 8294471 = 12441707) B12441707
theorem B5600623 : Blo 1532463 5600623 := bstep (se 1 (by rfl) ⟨4200467, by rfl⟩ : syracuseStep 5600623 = 8400935) B8400935
theorem B2586377 : Blo 1532463 2586377 := bstep (se 2 (by rfl) ⟨969891, by rfl⟩ : syracuseStep 2586377 = 1939783) B1939783
theorem B9820025 : Blo 1532463 9820025 := bstep (se 2 (by rfl) ⟨3682509, by rfl⟩ : syracuseStep 9820025 = 7365019) B7365019
theorem B103675783 : Blo 1532463 103675783 := bstep (se 1 (by rfl) ⟨77756837, by rfl⟩ : syracuseStep 103675783 = 155513675) B155513675
theorem B17463923 : Blo 1532463 17463923 := bstep (se 1 (by rfl) ⟨13097942, by rfl⟩ : syracuseStep 17463923 = 26195885) B26195885
theorem B9829097 : Blo 1532463 9829097 := bstep (se 2 (by rfl) ⟨3685911, by rfl⟩ : syracuseStep 9829097 = 7371823) B7371823
theorem B3881753 : Blo 1532463 3881753 := bstep (se 2 (by rfl) ⟨1455657, by rfl⟩ : syracuseStep 3881753 = 2911315) B2911315
theorem B49741127 : Blo 1532463 49741127 := bstep (se 1 (by rfl) ⟨37305845, by rfl⟩ : syracuseStep 49741127 = 74611691) B74611691
theorem B18661103 : Blo 1532463 18661103 := bstep (se 1 (by rfl) ⟨13995827, by rfl⟩ : syracuseStep 18661103 = 27991655) B27991655
theorem B5529647 : Blo 1532463 5529647 := bstep (se 1 (by rfl) ⟨4147235, by rfl⟩ : syracuseStep 5529647 = 8294471) B8294471
theorem B159449431 : Blo 1532463 159449431 := bstep (se 1 (by rfl) ⟨119587073, by rfl⟩ : syracuseStep 159449431 = 239174147) B239174147
theorem B6546683 : Blo 1532463 6546683 := bstep (se 1 (by rfl) ⟨4910012, by rfl⟩ : syracuseStep 6546683 = 9820025) B9820025
theorem B11642615 : Blo 1532463 11642615 := bstep (se 1 (by rfl) ⟨8731961, by rfl⟩ : syracuseStep 11642615 = 17463923) B17463923
theorem B138234377 : Blo 1532463 138234377 := bstep (se 2 (by rfl) ⟨51837891, by rfl⟩ : syracuseStep 138234377 = 103675783) B103675783
theorem B1724251 : Blo 1532463 1724251 := bstep (se 1 (by rfl) ⟨1293188, by rfl⟩ : syracuseStep 1724251 = 2586377) B2586377
theorem B5173415 : Blo 1532463 5173415 := bstep (se 1 (by rfl) ⟨3880061, by rfl⟩ : syracuseStep 5173415 = 7760123) B7760123
theorem B7467497 : Blo 1532463 7467497 := bstep (se 2 (by rfl) ⟨2800311, by rfl⟩ : syracuseStep 7467497 = 5600623) B5600623
theorem B12440735 : Blo 1532463 12440735 := bstep (se 1 (by rfl) ⟨9330551, by rfl⟩ : syracuseStep 12440735 = 18661103) B18661103
theorem B2300699 : Blo 1532463 2300699 := bstep (se 1 (by rfl) ⟨1725524, by rfl⟩ : syracuseStep 2300699 = 3451049) B3451049
theorem B2300927 : Blo 1532463 2300927 := bstep (se 1 (by rfl) ⟨1725695, by rfl⟩ : syracuseStep 2300927 = 3451391) B3451391
theorem B6552731 : Blo 1532463 6552731 := bstep (se 1 (by rfl) ⟨4914548, by rfl⟩ : syracuseStep 6552731 = 9829097) B9829097
theorem B2587835 : Blo 1532463 2587835 := bstep (se 1 (by rfl) ⟨1940876, by rfl⟩ : syracuseStep 2587835 = 3881753) B3881753
theorem B2301287 : Blo 1532463 2301287 := bstep (se 1 (by rfl) ⟨1725965, by rfl⟩ : syracuseStep 2301287 = 3451931) B3451931
theorem B33160751 : Blo 1532463 33160751 := bstep (se 1 (by rfl) ⟨24870563, by rfl⟩ : syracuseStep 33160751 = 49741127) B49741127
theorem B3448943 : Blo 1532463 3448943 := bstep (se 1 (by rfl) ⟨2586707, by rfl⟩ : syracuseStep 3448943 = 5173415) B5173415
theorem B14745725 : Blo 1532463 14745725 := bstep (se 3 (by rfl) ⟨2764823, by rfl⟩ : syracuseStep 14745725 = 5529647) B5529647
theorem B212599241 : Blo 1532463 212599241 := bstep (se 2 (by rfl) ⟨79724715, by rfl⟩ : syracuseStep 212599241 = 159449431) B159449431
theorem B1533799 : Blo 1532463 1533799 := bstep (se 1 (by rfl) ⟨1150349, by rfl⟩ : syracuseStep 1533799 = 2300699) B2300699
theorem B1533951 : Blo 1532463 1533951 := bstep (se 1 (by rfl) ⟨1150463, by rfl⟩ : syracuseStep 1533951 = 2300927) B2300927
theorem B4368487 : Blo 1532463 4368487 := bstep (se 1 (by rfl) ⟨3276365, by rfl⟩ : syracuseStep 4368487 = 6552731) B6552731
theorem B1534191 : Blo 1532463 1534191 := bstep (se 1 (by rfl) ⟨1150643, by rfl⟩ : syracuseStep 1534191 = 2301287) B2301287
theorem B8293823 : Blo 1532463 8293823 := bstep (se 1 (by rfl) ⟨6220367, by rfl⟩ : syracuseStep 8293823 = 12440735) B12440735
theorem B7761743 : Blo 1532463 7761743 := bstep (se 1 (by rfl) ⟨5821307, by rfl⟩ : syracuseStep 7761743 = 11642615) B11642615
theorem B92156251 : Blo 1532463 92156251 := bstep (se 1 (by rfl) ⟨69117188, by rfl⟩ : syracuseStep 92156251 = 138234377) B138234377
theorem B1725223 : Blo 1532463 1725223 := bstep (se 1 (by rfl) ⟨1293917, by rfl⟩ : syracuseStep 1725223 = 2587835) B2587835
theorem B22107167 : Blo 1532463 22107167 := bstep (se 1 (by rfl) ⟨16580375, by rfl⟩ : syracuseStep 22107167 = 33160751) B33160751
theorem B2299001 : Blo 1532463 2299001 := bstep (se 2 (by rfl) ⟨862125, by rfl⟩ : syracuseStep 2299001 = 1724251) B1724251
theorem B4978331 : Blo 1532463 4978331 := bstep (se 1 (by rfl) ⟨3733748, by rfl⟩ : syracuseStep 4978331 = 7467497) B7467497
theorem B4364455 : Blo 1532463 4364455 := bstep (se 1 (by rfl) ⟨3273341, by rfl⟩ : syracuseStep 4364455 = 6546683) B6546683
theorem B9830483 : Blo 1532463 9830483 := bstep (se 1 (by rfl) ⟨7372862, by rfl⟩ : syracuseStep 9830483 = 14745725) B14745725
theorem B5824649 : Blo 1532463 5824649 := bstep (se 2 (by rfl) ⟨2184243, by rfl⟩ : syracuseStep 5824649 = 4368487) B4368487
theorem B14738111 : Blo 1532463 14738111 := bstep (se 1 (by rfl) ⟨11053583, by rfl⟩ : syracuseStep 14738111 = 22107167) B22107167
theorem B1532667 : Blo 1532463 1532667 := bstep (se 1 (by rfl) ⟨1149500, by rfl⟩ : syracuseStep 1532667 = 2299001) B2299001
theorem B3318887 : Blo 1532463 3318887 := bstep (se 1 (by rfl) ⟨2489165, by rfl⟩ : syracuseStep 3318887 = 4978331) B4978331
theorem B5819273 : Blo 1532463 5819273 := bstep (se 2 (by rfl) ⟨2182227, by rfl⟩ : syracuseStep 5819273 = 4364455) B4364455
theorem B141732827 : Blo 1532463 141732827 := bstep (se 1 (by rfl) ⟨106299620, by rfl⟩ : syracuseStep 141732827 = 212599241) B212599241
theorem B122875001 : Blo 1532463 122875001 := bstep (se 2 (by rfl) ⟨46078125, by rfl⟩ : syracuseStep 122875001 = 92156251) B92156251
theorem B5174495 : Blo 1532463 5174495 := bstep (se 1 (by rfl) ⟨3880871, by rfl⟩ : syracuseStep 5174495 = 7761743) B7761743
theorem B2299295 : Blo 1532463 2299295 := bstep (se 1 (by rfl) ⟨1724471, by rfl⟩ : syracuseStep 2299295 = 3448943) B3448943
theorem B2300297 : Blo 1532463 2300297 := bstep (se 2 (by rfl) ⟨862611, by rfl⟩ : syracuseStep 2300297 = 1725223) B1725223
theorem B5529215 : Blo 1532463 5529215 := bstep (se 1 (by rfl) ⟨4146911, by rfl⟩ : syracuseStep 5529215 = 8293823) B8293823
theorem B6553655 : Blo 1532463 6553655 := bstep (se 1 (by rfl) ⟨4915241, by rfl⟩ : syracuseStep 6553655 = 9830483) B9830483
theorem B3883099 : Blo 1532463 3883099 := bstep (se 1 (by rfl) ⟨2912324, by rfl⟩ : syracuseStep 3883099 = 5824649) B5824649
theorem B2212591 : Blo 1532463 2212591 := bstep (se 1 (by rfl) ⟨1659443, by rfl⟩ : syracuseStep 2212591 = 3318887) B3318887
theorem B3449663 : Blo 1532463 3449663 := bstep (se 1 (by rfl) ⟨2587247, by rfl⟩ : syracuseStep 3449663 = 5174495) B5174495
theorem B1532863 : Blo 1532463 1532863 := bstep (se 1 (by rfl) ⟨1149647, by rfl⟩ : syracuseStep 1532863 = 2299295) B2299295
theorem B1533531 : Blo 1532463 1533531 := bstep (se 1 (by rfl) ⟨1150148, by rfl⟩ : syracuseStep 1533531 = 2300297) B2300297
theorem B94488551 : Blo 1532463 94488551 := bstep (se 1 (by rfl) ⟨70866413, by rfl⟩ : syracuseStep 94488551 = 141732827) B141732827
theorem B9825407 : Blo 1532463 9825407 := bstep (se 1 (by rfl) ⟨7369055, by rfl⟩ : syracuseStep 9825407 = 14738111) B14738111
theorem B3879515 : Blo 1532463 3879515 := bstep (se 1 (by rfl) ⟨2909636, by rfl⟩ : syracuseStep 3879515 = 5819273) B5819273
theorem B81916667 : Blo 1532463 81916667 := bstep (se 1 (by rfl) ⟨61437500, by rfl⟩ : syracuseStep 81916667 = 122875001) B122875001
theorem B3686143 : Blo 1532463 3686143 := bstep (se 1 (by rfl) ⟨2764607, by rfl⟩ : syracuseStep 3686143 = 5529215) B5529215
theorem B5177465 : Blo 1532463 5177465 := bstep (se 2 (by rfl) ⟨1941549, by rfl⟩ : syracuseStep 5177465 = 3883099) B3883099
theorem B2950121 : Blo 1532463 2950121 := bstep (se 2 (by rfl) ⟨1106295, by rfl⟩ : syracuseStep 2950121 = 2212591) B2212591
theorem B4369103 : Blo 1532463 4369103 := bstep (se 1 (by rfl) ⟨3276827, by rfl⟩ : syracuseStep 4369103 = 6553655) B6553655
theorem B54611111 : Blo 1532463 54611111 := bstep (se 1 (by rfl) ⟨40958333, by rfl⟩ : syracuseStep 54611111 = 81916667) B81916667
theorem B62992367 : Blo 1532463 62992367 := bstep (se 1 (by rfl) ⟨47244275, by rfl⟩ : syracuseStep 62992367 = 94488551) B94488551
theorem B6550271 : Blo 1532463 6550271 := bstep (se 1 (by rfl) ⟨4912703, by rfl⟩ : syracuseStep 6550271 = 9825407) B9825407
theorem B2586343 : Blo 1532463 2586343 := bstep (se 1 (by rfl) ⟨1939757, by rfl⟩ : syracuseStep 2586343 = 3879515) B3879515
theorem B2299775 : Blo 1532463 2299775 := bstep (se 1 (by rfl) ⟨1724831, by rfl⟩ : syracuseStep 2299775 = 3449663) B3449663
theorem B4914857 : Blo 1532463 4914857 := bstep (se 2 (by rfl) ⟨1843071, by rfl⟩ : syracuseStep 4914857 = 3686143) B3686143
theorem B4366847 : Blo 1532463 4366847 := bstep (se 1 (by rfl) ⟨3275135, by rfl⟩ : syracuseStep 4366847 = 6550271) B6550271
theorem B1533183 : Blo 1532463 1533183 := bstep (se 1 (by rfl) ⟨1149887, by rfl⟩ : syracuseStep 1533183 = 2299775) B2299775
theorem B36407407 : Blo 1532463 36407407 := bstep (se 1 (by rfl) ⟨27305555, by rfl⟩ : syracuseStep 36407407 = 54611111) B54611111
theorem B7866989 : Blo 1532463 7866989 := bstep (se 3 (by rfl) ⟨1475060, by rfl⟩ : syracuseStep 7866989 = 2950121) B2950121
theorem B41994911 : Blo 1532463 41994911 := bstep (se 1 (by rfl) ⟨31496183, by rfl⟩ : syracuseStep 41994911 = 62992367) B62992367
theorem B3451643 : Blo 1532463 3451643 := bstep (se 1 (by rfl) ⟨2588732, by rfl⟩ : syracuseStep 3451643 = 5177465) B5177465
theorem B2912735 : Blo 1532463 2912735 := bstep (se 1 (by rfl) ⟨2184551, by rfl⟩ : syracuseStep 2912735 = 4369103) B4369103
theorem B3448457 : Blo 1532463 3448457 := bstep (se 2 (by rfl) ⟨1293171, by rfl⟩ : syracuseStep 3448457 = 2586343) B2586343
theorem B3276571 : Blo 1532463 3276571 := bstep (se 1 (by rfl) ⟨2457428, by rfl⟩ : syracuseStep 3276571 = 4914857) B4914857
theorem B1941823 : Blo 1532463 1941823 := bstep (se 1 (by rfl) ⟨1456367, by rfl⟩ : syracuseStep 1941823 = 2912735) B2912735
theorem B5244659 : Blo 1532463 5244659 := bstep (se 1 (by rfl) ⟨3933494, by rfl⟩ : syracuseStep 5244659 = 7866989) B7866989
theorem B4368761 : Blo 1532463 4368761 := bstep (se 2 (by rfl) ⟨1638285, by rfl⟩ : syracuseStep 4368761 = 3276571) B3276571
theorem B2911231 : Blo 1532463 2911231 := bstep (se 1 (by rfl) ⟨2183423, by rfl⟩ : syracuseStep 2911231 = 4366847) B4366847
theorem B27996607 : Blo 1532463 27996607 := bstep (se 1 (by rfl) ⟨20997455, by rfl⟩ : syracuseStep 27996607 = 41994911) B41994911
theorem B2298971 : Blo 1532463 2298971 := bstep (se 1 (by rfl) ⟨1724228, by rfl⟩ : syracuseStep 2298971 = 3448457) B3448457
theorem B48543209 : Blo 1532463 48543209 := bstep (se 2 (by rfl) ⟨18203703, by rfl⟩ : syracuseStep 48543209 = 36407407) B36407407
theorem B2301095 : Blo 1532463 2301095 := bstep (se 1 (by rfl) ⟨1725821, by rfl⟩ : syracuseStep 2301095 = 3451643) B3451643
theorem B2589097 : Blo 1532463 2589097 := bstep (se 2 (by rfl) ⟨970911, by rfl⟩ : syracuseStep 2589097 = 1941823) B1941823
theorem B1532647 : Blo 1532463 1532647 := bstep (se 1 (by rfl) ⟨1149485, by rfl⟩ : syracuseStep 1532647 = 2298971) B2298971
theorem B1534063 : Blo 1532463 1534063 := bstep (se 1 (by rfl) ⟨1150547, by rfl⟩ : syracuseStep 1534063 = 2301095) B2301095
theorem B32362139 : Blo 1532463 32362139 := bstep (se 1 (by rfl) ⟨24271604, by rfl⟩ : syracuseStep 32362139 = 48543209) B48543209
theorem B2912507 : Blo 1532463 2912507 := bstep (se 1 (by rfl) ⟨2184380, by rfl⟩ : syracuseStep 2912507 = 4368761) B4368761
theorem B37328809 : Blo 1532463 37328809 := bstep (se 2 (by rfl) ⟨13998303, by rfl⟩ : syracuseStep 37328809 = 27996607) B27996607
theorem B3496439 : Blo 1532463 3496439 := bstep (se 1 (by rfl) ⟨2622329, by rfl⟩ : syracuseStep 3496439 = 5244659) B5244659
theorem B3881641 : Blo 1532463 3881641 := bstep (se 2 (by rfl) ⟨1455615, by rfl⟩ : syracuseStep 3881641 = 2911231) B2911231
theorem B1941671 : Blo 1532463 1941671 := bstep (se 1 (by rfl) ⟨1456253, by rfl⟩ : syracuseStep 1941671 = 2912507) B2912507
theorem B3452129 : Blo 1532463 3452129 := bstep (se 2 (by rfl) ⟨1294548, by rfl⟩ : syracuseStep 3452129 = 2589097) B2589097
theorem B2330959 : Blo 1532463 2330959 := bstep (se 1 (by rfl) ⟨1748219, by rfl⟩ : syracuseStep 2330959 = 3496439) B3496439
theorem B21574759 : Blo 1532463 21574759 := bstep (se 1 (by rfl) ⟨16181069, by rfl⟩ : syracuseStep 21574759 = 32362139) B32362139
theorem B49771745 : Blo 1532463 49771745 := bstep (se 2 (by rfl) ⟨18664404, by rfl⟩ : syracuseStep 49771745 = 37328809) B37328809
theorem B5175521 : Blo 1532463 5175521 := bstep (se 2 (by rfl) ⟨1940820, by rfl⟩ : syracuseStep 5175521 = 3881641) B3881641
theorem B5177789 : Blo 1532463 5177789 := bstep (se 3 (by rfl) ⟨970835, by rfl⟩ : syracuseStep 5177789 = 1941671) B1941671
theorem B3450347 : Blo 1532463 3450347 := bstep (se 1 (by rfl) ⟨2587760, by rfl⟩ : syracuseStep 3450347 = 5175521) B5175521
theorem B3107945 : Blo 1532463 3107945 := bstep (se 2 (by rfl) ⟨1165479, by rfl⟩ : syracuseStep 3107945 = 2330959) B2330959
theorem B33181163 : Blo 1532463 33181163 := bstep (se 1 (by rfl) ⟨24885872, by rfl⟩ : syracuseStep 33181163 = 49771745) B49771745
theorem B28766345 : Blo 1532463 28766345 := bstep (se 2 (by rfl) ⟨10787379, by rfl⟩ : syracuseStep 28766345 = 21574759) B21574759
theorem B2301419 : Blo 1532463 2301419 := bstep (se 1 (by rfl) ⟨1726064, by rfl⟩ : syracuseStep 2301419 = 3452129) B3452129
theorem B76710253 : Blo 1532463 76710253 := bstep (se 3 (by rfl) ⟨14383172, by rfl⟩ : syracuseStep 76710253 = 28766345) B28766345
theorem B1534279 : Blo 1532463 1534279 := bstep (se 1 (by rfl) ⟨1150709, by rfl⟩ : syracuseStep 1534279 = 2301419) B2301419
theorem B22120775 : Blo 1532463 22120775 := bstep (se 1 (by rfl) ⟨16590581, by rfl⟩ : syracuseStep 22120775 = 33181163) B33181163
theorem B3451859 : Blo 1532463 3451859 := bstep (se 1 (by rfl) ⟨2588894, by rfl⟩ : syracuseStep 3451859 = 5177789) B5177789
theorem B2300231 : Blo 1532463 2300231 := bstep (se 1 (by rfl) ⟨1725173, by rfl⟩ : syracuseStep 2300231 = 3450347) B3450347
theorem B2071963 : Blo 1532463 2071963 := bstep (se 1 (by rfl) ⟨1553972, by rfl⟩ : syracuseStep 2071963 = 3107945) B3107945
theorem B1533487 : Blo 1532463 1533487 := bstep (se 1 (by rfl) ⟨1150115, by rfl⟩ : syracuseStep 1533487 = 2300231) B2300231
theorem B14747183 : Blo 1532463 14747183 := bstep (se 1 (by rfl) ⟨11060387, by rfl⟩ : syracuseStep 14747183 = 22120775) B22120775
theorem B2762617 : Blo 1532463 2762617 := bstep (se 2 (by rfl) ⟨1035981, by rfl⟩ : syracuseStep 2762617 = 2071963) B2071963
theorem B102280337 : Blo 1532463 102280337 := bstep (se 2 (by rfl) ⟨38355126, by rfl⟩ : syracuseStep 102280337 = 76710253) B76710253
theorem B2301239 : Blo 1532463 2301239 := bstep (se 1 (by rfl) ⟨1725929, by rfl⟩ : syracuseStep 2301239 = 3451859) B3451859
theorem B9831455 : Blo 1532463 9831455 := bstep (se 1 (by rfl) ⟨7373591, by rfl⟩ : syracuseStep 9831455 = 14747183) B14747183
theorem B1534159 : Blo 1532463 1534159 := bstep (se 1 (by rfl) ⟨1150619, by rfl⟩ : syracuseStep 1534159 = 2301239) B2301239
theorem B68186891 : Blo 1532463 68186891 := bstep (se 1 (by rfl) ⟨51140168, by rfl⟩ : syracuseStep 68186891 = 102280337) B102280337
theorem B3683489 : Blo 1532463 3683489 := bstep (se 2 (by rfl) ⟨1381308, by rfl⟩ : syracuseStep 3683489 = 2762617) B2762617
theorem B9822637 : Blo 1532463 9822637 := bstep (se 3 (by rfl) ⟨1841744, by rfl⟩ : syracuseStep 9822637 = 3683489) B3683489
theorem B6554303 : Blo 1532463 6554303 := bstep (se 1 (by rfl) ⟨4915727, by rfl⟩ : syracuseStep 6554303 = 9831455) B9831455
theorem B181831709 : Blo 1532463 181831709 := bstep (se 3 (by rfl) ⟨34093445, by rfl⟩ : syracuseStep 181831709 = 68186891) B68186891
theorem B4369535 : Blo 1532463 4369535 := bstep (se 1 (by rfl) ⟨3277151, by rfl⟩ : syracuseStep 4369535 = 6554303) B6554303
theorem B121221139 : Blo 1532463 121221139 := bstep (se 1 (by rfl) ⟨90915854, by rfl⟩ : syracuseStep 121221139 = 181831709) B181831709
theorem B13096849 : Blo 1532463 13096849 := bstep (se 2 (by rfl) ⟨4911318, by rfl⟩ : syracuseStep 13096849 = 9822637) B9822637
theorem B161628185 : Blo 1532463 161628185 := bstep (se 2 (by rfl) ⟨60610569, by rfl⟩ : syracuseStep 161628185 = 121221139) B121221139
theorem B2913023 : Blo 1532463 2913023 := bstep (se 1 (by rfl) ⟨2184767, by rfl⟩ : syracuseStep 2913023 = 4369535) B4369535
theorem B17462465 : Blo 1532463 17462465 := bstep (se 2 (by rfl) ⟨6548424, by rfl⟩ : syracuseStep 17462465 = 13096849) B13096849
theorem B11641643 : Blo 1532463 11641643 := bstep (se 1 (by rfl) ⟨8731232, by rfl⟩ : syracuseStep 11641643 = 17462465) B17462465
theorem B7768061 : Blo 1532463 7768061 := bstep (se 3 (by rfl) ⟨1456511, by rfl⟩ : syracuseStep 7768061 = 2913023) B2913023
theorem B107752123 : Blo 1532463 107752123 := bstep (se 1 (by rfl) ⟨80814092, by rfl⟩ : syracuseStep 107752123 = 161628185) B161628185
theorem B5178707 : Blo 1532463 5178707 := bstep (se 1 (by rfl) ⟨3884030, by rfl⟩ : syracuseStep 5178707 = 7768061) B7768061
theorem B7761095 : Blo 1532463 7761095 := bstep (se 1 (by rfl) ⟨5820821, by rfl⟩ : syracuseStep 7761095 = 11641643) B11641643
theorem B143669497 : Blo 1532463 143669497 := bstep (se 2 (by rfl) ⟨53876061, by rfl⟩ : syracuseStep 143669497 = 107752123) B107752123
theorem B3452471 : Blo 1532463 3452471 := bstep (se 1 (by rfl) ⟨2589353, by rfl⟩ : syracuseStep 3452471 = 5178707) B5178707
theorem B5174063 : Blo 1532463 5174063 := bstep (se 1 (by rfl) ⟨3880547, by rfl⟩ : syracuseStep 5174063 = 7761095) B7761095
theorem B191559329 : Blo 1532463 191559329 := bstep (se 2 (by rfl) ⟨71834748, by rfl⟩ : syracuseStep 191559329 = 143669497) B143669497
theorem B3449375 : Blo 1532463 3449375 := bstep (se 1 (by rfl) ⟨2587031, by rfl⟩ : syracuseStep 3449375 = 5174063) B5174063
theorem B127706219 : Blo 1532463 127706219 := bstep (se 1 (by rfl) ⟨95779664, by rfl⟩ : syracuseStep 127706219 = 191559329) B191559329
theorem B2301647 : Blo 1532463 2301647 := bstep (se 1 (by rfl) ⟨1726235, by rfl⟩ : syracuseStep 2301647 = 3452471) B3452471
theorem B1534431 : Blo 1532463 1534431 := bstep (se 1 (by rfl) ⟨1150823, by rfl⟩ : syracuseStep 1534431 = 2301647) B2301647
theorem B2299583 : Blo 1532463 2299583 := bstep (se 1 (by rfl) ⟨1724687, by rfl⟩ : syracuseStep 2299583 = 3449375) B3449375
theorem B85137479 : Blo 1532463 85137479 := bstep (se 1 (by rfl) ⟨63853109, by rfl⟩ : syracuseStep 85137479 = 127706219) B127706219
theorem B1533055 : Blo 1532463 1533055 := bstep (se 1 (by rfl) ⟨1149791, by rfl⟩ : syracuseStep 1533055 = 2299583) B2299583
theorem B56758319 : Blo 1532463 56758319 := bstep (se 1 (by rfl) ⟨42568739, by rfl⟩ : syracuseStep 56758319 = 85137479) B85137479
theorem B37838879 : Blo 1532463 37838879 := bstep (se 1 (by rfl) ⟨28379159, by rfl⟩ : syracuseStep 37838879 = 56758319) B56758319
theorem B25225919 : Blo 1532463 25225919 := bstep (se 1 (by rfl) ⟨18919439, by rfl⟩ : syracuseStep 25225919 = 37838879) B37838879
theorem B16817279 : Blo 1532463 16817279 := bstep (se 1 (by rfl) ⟨12612959, by rfl⟩ : syracuseStep 16817279 = 25225919) B25225919
theorem B44846077 : Blo 1532463 44846077 := bstep (se 3 (by rfl) ⟨8408639, by rfl⟩ : syracuseStep 44846077 = 16817279) B16817279
theorem B59794769 : Blo 1532463 59794769 := bstep (se 2 (by rfl) ⟨22423038, by rfl⟩ : syracuseStep 59794769 = 44846077) B44846077
theorem B39863179 : Blo 1532463 39863179 := bstep (se 1 (by rfl) ⟨29897384, by rfl⟩ : syracuseStep 39863179 = 59794769) B59794769
theorem B53150905 : Blo 1532463 53150905 := bstep (se 2 (by rfl) ⟨19931589, by rfl⟩ : syracuseStep 53150905 = 39863179) B39863179
theorem B70867873 : Blo 1532463 70867873 := bstep (se 2 (by rfl) ⟨26575452, by rfl⟩ : syracuseStep 70867873 = 53150905) B53150905
theorem B94490497 : Blo 1532463 94490497 := bstep (se 2 (by rfl) ⟨35433936, by rfl⟩ : syracuseStep 94490497 = 70867873) B70867873
theorem B125987329 : Blo 1532463 125987329 := bstep (se 2 (by rfl) ⟨47245248, by rfl⟩ : syracuseStep 125987329 = 94490497) B94490497
theorem B167983105 : Blo 1532463 167983105 := bstep (se 2 (by rfl) ⟨62993664, by rfl⟩ : syracuseStep 167983105 = 125987329) B125987329
theorem B223977473 : Blo 1532463 223977473 := bstep (se 2 (by rfl) ⟨83991552, by rfl⟩ : syracuseStep 223977473 = 167983105) B167983105
theorem B149318315 : Blo 1532463 149318315 := bstep (se 1 (by rfl) ⟨111988736, by rfl⟩ : syracuseStep 149318315 = 223977473) B223977473
theorem B99545543 : Blo 1532463 99545543 := bstep (se 1 (by rfl) ⟨74659157, by rfl⟩ : syracuseStep 99545543 = 149318315) B149318315
theorem B66363695 : Blo 1532463 66363695 := bstep (se 1 (by rfl) ⟨49772771, by rfl⟩ : syracuseStep 66363695 = 99545543) B99545543
theorem B44242463 : Blo 1532463 44242463 := bstep (se 1 (by rfl) ⟨33181847, by rfl⟩ : syracuseStep 44242463 = 66363695) B66363695
theorem B29494975 : Blo 1532463 29494975 := bstep (se 1 (by rfl) ⟨22121231, by rfl⟩ : syracuseStep 29494975 = 44242463) B44242463
theorem B39326633 : Blo 1532463 39326633 := bstep (se 2 (by rfl) ⟨14747487, by rfl⟩ : syracuseStep 39326633 = 29494975) B29494975
theorem B26217755 : Blo 1532463 26217755 := bstep (se 1 (by rfl) ⟨19663316, by rfl⟩ : syracuseStep 26217755 = 39326633) B39326633
theorem B17478503 : Blo 1532463 17478503 := bstep (se 1 (by rfl) ⟨13108877, by rfl⟩ : syracuseStep 17478503 = 26217755) B26217755
theorem B11652335 : Blo 1532463 11652335 := bstep (se 1 (by rfl) ⟨8739251, by rfl⟩ : syracuseStep 11652335 = 17478503) B17478503
theorem B7768223 : Blo 1532463 7768223 := bstep (se 1 (by rfl) ⟨5826167, by rfl⟩ : syracuseStep 7768223 = 11652335) B11652335
theorem B5178815 : Blo 1532463 5178815 := bstep (se 1 (by rfl) ⟨3884111, by rfl⟩ : syracuseStep 5178815 = 7768223) B7768223
theorem B3452543 : Blo 1532463 3452543 := bstep (se 1 (by rfl) ⟨2589407, by rfl⟩ : syracuseStep 3452543 = 5178815) B5178815
theorem B2301695 : Blo 1532463 2301695 := bstep (se 1 (by rfl) ⟨1726271, by rfl⟩ : syracuseStep 2301695 = 3452543) B3452543
theorem B1534463 : Blo 1532463 1534463 := bstep (se 1 (by rfl) ⟨1150847, by rfl⟩ : syracuseStep 1534463 = 2301695) B2301695

theorem C0 (j : ℕ) (h1 : 383115 ≤ j) (h2 : j ≤ 383615) : Blo 1532463 (4 * j + 3) := by
  interval_cases j
  · exact B1532463
  · exact B1532467
  · exact B1532471
  · exact B1532475
  · exact B1532479
  · exact B1532483
  · exact B1532487
  · exact B1532491
  · exact B1532495
  · exact B1532499
  · exact B1532503
  · exact B1532507
  · exact B1532511
  · exact B1532515
  · exact B1532519
  · exact B1532523
  · exact B1532527
  · exact B1532531
  · exact B1532535
  · exact B1532539
  · exact B1532543
  · exact B1532547
  · exact B1532551
  · exact B1532555
  · exact B1532559
  · exact B1532563
  · exact B1532567
  · exact B1532571
  · exact B1532575
  · exact B1532579
  · exact B1532583
  · exact B1532587
  · exact B1532591
  · exact B1532595
  · exact B1532599
  · exact B1532603
  · exact B1532607
  · exact B1532611
  · exact B1532615
  · exact B1532619
  · exact B1532623
  · exact B1532627
  · exact B1532631
  · exact B1532635
  · exact B1532639
  · exact B1532643
  · exact B1532647
  · exact B1532651
  · exact B1532655
  · exact B1532659
  · exact B1532663
  · exact B1532667
  · exact B1532671
  · exact B1532675
  · exact B1532679
  · exact B1532683
  · exact B1532687
  · exact B1532691
  · exact B1532695
  · exact B1532699
  · exact B1532703
  · exact B1532707
  · exact B1532711
  · exact B1532715
  · exact B1532719
  · exact B1532723
  · exact B1532727
  · exact B1532731
  · exact B1532735
  · exact B1532739
  · exact B1532743
  · exact B1532747
  · exact B1532751
  · exact B1532755
  · exact B1532759
  · exact B1532763
  · exact B1532767
  · exact B1532771
  · exact B1532775
  · exact B1532779
  · exact B1532783
  · exact B1532787
  · exact B1532791
  · exact B1532795
  · exact B1532799
  · exact B1532803
  · exact B1532807
  · exact B1532811
  · exact B1532815
  · exact B1532819
  · exact B1532823
  · exact B1532827
  · exact B1532831
  · exact B1532835
  · exact B1532839
  · exact B1532843
  · exact B1532847
  · exact B1532851
  · exact B1532855
  · exact B1532859
  · exact B1532863
  · exact B1532867
  · exact B1532871
  · exact B1532875
  · exact B1532879
  · exact B1532883
  · exact B1532887
  · exact B1532891
  · exact B1532895
  · exact B1532899
  · exact B1532903
  · exact B1532907
  · exact B1532911
  · exact B1532915
  · exact B1532919
  · exact B1532923
  · exact B1532927
  · exact B1532931
  · exact B1532935
  · exact B1532939
  · exact B1532943
  · exact B1532947
  · exact B1532951
  · exact B1532955
  · exact B1532959
  · exact B1532963
  · exact B1532967
  · exact B1532971
  · exact B1532975
  · exact B1532979
  · exact B1532983
  · exact B1532987
  · exact B1532991
  · exact B1532995
  · exact B1532999
  · exact B1533003
  · exact B1533007
  · exact B1533011
  · exact B1533015
  · exact B1533019
  · exact B1533023
  · exact B1533027
  · exact B1533031
  · exact B1533035
  · exact B1533039
  · exact B1533043
  · exact B1533047
  · exact B1533051
  · exact B1533055
  · exact B1533059
  · exact B1533063
  · exact B1533067
  · exact B1533071
  · exact B1533075
  · exact B1533079
  · exact B1533083
  · exact B1533087
  · exact B1533091
  · exact B1533095
  · exact B1533099
  · exact B1533103
  · exact B1533107
  · exact B1533111
  · exact B1533115
  · exact B1533119
  · exact B1533123
  · exact B1533127
  · exact B1533131
  · exact B1533135
  · exact B1533139
  · exact B1533143
  · exact B1533147
  · exact B1533151
  · exact B1533155
  · exact B1533159
  · exact B1533163
  · exact B1533167
  · exact B1533171
  · exact B1533175
  · exact B1533179
  · exact B1533183
  · exact B1533187
  · exact B1533191
  · exact B1533195
  · exact B1533199
  · exact B1533203
  · exact B1533207
  · exact B1533211
  · exact B1533215
  · exact B1533219
  · exact B1533223
  · exact B1533227
  · exact B1533231
  · exact B1533235
  · exact B1533239
  · exact B1533243
  · exact B1533247
  · exact B1533251
  · exact B1533255
  · exact B1533259
  · exact B1533263
  · exact B1533267
  · exact B1533271
  · exact B1533275
  · exact B1533279
  · exact B1533283
  · exact B1533287
  · exact B1533291
  · exact B1533295
  · exact B1533299
  · exact B1533303
  · exact B1533307
  · exact B1533311
  · exact B1533315
  · exact B1533319
  · exact B1533323
  · exact B1533327
  · exact B1533331
  · exact B1533335
  · exact B1533339
  · exact B1533343
  · exact B1533347
  · exact B1533351
  · exact B1533355
  · exact B1533359
  · exact B1533363
  · exact B1533367
  · exact B1533371
  · exact B1533375
  · exact B1533379
  · exact B1533383
  · exact B1533387
  · exact B1533391
  · exact B1533395
  · exact B1533399
  · exact B1533403
  · exact B1533407
  · exact B1533411
  · exact B1533415
  · exact B1533419
  · exact B1533423
  · exact B1533427
  · exact B1533431
  · exact B1533435
  · exact B1533439
  · exact B1533443
  · exact B1533447
  · exact B1533451
  · exact B1533455
  · exact B1533459
  · exact B1533463
  · exact B1533467
  · exact B1533471
  · exact B1533475
  · exact B1533479
  · exact B1533483
  · exact B1533487
  · exact B1533491
  · exact B1533495
  · exact B1533499
  · exact B1533503
  · exact B1533507
  · exact B1533511
  · exact B1533515
  · exact B1533519
  · exact B1533523
  · exact B1533527
  · exact B1533531
  · exact B1533535
  · exact B1533539
  · exact B1533543
  · exact B1533547
  · exact B1533551
  · exact B1533555
  · exact B1533559
  · exact B1533563
  · exact B1533567
  · exact B1533571
  · exact B1533575
  · exact B1533579
  · exact B1533583
  · exact B1533587
  · exact B1533591
  · exact B1533595
  · exact B1533599
  · exact B1533603
  · exact B1533607
  · exact B1533611
  · exact B1533615
  · exact B1533619
  · exact B1533623
  · exact B1533627
  · exact B1533631
  · exact B1533635
  · exact B1533639
  · exact B1533643
  · exact B1533647
  · exact B1533651
  · exact B1533655
  · exact B1533659
  · exact B1533663
  · exact B1533667
  · exact B1533671
  · exact B1533675
  · exact B1533679
  · exact B1533683
  · exact B1533687
  · exact B1533691
  · exact B1533695
  · exact B1533699
  · exact B1533703
  · exact B1533707
  · exact B1533711
  · exact B1533715
  · exact B1533719
  · exact B1533723
  · exact B1533727
  · exact B1533731
  · exact B1533735
  · exact B1533739
  · exact B1533743
  · exact B1533747
  · exact B1533751
  · exact B1533755
  · exact B1533759
  · exact B1533763
  · exact B1533767
  · exact B1533771
  · exact B1533775
  · exact B1533779
  · exact B1533783
  · exact B1533787
  · exact B1533791
  · exact B1533795
  · exact B1533799
  · exact B1533803
  · exact B1533807
  · exact B1533811
  · exact B1533815
  · exact B1533819
  · exact B1533823
  · exact B1533827
  · exact B1533831
  · exact B1533835
  · exact B1533839
  · exact B1533843
  · exact B1533847
  · exact B1533851
  · exact B1533855
  · exact B1533859
  · exact B1533863
  · exact B1533867
  · exact B1533871
  · exact B1533875
  · exact B1533879
  · exact B1533883
  · exact B1533887
  · exact B1533891
  · exact B1533895
  · exact B1533899
  · exact B1533903
  · exact B1533907
  · exact B1533911
  · exact B1533915
  · exact B1533919
  · exact B1533923
  · exact B1533927
  · exact B1533931
  · exact B1533935
  · exact B1533939
  · exact B1533943
  · exact B1533947
  · exact B1533951
  · exact B1533955
  · exact B1533959
  · exact B1533963
  · exact B1533967
  · exact B1533971
  · exact B1533975
  · exact B1533979
  · exact B1533983
  · exact B1533987
  · exact B1533991
  · exact B1533995
  · exact B1533999
  · exact B1534003
  · exact B1534007
  · exact B1534011
  · exact B1534015
  · exact B1534019
  · exact B1534023
  · exact B1534027
  · exact B1534031
  · exact B1534035
  · exact B1534039
  · exact B1534043
  · exact B1534047
  · exact B1534051
  · exact B1534055
  · exact B1534059
  · exact B1534063
  · exact B1534067
  · exact B1534071
  · exact B1534075
  · exact B1534079
  · exact B1534083
  · exact B1534087
  · exact B1534091
  · exact B1534095
  · exact B1534099
  · exact B1534103
  · exact B1534107
  · exact B1534111
  · exact B1534115
  · exact B1534119
  · exact B1534123
  · exact B1534127
  · exact B1534131
  · exact B1534135
  · exact B1534139
  · exact B1534143
  · exact B1534147
  · exact B1534151
  · exact B1534155
  · exact B1534159
  · exact B1534163
  · exact B1534167
  · exact B1534171
  · exact B1534175
  · exact B1534179
  · exact B1534183
  · exact B1534187
  · exact B1534191
  · exact B1534195
  · exact B1534199
  · exact B1534203
  · exact B1534207
  · exact B1534211
  · exact B1534215
  · exact B1534219
  · exact B1534223
  · exact B1534227
  · exact B1534231
  · exact B1534235
  · exact B1534239
  · exact B1534243
  · exact B1534247
  · exact B1534251
  · exact B1534255
  · exact B1534259
  · exact B1534263
  · exact B1534267
  · exact B1534271
  · exact B1534275
  · exact B1534279
  · exact B1534283
  · exact B1534287
  · exact B1534291
  · exact B1534295
  · exact B1534299
  · exact B1534303
  · exact B1534307
  · exact B1534311
  · exact B1534315
  · exact B1534319
  · exact B1534323
  · exact B1534327
  · exact B1534331
  · exact B1534335
  · exact B1534339
  · exact B1534343
  · exact B1534347
  · exact B1534351
  · exact B1534355
  · exact B1534359
  · exact B1534363
  · exact B1534367
  · exact B1534371
  · exact B1534375
  · exact B1534379
  · exact B1534383
  · exact B1534387
  · exact B1534391
  · exact B1534395
  · exact B1534399
  · exact B1534403
  · exact B1534407
  · exact B1534411
  · exact B1534415
  · exact B1534419
  · exact B1534423
  · exact B1534427
  · exact B1534431
  · exact B1534435
  · exact B1534439
  · exact B1534443
  · exact B1534447
  · exact B1534451
  · exact B1534455
  · exact B1534459
  · exact B1534463

theorem solution (m : ℕ) (hlo : 1532463 ≤ m) (hhi : m ≤ 1534463) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 383115 ≤ j := by omega
    have hj2 : j ≤ 383615 := by omega
    have hb : Blo 1532463 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
