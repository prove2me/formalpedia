-- Prove2me | solution 1 for syracuse_descends_range_1794098_1796098
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:48:26.28671+00:00
-- url     : https://prove2.me/submissions/83f4dbba-bf6d-4d35-82ff-c66bb0a7e3aa

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


theorem B4038677 : Blo 1794098 4038677 := bbase (se 6 (by rfl) ⟨94656, by rfl⟩ : syracuseStep 4038677 = 189313) (by norm_num)
theorem B1916957 : Blo 1794098 1916957 := bbase (se 3 (by rfl) ⟨359429, by rfl⟩ : syracuseStep 1916957 = 718859) (by norm_num)
theorem B2555965 : Blo 1794098 2555965 := bbase (se 3 (by rfl) ⟨479243, by rfl⟩ : syracuseStep 2555965 = 958487) (by norm_num)
theorem B4038749 : Blo 1794098 4038749 := bbase (se 3 (by rfl) ⟨757265, by rfl⟩ : syracuseStep 4038749 = 1514531) (by norm_num)
theorem B1818781 : Blo 1794098 1818781 := bbase (se 3 (by rfl) ⟨341021, by rfl⟩ : syracuseStep 1818781 = 682043) (by norm_num)
theorem B4038821 : Blo 1794098 4038821 := bbase (se 4 (by rfl) ⟨378639, by rfl⟩ : syracuseStep 4038821 = 757279) (by norm_num)
theorem B1917145 : Blo 1794098 1917145 := bbase (se 2 (by rfl) ⟨718929, by rfl⟩ : syracuseStep 1917145 = 1437859) (by norm_num)
theorem B5751013 : Blo 1794098 5751013 := bbase (se 4 (by rfl) ⟨539157, by rfl⟩ : syracuseStep 5751013 = 1078315) (by norm_num)
theorem B4038893 : Blo 1794098 4038893 := bbase (se 3 (by rfl) ⟨757292, by rfl⟩ : syracuseStep 4038893 = 1514585) (by norm_num)
theorem B4038965 : Blo 1794098 4038965 := bbase (se 5 (by rfl) ⟨189326, by rfl⟩ : syracuseStep 4038965 = 378653) (by norm_num)
theorem B3834221 : Blo 1794098 3834221 := bbase (se 3 (by rfl) ⟨718916, by rfl⟩ : syracuseStep 3834221 = 1437833) (by norm_num)
theorem B4039037 : Blo 1794098 4039037 := bbase (se 3 (by rfl) ⟨757319, by rfl⟩ : syracuseStep 4039037 = 1514639) (by norm_num)
theorem B7668101 : Blo 1794098 7668101 := bbase (se 4 (by rfl) ⟨718884, by rfl⟩ : syracuseStep 7668101 = 1437769) (by norm_num)
theorem B4039109 : Blo 1794098 4039109 := bbase (se 4 (by rfl) ⟨378666, by rfl⟩ : syracuseStep 4039109 = 757333) (by norm_num)
theorem B2728421 : Blo 1794098 2728421 := bbase (se 4 (by rfl) ⟨255789, by rfl⟩ : syracuseStep 2728421 = 511579) (by norm_num)
theorem B2425349 : Blo 1794098 2425349 := bbase (se 4 (by rfl) ⟨227376, by rfl⟩ : syracuseStep 2425349 = 454753) (by norm_num)
theorem B9085445 : Blo 1794098 9085445 := bbase (se 4 (by rfl) ⟨851760, by rfl⟩ : syracuseStep 9085445 = 1703521) (by norm_num)
theorem B4039181 : Blo 1794098 4039181 := bbase (se 3 (by rfl) ⟨757346, by rfl⟩ : syracuseStep 4039181 = 1514693) (by norm_num)
theorem B3236365 : Blo 1794098 3236365 := bbase (se 3 (by rfl) ⟨606818, by rfl⟩ : syracuseStep 3236365 = 1213637) (by norm_num)
theorem B3637781 : Blo 1794098 3637781 := bbase (se 6 (by rfl) ⟨85260, by rfl⟩ : syracuseStep 3637781 = 170521) (by norm_num)
theorem B2728469 : Blo 1794098 2728469 := bbase (se 6 (by rfl) ⟨63948, by rfl⟩ : syracuseStep 2728469 = 127897) (by norm_num)
theorem B11502101 : Blo 1794098 11502101 := bbase (se 6 (by rfl) ⟨269580, by rfl⟩ : syracuseStep 11502101 = 539161) (by norm_num)
theorem B5112341 : Blo 1794098 5112341 := bbase (se 6 (by rfl) ⟨119820, by rfl⟩ : syracuseStep 5112341 = 239641) (by norm_num)
theorem B2556461 : Blo 1794098 2556461 := bbase (se 3 (by rfl) ⟨479336, by rfl⟩ : syracuseStep 2556461 = 958673) (by norm_num)
theorem B4039253 : Blo 1794098 4039253 := bbase (se 8 (by rfl) ⟨23667, by rfl⟩ : syracuseStep 4039253 = 47335) (by norm_num)
theorem B12943957 : Blo 1794098 12943957 := bbase (se 8 (by rfl) ⟨75843, by rfl⟩ : syracuseStep 12943957 = 151687) (by norm_num)
theorem B3834461 : Blo 1794098 3834461 := bbase (se 3 (by rfl) ⟨718961, by rfl⟩ : syracuseStep 3834461 = 1437923) (by norm_num)
theorem B3408493 : Blo 1794098 3408493 := bbase (se 3 (by rfl) ⟨639092, by rfl⟩ : syracuseStep 3408493 = 1278185) (by norm_num)
theorem B7668341 : Blo 1794098 7668341 := bbase (se 5 (by rfl) ⟨359453, by rfl⟩ : syracuseStep 7668341 = 718907) (by norm_num)
theorem B20439701 : Blo 1794098 20439701 := bbase (se 6 (by rfl) ⟨479055, by rfl⟩ : syracuseStep 20439701 = 958111) (by norm_num)
theorem B4039325 : Blo 1794098 4039325 := bbase (se 3 (by rfl) ⟨757373, by rfl⟩ : syracuseStep 4039325 = 1514747) (by norm_num)
theorem B5751461 : Blo 1794098 5751461 := bbase (se 4 (by rfl) ⟨539199, by rfl⟩ : syracuseStep 5751461 = 1078399) (by norm_num)
theorem B4039397 : Blo 1794098 4039397 := bbase (se 4 (by rfl) ⟨378693, by rfl⟩ : syracuseStep 4039397 = 757387) (by norm_num)
theorem B1819369 : Blo 1794098 1819369 := bbase (se 2 (by rfl) ⟨682263, by rfl⟩ : syracuseStep 1819369 = 1364527) (by norm_num)
theorem B2876141 : Blo 1794098 2876141 := bbase (se 3 (by rfl) ⟨539276, by rfl⟩ : syracuseStep 2876141 = 1078553) (by norm_num)
theorem B7275253 : Blo 1794098 7275253 := bbase (se 5 (by rfl) ⟨341027, by rfl⟩ : syracuseStep 7275253 = 682055) (by norm_num)
theorem B3408637 : Blo 1794098 3408637 := bbase (se 3 (by rfl) ⟨639119, by rfl⟩ : syracuseStep 3408637 = 1278239) (by norm_num)
theorem B1819409 : Blo 1794098 1819409 := bbase (se 2 (by rfl) ⟨682278, by rfl⟩ : syracuseStep 1819409 = 1364557) (by norm_num)
theorem B14754581 : Blo 1794098 14754581 := bbase (se 6 (by rfl) ⟨345810, by rfl⟩ : syracuseStep 14754581 = 691621) (by norm_num)
theorem B4039469 : Blo 1794098 4039469 := bbase (se 3 (by rfl) ⟨757400, by rfl⟩ : syracuseStep 4039469 = 1514801) (by norm_num)
theorem B4039541 : Blo 1794098 4039541 := bbase (se 5 (by rfl) ⟨189353, by rfl⟩ : syracuseStep 4039541 = 378707) (by norm_num)
theorem B3408797 : Blo 1794098 3408797 := bbase (se 3 (by rfl) ⟨639149, by rfl⟩ : syracuseStep 3408797 = 1278299) (by norm_num)
theorem B4039613 : Blo 1794098 4039613 := bbase (se 3 (by rfl) ⟨757427, by rfl⟩ : syracuseStep 4039613 = 1514855) (by norm_num)
theorem B2155477 : Blo 1794098 2155477 := bbase (se 7 (by rfl) ⟨25259, by rfl⟩ : syracuseStep 2155477 = 50519) (by norm_num)
theorem B6816757 : Blo 1794098 6816757 := bbase (se 5 (by rfl) ⟨319535, by rfl⟩ : syracuseStep 6816757 = 639071) (by norm_num)
theorem B4039685 : Blo 1794098 4039685 := bbase (se 4 (by rfl) ⟨378720, by rfl⟩ : syracuseStep 4039685 = 757441) (by norm_num)
theorem B2876429 : Blo 1794098 2876429 := bbase (se 3 (by rfl) ⟨539330, by rfl⟩ : syracuseStep 2876429 = 1078661) (by norm_num)
theorem B1917965 : Blo 1794098 1917965 := bbase (se 3 (by rfl) ⟨359618, by rfl⟩ : syracuseStep 1917965 = 719237) (by norm_num)
theorem B1819693 : Blo 1794098 1819693 := bbase (se 3 (by rfl) ⟨341192, by rfl⟩ : syracuseStep 1819693 = 682385) (by norm_num)
theorem B3408941 : Blo 1794098 3408941 := bbase (se 3 (by rfl) ⟨639176, by rfl⟩ : syracuseStep 3408941 = 1278353) (by norm_num)
theorem B4850741 : Blo 1794098 4850741 := bbase (se 5 (by rfl) ⟨227378, by rfl⟩ : syracuseStep 4850741 = 454757) (by norm_num)
theorem B2155577 : Blo 1794098 2155577 := bbase (se 2 (by rfl) ⟨808341, by rfl⟩ : syracuseStep 2155577 = 1616683) (by norm_num)
theorem B3884101 : Blo 1794098 3884101 := bbase (se 4 (by rfl) ⟨364134, by rfl⟩ : syracuseStep 3884101 = 728269) (by norm_num)
theorem B4039757 : Blo 1794098 4039757 := bbase (se 3 (by rfl) ⟨757454, by rfl⟩ : syracuseStep 4039757 = 1514909) (by norm_num)
theorem B3834965 : Blo 1794098 3834965 := bbase (se 8 (by rfl) ⟨22470, by rfl⟩ : syracuseStep 3834965 = 44941) (by norm_num)
theorem B2557013 : Blo 1794098 2557013 := bbase (se 8 (by rfl) ⟨14982, by rfl⟩ : syracuseStep 2557013 = 29965) (by norm_num)
theorem B3834973 : Blo 1794098 3834973 := bbase (se 3 (by rfl) ⟨719057, by rfl⟩ : syracuseStep 3834973 = 1438115) (by norm_num)
theorem B3638405 : Blo 1794098 3638405 := bbase (se 4 (by rfl) ⟨341100, by rfl⟩ : syracuseStep 3638405 = 682201) (by norm_num)
theorem B4039829 : Blo 1794098 4039829 := bbase (se 6 (by rfl) ⟨94683, by rfl⟩ : syracuseStep 4039829 = 189367) (by norm_num)
theorem B5457061 : Blo 1794098 5457061 := bbase (se 4 (by rfl) ⟨511599, by rfl⟩ : syracuseStep 5457061 = 1023199) (by norm_num)
theorem B3638477 : Blo 1794098 3638477 := bbase (se 3 (by rfl) ⟨682214, by rfl⟩ : syracuseStep 3638477 = 1364429) (by norm_num)
theorem B4039901 : Blo 1794098 4039901 := bbase (se 3 (by rfl) ⟨757481, by rfl⟩ : syracuseStep 4039901 = 1514963) (by norm_num)
theorem B2303213 : Blo 1794098 2303213 := bbase (se 3 (by rfl) ⟨431852, by rfl⟩ : syracuseStep 2303213 = 863705) (by norm_num)
theorem B6817061 : Blo 1794098 6817061 := bbase (se 4 (by rfl) ⟨639099, by rfl⟩ : syracuseStep 6817061 = 1278199) (by norm_num)
theorem B4039973 : Blo 1794098 4039973 := bbase (se 4 (by rfl) ⟨378747, by rfl⟩ : syracuseStep 4039973 = 757495) (by norm_num)
theorem B3409229 : Blo 1794098 3409229 := bbase (se 3 (by rfl) ⟨639230, by rfl⟩ : syracuseStep 3409229 = 1278461) (by norm_num)
theorem B4040045 : Blo 1794098 4040045 := bbase (se 3 (by rfl) ⟨757508, by rfl⟩ : syracuseStep 4040045 = 1515017) (by norm_num)
theorem B2876845 : Blo 1794098 2876845 := bbase (se 3 (by rfl) ⟨539408, by rfl⟩ : syracuseStep 2876845 = 1078817) (by norm_num)
theorem B4040117 : Blo 1794098 4040117 := bbase (se 5 (by rfl) ⟨189380, by rfl⟩ : syracuseStep 4040117 = 378761) (by norm_num)
theorem B2590141 : Blo 1794098 2590141 := bbase (se 3 (by rfl) ⟨485651, by rfl⟩ : syracuseStep 2590141 = 971303) (by norm_num)
theorem B2270693 : Blo 1794098 2270693 := bbase (se 4 (by rfl) ⟨212877, by rfl⟩ : syracuseStep 2270693 = 425755) (by norm_num)
theorem B6055397 : Blo 1794098 6055397 := bbase (se 4 (by rfl) ⟨567693, by rfl⟩ : syracuseStep 6055397 = 1135387) (by norm_num)
theorem B3409381 : Blo 1794098 3409381 := bbase (se 4 (by rfl) ⟨319629, by rfl⟩ : syracuseStep 3409381 = 639259) (by norm_num)
theorem B4040189 : Blo 1794098 4040189 := bbase (se 3 (by rfl) ⟨757535, by rfl⟩ : syracuseStep 4040189 = 1515071) (by norm_num)
theorem B2270749 : Blo 1794098 2270749 := bbase (se 3 (by rfl) ⟨425765, by rfl⟩ : syracuseStep 2270749 = 851531) (by norm_num)
theorem B4040261 : Blo 1794098 4040261 := bbase (se 4 (by rfl) ⟨378774, by rfl⟩ : syracuseStep 4040261 = 757549) (by norm_num)
theorem B2270845 : Blo 1794098 2270845 := bbase (se 3 (by rfl) ⟨425783, by rfl⟩ : syracuseStep 2270845 = 851567) (by norm_num)
theorem B4040333 : Blo 1794098 4040333 := bbase (se 3 (by rfl) ⟨757562, by rfl⟩ : syracuseStep 4040333 = 1515125) (by norm_num)
theorem B5113525 : Blo 1794098 5113525 := bbase (se 5 (by rfl) ⟨239696, by rfl⟩ : syracuseStep 5113525 = 479393) (by norm_num)
theorem B1943233 : Blo 1794098 1943233 := bbase (se 2 (by rfl) ⟨728712, by rfl⟩ : syracuseStep 1943233 = 1457425) (by norm_num)
theorem B4040405 : Blo 1794098 4040405 := bbase (se 7 (by rfl) ⟨47348, by rfl⟩ : syracuseStep 4040405 = 94697) (by norm_num)
theorem B9086741 : Blo 1794098 9086741 := bbase (se 6 (by rfl) ⟨212970, by rfl⟩ : syracuseStep 9086741 = 425941) (by norm_num)
theorem B3409685 : Blo 1794098 3409685 := bbase (se 6 (by rfl) ⟨79914, by rfl⟩ : syracuseStep 3409685 = 159829) (by norm_num)
theorem B4040477 : Blo 1794098 4040477 := bbase (se 3 (by rfl) ⟨757589, by rfl⟩ : syracuseStep 4040477 = 1515179) (by norm_num)
theorem B2271017 : Blo 1794098 2271017 := bbase (se 2 (by rfl) ⟨851631, by rfl⟩ : syracuseStep 2271017 = 1703263) (by norm_num)
theorem B2156365 : Blo 1794098 2156365 := bbase (se 3 (by rfl) ⟨404318, by rfl⟩ : syracuseStep 2156365 = 808637) (by norm_num)
theorem B5113685 : Blo 1794098 5113685 := bbase (se 9 (by rfl) ⟨14981, by rfl⟩ : syracuseStep 5113685 = 29963) (by norm_num)
theorem B2271073 : Blo 1794098 2271073 := bbase (se 2 (by rfl) ⟨851652, by rfl⟩ : syracuseStep 2271073 = 1703305) (by norm_num)
theorem B4310885 : Blo 1794098 4310885 := bbase (se 4 (by rfl) ⟨404145, by rfl⟩ : syracuseStep 4310885 = 808291) (by norm_num)
theorem B4040549 : Blo 1794098 4040549 := bbase (se 4 (by rfl) ⟨378801, by rfl⟩ : syracuseStep 4040549 = 757603) (by norm_num)
theorem B6055829 : Blo 1794098 6055829 := bbase (se 6 (by rfl) ⟨141933, by rfl⟩ : syracuseStep 6055829 = 283867) (by norm_num)
theorem B4040621 : Blo 1794098 4040621 := bbase (se 3 (by rfl) ⟨757616, by rfl⟩ : syracuseStep 4040621 = 1515233) (by norm_num)
theorem B2271169 : Blo 1794098 2271169 := bbase (se 2 (by rfl) ⟨851688, by rfl⟩ : syracuseStep 2271169 = 1703377) (by norm_num)
theorem B4040693 : Blo 1794098 4040693 := bbase (se 5 (by rfl) ⟨189407, by rfl⟩ : syracuseStep 4040693 = 378815) (by norm_num)
theorem B2426917 : Blo 1794098 2426917 := bbase (se 4 (by rfl) ⟨227523, by rfl⟩ : syracuseStep 2426917 = 455047) (by norm_num)
theorem B4040765 : Blo 1794098 4040765 := bbase (se 3 (by rfl) ⟨757643, by rfl⟩ : syracuseStep 4040765 = 1515287) (by norm_num)
theorem B5113925 : Blo 1794098 5113925 := bbase (se 4 (by rfl) ⟨479430, by rfl⟩ : syracuseStep 5113925 = 958861) (by norm_num)
theorem B2271341 : Blo 1794098 2271341 := bbase (se 3 (by rfl) ⟨425876, by rfl⟩ : syracuseStep 2271341 = 851753) (by norm_num)
theorem B4040837 : Blo 1794098 4040837 := bbase (se 4 (by rfl) ⟨378828, by rfl⟩ : syracuseStep 4040837 = 757657) (by norm_num)
theorem B2271397 : Blo 1794098 2271397 := bbase (se 4 (by rfl) ⟨212943, by rfl⟩ : syracuseStep 2271397 = 425887) (by norm_num)
theorem B4040909 : Blo 1794098 4040909 := bbase (se 3 (by rfl) ⟨757670, by rfl⟩ : syracuseStep 4040909 = 1515341) (by norm_num)
theorem B2271493 : Blo 1794098 2271493 := bbase (se 4 (by rfl) ⟨212952, by rfl⟩ : syracuseStep 2271493 = 425905) (by norm_num)
theorem B5114117 : Blo 1794098 5114117 := bbase (se 4 (by rfl) ⟨479448, by rfl⟩ : syracuseStep 5114117 = 958897) (by norm_num)
theorem B4040981 : Blo 1794098 4040981 := bbase (se 6 (by rfl) ⟨94710, by rfl⟩ : syracuseStep 4040981 = 189421) (by norm_num)
theorem B6056261 : Blo 1794098 6056261 := bbase (se 4 (by rfl) ⟨567774, by rfl⟩ : syracuseStep 6056261 = 1135549) (by norm_num)
theorem B4041053 : Blo 1794098 4041053 := bbase (se 3 (by rfl) ⟨757697, by rfl⟩ : syracuseStep 4041053 = 1515395) (by norm_num)
theorem B2460061 : Blo 1794098 2460061 := bbase (se 3 (by rfl) ⟨461261, by rfl⟩ : syracuseStep 2460061 = 922523) (by norm_num)
theorem B4041125 : Blo 1794098 4041125 := bbase (se 4 (by rfl) ⟨378855, by rfl⟩ : syracuseStep 4041125 = 757711) (by norm_num)
theorem B2271665 : Blo 1794098 2271665 := bbase (se 2 (by rfl) ⟨851874, by rfl⟩ : syracuseStep 2271665 = 1703749) (by norm_num)
theorem B2271721 : Blo 1794098 2271721 := bbase (se 2 (by rfl) ⟨851895, by rfl⟩ : syracuseStep 2271721 = 1703791) (by norm_num)
theorem B4041197 : Blo 1794098 4041197 := bbase (se 3 (by rfl) ⟨757724, by rfl⟩ : syracuseStep 4041197 = 1515449) (by norm_num)
theorem B3885565 : Blo 1794098 3885565 := bbase (se 3 (by rfl) ⟨728543, by rfl⟩ : syracuseStep 3885565 = 1457087) (by norm_num)
theorem B2157077 : Blo 1794098 2157077 := bbase (se 6 (by rfl) ⟨50556, by rfl⟩ : syracuseStep 2157077 = 101113) (by norm_num)
theorem B2271817 : Blo 1794098 2271817 := bbase (se 2 (by rfl) ⟨851931, by rfl⟩ : syracuseStep 2271817 = 1703863) (by norm_num)
theorem B6056693 : Blo 1794098 6056693 := bbase (se 5 (by rfl) ⟨283907, by rfl⟩ : syracuseStep 6056693 = 567815) (by norm_num)
theorem B2271989 : Blo 1794098 2271989 := bbase (se 5 (by rfl) ⟨106499, by rfl⟩ : syracuseStep 2271989 = 212999) (by norm_num)
theorem B2460413 : Blo 1794098 2460413 := bbase (se 3 (by rfl) ⟨461327, by rfl⟩ : syracuseStep 2460413 = 922655) (by norm_num)
theorem B4606757 : Blo 1794098 4606757 := bbase (se 4 (by rfl) ⟨431883, by rfl⟩ : syracuseStep 4606757 = 863767) (by norm_num)
theorem B2272045 : Blo 1794098 2272045 := bbase (se 3 (by rfl) ⟨426008, by rfl⟩ : syracuseStep 2272045 = 852017) (by norm_num)
theorem B3640133 : Blo 1794098 3640133 := bbase (se 4 (by rfl) ⟨341262, by rfl⟩ : syracuseStep 3640133 = 682525) (by norm_num)
theorem B30657365 : Blo 1794098 30657365 := bbase (se 9 (by rfl) ⟨89816, by rfl⟩ : syracuseStep 30657365 = 179633) (by norm_num)
theorem B7670629 : Blo 1794098 7670629 := bbase (se 4 (by rfl) ⟨719121, by rfl⟩ : syracuseStep 7670629 = 1438243) (by norm_num)
theorem B2157413 : Blo 1794098 2157413 := bbase (se 4 (by rfl) ⟨202257, by rfl⟩ : syracuseStep 2157413 = 404515) (by norm_num)
theorem B5753717 : Blo 1794098 5753717 := bbase (se 5 (by rfl) ⟨269705, by rfl⟩ : syracuseStep 5753717 = 539411) (by norm_num)
theorem B2272141 : Blo 1794098 2272141 := bbase (se 3 (by rfl) ⟨426026, by rfl⟩ : syracuseStep 2272141 = 852053) (by norm_num)
theorem B2157529 : Blo 1794098 2157529 := bbase (se 2 (by rfl) ⟨809073, by rfl⟩ : syracuseStep 2157529 = 1618147) (by norm_num)
theorem B2157553 : Blo 1794098 2157553 := bbase (se 2 (by rfl) ⟨809082, by rfl⟩ : syracuseStep 2157553 = 1618165) (by norm_num)
theorem B2993141 : Blo 1794098 2993141 := bbase (se 5 (by rfl) ⟨140303, by rfl⟩ : syracuseStep 2993141 = 280607) (by norm_num)
theorem B9088037 : Blo 1794098 9088037 := bbase (se 4 (by rfl) ⟨852003, by rfl⟩ : syracuseStep 9088037 = 1704007) (by norm_num)
theorem B2272313 : Blo 1794098 2272313 := bbase (se 2 (by rfl) ⟨852117, by rfl⟩ : syracuseStep 2272313 = 1704235) (by norm_num)
theorem B2018389 : Blo 1794098 2018389 := bbase (se 8 (by rfl) ⟨11826, by rfl⟩ : syracuseStep 2018389 = 23653) (by norm_num)
theorem B2272369 : Blo 1794098 2272369 := bbase (se 2 (by rfl) ⟨852138, by rfl⟩ : syracuseStep 2272369 = 1704277) (by norm_num)
theorem B2018425 : Blo 1794098 2018425 := bbase (se 2 (by rfl) ⟨756909, by rfl⟩ : syracuseStep 2018425 = 1513819) (by norm_num)
theorem B2018461 : Blo 1794098 2018461 := bbase (se 3 (by rfl) ⟨378461, by rfl⟩ : syracuseStep 2018461 = 756923) (by norm_num)
theorem B6057125 : Blo 1794098 6057125 := bbase (se 4 (by rfl) ⟨567855, by rfl⟩ : syracuseStep 6057125 = 1135711) (by norm_num)
theorem B4541629 : Blo 1794098 4541629 := bbase (se 3 (by rfl) ⟨851555, by rfl⟩ : syracuseStep 4541629 = 1703111) (by norm_num)
theorem B2018497 : Blo 1794098 2018497 := bbase (se 2 (by rfl) ⟨756936, by rfl⟩ : syracuseStep 2018497 = 1513873) (by norm_num)
theorem B2272465 : Blo 1794098 2272465 := bbase (se 2 (by rfl) ⟨852174, by rfl⟩ : syracuseStep 2272465 = 1704349) (by norm_num)
theorem B2018533 : Blo 1794098 2018533 := bbase (se 4 (by rfl) ⟨189237, by rfl⟩ : syracuseStep 2018533 = 378475) (by norm_num)
theorem B2018569 : Blo 1794098 2018569 := bbase (se 2 (by rfl) ⟨756963, by rfl⟩ : syracuseStep 2018569 = 1513927) (by norm_num)
theorem B4541741 : Blo 1794098 4541741 := bbase (se 3 (by rfl) ⟨851576, by rfl⟩ : syracuseStep 4541741 = 1703153) (by norm_num)
theorem B2018605 : Blo 1794098 2018605 := bbase (se 3 (by rfl) ⟨378488, by rfl⟩ : syracuseStep 2018605 = 756977) (by norm_num)
theorem B2018641 : Blo 1794098 2018641 := bbase (se 2 (by rfl) ⟨756990, by rfl⟩ : syracuseStep 2018641 = 1513981) (by norm_num)
theorem B6819173 : Blo 1794098 6819173 := bbase (se 4 (by rfl) ⟨639297, by rfl⟩ : syracuseStep 6819173 = 1278595) (by norm_num)
theorem B2018677 : Blo 1794098 2018677 := bbase (se 5 (by rfl) ⟨94625, by rfl⟩ : syracuseStep 2018677 = 189251) (by norm_num)
theorem B2272637 : Blo 1794098 2272637 := bbase (se 3 (by rfl) ⟨426119, by rfl⟩ : syracuseStep 2272637 = 852239) (by norm_num)
theorem B2018713 : Blo 1794098 2018713 := bbase (se 2 (by rfl) ⟨757017, by rfl⟩ : syracuseStep 2018713 = 1514035) (by norm_num)
theorem B2272693 : Blo 1794098 2272693 := bbase (se 5 (by rfl) ⟨106532, by rfl⟩ : syracuseStep 2272693 = 213065) (by norm_num)
theorem B2018749 : Blo 1794098 2018749 := bbase (se 3 (by rfl) ⟨378515, by rfl⟩ : syracuseStep 2018749 = 757031) (by norm_num)
theorem B2076121 : Blo 1794098 2076121 := bbase (se 2 (by rfl) ⟨778545, by rfl⟩ : syracuseStep 2076121 = 1557091) (by norm_num)
theorem B2018785 : Blo 1794098 2018785 := bbase (se 2 (by rfl) ⟨757044, by rfl⟩ : syracuseStep 2018785 = 1514089) (by norm_num)
theorem B4541933 : Blo 1794098 4541933 := bbase (se 3 (by rfl) ⟨851612, by rfl⟩ : syracuseStep 4541933 = 1703225) (by norm_num)
theorem B2018821 : Blo 1794098 2018821 := bbase (se 4 (by rfl) ⟨189264, by rfl⟩ : syracuseStep 2018821 = 378529) (by norm_num)
theorem B29101589 : Blo 1794098 29101589 := bbase (se 6 (by rfl) ⟨682068, by rfl⟩ : syracuseStep 29101589 = 1364137) (by norm_num)
theorem B4312597 : Blo 1794098 4312597 := bbase (se 6 (by rfl) ⟨101076, by rfl⟩ : syracuseStep 4312597 = 202153) (by norm_num)
theorem B2272789 : Blo 1794098 2272789 := bbase (se 6 (by rfl) ⟨53268, by rfl⟩ : syracuseStep 2272789 = 106537) (by norm_num)
theorem B2018857 : Blo 1794098 2018857 := bbase (se 2 (by rfl) ⟨757071, by rfl⟩ : syracuseStep 2018857 = 1514143) (by norm_num)
theorem B2018893 : Blo 1794098 2018893 := bbase (se 3 (by rfl) ⟨378542, by rfl⟩ : syracuseStep 2018893 = 757085) (by norm_num)
theorem B6057557 : Blo 1794098 6057557 := bbase (se 8 (by rfl) ⟨35493, by rfl⟩ : syracuseStep 6057557 = 70987) (by norm_num)
theorem B110587477 : Blo 1794098 110587477 := bbase (se 8 (by rfl) ⟨647973, by rfl⟩ : syracuseStep 110587477 = 1295947) (by norm_num)
theorem B2018929 : Blo 1794098 2018929 := bbase (se 2 (by rfl) ⟨757098, by rfl⟩ : syracuseStep 2018929 = 1514197) (by norm_num)
theorem B6819461 : Blo 1794098 6819461 := bbase (se 4 (by rfl) ⟨639324, by rfl⟩ : syracuseStep 6819461 = 1278649) (by norm_num)
theorem B2018965 : Blo 1794098 2018965 := bbase (se 6 (by rfl) ⟨47319, by rfl⟩ : syracuseStep 2018965 = 94639) (by norm_num)
theorem B2019001 : Blo 1794098 2019001 := bbase (se 2 (by rfl) ⟨757125, by rfl⟩ : syracuseStep 2019001 = 1514251) (by norm_num)
theorem B2272961 : Blo 1794098 2272961 := bbase (se 2 (by rfl) ⟨852360, by rfl⟩ : syracuseStep 2272961 = 1704721) (by norm_num)
theorem B25882325 : Blo 1794098 25882325 := bbase (se 7 (by rfl) ⟨303308, by rfl⟩ : syracuseStep 25882325 = 606617) (by norm_num)
theorem B17256149 : Blo 1794098 17256149 := bbase (se 7 (by rfl) ⟨202220, by rfl⟩ : syracuseStep 17256149 = 404441) (by norm_num)
theorem B2019037 : Blo 1794098 2019037 := bbase (se 3 (by rfl) ⟨378569, by rfl⟩ : syracuseStep 2019037 = 757139) (by norm_num)
theorem B2273017 : Blo 1794098 2273017 := bbase (se 2 (by rfl) ⟨852381, by rfl⟩ : syracuseStep 2273017 = 1704763) (by norm_num)
theorem B2019073 : Blo 1794098 2019073 := bbase (se 2 (by rfl) ⟨757152, by rfl⟩ : syracuseStep 2019073 = 1514305) (by norm_num)
theorem B1969921 : Blo 1794098 1969921 := bbase (se 2 (by rfl) ⟨738720, by rfl⟩ : syracuseStep 1969921 = 1477441) (by norm_num)
theorem B2019109 : Blo 1794098 2019109 := bbase (se 4 (by rfl) ⟨189291, by rfl⟩ : syracuseStep 2019109 = 378583) (by norm_num)
theorem B4542277 : Blo 1794098 4542277 := bbase (se 4 (by rfl) ⟨425838, by rfl⟩ : syracuseStep 4542277 = 851677) (by norm_num)
theorem B2019145 : Blo 1794098 2019145 := bbase (se 2 (by rfl) ⟨757179, by rfl⟩ : syracuseStep 2019145 = 1514359) (by norm_num)
theorem B2273113 : Blo 1794098 2273113 := bbase (se 2 (by rfl) ⟨852417, by rfl⟩ : syracuseStep 2273113 = 1704835) (by norm_num)
theorem B2019181 : Blo 1794098 2019181 := bbase (se 3 (by rfl) ⟨378596, by rfl⟩ : syracuseStep 2019181 = 757193) (by norm_num)
theorem B2019217 : Blo 1794098 2019217 := bbase (se 2 (by rfl) ⟨757206, by rfl⟩ : syracuseStep 2019217 = 1514413) (by norm_num)
theorem B4542389 : Blo 1794098 4542389 := bbase (se 5 (by rfl) ⟨212924, by rfl⟩ : syracuseStep 4542389 = 425849) (by norm_num)
theorem B2019253 : Blo 1794098 2019253 := bbase (se 5 (by rfl) ⟨94652, by rfl⟩ : syracuseStep 2019253 = 189305) (by norm_num)
theorem B2019289 : Blo 1794098 2019289 := bbase (se 2 (by rfl) ⟨757233, by rfl⟩ : syracuseStep 2019289 = 1514467) (by norm_num)
theorem B2019325 : Blo 1794098 2019325 := bbase (se 3 (by rfl) ⟨378623, by rfl⟩ : syracuseStep 2019325 = 757247) (by norm_num)
theorem B6057989 : Blo 1794098 6057989 := bbase (se 4 (by rfl) ⟨567936, by rfl⟩ : syracuseStep 6057989 = 1135873) (by norm_num)
theorem B2019361 : Blo 1794098 2019361 := bbase (se 2 (by rfl) ⟨757260, by rfl⟩ : syracuseStep 2019361 = 1514521) (by norm_num)
theorem B2019397 : Blo 1794098 2019397 := bbase (se 4 (by rfl) ⟨189318, by rfl⟩ : syracuseStep 2019397 = 378637) (by norm_num)
theorem B2691149 : Blo 1794098 2691149 := bbase (se 3 (by rfl) ⟨504590, by rfl⟩ : syracuseStep 2691149 = 1009181) (by norm_num)
theorem B2691173 : Blo 1794098 2691173 := bbase (se 4 (by rfl) ⟨252297, by rfl⟩ : syracuseStep 2691173 = 504595) (by norm_num)
theorem B2019433 : Blo 1794098 2019433 := bbase (se 2 (by rfl) ⟨757287, by rfl⟩ : syracuseStep 2019433 = 1514575) (by norm_num)
theorem B4542581 : Blo 1794098 4542581 := bbase (se 5 (by rfl) ⟨212933, by rfl⟩ : syracuseStep 4542581 = 425867) (by norm_num)
theorem B13635701 : Blo 1794098 13635701 := bbase (se 5 (by rfl) ⟨639173, by rfl⟩ : syracuseStep 13635701 = 1278347) (by norm_num)
theorem B2691197 : Blo 1794098 2691197 := bbase (se 3 (by rfl) ⟨504599, by rfl⟩ : syracuseStep 2691197 = 1009199) (by norm_num)
theorem B4313213 : Blo 1794098 4313213 := bbase (se 3 (by rfl) ⟨808727, by rfl⟩ : syracuseStep 4313213 = 1617455) (by norm_num)
theorem B2019469 : Blo 1794098 2019469 := bbase (se 3 (by rfl) ⟨378650, by rfl⟩ : syracuseStep 2019469 = 757301) (by norm_num)
theorem B2691221 : Blo 1794098 2691221 := bbase (se 6 (by rfl) ⟨63075, by rfl⟩ : syracuseStep 2691221 = 126151) (by norm_num)
theorem B2691245 : Blo 1794098 2691245 := bbase (se 3 (by rfl) ⟨504608, by rfl⟩ : syracuseStep 2691245 = 1009217) (by norm_num)
theorem B2019505 : Blo 1794098 2019505 := bbase (se 2 (by rfl) ⟨757314, by rfl⟩ : syracuseStep 2019505 = 1514629) (by norm_num)
theorem B2527421 : Blo 1794098 2527421 := bbase (se 3 (by rfl) ⟨473891, by rfl⟩ : syracuseStep 2527421 = 947783) (by norm_num)
theorem B2691269 : Blo 1794098 2691269 := bbase (se 4 (by rfl) ⟨252306, by rfl⟩ : syracuseStep 2691269 = 504613) (by norm_num)
theorem B2019541 : Blo 1794098 2019541 := bbase (se 7 (by rfl) ⟨23666, by rfl⟩ : syracuseStep 2019541 = 47333) (by norm_num)
theorem B2691293 : Blo 1794098 2691293 := bbase (se 3 (by rfl) ⟨504617, by rfl⟩ : syracuseStep 2691293 = 1009235) (by norm_num)
theorem B2691317 : Blo 1794098 2691317 := bbase (se 5 (by rfl) ⟨126155, by rfl⟩ : syracuseStep 2691317 = 252311) (by norm_num)
theorem B2019577 : Blo 1794098 2019577 := bbase (se 2 (by rfl) ⟨757341, by rfl⟩ : syracuseStep 2019577 = 1514683) (by norm_num)
theorem B2691341 : Blo 1794098 2691341 := bbase (se 3 (by rfl) ⟨504626, by rfl⟩ : syracuseStep 2691341 = 1009253) (by norm_num)
theorem B2019613 : Blo 1794098 2019613 := bbase (se 3 (by rfl) ⟨378677, by rfl⟩ : syracuseStep 2019613 = 757355) (by norm_num)
theorem B2691365 : Blo 1794098 2691365 := bbase (se 4 (by rfl) ⟨252315, by rfl⟩ : syracuseStep 2691365 = 504631) (by norm_num)
theorem B9089333 : Blo 1794098 9089333 := bbase (se 5 (by rfl) ⟨426062, by rfl⟩ : syracuseStep 9089333 = 852125) (by norm_num)
theorem B2691389 : Blo 1794098 2691389 := bbase (se 3 (by rfl) ⟨504635, by rfl⟩ : syracuseStep 2691389 = 1009271) (by norm_num)
theorem B2019649 : Blo 1794098 2019649 := bbase (se 2 (by rfl) ⟨757368, by rfl⟩ : syracuseStep 2019649 = 1514737) (by norm_num)
theorem B2691413 : Blo 1794098 2691413 := bbase (se 10 (by rfl) ⟨3942, by rfl⟩ : syracuseStep 2691413 = 7885) (by norm_num)
theorem B2019685 : Blo 1794098 2019685 := bbase (se 4 (by rfl) ⟨189345, by rfl⟩ : syracuseStep 2019685 = 378691) (by norm_num)
theorem B2691437 : Blo 1794098 2691437 := bbase (se 3 (by rfl) ⟨504644, by rfl⟩ : syracuseStep 2691437 = 1009289) (by norm_num)
theorem B2691461 : Blo 1794098 2691461 := bbase (se 4 (by rfl) ⟨252324, by rfl⟩ : syracuseStep 2691461 = 504649) (by norm_num)
theorem B2019721 : Blo 1794098 2019721 := bbase (se 2 (by rfl) ⟨757395, by rfl⟩ : syracuseStep 2019721 = 1514791) (by norm_num)
theorem B2691485 : Blo 1794098 2691485 := bbase (se 3 (by rfl) ⟨504653, by rfl⟩ : syracuseStep 2691485 = 1009307) (by norm_num)
theorem B3453341 : Blo 1794098 3453341 := bbase (se 3 (by rfl) ⟨647501, by rfl⟩ : syracuseStep 3453341 = 1295003) (by norm_num)
theorem B2019757 : Blo 1794098 2019757 := bbase (se 3 (by rfl) ⟨378704, by rfl⟩ : syracuseStep 2019757 = 757409) (by norm_num)
theorem B2691509 : Blo 1794098 2691509 := bbase (se 5 (by rfl) ⟨126164, by rfl⟩ : syracuseStep 2691509 = 252329) (by norm_num)
theorem B6058421 : Blo 1794098 6058421 := bbase (se 5 (by rfl) ⟨283988, by rfl⟩ : syracuseStep 6058421 = 567977) (by norm_num)
theorem B2691533 : Blo 1794098 2691533 := bbase (se 3 (by rfl) ⟨504662, by rfl⟩ : syracuseStep 2691533 = 1009325) (by norm_num)
theorem B4542925 : Blo 1794098 4542925 := bbase (se 3 (by rfl) ⟨851798, by rfl⟩ : syracuseStep 4542925 = 1703597) (by norm_num)
theorem B2019793 : Blo 1794098 2019793 := bbase (se 2 (by rfl) ⟨757422, by rfl⟩ : syracuseStep 2019793 = 1514845) (by norm_num)
theorem B2691557 : Blo 1794098 2691557 := bbase (se 4 (by rfl) ⟨252333, by rfl⟩ : syracuseStep 2691557 = 504667) (by norm_num)
theorem B2019829 : Blo 1794098 2019829 := bbase (se 5 (by rfl) ⟨94679, by rfl⟩ : syracuseStep 2019829 = 189359) (by norm_num)
theorem B2691581 : Blo 1794098 2691581 := bbase (se 3 (by rfl) ⟨504671, by rfl⟩ : syracuseStep 2691581 = 1009343) (by norm_num)
theorem B2691605 : Blo 1794098 2691605 := bbase (se 6 (by rfl) ⟨63084, by rfl⟩ : syracuseStep 2691605 = 126169) (by norm_num)
theorem B13627925 : Blo 1794098 13627925 := bbase (se 6 (by rfl) ⟨319404, by rfl⟩ : syracuseStep 13627925 = 638809) (by norm_num)
theorem B2019865 : Blo 1794098 2019865 := bbase (se 2 (by rfl) ⟨757449, by rfl⟩ : syracuseStep 2019865 = 1514899) (by norm_num)
theorem B2691629 : Blo 1794098 2691629 := bbase (se 3 (by rfl) ⟨504680, by rfl⟩ : syracuseStep 2691629 = 1009361) (by norm_num)
theorem B4313645 : Blo 1794098 4313645 := bbase (se 3 (by rfl) ⟨808808, by rfl⟩ : syracuseStep 4313645 = 1617617) (by norm_num)
theorem B4543037 : Blo 1794098 4543037 := bbase (se 3 (by rfl) ⟨851819, by rfl⟩ : syracuseStep 4543037 = 1703639) (by norm_num)
theorem B2019901 : Blo 1794098 2019901 := bbase (se 3 (by rfl) ⟨378731, by rfl⟩ : syracuseStep 2019901 = 757463) (by norm_num)
theorem B2691653 : Blo 1794098 2691653 := bbase (se 4 (by rfl) ⟨252342, by rfl⟩ : syracuseStep 2691653 = 504685) (by norm_num)
theorem B2691677 : Blo 1794098 2691677 := bbase (se 3 (by rfl) ⟨504689, by rfl⟩ : syracuseStep 2691677 = 1009379) (by norm_num)
theorem B2019937 : Blo 1794098 2019937 := bbase (se 2 (by rfl) ⟨757476, by rfl⟩ : syracuseStep 2019937 = 1514953) (by norm_num)
theorem B3027557 : Blo 1794098 3027557 := bbase (se 4 (by rfl) ⟨283833, by rfl⟩ : syracuseStep 3027557 = 567667) (by norm_num)
theorem B2691701 : Blo 1794098 2691701 := bbase (se 5 (by rfl) ⟨126173, by rfl⟩ : syracuseStep 2691701 = 252347) (by norm_num)
theorem B2019973 : Blo 1794098 2019973 := bbase (se 4 (by rfl) ⟨189372, by rfl⟩ : syracuseStep 2019973 = 378745) (by norm_num)
theorem B2691725 : Blo 1794098 2691725 := bbase (se 3 (by rfl) ⟨504698, by rfl⟩ : syracuseStep 2691725 = 1009397) (by norm_num)
theorem B2691749 : Blo 1794098 2691749 := bbase (se 4 (by rfl) ⟨252351, by rfl⟩ : syracuseStep 2691749 = 504703) (by norm_num)
theorem B2020009 : Blo 1794098 2020009 := bbase (se 2 (by rfl) ⟨757503, by rfl⟩ : syracuseStep 2020009 = 1515007) (by norm_num)
theorem B2691773 : Blo 1794098 2691773 := bbase (se 3 (by rfl) ⟨504707, by rfl⟩ : syracuseStep 2691773 = 1009415) (by norm_num)
theorem B4149949 : Blo 1794098 4149949 := bbase (se 3 (by rfl) ⟨778115, by rfl⟩ : syracuseStep 4149949 = 1556231) (by norm_num)
theorem B8630981 : Blo 1794098 8630981 := bbase (se 4 (by rfl) ⟨809154, by rfl⟩ : syracuseStep 8630981 = 1618309) (by norm_num)
theorem B2020045 : Blo 1794098 2020045 := bbase (se 3 (by rfl) ⟨378758, by rfl⟩ : syracuseStep 2020045 = 757517) (by norm_num)
theorem B2691797 : Blo 1794098 2691797 := bbase (se 7 (by rfl) ⟨31544, by rfl⟩ : syracuseStep 2691797 = 63089) (by norm_num)
theorem B3027685 : Blo 1794098 3027685 := bbase (se 4 (by rfl) ⟨283845, by rfl⟩ : syracuseStep 3027685 = 567691) (by norm_num)
theorem B2691821 : Blo 1794098 2691821 := bbase (se 3 (by rfl) ⟨504716, by rfl⟩ : syracuseStep 2691821 = 1009433) (by norm_num)
theorem B2020081 : Blo 1794098 2020081 := bbase (se 2 (by rfl) ⟨757530, by rfl⟩ : syracuseStep 2020081 = 1515061) (by norm_num)
theorem B4543229 : Blo 1794098 4543229 := bbase (se 3 (by rfl) ⟨851855, by rfl⟩ : syracuseStep 4543229 = 1703711) (by norm_num)
theorem B2691845 : Blo 1794098 2691845 := bbase (se 4 (by rfl) ⟨252360, by rfl⟩ : syracuseStep 2691845 = 504721) (by norm_num)
theorem B2020117 : Blo 1794098 2020117 := bbase (se 6 (by rfl) ⟨47346, by rfl⟩ : syracuseStep 2020117 = 94693) (by norm_num)
theorem B2691869 : Blo 1794098 2691869 := bbase (se 3 (by rfl) ⟨504725, by rfl⟩ : syracuseStep 2691869 = 1009451) (by norm_num)
theorem B2691893 : Blo 1794098 2691893 := bbase (se 5 (by rfl) ⟨126182, by rfl⟩ : syracuseStep 2691893 = 252365) (by norm_num)
theorem B2020153 : Blo 1794098 2020153 := bbase (se 2 (by rfl) ⟨757557, by rfl⟩ : syracuseStep 2020153 = 1515115) (by norm_num)
theorem B3027773 : Blo 1794098 3027773 := bbase (se 3 (by rfl) ⟨567707, by rfl⟩ : syracuseStep 3027773 = 1135415) (by norm_num)
theorem B2691917 : Blo 1794098 2691917 := bbase (se 3 (by rfl) ⟨504734, by rfl⟩ : syracuseStep 2691917 = 1009469) (by norm_num)
theorem B2020189 : Blo 1794098 2020189 := bbase (se 3 (by rfl) ⟨378785, by rfl⟩ : syracuseStep 2020189 = 757571) (by norm_num)
theorem B2691941 : Blo 1794098 2691941 := bbase (se 4 (by rfl) ⟨252369, by rfl⟩ : syracuseStep 2691941 = 504739) (by norm_num)
theorem B6058853 : Blo 1794098 6058853 := bbase (se 4 (by rfl) ⟨568017, by rfl⟩ : syracuseStep 6058853 = 1136035) (by norm_num)
theorem B2691965 : Blo 1794098 2691965 := bbase (se 3 (by rfl) ⟨504743, by rfl⟩ : syracuseStep 2691965 = 1009487) (by norm_num)
theorem B2020225 : Blo 1794098 2020225 := bbase (se 2 (by rfl) ⟨757584, by rfl⟩ : syracuseStep 2020225 = 1515169) (by norm_num)
theorem B2691989 : Blo 1794098 2691989 := bbase (se 6 (by rfl) ⟨63093, by rfl⟩ : syracuseStep 2691989 = 126187) (by norm_num)
theorem B2020261 : Blo 1794098 2020261 := bbase (se 4 (by rfl) ⟨189399, by rfl⟩ : syracuseStep 2020261 = 378799) (by norm_num)
theorem B2692013 : Blo 1794098 2692013 := bbase (se 3 (by rfl) ⟨504752, by rfl⟩ : syracuseStep 2692013 = 1009505) (by norm_num)
theorem B3027901 : Blo 1794098 3027901 := bbase (se 3 (by rfl) ⟨567731, by rfl⟩ : syracuseStep 3027901 = 1135463) (by norm_num)
theorem B2692037 : Blo 1794098 2692037 := bbase (se 4 (by rfl) ⟨252378, by rfl⟩ : syracuseStep 2692037 = 504757) (by norm_num)
theorem B2020297 : Blo 1794098 2020297 := bbase (se 2 (by rfl) ⟨757611, by rfl⟩ : syracuseStep 2020297 = 1515223) (by norm_num)
theorem B5747669 : Blo 1794098 5747669 := bbase (se 7 (by rfl) ⟨67355, by rfl⟩ : syracuseStep 5747669 = 134711) (by norm_num)
theorem B2692061 : Blo 1794098 2692061 := bbase (se 3 (by rfl) ⟨504761, by rfl⟩ : syracuseStep 2692061 = 1009523) (by norm_num)
theorem B2020333 : Blo 1794098 2020333 := bbase (se 3 (by rfl) ⟨378812, by rfl⟩ : syracuseStep 2020333 = 757625) (by norm_num)
theorem B2692085 : Blo 1794098 2692085 := bbase (se 5 (by rfl) ⟨126191, by rfl⟩ : syracuseStep 2692085 = 252383) (by norm_num)
theorem B2692109 : Blo 1794098 2692109 := bbase (se 3 (by rfl) ⟨504770, by rfl⟩ : syracuseStep 2692109 = 1009541) (by norm_num)
theorem B2020369 : Blo 1794098 2020369 := bbase (se 2 (by rfl) ⟨757638, by rfl⟩ : syracuseStep 2020369 = 1515277) (by norm_num)
theorem B3027989 : Blo 1794098 3027989 := bbase (se 6 (by rfl) ⟨70968, by rfl⟩ : syracuseStep 3027989 = 141937) (by norm_num)
theorem B2692133 : Blo 1794098 2692133 := bbase (se 4 (by rfl) ⟨252387, by rfl⟩ : syracuseStep 2692133 = 504775) (by norm_num)
theorem B2020405 : Blo 1794098 2020405 := bbase (se 5 (by rfl) ⟨94706, by rfl⟩ : syracuseStep 2020405 = 189413) (by norm_num)
theorem B2692157 : Blo 1794098 2692157 := bbase (se 3 (by rfl) ⟨504779, by rfl⟩ : syracuseStep 2692157 = 1009559) (by norm_num)
theorem B2692181 : Blo 1794098 2692181 := bbase (se 8 (by rfl) ⟨15774, by rfl⟩ : syracuseStep 2692181 = 31549) (by norm_num)
theorem B4543573 : Blo 1794098 4543573 := bbase (se 8 (by rfl) ⟨26622, by rfl⟩ : syracuseStep 4543573 = 53245) (by norm_num)
theorem B2020441 : Blo 1794098 2020441 := bbase (se 2 (by rfl) ⟨757665, by rfl⟩ : syracuseStep 2020441 = 1515331) (by norm_num)
theorem B2692205 : Blo 1794098 2692205 := bbase (se 3 (by rfl) ⟨504788, by rfl⟩ : syracuseStep 2692205 = 1009577) (by norm_num)
theorem B2020477 : Blo 1794098 2020477 := bbase (se 3 (by rfl) ⟨378839, by rfl⟩ : syracuseStep 2020477 = 757679) (by norm_num)
theorem B2692229 : Blo 1794098 2692229 := bbase (se 4 (by rfl) ⟨252396, by rfl⟩ : syracuseStep 2692229 = 504793) (by norm_num)
theorem B3028117 : Blo 1794098 3028117 := bbase (se 6 (by rfl) ⟨70971, by rfl⟩ : syracuseStep 3028117 = 141943) (by norm_num)
theorem B2692253 : Blo 1794098 2692253 := bbase (se 3 (by rfl) ⟨504797, by rfl⟩ : syracuseStep 2692253 = 1009595) (by norm_num)
theorem B2020513 : Blo 1794098 2020513 := bbase (se 2 (by rfl) ⟨757692, by rfl⟩ : syracuseStep 2020513 = 1515385) (by norm_num)
theorem B2692277 : Blo 1794098 2692277 := bbase (se 5 (by rfl) ⟨126200, by rfl⟩ : syracuseStep 2692277 = 252401) (by norm_num)
theorem B6812869 : Blo 1794098 6812869 := bbase (se 4 (by rfl) ⟨638706, by rfl⟩ : syracuseStep 6812869 = 1277413) (by norm_num)
theorem B4543685 : Blo 1794098 4543685 := bbase (se 4 (by rfl) ⟨425970, by rfl⟩ : syracuseStep 4543685 = 851941) (by norm_num)
theorem B2020549 : Blo 1794098 2020549 := bbase (se 4 (by rfl) ⟨189426, by rfl⟩ : syracuseStep 2020549 = 378853) (by norm_num)
theorem B2692301 : Blo 1794098 2692301 := bbase (se 3 (by rfl) ⟨504806, by rfl⟩ : syracuseStep 2692301 = 1009613) (by norm_num)
theorem B4093141 : Blo 1794098 4093141 := bbase (se 7 (by rfl) ⟨47966, by rfl⟩ : syracuseStep 4093141 = 95933) (by norm_num)
theorem B2692325 : Blo 1794098 2692325 := bbase (se 4 (by rfl) ⟨252405, by rfl⟩ : syracuseStep 2692325 = 504811) (by norm_num)
theorem B2020585 : Blo 1794098 2020585 := bbase (se 2 (by rfl) ⟨757719, by rfl⟩ : syracuseStep 2020585 = 1515439) (by norm_num)
theorem B3028205 : Blo 1794098 3028205 := bbase (se 3 (by rfl) ⟨567788, by rfl⟩ : syracuseStep 3028205 = 1135577) (by norm_num)
theorem B2692349 : Blo 1794098 2692349 := bbase (se 3 (by rfl) ⟨504815, by rfl⟩ : syracuseStep 2692349 = 1009631) (by norm_num)
theorem B2692373 : Blo 1794098 2692373 := bbase (se 6 (by rfl) ⟨63102, by rfl⟩ : syracuseStep 2692373 = 126205) (by norm_num)
theorem B6059285 : Blo 1794098 6059285 := bbase (se 6 (by rfl) ⟨142014, by rfl⟩ : syracuseStep 6059285 = 284029) (by norm_num)
theorem B2692397 : Blo 1794098 2692397 := bbase (se 3 (by rfl) ⟨504824, by rfl⟩ : syracuseStep 2692397 = 1009649) (by norm_num)
theorem B2692421 : Blo 1794098 2692421 := bbase (se 4 (by rfl) ⟨252414, by rfl⟩ : syracuseStep 2692421 = 504829) (by norm_num)
theorem B2692445 : Blo 1794098 2692445 := bbase (se 3 (by rfl) ⟨504833, by rfl⟩ : syracuseStep 2692445 = 1009667) (by norm_num)
theorem B3028333 : Blo 1794098 3028333 := bbase (se 3 (by rfl) ⟨567812, by rfl⟩ : syracuseStep 3028333 = 1135625) (by norm_num)
theorem B8295797 : Blo 1794098 8295797 := bbase (se 5 (by rfl) ⟨388865, by rfl⟩ : syracuseStep 8295797 = 777731) (by norm_num)
theorem B2692469 : Blo 1794098 2692469 := bbase (se 5 (by rfl) ⟨126209, by rfl⟩ : syracuseStep 2692469 = 252419) (by norm_num)
theorem B4543877 : Blo 1794098 4543877 := bbase (se 4 (by rfl) ⟨425988, by rfl⟩ : syracuseStep 4543877 = 851977) (by norm_num)
theorem B2692493 : Blo 1794098 2692493 := bbase (se 3 (by rfl) ⟨504842, by rfl⟩ : syracuseStep 2692493 = 1009685) (by norm_num)
theorem B2692517 : Blo 1794098 2692517 := bbase (se 4 (by rfl) ⟨252423, by rfl⟩ : syracuseStep 2692517 = 504847) (by norm_num)
theorem B2692541 : Blo 1794098 2692541 := bbase (se 3 (by rfl) ⟨504851, by rfl⟩ : syracuseStep 2692541 = 1009703) (by norm_num)
theorem B3028421 : Blo 1794098 3028421 := bbase (se 4 (by rfl) ⟨283914, by rfl⟩ : syracuseStep 3028421 = 567829) (by norm_num)
theorem B4093397 : Blo 1794098 4093397 := bbase (se 7 (by rfl) ⟨47969, by rfl⟩ : syracuseStep 4093397 = 95939) (by norm_num)
theorem B2692565 : Blo 1794098 2692565 := bbase (se 7 (by rfl) ⟨31553, by rfl⟩ : syracuseStep 2692565 = 63107) (by norm_num)
theorem B2692589 : Blo 1794098 2692589 := bbase (se 3 (by rfl) ⟨504860, by rfl⟩ : syracuseStep 2692589 = 1009721) (by norm_num)
theorem B6813173 : Blo 1794098 6813173 := bbase (se 5 (by rfl) ⟨319367, by rfl⟩ : syracuseStep 6813173 = 638735) (by norm_num)
theorem B10229237 : Blo 1794098 10229237 := bbase (se 5 (by rfl) ⟨479495, by rfl⟩ : syracuseStep 10229237 = 958991) (by norm_num)
theorem B2692613 : Blo 1794098 2692613 := bbase (se 4 (by rfl) ⟨252432, by rfl⟩ : syracuseStep 2692613 = 504865) (by norm_num)
theorem B2692637 : Blo 1794098 2692637 := bbase (se 3 (by rfl) ⟨504869, by rfl⟩ : syracuseStep 2692637 = 1009739) (by norm_num)
theorem B2692661 : Blo 1794098 2692661 := bbase (se 5 (by rfl) ⟨126218, by rfl⟩ : syracuseStep 2692661 = 252437) (by norm_num)
theorem B3028549 : Blo 1794098 3028549 := bbase (se 4 (by rfl) ⟨283926, by rfl⟩ : syracuseStep 3028549 = 567853) (by norm_num)
theorem B9090629 : Blo 1794098 9090629 := bbase (se 4 (by rfl) ⟨852246, by rfl⟩ : syracuseStep 9090629 = 1704493) (by norm_num)
theorem B2692685 : Blo 1794098 2692685 := bbase (se 3 (by rfl) ⟨504878, by rfl⟩ : syracuseStep 2692685 = 1009757) (by norm_num)
theorem B2692709 : Blo 1794098 2692709 := bbase (se 4 (by rfl) ⟨252441, by rfl⟩ : syracuseStep 2692709 = 504883) (by norm_num)
theorem B10221173 : Blo 1794098 10221173 := bbase (se 5 (by rfl) ⟨479117, by rfl⟩ : syracuseStep 10221173 = 958235) (by norm_num)
theorem B2692733 : Blo 1794098 2692733 := bbase (se 3 (by rfl) ⟨504887, by rfl⟩ : syracuseStep 2692733 = 1009775) (by norm_num)
theorem B2692757 : Blo 1794098 2692757 := bbase (se 6 (by rfl) ⟨63111, by rfl⟩ : syracuseStep 2692757 = 126223) (by norm_num)
theorem B3028637 : Blo 1794098 3028637 := bbase (se 3 (by rfl) ⟨567869, by rfl⟩ : syracuseStep 3028637 = 1135739) (by norm_num)
theorem B2692781 : Blo 1794098 2692781 := bbase (se 3 (by rfl) ⟨504896, by rfl⟩ : syracuseStep 2692781 = 1009793) (by norm_num)
theorem B2692805 : Blo 1794098 2692805 := bbase (se 4 (by rfl) ⟨252450, by rfl⟩ : syracuseStep 2692805 = 504901) (by norm_num)
theorem B6059717 : Blo 1794098 6059717 := bbase (se 4 (by rfl) ⟨568098, by rfl⟩ : syracuseStep 6059717 = 1136197) (by norm_num)
theorem B2692829 : Blo 1794098 2692829 := bbase (se 3 (by rfl) ⟨504905, by rfl⟩ : syracuseStep 2692829 = 1009811) (by norm_num)
theorem B4544221 : Blo 1794098 4544221 := bbase (se 3 (by rfl) ⟨852041, by rfl⟩ : syracuseStep 4544221 = 1704083) (by norm_num)
theorem B4314845 : Blo 1794098 4314845 := bbase (se 3 (by rfl) ⟨809033, by rfl⟩ : syracuseStep 4314845 = 1618067) (by norm_num)
theorem B5109493 : Blo 1794098 5109493 := bbase (se 5 (by rfl) ⟨239507, by rfl⟩ : syracuseStep 5109493 = 479015) (by norm_num)
theorem B3233525 : Blo 1794098 3233525 := bbase (se 5 (by rfl) ⟨151571, by rfl⟩ : syracuseStep 3233525 = 303143) (by norm_num)
theorem B2692853 : Blo 1794098 2692853 := bbase (se 5 (by rfl) ⟨126227, by rfl⟩ : syracuseStep 2692853 = 252455) (by norm_num)
theorem B2692877 : Blo 1794098 2692877 := bbase (se 3 (by rfl) ⟨504914, by rfl⟩ : syracuseStep 2692877 = 1009829) (by norm_num)
theorem B12932885 : Blo 1794098 12932885 := bbase (se 6 (by rfl) ⟨303114, by rfl⟩ : syracuseStep 12932885 = 606229) (by norm_num)
theorem B3028765 : Blo 1794098 3028765 := bbase (se 3 (by rfl) ⟨567893, by rfl⟩ : syracuseStep 3028765 = 1135787) (by norm_num)
theorem B2692901 : Blo 1794098 2692901 := bbase (se 4 (by rfl) ⟨252459, by rfl⟩ : syracuseStep 2692901 = 504919) (by norm_num)
theorem B3323701 : Blo 1794098 3323701 := bbase (se 5 (by rfl) ⟨155798, by rfl⟩ : syracuseStep 3323701 = 311597) (by norm_num)
theorem B2692925 : Blo 1794098 2692925 := bbase (se 3 (by rfl) ⟨504923, by rfl⟩ : syracuseStep 2692925 = 1009847) (by norm_num)
theorem B4544333 : Blo 1794098 4544333 := bbase (se 3 (by rfl) ⟨852062, by rfl⟩ : syracuseStep 4544333 = 1704125) (by norm_num)
theorem B2692949 : Blo 1794098 2692949 := bbase (se 9 (by rfl) ⟨7889, by rfl⟩ : syracuseStep 2692949 = 15779) (by norm_num)
theorem B2692973 : Blo 1794098 2692973 := bbase (se 3 (by rfl) ⟨504932, by rfl⟩ : syracuseStep 2692973 = 1009865) (by norm_num)
theorem B3028853 : Blo 1794098 3028853 := bbase (se 5 (by rfl) ⟨141977, by rfl⟩ : syracuseStep 3028853 = 283955) (by norm_num)
theorem B2692997 : Blo 1794098 2692997 := bbase (se 4 (by rfl) ⟨252468, by rfl⟩ : syracuseStep 2692997 = 504937) (by norm_num)
theorem B3233677 : Blo 1794098 3233677 := bbase (se 3 (by rfl) ⟨606314, by rfl⟩ : syracuseStep 3233677 = 1212629) (by norm_num)
theorem B2693021 : Blo 1794098 2693021 := bbase (se 3 (by rfl) ⟨504941, by rfl⟩ : syracuseStep 2693021 = 1009883) (by norm_num)
theorem B2693045 : Blo 1794098 2693045 := bbase (se 5 (by rfl) ⟨126236, by rfl⟩ : syracuseStep 2693045 = 252473) (by norm_num)
theorem B2693069 : Blo 1794098 2693069 := bbase (se 3 (by rfl) ⟨504950, by rfl⟩ : syracuseStep 2693069 = 1009901) (by norm_num)
theorem B9082853 : Blo 1794098 9082853 := bbase (se 4 (by rfl) ⟨851517, by rfl⟩ : syracuseStep 9082853 = 1703035) (by norm_num)
theorem B2693093 : Blo 1794098 2693093 := bbase (se 4 (by rfl) ⟨252477, by rfl⟩ : syracuseStep 2693093 = 504955) (by norm_num)
theorem B3028981 : Blo 1794098 3028981 := bbase (se 5 (by rfl) ⟨141983, by rfl⟩ : syracuseStep 3028981 = 283967) (by norm_num)
theorem B9975797 : Blo 1794098 9975797 := bbase (se 5 (by rfl) ⟨467615, by rfl⟩ : syracuseStep 9975797 = 935231) (by norm_num)
theorem B2693117 : Blo 1794098 2693117 := bbase (se 3 (by rfl) ⟨504959, by rfl⟩ : syracuseStep 2693117 = 1009919) (by norm_num)
theorem B4544525 : Blo 1794098 4544525 := bbase (se 3 (by rfl) ⟨852098, by rfl⟩ : syracuseStep 4544525 = 1704197) (by norm_num)
theorem B2693141 : Blo 1794098 2693141 := bbase (se 6 (by rfl) ⟨63120, by rfl⟩ : syracuseStep 2693141 = 126241) (by norm_num)
theorem B34519061 : Blo 1794098 34519061 := bbase (se 6 (by rfl) ⟨809040, by rfl⟩ : syracuseStep 34519061 = 1618081) (by norm_num)
theorem B3455021 : Blo 1794098 3455021 := bbase (se 3 (by rfl) ⟨647816, by rfl⟩ : syracuseStep 3455021 = 1295633) (by norm_num)
theorem B2693165 : Blo 1794098 2693165 := bbase (se 3 (by rfl) ⟨504968, by rfl⟩ : syracuseStep 2693165 = 1009937) (by norm_num)
theorem B2693189 : Blo 1794098 2693189 := bbase (se 4 (by rfl) ⟨252486, by rfl⟩ : syracuseStep 2693189 = 504973) (by norm_num)
theorem B3029069 : Blo 1794098 3029069 := bbase (se 3 (by rfl) ⟨567950, by rfl⟩ : syracuseStep 3029069 = 1135901) (by norm_num)
theorem B2693213 : Blo 1794098 2693213 := bbase (se 3 (by rfl) ⟨504977, by rfl⟩ : syracuseStep 2693213 = 1009955) (by norm_num)
theorem B2693237 : Blo 1794098 2693237 := bbase (se 5 (by rfl) ⟨126245, by rfl⟩ : syracuseStep 2693237 = 252491) (by norm_num)
theorem B6060149 : Blo 1794098 6060149 := bbase (se 5 (by rfl) ⟨284069, by rfl⟩ : syracuseStep 6060149 = 568139) (by norm_num)
theorem B4036733 : Blo 1794098 4036733 := bbase (se 3 (by rfl) ⟨756887, by rfl⟩ : syracuseStep 4036733 = 1513775) (by norm_num)
theorem B2693261 : Blo 1794098 2693261 := bbase (se 3 (by rfl) ⟨504986, by rfl⟩ : syracuseStep 2693261 = 1009973) (by norm_num)
theorem B2046097 : Blo 1794098 2046097 := bbase (se 2 (by rfl) ⟨767286, by rfl⟩ : syracuseStep 2046097 = 1534573) (by norm_num)
theorem B2693285 : Blo 1794098 2693285 := bbase (se 4 (by rfl) ⟨252495, by rfl⟩ : syracuseStep 2693285 = 504991) (by norm_num)
theorem B2693309 : Blo 1794098 2693309 := bbase (se 3 (by rfl) ⟨504995, by rfl⟩ : syracuseStep 2693309 = 1009991) (by norm_num)
theorem B4036805 : Blo 1794098 4036805 := bbase (se 4 (by rfl) ⟨378450, by rfl⟩ : syracuseStep 4036805 = 756901) (by norm_num)
theorem B3029197 : Blo 1794098 3029197 := bbase (se 3 (by rfl) ⟨567974, by rfl⟩ : syracuseStep 3029197 = 1135949) (by norm_num)
theorem B31520981 : Blo 1794098 31520981 := bbase (se 7 (by rfl) ⟨369386, by rfl⟩ : syracuseStep 31520981 = 738773) (by norm_num)
theorem B2693333 : Blo 1794098 2693333 := bbase (se 7 (by rfl) ⟨31562, by rfl⟩ : syracuseStep 2693333 = 63125) (by norm_num)
theorem B9214165 : Blo 1794098 9214165 := bbase (se 7 (by rfl) ⟨107978, by rfl⟩ : syracuseStep 9214165 = 215957) (by norm_num)
theorem B2693357 : Blo 1794098 2693357 := bbase (se 3 (by rfl) ⟨505004, by rfl⟩ : syracuseStep 2693357 = 1010009) (by norm_num)
theorem B3832069 : Blo 1794098 3832069 := bbase (se 4 (by rfl) ⟨359256, by rfl⟩ : syracuseStep 3832069 = 718513) (by norm_num)
theorem B2693381 : Blo 1794098 2693381 := bbase (se 4 (by rfl) ⟨252504, by rfl⟩ : syracuseStep 2693381 = 505009) (by norm_num)
theorem B4036877 : Blo 1794098 4036877 := bbase (se 3 (by rfl) ⟨756914, by rfl⟩ : syracuseStep 4036877 = 1513829) (by norm_num)
theorem B2693405 : Blo 1794098 2693405 := bbase (se 3 (by rfl) ⟨505013, by rfl⟩ : syracuseStep 2693405 = 1010027) (by norm_num)
theorem B3029285 : Blo 1794098 3029285 := bbase (se 4 (by rfl) ⟨283995, by rfl⟩ : syracuseStep 3029285 = 567991) (by norm_num)
theorem B2693429 : Blo 1794098 2693429 := bbase (se 5 (by rfl) ⟨126254, by rfl⟩ : syracuseStep 2693429 = 252509) (by norm_num)
theorem B2693453 : Blo 1794098 2693453 := bbase (se 3 (by rfl) ⟨505022, by rfl⟩ : syracuseStep 2693453 = 1010045) (by norm_num)
theorem B4036949 : Blo 1794098 4036949 := bbase (se 10 (by rfl) ⟨5913, by rfl⟩ : syracuseStep 4036949 = 11827) (by norm_num)
theorem B4544869 : Blo 1794098 4544869 := bbase (se 4 (by rfl) ⟨426081, by rfl⟩ : syracuseStep 4544869 = 852163) (by norm_num)
theorem B2693477 : Blo 1794098 2693477 := bbase (se 4 (by rfl) ⟨252513, by rfl⟩ : syracuseStep 2693477 = 505027) (by norm_num)
theorem B2693501 : Blo 1794098 2693501 := bbase (se 3 (by rfl) ⟨505031, by rfl⟩ : syracuseStep 2693501 = 1010063) (by norm_num)
theorem B2185601 : Blo 1794098 2185601 := bbase (se 2 (by rfl) ⟨819600, by rfl⟩ : syracuseStep 2185601 = 1639201) (by norm_num)
theorem B2693525 : Blo 1794098 2693525 := bbase (se 6 (by rfl) ⟨63129, by rfl⟩ : syracuseStep 2693525 = 126259) (by norm_num)
theorem B4037021 : Blo 1794098 4037021 := bbase (se 3 (by rfl) ⟨756941, by rfl⟩ : syracuseStep 4037021 = 1513883) (by norm_num)
theorem B3029413 : Blo 1794098 3029413 := bbase (se 4 (by rfl) ⟨284007, by rfl⟩ : syracuseStep 3029413 = 568015) (by norm_num)
theorem B3455405 : Blo 1794098 3455405 := bbase (se 3 (by rfl) ⟨647888, by rfl⟩ : syracuseStep 3455405 = 1295777) (by norm_num)
theorem B2693549 : Blo 1794098 2693549 := bbase (se 3 (by rfl) ⟨505040, by rfl⟩ : syracuseStep 2693549 = 1010081) (by norm_num)
theorem B2693573 : Blo 1794098 2693573 := bbase (se 4 (by rfl) ⟨252522, by rfl⟩ : syracuseStep 2693573 = 505045) (by norm_num)
theorem B4544981 : Blo 1794098 4544981 := bbase (se 7 (by rfl) ⟨53261, by rfl⟩ : syracuseStep 4544981 = 106523) (by norm_num)
theorem B2873821 : Blo 1794098 2873821 := bbase (se 3 (by rfl) ⟨538841, by rfl⟩ : syracuseStep 2873821 = 1077683) (by norm_num)
theorem B2693597 : Blo 1794098 2693597 := bbase (se 3 (by rfl) ⟨505049, by rfl⟩ : syracuseStep 2693597 = 1010099) (by norm_num)
theorem B4037093 : Blo 1794098 4037093 := bbase (se 4 (by rfl) ⟨378477, by rfl⟩ : syracuseStep 4037093 = 756955) (by norm_num)
theorem B2693621 : Blo 1794098 2693621 := bbase (se 5 (by rfl) ⟨126263, by rfl⟩ : syracuseStep 2693621 = 252527) (by norm_num)
theorem B3029501 : Blo 1794098 3029501 := bbase (se 3 (by rfl) ⟨568031, by rfl⟩ : syracuseStep 3029501 = 1136063) (by norm_num)
theorem B2693645 : Blo 1794098 2693645 := bbase (se 3 (by rfl) ⟨505058, by rfl⟩ : syracuseStep 2693645 = 1010117) (by norm_num)
theorem B7281173 : Blo 1794098 7281173 := bbase (se 6 (by rfl) ⟨170652, by rfl⟩ : syracuseStep 7281173 = 341305) (by norm_num)
theorem B2873885 : Blo 1794098 2873885 := bbase (se 3 (by rfl) ⟨538853, by rfl⟩ : syracuseStep 2873885 = 1077707) (by norm_num)
theorem B6060581 : Blo 1794098 6060581 := bbase (se 4 (by rfl) ⟨568179, by rfl⟩ : syracuseStep 6060581 = 1136359) (by norm_num)
theorem B2693669 : Blo 1794098 2693669 := bbase (se 4 (by rfl) ⟨252531, by rfl⟩ : syracuseStep 2693669 = 505063) (by norm_num)
theorem B4037165 : Blo 1794098 4037165 := bbase (se 3 (by rfl) ⟨756968, by rfl⟩ : syracuseStep 4037165 = 1513937) (by norm_num)
theorem B2693693 : Blo 1794098 2693693 := bbase (se 3 (by rfl) ⟨505067, by rfl⟩ : syracuseStep 2693693 = 1010135) (by norm_num)
theorem B2693717 : Blo 1794098 2693717 := bbase (se 8 (by rfl) ⟨15783, by rfl⟩ : syracuseStep 2693717 = 31567) (by norm_num)
theorem B2693741 : Blo 1794098 2693741 := bbase (se 3 (by rfl) ⟨505076, by rfl⟩ : syracuseStep 2693741 = 1010153) (by norm_num)
theorem B4037237 : Blo 1794098 4037237 := bbase (se 5 (by rfl) ⟨189245, by rfl⟩ : syracuseStep 4037237 = 378491) (by norm_num)
theorem B3029629 : Blo 1794098 3029629 := bbase (se 3 (by rfl) ⟨568055, by rfl⟩ : syracuseStep 3029629 = 1136111) (by norm_num)
theorem B2693765 : Blo 1794098 2693765 := bbase (se 4 (by rfl) ⟨252540, by rfl⟩ : syracuseStep 2693765 = 505081) (by norm_num)
theorem B7666325 : Blo 1794098 7666325 := bbase (se 6 (by rfl) ⟨179679, by rfl⟩ : syracuseStep 7666325 = 359359) (by norm_num)
theorem B4545173 : Blo 1794098 4545173 := bbase (se 6 (by rfl) ⟨106527, by rfl⟩ : syracuseStep 4545173 = 213055) (by norm_num)
theorem B2693789 : Blo 1794098 2693789 := bbase (se 3 (by rfl) ⟨505085, by rfl⟩ : syracuseStep 2693789 = 1010171) (by norm_num)
theorem B3234485 : Blo 1794098 3234485 := bbase (se 5 (by rfl) ⟨151616, by rfl⟩ : syracuseStep 3234485 = 303233) (by norm_num)
theorem B2693813 : Blo 1794098 2693813 := bbase (se 5 (by rfl) ⟨126272, by rfl⟩ : syracuseStep 2693813 = 252545) (by norm_num)
theorem B4037309 : Blo 1794098 4037309 := bbase (se 3 (by rfl) ⟨756995, by rfl⟩ : syracuseStep 4037309 = 1513991) (by norm_num)
theorem B2693837 : Blo 1794098 2693837 := bbase (se 3 (by rfl) ⟨505094, by rfl⟩ : syracuseStep 2693837 = 1010189) (by norm_num)
theorem B3406549 : Blo 1794098 3406549 := bbase (se 7 (by rfl) ⟨39920, by rfl⟩ : syracuseStep 3406549 = 79841) (by norm_num)
theorem B3029717 : Blo 1794098 3029717 := bbase (se 7 (by rfl) ⟨35504, by rfl⟩ : syracuseStep 3029717 = 71009) (by norm_num)
theorem B2693861 : Blo 1794098 2693861 := bbase (se 4 (by rfl) ⟨252549, by rfl⟩ : syracuseStep 2693861 = 505099) (by norm_num)
theorem B2046713 : Blo 1794098 2046713 := bbase (se 2 (by rfl) ⟨767517, by rfl⟩ : syracuseStep 2046713 = 1535035) (by norm_num)
theorem B2693885 : Blo 1794098 2693885 := bbase (se 3 (by rfl) ⟨505103, by rfl⟩ : syracuseStep 2693885 = 1010207) (by norm_num)
theorem B4037381 : Blo 1794098 4037381 := bbase (se 4 (by rfl) ⟨378504, by rfl⟩ : syracuseStep 4037381 = 757009) (by norm_num)
theorem B2693909 : Blo 1794098 2693909 := bbase (se 6 (by rfl) ⟨63138, by rfl⟩ : syracuseStep 2693909 = 126277) (by norm_num)
theorem B2693933 : Blo 1794098 2693933 := bbase (se 3 (by rfl) ⟨505112, by rfl⟩ : syracuseStep 2693933 = 1010225) (by norm_num)
theorem B2693957 : Blo 1794098 2693957 := bbase (se 4 (by rfl) ⟨252558, by rfl⟩ : syracuseStep 2693957 = 505117) (by norm_num)
theorem B4037453 : Blo 1794098 4037453 := bbase (se 3 (by rfl) ⟨757022, by rfl⟩ : syracuseStep 4037453 = 1514045) (by norm_num)
theorem B5749589 : Blo 1794098 5749589 := bbase (se 9 (by rfl) ⟨16844, by rfl⟩ : syracuseStep 5749589 = 33689) (by norm_num)
theorem B8624981 : Blo 1794098 8624981 := bbase (se 9 (by rfl) ⟨25268, by rfl⟩ : syracuseStep 8624981 = 50537) (by norm_num)
theorem B3029845 : Blo 1794098 3029845 := bbase (se 9 (by rfl) ⟨8876, by rfl⟩ : syracuseStep 3029845 = 17753) (by norm_num)
theorem B9091925 : Blo 1794098 9091925 := bbase (se 9 (by rfl) ⟨26636, by rfl⟩ : syracuseStep 9091925 = 53273) (by norm_num)
theorem B2693981 : Blo 1794098 2693981 := bbase (se 3 (by rfl) ⟨505121, by rfl⟩ : syracuseStep 2693981 = 1010243) (by norm_num)
theorem B3406693 : Blo 1794098 3406693 := bbase (se 4 (by rfl) ⟨319377, by rfl⟩ : syracuseStep 3406693 = 638755) (by norm_num)
theorem B2694005 : Blo 1794098 2694005 := bbase (se 5 (by rfl) ⟨126281, by rfl⟩ : syracuseStep 2694005 = 252563) (by norm_num)
theorem B2694029 : Blo 1794098 2694029 := bbase (se 3 (by rfl) ⟨505130, by rfl⟩ : syracuseStep 2694029 = 1010261) (by norm_num)
theorem B4037525 : Blo 1794098 4037525 := bbase (se 6 (by rfl) ⟨94629, by rfl⟩ : syracuseStep 4037525 = 189259) (by norm_num)
theorem B2694053 : Blo 1794098 2694053 := bbase (se 4 (by rfl) ⟨252567, by rfl⟩ : syracuseStep 2694053 = 505135) (by norm_num)
theorem B3029933 : Blo 1794098 3029933 := bbase (se 3 (by rfl) ⟨568112, by rfl⟩ : syracuseStep 3029933 = 1136225) (by norm_num)
theorem B10918837 : Blo 1794098 10918837 := bbase (se 5 (by rfl) ⟨511820, by rfl⟩ : syracuseStep 10918837 = 1023641) (by norm_num)
theorem B2694077 : Blo 1794098 2694077 := bbase (se 3 (by rfl) ⟨505139, by rfl⟩ : syracuseStep 2694077 = 1010279) (by norm_num)
theorem B6061013 : Blo 1794098 6061013 := bbase (se 7 (by rfl) ⟨71027, by rfl⟩ : syracuseStep 6061013 = 142055) (by norm_num)
theorem B2694101 : Blo 1794098 2694101 := bbase (se 7 (by rfl) ⟨31571, by rfl⟩ : syracuseStep 2694101 = 63143) (by norm_num)
theorem B4037597 : Blo 1794098 4037597 := bbase (se 3 (by rfl) ⟨757049, by rfl⟩ : syracuseStep 4037597 = 1514099) (by norm_num)
theorem B4545517 : Blo 1794098 4545517 := bbase (se 3 (by rfl) ⟨852284, by rfl⟩ : syracuseStep 4545517 = 1704569) (by norm_num)
theorem B2694125 : Blo 1794098 2694125 := bbase (se 3 (by rfl) ⟨505148, by rfl⟩ : syracuseStep 2694125 = 1010297) (by norm_num)
theorem B2046973 : Blo 1794098 2046973 := bbase (se 3 (by rfl) ⟨383807, by rfl⟩ : syracuseStep 2046973 = 767615) (by norm_num)
theorem B3406853 : Blo 1794098 3406853 := bbase (se 4 (by rfl) ⟨319392, by rfl⟩ : syracuseStep 3406853 = 638785) (by norm_num)
theorem B2333701 : Blo 1794098 2333701 := bbase (se 4 (by rfl) ⟨218784, by rfl⟩ : syracuseStep 2333701 = 437569) (by norm_num)
theorem B4037669 : Blo 1794098 4037669 := bbase (se 4 (by rfl) ⟨378531, by rfl⟩ : syracuseStep 4037669 = 757063) (by norm_num)
theorem B3030061 : Blo 1794098 3030061 := bbase (se 3 (by rfl) ⟨568136, by rfl⟩ : syracuseStep 3030061 = 1136273) (by norm_num)
theorem B6470741 : Blo 1794098 6470741 := bbase (se 8 (by rfl) ⟨37914, by rfl⟩ : syracuseStep 6470741 = 75829) (by norm_num)
theorem B4545629 : Blo 1794098 4545629 := bbase (se 3 (by rfl) ⟨852305, by rfl⟩ : syracuseStep 4545629 = 1704611) (by norm_num)
theorem B4037741 : Blo 1794098 4037741 := bbase (se 3 (by rfl) ⟨757076, by rfl⟩ : syracuseStep 4037741 = 1514153) (by norm_num)
theorem B1916017 : Blo 1794098 1916017 := bbase (se 2 (by rfl) ⟨718506, by rfl⟩ : syracuseStep 1916017 = 1437013) (by norm_num)
theorem B3832957 : Blo 1794098 3832957 := bbase (se 3 (by rfl) ⟨718679, by rfl⟩ : syracuseStep 3832957 = 1437359) (by norm_num)
theorem B3030149 : Blo 1794098 3030149 := bbase (se 4 (by rfl) ⟨284076, by rfl⟩ : syracuseStep 3030149 = 568153) (by norm_num)
theorem B3406997 : Blo 1794098 3406997 := bbase (se 6 (by rfl) ⟨79851, by rfl⟩ : syracuseStep 3406997 = 159703) (by norm_num)
theorem B4037813 : Blo 1794098 4037813 := bbase (se 5 (by rfl) ⟨189272, by rfl⟩ : syracuseStep 4037813 = 378545) (by norm_num)
theorem B2555077 : Blo 1794098 2555077 := bbase (se 4 (by rfl) ⟨239538, by rfl⟩ : syracuseStep 2555077 = 479077) (by norm_num)
theorem B69008597 : Blo 1794098 69008597 := bbase (se 7 (by rfl) ⟨808694, by rfl⟩ : syracuseStep 69008597 = 1617389) (by norm_num)
theorem B1916137 : Blo 1794098 1916137 := bbase (se 2 (by rfl) ⟨718551, by rfl⟩ : syracuseStep 1916137 = 1437103) (by norm_num)
theorem B9084149 : Blo 1794098 9084149 := bbase (se 5 (by rfl) ⟨425819, by rfl⟩ : syracuseStep 9084149 = 851639) (by norm_num)
theorem B3833077 : Blo 1794098 3833077 := bbase (se 5 (by rfl) ⟨179675, by rfl⟩ : syracuseStep 3833077 = 359351) (by norm_num)
theorem B3235061 : Blo 1794098 3235061 := bbase (se 5 (by rfl) ⟨151643, by rfl⟩ : syracuseStep 3235061 = 303287) (by norm_num)
theorem B4037885 : Blo 1794098 4037885 := bbase (se 3 (by rfl) ⟨757103, by rfl⟩ : syracuseStep 4037885 = 1514207) (by norm_num)
theorem B3030277 : Blo 1794098 3030277 := bbase (se 4 (by rfl) ⟨284088, by rfl⟩ : syracuseStep 3030277 = 568177) (by norm_num)
theorem B4545821 : Blo 1794098 4545821 := bbase (se 3 (by rfl) ⟨852341, by rfl⟩ : syracuseStep 4545821 = 1704683) (by norm_num)
theorem B4037957 : Blo 1794098 4037957 := bbase (se 4 (by rfl) ⟨378558, by rfl⟩ : syracuseStep 4037957 = 757117) (by norm_num)
theorem B3030365 : Blo 1794098 3030365 := bbase (se 3 (by rfl) ⟨568193, by rfl⟩ : syracuseStep 3030365 = 1136387) (by norm_num)
theorem B6061445 : Blo 1794098 6061445 := bbase (se 4 (by rfl) ⟨568260, by rfl⟩ : syracuseStep 6061445 = 1136521) (by norm_num)
theorem B4038029 : Blo 1794098 4038029 := bbase (se 3 (by rfl) ⟨757130, by rfl⟩ : syracuseStep 4038029 = 1514261) (by norm_num)
theorem B4095397 : Blo 1794098 4095397 := bbase (se 4 (by rfl) ⟨383943, by rfl⟩ : syracuseStep 4095397 = 767887) (by norm_num)
theorem B3407285 : Blo 1794098 3407285 := bbase (se 5 (by rfl) ⟨159716, by rfl⟩ : syracuseStep 3407285 = 319433) (by norm_num)
theorem B4038101 : Blo 1794098 4038101 := bbase (se 7 (by rfl) ⟨47321, by rfl⟩ : syracuseStep 4038101 = 94643) (by norm_num)
theorem B3030493 : Blo 1794098 3030493 := bbase (se 3 (by rfl) ⟨568217, by rfl⟩ : syracuseStep 3030493 = 1136435) (by norm_num)
theorem B1916389 : Blo 1794098 1916389 := bbase (se 4 (by rfl) ⟨179661, by rfl⟩ : syracuseStep 1916389 = 359323) (by norm_num)
theorem B1916393 : Blo 1794098 1916393 := bbase (se 2 (by rfl) ⟨718647, by rfl⟩ : syracuseStep 1916393 = 1437295) (by norm_num)
theorem B3833333 : Blo 1794098 3833333 := bbase (se 5 (by rfl) ⟨179687, by rfl⟩ : syracuseStep 3833333 = 359375) (by norm_num)
theorem B4038173 : Blo 1794098 4038173 := bbase (se 3 (by rfl) ⟨757157, by rfl⟩ : syracuseStep 4038173 = 1514315) (by norm_num)
theorem B6815285 : Blo 1794098 6815285 := bbase (se 5 (by rfl) ⟨319466, by rfl⟩ : syracuseStep 6815285 = 638933) (by norm_num)
theorem B3030581 : Blo 1794098 3030581 := bbase (se 5 (by rfl) ⟨142058, by rfl⟩ : syracuseStep 3030581 = 284117) (by norm_num)
theorem B3407437 : Blo 1794098 3407437 := bbase (se 3 (by rfl) ⟨638894, by rfl⟩ : syracuseStep 3407437 = 1277789) (by norm_num)
theorem B4038245 : Blo 1794098 4038245 := bbase (se 4 (by rfl) ⟨378585, by rfl⟩ : syracuseStep 4038245 = 757171) (by norm_num)
theorem B4546165 : Blo 1794098 4546165 := bbase (se 5 (by rfl) ⟨213101, by rfl⟩ : syracuseStep 4546165 = 426203) (by norm_num)
theorem B4038317 : Blo 1794098 4038317 := bbase (se 3 (by rfl) ⟨757184, by rfl⟩ : syracuseStep 4038317 = 1514369) (by norm_num)
theorem B3030709 : Blo 1794098 3030709 := bbase (se 5 (by rfl) ⟨142064, by rfl⟩ : syracuseStep 3030709 = 284129) (by norm_num)
theorem B4546277 : Blo 1794098 4546277 := bbase (se 4 (by rfl) ⟨426213, by rfl⟩ : syracuseStep 4546277 = 852427) (by norm_num)
theorem B4038389 : Blo 1794098 4038389 := bbase (se 5 (by rfl) ⟨189299, by rfl⟩ : syracuseStep 4038389 = 378599) (by norm_num)
theorem B3030797 : Blo 1794098 3030797 := bbase (se 3 (by rfl) ⟨568274, by rfl⟩ : syracuseStep 3030797 = 1136549) (by norm_num)
theorem B2555669 : Blo 1794098 2555669 := bbase (se 6 (by rfl) ⟨59898, by rfl⟩ : syracuseStep 2555669 = 119797) (by norm_num)
theorem B4038461 : Blo 1794098 4038461 := bbase (se 3 (by rfl) ⟨757211, by rfl⟩ : syracuseStep 4038461 = 1514423) (by norm_num)
theorem B2875205 : Blo 1794098 2875205 := bbase (se 4 (by rfl) ⟨269550, by rfl⟩ : syracuseStep 2875205 = 539101) (by norm_num)
theorem B6815573 : Blo 1794098 6815573 := bbase (se 9 (by rfl) ⟨19967, by rfl⟩ : syracuseStep 6815573 = 39935) (by norm_num)
theorem B15343445 : Blo 1794098 15343445 := bbase (se 9 (by rfl) ⟨44951, by rfl⟩ : syracuseStep 15343445 = 89903) (by norm_num)
theorem B2555749 : Blo 1794098 2555749 := bbase (se 4 (by rfl) ⟨239601, by rfl⟩ : syracuseStep 2555749 = 479203) (by norm_num)
theorem B3407741 : Blo 1794098 3407741 := bbase (se 3 (by rfl) ⟨638951, by rfl⟩ : syracuseStep 3407741 = 1277903) (by norm_num)
theorem B4038533 : Blo 1794098 4038533 := bbase (se 4 (by rfl) ⟨378612, by rfl⟩ : syracuseStep 4038533 = 757225) (by norm_num)
theorem B2875333 : Blo 1794098 2875333 := bbase (se 4 (by rfl) ⟨269562, by rfl⟩ : syracuseStep 2875333 = 539125) (by norm_num)
theorem B4038605 : Blo 1794098 4038605 := bbase (se 3 (by rfl) ⟨757238, by rfl⟩ : syracuseStep 4038605 = 1514477) (by norm_num)
theorem B2555869 : Blo 1794098 2555869 := bbase (se 3 (by rfl) ⟨479225, by rfl⟩ : syracuseStep 2555869 = 958451) (by norm_num)
theorem B4038659 : Blo 1794098 4038659 := bstep (se 1 (by rfl) ⟨3028994, by rfl⟩ : syracuseStep 4038659 = 6057989) B6057989
theorem B3235889 : Blo 1794098 3235889 := bstep (se 2 (by rfl) ⟨1213458, by rfl⟩ : syracuseStep 3235889 = 2426917) B2426917
theorem B1794099 : Blo 1794098 1794099 := bstep (se 1 (by rfl) ⟨1345574, by rfl⟩ : syracuseStep 1794099 = 2691149) B2691149
theorem B1794115 : Blo 1794098 1794115 := bstep (se 1 (by rfl) ⟨1345586, by rfl⟩ : syracuseStep 1794115 = 2691173) B2691173
theorem B5111885 : Blo 1794098 5111885 := bstep (se 3 (by rfl) ⟨958478, by rfl⟩ : syracuseStep 5111885 = 1916957) B1916957
theorem B1794131 : Blo 1794098 1794131 := bstep (se 1 (by rfl) ⟨1345598, by rfl⟩ : syracuseStep 1794131 = 2691197) B2691197
theorem B2875475 : Blo 1794098 2875475 := bstep (se 1 (by rfl) ⟨2156606, by rfl⟩ : syracuseStep 2875475 = 4313213) B4313213
theorem B1794147 : Blo 1794098 1794147 := bstep (se 1 (by rfl) ⟨1345610, by rfl⟩ : syracuseStep 1794147 = 2691221) B2691221
theorem B1794163 : Blo 1794098 1794163 := bstep (se 1 (by rfl) ⟨1345622, by rfl⟩ : syracuseStep 1794163 = 2691245) B2691245
theorem B1794179 : Blo 1794098 1794179 := bstep (se 1 (by rfl) ⟨1345634, by rfl⟩ : syracuseStep 1794179 = 2691269) B2691269
theorem B1794195 : Blo 1794098 1794195 := bstep (se 1 (by rfl) ⟨1345646, by rfl⟩ : syracuseStep 1794195 = 2691293) B2691293
theorem B1794211 : Blo 1794098 1794211 := bstep (se 1 (by rfl) ⟨1345658, by rfl⟩ : syracuseStep 1794211 = 2691317) B2691317
theorem B1794227 : Blo 1794098 1794227 := bstep (se 1 (by rfl) ⟨1345670, by rfl⟩ : syracuseStep 1794227 = 2691341) B2691341
theorem B2728129 : Blo 1794098 2728129 := bstep (se 2 (by rfl) ⟨1023048, by rfl⟩ : syracuseStep 2728129 = 2046097) B2046097
theorem B1794243 : Blo 1794098 1794243 := bstep (se 1 (by rfl) ⟨1345682, by rfl⟩ : syracuseStep 1794243 = 2691365) B2691365
theorem B1794259 : Blo 1794098 1794259 := bstep (se 1 (by rfl) ⟨1345694, by rfl⟩ : syracuseStep 1794259 = 2691389) B2691389
theorem B1794275 : Blo 1794098 1794275 := bstep (se 1 (by rfl) ⟨1345706, by rfl⟩ : syracuseStep 1794275 = 2691413) B2691413
theorem B1794291 : Blo 1794098 1794291 := bstep (se 1 (by rfl) ⟨1345718, by rfl⟩ : syracuseStep 1794291 = 2691437) B2691437
theorem B1794307 : Blo 1794098 1794307 := bstep (se 1 (by rfl) ⟨1345730, by rfl⟩ : syracuseStep 1794307 = 2691461) B2691461
theorem B5112067 : Blo 1794098 5112067 := bstep (se 1 (by rfl) ⟨3834050, by rfl⟩ : syracuseStep 5112067 = 7668101) B7668101
theorem B4038929 : Blo 1794098 4038929 := bstep (se 2 (by rfl) ⟨1514598, by rfl⟩ : syracuseStep 4038929 = 3029197) B3029197
theorem B1794323 : Blo 1794098 1794323 := bstep (se 1 (by rfl) ⟨1345742, by rfl⟩ : syracuseStep 1794323 = 2691485) B2691485
theorem B2556193 : Blo 1794098 2556193 := bstep (se 2 (by rfl) ⟨958572, by rfl⟩ : syracuseStep 2556193 = 1917145) B1917145
theorem B1794339 : Blo 1794098 1794339 := bstep (se 1 (by rfl) ⟨1345754, by rfl⟩ : syracuseStep 1794339 = 2691509) B2691509
theorem B4038947 : Blo 1794098 4038947 := bstep (se 1 (by rfl) ⟨3029210, by rfl⟩ : syracuseStep 4038947 = 6058421) B6058421
theorem B7668017 : Blo 1794098 7668017 := bstep (se 2 (by rfl) ⟨2875506, by rfl⟩ : syracuseStep 7668017 = 5751013) B5751013
theorem B1794355 : Blo 1794098 1794355 := bstep (se 1 (by rfl) ⟨1345766, by rfl⟩ : syracuseStep 1794355 = 2691533) B2691533
theorem B1794371 : Blo 1794098 1794371 := bstep (se 1 (by rfl) ⟨1345778, by rfl⟩ : syracuseStep 1794371 = 2691557) B2691557
theorem B1818947 : Blo 1794098 1818947 := bstep (se 1 (by rfl) ⟨1364210, by rfl⟩ : syracuseStep 1818947 = 2728421) B2728421
theorem B13631813 : Blo 1794098 13631813 := bstep (se 4 (by rfl) ⟨1277982, by rfl⟩ : syracuseStep 13631813 = 2555965) B2555965
theorem B1794387 : Blo 1794098 1794387 := bstep (se 1 (by rfl) ⟨1345790, by rfl⟩ : syracuseStep 1794387 = 2691581) B2691581
theorem B1794403 : Blo 1794098 1794403 := bstep (se 1 (by rfl) ⟨1345802, by rfl⟩ : syracuseStep 1794403 = 2691605) B2691605
theorem B2425187 : Blo 1794098 2425187 := bstep (se 1 (by rfl) ⟨1818890, by rfl⟩ : syracuseStep 2425187 = 3637781) B3637781
theorem B1818979 : Blo 1794098 1818979 := bstep (se 1 (by rfl) ⟨1364234, by rfl⟩ : syracuseStep 1818979 = 2728469) B2728469
theorem B9085283 : Blo 1794098 9085283 := bstep (se 1 (by rfl) ⟨6813962, by rfl⟩ : syracuseStep 9085283 = 13627925) B13627925
theorem B7668067 : Blo 1794098 7668067 := bstep (se 1 (by rfl) ⟨5751050, by rfl⟩ : syracuseStep 7668067 = 11502101) B11502101
theorem B3408227 : Blo 1794098 3408227 := bstep (se 1 (by rfl) ⟨2556170, by rfl⟩ : syracuseStep 3408227 = 5112341) B5112341
theorem B1794419 : Blo 1794098 1794419 := bstep (se 1 (by rfl) ⟨1345814, by rfl⟩ : syracuseStep 1794419 = 2691629) B2691629
theorem B2875763 : Blo 1794098 2875763 := bstep (se 1 (by rfl) ⟨2156822, by rfl⟩ : syracuseStep 2875763 = 4313645) B4313645
theorem B1794435 : Blo 1794098 1794435 := bstep (se 1 (by rfl) ⟨1345826, by rfl⟩ : syracuseStep 1794435 = 2691653) B2691653
theorem B1794451 : Blo 1794098 1794451 := bstep (se 1 (by rfl) ⟨1345838, by rfl⟩ : syracuseStep 1794451 = 2691677) B2691677
theorem B2556307 : Blo 1794098 2556307 := bstep (se 1 (by rfl) ⟨1917230, by rfl⟩ : syracuseStep 2556307 = 3834461) B3834461
theorem B1794467 : Blo 1794098 1794467 := bstep (se 1 (by rfl) ⟨1345850, by rfl⟩ : syracuseStep 1794467 = 2691701) B2691701
theorem B5112227 : Blo 1794098 5112227 := bstep (se 1 (by rfl) ⟨3834170, by rfl⟩ : syracuseStep 5112227 = 7668341) B7668341
theorem B1794483 : Blo 1794098 1794483 := bstep (se 1 (by rfl) ⟨1345862, by rfl⟩ : syracuseStep 1794483 = 2691725) B2691725
theorem B1794499 : Blo 1794098 1794499 := bstep (se 1 (by rfl) ⟨1345874, by rfl⟩ : syracuseStep 1794499 = 2691749) B2691749
theorem B3834307 : Blo 1794098 3834307 := bstep (se 1 (by rfl) ⟨2875730, by rfl⟩ : syracuseStep 3834307 = 5751461) B5751461
theorem B1794515 : Blo 1794098 1794515 := bstep (se 1 (by rfl) ⟨1345886, by rfl⟩ : syracuseStep 1794515 = 2691773) B2691773
theorem B1794531 : Blo 1794098 1794531 := bstep (se 1 (by rfl) ⟨1345898, by rfl⟩ : syracuseStep 1794531 = 2691797) B2691797
theorem B1794547 : Blo 1794098 1794547 := bstep (se 1 (by rfl) ⟨1345910, by rfl⟩ : syracuseStep 1794547 = 2691821) B2691821
theorem B1917427 : Blo 1794098 1917427 := bstep (se 1 (by rfl) ⟨1438070, by rfl⟩ : syracuseStep 1917427 = 2876141) B2876141
theorem B1794563 : Blo 1794098 1794563 := bstep (se 1 (by rfl) ⟨1345922, by rfl⟩ : syracuseStep 1794563 = 2691845) B2691845
theorem B1794579 : Blo 1794098 1794579 := bstep (se 1 (by rfl) ⟨1345934, by rfl⟩ : syracuseStep 1794579 = 2691869) B2691869
theorem B1794595 : Blo 1794098 1794595 := bstep (se 1 (by rfl) ⟨1345946, by rfl⟩ : syracuseStep 1794595 = 2691893) B2691893
theorem B4039217 : Blo 1794098 4039217 := bstep (se 2 (by rfl) ⟨1514706, by rfl⟩ : syracuseStep 4039217 = 3029413) B3029413
theorem B1794611 : Blo 1794098 1794611 := bstep (se 1 (by rfl) ⟨1345958, by rfl⟩ : syracuseStep 1794611 = 2691917) B2691917
theorem B1794627 : Blo 1794098 1794627 := bstep (se 1 (by rfl) ⟨1345970, by rfl⟩ : syracuseStep 1794627 = 2691941) B2691941
theorem B4039235 : Blo 1794098 4039235 := bstep (se 1 (by rfl) ⟨3029426, by rfl⟩ : syracuseStep 4039235 = 6058853) B6058853
theorem B1794643 : Blo 1794098 1794643 := bstep (se 1 (by rfl) ⟨1345982, by rfl⟩ : syracuseStep 1794643 = 2691965) B2691965
theorem B1794659 : Blo 1794098 1794659 := bstep (se 1 (by rfl) ⟨1345994, by rfl⟩ : syracuseStep 1794659 = 2691989) B2691989
theorem B1794675 : Blo 1794098 1794675 := bstep (se 1 (by rfl) ⟨1346006, by rfl⟩ : syracuseStep 1794675 = 2692013) B2692013
theorem B1794691 : Blo 1794098 1794691 := bstep (se 1 (by rfl) ⟨1346018, by rfl⟩ : syracuseStep 1794691 = 2692037) B2692037
theorem B1794707 : Blo 1794098 1794707 := bstep (se 1 (by rfl) ⟨1346030, by rfl⟩ : syracuseStep 1794707 = 2692061) B2692061
theorem B1794723 : Blo 1794098 1794723 := bstep (se 1 (by rfl) ⟨1346042, by rfl⟩ : syracuseStep 1794723 = 2692085) B2692085
theorem B1794739 : Blo 1794098 1794739 := bstep (se 1 (by rfl) ⟨1346054, by rfl⟩ : syracuseStep 1794739 = 2692109) B2692109
theorem B1794755 : Blo 1794098 1794755 := bstep (se 1 (by rfl) ⟨1346066, by rfl⟩ : syracuseStep 1794755 = 2692133) B2692133
theorem B1794771 : Blo 1794098 1794771 := bstep (se 1 (by rfl) ⟨1346078, by rfl⟩ : syracuseStep 1794771 = 2692157) B2692157
theorem B1794787 : Blo 1794098 1794787 := bstep (se 1 (by rfl) ⟨1346090, by rfl⟩ : syracuseStep 1794787 = 2692181) B2692181
theorem B1794803 : Blo 1794098 1794803 := bstep (se 1 (by rfl) ⟨1346102, by rfl⟩ : syracuseStep 1794803 = 2692205) B2692205
theorem B1794819 : Blo 1794098 1794819 := bstep (se 1 (by rfl) ⟨1346114, by rfl⟩ : syracuseStep 1794819 = 2692229) B2692229
theorem B1794835 : Blo 1794098 1794835 := bstep (se 1 (by rfl) ⟨1346126, by rfl⟩ : syracuseStep 1794835 = 2692253) B2692253
theorem B1794851 : Blo 1794098 1794851 := bstep (se 1 (by rfl) ⟨1346138, by rfl⟩ : syracuseStep 1794851 = 2692277) B2692277
theorem B1794867 : Blo 1794098 1794867 := bstep (se 1 (by rfl) ⟨1346150, by rfl⟩ : syracuseStep 1794867 = 2692301) B2692301
theorem B1794883 : Blo 1794098 1794883 := bstep (se 1 (by rfl) ⟨1346162, by rfl⟩ : syracuseStep 1794883 = 2692325) B2692325
theorem B9700165 : Blo 1794098 9700165 := bstep (se 4 (by rfl) ⟨909390, by rfl⟩ : syracuseStep 9700165 = 1818781) B1818781
theorem B4039505 : Blo 1794098 4039505 := bstep (se 2 (by rfl) ⟨1514814, by rfl⟩ : syracuseStep 4039505 = 3029629) B3029629
theorem B1794899 : Blo 1794098 1794899 := bstep (se 1 (by rfl) ⟨1346174, by rfl⟩ : syracuseStep 1794899 = 2692349) B2692349
theorem B1794915 : Blo 1794098 1794915 := bstep (se 1 (by rfl) ⟨1346186, by rfl⟩ : syracuseStep 1794915 = 2692373) B2692373
theorem B4039523 : Blo 1794098 4039523 := bstep (se 1 (by rfl) ⟨3029642, by rfl⟩ : syracuseStep 4039523 = 6059285) B6059285
theorem B1794931 : Blo 1794098 1794931 := bstep (se 1 (by rfl) ⟨1346198, by rfl⟩ : syracuseStep 1794931 = 2692397) B2692397
theorem B1794947 : Blo 1794098 1794947 := bstep (se 1 (by rfl) ⟨1346210, by rfl⟩ : syracuseStep 1794947 = 2692421) B2692421
theorem B1794963 : Blo 1794098 1794963 := bstep (se 1 (by rfl) ⟨1346222, by rfl⟩ : syracuseStep 1794963 = 2692445) B2692445
theorem B5530531 : Blo 1794098 5530531 := bstep (se 1 (by rfl) ⟨4147898, by rfl⟩ : syracuseStep 5530531 = 8295797) B8295797
theorem B1794979 : Blo 1794098 1794979 := bstep (se 1 (by rfl) ⟨1346234, by rfl⟩ : syracuseStep 1794979 = 2692469) B2692469
theorem B1794995 : Blo 1794098 1794995 := bstep (se 1 (by rfl) ⟨1346246, by rfl⟩ : syracuseStep 1794995 = 2692493) B2692493
theorem B1795011 : Blo 1794098 1795011 := bstep (se 1 (by rfl) ⟨1346258, by rfl⟩ : syracuseStep 1795011 = 2692517) B2692517
theorem B10224589 : Blo 1794098 10224589 := bstep (se 3 (by rfl) ⟨1917110, by rfl⟩ : syracuseStep 10224589 = 3834221) B3834221
theorem B1795027 : Blo 1794098 1795027 := bstep (se 1 (by rfl) ⟨1346270, by rfl⟩ : syracuseStep 1795027 = 2692541) B2692541
theorem B2425825 : Blo 1794098 2425825 := bstep (se 2 (by rfl) ⟨909684, by rfl⟩ : syracuseStep 2425825 = 1819369) B1819369
theorem B2728931 : Blo 1794098 2728931 := bstep (se 1 (by rfl) ⟨2046698, by rfl⟩ : syracuseStep 2728931 = 4093397) B4093397
theorem B1795043 : Blo 1794098 1795043 := bstep (se 1 (by rfl) ⟨1346282, by rfl⟩ : syracuseStep 1795043 = 2692565) B2692565
theorem B9700337 : Blo 1794098 9700337 := bstep (se 2 (by rfl) ⟨3637626, by rfl⟩ : syracuseStep 9700337 = 7275253) B7275253
theorem B1795059 : Blo 1794098 1795059 := bstep (se 1 (by rfl) ⟨1346294, by rfl⟩ : syracuseStep 1795059 = 2692589) B2692589
theorem B1795075 : Blo 1794098 1795075 := bstep (se 1 (by rfl) ⟨1346306, by rfl⟩ : syracuseStep 1795075 = 2692613) B2692613
theorem B10363909 : Blo 1794098 10363909 := bstep (se 4 (by rfl) ⟨971616, by rfl⟩ : syracuseStep 10363909 = 1943233) B1943233
theorem B1795091 : Blo 1794098 1795091 := bstep (se 1 (by rfl) ⟨1346318, by rfl⟩ : syracuseStep 1795091 = 2692637) B2692637
theorem B1795107 : Blo 1794098 1795107 := bstep (se 1 (by rfl) ⟨1346330, by rfl⟩ : syracuseStep 1795107 = 2692661) B2692661
theorem B1795123 : Blo 1794098 1795123 := bstep (se 1 (by rfl) ⟨1346342, by rfl⟩ : syracuseStep 1795123 = 2692685) B2692685
theorem B1795139 : Blo 1794098 1795139 := bstep (se 1 (by rfl) ⟨1346354, by rfl⟩ : syracuseStep 1795139 = 2692709) B2692709
theorem B9208909 : Blo 1794098 9208909 := bstep (se 3 (by rfl) ⟨1726670, by rfl⟩ : syracuseStep 9208909 = 3453341) B3453341
theorem B1795155 : Blo 1794098 1795155 := bstep (se 1 (by rfl) ⟨1346366, by rfl⟩ : syracuseStep 1795155 = 2692733) B2692733
theorem B1795171 : Blo 1794098 1795171 := bstep (se 1 (by rfl) ⟨1346378, by rfl⟩ : syracuseStep 1795171 = 2692757) B2692757
theorem B4039793 : Blo 1794098 4039793 := bstep (se 2 (by rfl) ⟨1514922, by rfl⟩ : syracuseStep 4039793 = 3029845) B3029845
theorem B1795187 : Blo 1794098 1795187 := bstep (se 1 (by rfl) ⟨1346390, by rfl⟩ : syracuseStep 1795187 = 2692781) B2692781
theorem B1795203 : Blo 1794098 1795203 := bstep (se 1 (by rfl) ⟨1346402, by rfl⟩ : syracuseStep 1795203 = 2692805) B2692805
theorem B4039811 : Blo 1794098 4039811 := bstep (se 1 (by rfl) ⟨3029858, by rfl⟩ : syracuseStep 4039811 = 6059717) B6059717
theorem B9086093 : Blo 1794098 9086093 := bstep (se 3 (by rfl) ⟨1703642, by rfl⟩ : syracuseStep 9086093 = 3407285) B3407285
theorem B1795219 : Blo 1794098 1795219 := bstep (se 1 (by rfl) ⟨1346414, by rfl⟩ : syracuseStep 1795219 = 2692829) B2692829
theorem B2876563 : Blo 1794098 2876563 := bstep (se 1 (by rfl) ⟨2157422, by rfl⟩ : syracuseStep 2876563 = 4314845) B4314845
theorem B1795235 : Blo 1794098 1795235 := bstep (se 1 (by rfl) ⟨1346426, by rfl⟩ : syracuseStep 1795235 = 2692853) B2692853
theorem B1795251 : Blo 1794098 1795251 := bstep (se 1 (by rfl) ⟨1346438, by rfl⟩ : syracuseStep 1795251 = 2692877) B2692877
theorem B1795267 : Blo 1794098 1795267 := bstep (se 1 (by rfl) ⟨1346450, by rfl⟩ : syracuseStep 1795267 = 2692901) B2692901
theorem B1795283 : Blo 1794098 1795283 := bstep (se 1 (by rfl) ⟨1346462, by rfl⟩ : syracuseStep 1795283 = 2692925) B2692925
theorem B1795299 : Blo 1794098 1795299 := bstep (se 1 (by rfl) ⟨1346474, by rfl⟩ : syracuseStep 1795299 = 2692949) B2692949
theorem B3409123 : Blo 1794098 3409123 := bstep (se 1 (by rfl) ⟨2556842, by rfl⟩ : syracuseStep 3409123 = 5113685) B5113685
theorem B14558449 : Blo 1794098 14558449 := bstep (se 2 (by rfl) ⟨5459418, by rfl⟩ : syracuseStep 14558449 = 10918837) B10918837
theorem B1795315 : Blo 1794098 1795315 := bstep (se 1 (by rfl) ⟨1346486, by rfl⟩ : syracuseStep 1795315 = 2692973) B2692973
theorem B1795331 : Blo 1794098 1795331 := bstep (se 1 (by rfl) ⟨1346498, by rfl⟩ : syracuseStep 1795331 = 2692997) B2692997
theorem B6055181 : Blo 1794098 6055181 := bstep (se 3 (by rfl) ⟨1135346, by rfl⟩ : syracuseStep 6055181 = 2270693) B2270693
theorem B1795347 : Blo 1794098 1795347 := bstep (se 1 (by rfl) ⟨1346510, by rfl⟩ : syracuseStep 1795347 = 2693021) B2693021
theorem B2876705 : Blo 1794098 2876705 := bstep (se 2 (by rfl) ⟨1078764, by rfl⟩ : syracuseStep 2876705 = 2157529) B2157529
theorem B1795363 : Blo 1794098 1795363 := bstep (se 1 (by rfl) ⟨1346522, by rfl⟩ : syracuseStep 1795363 = 2693045) B2693045
theorem B1795379 : Blo 1794098 1795379 := bstep (se 1 (by rfl) ⟨1346534, by rfl⟩ : syracuseStep 1795379 = 2693069) B2693069
theorem B2876737 : Blo 1794098 2876737 := bstep (se 2 (by rfl) ⟨1078776, by rfl⟩ : syracuseStep 2876737 = 2157553) B2157553
theorem B6055235 : Blo 1794098 6055235 := bstep (se 1 (by rfl) ⟨4541426, by rfl⟩ : syracuseStep 6055235 = 9082853) B9082853
theorem B1795395 : Blo 1794098 1795395 := bstep (se 1 (by rfl) ⟨1346546, by rfl⟩ : syracuseStep 1795395 = 2693093) B2693093
theorem B2729297 : Blo 1794098 2729297 := bstep (se 2 (by rfl) ⟨1023486, by rfl⟩ : syracuseStep 2729297 = 2046973) B2046973
theorem B1795411 : Blo 1794098 1795411 := bstep (se 1 (by rfl) ⟨1346558, by rfl⟩ : syracuseStep 1795411 = 2693117) B2693117
theorem B1795427 : Blo 1794098 1795427 := bstep (se 1 (by rfl) ⟨1346570, by rfl⟩ : syracuseStep 1795427 = 2693141) B2693141
theorem B23012707 : Blo 1794098 23012707 := bstep (se 1 (by rfl) ⟨17259530, by rfl⟩ : syracuseStep 23012707 = 34519061) B34519061
theorem B2303347 : Blo 1794098 2303347 := bstep (se 1 (by rfl) ⟨1727510, by rfl⟩ : syracuseStep 2303347 = 3455021) B3455021
theorem B1795443 : Blo 1794098 1795443 := bstep (se 1 (by rfl) ⟨1346582, by rfl⟩ : syracuseStep 1795443 = 2693165) B2693165
theorem B1795459 : Blo 1794098 1795459 := bstep (se 1 (by rfl) ⟨1346594, by rfl⟩ : syracuseStep 1795459 = 2693189) B2693189
theorem B3409283 : Blo 1794098 3409283 := bstep (se 1 (by rfl) ⟨2556962, by rfl⟩ : syracuseStep 3409283 = 5113925) B5113925
theorem B5752205 : Blo 1794098 5752205 := bstep (se 3 (by rfl) ⟨1078538, by rfl⟩ : syracuseStep 5752205 = 2157077) B2157077
theorem B2426257 : Blo 1794098 2426257 := bstep (se 2 (by rfl) ⟨909846, by rfl⟩ : syracuseStep 2426257 = 1819693) B1819693
theorem B4040081 : Blo 1794098 4040081 := bstep (se 2 (by rfl) ⟨1515030, by rfl⟩ : syracuseStep 4040081 = 3030061) B3030061
theorem B1795475 : Blo 1794098 1795475 := bstep (se 1 (by rfl) ⟨1346606, by rfl⟩ : syracuseStep 1795475 = 2693213) B2693213
theorem B1795491 : Blo 1794098 1795491 := bstep (se 1 (by rfl) ⟨1346618, by rfl⟩ : syracuseStep 1795491 = 2693237) B2693237
theorem B4040099 : Blo 1794098 4040099 := bstep (se 1 (by rfl) ⟨3030074, by rfl⟩ : syracuseStep 4040099 = 6060149) B6060149
theorem B1795507 : Blo 1794098 1795507 := bstep (se 1 (by rfl) ⟨1346630, by rfl⟩ : syracuseStep 1795507 = 2693261) B2693261
theorem B1795523 : Blo 1794098 1795523 := bstep (se 1 (by rfl) ⟨1346642, by rfl⟩ : syracuseStep 1795523 = 2693285) B2693285
theorem B6817229 : Blo 1794098 6817229 := bstep (se 3 (by rfl) ⟨1278230, by rfl⟩ : syracuseStep 6817229 = 2556461) B2556461
theorem B5113297 : Blo 1794098 5113297 := bstep (se 2 (by rfl) ⟨1917486, by rfl⟩ : syracuseStep 5113297 = 3834973) B3834973
theorem B1795539 : Blo 1794098 1795539 := bstep (se 1 (by rfl) ⟨1346654, by rfl⟩ : syracuseStep 1795539 = 2693309) B2693309
theorem B21013987 : Blo 1794098 21013987 := bstep (se 1 (by rfl) ⟨15760490, by rfl⟩ : syracuseStep 21013987 = 31520981) B31520981
theorem B1795555 : Blo 1794098 1795555 := bstep (se 1 (by rfl) ⟨1346666, by rfl⟩ : syracuseStep 1795555 = 2693333) B2693333
theorem B1795571 : Blo 1794098 1795571 := bstep (se 1 (by rfl) ⟨1346678, by rfl⟩ : syracuseStep 1795571 = 2693357) B2693357
theorem B1795587 : Blo 1794098 1795587 := bstep (se 1 (by rfl) ⟨1346690, by rfl⟩ : syracuseStep 1795587 = 2693381) B2693381
theorem B1795603 : Blo 1794098 1795603 := bstep (se 1 (by rfl) ⟨1346702, by rfl⟩ : syracuseStep 1795603 = 2693405) B2693405
theorem B1795619 : Blo 1794098 1795619 := bstep (se 1 (by rfl) ⟨1346714, by rfl⟩ : syracuseStep 1795619 = 2693429) B2693429
theorem B7276081 : Blo 1794098 7276081 := bstep (se 2 (by rfl) ⟨2728530, by rfl⟩ : syracuseStep 7276081 = 5457061) B5457061
theorem B1795635 : Blo 1794098 1795635 := bstep (se 1 (by rfl) ⟨1346726, by rfl⟩ : syracuseStep 1795635 = 2693453) B2693453
theorem B1795651 : Blo 1794098 1795651 := bstep (se 1 (by rfl) ⟨1346738, by rfl⟩ : syracuseStep 1795651 = 2693477) B2693477
theorem B6055505 : Blo 1794098 6055505 := bstep (se 2 (by rfl) ⟨2270814, by rfl⟩ : syracuseStep 6055505 = 4541629) B4541629
theorem B1795667 : Blo 1794098 1795667 := bstep (se 1 (by rfl) ⟨1346750, by rfl⟩ : syracuseStep 1795667 = 2693501) B2693501
theorem B1795683 : Blo 1794098 1795683 := bstep (se 1 (by rfl) ⟨1346762, by rfl⟩ : syracuseStep 1795683 = 2693525) B2693525
theorem B5457521 : Blo 1794098 5457521 := bstep (se 2 (by rfl) ⟨2046570, by rfl⟩ : syracuseStep 5457521 = 4093141) B4093141
theorem B2303603 : Blo 1794098 2303603 := bstep (se 1 (by rfl) ⟨1727702, by rfl⟩ : syracuseStep 2303603 = 3455405) B3455405
theorem B1795699 : Blo 1794098 1795699 := bstep (se 1 (by rfl) ⟨1346774, by rfl⟩ : syracuseStep 1795699 = 2693549) B2693549
theorem B1795715 : Blo 1794098 1795715 := bstep (se 1 (by rfl) ⟨1346786, by rfl⟩ : syracuseStep 1795715 = 2693573) B2693573
theorem B1795731 : Blo 1794098 1795731 := bstep (se 1 (by rfl) ⟨1346798, by rfl⟩ : syracuseStep 1795731 = 2693597) B2693597
theorem B1795747 : Blo 1794098 1795747 := bstep (se 1 (by rfl) ⟨1346810, by rfl⟩ : syracuseStep 1795747 = 2693621) B2693621
theorem B4040369 : Blo 1794098 4040369 := bstep (se 2 (by rfl) ⟨1515138, by rfl⟩ : syracuseStep 4040369 = 3030277) B3030277
theorem B1795763 : Blo 1794098 1795763 := bstep (se 1 (by rfl) ⟨1346822, by rfl⟩ : syracuseStep 1795763 = 2693645) B2693645
theorem B4040387 : Blo 1794098 4040387 := bstep (se 1 (by rfl) ⟨3030290, by rfl⟩ : syracuseStep 4040387 = 6060581) B6060581
theorem B1795779 : Blo 1794098 1795779 := bstep (se 1 (by rfl) ⟨1346834, by rfl⟩ : syracuseStep 1795779 = 2693669) B2693669
theorem B1795795 : Blo 1794098 1795795 := bstep (se 1 (by rfl) ⟨1346846, by rfl⟩ : syracuseStep 1795795 = 2693693) B2693693
theorem B1795811 : Blo 1794098 1795811 := bstep (se 1 (by rfl) ⟨1346858, by rfl⟩ : syracuseStep 1795811 = 2693717) B2693717
theorem B1795827 : Blo 1794098 1795827 := bstep (se 1 (by rfl) ⟨1346870, by rfl⟩ : syracuseStep 1795827 = 2693741) B2693741
theorem B1795843 : Blo 1794098 1795843 := bstep (se 1 (by rfl) ⟨1346882, by rfl⟩ : syracuseStep 1795843 = 2693765) B2693765
theorem B1795859 : Blo 1794098 1795859 := bstep (se 1 (by rfl) ⟨1346894, by rfl⟩ : syracuseStep 1795859 = 2693789) B2693789
theorem B2156323 : Blo 1794098 2156323 := bstep (se 1 (by rfl) ⟨1617242, by rfl⟩ : syracuseStep 2156323 = 3234485) B3234485
theorem B1795875 : Blo 1794098 1795875 := bstep (se 1 (by rfl) ⟨1346906, by rfl⟩ : syracuseStep 1795875 = 2693813) B2693813
theorem B1795891 : Blo 1794098 1795891 := bstep (se 1 (by rfl) ⟨1346918, by rfl⟩ : syracuseStep 1795891 = 2693837) B2693837
theorem B1795907 : Blo 1794098 1795907 := bstep (se 1 (by rfl) ⟨1346930, by rfl⟩ : syracuseStep 1795907 = 2693861) B2693861
theorem B1795923 : Blo 1794098 1795923 := bstep (se 1 (by rfl) ⟨1346942, by rfl⟩ : syracuseStep 1795923 = 2693885) B2693885
theorem B1795939 : Blo 1794098 1795939 := bstep (se 1 (by rfl) ⟨1346954, by rfl⟩ : syracuseStep 1795939 = 2693909) B2693909
theorem B1795955 : Blo 1794098 1795955 := bstep (se 1 (by rfl) ⟨1346966, by rfl⟩ : syracuseStep 1795955 = 2693933) B2693933
theorem B2426755 : Blo 1794098 2426755 := bstep (se 1 (by rfl) ⟨1820066, by rfl⟩ : syracuseStep 2426755 = 3640133) B3640133
theorem B1795971 : Blo 1794098 1795971 := bstep (se 1 (by rfl) ⟨1346978, by rfl⟩ : syracuseStep 1795971 = 2693957) B2693957
theorem B3835793 : Blo 1794098 3835793 := bstep (se 2 (by rfl) ⟨1438422, by rfl⟩ : syracuseStep 3835793 = 2876845) B2876845
theorem B1795987 : Blo 1794098 1795987 := bstep (se 1 (by rfl) ⟨1346990, by rfl⟩ : syracuseStep 1795987 = 2693981) B2693981
theorem B1796003 : Blo 1794098 1796003 := bstep (se 1 (by rfl) ⟨1347002, by rfl⟩ : syracuseStep 1796003 = 2694005) B2694005
theorem B3835811 : Blo 1794098 3835811 := bstep (se 1 (by rfl) ⟨2876858, by rfl⟩ : syracuseStep 3835811 = 5753717) B5753717
theorem B1796019 : Blo 1794098 1796019 := bstep (se 1 (by rfl) ⟨1347014, by rfl⟩ : syracuseStep 1796019 = 2694029) B2694029
theorem B1796035 : Blo 1794098 1796035 := bstep (se 1 (by rfl) ⟨1347026, by rfl⟩ : syracuseStep 1796035 = 2694053) B2694053
theorem B4040657 : Blo 1794098 4040657 := bstep (se 2 (by rfl) ⟨1515246, by rfl⟩ : syracuseStep 4040657 = 3030493) B3030493
theorem B1796051 : Blo 1794098 1796051 := bstep (se 1 (by rfl) ⟨1347038, by rfl⟩ : syracuseStep 1796051 = 2694077) B2694077
theorem B4040675 : Blo 1794098 4040675 := bstep (se 1 (by rfl) ⟨3030506, by rfl⟩ : syracuseStep 4040675 = 6061013) B6061013
theorem B1796067 : Blo 1794098 1796067 := bstep (se 1 (by rfl) ⟨1347050, by rfl⟩ : syracuseStep 1796067 = 2694101) B2694101
theorem B1796083 : Blo 1794098 1796083 := bstep (se 1 (by rfl) ⟨1347062, by rfl⟩ : syracuseStep 1796083 = 2694125) B2694125
theorem B2271235 : Blo 1794098 2271235 := bstep (se 1 (by rfl) ⟨1703426, by rfl⟩ : syracuseStep 2271235 = 3406853) B3406853
theorem B4851757 : Blo 1794098 4851757 := bstep (se 3 (by rfl) ⟨909704, by rfl⟩ : syracuseStep 4851757 = 1819409) B1819409
theorem B2271331 : Blo 1794098 2271331 := bstep (se 1 (by rfl) ⟨1703498, by rfl⟩ : syracuseStep 2271331 = 3406997) B3406997
theorem B6056045 : Blo 1794098 6056045 := bstep (se 3 (by rfl) ⟨1135508, by rfl⟩ : syracuseStep 6056045 = 2271017) B2271017
theorem B147449969 : Blo 1794098 147449969 := bstep (se 2 (by rfl) ⟨55293738, by rfl⟩ : syracuseStep 147449969 = 110587477) B110587477
theorem B6056099 : Blo 1794098 6056099 := bstep (se 1 (by rfl) ⟨4542074, by rfl⟩ : syracuseStep 6056099 = 9084149) B9084149
theorem B2156707 : Blo 1794098 2156707 := bstep (se 1 (by rfl) ⟨1617530, by rfl⟩ : syracuseStep 2156707 = 3235061) B3235061
theorem B6818033 : Blo 1794098 6818033 := bstep (se 2 (by rfl) ⟨2556762, by rfl⟩ : syracuseStep 6818033 = 5113525) B5113525
theorem B4040945 : Blo 1794098 4040945 := bstep (se 2 (by rfl) ⟨1515354, by rfl⟩ : syracuseStep 4040945 = 3030709) B3030709
theorem B4040963 : Blo 1794098 4040963 := bstep (se 1 (by rfl) ⟨3030722, by rfl⟩ : syracuseStep 4040963 = 6061445) B6061445
theorem B5753101 : Blo 1794098 5753101 := bstep (se 3 (by rfl) ⟨1078706, by rfl⟩ : syracuseStep 5753101 = 2157413) B2157413
theorem B19401059 : Blo 1794098 19401059 := bstep (se 1 (by rfl) ⟨14550794, by rfl⟩ : syracuseStep 19401059 = 29101589) B29101589
theorem B6056369 : Blo 1794098 6056369 := bstep (se 2 (by rfl) ⟨2271138, by rfl⟩ : syracuseStep 6056369 = 4542277) B4542277
theorem B17254883 : Blo 1794098 17254883 := bstep (se 1 (by rfl) ⟨12941162, by rfl⟩ : syracuseStep 17254883 = 25882325) B25882325
theorem B11504099 : Blo 1794098 11504099 := bstep (se 1 (by rfl) ⟨8628074, by rfl⟩ : syracuseStep 11504099 = 17256149) B17256149
theorem B4311569 : Blo 1794098 4311569 := bstep (se 2 (by rfl) ⟨1616838, by rfl⟩ : syracuseStep 4311569 = 3233677) B3233677
theorem B2271827 : Blo 1794098 2271827 := bstep (se 1 (by rfl) ⟨1703870, by rfl⟩ : syracuseStep 2271827 = 3407741) B3407741
theorem B7670477 : Blo 1794098 7670477 := bstep (se 3 (by rfl) ⟨1438214, by rfl⟩ : syracuseStep 7670477 = 2876429) B2876429
theorem B5114573 : Blo 1794098 5114573 := bstep (se 3 (by rfl) ⟨958982, by rfl⟩ : syracuseStep 5114573 = 1917965) B1917965
theorem B10226573 : Blo 1794098 10226573 := bstep (se 3 (by rfl) ⟨1917482, by rfl⟩ : syracuseStep 10226573 = 3834965) B3834965
theorem B6818701 : Blo 1794098 6818701 := bstep (se 3 (by rfl) ⟨1278506, by rfl⟩ : syracuseStep 6818701 = 2557013) B2557013
theorem B6056909 : Blo 1794098 6056909 := bstep (se 3 (by rfl) ⟨1135670, by rfl⟩ : syracuseStep 6056909 = 2271341) B2271341
theorem B6056963 : Blo 1794098 6056963 := bstep (se 1 (by rfl) ⟨4542722, by rfl⟩ : syracuseStep 6056963 = 9085445) B9085445
theorem B9702413 : Blo 1794098 9702413 := bstep (se 3 (by rfl) ⟨1819202, by rfl⟩ : syracuseStep 9702413 = 3638405) B3638405
theorem B2018371 : Blo 1794098 2018371 := bstep (se 1 (by rfl) ⟨1513778, by rfl⟩ : syracuseStep 2018371 = 3027557) B3027557
theorem B13626467 : Blo 1794098 13626467 := bstep (se 1 (by rfl) ⟨10219850, by rfl⟩ : syracuseStep 13626467 = 20439701) B20439701
theorem B5753987 : Blo 1794098 5753987 := bstep (se 1 (by rfl) ⟨4315490, by rfl⟩ : syracuseStep 5753987 = 8630981) B8630981
theorem B9702605 : Blo 1794098 9702605 := bstep (se 3 (by rfl) ⟨1819238, by rfl⟩ : syracuseStep 9702605 = 3638477) B3638477
theorem B3280081 : Blo 1794098 3280081 := bstep (se 2 (by rfl) ⟨1230030, by rfl⟩ : syracuseStep 3280081 = 2460061) B2460061
theorem B2018515 : Blo 1794098 2018515 := bstep (se 1 (by rfl) ⟨1513886, by rfl⟩ : syracuseStep 2018515 = 3027773) B3027773
theorem B10218757 : Blo 1794098 10218757 := bstep (se 4 (by rfl) ⟨958008, by rfl⟩ : syracuseStep 10218757 = 1916017) B1916017
theorem B6057233 : Blo 1794098 6057233 := bstep (se 2 (by rfl) ⟨2271462, by rfl⟩ : syracuseStep 6057233 = 4542925) B4542925
theorem B2272531 : Blo 1794098 2272531 := bstep (se 1 (by rfl) ⟨1704398, by rfl⟩ : syracuseStep 2272531 = 3408797) B3408797
theorem B5180753 : Blo 1794098 5180753 := bstep (se 2 (by rfl) ⟨1942782, by rfl⟩ : syracuseStep 5180753 = 3885565) B3885565
theorem B2018659 : Blo 1794098 2018659 := bstep (se 1 (by rfl) ⟨1513994, by rfl⟩ : syracuseStep 2018659 = 3027989) B3027989
theorem B2272627 : Blo 1794098 2272627 := bstep (se 1 (by rfl) ⟨1704470, by rfl⟩ : syracuseStep 2272627 = 3408941) B3408941
theorem B2018803 : Blo 1794098 2018803 := bstep (se 1 (by rfl) ⟨1514102, by rfl⟩ : syracuseStep 2018803 = 3028205) B3028205
theorem B5533265 : Blo 1794098 5533265 := bstep (se 2 (by rfl) ⟨2074974, by rfl⟩ : syracuseStep 5533265 = 4149949) B4149949
theorem B4542065 : Blo 1794098 4542065 := bstep (se 2 (by rfl) ⟨1703274, by rfl⟩ : syracuseStep 4542065 = 3406549) B3406549
theorem B2018947 : Blo 1794098 2018947 := bstep (se 1 (by rfl) ⟨1514210, by rfl⟩ : syracuseStep 2018947 = 3028421) B3028421
theorem B4542115 : Blo 1794098 4542115 := bstep (se 1 (by rfl) ⟨3406586, by rfl⟩ : syracuseStep 4542115 = 6813173) B6813173
theorem B6819491 : Blo 1794098 6819491 := bstep (se 1 (by rfl) ⟨5114618, by rfl⟩ : syracuseStep 6819491 = 10229237) B10229237
theorem B5828269 : Blo 1794098 5828269 := bstep (se 3 (by rfl) ⟨1092800, by rfl⟩ : syracuseStep 5828269 = 2185601) B2185601
theorem B2019091 : Blo 1794098 2019091 := bstep (se 1 (by rfl) ⟨1514318, by rfl⟩ : syracuseStep 2019091 = 3028637) B3028637
theorem B6057773 : Blo 1794098 6057773 := bstep (se 3 (by rfl) ⟨1135832, by rfl⟩ : syracuseStep 6057773 = 2271665) B2271665
theorem B4542257 : Blo 1794098 4542257 := bstep (se 2 (by rfl) ⟨1703346, by rfl⟩ : syracuseStep 4542257 = 3406693) B3406693
theorem B10227505 : Blo 1794098 10227505 := bstep (se 2 (by rfl) ⟨3835314, by rfl⟩ : syracuseStep 10227505 = 7670629) B7670629
theorem B6057827 : Blo 1794098 6057827 := bstep (se 1 (by rfl) ⟨4543370, by rfl⟩ : syracuseStep 6057827 = 9086741) B9086741
theorem B2273123 : Blo 1794098 2273123 := bstep (se 1 (by rfl) ⟨1704842, by rfl⟩ : syracuseStep 2273123 = 3409685) B3409685
theorem B2019235 : Blo 1794098 2019235 := bstep (se 1 (by rfl) ⟨1514426, by rfl⟩ : syracuseStep 2019235 = 3028853) B3028853
theorem B9089009 : Blo 1794098 9089009 := bstep (se 2 (by rfl) ⟨3408378, by rfl⟩ : syracuseStep 9089009 = 6816757) B6816757
theorem B6467597 : Blo 1794098 6467597 := bstep (se 3 (by rfl) ⟨1212674, by rfl⟩ : syracuseStep 6467597 = 2425349) B2425349
theorem B2019379 : Blo 1794098 2019379 := bstep (se 1 (by rfl) ⟨1514534, by rfl⟩ : syracuseStep 2019379 = 3029069) B3029069
theorem B7663693 : Blo 1794098 7663693 := bstep (se 3 (by rfl) ⟨1436942, by rfl⟩ : syracuseStep 7663693 = 2873885) B2873885
theorem B2691155 : Blo 1794098 2691155 := bstep (se 1 (by rfl) ⟨2018366, by rfl⟩ : syracuseStep 2691155 = 4036733) B4036733
theorem B2691185 : Blo 1794098 2691185 := bstep (se 2 (by rfl) ⟨1009194, by rfl⟩ : syracuseStep 2691185 = 2018389) B2018389
theorem B6058097 : Blo 1794098 6058097 := bstep (se 2 (by rfl) ⟨2271786, by rfl⟩ : syracuseStep 6058097 = 4543573) B4543573
theorem B2691203 : Blo 1794098 2691203 := bstep (se 1 (by rfl) ⟨2018402, by rfl⟩ : syracuseStep 2691203 = 4036805) B4036805
theorem B2691233 : Blo 1794098 2691233 := bstep (se 2 (by rfl) ⟨1009212, by rfl⟩ : syracuseStep 2691233 = 2018425) B2018425
theorem B2691251 : Blo 1794098 2691251 := bstep (se 1 (by rfl) ⟨2018438, by rfl⟩ : syracuseStep 2691251 = 4036877) B4036877
theorem B2019523 : Blo 1794098 2019523 := bstep (se 1 (by rfl) ⟨1514642, by rfl⟩ : syracuseStep 2019523 = 3029285) B3029285
theorem B2691281 : Blo 1794098 2691281 := bstep (se 2 (by rfl) ⟨1009230, by rfl⟩ : syracuseStep 2691281 = 2018461) B2018461
theorem B2691299 : Blo 1794098 2691299 := bstep (se 1 (by rfl) ⟨2018474, by rfl⟩ : syracuseStep 2691299 = 4036949) B4036949
theorem B2691329 : Blo 1794098 2691329 := bstep (se 2 (by rfl) ⟨1009248, by rfl⟩ : syracuseStep 2691329 = 2018497) B2018497
theorem B2691347 : Blo 1794098 2691347 := bstep (se 1 (by rfl) ⟨2018510, by rfl⟩ : syracuseStep 2691347 = 4037021) B4037021
theorem B2691377 : Blo 1794098 2691377 := bstep (se 2 (by rfl) ⟨1009266, by rfl⟩ : syracuseStep 2691377 = 2018533) B2018533
theorem B2691395 : Blo 1794098 2691395 := bstep (se 1 (by rfl) ⟨2018546, by rfl⟩ : syracuseStep 2691395 = 4037093) B4037093
theorem B2019667 : Blo 1794098 2019667 := bstep (se 1 (by rfl) ⟨1514750, by rfl⟩ : syracuseStep 2019667 = 3029501) B3029501
theorem B2691425 : Blo 1794098 2691425 := bstep (se 2 (by rfl) ⟨1009284, by rfl⟩ : syracuseStep 2691425 = 2018569) B2018569
theorem B4854115 : Blo 1794098 4854115 := bstep (se 1 (by rfl) ⟨3640586, by rfl⟩ : syracuseStep 4854115 = 7281173) B7281173
theorem B2691443 : Blo 1794098 2691443 := bstep (se 1 (by rfl) ⟨2018582, by rfl⟩ : syracuseStep 2691443 = 4037165) B4037165
theorem B2691473 : Blo 1794098 2691473 := bstep (se 2 (by rfl) ⟨1009302, by rfl⟩ : syracuseStep 2691473 = 2018605) B2018605
theorem B2691491 : Blo 1794098 2691491 := bstep (se 1 (by rfl) ⟨2018618, by rfl⟩ : syracuseStep 2691491 = 4037237) B4037237
theorem B2691521 : Blo 1794098 2691521 := bstep (se 2 (by rfl) ⟨1009320, by rfl⟩ : syracuseStep 2691521 = 2018641) B2018641
theorem B2691539 : Blo 1794098 2691539 := bstep (se 1 (by rfl) ⟨2018654, by rfl⟩ : syracuseStep 2691539 = 4037309) B4037309
theorem B2019811 : Blo 1794098 2019811 := bstep (se 1 (by rfl) ⟨1514858, by rfl⟩ : syracuseStep 2019811 = 3029717) B3029717
theorem B2691569 : Blo 1794098 2691569 := bstep (se 2 (by rfl) ⟨1009338, by rfl⟩ : syracuseStep 2691569 = 2018677) B2018677
theorem B2691587 : Blo 1794098 2691587 := bstep (se 1 (by rfl) ⟨2018690, by rfl⟩ : syracuseStep 2691587 = 4037381) B4037381
theorem B2691617 : Blo 1794098 2691617 := bstep (se 2 (by rfl) ⟨1009356, by rfl⟩ : syracuseStep 2691617 = 2018713) B2018713
theorem B5460529 : Blo 1794098 5460529 := bstep (se 2 (by rfl) ⟨2047698, by rfl⟩ : syracuseStep 5460529 = 4095397) B4095397
theorem B2691635 : Blo 1794098 2691635 := bstep (se 1 (by rfl) ⟨2018726, by rfl⟩ : syracuseStep 2691635 = 4037453) B4037453
theorem B2691665 : Blo 1794098 2691665 := bstep (se 2 (by rfl) ⟨1009374, by rfl⟩ : syracuseStep 2691665 = 2018749) B2018749
theorem B3453521 : Blo 1794098 3453521 := bstep (se 2 (by rfl) ⟨1295070, by rfl⟩ : syracuseStep 3453521 = 2590141) B2590141
theorem B2691683 : Blo 1794098 2691683 := bstep (se 1 (by rfl) ⟨2018762, by rfl⟩ : syracuseStep 2691683 = 4037525) B4037525
theorem B2019955 : Blo 1794098 2019955 := bstep (se 1 (by rfl) ⟨1514966, by rfl⟩ : syracuseStep 2019955 = 3029933) B3029933
theorem B2691713 : Blo 1794098 2691713 := bstep (se 2 (by rfl) ⟨1009392, by rfl⟩ : syracuseStep 2691713 = 2018785) B2018785
theorem B8622733 : Blo 1794098 8622733 := bstep (se 3 (by rfl) ⟨1616762, by rfl⟩ : syracuseStep 8622733 = 3233525) B3233525
theorem B6058637 : Blo 1794098 6058637 := bstep (se 3 (by rfl) ⟨1135994, by rfl⟩ : syracuseStep 6058637 = 2271989) B2271989
theorem B2691731 : Blo 1794098 2691731 := bstep (se 1 (by rfl) ⟨2018798, by rfl⟩ : syracuseStep 2691731 = 4037597) B4037597
theorem B1995427 : Blo 1794098 1995427 := bstep (se 1 (by rfl) ⟨1496570, by rfl⟩ : syracuseStep 1995427 = 2993141) B2993141
theorem B2691761 : Blo 1794098 2691761 := bstep (se 2 (by rfl) ⟨1009410, by rfl⟩ : syracuseStep 2691761 = 2018821) B2018821
theorem B2691779 : Blo 1794098 2691779 := bstep (se 1 (by rfl) ⟨2018834, by rfl⟩ : syracuseStep 2691779 = 4037669) B4037669
theorem B6058691 : Blo 1794098 6058691 := bstep (se 1 (by rfl) ⟨4544018, by rfl⟩ : syracuseStep 6058691 = 9088037) B9088037
theorem B3027665 : Blo 1794098 3027665 := bstep (se 2 (by rfl) ⟨1135374, by rfl⟩ : syracuseStep 3027665 = 2270749) B2270749
theorem B2691809 : Blo 1794098 2691809 := bstep (se 2 (by rfl) ⟨1009428, by rfl⟩ : syracuseStep 2691809 = 2018857) B2018857
theorem B4313827 : Blo 1794098 4313827 := bstep (se 1 (by rfl) ⟨3235370, by rfl⟩ : syracuseStep 4313827 = 6470741) B6470741
theorem B2691827 : Blo 1794098 2691827 := bstep (se 1 (by rfl) ⟨2018870, by rfl⟩ : syracuseStep 2691827 = 4037741) B4037741
theorem B2020099 : Blo 1794098 2020099 := bstep (se 1 (by rfl) ⟨1515074, by rfl⟩ : syracuseStep 2020099 = 3030149) B3030149
theorem B2691857 : Blo 1794098 2691857 := bstep (se 2 (by rfl) ⟨1009446, by rfl⟩ : syracuseStep 2691857 = 2018893) B2018893
theorem B4543249 : Blo 1794098 4543249 := bstep (se 2 (by rfl) ⟨1703718, by rfl⟩ : syracuseStep 4543249 = 3407437) B3407437
theorem B2691875 : Blo 1794098 2691875 := bstep (se 1 (by rfl) ⟨2018906, by rfl⟩ : syracuseStep 2691875 = 4037813) B4037813
theorem B2691905 : Blo 1794098 2691905 := bstep (se 2 (by rfl) ⟨1009464, by rfl⟩ : syracuseStep 2691905 = 2018929) B2018929
theorem B3027793 : Blo 1794098 3027793 := bstep (se 2 (by rfl) ⟨1135422, by rfl⟩ : syracuseStep 3027793 = 2270845) B2270845
theorem B2691923 : Blo 1794098 2691923 := bstep (se 1 (by rfl) ⟨2018942, by rfl⟩ : syracuseStep 2691923 = 4037885) B4037885
theorem B2691953 : Blo 1794098 2691953 := bstep (se 2 (by rfl) ⟨1009482, by rfl⟩ : syracuseStep 2691953 = 2018965) B2018965
theorem B3027827 : Blo 1794098 3027827 := bstep (se 1 (by rfl) ⟨2270870, by rfl⟩ : syracuseStep 3027827 = 4541741) B4541741
theorem B2691971 : Blo 1794098 2691971 := bstep (se 1 (by rfl) ⟨2018978, by rfl⟩ : syracuseStep 2691971 = 4037957) B4037957
theorem B15332237 : Blo 1794098 15332237 := bstep (se 3 (by rfl) ⟨2874794, by rfl⟩ : syracuseStep 15332237 = 5749589) B5749589
theorem B22999949 : Blo 1794098 22999949 := bstep (se 3 (by rfl) ⟨4312490, by rfl⟩ : syracuseStep 22999949 = 8624981) B8624981
theorem B2020243 : Blo 1794098 2020243 := bstep (se 1 (by rfl) ⟨1515182, by rfl⟩ : syracuseStep 2020243 = 3030365) B3030365
theorem B2692001 : Blo 1794098 2692001 := bstep (se 2 (by rfl) ⟨1009500, by rfl⟩ : syracuseStep 2692001 = 2019001) B2019001
theorem B2692019 : Blo 1794098 2692019 := bstep (se 1 (by rfl) ⟨2019014, by rfl⟩ : syracuseStep 2692019 = 4038029) B4038029
theorem B2692049 : Blo 1794098 2692049 := bstep (se 2 (by rfl) ⟨1009518, by rfl⟩ : syracuseStep 2692049 = 2019037) B2019037
theorem B6058961 : Blo 1794098 6058961 := bstep (se 2 (by rfl) ⟨2272110, by rfl⟩ : syracuseStep 6058961 = 4544221) B4544221
theorem B2692067 : Blo 1794098 2692067 := bstep (se 1 (by rfl) ⟨2019050, by rfl⟩ : syracuseStep 2692067 = 4038101) B4038101
theorem B6812657 : Blo 1794098 6812657 := bstep (se 2 (by rfl) ⟨2554746, by rfl⟩ : syracuseStep 6812657 = 5109493) B5109493
theorem B3027955 : Blo 1794098 3027955 := bstep (se 1 (by rfl) ⟨2270966, by rfl⟩ : syracuseStep 3027955 = 4541933) B4541933
theorem B2692097 : Blo 1794098 2692097 := bstep (se 2 (by rfl) ⟨1009536, by rfl⟩ : syracuseStep 2692097 = 2019073) B2019073
theorem B2626561 : Blo 1794098 2626561 := bstep (se 2 (by rfl) ⟨984960, by rfl⟩ : syracuseStep 2626561 = 1969921) B1969921
theorem B2692115 : Blo 1794098 2692115 := bstep (se 1 (by rfl) ⟨2019086, by rfl⟩ : syracuseStep 2692115 = 4038173) B4038173
theorem B4543523 : Blo 1794098 4543523 := bstep (se 1 (by rfl) ⟨3407642, by rfl⟩ : syracuseStep 4543523 = 6815285) B6815285
theorem B2020387 : Blo 1794098 2020387 := bstep (se 1 (by rfl) ⟨1515290, by rfl⟩ : syracuseStep 2020387 = 3030581) B3030581
theorem B2692145 : Blo 1794098 2692145 := bstep (se 2 (by rfl) ⟨1009554, by rfl⟩ : syracuseStep 2692145 = 2019109) B2019109
theorem B2692163 : Blo 1794098 2692163 := bstep (se 1 (by rfl) ⟨2019122, by rfl⟩ : syracuseStep 2692163 = 4038245) B4038245
theorem B2692193 : Blo 1794098 2692193 := bstep (se 2 (by rfl) ⟨1009572, by rfl⟩ : syracuseStep 2692193 = 2019145) B2019145
theorem B2692211 : Blo 1794098 2692211 := bstep (se 1 (by rfl) ⟨2019158, by rfl⟩ : syracuseStep 2692211 = 4038317) B4038317
theorem B3028097 : Blo 1794098 3028097 := bstep (se 2 (by rfl) ⟨1135536, by rfl⟩ : syracuseStep 3028097 = 2271073) B2271073
theorem B11072645 : Blo 1794098 11072645 := bstep (se 4 (by rfl) ⟨1038060, by rfl⟩ : syracuseStep 11072645 = 2076121) B2076121
theorem B2692241 : Blo 1794098 2692241 := bstep (se 2 (by rfl) ⟨1009590, by rfl⟩ : syracuseStep 2692241 = 2019181) B2019181
theorem B2692259 : Blo 1794098 2692259 := bstep (se 1 (by rfl) ⟨2019194, by rfl⟩ : syracuseStep 2692259 = 4038389) B4038389
theorem B2020531 : Blo 1794098 2020531 := bstep (se 1 (by rfl) ⟨1515398, by rfl⟩ : syracuseStep 2020531 = 3030797) B3030797
theorem B2692289 : Blo 1794098 2692289 := bstep (se 2 (by rfl) ⟨1009608, by rfl⟩ : syracuseStep 2692289 = 2019217) B2019217
theorem B10220741 : Blo 1794098 10220741 := bstep (se 4 (by rfl) ⟨958194, by rfl⟩ : syracuseStep 10220741 = 1916389) B1916389
theorem B2692307 : Blo 1794098 2692307 := bstep (se 1 (by rfl) ⟨2019230, by rfl⟩ : syracuseStep 2692307 = 4038461) B4038461
theorem B4543715 : Blo 1794098 4543715 := bstep (se 1 (by rfl) ⟨3407786, by rfl⟩ : syracuseStep 4543715 = 6815573) B6815573
theorem B10228963 : Blo 1794098 10228963 := bstep (se 1 (by rfl) ⟨7671722, by rfl⟩ : syracuseStep 10228963 = 15343445) B15343445
theorem B2692337 : Blo 1794098 2692337 := bstep (se 2 (by rfl) ⟨1009626, by rfl⟩ : syracuseStep 2692337 = 2019253) B2019253
theorem B3028225 : Blo 1794098 3028225 := bstep (se 2 (by rfl) ⟨1135584, by rfl⟩ : syracuseStep 3028225 = 2271169) B2271169
theorem B2692355 : Blo 1794098 2692355 := bstep (se 1 (by rfl) ⟨2019266, by rfl⟩ : syracuseStep 2692355 = 4038533) B4038533
theorem B2692385 : Blo 1794098 2692385 := bstep (se 2 (by rfl) ⟨1009644, by rfl⟩ : syracuseStep 2692385 = 2019289) B2019289
theorem B3028259 : Blo 1794098 3028259 := bstep (se 1 (by rfl) ⟨2271194, by rfl⟩ : syracuseStep 3028259 = 4542389) B4542389
theorem B2692403 : Blo 1794098 2692403 := bstep (se 1 (by rfl) ⟨2019302, by rfl⟩ : syracuseStep 2692403 = 4038605) B4038605
theorem B2692433 : Blo 1794098 2692433 := bstep (se 2 (by rfl) ⟨1009662, by rfl⟩ : syracuseStep 2692433 = 2019325) B2019325
theorem B2692451 : Blo 1794098 2692451 := bstep (se 1 (by rfl) ⟨2019338, by rfl⟩ : syracuseStep 2692451 = 4038677) B4038677
theorem B2692481 : Blo 1794098 2692481 := bstep (se 2 (by rfl) ⟨1009680, by rfl⟩ : syracuseStep 2692481 = 2019361) B2019361
theorem B2692499 : Blo 1794098 2692499 := bstep (se 1 (by rfl) ⟨2019374, by rfl⟩ : syracuseStep 2692499 = 4038749) B4038749
theorem B3028387 : Blo 1794098 3028387 := bstep (se 1 (by rfl) ⟨2271290, by rfl⟩ : syracuseStep 3028387 = 4542581) B4542581
theorem B9090467 : Blo 1794098 9090467 := bstep (se 1 (by rfl) ⟨6817850, by rfl⟩ : syracuseStep 9090467 = 13635701) B13635701
theorem B2692529 : Blo 1794098 2692529 := bstep (se 2 (by rfl) ⟨1009698, by rfl⟩ : syracuseStep 2692529 = 2019397) B2019397
theorem B2692547 : Blo 1794098 2692547 := bstep (se 1 (by rfl) ⟨2019410, by rfl⟩ : syracuseStep 2692547 = 4038821) B4038821
theorem B2692577 : Blo 1794098 2692577 := bstep (se 2 (by rfl) ⟨1009716, by rfl⟩ : syracuseStep 2692577 = 2019433) B2019433
theorem B6059501 : Blo 1794098 6059501 := bstep (se 3 (by rfl) ⟨1136156, by rfl⟩ : syracuseStep 6059501 = 2272313) B2272313
theorem B2692595 : Blo 1794098 2692595 := bstep (se 1 (by rfl) ⟨2019446, by rfl⟩ : syracuseStep 2692595 = 4038893) B4038893
theorem B2692625 : Blo 1794098 2692625 := bstep (se 2 (by rfl) ⟨1009734, by rfl⟩ : syracuseStep 2692625 = 2019469) B2019469
theorem B2692643 : Blo 1794098 2692643 := bstep (se 1 (by rfl) ⟨2019482, by rfl⟩ : syracuseStep 2692643 = 4038965) B4038965
theorem B6059555 : Blo 1794098 6059555 := bstep (se 1 (by rfl) ⟨4544666, by rfl⟩ : syracuseStep 6059555 = 9089333) B9089333
theorem B3028529 : Blo 1794098 3028529 := bstep (se 2 (by rfl) ⟨1135698, by rfl⟩ : syracuseStep 3028529 = 2271397) B2271397
theorem B2692673 : Blo 1794098 2692673 := bstep (se 2 (by rfl) ⟨1009752, by rfl⟩ : syracuseStep 2692673 = 2019505) B2019505
theorem B2692691 : Blo 1794098 2692691 := bstep (se 1 (by rfl) ⟨2019518, by rfl⟩ : syracuseStep 2692691 = 4039037) B4039037
theorem B2692721 : Blo 1794098 2692721 := bstep (se 2 (by rfl) ⟨1009770, by rfl⟩ : syracuseStep 2692721 = 2019541) B2019541
theorem B12285553 : Blo 1794098 12285553 := bstep (se 2 (by rfl) ⟨4607082, by rfl⟩ : syracuseStep 12285553 = 9214165) B9214165
theorem B2692739 : Blo 1794098 2692739 := bstep (se 1 (by rfl) ⟨2019554, by rfl⟩ : syracuseStep 2692739 = 4039109) B4039109
theorem B2692769 : Blo 1794098 2692769 := bstep (se 2 (by rfl) ⟨1009788, by rfl⟩ : syracuseStep 2692769 = 2019577) B2019577
theorem B5109425 : Blo 1794098 5109425 := bstep (se 2 (by rfl) ⟨1916034, by rfl⟩ : syracuseStep 5109425 = 3832069) B3832069
theorem B3028657 : Blo 1794098 3028657 := bstep (se 2 (by rfl) ⟨1135746, by rfl⟩ : syracuseStep 3028657 = 2271493) B2271493
theorem B2692787 : Blo 1794098 2692787 := bstep (se 1 (by rfl) ⟨2019590, by rfl⟩ : syracuseStep 2692787 = 4039181) B4039181
theorem B20715205 : Blo 1794098 20715205 := bstep (se 4 (by rfl) ⟨1942050, by rfl⟩ : syracuseStep 20715205 = 3884101) B3884101
theorem B2692817 : Blo 1794098 2692817 := bstep (se 2 (by rfl) ⟨1009806, by rfl⟩ : syracuseStep 2692817 = 2019613) B2019613
theorem B3028691 : Blo 1794098 3028691 := bstep (se 1 (by rfl) ⟨2271518, by rfl⟩ : syracuseStep 3028691 = 4543037) B4543037
theorem B2692835 : Blo 1794098 2692835 := bstep (se 1 (by rfl) ⟨2019626, by rfl⟩ : syracuseStep 2692835 = 4039253) B4039253
theorem B2692865 : Blo 1794098 2692865 := bstep (se 2 (by rfl) ⟨1009824, by rfl⟩ : syracuseStep 2692865 = 2019649) B2019649
theorem B2692883 : Blo 1794098 2692883 := bstep (se 1 (by rfl) ⟨2019662, by rfl⟩ : syracuseStep 2692883 = 4039325) B4039325
theorem B2692913 : Blo 1794098 2692913 := bstep (se 2 (by rfl) ⟨1009842, by rfl⟩ : syracuseStep 2692913 = 2019685) B2019685
theorem B6059825 : Blo 1794098 6059825 := bstep (se 2 (by rfl) ⟨2272434, by rfl⟩ : syracuseStep 6059825 = 4544869) B4544869
theorem B2692931 : Blo 1794098 2692931 := bstep (se 1 (by rfl) ⟨2019698, by rfl⟩ : syracuseStep 2692931 = 4039397) B4039397
theorem B6739789 : Blo 1794098 6739789 := bstep (se 3 (by rfl) ⟨1263710, by rfl⟩ : syracuseStep 6739789 = 2527421) B2527421
theorem B3028819 : Blo 1794098 3028819 := bstep (se 1 (by rfl) ⟨2271614, by rfl⟩ : syracuseStep 3028819 = 4543229) B4543229
theorem B2692961 : Blo 1794098 2692961 := bstep (se 2 (by rfl) ⟨1009860, by rfl⟩ : syracuseStep 2692961 = 2019721) B2019721
theorem B9836387 : Blo 1794098 9836387 := bstep (se 1 (by rfl) ⟨7377290, by rfl⟩ : syracuseStep 9836387 = 14754581) B14754581
theorem B2692979 : Blo 1794098 2692979 := bstep (se 1 (by rfl) ⟨2019734, by rfl⟩ : syracuseStep 2692979 = 4039469) B4039469
theorem B2693009 : Blo 1794098 2693009 := bstep (se 2 (by rfl) ⟨1009878, by rfl⟩ : syracuseStep 2693009 = 2019757) B2019757
theorem B2693027 : Blo 1794098 2693027 := bstep (se 1 (by rfl) ⟨2019770, by rfl⟩ : syracuseStep 2693027 = 4039541) B4039541
theorem B22992821 : Blo 1794098 22992821 := bstep (se 5 (by rfl) ⟨1077788, by rfl⟩ : syracuseStep 22992821 = 2155577) B2155577
theorem B2693057 : Blo 1794098 2693057 := bstep (se 2 (by rfl) ⟨1009896, by rfl⟩ : syracuseStep 2693057 = 2019793) B2019793
theorem B6141901 : Blo 1794098 6141901 := bstep (se 3 (by rfl) ⟨1151606, by rfl⟩ : syracuseStep 6141901 = 2303213) B2303213
theorem B3831761 : Blo 1794098 3831761 := bstep (se 2 (by rfl) ⟨1436910, by rfl⟩ : syracuseStep 3831761 = 2873821) B2873821
theorem B2693075 : Blo 1794098 2693075 := bstep (se 1 (by rfl) ⟨2019806, by rfl⟩ : syracuseStep 2693075 = 4039613) B4039613
theorem B3028961 : Blo 1794098 3028961 := bstep (se 2 (by rfl) ⟨1135860, by rfl⟩ : syracuseStep 3028961 = 2271721) B2271721
theorem B3831779 : Blo 1794098 3831779 := bstep (se 1 (by rfl) ⟨2873834, by rfl⟩ : syracuseStep 3831779 = 5747669) B5747669
theorem B2693105 : Blo 1794098 2693105 := bstep (se 2 (by rfl) ⟨1009914, by rfl⟩ : syracuseStep 2693105 = 2019829) B2019829
theorem B2693123 : Blo 1794098 2693123 := bstep (se 1 (by rfl) ⟨2019842, by rfl⟩ : syracuseStep 2693123 = 4039685) B4039685
theorem B13637645 : Blo 1794098 13637645 := bstep (se 3 (by rfl) ⟨2557058, by rfl⟩ : syracuseStep 13637645 = 5114117) B5114117
theorem B4315153 : Blo 1794098 4315153 := bstep (se 2 (by rfl) ⟨1618182, by rfl⟩ : syracuseStep 4315153 = 3236365) B3236365
theorem B3233827 : Blo 1794098 3233827 := bstep (se 1 (by rfl) ⟨2425370, by rfl⟩ : syracuseStep 3233827 = 4850741) B4850741
theorem B2693153 : Blo 1794098 2693153 := bstep (se 2 (by rfl) ⟨1009932, by rfl⟩ : syracuseStep 2693153 = 2019865) B2019865
theorem B2693171 : Blo 1794098 2693171 := bstep (se 1 (by rfl) ⟨2019878, by rfl⟩ : syracuseStep 2693171 = 4039757) B4039757
theorem B2693201 : Blo 1794098 2693201 := bstep (se 2 (by rfl) ⟨1009950, by rfl⟩ : syracuseStep 2693201 = 2019901) B2019901
theorem B3029089 : Blo 1794098 3029089 := bstep (se 2 (by rfl) ⟨1135908, by rfl⟩ : syracuseStep 3029089 = 2271817) B2271817
theorem B2693219 : Blo 1794098 2693219 := bstep (se 1 (by rfl) ⟨2019914, by rfl⟩ : syracuseStep 2693219 = 4039829) B4039829
theorem B17258609 : Blo 1794098 17258609 := bstep (se 2 (by rfl) ⟨6471978, by rfl⟩ : syracuseStep 17258609 = 12943957) B12943957
theorem B2693249 : Blo 1794098 2693249 := bstep (se 2 (by rfl) ⟨1009968, by rfl⟩ : syracuseStep 2693249 = 2019937) B2019937
theorem B3029123 : Blo 1794098 3029123 := bstep (se 1 (by rfl) ⟨2271842, by rfl⟩ : syracuseStep 3029123 = 4543685) B4543685
theorem B4544657 : Blo 1794098 4544657 := bstep (se 2 (by rfl) ⟨1704246, by rfl⟩ : syracuseStep 4544657 = 3408493) B3408493
theorem B2693267 : Blo 1794098 2693267 := bstep (se 1 (by rfl) ⟨2019950, by rfl⟩ : syracuseStep 2693267 = 4039901) B4039901
theorem B2693297 : Blo 1794098 2693297 := bstep (se 2 (by rfl) ⟨1009986, by rfl⟩ : syracuseStep 2693297 = 2019973) B2019973
theorem B4544707 : Blo 1794098 4544707 := bstep (se 1 (by rfl) ⟨3408530, by rfl⟩ : syracuseStep 4544707 = 6817061) B6817061
theorem B2693315 : Blo 1794098 2693315 := bstep (se 1 (by rfl) ⟨2019986, by rfl⟩ : syracuseStep 2693315 = 4039973) B4039973
theorem B9091277 : Blo 1794098 9091277 := bstep (se 3 (by rfl) ⟨1704614, by rfl⟩ : syracuseStep 9091277 = 3409229) B3409229
theorem B2693345 : Blo 1794098 2693345 := bstep (se 2 (by rfl) ⟨1010004, by rfl⟩ : syracuseStep 2693345 = 2020009) B2020009
theorem B2693363 : Blo 1794098 2693363 := bstep (se 1 (by rfl) ⟨2020022, by rfl⟩ : syracuseStep 2693363 = 4040045) B4040045
theorem B3029251 : Blo 1794098 3029251 := bstep (se 1 (by rfl) ⟨2271938, by rfl⟩ : syracuseStep 3029251 = 4543877) B4543877
theorem B2693393 : Blo 1794098 2693393 := bstep (se 2 (by rfl) ⟨1010022, by rfl⟩ : syracuseStep 2693393 = 2020045) B2020045
theorem B2693411 : Blo 1794098 2693411 := bstep (se 1 (by rfl) ⟨2020058, by rfl⟩ : syracuseStep 2693411 = 4040117) B4040117
theorem B4036913 : Blo 1794098 4036913 := bstep (se 2 (by rfl) ⟨1513842, by rfl⟩ : syracuseStep 4036913 = 3027685) B3027685
theorem B2693441 : Blo 1794098 2693441 := bstep (se 2 (by rfl) ⟨1010040, by rfl⟩ : syracuseStep 2693441 = 2020081) B2020081
theorem B4036931 : Blo 1794098 4036931 := bstep (se 1 (by rfl) ⟨3027698, by rfl⟩ : syracuseStep 4036931 = 6055397) B6055397
theorem B6060365 : Blo 1794098 6060365 := bstep (se 3 (by rfl) ⟨1136318, by rfl⟩ : syracuseStep 6060365 = 2272637) B2272637
theorem B4544849 : Blo 1794098 4544849 := bstep (se 2 (by rfl) ⟨1704318, by rfl⟩ : syracuseStep 4544849 = 3408637) B3408637
theorem B2693459 : Blo 1794098 2693459 := bstep (se 1 (by rfl) ⟨2020094, by rfl⟩ : syracuseStep 2693459 = 4040189) B4040189
theorem B2693489 : Blo 1794098 2693489 := bstep (se 2 (by rfl) ⟨1010058, by rfl⟩ : syracuseStep 2693489 = 2020117) B2020117
theorem B2693507 : Blo 1794098 2693507 := bstep (se 1 (by rfl) ⟨2020130, by rfl⟩ : syracuseStep 2693507 = 4040261) B4040261
theorem B6060419 : Blo 1794098 6060419 := bstep (se 1 (by rfl) ⟨4545314, by rfl⟩ : syracuseStep 6060419 = 9090629) B9090629
theorem B3029393 : Blo 1794098 3029393 := bstep (se 2 (by rfl) ⟨1136022, by rfl⟩ : syracuseStep 3029393 = 2272045) B2272045
theorem B2693537 : Blo 1794098 2693537 := bstep (se 2 (by rfl) ⟨1010076, by rfl⟩ : syracuseStep 2693537 = 2020153) B2020153
theorem B6814115 : Blo 1794098 6814115 := bstep (se 1 (by rfl) ⟨5110586, by rfl⟩ : syracuseStep 6814115 = 10221173) B10221173
theorem B2693555 : Blo 1794098 2693555 := bstep (se 1 (by rfl) ⟨2020166, by rfl⟩ : syracuseStep 2693555 = 4040333) B4040333
theorem B2693585 : Blo 1794098 2693585 := bstep (se 2 (by rfl) ⟨1010094, by rfl⟩ : syracuseStep 2693585 = 2020189) B2020189
theorem B2693603 : Blo 1794098 2693603 := bstep (se 1 (by rfl) ⟨2020202, by rfl⟩ : syracuseStep 2693603 = 4040405) B4040405
theorem B2693633 : Blo 1794098 2693633 := bstep (se 2 (by rfl) ⟨1010112, by rfl⟩ : syracuseStep 2693633 = 2020225) B2020225
theorem B3029521 : Blo 1794098 3029521 := bstep (se 2 (by rfl) ⟨1136070, by rfl⟩ : syracuseStep 3029521 = 2272141) B2272141
theorem B2693651 : Blo 1794098 2693651 := bstep (se 1 (by rfl) ⟨2020238, by rfl⟩ : syracuseStep 2693651 = 4040477) B4040477
theorem B2693681 : Blo 1794098 2693681 := bstep (se 2 (by rfl) ⟨1010130, by rfl⟩ : syracuseStep 2693681 = 2020261) B2020261
theorem B3029555 : Blo 1794098 3029555 := bstep (se 1 (by rfl) ⟨2272166, by rfl⟩ : syracuseStep 3029555 = 4544333) B4544333
theorem B2873923 : Blo 1794098 2873923 := bstep (se 1 (by rfl) ⟨2155442, by rfl⟩ : syracuseStep 2873923 = 4310885) B4310885
theorem B2693699 : Blo 1794098 2693699 := bstep (se 1 (by rfl) ⟨2020274, by rfl⟩ : syracuseStep 2693699 = 4040549) B4040549
theorem B4037201 : Blo 1794098 4037201 := bstep (se 2 (by rfl) ⟨1513950, by rfl⟩ : syracuseStep 4037201 = 3027901) B3027901
theorem B2693729 : Blo 1794098 2693729 := bstep (se 2 (by rfl) ⟨1010148, by rfl⟩ : syracuseStep 2693729 = 2020297) B2020297
theorem B4037219 : Blo 1794098 4037219 := bstep (se 1 (by rfl) ⟨3027914, by rfl⟩ : syracuseStep 4037219 = 6055829) B6055829
theorem B5110381 : Blo 1794098 5110381 := bstep (se 3 (by rfl) ⟨958196, by rfl⟩ : syracuseStep 5110381 = 1916393) B1916393
theorem B2873969 : Blo 1794098 2873969 := bstep (se 2 (by rfl) ⟨1077738, by rfl⟩ : syracuseStep 2873969 = 2155477) B2155477
theorem B2693747 : Blo 1794098 2693747 := bstep (se 1 (by rfl) ⟨2020310, by rfl⟩ : syracuseStep 2693747 = 4040621) B4040621
theorem B6060689 : Blo 1794098 6060689 := bstep (se 2 (by rfl) ⟨2272758, by rfl⟩ : syracuseStep 6060689 = 4545517) B4545517
theorem B2693777 : Blo 1794098 2693777 := bstep (se 2 (by rfl) ⟨1010166, by rfl⟩ : syracuseStep 2693777 = 2020333) B2020333
theorem B2693795 : Blo 1794098 2693795 := bstep (se 1 (by rfl) ⟨2020346, by rfl⟩ : syracuseStep 2693795 = 4040693) B4040693
theorem B6650531 : Blo 1794098 6650531 := bstep (se 1 (by rfl) ⟨4987898, by rfl⟩ : syracuseStep 6650531 = 9975797) B9975797
theorem B3111601 : Blo 1794098 3111601 := bstep (se 2 (by rfl) ⟨1166850, by rfl⟩ : syracuseStep 3111601 = 2333701) B2333701
theorem B3029683 : Blo 1794098 3029683 := bstep (se 1 (by rfl) ⟨2272262, by rfl⟩ : syracuseStep 3029683 = 4544525) B4544525
theorem B2693825 : Blo 1794098 2693825 := bstep (se 2 (by rfl) ⟨1010184, by rfl⟩ : syracuseStep 2693825 = 2020369) B2020369
theorem B2693843 : Blo 1794098 2693843 := bstep (se 1 (by rfl) ⟨2020382, by rfl⟩ : syracuseStep 2693843 = 4040765) B4040765
theorem B2693873 : Blo 1794098 2693873 := bstep (se 2 (by rfl) ⟨1010202, by rfl⟩ : syracuseStep 2693873 = 2020405) B2020405
theorem B2693891 : Blo 1794098 2693891 := bstep (se 1 (by rfl) ⟨2020418, by rfl⟩ : syracuseStep 2693891 = 4040837) B4040837
theorem B2693921 : Blo 1794098 2693921 := bstep (se 2 (by rfl) ⟨1010220, by rfl⟩ : syracuseStep 2693921 = 2020441) B2020441
theorem B2693939 : Blo 1794098 2693939 := bstep (se 1 (by rfl) ⟨2020454, by rfl⟩ : syracuseStep 2693939 = 4040909) B4040909
theorem B3029825 : Blo 1794098 3029825 := bstep (se 2 (by rfl) ⟨1136184, by rfl⟩ : syracuseStep 3029825 = 2272369) B2272369
theorem B5110609 : Blo 1794098 5110609 := bstep (se 2 (by rfl) ⟨1916478, by rfl⟩ : syracuseStep 5110609 = 3832957) B3832957
theorem B2693969 : Blo 1794098 2693969 := bstep (se 2 (by rfl) ⟨1010238, by rfl⟩ : syracuseStep 2693969 = 2020477) B2020477
theorem B2693987 : Blo 1794098 2693987 := bstep (se 1 (by rfl) ⟨2020490, by rfl⟩ : syracuseStep 2693987 = 4040981) B4040981
theorem B4037489 : Blo 1794098 4037489 := bstep (se 2 (by rfl) ⟨1514058, by rfl⟩ : syracuseStep 4037489 = 3028117) B3028117
theorem B2694017 : Blo 1794098 2694017 := bstep (se 2 (by rfl) ⟨1010256, by rfl⟩ : syracuseStep 2694017 = 2020513) B2020513
theorem B4037507 : Blo 1794098 4037507 := bstep (se 1 (by rfl) ⟨3028130, by rfl⟩ : syracuseStep 4037507 = 6056261) B6056261
theorem B2694035 : Blo 1794098 2694035 := bstep (se 1 (by rfl) ⟨2020526, by rfl⟩ : syracuseStep 2694035 = 4041053) B4041053
theorem B9083825 : Blo 1794098 9083825 := bstep (se 2 (by rfl) ⟨3406434, by rfl⟩ : syracuseStep 9083825 = 6812869) B6812869
theorem B3406769 : Blo 1794098 3406769 := bstep (se 2 (by rfl) ⟨1277538, by rfl⟩ : syracuseStep 3406769 = 2555077) B2555077
theorem B2694065 : Blo 1794098 2694065 := bstep (se 2 (by rfl) ⟨1010274, by rfl⟩ : syracuseStep 2694065 = 2020549) B2020549
theorem B3029953 : Blo 1794098 3029953 := bstep (se 2 (by rfl) ⟨1136232, by rfl⟩ : syracuseStep 3029953 = 2272465) B2272465
theorem B2694083 : Blo 1794098 2694083 := bstep (se 1 (by rfl) ⟨2020562, by rfl⟩ : syracuseStep 2694083 = 4041125) B4041125
theorem B2554849 : Blo 1794098 2554849 := bstep (se 2 (by rfl) ⟨958068, by rfl⟩ : syracuseStep 2554849 = 1916137) B1916137
theorem B3029987 : Blo 1794098 3029987 := bstep (se 1 (by rfl) ⟨2272490, by rfl⟩ : syracuseStep 3029987 = 4544981) B4544981
theorem B2694113 : Blo 1794098 2694113 := bstep (se 2 (by rfl) ⟨1010292, by rfl⟩ : syracuseStep 2694113 = 2020585) B2020585
theorem B5110769 : Blo 1794098 5110769 := bstep (se 2 (by rfl) ⟨1916538, by rfl⟩ : syracuseStep 5110769 = 3833077) B3833077
theorem B2694131 : Blo 1794098 2694131 := bstep (se 1 (by rfl) ⟨2020598, by rfl⟩ : syracuseStep 2694131 = 4041197) B4041197
theorem B11500613 : Blo 1794098 11500613 := bstep (se 4 (by rfl) ⟨1078182, by rfl⟩ : syracuseStep 11500613 = 2156365) B2156365
theorem B5110883 : Blo 1794098 5110883 := bstep (se 1 (by rfl) ⟨3833162, by rfl⟩ : syracuseStep 5110883 = 7666325) B7666325
theorem B3030115 : Blo 1794098 3030115 := bstep (se 1 (by rfl) ⟨2272586, by rfl⟩ : syracuseStep 3030115 = 4545173) B4545173
theorem B4037777 : Blo 1794098 4037777 := bstep (se 2 (by rfl) ⟨1514166, by rfl⟩ : syracuseStep 4037777 = 3028333) B3028333
theorem B4037795 : Blo 1794098 4037795 := bstep (se 1 (by rfl) ⟨3028346, by rfl⟩ : syracuseStep 4037795 = 6056693) B6056693
theorem B6061229 : Blo 1794098 6061229 := bstep (se 3 (by rfl) ⟨1136480, by rfl⟩ : syracuseStep 6061229 = 2272961) B2272961
theorem B3071171 : Blo 1794098 3071171 := bstep (se 1 (by rfl) ⟨2303378, by rfl⟩ : syracuseStep 3071171 = 4606757) B4606757
theorem B20438243 : Blo 1794098 20438243 := bstep (se 1 (by rfl) ⟨15328682, by rfl⟩ : syracuseStep 20438243 = 30657365) B30657365
theorem B6061283 : Blo 1794098 6061283 := bstep (se 1 (by rfl) ⟨4545962, by rfl⟩ : syracuseStep 6061283 = 9091925) B9091925
theorem B3030257 : Blo 1794098 3030257 := bstep (se 2 (by rfl) ⟨1136346, by rfl⟩ : syracuseStep 3030257 = 2272693) B2272693
theorem B4545841 : Blo 1794098 4545841 := bstep (se 2 (by rfl) ⟨1704690, by rfl⟩ : syracuseStep 4545841 = 3409381) B3409381
theorem B6561101 : Blo 1794098 6561101 := bstep (se 3 (by rfl) ⟨1230206, by rfl⟩ : syracuseStep 6561101 = 2460413) B2460413
theorem B5750129 : Blo 1794098 5750129 := bstep (se 2 (by rfl) ⟨2156298, by rfl⟩ : syracuseStep 5750129 = 4312597) B4312597
theorem B3030385 : Blo 1794098 3030385 := bstep (se 2 (by rfl) ⟨1136394, by rfl⟩ : syracuseStep 3030385 = 2272789) B2272789
theorem B34487693 : Blo 1794098 34487693 := bstep (se 3 (by rfl) ⟨6466442, by rfl⟩ : syracuseStep 34487693 = 12932885) B12932885
theorem B6815117 : Blo 1794098 6815117 := bstep (se 3 (by rfl) ⟨1277834, by rfl⟩ : syracuseStep 6815117 = 2555669) B2555669
theorem B3030419 : Blo 1794098 3030419 := bstep (se 1 (by rfl) ⟨2272814, by rfl⟩ : syracuseStep 3030419 = 4545629) B4545629
theorem B4038065 : Blo 1794098 4038065 := bstep (se 2 (by rfl) ⟨1514274, by rfl⟩ : syracuseStep 4038065 = 3028549) B3028549
theorem B4038083 : Blo 1794098 4038083 := bstep (se 1 (by rfl) ⟨3028562, by rfl⟩ : syracuseStep 4038083 = 6057125) B6057125
theorem B46005731 : Blo 1794098 46005731 := bstep (se 1 (by rfl) ⟨34504298, by rfl⟩ : syracuseStep 46005731 = 69008597) B69008597
theorem B6061553 : Blo 1794098 6061553 := bstep (se 2 (by rfl) ⟨2273082, by rfl⟩ : syracuseStep 6061553 = 4546165) B4546165
theorem B3030547 : Blo 1794098 3030547 := bstep (se 1 (by rfl) ⟨2272910, by rfl⟩ : syracuseStep 3030547 = 4545821) B4545821
theorem B4546115 : Blo 1794098 4546115 := bstep (se 1 (by rfl) ⟨3409586, by rfl⟩ : syracuseStep 4546115 = 6819173) B6819173
theorem B3030689 : Blo 1794098 3030689 := bstep (se 2 (by rfl) ⟨1136508, by rfl⟩ : syracuseStep 3030689 = 2273017) B2273017
theorem B2555555 : Blo 1794098 2555555 := bstep (se 1 (by rfl) ⟨1916666, by rfl⟩ : syracuseStep 2555555 = 3833333) B3833333
theorem B4038353 : Blo 1794098 4038353 := bstep (se 2 (by rfl) ⟨1514382, by rfl⟩ : syracuseStep 4038353 = 3028765) B3028765
theorem B4038371 : Blo 1794098 4038371 := bstep (se 1 (by rfl) ⟨3028778, by rfl⟩ : syracuseStep 4038371 = 6057557) B6057557
theorem B4431601 : Blo 1794098 4431601 := bstep (se 2 (by rfl) ⟨1661850, by rfl⟩ : syracuseStep 4431601 = 3323701) B3323701
theorem B4546307 : Blo 1794098 4546307 := bstep (se 1 (by rfl) ⟨3409730, by rfl⟩ : syracuseStep 4546307 = 6819461) B6819461
theorem B3030817 : Blo 1794098 3030817 := bstep (se 2 (by rfl) ⟨1136556, by rfl⟩ : syracuseStep 3030817 = 2273113) B2273113
theorem B3407665 : Blo 1794098 3407665 := bstep (se 2 (by rfl) ⟨1277874, by rfl⟩ : syracuseStep 3407665 = 2555749) B2555749
theorem B3030851 : Blo 1794098 3030851 := bstep (se 1 (by rfl) ⟨2273138, by rfl⟩ : syracuseStep 3030851 = 4546277) B4546277
theorem B1916803 : Blo 1794098 1916803 := bstep (se 1 (by rfl) ⟨1437602, by rfl⟩ : syracuseStep 1916803 = 2875205) B2875205
theorem B3833777 : Blo 1794098 3833777 := bstep (se 2 (by rfl) ⟨1437666, by rfl⟩ : syracuseStep 3833777 = 2875333) B2875333
theorem B21831605 : Blo 1794098 21831605 := bstep (se 5 (by rfl) ⟨1023356, by rfl⟩ : syracuseStep 21831605 = 2046713) B2046713
theorem B3407825 : Blo 1794098 3407825 := bstep (se 2 (by rfl) ⟨1277934, by rfl⟩ : syracuseStep 3407825 = 2555869) B2555869
theorem B4038641 : Blo 1794098 4038641 := bstep (se 2 (by rfl) ⟨1514490, by rfl⟩ : syracuseStep 4038641 = 3028981) B3028981
theorem B3407923 : Blo 1794098 3407923 := bstep (se 1 (by rfl) ⟨2555942, by rfl⟩ : syracuseStep 3407923 = 5111885) B5111885
theorem B1794103 : Blo 1794098 1794103 := bstep (se 1 (by rfl) ⟨1345577, by rfl⟩ : syracuseStep 1794103 = 2691155) B2691155
theorem B1916983 : Blo 1794098 1916983 := bstep (se 1 (by rfl) ⟨1437737, by rfl⟩ : syracuseStep 1916983 = 2875475) B2875475
theorem B1794123 : Blo 1794098 1794123 := bstep (se 1 (by rfl) ⟨1345592, by rfl⟩ : syracuseStep 1794123 = 2691185) B2691185
theorem B4038731 : Blo 1794098 4038731 := bstep (se 1 (by rfl) ⟨3029048, by rfl⟩ : syracuseStep 4038731 = 6058097) B6058097
theorem B1794135 : Blo 1794098 1794135 := bstep (se 1 (by rfl) ⟨1345601, by rfl⟩ : syracuseStep 1794135 = 2691203) B2691203
theorem B1794155 : Blo 1794098 1794155 := bstep (se 1 (by rfl) ⟨1345616, by rfl⟩ : syracuseStep 1794155 = 2691233) B2691233
theorem B1794167 : Blo 1794098 1794167 := bstep (se 1 (by rfl) ⟨1345625, by rfl⟩ : syracuseStep 1794167 = 2691251) B2691251
theorem B4038785 : Blo 1794098 4038785 := bstep (se 2 (by rfl) ⟨1514544, by rfl⟩ : syracuseStep 4038785 = 3029089) B3029089
theorem B1794187 : Blo 1794098 1794187 := bstep (se 1 (by rfl) ⟨1345640, by rfl⟩ : syracuseStep 1794187 = 2691281) B2691281
theorem B1794199 : Blo 1794098 1794199 := bstep (se 1 (by rfl) ⟨1345649, by rfl⟩ : syracuseStep 1794199 = 2691299) B2691299
theorem B1794219 : Blo 1794098 1794219 := bstep (se 1 (by rfl) ⟨1345664, by rfl⟩ : syracuseStep 1794219 = 2691329) B2691329
theorem B1794231 : Blo 1794098 1794231 := bstep (se 1 (by rfl) ⟨1345673, by rfl⟩ : syracuseStep 1794231 = 2691347) B2691347
theorem B1794251 : Blo 1794098 1794251 := bstep (se 1 (by rfl) ⟨1345688, by rfl⟩ : syracuseStep 1794251 = 2691377) B2691377
theorem B5112011 : Blo 1794098 5112011 := bstep (se 1 (by rfl) ⟨3834008, by rfl⟩ : syracuseStep 5112011 = 7668017) B7668017
theorem B1794263 : Blo 1794098 1794263 := bstep (se 1 (by rfl) ⟨1345697, by rfl⟩ : syracuseStep 1794263 = 2691395) B2691395
theorem B2875609 : Blo 1794098 2875609 := bstep (se 2 (by rfl) ⟨1078353, by rfl⟩ : syracuseStep 2875609 = 2156707) B2156707
theorem B1794283 : Blo 1794098 1794283 := bstep (se 1 (by rfl) ⟨1345712, by rfl⟩ : syracuseStep 1794283 = 2691425) B2691425
theorem B1794295 : Blo 1794098 1794295 := bstep (se 1 (by rfl) ⟨1345721, by rfl⟩ : syracuseStep 1794295 = 2691443) B2691443
theorem B3637505 : Blo 1794098 3637505 := bstep (se 2 (by rfl) ⟨1364064, by rfl⟩ : syracuseStep 3637505 = 2728129) B2728129
theorem B1794315 : Blo 1794098 1794315 := bstep (se 1 (by rfl) ⟨1345736, by rfl⟩ : syracuseStep 1794315 = 2691473) B2691473
theorem B1794327 : Blo 1794098 1794327 := bstep (se 1 (by rfl) ⟨1345745, by rfl⟩ : syracuseStep 1794327 = 2691491) B2691491
theorem B3408151 : Blo 1794098 3408151 := bstep (se 1 (by rfl) ⟨2556113, by rfl⟩ : syracuseStep 3408151 = 5112227) B5112227
theorem B1794347 : Blo 1794098 1794347 := bstep (se 1 (by rfl) ⟨1345760, by rfl⟩ : syracuseStep 1794347 = 2691521) B2691521
theorem B1794359 : Blo 1794098 1794359 := bstep (se 1 (by rfl) ⟨1345769, by rfl⟩ : syracuseStep 1794359 = 2691539) B2691539
theorem B1794379 : Blo 1794098 1794379 := bstep (se 1 (by rfl) ⟨1345784, by rfl⟩ : syracuseStep 1794379 = 2691569) B2691569
theorem B1794391 : Blo 1794098 1794391 := bstep (se 1 (by rfl) ⟨1345793, by rfl⟩ : syracuseStep 1794391 = 2691587) B2691587
theorem B4039001 : Blo 1794098 4039001 := bstep (se 2 (by rfl) ⟨1514625, by rfl⟩ : syracuseStep 4039001 = 3029251) B3029251
theorem B6816089 : Blo 1794098 6816089 := bstep (se 2 (by rfl) ⟨2556033, by rfl⟩ : syracuseStep 6816089 = 5112067) B5112067
theorem B15327589 : Blo 1794098 15327589 := bstep (se 4 (by rfl) ⟨1436961, by rfl⟩ : syracuseStep 15327589 = 2873923) B2873923
theorem B1794411 : Blo 1794098 1794411 := bstep (se 1 (by rfl) ⟨1345808, by rfl⟩ : syracuseStep 1794411 = 2691617) B2691617
theorem B1794423 : Blo 1794098 1794423 := bstep (se 1 (by rfl) ⟨1345817, by rfl⟩ : syracuseStep 1794423 = 2691635) B2691635
theorem B3408257 : Blo 1794098 3408257 := bstep (se 2 (by rfl) ⟨1278096, by rfl⟩ : syracuseStep 3408257 = 2556193) B2556193
theorem B1794443 : Blo 1794098 1794443 := bstep (se 1 (by rfl) ⟨1345832, by rfl⟩ : syracuseStep 1794443 = 2691665) B2691665
theorem B1794455 : Blo 1794098 1794455 := bstep (se 1 (by rfl) ⟨1345841, by rfl⟩ : syracuseStep 1794455 = 2691683) B2691683
theorem B1794475 : Blo 1794098 1794475 := bstep (se 1 (by rfl) ⟨1345856, by rfl⟩ : syracuseStep 1794475 = 2691713) B2691713
theorem B4039091 : Blo 1794098 4039091 := bstep (se 1 (by rfl) ⟨3029318, by rfl⟩ : syracuseStep 4039091 = 6058637) B6058637
theorem B1794487 : Blo 1794098 1794487 := bstep (se 1 (by rfl) ⟨1345865, by rfl⟩ : syracuseStep 1794487 = 2691731) B2691731
theorem B1794507 : Blo 1794098 1794507 := bstep (se 1 (by rfl) ⟨1345880, by rfl⟩ : syracuseStep 1794507 = 2691761) B2691761
theorem B1794519 : Blo 1794098 1794519 := bstep (se 1 (by rfl) ⟨1345889, by rfl⟩ : syracuseStep 1794519 = 2691779) B2691779
theorem B4039127 : Blo 1794098 4039127 := bstep (se 1 (by rfl) ⟨3029345, by rfl⟩ : syracuseStep 4039127 = 6058691) B6058691
theorem B10224089 : Blo 1794098 10224089 := bstep (se 2 (by rfl) ⟨3834033, by rfl⟩ : syracuseStep 10224089 = 7668067) B7668067
theorem B6472153 : Blo 1794098 6472153 := bstep (se 2 (by rfl) ⟨2427057, by rfl⟩ : syracuseStep 6472153 = 4854115) B4854115
theorem B1794539 : Blo 1794098 1794539 := bstep (se 1 (by rfl) ⟨1345904, by rfl⟩ : syracuseStep 1794539 = 2691809) B2691809
theorem B1794551 : Blo 1794098 1794551 := bstep (se 1 (by rfl) ⟨1345913, by rfl⟩ : syracuseStep 1794551 = 2691827) B2691827
theorem B1794571 : Blo 1794098 1794571 := bstep (se 1 (by rfl) ⟨1345928, by rfl⟩ : syracuseStep 1794571 = 2691857) B2691857
theorem B1794583 : Blo 1794098 1794583 := bstep (se 1 (by rfl) ⟨1345937, by rfl⟩ : syracuseStep 1794583 = 2691875) B2691875
theorem B3408409 : Blo 1794098 3408409 := bstep (se 2 (by rfl) ⟨1278153, by rfl⟩ : syracuseStep 3408409 = 2556307) B2556307
theorem B1794603 : Blo 1794098 1794603 := bstep (se 1 (by rfl) ⟨1345952, by rfl⟩ : syracuseStep 1794603 = 2691905) B2691905
theorem B1794615 : Blo 1794098 1794615 := bstep (se 1 (by rfl) ⟨1345961, by rfl⟩ : syracuseStep 1794615 = 2691923) B2691923
theorem B1794635 : Blo 1794098 1794635 := bstep (se 1 (by rfl) ⟨1345976, by rfl⟩ : syracuseStep 1794635 = 2691953) B2691953
theorem B1794647 : Blo 1794098 1794647 := bstep (se 1 (by rfl) ⟨1345985, by rfl⟩ : syracuseStep 1794647 = 2691971) B2691971
theorem B5112409 : Blo 1794098 5112409 := bstep (se 2 (by rfl) ⟨1917153, by rfl⟩ : syracuseStep 5112409 = 3834307) B3834307
theorem B1794667 : Blo 1794098 1794667 := bstep (se 1 (by rfl) ⟨1346000, by rfl⟩ : syracuseStep 1794667 = 2692001) B2692001
theorem B1794679 : Blo 1794098 1794679 := bstep (se 1 (by rfl) ⟨1346009, by rfl⟩ : syracuseStep 1794679 = 2692019) B2692019
theorem B1794699 : Blo 1794098 1794699 := bstep (se 1 (by rfl) ⟨1346024, by rfl⟩ : syracuseStep 1794699 = 2692049) B2692049
theorem B4039307 : Blo 1794098 4039307 := bstep (se 1 (by rfl) ⟨3029480, by rfl⟩ : syracuseStep 4039307 = 6058961) B6058961
theorem B1794711 : Blo 1794098 1794711 := bstep (se 1 (by rfl) ⟨1346033, by rfl⟩ : syracuseStep 1794711 = 2692067) B2692067
theorem B2556569 : Blo 1794098 2556569 := bstep (se 2 (by rfl) ⟨958713, by rfl⟩ : syracuseStep 2556569 = 1917427) B1917427
theorem B1794731 : Blo 1794098 1794731 := bstep (se 1 (by rfl) ⟨1346048, by rfl⟩ : syracuseStep 1794731 = 2692097) B2692097
theorem B1794743 : Blo 1794098 1794743 := bstep (se 1 (by rfl) ⟨1346057, by rfl⟩ : syracuseStep 1794743 = 2692115) B2692115
theorem B4039361 : Blo 1794098 4039361 := bstep (se 2 (by rfl) ⟨1514760, by rfl⟩ : syracuseStep 4039361 = 3029521) B3029521
theorem B1794763 : Blo 1794098 1794763 := bstep (se 1 (by rfl) ⟨1346072, by rfl⟩ : syracuseStep 1794763 = 2692145) B2692145
theorem B1794775 : Blo 1794098 1794775 := bstep (se 1 (by rfl) ⟨1346081, by rfl⟩ : syracuseStep 1794775 = 2692163) B2692163
theorem B1794795 : Blo 1794098 1794795 := bstep (se 1 (by rfl) ⟨1346096, by rfl⟩ : syracuseStep 1794795 = 2692193) B2692193
theorem B1794807 : Blo 1794098 1794807 := bstep (se 1 (by rfl) ⟨1346105, by rfl⟩ : syracuseStep 1794807 = 2692211) B2692211
theorem B7381763 : Blo 1794098 7381763 := bstep (se 1 (by rfl) ⟨5536322, by rfl⟩ : syracuseStep 7381763 = 11072645) B11072645
theorem B1794827 : Blo 1794098 1794827 := bstep (se 1 (by rfl) ⟨1346120, by rfl⟩ : syracuseStep 1794827 = 2692241) B2692241
theorem B1794839 : Blo 1794098 1794839 := bstep (se 1 (by rfl) ⟨1346129, by rfl⟩ : syracuseStep 1794839 = 2692259) B2692259
theorem B1794859 : Blo 1794098 1794859 := bstep (se 1 (by rfl) ⟨1346144, by rfl⟩ : syracuseStep 1794859 = 2692289) B2692289
theorem B1794871 : Blo 1794098 1794871 := bstep (se 1 (by rfl) ⟨1346153, by rfl⟩ : syracuseStep 1794871 = 2692307) B2692307
theorem B1794891 : Blo 1794098 1794891 := bstep (se 1 (by rfl) ⟨1346168, by rfl⟩ : syracuseStep 1794891 = 2692337) B2692337
theorem B1794903 : Blo 1794098 1794903 := bstep (se 1 (by rfl) ⟨1346177, by rfl⟩ : syracuseStep 1794903 = 2692355) B2692355
theorem B4850525 : Blo 1794098 4850525 := bstep (se 3 (by rfl) ⟨909473, by rfl⟩ : syracuseStep 4850525 = 1818947) B1818947
theorem B1794923 : Blo 1794098 1794923 := bstep (se 1 (by rfl) ⟨1346192, by rfl⟩ : syracuseStep 1794923 = 2692385) B2692385
theorem B1917803 : Blo 1794098 1917803 := bstep (se 1 (by rfl) ⟨1438352, by rfl⟩ : syracuseStep 1917803 = 2876705) B2876705
theorem B1794935 : Blo 1794098 1794935 := bstep (se 1 (by rfl) ⟨1346201, by rfl⟩ : syracuseStep 1794935 = 2692403) B2692403
theorem B1794955 : Blo 1794098 1794955 := bstep (se 1 (by rfl) ⟨1346216, by rfl⟩ : syracuseStep 1794955 = 2692433) B2692433
theorem B1819531 : Blo 1794098 1819531 := bstep (se 1 (by rfl) ⟨1364648, by rfl⟩ : syracuseStep 1819531 = 2729297) B2729297
theorem B1794967 : Blo 1794098 1794967 := bstep (se 1 (by rfl) ⟨1346225, by rfl⟩ : syracuseStep 1794967 = 2692451) B2692451
theorem B4039577 : Blo 1794098 4039577 := bstep (se 2 (by rfl) ⟨1514841, by rfl⟩ : syracuseStep 4039577 = 3029683) B3029683
theorem B1794987 : Blo 1794098 1794987 := bstep (se 1 (by rfl) ⟨1346240, by rfl⟩ : syracuseStep 1794987 = 2692481) B2692481
theorem B3834803 : Blo 1794098 3834803 := bstep (se 1 (by rfl) ⟨2876102, by rfl⟩ : syracuseStep 3834803 = 5752205) B5752205
theorem B1794999 : Blo 1794098 1794999 := bstep (se 1 (by rfl) ⟨1346249, by rfl⟩ : syracuseStep 1794999 = 2692499) B2692499
theorem B1795019 : Blo 1794098 1795019 := bstep (se 1 (by rfl) ⟨1346264, by rfl⟩ : syracuseStep 1795019 = 2692529) B2692529
theorem B1795031 : Blo 1794098 1795031 := bstep (se 1 (by rfl) ⟨1346273, by rfl⟩ : syracuseStep 1795031 = 2692547) B2692547
theorem B5751769 : Blo 1794098 5751769 := bstep (se 2 (by rfl) ⟨2156913, by rfl⟩ : syracuseStep 5751769 = 4313827) B4313827
theorem B7668701 : Blo 1794098 7668701 := bstep (se 3 (by rfl) ⟨1437881, by rfl⟩ : syracuseStep 7668701 = 2875763) B2875763
theorem B1795051 : Blo 1794098 1795051 := bstep (se 1 (by rfl) ⟨1346288, by rfl⟩ : syracuseStep 1795051 = 2692577) B2692577
theorem B4039667 : Blo 1794098 4039667 := bstep (se 1 (by rfl) ⟨3029750, by rfl⟩ : syracuseStep 4039667 = 6059501) B6059501
theorem B1795063 : Blo 1794098 1795063 := bstep (se 1 (by rfl) ⟨1346297, by rfl⟩ : syracuseStep 1795063 = 2692595) B2692595
theorem B1795083 : Blo 1794098 1795083 := bstep (se 1 (by rfl) ⟨1346312, by rfl⟩ : syracuseStep 1795083 = 2692625) B2692625
theorem B1795095 : Blo 1794098 1795095 := bstep (se 1 (by rfl) ⟨1346321, by rfl⟩ : syracuseStep 1795095 = 2692643) B2692643
theorem B4039703 : Blo 1794098 4039703 := bstep (se 1 (by rfl) ⟨3029777, by rfl⟩ : syracuseStep 4039703 = 6059555) B6059555
theorem B1795115 : Blo 1794098 1795115 := bstep (se 1 (by rfl) ⟨1346336, by rfl⟩ : syracuseStep 1795115 = 2692673) B2692673
theorem B1795127 : Blo 1794098 1795127 := bstep (se 1 (by rfl) ⟨1346345, by rfl⟩ : syracuseStep 1795127 = 2692691) B2692691
theorem B3638347 : Blo 1794098 3638347 := bstep (se 1 (by rfl) ⟨2728760, by rfl⟩ : syracuseStep 3638347 = 5457521) B5457521
theorem B1795147 : Blo 1794098 1795147 := bstep (se 1 (by rfl) ⟨1346360, by rfl⟩ : syracuseStep 1795147 = 2692721) B2692721
theorem B1795159 : Blo 1794098 1795159 := bstep (se 1 (by rfl) ⟨1346369, by rfl⟩ : syracuseStep 1795159 = 2692739) B2692739
theorem B1795179 : Blo 1794098 1795179 := bstep (se 1 (by rfl) ⟨1346384, by rfl⟩ : syracuseStep 1795179 = 2692769) B2692769
theorem B1795191 : Blo 1794098 1795191 := bstep (se 1 (by rfl) ⟨1346393, by rfl⟩ : syracuseStep 1795191 = 2692787) B2692787
theorem B1795211 : Blo 1794098 1795211 := bstep (se 1 (by rfl) ⟨1346408, by rfl⟩ : syracuseStep 1795211 = 2692817) B2692817
theorem B1795223 : Blo 1794098 1795223 := bstep (se 1 (by rfl) ⟨1346417, by rfl⟩ : syracuseStep 1795223 = 2692835) B2692835
theorem B1795243 : Blo 1794098 1795243 := bstep (se 1 (by rfl) ⟨1346432, by rfl⟩ : syracuseStep 1795243 = 2692865) B2692865
theorem B1795255 : Blo 1794098 1795255 := bstep (se 1 (by rfl) ⟨1346441, by rfl⟩ : syracuseStep 1795255 = 2692883) B2692883
theorem B1795275 : Blo 1794098 1795275 := bstep (se 1 (by rfl) ⟨1346456, by rfl⟩ : syracuseStep 1795275 = 2692913) B2692913
theorem B4039883 : Blo 1794098 4039883 := bstep (se 1 (by rfl) ⟨3029912, by rfl⟩ : syracuseStep 4039883 = 6059825) B6059825
theorem B1795287 : Blo 1794098 1795287 := bstep (se 1 (by rfl) ⟨1346465, by rfl⟩ : syracuseStep 1795287 = 2692931) B2692931
theorem B7374041 : Blo 1794098 7374041 := bstep (se 2 (by rfl) ⟨2765265, by rfl⟩ : syracuseStep 7374041 = 5530531) B5530531
theorem B1795307 : Blo 1794098 1795307 := bstep (se 1 (by rfl) ⟨1346480, by rfl⟩ : syracuseStep 1795307 = 2692961) B2692961
theorem B1795319 : Blo 1794098 1795319 := bstep (se 1 (by rfl) ⟨1346489, by rfl⟩ : syracuseStep 1795319 = 2692979) B2692979
theorem B4039937 : Blo 1794098 4039937 := bstep (se 2 (by rfl) ⟨1514976, by rfl⟩ : syracuseStep 4039937 = 3029953) B3029953
theorem B1795339 : Blo 1794098 1795339 := bstep (se 1 (by rfl) ⟨1346504, by rfl⟩ : syracuseStep 1795339 = 2693009) B2693009
theorem B13632785 : Blo 1794098 13632785 := bstep (se 2 (by rfl) ⟨5112294, by rfl⟩ : syracuseStep 13632785 = 10224589) B10224589
theorem B1795351 : Blo 1794098 1795351 := bstep (se 1 (by rfl) ⟨1346513, by rfl⟩ : syracuseStep 1795351 = 2693027) B2693027
theorem B2557207 : Blo 1794098 2557207 := bstep (se 1 (by rfl) ⟨1917905, by rfl⟩ : syracuseStep 2557207 = 3835811) B3835811
theorem B15328547 : Blo 1794098 15328547 := bstep (se 1 (by rfl) ⟨11496410, by rfl⟩ : syracuseStep 15328547 = 22992821) B22992821
theorem B1795371 : Blo 1794098 1795371 := bstep (se 1 (by rfl) ⟨1346528, by rfl⟩ : syracuseStep 1795371 = 2693057) B2693057
theorem B1795383 : Blo 1794098 1795383 := bstep (se 1 (by rfl) ⟨1346537, by rfl⟩ : syracuseStep 1795383 = 2693075) B2693075
theorem B1795403 : Blo 1794098 1795403 := bstep (se 1 (by rfl) ⟨1346552, by rfl⟩ : syracuseStep 1795403 = 2693105) B2693105
theorem B1795415 : Blo 1794098 1795415 := bstep (se 1 (by rfl) ⟨1346561, by rfl⟩ : syracuseStep 1795415 = 2693123) B2693123
theorem B1795435 : Blo 1794098 1795435 := bstep (se 1 (by rfl) ⟨1346576, by rfl⟩ : syracuseStep 1795435 = 2693153) B2693153
theorem B1795447 : Blo 1794098 1795447 := bstep (se 1 (by rfl) ⟨1346585, by rfl⟩ : syracuseStep 1795447 = 2693171) B2693171
theorem B1795467 : Blo 1794098 1795467 := bstep (se 1 (by rfl) ⟨1346600, by rfl⟩ : syracuseStep 1795467 = 2693201) B2693201
theorem B1795479 : Blo 1794098 1795479 := bstep (se 1 (by rfl) ⟨1346609, by rfl⟩ : syracuseStep 1795479 = 2693219) B2693219
theorem B1795499 : Blo 1794098 1795499 := bstep (se 1 (by rfl) ⟨1346624, by rfl⟩ : syracuseStep 1795499 = 2693249) B2693249
theorem B1795511 : Blo 1794098 1795511 := bstep (se 1 (by rfl) ⟨1346633, by rfl⟩ : syracuseStep 1795511 = 2693267) B2693267
theorem B1795531 : Blo 1794098 1795531 := bstep (se 1 (by rfl) ⟨1346648, by rfl⟩ : syracuseStep 1795531 = 2693297) B2693297
theorem B1795543 : Blo 1794098 1795543 := bstep (se 1 (by rfl) ⟨1346657, by rfl⟩ : syracuseStep 1795543 = 2693315) B2693315
theorem B4040153 : Blo 1794098 4040153 := bstep (se 2 (by rfl) ⟨1515057, by rfl⟩ : syracuseStep 4040153 = 3030115) B3030115
theorem B1795563 : Blo 1794098 1795563 := bstep (se 1 (by rfl) ⟨1346672, by rfl⟩ : syracuseStep 1795563 = 2693345) B2693345
theorem B1795575 : Blo 1794098 1795575 := bstep (se 1 (by rfl) ⟨1346681, by rfl⟩ : syracuseStep 1795575 = 2693363) B2693363
theorem B1795595 : Blo 1794098 1795595 := bstep (se 1 (by rfl) ⟨1346696, by rfl⟩ : syracuseStep 1795595 = 2693393) B2693393
theorem B1795607 : Blo 1794098 1795607 := bstep (se 1 (by rfl) ⟨1346705, by rfl⟩ : syracuseStep 1795607 = 2693411) B2693411
theorem B1795627 : Blo 1794098 1795627 := bstep (se 1 (by rfl) ⟨1346720, by rfl⟩ : syracuseStep 1795627 = 2693441) B2693441
theorem B9209389 : Blo 1794098 9209389 := bstep (se 3 (by rfl) ⟨1726760, by rfl⟩ : syracuseStep 9209389 = 3453521) B3453521
theorem B4040243 : Blo 1794098 4040243 := bstep (se 1 (by rfl) ⟨3030182, by rfl⟩ : syracuseStep 4040243 = 6060365) B6060365
theorem B1795639 : Blo 1794098 1795639 := bstep (se 1 (by rfl) ⟨1346729, by rfl⟩ : syracuseStep 1795639 = 2693459) B2693459
theorem B1795659 : Blo 1794098 1795659 := bstep (se 1 (by rfl) ⟨1346744, by rfl⟩ : syracuseStep 1795659 = 2693489) B2693489
theorem B1795671 : Blo 1794098 1795671 := bstep (se 1 (by rfl) ⟨1346753, by rfl⟩ : syracuseStep 1795671 = 2693507) B2693507
theorem B4040279 : Blo 1794098 4040279 := bstep (se 1 (by rfl) ⟨3030209, by rfl⟩ : syracuseStep 4040279 = 6060419) B6060419
theorem B1795691 : Blo 1794098 1795691 := bstep (se 1 (by rfl) ⟨1346768, by rfl⟩ : syracuseStep 1795691 = 2693537) B2693537
theorem B1795703 : Blo 1794098 1795703 := bstep (se 1 (by rfl) ⟨1346777, by rfl⟩ : syracuseStep 1795703 = 2693555) B2693555
theorem B1795723 : Blo 1794098 1795723 := bstep (se 1 (by rfl) ⟨1346792, by rfl⟩ : syracuseStep 1795723 = 2693585) B2693585
theorem B11503255 : Blo 1794098 11503255 := bstep (se 1 (by rfl) ⟨8627441, by rfl⟩ : syracuseStep 11503255 = 17254883) B17254883
theorem B7669399 : Blo 1794098 7669399 := bstep (se 1 (by rfl) ⟨5752049, by rfl⟩ : syracuseStep 7669399 = 11504099) B11504099
theorem B1795735 : Blo 1794098 1795735 := bstep (se 1 (by rfl) ⟨1346801, by rfl⟩ : syracuseStep 1795735 = 2693603) B2693603
theorem B1795755 : Blo 1794098 1795755 := bstep (se 1 (by rfl) ⟨1346816, by rfl⟩ : syracuseStep 1795755 = 2693633) B2693633
theorem B13625009 : Blo 1794098 13625009 := bstep (se 2 (by rfl) ⟨5109378, by rfl⟩ : syracuseStep 13625009 = 10218757) B10218757
theorem B1795767 : Blo 1794098 1795767 := bstep (se 1 (by rfl) ⟨1346825, by rfl⟩ : syracuseStep 1795767 = 2693651) B2693651
theorem B1795787 : Blo 1794098 1795787 := bstep (se 1 (by rfl) ⟨1346840, by rfl⟩ : syracuseStep 1795787 = 2693681) B2693681
theorem B1795799 : Blo 1794098 1795799 := bstep (se 1 (by rfl) ⟨1346849, by rfl⟩ : syracuseStep 1795799 = 2693699) B2693699
theorem B1795819 : Blo 1794098 1795819 := bstep (se 1 (by rfl) ⟨1346864, by rfl⟩ : syracuseStep 1795819 = 2693729) B2693729
theorem B1795831 : Blo 1794098 1795831 := bstep (se 1 (by rfl) ⟨1346873, by rfl⟩ : syracuseStep 1795831 = 2693747) B2693747
theorem B3835649 : Blo 1794098 3835649 := bstep (se 2 (by rfl) ⟨1438368, by rfl⟩ : syracuseStep 3835649 = 2876737) B2876737
theorem B4040459 : Blo 1794098 4040459 := bstep (se 1 (by rfl) ⟨3030344, by rfl⟩ : syracuseStep 4040459 = 6060689) B6060689
theorem B1795851 : Blo 1794098 1795851 := bstep (se 1 (by rfl) ⟨1346888, by rfl⟩ : syracuseStep 1795851 = 2693777) B2693777
theorem B1795863 : Blo 1794098 1795863 := bstep (se 1 (by rfl) ⟨1346897, by rfl⟩ : syracuseStep 1795863 = 2693795) B2693795
theorem B4433687 : Blo 1794098 4433687 := bstep (se 1 (by rfl) ⟨3325265, by rfl⟩ : syracuseStep 4433687 = 6650531) B6650531
theorem B1795883 : Blo 1794098 1795883 := bstep (se 1 (by rfl) ⟨1346912, by rfl⟩ : syracuseStep 1795883 = 2693825) B2693825
theorem B5113651 : Blo 1794098 5113651 := bstep (se 1 (by rfl) ⟨3835238, by rfl⟩ : syracuseStep 5113651 = 7670477) B7670477
theorem B3409715 : Blo 1794098 3409715 := bstep (se 1 (by rfl) ⟨2557286, by rfl⟩ : syracuseStep 3409715 = 5114573) B5114573
theorem B1795895 : Blo 1794098 1795895 := bstep (se 1 (by rfl) ⟨1346921, by rfl⟩ : syracuseStep 1795895 = 2693843) B2693843
theorem B4040513 : Blo 1794098 4040513 := bstep (se 2 (by rfl) ⟨1515192, by rfl⟩ : syracuseStep 4040513 = 3030385) B3030385
theorem B1795915 : Blo 1794098 1795915 := bstep (se 1 (by rfl) ⟨1346936, by rfl⟩ : syracuseStep 1795915 = 2693873) B2693873
theorem B1795927 : Blo 1794098 1795927 := bstep (se 1 (by rfl) ⟨1346945, by rfl⟩ : syracuseStep 1795927 = 2693891) B2693891
theorem B9701221 : Blo 1794098 9701221 := bstep (se 4 (by rfl) ⟨909489, by rfl⟩ : syracuseStep 9701221 = 1818979) B1818979
theorem B1795947 : Blo 1794098 1795947 := bstep (se 1 (by rfl) ⟨1346960, by rfl⟩ : syracuseStep 1795947 = 2693921) B2693921
theorem B1795959 : Blo 1794098 1795959 := bstep (se 1 (by rfl) ⟨1346969, by rfl⟩ : syracuseStep 1795959 = 2693939) B2693939
theorem B1795979 : Blo 1794098 1795979 := bstep (se 1 (by rfl) ⟨1346984, by rfl⟩ : syracuseStep 1795979 = 2693969) B2693969
theorem B1795991 : Blo 1794098 1795991 := bstep (se 1 (by rfl) ⟨1346993, by rfl⟩ : syracuseStep 1795991 = 2693987) B2693987
theorem B1796011 : Blo 1794098 1796011 := bstep (se 1 (by rfl) ⟨1347008, by rfl⟩ : syracuseStep 1796011 = 2694017) B2694017
theorem B6817715 : Blo 1794098 6817715 := bstep (se 1 (by rfl) ⟨5113286, by rfl⟩ : syracuseStep 6817715 = 10226573) B10226573
theorem B1796023 : Blo 1794098 1796023 := bstep (se 1 (by rfl) ⟨1347017, by rfl⟩ : syracuseStep 1796023 = 2694035) B2694035
theorem B6817729 : Blo 1794098 6817729 := bstep (se 2 (by rfl) ⟨2556648, by rfl⟩ : syracuseStep 6817729 = 5113297) B5113297
theorem B6055883 : Blo 1794098 6055883 := bstep (se 1 (by rfl) ⟨4541912, by rfl⟩ : syracuseStep 6055883 = 9083825) B9083825
theorem B2271179 : Blo 1794098 2271179 := bstep (se 1 (by rfl) ⟨1703384, by rfl⟩ : syracuseStep 2271179 = 3406769) B3406769
theorem B1796043 : Blo 1794098 1796043 := bstep (se 1 (by rfl) ⟨1347032, by rfl⟩ : syracuseStep 1796043 = 2694065) B2694065
theorem B1796055 : Blo 1794098 1796055 := bstep (se 1 (by rfl) ⟨1347041, by rfl⟩ : syracuseStep 1796055 = 2694083) B2694083
theorem B28018649 : Blo 1794098 28018649 := bstep (se 2 (by rfl) ⟨10506993, by rfl⟩ : syracuseStep 28018649 = 21013987) B21013987
theorem B1796075 : Blo 1794098 1796075 := bstep (se 1 (by rfl) ⟨1347056, by rfl⟩ : syracuseStep 1796075 = 2694113) B2694113
theorem B1796087 : Blo 1794098 1796087 := bstep (se 1 (by rfl) ⟨1347065, by rfl⟩ : syracuseStep 1796087 = 2694131) B2694131
theorem B4040729 : Blo 1794098 4040729 := bstep (se 2 (by rfl) ⟨1515273, by rfl⟩ : syracuseStep 4040729 = 3030547) B3030547
theorem B9701441 : Blo 1794098 9701441 := bstep (se 2 (by rfl) ⟨3638040, by rfl⟩ : syracuseStep 9701441 = 7276081) B7276081
theorem B3835991 : Blo 1794098 3835991 := bstep (se 1 (by rfl) ⟨2876993, by rfl⟩ : syracuseStep 3835991 = 5753987) B5753987
theorem B4040819 : Blo 1794098 4040819 := bstep (se 1 (by rfl) ⟨3030614, by rfl⟩ : syracuseStep 4040819 = 6061229) B6061229
theorem B13625495 : Blo 1794098 13625495 := bstep (se 1 (by rfl) ⟨10219121, by rfl⟩ : syracuseStep 13625495 = 20438243) B20438243
theorem B4040855 : Blo 1794098 4040855 := bstep (se 1 (by rfl) ⟨3030641, by rfl⟩ : syracuseStep 4040855 = 6061283) B6061283
theorem B6056153 : Blo 1794098 6056153 := bstep (se 2 (by rfl) ⟨2271057, by rfl⟩ : syracuseStep 6056153 = 4542115) B4542115
theorem B5908801 : Blo 1794098 5908801 := bstep (se 2 (by rfl) ⟨2215800, by rfl⟩ : syracuseStep 5908801 = 4431601) B4431601
theorem B4041035 : Blo 1794098 4041035 := bstep (se 1 (by rfl) ⟨3030776, by rfl⟩ : syracuseStep 4041035 = 6061553) B6061553
theorem B4041089 : Blo 1794098 4041089 := bstep (se 2 (by rfl) ⟨1515408, by rfl⟩ : syracuseStep 4041089 = 3030817) B3030817
theorem B3688843 : Blo 1794098 3688843 := bstep (se 1 (by rfl) ⟨2766632, by rfl⟩ : syracuseStep 3688843 = 5533265) B5533265
theorem B7277149 : Blo 1794098 7277149 := bstep (se 3 (by rfl) ⟨1364465, by rfl⟩ : syracuseStep 7277149 = 2728931) B2728931
theorem B2271883 : Blo 1794098 2271883 := bstep (se 1 (by rfl) ⟨1703912, by rfl⟩ : syracuseStep 2271883 = 3407825) B3407825
theorem B4311731 : Blo 1794098 4311731 := bstep (se 1 (by rfl) ⟨3233798, by rfl⟩ : syracuseStep 4311731 = 6467597) B6467597
theorem B5753537 : Blo 1794098 5753537 := bstep (se 2 (by rfl) ⟨2157576, by rfl⟩ : syracuseStep 5753537 = 4315153) B4315153
theorem B10218257 : Blo 1794098 10218257 := bstep (se 2 (by rfl) ⟨3831846, by rfl⟩ : syracuseStep 10218257 = 7663693) B7663693
theorem B8629037 : Blo 1794098 8629037 := bstep (se 3 (by rfl) ⟨1617944, by rfl⟩ : syracuseStep 8629037 = 3235889) B3235889
theorem B17247077 : Blo 1794098 17247077 := bstep (se 4 (by rfl) ⟨1616913, by rfl⟩ : syracuseStep 17247077 = 3233827) B3233827
theorem B9087875 : Blo 1794098 9087875 := bstep (se 1 (by rfl) ⟨6815906, by rfl⟩ : syracuseStep 9087875 = 13631813) B13631813
theorem B6056855 : Blo 1794098 6056855 := bstep (se 1 (by rfl) ⟨4542641, by rfl⟩ : syracuseStep 6056855 = 9085283) B9085283
theorem B2272151 : Blo 1794098 2272151 := bstep (se 1 (by rfl) ⟨1704113, by rfl⟩ : syracuseStep 2272151 = 3408227) B3408227
theorem B7670801 : Blo 1794098 7670801 := bstep (se 2 (by rfl) ⟨2876550, by rfl⟩ : syracuseStep 7670801 = 5753101) B5753101
theorem B49114181 : Blo 1794098 49114181 := bstep (se 4 (by rfl) ⟨4604454, by rfl⟩ : syracuseStep 49114181 = 9208909) B9208909
theorem B2018443 : Blo 1794098 2018443 := bstep (se 1 (by rfl) ⟨1513832, by rfl⟩ : syracuseStep 2018443 = 3027665) B3027665
theorem B25873613 : Blo 1794098 25873613 := bstep (se 3 (by rfl) ⟨4851302, by rfl⟩ : syracuseStep 25873613 = 9702605) B9702605
theorem B2018551 : Blo 1794098 2018551 := bstep (se 1 (by rfl) ⟨1513913, by rfl⟩ : syracuseStep 2018551 = 3027827) B3027827
theorem B4541771 : Blo 1794098 4541771 := bstep (se 1 (by rfl) ⟨3406328, by rfl⟩ : syracuseStep 4541771 = 6812657) B6812657
theorem B6466891 : Blo 1794098 6466891 := bstep (se 1 (by rfl) ⟨4850168, by rfl⟩ : syracuseStep 6466891 = 9700337) B9700337
theorem B2018731 : Blo 1794098 2018731 := bstep (se 1 (by rfl) ⟨1514048, by rfl⟩ : syracuseStep 2018731 = 3028097) B3028097
theorem B6057395 : Blo 1794098 6057395 := bstep (se 1 (by rfl) ⟨4543046, by rfl⟩ : syracuseStep 6057395 = 9086093) B9086093
theorem B11496977 : Blo 1794098 11496977 := bstep (se 2 (by rfl) ⟨4311366, by rfl⟩ : syracuseStep 11496977 = 8622733) B8622733
theorem B2018839 : Blo 1794098 2018839 := bstep (se 1 (by rfl) ⟨1514129, by rfl⟩ : syracuseStep 2018839 = 3028259) B3028259
theorem B4148801 : Blo 1794098 4148801 := bstep (se 2 (by rfl) ⟨1555800, by rfl⟩ : syracuseStep 4148801 = 3111601) B3111601
theorem B2272855 : Blo 1794098 2272855 := bstep (se 1 (by rfl) ⟨1704641, by rfl⟩ : syracuseStep 2272855 = 3409283) B3409283
theorem B6467165 : Blo 1794098 6467165 := bstep (se 3 (by rfl) ⟨1212593, by rfl⟩ : syracuseStep 6467165 = 2425187) B2425187
theorem B6057665 : Blo 1794098 6057665 := bstep (se 2 (by rfl) ⟨2271624, by rfl⟩ : syracuseStep 6057665 = 4543249) B4543249
theorem B2019019 : Blo 1794098 2019019 := bstep (se 1 (by rfl) ⟨1514264, by rfl⟩ : syracuseStep 2019019 = 3028529) B3028529
theorem B2019127 : Blo 1794098 2019127 := bstep (se 1 (by rfl) ⟨1514345, by rfl⟩ : syracuseStep 2019127 = 3028691) B3028691
theorem B24571765 : Blo 1794098 24571765 := bstep (se 5 (by rfl) ⟨1151801, by rfl⟩ : syracuseStep 24571765 = 2303603) B2303603
theorem B6557591 : Blo 1794098 6557591 := bstep (se 1 (by rfl) ⟨4918193, by rfl⟩ : syracuseStep 6557591 = 9836387) B9836387
theorem B2019307 : Blo 1794098 2019307 := bstep (se 1 (by rfl) ⟨1514480, by rfl⟩ : syracuseStep 2019307 = 3028961) B3028961
theorem B3502081 : Blo 1794098 3502081 := bstep (se 2 (by rfl) ⟨1313280, by rfl⟩ : syracuseStep 3502081 = 2626561) B2626561
theorem B11505739 : Blo 1794098 11505739 := bstep (se 1 (by rfl) ⟨8629304, by rfl⟩ : syracuseStep 11505739 = 17258609) B17258609
theorem B98299979 : Blo 1794098 98299979 := bstep (se 1 (by rfl) ⟨73724984, by rfl⟩ : syracuseStep 98299979 = 147449969) B147449969
theorem B2019415 : Blo 1794098 2019415 := bstep (se 1 (by rfl) ⟨1514561, by rfl⟩ : syracuseStep 2019415 = 3029123) B3029123
theorem B2691161 : Blo 1794098 2691161 := bstep (se 2 (by rfl) ⟨1009185, by rfl⟩ : syracuseStep 2691161 = 2018371) B2018371
theorem B2691275 : Blo 1794098 2691275 := bstep (se 1 (by rfl) ⟨2018456, by rfl⟩ : syracuseStep 2691275 = 4036913) B4036913
theorem B2691287 : Blo 1794098 2691287 := bstep (se 1 (by rfl) ⟨2018465, by rfl⟩ : syracuseStep 2691287 = 4036931) B4036931
theorem B6058205 : Blo 1794098 6058205 := bstep (se 3 (by rfl) ⟨1135913, by rfl⟩ : syracuseStep 6058205 = 2271827) B2271827
theorem B2019595 : Blo 1794098 2019595 := bstep (se 1 (by rfl) ⟨1514696, by rfl⟩ : syracuseStep 2019595 = 3029393) B3029393
theorem B4542743 : Blo 1794098 4542743 := bstep (se 1 (by rfl) ⟨3407057, by rfl⟩ : syracuseStep 4542743 = 6814115) B6814115
theorem B2691353 : Blo 1794098 2691353 := bstep (se 2 (by rfl) ⟨1009257, by rfl⟩ : syracuseStep 2691353 = 2018515) B2018515
theorem B19411265 : Blo 1794098 19411265 := bstep (se 2 (by rfl) ⟨7279224, by rfl⟩ : syracuseStep 19411265 = 14558449) B14558449
theorem B2019703 : Blo 1794098 2019703 := bstep (se 1 (by rfl) ⟨1514777, by rfl⟩ : syracuseStep 2019703 = 3029555) B3029555
theorem B2691467 : Blo 1794098 2691467 := bstep (se 1 (by rfl) ⟨2018600, by rfl⟩ : syracuseStep 2691467 = 4037201) B4037201
theorem B2691479 : Blo 1794098 2691479 := bstep (se 1 (by rfl) ⟨2018609, by rfl⟩ : syracuseStep 2691479 = 4037219) B4037219
theorem B2691545 : Blo 1794098 2691545 := bstep (se 2 (by rfl) ⟨1009329, by rfl⟩ : syracuseStep 2691545 = 2018659) B2018659
theorem B30683609 : Blo 1794098 30683609 := bstep (se 2 (by rfl) ⟨11506353, by rfl⟩ : syracuseStep 30683609 = 23012707) B23012707
theorem B2019883 : Blo 1794098 2019883 := bstep (se 1 (by rfl) ⟨1514912, by rfl⟩ : syracuseStep 2019883 = 3029825) B3029825
theorem B2691659 : Blo 1794098 2691659 := bstep (se 1 (by rfl) ⟨2018744, by rfl⟩ : syracuseStep 2691659 = 4037489) B4037489
theorem B2691671 : Blo 1794098 2691671 := bstep (se 1 (by rfl) ⟨2018753, by rfl⟩ : syracuseStep 2691671 = 4037507) B4037507
theorem B2019991 : Blo 1794098 2019991 := bstep (se 1 (by rfl) ⟨1514993, by rfl⟩ : syracuseStep 2019991 = 3029987) B3029987
theorem B2691737 : Blo 1794098 2691737 := bstep (se 2 (by rfl) ⟨1009401, by rfl⟩ : syracuseStep 2691737 = 2018803) B2018803
theorem B6468275 : Blo 1794098 6468275 := bstep (se 1 (by rfl) ⟨4851206, by rfl⟩ : syracuseStep 6468275 = 9702413) B9702413
theorem B2691851 : Blo 1794098 2691851 := bstep (se 1 (by rfl) ⟨2018888, by rfl⟩ : syracuseStep 2691851 = 4037777) B4037777
theorem B2691863 : Blo 1794098 2691863 := bstep (se 1 (by rfl) ⟨2018897, by rfl⟩ : syracuseStep 2691863 = 4037795) B4037795
theorem B16380737 : Blo 1794098 16380737 := bstep (se 2 (by rfl) ⟨6142776, by rfl⟩ : syracuseStep 16380737 = 12285553) B12285553
theorem B2020171 : Blo 1794098 2020171 := bstep (se 1 (by rfl) ⟨1515128, by rfl⟩ : syracuseStep 2020171 = 3030257) B3030257
theorem B2691929 : Blo 1794098 2691929 := bstep (se 2 (by rfl) ⟨1009473, by rfl⟩ : syracuseStep 2691929 = 2018947) B2018947
theorem B3453835 : Blo 1794098 3453835 := bstep (se 1 (by rfl) ⟨2590376, by rfl⟩ : syracuseStep 3453835 = 5180753) B5180753
theorem B7771025 : Blo 1794098 7771025 := bstep (se 2 (by rfl) ⟨2914134, by rfl⟩ : syracuseStep 7771025 = 5828269) B5828269
theorem B27620273 : Blo 1794098 27620273 := bstep (se 2 (by rfl) ⟨10357602, by rfl⟩ : syracuseStep 27620273 = 20715205) B20715205
theorem B22991795 : Blo 1794098 22991795 := bstep (se 1 (by rfl) ⟨17243846, by rfl⟩ : syracuseStep 22991795 = 34487693) B34487693
theorem B4543411 : Blo 1794098 4543411 := bstep (se 1 (by rfl) ⟨3407558, by rfl⟩ : syracuseStep 4543411 = 6815117) B6815117
theorem B2020279 : Blo 1794098 2020279 := bstep (se 1 (by rfl) ⟨1515209, by rfl⟩ : syracuseStep 2020279 = 3030419) B3030419
theorem B2692043 : Blo 1794098 2692043 := bstep (se 1 (by rfl) ⟨2019032, by rfl⟩ : syracuseStep 2692043 = 4038065) B4038065
theorem B2692055 : Blo 1794098 2692055 := bstep (se 1 (by rfl) ⟨2019041, by rfl⟩ : syracuseStep 2692055 = 4038083) B4038083
theorem B2692121 : Blo 1794098 2692121 := bstep (se 2 (by rfl) ⟨1009545, by rfl⟩ : syracuseStep 2692121 = 2019091) B2019091
theorem B10228781 : Blo 1794098 10228781 := bstep (se 3 (by rfl) ⟨1917896, by rfl⟩ : syracuseStep 10228781 = 3835793) B3835793
theorem B4543553 : Blo 1794098 4543553 := bstep (se 2 (by rfl) ⟨1703832, by rfl⟩ : syracuseStep 4543553 = 3407665) B3407665
theorem B13636673 : Blo 1794098 13636673 := bstep (se 2 (by rfl) ⟨5113752, by rfl⟩ : syracuseStep 13636673 = 10227505) B10227505
theorem B3028043 : Blo 1794098 3028043 := bstep (se 1 (by rfl) ⟨2271032, by rfl⟩ : syracuseStep 3028043 = 4542065) B4542065
theorem B2020459 : Blo 1794098 2020459 := bstep (se 1 (by rfl) ⟨1515344, by rfl⟩ : syracuseStep 2020459 = 3030689) B3030689
theorem B2692235 : Blo 1794098 2692235 := bstep (se 1 (by rfl) ⟨2019176, by rfl⟩ : syracuseStep 2692235 = 4038353) B4038353
theorem B2692247 : Blo 1794098 2692247 := bstep (se 1 (by rfl) ⟨2019185, by rfl⟩ : syracuseStep 2692247 = 4038371) B4038371
theorem B3028171 : Blo 1794098 3028171 := bstep (se 1 (by rfl) ⟨2271128, by rfl⟩ : syracuseStep 3028171 = 4542257) B4542257
theorem B2020567 : Blo 1794098 2020567 := bstep (se 1 (by rfl) ⟨1515425, by rfl⟩ : syracuseStep 2020567 = 3030851) B3030851
theorem B2692313 : Blo 1794098 2692313 := bstep (se 2 (by rfl) ⟨1009617, by rfl⟩ : syracuseStep 2692313 = 2019235) B2019235
theorem B8189201 : Blo 1794098 8189201 := bstep (se 2 (by rfl) ⟨3070950, by rfl⟩ : syracuseStep 8189201 = 6141901) B6141901
theorem B14554403 : Blo 1794098 14554403 := bstep (se 1 (by rfl) ⟨10915802, by rfl⟩ : syracuseStep 14554403 = 21831605) B21831605
theorem B2692427 : Blo 1794098 2692427 := bstep (se 1 (by rfl) ⟨2019320, by rfl⟩ : syracuseStep 2692427 = 4038641) B4038641
theorem B6059339 : Blo 1794098 6059339 := bstep (se 1 (by rfl) ⟨4544504, by rfl⟩ : syracuseStep 6059339 = 9089009) B9089009
theorem B2692439 : Blo 1794098 2692439 := bstep (se 1 (by rfl) ⟨2019329, by rfl⟩ : syracuseStep 2692439 = 4038659) B4038659
theorem B3028313 : Blo 1794098 3028313 := bstep (se 2 (by rfl) ⟨1135617, by rfl⟩ : syracuseStep 3028313 = 2271235) B2271235
theorem B2692505 : Blo 1794098 2692505 := bstep (se 2 (by rfl) ⟨1009689, by rfl⟩ : syracuseStep 2692505 = 2019379) B2019379
theorem B3028441 : Blo 1794098 3028441 := bstep (se 2 (by rfl) ⟨1135665, by rfl⟩ : syracuseStep 3028441 = 2271331) B2271331
theorem B2692619 : Blo 1794098 2692619 := bstep (se 1 (by rfl) ⟨2019464, by rfl⟩ : syracuseStep 2692619 = 4038929) B4038929
theorem B2692631 : Blo 1794098 2692631 := bstep (se 1 (by rfl) ⟨2019473, by rfl⟩ : syracuseStep 2692631 = 4038947) B4038947
theorem B25876037 : Blo 1794098 25876037 := bstep (se 4 (by rfl) ⟨2425878, by rfl⟩ : syracuseStep 25876037 = 4851757) B4851757
theorem B2692697 : Blo 1794098 2692697 := bstep (se 2 (by rfl) ⟨1009761, by rfl⟩ : syracuseStep 2692697 = 2019523) B2019523
theorem B6059609 : Blo 1794098 6059609 := bstep (se 2 (by rfl) ⟨2272353, by rfl⟩ : syracuseStep 6059609 = 4544707) B4544707
theorem B2692811 : Blo 1794098 2692811 := bstep (se 1 (by rfl) ⟨2019608, by rfl⟩ : syracuseStep 2692811 = 4039217) B4039217
theorem B2692823 : Blo 1794098 2692823 := bstep (se 1 (by rfl) ⟨2019617, by rfl⟩ : syracuseStep 2692823 = 4039235) B4039235
theorem B2692889 : Blo 1794098 2692889 := bstep (se 2 (by rfl) ⟨1009833, by rfl⟩ : syracuseStep 2692889 = 2019667) B2019667
theorem B2693003 : Blo 1794098 2693003 := bstep (se 1 (by rfl) ⟨2019752, by rfl⟩ : syracuseStep 2693003 = 4039505) B4039505
theorem B2693015 : Blo 1794098 2693015 := bstep (se 1 (by rfl) ⟨2019761, by rfl⟩ : syracuseStep 2693015 = 4039523) B4039523
theorem B10221491 : Blo 1794098 10221491 := bstep (se 1 (by rfl) ⟨7666118, by rfl⟩ : syracuseStep 10221491 = 15332237) B15332237
theorem B15333299 : Blo 1794098 15333299 := bstep (se 1 (by rfl) ⟨11499974, by rfl⟩ : syracuseStep 15333299 = 22999949) B22999949
theorem B2693081 : Blo 1794098 2693081 := bstep (se 2 (by rfl) ⟨1009905, by rfl⟩ : syracuseStep 2693081 = 2019811) B2019811
theorem B3029015 : Blo 1794098 3029015 := bstep (se 1 (by rfl) ⟨2271761, by rfl⟩ : syracuseStep 3029015 = 4543523) B4543523
theorem B7280705 : Blo 1794098 7280705 := bstep (se 2 (by rfl) ⟨2730264, by rfl⟩ : syracuseStep 7280705 = 5460529) B5460529
theorem B2693195 : Blo 1794098 2693195 := bstep (se 1 (by rfl) ⟨2019896, by rfl⟩ : syracuseStep 2693195 = 4039793) B4039793
theorem B2693207 : Blo 1794098 2693207 := bstep (se 1 (by rfl) ⟨2019905, by rfl⟩ : syracuseStep 2693207 = 4039811) B4039811
theorem B15341669 : Blo 1794098 15341669 := bstep (se 4 (by rfl) ⟨1438281, by rfl⟩ : syracuseStep 15341669 = 2876563) B2876563
theorem B6813827 : Blo 1794098 6813827 := bstep (se 1 (by rfl) ⟨5110370, by rfl⟩ : syracuseStep 6813827 = 10220741) B10220741
theorem B6813841 : Blo 1794098 6813841 := bstep (se 2 (by rfl) ⟨2555190, by rfl⟩ : syracuseStep 6813841 = 5110381) B5110381
theorem B3029143 : Blo 1794098 3029143 := bstep (se 1 (by rfl) ⟨2271857, by rfl⟩ : syracuseStep 3029143 = 4543715) B4543715
theorem B2693273 : Blo 1794098 2693273 := bstep (se 2 (by rfl) ⟨1009977, by rfl⟩ : syracuseStep 2693273 = 2019955) B2019955
theorem B4036787 : Blo 1794098 4036787 := bstep (se 1 (by rfl) ⟨3027590, by rfl⟩ : syracuseStep 4036787 = 6055181) B6055181
theorem B4036823 : Blo 1794098 4036823 := bstep (se 1 (by rfl) ⟨3027617, by rfl⟩ : syracuseStep 4036823 = 6055235) B6055235
theorem B2660569 : Blo 1794098 2660569 := bstep (se 2 (by rfl) ⟨997713, by rfl⟩ : syracuseStep 2660569 = 1995427) B1995427
theorem B2693387 : Blo 1794098 2693387 := bstep (se 1 (by rfl) ⟨2020040, by rfl⟩ : syracuseStep 2693387 = 4040081) B4040081
theorem B2693399 : Blo 1794098 2693399 := bstep (se 1 (by rfl) ⟨2020049, by rfl⟩ : syracuseStep 2693399 = 4040099) B4040099
theorem B6060311 : Blo 1794098 6060311 := bstep (se 1 (by rfl) ⟨4545233, by rfl⟩ : syracuseStep 6060311 = 9090467) B9090467
theorem B4544819 : Blo 1794098 4544819 := bstep (se 1 (by rfl) ⟨3408614, by rfl⟩ : syracuseStep 4544819 = 6817229) B6817229
theorem B2693465 : Blo 1794098 2693465 := bstep (se 2 (by rfl) ⟨1010049, by rfl⟩ : syracuseStep 2693465 = 2020099) B2020099
theorem B4037003 : Blo 1794098 4037003 := bstep (se 1 (by rfl) ⟨3027752, by rfl⟩ : syracuseStep 4037003 = 6055505) B6055505
theorem B12933553 : Blo 1794098 12933553 := bstep (se 2 (by rfl) ⟨4850082, by rfl⟩ : syracuseStep 12933553 = 9700165) B9700165
theorem B4037057 : Blo 1794098 4037057 := bstep (se 2 (by rfl) ⟨1513896, by rfl⟩ : syracuseStep 4037057 = 3027793) B3027793
theorem B6814145 : Blo 1794098 6814145 := bstep (se 2 (by rfl) ⟨2555304, by rfl⟩ : syracuseStep 6814145 = 5110609) B5110609
theorem B3406283 : Blo 1794098 3406283 := bstep (se 1 (by rfl) ⟨2554712, by rfl⟩ : syracuseStep 3406283 = 5109425) B5109425
theorem B2693579 : Blo 1794098 2693579 := bstep (se 1 (by rfl) ⟨2020184, by rfl⟩ : syracuseStep 2693579 = 4040369) B4040369
theorem B2693591 : Blo 1794098 2693591 := bstep (se 1 (by rfl) ⟨2020193, by rfl⟩ : syracuseStep 2693591 = 4040387) B4040387
theorem B9091601 : Blo 1794098 9091601 := bstep (se 2 (by rfl) ⟨3409350, by rfl⟩ : syracuseStep 9091601 = 6818701) B6818701
theorem B2693657 : Blo 1794098 2693657 := bstep (se 2 (by rfl) ⟨1010121, by rfl⟩ : syracuseStep 2693657 = 2020243) B2020243
theorem B3406465 : Blo 1794098 3406465 := bstep (se 2 (by rfl) ⟨1277424, by rfl⟩ : syracuseStep 3406465 = 2554849) B2554849
theorem B3234433 : Blo 1794098 3234433 := bstep (se 2 (by rfl) ⟨1212912, by rfl⟩ : syracuseStep 3234433 = 2425825) B2425825
theorem B2554507 : Blo 1794098 2554507 := bstep (se 1 (by rfl) ⟨1915880, by rfl⟩ : syracuseStep 2554507 = 3831761) B3831761
theorem B2693771 : Blo 1794098 2693771 := bstep (se 1 (by rfl) ⟨2020328, by rfl⟩ : syracuseStep 2693771 = 4040657) B4040657
theorem B2554519 : Blo 1794098 2554519 := bstep (se 1 (by rfl) ⟨1915889, by rfl⟩ : syracuseStep 2554519 = 3831779) B3831779
theorem B2693783 : Blo 1794098 2693783 := bstep (se 1 (by rfl) ⟨2020337, by rfl⟩ : syracuseStep 2693783 = 4040675) B4040675
theorem B4037273 : Blo 1794098 4037273 := bstep (se 2 (by rfl) ⟨1513977, by rfl⟩ : syracuseStep 4037273 = 3027955) B3027955
theorem B13818545 : Blo 1794098 13818545 := bstep (se 2 (by rfl) ⟨5181954, by rfl⟩ : syracuseStep 13818545 = 10363909) B10363909
theorem B9091763 : Blo 1794098 9091763 := bstep (se 1 (by rfl) ⟨6818822, by rfl⟩ : syracuseStep 9091763 = 13637645) B13637645
theorem B2693849 : Blo 1794098 2693849 := bstep (se 2 (by rfl) ⟨1010193, by rfl⟩ : syracuseStep 2693849 = 2020387) B2020387
theorem B4037363 : Blo 1794098 4037363 := bstep (se 1 (by rfl) ⟨3028022, by rfl⟩ : syracuseStep 4037363 = 6056045) B6056045
theorem B3029771 : Blo 1794098 3029771 := bstep (se 1 (by rfl) ⟨2272328, by rfl⟩ : syracuseStep 3029771 = 4544657) B4544657
theorem B4037399 : Blo 1794098 4037399 := bstep (se 1 (by rfl) ⟨3028049, by rfl⟩ : syracuseStep 4037399 = 6056099) B6056099
theorem B6060851 : Blo 1794098 6060851 := bstep (se 1 (by rfl) ⟨4545638, by rfl⟩ : syracuseStep 6060851 = 9091277) B9091277
theorem B4545355 : Blo 1794098 4545355 := bstep (se 1 (by rfl) ⟨3409016, by rfl⟩ : syracuseStep 4545355 = 6818033) B6818033
theorem B2693963 : Blo 1794098 2693963 := bstep (se 1 (by rfl) ⟨2020472, by rfl⟩ : syracuseStep 2693963 = 4040945) B4040945
theorem B2693975 : Blo 1794098 2693975 := bstep (se 1 (by rfl) ⟨2020481, by rfl⟩ : syracuseStep 2693975 = 4040963) B4040963
theorem B3029899 : Blo 1794098 3029899 := bstep (se 1 (by rfl) ⟨2272424, by rfl⟩ : syracuseStep 3029899 = 4544849) B4544849
theorem B12934039 : Blo 1794098 12934039 := bstep (se 1 (by rfl) ⟨9700529, by rfl⟩ : syracuseStep 12934039 = 19401059) B19401059
theorem B2694041 : Blo 1794098 2694041 := bstep (se 2 (by rfl) ⟨1010265, by rfl⟩ : syracuseStep 2694041 = 2020531) B2020531
theorem B4373441 : Blo 1794098 4373441 := bstep (se 2 (by rfl) ⟨1640040, by rfl⟩ : syracuseStep 4373441 = 3280081) B3280081
theorem B4037579 : Blo 1794098 4037579 := bstep (se 1 (by rfl) ⟨3028184, by rfl⟩ : syracuseStep 4037579 = 6056369) B6056369
theorem B4545497 : Blo 1794098 4545497 := bstep (se 2 (by rfl) ⟨1704561, by rfl⟩ : syracuseStep 4545497 = 3409123) B3409123
theorem B13638617 : Blo 1794098 13638617 := bstep (se 2 (by rfl) ⟨5114481, by rfl⟩ : syracuseStep 13638617 = 10228963) B10228963
theorem B4037633 : Blo 1794098 4037633 := bstep (se 2 (by rfl) ⟨1514112, by rfl⟩ : syracuseStep 4037633 = 3028225) B3028225
theorem B2874379 : Blo 1794098 2874379 := bstep (se 1 (by rfl) ⟨2155784, by rfl⟩ : syracuseStep 2874379 = 4311569) B4311569
theorem B3030041 : Blo 1794098 3030041 := bstep (se 2 (by rfl) ⟨1136265, by rfl⟩ : syracuseStep 3030041 = 2272531) B2272531
theorem B6061121 : Blo 1794098 6061121 := bstep (se 2 (by rfl) ⟨2272920, by rfl⟩ : syracuseStep 6061121 = 4545841) B4545841
theorem B1915979 : Blo 1794098 1915979 := bstep (se 1 (by rfl) ⟨1436984, by rfl⟩ : syracuseStep 1915979 = 2873969) B2873969
theorem B6814813 : Blo 1794098 6814813 := bstep (se 3 (by rfl) ⟨1277777, by rfl⟩ : syracuseStep 6814813 = 2555555) B2555555
theorem B3071129 : Blo 1794098 3071129 := bstep (se 2 (by rfl) ⟨1151673, by rfl⟩ : syracuseStep 3071129 = 2303347) B2303347
theorem B3030169 : Blo 1794098 3030169 := bstep (se 2 (by rfl) ⟨1136313, by rfl⟩ : syracuseStep 3030169 = 2272627) B2272627
theorem B3235009 : Blo 1794098 3235009 := bstep (se 2 (by rfl) ⟨1213128, by rfl⟩ : syracuseStep 3235009 = 2426257) B2426257
theorem B4037849 : Blo 1794098 4037849 := bstep (se 2 (by rfl) ⟨1514193, by rfl⟩ : syracuseStep 4037849 = 3028387) B3028387
theorem B4037939 : Blo 1794098 4037939 := bstep (se 1 (by rfl) ⟨3028454, by rfl⟩ : syracuseStep 4037939 = 6056909) B6056909
theorem B3407179 : Blo 1794098 3407179 := bstep (se 1 (by rfl) ⟨2555384, by rfl⟩ : syracuseStep 3407179 = 5110769) B5110769
theorem B4037975 : Blo 1794098 4037975 := bstep (se 1 (by rfl) ⟨3028481, by rfl⟩ : syracuseStep 4037975 = 6056963) B6056963
theorem B10222949 : Blo 1794098 10222949 := bstep (se 4 (by rfl) ⟨958401, by rfl⟩ : syracuseStep 10222949 = 1916803) B1916803
theorem B7667075 : Blo 1794098 7667075 := bstep (se 1 (by rfl) ⟨5750306, by rfl⟩ : syracuseStep 7667075 = 11500613) B11500613
theorem B9084311 : Blo 1794098 9084311 := bstep (se 1 (by rfl) ⟨6813233, by rfl⟩ : syracuseStep 9084311 = 13626467) B13626467
theorem B3407255 : Blo 1794098 3407255 := bstep (se 1 (by rfl) ⟨2555441, by rfl⟩ : syracuseStep 3407255 = 5110883) B5110883
theorem B2047447 : Blo 1794098 2047447 := bstep (se 1 (by rfl) ⟨1535585, by rfl⟩ : syracuseStep 2047447 = 3071171) B3071171
theorem B4038155 : Blo 1794098 4038155 := bstep (se 1 (by rfl) ⟨3028616, by rfl⟩ : syracuseStep 4038155 = 6057233) B6057233
theorem B4374067 : Blo 1794098 4374067 := bstep (se 1 (by rfl) ⟨3280550, by rfl⟩ : syracuseStep 4374067 = 6561101) B6561101
theorem B4038209 : Blo 1794098 4038209 := bstep (se 2 (by rfl) ⟨1514328, by rfl⟩ : syracuseStep 4038209 = 3028657) B3028657
theorem B3833419 : Blo 1794098 3833419 := bstep (se 1 (by rfl) ⟨2875064, by rfl⟩ : syracuseStep 3833419 = 5750129) B5750129
theorem B6061661 : Blo 1794098 6061661 := bstep (se 3 (by rfl) ⟨1136561, by rfl⟩ : syracuseStep 6061661 = 2273123) B2273123
theorem B30670487 : Blo 1794098 30670487 := bstep (se 1 (by rfl) ⟨23002865, by rfl⟩ : syracuseStep 30670487 = 46005731) B46005731
theorem B3030743 : Blo 1794098 3030743 := bstep (se 1 (by rfl) ⟨2273057, by rfl⟩ : syracuseStep 3030743 = 4546115) B4546115
theorem B2875097 : Blo 1794098 2875097 := bstep (se 2 (by rfl) ⟨1078161, by rfl⟩ : syracuseStep 2875097 = 2156323) B2156323
theorem B8986385 : Blo 1794098 8986385 := bstep (se 2 (by rfl) ⟨3369894, by rfl⟩ : syracuseStep 8986385 = 6739789) B6739789
theorem B4546327 : Blo 1794098 4546327 := bstep (se 1 (by rfl) ⟨3409745, by rfl⟩ : syracuseStep 4546327 = 6819491) B6819491
theorem B4038425 : Blo 1794098 4038425 := bstep (se 2 (by rfl) ⟨1514409, by rfl⟩ : syracuseStep 4038425 = 3028819) B3028819
theorem B10223405 : Blo 1794098 10223405 := bstep (se 3 (by rfl) ⟨1916888, by rfl⟩ : syracuseStep 10223405 = 3833777) B3833777
theorem B3030871 : Blo 1794098 3030871 := bstep (se 1 (by rfl) ⟨2273153, by rfl⟩ : syracuseStep 3030871 = 4546307) B4546307
theorem B3235673 : Blo 1794098 3235673 := bstep (se 2 (by rfl) ⟨1213377, by rfl⟩ : syracuseStep 3235673 = 2426755) B2426755
theorem B4038515 : Blo 1794098 4038515 := bstep (se 1 (by rfl) ⟨3028886, by rfl⟩ : syracuseStep 4038515 = 6057773) B6057773
theorem B4038551 : Blo 1794098 4038551 := bstep (se 1 (by rfl) ⟨3028913, by rfl⟩ : syracuseStep 4038551 = 6057827) B6057827
theorem B18677765 : Blo 1794098 18677765 := bstep (se 4 (by rfl) ⟨1751040, by rfl⟩ : syracuseStep 18677765 = 3502081) B3502081
theorem B1794107 : Blo 1794098 1794107 := bstep (se 1 (by rfl) ⟨1345580, by rfl⟩ : syracuseStep 1794107 = 2691161) B2691161
theorem B2555977 : Blo 1794098 2555977 := bstep (se 2 (by rfl) ⟨958491, by rfl⟩ : syracuseStep 2555977 = 1916983) B1916983
theorem B1794183 : Blo 1794098 1794183 := bstep (se 1 (by rfl) ⟨1345637, by rfl⟩ : syracuseStep 1794183 = 2691275) B2691275
theorem B3408007 : Blo 1794098 3408007 := bstep (se 1 (by rfl) ⟨2556005, by rfl⟩ : syracuseStep 3408007 = 5112011) B5112011
theorem B1794191 : Blo 1794098 1794191 := bstep (se 1 (by rfl) ⟨1345643, by rfl⟩ : syracuseStep 1794191 = 2691287) B2691287
theorem B4038803 : Blo 1794098 4038803 := bstep (se 1 (by rfl) ⟨3029102, by rfl⟩ : syracuseStep 4038803 = 6058205) B6058205
theorem B1794235 : Blo 1794098 1794235 := bstep (se 1 (by rfl) ⟨1345676, by rfl⟩ : syracuseStep 1794235 = 2691353) B2691353
theorem B9085121 : Blo 1794098 9085121 := bstep (se 2 (by rfl) ⟨3406920, by rfl⟩ : syracuseStep 9085121 = 6813841) B6813841
theorem B4038857 : Blo 1794098 4038857 := bstep (se 2 (by rfl) ⟨1514571, by rfl⟩ : syracuseStep 4038857 = 3029143) B3029143
theorem B1794311 : Blo 1794098 1794311 := bstep (se 1 (by rfl) ⟨1345733, by rfl⟩ : syracuseStep 1794311 = 2691467) B2691467
theorem B1794319 : Blo 1794098 1794319 := bstep (se 1 (by rfl) ⟨1345739, by rfl⟩ : syracuseStep 1794319 = 2691479) B2691479
theorem B3834145 : Blo 1794098 3834145 := bstep (se 2 (by rfl) ⟨1437804, by rfl⟩ : syracuseStep 3834145 = 2875609) B2875609
theorem B1794363 : Blo 1794098 1794363 := bstep (se 1 (by rfl) ⟨1345772, by rfl⟩ : syracuseStep 1794363 = 2691545) B2691545
theorem B6816059 : Blo 1794098 6816059 := bstep (se 1 (by rfl) ⟨5112044, by rfl⟩ : syracuseStep 6816059 = 10224089) B10224089
theorem B20455739 : Blo 1794098 20455739 := bstep (se 1 (by rfl) ⟨15341804, by rfl⟩ : syracuseStep 20455739 = 30683609) B30683609
theorem B1794439 : Blo 1794098 1794439 := bstep (se 1 (by rfl) ⟨1345829, by rfl⟩ : syracuseStep 1794439 = 2691659) B2691659
theorem B1794447 : Blo 1794098 1794447 := bstep (se 1 (by rfl) ⟨1345835, by rfl⟩ : syracuseStep 1794447 = 2691671) B2691671
theorem B1794491 : Blo 1794098 1794491 := bstep (se 1 (by rfl) ⟨1345868, by rfl⟩ : syracuseStep 1794491 = 2691737) B2691737
theorem B1794567 : Blo 1794098 1794567 := bstep (se 1 (by rfl) ⟨1345925, by rfl⟩ : syracuseStep 1794567 = 2691851) B2691851
theorem B1794575 : Blo 1794098 1794575 := bstep (se 1 (by rfl) ⟨1345931, by rfl⟩ : syracuseStep 1794575 = 2691863) B2691863
theorem B10920491 : Blo 1794098 10920491 := bstep (se 1 (by rfl) ⟨8190368, by rfl⟩ : syracuseStep 10920491 = 16380737) B16380737
theorem B1794619 : Blo 1794098 1794619 := bstep (se 1 (by rfl) ⟨1345964, by rfl⟩ : syracuseStep 1794619 = 2691929) B2691929
theorem B17244737 : Blo 1794098 17244737 := bstep (se 2 (by rfl) ⟨6466776, by rfl⟩ : syracuseStep 17244737 = 12933553) B12933553
theorem B15327863 : Blo 1794098 15327863 := bstep (se 1 (by rfl) ⟨11495897, by rfl⟩ : syracuseStep 15327863 = 22991795) B22991795
theorem B2556535 : Blo 1794098 2556535 := bstep (se 1 (by rfl) ⟨1917401, by rfl⟩ : syracuseStep 2556535 = 3834803) B3834803
theorem B1794695 : Blo 1794098 1794695 := bstep (se 1 (by rfl) ⟨1346021, by rfl⟩ : syracuseStep 1794695 = 2692043) B2692043
theorem B1794703 : Blo 1794098 1794703 := bstep (se 1 (by rfl) ⟨1346027, by rfl⟩ : syracuseStep 1794703 = 2692055) B2692055
theorem B5112467 : Blo 1794098 5112467 := bstep (se 1 (by rfl) ⟨3834350, by rfl⟩ : syracuseStep 5112467 = 7668701) B7668701
theorem B9700013 : Blo 1794098 9700013 := bstep (se 3 (by rfl) ⟨1818752, by rfl⟩ : syracuseStep 9700013 = 3637505) B3637505
theorem B44253877 : Blo 1794098 44253877 := bstep (se 5 (by rfl) ⟨2074400, by rfl⟩ : syracuseStep 44253877 = 4148801) B4148801
theorem B1794747 : Blo 1794098 1794747 := bstep (se 1 (by rfl) ⟨1346060, by rfl⟩ : syracuseStep 1794747 = 2692121) B2692121
theorem B13624037 : Blo 1794098 13624037 := bstep (se 4 (by rfl) ⟨1277253, by rfl⟩ : syracuseStep 13624037 = 2554507) B2554507
theorem B1794823 : Blo 1794098 1794823 := bstep (se 1 (by rfl) ⟨1346117, by rfl⟩ : syracuseStep 1794823 = 2692235) B2692235
theorem B1794831 : Blo 1794098 1794831 := bstep (se 1 (by rfl) ⟨1346123, by rfl⟩ : syracuseStep 1794831 = 2692247) B2692247
theorem B6816545 : Blo 1794098 6816545 := bstep (se 2 (by rfl) ⟨2556204, by rfl⟩ : syracuseStep 6816545 = 5112409) B5112409
theorem B4916027 : Blo 1794098 4916027 := bstep (se 1 (by rfl) ⟨3687020, by rfl⟩ : syracuseStep 4916027 = 7374041) B7374041
theorem B1794875 : Blo 1794098 1794875 := bstep (se 1 (by rfl) ⟨1346156, by rfl⟩ : syracuseStep 1794875 = 2692313) B2692313
theorem B1794951 : Blo 1794098 1794951 := bstep (se 1 (by rfl) ⟨1346213, by rfl⟩ : syracuseStep 1794951 = 2692427) B2692427
theorem B4039559 : Blo 1794098 4039559 := bstep (se 1 (by rfl) ⟨3029669, by rfl⟩ : syracuseStep 4039559 = 6059339) B6059339
theorem B1794959 : Blo 1794098 1794959 := bstep (se 1 (by rfl) ⟨1346219, by rfl⟩ : syracuseStep 1794959 = 2692439) B2692439
theorem B1795003 : Blo 1794098 1795003 := bstep (se 1 (by rfl) ⟨1346252, by rfl⟩ : syracuseStep 1795003 = 2692505) B2692505
theorem B1795079 : Blo 1794098 1795079 := bstep (se 1 (by rfl) ⟨1346309, by rfl⟩ : syracuseStep 1795079 = 2692619) B2692619
theorem B1795087 : Blo 1794098 1795087 := bstep (se 1 (by rfl) ⟨1346315, by rfl⟩ : syracuseStep 1795087 = 2692631) B2692631
theorem B1795131 : Blo 1794098 1795131 := bstep (se 1 (by rfl) ⟨1346348, by rfl⟩ : syracuseStep 1795131 = 2692697) B2692697
theorem B4039739 : Blo 1794098 4039739 := bstep (se 1 (by rfl) ⟨3029804, by rfl⟩ : syracuseStep 4039739 = 6059609) B6059609
theorem B14189701 : Blo 1794098 14189701 := bstep (se 4 (by rfl) ⟨1330284, by rfl⟩ : syracuseStep 14189701 = 2660569) B2660569
theorem B1795207 : Blo 1794098 1795207 := bstep (se 1 (by rfl) ⟨1346405, by rfl⟩ : syracuseStep 1795207 = 2692811) B2692811
theorem B1795215 : Blo 1794098 1795215 := bstep (se 1 (by rfl) ⟨1346411, by rfl⟩ : syracuseStep 1795215 = 2692823) B2692823
theorem B2557099 : Blo 1794098 2557099 := bstep (se 1 (by rfl) ⟨1917824, by rfl⟩ : syracuseStep 2557099 = 3835649) B3835649
theorem B4605113 : Blo 1794098 4605113 := bstep (se 2 (by rfl) ⟨1726917, by rfl⟩ : syracuseStep 4605113 = 3453835) B3453835
theorem B2426041 : Blo 1794098 2426041 := bstep (se 2 (by rfl) ⟨909765, by rfl⟩ : syracuseStep 2426041 = 1819531) B1819531
theorem B1795259 : Blo 1794098 1795259 := bstep (se 1 (by rfl) ⟨1346444, by rfl⟩ : syracuseStep 1795259 = 2692889) B2692889
theorem B4039865 : Blo 1794098 4039865 := bstep (se 2 (by rfl) ⟨1514949, by rfl⟩ : syracuseStep 4039865 = 3029899) B3029899
theorem B17245385 : Blo 1794098 17245385 := bstep (se 2 (by rfl) ⟨6467019, by rfl⟩ : syracuseStep 17245385 = 12934039) B12934039
theorem B1795335 : Blo 1794098 1795335 := bstep (se 1 (by rfl) ⟨1346501, by rfl⟩ : syracuseStep 1795335 = 2693003) B2693003
theorem B1795343 : Blo 1794098 1795343 := bstep (se 1 (by rfl) ⟨1346507, by rfl⟩ : syracuseStep 1795343 = 2693015) B2693015
theorem B7669025 : Blo 1794098 7669025 := bstep (se 2 (by rfl) ⟨2875884, by rfl⟩ : syracuseStep 7669025 = 5751769) B5751769
theorem B1795387 : Blo 1794098 1795387 := bstep (se 1 (by rfl) ⟨1346540, by rfl⟩ : syracuseStep 1795387 = 2693081) B2693081
theorem B18679099 : Blo 1794098 18679099 := bstep (se 1 (by rfl) ⟨14009324, by rfl⟩ : syracuseStep 18679099 = 28018649) B28018649
theorem B1795463 : Blo 1794098 1795463 := bstep (se 1 (by rfl) ⟨1346597, by rfl⟩ : syracuseStep 1795463 = 2693195) B2693195
theorem B1795471 : Blo 1794098 1795471 := bstep (se 1 (by rfl) ⟨1346603, by rfl⟩ : syracuseStep 1795471 = 2693207) B2693207
theorem B2557327 : Blo 1794098 2557327 := bstep (se 1 (by rfl) ⟨1917995, by rfl⟩ : syracuseStep 2557327 = 3835991) B3835991
theorem B1795515 : Blo 1794098 1795515 := bstep (se 1 (by rfl) ⟨1346636, by rfl⟩ : syracuseStep 1795515 = 2693273) B2693273
theorem B9086417 : Blo 1794098 9086417 := bstep (se 2 (by rfl) ⟨3407406, by rfl⟩ : syracuseStep 9086417 = 6814813) B6814813
theorem B1795591 : Blo 1794098 1795591 := bstep (se 1 (by rfl) ⟨1346693, by rfl⟩ : syracuseStep 1795591 = 2693387) B2693387
theorem B1795599 : Blo 1794098 1795599 := bstep (se 1 (by rfl) ⟨1346699, by rfl⟩ : syracuseStep 1795599 = 2693399) B2693399
theorem B4040207 : Blo 1794098 4040207 := bstep (se 1 (by rfl) ⟨3030155, by rfl⟩ : syracuseStep 4040207 = 6060311) B6060311
theorem B4040225 : Blo 1794098 4040225 := bstep (se 2 (by rfl) ⟨1515084, by rfl⟩ : syracuseStep 4040225 = 3030169) B3030169
theorem B1795643 : Blo 1794098 1795643 := bstep (se 1 (by rfl) ⟨1346732, by rfl⟩ : syracuseStep 1795643 = 2693465) B2693465
theorem B2270855 : Blo 1794098 2270855 := bstep (se 1 (by rfl) ⟨1703141, by rfl⟩ : syracuseStep 2270855 = 3406283) B3406283
theorem B1795719 : Blo 1794098 1795719 := bstep (se 1 (by rfl) ⟨1346789, by rfl⟩ : syracuseStep 1795719 = 2693579) B2693579
theorem B1795727 : Blo 1794098 1795727 := bstep (se 1 (by rfl) ⟨1346795, by rfl⟩ : syracuseStep 1795727 = 2693591) B2693591
theorem B1795771 : Blo 1794098 1795771 := bstep (se 1 (by rfl) ⟨1346828, by rfl⟩ : syracuseStep 1795771 = 2693657) B2693657
theorem B3409609 : Blo 1794098 3409609 := bstep (se 2 (by rfl) ⟨1278603, by rfl⟩ : syracuseStep 3409609 = 2557207) B2557207
theorem B6817517 : Blo 1794098 6817517 := bstep (se 3 (by rfl) ⟨1278284, by rfl⟩ : syracuseStep 6817517 = 2556569) B2556569
theorem B1795847 : Blo 1794098 1795847 := bstep (se 1 (by rfl) ⟨1346885, by rfl⟩ : syracuseStep 1795847 = 2693771) B2693771
theorem B1795855 : Blo 1794098 1795855 := bstep (se 1 (by rfl) ⟨1346891, by rfl⟩ : syracuseStep 1795855 = 2693783) B2693783
theorem B3835691 : Blo 1794098 3835691 := bstep (se 1 (by rfl) ⟨2876768, by rfl⟩ : syracuseStep 3835691 = 5753537) B5753537
theorem B1795899 : Blo 1794098 1795899 := bstep (se 1 (by rfl) ⟨1346924, by rfl⟩ : syracuseStep 1795899 = 2693849) B2693849
theorem B5752691 : Blo 1794098 5752691 := bstep (se 1 (by rfl) ⟨4314518, by rfl⟩ : syracuseStep 5752691 = 8629037) B8629037
theorem B4040567 : Blo 1794098 4040567 := bstep (se 1 (by rfl) ⟨3030425, by rfl⟩ : syracuseStep 4040567 = 6060851) B6060851
theorem B1795975 : Blo 1794098 1795975 := bstep (se 1 (by rfl) ⟨1346981, by rfl⟩ : syracuseStep 1795975 = 2693963) B2693963
theorem B1795983 : Blo 1794098 1795983 := bstep (se 1 (by rfl) ⟨1346987, by rfl⟩ : syracuseStep 1795983 = 2693975) B2693975
theorem B1796027 : Blo 1794098 1796027 := bstep (se 1 (by rfl) ⟨1347020, by rfl⟩ : syracuseStep 1796027 = 2694041) B2694041
theorem B131049413 : Blo 1794098 131049413 := bstep (se 4 (by rfl) ⟨12285882, by rfl⟩ : syracuseStep 131049413 = 24571765) B24571765
theorem B2729929 : Blo 1794098 2729929 := bstep (se 2 (by rfl) ⟨1023723, by rfl⟩ : syracuseStep 2729929 = 2047447) B2047447
theorem B5113867 : Blo 1794098 5113867 := bstep (se 1 (by rfl) ⟨3835400, by rfl⟩ : syracuseStep 5113867 = 7670801) B7670801
theorem B4040747 : Blo 1794098 4040747 := bstep (se 1 (by rfl) ⟨3030560, by rfl⟩ : syracuseStep 4040747 = 6061121) B6061121
theorem B15337673 : Blo 1794098 15337673 := bstep (se 2 (by rfl) ⟨5751627, by rfl⟩ : syracuseStep 15337673 = 11503255) B11503255
theorem B10225865 : Blo 1794098 10225865 := bstep (se 2 (by rfl) ⟨3834699, by rfl⟩ : syracuseStep 10225865 = 7669399) B7669399
theorem B6056207 : Blo 1794098 6056207 := bstep (se 1 (by rfl) ⟨4542155, by rfl⟩ : syracuseStep 6056207 = 9084311) B9084311
theorem B2271503 : Blo 1794098 2271503 := bstep (se 1 (by rfl) ⟨1703627, by rfl⟩ : syracuseStep 2271503 = 3407255) B3407255
theorem B5114141 : Blo 1794098 5114141 := bstep (se 3 (by rfl) ⟨958901, by rfl⟩ : syracuseStep 5114141 = 1917803) B1917803
theorem B4311443 : Blo 1794098 4311443 := bstep (se 1 (by rfl) ⟨3233582, by rfl⟩ : syracuseStep 4311443 = 6467165) B6467165
theorem B4041107 : Blo 1794098 4041107 := bstep (se 1 (by rfl) ⟨3030830, by rfl⟩ : syracuseStep 4041107 = 6061661) B6061661
theorem B6818201 : Blo 1794098 6818201 := bstep (se 2 (by rfl) ⟨2556825, by rfl⟩ : syracuseStep 6818201 = 5113651) B5113651
theorem B4041161 : Blo 1794098 4041161 := bstep (se 2 (by rfl) ⟨1515435, by rfl⟩ : syracuseStep 4041161 = 3030871) B3030871
theorem B5990923 : Blo 1794098 5990923 := bstep (se 1 (by rfl) ⟨4493192, by rfl⟩ : syracuseStep 5990923 = 8986385) B8986385
theorem B6056477 : Blo 1794098 6056477 := bstep (se 3 (by rfl) ⟨1135589, by rfl⟩ : syracuseStep 6056477 = 2271179) B2271179
theorem B2157115 : Blo 1794098 2157115 := bstep (se 1 (by rfl) ⟨1617836, by rfl⟩ : syracuseStep 2157115 = 3235673) B3235673
theorem B4918457 : Blo 1794098 4918457 := bstep (se 2 (by rfl) ⟨1844421, by rfl⟩ : syracuseStep 4918457 = 3688843) B3688843
theorem B5180683 : Blo 1794098 5180683 := bstep (se 1 (by rfl) ⟨3885512, by rfl⟩ : syracuseStep 5180683 = 7771025) B7771025
theorem B8629537 : Blo 1794098 8629537 := bstep (se 2 (by rfl) ⟨3236076, by rfl⟩ : syracuseStep 8629537 = 6472153) B6472153
theorem B6819187 : Blo 1794098 6819187 := bstep (se 1 (by rfl) ⟨5114390, by rfl⟩ : syracuseStep 6819187 = 10228781) B10228781
theorem B2018695 : Blo 1794098 2018695 := bstep (se 1 (by rfl) ⟨1514021, by rfl⟩ : syracuseStep 2018695 = 3028043) B3028043
theorem B9702865 : Blo 1794098 9702865 := bstep (se 2 (by rfl) ⟨3638574, by rfl⟩ : syracuseStep 9702865 = 7277149) B7277149
theorem B4541953 : Blo 1794098 4541953 := bstep (se 2 (by rfl) ⟨1703232, by rfl⟩ : syracuseStep 4541953 = 3406465) B3406465
theorem B4312577 : Blo 1794098 4312577 := bstep (se 2 (by rfl) ⟨1617216, by rfl⟩ : syracuseStep 4312577 = 3234433) B3234433
theorem B9088523 : Blo 1794098 9088523 := bstep (se 1 (by rfl) ⟨6816392, by rfl⟩ : syracuseStep 9088523 = 13632785) B13632785
theorem B10219031 : Blo 1794098 10219031 := bstep (se 1 (by rfl) ⟨7664273, by rfl⟩ : syracuseStep 10219031 = 15328547) B15328547
theorem B9702935 : Blo 1794098 9702935 := bstep (se 1 (by rfl) ⟨7277201, by rfl⟩ : syracuseStep 9702935 = 14554403) B14554403
theorem B2018875 : Blo 1794098 2018875 := bstep (se 1 (by rfl) ⟨1514156, by rfl⟩ : syracuseStep 2018875 = 3028313) B3028313
theorem B9088685 : Blo 1794098 9088685 := bstep (se 3 (by rfl) ⟨1704128, by rfl⟩ : syracuseStep 9088685 = 3408257) B3408257
theorem B6057881 : Blo 1794098 6057881 := bstep (se 2 (by rfl) ⟨2271705, by rfl⟩ : syracuseStep 6057881 = 4543411) B4543411
theorem B2019343 : Blo 1794098 2019343 := bstep (se 1 (by rfl) ⟨1514507, by rfl⟩ : syracuseStep 2019343 = 3029015) B3029015
theorem B6467627 : Blo 1794098 6467627 := bstep (se 1 (by rfl) ⟨4850720, by rfl⟩ : syracuseStep 6467627 = 9701441) B9701441
theorem B4853803 : Blo 1794098 4853803 := bstep (se 1 (by rfl) ⟨3640352, by rfl⟩ : syracuseStep 4853803 = 7280705) B7280705
theorem B10227779 : Blo 1794098 10227779 := bstep (se 1 (by rfl) ⟨7670834, by rfl⟩ : syracuseStep 10227779 = 15341669) B15341669
theorem B4542551 : Blo 1794098 4542551 := bstep (se 1 (by rfl) ⟨3406913, by rfl⟩ : syracuseStep 4542551 = 6813827) B6813827
theorem B2691191 : Blo 1794098 2691191 := bstep (se 1 (by rfl) ⟨2018393, by rfl⟩ : syracuseStep 2691191 = 4036787) B4036787
theorem B2691215 : Blo 1794098 2691215 := bstep (se 1 (by rfl) ⟨2018411, by rfl⟩ : syracuseStep 2691215 = 4036823) B4036823
theorem B2691257 : Blo 1794098 2691257 := bstep (se 2 (by rfl) ⟨1009221, by rfl⟩ : syracuseStep 2691257 = 2018443) B2018443
theorem B4313345 : Blo 1794098 4313345 := bstep (se 2 (by rfl) ⟨1617504, by rfl⟩ : syracuseStep 4313345 = 3235009) B3235009
theorem B2691335 : Blo 1794098 2691335 := bstep (se 1 (by rfl) ⟨2018501, by rfl⟩ : syracuseStep 2691335 = 4037003) B4037003
theorem B2691371 : Blo 1794098 2691371 := bstep (se 1 (by rfl) ⟨2018528, by rfl⟩ : syracuseStep 2691371 = 4037057) B4037057
theorem B4542763 : Blo 1794098 4542763 := bstep (se 1 (by rfl) ⟨3407072, by rfl⟩ : syracuseStep 4542763 = 6814145) B6814145
theorem B2691401 : Blo 1794098 2691401 := bstep (se 2 (by rfl) ⟨1009275, by rfl⟩ : syracuseStep 2691401 = 2018551) B2018551
theorem B8622521 : Blo 1794098 8622521 := bstep (se 2 (by rfl) ⟨3233445, by rfl⟩ : syracuseStep 8622521 = 6466891) B6466891
theorem B4542905 : Blo 1794098 4542905 := bstep (se 2 (by rfl) ⟨1703589, by rfl⟩ : syracuseStep 4542905 = 3407179) B3407179
theorem B2691515 : Blo 1794098 2691515 := bstep (se 1 (by rfl) ⟨2018636, by rfl⟩ : syracuseStep 2691515 = 4037273) B4037273
theorem B9212363 : Blo 1794098 9212363 := bstep (se 1 (by rfl) ⟨6909272, by rfl⟩ : syracuseStep 9212363 = 13818545) B13818545
theorem B11497949 : Blo 1794098 11497949 := bstep (se 3 (by rfl) ⟨2155865, by rfl⟩ : syracuseStep 11497949 = 4311731) B4311731
theorem B17248733 : Blo 1794098 17248733 := bstep (se 3 (by rfl) ⟨3234137, by rfl⟩ : syracuseStep 17248733 = 6468275) B6468275
theorem B2691575 : Blo 1794098 2691575 := bstep (se 1 (by rfl) ⟨2018681, by rfl⟩ : syracuseStep 2691575 = 4037363) B4037363
theorem B2019847 : Blo 1794098 2019847 := bstep (se 1 (by rfl) ⟨1514885, by rfl⟩ : syracuseStep 2019847 = 3029771) B3029771
theorem B6812171 : Blo 1794098 6812171 := bstep (se 1 (by rfl) ⟨5109128, by rfl⟩ : syracuseStep 6812171 = 10218257) B10218257
theorem B2691599 : Blo 1794098 2691599 := bstep (se 1 (by rfl) ⟨2018699, by rfl⟩ : syracuseStep 2691599 = 4037399) B4037399
theorem B2691641 : Blo 1794098 2691641 := bstep (se 2 (by rfl) ⟨1009365, by rfl⟩ : syracuseStep 2691641 = 2018731) B2018731
theorem B11498051 : Blo 1794098 11498051 := bstep (se 1 (by rfl) ⟨8623538, by rfl⟩ : syracuseStep 11498051 = 17247077) B17247077
theorem B6058583 : Blo 1794098 6058583 := bstep (se 1 (by rfl) ⟨4543937, by rfl⟩ : syracuseStep 6058583 = 9087875) B9087875
theorem B2691719 : Blo 1794098 2691719 := bstep (se 1 (by rfl) ⟨2018789, by rfl⟩ : syracuseStep 2691719 = 4037579) B4037579
theorem B2691755 : Blo 1794098 2691755 := bstep (se 1 (by rfl) ⟨2018816, by rfl⟩ : syracuseStep 2691755 = 4037633) B4037633
theorem B2020027 : Blo 1794098 2020027 := bstep (se 1 (by rfl) ⟨1515020, by rfl⟩ : syracuseStep 2020027 = 3030041) B3030041
theorem B2691785 : Blo 1794098 2691785 := bstep (se 2 (by rfl) ⟨1009419, by rfl⟩ : syracuseStep 2691785 = 2018839) B2018839
theorem B17249075 : Blo 1794098 17249075 := bstep (se 1 (by rfl) ⟨12936806, by rfl⟩ : syracuseStep 17249075 = 25873613) B25873613
theorem B2691899 : Blo 1794098 2691899 := bstep (se 1 (by rfl) ⟨2018924, by rfl⟩ : syracuseStep 2691899 = 4037849) B4037849
theorem B2691959 : Blo 1794098 2691959 := bstep (se 1 (by rfl) ⟨2018969, by rfl⟩ : syracuseStep 2691959 = 4037939) B4037939
theorem B3027847 : Blo 1794098 3027847 := bstep (se 1 (by rfl) ⟨2270885, by rfl⟩ : syracuseStep 3027847 = 4541771) B4541771
theorem B2691983 : Blo 1794098 2691983 := bstep (se 1 (by rfl) ⟨2018987, by rfl⟩ : syracuseStep 2691983 = 4037975) B4037975
theorem B2692025 : Blo 1794098 2692025 := bstep (se 2 (by rfl) ⟨1009509, by rfl⟩ : syracuseStep 2692025 = 2019019) B2019019
theorem B2692103 : Blo 1794098 2692103 := bstep (se 1 (by rfl) ⟨2019077, by rfl⟩ : syracuseStep 2692103 = 4038155) B4038155
theorem B7664651 : Blo 1794098 7664651 := bstep (se 1 (by rfl) ⟨5748488, by rfl⟩ : syracuseStep 7664651 = 11496977) B11496977
theorem B2692139 : Blo 1794098 2692139 := bstep (se 1 (by rfl) ⟨2019104, by rfl⟩ : syracuseStep 2692139 = 4038209) B4038209
theorem B6059069 : Blo 1794098 6059069 := bstep (se 3 (by rfl) ⟨1136075, by rfl⟩ : syracuseStep 6059069 = 2272151) B2272151
theorem B2692169 : Blo 1794098 2692169 := bstep (se 2 (by rfl) ⟨1009563, by rfl⟩ : syracuseStep 2692169 = 2019127) B2019127
theorem B2020495 : Blo 1794098 2020495 := bstep (se 1 (by rfl) ⟨1515371, by rfl⟩ : syracuseStep 2020495 = 3030743) B3030743
theorem B2692283 : Blo 1794098 2692283 := bstep (se 1 (by rfl) ⟨2019212, by rfl⟩ : syracuseStep 2692283 = 4038425) B4038425
theorem B2692343 : Blo 1794098 2692343 := bstep (se 1 (by rfl) ⟨2019257, by rfl⟩ : syracuseStep 2692343 = 4038515) B4038515
theorem B9090305 : Blo 1794098 9090305 := bstep (se 2 (by rfl) ⟨3408864, by rfl⟩ : syracuseStep 9090305 = 6817729) B6817729
theorem B2692367 : Blo 1794098 2692367 := bstep (se 1 (by rfl) ⟨2019275, by rfl⟩ : syracuseStep 2692367 = 4038551) B4038551
theorem B4371727 : Blo 1794098 4371727 := bstep (se 1 (by rfl) ⟨3278795, by rfl⟩ : syracuseStep 4371727 = 6557591) B6557591
theorem B2692409 : Blo 1794098 2692409 := bstep (se 2 (by rfl) ⟨1009653, by rfl⟩ : syracuseStep 2692409 = 2019307) B2019307
theorem B2692487 : Blo 1794098 2692487 := bstep (se 1 (by rfl) ⟨2019365, by rfl⟩ : syracuseStep 2692487 = 4038731) B4038731
theorem B65533319 : Blo 1794098 65533319 := bstep (se 1 (by rfl) ⟨49149989, by rfl⟩ : syracuseStep 65533319 = 98299979) B98299979
theorem B4543897 : Blo 1794098 4543897 := bstep (se 2 (by rfl) ⟨1703961, by rfl⟩ : syracuseStep 4543897 = 3407923) B3407923
theorem B2692523 : Blo 1794098 2692523 := bstep (se 1 (by rfl) ⟨2019392, by rfl⟩ : syracuseStep 2692523 = 4038785) B4038785
theorem B15340985 : Blo 1794098 15340985 := bstep (se 2 (by rfl) ⟨5752869, by rfl⟩ : syracuseStep 15340985 = 11505739) B11505739
theorem B2692553 : Blo 1794098 2692553 := bstep (se 2 (by rfl) ⟨1009707, by rfl⟩ : syracuseStep 2692553 = 2019415) B2019415
theorem B3028495 : Blo 1794098 3028495 := bstep (se 1 (by rfl) ⟨2271371, by rfl⟩ : syracuseStep 3028495 = 4542743) B4542743
theorem B5109277 : Blo 1794098 5109277 := bstep (se 3 (by rfl) ⟨957989, by rfl⟩ : syracuseStep 5109277 = 1915979) B1915979
theorem B2692667 : Blo 1794098 2692667 := bstep (se 1 (by rfl) ⟨2019500, by rfl⟩ : syracuseStep 2692667 = 4039001) B4039001
theorem B4544059 : Blo 1794098 4544059 := bstep (se 1 (by rfl) ⟨3408044, by rfl⟩ : syracuseStep 4544059 = 6816089) B6816089
theorem B2692727 : Blo 1794098 2692727 := bstep (se 1 (by rfl) ⟨2019545, by rfl⟩ : syracuseStep 2692727 = 4039091) B4039091
theorem B2692751 : Blo 1794098 2692751 := bstep (se 1 (by rfl) ⟨2019563, by rfl⟩ : syracuseStep 2692751 = 4039127) B4039127
theorem B2692793 : Blo 1794098 2692793 := bstep (se 2 (by rfl) ⟨1009797, by rfl⟩ : syracuseStep 2692793 = 2019595) B2019595
theorem B4544201 : Blo 1794098 4544201 := bstep (se 2 (by rfl) ⟨1704075, by rfl⟩ : syracuseStep 4544201 = 3408151) B3408151
theorem B19404517 : Blo 1794098 19404517 := bstep (se 4 (by rfl) ⟨1819173, by rfl⟩ : syracuseStep 19404517 = 3638347) B3638347
theorem B8189677 : Blo 1794098 8189677 := bstep (se 3 (by rfl) ⟨1535564, by rfl⟩ : syracuseStep 8189677 = 3071129) B3071129
theorem B7878401 : Blo 1794098 7878401 := bstep (se 2 (by rfl) ⟨2954400, by rfl⟩ : syracuseStep 7878401 = 5908801) B5908801
theorem B2692871 : Blo 1794098 2692871 := bstep (se 1 (by rfl) ⟨2019653, by rfl⟩ : syracuseStep 2692871 = 4039307) B4039307
theorem B2692907 : Blo 1794098 2692907 := bstep (se 1 (by rfl) ⟨2019680, by rfl⟩ : syracuseStep 2692907 = 4039361) B4039361
theorem B20436785 : Blo 1794098 20436785 := bstep (se 2 (by rfl) ⟨7663794, by rfl⟩ : syracuseStep 20436785 = 15327589) B15327589
theorem B2692937 : Blo 1794098 2692937 := bstep (se 2 (by rfl) ⟨1009851, by rfl⟩ : syracuseStep 2692937 = 2019703) B2019703
theorem B4921175 : Blo 1794098 4921175 := bstep (se 1 (by rfl) ⟨3690881, by rfl⟩ : syracuseStep 4921175 = 7381763) B7381763
theorem B3233683 : Blo 1794098 3233683 := bstep (se 1 (by rfl) ⟨2425262, by rfl⟩ : syracuseStep 3233683 = 4850525) B4850525
theorem B2693051 : Blo 1794098 2693051 := bstep (se 1 (by rfl) ⟨2019788, by rfl⟩ : syracuseStep 2693051 = 4039577) B4039577
theorem B18413515 : Blo 1794098 18413515 := bstep (se 1 (by rfl) ⟨13810136, by rfl⟩ : syracuseStep 18413515 = 27620273) B27620273
theorem B2693111 : Blo 1794098 2693111 := bstep (se 1 (by rfl) ⟨2019833, by rfl⟩ : syracuseStep 2693111 = 4039667) B4039667
theorem B2693135 : Blo 1794098 2693135 := bstep (se 1 (by rfl) ⟨2019851, by rfl⟩ : syracuseStep 2693135 = 4039703) B4039703
theorem B4544545 : Blo 1794098 4544545 := bstep (se 2 (by rfl) ⟨1704204, by rfl⟩ : syracuseStep 4544545 = 3408409) B3408409
theorem B3029035 : Blo 1794098 3029035 := bstep (se 1 (by rfl) ⟨2271776, by rfl⟩ : syracuseStep 3029035 = 4543553) B4543553
theorem B9091115 : Blo 1794098 9091115 := bstep (se 1 (by rfl) ⟨6818336, by rfl⟩ : syracuseStep 9091115 = 13636673) B13636673
theorem B21837869 : Blo 1794098 21837869 := bstep (se 3 (by rfl) ⟨4094600, by rfl⟩ : syracuseStep 21837869 = 8189201) B8189201
theorem B2693177 : Blo 1794098 2693177 := bstep (se 2 (by rfl) ⟨1009941, by rfl⟩ : syracuseStep 2693177 = 2019883) B2019883
theorem B2693255 : Blo 1794098 2693255 := bstep (se 1 (by rfl) ⟨2019941, by rfl⟩ : syracuseStep 2693255 = 4039883) B4039883
theorem B2693291 : Blo 1794098 2693291 := bstep (se 1 (by rfl) ⟨2019968, by rfl⟩ : syracuseStep 2693291 = 4039937) B4039937
theorem B51763373 : Blo 1794098 51763373 := bstep (se 3 (by rfl) ⟨9705632, by rfl⟩ : syracuseStep 51763373 = 19411265) B19411265
theorem B3029177 : Blo 1794098 3029177 := bstep (se 2 (by rfl) ⟨1135941, by rfl⟩ : syracuseStep 3029177 = 2271883) B2271883
theorem B3406025 : Blo 1794098 3406025 := bstep (se 2 (by rfl) ⟨1277259, by rfl⟩ : syracuseStep 3406025 = 2554519) B2554519
theorem B2693321 : Blo 1794098 2693321 := bstep (se 2 (by rfl) ⟨1009995, by rfl⟩ : syracuseStep 2693321 = 2019991) B2019991
theorem B2693435 : Blo 1794098 2693435 := bstep (se 1 (by rfl) ⟨2020076, by rfl⟩ : syracuseStep 2693435 = 4040153) B4040153
theorem B20445533 : Blo 1794098 20445533 := bstep (se 3 (by rfl) ⟨3833537, by rfl⟩ : syracuseStep 20445533 = 7667075) B7667075
theorem B2693495 : Blo 1794098 2693495 := bstep (se 1 (by rfl) ⟨2020121, by rfl⟩ : syracuseStep 2693495 = 4040243) B4040243
theorem B17250691 : Blo 1794098 17250691 := bstep (se 1 (by rfl) ⟨12938018, by rfl⟩ : syracuseStep 17250691 = 25876037) B25876037
theorem B2693519 : Blo 1794098 2693519 := bstep (se 1 (by rfl) ⟨2020139, by rfl⟩ : syracuseStep 2693519 = 4040279) B4040279
theorem B6060473 : Blo 1794098 6060473 := bstep (se 2 (by rfl) ⟨2272677, by rfl⟩ : syracuseStep 6060473 = 4545355) B4545355
theorem B2693561 : Blo 1794098 2693561 := bstep (se 2 (by rfl) ⟨1010085, by rfl⟩ : syracuseStep 2693561 = 2020171) B2020171
theorem B9083339 : Blo 1794098 9083339 := bstep (se 1 (by rfl) ⟨6812504, by rfl⟩ : syracuseStep 9083339 = 13625009) B13625009
theorem B2693639 : Blo 1794098 2693639 := bstep (se 1 (by rfl) ⟨2020229, by rfl⟩ : syracuseStep 2693639 = 4040459) B4040459
theorem B2955791 : Blo 1794098 2955791 := bstep (se 1 (by rfl) ⟨2216843, by rfl⟩ : syracuseStep 2955791 = 4433687) B4433687
theorem B2693675 : Blo 1794098 2693675 := bstep (se 1 (by rfl) ⟨2020256, by rfl⟩ : syracuseStep 2693675 = 4040513) B4040513
theorem B2693705 : Blo 1794098 2693705 := bstep (se 2 (by rfl) ⟨1010139, by rfl⟩ : syracuseStep 2693705 = 2020279) B2020279
theorem B6814327 : Blo 1794098 6814327 := bstep (se 1 (by rfl) ⟨5110745, by rfl⟩ : syracuseStep 6814327 = 10221491) B10221491
theorem B10222199 : Blo 1794098 10222199 := bstep (se 1 (by rfl) ⟨7666649, by rfl⟩ : syracuseStep 10222199 = 15333299) B15333299
theorem B4545143 : Blo 1794098 4545143 := bstep (se 1 (by rfl) ⟨3408857, by rfl⟩ : syracuseStep 4545143 = 6817715) B6817715
theorem B4037255 : Blo 1794098 4037255 := bstep (se 1 (by rfl) ⟨3027941, by rfl⟩ : syracuseStep 4037255 = 6055883) B6055883
theorem B3832505 : Blo 1794098 3832505 := bstep (se 2 (by rfl) ⟨1437189, by rfl⟩ : syracuseStep 3832505 = 2874379) B2874379
theorem B2693819 : Blo 1794098 2693819 := bstep (se 1 (by rfl) ⟨2020364, by rfl⟩ : syracuseStep 2693819 = 4040729) B4040729
theorem B2693879 : Blo 1794098 2693879 := bstep (se 1 (by rfl) ⟨2020409, by rfl⟩ : syracuseStep 2693879 = 4040819) B4040819
theorem B9083663 : Blo 1794098 9083663 := bstep (se 1 (by rfl) ⟨6812747, by rfl⟩ : syracuseStep 9083663 = 13625495) B13625495
theorem B2693903 : Blo 1794098 2693903 := bstep (se 1 (by rfl) ⟨2020427, by rfl⟩ : syracuseStep 2693903 = 4040855) B4040855
theorem B2693945 : Blo 1794098 2693945 := bstep (se 2 (by rfl) ⟨1010229, by rfl⟩ : syracuseStep 2693945 = 2020459) B2020459
theorem B4037435 : Blo 1794098 4037435 := bstep (se 1 (by rfl) ⟨3028076, by rfl⟩ : syracuseStep 4037435 = 6056153) B6056153
theorem B3029879 : Blo 1794098 3029879 := bstep (se 1 (by rfl) ⟨2272409, by rfl⟩ : syracuseStep 3029879 = 4544819) B4544819
theorem B2694023 : Blo 1794098 2694023 := bstep (se 1 (by rfl) ⟨2020517, by rfl⟩ : syracuseStep 2694023 = 4041035) B4041035
theorem B2694059 : Blo 1794098 2694059 := bstep (se 1 (by rfl) ⟨2020544, by rfl⟩ : syracuseStep 2694059 = 4041089) B4041089
theorem B4037561 : Blo 1794098 4037561 := bstep (se 2 (by rfl) ⟨1514085, by rfl⟩ : syracuseStep 4037561 = 3028171) B3028171
theorem B2694089 : Blo 1794098 2694089 := bstep (se 2 (by rfl) ⟨1010283, by rfl⟩ : syracuseStep 2694089 = 2020567) B2020567
theorem B6061067 : Blo 1794098 6061067 := bstep (se 1 (by rfl) ⟨4545800, by rfl⟩ : syracuseStep 6061067 = 9091601) B9091601
theorem B6061175 : Blo 1794098 6061175 := bstep (se 1 (by rfl) ⟨4545881, by rfl⟩ : syracuseStep 6061175 = 9091763) B9091763
theorem B4037903 : Blo 1794098 4037903 := bstep (se 1 (by rfl) ⟨3028427, by rfl⟩ : syracuseStep 4037903 = 6056855) B6056855
theorem B4037921 : Blo 1794098 4037921 := bstep (se 2 (by rfl) ⟨1514220, by rfl⟩ : syracuseStep 4037921 = 3028441) B3028441
theorem B2915627 : Blo 1794098 2915627 := bstep (se 1 (by rfl) ⟨2186720, by rfl⟩ : syracuseStep 2915627 = 4373441) B4373441
theorem B3030331 : Blo 1794098 3030331 := bstep (se 1 (by rfl) ⟨2272748, by rfl⟩ : syracuseStep 3030331 = 4545497) B4545497
theorem B9092411 : Blo 1794098 9092411 := bstep (se 1 (by rfl) ⟨6819308, by rfl⟩ : syracuseStep 9092411 = 13638617) B13638617
theorem B32742787 : Blo 1794098 32742787 := bstep (se 1 (by rfl) ⟨24557090, by rfl⟩ : syracuseStep 32742787 = 49114181) B49114181
theorem B12279185 : Blo 1794098 12279185 := bstep (se 2 (by rfl) ⟨4604694, by rfl⟩ : syracuseStep 12279185 = 9209389) B9209389
theorem B5832089 : Blo 1794098 5832089 := bstep (se 2 (by rfl) ⟨2187033, by rfl⟩ : syracuseStep 5832089 = 4374067) B4374067
theorem B5111225 : Blo 1794098 5111225 := bstep (se 2 (by rfl) ⟨1916709, by rfl⟩ : syracuseStep 5111225 = 3833419) B3833419
theorem B3030473 : Blo 1794098 3030473 := bstep (se 2 (by rfl) ⟨1136427, by rfl⟩ : syracuseStep 3030473 = 2272855) B2272855
theorem B9092573 : Blo 1794098 9092573 := bstep (se 3 (by rfl) ⟨1704857, by rfl⟩ : syracuseStep 9092573 = 3409715) B3409715
theorem B6815299 : Blo 1794098 6815299 := bstep (se 1 (by rfl) ⟨5111474, by rfl⟩ : syracuseStep 6815299 = 10222949) B10222949
theorem B4038263 : Blo 1794098 4038263 := bstep (se 1 (by rfl) ⟨3028697, by rfl⟩ : syracuseStep 4038263 = 6057395) B6057395
theorem B6061769 : Blo 1794098 6061769 := bstep (se 2 (by rfl) ⟨2273163, by rfl⟩ : syracuseStep 6061769 = 4546327) B4546327
theorem B20446991 : Blo 1794098 20446991 := bstep (se 1 (by rfl) ⟨15335243, by rfl⟩ : syracuseStep 20446991 = 30670487) B30670487
theorem B4038443 : Blo 1794098 4038443 := bstep (se 1 (by rfl) ⟨3028832, by rfl⟩ : syracuseStep 4038443 = 6057665) B6057665
theorem B12934961 : Blo 1794098 12934961 := bstep (se 2 (by rfl) ⟨4850610, by rfl⟩ : syracuseStep 12934961 = 9701221) B9701221
theorem B1916731 : Blo 1794098 1916731 := bstep (se 1 (by rfl) ⟨1437548, by rfl⟩ : syracuseStep 1916731 = 2875097) B2875097
theorem B6815603 : Blo 1794098 6815603 := bstep (se 1 (by rfl) ⟨5111702, by rfl⟩ : syracuseStep 6815603 = 10223405) B10223405
theorem B12451843 : Blo 1794098 12451843 := bstep (se 1 (by rfl) ⟨9338882, by rfl⟩ : syracuseStep 12451843 = 18677765) B18677765
theorem B4038713 : Blo 1794098 4038713 := bstep (se 2 (by rfl) ⟨1514517, by rfl⟩ : syracuseStep 4038713 = 3029035) B3029035
theorem B6471737 : Blo 1794098 6471737 := bstep (se 2 (by rfl) ⟨2426901, by rfl⟩ : syracuseStep 6471737 = 4853803) B4853803
theorem B1794127 : Blo 1794098 1794127 := bstep (se 1 (by rfl) ⟨1345595, by rfl⟩ : syracuseStep 1794127 = 2691191) B2691191
theorem B1794143 : Blo 1794098 1794143 := bstep (se 1 (by rfl) ⟨1345607, by rfl⟩ : syracuseStep 1794143 = 2691215) B2691215
theorem B3407969 : Blo 1794098 3407969 := bstep (se 2 (by rfl) ⟨1277988, by rfl⟩ : syracuseStep 3407969 = 2555977) B2555977
theorem B1794171 : Blo 1794098 1794171 := bstep (se 1 (by rfl) ⟨1345628, by rfl⟩ : syracuseStep 1794171 = 2691257) B2691257
theorem B1794223 : Blo 1794098 1794223 := bstep (se 1 (by rfl) ⟨1345667, by rfl⟩ : syracuseStep 1794223 = 2691335) B2691335
theorem B1794247 : Blo 1794098 1794247 := bstep (se 1 (by rfl) ⟨1345685, by rfl⟩ : syracuseStep 1794247 = 2691371) B2691371
theorem B1794267 : Blo 1794098 1794267 := bstep (se 1 (by rfl) ⟨1345700, by rfl⟩ : syracuseStep 1794267 = 2691401) B2691401
theorem B1794343 : Blo 1794098 1794343 := bstep (se 1 (by rfl) ⟨1345757, by rfl⟩ : syracuseStep 1794343 = 2691515) B2691515
theorem B1794383 : Blo 1794098 1794383 := bstep (se 1 (by rfl) ⟨1345787, by rfl⟩ : syracuseStep 1794383 = 2691575) B2691575
theorem B1794399 : Blo 1794098 1794399 := bstep (se 1 (by rfl) ⟨1345799, by rfl⟩ : syracuseStep 1794399 = 2691599) B2691599
theorem B1794427 : Blo 1794098 1794427 := bstep (se 1 (by rfl) ⟨1345820, by rfl⟩ : syracuseStep 1794427 = 2691641) B2691641
theorem B5112193 : Blo 1794098 5112193 := bstep (se 2 (by rfl) ⟨1917072, by rfl⟩ : syracuseStep 5112193 = 3834145) B3834145
theorem B4039055 : Blo 1794098 4039055 := bstep (se 1 (by rfl) ⟨3029291, by rfl⟩ : syracuseStep 4039055 = 6058583) B6058583
theorem B1794479 : Blo 1794098 1794479 := bstep (se 1 (by rfl) ⟨1345859, by rfl⟩ : syracuseStep 1794479 = 2691719) B2691719
theorem B3408311 : Blo 1794098 3408311 := bstep (se 1 (by rfl) ⟨2556233, by rfl⟩ : syracuseStep 3408311 = 5112467) B5112467
theorem B1794503 : Blo 1794098 1794503 := bstep (se 1 (by rfl) ⟨1345877, by rfl⟩ : syracuseStep 1794503 = 2691755) B2691755
theorem B1794523 : Blo 1794098 1794523 := bstep (se 1 (by rfl) ⟨1345892, by rfl⟩ : syracuseStep 1794523 = 2691785) B2691785
theorem B3277351 : Blo 1794098 3277351 := bstep (se 1 (by rfl) ⟨2458013, by rfl⟩ : syracuseStep 3277351 = 4916027) B4916027
theorem B1794599 : Blo 1794098 1794599 := bstep (se 1 (by rfl) ⟨1345949, by rfl⟩ : syracuseStep 1794599 = 2691899) B2691899
theorem B1794639 : Blo 1794098 1794639 := bstep (se 1 (by rfl) ⟨1345979, by rfl⟩ : syracuseStep 1794639 = 2691959) B2691959
theorem B1794655 : Blo 1794098 1794655 := bstep (se 1 (by rfl) ⟨1345991, by rfl⟩ : syracuseStep 1794655 = 2691983) B2691983
theorem B1794683 : Blo 1794098 1794683 := bstep (se 1 (by rfl) ⟨1346012, by rfl⟩ : syracuseStep 1794683 = 2692025) B2692025
theorem B11502253 : Blo 1794098 11502253 := bstep (se 3 (by rfl) ⟨2156672, by rfl⟩ : syracuseStep 11502253 = 4313345) B4313345
theorem B1794735 : Blo 1794098 1794735 := bstep (se 1 (by rfl) ⟨1346051, by rfl⟩ : syracuseStep 1794735 = 2692103) B2692103
theorem B7987897 : Blo 1794098 7987897 := bstep (se 2 (by rfl) ⟨2995461, by rfl⟩ : syracuseStep 7987897 = 5990923) B5990923
theorem B1794759 : Blo 1794098 1794759 := bstep (se 1 (by rfl) ⟨1346069, by rfl⟩ : syracuseStep 1794759 = 2692139) B2692139
theorem B4039379 : Blo 1794098 4039379 := bstep (se 1 (by rfl) ⟨3029534, by rfl⟩ : syracuseStep 4039379 = 6059069) B6059069
theorem B1794779 : Blo 1794098 1794779 := bstep (se 1 (by rfl) ⟨1346084, by rfl⟩ : syracuseStep 1794779 = 2692169) B2692169
theorem B2876153 : Blo 1794098 2876153 := bstep (se 2 (by rfl) ⟨1078557, by rfl⟩ : syracuseStep 2876153 = 2157115) B2157115
theorem B1794855 : Blo 1794098 1794855 := bstep (se 1 (by rfl) ⟨1346141, by rfl⟩ : syracuseStep 1794855 = 2692283) B2692283
theorem B9085769 : Blo 1794098 9085769 := bstep (se 2 (by rfl) ⟨3407163, by rfl⟩ : syracuseStep 9085769 = 6814327) B6814327
theorem B3408713 : Blo 1794098 3408713 := bstep (se 2 (by rfl) ⟨1278267, by rfl⟩ : syracuseStep 3408713 = 2556535) B2556535
theorem B1794895 : Blo 1794098 1794895 := bstep (se 1 (by rfl) ⟨1346171, by rfl⟩ : syracuseStep 1794895 = 2692343) B2692343
theorem B1794911 : Blo 1794098 1794911 := bstep (se 1 (by rfl) ⟨1346183, by rfl⟩ : syracuseStep 1794911 = 2692367) B2692367
theorem B5112683 : Blo 1794098 5112683 := bstep (se 1 (by rfl) ⟨3834512, by rfl⟩ : syracuseStep 5112683 = 7669025) B7669025
theorem B1794939 : Blo 1794098 1794939 := bstep (se 1 (by rfl) ⟨1346204, by rfl⟩ : syracuseStep 1794939 = 2692409) B2692409
theorem B1794991 : Blo 1794098 1794991 := bstep (se 1 (by rfl) ⟨1346243, by rfl⟩ : syracuseStep 1794991 = 2692487) B2692487
theorem B43688879 : Blo 1794098 43688879 := bstep (se 1 (by rfl) ⟨32766659, by rfl⟩ : syracuseStep 43688879 = 65533319) B65533319
theorem B1795015 : Blo 1794098 1795015 := bstep (se 1 (by rfl) ⟨1346261, by rfl⟩ : syracuseStep 1795015 = 2692523) B2692523
theorem B1795035 : Blo 1794098 1795035 := bstep (se 1 (by rfl) ⟨1346276, by rfl⟩ : syracuseStep 1795035 = 2692553) B2692553
theorem B1795111 : Blo 1794098 1795111 := bstep (se 1 (by rfl) ⟨1346333, by rfl⟩ : syracuseStep 1795111 = 2692667) B2692667
theorem B1795151 : Blo 1794098 1795151 := bstep (se 1 (by rfl) ⟨1346363, by rfl⟩ : syracuseStep 1795151 = 2692727) B2692727
theorem B1795167 : Blo 1794098 1795167 := bstep (se 1 (by rfl) ⟨1346375, by rfl⟩ : syracuseStep 1795167 = 2692751) B2692751
theorem B1795195 : Blo 1794098 1795195 := bstep (se 1 (by rfl) ⟨1346396, by rfl⟩ : syracuseStep 1795195 = 2692793) B2692793
theorem B5252267 : Blo 1794098 5252267 := bstep (se 1 (by rfl) ⟨3939200, by rfl⟩ : syracuseStep 5252267 = 7878401) B7878401
theorem B1795247 : Blo 1794098 1795247 := bstep (se 1 (by rfl) ⟨1346435, by rfl⟩ : syracuseStep 1795247 = 2692871) B2692871
theorem B1795271 : Blo 1794098 1795271 := bstep (se 1 (by rfl) ⟨1346453, by rfl⟩ : syracuseStep 1795271 = 2692907) B2692907
theorem B2557127 : Blo 1794098 2557127 := bstep (se 1 (by rfl) ⟨1917845, by rfl⟩ : syracuseStep 2557127 = 3835691) B3835691
theorem B13624523 : Blo 1794098 13624523 := bstep (se 1 (by rfl) ⟨10218392, by rfl⟩ : syracuseStep 13624523 = 20436785) B20436785
theorem B1795291 : Blo 1794098 1795291 := bstep (se 1 (by rfl) ⟨1346468, by rfl⟩ : syracuseStep 1795291 = 2692937) B2692937
theorem B3835127 : Blo 1794098 3835127 := bstep (se 1 (by rfl) ⟨2876345, by rfl⟩ : syracuseStep 3835127 = 5752691) B5752691
theorem B1795367 : Blo 1794098 1795367 := bstep (se 1 (by rfl) ⟨1346525, by rfl⟩ : syracuseStep 1795367 = 2693051) B2693051
theorem B1795407 : Blo 1794098 1795407 := bstep (se 1 (by rfl) ⟨1346555, by rfl⟩ : syracuseStep 1795407 = 2693111) B2693111
theorem B1795423 : Blo 1794098 1795423 := bstep (se 1 (by rfl) ⟨1346567, by rfl⟩ : syracuseStep 1795423 = 2693135) B2693135
theorem B14558579 : Blo 1794098 14558579 := bstep (se 1 (by rfl) ⟨10918934, by rfl⟩ : syracuseStep 14558579 = 21837869) B21837869
theorem B1795451 : Blo 1794098 1795451 := bstep (se 1 (by rfl) ⟨1346588, by rfl⟩ : syracuseStep 1795451 = 2693177) B2693177
theorem B7882109 : Blo 1794098 7882109 := bstep (se 3 (by rfl) ⟨1477895, by rfl⟩ : syracuseStep 7882109 = 2955791) B2955791
theorem B1795503 : Blo 1794098 1795503 := bstep (se 1 (by rfl) ⟨1346627, by rfl⟩ : syracuseStep 1795503 = 2693255) B2693255
theorem B1795527 : Blo 1794098 1795527 := bstep (se 1 (by rfl) ⟨1346645, by rfl⟩ : syracuseStep 1795527 = 2693291) B2693291
theorem B2270683 : Blo 1794098 2270683 := bstep (se 1 (by rfl) ⟨1703012, by rfl⟩ : syracuseStep 2270683 = 3406025) B3406025
theorem B10225115 : Blo 1794098 10225115 := bstep (se 1 (by rfl) ⟨7668836, by rfl⟩ : syracuseStep 10225115 = 15337673) B15337673
theorem B6817243 : Blo 1794098 6817243 := bstep (se 1 (by rfl) ⟨5112932, by rfl⟩ : syracuseStep 6817243 = 10225865) B10225865
theorem B1795547 : Blo 1794098 1795547 := bstep (se 1 (by rfl) ⟨1346660, by rfl⟩ : syracuseStep 1795547 = 2693321) B2693321
theorem B3409427 : Blo 1794098 3409427 := bstep (se 1 (by rfl) ⟨2557070, by rfl⟩ : syracuseStep 3409427 = 5114141) B5114141
theorem B1795623 : Blo 1794098 1795623 := bstep (se 1 (by rfl) ⟨1346717, by rfl⟩ : syracuseStep 1795623 = 2693435) B2693435
theorem B3409465 : Blo 1794098 3409465 := bstep (se 2 (by rfl) ⟨1278549, by rfl⟩ : syracuseStep 3409465 = 2557099) B2557099
theorem B1795663 : Blo 1794098 1795663 := bstep (se 1 (by rfl) ⟨1346747, by rfl⟩ : syracuseStep 1795663 = 2693495) B2693495
theorem B1795679 : Blo 1794098 1795679 := bstep (se 1 (by rfl) ⟨1346759, by rfl⟩ : syracuseStep 1795679 = 2693519) B2693519
theorem B4040315 : Blo 1794098 4040315 := bstep (se 1 (by rfl) ⟨3030236, by rfl⟩ : syracuseStep 4040315 = 6060473) B6060473
theorem B1795707 : Blo 1794098 1795707 := bstep (se 1 (by rfl) ⟨1346780, by rfl⟩ : syracuseStep 1795707 = 2693561) B2693561
theorem B6055559 : Blo 1794098 6055559 := bstep (se 1 (by rfl) ⟨4541669, by rfl⟩ : syracuseStep 6055559 = 9083339) B9083339
theorem B1795759 : Blo 1794098 1795759 := bstep (se 1 (by rfl) ⟨1346819, by rfl⟩ : syracuseStep 1795759 = 2693639) B2693639
theorem B6907577 : Blo 1794098 6907577 := bstep (se 2 (by rfl) ⟨2590341, by rfl⟩ : syracuseStep 6907577 = 5180683) B5180683
theorem B6055613 : Blo 1794098 6055613 := bstep (se 3 (by rfl) ⟨1135427, by rfl⟩ : syracuseStep 6055613 = 2270855) B2270855
theorem B1795783 : Blo 1794098 1795783 := bstep (se 1 (by rfl) ⟨1346837, by rfl⟩ : syracuseStep 1795783 = 2693675) B2693675
theorem B1795803 : Blo 1794098 1795803 := bstep (se 1 (by rfl) ⟨1346852, by rfl⟩ : syracuseStep 1795803 = 2693705) B2693705
theorem B24905465 : Blo 1794098 24905465 := bstep (se 2 (by rfl) ⟨9339549, by rfl⟩ : syracuseStep 24905465 = 18679099) B18679099
theorem B4040441 : Blo 1794098 4040441 := bstep (se 2 (by rfl) ⟨1515165, by rfl⟩ : syracuseStep 4040441 = 3030331) B3030331
theorem B1795879 : Blo 1794098 1795879 := bstep (se 1 (by rfl) ⟨1346909, by rfl⟩ : syracuseStep 1795879 = 2693819) B2693819
theorem B1795919 : Blo 1794098 1795919 := bstep (se 1 (by rfl) ⟨1346939, by rfl⟩ : syracuseStep 1795919 = 2693879) B2693879
theorem B43657049 : Blo 1794098 43657049 := bstep (se 2 (by rfl) ⟨16371393, by rfl⟩ : syracuseStep 43657049 = 32742787) B32742787
theorem B6055775 : Blo 1794098 6055775 := bstep (se 1 (by rfl) ⟨4541831, by rfl⟩ : syracuseStep 6055775 = 9083663) B9083663
theorem B1795935 : Blo 1794098 1795935 := bstep (se 1 (by rfl) ⟨1346951, by rfl⟩ : syracuseStep 1795935 = 2693903) B2693903
theorem B3409769 : Blo 1794098 3409769 := bstep (se 2 (by rfl) ⟨1278663, by rfl⟩ : syracuseStep 3409769 = 2557327) B2557327
theorem B1795963 : Blo 1794098 1795963 := bstep (se 1 (by rfl) ⟨1346972, by rfl⟩ : syracuseStep 1795963 = 2693945) B2693945
theorem B1796015 : Blo 1794098 1796015 := bstep (se 1 (by rfl) ⟨1347011, by rfl⟩ : syracuseStep 1796015 = 2694023) B2694023
theorem B12937153 : Blo 1794098 12937153 := bstep (se 2 (by rfl) ⟨4851432, by rfl⟩ : syracuseStep 12937153 = 9702865) B9702865
theorem B1796039 : Blo 1794098 1796039 := bstep (se 1 (by rfl) ⟨1347029, by rfl⟩ : syracuseStep 1796039 = 2694059) B2694059
theorem B1796059 : Blo 1794098 1796059 := bstep (se 1 (by rfl) ⟨1347044, by rfl⟩ : syracuseStep 1796059 = 2694089) B2694089
theorem B6055937 : Blo 1794098 6055937 := bstep (se 2 (by rfl) ⟨2270976, by rfl⟩ : syracuseStep 6055937 = 4541953) B4541953
theorem B4040711 : Blo 1794098 4040711 := bstep (se 1 (by rfl) ⟨3030533, by rfl⟩ : syracuseStep 4040711 = 6061067) B6061067
theorem B4040783 : Blo 1794098 4040783 := bstep (se 1 (by rfl) ⟨3030587, by rfl⟩ : syracuseStep 4040783 = 6061175) B6061175
theorem B9087065 : Blo 1794098 9087065 := bstep (se 2 (by rfl) ⟨3407649, by rfl⟩ : syracuseStep 9087065 = 6815299) B6815299
theorem B3278971 : Blo 1794098 3278971 := bstep (se 1 (by rfl) ⟨2459228, by rfl⟩ : syracuseStep 3278971 = 4918457) B4918457
theorem B8186123 : Blo 1794098 8186123 := bstep (se 1 (by rfl) ⟨6139592, by rfl⟩ : syracuseStep 8186123 = 12279185) B12279185
theorem B25872689 : Blo 1794098 25872689 := bstep (se 2 (by rfl) ⟨9702258, by rfl⟩ : syracuseStep 25872689 = 19404517) B19404517
theorem B4041179 : Blo 1794098 4041179 := bstep (se 1 (by rfl) ⟨3030884, by rfl⟩ : syracuseStep 4041179 = 6061769) B6061769
theorem B4311577 : Blo 1794098 4311577 := bstep (se 2 (by rfl) ⟨1616841, by rfl⟩ : syracuseStep 4311577 = 3233683) B3233683
theorem B3639905 : Blo 1794098 3639905 := bstep (se 2 (by rfl) ⟨1364964, by rfl⟩ : syracuseStep 3639905 = 2729929) B2729929
theorem B6818489 : Blo 1794098 6818489 := bstep (se 2 (by rfl) ⟨2556933, by rfl⟩ : syracuseStep 6818489 = 5113867) B5113867
theorem B4311751 : Blo 1794098 4311751 := bstep (se 1 (by rfl) ⟨3233813, by rfl⟩ : syracuseStep 4311751 = 6467627) B6467627
theorem B6818519 : Blo 1794098 6818519 := bstep (se 1 (by rfl) ⟨5113889, by rfl⟩ : syracuseStep 6818519 = 10227779) B10227779
theorem B6056747 : Blo 1794098 6056747 := bstep (se 1 (by rfl) ⟨4542560, by rfl⟩ : syracuseStep 6056747 = 9085121) B9085121
theorem B4541447 : Blo 1794098 4541447 := bstep (se 1 (by rfl) ⟨3406085, by rfl⟩ : syracuseStep 4541447 = 6812171) B6812171
theorem B11496491 : Blo 1794098 11496491 := bstep (se 1 (by rfl) ⟨8622368, by rfl⟩ : syracuseStep 11496491 = 17244737) B17244737
theorem B6057017 : Blo 1794098 6057017 := bstep (se 2 (by rfl) ⟨2271381, by rfl⟩ : syracuseStep 6057017 = 4542763) B4542763
theorem B10218575 : Blo 1794098 10218575 := bstep (se 1 (by rfl) ⟨7663931, by rfl⟩ : syracuseStep 10218575 = 15327863) B15327863
theorem B6466675 : Blo 1794098 6466675 := bstep (se 1 (by rfl) ⟨4850006, by rfl⟩ : syracuseStep 6466675 = 9700013) B9700013
theorem B31100021 : Blo 1794098 31100021 := bstep (se 5 (by rfl) ⟨1457813, by rfl⟩ : syracuseStep 31100021 = 2915627) B2915627
theorem B6057341 : Blo 1794098 6057341 := bstep (se 3 (by rfl) ⟨1135751, by rfl⟩ : syracuseStep 6057341 = 2271503) B2271503
theorem B11496923 : Blo 1794098 11496923 := bstep (se 1 (by rfl) ⟨8622692, by rfl⟩ : syracuseStep 11496923 = 17245385) B17245385
theorem B10227323 : Blo 1794098 10227323 := bstep (se 1 (by rfl) ⟨7670492, by rfl⟩ : syracuseStep 10227323 = 15340985) B15340985
theorem B12938885 : Blo 1794098 12938885 := bstep (se 4 (by rfl) ⟨1213020, by rfl⟩ : syracuseStep 12938885 = 2426041) B2426041
theorem B6057611 : Blo 1794098 6057611 := bstep (se 1 (by rfl) ⟨4543208, by rfl⟩ : syracuseStep 6057611 = 9086417) B9086417
theorem B3280783 : Blo 1794098 3280783 := bstep (se 1 (by rfl) ⟨2460587, by rfl⟩ : syracuseStep 3280783 = 4921175) B4921175
theorem B34508915 : Blo 1794098 34508915 := bstep (se 1 (by rfl) ⟨25881686, by rfl⟩ : syracuseStep 34508915 = 51763373) B51763373
theorem B2019451 : Blo 1794098 2019451 := bstep (se 1 (by rfl) ⟨1514588, by rfl⟩ : syracuseStep 2019451 = 3029177) B3029177
theorem B18919601 : Blo 1794098 18919601 := bstep (se 2 (by rfl) ⟨7094850, by rfl⟩ : syracuseStep 18919601 = 14189701) B14189701
theorem B5828969 : Blo 1794098 5828969 := bstep (se 2 (by rfl) ⟨2185863, by rfl⟩ : syracuseStep 5828969 = 4371727) B4371727
theorem B11506049 : Blo 1794098 11506049 := bstep (se 2 (by rfl) ⟨4314768, by rfl⟩ : syracuseStep 11506049 = 8629537) B8629537
theorem B2691503 : Blo 1794098 2691503 := bstep (se 1 (by rfl) ⟨2018627, by rfl⟩ : syracuseStep 2691503 = 4037255) B4037255
theorem B2691593 : Blo 1794098 2691593 := bstep (se 2 (by rfl) ⟨1009347, by rfl⟩ : syracuseStep 2691593 = 2018695) B2018695
theorem B6058529 : Blo 1794098 6058529 := bstep (se 2 (by rfl) ⟨2271948, by rfl⟩ : syracuseStep 6058529 = 4543897) B4543897
theorem B2691623 : Blo 1794098 2691623 := bstep (se 1 (by rfl) ⟨2018717, by rfl⟩ : syracuseStep 2691623 = 4037435) B4037435
theorem B2019919 : Blo 1794098 2019919 := bstep (se 1 (by rfl) ⟨1514939, by rfl⟩ : syracuseStep 2019919 = 3029879) B3029879
theorem B2691707 : Blo 1794098 2691707 := bstep (se 1 (by rfl) ⟨2018780, by rfl⟩ : syracuseStep 2691707 = 4037561) B4037561
theorem B6812369 : Blo 1794098 6812369 := bstep (se 2 (by rfl) ⟨2554638, by rfl⟩ : syracuseStep 6812369 = 5109277) B5109277
theorem B2691833 : Blo 1794098 2691833 := bstep (se 2 (by rfl) ⟨1009437, by rfl⟩ : syracuseStep 2691833 = 2018875) B2018875
theorem B6058745 : Blo 1794098 6058745 := bstep (se 2 (by rfl) ⟨2272029, by rfl⟩ : syracuseStep 6058745 = 4544059) B4544059
theorem B2691935 : Blo 1794098 2691935 := bstep (se 1 (by rfl) ⟨2018951, by rfl⟩ : syracuseStep 2691935 = 4037903) B4037903
theorem B2691947 : Blo 1794098 2691947 := bstep (se 1 (by rfl) ⟨2018960, by rfl⟩ : syracuseStep 2691947 = 4037921) B4037921
theorem B3888059 : Blo 1794098 3888059 := bstep (se 1 (by rfl) ⟨2916044, by rfl⟩ : syracuseStep 3888059 = 5832089) B5832089
theorem B2020315 : Blo 1794098 2020315 := bstep (se 1 (by rfl) ⟨1515236, by rfl⟩ : syracuseStep 2020315 = 3030473) B3030473
theorem B6059015 : Blo 1794098 6059015 := bstep (se 1 (by rfl) ⟨4544261, by rfl⟩ : syracuseStep 6059015 = 9088523) B9088523
theorem B6812687 : Blo 1794098 6812687 := bstep (se 1 (by rfl) ⟨5109515, by rfl⟩ : syracuseStep 6812687 = 10219031) B10219031
theorem B6468623 : Blo 1794098 6468623 := bstep (se 1 (by rfl) ⟨4851467, by rfl⟩ : syracuseStep 6468623 = 9702935) B9702935
theorem B2692175 : Blo 1794098 2692175 := bstep (se 1 (by rfl) ⟨2019131, by rfl⟩ : syracuseStep 2692175 = 4038263) B4038263
theorem B6059123 : Blo 1794098 6059123 := bstep (se 1 (by rfl) ⟨4544342, by rfl⟩ : syracuseStep 6059123 = 9088685) B9088685
theorem B2692295 : Blo 1794098 2692295 := bstep (se 1 (by rfl) ⟨2019221, by rfl⟩ : syracuseStep 2692295 = 4038443) B4038443
theorem B8623307 : Blo 1794098 8623307 := bstep (se 1 (by rfl) ⟨6467480, by rfl⟩ : syracuseStep 8623307 = 12934961) B12934961
theorem B4543735 : Blo 1794098 4543735 := bstep (se 1 (by rfl) ⟨3407801, by rfl⟩ : syracuseStep 4543735 = 6815603) B6815603
theorem B2692457 : Blo 1794098 2692457 := bstep (se 2 (by rfl) ⟨1009671, by rfl⟩ : syracuseStep 2692457 = 2019343) B2019343
theorem B6059393 : Blo 1794098 6059393 := bstep (se 2 (by rfl) ⟨2272272, by rfl⟩ : syracuseStep 6059393 = 4544545) B4544545
theorem B3028367 : Blo 1794098 3028367 := bstep (se 1 (by rfl) ⟨2271275, by rfl⟩ : syracuseStep 3028367 = 4542551) B4542551
theorem B2692535 : Blo 1794098 2692535 := bstep (se 1 (by rfl) ⟨2019401, by rfl⟩ : syracuseStep 2692535 = 4038803) B4038803
theorem B2692571 : Blo 1794098 2692571 := bstep (se 1 (by rfl) ⟨2019428, by rfl⟩ : syracuseStep 2692571 = 4038857) B4038857
theorem B4544009 : Blo 1794098 4544009 := bstep (se 2 (by rfl) ⟨1704003, by rfl⟩ : syracuseStep 4544009 = 3408007) B3408007
theorem B4544039 : Blo 1794098 4544039 := bstep (se 1 (by rfl) ⟨3408029, by rfl⟩ : syracuseStep 4544039 = 6816059) B6816059
theorem B13637159 : Blo 1794098 13637159 := bstep (se 1 (by rfl) ⟨10227869, by rfl⟩ : syracuseStep 13637159 = 20455739) B20455739
theorem B5748347 : Blo 1794098 5748347 := bstep (se 1 (by rfl) ⟨4311260, by rfl⟩ : syracuseStep 5748347 = 8622521) B8622521
theorem B3028603 : Blo 1794098 3028603 := bstep (se 1 (by rfl) ⟨2271452, by rfl⟩ : syracuseStep 3028603 = 4542905) B4542905
theorem B6141575 : Blo 1794098 6141575 := bstep (se 1 (by rfl) ⟨4606181, by rfl⟩ : syracuseStep 6141575 = 9212363) B9212363
theorem B7665299 : Blo 1794098 7665299 := bstep (se 1 (by rfl) ⟨5748974, by rfl⟩ : syracuseStep 7665299 = 11497949) B11497949
theorem B11499155 : Blo 1794098 11499155 := bstep (se 1 (by rfl) ⟨8624366, by rfl⟩ : syracuseStep 11499155 = 17248733) B17248733
theorem B7280327 : Blo 1794098 7280327 := bstep (se 1 (by rfl) ⟨5460245, by rfl⟩ : syracuseStep 7280327 = 10920491) B10920491
theorem B7665367 : Blo 1794098 7665367 := bstep (se 1 (by rfl) ⟨5749025, by rfl⟩ : syracuseStep 7665367 = 11498051) B11498051
theorem B9082691 : Blo 1794098 9082691 := bstep (se 1 (by rfl) ⟨6812018, by rfl⟩ : syracuseStep 9082691 = 13624037) B13624037
theorem B23000921 : Blo 1794098 23000921 := bstep (se 2 (by rfl) ⟨8625345, by rfl⟩ : syracuseStep 23000921 = 17250691) B17250691
theorem B4544363 : Blo 1794098 4544363 := bstep (se 1 (by rfl) ⟨3408272, by rfl⟩ : syracuseStep 4544363 = 6816545) B6816545
theorem B11499383 : Blo 1794098 11499383 := bstep (se 1 (by rfl) ⟨8624537, by rfl⟩ : syracuseStep 11499383 = 17249075) B17249075
theorem B2693039 : Blo 1794098 2693039 := bstep (se 1 (by rfl) ⟨2019779, by rfl⟩ : syracuseStep 2693039 = 4039559) B4039559
theorem B5109767 : Blo 1794098 5109767 := bstep (se 1 (by rfl) ⟨3832325, by rfl⟩ : syracuseStep 5109767 = 7664651) B7664651
theorem B2693129 : Blo 1794098 2693129 := bstep (se 2 (by rfl) ⟨1009923, by rfl⟩ : syracuseStep 2693129 = 2019847) B2019847
theorem B2693159 : Blo 1794098 2693159 := bstep (se 1 (by rfl) ⟨2019869, by rfl⟩ : syracuseStep 2693159 = 4039739) B4039739
theorem B3070075 : Blo 1794098 3070075 := bstep (se 1 (by rfl) ⟨2302556, by rfl⟩ : syracuseStep 3070075 = 4605113) B4605113
theorem B2693243 : Blo 1794098 2693243 := bstep (se 1 (by rfl) ⟨2019932, by rfl⟩ : syracuseStep 2693243 = 4039865) B4039865
theorem B6060203 : Blo 1794098 6060203 := bstep (se 1 (by rfl) ⟨4545152, by rfl⟩ : syracuseStep 6060203 = 9090305) B9090305
theorem B59005169 : Blo 1794098 59005169 := bstep (se 2 (by rfl) ⟨22126938, by rfl⟩ : syracuseStep 59005169 = 44253877) B44253877
theorem B2693369 : Blo 1794098 2693369 := bstep (se 2 (by rfl) ⟨1010013, by rfl⟩ : syracuseStep 2693369 = 2020027) B2020027
theorem B2693471 : Blo 1794098 2693471 := bstep (se 1 (by rfl) ⟨2020103, by rfl⟩ : syracuseStep 2693471 = 4040207) B4040207
theorem B2693483 : Blo 1794098 2693483 := bstep (se 1 (by rfl) ⟨2020112, by rfl⟩ : syracuseStep 2693483 = 4040225) B4040225
theorem B3029467 : Blo 1794098 3029467 := bstep (se 1 (by rfl) ⟨2272100, by rfl⟩ : syracuseStep 3029467 = 4544201) B4544201
theorem B4545011 : Blo 1794098 4545011 := bstep (se 1 (by rfl) ⟨3408758, by rfl⟩ : syracuseStep 4545011 = 6817517) B6817517
theorem B4037129 : Blo 1794098 4037129 := bstep (se 2 (by rfl) ⟨1513923, by rfl⟩ : syracuseStep 4037129 = 3027847) B3027847
theorem B2693711 : Blo 1794098 2693711 := bstep (se 1 (by rfl) ⟨2020283, by rfl⟩ : syracuseStep 2693711 = 4040567) B4040567
theorem B87366275 : Blo 1794098 87366275 := bstep (se 1 (by rfl) ⟨65524706, by rfl⟩ : syracuseStep 87366275 = 131049413) B131049413
theorem B6060743 : Blo 1794098 6060743 := bstep (se 1 (by rfl) ⟨4545557, by rfl⟩ : syracuseStep 6060743 = 9091115) B9091115
theorem B2693831 : Blo 1794098 2693831 := bstep (se 1 (by rfl) ⟨2020373, by rfl⟩ : syracuseStep 2693831 = 4040747) B4040747
theorem B4037471 : Blo 1794098 4037471 := bstep (se 1 (by rfl) ⟨3028103, by rfl⟩ : syracuseStep 4037471 = 6056207) B6056207
theorem B2693993 : Blo 1794098 2693993 := bstep (se 2 (by rfl) ⟨1010247, by rfl⟩ : syracuseStep 2693993 = 2020495) B2020495
theorem B13630355 : Blo 1794098 13630355 := bstep (se 1 (by rfl) ⟨10222766, by rfl⟩ : syracuseStep 13630355 = 20445533) B20445533
theorem B2874295 : Blo 1794098 2874295 := bstep (se 1 (by rfl) ⟨2155721, by rfl⟩ : syracuseStep 2874295 = 4311443) B4311443
theorem B2694071 : Blo 1794098 2694071 := bstep (se 1 (by rfl) ⟨2020553, by rfl⟩ : syracuseStep 2694071 = 4041107) B4041107
theorem B4545467 : Blo 1794098 4545467 := bstep (se 1 (by rfl) ⟨3409100, by rfl⟩ : syracuseStep 4545467 = 6818201) B6818201
theorem B2694107 : Blo 1794098 2694107 := bstep (se 1 (by rfl) ⟨2020580, by rfl⟩ : syracuseStep 2694107 = 4041161) B4041161
theorem B4037651 : Blo 1794098 4037651 := bstep (se 1 (by rfl) ⟨3028238, by rfl⟩ : syracuseStep 4037651 = 6056477) B6056477
theorem B6814799 : Blo 1794098 6814799 := bstep (se 1 (by rfl) ⟨5111099, by rfl⟩ : syracuseStep 6814799 = 10222199) B10222199
theorem B3030095 : Blo 1794098 3030095 := bstep (se 1 (by rfl) ⟨2272571, by rfl⟩ : syracuseStep 3030095 = 4545143) B4545143
theorem B2555003 : Blo 1794098 2555003 := bstep (se 1 (by rfl) ⟨1916252, by rfl⟩ : syracuseStep 2555003 = 3832505) B3832505
theorem B9092249 : Blo 1794098 9092249 := bstep (se 2 (by rfl) ⟨3409593, by rfl⟩ : syracuseStep 9092249 = 6819187) B6819187
theorem B4037993 : Blo 1794098 4037993 := bstep (se 2 (by rfl) ⟨1514247, by rfl⟩ : syracuseStep 4037993 = 3028495) B3028495
theorem B6061607 : Blo 1794098 6061607 := bstep (se 1 (by rfl) ⟨4546205, by rfl⟩ : syracuseStep 6061607 = 9092411) B9092411
theorem B4546145 : Blo 1794098 4546145 := bstep (se 2 (by rfl) ⟨1704804, by rfl⟩ : syracuseStep 4546145 = 3409609) B3409609
theorem B3407483 : Blo 1794098 3407483 := bstep (se 1 (by rfl) ⟨2555612, by rfl⟩ : syracuseStep 3407483 = 5111225) B5111225
theorem B10919569 : Blo 1794098 10919569 := bstep (se 2 (by rfl) ⟨4094838, by rfl⟩ : syracuseStep 10919569 = 8189677) B8189677
theorem B6061715 : Blo 1794098 6061715 := bstep (se 1 (by rfl) ⟨4546286, by rfl⟩ : syracuseStep 6061715 = 9092573) B9092573
theorem B2875051 : Blo 1794098 2875051 := bstep (se 1 (by rfl) ⟨2156288, by rfl⟩ : syracuseStep 2875051 = 4312577) B4312577
theorem B2555641 : Blo 1794098 2555641 := bstep (se 2 (by rfl) ⟨958365, by rfl⟩ : syracuseStep 2555641 = 1916731) B1916731
theorem B13631327 : Blo 1794098 13631327 := bstep (se 1 (by rfl) ⟨10223495, by rfl⟩ : syracuseStep 13631327 = 20446991) B20446991
theorem B24551353 : Blo 1794098 24551353 := bstep (se 2 (by rfl) ⟨9206757, by rfl⟩ : syracuseStep 24551353 = 18413515) B18413515
theorem B4038587 : Blo 1794098 4038587 := bstep (se 1 (by rfl) ⟨3028940, by rfl⟩ : syracuseStep 4038587 = 6057881) B6057881
theorem B1794335 : Blo 1794098 1794335 := bstep (se 1 (by rfl) ⟨1345751, by rfl⟩ : syracuseStep 1794335 = 2691503) B2691503
theorem B1794395 : Blo 1794098 1794395 := bstep (se 1 (by rfl) ⟨1345796, by rfl⟩ : syracuseStep 1794395 = 2691593) B2691593
theorem B4039019 : Blo 1794098 4039019 := bstep (se 1 (by rfl) ⟨3029264, by rfl⟩ : syracuseStep 4039019 = 6058529) B6058529
theorem B1794415 : Blo 1794098 1794415 := bstep (se 1 (by rfl) ⟨1345811, by rfl⟩ : syracuseStep 1794415 = 2691623) B2691623
theorem B1794471 : Blo 1794098 1794471 := bstep (se 1 (by rfl) ⟨1345853, by rfl⟩ : syracuseStep 1794471 = 2691707) B2691707
theorem B1794555 : Blo 1794098 1794555 := bstep (se 1 (by rfl) ⟨1345916, by rfl⟩ : syracuseStep 1794555 = 2691833) B2691833
theorem B4039163 : Blo 1794098 4039163 := bstep (se 1 (by rfl) ⟨3029372, by rfl⟩ : syracuseStep 4039163 = 6058745) B6058745
theorem B6816257 : Blo 1794098 6816257 := bstep (se 2 (by rfl) ⟨2556096, by rfl⟩ : syracuseStep 6816257 = 5112193) B5112193
theorem B22995485 : Blo 1794098 22995485 := bstep (se 3 (by rfl) ⟨4311653, by rfl⟩ : syracuseStep 22995485 = 8623307) B8623307
theorem B1794623 : Blo 1794098 1794623 := bstep (se 1 (by rfl) ⟨1345967, by rfl⟩ : syracuseStep 1794623 = 2691935) B2691935
theorem B1794631 : Blo 1794098 1794631 := bstep (se 1 (by rfl) ⟨1345973, by rfl⟩ : syracuseStep 1794631 = 2691947) B2691947
theorem B3408455 : Blo 1794098 3408455 := bstep (se 1 (by rfl) ⟨2556341, by rfl⟩ : syracuseStep 3408455 = 5112683) B5112683
theorem B4039289 : Blo 1794098 4039289 := bstep (se 2 (by rfl) ⟨1514733, by rfl⟩ : syracuseStep 4039289 = 3029467) B3029467
theorem B4039343 : Blo 1794098 4039343 := bstep (se 1 (by rfl) ⟨3029507, by rfl⟩ : syracuseStep 4039343 = 6059015) B6059015
theorem B1794783 : Blo 1794098 1794783 := bstep (se 1 (by rfl) ⟨1346087, by rfl⟩ : syracuseStep 1794783 = 2692175) B2692175
theorem B4039415 : Blo 1794098 4039415 := bstep (se 1 (by rfl) ⟨3029561, by rfl⟩ : syracuseStep 4039415 = 6059123) B6059123
theorem B1794863 : Blo 1794098 1794863 := bstep (se 1 (by rfl) ⟨1346147, by rfl⟩ : syracuseStep 1794863 = 2692295) B2692295
theorem B15336337 : Blo 1794098 15336337 := bstep (se 2 (by rfl) ⟨5751126, by rfl⟩ : syracuseStep 15336337 = 11502253) B11502253
theorem B1794971 : Blo 1794098 1794971 := bstep (se 1 (by rfl) ⟨1346228, by rfl⟩ : syracuseStep 1794971 = 2692457) B2692457
theorem B10650529 : Blo 1794098 10650529 := bstep (se 2 (by rfl) ⟨3993948, by rfl⟩ : syracuseStep 10650529 = 7987897) B7987897
theorem B4039595 : Blo 1794098 4039595 := bstep (se 1 (by rfl) ⟨3029696, by rfl⟩ : syracuseStep 4039595 = 6059393) B6059393
theorem B1795023 : Blo 1794098 1795023 := bstep (se 1 (by rfl) ⟨1346267, by rfl⟩ : syracuseStep 1795023 = 2692535) B2692535
theorem B1795047 : Blo 1794098 1795047 := bstep (se 1 (by rfl) ⟨1346285, by rfl⟩ : syracuseStep 1795047 = 2692571) B2692571
theorem B6816743 : Blo 1794098 6816743 := bstep (se 1 (by rfl) ⟨5112557, by rfl⟩ : syracuseStep 6816743 = 10225115) B10225115
theorem B6055127 : Blo 1794098 6055127 := bstep (se 1 (by rfl) ⟨4541345, by rfl⟩ : syracuseStep 6055127 = 9082691) B9082691
theorem B1795359 : Blo 1794098 1795359 := bstep (se 1 (by rfl) ⟨1346519, by rfl⟩ : syracuseStep 1795359 = 2693039) B2693039
theorem B1795419 : Blo 1794098 1795419 := bstep (se 1 (by rfl) ⟨1346564, by rfl⟩ : syracuseStep 1795419 = 2693129) B2693129
theorem B1795439 : Blo 1794098 1795439 := bstep (se 1 (by rfl) ⟨1346579, by rfl⟩ : syracuseStep 1795439 = 2693159) B2693159
theorem B1795495 : Blo 1794098 1795495 := bstep (se 1 (by rfl) ⟨1346621, by rfl⟩ : syracuseStep 1795495 = 2693243) B2693243
theorem B4040135 : Blo 1794098 4040135 := bstep (se 1 (by rfl) ⟨3030101, by rfl⟩ : syracuseStep 4040135 = 6060203) B6060203
theorem B1795579 : Blo 1794098 1795579 := bstep (se 1 (by rfl) ⟨1346684, by rfl⟩ : syracuseStep 1795579 = 2693369) B2693369
theorem B5457415 : Blo 1794098 5457415 := bstep (se 1 (by rfl) ⟨4093061, by rfl⟩ : syracuseStep 5457415 = 8186123) B8186123
theorem B1795647 : Blo 1794098 1795647 := bstep (se 1 (by rfl) ⟨1346735, by rfl⟩ : syracuseStep 1795647 = 2693471) B2693471
theorem B1795655 : Blo 1794098 1795655 := bstep (se 1 (by rfl) ⟨1346741, by rfl⟩ : syracuseStep 1795655 = 2693483) B2693483
theorem B15328925 : Blo 1794098 15328925 := bstep (se 3 (by rfl) ⟨2874173, by rfl⟩ : syracuseStep 15328925 = 5748347) B5748347
theorem B1795807 : Blo 1794098 1795807 := bstep (se 1 (by rfl) ⟨1346855, by rfl⟩ : syracuseStep 1795807 = 2693711) B2693711
theorem B2426603 : Blo 1794098 2426603 := bstep (se 1 (by rfl) ⟨1819952, by rfl⟩ : syracuseStep 2426603 = 3639905) B3639905
theorem B4040495 : Blo 1794098 4040495 := bstep (se 1 (by rfl) ⟨3030371, by rfl⟩ : syracuseStep 4040495 = 6060743) B6060743
theorem B1795887 : Blo 1794098 1795887 := bstep (se 1 (by rfl) ⟨1346915, by rfl⟩ : syracuseStep 1795887 = 2693831) B2693831
theorem B1795995 : Blo 1794098 1795995 := bstep (se 1 (by rfl) ⟨1346996, by rfl⟩ : syracuseStep 1795995 = 2693993) B2693993
theorem B9086903 : Blo 1794098 9086903 := bstep (se 1 (by rfl) ⟨6815177, by rfl⟩ : syracuseStep 9086903 = 13630355) B13630355
theorem B1796047 : Blo 1794098 1796047 := bstep (se 1 (by rfl) ⟨1347035, by rfl⟩ : syracuseStep 1796047 = 2694071) B2694071
theorem B1796071 : Blo 1794098 1796071 := bstep (se 1 (by rfl) ⟨1347053, by rfl⟩ : syracuseStep 1796071 = 2694107) B2694107
theorem B7669741 : Blo 1794098 7669741 := bstep (se 3 (by rfl) ⟨1438076, by rfl⟩ : syracuseStep 7669741 = 2876153) B2876153
theorem B14559425 : Blo 1794098 14559425 := bstep (se 2 (by rfl) ⟨5459784, by rfl⟩ : syracuseStep 14559425 = 10919569) B10919569
theorem B15329573 : Blo 1794098 15329573 := bstep (se 4 (by rfl) ⟨1437147, by rfl⟩ : syracuseStep 15329573 = 2874295) B2874295
theorem B4041071 : Blo 1794098 4041071 := bstep (se 1 (by rfl) ⟨3030803, by rfl⟩ : syracuseStep 4041071 = 6061607) B6061607
theorem B2271655 : Blo 1794098 2271655 := bstep (se 1 (by rfl) ⟨1703741, by rfl⟩ : syracuseStep 2271655 = 3407483) B3407483
theorem B6818215 : Blo 1794098 6818215 := bstep (se 1 (by rfl) ⟨5113661, by rfl⟩ : syracuseStep 6818215 = 10227323) B10227323
theorem B4041143 : Blo 1794098 4041143 := bstep (se 1 (by rfl) ⟨3030857, by rfl⟩ : syracuseStep 4041143 = 6061715) B6061715
theorem B9087551 : Blo 1794098 9087551 := bstep (se 1 (by rfl) ⟨6815663, by rfl⟩ : syracuseStep 9087551 = 13631327) B13631327
theorem B2271979 : Blo 1794098 2271979 := bstep (se 1 (by rfl) ⟨1703984, by rfl⟩ : syracuseStep 2271979 = 3407969) B3407969
theorem B23005943 : Blo 1794098 23005943 := bstep (se 1 (by rfl) ⟨17254457, by rfl⟩ : syracuseStep 23005943 = 34508915) B34508915
theorem B3885979 : Blo 1794098 3885979 := bstep (se 1 (by rfl) ⟨2914484, by rfl⟩ : syracuseStep 3885979 = 5828969) B5828969
theorem B7670699 : Blo 1794098 7670699 := bstep (se 1 (by rfl) ⟨5753024, by rfl⟩ : syracuseStep 7670699 = 11506049) B11506049
theorem B2272207 : Blo 1794098 2272207 := bstep (se 1 (by rfl) ⟨1704155, by rfl⟩ : syracuseStep 2272207 = 3408311) B3408311
theorem B4541579 : Blo 1794098 4541579 := bstep (se 1 (by rfl) ⟨3406184, by rfl⟩ : syracuseStep 4541579 = 6812369) B6812369
theorem B6819005 : Blo 1794098 6819005 := bstep (se 3 (by rfl) ⟨1278563, by rfl⟩ : syracuseStep 6819005 = 2557127) B2557127
theorem B6057179 : Blo 1794098 6057179 := bstep (se 1 (by rfl) ⟨4542884, by rfl⟩ : syracuseStep 6057179 = 9085769) B9085769
theorem B2272475 : Blo 1794098 2272475 := bstep (se 1 (by rfl) ⟨1704356, by rfl⟩ : syracuseStep 2272475 = 3408713) B3408713
theorem B29125919 : Blo 1794098 29125919 := bstep (se 1 (by rfl) ⟨21844439, by rfl⟩ : syracuseStep 29125919 = 43688879) B43688879
theorem B10227005 : Blo 1794098 10227005 := bstep (se 3 (by rfl) ⟨1917563, by rfl⟩ : syracuseStep 10227005 = 3835127) B3835127
theorem B4541791 : Blo 1794098 4541791 := bstep (se 1 (by rfl) ⟨3406343, by rfl⟩ : syracuseStep 4541791 = 6812687) B6812687
theorem B4312415 : Blo 1794098 4312415 := bstep (se 1 (by rfl) ⟨3234311, by rfl⟩ : syracuseStep 4312415 = 6468623) B6468623
theorem B4369801 : Blo 1794098 4369801 := bstep (se 2 (by rfl) ⟨1638675, by rfl⟩ : syracuseStep 4369801 = 3277351) B3277351
theorem B3501511 : Blo 1794098 3501511 := bstep (se 1 (by rfl) ⟨2626133, by rfl⟩ : syracuseStep 3501511 = 5252267) B5252267
theorem B5254739 : Blo 1794098 5254739 := bstep (se 1 (by rfl) ⟨3941054, by rfl⟩ : syracuseStep 5254739 = 7882109) B7882109
theorem B2018911 : Blo 1794098 2018911 := bstep (se 1 (by rfl) ⟨1514183, by rfl⟩ : syracuseStep 2018911 = 3028367) B3028367
theorem B2272951 : Blo 1794098 2272951 := bstep (se 1 (by rfl) ⟨1704713, by rfl⟩ : syracuseStep 2272951 = 3409427) B3409427
theorem B2273179 : Blo 1794098 2273179 := bstep (se 1 (by rfl) ⟨1704884, by rfl⟩ : syracuseStep 2273179 = 3409769) B3409769
theorem B6058043 : Blo 1794098 6058043 := bstep (se 1 (by rfl) ⟨4543532, by rfl⟩ : syracuseStep 6058043 = 9087065) B9087065
theorem B8622233 : Blo 1794098 8622233 := bstep (se 2 (by rfl) ⟨3233337, by rfl⟩ : syracuseStep 8622233 = 6466675) B6466675
theorem B17248459 : Blo 1794098 17248459 := bstep (se 1 (by rfl) ⟨12936344, by rfl⟩ : syracuseStep 17248459 = 25872689) B25872689
theorem B6058313 : Blo 1794098 6058313 := bstep (se 2 (by rfl) ⟨2271867, by rfl⟩ : syracuseStep 6058313 = 4543735) B4543735
theorem B2691419 : Blo 1794098 2691419 := bstep (se 1 (by rfl) ⟨2018564, by rfl⟩ : syracuseStep 2691419 = 4037129) B4037129
theorem B18420205 : Blo 1794098 18420205 := bstep (se 3 (by rfl) ⟨3453788, by rfl⟩ : syracuseStep 18420205 = 6907577) B6907577
theorem B2691647 : Blo 1794098 2691647 := bstep (se 1 (by rfl) ⟨2018735, by rfl⟩ : syracuseStep 2691647 = 4037471) B4037471
theorem B3027577 : Blo 1794098 3027577 := bstep (se 2 (by rfl) ⟨1135341, by rfl⟩ : syracuseStep 3027577 = 2270683) B2270683
theorem B9089657 : Blo 1794098 9089657 := bstep (se 2 (by rfl) ⟨3408621, by rfl⟩ : syracuseStep 9089657 = 6817243) B6817243
theorem B3027631 : Blo 1794098 3027631 := bstep (se 1 (by rfl) ⟨2270723, by rfl⟩ : syracuseStep 3027631 = 4541447) B4541447
theorem B2691767 : Blo 1794098 2691767 := bstep (se 1 (by rfl) ⟨2018825, by rfl⟩ : syracuseStep 2691767 = 4037651) B4037651
theorem B7664327 : Blo 1794098 7664327 := bstep (se 1 (by rfl) ⟨5748245, by rfl⟩ : syracuseStep 7664327 = 11496491) B11496491
theorem B6812383 : Blo 1794098 6812383 := bstep (se 1 (by rfl) ⟨5109287, by rfl⟩ : syracuseStep 6812383 = 10218575) B10218575
theorem B4543199 : Blo 1794098 4543199 := bstep (se 1 (by rfl) ⟨3407399, by rfl⟩ : syracuseStep 4543199 = 6814799) B6814799
theorem B2020063 : Blo 1794098 2020063 := bstep (se 1 (by rfl) ⟨1515047, by rfl⟩ : syracuseStep 2020063 = 3030095) B3030095
theorem B2691995 : Blo 1794098 2691995 := bstep (se 1 (by rfl) ⟨2018996, by rfl⟩ : syracuseStep 2691995 = 4037993) B4037993
theorem B10220489 : Blo 1794098 10220489 := bstep (se 2 (by rfl) ⟨3832683, by rfl⟩ : syracuseStep 10220489 = 7665367) B7665367
theorem B7664615 : Blo 1794098 7664615 := bstep (se 1 (by rfl) ⟨5748461, by rfl⟩ : syracuseStep 7664615 = 11496923) B11496923
theorem B10368157 : Blo 1794098 10368157 := bstep (se 3 (by rfl) ⟨1944029, by rfl⟩ : syracuseStep 10368157 = 3888059) B3888059
theorem B17249537 : Blo 1794098 17249537 := bstep (se 2 (by rfl) ⟨6468576, by rfl⟩ : syracuseStep 17249537 = 12937153) B12937153
theorem B2692391 : Blo 1794098 2692391 := bstep (se 1 (by rfl) ⟨2019293, by rfl⟩ : syracuseStep 2692391 = 4038587) B4038587
theorem B16602457 : Blo 1794098 16602457 := bstep (se 2 (by rfl) ⟨6225921, by rfl⟩ : syracuseStep 16602457 = 12451843) B12451843
theorem B2692475 : Blo 1794098 2692475 := bstep (se 1 (by rfl) ⟨2019356, by rfl⟩ : syracuseStep 2692475 = 4038713) B4038713
theorem B4314491 : Blo 1794098 4314491 := bstep (se 1 (by rfl) ⟨3235868, by rfl⟩ : syracuseStep 4314491 = 6471737) B6471737
theorem B12613067 : Blo 1794098 12613067 := bstep (se 1 (by rfl) ⟨9459800, by rfl⟩ : syracuseStep 12613067 = 18919601) B18919601
theorem B4093433 : Blo 1794098 4093433 := bstep (se 2 (by rfl) ⟨1535037, by rfl⟩ : syracuseStep 4093433 = 3070075) B3070075
theorem B2692601 : Blo 1794098 2692601 := bstep (se 2 (by rfl) ⟨1009725, by rfl⟩ : syracuseStep 2692601 = 2019451) B2019451
theorem B4371961 : Blo 1794098 4371961 := bstep (se 2 (by rfl) ⟨1639485, by rfl⟩ : syracuseStep 4371961 = 3278971) B3278971
theorem B2692703 : Blo 1794098 2692703 := bstep (se 1 (by rfl) ⟨2019527, by rfl⟩ : syracuseStep 2692703 = 4039055) B4039055
theorem B6813341 : Blo 1794098 6813341 := bstep (se 3 (by rfl) ⟨1277501, by rfl⟩ : syracuseStep 6813341 = 2555003) B2555003
theorem B2692919 : Blo 1794098 2692919 := bstep (se 1 (by rfl) ⟨2019689, by rfl⟩ : syracuseStep 2692919 = 4039379) B4039379
theorem B5748769 : Blo 1794098 5748769 := bstep (se 2 (by rfl) ⟨2155788, by rfl⟩ : syracuseStep 5748769 = 4311577) B4311577
theorem B2693225 : Blo 1794098 2693225 := bstep (se 2 (by rfl) ⟨1009959, by rfl⟩ : syracuseStep 2693225 = 2019919) B2019919
theorem B9083015 : Blo 1794098 9083015 := bstep (se 1 (by rfl) ⟨6812261, by rfl⟩ : syracuseStep 9083015 = 13624523) B13624523
theorem B9705719 : Blo 1794098 9705719 := bstep (se 1 (by rfl) ⟨7279289, by rfl⟩ : syracuseStep 9705719 = 14558579) B14558579
theorem B5749001 : Blo 1794098 5749001 := bstep (se 2 (by rfl) ⟨2155875, by rfl⟩ : syracuseStep 5749001 = 4311751) B4311751
theorem B3029339 : Blo 1794098 3029339 := bstep (se 1 (by rfl) ⟨2272004, by rfl⟩ : syracuseStep 3029339 = 4544009) B4544009
theorem B3029359 : Blo 1794098 3029359 := bstep (se 1 (by rfl) ⟨2272019, by rfl⟩ : syracuseStep 3029359 = 4544039) B4544039
theorem B9091439 : Blo 1794098 9091439 := bstep (se 1 (by rfl) ⟨6818579, by rfl⟩ : syracuseStep 9091439 = 13637159) B13637159
theorem B2693543 : Blo 1794098 2693543 := bstep (se 1 (by rfl) ⟨2020157, by rfl⟩ : syracuseStep 2693543 = 4040315) B4040315
theorem B4037039 : Blo 1794098 4037039 := bstep (se 1 (by rfl) ⟨3027779, by rfl⟩ : syracuseStep 4037039 = 6055559) B6055559
theorem B4094383 : Blo 1794098 4094383 := bstep (se 1 (by rfl) ⟨3070787, by rfl⟩ : syracuseStep 4094383 = 6141575) B6141575
theorem B5110199 : Blo 1794098 5110199 := bstep (se 1 (by rfl) ⟨3832649, by rfl⟩ : syracuseStep 5110199 = 7665299) B7665299
theorem B7666103 : Blo 1794098 7666103 := bstep (se 1 (by rfl) ⟨5749577, by rfl⟩ : syracuseStep 7666103 = 11499155) B11499155
theorem B4037075 : Blo 1794098 4037075 := bstep (se 1 (by rfl) ⟨3027806, by rfl⟩ : syracuseStep 4037075 = 6055613) B6055613
theorem B16603643 : Blo 1794098 16603643 := bstep (se 1 (by rfl) ⟨12452732, by rfl⟩ : syracuseStep 16603643 = 24905465) B24905465
theorem B2693627 : Blo 1794098 2693627 := bstep (se 1 (by rfl) ⟨2020220, by rfl⟩ : syracuseStep 2693627 = 4040441) B4040441
theorem B29104699 : Blo 1794098 29104699 := bstep (se 1 (by rfl) ⟨21828524, by rfl⟩ : syracuseStep 29104699 = 43657049) B43657049
theorem B15333947 : Blo 1794098 15333947 := bstep (se 1 (by rfl) ⟨11500460, by rfl⟩ : syracuseStep 15333947 = 23000921) B23000921
theorem B4037183 : Blo 1794098 4037183 := bstep (se 1 (by rfl) ⟨3027887, by rfl⟩ : syracuseStep 4037183 = 6055775) B6055775
theorem B3029575 : Blo 1794098 3029575 := bstep (se 1 (by rfl) ⟨2272181, by rfl⟩ : syracuseStep 3029575 = 4544363) B4544363
theorem B7666255 : Blo 1794098 7666255 := bstep (se 1 (by rfl) ⟨5749691, by rfl⟩ : syracuseStep 7666255 = 11499383) B11499383
theorem B2693753 : Blo 1794098 2693753 := bstep (se 2 (by rfl) ⟨1010157, by rfl⟩ : syracuseStep 2693753 = 2020315) B2020315
theorem B4037291 : Blo 1794098 4037291 := bstep (se 1 (by rfl) ⟨3027968, by rfl⟩ : syracuseStep 4037291 = 6055937) B6055937
theorem B3406511 : Blo 1794098 3406511 := bstep (se 1 (by rfl) ⟨2554883, by rfl⟩ : syracuseStep 3406511 = 5109767) B5109767
theorem B2693807 : Blo 1794098 2693807 := bstep (se 1 (by rfl) ⟨2020355, by rfl⟩ : syracuseStep 2693807 = 4040711) B4040711
theorem B2693855 : Blo 1794098 2693855 := bstep (se 1 (by rfl) ⟨2020391, by rfl⟩ : syracuseStep 2693855 = 4040783) B4040783
theorem B39336779 : Blo 1794098 39336779 := bstep (se 1 (by rfl) ⟨29502584, by rfl⟩ : syracuseStep 39336779 = 59005169) B59005169
theorem B2694119 : Blo 1794098 2694119 := bstep (se 1 (by rfl) ⟨2020589, by rfl⟩ : syracuseStep 2694119 = 4041179) B4041179
theorem B3030007 : Blo 1794098 3030007 := bstep (se 1 (by rfl) ⟨2272505, by rfl⟩ : syracuseStep 3030007 = 4545011) B4545011
theorem B58244183 : Blo 1794098 58244183 := bstep (se 1 (by rfl) ⟨43683137, by rfl⟩ : syracuseStep 58244183 = 87366275) B87366275
theorem B4545659 : Blo 1794098 4545659 := bstep (se 1 (by rfl) ⟨3409244, by rfl⟩ : syracuseStep 4545659 = 6818489) B6818489
theorem B4545679 : Blo 1794098 4545679 := bstep (se 1 (by rfl) ⟨3409259, by rfl⟩ : syracuseStep 4545679 = 6818519) B6818519
theorem B19414205 : Blo 1794098 19414205 := bstep (se 3 (by rfl) ⟨3640163, by rfl⟩ : syracuseStep 19414205 = 7280327) B7280327
theorem B4037831 : Blo 1794098 4037831 := bstep (se 1 (by rfl) ⟨3028373, by rfl⟩ : syracuseStep 4037831 = 6056747) B6056747
theorem B3030311 : Blo 1794098 3030311 := bstep (se 1 (by rfl) ⟨2272733, by rfl⟩ : syracuseStep 3030311 = 4545467) B4545467
theorem B4038011 : Blo 1794098 4038011 := bstep (se 1 (by rfl) ⟨3028508, by rfl⟩ : syracuseStep 4038011 = 6057017) B6057017
theorem B20733347 : Blo 1794098 20733347 := bstep (se 1 (by rfl) ⟨15550010, by rfl⟩ : syracuseStep 20733347 = 31100021) B31100021
theorem B4545953 : Blo 1794098 4545953 := bstep (se 2 (by rfl) ⟨1704732, by rfl⟩ : syracuseStep 4545953 = 3409465) B3409465
theorem B6061499 : Blo 1794098 6061499 := bstep (se 1 (by rfl) ⟨4546124, by rfl⟩ : syracuseStep 6061499 = 9092249) B9092249
theorem B4038137 : Blo 1794098 4038137 := bstep (se 2 (by rfl) ⟨1514301, by rfl⟩ : syracuseStep 4038137 = 3028603) B3028603
theorem B3833401 : Blo 1794098 3833401 := bstep (se 2 (by rfl) ⟨1437525, by rfl⟩ : syracuseStep 3833401 = 2875051) B2875051
theorem B4038227 : Blo 1794098 4038227 := bstep (se 1 (by rfl) ⟨3028670, by rfl⟩ : syracuseStep 4038227 = 6057341) B6057341
theorem B3407521 : Blo 1794098 3407521 := bstep (se 2 (by rfl) ⟨1277820, by rfl⟩ : syracuseStep 3407521 = 2555641) B2555641
theorem B3030763 : Blo 1794098 3030763 := bstep (se 1 (by rfl) ⟨2273072, by rfl⟩ : syracuseStep 3030763 = 4546145) B4546145
theorem B8625923 : Blo 1794098 8625923 := bstep (se 1 (by rfl) ⟨6469442, by rfl⟩ : syracuseStep 8625923 = 12938885) B12938885
theorem B4038407 : Blo 1794098 4038407 := bstep (se 1 (by rfl) ⟨3028805, by rfl⟩ : syracuseStep 4038407 = 6057611) B6057611
theorem B4374377 : Blo 1794098 4374377 := bstep (se 2 (by rfl) ⟨1640391, by rfl⟩ : syracuseStep 4374377 = 3280783) B3280783
theorem B32735137 : Blo 1794098 32735137 := bstep (se 2 (by rfl) ⟨12275676, by rfl⟩ : syracuseStep 32735137 = 24551353) B24551353
theorem B4038695 : Blo 1794098 4038695 := bstep (se 1 (by rfl) ⟨3029021, by rfl⟩ : syracuseStep 4038695 = 6058043) B6058043
theorem B4038875 : Blo 1794098 4038875 := bstep (se 1 (by rfl) ⟨3029156, by rfl⟩ : syracuseStep 4038875 = 6058313) B6058313
theorem B1794279 : Blo 1794098 1794279 := bstep (se 1 (by rfl) ⟨1345709, by rfl⟩ : syracuseStep 1794279 = 2691419) B2691419
theorem B1794431 : Blo 1794098 1794431 := bstep (se 1 (by rfl) ⟨1345823, by rfl⟩ : syracuseStep 1794431 = 2691647) B2691647
theorem B1794511 : Blo 1794098 1794511 := bstep (se 1 (by rfl) ⟨1345883, by rfl⟩ : syracuseStep 1794511 = 2691767) B2691767
theorem B4039145 : Blo 1794098 4039145 := bstep (se 2 (by rfl) ⟨1514679, by rfl⟩ : syracuseStep 4039145 = 3029359) B3029359
theorem B1794663 : Blo 1794098 1794663 := bstep (se 1 (by rfl) ⟨1345997, by rfl⟩ : syracuseStep 1794663 = 2691995) B2691995
theorem B24560273 : Blo 1794098 24560273 := bstep (se 2 (by rfl) ⟨9210102, by rfl⟩ : syracuseStep 24560273 = 18420205) B18420205
theorem B38806265 : Blo 1794098 38806265 := bstep (se 2 (by rfl) ⟨14552349, by rfl⟩ : syracuseStep 38806265 = 29104699) B29104699
theorem B77669117 : Blo 1794098 77669117 := bstep (se 3 (by rfl) ⟨14562959, by rfl⟩ : syracuseStep 77669117 = 29125919) B29125919
theorem B4039433 : Blo 1794098 4039433 := bstep (se 2 (by rfl) ⟨1514787, by rfl⟩ : syracuseStep 4039433 = 3029575) B3029575
theorem B1794927 : Blo 1794098 1794927 := bstep (se 1 (by rfl) ⟨1346195, by rfl⟩ : syracuseStep 1794927 = 2692391) B2692391
theorem B1794983 : Blo 1794098 1794983 := bstep (se 1 (by rfl) ⟨1346237, by rfl⟩ : syracuseStep 1794983 = 2692475) B2692475
theorem B2876327 : Blo 1794098 2876327 := bstep (se 1 (by rfl) ⟨2157245, by rfl⟩ : syracuseStep 2876327 = 4314491) B4314491
theorem B2728955 : Blo 1794098 2728955 := bstep (se 1 (by rfl) ⟨2046716, by rfl⟩ : syracuseStep 2728955 = 4093433) B4093433
theorem B1795067 : Blo 1794098 1795067 := bstep (se 1 (by rfl) ⟨1346300, by rfl⟩ : syracuseStep 1795067 = 2692601) B2692601
theorem B1795135 : Blo 1794098 1795135 := bstep (se 1 (by rfl) ⟨1346351, by rfl⟩ : syracuseStep 1795135 = 2692703) B2692703
theorem B55288925 : Blo 1794098 55288925 := bstep (se 3 (by rfl) ⟨10366673, by rfl⟩ : syracuseStep 55288925 = 20733347) B20733347
theorem B20448449 : Blo 1794098 20448449 := bstep (se 2 (by rfl) ⟨7668168, by rfl⟩ : syracuseStep 20448449 = 15336337) B15336337
theorem B1795279 : Blo 1794098 1795279 := bstep (se 1 (by rfl) ⟨1346459, by rfl⟩ : syracuseStep 1795279 = 2692919) B2692919
theorem B4040009 : Blo 1794098 4040009 := bstep (se 2 (by rfl) ⟨1515003, by rfl⟩ : syracuseStep 4040009 = 3030007) B3030007
theorem B1795483 : Blo 1794098 1795483 := bstep (se 1 (by rfl) ⟨1346612, by rfl⟩ : syracuseStep 1795483 = 2693225) B2693225
theorem B6055343 : Blo 1794098 6055343 := bstep (se 1 (by rfl) ⟨4541507, by rfl⟩ : syracuseStep 6055343 = 9083015) B9083015
theorem B1795695 : Blo 1794098 1795695 := bstep (se 1 (by rfl) ⟨1346771, by rfl⟩ : syracuseStep 1795695 = 2693543) B2693543
theorem B11069095 : Blo 1794098 11069095 := bstep (se 1 (by rfl) ⟨8301821, by rfl⟩ : syracuseStep 11069095 = 16603643) B16603643
theorem B1795751 : Blo 1794098 1795751 := bstep (se 1 (by rfl) ⟨1346813, by rfl⟩ : syracuseStep 1795751 = 2693627) B2693627
theorem B1795835 : Blo 1794098 1795835 := bstep (se 1 (by rfl) ⟨1346876, by rfl⟩ : syracuseStep 1795835 = 2693753) B2693753
theorem B2271007 : Blo 1794098 2271007 := bstep (se 1 (by rfl) ⟨1703255, by rfl⟩ : syracuseStep 2271007 = 3406511) B3406511
theorem B1795871 : Blo 1794098 1795871 := bstep (se 1 (by rfl) ⟨1346903, by rfl⟩ : syracuseStep 1795871 = 2693807) B2693807
theorem B22136609 : Blo 1794098 22136609 := bstep (se 2 (by rfl) ⟨8301228, by rfl⟩ : syracuseStep 22136609 = 16602457) B16602457
theorem B6055721 : Blo 1794098 6055721 := bstep (se 2 (by rfl) ⟨2270895, by rfl⟩ : syracuseStep 6055721 = 4541791) B4541791
theorem B1795903 : Blo 1794098 1795903 := bstep (se 1 (by rfl) ⟨1346927, by rfl⟩ : syracuseStep 1795903 = 2693855) B2693855
theorem B15337295 : Blo 1794098 15337295 := bstep (se 1 (by rfl) ⟨11502971, by rfl⟩ : syracuseStep 15337295 = 23005943) B23005943
theorem B5826401 : Blo 1794098 5826401 := bstep (se 2 (by rfl) ⟨2184900, by rfl⟩ : syracuseStep 5826401 = 4369801) B4369801
theorem B26224519 : Blo 1794098 26224519 := bstep (se 1 (by rfl) ⟨19668389, by rfl⟩ : syracuseStep 26224519 = 39336779) B39336779
theorem B5113799 : Blo 1794098 5113799 := bstep (se 1 (by rfl) ⟨3835349, by rfl⟩ : syracuseStep 5113799 = 7670699) B7670699
theorem B1796079 : Blo 1794098 1796079 := bstep (se 1 (by rfl) ⟨1347059, by rfl⟩ : syracuseStep 1796079 = 2694119) B2694119
theorem B7276553 : Blo 1794098 7276553 := bstep (se 2 (by rfl) ⟨2728707, by rfl⟩ : syracuseStep 7276553 = 5457415) B5457415
theorem B6818003 : Blo 1794098 6818003 := bstep (se 1 (by rfl) ⟨5113502, by rfl⟩ : syracuseStep 6818003 = 10227005) B10227005
theorem B4040999 : Blo 1794098 4040999 := bstep (se 1 (by rfl) ⟨3030749, by rfl⟩ : syracuseStep 4040999 = 6061499) B6061499
theorem B4041017 : Blo 1794098 4041017 := bstep (se 2 (by rfl) ⟨1515381, by rfl⟩ : syracuseStep 4041017 = 3030763) B3030763
theorem B10226321 : Blo 1794098 10226321 := bstep (se 2 (by rfl) ⟨3834870, by rfl⟩ : syracuseStep 10226321 = 7669741) B7669741
theorem B22997945 : Blo 1794098 22997945 := bstep (se 2 (by rfl) ⟨8624229, by rfl⟩ : syracuseStep 22997945 = 17248459) B17248459
theorem B15330323 : Blo 1794098 15330323 := bstep (se 1 (by rfl) ⟨11497742, by rfl⟩ : syracuseStep 15330323 = 22995485) B22995485
theorem B2272303 : Blo 1794098 2272303 := bstep (se 1 (by rfl) ⟨1704227, by rfl⟩ : syracuseStep 2272303 = 3408455) B3408455
theorem B5459177 : Blo 1794098 5459177 := bstep (se 2 (by rfl) ⟨2047191, by rfl⟩ : syracuseStep 5459177 = 4094383) B4094383
theorem B8408711 : Blo 1794098 8408711 := bstep (se 1 (by rfl) ⟨6306533, by rfl⟩ : syracuseStep 8408711 = 12613067) B12613067
theorem B10219283 : Blo 1794098 10219283 := bstep (se 1 (by rfl) ⟨7664462, by rfl⟩ : syracuseStep 10219283 = 15328925) B15328925
theorem B4542227 : Blo 1794098 4542227 := bstep (se 1 (by rfl) ⟨3406670, by rfl⟩ : syracuseStep 4542227 = 6813341) B6813341
theorem B5181305 : Blo 1794098 5181305 := bstep (se 2 (by rfl) ⟨1942989, by rfl⟩ : syracuseStep 5181305 = 3885979) B3885979
theorem B14200705 : Blo 1794098 14200705 := bstep (se 2 (by rfl) ⟨5325264, by rfl⟩ : syracuseStep 14200705 = 10650529) B10650529
theorem B6057935 : Blo 1794098 6057935 := bstep (se 1 (by rfl) ⟨4543451, by rfl⟩ : syracuseStep 6057935 = 9086903) B9086903
theorem B10219715 : Blo 1794098 10219715 := bstep (se 1 (by rfl) ⟨7664786, by rfl⟩ : syracuseStep 10219715 = 15329573) B15329573
theorem B13824209 : Blo 1794098 13824209 := bstep (se 2 (by rfl) ⟨5184078, by rfl⟩ : syracuseStep 13824209 = 10368157) B10368157
theorem B2019559 : Blo 1794098 2019559 := bstep (se 1 (by rfl) ⟨1514669, by rfl⟩ : syracuseStep 2019559 = 3029339) B3029339
theorem B2691359 : Blo 1794098 2691359 := bstep (se 1 (by rfl) ⟨2018519, by rfl⟩ : syracuseStep 2691359 = 4037039) B4037039
theorem B2691383 : Blo 1794098 2691383 := bstep (se 1 (by rfl) ⟨2018537, by rfl⟩ : syracuseStep 2691383 = 4037075) B4037075
theorem B2691455 : Blo 1794098 2691455 := bstep (se 1 (by rfl) ⟨2018591, by rfl⟩ : syracuseStep 2691455 = 4037183) B4037183
theorem B6058367 : Blo 1794098 6058367 := bstep (se 1 (by rfl) ⟨4543775, by rfl⟩ : syracuseStep 6058367 = 9087551) B9087551
theorem B2691527 : Blo 1794098 2691527 := bstep (se 1 (by rfl) ⟨2018645, by rfl⟩ : syracuseStep 2691527 = 4037291) B4037291
theorem B5829281 : Blo 1794098 5829281 := bstep (se 2 (by rfl) ⟨2185980, by rfl⟩ : syracuseStep 5829281 = 4371961) B4371961
theorem B3027719 : Blo 1794098 3027719 := bstep (se 1 (by rfl) ⟨2270789, by rfl⟩ : syracuseStep 3027719 = 4541579) B4541579
theorem B2691881 : Blo 1794098 2691881 := bstep (se 2 (by rfl) ⟨1009455, by rfl⟩ : syracuseStep 2691881 = 2018911) B2018911
theorem B2691887 : Blo 1794098 2691887 := bstep (se 1 (by rfl) ⟨2018915, by rfl⟩ : syracuseStep 2691887 = 4037831) B4037831
theorem B2020207 : Blo 1794098 2020207 := bstep (se 1 (by rfl) ⟨1515155, by rfl⟩ : syracuseStep 2020207 = 3030311) B3030311
theorem B4543361 : Blo 1794098 4543361 := bstep (se 2 (by rfl) ⟨1703760, by rfl⟩ : syracuseStep 4543361 = 3407521) B3407521
theorem B2692007 : Blo 1794098 2692007 := bstep (se 1 (by rfl) ⟨2019005, by rfl⟩ : syracuseStep 2692007 = 4038011) B4038011
theorem B2692091 : Blo 1794098 2692091 := bstep (se 1 (by rfl) ⟨2019068, by rfl⟩ : syracuseStep 2692091 = 4038137) B4038137
theorem B18674725 : Blo 1794098 18674725 := bstep (se 4 (by rfl) ⟨1750755, by rfl⟩ : syracuseStep 18674725 = 3501511) B3501511
theorem B2692151 : Blo 1794098 2692151 := bstep (se 1 (by rfl) ⟨2019113, by rfl⟩ : syracuseStep 2692151 = 4038227) B4038227
theorem B3503159 : Blo 1794098 3503159 := bstep (se 1 (by rfl) ⟨2627369, by rfl⟩ : syracuseStep 3503159 = 5254739) B5254739
theorem B2692271 : Blo 1794098 2692271 := bstep (se 1 (by rfl) ⟨2019203, by rfl⟩ : syracuseStep 2692271 = 4038407) B4038407
theorem B7665025 : Blo 1794098 7665025 := bstep (se 2 (by rfl) ⟨2874384, by rfl⟩ : syracuseStep 7665025 = 5748769) B5748769
theorem B5748155 : Blo 1794098 5748155 := bstep (se 1 (by rfl) ⟨4311116, by rfl⟩ : syracuseStep 5748155 = 8622233) B8622233
theorem B2692679 : Blo 1794098 2692679 := bstep (se 1 (by rfl) ⟨2019509, by rfl⟩ : syracuseStep 2692679 = 4039019) B4039019
theorem B2692775 : Blo 1794098 2692775 := bstep (se 1 (by rfl) ⟨2019581, by rfl⟩ : syracuseStep 2692775 = 4039163) B4039163
theorem B4544171 : Blo 1794098 4544171 := bstep (se 1 (by rfl) ⟨3408128, by rfl⟩ : syracuseStep 4544171 = 6816257) B6816257
theorem B2692859 : Blo 1794098 2692859 := bstep (se 1 (by rfl) ⟨2019644, by rfl⟩ : syracuseStep 2692859 = 4039289) B4039289
theorem B6059771 : Blo 1794098 6059771 := bstep (se 1 (by rfl) ⟨4544828, by rfl⟩ : syracuseStep 6059771 = 9089657) B9089657
theorem B2692895 : Blo 1794098 2692895 := bstep (se 1 (by rfl) ⟨2019671, by rfl⟩ : syracuseStep 2692895 = 4039343) B4039343
theorem B5109551 : Blo 1794098 5109551 := bstep (se 1 (by rfl) ⟨3832163, by rfl⟩ : syracuseStep 5109551 = 7664327) B7664327
theorem B3028799 : Blo 1794098 3028799 := bstep (se 1 (by rfl) ⟨2271599, by rfl⟩ : syracuseStep 3028799 = 4543199) B4543199
theorem B2692943 : Blo 1794098 2692943 := bstep (se 1 (by rfl) ⟨2019707, by rfl⟩ : syracuseStep 2692943 = 4039415) B4039415
theorem B3028873 : Blo 1794098 3028873 := bstep (se 2 (by rfl) ⟨1135827, by rfl⟩ : syracuseStep 3028873 = 2271655) B2271655
theorem B9090953 : Blo 1794098 9090953 := bstep (se 2 (by rfl) ⟨3409107, by rfl⟩ : syracuseStep 9090953 = 6818215) B6818215
theorem B6059933 : Blo 1794098 6059933 := bstep (se 3 (by rfl) ⟨1136237, by rfl⟩ : syracuseStep 6059933 = 2272475) B2272475
theorem B2693063 : Blo 1794098 2693063 := bstep (se 1 (by rfl) ⟨2019797, by rfl⟩ : syracuseStep 2693063 = 4039595) B4039595
theorem B6813659 : Blo 1794098 6813659 := bstep (se 1 (by rfl) ⟨5110244, by rfl⟩ : syracuseStep 6813659 = 10220489) B10220489
theorem B5109743 : Blo 1794098 5109743 := bstep (se 1 (by rfl) ⟨3832307, by rfl⟩ : syracuseStep 5109743 = 7664615) B7664615
theorem B4544495 : Blo 1794098 4544495 := bstep (se 1 (by rfl) ⟨3408371, by rfl⟩ : syracuseStep 4544495 = 6816743) B6816743
theorem B10221673 : Blo 1794098 10221673 := bstep (se 2 (by rfl) ⟨3833127, by rfl⟩ : syracuseStep 10221673 = 7666255) B7666255
theorem B4036751 : Blo 1794098 4036751 := bstep (se 1 (by rfl) ⟨3027563, by rfl⟩ : syracuseStep 4036751 = 6055127) B6055127
theorem B4036769 : Blo 1794098 4036769 := bstep (se 2 (by rfl) ⟨1513788, by rfl⟩ : syracuseStep 4036769 = 3027577) B3027577
theorem B11499691 : Blo 1794098 11499691 := bstep (se 1 (by rfl) ⟨8624768, by rfl⟩ : syracuseStep 11499691 = 17249537) B17249537
theorem B4036841 : Blo 1794098 4036841 := bstep (se 2 (by rfl) ⟨1513815, by rfl⟩ : syracuseStep 4036841 = 3027631) B3027631
theorem B9083177 : Blo 1794098 9083177 := bstep (se 2 (by rfl) ⟨3406191, by rfl⟩ : syracuseStep 9083177 = 6812383) B6812383
theorem B2693417 : Blo 1794098 2693417 := bstep (se 2 (by rfl) ⟨1010031, by rfl⟩ : syracuseStep 2693417 = 2020063) B2020063
theorem B2693423 : Blo 1794098 2693423 := bstep (se 1 (by rfl) ⟨2020067, by rfl⟩ : syracuseStep 2693423 = 4040135) B4040135
theorem B3029305 : Blo 1794098 3029305 := bstep (se 2 (by rfl) ⟨1135989, by rfl⟩ : syracuseStep 3029305 = 2271979) B2271979
theorem B2693663 : Blo 1794098 2693663 := bstep (se 1 (by rfl) ⟨2020247, by rfl⟩ : syracuseStep 2693663 = 4040495) B4040495
theorem B3029609 : Blo 1794098 3029609 := bstep (se 2 (by rfl) ⟨1136103, by rfl⟩ : syracuseStep 3029609 = 2272207) B2272207
theorem B9706283 : Blo 1794098 9706283 := bstep (se 1 (by rfl) ⟨7279712, by rfl⟩ : syracuseStep 9706283 = 14559425) B14559425
theorem B6470479 : Blo 1794098 6470479 := bstep (se 1 (by rfl) ⟨4852859, by rfl⟩ : syracuseStep 6470479 = 9705719) B9705719
theorem B3832667 : Blo 1794098 3832667 := bstep (se 1 (by rfl) ⟨2874500, by rfl⟩ : syracuseStep 3832667 = 5749001) B5749001
theorem B6060905 : Blo 1794098 6060905 := bstep (se 2 (by rfl) ⟨2272839, by rfl⟩ : syracuseStep 6060905 = 4545679) B4545679
theorem B6060959 : Blo 1794098 6060959 := bstep (se 1 (by rfl) ⟨4545719, by rfl⟩ : syracuseStep 6060959 = 9091439) B9091439
theorem B2694047 : Blo 1794098 2694047 := bstep (se 1 (by rfl) ⟨2020535, by rfl⟩ : syracuseStep 2694047 = 4041071) B4041071
theorem B3406799 : Blo 1794098 3406799 := bstep (se 1 (by rfl) ⟨2555099, by rfl⟩ : syracuseStep 3406799 = 5110199) B5110199
theorem B5110735 : Blo 1794098 5110735 := bstep (se 1 (by rfl) ⟨3833051, by rfl⟩ : syracuseStep 5110735 = 7666103) B7666103
theorem B2694095 : Blo 1794098 2694095 := bstep (se 1 (by rfl) ⟨2020571, by rfl⟩ : syracuseStep 2694095 = 4041143) B4041143
theorem B10222631 : Blo 1794098 10222631 := bstep (se 1 (by rfl) ⟨7666973, by rfl⟩ : syracuseStep 10222631 = 15333947) B15333947
theorem B6470941 : Blo 1794098 6470941 := bstep (se 3 (by rfl) ⟨1213301, by rfl⟩ : syracuseStep 6470941 = 2426603) B2426603
theorem B38829455 : Blo 1794098 38829455 := bstep (se 1 (by rfl) ⟨29122091, by rfl⟩ : syracuseStep 38829455 = 58244183) B58244183
theorem B5111201 : Blo 1794098 5111201 := bstep (se 2 (by rfl) ⟨1916700, by rfl⟩ : syracuseStep 5111201 = 3833401) B3833401
theorem B3030439 : Blo 1794098 3030439 := bstep (se 1 (by rfl) ⟨2272829, by rfl⟩ : syracuseStep 3030439 = 4545659) B4545659
theorem B12942803 : Blo 1794098 12942803 := bstep (se 1 (by rfl) ⟨9707102, by rfl⟩ : syracuseStep 12942803 = 19414205) B19414205
theorem B4546003 : Blo 1794098 4546003 := bstep (se 1 (by rfl) ⟨3409502, by rfl⟩ : syracuseStep 4546003 = 6819005) B6819005
theorem B4038119 : Blo 1794098 4038119 := bstep (se 1 (by rfl) ⟨3028589, by rfl⟩ : syracuseStep 4038119 = 6057179) B6057179
theorem B2874943 : Blo 1794098 2874943 := bstep (se 1 (by rfl) ⟨2156207, by rfl⟩ : syracuseStep 2874943 = 4312415) B4312415
theorem B3030601 : Blo 1794098 3030601 := bstep (se 2 (by rfl) ⟨1136475, by rfl⟩ : syracuseStep 3030601 = 2272951) B2272951
theorem B3030635 : Blo 1794098 3030635 := bstep (se 1 (by rfl) ⟨2272976, by rfl⟩ : syracuseStep 3030635 = 4545953) B4545953
theorem B5750615 : Blo 1794098 5750615 := bstep (se 1 (by rfl) ⟨4312961, by rfl⟩ : syracuseStep 5750615 = 8625923) B8625923
theorem B3030905 : Blo 1794098 3030905 := bstep (se 2 (by rfl) ⟨1136589, by rfl⟩ : syracuseStep 3030905 = 2273179) B2273179
theorem B43646849 : Blo 1794098 43646849 := bstep (se 2 (by rfl) ⟨16367568, by rfl⟩ : syracuseStep 43646849 = 32735137) B32735137
theorem B2916251 : Blo 1794098 2916251 := bstep (se 1 (by rfl) ⟨2187188, by rfl⟩ : syracuseStep 2916251 = 4374377) B4374377
theorem B9216139 : Blo 1794098 9216139 := bstep (se 1 (by rfl) ⟨6912104, by rfl⟩ : syracuseStep 9216139 = 13824209) B13824209
theorem B1794239 : Blo 1794098 1794239 := bstep (se 1 (by rfl) ⟨1345679, by rfl⟩ : syracuseStep 1794239 = 2691359) B2691359
theorem B1794255 : Blo 1794098 1794255 := bstep (se 1 (by rfl) ⟨1345691, by rfl⟩ : syracuseStep 1794255 = 2691383) B2691383
theorem B1794303 : Blo 1794098 1794303 := bstep (se 1 (by rfl) ⟨1345727, by rfl⟩ : syracuseStep 1794303 = 2691455) B2691455
theorem B4038911 : Blo 1794098 4038911 := bstep (se 1 (by rfl) ⟨3029183, by rfl⟩ : syracuseStep 4038911 = 6058367) B6058367
theorem B1794351 : Blo 1794098 1794351 := bstep (se 1 (by rfl) ⟨1345763, by rfl⟩ : syracuseStep 1794351 = 2691527) B2691527
theorem B4039073 : Blo 1794098 4039073 := bstep (se 2 (by rfl) ⟨1514652, by rfl⟩ : syracuseStep 4039073 = 3029305) B3029305
theorem B25870843 : Blo 1794098 25870843 := bstep (se 1 (by rfl) ⟨19403132, by rfl⟩ : syracuseStep 25870843 = 38806265) B38806265
theorem B1794587 : Blo 1794098 1794587 := bstep (se 1 (by rfl) ⟨1345940, by rfl⟩ : syracuseStep 1794587 = 2691881) B2691881
theorem B1794591 : Blo 1794098 1794591 := bstep (se 1 (by rfl) ⟨1345943, by rfl⟩ : syracuseStep 1794591 = 2691887) B2691887
theorem B1794671 : Blo 1794098 1794671 := bstep (se 1 (by rfl) ⟨1346003, by rfl⟩ : syracuseStep 1794671 = 2692007) B2692007
theorem B1917551 : Blo 1794098 1917551 := bstep (se 1 (by rfl) ⟨1438163, by rfl⟩ : syracuseStep 1917551 = 2876327) B2876327
theorem B1794727 : Blo 1794098 1794727 := bstep (se 1 (by rfl) ⟨1346045, by rfl⟩ : syracuseStep 1794727 = 2692091) B2692091
theorem B1794767 : Blo 1794098 1794767 := bstep (se 1 (by rfl) ⟨1346075, by rfl⟩ : syracuseStep 1794767 = 2692151) B2692151
theorem B2335439 : Blo 1794098 2335439 := bstep (se 1 (by rfl) ⟨1751579, by rfl⟩ : syracuseStep 2335439 = 3503159) B3503159
theorem B1794847 : Blo 1794098 1794847 := bstep (se 1 (by rfl) ⟨1346135, by rfl⟩ : syracuseStep 1794847 = 2692271) B2692271
theorem B13632299 : Blo 1794098 13632299 := bstep (se 1 (by rfl) ⟨10224224, by rfl⟩ : syracuseStep 13632299 = 20448449) B20448449
theorem B1795119 : Blo 1794098 1795119 := bstep (se 1 (by rfl) ⟨1346339, by rfl⟩ : syracuseStep 1795119 = 2692679) B2692679
theorem B8627305 : Blo 1794098 8627305 := bstep (se 2 (by rfl) ⟨3235239, by rfl⟩ : syracuseStep 8627305 = 6470479) B6470479
theorem B1795183 : Blo 1794098 1795183 := bstep (se 1 (by rfl) ⟨1346387, by rfl⟩ : syracuseStep 1795183 = 2692775) B2692775
theorem B1795239 : Blo 1794098 1795239 := bstep (se 1 (by rfl) ⟨1346429, by rfl⟩ : syracuseStep 1795239 = 2692859) B2692859
theorem B4039847 : Blo 1794098 4039847 := bstep (se 1 (by rfl) ⟨3029885, by rfl⟩ : syracuseStep 4039847 = 6059771) B6059771
theorem B1795263 : Blo 1794098 1795263 := bstep (se 1 (by rfl) ⟨1346447, by rfl⟩ : syracuseStep 1795263 = 2692895) B2692895
theorem B1795295 : Blo 1794098 1795295 := bstep (se 1 (by rfl) ⟨1346471, by rfl⟩ : syracuseStep 1795295 = 2692943) B2692943
theorem B10224863 : Blo 1794098 10224863 := bstep (se 1 (by rfl) ⟨7668647, by rfl⟩ : syracuseStep 10224863 = 15337295) B15337295
theorem B3884267 : Blo 1794098 3884267 := bstep (se 1 (by rfl) ⟨2913200, by rfl⟩ : syracuseStep 3884267 = 5826401) B5826401
theorem B4039955 : Blo 1794098 4039955 := bstep (se 1 (by rfl) ⟨3029966, by rfl⟩ : syracuseStep 4039955 = 6059933) B6059933
theorem B1795375 : Blo 1794098 1795375 := bstep (se 1 (by rfl) ⟨1346531, by rfl⟩ : syracuseStep 1795375 = 2693063) B2693063
theorem B3409199 : Blo 1794098 3409199 := bstep (se 1 (by rfl) ⟨2556899, by rfl⟩ : syracuseStep 3409199 = 5113799) B5113799
theorem B4851035 : Blo 1794098 4851035 := bstep (se 1 (by rfl) ⟨3638276, by rfl⟩ : syracuseStep 4851035 = 7276553) B7276553
theorem B6055451 : Blo 1794098 6055451 := bstep (se 1 (by rfl) ⟨4541588, by rfl⟩ : syracuseStep 6055451 = 9083177) B9083177
theorem B1795611 : Blo 1794098 1795611 := bstep (se 1 (by rfl) ⟨1346708, by rfl⟩ : syracuseStep 1795611 = 2693417) B2693417
theorem B1795615 : Blo 1794098 1795615 := bstep (se 1 (by rfl) ⟨1346711, by rfl⟩ : syracuseStep 1795615 = 2693423) B2693423
theorem B22423229 : Blo 1794098 22423229 := bstep (se 3 (by rfl) ⟨4204355, by rfl⟩ : syracuseStep 22423229 = 8408711) B8408711
theorem B1795775 : Blo 1794098 1795775 := bstep (se 1 (by rfl) ⟨1346831, by rfl⟩ : syracuseStep 1795775 = 2693663) B2693663
theorem B8627921 : Blo 1794098 8627921 := bstep (se 2 (by rfl) ⟨3235470, by rfl⟩ : syracuseStep 8627921 = 6470941) B6470941
theorem B6817547 : Blo 1794098 6817547 := bstep (se 1 (by rfl) ⟨5113160, by rfl⟩ : syracuseStep 6817547 = 10226321) B10226321
theorem B4040585 : Blo 1794098 4040585 := bstep (se 2 (by rfl) ⟨1515219, by rfl⟩ : syracuseStep 4040585 = 3030439) B3030439
theorem B4040603 : Blo 1794098 4040603 := bstep (se 1 (by rfl) ⟨3030452, by rfl⟩ : syracuseStep 4040603 = 6060905) B6060905
theorem B4040639 : Blo 1794098 4040639 := bstep (se 1 (by rfl) ⟨3030479, by rfl⟩ : syracuseStep 4040639 = 6060959) B6060959
theorem B1796031 : Blo 1794098 1796031 := bstep (se 1 (by rfl) ⟨1347023, by rfl⟩ : syracuseStep 1796031 = 2694047) B2694047
theorem B1796063 : Blo 1794098 1796063 := bstep (se 1 (by rfl) ⟨1347047, by rfl⟩ : syracuseStep 1796063 = 2694095) B2694095
theorem B4040801 : Blo 1794098 4040801 := bstep (se 2 (by rfl) ⟨1515300, by rfl⟩ : syracuseStep 4040801 = 3030601) B3030601
theorem B3639451 : Blo 1794098 3639451 := bstep (se 1 (by rfl) ⟨2729588, by rfl⟩ : syracuseStep 3639451 = 5459177) B5459177
theorem B8628535 : Blo 1794098 8628535 := bstep (se 1 (by rfl) ⟨6471401, by rfl⟩ : syracuseStep 8628535 = 12942803) B12942803
theorem B18934273 : Blo 1794098 18934273 := bstep (se 2 (by rfl) ⟨7100352, by rfl⟩ : syracuseStep 18934273 = 14200705) B14200705
theorem B34966025 : Blo 1794098 34966025 := bstep (se 2 (by rfl) ⟨13112259, by rfl⟩ : syracuseStep 34966025 = 26224519) B26224519
theorem B1944167 : Blo 1794098 1944167 := bstep (se 1 (by rfl) ⟨1458125, by rfl⟩ : syracuseStep 1944167 = 2916251) B2916251
theorem B13625981 : Blo 1794098 13625981 := bstep (se 3 (by rfl) ⟨2554871, by rfl⟩ : syracuseStep 13625981 = 5109743) B5109743
theorem B7277213 : Blo 1794098 7277213 := bstep (se 3 (by rfl) ⟨1364477, by rfl⟩ : syracuseStep 7277213 = 2728955) B2728955
theorem B3886187 : Blo 1794098 3886187 := bstep (se 1 (by rfl) ⟨2914640, by rfl⟩ : syracuseStep 3886187 = 5829281) B5829281
theorem B2018479 : Blo 1794098 2018479 := bstep (se 1 (by rfl) ⟨1513859, by rfl⟩ : syracuseStep 2018479 = 3027719) B3027719
theorem B36859283 : Blo 1794098 36859283 := bstep (se 1 (by rfl) ⟨27644462, by rfl⟩ : syracuseStep 36859283 = 55288925) B55288925
theorem B2019199 : Blo 1794098 2019199 := bstep (se 1 (by rfl) ⟨1514399, by rfl⟩ : syracuseStep 2019199 = 3028799) B3028799
theorem B4542439 : Blo 1794098 4542439 := bstep (se 1 (by rfl) ⟨3406829, by rfl⟩ : syracuseStep 4542439 = 6813659) B6813659
theorem B24899633 : Blo 1794098 24899633 := bstep (se 2 (by rfl) ⟨9337362, by rfl⟩ : syracuseStep 24899633 = 18674725) B18674725
theorem B2691167 : Blo 1794098 2691167 := bstep (se 1 (by rfl) ⟨2018375, by rfl⟩ : syracuseStep 2691167 = 4036751) B4036751
theorem B2691179 : Blo 1794098 2691179 := bstep (se 1 (by rfl) ⟨2018384, by rfl⟩ : syracuseStep 2691179 = 4036769) B4036769
theorem B2691227 : Blo 1794098 2691227 := bstep (se 1 (by rfl) ⟨2018420, by rfl⟩ : syracuseStep 2691227 = 4036841) B4036841
theorem B2019739 : Blo 1794098 2019739 := bstep (se 1 (by rfl) ⟨1514804, by rfl⟩ : syracuseStep 2019739 = 3029609) B3029609
theorem B10220033 : Blo 1794098 10220033 := bstep (se 2 (by rfl) ⟨3832512, by rfl⟩ : syracuseStep 10220033 = 7665025) B7665025
theorem B15331963 : Blo 1794098 15331963 := bstep (se 1 (by rfl) ⟨11498972, by rfl⟩ : syracuseStep 15331963 = 22997945) B22997945
theorem B10220215 : Blo 1794098 10220215 := bstep (se 1 (by rfl) ⟨7665161, by rfl⟩ : syracuseStep 10220215 = 15330323) B15330323
theorem B14758793 : Blo 1794098 14758793 := bstep (se 2 (by rfl) ⟨5534547, by rfl⟩ : syracuseStep 14758793 = 11069095) B11069095
theorem B13816813 : Blo 1794098 13816813 := bstep (se 3 (by rfl) ⟨2590652, by rfl⟩ : syracuseStep 13816813 = 5181305) B5181305
theorem B2692079 : Blo 1794098 2692079 := bstep (se 1 (by rfl) ⟨2019059, by rfl⟩ : syracuseStep 2692079 = 4038119) B4038119
theorem B3028009 : Blo 1794098 3028009 := bstep (se 2 (by rfl) ⟨1135503, by rfl⟩ : syracuseStep 3028009 = 2271007) B2271007
theorem B2020423 : Blo 1794098 2020423 := bstep (se 1 (by rfl) ⟨1515317, by rfl⟩ : syracuseStep 2020423 = 3030635) B3030635
theorem B6812855 : Blo 1794098 6812855 := bstep (se 1 (by rfl) ⟨5109641, by rfl⟩ : syracuseStep 6812855 = 10219283) B10219283
theorem B3028151 : Blo 1794098 3028151 := bstep (se 1 (by rfl) ⟨2271113, by rfl⟩ : syracuseStep 3028151 = 4542227) B4542227
theorem B2020603 : Blo 1794098 2020603 := bstep (se 1 (by rfl) ⟨1515452, by rfl⟩ : syracuseStep 2020603 = 3030905) B3030905
theorem B2692463 : Blo 1794098 2692463 := bstep (se 1 (by rfl) ⟨2019347, by rfl⟩ : syracuseStep 2692463 = 4038695) B4038695
theorem B6813143 : Blo 1794098 6813143 := bstep (se 1 (by rfl) ⟨5109857, by rfl⟩ : syracuseStep 6813143 = 10219715) B10219715
theorem B13628897 : Blo 1794098 13628897 := bstep (se 2 (by rfl) ⟨5110836, by rfl⟩ : syracuseStep 13628897 = 10221673) B10221673
theorem B2692583 : Blo 1794098 2692583 := bstep (se 1 (by rfl) ⟨2019437, by rfl⟩ : syracuseStep 2692583 = 4038875) B4038875
theorem B15332921 : Blo 1794098 15332921 := bstep (se 2 (by rfl) ⟨5749845, by rfl⟩ : syracuseStep 15332921 = 11499691) B11499691
theorem B2692745 : Blo 1794098 2692745 := bstep (se 2 (by rfl) ⟨1009779, by rfl⟩ : syracuseStep 2692745 = 2019559) B2019559
theorem B2692763 : Blo 1794098 2692763 := bstep (se 1 (by rfl) ⟨2019572, by rfl⟩ : syracuseStep 2692763 = 4039145) B4039145
theorem B16373515 : Blo 1794098 16373515 := bstep (se 1 (by rfl) ⟨12280136, by rfl⟩ : syracuseStep 16373515 = 24560273) B24560273
theorem B51779411 : Blo 1794098 51779411 := bstep (se 1 (by rfl) ⟨38834558, by rfl⟩ : syracuseStep 51779411 = 77669117) B77669117
theorem B2692955 : Blo 1794098 2692955 := bstep (se 1 (by rfl) ⟨2019716, by rfl⟩ : syracuseStep 2692955 = 4039433) B4039433
theorem B3028907 : Blo 1794098 3028907 := bstep (se 1 (by rfl) ⟨2271680, by rfl⟩ : syracuseStep 3028907 = 4543361) B4543361
theorem B2693339 : Blo 1794098 2693339 := bstep (se 1 (by rfl) ⟨2020004, by rfl⟩ : syracuseStep 2693339 = 4040009) B4040009
theorem B4036895 : Blo 1794098 4036895 := bstep (se 1 (by rfl) ⟨3027671, by rfl⟩ : syracuseStep 4036895 = 6055343) B6055343
theorem B3832103 : Blo 1794098 3832103 := bstep (se 1 (by rfl) ⟨2874077, by rfl⟩ : syracuseStep 3832103 = 5748155) B5748155
theorem B13629869 : Blo 1794098 13629869 := bstep (se 3 (by rfl) ⟨2555600, by rfl⟩ : syracuseStep 13629869 = 5111201) B5111201
theorem B3029447 : Blo 1794098 3029447 := bstep (se 1 (by rfl) ⟨2272085, by rfl⟩ : syracuseStep 3029447 = 4544171) B4544171
theorem B2693609 : Blo 1794098 2693609 := bstep (se 2 (by rfl) ⟨1010103, by rfl⟩ : syracuseStep 2693609 = 2020207) B2020207
theorem B4037147 : Blo 1794098 4037147 := bstep (se 1 (by rfl) ⟨3027860, by rfl⟩ : syracuseStep 4037147 = 6055721) B6055721
theorem B3406367 : Blo 1794098 3406367 := bstep (se 1 (by rfl) ⟨2554775, by rfl⟩ : syracuseStep 3406367 = 5109551) B5109551
theorem B6060635 : Blo 1794098 6060635 := bstep (se 1 (by rfl) ⟨4545476, by rfl⟩ : syracuseStep 6060635 = 9090953) B9090953
theorem B6814313 : Blo 1794098 6814313 := bstep (se 2 (by rfl) ⟨2555367, by rfl⟩ : syracuseStep 6814313 = 5110735) B5110735
theorem B3029663 : Blo 1794098 3029663 := bstep (se 1 (by rfl) ⟨2272247, by rfl⟩ : syracuseStep 3029663 = 4544495) B4544495
theorem B3029737 : Blo 1794098 3029737 := bstep (se 2 (by rfl) ⟨1136151, by rfl⟩ : syracuseStep 3029737 = 2272303) B2272303
theorem B4545335 : Blo 1794098 4545335 := bstep (se 1 (by rfl) ⟨3409001, by rfl⟩ : syracuseStep 4545335 = 6818003) B6818003
theorem B2693999 : Blo 1794098 2693999 := bstep (se 1 (by rfl) ⟨2020499, by rfl⟩ : syracuseStep 2693999 = 4040999) B4040999
theorem B2694011 : Blo 1794098 2694011 := bstep (se 1 (by rfl) ⟨2020508, by rfl⟩ : syracuseStep 2694011 = 4041017) B4041017
theorem B6470855 : Blo 1794098 6470855 := bstep (se 1 (by rfl) ⟨4853141, by rfl⟩ : syracuseStep 6470855 = 9706283) B9706283
theorem B2555111 : Blo 1794098 2555111 := bstep (se 1 (by rfl) ⟨1916333, by rfl⟩ : syracuseStep 2555111 = 3832667) B3832667
theorem B6061337 : Blo 1794098 6061337 := bstep (se 2 (by rfl) ⟨2273001, by rfl⟩ : syracuseStep 6061337 = 4546003) B4546003
theorem B6815087 : Blo 1794098 6815087 := bstep (se 1 (by rfl) ⟨5111315, by rfl⟩ : syracuseStep 6815087 = 10222631) B10222631
theorem B3833257 : Blo 1794098 3833257 := bstep (se 2 (by rfl) ⟨1437471, by rfl⟩ : syracuseStep 3833257 = 2874943) B2874943
theorem B59030957 : Blo 1794098 59030957 := bstep (se 3 (by rfl) ⟨11068304, by rfl⟩ : syracuseStep 59030957 = 22136609) B22136609
theorem B25886303 : Blo 1794098 25886303 := bstep (se 1 (by rfl) ⟨19414727, by rfl⟩ : syracuseStep 25886303 = 38829455) B38829455
theorem B4038497 : Blo 1794098 4038497 := bstep (se 2 (by rfl) ⟨1514436, by rfl⟩ : syracuseStep 4038497 = 3028873) B3028873
theorem B9084797 : Blo 1794098 9084797 := bstep (se 3 (by rfl) ⟨1703399, by rfl⟩ : syracuseStep 9084797 = 3406799) B3406799
theorem B3833743 : Blo 1794098 3833743 := bstep (se 1 (by rfl) ⟨2875307, by rfl⟩ : syracuseStep 3833743 = 5750615) B5750615
theorem B29097899 : Blo 1794098 29097899 := bstep (se 1 (by rfl) ⟨21823424, by rfl⟩ : syracuseStep 29097899 = 43646849) B43646849
theorem B4038623 : Blo 1794098 4038623 := bstep (se 1 (by rfl) ⟨3028967, by rfl⟩ : syracuseStep 4038623 = 6057935) B6057935
theorem B1794111 : Blo 1794098 1794111 := bstep (se 1 (by rfl) ⟨1345583, by rfl⟩ : syracuseStep 1794111 = 2691167) B2691167
theorem B1794119 : Blo 1794098 1794119 := bstep (se 1 (by rfl) ⟨1345589, by rfl⟩ : syracuseStep 1794119 = 2691179) B2691179
theorem B1794151 : Blo 1794098 1794151 := bstep (se 1 (by rfl) ⟨1345613, by rfl⟩ : syracuseStep 1794151 = 2691227) B2691227
theorem B12288185 : Blo 1794098 12288185 := bstep (se 2 (by rfl) ⟨4608069, by rfl⟩ : syracuseStep 12288185 = 9216139) B9216139
theorem B9839195 : Blo 1794098 9839195 := bstep (se 1 (by rfl) ⟨7379396, by rfl⟩ : syracuseStep 9839195 = 14758793) B14758793
theorem B1794719 : Blo 1794098 1794719 := bstep (se 1 (by rfl) ⟨1346039, by rfl⟩ : syracuseStep 1794719 = 2692079) B2692079
theorem B6816575 : Blo 1794098 6816575 := bstep (se 1 (by rfl) ⟨5112431, by rfl⟩ : syracuseStep 6816575 = 10224863) B10224863
theorem B2589511 : Blo 1794098 2589511 := bstep (se 1 (by rfl) ⟨1942133, by rfl⟩ : syracuseStep 2589511 = 3884267) B3884267
theorem B1794975 : Blo 1794098 1794975 := bstep (se 1 (by rfl) ⟨1346231, by rfl⟩ : syracuseStep 1794975 = 2692463) B2692463
theorem B4039649 : Blo 1794098 4039649 := bstep (se 2 (by rfl) ⟨1514868, by rfl⟩ : syracuseStep 4039649 = 3029737) B3029737
theorem B9085931 : Blo 1794098 9085931 := bstep (se 1 (by rfl) ⟨6814448, by rfl⟩ : syracuseStep 9085931 = 13628897) B13628897
theorem B1795055 : Blo 1794098 1795055 := bstep (se 1 (by rfl) ⟨1346291, by rfl⟩ : syracuseStep 1795055 = 2692583) B2692583
theorem B1795163 : Blo 1794098 1795163 := bstep (se 1 (by rfl) ⟨1346372, by rfl⟩ : syracuseStep 1795163 = 2692745) B2692745
theorem B1795175 : Blo 1794098 1795175 := bstep (se 1 (by rfl) ⟨1346381, by rfl⟩ : syracuseStep 1795175 = 2692763) B2692763
theorem B41452661 : Blo 1794098 41452661 := bstep (se 5 (by rfl) ⟨1943093, by rfl⟩ : syracuseStep 41452661 = 3886187) B3886187
theorem B5751947 : Blo 1794098 5751947 := bstep (se 1 (by rfl) ⟨4313960, by rfl⟩ : syracuseStep 5751947 = 8627921) B8627921
theorem B1795303 : Blo 1794098 1795303 := bstep (se 1 (by rfl) ⟨1346477, by rfl⟩ : syracuseStep 1795303 = 2692955) B2692955
theorem B11503073 : Blo 1794098 11503073 := bstep (se 2 (by rfl) ⟨4313652, by rfl⟩ : syracuseStep 11503073 = 8627305) B8627305
theorem B1795559 : Blo 1794098 1795559 := bstep (se 1 (by rfl) ⟨1346669, by rfl⟩ : syracuseStep 1795559 = 2693339) B2693339
theorem B9086579 : Blo 1794098 9086579 := bstep (se 1 (by rfl) ⟨6814934, by rfl⟩ : syracuseStep 9086579 = 13629869) B13629869
theorem B5113469 : Blo 1794098 5113469 := bstep (se 3 (by rfl) ⟨958775, by rfl⟩ : syracuseStep 5113469 = 1917551) B1917551
theorem B1795739 : Blo 1794098 1795739 := bstep (se 1 (by rfl) ⟨1346804, by rfl⟩ : syracuseStep 1795739 = 2693609) B2693609
theorem B2270911 : Blo 1794098 2270911 := bstep (se 1 (by rfl) ⟨1703183, by rfl⟩ : syracuseStep 2270911 = 3406367) B3406367
theorem B4040423 : Blo 1794098 4040423 := bstep (se 1 (by rfl) ⟨3030317, by rfl⟩ : syracuseStep 4040423 = 6060635) B6060635
theorem B6227837 : Blo 1794098 6227837 := bstep (se 3 (by rfl) ⟨1167719, by rfl⟩ : syracuseStep 6227837 = 2335439) B2335439
theorem B1795999 : Blo 1794098 1795999 := bstep (se 1 (by rfl) ⟨1346999, by rfl⟩ : syracuseStep 1795999 = 2693999) B2693999
theorem B1796007 : Blo 1794098 1796007 := bstep (se 1 (by rfl) ⟨1347005, by rfl⟩ : syracuseStep 1796007 = 2694011) B2694011
theorem B4040891 : Blo 1794098 4040891 := bstep (se 1 (by rfl) ⟨3030668, by rfl⟩ : syracuseStep 4040891 = 6061337) B6061337
theorem B6056531 : Blo 1794098 6056531 := bstep (se 1 (by rfl) ⟨4542398, by rfl⟩ : syracuseStep 6056531 = 9084797) B9084797
theorem B6056585 : Blo 1794098 6056585 := bstep (se 2 (by rfl) ⟨2271219, by rfl⟩ : syracuseStep 6056585 = 4542439) B4542439
theorem B16599755 : Blo 1794098 16599755 := bstep (se 1 (by rfl) ⟨12449816, by rfl⟩ : syracuseStep 16599755 = 24899633) B24899633
theorem B4852601 : Blo 1794098 4852601 := bstep (se 2 (by rfl) ⟨1819725, by rfl⟩ : syracuseStep 4852601 = 3639451) B3639451
theorem B9088199 : Blo 1794098 9088199 := bstep (se 1 (by rfl) ⟨6816149, by rfl⟩ : syracuseStep 9088199 = 13632299) B13632299
theorem B4541903 : Blo 1794098 4541903 := bstep (se 1 (by rfl) ⟨3406427, by rfl⟩ : syracuseStep 4541903 = 6812855) B6812855
theorem B2018767 : Blo 1794098 2018767 := bstep (se 1 (by rfl) ⟨1514075, by rfl⟩ : syracuseStep 2018767 = 3028151) B3028151
theorem B20442617 : Blo 1794098 20442617 := bstep (se 2 (by rfl) ⟨7665981, by rfl⟩ : syracuseStep 20442617 = 15331963) B15331963
theorem B2272799 : Blo 1794098 2272799 := bstep (se 1 (by rfl) ⟨1704599, by rfl⟩ : syracuseStep 2272799 = 3409199) B3409199
theorem B13626953 : Blo 1794098 13626953 := bstep (se 2 (by rfl) ⟨5110107, by rfl⟩ : syracuseStep 13626953 = 10220215) B10220215
theorem B4542095 : Blo 1794098 4542095 := bstep (se 1 (by rfl) ⟨3406571, by rfl⟩ : syracuseStep 4542095 = 6813143) B6813143
theorem B2019271 : Blo 1794098 2019271 := bstep (se 1 (by rfl) ⟨1514453, by rfl⟩ : syracuseStep 2019271 = 3028907) B3028907
theorem B2691263 : Blo 1794098 2691263 := bstep (se 1 (by rfl) ⟨2018447, by rfl⟩ : syracuseStep 2691263 = 4036895) B4036895
theorem B2691305 : Blo 1794098 2691305 := bstep (se 2 (by rfl) ⟨1009239, by rfl⟩ : syracuseStep 2691305 = 2018479) B2018479
theorem B46018853 : Blo 1794098 46018853 := bstep (se 4 (by rfl) ⟨4314267, by rfl⟩ : syracuseStep 46018853 = 8628535) B8628535
theorem B2019631 : Blo 1794098 2019631 := bstep (se 1 (by rfl) ⟨1514723, by rfl⟩ : syracuseStep 2019631 = 3029447) B3029447
theorem B23310683 : Blo 1794098 23310683 := bstep (se 1 (by rfl) ⟨17483012, by rfl⟩ : syracuseStep 23310683 = 34966025) B34966025
theorem B2691431 : Blo 1794098 2691431 := bstep (se 1 (by rfl) ⟨2018573, by rfl⟩ : syracuseStep 2691431 = 4037147) B4037147
theorem B4542875 : Blo 1794098 4542875 := bstep (se 1 (by rfl) ⟨3407156, by rfl⟩ : syracuseStep 4542875 = 6814313) B6814313
theorem B2019775 : Blo 1794098 2019775 := bstep (se 1 (by rfl) ⟨1514831, by rfl⟩ : syracuseStep 2019775 = 3029663) B3029663
theorem B4313903 : Blo 1794098 4313903 := bstep (se 1 (by rfl) ⟨3235427, by rfl⟩ : syracuseStep 4313903 = 6470855) B6470855
theorem B4543391 : Blo 1794098 4543391 := bstep (se 1 (by rfl) ⟨3407543, by rfl⟩ : syracuseStep 4543391 = 6815087) B6815087
theorem B24572855 : Blo 1794098 24572855 := bstep (se 1 (by rfl) ⟨18429641, by rfl⟩ : syracuseStep 24572855 = 36859283) B36859283
theorem B17257535 : Blo 1794098 17257535 := bstep (se 1 (by rfl) ⟨12943151, by rfl⟩ : syracuseStep 17257535 = 25886303) B25886303
theorem B2692265 : Blo 1794098 2692265 := bstep (se 2 (by rfl) ⟨1009599, by rfl⟩ : syracuseStep 2692265 = 2019199) B2019199
theorem B2692331 : Blo 1794098 2692331 := bstep (se 1 (by rfl) ⟨2019248, by rfl⟩ : syracuseStep 2692331 = 4038497) B4038497
theorem B2692415 : Blo 1794098 2692415 := bstep (se 1 (by rfl) ⟨2019311, by rfl⟩ : syracuseStep 2692415 = 4038623) B4038623
theorem B2692607 : Blo 1794098 2692607 := bstep (se 1 (by rfl) ⟨2019455, by rfl⟩ : syracuseStep 2692607 = 4038911) B4038911
theorem B2692715 : Blo 1794098 2692715 := bstep (se 1 (by rfl) ⟨2019536, by rfl⟩ : syracuseStep 2692715 = 4039073) B4039073
theorem B6813355 : Blo 1794098 6813355 := bstep (se 1 (by rfl) ⟨5110016, by rfl⟩ : syracuseStep 6813355 = 10220033) B10220033
theorem B2692985 : Blo 1794098 2692985 := bstep (se 2 (by rfl) ⟨1009869, by rfl⟩ : syracuseStep 2692985 = 2019739) B2019739
theorem B6813629 : Blo 1794098 6813629 := bstep (se 3 (by rfl) ⟨1277555, by rfl⟩ : syracuseStep 6813629 = 2555111) B2555111
theorem B34494457 : Blo 1794098 34494457 := bstep (se 2 (by rfl) ⟨12935421, by rfl⟩ : syracuseStep 34494457 = 25870843) B25870843
theorem B25245697 : Blo 1794098 25245697 := bstep (se 2 (by rfl) ⟨9467136, by rfl⟩ : syracuseStep 25245697 = 18934273) B18934273
theorem B2693231 : Blo 1794098 2693231 := bstep (se 1 (by rfl) ⟨2019923, by rfl⟩ : syracuseStep 2693231 = 4039847) B4039847
theorem B2693303 : Blo 1794098 2693303 := bstep (se 1 (by rfl) ⟨2019977, by rfl⟩ : syracuseStep 2693303 = 4039955) B4039955
theorem B3234023 : Blo 1794098 3234023 := bstep (se 1 (by rfl) ⟨2425517, by rfl⟩ : syracuseStep 3234023 = 4851035) B4851035
theorem B4036967 : Blo 1794098 4036967 := bstep (se 1 (by rfl) ⟨3027725, by rfl⟩ : syracuseStep 4036967 = 6055451) B6055451
theorem B10221947 : Blo 1794098 10221947 := bstep (se 1 (by rfl) ⟨7666460, by rfl⟩ : syracuseStep 10221947 = 15332921) B15332921
theorem B14948819 : Blo 1794098 14948819 := bstep (se 1 (by rfl) ⟨11211614, by rfl⟩ : syracuseStep 14948819 = 22423229) B22423229
theorem B4545031 : Blo 1794098 4545031 := bstep (se 1 (by rfl) ⟨3408773, by rfl⟩ : syracuseStep 4545031 = 6817547) B6817547
theorem B34519607 : Blo 1794098 34519607 := bstep (se 1 (by rfl) ⟨25889705, by rfl⟩ : syracuseStep 34519607 = 51779411) B51779411
theorem B2693723 : Blo 1794098 2693723 := bstep (se 1 (by rfl) ⟨2020292, by rfl⟩ : syracuseStep 2693723 = 4040585) B4040585
theorem B2693735 : Blo 1794098 2693735 := bstep (se 1 (by rfl) ⟨2020301, by rfl⟩ : syracuseStep 2693735 = 4040603) B4040603
theorem B2693759 : Blo 1794098 2693759 := bstep (se 1 (by rfl) ⟨2020319, by rfl⟩ : syracuseStep 2693759 = 4040639) B4040639
theorem B18422417 : Blo 1794098 18422417 := bstep (se 2 (by rfl) ⟨6908406, by rfl⟩ : syracuseStep 18422417 = 13816813) B13816813
theorem B4037345 : Blo 1794098 4037345 := bstep (se 2 (by rfl) ⟨1514004, by rfl⟩ : syracuseStep 4037345 = 3028009) B3028009
theorem B2693867 : Blo 1794098 2693867 := bstep (se 1 (by rfl) ⟨2020400, by rfl⟩ : syracuseStep 2693867 = 4040801) B4040801
theorem B2693897 : Blo 1794098 2693897 := bstep (se 2 (by rfl) ⟨1010211, by rfl⟩ : syracuseStep 2693897 = 2020423) B2020423
theorem B2554735 : Blo 1794098 2554735 := bstep (se 1 (by rfl) ⟨1916051, by rfl⟩ : syracuseStep 2554735 = 3832103) B3832103
theorem B5184445 : Blo 1794098 5184445 := bstep (se 3 (by rfl) ⟨972083, by rfl⟩ : syracuseStep 5184445 = 1944167) B1944167
theorem B2694137 : Blo 1794098 2694137 := bstep (se 2 (by rfl) ⟨1010301, by rfl⟩ : syracuseStep 2694137 = 2020603) B2020603
theorem B19405901 : Blo 1794098 19405901 := bstep (se 3 (by rfl) ⟨3638606, by rfl⟩ : syracuseStep 19405901 = 7277213) B7277213
theorem B9083987 : Blo 1794098 9083987 := bstep (se 1 (by rfl) ⟨6812990, by rfl⟩ : syracuseStep 9083987 = 13625981) B13625981
theorem B3030223 : Blo 1794098 3030223 := bstep (se 1 (by rfl) ⟨2272667, by rfl⟩ : syracuseStep 3030223 = 4545335) B4545335
theorem B5111009 : Blo 1794098 5111009 := bstep (se 2 (by rfl) ⟨1916628, by rfl⟩ : syracuseStep 5111009 = 3833257) B3833257
theorem B39353971 : Blo 1794098 39353971 := bstep (se 1 (by rfl) ⟨29515478, by rfl⟩ : syracuseStep 39353971 = 59030957) B59030957
theorem B21831353 : Blo 1794098 21831353 := bstep (se 2 (by rfl) ⟨8186757, by rfl⟩ : syracuseStep 21831353 = 16373515) B16373515
theorem B5111657 : Blo 1794098 5111657 := bstep (se 2 (by rfl) ⟨1916871, by rfl⟩ : syracuseStep 5111657 = 3833743) B3833743
theorem B19398599 : Blo 1794098 19398599 := bstep (se 1 (by rfl) ⟨14548949, by rfl⟩ : syracuseStep 19398599 = 29097899) B29097899
theorem B33660929 : Blo 1794098 33660929 := bstep (se 2 (by rfl) ⟨12622848, by rfl⟩ : syracuseStep 33660929 = 25245697) B25245697
theorem B8192123 : Blo 1794098 8192123 := bstep (se 1 (by rfl) ⟨6144092, by rfl⟩ : syracuseStep 8192123 = 12288185) B12288185
theorem B1794175 : Blo 1794098 1794175 := bstep (se 1 (by rfl) ⟨1345631, by rfl⟩ : syracuseStep 1794175 = 2691263) B2691263
theorem B1794203 : Blo 1794098 1794203 := bstep (se 1 (by rfl) ⟨1345652, by rfl⟩ : syracuseStep 1794203 = 2691305) B2691305
theorem B30679235 : Blo 1794098 30679235 := bstep (se 1 (by rfl) ⟨23009426, by rfl⟩ : syracuseStep 30679235 = 46018853) B46018853
theorem B15540455 : Blo 1794098 15540455 := bstep (se 1 (by rfl) ⟨11655341, by rfl⟩ : syracuseStep 15540455 = 23310683) B23310683
theorem B1794287 : Blo 1794098 1794287 := bstep (se 1 (by rfl) ⟨1345715, by rfl⟩ : syracuseStep 1794287 = 2691431) B2691431
theorem B3834631 : Blo 1794098 3834631 := bstep (se 1 (by rfl) ⟨2875973, by rfl⟩ : syracuseStep 3834631 = 5751947) B5751947
theorem B1794843 : Blo 1794098 1794843 := bstep (se 1 (by rfl) ⟨1346132, by rfl⟩ : syracuseStep 1794843 = 2692265) B2692265
theorem B1794887 : Blo 1794098 1794887 := bstep (se 1 (by rfl) ⟨1346165, by rfl⟩ : syracuseStep 1794887 = 2692331) B2692331
theorem B1794943 : Blo 1794098 1794943 := bstep (se 1 (by rfl) ⟨1346207, by rfl⟩ : syracuseStep 1794943 = 2692415) B2692415
theorem B1795071 : Blo 1794098 1795071 := bstep (se 1 (by rfl) ⟨1346303, by rfl⟩ : syracuseStep 1795071 = 2692607) B2692607
theorem B1795143 : Blo 1794098 1795143 := bstep (se 1 (by rfl) ⟨1346357, by rfl⟩ : syracuseStep 1795143 = 2692715) B2692715
theorem B3408979 : Blo 1794098 3408979 := bstep (se 1 (by rfl) ⟨2556734, by rfl⟩ : syracuseStep 3408979 = 5113469) B5113469
theorem B1795323 : Blo 1794098 1795323 := bstep (se 1 (by rfl) ⟨1346492, by rfl⟩ : syracuseStep 1795323 = 2692985) B2692985
theorem B1795487 : Blo 1794098 1795487 := bstep (se 1 (by rfl) ⟨1346615, by rfl⟩ : syracuseStep 1795487 = 2693231) B2693231
theorem B1795535 : Blo 1794098 1795535 := bstep (se 1 (by rfl) ⟨1346651, by rfl⟩ : syracuseStep 1795535 = 2693303) B2693303
theorem B2156015 : Blo 1794098 2156015 := bstep (se 1 (by rfl) ⟨1617011, by rfl⟩ : syracuseStep 2156015 = 3234023) B3234023
theorem B4040297 : Blo 1794098 4040297 := bstep (se 2 (by rfl) ⟨1515111, by rfl⟩ : syracuseStep 4040297 = 3030223) B3030223
theorem B23013071 : Blo 1794098 23013071 := bstep (se 1 (by rfl) ⟨17259803, by rfl⟩ : syracuseStep 23013071 = 34519607) B34519607
theorem B1795815 : Blo 1794098 1795815 := bstep (se 1 (by rfl) ⟨1346861, by rfl⟩ : syracuseStep 1795815 = 2693723) B2693723
theorem B1795823 : Blo 1794098 1795823 := bstep (se 1 (by rfl) ⟨1346867, by rfl⟩ : syracuseStep 1795823 = 2693735) B2693735
theorem B1795839 : Blo 1794098 1795839 := bstep (se 1 (by rfl) ⟨1346879, by rfl⟩ : syracuseStep 1795839 = 2693759) B2693759
theorem B1795911 : Blo 1794098 1795911 := bstep (se 1 (by rfl) ⟨1346933, by rfl⟩ : syracuseStep 1795911 = 2693867) B2693867
theorem B1795931 : Blo 1794098 1795931 := bstep (se 1 (by rfl) ⟨1346948, by rfl⟩ : syracuseStep 1795931 = 2693897) B2693897
theorem B1796091 : Blo 1794098 1796091 := bstep (se 1 (by rfl) ⟨1347068, by rfl⟩ : syracuseStep 1796091 = 2694137) B2694137
theorem B12937267 : Blo 1794098 12937267 := bstep (se 1 (by rfl) ⟨9702950, by rfl⟩ : syracuseStep 12937267 = 19405901) B19405901
theorem B6055991 : Blo 1794098 6055991 := bstep (se 1 (by rfl) ⟨4541993, by rfl⟩ : syracuseStep 6055991 = 9083987) B9083987
theorem B11503741 : Blo 1794098 11503741 := bstep (se 3 (by rfl) ⟨2156951, by rfl⟩ : syracuseStep 11503741 = 4313903) B4313903
theorem B52471961 : Blo 1794098 52471961 := bstep (se 2 (by rfl) ⟨19676985, by rfl⟩ : syracuseStep 52471961 = 39353971) B39353971
theorem B45992609 : Blo 1794098 45992609 := bstep (se 2 (by rfl) ⟨17247228, by rfl⟩ : syracuseStep 45992609 = 34494457) B34494457
theorem B6057287 : Blo 1794098 6057287 := bstep (se 1 (by rfl) ⟨4542965, by rfl⟩ : syracuseStep 6057287 = 9085931) B9085931
theorem B11505023 : Blo 1794098 11505023 := bstep (se 1 (by rfl) ⟨8628767, by rfl⟩ : syracuseStep 11505023 = 17257535) B17257535
theorem B27635107 : Blo 1794098 27635107 := bstep (se 1 (by rfl) ⟨20726330, by rfl⟩ : syracuseStep 27635107 = 41452661) B41452661
theorem B6057719 : Blo 1794098 6057719 := bstep (se 1 (by rfl) ⟨4543289, by rfl⟩ : syracuseStep 6057719 = 9086579) B9086579
theorem B3452681 : Blo 1794098 3452681 := bstep (se 2 (by rfl) ⟨1294755, by rfl⟩ : syracuseStep 3452681 = 2589511) B2589511
theorem B30674861 : Blo 1794098 30674861 := bstep (se 3 (by rfl) ⟨5751536, by rfl⟩ : syracuseStep 30674861 = 11503073) B11503073
theorem B4542419 : Blo 1794098 4542419 := bstep (se 1 (by rfl) ⟨3406814, by rfl⟩ : syracuseStep 4542419 = 6813629) B6813629
theorem B2691311 : Blo 1794098 2691311 := bstep (se 1 (by rfl) ⟨2018483, by rfl⟩ : syracuseStep 2691311 = 4036967) B4036967
theorem B9965879 : Blo 1794098 9965879 := bstep (se 1 (by rfl) ⟨7474409, by rfl⟩ : syracuseStep 9965879 = 14948819) B14948819
theorem B2691563 : Blo 1794098 2691563 := bstep (se 1 (by rfl) ⟨2018672, by rfl⟩ : syracuseStep 2691563 = 4037345) B4037345
theorem B2691689 : Blo 1794098 2691689 := bstep (se 2 (by rfl) ⟨1009383, by rfl⟩ : syracuseStep 2691689 = 2018767) B2018767
theorem B6058799 : Blo 1794098 6058799 := bstep (se 1 (by rfl) ⟨4544099, by rfl⟩ : syracuseStep 6058799 = 9088199) B9088199
theorem B3027881 : Blo 1794098 3027881 := bstep (se 2 (by rfl) ⟨1135455, by rfl⟩ : syracuseStep 3027881 = 2270911) B2270911
theorem B3027935 : Blo 1794098 3027935 := bstep (se 1 (by rfl) ⟨2270951, by rfl⟩ : syracuseStep 3027935 = 4541903) B4541903
theorem B13628411 : Blo 1794098 13628411 := bstep (se 1 (by rfl) ⟨10221308, by rfl⟩ : syracuseStep 13628411 = 20442617) B20442617
theorem B3028063 : Blo 1794098 3028063 := bstep (se 1 (by rfl) ⟨2271047, by rfl⟩ : syracuseStep 3028063 = 4542095) B4542095
theorem B14554235 : Blo 1794098 14554235 := bstep (se 1 (by rfl) ⟨10915676, by rfl⟩ : syracuseStep 14554235 = 21831353) B21831353
theorem B2692361 : Blo 1794098 2692361 := bstep (se 2 (by rfl) ⟨1009635, by rfl⟩ : syracuseStep 2692361 = 2019271) B2019271
theorem B12932399 : Blo 1794098 12932399 := bstep (se 1 (by rfl) ⟨9699299, by rfl⟩ : syracuseStep 12932399 = 19398599) B19398599
theorem B3028583 : Blo 1794098 3028583 := bstep (se 1 (by rfl) ⟨2271437, by rfl⟩ : syracuseStep 3028583 = 4542875) B4542875
theorem B2692841 : Blo 1794098 2692841 := bstep (se 2 (by rfl) ⟨1009815, by rfl⟩ : syracuseStep 2692841 = 2019631) B2019631
theorem B6559463 : Blo 1794098 6559463 := bstep (se 1 (by rfl) ⟨4919597, by rfl⟩ : syracuseStep 6559463 = 9839195) B9839195
theorem B4544383 : Blo 1794098 4544383 := bstep (se 1 (by rfl) ⟨3408287, by rfl⟩ : syracuseStep 4544383 = 6816575) B6816575
theorem B2693033 : Blo 1794098 2693033 := bstep (se 2 (by rfl) ⟨1009887, by rfl⟩ : syracuseStep 2693033 = 2019775) B2019775
theorem B3028927 : Blo 1794098 3028927 := bstep (se 1 (by rfl) ⟨2271695, by rfl⟩ : syracuseStep 3028927 = 4543391) B4543391
theorem B2693099 : Blo 1794098 2693099 := bstep (se 1 (by rfl) ⟨2019824, by rfl⟩ : syracuseStep 2693099 = 4039649) B4039649
theorem B6060041 : Blo 1794098 6060041 := bstep (se 2 (by rfl) ⟨2272515, by rfl⟩ : syracuseStep 6060041 = 4545031) B4545031
theorem B3406313 : Blo 1794098 3406313 := bstep (se 2 (by rfl) ⟨1277367, by rfl⟩ : syracuseStep 3406313 = 2554735) B2554735
theorem B2693615 : Blo 1794098 2693615 := bstep (se 1 (by rfl) ⟨2020211, by rfl⟩ : syracuseStep 2693615 = 4040423) B4040423
theorem B6912593 : Blo 1794098 6912593 := bstep (se 2 (by rfl) ⟨2592222, by rfl⟩ : syracuseStep 6912593 = 5184445) B5184445
theorem B4151891 : Blo 1794098 4151891 := bstep (se 1 (by rfl) ⟨3113918, by rfl⟩ : syracuseStep 4151891 = 6227837) B6227837
theorem B6060797 : Blo 1794098 6060797 := bstep (se 3 (by rfl) ⟨1136399, by rfl⟩ : syracuseStep 6060797 = 2272799) B2272799
theorem B2693927 : Blo 1794098 2693927 := bstep (se 1 (by rfl) ⟨2020445, by rfl⟩ : syracuseStep 2693927 = 4040891) B4040891
theorem B6814631 : Blo 1794098 6814631 := bstep (se 1 (by rfl) ⟨5110973, by rfl⟩ : syracuseStep 6814631 = 10221947) B10221947
theorem B49126445 : Blo 1794098 49126445 := bstep (se 3 (by rfl) ⟨9211208, by rfl⟩ : syracuseStep 49126445 = 18422417) B18422417
theorem B4037687 : Blo 1794098 4037687 := bstep (se 1 (by rfl) ⟨3028265, by rfl⟩ : syracuseStep 4037687 = 6056531) B6056531
theorem B4037723 : Blo 1794098 4037723 := bstep (se 1 (by rfl) ⟨3028292, by rfl⟩ : syracuseStep 4037723 = 6056585) B6056585
theorem B11066503 : Blo 1794098 11066503 := bstep (se 1 (by rfl) ⟨8299877, by rfl⟩ : syracuseStep 11066503 = 16599755) B16599755
theorem B3235067 : Blo 1794098 3235067 := bstep (se 1 (by rfl) ⟨2426300, by rfl⟩ : syracuseStep 3235067 = 4852601) B4852601
theorem B3407339 : Blo 1794098 3407339 := bstep (se 1 (by rfl) ⟨2555504, by rfl⟩ : syracuseStep 3407339 = 5111009) B5111009
theorem B9084473 : Blo 1794098 9084473 := bstep (se 2 (by rfl) ⟨3406677, by rfl⟩ : syracuseStep 9084473 = 6813355) B6813355
theorem B9084635 : Blo 1794098 9084635 := bstep (se 1 (by rfl) ⟨6813476, by rfl⟩ : syracuseStep 9084635 = 13626953) B13626953
theorem B65527613 : Blo 1794098 65527613 := bstep (se 3 (by rfl) ⟨12286427, by rfl⟩ : syracuseStep 65527613 = 24572855) B24572855
theorem B3407771 : Blo 1794098 3407771 := bstep (se 1 (by rfl) ⟨2555828, by rfl⟩ : syracuseStep 3407771 = 5111657) B5111657
theorem B1794207 : Blo 1794098 1794207 := bstep (se 1 (by rfl) ⟨1345655, by rfl⟩ : syracuseStep 1794207 = 2691311) B2691311
theorem B6643919 : Blo 1794098 6643919 := bstep (se 1 (by rfl) ⟨4982939, by rfl⟩ : syracuseStep 6643919 = 9965879) B9965879
theorem B1794375 : Blo 1794098 1794375 := bstep (se 1 (by rfl) ⟨1345781, by rfl⟩ : syracuseStep 1794375 = 2691563) B2691563
theorem B1794459 : Blo 1794098 1794459 := bstep (se 1 (by rfl) ⟨1345844, by rfl⟩ : syracuseStep 1794459 = 2691689) B2691689
theorem B4039199 : Blo 1794098 4039199 := bstep (se 1 (by rfl) ⟨3029399, by rfl⟩ : syracuseStep 4039199 = 6058799) B6058799
theorem B9085607 : Blo 1794098 9085607 := bstep (se 1 (by rfl) ⟨6814205, by rfl⟩ : syracuseStep 9085607 = 13628411) B13628411
theorem B294937301 : Blo 1794098 294937301 := bstep (se 7 (by rfl) ⟨3456296, by rfl⟩ : syracuseStep 294937301 = 6912593) B6912593
theorem B1794907 : Blo 1794098 1794907 := bstep (se 1 (by rfl) ⟨1346180, by rfl⟩ : syracuseStep 1794907 = 2692361) B2692361
theorem B1795227 : Blo 1794098 1795227 := bstep (se 1 (by rfl) ⟨1346420, by rfl⟩ : syracuseStep 1795227 = 2692841) B2692841
theorem B1795355 : Blo 1794098 1795355 := bstep (se 1 (by rfl) ⟨1346516, by rfl⟩ : syracuseStep 1795355 = 2693033) B2693033
theorem B1795399 : Blo 1794098 1795399 := bstep (se 1 (by rfl) ⟨1346549, by rfl⟩ : syracuseStep 1795399 = 2693099) B2693099
theorem B4040027 : Blo 1794098 4040027 := bstep (se 1 (by rfl) ⟨3030020, by rfl⟩ : syracuseStep 4040027 = 6060041) B6060041
theorem B34981307 : Blo 1794098 34981307 := bstep (se 1 (by rfl) ⟨26235980, by rfl⟩ : syracuseStep 34981307 = 52471961) B52471961
theorem B14755337 : Blo 1794098 14755337 := bstep (se 2 (by rfl) ⟨5533251, by rfl⟩ : syracuseStep 14755337 = 11066503) B11066503
theorem B1795743 : Blo 1794098 1795743 := bstep (se 1 (by rfl) ⟨1346807, by rfl⟩ : syracuseStep 1795743 = 2693615) B2693615
theorem B4040531 : Blo 1794098 4040531 := bstep (se 1 (by rfl) ⟨3030398, by rfl⟩ : syracuseStep 4040531 = 6060797) B6060797
theorem B1795951 : Blo 1794098 1795951 := bstep (se 1 (by rfl) ⟨1346963, by rfl⟩ : syracuseStep 1795951 = 2693927) B2693927
theorem B2156711 : Blo 1794098 2156711 := bstep (se 1 (by rfl) ⟨1617533, by rfl⟩ : syracuseStep 2156711 = 3235067) B3235067
theorem B7670015 : Blo 1794098 7670015 := bstep (se 1 (by rfl) ⟨5752511, by rfl⟩ : syracuseStep 7670015 = 11505023) B11505023
theorem B2271559 : Blo 1794098 2271559 := bstep (se 1 (by rfl) ⟨1703669, by rfl⟩ : syracuseStep 2271559 = 3407339) B3407339
theorem B6056315 : Blo 1794098 6056315 := bstep (se 1 (by rfl) ⟨4542236, by rfl⟩ : syracuseStep 6056315 = 9084473) B9084473
theorem B9087389 : Blo 1794098 9087389 := bstep (se 3 (by rfl) ⟨1703885, by rfl⟩ : syracuseStep 9087389 = 3407771) B3407771
theorem B6056423 : Blo 1794098 6056423 := bstep (se 1 (by rfl) ⟨4542317, by rfl⟩ : syracuseStep 6056423 = 9084635) B9084635
theorem B20449907 : Blo 1794098 20449907 := bstep (se 1 (by rfl) ⟨15337430, by rfl⟩ : syracuseStep 20449907 = 30674861) B30674861
theorem B22440619 : Blo 1794098 22440619 := bstep (se 1 (by rfl) ⟨16830464, by rfl⟩ : syracuseStep 22440619 = 33660929) B33660929
theorem B15338321 : Blo 1794098 15338321 := bstep (se 2 (by rfl) ⟨5751870, by rfl⟩ : syracuseStep 15338321 = 11503741) B11503741
theorem B2018587 : Blo 1794098 2018587 := bstep (se 1 (by rfl) ⟨1513940, by rfl⟩ : syracuseStep 2018587 = 3027881) B3027881
theorem B2018623 : Blo 1794098 2018623 := bstep (se 1 (by rfl) ⟨1513967, by rfl⟩ : syracuseStep 2018623 = 3027935) B3027935
theorem B9702823 : Blo 1794098 9702823 := bstep (se 1 (by rfl) ⟨7277117, by rfl⟩ : syracuseStep 9702823 = 14554235) B14554235
theorem B8621599 : Blo 1794098 8621599 := bstep (se 1 (by rfl) ⟨6466199, by rfl⟩ : syracuseStep 8621599 = 12932399) B12932399
theorem B2019055 : Blo 1794098 2019055 := bstep (se 1 (by rfl) ⟨1514291, by rfl⟩ : syracuseStep 2019055 = 3028583) B3028583
theorem B20451365 : Blo 1794098 20451365 := bstep (se 4 (by rfl) ⟨1917315, by rfl⟩ : syracuseStep 20451365 = 3834631) B3834631
theorem B4543087 : Blo 1794098 4543087 := bstep (se 1 (by rfl) ⟨3407315, by rfl⟩ : syracuseStep 4543087 = 6814631) B6814631
theorem B2691791 : Blo 1794098 2691791 := bstep (se 1 (by rfl) ⟨2018843, by rfl⟩ : syracuseStep 2691791 = 4037687) B4037687
theorem B2691815 : Blo 1794098 2691815 := bstep (se 1 (by rfl) ⟨2018861, by rfl⟩ : syracuseStep 2691815 = 4037723) B4037723
theorem B6059177 : Blo 1794098 6059177 := bstep (se 2 (by rfl) ⟨2272191, by rfl⟩ : syracuseStep 6059177 = 4544383) B4544383
theorem B43685075 : Blo 1794098 43685075 := bstep (se 1 (by rfl) ⟨32763806, by rfl⟩ : syracuseStep 43685075 = 65527613) B65527613
theorem B3028279 : Blo 1794098 3028279 := bstep (se 1 (by rfl) ⟨2271209, by rfl⟩ : syracuseStep 3028279 = 4542419) B4542419
theorem B17249689 : Blo 1794098 17249689 := bstep (se 2 (by rfl) ⟨6468633, by rfl⟩ : syracuseStep 17249689 = 12937267) B12937267
theorem B5461415 : Blo 1794098 5461415 := bstep (se 1 (by rfl) ⟨4096061, by rfl⟩ : syracuseStep 5461415 = 8192123) B8192123
theorem B20452823 : Blo 1794098 20452823 := bstep (se 1 (by rfl) ⟨15339617, by rfl⟩ : syracuseStep 20452823 = 30679235) B30679235
theorem B41441213 : Blo 1794098 41441213 := bstep (se 3 (by rfl) ⟨7770227, by rfl⟩ : syracuseStep 41441213 = 15540455) B15540455
theorem B2693531 : Blo 1794098 2693531 := bstep (se 1 (by rfl) ⟨2020148, by rfl⟩ : syracuseStep 2693531 = 4040297) B4040297
theorem B15342047 : Blo 1794098 15342047 := bstep (se 1 (by rfl) ⟨11506535, by rfl⟩ : syracuseStep 15342047 = 23013071) B23013071
theorem B4372975 : Blo 1794098 4372975 := bstep (se 1 (by rfl) ⟨3279731, by rfl⟩ : syracuseStep 4372975 = 6559463) B6559463
theorem B9083501 : Blo 1794098 9083501 := bstep (se 3 (by rfl) ⟨1703156, by rfl⟩ : syracuseStep 9083501 = 3406313) B3406313
theorem B5749373 : Blo 1794098 5749373 := bstep (se 3 (by rfl) ⟨1078007, by rfl⟩ : syracuseStep 5749373 = 2156015) B2156015
theorem B4037327 : Blo 1794098 4037327 := bstep (se 1 (by rfl) ⟨3027995, by rfl⟩ : syracuseStep 4037327 = 6055991) B6055991
theorem B4545305 : Blo 1794098 4545305 := bstep (se 2 (by rfl) ⟨1704489, by rfl⟩ : syracuseStep 4545305 = 3408979) B3408979
theorem B4037417 : Blo 1794098 4037417 := bstep (se 2 (by rfl) ⟨1514031, by rfl⟩ : syracuseStep 4037417 = 3028063) B3028063
theorem B2767927 : Blo 1794098 2767927 := bstep (se 1 (by rfl) ⟨2075945, by rfl⟩ : syracuseStep 2767927 = 4151891) B4151891
theorem B30661739 : Blo 1794098 30661739 := bstep (se 1 (by rfl) ⟨22996304, by rfl⟩ : syracuseStep 30661739 = 45992609) B45992609
theorem B36846809 : Blo 1794098 36846809 := bstep (se 2 (by rfl) ⟨13817553, by rfl⟩ : syracuseStep 36846809 = 27635107) B27635107
theorem B32750963 : Blo 1794098 32750963 := bstep (se 1 (by rfl) ⟨24563222, by rfl⟩ : syracuseStep 32750963 = 49126445) B49126445
theorem B4038191 : Blo 1794098 4038191 := bstep (se 1 (by rfl) ⟨3028643, by rfl⟩ : syracuseStep 4038191 = 6057287) B6057287
theorem B4038479 : Blo 1794098 4038479 := bstep (se 1 (by rfl) ⟨3028859, by rfl⟩ : syracuseStep 4038479 = 6057719) B6057719
theorem B2301787 : Blo 1794098 2301787 := bstep (se 1 (by rfl) ⟨1726340, by rfl⟩ : syracuseStep 2301787 = 3452681) B3452681
theorem B4038569 : Blo 1794098 4038569 := bstep (se 2 (by rfl) ⟨1514463, by rfl⟩ : syracuseStep 4038569 = 3028927) B3028927
theorem B1794527 : Blo 1794098 1794527 := bstep (se 1 (by rfl) ⟨1345895, by rfl⟩ : syracuseStep 1794527 = 2691791) B2691791
theorem B196624867 : Blo 1794098 196624867 := bstep (se 1 (by rfl) ⟨147468650, by rfl⟩ : syracuseStep 196624867 = 294937301) B294937301
theorem B1794543 : Blo 1794098 1794543 := bstep (se 1 (by rfl) ⟨1345907, by rfl⟩ : syracuseStep 1794543 = 2691815) B2691815
theorem B4039451 : Blo 1794098 4039451 := bstep (se 1 (by rfl) ⟨3029588, by rfl⟩ : syracuseStep 4039451 = 6059177) B6059177
theorem B29123383 : Blo 1794098 29123383 := bstep (se 1 (by rfl) ⟨21842537, by rfl⟩ : syracuseStep 29123383 = 43685075) B43685075
theorem B5113343 : Blo 1794098 5113343 := bstep (se 1 (by rfl) ⟨3835007, by rfl⟩ : syracuseStep 5113343 = 7670015) B7670015
theorem B1795687 : Blo 1794098 1795687 := bstep (se 1 (by rfl) ⟨1346765, by rfl⟩ : syracuseStep 1795687 = 2693531) B2693531
theorem B6055667 : Blo 1794098 6055667 := bstep (se 1 (by rfl) ⟨4541750, by rfl⟩ : syracuseStep 6055667 = 9083501) B9083501
theorem B23004917 : Blo 1794098 23004917 := bstep (se 5 (by rfl) ⟨1078355, by rfl⟩ : syracuseStep 23004917 = 2156711) B2156711
theorem B13633271 : Blo 1794098 13633271 := bstep (se 1 (by rfl) ⟨10224953, by rfl⟩ : syracuseStep 13633271 = 20449907) B20449907
theorem B12937097 : Blo 1794098 12937097 := bstep (se 2 (by rfl) ⟨4851411, by rfl⟩ : syracuseStep 12937097 = 9702823) B9702823
theorem B10225547 : Blo 1794098 10225547 := bstep (se 1 (by rfl) ⟨7669160, by rfl⟩ : syracuseStep 10225547 = 15338321) B15338321
theorem B11495465 : Blo 1794098 11495465 := bstep (se 2 (by rfl) ⟨4310799, by rfl⟩ : syracuseStep 11495465 = 8621599) B8621599
theorem B20441159 : Blo 1794098 20441159 := bstep (se 1 (by rfl) ⟨15330869, by rfl⟩ : syracuseStep 20441159 = 30661739) B30661739
theorem B21833975 : Blo 1794098 21833975 := bstep (se 1 (by rfl) ⟨16375481, by rfl⟩ : syracuseStep 21833975 = 32750963) B32750963
theorem B13634243 : Blo 1794098 13634243 := bstep (se 1 (by rfl) ⟨10225682, by rfl⟩ : syracuseStep 13634243 = 20451365) B20451365
theorem B6057071 : Blo 1794098 6057071 := bstep (se 1 (by rfl) ⟨4542803, by rfl⟩ : syracuseStep 6057071 = 9085607) B9085607
theorem B6057449 : Blo 1794098 6057449 := bstep (se 2 (by rfl) ⟨2271543, by rfl⟩ : syracuseStep 6057449 = 4543087) B4543087
theorem B29920825 : Blo 1794098 29920825 := bstep (se 2 (by rfl) ⟨11220309, by rfl⟩ : syracuseStep 29920825 = 22440619) B22440619
theorem B3640943 : Blo 1794098 3640943 := bstep (se 1 (by rfl) ⟨2730707, by rfl⟩ : syracuseStep 3640943 = 5461415) B5461415
theorem B13635215 : Blo 1794098 13635215 := bstep (se 1 (by rfl) ⟨10226411, by rfl⟩ : syracuseStep 13635215 = 20452823) B20452823
theorem B27627475 : Blo 1794098 27627475 := bstep (se 1 (by rfl) ⟨20720606, by rfl⟩ : syracuseStep 27627475 = 41441213) B41441213
theorem B3690569 : Blo 1794098 3690569 := bstep (se 2 (by rfl) ⟨1383963, by rfl⟩ : syracuseStep 3690569 = 2767927) B2767927
theorem B6058259 : Blo 1794098 6058259 := bstep (se 1 (by rfl) ⟨4543694, by rfl⟩ : syracuseStep 6058259 = 9087389) B9087389
theorem B10228031 : Blo 1794098 10228031 := bstep (se 1 (by rfl) ⟨7671023, by rfl⟩ : syracuseStep 10228031 = 15342047) B15342047
theorem B2691449 : Blo 1794098 2691449 := bstep (se 2 (by rfl) ⟨1009293, by rfl⟩ : syracuseStep 2691449 = 2018587) B2018587
theorem B2691497 : Blo 1794098 2691497 := bstep (se 2 (by rfl) ⟨1009311, by rfl⟩ : syracuseStep 2691497 = 2018623) B2018623
theorem B2691551 : Blo 1794098 2691551 := bstep (se 1 (by rfl) ⟨2018663, by rfl⟩ : syracuseStep 2691551 = 4037327) B4037327
theorem B12276197 : Blo 1794098 12276197 := bstep (se 4 (by rfl) ⟨1150893, by rfl⟩ : syracuseStep 12276197 = 2301787) B2301787
theorem B2691611 : Blo 1794098 2691611 := bstep (se 1 (by rfl) ⟨2018708, by rfl⟩ : syracuseStep 2691611 = 4037417) B4037417
theorem B22999585 : Blo 1794098 22999585 := bstep (se 2 (by rfl) ⟨8624844, by rfl⟩ : syracuseStep 22999585 = 17249689) B17249689
theorem B24564539 : Blo 1794098 24564539 := bstep (se 1 (by rfl) ⟨18423404, by rfl⟩ : syracuseStep 24564539 = 36846809) B36846809
theorem B2692073 : Blo 1794098 2692073 := bstep (se 2 (by rfl) ⟨1009527, by rfl⟩ : syracuseStep 2692073 = 2019055) B2019055
theorem B2692127 : Blo 1794098 2692127 := bstep (se 1 (by rfl) ⟨2019095, by rfl⟩ : syracuseStep 2692127 = 4038191) B4038191
theorem B2692319 : Blo 1794098 2692319 := bstep (se 1 (by rfl) ⟨2019239, by rfl⟩ : syracuseStep 2692319 = 4038479) B4038479
theorem B2692379 : Blo 1794098 2692379 := bstep (se 1 (by rfl) ⟨2019284, by rfl⟩ : syracuseStep 2692379 = 4038569) B4038569
theorem B4429279 : Blo 1794098 4429279 := bstep (se 1 (by rfl) ⟨3321959, by rfl⟩ : syracuseStep 4429279 = 6643919) B6643919
theorem B2692799 : Blo 1794098 2692799 := bstep (se 1 (by rfl) ⟨2019599, by rfl⟩ : syracuseStep 2692799 = 4039199) B4039199
theorem B3028745 : Blo 1794098 3028745 := bstep (se 2 (by rfl) ⟨1135779, by rfl⟩ : syracuseStep 3028745 = 2271559) B2271559
theorem B5830633 : Blo 1794098 5830633 := bstep (se 2 (by rfl) ⟨2186487, by rfl⟩ : syracuseStep 5830633 = 4372975) B4372975
theorem B2693351 : Blo 1794098 2693351 := bstep (se 1 (by rfl) ⟨2020013, by rfl⟩ : syracuseStep 2693351 = 4040027) B4040027
theorem B23320871 : Blo 1794098 23320871 := bstep (se 1 (by rfl) ⟨17490653, by rfl⟩ : syracuseStep 23320871 = 34981307) B34981307
theorem B9836891 : Blo 1794098 9836891 := bstep (se 1 (by rfl) ⟨7377668, by rfl⟩ : syracuseStep 9836891 = 14755337) B14755337
theorem B2693687 : Blo 1794098 2693687 := bstep (se 1 (by rfl) ⟨2020265, by rfl⟩ : syracuseStep 2693687 = 4040531) B4040531
theorem B4037543 : Blo 1794098 4037543 := bstep (se 1 (by rfl) ⟨3028157, by rfl⟩ : syracuseStep 4037543 = 6056315) B6056315
theorem B4037615 : Blo 1794098 4037615 := bstep (se 1 (by rfl) ⟨3028211, by rfl⟩ : syracuseStep 4037615 = 6056423) B6056423
theorem B4037705 : Blo 1794098 4037705 := bstep (se 2 (by rfl) ⟨1514139, by rfl⟩ : syracuseStep 4037705 = 3028279) B3028279
theorem B3832915 : Blo 1794098 3832915 := bstep (se 1 (by rfl) ⟨2874686, by rfl⟩ : syracuseStep 3832915 = 5749373) B5749373
theorem B3030203 : Blo 1794098 3030203 := bstep (se 1 (by rfl) ⟨2272652, by rfl⟩ : syracuseStep 3030203 = 4545305) B4545305
theorem B4038839 : Blo 1794098 4038839 := bstep (se 1 (by rfl) ⟨3029129, by rfl⟩ : syracuseStep 4038839 = 6058259) B6058259
theorem B1794299 : Blo 1794098 1794299 := bstep (se 1 (by rfl) ⟨1345724, by rfl⟩ : syracuseStep 1794299 = 2691449) B2691449
theorem B1794331 : Blo 1794098 1794331 := bstep (se 1 (by rfl) ⟨1345748, by rfl⟩ : syracuseStep 1794331 = 2691497) B2691497
theorem B1794367 : Blo 1794098 1794367 := bstep (se 1 (by rfl) ⟨1345775, by rfl⟩ : syracuseStep 1794367 = 2691551) B2691551
theorem B8184131 : Blo 1794098 8184131 := bstep (se 1 (by rfl) ⟨6138098, by rfl⟩ : syracuseStep 8184131 = 12276197) B12276197
theorem B1794407 : Blo 1794098 1794407 := bstep (se 1 (by rfl) ⟨1345805, by rfl⟩ : syracuseStep 1794407 = 2691611) B2691611
theorem B16376359 : Blo 1794098 16376359 := bstep (se 1 (by rfl) ⟨12282269, by rfl⟩ : syracuseStep 16376359 = 24564539) B24564539
theorem B1794715 : Blo 1794098 1794715 := bstep (se 1 (by rfl) ⟨1346036, by rfl⟩ : syracuseStep 1794715 = 2692073) B2692073
theorem B1794751 : Blo 1794098 1794751 := bstep (se 1 (by rfl) ⟨1346063, by rfl⟩ : syracuseStep 1794751 = 2692127) B2692127
theorem B1794879 : Blo 1794098 1794879 := bstep (se 1 (by rfl) ⟨1346159, by rfl⟩ : syracuseStep 1794879 = 2692319) B2692319
theorem B1794919 : Blo 1794098 1794919 := bstep (se 1 (by rfl) ⟨1346189, by rfl⟩ : syracuseStep 1794919 = 2692379) B2692379
theorem B3408895 : Blo 1794098 3408895 := bstep (se 1 (by rfl) ⟨2556671, by rfl⟩ : syracuseStep 3408895 = 5113343) B5113343
theorem B38831177 : Blo 1794098 38831177 := bstep (se 2 (by rfl) ⟨14561691, by rfl⟩ : syracuseStep 38831177 = 29123383) B29123383
theorem B1795199 : Blo 1794098 1795199 := bstep (se 1 (by rfl) ⟨1346399, by rfl⟩ : syracuseStep 1795199 = 2692799) B2692799
theorem B15336611 : Blo 1794098 15336611 := bstep (se 1 (by rfl) ⟨11502458, by rfl⟩ : syracuseStep 15336611 = 23004917) B23004917
theorem B6817031 : Blo 1794098 6817031 := bstep (se 1 (by rfl) ⟨5112773, by rfl⟩ : syracuseStep 6817031 = 10225547) B10225547
theorem B1795567 : Blo 1794098 1795567 := bstep (se 1 (by rfl) ⟨1346675, by rfl⟩ : syracuseStep 1795567 = 2693351) B2693351
theorem B1795791 : Blo 1794098 1795791 := bstep (se 1 (by rfl) ⟨1346843, by rfl⟩ : syracuseStep 1795791 = 2693687) B2693687
theorem B2427295 : Blo 1794098 2427295 := bstep (se 1 (by rfl) ⟨1820471, by rfl⟩ : syracuseStep 2427295 = 3640943) B3640943
theorem B2460379 : Blo 1794098 2460379 := bstep (se 1 (by rfl) ⟨1845284, by rfl⟩ : syracuseStep 2460379 = 3690569) B3690569
theorem B6818687 : Blo 1794098 6818687 := bstep (se 1 (by rfl) ⟨5114015, by rfl⟩ : syracuseStep 6818687 = 10228031) B10228031
theorem B58223933 : Blo 1794098 58223933 := bstep (se 3 (by rfl) ⟨10916987, by rfl⟩ : syracuseStep 58223933 = 21833975) B21833975
theorem B30666113 : Blo 1794098 30666113 := bstep (se 2 (by rfl) ⟨11499792, by rfl⟩ : syracuseStep 30666113 = 22999585) B22999585
theorem B9088847 : Blo 1794098 9088847 := bstep (se 1 (by rfl) ⟨6816635, by rfl⟩ : syracuseStep 9088847 = 13633271) B13633271
theorem B2019163 : Blo 1794098 2019163 := bstep (se 1 (by rfl) ⟨1514372, by rfl⟩ : syracuseStep 2019163 = 3028745) B3028745
theorem B7663643 : Blo 1794098 7663643 := bstep (se 1 (by rfl) ⟨5747732, by rfl⟩ : syracuseStep 7663643 = 11495465) B11495465
theorem B13627439 : Blo 1794098 13627439 := bstep (se 1 (by rfl) ⟨10220579, by rfl⟩ : syracuseStep 13627439 = 20441159) B20441159
theorem B6557927 : Blo 1794098 6557927 := bstep (se 1 (by rfl) ⟨4918445, by rfl⟩ : syracuseStep 6557927 = 9836891) B9836891
theorem B9089495 : Blo 1794098 9089495 := bstep (se 1 (by rfl) ⟨6817121, by rfl⟩ : syracuseStep 9089495 = 13634243) B13634243
theorem B2691695 : Blo 1794098 2691695 := bstep (se 1 (by rfl) ⟨2018771, by rfl⟩ : syracuseStep 2691695 = 4037543) B4037543
theorem B2691743 : Blo 1794098 2691743 := bstep (se 1 (by rfl) ⟨2018807, by rfl⟩ : syracuseStep 2691743 = 4037615) B4037615
theorem B2691803 : Blo 1794098 2691803 := bstep (se 1 (by rfl) ⟨2018852, by rfl⟩ : syracuseStep 2691803 = 4037705) B4037705
theorem B2020135 : Blo 1794098 2020135 := bstep (se 1 (by rfl) ⟨1515101, by rfl⟩ : syracuseStep 2020135 = 3030203) B3030203
theorem B9090143 : Blo 1794098 9090143 := bstep (se 1 (by rfl) ⟨6817607, by rfl⟩ : syracuseStep 9090143 = 13635215) B13635215
theorem B36836633 : Blo 1794098 36836633 := bstep (se 2 (by rfl) ⟨13813737, by rfl⟩ : syracuseStep 36836633 = 27627475) B27627475
theorem B2692967 : Blo 1794098 2692967 := bstep (se 1 (by rfl) ⟨2019725, by rfl⟩ : syracuseStep 2692967 = 4039451) B4039451
theorem B262166489 : Blo 1794098 262166489 := bstep (se 2 (by rfl) ⟨98312433, by rfl⟩ : syracuseStep 262166489 = 196624867) B196624867
theorem B4037111 : Blo 1794098 4037111 := bstep (se 1 (by rfl) ⟨3027833, by rfl⟩ : syracuseStep 4037111 = 6055667) B6055667
theorem B8624731 : Blo 1794098 8624731 := bstep (se 1 (by rfl) ⟨6468548, by rfl⟩ : syracuseStep 8624731 = 12937097) B12937097
theorem B5110553 : Blo 1794098 5110553 := bstep (se 2 (by rfl) ⟨1916457, by rfl⟩ : syracuseStep 5110553 = 3832915) B3832915
theorem B15547247 : Blo 1794098 15547247 := bstep (se 1 (by rfl) ⟨11660435, by rfl⟩ : syracuseStep 15547247 = 23320871) B23320871
theorem B5905705 : Blo 1794098 5905705 := bstep (se 2 (by rfl) ⟨2214639, by rfl⟩ : syracuseStep 5905705 = 4429279) B4429279
theorem B4038047 : Blo 1794098 4038047 := bstep (se 1 (by rfl) ⟨3028535, by rfl⟩ : syracuseStep 4038047 = 6057071) B6057071
theorem B39894433 : Blo 1794098 39894433 := bstep (se 2 (by rfl) ⟨14960412, by rfl⟩ : syracuseStep 39894433 = 29920825) B29920825
theorem B4038299 : Blo 1794098 4038299 := bstep (se 1 (by rfl) ⟨3028724, by rfl⟩ : syracuseStep 4038299 = 6057449) B6057449
theorem B7774177 : Blo 1794098 7774177 := bstep (se 2 (by rfl) ⟨2915316, by rfl⟩ : syracuseStep 7774177 = 5830633) B5830633
theorem B9084959 : Blo 1794098 9084959 := bstep (se 1 (by rfl) ⟨6813719, by rfl⟩ : syracuseStep 9084959 = 13627439) B13627439
theorem B5456087 : Blo 1794098 5456087 := bstep (se 1 (by rfl) ⟨4092065, by rfl⟩ : syracuseStep 5456087 = 8184131) B8184131
theorem B1794463 : Blo 1794098 1794463 := bstep (se 1 (by rfl) ⟨1345847, by rfl⟩ : syracuseStep 1794463 = 2691695) B2691695
theorem B1794495 : Blo 1794098 1794495 := bstep (se 1 (by rfl) ⟨1345871, by rfl⟩ : syracuseStep 1794495 = 2691743) B2691743
theorem B1794535 : Blo 1794098 1794535 := bstep (se 1 (by rfl) ⟨1345901, by rfl⟩ : syracuseStep 1794535 = 2691803) B2691803
theorem B3236393 : Blo 1794098 3236393 := bstep (se 2 (by rfl) ⟨1213647, by rfl⟩ : syracuseStep 3236393 = 2427295) B2427295
theorem B25887451 : Blo 1794098 25887451 := bstep (se 1 (by rfl) ⟨19415588, by rfl⟩ : syracuseStep 25887451 = 38831177) B38831177
theorem B10224407 : Blo 1794098 10224407 := bstep (se 1 (by rfl) ⟨7668305, by rfl⟩ : syracuseStep 10224407 = 15336611) B15336611
theorem B1795311 : Blo 1794098 1795311 := bstep (se 1 (by rfl) ⟨1346483, by rfl⟩ : syracuseStep 1795311 = 2692967) B2692967
theorem B174777659 : Blo 1794098 174777659 := bstep (se 1 (by rfl) ⟨131083244, by rfl⟩ : syracuseStep 174777659 = 262166489) B262166489
theorem B7874273 : Blo 1794098 7874273 := bstep (se 2 (by rfl) ⟨2952852, by rfl⟩ : syracuseStep 7874273 = 5905705) B5905705
theorem B10364831 : Blo 1794098 10364831 := bstep (se 1 (by rfl) ⟨7773623, by rfl⟩ : syracuseStep 10364831 = 15547247) B15547247
theorem B38815955 : Blo 1794098 38815955 := bstep (se 1 (by rfl) ⟨29111966, by rfl⟩ : syracuseStep 38815955 = 58223933) B58223933
theorem B10365569 : Blo 1794098 10365569 := bstep (se 2 (by rfl) ⟨3887088, by rfl⟩ : syracuseStep 10365569 = 7774177) B7774177
theorem B21835145 : Blo 1794098 21835145 := bstep (se 2 (by rfl) ⟨8188179, by rfl⟩ : syracuseStep 21835145 = 16376359) B16376359
theorem B3280505 : Blo 1794098 3280505 := bstep (se 2 (by rfl) ⟨1230189, by rfl⟩ : syracuseStep 3280505 = 2460379) B2460379
theorem B2691407 : Blo 1794098 2691407 := bstep (se 1 (by rfl) ⟨2018555, by rfl⟩ : syracuseStep 2691407 = 4037111) B4037111
theorem B20444075 : Blo 1794098 20444075 := bstep (se 1 (by rfl) ⟨15333056, by rfl⟩ : syracuseStep 20444075 = 30666113) B30666113
theorem B2692031 : Blo 1794098 2692031 := bstep (se 1 (by rfl) ⟨2019023, by rfl⟩ : syracuseStep 2692031 = 4038047) B4038047
theorem B2692199 : Blo 1794098 2692199 := bstep (se 1 (by rfl) ⟨2019149, by rfl⟩ : syracuseStep 2692199 = 4038299) B4038299
theorem B2692217 : Blo 1794098 2692217 := bstep (se 2 (by rfl) ⟨1009581, by rfl⟩ : syracuseStep 2692217 = 2019163) B2019163
theorem B6059231 : Blo 1794098 6059231 := bstep (se 1 (by rfl) ⟨4544423, by rfl⟩ : syracuseStep 6059231 = 9088847) B9088847
theorem B5109095 : Blo 1794098 5109095 := bstep (se 1 (by rfl) ⟨3831821, by rfl⟩ : syracuseStep 5109095 = 7663643) B7663643
theorem B2692559 : Blo 1794098 2692559 := bstep (se 1 (by rfl) ⟨2019419, by rfl⟩ : syracuseStep 2692559 = 4038839) B4038839
theorem B6059663 : Blo 1794098 6059663 := bstep (se 1 (by rfl) ⟨4544747, by rfl⟩ : syracuseStep 6059663 = 9089495) B9089495
theorem B17487805 : Blo 1794098 17487805 := bstep (se 3 (by rfl) ⟨3278963, by rfl⟩ : syracuseStep 17487805 = 6557927) B6557927
theorem B6060095 : Blo 1794098 6060095 := bstep (se 1 (by rfl) ⟨4545071, by rfl⟩ : syracuseStep 6060095 = 9090143) B9090143
theorem B11499641 : Blo 1794098 11499641 := bstep (se 2 (by rfl) ⟨4312365, by rfl⟩ : syracuseStep 11499641 = 8624731) B8624731
theorem B4544687 : Blo 1794098 4544687 := bstep (se 1 (by rfl) ⟨3408515, by rfl⟩ : syracuseStep 4544687 = 6817031) B6817031
theorem B24557755 : Blo 1794098 24557755 := bstep (se 1 (by rfl) ⟨18418316, by rfl⟩ : syracuseStep 24557755 = 36836633) B36836633
theorem B2693513 : Blo 1794098 2693513 := bstep (se 2 (by rfl) ⟨1010067, by rfl⟩ : syracuseStep 2693513 = 2020135) B2020135
theorem B4545193 : Blo 1794098 4545193 := bstep (se 2 (by rfl) ⟨1704447, by rfl⟩ : syracuseStep 4545193 = 3408895) B3408895
theorem B3407035 : Blo 1794098 3407035 := bstep (se 1 (by rfl) ⟨2555276, by rfl⟩ : syracuseStep 3407035 = 5110553) B5110553
theorem B4545791 : Blo 1794098 4545791 := bstep (se 1 (by rfl) ⟨3409343, by rfl⟩ : syracuseStep 4545791 = 6818687) B6818687
theorem B212770309 : Blo 1794098 212770309 := bstep (se 4 (by rfl) ⟨19947216, by rfl⟩ : syracuseStep 212770309 = 39894433) B39894433
theorem B3637391 : Blo 1794098 3637391 := bstep (se 1 (by rfl) ⟨2728043, by rfl⟩ : syracuseStep 3637391 = 5456087) B5456087
theorem B1794271 : Blo 1794098 1794271 := bstep (se 1 (by rfl) ⟨1345703, by rfl⟩ : syracuseStep 1794271 = 2691407) B2691407
theorem B32743673 : Blo 1794098 32743673 := bstep (se 2 (by rfl) ⟨12278877, by rfl⟩ : syracuseStep 32743673 = 24557755) B24557755
theorem B6816271 : Blo 1794098 6816271 := bstep (se 1 (by rfl) ⟨5112203, by rfl⟩ : syracuseStep 6816271 = 10224407) B10224407
theorem B1794687 : Blo 1794098 1794687 := bstep (se 1 (by rfl) ⟨1346015, by rfl⟩ : syracuseStep 1794687 = 2692031) B2692031
theorem B1794799 : Blo 1794098 1794799 := bstep (se 1 (by rfl) ⟨1346099, by rfl⟩ : syracuseStep 1794799 = 2692199) B2692199
theorem B1794811 : Blo 1794098 1794811 := bstep (se 1 (by rfl) ⟨1346108, by rfl⟩ : syracuseStep 1794811 = 2692217) B2692217
theorem B4039487 : Blo 1794098 4039487 := bstep (se 1 (by rfl) ⟨3029615, by rfl⟩ : syracuseStep 4039487 = 6059231) B6059231
theorem B1795039 : Blo 1794098 1795039 := bstep (se 1 (by rfl) ⟨1346279, by rfl⟩ : syracuseStep 1795039 = 2692559) B2692559
theorem B4039775 : Blo 1794098 4039775 := bstep (se 1 (by rfl) ⟨3029831, by rfl⟩ : syracuseStep 4039775 = 6059663) B6059663
theorem B4040063 : Blo 1794098 4040063 := bstep (se 1 (by rfl) ⟨3030047, by rfl⟩ : syracuseStep 4040063 = 6060095) B6060095
theorem B1795675 : Blo 1794098 1795675 := bstep (se 1 (by rfl) ⟨1346756, by rfl⟩ : syracuseStep 1795675 = 2693513) B2693513
theorem B23317073 : Blo 1794098 23317073 := bstep (se 2 (by rfl) ⟨8743902, by rfl⟩ : syracuseStep 23317073 = 17487805) B17487805
theorem B6056639 : Blo 1794098 6056639 := bstep (se 1 (by rfl) ⟨4542479, by rfl⟩ : syracuseStep 6056639 = 9084959) B9084959
theorem B116518439 : Blo 1794098 116518439 := bstep (se 1 (by rfl) ⟨87388829, by rfl⟩ : syracuseStep 116518439 = 174777659) B174777659
theorem B34516601 : Blo 1794098 34516601 := bstep (se 2 (by rfl) ⟨12943725, by rfl⟩ : syracuseStep 34516601 = 25887451) B25887451
theorem B6909887 : Blo 1794098 6909887 := bstep (se 1 (by rfl) ⟨5182415, by rfl⟩ : syracuseStep 6909887 = 10364831) B10364831
theorem B8630381 : Blo 1794098 8630381 := bstep (se 3 (by rfl) ⟨1618196, by rfl⟩ : syracuseStep 8630381 = 3236393) B3236393
theorem B4542713 : Blo 1794098 4542713 := bstep (se 2 (by rfl) ⟨1703517, by rfl⟩ : syracuseStep 4542713 = 3407035) B3407035
theorem B6910379 : Blo 1794098 6910379 := bstep (se 1 (by rfl) ⟨5182784, by rfl⟩ : syracuseStep 6910379 = 10365569) B10365569
theorem B283693745 : Blo 1794098 283693745 := bstep (se 2 (by rfl) ⟨106385154, by rfl⟩ : syracuseStep 283693745 = 212770309) B212770309
theorem B13629383 : Blo 1794098 13629383 := bstep (se 1 (by rfl) ⟨10222037, by rfl⟩ : syracuseStep 13629383 = 20444075) B20444075
theorem B6060257 : Blo 1794098 6060257 := bstep (se 2 (by rfl) ⟨2272596, by rfl⟩ : syracuseStep 6060257 = 4545193) B4545193
theorem B3406063 : Blo 1794098 3406063 := bstep (se 1 (by rfl) ⟨2554547, by rfl⟩ : syracuseStep 3406063 = 5109095) B5109095
theorem B5249515 : Blo 1794098 5249515 := bstep (se 1 (by rfl) ⟨3937136, by rfl⟩ : syracuseStep 5249515 = 7874273) B7874273
theorem B7666427 : Blo 1794098 7666427 := bstep (se 1 (by rfl) ⟨5749820, by rfl⟩ : syracuseStep 7666427 = 11499641) B11499641
theorem B3029791 : Blo 1794098 3029791 := bstep (se 1 (by rfl) ⟨2272343, by rfl⟩ : syracuseStep 3029791 = 4544687) B4544687
theorem B25877303 : Blo 1794098 25877303 := bstep (se 1 (by rfl) ⟨19407977, by rfl⟩ : syracuseStep 25877303 = 38815955) B38815955
theorem B8748013 : Blo 1794098 8748013 := bstep (se 3 (by rfl) ⟨1640252, by rfl⟩ : syracuseStep 8748013 = 3280505) B3280505
theorem B3030527 : Blo 1794098 3030527 := bstep (se 1 (by rfl) ⟨2272895, by rfl⟩ : syracuseStep 3030527 = 4545791) B4545791
theorem B14556763 : Blo 1794098 14556763 := bstep (se 1 (by rfl) ⟨10917572, by rfl⟩ : syracuseStep 14556763 = 21835145) B21835145
theorem B189129163 : Blo 1794098 189129163 := bstep (se 1 (by rfl) ⟨141846872, by rfl⟩ : syracuseStep 189129163 = 283693745) B283693745
theorem B4039721 : Blo 1794098 4039721 := bstep (se 2 (by rfl) ⟨1514895, by rfl⟩ : syracuseStep 4039721 = 3029791) B3029791
theorem B9086255 : Blo 1794098 9086255 := bstep (se 1 (by rfl) ⟨6814691, by rfl⟩ : syracuseStep 9086255 = 13629383) B13629383
theorem B4040171 : Blo 1794098 4040171 := bstep (se 1 (by rfl) ⟨3030128, by rfl⟩ : syracuseStep 4040171 = 6060257) B6060257
theorem B38798837 : Blo 1794098 38798837 := bstep (se 5 (by rfl) ⟨1818695, by rfl⟩ : syracuseStep 38798837 = 3637391) B3637391
theorem B19409017 : Blo 1794098 19409017 := bstep (se 2 (by rfl) ⟨7278381, by rfl⟩ : syracuseStep 19409017 = 14556763) B14556763
theorem B77678959 : Blo 1794098 77678959 := bstep (se 1 (by rfl) ⟨58259219, by rfl⟩ : syracuseStep 77678959 = 116518439) B116518439
theorem B18426365 : Blo 1794098 18426365 := bstep (se 3 (by rfl) ⟨3454943, by rfl⟩ : syracuseStep 18426365 = 6909887) B6909887
theorem B5753587 : Blo 1794098 5753587 := bstep (se 1 (by rfl) ⟨4315190, by rfl⟩ : syracuseStep 5753587 = 8630381) B8630381
theorem B4606919 : Blo 1794098 4606919 := bstep (se 1 (by rfl) ⟨3455189, by rfl⟩ : syracuseStep 4606919 = 6910379) B6910379
theorem B4541417 : Blo 1794098 4541417 := bstep (se 2 (by rfl) ⟨1703031, by rfl⟩ : syracuseStep 4541417 = 3406063) B3406063
theorem B6999353 : Blo 1794098 6999353 := bstep (se 2 (by rfl) ⟨2624757, by rfl⟩ : syracuseStep 6999353 = 5249515) B5249515
theorem B9088361 : Blo 1794098 9088361 := bstep (se 2 (by rfl) ⟨3408135, by rfl⟩ : syracuseStep 9088361 = 6816271) B6816271
theorem B15544715 : Blo 1794098 15544715 := bstep (se 1 (by rfl) ⟨11658536, by rfl⟩ : syracuseStep 15544715 = 23317073) B23317073
theorem B2020351 : Blo 1794098 2020351 := bstep (se 1 (by rfl) ⟨1515263, by rfl⟩ : syracuseStep 2020351 = 3030527) B3030527
theorem B21829115 : Blo 1794098 21829115 := bstep (se 1 (by rfl) ⟨16371836, by rfl⟩ : syracuseStep 21829115 = 32743673) B32743673
theorem B3028475 : Blo 1794098 3028475 := bstep (se 1 (by rfl) ⟨2271356, by rfl⟩ : syracuseStep 3028475 = 4542713) B4542713
theorem B2692991 : Blo 1794098 2692991 := bstep (se 1 (by rfl) ⟨2019743, by rfl⟩ : syracuseStep 2692991 = 4039487) B4039487
theorem B2693183 : Blo 1794098 2693183 := bstep (se 1 (by rfl) ⟨2019887, by rfl⟩ : syracuseStep 2693183 = 4039775) B4039775
theorem B2693375 : Blo 1794098 2693375 := bstep (se 1 (by rfl) ⟨2020031, by rfl⟩ : syracuseStep 2693375 = 4040063) B4040063
theorem B11664017 : Blo 1794098 11664017 := bstep (se 2 (by rfl) ⟨4374006, by rfl⟩ : syracuseStep 11664017 = 8748013) B8748013
theorem B4037759 : Blo 1794098 4037759 := bstep (se 1 (by rfl) ⟨3028319, by rfl⟩ : syracuseStep 4037759 = 6056639) B6056639
theorem B5110951 : Blo 1794098 5110951 := bstep (se 1 (by rfl) ⟨3833213, by rfl⟩ : syracuseStep 5110951 = 7666427) B7666427
theorem B17251535 : Blo 1794098 17251535 := bstep (se 1 (by rfl) ⟨12938651, by rfl⟩ : syracuseStep 17251535 = 25877303) B25877303
theorem B23011067 : Blo 1794098 23011067 := bstep (se 1 (by rfl) ⟨17258300, by rfl⟩ : syracuseStep 23011067 = 34516601) B34516601
theorem B25878689 : Blo 1794098 25878689 := bstep (se 2 (by rfl) ⟨9704508, by rfl⟩ : syracuseStep 25878689 = 19409017) B19409017
theorem B103571945 : Blo 1794098 103571945 := bstep (se 2 (by rfl) ⟨38839479, by rfl⟩ : syracuseStep 103571945 = 77678959) B77678959
theorem B41452573 : Blo 1794098 41452573 := bstep (se 3 (by rfl) ⟨7772357, by rfl⟩ : syracuseStep 41452573 = 15544715) B15544715
theorem B1795327 : Blo 1794098 1795327 := bstep (se 1 (by rfl) ⟨1346495, by rfl⟩ : syracuseStep 1795327 = 2692991) B2692991
theorem B1795455 : Blo 1794098 1795455 := bstep (se 1 (by rfl) ⟨1346591, by rfl⟩ : syracuseStep 1795455 = 2693183) B2693183
theorem B1795583 : Blo 1794098 1795583 := bstep (se 1 (by rfl) ⟨1346687, by rfl⟩ : syracuseStep 1795583 = 2693375) B2693375
theorem B7776011 : Blo 1794098 7776011 := bstep (se 1 (by rfl) ⟨5832008, by rfl⟩ : syracuseStep 7776011 = 11664017) B11664017
theorem B6057503 : Blo 1794098 6057503 := bstep (se 1 (by rfl) ⟨4543127, by rfl⟩ : syracuseStep 6057503 = 9086255) B9086255
theorem B7671449 : Blo 1794098 7671449 := bstep (se 2 (by rfl) ⟨2876793, by rfl⟩ : syracuseStep 7671449 = 5753587) B5753587
theorem B25865891 : Blo 1794098 25865891 := bstep (se 1 (by rfl) ⟨19399418, by rfl⟩ : syracuseStep 25865891 = 38798837) B38798837
theorem B14552743 : Blo 1794098 14552743 := bstep (se 1 (by rfl) ⟨10914557, by rfl⟩ : syracuseStep 14552743 = 21829115) B21829115
theorem B2018983 : Blo 1794098 2018983 := bstep (se 1 (by rfl) ⟨1514237, by rfl⟩ : syracuseStep 2018983 = 3028475) B3028475
theorem B12284243 : Blo 1794098 12284243 := bstep (se 1 (by rfl) ⟨9213182, by rfl⟩ : syracuseStep 12284243 = 18426365) B18426365
theorem B3027611 : Blo 1794098 3027611 := bstep (se 1 (by rfl) ⟨2270708, by rfl⟩ : syracuseStep 3027611 = 4541417) B4541417
theorem B2691839 : Blo 1794098 2691839 := bstep (se 1 (by rfl) ⟨2018879, by rfl⟩ : syracuseStep 2691839 = 4037759) B4037759
theorem B6058907 : Blo 1794098 6058907 := bstep (se 1 (by rfl) ⟨4544180, by rfl⟩ : syracuseStep 6058907 = 9088361) B9088361
theorem B15340711 : Blo 1794098 15340711 := bstep (se 1 (by rfl) ⟨11505533, by rfl⟩ : syracuseStep 15340711 = 23011067) B23011067
theorem B74659765 : Blo 1794098 74659765 := bstep (se 5 (by rfl) ⟨3499676, by rfl⟩ : syracuseStep 74659765 = 6999353) B6999353
theorem B252172217 : Blo 1794098 252172217 := bstep (se 2 (by rfl) ⟨94564581, by rfl⟩ : syracuseStep 252172217 = 189129163) B189129163
theorem B2693147 : Blo 1794098 2693147 := bstep (se 1 (by rfl) ⟨2019860, by rfl⟩ : syracuseStep 2693147 = 4039721) B4039721
theorem B2693447 : Blo 1794098 2693447 := bstep (se 1 (by rfl) ⟨2020085, by rfl⟩ : syracuseStep 2693447 = 4040171) B4040171
theorem B2693801 : Blo 1794098 2693801 := bstep (se 2 (by rfl) ⟨1010175, by rfl⟩ : syracuseStep 2693801 = 2020351) B2020351
theorem B6814601 : Blo 1794098 6814601 := bstep (se 2 (by rfl) ⟨2555475, by rfl⟩ : syracuseStep 6814601 = 5110951) B5110951
theorem B3071279 : Blo 1794098 3071279 := bstep (se 1 (by rfl) ⟨2303459, by rfl⟩ : syracuseStep 3071279 = 4606919) B4606919
theorem B11501023 : Blo 1794098 11501023 := bstep (se 1 (by rfl) ⟨8625767, by rfl⟩ : syracuseStep 11501023 = 17251535) B17251535
theorem B17252459 : Blo 1794098 17252459 := bstep (se 1 (by rfl) ⟨12939344, by rfl⟩ : syracuseStep 17252459 = 25878689) B25878689
theorem B1794559 : Blo 1794098 1794559 := bstep (se 1 (by rfl) ⟨1345919, by rfl⟩ : syracuseStep 1794559 = 2691839) B2691839
theorem B4039271 : Blo 1794098 4039271 := bstep (se 1 (by rfl) ⟨3029453, by rfl⟩ : syracuseStep 4039271 = 6058907) B6058907
theorem B1795431 : Blo 1794098 1795431 := bstep (se 1 (by rfl) ⟨1346573, by rfl⟩ : syracuseStep 1795431 = 2693147) B2693147
theorem B1795631 : Blo 1794098 1795631 := bstep (se 1 (by rfl) ⟨1346723, by rfl⟩ : syracuseStep 1795631 = 2693447) B2693447
theorem B20457197 : Blo 1794098 20457197 := bstep (se 3 (by rfl) ⟨3835724, by rfl⟩ : syracuseStep 20457197 = 7671449) B7671449
theorem B1795867 : Blo 1794098 1795867 := bstep (se 1 (by rfl) ⟨1346900, by rfl⟩ : syracuseStep 1795867 = 2693801) B2693801
theorem B2018407 : Blo 1794098 2018407 := bstep (se 1 (by rfl) ⟨1513805, by rfl⟩ : syracuseStep 2018407 = 3027611) B3027611
theorem B4543067 : Blo 1794098 4543067 := bstep (se 1 (by rfl) ⟨3407300, by rfl⟩ : syracuseStep 4543067 = 6814601) B6814601
theorem B19403657 : Blo 1794098 19403657 := bstep (se 2 (by rfl) ⟨7276371, by rfl⟩ : syracuseStep 19403657 = 14552743) B14552743
theorem B2691977 : Blo 1794098 2691977 := bstep (se 2 (by rfl) ⟨1009491, by rfl⟩ : syracuseStep 2691977 = 2018983) B2018983
theorem B99546353 : Blo 1794098 99546353 := bstep (se 2 (by rfl) ⟨37329882, by rfl⟩ : syracuseStep 99546353 = 74659765) B74659765
theorem B8189495 : Blo 1794098 8189495 := bstep (se 1 (by rfl) ⟨6142121, by rfl⟩ : syracuseStep 8189495 = 12284243) B12284243
theorem B69047963 : Blo 1794098 69047963 := bstep (se 1 (by rfl) ⟨51785972, by rfl⟩ : syracuseStep 69047963 = 103571945) B103571945
theorem B5184007 : Blo 1794098 5184007 := bstep (se 1 (by rfl) ⟨3888005, by rfl⟩ : syracuseStep 5184007 = 7776011) B7776011
theorem B168114811 : Blo 1794098 168114811 := bstep (se 1 (by rfl) ⟨126086108, by rfl⟩ : syracuseStep 168114811 = 252172217) B252172217
theorem B55270097 : Blo 1794098 55270097 := bstep (se 2 (by rfl) ⟨20726286, by rfl⟩ : syracuseStep 55270097 = 41452573) B41452573
theorem B20454281 : Blo 1794098 20454281 := bstep (se 2 (by rfl) ⟨7670355, by rfl⟩ : syracuseStep 20454281 = 15340711) B15340711
theorem B15334697 : Blo 1794098 15334697 := bstep (se 2 (by rfl) ⟨5750511, by rfl⟩ : syracuseStep 15334697 = 11501023) B11501023
theorem B2047519 : Blo 1794098 2047519 := bstep (se 1 (by rfl) ⟨1535639, by rfl⟩ : syracuseStep 2047519 = 3071279) B3071279
theorem B4038335 : Blo 1794098 4038335 := bstep (se 1 (by rfl) ⟨3028751, by rfl⟩ : syracuseStep 4038335 = 6057503) B6057503
theorem B17243927 : Blo 1794098 17243927 := bstep (se 1 (by rfl) ⟨12932945, by rfl⟩ : syracuseStep 17243927 = 25865891) B25865891
theorem B27648037 : Blo 1794098 27648037 := bstep (se 4 (by rfl) ⟨2592003, by rfl⟩ : syracuseStep 27648037 = 5184007) B5184007
theorem B11501639 : Blo 1794098 11501639 := bstep (se 1 (by rfl) ⟨8626229, by rfl⟩ : syracuseStep 11501639 = 17252459) B17252459
theorem B10920101 : Blo 1794098 10920101 := bstep (se 4 (by rfl) ⟨1023759, by rfl⟩ : syracuseStep 10920101 = 2047519) B2047519
theorem B12935771 : Blo 1794098 12935771 := bstep (se 1 (by rfl) ⟨9701828, by rfl⟩ : syracuseStep 12935771 = 19403657) B19403657
theorem B1794651 : Blo 1794098 1794651 := bstep (se 1 (by rfl) ⟨1345988, by rfl⟩ : syracuseStep 1794651 = 2691977) B2691977
theorem B66364235 : Blo 1794098 66364235 := bstep (se 1 (by rfl) ⟨49773176, by rfl⟩ : syracuseStep 66364235 = 99546353) B99546353
theorem B46031975 : Blo 1794098 46031975 := bstep (se 1 (by rfl) ⟨34523981, by rfl⟩ : syracuseStep 46031975 = 69047963) B69047963
theorem B11495951 : Blo 1794098 11495951 := bstep (se 1 (by rfl) ⟨8621963, by rfl⟩ : syracuseStep 11495951 = 17243927) B17243927
theorem B224153081 : Blo 1794098 224153081 := bstep (se 2 (by rfl) ⟨84057405, by rfl⟩ : syracuseStep 224153081 = 168114811) B168114811
theorem B5459663 : Blo 1794098 5459663 := bstep (se 1 (by rfl) ⟨4094747, by rfl⟩ : syracuseStep 5459663 = 8189495) B8189495
theorem B2691209 : Blo 1794098 2691209 := bstep (se 2 (by rfl) ⟨1009203, by rfl⟩ : syracuseStep 2691209 = 2018407) B2018407
theorem B13636187 : Blo 1794098 13636187 := bstep (se 1 (by rfl) ⟨10227140, by rfl⟩ : syracuseStep 13636187 = 20454281) B20454281
theorem B2692223 : Blo 1794098 2692223 := bstep (se 1 (by rfl) ⟨2019167, by rfl⟩ : syracuseStep 2692223 = 4038335) B4038335
theorem B3028711 : Blo 1794098 3028711 := bstep (se 1 (by rfl) ⟨2271533, by rfl⟩ : syracuseStep 3028711 = 4543067) B4543067
theorem B2692847 : Blo 1794098 2692847 := bstep (se 1 (by rfl) ⟨2019635, by rfl⟩ : syracuseStep 2692847 = 4039271) B4039271
theorem B13638131 : Blo 1794098 13638131 := bstep (se 1 (by rfl) ⟨10228598, by rfl⟩ : syracuseStep 13638131 = 20457197) B20457197
theorem B36846731 : Blo 1794098 36846731 := bstep (se 1 (by rfl) ⟨27635048, by rfl⟩ : syracuseStep 36846731 = 55270097) B55270097
theorem B10223131 : Blo 1794098 10223131 := bstep (se 1 (by rfl) ⟨7667348, by rfl⟩ : syracuseStep 10223131 = 15334697) B15334697
theorem B7667759 : Blo 1794098 7667759 := bstep (se 1 (by rfl) ⟨5750819, by rfl⟩ : syracuseStep 7667759 = 11501639) B11501639
theorem B1794139 : Blo 1794098 1794139 := bstep (se 1 (by rfl) ⟨1345604, by rfl⟩ : syracuseStep 1794139 = 2691209) B2691209
theorem B147456197 : Blo 1794098 147456197 := bstep (se 4 (by rfl) ⟨13824018, by rfl⟩ : syracuseStep 147456197 = 27648037) B27648037
theorem B30687983 : Blo 1794098 30687983 := bstep (se 1 (by rfl) ⟨23015987, by rfl⟩ : syracuseStep 30687983 = 46031975) B46031975
theorem B1794815 : Blo 1794098 1794815 := bstep (se 1 (by rfl) ⟨1346111, by rfl⟩ : syracuseStep 1794815 = 2692223) B2692223
theorem B1795231 : Blo 1794098 1795231 := bstep (se 1 (by rfl) ⟨1346423, by rfl⟩ : syracuseStep 1795231 = 2692847) B2692847
theorem B14559101 : Blo 1794098 14559101 := bstep (se 3 (by rfl) ⟨2729831, by rfl⟩ : syracuseStep 14559101 = 5459663) B5459663
theorem B7663967 : Blo 1794098 7663967 := bstep (se 1 (by rfl) ⟨5747975, by rfl⟩ : syracuseStep 7663967 = 11495951) B11495951
theorem B24564487 : Blo 1794098 24564487 := bstep (se 1 (by rfl) ⟨18423365, by rfl⟩ : syracuseStep 24564487 = 36846731) B36846731
theorem B149435387 : Blo 1794098 149435387 := bstep (se 1 (by rfl) ⟨112076540, by rfl⟩ : syracuseStep 149435387 = 224153081) B224153081
theorem B8623847 : Blo 1794098 8623847 := bstep (se 1 (by rfl) ⟨6467885, by rfl⟩ : syracuseStep 8623847 = 12935771) B12935771
theorem B9090791 : Blo 1794098 9090791 := bstep (se 1 (by rfl) ⟨6818093, by rfl⟩ : syracuseStep 9090791 = 13636187) B13636187
theorem B44242823 : Blo 1794098 44242823 := bstep (se 1 (by rfl) ⟨33182117, by rfl⟩ : syracuseStep 44242823 = 66364235) B66364235
theorem B9092087 : Blo 1794098 9092087 := bstep (se 1 (by rfl) ⟨6819065, by rfl⟩ : syracuseStep 9092087 = 13638131) B13638131
theorem B116481077 : Blo 1794098 116481077 := bstep (se 5 (by rfl) ⟨5460050, by rfl⟩ : syracuseStep 116481077 = 10920101) B10920101
theorem B13630841 : Blo 1794098 13630841 := bstep (se 2 (by rfl) ⟨5111565, by rfl⟩ : syracuseStep 13630841 = 10223131) B10223131
theorem B4038281 : Blo 1794098 4038281 := bstep (se 2 (by rfl) ⟨1514355, by rfl⟩ : syracuseStep 4038281 = 3028711) B3028711
theorem B5111839 : Blo 1794098 5111839 := bstep (se 1 (by rfl) ⟨3833879, by rfl⟩ : syracuseStep 5111839 = 7667759) B7667759
theorem B98304131 : Blo 1794098 98304131 := bstep (se 1 (by rfl) ⟨73728098, by rfl⟩ : syracuseStep 98304131 = 147456197) B147456197
theorem B99623591 : Blo 1794098 99623591 := bstep (se 1 (by rfl) ⟨74717693, by rfl⟩ : syracuseStep 99623591 = 149435387) B149435387
theorem B32752649 : Blo 1794098 32752649 := bstep (se 2 (by rfl) ⟨12282243, by rfl⟩ : syracuseStep 32752649 = 24564487) B24564487
theorem B77654051 : Blo 1794098 77654051 := bstep (se 1 (by rfl) ⟨58240538, by rfl⟩ : syracuseStep 77654051 = 116481077) B116481077
theorem B9087227 : Blo 1794098 9087227 := bstep (se 1 (by rfl) ⟨6815420, by rfl⟩ : syracuseStep 9087227 = 13630841) B13630841
theorem B20458655 : Blo 1794098 20458655 := bstep (se 1 (by rfl) ⟨15343991, by rfl⟩ : syracuseStep 20458655 = 30687983) B30687983
theorem B29495215 : Blo 1794098 29495215 := bstep (se 1 (by rfl) ⟨22121411, by rfl⟩ : syracuseStep 29495215 = 44242823) B44242823
theorem B2692187 : Blo 1794098 2692187 := bstep (se 1 (by rfl) ⟨2019140, by rfl⟩ : syracuseStep 2692187 = 4038281) B4038281
theorem B5109311 : Blo 1794098 5109311 := bstep (se 1 (by rfl) ⟨3831983, by rfl⟩ : syracuseStep 5109311 = 7663967) B7663967
theorem B5749231 : Blo 1794098 5749231 := bstep (se 1 (by rfl) ⟨4311923, by rfl⟩ : syracuseStep 5749231 = 8623847) B8623847
theorem B6060527 : Blo 1794098 6060527 := bstep (se 1 (by rfl) ⟨4545395, by rfl⟩ : syracuseStep 6060527 = 9090791) B9090791
theorem B9706067 : Blo 1794098 9706067 := bstep (se 1 (by rfl) ⟨7279550, by rfl⟩ : syracuseStep 9706067 = 14559101) B14559101
theorem B6061391 : Blo 1794098 6061391 := bstep (se 1 (by rfl) ⟨4546043, by rfl⟩ : syracuseStep 6061391 = 9092087) B9092087
theorem B6815785 : Blo 1794098 6815785 := bstep (se 2 (by rfl) ⟨2555919, by rfl⟩ : syracuseStep 6815785 = 5111839) B5111839
theorem B65536087 : Blo 1794098 65536087 := bstep (se 1 (by rfl) ⟨49152065, by rfl⟩ : syracuseStep 65536087 = 98304131) B98304131
theorem B1794791 : Blo 1794098 1794791 := bstep (se 1 (by rfl) ⟨1346093, by rfl⟩ : syracuseStep 1794791 = 2692187) B2692187
theorem B4040351 : Blo 1794098 4040351 := bstep (se 1 (by rfl) ⟨3030263, by rfl⟩ : syracuseStep 4040351 = 6060527) B6060527
theorem B4040927 : Blo 1794098 4040927 := bstep (se 1 (by rfl) ⟨3030695, by rfl⟩ : syracuseStep 4040927 = 6061391) B6061391
theorem B66415727 : Blo 1794098 66415727 := bstep (se 1 (by rfl) ⟨49811795, by rfl⟩ : syracuseStep 66415727 = 99623591) B99623591
theorem B21835099 : Blo 1794098 21835099 := bstep (se 1 (by rfl) ⟨16376324, by rfl⟩ : syracuseStep 21835099 = 32752649) B32752649
theorem B51769367 : Blo 1794098 51769367 := bstep (se 1 (by rfl) ⟨38827025, by rfl⟩ : syracuseStep 51769367 = 77654051) B77654051
theorem B6058151 : Blo 1794098 6058151 := bstep (se 1 (by rfl) ⟨4543613, by rfl⟩ : syracuseStep 6058151 = 9087227) B9087227
theorem B39326953 : Blo 1794098 39326953 := bstep (se 2 (by rfl) ⟨14747607, by rfl⟩ : syracuseStep 39326953 = 29495215) B29495215
theorem B7665641 : Blo 1794098 7665641 := bstep (se 2 (by rfl) ⟨2874615, by rfl⟩ : syracuseStep 7665641 = 5749231) B5749231
theorem B3406207 : Blo 1794098 3406207 := bstep (se 1 (by rfl) ⟨2554655, by rfl⟩ : syracuseStep 3406207 = 5109311) B5109311
theorem B6470711 : Blo 1794098 6470711 := bstep (se 1 (by rfl) ⟨4853033, by rfl⟩ : syracuseStep 6470711 = 9706067) B9706067
theorem B13639103 : Blo 1794098 13639103 := bstep (se 1 (by rfl) ⟨10229327, by rfl⟩ : syracuseStep 13639103 = 20458655) B20458655
theorem B34512911 : Blo 1794098 34512911 := bstep (se 1 (by rfl) ⟨25884683, by rfl⟩ : syracuseStep 34512911 = 51769367) B51769367
theorem B4038767 : Blo 1794098 4038767 := bstep (se 1 (by rfl) ⟨3029075, by rfl⟩ : syracuseStep 4038767 = 6058151) B6058151
theorem B9087713 : Blo 1794098 9087713 := bstep (se 2 (by rfl) ⟨3407892, by rfl⟩ : syracuseStep 9087713 = 6815785) B6815785
theorem B4541609 : Blo 1794098 4541609 := bstep (se 2 (by rfl) ⟨1703103, by rfl⟩ : syracuseStep 4541609 = 3406207) B3406207
theorem B4313807 : Blo 1794098 4313807 := bstep (se 1 (by rfl) ⟨3235355, by rfl⟩ : syracuseStep 4313807 = 6470711) B6470711
theorem B87381449 : Blo 1794098 87381449 := bstep (se 2 (by rfl) ⟨32768043, by rfl⟩ : syracuseStep 87381449 = 65536087) B65536087
theorem B2693567 : Blo 1794098 2693567 := bstep (se 1 (by rfl) ⟨2020175, by rfl⟩ : syracuseStep 2693567 = 4040351) B4040351
theorem B5110427 : Blo 1794098 5110427 := bstep (se 1 (by rfl) ⟨3832820, by rfl⟩ : syracuseStep 5110427 = 7665641) B7665641
theorem B2693951 : Blo 1794098 2693951 := bstep (se 1 (by rfl) ⟨2020463, by rfl⟩ : syracuseStep 2693951 = 4040927) B4040927
theorem B52435937 : Blo 1794098 52435937 := bstep (se 2 (by rfl) ⟨19663476, by rfl⟩ : syracuseStep 52435937 = 39326953) B39326953
theorem B29113465 : Blo 1794098 29113465 := bstep (se 2 (by rfl) ⟨10917549, by rfl⟩ : syracuseStep 29113465 = 21835099) B21835099
theorem B44277151 : Blo 1794098 44277151 := bstep (se 1 (by rfl) ⟨33207863, by rfl⟩ : syracuseStep 44277151 = 66415727) B66415727
theorem B9092735 : Blo 1794098 9092735 := bstep (se 1 (by rfl) ⟨6819551, by rfl⟩ : syracuseStep 9092735 = 13639103) B13639103
theorem B2875871 : Blo 1794098 2875871 := bstep (se 1 (by rfl) ⟨2156903, by rfl⟩ : syracuseStep 2875871 = 4313807) B4313807
theorem B58254299 : Blo 1794098 58254299 := bstep (se 1 (by rfl) ⟨43690724, by rfl⟩ : syracuseStep 58254299 = 87381449) B87381449
theorem B1795711 : Blo 1794098 1795711 := bstep (se 1 (by rfl) ⟨1346783, by rfl⟩ : syracuseStep 1795711 = 2693567) B2693567
theorem B1795967 : Blo 1794098 1795967 := bstep (se 1 (by rfl) ⟨1346975, by rfl⟩ : syracuseStep 1795967 = 2693951) B2693951
theorem B34957291 : Blo 1794098 34957291 := bstep (se 1 (by rfl) ⟨26217968, by rfl⟩ : syracuseStep 34957291 = 52435937) B52435937
theorem B38817953 : Blo 1794098 38817953 := bstep (se 2 (by rfl) ⟨14556732, by rfl⟩ : syracuseStep 38817953 = 29113465) B29113465
theorem B6058475 : Blo 1794098 6058475 := bstep (se 1 (by rfl) ⟨4543856, by rfl⟩ : syracuseStep 6058475 = 9087713) B9087713
theorem B59036201 : Blo 1794098 59036201 := bstep (se 2 (by rfl) ⟨22138575, by rfl⟩ : syracuseStep 59036201 = 44277151) B44277151
theorem B3027739 : Blo 1794098 3027739 := bstep (se 1 (by rfl) ⟨2270804, by rfl⟩ : syracuseStep 3027739 = 4541609) B4541609
theorem B23008607 : Blo 1794098 23008607 := bstep (se 1 (by rfl) ⟨17256455, by rfl⟩ : syracuseStep 23008607 = 34512911) B34512911
theorem B2692511 : Blo 1794098 2692511 := bstep (se 1 (by rfl) ⟨2019383, by rfl⟩ : syracuseStep 2692511 = 4038767) B4038767
theorem B3406951 : Blo 1794098 3406951 := bstep (se 1 (by rfl) ⟨2555213, by rfl⟩ : syracuseStep 3406951 = 5110427) B5110427
theorem B6061823 : Blo 1794098 6061823 := bstep (se 1 (by rfl) ⟨4546367, by rfl⟩ : syracuseStep 6061823 = 9092735) B9092735
theorem B25878635 : Blo 1794098 25878635 := bstep (se 1 (by rfl) ⟨19408976, by rfl⟩ : syracuseStep 25878635 = 38817953) B38817953
theorem B4038983 : Blo 1794098 4038983 := bstep (se 1 (by rfl) ⟨3029237, by rfl⟩ : syracuseStep 4038983 = 6058475) B6058475
theorem B1795007 : Blo 1794098 1795007 := bstep (se 1 (by rfl) ⟨1346255, by rfl⟩ : syracuseStep 1795007 = 2692511) B2692511
theorem B7668989 : Blo 1794098 7668989 := bstep (se 3 (by rfl) ⟨1437935, by rfl⟩ : syracuseStep 7668989 = 2875871) B2875871
theorem B4041215 : Blo 1794098 4041215 := bstep (se 1 (by rfl) ⟨3030911, by rfl⟩ : syracuseStep 4041215 = 6061823) B6061823
theorem B39357467 : Blo 1794098 39357467 := bstep (se 1 (by rfl) ⟨29518100, by rfl⟩ : syracuseStep 39357467 = 59036201) B59036201
theorem B15339071 : Blo 1794098 15339071 := bstep (se 1 (by rfl) ⟨11504303, by rfl⟩ : syracuseStep 15339071 = 23008607) B23008607
theorem B4542601 : Blo 1794098 4542601 := bstep (se 2 (by rfl) ⟨1703475, by rfl⟩ : syracuseStep 4542601 = 3406951) B3406951
theorem B46609721 : Blo 1794098 46609721 := bstep (se 2 (by rfl) ⟨17478645, by rfl⟩ : syracuseStep 46609721 = 34957291) B34957291
theorem B38836199 : Blo 1794098 38836199 := bstep (se 1 (by rfl) ⟨29127149, by rfl⟩ : syracuseStep 38836199 = 58254299) B58254299
theorem B4036985 : Blo 1794098 4036985 := bstep (se 2 (by rfl) ⟨1513869, by rfl⟩ : syracuseStep 4036985 = 3027739) B3027739
theorem B17252423 : Blo 1794098 17252423 := bstep (se 1 (by rfl) ⟨12939317, by rfl⟩ : syracuseStep 17252423 = 25878635) B25878635
theorem B5112659 : Blo 1794098 5112659 := bstep (se 1 (by rfl) ⟨3834494, by rfl⟩ : syracuseStep 5112659 = 7668989) B7668989
theorem B31073147 : Blo 1794098 31073147 := bstep (se 1 (by rfl) ⟨23304860, by rfl⟩ : syracuseStep 31073147 = 46609721) B46609721
theorem B10226047 : Blo 1794098 10226047 := bstep (se 1 (by rfl) ⟨7669535, by rfl⟩ : syracuseStep 10226047 = 15339071) B15339071
theorem B6056801 : Blo 1794098 6056801 := bstep (se 2 (by rfl) ⟨2271300, by rfl⟩ : syracuseStep 6056801 = 4542601) B4542601
theorem B25890799 : Blo 1794098 25890799 := bstep (se 1 (by rfl) ⟨19418099, by rfl⟩ : syracuseStep 25890799 = 38836199) B38836199
theorem B2691323 : Blo 1794098 2691323 := bstep (se 1 (by rfl) ⟨2018492, by rfl⟩ : syracuseStep 2691323 = 4036985) B4036985
theorem B2692655 : Blo 1794098 2692655 := bstep (se 1 (by rfl) ⟨2019491, by rfl⟩ : syracuseStep 2692655 = 4038983) B4038983
theorem B2694143 : Blo 1794098 2694143 := bstep (se 1 (by rfl) ⟨2020607, by rfl⟩ : syracuseStep 2694143 = 4041215) B4041215
theorem B26238311 : Blo 1794098 26238311 := bstep (se 1 (by rfl) ⟨19678733, by rfl⟩ : syracuseStep 26238311 = 39357467) B39357467
theorem B11501615 : Blo 1794098 11501615 := bstep (se 1 (by rfl) ⟨8626211, by rfl⟩ : syracuseStep 11501615 = 17252423) B17252423
theorem B1794215 : Blo 1794098 1794215 := bstep (se 1 (by rfl) ⟨1345661, by rfl⟩ : syracuseStep 1794215 = 2691323) B2691323
theorem B1795103 : Blo 1794098 1795103 := bstep (se 1 (by rfl) ⟨1346327, by rfl⟩ : syracuseStep 1795103 = 2692655) B2692655
theorem B1796095 : Blo 1794098 1796095 := bstep (se 1 (by rfl) ⟨1347071, by rfl⟩ : syracuseStep 1796095 = 2694143) B2694143
theorem B13633757 : Blo 1794098 13633757 := bstep (se 3 (by rfl) ⟨2556329, by rfl⟩ : syracuseStep 13633757 = 5112659) B5112659
theorem B17492207 : Blo 1794098 17492207 := bstep (se 1 (by rfl) ⟨13119155, by rfl⟩ : syracuseStep 17492207 = 26238311) B26238311
theorem B13634729 : Blo 1794098 13634729 := bstep (se 2 (by rfl) ⟨5113023, by rfl⟩ : syracuseStep 13634729 = 10226047) B10226047
theorem B20715431 : Blo 1794098 20715431 := bstep (se 1 (by rfl) ⟨15536573, by rfl⟩ : syracuseStep 20715431 = 31073147) B31073147
theorem B4037867 : Blo 1794098 4037867 := bstep (se 1 (by rfl) ⟨3028400, by rfl⟩ : syracuseStep 4037867 = 6056801) B6056801
theorem B34521065 : Blo 1794098 34521065 := bstep (se 2 (by rfl) ⟨12945399, by rfl⟩ : syracuseStep 34521065 = 25890799) B25890799
theorem B7667743 : Blo 1794098 7667743 := bstep (se 1 (by rfl) ⟨5750807, by rfl⟩ : syracuseStep 7667743 = 11501615) B11501615
theorem B46645885 : Blo 1794098 46645885 := bstep (se 3 (by rfl) ⟨8746103, by rfl⟩ : syracuseStep 46645885 = 17492207) B17492207
theorem B55241149 : Blo 1794098 55241149 := bstep (se 3 (by rfl) ⟨10357715, by rfl⟩ : syracuseStep 55241149 = 20715431) B20715431
theorem B23014043 : Blo 1794098 23014043 := bstep (se 1 (by rfl) ⟨17260532, by rfl⟩ : syracuseStep 23014043 = 34521065) B34521065
theorem B9089171 : Blo 1794098 9089171 := bstep (se 1 (by rfl) ⟨6816878, by rfl⟩ : syracuseStep 9089171 = 13633757) B13633757
theorem B9089819 : Blo 1794098 9089819 := bstep (se 1 (by rfl) ⟨6817364, by rfl⟩ : syracuseStep 9089819 = 13634729) B13634729
theorem B2691911 : Blo 1794098 2691911 := bstep (se 1 (by rfl) ⟨2018933, by rfl⟩ : syracuseStep 2691911 = 4037867) B4037867
theorem B10223657 : Blo 1794098 10223657 := bstep (se 2 (by rfl) ⟨3833871, by rfl⟩ : syracuseStep 10223657 = 7667743) B7667743
theorem B1794607 : Blo 1794098 1794607 := bstep (se 1 (by rfl) ⟨1345955, by rfl⟩ : syracuseStep 1794607 = 2691911) B2691911
theorem B73654865 : Blo 1794098 73654865 := bstep (se 2 (by rfl) ⟨27620574, by rfl⟩ : syracuseStep 73654865 = 55241149) B55241149
theorem B248778053 : Blo 1794098 248778053 := bstep (se 4 (by rfl) ⟨23322942, by rfl⟩ : syracuseStep 248778053 = 46645885) B46645885
theorem B6059447 : Blo 1794098 6059447 := bstep (se 1 (by rfl) ⟨4544585, by rfl⟩ : syracuseStep 6059447 = 9089171) B9089171
theorem B6059879 : Blo 1794098 6059879 := bstep (se 1 (by rfl) ⟨4544909, by rfl⟩ : syracuseStep 6059879 = 9089819) B9089819
theorem B15342695 : Blo 1794098 15342695 := bstep (se 1 (by rfl) ⟨11507021, by rfl⟩ : syracuseStep 15342695 = 23014043) B23014043
theorem B6815771 : Blo 1794098 6815771 := bstep (se 1 (by rfl) ⟨5111828, by rfl⟩ : syracuseStep 6815771 = 10223657) B10223657
theorem B49103243 : Blo 1794098 49103243 := bstep (se 1 (by rfl) ⟨36827432, by rfl⟩ : syracuseStep 49103243 = 73654865) B73654865
theorem B4039631 : Blo 1794098 4039631 := bstep (se 1 (by rfl) ⟨3029723, by rfl⟩ : syracuseStep 4039631 = 6059447) B6059447
theorem B4039919 : Blo 1794098 4039919 := bstep (se 1 (by rfl) ⟨3029939, by rfl⟩ : syracuseStep 4039919 = 6059879) B6059879
theorem B10228463 : Blo 1794098 10228463 := bstep (se 1 (by rfl) ⟨7671347, by rfl⟩ : syracuseStep 10228463 = 15342695) B15342695
theorem B165852035 : Blo 1794098 165852035 := bstep (se 1 (by rfl) ⟨124389026, by rfl⟩ : syracuseStep 165852035 = 248778053) B248778053
theorem B32735495 : Blo 1794098 32735495 := bstep (se 1 (by rfl) ⟨24551621, by rfl⟩ : syracuseStep 32735495 = 49103243) B49103243
theorem B110568023 : Blo 1794098 110568023 := bstep (se 1 (by rfl) ⟨82926017, by rfl⟩ : syracuseStep 110568023 = 165852035) B165852035
theorem B6818975 : Blo 1794098 6818975 := bstep (se 1 (by rfl) ⟨5114231, by rfl⟩ : syracuseStep 6818975 = 10228463) B10228463
theorem B4543847 : Blo 1794098 4543847 := bstep (se 1 (by rfl) ⟨3407885, by rfl⟩ : syracuseStep 4543847 = 6815771) B6815771
theorem B2693087 : Blo 1794098 2693087 := bstep (se 1 (by rfl) ⟨2019815, by rfl⟩ : syracuseStep 2693087 = 4039631) B4039631
theorem B2693279 : Blo 1794098 2693279 := bstep (se 1 (by rfl) ⟨2019959, by rfl⟩ : syracuseStep 2693279 = 4039919) B4039919
theorem B21823663 : Blo 1794098 21823663 := bstep (se 1 (by rfl) ⟨16367747, by rfl⟩ : syracuseStep 21823663 = 32735495) B32735495
theorem B73712015 : Blo 1794098 73712015 := bstep (se 1 (by rfl) ⟨55284011, by rfl⟩ : syracuseStep 73712015 = 110568023) B110568023
theorem B1795391 : Blo 1794098 1795391 := bstep (se 1 (by rfl) ⟨1346543, by rfl⟩ : syracuseStep 1795391 = 2693087) B2693087
theorem B1795519 : Blo 1794098 1795519 := bstep (se 1 (by rfl) ⟨1346639, by rfl⟩ : syracuseStep 1795519 = 2693279) B2693279
theorem B3029231 : Blo 1794098 3029231 := bstep (se 1 (by rfl) ⟨2271923, by rfl⟩ : syracuseStep 3029231 = 4543847) B4543847
theorem B4545983 : Blo 1794098 4545983 := bstep (se 1 (by rfl) ⟨3409487, by rfl⟩ : syracuseStep 4545983 = 6818975) B6818975
theorem B29098217 : Blo 1794098 29098217 := bstep (se 2 (by rfl) ⟨10911831, by rfl⟩ : syracuseStep 29098217 = 21823663) B21823663
theorem B2019487 : Blo 1794098 2019487 := bstep (se 1 (by rfl) ⟨1514615, by rfl⟩ : syracuseStep 2019487 = 3029231) B3029231
theorem B49141343 : Blo 1794098 49141343 := bstep (se 1 (by rfl) ⟨36856007, by rfl⟩ : syracuseStep 49141343 = 73712015) B73712015
theorem B3030655 : Blo 1794098 3030655 := bstep (se 1 (by rfl) ⟨2272991, by rfl⟩ : syracuseStep 3030655 = 4545983) B4545983
theorem B19398811 : Blo 1794098 19398811 := bstep (se 1 (by rfl) ⟨14549108, by rfl⟩ : syracuseStep 19398811 = 29098217) B29098217
theorem B32760895 : Blo 1794098 32760895 := bstep (se 1 (by rfl) ⟨24570671, by rfl⟩ : syracuseStep 32760895 = 49141343) B49141343
theorem B4040873 : Blo 1794098 4040873 := bstep (se 2 (by rfl) ⟨1515327, by rfl⟩ : syracuseStep 4040873 = 3030655) B3030655
theorem B2692649 : Blo 1794098 2692649 := bstep (se 2 (by rfl) ⟨1009743, by rfl⟩ : syracuseStep 2692649 = 2019487) B2019487
theorem B1795099 : Blo 1794098 1795099 := bstep (se 1 (by rfl) ⟨1346324, by rfl⟩ : syracuseStep 1795099 = 2692649) B2692649
theorem B43681193 : Blo 1794098 43681193 := bstep (se 2 (by rfl) ⟨16380447, by rfl⟩ : syracuseStep 43681193 = 32760895) B32760895
theorem B25865081 : Blo 1794098 25865081 := bstep (se 2 (by rfl) ⟨9699405, by rfl⟩ : syracuseStep 25865081 = 19398811) B19398811
theorem B2693915 : Blo 1794098 2693915 := bstep (se 1 (by rfl) ⟨2020436, by rfl⟩ : syracuseStep 2693915 = 4040873) B4040873
theorem B1795943 : Blo 1794098 1795943 := bstep (se 1 (by rfl) ⟨1346957, by rfl⟩ : syracuseStep 1795943 = 2693915) B2693915
theorem B29120795 : Blo 1794098 29120795 := bstep (se 1 (by rfl) ⟨21840596, by rfl⟩ : syracuseStep 29120795 = 43681193) B43681193
theorem B17243387 : Blo 1794098 17243387 := bstep (se 1 (by rfl) ⟨12932540, by rfl⟩ : syracuseStep 17243387 = 25865081) B25865081
theorem B11495591 : Blo 1794098 11495591 := bstep (se 1 (by rfl) ⟨8621693, by rfl⟩ : syracuseStep 11495591 = 17243387) B17243387
theorem B19413863 : Blo 1794098 19413863 := bstep (se 1 (by rfl) ⟨14560397, by rfl⟩ : syracuseStep 19413863 = 29120795) B29120795
theorem B7663727 : Blo 1794098 7663727 := bstep (se 1 (by rfl) ⟨5747795, by rfl⟩ : syracuseStep 7663727 = 11495591) B11495591
theorem B12942575 : Blo 1794098 12942575 := bstep (se 1 (by rfl) ⟨9706931, by rfl⟩ : syracuseStep 12942575 = 19413863) B19413863
theorem B8628383 : Blo 1794098 8628383 := bstep (se 1 (by rfl) ⟨6471287, by rfl⟩ : syracuseStep 8628383 = 12942575) B12942575
theorem B5109151 : Blo 1794098 5109151 := bstep (se 1 (by rfl) ⟨3831863, by rfl⟩ : syracuseStep 5109151 = 7663727) B7663727
theorem B5752255 : Blo 1794098 5752255 := bstep (se 1 (by rfl) ⟨4314191, by rfl⟩ : syracuseStep 5752255 = 8628383) B8628383
theorem B6812201 : Blo 1794098 6812201 := bstep (se 2 (by rfl) ⟨2554575, by rfl⟩ : syracuseStep 6812201 = 5109151) B5109151
theorem B7669673 : Blo 1794098 7669673 := bstep (se 2 (by rfl) ⟨2876127, by rfl⟩ : syracuseStep 7669673 = 5752255) B5752255
theorem B4541467 : Blo 1794098 4541467 := bstep (se 1 (by rfl) ⟨3406100, by rfl⟩ : syracuseStep 4541467 = 6812201) B6812201
theorem B5113115 : Blo 1794098 5113115 := bstep (se 1 (by rfl) ⟨3834836, by rfl⟩ : syracuseStep 5113115 = 7669673) B7669673
theorem B6055289 : Blo 1794098 6055289 := bstep (se 2 (by rfl) ⟨2270733, by rfl⟩ : syracuseStep 6055289 = 4541467) B4541467
theorem B3408743 : Blo 1794098 3408743 := bstep (se 1 (by rfl) ⟨2556557, by rfl⟩ : syracuseStep 3408743 = 5113115) B5113115
theorem B4036859 : Blo 1794098 4036859 := bstep (se 1 (by rfl) ⟨3027644, by rfl⟩ : syracuseStep 4036859 = 6055289) B6055289
theorem B2691239 : Blo 1794098 2691239 := bstep (se 1 (by rfl) ⟨2018429, by rfl⟩ : syracuseStep 2691239 = 4036859) B4036859
theorem B9089981 : Blo 1794098 9089981 := bstep (se 3 (by rfl) ⟨1704371, by rfl⟩ : syracuseStep 9089981 = 3408743) B3408743
theorem B1794159 : Blo 1794098 1794159 := bstep (se 1 (by rfl) ⟨1345619, by rfl⟩ : syracuseStep 1794159 = 2691239) B2691239
theorem B6059987 : Blo 1794098 6059987 := bstep (se 1 (by rfl) ⟨4544990, by rfl⟩ : syracuseStep 6059987 = 9089981) B9089981
theorem B4039991 : Blo 1794098 4039991 := bstep (se 1 (by rfl) ⟨3029993, by rfl⟩ : syracuseStep 4039991 = 6059987) B6059987
theorem B2693327 : Blo 1794098 2693327 := bstep (se 1 (by rfl) ⟨2019995, by rfl⟩ : syracuseStep 2693327 = 4039991) B4039991
theorem B1795551 : Blo 1794098 1795551 := bstep (se 1 (by rfl) ⟨1346663, by rfl⟩ : syracuseStep 1795551 = 2693327) B2693327

theorem C0 (j : ℕ) (h1 : 448524 ≤ j) (h2 : j ≤ 449023) : Blo 1794098 (4 * j + 3) := by
  interval_cases j
  · exact B1794099
  · exact B1794103
  · exact B1794107
  · exact B1794111
  · exact B1794115
  · exact B1794119
  · exact B1794123
  · exact B1794127
  · exact B1794131
  · exact B1794135
  · exact B1794139
  · exact B1794143
  · exact B1794147
  · exact B1794151
  · exact B1794155
  · exact B1794159
  · exact B1794163
  · exact B1794167
  · exact B1794171
  · exact B1794175
  · exact B1794179
  · exact B1794183
  · exact B1794187
  · exact B1794191
  · exact B1794195
  · exact B1794199
  · exact B1794203
  · exact B1794207
  · exact B1794211
  · exact B1794215
  · exact B1794219
  · exact B1794223
  · exact B1794227
  · exact B1794231
  · exact B1794235
  · exact B1794239
  · exact B1794243
  · exact B1794247
  · exact B1794251
  · exact B1794255
  · exact B1794259
  · exact B1794263
  · exact B1794267
  · exact B1794271
  · exact B1794275
  · exact B1794279
  · exact B1794283
  · exact B1794287
  · exact B1794291
  · exact B1794295
  · exact B1794299
  · exact B1794303
  · exact B1794307
  · exact B1794311
  · exact B1794315
  · exact B1794319
  · exact B1794323
  · exact B1794327
  · exact B1794331
  · exact B1794335
  · exact B1794339
  · exact B1794343
  · exact B1794347
  · exact B1794351
  · exact B1794355
  · exact B1794359
  · exact B1794363
  · exact B1794367
  · exact B1794371
  · exact B1794375
  · exact B1794379
  · exact B1794383
  · exact B1794387
  · exact B1794391
  · exact B1794395
  · exact B1794399
  · exact B1794403
  · exact B1794407
  · exact B1794411
  · exact B1794415
  · exact B1794419
  · exact B1794423
  · exact B1794427
  · exact B1794431
  · exact B1794435
  · exact B1794439
  · exact B1794443
  · exact B1794447
  · exact B1794451
  · exact B1794455
  · exact B1794459
  · exact B1794463
  · exact B1794467
  · exact B1794471
  · exact B1794475
  · exact B1794479
  · exact B1794483
  · exact B1794487
  · exact B1794491
  · exact B1794495
  · exact B1794499
  · exact B1794503
  · exact B1794507
  · exact B1794511
  · exact B1794515
  · exact B1794519
  · exact B1794523
  · exact B1794527
  · exact B1794531
  · exact B1794535
  · exact B1794539
  · exact B1794543
  · exact B1794547
  · exact B1794551
  · exact B1794555
  · exact B1794559
  · exact B1794563
  · exact B1794567
  · exact B1794571
  · exact B1794575
  · exact B1794579
  · exact B1794583
  · exact B1794587
  · exact B1794591
  · exact B1794595
  · exact B1794599
  · exact B1794603
  · exact B1794607
  · exact B1794611
  · exact B1794615
  · exact B1794619
  · exact B1794623
  · exact B1794627
  · exact B1794631
  · exact B1794635
  · exact B1794639
  · exact B1794643
  · exact B1794647
  · exact B1794651
  · exact B1794655
  · exact B1794659
  · exact B1794663
  · exact B1794667
  · exact B1794671
  · exact B1794675
  · exact B1794679
  · exact B1794683
  · exact B1794687
  · exact B1794691
  · exact B1794695
  · exact B1794699
  · exact B1794703
  · exact B1794707
  · exact B1794711
  · exact B1794715
  · exact B1794719
  · exact B1794723
  · exact B1794727
  · exact B1794731
  · exact B1794735
  · exact B1794739
  · exact B1794743
  · exact B1794747
  · exact B1794751
  · exact B1794755
  · exact B1794759
  · exact B1794763
  · exact B1794767
  · exact B1794771
  · exact B1794775
  · exact B1794779
  · exact B1794783
  · exact B1794787
  · exact B1794791
  · exact B1794795
  · exact B1794799
  · exact B1794803
  · exact B1794807
  · exact B1794811
  · exact B1794815
  · exact B1794819
  · exact B1794823
  · exact B1794827
  · exact B1794831
  · exact B1794835
  · exact B1794839
  · exact B1794843
  · exact B1794847
  · exact B1794851
  · exact B1794855
  · exact B1794859
  · exact B1794863
  · exact B1794867
  · exact B1794871
  · exact B1794875
  · exact B1794879
  · exact B1794883
  · exact B1794887
  · exact B1794891
  · exact B1794895
  · exact B1794899
  · exact B1794903
  · exact B1794907
  · exact B1794911
  · exact B1794915
  · exact B1794919
  · exact B1794923
  · exact B1794927
  · exact B1794931
  · exact B1794935
  · exact B1794939
  · exact B1794943
  · exact B1794947
  · exact B1794951
  · exact B1794955
  · exact B1794959
  · exact B1794963
  · exact B1794967
  · exact B1794971
  · exact B1794975
  · exact B1794979
  · exact B1794983
  · exact B1794987
  · exact B1794991
  · exact B1794995
  · exact B1794999
  · exact B1795003
  · exact B1795007
  · exact B1795011
  · exact B1795015
  · exact B1795019
  · exact B1795023
  · exact B1795027
  · exact B1795031
  · exact B1795035
  · exact B1795039
  · exact B1795043
  · exact B1795047
  · exact B1795051
  · exact B1795055
  · exact B1795059
  · exact B1795063
  · exact B1795067
  · exact B1795071
  · exact B1795075
  · exact B1795079
  · exact B1795083
  · exact B1795087
  · exact B1795091
  · exact B1795095
  · exact B1795099
  · exact B1795103
  · exact B1795107
  · exact B1795111
  · exact B1795115
  · exact B1795119
  · exact B1795123
  · exact B1795127
  · exact B1795131
  · exact B1795135
  · exact B1795139
  · exact B1795143
  · exact B1795147
  · exact B1795151
  · exact B1795155
  · exact B1795159
  · exact B1795163
  · exact B1795167
  · exact B1795171
  · exact B1795175
  · exact B1795179
  · exact B1795183
  · exact B1795187
  · exact B1795191
  · exact B1795195
  · exact B1795199
  · exact B1795203
  · exact B1795207
  · exact B1795211
  · exact B1795215
  · exact B1795219
  · exact B1795223
  · exact B1795227
  · exact B1795231
  · exact B1795235
  · exact B1795239
  · exact B1795243
  · exact B1795247
  · exact B1795251
  · exact B1795255
  · exact B1795259
  · exact B1795263
  · exact B1795267
  · exact B1795271
  · exact B1795275
  · exact B1795279
  · exact B1795283
  · exact B1795287
  · exact B1795291
  · exact B1795295
  · exact B1795299
  · exact B1795303
  · exact B1795307
  · exact B1795311
  · exact B1795315
  · exact B1795319
  · exact B1795323
  · exact B1795327
  · exact B1795331
  · exact B1795335
  · exact B1795339
  · exact B1795343
  · exact B1795347
  · exact B1795351
  · exact B1795355
  · exact B1795359
  · exact B1795363
  · exact B1795367
  · exact B1795371
  · exact B1795375
  · exact B1795379
  · exact B1795383
  · exact B1795387
  · exact B1795391
  · exact B1795395
  · exact B1795399
  · exact B1795403
  · exact B1795407
  · exact B1795411
  · exact B1795415
  · exact B1795419
  · exact B1795423
  · exact B1795427
  · exact B1795431
  · exact B1795435
  · exact B1795439
  · exact B1795443
  · exact B1795447
  · exact B1795451
  · exact B1795455
  · exact B1795459
  · exact B1795463
  · exact B1795467
  · exact B1795471
  · exact B1795475
  · exact B1795479
  · exact B1795483
  · exact B1795487
  · exact B1795491
  · exact B1795495
  · exact B1795499
  · exact B1795503
  · exact B1795507
  · exact B1795511
  · exact B1795515
  · exact B1795519
  · exact B1795523
  · exact B1795527
  · exact B1795531
  · exact B1795535
  · exact B1795539
  · exact B1795543
  · exact B1795547
  · exact B1795551
  · exact B1795555
  · exact B1795559
  · exact B1795563
  · exact B1795567
  · exact B1795571
  · exact B1795575
  · exact B1795579
  · exact B1795583
  · exact B1795587
  · exact B1795591
  · exact B1795595
  · exact B1795599
  · exact B1795603
  · exact B1795607
  · exact B1795611
  · exact B1795615
  · exact B1795619
  · exact B1795623
  · exact B1795627
  · exact B1795631
  · exact B1795635
  · exact B1795639
  · exact B1795643
  · exact B1795647
  · exact B1795651
  · exact B1795655
  · exact B1795659
  · exact B1795663
  · exact B1795667
  · exact B1795671
  · exact B1795675
  · exact B1795679
  · exact B1795683
  · exact B1795687
  · exact B1795691
  · exact B1795695
  · exact B1795699
  · exact B1795703
  · exact B1795707
  · exact B1795711
  · exact B1795715
  · exact B1795719
  · exact B1795723
  · exact B1795727
  · exact B1795731
  · exact B1795735
  · exact B1795739
  · exact B1795743
  · exact B1795747
  · exact B1795751
  · exact B1795755
  · exact B1795759
  · exact B1795763
  · exact B1795767
  · exact B1795771
  · exact B1795775
  · exact B1795779
  · exact B1795783
  · exact B1795787
  · exact B1795791
  · exact B1795795
  · exact B1795799
  · exact B1795803
  · exact B1795807
  · exact B1795811
  · exact B1795815
  · exact B1795819
  · exact B1795823
  · exact B1795827
  · exact B1795831
  · exact B1795835
  · exact B1795839
  · exact B1795843
  · exact B1795847
  · exact B1795851
  · exact B1795855
  · exact B1795859
  · exact B1795863
  · exact B1795867
  · exact B1795871
  · exact B1795875
  · exact B1795879
  · exact B1795883
  · exact B1795887
  · exact B1795891
  · exact B1795895
  · exact B1795899
  · exact B1795903
  · exact B1795907
  · exact B1795911
  · exact B1795915
  · exact B1795919
  · exact B1795923
  · exact B1795927
  · exact B1795931
  · exact B1795935
  · exact B1795939
  · exact B1795943
  · exact B1795947
  · exact B1795951
  · exact B1795955
  · exact B1795959
  · exact B1795963
  · exact B1795967
  · exact B1795971
  · exact B1795975
  · exact B1795979
  · exact B1795983
  · exact B1795987
  · exact B1795991
  · exact B1795995
  · exact B1795999
  · exact B1796003
  · exact B1796007
  · exact B1796011
  · exact B1796015
  · exact B1796019
  · exact B1796023
  · exact B1796027
  · exact B1796031
  · exact B1796035
  · exact B1796039
  · exact B1796043
  · exact B1796047
  · exact B1796051
  · exact B1796055
  · exact B1796059
  · exact B1796063
  · exact B1796067
  · exact B1796071
  · exact B1796075
  · exact B1796079
  · exact B1796083
  · exact B1796087
  · exact B1796091
  · exact B1796095

theorem solution (m : ℕ) (hlo : 1794098 ≤ m) (hhi : m ≤ 1796098) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 448524 ≤ j := by omega
    have hj2 : j ≤ 449023 := by omega
    have hb : Blo 1794098 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
