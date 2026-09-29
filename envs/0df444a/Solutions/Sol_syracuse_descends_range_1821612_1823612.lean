-- Prove2me | solution 1 for syracuse_descends_range_1821612_1823612
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:56:49.967614+00:00
-- url     : https://prove2.me/submissions/87c261fd-a8b9-4d0e-9f2d-fff52ebf6bcf

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


theorem B7110773 : Blo 1821612 7110773 := bbase (se 5 (by rfl) ⟨333317, by rfl⟩ : syracuseStep 7110773 = 666635) (by norm_num)
theorem B4612261 : Blo 1821612 4612261 := bbase (se 4 (by rfl) ⟨432399, by rfl⟩ : syracuseStep 4612261 = 864799) (by norm_num)
theorem B4497653 : Blo 1821612 4497653 := bbase (se 5 (by rfl) ⟨210827, by rfl⟩ : syracuseStep 4497653 = 421655) (by norm_num)
theorem B4612373 : Blo 1821612 4612373 := bbase (se 6 (by rfl) ⟨108102, by rfl⟩ : syracuseStep 4612373 = 216205) (by norm_num)
theorem B3891493 : Blo 1821612 3891493 := bbase (se 4 (by rfl) ⟨364827, by rfl⟩ : syracuseStep 3891493 = 729655) (by norm_num)
theorem B6152597 : Blo 1821612 6152597 := bbase (se 6 (by rfl) ⟨144201, by rfl⟩ : syracuseStep 6152597 = 288403) (by norm_num)
theorem B4612565 : Blo 1821612 4612565 := bbase (se 7 (by rfl) ⟨54053, by rfl⟩ : syracuseStep 4612565 = 108107) (by norm_num)
theorem B3080717 : Blo 1821612 3080717 := bbase (se 3 (by rfl) ⟨577634, by rfl⟩ : syracuseStep 3080717 = 1155269) (by norm_num)
theorem B9355925 : Blo 1821612 9355925 := bbase (se 6 (by rfl) ⟨219279, by rfl⟩ : syracuseStep 9355925 = 438559) (by norm_num)
theorem B4924133 : Blo 1821612 4924133 := bbase (se 4 (by rfl) ⟨461637, by rfl⟩ : syracuseStep 4924133 = 923275) (by norm_num)
theorem B7111397 : Blo 1821612 7111397 := bbase (se 4 (by rfl) ⟨666693, by rfl⟩ : syracuseStep 7111397 = 1333387) (by norm_num)
theorem B3891989 : Blo 1821612 3891989 := bbase (se 6 (by rfl) ⟨91218, by rfl⟩ : syracuseStep 3891989 = 182437) (by norm_num)
theorem B4612909 : Blo 1821612 4612909 := bbase (se 3 (by rfl) ⟨864920, by rfl⟩ : syracuseStep 4612909 = 1729841) (by norm_num)
theorem B6153029 : Blo 1821612 6153029 := bbase (se 4 (by rfl) ⟨576846, by rfl⟩ : syracuseStep 6153029 = 1153693) (by norm_num)
theorem B4613021 : Blo 1821612 4613021 := bbase (se 3 (by rfl) ⟨864941, by rfl⟩ : syracuseStep 4613021 = 1729883) (by norm_num)
theorem B7783397 : Blo 1821612 7783397 := bbase (se 4 (by rfl) ⟨729693, by rfl⟩ : syracuseStep 7783397 = 1459387) (by norm_num)
theorem B14779381 : Blo 1821612 14779381 := bbase (se 5 (by rfl) ⟨692783, by rfl⟩ : syracuseStep 14779381 = 1385567) (by norm_num)
theorem B15778901 : Blo 1821612 15778901 := bbase (se 8 (by rfl) ⟨92454, by rfl⟩ : syracuseStep 15778901 = 184909) (by norm_num)
theorem B4613213 : Blo 1821612 4613213 := bbase (se 3 (by rfl) ⟨864977, by rfl⟩ : syracuseStep 4613213 = 1729955) (by norm_num)
theorem B13845653 : Blo 1821612 13845653 := bbase (se 6 (by rfl) ⟨324507, by rfl⟩ : syracuseStep 13845653 = 649015) (by norm_num)
theorem B9225413 : Blo 1821612 9225413 := bbase (se 4 (by rfl) ⟨864882, by rfl⟩ : syracuseStep 9225413 = 1729765) (by norm_num)
theorem B3458285 : Blo 1821612 3458285 := bbase (se 3 (by rfl) ⟨648428, by rfl⟩ : syracuseStep 3458285 = 1296857) (by norm_num)
theorem B6153461 : Blo 1821612 6153461 := bbase (se 5 (by rfl) ⟨288443, by rfl⟩ : syracuseStep 6153461 = 576887) (by norm_num)
theorem B17524021 : Blo 1821612 17524021 := bbase (se 5 (by rfl) ⟨821438, by rfl⟩ : syracuseStep 17524021 = 1642877) (by norm_num)
theorem B2049349 : Blo 1821612 2049349 := bbase (se 4 (by rfl) ⟨192126, by rfl⟩ : syracuseStep 2049349 = 384253) (by norm_num)
theorem B2049385 : Blo 1821612 2049385 := bbase (se 2 (by rfl) ⟨768519, by rfl⟩ : syracuseStep 2049385 = 1537039) (by norm_num)
theorem B6571381 : Blo 1821612 6571381 := bbase (se 5 (by rfl) ⟨308033, by rfl⟩ : syracuseStep 6571381 = 616067) (by norm_num)
theorem B2049421 : Blo 1821612 2049421 := bbase (se 3 (by rfl) ⟨384266, by rfl⟩ : syracuseStep 2049421 = 768533) (by norm_num)
theorem B2049457 : Blo 1821612 2049457 := bbase (se 2 (by rfl) ⟨768546, by rfl⟩ : syracuseStep 2049457 = 1537093) (by norm_num)
theorem B4613557 : Blo 1821612 4613557 := bbase (se 5 (by rfl) ⟨216260, by rfl⟩ : syracuseStep 4613557 = 432521) (by norm_num)
theorem B2770373 : Blo 1821612 2770373 := bbase (se 4 (by rfl) ⟨259722, by rfl⟩ : syracuseStep 2770373 = 519445) (by norm_num)
theorem B2049493 : Blo 1821612 2049493 := bbase (se 7 (by rfl) ⟨24017, by rfl⟩ : syracuseStep 2049493 = 48035) (by norm_num)
theorem B4007405 : Blo 1821612 4007405 := bbase (se 3 (by rfl) ⟨751388, by rfl⟩ : syracuseStep 4007405 = 1502777) (by norm_num)
theorem B15574517 : Blo 1821612 15574517 := bbase (se 5 (by rfl) ⟨730055, by rfl⟩ : syracuseStep 15574517 = 1460111) (by norm_num)
theorem B2049529 : Blo 1821612 2049529 := bbase (se 2 (by rfl) ⟨768573, by rfl⟩ : syracuseStep 2049529 = 1537147) (by norm_num)
theorem B11683349 : Blo 1821612 11683349 := bbase (se 6 (by rfl) ⟨273828, by rfl⟩ : syracuseStep 11683349 = 547657) (by norm_num)
theorem B3327517 : Blo 1821612 3327517 := bbase (se 3 (by rfl) ⟨623909, by rfl⟩ : syracuseStep 3327517 = 1247819) (by norm_num)
theorem B2049565 : Blo 1821612 2049565 := bbase (se 3 (by rfl) ⟨384293, by rfl⟩ : syracuseStep 2049565 = 768587) (by norm_num)
theorem B4613669 : Blo 1821612 4613669 := bbase (se 4 (by rfl) ⟨432531, by rfl⟩ : syracuseStep 4613669 = 865063) (by norm_num)
theorem B13837877 : Blo 1821612 13837877 := bbase (se 5 (by rfl) ⟨648650, by rfl⟩ : syracuseStep 13837877 = 1297301) (by norm_num)
theorem B2049601 : Blo 1821612 2049601 := bbase (se 2 (by rfl) ⟨768600, by rfl⟩ : syracuseStep 2049601 = 1537201) (by norm_num)
theorem B2049637 : Blo 1821612 2049637 := bbase (se 4 (by rfl) ⟨192153, by rfl⟩ : syracuseStep 2049637 = 384307) (by norm_num)
theorem B3892853 : Blo 1821612 3892853 := bbase (se 5 (by rfl) ⟨182477, by rfl⟩ : syracuseStep 3892853 = 364955) (by norm_num)
theorem B2049673 : Blo 1821612 2049673 := bbase (se 2 (by rfl) ⟨768627, by rfl⟩ : syracuseStep 2049673 = 1537255) (by norm_num)
theorem B6153893 : Blo 1821612 6153893 := bbase (se 4 (by rfl) ⟨576927, by rfl⟩ : syracuseStep 6153893 = 1153855) (by norm_num)
theorem B2049709 : Blo 1821612 2049709 := bbase (se 3 (by rfl) ⟨384320, by rfl⟩ : syracuseStep 2049709 = 768641) (by norm_num)
theorem B2049745 : Blo 1821612 2049745 := bbase (se 2 (by rfl) ⟨768654, by rfl⟩ : syracuseStep 2049745 = 1537309) (by norm_num)
theorem B4613861 : Blo 1821612 4613861 := bbase (se 4 (by rfl) ⟨432549, by rfl⟩ : syracuseStep 4613861 = 865099) (by norm_num)
theorem B9357029 : Blo 1821612 9357029 := bbase (se 4 (by rfl) ⟨877221, by rfl⟩ : syracuseStep 9357029 = 1754443) (by norm_num)
theorem B2049781 : Blo 1821612 2049781 := bbase (se 5 (by rfl) ⟨96083, by rfl⟩ : syracuseStep 2049781 = 192167) (by norm_num)
theorem B3892997 : Blo 1821612 3892997 := bbase (se 4 (by rfl) ⟨364968, by rfl⟩ : syracuseStep 3892997 = 729937) (by norm_num)
theorem B2049817 : Blo 1821612 2049817 := bbase (se 2 (by rfl) ⟨768681, by rfl⟩ : syracuseStep 2049817 = 1537363) (by norm_num)
theorem B2049853 : Blo 1821612 2049853 := bbase (se 3 (by rfl) ⟨384347, by rfl⟩ : syracuseStep 2049853 = 768695) (by norm_num)
theorem B2107225 : Blo 1821612 2107225 := bbase (se 2 (by rfl) ⟨790209, by rfl⟩ : syracuseStep 2107225 = 1580419) (by norm_num)
theorem B2049889 : Blo 1821612 2049889 := bbase (se 2 (by rfl) ⟨768708, by rfl⟩ : syracuseStep 2049889 = 1537417) (by norm_num)
theorem B2189153 : Blo 1821612 2189153 := bbase (se 2 (by rfl) ⟨820932, by rfl⟩ : syracuseStep 2189153 = 1641865) (by norm_num)
theorem B9348965 : Blo 1821612 9348965 := bbase (se 4 (by rfl) ⟨876465, by rfl⟩ : syracuseStep 9348965 = 1752931) (by norm_num)
theorem B2049925 : Blo 1821612 2049925 := bbase (se 4 (by rfl) ⟨192180, by rfl⟩ : syracuseStep 2049925 = 384361) (by norm_num)
theorem B2049961 : Blo 1821612 2049961 := bbase (se 2 (by rfl) ⟨768735, by rfl⟩ : syracuseStep 2049961 = 1537471) (by norm_num)
theorem B2770861 : Blo 1821612 2770861 := bbase (se 3 (by rfl) ⟨519536, by rfl⟩ : syracuseStep 2770861 = 1039073) (by norm_num)
theorem B2631613 : Blo 1821612 2631613 := bbase (se 3 (by rfl) ⟨493427, by rfl⟩ : syracuseStep 2631613 = 986855) (by norm_num)
theorem B3073997 : Blo 1821612 3073997 := bbase (se 3 (by rfl) ⟨576374, by rfl⟩ : syracuseStep 3073997 = 1152749) (by norm_num)
theorem B2049997 : Blo 1821612 2049997 := bbase (se 3 (by rfl) ⟨384374, by rfl⟩ : syracuseStep 2049997 = 768749) (by norm_num)
theorem B3459037 : Blo 1821612 3459037 := bbase (se 3 (by rfl) ⟨648569, by rfl⟩ : syracuseStep 3459037 = 1297139) (by norm_num)
theorem B2050033 : Blo 1821612 2050033 := bbase (se 2 (by rfl) ⟨768762, by rfl⟩ : syracuseStep 2050033 = 1537525) (by norm_num)
theorem B8759285 : Blo 1821612 8759285 := bbase (se 5 (by rfl) ⟨410591, by rfl⟩ : syracuseStep 8759285 = 821183) (by norm_num)
theorem B2050069 : Blo 1821612 2050069 := bbase (se 6 (by rfl) ⟨48048, by rfl⟩ : syracuseStep 2050069 = 96097) (by norm_num)
theorem B2050105 : Blo 1821612 2050105 := bbase (se 2 (by rfl) ⟨768789, by rfl⟩ : syracuseStep 2050105 = 1537579) (by norm_num)
theorem B4614205 : Blo 1821612 4614205 := bbase (se 3 (by rfl) ⟨865163, by rfl⟩ : syracuseStep 4614205 = 1730327) (by norm_num)
theorem B3074125 : Blo 1821612 3074125 := bbase (se 3 (by rfl) ⟨576398, by rfl⟩ : syracuseStep 3074125 = 1152797) (by norm_num)
theorem B6154325 : Blo 1821612 6154325 := bbase (se 8 (by rfl) ⟨36060, by rfl⟩ : syracuseStep 6154325 = 72121) (by norm_num)
theorem B2050141 : Blo 1821612 2050141 := bbase (se 3 (by rfl) ⟨384401, by rfl⟩ : syracuseStep 2050141 = 768803) (by norm_num)
theorem B3696733 : Blo 1821612 3696733 := bbase (se 3 (by rfl) ⟨693137, by rfl⟩ : syracuseStep 3696733 = 1386275) (by norm_num)
theorem B3459181 : Blo 1821612 3459181 := bbase (se 3 (by rfl) ⟨648596, by rfl⟩ : syracuseStep 3459181 = 1297193) (by norm_num)
theorem B5187701 : Blo 1821612 5187701 := bbase (se 5 (by rfl) ⟨243173, by rfl⟩ : syracuseStep 5187701 = 486347) (by norm_num)
theorem B2050177 : Blo 1821612 2050177 := bbase (se 2 (by rfl) ⟨768816, by rfl⟩ : syracuseStep 2050177 = 1537633) (by norm_num)
theorem B3074213 : Blo 1821612 3074213 := bbase (se 4 (by rfl) ⟨288207, by rfl⟩ : syracuseStep 3074213 = 576415) (by norm_num)
theorem B4925605 : Blo 1821612 4925605 := bbase (se 4 (by rfl) ⟨461775, by rfl⟩ : syracuseStep 4925605 = 923551) (by norm_num)
theorem B2050213 : Blo 1821612 2050213 := bbase (se 4 (by rfl) ⟨192207, by rfl⟩ : syracuseStep 2050213 = 384415) (by norm_num)
theorem B4614317 : Blo 1821612 4614317 := bbase (se 3 (by rfl) ⟨865184, by rfl⟩ : syracuseStep 4614317 = 1730369) (by norm_num)
theorem B2050249 : Blo 1821612 2050249 := bbase (se 2 (by rfl) ⟨768843, by rfl⟩ : syracuseStep 2050249 = 1537687) (by norm_num)
theorem B2771165 : Blo 1821612 2771165 := bbase (se 3 (by rfl) ⟨519593, by rfl⟩ : syracuseStep 2771165 = 1039187) (by norm_num)
theorem B2050285 : Blo 1821612 2050285 := bbase (se 3 (by rfl) ⟨384428, by rfl⟩ : syracuseStep 2050285 = 768857) (by norm_num)
theorem B11233525 : Blo 1821612 11233525 := bbase (se 5 (by rfl) ⟨526571, by rfl⟩ : syracuseStep 11233525 = 1053143) (by norm_num)
theorem B3459341 : Blo 1821612 3459341 := bbase (se 3 (by rfl) ⟨648626, by rfl⟩ : syracuseStep 3459341 = 1297253) (by norm_num)
theorem B2050321 : Blo 1821612 2050321 := bbase (se 2 (by rfl) ⟨768870, by rfl⟩ : syracuseStep 2050321 = 1537741) (by norm_num)
theorem B3074341 : Blo 1821612 3074341 := bbase (se 4 (by rfl) ⟨288219, by rfl⟩ : syracuseStep 3074341 = 576439) (by norm_num)
theorem B2771237 : Blo 1821612 2771237 := bbase (se 4 (by rfl) ⟨259803, by rfl⟩ : syracuseStep 2771237 = 519607) (by norm_num)
theorem B2050357 : Blo 1821612 2050357 := bbase (se 5 (by rfl) ⟨96110, by rfl⟩ : syracuseStep 2050357 = 192221) (by norm_num)
theorem B2189629 : Blo 1821612 2189629 := bbase (se 3 (by rfl) ⟨410555, by rfl⟩ : syracuseStep 2189629 = 821111) (by norm_num)
theorem B2050393 : Blo 1821612 2050393 := bbase (se 2 (by rfl) ⟨768897, by rfl⟩ : syracuseStep 2050393 = 1537795) (by norm_num)
theorem B2189657 : Blo 1821612 2189657 := bbase (se 2 (by rfl) ⟨821121, by rfl⟩ : syracuseStep 2189657 = 1642243) (by norm_num)
theorem B2918749 : Blo 1821612 2918749 := bbase (se 3 (by rfl) ⟨547265, by rfl⟩ : syracuseStep 2918749 = 1094531) (by norm_num)
theorem B4614509 : Blo 1821612 4614509 := bbase (se 3 (by rfl) ⟨865220, by rfl⟩ : syracuseStep 4614509 = 1730441) (by norm_num)
theorem B2107765 : Blo 1821612 2107765 := bbase (se 5 (by rfl) ⟨98801, by rfl⟩ : syracuseStep 2107765 = 197603) (by norm_num)
theorem B3074429 : Blo 1821612 3074429 := bbase (se 3 (by rfl) ⟨576455, by rfl⟩ : syracuseStep 3074429 = 1152911) (by norm_num)
theorem B2050429 : Blo 1821612 2050429 := bbase (se 3 (by rfl) ⟨384455, by rfl⟩ : syracuseStep 2050429 = 768911) (by norm_num)
theorem B6752645 : Blo 1821612 6752645 := bbase (se 4 (by rfl) ⟨633060, by rfl⟩ : syracuseStep 6752645 = 1266121) (by norm_num)
theorem B3459485 : Blo 1821612 3459485 := bbase (se 3 (by rfl) ⟨648653, by rfl⟩ : syracuseStep 3459485 = 1297307) (by norm_num)
theorem B2050465 : Blo 1821612 2050465 := bbase (se 2 (by rfl) ⟨768924, by rfl⟩ : syracuseStep 2050465 = 1537849) (by norm_num)
theorem B2050501 : Blo 1821612 2050501 := bbase (se 4 (by rfl) ⟨192234, by rfl⟩ : syracuseStep 2050501 = 384469) (by norm_num)
theorem B9226709 : Blo 1821612 9226709 := bbase (se 7 (by rfl) ⟨108125, by rfl⟩ : syracuseStep 9226709 = 216251) (by norm_num)
theorem B2050537 : Blo 1821612 2050537 := bbase (se 2 (by rfl) ⟨768951, by rfl⟩ : syracuseStep 2050537 = 1537903) (by norm_num)
theorem B3893741 : Blo 1821612 3893741 := bbase (se 3 (by rfl) ⟨730076, by rfl⟩ : syracuseStep 3893741 = 1460153) (by norm_num)
theorem B3074557 : Blo 1821612 3074557 := bbase (se 3 (by rfl) ⟨576479, by rfl⟩ : syracuseStep 3074557 = 1152959) (by norm_num)
theorem B2050573 : Blo 1821612 2050573 := bbase (se 3 (by rfl) ⟨384482, by rfl⟩ : syracuseStep 2050573 = 768965) (by norm_num)
theorem B2189845 : Blo 1821612 2189845 := bbase (se 6 (by rfl) ⟨51324, by rfl⟩ : syracuseStep 2189845 = 102649) (by norm_num)
theorem B2050609 : Blo 1821612 2050609 := bbase (se 2 (by rfl) ⟨768978, by rfl⟩ : syracuseStep 2050609 = 1537957) (by norm_num)
theorem B6916661 : Blo 1821612 6916661 := bbase (se 5 (by rfl) ⟨324218, by rfl⟩ : syracuseStep 6916661 = 648437) (by norm_num)
theorem B9357893 : Blo 1821612 9357893 := bbase (se 4 (by rfl) ⟨877302, by rfl⟩ : syracuseStep 9357893 = 1754605) (by norm_num)
theorem B3074645 : Blo 1821612 3074645 := bbase (se 8 (by rfl) ⟨18015, by rfl⟩ : syracuseStep 3074645 = 36031) (by norm_num)
theorem B4926037 : Blo 1821612 4926037 := bbase (se 8 (by rfl) ⟨28863, by rfl⟩ : syracuseStep 4926037 = 57727) (by norm_num)
theorem B2050645 : Blo 1821612 2050645 := bbase (se 8 (by rfl) ⟨12015, by rfl⟩ : syracuseStep 2050645 = 24031) (by norm_num)
theorem B4098653 : Blo 1821612 4098653 := bbase (se 3 (by rfl) ⟨768497, by rfl⟩ : syracuseStep 4098653 = 1536995) (by norm_num)
theorem B2919005 : Blo 1821612 2919005 := bbase (se 3 (by rfl) ⟨547313, by rfl⟩ : syracuseStep 2919005 = 1094627) (by norm_num)
theorem B2050681 : Blo 1821612 2050681 := bbase (se 2 (by rfl) ⟨769005, by rfl⟩ : syracuseStep 2050681 = 1538011) (by norm_num)
theorem B2189965 : Blo 1821612 2189965 := bbase (se 3 (by rfl) ⟨410618, by rfl⟩ : syracuseStep 2189965 = 821237) (by norm_num)
theorem B2050717 : Blo 1821612 2050717 := bbase (se 3 (by rfl) ⟨384509, by rfl⟩ : syracuseStep 2050717 = 769019) (by norm_num)
theorem B4098725 : Blo 1821612 4098725 := bbase (se 4 (by rfl) ⟨384255, by rfl⟩ : syracuseStep 4098725 = 768511) (by norm_num)
theorem B4991669 : Blo 1821612 4991669 := bbase (se 5 (by rfl) ⟨233984, by rfl⟩ : syracuseStep 4991669 = 467969) (by norm_num)
theorem B4377277 : Blo 1821612 4377277 := bbase (se 3 (by rfl) ⟨820739, by rfl⟩ : syracuseStep 4377277 = 1641479) (by norm_num)
theorem B3459773 : Blo 1821612 3459773 := bbase (se 3 (by rfl) ⟨648707, by rfl⟩ : syracuseStep 3459773 = 1297415) (by norm_num)
theorem B2050753 : Blo 1821612 2050753 := bbase (se 2 (by rfl) ⟨769032, by rfl⟩ : syracuseStep 2050753 = 1538065) (by norm_num)
theorem B4614853 : Blo 1821612 4614853 := bbase (se 4 (by rfl) ⟨432642, by rfl⟩ : syracuseStep 4614853 = 865285) (by norm_num)
theorem B3074773 : Blo 1821612 3074773 := bbase (se 7 (by rfl) ⟨36032, by rfl⟩ : syracuseStep 3074773 = 72065) (by norm_num)
theorem B7785173 : Blo 1821612 7785173 := bbase (se 7 (by rfl) ⟨91232, by rfl⟩ : syracuseStep 7785173 = 182465) (by norm_num)
theorem B2050789 : Blo 1821612 2050789 := bbase (se 4 (by rfl) ⟨192261, by rfl⟩ : syracuseStep 2050789 = 384523) (by norm_num)
theorem B4098797 : Blo 1821612 4098797 := bbase (se 3 (by rfl) ⟨768524, by rfl⟩ : syracuseStep 4098797 = 1537049) (by norm_num)
theorem B3328765 : Blo 1821612 3328765 := bbase (se 3 (by rfl) ⟨624143, by rfl⟩ : syracuseStep 3328765 = 1248287) (by norm_num)
theorem B2050825 : Blo 1821612 2050825 := bbase (se 2 (by rfl) ⟨769059, by rfl⟩ : syracuseStep 2050825 = 1538119) (by norm_num)
theorem B2919197 : Blo 1821612 2919197 := bbase (se 3 (by rfl) ⟨547349, by rfl⟩ : syracuseStep 2919197 = 1094699) (by norm_num)
theorem B3074861 : Blo 1821612 3074861 := bbase (se 3 (by rfl) ⟨576536, by rfl⟩ : syracuseStep 3074861 = 1153073) (by norm_num)
theorem B2050861 : Blo 1821612 2050861 := bbase (se 3 (by rfl) ⟨384536, by rfl⟩ : syracuseStep 2050861 = 769073) (by norm_num)
theorem B4098869 : Blo 1821612 4098869 := bbase (se 5 (by rfl) ⟨192134, by rfl⟩ : syracuseStep 4098869 = 384269) (by norm_num)
theorem B4614965 : Blo 1821612 4614965 := bbase (se 5 (by rfl) ⟨216326, by rfl⟩ : syracuseStep 4614965 = 432653) (by norm_num)
theorem B2050897 : Blo 1821612 2050897 := bbase (se 2 (by rfl) ⟨769086, by rfl⟩ : syracuseStep 2050897 = 1538173) (by norm_num)
theorem B3459925 : Blo 1821612 3459925 := bbase (se 9 (by rfl) ⟨10136, by rfl⟩ : syracuseStep 3459925 = 20273) (by norm_num)
theorem B2050933 : Blo 1821612 2050933 := bbase (se 5 (by rfl) ⟨96137, by rfl⟩ : syracuseStep 2050933 = 192275) (by norm_num)
theorem B4098941 : Blo 1821612 4098941 := bbase (se 3 (by rfl) ⟨768551, by rfl⟩ : syracuseStep 4098941 = 1537103) (by norm_num)
theorem B4377469 : Blo 1821612 4377469 := bbase (se 3 (by rfl) ⟨820775, by rfl⟩ : syracuseStep 4377469 = 1641551) (by norm_num)
theorem B2050969 : Blo 1821612 2050969 := bbase (se 2 (by rfl) ⟨769113, by rfl⟩ : syracuseStep 2050969 = 1538227) (by norm_num)
theorem B2771869 : Blo 1821612 2771869 := bbase (se 3 (by rfl) ⟨519725, by rfl⟩ : syracuseStep 2771869 = 1039451) (by norm_num)
theorem B2960285 : Blo 1821612 2960285 := bbase (se 3 (by rfl) ⟨555053, by rfl⟩ : syracuseStep 2960285 = 1110107) (by norm_num)
theorem B3509149 : Blo 1821612 3509149 := bbase (se 3 (by rfl) ⟨657965, by rfl⟩ : syracuseStep 3509149 = 1315931) (by norm_num)
theorem B4377509 : Blo 1821612 4377509 := bbase (se 4 (by rfl) ⟨410391, by rfl⟩ : syracuseStep 4377509 = 820783) (by norm_num)
theorem B3074989 : Blo 1821612 3074989 := bbase (se 3 (by rfl) ⟨576560, by rfl⟩ : syracuseStep 3074989 = 1153121) (by norm_num)
theorem B2051005 : Blo 1821612 2051005 := bbase (se 3 (by rfl) ⟨384563, by rfl⟩ : syracuseStep 2051005 = 769127) (by norm_num)
theorem B4099013 : Blo 1821612 4099013 := bbase (se 4 (by rfl) ⟨384282, by rfl⟩ : syracuseStep 4099013 = 768565) (by norm_num)
theorem B4156381 : Blo 1821612 4156381 := bbase (se 3 (by rfl) ⟨779321, by rfl⟩ : syracuseStep 4156381 = 1558643) (by norm_num)
theorem B2051041 : Blo 1821612 2051041 := bbase (se 2 (by rfl) ⟨769140, by rfl⟩ : syracuseStep 2051041 = 1538281) (by norm_num)
theorem B4615157 : Blo 1821612 4615157 := bbase (se 5 (by rfl) ⟨216335, by rfl⟩ : syracuseStep 4615157 = 432671) (by norm_num)
theorem B3075077 : Blo 1821612 3075077 := bbase (se 4 (by rfl) ⟨288288, by rfl⟩ : syracuseStep 3075077 = 576577) (by norm_num)
theorem B2051077 : Blo 1821612 2051077 := bbase (se 4 (by rfl) ⟨192288, by rfl⟩ : syracuseStep 2051077 = 384577) (by norm_num)
theorem B4099085 : Blo 1821612 4099085 := bbase (se 3 (by rfl) ⟨768578, by rfl⟩ : syracuseStep 4099085 = 1537157) (by norm_num)
theorem B2051113 : Blo 1821612 2051113 := bbase (se 2 (by rfl) ⟨769167, by rfl⟩ : syracuseStep 2051113 = 1538335) (by norm_num)
theorem B6237253 : Blo 1821612 6237253 := bbase (se 4 (by rfl) ⟨584742, by rfl⟩ : syracuseStep 6237253 = 1169485) (by norm_num)
theorem B2051149 : Blo 1821612 2051149 := bbase (se 3 (by rfl) ⟨384590, by rfl⟩ : syracuseStep 2051149 = 769181) (by norm_num)
theorem B4099157 : Blo 1821612 4099157 := bbase (se 8 (by rfl) ⟨24018, by rfl⟩ : syracuseStep 4099157 = 48037) (by norm_num)
theorem B2051185 : Blo 1821612 2051185 := bbase (se 2 (by rfl) ⟨769194, by rfl⟩ : syracuseStep 2051185 = 1538389) (by norm_num)
theorem B3075205 : Blo 1821612 3075205 := bbase (se 4 (by rfl) ⟨288300, by rfl⟩ : syracuseStep 3075205 = 576601) (by norm_num)
theorem B3460229 : Blo 1821612 3460229 := bbase (se 4 (by rfl) ⟨324396, by rfl⟩ : syracuseStep 3460229 = 648793) (by norm_num)
theorem B2051221 : Blo 1821612 2051221 := bbase (se 6 (by rfl) ⟨48075, by rfl⟩ : syracuseStep 2051221 = 96151) (by norm_num)
theorem B4099229 : Blo 1821612 4099229 := bbase (se 3 (by rfl) ⟨768605, by rfl⟩ : syracuseStep 4099229 = 1537211) (by norm_num)
theorem B2051257 : Blo 1821612 2051257 := bbase (se 2 (by rfl) ⟨769221, by rfl⟩ : syracuseStep 2051257 = 1538443) (by norm_num)
theorem B4377797 : Blo 1821612 4377797 := bbase (se 4 (by rfl) ⟨410418, by rfl⟩ : syracuseStep 4377797 = 820837) (by norm_num)
theorem B13135061 : Blo 1821612 13135061 := bbase (se 7 (by rfl) ⟨153926, by rfl⟩ : syracuseStep 13135061 = 307853) (by norm_num)
theorem B3075293 : Blo 1821612 3075293 := bbase (se 3 (by rfl) ⟨576617, by rfl⟩ : syracuseStep 3075293 = 1153235) (by norm_num)
theorem B2051293 : Blo 1821612 2051293 := bbase (se 3 (by rfl) ⟨384617, by rfl⟩ : syracuseStep 2051293 = 769235) (by norm_num)
theorem B3894493 : Blo 1821612 3894493 := bbase (se 3 (by rfl) ⟨730217, by rfl⟩ : syracuseStep 3894493 = 1460435) (by norm_num)
theorem B4099301 : Blo 1821612 4099301 := bbase (se 4 (by rfl) ⟨384309, by rfl⟩ : syracuseStep 4099301 = 768619) (by norm_num)
theorem B2051329 : Blo 1821612 2051329 := bbase (se 2 (by rfl) ⟨769248, by rfl⟩ : syracuseStep 2051329 = 1538497) (by norm_num)
theorem B6237461 : Blo 1821612 6237461 := bbase (se 6 (by rfl) ⟨146190, by rfl⟩ : syracuseStep 6237461 = 292381) (by norm_num)
theorem B2051365 : Blo 1821612 2051365 := bbase (se 4 (by rfl) ⟨192315, by rfl⟩ : syracuseStep 2051365 = 384631) (by norm_num)
theorem B4099373 : Blo 1821612 4099373 := bbase (se 3 (by rfl) ⟨768632, by rfl⟩ : syracuseStep 4099373 = 1537265) (by norm_num)
theorem B2051401 : Blo 1821612 2051401 := bbase (se 2 (by rfl) ⟨769275, by rfl⟩ : syracuseStep 2051401 = 1538551) (by norm_num)
theorem B4615501 : Blo 1821612 4615501 := bbase (se 3 (by rfl) ⟨865406, by rfl⟩ : syracuseStep 4615501 = 1730813) (by norm_num)
theorem B3075421 : Blo 1821612 3075421 := bbase (se 3 (by rfl) ⟨576641, by rfl⟩ : syracuseStep 3075421 = 1153283) (by norm_num)
theorem B2051437 : Blo 1821612 2051437 := bbase (se 3 (by rfl) ⟨384644, by rfl⟩ : syracuseStep 2051437 = 769289) (by norm_num)
theorem B3894637 : Blo 1821612 3894637 := bbase (se 3 (by rfl) ⟨730244, by rfl⟩ : syracuseStep 3894637 = 1460489) (by norm_num)
theorem B4099445 : Blo 1821612 4099445 := bbase (se 5 (by rfl) ⟨192161, by rfl⟩ : syracuseStep 4099445 = 384323) (by norm_num)
theorem B2051473 : Blo 1821612 2051473 := bbase (se 2 (by rfl) ⟨769302, by rfl⟩ : syracuseStep 2051473 = 1538605) (by norm_num)
theorem B33238421 : Blo 1821612 33238421 := bbase (se 6 (by rfl) ⟨779025, by rfl⟩ : syracuseStep 33238421 = 1558051) (by norm_num)
theorem B3075509 : Blo 1821612 3075509 := bbase (se 5 (by rfl) ⟨144164, by rfl⟩ : syracuseStep 3075509 = 288329) (by norm_num)
theorem B2051509 : Blo 1821612 2051509 := bbase (se 5 (by rfl) ⟨96164, by rfl⟩ : syracuseStep 2051509 = 192329) (by norm_num)
theorem B4099517 : Blo 1821612 4099517 := bbase (se 3 (by rfl) ⟨768659, by rfl⟩ : syracuseStep 4099517 = 1537319) (by norm_num)
theorem B4615613 : Blo 1821612 4615613 := bbase (se 3 (by rfl) ⟨865427, by rfl⟩ : syracuseStep 4615613 = 1730855) (by norm_num)
theorem B2051545 : Blo 1821612 2051545 := bbase (se 2 (by rfl) ⟨769329, by rfl⟩ : syracuseStep 2051545 = 1538659) (by norm_num)
theorem B2305513 : Blo 1821612 2305513 := bbase (se 2 (by rfl) ⟨864567, by rfl⟩ : syracuseStep 2305513 = 1729135) (by norm_num)
theorem B4099589 : Blo 1821612 4099589 := bbase (se 4 (by rfl) ⟨384336, by rfl⟩ : syracuseStep 4099589 = 768673) (by norm_num)
theorem B3075637 : Blo 1821612 3075637 := bbase (se 5 (by rfl) ⟨144170, by rfl⟩ : syracuseStep 3075637 = 288341) (by norm_num)
theorem B4099661 : Blo 1821612 4099661 := bbase (se 3 (by rfl) ⟨768686, by rfl⟩ : syracuseStep 4099661 = 1537373) (by norm_num)
theorem B4615805 : Blo 1821612 4615805 := bbase (se 3 (by rfl) ⟨865463, by rfl⟩ : syracuseStep 4615805 = 1730927) (by norm_num)
theorem B3075725 : Blo 1821612 3075725 := bbase (se 3 (by rfl) ⟨576698, by rfl⟩ : syracuseStep 3075725 = 1153397) (by norm_num)
theorem B2305685 : Blo 1821612 2305685 := bbase (se 6 (by rfl) ⟨54039, by rfl⟩ : syracuseStep 2305685 = 108079) (by norm_num)
theorem B4099733 : Blo 1821612 4099733 := bbase (se 6 (by rfl) ⟨96087, by rfl⟩ : syracuseStep 4099733 = 192175) (by norm_num)
theorem B9850517 : Blo 1821612 9850517 := bbase (se 6 (by rfl) ⟨230871, by rfl⟩ : syracuseStep 9850517 = 461743) (by norm_num)
theorem B5189285 : Blo 1821612 5189285 := bbase (se 4 (by rfl) ⟨486495, by rfl⟩ : syracuseStep 5189285 = 972991) (by norm_num)
theorem B7786165 : Blo 1821612 7786165 := bbase (se 5 (by rfl) ⟨364976, by rfl⟩ : syracuseStep 7786165 = 729953) (by norm_num)
theorem B2920133 : Blo 1821612 2920133 := bbase (se 4 (by rfl) ⟨273762, by rfl⟩ : syracuseStep 2920133 = 547525) (by norm_num)
theorem B2305741 : Blo 1821612 2305741 := bbase (se 3 (by rfl) ⟨432326, by rfl⟩ : syracuseStep 2305741 = 864653) (by norm_num)
theorem B6917845 : Blo 1821612 6917845 := bbase (se 7 (by rfl) ⟨81068, by rfl⟩ : syracuseStep 6917845 = 162137) (by norm_num)
theorem B4099805 : Blo 1821612 4099805 := bbase (se 3 (by rfl) ⟨768713, by rfl⟩ : syracuseStep 4099805 = 1537427) (by norm_num)
theorem B9228005 : Blo 1821612 9228005 := bbase (se 4 (by rfl) ⟨865125, by rfl⟩ : syracuseStep 9228005 = 1730251) (by norm_num)
theorem B4927205 : Blo 1821612 4927205 := bbase (se 4 (by rfl) ⟨461925, by rfl⟩ : syracuseStep 4927205 = 923851) (by norm_num)
theorem B1945333 : Blo 1821612 1945333 := bbase (se 5 (by rfl) ⟨91187, by rfl⟩ : syracuseStep 1945333 = 182375) (by norm_num)
theorem B5836549 : Blo 1821612 5836549 := bbase (se 4 (by rfl) ⟨547176, by rfl⟩ : syracuseStep 5836549 = 1094353) (by norm_num)
theorem B3075853 : Blo 1821612 3075853 := bbase (se 3 (by rfl) ⟨576722, by rfl⟩ : syracuseStep 3075853 = 1153445) (by norm_num)
theorem B4099877 : Blo 1821612 4099877 := bbase (se 4 (by rfl) ⟨384363, by rfl⟩ : syracuseStep 4099877 = 768727) (by norm_num)
theorem B2305837 : Blo 1821612 2305837 := bbase (se 3 (by rfl) ⟨432344, by rfl⟩ : syracuseStep 2305837 = 864689) (by norm_num)
theorem B1945405 : Blo 1821612 1945405 := bbase (se 3 (by rfl) ⟨364763, by rfl⟩ : syracuseStep 1945405 = 729527) (by norm_num)
theorem B3944261 : Blo 1821612 3944261 := bbase (se 4 (by rfl) ⟨369774, by rfl⟩ : syracuseStep 3944261 = 739549) (by norm_num)
theorem B3075941 : Blo 1821612 3075941 := bbase (se 4 (by rfl) ⟨288369, by rfl⟩ : syracuseStep 3075941 = 576739) (by norm_num)
theorem B4099949 : Blo 1821612 4099949 := bbase (se 3 (by rfl) ⟨768740, by rfl⟩ : syracuseStep 4099949 = 1537481) (by norm_num)
theorem B3460981 : Blo 1821612 3460981 := bbase (se 5 (by rfl) ⟨162233, by rfl⟩ : syracuseStep 3460981 = 324467) (by norm_num)
theorem B4100021 : Blo 1821612 4100021 := bbase (se 5 (by rfl) ⟨192188, by rfl⟩ : syracuseStep 4100021 = 384377) (by norm_num)
theorem B2306009 : Blo 1821612 2306009 := bbase (se 2 (by rfl) ⟨864753, by rfl⟩ : syracuseStep 2306009 = 1729507) (by norm_num)
theorem B3076069 : Blo 1821612 3076069 := bbase (se 4 (by rfl) ⟨288381, by rfl⟩ : syracuseStep 3076069 = 576763) (by norm_num)
theorem B4100093 : Blo 1821612 4100093 := bbase (se 3 (by rfl) ⟨768767, by rfl⟩ : syracuseStep 4100093 = 1537535) (by norm_num)
theorem B6918149 : Blo 1821612 6918149 := bbase (se 4 (by rfl) ⟨648576, by rfl⟩ : syracuseStep 6918149 = 1297153) (by norm_num)
theorem B3461125 : Blo 1821612 3461125 := bbase (se 4 (by rfl) ⟨324480, by rfl⟩ : syracuseStep 3461125 = 648961) (by norm_num)
theorem B2306065 : Blo 1821612 2306065 := bbase (se 2 (by rfl) ⟨864774, by rfl⟩ : syracuseStep 2306065 = 1729549) (by norm_num)
theorem B12472373 : Blo 1821612 12472373 := bbase (se 5 (by rfl) ⟨584642, by rfl⟩ : syracuseStep 12472373 = 1169285) (by norm_num)
theorem B3076157 : Blo 1821612 3076157 := bbase (se 3 (by rfl) ⟨576779, by rfl⟩ : syracuseStep 3076157 = 1153559) (by norm_num)
theorem B4100165 : Blo 1821612 4100165 := bbase (se 4 (by rfl) ⟨384390, by rfl⟩ : syracuseStep 4100165 = 768781) (by norm_num)
theorem B2920517 : Blo 1821612 2920517 := bbase (se 4 (by rfl) ⟨273798, by rfl⟩ : syracuseStep 2920517 = 547597) (by norm_num)
theorem B2306161 : Blo 1821612 2306161 := bbase (se 2 (by rfl) ⟨864810, by rfl⟩ : syracuseStep 2306161 = 1729621) (by norm_num)
theorem B4100237 : Blo 1821612 4100237 := bbase (se 3 (by rfl) ⟨768794, by rfl⟩ : syracuseStep 4100237 = 1537589) (by norm_num)
theorem B3461285 : Blo 1821612 3461285 := bbase (se 4 (by rfl) ⟨324495, by rfl⟩ : syracuseStep 3461285 = 648991) (by norm_num)
theorem B1945777 : Blo 1821612 1945777 := bbase (se 2 (by rfl) ⟨729666, by rfl⟩ : syracuseStep 1945777 = 1459333) (by norm_num)
theorem B6148277 : Blo 1821612 6148277 := bbase (se 5 (by rfl) ⟨288200, by rfl⟩ : syracuseStep 6148277 = 576401) (by norm_num)
theorem B3076285 : Blo 1821612 3076285 := bbase (se 3 (by rfl) ⟨576803, by rfl⟩ : syracuseStep 3076285 = 1153607) (by norm_num)
theorem B2920645 : Blo 1821612 2920645 := bbase (se 4 (by rfl) ⟨273810, by rfl⟩ : syracuseStep 2920645 = 547621) (by norm_num)
theorem B4100309 : Blo 1821612 4100309 := bbase (se 7 (by rfl) ⟨48050, by rfl⟩ : syracuseStep 4100309 = 96101) (by norm_num)
theorem B3076373 : Blo 1821612 3076373 := bbase (se 6 (by rfl) ⟨72102, by rfl⟩ : syracuseStep 3076373 = 144205) (by norm_num)
theorem B2306333 : Blo 1821612 2306333 := bbase (se 3 (by rfl) ⟨432437, by rfl⟩ : syracuseStep 2306333 = 864875) (by norm_num)
theorem B4100381 : Blo 1821612 4100381 := bbase (se 3 (by rfl) ⟨768821, by rfl⟩ : syracuseStep 4100381 = 1537643) (by norm_num)
theorem B3117341 : Blo 1821612 3117341 := bbase (se 3 (by rfl) ⟨584501, by rfl⟩ : syracuseStep 3117341 = 1169003) (by norm_num)
theorem B3461429 : Blo 1821612 3461429 := bbase (se 5 (by rfl) ⟨162254, by rfl⟩ : syracuseStep 3461429 = 324509) (by norm_num)
theorem B5189957 : Blo 1821612 5189957 := bbase (se 4 (by rfl) ⟨486558, by rfl⟩ : syracuseStep 5189957 = 973117) (by norm_num)
theorem B1847621 : Blo 1821612 1847621 := bbase (se 4 (by rfl) ⟨173214, by rfl⟩ : syracuseStep 1847621 = 346429) (by norm_num)
theorem B2306389 : Blo 1821612 2306389 := bbase (se 10 (by rfl) ⟨3378, by rfl⟩ : syracuseStep 2306389 = 6757) (by norm_num)
theorem B4100453 : Blo 1821612 4100453 := bbase (se 4 (by rfl) ⟨384417, by rfl⟩ : syracuseStep 4100453 = 768835) (by norm_num)
theorem B2732429 : Blo 1821612 2732429 := bbase (se 3 (by rfl) ⟨512330, by rfl⟩ : syracuseStep 2732429 = 1024661) (by norm_num)
theorem B3076501 : Blo 1821612 3076501 := bbase (se 6 (by rfl) ⟨72105, by rfl⟩ : syracuseStep 3076501 = 144211) (by norm_num)
theorem B2732453 : Blo 1821612 2732453 := bbase (se 4 (by rfl) ⟨256167, by rfl⟩ : syracuseStep 2732453 = 512335) (by norm_num)
theorem B4100525 : Blo 1821612 4100525 := bbase (se 3 (by rfl) ⟨768848, by rfl⟩ : syracuseStep 4100525 = 1537697) (by norm_num)
theorem B2306485 : Blo 1821612 2306485 := bbase (se 5 (by rfl) ⟨108116, by rfl⟩ : syracuseStep 2306485 = 216233) (by norm_num)
theorem B2732477 : Blo 1821612 2732477 := bbase (se 3 (by rfl) ⟨512339, by rfl⟩ : syracuseStep 2732477 = 1024679) (by norm_num)
theorem B2732501 : Blo 1821612 2732501 := bbase (se 7 (by rfl) ⟨32021, by rfl⟩ : syracuseStep 2732501 = 64043) (by norm_num)
theorem B2732525 : Blo 1821612 2732525 := bbase (se 3 (by rfl) ⟨512348, by rfl⟩ : syracuseStep 2732525 = 1024697) (by norm_num)
theorem B3076589 : Blo 1821612 3076589 := bbase (se 3 (by rfl) ⟨576860, by rfl⟩ : syracuseStep 3076589 = 1153721) (by norm_num)
theorem B4100597 : Blo 1821612 4100597 := bbase (se 5 (by rfl) ⟨192215, by rfl⟩ : syracuseStep 4100597 = 384431) (by norm_num)
theorem B2732549 : Blo 1821612 2732549 := bbase (se 4 (by rfl) ⟨256176, by rfl⟩ : syracuseStep 2732549 = 512353) (by norm_num)
theorem B2732573 : Blo 1821612 2732573 := bbase (se 3 (by rfl) ⟨512357, by rfl⟩ : syracuseStep 2732573 = 1024715) (by norm_num)
theorem B1946153 : Blo 1821612 1946153 := bbase (se 2 (by rfl) ⟨729807, by rfl⟩ : syracuseStep 1946153 = 1459615) (by norm_num)
theorem B2732597 : Blo 1821612 2732597 := bbase (se 5 (by rfl) ⟨128090, by rfl⟩ : syracuseStep 2732597 = 256181) (by norm_num)
theorem B4100669 : Blo 1821612 4100669 := bbase (se 3 (by rfl) ⟨768875, by rfl⟩ : syracuseStep 4100669 = 1537751) (by norm_num)
theorem B2732621 : Blo 1821612 2732621 := bbase (se 3 (by rfl) ⟨512366, by rfl⟩ : syracuseStep 2732621 = 1024733) (by norm_num)
theorem B3461717 : Blo 1821612 3461717 := bbase (se 8 (by rfl) ⟨20283, by rfl⟩ : syracuseStep 3461717 = 40567) (by norm_num)
theorem B2306657 : Blo 1821612 2306657 := bbase (se 2 (by rfl) ⟨864996, by rfl⟩ : syracuseStep 2306657 = 1729993) (by norm_num)
theorem B2732645 : Blo 1821612 2732645 := bbase (se 4 (by rfl) ⟨256185, by rfl⟩ : syracuseStep 2732645 = 512371) (by norm_num)
theorem B6148709 : Blo 1821612 6148709 := bbase (se 4 (by rfl) ⟨576441, by rfl⟩ : syracuseStep 6148709 = 1152883) (by norm_num)
theorem B3076717 : Blo 1821612 3076717 := bbase (se 3 (by rfl) ⟨576884, by rfl⟩ : syracuseStep 3076717 = 1153769) (by norm_num)
theorem B1946225 : Blo 1821612 1946225 := bbase (se 2 (by rfl) ⟨729834, by rfl⟩ : syracuseStep 1946225 = 1459669) (by norm_num)
theorem B12472949 : Blo 1821612 12472949 := bbase (se 5 (by rfl) ⟨584669, by rfl⟩ : syracuseStep 12472949 = 1169339) (by norm_num)
theorem B2732669 : Blo 1821612 2732669 := bbase (se 3 (by rfl) ⟨512375, by rfl⟩ : syracuseStep 2732669 = 1024751) (by norm_num)
theorem B4100741 : Blo 1821612 4100741 := bbase (se 4 (by rfl) ⟨384444, by rfl⟩ : syracuseStep 4100741 = 768889) (by norm_num)
theorem B2667149 : Blo 1821612 2667149 := bbase (se 3 (by rfl) ⟨500090, by rfl⟩ : syracuseStep 2667149 = 1000181) (by norm_num)
theorem B2732693 : Blo 1821612 2732693 := bbase (se 6 (by rfl) ⟨64047, by rfl⟩ : syracuseStep 2732693 = 128095) (by norm_num)
theorem B2306713 : Blo 1821612 2306713 := bbase (se 2 (by rfl) ⟨865017, by rfl⟩ : syracuseStep 2306713 = 1730035) (by norm_num)
theorem B2732717 : Blo 1821612 2732717 := bbase (se 3 (by rfl) ⟨512384, by rfl⟩ : syracuseStep 2732717 = 1024769) (by norm_num)
theorem B2732741 : Blo 1821612 2732741 := bbase (se 4 (by rfl) ⟨256194, by rfl⟩ : syracuseStep 2732741 = 512389) (by norm_num)
theorem B3076805 : Blo 1821612 3076805 := bbase (se 4 (by rfl) ⟨288450, by rfl⟩ : syracuseStep 3076805 = 576901) (by norm_num)
theorem B4100813 : Blo 1821612 4100813 := bbase (se 3 (by rfl) ⟨768902, by rfl⟩ : syracuseStep 4100813 = 1537805) (by norm_num)
theorem B2732765 : Blo 1821612 2732765 := bbase (se 3 (by rfl) ⟨512393, by rfl⟩ : syracuseStep 2732765 = 1024787) (by norm_num)
theorem B3461869 : Blo 1821612 3461869 := bbase (se 3 (by rfl) ⟨649100, by rfl⟩ : syracuseStep 3461869 = 1298201) (by norm_num)
theorem B2732789 : Blo 1821612 2732789 := bbase (se 5 (by rfl) ⟨128099, by rfl⟩ : syracuseStep 2732789 = 256199) (by norm_num)
theorem B5190389 : Blo 1821612 5190389 := bbase (se 5 (by rfl) ⟨243299, by rfl⟩ : syracuseStep 5190389 = 486599) (by norm_num)
theorem B2306809 : Blo 1821612 2306809 := bbase (se 2 (by rfl) ⟨865053, by rfl⟩ : syracuseStep 2306809 = 1730107) (by norm_num)
theorem B2732813 : Blo 1821612 2732813 := bbase (se 3 (by rfl) ⟨512402, by rfl⟩ : syracuseStep 2732813 = 1024805) (by norm_num)
theorem B4100885 : Blo 1821612 4100885 := bbase (se 6 (by rfl) ⟨96114, by rfl⟩ : syracuseStep 4100885 = 192229) (by norm_num)
theorem B2732837 : Blo 1821612 2732837 := bbase (se 4 (by rfl) ⟨256203, by rfl⟩ : syracuseStep 2732837 = 512407) (by norm_num)
theorem B1946413 : Blo 1821612 1946413 := bbase (se 3 (by rfl) ⟨364952, by rfl⟩ : syracuseStep 1946413 = 729905) (by norm_num)
theorem B8762165 : Blo 1821612 8762165 := bbase (se 5 (by rfl) ⟨410726, by rfl⟩ : syracuseStep 8762165 = 821453) (by norm_num)
theorem B2732861 : Blo 1821612 2732861 := bbase (se 3 (by rfl) ⟨512411, by rfl⟩ : syracuseStep 2732861 = 1024823) (by norm_num)
theorem B3076933 : Blo 1821612 3076933 := bbase (se 4 (by rfl) ⟨288462, by rfl⟩ : syracuseStep 3076933 = 576925) (by norm_num)
theorem B7385941 : Blo 1821612 7385941 := bbase (se 9 (by rfl) ⟨21638, by rfl⟩ : syracuseStep 7385941 = 43277) (by norm_num)
theorem B2732885 : Blo 1821612 2732885 := bbase (se 9 (by rfl) ⟨8006, by rfl⟩ : syracuseStep 2732885 = 16013) (by norm_num)
theorem B4100957 : Blo 1821612 4100957 := bbase (se 3 (by rfl) ⟨768929, by rfl⟩ : syracuseStep 4100957 = 1537859) (by norm_num)
theorem B2732909 : Blo 1821612 2732909 := bbase (se 3 (by rfl) ⟨512420, by rfl⟩ : syracuseStep 2732909 = 1024841) (by norm_num)
theorem B2732933 : Blo 1821612 2732933 := bbase (se 4 (by rfl) ⟨256212, by rfl⟩ : syracuseStep 2732933 = 512425) (by norm_num)
theorem B2732957 : Blo 1821612 2732957 := bbase (se 3 (by rfl) ⟨512429, by rfl⟩ : syracuseStep 2732957 = 1024859) (by norm_num)
theorem B3077021 : Blo 1821612 3077021 := bbase (se 3 (by rfl) ⟨576941, by rfl⟩ : syracuseStep 3077021 = 1153883) (by norm_num)
theorem B4101029 : Blo 1821612 4101029 := bbase (se 4 (by rfl) ⟨384471, by rfl⟩ : syracuseStep 4101029 = 768943) (by norm_num)
theorem B2306981 : Blo 1821612 2306981 := bbase (se 4 (by rfl) ⟨216279, by rfl⟩ : syracuseStep 2306981 = 432559) (by norm_num)
theorem B2732981 : Blo 1821612 2732981 := bbase (se 5 (by rfl) ⟨128108, by rfl⟩ : syracuseStep 2732981 = 256217) (by norm_num)
theorem B2733005 : Blo 1821612 2733005 := bbase (se 3 (by rfl) ⟨512438, by rfl⟩ : syracuseStep 2733005 = 1024877) (by norm_num)
theorem B59110357 : Blo 1821612 59110357 := bbase (se 7 (by rfl) ⟨692699, by rfl⟩ : syracuseStep 59110357 = 1385399) (by norm_num)
theorem B2077661 : Blo 1821612 2077661 := bbase (se 3 (by rfl) ⟨389561, by rfl⟩ : syracuseStep 2077661 = 779123) (by norm_num)
theorem B2307037 : Blo 1821612 2307037 := bbase (se 3 (by rfl) ⟨432569, by rfl⟩ : syracuseStep 2307037 = 865139) (by norm_num)
theorem B2733029 : Blo 1821612 2733029 := bbase (se 4 (by rfl) ⟨256221, by rfl⟩ : syracuseStep 2733029 = 512443) (by norm_num)
theorem B1946597 : Blo 1821612 1946597 := bbase (se 4 (by rfl) ⟨182493, by rfl⟩ : syracuseStep 1946597 = 364987) (by norm_num)
theorem B4101101 : Blo 1821612 4101101 := bbase (se 3 (by rfl) ⟨768956, by rfl⟩ : syracuseStep 4101101 = 1537913) (by norm_num)
theorem B9229301 : Blo 1821612 9229301 := bbase (se 5 (by rfl) ⟨432623, by rfl⟩ : syracuseStep 9229301 = 865247) (by norm_num)
theorem B2733053 : Blo 1821612 2733053 := bbase (se 3 (by rfl) ⟨512447, by rfl⟩ : syracuseStep 2733053 = 1024895) (by norm_num)
theorem B6149141 : Blo 1821612 6149141 := bbase (se 6 (by rfl) ⟨144120, by rfl⟩ : syracuseStep 6149141 = 288241) (by norm_num)
theorem B2077717 : Blo 1821612 2077717 := bbase (se 6 (by rfl) ⟨48696, by rfl⟩ : syracuseStep 2077717 = 97393) (by norm_num)
theorem B2733077 : Blo 1821612 2733077 := bbase (se 6 (by rfl) ⟨64056, by rfl⟩ : syracuseStep 2733077 = 128113) (by norm_num)
theorem B3077149 : Blo 1821612 3077149 := bbase (se 3 (by rfl) ⟨576965, by rfl⟩ : syracuseStep 3077149 = 1153931) (by norm_num)
theorem B2733101 : Blo 1821612 2733101 := bbase (se 3 (by rfl) ⟨512456, by rfl⟩ : syracuseStep 2733101 = 1024913) (by norm_num)
theorem B4101173 : Blo 1821612 4101173 := bbase (se 5 (by rfl) ⟨192242, by rfl⟩ : syracuseStep 4101173 = 384485) (by norm_num)
theorem B2307133 : Blo 1821612 2307133 := bbase (se 3 (by rfl) ⟨432587, by rfl⟩ : syracuseStep 2307133 = 865175) (by norm_num)
theorem B2733125 : Blo 1821612 2733125 := bbase (se 4 (by rfl) ⟨256230, by rfl⟩ : syracuseStep 2733125 = 512461) (by norm_num)
theorem B10384469 : Blo 1821612 10384469 := bbase (se 8 (by rfl) ⟨60846, by rfl⟩ : syracuseStep 10384469 = 121693) (by norm_num)
theorem B2593885 : Blo 1821612 2593885 := bbase (se 3 (by rfl) ⟨486353, by rfl⟩ : syracuseStep 2593885 = 972707) (by norm_num)
theorem B2733149 : Blo 1821612 2733149 := bbase (se 3 (by rfl) ⟨512465, by rfl⟩ : syracuseStep 2733149 = 1024931) (by norm_num)
theorem B2733173 : Blo 1821612 2733173 := bbase (se 5 (by rfl) ⟨128117, by rfl⟩ : syracuseStep 2733173 = 256235) (by norm_num)
theorem B3077237 : Blo 1821612 3077237 := bbase (se 5 (by rfl) ⟨144245, by rfl⟩ : syracuseStep 3077237 = 288491) (by norm_num)
theorem B4101245 : Blo 1821612 4101245 := bbase (se 3 (by rfl) ⟨768983, by rfl⟩ : syracuseStep 4101245 = 1537967) (by norm_num)
theorem B2733197 : Blo 1821612 2733197 := bbase (se 3 (by rfl) ⟨512474, by rfl⟩ : syracuseStep 2733197 = 1024949) (by norm_num)
theorem B2733221 : Blo 1821612 2733221 := bbase (se 4 (by rfl) ⟨256239, by rfl⟩ : syracuseStep 2733221 = 512479) (by norm_num)
theorem B2733245 : Blo 1821612 2733245 := bbase (se 3 (by rfl) ⟨512483, by rfl⟩ : syracuseStep 2733245 = 1024967) (by norm_num)
theorem B4101317 : Blo 1821612 4101317 := bbase (se 4 (by rfl) ⟨384498, by rfl⟩ : syracuseStep 4101317 = 768997) (by norm_num)
theorem B2733269 : Blo 1821612 2733269 := bbase (se 7 (by rfl) ⟨32030, by rfl⟩ : syracuseStep 2733269 = 64061) (by norm_num)
theorem B2307305 : Blo 1821612 2307305 := bbase (se 2 (by rfl) ⟨865239, by rfl⟩ : syracuseStep 2307305 = 1730479) (by norm_num)
theorem B2733293 : Blo 1821612 2733293 := bbase (se 3 (by rfl) ⟨512492, by rfl⟩ : syracuseStep 2733293 = 1024985) (by norm_num)
theorem B2733317 : Blo 1821612 2733317 := bbase (se 4 (by rfl) ⟨256248, by rfl⟩ : syracuseStep 2733317 = 512497) (by norm_num)
theorem B4101389 : Blo 1821612 4101389 := bbase (se 3 (by rfl) ⟨769010, by rfl⟩ : syracuseStep 4101389 = 1538021) (by norm_num)
theorem B2733341 : Blo 1821612 2733341 := bbase (se 3 (by rfl) ⟨512501, by rfl⟩ : syracuseStep 2733341 = 1025003) (by norm_num)
theorem B2307361 : Blo 1821612 2307361 := bbase (se 2 (by rfl) ⟨865260, by rfl⟩ : syracuseStep 2307361 = 1730521) (by norm_num)
theorem B2594101 : Blo 1821612 2594101 := bbase (se 5 (by rfl) ⟨121598, by rfl⟩ : syracuseStep 2594101 = 243197) (by norm_num)
theorem B2733365 : Blo 1821612 2733365 := bbase (se 5 (by rfl) ⟨128126, by rfl⟩ : syracuseStep 2733365 = 256253) (by norm_num)
theorem B2733389 : Blo 1821612 2733389 := bbase (se 3 (by rfl) ⟨512510, by rfl⟩ : syracuseStep 2733389 = 1025021) (by norm_num)
theorem B4101461 : Blo 1821612 4101461 := bbase (se 14 (by rfl) ⟨375, by rfl⟩ : syracuseStep 4101461 = 751) (by norm_num)
theorem B2733413 : Blo 1821612 2733413 := bbase (se 4 (by rfl) ⟨256257, by rfl⟩ : syracuseStep 2733413 = 512515) (by norm_num)
theorem B2733437 : Blo 1821612 2733437 := bbase (se 3 (by rfl) ⟨512519, by rfl⟩ : syracuseStep 2733437 = 1025039) (by norm_num)
theorem B2307457 : Blo 1821612 2307457 := bbase (se 2 (by rfl) ⟨865296, by rfl⟩ : syracuseStep 2307457 = 1730593) (by norm_num)
theorem B2733461 : Blo 1821612 2733461 := bbase (se 6 (by rfl) ⟨64065, by rfl⟩ : syracuseStep 2733461 = 128131) (by norm_num)
theorem B4101533 : Blo 1821612 4101533 := bbase (se 3 (by rfl) ⟨769037, by rfl⟩ : syracuseStep 4101533 = 1538075) (by norm_num)
theorem B2733485 : Blo 1821612 2733485 := bbase (se 3 (by rfl) ⟨512528, by rfl⟩ : syracuseStep 2733485 = 1025057) (by norm_num)
theorem B2463149 : Blo 1821612 2463149 := bbase (se 3 (by rfl) ⟨461840, by rfl⟩ : syracuseStep 2463149 = 923681) (by norm_num)
theorem B6149573 : Blo 1821612 6149573 := bbase (se 4 (by rfl) ⟨576522, by rfl⟩ : syracuseStep 6149573 = 1153045) (by norm_num)
theorem B2733509 : Blo 1821612 2733509 := bbase (se 4 (by rfl) ⟨256266, by rfl⟩ : syracuseStep 2733509 = 512533) (by norm_num)
theorem B2733533 : Blo 1821612 2733533 := bbase (se 3 (by rfl) ⟨512537, by rfl⟩ : syracuseStep 2733533 = 1025075) (by norm_num)
theorem B4101605 : Blo 1821612 4101605 := bbase (se 4 (by rfl) ⟨384525, by rfl⟩ : syracuseStep 4101605 = 769051) (by norm_num)
theorem B5191141 : Blo 1821612 5191141 := bbase (se 4 (by rfl) ⟨486669, by rfl⟩ : syracuseStep 5191141 = 973339) (by norm_num)
theorem B2733557 : Blo 1821612 2733557 := bbase (se 5 (by rfl) ⟨128135, by rfl⟩ : syracuseStep 2733557 = 256271) (by norm_num)
theorem B2733581 : Blo 1821612 2733581 := bbase (se 3 (by rfl) ⟨512546, by rfl⟩ : syracuseStep 2733581 = 1025093) (by norm_num)
theorem B2733605 : Blo 1821612 2733605 := bbase (se 4 (by rfl) ⟨256275, by rfl⟩ : syracuseStep 2733605 = 512551) (by norm_num)
theorem B2078245 : Blo 1821612 2078245 := bbase (se 4 (by rfl) ⟨194835, by rfl⟩ : syracuseStep 2078245 = 389671) (by norm_num)
theorem B4101677 : Blo 1821612 4101677 := bbase (se 3 (by rfl) ⟨769064, by rfl⟩ : syracuseStep 4101677 = 1538129) (by norm_num)
theorem B2307629 : Blo 1821612 2307629 := bbase (se 3 (by rfl) ⟨432680, by rfl⟩ : syracuseStep 2307629 = 865361) (by norm_num)
theorem B2733629 : Blo 1821612 2733629 := bbase (se 3 (by rfl) ⟨512555, by rfl⟩ : syracuseStep 2733629 = 1025111) (by norm_num)
theorem B2733653 : Blo 1821612 2733653 := bbase (se 8 (by rfl) ⟨16017, by rfl⟩ : syracuseStep 2733653 = 32035) (by norm_num)
theorem B2307685 : Blo 1821612 2307685 := bbase (se 4 (by rfl) ⟨216345, by rfl⟩ : syracuseStep 2307685 = 432691) (by norm_num)
theorem B2733677 : Blo 1821612 2733677 := bbase (se 3 (by rfl) ⟨512564, by rfl⟩ : syracuseStep 2733677 = 1025129) (by norm_num)
theorem B4101749 : Blo 1821612 4101749 := bbase (se 5 (by rfl) ⟨192269, by rfl⟩ : syracuseStep 4101749 = 384539) (by norm_num)
theorem B2733701 : Blo 1821612 2733701 := bbase (se 4 (by rfl) ⟨256284, by rfl⟩ : syracuseStep 2733701 = 512569) (by norm_num)
theorem B2733725 : Blo 1821612 2733725 := bbase (se 3 (by rfl) ⟨512573, by rfl⟩ : syracuseStep 2733725 = 1025147) (by norm_num)
theorem B2594477 : Blo 1821612 2594477 := bbase (se 3 (by rfl) ⟨486464, by rfl⟩ : syracuseStep 2594477 = 972929) (by norm_num)
theorem B3118765 : Blo 1821612 3118765 := bbase (se 3 (by rfl) ⟨584768, by rfl⟩ : syracuseStep 3118765 = 1169537) (by norm_num)
theorem B2733749 : Blo 1821612 2733749 := bbase (se 5 (by rfl) ⟨128144, by rfl⟩ : syracuseStep 2733749 = 256289) (by norm_num)
theorem B4101821 : Blo 1821612 4101821 := bbase (se 3 (by rfl) ⟨769091, by rfl⟩ : syracuseStep 4101821 = 1538183) (by norm_num)
theorem B2307781 : Blo 1821612 2307781 := bbase (se 4 (by rfl) ⟨216354, by rfl⟩ : syracuseStep 2307781 = 432709) (by norm_num)
theorem B1971913 : Blo 1821612 1971913 := bbase (se 2 (by rfl) ⟨739467, by rfl⟩ : syracuseStep 1971913 = 1478935) (by norm_num)
theorem B2733773 : Blo 1821612 2733773 := bbase (se 3 (by rfl) ⟨512582, by rfl⟩ : syracuseStep 2733773 = 1025165) (by norm_num)
theorem B1947349 : Blo 1821612 1947349 := bbase (se 7 (by rfl) ⟨22820, by rfl⟩ : syracuseStep 1947349 = 45641) (by norm_num)
theorem B2733797 : Blo 1821612 2733797 := bbase (se 4 (by rfl) ⟨256293, by rfl⟩ : syracuseStep 2733797 = 512587) (by norm_num)
theorem B2733821 : Blo 1821612 2733821 := bbase (se 3 (by rfl) ⟨512591, by rfl⟩ : syracuseStep 2733821 = 1025183) (by norm_num)
theorem B4101893 : Blo 1821612 4101893 := bbase (se 4 (by rfl) ⟨384552, by rfl⟩ : syracuseStep 4101893 = 769105) (by norm_num)
theorem B2733845 : Blo 1821612 2733845 := bbase (se 6 (by rfl) ⟨64074, by rfl⟩ : syracuseStep 2733845 = 128149) (by norm_num)
theorem B2733869 : Blo 1821612 2733869 := bbase (se 3 (by rfl) ⟨512600, by rfl⟩ : syracuseStep 2733869 = 1025201) (by norm_num)
theorem B2733893 : Blo 1821612 2733893 := bbase (se 4 (by rfl) ⟨256302, by rfl⟩ : syracuseStep 2733893 = 512605) (by norm_num)
theorem B4101965 : Blo 1821612 4101965 := bbase (se 3 (by rfl) ⟨769118, by rfl⟩ : syracuseStep 4101965 = 1538237) (by norm_num)
theorem B5543765 : Blo 1821612 5543765 := bbase (se 9 (by rfl) ⟨16241, by rfl⟩ : syracuseStep 5543765 = 32483) (by norm_num)
theorem B2733917 : Blo 1821612 2733917 := bbase (se 3 (by rfl) ⟨512609, by rfl⟩ : syracuseStep 2733917 = 1025219) (by norm_num)
theorem B2307953 : Blo 1821612 2307953 := bbase (se 2 (by rfl) ⟨865482, by rfl⟩ : syracuseStep 2307953 = 1730965) (by norm_num)
theorem B6150005 : Blo 1821612 6150005 := bbase (se 5 (by rfl) ⟨288281, by rfl⟩ : syracuseStep 6150005 = 576563) (by norm_num)
theorem B2733941 : Blo 1821612 2733941 := bbase (se 5 (by rfl) ⟨128153, by rfl⟩ : syracuseStep 2733941 = 256307) (by norm_num)
theorem B2733965 : Blo 1821612 2733965 := bbase (se 3 (by rfl) ⟨512618, by rfl⟩ : syracuseStep 2733965 = 1025237) (by norm_num)
theorem B4102037 : Blo 1821612 4102037 := bbase (se 6 (by rfl) ⟨96141, by rfl⟩ : syracuseStep 4102037 = 192283) (by norm_num)
theorem B2733989 : Blo 1821612 2733989 := bbase (se 4 (by rfl) ⟨256311, by rfl⟩ : syracuseStep 2733989 = 512623) (by norm_num)
theorem B2308009 : Blo 1821612 2308009 := bbase (se 2 (by rfl) ⟨865503, by rfl⟩ : syracuseStep 2308009 = 1731007) (by norm_num)
theorem B2734013 : Blo 1821612 2734013 := bbase (se 3 (by rfl) ⟨512627, by rfl⟩ : syracuseStep 2734013 = 1025255) (by norm_num)
theorem B2734037 : Blo 1821612 2734037 := bbase (se 7 (by rfl) ⟨32039, by rfl⟩ : syracuseStep 2734037 = 64079) (by norm_num)
theorem B4102109 : Blo 1821612 4102109 := bbase (se 3 (by rfl) ⟨769145, by rfl⟩ : syracuseStep 4102109 = 1538291) (by norm_num)
theorem B2734061 : Blo 1821612 2734061 := bbase (se 3 (by rfl) ⟨512636, by rfl⟩ : syracuseStep 2734061 = 1025273) (by norm_num)
theorem B2463733 : Blo 1821612 2463733 := bbase (se 5 (by rfl) ⟨115487, by rfl⟩ : syracuseStep 2463733 = 230975) (by norm_num)
theorem B3946493 : Blo 1821612 3946493 := bbase (se 3 (by rfl) ⟨739967, by rfl⟩ : syracuseStep 3946493 = 1479935) (by norm_num)
theorem B1972225 : Blo 1821612 1972225 := bbase (se 2 (by rfl) ⟨739584, by rfl⟩ : syracuseStep 1972225 = 1479169) (by norm_num)
theorem B2734085 : Blo 1821612 2734085 := bbase (se 4 (by rfl) ⟨256320, by rfl⟩ : syracuseStep 2734085 = 512641) (by norm_num)
theorem B2734109 : Blo 1821612 2734109 := bbase (se 3 (by rfl) ⟨512645, by rfl⟩ : syracuseStep 2734109 = 1025291) (by norm_num)
theorem B4102181 : Blo 1821612 4102181 := bbase (se 4 (by rfl) ⟨384579, by rfl⟩ : syracuseStep 4102181 = 769159) (by norm_num)
theorem B2734133 : Blo 1821612 2734133 := bbase (se 5 (by rfl) ⟨128162, by rfl⟩ : syracuseStep 2734133 = 256325) (by norm_num)
theorem B2463797 : Blo 1821612 2463797 := bbase (se 5 (by rfl) ⟨115490, by rfl⟩ : syracuseStep 2463797 = 230981) (by norm_num)
theorem B6920261 : Blo 1821612 6920261 := bbase (se 4 (by rfl) ⟨648774, by rfl⟩ : syracuseStep 6920261 = 1297549) (by norm_num)
theorem B2734157 : Blo 1821612 2734157 := bbase (se 3 (by rfl) ⟨512654, by rfl⟩ : syracuseStep 2734157 = 1025309) (by norm_num)
theorem B2734181 : Blo 1821612 2734181 := bbase (se 4 (by rfl) ⟨256329, by rfl⟩ : syracuseStep 2734181 = 512659) (by norm_num)
theorem B4102253 : Blo 1821612 4102253 := bbase (se 3 (by rfl) ⟨769172, by rfl⟩ : syracuseStep 4102253 = 1538345) (by norm_num)
theorem B2734205 : Blo 1821612 2734205 := bbase (se 3 (by rfl) ⟨512663, by rfl⟩ : syracuseStep 2734205 = 1025327) (by norm_num)
theorem B2734229 : Blo 1821612 2734229 := bbase (se 6 (by rfl) ⟨64083, by rfl⟩ : syracuseStep 2734229 = 128167) (by norm_num)
theorem B2734253 : Blo 1821612 2734253 := bbase (se 3 (by rfl) ⟨512672, by rfl⟩ : syracuseStep 2734253 = 1025345) (by norm_num)
theorem B8755381 : Blo 1821612 8755381 := bbase (se 5 (by rfl) ⟨410408, by rfl⟩ : syracuseStep 8755381 = 820817) (by norm_num)
theorem B4102325 : Blo 1821612 4102325 := bbase (se 5 (by rfl) ⟨192296, by rfl⟩ : syracuseStep 4102325 = 384593) (by norm_num)
theorem B2734277 : Blo 1821612 2734277 := bbase (se 4 (by rfl) ⟨256338, by rfl⟩ : syracuseStep 2734277 = 512677) (by norm_num)
theorem B2734301 : Blo 1821612 2734301 := bbase (se 3 (by rfl) ⟨512681, by rfl⟩ : syracuseStep 2734301 = 1025363) (by norm_num)
theorem B2734325 : Blo 1821612 2734325 := bbase (se 5 (by rfl) ⟨128171, by rfl⟩ : syracuseStep 2734325 = 256343) (by norm_num)
theorem B4102397 : Blo 1821612 4102397 := bbase (se 3 (by rfl) ⟨769199, by rfl⟩ : syracuseStep 4102397 = 1538399) (by norm_num)
theorem B9230597 : Blo 1821612 9230597 := bbase (se 4 (by rfl) ⟨865368, by rfl⟩ : syracuseStep 9230597 = 1730737) (by norm_num)
theorem B2734349 : Blo 1821612 2734349 := bbase (se 3 (by rfl) ⟨512690, by rfl⟩ : syracuseStep 2734349 = 1025381) (by norm_num)
theorem B6150437 : Blo 1821612 6150437 := bbase (se 4 (by rfl) ⟨576603, by rfl⟩ : syracuseStep 6150437 = 1153207) (by norm_num)
theorem B2734373 : Blo 1821612 2734373 := bbase (se 4 (by rfl) ⟨256347, by rfl⟩ : syracuseStep 2734373 = 512695) (by norm_num)
theorem B2734397 : Blo 1821612 2734397 := bbase (se 3 (by rfl) ⟨512699, by rfl⟩ : syracuseStep 2734397 = 1025399) (by norm_num)
theorem B4102469 : Blo 1821612 4102469 := bbase (se 4 (by rfl) ⟨384606, by rfl⟩ : syracuseStep 4102469 = 769213) (by norm_num)
theorem B2496853 : Blo 1821612 2496853 := bbase (se 10 (by rfl) ⟨3657, by rfl⟩ : syracuseStep 2496853 = 7315) (by norm_num)
theorem B2734421 : Blo 1821612 2734421 := bbase (se 10 (by rfl) ⟨4005, by rfl⟩ : syracuseStep 2734421 = 8011) (by norm_num)
theorem B6920549 : Blo 1821612 6920549 := bbase (se 4 (by rfl) ⟨648801, by rfl⟩ : syracuseStep 6920549 = 1297603) (by norm_num)
theorem B2734445 : Blo 1821612 2734445 := bbase (se 3 (by rfl) ⟨512708, by rfl⟩ : syracuseStep 2734445 = 1025417) (by norm_num)
theorem B2734469 : Blo 1821612 2734469 := bbase (se 4 (by rfl) ⟨256356, by rfl⟩ : syracuseStep 2734469 = 512713) (by norm_num)
theorem B4102541 : Blo 1821612 4102541 := bbase (se 3 (by rfl) ⟨769226, by rfl⟩ : syracuseStep 4102541 = 1538453) (by norm_num)
theorem B2079121 : Blo 1821612 2079121 := bbase (se 2 (by rfl) ⟨779670, by rfl⟩ : syracuseStep 2079121 = 1559341) (by norm_num)
theorem B2734493 : Blo 1821612 2734493 := bbase (se 3 (by rfl) ⟨512717, by rfl⟩ : syracuseStep 2734493 = 1025435) (by norm_num)
theorem B2734517 : Blo 1821612 2734517 := bbase (se 5 (by rfl) ⟨128180, by rfl⟩ : syracuseStep 2734517 = 256361) (by norm_num)
theorem B2734541 : Blo 1821612 2734541 := bbase (se 3 (by rfl) ⟨512726, by rfl⟩ : syracuseStep 2734541 = 1025453) (by norm_num)
theorem B4102613 : Blo 1821612 4102613 := bbase (se 7 (by rfl) ⟨48077, by rfl⟩ : syracuseStep 4102613 = 96155) (by norm_num)
theorem B2734565 : Blo 1821612 2734565 := bbase (se 4 (by rfl) ⟨256365, by rfl⟩ : syracuseStep 2734565 = 512731) (by norm_num)
theorem B2218477 : Blo 1821612 2218477 := bbase (se 3 (by rfl) ⟨415964, by rfl⟩ : syracuseStep 2218477 = 831929) (by norm_num)
theorem B17512949 : Blo 1821612 17512949 := bbase (se 5 (by rfl) ⟨820919, by rfl⟩ : syracuseStep 17512949 = 1641839) (by norm_num)
theorem B2734589 : Blo 1821612 2734589 := bbase (se 3 (by rfl) ⟨512735, by rfl⟩ : syracuseStep 2734589 = 1025471) (by norm_num)
theorem B5839381 : Blo 1821612 5839381 := bbase (se 6 (by rfl) ⟨136860, by rfl⟩ : syracuseStep 5839381 = 273721) (by norm_num)
theorem B2734613 : Blo 1821612 2734613 := bbase (se 6 (by rfl) ⟨64092, by rfl⟩ : syracuseStep 2734613 = 128185) (by norm_num)
theorem B4676125 : Blo 1821612 4676125 := bbase (se 3 (by rfl) ⟨876773, by rfl⟩ : syracuseStep 4676125 = 1753547) (by norm_num)
theorem B4102685 : Blo 1821612 4102685 := bbase (se 3 (by rfl) ⟨769253, by rfl⟩ : syracuseStep 4102685 = 1538507) (by norm_num)
theorem B2734637 : Blo 1821612 2734637 := bbase (se 3 (by rfl) ⟨512744, by rfl⟩ : syracuseStep 2734637 = 1025489) (by norm_num)
theorem B2734661 : Blo 1821612 2734661 := bbase (se 4 (by rfl) ⟨256374, by rfl⟩ : syracuseStep 2734661 = 512749) (by norm_num)
theorem B2079313 : Blo 1821612 2079313 := bbase (se 2 (by rfl) ⟨779742, by rfl⟩ : syracuseStep 2079313 = 1559485) (by norm_num)
theorem B5839445 : Blo 1821612 5839445 := bbase (se 8 (by rfl) ⟨34215, by rfl⟩ : syracuseStep 5839445 = 68431) (by norm_num)
theorem B2734685 : Blo 1821612 2734685 := bbase (se 3 (by rfl) ⟨512753, by rfl⟩ : syracuseStep 2734685 = 1025507) (by norm_num)
theorem B4102757 : Blo 1821612 4102757 := bbase (se 4 (by rfl) ⟨384633, by rfl⟩ : syracuseStep 4102757 = 769267) (by norm_num)
theorem B2734709 : Blo 1821612 2734709 := bbase (se 5 (by rfl) ⟨128189, by rfl⟩ : syracuseStep 2734709 = 256379) (by norm_num)
theorem B2734733 : Blo 1821612 2734733 := bbase (se 3 (by rfl) ⟨512762, by rfl⟩ : syracuseStep 2734733 = 1025525) (by norm_num)
theorem B9222821 : Blo 1821612 9222821 := bbase (se 4 (by rfl) ⟨864639, by rfl⟩ : syracuseStep 9222821 = 1729279) (by norm_num)
theorem B2734757 : Blo 1821612 2734757 := bbase (se 4 (by rfl) ⟨256383, by rfl⟩ : syracuseStep 2734757 = 512767) (by norm_num)
theorem B4102829 : Blo 1821612 4102829 := bbase (se 3 (by rfl) ⟨769280, by rfl⟩ : syracuseStep 4102829 = 1538561) (by norm_num)
theorem B2734781 : Blo 1821612 2734781 := bbase (se 3 (by rfl) ⟨512771, by rfl⟩ : syracuseStep 2734781 = 1025543) (by norm_num)
theorem B4381381 : Blo 1821612 4381381 := bbase (se 4 (by rfl) ⟨410754, by rfl⟩ : syracuseStep 4381381 = 821509) (by norm_num)
theorem B6150869 : Blo 1821612 6150869 := bbase (se 7 (by rfl) ⟨72080, by rfl⟩ : syracuseStep 6150869 = 144161) (by norm_num)
theorem B2734805 : Blo 1821612 2734805 := bbase (se 7 (by rfl) ⟨32048, by rfl⟩ : syracuseStep 2734805 = 64097) (by norm_num)
theorem B2734829 : Blo 1821612 2734829 := bbase (se 3 (by rfl) ⟨512780, by rfl⟩ : syracuseStep 2734829 = 1025561) (by norm_num)
theorem B4102901 : Blo 1821612 4102901 := bbase (se 5 (by rfl) ⟨192323, by rfl⟩ : syracuseStep 4102901 = 384647) (by norm_num)
theorem B2734853 : Blo 1821612 2734853 := bbase (se 4 (by rfl) ⟨256392, by rfl⟩ : syracuseStep 2734853 = 512785) (by norm_num)
theorem B2734877 : Blo 1821612 2734877 := bbase (se 3 (by rfl) ⟨512789, by rfl⟩ : syracuseStep 2734877 = 1025579) (by norm_num)
theorem B2734901 : Blo 1821612 2734901 := bbase (se 5 (by rfl) ⟨128198, by rfl⟩ : syracuseStep 2734901 = 256397) (by norm_num)
theorem B4102973 : Blo 1821612 4102973 := bbase (se 3 (by rfl) ⟨769307, by rfl⟩ : syracuseStep 4102973 = 1538615) (by norm_num)
theorem B2734925 : Blo 1821612 2734925 := bbase (se 3 (by rfl) ⟨512798, by rfl⟩ : syracuseStep 2734925 = 1025597) (by norm_num)
theorem B2734949 : Blo 1821612 2734949 := bbase (se 4 (by rfl) ⟨256401, by rfl⟩ : syracuseStep 2734949 = 512803) (by norm_num)
theorem B2734973 : Blo 1821612 2734973 := bbase (se 3 (by rfl) ⟨512807, by rfl⟩ : syracuseStep 2734973 = 1025615) (by norm_num)
theorem B4103045 : Blo 1821612 4103045 := bbase (se 4 (by rfl) ⟨384660, by rfl⟩ : syracuseStep 4103045 = 769321) (by norm_num)
theorem B4610965 : Blo 1821612 4610965 := bbase (se 6 (by rfl) ⟨108069, by rfl⟩ : syracuseStep 4610965 = 216139) (by norm_num)
theorem B2734997 : Blo 1821612 2734997 := bbase (se 6 (by rfl) ⟨64101, by rfl⟩ : syracuseStep 2734997 = 128203) (by norm_num)
theorem B2735021 : Blo 1821612 2735021 := bbase (se 3 (by rfl) ⟨512816, by rfl⟩ : syracuseStep 2735021 = 1025633) (by norm_num)
theorem B2735045 : Blo 1821612 2735045 := bbase (se 4 (by rfl) ⟨256410, by rfl⟩ : syracuseStep 2735045 = 512821) (by norm_num)
theorem B4103117 : Blo 1821612 4103117 := bbase (se 3 (by rfl) ⟨769334, by rfl⟩ : syracuseStep 4103117 = 1538669) (by norm_num)
theorem B2735069 : Blo 1821612 2735069 := bbase (se 3 (by rfl) ⟨512825, by rfl⟩ : syracuseStep 2735069 = 1025651) (by norm_num)
theorem B2735093 : Blo 1821612 2735093 := bbase (se 5 (by rfl) ⟨128207, by rfl⟩ : syracuseStep 2735093 = 256415) (by norm_num)
theorem B4611077 : Blo 1821612 4611077 := bbase (se 4 (by rfl) ⟨432288, by rfl⟩ : syracuseStep 4611077 = 864577) (by norm_num)
theorem B2735117 : Blo 1821612 2735117 := bbase (se 3 (by rfl) ⟨512834, by rfl⟩ : syracuseStep 2735117 = 1025669) (by norm_num)
theorem B2735141 : Blo 1821612 2735141 := bbase (se 4 (by rfl) ⟨256419, by rfl⟩ : syracuseStep 2735141 = 512839) (by norm_num)
theorem B3693613 : Blo 1821612 3693613 := bbase (se 3 (by rfl) ⟨692552, by rfl⟩ : syracuseStep 3693613 = 1385105) (by norm_num)
theorem B2595901 : Blo 1821612 2595901 := bbase (se 3 (by rfl) ⟨486731, by rfl⟩ : syracuseStep 2595901 = 973463) (by norm_num)
theorem B2735165 : Blo 1821612 2735165 := bbase (se 3 (by rfl) ⟨512843, by rfl⟩ : syracuseStep 2735165 = 1025687) (by norm_num)
theorem B2735189 : Blo 1821612 2735189 := bbase (se 8 (by rfl) ⟨16026, by rfl⟩ : syracuseStep 2735189 = 32053) (by norm_num)
theorem B2735213 : Blo 1821612 2735213 := bbase (se 3 (by rfl) ⟨512852, by rfl⟩ : syracuseStep 2735213 = 1025705) (by norm_num)
theorem B6151301 : Blo 1821612 6151301 := bbase (se 4 (by rfl) ⟨576684, by rfl⟩ : syracuseStep 6151301 = 1153369) (by norm_num)
theorem B2735237 : Blo 1821612 2735237 := bbase (se 4 (by rfl) ⟨256428, by rfl⟩ : syracuseStep 2735237 = 512857) (by norm_num)
theorem B2735261 : Blo 1821612 2735261 := bbase (se 3 (by rfl) ⟨512861, by rfl⟩ : syracuseStep 2735261 = 1025723) (by norm_num)
theorem B2735285 : Blo 1821612 2735285 := bbase (se 5 (by rfl) ⟨128216, by rfl⟩ : syracuseStep 2735285 = 256433) (by norm_num)
theorem B4611269 : Blo 1821612 4611269 := bbase (se 4 (by rfl) ⟨432306, by rfl⟩ : syracuseStep 4611269 = 864613) (by norm_num)
theorem B2735309 : Blo 1821612 2735309 := bbase (se 3 (by rfl) ⟨512870, by rfl⟩ : syracuseStep 2735309 = 1025741) (by norm_num)
theorem B2735333 : Blo 1821612 2735333 := bbase (se 4 (by rfl) ⟨256437, by rfl⟩ : syracuseStep 2735333 = 512875) (by norm_num)
theorem B2735357 : Blo 1821612 2735357 := bbase (se 3 (by rfl) ⟨512879, by rfl⟩ : syracuseStep 2735357 = 1025759) (by norm_num)
theorem B2735381 : Blo 1821612 2735381 := bbase (se 6 (by rfl) ⟨64110, by rfl⟩ : syracuseStep 2735381 = 128221) (by norm_num)
theorem B2735405 : Blo 1821612 2735405 := bbase (se 3 (by rfl) ⟨512888, by rfl⟩ : syracuseStep 2735405 = 1025777) (by norm_num)
theorem B23362901 : Blo 1821612 23362901 := bbase (se 11 (by rfl) ⟨17111, by rfl⟩ : syracuseStep 23362901 = 34223) (by norm_num)
theorem B3890605 : Blo 1821612 3890605 := bbase (se 3 (by rfl) ⟨729488, by rfl⟩ : syracuseStep 3890605 = 1458977) (by norm_num)
theorem B6921733 : Blo 1821612 6921733 := bbase (se 4 (by rfl) ⟨648912, by rfl⟩ : syracuseStep 6921733 = 1297825) (by norm_num)
theorem B9231893 : Blo 1821612 9231893 := bbase (se 6 (by rfl) ⟨216372, by rfl⟩ : syracuseStep 9231893 = 432745) (by norm_num)
theorem B4611613 : Blo 1821612 4611613 := bbase (se 3 (by rfl) ⟨864677, by rfl⟩ : syracuseStep 4611613 = 1729355) (by norm_num)
theorem B6151733 : Blo 1821612 6151733 := bbase (se 5 (by rfl) ⟨288362, by rfl⟩ : syracuseStep 6151733 = 576725) (by norm_num)
theorem B15572533 : Blo 1821612 15572533 := bbase (se 5 (by rfl) ⟨729962, by rfl⟩ : syracuseStep 15572533 = 1459925) (by norm_num)
theorem B16621141 : Blo 1821612 16621141 := bbase (se 8 (by rfl) ⟨97389, by rfl⟩ : syracuseStep 16621141 = 194779) (by norm_num)
theorem B20766293 : Blo 1821612 20766293 := bbase (se 8 (by rfl) ⟨121677, by rfl⟩ : syracuseStep 20766293 = 243355) (by norm_num)
theorem B4611725 : Blo 1821612 4611725 := bbase (se 3 (by rfl) ⟨864698, by rfl⟩ : syracuseStep 4611725 = 1729397) (by norm_num)
theorem B2596493 : Blo 1821612 2596493 := bbase (se 3 (by rfl) ⟨486842, by rfl⟩ : syracuseStep 2596493 = 973685) (by norm_num)
theorem B31571669 : Blo 1821612 31571669 := bbase (se 7 (by rfl) ⟨369980, by rfl⟩ : syracuseStep 31571669 = 739961) (by norm_num)
theorem B6922037 : Blo 1821612 6922037 := bbase (se 5 (by rfl) ⟨324470, by rfl⟩ : syracuseStep 6922037 = 648941) (by norm_num)
theorem B4611917 : Blo 1821612 4611917 := bbase (se 3 (by rfl) ⟨864734, by rfl⟩ : syracuseStep 4611917 = 1729469) (by norm_num)
theorem B9224117 : Blo 1821612 9224117 := bbase (se 5 (by rfl) ⟨432380, by rfl⟩ : syracuseStep 9224117 = 864761) (by norm_num)
theorem B6152165 : Blo 1821612 6152165 := bbase (se 4 (by rfl) ⟨576765, by rfl⟩ : syracuseStep 6152165 = 1153531) (by norm_num)
theorem B14786549 : Blo 1821612 14786549 := bbase (se 5 (by rfl) ⟨693119, by rfl⟩ : syracuseStep 14786549 = 1386239) (by norm_num)
theorem B2629633 : Blo 1821612 2629633 := bstep (se 2 (by rfl) ⟨986112, by rfl⟩ : syracuseStep 2629633 = 1972225) B1972225
theorem B4612099 : Blo 1821612 4612099 := bstep (se 1 (by rfl) ⟨3459074, by rfl⟩ : syracuseStep 4612099 = 6918149) B6918149
theorem B8314915 : Blo 1821612 8314915 := bstep (se 1 (by rfl) ⟨6236186, by rfl⟩ : syracuseStep 8314915 = 12472373) B12472373
theorem B6152273 : Blo 1821612 6152273 := bstep (se 2 (by rfl) ⟨2307102, by rfl⟩ : syracuseStep 6152273 = 4614205) B4614205
theorem B6570125 : Blo 1821612 6570125 := bstep (se 3 (by rfl) ⟨1231898, by rfl⟩ : syracuseStep 6570125 = 2463797) B2463797
theorem B4612241 : Blo 1821612 4612241 := bstep (se 2 (by rfl) ⟨1729590, by rfl⟩ : syracuseStep 4612241 = 3459181) B3459181
theorem B11673841 : Blo 1821612 11673841 := bstep (se 2 (by rfl) ⟨4377690, by rfl⟩ : syracuseStep 11673841 = 8755381) B8755381
theorem B8315299 : Blo 1821612 8315299 := bstep (se 1 (by rfl) ⟨6236474, by rfl⟩ : syracuseStep 8315299 = 12472949) B12472949
theorem B3891665 : Blo 1821612 3891665 := bstep (se 2 (by rfl) ⟨1459374, by rfl⟩ : syracuseStep 3891665 = 2918749) B2918749
theorem B5841443 : Blo 1821612 5841443 := bstep (se 1 (by rfl) ⟨4381082, by rfl⟩ : syracuseStep 5841443 = 8762165) B8762165
theorem B6152813 : Blo 1821612 6152813 := bstep (se 3 (by rfl) ⟨1153652, by rfl⟩ : syracuseStep 6152813 = 2307305) B2307305
theorem B11993741 : Blo 1821612 11993741 := bstep (se 3 (by rfl) ⟨2248826, by rfl⟩ : syracuseStep 11993741 = 4497653) B4497653
theorem B2957969 : Blo 1821612 2957969 := bstep (se 2 (by rfl) ⟨1109238, by rfl⟩ : syracuseStep 2957969 = 2218477) B2218477
theorem B6152867 : Blo 1821612 6152867 := bstep (se 1 (by rfl) ⟨4614650, by rfl⟩ : syracuseStep 6152867 = 9229301) B9229301
theorem B6234833 : Blo 1821612 6234833 := bstep (se 2 (by rfl) ⟨2338062, by rfl⟩ : syracuseStep 6234833 = 4676125) B4676125
theorem B6922979 : Blo 1821612 6922979 := bstep (se 1 (by rfl) ⟨5192234, by rfl⟩ : syracuseStep 6922979 = 10384469) B10384469
theorem B6153137 : Blo 1821612 6153137 := bstep (se 2 (by rfl) ⟨2307426, by rfl⟩ : syracuseStep 6153137 = 4614853) B4614853
theorem B2671603 : Blo 1821612 2671603 := bstep (se 1 (by rfl) ⟨2003702, by rfl⟩ : syracuseStep 2671603 = 4007405) B4007405
theorem B9225251 : Blo 1821612 9225251 := bstep (se 1 (by rfl) ⟨6918938, by rfl⟩ : syracuseStep 9225251 = 13837877) B13837877
theorem B9847921 : Blo 1821612 9847921 := bstep (se 2 (by rfl) ⟨3692970, by rfl⟩ : syracuseStep 9847921 = 7385941) B7385941
theorem B4613233 : Blo 1821612 4613233 := bstep (se 2 (by rfl) ⟨1729962, by rfl⟩ : syracuseStep 4613233 = 3459925) B3459925
theorem B3695825 : Blo 1821612 3695825 := bstep (se 2 (by rfl) ⟨1385934, by rfl⟩ : syracuseStep 3695825 = 2771869) B2771869
theorem B4678865 : Blo 1821612 4678865 := bstep (se 2 (by rfl) ⟨1754574, by rfl⟩ : syracuseStep 4678865 = 3509149) B3509149
theorem B3695843 : Blo 1821612 3695843 := bstep (se 1 (by rfl) ⟨2771882, by rfl⟩ : syracuseStep 3695843 = 5543765) B5543765
theorem B2049331 : Blo 1821612 2049331 := bstep (se 1 (by rfl) ⟨1536998, by rfl⟩ : syracuseStep 2049331 = 3073997) B3073997
theorem B17753413 : Blo 1821612 17753413 := bstep (se 4 (by rfl) ⟨1664382, by rfl⟩ : syracuseStep 17753413 = 3328765) B3328765
theorem B2770289 : Blo 1821612 2770289 := bstep (se 2 (by rfl) ⟨1038858, by rfl⟩ : syracuseStep 2770289 = 2077717) B2077717
theorem B4613507 : Blo 1821612 4613507 := bstep (se 1 (by rfl) ⟨3460130, by rfl⟩ : syracuseStep 4613507 = 6920261) B6920261
theorem B4924817 : Blo 1821612 4924817 := bstep (se 2 (by rfl) ⟨1846806, by rfl⟩ : syracuseStep 4924817 = 3693613) B3693613
theorem B3458467 : Blo 1821612 3458467 := bstep (se 1 (by rfl) ⟨2593850, by rfl⟩ : syracuseStep 3458467 = 5187701) B5187701
theorem B2049475 : Blo 1821612 2049475 := bstep (se 1 (by rfl) ⟨1537106, by rfl⟩ : syracuseStep 2049475 = 3074213) B3074213
theorem B6153677 : Blo 1821612 6153677 := bstep (se 3 (by rfl) ⟨1153814, by rfl⟩ : syracuseStep 6153677 = 2307629) B2307629
theorem B3458513 : Blo 1821612 3458513 := bstep (se 2 (by rfl) ⟨1296942, by rfl⟩ : syracuseStep 3458513 = 2593885) B2593885
theorem B6153731 : Blo 1821612 6153731 := bstep (se 1 (by rfl) ⟨4615298, by rfl⟩ : syracuseStep 6153731 = 9230597) B9230597
theorem B4613699 : Blo 1821612 4613699 := bstep (se 1 (by rfl) ⟨3460274, by rfl⟩ : syracuseStep 4613699 = 6920549) B6920549
theorem B10380869 : Blo 1821612 10380869 := bstep (se 4 (by rfl) ⟨973206, by rfl⟩ : syracuseStep 10380869 = 1946413) B1946413
theorem B2049619 : Blo 1821612 2049619 := bstep (se 1 (by rfl) ⟨1537214, by rfl⟩ : syracuseStep 2049619 = 3074429) B3074429
theorem B6923981 : Blo 1821612 6923981 := bstep (se 3 (by rfl) ⟨1298246, by rfl⟩ : syracuseStep 6923981 = 2596493) B2596493
theorem B2049763 : Blo 1821612 2049763 := bstep (se 1 (by rfl) ⟨1537322, by rfl⟩ : syracuseStep 2049763 = 3074645) B3074645
theorem B3892963 : Blo 1821612 3892963 := bstep (se 1 (by rfl) ⟨2919722, by rfl⟩ : syracuseStep 3892963 = 5839445) B5839445
theorem B3458801 : Blo 1821612 3458801 := bstep (se 2 (by rfl) ⟨1297050, by rfl⟩ : syracuseStep 3458801 = 2594101) B2594101
theorem B23365361 : Blo 1821612 23365361 := bstep (se 2 (by rfl) ⟨8762010, by rfl⟩ : syracuseStep 23365361 = 17524021) B17524021
theorem B6154001 : Blo 1821612 6154001 := bstep (se 2 (by rfl) ⟨2307750, by rfl⟩ : syracuseStep 6154001 = 4615501) B4615501
theorem B3327779 : Blo 1821612 3327779 := bstep (se 1 (by rfl) ⟨2495834, by rfl⟩ : syracuseStep 3327779 = 4991669) B4991669
theorem B9226061 : Blo 1821612 9226061 := bstep (se 3 (by rfl) ⟨1729886, by rfl⟩ : syracuseStep 9226061 = 3459773) B3459773
theorem B2049907 : Blo 1821612 2049907 := bstep (se 1 (by rfl) ⟨1537430, by rfl⟩ : syracuseStep 2049907 = 3074861) B3074861
theorem B20760461 : Blo 1821612 20760461 := bstep (se 3 (by rfl) ⟨3892586, by rfl⟩ : syracuseStep 20760461 = 7785173) B7785173
theorem B5187473 : Blo 1821612 5187473 := bstep (se 2 (by rfl) ⟨1945302, by rfl⟩ : syracuseStep 5187473 = 3890605) B3890605
theorem B2918339 : Blo 1821612 2918339 := bstep (se 1 (by rfl) ⟨2188754, by rfl⟩ : syracuseStep 2918339 = 4377509) B4377509
theorem B11241413 : Blo 1821612 11241413 := bstep (se 4 (by rfl) ⟨1053882, by rfl⟩ : syracuseStep 11241413 = 2107765) B2107765
theorem B3074017 : Blo 1821612 3074017 := bstep (se 2 (by rfl) ⟨1152756, by rfl⟩ : syracuseStep 3074017 = 2305513) B2305513
theorem B3074051 : Blo 1821612 3074051 := bstep (se 1 (by rfl) ⟨2305538, by rfl⟩ : syracuseStep 3074051 = 4611077) B4611077
theorem B2050051 : Blo 1821612 2050051 := bstep (se 1 (by rfl) ⟨1537538, by rfl⟩ : syracuseStep 2050051 = 3075077) B3075077
theorem B2770993 : Blo 1821612 2770993 := bstep (se 2 (by rfl) ⟨1039122, by rfl⟩ : syracuseStep 2770993 = 2078245) B2078245
theorem B7784525 : Blo 1821612 7784525 := bstep (se 3 (by rfl) ⟨1459598, by rfl⟩ : syracuseStep 7784525 = 2919197) B2919197
theorem B22161521 : Blo 1821612 22161521 := bstep (se 2 (by rfl) ⟨8310570, by rfl⟩ : syracuseStep 22161521 = 16621141) B16621141
theorem B3074179 : Blo 1821612 3074179 := bstep (se 1 (by rfl) ⟨2305634, by rfl⟩ : syracuseStep 3074179 = 4611269) B4611269
theorem B2918531 : Blo 1821612 2918531 := bstep (se 1 (by rfl) ⟨2188898, by rfl⟩ : syracuseStep 2918531 = 4377797) B4377797
theorem B2050195 : Blo 1821612 2050195 := bstep (se 1 (by rfl) ⟨1537646, by rfl⟩ : syracuseStep 2050195 = 3075293) B3075293
theorem B15575267 : Blo 1821612 15575267 := bstep (se 1 (by rfl) ⟨11681450, by rfl⟩ : syracuseStep 15575267 = 23362901) B23362901
theorem B10381553 : Blo 1821612 10381553 := bstep (se 2 (by rfl) ⟨3893082, by rfl⟩ : syracuseStep 10381553 = 7786165) B7786165
theorem B3074321 : Blo 1821612 3074321 := bstep (se 2 (by rfl) ⟨1152870, by rfl⟩ : syracuseStep 3074321 = 2305741) B2305741
theorem B2050339 : Blo 1821612 2050339 := bstep (se 1 (by rfl) ⟨1537754, by rfl⟩ : syracuseStep 2050339 = 3075509) B3075509
theorem B6154541 : Blo 1821612 6154541 := bstep (se 3 (by rfl) ⟨1153976, by rfl⟩ : syracuseStep 6154541 = 2307953) B2307953
theorem B6154595 : Blo 1821612 6154595 := bstep (se 1 (by rfl) ⟨4615946, by rfl⟩ : syracuseStep 6154595 = 9231893) B9231893
theorem B3074449 : Blo 1821612 3074449 := bstep (se 2 (by rfl) ⟨1152918, by rfl⟩ : syracuseStep 3074449 = 2305837) B2305837
theorem B3074483 : Blo 1821612 3074483 := bstep (se 1 (by rfl) ⟨2305862, by rfl⟩ : syracuseStep 3074483 = 4611725) B4611725
theorem B2050483 : Blo 1821612 2050483 := bstep (se 1 (by rfl) ⟨1537862, by rfl⟩ : syracuseStep 2050483 = 3075725) B3075725
theorem B3459523 : Blo 1821612 3459523 := bstep (se 1 (by rfl) ⟨2594642, by rfl⟩ : syracuseStep 3459523 = 5189285) B5189285
theorem B21047779 : Blo 1821612 21047779 := bstep (se 1 (by rfl) ⟨15785834, by rfl⟩ : syracuseStep 21047779 = 31571669) B31571669
theorem B4614641 : Blo 1821612 4614641 := bstep (se 2 (by rfl) ⟨1730490, by rfl⟩ : syracuseStep 4614641 = 3460981) B3460981
theorem B4614691 : Blo 1821612 4614691 := bstep (se 1 (by rfl) ⟨3461018, by rfl⟩ : syracuseStep 4614691 = 6922037) B6922037
theorem B3074611 : Blo 1821612 3074611 := bstep (se 1 (by rfl) ⟨2305958, by rfl⟩ : syracuseStep 3074611 = 4611917) B4611917
theorem B2050627 : Blo 1821612 2050627 := bstep (se 1 (by rfl) ⟨1537970, by rfl⟩ : syracuseStep 2050627 = 3075941) B3075941
theorem B5540429 : Blo 1821612 5540429 := bstep (se 3 (by rfl) ⟨1038830, by rfl⟩ : syracuseStep 5540429 = 2077661) B2077661
theorem B3508817 : Blo 1821612 3508817 := bstep (se 2 (by rfl) ⟨1315806, by rfl⟩ : syracuseStep 3508817 = 2631613) B2631613
theorem B9857699 : Blo 1821612 9857699 := bstep (se 1 (by rfl) ⟨7393274, by rfl⟩ : syracuseStep 9857699 = 14786549) B14786549
theorem B4614833 : Blo 1821612 4614833 := bstep (se 2 (by rfl) ⟨1730562, by rfl⟩ : syracuseStep 4614833 = 3461125) B3461125
theorem B3074753 : Blo 1821612 3074753 := bstep (se 2 (by rfl) ⟨1153032, by rfl⟩ : syracuseStep 3074753 = 2306065) B2306065
theorem B2050771 : Blo 1821612 2050771 := bstep (se 1 (by rfl) ⟨1538078, by rfl⟩ : syracuseStep 2050771 = 3076157) B3076157
theorem B4098833 : Blo 1821612 4098833 := bstep (se 2 (by rfl) ⟨1537062, by rfl⟩ : syracuseStep 4098833 = 3074125) B3074125
theorem B4098851 : Blo 1821612 4098851 := bstep (se 1 (by rfl) ⟨3074138, by rfl⟩ : syracuseStep 4098851 = 6148277) B6148277
theorem B3074881 : Blo 1821612 3074881 := bstep (se 2 (by rfl) ⟨1153080, by rfl⟩ : syracuseStep 3074881 = 2306161) B2306161
theorem B3074915 : Blo 1821612 3074915 := bstep (se 1 (by rfl) ⟨2306186, by rfl⟩ : syracuseStep 3074915 = 4612373) B4612373
theorem B2050915 : Blo 1821612 2050915 := bstep (se 1 (by rfl) ⟨1538186, by rfl⟩ : syracuseStep 2050915 = 3076373) B3076373
theorem B3459971 : Blo 1821612 3459971 := bstep (se 1 (by rfl) ⟨2594978, by rfl⟩ : syracuseStep 3459971 = 5189957) B5189957
theorem B42077069 : Blo 1821612 42077069 := bstep (se 3 (by rfl) ⟨7889450, by rfl⟩ : syracuseStep 42077069 = 15778901) B15778901
theorem B3894193 : Blo 1821612 3894193 := bstep (se 2 (by rfl) ⟨1460322, by rfl⟩ : syracuseStep 3894193 = 2920645) B2920645
theorem B1821619 : Blo 1821612 1821619 := bstep (se 1 (by rfl) ⟨1366214, by rfl⟩ : syracuseStep 1821619 = 2732429) B2732429
theorem B1821635 : Blo 1821612 1821635 := bstep (se 1 (by rfl) ⟨1366226, by rfl⟩ : syracuseStep 1821635 = 2732453) B2732453
theorem B1821651 : Blo 1821612 1821651 := bstep (se 1 (by rfl) ⟨1366238, by rfl⟩ : syracuseStep 1821651 = 2732477) B2732477
theorem B1821667 : Blo 1821612 1821667 := bstep (se 1 (by rfl) ⟨1366250, by rfl⟩ : syracuseStep 1821667 = 2732501) B2732501
theorem B3075043 : Blo 1821612 3075043 := bstep (se 1 (by rfl) ⟨2306282, by rfl⟩ : syracuseStep 3075043 = 4612565) B4612565
theorem B14978033 : Blo 1821612 14978033 := bstep (se 2 (by rfl) ⟨5616762, by rfl⟩ : syracuseStep 14978033 = 11233525) B11233525
theorem B1821683 : Blo 1821612 1821683 := bstep (se 1 (by rfl) ⟨1366262, by rfl⟩ : syracuseStep 1821683 = 2732525) B2732525
theorem B2051059 : Blo 1821612 2051059 := bstep (se 1 (by rfl) ⟨1538294, by rfl⟩ : syracuseStep 2051059 = 3076589) B3076589
theorem B1821699 : Blo 1821612 1821699 := bstep (se 1 (by rfl) ⟨1366274, by rfl⟩ : syracuseStep 1821699 = 2732549) B2732549
theorem B1821715 : Blo 1821612 1821715 := bstep (se 1 (by rfl) ⟨1366286, by rfl⟩ : syracuseStep 1821715 = 2732573) B2732573
theorem B1821731 : Blo 1821612 1821731 := bstep (se 1 (by rfl) ⟨1366298, by rfl⟩ : syracuseStep 1821731 = 2732597) B2732597
theorem B4099121 : Blo 1821612 4099121 := bstep (se 2 (by rfl) ⟨1537170, by rfl⟩ : syracuseStep 4099121 = 3074341) B3074341
theorem B1821747 : Blo 1821612 1821747 := bstep (se 1 (by rfl) ⟨1366310, by rfl⟩ : syracuseStep 1821747 = 2732621) B2732621
theorem B1821763 : Blo 1821612 1821763 := bstep (se 1 (by rfl) ⟨1366322, by rfl⟩ : syracuseStep 1821763 = 2732645) B2732645
theorem B4099139 : Blo 1821612 4099139 := bstep (se 1 (by rfl) ⟨3074354, by rfl⟩ : syracuseStep 4099139 = 6148709) B6148709
theorem B2919505 : Blo 1821612 2919505 := bstep (se 2 (by rfl) ⟨1094814, by rfl⟩ : syracuseStep 2919505 = 2189629) B2189629
theorem B1821779 : Blo 1821612 1821779 := bstep (se 1 (by rfl) ⟨1366334, by rfl⟩ : syracuseStep 1821779 = 2732669) B2732669
theorem B1821795 : Blo 1821612 1821795 := bstep (se 1 (by rfl) ⟨1366346, by rfl⟩ : syracuseStep 1821795 = 2732693) B2732693
theorem B6237283 : Blo 1821612 6237283 := bstep (se 1 (by rfl) ⟨4677962, by rfl⟩ : syracuseStep 6237283 = 9355925) B9355925
theorem B3075185 : Blo 1821612 3075185 := bstep (se 2 (by rfl) ⟨1153194, by rfl⟩ : syracuseStep 3075185 = 2306389) B2306389
theorem B3329137 : Blo 1821612 3329137 := bstep (se 2 (by rfl) ⟨1248426, by rfl⟩ : syracuseStep 3329137 = 2496853) B2496853
theorem B1821811 : Blo 1821612 1821811 := bstep (se 1 (by rfl) ⟨1366358, by rfl⟩ : syracuseStep 1821811 = 2732717) B2732717
theorem B1821827 : Blo 1821612 1821827 := bstep (se 1 (by rfl) ⟨1366370, by rfl⟩ : syracuseStep 1821827 = 2732741) B2732741
theorem B2051203 : Blo 1821612 2051203 := bstep (se 1 (by rfl) ⟨1538402, by rfl⟩ : syracuseStep 2051203 = 3076805) B3076805
theorem B1821843 : Blo 1821612 1821843 := bstep (se 1 (by rfl) ⟨1366382, by rfl⟩ : syracuseStep 1821843 = 2732765) B2732765
theorem B1821859 : Blo 1821612 1821859 := bstep (se 1 (by rfl) ⟨1366394, by rfl⟩ : syracuseStep 1821859 = 2732789) B2732789
theorem B3460259 : Blo 1821612 3460259 := bstep (se 1 (by rfl) ⟨2595194, by rfl⟩ : syracuseStep 3460259 = 5190389) B5190389
theorem B1821875 : Blo 1821612 1821875 := bstep (se 1 (by rfl) ⟨1366406, by rfl⟩ : syracuseStep 1821875 = 2732813) B2732813
theorem B2772161 : Blo 1821612 2772161 := bstep (se 2 (by rfl) ⟨1039560, by rfl⟩ : syracuseStep 2772161 = 2079121) B2079121
theorem B1821891 : Blo 1821612 1821891 := bstep (se 1 (by rfl) ⟨1366418, by rfl⟩ : syracuseStep 1821891 = 2732837) B2732837
theorem B1821907 : Blo 1821612 1821907 := bstep (se 1 (by rfl) ⟨1366430, by rfl⟩ : syracuseStep 1821907 = 2732861) B2732861
theorem B1821923 : Blo 1821612 1821923 := bstep (se 1 (by rfl) ⟨1366442, by rfl⟩ : syracuseStep 1821923 = 2732885) B2732885
theorem B3075313 : Blo 1821612 3075313 := bstep (se 2 (by rfl) ⟨1153242, by rfl⟩ : syracuseStep 3075313 = 2306485) B2306485
theorem B1821939 : Blo 1821612 1821939 := bstep (se 1 (by rfl) ⟨1366454, by rfl⟩ : syracuseStep 1821939 = 2732909) B2732909
theorem B1821955 : Blo 1821612 1821955 := bstep (se 1 (by rfl) ⟨1366466, by rfl⟩ : syracuseStep 1821955 = 2732933) B2732933
theorem B1821971 : Blo 1821612 1821971 := bstep (se 1 (by rfl) ⟨1366478, by rfl⟩ : syracuseStep 1821971 = 2732957) B2732957
theorem B3075347 : Blo 1821612 3075347 := bstep (se 1 (by rfl) ⟨2306510, by rfl⟩ : syracuseStep 3075347 = 4613021) B4613021
theorem B2051347 : Blo 1821612 2051347 := bstep (se 1 (by rfl) ⟨1538510, by rfl⟩ : syracuseStep 2051347 = 3077021) B3077021
theorem B1821987 : Blo 1821612 1821987 := bstep (se 1 (by rfl) ⟨1366490, by rfl⟩ : syracuseStep 1821987 = 2732981) B2732981
theorem B1822003 : Blo 1821612 1822003 := bstep (se 1 (by rfl) ⟨1366502, by rfl⟩ : syracuseStep 1822003 = 2733005) B2733005
theorem B1822019 : Blo 1821612 1822019 := bstep (se 1 (by rfl) ⟨1366514, by rfl⟩ : syracuseStep 1822019 = 2733029) B2733029
theorem B5188931 : Blo 1821612 5188931 := bstep (se 1 (by rfl) ⟨3891698, by rfl⟩ : syracuseStep 5188931 = 7783397) B7783397
theorem B4099409 : Blo 1821612 4099409 := bstep (se 2 (by rfl) ⟨1537278, by rfl⟩ : syracuseStep 4099409 = 3074557) B3074557
theorem B1822035 : Blo 1821612 1822035 := bstep (se 1 (by rfl) ⟨1366526, by rfl⟩ : syracuseStep 1822035 = 2733053) B2733053
theorem B4099427 : Blo 1821612 4099427 := bstep (se 1 (by rfl) ⟨3074570, by rfl⟩ : syracuseStep 4099427 = 6149141) B6149141
theorem B1822051 : Blo 1821612 1822051 := bstep (se 1 (by rfl) ⟨1366538, by rfl⟩ : syracuseStep 1822051 = 2733077) B2733077
theorem B7785841 : Blo 1821612 7785841 := bstep (se 2 (by rfl) ⟨2919690, by rfl⟩ : syracuseStep 7785841 = 5839381) B5839381
theorem B1822067 : Blo 1821612 1822067 := bstep (se 1 (by rfl) ⟨1366550, by rfl⟩ : syracuseStep 1822067 = 2733101) B2733101
theorem B1822083 : Blo 1821612 1822083 := bstep (se 1 (by rfl) ⟨1366562, by rfl⟩ : syracuseStep 1822083 = 2733125) B2733125
theorem B1822099 : Blo 1821612 1822099 := bstep (se 1 (by rfl) ⟨1366574, by rfl⟩ : syracuseStep 1822099 = 2733149) B2733149
theorem B3075475 : Blo 1821612 3075475 := bstep (se 1 (by rfl) ⟨2306606, by rfl⟩ : syracuseStep 3075475 = 4613213) B4613213
theorem B1822115 : Blo 1821612 1822115 := bstep (se 1 (by rfl) ⟨1366586, by rfl⟩ : syracuseStep 1822115 = 2733173) B2733173
theorem B2051491 : Blo 1821612 2051491 := bstep (se 1 (by rfl) ⟨1538618, by rfl⟩ : syracuseStep 2051491 = 3077237) B3077237
theorem B1822131 : Blo 1821612 1822131 := bstep (se 1 (by rfl) ⟨1366598, by rfl⟩ : syracuseStep 1822131 = 2733197) B2733197
theorem B1822147 : Blo 1821612 1822147 := bstep (se 1 (by rfl) ⟨1366610, by rfl⟩ : syracuseStep 1822147 = 2733221) B2733221
theorem B1822163 : Blo 1821612 1822163 := bstep (se 1 (by rfl) ⟨1366622, by rfl⟩ : syracuseStep 1822163 = 2733245) B2733245
theorem B1822179 : Blo 1821612 1822179 := bstep (se 1 (by rfl) ⟨1366634, by rfl⟩ : syracuseStep 1822179 = 2733269) B2733269
theorem B2305523 : Blo 1821612 2305523 := bstep (se 1 (by rfl) ⟨1729142, by rfl⟩ : syracuseStep 2305523 = 3458285) B3458285
theorem B1822195 : Blo 1821612 1822195 := bstep (se 1 (by rfl) ⟨1366646, by rfl⟩ : syracuseStep 1822195 = 2733293) B2733293
theorem B1822211 : Blo 1821612 1822211 := bstep (se 1 (by rfl) ⟨1366658, by rfl⟩ : syracuseStep 1822211 = 2733317) B2733317
theorem B4926989 : Blo 1821612 4926989 := bstep (se 3 (by rfl) ⟨923810, by rfl⟩ : syracuseStep 4926989 = 1847621) B1847621
theorem B2919953 : Blo 1821612 2919953 := bstep (se 2 (by rfl) ⟨1094982, by rfl⟩ : syracuseStep 2919953 = 2189965) B2189965
theorem B1822227 : Blo 1821612 1822227 := bstep (se 1 (by rfl) ⟨1366670, by rfl⟩ : syracuseStep 1822227 = 2733341) B2733341
theorem B3075617 : Blo 1821612 3075617 := bstep (se 2 (by rfl) ⟨1153356, by rfl⟩ : syracuseStep 3075617 = 2306713) B2306713
theorem B1822243 : Blo 1821612 1822243 := bstep (se 1 (by rfl) ⟨1366682, by rfl⟩ : syracuseStep 1822243 = 2733365) B2733365
theorem B1822259 : Blo 1821612 1822259 := bstep (se 1 (by rfl) ⟨1366694, by rfl⟩ : syracuseStep 1822259 = 2733389) B2733389
theorem B1822275 : Blo 1821612 1822275 := bstep (se 1 (by rfl) ⟨1366706, by rfl⟩ : syracuseStep 1822275 = 2733413) B2733413
theorem B5836369 : Blo 1821612 5836369 := bstep (se 2 (by rfl) ⟨2188638, by rfl⟩ : syracuseStep 5836369 = 4377277) B4377277
theorem B1822291 : Blo 1821612 1822291 := bstep (se 1 (by rfl) ⟨1366718, by rfl⟩ : syracuseStep 1822291 = 2733437) B2733437
theorem B1822307 : Blo 1821612 1822307 := bstep (se 1 (by rfl) ⟨1366730, by rfl⟩ : syracuseStep 1822307 = 2733461) B2733461
theorem B4099697 : Blo 1821612 4099697 := bstep (se 2 (by rfl) ⟨1537386, by rfl⟩ : syracuseStep 4099697 = 3074773) B3074773
theorem B1822323 : Blo 1821612 1822323 := bstep (se 1 (by rfl) ⟨1366742, by rfl⟩ : syracuseStep 1822323 = 2733485) B2733485
theorem B4099715 : Blo 1821612 4099715 := bstep (se 1 (by rfl) ⟨3074786, by rfl⟩ : syracuseStep 4099715 = 6149573) B6149573
theorem B1822339 : Blo 1821612 1822339 := bstep (se 1 (by rfl) ⟨1366754, by rfl⟩ : syracuseStep 1822339 = 2733509) B2733509
theorem B4615825 : Blo 1821612 4615825 := bstep (se 2 (by rfl) ⟨1730934, by rfl⟩ : syracuseStep 4615825 = 3461869) B3461869
theorem B1822355 : Blo 1821612 1822355 := bstep (se 1 (by rfl) ⟨1366766, by rfl⟩ : syracuseStep 1822355 = 2733533) B2733533
theorem B3075745 : Blo 1821612 3075745 := bstep (se 2 (by rfl) ⟨1153404, by rfl⟩ : syracuseStep 3075745 = 2306809) B2306809
theorem B1822371 : Blo 1821612 1822371 := bstep (se 1 (by rfl) ⟨1366778, by rfl⟩ : syracuseStep 1822371 = 2733557) B2733557
theorem B10383011 : Blo 1821612 10383011 := bstep (se 1 (by rfl) ⟨7787258, by rfl⟩ : syracuseStep 10383011 = 15574517) B15574517
theorem B1822387 : Blo 1821612 1822387 := bstep (se 1 (by rfl) ⟨1366790, by rfl⟩ : syracuseStep 1822387 = 2733581) B2733581
theorem B1822403 : Blo 1821612 1822403 := bstep (se 1 (by rfl) ⟨1366802, by rfl⟩ : syracuseStep 1822403 = 2733605) B2733605
theorem B3075779 : Blo 1821612 3075779 := bstep (se 1 (by rfl) ⟨2306834, by rfl⟩ : syracuseStep 3075779 = 4613669) B4613669
theorem B23367365 : Blo 1821612 23367365 := bstep (se 4 (by rfl) ⟨2190690, by rfl⟩ : syracuseStep 23367365 = 4381381) B4381381
theorem B1822419 : Blo 1821612 1822419 := bstep (se 1 (by rfl) ⟨1366814, by rfl⟩ : syracuseStep 1822419 = 2733629) B2733629
theorem B1822435 : Blo 1821612 1822435 := bstep (se 1 (by rfl) ⟨1366826, by rfl⟩ : syracuseStep 1822435 = 2733653) B2733653
theorem B1822451 : Blo 1821612 1822451 := bstep (se 1 (by rfl) ⟨1366838, by rfl⟩ : syracuseStep 1822451 = 2733677) B2733677
theorem B1822467 : Blo 1821612 1822467 := bstep (se 1 (by rfl) ⟨1366850, by rfl⟩ : syracuseStep 1822467 = 2733701) B2733701
theorem B1822483 : Blo 1821612 1822483 := bstep (se 1 (by rfl) ⟨1366862, by rfl⟩ : syracuseStep 1822483 = 2733725) B2733725
theorem B1822499 : Blo 1821612 1822499 := bstep (se 1 (by rfl) ⟨1366874, by rfl⟩ : syracuseStep 1822499 = 2733749) B2733749
theorem B1822515 : Blo 1821612 1822515 := bstep (se 1 (by rfl) ⟨1366886, by rfl⟩ : syracuseStep 1822515 = 2733773) B2733773
theorem B1822531 : Blo 1821612 1822531 := bstep (se 1 (by rfl) ⟨1366898, by rfl⟩ : syracuseStep 1822531 = 2733797) B2733797
theorem B3075907 : Blo 1821612 3075907 := bstep (se 1 (by rfl) ⟨2306930, by rfl⟩ : syracuseStep 3075907 = 4613861) B4613861
theorem B6238019 : Blo 1821612 6238019 := bstep (se 1 (by rfl) ⟨4678514, by rfl⟩ : syracuseStep 6238019 = 9357029) B9357029
theorem B5836625 : Blo 1821612 5836625 := bstep (se 2 (by rfl) ⟨2188734, by rfl⟩ : syracuseStep 5836625 = 4377469) B4377469
theorem B1822547 : Blo 1821612 1822547 := bstep (se 1 (by rfl) ⟨1366910, by rfl⟩ : syracuseStep 1822547 = 2733821) B2733821
theorem B1822563 : Blo 1821612 1822563 := bstep (se 1 (by rfl) ⟨1366922, by rfl⟩ : syracuseStep 1822563 = 2733845) B2733845
theorem B6147953 : Blo 1821612 6147953 := bstep (se 2 (by rfl) ⟨2305482, by rfl⟩ : syracuseStep 6147953 = 4610965) B4610965
theorem B1822579 : Blo 1821612 1822579 := bstep (se 1 (by rfl) ⟨1366934, by rfl⟩ : syracuseStep 1822579 = 2733869) B2733869
theorem B1822595 : Blo 1821612 1822595 := bstep (se 1 (by rfl) ⟨1366946, by rfl⟩ : syracuseStep 1822595 = 2733893) B2733893
theorem B4099985 : Blo 1821612 4099985 := bstep (se 2 (by rfl) ⟨1537494, by rfl⟩ : syracuseStep 4099985 = 3074989) B3074989
theorem B1822611 : Blo 1821612 1822611 := bstep (se 1 (by rfl) ⟨1366958, by rfl⟩ : syracuseStep 1822611 = 2733917) B2733917
theorem B4100003 : Blo 1821612 4100003 := bstep (se 1 (by rfl) ⟨3075002, by rfl⟩ : syracuseStep 4100003 = 6150005) B6150005
theorem B1822627 : Blo 1821612 1822627 := bstep (se 1 (by rfl) ⟨1366970, by rfl⟩ : syracuseStep 1822627 = 2733941) B2733941
theorem B1822643 : Blo 1821612 1822643 := bstep (se 1 (by rfl) ⟨1366982, by rfl⟩ : syracuseStep 1822643 = 2733965) B2733965
theorem B1822659 : Blo 1821612 1822659 := bstep (se 1 (by rfl) ⟨1366994, by rfl⟩ : syracuseStep 1822659 = 2733989) B2733989
theorem B5541841 : Blo 1821612 5541841 := bstep (se 2 (by rfl) ⟨2078190, by rfl⟩ : syracuseStep 5541841 = 4156381) B4156381
theorem B3076049 : Blo 1821612 3076049 := bstep (se 2 (by rfl) ⟨1153518, by rfl⟩ : syracuseStep 3076049 = 2307037) B2307037
theorem B1822675 : Blo 1821612 1822675 := bstep (se 1 (by rfl) ⟨1367006, by rfl⟩ : syracuseStep 1822675 = 2734013) B2734013
theorem B1822691 : Blo 1821612 1822691 := bstep (se 1 (by rfl) ⟨1367018, by rfl⟩ : syracuseStep 1822691 = 2734037) B2734037
theorem B19705841 : Blo 1821612 19705841 := bstep (se 2 (by rfl) ⟨7389690, by rfl⟩ : syracuseStep 19705841 = 14779381) B14779381
theorem B1822707 : Blo 1821612 1822707 := bstep (se 1 (by rfl) ⟨1367030, by rfl⟩ : syracuseStep 1822707 = 2734061) B2734061
theorem B1822723 : Blo 1821612 1822723 := bstep (se 1 (by rfl) ⟨1367042, by rfl⟩ : syracuseStep 1822723 = 2734085) B2734085
theorem B1822739 : Blo 1821612 1822739 := bstep (se 1 (by rfl) ⟨1367054, by rfl⟩ : syracuseStep 1822739 = 2734109) B2734109
theorem B1822755 : Blo 1821612 1822755 := bstep (se 1 (by rfl) ⟨1367066, by rfl⟩ : syracuseStep 1822755 = 2734133) B2734133
theorem B1822771 : Blo 1821612 1822771 := bstep (se 1 (by rfl) ⟨1367078, by rfl⟩ : syracuseStep 1822771 = 2734157) B2734157
theorem B1822787 : Blo 1821612 1822787 := bstep (se 1 (by rfl) ⟨1367090, by rfl⟩ : syracuseStep 1822787 = 2734181) B2734181
theorem B3076177 : Blo 1821612 3076177 := bstep (se 2 (by rfl) ⟨1153566, by rfl⟩ : syracuseStep 3076177 = 2307133) B2307133
theorem B3461201 : Blo 1821612 3461201 := bstep (se 2 (by rfl) ⟨1297950, by rfl⟩ : syracuseStep 3461201 = 2595901) B2595901
theorem B1822803 : Blo 1821612 1822803 := bstep (se 1 (by rfl) ⟨1367102, by rfl⟩ : syracuseStep 1822803 = 2734205) B2734205
theorem B1822819 : Blo 1821612 1822819 := bstep (se 1 (by rfl) ⟨1367114, by rfl⟩ : syracuseStep 1822819 = 2734229) B2734229
theorem B5189741 : Blo 1821612 5189741 := bstep (se 3 (by rfl) ⟨973076, by rfl⟩ : syracuseStep 5189741 = 1946153) B1946153
theorem B1822835 : Blo 1821612 1822835 := bstep (se 1 (by rfl) ⟨1367126, by rfl⟩ : syracuseStep 1822835 = 2734253) B2734253
theorem B3076211 : Blo 1821612 3076211 := bstep (se 1 (by rfl) ⟨2307158, by rfl⟩ : syracuseStep 3076211 = 4614317) B4614317
theorem B1822851 : Blo 1821612 1822851 := bstep (se 1 (by rfl) ⟨1367138, by rfl⟩ : syracuseStep 1822851 = 2734277) B2734277
theorem B1847443 : Blo 1821612 1847443 := bstep (se 1 (by rfl) ⟨1385582, by rfl⟩ : syracuseStep 1847443 = 2771165) B2771165
theorem B1822867 : Blo 1821612 1822867 := bstep (se 1 (by rfl) ⟨1367150, by rfl⟩ : syracuseStep 1822867 = 2734301) B2734301
theorem B1822883 : Blo 1821612 1822883 := bstep (se 1 (by rfl) ⟨1367162, by rfl⟩ : syracuseStep 1822883 = 2734325) B2734325
theorem B4100273 : Blo 1821612 4100273 := bstep (se 2 (by rfl) ⟨1537602, by rfl⟩ : syracuseStep 4100273 = 3075205) B3075205
theorem B2306227 : Blo 1821612 2306227 := bstep (se 1 (by rfl) ⟨1729670, by rfl⟩ : syracuseStep 2306227 = 3459341) B3459341
theorem B1822899 : Blo 1821612 1822899 := bstep (se 1 (by rfl) ⟨1367174, by rfl⟩ : syracuseStep 1822899 = 2734349) B2734349
theorem B4100291 : Blo 1821612 4100291 := bstep (se 1 (by rfl) ⟨3075218, by rfl⟩ : syracuseStep 4100291 = 6150437) B6150437
theorem B1847491 : Blo 1821612 1847491 := bstep (se 1 (by rfl) ⟨1385618, by rfl⟩ : syracuseStep 1847491 = 2771237) B2771237
theorem B20754629 : Blo 1821612 20754629 := bstep (se 4 (by rfl) ⟨1945746, by rfl⟩ : syracuseStep 20754629 = 3891493) B3891493
theorem B1822915 : Blo 1821612 1822915 := bstep (se 1 (by rfl) ⟨1367186, by rfl⟩ : syracuseStep 1822915 = 2734373) B2734373
theorem B1822931 : Blo 1821612 1822931 := bstep (se 1 (by rfl) ⟨1367198, by rfl⟩ : syracuseStep 1822931 = 2734397) B2734397
theorem B1822947 : Blo 1821612 1822947 := bstep (se 1 (by rfl) ⟨1367210, by rfl⟩ : syracuseStep 1822947 = 2734421) B2734421
theorem B1822963 : Blo 1821612 1822963 := bstep (se 1 (by rfl) ⟨1367222, by rfl⟩ : syracuseStep 1822963 = 2734445) B2734445
theorem B3076339 : Blo 1821612 3076339 := bstep (se 1 (by rfl) ⟨2307254, by rfl⟩ : syracuseStep 3076339 = 4614509) B4614509
theorem B1822979 : Blo 1821612 1822979 := bstep (se 1 (by rfl) ⟨1367234, by rfl⟩ : syracuseStep 1822979 = 2734469) B2734469
theorem B4501763 : Blo 1821612 4501763 := bstep (se 1 (by rfl) ⟨3376322, by rfl⟩ : syracuseStep 4501763 = 6752645) B6752645
theorem B2306323 : Blo 1821612 2306323 := bstep (se 1 (by rfl) ⟨1729742, by rfl⟩ : syracuseStep 2306323 = 3459485) B3459485
theorem B1822995 : Blo 1821612 1822995 := bstep (se 1 (by rfl) ⟨1367246, by rfl⟩ : syracuseStep 1822995 = 2734493) B2734493
theorem B1823011 : Blo 1821612 1823011 := bstep (se 1 (by rfl) ⟨1367258, by rfl⟩ : syracuseStep 1823011 = 2734517) B2734517
theorem B5189933 : Blo 1821612 5189933 := bstep (se 3 (by rfl) ⟨973112, by rfl⟩ : syracuseStep 5189933 = 1946225) B1946225
theorem B1823027 : Blo 1821612 1823027 := bstep (se 1 (by rfl) ⟨1367270, by rfl⟩ : syracuseStep 1823027 = 2734541) B2734541
theorem B1823043 : Blo 1821612 1823043 := bstep (se 1 (by rfl) ⟨1367282, by rfl⟩ : syracuseStep 1823043 = 2734565) B2734565
theorem B1823059 : Blo 1821612 1823059 := bstep (se 1 (by rfl) ⟨1367294, by rfl⟩ : syracuseStep 1823059 = 2734589) B2734589
theorem B1823075 : Blo 1821612 1823075 := bstep (se 1 (by rfl) ⟨1367306, by rfl⟩ : syracuseStep 1823075 = 2734613) B2734613
theorem B1823091 : Blo 1821612 1823091 := bstep (se 1 (by rfl) ⟨1367318, by rfl⟩ : syracuseStep 1823091 = 2734637) B2734637
theorem B3076481 : Blo 1821612 3076481 := bstep (se 2 (by rfl) ⟨1153680, by rfl⟩ : syracuseStep 3076481 = 2307361) B2307361
theorem B1823107 : Blo 1821612 1823107 := bstep (se 1 (by rfl) ⟨1367330, by rfl⟩ : syracuseStep 1823107 = 2734661) B2734661
theorem B6238595 : Blo 1821612 6238595 := bstep (se 1 (by rfl) ⟨4678946, by rfl⟩ : syracuseStep 6238595 = 9357893) B9357893
theorem B6148493 : Blo 1821612 6148493 := bstep (se 3 (by rfl) ⟨1152842, by rfl⟩ : syracuseStep 6148493 = 2305685) B2305685
theorem B2732435 : Blo 1821612 2732435 := bstep (se 1 (by rfl) ⟨2049326, by rfl⟩ : syracuseStep 2732435 = 4098653) B4098653
theorem B1946003 : Blo 1821612 1946003 := bstep (se 1 (by rfl) ⟨1459502, by rfl⟩ : syracuseStep 1946003 = 2919005) B2919005
theorem B1823123 : Blo 1821612 1823123 := bstep (se 1 (by rfl) ⟨1367342, by rfl⟩ : syracuseStep 1823123 = 2734685) B2734685
theorem B1823139 : Blo 1821612 1823139 := bstep (se 1 (by rfl) ⟨1367354, by rfl⟩ : syracuseStep 1823139 = 2734709) B2734709
theorem B2732465 : Blo 1821612 2732465 := bstep (se 2 (by rfl) ⟨1024674, by rfl⟩ : syracuseStep 2732465 = 2049349) B2049349
theorem B1823155 : Blo 1821612 1823155 := bstep (se 1 (by rfl) ⟨1367366, by rfl⟩ : syracuseStep 1823155 = 2734733) B2734733
theorem B2732483 : Blo 1821612 2732483 := bstep (se 1 (by rfl) ⟨2049362, by rfl⟩ : syracuseStep 2732483 = 4098725) B4098725
theorem B6148547 : Blo 1821612 6148547 := bstep (se 1 (by rfl) ⟨4611410, by rfl⟩ : syracuseStep 6148547 = 9222821) B9222821
theorem B1823171 : Blo 1821612 1823171 := bstep (se 1 (by rfl) ⟨1367378, by rfl⟩ : syracuseStep 1823171 = 2734757) B2734757
theorem B6918605 : Blo 1821612 6918605 := bstep (se 3 (by rfl) ⟨1297238, by rfl⟩ : syracuseStep 6918605 = 2594477) B2594477
theorem B4100561 : Blo 1821612 4100561 := bstep (se 2 (by rfl) ⟨1537710, by rfl⟩ : syracuseStep 4100561 = 3075421) B3075421
theorem B1823187 : Blo 1821612 1823187 := bstep (se 1 (by rfl) ⟨1367390, by rfl⟩ : syracuseStep 1823187 = 2734781) B2734781
theorem B2732513 : Blo 1821612 2732513 := bstep (se 2 (by rfl) ⟨1024692, by rfl⟩ : syracuseStep 2732513 = 2049385) B2049385
theorem B4100579 : Blo 1821612 4100579 := bstep (se 1 (by rfl) ⟨3075434, by rfl⟩ : syracuseStep 4100579 = 6150869) B6150869
theorem B1823203 : Blo 1821612 1823203 := bstep (se 1 (by rfl) ⟨1367402, by rfl⟩ : syracuseStep 1823203 = 2734805) B2734805
theorem B8761841 : Blo 1821612 8761841 := bstep (se 2 (by rfl) ⟨3285690, by rfl⟩ : syracuseStep 8761841 = 6571381) B6571381
theorem B2732531 : Blo 1821612 2732531 := bstep (se 1 (by rfl) ⟨2049398, by rfl⟩ : syracuseStep 2732531 = 4098797) B4098797
theorem B1823219 : Blo 1821612 1823219 := bstep (se 1 (by rfl) ⟨1367414, by rfl⟩ : syracuseStep 1823219 = 2734829) B2734829
theorem B3076609 : Blo 1821612 3076609 := bstep (se 2 (by rfl) ⟨1153728, by rfl⟩ : syracuseStep 3076609 = 2307457) B2307457
theorem B1823235 : Blo 1821612 1823235 := bstep (se 1 (by rfl) ⟨1367426, by rfl⟩ : syracuseStep 1823235 = 2734853) B2734853
theorem B2732561 : Blo 1821612 2732561 := bstep (se 2 (by rfl) ⟨1024710, by rfl⟩ : syracuseStep 2732561 = 2049421) B2049421
theorem B1823251 : Blo 1821612 1823251 := bstep (se 1 (by rfl) ⟨1367438, by rfl⟩ : syracuseStep 1823251 = 2734877) B2734877
theorem B2732579 : Blo 1821612 2732579 := bstep (se 1 (by rfl) ⟨2049434, by rfl⟩ : syracuseStep 2732579 = 4098869) B4098869
theorem B3076643 : Blo 1821612 3076643 := bstep (se 1 (by rfl) ⟨2307482, by rfl⟩ : syracuseStep 3076643 = 4614965) B4614965
theorem B1823267 : Blo 1821612 1823267 := bstep (se 1 (by rfl) ⟨1367450, by rfl⟩ : syracuseStep 1823267 = 2734901) B2734901
theorem B1823283 : Blo 1821612 1823283 := bstep (se 1 (by rfl) ⟨1367462, by rfl⟩ : syracuseStep 1823283 = 2734925) B2734925
theorem B2732609 : Blo 1821612 2732609 := bstep (se 2 (by rfl) ⟨1024728, by rfl⟩ : syracuseStep 2732609 = 2049457) B2049457
theorem B1823299 : Blo 1821612 1823299 := bstep (se 1 (by rfl) ⟨1367474, by rfl⟩ : syracuseStep 1823299 = 2734949) B2734949
theorem B2732627 : Blo 1821612 2732627 := bstep (se 1 (by rfl) ⟨2049470, by rfl⟩ : syracuseStep 2732627 = 4098941) B4098941
theorem B1823315 : Blo 1821612 1823315 := bstep (se 1 (by rfl) ⟨1367486, by rfl⟩ : syracuseStep 1823315 = 2734973) B2734973
theorem B1823331 : Blo 1821612 1823331 := bstep (se 1 (by rfl) ⟨1367498, by rfl⟩ : syracuseStep 1823331 = 2734997) B2734997
theorem B2732657 : Blo 1821612 2732657 := bstep (se 2 (by rfl) ⟨1024746, by rfl⟩ : syracuseStep 2732657 = 2049493) B2049493
theorem B1823347 : Blo 1821612 1823347 := bstep (se 1 (by rfl) ⟨1367510, by rfl⟩ : syracuseStep 1823347 = 2735021) B2735021
theorem B2732675 : Blo 1821612 2732675 := bstep (se 1 (by rfl) ⟨2049506, by rfl⟩ : syracuseStep 2732675 = 4099013) B4099013
theorem B1823363 : Blo 1821612 1823363 := bstep (se 1 (by rfl) ⟨1367522, by rfl⟩ : syracuseStep 1823363 = 2735045) B2735045
theorem B1823379 : Blo 1821612 1823379 := bstep (se 1 (by rfl) ⟨1367534, by rfl⟩ : syracuseStep 1823379 = 2735069) B2735069
theorem B2732705 : Blo 1821612 2732705 := bstep (se 2 (by rfl) ⟨1024764, by rfl⟩ : syracuseStep 2732705 = 2049529) B2049529
theorem B3076771 : Blo 1821612 3076771 := bstep (se 1 (by rfl) ⟨2307578, by rfl⟩ : syracuseStep 3076771 = 4615157) B4615157
theorem B1823395 : Blo 1821612 1823395 := bstep (se 1 (by rfl) ⟨1367546, by rfl⟩ : syracuseStep 1823395 = 2735093) B2735093
theorem B9228977 : Blo 1821612 9228977 := bstep (se 2 (by rfl) ⟨3460866, by rfl⟩ : syracuseStep 9228977 = 6921733) B6921733
theorem B2732723 : Blo 1821612 2732723 := bstep (se 1 (by rfl) ⟨2049542, by rfl⟩ : syracuseStep 2732723 = 4099085) B4099085
theorem B1823411 : Blo 1821612 1823411 := bstep (se 1 (by rfl) ⟨1367558, by rfl⟩ : syracuseStep 1823411 = 2735117) B2735117
theorem B1823427 : Blo 1821612 1823427 := bstep (se 1 (by rfl) ⟨1367570, by rfl⟩ : syracuseStep 1823427 = 2735141) B2735141
theorem B4436689 : Blo 1821612 4436689 := bstep (se 2 (by rfl) ⟨1663758, by rfl⟩ : syracuseStep 4436689 = 3327517) B3327517
theorem B2732753 : Blo 1821612 2732753 := bstep (se 2 (by rfl) ⟨1024782, by rfl⟩ : syracuseStep 2732753 = 2049565) B2049565
theorem B6148817 : Blo 1821612 6148817 := bstep (se 2 (by rfl) ⟨2305806, by rfl⟩ : syracuseStep 6148817 = 4611613) B4611613
theorem B1823443 : Blo 1821612 1823443 := bstep (se 1 (by rfl) ⟨1367582, by rfl⟩ : syracuseStep 1823443 = 2735165) B2735165
theorem B2732771 : Blo 1821612 2732771 := bstep (se 1 (by rfl) ⟨2049578, by rfl⟩ : syracuseStep 2732771 = 4099157) B4099157
theorem B1823459 : Blo 1821612 1823459 := bstep (se 1 (by rfl) ⟨1367594, by rfl⟩ : syracuseStep 1823459 = 2735189) B2735189
theorem B4100849 : Blo 1821612 4100849 := bstep (se 2 (by rfl) ⟨1537818, by rfl⟩ : syracuseStep 4100849 = 3075637) B3075637
theorem B20763377 : Blo 1821612 20763377 := bstep (se 2 (by rfl) ⟨7786266, by rfl⟩ : syracuseStep 20763377 = 15572533) B15572533
theorem B1823475 : Blo 1821612 1823475 := bstep (se 1 (by rfl) ⟨1367606, by rfl⟩ : syracuseStep 1823475 = 2735213) B2735213
theorem B2732801 : Blo 1821612 2732801 := bstep (se 2 (by rfl) ⟨1024800, by rfl⟩ : syracuseStep 2732801 = 2049601) B2049601
theorem B4100867 : Blo 1821612 4100867 := bstep (se 1 (by rfl) ⟨3075650, by rfl⟩ : syracuseStep 4100867 = 6151301) B6151301
theorem B2306819 : Blo 1821612 2306819 := bstep (se 1 (by rfl) ⟨1730114, by rfl⟩ : syracuseStep 2306819 = 3460229) B3460229
theorem B1823491 : Blo 1821612 1823491 := bstep (se 1 (by rfl) ⟨1367618, by rfl⟩ : syracuseStep 1823491 = 2735237) B2735237
theorem B2732819 : Blo 1821612 2732819 := bstep (se 1 (by rfl) ⟨2049614, by rfl⟩ : syracuseStep 2732819 = 4099229) B4099229
theorem B1823507 : Blo 1821612 1823507 := bstep (se 1 (by rfl) ⟨1367630, by rfl⟩ : syracuseStep 1823507 = 2735261) B2735261
theorem B1823523 : Blo 1821612 1823523 := bstep (se 1 (by rfl) ⟨1367642, by rfl⟩ : syracuseStep 1823523 = 2735285) B2735285
theorem B2732849 : Blo 1821612 2732849 := bstep (se 2 (by rfl) ⟨1024818, by rfl⟩ : syracuseStep 2732849 = 2049637) B2049637
theorem B3076913 : Blo 1821612 3076913 := bstep (se 2 (by rfl) ⟨1153842, by rfl⟩ : syracuseStep 3076913 = 2307685) B2307685
theorem B1823539 : Blo 1821612 1823539 := bstep (se 1 (by rfl) ⟨1367654, by rfl⟩ : syracuseStep 1823539 = 2735309) B2735309
theorem B2732867 : Blo 1821612 2732867 := bstep (se 1 (by rfl) ⟨2049650, by rfl⟩ : syracuseStep 2732867 = 4099301) B4099301
theorem B1823555 : Blo 1821612 1823555 := bstep (se 1 (by rfl) ⟨1367666, by rfl⟩ : syracuseStep 1823555 = 2735333) B2735333
theorem B1823571 : Blo 1821612 1823571 := bstep (se 1 (by rfl) ⟨1367678, by rfl⟩ : syracuseStep 1823571 = 2735357) B2735357
theorem B2732897 : Blo 1821612 2732897 := bstep (se 2 (by rfl) ⟨1024836, by rfl⟩ : syracuseStep 2732897 = 2049673) B2049673
theorem B4158307 : Blo 1821612 4158307 := bstep (se 1 (by rfl) ⟨3118730, by rfl⟩ : syracuseStep 4158307 = 6237461) B6237461
theorem B1823587 : Blo 1821612 1823587 := bstep (se 1 (by rfl) ⟨1367690, by rfl⟩ : syracuseStep 1823587 = 2735381) B2735381
theorem B2732915 : Blo 1821612 2732915 := bstep (se 1 (by rfl) ⟨2049686, by rfl⟩ : syracuseStep 2732915 = 4099373) B4099373
theorem B1823603 : Blo 1821612 1823603 := bstep (se 1 (by rfl) ⟨1367702, by rfl⟩ : syracuseStep 1823603 = 2735405) B2735405
theorem B2732945 : Blo 1821612 2732945 := bstep (se 2 (by rfl) ⟨1024854, by rfl⟩ : syracuseStep 2732945 = 2049709) B2049709
theorem B4158353 : Blo 1821612 4158353 := bstep (se 2 (by rfl) ⟨1559382, by rfl⟩ : syracuseStep 4158353 = 3118765) B3118765
theorem B2732963 : Blo 1821612 2732963 := bstep (se 1 (by rfl) ⟨2049722, by rfl⟩ : syracuseStep 2732963 = 4099445) B4099445
theorem B5837741 : Blo 1821612 5837741 := bstep (se 3 (by rfl) ⟨1094576, by rfl⟩ : syracuseStep 5837741 = 2189153) B2189153
theorem B3077041 : Blo 1821612 3077041 := bstep (se 2 (by rfl) ⟨1153890, by rfl⟩ : syracuseStep 3077041 = 2307781) B2307781
theorem B2732993 : Blo 1821612 2732993 := bstep (se 2 (by rfl) ⟨1024872, by rfl⟩ : syracuseStep 2732993 = 2049745) B2049745
theorem B2733011 : Blo 1821612 2733011 := bstep (se 1 (by rfl) ⟨2049758, by rfl⟩ : syracuseStep 2733011 = 4099517) B4099517
theorem B3077075 : Blo 1821612 3077075 := bstep (se 1 (by rfl) ⟨2307806, by rfl⟩ : syracuseStep 3077075 = 4615613) B4615613
theorem B2593777 : Blo 1821612 2593777 := bstep (se 2 (by rfl) ⟨972666, by rfl⟩ : syracuseStep 2593777 = 1945333) B1945333
theorem B2733041 : Blo 1821612 2733041 := bstep (se 2 (by rfl) ⟨1024890, by rfl⟩ : syracuseStep 2733041 = 2049781) B2049781
theorem B2733059 : Blo 1821612 2733059 := bstep (se 1 (by rfl) ⟨2049794, by rfl⟩ : syracuseStep 2733059 = 4099589) B4099589
theorem B4101137 : Blo 1821612 4101137 := bstep (se 2 (by rfl) ⟨1537926, by rfl⟩ : syracuseStep 4101137 = 3075853) B3075853
theorem B2733089 : Blo 1821612 2733089 := bstep (se 2 (by rfl) ⟨1024908, by rfl⟩ : syracuseStep 2733089 = 2049817) B2049817
theorem B4101155 : Blo 1821612 4101155 := bstep (se 1 (by rfl) ⟨3075866, by rfl⟩ : syracuseStep 4101155 = 6151733) B6151733
theorem B2733107 : Blo 1821612 2733107 := bstep (se 1 (by rfl) ⟨2049830, by rfl⟩ : syracuseStep 2733107 = 4099661) B4099661
theorem B52524085 : Blo 1821612 52524085 := bstep (se 5 (by rfl) ⟨2462066, by rfl⟩ : syracuseStep 52524085 = 4924133) B4924133
theorem B7894093 : Blo 1821612 7894093 := bstep (se 3 (by rfl) ⟨1480142, by rfl⟩ : syracuseStep 7894093 = 2960285) B2960285
theorem B2593873 : Blo 1821612 2593873 := bstep (se 2 (by rfl) ⟨972702, by rfl⟩ : syracuseStep 2593873 = 1945405) B1945405
theorem B2733137 : Blo 1821612 2733137 := bstep (se 2 (by rfl) ⟨1024926, by rfl⟩ : syracuseStep 2733137 = 2049853) B2049853
theorem B3077203 : Blo 1821612 3077203 := bstep (se 1 (by rfl) ⟨2307902, by rfl⟩ : syracuseStep 3077203 = 4615805) B4615805
theorem B2733155 : Blo 1821612 2733155 := bstep (se 1 (by rfl) ⟨2049866, by rfl⟩ : syracuseStep 2733155 = 4099733) B4099733
theorem B6567011 : Blo 1821612 6567011 := bstep (se 1 (by rfl) ⟨4925258, by rfl⟩ : syracuseStep 6567011 = 9850517) B9850517
theorem B2733185 : Blo 1821612 2733185 := bstep (se 2 (by rfl) ⟨1024944, by rfl⟩ : syracuseStep 2733185 = 2049889) B2049889
theorem B1946755 : Blo 1821612 1946755 := bstep (se 1 (by rfl) ⟨1460066, by rfl⟩ : syracuseStep 1946755 = 2920133) B2920133
theorem B2733203 : Blo 1821612 2733203 := bstep (se 1 (by rfl) ⟨2049902, by rfl⟩ : syracuseStep 2733203 = 4099805) B4099805
theorem B2733233 : Blo 1821612 2733233 := bstep (se 2 (by rfl) ⟨1024962, by rfl⟩ : syracuseStep 2733233 = 2049925) B2049925
theorem B2733251 : Blo 1821612 2733251 := bstep (se 1 (by rfl) ⟨2049938, by rfl⟩ : syracuseStep 2733251 = 4099877) B4099877
theorem B2733281 : Blo 1821612 2733281 := bstep (se 2 (by rfl) ⟨1024980, by rfl⟩ : syracuseStep 2733281 = 2049961) B2049961
theorem B3077345 : Blo 1821612 3077345 := bstep (se 2 (by rfl) ⟨1154004, by rfl⟩ : syracuseStep 3077345 = 2308009) B2308009
theorem B6149357 : Blo 1821612 6149357 := bstep (se 3 (by rfl) ⟨1153004, by rfl⟩ : syracuseStep 6149357 = 2306009) B2306009
theorem B2733299 : Blo 1821612 2733299 := bstep (se 1 (by rfl) ⟨2049974, by rfl⟩ : syracuseStep 2733299 = 4099949) B4099949
theorem B5190925 : Blo 1821612 5190925 := bstep (se 3 (by rfl) ⟨973298, by rfl⟩ : syracuseStep 5190925 = 1946597) B1946597
theorem B2733329 : Blo 1821612 2733329 := bstep (se 2 (by rfl) ⟨1024998, by rfl⟩ : syracuseStep 2733329 = 2049997) B2049997
theorem B6149411 : Blo 1821612 6149411 := bstep (se 1 (by rfl) ⟨4612058, by rfl⟩ : syracuseStep 6149411 = 9224117) B9224117
theorem B2733347 : Blo 1821612 2733347 := bstep (se 1 (by rfl) ⟨2050010, by rfl⟩ : syracuseStep 2733347 = 4100021) B4100021
theorem B4101425 : Blo 1821612 4101425 := bstep (se 2 (by rfl) ⟨1538034, by rfl⟩ : syracuseStep 4101425 = 3076069) B3076069
theorem B2733377 : Blo 1821612 2733377 := bstep (se 2 (by rfl) ⟨1025016, by rfl⟩ : syracuseStep 2733377 = 2050033) B2050033
theorem B4101443 : Blo 1821612 4101443 := bstep (se 1 (by rfl) ⟨3076082, by rfl⟩ : syracuseStep 4101443 = 6152165) B6152165
theorem B10523981 : Blo 1821612 10523981 := bstep (se 3 (by rfl) ⟨1973246, by rfl⟩ : syracuseStep 10523981 = 3946493) B3946493
theorem B2733395 : Blo 1821612 2733395 := bstep (se 1 (by rfl) ⟨2050046, by rfl⟩ : syracuseStep 2733395 = 4100093) B4100093
theorem B2733425 : Blo 1821612 2733425 := bstep (se 2 (by rfl) ⟨1025034, by rfl⟩ : syracuseStep 2733425 = 2050069) B2050069
theorem B2733443 : Blo 1821612 2733443 := bstep (se 1 (by rfl) ⟨2050082, by rfl⟩ : syracuseStep 2733443 = 4100165) B4100165
theorem B1947011 : Blo 1821612 1947011 := bstep (se 1 (by rfl) ⟨1460258, by rfl⟩ : syracuseStep 1947011 = 2920517) B2920517
theorem B2733473 : Blo 1821612 2733473 := bstep (se 2 (by rfl) ⟨1025052, by rfl⟩ : syracuseStep 2733473 = 2050105) B2050105
theorem B4740515 : Blo 1821612 4740515 := bstep (se 1 (by rfl) ⟨3555386, by rfl⟩ : syracuseStep 4740515 = 7110773) B7110773
theorem B2733491 : Blo 1821612 2733491 := bstep (se 1 (by rfl) ⟨2050118, by rfl⟩ : syracuseStep 2733491 = 4100237) B4100237
theorem B2307523 : Blo 1821612 2307523 := bstep (se 1 (by rfl) ⟨1730642, by rfl⟩ : syracuseStep 2307523 = 3461285) B3461285
theorem B11679173 : Blo 1821612 11679173 := bstep (se 4 (by rfl) ⟨1094922, by rfl⟩ : syracuseStep 11679173 = 2189845) B2189845
theorem B2733521 : Blo 1821612 2733521 := bstep (se 2 (by rfl) ⟨1025070, by rfl⟩ : syracuseStep 2733521 = 2050141) B2050141
theorem B4928977 : Blo 1821612 4928977 := bstep (se 2 (by rfl) ⟨1848366, by rfl⟩ : syracuseStep 4928977 = 3696733) B3696733
theorem B2733539 : Blo 1821612 2733539 := bstep (se 1 (by rfl) ⟨2050154, by rfl⟩ : syracuseStep 2733539 = 4100309) B4100309
theorem B2733569 : Blo 1821612 2733569 := bstep (se 2 (by rfl) ⟨1025088, by rfl⟩ : syracuseStep 2733569 = 2050177) B2050177
theorem B2733587 : Blo 1821612 2733587 := bstep (se 1 (by rfl) ⟨2050190, by rfl⟩ : syracuseStep 2733587 = 4100381) B4100381
theorem B2078227 : Blo 1821612 2078227 := bstep (se 1 (by rfl) ⟨1558670, by rfl⟩ : syracuseStep 2078227 = 3117341) B3117341
theorem B2307619 : Blo 1821612 2307619 := bstep (se 1 (by rfl) ⟨1730714, by rfl⟩ : syracuseStep 2307619 = 3461429) B3461429
theorem B6149681 : Blo 1821612 6149681 := bstep (se 2 (by rfl) ⟨2306130, by rfl⟩ : syracuseStep 6149681 = 4612261) B4612261
theorem B6567473 : Blo 1821612 6567473 := bstep (se 2 (by rfl) ⟨2462802, by rfl⟩ : syracuseStep 6567473 = 4925605) B4925605
theorem B2733617 : Blo 1821612 2733617 := bstep (se 2 (by rfl) ⟨1025106, by rfl⟩ : syracuseStep 2733617 = 2050213) B2050213
theorem B2594369 : Blo 1821612 2594369 := bstep (se 2 (by rfl) ⟨972888, by rfl⟩ : syracuseStep 2594369 = 1945777) B1945777
theorem B2733635 : Blo 1821612 2733635 := bstep (se 1 (by rfl) ⟨2050226, by rfl⟩ : syracuseStep 2733635 = 4100453) B4100453
theorem B4101713 : Blo 1821612 4101713 := bstep (se 2 (by rfl) ⟨1538142, by rfl⟩ : syracuseStep 4101713 = 3076285) B3076285
theorem B2733665 : Blo 1821612 2733665 := bstep (se 2 (by rfl) ⟨1025124, by rfl⟩ : syracuseStep 2733665 = 2050249) B2050249
theorem B4101731 : Blo 1821612 4101731 := bstep (se 1 (by rfl) ⟨3076298, by rfl⟩ : syracuseStep 4101731 = 6152597) B6152597
theorem B2733683 : Blo 1821612 2733683 := bstep (se 1 (by rfl) ⟨2050262, by rfl⟩ : syracuseStep 2733683 = 4100525) B4100525
theorem B2733713 : Blo 1821612 2733713 := bstep (se 2 (by rfl) ⟨1025142, by rfl⟩ : syracuseStep 2733713 = 2050285) B2050285
theorem B2733731 : Blo 1821612 2733731 := bstep (se 1 (by rfl) ⟨2050298, by rfl⟩ : syracuseStep 2733731 = 4100597) B4100597
theorem B2053811 : Blo 1821612 2053811 := bstep (se 1 (by rfl) ⟨1540358, by rfl⟩ : syracuseStep 2053811 = 3080717) B3080717
theorem B2733761 : Blo 1821612 2733761 := bstep (se 2 (by rfl) ⟨1025160, by rfl⟩ : syracuseStep 2733761 = 2050321) B2050321
theorem B33265349 : Blo 1821612 33265349 := bstep (se 4 (by rfl) ⟨3118626, by rfl⟩ : syracuseStep 33265349 = 6237253) B6237253
theorem B2733779 : Blo 1821612 2733779 := bstep (se 1 (by rfl) ⟨2050334, by rfl⟩ : syracuseStep 2733779 = 4100669) B4100669
theorem B2733809 : Blo 1821612 2733809 := bstep (se 2 (by rfl) ⟨1025178, by rfl⟩ : syracuseStep 2733809 = 2050357) B2050357
theorem B2733827 : Blo 1821612 2733827 := bstep (se 1 (by rfl) ⟨2050370, by rfl⟩ : syracuseStep 2733827 = 4100741) B4100741
theorem B11089669 : Blo 1821612 11089669 := bstep (se 4 (by rfl) ⟨1039656, by rfl⟩ : syracuseStep 11089669 = 2079313) B2079313
theorem B2733857 : Blo 1821612 2733857 := bstep (se 2 (by rfl) ⟨1025196, by rfl⟩ : syracuseStep 2733857 = 2050393) B2050393
theorem B2733875 : Blo 1821612 2733875 := bstep (se 1 (by rfl) ⟨2050406, by rfl⟩ : syracuseStep 2733875 = 4100813) B4100813
theorem B2733905 : Blo 1821612 2733905 := bstep (se 2 (by rfl) ⟨1025214, by rfl⟩ : syracuseStep 2733905 = 2050429) B2050429
theorem B2733923 : Blo 1821612 2733923 := bstep (se 1 (by rfl) ⟨2050442, by rfl⟩ : syracuseStep 2733923 = 4100885) B4100885
theorem B4102001 : Blo 1821612 4102001 := bstep (se 2 (by rfl) ⟨1538250, by rfl⟩ : syracuseStep 4102001 = 3076501) B3076501
theorem B2733953 : Blo 1821612 2733953 := bstep (se 2 (by rfl) ⟨1025232, by rfl⟩ : syracuseStep 2733953 = 2050465) B2050465
theorem B4102019 : Blo 1821612 4102019 := bstep (se 1 (by rfl) ⟨3076514, by rfl⟩ : syracuseStep 4102019 = 6153029) B6153029
theorem B2733971 : Blo 1821612 2733971 := bstep (se 1 (by rfl) ⟨2050478, by rfl⟩ : syracuseStep 2733971 = 4100957) B4100957
theorem B2734001 : Blo 1821612 2734001 := bstep (se 2 (by rfl) ⟨1025250, by rfl⟩ : syracuseStep 2734001 = 2050501) B2050501
theorem B2734019 : Blo 1821612 2734019 := bstep (se 1 (by rfl) ⟨2050514, by rfl⟩ : syracuseStep 2734019 = 4101029) B4101029
theorem B2734049 : Blo 1821612 2734049 := bstep (se 2 (by rfl) ⟨1025268, by rfl⟩ : syracuseStep 2734049 = 2050537) B2050537
theorem B2734067 : Blo 1821612 2734067 := bstep (se 1 (by rfl) ⟨2050550, by rfl⟩ : syracuseStep 2734067 = 4101101) B4101101
theorem B2734097 : Blo 1821612 2734097 := bstep (se 2 (by rfl) ⟨1025286, by rfl⟩ : syracuseStep 2734097 = 2050573) B2050573
theorem B2734115 : Blo 1821612 2734115 := bstep (se 1 (by rfl) ⟨2050586, by rfl⟩ : syracuseStep 2734115 = 4101173) B4101173
theorem B2734145 : Blo 1821612 2734145 := bstep (se 2 (by rfl) ⟨1025304, by rfl⟩ : syracuseStep 2734145 = 2050609) B2050609
theorem B6150221 : Blo 1821612 6150221 := bstep (se 3 (by rfl) ⟨1153166, by rfl⟩ : syracuseStep 6150221 = 2306333) B2306333
theorem B2734163 : Blo 1821612 2734163 := bstep (se 1 (by rfl) ⟨2050622, by rfl⟩ : syracuseStep 2734163 = 4101245) B4101245
theorem B9230435 : Blo 1821612 9230435 := bstep (se 1 (by rfl) ⟨6922826, by rfl⟩ : syracuseStep 9230435 = 13845653) B13845653
theorem B6568049 : Blo 1821612 6568049 := bstep (se 2 (by rfl) ⟨2463018, by rfl⟩ : syracuseStep 6568049 = 4926037) B4926037
theorem B2734193 : Blo 1821612 2734193 := bstep (se 2 (by rfl) ⟨1025322, by rfl⟩ : syracuseStep 2734193 = 2050645) B2050645
theorem B6150275 : Blo 1821612 6150275 := bstep (se 1 (by rfl) ⟨4612706, by rfl⟩ : syracuseStep 6150275 = 9225413) B9225413
theorem B2734211 : Blo 1821612 2734211 := bstep (se 1 (by rfl) ⟨2050658, by rfl⟩ : syracuseStep 2734211 = 4101317) B4101317
theorem B4102289 : Blo 1821612 4102289 := bstep (se 2 (by rfl) ⟨1538358, by rfl⟩ : syracuseStep 4102289 = 3076717) B3076717
theorem B2734241 : Blo 1821612 2734241 := bstep (se 2 (by rfl) ⟨1025340, by rfl⟩ : syracuseStep 2734241 = 2050681) B2050681
theorem B4102307 : Blo 1821612 4102307 := bstep (se 1 (by rfl) ⟨3076730, by rfl⟩ : syracuseStep 4102307 = 6153461) B6153461
theorem B2734259 : Blo 1821612 2734259 := bstep (se 1 (by rfl) ⟨2050694, by rfl⟩ : syracuseStep 2734259 = 4101389) B4101389
theorem B2734289 : Blo 1821612 2734289 := bstep (se 2 (by rfl) ⟨1025358, by rfl⟩ : syracuseStep 2734289 = 2050717) B2050717
theorem B2734307 : Blo 1821612 2734307 := bstep (se 1 (by rfl) ⟨2050730, by rfl⟩ : syracuseStep 2734307 = 4101461) B4101461
theorem B5839085 : Blo 1821612 5839085 := bstep (se 3 (by rfl) ⟨1094828, by rfl⟩ : syracuseStep 5839085 = 2189657) B2189657
theorem B2734337 : Blo 1821612 2734337 := bstep (se 2 (by rfl) ⟨1025376, by rfl⟩ : syracuseStep 2734337 = 2050753) B2050753
theorem B2734355 : Blo 1821612 2734355 := bstep (se 1 (by rfl) ⟨2050766, by rfl⟩ : syracuseStep 2734355 = 4101533) B4101533
theorem B2734385 : Blo 1821612 2734385 := bstep (se 2 (by rfl) ⟨1025394, by rfl⟩ : syracuseStep 2734385 = 2050789) B2050789
theorem B2734403 : Blo 1821612 2734403 := bstep (se 1 (by rfl) ⟨2050802, by rfl⟩ : syracuseStep 2734403 = 4101605) B4101605
theorem B2734433 : Blo 1821612 2734433 := bstep (se 2 (by rfl) ⟨1025412, by rfl⟩ : syracuseStep 2734433 = 2050825) B2050825
theorem B7788899 : Blo 1821612 7788899 := bstep (se 1 (by rfl) ⟨5841674, by rfl⟩ : syracuseStep 7788899 = 11683349) B11683349
theorem B2734451 : Blo 1821612 2734451 := bstep (se 1 (by rfl) ⟨2050838, by rfl⟩ : syracuseStep 2734451 = 4101677) B4101677
theorem B6150545 : Blo 1821612 6150545 := bstep (se 2 (by rfl) ⟨2306454, by rfl⟩ : syracuseStep 6150545 = 4612909) B4612909
theorem B2734481 : Blo 1821612 2734481 := bstep (se 2 (by rfl) ⟨1025430, by rfl⟩ : syracuseStep 2734481 = 2050861) B2050861
theorem B2595235 : Blo 1821612 2595235 := bstep (se 1 (by rfl) ⟨1946426, by rfl⟩ : syracuseStep 2595235 = 3892853) B3892853
theorem B2734499 : Blo 1821612 2734499 := bstep (se 1 (by rfl) ⟨2050874, by rfl⟩ : syracuseStep 2734499 = 4101749) B4101749
theorem B4102577 : Blo 1821612 4102577 := bstep (se 2 (by rfl) ⟨1538466, by rfl⟩ : syracuseStep 4102577 = 3076933) B3076933
theorem B2734529 : Blo 1821612 2734529 := bstep (se 2 (by rfl) ⟨1025448, by rfl⟩ : syracuseStep 2734529 = 2050897) B2050897
theorem B4102595 : Blo 1821612 4102595 := bstep (se 1 (by rfl) ⟨3076946, by rfl⟩ : syracuseStep 4102595 = 6153893) B6153893
theorem B6568397 : Blo 1821612 6568397 := bstep (se 3 (by rfl) ⟨1231574, by rfl⟩ : syracuseStep 6568397 = 2463149) B2463149
theorem B2734547 : Blo 1821612 2734547 := bstep (se 1 (by rfl) ⟨2050910, by rfl⟩ : syracuseStep 2734547 = 4101821) B4101821
theorem B2734577 : Blo 1821612 2734577 := bstep (se 2 (by rfl) ⟨1025466, by rfl⟩ : syracuseStep 2734577 = 2050933) B2050933
theorem B2595331 : Blo 1821612 2595331 := bstep (se 1 (by rfl) ⟨1946498, by rfl⟩ : syracuseStep 2595331 = 3892997) B3892997
theorem B2734595 : Blo 1821612 2734595 := bstep (se 1 (by rfl) ⟨2050946, by rfl⟩ : syracuseStep 2734595 = 4101893) B4101893
theorem B7387661 : Blo 1821612 7387661 := bstep (se 3 (by rfl) ⟨1385186, by rfl⟩ : syracuseStep 7387661 = 2770373) B2770373
theorem B2734625 : Blo 1821612 2734625 := bstep (se 2 (by rfl) ⟨1025484, by rfl⟩ : syracuseStep 2734625 = 2050969) B2050969
theorem B2734643 : Blo 1821612 2734643 := bstep (se 1 (by rfl) ⟨2050982, by rfl⟩ : syracuseStep 2734643 = 4101965) B4101965
theorem B6232643 : Blo 1821612 6232643 := bstep (se 1 (by rfl) ⟨4674482, by rfl⟩ : syracuseStep 6232643 = 9348965) B9348965
theorem B2734673 : Blo 1821612 2734673 := bstep (se 2 (by rfl) ⟨1025502, by rfl⟩ : syracuseStep 2734673 = 2051005) B2051005
theorem B2734691 : Blo 1821612 2734691 := bstep (se 1 (by rfl) ⟨2051018, by rfl⟩ : syracuseStep 2734691 = 4102037) B4102037
theorem B78813809 : Blo 1821612 78813809 := bstep (se 2 (by rfl) ⟨29555178, by rfl⟩ : syracuseStep 78813809 = 59110357) B59110357
theorem B2734721 : Blo 1821612 2734721 := bstep (se 2 (by rfl) ⟨1025520, by rfl⟩ : syracuseStep 2734721 = 2051041) B2051041
theorem B46701197 : Blo 1821612 46701197 := bstep (se 3 (by rfl) ⟨8756474, by rfl⟩ : syracuseStep 46701197 = 17512949) B17512949
theorem B2734739 : Blo 1821612 2734739 := bstep (se 1 (by rfl) ⟨2051054, by rfl⟩ : syracuseStep 2734739 = 4102109) B4102109
theorem B5839523 : Blo 1821612 5839523 := bstep (se 1 (by rfl) ⟨4379642, by rfl⟩ : syracuseStep 5839523 = 8759285) B8759285
theorem B2734769 : Blo 1821612 2734769 := bstep (se 2 (by rfl) ⟨1025538, by rfl⟩ : syracuseStep 2734769 = 2051077) B2051077
theorem B2734787 : Blo 1821612 2734787 := bstep (se 1 (by rfl) ⟨2051090, by rfl⟩ : syracuseStep 2734787 = 4102181) B4102181
theorem B4102865 : Blo 1821612 4102865 := bstep (se 2 (by rfl) ⟨1538574, by rfl⟩ : syracuseStep 4102865 = 3077149) B3077149
theorem B2734817 : Blo 1821612 2734817 := bstep (se 2 (by rfl) ⟨1025556, by rfl⟩ : syracuseStep 2734817 = 2051113) B2051113
theorem B4102883 : Blo 1821612 4102883 := bstep (se 1 (by rfl) ⟨3077162, by rfl⟩ : syracuseStep 4102883 = 6154325) B6154325
theorem B2734835 : Blo 1821612 2734835 := bstep (se 1 (by rfl) ⟨2051126, by rfl⟩ : syracuseStep 2734835 = 4102253) B4102253
theorem B2734865 : Blo 1821612 2734865 := bstep (se 2 (by rfl) ⟨1025574, by rfl⟩ : syracuseStep 2734865 = 2051149) B2051149
theorem B2734883 : Blo 1821612 2734883 := bstep (se 1 (by rfl) ⟨2051162, by rfl⟩ : syracuseStep 2734883 = 4102325) B4102325
theorem B28449589 : Blo 1821612 28449589 := bstep (se 5 (by rfl) ⟨1333574, by rfl⟩ : syracuseStep 28449589 = 2667149) B2667149
theorem B2734913 : Blo 1821612 2734913 := bstep (se 2 (by rfl) ⟨1025592, by rfl⟩ : syracuseStep 2734913 = 2051185) B2051185
theorem B2734931 : Blo 1821612 2734931 := bstep (se 1 (by rfl) ⟨2051198, by rfl⟩ : syracuseStep 2734931 = 4102397) B4102397
theorem B2734961 : Blo 1821612 2734961 := bstep (se 2 (by rfl) ⟨1025610, by rfl⟩ : syracuseStep 2734961 = 2051221) B2051221
theorem B2734979 : Blo 1821612 2734979 := bstep (se 1 (by rfl) ⟨2051234, by rfl⟩ : syracuseStep 2734979 = 4102469) B4102469
theorem B9231245 : Blo 1821612 9231245 := bstep (se 3 (by rfl) ⟨1730858, by rfl⟩ : syracuseStep 9231245 = 3461717) B3461717
theorem B2735009 : Blo 1821612 2735009 := bstep (se 2 (by rfl) ⟨1025628, by rfl⟩ : syracuseStep 2735009 = 2051257) B2051257
theorem B6151085 : Blo 1821612 6151085 := bstep (se 3 (by rfl) ⟨1153328, by rfl⟩ : syracuseStep 6151085 = 2306657) B2306657
theorem B2735027 : Blo 1821612 2735027 := bstep (se 1 (by rfl) ⟨2051270, by rfl⟩ : syracuseStep 2735027 = 4102541) B4102541
theorem B2735057 : Blo 1821612 2735057 := bstep (se 2 (by rfl) ⟨1025646, by rfl⟩ : syracuseStep 2735057 = 2051293) B2051293
theorem B5192657 : Blo 1821612 5192657 := bstep (se 2 (by rfl) ⟨1947246, by rfl⟩ : syracuseStep 5192657 = 3894493) B3894493
theorem B6151139 : Blo 1821612 6151139 := bstep (se 1 (by rfl) ⟨4613354, by rfl⟩ : syracuseStep 6151139 = 9226709) B9226709
theorem B2735075 : Blo 1821612 2735075 := bstep (se 1 (by rfl) ⟨2051306, by rfl⟩ : syracuseStep 2735075 = 4102613) B4102613
theorem B2595827 : Blo 1821612 2595827 := bstep (se 1 (by rfl) ⟨1946870, by rfl⟩ : syracuseStep 2595827 = 3893741) B3893741
theorem B2735105 : Blo 1821612 2735105 := bstep (se 2 (by rfl) ⟨1025664, by rfl⟩ : syracuseStep 2735105 = 2051329) B2051329
theorem B2735123 : Blo 1821612 2735123 := bstep (se 1 (by rfl) ⟨2051342, by rfl⟩ : syracuseStep 2735123 = 4102685) B4102685
theorem B4611107 : Blo 1821612 4611107 := bstep (se 1 (by rfl) ⟨3458330, by rfl⟩ : syracuseStep 4611107 = 6916661) B6916661
theorem B2735153 : Blo 1821612 2735153 := bstep (se 2 (by rfl) ⟨1025682, by rfl⟩ : syracuseStep 2735153 = 2051365) B2051365
theorem B2735171 : Blo 1821612 2735171 := bstep (se 1 (by rfl) ⟨2051378, by rfl⟩ : syracuseStep 2735171 = 4102757) B4102757
theorem B2735201 : Blo 1821612 2735201 := bstep (se 2 (by rfl) ⟨1025700, by rfl⟩ : syracuseStep 2735201 = 2051401) B2051401
theorem B2735219 : Blo 1821612 2735219 := bstep (se 1 (by rfl) ⟨2051414, by rfl⟩ : syracuseStep 2735219 = 4102829) B4102829
theorem B11238533 : Blo 1821612 11238533 := bstep (se 4 (by rfl) ⟨1053612, by rfl⟩ : syracuseStep 11238533 = 2107225) B2107225
theorem B2735249 : Blo 1821612 2735249 := bstep (se 2 (by rfl) ⟨1025718, by rfl⟩ : syracuseStep 2735249 = 2051437) B2051437
theorem B5192849 : Blo 1821612 5192849 := bstep (se 2 (by rfl) ⟨1947318, by rfl⟩ : syracuseStep 5192849 = 3894637) B3894637
theorem B2735267 : Blo 1821612 2735267 := bstep (se 1 (by rfl) ⟨2051450, by rfl⟩ : syracuseStep 2735267 = 4102901) B4102901
theorem B2735297 : Blo 1821612 2735297 := bstep (se 2 (by rfl) ⟨1025736, by rfl⟩ : syracuseStep 2735297 = 2051473) B2051473
theorem B2735315 : Blo 1821612 2735315 := bstep (se 1 (by rfl) ⟨2051486, by rfl⟩ : syracuseStep 2735315 = 4102973) B4102973
theorem B6151409 : Blo 1821612 6151409 := bstep (se 2 (by rfl) ⟨2306778, by rfl⟩ : syracuseStep 6151409 = 4613557) B4613557
theorem B2735345 : Blo 1821612 2735345 := bstep (se 2 (by rfl) ⟨1025754, by rfl⟩ : syracuseStep 2735345 = 2051509) B2051509
theorem B2735363 : Blo 1821612 2735363 := bstep (se 1 (by rfl) ⟨2051522, by rfl⟩ : syracuseStep 2735363 = 4103045) B4103045
theorem B18963725 : Blo 1821612 18963725 := bstep (se 3 (by rfl) ⟨3555698, by rfl⟩ : syracuseStep 18963725 = 7111397) B7111397
theorem B2735393 : Blo 1821612 2735393 := bstep (se 2 (by rfl) ⟨1025772, by rfl⟩ : syracuseStep 2735393 = 2051545) B2051545
theorem B6921521 : Blo 1821612 6921521 := bstep (se 2 (by rfl) ⟨2595570, by rfl⟩ : syracuseStep 6921521 = 5191141) B5191141
theorem B2735411 : Blo 1821612 2735411 := bstep (se 1 (by rfl) ⟨2051558, by rfl⟩ : syracuseStep 2735411 = 4103117) B4103117
theorem B10378637 : Blo 1821612 10378637 := bstep (se 3 (by rfl) ⟨1945994, by rfl⟩ : syracuseStep 10378637 = 3891989) B3891989
theorem B8756707 : Blo 1821612 8756707 := bstep (se 1 (by rfl) ⟨6567530, by rfl⟩ : syracuseStep 8756707 = 13135061) B13135061
theorem B2629217 : Blo 1821612 2629217 := bstep (se 2 (by rfl) ⟨985956, by rfl⟩ : syracuseStep 2629217 = 1971913) B1971913
theorem B22158947 : Blo 1821612 22158947 := bstep (se 1 (by rfl) ⟨16619210, by rfl⟩ : syracuseStep 22158947 = 33238421) B33238421
theorem B9223793 : Blo 1821612 9223793 := bstep (se 2 (by rfl) ⟨3458922, by rfl⟩ : syracuseStep 9223793 = 6917845) B6917845
theorem B2596465 : Blo 1821612 2596465 := bstep (se 2 (by rfl) ⟨973674, by rfl⟩ : syracuseStep 2596465 = 1947349) B1947349
theorem B7782065 : Blo 1821612 7782065 := bstep (se 2 (by rfl) ⟨2918274, by rfl⟩ : syracuseStep 7782065 = 5836549) B5836549
theorem B13844195 : Blo 1821612 13844195 := bstep (se 1 (by rfl) ⟨10383146, by rfl⟩ : syracuseStep 13844195 = 20766293) B20766293
theorem B6151949 : Blo 1821612 6151949 := bstep (se 3 (by rfl) ⟨1153490, by rfl⟩ : syracuseStep 6151949 = 2306981) B2306981
theorem B6152003 : Blo 1821612 6152003 := bstep (se 1 (by rfl) ⟨4614002, by rfl⟩ : syracuseStep 6152003 = 9228005) B9228005
theorem B3284803 : Blo 1821612 3284803 := bstep (se 1 (by rfl) ⟨2463602, by rfl⟩ : syracuseStep 3284803 = 4927205) B4927205
theorem B2629507 : Blo 1821612 2629507 := bstep (se 1 (by rfl) ⟨1972130, by rfl⟩ : syracuseStep 2629507 = 3944261) B3944261
theorem B3694481 : Blo 1821612 3694481 := bstep (se 2 (by rfl) ⟨1385430, by rfl⟩ : syracuseStep 3694481 = 2770861) B2770861
theorem B4612049 : Blo 1821612 4612049 := bstep (se 2 (by rfl) ⟨1729518, by rfl⟩ : syracuseStep 4612049 = 3459037) B3459037
theorem B3284977 : Blo 1821612 3284977 := bstep (se 2 (by rfl) ⟨1231866, by rfl⟩ : syracuseStep 3284977 = 2463733) B2463733
theorem B3506177 : Blo 1821612 3506177 := bstep (se 2 (by rfl) ⟨1314816, by rfl⟩ : syracuseStep 3506177 = 2629633) B2629633
theorem B3694657 : Blo 1821612 3694657 := bstep (se 2 (by rfl) ⟨1385496, by rfl⟩ : syracuseStep 3694657 = 2770993) B2770993
theorem B11083877 : Blo 1821612 11083877 := bstep (se 4 (by rfl) ⟨1039113, by rfl⟩ : syracuseStep 11083877 = 2078227) B2078227
theorem B13836419 : Blo 1821612 13836419 := bstep (se 1 (by rfl) ⟨10377314, by rfl⟩ : syracuseStep 13836419 = 20754629) B20754629
theorem B4612403 : Blo 1821612 4612403 := bstep (se 1 (by rfl) ⟨3459302, by rfl⟩ : syracuseStep 4612403 = 6918605) B6918605
theorem B15565121 : Blo 1821612 15565121 := bstep (se 2 (by rfl) ⟨5836920, by rfl⟩ : syracuseStep 15565121 = 11673841) B11673841
theorem B5841227 : Blo 1821612 5841227 := bstep (se 1 (by rfl) ⟨4380920, by rfl⟩ : syracuseStep 5841227 = 8761841) B8761841
theorem B7782749 : Blo 1821612 7782749 := bstep (se 3 (by rfl) ⟨1459265, by rfl⟩ : syracuseStep 7782749 = 2918531) B2918531
theorem B7995827 : Blo 1821612 7995827 := bstep (se 1 (by rfl) ⟨5996870, by rfl⟩ : syracuseStep 7995827 = 11993741) B11993741
theorem B6152651 : Blo 1821612 6152651 := bstep (se 1 (by rfl) ⟨4614488, by rfl⟩ : syracuseStep 6152651 = 9228977) B9228977
theorem B9855533 : Blo 1821612 9855533 := bstep (se 3 (by rfl) ⟨1847912, by rfl⟩ : syracuseStep 9855533 = 3695825) B3695825
theorem B4612697 : Blo 1821612 4612697 := bstep (se 2 (by rfl) ⟨1729761, by rfl⟩ : syracuseStep 4612697 = 3459523) B3459523
theorem B3891827 : Blo 1821612 3891827 := bstep (se 1 (by rfl) ⟨2918870, by rfl⟩ : syracuseStep 3891827 = 5837741) B5837741
theorem B50569933 : Blo 1821612 50569933 := bstep (se 3 (by rfl) ⟨9481862, by rfl⟩ : syracuseStep 50569933 = 18963725) B18963725
theorem B6152921 : Blo 1821612 6152921 := bstep (se 2 (by rfl) ⟨2307345, by rfl⟩ : syracuseStep 6152921 = 4614691) B4614691
theorem B5915585 : Blo 1821612 5915585 := bstep (se 2 (by rfl) ⟨2218344, by rfl⟩ : syracuseStep 5915585 = 4436689) B4436689
theorem B22176899 : Blo 1821612 22176899 := bstep (se 1 (by rfl) ⟨16632674, by rfl⟩ : syracuseStep 22176899 = 33265349) B33265349
theorem B3458315 : Blo 1821612 3458315 := bstep (se 1 (by rfl) ⟨2593736, by rfl⟩ : syracuseStep 3458315 = 5187473) B5187473
theorem B3458369 : Blo 1821612 3458369 := bstep (se 2 (by rfl) ⟨1296888, by rfl⟩ : syracuseStep 3458369 = 2593777) B2593777
theorem B2049367 : Blo 1821612 2049367 := bstep (se 1 (by rfl) ⟨1537025, by rfl⟩ : syracuseStep 2049367 = 3074051) B3074051
theorem B6153623 : Blo 1821612 6153623 := bstep (se 1 (by rfl) ⟨4615217, by rfl⟩ : syracuseStep 6153623 = 9230435) B9230435
theorem B3892673 : Blo 1821612 3892673 := bstep (se 2 (by rfl) ⟨1459752, by rfl⟩ : syracuseStep 3892673 = 2919505) B2919505
theorem B8316377 : Blo 1821612 8316377 := bstep (se 2 (by rfl) ⟨3118641, by rfl⟩ : syracuseStep 8316377 = 6237283) B6237283
theorem B2049547 : Blo 1821612 2049547 := bstep (se 1 (by rfl) ⟨1537160, by rfl⟩ : syracuseStep 2049547 = 3074321) B3074321
theorem B9356845 : Blo 1821612 9356845 := bstep (se 3 (by rfl) ⟨1754408, by rfl⟩ : syracuseStep 9356845 = 3508817) B3508817
theorem B2049655 : Blo 1821612 2049655 := bstep (se 1 (by rfl) ⟨1537241, by rfl⟩ : syracuseStep 2049655 = 3074483) B3074483
theorem B4925107 : Blo 1821612 4925107 := bstep (se 1 (by rfl) ⟨3693830, by rfl⟩ : syracuseStep 4925107 = 7387661) B7387661
theorem B4155095 : Blo 1821612 4155095 := bstep (se 1 (by rfl) ⟨3116321, by rfl⟩ : syracuseStep 4155095 = 6232643) B6232643
theorem B3893015 : Blo 1821612 3893015 := bstep (se 1 (by rfl) ⟨2919761, by rfl⟩ : syracuseStep 3893015 = 5839523) B5839523
theorem B6571799 : Blo 1821612 6571799 := bstep (se 1 (by rfl) ⟨4928849, by rfl⟩ : syracuseStep 6571799 = 9857699) B9857699
theorem B2049835 : Blo 1821612 2049835 := bstep (se 1 (by rfl) ⟨1537376, by rfl⟩ : syracuseStep 2049835 = 3074753) B3074753
theorem B10381121 : Blo 1821612 10381121 := bstep (se 2 (by rfl) ⟨3892920, by rfl⟩ : syracuseStep 10381121 = 7785841) B7785841
theorem B22177637 : Blo 1821612 22177637 := bstep (se 4 (by rfl) ⟨2079153, by rfl⟩ : syracuseStep 22177637 = 4158307) B4158307
theorem B2049943 : Blo 1821612 2049943 := bstep (se 1 (by rfl) ⟨1537457, by rfl⟩ : syracuseStep 2049943 = 3074915) B3074915
theorem B28051379 : Blo 1821612 28051379 := bstep (se 1 (by rfl) ⟨21038534, by rfl⟩ : syracuseStep 28051379 = 42077069) B42077069
theorem B6154163 : Blo 1821612 6154163 := bstep (se 1 (by rfl) ⟨4615622, by rfl⟩ : syracuseStep 6154163 = 9231245) B9231245
theorem B11675609 : Blo 1821612 11675609 := bstep (se 2 (by rfl) ⟨4378353, by rfl⟩ : syracuseStep 11675609 = 8756707) B8756707
theorem B3074071 : Blo 1821612 3074071 := bstep (se 1 (by rfl) ⟨2305553, by rfl⟩ : syracuseStep 3074071 = 4611107) B4611107
theorem B2050123 : Blo 1821612 2050123 := bstep (se 1 (by rfl) ⟨1537592, by rfl⟩ : syracuseStep 2050123 = 3075185) B3075185
theorem B2050231 : Blo 1821612 2050231 := bstep (se 1 (by rfl) ⟨1537673, by rfl⟩ : syracuseStep 2050231 = 3075347) B3075347
theorem B6154433 : Blo 1821612 6154433 := bstep (se 2 (by rfl) ⟨2307912, by rfl⟩ : syracuseStep 6154433 = 4615825) B4615825
theorem B4614347 : Blo 1821612 4614347 := bstep (se 1 (by rfl) ⟨3460760, by rfl⟩ : syracuseStep 4614347 = 6921521) B6921521
theorem B3459287 : Blo 1821612 3459287 := bstep (se 1 (by rfl) ⟨2594465, by rfl⟩ : syracuseStep 3459287 = 5188931) B5188931
theorem B2050411 : Blo 1821612 2050411 := bstep (se 1 (by rfl) ⟨1537808, by rfl⟩ : syracuseStep 2050411 = 3075617) B3075617
theorem B14772631 : Blo 1821612 14772631 := bstep (se 1 (by rfl) ⟨11079473, by rfl⟩ : syracuseStep 14772631 = 22158947) B22158947
theorem B5188043 : Blo 1821612 5188043 := bstep (se 1 (by rfl) ⟨3891032, by rfl⟩ : syracuseStep 5188043 = 7782065) B7782065
theorem B2050519 : Blo 1821612 2050519 := bstep (se 1 (by rfl) ⟨1537889, by rfl⟩ : syracuseStep 2050519 = 3075779) B3075779
theorem B4098635 : Blo 1821612 4098635 := bstep (se 1 (by rfl) ⟨3073976, by rfl⟩ : syracuseStep 4098635 = 6147953) B6147953
theorem B14248549 : Blo 1821612 14248549 := bstep (se 4 (by rfl) ⟨1335801, by rfl⟩ : syracuseStep 14248549 = 2671603) B2671603
theorem B4098689 : Blo 1821612 4098689 := bstep (se 2 (by rfl) ⟨1537008, by rfl⟩ : syracuseStep 4098689 = 3074017) B3074017
theorem B3074699 : Blo 1821612 3074699 := bstep (se 1 (by rfl) ⟨2306024, by rfl⟩ : syracuseStep 3074699 = 4612049) B4612049
theorem B2050699 : Blo 1821612 2050699 := bstep (se 1 (by rfl) ⟨1538024, by rfl⟩ : syracuseStep 2050699 = 3076049) B3076049
theorem B11086553 : Blo 1821612 11086553 := bstep (se 2 (by rfl) ⟨4157457, by rfl⟩ : syracuseStep 11086553 = 8314915) B8314915
theorem B3459827 : Blo 1821612 3459827 := bstep (se 1 (by rfl) ⟨2594870, by rfl⟩ : syracuseStep 3459827 = 5189741) B5189741
theorem B2050807 : Blo 1821612 2050807 := bstep (se 1 (by rfl) ⟨1538105, by rfl⟩ : syracuseStep 2050807 = 3076211) B3076211
theorem B3074827 : Blo 1821612 3074827 := bstep (se 1 (by rfl) ⟨2306120, by rfl⟩ : syracuseStep 3074827 = 4612241) B4612241
theorem B3001175 : Blo 1821612 3001175 := bstep (se 1 (by rfl) ⟨2250881, by rfl⟩ : syracuseStep 3001175 = 4501763) B4501763
theorem B4098905 : Blo 1821612 4098905 := bstep (se 2 (by rfl) ⟨1537089, by rfl⟩ : syracuseStep 4098905 = 3074179) B3074179
theorem B3074969 : Blo 1821612 3074969 := bstep (se 2 (by rfl) ⟨1153113, by rfl⟩ : syracuseStep 3074969 = 2306227) B2306227
theorem B2050987 : Blo 1821612 2050987 := bstep (se 1 (by rfl) ⟨1538240, by rfl⟩ : syracuseStep 2050987 = 3076481) B3076481
theorem B4098995 : Blo 1821612 4098995 := bstep (se 1 (by rfl) ⟨3074246, by rfl⟩ : syracuseStep 4098995 = 6148493) B6148493
theorem B1821623 : Blo 1821612 1821623 := bstep (se 1 (by rfl) ⟨1366217, by rfl⟩ : syracuseStep 1821623 = 2732435) B2732435
theorem B1821643 : Blo 1821612 1821643 := bstep (se 1 (by rfl) ⟨1366232, by rfl⟩ : syracuseStep 1821643 = 2732465) B2732465
theorem B1821655 : Blo 1821612 1821655 := bstep (se 1 (by rfl) ⟨1366241, by rfl⟩ : syracuseStep 1821655 = 2732483) B2732483
theorem B4099031 : Blo 1821612 4099031 := bstep (se 1 (by rfl) ⟨3074273, by rfl⟩ : syracuseStep 4099031 = 6148547) B6148547
theorem B1821675 : Blo 1821612 1821675 := bstep (se 1 (by rfl) ⟨1366256, by rfl⟩ : syracuseStep 1821675 = 2732513) B2732513
theorem B1821687 : Blo 1821612 1821687 := bstep (se 1 (by rfl) ⟨1366265, by rfl⟩ : syracuseStep 1821687 = 2732531) B2732531
theorem B1821707 : Blo 1821612 1821707 := bstep (se 1 (by rfl) ⟨1366280, by rfl⟩ : syracuseStep 1821707 = 2732561) B2732561
theorem B1821719 : Blo 1821612 1821719 := bstep (se 1 (by rfl) ⟨1366289, by rfl⟩ : syracuseStep 1821719 = 2732579) B2732579
theorem B2051095 : Blo 1821612 2051095 := bstep (se 1 (by rfl) ⟨1538321, by rfl⟩ : syracuseStep 2051095 = 3076643) B3076643
theorem B3075097 : Blo 1821612 3075097 := bstep (se 2 (by rfl) ⟨1153161, by rfl⟩ : syracuseStep 3075097 = 2306323) B2306323
theorem B1821739 : Blo 1821612 1821739 := bstep (se 1 (by rfl) ⟨1366304, by rfl⟩ : syracuseStep 1821739 = 2732609) B2732609
theorem B13847597 : Blo 1821612 13847597 := bstep (se 3 (by rfl) ⟨2596424, by rfl⟩ : syracuseStep 13847597 = 5192849) B5192849
theorem B1821751 : Blo 1821612 1821751 := bstep (se 1 (by rfl) ⟨1366313, by rfl⟩ : syracuseStep 1821751 = 2732627) B2732627
theorem B1821771 : Blo 1821612 1821771 := bstep (se 1 (by rfl) ⟨1366328, by rfl⟩ : syracuseStep 1821771 = 2732657) B2732657
theorem B1821783 : Blo 1821612 1821783 := bstep (se 1 (by rfl) ⟨1366337, by rfl⟩ : syracuseStep 1821783 = 2732675) B2732675
theorem B9227357 : Blo 1821612 9227357 := bstep (se 3 (by rfl) ⟨1730129, by rfl⟩ : syracuseStep 9227357 = 3460259) B3460259
theorem B1821803 : Blo 1821612 1821803 := bstep (se 1 (by rfl) ⟨1366352, by rfl⟩ : syracuseStep 1821803 = 2732705) B2732705
theorem B1821815 : Blo 1821612 1821815 := bstep (se 1 (by rfl) ⟨1366361, by rfl⟩ : syracuseStep 1821815 = 2732723) B2732723
theorem B1821835 : Blo 1821612 1821835 := bstep (se 1 (by rfl) ⟨1366376, by rfl⟩ : syracuseStep 1821835 = 2732753) B2732753
theorem B4099211 : Blo 1821612 4099211 := bstep (se 1 (by rfl) ⟨3074408, by rfl⟩ : syracuseStep 4099211 = 6148817) B6148817
theorem B4156555 : Blo 1821612 4156555 := bstep (se 1 (by rfl) ⟨3117416, by rfl⟩ : syracuseStep 4156555 = 6234833) B6234833
theorem B1821847 : Blo 1821612 1821847 := bstep (se 1 (by rfl) ⟨1366385, by rfl⟩ : syracuseStep 1821847 = 2732771) B2732771
theorem B4615319 : Blo 1821612 4615319 := bstep (se 1 (by rfl) ⟨3461489, by rfl⟩ : syracuseStep 4615319 = 6922979) B6922979
theorem B1821867 : Blo 1821612 1821867 := bstep (se 1 (by rfl) ⟨1366400, by rfl⟩ : syracuseStep 1821867 = 2732801) B2732801
theorem B1821879 : Blo 1821612 1821879 := bstep (se 1 (by rfl) ⟨1366409, by rfl⟩ : syracuseStep 1821879 = 2732819) B2732819
theorem B4099265 : Blo 1821612 4099265 := bstep (se 2 (by rfl) ⟨1537224, by rfl⟩ : syracuseStep 4099265 = 3074449) B3074449
theorem B1821899 : Blo 1821612 1821899 := bstep (se 1 (by rfl) ⟨1366424, by rfl⟩ : syracuseStep 1821899 = 2732849) B2732849
theorem B2051275 : Blo 1821612 2051275 := bstep (se 1 (by rfl) ⟨1538456, by rfl⟩ : syracuseStep 2051275 = 3076913) B3076913
theorem B1821911 : Blo 1821612 1821911 := bstep (se 1 (by rfl) ⟨1366433, by rfl⟩ : syracuseStep 1821911 = 2732867) B2732867
theorem B3460313 : Blo 1821612 3460313 := bstep (se 2 (by rfl) ⟨1297617, by rfl⟩ : syracuseStep 3460313 = 2595235) B2595235
theorem B11087065 : Blo 1821612 11087065 := bstep (se 2 (by rfl) ⟨4157649, by rfl⟩ : syracuseStep 11087065 = 8315299) B8315299
theorem B1821931 : Blo 1821612 1821931 := bstep (se 1 (by rfl) ⟨1366448, by rfl⟩ : syracuseStep 1821931 = 2732897) B2732897
theorem B1821943 : Blo 1821612 1821943 := bstep (se 1 (by rfl) ⟨1366457, by rfl⟩ : syracuseStep 1821943 = 2732915) B2732915
theorem B1821963 : Blo 1821612 1821963 := bstep (se 1 (by rfl) ⟨1366472, by rfl⟩ : syracuseStep 1821963 = 2732945) B2732945
theorem B2772235 : Blo 1821612 2772235 := bstep (se 1 (by rfl) ⟨2079176, by rfl⟩ : syracuseStep 2772235 = 4158353) B4158353
theorem B1821975 : Blo 1821612 1821975 := bstep (se 1 (by rfl) ⟨1366481, by rfl⟩ : syracuseStep 1821975 = 2732963) B2732963
theorem B1821995 : Blo 1821612 1821995 := bstep (se 1 (by rfl) ⟨1366496, by rfl⟩ : syracuseStep 1821995 = 2732993) B2732993
theorem B1822007 : Blo 1821612 1822007 := bstep (se 1 (by rfl) ⟨1366505, by rfl⟩ : syracuseStep 1822007 = 2733011) B2733011
theorem B2051383 : Blo 1821612 2051383 := bstep (se 1 (by rfl) ⟨1538537, by rfl⟩ : syracuseStep 2051383 = 3077075) B3077075
theorem B1822027 : Blo 1821612 1822027 := bstep (se 1 (by rfl) ⟨1366520, by rfl⟩ : syracuseStep 1822027 = 2733041) B2733041
theorem B1822039 : Blo 1821612 1822039 := bstep (se 1 (by rfl) ⟨1366529, by rfl⟩ : syracuseStep 1822039 = 2733059) B2733059
theorem B1822059 : Blo 1821612 1822059 := bstep (se 1 (by rfl) ⟨1366544, by rfl⟩ : syracuseStep 1822059 = 2733089) B2733089
theorem B1822071 : Blo 1821612 1822071 := bstep (se 1 (by rfl) ⟨1366553, by rfl⟩ : syracuseStep 1822071 = 2733107) B2733107
theorem B1822091 : Blo 1821612 1822091 := bstep (se 1 (by rfl) ⟨1366568, by rfl⟩ : syracuseStep 1822091 = 2733137) B2733137
theorem B1822103 : Blo 1821612 1822103 := bstep (se 1 (by rfl) ⟨1366577, by rfl⟩ : syracuseStep 1822103 = 2733155) B2733155
theorem B4378007 : Blo 1821612 4378007 := bstep (se 1 (by rfl) ⟨3283505, by rfl⟩ : syracuseStep 4378007 = 6567011) B6567011
theorem B4099481 : Blo 1821612 4099481 := bstep (se 2 (by rfl) ⟨1537305, by rfl⟩ : syracuseStep 4099481 = 3074611) B3074611
theorem B1822123 : Blo 1821612 1822123 := bstep (se 1 (by rfl) ⟨1366592, by rfl⟩ : syracuseStep 1822123 = 2733185) B2733185
theorem B1822135 : Blo 1821612 1822135 := bstep (se 1 (by rfl) ⟨1366601, by rfl⟩ : syracuseStep 1822135 = 2733203) B2733203
theorem B1822155 : Blo 1821612 1822155 := bstep (se 1 (by rfl) ⟨1366616, by rfl⟩ : syracuseStep 1822155 = 2733233) B2733233
theorem B13839821 : Blo 1821612 13839821 := bstep (se 3 (by rfl) ⟨2594966, by rfl⟩ : syracuseStep 13839821 = 5189933) B5189933
theorem B1822167 : Blo 1821612 1822167 := bstep (se 1 (by rfl) ⟨1366625, by rfl⟩ : syracuseStep 1822167 = 2733251) B2733251
theorem B1822187 : Blo 1821612 1822187 := bstep (se 1 (by rfl) ⟨1366640, by rfl⟩ : syracuseStep 1822187 = 2733281) B2733281
theorem B2051563 : Blo 1821612 2051563 := bstep (se 1 (by rfl) ⟨1538672, by rfl⟩ : syracuseStep 2051563 = 3077345) B3077345
theorem B4099571 : Blo 1821612 4099571 := bstep (se 1 (by rfl) ⟨3074678, by rfl⟩ : syracuseStep 4099571 = 6149357) B6149357
theorem B1822199 : Blo 1821612 1822199 := bstep (se 1 (by rfl) ⟨1366649, by rfl⟩ : syracuseStep 1822199 = 2733299) B2733299
theorem B1822219 : Blo 1821612 1822219 := bstep (se 1 (by rfl) ⟨1366664, by rfl⟩ : syracuseStep 1822219 = 2733329) B2733329
theorem B4099607 : Blo 1821612 4099607 := bstep (se 1 (by rfl) ⟨3074705, by rfl⟩ : syracuseStep 4099607 = 6149411) B6149411
theorem B1822231 : Blo 1821612 1822231 := bstep (se 1 (by rfl) ⟨1366673, by rfl⟩ : syracuseStep 1822231 = 2733347) B2733347
theorem B1822251 : Blo 1821612 1822251 := bstep (se 1 (by rfl) ⟨1366688, by rfl⟩ : syracuseStep 1822251 = 2733377) B2733377
theorem B7015987 : Blo 1821612 7015987 := bstep (se 1 (by rfl) ⟨5261990, by rfl⟩ : syracuseStep 7015987 = 10523981) B10523981
theorem B1822263 : Blo 1821612 1822263 := bstep (se 1 (by rfl) ⟨1366697, by rfl⟩ : syracuseStep 1822263 = 2733395) B2733395
theorem B1846859 : Blo 1821612 1846859 := bstep (se 1 (by rfl) ⟨1385144, by rfl⟩ : syracuseStep 1846859 = 2770289) B2770289
theorem B1822283 : Blo 1821612 1822283 := bstep (se 1 (by rfl) ⟨1366712, by rfl⟩ : syracuseStep 1822283 = 2733425) B2733425
theorem B1822295 : Blo 1821612 1822295 := bstep (se 1 (by rfl) ⟨1366721, by rfl⟩ : syracuseStep 1822295 = 2733443) B2733443
theorem B3075671 : Blo 1821612 3075671 := bstep (se 1 (by rfl) ⟨2306753, by rfl⟩ : syracuseStep 3075671 = 4613507) B4613507
theorem B1822315 : Blo 1821612 1822315 := bstep (se 1 (by rfl) ⟨1366736, by rfl⟩ : syracuseStep 1822315 = 2733473) B2733473
theorem B1822327 : Blo 1821612 1822327 := bstep (se 1 (by rfl) ⟨1366745, by rfl⟩ : syracuseStep 1822327 = 2733491) B2733491
theorem B7786115 : Blo 1821612 7786115 := bstep (se 1 (by rfl) ⟨5839586, by rfl⟩ : syracuseStep 7786115 = 11679173) B11679173
theorem B2305675 : Blo 1821612 2305675 := bstep (se 1 (by rfl) ⟨1729256, by rfl⟩ : syracuseStep 2305675 = 3458513) B3458513
theorem B1822347 : Blo 1821612 1822347 := bstep (se 1 (by rfl) ⟨1366760, by rfl⟩ : syracuseStep 1822347 = 2733521) B2733521
theorem B1822359 : Blo 1821612 1822359 := bstep (se 1 (by rfl) ⟨1366769, by rfl⟩ : syracuseStep 1822359 = 2733539) B2733539
theorem B1822379 : Blo 1821612 1822379 := bstep (se 1 (by rfl) ⟨1366784, by rfl⟩ : syracuseStep 1822379 = 2733569) B2733569
theorem B1822391 : Blo 1821612 1822391 := bstep (se 1 (by rfl) ⟨1366793, by rfl⟩ : syracuseStep 1822391 = 2733587) B2733587
theorem B4099787 : Blo 1821612 4099787 := bstep (se 1 (by rfl) ⟨3074840, by rfl⟩ : syracuseStep 4099787 = 6149681) B6149681
theorem B4378315 : Blo 1821612 4378315 := bstep (se 1 (by rfl) ⟨3283736, by rfl⟩ : syracuseStep 4378315 = 6567473) B6567473
theorem B1822411 : Blo 1821612 1822411 := bstep (se 1 (by rfl) ⟨1366808, by rfl⟩ : syracuseStep 1822411 = 2733617) B2733617
theorem B1822423 : Blo 1821612 1822423 := bstep (se 1 (by rfl) ⟨1366817, by rfl⟩ : syracuseStep 1822423 = 2733635) B2733635
theorem B3075799 : Blo 1821612 3075799 := bstep (se 1 (by rfl) ⟨2306849, by rfl⟩ : syracuseStep 3075799 = 4613699) B4613699
theorem B5189341 : Blo 1821612 5189341 := bstep (se 3 (by rfl) ⟨973001, by rfl⟩ : syracuseStep 5189341 = 1946003) B1946003
theorem B1822443 : Blo 1821612 1822443 := bstep (se 1 (by rfl) ⟨1366832, by rfl⟩ : syracuseStep 1822443 = 2733665) B2733665
theorem B37932785 : Blo 1821612 37932785 := bstep (se 2 (by rfl) ⟨14224794, by rfl⟩ : syracuseStep 37932785 = 28449589) B28449589
theorem B1822455 : Blo 1821612 1822455 := bstep (se 1 (by rfl) ⟨1366841, by rfl⟩ : syracuseStep 1822455 = 2733683) B2733683
theorem B4099841 : Blo 1821612 4099841 := bstep (se 2 (by rfl) ⟨1537440, by rfl⟩ : syracuseStep 4099841 = 3074881) B3074881
theorem B1822475 : Blo 1821612 1822475 := bstep (se 1 (by rfl) ⟨1366856, by rfl⟩ : syracuseStep 1822475 = 2733713) B2733713
theorem B1822487 : Blo 1821612 1822487 := bstep (se 1 (by rfl) ⟨1366865, by rfl⟩ : syracuseStep 1822487 = 2733731) B2733731
theorem B1822507 : Blo 1821612 1822507 := bstep (se 1 (by rfl) ⟨1366880, by rfl⟩ : syracuseStep 1822507 = 2733761) B2733761
theorem B4615987 : Blo 1821612 4615987 := bstep (se 1 (by rfl) ⟨3461990, by rfl⟩ : syracuseStep 4615987 = 6923981) B6923981
theorem B1822519 : Blo 1821612 1822519 := bstep (se 1 (by rfl) ⟨1366889, by rfl⟩ : syracuseStep 1822519 = 2733779) B2733779
theorem B1822539 : Blo 1821612 1822539 := bstep (se 1 (by rfl) ⟨1366904, by rfl⟩ : syracuseStep 1822539 = 2733809) B2733809
theorem B15576907 : Blo 1821612 15576907 := bstep (se 1 (by rfl) ⟨11682680, by rfl⟩ : syracuseStep 15576907 = 23365361) B23365361
theorem B1822551 : Blo 1821612 1822551 := bstep (se 1 (by rfl) ⟨1366913, by rfl⟩ : syracuseStep 1822551 = 2733827) B2733827
theorem B1822571 : Blo 1821612 1822571 := bstep (se 1 (by rfl) ⟨1366928, by rfl⟩ : syracuseStep 1822571 = 2733857) B2733857
theorem B1822583 : Blo 1821612 1822583 := bstep (se 1 (by rfl) ⟨1366937, by rfl⟩ : syracuseStep 1822583 = 2733875) B2733875
theorem B1822603 : Blo 1821612 1822603 := bstep (se 1 (by rfl) ⟨1366952, by rfl⟩ : syracuseStep 1822603 = 2733905) B2733905
theorem B1822615 : Blo 1821612 1822615 := bstep (se 1 (by rfl) ⟨1366961, by rfl⟩ : syracuseStep 1822615 = 2733923) B2733923
theorem B1822635 : Blo 1821612 1822635 := bstep (se 1 (by rfl) ⟨1366976, by rfl⟩ : syracuseStep 1822635 = 2733953) B2733953
theorem B13840307 : Blo 1821612 13840307 := bstep (se 1 (by rfl) ⟨10380230, by rfl⟩ : syracuseStep 13840307 = 20760461) B20760461
theorem B1822647 : Blo 1821612 1822647 := bstep (se 1 (by rfl) ⟨1366985, by rfl⟩ : syracuseStep 1822647 = 2733971) B2733971
theorem B1822667 : Blo 1821612 1822667 := bstep (se 1 (by rfl) ⟨1367000, by rfl⟩ : syracuseStep 1822667 = 2734001) B2734001
theorem B1945559 : Blo 1821612 1945559 := bstep (se 1 (by rfl) ⟨1459169, by rfl⟩ : syracuseStep 1945559 = 2918339) B2918339
theorem B1822679 : Blo 1821612 1822679 := bstep (se 1 (by rfl) ⟨1367009, by rfl⟩ : syracuseStep 1822679 = 2734019) B2734019
theorem B4100057 : Blo 1821612 4100057 := bstep (se 2 (by rfl) ⟨1537521, by rfl⟩ : syracuseStep 4100057 = 3075043) B3075043
theorem B6148061 : Blo 1821612 6148061 := bstep (se 3 (by rfl) ⟨1152761, by rfl⟩ : syracuseStep 6148061 = 2305523) B2305523
theorem B1822699 : Blo 1821612 1822699 := bstep (se 1 (by rfl) ⟨1367024, by rfl⟩ : syracuseStep 1822699 = 2734049) B2734049
theorem B1822711 : Blo 1821612 1822711 := bstep (se 1 (by rfl) ⟨1367033, by rfl⟩ : syracuseStep 1822711 = 2734067) B2734067
theorem B1822731 : Blo 1821612 1822731 := bstep (se 1 (by rfl) ⟨1367048, by rfl⟩ : syracuseStep 1822731 = 2734097) B2734097
theorem B1822743 : Blo 1821612 1822743 := bstep (se 1 (by rfl) ⟨1367057, by rfl⟩ : syracuseStep 1822743 = 2734115) B2734115
theorem B1822763 : Blo 1821612 1822763 := bstep (se 1 (by rfl) ⟨1367072, by rfl⟩ : syracuseStep 1822763 = 2734145) B2734145
theorem B4100147 : Blo 1821612 4100147 := bstep (se 1 (by rfl) ⟨3075110, by rfl⟩ : syracuseStep 4100147 = 6150221) B6150221
theorem B5189683 : Blo 1821612 5189683 := bstep (se 1 (by rfl) ⟨3892262, by rfl⟩ : syracuseStep 5189683 = 7784525) B7784525
theorem B1822775 : Blo 1821612 1822775 := bstep (se 1 (by rfl) ⟨1367081, by rfl⟩ : syracuseStep 1822775 = 2734163) B2734163
theorem B14774347 : Blo 1821612 14774347 := bstep (se 1 (by rfl) ⟨11080760, by rfl⟩ : syracuseStep 14774347 = 22161521) B22161521
theorem B4378699 : Blo 1821612 4378699 := bstep (se 1 (by rfl) ⟨3284024, by rfl⟩ : syracuseStep 4378699 = 6568049) B6568049
theorem B1822795 : Blo 1821612 1822795 := bstep (se 1 (by rfl) ⟨1367096, by rfl⟩ : syracuseStep 1822795 = 2734193) B2734193
theorem B4100183 : Blo 1821612 4100183 := bstep (se 1 (by rfl) ⟨3075137, by rfl⟩ : syracuseStep 4100183 = 6150275) B6150275
theorem B1822807 : Blo 1821612 1822807 := bstep (se 1 (by rfl) ⟨1367105, by rfl⟩ : syracuseStep 1822807 = 2734211) B2734211
theorem B15577181 : Blo 1821612 15577181 := bstep (se 3 (by rfl) ⟨2920721, by rfl⟩ : syracuseStep 15577181 = 5841443) B5841443
theorem B1822827 : Blo 1821612 1822827 := bstep (se 1 (by rfl) ⟨1367120, by rfl⟩ : syracuseStep 1822827 = 2734241) B2734241
theorem B1822839 : Blo 1821612 1822839 := bstep (se 1 (by rfl) ⟨1367129, by rfl⟩ : syracuseStep 1822839 = 2734259) B2734259
theorem B1822859 : Blo 1821612 1822859 := bstep (se 1 (by rfl) ⟨1367144, by rfl⟩ : syracuseStep 1822859 = 2734289) B2734289
theorem B1822871 : Blo 1821612 1822871 := bstep (se 1 (by rfl) ⟨1367153, by rfl⟩ : syracuseStep 1822871 = 2734307) B2734307
theorem B10383511 : Blo 1821612 10383511 := bstep (se 1 (by rfl) ⟨7787633, by rfl⟩ : syracuseStep 10383511 = 15575267) B15575267
theorem B1822891 : Blo 1821612 1822891 := bstep (se 1 (by rfl) ⟨1367168, by rfl⟩ : syracuseStep 1822891 = 2734337) B2734337
theorem B6918317 : Blo 1821612 6918317 := bstep (se 3 (by rfl) ⟨1297184, by rfl⟩ : syracuseStep 6918317 = 2594369) B2594369
theorem B1822903 : Blo 1821612 1822903 := bstep (se 1 (by rfl) ⟨1367177, by rfl⟩ : syracuseStep 1822903 = 2734355) B2734355
theorem B1822923 : Blo 1821612 1822923 := bstep (se 1 (by rfl) ⟨1367192, by rfl⟩ : syracuseStep 1822923 = 2734385) B2734385
theorem B1822935 : Blo 1821612 1822935 := bstep (se 1 (by rfl) ⟨1367201, by rfl⟩ : syracuseStep 1822935 = 2734403) B2734403
theorem B1822955 : Blo 1821612 1822955 := bstep (se 1 (by rfl) ⟨1367216, by rfl⟩ : syracuseStep 1822955 = 2734433) B2734433
theorem B1822967 : Blo 1821612 1822967 := bstep (se 1 (by rfl) ⟨1367225, by rfl⟩ : syracuseStep 1822967 = 2734451) B2734451
theorem B4100363 : Blo 1821612 4100363 := bstep (se 1 (by rfl) ⟨3075272, by rfl⟩ : syracuseStep 4100363 = 6150545) B6150545
theorem B1822987 : Blo 1821612 1822987 := bstep (se 1 (by rfl) ⟨1367240, by rfl⟩ : syracuseStep 1822987 = 2734481) B2734481
theorem B1822999 : Blo 1821612 1822999 := bstep (se 1 (by rfl) ⟨1367249, by rfl⟩ : syracuseStep 1822999 = 2734499) B2734499
theorem B1823019 : Blo 1821612 1823019 := bstep (se 1 (by rfl) ⟨1367264, by rfl⟩ : syracuseStep 1823019 = 2734529) B2734529
theorem B4378931 : Blo 1821612 4378931 := bstep (se 1 (by rfl) ⟨3284198, by rfl⟩ : syracuseStep 4378931 = 6568397) B6568397
theorem B1823031 : Blo 1821612 1823031 := bstep (se 1 (by rfl) ⟨1367273, by rfl⟩ : syracuseStep 1823031 = 2734547) B2734547
theorem B4100417 : Blo 1821612 4100417 := bstep (se 2 (by rfl) ⟨1537656, by rfl⟩ : syracuseStep 4100417 = 3075313) B3075313
theorem B1823051 : Blo 1821612 1823051 := bstep (se 1 (by rfl) ⟨1367288, by rfl⟩ : syracuseStep 1823051 = 2734577) B2734577
theorem B3076427 : Blo 1821612 3076427 := bstep (se 1 (by rfl) ⟨2307320, by rfl⟩ : syracuseStep 3076427 = 4614641) B4614641
theorem B1823063 : Blo 1821612 1823063 := bstep (se 1 (by rfl) ⟨1367297, by rfl⟩ : syracuseStep 1823063 = 2734595) B2734595
theorem B17518949 : Blo 1821612 17518949 := bstep (se 4 (by rfl) ⟨1642401, by rfl⟩ : syracuseStep 17518949 = 3284803) B3284803
theorem B1823083 : Blo 1821612 1823083 := bstep (se 1 (by rfl) ⟨1367312, by rfl⟩ : syracuseStep 1823083 = 2734625) B2734625
theorem B1823095 : Blo 1821612 1823095 := bstep (se 1 (by rfl) ⟨1367321, by rfl⟩ : syracuseStep 1823095 = 2734643) B2734643
theorem B1823115 : Blo 1821612 1823115 := bstep (se 1 (by rfl) ⟨1367336, by rfl⟩ : syracuseStep 1823115 = 2734673) B2734673
theorem B1823127 : Blo 1821612 1823127 := bstep (se 1 (by rfl) ⟨1367345, by rfl⟩ : syracuseStep 1823127 = 2734691) B2734691
theorem B2732441 : Blo 1821612 2732441 := bstep (se 2 (by rfl) ⟨1024665, by rfl⟩ : syracuseStep 2732441 = 2049331) B2049331
theorem B1823147 : Blo 1821612 1823147 := bstep (se 1 (by rfl) ⟨1367360, by rfl⟩ : syracuseStep 1823147 = 2734721) B2734721
theorem B23671217 : Blo 1821612 23671217 := bstep (se 2 (by rfl) ⟨8876706, by rfl⟩ : syracuseStep 23671217 = 17753413) B17753413
theorem B31134131 : Blo 1821612 31134131 := bstep (se 1 (by rfl) ⟨23350598, by rfl⟩ : syracuseStep 31134131 = 46701197) B46701197
theorem B1823159 : Blo 1821612 1823159 := bstep (se 1 (by rfl) ⟨1367369, by rfl⟩ : syracuseStep 1823159 = 2734739) B2734739
theorem B3076555 : Blo 1821612 3076555 := bstep (se 1 (by rfl) ⟨2307416, by rfl⟩ : syracuseStep 3076555 = 4614833) B4614833
theorem B1823179 : Blo 1821612 1823179 := bstep (se 1 (by rfl) ⟨1367384, by rfl⟩ : syracuseStep 1823179 = 2734769) B2734769
theorem B1823191 : Blo 1821612 1823191 := bstep (se 1 (by rfl) ⟨1367393, by rfl⟩ : syracuseStep 1823191 = 2734787) B2734787
theorem B5476829 : Blo 1821612 5476829 := bstep (se 3 (by rfl) ⟨1026905, by rfl⟩ : syracuseStep 5476829 = 2053811) B2053811
theorem B1823211 : Blo 1821612 1823211 := bstep (se 1 (by rfl) ⟨1367408, by rfl⟩ : syracuseStep 1823211 = 2734817) B2734817
theorem B1823223 : Blo 1821612 1823223 := bstep (se 1 (by rfl) ⟨1367417, by rfl⟩ : syracuseStep 1823223 = 2734835) B2734835
theorem B2732555 : Blo 1821612 2732555 := bstep (se 1 (by rfl) ⟨2049416, by rfl⟩ : syracuseStep 2732555 = 4098833) B4098833
theorem B1823243 : Blo 1821612 1823243 := bstep (se 1 (by rfl) ⟨1367432, by rfl⟩ : syracuseStep 1823243 = 2734865) B2734865
theorem B2732567 : Blo 1821612 2732567 := bstep (se 1 (by rfl) ⟨2049425, by rfl⟩ : syracuseStep 2732567 = 4098851) B4098851
theorem B1823255 : Blo 1821612 1823255 := bstep (se 1 (by rfl) ⟨1367441, by rfl⟩ : syracuseStep 1823255 = 2734883) B2734883
theorem B4100633 : Blo 1821612 4100633 := bstep (se 2 (by rfl) ⟨1537737, by rfl⟩ : syracuseStep 4100633 = 3075475) B3075475
theorem B1823275 : Blo 1821612 1823275 := bstep (se 1 (by rfl) ⟨1367456, by rfl⟩ : syracuseStep 1823275 = 2734913) B2734913
theorem B1823287 : Blo 1821612 1823287 := bstep (se 1 (by rfl) ⟨1367465, by rfl⟩ : syracuseStep 1823287 = 2734931) B2734931
theorem B1823307 : Blo 1821612 1823307 := bstep (se 1 (by rfl) ⟨1367480, by rfl⟩ : syracuseStep 1823307 = 2734961) B2734961
theorem B2306647 : Blo 1821612 2306647 := bstep (se 1 (by rfl) ⟨1729985, by rfl⟩ : syracuseStep 2306647 = 3459971) B3459971
theorem B2732633 : Blo 1821612 2732633 := bstep (se 2 (by rfl) ⟨1024737, by rfl⟩ : syracuseStep 2732633 = 2049475) B2049475
theorem B3076697 : Blo 1821612 3076697 := bstep (se 2 (by rfl) ⟨1153761, by rfl⟩ : syracuseStep 3076697 = 2307523) B2307523
theorem B1823319 : Blo 1821612 1823319 := bstep (se 1 (by rfl) ⟨1367489, by rfl⟩ : syracuseStep 1823319 = 2734979) B2734979
theorem B1823339 : Blo 1821612 1823339 := bstep (se 1 (by rfl) ⟨1367504, by rfl⟩ : syracuseStep 1823339 = 2735009) B2735009
theorem B4100723 : Blo 1821612 4100723 := bstep (se 1 (by rfl) ⟨3075542, by rfl⟩ : syracuseStep 4100723 = 6151085) B6151085
theorem B1823351 : Blo 1821612 1823351 := bstep (se 1 (by rfl) ⟨1367513, by rfl⟩ : syracuseStep 1823351 = 2735027) B2735027
theorem B1823371 : Blo 1821612 1823371 := bstep (se 1 (by rfl) ⟨1367528, by rfl⟩ : syracuseStep 1823371 = 2735057) B2735057
theorem B3461771 : Blo 1821612 3461771 := bstep (se 1 (by rfl) ⟨2596328, by rfl⟩ : syracuseStep 3461771 = 5192657) B5192657
theorem B4100759 : Blo 1821612 4100759 := bstep (se 1 (by rfl) ⟨3075569, by rfl⟩ : syracuseStep 4100759 = 6151139) B6151139
theorem B1823383 : Blo 1821612 1823383 := bstep (se 1 (by rfl) ⟨1367537, by rfl⟩ : syracuseStep 1823383 = 2735075) B2735075
theorem B1823403 : Blo 1821612 1823403 := bstep (se 1 (by rfl) ⟨1367552, by rfl⟩ : syracuseStep 1823403 = 2735105) B2735105
theorem B1823415 : Blo 1821612 1823415 := bstep (se 1 (by rfl) ⟨1367561, by rfl⟩ : syracuseStep 1823415 = 2735123) B2735123
theorem B2732747 : Blo 1821612 2732747 := bstep (se 1 (by rfl) ⟨2049560, by rfl⟩ : syracuseStep 2732747 = 4099121) B4099121
theorem B1823435 : Blo 1821612 1823435 := bstep (se 1 (by rfl) ⟨1367576, by rfl⟩ : syracuseStep 1823435 = 2735153) B2735153
theorem B2732759 : Blo 1821612 2732759 := bstep (se 1 (by rfl) ⟨2049569, by rfl⟩ : syracuseStep 2732759 = 4099139) B4099139
theorem B1823447 : Blo 1821612 1823447 := bstep (se 1 (by rfl) ⟨1367585, by rfl⟩ : syracuseStep 1823447 = 2735171) B2735171
theorem B3076825 : Blo 1821612 3076825 := bstep (se 2 (by rfl) ⟨1153809, by rfl⟩ : syracuseStep 3076825 = 2307619) B2307619
theorem B1823467 : Blo 1821612 1823467 := bstep (se 1 (by rfl) ⟨1367600, by rfl⟩ : syracuseStep 1823467 = 2735201) B2735201
theorem B1823479 : Blo 1821612 1823479 := bstep (se 1 (by rfl) ⟨1367609, by rfl⟩ : syracuseStep 1823479 = 2735219) B2735219
theorem B7492355 : Blo 1821612 7492355 := bstep (se 1 (by rfl) ⟨5619266, by rfl⟩ : syracuseStep 7492355 = 11238533) B11238533
theorem B1823499 : Blo 1821612 1823499 := bstep (se 1 (by rfl) ⟨1367624, by rfl⟩ : syracuseStep 1823499 = 2735249) B2735249
theorem B1823511 : Blo 1821612 1823511 := bstep (se 1 (by rfl) ⟨1367633, by rfl⟩ : syracuseStep 1823511 = 2735267) B2735267
theorem B2732825 : Blo 1821612 2732825 := bstep (se 2 (by rfl) ⟨1024809, by rfl⟩ : syracuseStep 2732825 = 2049619) B2049619
theorem B1848107 : Blo 1821612 1848107 := bstep (se 1 (by rfl) ⟨1386080, by rfl⟩ : syracuseStep 1848107 = 2772161) B2772161
theorem B1823531 : Blo 1821612 1823531 := bstep (se 1 (by rfl) ⟨1367648, by rfl⟩ : syracuseStep 1823531 = 2735297) B2735297
theorem B1823543 : Blo 1821612 1823543 := bstep (se 1 (by rfl) ⟨1367657, by rfl⟩ : syracuseStep 1823543 = 2735315) B2735315
theorem B3461953 : Blo 1821612 3461953 := bstep (se 2 (by rfl) ⟨1298232, by rfl⟩ : syracuseStep 3461953 = 2596465) B2596465
theorem B4100939 : Blo 1821612 4100939 := bstep (se 1 (by rfl) ⟨3075704, by rfl⟩ : syracuseStep 4100939 = 6151409) B6151409
theorem B1823563 : Blo 1821612 1823563 := bstep (se 1 (by rfl) ⟨1367672, by rfl⟩ : syracuseStep 1823563 = 2735345) B2735345
theorem B1823575 : Blo 1821612 1823575 := bstep (se 1 (by rfl) ⟨1367681, by rfl⟩ : syracuseStep 1823575 = 2735363) B2735363
theorem B16634717 : Blo 1821612 16634717 := bstep (se 3 (by rfl) ⟨3119009, by rfl⟩ : syracuseStep 16634717 = 6238019) B6238019
theorem B1823595 : Blo 1821612 1823595 := bstep (se 1 (by rfl) ⟨1367696, by rfl⟩ : syracuseStep 1823595 = 2735393) B2735393
theorem B1823607 : Blo 1821612 1823607 := bstep (se 1 (by rfl) ⟨1367705, by rfl⟩ : syracuseStep 1823607 = 2735411) B2735411
theorem B4100993 : Blo 1821612 4100993 := bstep (se 2 (by rfl) ⟨1537872, by rfl⟩ : syracuseStep 4100993 = 3075745) B3075745
theorem B2732939 : Blo 1821612 2732939 := bstep (se 1 (by rfl) ⟨2049704, by rfl⟩ : syracuseStep 2732939 = 4099409) B4099409
theorem B2732951 : Blo 1821612 2732951 := bstep (se 1 (by rfl) ⟨2049713, by rfl⟩ : syracuseStep 2732951 = 4099427) B4099427
theorem B6919091 : Blo 1821612 6919091 := bstep (se 1 (by rfl) ⟨5189318, by rfl⟩ : syracuseStep 6919091 = 10378637) B10378637
theorem B2733017 : Blo 1821612 2733017 := bstep (se 2 (by rfl) ⟨1024881, by rfl⟩ : syracuseStep 2733017 = 2049763) B2049763
theorem B5190617 : Blo 1821612 5190617 := bstep (se 2 (by rfl) ⟨1946481, by rfl⟩ : syracuseStep 5190617 = 3892963) B3892963
theorem B1946635 : Blo 1821612 1946635 := bstep (se 1 (by rfl) ⟨1459976, by rfl⟩ : syracuseStep 1946635 = 2919953) B2919953
theorem B6149195 : Blo 1821612 6149195 := bstep (se 1 (by rfl) ⟨4611896, by rfl⟩ : syracuseStep 6149195 = 9223793) B9223793
theorem B2733131 : Blo 1821612 2733131 := bstep (se 1 (by rfl) ⟨2049848, by rfl⟩ : syracuseStep 2733131 = 4099697) B4099697
theorem B2733143 : Blo 1821612 2733143 := bstep (se 1 (by rfl) ⟨2049857, by rfl⟩ : syracuseStep 2733143 = 4099715) B4099715
theorem B4101209 : Blo 1821612 4101209 := bstep (se 2 (by rfl) ⟨1537953, by rfl⟩ : syracuseStep 4101209 = 3075907) B3075907
theorem B15578243 : Blo 1821612 15578243 := bstep (se 1 (by rfl) ⟨11683682, by rfl⟩ : syracuseStep 15578243 = 23367365) B23367365
theorem B9229463 : Blo 1821612 9229463 := bstep (se 1 (by rfl) ⟨6922097, by rfl⟩ : syracuseStep 9229463 = 13844195) B13844195
theorem B2733209 : Blo 1821612 2733209 := bstep (se 2 (by rfl) ⟨1024953, by rfl⟩ : syracuseStep 2733209 = 2049907) B2049907
theorem B4101299 : Blo 1821612 4101299 := bstep (se 1 (by rfl) ⟨3075974, by rfl⟩ : syracuseStep 4101299 = 6151949) B6151949
theorem B4101335 : Blo 1821612 4101335 := bstep (se 1 (by rfl) ⟨3076001, by rfl⟩ : syracuseStep 4101335 = 6152003) B6152003
theorem B2733323 : Blo 1821612 2733323 := bstep (se 1 (by rfl) ⟨2049992, by rfl⟩ : syracuseStep 2733323 = 4099985) B4099985
theorem B2462987 : Blo 1821612 2462987 := bstep (se 1 (by rfl) ⟨1847240, by rfl⟩ : syracuseStep 2462987 = 3694481) B3694481
theorem B2733335 : Blo 1821612 2733335 := bstep (se 1 (by rfl) ⟨2050001, by rfl⟩ : syracuseStep 2733335 = 4100003) B4100003
theorem B4379969 : Blo 1821612 4379969 := bstep (se 2 (by rfl) ⟨1642488, by rfl⟩ : syracuseStep 4379969 = 3284977) B3284977
theorem B13137227 : Blo 1821612 13137227 := bstep (se 1 (by rfl) ⟨9852920, by rfl⟩ : syracuseStep 13137227 = 19705841) B19705841
theorem B6149465 : Blo 1821612 6149465 := bstep (se 2 (by rfl) ⟨2306049, by rfl⟩ : syracuseStep 6149465 = 4612099) B4612099
theorem B2733401 : Blo 1821612 2733401 := bstep (se 2 (by rfl) ⟨1025025, by rfl⟩ : syracuseStep 2733401 = 2050051) B2050051
theorem B13841765 : Blo 1821612 13841765 := bstep (se 4 (by rfl) ⟨1297665, by rfl⟩ : syracuseStep 13841765 = 2595331) B2595331
theorem B4101515 : Blo 1821612 4101515 := bstep (se 1 (by rfl) ⟨3076136, by rfl⟩ : syracuseStep 4101515 = 6152273) B6152273
theorem B2307467 : Blo 1821612 2307467 := bstep (se 1 (by rfl) ⟨1730600, by rfl⟩ : syracuseStep 2307467 = 3461201) B3461201
theorem B4380083 : Blo 1821612 4380083 := bstep (se 1 (by rfl) ⟨3285062, by rfl⟩ : syracuseStep 4380083 = 6570125) B6570125
theorem B4101569 : Blo 1821612 4101569 := bstep (se 2 (by rfl) ⟨1538088, by rfl⟩ : syracuseStep 4101569 = 3076177) B3076177
theorem B2733515 : Blo 1821612 2733515 := bstep (se 1 (by rfl) ⟨2050136, by rfl⟩ : syracuseStep 2733515 = 4100273) B4100273
theorem B2733527 : Blo 1821612 2733527 := bstep (se 1 (by rfl) ⟨2050145, by rfl⟩ : syracuseStep 2733527 = 4100291) B4100291
theorem B2733593 : Blo 1821612 2733593 := bstep (se 2 (by rfl) ⟨1025097, by rfl⟩ : syracuseStep 2733593 = 2050195) B2050195
theorem B2463257 : Blo 1821612 2463257 := bstep (se 2 (by rfl) ⟨923721, by rfl⟩ : syracuseStep 2463257 = 1847443) B1847443
theorem B4159063 : Blo 1821612 4159063 := bstep (se 1 (by rfl) ⟨3119297, by rfl⟩ : syracuseStep 4159063 = 6238595) B6238595
theorem B2594443 : Blo 1821612 2594443 := bstep (se 1 (by rfl) ⟨1945832, by rfl⟩ : syracuseStep 2594443 = 3891665) B3891665
theorem B2733707 : Blo 1821612 2733707 := bstep (se 1 (by rfl) ⟨2050280, by rfl⟩ : syracuseStep 2733707 = 4100561) B4100561
theorem B2733719 : Blo 1821612 2733719 := bstep (se 1 (by rfl) ⟨2050289, by rfl⟩ : syracuseStep 2733719 = 4100579) B4100579
theorem B4101785 : Blo 1821612 4101785 := bstep (se 2 (by rfl) ⟨1538169, by rfl⟩ : syracuseStep 4101785 = 3076339) B3076339
theorem B2733785 : Blo 1821612 2733785 := bstep (se 2 (by rfl) ⟨1025169, by rfl⟩ : syracuseStep 2733785 = 2050339) B2050339
theorem B4101875 : Blo 1821612 4101875 := bstep (se 1 (by rfl) ⟨3076406, by rfl⟩ : syracuseStep 4101875 = 6152813) B6152813
theorem B13833989 : Blo 1821612 13833989 := bstep (se 4 (by rfl) ⟨1296936, by rfl⟩ : syracuseStep 13833989 = 2593873) B2593873
theorem B4101911 : Blo 1821612 4101911 := bstep (se 1 (by rfl) ⟨3076433, by rfl⟩ : syracuseStep 4101911 = 6152867) B6152867
theorem B2733899 : Blo 1821612 2733899 := bstep (se 1 (by rfl) ⟨2050424, by rfl⟩ : syracuseStep 2733899 = 4100849) B4100849
theorem B13842251 : Blo 1821612 13842251 := bstep (se 1 (by rfl) ⟨10381688, by rfl⟩ : syracuseStep 13842251 = 20763377) B20763377
theorem B2733911 : Blo 1821612 2733911 := bstep (se 1 (by rfl) ⟨2050433, by rfl⟩ : syracuseStep 2733911 = 4100867) B4100867
theorem B2733977 : Blo 1821612 2733977 := bstep (se 2 (by rfl) ⟨1025241, by rfl⟩ : syracuseStep 2733977 = 2050483) B2050483
theorem B4102091 : Blo 1821612 4102091 := bstep (se 1 (by rfl) ⟨3076568, by rfl⟩ : syracuseStep 4102091 = 6153137) B6153137
theorem B15570893 : Blo 1821612 15570893 := bstep (se 3 (by rfl) ⟨2919542, by rfl⟩ : syracuseStep 15570893 = 5839085) B5839085
theorem B28063705 : Blo 1821612 28063705 := bstep (se 2 (by rfl) ⟨10523889, by rfl⟩ : syracuseStep 28063705 = 21047779) B21047779
theorem B4102145 : Blo 1821612 4102145 := bstep (se 2 (by rfl) ⟨1538304, by rfl⟩ : syracuseStep 4102145 = 3076609) B3076609
theorem B2734091 : Blo 1821612 2734091 := bstep (se 1 (by rfl) ⟨2050568, by rfl⟩ : syracuseStep 2734091 = 4101137) B4101137
theorem B6150167 : Blo 1821612 6150167 := bstep (se 1 (by rfl) ⟨4612625, by rfl⟩ : syracuseStep 6150167 = 9225251) B9225251
theorem B2734103 : Blo 1821612 2734103 := bstep (se 1 (by rfl) ⟨2050577, by rfl⟩ : syracuseStep 2734103 = 4101155) B4101155
theorem B2734169 : Blo 1821612 2734169 := bstep (se 2 (by rfl) ⟨1025313, by rfl⟩ : syracuseStep 2734169 = 2050627) B2050627
theorem B3119243 : Blo 1821612 3119243 := bstep (se 1 (by rfl) ⟨2339432, by rfl⟩ : syracuseStep 3119243 = 4678865) B4678865
theorem B2463895 : Blo 1821612 2463895 := bstep (se 1 (by rfl) ⟨1847921, by rfl⟩ : syracuseStep 2463895 = 3695843) B3695843
theorem B2734283 : Blo 1821612 2734283 := bstep (se 1 (by rfl) ⟨2050712, by rfl⟩ : syracuseStep 2734283 = 4101425) B4101425
theorem B2734295 : Blo 1821612 2734295 := bstep (se 1 (by rfl) ⟨2050721, by rfl⟩ : syracuseStep 2734295 = 4101443) B4101443
theorem B4102361 : Blo 1821612 4102361 := bstep (se 2 (by rfl) ⟨1538385, by rfl⟩ : syracuseStep 4102361 = 3076771) B3076771
theorem B3283211 : Blo 1821612 3283211 := bstep (se 1 (by rfl) ⟨2462408, by rfl⟩ : syracuseStep 3283211 = 4924817) B4924817
theorem B3160343 : Blo 1821612 3160343 := bstep (se 1 (by rfl) ⟨2370257, by rfl⟩ : syracuseStep 3160343 = 4740515) B4740515
theorem B2734361 : Blo 1821612 2734361 := bstep (se 2 (by rfl) ⟨1025385, by rfl⟩ : syracuseStep 2734361 = 2050771) B2050771
theorem B4102451 : Blo 1821612 4102451 := bstep (se 1 (by rfl) ⟨3076838, by rfl⟩ : syracuseStep 4102451 = 6153677) B6153677
theorem B4102487 : Blo 1821612 4102487 := bstep (se 1 (by rfl) ⟨3076865, by rfl⟩ : syracuseStep 4102487 = 6153731) B6153731
theorem B5192029 : Blo 1821612 5192029 := bstep (se 3 (by rfl) ⟨973505, by rfl⟩ : syracuseStep 5192029 = 1947011) B1947011
theorem B9853285 : Blo 1821612 9853285 := bstep (se 4 (by rfl) ⟨923745, by rfl⟩ : syracuseStep 9853285 = 1847491) B1847491
theorem B6920579 : Blo 1821612 6920579 := bstep (se 1 (by rfl) ⟨5190434, by rfl⟩ : syracuseStep 6920579 = 10380869) B10380869
theorem B2734475 : Blo 1821612 2734475 := bstep (se 1 (by rfl) ⟨2050856, by rfl⟩ : syracuseStep 2734475 = 4101713) B4101713
theorem B2734487 : Blo 1821612 2734487 := bstep (se 1 (by rfl) ⟨2050865, by rfl⟩ : syracuseStep 2734487 = 4101731) B4101731
theorem B2734553 : Blo 1821612 2734553 := bstep (se 2 (by rfl) ⟨1025457, by rfl⟩ : syracuseStep 2734553 = 2050915) B2050915
theorem B4102667 : Blo 1821612 4102667 := bstep (se 1 (by rfl) ⟨3077000, by rfl⟩ : syracuseStep 4102667 = 6154001) B6154001
theorem B2218519 : Blo 1821612 2218519 := bstep (se 1 (by rfl) ⟨1663889, by rfl⟩ : syracuseStep 2218519 = 3327779) B3327779
theorem B6150707 : Blo 1821612 6150707 := bstep (se 1 (by rfl) ⟨4613030, by rfl⟩ : syracuseStep 6150707 = 9226061) B9226061
theorem B5192257 : Blo 1821612 5192257 := bstep (se 2 (by rfl) ⟨1947096, by rfl⟩ : syracuseStep 5192257 = 3894193) B3894193
theorem B4102721 : Blo 1821612 4102721 := bstep (se 2 (by rfl) ⟨1538520, by rfl⟩ : syracuseStep 4102721 = 3077041) B3077041
theorem B2734667 : Blo 1821612 2734667 := bstep (se 1 (by rfl) ⟨2051000, by rfl⟩ : syracuseStep 2734667 = 4102001) B4102001
theorem B2734679 : Blo 1821612 2734679 := bstep (se 1 (by rfl) ⟨2051009, by rfl⟩ : syracuseStep 2734679 = 4102019) B4102019
theorem B7494275 : Blo 1821612 7494275 := bstep (se 1 (by rfl) ⟨5620706, by rfl⟩ : syracuseStep 7494275 = 11241413) B11241413
theorem B2734745 : Blo 1821612 2734745 := bstep (se 2 (by rfl) ⟨1025529, by rfl⟩ : syracuseStep 2734745 = 2051059) B2051059
theorem B70032113 : Blo 1821612 70032113 := bstep (se 2 (by rfl) ⟨26262042, by rfl⟩ : syracuseStep 70032113 = 52524085) B52524085
theorem B2734859 : Blo 1821612 2734859 := bstep (se 1 (by rfl) ⟨2051144, by rfl⟩ : syracuseStep 2734859 = 4102289) B4102289
theorem B10525457 : Blo 1821612 10525457 := bstep (se 2 (by rfl) ⟨3947046, by rfl⟩ : syracuseStep 10525457 = 7894093) B7894093
theorem B2734871 : Blo 1821612 2734871 := bstep (se 1 (by rfl) ⟨2051153, by rfl⟩ : syracuseStep 2734871 = 4102307) B4102307
theorem B4102937 : Blo 1821612 4102937 := bstep (se 2 (by rfl) ⟨1538601, by rfl⟩ : syracuseStep 4102937 = 3077203) B3077203
theorem B13130561 : Blo 1821612 13130561 := bstep (se 2 (by rfl) ⟨4923960, by rfl⟩ : syracuseStep 13130561 = 9847921) B9847921
theorem B6150977 : Blo 1821612 6150977 := bstep (se 2 (by rfl) ⟨2306616, by rfl⟩ : syracuseStep 6150977 = 4613233) B4613233
theorem B4438849 : Blo 1821612 4438849 := bstep (se 2 (by rfl) ⟨1664568, by rfl⟩ : syracuseStep 4438849 = 3329137) B3329137
theorem B6921035 : Blo 1821612 6921035 := bstep (se 1 (by rfl) ⟨5190776, by rfl⟩ : syracuseStep 6921035 = 10381553) B10381553
theorem B2595673 : Blo 1821612 2595673 := bstep (se 2 (by rfl) ⟨973377, by rfl⟩ : syracuseStep 2595673 = 1946755) B1946755
theorem B2734937 : Blo 1821612 2734937 := bstep (se 2 (by rfl) ⟨1025601, by rfl⟩ : syracuseStep 2734937 = 2051203) B2051203
theorem B4103027 : Blo 1821612 4103027 := bstep (se 1 (by rfl) ⟨3077270, by rfl⟩ : syracuseStep 4103027 = 6154541) B6154541
theorem B5192599 : Blo 1821612 5192599 := bstep (se 1 (by rfl) ⟨3894449, by rfl⟩ : syracuseStep 5192599 = 7788899) B7788899
theorem B4103063 : Blo 1821612 4103063 := bstep (se 1 (by rfl) ⟨3077297, by rfl⟩ : syracuseStep 4103063 = 6154595) B6154595
theorem B7011245 : Blo 1821612 7011245 := bstep (se 3 (by rfl) ⟨1314608, by rfl⟩ : syracuseStep 7011245 = 2629217) B2629217
theorem B2735051 : Blo 1821612 2735051 := bstep (se 1 (by rfl) ⟨2051288, by rfl⟩ : syracuseStep 2735051 = 4102577) B4102577
theorem B2735063 : Blo 1821612 2735063 := bstep (se 1 (by rfl) ⟨2051297, by rfl⟩ : syracuseStep 2735063 = 4102595) B4102595
theorem B6921233 : Blo 1821612 6921233 := bstep (se 2 (by rfl) ⟨2595462, by rfl⟩ : syracuseStep 6921233 = 5190925) B5190925
theorem B2735129 : Blo 1821612 2735129 := bstep (se 2 (by rfl) ⟨1025673, by rfl⟩ : syracuseStep 2735129 = 2051347) B2051347
theorem B7887917 : Blo 1821612 7887917 := bstep (se 3 (by rfl) ⟨1478984, by rfl⟩ : syracuseStep 7887917 = 2957969) B2957969
theorem B3693619 : Blo 1821612 3693619 := bstep (se 1 (by rfl) ⟨2770214, by rfl⟩ : syracuseStep 3693619 = 5540429) B5540429
theorem B52542539 : Blo 1821612 52542539 := bstep (se 1 (by rfl) ⟨39406904, by rfl⟩ : syracuseStep 52542539 = 78813809) B78813809
theorem B2735243 : Blo 1821612 2735243 := bstep (se 1 (by rfl) ⟨2051432, by rfl⟩ : syracuseStep 2735243 = 4102865) B4102865
theorem B2735255 : Blo 1821612 2735255 := bstep (se 1 (by rfl) ⟨2051441, by rfl⟩ : syracuseStep 2735255 = 4102883) B4102883
theorem B4611289 : Blo 1821612 4611289 := bstep (se 2 (by rfl) ⟨1729233, by rfl⟩ : syracuseStep 4611289 = 3458467) B3458467
theorem B2735321 : Blo 1821612 2735321 := bstep (se 2 (by rfl) ⟨1025745, by rfl⟩ : syracuseStep 2735321 = 2051491) B2051491
theorem B9223469 : Blo 1821612 9223469 := bstep (se 3 (by rfl) ⟨1729400, by rfl⟩ : syracuseStep 9223469 = 3458801) B3458801
theorem B9985355 : Blo 1821612 9985355 := bstep (se 1 (by rfl) ⟨7489016, by rfl⟩ : syracuseStep 9985355 = 14978033) B14978033
theorem B6151517 : Blo 1821612 6151517 := bstep (se 3 (by rfl) ⟨1153409, by rfl⟩ : syracuseStep 6151517 = 2306819) B2306819
theorem B7781825 : Blo 1821612 7781825 := bstep (se 2 (by rfl) ⟨2918184, by rfl⟩ : syracuseStep 7781825 = 5836369) B5836369
theorem B14786225 : Blo 1821612 14786225 := bstep (se 2 (by rfl) ⟨5544834, by rfl⟩ : syracuseStep 14786225 = 11089669) B11089669
theorem B3284659 : Blo 1821612 3284659 := bstep (se 1 (by rfl) ⟨2463494, by rfl⟩ : syracuseStep 3284659 = 4926989) B4926989
theorem B29556485 : Blo 1821612 29556485 := bstep (se 4 (by rfl) ⟨2770920, by rfl⟩ : syracuseStep 29556485 = 5541841) B5541841
theorem B26287877 : Blo 1821612 26287877 := bstep (se 4 (by rfl) ⟨2464488, by rfl⟩ : syracuseStep 26287877 = 4928977) B4928977
theorem B6922007 : Blo 1821612 6922007 := bstep (se 1 (by rfl) ⟨5191505, by rfl⟩ : syracuseStep 6922007 = 10383011) B10383011
theorem B3506009 : Blo 1821612 3506009 := bstep (se 2 (by rfl) ⟨1314753, by rfl⟩ : syracuseStep 3506009 = 2629507) B2629507
theorem B3891083 : Blo 1821612 3891083 := bstep (se 1 (by rfl) ⟨2918312, by rfl⟩ : syracuseStep 3891083 = 5836625) B5836625
theorem B6922205 : Blo 1821612 6922205 := bstep (se 3 (by rfl) ⟨1297913, by rfl⟩ : syracuseStep 6922205 = 2595827) B2595827
theorem B7389251 : Blo 1821612 7389251 := bstep (se 1 (by rfl) ⟨5541938, by rfl⟩ : syracuseStep 7389251 = 11083877) B11083877
theorem B9224279 : Blo 1821612 9224279 := bstep (se 1 (by rfl) ⟨6918209, by rfl⟩ : syracuseStep 9224279 = 13836419) B13836419
theorem B4612211 : Blo 1821612 4612211 := bstep (se 1 (by rfl) ⟨3459158, by rfl⟩ : syracuseStep 4612211 = 6918317) B6918317
theorem B3285193 : Blo 1821612 3285193 := bstep (se 2 (by rfl) ⟨1231947, by rfl⟩ : syracuseStep 3285193 = 2463895) B2463895
theorem B13844681 : Blo 1821612 13844681 := bstep (se 2 (by rfl) ⟨5191755, by rfl⟩ : syracuseStep 13844681 = 10383511) B10383511
theorem B6922705 : Blo 1821612 6922705 := bstep (se 2 (by rfl) ⟨2596014, by rfl⟩ : syracuseStep 6922705 = 5192029) B5192029
theorem B9224765 : Blo 1821612 9224765 := bstep (se 3 (by rfl) ⟨1729643, by rfl⟩ : syracuseStep 9224765 = 3459287) B3459287
theorem B4612727 : Blo 1821612 4612727 := bstep (se 1 (by rfl) ⟨3459545, by rfl⟩ : syracuseStep 4612727 = 6919091) B6919091
theorem B2958025 : Blo 1821612 2958025 := bstep (se 2 (by rfl) ⟨1109259, by rfl⟩ : syracuseStep 2958025 = 2218519) B2218519
theorem B6923009 : Blo 1821612 6923009 := bstep (se 2 (by rfl) ⟨2596128, by rfl⟩ : syracuseStep 6923009 = 5192257) B5192257
theorem B6152975 : Blo 1821612 6152975 := bstep (se 1 (by rfl) ⟨4614731, by rfl⟩ : syracuseStep 6152975 = 9229463) B9229463
theorem B18998065 : Blo 1821612 18998065 := bstep (se 2 (by rfl) ⟨7124274, by rfl⟩ : syracuseStep 18998065 = 14248549) B14248549
theorem B8758151 : Blo 1821612 8758151 := bstep (se 1 (by rfl) ⟨6568613, by rfl⟩ : syracuseStep 8758151 = 13137227) B13137227
theorem B6153245 : Blo 1821612 6153245 := bstep (se 3 (by rfl) ⟨1153733, by rfl⟩ : syracuseStep 6153245 = 2307467) B2307467
theorem B11674685 : Blo 1821612 11674685 := bstep (se 3 (by rfl) ⟨2189003, by rfl⟩ : syracuseStep 11674685 = 4378007) B4378007
theorem B6923465 : Blo 1821612 6923465 := bstep (se 2 (by rfl) ⟨2596299, by rfl⟩ : syracuseStep 6923465 = 5192599) B5192599
theorem B10380595 : Blo 1821612 10380595 := bstep (se 1 (by rfl) ⟨7785446, by rfl⟩ : syracuseStep 10380595 = 15570893) B15570893
theorem B7783739 : Blo 1821612 7783739 := bstep (se 1 (by rfl) ⟨5837804, by rfl⟩ : syracuseStep 7783739 = 11675609) B11675609
theorem B26281421 : Blo 1821612 26281421 := bstep (se 3 (by rfl) ⟨4927766, by rfl⟩ : syracuseStep 26281421 = 9855533) B9855533
theorem B2106895 : Blo 1821612 2106895 := bstep (se 1 (by rfl) ⟨1580171, by rfl⟩ : syracuseStep 2106895 = 3160343) B3160343
theorem B4924957 : Blo 1821612 4924957 := bstep (se 3 (by rfl) ⟨923429, by rfl⟩ : syracuseStep 4924957 = 1846859) B1846859
theorem B4613719 : Blo 1821612 4613719 := bstep (se 1 (by rfl) ⟨3460289, by rfl⟩ : syracuseStep 4613719 = 6920579) B6920579
theorem B3458695 : Blo 1821612 3458695 := bstep (se 1 (by rfl) ⟨2594021, by rfl⟩ : syracuseStep 3458695 = 5188043) B5188043
theorem B3696313 : Blo 1821612 3696313 := bstep (se 2 (by rfl) ⟨1386117, by rfl⟩ : syracuseStep 3696313 = 2772235) B2772235
theorem B2049799 : Blo 1821612 2049799 := bstep (se 1 (by rfl) ⟨1537349, by rfl⟩ : syracuseStep 2049799 = 3074699) B3074699
theorem B7391035 : Blo 1821612 7391035 := bstep (se 1 (by rfl) ⟨5543276, by rfl⟩ : syracuseStep 7391035 = 11086553) B11086553
theorem B46688075 : Blo 1821612 46688075 := bstep (se 1 (by rfl) ⟨35016056, by rfl⟩ : syracuseStep 46688075 = 70032113) B70032113
theorem B4614023 : Blo 1821612 4614023 := bstep (se 1 (by rfl) ⟨3460517, by rfl⟩ : syracuseStep 4614023 = 6921035) B6921035
theorem B2000783 : Blo 1821612 2000783 := bstep (se 1 (by rfl) ⟨1500587, by rfl⟩ : syracuseStep 2000783 = 3001175) B3001175
theorem B2049979 : Blo 1821612 2049979 := bstep (se 1 (by rfl) ⟨1537484, by rfl⟩ : syracuseStep 2049979 = 3074969) B3074969
theorem B4614155 : Blo 1821612 4614155 := bstep (se 1 (by rfl) ⟨3460616, by rfl⟩ : syracuseStep 4614155 = 6921233) B6921233
theorem B3074233 : Blo 1821612 3074233 := bstep (se 2 (by rfl) ⟨1152837, by rfl⟩ : syracuseStep 3074233 = 2305675) B2305675
theorem B3459257 : Blo 1821612 3459257 := bstep (se 2 (by rfl) ⟨1297221, by rfl⟩ : syracuseStep 3459257 = 2594443) B2594443
theorem B9349357 : Blo 1821612 9349357 := bstep (se 3 (by rfl) ⟨1753004, by rfl⟩ : syracuseStep 9349357 = 3506009) B3506009
theorem B5187883 : Blo 1821612 5187883 := bstep (se 1 (by rfl) ⟨3890912, by rfl⟩ : syracuseStep 5187883 = 7781825) B7781825
theorem B9226547 : Blo 1821612 9226547 := bstep (se 1 (by rfl) ⟨6919910, by rfl⟩ : syracuseStep 9226547 = 13839821) B13839821
theorem B2050447 : Blo 1821612 2050447 := bstep (se 1 (by rfl) ⟨1537835, by rfl⟩ : syracuseStep 2050447 = 3075671) B3075671
theorem B6154649 : Blo 1821612 6154649 := bstep (se 2 (by rfl) ⟨2307993, by rfl⟩ : syracuseStep 6154649 = 4615987) B4615987
theorem B20769209 : Blo 1821612 20769209 := bstep (se 2 (by rfl) ⟨7788453, by rfl⟩ : syracuseStep 20769209 = 15576907) B15576907
theorem B9857483 : Blo 1821612 9857483 := bstep (se 1 (by rfl) ⟨7393112, by rfl⟩ : syracuseStep 9857483 = 14786225) B14786225
theorem B18696653 : Blo 1821612 18696653 := bstep (se 3 (by rfl) ⟨3505622, by rfl⟩ : syracuseStep 18696653 = 7011245) B7011245
theorem B19704323 : Blo 1821612 19704323 := bstep (se 1 (by rfl) ⟨14778242, by rfl⟩ : syracuseStep 19704323 = 29556485) B29556485
theorem B17525251 : Blo 1821612 17525251 := bstep (se 1 (by rfl) ⟨13143938, by rfl⟩ : syracuseStep 17525251 = 26287877) B26287877
theorem B4614671 : Blo 1821612 4614671 := bstep (se 1 (by rfl) ⟨3461003, by rfl⟩ : syracuseStep 4614671 = 6922007) B6922007
theorem B5188157 : Blo 1821612 5188157 := bstep (se 3 (by rfl) ⟨972779, by rfl⟩ : syracuseStep 5188157 = 1945559) B1945559
theorem B9226871 : Blo 1821612 9226871 := bstep (se 1 (by rfl) ⟨6920153, by rfl⟩ : syracuseStep 9226871 = 13840307) B13840307
theorem B4098707 : Blo 1821612 4098707 := bstep (se 1 (by rfl) ⟨3074030, by rfl⟩ : syracuseStep 4098707 = 6148061) B6148061
theorem B4614803 : Blo 1821612 4614803 := bstep (se 1 (by rfl) ⟨3461102, by rfl⟩ : syracuseStep 4614803 = 6922205) B6922205
theorem B9349805 : Blo 1821612 9349805 := bstep (se 3 (by rfl) ⟨1753088, by rfl⟩ : syracuseStep 9349805 = 3506177) B3506177
theorem B4098761 : Blo 1821612 4098761 := bstep (se 2 (by rfl) ⟨1537035, by rfl⟩ : syracuseStep 4098761 = 3074071) B3074071
theorem B10382053 : Blo 1821612 10382053 := bstep (se 4 (by rfl) ⟨973317, by rfl⟩ : syracuseStep 10382053 = 1946635) B1946635
theorem B4926209 : Blo 1821612 4926209 := bstep (se 2 (by rfl) ⟨1847328, by rfl⟩ : syracuseStep 4926209 = 3694657) B3694657
theorem B3074935 : Blo 1821612 3074935 := bstep (se 1 (by rfl) ⟨2306201, by rfl⟩ : syracuseStep 3074935 = 4612403) B4612403
theorem B2919287 : Blo 1821612 2919287 := bstep (se 1 (by rfl) ⟨2189465, by rfl⟩ : syracuseStep 2919287 = 4378931) B4378931
theorem B2050951 : Blo 1821612 2050951 := bstep (se 1 (by rfl) ⟨1538213, by rfl⟩ : syracuseStep 2050951 = 3076427) B3076427
theorem B3894151 : Blo 1821612 3894151 := bstep (se 1 (by rfl) ⟨2920613, by rfl⟩ : syracuseStep 3894151 = 5841227) B5841227
theorem B5188499 : Blo 1821612 5188499 := bstep (se 1 (by rfl) ⟨3891374, by rfl⟩ : syracuseStep 5188499 = 7782749) B7782749
theorem B1821627 : Blo 1821612 1821627 := bstep (se 1 (by rfl) ⟨1366220, by rfl⟩ : syracuseStep 1821627 = 2732441) B2732441
theorem B1821703 : Blo 1821612 1821703 := bstep (se 1 (by rfl) ⟨1366277, by rfl⟩ : syracuseStep 1821703 = 2732555) B2732555
theorem B1821711 : Blo 1821612 1821711 := bstep (se 1 (by rfl) ⟨1366283, by rfl⟩ : syracuseStep 1821711 = 2732567) B2732567
theorem B8317981 : Blo 1821612 8317981 := bstep (se 3 (by rfl) ⟨1559621, by rfl⟩ : syracuseStep 8317981 = 3119243) B3119243
theorem B1821755 : Blo 1821612 1821755 := bstep (se 1 (by rfl) ⟨1366316, by rfl⟩ : syracuseStep 1821755 = 2732633) B2732633
theorem B3075131 : Blo 1821612 3075131 := bstep (se 1 (by rfl) ⟨2306348, by rfl⟩ : syracuseStep 3075131 = 4612697) B4612697
theorem B2051131 : Blo 1821612 2051131 := bstep (se 1 (by rfl) ⟨1538348, by rfl⟩ : syracuseStep 2051131 = 3076697) B3076697
theorem B1821831 : Blo 1821612 1821831 := bstep (se 1 (by rfl) ⟨1366373, by rfl⟩ : syracuseStep 1821831 = 2732747) B2732747
theorem B1821839 : Blo 1821612 1821839 := bstep (se 1 (by rfl) ⟨1366379, by rfl⟩ : syracuseStep 1821839 = 2732759) B2732759
theorem B1821883 : Blo 1821612 1821883 := bstep (se 1 (by rfl) ⟨1366412, by rfl⟩ : syracuseStep 1821883 = 2732825) B2732825
theorem B19696841 : Blo 1821612 19696841 := bstep (se 2 (by rfl) ⟨7386315, by rfl⟩ : syracuseStep 19696841 = 14772631) B14772631
theorem B1821959 : Blo 1821612 1821959 := bstep (se 1 (by rfl) ⟨1366469, by rfl⟩ : syracuseStep 1821959 = 2732939) B2732939
theorem B1821967 : Blo 1821612 1821967 := bstep (se 1 (by rfl) ⟨1366475, by rfl⟩ : syracuseStep 1821967 = 2732951) B2732951
theorem B3943723 : Blo 1821612 3943723 := bstep (se 1 (by rfl) ⟨2957792, by rfl⟩ : syracuseStep 3943723 = 5915585) B5915585
theorem B1822011 : Blo 1821612 1822011 := bstep (se 1 (by rfl) ⟨1366508, by rfl⟩ : syracuseStep 1822011 = 2733017) B2733017
theorem B3460411 : Blo 1821612 3460411 := bstep (se 1 (by rfl) ⟨2595308, by rfl⟩ : syracuseStep 3460411 = 5190617) B5190617
theorem B4099463 : Blo 1821612 4099463 := bstep (se 1 (by rfl) ⟨3074597, by rfl⟩ : syracuseStep 4099463 = 6149195) B6149195
theorem B1822087 : Blo 1821612 1822087 := bstep (se 1 (by rfl) ⟨1366565, by rfl⟩ : syracuseStep 1822087 = 2733131) B2733131
theorem B1822095 : Blo 1821612 1822095 := bstep (se 1 (by rfl) ⟨1366571, by rfl⟩ : syracuseStep 1822095 = 2733143) B2733143
theorem B1822139 : Blo 1821612 1822139 := bstep (se 1 (by rfl) ⟨1366604, by rfl⟩ : syracuseStep 1822139 = 2733209) B2733209
theorem B3075529 : Blo 1821612 3075529 := bstep (se 2 (by rfl) ⟨1153323, by rfl⟩ : syracuseStep 3075529 = 2306647) B2306647
theorem B1822215 : Blo 1821612 1822215 := bstep (se 1 (by rfl) ⟨1366661, by rfl⟩ : syracuseStep 1822215 = 2733323) B2733323
theorem B1822223 : Blo 1821612 1822223 := bstep (se 1 (by rfl) ⟨1366667, by rfl⟩ : syracuseStep 1822223 = 2733335) B2733335
theorem B2305579 : Blo 1821612 2305579 := bstep (se 1 (by rfl) ⟨1729184, by rfl⟩ : syracuseStep 2305579 = 3458369) B3458369
theorem B2919979 : Blo 1821612 2919979 := bstep (se 1 (by rfl) ⟨2189984, by rfl⟩ : syracuseStep 2919979 = 4379969) B4379969
theorem B4099643 : Blo 1821612 4099643 := bstep (se 1 (by rfl) ⟨3074732, by rfl⟩ : syracuseStep 4099643 = 6149465) B6149465
theorem B1822267 : Blo 1821612 1822267 := bstep (se 1 (by rfl) ⟨1366700, by rfl⟩ : syracuseStep 1822267 = 2733401) B2733401
theorem B9227843 : Blo 1821612 9227843 := bstep (se 1 (by rfl) ⟨6920882, by rfl⟩ : syracuseStep 9227843 = 13841765) B13841765
theorem B26267237 : Blo 1821612 26267237 := bstep (se 4 (by rfl) ⟨2462553, by rfl⟩ : syracuseStep 26267237 = 4925107) B4925107
theorem B2920055 : Blo 1821612 2920055 := bstep (se 1 (by rfl) ⟨2190041, by rfl⟩ : syracuseStep 2920055 = 4380083) B4380083
theorem B1822343 : Blo 1821612 1822343 := bstep (se 1 (by rfl) ⟨1366757, by rfl⟩ : syracuseStep 1822343 = 2733515) B2733515
theorem B1822351 : Blo 1821612 1822351 := bstep (se 1 (by rfl) ⟨1366763, by rfl⟩ : syracuseStep 1822351 = 2733527) B2733527
theorem B4099769 : Blo 1821612 4099769 := bstep (se 2 (by rfl) ⟨1537413, by rfl⟩ : syracuseStep 4099769 = 3074827) B3074827
theorem B1822395 : Blo 1821612 1822395 := bstep (se 1 (by rfl) ⟨1366796, by rfl⟩ : syracuseStep 1822395 = 2733593) B2733593
theorem B5918465 : Blo 1821612 5918465 := bstep (se 2 (by rfl) ⟨2219424, by rfl⟩ : syracuseStep 5918465 = 4438849) B4438849
theorem B4615937 : Blo 1821612 4615937 := bstep (se 2 (by rfl) ⟨1730976, by rfl⟩ : syracuseStep 4615937 = 3461953) B3461953
theorem B1822471 : Blo 1821612 1822471 := bstep (se 1 (by rfl) ⟨1366853, by rfl⟩ : syracuseStep 1822471 = 2733707) B2733707
theorem B1822479 : Blo 1821612 1822479 := bstep (se 1 (by rfl) ⟨1366859, by rfl⟩ : syracuseStep 1822479 = 2733719) B2733719
theorem B3460897 : Blo 1821612 3460897 := bstep (se 2 (by rfl) ⟨1297836, by rfl⟩ : syracuseStep 3460897 = 2595673) B2595673
theorem B63123245 : Blo 1821612 63123245 := bstep (se 3 (by rfl) ⟨11835608, by rfl⟩ : syracuseStep 63123245 = 23671217) B23671217
theorem B1822523 : Blo 1821612 1822523 := bstep (se 1 (by rfl) ⟨1366892, by rfl⟩ : syracuseStep 1822523 = 2733785) B2733785
theorem B1822599 : Blo 1821612 1822599 := bstep (se 1 (by rfl) ⟨1366949, by rfl⟩ : syracuseStep 1822599 = 2733899) B2733899
theorem B9228167 : Blo 1821612 9228167 := bstep (se 1 (by rfl) ⟨6921125, by rfl⟩ : syracuseStep 9228167 = 13842251) B13842251
theorem B1822607 : Blo 1821612 1822607 := bstep (se 1 (by rfl) ⟨1366955, by rfl⟩ : syracuseStep 1822607 = 2733911) B2733911
theorem B1822651 : Blo 1821612 1822651 := bstep (se 1 (by rfl) ⟨1366988, by rfl⟩ : syracuseStep 1822651 = 2733977) B2733977
theorem B1822727 : Blo 1821612 1822727 := bstep (se 1 (by rfl) ⟨1367045, by rfl⟩ : syracuseStep 1822727 = 2734091) B2734091
theorem B4100111 : Blo 1821612 4100111 := bstep (se 1 (by rfl) ⟨3075083, by rfl⟩ : syracuseStep 4100111 = 6150167) B6150167
theorem B1822735 : Blo 1821612 1822735 := bstep (se 1 (by rfl) ⟨1367051, by rfl⟩ : syracuseStep 1822735 = 2734103) B2734103
theorem B4100129 : Blo 1821612 4100129 := bstep (se 2 (by rfl) ⟨1537548, by rfl⟩ : syracuseStep 4100129 = 3075097) B3075097
theorem B1822779 : Blo 1821612 1822779 := bstep (se 1 (by rfl) ⟨1367084, by rfl⟩ : syracuseStep 1822779 = 2734169) B2734169
theorem B1822855 : Blo 1821612 1822855 := bstep (se 1 (by rfl) ⟨1367141, by rfl⟩ : syracuseStep 1822855 = 2734283) B2734283
theorem B3076231 : Blo 1821612 3076231 := bstep (se 1 (by rfl) ⟨2307173, by rfl⟩ : syracuseStep 3076231 = 4614347) B4614347
theorem B1822863 : Blo 1821612 1822863 := bstep (se 1 (by rfl) ⟨1367147, by rfl⟩ : syracuseStep 1822863 = 2734295) B2734295
theorem B5542073 : Blo 1821612 5542073 := bstep (se 2 (by rfl) ⟨2078277, by rfl⟩ : syracuseStep 5542073 = 4156555) B4156555
theorem B1822907 : Blo 1821612 1822907 := bstep (se 1 (by rfl) ⟨1367180, by rfl⟩ : syracuseStep 1822907 = 2734361) B2734361
theorem B1822983 : Blo 1821612 1822983 := bstep (se 1 (by rfl) ⟨1367237, by rfl⟩ : syracuseStep 1822983 = 2734475) B2734475
theorem B1822991 : Blo 1821612 1822991 := bstep (se 1 (by rfl) ⟨1367243, by rfl⟩ : syracuseStep 1822991 = 2734487) B2734487
theorem B6148385 : Blo 1821612 6148385 := bstep (se 2 (by rfl) ⟨2305644, by rfl⟩ : syracuseStep 6148385 = 4611289) B4611289
theorem B14782753 : Blo 1821612 14782753 := bstep (se 2 (by rfl) ⟨5543532, by rfl⟩ : syracuseStep 14782753 = 11087065) B11087065
theorem B1823035 : Blo 1821612 1823035 := bstep (se 1 (by rfl) ⟨1367276, by rfl⟩ : syracuseStep 1823035 = 2734553) B2734553
theorem B4100471 : Blo 1821612 4100471 := bstep (se 1 (by rfl) ⟨3075353, by rfl⟩ : syracuseStep 4100471 = 6150707) B6150707
theorem B2732423 : Blo 1821612 2732423 := bstep (se 1 (by rfl) ⟨2049317, by rfl⟩ : syracuseStep 2732423 = 4098635) B4098635
theorem B1823111 : Blo 1821612 1823111 := bstep (se 1 (by rfl) ⟨1367333, by rfl⟩ : syracuseStep 1823111 = 2734667) B2734667
theorem B1823119 : Blo 1821612 1823119 := bstep (se 1 (by rfl) ⟨1367339, by rfl⟩ : syracuseStep 1823119 = 2734679) B2734679
theorem B2732459 : Blo 1821612 2732459 := bstep (se 1 (by rfl) ⟨2049344, by rfl⟩ : syracuseStep 2732459 = 4098689) B4098689
theorem B1823163 : Blo 1821612 1823163 := bstep (se 1 (by rfl) ⟨1367372, by rfl⟩ : syracuseStep 1823163 = 2734745) B2734745
theorem B2732489 : Blo 1821612 2732489 := bstep (se 2 (by rfl) ⟨1024683, by rfl⟩ : syracuseStep 2732489 = 2049367) B2049367
theorem B2306551 : Blo 1821612 2306551 := bstep (se 1 (by rfl) ⟨1729913, by rfl⟩ : syracuseStep 2306551 = 3459827) B3459827
theorem B1823239 : Blo 1821612 1823239 := bstep (se 1 (by rfl) ⟨1367429, by rfl⟩ : syracuseStep 1823239 = 2734859) B2734859
theorem B7016971 : Blo 1821612 7016971 := bstep (se 1 (by rfl) ⟨5262728, by rfl⟩ : syracuseStep 7016971 = 10525457) B10525457
theorem B1823247 : Blo 1821612 1823247 := bstep (se 1 (by rfl) ⟨1367435, by rfl⟩ : syracuseStep 1823247 = 2734871) B2734871
theorem B8753707 : Blo 1821612 8753707 := bstep (se 1 (by rfl) ⟨6565280, by rfl⟩ : syracuseStep 8753707 = 13130561) B13130561
theorem B4100651 : Blo 1821612 4100651 := bstep (se 1 (by rfl) ⟨3075488, by rfl⟩ : syracuseStep 4100651 = 6150977) B6150977
theorem B2732603 : Blo 1821612 2732603 := bstep (se 1 (by rfl) ⟨2049452, by rfl⟩ : syracuseStep 2732603 = 4098905) B4098905
theorem B1823291 : Blo 1821612 1823291 := bstep (se 1 (by rfl) ⟨1367468, by rfl⟩ : syracuseStep 1823291 = 2734937) B2734937
theorem B11080253 : Blo 1821612 11080253 := bstep (se 3 (by rfl) ⟨2077547, by rfl⟩ : syracuseStep 11080253 = 4155095) B4155095
theorem B2732663 : Blo 1821612 2732663 := bstep (se 1 (by rfl) ⟨2049497, by rfl⟩ : syracuseStep 2732663 = 4098995) B4098995
theorem B1823367 : Blo 1821612 1823367 := bstep (se 1 (by rfl) ⟨1367525, by rfl⟩ : syracuseStep 1823367 = 2735051) B2735051
theorem B2732687 : Blo 1821612 2732687 := bstep (se 1 (by rfl) ⟨2049515, by rfl⟩ : syracuseStep 2732687 = 4099031) B4099031
theorem B1823375 : Blo 1821612 1823375 := bstep (se 1 (by rfl) ⟨1367531, by rfl⟩ : syracuseStep 1823375 = 2735063) B2735063
theorem B2732729 : Blo 1821612 2732729 := bstep (se 2 (by rfl) ⟨1024773, by rfl⟩ : syracuseStep 2732729 = 2049547) B2049547
theorem B1823419 : Blo 1821612 1823419 := bstep (se 1 (by rfl) ⟨1367564, by rfl⟩ : syracuseStep 1823419 = 2735129) B2735129
theorem B2732807 : Blo 1821612 2732807 := bstep (se 1 (by rfl) ⟨2049605, by rfl⟩ : syracuseStep 2732807 = 4099211) B4099211
theorem B1823495 : Blo 1821612 1823495 := bstep (se 1 (by rfl) ⟨1367621, by rfl⟩ : syracuseStep 1823495 = 2735243) B2735243
theorem B3076879 : Blo 1821612 3076879 := bstep (se 1 (by rfl) ⟨2307659, by rfl⟩ : syracuseStep 3076879 = 4615319) B4615319
theorem B1823503 : Blo 1821612 1823503 := bstep (se 1 (by rfl) ⟨1367627, by rfl⟩ : syracuseStep 1823503 = 2735255) B2735255
theorem B4928285 : Blo 1821612 4928285 := bstep (se 3 (by rfl) ⟨924053, by rfl⟩ : syracuseStep 4928285 = 1848107) B1848107
theorem B2732843 : Blo 1821612 2732843 := bstep (se 1 (by rfl) ⟨2049632, by rfl⟩ : syracuseStep 2732843 = 4099265) B4099265
theorem B2306875 : Blo 1821612 2306875 := bstep (se 1 (by rfl) ⟨1730156, by rfl⟩ : syracuseStep 2306875 = 3460313) B3460313
theorem B1823547 : Blo 1821612 1823547 := bstep (se 1 (by rfl) ⟨1367660, by rfl⟩ : syracuseStep 1823547 = 2735321) B2735321
theorem B2732873 : Blo 1821612 2732873 := bstep (se 2 (by rfl) ⟨1024827, by rfl⟩ : syracuseStep 2732873 = 2049655) B2049655
theorem B6148979 : Blo 1821612 6148979 := bstep (se 1 (by rfl) ⟨4611734, by rfl⟩ : syracuseStep 6148979 = 9223469) B9223469
theorem B6656903 : Blo 1821612 6656903 := bstep (se 1 (by rfl) ⟨4992677, by rfl⟩ : syracuseStep 6656903 = 9985355) B9985355
theorem B4101011 : Blo 1821612 4101011 := bstep (se 1 (by rfl) ⟨3075758, by rfl⟩ : syracuseStep 4101011 = 6151517) B6151517
theorem B4379545 : Blo 1821612 4379545 := bstep (se 2 (by rfl) ⟨1642329, by rfl⟩ : syracuseStep 4379545 = 3284659) B3284659
theorem B5837753 : Blo 1821612 5837753 := bstep (se 2 (by rfl) ⟨2189157, by rfl⟩ : syracuseStep 5837753 = 4378315) B4378315
theorem B2732987 : Blo 1821612 2732987 := bstep (se 1 (by rfl) ⟨2049740, by rfl⟩ : syracuseStep 2732987 = 4099481) B4099481
theorem B4101065 : Blo 1821612 4101065 := bstep (se 2 (by rfl) ⟨1537899, by rfl⟩ : syracuseStep 4101065 = 3075799) B3075799
theorem B6919121 : Blo 1821612 6919121 := bstep (se 2 (by rfl) ⟨2594670, by rfl⟩ : syracuseStep 6919121 = 5189341) B5189341
theorem B2733047 : Blo 1821612 2733047 := bstep (se 1 (by rfl) ⟨2049785, by rfl⟩ : syracuseStep 2733047 = 4099571) B4099571
theorem B2733071 : Blo 1821612 2733071 := bstep (se 1 (by rfl) ⟨2049803, by rfl⟩ : syracuseStep 2733071 = 4099607) B4099607
theorem B10376221 : Blo 1821612 10376221 := bstep (se 3 (by rfl) ⟨1945541, by rfl⟩ : syracuseStep 10376221 = 3891083) B3891083
theorem B2733113 : Blo 1821612 2733113 := bstep (se 2 (by rfl) ⟨1024917, by rfl⟩ : syracuseStep 2733113 = 2049835) B2049835
theorem B5190743 : Blo 1821612 5190743 := bstep (se 1 (by rfl) ⟨3893057, by rfl⟩ : syracuseStep 5190743 = 7786115) B7786115
theorem B2733191 : Blo 1821612 2733191 := bstep (se 1 (by rfl) ⟨2049893, by rfl⟩ : syracuseStep 2733191 = 4099787) B4099787
theorem B2733227 : Blo 1821612 2733227 := bstep (se 1 (by rfl) ⟨2049920, by rfl⟩ : syracuseStep 2733227 = 4099841) B4099841
theorem B2733257 : Blo 1821612 2733257 := bstep (se 2 (by rfl) ⟨1024971, by rfl⟩ : syracuseStep 2733257 = 2049943) B2049943
theorem B37418273 : Blo 1821612 37418273 := bstep (se 2 (by rfl) ⟨14031852, by rfl⟩ : syracuseStep 37418273 = 28063705) B28063705
theorem B2733371 : Blo 1821612 2733371 := bstep (se 1 (by rfl) ⟨2050028, by rfl⟩ : syracuseStep 2733371 = 4100057) B4100057
theorem B2733431 : Blo 1821612 2733431 := bstep (se 1 (by rfl) ⟨2050073, by rfl⟩ : syracuseStep 2733431 = 4100147) B4100147
theorem B2733455 : Blo 1821612 2733455 := bstep (se 1 (by rfl) ⟨2050091, by rfl⟩ : syracuseStep 2733455 = 4100183) B4100183
theorem B10384787 : Blo 1821612 10384787 := bstep (se 1 (by rfl) ⟨7788590, by rfl⟩ : syracuseStep 10384787 = 15577181) B15577181
theorem B6919577 : Blo 1821612 6919577 := bstep (se 2 (by rfl) ⟨2594841, by rfl⟩ : syracuseStep 6919577 = 5189683) B5189683
theorem B19699129 : Blo 1821612 19699129 := bstep (se 2 (by rfl) ⟨7387173, by rfl⟩ : syracuseStep 19699129 = 14774347) B14774347
theorem B2733497 : Blo 1821612 2733497 := bstep (se 2 (by rfl) ⟨1025061, by rfl⟩ : syracuseStep 2733497 = 2050123) B2050123
theorem B5838265 : Blo 1821612 5838265 := bstep (se 2 (by rfl) ⟨2189349, by rfl⟩ : syracuseStep 5838265 = 4378699) B4378699
theorem B2733575 : Blo 1821612 2733575 := bstep (se 1 (by rfl) ⟨2050181, by rfl⟩ : syracuseStep 2733575 = 4100363) B4100363
theorem B10376747 : Blo 1821612 10376747 := bstep (se 1 (by rfl) ⟨7782560, by rfl⟩ : syracuseStep 10376747 = 15565121) B15565121
theorem B2733611 : Blo 1821612 2733611 := bstep (se 1 (by rfl) ⟨2050208, by rfl⟩ : syracuseStep 2733611 = 4100417) B4100417
theorem B11679299 : Blo 1821612 11679299 := bstep (se 1 (by rfl) ⟨8759474, by rfl⟩ : syracuseStep 11679299 = 17518949) B17518949
theorem B2733641 : Blo 1821612 2733641 := bstep (se 2 (by rfl) ⟨1025115, by rfl⟩ : syracuseStep 2733641 = 2050231) B2050231
theorem B19699301 : Blo 1821612 19699301 := bstep (se 4 (by rfl) ⟨1846809, by rfl⟩ : syracuseStep 19699301 = 3693619) B3693619
theorem B5330551 : Blo 1821612 5330551 := bstep (se 1 (by rfl) ⟨3997913, by rfl⟩ : syracuseStep 5330551 = 7995827) B7995827
theorem B20756087 : Blo 1821612 20756087 := bstep (se 1 (by rfl) ⟨15567065, by rfl⟩ : syracuseStep 20756087 = 31134131) B31134131
theorem B4101767 : Blo 1821612 4101767 := bstep (se 1 (by rfl) ⟨3076325, by rfl⟩ : syracuseStep 4101767 = 6152651) B6152651
theorem B2733755 : Blo 1821612 2733755 := bstep (se 1 (by rfl) ⟨2050316, by rfl⟩ : syracuseStep 2733755 = 4100633) B4100633
theorem B2733815 : Blo 1821612 2733815 := bstep (se 1 (by rfl) ⟨2050361, by rfl⟩ : syracuseStep 2733815 = 4100723) B4100723
theorem B2307847 : Blo 1821612 2307847 := bstep (se 1 (by rfl) ⟨1730885, by rfl⟩ : syracuseStep 2307847 = 3461771) B3461771
theorem B2733839 : Blo 1821612 2733839 := bstep (se 1 (by rfl) ⟨2050379, by rfl⟩ : syracuseStep 2733839 = 4100759) B4100759
theorem B13137713 : Blo 1821612 13137713 := bstep (se 2 (by rfl) ⟨4926642, by rfl⟩ : syracuseStep 13137713 = 9853285) B9853285
theorem B2733881 : Blo 1821612 2733881 := bstep (se 2 (by rfl) ⟨1025205, by rfl⟩ : syracuseStep 2733881 = 2050411) B2050411
theorem B4101947 : Blo 1821612 4101947 := bstep (se 1 (by rfl) ⟨3076460, by rfl⟩ : syracuseStep 4101947 = 6152921) B6152921
theorem B4994903 : Blo 1821612 4994903 := bstep (se 1 (by rfl) ⟨3746177, by rfl⟩ : syracuseStep 4994903 = 7492355) B7492355
theorem B2733959 : Blo 1821612 2733959 := bstep (se 1 (by rfl) ⟨2050469, by rfl⟩ : syracuseStep 2733959 = 4100939) B4100939
theorem B11089811 : Blo 1821612 11089811 := bstep (se 1 (by rfl) ⟨8317358, by rfl⟩ : syracuseStep 11089811 = 16634717) B16634717
theorem B2733995 : Blo 1821612 2733995 := bstep (se 1 (by rfl) ⟨2050496, by rfl⟩ : syracuseStep 2733995 = 4100993) B4100993
theorem B4102073 : Blo 1821612 4102073 := bstep (se 2 (by rfl) ⟨1538277, by rfl⟩ : syracuseStep 4102073 = 3076555) B3076555
theorem B2734025 : Blo 1821612 2734025 := bstep (se 2 (by rfl) ⟨1025259, by rfl⟩ : syracuseStep 2734025 = 2050519) B2050519
theorem B9222173 : Blo 1821612 9222173 := bstep (se 3 (by rfl) ⟨1729157, by rfl⟩ : syracuseStep 9222173 = 3458315) B3458315
theorem B8755229 : Blo 1821612 8755229 := bstep (se 3 (by rfl) ⟨1641605, by rfl⟩ : syracuseStep 8755229 = 3283211) B3283211
theorem B6567965 : Blo 1821612 6567965 := bstep (se 3 (by rfl) ⟨1231493, by rfl⟩ : syracuseStep 6567965 = 2462987) B2462987
theorem B2734139 : Blo 1821612 2734139 := bstep (se 1 (by rfl) ⟨2050604, by rfl⟩ : syracuseStep 2734139 = 4101209) B4101209
theorem B14784599 : Blo 1821612 14784599 := bstep (se 1 (by rfl) ⟨11088449, by rfl⟩ : syracuseStep 14784599 = 22176899) B22176899
theorem B10385495 : Blo 1821612 10385495 := bstep (se 1 (by rfl) ⟨7789121, by rfl⟩ : syracuseStep 10385495 = 15578243) B15578243
theorem B2734199 : Blo 1821612 2734199 := bstep (se 1 (by rfl) ⟨2050649, by rfl⟩ : syracuseStep 2734199 = 4101299) B4101299
theorem B2734223 : Blo 1821612 2734223 := bstep (se 1 (by rfl) ⟨2050667, by rfl⟩ : syracuseStep 2734223 = 4101335) B4101335
theorem B2734265 : Blo 1821612 2734265 := bstep (se 2 (by rfl) ⟨1025349, by rfl⟩ : syracuseStep 2734265 = 2050699) B2050699
theorem B2734343 : Blo 1821612 2734343 := bstep (se 1 (by rfl) ⟨2050757, by rfl⟩ : syracuseStep 2734343 = 4101515) B4101515
theorem B4102415 : Blo 1821612 4102415 := bstep (se 1 (by rfl) ⟨3076811, by rfl⟩ : syracuseStep 4102415 = 6153623) B6153623
theorem B67426577 : Blo 1821612 67426577 := bstep (se 2 (by rfl) ⟨25284966, by rfl⟩ : syracuseStep 67426577 = 50569933) B50569933
theorem B4102433 : Blo 1821612 4102433 := bstep (se 2 (by rfl) ⟨1538412, by rfl⟩ : syracuseStep 4102433 = 3076825) B3076825
theorem B2595115 : Blo 1821612 2595115 := bstep (se 1 (by rfl) ⟨1946336, by rfl⟩ : syracuseStep 2595115 = 3892673) B3892673
theorem B2734379 : Blo 1821612 2734379 := bstep (se 1 (by rfl) ⟨2050784, by rfl⟩ : syracuseStep 2734379 = 4101569) B4101569
theorem B5544251 : Blo 1821612 5544251 := bstep (se 1 (by rfl) ⟨4158188, by rfl⟩ : syracuseStep 5544251 = 8316377) B8316377
theorem B2734409 : Blo 1821612 2734409 := bstep (se 2 (by rfl) ⟨1025403, by rfl⟩ : syracuseStep 2734409 = 2050807) B2050807
theorem B2734523 : Blo 1821612 2734523 := bstep (se 1 (by rfl) ⟨2050892, by rfl⟩ : syracuseStep 2734523 = 4101785) B4101785
theorem B2734583 : Blo 1821612 2734583 := bstep (se 1 (by rfl) ⟨2050937, by rfl⟩ : syracuseStep 2734583 = 4101875) B4101875
theorem B9222659 : Blo 1821612 9222659 := bstep (se 1 (by rfl) ⟨6916994, by rfl⟩ : syracuseStep 9222659 = 13833989) B13833989
theorem B2595343 : Blo 1821612 2595343 := bstep (se 1 (by rfl) ⟨1946507, by rfl⟩ : syracuseStep 2595343 = 3893015) B3893015
theorem B2734607 : Blo 1821612 2734607 := bstep (se 1 (by rfl) ⟨2050955, by rfl⟩ : syracuseStep 2734607 = 4101911) B4101911
theorem B4381199 : Blo 1821612 4381199 := bstep (se 1 (by rfl) ⟨3285899, by rfl⟩ : syracuseStep 4381199 = 6571799) B6571799
theorem B6920747 : Blo 1821612 6920747 := bstep (se 1 (by rfl) ⟨5190560, by rfl⟩ : syracuseStep 6920747 = 10381121) B10381121
theorem B2734649 : Blo 1821612 2734649 := bstep (se 2 (by rfl) ⟨1025493, by rfl⟩ : syracuseStep 2734649 = 2050987) B2050987
theorem B14785091 : Blo 1821612 14785091 := bstep (se 1 (by rfl) ⟨11088818, by rfl⟩ : syracuseStep 14785091 = 22177637) B22177637
theorem B14604877 : Blo 1821612 14604877 := bstep (se 3 (by rfl) ⟨2738414, by rfl⟩ : syracuseStep 14604877 = 5476829) B5476829
theorem B18700919 : Blo 1821612 18700919 := bstep (se 1 (by rfl) ⟨14025689, by rfl⟩ : syracuseStep 18700919 = 28051379) B28051379
theorem B4102775 : Blo 1821612 4102775 := bstep (se 1 (by rfl) ⟨3077081, by rfl⟩ : syracuseStep 4102775 = 6154163) B6154163
theorem B2734727 : Blo 1821612 2734727 := bstep (se 1 (by rfl) ⟨2051045, by rfl⟩ : syracuseStep 2734727 = 4102091) B4102091
theorem B2734763 : Blo 1821612 2734763 := bstep (se 1 (by rfl) ⟨2051072, by rfl⟩ : syracuseStep 2734763 = 4102145) B4102145
theorem B2734793 : Blo 1821612 2734793 := bstep (se 2 (by rfl) ⟨1025547, by rfl⟩ : syracuseStep 2734793 = 2051095) B2051095
theorem B6568685 : Blo 1821612 6568685 := bstep (se 3 (by rfl) ⟨1231628, by rfl⟩ : syracuseStep 6568685 = 2463257) B2463257
theorem B4102955 : Blo 1821612 4102955 := bstep (se 1 (by rfl) ⟨3077216, by rfl⟩ : syracuseStep 4102955 = 6154433) B6154433
theorem B2734907 : Blo 1821612 2734907 := bstep (se 1 (by rfl) ⟨2051180, by rfl⟩ : syracuseStep 2734907 = 4102361) B4102361
theorem B2734967 : Blo 1821612 2734967 := bstep (se 1 (by rfl) ⟨2051225, by rfl⟩ : syracuseStep 2734967 = 4102451) B4102451
theorem B2734991 : Blo 1821612 2734991 := bstep (se 1 (by rfl) ⟨2051243, by rfl⟩ : syracuseStep 2734991 = 4102487) B4102487
theorem B2735033 : Blo 1821612 2735033 := bstep (se 2 (by rfl) ⟨1025637, by rfl⟩ : syracuseStep 2735033 = 2051275) B2051275
theorem B10378205 : Blo 1821612 10378205 := bstep (se 3 (by rfl) ⟨1945913, by rfl⟩ : syracuseStep 10378205 = 3891827) B3891827
theorem B2735111 : Blo 1821612 2735111 := bstep (se 1 (by rfl) ⟨2051333, by rfl⟩ : syracuseStep 2735111 = 4102667) B4102667
theorem B2735147 : Blo 1821612 2735147 := bstep (se 1 (by rfl) ⟨2051360, by rfl⟩ : syracuseStep 2735147 = 4102721) B4102721
theorem B2735177 : Blo 1821612 2735177 := bstep (se 2 (by rfl) ⟨1025691, by rfl⟩ : syracuseStep 2735177 = 2051383) B2051383
theorem B4996183 : Blo 1821612 4996183 := bstep (se 1 (by rfl) ⟨3747137, by rfl⟩ : syracuseStep 4996183 = 7494275) B7494275
theorem B2735291 : Blo 1821612 2735291 := bstep (se 1 (by rfl) ⟨2051468, by rfl⟩ : syracuseStep 2735291 = 4102937) B4102937
theorem B2735351 : Blo 1821612 2735351 := bstep (se 1 (by rfl) ⟨2051513, by rfl⟩ : syracuseStep 2735351 = 4103027) B4103027
theorem B2735375 : Blo 1821612 2735375 := bstep (se 1 (by rfl) ⟨2051531, by rfl⟩ : syracuseStep 2735375 = 4103063) B4103063
theorem B2735417 : Blo 1821612 2735417 := bstep (se 2 (by rfl) ⟨1025781, by rfl⟩ : syracuseStep 2735417 = 2051563) B2051563
theorem B5258611 : Blo 1821612 5258611 := bstep (se 1 (by rfl) ⟨3943958, by rfl⟩ : syracuseStep 5258611 = 7887917) B7887917
theorem B9231731 : Blo 1821612 9231731 := bstep (se 1 (by rfl) ⟨6923798, by rfl⟩ : syracuseStep 9231731 = 13847597) B13847597
theorem B35028359 : Blo 1821612 35028359 := bstep (se 1 (by rfl) ⟨26271269, by rfl⟩ : syracuseStep 35028359 = 52542539) B52542539
theorem B12475793 : Blo 1821612 12475793 := bstep (se 2 (by rfl) ⟨4678422, by rfl⟩ : syracuseStep 12475793 = 9356845) B9356845
theorem B6151571 : Blo 1821612 6151571 := bstep (se 1 (by rfl) ⟨4613678, by rfl⟩ : syracuseStep 6151571 = 9227357) B9227357
theorem B9354649 : Blo 1821612 9354649 := bstep (se 2 (by rfl) ⟨3507993, by rfl⟩ : syracuseStep 9354649 = 7015987) B7015987
theorem B5545417 : Blo 1821612 5545417 := bstep (se 2 (by rfl) ⟨2079531, by rfl⟩ : syracuseStep 5545417 = 4159063) B4159063
theorem B25288523 : Blo 1821612 25288523 := bstep (se 1 (by rfl) ⟨18966392, by rfl⟩ : syracuseStep 25288523 = 37932785) B37932785
theorem B3694715 : Blo 1821612 3694715 := bstep (se 1 (by rfl) ⟨2771036, by rfl⟩ : syracuseStep 3694715 = 5542073) B5542073
theorem B19710337 : Blo 1821612 19710337 := bstep (se 2 (by rfl) ⟨7391376, by rfl⟩ : syracuseStep 19710337 = 14782753) B14782753
theorem B3891835 : Blo 1821612 3891835 := bstep (se 1 (by rfl) ⟨2918876, by rfl⟩ : syracuseStep 3891835 = 5837753) B5837753
theorem B4612747 : Blo 1821612 4612747 := bstep (se 1 (by rfl) ⟨3459560, by rfl⟩ : syracuseStep 4612747 = 6919121) B6919121
theorem B9355961 : Blo 1821612 9355961 := bstep (se 2 (by rfl) ⟨3508485, by rfl⟩ : syracuseStep 9355961 = 7016971) B7016971
theorem B7783123 : Blo 1821612 7783123 := bstep (se 1 (by rfl) ⟨5837342, by rfl⟩ : syracuseStep 7783123 = 11674685) B11674685
theorem B19473169 : Blo 1821612 19473169 := bstep (se 2 (by rfl) ⟨7302438, by rfl⟩ : syracuseStep 19473169 = 14604877) B14604877
theorem B24945515 : Blo 1821612 24945515 := bstep (se 1 (by rfl) ⟨18709136, by rfl⟩ : syracuseStep 24945515 = 37418273) B37418273
theorem B6923191 : Blo 1821612 6923191 := bstep (se 1 (by rfl) ⟨5192393, by rfl⟩ : syracuseStep 6923191 = 10384787) B10384787
theorem B4613051 : Blo 1821612 4613051 := bstep (se 1 (by rfl) ⟨3459788, by rfl⟩ : syracuseStep 4613051 = 6919577) B6919577
theorem B33268781 : Blo 1821612 33268781 := bstep (se 3 (by rfl) ⟨6237896, by rfl⟩ : syracuseStep 33268781 = 12475793) B12475793
theorem B25330753 : Blo 1821612 25330753 := bstep (se 2 (by rfl) ⟨9499032, by rfl⟩ : syracuseStep 25330753 = 18998065) B18998065
theorem B13132867 : Blo 1821612 13132867 := bstep (se 1 (by rfl) ⟨9849650, by rfl⟩ : syracuseStep 13132867 = 19699301) B19699301
theorem B13837391 : Blo 1821612 13837391 := bstep (se 1 (by rfl) ⟨10378043, by rfl⟩ : syracuseStep 13837391 = 20756087) B20756087
theorem B8758475 : Blo 1821612 8758475 := bstep (se 1 (by rfl) ⟨6568856, by rfl⟩ : syracuseStep 8758475 = 13137713) B13137713
theorem B31147253 : Blo 1821612 31147253 := bstep (se 5 (by rfl) ⟨1460027, by rfl⟩ : syracuseStep 31147253 = 2920055) B2920055
theorem B9856399 : Blo 1821612 9856399 := bstep (se 1 (by rfl) ⟨7392299, by rfl⟩ : syracuseStep 9856399 = 14784599) B14784599
theorem B6923663 : Blo 1821612 6923663 := bstep (se 1 (by rfl) ⟨5192747, by rfl⟩ : syracuseStep 6923663 = 10385495) B10385495
theorem B6661577 : Blo 1821612 6661577 := bstep (se 2 (by rfl) ⟨2498091, by rfl⟩ : syracuseStep 6661577 = 4996183) B4996183
theorem B44951051 : Blo 1821612 44951051 := bstep (se 1 (by rfl) ⟨33713288, by rfl⟩ : syracuseStep 44951051 = 67426577) B67426577
theorem B3696167 : Blo 1821612 3696167 := bstep (se 1 (by rfl) ⟨2772125, by rfl⟩ : syracuseStep 3696167 = 5544251) B5544251
theorem B13846139 : Blo 1821612 13846139 := bstep (se 1 (by rfl) ⟨10384604, by rfl⟩ : syracuseStep 13846139 = 20769209) B20769209
theorem B6571655 : Blo 1821612 6571655 := bstep (se 1 (by rfl) ⟨4928741, by rfl⟩ : syracuseStep 6571655 = 9857483) B9857483
theorem B4613831 : Blo 1821612 4613831 := bstep (se 1 (by rfl) ⟨3460373, by rfl⟩ : syracuseStep 4613831 = 6920747) B6920747
theorem B3458771 : Blo 1821612 3458771 := bstep (se 1 (by rfl) ⟨2594078, by rfl⟩ : syracuseStep 3458771 = 5188157) B5188157
theorem B9856727 : Blo 1821612 9856727 := bstep (se 1 (by rfl) ⟨7392545, by rfl⟩ : syracuseStep 9856727 = 14785091) B14785091
theorem B4613881 : Blo 1821612 4613881 := bstep (se 2 (by rfl) ⟨1730205, by rfl⟩ : syracuseStep 4613881 = 3460411) B3460411
theorem B26265505 : Blo 1821612 26265505 := bstep (se 2 (by rfl) ⟨9849564, by rfl⟩ : syracuseStep 26265505 = 19699129) B19699129
theorem B7784353 : Blo 1821612 7784353 := bstep (se 2 (by rfl) ⟨2919132, by rfl⟩ : syracuseStep 7784353 = 5838265) B5838265
theorem B3458999 : Blo 1821612 3458999 := bstep (se 1 (by rfl) ⟨2594249, by rfl⟩ : syracuseStep 3458999 = 5188499) B5188499
theorem B2050087 : Blo 1821612 2050087 := bstep (se 1 (by rfl) ⟨1537565, by rfl⟩ : syracuseStep 2050087 = 3075131) B3075131
theorem B3074105 : Blo 1821612 3074105 := bstep (se 2 (by rfl) ⟨1152789, by rfl⟩ : syracuseStep 3074105 = 2305579) B2305579
theorem B3893305 : Blo 1821612 3893305 := bstep (se 2 (by rfl) ⟨1459989, by rfl⟩ : syracuseStep 3893305 = 2919979) B2919979
theorem B13142093 : Blo 1821612 13142093 := bstep (se 3 (by rfl) ⟨2464142, by rfl⟩ : syracuseStep 13142093 = 4928285) B4928285
theorem B6154487 : Blo 1821612 6154487 := bstep (se 1 (by rfl) ⟨4615865, by rfl⟩ : syracuseStep 6154487 = 9231731) B9231731
theorem B5335421 : Blo 1821612 5335421 := bstep (se 3 (by rfl) ⟨1000391, by rfl⟩ : syracuseStep 5335421 = 2000783) B2000783
theorem B4614529 : Blo 1821612 4614529 := bstep (se 2 (by rfl) ⟨1730448, by rfl⟩ : syracuseStep 4614529 = 3460897) B3460897
theorem B52546229 : Blo 1821612 52546229 := bstep (se 5 (by rfl) ⟨2463104, by rfl⟩ : syracuseStep 52546229 = 4926209) B4926209
theorem B4926167 : Blo 1821612 4926167 := bstep (se 1 (by rfl) ⟨3694625, by rfl⟩ : syracuseStep 4926167 = 7389251) B7389251
theorem B3074807 : Blo 1821612 3074807 := bstep (se 1 (by rfl) ⟨2306105, by rfl⟩ : syracuseStep 3074807 = 4612211) B4612211
theorem B44362565 : Blo 1821612 44362565 := bstep (se 4 (by rfl) ⟨4158990, by rfl⟩ : syracuseStep 44362565 = 8317981) B8317981
theorem B4098923 : Blo 1821612 4098923 := bstep (se 1 (by rfl) ⟨3074192, by rfl⟩ : syracuseStep 4098923 = 6148385) B6148385
theorem B4098977 : Blo 1821612 4098977 := bstep (se 2 (by rfl) ⟨1537116, by rfl⟩ : syracuseStep 4098977 = 3074233) B3074233
theorem B1821615 : Blo 1821612 1821615 := bstep (se 1 (by rfl) ⟨1366211, by rfl⟩ : syracuseStep 1821615 = 2732423) B2732423
theorem B1821639 : Blo 1821612 1821639 := bstep (se 1 (by rfl) ⟨1366229, by rfl⟩ : syracuseStep 1821639 = 2732459) B2732459
theorem B1821659 : Blo 1821612 1821659 := bstep (se 1 (by rfl) ⟨1366244, by rfl⟩ : syracuseStep 1821659 = 2732489) B2732489
theorem B1821735 : Blo 1821612 1821735 := bstep (se 1 (by rfl) ⟨1366301, by rfl⟩ : syracuseStep 1821735 = 2732603) B2732603
theorem B6917177 : Blo 1821612 6917177 := bstep (se 2 (by rfl) ⟨2593941, by rfl⟩ : syracuseStep 6917177 = 5187883) B5187883
theorem B3460153 : Blo 1821612 3460153 := bstep (se 2 (by rfl) ⟨1297557, by rfl⟩ : syracuseStep 3460153 = 2595115) B2595115
theorem B1821775 : Blo 1821612 1821775 := bstep (se 1 (by rfl) ⟨1366331, by rfl⟩ : syracuseStep 1821775 = 2732663) B2732663
theorem B3075151 : Blo 1821612 3075151 := bstep (se 1 (by rfl) ⟨2306363, by rfl⟩ : syracuseStep 3075151 = 4612727) B4612727
theorem B1821791 : Blo 1821612 1821791 := bstep (se 1 (by rfl) ⟨1366343, by rfl⟩ : syracuseStep 1821791 = 2732687) B2732687
theorem B1821819 : Blo 1821612 1821819 := bstep (se 1 (by rfl) ⟨1366364, by rfl⟩ : syracuseStep 1821819 = 2732729) B2732729
theorem B4615339 : Blo 1821612 4615339 := bstep (se 1 (by rfl) ⟨3461504, by rfl⟩ : syracuseStep 4615339 = 6923009) B6923009
theorem B1821871 : Blo 1821612 1821871 := bstep (se 1 (by rfl) ⟨1366403, by rfl⟩ : syracuseStep 1821871 = 2732807) B2732807
theorem B1821895 : Blo 1821612 1821895 := bstep (se 1 (by rfl) ⟨1366421, by rfl⟩ : syracuseStep 1821895 = 2732843) B2732843
theorem B1821915 : Blo 1821612 1821915 := bstep (se 1 (by rfl) ⟨1366436, by rfl⟩ : syracuseStep 1821915 = 2732873) B2732873
theorem B4099319 : Blo 1821612 4099319 := bstep (se 1 (by rfl) ⟨3074489, by rfl⟩ : syracuseStep 4099319 = 6148979) B6148979
theorem B1821991 : Blo 1821612 1821991 := bstep (se 1 (by rfl) ⟨1366493, by rfl⟩ : syracuseStep 1821991 = 2732987) B2732987
theorem B3075401 : Blo 1821612 3075401 := bstep (se 2 (by rfl) ⟨1153275, by rfl⟩ : syracuseStep 3075401 = 2306551) B2306551
theorem B1822031 : Blo 1821612 1822031 := bstep (se 1 (by rfl) ⟨1366523, by rfl⟩ : syracuseStep 1822031 = 2733047) B2733047
theorem B23367001 : Blo 1821612 23367001 := bstep (se 2 (by rfl) ⟨8762625, by rfl⟩ : syracuseStep 23367001 = 17525251) B17525251
theorem B1822047 : Blo 1821612 1822047 := bstep (se 1 (by rfl) ⟨1366535, by rfl⟩ : syracuseStep 1822047 = 2733071) B2733071
theorem B3460457 : Blo 1821612 3460457 := bstep (se 2 (by rfl) ⟨1297671, by rfl⟩ : syracuseStep 3460457 = 2595343) B2595343
theorem B1822075 : Blo 1821612 1822075 := bstep (se 1 (by rfl) ⟨1366556, by rfl⟩ : syracuseStep 1822075 = 2733113) B2733113
theorem B3460495 : Blo 1821612 3460495 := bstep (se 1 (by rfl) ⟨2595371, by rfl⟩ : syracuseStep 3460495 = 5190743) B5190743
theorem B1822127 : Blo 1821612 1822127 := bstep (se 1 (by rfl) ⟨1366595, by rfl⟩ : syracuseStep 1822127 = 2733191) B2733191
theorem B1822151 : Blo 1821612 1822151 := bstep (se 1 (by rfl) ⟨1366613, by rfl⟩ : syracuseStep 1822151 = 2733227) B2733227
theorem B1822171 : Blo 1821612 1822171 := bstep (se 1 (by rfl) ⟨1366628, by rfl⟩ : syracuseStep 1822171 = 2733257) B2733257
theorem B4615643 : Blo 1821612 4615643 := bstep (se 1 (by rfl) ⟨3461732, by rfl⟩ : syracuseStep 4615643 = 6923465) B6923465
theorem B1822247 : Blo 1821612 1822247 := bstep (se 1 (by rfl) ⟨1366685, by rfl⟩ : syracuseStep 1822247 = 2733371) B2733371
theorem B5189159 : Blo 1821612 5189159 := bstep (se 1 (by rfl) ⟨3891869, by rfl⟩ : syracuseStep 5189159 = 7783739) B7783739
theorem B1822287 : Blo 1821612 1822287 := bstep (se 1 (by rfl) ⟨1366715, by rfl⟩ : syracuseStep 1822287 = 2733431) B2733431
theorem B1822303 : Blo 1821612 1822303 := bstep (se 1 (by rfl) ⟨1366727, by rfl⟩ : syracuseStep 1822303 = 2733455) B2733455
theorem B3944033 : Blo 1821612 3944033 := bstep (se 2 (by rfl) ⟨1479012, by rfl⟩ : syracuseStep 3944033 = 2958025) B2958025
theorem B1822331 : Blo 1821612 1822331 := bstep (se 1 (by rfl) ⟨1366748, by rfl⟩ : syracuseStep 1822331 = 2733497) B2733497
theorem B1822383 : Blo 1821612 1822383 := bstep (se 1 (by rfl) ⟨1366787, by rfl⟩ : syracuseStep 1822383 = 2733575) B2733575
theorem B6917831 : Blo 1821612 6917831 := bstep (se 1 (by rfl) ⟨5188373, by rfl⟩ : syracuseStep 6917831 = 10376747) B10376747
theorem B1822407 : Blo 1821612 1822407 := bstep (se 1 (by rfl) ⟨1366805, by rfl⟩ : syracuseStep 1822407 = 2733611) B2733611
theorem B7786199 : Blo 1821612 7786199 := bstep (se 1 (by rfl) ⟨5839649, by rfl⟩ : syracuseStep 7786199 = 11679299) B11679299
theorem B1822427 : Blo 1821612 1822427 := bstep (se 1 (by rfl) ⟨1366820, by rfl⟩ : syracuseStep 1822427 = 2733641) B2733641
theorem B3075833 : Blo 1821612 3075833 := bstep (se 2 (by rfl) ⟨1153437, by rfl⟩ : syracuseStep 3075833 = 2306875) B2306875
theorem B1822503 : Blo 1821612 1822503 := bstep (se 1 (by rfl) ⟨1366877, by rfl⟩ : syracuseStep 1822503 = 2733755) B2733755
theorem B4099913 : Blo 1821612 4099913 := bstep (se 2 (by rfl) ⟨1537467, by rfl⟩ : syracuseStep 4099913 = 3074935) B3074935
theorem B1822543 : Blo 1821612 1822543 := bstep (se 1 (by rfl) ⟨1366907, by rfl⟩ : syracuseStep 1822543 = 2733815) B2733815
theorem B1822559 : Blo 1821612 1822559 := bstep (se 1 (by rfl) ⟨1366919, by rfl⟩ : syracuseStep 1822559 = 2733839) B2733839
theorem B1822587 : Blo 1821612 1822587 := bstep (se 1 (by rfl) ⟨1366940, by rfl⟩ : syracuseStep 1822587 = 2733881) B2733881
theorem B31125383 : Blo 1821612 31125383 := bstep (se 1 (by rfl) ⟨23344037, by rfl⟩ : syracuseStep 31125383 = 46688075) B46688075
theorem B1822639 : Blo 1821612 1822639 := bstep (se 1 (by rfl) ⟨1366979, by rfl⟩ : syracuseStep 1822639 = 2733959) B2733959
theorem B3076015 : Blo 1821612 3076015 := bstep (se 1 (by rfl) ⟨2307011, by rfl⟩ : syracuseStep 3076015 = 4614023) B4614023
theorem B7393207 : Blo 1821612 7393207 := bstep (se 1 (by rfl) ⟨5544905, by rfl⟩ : syracuseStep 7393207 = 11089811) B11089811
theorem B1822663 : Blo 1821612 1822663 := bstep (se 1 (by rfl) ⟨1366997, by rfl⟩ : syracuseStep 1822663 = 2733995) B2733995
theorem B1822683 : Blo 1821612 1822683 := bstep (se 1 (by rfl) ⟨1367012, by rfl⟩ : syracuseStep 1822683 = 2734025) B2734025
theorem B3076103 : Blo 1821612 3076103 := bstep (se 1 (by rfl) ⟨2307077, by rfl⟩ : syracuseStep 3076103 = 4614155) B4614155
theorem B6148115 : Blo 1821612 6148115 := bstep (se 1 (by rfl) ⟨4611086, by rfl⟩ : syracuseStep 6148115 = 9222173) B9222173
theorem B5836819 : Blo 1821612 5836819 := bstep (se 1 (by rfl) ⟨4377614, by rfl⟩ : syracuseStep 5836819 = 8755229) B8755229
theorem B4378643 : Blo 1821612 4378643 := bstep (se 1 (by rfl) ⟨3283982, by rfl⟩ : syracuseStep 4378643 = 6567965) B6567965
theorem B1822759 : Blo 1821612 1822759 := bstep (se 1 (by rfl) ⟨1367069, by rfl⟩ : syracuseStep 1822759 = 2734139) B2734139
theorem B1822799 : Blo 1821612 1822799 := bstep (se 1 (by rfl) ⟨1367099, by rfl⟩ : syracuseStep 1822799 = 2734199) B2734199
theorem B1822815 : Blo 1821612 1822815 := bstep (se 1 (by rfl) ⟨1367111, by rfl⟩ : syracuseStep 1822815 = 2734223) B2734223
theorem B2306171 : Blo 1821612 2306171 := bstep (se 1 (by rfl) ⟨1729628, by rfl⟩ : syracuseStep 2306171 = 3459257) B3459257
theorem B1822843 : Blo 1821612 1822843 := bstep (se 1 (by rfl) ⟨1367132, by rfl⟩ : syracuseStep 1822843 = 2734265) B2734265
theorem B1822895 : Blo 1821612 1822895 := bstep (se 1 (by rfl) ⟨1367171, by rfl⟩ : syracuseStep 1822895 = 2734343) B2734343
theorem B1822919 : Blo 1821612 1822919 := bstep (se 1 (by rfl) ⟨1367189, by rfl⟩ : syracuseStep 1822919 = 2734379) B2734379
theorem B1822939 : Blo 1821612 1822939 := bstep (se 1 (by rfl) ⟨1367204, by rfl⟩ : syracuseStep 1822939 = 2734409) B2734409
theorem B1823015 : Blo 1821612 1823015 := bstep (se 1 (by rfl) ⟨1367261, by rfl⟩ : syracuseStep 1823015 = 2734523) B2734523
theorem B12464435 : Blo 1821612 12464435 := bstep (se 1 (by rfl) ⟨9348326, by rfl⟩ : syracuseStep 12464435 = 18696653) B18696653
theorem B1823055 : Blo 1821612 1823055 := bstep (se 1 (by rfl) ⟨1367291, by rfl⟩ : syracuseStep 1823055 = 2734583) B2734583
theorem B6148439 : Blo 1821612 6148439 := bstep (se 1 (by rfl) ⟨4611329, by rfl⟩ : syracuseStep 6148439 = 9222659) B9222659
theorem B13136215 : Blo 1821612 13136215 := bstep (se 1 (by rfl) ⟨9852161, by rfl⟩ : syracuseStep 13136215 = 19704323) B19704323
theorem B1823071 : Blo 1821612 1823071 := bstep (se 1 (by rfl) ⟨1367303, by rfl⟩ : syracuseStep 1823071 = 2734607) B2734607
theorem B3076447 : Blo 1821612 3076447 := bstep (se 1 (by rfl) ⟨2307335, by rfl⟩ : syracuseStep 3076447 = 4614671) B4614671
theorem B2920799 : Blo 1821612 2920799 := bstep (se 1 (by rfl) ⟨2190599, by rfl⟩ : syracuseStep 2920799 = 4381199) B4381199
theorem B1823099 : Blo 1821612 1823099 := bstep (se 1 (by rfl) ⟨1367324, by rfl⟩ : syracuseStep 1823099 = 2734649) B2734649
theorem B13840793 : Blo 1821612 13840793 := bstep (se 2 (by rfl) ⟨5190297, by rfl⟩ : syracuseStep 13840793 = 10380595) B10380595
theorem B1823151 : Blo 1821612 1823151 := bstep (se 1 (by rfl) ⟨1367363, by rfl⟩ : syracuseStep 1823151 = 2734727) B2734727
theorem B2732471 : Blo 1821612 2732471 := bstep (se 1 (by rfl) ⟨2049353, by rfl⟩ : syracuseStep 2732471 = 4098707) B4098707
theorem B3076535 : Blo 1821612 3076535 := bstep (se 1 (by rfl) ⟨2307401, by rfl⟩ : syracuseStep 3076535 = 4614803) B4614803
theorem B1823175 : Blo 1821612 1823175 := bstep (se 1 (by rfl) ⟨1367381, by rfl⟩ : syracuseStep 1823175 = 2734763) B2734763
theorem B2732507 : Blo 1821612 2732507 := bstep (se 1 (by rfl) ⟨2049380, by rfl⟩ : syracuseStep 2732507 = 4098761) B4098761
theorem B1823195 : Blo 1821612 1823195 := bstep (se 1 (by rfl) ⟨1367396, by rfl⟩ : syracuseStep 1823195 = 2734793) B2734793
theorem B4379123 : Blo 1821612 4379123 := bstep (se 1 (by rfl) ⟨3284342, by rfl⟩ : syracuseStep 4379123 = 6568685) B6568685
theorem B12472865 : Blo 1821612 12472865 := bstep (se 2 (by rfl) ⟨4677324, by rfl⟩ : syracuseStep 12472865 = 9354649) B9354649
theorem B1823271 : Blo 1821612 1823271 := bstep (se 1 (by rfl) ⟨1367453, by rfl⟩ : syracuseStep 1823271 = 2734907) B2734907
theorem B1946191 : Blo 1821612 1946191 := bstep (se 1 (by rfl) ⟨1459643, by rfl⟩ : syracuseStep 1946191 = 2919287) B2919287
theorem B1823311 : Blo 1821612 1823311 := bstep (se 1 (by rfl) ⟨1367483, by rfl⟩ : syracuseStep 1823311 = 2734967) B2734967
theorem B1823327 : Blo 1821612 1823327 := bstep (se 1 (by rfl) ⟨1367495, by rfl⟩ : syracuseStep 1823327 = 2734991) B2734991
theorem B4100705 : Blo 1821612 4100705 := bstep (se 2 (by rfl) ⟨1537764, by rfl⟩ : syracuseStep 4100705 = 3075529) B3075529
theorem B7393889 : Blo 1821612 7393889 := bstep (se 2 (by rfl) ⟨2772708, by rfl⟩ : syracuseStep 7393889 = 5545417) B5545417
theorem B1823355 : Blo 1821612 1823355 := bstep (se 1 (by rfl) ⟨1367516, by rfl⟩ : syracuseStep 1823355 = 2735033) B2735033
theorem B6918803 : Blo 1821612 6918803 := bstep (se 1 (by rfl) ⟨5189102, by rfl⟩ : syracuseStep 6918803 = 10378205) B10378205
theorem B15782573 : Blo 1821612 15782573 := bstep (se 3 (by rfl) ⟨2959232, by rfl⟩ : syracuseStep 15782573 = 5918465) B5918465
theorem B1823407 : Blo 1821612 1823407 := bstep (se 1 (by rfl) ⟨1367555, by rfl⟩ : syracuseStep 1823407 = 2735111) B2735111
theorem B1823431 : Blo 1821612 1823431 := bstep (se 1 (by rfl) ⟨1367573, by rfl⟩ : syracuseStep 1823431 = 2735147) B2735147
theorem B6566609 : Blo 1821612 6566609 := bstep (se 2 (by rfl) ⟨2462478, by rfl⟩ : syracuseStep 6566609 = 4924957) B4924957
theorem B1823451 : Blo 1821612 1823451 := bstep (se 1 (by rfl) ⟨1367588, by rfl⟩ : syracuseStep 1823451 = 2735177) B2735177
theorem B1823527 : Blo 1821612 1823527 := bstep (se 1 (by rfl) ⟨1367645, by rfl⟩ : syracuseStep 1823527 = 2735291) B2735291
theorem B7107401 : Blo 1821612 7107401 := bstep (se 2 (by rfl) ⟨2665275, by rfl⟩ : syracuseStep 7107401 = 5330551) B5330551
theorem B1823567 : Blo 1821612 1823567 := bstep (se 1 (by rfl) ⟨1367675, by rfl⟩ : syracuseStep 1823567 = 2735351) B2735351
theorem B1823583 : Blo 1821612 1823583 := bstep (se 1 (by rfl) ⟨1367687, by rfl⟩ : syracuseStep 1823583 = 2735375) B2735375
theorem B1823611 : Blo 1821612 1823611 := bstep (se 1 (by rfl) ⟨1367708, by rfl⟩ : syracuseStep 1823611 = 2735417) B2735417
theorem B4928417 : Blo 1821612 4928417 := bstep (se 2 (by rfl) ⟨1848156, by rfl⟩ : syracuseStep 4928417 = 3696313) B3696313
theorem B2732975 : Blo 1821612 2732975 := bstep (se 1 (by rfl) ⟨2049731, by rfl⟩ : syracuseStep 2732975 = 4099463) B4099463
theorem B23352239 : Blo 1821612 23352239 := bstep (se 1 (by rfl) ⟨17514179, by rfl⟩ : syracuseStep 23352239 = 35028359) B35028359
theorem B4101047 : Blo 1821612 4101047 := bstep (se 1 (by rfl) ⟨3075785, by rfl⟩ : syracuseStep 4101047 = 6151571) B6151571
theorem B2733065 : Blo 1821612 2733065 := bstep (se 2 (by rfl) ⟨1024899, by rfl⟩ : syracuseStep 2733065 = 2049799) B2049799
theorem B3077129 : Blo 1821612 3077129 := bstep (se 2 (by rfl) ⟨1153923, by rfl⟩ : syracuseStep 3077129 = 2307847) B2307847
theorem B2733095 : Blo 1821612 2733095 := bstep (se 1 (by rfl) ⟨2049821, by rfl⟩ : syracuseStep 2733095 = 4099643) B4099643
theorem B17511491 : Blo 1821612 17511491 := bstep (se 1 (by rfl) ⟨13133618, by rfl⟩ : syracuseStep 17511491 = 26267237) B26267237
theorem B2733179 : Blo 1821612 2733179 := bstep (se 1 (by rfl) ⟨2049884, by rfl⟩ : syracuseStep 2733179 = 4099769) B4099769
theorem B3077291 : Blo 1821612 3077291 := bstep (se 1 (by rfl) ⟨2307968, by rfl⟩ : syracuseStep 3077291 = 4615937) B4615937
theorem B2733305 : Blo 1821612 2733305 := bstep (se 2 (by rfl) ⟨1024989, by rfl⟩ : syracuseStep 2733305 = 2049979) B2049979
theorem B2733407 : Blo 1821612 2733407 := bstep (se 1 (by rfl) ⟨2050055, by rfl⟩ : syracuseStep 2733407 = 4100111) B4100111
theorem B2733419 : Blo 1821612 2733419 := bstep (se 1 (by rfl) ⟨2050064, by rfl⟩ : syracuseStep 2733419 = 4100129) B4100129
theorem B6149519 : Blo 1821612 6149519 := bstep (se 1 (by rfl) ⟨4612139, by rfl⟩ : syracuseStep 6149519 = 9224279) B9224279
theorem B9229787 : Blo 1821612 9229787 := bstep (se 1 (by rfl) ⟨6922340, by rfl⟩ : syracuseStep 9229787 = 13844681) B13844681
theorem B4101641 : Blo 1821612 4101641 := bstep (se 2 (by rfl) ⟨1538115, by rfl⟩ : syracuseStep 4101641 = 3076231) B3076231
theorem B2733647 : Blo 1821612 2733647 := bstep (se 1 (by rfl) ⟨2050235, by rfl⟩ : syracuseStep 2733647 = 4100471) B4100471
theorem B4380257 : Blo 1821612 4380257 := bstep (se 2 (by rfl) ⟨1642596, by rfl⟩ : syracuseStep 4380257 = 3285193) B3285193
theorem B12465809 : Blo 1821612 12465809 := bstep (se 2 (by rfl) ⟨4674678, by rfl⟩ : syracuseStep 12465809 = 9349357) B9349357
theorem B2733767 : Blo 1821612 2733767 := bstep (se 1 (by rfl) ⟨2050325, by rfl⟩ : syracuseStep 2733767 = 4100651) B4100651
theorem B6149843 : Blo 1821612 6149843 := bstep (se 1 (by rfl) ⟨4612382, by rfl⟩ : syracuseStep 6149843 = 9224765) B9224765
theorem B4101983 : Blo 1821612 4101983 := bstep (se 1 (by rfl) ⟨3076487, by rfl⟩ : syracuseStep 4101983 = 6152975) B6152975
theorem B2733929 : Blo 1821612 2733929 := bstep (se 2 (by rfl) ⟨1025223, by rfl⟩ : syracuseStep 2733929 = 2050447) B2050447
theorem B4437935 : Blo 1821612 4437935 := bstep (se 1 (by rfl) ⟨3328451, by rfl⟩ : syracuseStep 4437935 = 6656903) B6656903
theorem B5838767 : Blo 1821612 5838767 := bstep (se 1 (by rfl) ⟨4379075, by rfl⟩ : syracuseStep 5838767 = 8758151) B8758151
theorem B2734007 : Blo 1821612 2734007 := bstep (se 1 (by rfl) ⟨2050505, by rfl⟩ : syracuseStep 2734007 = 4101011) B4101011
theorem B9230273 : Blo 1821612 9230273 := bstep (se 2 (by rfl) ⟨3461352, by rfl⟩ : syracuseStep 9230273 = 6922705) B6922705
theorem B2734043 : Blo 1821612 2734043 := bstep (se 1 (by rfl) ⟨2050532, by rfl⟩ : syracuseStep 2734043 = 4101065) B4101065
theorem B4102163 : Blo 1821612 4102163 := bstep (se 1 (by rfl) ⟨3076622, by rfl⟩ : syracuseStep 4102163 = 6153245) B6153245
theorem B11671609 : Blo 1821612 11671609 := bstep (se 2 (by rfl) ⟨4376853, by rfl⟩ : syracuseStep 11671609 = 8753707) B8753707
theorem B13842737 : Blo 1821612 13842737 := bstep (se 2 (by rfl) ⟨5191026, by rfl⟩ : syracuseStep 13842737 = 10382053) B10382053
theorem B17520947 : Blo 1821612 17520947 := bstep (se 1 (by rfl) ⟨13140710, by rfl⟩ : syracuseStep 17520947 = 26281421) B26281421
theorem B4102505 : Blo 1821612 4102505 := bstep (se 2 (by rfl) ⟨1538439, by rfl⟩ : syracuseStep 4102505 = 3076879) B3076879
theorem B2734511 : Blo 1821612 2734511 := bstep (se 1 (by rfl) ⟨2050883, by rfl⟩ : syracuseStep 2734511 = 4101767) B4101767
theorem B2734601 : Blo 1821612 2734601 := bstep (se 2 (by rfl) ⟨1025475, by rfl⟩ : syracuseStep 2734601 = 2050951) B2050951
theorem B5192201 : Blo 1821612 5192201 := bstep (se 2 (by rfl) ⟨1947075, by rfl⟩ : syracuseStep 5192201 = 3894151) B3894151
theorem B5839393 : Blo 1821612 5839393 := bstep (se 2 (by rfl) ⟨2189772, by rfl⟩ : syracuseStep 5839393 = 4379545) B4379545
theorem B2734631 : Blo 1821612 2734631 := bstep (se 1 (by rfl) ⟨2050973, by rfl⟩ : syracuseStep 2734631 = 4101947) B4101947
theorem B2734715 : Blo 1821612 2734715 := bstep (se 1 (by rfl) ⟨2051036, by rfl⟩ : syracuseStep 2734715 = 4102073) B4102073
theorem B13834961 : Blo 1821612 13834961 := bstep (se 2 (by rfl) ⟨5188110, by rfl⟩ : syracuseStep 13834961 = 10376221) B10376221
theorem B2734841 : Blo 1821612 2734841 := bstep (se 2 (by rfl) ⟨1025565, by rfl⟩ : syracuseStep 2734841 = 2051131) B2051131
theorem B29547341 : Blo 1821612 29547341 := bstep (se 3 (by rfl) ⟨5540126, by rfl⟩ : syracuseStep 29547341 = 11080253) B11080253
theorem B2734943 : Blo 1821612 2734943 := bstep (se 1 (by rfl) ⟨2051207, by rfl⟩ : syracuseStep 2734943 = 4102415) B4102415
theorem B2734955 : Blo 1821612 2734955 := bstep (se 1 (by rfl) ⟨2051216, by rfl⟩ : syracuseStep 2734955 = 4102433) B4102433
theorem B6151031 : Blo 1821612 6151031 := bstep (se 1 (by rfl) ⟨4613273, by rfl⟩ : syracuseStep 6151031 = 9226547) B9226547
theorem B4103099 : Blo 1821612 4103099 := bstep (se 1 (by rfl) ⟨3077324, by rfl⟩ : syracuseStep 4103099 = 6154649) B6154649
theorem B5258297 : Blo 1821612 5258297 := bstep (se 2 (by rfl) ⟨1971861, by rfl⟩ : syracuseStep 5258297 = 3943723) B3943723
theorem B12467279 : Blo 1821612 12467279 := bstep (se 1 (by rfl) ⟨9350459, by rfl⟩ : syracuseStep 12467279 = 18700919) B18700919
theorem B6151247 : Blo 1821612 6151247 := bstep (se 1 (by rfl) ⟨4613435, by rfl⟩ : syracuseStep 6151247 = 9226871) B9226871
theorem B2735183 : Blo 1821612 2735183 := bstep (se 1 (by rfl) ⟨2051387, by rfl⟩ : syracuseStep 2735183 = 4102775) B4102775
theorem B6233203 : Blo 1821612 6233203 := bstep (se 1 (by rfl) ⟨4674902, by rfl⟩ : syracuseStep 6233203 = 9349805) B9349805
theorem B7011481 : Blo 1821612 7011481 := bstep (se 2 (by rfl) ⟨2629305, by rfl⟩ : syracuseStep 7011481 = 5258611) B5258611
theorem B2735303 : Blo 1821612 2735303 := bstep (se 1 (by rfl) ⟨2051477, by rfl⟩ : syracuseStep 2735303 = 4102955) B4102955
theorem B2809193 : Blo 1821612 2809193 := bstep (se 2 (by rfl) ⟨1053447, by rfl⟩ : syracuseStep 2809193 = 2106895) B2106895
theorem B6151625 : Blo 1821612 6151625 := bstep (se 2 (by rfl) ⟨2306859, by rfl⟩ : syracuseStep 6151625 = 4613719) B4613719
theorem B13131227 : Blo 1821612 13131227 := bstep (se 1 (by rfl) ⟨9848420, by rfl⟩ : syracuseStep 13131227 = 19696841) B19696841
theorem B4611593 : Blo 1821612 4611593 := bstep (se 2 (by rfl) ⟨1729347, by rfl⟩ : syracuseStep 4611593 = 3458695) B3458695
theorem B13319741 : Blo 1821612 13319741 := bstep (se 3 (by rfl) ⟨2497451, by rfl⟩ : syracuseStep 13319741 = 4994903) B4994903
theorem B6151895 : Blo 1821612 6151895 := bstep (se 1 (by rfl) ⟨4613921, by rfl⟩ : syracuseStep 6151895 = 9227843) B9227843
theorem B9854713 : Blo 1821612 9854713 := bstep (se 2 (by rfl) ⟨3695517, by rfl⟩ : syracuseStep 9854713 = 7391035) B7391035
theorem B42082163 : Blo 1821612 42082163 := bstep (se 1 (by rfl) ⟨31561622, by rfl⟩ : syracuseStep 42082163 = 63123245) B63123245
theorem B16859015 : Blo 1821612 16859015 := bstep (se 1 (by rfl) ⟨12644261, by rfl⟩ : syracuseStep 16859015 = 25288523) B25288523
theorem B6152111 : Blo 1821612 6152111 := bstep (se 1 (by rfl) ⟨4614083, by rfl⟩ : syracuseStep 6152111 = 9228167) B9228167
theorem B7782425 : Blo 1821612 7782425 := bstep (se 2 (by rfl) ⟨2918409, by rfl⟩ : syracuseStep 7782425 = 5836819) B5836819
theorem B35045581 : Blo 1821612 35045581 := bstep (se 3 (by rfl) ⟨6571046, by rfl⟩ : syracuseStep 35045581 = 13142093) B13142093
theorem B8315243 : Blo 1821612 8315243 := bstep (se 1 (by rfl) ⟨6236432, by rfl⟩ : syracuseStep 8315243 = 12472865) B12472865
theorem B4612535 : Blo 1821612 4612535 := bstep (se 1 (by rfl) ⟨3459401, by rfl⟩ : syracuseStep 4612535 = 6918803) B6918803
theorem B17514953 : Blo 1821612 17514953 := bstep (se 2 (by rfl) ⟨6568107, by rfl⟩ : syracuseStep 17514953 = 13136215) B13136215
theorem B26280449 : Blo 1821612 26280449 := bstep (se 2 (by rfl) ⟨9855168, by rfl⟩ : syracuseStep 26280449 = 19710337) B19710337
theorem B6152705 : Blo 1821612 6152705 := bstep (se 2 (by rfl) ⟨2307264, by rfl⟩ : syracuseStep 6152705 = 4614529) B4614529
theorem B16630343 : Blo 1821612 16630343 := bstep (se 1 (by rfl) ⟨12472757, by rfl⟩ : syracuseStep 16630343 = 24945515) B24945515
theorem B3285611 : Blo 1821612 3285611 := bstep (se 1 (by rfl) ⟨2464208, by rfl⟩ : syracuseStep 3285611 = 4928417) B4928417
theorem B11674327 : Blo 1821612 11674327 := bstep (se 1 (by rfl) ⟨8755745, by rfl⟩ : syracuseStep 11674327 = 17511491) B17511491
theorem B9224927 : Blo 1821612 9224927 := bstep (se 1 (by rfl) ⟨6918695, by rfl⟩ : syracuseStep 9224927 = 13837391) B13837391
theorem B4441051 : Blo 1821612 4441051 := bstep (se 1 (by rfl) ⟨3330788, by rfl⟩ : syracuseStep 4441051 = 6661577) B6661577
theorem B6153191 : Blo 1821612 6153191 := bstep (se 1 (by rfl) ⟨4614893, by rfl⟩ : syracuseStep 6153191 = 9229787) B9229787
theorem B6571151 : Blo 1821612 6571151 := bstep (se 1 (by rfl) ⟨4928363, by rfl⟩ : syracuseStep 6571151 = 9856727) B9856727
theorem B2958623 : Blo 1821612 2958623 := bstep (se 1 (by rfl) ⟨2218967, by rfl⟩ : syracuseStep 2958623 = 4437935) B4437935
theorem B3892511 : Blo 1821612 3892511 := bstep (se 1 (by rfl) ⟨2919383, by rfl⟩ : syracuseStep 3892511 = 5838767) B5838767
theorem B6153515 : Blo 1821612 6153515 := bstep (se 1 (by rfl) ⟨4615136, by rfl⟩ : syracuseStep 6153515 = 9230273) B9230273
theorem B56911157 : Blo 1821612 56911157 := bstep (se 5 (by rfl) ⟨2667710, by rfl⟩ : syracuseStep 56911157 = 5335421) B5335421
theorem B2049403 : Blo 1821612 2049403 := bstep (se 1 (by rfl) ⟨1537052, by rfl⟩ : syracuseStep 2049403 = 3074105) B3074105
theorem B4613537 : Blo 1821612 4613537 := bstep (se 2 (by rfl) ⟨1730076, by rfl⟩ : syracuseStep 4613537 = 3460153) B3460153
theorem B9348641 : Blo 1821612 9348641 := bstep (se 2 (by rfl) ⟨3505740, by rfl⟩ : syracuseStep 9348641 = 7011481) B7011481
theorem B6153785 : Blo 1821612 6153785 := bstep (se 2 (by rfl) ⟨2307669, by rfl⟩ : syracuseStep 6153785 = 4615339) B4615339
theorem B31156001 : Blo 1821612 31156001 := bstep (se 2 (by rfl) ⟨11683500, by rfl⟩ : syracuseStep 31156001 = 23367001) B23367001
theorem B35030819 : Blo 1821612 35030819 := bstep (se 1 (by rfl) ⟨26273114, by rfl⟩ : syracuseStep 35030819 = 52546229) B52546229
theorem B2049871 : Blo 1821612 2049871 := bstep (se 1 (by rfl) ⟨1537403, by rfl⟩ : syracuseStep 2049871 = 3074807) B3074807
theorem B4613993 : Blo 1821612 4613993 := bstep (se 2 (by rfl) ⟨1730247, by rfl⟩ : syracuseStep 4613993 = 3460495) B3460495
theorem B13141865 : Blo 1821612 13141865 := bstep (se 2 (by rfl) ⟨4928199, by rfl⟩ : syracuseStep 13141865 = 9856399) B9856399
theorem B29575043 : Blo 1821612 29575043 := bstep (se 1 (by rfl) ⟨22181282, by rfl⟩ : syracuseStep 29575043 = 44362565) B44362565
theorem B2050267 : Blo 1821612 2050267 := bstep (se 1 (by rfl) ⟨1537700, by rfl⟩ : syracuseStep 2050267 = 3075401) B3075401
theorem B3074395 : Blo 1821612 3074395 := bstep (se 1 (by rfl) ⟨2305796, by rfl⟩ : syracuseStep 3074395 = 4611593) B4611593
theorem B3459439 : Blo 1821612 3459439 := bstep (se 1 (by rfl) ⟨2594579, by rfl⟩ : syracuseStep 3459439 = 5189159) B5189159
theorem B2050555 : Blo 1821612 2050555 := bstep (se 1 (by rfl) ⟨1537916, by rfl⟩ : syracuseStep 2050555 = 3075833) B3075833
theorem B9857609 : Blo 1821612 9857609 := bstep (se 2 (by rfl) ⟨3696603, by rfl⟩ : syracuseStep 9857609 = 7393207) B7393207
theorem B2050735 : Blo 1821612 2050735 := bstep (se 1 (by rfl) ⟨1538051, by rfl⟩ : syracuseStep 2050735 = 3076103) B3076103
theorem B4098743 : Blo 1821612 4098743 := bstep (se 1 (by rfl) ⟨3074057, by rfl⟩ : syracuseStep 4098743 = 6148115) B6148115
theorem B2919095 : Blo 1821612 2919095 := bstep (se 1 (by rfl) ⟨2189321, by rfl⟩ : syracuseStep 2919095 = 4378643) B4378643
theorem B8309623 : Blo 1821612 8309623 := bstep (se 1 (by rfl) ⟨6232217, by rfl⟩ : syracuseStep 8309623 = 12464435) B12464435
theorem B4098959 : Blo 1821612 4098959 := bstep (se 1 (by rfl) ⟨3074219, by rfl⟩ : syracuseStep 4098959 = 6148439) B6148439
theorem B9227195 : Blo 1821612 9227195 := bstep (se 1 (by rfl) ⟨6920396, by rfl⟩ : syracuseStep 9227195 = 13840793) B13840793
theorem B1821647 : Blo 1821612 1821647 := bstep (se 1 (by rfl) ⟨1366235, by rfl⟩ : syracuseStep 1821647 = 2732471) B2732471
theorem B2051023 : Blo 1821612 2051023 := bstep (se 1 (by rfl) ⟨1538267, by rfl⟩ : syracuseStep 2051023 = 3076535) B3076535
theorem B1821671 : Blo 1821612 1821671 := bstep (se 1 (by rfl) ⟨1366253, by rfl⟩ : syracuseStep 1821671 = 2732507) B2732507
theorem B2919415 : Blo 1821612 2919415 := bstep (se 1 (by rfl) ⟨2189561, by rfl⟩ : syracuseStep 2919415 = 4379123) B4379123
theorem B6237307 : Blo 1821612 6237307 := bstep (se 1 (by rfl) ⟨4677980, by rfl⟩ : syracuseStep 6237307 = 9355961) B9355961
theorem B4377739 : Blo 1821612 4377739 := bstep (se 1 (by rfl) ⟨3283304, by rfl⟩ : syracuseStep 4377739 = 6566609) B6566609
theorem B4738267 : Blo 1821612 4738267 := bstep (se 1 (by rfl) ⟨3553700, by rfl⟩ : syracuseStep 4738267 = 7107401) B7107401
theorem B1821983 : Blo 1821612 1821983 := bstep (se 1 (by rfl) ⟨1366487, by rfl⟩ : syracuseStep 1821983 = 2732975) B2732975
theorem B15568159 : Blo 1821612 15568159 := bstep (se 1 (by rfl) ⟨11676119, by rfl⟩ : syracuseStep 15568159 = 23352239) B23352239
theorem B3075367 : Blo 1821612 3075367 := bstep (se 1 (by rfl) ⟨2306525, by rfl⟩ : syracuseStep 3075367 = 4613051) B4613051
theorem B1822043 : Blo 1821612 1822043 := bstep (se 1 (by rfl) ⟨1366532, by rfl⟩ : syracuseStep 1822043 = 2733065) B2733065
theorem B2051419 : Blo 1821612 2051419 := bstep (se 1 (by rfl) ⟨1538564, by rfl⟩ : syracuseStep 2051419 = 3077129) B3077129
theorem B1822063 : Blo 1821612 1822063 := bstep (se 1 (by rfl) ⟨1366547, by rfl⟩ : syracuseStep 1822063 = 2733095) B2733095
theorem B22179187 : Blo 1821612 22179187 := bstep (se 1 (by rfl) ⟨16634390, by rfl⟩ : syracuseStep 22179187 = 33268781) B33268781
theorem B7785857 : Blo 1821612 7785857 := bstep (se 2 (by rfl) ⟨2919696, by rfl⟩ : syracuseStep 7785857 = 5839393) B5839393
theorem B1822119 : Blo 1821612 1822119 := bstep (se 1 (by rfl) ⟨1366589, by rfl⟩ : syracuseStep 1822119 = 2733179) B2733179
theorem B2051527 : Blo 1821612 2051527 := bstep (se 1 (by rfl) ⟨1538645, by rfl⟩ : syracuseStep 2051527 = 3077291) B3077291
theorem B5189113 : Blo 1821612 5189113 := bstep (se 2 (by rfl) ⟨1945917, by rfl⟩ : syracuseStep 5189113 = 3891835) B3891835
theorem B1822203 : Blo 1821612 1822203 := bstep (se 1 (by rfl) ⟨1366652, by rfl⟩ : syracuseStep 1822203 = 2733305) B2733305
theorem B1822271 : Blo 1821612 1822271 := bstep (se 1 (by rfl) ⟨1366703, by rfl⟩ : syracuseStep 1822271 = 2733407) B2733407
theorem B1822279 : Blo 1821612 1822279 := bstep (se 1 (by rfl) ⟨1366709, by rfl⟩ : syracuseStep 1822279 = 2733419) B2733419
theorem B4099679 : Blo 1821612 4099679 := bstep (se 1 (by rfl) ⟨3074759, by rfl⟩ : syracuseStep 4099679 = 6149519) B6149519
theorem B4615775 : Blo 1821612 4615775 := bstep (se 1 (by rfl) ⟨3461831, by rfl⟩ : syracuseStep 4615775 = 6923663) B6923663
theorem B25964225 : Blo 1821612 25964225 := bstep (se 2 (by rfl) ⟨9736584, by rfl⟩ : syracuseStep 25964225 = 19473169) B19473169
theorem B1822431 : Blo 1821612 1822431 := bstep (se 1 (by rfl) ⟨1366823, by rfl⟩ : syracuseStep 1822431 = 2733647) B2733647
theorem B8310539 : Blo 1821612 8310539 := bstep (se 1 (by rfl) ⟨6232904, by rfl⟩ : syracuseStep 8310539 = 12465809) B12465809
theorem B1822511 : Blo 1821612 1822511 := bstep (se 1 (by rfl) ⟨1366883, by rfl⟩ : syracuseStep 1822511 = 2733767) B2733767
theorem B3075887 : Blo 1821612 3075887 := bstep (se 1 (by rfl) ⟨2306915, by rfl⟩ : syracuseStep 3075887 = 4613831) B4613831
theorem B2305847 : Blo 1821612 2305847 := bstep (se 1 (by rfl) ⟨1729385, by rfl⟩ : syracuseStep 2305847 = 3458771) B3458771
theorem B4099895 : Blo 1821612 4099895 := bstep (se 1 (by rfl) ⟨3074921, by rfl⟩ : syracuseStep 4099895 = 6149843) B6149843
theorem B1822619 : Blo 1821612 1822619 := bstep (se 1 (by rfl) ⟨1366964, by rfl⟩ : syracuseStep 1822619 = 2733929) B2733929
theorem B2305999 : Blo 1821612 2305999 := bstep (se 1 (by rfl) ⟨1729499, by rfl⟩ : syracuseStep 2305999 = 3458999) B3458999
theorem B1822671 : Blo 1821612 1822671 := bstep (se 1 (by rfl) ⟨1367003, by rfl⟩ : syracuseStep 1822671 = 2734007) B2734007
theorem B1822695 : Blo 1821612 1822695 := bstep (se 1 (by rfl) ⟨1367021, by rfl⟩ : syracuseStep 1822695 = 2734043) B2734043
theorem B119869469 : Blo 1821612 119869469 := bstep (se 3 (by rfl) ⟨22475525, by rfl⟩ : syracuseStep 119869469 = 44951051) B44951051
theorem B17510489 : Blo 1821612 17510489 := bstep (se 2 (by rfl) ⟨6566433, by rfl⟩ : syracuseStep 17510489 = 13132867) B13132867
theorem B4100201 : Blo 1821612 4100201 := bstep (se 2 (by rfl) ⟨1537575, by rfl⟩ : syracuseStep 4100201 = 3075151) B3075151
theorem B8310937 : Blo 1821612 8310937 := bstep (se 2 (by rfl) ⟨3116601, by rfl⟩ : syracuseStep 8310937 = 6233203) B6233203
theorem B9228491 : Blo 1821612 9228491 := bstep (se 1 (by rfl) ⟨6921368, by rfl⟩ : syracuseStep 9228491 = 13842737) B13842737
theorem B1823007 : Blo 1821612 1823007 := bstep (se 1 (by rfl) ⟨1367255, by rfl⟩ : syracuseStep 1823007 = 2734511) B2734511
theorem B1823067 : Blo 1821612 1823067 := bstep (se 1 (by rfl) ⟨1367300, by rfl⟩ : syracuseStep 1823067 = 2734601) B2734601
theorem B3461467 : Blo 1821612 3461467 := bstep (se 1 (by rfl) ⟨2596100, by rfl⟩ : syracuseStep 3461467 = 5192201) B5192201
theorem B1823087 : Blo 1821612 1823087 := bstep (se 1 (by rfl) ⟨1367315, by rfl⟩ : syracuseStep 1823087 = 2734631) B2734631
theorem B1823143 : Blo 1821612 1823143 := bstep (se 1 (by rfl) ⟨1367357, by rfl⟩ : syracuseStep 1823143 = 2734715) B2734715
theorem B42086861 : Blo 1821612 42086861 := bstep (se 3 (by rfl) ⟨7891286, by rfl⟩ : syracuseStep 42086861 = 15782573) B15782573
theorem B1823227 : Blo 1821612 1823227 := bstep (se 1 (by rfl) ⟨1367420, by rfl⟩ : syracuseStep 1823227 = 2734841) B2734841
theorem B19698227 : Blo 1821612 19698227 := bstep (se 1 (by rfl) ⟨14773670, by rfl⟩ : syracuseStep 19698227 = 29547341) B29547341
theorem B1823295 : Blo 1821612 1823295 := bstep (se 1 (by rfl) ⟨1367471, by rfl⟩ : syracuseStep 1823295 = 2734943) B2734943
theorem B2732615 : Blo 1821612 2732615 := bstep (se 1 (by rfl) ⟨2049461, by rfl⟩ : syracuseStep 2732615 = 4098923) B4098923
theorem B1823303 : Blo 1821612 1823303 := bstep (se 1 (by rfl) ⟨1367477, by rfl⟩ : syracuseStep 1823303 = 2734955) B2734955
theorem B4100687 : Blo 1821612 4100687 := bstep (se 1 (by rfl) ⟨3075515, by rfl⟩ : syracuseStep 4100687 = 6151031) B6151031
theorem B2732651 : Blo 1821612 2732651 := bstep (se 1 (by rfl) ⟨2049488, by rfl⟩ : syracuseStep 2732651 = 4098977) B4098977
theorem B8311519 : Blo 1821612 8311519 := bstep (se 1 (by rfl) ⟨6233639, by rfl⟩ : syracuseStep 8311519 = 12467279) B12467279
theorem B4100831 : Blo 1821612 4100831 := bstep (se 1 (by rfl) ⟨3075623, by rfl⟩ : syracuseStep 4100831 = 6151247) B6151247
theorem B1823455 : Blo 1821612 1823455 := bstep (se 1 (by rfl) ⟨1367591, by rfl⟩ : syracuseStep 1823455 = 2735183) B2735183
theorem B1823535 : Blo 1821612 1823535 := bstep (se 1 (by rfl) ⟨1367651, by rfl⟩ : syracuseStep 1823535 = 2735303) B2735303
theorem B2732879 : Blo 1821612 2732879 := bstep (se 1 (by rfl) ⟨2049659, by rfl⟩ : syracuseStep 2732879 = 4099319) B4099319
theorem B2306971 : Blo 1821612 2306971 := bstep (se 1 (by rfl) ⟨1730228, by rfl⟩ : syracuseStep 2306971 = 3460457) B3460457
theorem B4101083 : Blo 1821612 4101083 := bstep (se 1 (by rfl) ⟨3075812, by rfl⟩ : syracuseStep 4101083 = 6151625) B6151625
theorem B8754151 : Blo 1821612 8754151 := bstep (se 1 (by rfl) ⟨6565613, by rfl⟩ : syracuseStep 8754151 = 13131227) B13131227
theorem B3077095 : Blo 1821612 3077095 := bstep (se 1 (by rfl) ⟨2307821, by rfl⟩ : syracuseStep 3077095 = 4615643) B4615643
theorem B4101263 : Blo 1821612 4101263 := bstep (se 1 (by rfl) ⟨3075947, by rfl⟩ : syracuseStep 4101263 = 6151895) B6151895
theorem B5190799 : Blo 1821612 5190799 := bstep (se 1 (by rfl) ⟨3893099, by rfl⟩ : syracuseStep 5190799 = 7786199) B7786199
theorem B2733275 : Blo 1821612 2733275 := bstep (se 1 (by rfl) ⟨2049956, by rfl⟩ : syracuseStep 2733275 = 4099913) B4099913
theorem B4101353 : Blo 1821612 4101353 := bstep (se 2 (by rfl) ⟨1538007, by rfl⟩ : syracuseStep 4101353 = 3076015) B3076015
theorem B28054775 : Blo 1821612 28054775 := bstep (se 1 (by rfl) ⟨21041081, by rfl⟩ : syracuseStep 28054775 = 42082163) B42082163
theorem B4101407 : Blo 1821612 4101407 := bstep (se 1 (by rfl) ⟨3076055, by rfl⟩ : syracuseStep 4101407 = 6152111) B6152111
theorem B2733449 : Blo 1821612 2733449 := bstep (se 2 (by rfl) ⟨1025043, by rfl⟩ : syracuseStep 2733449 = 2050087) B2050087
theorem B15562145 : Blo 1821612 15562145 := bstep (se 2 (by rfl) ⟨5835804, by rfl⟩ : syracuseStep 15562145 = 11671609) B11671609
theorem B5191073 : Blo 1821612 5191073 := bstep (se 2 (by rfl) ⟨1946652, by rfl⟩ : syracuseStep 5191073 = 3893305) B3893305
theorem B2463143 : Blo 1821612 2463143 := bstep (se 1 (by rfl) ⟨1847357, by rfl⟩ : syracuseStep 2463143 = 3694715) B3694715
theorem B6149789 : Blo 1821612 6149789 := bstep (se 3 (by rfl) ⟨1153085, by rfl⟩ : syracuseStep 6149789 = 2306171) B2306171
theorem B2733803 : Blo 1821612 2733803 := bstep (se 1 (by rfl) ⟨2050352, by rfl⟩ : syracuseStep 2733803 = 4100705) B4100705
theorem B4929259 : Blo 1821612 4929259 := bstep (se 1 (by rfl) ⟨3696944, by rfl⟩ : syracuseStep 4929259 = 7393889) B7393889
theorem B4101929 : Blo 1821612 4101929 := bstep (se 2 (by rfl) ⟨1538223, by rfl⟩ : syracuseStep 4101929 = 3076447) B3076447
theorem B2734031 : Blo 1821612 2734031 := bstep (se 1 (by rfl) ⟨2050523, by rfl⟩ : syracuseStep 2734031 = 4101047) B4101047
theorem B2594921 : Blo 1821612 2594921 := bstep (se 2 (by rfl) ⟨973095, by rfl⟩ : syracuseStep 2594921 = 1946191) B1946191
theorem B5838983 : Blo 1821612 5838983 := bstep (se 1 (by rfl) ⟨4379237, by rfl⟩ : syracuseStep 5838983 = 8758475) B8758475
theorem B20764835 : Blo 1821612 20764835 := bstep (se 1 (by rfl) ⟨15573626, by rfl⟩ : syracuseStep 20764835 = 31147253) B31147253
theorem B6150329 : Blo 1821612 6150329 := bstep (se 2 (by rfl) ⟨2306373, by rfl⟩ : syracuseStep 6150329 = 4612747) B4612747
theorem B7788797 : Blo 1821612 7788797 := bstep (se 3 (by rfl) ⟨1460399, by rfl⟩ : syracuseStep 7788797 = 2920799) B2920799
theorem B10377497 : Blo 1821612 10377497 := bstep (se 2 (by rfl) ⟨3891561, by rfl⟩ : syracuseStep 10377497 = 7783123) B7783123
theorem B2734427 : Blo 1821612 2734427 := bstep (se 1 (by rfl) ⟨2050820, by rfl⟩ : syracuseStep 2734427 = 4101641) B4101641
theorem B2464111 : Blo 1821612 2464111 := bstep (se 1 (by rfl) ⟨1848083, by rfl⟩ : syracuseStep 2464111 = 3696167) B3696167
theorem B9230759 : Blo 1821612 9230759 := bstep (se 1 (by rfl) ⟨6923069, by rfl⟩ : syracuseStep 9230759 = 13846139) B13846139
theorem B4381103 : Blo 1821612 4381103 := bstep (se 1 (by rfl) ⟨3285827, by rfl⟩ : syracuseStep 4381103 = 6571655) B6571655
theorem B29964725 : Blo 1821612 29964725 := bstep (se 5 (by rfl) ⟨1404596, by rfl⟩ : syracuseStep 29964725 = 2809193) B2809193
theorem B2734655 : Blo 1821612 2734655 := bstep (se 1 (by rfl) ⟨2050991, by rfl⟩ : syracuseStep 2734655 = 4101983) B4101983
theorem B9230921 : Blo 1821612 9230921 := bstep (se 2 (by rfl) ⟨3461595, by rfl⟩ : syracuseStep 9230921 = 6923191) B6923191
theorem B2734775 : Blo 1821612 2734775 := bstep (se 1 (by rfl) ⟨2051081, by rfl⟩ : syracuseStep 2734775 = 4102163) B4102163
theorem B33774337 : Blo 1821612 33774337 := bstep (se 2 (by rfl) ⟨12665376, by rfl⟩ : syracuseStep 33774337 = 25330753) B25330753
theorem B35519309 : Blo 1821612 35519309 := bstep (se 3 (by rfl) ⟨6659870, by rfl⟩ : syracuseStep 35519309 = 13319741) B13319741
theorem B4102991 : Blo 1821612 4102991 := bstep (se 1 (by rfl) ⟨3077243, by rfl⟩ : syracuseStep 4102991 = 6154487) B6154487
theorem B11680631 : Blo 1821612 11680631 := bstep (se 1 (by rfl) ⟨8760473, by rfl⟩ : syracuseStep 11680631 = 17520947) B17520947
theorem B2735003 : Blo 1821612 2735003 := bstep (se 1 (by rfl) ⟨2051252, by rfl⟩ : syracuseStep 2735003 = 4102505) B4102505
theorem B11680685 : Blo 1821612 11680685 := bstep (se 3 (by rfl) ⟨2190128, by rfl⟩ : syracuseStep 11680685 = 4380257) B4380257
theorem B9223307 : Blo 1821612 9223307 := bstep (se 1 (by rfl) ⟨6917480, by rfl⟩ : syracuseStep 9223307 = 13834961) B13834961
theorem B3284111 : Blo 1821612 3284111 := bstep (se 1 (by rfl) ⟨2463083, by rfl⟩ : syracuseStep 3284111 = 4926167) B4926167
theorem B2735399 : Blo 1821612 2735399 := bstep (se 1 (by rfl) ⟨2051549, by rfl⟩ : syracuseStep 2735399 = 4103099) B4103099
theorem B3505531 : Blo 1821612 3505531 := bstep (se 1 (by rfl) ⟨2629148, by rfl⟩ : syracuseStep 3505531 = 5258297) B5258297
theorem B4611451 : Blo 1821612 4611451 := bstep (se 1 (by rfl) ⟨3458588, by rfl⟩ : syracuseStep 4611451 = 6917177) B6917177
theorem B6151841 : Blo 1821612 6151841 := bstep (se 2 (by rfl) ⟨2306940, by rfl⟩ : syracuseStep 6151841 = 4613881) B4613881
theorem B13139617 : Blo 1821612 13139617 := bstep (se 2 (by rfl) ⟨4927356, by rfl⟩ : syracuseStep 13139617 = 9854713) B9854713
theorem B2629355 : Blo 1821612 2629355 := bstep (se 1 (by rfl) ⟨1972016, by rfl⟩ : syracuseStep 2629355 = 3944033) B3944033
theorem B4611887 : Blo 1821612 4611887 := bstep (se 1 (by rfl) ⟨3458915, by rfl⟩ : syracuseStep 4611887 = 6917831) B6917831
theorem B35020673 : Blo 1821612 35020673 := bstep (se 2 (by rfl) ⟨13132752, by rfl⟩ : syracuseStep 35020673 = 26265505) B26265505
theorem B10379137 : Blo 1821612 10379137 := bstep (se 2 (by rfl) ⟨3892176, by rfl⟩ : syracuseStep 10379137 = 7784353) B7784353
theorem B20750255 : Blo 1821612 20750255 := bstep (se 1 (by rfl) ⟨15562691, by rfl⟩ : syracuseStep 20750255 = 31125383) B31125383
theorem B11239343 : Blo 1821612 11239343 := bstep (se 1 (by rfl) ⟨8429507, by rfl⟩ : syracuseStep 11239343 = 16859015) B16859015
theorem B79912979 : Blo 1821612 79912979 := bstep (se 1 (by rfl) ⟨59934734, by rfl⟩ : syracuseStep 79912979 = 119869469) B119869469
theorem B11673659 : Blo 1821612 11673659 := bstep (se 1 (by rfl) ⟨8755244, by rfl⟩ : syracuseStep 11673659 = 17510489) B17510489
theorem B6152327 : Blo 1821612 6152327 := bstep (se 1 (by rfl) ⟨4614245, by rfl⟩ : syracuseStep 6152327 = 9228491) B9228491
theorem B46727441 : Blo 1821612 46727441 := bstep (se 2 (by rfl) ⟨17522790, by rfl⟩ : syracuseStep 46727441 = 35045581) B35045581
theorem B28057907 : Blo 1821612 28057907 := bstep (se 1 (by rfl) ⟨21043430, by rfl⟩ : syracuseStep 28057907 = 42086861) B42086861
theorem B13132151 : Blo 1821612 13132151 := bstep (se 1 (by rfl) ⟨9849113, by rfl⟩ : syracuseStep 13132151 = 19698227) B19698227
theorem B8757629 : Blo 1821612 8757629 := bstep (se 3 (by rfl) ⟨1642055, by rfl⟩ : syracuseStep 8757629 = 3284111) B3284111
theorem B4612585 : Blo 1821612 4612585 := bstep (se 2 (by rfl) ⟨1729719, by rfl⟩ : syracuseStep 4612585 = 3459439) B3459439
theorem B18703183 : Blo 1821612 18703183 := bstep (se 1 (by rfl) ⟨14027387, by rfl⟩ : syracuseStep 18703183 = 28054775) B28054775
theorem B15565769 : Blo 1821612 15565769 := bstep (se 2 (by rfl) ⟨5837163, by rfl⟩ : syracuseStep 15565769 = 11674327) B11674327
theorem B45032449 : Blo 1821612 45032449 := bstep (se 2 (by rfl) ⟨16887168, by rfl⟩ : syracuseStep 45032449 = 33774337) B33774337
theorem B3892553 : Blo 1821612 3892553 := bstep (se 2 (by rfl) ⟨1459707, by rfl⟩ : syracuseStep 3892553 = 2919415) B2919415
theorem B3892655 : Blo 1821612 3892655 := bstep (se 1 (by rfl) ⟨2919491, by rfl⟩ : syracuseStep 3892655 = 5838983) B5838983
theorem B6153839 : Blo 1821612 6153839 := bstep (se 1 (by rfl) ⟨4615379, by rfl⟩ : syracuseStep 6153839 = 9230759) B9230759
theorem B6317689 : Blo 1821612 6317689 := bstep (se 2 (by rfl) ⟨2369133, by rfl⟩ : syracuseStep 6317689 = 4738267) B4738267
theorem B6153947 : Blo 1821612 6153947 := bstep (se 1 (by rfl) ⟨4615460, by rfl⟩ : syracuseStep 6153947 = 9230921) B9230921
theorem B6571739 : Blo 1821612 6571739 := bstep (se 1 (by rfl) ⟨4928804, by rfl⟩ : syracuseStep 6571739 = 9857609) B9857609
theorem B13141925 : Blo 1821612 13141925 := bstep (se 4 (by rfl) ⟨1232055, by rfl⟩ : syracuseStep 13141925 = 2464111) B2464111
theorem B6572345 : Blo 1821612 6572345 := bstep (se 2 (by rfl) ⟨2464629, by rfl⟩ : syracuseStep 6572345 = 4929259) B4929259
theorem B23685605 : Blo 1821612 23685605 := bstep (se 4 (by rfl) ⟨2220525, by rfl⟩ : syracuseStep 23685605 = 4441051) B4441051
theorem B13838849 : Blo 1821612 13838849 := bstep (se 2 (by rfl) ⟨5189568, by rfl⟩ : syracuseStep 13838849 = 10379137) B10379137
theorem B5540359 : Blo 1821612 5540359 := bstep (se 1 (by rfl) ⟨4155269, by rfl⟩ : syracuseStep 5540359 = 8310539) B8310539
theorem B3074591 : Blo 1821612 3074591 := bstep (se 1 (by rfl) ⟨2305943, by rfl⟩ : syracuseStep 3074591 = 4611887) B4611887
theorem B2050591 : Blo 1821612 2050591 := bstep (se 1 (by rfl) ⟨1537943, by rfl⟩ : syracuseStep 2050591 = 3075887) B3075887
theorem B3074665 : Blo 1821612 3074665 := bstep (se 2 (by rfl) ⟨1152999, by rfl⟩ : syracuseStep 3074665 = 2305999) B2305999
theorem B5188283 : Blo 1821612 5188283 := bstep (se 1 (by rfl) ⟨3891212, by rfl⟩ : syracuseStep 5188283 = 7782425) B7782425
theorem B3075023 : Blo 1821612 3075023 := bstep (se 1 (by rfl) ⟨2306267, by rfl⟩ : syracuseStep 3075023 = 4612535) B4612535
theorem B11676635 : Blo 1821612 11676635 := bstep (se 1 (by rfl) ⟨8757476, by rfl⟩ : syracuseStep 11676635 = 17514953) B17514953
theorem B1821743 : Blo 1821612 1821743 := bstep (se 1 (by rfl) ⟨1366307, by rfl⟩ : syracuseStep 1821743 = 2732615) B2732615
theorem B11086895 : Blo 1821612 11086895 := bstep (se 1 (by rfl) ⟨8315171, by rfl⟩ : syracuseStep 11086895 = 16630343) B16630343
theorem B1821767 : Blo 1821612 1821767 := bstep (se 1 (by rfl) ⟨1366325, by rfl⟩ : syracuseStep 1821767 = 2732651) B2732651
theorem B2190407 : Blo 1821612 2190407 := bstep (se 1 (by rfl) ⟨1642805, by rfl⟩ : syracuseStep 2190407 = 3285611) B3285611
theorem B4099193 : Blo 1821612 4099193 := bstep (se 2 (by rfl) ⟨1537197, by rfl⟩ : syracuseStep 4099193 = 3074395) B3074395
theorem B4615289 : Blo 1821612 4615289 := bstep (se 2 (by rfl) ⟨1730733, by rfl⟩ : syracuseStep 4615289 = 3461467) B3461467
theorem B1821919 : Blo 1821612 1821919 := bstep (se 1 (by rfl) ⟨1366439, by rfl⟩ : syracuseStep 1821919 = 2732879) B2732879
theorem B1822183 : Blo 1821612 1822183 := bstep (se 1 (by rfl) ⟨1366637, by rfl⟩ : syracuseStep 1822183 = 2733275) B2733275
theorem B37940771 : Blo 1821612 37940771 := bstep (se 1 (by rfl) ⟨28455578, by rfl⟩ : syracuseStep 37940771 = 56911157) B56911157
theorem B1822299 : Blo 1821612 1822299 := bstep (se 1 (by rfl) ⟨1366724, by rfl⟩ : syracuseStep 1822299 = 2733449) B2733449
theorem B10374763 : Blo 1821612 10374763 := bstep (se 1 (by rfl) ⟨7781072, by rfl⟩ : syracuseStep 10374763 = 15562145) B15562145
theorem B3075691 : Blo 1821612 3075691 := bstep (se 1 (by rfl) ⟨2306768, by rfl⟩ : syracuseStep 3075691 = 4613537) B4613537
theorem B3460715 : Blo 1821612 3460715 := bstep (se 1 (by rfl) ⟨2595536, by rfl⟩ : syracuseStep 3460715 = 5191073) B5191073
theorem B4099859 : Blo 1821612 4099859 := bstep (se 1 (by rfl) ⟨3074894, by rfl⟩ : syracuseStep 4099859 = 6149789) B6149789
theorem B1822535 : Blo 1821612 1822535 := bstep (se 1 (by rfl) ⟨1366901, by rfl⟩ : syracuseStep 1822535 = 2733803) B2733803
theorem B11079497 : Blo 1821612 11079497 := bstep (se 2 (by rfl) ⟨4154811, by rfl⟩ : syracuseStep 11079497 = 8309623) B8309623
theorem B20770667 : Blo 1821612 20770667 := bstep (se 1 (by rfl) ⟨15578000, by rfl⟩ : syracuseStep 20770667 = 31156001) B31156001
theorem B3075961 : Blo 1821612 3075961 := bstep (se 2 (by rfl) ⟨1153485, by rfl⟩ : syracuseStep 3075961 = 2306971) B2306971
theorem B3075995 : Blo 1821612 3075995 := bstep (se 1 (by rfl) ⟨2306996, by rfl⟩ : syracuseStep 3075995 = 4613993) B4613993
theorem B8761243 : Blo 1821612 8761243 := bstep (se 1 (by rfl) ⟨6570932, by rfl⟩ : syracuseStep 8761243 = 13141865) B13141865
theorem B1822687 : Blo 1821612 1822687 := bstep (se 1 (by rfl) ⟨1367015, by rfl⟩ : syracuseStep 1822687 = 2734031) B2734031
theorem B4100219 : Blo 1821612 4100219 := bstep (se 1 (by rfl) ⟨3075164, by rfl⟩ : syracuseStep 4100219 = 6150329) B6150329
theorem B5836985 : Blo 1821612 5836985 := bstep (se 2 (by rfl) ⟨2188869, by rfl⟩ : syracuseStep 5836985 = 4377739) B4377739
theorem B6918331 : Blo 1821612 6918331 := bstep (se 1 (by rfl) ⟨5188748, by rfl⟩ : syracuseStep 6918331 = 10377497) B10377497
theorem B1822951 : Blo 1821612 1822951 := bstep (se 1 (by rfl) ⟨1367213, by rfl⟩ : syracuseStep 1822951 = 2734427) B2734427
theorem B19976483 : Blo 1821612 19976483 := bstep (se 1 (by rfl) ⟨14982362, by rfl⟩ : syracuseStep 19976483 = 29964725) B29964725
theorem B2920735 : Blo 1821612 2920735 := bstep (se 1 (by rfl) ⟨2190551, by rfl⟩ : syracuseStep 2920735 = 4381103) B4381103
theorem B1823103 : Blo 1821612 1823103 := bstep (se 1 (by rfl) ⟨1367327, by rfl⟩ : syracuseStep 1823103 = 2734655) B2734655
theorem B4100489 : Blo 1821612 4100489 := bstep (se 2 (by rfl) ⟨1537683, by rfl⟩ : syracuseStep 4100489 = 3075367) B3075367
theorem B2732495 : Blo 1821612 2732495 := bstep (se 1 (by rfl) ⟨2049371, by rfl⟩ : syracuseStep 2732495 = 4098743) B4098743
theorem B1946063 : Blo 1821612 1946063 := bstep (se 1 (by rfl) ⟨1459547, by rfl⟩ : syracuseStep 1946063 = 2919095) B2919095
theorem B1823183 : Blo 1821612 1823183 := bstep (se 1 (by rfl) ⟨1367387, by rfl⟩ : syracuseStep 1823183 = 2734775) B2734775
theorem B2732537 : Blo 1821612 2732537 := bstep (se 2 (by rfl) ⟨1024701, by rfl⟩ : syracuseStep 2732537 = 2049403) B2049403
theorem B4674041 : Blo 1821612 4674041 := bstep (se 2 (by rfl) ⟨1752765, by rfl⟩ : syracuseStep 4674041 = 3505531) B3505531
theorem B6148601 : Blo 1821612 6148601 := bstep (se 2 (by rfl) ⟨2305725, by rfl⟩ : syracuseStep 6148601 = 4611451) B4611451
theorem B23679539 : Blo 1821612 23679539 := bstep (se 1 (by rfl) ⟨17759654, by rfl⟩ : syracuseStep 23679539 = 35519309) B35519309
theorem B7787087 : Blo 1821612 7787087 := bstep (se 1 (by rfl) ⟨5840315, by rfl⟩ : syracuseStep 7787087 = 11680631) B11680631
theorem B2732639 : Blo 1821612 2732639 := bstep (se 1 (by rfl) ⟨2049479, by rfl⟩ : syracuseStep 2732639 = 4098959) B4098959
theorem B1823335 : Blo 1821612 1823335 := bstep (se 1 (by rfl) ⟨1367501, by rfl⟩ : syracuseStep 1823335 = 2735003) B2735003
theorem B7787123 : Blo 1821612 7787123 := bstep (se 1 (by rfl) ⟨5840342, by rfl⟩ : syracuseStep 7787123 = 11680685) B11680685
theorem B6918817 : Blo 1821612 6918817 := bstep (se 2 (by rfl) ⟨2594556, by rfl⟩ : syracuseStep 6918817 = 5189113) B5189113
theorem B6148871 : Blo 1821612 6148871 := bstep (se 1 (by rfl) ⟨4611653, by rfl⟩ : syracuseStep 6148871 = 9223307) B9223307
theorem B6148925 : Blo 1821612 6148925 := bstep (se 3 (by rfl) ⟨1152923, by rfl⟩ : syracuseStep 6148925 = 2305847) B2305847
theorem B1823599 : Blo 1821612 1823599 := bstep (se 1 (by rfl) ⟨1367699, by rfl⟩ : syracuseStep 1823599 = 2735399) B2735399
theorem B17519489 : Blo 1821612 17519489 := bstep (se 2 (by rfl) ⟨6569808, by rfl⟩ : syracuseStep 17519489 = 13139617) B13139617
theorem B5190571 : Blo 1821612 5190571 := bstep (se 1 (by rfl) ⟨3892928, by rfl⟩ : syracuseStep 5190571 = 7785857) B7785857
theorem B2733119 : Blo 1821612 2733119 := bstep (se 1 (by rfl) ⟨2049839, by rfl⟩ : syracuseStep 2733119 = 4099679) B4099679
theorem B3077183 : Blo 1821612 3077183 := bstep (se 1 (by rfl) ⟨2307887, by rfl⟩ : syracuseStep 3077183 = 4615775) B4615775
theorem B2733161 : Blo 1821612 2733161 := bstep (se 2 (by rfl) ⟨1024935, by rfl⟩ : syracuseStep 2733161 = 2049871) B2049871
theorem B4101227 : Blo 1821612 4101227 := bstep (se 1 (by rfl) ⟨3075920, by rfl⟩ : syracuseStep 4101227 = 6151841) B6151841
theorem B2733263 : Blo 1821612 2733263 := bstep (se 1 (by rfl) ⟨2049947, by rfl⟩ : syracuseStep 2733263 = 4099895) B4099895
theorem B13833503 : Blo 1821612 13833503 := bstep (se 1 (by rfl) ⟨10375127, by rfl⟩ : syracuseStep 13833503 = 20750255) B20750255
theorem B7492895 : Blo 1821612 7492895 := bstep (se 1 (by rfl) ⟨5619671, by rfl⟩ : syracuseStep 7492895 = 11239343) B11239343
theorem B2733467 : Blo 1821612 2733467 := bstep (se 1 (by rfl) ⟨2050100, by rfl⟩ : syracuseStep 2733467 = 4100201) B4100201
theorem B11081249 : Blo 1821612 11081249 := bstep (se 2 (by rfl) ⟨4155468, by rfl⟩ : syracuseStep 11081249 = 8310937) B8310937
theorem B5543495 : Blo 1821612 5543495 := bstep (se 1 (by rfl) ⟨4157621, by rfl⟩ : syracuseStep 5543495 = 8315243) B8315243
theorem B6919789 : Blo 1821612 6919789 := bstep (se 3 (by rfl) ⟨1297460, by rfl⟩ : syracuseStep 6919789 = 2594921) B2594921
theorem B2733689 : Blo 1821612 2733689 := bstep (se 2 (by rfl) ⟨1025133, by rfl⟩ : syracuseStep 2733689 = 2050267) B2050267
theorem B17520299 : Blo 1821612 17520299 := bstep (se 1 (by rfl) ⟨13140224, by rfl⟩ : syracuseStep 17520299 = 26280449) B26280449
theorem B4101803 : Blo 1821612 4101803 := bstep (se 1 (by rfl) ⟨3076352, by rfl⟩ : syracuseStep 4101803 = 6152705) B6152705
theorem B2733791 : Blo 1821612 2733791 := bstep (se 1 (by rfl) ⟨2050343, by rfl⟩ : syracuseStep 2733791 = 4100687) B4100687
theorem B6149951 : Blo 1821612 6149951 := bstep (se 1 (by rfl) ⟨4612463, by rfl⟩ : syracuseStep 6149951 = 9224927) B9224927
theorem B2733887 : Blo 1821612 2733887 := bstep (se 1 (by rfl) ⟨2050415, by rfl⟩ : syracuseStep 2733887 = 4100831) B4100831
theorem B33265637 : Blo 1821612 33265637 := bstep (se 4 (by rfl) ⟨3118653, by rfl⟩ : syracuseStep 33265637 = 6237307) B6237307
theorem B2734055 : Blo 1821612 2734055 := bstep (se 1 (by rfl) ⟨2050541, by rfl⟩ : syracuseStep 2734055 = 4101083) B4101083
theorem B4102127 : Blo 1821612 4102127 := bstep (se 1 (by rfl) ⟨3076595, by rfl⟩ : syracuseStep 4102127 = 6153191) B6153191
theorem B2734073 : Blo 1821612 2734073 := bstep (se 2 (by rfl) ⟨1025277, by rfl⟩ : syracuseStep 2734073 = 2050555) B2050555
theorem B2734175 : Blo 1821612 2734175 := bstep (se 1 (by rfl) ⟨2050631, by rfl⟩ : syracuseStep 2734175 = 4101263) B4101263
theorem B4380767 : Blo 1821612 4380767 := bstep (se 1 (by rfl) ⟨3285575, by rfl⟩ : syracuseStep 4380767 = 6571151) B6571151
theorem B2734235 : Blo 1821612 2734235 := bstep (se 1 (by rfl) ⟨2050676, by rfl⟩ : syracuseStep 2734235 = 4101353) B4101353
theorem B1972415 : Blo 1821612 1972415 := bstep (se 1 (by rfl) ⟨1479311, by rfl⟩ : syracuseStep 1972415 = 2958623) B2958623
theorem B2595007 : Blo 1821612 2595007 := bstep (se 1 (by rfl) ⟨1946255, by rfl⟩ : syracuseStep 2595007 = 3892511) B3892511
theorem B2734271 : Blo 1821612 2734271 := bstep (se 1 (by rfl) ⟨2050703, by rfl⟩ : syracuseStep 2734271 = 4101407) B4101407
theorem B4102343 : Blo 1821612 4102343 := bstep (se 1 (by rfl) ⟨3076757, by rfl⟩ : syracuseStep 4102343 = 6153515) B6153515
theorem B2734313 : Blo 1821612 2734313 := bstep (se 2 (by rfl) ⟨1025367, by rfl⟩ : syracuseStep 2734313 = 2050735) B2050735
theorem B11082025 : Blo 1821612 11082025 := bstep (se 2 (by rfl) ⟨4155759, by rfl⟩ : syracuseStep 11082025 = 8311519) B8311519
theorem B6232427 : Blo 1821612 6232427 := bstep (se 1 (by rfl) ⟨4674320, by rfl⟩ : syracuseStep 6232427 = 9348641) B9348641
theorem B4102523 : Blo 1821612 4102523 := bstep (se 1 (by rfl) ⟨3076892, by rfl⟩ : syracuseStep 4102523 = 6153785) B6153785
theorem B6568381 : Blo 1821612 6568381 := bstep (se 3 (by rfl) ⟨1231571, by rfl⟩ : syracuseStep 6568381 = 2463143) B2463143
theorem B23353879 : Blo 1821612 23353879 := bstep (se 1 (by rfl) ⟨17515409, by rfl⟩ : syracuseStep 23353879 = 35030819) B35030819
theorem B2734619 : Blo 1821612 2734619 := bstep (se 1 (by rfl) ⟨2050964, by rfl⟩ : syracuseStep 2734619 = 4101929) B4101929
theorem B19716695 : Blo 1821612 19716695 := bstep (se 1 (by rfl) ⟨14787521, by rfl⟩ : syracuseStep 19716695 = 29575043) B29575043
theorem B2734697 : Blo 1821612 2734697 := bstep (se 2 (by rfl) ⟨1025511, by rfl⟩ : syracuseStep 2734697 = 2051023) B2051023
theorem B11672201 : Blo 1821612 11672201 := bstep (se 2 (by rfl) ⟨4377075, by rfl⟩ : syracuseStep 11672201 = 8754151) B8754151
theorem B4102793 : Blo 1821612 4102793 := bstep (se 2 (by rfl) ⟨1538547, by rfl⟩ : syracuseStep 4102793 = 3077095) B3077095
theorem B13843223 : Blo 1821612 13843223 := bstep (se 1 (by rfl) ⟨10382417, by rfl⟩ : syracuseStep 13843223 = 20764835) B20764835
theorem B5192531 : Blo 1821612 5192531 := bstep (se 1 (by rfl) ⟨3894398, by rfl⟩ : syracuseStep 5192531 = 7788797) B7788797
theorem B6921065 : Blo 1821612 6921065 := bstep (se 2 (by rfl) ⟨2595399, by rfl⟩ : syracuseStep 6921065 = 5190799) B5190799
theorem B20757545 : Blo 1821612 20757545 := bstep (se 2 (by rfl) ⟨7784079, by rfl⟩ : syracuseStep 20757545 = 15568159) B15568159
theorem B2735225 : Blo 1821612 2735225 := bstep (se 2 (by rfl) ⟨1025709, by rfl⟩ : syracuseStep 2735225 = 2051419) B2051419
theorem B29572249 : Blo 1821612 29572249 := bstep (se 2 (by rfl) ⟨11089593, by rfl⟩ : syracuseStep 29572249 = 22179187) B22179187
theorem B2735327 : Blo 1821612 2735327 := bstep (se 1 (by rfl) ⟨2051495, by rfl⟩ : syracuseStep 2735327 = 4102991) B4102991
theorem B2735369 : Blo 1821612 2735369 := bstep (se 2 (by rfl) ⟨1025763, by rfl⟩ : syracuseStep 2735369 = 2051527) B2051527
theorem B7011613 : Blo 1821612 7011613 := bstep (se 3 (by rfl) ⟨1314677, by rfl⟩ : syracuseStep 7011613 = 2629355) B2629355
theorem B6151463 : Blo 1821612 6151463 := bstep (se 1 (by rfl) ⟨4613597, by rfl⟩ : syracuseStep 6151463 = 9227195) B9227195
theorem B17309483 : Blo 1821612 17309483 := bstep (se 1 (by rfl) ⟨12982112, by rfl⟩ : syracuseStep 17309483 = 25964225) B25964225
theorem B23347115 : Blo 1821612 23347115 := bstep (se 1 (by rfl) ⟨17510336, by rfl⟩ : syracuseStep 23347115 = 35020673) B35020673
theorem B3891323 : Blo 1821612 3891323 := bstep (se 1 (by rfl) ⟨2918492, by rfl⟩ : syracuseStep 3891323 = 5836985) B5836985
theorem B31129757 : Blo 1821612 31129757 := bstep (se 3 (by rfl) ⟨5836829, by rfl⟩ : syracuseStep 31129757 = 11673659) B11673659
theorem B5841085 : Blo 1821612 5841085 := bstep (se 3 (by rfl) ⟨1095203, by rfl⟩ : syracuseStep 5841085 = 2190407) B2190407
theorem B9224441 : Blo 1821612 9224441 := bstep (se 2 (by rfl) ⟨3459165, by rfl⟩ : syracuseStep 9224441 = 6918331) B6918331
theorem B15786359 : Blo 1821612 15786359 := bstep (se 1 (by rfl) ⟨11839769, by rfl⟩ : syracuseStep 15786359 = 23679539) B23679539
theorem B5259773 : Blo 1821612 5259773 := bstep (se 3 (by rfl) ⟨986207, by rfl⟩ : syracuseStep 5259773 = 1972415) B1972415
theorem B31138505 : Blo 1821612 31138505 := bstep (se 2 (by rfl) ⟨11676939, by rfl⟩ : syracuseStep 31138505 = 23353879) B23353879
theorem B9225089 : Blo 1821612 9225089 := bstep (se 2 (by rfl) ⟨3459408, by rfl⟩ : syracuseStep 9225089 = 6918817) B6918817
theorem B3695663 : Blo 1821612 3695663 := bstep (se 1 (by rfl) ⟨2771747, by rfl⟩ : syracuseStep 3695663 = 5543495) B5543495
theorem B24937577 : Blo 1821612 24937577 := bstep (se 2 (by rfl) ⟨9351591, by rfl⟩ : syracuseStep 24937577 = 18703183) B18703183
theorem B10380413 : Blo 1821612 10380413 := bstep (se 3 (by rfl) ⟨1946327, by rfl⟩ : syracuseStep 10380413 = 3892655) B3892655
theorem B22177091 : Blo 1821612 22177091 := bstep (se 1 (by rfl) ⟨16632818, by rfl⟩ : syracuseStep 22177091 = 33265637) B33265637
theorem B39429665 : Blo 1821612 39429665 := bstep (se 2 (by rfl) ⟨14786124, by rfl⟩ : syracuseStep 39429665 = 29572249) B29572249
theorem B4154951 : Blo 1821612 4154951 := bstep (se 1 (by rfl) ⟨3116213, by rfl⟩ : syracuseStep 4154951 = 6232427) B6232427
theorem B9225899 : Blo 1821612 9225899 := bstep (se 1 (by rfl) ⟨6919424, by rfl⟩ : syracuseStep 9225899 = 13838849) B13838849
theorem B2049727 : Blo 1821612 2049727 := bstep (se 1 (by rfl) ⟨1537295, by rfl⟩ : syracuseStep 2049727 = 3074591) B3074591
theorem B3458855 : Blo 1821612 3458855 := bstep (se 1 (by rfl) ⟨2594141, by rfl⟩ : syracuseStep 3458855 = 5188283) B5188283
theorem B4614043 : Blo 1821612 4614043 := bstep (se 1 (by rfl) ⟨3460532, by rfl⟩ : syracuseStep 4614043 = 6921065) B6921065
theorem B17524637 : Blo 1821612 17524637 := bstep (se 3 (by rfl) ⟨3285869, by rfl⟩ : syracuseStep 17524637 = 6571739) B6571739
theorem B2050015 : Blo 1821612 2050015 := bstep (se 1 (by rfl) ⟨1537511, by rfl⟩ : syracuseStep 2050015 = 3075023) B3075023
theorem B7784423 : Blo 1821612 7784423 := bstep (se 1 (by rfl) ⟨5838317, by rfl⟩ : syracuseStep 7784423 = 11676635) B11676635
theorem B13838363 : Blo 1821612 13838363 := bstep (se 1 (by rfl) ⟨10378772, by rfl⟩ : syracuseStep 13838363 = 20757545) B20757545
theorem B7391263 : Blo 1821612 7391263 := bstep (se 1 (by rfl) ⟨5543447, by rfl⟩ : syracuseStep 7391263 = 11086895) B11086895
theorem B9226385 : Blo 1821612 9226385 := bstep (se 2 (by rfl) ⟨3459894, by rfl⟩ : syracuseStep 9226385 = 6919789) B6919789
theorem B8423585 : Blo 1821612 8423585 := bstep (se 2 (by rfl) ⟨3158844, by rfl⟩ : syracuseStep 8423585 = 6317689) B6317689
theorem B35031365 : Blo 1821612 35031365 := bstep (se 4 (by rfl) ⟨3284190, by rfl⟩ : syracuseStep 35031365 = 6568381) B6568381
theorem B13847111 : Blo 1821612 13847111 := bstep (se 1 (by rfl) ⟨10385333, by rfl⟩ : syracuseStep 13847111 = 20770667) B20770667
theorem B2050663 : Blo 1821612 2050663 := bstep (se 1 (by rfl) ⟨1537997, by rfl⟩ : syracuseStep 2050663 = 3075995) B3075995
theorem B53275319 : Blo 1821612 53275319 := bstep (se 1 (by rfl) ⟨39956489, by rfl⟩ : syracuseStep 53275319 = 79912979) B79912979
theorem B18705271 : Blo 1821612 18705271 := bstep (se 1 (by rfl) ⟨14028953, by rfl⟩ : syracuseStep 18705271 = 28057907) B28057907
theorem B3460009 : Blo 1821612 3460009 := bstep (se 2 (by rfl) ⟨1297503, by rfl⟩ : syracuseStep 3460009 = 2595007) B2595007
theorem B1821663 : Blo 1821612 1821663 := bstep (se 1 (by rfl) ⟨1366247, by rfl⟩ : syracuseStep 1821663 = 2732495) B2732495
theorem B1821691 : Blo 1821612 1821691 := bstep (se 1 (by rfl) ⟨1366268, by rfl⟩ : syracuseStep 1821691 = 2732537) B2732537
theorem B3116027 : Blo 1821612 3116027 := bstep (se 1 (by rfl) ⟨2337020, by rfl⟩ : syracuseStep 3116027 = 4674041) B4674041
theorem B4099067 : Blo 1821612 4099067 := bstep (se 1 (by rfl) ⟨3074300, by rfl⟩ : syracuseStep 4099067 = 6148601) B6148601
theorem B3894313 : Blo 1821612 3894313 := bstep (se 2 (by rfl) ⟨1460367, by rfl⟩ : syracuseStep 3894313 = 2920735) B2920735
theorem B1821759 : Blo 1821612 1821759 := bstep (se 1 (by rfl) ⟨1366319, by rfl⟩ : syracuseStep 1821759 = 2732639) B2732639
theorem B4099247 : Blo 1821612 4099247 := bstep (se 1 (by rfl) ⟨3074435, by rfl⟩ : syracuseStep 4099247 = 6148871) B6148871
theorem B4099283 : Blo 1821612 4099283 := bstep (se 1 (by rfl) ⟨3074462, by rfl⟩ : syracuseStep 4099283 = 6148925) B6148925
theorem B1822079 : Blo 1821612 1822079 := bstep (se 1 (by rfl) ⟨1366559, by rfl⟩ : syracuseStep 1822079 = 2733119) B2733119
theorem B2051455 : Blo 1821612 2051455 := bstep (se 1 (by rfl) ⟨1538591, by rfl⟩ : syracuseStep 2051455 = 3077183) B3077183
theorem B1822107 : Blo 1821612 1822107 := bstep (se 1 (by rfl) ⟨1366580, by rfl⟩ : syracuseStep 1822107 = 2733161) B2733161
theorem B1822175 : Blo 1821612 1822175 := bstep (se 1 (by rfl) ⟨1366631, by rfl⟩ : syracuseStep 1822175 = 2733263) B2733263
theorem B4099553 : Blo 1821612 4099553 := bstep (se 2 (by rfl) ⟨1537332, by rfl⟩ : syracuseStep 4099553 = 3074665) B3074665
theorem B17526253 : Blo 1821612 17526253 := bstep (se 3 (by rfl) ⟨3286172, by rfl⟩ : syracuseStep 17526253 = 6572345) B6572345
theorem B1822311 : Blo 1821612 1822311 := bstep (se 1 (by rfl) ⟨1366733, by rfl⟩ : syracuseStep 1822311 = 2733467) B2733467
theorem B1822459 : Blo 1821612 1822459 := bstep (se 1 (by rfl) ⟨1366844, by rfl⟩ : syracuseStep 1822459 = 2733689) B2733689
theorem B1822527 : Blo 1821612 1822527 := bstep (se 1 (by rfl) ⟨1366895, by rfl⟩ : syracuseStep 1822527 = 2733791) B2733791
theorem B5189501 : Blo 1821612 5189501 := bstep (se 3 (by rfl) ⟨973031, by rfl⟩ : syracuseStep 5189501 = 1946063) B1946063
theorem B4099967 : Blo 1821612 4099967 := bstep (se 1 (by rfl) ⟨3074975, by rfl⟩ : syracuseStep 4099967 = 6149951) B6149951
theorem B1822591 : Blo 1821612 1822591 := bstep (se 1 (by rfl) ⟨1366943, by rfl⟩ : syracuseStep 1822591 = 2733887) B2733887
theorem B8761283 : Blo 1821612 8761283 := bstep (se 1 (by rfl) ⟨6570962, by rfl⟩ : syracuseStep 8761283 = 13141925) B13141925
theorem B1822703 : Blo 1821612 1822703 := bstep (se 1 (by rfl) ⟨1367027, by rfl⟩ : syracuseStep 1822703 = 2734055) B2734055
theorem B1822715 : Blo 1821612 1822715 := bstep (se 1 (by rfl) ⟨1367036, by rfl⟩ : syracuseStep 1822715 = 2734073) B2734073
theorem B60043265 : Blo 1821612 60043265 := bstep (se 2 (by rfl) ⟨22516224, by rfl⟩ : syracuseStep 60043265 = 45032449) B45032449
theorem B1822783 : Blo 1821612 1822783 := bstep (se 1 (by rfl) ⟨1367087, by rfl⟩ : syracuseStep 1822783 = 2734175) B2734175
theorem B2920511 : Blo 1821612 2920511 := bstep (se 1 (by rfl) ⟨2190383, by rfl⟩ : syracuseStep 2920511 = 4380767) B4380767
theorem B101175389 : Blo 1821612 101175389 := bstep (se 3 (by rfl) ⟨18970385, by rfl⟩ : syracuseStep 101175389 = 37940771) B37940771
theorem B1822823 : Blo 1821612 1822823 := bstep (se 1 (by rfl) ⟨1367117, by rfl⟩ : syracuseStep 1822823 = 2734235) B2734235
theorem B1822847 : Blo 1821612 1822847 := bstep (se 1 (by rfl) ⟨1367135, by rfl⟩ : syracuseStep 1822847 = 2734271) B2734271
theorem B1822875 : Blo 1821612 1822875 := bstep (se 1 (by rfl) ⟨1367156, by rfl⟩ : syracuseStep 1822875 = 2734313) B2734313
theorem B15790403 : Blo 1821612 15790403 := bstep (se 1 (by rfl) ⟨11842802, by rfl⟩ : syracuseStep 15790403 = 23685605) B23685605
theorem B1823079 : Blo 1821612 1823079 := bstep (se 1 (by rfl) ⟨1367309, by rfl⟩ : syracuseStep 1823079 = 2734619) B2734619
theorem B13144463 : Blo 1821612 13144463 := bstep (se 1 (by rfl) ⟨9858347, by rfl⟩ : syracuseStep 13144463 = 19716695) B19716695
theorem B1823131 : Blo 1821612 1823131 := bstep (se 1 (by rfl) ⟨1367348, by rfl⟩ : syracuseStep 1823131 = 2734697) B2734697
theorem B9228815 : Blo 1821612 9228815 := bstep (se 1 (by rfl) ⟨6921611, by rfl⟩ : syracuseStep 9228815 = 13843223) B13843223
theorem B3461687 : Blo 1821612 3461687 := bstep (se 1 (by rfl) ⟨2596265, by rfl⟩ : syracuseStep 3461687 = 5192531) B5192531
theorem B2732795 : Blo 1821612 2732795 := bstep (se 1 (by rfl) ⟨2049596, by rfl⟩ : syracuseStep 2732795 = 4099193) B4099193
theorem B3076859 : Blo 1821612 3076859 := bstep (se 1 (by rfl) ⟨2307644, by rfl⟩ : syracuseStep 3076859 = 4615289) B4615289
theorem B1823483 : Blo 1821612 1823483 := bstep (se 1 (by rfl) ⟨1367612, by rfl⟩ : syracuseStep 1823483 = 2735225) B2735225
theorem B13833017 : Blo 1821612 13833017 := bstep (se 2 (by rfl) ⟨5187381, by rfl⟩ : syracuseStep 13833017 = 10374763) B10374763
theorem B4100921 : Blo 1821612 4100921 := bstep (se 2 (by rfl) ⟨1537845, by rfl⟩ : syracuseStep 4100921 = 3075691) B3075691
theorem B1823551 : Blo 1821612 1823551 := bstep (se 1 (by rfl) ⟨1367663, by rfl⟩ : syracuseStep 1823551 = 2735327) B2735327
theorem B1823579 : Blo 1821612 1823579 := bstep (se 1 (by rfl) ⟨1367684, by rfl⟩ : syracuseStep 1823579 = 2735369) B2735369
theorem B4100975 : Blo 1821612 4100975 := bstep (se 1 (by rfl) ⟨3075731, by rfl⟩ : syracuseStep 4100975 = 6151463) B6151463
theorem B2307143 : Blo 1821612 2307143 := bstep (se 1 (by rfl) ⟨1730357, by rfl⟩ : syracuseStep 2307143 = 3460715) B3460715
theorem B4101281 : Blo 1821612 4101281 := bstep (se 2 (by rfl) ⟨1537980, by rfl⟩ : syracuseStep 4101281 = 3075961) B3075961
theorem B2733239 : Blo 1821612 2733239 := bstep (se 1 (by rfl) ⟨2049929, by rfl⟩ : syracuseStep 2733239 = 4099859) B4099859
theorem B11539655 : Blo 1821612 11539655 := bstep (se 1 (by rfl) ⟨8654741, by rfl⟩ : syracuseStep 11539655 = 17309483) B17309483
theorem B7386331 : Blo 1821612 7386331 := bstep (se 1 (by rfl) ⟨5539748, by rfl⟩ : syracuseStep 7386331 = 11079497) B11079497
theorem B2733479 : Blo 1821612 2733479 := bstep (se 1 (by rfl) ⟨2050109, by rfl⟩ : syracuseStep 2733479 = 4100219) B4100219
theorem B4101551 : Blo 1821612 4101551 := bstep (se 1 (by rfl) ⟨3076163, by rfl⟩ : syracuseStep 4101551 = 6152327) B6152327
theorem B31151627 : Blo 1821612 31151627 := bstep (se 1 (by rfl) ⟨23363720, by rfl⟩ : syracuseStep 31151627 = 46727441) B46727441
theorem B13317655 : Blo 1821612 13317655 := bstep (se 1 (by rfl) ⟨9988241, by rfl⟩ : syracuseStep 13317655 = 19976483) B19976483
theorem B8754767 : Blo 1821612 8754767 := bstep (se 1 (by rfl) ⟨6566075, by rfl⟩ : syracuseStep 8754767 = 13132151) B13132151
theorem B5838419 : Blo 1821612 5838419 := bstep (se 1 (by rfl) ⟨4378814, by rfl⟩ : syracuseStep 5838419 = 8757629) B8757629
theorem B2733659 : Blo 1821612 2733659 := bstep (se 1 (by rfl) ⟨2050244, by rfl⟩ : syracuseStep 2733659 = 4100489) B4100489
theorem B5191391 : Blo 1821612 5191391 := bstep (se 1 (by rfl) ⟨3893543, by rfl⟩ : syracuseStep 5191391 = 7787087) B7787087
theorem B14776033 : Blo 1821612 14776033 := bstep (se 2 (by rfl) ⟨5541012, by rfl⟩ : syracuseStep 14776033 = 11082025) B11082025
theorem B5191415 : Blo 1821612 5191415 := bstep (se 1 (by rfl) ⟨3893561, by rfl⟩ : syracuseStep 5191415 = 7787123) B7787123
theorem B11679659 : Blo 1821612 11679659 := bstep (se 1 (by rfl) ⟨8759744, by rfl⟩ : syracuseStep 11679659 = 17519489) B17519489
theorem B10377179 : Blo 1821612 10377179 := bstep (se 1 (by rfl) ⟨7782884, by rfl⟩ : syracuseStep 10377179 = 15565769) B15565769
theorem B6150113 : Blo 1821612 6150113 := bstep (se 2 (by rfl) ⟨2306292, by rfl⟩ : syracuseStep 6150113 = 4612585) B4612585
theorem B7387145 : Blo 1821612 7387145 := bstep (se 2 (by rfl) ⟨2770179, by rfl⟩ : syracuseStep 7387145 = 5540359) B5540359
theorem B2734121 : Blo 1821612 2734121 := bstep (se 2 (by rfl) ⟨1025295, by rfl⟩ : syracuseStep 2734121 = 2050591) B2050591
theorem B2734151 : Blo 1821612 2734151 := bstep (se 1 (by rfl) ⟨2050613, by rfl⟩ : syracuseStep 2734151 = 4101227) B4101227
theorem B9222335 : Blo 1821612 9222335 := bstep (se 1 (by rfl) ⟨6916751, by rfl⟩ : syracuseStep 9222335 = 13833503) B13833503
theorem B4995263 : Blo 1821612 4995263 := bstep (se 1 (by rfl) ⟨3746447, by rfl⟩ : syracuseStep 4995263 = 7492895) B7492895
theorem B2595035 : Blo 1821612 2595035 := bstep (se 1 (by rfl) ⟨1946276, by rfl⟩ : syracuseStep 2595035 = 3892553) B3892553
theorem B7387499 : Blo 1821612 7387499 := bstep (se 1 (by rfl) ⟨5540624, by rfl⟩ : syracuseStep 7387499 = 11081249) B11081249
theorem B4102559 : Blo 1821612 4102559 := bstep (se 1 (by rfl) ⟨3076919, by rfl⟩ : syracuseStep 4102559 = 6153839) B6153839
theorem B11680199 : Blo 1821612 11680199 := bstep (se 1 (by rfl) ⟨8760149, by rfl⟩ : syracuseStep 11680199 = 17520299) B17520299
theorem B2734535 : Blo 1821612 2734535 := bstep (se 1 (by rfl) ⟨2050901, by rfl⟩ : syracuseStep 2734535 = 4101803) B4101803
theorem B4102631 : Blo 1821612 4102631 := bstep (se 1 (by rfl) ⟨3076973, by rfl⟩ : syracuseStep 4102631 = 6153947) B6153947
theorem B6920761 : Blo 1821612 6920761 := bstep (se 2 (by rfl) ⟨2595285, by rfl⟩ : syracuseStep 6920761 = 5190571) B5190571
theorem B2734751 : Blo 1821612 2734751 := bstep (se 1 (by rfl) ⟨2051063, by rfl⟩ : syracuseStep 2734751 = 4102127) B4102127
theorem B2734895 : Blo 1821612 2734895 := bstep (se 1 (by rfl) ⟨2051171, by rfl⟩ : syracuseStep 2734895 = 4102343) B4102343
theorem B37395269 : Blo 1821612 37395269 := bstep (se 4 (by rfl) ⟨3505806, by rfl⟩ : syracuseStep 37395269 = 7011613) B7011613
theorem B2735015 : Blo 1821612 2735015 := bstep (se 1 (by rfl) ⟨2051261, by rfl⟩ : syracuseStep 2735015 = 4102523) B4102523
theorem B7781467 : Blo 1821612 7781467 := bstep (se 1 (by rfl) ⟨5836100, by rfl⟩ : syracuseStep 7781467 = 11672201) B11672201
theorem B2735195 : Blo 1821612 2735195 := bstep (se 1 (by rfl) ⟨2051396, by rfl⟩ : syracuseStep 2735195 = 4102793) B4102793
theorem B11681657 : Blo 1821612 11681657 := bstep (se 2 (by rfl) ⟨4380621, by rfl⟩ : syracuseStep 11681657 = 8761243) B8761243
theorem B15564743 : Blo 1821612 15564743 := bstep (se 1 (by rfl) ⟨11673557, by rfl⟩ : syracuseStep 15564743 = 23347115) B23347115
theorem B9855017 : Blo 1821612 9855017 := bstep (se 2 (by rfl) ⟨3695631, by rfl⟩ : syracuseStep 9855017 = 7391263) B7391263
theorem B9855101 : Blo 1821612 9855101 := bstep (se 3 (by rfl) ⟨1847831, by rfl⟩ : syracuseStep 9855101 = 3695663) B3695663
theorem B6152381 : Blo 1821612 6152381 := bstep (se 3 (by rfl) ⟨1153571, by rfl⟩ : syracuseStep 6152381 = 2307143) B2307143
theorem B10526935 : Blo 1821612 10526935 := bstep (se 1 (by rfl) ⟨7895201, by rfl⟩ : syracuseStep 10526935 = 15790403) B15790403
theorem B6152543 : Blo 1821612 6152543 := bstep (se 1 (by rfl) ⟨4614407, by rfl⟩ : syracuseStep 6152543 = 9228815) B9228815
theorem B20759003 : Blo 1821612 20759003 := bstep (se 1 (by rfl) ⟨15569252, by rfl⟩ : syracuseStep 20759003 = 31138505) B31138505
theorem B7693103 : Blo 1821612 7693103 := bstep (se 1 (by rfl) ⟨5769827, by rfl⟩ : syracuseStep 7693103 = 11539655) B11539655
theorem B59138909 : Blo 1821612 59138909 := bstep (se 3 (by rfl) ⟨11088545, by rfl⟩ : syracuseStep 59138909 = 22177091) B22177091
theorem B20767751 : Blo 1821612 20767751 := bstep (se 1 (by rfl) ⟨15575813, by rfl⟩ : syracuseStep 20767751 = 31151627) B31151627
theorem B2769967 : Blo 1821612 2769967 := bstep (se 1 (by rfl) ⟨2077475, by rfl⟩ : syracuseStep 2769967 = 4154951) B4154951
theorem B4613345 : Blo 1821612 4613345 := bstep (se 2 (by rfl) ⟨1730004, by rfl⟩ : syracuseStep 4613345 = 3460009) B3460009
theorem B11683091 : Blo 1821612 11683091 := bstep (se 1 (by rfl) ⟨8762318, by rfl⟩ : syracuseStep 11683091 = 17524637) B17524637
theorem B14026061 : Blo 1821612 14026061 := bstep (se 3 (by rfl) ⟨2629886, by rfl⟩ : syracuseStep 14026061 = 5259773) B5259773
theorem B4924763 : Blo 1821612 4924763 := bstep (se 1 (by rfl) ⟨3693572, by rfl⟩ : syracuseStep 4924763 = 7387145) B7387145
theorem B9225575 : Blo 1821612 9225575 := bstep (se 1 (by rfl) ⟨6919181, by rfl⟩ : syracuseStep 9225575 = 13838363) B13838363
theorem B4924999 : Blo 1821612 4924999 := bstep (se 1 (by rfl) ⟨3693749, by rfl⟩ : syracuseStep 4924999 = 7387499) B7387499
theorem B9848441 : Blo 1821612 9848441 := bstep (se 2 (by rfl) ⟨3693165, by rfl⟩ : syracuseStep 9848441 = 7386331) B7386331
theorem B24930179 : Blo 1821612 24930179 := bstep (se 1 (by rfl) ⟨18697634, by rfl⟩ : syracuseStep 24930179 = 37395269) B37395269
theorem B3459667 : Blo 1821612 3459667 := bstep (se 1 (by rfl) ⟨2594750, by rfl⟩ : syracuseStep 3459667 = 5189501) B5189501
theorem B8309405 : Blo 1821612 8309405 := bstep (se 3 (by rfl) ⟨1558013, by rfl⟩ : syracuseStep 8309405 = 3116027) B3116027
theorem B40028843 : Blo 1821612 40028843 := bstep (se 1 (by rfl) ⟨30021632, by rfl⟩ : syracuseStep 40028843 = 60043265) B60043265
theorem B20753171 : Blo 1821612 20753171 := bstep (se 1 (by rfl) ⟨15564878, by rfl⟩ : syracuseStep 20753171 = 31129757) B31129757
theorem B1821863 : Blo 1821612 1821863 := bstep (se 1 (by rfl) ⟨1366397, by rfl⟩ : syracuseStep 1821863 = 2732795) B2732795
theorem B2051239 : Blo 1821612 2051239 := bstep (se 1 (by rfl) ⟨1538429, by rfl⟩ : syracuseStep 2051239 = 3076859) B3076859
theorem B16625051 : Blo 1821612 16625051 := bstep (se 1 (by rfl) ⟨12468788, by rfl⟩ : syracuseStep 16625051 = 24937577) B24937577
theorem B9227681 : Blo 1821612 9227681 := bstep (se 2 (by rfl) ⟨3460380, by rfl⟩ : syracuseStep 9227681 = 6920761) B6920761
theorem B1822159 : Blo 1821612 1822159 := bstep (se 1 (by rfl) ⟨1366619, by rfl⟩ : syracuseStep 1822159 = 2733239) B2733239
theorem B1822319 : Blo 1821612 1822319 := bstep (se 1 (by rfl) ⟨1366739, by rfl⟩ : syracuseStep 1822319 = 2733479) B2733479
theorem B5836511 : Blo 1821612 5836511 := bstep (se 1 (by rfl) ⟨4377383, by rfl⟩ : syracuseStep 5836511 = 8754767) B8754767
theorem B1822439 : Blo 1821612 1822439 := bstep (se 1 (by rfl) ⟨1366829, by rfl⟩ : syracuseStep 1822439 = 2733659) B2733659
theorem B24940361 : Blo 1821612 24940361 := bstep (se 2 (by rfl) ⟨9352635, by rfl⟩ : syracuseStep 24940361 = 18705271) B18705271
theorem B3460943 : Blo 1821612 3460943 := bstep (se 1 (by rfl) ⟨2595707, by rfl⟩ : syracuseStep 3460943 = 5191415) B5191415
theorem B2305903 : Blo 1821612 2305903 := bstep (se 1 (by rfl) ⟨1729427, by rfl⟩ : syracuseStep 2305903 = 3458855) B3458855
theorem B7786439 : Blo 1821612 7786439 := bstep (se 1 (by rfl) ⟨5839829, by rfl⟩ : syracuseStep 7786439 = 11679659) B11679659
theorem B6918119 : Blo 1821612 6918119 := bstep (se 1 (by rfl) ⟨5188589, by rfl⟩ : syracuseStep 6918119 = 10377179) B10377179
theorem B4100075 : Blo 1821612 4100075 := bstep (se 1 (by rfl) ⟨3075056, by rfl⟩ : syracuseStep 4100075 = 6150113) B6150113
theorem B5189615 : Blo 1821612 5189615 := bstep (se 1 (by rfl) ⟨3892211, by rfl⟩ : syracuseStep 5189615 = 7784423) B7784423
theorem B1822747 : Blo 1821612 1822747 := bstep (se 1 (by rfl) ⟨1367060, by rfl⟩ : syracuseStep 1822747 = 2734121) B2734121
theorem B1822767 : Blo 1821612 1822767 := bstep (se 1 (by rfl) ⟨1367075, by rfl⟩ : syracuseStep 1822767 = 2734151) B2734151
theorem B5615723 : Blo 1821612 5615723 := bstep (se 1 (by rfl) ⟨4211792, by rfl⟩ : syracuseStep 5615723 = 8423585) B8423585
theorem B10375289 : Blo 1821612 10375289 := bstep (se 2 (by rfl) ⟨3890733, by rfl⟩ : syracuseStep 10375289 = 7781467) B7781467
theorem B6148223 : Blo 1821612 6148223 := bstep (se 1 (by rfl) ⟨4611167, by rfl⟩ : syracuseStep 6148223 = 9222335) B9222335
theorem B3330175 : Blo 1821612 3330175 := bstep (se 1 (by rfl) ⟨2497631, by rfl⟩ : syracuseStep 3330175 = 4995263) B4995263
theorem B15569117 : Blo 1821612 15569117 := bstep (se 3 (by rfl) ⟨2919209, by rfl⟩ : syracuseStep 15569117 = 5838419) B5838419
theorem B7786799 : Blo 1821612 7786799 := bstep (se 1 (by rfl) ⟨5840099, by rfl⟩ : syracuseStep 7786799 = 11680199) B11680199
theorem B1823023 : Blo 1821612 1823023 := bstep (se 1 (by rfl) ⟨1367267, by rfl⟩ : syracuseStep 1823023 = 2734535) B2734535
theorem B1823167 : Blo 1821612 1823167 := bstep (se 1 (by rfl) ⟨1367375, by rfl⟩ : syracuseStep 1823167 = 2734751) B2734751
theorem B35516879 : Blo 1821612 35516879 := bstep (se 1 (by rfl) ⟨26637659, by rfl⟩ : syracuseStep 35516879 = 53275319) B53275319
theorem B1823263 : Blo 1821612 1823263 := bstep (se 1 (by rfl) ⟨1367447, by rfl⟩ : syracuseStep 1823263 = 2734895) B2734895
theorem B1823343 : Blo 1821612 1823343 := bstep (se 1 (by rfl) ⟨1367507, by rfl⟩ : syracuseStep 1823343 = 2735015) B2735015
theorem B23368337 : Blo 1821612 23368337 := bstep (se 2 (by rfl) ⟨8763126, by rfl⟩ : syracuseStep 23368337 = 17526253) B17526253
theorem B2732711 : Blo 1821612 2732711 := bstep (se 1 (by rfl) ⟨2049533, by rfl⟩ : syracuseStep 2732711 = 4099067) B4099067
theorem B17756873 : Blo 1821612 17756873 := bstep (se 2 (by rfl) ⟨6658827, by rfl⟩ : syracuseStep 17756873 = 13317655) B13317655
theorem B1823463 : Blo 1821612 1823463 := bstep (se 1 (by rfl) ⟨1367597, by rfl⟩ : syracuseStep 1823463 = 2735195) B2735195
theorem B2732831 : Blo 1821612 2732831 := bstep (se 1 (by rfl) ⟨2049623, by rfl⟩ : syracuseStep 2732831 = 4099247) B4099247
theorem B2732855 : Blo 1821612 2732855 := bstep (se 1 (by rfl) ⟨2049641, by rfl⟩ : syracuseStep 2732855 = 4099283) B4099283
theorem B2732969 : Blo 1821612 2732969 := bstep (se 2 (by rfl) ⟨1024863, by rfl⟩ : syracuseStep 2732969 = 2049727) B2049727
theorem B2733035 : Blo 1821612 2733035 := bstep (se 1 (by rfl) ⟨2049776, by rfl⟩ : syracuseStep 2733035 = 4099553) B4099553
theorem B7787771 : Blo 1821612 7787771 := bstep (se 1 (by rfl) ⟨5840828, by rfl⟩ : syracuseStep 7787771 = 11681657) B11681657
theorem B2733311 : Blo 1821612 2733311 := bstep (se 1 (by rfl) ⟨2049983, by rfl⟩ : syracuseStep 2733311 = 4099967) B4099967
theorem B2733353 : Blo 1821612 2733353 := bstep (se 2 (by rfl) ⟨1025007, by rfl⟩ : syracuseStep 2733353 = 2050015) B2050015
theorem B10376495 : Blo 1821612 10376495 := bstep (se 1 (by rfl) ⟨7782371, by rfl⟩ : syracuseStep 10376495 = 15564743) B15564743
theorem B1947007 : Blo 1821612 1947007 := bstep (se 1 (by rfl) ⟨1460255, by rfl⟩ : syracuseStep 1947007 = 2920511) B2920511
theorem B67450259 : Blo 1821612 67450259 := bstep (se 1 (by rfl) ⟨50587694, by rfl⟩ : syracuseStep 67450259 = 101175389) B101175389
theorem B2594215 : Blo 1821612 2594215 := bstep (se 1 (by rfl) ⟨1945661, by rfl⟩ : syracuseStep 2594215 = 3891323) B3891323
theorem B6149627 : Blo 1821612 6149627 := bstep (se 1 (by rfl) ⟨4612220, by rfl⟩ : syracuseStep 6149627 = 9224441) B9224441
theorem B10524239 : Blo 1821612 10524239 := bstep (se 1 (by rfl) ⟨7893179, by rfl⟩ : syracuseStep 10524239 = 15786359) B15786359
theorem B7788113 : Blo 1821612 7788113 := bstep (se 2 (by rfl) ⟨2920542, by rfl⟩ : syracuseStep 7788113 = 5841085) B5841085
theorem B8762975 : Blo 1821612 8762975 := bstep (se 1 (by rfl) ⟨6572231, by rfl⟩ : syracuseStep 8762975 = 13144463) B13144463
theorem B2307791 : Blo 1821612 2307791 := bstep (se 1 (by rfl) ⟨1730843, by rfl⟩ : syracuseStep 2307791 = 3461687) B3461687
theorem B9222011 : Blo 1821612 9222011 := bstep (se 1 (by rfl) ⟨6916508, by rfl⟩ : syracuseStep 9222011 = 13833017) B13833017
theorem B2733947 : Blo 1821612 2733947 := bstep (se 1 (by rfl) ⟨2050460, by rfl⟩ : syracuseStep 2733947 = 4100921) B4100921
theorem B6920093 : Blo 1821612 6920093 := bstep (se 3 (by rfl) ⟨1297517, by rfl⟩ : syracuseStep 6920093 = 2595035) B2595035
theorem B2733983 : Blo 1821612 2733983 := bstep (se 1 (by rfl) ⟨2050487, by rfl⟩ : syracuseStep 2733983 = 4100975) B4100975
theorem B6150059 : Blo 1821612 6150059 := bstep (se 1 (by rfl) ⟨4612544, by rfl⟩ : syracuseStep 6150059 = 9225089) B9225089
theorem B6920275 : Blo 1821612 6920275 := bstep (se 1 (by rfl) ⟨5190206, by rfl⟩ : syracuseStep 6920275 = 10380413) B10380413
theorem B2734187 : Blo 1821612 2734187 := bstep (se 1 (by rfl) ⟨2050640, by rfl⟩ : syracuseStep 2734187 = 4101281) B4101281
theorem B2734217 : Blo 1821612 2734217 := bstep (se 2 (by rfl) ⟨1025331, by rfl⟩ : syracuseStep 2734217 = 2050663) B2050663
theorem B2734367 : Blo 1821612 2734367 := bstep (se 1 (by rfl) ⟨2050775, by rfl⟩ : syracuseStep 2734367 = 4101551) B4101551
theorem B26286443 : Blo 1821612 26286443 := bstep (se 1 (by rfl) ⟨19714832, by rfl⟩ : syracuseStep 26286443 = 39429665) B39429665
theorem B6150599 : Blo 1821612 6150599 := bstep (se 1 (by rfl) ⟨4612949, by rfl⟩ : syracuseStep 6150599 = 9225899) B9225899
theorem B5192417 : Blo 1821612 5192417 := bstep (se 2 (by rfl) ⟨1947156, by rfl⟩ : syracuseStep 5192417 = 3894313) B3894313
theorem B6150923 : Blo 1821612 6150923 := bstep (se 1 (by rfl) ⟨4613192, by rfl⟩ : syracuseStep 6150923 = 9226385) B9226385
theorem B23354243 : Blo 1821612 23354243 := bstep (se 1 (by rfl) ⟨17515682, by rfl⟩ : syracuseStep 23354243 = 35031365) B35031365
theorem B2735039 : Blo 1821612 2735039 := bstep (se 1 (by rfl) ⟨2051279, by rfl⟩ : syracuseStep 2735039 = 4102559) B4102559
theorem B2735087 : Blo 1821612 2735087 := bstep (se 1 (by rfl) ⟨2051315, by rfl⟩ : syracuseStep 2735087 = 4102631) B4102631
theorem B9231407 : Blo 1821612 9231407 := bstep (se 1 (by rfl) ⟨6923555, by rfl⟩ : syracuseStep 9231407 = 13847111) B13847111
theorem B2735273 : Blo 1821612 2735273 := bstep (se 2 (by rfl) ⟨1025727, by rfl⟩ : syracuseStep 2735273 = 2051455) B2051455
theorem B13843709 : Blo 1821612 13843709 := bstep (se 3 (by rfl) ⟨2595695, by rfl⟩ : syracuseStep 13843709 = 5191391) B5191391
theorem B19701377 : Blo 1821612 19701377 := bstep (se 2 (by rfl) ⟨7388016, by rfl⟩ : syracuseStep 19701377 = 14776033) B14776033
theorem B6152057 : Blo 1821612 6152057 := bstep (se 2 (by rfl) ⟨2307021, by rfl⟩ : syracuseStep 6152057 = 4614043) B4614043
theorem B5840855 : Blo 1821612 5840855 := bstep (se 1 (by rfl) ⟨4380641, by rfl⟩ : syracuseStep 5840855 = 8761283) B8761283
theorem B6570011 : Blo 1821612 6570011 := bstep (se 1 (by rfl) ⟨4927508, by rfl⟩ : syracuseStep 6570011 = 9855017) B9855017
theorem B6570067 : Blo 1821612 6570067 := bstep (se 1 (by rfl) ⟨4927550, by rfl⟩ : syracuseStep 6570067 = 9855101) B9855101
theorem B10379411 : Blo 1821612 10379411 := bstep (se 1 (by rfl) ⟨7784558, by rfl⟩ : syracuseStep 10379411 = 15569117) B15569117
theorem B4440233 : Blo 1821612 4440233 := bstep (se 2 (by rfl) ⟨1665087, by rfl⟩ : syracuseStep 4440233 = 3330175) B3330175
theorem B14975261 : Blo 1821612 14975261 := bstep (se 3 (by rfl) ⟨2807861, by rfl⟩ : syracuseStep 14975261 = 5615723) B5615723
theorem B11837915 : Blo 1821612 11837915 := bstep (se 1 (by rfl) ⟨8878436, by rfl⟩ : syracuseStep 11837915 = 17756873) B17756873
theorem B5128735 : Blo 1821612 5128735 := bstep (se 1 (by rfl) ⟨3846551, by rfl⟩ : syracuseStep 5128735 = 7693103) B7693103
theorem B13845167 : Blo 1821612 13845167 := bstep (se 1 (by rfl) ⟨10383875, by rfl⟩ : syracuseStep 13845167 = 20767751) B20767751
theorem B4612889 : Blo 1821612 4612889 := bstep (se 2 (by rfl) ⟨1729833, by rfl⟩ : syracuseStep 4612889 = 3459667) B3459667
theorem B44966839 : Blo 1821612 44966839 := bstep (se 1 (by rfl) ⟨33725129, by rfl⟩ : syracuseStep 44966839 = 67450259) B67450259
theorem B5841983 : Blo 1821612 5841983 := bstep (se 1 (by rfl) ⟨4381487, by rfl⟩ : syracuseStep 5841983 = 8762975) B8762975
theorem B4613395 : Blo 1821612 4613395 := bstep (se 1 (by rfl) ⟨3460046, by rfl⟩ : syracuseStep 4613395 = 6920093) B6920093
theorem B17524295 : Blo 1821612 17524295 := bstep (se 1 (by rfl) ⟨13143221, by rfl⟩ : syracuseStep 17524295 = 26286443) B26286443
theorem B5539603 : Blo 1821612 5539603 := bstep (se 1 (by rfl) ⟨4154702, by rfl⟩ : syracuseStep 5539603 = 8309405) B8309405
theorem B6154109 : Blo 1821612 6154109 := bstep (se 3 (by rfl) ⟨1153895, by rfl⟩ : syracuseStep 6154109 = 2307791) B2307791
theorem B3458953 : Blo 1821612 3458953 := bstep (se 2 (by rfl) ⟨1297107, by rfl⟩ : syracuseStep 3458953 = 2594215) B2594215
theorem B6154271 : Blo 1821612 6154271 := bstep (se 1 (by rfl) ⟨4615703, by rfl⟩ : syracuseStep 6154271 = 9231407) B9231407
theorem B13134251 : Blo 1821612 13134251 := bstep (se 1 (by rfl) ⟨9850688, by rfl⟩ : syracuseStep 13134251 = 19701377) B19701377
theorem B3074537 : Blo 1821612 3074537 := bstep (se 2 (by rfl) ⟨1152951, by rfl⟩ : syracuseStep 3074537 = 2305903) B2305903
theorem B3893903 : Blo 1821612 3893903 := bstep (se 1 (by rfl) ⟨2920427, by rfl⟩ : syracuseStep 3893903 = 5840855) B5840855
theorem B3459743 : Blo 1821612 3459743 := bstep (se 1 (by rfl) ⟨2594807, by rfl⟩ : syracuseStep 3459743 = 5189615) B5189615
theorem B6916859 : Blo 1821612 6916859 := bstep (se 1 (by rfl) ⟨5187644, by rfl⟩ : syracuseStep 6916859 = 10375289) B10375289
theorem B4098815 : Blo 1821612 4098815 := bstep (se 1 (by rfl) ⟨3074111, by rfl⟩ : syracuseStep 4098815 = 6148223) B6148223
theorem B9227033 : Blo 1821612 9227033 := bstep (se 2 (by rfl) ⟨3460137, by rfl⟩ : syracuseStep 9227033 = 6920275) B6920275
theorem B14035913 : Blo 1821612 14035913 := bstep (se 2 (by rfl) ⟨5263467, by rfl⟩ : syracuseStep 14035913 = 10526935) B10526935
theorem B23677919 : Blo 1821612 23677919 := bstep (se 1 (by rfl) ⟨17758439, by rfl⟩ : syracuseStep 23677919 = 35516879) B35516879
theorem B13839335 : Blo 1821612 13839335 := bstep (se 1 (by rfl) ⟨10379501, by rfl⟩ : syracuseStep 13839335 = 20759003) B20759003
theorem B1821807 : Blo 1821612 1821807 := bstep (se 1 (by rfl) ⟨1366355, by rfl⟩ : syracuseStep 1821807 = 2732711) B2732711
theorem B1821887 : Blo 1821612 1821887 := bstep (se 1 (by rfl) ⟨1366415, by rfl⟩ : syracuseStep 1821887 = 2732831) B2732831
theorem B1821903 : Blo 1821612 1821903 := bstep (se 1 (by rfl) ⟨1366427, by rfl⟩ : syracuseStep 1821903 = 2732855) B2732855
theorem B1821979 : Blo 1821612 1821979 := bstep (se 1 (by rfl) ⟨1366484, by rfl⟩ : syracuseStep 1821979 = 2732969) B2732969
theorem B1822023 : Blo 1821612 1822023 := bstep (se 1 (by rfl) ⟨1366517, by rfl⟩ : syracuseStep 1822023 = 2733035) B2733035
theorem B3075563 : Blo 1821612 3075563 := bstep (se 1 (by rfl) ⟨2306672, by rfl⟩ : syracuseStep 3075563 = 4613345) B4613345
theorem B1822207 : Blo 1821612 1822207 := bstep (se 1 (by rfl) ⟨1366655, by rfl⟩ : syracuseStep 1822207 = 2733311) B2733311
theorem B1822235 : Blo 1821612 1822235 := bstep (se 1 (by rfl) ⟨1366676, by rfl⟩ : syracuseStep 1822235 = 2733353) B2733353
theorem B6917663 : Blo 1821612 6917663 := bstep (se 1 (by rfl) ⟨5188247, by rfl⟩ : syracuseStep 6917663 = 10376495) B10376495
theorem B9350707 : Blo 1821612 9350707 := bstep (se 1 (by rfl) ⟨7013030, by rfl⟩ : syracuseStep 9350707 = 14026061) B14026061
theorem B4099751 : Blo 1821612 4099751 := bstep (se 1 (by rfl) ⟨3074813, by rfl⟩ : syracuseStep 4099751 = 6149627) B6149627
theorem B7016159 : Blo 1821612 7016159 := bstep (se 1 (by rfl) ⟨5262119, by rfl⟩ : syracuseStep 7016159 = 10524239) B10524239
theorem B6565627 : Blo 1821612 6565627 := bstep (se 1 (by rfl) ⟨4924220, by rfl⟩ : syracuseStep 6565627 = 9848441) B9848441
theorem B6148007 : Blo 1821612 6148007 := bstep (se 1 (by rfl) ⟨4611005, by rfl⟩ : syracuseStep 6148007 = 9222011) B9222011
theorem B1822631 : Blo 1821612 1822631 := bstep (se 1 (by rfl) ⟨1366973, by rfl⟩ : syracuseStep 1822631 = 2733947) B2733947
theorem B1822655 : Blo 1821612 1822655 := bstep (se 1 (by rfl) ⟨1366991, by rfl⟩ : syracuseStep 1822655 = 2733983) B2733983
theorem B4100039 : Blo 1821612 4100039 := bstep (se 1 (by rfl) ⟨3075029, by rfl⟩ : syracuseStep 4100039 = 6150059) B6150059
theorem B1822791 : Blo 1821612 1822791 := bstep (se 1 (by rfl) ⟨1367093, by rfl⟩ : syracuseStep 1822791 = 2734187) B2734187
theorem B1822811 : Blo 1821612 1822811 := bstep (se 1 (by rfl) ⟨1367108, by rfl⟩ : syracuseStep 1822811 = 2734217) B2734217
theorem B1822911 : Blo 1821612 1822911 := bstep (se 1 (by rfl) ⟨1367183, by rfl⟩ : syracuseStep 1822911 = 2734367) B2734367
theorem B4100399 : Blo 1821612 4100399 := bstep (se 1 (by rfl) ⟨3075299, by rfl⟩ : syracuseStep 4100399 = 6150599) B6150599
theorem B26685895 : Blo 1821612 26685895 := bstep (se 1 (by rfl) ⟨20014421, by rfl⟩ : syracuseStep 26685895 = 40028843) B40028843
theorem B3461611 : Blo 1821612 3461611 := bstep (se 1 (by rfl) ⟨2596208, by rfl⟩ : syracuseStep 3461611 = 5192417) B5192417
theorem B4100615 : Blo 1821612 4100615 := bstep (se 1 (by rfl) ⟨3075461, by rfl⟩ : syracuseStep 4100615 = 6150923) B6150923
theorem B15569495 : Blo 1821612 15569495 := bstep (se 1 (by rfl) ⟨11677121, by rfl⟩ : syracuseStep 15569495 = 23354243) B23354243
theorem B1823359 : Blo 1821612 1823359 := bstep (se 1 (by rfl) ⟨1367519, by rfl⟩ : syracuseStep 1823359 = 2735039) B2735039
theorem B1823391 : Blo 1821612 1823391 := bstep (se 1 (by rfl) ⟨1367543, by rfl⟩ : syracuseStep 1823391 = 2735087) B2735087
theorem B10384037 : Blo 1821612 10384037 := bstep (se 4 (by rfl) ⟨973503, by rfl⟩ : syracuseStep 10384037 = 1947007) B1947007
theorem B6566665 : Blo 1821612 6566665 := bstep (se 2 (by rfl) ⟨2462499, by rfl⟩ : syracuseStep 6566665 = 4924999) B4924999
theorem B1823515 : Blo 1821612 1823515 := bstep (se 1 (by rfl) ⟨1367636, by rfl⟩ : syracuseStep 1823515 = 2735273) B2735273
theorem B9229139 : Blo 1821612 9229139 := bstep (se 1 (by rfl) ⟨6921854, by rfl⟩ : syracuseStep 9229139 = 13843709) B13843709
theorem B16626907 : Blo 1821612 16626907 := bstep (se 1 (by rfl) ⟨12470180, by rfl⟩ : syracuseStep 16626907 = 24940361) B24940361
theorem B2307295 : Blo 1821612 2307295 := bstep (se 1 (by rfl) ⟨1730471, by rfl⟩ : syracuseStep 2307295 = 3460943) B3460943
theorem B4101371 : Blo 1821612 4101371 := bstep (se 1 (by rfl) ⟨3076028, by rfl⟩ : syracuseStep 4101371 = 6152057) B6152057
theorem B5190959 : Blo 1821612 5190959 := bstep (se 1 (by rfl) ⟨3893219, by rfl⟩ : syracuseStep 5190959 = 7786439) B7786439
theorem B2733383 : Blo 1821612 2733383 := bstep (se 1 (by rfl) ⟨2050037, by rfl⟩ : syracuseStep 2733383 = 4100075) B4100075
theorem B4101587 : Blo 1821612 4101587 := bstep (se 1 (by rfl) ⟨3076190, by rfl⟩ : syracuseStep 4101587 = 6152381) B6152381
theorem B5191199 : Blo 1821612 5191199 := bstep (se 1 (by rfl) ⟨3893399, by rfl⟩ : syracuseStep 5191199 = 7786799) B7786799
theorem B4101695 : Blo 1821612 4101695 := bstep (se 1 (by rfl) ⟨3076271, by rfl⟩ : syracuseStep 4101695 = 6152543) B6152543
theorem B15578891 : Blo 1821612 15578891 := bstep (se 1 (by rfl) ⟨11684168, by rfl⟩ : syracuseStep 15578891 = 23368337) B23368337
theorem B39425939 : Blo 1821612 39425939 := bstep (se 1 (by rfl) ⟨29569454, by rfl⟩ : syracuseStep 39425939 = 59138909) B59138909
theorem B5191847 : Blo 1821612 5191847 := bstep (se 1 (by rfl) ⟨3893885, by rfl⟩ : syracuseStep 5191847 = 7787771) B7787771
theorem B7788727 : Blo 1821612 7788727 := bstep (se 1 (by rfl) ⟨5841545, by rfl⟩ : syracuseStep 7788727 = 11683091) B11683091
theorem B3283175 : Blo 1821612 3283175 := bstep (se 1 (by rfl) ⟨2462381, by rfl⟩ : syracuseStep 3283175 = 4924763) B4924763
theorem B6150383 : Blo 1821612 6150383 := bstep (se 1 (by rfl) ⟨4612787, by rfl⟩ : syracuseStep 6150383 = 9225575) B9225575
theorem B5192075 : Blo 1821612 5192075 := bstep (se 1 (by rfl) ⟨3894056, by rfl⟩ : syracuseStep 5192075 = 7788113) B7788113
theorem B16620119 : Blo 1821612 16620119 := bstep (se 1 (by rfl) ⟨12465089, by rfl⟩ : syracuseStep 16620119 = 24930179) B24930179
theorem B3693289 : Blo 1821612 3693289 := bstep (se 2 (by rfl) ⟨1384983, by rfl⟩ : syracuseStep 3693289 = 2769967) B2769967
theorem B2734985 : Blo 1821612 2734985 := bstep (se 2 (by rfl) ⟨1025619, by rfl⟩ : syracuseStep 2734985 = 2051239) B2051239
theorem B13835447 : Blo 1821612 13835447 := bstep (se 1 (by rfl) ⟨10376585, by rfl⟩ : syracuseStep 13835447 = 20753171) B20753171
theorem B11083367 : Blo 1821612 11083367 := bstep (se 1 (by rfl) ⟨8312525, by rfl⟩ : syracuseStep 11083367 = 16625051) B16625051
theorem B6151787 : Blo 1821612 6151787 := bstep (se 1 (by rfl) ⟨4613840, by rfl⟩ : syracuseStep 6151787 = 9227681) B9227681
theorem B3891007 : Blo 1821612 3891007 := bstep (se 1 (by rfl) ⟨2918255, by rfl⟩ : syracuseStep 3891007 = 5836511) B5836511
theorem B4612079 : Blo 1821612 4612079 := bstep (se 1 (by rfl) ⟨3459059, by rfl⟩ : syracuseStep 4612079 = 6918119) B6918119
theorem B10379663 : Blo 1821612 10379663 := bstep (se 1 (by rfl) ⟨7784747, by rfl⟩ : syracuseStep 10379663 = 15569495) B15569495
theorem B6922691 : Blo 1821612 6922691 := bstep (se 1 (by rfl) ⟨5192018, by rfl⟩ : syracuseStep 6922691 = 10384037) B10384037
theorem B6152759 : Blo 1821612 6152759 := bstep (se 1 (by rfl) ⟨4614569, by rfl⟩ : syracuseStep 6152759 = 9229139) B9229139
theorem B109413013 : Blo 1821612 109413013 := bstep (se 6 (by rfl) ⟨2564367, by rfl⟩ : syracuseStep 109413013 = 5128735) B5128735
theorem B4924385 : Blo 1821612 4924385 := bstep (se 2 (by rfl) ⟨1846644, by rfl⟩ : syracuseStep 4924385 = 3693289) B3693289
theorem B11682863 : Blo 1821612 11682863 := bstep (se 1 (by rfl) ⟨8762147, by rfl⟩ : syracuseStep 11682863 = 17524295) B17524295
theorem B2188783 : Blo 1821612 2188783 := bstep (se 1 (by rfl) ⟨1641587, by rfl⟩ : syracuseStep 2188783 = 3283175) B3283175
theorem B22169209 : Blo 1821612 22169209 := bstep (se 2 (by rfl) ⟨8313453, by rfl⟩ : syracuseStep 22169209 = 16626907) B16626907
theorem B2049691 : Blo 1821612 2049691 := bstep (se 1 (by rfl) ⟨1537268, by rfl⟩ : syracuseStep 2049691 = 3074537) B3074537
theorem B9357275 : Blo 1821612 9357275 := bstep (se 1 (by rfl) ⟨7017956, by rfl⟩ : syracuseStep 9357275 = 14035913) B14035913
theorem B9226223 : Blo 1821612 9226223 := bstep (se 1 (by rfl) ⟨6919667, by rfl⟩ : syracuseStep 9226223 = 13839335) B13839335
theorem B2050375 : Blo 1821612 2050375 := bstep (se 1 (by rfl) ⟨1537781, by rfl⟩ : syracuseStep 2050375 = 3075563) B3075563
theorem B5188009 : Blo 1821612 5188009 := bstep (se 2 (by rfl) ⟨1945503, by rfl⟩ : syracuseStep 5188009 = 3891007) B3891007
theorem B4098671 : Blo 1821612 4098671 := bstep (se 1 (by rfl) ⟨3074003, by rfl⟩ : syracuseStep 4098671 = 6148007) B6148007
theorem B3074719 : Blo 1821612 3074719 := bstep (se 1 (by rfl) ⟨2306039, by rfl⟩ : syracuseStep 3074719 = 4612079) B4612079
theorem B8760089 : Blo 1821612 8760089 := bstep (se 2 (by rfl) ⟨3285033, by rfl⟩ : syracuseStep 8760089 = 6570067) B6570067
theorem B2960155 : Blo 1821612 2960155 := bstep (se 1 (by rfl) ⟨2220116, by rfl⟩ : syracuseStep 2960155 = 4440233) B4440233
theorem B7891943 : Blo 1821612 7891943 := bstep (se 1 (by rfl) ⟨5918957, by rfl⟩ : syracuseStep 7891943 = 11837915) B11837915
theorem B3075259 : Blo 1821612 3075259 := bstep (se 1 (by rfl) ⟨2306444, by rfl⟩ : syracuseStep 3075259 = 4612889) B4612889
theorem B35581193 : Blo 1821612 35581193 := bstep (se 2 (by rfl) ⟨13342947, by rfl⟩ : syracuseStep 35581193 = 26685895) B26685895
theorem B4615481 : Blo 1821612 4615481 := bstep (se 2 (by rfl) ⟨1730805, by rfl⟩ : syracuseStep 4615481 = 3461611) B3461611
theorem B3894655 : Blo 1821612 3894655 := bstep (se 1 (by rfl) ⟨2920991, by rfl⟩ : syracuseStep 3894655 = 5841983) B5841983
theorem B3460639 : Blo 1821612 3460639 := bstep (se 1 (by rfl) ⟨2595479, by rfl⟩ : syracuseStep 3460639 = 5190959) B5190959
theorem B1822255 : Blo 1821612 1822255 := bstep (se 1 (by rfl) ⟨1366691, by rfl⟩ : syracuseStep 1822255 = 2733383) B2733383
theorem B3460799 : Blo 1821612 3460799 := bstep (se 1 (by rfl) ⟨2595599, by rfl⟩ : syracuseStep 3460799 = 5191199) B5191199
theorem B35024669 : Blo 1821612 35024669 := bstep (se 3 (by rfl) ⟨6567125, by rfl⟩ : syracuseStep 35024669 = 13134251) B13134251
theorem B26283959 : Blo 1821612 26283959 := bstep (se 1 (by rfl) ⟨19712969, by rfl⟩ : syracuseStep 26283959 = 39425939) B39425939
theorem B3461231 : Blo 1821612 3461231 := bstep (se 1 (by rfl) ⟨2595923, by rfl⟩ : syracuseStep 3461231 = 5191847) B5191847
theorem B4100255 : Blo 1821612 4100255 := bstep (se 1 (by rfl) ⟨3075191, by rfl⟩ : syracuseStep 4100255 = 6150383) B6150383
theorem B3461383 : Blo 1821612 3461383 := bstep (se 1 (by rfl) ⟨2596037, by rfl⟩ : syracuseStep 3461383 = 5192075) B5192075
theorem B3076393 : Blo 1821612 3076393 := bstep (se 2 (by rfl) ⟨1153647, by rfl⟩ : syracuseStep 3076393 = 2307295) B2307295
theorem B11080079 : Blo 1821612 11080079 := bstep (se 1 (by rfl) ⟨8310059, by rfl⟩ : syracuseStep 11080079 = 16620119) B16620119
theorem B2306495 : Blo 1821612 2306495 := bstep (se 1 (by rfl) ⟨1729871, by rfl⟩ : syracuseStep 2306495 = 3459743) B3459743
theorem B2732543 : Blo 1821612 2732543 := bstep (se 1 (by rfl) ⟨2049407, by rfl⟩ : syracuseStep 2732543 = 4098815) B4098815
theorem B1823323 : Blo 1821612 1823323 := bstep (se 1 (by rfl) ⟨1367492, by rfl⟩ : syracuseStep 1823323 = 2734985) B2734985
theorem B8754169 : Blo 1821612 8754169 := bstep (se 2 (by rfl) ⟨3282813, by rfl⟩ : syracuseStep 8754169 = 6565627) B6565627
theorem B7386137 : Blo 1821612 7386137 := bstep (se 2 (by rfl) ⟨2769801, by rfl⟩ : syracuseStep 7386137 = 5539603) B5539603
theorem B4101191 : Blo 1821612 4101191 := bstep (se 1 (by rfl) ⟨3075893, by rfl⟩ : syracuseStep 4101191 = 6151787) B6151787
theorem B2733167 : Blo 1821612 2733167 := bstep (se 1 (by rfl) ⟨2049875, by rfl⟩ : syracuseStep 2733167 = 4099751) B4099751
theorem B2733359 : Blo 1821612 2733359 := bstep (se 1 (by rfl) ⟨2050019, by rfl⟩ : syracuseStep 2733359 = 4100039) B4100039
theorem B4380007 : Blo 1821612 4380007 := bstep (se 1 (by rfl) ⟨3285005, by rfl⟩ : syracuseStep 4380007 = 6570011) B6570011
theorem B6919607 : Blo 1821612 6919607 := bstep (se 1 (by rfl) ⟨5189705, by rfl⟩ : syracuseStep 6919607 = 10379411) B10379411
theorem B9983507 : Blo 1821612 9983507 := bstep (se 1 (by rfl) ⟨7487630, by rfl⟩ : syracuseStep 9983507 = 14975261) B14975261
theorem B2733599 : Blo 1821612 2733599 := bstep (se 1 (by rfl) ⟨2050199, by rfl⟩ : syracuseStep 2733599 = 4100399) B4100399
theorem B10384969 : Blo 1821612 10384969 := bstep (se 2 (by rfl) ⟨3894363, by rfl⟩ : syracuseStep 10384969 = 7788727) B7788727
theorem B2733743 : Blo 1821612 2733743 := bstep (se 1 (by rfl) ⟨2050307, by rfl⟩ : syracuseStep 2733743 = 4100615) B4100615
theorem B9230111 : Blo 1821612 9230111 := bstep (se 1 (by rfl) ⟨6922583, by rfl⟩ : syracuseStep 9230111 = 13845167) B13845167
theorem B2734247 : Blo 1821612 2734247 := bstep (se 1 (by rfl) ⟨2050685, by rfl⟩ : syracuseStep 2734247 = 4101371) B4101371
theorem B2734391 : Blo 1821612 2734391 := bstep (se 1 (by rfl) ⟨2050793, by rfl⟩ : syracuseStep 2734391 = 4101587) B4101587
theorem B8755553 : Blo 1821612 8755553 := bstep (se 2 (by rfl) ⟨3283332, by rfl⟩ : syracuseStep 8755553 = 6566665) B6566665
theorem B2734463 : Blo 1821612 2734463 := bstep (se 1 (by rfl) ⟨2050847, by rfl⟩ : syracuseStep 2734463 = 4101695) B4101695
theorem B10385927 : Blo 1821612 10385927 := bstep (se 1 (by rfl) ⟨7789445, by rfl⟩ : syracuseStep 10385927 = 15578891) B15578891
theorem B59955785 : Blo 1821612 59955785 := bstep (se 2 (by rfl) ⟨22483419, by rfl⟩ : syracuseStep 59955785 = 44966839) B44966839
theorem B4102739 : Blo 1821612 4102739 := bstep (se 1 (by rfl) ⟨3077054, by rfl⟩ : syracuseStep 4102739 = 6154109) B6154109
theorem B4102847 : Blo 1821612 4102847 := bstep (se 1 (by rfl) ⟨3077135, by rfl⟩ : syracuseStep 4102847 = 6154271) B6154271
theorem B6151193 : Blo 1821612 6151193 := bstep (se 2 (by rfl) ⟨2306697, by rfl⟩ : syracuseStep 6151193 = 4613395) B4613395
theorem B2595935 : Blo 1821612 2595935 := bstep (se 1 (by rfl) ⟨1946951, by rfl⟩ : syracuseStep 2595935 = 3893903) B3893903
theorem B4611239 : Blo 1821612 4611239 := bstep (se 1 (by rfl) ⟨3458429, by rfl⟩ : syracuseStep 4611239 = 6916859) B6916859
theorem B6151355 : Blo 1821612 6151355 := bstep (se 1 (by rfl) ⟨4613516, by rfl⟩ : syracuseStep 6151355 = 9227033) B9227033
theorem B15785279 : Blo 1821612 15785279 := bstep (se 1 (by rfl) ⟨11838959, by rfl⟩ : syracuseStep 15785279 = 23677919) B23677919
theorem B12467609 : Blo 1821612 12467609 := bstep (se 2 (by rfl) ⟨4675353, by rfl⟩ : syracuseStep 12467609 = 9350707) B9350707
theorem B9223631 : Blo 1821612 9223631 := bstep (se 1 (by rfl) ⟨6917723, by rfl⟩ : syracuseStep 9223631 = 13835447) B13835447
theorem B4611775 : Blo 1821612 4611775 := bstep (se 1 (by rfl) ⟨3458831, by rfl⟩ : syracuseStep 4611775 = 6917663) B6917663
theorem B7388911 : Blo 1821612 7388911 := bstep (se 1 (by rfl) ⟨5541683, by rfl⟩ : syracuseStep 7388911 = 11083367) B11083367
theorem B4677439 : Blo 1821612 4677439 := bstep (se 1 (by rfl) ⟨3508079, by rfl⟩ : syracuseStep 4677439 = 7016159) B7016159
theorem B4611937 : Blo 1821612 4611937 := bstep (se 2 (by rfl) ⟨1729476, by rfl⟩ : syracuseStep 4611937 = 3458953) B3458953
theorem B6922493 : Blo 1821612 6922493 := bstep (se 3 (by rfl) ⟨1297967, by rfl⟩ : syracuseStep 6922493 = 2595935) B2595935
theorem B4924091 : Blo 1821612 4924091 := bstep (se 1 (by rfl) ⟨3693068, by rfl⟩ : syracuseStep 4924091 = 7386137) B7386137
theorem B145884017 : Blo 1821612 145884017 := bstep (se 2 (by rfl) ⟨54706506, by rfl⟩ : syracuseStep 145884017 = 109413013) B109413013
theorem B4613071 : Blo 1821612 4613071 := bstep (se 1 (by rfl) ⟨3459803, by rfl⟩ : syracuseStep 4613071 = 6919607) B6919607
theorem B6153407 : Blo 1821612 6153407 := bstep (se 1 (by rfl) ⟨4615055, by rfl⟩ : syracuseStep 6153407 = 9230111) B9230111
theorem B15787493 : Blo 1821612 15787493 := bstep (se 4 (by rfl) ⟨1480077, by rfl⟩ : syracuseStep 15787493 = 2960155) B2960155
theorem B6923951 : Blo 1821612 6923951 := bstep (se 1 (by rfl) ⟨5192963, by rfl⟩ : syracuseStep 6923951 = 10385927) B10385927
theorem B39970523 : Blo 1821612 39970523 := bstep (se 1 (by rfl) ⟨29977892, by rfl⟩ : syracuseStep 39970523 = 59955785) B59955785
theorem B2918377 : Blo 1821612 2918377 := bstep (se 2 (by rfl) ⟨1094391, by rfl⟩ : syracuseStep 2918377 = 2188783) B2188783
theorem B4614185 : Blo 1821612 4614185 := bstep (se 2 (by rfl) ⟨1730319, by rfl⟩ : syracuseStep 4614185 = 3460639) B3460639
theorem B13846625 : Blo 1821612 13846625 := bstep (se 2 (by rfl) ⟨5192484, by rfl⟩ : syracuseStep 13846625 = 10384969) B10384969
theorem B3074159 : Blo 1821612 3074159 := bstep (se 1 (by rfl) ⟨2305619, by rfl⟩ : syracuseStep 3074159 = 4611239) B4611239
theorem B29558945 : Blo 1821612 29558945 := bstep (se 2 (by rfl) ⟨11084604, by rfl⟩ : syracuseStep 29558945 = 22169209) B22169209
theorem B6236585 : Blo 1821612 6236585 := bstep (se 2 (by rfl) ⟨2338719, by rfl⟩ : syracuseStep 6236585 = 4677439) B4677439
theorem B23349779 : Blo 1821612 23349779 := bstep (se 1 (by rfl) ⟨17512334, by rfl⟩ : syracuseStep 23349779 = 35024669) B35024669
theorem B4615127 : Blo 1821612 4615127 := bstep (se 1 (by rfl) ⟨3461345, by rfl⟩ : syracuseStep 4615127 = 6922691) B6922691
theorem B1821695 : Blo 1821612 1821695 := bstep (se 1 (by rfl) ⟨1366271, by rfl⟩ : syracuseStep 1821695 = 2732543) B2732543
theorem B4615177 : Blo 1821612 4615177 := bstep (se 2 (by rfl) ⟨1730691, by rfl⟩ : syracuseStep 4615177 = 3461383) B3461383
theorem B6917345 : Blo 1821612 6917345 := bstep (se 2 (by rfl) ⟨2594004, by rfl⟩ : syracuseStep 6917345 = 5188009) B5188009
theorem B1822111 : Blo 1821612 1822111 := bstep (se 1 (by rfl) ⟨1366583, by rfl⟩ : syracuseStep 1822111 = 2733167) B2733167
theorem B1822239 : Blo 1821612 1822239 := bstep (se 1 (by rfl) ⟨1366679, by rfl⟩ : syracuseStep 1822239 = 2733359) B2733359
theorem B4099625 : Blo 1821612 4099625 := bstep (se 2 (by rfl) ⟨1537359, by rfl⟩ : syracuseStep 4099625 = 3074719) B3074719
theorem B1822399 : Blo 1821612 1822399 := bstep (se 1 (by rfl) ⟨1366799, by rfl⟩ : syracuseStep 1822399 = 2733599) B2733599
theorem B1822495 : Blo 1821612 1822495 := bstep (se 1 (by rfl) ⟨1366871, by rfl⟩ : syracuseStep 1822495 = 2733743) B2733743
theorem B6238183 : Blo 1821612 6238183 := bstep (se 1 (by rfl) ⟨4678637, by rfl⟩ : syracuseStep 6238183 = 9357275) B9357275
theorem B1822831 : Blo 1821612 1822831 := bstep (se 1 (by rfl) ⟨1367123, by rfl⟩ : syracuseStep 1822831 = 2734247) B2734247
theorem B1822927 : Blo 1821612 1822927 := bstep (se 1 (by rfl) ⟨1367195, by rfl⟩ : syracuseStep 1822927 = 2734391) B2734391
theorem B5837035 : Blo 1821612 5837035 := bstep (se 1 (by rfl) ⟨4377776, by rfl⟩ : syracuseStep 5837035 = 8755553) B8755553
theorem B4100345 : Blo 1821612 4100345 := bstep (se 2 (by rfl) ⟨1537629, by rfl⟩ : syracuseStep 4100345 = 3075259) B3075259
theorem B1822975 : Blo 1821612 1822975 := bstep (se 1 (by rfl) ⟨1367231, by rfl⟩ : syracuseStep 1822975 = 2734463) B2734463
theorem B2732447 : Blo 1821612 2732447 := bstep (se 1 (by rfl) ⟨2049335, by rfl⟩ : syracuseStep 2732447 = 4098671) B4098671
theorem B4100795 : Blo 1821612 4100795 := bstep (se 1 (by rfl) ⟨3075596, by rfl⟩ : syracuseStep 4100795 = 6151193) B6151193
theorem B23360237 : Blo 1821612 23360237 := bstep (se 3 (by rfl) ⟨4380044, by rfl⟩ : syracuseStep 23360237 = 8760089) B8760089
theorem B4100903 : Blo 1821612 4100903 := bstep (se 1 (by rfl) ⟨3075677, by rfl⟩ : syracuseStep 4100903 = 6151355) B6151355
theorem B23720795 : Blo 1821612 23720795 := bstep (se 1 (by rfl) ⟨17790596, by rfl⟩ : syracuseStep 23720795 = 35581193) B35581193
theorem B2732921 : Blo 1821612 2732921 := bstep (se 2 (by rfl) ⟨1024845, by rfl⟩ : syracuseStep 2732921 = 2049691) B2049691
theorem B3076987 : Blo 1821612 3076987 := bstep (se 1 (by rfl) ⟨2307740, by rfl⟩ : syracuseStep 3076987 = 4615481) B4615481
theorem B10523519 : Blo 1821612 10523519 := bstep (se 1 (by rfl) ⟨7892639, by rfl⟩ : syracuseStep 10523519 = 15785279) B15785279
theorem B6149033 : Blo 1821612 6149033 := bstep (se 2 (by rfl) ⟨2305887, by rfl⟩ : syracuseStep 6149033 = 4611775) B4611775
theorem B8311739 : Blo 1821612 8311739 := bstep (se 1 (by rfl) ⟨6233804, by rfl⟩ : syracuseStep 8311739 = 12467609) B12467609
theorem B6149087 : Blo 1821612 6149087 := bstep (se 1 (by rfl) ⟨4611815, by rfl⟩ : syracuseStep 6149087 = 9223631) B9223631
theorem B9851881 : Blo 1821612 9851881 := bstep (se 2 (by rfl) ⟨3694455, by rfl⟩ : syracuseStep 9851881 = 7388911) B7388911
theorem B2307199 : Blo 1821612 2307199 := bstep (se 1 (by rfl) ⟨1730399, by rfl⟩ : syracuseStep 2307199 = 3460799) B3460799
theorem B6149249 : Blo 1821612 6149249 := bstep (se 2 (by rfl) ⟨2305968, by rfl⟩ : syracuseStep 6149249 = 4611937) B4611937
theorem B2733503 : Blo 1821612 2733503 := bstep (se 1 (by rfl) ⟨2050127, by rfl⟩ : syracuseStep 2733503 = 4100255) B4100255
theorem B7386719 : Blo 1821612 7386719 := bstep (se 1 (by rfl) ⟨5540039, by rfl⟩ : syracuseStep 7386719 = 11080079) B11080079
theorem B6919775 : Blo 1821612 6919775 := bstep (se 1 (by rfl) ⟨5189831, by rfl⟩ : syracuseStep 6919775 = 10379663) B10379663
theorem B9229949 : Blo 1821612 9229949 := bstep (se 3 (by rfl) ⟨1730615, by rfl⟩ : syracuseStep 9229949 = 3461231) B3461231
theorem B4101839 : Blo 1821612 4101839 := bstep (se 1 (by rfl) ⟨3076379, by rfl⟩ : syracuseStep 4101839 = 6152759) B6152759
theorem B4101857 : Blo 1821612 4101857 := bstep (se 2 (by rfl) ⟨1538196, by rfl⟩ : syracuseStep 4101857 = 3076393) B3076393
theorem B2733833 : Blo 1821612 2733833 := bstep (se 2 (by rfl) ⟨1025187, by rfl⟩ : syracuseStep 2733833 = 2050375) B2050375
theorem B3282923 : Blo 1821612 3282923 := bstep (se 1 (by rfl) ⟨2462192, by rfl⟩ : syracuseStep 3282923 = 4924385) B4924385
theorem B7788575 : Blo 1821612 7788575 := bstep (se 1 (by rfl) ⟨5841431, by rfl⟩ : syracuseStep 7788575 = 11682863) B11682863
theorem B2734127 : Blo 1821612 2734127 := bstep (se 1 (by rfl) ⟨2050595, by rfl⟩ : syracuseStep 2734127 = 4101191) B4101191
theorem B6150653 : Blo 1821612 6150653 := bstep (se 3 (by rfl) ⟨1153247, by rfl⟩ : syracuseStep 6150653 = 2306495) B2306495
theorem B6150815 : Blo 1821612 6150815 := bstep (se 1 (by rfl) ⟨4613111, by rfl⟩ : syracuseStep 6150815 = 9226223) B9226223
theorem B11672225 : Blo 1821612 11672225 := bstep (se 2 (by rfl) ⟨4377084, by rfl⟩ : syracuseStep 11672225 = 8754169) B8754169
theorem B26622685 : Blo 1821612 26622685 := bstep (se 3 (by rfl) ⟨4991753, by rfl⟩ : syracuseStep 26622685 = 9983507) B9983507
theorem B2735159 : Blo 1821612 2735159 := bstep (se 1 (by rfl) ⟨2051369, by rfl⟩ : syracuseStep 2735159 = 4102739) B4102739
theorem B2735231 : Blo 1821612 2735231 := bstep (se 1 (by rfl) ⟨2051423, by rfl⟩ : syracuseStep 2735231 = 4102847) B4102847
theorem B5840009 : Blo 1821612 5840009 := bstep (se 2 (by rfl) ⟨2190003, by rfl⟩ : syracuseStep 5840009 = 4380007) B4380007
theorem B5192873 : Blo 1821612 5192873 := bstep (se 2 (by rfl) ⟨1947327, by rfl⟩ : syracuseStep 5192873 = 3894655) B3894655
theorem B21045181 : Blo 1821612 21045181 := bstep (se 3 (by rfl) ⟨3945971, by rfl⟩ : syracuseStep 21045181 = 7891943) B7891943
theorem B17522639 : Blo 1821612 17522639 := bstep (se 1 (by rfl) ⟨13141979, by rfl⟩ : syracuseStep 17522639 = 26283959) B26283959
theorem B7782713 : Blo 1821612 7782713 := bstep (se 2 (by rfl) ⟨2918517, by rfl⟩ : syracuseStep 7782713 = 5837035) B5837035
theorem B78823853 : Blo 1821612 78823853 := bstep (se 3 (by rfl) ⟨14779472, by rfl⟩ : syracuseStep 78823853 = 29558945) B29558945
theorem B15573491 : Blo 1821612 15573491 := bstep (se 1 (by rfl) ⟨11680118, by rfl⟩ : syracuseStep 15573491 = 23360237) B23360237
theorem B97256011 : Blo 1821612 97256011 := bstep (se 1 (by rfl) ⟨72942008, by rfl⟩ : syracuseStep 97256011 = 145884017) B145884017
theorem B35496913 : Blo 1821612 35496913 := bstep (se 2 (by rfl) ⟨13311342, by rfl⟩ : syracuseStep 35496913 = 26622685) B26622685
theorem B4613183 : Blo 1821612 4613183 := bstep (se 1 (by rfl) ⟨3459887, by rfl⟩ : syracuseStep 4613183 = 6919775) B6919775
theorem B6153299 : Blo 1821612 6153299 := bstep (se 1 (by rfl) ⟨4614974, by rfl⟩ : syracuseStep 6153299 = 9229949) B9229949
theorem B2188615 : Blo 1821612 2188615 := bstep (se 1 (by rfl) ⟨1641461, by rfl⟩ : syracuseStep 2188615 = 3282923) B3282923
theorem B6153569 : Blo 1821612 6153569 := bstep (se 2 (by rfl) ⟨2307588, by rfl⟩ : syracuseStep 6153569 = 4615177) B4615177
theorem B2049439 : Blo 1821612 2049439 := bstep (se 1 (by rfl) ⟨1537079, by rfl⟩ : syracuseStep 2049439 = 3074159) B3074159
theorem B15566519 : Blo 1821612 15566519 := bstep (se 1 (by rfl) ⟨11674889, by rfl⟩ : syracuseStep 15566519 = 23349779) B23349779
theorem B106588061 : Blo 1821612 106588061 := bstep (se 3 (by rfl) ⟨19985261, by rfl⟩ : syracuseStep 106588061 = 39970523) B39970523
theorem B3893339 : Blo 1821612 3893339 := bstep (se 1 (by rfl) ⟨2920004, by rfl⟩ : syracuseStep 3893339 = 5840009) B5840009
theorem B28060241 : Blo 1821612 28060241 := bstep (se 2 (by rfl) ⟨10522590, by rfl⟩ : syracuseStep 28060241 = 21045181) B21045181
theorem B8317577 : Blo 1821612 8317577 := bstep (se 2 (by rfl) ⟨3119091, by rfl⟩ : syracuseStep 8317577 = 6238183) B6238183
theorem B4614995 : Blo 1821612 4614995 := bstep (se 1 (by rfl) ⟨3461246, by rfl⟩ : syracuseStep 4614995 = 6922493) B6922493
theorem B1821631 : Blo 1821612 1821631 := bstep (se 1 (by rfl) ⟨1366223, by rfl⟩ : syracuseStep 1821631 = 2732447) B2732447
theorem B15813863 : Blo 1821612 15813863 := bstep (se 1 (by rfl) ⟨11860397, by rfl⟩ : syracuseStep 15813863 = 23720795) B23720795
theorem B1821947 : Blo 1821612 1821947 := bstep (se 1 (by rfl) ⟨1366460, by rfl⟩ : syracuseStep 1821947 = 2732921) B2732921
theorem B7015679 : Blo 1821612 7015679 := bstep (se 1 (by rfl) ⟨5261759, by rfl⟩ : syracuseStep 7015679 = 10523519) B10523519
theorem B4099355 : Blo 1821612 4099355 := bstep (se 1 (by rfl) ⟨3074516, by rfl⟩ : syracuseStep 4099355 = 6149033) B6149033
theorem B4099391 : Blo 1821612 4099391 := bstep (se 1 (by rfl) ⟨3074543, by rfl⟩ : syracuseStep 4099391 = 6149087) B6149087
theorem B4099499 : Blo 1821612 4099499 := bstep (se 1 (by rfl) ⟨3074624, by rfl⟩ : syracuseStep 4099499 = 6149249) B6149249
theorem B1822335 : Blo 1821612 1822335 := bstep (se 1 (by rfl) ⟨1366751, by rfl⟩ : syracuseStep 1822335 = 2733503) B2733503
theorem B4615967 : Blo 1821612 4615967 := bstep (se 1 (by rfl) ⟨3461975, by rfl⟩ : syracuseStep 4615967 = 6923951) B6923951
theorem B1822555 : Blo 1821612 1822555 := bstep (se 1 (by rfl) ⟨1366916, by rfl⟩ : syracuseStep 1822555 = 2733833) B2733833
theorem B13135841 : Blo 1821612 13135841 := bstep (se 2 (by rfl) ⟨4925940, by rfl⟩ : syracuseStep 13135841 = 9851881) B9851881
theorem B3076123 : Blo 1821612 3076123 := bstep (se 1 (by rfl) ⟨2307092, by rfl⟩ : syracuseStep 3076123 = 4614185) B4614185
theorem B1822751 : Blo 1821612 1822751 := bstep (se 1 (by rfl) ⟨1367063, by rfl⟩ : syracuseStep 1822751 = 2734127) B2734127
theorem B3076265 : Blo 1821612 3076265 := bstep (se 2 (by rfl) ⟨1153599, by rfl⟩ : syracuseStep 3076265 = 2307199) B2307199
theorem B19697917 : Blo 1821612 19697917 := bstep (se 3 (by rfl) ⟨3693359, by rfl⟩ : syracuseStep 19697917 = 7386719) B7386719
theorem B4157723 : Blo 1821612 4157723 := bstep (se 1 (by rfl) ⟨3118292, by rfl⟩ : syracuseStep 4157723 = 6236585) B6236585
theorem B4100435 : Blo 1821612 4100435 := bstep (se 1 (by rfl) ⟨3075326, by rfl⟩ : syracuseStep 4100435 = 6150653) B6150653
theorem B4100543 : Blo 1821612 4100543 := bstep (se 1 (by rfl) ⟨3075407, by rfl⟩ : syracuseStep 4100543 = 6150815) B6150815
theorem B3076751 : Blo 1821612 3076751 := bstep (se 1 (by rfl) ⟨2307563, by rfl⟩ : syracuseStep 3076751 = 4615127) B4615127
theorem B1823439 : Blo 1821612 1823439 := bstep (se 1 (by rfl) ⟨1367579, by rfl⟩ : syracuseStep 1823439 = 2735159) B2735159
theorem B1823487 : Blo 1821612 1823487 := bstep (se 1 (by rfl) ⟨1367615, by rfl⟩ : syracuseStep 1823487 = 2735231) B2735231
theorem B3461915 : Blo 1821612 3461915 := bstep (se 1 (by rfl) ⟨2596436, by rfl⟩ : syracuseStep 3461915 = 5192873) B5192873
theorem B2733083 : Blo 1821612 2733083 := bstep (se 1 (by rfl) ⟨2049812, by rfl⟩ : syracuseStep 2733083 = 4099625) B4099625
theorem B22164637 : Blo 1821612 22164637 := bstep (se 3 (by rfl) ⟨4155869, by rfl⟩ : syracuseStep 22164637 = 8311739) B8311739
theorem B2733563 : Blo 1821612 2733563 := bstep (se 1 (by rfl) ⟨2050172, by rfl⟩ : syracuseStep 2733563 = 4100345) B4100345
theorem B2733863 : Blo 1821612 2733863 := bstep (se 1 (by rfl) ⟨2050397, by rfl⟩ : syracuseStep 2733863 = 4100795) B4100795
theorem B2733935 : Blo 1821612 2733935 := bstep (se 1 (by rfl) ⟨2050451, by rfl⟩ : syracuseStep 2733935 = 4100903) B4100903
theorem B4102271 : Blo 1821612 4102271 := bstep (se 1 (by rfl) ⟨3076703, by rfl⟩ : syracuseStep 4102271 = 6153407) B6153407
theorem B10524995 : Blo 1821612 10524995 := bstep (se 1 (by rfl) ⟨7893746, by rfl⟩ : syracuseStep 10524995 = 15787493) B15787493
theorem B2734559 : Blo 1821612 2734559 := bstep (se 1 (by rfl) ⟨2050919, by rfl⟩ : syracuseStep 2734559 = 4101839) B4101839
theorem B2734571 : Blo 1821612 2734571 := bstep (se 1 (by rfl) ⟨2050928, by rfl⟩ : syracuseStep 2734571 = 4101857) B4101857
theorem B4102649 : Blo 1821612 4102649 := bstep (se 2 (by rfl) ⟨1538493, by rfl⟩ : syracuseStep 4102649 = 3076987) B3076987
theorem B6150761 : Blo 1821612 6150761 := bstep (se 2 (by rfl) ⟨2306535, by rfl⟩ : syracuseStep 6150761 = 4613071) B4613071
theorem B5192383 : Blo 1821612 5192383 := bstep (se 1 (by rfl) ⟨3894287, by rfl⟩ : syracuseStep 5192383 = 7788575) B7788575
theorem B9231083 : Blo 1821612 9231083 := bstep (se 1 (by rfl) ⟨6923312, by rfl⟩ : syracuseStep 9231083 = 13846625) B13846625
theorem B7781483 : Blo 1821612 7781483 := bstep (se 1 (by rfl) ⟨5836112, by rfl⟩ : syracuseStep 7781483 = 11672225) B11672225
theorem B13130909 : Blo 1821612 13130909 := bstep (se 3 (by rfl) ⟨2462045, by rfl⟩ : syracuseStep 13130909 = 4924091) B4924091
theorem B4611563 : Blo 1821612 4611563 := bstep (se 1 (by rfl) ⟨3458672, by rfl⟩ : syracuseStep 4611563 = 6917345) B6917345
theorem B11681759 : Blo 1821612 11681759 := bstep (se 1 (by rfl) ⟨8761319, by rfl⟩ : syracuseStep 11681759 = 17522639) B17522639
theorem B3891169 : Blo 1821612 3891169 := bstep (se 2 (by rfl) ⟨1459188, by rfl⟩ : syracuseStep 3891169 = 2918377) B2918377
theorem B26263889 : Blo 1821612 26263889 := bstep (se 2 (by rfl) ⟨9848958, by rfl⟩ : syracuseStep 26263889 = 19697917) B19697917
theorem B6923177 : Blo 1821612 6923177 := bstep (se 2 (by rfl) ⟨2596191, by rfl⟩ : syracuseStep 6923177 = 5192383) B5192383
theorem B71058707 : Blo 1821612 71058707 := bstep (se 1 (by rfl) ⟨53294030, by rfl⟩ : syracuseStep 71058707 = 106588061) B106588061
theorem B74827309 : Blo 1821612 74827309 := bstep (se 3 (by rfl) ⟨14030120, by rfl⟩ : syracuseStep 74827309 = 28060241) B28060241
theorem B2918153 : Blo 1821612 2918153 := bstep (se 2 (by rfl) ⟨1094307, by rfl⟩ : syracuseStep 2918153 = 2188615) B2188615
theorem B6154055 : Blo 1821612 6154055 := bstep (se 1 (by rfl) ⟨4615541, by rfl⟩ : syracuseStep 6154055 = 9231083) B9231083
theorem B5187655 : Blo 1821612 5187655 := bstep (se 1 (by rfl) ⟨3890741, by rfl⟩ : syracuseStep 5187655 = 7781483) B7781483
theorem B3074375 : Blo 1821612 3074375 := bstep (se 1 (by rfl) ⟨2305781, by rfl⟩ : syracuseStep 3074375 = 4611563) B4611563
theorem B5188225 : Blo 1821612 5188225 := bstep (se 2 (by rfl) ⟨1945584, by rfl⟩ : syracuseStep 5188225 = 3891169) B3891169
theorem B2050843 : Blo 1821612 2050843 := bstep (se 1 (by rfl) ⟨1538132, by rfl⟩ : syracuseStep 2050843 = 3076265) B3076265
theorem B2771815 : Blo 1821612 2771815 := bstep (se 1 (by rfl) ⟨2078861, by rfl⟩ : syracuseStep 2771815 = 4157723) B4157723
theorem B5188475 : Blo 1821612 5188475 := bstep (se 1 (by rfl) ⟨3891356, by rfl⟩ : syracuseStep 5188475 = 7782713) B7782713
theorem B10382327 : Blo 1821612 10382327 := bstep (se 1 (by rfl) ⟨7786745, by rfl⟩ : syracuseStep 10382327 = 15573491) B15573491
theorem B2051167 : Blo 1821612 2051167 := bstep (se 1 (by rfl) ⟨1538375, by rfl⟩ : syracuseStep 2051167 = 3076751) B3076751
theorem B1822055 : Blo 1821612 1822055 := bstep (se 1 (by rfl) ⟨1366541, by rfl⟩ : syracuseStep 1822055 = 2733083) B2733083
theorem B3075455 : Blo 1821612 3075455 := bstep (se 1 (by rfl) ⟨2306591, by rfl⟩ : syracuseStep 3075455 = 4613183) B4613183
theorem B129674681 : Blo 1821612 129674681 := bstep (se 2 (by rfl) ⟨48628005, by rfl⟩ : syracuseStep 129674681 = 97256011) B97256011
theorem B1822375 : Blo 1821612 1822375 := bstep (se 1 (by rfl) ⟨1366781, by rfl⟩ : syracuseStep 1822375 = 2733563) B2733563
theorem B1822575 : Blo 1821612 1822575 := bstep (se 1 (by rfl) ⟨1366931, by rfl⟩ : syracuseStep 1822575 = 2733863) B2733863
theorem B1822623 : Blo 1821612 1822623 := bstep (se 1 (by rfl) ⟨1366967, by rfl⟩ : syracuseStep 1822623 = 2733935) B2733935
theorem B47329217 : Blo 1821612 47329217 := bstep (se 2 (by rfl) ⟨17748456, by rfl⟩ : syracuseStep 47329217 = 35496913) B35496913
theorem B29552849 : Blo 1821612 29552849 := bstep (se 2 (by rfl) ⟨11082318, by rfl⟩ : syracuseStep 29552849 = 22164637) B22164637
theorem B7016663 : Blo 1821612 7016663 := bstep (se 1 (by rfl) ⟨5262497, by rfl⟩ : syracuseStep 7016663 = 10524995) B10524995
theorem B1823039 : Blo 1821612 1823039 := bstep (se 1 (by rfl) ⟨1367279, by rfl⟩ : syracuseStep 1823039 = 2734559) B2734559
theorem B1823047 : Blo 1821612 1823047 := bstep (se 1 (by rfl) ⟨1367285, by rfl⟩ : syracuseStep 1823047 = 2734571) B2734571
theorem B22180205 : Blo 1821612 22180205 := bstep (se 3 (by rfl) ⟨4158788, by rfl⟩ : syracuseStep 22180205 = 8317577) B8317577
theorem B4100507 : Blo 1821612 4100507 := bstep (se 1 (by rfl) ⟨3075380, by rfl⟩ : syracuseStep 4100507 = 6150761) B6150761
theorem B2732585 : Blo 1821612 2732585 := bstep (se 2 (by rfl) ⟨1024719, by rfl⟩ : syracuseStep 2732585 = 2049439) B2049439
theorem B3076663 : Blo 1821612 3076663 := bstep (se 1 (by rfl) ⟨2307497, by rfl⟩ : syracuseStep 3076663 = 4614995) B4614995
theorem B8753939 : Blo 1821612 8753939 := bstep (se 1 (by rfl) ⟨6565454, by rfl⟩ : syracuseStep 8753939 = 13130909) B13130909
theorem B2732903 : Blo 1821612 2732903 := bstep (se 1 (by rfl) ⟨2049677, by rfl⟩ : syracuseStep 2732903 = 4099355) B4099355
theorem B2732927 : Blo 1821612 2732927 := bstep (se 1 (by rfl) ⟨2049695, by rfl⟩ : syracuseStep 2732927 = 4099391) B4099391
theorem B2732999 : Blo 1821612 2732999 := bstep (se 1 (by rfl) ⟨2049749, by rfl⟩ : syracuseStep 2732999 = 4099499) B4099499
theorem B3077311 : Blo 1821612 3077311 := bstep (se 1 (by rfl) ⟨2307983, by rfl⟩ : syracuseStep 3077311 = 4615967) B4615967
theorem B7787839 : Blo 1821612 7787839 := bstep (se 1 (by rfl) ⟨5840879, by rfl⟩ : syracuseStep 7787839 = 11681759) B11681759
theorem B4101497 : Blo 1821612 4101497 := bstep (se 2 (by rfl) ⟨1538061, by rfl⟩ : syracuseStep 4101497 = 3076123) B3076123
theorem B2733623 : Blo 1821612 2733623 := bstep (se 1 (by rfl) ⟨2050217, by rfl⟩ : syracuseStep 2733623 = 4100435) B4100435
theorem B52549235 : Blo 1821612 52549235 := bstep (se 1 (by rfl) ⟨39411926, by rfl⟩ : syracuseStep 52549235 = 78823853) B78823853
theorem B2733695 : Blo 1821612 2733695 := bstep (se 1 (by rfl) ⟨2050271, by rfl⟩ : syracuseStep 2733695 = 4100543) B4100543
theorem B2307943 : Blo 1821612 2307943 := bstep (se 1 (by rfl) ⟨1730957, by rfl⟩ : syracuseStep 2307943 = 3461915) B3461915
theorem B4102199 : Blo 1821612 4102199 := bstep (se 1 (by rfl) ⟨3076649, by rfl⟩ : syracuseStep 4102199 = 6153299) B6153299
theorem B4102379 : Blo 1821612 4102379 := bstep (se 1 (by rfl) ⟨3076784, by rfl⟩ : syracuseStep 4102379 = 6153569) B6153569
theorem B10377679 : Blo 1821612 10377679 := bstep (se 1 (by rfl) ⟨7783259, by rfl⟩ : syracuseStep 10377679 = 15566519) B15566519
theorem B2595559 : Blo 1821612 2595559 := bstep (se 1 (by rfl) ⟨1946669, by rfl⟩ : syracuseStep 2595559 = 3893339) B3893339
theorem B2734847 : Blo 1821612 2734847 := bstep (se 1 (by rfl) ⟨2051135, by rfl⟩ : syracuseStep 2734847 = 4102271) B4102271
theorem B2735099 : Blo 1821612 2735099 := bstep (se 1 (by rfl) ⟨2051324, by rfl⟩ : syracuseStep 2735099 = 4102649) B4102649
theorem B10542575 : Blo 1821612 10542575 := bstep (se 1 (by rfl) ⟨7906931, by rfl⟩ : syracuseStep 10542575 = 15813863) B15813863
theorem B4677119 : Blo 1821612 4677119 := bstep (se 1 (by rfl) ⟨3507839, by rfl⟩ : syracuseStep 4677119 = 7015679) B7015679
theorem B8757227 : Blo 1821612 8757227 := bstep (se 1 (by rfl) ⟨6567920, by rfl⟩ : syracuseStep 8757227 = 13135841) B13135841
theorem B19701899 : Blo 1821612 19701899 := bstep (se 1 (by rfl) ⟨14776424, by rfl⟩ : syracuseStep 19701899 = 29552849) B29552849
theorem B14786803 : Blo 1821612 14786803 := bstep (se 1 (by rfl) ⟨11090102, by rfl⟩ : syracuseStep 14786803 = 22180205) B22180205
theorem B18711101 : Blo 1821612 18711101 := bstep (se 3 (by rfl) ⟨3508331, by rfl⟩ : syracuseStep 18711101 = 7016663) B7016663
theorem B13836905 : Blo 1821612 13836905 := bstep (se 2 (by rfl) ⟨5188839, by rfl⟩ : syracuseStep 13836905 = 10377679) B10377679
theorem B3695753 : Blo 1821612 3695753 := bstep (se 2 (by rfl) ⟨1385907, by rfl⟩ : syracuseStep 3695753 = 2771815) B2771815
theorem B2049583 : Blo 1821612 2049583 := bstep (se 1 (by rfl) ⟨1537187, by rfl⟩ : syracuseStep 2049583 = 3074375) B3074375
theorem B2050303 : Blo 1821612 2050303 := bstep (se 1 (by rfl) ⟨1537727, by rfl⟩ : syracuseStep 2050303 = 3075455) B3075455
theorem B6916873 : Blo 1821612 6916873 := bstep (se 2 (by rfl) ⟨2593827, by rfl⟩ : syracuseStep 6916873 = 5187655) B5187655
theorem B17509259 : Blo 1821612 17509259 := bstep (se 1 (by rfl) ⟨13131944, by rfl⟩ : syracuseStep 17509259 = 26263889) B26263889
theorem B1821723 : Blo 1821612 1821723 := bstep (se 1 (by rfl) ⟨1366292, by rfl⟩ : syracuseStep 1821723 = 2732585) B2732585
theorem B5835959 : Blo 1821612 5835959 := bstep (se 1 (by rfl) ⟨4376969, by rfl⟩ : syracuseStep 5835959 = 8753939) B8753939
theorem B1821935 : Blo 1821612 1821935 := bstep (se 1 (by rfl) ⟨1366451, by rfl⟩ : syracuseStep 1821935 = 2732903) B2732903
theorem B1821951 : Blo 1821612 1821951 := bstep (se 1 (by rfl) ⟨1366463, by rfl⟩ : syracuseStep 1821951 = 2732927) B2732927
theorem B4615451 : Blo 1821612 4615451 := bstep (se 1 (by rfl) ⟨3461588, by rfl⟩ : syracuseStep 4615451 = 6923177) B6923177
theorem B1821999 : Blo 1821612 1821999 := bstep (se 1 (by rfl) ⟨1366499, by rfl⟩ : syracuseStep 1821999 = 2732999) B2732999
theorem B6917633 : Blo 1821612 6917633 := bstep (se 2 (by rfl) ⟨2594112, by rfl⟩ : syracuseStep 6917633 = 5188225) B5188225
theorem B3460745 : Blo 1821612 3460745 := bstep (se 2 (by rfl) ⟨1297779, by rfl⟩ : syracuseStep 3460745 = 2595559) B2595559
theorem B1822415 : Blo 1821612 1822415 := bstep (se 1 (by rfl) ⟨1366811, by rfl⟩ : syracuseStep 1822415 = 2733623) B2733623
theorem B35032823 : Blo 1821612 35032823 := bstep (se 1 (by rfl) ⟨26274617, by rfl⟩ : syracuseStep 35032823 = 52549235) B52549235
theorem B1822463 : Blo 1821612 1822463 := bstep (se 1 (by rfl) ⟨1366847, by rfl⟩ : syracuseStep 1822463 = 2733695) B2733695
theorem B10383785 : Blo 1821612 10383785 := bstep (se 2 (by rfl) ⟨3893919, by rfl⟩ : syracuseStep 10383785 = 7787839) B7787839
theorem B1823231 : Blo 1821612 1823231 := bstep (se 1 (by rfl) ⟨1367423, by rfl⟩ : syracuseStep 1823231 = 2734847) B2734847
theorem B1823399 : Blo 1821612 1823399 := bstep (se 1 (by rfl) ⟨1367549, by rfl⟩ : syracuseStep 1823399 = 2735099) B2735099
theorem B3118079 : Blo 1821612 3118079 := bstep (se 1 (by rfl) ⟨2338559, by rfl⟩ : syracuseStep 3118079 = 4677119) B4677119
theorem B3077257 : Blo 1821612 3077257 := bstep (se 2 (by rfl) ⟨1153971, by rfl⟩ : syracuseStep 3077257 = 2307943) B2307943
theorem B31552811 : Blo 1821612 31552811 := bstep (se 1 (by rfl) ⟨23664608, by rfl⟩ : syracuseStep 31552811 = 47329217) B47329217
theorem B5838151 : Blo 1821612 5838151 := bstep (se 1 (by rfl) ⟨4378613, by rfl⟩ : syracuseStep 5838151 = 8757227) B8757227
theorem B2733671 : Blo 1821612 2733671 := bstep (se 1 (by rfl) ⟨2050253, by rfl⟩ : syracuseStep 2733671 = 4100507) B4100507
theorem B4102217 : Blo 1821612 4102217 := bstep (se 2 (by rfl) ⟨1538331, by rfl⟩ : syracuseStep 4102217 = 3076663) B3076663
theorem B47372471 : Blo 1821612 47372471 := bstep (se 1 (by rfl) ⟨35529353, by rfl⟩ : syracuseStep 47372471 = 71058707) B71058707
theorem B2734331 : Blo 1821612 2734331 := bstep (se 1 (by rfl) ⟨2050748, by rfl⟩ : syracuseStep 2734331 = 4101497) B4101497
theorem B2734457 : Blo 1821612 2734457 := bstep (se 2 (by rfl) ⟨1025421, by rfl⟩ : syracuseStep 2734457 = 2050843) B2050843
theorem B4102703 : Blo 1821612 4102703 := bstep (se 1 (by rfl) ⟨3077027, by rfl⟩ : syracuseStep 4102703 = 6154055) B6154055
theorem B2734799 : Blo 1821612 2734799 := bstep (se 1 (by rfl) ⟨2051099, by rfl⟩ : syracuseStep 2734799 = 4102199) B4102199
theorem B2734889 : Blo 1821612 2734889 := bstep (se 2 (by rfl) ⟨1025583, by rfl⟩ : syracuseStep 2734889 = 2051167) B2051167
theorem B2734919 : Blo 1821612 2734919 := bstep (se 1 (by rfl) ⟨2051189, by rfl⟩ : syracuseStep 2734919 = 4102379) B4102379
theorem B4103081 : Blo 1821612 4103081 := bstep (se 2 (by rfl) ⟨1538655, by rfl⟩ : syracuseStep 4103081 = 3077311) B3077311
theorem B6921551 : Blo 1821612 6921551 := bstep (se 1 (by rfl) ⟨5191163, by rfl⟩ : syracuseStep 6921551 = 10382327) B10382327
theorem B7781741 : Blo 1821612 7781741 := bstep (se 3 (by rfl) ⟨1459076, by rfl⟩ : syracuseStep 7781741 = 2918153) B2918153
theorem B99769745 : Blo 1821612 99769745 := bstep (se 2 (by rfl) ⟨37413654, by rfl⟩ : syracuseStep 99769745 = 74827309) B74827309
theorem B86449787 : Blo 1821612 86449787 := bstep (se 1 (by rfl) ⟨64837340, by rfl⟩ : syracuseStep 86449787 = 129674681) B129674681
theorem B13835933 : Blo 1821612 13835933 := bstep (se 3 (by rfl) ⟨2594237, by rfl⟩ : syracuseStep 13835933 = 5188475) B5188475
theorem B7028383 : Blo 1821612 7028383 := bstep (se 1 (by rfl) ⟨5271287, by rfl⟩ : syracuseStep 7028383 = 10542575) B10542575
theorem B6922523 : Blo 1821612 6922523 := bstep (se 1 (by rfl) ⟨5191892, by rfl⟩ : syracuseStep 6922523 = 10383785) B10383785
theorem B9855341 : Blo 1821612 9855341 := bstep (se 3 (by rfl) ⟨1847876, by rfl⟩ : syracuseStep 9855341 = 3695753) B3695753
theorem B9224603 : Blo 1821612 9224603 := bstep (se 1 (by rfl) ⟨6918452, by rfl⟩ : syracuseStep 9224603 = 13836905) B13836905
theorem B31581647 : Blo 1821612 31581647 := bstep (se 1 (by rfl) ⟨23686235, by rfl⟩ : syracuseStep 31581647 = 47372471) B47372471
theorem B7784201 : Blo 1821612 7784201 := bstep (se 2 (by rfl) ⟨2919075, by rfl⟩ : syracuseStep 7784201 = 5838151) B5838151
theorem B4614367 : Blo 1821612 4614367 := bstep (se 1 (by rfl) ⟨3460775, by rfl⟩ : syracuseStep 4614367 = 6921551) B6921551
theorem B5187827 : Blo 1821612 5187827 := bstep (se 1 (by rfl) ⟨3890870, by rfl⟩ : syracuseStep 5187827 = 7781741) B7781741
theorem B66513163 : Blo 1821612 66513163 := bstep (se 1 (by rfl) ⟨49884872, by rfl⟩ : syracuseStep 66513163 = 99769745) B99769745
theorem B57633191 : Blo 1821612 57633191 := bstep (se 1 (by rfl) ⟨43224893, by rfl⟩ : syracuseStep 57633191 = 86449787) B86449787
theorem B13134599 : Blo 1821612 13134599 := bstep (se 1 (by rfl) ⟨9850949, by rfl⟩ : syracuseStep 13134599 = 19701899) B19701899
theorem B1822447 : Blo 1821612 1822447 := bstep (se 1 (by rfl) ⟨1366835, by rfl⟩ : syracuseStep 1822447 = 2733671) B2733671
theorem B1822887 : Blo 1821612 1822887 := bstep (se 1 (by rfl) ⟨1367165, by rfl⟩ : syracuseStep 1822887 = 2734331) B2734331
theorem B1822971 : Blo 1821612 1822971 := bstep (se 1 (by rfl) ⟨1367228, by rfl⟩ : syracuseStep 1822971 = 2734457) B2734457
theorem B9228653 : Blo 1821612 9228653 := bstep (se 3 (by rfl) ⟨1730372, by rfl⟩ : syracuseStep 9228653 = 3460745) B3460745
theorem B1823199 : Blo 1821612 1823199 := bstep (se 1 (by rfl) ⟨1367399, by rfl⟩ : syracuseStep 1823199 = 2734799) B2734799
theorem B1823259 : Blo 1821612 1823259 := bstep (se 1 (by rfl) ⟨1367444, by rfl⟩ : syracuseStep 1823259 = 2734889) B2734889
theorem B1823279 : Blo 1821612 1823279 := bstep (se 1 (by rfl) ⟨1367459, by rfl⟩ : syracuseStep 1823279 = 2734919) B2734919
theorem B2732777 : Blo 1821612 2732777 := bstep (se 2 (by rfl) ⟨1024791, by rfl⟩ : syracuseStep 2732777 = 2049583) B2049583
theorem B3076967 : Blo 1821612 3076967 := bstep (se 1 (by rfl) ⟨2307725, by rfl⟩ : syracuseStep 3076967 = 4615451) B4615451
theorem B19715737 : Blo 1821612 19715737 := bstep (se 2 (by rfl) ⟨7393401, by rfl⟩ : syracuseStep 19715737 = 14786803) B14786803
theorem B2733737 : Blo 1821612 2733737 := bstep (se 2 (by rfl) ⟨1025151, by rfl⟩ : syracuseStep 2733737 = 2050303) B2050303
theorem B2078719 : Blo 1821612 2078719 := bstep (se 1 (by rfl) ⟨1559039, by rfl⟩ : syracuseStep 2078719 = 3118079) B3118079
theorem B21035207 : Blo 1821612 21035207 := bstep (se 1 (by rfl) ⟨15776405, by rfl⟩ : syracuseStep 21035207 = 31552811) B31552811
theorem B9222497 : Blo 1821612 9222497 := bstep (se 2 (by rfl) ⟨3458436, by rfl⟩ : syracuseStep 9222497 = 6916873) B6916873
theorem B2734811 : Blo 1821612 2734811 := bstep (se 1 (by rfl) ⟨2051108, by rfl⟩ : syracuseStep 2734811 = 4102217) B4102217
theorem B49896269 : Blo 1821612 49896269 := bstep (se 3 (by rfl) ⟨9355550, by rfl⟩ : syracuseStep 49896269 = 18711101) B18711101
theorem B4103009 : Blo 1821612 4103009 := bstep (se 2 (by rfl) ⟨1538628, by rfl⟩ : syracuseStep 4103009 = 3077257) B3077257
theorem B2735135 : Blo 1821612 2735135 := bstep (se 1 (by rfl) ⟨2051351, by rfl⟩ : syracuseStep 2735135 = 4102703) B4102703
theorem B11672839 : Blo 1821612 11672839 := bstep (se 1 (by rfl) ⟨8754629, by rfl⟩ : syracuseStep 11672839 = 17509259) B17509259
theorem B2735387 : Blo 1821612 2735387 := bstep (se 1 (by rfl) ⟨2051540, by rfl⟩ : syracuseStep 2735387 = 4103081) B4103081
theorem B3890639 : Blo 1821612 3890639 := bstep (se 1 (by rfl) ⟨2917979, by rfl⟩ : syracuseStep 3890639 = 5835959) B5835959
theorem B9371177 : Blo 1821612 9371177 := bstep (se 2 (by rfl) ⟨3514191, by rfl⟩ : syracuseStep 9371177 = 7028383) B7028383
theorem B4611755 : Blo 1821612 4611755 := bstep (se 1 (by rfl) ⟨3458816, by rfl⟩ : syracuseStep 4611755 = 6917633) B6917633
theorem B9223955 : Blo 1821612 9223955 := bstep (se 1 (by rfl) ⟨6917966, by rfl⟩ : syracuseStep 9223955 = 13835933) B13835933
theorem B23355215 : Blo 1821612 23355215 := bstep (se 1 (by rfl) ⟨17516411, by rfl⟩ : syracuseStep 23355215 = 35032823) B35032823
theorem B6152435 : Blo 1821612 6152435 := bstep (se 1 (by rfl) ⟨4614326, by rfl⟩ : syracuseStep 6152435 = 9228653) B9228653
theorem B6570227 : Blo 1821612 6570227 := bstep (se 1 (by rfl) ⟨4927670, by rfl⟩ : syracuseStep 6570227 = 9855341) B9855341
theorem B6152489 : Blo 1821612 6152489 := bstep (se 2 (by rfl) ⟨2307183, by rfl⟩ : syracuseStep 6152489 = 4614367) B4614367
theorem B21054431 : Blo 1821612 21054431 := bstep (se 1 (by rfl) ⟨15790823, by rfl⟩ : syracuseStep 21054431 = 31581647) B31581647
theorem B3458551 : Blo 1821612 3458551 := bstep (se 1 (by rfl) ⟨2593913, by rfl⟩ : syracuseStep 3458551 = 5187827) B5187827
theorem B38422127 : Blo 1821612 38422127 := bstep (se 1 (by rfl) ⟨28816595, by rfl⟩ : syracuseStep 38422127 = 57633191) B57633191
theorem B3074503 : Blo 1821612 3074503 := bstep (se 1 (by rfl) ⟨2305877, by rfl⟩ : syracuseStep 3074503 = 4611755) B4611755
theorem B44346005 : Blo 1821612 44346005 := bstep (se 6 (by rfl) ⟨1039359, by rfl⟩ : syracuseStep 44346005 = 2078719) B2078719
theorem B4615015 : Blo 1821612 4615015 := bstep (se 1 (by rfl) ⟨3461261, by rfl⟩ : syracuseStep 4615015 = 6922523) B6922523
theorem B1821851 : Blo 1821612 1821851 := bstep (se 1 (by rfl) ⟨1366388, by rfl⟩ : syracuseStep 1821851 = 2732777) B2732777
theorem B56093885 : Blo 1821612 56093885 := bstep (se 3 (by rfl) ⟨10517603, by rfl⟩ : syracuseStep 56093885 = 21035207) B21035207
theorem B2051311 : Blo 1821612 2051311 := bstep (se 1 (by rfl) ⟨1538483, by rfl⟩ : syracuseStep 2051311 = 3076967) B3076967
theorem B1822491 : Blo 1821612 1822491 := bstep (se 1 (by rfl) ⟨1366868, by rfl⟩ : syracuseStep 1822491 = 2733737) B2733737
theorem B5189467 : Blo 1821612 5189467 := bstep (se 1 (by rfl) ⟨3892100, by rfl⟩ : syracuseStep 5189467 = 7784201) B7784201
theorem B10375037 : Blo 1821612 10375037 := bstep (se 3 (by rfl) ⟨1945319, by rfl⟩ : syracuseStep 10375037 = 3890639) B3890639
theorem B6148331 : Blo 1821612 6148331 := bstep (se 1 (by rfl) ⟨4611248, by rfl⟩ : syracuseStep 6148331 = 9222497) B9222497
theorem B1823207 : Blo 1821612 1823207 := bstep (se 1 (by rfl) ⟨1367405, by rfl⟩ : syracuseStep 1823207 = 2734811) B2734811
theorem B33264179 : Blo 1821612 33264179 := bstep (se 1 (by rfl) ⟨24948134, by rfl⟩ : syracuseStep 33264179 = 49896269) B49896269
theorem B1823423 : Blo 1821612 1823423 := bstep (se 1 (by rfl) ⟨1367567, by rfl⟩ : syracuseStep 1823423 = 2735135) B2735135
theorem B1823591 : Blo 1821612 1823591 := bstep (se 1 (by rfl) ⟨1367693, by rfl⟩ : syracuseStep 1823591 = 2735387) B2735387
theorem B6247451 : Blo 1821612 6247451 := bstep (se 1 (by rfl) ⟨4685588, by rfl⟩ : syracuseStep 6247451 = 9371177) B9371177
theorem B6149303 : Blo 1821612 6149303 := bstep (se 1 (by rfl) ⟨4611977, by rfl⟩ : syracuseStep 6149303 = 9223955) B9223955
theorem B15570143 : Blo 1821612 15570143 := bstep (se 1 (by rfl) ⟨11677607, by rfl⟩ : syracuseStep 15570143 = 23355215) B23355215
theorem B6149735 : Blo 1821612 6149735 := bstep (se 1 (by rfl) ⟨4612301, by rfl⟩ : syracuseStep 6149735 = 9224603) B9224603
theorem B88684217 : Blo 1821612 88684217 := bstep (se 2 (by rfl) ⟨33256581, by rfl⟩ : syracuseStep 88684217 = 66513163) B66513163
theorem B15563785 : Blo 1821612 15563785 := bstep (se 2 (by rfl) ⟨5836419, by rfl⟩ : syracuseStep 15563785 = 11672839) B11672839
theorem B8756399 : Blo 1821612 8756399 := bstep (se 1 (by rfl) ⟨6567299, by rfl⟩ : syracuseStep 8756399 = 13134599) B13134599
theorem B2735339 : Blo 1821612 2735339 := bstep (se 1 (by rfl) ⟨2051504, by rfl⟩ : syracuseStep 2735339 = 4103009) B4103009
theorem B26287649 : Blo 1821612 26287649 := bstep (se 2 (by rfl) ⟨9857868, by rfl⟩ : syracuseStep 26287649 = 19715737) B19715737
theorem B22176119 : Blo 1821612 22176119 := bstep (se 1 (by rfl) ⟨16632089, by rfl⟩ : syracuseStep 22176119 = 33264179) B33264179
theorem B10380095 : Blo 1821612 10380095 := bstep (se 1 (by rfl) ⟨7785071, by rfl⟩ : syracuseStep 10380095 = 15570143) B15570143
theorem B59122811 : Blo 1821612 59122811 := bstep (se 1 (by rfl) ⟨44342108, by rfl⟩ : syracuseStep 59122811 = 88684217) B88684217
theorem B6153353 : Blo 1821612 6153353 := bstep (se 2 (by rfl) ⟨2307507, by rfl⟩ : syracuseStep 6153353 = 4615015) B4615015
theorem B20751713 : Blo 1821612 20751713 := bstep (se 2 (by rfl) ⟨7781892, by rfl⟩ : syracuseStep 20751713 = 15563785) B15563785
theorem B102459005 : Blo 1821612 102459005 := bstep (se 3 (by rfl) ⟨19211063, by rfl⟩ : syracuseStep 102459005 = 38422127) B38422127
theorem B17525099 : Blo 1821612 17525099 := bstep (se 1 (by rfl) ⟨13143824, by rfl⟩ : syracuseStep 17525099 = 26287649) B26287649
theorem B6916691 : Blo 1821612 6916691 := bstep (se 1 (by rfl) ⟨5187518, by rfl⟩ : syracuseStep 6916691 = 10375037) B10375037
theorem B4098887 : Blo 1821612 4098887 := bstep (se 1 (by rfl) ⟨3074165, by rfl⟩ : syracuseStep 4098887 = 6148331) B6148331
theorem B4099337 : Blo 1821612 4099337 := bstep (se 2 (by rfl) ⟨1537251, by rfl⟩ : syracuseStep 4099337 = 3074503) B3074503
theorem B14036287 : Blo 1821612 14036287 := bstep (se 1 (by rfl) ⟨10527215, by rfl⟩ : syracuseStep 14036287 = 21054431) B21054431
theorem B4164967 : Blo 1821612 4164967 := bstep (se 1 (by rfl) ⟨3123725, by rfl⟩ : syracuseStep 4164967 = 6247451) B6247451
theorem B4099535 : Blo 1821612 4099535 := bstep (se 1 (by rfl) ⟨3074651, by rfl⟩ : syracuseStep 4099535 = 6149303) B6149303
theorem B4099823 : Blo 1821612 4099823 := bstep (se 1 (by rfl) ⟨3074867, by rfl⟩ : syracuseStep 4099823 = 6149735) B6149735
theorem B5837599 : Blo 1821612 5837599 := bstep (se 1 (by rfl) ⟨4378199, by rfl⟩ : syracuseStep 5837599 = 8756399) B8756399
theorem B1823559 : Blo 1821612 1823559 := bstep (se 1 (by rfl) ⟨1367669, by rfl⟩ : syracuseStep 1823559 = 2735339) B2735339
theorem B6919289 : Blo 1821612 6919289 := bstep (se 2 (by rfl) ⟨2594733, by rfl⟩ : syracuseStep 6919289 = 5189467) B5189467
theorem B4101623 : Blo 1821612 4101623 := bstep (se 1 (by rfl) ⟨3076217, by rfl⟩ : syracuseStep 4101623 = 6152435) B6152435
theorem B4380151 : Blo 1821612 4380151 := bstep (se 1 (by rfl) ⟨3285113, by rfl⟩ : syracuseStep 4380151 = 6570227) B6570227
theorem B4101659 : Blo 1821612 4101659 := bstep (se 1 (by rfl) ⟨3076244, by rfl⟩ : syracuseStep 4101659 = 6152489) B6152489
theorem B2735081 : Blo 1821612 2735081 := bstep (se 2 (by rfl) ⟨1025655, by rfl⟩ : syracuseStep 2735081 = 2051311) B2051311
theorem B29564003 : Blo 1821612 29564003 := bstep (se 1 (by rfl) ⟨22173002, by rfl⟩ : syracuseStep 29564003 = 44346005) B44346005
theorem B4611401 : Blo 1821612 4611401 := bstep (se 2 (by rfl) ⟨1729275, by rfl⟩ : syracuseStep 4611401 = 3458551) B3458551
theorem B37395923 : Blo 1821612 37395923 := bstep (se 1 (by rfl) ⟨28046942, by rfl⟩ : syracuseStep 37395923 = 56093885) B56093885
theorem B4612859 : Blo 1821612 4612859 := bstep (se 1 (by rfl) ⟨3459644, by rfl⟩ : syracuseStep 4612859 = 6919289) B6919289
theorem B7783465 : Blo 1821612 7783465 := bstep (se 2 (by rfl) ⟨2918799, by rfl⟩ : syracuseStep 7783465 = 5837599) B5837599
theorem B68306003 : Blo 1821612 68306003 := bstep (se 1 (by rfl) ⟨51229502, by rfl⟩ : syracuseStep 68306003 = 102459005) B102459005
theorem B99722461 : Blo 1821612 99722461 := bstep (se 3 (by rfl) ⟨18697961, by rfl⟩ : syracuseStep 99722461 = 37395923) B37395923
theorem B11683399 : Blo 1821612 11683399 := bstep (se 1 (by rfl) ⟨8762549, by rfl⟩ : syracuseStep 11683399 = 17525099) B17525099
theorem B3074267 : Blo 1821612 3074267 := bstep (se 1 (by rfl) ⟨2305700, by rfl⟩ : syracuseStep 3074267 = 4611401) B4611401
theorem B18715049 : Blo 1821612 18715049 := bstep (se 2 (by rfl) ⟨7018143, by rfl⟩ : syracuseStep 18715049 = 14036287) B14036287
theorem B2732591 : Blo 1821612 2732591 := bstep (se 1 (by rfl) ⟨2049443, by rfl⟩ : syracuseStep 2732591 = 4098887) B4098887
theorem B1823387 : Blo 1821612 1823387 := bstep (se 1 (by rfl) ⟨1367540, by rfl⟩ : syracuseStep 1823387 = 2735081) B2735081
theorem B2732891 : Blo 1821612 2732891 := bstep (se 1 (by rfl) ⟨2049668, by rfl⟩ : syracuseStep 2732891 = 4099337) B4099337
theorem B2733023 : Blo 1821612 2733023 := bstep (se 1 (by rfl) ⟨2049767, by rfl⟩ : syracuseStep 2733023 = 4099535) B4099535
theorem B2733215 : Blo 1821612 2733215 := bstep (se 1 (by rfl) ⟨2049911, by rfl⟩ : syracuseStep 2733215 = 4099823) B4099823
theorem B14784079 : Blo 1821612 14784079 := bstep (se 1 (by rfl) ⟨11088059, by rfl⟩ : syracuseStep 14784079 = 22176119) B22176119
theorem B157660829 : Blo 1821612 157660829 := bstep (se 3 (by rfl) ⟨29561405, by rfl⟩ : syracuseStep 157660829 = 59122811) B59122811
theorem B6920063 : Blo 1821612 6920063 := bstep (se 1 (by rfl) ⟨5190047, by rfl⟩ : syracuseStep 6920063 = 10380095) B10380095
theorem B4102235 : Blo 1821612 4102235 := bstep (se 1 (by rfl) ⟨3076676, by rfl⟩ : syracuseStep 4102235 = 6153353) B6153353
theorem B13834475 : Blo 1821612 13834475 := bstep (se 1 (by rfl) ⟨10375856, by rfl⟩ : syracuseStep 13834475 = 20751713) B20751713
theorem B2734415 : Blo 1821612 2734415 := bstep (se 1 (by rfl) ⟨2050811, by rfl⟩ : syracuseStep 2734415 = 4101623) B4101623
theorem B2734439 : Blo 1821612 2734439 := bstep (se 1 (by rfl) ⟨2050829, by rfl⟩ : syracuseStep 2734439 = 4101659) B4101659
theorem B4611127 : Blo 1821612 4611127 := bstep (se 1 (by rfl) ⟨3458345, by rfl⟩ : syracuseStep 4611127 = 6916691) B6916691
theorem B5553289 : Blo 1821612 5553289 := bstep (se 2 (by rfl) ⟨2082483, by rfl⟩ : syracuseStep 5553289 = 4164967) B4164967
theorem B5840201 : Blo 1821612 5840201 := bstep (se 2 (by rfl) ⟨2190075, by rfl⟩ : syracuseStep 5840201 = 4380151) B4380151
theorem B19709335 : Blo 1821612 19709335 := bstep (se 1 (by rfl) ⟨14782001, by rfl⟩ : syracuseStep 19709335 = 29564003) B29564003
theorem B12476699 : Blo 1821612 12476699 := bstep (se 1 (by rfl) ⟨9357524, by rfl⟩ : syracuseStep 12476699 = 18715049) B18715049
theorem B15573869 : Blo 1821612 15573869 := bstep (se 3 (by rfl) ⟨2920100, by rfl⟩ : syracuseStep 15573869 = 5840201) B5840201
theorem B4613375 : Blo 1821612 4613375 := bstep (se 1 (by rfl) ⟨3460031, by rfl⟩ : syracuseStep 4613375 = 6920063) B6920063
theorem B2049511 : Blo 1821612 2049511 := bstep (se 1 (by rfl) ⟨1537133, by rfl⟩ : syracuseStep 2049511 = 3074267) B3074267
theorem B19712105 : Blo 1821612 19712105 := bstep (se 2 (by rfl) ⟨7392039, by rfl⟩ : syracuseStep 19712105 = 14784079) B14784079
theorem B1821727 : Blo 1821612 1821727 := bstep (se 1 (by rfl) ⟨1366295, by rfl⟩ : syracuseStep 1821727 = 2732591) B2732591
theorem B3075239 : Blo 1821612 3075239 := bstep (se 1 (by rfl) ⟨2306429, by rfl⟩ : syracuseStep 3075239 = 4612859) B4612859
theorem B1821927 : Blo 1821612 1821927 := bstep (se 1 (by rfl) ⟨1366445, by rfl⟩ : syracuseStep 1821927 = 2732891) B2732891
theorem B1822015 : Blo 1821612 1822015 := bstep (se 1 (by rfl) ⟨1366511, by rfl⟩ : syracuseStep 1822015 = 2733023) B2733023
theorem B1822143 : Blo 1821612 1822143 := bstep (se 1 (by rfl) ⟨1366607, by rfl⟩ : syracuseStep 1822143 = 2733215) B2733215
theorem B105107219 : Blo 1821612 105107219 := bstep (se 1 (by rfl) ⟨78830414, by rfl⟩ : syracuseStep 105107219 = 157660829) B157660829
theorem B6148169 : Blo 1821612 6148169 := bstep (se 2 (by rfl) ⟨2305563, by rfl⟩ : syracuseStep 6148169 = 4611127) B4611127
theorem B1822943 : Blo 1821612 1822943 := bstep (se 1 (by rfl) ⟨1367207, by rfl⟩ : syracuseStep 1822943 = 2734415) B2734415
theorem B1822959 : Blo 1821612 1822959 := bstep (se 1 (by rfl) ⟨1367219, by rfl⟩ : syracuseStep 1822959 = 2734439) B2734439
theorem B15577865 : Blo 1821612 15577865 := bstep (se 2 (by rfl) ⟨5841699, by rfl⟩ : syracuseStep 15577865 = 11683399) B11683399
theorem B45537335 : Blo 1821612 45537335 := bstep (se 1 (by rfl) ⟨34153001, by rfl⟩ : syracuseStep 45537335 = 68306003) B68306003
theorem B10377953 : Blo 1821612 10377953 := bstep (se 2 (by rfl) ⟨3891732, by rfl⟩ : syracuseStep 10377953 = 7783465) B7783465
theorem B2734823 : Blo 1821612 2734823 := bstep (se 1 (by rfl) ⟨2051117, by rfl⟩ : syracuseStep 2734823 = 4102235) B4102235
theorem B9222983 : Blo 1821612 9222983 := bstep (se 1 (by rfl) ⟨6917237, by rfl⟩ : syracuseStep 9222983 = 13834475) B13834475
theorem B7404385 : Blo 1821612 7404385 := bstep (se 2 (by rfl) ⟨2776644, by rfl⟩ : syracuseStep 7404385 = 5553289) B5553289
theorem B132963281 : Blo 1821612 132963281 := bstep (se 2 (by rfl) ⟨49861230, by rfl⟩ : syracuseStep 132963281 = 99722461) B99722461
theorem B26279113 : Blo 1821612 26279113 := bstep (se 2 (by rfl) ⟨9854667, by rfl⟩ : syracuseStep 26279113 = 19709335) B19709335
theorem B9872513 : Blo 1821612 9872513 := bstep (se 2 (by rfl) ⟨3702192, by rfl⟩ : syracuseStep 9872513 = 7404385) B7404385
theorem B13141403 : Blo 1821612 13141403 := bstep (se 1 (by rfl) ⟨9856052, by rfl⟩ : syracuseStep 13141403 = 19712105) B19712105
theorem B35038817 : Blo 1821612 35038817 := bstep (se 2 (by rfl) ⟨13139556, by rfl⟩ : syracuseStep 35038817 = 26279113) B26279113
theorem B2050159 : Blo 1821612 2050159 := bstep (se 1 (by rfl) ⟨1537619, by rfl⟩ : syracuseStep 2050159 = 3075239) B3075239
theorem B4098779 : Blo 1821612 4098779 := bstep (se 1 (by rfl) ⟨3074084, by rfl⟩ : syracuseStep 4098779 = 6148169) B6148169
theorem B8317799 : Blo 1821612 8317799 := bstep (se 1 (by rfl) ⟨6238349, by rfl⟩ : syracuseStep 8317799 = 12476699) B12476699
theorem B10382579 : Blo 1821612 10382579 := bstep (se 1 (by rfl) ⟨7786934, by rfl⟩ : syracuseStep 10382579 = 15573869) B15573869
theorem B3075583 : Blo 1821612 3075583 := bstep (se 1 (by rfl) ⟨2306687, by rfl⟩ : syracuseStep 3075583 = 4613375) B4613375
theorem B6918635 : Blo 1821612 6918635 := bstep (se 1 (by rfl) ⟨5188976, by rfl⟩ : syracuseStep 6918635 = 10377953) B10377953
theorem B1823215 : Blo 1821612 1823215 := bstep (se 1 (by rfl) ⟨1367411, by rfl⟩ : syracuseStep 1823215 = 2734823) B2734823
theorem B6148655 : Blo 1821612 6148655 := bstep (se 1 (by rfl) ⟨4611491, by rfl⟩ : syracuseStep 6148655 = 9222983) B9222983
theorem B2732681 : Blo 1821612 2732681 := bstep (se 2 (by rfl) ⟨1024755, by rfl⟩ : syracuseStep 2732681 = 2049511) B2049511
theorem B88642187 : Blo 1821612 88642187 := bstep (se 1 (by rfl) ⟨66481640, by rfl⟩ : syracuseStep 88642187 = 132963281) B132963281
theorem B70071479 : Blo 1821612 70071479 := bstep (se 1 (by rfl) ⟨52553609, by rfl⟩ : syracuseStep 70071479 = 105107219) B105107219
theorem B10385243 : Blo 1821612 10385243 := bstep (se 1 (by rfl) ⟨7788932, by rfl⟩ : syracuseStep 10385243 = 15577865) B15577865
theorem B30358223 : Blo 1821612 30358223 := bstep (se 1 (by rfl) ⟨22768667, by rfl⟩ : syracuseStep 30358223 = 45537335) B45537335
theorem B4612423 : Blo 1821612 4612423 := bstep (se 1 (by rfl) ⟨3459317, by rfl⟩ : syracuseStep 4612423 = 6918635) B6918635
theorem B6923495 : Blo 1821612 6923495 := bstep (se 1 (by rfl) ⟨5192621, by rfl⟩ : syracuseStep 6923495 = 10385243) B10385243
theorem B4099103 : Blo 1821612 4099103 := bstep (se 1 (by rfl) ⟨3074327, by rfl⟩ : syracuseStep 4099103 = 6148655) B6148655
theorem B1821787 : Blo 1821612 1821787 := bstep (se 1 (by rfl) ⟨1366340, by rfl⟩ : syracuseStep 1821787 = 2732681) B2732681
theorem B6581675 : Blo 1821612 6581675 := bstep (se 1 (by rfl) ⟨4936256, by rfl⟩ : syracuseStep 6581675 = 9872513) B9872513
theorem B46714319 : Blo 1821612 46714319 := bstep (se 1 (by rfl) ⟨35035739, by rfl⟩ : syracuseStep 46714319 = 70071479) B70071479
theorem B8760935 : Blo 1821612 8760935 := bstep (se 1 (by rfl) ⟨6570701, by rfl⟩ : syracuseStep 8760935 = 13141403) B13141403
theorem B23359211 : Blo 1821612 23359211 := bstep (se 1 (by rfl) ⟨17519408, by rfl⟩ : syracuseStep 23359211 = 35038817) B35038817
theorem B20238815 : Blo 1821612 20238815 := bstep (se 1 (by rfl) ⟨15179111, by rfl⟩ : syracuseStep 20238815 = 30358223) B30358223
theorem B2732519 : Blo 1821612 2732519 := bstep (se 1 (by rfl) ⟨2049389, by rfl⟩ : syracuseStep 2732519 = 4098779) B4098779
theorem B4100777 : Blo 1821612 4100777 := bstep (se 2 (by rfl) ⟨1537791, by rfl⟩ : syracuseStep 4100777 = 3075583) B3075583
theorem B2733545 : Blo 1821612 2733545 := bstep (se 2 (by rfl) ⟨1025079, by rfl⟩ : syracuseStep 2733545 = 2050159) B2050159
theorem B59094791 : Blo 1821612 59094791 := bstep (se 1 (by rfl) ⟨44321093, by rfl⟩ : syracuseStep 59094791 = 88642187) B88642187
theorem B5545199 : Blo 1821612 5545199 := bstep (se 1 (by rfl) ⟨4158899, by rfl⟩ : syracuseStep 5545199 = 8317799) B8317799
theorem B6921719 : Blo 1821612 6921719 := bstep (se 1 (by rfl) ⟨5191289, by rfl⟩ : syracuseStep 6921719 = 10382579) B10382579
theorem B13492543 : Blo 1821612 13492543 := bstep (se 1 (by rfl) ⟨10119407, by rfl⟩ : syracuseStep 13492543 = 20238815) B20238815
theorem B14787197 : Blo 1821612 14787197 := bstep (se 3 (by rfl) ⟨2772599, by rfl⟩ : syracuseStep 14787197 = 5545199) B5545199
theorem B39396527 : Blo 1821612 39396527 := bstep (se 1 (by rfl) ⟨29547395, by rfl⟩ : syracuseStep 39396527 = 59094791) B59094791
theorem B4614479 : Blo 1821612 4614479 := bstep (se 1 (by rfl) ⟨3460859, by rfl⟩ : syracuseStep 4614479 = 6921719) B6921719
theorem B1821679 : Blo 1821612 1821679 := bstep (se 1 (by rfl) ⟨1366259, by rfl⟩ : syracuseStep 1821679 = 2732519) B2732519
theorem B4615663 : Blo 1821612 4615663 := bstep (se 1 (by rfl) ⟨3461747, by rfl⟩ : syracuseStep 4615663 = 6923495) B6923495
theorem B1822363 : Blo 1821612 1822363 := bstep (se 1 (by rfl) ⟨1366772, by rfl⟩ : syracuseStep 1822363 = 2733545) B2733545
theorem B2732735 : Blo 1821612 2732735 := bstep (se 1 (by rfl) ⟨2049551, by rfl⟩ : syracuseStep 2732735 = 4099103) B4099103
theorem B4387783 : Blo 1821612 4387783 := bstep (se 1 (by rfl) ⟨3290837, by rfl⟩ : syracuseStep 4387783 = 6581675) B6581675
theorem B31142879 : Blo 1821612 31142879 := bstep (se 1 (by rfl) ⟨23357159, by rfl⟩ : syracuseStep 31142879 = 46714319) B46714319
theorem B6149897 : Blo 1821612 6149897 := bstep (se 2 (by rfl) ⟨2306211, by rfl⟩ : syracuseStep 6149897 = 4612423) B4612423
theorem B2733851 : Blo 1821612 2733851 := bstep (se 1 (by rfl) ⟨2050388, by rfl⟩ : syracuseStep 2733851 = 4100777) B4100777
theorem B5840623 : Blo 1821612 5840623 := bstep (se 1 (by rfl) ⟨4380467, by rfl⟩ : syracuseStep 5840623 = 8760935) B8760935
theorem B15572807 : Blo 1821612 15572807 := bstep (se 1 (by rfl) ⟨11679605, by rfl⟩ : syracuseStep 15572807 = 23359211) B23359211
theorem B17990057 : Blo 1821612 17990057 := bstep (se 2 (by rfl) ⟨6746271, by rfl⟩ : syracuseStep 17990057 = 13492543) B13492543
theorem B26264351 : Blo 1821612 26264351 := bstep (se 1 (by rfl) ⟨19698263, by rfl⟩ : syracuseStep 26264351 = 39396527) B39396527
theorem B5850377 : Blo 1821612 5850377 := bstep (se 2 (by rfl) ⟨2193891, by rfl⟩ : syracuseStep 5850377 = 4387783) B4387783
theorem B6154217 : Blo 1821612 6154217 := bstep (se 2 (by rfl) ⟨2307831, by rfl⟩ : syracuseStep 6154217 = 4615663) B4615663
theorem B10381871 : Blo 1821612 10381871 := bstep (se 1 (by rfl) ⟨7786403, by rfl⟩ : syracuseStep 10381871 = 15572807) B15572807
theorem B9858131 : Blo 1821612 9858131 := bstep (se 1 (by rfl) ⟨7393598, by rfl⟩ : syracuseStep 9858131 = 14787197) B14787197
theorem B1821823 : Blo 1821612 1821823 := bstep (se 1 (by rfl) ⟨1366367, by rfl⟩ : syracuseStep 1821823 = 2732735) B2732735
theorem B20761919 : Blo 1821612 20761919 := bstep (se 1 (by rfl) ⟨15571439, by rfl⟩ : syracuseStep 20761919 = 31142879) B31142879
theorem B4099931 : Blo 1821612 4099931 := bstep (se 1 (by rfl) ⟨3074948, by rfl⟩ : syracuseStep 4099931 = 6149897) B6149897
theorem B1822567 : Blo 1821612 1822567 := bstep (se 1 (by rfl) ⟨1366925, by rfl⟩ : syracuseStep 1822567 = 2733851) B2733851
theorem B3076319 : Blo 1821612 3076319 := bstep (se 1 (by rfl) ⟨2307239, by rfl⟩ : syracuseStep 3076319 = 4614479) B4614479
theorem B7787497 : Blo 1821612 7787497 := bstep (se 2 (by rfl) ⟨2920311, by rfl⟩ : syracuseStep 7787497 = 5840623) B5840623
theorem B3900251 : Blo 1821612 3900251 := bstep (se 1 (by rfl) ⟨2925188, by rfl⟩ : syracuseStep 3900251 = 5850377) B5850377
theorem B47973485 : Blo 1821612 47973485 := bstep (se 3 (by rfl) ⟨8995028, by rfl⟩ : syracuseStep 47973485 = 17990057) B17990057
theorem B6572087 : Blo 1821612 6572087 := bstep (se 1 (by rfl) ⟨4929065, by rfl⟩ : syracuseStep 6572087 = 9858131) B9858131
theorem B2050879 : Blo 1821612 2050879 := bstep (se 1 (by rfl) ⟨1538159, by rfl⟩ : syracuseStep 2050879 = 3076319) B3076319
theorem B17509567 : Blo 1821612 17509567 := bstep (se 1 (by rfl) ⟨13132175, by rfl⟩ : syracuseStep 17509567 = 26264351) B26264351
theorem B10383329 : Blo 1821612 10383329 := bstep (se 2 (by rfl) ⟨3893748, by rfl⟩ : syracuseStep 10383329 = 7787497) B7787497
theorem B13841279 : Blo 1821612 13841279 := bstep (se 1 (by rfl) ⟨10380959, by rfl⟩ : syracuseStep 13841279 = 20761919) B20761919
theorem B2733287 : Blo 1821612 2733287 := bstep (se 1 (by rfl) ⟨2049965, by rfl⟩ : syracuseStep 2733287 = 4099931) B4099931
theorem B4102811 : Blo 1821612 4102811 := bstep (se 1 (by rfl) ⟨3077108, by rfl⟩ : syracuseStep 4102811 = 6154217) B6154217
theorem B6921247 : Blo 1821612 6921247 := bstep (se 1 (by rfl) ⟨5190935, by rfl⟩ : syracuseStep 6921247 = 10381871) B10381871
theorem B31982323 : Blo 1821612 31982323 := bstep (se 1 (by rfl) ⟨23986742, by rfl⟩ : syracuseStep 31982323 = 47973485) B47973485
theorem B2600167 : Blo 1821612 2600167 := bstep (se 1 (by rfl) ⟨1950125, by rfl⟩ : syracuseStep 2600167 = 3900251) B3900251
theorem B9227519 : Blo 1821612 9227519 := bstep (se 1 (by rfl) ⟨6920639, by rfl⟩ : syracuseStep 9227519 = 13841279) B13841279
theorem B1822191 : Blo 1821612 1822191 := bstep (se 1 (by rfl) ⟨1366643, by rfl⟩ : syracuseStep 1822191 = 2733287) B2733287
theorem B9228329 : Blo 1821612 9228329 := bstep (se 2 (by rfl) ⟨3460623, by rfl⟩ : syracuseStep 9228329 = 6921247) B6921247
theorem B2734505 : Blo 1821612 2734505 := bstep (se 2 (by rfl) ⟨1025439, by rfl⟩ : syracuseStep 2734505 = 2050879) B2050879
theorem B4381391 : Blo 1821612 4381391 := bstep (se 1 (by rfl) ⟨3286043, by rfl⟩ : syracuseStep 4381391 = 6572087) B6572087
theorem B23346089 : Blo 1821612 23346089 := bstep (se 2 (by rfl) ⟨8754783, by rfl⟩ : syracuseStep 23346089 = 17509567) B17509567
theorem B2735207 : Blo 1821612 2735207 := bstep (se 1 (by rfl) ⟨2051405, by rfl⟩ : syracuseStep 2735207 = 4102811) B4102811
theorem B6922219 : Blo 1821612 6922219 := bstep (se 1 (by rfl) ⟨5191664, by rfl⟩ : syracuseStep 6922219 = 10383329) B10383329
theorem B6152219 : Blo 1821612 6152219 := bstep (se 1 (by rfl) ⟨4614164, by rfl⟩ : syracuseStep 6152219 = 9228329) B9228329
theorem B3466889 : Blo 1821612 3466889 := bstep (se 2 (by rfl) ⟨1300083, by rfl⟩ : syracuseStep 3466889 = 2600167) B2600167
theorem B42643097 : Blo 1821612 42643097 := bstep (se 2 (by rfl) ⟨15991161, by rfl⟩ : syracuseStep 42643097 = 31982323) B31982323
theorem B1823003 : Blo 1821612 1823003 := bstep (se 1 (by rfl) ⟨1367252, by rfl⟩ : syracuseStep 1823003 = 2734505) B2734505
theorem B2920927 : Blo 1821612 2920927 := bstep (se 1 (by rfl) ⟨2190695, by rfl⟩ : syracuseStep 2920927 = 4381391) B4381391
theorem B1823471 : Blo 1821612 1823471 := bstep (se 1 (by rfl) ⟨1367603, by rfl⟩ : syracuseStep 1823471 = 2735207) B2735207
theorem B9229625 : Blo 1821612 9229625 := bstep (se 2 (by rfl) ⟨3461109, by rfl⟩ : syracuseStep 9229625 = 6922219) B6922219
theorem B15564059 : Blo 1821612 15564059 := bstep (se 1 (by rfl) ⟨11673044, by rfl⟩ : syracuseStep 15564059 = 23346089) B23346089
theorem B6151679 : Blo 1821612 6151679 := bstep (se 1 (by rfl) ⟨4613759, by rfl⟩ : syracuseStep 6151679 = 9227519) B9227519
theorem B6153083 : Blo 1821612 6153083 := bstep (se 1 (by rfl) ⟨4614812, by rfl⟩ : syracuseStep 6153083 = 9229625) B9229625
theorem B2311259 : Blo 1821612 2311259 := bstep (se 1 (by rfl) ⟨1733444, by rfl⟩ : syracuseStep 2311259 = 3466889) B3466889
theorem B28428731 : Blo 1821612 28428731 := bstep (se 1 (by rfl) ⟨21321548, by rfl⟩ : syracuseStep 28428731 = 42643097) B42643097
theorem B3894569 : Blo 1821612 3894569 := bstep (se 2 (by rfl) ⟨1460463, by rfl⟩ : syracuseStep 3894569 = 2920927) B2920927
theorem B10376039 : Blo 1821612 10376039 := bstep (se 1 (by rfl) ⟨7782029, by rfl⟩ : syracuseStep 10376039 = 15564059) B15564059
theorem B4101119 : Blo 1821612 4101119 := bstep (se 1 (by rfl) ⟨3075839, by rfl⟩ : syracuseStep 4101119 = 6151679) B6151679
theorem B4101479 : Blo 1821612 4101479 := bstep (se 1 (by rfl) ⟨3076109, by rfl⟩ : syracuseStep 4101479 = 6152219) B6152219
theorem B6917359 : Blo 1821612 6917359 := bstep (se 1 (by rfl) ⟨5188019, by rfl⟩ : syracuseStep 6917359 = 10376039) B10376039
theorem B24653429 : Blo 1821612 24653429 := bstep (se 5 (by rfl) ⟨1155629, by rfl⟩ : syracuseStep 24653429 = 2311259) B2311259
theorem B18952487 : Blo 1821612 18952487 := bstep (se 1 (by rfl) ⟨14214365, by rfl⟩ : syracuseStep 18952487 = 28428731) B28428731
theorem B4102055 : Blo 1821612 4102055 := bstep (se 1 (by rfl) ⟨3076541, by rfl⟩ : syracuseStep 4102055 = 6153083) B6153083
theorem B2734079 : Blo 1821612 2734079 := bstep (se 1 (by rfl) ⟨2050559, by rfl⟩ : syracuseStep 2734079 = 4101119) B4101119
theorem B2734319 : Blo 1821612 2734319 := bstep (se 1 (by rfl) ⟨2050739, by rfl⟩ : syracuseStep 2734319 = 4101479) B4101479
theorem B2596379 : Blo 1821612 2596379 := bstep (se 1 (by rfl) ⟨1947284, by rfl⟩ : syracuseStep 2596379 = 3894569) B3894569
theorem B6923677 : Blo 1821612 6923677 := bstep (se 3 (by rfl) ⟨1298189, by rfl⟩ : syracuseStep 6923677 = 2596379) B2596379
theorem B16435619 : Blo 1821612 16435619 := bstep (se 1 (by rfl) ⟨12326714, by rfl⟩ : syracuseStep 16435619 = 24653429) B24653429
theorem B12634991 : Blo 1821612 12634991 := bstep (se 1 (by rfl) ⟨9476243, by rfl⟩ : syracuseStep 12634991 = 18952487) B18952487
theorem B1822719 : Blo 1821612 1822719 := bstep (se 1 (by rfl) ⟨1367039, by rfl⟩ : syracuseStep 1822719 = 2734079) B2734079
theorem B1822879 : Blo 1821612 1822879 := bstep (se 1 (by rfl) ⟨1367159, by rfl⟩ : syracuseStep 1822879 = 2734319) B2734319
theorem B2734703 : Blo 1821612 2734703 := bstep (se 1 (by rfl) ⟨2051027, by rfl⟩ : syracuseStep 2734703 = 4102055) B4102055
theorem B9223145 : Blo 1821612 9223145 := bstep (se 2 (by rfl) ⟨3458679, by rfl⟩ : syracuseStep 9223145 = 6917359) B6917359
theorem B8423327 : Blo 1821612 8423327 := bstep (se 1 (by rfl) ⟨6317495, by rfl⟩ : syracuseStep 8423327 = 12634991) B12634991
theorem B10957079 : Blo 1821612 10957079 := bstep (se 1 (by rfl) ⟨8217809, by rfl⟩ : syracuseStep 10957079 = 16435619) B16435619
theorem B1823135 : Blo 1821612 1823135 := bstep (se 1 (by rfl) ⟨1367351, by rfl⟩ : syracuseStep 1823135 = 2734703) B2734703
theorem B6148763 : Blo 1821612 6148763 := bstep (se 1 (by rfl) ⟨4611572, by rfl⟩ : syracuseStep 6148763 = 9223145) B9223145
theorem B9231569 : Blo 1821612 9231569 := bstep (se 2 (by rfl) ⟨3461838, by rfl⟩ : syracuseStep 9231569 = 6923677) B6923677
theorem B6154379 : Blo 1821612 6154379 := bstep (se 1 (by rfl) ⟨4615784, by rfl⟩ : syracuseStep 6154379 = 9231569) B9231569
theorem B4099175 : Blo 1821612 4099175 := bstep (se 1 (by rfl) ⟨3074381, by rfl⟩ : syracuseStep 4099175 = 6148763) B6148763
theorem B5615551 : Blo 1821612 5615551 := bstep (se 1 (by rfl) ⟨4211663, by rfl⟩ : syracuseStep 5615551 = 8423327) B8423327
theorem B29218877 : Blo 1821612 29218877 := bstep (se 3 (by rfl) ⟨5478539, by rfl⟩ : syracuseStep 29218877 = 10957079) B10957079
theorem B2732783 : Blo 1821612 2732783 := bstep (se 1 (by rfl) ⟨2049587, by rfl⟩ : syracuseStep 2732783 = 4099175) B4099175
theorem B19479251 : Blo 1821612 19479251 := bstep (se 1 (by rfl) ⟨14609438, by rfl⟩ : syracuseStep 19479251 = 29218877) B29218877
theorem B4102919 : Blo 1821612 4102919 := bstep (se 1 (by rfl) ⟨3077189, by rfl⟩ : syracuseStep 4102919 = 6154379) B6154379
theorem B29949605 : Blo 1821612 29949605 := bstep (se 4 (by rfl) ⟨2807775, by rfl⟩ : syracuseStep 29949605 = 5615551) B5615551
theorem B12986167 : Blo 1821612 12986167 := bstep (se 1 (by rfl) ⟨9739625, by rfl⟩ : syracuseStep 12986167 = 19479251) B19479251
theorem B19966403 : Blo 1821612 19966403 := bstep (se 1 (by rfl) ⟨14974802, by rfl⟩ : syracuseStep 19966403 = 29949605) B29949605
theorem B1821855 : Blo 1821612 1821855 := bstep (se 1 (by rfl) ⟨1366391, by rfl⟩ : syracuseStep 1821855 = 2732783) B2732783
theorem B2735279 : Blo 1821612 2735279 := bstep (se 1 (by rfl) ⟨2051459, by rfl⟩ : syracuseStep 2735279 = 4102919) B4102919
theorem B1823519 : Blo 1821612 1823519 := bstep (se 1 (by rfl) ⟨1367639, by rfl⟩ : syracuseStep 1823519 = 2735279) B2735279
theorem B17314889 : Blo 1821612 17314889 := bstep (se 2 (by rfl) ⟨6493083, by rfl⟩ : syracuseStep 17314889 = 12986167) B12986167
theorem B13310935 : Blo 1821612 13310935 := bstep (se 1 (by rfl) ⟨9983201, by rfl⟩ : syracuseStep 13310935 = 19966403) B19966403
theorem B46173037 : Blo 1821612 46173037 := bstep (se 3 (by rfl) ⟨8657444, by rfl⟩ : syracuseStep 46173037 = 17314889) B17314889
theorem B70991653 : Blo 1821612 70991653 := bstep (se 4 (by rfl) ⟨6655467, by rfl⟩ : syracuseStep 70991653 = 13310935) B13310935
theorem B61564049 : Blo 1821612 61564049 := bstep (se 2 (by rfl) ⟨23086518, by rfl⟩ : syracuseStep 61564049 = 46173037) B46173037
theorem B94655537 : Blo 1821612 94655537 := bstep (se 2 (by rfl) ⟨35495826, by rfl⟩ : syracuseStep 94655537 = 70991653) B70991653
theorem B63103691 : Blo 1821612 63103691 := bstep (se 1 (by rfl) ⟨47327768, by rfl⟩ : syracuseStep 63103691 = 94655537) B94655537
theorem B41042699 : Blo 1821612 41042699 := bstep (se 1 (by rfl) ⟨30782024, by rfl⟩ : syracuseStep 41042699 = 61564049) B61564049
theorem B27361799 : Blo 1821612 27361799 := bstep (se 1 (by rfl) ⟨20521349, by rfl⟩ : syracuseStep 27361799 = 41042699) B41042699
theorem B42069127 : Blo 1821612 42069127 := bstep (se 1 (by rfl) ⟨31551845, by rfl⟩ : syracuseStep 42069127 = 63103691) B63103691
theorem B56092169 : Blo 1821612 56092169 := bstep (se 2 (by rfl) ⟨21034563, by rfl⟩ : syracuseStep 56092169 = 42069127) B42069127
theorem B18241199 : Blo 1821612 18241199 := bstep (se 1 (by rfl) ⟨13680899, by rfl⟩ : syracuseStep 18241199 = 27361799) B27361799
theorem B12160799 : Blo 1821612 12160799 := bstep (se 1 (by rfl) ⟨9120599, by rfl⟩ : syracuseStep 12160799 = 18241199) B18241199
theorem B37394779 : Blo 1821612 37394779 := bstep (se 1 (by rfl) ⟨28046084, by rfl⟩ : syracuseStep 37394779 = 56092169) B56092169
theorem B49859705 : Blo 1821612 49859705 := bstep (se 2 (by rfl) ⟨18697389, by rfl⟩ : syracuseStep 49859705 = 37394779) B37394779
theorem B8107199 : Blo 1821612 8107199 := bstep (se 1 (by rfl) ⟨6080399, by rfl⟩ : syracuseStep 8107199 = 12160799) B12160799
theorem B33239803 : Blo 1821612 33239803 := bstep (se 1 (by rfl) ⟨24929852, by rfl⟩ : syracuseStep 33239803 = 49859705) B49859705
theorem B5404799 : Blo 1821612 5404799 := bstep (se 1 (by rfl) ⟨4053599, by rfl⟩ : syracuseStep 5404799 = 8107199) B8107199
theorem B44319737 : Blo 1821612 44319737 := bstep (se 2 (by rfl) ⟨16619901, by rfl⟩ : syracuseStep 44319737 = 33239803) B33239803
theorem B3603199 : Blo 1821612 3603199 := bstep (se 1 (by rfl) ⟨2702399, by rfl⟩ : syracuseStep 3603199 = 5404799) B5404799
theorem B4804265 : Blo 1821612 4804265 := bstep (se 2 (by rfl) ⟨1801599, by rfl⟩ : syracuseStep 4804265 = 3603199) B3603199
theorem B29546491 : Blo 1821612 29546491 := bstep (se 1 (by rfl) ⟨22159868, by rfl⟩ : syracuseStep 29546491 = 44319737) B44319737
theorem B3202843 : Blo 1821612 3202843 := bstep (se 1 (by rfl) ⟨2402132, by rfl⟩ : syracuseStep 3202843 = 4804265) B4804265
theorem B39395321 : Blo 1821612 39395321 := bstep (se 2 (by rfl) ⟨14773245, by rfl⟩ : syracuseStep 39395321 = 29546491) B29546491
theorem B4270457 : Blo 1821612 4270457 := bstep (se 2 (by rfl) ⟨1601421, by rfl⟩ : syracuseStep 4270457 = 3202843) B3202843
theorem B26263547 : Blo 1821612 26263547 := bstep (se 1 (by rfl) ⟨19697660, by rfl⟩ : syracuseStep 26263547 = 39395321) B39395321
theorem B17509031 : Blo 1821612 17509031 := bstep (se 1 (by rfl) ⟨13131773, by rfl⟩ : syracuseStep 17509031 = 26263547) B26263547
theorem B2846971 : Blo 1821612 2846971 := bstep (se 1 (by rfl) ⟨2135228, by rfl⟩ : syracuseStep 2846971 = 4270457) B4270457
theorem B15183845 : Blo 1821612 15183845 := bstep (se 4 (by rfl) ⟨1423485, by rfl⟩ : syracuseStep 15183845 = 2846971) B2846971
theorem B11672687 : Blo 1821612 11672687 := bstep (se 1 (by rfl) ⟨8754515, by rfl⟩ : syracuseStep 11672687 = 17509031) B17509031
theorem B10122563 : Blo 1821612 10122563 := bstep (se 1 (by rfl) ⟨7591922, by rfl⟩ : syracuseStep 10122563 = 15183845) B15183845
theorem B7781791 : Blo 1821612 7781791 := bstep (se 1 (by rfl) ⟨5836343, by rfl⟩ : syracuseStep 7781791 = 11672687) B11672687
theorem B26993501 : Blo 1821612 26993501 := bstep (se 3 (by rfl) ⟨5061281, by rfl⟩ : syracuseStep 26993501 = 10122563) B10122563
theorem B10375721 : Blo 1821612 10375721 := bstep (se 2 (by rfl) ⟨3890895, by rfl⟩ : syracuseStep 10375721 = 7781791) B7781791
theorem B6917147 : Blo 1821612 6917147 := bstep (se 1 (by rfl) ⟨5187860, by rfl⟩ : syracuseStep 6917147 = 10375721) B10375721
theorem B17995667 : Blo 1821612 17995667 := bstep (se 1 (by rfl) ⟨13496750, by rfl⟩ : syracuseStep 17995667 = 26993501) B26993501
theorem B4611431 : Blo 1821612 4611431 := bstep (se 1 (by rfl) ⟨3458573, by rfl⟩ : syracuseStep 4611431 = 6917147) B6917147
theorem B47988445 : Blo 1821612 47988445 := bstep (se 3 (by rfl) ⟨8997833, by rfl⟩ : syracuseStep 47988445 = 17995667) B17995667
theorem B3074287 : Blo 1821612 3074287 := bstep (se 1 (by rfl) ⟨2305715, by rfl⟩ : syracuseStep 3074287 = 4611431) B4611431
theorem B63984593 : Blo 1821612 63984593 := bstep (se 2 (by rfl) ⟨23994222, by rfl⟩ : syracuseStep 63984593 = 47988445) B47988445
theorem B42656395 : Blo 1821612 42656395 := bstep (se 1 (by rfl) ⟨31992296, by rfl⟩ : syracuseStep 42656395 = 63984593) B63984593
theorem B4099049 : Blo 1821612 4099049 := bstep (se 2 (by rfl) ⟨1537143, by rfl⟩ : syracuseStep 4099049 = 3074287) B3074287
theorem B2732699 : Blo 1821612 2732699 := bstep (se 1 (by rfl) ⟨2049524, by rfl⟩ : syracuseStep 2732699 = 4099049) B4099049
theorem B56875193 : Blo 1821612 56875193 := bstep (se 2 (by rfl) ⟨21328197, by rfl⟩ : syracuseStep 56875193 = 42656395) B42656395
theorem B1821799 : Blo 1821612 1821799 := bstep (se 1 (by rfl) ⟨1366349, by rfl⟩ : syracuseStep 1821799 = 2732699) B2732699
theorem B37916795 : Blo 1821612 37916795 := bstep (se 1 (by rfl) ⟨28437596, by rfl⟩ : syracuseStep 37916795 = 56875193) B56875193
theorem B101111453 : Blo 1821612 101111453 := bstep (se 3 (by rfl) ⟨18958397, by rfl⟩ : syracuseStep 101111453 = 37916795) B37916795
theorem B67407635 : Blo 1821612 67407635 := bstep (se 1 (by rfl) ⟨50555726, by rfl⟩ : syracuseStep 67407635 = 101111453) B101111453
theorem B44938423 : Blo 1821612 44938423 := bstep (se 1 (by rfl) ⟨33703817, by rfl⟩ : syracuseStep 44938423 = 67407635) B67407635
theorem B59917897 : Blo 1821612 59917897 := bstep (se 2 (by rfl) ⟨22469211, by rfl⟩ : syracuseStep 59917897 = 44938423) B44938423
theorem B319562117 : Blo 1821612 319562117 := bstep (se 4 (by rfl) ⟨29958948, by rfl⟩ : syracuseStep 319562117 = 59917897) B59917897
theorem B213041411 : Blo 1821612 213041411 := bstep (se 1 (by rfl) ⟨159781058, by rfl⟩ : syracuseStep 213041411 = 319562117) B319562117
theorem B142027607 : Blo 1821612 142027607 := bstep (se 1 (by rfl) ⟨106520705, by rfl⟩ : syracuseStep 142027607 = 213041411) B213041411
theorem B94685071 : Blo 1821612 94685071 := bstep (se 1 (by rfl) ⟨71013803, by rfl⟩ : syracuseStep 94685071 = 142027607) B142027607
theorem B126246761 : Blo 1821612 126246761 := bstep (se 2 (by rfl) ⟨47342535, by rfl⟩ : syracuseStep 126246761 = 94685071) B94685071
theorem B84164507 : Blo 1821612 84164507 := bstep (se 1 (by rfl) ⟨63123380, by rfl⟩ : syracuseStep 84164507 = 126246761) B126246761
theorem B56109671 : Blo 1821612 56109671 := bstep (se 1 (by rfl) ⟨42082253, by rfl⟩ : syracuseStep 56109671 = 84164507) B84164507
theorem B37406447 : Blo 1821612 37406447 := bstep (se 1 (by rfl) ⟨28054835, by rfl⟩ : syracuseStep 37406447 = 56109671) B56109671
theorem B24937631 : Blo 1821612 24937631 := bstep (se 1 (by rfl) ⟨18703223, by rfl⟩ : syracuseStep 24937631 = 37406447) B37406447
theorem B16625087 : Blo 1821612 16625087 := bstep (se 1 (by rfl) ⟨12468815, by rfl⟩ : syracuseStep 16625087 = 24937631) B24937631
theorem B11083391 : Blo 1821612 11083391 := bstep (se 1 (by rfl) ⟨8312543, by rfl⟩ : syracuseStep 11083391 = 16625087) B16625087
theorem B7388927 : Blo 1821612 7388927 := bstep (se 1 (by rfl) ⟨5541695, by rfl⟩ : syracuseStep 7388927 = 11083391) B11083391
theorem B4925951 : Blo 1821612 4925951 := bstep (se 1 (by rfl) ⟨3694463, by rfl⟩ : syracuseStep 4925951 = 7388927) B7388927
theorem B3283967 : Blo 1821612 3283967 := bstep (se 1 (by rfl) ⟨2462975, by rfl⟩ : syracuseStep 3283967 = 4925951) B4925951
theorem B2189311 : Blo 1821612 2189311 := bstep (se 1 (by rfl) ⟨1641983, by rfl⟩ : syracuseStep 2189311 = 3283967) B3283967
theorem B11676325 : Blo 1821612 11676325 := bstep (se 4 (by rfl) ⟨1094655, by rfl⟩ : syracuseStep 11676325 = 2189311) B2189311
theorem B15568433 : Blo 1821612 15568433 := bstep (se 2 (by rfl) ⟨5838162, by rfl⟩ : syracuseStep 15568433 = 11676325) B11676325
theorem B10378955 : Blo 1821612 10378955 := bstep (se 1 (by rfl) ⟨7784216, by rfl⟩ : syracuseStep 10378955 = 15568433) B15568433
theorem B6919303 : Blo 1821612 6919303 := bstep (se 1 (by rfl) ⟨5189477, by rfl⟩ : syracuseStep 6919303 = 10378955) B10378955
theorem B9225737 : Blo 1821612 9225737 := bstep (se 2 (by rfl) ⟨3459651, by rfl⟩ : syracuseStep 9225737 = 6919303) B6919303
theorem B6150491 : Blo 1821612 6150491 := bstep (se 1 (by rfl) ⟨4612868, by rfl⟩ : syracuseStep 6150491 = 9225737) B9225737
theorem B4100327 : Blo 1821612 4100327 := bstep (se 1 (by rfl) ⟨3075245, by rfl⟩ : syracuseStep 4100327 = 6150491) B6150491
theorem B2733551 : Blo 1821612 2733551 := bstep (se 1 (by rfl) ⟨2050163, by rfl⟩ : syracuseStep 2733551 = 4100327) B4100327
theorem B1822367 : Blo 1821612 1822367 := bstep (se 1 (by rfl) ⟨1366775, by rfl⟩ : syracuseStep 1822367 = 2733551) B2733551

theorem C0 (j : ℕ) (h1 : 455403 ≤ j) (h2 : j ≤ 455902) : Blo 1821612 (4 * j + 3) := by
  interval_cases j
  · exact B1821615
  · exact B1821619
  · exact B1821623
  · exact B1821627
  · exact B1821631
  · exact B1821635
  · exact B1821639
  · exact B1821643
  · exact B1821647
  · exact B1821651
  · exact B1821655
  · exact B1821659
  · exact B1821663
  · exact B1821667
  · exact B1821671
  · exact B1821675
  · exact B1821679
  · exact B1821683
  · exact B1821687
  · exact B1821691
  · exact B1821695
  · exact B1821699
  · exact B1821703
  · exact B1821707
  · exact B1821711
  · exact B1821715
  · exact B1821719
  · exact B1821723
  · exact B1821727
  · exact B1821731
  · exact B1821735
  · exact B1821739
  · exact B1821743
  · exact B1821747
  · exact B1821751
  · exact B1821755
  · exact B1821759
  · exact B1821763
  · exact B1821767
  · exact B1821771
  · exact B1821775
  · exact B1821779
  · exact B1821783
  · exact B1821787
  · exact B1821791
  · exact B1821795
  · exact B1821799
  · exact B1821803
  · exact B1821807
  · exact B1821811
  · exact B1821815
  · exact B1821819
  · exact B1821823
  · exact B1821827
  · exact B1821831
  · exact B1821835
  · exact B1821839
  · exact B1821843
  · exact B1821847
  · exact B1821851
  · exact B1821855
  · exact B1821859
  · exact B1821863
  · exact B1821867
  · exact B1821871
  · exact B1821875
  · exact B1821879
  · exact B1821883
  · exact B1821887
  · exact B1821891
  · exact B1821895
  · exact B1821899
  · exact B1821903
  · exact B1821907
  · exact B1821911
  · exact B1821915
  · exact B1821919
  · exact B1821923
  · exact B1821927
  · exact B1821931
  · exact B1821935
  · exact B1821939
  · exact B1821943
  · exact B1821947
  · exact B1821951
  · exact B1821955
  · exact B1821959
  · exact B1821963
  · exact B1821967
  · exact B1821971
  · exact B1821975
  · exact B1821979
  · exact B1821983
  · exact B1821987
  · exact B1821991
  · exact B1821995
  · exact B1821999
  · exact B1822003
  · exact B1822007
  · exact B1822011
  · exact B1822015
  · exact B1822019
  · exact B1822023
  · exact B1822027
  · exact B1822031
  · exact B1822035
  · exact B1822039
  · exact B1822043
  · exact B1822047
  · exact B1822051
  · exact B1822055
  · exact B1822059
  · exact B1822063
  · exact B1822067
  · exact B1822071
  · exact B1822075
  · exact B1822079
  · exact B1822083
  · exact B1822087
  · exact B1822091
  · exact B1822095
  · exact B1822099
  · exact B1822103
  · exact B1822107
  · exact B1822111
  · exact B1822115
  · exact B1822119
  · exact B1822123
  · exact B1822127
  · exact B1822131
  · exact B1822135
  · exact B1822139
  · exact B1822143
  · exact B1822147
  · exact B1822151
  · exact B1822155
  · exact B1822159
  · exact B1822163
  · exact B1822167
  · exact B1822171
  · exact B1822175
  · exact B1822179
  · exact B1822183
  · exact B1822187
  · exact B1822191
  · exact B1822195
  · exact B1822199
  · exact B1822203
  · exact B1822207
  · exact B1822211
  · exact B1822215
  · exact B1822219
  · exact B1822223
  · exact B1822227
  · exact B1822231
  · exact B1822235
  · exact B1822239
  · exact B1822243
  · exact B1822247
  · exact B1822251
  · exact B1822255
  · exact B1822259
  · exact B1822263
  · exact B1822267
  · exact B1822271
  · exact B1822275
  · exact B1822279
  · exact B1822283
  · exact B1822287
  · exact B1822291
  · exact B1822295
  · exact B1822299
  · exact B1822303
  · exact B1822307
  · exact B1822311
  · exact B1822315
  · exact B1822319
  · exact B1822323
  · exact B1822327
  · exact B1822331
  · exact B1822335
  · exact B1822339
  · exact B1822343
  · exact B1822347
  · exact B1822351
  · exact B1822355
  · exact B1822359
  · exact B1822363
  · exact B1822367
  · exact B1822371
  · exact B1822375
  · exact B1822379
  · exact B1822383
  · exact B1822387
  · exact B1822391
  · exact B1822395
  · exact B1822399
  · exact B1822403
  · exact B1822407
  · exact B1822411
  · exact B1822415
  · exact B1822419
  · exact B1822423
  · exact B1822427
  · exact B1822431
  · exact B1822435
  · exact B1822439
  · exact B1822443
  · exact B1822447
  · exact B1822451
  · exact B1822455
  · exact B1822459
  · exact B1822463
  · exact B1822467
  · exact B1822471
  · exact B1822475
  · exact B1822479
  · exact B1822483
  · exact B1822487
  · exact B1822491
  · exact B1822495
  · exact B1822499
  · exact B1822503
  · exact B1822507
  · exact B1822511
  · exact B1822515
  · exact B1822519
  · exact B1822523
  · exact B1822527
  · exact B1822531
  · exact B1822535
  · exact B1822539
  · exact B1822543
  · exact B1822547
  · exact B1822551
  · exact B1822555
  · exact B1822559
  · exact B1822563
  · exact B1822567
  · exact B1822571
  · exact B1822575
  · exact B1822579
  · exact B1822583
  · exact B1822587
  · exact B1822591
  · exact B1822595
  · exact B1822599
  · exact B1822603
  · exact B1822607
  · exact B1822611
  · exact B1822615
  · exact B1822619
  · exact B1822623
  · exact B1822627
  · exact B1822631
  · exact B1822635
  · exact B1822639
  · exact B1822643
  · exact B1822647
  · exact B1822651
  · exact B1822655
  · exact B1822659
  · exact B1822663
  · exact B1822667
  · exact B1822671
  · exact B1822675
  · exact B1822679
  · exact B1822683
  · exact B1822687
  · exact B1822691
  · exact B1822695
  · exact B1822699
  · exact B1822703
  · exact B1822707
  · exact B1822711
  · exact B1822715
  · exact B1822719
  · exact B1822723
  · exact B1822727
  · exact B1822731
  · exact B1822735
  · exact B1822739
  · exact B1822743
  · exact B1822747
  · exact B1822751
  · exact B1822755
  · exact B1822759
  · exact B1822763
  · exact B1822767
  · exact B1822771
  · exact B1822775
  · exact B1822779
  · exact B1822783
  · exact B1822787
  · exact B1822791
  · exact B1822795
  · exact B1822799
  · exact B1822803
  · exact B1822807
  · exact B1822811
  · exact B1822815
  · exact B1822819
  · exact B1822823
  · exact B1822827
  · exact B1822831
  · exact B1822835
  · exact B1822839
  · exact B1822843
  · exact B1822847
  · exact B1822851
  · exact B1822855
  · exact B1822859
  · exact B1822863
  · exact B1822867
  · exact B1822871
  · exact B1822875
  · exact B1822879
  · exact B1822883
  · exact B1822887
  · exact B1822891
  · exact B1822895
  · exact B1822899
  · exact B1822903
  · exact B1822907
  · exact B1822911
  · exact B1822915
  · exact B1822919
  · exact B1822923
  · exact B1822927
  · exact B1822931
  · exact B1822935
  · exact B1822939
  · exact B1822943
  · exact B1822947
  · exact B1822951
  · exact B1822955
  · exact B1822959
  · exact B1822963
  · exact B1822967
  · exact B1822971
  · exact B1822975
  · exact B1822979
  · exact B1822983
  · exact B1822987
  · exact B1822991
  · exact B1822995
  · exact B1822999
  · exact B1823003
  · exact B1823007
  · exact B1823011
  · exact B1823015
  · exact B1823019
  · exact B1823023
  · exact B1823027
  · exact B1823031
  · exact B1823035
  · exact B1823039
  · exact B1823043
  · exact B1823047
  · exact B1823051
  · exact B1823055
  · exact B1823059
  · exact B1823063
  · exact B1823067
  · exact B1823071
  · exact B1823075
  · exact B1823079
  · exact B1823083
  · exact B1823087
  · exact B1823091
  · exact B1823095
  · exact B1823099
  · exact B1823103
  · exact B1823107
  · exact B1823111
  · exact B1823115
  · exact B1823119
  · exact B1823123
  · exact B1823127
  · exact B1823131
  · exact B1823135
  · exact B1823139
  · exact B1823143
  · exact B1823147
  · exact B1823151
  · exact B1823155
  · exact B1823159
  · exact B1823163
  · exact B1823167
  · exact B1823171
  · exact B1823175
  · exact B1823179
  · exact B1823183
  · exact B1823187
  · exact B1823191
  · exact B1823195
  · exact B1823199
  · exact B1823203
  · exact B1823207
  · exact B1823211
  · exact B1823215
  · exact B1823219
  · exact B1823223
  · exact B1823227
  · exact B1823231
  · exact B1823235
  · exact B1823239
  · exact B1823243
  · exact B1823247
  · exact B1823251
  · exact B1823255
  · exact B1823259
  · exact B1823263
  · exact B1823267
  · exact B1823271
  · exact B1823275
  · exact B1823279
  · exact B1823283
  · exact B1823287
  · exact B1823291
  · exact B1823295
  · exact B1823299
  · exact B1823303
  · exact B1823307
  · exact B1823311
  · exact B1823315
  · exact B1823319
  · exact B1823323
  · exact B1823327
  · exact B1823331
  · exact B1823335
  · exact B1823339
  · exact B1823343
  · exact B1823347
  · exact B1823351
  · exact B1823355
  · exact B1823359
  · exact B1823363
  · exact B1823367
  · exact B1823371
  · exact B1823375
  · exact B1823379
  · exact B1823383
  · exact B1823387
  · exact B1823391
  · exact B1823395
  · exact B1823399
  · exact B1823403
  · exact B1823407
  · exact B1823411
  · exact B1823415
  · exact B1823419
  · exact B1823423
  · exact B1823427
  · exact B1823431
  · exact B1823435
  · exact B1823439
  · exact B1823443
  · exact B1823447
  · exact B1823451
  · exact B1823455
  · exact B1823459
  · exact B1823463
  · exact B1823467
  · exact B1823471
  · exact B1823475
  · exact B1823479
  · exact B1823483
  · exact B1823487
  · exact B1823491
  · exact B1823495
  · exact B1823499
  · exact B1823503
  · exact B1823507
  · exact B1823511
  · exact B1823515
  · exact B1823519
  · exact B1823523
  · exact B1823527
  · exact B1823531
  · exact B1823535
  · exact B1823539
  · exact B1823543
  · exact B1823547
  · exact B1823551
  · exact B1823555
  · exact B1823559
  · exact B1823563
  · exact B1823567
  · exact B1823571
  · exact B1823575
  · exact B1823579
  · exact B1823583
  · exact B1823587
  · exact B1823591
  · exact B1823595
  · exact B1823599
  · exact B1823603
  · exact B1823607
  · exact B1823611

theorem solution (m : ℕ) (hlo : 1821612 ≤ m) (hhi : m ≤ 1823612) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 455403 ≤ j := by omega
    have hj2 : j ≤ 455902 := by omega
    have hb : Blo 1821612 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
