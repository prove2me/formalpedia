-- Prove2me | solution 1 for section5_window_truncate_error
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:09:07.152599+00:00
-- url     : https://prove2.me/submissions/ba25bac6-d87b-4e12-b371-5efb1a0d7d13

import Definitions.Def_Section5Verified_Section5SignedWindow
import Mathlib
section
set_option autoImplicit false

/-! Signed middle-bit windows. The discarded low bits cause a bounded rounding error;
the omitted high bits are irrelevant inside the represented interval. -/



theorem section5_signed_residue_exact (H z : ℤ) (hH : 0 < H) (hlo : -H ≤ z) (hhi : z < H) :
    section5_signed_residue H z=z := by
  unfold section5_signed_residue
  by_cases hz : 0 ≤ z
  · have hr : z % (2*H)=z := Int.emod_eq_of_lt hz (by omega)
    rw [hr,if_pos hhi]
  · have hr : (z+2*H) % (2*H)=z+2*H := Int.emod_eq_of_lt (by omega) (by omega)
    have hzmod : z % (2*H)=z+2*H := by
      simpa only [Int.add_emod,Int.emod_self,add_zero,Int.emod_emod] using hr
    rw [hzmod,if_neg (by omega)]
    omega



theorem section5_window_truncate_remainder (P H z : ℤ) (hP : 0 < P) (hH : 0 < H)
    (hlo : -H*P ≤ z) (hhi : z < H*P) :
    z-section5_window_truncate P H z=z%P := by
  have hqlo : -H ≤ z/P := (Int.le_ediv_iff_mul_le hP).mpr hlo
  have hqhi : z/P < H := (Int.ediv_lt_iff_lt_mul hP).mpr hhi
  unfold section5_window_truncate
  rw [section5_signed_residue_exact H (z/P) hH hqlo hqhi,Int.emod_def]







end
set_option autoImplicit false
theorem solution (P H z : ℤ) (hP : 0 < P) (hH : 0 < H)
    (hlo : -H*P ≤ z) (hhi : z < H*P) :
    |z-section5_window_truncate P H z| < P := by
  rw [section5_window_truncate_remainder P H z hP hH hlo hhi,
    abs_of_nonneg (Int.emod_nonneg _ (ne_of_gt hP))]
  exact Int.emod_lt_of_pos _ hP
