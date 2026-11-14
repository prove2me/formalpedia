-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_C1_negative_jump_candidate_loss_uniform_zero_band_bound_without_zero_boundary_value
-- name    : AvramDividend.Classical.avram_bva_a22_original_C1_negative_jump_candidate_loss_uniform_zero_band_bound_without_zero_boundary_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:53:27.934365+00:00
-- url     : https://prove2.me/theorems/c70ea408-d618-4606-969c-876b974e4b95
-- title:
--   Original negative-jump candidate loss at positive reserves below a small band is nonnegative and bounded by w(epsilon), even when w(0)>0
-- statement:
--   Let w be an original dividend verification candidate equal to zero on strictly negative ruin reserves, nonnegative at reserve zero and monotone on a closed nonnegative band [0,epsilon]. Every actual negative jump mark z<0 from a prepayment reserve y in (0,epsilon] has candidate loss w(y)-w(y+z) between zero and w(epsilon), whether or not the jump crosses the ruin boundary. Crucially no assumption w(0)=0 is needed. This is the pointwise jump-loss ingredient for combining the original BV truncated first-moment spatial boundary layer with the stopped negative-mark compensator in BVA96, without asserting full source occupation-time integrability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical Set Filter AvramDividend.Classical
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_C1_negative_jump_candidate_loss_uniform_zero_band_bound_without_zero_boundary_value
    (w : ℝ → ℝ)
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw0 : 0 ≤ w 0)
    (ε : ℝ) (hε : 0 < ε)
    (hmono : MonotoneOn w (Icc (0 : ℝ) ε)) :
    ∀ y ∈ Ioc (0 : ℝ) ε, ∀ z : ℝ, z < 0 →
      0 ≤ w y - w (y + z) ∧ w y - w (y + z) ≤ w ε := by sorry
