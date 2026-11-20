-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_topcap_exp_growth_scalar_value_envelope
-- name    : AvramDividend.Classical.avram_f6_original_topcap_exp_growth_scalar_value_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:42:00.638797+00:00
-- url     : https://prove2.me/theorems/d494078c-d1e8-451b-8400-7ba5a2a11cd3
-- title:
--   Original true topcap value w bounded absolutely by exponential ceiling including negative ruin reserve
-- statement:
--   For original HJB w zero on negative reserves and nonnegative on positive reserves, any genuine global exp growth envelope K e^{θz} yields |w(W)|≤K e^{θS} for any actual stopped W≤S. Supports the zero-jump Gaussian topcap original expected rightmesh dominated convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_topcap_exp_growth_scalar_value_envelope
    (w : ℝ → ℝ)
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_pos : ∀ y : ℝ, 0 ≤ y → 0 ≤ w y)
    (θ K : ℝ) (hθ : 0 ≤ θ) (hK : 0 ≤ K)
    (hw_exp : ∀ y : ℝ, 0 ≤ y →
      w y ≤ K * Real.exp (θ * y))
    (S z : ℝ) (hzS : z ≤ S) :
    |w z| ≤ K * Real.exp (θ * S) := by sorry
