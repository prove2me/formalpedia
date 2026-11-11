-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger64_topcap_C2_supplies_original_classical_derivatives
-- name    : AvramDividend.Classical.avram_gledger64_topcap_C2_supplies_original_classical_derivatives
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:42:25.670709+00:00
-- url     : https://prove2.me/theorems/980916f6-9c72-4f65-b315-9cdc4f8e47ba
-- title:
--   Original top-cap interior C2 hypothesis supplies ordinary first and second derivative witnesses
-- statement:
--   In the infinite-cap case the C2 smooth interior is the positive half-line. On that open set a twice continuously differentiable value candidate has the ordinary derivative of w and the ordinary derivative of deriv w at every positive reserve, with the latter equal to the second iterated derivative. This unblocks the analytic original zero-jump Gaussian growth certificate from the exact source smoothness hypothesis.
-- source:
--   Exact derivative bridge needed to apply gledger61 original zero-jump HJB upper envelope to original root-connected gledger53 and f77 smoothness hypotheses. Official pinned API: ContDiffOn.deriv_of_isOpen and ContDiffOn.differentiableOn.

import Mathlib
open Set Filter
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger64_topcap_C2_supplies_original_classical_derivatives
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∀ y : ℝ, 0 < y →
      HasDerivAt w (deriv w y) y ∧
        HasDerivAt (deriv w) (iteratedDeriv 2 w y) y := by sorry
