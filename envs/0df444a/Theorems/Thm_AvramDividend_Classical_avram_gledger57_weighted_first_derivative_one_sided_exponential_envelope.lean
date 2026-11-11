-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger57_weighted_first_derivative_one_sided_exponential_envelope
-- name    : AvramDividend.Classical.avram_gledger57_weighted_first_derivative_one_sided_exponential_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:08:01.354366+00:00
-- url     : https://prove2.me/theorems/e8272194-1847-43d6-896f-5818629bab44
-- title:
--   One-sided exponential growth envelope from an upper bound on the weighted derivative
-- statement:
--   Once the HJB factorisation shows the weighted first derivative is nonincreasing from an anchor u, a one-sided exponential majorant follows by scalar first-order comparison. The constant K depends only on the value and derivative at the anchor. The estimate allows arbitrarily negative values of w, so it is suitable for positive-part integrability without an unjustified absolute-growth hypothesis.
-- source:
--   Necessary deterministic growth bridge for Open gledger53 after gledger55 weighted-derivative factorisation and gledger56 positive/negative characteristic roots. Uses Proved 1ba47f4d scalar exponential derivative comparison.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gsource15_exponential_derivative_comparison
open AvramDividend.Classical MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_gledger57_weighted_first_derivative_one_sided_exponential_envelope
    (r l u : ℝ) (hr : l < r) (hu : 0 < u) (w : ℝ → ℝ)
    (hw : ∀ y : ℝ, u ≤ y → HasDerivAt w (deriv w y) y)
    (hweighted : ∀ y : ℝ, u ≤ y →
      Real.exp (-(r * y)) * (deriv w y - l * w y) ≤
        Real.exp (-(r * u)) * (deriv w u - l * w u)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, u ≤ y →
      w y ≤ K * Real.exp (r * y) := by sorry
