-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_interior_nonnegative_gradient_preserves_boundary_payoff
-- name    : AvramDividend.Classical.avram_p4_e_localise_interior_nonnegative_gradient_preserves_boundary_payoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:54:28.470686+00:00
-- url     : https://prove2.me/theorems/4da8dd65-dc5d-453c-b54e-76abea31dd95
-- title:
--   Interior derivative sign and closed-interval continuity guarantee nonnegative value even at zero or cap contact
-- statement:
--   From continuous closed-interval payoff and nonnegative derivative on the open interval only, nonnegative initial value extends to either zero or cap endpoint. Uses pinned Mathlib monotoneOn_of_deriv_nonneg; original Avram namespace is loaded from source dividend definition to make the published declaration valid. No assertion of zero occupation at endpoints.
-- source:
--   Avram Proposition 4(i) continuity and interior derivative sign; pinned Mathlib monotoneOn_of_deriv_nonneg.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_p4_e_localise_interior_nonnegative_gradient_preserves_boundary_payoff
    (w : ℝ → ℝ) (y : ℝ) (hy : 0 ≤ y)
    (hw0 : 0 ≤ w 0)
    (hcont : ContinuousOn w (Icc 0 y))
    (hdiff : DifferentiableOn ℝ w (Ioo 0 y))
    (hgrad : ∀ z ∈ Ioo 0 y, 0 ≤ deriv w z) :
    0 ≤ w y := by sorry
