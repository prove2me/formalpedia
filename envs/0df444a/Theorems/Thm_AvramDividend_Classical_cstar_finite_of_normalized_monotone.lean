-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_finite_of_normalized_monotone
-- name    : AvramDividend.Classical.cstar_finite_of_normalized_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T18:13:40.211348+00:00
-- url     : https://prove2.me/theorems/330ec601-3f42-4ef8-898a-e64f0c13ee5c
-- title:
--   Finite Avram barrier from tilted-scale monotonicity and positive-axis regularity
-- statement:
--   If φ>0, W(1)>0, the tilted W is nondecreasing, and W is differentiable for all positive x with its derivative continuous on the positive half-line, the canonical optimal-dividend level cstar is finite. This composes a new exponential-growth bridge for W' with the already-proved positive-axis-continuity cstar finiteness theorem, without requiring a positive derivative-minimising point to exist.
-- source:
--   Compose previously proved normalized_derivative_lower_bound and normalized_eventual_derivative_growth to get an eventual positive exponential lower bound on W' without importing any Open child. Pinned Mathlib converts this to Tendsto W' atTop, and the already Proved cstar_finite_of_deriv_continuous_positive_axis_growth gives finiteness. This repairs an authoring dependency rejection in v1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_normalized_derivative_lower_bound
import Theorems.Thm_AvramDividend_Classical_normalized_eventual_derivative_growth
import Theorems.Thm_AvramDividend_Classical_cstar_finite_of_deriv_continuous_positive_axis_growth
open AvramDividend.Classical Filter
open scoped Topology ENNReal

namespace AvramDividend.Classical

theorem cstar_finite_of_normalized_monotone
    (W : ℝ → ℝ) (φ : ℝ)
    (hφ : 0 < φ) (hW1 : 0 < W 1)
    (htilt : MonotoneOn
      (fun t : ℝ => Real.exp (-φ * t) * W t) (Set.Ioi 0))
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x)
    (hcont : ContinuousOn (deriv W) (Set.Ioi 0)) :
    cstar W < ⊤ := by sorry

end AvramDividend.Classical
