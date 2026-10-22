-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_positive_clock_inverse_derivative
-- name    : BirkhoffGlobalSection.positive_clock_inverse_derivative
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T22:01:43.98399+00:00
-- url     : https://prove2.me/theorems/64e5a664-536c-400e-9756-23a4e69959f1
-- title:
--   Positive clock inverse derivative
-- statement:
--   The inverse of a real order clock with positive derivative has derivative equal to the reciprocal rate evaluated at inverse time.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Original auxiliary result from the accepted source Solutions/Sol_BirkhoffGlobalSection_convex_model_complete_normalized_flow_of_model_fields.lean:145. Exact quantified statement retained; foundational calculus and geometry are imported from Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Theorems.Thm_BirkhoffGlobalSection_convex_model_boundary_contact_positive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Order.Hom.Set
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.MeanValue
import Theorems.Thm_BirkhoffGlobalSection_hamiltonian_radial_characteristic_normalization

open Set
open scoped Topology ContDiff



set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.positive_clock_inverse_derivative (clock : ℝ ≃o ℝ) (r : ℝ → ℝ)
    (hd : ∀ t, HasDerivAt clock (r t) t) (hpos : ∀ t, 0 < r t) (t : ℝ) :
    HasDerivAt clock.symm (r (clock.symm t))⁻¹ t := by sorry
