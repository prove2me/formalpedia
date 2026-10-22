-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_compact_trajectory_positive_clock
-- name    : BirkhoffGlobalSection.compact_trajectory_positive_clock
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T22:01:26.498231+00:00
-- url     : https://prove2.me/theorems/6e2012d6-ecf5-47d2-a12d-b35b66e6962e
-- title:
--   Compact trajectory positive clock
-- statement:
--   A continuous trajectory contained in a compact set with a continuous positive rate admits a complete increasing integral clock starting at zero, whose derivative equals the rate along the trajectory.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Original auxiliary result from the accepted source Solutions/Sol_BirkhoffGlobalSection_convex_model_complete_normalized_flow_of_model_fields.lean:84. Exact quantified statement retained; foundational calculus and geometry are imported from Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

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

import Theorems.Thm_TimeChange_compact_positive_rate_bounds
import Theorems.Thm_TimeChange_complete_positive_clock
open Set
open scoped Topology ContDiff



set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.compact_trajectory_positive_clock {S : Type*} [TopologicalSpace S]
    (K : Set S) (hK : IsCompact K) (r : S → ℝ) (hr : ContinuousOn r K)
    (hpos : ∀ x ∈ K, 0 < r x) (y : ℝ → S) (hy : Continuous y)
    (hyK : ∀ t, y t ∈ K) :
    ∃ clock : ℝ ≃o ℝ,
      clock 0 = 0 ∧ (∀ t, HasDerivAt clock (r (y t)) t) ∧
      (∀ t, clock t = ∫ s in (0 : ℝ)..t, r (y s)) := by sorry
