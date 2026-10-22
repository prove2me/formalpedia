-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_hamiltonian_radial_contact_continuousAt
-- name    : BirkhoffGlobalSection.hamiltonian_radial_contact_continuousAt
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T22:01:46.463953+00:00
-- url     : https://prove2.me/theorems/f4d69396-6ae8-4815-a349-7262a2e29e86
-- title:
--   Hamiltonian radial contact continuousAt
-- statement:
--   The radial contact pairing with a smooth Hamiltonian vector field is continuous at the base point.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Original auxiliary result from the accepted source Solutions/Sol_BirkhoffGlobalSection_convex_model_complete_normalized_flow_of_model_fields.lean:333. Exact quantified statement retained; foundational calculus and geometry are imported from Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

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

theorem BirkhoffGlobalSection.hamiltonian_radial_contact_continuousAt
    (F : BirkhoffGlobalSection.Phase → ℝ) (y : BirkhoffGlobalSection.Phase)
    (hF : ContDiffAt ℝ ∞ F y) :
    ContinuousAt (fun x => BirkhoffGlobalSection.phaseRadialContact x
      (BirkhoffGlobalSection.hamiltonianVectorField F x)) y := by sorry
