-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_local_inward_negative_not_stationary
-- name    : BirkhoffGlobalSection.local_inward_negative_not_stationary
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T22:39:18.162862+00:00
-- url     : https://prove2.me/theorems/92fc4712-cd94-4866-990e-dde51559d862
-- title:
--   Local inward negative not stationary
-- statement:
--   A real function vanishing at one, continuous there and strictly negative just to its left cannot have zero first derivative there if its second total derivative is positive.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Original auxiliary result from the accepted source Solutions/Sol_BirkhoffGlobalSection_radial_characteristic_bundle.lean:291. Exact quantified statement retained; foundational calculus and geometry are imported from Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Theorems.Thm_BirkhoffGlobalSection_convex_model_boundary_contact_positive
import Theorems.Thm_BirkhoffGlobalSection_weighted_radial_contact_exterior_derivative
import Theorems.Thm_BirkhoffGlobalSection_radial_rescaling_contact_pullback
import Theorems.Thm_BirkhoffGlobalSection_hamiltonian_radial_characteristic_normalization
import Theorems.Thm_BirkhoffGlobalSection_smooth_radial_gauge_chart
import Theorems.Thm_ConvexAnalysis_radial_derivative_pos_of_inward_negative
import Definitions.Def_BirkhoffGlobalSection_ContactVariationalInterfaces
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false




set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.local_inward_negative_not_stationary (f : ℝ → ℝ) (ε : ℝ)
    (hε : 0 < ε) (hc : ContinuousAt f 1) (hzero : f 1 = 0)
    (hneg : ∀ t : ℝ, 1 - ε ≤ t → t < 1 → f t < 0)
    (hsecond : 0 < deriv (deriv f) 1) : deriv f 1 ≠ 0 := by sorry
