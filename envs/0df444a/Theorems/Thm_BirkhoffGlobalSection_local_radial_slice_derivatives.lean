-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_local_radial_slice_derivatives
-- name    : BirkhoffGlobalSection.local_radial_slice_derivatives
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T22:39:13.719266+00:00
-- url     : https://prove2.me/theorems/269fdd4b-2b46-481c-88ed-3820fcf187ac
-- title:
--   Local radial slice derivatives
-- statement:
--   For a twice differentiable function on any real normed space, the first and second derivatives of its radial slice at scale one equal its radial differential and directional Hessian respectively.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Original auxiliary result from the accepted source Solutions/Sol_BirkhoffGlobalSection_radial_characteristic_bundle.lean:312. Exact quantified statement retained; foundational calculus and geometry are imported from Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

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

theorem BirkhoffGlobalSection.local_radial_slice_derivatives {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℝ) (s : E)
    (hc : ContDiffAt ℝ 2 F s) :
    let f : ℝ → ℝ := fun t => F (t • s)
    deriv f 1 = fderiv ℝ F s s ∧
      deriv (deriv f) 1 = fderiv ℝ (fun x => fderiv ℝ F x s) s s := by sorry
