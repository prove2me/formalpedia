-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_radial_state_homeomorph
-- name    : BirkhoffGlobalSection.convex_model_radial_state_homeomorph
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T22:39:13.734226+00:00
-- url     : https://prove2.me/theorems/327854ef-3b36-468c-b667-5b15e7778dca
-- title:
--   Convex model radial state homeomorph
-- statement:
--   The inverse-gauge radial map gives a homeomorphism from the unit three-sphere to the convex model state space, with inverse radial normalization.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Original auxiliary result from the accepted source Solutions/Sol_BirkhoffGlobalSection_convex_model_complete_sphere_reeb_flow.lean:79. Exact quantified statement retained; foundational calculus and geometry are imported from Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Theorems.Thm_BirkhoffGlobalSection_convex_model_complete_normalized_flow_of_model_fields
import Theorems.Thm_BirkhoffGlobalSection_convex_model_sphere_reeb_transport_of_model_fields
import Theorems.Thm_BirkhoffGlobalSection_convex_model_smooth_radial_chart
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

open BirkhoffGlobalSection Set
open scoped Topology ContDiff


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_radial_state_homeomorph {μ c : ℝ} (M : ConvexRegularizationModel μ c) :
    ∃ e : {u : Phase // u ∈ unitThreeSphere} ≃ₜ ConvexModelState M,
      (∀ u, (e u : Phase) = (gauge M.body (u : Phase))⁻¹ • (u : Phase)) ∧
      (∀ y, (e.symm y : Phase) = radialNormalize (y : Phase)) := by sorry
