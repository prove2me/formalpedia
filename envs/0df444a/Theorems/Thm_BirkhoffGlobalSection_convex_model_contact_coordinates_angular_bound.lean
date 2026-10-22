-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_contact_coordinates_angular_bound
-- name    : BirkhoffGlobalSection.convex_model_contact_coordinates_angular_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:43:27.040983+00:00
-- url     : https://prove2.me/theorems/f946afd4-7284-47c4-8ba9-fd2e22fc33e8
-- title:
--   Convex model contact coordinates angular bound
-- statement:
--   The displayed transverse-coordinate angular bound transfers to normalized convex model contact coordinates via their positive scalar relation.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 8 of the Proved theorem BirkhoffGlobalSection.contact_frame_angle_disk_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_frame_angle_disk_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_angle_disk_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_contact_coordinates_angular_bound :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q v : ℝ → Phase) (T B : ℝ)
    (hq : ∀ t, q t ∈ unitThreeSphere)
    (hbound : ∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧
        transverseFrameCoordinates
          (TangentialHessian.grad M.modelHamiltonian ((gauge M.body (q t))⁻¹ • q t))
          (fderiv ℝ (fun x : Phase => (gauge M.body x)⁻¹ • x) (q t) (v t)) =
            ![r * Real.cos (θ t), r * Real.sin (θ t)]) → B < θ T - θ 0),
    ∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧ convexModelContactCoordinates M (q t) (v t) =
        ![r * Real.cos (θ t), r * Real.sin (θ t)]) → B < θ T - θ 0 := by sorry
