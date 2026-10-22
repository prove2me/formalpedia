-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_sphere_contact_frame_pairing
-- name    : BirkhoffGlobalSection.convex_model_sphere_contact_frame_pairing
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:18:34.475994+00:00
-- url     : https://prove2.me/theorems/a1cc664b-7c65-44d8-a15a-0bc8625897a6
-- title:
--   Convex model sphere contact frame pairing
-- statement:
--   The two convex model sphere contact-frame vectors have the displayed weighted exterior pairing.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 9 of the Proved theorem BirkhoffGlobalSection.transverse_contact_frame_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_transverse_contact_frame_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_transverse_contact_frame_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_sphere_contact_frame_pairing :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere),
    let f : Phase → ℝ := fun x => ((gauge M.body x)⁻¹)^2
    let A := convexModelSphereContactFrame M u 0
    let B := convexModelSphereContactFrame M u 1
    let y := (gauge M.body u)⁻¹ • u
    fderiv ℝ (fun x => f x * phaseRadialContact x B) u A -
      fderiv ℝ (fun x => f x * phaseRadialContact x A) u B =
        zNormSq (TangentialHessian.grad M.modelHamiltonian y) +
          wNormSq (TangentialHessian.grad M.modelHamiltonian y) := by sorry
