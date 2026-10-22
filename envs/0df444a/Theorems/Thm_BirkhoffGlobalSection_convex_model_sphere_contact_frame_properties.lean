-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_sphere_contact_frame_properties
-- name    : BirkhoffGlobalSection.convex_model_sphere_contact_frame_properties
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:18:17.655344+00:00
-- url     : https://prove2.me/theorems/4a3f3376-692f-4fba-94ed-fbcda25c38f7
-- title:
--   Convex model sphere contact frame properties
-- statement:
--   The pulled-back Hamiltonian contact frame of a convex model consists of sphere-tangent, zero-contact vectors.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 8 of the Proved theorem BirkhoffGlobalSection.transverse_contact_frame_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_transverse_contact_frame_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_transverse_contact_frame_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_sphere_contact_frame_properties :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere) (i : Fin 2),
    let v := convexModelSphereContactFrame M u i
    (u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0) ∧
      phaseRadialContact u v = 0 ∧
      fderiv ℝ (fun x : Phase => (gauge M.body x)⁻¹ • x) u v =
        hamiltonianContactFrame M.modelHamiltonian ((gauge M.body u)⁻¹ • u) i := by sorry
