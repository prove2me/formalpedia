-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_symplectic_contact_frame_reconstruction
-- name    : BirkhoffGlobalSection.convex_model_symplectic_contact_frame_reconstruction
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:41:12.307599+00:00
-- url     : https://prove2.me/theorems/4226da61-e6e9-4892-a455-6f775a130678
-- title:
--   Convex model symplectic contact frame reconstruction
-- statement:
--   Every sphere-contact vector has the displayed reconstruction in the normalized convex model symplectic contact frame.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 15 of the Proved theorem BirkhoffGlobalSection.contact_frame_basis_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_frame_basis_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_basis_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_symplectic_contact_frame_reconstruction :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u v : Phase) (hu : u ∈ unitThreeSphere)
    (hv : u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0)
    (hα : phaseRadialContact u v = 0),
    let G : Phase → Phase := fun x => (gauge M.body x)⁻¹ • x
    let c := transverseFrameCoordinates (TangentialHessian.grad M.modelHamiltonian (G u)) (fderiv ℝ G u v)
    v = (c 0 / Real.sqrt (convexModelFrameRadius M u)) • convexModelSymplecticContactFrame M u 0 +
      (c 1 / Real.sqrt (convexModelFrameRadius M u)) • convexModelSymplecticContactFrame M u 1 := by sorry
