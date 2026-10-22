-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_quaternionic_vector_reconstruction
-- name    : BirkhoffGlobalSection.quaternionic_vector_reconstruction
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:37:34.06992+00:00
-- url     : https://prove2.me/theorems/08f8b9f1-7146-4215-bacc-4b9a01c32c52
-- title:
--   Quaternionic vector reconstruction
-- statement:
--   The displayed quaternionic reconstruction expresses a vector from its pairings with a nonzero phase vector and the associated quaternionic basis, under the stated orthogonality conditions.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 2 of the Proved theorem BirkhoffGlobalSection.contact_frame_basis_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_frame_basis_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_basis_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.quaternionic_vector_reconstruction :
∀ (g v : Phase),
    (zNormSq g + wNormSq g) • v = (v ⬝ᵥ g) • g +
      (v ⬝ᵥ TangentialHessian.frame g 0) • TangentialHessian.frame g 0 +
      (v ⬝ᵥ TangentialHessian.frame g 1) • TangentialHessian.frame g 1 +
      (v ⬝ᵥ TangentialHessian.frame g 2) • TangentialHessian.frame g 2 := by sorry
