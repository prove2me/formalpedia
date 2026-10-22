-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_quaternionic_transverse_pair
-- name    : BirkhoffGlobalSection.quaternionic_transverse_pair
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:17:38.595264+00:00
-- url     : https://prove2.me/theorems/38629f55-ab16-4803-ae95-af8e7ebe9d29
-- title:
--   Quaternionic transverse pair
-- statement:
--   The two standard quaternionic transverse vectors satisfy the displayed tangency, orthogonality and symplectic pairing identities for the supplied phase vector.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 1 of the Proved theorem BirkhoffGlobalSection.transverse_contact_frame_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_transverse_contact_frame_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_transverse_contact_frame_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.quaternionic_transverse_pair :
∀ (g : Phase),
    phaseSymplecticForm (TangentialHessian.frame g 1) (TangentialHessian.frame g 2) =
      -(zNormSq g + wNormSq g) ∧
    transverseFrameCoordinates g (TangentialHessian.frame g 1) = ![zNormSq g + wNormSq g, 0] ∧
    transverseFrameCoordinates g (TangentialHessian.frame g 2) = ![0, zNormSq g + wNormSq g] := by sorry
