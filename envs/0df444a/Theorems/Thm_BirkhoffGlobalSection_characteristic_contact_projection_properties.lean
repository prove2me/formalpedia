-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_characteristic_contact_projection_properties
-- name    : BirkhoffGlobalSection.characteristic_contact_projection_properties
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:17:51.881265+00:00
-- url     : https://prove2.me/theorems/fa027b31-2fa5-41d9-b66a-3fbeaef911b2
-- title:
--   Characteristic contact projection properties
-- statement:
--   For a nonzero radial pairing, projection along the characteristic vector has the displayed energy-kernel and radial-contact-kernel properties.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 3 of the Proved theorem BirkhoffGlobalSection.transverse_contact_frame_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_transverse_contact_frame_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_transverse_contact_frame_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.characteristic_contact_projection_properties :
∀ (F : Phase → ℝ) (y v : Phase)
    (hp : 0 < phaseRadialContact y (hamiltonianVectorField F y))
    (hv : fderiv ℝ F y v = 0),
    phaseRadialContact y (characteristicContactProjection F y v) = 0 ∧
    fderiv ℝ F y (characteristicContactProjection F y v) = 0 ∧
    transverseFrameCoordinates (TangentialHessian.grad F y)
      (characteristicContactProjection F y v) =
        transverseFrameCoordinates (TangentialHessian.grad F y) v := by sorry
