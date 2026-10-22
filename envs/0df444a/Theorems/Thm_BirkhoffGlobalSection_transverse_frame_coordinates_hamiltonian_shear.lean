-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_transverse_frame_coordinates_hamiltonian_shear
-- name    : BirkhoffGlobalSection.transverse_frame_coordinates_hamiltonian_shear
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:13:04.152987+00:00
-- url     : https://prove2.me/theorems/e1a5b7a7-677a-4f51-a985-f40286617331
-- title:
--   Transverse frame coordinates hamiltonian shear
-- statement:
--   Adding any scalar multiple of the Hamiltonian vector to a vector does not change its quaternionic transverse coordinates.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 1 of the Proved theorem BirkhoffGlobalSection.positive_time_change_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_positive_time_change_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_positive_time_change_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.transverse_frame_coordinates_hamiltonian_shear :
∀ (F : Phase → ℝ) (y w : Phase) (c : ℝ),
    transverseFrameCoordinates (TangentialHessian.grad F y)
      (w + c • hamiltonianVectorField F y) =
        transverseFrameCoordinates (TangentialHessian.grad F y) w := by sorry
