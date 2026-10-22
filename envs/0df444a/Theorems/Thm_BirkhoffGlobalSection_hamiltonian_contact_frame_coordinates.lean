-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_hamiltonian_contact_frame_coordinates
-- name    : BirkhoffGlobalSection.hamiltonian_contact_frame_coordinates
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:18:05.209351+00:00
-- url     : https://prove2.me/theorems/73670941-cb8f-435d-80fb-180fde01ced6
-- title:
--   Hamiltonian contact frame coordinates
-- statement:
--   A vector in the energy and contact kernels has the displayed pairings with the Hamiltonian contact frame and its transverse coordinates.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 6 of the Proved theorem BirkhoffGlobalSection.transverse_contact_frame_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_transverse_contact_frame_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_transverse_contact_frame_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.hamiltonian_contact_frame_coordinates :
∀ (F : Phase → ℝ) (y : Phase)
    (hp : 0 < phaseRadialContact y (hamiltonianVectorField F y)),
    let n := zNormSq (TangentialHessian.grad F y) + wNormSq (TangentialHessian.grad F y)
    transverseFrameCoordinates (TangentialHessian.grad F y) (hamiltonianContactFrame F y 0) = ![n, 0] ∧
    transverseFrameCoordinates (TangentialHessian.grad F y) (hamiltonianContactFrame F y 1) = ![0, n] := by sorry
