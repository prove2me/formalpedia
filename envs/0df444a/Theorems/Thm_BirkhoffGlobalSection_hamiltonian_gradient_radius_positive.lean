-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_hamiltonian_gradient_radius_positive
-- name    : BirkhoffGlobalSection.hamiltonian_gradient_radius_positive
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:18:14.868001+00:00
-- url     : https://prove2.me/theorems/1985e273-4454-4b01-838e-b8211153d457
-- title:
--   Hamiltonian gradient radius positive
-- statement:
--   A positive radial Hamiltonian derivative forces the Hamiltonian gradient's squared radius to be positive.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 7 of the Proved theorem BirkhoffGlobalSection.transverse_contact_frame_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_transverse_contact_frame_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_transverse_contact_frame_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.hamiltonian_gradient_radius_positive :
∀ (F : Phase → ℝ) (y : Phase)
    (hp : 0 < phaseRadialContact y (hamiltonianVectorField F y)),
    0 < zNormSq (TangentialHessian.grad F y) + wNormSq (TangentialHessian.grad F y) := by sorry
