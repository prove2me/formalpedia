-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_hamiltonian_quaternionic_transverse_tangent
-- name    : BirkhoffGlobalSection.hamiltonian_quaternionic_transverse_tangent
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:17:49.021522+00:00
-- url     : https://prove2.me/theorems/b4e89967-473a-4eba-8bd5-23b8539236aa
-- title:
--   Hamiltonian quaternionic transverse tangent
-- statement:
--   The quaternionic transverse vectors of a Hamiltonian gradient lie in the Hamiltonian differential kernel.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 2 of the Proved theorem BirkhoffGlobalSection.transverse_contact_frame_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_transverse_contact_frame_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_transverse_contact_frame_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.hamiltonian_quaternionic_transverse_tangent :
∀ (F : Phase → ℝ) (y : Phase),
    fderiv ℝ F y (TangentialHessian.frame (TangentialHessian.grad F y) 1) = 0 ∧
    fderiv ℝ F y (TangentialHessian.frame (TangentialHessian.grad F y) 2) = 0 := by sorry
