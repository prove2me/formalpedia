-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_differential_dot_gradient
-- name    : BirkhoffGlobalSection.differential_dot_gradient
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:37:22.566476+00:00
-- url     : https://prove2.me/theorems/2a1b916f-3862-4b56-b370-b82ef6b3c39c
-- title:
--   Differential dot gradient
-- statement:
--   A phase-space function's Fréchet differential equals the coordinate pairing with its designated gradient.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 1 of the Proved theorem BirkhoffGlobalSection.contact_frame_basis_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_frame_basis_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_basis_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.differential_dot_gradient :
∀ (F : Phase → ℝ) (y v : Phase),
    fderiv ℝ F y v = v ⬝ᵥ TangentialHessian.grad F y := by sorry
