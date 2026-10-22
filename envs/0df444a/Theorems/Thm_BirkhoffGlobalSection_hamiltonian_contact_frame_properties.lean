-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_hamiltonian_contact_frame_properties
-- name    : BirkhoffGlobalSection.hamiltonian_contact_frame_properties
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:18:35.846988+00:00
-- url     : https://prove2.me/theorems/33c6ffe7-5506-4f95-af3d-198fa4fb8c8d
-- title:
--   Hamiltonian contact frame properties
-- statement:
--   Under a positive radial Hamiltonian derivative, the two contact-frame vectors satisfy the displayed energy tangency and zero-contact identities.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 5 of the Proved theorem BirkhoffGlobalSection.transverse_contact_frame_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_transverse_contact_frame_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_transverse_contact_frame_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.hamiltonian_contact_frame_properties :
∀ (F : Phase → ℝ) (y : Phase)
    (hp : 0 < phaseRadialContact y (hamiltonianVectorField F y)) (i : Fin 2),
    fderiv ℝ F y (hamiltonianContactFrame F y i) = 0 ∧
      phaseRadialContact y (hamiltonianContactFrame F y i) = 0 := by sorry
