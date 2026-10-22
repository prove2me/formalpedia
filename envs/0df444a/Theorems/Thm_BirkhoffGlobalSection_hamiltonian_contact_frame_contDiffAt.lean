-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_hamiltonian_contact_frame_contDiffAt
-- name    : BirkhoffGlobalSection.hamiltonian_contact_frame_contDiffAt
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:39:04.029959+00:00
-- url     : https://prove2.me/theorems/664a85f3-af46-4d45-a356-2906aa6295d6
-- title:
--   Hamiltonian contact frame contDiffAt
-- statement:
--   A Hamiltonian contact frame is smooth where the Hamiltonian is smooth and its radial differential denominator is nonzero.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 8 of the Proved theorem BirkhoffGlobalSection.contact_frame_basis_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_frame_basis_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_basis_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.hamiltonian_contact_frame_contDiffAt :
∀ (F : Phase → ℝ) (y : Phase)
    (hF : ContDiffAt ℝ ∞ F y)
    (hp : 0 < phaseRadialContact y (hamiltonianVectorField F y)) (i : Fin 2),
    ContDiffAt ℝ ∞ (fun z => hamiltonianContactFrame F z i) y := by sorry
