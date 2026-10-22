-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_hamiltonian_contact_frame_pairing
-- name    : BirkhoffGlobalSection.hamiltonian_contact_frame_pairing
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:18:01.806982+00:00
-- url     : https://prove2.me/theorems/5d6115c6-97f4-44ef-bf08-2d1f090dd66a
-- title:
--   Hamiltonian contact frame pairing
-- statement:
--   The two projected Hamiltonian contact-frame vectors have the displayed symplectic pairing in terms of gradient radius.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 4 of the Proved theorem BirkhoffGlobalSection.transverse_contact_frame_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_transverse_contact_frame_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_transverse_contact_frame_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.hamiltonian_contact_frame_pairing :
∀ (F : Phase → ℝ) (y : Phase)
    (hp : 0 < phaseRadialContact y (hamiltonianVectorField F y)),
    phaseSymplecticForm (hamiltonianContactFrame F y 0) (hamiltonianContactFrame F y 1) =
      -(zNormSq (TangentialHessian.grad F y) + wNormSq (TangentialHessian.grad F y)) := by sorry
