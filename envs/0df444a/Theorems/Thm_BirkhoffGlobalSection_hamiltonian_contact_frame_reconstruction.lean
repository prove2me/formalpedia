-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_hamiltonian_contact_frame_reconstruction
-- name    : BirkhoffGlobalSection.hamiltonian_contact_frame_reconstruction
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:38:26.515984+00:00
-- url     : https://prove2.me/theorems/3a1c18e8-0a61-4297-98ba-564f795dbed7
-- title:
--   Hamiltonian contact frame reconstruction
-- statement:
--   A vector in the Hamiltonian energy and radial-contact kernels is reconstructed from the two contact-frame vectors and its displayed coordinate coefficients.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 4 of the Proved theorem BirkhoffGlobalSection.contact_frame_basis_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_frame_basis_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_basis_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.hamiltonian_contact_frame_reconstruction :
∀ (F : Phase → ℝ) (y v : Phase)
    (hp : 0 < phaseRadialContact y (hamiltonianVectorField F y))
    (hv : fderiv ℝ F y v = 0) (hα : phaseRadialContact y v = 0),
    let g := TangentialHessian.grad F y
    let n := zNormSq g + wNormSq g
    let c := transverseFrameCoordinates g v
    v = (c 0 / n) • hamiltonianContactFrame F y 0 +
      (c 1 / n) • hamiltonianContactFrame F y 1 := by sorry
