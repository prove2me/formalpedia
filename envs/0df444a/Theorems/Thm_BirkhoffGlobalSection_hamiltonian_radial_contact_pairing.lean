-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_hamiltonian_radial_contact_pairing
-- name    : BirkhoffGlobalSection.hamiltonian_radial_contact_pairing
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:12:08.501058+00:00
-- url     : https://prove2.me/theorems/0f675e86-128d-482b-bbf7-9fc9680a62f7
-- title:
--   Hamiltonian radial contact pairing
-- statement:
--   The radial contact form evaluated on a Hamiltonian vector field equals one half of the radial derivative of its Hamiltonian.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 5 of the Proved theorem BirkhoffGlobalSection.radial_characteristic_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_radial_characteristic_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_radial_characteristic_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.hamiltonian_radial_contact_pairing :
∀ (F : Phase → ℝ) (y : Phase),
    phaseRadialContact y (hamiltonianVectorField F y) = fderiv ℝ F y y / 2 := by sorry
