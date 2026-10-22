-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_hamiltonian_symplectic_differential
-- name    : BirkhoffGlobalSection.hamiltonian_symplectic_differential
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:47:22.149775+00:00
-- url     : https://prove2.me/theorems/886bad40-8c0e-46fc-9fdc-54e5c878f04e
-- title:
--   Hamiltonian symplectic differential
-- statement:
--   The symplectic pairing of a Hamiltonian vector field with a phase vector equals the Hamiltonian differential applied to that vector.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 2 of the Proved theorem BirkhoffGlobalSection.variational_symplecticity_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_variational_symplecticity_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_variational_symplecticity_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.hamiltonian_symplectic_differential :
∀ (F : Phase → ℝ) (y v : Phase),
    phaseSymplecticForm (hamiltonianVectorField F y) v = fderiv ℝ F y v := by sorry
