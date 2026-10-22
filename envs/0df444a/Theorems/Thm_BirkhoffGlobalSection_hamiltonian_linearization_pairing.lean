-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_hamiltonian_linearization_pairing
-- name    : BirkhoffGlobalSection.hamiltonian_linearization_pairing
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:47:28.134091+00:00
-- url     : https://prove2.me/theorems/1c7a4f9d-d1c5-4a85-9d0d-535790c5d01c
-- title:
--   Hamiltonian linearization pairing
-- statement:
--   For a smooth Hamiltonian, pairing its linearized Hamiltonian vector field with a vector equals the Hessian evaluated on the corresponding two vectors.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 3 of the Proved theorem BirkhoffGlobalSection.variational_symplecticity_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_variational_symplecticity_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_variational_symplecticity_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.hamiltonian_linearization_pairing :
∀ (F : Phase → ℝ) (y v w : Phase)
    (hF : ContDiffAt ℝ ∞ F y),
    phaseSymplecticForm (fderiv ℝ (hamiltonianVectorField F) y v) w =
      fderiv ℝ (fderiv ℝ F) y v w := by sorry
