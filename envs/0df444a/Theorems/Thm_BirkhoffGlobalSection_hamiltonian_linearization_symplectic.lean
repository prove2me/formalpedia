-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_hamiltonian_linearization_symplectic
-- name    : BirkhoffGlobalSection.hamiltonian_linearization_symplectic
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:47:20.078977+00:00
-- url     : https://prove2.me/theorems/83046832-5bed-4033-a593-2a0782948405
-- title:
--   Hamiltonian linearization symplectic
-- statement:
--   The derivative of a smooth Hamiltonian vector field is infinitesimally symplectic: its two contributions to the derivative of a symplectic pairing sum to zero.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 4 of the Proved theorem BirkhoffGlobalSection.variational_symplecticity_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_variational_symplecticity_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_variational_symplecticity_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.hamiltonian_linearization_symplectic :
∀ (F : Phase → ℝ) (y v w : Phase)
    (hF : ContDiffAt ℝ ∞ F y),
    phaseSymplecticForm (fderiv ℝ (hamiltonianVectorField F) y v) w +
      phaseSymplecticForm v (fderiv ℝ (hamiltonianVectorField F) y w) = 0 := by sorry
