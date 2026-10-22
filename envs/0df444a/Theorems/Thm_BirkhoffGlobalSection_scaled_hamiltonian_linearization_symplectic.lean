-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_scaled_hamiltonian_linearization_symplectic
-- name    : BirkhoffGlobalSection.scaled_hamiltonian_linearization_symplectic
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:47:33.66817+00:00
-- url     : https://prove2.me/theorems/cd48b1f8-a127-4376-a3d5-49127b58ce6e
-- title:
--   Scaled hamiltonian linearization symplectic
-- statement:
--   The linearization of a differentiably scaled smooth Hamiltonian field is infinitesimally symplectic on vectors in the Hamiltonian differential kernel.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 5 of the Proved theorem BirkhoffGlobalSection.variational_symplecticity_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_variational_symplecticity_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_variational_symplecticity_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.scaled_hamiltonian_linearization_symplectic :
∀ (F b : Phase → ℝ) (y v w : Phase)
    (hF : ContDiffAt ℝ ∞ F y) (hb : DifferentiableAt ℝ b y)
    (hv : fderiv ℝ F y v = 0) (hw : fderiv ℝ F y w = 0),
    phaseSymplecticForm (fderiv ℝ (fun x => b x • hamiltonianVectorField F x) y v) w +
      phaseSymplecticForm v (fderiv ℝ (fun x => b x • hamiltonianVectorField F x) y w) = 0 := by sorry
