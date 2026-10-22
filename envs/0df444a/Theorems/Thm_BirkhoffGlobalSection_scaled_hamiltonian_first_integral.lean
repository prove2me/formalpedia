-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_scaled_hamiltonian_first_integral
-- name    : BirkhoffGlobalSection.scaled_hamiltonian_first_integral
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:16:45.185042+00:00
-- url     : https://prove2.me/theorems/5505b7a3-ed8f-453d-8262-f470b89abf6c
-- title:
--   Scaled hamiltonian first integral
-- statement:
--   A Hamiltonian's differential annihilates every scalar multiple of its Hamiltonian vector field.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 1 of the Proved theorem BirkhoffGlobalSection.reverse_radial_variation_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_reverse_radial_variation_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_reverse_radial_variation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.scaled_hamiltonian_first_integral :
∀ (F b : Phase → ℝ) (y : Phase),
    fderiv ℝ F y (b y • hamiltonianVectorField F y) = 0 := by sorry
