-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_hamiltonian_vector_field_contDiffAt
-- name    : BirkhoffGlobalSection.hamiltonian_vector_field_contDiffAt
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:15:14.288999+00:00
-- url     : https://prove2.me/theorems/15d6847b-3b89-4bdf-b076-5e49c84d3156
-- title:
--   Hamiltonian vector field contDiffAt
-- statement:
--   A smooth Hamiltonian has a smooth Hamiltonian vector field at the same phase point.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 1 of the Proved theorem BirkhoffGlobalSection.model_contact_rate_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_model_contact_rate_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_model_contact_rate_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.hamiltonian_vector_field_contDiffAt :
∀ (F : Phase → ℝ) (y : Phase)
    (hF : ContDiffAt ℝ ∞ F y),
    ContDiffAt ℝ ∞ (hamiltonianVectorField F) y := by sorry
