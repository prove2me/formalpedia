-- Prove2me | Theorems.Thm_CompactnessConjecture_familyExtremal_real_le_of_forall_free
-- name    : CompactnessConjecture.familyExtremal_real_le_of_forall_free
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:37.975989+00:00
-- url     : https://prove2.me/theorems/194a9f05-bba7-4e1d-bbef-9f0bb39dc2c3
-- title:
--   CompactnessConjecture.familyExtremal_real_le_of_forall_free
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Filter Finset SimpleGraph
open scoped Classical Topology

theorem CompactnessConjecture.familyExtremal_real_le_of_forall_free
    (family : Finset FiniteGraph) (n : ℕ)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hfree : ∀ host : SimpleGraph (Fin n),
      FamilyFree family host →
        (host.edgeFinset.card : ℝ) ≤ bound) :
    (familyExtremal family n : ℝ) ≤ bound := by sorry
