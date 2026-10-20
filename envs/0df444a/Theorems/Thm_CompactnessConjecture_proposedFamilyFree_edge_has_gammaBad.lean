-- Prove2me | Theorems.Thm_CompactnessConjecture_proposedFamilyFree_edge_has_gammaBad
-- name    : CompactnessConjecture.proposedFamilyFree_edge_has_gammaBad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:37.072441+00:00
-- url     : https://prove2.me/theorems/16e93b21-792d-498a-bfab-90ea617c7d53
-- title:
--   CompactnessConjecture.proposedFamilyFree_edge_has_gammaBad
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem CompactnessConjecture.proposedFamilyFree_edge_has_gammaBad
    {n : ℕ} (host : SimpleGraph (Fin n))
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    {u v : Fin n}
    (hedge : host.Adj u v) :
    u ∈ gammaBadVertices host ∨ v ∈ gammaBadVertices host := by sorry
