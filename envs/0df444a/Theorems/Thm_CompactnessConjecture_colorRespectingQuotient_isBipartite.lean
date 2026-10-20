-- Prove2me | Theorems.Thm_CompactnessConjecture_colorRespectingQuotient_isBipartite
-- name    : CompactnessConjecture.colorRespectingQuotient_isBipartite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:39.087222+00:00
-- url     : https://prove2.me/theorems/319f8a15-ce4f-47e2-befe-94b6288a67cb
-- title:
--   CompactnessConjecture.colorRespectingQuotient_isBipartite
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph

theorem CompactnessConjecture.colorRespectingQuotient_isBipartite
    {V : Type*} (graph : SimpleGraph V) (color : V → Bool)
    (hproper : ∀ ⦃u v : V⦄, graph.Adj u v → color u ≠ color v)
    (f : V → V) (hf : ColorRespecting color f) :
    (quotientGraph graph f).IsBipartite := by sorry
