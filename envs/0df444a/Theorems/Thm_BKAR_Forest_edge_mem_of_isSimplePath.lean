-- Prove2me | Theorems.Thm_BKAR_Forest_edge_mem_of_isSimplePath
-- name    : BKAR.Forest.edge_mem_of_isSimplePath
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:03:16.71415+00:00
-- url     : https://prove2.me/theorems/3b75b1a9-f244-4b45-bca9-26e3f82ee81c
-- title:
--   Forest: edge mem of is Simple Path
-- statement:
--   The Forest construction uses the edge mem of is Simple Path property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L642-L645
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L642-L645

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Sym.Sym2
import Definitions.Def_BKAR_Forest
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.edge_mem_of_isSimplePath (F : Forest V) {i j : V}
    {γ : List (Edge V)} (hγ : IsSimplePath F γ i j) :
    ∀ e ∈ γ, e ∈ F.edges := by sorry
