-- Prove2me | Theorems.Thm_BKAR_Forest_inSameComponent_iff_of_edges_eq
-- name    : BKAR.Forest.inSameComponent_iff_of_edges_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:03:26.413801+00:00
-- url     : https://prove2.me/theorems/13982751-be66-4cbe-a69f-f9a58952348a
-- title:
--   Forest: in Same Component iff of edges eq
-- statement:
--   The Forest construction uses the in Same Component iff of edges eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L687-L692
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L687-L692

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

theorem BKAR.Forest.inSameComponent_iff_of_edges_eq
    (F G : Forest V) (hedges : F.edges = G.edges)
    {i j : V} :
    F.inSameComponent i j ↔ G.inSameComponent i j := by sorry
