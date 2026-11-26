-- Prove2me | Theorems.Thm_BKAR_Forest_inSameComponent_of_edges_eq
-- name    : BKAR.Forest.inSameComponent_of_edges_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:40.282935+00:00
-- url     : https://prove2.me/theorems/0cd336b8-8b7f-59e3-bed8-02c0722bd6d9
-- title:
--   Forest: in Same Component of edges eq
-- statement:
--   The component relation is invariant under changing only the auxiliary path data.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L680-L685
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L680-L685

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

theorem BKAR.Forest.inSameComponent_of_edges_eq
    (F G : Forest V) (hedges : F.edges = G.edges)
    {i j : V} (h : F.inSameComponent i j) :
    G.inSameComponent i j := by sorry
