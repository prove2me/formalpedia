-- Prove2me | Theorems.Thm_BKAR_AcyclicEdgeSetData_inSameComponent_symm
-- name    : BKAR.AcyclicEdgeSetData.inSameComponent_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:33.208424+00:00
-- url     : https://prove2.me/theorems/389f4f8e-d4f7-5924-8f40-ae46cd018ffb
-- title:
--   Acyclic Edge Set Data: in Same Component symm
-- statement:
--   The Acyclic Edge Set Data construction uses the in Same Component symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L380-L386
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L380-L386

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Sym.Sym2
import Definitions.Def_BKAR_Forest
set_option autoImplicit false
open BKAR
open BKAR.AcyclicEdgeSetData
variable {V} [Fintype V] [DecidableEq V]

theorem BKAR.AcyclicEdgeSetData.inSameComponent_symm
    {S : Finset (Edge V)} (data : AcyclicEdgeSetData S)
    {i j : V} (h : data.inSameComponent i j) :
    data.inSameComponent j i := by sorry
