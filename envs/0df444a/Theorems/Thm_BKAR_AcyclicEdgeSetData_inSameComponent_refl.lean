-- Prove2me | Theorems.Thm_BKAR_AcyclicEdgeSetData_inSameComponent_refl
-- name    : BKAR.AcyclicEdgeSetData.inSameComponent_refl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:03:02.338043+00:00
-- url     : https://prove2.me/theorems/0ceb1214-dd36-5405-a8b2-6cec0e34cc21
-- title:
--   Acyclic Edge Set Data: in Same Component refl
-- statement:
--   The Acyclic Edge Set Data construction uses the in Same Component refl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L373-L378
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L373-L378

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

theorem BKAR.AcyclicEdgeSetData.inSameComponent_refl
    {S : Finset (Edge V)} (data : AcyclicEdgeSetData S)
    (i : V) :
    data.inSameComponent i i := by sorry
