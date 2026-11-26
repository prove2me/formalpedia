-- Prove2me | Theorems.Thm_BKAR_AcyclicEdgeSetData_inSameComponent_trans
-- name    : BKAR.AcyclicEdgeSetData.inSameComponent_trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:04:55.443799+00:00
-- url     : https://prove2.me/theorems/e2da441a-792d-5776-8850-60617a77d763
-- title:
--   Acyclic Edge Set Data: in Same Component trans
-- statement:
--   The Acyclic Edge Set Data construction uses the in Same Component trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ForestGraph.lean#L306-L318
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ForestGraph.lean#L306-L318

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_ForestGraph
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.AcyclicEdgeSetData
open EdgePath
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.AcyclicEdgeSetData.inSameComponent_trans
    {S : Finset (Edge V)} (data : AcyclicEdgeSetData S)
    {i j k : V} (hij : data.inSameComponent i j)
    (hjk : data.inSameComponent j k) :
    data.inSameComponent i k := by sorry
