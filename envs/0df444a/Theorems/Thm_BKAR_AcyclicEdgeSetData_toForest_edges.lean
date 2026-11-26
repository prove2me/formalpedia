-- Prove2me | Theorems.Thm_BKAR_AcyclicEdgeSetData_toForest_edges
-- name    : BKAR.AcyclicEdgeSetData.toForest_edges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:04:57.436485+00:00
-- url     : https://prove2.me/theorems/2c48ddbf-d60c-58f1-a09f-85d93f36932b
-- title:
--   Acyclic Edge Set Data: to Forest edges
-- statement:
--   The Acyclic Edge Set Data construction uses the to Forest edges property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ForestGraph.lean#L399-L401
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ForestGraph.lean#L399-L401

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_ForestGraph
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.AcyclicEdgeSetData
open EdgePath
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.AcyclicEdgeSetData.toForest_edges {S : Finset (Edge V)} (data : AcyclicEdgeSetData S) :
    data.toForest.edges = S := by sorry
