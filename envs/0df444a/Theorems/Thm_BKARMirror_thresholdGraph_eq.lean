-- Prove2me | Theorems.Thm_BKARMirror_thresholdGraph_eq
-- name    : BKARMirror.thresholdGraph_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:13:52.727369+00:00
-- url     : https://prove2.me/theorems/145b5b04-12b3-5349-930b-d799aebbcfb9
-- title:
--   BKARMirror: threshold Graph eq
-- statement:
--   The mirror threshold graph coincides with the repository threshold-edge
--   graph.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/Audit/ForestFormula/SolutionBasic.lean#L210-L225
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/Audit/ForestFormula/SolutionBasic.lean#L210-L225

import Mathlib
import Definitions.Def_BKAR
import Definitions.Def_Audit_ForestFormula_SolutionBasic
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff
open BKARMirror
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKARMirror.thresholdGraph_eq (J : ForestIndex V)
    (data : BKAR.AcyclicEdgeSetData J.edges)
    (u : {e : Edge V // e ∈ J.edges} → ℝ) (s : ℝ) :
    thresholdGraph J u s
      = BKAR.EdgePath.edgeSetGraph ((data.toForest).thresholdEdges u s) := by sorry
