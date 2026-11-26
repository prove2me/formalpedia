-- Prove2me | Theorems.Thm_BKARMirror_edgeSetGraph_reachable_iff_exists_isSimplePath
-- name    : BKARMirror.edgeSetGraph_reachable_iff_exists_isSimplePath
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:13:43.165385+00:00
-- url     : https://prove2.me/theorems/4c73922c-60af-54c9-9910-7164401cd090
-- title:
--   BKARMirror: edge Set Graph reachable iff exists is Simple Path
-- statement:
--   Reachability in `edgeSetGraph S` is the existence of a simple edge path.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/Audit/ForestFormula/SolutionBasic.lean#L179-L188
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/Audit/ForestFormula/SolutionBasic.lean#L179-L188

import Mathlib
import Definitions.Def_BKAR
import Definitions.Def_Audit_ForestFormula_SolutionBasic
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff
open BKARMirror
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V]

theorem BKARMirror.edgeSetGraph_reachable_iff_exists_isSimplePath
    (S : Finset (Edge V)) (i j : V) :
    (BKAR.EdgePath.edgeSetGraph S).Reachable i j ↔
      ∃ γ, BKAR.EdgePath.IsSimplePath S γ i j := by sorry
