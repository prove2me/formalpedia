-- Prove2me | Theorems.Thm_BKARMirror_edgeGraph_eq
-- name    : BKARMirror.edgeGraph_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:15:14.754571+00:00
-- url     : https://prove2.me/theorems/b03b82c5-82ba-561d-8daf-00bf29b1a4eb
-- title:
--   BKARMirror: edge Graph eq
-- statement:
--   The mirror graph on an edge set is byte-identical to the repository's
--   `EdgePath.edgeSetGraph`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/Audit/ForestFormula/SolutionBasic.lean#L128-L129
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/Audit/ForestFormula/SolutionBasic.lean#L128-L129

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

theorem BKARMirror.edgeGraph_eq (S : Finset (Edge V)) :
    edgeGraph S = BKAR.EdgePath.edgeSetGraph S := by sorry
