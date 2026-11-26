-- Prove2me | Theorems.Thm_BKARMirror_mixedPartial_bridge
-- name    : BKARMirror.mixedPartial_bridge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:13:56.638124+00:00
-- url     : https://prove2.me/theorems/54cb92d2-cb79-5cd5-808a-fd8c89be460e
-- title:
--   BKARMirror: mixed Partial bridge
-- statement:
--   The forest mixed partial agrees with the mirror mixed partial.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/Audit/ForestFormula/SolutionBasic.lean#L287-L290
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/Audit/ForestFormula/SolutionBasic.lean#L287-L290

import Mathlib
import Definitions.Def_BKAR
import Definitions.Def_Audit_ForestFormula_SolutionBasic
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff
open BKARMirror
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKARMirror.mixedPartial_bridge (J : ForestIndex V)
    (data : BKAR.AcyclicEdgeSetData J.edges) (ρ : (Edge V → ℝ) → ℝ) :
    mixedPartial J ρ = (data.toForest).mixedPartial ρ := by sorry
