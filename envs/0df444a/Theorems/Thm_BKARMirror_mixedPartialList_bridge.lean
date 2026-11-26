-- Prove2me | Theorems.Thm_BKARMirror_mixedPartialList_bridge
-- name    : BKARMirror.mixedPartialList_bridge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:15:11.345045+00:00
-- url     : https://prove2.me/theorems/84715a0e-e05b-43fc-af51-55ed3ac29371
-- title:
--   BKARMirror: mixed Partial List bridge
-- statement:
--   Q3: the mirror iterated mixed partial coincides with the repository one.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/Audit/ForestFormula/SolutionBasic.lean#L276-L284
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/Audit/ForestFormula/SolutionBasic.lean#L276-L284

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

theorem BKARMirror.mixedPartialList_bridge :
    ∀ (l : List (Edge V)) (ρ : (Edge V → ℝ) → ℝ),
      mixedPartialList l ρ = BKAR.mixedPartialList l ρ
  := by sorry
