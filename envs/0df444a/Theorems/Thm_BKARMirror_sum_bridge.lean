-- Prove2me | Theorems.Thm_BKARMirror_sum_bridge
-- name    : BKARMirror.sum_bridge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:15:16.371145+00:00
-- url     : https://prove2.me/theorems/5654c9be-1280-4b8b-8b78-20cf6543466f
-- title:
--   BKARMirror: sum bridge
-- statement:
--   **Sum bridge.**  Transport the mirror sum to the repository sum via `indexEquiv`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/Audit/ForestFormula/SolutionBasic.lean#L328-L335
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/Audit/ForestFormula/SolutionBasic.lean#L328-L335

import Mathlib
import Definitions.Def_BKAR
import Definitions.Def_Audit_ForestFormula_SolutionBasic
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff
open BKARMirror
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKARMirror.sum_bridge (ρ : (Edge V → ℝ) → ℝ) (hρ : ContDiffHyp ρ) :
    (∑ J : ForestIndex V, cubeContribution J ρ) =
      ∑ I : BKAR.ForestIndex V, I.cubeContribution ρ := by sorry
