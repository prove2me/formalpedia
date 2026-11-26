-- Prove2me | Theorems.Thm_BKAR_Forest_pathMin_continuous_comp
-- name    : BKAR.Forest.pathMin_continuous_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:23:45.577722+00:00
-- url     : https://prove2.me/theorems/c254f625-a7ce-451b-84da-17e05b314301
-- title:
--   Forest: path Min continuous comp
-- statement:
--   The Forest construction uses the path Min continuous comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L347-L357
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L347-L357

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.List.GetD
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Smoothness
set_option autoImplicit false
open scoped ContDiff
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest
variable (F : Forest V)

theorem BKAR.Forest.pathMin_continuous_comp
    {X : Type*} [TopologicalSpace X] {uPath : X → F.EdgeParam → ℝ}
    (hu : Continuous uPath) (γ : List (Edge V)) :
    Continuous (fun x : X => F.pathMin (uPath x) γ) := by sorry
