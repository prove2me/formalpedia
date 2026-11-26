-- Prove2me | Theorems.Thm_BKAR_Forest_standardInterp_continuous_comp
-- name    : BKAR.Forest.standardInterp_continuous_comp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:23:46.034802+00:00
-- url     : https://prove2.me/theorems/027ae5b4-f194-46e4-80aa-9e77b0f28b21
-- title:
--   Forest: standard Interp continuous comp
-- statement:
--   The Forest construction uses the standard Interp continuous comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L359-L379
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L359-L379

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

theorem BKAR.Forest.standardInterp_continuous_comp
    {X : Type*} [TopologicalSpace X] {uPath : X → F.EdgeParam → ℝ}
    (hu : Continuous uPath) :
    Continuous (fun x : X => F.standardInterp (uPath x)) := by sorry
