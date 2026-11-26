-- Prove2me | Theorems.Thm_BKAR_Forest_EdgeExtension_extendParam_continuous_comp
-- name    : BKAR.Forest.EdgeExtension.extendParam_continuous_comp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:26:17.117299+00:00
-- url     : https://prove2.me/theorems/84c683fe-89b8-5416-8e59-af1b6157ba44
-- title:
--   Edge Extension: extend Param continuous comp
-- statement:
--   The Edge Extension construction uses the extend Param continuous comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L254-L278
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L254-L278

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
open BKAR.Forest BKAR.Forest.EdgeExtension
variable {F F' : Forest V} {e : Edge V}

theorem BKAR.Forest.EdgeExtension.extendParam_continuous_comp
    {X : Type*} [TopologicalSpace X] (h : EdgeExtension F F' e)
    {uPath : X → F.EdgeParam → ℝ} (hu : Continuous uPath)
    {tPath : X → ℝ} (ht : Continuous tPath) :
    Continuous (fun x : X => h.extendParam (uPath x) (tPath x)) := by sorry
