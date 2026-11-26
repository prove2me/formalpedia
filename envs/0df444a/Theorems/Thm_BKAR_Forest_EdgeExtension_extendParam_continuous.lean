-- Prove2me | Theorems.Thm_BKAR_Forest_EdgeExtension_extendParam_continuous
-- name    : BKAR.Forest.EdgeExtension.extendParam_continuous
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:26:14.297718+00:00
-- url     : https://prove2.me/theorems/f215e47c-9dfd-5d6f-a9a8-b3c10cf5a2f7
-- title:
--   Edge Extension: extend Param continuous
-- statement:
--   The Edge Extension construction uses the extend Param continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L233-L252
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L233-L252

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

theorem BKAR.Forest.EdgeExtension.extendParam_continuous (h : EdgeExtension F F' e)
    (u : F.EdgeParam → ℝ) :
    Continuous (fun t : ℝ => h.extendParam u t) := by sorry
