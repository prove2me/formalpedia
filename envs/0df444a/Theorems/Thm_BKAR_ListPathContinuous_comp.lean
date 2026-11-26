-- Prove2me | Theorems.Thm_BKAR_ListPathContinuous_comp
-- name    : BKAR.ListPathContinuous.comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:22:37.189736+00:00
-- url     : https://prove2.me/theorems/1ef60f36-5c4e-536c-8ff3-91949f5b38bb
-- title:
--   List Path Continuous: comp
-- statement:
--   The List Path Continuous construction uses the comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L158-L166
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L158-L166

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
open BKAR.ListPathContinuous

theorem BKAR.ListPathContinuous.comp {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {n : Nat} {tsPath : X → List ℝ}
    (hts : ListPathContinuous n tsPath) {f : Y → X} (hf : Continuous f) :
    ListPathContinuous n (fun y : Y => tsPath (f y)) := by sorry
