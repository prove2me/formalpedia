-- Prove2me | Theorems.Thm_BKAR_Forest_paramValue_continuous_comp
-- name    : BKAR.Forest.paramValue_continuous_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:23:09.718119+00:00
-- url     : https://prove2.me/theorems/411b16fa-a8dd-4e3e-913f-3de31de02d41
-- title:
--   Forest: param Value continuous comp
-- statement:
--   The Forest construction uses the param Value continuous comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L310-L328
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L310-L328

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

theorem BKAR.Forest.paramValue_continuous_comp
    {X : Type*} [TopologicalSpace X] {uPath : X → F.EdgeParam → ℝ}
    (hu : Continuous uPath) (e : Edge V) :
    Continuous (fun x : X => F.paramValue (uPath x) e) := by sorry
