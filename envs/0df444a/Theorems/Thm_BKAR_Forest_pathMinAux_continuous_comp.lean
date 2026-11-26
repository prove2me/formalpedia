-- Prove2me | Theorems.Thm_BKAR_Forest_pathMinAux_continuous_comp
-- name    : BKAR.Forest.pathMinAux_continuous_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:23:45.147874+00:00
-- url     : https://prove2.me/theorems/97178903-122d-436e-ba07-f31947a0651a
-- title:
--   Forest: path Min Aux continuous comp
-- statement:
--   The Forest construction uses the path Min Aux continuous comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L330-L345
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L330-L345

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

theorem BKAR.Forest.pathMinAux_continuous_comp
    {X : Type*} [TopologicalSpace X] {uPath : X → F.EdgeParam → ℝ}
    (hu : Continuous uPath) {aPath : X → ℝ} (ha : Continuous aPath)
    (γ : List (Edge V)) :
    Continuous (fun x : X => F.pathMinAux (uPath x) (aPath x) γ) := by sorry
