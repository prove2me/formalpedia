-- Prove2me | Theorems.Thm_BKAR_BKARContDiff_continuous_comp_updateCoord
-- name    : BKAR.BKARContDiff.continuous_comp_updateCoord
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:23:48.879069+00:00
-- url     : https://prove2.me/theorems/463611fe-b2bd-55d7-a538-b036fd1c54f9
-- title:
--   BKARCont Diff: continuous comp update Coord
-- statement:
--   The BKARCont Diff construction uses the continuous comp update Coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L390-L394
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L390-L394

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

theorem BKAR.BKARContDiff.continuous_comp_updateCoord
    {ρ : (Edge V → ℝ) → ℝ} (hρ : BKARContDiff ρ)
    (x : Edge V → ℝ) (e : Edge V) :
    Continuous (fun t : ℝ => ρ (updateCoord x e t)) := by sorry
