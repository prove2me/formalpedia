-- Prove2me | Theorems.Thm_BKAR_BKARContDiff_intervalIntegrable_comp_updateCoord
-- name    : BKAR.BKARContDiff.intervalIntegrable_comp_updateCoord
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:26:32.595415+00:00
-- url     : https://prove2.me/theorems/aa5901eb-449d-4b7f-a3bf-620674c3be51
-- title:
--   BKARCont Diff: interval Integrable comp update Coord
-- statement:
--   The BKARCont Diff construction uses the interval Integrable comp update Coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L396-L402
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L396-L402

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

theorem BKAR.BKARContDiff.intervalIntegrable_comp_updateCoord
    {ρ : (Edge V → ℝ) → ℝ}
    (hρ : BKARContDiff ρ) (x : Edge V → ℝ) (e : Edge V)
    (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => ρ (updateCoord x e t))
      MeasureTheory.volume a b := by sorry
