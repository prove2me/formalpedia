-- Prove2me | Theorems.Thm_BKAR_updateCoord_contDiff
-- name    : BKAR.updateCoord_contDiff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:23:23.142832+00:00
-- url     : https://prove2.me/theorems/11ae2661-adaa-5ef8-b505-9d8d7f8d87a5
-- title:
--   BKAR: update Coord cont Diff
-- statement:
--   The BKAR construction uses the update Coord cont Diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L224-L227
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L224-L227

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

theorem BKAR.updateCoord_contDiff (x : Edge V → ℝ) (e : Edge V) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (updateCoord x e) := by sorry
