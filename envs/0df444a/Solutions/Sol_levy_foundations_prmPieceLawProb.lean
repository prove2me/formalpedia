-- Prove2me | solution 1 for levy_foundations_prmPieceLawProb
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T00:01:51.717095+00:00
-- url     : https://prove2.me/submissions/66656acd-850e-460a-89e4-a8ba9742c6ff

import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Definitions.Def_levy_foundations_prmPiece
import Definitions.Def_levy_foundations_prmPieceLaw
import Theorems.Thm_levy_foundations_prmFinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

theorem solution
    {E : Type*} [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m] (k : ℕ) :
    IsProbabilityMeasure (LevyFoundations.prmPieceLaw m k) := by
  unfold LevyFoundations.prmPieceLaw
  split_ifs with h
  · infer_instance
  · refine ⟨?_⟩
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel h (levy_foundations_prmFinite m k).ne
