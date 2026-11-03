-- Prove2me | solution 1 for levy_foundations_measurablePRMEval
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T07:36:59.541221+00:00
-- url     : https://prove2.me/submissions/60e12e87-af81-4e64-a303-f85606fa7561

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_levy_foundations_poissonRandomMeasure
import Theorems.Thm_levy_foundations_poissonRandomMeasureApply
import Theorems.Thm_levy_foundations_thinnedCountMeasurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (hK : ∀ k, Measurable (K k))
    (hX : ∀ k n, Measurable (X k n))
    {A : Set E} (hA : MeasurableSet A) :
    Measurable (fun ω => LevyFoundations.poissonRandomMeasure K X ω A) := by
  simp_rw [levy_foundations_poissonRandomMeasureApply K X _ hA]
  refine Measurable.tsum fun k => ?_
  exact measurable_from_top.comp
    (levy_foundations_thinnedCountMeasurable K X A k (hK k) (hX k) hA)
