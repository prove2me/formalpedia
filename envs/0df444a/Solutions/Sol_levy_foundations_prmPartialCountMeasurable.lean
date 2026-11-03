-- Prove2me | solution 1 for levy_foundations_prmPartialCountMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:44:13.454853+00:00
-- url     : https://prove2.me/submissions/d59d468e-9d9b-4b87-bb08-f5ad14aeb219

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_levy_foundations_prmPartialCount
import Theorems.Thm_levy_foundations_thinnedCountMeasurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (A : Set E) (n : ℕ)
    (hK : ∀ k, Measurable (K k))
    (hX : ∀ k j, Measurable (X k j))
    (hA : MeasurableSet A) :
    Measurable (LevyFoundations.prmPartialCount K X A n) := by
  change Measurable (fun ω =>
    ∑ k ∈ Finset.range (n + 1), LevyFoundations.thinnedCount K X A k ω)
  exact Finset.measurable_sum _ fun k _ =>
    levy_foundations_thinnedCountMeasurable K X A k (hK k) (hX k) hA
