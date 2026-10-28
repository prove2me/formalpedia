-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_restrictedPath_continuousReward_lintegral
-- name    : AvramDividend.Classical.levy_finiteStopping_restrictedPath_continuousReward_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:43:47.855976+00:00
-- url     : https://prove2.me/theorems/3075481a-89a4-4c24-b131-2afd90b66eea
-- title:
--   Strong-Markov lower integrals of stopped-history restricted future path laws
-- statement:
--   At every finite Lévy stopping time, the distribution of the entire shifted future path under the probability measure restricted to a stopped-history event has the same bounded continuous nonnegative test integrals as event probability times the original path law.
-- source:
--   Combines three already Proved canonical prerequisites: finite-stopping whole future-path measurability, measurability of stopped-history events, and finite-stopping strong-Markov scalar factorisation. Direct bridge to uniqueness of stopped-future-path measure and then canonical independence theorem 61930a38-11f1-449e-bbb6-67d59c6d5ca8.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_scalar_markov_no_meas_premise

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_finiteStopping_restrictedPath_continuousReward_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (g : (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hg : Continuous g) (hgm : Measurable g)
    (C : ℝ≥0∞) (hbound : ∀ y, g y ≤ C)
    (hfin : (∫⁻ _ : Ω, C ∂P) ≠ ∞) :
    (∫⁻ y, g y ∂(Measure.map
      (fun ω : Ω => fun t : ℝ≥0 =>
        X.X (τ ω + t) ω - X.X (τ ω) ω) (P.restrict A))) =
    P A * (∫⁻ y, g y ∂(Measure.map
      (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)) := by
  sorry
