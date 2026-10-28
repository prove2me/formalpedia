-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_stoppedHistory_gridFutureReward_fibre_measurable
-- name    : AvramDividend.Classical.levy_stoppedHistory_gridFutureReward_fibre_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T12:08:09.416981+00:00
-- url     : https://prove2.me/theorems/2c2cd046-3146-460f-bbc8-656886400292
-- title:
--   Stopped-history fibre weighted by a measurable future Lévy path reward is measurable
-- statement:
--   For an adapted upper-grid approximation to a Lévy stopping time, the product of a stopped-past event and any measurable nonnegative whole-future-path reward is a measurable integrand on each deterministic grid fibre. This supplies the integrand measurability required by the finite-grid integral decomposition, and therefore the precise finite-grid strong-Markov factorisation.
-- source:
--   Direct prerequisite for AvramDividend.Classical.finiteGrid_stoppedReward_lintegral_decomposition (d7b9d4a5-11f7-49f0-8415-4da63551b075), on the path to strong Markov 61930a38-11f1-449e-bbb6-67d59c6d5ca8 and W-free barrier child 79978d61-9d1f-4b20-b8a5-114797a8e380; uses proved stopped fibre adaptedness ddc5c663-4003-4dfd-aaf7-c2d390b54283 and adapted process coordinates.

import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_stoppedEvent_upperGridFibre_measurable

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_stoppedHistory_gridFutureReward_fibre_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (τn : ℕ → Ω → ℝ≥0)
    (habove : ∀ ω n, τ ω ≤ τn n ω)
    (hfibres : ∀ n s,
      MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s})
    (n : ℕ) (s : ℝ≥0)
    (g : (ℝ≥0 → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    Measurable
      (Set.indicator (A ∩ {ω : Ω | τn n ω = s})
        (fun ω => g (fun t : ℝ≥0 =>
          X.X (s + t) ω - X.X s ω))) := by
  sorry
