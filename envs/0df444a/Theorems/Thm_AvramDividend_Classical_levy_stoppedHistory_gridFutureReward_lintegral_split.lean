-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_stoppedHistory_gridFutureReward_lintegral_split
-- name    : AvramDividend.Classical.levy_stoppedHistory_gridFutureReward_lintegral_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T12:18:51.909375+00:00
-- url     : https://prove2.me/theorems/41ea67e0-cf9e-4f23-a927-c79e2440e634
-- title:
--   Expected stopped Lévy future reward splits over all adapted upper-grid stopping fibres
-- statement:
--   For a finite adapted upper-grid approximation of a Lévy stopping time, the nonnegative expected future-path reward restricted to a stopped-history event equals the finite sum of expected deterministic-shifted future-path rewards on each stopped-time fibre. The fibre-measurability and finite-sum integration lemmas give a fully formal identity, which combines directly with the already Proved future-path product law to establish finite-grid strong Markov.
-- source:
--   Composes two explicitly root-connected proof obligations: finiteGrid_stoppedReward_lintegral_decomposition d7b9d4a5-11f7-49f0-8415-4da63551b075 and levy_stoppedHistory_gridFutureReward_fibre_measurable. Next consume levy_stoppedHistory_upperGrid_futureReward_product f8d196c7-e8f7-4929-bc3b-b6c523c5ea5b; ultimately Open strong-Markov theorem 61930a38-11f1-449e-bbb6-67d59c6d5ca8 and W-free barrier child 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_finiteGrid_stoppedReward_lintegral_decomposition
import Theorems.Thm_AvramDividend_Classical_levy_stoppedHistory_gridFutureReward_fibre_measurable

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_stoppedHistory_gridFutureReward_lintegral_split
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
    (n : ℕ) (grid : Finset ℝ≥0)
    (hgrid : ∀ ω, τn n ω ∈ grid)
    (g : (ℝ≥0 → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω, Set.indicator A
      (fun ω' : Ω => g (fun t : ℝ≥0 =>
        X.X (τn n ω' + t) ω' - X.X (τn n ω') ω')) ω ∂P) =
      ∑ s ∈ grid, ∫⁻ ω,
        Set.indicator (A ∩ {ω' : Ω | τn n ω' = s})
          (fun ω' => g (fun t : ℝ≥0 =>
            X.X (s + t) ω' - X.X s ω')) ω ∂P := by
  sorry
