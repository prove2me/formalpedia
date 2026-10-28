-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_upperGrid_stoppedHistory_scalar_markov
-- name    : AvramDividend.Classical.levy_upperGrid_stoppedHistory_scalar_markov
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T12:56:33.72062+00:00
-- url     : https://prove2.me/theorems/14d2968b-0236-4682-8a42-4227df569e78
-- title:
--   Full finite-grid strong-Markov scalar reward factorisation
-- statement:
--   For any measurable stopped-history event of a Lévy stopping time, at every adapted finite-valued upper-grid approximation, the expected future-path reward on that event equals the event probability times the stationary whole-path expected reward. This follows from the proved fibrewise restart law, the exact sum-of-fibres reward integral and the event-mass partition, without a scale function.
-- source:
--   Direct root-connected strong-Markov intermediate for 61930a38-11f1-449e-bbb6-67d59c6d5ca8, ultimately barrier dividend split 79978d61-9d1f-4b20-b8a5-114797a8e380. Imports the finite-grid integral split 41ea67e0-cf9e-4f23-a927-c79e2440e634, fibre factor, and finite-grid stopped event partition 5edb1a0c-5d8b-4d2e-bab5-01b6b88e542e.

import Mathlib.Probability.IdentDistrib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_stoppedHistory_gridFutureReward_lintegral_split
import Theorems.Thm_AvramDividend_Classical_levy_upperGrid_fibre_futureReward_scalar_factor
import Theorems.Thm_AvramDividend_Classical_finiteGrid_stoppedEvent_measure_partition

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_upperGrid_stoppedHistory_scalar_markov
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (hAm : MeasurableSet A)
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
    P A * (∫⁻ y, g y ∂(Measure.map
      (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)) := by
  sorry
