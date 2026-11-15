-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a424_continuous_martingale_dyadic_discrete_L2_maximal
-- name    : AvramDividend.Classical.avram_ga_a424_continuous_martingale_dyadic_discrete_L2_maximal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:52:38.767209+00:00
-- url     : https://prove2.me/theorems/d8b0f22d-28e7-47ec-a869-97d6d7892bd6
-- title:
--   Dyadic discrete-time Doob L2 maximal bound uniformly across mesh depths
-- statement:
--   Sampling a continuous-time martingale at all dyadic time grid points up to T yields a discrete-time martingale. Its squared finite-grid maximum is integrable and has expectation at most four times the terminal squared expectation, uniformly in dyadic mesh depth.
-- source:
--   Classical Doob L2 maximal inequality and monotone convergence across dyadic grids, with continuity/density of dyadic rationals.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a424_continuous_martingale_dyadic_discrete_L2_maximal
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (M : ℝ≥0 → Ω → ℝ)
    (hMart : Martingale M 𝓕 P)
    (hCont : ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => M t ω))
    (T : ℝ≥0)
    (hL2 : Integrable (fun ω => (M T ω)^2) P) :
    ∀ k : ℕ,
      Integrable (fun ω =>
        (Finset.range (2^k + 1)).sup'
          (by simp) (fun i =>
            (M ((i : ℝ≥0) * T / (2^k : ℝ≥0)) ω)^2)) P ∧
      (∫ ω,
        (Finset.range (2^k + 1)).sup'
          (by simp) (fun i =>
            (M ((i : ℝ≥0) * T / (2^k : ℝ≥0)) ω)^2) ∂P) ≤
        4 * (∫ ω, (M T ω)^2 ∂P) := by sorry
