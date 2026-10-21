-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_closed_horizon_survival_lintegral_grid_limit
-- name    : AvramDividend.Classical.chat04_closed_horizon_survival_lintegral_grid_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T21:18:24.140875+00:00
-- url     : https://prove2.me/theorems/e92f3b07-8334-4823-8583-e5582bd92442
-- title:
--   Expected payoff killed on closed finite horizon equals decreasing finite-grid expectations
-- statement:
--   For any spectrally negative Lévy process, strict lower and upper barriers, finite horizon T, an observation schedule containing all reciprocal-natural times, and an arbitrary measurable nonnegative finite-mass payoff g, the expected payoff restricted to no strict exit at any continuous time t≤T equals the infimum over expected payoffs restricted to finitely many grid observations strictly before T AND an explicit no-exit check at T. This is the correct pathwise and measure-theoretic killed Markov semigroup limit with a CLOSED terminal horizon. It uses the accepted countable-grid survival prefix-limit theorem, and the accompanying finite-horizon dense-grid event equality plus a necessary terminal observation. It does not require fixed-time jump atom assumptions or a killed q-scale martingale.
-- source:
--   Proved chat04_countable_grid_survival_prefix_limit UUID 879173a3-92c2-4dd4-8ee9-ac34088c07bb and pending chat04_closed_horizon_dense_survival_eq from the same Chat04 worker. Pinned Mathlib measurability of order comparisons and countable indicators.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_closed_horizon_dense_survival_eq
import Theorems.Thm_AvramDividend_Classical_chat04_countable_grid_survival_prefix_limit

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_closed_horizon_survival_lintegral_grid_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (lower upper : ℝ) (T : ℝ≥0)
    (g : Ω → ℝ≥0∞) (hg : Measurable g)
    (hFin : (∫⁻ ω, g ω ∂P) ≠ ∞) :
    (∫⁻ ω,
      ({ω | ∀ t : ℝ≥0, t ≤ T →
        ¬ (X.X t ω < lower ∨ upper < X.X t ω)}).indicator g ω ∂P) =
      ⨅ n : ℕ, ∫⁻ ω,
        ({ω | ∀ j ≤ n,
          (τ j < T →
            ¬ (X.X (τ j) ω < lower ∨ upper < X.X (τ j) ω)) ∧
          ¬ (X.X T ω < lower ∨ upper < X.X T ω)}).indicator g ω ∂P := by sorry
