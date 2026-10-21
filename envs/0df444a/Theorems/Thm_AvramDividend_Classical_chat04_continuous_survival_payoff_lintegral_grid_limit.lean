-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_continuous_survival_payoff_lintegral_grid_limit
-- name    : AvramDividend.Classical.chat04_continuous_survival_payoff_lintegral_grid_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T09:54:40.703763+00:00
-- url     : https://prove2.me/theorems/43a842bb-4499-4db2-9452-e3c0b5240352
-- title:
--   Continuous-time strict survival payoff is the limit of finite-grid expectations
-- statement:
--   For any spectrally negative Lévy process, any countable deterministic observation schedule containing every reciprocal-natural-grid time k/n, a strict lower and upper barrier and any measurable nonnegative terminal payoff with finite ENNReal expectation, the expected payoff restricted to genuine continuous-time survival between both barriers equals the infimum of expected payoffs restricted to all finite prefixes of the observation schedule. The equality is sample-path exact and uses the previously accepted strict-exit density theorem and the accepted monotone finite-grid integral limit. It does not assume the killed q-scale martingale or erase undetected between-grid excursions.
-- source:
--   Accepted AvramDividend.Classical.chat04_countable_grid_strict_survival_event_eq UUID 2d1d4d5d-72ab-4e14-aedc-4018903df231 and chat04_countable_grid_survival_prefix_limit UUID 879173a3-92c2-4dd4-8ee9-ac34088c07bb.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_countable_grid_strict_survival_event_eq
import Theorems.Thm_AvramDividend_Classical_chat04_countable_grid_survival_prefix_limit

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_continuous_survival_payoff_lintegral_grid_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (lower upper : ℝ)
    (g : Ω → ℝ≥0∞) (hg : Measurable g)
    (hFin : (∫⁻ ω, g ω ∂P) ≠ ∞) :
    (∫⁻ ω,
      ({ω | ∀ t : ℝ≥0,
        ¬ (X.X t ω < lower ∨ upper < X.X t ω)}).indicator g ω ∂P) =
      ⨅ n : ℕ, ∫⁻ ω,
        ({ω | ∀ k ≤ n,
          ¬ (X.X (τ k) ω < lower ∨ upper < X.X (τ k) ω)}).indicator g ω ∂P := by sorry
