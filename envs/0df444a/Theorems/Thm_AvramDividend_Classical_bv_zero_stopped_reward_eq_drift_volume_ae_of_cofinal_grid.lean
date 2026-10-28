-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_zero_stopped_reward_eq_drift_volume_ae_of_cofinal_grid
-- name    : AvramDividend.Classical.bv_zero_stopped_reward_eq_drift_volume_ae_of_cofinal_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T18:57:20.422163+00:00
-- url     : https://prove2.me/theorems/dfa4fca9-cad6-45e6-9ff8-92560048b381
-- title:
--   A cofinal grid upgrades surviving BV Stieltjes prefixes to the stopped dividend reward almost surely
-- statement:
--   For a bounded-variation spectrally negative Lévy process of finite jump intensity, any deterministic countable grid cofinal before each extended stopping horizon turns the almost-sure equality of all surviving weighted dividend-prefix integrals into almost-sure equality of the entire stopped dividend Stieltjes measure with the drift-scaled Lebesgue measure. The initial-time atom is correctly eliminated.
-- source:
--   Finite-activity Lévy pathwise drift pre-jump property; accepted countable-grid prefix and stopped Stieltjes union lemmas.

import Theorems.Thm_AvramDividend_Classical_bv_zero_surviving_stieltjes_countable_grid_ae
import Theorems.Thm_AvramDividend_Classical_zero_stopped_weighted_grid_prefixes_to_paymentTimes
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_zero_initial_atom
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_zero_stopped_reward_eq_drift_volume_ae_of_cofinal_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hStanding : X.Standing)
    (hBV : X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (grid : ℕ → ℝ≥0)
    (hcofinal : ∀ σ : ℝ≥0∞, ∀ t : ℝ, 0 < t → ENNReal.ofReal t < σ →
      ∃ n : ℕ, t ≤ (grid n : ℝ) ∧ (grid n : ℝ≥0∞) < σ) :
    ∀ᵐ ω ∂P, ∀ f : ℝ → ℝ≥0∞,
      (∫⁻ t in paymentTimes (barrierRuinTime X 0 ω), f t
        ∂(dividendMeasure (runningSup X) ω)) =
      (∫⁻ t in paymentTimes (barrierRuinTime X 0 ω), f t
        ∂((ENNReal.ofReal X.drift) • volume)) := by sorry
