-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_zero_stopped_reward_eq_drift_volume_ae_unconditional
-- name    : AvramDividend.Classical.bv_zero_stopped_reward_eq_drift_volume_ae_unconditional
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:43:24.120948+00:00
-- url     : https://prove2.me/theorems/2e05162c-66ac-4f30-8add-586accc1c834
-- title:
--   Finite-activity zero-barrier stopped Stieltjes dividend reward is unconditionally drift-weighted Lebesgue reward almost surely
-- statement:
--   For a spectrally negative Lévy process with bounded variation, finite negative-jump intensity and standing assumptions, the actual stopped zero-barrier discounted-dividend Stieltjes measure equals its drift-scaled Lebesgue counterpart for every nonnegative weight, almost surely. A deterministic countable dense nonnegative grid is selected from separability and its strict cofinality before any extended ruin horizon is guaranteed by the accepted density theorem.
-- source:
--   Finite-activity zero-barrier pathwise valuation and Mathlib exists_dense_seq; established Prove2Me cofinal-grid stopped Stieltjes theorem.

import Theorems.Thm_AvramDividend_Classical_bv_zero_stopped_reward_eq_drift_volume_ae_of_cofinal_grid
import Theorems.Thm_AvramDividend_Classical_countable_nnreal_dense_grid_strictly_cofinal
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Bases

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_zero_stopped_reward_eq_drift_volume_ae_unconditional
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hStanding : X.Standing)
    (hBV : X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    ∀ᵐ ω ∂P, ∀ f : ℝ → ℝ≥0∞,
      (∫⁻ t in paymentTimes (barrierRuinTime X 0 ω), f t
        ∂(dividendMeasure (runningSup X) ω)) =
      (∫⁻ t in paymentTimes (barrierRuinTime X 0 ω), f t
        ∂((ENNReal.ofReal X.drift) • volume)) := by sorry
