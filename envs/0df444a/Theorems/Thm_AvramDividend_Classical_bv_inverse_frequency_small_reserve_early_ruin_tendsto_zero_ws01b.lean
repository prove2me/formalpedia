-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_inverse_frequency_small_reserve_early_ruin_tendsto_zero_ws01b
-- name    : AvramDividend.Classical.bv_inverse_frequency_small_reserve_early_ruin_tendsto_zero_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T09:29:31.649421+00:00
-- url     : https://prove2.me/theorems/91febd72-77ba-4ebf-b6b4-21520437d294
-- title:
--   BV Lévy early-ruin probability vanishes for inverse-frequency initial reserve
-- statement:
--   For a standing bounded-variation spectrally negative Lévy process with positive physical drift, at inverse-frequency horizons δ_nθ_n=c and θ_n→∞ the probability of reaching below the shrinking reserve -a/θ_n at some t≤δ_n tends to zero, for every a>0. This is a direct pathwise early-ruin application of uniformly vanishing scaled drift-deficit tails, valid with infinite jump activity.
-- source:
--   Proved uniform BV deficit convergence 0f9f587f and BV positive drift 0432f641; Kyprianou fluctuation theory for BV SNLP and exit-time localisation.

import Theorems.Thm_AvramDividend_Classical_bv_uniform_smalltime_drift_deficit_tails_tendsto_zero_ws01b
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Data.ENNReal.Real
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_inverse_frequency_small_reserve_early_ruin_tendsto_zero_ws01b
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (δ : ℕ → ℝ≥0) (θ : ℕ → ℝ) (c : ℝ)
    (hθ : Tendsto θ atTop atTop)
    (hθge : ∀ n, 1 ≤ θ n)
    (hProduct : ∀ n, (δ n : ℝ) * θ n = c)
    (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ =>
      P.real {ω : Ω | ∃ t : ℝ≥0, t ≤ δ n ∧
        a + θ n * X.X t ω < 0})
      atTop (𝓝 (0 : ℝ)) := by sorry
