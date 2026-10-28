-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_residual_zero_prefix_stieltjes_eq_volume
-- name    : AvramDividend.Classical.bv_actual_residual_zero_prefix_stieltjes_eq_volume
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:09:32.213149+00:00
-- url     : https://prove2.me/theorems/208020fc-70db-4af7-97a3-b9c6cb195c68
-- title:
--   Actual zero-residual Lévy survival prefix has exact drift-scaled Stieltjes payout
-- statement:
--   Under the original bounded-variation standing assumptions, on any sample path with no drift residual through T, the genuine running-supremum Stieltjes dividend measure on (0,T] agrees against every nonnegative reward integrand with drift-scaled Lebesgue measure. It is a direct application of the already-Proved zero-residual-prefix running-supremum theorem and the already-Proved drift-prefix Stieltjes measure identity. It connects the actual Lévy no-jump survival event to the exact stopped reward integrand of the zero-barrier valuation.
-- source:
--   Avram Palmowski Pistorius (2007), §3.3 first-jump reward; Proved BV zero-residual running-supremum and Stieltjes prefix identities.

import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_zero_prefix_runningSup_linear
import Theorems.Thm_AvramDividend_Classical_runningSup_drift_prefix_discounted_stieltjes_eq_scaled_volume
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Mathlib.Data.NNReal.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_residual_zero_prefix_stieltjes_eq_volume
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (ω : Ω) (T : ℝ) (hT : 0 ≤ T)
    (hHistory : ∀ s : ℝ≥0, s ≤ Real.toNNReal T →
      (s : ℝ) * X.drift - X.X s ω = 0)
    (f : ℝ → ℝ≥0∞) :
    (∫⁻ t in Ioc (0 : ℝ) T, f t ∂(dividendMeasure (runningSup X) ω)) =
    (∫⁻ t in Ioc (0 : ℝ) T, f t ∂((ENNReal.ofReal X.drift) • volume)) := by sorry
