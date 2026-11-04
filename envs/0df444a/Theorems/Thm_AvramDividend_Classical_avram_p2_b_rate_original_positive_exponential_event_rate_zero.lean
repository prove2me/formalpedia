-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_positive_exponential_event_rate_zero
-- name    : AvramDividend.Classical.avram_p2_b_rate_original_positive_exponential_event_rate_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:04:03.40861+00:00
-- url     : https://prove2.me/theorems/370951d5-c2a0-4fe5-a2f9-df94a6e6c066
-- title:
--   Original spectrally negative Lévy process has zero positive exponential-event small-time intensity
-- statement:
--   For every positive exponential threshold R>1 and nonnegative θ, the original Lévy process probability mass of exp(θ X_h)≥R, converted from ENNReal and divided by positive small h, tends to zero. This source-exact zero-positive-jump consequence follows from uniformly finite all-order exponential moments, a genuinely k-independent bound and an all-power squeezing theorem. It does not assume a jump compensator or Lévy rate.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_positive_event_all_k_real_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_eventual_all_power_tail_bounds_tendsto_zero

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_original_positive_exponential_event_rate_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : ∀ t : ℝ≥0, Measurable (X.X t))
    (θ R : ℝ) (hθ : 0 ≤ θ) (hR : 1 < R) :
    Tendsto (fun h : ℝ => ((P {ω | R ≤ Real.exp (θ * X.X (Real.toNNReal h) ω)}).toReal / h))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by sorry
