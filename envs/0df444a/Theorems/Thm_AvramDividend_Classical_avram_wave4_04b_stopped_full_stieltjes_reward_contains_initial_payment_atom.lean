-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_stopped_full_stieltjes_reward_contains_initial_payment_atom
-- name    : AvramDividend.Classical.avram_wave4_04b_stopped_full_stieltjes_reward_contains_initial_payment_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:18:41.797985+00:00
-- url     : https://prove2.me/theorems/25b0a357-8d6a-4732-8406-7d6a89482f60
-- title:
--   The exact stopped full Stieltjes dividend reward always retains its time-zero right-payment atom
-- statement:
--   At every sample of an actual dividend strategy, the full finite-horizon stopped discounted Stieltjes reward integrates over a set containing t=0. Its mass is therefore at least the entire initial right-payment atom D⁺_0−D_0, with unit discount, regardless of the stopping horizon or nonnegative discount rate. Absolutely continuous and singular-continuous dividend mass remain in the integral.
-- source:
--   04-B full stopped Stieltjes reward, source time-zero dividend atom identity and chronological paymentTimes convention

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_stopped_full_stieltjes_reward_contains_initial_payment_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (τ : ℝ≥0∞) (q : ℝ) :
    ENNReal.ofReal (rightLimit D (0 : ℝ≥0) ω - D (0 : ℝ≥0) ω) ≤
      (∫⁻ s in paymentTimes τ ∩ Icc (0 : ℝ) (T : ℝ),
        ENNReal.ofReal (Real.exp (-q * s)) ∂dividendMeasure D ω) := by
  sorry
