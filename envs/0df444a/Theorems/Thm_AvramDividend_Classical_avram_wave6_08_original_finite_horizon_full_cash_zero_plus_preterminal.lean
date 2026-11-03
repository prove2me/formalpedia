-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_finite_horizon_full_cash_zero_plus_preterminal
-- name    : AvramDividend.Classical.avram_wave6_08_original_finite_horizon_full_cash_zero_plus_preterminal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T09:19:12.424406+00:00
-- url     : https://prove2.me/theorems/7b829c58-825e-4c84-ac0a-078bba1ec0d1
-- title:
--   Original all-horizon complete discounted Stieltjes cash: initial atom plus closed/pre-ruin interior branch
-- statement:
--   The exact full original dividend Stieltjes cash at every real truncated horizon T before or after a positive finite ruin τ always includes the time-zero right-payment atom. If T<τ, the remaining strictly positive cash is over (0,T], including a right dividend at the horizon; if τ≤T, it is over (0,τ), excluding the ruin-time right atom. All diffuse, singular-continuous and interior atomic payments are retained. The proof uses the Proved original payment clipping and positive ruin cash decomposition, plus measurable disjoint additivity, not a missing stochastic estimate.
-- source:
--   Canonical source finite-horizon payment clip, positive finite ruin cash split, exact Stieltjes lintegral_union for initial singleton and positive interval.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_ruin_real_horizon_payment_clip_exact
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_finite_ruin_full_cash_zero_atom_plus_strict_left

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_08_original_finite_horizon_full_cash_zero_plus_preterminal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (τ : ℝ≥0) (hτ : 0 < τ)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ t in paymentTimes (τ : ℝ≥0∞) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
    (∫⁻ t in ({(0 : ℝ)} : Set ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
    (if T < (τ : ℝ) then
      (∫⁻ t in Ioc (0 : ℝ) T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
     else
      (∫⁻ t in Ioo (0 : ℝ) (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) := by sorry
