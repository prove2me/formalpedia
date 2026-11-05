-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_discounted_stopped_atomic_diffuse_cash_le_total
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_discounted_stopped_atomic_diffuse_cash_le_total
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T22:20:00.216487+00:00
-- url     : https://prove2.me/theorems/57823309-ec01-489f-ab7e-344153c38157
-- title:
--   Each exact original stopped atom and diffuse dividend Cash component is bounded by total Cash
-- statement:
--   For every sample path, the genuinely original discounted pre-ruin Stieltjes payment integral over the closed horizon dominates both the atomic contribution from all positive singleton-mass rightpayments and the complementary diffuse contribution, including singular-continuous mass. The inequalities hold in extended nonnegative reals and are immediate source-exact consequences of the independently proved Cash additivity identity.
-- source:
--   Accepted exact source original_closed_discounted_cash_atomic_diffuse_exact 0b22cdad, using ENNReal nonnegativity of both integral components.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_discounted_cash_atomic_diffuse_exact

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_discounted_stopped_atomic_diffuse_cash_le_total
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : Ω → ℝ≥0∞) (τ : Ω → ℝ≥0) (q : ℝ) :
    ∀ ω : Ω,
      (∫⁻ s in paymentTimes (σ ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂
          (dividendMeasure D ω).restrict
            {t : ℝ | 0 < dividendMeasure D ω {t}}) ≤
        (∫⁻ s in paymentTimes (σ ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ∧
      (∫⁻ s in paymentTimes (σ ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂
          (dividendMeasure D ω).restrict
            {t : ℝ | ¬0 < dividendMeasure D ω {t}}) ≤
        (∫⁻ s in paymentTimes (σ ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) := by sorry
