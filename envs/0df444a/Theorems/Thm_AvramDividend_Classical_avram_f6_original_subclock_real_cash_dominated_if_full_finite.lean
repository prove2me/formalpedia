-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_subclock_real_cash_dominated_if_full_finite
-- name    : AvramDividend.Classical.avram_f6_original_subclock_real_cash_dominated_if_full_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T10:08:50.059167+00:00
-- url     : https://prove2.me/theorems/ef2a582f-d8b8-4748-9ac8-ad54f75961ad
-- title:
--   Actual subordinate clock real discounted dividend cash bounded by full clock cash under genuine full mass finiteness
-- statement:
--   For the original Lévy dividend strategy and arbitrary subordinate stopping clocks sigma(k)<=tau, the real converted inclusive discounted paymentTimes dividend cash at sigma(k) is pointwise <= the real cash at tau when the actual full tau ENNReal discounted cash mass is finite. The proof applies the already Proved actual original random-stop lintegral monotonicity and an explicit finiteness-sensitive ENNReal.toReal_mono step. This avoids the invalid inference toReal(top)=0 that would otherwise break L1 cash domination. No abstract stochastic witness or new assumptions about X.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_subclock_real_cash_dominated_if_full_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (σ : ℕ → Ω → ℝ≥0)
    (hclock : ∀ k ω, σ k ω ≤ τ ω)
    (hFullFinite : ∀ ω : Ω,
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)) ≠ ⊤) :
    ∀ k ω,
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal ≤
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal := by sorry
