-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_right_endpoint_cash_lintegral_lower
-- name    : AvramDividend.Classical.avram_p3_2_original_right_endpoint_cash_lintegral_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:02:04.319811+00:00
-- url     : https://prove2.me/theorems/246b0a3d-4945-46a6-9696-0e35aba17f2d
-- title:
--   Original physical Stieltjes cash dominates right-endpoint discounted mass
-- statement:
--   For each actual original stopped mesh cell, the ENNReal Stieltjes dividend integral with one exponential discount dominates the original unweighted payment mass multiplied by the right-endpoint discount; no extra discount appears.
-- source:
--   Use monotonicity of exp(-q*t) on the actual Ioc stopped cell, ae_restrict_mem and lintegral_const_mul for the source dividendMeasure restricted to original paymentTimes.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_right_endpoint_cash_lintegral_lower
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) (m i : ℕ) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    let ν : Measure ℝ :=
      (dividendMeasure D ω).restrict (paymentTimes (ruinTime X x D ω))
    ENNReal.ofReal (Real.exp (-(q * (u (i + 1) : ℝ)))) *
      (∫⁻ t in Ioc (u i : ℝ) (u (i + 1) : ℝ),
        (1 : ℝ≥0∞) ∂ν) ≤
      (∫⁻ t in Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂ν):= by sorry
