-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_predictable_L2_linear_mark_factorisation
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_predictable_L2_linear_mark_factorisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:09:19.374063+00:00
-- url     : https://prove2.me/theorems/7fdb13aa-3cfc-4e45-b2ce-6f3c5398b904
-- title:
--   Exact actual-source deterministic L2 jump-mark energy factorisation for an L2 predictable coefficient
-- statement:
--   For the original spectrally negative Lévy process X, a coefficient g measurable for the original right-continuous predictable sigma algebra with finite quadratic physical-clock norm, and a mark set with finite true X.nu quadratic moment, the nested small-jump quadratic energy equals the product of the coefficient energy and the genuine Lévy mark second moment. In particular it is finite. This is the analytic deterministic compensator factorisation, not a stochastic isometry or an independent PRM construction.
-- source:
--   Algebraic square factorisation, ENNReal.ofReal_mul, lintegral_const_mul and lintegral_mul_const on the actual source X.nu and predictable physical clock.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_predictable_L2_linear_mark_factorisation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (g : ℝ≥0 × Ω → ℝ)
    (hgm : Measurable[𝓕.rightCont.predictable] g)
    (hgL2 : (∫⁻ p : ℝ≥0 × Ω,
      ENNReal.ofReal ((g p)^2) ∂μ) < ⊤)
    (B : Set ℝ)
    (hBmoment : (∫⁻ z in B,
      ENNReal.ofReal (z^2) ∂X.ν) < ⊤) :
    (∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B, ENNReal.ofReal ((g p * z)^2) ∂X.ν ∂μ) = (∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal ((g p)^2) ∂μ) * (∫⁻ z in B, ENNReal.ofReal (z^2) ∂X.ν) ∧
    (∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B, ENNReal.ofReal ((g p * z)^2) ∂X.ν ∂μ) < ⊤ := by sorry
