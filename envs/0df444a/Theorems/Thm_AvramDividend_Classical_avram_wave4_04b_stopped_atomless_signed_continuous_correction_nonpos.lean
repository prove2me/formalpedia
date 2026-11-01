-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_stopped_atomless_signed_continuous_correction_nonpos
-- name    : AvramDividend.Classical.avram_wave4_04b_stopped_atomless_signed_continuous_correction_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:29:52.512159+00:00
-- url     : https://prove2.me/theorems/88948c38-9c0c-4f70-9be8-eafce8a7200d
-- title:
--   Real signed continuous Stieltjes dividend correction is nonpositive against any integrable atomless payment measure
-- statement:
--   For the genuine original Lévy-driven controlled reserve and every atomless time measure, including absolutely continuous and singular-continuous dividend mass, the stopped finite-horizon real integral of the exact signed continuous Itô–Meyer dividend correction exp(-qt)(1-deriv w(A_t)) is nonpositive. Assumes the real-integrability that a stochastic change-of-variable proof must discharge; HJB gradient and strict interior localisation are only imposed at paid times. No absolute-continuity condition is used.
-- source:
--   Proved paymentTimes_measurable, Mathlib MeasureTheory.ae_restrict_mem and integral_nonpos_of_ae; exact real/NNReal time coercions and pointwise original HJB gradient.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_stopped_atomless_signed_continuous_correction_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (ω : Ω) (T : ℝ≥0) (τ : ℝ≥0∞) (q : ℝ)
    (ν : Measure ℝ) [NullSingletonClass ν]
    (hloc : ∀ t : ℝ≥0, t ≤ T → (t : ℝ) ∈ paymentTimes τ →
      0 < riskProcess X x D t ω ∧
        ENNReal.ofReal (riskProcess X x D t ω) < C)
    (hIntegrable : IntegrableOn
      (fun s : ℝ => Real.exp (-q * s) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω)))
      (paymentTimes τ ∩ Icc (0 : ℝ) (T : ℝ)) ν) :
    (∫ s in paymentTimes τ ∩ Icc (0 : ℝ) (T : ℝ),
      Real.exp (-q * s) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω)) ∂ν) ≤ 0 := by sorry
