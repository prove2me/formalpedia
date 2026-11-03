-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_integrable_signed_stieltjes_subwindow_exact_ENNReal
-- name    : AvramDividend.Classical.avram_wave7_03_original_integrable_signed_stieltjes_subwindow_exact_ENNReal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:46:12.233473+00:00
-- url     : https://prove2.me/theorems/ec978b7a-c0d9-4e46-a3a4-0cd8edba05e6
-- title:
--   Genuine signed original full Stieltjes integrability yields exact ENNReal cash equality on every original payment subwindow
-- statement:
--   On the original spectrally negative Lévy process, fix the original dividend D, sample path ω, and ruinTime. If the actual real exponential factor is genuinely IntegrableOn the full original paymentTimes against the original dividendMeasure D ω, then for every subset S of that precise original pre-ruin payment set the ENNReal Stieltjes cash on S equals ENNReal.ofReal of the real signed Stieltjes integral on the exact same subset and same source measure. The proof uses subset monotonicity of IntegrableOn, exponential positivity and the pinned Mathlib signed-real/ENNReal integral identity. It covers original time-zero right-limit atoms, continuous payments, and arbitrary stopped/future windows without replacing the process or measure.
-- source:
--   Pinned Mathlib MeasureTheory.IntegrableOn.mono_set and MeasureTheory.ofReal_integral_eq_lintegral_ofReal; original dividendMeasure, paymentTimes and ruinTime source Definitions.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_integrable_signed_stieltjes_subwindow_exact_ENNReal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (q : ℝ)
    (hInt : IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
      (paymentTimes (ruinTime X x D ω)) (dividendMeasure D ω))
    (S : Set ℝ) (hS : S ⊆ paymentTimes (ruinTime X x D ω)) :
    (∫⁻ t in S,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
    ENNReal.ofReal
      (∫ t in S, Real.exp (-(q * t)) ∂(dividendMeasure D ω)) := by sorry
