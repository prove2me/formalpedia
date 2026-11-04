-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_finite_original_value_ae_random_strict_future_signed_ennreal_eq
-- name    : AvramDividend.Classical.avram_wave7_03_finite_original_value_ae_random_strict_future_signed_ennreal_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:09:09.7707+00:00
-- url     : https://prove2.me/theorems/20b6b583-c72c-40ef-8d5a-4f6f776fc474
-- title:
--   Finite canonical value makes real signed and ENNReal random strict-future Stieltjes cash exactly equal almost surely
-- statement:
--   With the original Lévy process, dividend strategy, P and dividendMeasure D ω, finiteness of the canonical dividendValue proves almost-sure exact equality between ENNReal.ofReal of the real discounted Stieltjes integral and the genuine ENNReal Stieltjes integral on the identical paymentTimes(ruinTime) ∩ Ioi(T ω) set, for any random real clock T. All continuous and subsequent right-limit jump dividends are included. The atom at T is excluded by Ioi. This bridges signed to nonnegative cash at the same measure and domain.
-- source:
--   Proved original unrestricted signed IntegrableOn theorem 3a9d20cb; pinned Mathlib IntegrableOn.mono for window restriction and ofReal_integral_eq_lintegral_ofReal using pointwise positive exponential on the original restricted dividend measure.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_finite_value_implies_original_unrestricted_signed_stieltjes_integrable_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_finite_original_value_ae_random_strict_future_signed_ennreal_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ)
    (T : Ω → ℝ)
    (hFinite : dividendValue X q x D < ⊤) :
    ∀ᵐ ω ∂P,
      ENNReal.ofReal
        (∫ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (T ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (T ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
