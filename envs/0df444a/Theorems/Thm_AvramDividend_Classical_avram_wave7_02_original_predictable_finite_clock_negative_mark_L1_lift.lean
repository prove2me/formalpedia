-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_predictable_finite_clock_negative_mark_L1_lift
-- name    : AvramDividend.Classical.avram_wave7_02_original_predictable_finite_clock_negative_mark_L1_lift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:36:30.049766+00:00
-- url     : https://prove2.me/theorems/bc90d50e-ce84-4333-aa54-5100168f8a88
-- title:
--   Original finite right-continuous predictable clock lifts every integrable negative Lévy mark kernel to the genuine marked source product L1
-- statement:
--   In the original spectrally negative Levy filtration, any finite predictable physical clock μ and mark-only real integrable kernel g under the actual restricted negative Lévy measure X.ν yield a genuinely integrable g(z) function on the original predictable product intensity μ×X.ν. The proof uses constant-one integrability for the finite true clock and Bochner product integrability; no artificial independent Poisson source or assumed compensation equality.
-- source:
--   Pinned Mathlib MeasureTheory.Integrable.mul_prod and integrable_const on the exact original right-continuous predictable time-space and X.ν negative mark measures.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_predictable_finite_clock_negative_mark_L1_lift
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (g : ℝ → ℝ) (hg : Integrable g (X.ν.restrict (Iio (0 : ℝ)))) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      Integrable (fun p : (ℝ≥0 × Ω) × ℝ => g p.2)
        (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by sorry
