-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_actual_BV_predictable_source_full_discounted_signed_stieltjes_HJB
-- name    : AvramDividend.Classical.avram_wave7_02_actual_BV_predictable_source_full_discounted_signed_stieltjes_HJB
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:43:11.647913+00:00
-- url     : https://prove2.me/theorems/1d7cf1c2-7489-4414-97f6-cbf68cf10f64
-- title:
--   Actual BV predictable original source physical generator and complete original Stieltjes dividend signed HJB integrals are nonpositive on interior clock
-- statement:
--   The exact original bounded-variation Levy process and the original right-continuous predictable filtration give a nonpositive joint signed HJB integral of the discounted physical Lévy generator and the full actual dividend Stieltjes measure, over original interior predictable time-space and original interior pre-ruin payment region. The local stochastic generator occupation measure, integration, and original cash payment time domain are literal and not replaced by artificial processes. The theorem preserves weaker canonical generator minus q*w and gradient conditions; separate atom secants and stopping compensation remain necessary.
-- source:
--   Proved original predictable source signed HJB occupation 5219ff90, original stopped source and physical dividend Stieltjes measure, and a.e. integral sign theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_actual_predictable_stopped_generator_integral_nonpos
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_actual_BV_predictable_source_full_discounted_signed_stieltjes_HJB
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (E : Set (ℝ≥0 × Ω))
    (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
    (hEregion : ∀ p ∈ E,
      0 < Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∧
      ENNReal.ofReal (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) < C)
    (hIGen : IntegrableOn
      (fun p : ℝ≥0 × Ω =>
        Real.exp (-(q * (p.1 : ℝ))) *
          (X.drift * deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) +
            (∫ z in Iio (0 : ℝ),
              w (Function.leftLim
                (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 + z) -
              w (Function.leftLim
                (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) ∂X.ν) -
            q * w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)))
      E μ)
    (A : Set ℝ) (hAm : MeasurableSet A)
    (hAclock : A ⊆ paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ))
    (hAregion : ∀ t ∈ A,
      0 < riskProcess X x D t.toNNReal ω ∧
      ENNReal.ofReal (riskProcess X x D t.toNNReal ω) < C)
    (hIDiv : IntegrableOn
      (fun t : ℝ => Real.exp (-(q * t)) *
        (1 - deriv w (riskProcess X x D t.toNNReal ω)))
      A (dividendMeasure D ω)) :
    (∫ p in E,
      Real.exp (-(q * (p.1 : ℝ))) *
        (X.drift * deriv w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) +
          (∫ z in Iio (0 : ℝ),
            w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 + z) -
            w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) ∂X.ν) -
          q * w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)) ∂μ) +
    (∫ t in A, Real.exp (-(q * t)) *
      (1 - deriv w (riskProcess X x D t.toNNReal ω))
      ∂(dividendMeasure D ω)) ≤ 0 := by sorry
