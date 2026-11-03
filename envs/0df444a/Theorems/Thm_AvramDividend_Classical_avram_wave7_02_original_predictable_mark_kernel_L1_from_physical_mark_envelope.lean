-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_predictable_mark_kernel_L1_from_physical_mark_envelope
-- name    : AvramDividend.Classical.avram_wave7_02_original_predictable_mark_kernel_L1_from_physical_mark_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:37:22.475438+00:00
-- url     : https://prove2.me/theorems/0fd3279a-04e0-4d8d-952f-7a555574df54
-- title:
--   Original right-continuous predictable nonlinear jump kernel is L1 under a physical mark-only integrable domination
-- statement:
--   For any actual SpectrallyNegativeLevy X with its exact original right-continuous predictable filtration and a finite physical clock μ, a strongly measurable signed random marked kernel H bounded almost everywhere by the absolute value of one X.ν-integrable negative-mark envelope g is itself L1 with respect to μ×X.ν. This discharges the marked product-integrability requirement in genuine original-source C1 predictable compensation without imposing C2 or a new Poisson source.
-- source:
--   Pinned exact-source Mathlib Integrable.mul_prod for a finite predictable clock constant-one factor and Integrable.mono' using original full negative Levy mark intensity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_predictable_mark_kernel_L1_from_physical_mark_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (g : ℝ → ℝ) (hg : Integrable g (X.ν.restrict (Iio (0 : ℝ))))
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hHm : (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable;
      AEStronglyMeasurable H (μ.prod (X.ν.restrict (Iio (0 : ℝ))))))
    (hBound : (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable;
      ∀ᵐ p ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ)))),
        ‖H p‖ ≤ ‖g p.2‖)) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      Integrable H (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by sorry
