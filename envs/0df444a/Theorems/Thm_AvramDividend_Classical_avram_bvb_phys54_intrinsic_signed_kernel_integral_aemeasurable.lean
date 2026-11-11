-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys54_intrinsic_signed_kernel_integral_aemeasurable
-- name    : AvramDividend.Classical.avram_bvb_phys54_intrinsic_signed_kernel_integral_aemeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T15:57:02.314371+00:00
-- url     : https://prove2.me/theorems/6930913e-7abf-48cd-b551-f68a005132ca
-- title:
--   Measurability of an integrable original predictable signed jump kernel
-- statement:
--   For an original spectrally negative Levy path, a real predictable marked integrand whose restriction to the original jump-counting measure is almost surely integrable has an almost-everywhere strongly measurable pathwise integral. Derive by the right-continuous original-process kernel lift and positive/negative lintegral measurability, then fibrewise signed-integral reconstruction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys54_intrinsic_signed_kernel_integral_aemeasurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (F : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hFm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] F) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧ X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
    (∀ᵐ ω ∂P, Integrable
       (fun p : ℝ≥0 × ℝ => F ((p.1, ω), p.2)) (NX ω)) →
    AEStronglyMeasurable
      (fun ω => ∫ p, F ((p.1, ω), p.2) ∂(NX ω)) P := by sorry
