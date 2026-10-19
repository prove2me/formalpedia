-- Prove2me | Theorems.Thm_AvramDividend_Classical_generatorIntegrable_of_zero_near_and_bounded_tail
-- name    : AvramDividend.Classical.generatorIntegrable_of_zero_near_and_bounded_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T05:47:36.794982+00:00
-- url     : https://prove2.me/theorems/67a9b57b-cfdb-44ea-9ba0-f4696f7ca1f9
-- title:
--   Lévy generator integrability from finite tail mass and exact local cancellation
-- statement:
--   If the compensated generator jump integrand is measurable, bounded on negative jumps y<=-δ where the Lévy measure has finite mass, and zero on (-δ,0), then it is integrable over the entire negative half-line. This isolates the exact integrability mechanism required for a barrier policy above its cap without assuming any integrability of the raw large-jump magnitude.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.FunProp
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open Set MeasureTheory
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.generatorIntegrable_of_zero_near_and_bounded_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (x δ M : ℝ)
    (hδ : 0 < δ)
    (hmeas : Measurable (SpectrallyNegativeLevy.generatorIntegrand f x))
    (hfinite : X.ν (Iic (-δ)) < ⊤)
    (hbound : ∀ y ∈ Iic (-δ),
      |SpectrallyNegativeLevy.generatorIntegrand f x y| ≤ M)
    (hzero : ∀ y, -δ < y → y < 0 →
      SpectrallyNegativeLevy.generatorIntegrand f x y = 0) :
    X.GeneratorIntegrable f x := by sorry
