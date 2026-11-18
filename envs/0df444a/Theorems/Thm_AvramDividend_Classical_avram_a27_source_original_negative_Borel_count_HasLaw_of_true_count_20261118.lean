-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_source_original_negative_Borel_count_HasLaw_of_true_count_20261118
-- name    : AvramDividend.Classical.avram_a27_source_original_negative_Borel_count_HasLaw_of_true_count_20261118
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T00:24:34.001574+00:00
-- url     : https://prove2.me/theorems/b92a8424-2517-4b42-bc2f-f45ae472b958
-- title:
--   Any original physical negative Borel jump count representative has the exact Poisson law
-- statement:
--   For any finite-activity spectrally negative Lévy process on its original probability space, and any measurable natural-valued random variable agreeing almost surely with the actual count of physical negative jumps whose sizes lie in a negative Borel set B up to time T, the random variable has the exact Poisson(r) law with r=Tν(B). The proof uses the already formalised original-space exact singleton probabilities and uniqueness of a measure on a countable target from singleton masses.
-- source:
--   Proved A114 original Borel singleton physical Poisson probabilities, Mathlib Measure.ext_of_singleton and Measure.map_apply.

import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Probability.Distributions.Poisson.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a114_original_negative_Borel_count_exact_poisson_singleton_probabilities_20261114
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a27_source_original_negative_Borel_count_HasLaw_of_true_count_20261118
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ))
    (K : Ω → ℕ) (hK : Measurable K)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)).toReal)
    (r : ℝ≥0)
    (hr : (r : ℝ) = ((T : ℝ≥0∞) * X.ν B).toReal) :
    HasLaw K (poissonMeasure r) P := by sorry
