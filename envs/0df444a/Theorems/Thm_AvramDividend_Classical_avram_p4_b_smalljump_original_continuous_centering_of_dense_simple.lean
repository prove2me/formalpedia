-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_continuous_centering_of_dense_simple
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_continuous_centering_of_dense_simple
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:14:25.475415+00:00
-- url     : https://prove2.me/theorems/c7c2f407-def8-42a9-834e-4fbe6a17aaab
-- title:
--   Original compensated small-jump L2 centring extends from dense predictable simple functions
-- statement:
--   A continuous original-source compensated map has zero value under a bounded expectation functional on all integrands whenever zero centring holds on a dense simple class. The source simple centring is explicit. The existence of the actual original-source compensated operator and source simple-integrand moment identities remains a separate obligation.
-- source:
--   Mathlib Continuous.ext_on over the original Lévy predictable product Lp2 with the explicit right-continuous predictable measurable-space instance.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_continuous_centering_of_dense_simple
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      ∀ (I : Lp ℝ (2 : ℝ≥0∞)
          (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))) →L[ℝ]
          Lp ℝ (2 : ℝ≥0∞) P)
        (J : Lp ℝ (2 : ℝ≥0∞) P →L[ℝ] ℝ)
        (S : Set (Lp ℝ (2 : ℝ≥0∞)
          (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0)))))
        (hDense : Dense S)
        (hSimpleZero : ∀ v ∈ S, J (I v) = 0),
      ∀ v, J (I v) = 0) := by sorry
