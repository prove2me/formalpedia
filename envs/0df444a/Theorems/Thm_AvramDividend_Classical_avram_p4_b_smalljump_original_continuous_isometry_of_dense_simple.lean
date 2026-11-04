-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_continuous_isometry_of_dense_simple
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_continuous_isometry_of_dense_simple
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:14:22.488085+00:00
-- url     : https://prove2.me/theorems/b1acb515-8bd8-4a13-9981-38ee20b12bc7
-- title:
--   Original source compensated small-jump L2 isometry extends from dense simple functions
-- statement:
--   A continuous original-source small-jump map with the L2 variance isometry on a dense class of simple inputs preserves the norm everywhere. The source simple isometry is explicit. The existence of the actual original-source compensated operator and source simple-integrand moment identities remains a separate obligation.
-- source:
--   Mathlib Continuous.ext_on over the original Lévy predictable product Lp2 with the explicit right-continuous predictable measurable-space instance.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_continuous_isometry_of_dense_simple
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      ∀ (I : Lp ℝ (2 : ℝ≥0∞)
          (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))) →L[ℝ]
          Lp ℝ (2 : ℝ≥0∞) P)
        (S : Set (Lp ℝ (2 : ℝ≥0∞)
          (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0)))))
        (hDense : Dense S)
        (hSimpleIso : ∀ v ∈ S, ‖I v‖ = ‖v‖),
      ∀ v, ‖I v‖ = ‖v‖) := by sorry
