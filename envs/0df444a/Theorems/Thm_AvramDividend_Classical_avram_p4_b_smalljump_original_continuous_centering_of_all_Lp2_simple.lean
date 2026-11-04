-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_continuous_centering_of_all_Lp2_simple
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_continuous_centering_of_all_Lp2_simple
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:27:44.701802+00:00
-- url     : https://prove2.me/theorems/cc8d3c87-45ea-430f-8fd9-cd0b4c4da3d7
-- title:
--   Original source full compensated small-jump L2 centring from all Lp2 simple inputs
-- statement:
--   On the genuine original source Lévy predictable product Lp2, if a continuous compensated-integral map I and bounded linear original-expectation functional J have been established and their composition vanishes on every square-integrable simple input, then J(Iv)=0 for all predictable Lp2 inputs. The finite-simple source compensated centring remains an explicit assumption; this does not prove source rate, variance or martingale construction.
-- source:
--   Accepted source dense centring c7c2f407 and source simple density 57f21b85, with pinned Mathlib Lp.simpleFunc.dense.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_continuous_centering_of_dense_simple
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_predictable_mark_Lp2_simple_dense
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_continuous_centering_of_all_Lp2_simple
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      ∀ (I : Lp ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))) →L[ℝ] Lp ℝ (2 : ℝ≥0∞) P)
        (J : Lp ℝ (2 : ℝ≥0∞) P →L[ℝ] ℝ)
        (hSimpleZero : ∀ v : ↥(Lp.simpleFunc ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0)))),
          J (I (v : Lp ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))))) = 0),
      ∀ v, J (I v) = 0) := by sorry
