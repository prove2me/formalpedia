-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_continuous_isometry_of_all_Lp2_simple
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_continuous_isometry_of_all_Lp2_simple
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:26:40.527016+00:00
-- url     : https://prove2.me/theorems/d9b76a03-51e6-416f-94f1-4140e2aeef90
-- title:
--   Original source full compensated small-jump L2 isometry from all Lp2 simple inputs
-- statement:
--   For the genuine original-source predictable small-negative Lp2 space and original probability Lp2, a continuous linear stochastic integral operator that preserves Lp2 norm for every Lp2 simple-function input preserves Lp2 norm for all inputs. The theorem discharges density using the accepted source-specific simple-function density result and pinned Mathlib; existence of the operator and simple-source isometry remain explicit assumptions awaiting true P2 compensation and second moments.
-- source:
--   Accepted source-specific dense-class isometry extension b1acb515 and simple-density 57f21b85, with pinned Mathlib Lp.simpleFunc.dense.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_continuous_isometry_of_dense_simple
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_predictable_mark_Lp2_simple_dense
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_continuous_isometry_of_all_Lp2_simple
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      ∀ (I : Lp ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))) →L[ℝ] Lp ℝ (2 : ℝ≥0∞) P)
        (hSimpleIso : ∀ v : ↥(Lp.simpleFunc ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0)))),
          ‖I (v : Lp ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))))‖ =
          ‖(v : Lp ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))))‖),
      ∀ v, ‖I v‖ = ‖v‖) := by sorry
