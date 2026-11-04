-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_P2_rate_implies_stopped_source_rightcont_future
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_P2_rate_implies_stopped_source_rightcont_future
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T11:01:05.501205+00:00
-- url     : https://prove2.me/theorems/3afddb6f-874a-457c-9cfe-85980e133edf
-- title:
--   True original P2 Lévy rate implies genuine rightCont stopped source future compensator without surrogate processes
-- statement:
--   Assuming only the exact outstanding P2 original intrinsic source rectangle rate for the original X on Ω/P/𝓕, the genuine horizon-restricted original marked jump occupation and the true physical predictable X.ν intensity agree on every strict-future (i,∞)×A×B with A in the original right-continuous past 𝓕.rightCont i. This follows from the complete original all-adapted-cell compensator, plus the accepted finite-cell-to-rightCont-future extractor. It is the exact hFuture premise required by the already Proved stopped signed C1 BV nonlinear jump L1 zero-mean theorem and remains conditional until P2 rate is proved.
-- source:
--   P3-B Proved all source finite marked cells compensation (conditional exactly on original P2 rate), P3-B Proved original rightCont finite-cell future extractor.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_all_horizon_marked_finite_cells_compensate
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_finite_cells_force_original_rightcont_future
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_P2_rate_implies_stopped_source_rightcont_future
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hRate : ∀ (s t : ℝ≥0), s ≤ t →
      ∀ (A : Set Ω), MeasurableSet[𝓕 s] A →
      ∀ (B : Set ℝ), MeasurableSet B →
        M ((Ioc s t ×ˢ A) ×ˢ B) =
        P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμclock : ∀ E : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] E →
      μ E = ((((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) E)
    (N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable;
      μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
    (i : ℝ≥0) (A : Set Ω)
    (hA : MeasurableSet[𝓕.rightCont i] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (M.restrict {p | p.1.1 ≤ T}) ((Ioi i ×ˢ A) ×ˢ B) =
      N ((Ioi i ×ˢ A) ×ˢ B) := by sorry
