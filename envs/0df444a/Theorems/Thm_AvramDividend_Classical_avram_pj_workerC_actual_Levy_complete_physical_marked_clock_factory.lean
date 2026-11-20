-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_actual_Levy_complete_physical_marked_clock_factory
-- name    : AvramDividend.Classical.avram_pj_workerC_actual_Levy_complete_physical_marked_clock_factory
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T12:18:22.881599+00:00
-- url     : https://prove2.me/theorems/0d49c7f0-2fd3-4c05-a76c-57487afefcc2
-- title:
--   Original Levy finite horizon automatically supplies exact physical predictable clock, full negative mark exhaustion, local stopped count and right-continuous compensation
-- statement:
--   For each original spectrally negative Levy process and genuine finite physical horizon, construct from its own probability law a finite predictable time-sample measure agreeing with the original truncated Lebesgue product, then automatically obtain canonical finite-rate negative mark exhaustion, locally finite stopped original jump counts and right-continuous past-event future compensator rectangle identities on the original actual P.bind NX source, without adding probability, integrability or stochastic source hypotheses.
-- source:
--   Proved 7c19197b and 264bfd8d, original process X.isProbability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_true_Levy_finite_predictable_physical_clock
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_actual_full_mark_bands_future_local_source
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_actual_Levy_complete_physical_marked_clock_factory
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ∞ ∧
      (∀ E : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] E →
        μ E = ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal).prod P) E) ∧
      (
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict
        {u : ℝ≥0 | 0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)) :=
      fun ω => @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _
          (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω)
    let MK : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)) :=
      P.bind K
    let N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)) :=
      (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
        μ.prod (X.ν.restrict (Iio (0 : ℝ))))
    ∃ B : ℕ → Set ℝ,
      (∀ n, MeasurableSet (B n)) ∧
      (∀ n, (X.ν.restrict (Iio (0 : ℝ))) (B n) < ∞) ∧
      Monotone B ∧ (⋃ n, B n) = Set.univ ∧
      (∀ n, (MK.restrict {p | p.1.1 ≤ T})
        ((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B n) ≠ ∞) ∧
      (∀ (i : ℝ≥0) (A : Set Ω),
        MeasurableSet[𝓕.rightCont i] A → ∀ C : Set ℝ,
        MeasurableSet C →
        (MK.restrict {p | p.1.1 ≤ T}) ((Ioi i ×ˢ A) ×ˢ C) =
          N ((Ioi i ×ˢ A) ×ˢ C))) := by sorry
