-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_actual_full_mark_bands_future_local_source
-- name    : AvramDividend.Classical.avram_pj_workerC_actual_full_mark_bands_future_local_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T10:57:36.561325+00:00
-- url     : https://prove2.me/theorems/264bfd8d-3846-40dc-8984-d324f74a8604
-- title:
--   Actual original negative Lévy marked count has canonical finite band exhaustion, local finiteness and predictable future compensation
-- statement:
--   The actual marked negative-jump measure, under original spectrally negative Lévy law, admits canonical finite Lévy-rate bands covering the marks. Its stopped lifted count MK=P.bind K satisfies original right-continuous future compensator rectangle equalities and finite stopped local counts for every band under physical predictable μ matching time-product P.
-- source:
--   Proved b80e4040, 6a4042cf and 7a277885.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_rightcont_source_future_of_P2
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_levy_negative_quadratic_canonical_finite_mark_bands
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_true_clock_initial_future_rectangles_force_finite_mark_band
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_actual_full_mark_bands_future_local_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμclock : ∀ E : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] E →
      μ E = ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
        Real.toNNReal).prod P) E)
    (hμfinite : μ Set.univ < ∞) :
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
          N ((Ioi i ×ˢ A) ×ˢ C)) := by sorry
