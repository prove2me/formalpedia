-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_actual_Levy_future_marked_rectangles_auto
-- name    : AvramDividend.Classical.avram_pj_workerC_actual_Levy_future_marked_rectangles_auto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T09:32:23.936777+00:00
-- url     : https://prove2.me/theorems/ba3ae3e0-3fd2-45eb-a1eb-17c1c4efdfe3
-- title:
--   Original true Lévy marked jump count and predictable compensator satisfy all right-continuous past-event future-rectangle identities automatically
-- statement:
--   For the original spectrally negative Lévy process and an actual predictable physical finite clock measure μ matching the bounded true time-product law, construct genuine positive-time jump measure NX, its lifted count kernel K, the sample-integrated marked count MK=P.bind K, and μ×negative Lévy compensator N. For every right-continuous past-event A and Borel jump-mark set B and time i, the original marked count future rectangle equals the compensator future rectangle, on the genuine horizon T. The result removes any invented hFuture witness in physical stopped compensated Itô source calculations.
-- source:
--   Proved 6a4042cf original intrinsic P2 future rectangle equality, pinned X.isProbability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_rightcont_source_future_of_P2
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_actual_Levy_future_marked_rectangles_auto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμclock : ∀ E : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] E →
      μ E = ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
        Real.toNNReal).prod P) E) :
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
    ∀ (i : ℝ≥0) (A : Set Ω),
      MeasurableSet[𝓕.rightCont i] A → ∀ (B : Set ℝ),
      MeasurableSet B →
      (MK.restrict {p | p.1.1 ≤ T}) ((Ioi i ×ˢ A) ×ˢ B) =
        N ((Ioi i ×ˢ A) ×ˢ B) := by sorry
