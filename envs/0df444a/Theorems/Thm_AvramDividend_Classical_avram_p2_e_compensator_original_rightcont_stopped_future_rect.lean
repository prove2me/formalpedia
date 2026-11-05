-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_rightcont_stopped_future_rect
-- name    : AvramDividend.Classical.avram_p2_e_compensator_original_rightcont_stopped_future_rect
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:59:10.336623+00:00
-- url     : https://prove2.me/theorems/92775667-eccc-4c3c-a51d-6c3981cf4230
-- title:
--   Original source stopped right-continuous future rectangles from proven intrinsic P2
-- statement:
--   For a spectrally negative Levy process on the original probability space and original filtration, the physical stopped source jump measure equals the true finite-clock Levy compensator on every strict-future rectangle Ioi(i) times an event of the original right-continuous sigma-field and a Borel mark. The literal source jump measure NX, its lifted kernel K, true source mean M, and actual physical clock product mu are explicit. This composes the Proved original intrinsic P2 theorem 393b03a8 and Proved stopped right-continuous future transport a82307c0, without any assumed intensity identity, alternate stochastic process, extra axioms, or finiteness shortcut.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p2_e_compensator_original_rightcont_stopped_future_rect
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω = ((Measure.count.restrict
      {u : ℝ≥0 | 0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω = @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
      (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))
      (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω))
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
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
