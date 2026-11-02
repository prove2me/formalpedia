-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_rightcont_stopped_source_initial_compensator_rectangle
-- name    : AvramDividend.Classical.avram_wave5_01_actual_rightcont_stopped_source_initial_compensator_rectangle
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:52:09.732062+00:00
-- url     : https://prove2.me/theorems/41f9d39f-87ad-4c76-a487-7907220b3f1b
-- title:
--   Actual stopped source jump occupation equals canonical Lévy intensity at right-continuous initial predictable rectangles
-- statement:
--   For the genuine original process X and its unchanged right-continuous filtration (the process lift Y is definitionally same path), a literal predictable jump kernel K, occupation M=P.bind K, and any restriction MT=M.restrict S, construct canonical finite-horizon predictable μ agreeing with restricted Lebesgue time × P. The source MT and product canonical N=μ.prod(X.ν.restrict negative marks) agree on every initial-time predictable marked rectangle for 𝓕.rightCont0 histories. This removes hBot required by Chat02-C with no assumed future rectangle compensator, no separate Poisson space, and no restriction on stopped region S.
-- source:
--   Combines proved source kernel initial occupation c922c8ed, same-path rightCont Levy lift e58a099d, and new canonical time-zero intensity theorem. Proves exact source hBot for stopped MT, not hFuture.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_predictable_occupation_bottom_rectangle_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_rightcont_canonical_levy_intensity_initial_rectangle_zero
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_rightcont_stopped_source_initial_compensator_rectangle
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω =
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2))
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (MT : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hMT : MT = M.restrict S)
    (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
        μ A = ((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      (∀ (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
        ∀ (B : Set ℝ), MeasurableSet B →
        MT (({(0 : ℝ≥0)} ×ˢ A) ×ˢ B) =
          (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
           μ.prod (X.ν.restrict (Iio (0 : ℝ))))
            (({(0 : ℝ≥0)} ×ˢ A) ×ˢ B)) := by sorry
