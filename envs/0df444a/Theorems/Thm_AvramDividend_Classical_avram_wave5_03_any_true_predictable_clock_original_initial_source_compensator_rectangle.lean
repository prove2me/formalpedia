-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_any_true_predictable_clock_original_initial_source_compensator_rectangle
-- name    : AvramDividend.Classical.avram_wave5_03_any_true_predictable_clock_original_initial_source_compensator_rectangle
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:35:53.487106+00:00
-- url     : https://prove2.me/theorems/f04c5651-ad24-47a7-9e10-c132e668582d
-- title:
--   Any exact original finite physical predictable clock satisfies the literal source jump compensator initial rectangle law
-- statement:
--   For the same original SpectrallyNegativeLevy X, original intrinsic negative-mark jump occupation M=P.bind K and its actual stopped restriction MT, any rightCont predictable finite-horizon clock μ agreeing with restricted real Lebesgue time×P on every predictable set obeys the exact initial-time source occupation/intensity rectangle equality. Derive this, without assuming an hBot, from Chat01's canonical Proved existential physical clock/initial source compensator law and uniqueness of measures with equal values on all measurable predictable sets. The resulting hBot can be imported into the literal Chat02-C controlled compensated-jump theorem for the same chosen μ, leaving only the true source future-rectangle and finite band premises.
-- source:
--   Chat01 canonical Proved original rightCont stopped initial compensator rectangle 41f9d39f; Chat02-C actual controlled rightCont centred jump theorem c79643ac; original true predictable clock a6771154, all in Avram mission 1300fbe7.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_rightcont_stopped_source_initial_compensator_rectangle
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_any_true_predictable_clock_original_initial_source_compensator_rectangle
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
    (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμclock : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
        μ A = ((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) :
    ∀ (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
      ∀ (B : Set ℝ), MeasurableSet B →
      MT (({(0 : ℝ≥0)} ×ˢ A) ×ˢ B) =
        (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
         μ.prod (X.ν.restrict (Iio (0 : ℝ))))
          (({(0 : ℝ≥0)} ×ˢ A) ×ˢ B) := by sorry
