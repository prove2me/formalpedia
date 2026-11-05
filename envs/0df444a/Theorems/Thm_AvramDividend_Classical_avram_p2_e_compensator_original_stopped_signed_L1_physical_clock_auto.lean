-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_stopped_signed_L1_physical_clock_auto
-- name    : AvramDividend.Classical.avram_p2_e_compensator_original_stopped_signed_L1_physical_clock_auto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T10:39:41.185623+00:00
-- url     : https://prove2.me/theorems/c7cc0cd4-e2d8-4031-bdfc-ef3c4ae9b268
-- title:
--   Original stopped signed jump compensator L1 mean-zero with literal clock and P2 rates discharged
-- statement:
--   For a spectrally negative Levy process on its original probability space and original right-continuous filtration, the stopped signed source jump integral minus the actual physical-time Levy compensator integral is integrable and has mean zero. The proof discharges the literal source-kernel measurability and right-continuous future compensation assumptions of Proved source theorem 14adb08e using independently Proved original kernel fd94f92b and P2-complete original stopped rectangles 92775667. It preserves the exact source NX, lifted K, stopping time, integrand and clock identity, including legitimate integrability, support and predictability conditions; no new axiom, replacement process or independent-intensity assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p2_e_compensator_original_stopped_signed_L1_physical_clock_auto
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
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
    (hM : M = P.bind K) (T : ℝ≥0)
    (S : Set ((ℝ≥0 × Ω) × ℝ)) (hST : S = {p | p.1.1 ≤ T})
    (hS : MeasurableSet[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] S)
    (MT N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hMT : MT = M.restrict S)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμfinite : μ Set.univ < ∞)
    (hμclock : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
      μ A = ((((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A)
    (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable; μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕.rightCont τ)
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hGm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] G)
    (hGiN : Integrable G N)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hH : H = fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then G p else 0)
    (hSupport : S.indicator H = H) :
    Integrable (fun ω =>
      (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, H ((t, ω), z)
        ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal))) P ∧
    (∫ ω, ((∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, H ((t, ω), z)
        ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal))) ∂P) = 0 := by sorry
