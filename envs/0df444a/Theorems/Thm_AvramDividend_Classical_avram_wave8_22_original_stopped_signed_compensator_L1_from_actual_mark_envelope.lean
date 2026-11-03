-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_stopped_signed_compensator_L1_from_actual_mark_envelope
-- name    : AvramDividend.Classical.avram_wave8_22_original_stopped_signed_compensator_L1_from_actual_mark_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:26:04.606863+00:00
-- url     : https://prove2.me/theorems/a8bff5b9-7ff1-45b3-9690-691a1ce0c977
-- title:
--   Original stopped signed compensated negative jump is L1 centred from actual finite physical clock and integrable Levy mark envelope
-- statement:
--   On unchanged original Levy source NX and original right-continuous predictable clock mu, prove the stopped negative-jump random compensated integral is L1 and mean zero using a finite true Levy mark envelope g. The intensity-side marked product L1 is derived from the Proved W7-02 physical envelope lemma, rather than assumed. Canonical finite negative mark bands are constructed from the original X.ν internally. The exact original strict-future rectangle law remains an explicit source obligation.
-- source:
--   Proved original W7-02 mark envelope 0fd3279a-04e0-4d8d-952f-7a555574df54, canonical finite bands b80e4040-c3f7-4cd9-afc1-5f231aab3645, W8-22 signed stopped compensation 9ebbcecd-f9c3-4cf2-ad81-c54fffbc06c4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_stopped_signed_jump_minus_true_predictable_compensator_L1_zero_mean
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_levy_negative_quadratic_canonical_finite_mark_bands
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_predictable_mark_kernel_L1_from_physical_mark_envelope
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_stopped_signed_compensator_L1_from_actual_mark_envelope
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕)
  (NX : Ω → Measure (ℝ≥0 × ℝ))
  (hNX : ∀ ω, NX ω = ((Measure.count.restrict
    {u : ℝ≥0 | 0 < u ∧ X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
    (fun u : ℝ≥0 => (u, X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
  (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
    (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
      (inferInstance : MeasurableSpace ℝ)))
  (hK : ∀ ω, K ω = @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
    (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
    (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
      (inferInstance : MeasurableSpace ℝ))
    (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω))
  (hKmeas : AEMeasurable K P)
  (MK : @Measure ((ℝ≥0 × Ω) × ℝ)
    (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
      (inferInstance : MeasurableSpace ℝ)))
  (hMK : MK = P.bind K) (T : ℝ≥0)
  (S : Set ((ℝ≥0 × Ω) × ℝ)) (hST : S = {p | p.1.1 ≤ T})
  (hS : MeasurableSet[(@Prod.instMeasurableSpace _ _
    (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] S)
  (MT N : @Measure ((ℝ≥0 × Ω) × ℝ)
    (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
      (inferInstance : MeasurableSpace ℝ)))
  (hMT : MT = MK.restrict S)
  (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
  (hμfinite : μ Set.univ < ∞)
  (hμclock : ∀ A : Set (ℝ≥0 × Ω),
    MeasurableSet[𝓕.rightCont.predictable] A →
    μ A = ((((volume : Measure ℝ).restrict
      (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A)
  (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) :=
    𝓕.rightCont.predictable; μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
  (hFuture : ∀ (i : ℝ≥0) (A : Set Ω) (C' : Set ℝ),
    MeasurableSet[𝓕.rightCont i] A → MeasurableSet C' →
    MT ((Set.Ioi i ×ˢ A) ×ˢ C') = N ((Set.Ioi i ×ˢ A) ×ˢ C'))
  (τ : Ω → ℝ≥0) (hτBound : ∀ ω, τ ω ≤ T)
  (hτ : IsStoppingTime 𝓕.rightCont
    (fun ω => (τ ω : WithTop ℝ≥0)))
  (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
  (hGm : Measurable[(@Prod.instMeasurableSpace _ _
    (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] G)
  (g : ℝ → ℝ)
  (hg : Integrable g (X.ν.restrict (Iio (0 : ℝ))))
  (hBound : (letI : MeasurableSpace (ℝ≥0 × Ω) :=
    𝓕.rightCont.predictable;
    ∀ᵐ p ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ)))),
      ‖G p‖ ≤ ‖g p.2‖))
  (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
  (hH : H = fun p =>
    if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0)
  (hSupport : S.indicator H = H) :
  Integrable (fun ω =>
    (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
    (∫ t, ∫ z, H ((t, ω), z)
      ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal))) P ∧
  (∫ ω, ((∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
    (∫ t, ∫ z, H ((t, ω), z)
      ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal))) ∂P) = 0 := by sorry
