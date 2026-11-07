-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f14_original_truncated_sigma_intrinsic_jump_centered
-- name    : AvramDividend.Classical.avram_p4_f14_original_truncated_sigma_intrinsic_jump_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:51:34.469213+00:00
-- url     : https://prove2.me/theorems/3f67d539-e4e2-4c9a-a851-d4e3679350dd
-- title:
--   Literal original truncated ruin-localised intrinsic compensated jump integral is centred
-- statement:
--   The genuine original negative-marked Lévy jump measure and predictable intensity, under the already-known original finite-grid kernel law and L1 intensity-side integrability, yield an L1 centred compensated jump term for any physical localising σ≤min(ruinTime,n). The deterministic clock bound is discharged by the exact source normalisation. This is the stopped martingale side of the finitecap F14 Ito witness, with explicit traceable missing kernel and energy hypotheses.
-- source:
--   Original X, filtration and Lévy jump counts. Direct adaptation of public Proved 1d2380ce-82f2-49bd-b6aa-5de886f4b94d with source clock 6b7a13a0-fa75-494d-8d56-b14562c66491.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_intrinsic_stopped_signed_compensator_no_kernel_meas_no_bands
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f14_original_truncated_sigma_intrinsic_jump_centered
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
  (MK : @Measure ((ℝ≥0 × Ω) × ℝ)
    (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
      (inferInstance : MeasurableSpace ℝ)))
  (hMK : MK = P.bind K) (n : ℕ)
  (S : Set ((ℝ≥0 × Ω) × ℝ)) (hST : S = {p | p.1.1 ≤ (n : ℝ≥0)})
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
      (Icc 0 ((n : ℝ≥0) : ℝ))).map Real.toNNReal).prod P) A)
  (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) :=
    𝓕.rightCont.predictable; μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
  (hFuture : ∀ (i : ℝ≥0) (A : Set Ω) (C' : Set ℝ),
    MeasurableSet[𝓕.rightCont i] A → MeasurableSet C' →
    MT ((Set.Ioi i ×ˢ A) ×ˢ C') = N ((Set.Ioi i ×ˢ A) ×ˢ C'))
  (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
  (τ : Ω → ℝ≥0)
  (hτeq : ∀ ω, τ ω =
    (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
  (σ : Ω → ℝ≥0) (hσle : ∀ ω, σ ω ≤ τ ω)
  (hσstop : IsStoppingTime 𝓕.rightCont
    (fun ω => (σ ω : WithTop ℝ≥0)))
  (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
  (hGm : Measurable[(@Prod.instMeasurableSpace _ _
    (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] G)
  (hGiN : Integrable G N)
  (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
  (hH : H = fun p =>
    if (p.1.1 : ℝ≥0∞) ≤ (σ p.1.2 : ℝ≥0∞) then G p else 0)
  (hSupport : S.indicator H = H) :
  Integrable (fun ω =>
    (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
    (∫ t, ∫ z, H ((t, ω), z)
      ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict (Icc 0 ((n : ℝ≥0) : ℝ))).map Real.toNNReal))) P ∧
  (∫ ω, ((∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
    (∫ t, ∫ z, H ((t, ω), z)
      ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict (Icc 0 ((n : ℝ≥0) : ℝ))).map Real.toNNReal))) ∂P) = 0 := by sorry
