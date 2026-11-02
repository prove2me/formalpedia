-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02c_literal_rightcont_controlled_ruin_stopped_compensation
-- name    : AvramDividend.Classical.avram_wave5_02c_literal_rightcont_controlled_ruin_stopped_compensation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:56:37.601196+00:00
-- url     : https://prove2.me/theorems/5da3ec5b-0213-4c4f-93f6-cf5f65ffa75d
-- title:
--   Literal original ruin-stopped controlled negative-jump Taylor compensation in the right-continuous filtration
-- statement:
--   For the literal intrinsic nonzero-jump source measure of X on its original probability space, define the marked predictable lift K from the actual source. The ruin-stopped controlled C2 Taylor remainder with negative marks z < 0 and physical horizon t <= T is right-continuous-filtration predictable, integrable for actual source jumps and Levy intensity, and has zero expected compensated source term. The ruin-causing jump is included. Retain only required finite stopped mark-band occupation and adapted source rectangle laws; original source identity, kernel identity and AEMeasurable K are definitional or derived from proved Chat02-A.
-- source:
--   Proved rightCont 02-A source kernel measurability fd94f92b and 02-C controlled negative-mark automatically stopped compensation b7319870.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_original_rightcont_predictable_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02c_actual_controlled_negative_mark_horizon_automatic_compensation
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_02c_literal_rightcont_controlled_ruin_stopped_compensation
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
  :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ)) := fun ω =>
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω)
    ∀     (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (T : ℝ≥0) (S : Set ((ℝ≥0 × Ω) × ℝ))
    (hST : S = {p | p.1.1 ≤ T})
    (MT N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hMT : MT = M.restrict S)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
      μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
    (B : ℕ → Set ℝ) (hBm : ∀ k, MeasurableSet (B k))
    (hBmono : Monotone B) (hBcover : (⋃ k, B k) = Set.univ)
    (hLocal : ∀ k, MT ((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B k) ≠ ∞)
    (hBot : ∀ (A : Set Ω) (C' : Set ℝ),
      MeasurableSet[𝓕.rightCont ⊥] A → MeasurableSet C' →
      MT (({(⊥ : ℝ≥0)} ×ˢ A) ×ˢ C') =
        N (({(⊥ : ℝ≥0)} ×ˢ A) ×ˢ C'))
    (hFuture : ∀ (i : ℝ≥0) (A : Set Ω) (C' : Set ℝ),
      MeasurableSet[𝓕.rightCont i] A → MeasurableSet C' →
      MT ((Set.Ioi i ×ˢ A) ×ˢ C') =
        N ((Set.Ioi i ×ˢ A) ×ˢ C')),
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t p.2 - rightLimit D t p.2) p.1
    let J : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * J p
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ :=
      S.indicator (((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ Iio (0 : ℝ)).indicator HS)
    Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] G ∧
    Integrable G MT ∧ Integrable G N ∧
    Integrable (fun ω => ∫ p, G ((p.1, ω), p.2) ∂NX ω) P ∧
    (∫ ω, ∫ p, G ((p.1, ω), p.2) ∂NX ω ∂P) - (∫ p, G p ∂N) = 0 := by sorry
