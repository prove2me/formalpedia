-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02c_actual_controlled_rightcont_integrable_centered_ruin_stopped_compensated_term
-- name    : AvramDividend.Classical.avram_wave5_02c_actual_controlled_rightcont_integrable_centered_ruin_stopped_compensated_term
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:08:31.923099+00:00
-- url     : https://prove2.me/theorems/c79643ac-9e37-4f29-923f-7703a4a08df2
-- title:
--   Actual ruin-stopped controlled right-continuous negative-jump compensated term is an integrable zero-mean random variable
-- statement:
--   For the actual original spectrally negative Levy path X and original P, ruin-stopped controlled C2 Taylor kernel with deterministic t<=T and z<0 masks, use Chat02-A-proved rightCont source kernel measurability and restricted stopped compensation to derive the integrability under P of the random compensated jump integral F(ω)=∫G((t,ω),z) NX(ω)(dt,dz)−∫G dN, and its direct mean ∫F dP=0. The ruin-causing jump is retained by t<=τ. Finite stopped band and adapted source rectangle inputs remain explicit; no copied Poisson process, no infinite-horizon L1.
-- source:
--   Proved controlled rightCont Chat02-C source kernel measurable theorem 5c4e478d and Bochner L1 integral linearity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02c_actual_controlled_compensation_of_rightcont_source_kernel_measurable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual ruin-stopped controlled compensation uses proved source kernel measurability. -/

theorem AvramDividend.Classical.avram_wave5_02c_actual_controlled_rightcont_integrable_centered_ruin_stopped_compensated_term
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
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t))))
    (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω =
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω))
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
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
        N ((Set.Ioi i ×ˢ A) ×ˢ C')) :
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
    Integrable (fun ω =>
      (∫ p, G ((p.1, ω), p.2) ∂NX ω) - (∫ p, G p ∂N)) P ∧
    (∫ ω, ((∫ p, G ((p.1, ω), p.2) ∂NX ω) -
      (∫ p, G p ∂N)) ∂P) = 0 := by sorry
