-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02c_literal_intrinsic_source_integrable_centered_compensated_stopped_jump_term
-- name    : AvramDividend.Classical.avram_wave5_02c_literal_intrinsic_source_integrable_centered_compensated_stopped_jump_term
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:07:00.613547+00:00
-- url     : https://prove2.me/theorems/d8bdba75-075a-441c-996a-3cf3c8c2bb2c
-- title:
--   Literal original source stopped compensated jump reward is an integrable centered random variable with expectation zero
-- statement:
--   With NX and K defined literally from original spectrally negative Levy source X under the same probability P and horizon restriction MT, under exact finite stopped mark-band and adapted source rectangle law, the inclusively stopped predictable reward has L1 actual source integral and Levy compensator. Moreover the random compensated stopped source integral F(ω)=∫ H(t,ω,z) NX(ω)(dt,dz) − ∫H dN is itself Integrable under original P and its direct Bochner expectation ∫F dP is exactly zero, not merely an informal difference of expectations. No infinite horizon occupation and no independent Poisson copy.
-- source:
--   Accepted literal original stopped L1 compensation target 23c6c480 and Mathlib Bochner linearity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02c_literal_intrinsic_source_automatic_stopped_l1_compensation
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Literal intrinsic jump measure and predictable kernel are defined from the original X. -/

theorem AvramDividend.Classical.avram_wave5_02c_literal_intrinsic_source_integrable_centered_compensated_stopped_jump_term
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
  :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
        (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
          (inferInstance : MeasurableSpace ℝ)) := fun ω =>
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω)
    ∀ (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (T : ℝ≥0)
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (hST : S = {p | p.1.1 ≤ T})
    (MT N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hMT : MT = M.restrict S)
    (B : ℕ → Set ℝ) (hBm : ∀ k, MeasurableSet (B k))
    (hBmono : Monotone B) (hBcover : (⋃ k, B k) = Set.univ)
    (hLocal : ∀ k, MT ((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B k) ≠ ∞)
    (hBot : ∀ (A : Set Ω) (C : Set ℝ),
      MeasurableSet[𝓕 ⊥] A → MeasurableSet C →
      MT (({(⊥ : ℝ≥0)} ×ˢ A) ×ˢ C) =
        N (({(⊥ : ℝ≥0)} ×ˢ A) ×ˢ C))
    (hFuture : ∀ (i : ℝ≥0) (A : Set Ω) (C : Set ℝ),
      MeasurableSet[𝓕 i] A → MeasurableSet C →
      MT ((Set.Ioi i ×ˢ A) ×ˢ C) =
        N ((Set.Ioi i ×ˢ A) ×ˢ C))
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕 τ)
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hGm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))] G)
    (hGi : Integrable G MT)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hH : H = fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then G p else 0)
    (hSupport : S.indicator H = H),
    Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))] H ∧
    Integrable H MT ∧ Integrable H N ∧
    Integrable (fun ω =>
      ∫ p, H ((p.1, ω), p.2) ∂(NX ω)) P ∧
    Integrable (fun ω =>
      (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) - (∫ p, H p ∂N)) P ∧
    (∫ ω, ((∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ p, H p ∂N)) ∂P) = 0 := by sorry
