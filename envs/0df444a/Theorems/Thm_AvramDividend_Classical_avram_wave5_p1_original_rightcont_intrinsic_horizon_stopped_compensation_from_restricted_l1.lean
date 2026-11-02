-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_rightcont_intrinsic_horizon_stopped_compensation_from_restricted_l1
-- name    : AvramDividend.Classical.avram_wave5_p1_original_rightcont_intrinsic_horizon_stopped_compensation_from_restricted_l1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:33:30.936709+00:00
-- url     : https://prove2.me/theorems/d884e388-ccf1-4ad7-b61a-19f6e6232041
-- title:
--   Original right-continuous-filtration stopped Lévy compensation from intensity-side L¹ and actual adapted source rectangles
-- statement:
--   On the same unchanged original Levy X probability space, lift X path-identically to F.rightCont. Let source NX and K be the original intrinsic jump measure and actual source kernel on rightCont.predictable. On a finite horizon MT=M.restrict S, assume finite mark-band mass hLocal and original adapted rectangle equality hBot/hFuture against explicit intensity measure N. By the Proved sigma-finite predictable-measure uniqueness theorem derive MT=N. Thus it suffices to assume the rightCont predictable control reward G is integrable against the explicit N, not the source occupation MT. The proved stronger original-source restricted-L1 compensation theorem then yields integrability of actual source jump rewards under P and precisely zero expected compensated jump discrepancy. No independent Poisson copy or stochastic L2 isometry assumed.
-- source:
--   Standalone source-faithful rightCont interface: Proved path-identical Lévy lift e58a099d, Proved P1 sigma-finite predictable measure uniqueness 85791e69, Proved P1 L1 stopped transfer 80ae40da and Proved actual source signed Fubini/fibre/integral L1 results; no dependence on the new Open 059d child. Gives intensity-side hGiN under genuine original-source rectangle law without a Poisson copy.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_sigma_finite_marked_predictable_measure_unique
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_sigma_stopped_predictable_marked_l1_transfer
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_intrinsic_jump_fibres_integrable_ae_of_global_l1
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_intrinsic_jump_integral_integrable_from_global_l1
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_signed_source_fubini_of_integrable_predictable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_p1_original_rightcont_intrinsic_horizon_stopped_compensation_from_restricted_l1
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω =
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω))
    (hKmeas : AEMeasurable K P)
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (T : ℝ≥0)
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (hST : S = {p | p.1.1 ≤ T})
    (hS : MeasurableSet[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] S)
    (MT N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hMT : MT = M.restrict S)
    (B : ℕ → Set ℝ) (hBm : ∀ k, MeasurableSet (B k))
    (hBmono : Monotone B) (hBcover : (⋃ k, B k) = Set.univ)
    (hLocal : ∀ k, MT ((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B k) ≠ ∞)
    (hBot : ∀ (A : Set Ω) (C : Set ℝ),
      MeasurableSet[𝓕.rightCont ⊥] A → MeasurableSet C →
      MT (({(⊥ : ℝ≥0)} ×ˢ A) ×ˢ C) =
        N (({(⊥ : ℝ≥0)} ×ˢ A) ×ˢ C))
    (hFuture : ∀ (i : ℝ≥0) (A : Set Ω) (C : Set ℝ),
      MeasurableSet[𝓕.rightCont i] A → MeasurableSet C →
      MT ((Set.Ioi i ×ˢ A) ×ˢ C) =
        N ((Set.Ioi i ×ˢ A) ×ˢ C))
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕.rightCont τ)
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hGm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] G)
    (hGiN : Integrable G N)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hH : H = fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then G p else 0)
    (hSupport : S.indicator H = H) :
    Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] H ∧
    Integrable H MT ∧ Integrable H N ∧
    Integrable (fun ω =>
      ∫ p, H ((p.1, ω), p.2) ∂(NX ω)) P ∧
    (∫ ω, ∫ p, H ((p.1, ω), p.2) ∂(NX ω) ∂P) -
      (∫ p, H p ∂N) = 0 := by sorry
