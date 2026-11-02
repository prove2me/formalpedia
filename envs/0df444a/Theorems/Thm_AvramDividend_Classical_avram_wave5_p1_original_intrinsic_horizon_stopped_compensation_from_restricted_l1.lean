-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_intrinsic_horizon_stopped_compensation_from_restricted_l1
-- name    : AvramDividend.Classical.avram_wave5_p1_original_intrinsic_horizon_stopped_compensation_from_restricted_l1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:25:35.307203+00:00
-- url     : https://prove2.me/theorems/059d4b77-404f-424a-a216-522728bace99
-- title:
--   Original intrinsic Lévy stopped predictable jump compensation has zero expectation from restricted finite-horizon L¹ alone
-- statement:
--   For the literal intrinsic source NX of the same original SpectrallyNegativeLevy X, use the original filtration, actual samplewise occupation kernel K and full M=P.bind K, restricted to the finite horizon S={t≤T} as MT=M.restrict S. Assume precisely the finite-band local mass, original adapted-rectangle compensator identities against N, a stopping time, predictable G integrable with respect to MT and the stopped reward H supported on S. Conclude predictable measurability, L¹ under MT and N, actual NX jump-integral L¹ on P, and exact expectation zero of the compensated signed source jump reward. Crucially, global Integrable H M is DERIVED from restricted Integrable H MT using the horizon support indicator, rather than assumed; no independent Poisson copy or unrestricted compensated source is claimed.
-- source:
--   Source-faithful stronger companion to original actual stopped compensation f544dab9 and earlier unresolved first L¹ publication. Removes global hHi using Mathlib integrable_indicator_iff with hSupport and M.restrict S. Imports canonically Proved original predictable L¹ transfer, actual fibre L¹, actual inner integral L¹ and signed source Fubini. Original rectangle source-law remains Chat 01's independent obligation.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_sigma_stopped_predictable_marked_l1_transfer
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_intrinsic_jump_fibres_integrable_ae_of_global_l1
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_intrinsic_jump_integral_integrable_from_global_l1
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_signed_source_fubini_of_integrable_predictable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_p1_original_intrinsic_horizon_stopped_compensation_from_restricted_l1
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
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω =
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω))
    (hKmeas : AEMeasurable K P)
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (T : ℝ≥0)
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (hST : S = {p | p.1.1 ≤ T})
    (hS : MeasurableSet[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))] S)
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
    (hSupport : S.indicator H = H) :
    Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))] H ∧
    Integrable H MT ∧ Integrable H N ∧
    Integrable (fun ω =>
      ∫ p, H ((p.1, ω), p.2) ∂(NX ω)) P ∧
    (∫ ω, ∫ p, H ((p.1, ω), p.2) ∂(NX ω) ∂P) -
      (∫ p, H p ∂N) = 0 := by sorry
