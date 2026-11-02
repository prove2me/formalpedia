-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_actual_source_signed_fubini_finite_horizon_restriction
-- name    : AvramDividend.Classical.avram_wave5_p1_actual_source_signed_fubini_finite_horizon_restriction
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:13:41.947314+00:00
-- url     : https://prove2.me/theorems/0858f09f-cf6c-4300-a3bb-401bd1d52b3e
-- title:
--   Actual original-source signed Fubini transports to a finite predictable horizon restriction for supported rewards
-- statement:
--   For the literal original Lévy intrinsic jump measure, its signed source Fubini identity with the unrestricted expected occupation M=P.bind K is transported to MT=M.restrict S whenever the predictable marked set S is measurable and the reward H is supported in S. This is the finite-horizon restriction bridge needed to use the Proved finite-band source compensation theorem without assuming globally finite Lévy mass over infinite time. It imports the Proved signed Fubini with P-a.e. fibre integrability, and preserves all its explicit outer integrability, a.e. finiteness, and original occupation kernel hypotheses. It does not establish the source adapted rectangle intensity law or L² isometry.
-- source:
--   Proved original-source signed Fubini AE fibres 6cf166c8-97f3-47cd-91dd-01dde49a2a10; pinned Mathlib MeasureTheory.integral_indicator; horizon-supported H as S.indicator H=H.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_intrinsic_signed_occupation_fubini_ae_fibres
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_p1_actual_source_signed_fubini_finite_horizon_restriction
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
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (hS : MeasurableSet[(@Prod.instMeasurableSpace _ _ (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))] S)
    (MT : @Measure ((ℝ≥0 × Ω) × ℝ) (@Prod.instMeasurableSpace _ _ (𝓕.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hMT : MT = M.restrict S)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hSupport : S.indicator H = H)
    (hHi : Integrable H M)
    (hPosHm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))]
      (fun p => ENNReal.ofReal (H p)))
    (hNegHm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))]
      (fun p => ENNReal.ofReal (-H p)))
    (hFibre : ∀ᵐ ω ∂P, Integrable
      (fun p : ℝ≥0 × ℝ => H ((p.1, ω), p.2)) (NX ω))
    (hPosFin : ∀ᵐ ω ∂P,
      (∫⁻ p, ENNReal.ofReal (H ((p.1, ω), p.2)) ∂(NX ω)) < ∞)
    (hNegFin : ∀ᵐ ω ∂P,
      (∫⁻ p, ENNReal.ofReal (-H ((p.1, ω), p.2)) ∂(NX ω)) < ∞)
    (hPosI : Integrable (fun ω =>
      (∫⁻ p, ENNReal.ofReal (H ((p.1, ω), p.2)) ∂(NX ω)).toReal) P)
    (hNegI : Integrable (fun ω =>
      (∫⁻ p, ENNReal.ofReal (-H ((p.1, ω), p.2)) ∂(NX ω)).toReal) P) :
    (∫ ω, ∫ p, H ((p.1, ω), p.2) ∂(NX ω) ∂P) =
      ∫ p, H p ∂MT := by sorry
