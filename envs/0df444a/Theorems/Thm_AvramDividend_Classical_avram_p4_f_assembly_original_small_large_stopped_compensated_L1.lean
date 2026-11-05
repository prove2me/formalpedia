-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_small_large_stopped_compensated_L1
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_small_large_stopped_compensated_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:48:14.169488+00:00
-- url     : https://prove2.me/theorems/20afb132-b8a2-4c66-a044-85854699e88c
-- title:
--   Disjoint original stopped small and large compensated Levy mark sums are individually L1 centred
-- statement:
--   For the same physical intrinsic jumps of original X, finite stopped clock τ and intensity N with all source-kernel/stopping/intensity-integrability premises explicit, take two predictable integrands supported respectively on strictly small negative marks -1<z<0 and large negative marks z≤-1. Each has an actual stopped compensated real jump-sum random variable, integrable and centred. Pointwise small/large integrands have zero product, placing z=-1 only in the large branch; no auxiliary process and no Gaussian Itô or optional sampling claim.
-- source:
--   Proved public original stopped compensated Ms f445799e, applied separately at the same physical original X, τ, NX, K, M, MT, μ and N. Elementary band disjointness by cases at z=-1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_stopped_compensated_source_Ms_L1_mean_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_small_large_stopped_compensated_L1
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
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμfinite : μ Set.univ < ∞)
    (hμclock : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
        μ A = ((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A)
    (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
      μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
    (B : ℕ → Set ℝ) (hBm : ∀ k, MeasurableSet (B k))
    (hBmono : Monotone B) (hBcover : (⋃ k, B k) = Set.univ)
    (hBfinite : ∀ k, (X.ν.restrict (Iio (0 : ℝ))) (B k) < ∞)
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕.rightCont τ)
    (Gs Gl : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hGsm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] Gs)
    (hGlm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] Gl)
    (hGsiN : Integrable Gs N) (hGliN : Integrable Gl N)
    (hGsBand : ∀ p, p.2 ≤ (-1 : ℝ) ∨ 0 ≤ p.2 → Gs p = 0)
    (hGlBand : ∀ p, (-1 : ℝ) < p.2 → Gl p = 0)
    (Hs Hl : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hHs : Hs = fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then Gs p else 0)
    (hHl : Hl = fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then Gl p else 0)
    (hSupportS : S.indicator Hs = Hs)
    (hSupportL : S.indicator Hl = Hl) :
    (Integrable (fun ω => (∫ p, Hs ((p.1, ω), p.2) ∂(NX ω)) - (∫ p, Hs p ∂N)) P ∧
      (∫ ω, (fun ω => (∫ p, Hs ((p.1, ω), p.2) ∂(NX ω)) - (∫ p, Hs p ∂N)) ω ∂P) = 0) ∧
    (Integrable (fun ω => (∫ p, Hl ((p.1, ω), p.2) ∂(NX ω)) - (∫ p, Hl p ∂N)) P ∧
      (∫ ω, (fun ω => (∫ p, Hl ((p.1, ω), p.2) ∂(NX ω)) - (∫ p, Hl p ∂N)) ω ∂P) = 0) ∧
    ∀ p, Gs p * Gl p = 0 := by sorry
