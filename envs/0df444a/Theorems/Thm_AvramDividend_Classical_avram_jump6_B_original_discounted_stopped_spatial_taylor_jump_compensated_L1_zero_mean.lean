-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_discounted_stopped_spatial_taylor_jump_compensated_L1_zero_mean
-- name    : AvramDividend.Classical.avram_jump6_B_original_discounted_stopped_spatial_taylor_jump_compensated_L1_zero_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:59:48.321174+00:00
-- url     : https://prove2.me/theorems/d799ff3e-27ac-4e55-a4e9-cc718547dd12
-- title:
--   Original stopped spatial Taylor negative-jump compensated source L1 centring
-- statement:
--   For the original spectrally negative Levy X and physical pre-dividend left-limit state, construct the exact discounted spatial Taylor negative-jump kernel on an interior compact band. Under explicit predictability, product-measure integrability, true stopping-time, finite-time localisation and stopped support hypotheses, its negative-mark compensated stochastic integral is integrable and has mean zero even when negative-jump intensity is infinite. Applies the proved predictable compensation theorem with the original source kernel; the kernel integrability and source-grid L1 identification remain analytic obligations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_stopped_compensated_source_Ms_L1_mean_zero
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_discounted_stopped_spatial_taylor_jump_compensated_L1_zero_mean
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
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hGm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] G)
    (hGiN : Integrable G N)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hH : H = fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then G p else 0)
    (hSupport : S.indicator H = H)
    (x q u v δ : ℝ) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (hSource : G = fun p =>
      Real.exp (-(q * (p.1.1 : ℝ))) *
        (let Y : ℝ := Function.leftLim
          (fun t : ℝ≥0 => x + X.X t p.1.2 - rightLimit D t p.1.2) p.1.1
         (if Y ∈ Icc (u + δ) v then
            w (Y + p.2) - w Y -
              (if -1 < p.2 then p.2 * deriv w Y else 0)
          else 0))) :
    Integrable (fun ω =>
      (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
        (∫ p, H p ∂N)) P ∧
    (∫ ω, (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ p, H p ∂N) ∂P) = 0 := by sorry
