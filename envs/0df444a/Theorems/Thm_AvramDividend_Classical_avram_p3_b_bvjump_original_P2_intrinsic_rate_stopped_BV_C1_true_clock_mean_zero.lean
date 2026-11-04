-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_P2_intrinsic_rate_stopped_BV_C1_true_clock_mean_zero
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_P2_intrinsic_rate_stopped_BV_C1_true_clock_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:57:14.781141+00:00
-- url     : https://prove2.me/theorems/a0db3640-1fab-4b52-8ab2-4caa8f4846e4
-- title:
--   Original P2 BV signed stopped jump zero mean with automatic true-clock measurability and support
-- statement:
--   On the genuine original Ω,P,𝓕,X,NX and dividend strategy D, derive stopped nonlinear signed BV L1 zero mean from P2 intrinsic jump-count rate, explicitly removing separate marked horizon measurability and stopped kernel support assumptions by proving both from the true finite clock T and stopping bound τ≤T. All source stochastic integrability and physical X.ν assumptions stay as in the accepted original theorem. Conditional on P2 original rate only.
-- source:
--   Accepted b7ef0753 plus new marked original predictable horizon and stopped clock support helpers

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_P2_intrinsic_rate_stopped_BV_C1_signed_L1_zero_mean
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_stopped_clock_support_from_tau_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_true_clock_marked_horizon_predictable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_P2_intrinsic_rate_stopped_BV_C1_true_clock_mean_zero {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
(X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (NX : Ω → Measure (ℝ≥0 × ℝ)) (hNX : ∀ ω, NX ω = ((Measure.count.restrict
{u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0 => (u, X.X u ω -
Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ) (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
(inferInstance : MeasurableSpace ℝ))) (hK : ∀ ω, K ω = @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ) (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
(@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)) (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω))
(MK : @Measure ((ℝ≥0 × Ω) × ℝ) (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
(hMK : MK = P.bind K) (T : ℝ≥0) (S : Set ((ℝ≥0 × Ω) × ℝ)) (hST : S = {p | p.1.1 ≤ T}) (MT N : @Measure ((ℝ≥0 × Ω) × ℝ) (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
(inferInstance : MeasurableSpace ℝ))) (hMT : MT = MK.restrict S) (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
(hμfinite : μ Set.univ < ∞) (hμclock : ∀ A : Set (ℝ≥0 × Ω), MeasurableSet[𝓕.rightCont.predictable] A →
μ A = ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) :=
𝓕.rightCont.predictable; μ.prod (X.ν.restrict (Iio (0 : ℝ))))) (hP2 : ∀ (s t : ℝ≥0), s ≤ t →
  ∀ (A : Set Ω), MeasurableSet[𝓕 s] A →
  ∀ (B : Set ℝ), MeasurableSet B →
    (∫⁻ ω in A, NX ω (Ioc s t ×ˢ B) ∂P) =
      P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) (τ : Ω → ℝ≥0) (hτBound : ∀ ω, τ ω ≤ T) (hτ : IsStoppingTime 𝓕.rightCont
(fun ω => (τ ω : WithTop ℝ≥0))) (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (w : ℝ → ℝ)
(hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (q : ℝ) (hq : 0 ≤ q) (a b L R : ℝ)
(ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b) (hL : 0 ≤ L) (hR : 0 ≤ R) (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
|w u - w v| ≤ L * |u - v|) (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R) (E : Set (ℝ≥0 × Ω)) (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
(hEregion : ∀ p ∈ E, Function.leftLim (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b)
(hν : (∫⁻ z : ℝ, ENNReal.ofReal (min (1 : ℝ) (z ^ 2)) ∂X.ν) < ⊤) (G : ((ℝ≥0 × Ω) × ℝ) → ℝ) (hG : ∀ p, G p = if p.1 ∈ E ∧ p.2 < 0 then
Real.exp (-(q * (p.1.1 : ℝ))) * (w (Function.leftLim (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
w (Function.leftLim (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1)) else 0)
(H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
(hH : H = fun p => if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0)  :
Integrable (fun ω => (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) - (∫ t, ∫ z, H ((t, ω), z)
∂(X.ν.restrict (Iio (0 : ℝ))) ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal))) P ∧ (∫ ω, ((∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
(∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ))) ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal))) ∂P) = 0 := by sorry
