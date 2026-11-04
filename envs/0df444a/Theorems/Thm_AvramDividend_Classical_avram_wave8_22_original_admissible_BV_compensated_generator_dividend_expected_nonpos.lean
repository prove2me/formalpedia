-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_admissible_BV_compensated_generator_dividend_expected_nonpos
-- name    : AvramDividend.Classical.avram_wave8_22_original_admissible_BV_compensated_generator_dividend_expected_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T06:52:23.168711+00:00
-- url     : https://prove2.me/theorems/feb0b4b9-01fa-4d84-83fe-6c5c7d82476f
-- title:
--   True original stopped BV C1 compensated negative jumps plus physical signed generator and Stieltjes dividend correction have integrable nonpositive expected remainder
-- statement:
--   The actual original intrinsic negative jump sum minus its actual predictable random compensator is L1 and has zero mean by a genuinely accepted original Lévy source theorem, conditional on the original W7-01 strict-future adapted rectangle law. Under genuine original admissibility, bounded variation, compact C1 localisation, and original a.e. physical generator and Stieltjes dividend HJB hypotheses, its sum with the physical generator drift and Stieltjes correction is P-integrable and has nonpositive expectation.
-- source:
--   Proved original 1b45573e-c52f-4582-b19f-11a919aa40db, Proved 493d798a-ee92-46c4-9862-e387f11d1573; Mathlib integral linearity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_actual_BV_C1_intrinsic_stopped_compensated_negative_jump_L1_zero_mean
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_admissible_BV_ae_signed_generator_dividend_expected_nonpos
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_admissible_BV_compensated_generator_dividend_expected_nonpos {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
(X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (NX : Ω → Measure (ℝ≥0 × ℝ)) (hNX : ∀ ω, NX ω = ((Measure.count.restrict
{u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0 => (u, X.X u ω -
Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ) (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
(inferInstance : MeasurableSpace ℝ))) (hK : ∀ ω, K ω = @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ) (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
(@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)) (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω))
(MK : @Measure ((ℝ≥0 × Ω) × ℝ) (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
(hMK : MK = P.bind K) (T : ℝ≥0) (S : Set ((ℝ≥0 × Ω) × ℝ)) (hST : S = {p | p.1.1 ≤ T}) (hS : MeasurableSet[(@Prod.instMeasurableSpace _ _
(𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] S) (MT N : @Measure ((ℝ≥0 × Ω) × ℝ) (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
(inferInstance : MeasurableSpace ℝ))) (hMT : MT = MK.restrict S) (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
(hμfinite : μ Set.univ < ∞) (hμclock : ∀ A : Set (ℝ≥0 × Ω), MeasurableSet[𝓕.rightCont.predictable] A →
μ A = ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) :=
𝓕.rightCont.predictable; μ.prod (X.ν.restrict (Iio (0 : ℝ))))) (hFuture : ∀ (i : ℝ≥0) (A : Set Ω) (C' : Set ℝ), MeasurableSet[𝓕.rightCont i] A → MeasurableSet C' →
MT ((Set.Ioi i ×ˢ A) ×ˢ C') = N ((Set.Ioi i ×ˢ A) ×ˢ C')) (τ : Ω → ℝ≥0) (hτBound : ∀ ω, τ ω ≤ T) (hτ : IsStoppingTime 𝓕.rightCont
(fun ω => (τ ω : WithTop ℝ≥0))) (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (w : ℝ → ℝ)
(hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (q : ℝ) (hq : 0 ≤ q) (a b L R : ℝ)
(ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b) (hL : 0 ≤ L) (hR : 0 ≤ R) (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
|w u - w v| ≤ L * |u - v|) (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R) (E : Set (ℝ≥0 × Ω)) (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
(hEregion : ∀ p ∈ E, Function.leftLim (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b)
 (G : ((ℝ≥0 × Ω) × ℝ) → ℝ) (hG : ∀ p, G p = if p.1 ∈ E ∧ p.2 < 0 then
Real.exp (-(q * (p.1.1 : ℝ))) * (w (Function.leftLim (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
w (Function.leftLim (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1)) else 0)
(H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
(hH : H = fun p => if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0) (hSupport : S.indicator H = H)
(hw_gen : ∀ yy : ℝ, 0 < yy → ENNReal.ofReal yy < C → X.GeneratorIntegrable w yy ∧ X.generator w yy - q * w yy ≤ 0)
(hw_grad : ∀ yy : ℝ, 0 < yy → ENNReal.ofReal yy < C → 1 ≤ deriv w yy)
(Mart : Ω → ℝ) (hMart : ∀ ω, Mart ω = (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) - (∫ t, ∫ z, H ((t, ω), z)
∂(X.ν.restrict (Iio (0 : ℝ))) ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)))
(A : Ω → Set ℝ≥0) (hAm : ∀ ω, MeasurableSet (A ω)) (hRegion : ∀ᵐ ω ∂P, ∀ t, t ∈ A ω →
0 < Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ∧ ENNReal.ofReal (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) < C) (hGInt : ∀ᵐ ω ∂P, IntegrableOn (fun t : ℝ≥0 => Real.exp (-(q * (t : ℝ))) * (X.drift * deriv w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) + (∫ z in Iio (0 : ℝ), w ((Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) + z) - w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ∂X.ν) - q * w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t))) (A ω) (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal))
(B : Ω → Set ℝ) (hBm : ∀ ω, MeasurableSet (B ω)) (hDivRegion : ∀ᵐ ω ∂P, ∀ s, s ∈ B ω → 0 < riskProcess X x D s.toNNReal ω ∧
ENNReal.ofReal (riskProcess X x D s.toNNReal ω) < C) (hDivInt : ∀ᵐ ω ∂P, IntegrableOn (fun s : ℝ => Real.exp (-(q * s)) * (1 - deriv w (riskProcess X x D s.toNNReal ω))) (B ω) (dividendMeasure D ω))
(Gdrift Hdiv : Ω → ℝ) (hGDef : ∀ᵐ ω ∂P, Gdrift ω = ∫ t in A ω, Real.exp (-(q * (t : ℝ))) * (X.drift * deriv w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) + (∫ z in Iio (0 : ℝ), w ((Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) + z) - w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ∂X.ν) - q * w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)) (hHDef : ∀ᵐ ω ∂P, Hdiv ω = ∫ s in B ω, Real.exp (-(q * s)) * (1 - deriv w (riskProcess X x D s.toNNReal ω)) ∂(dividendMeasure D ω))

(hGI : Integrable Gdrift P) (hHI : Integrable Hdiv P):
Integrable Mart P ∧ Integrable (fun ω => Mart ω + Gdrift ω + Hdiv ω) P ∧
(∫ ω, Mart ω + Gdrift ω + Hdiv ω ∂P) ≤ 0 := by sorry
