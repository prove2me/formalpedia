-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_signed_jump_plus_HJB_expected_nonpos
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_original_signed_jump_plus_HJB_expected_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T10:40:16.386895+00:00
-- url     : https://prove2.me/theorems/ecfec8f9-f0fe-49ca-a538-0a926c82b3cc
-- title:
--   Original BV stopped nonlinear jump plus physical HJB drift has nonpositive signed mean
-- statement:
--   For the same original spectrally-negative bounded-variation Lévy process X and dividend strategy D, form the intrinsic source jump measure and centred signed nonlinear compensated jump residual M and actual deterministic physical-clock generator residual B. From the original generator upper bound on strictly positive interior reserve and explicit localisation/integrability assumptions, prove M+B integrable and expected M+B ≤ 0, discharging intrinsic jump count P2 and Fubini from proved source-specific theorems. This is a stochastic-budget bridge, not the remaining pathwise Stieltjes equality.
-- source:
--   P2-E 393b03a8, P3-C d345befb, P3-B 773f3823,36cfdb7a,5975ece6 all Proved and original-source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_c_bvchain_original_signed_jump_plus_HJB_expected_nonpos {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
(X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (T : ℝ≥0) (τ : Ω → ℝ≥0) (hτBound : ∀ ω, τ ω ≤ T) (hτ : IsStoppingTime 𝓕.rightCont
(fun ω => (τ ω : WithTop ℝ≥0))) (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (w : ℝ → ℝ)
(hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (q : ℝ) (hq : 0 ≤ q) (a b L R : ℝ)
(ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b) (hL : 0 ≤ L) (hR : 0 ≤ R) (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
|w u - w v| ≤ L * |u - v|) (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R) (E : Set (ℝ≥0 × Ω)) (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
(hEregion : ∀ p ∈ E, Function.leftLim (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b)
(hν : (∫⁻ z : ℝ, ENNReal.ofReal (min (1 : ℝ) (z ^ 2)) ∂X.ν) < ⊤) (G : ((ℝ≥0 × Ω) × ℝ) → ℝ) (hG : ∀ p, G p = if p.1 ∈ E ∧ p.2 < 0 then
Real.exp (-(q * (p.1.1 : ℝ))) * (w (Function.leftLim (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
w (Function.leftLim (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1)) else 0)
(H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
(hH : H = fun p => if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0)  (C : ℝ≥0∞)
(hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
  X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
(Upre : ℝ≥0 × Ω → ℝ)
(hUpre : ∀ p, Upre p = Function.leftLim
  (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1)
(hEcap : ∀ p ∈ E, ENNReal.ofReal (Upre p) < C)
(F : ℝ≥0 × Ω → ℝ)
(hF : ∀ p, F p = if p ∈ E then
  Real.exp (-(q * (p.1 : ℝ))) *
   (X.drift * deriv w (Upre p) +
    (∫ z in Iio (0 : ℝ), w (Upre p + z) - w (Upre p) ∂X.ν) -
    q * w (Upre p)) else 0)
(hFint : Integrable F ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)) :
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω => ((Measure.count.restrict
{u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0 => (u, X.X u ω -
Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)));
  let M : Ω → ℝ := fun ω => (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) - (∫ t, ∫ z, H ((t, ω), z)
∂(X.ν.restrict (Iio (0 : ℝ))) ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal));
  let B : Ω → ℝ := fun ω => (∫ t, F (t, ω) ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal));
  Integrable (fun ω => M ω + B ω) P ∧
    (∫ ω, M ω + B ω ∂P) ≤ 0 := by sorry
