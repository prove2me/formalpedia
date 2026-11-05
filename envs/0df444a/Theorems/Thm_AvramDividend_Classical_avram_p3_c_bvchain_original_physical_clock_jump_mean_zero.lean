-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_physical_clock_jump_mean_zero
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_original_physical_clock_jump_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T10:29:23.713342+00:00
-- url     : https://prove2.me/theorems/d345befb-e344-445b-ad81-49690a4204da
-- title:
--   Construct all intrinsic original predictable jump measures for stopped BV signed L1 centring
-- statement:
--   For the actual original spectrally negative bounded-variation Lévy process and original left-continuous dividend strategy D, construct the physical intrinsic jump measure NX, its predictable-space lift K, its probability bind MK, physical horizon set S and restriction MT definitionally. With only the original stopped clock/localised interior region and source integrability/Lipschitz assumptions of P3-B, prove the signed nonlinear compensated original jump functional integrable and exactly mean zero. The old hP2, hNX, hK, hMK, hST, hMT assumptions are all discharged, not reintroduced.
-- source:
--   Theorem 9d3f292d (Proved), P2-E 393b03a8 (Proved), P3-B bd3f3f6d (Proved). Authorisation to create only P3-C original helper.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_c_bvchain_original_physical_clock_jump_mean_zero {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
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
(hH : H = fun p => if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0)  :
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω => ((Measure.count.restrict
{u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0 => (u, X.X u ω -
Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)));
  Integrable (fun ω => (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) - (∫ t, ∫ z, H ((t, ω), z)
∂(X.ν.restrict (Iio (0 : ℝ))) ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal))) P ∧ (∫ ω, ((∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
(∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ))) ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal))) ∂P) = 0 := by sorry
