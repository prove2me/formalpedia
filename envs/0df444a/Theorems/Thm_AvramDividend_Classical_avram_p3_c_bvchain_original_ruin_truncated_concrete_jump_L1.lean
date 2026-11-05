-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_ruin_truncated_concrete_jump_L1
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_original_ruin_truncated_concrete_jump_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T11:02:05.563225+00:00
-- url     : https://prove2.me/theorems/2a7825dc-da45-4800-a336-3ea51206a27c
-- title:
--   Actual original ruin-truncated stopped BV source nonlinear jump L1 and zero mean
-- statement:
--   For true source original X,D at τ = (min(ruinTime X x D,n)).toNNReal, prove the genuine stopped nonlinear source jump functional with literal G,H,NX is integrable and exactly mean zero, deriving τ finite horizon and stopping certificate from the Proved original source 99c02ca9. This result needs no HJB generator and no free stopped kernel definitions.
-- source:
--   Original source P3-C concrete stopped signed jump d45641ff and original n-truncated ruin stopping theorem 99c02ca9.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_c_bvchain_original_ruin_truncated_concrete_jump_L1 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
(X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (n : ℕ) (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (w : ℝ → ℝ)
(hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (q : ℝ) (hq : 0 ≤ q) (a b L R : ℝ)
(ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b) (hL : 0 ≤ L) (hR : 0 ≤ R) (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
|w u - w v| ≤ L * |u - v|) (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R) (E : Set (ℝ≥0 × Ω)) (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
(hEregion : ∀ p ∈ E, Function.leftLim (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b)
(hν : (∫⁻ z : ℝ, ENNReal.ofReal (min (1 : ℝ) (z ^ 2)) ∂X.ν) < ⊤)  :
  let τ : Ω → ℝ≥0 := (fun ω : Ω => (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal);
  let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := (fun p : (ℝ≥0 × Ω) × ℝ =>
    if p.1 ∈ E ∧ p.2 < 0 then
      Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
         w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
    else 0);
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ :=
    fun p => if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0;
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω => ((Measure.count.restrict
{u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0 => (u, X.X u ω -
Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)));
  Integrable (fun ω => (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) - (∫ t, ∫ z, H ((t, ω), z)
∂(X.ν.restrict (Iio (0 : ℝ))) ∂(((volume : Measure ℝ).restrict (Icc 0 ((n : ℝ≥0) : ℝ))).map Real.toNNReal))) P ∧ (∫ ω, ((∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
(∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ))) ∂(((volume : Measure ℝ).restrict (Icc 0 ((n : ℝ≥0) : ℝ))).map Real.toNNReal))) ∂P) = 0 := by sorry
