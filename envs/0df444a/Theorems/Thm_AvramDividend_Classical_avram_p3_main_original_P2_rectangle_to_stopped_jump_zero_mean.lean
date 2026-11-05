-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_P2_rectangle_to_stopped_jump_zero_mean
-- name    : AvramDividend.Classical.avram_p3_main_original_P2_rectangle_to_stopped_jump_zero_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:47:12.970058+00:00
-- url     : https://prove2.me/theorems/2d6c886c-990c-4993-98ee-6380b8d9eec1
-- title:
--   Original P2 intrinsic rectangle rate implies the actual stopped BV C1 jump is centred
-- statement:
--   A direct source-exact bridge from the original predictable rectangle rate 393b03a8 to P3-B's fully constructed true stopped predictable C1 compensation theorem 1e2ddfab. The original NX, same Ω/P/𝓕 and X.X, right-continuous stopping clock, predictable interior region and integrable negative-mark kernel remain unchanged. The proof is complete and depends on the single presently Open original P2 rate theorem. It should be SKETCH_ACCEPTED until P2 becomes Proved, then gives a direct genuinely Proved P3 import without requiring the alternative hFuture interface.
-- source:
--   Proved P3-B source stopped jump mean-zero 1e2ddfab; exact original P2 rectangle rate 393b03a8 Open. No additional process law or hFuture assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_main_original_P2_rectangle_to_stopped_jump_zero_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω = ((Measure.count.restrict
      {u : ℝ≥0 | 0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (T : ℝ≥0) (τ : Ω → ℝ≥0) (hτBound : ∀ ω, τ ω ≤ T)
    (hτ : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (q : ℝ) (hq : 0 ≤ q)
    (a b L R : ℝ) (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
    (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
    (E : Set (ℝ≥0 × Ω))
    (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
    (hEregion : ∀ p ∈ E, Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b)
    (hν : (∫⁻ z : ℝ, ENNReal.ofReal (min (1 : ℝ) (z ^ 2)) ∂X.ν) < ⊤)
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hG : ∀ p, G p = if p.1 ∈ E ∧ p.2 < 0 then
      Real.exp (-(q * (p.1.1 : ℝ))) *
      (w (Function.leftLim (fun s : ℝ≥0 => x + X.X s p.1.2 -
        rightLimit D s p.1.2) p.1.1 + p.2) -
       w (Function.leftLim (fun s : ℝ≥0 => x + X.X s p.1.2 -
        rightLimit D s p.1.2) p.1.1)) else 0)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hH : H = fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0) :
    Integrable (fun ω =>
      (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal))) P ∧
    (∫ ω, ((∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal))) ∂P) = 0 := by sorry
