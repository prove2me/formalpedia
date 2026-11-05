-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_real_ruin_compact_source_jump_centered
-- name    : AvramDividend.Classical.avram_p3_bv_original_real_ruin_compact_source_jump_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T10:55:06.854282+00:00
-- url     : https://prove2.me/theorems/349d07b1-bd7a-4982-b38c-9f86f125304c
-- title:
--   Actual original BV stopped compact negative-jump martingale is integrable and centred at every real horizon
-- statement:
--   The exact original Lévy intrinsic negative jump count, actual controlled pre-reserve compact band and true ruin stopping time truncated at an arbitrary nonnegative real horizon give an integrable centred discounted negative-jump compensation residual. This extends the accepted integer-horizon source result, removes discretisation of the verification clock, and uses the original P2 rectangle compensator without surrogate processes.
-- source:
--   Original genuine stopped P2 zero-mean 2d6c886c, controlled compact prestate predictable 5115705e and separately Proved real-horizon bounded ruin stopping avram_p3_bv_original_real_truncated_ruin_nnreal_stopping.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_real_truncated_ruin_nnreal_stopping
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_controlled_prestate_compact_band_predictable
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_P2_rectangle_to_stopped_jump_zero_mean

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_real_ruin_compact_source_jump_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (a b L R : ℝ) (ha : 0 < a) (ha2 : a ≤ 2)
    (hab : a ≤ b) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
    (hν : (∫⁻ z : ℝ, ENNReal.ofReal (min (1 : ℝ) (z ^ 2)) ∂X.ν) < ⊤) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let E : Set (ℝ≥0 × Ω) := {p | Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b}
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if p.1 ∈ E ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Function.leftLim (fun s : ℝ≥0 => x + X.X s p.1.2 -
            rightLimit D s p.1.2) p.1.1 + p.2) -
           w (Function.leftLim (fun s : ℝ≥0 => x + X.X s p.1.2 -
            rightLimit D s p.1.2) p.1.1)) else 0
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
    Integrable (fun ω =>
      (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal))) P ∧
    (∫ ω, ((∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal))) ∂P) = 0 := by sorry
