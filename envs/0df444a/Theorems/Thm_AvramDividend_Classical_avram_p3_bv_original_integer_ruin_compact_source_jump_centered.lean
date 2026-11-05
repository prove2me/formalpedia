-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_integer_ruin_compact_source_jump_centered
-- name    : AvramDividend.Classical.avram_p3_bv_original_integer_ruin_compact_source_jump_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T10:31:56.054913+00:00
-- url     : https://prove2.me/theorems/b36bc5ef-9e92-445c-909b-ed402c80fd67
-- title:
--   Actual original BV compact pre-source compensated jumps have zero mean on the true integer-ruin clock
-- statement:
--   For the actual intrinsic marked negative jumps of the given original spectrally negative BV Lévy process, with the original admissible dividend strategy's finite integer-truncated ruin stopping time and its truly predictable compact pre-source reserve event, the canonical stopped compensated jump integral is integrable and centred. The original P2 rectangle compensator and true stopping/predictability theorems are applied with no artificial compensation assumptions. Explicit compact regularity and Lévy energy hypotheses remain for the later localisation passage.
-- source:
--   Accepted original stopped P2 jump zero-mean theorem 2d6c886c; genuine integer truncated ruin stopping theorem 99c02ca9; original controlled compact pre-jump predictable region theorem 5115705e; exact source NX on X.X, no surrogate process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_integer_truncated_ruin_nnreal_stopping
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_controlled_prestate_compact_band_predictable
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_P2_rectangle_to_stopped_jump_zero_mean
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_integer_ruin_compact_source_jump_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (q : ℝ) (hq : 0 ≤ q)
    (n : ℕ) (a b L R : ℝ) (ha : 0 < a) (ha2 : a ≤ 2)
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
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
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
        ∂(((volume : Measure ℝ).restrict (Icc 0 (n : ℝ))).map
          Real.toNNReal))) P ∧
    (∫ ω, ((∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 (n : ℝ))).map
          Real.toNNReal))) ∂P) = 0 := by sorry
