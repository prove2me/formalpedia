-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_compact_ruin_clock_source_signed_HJB_mean
-- name    : AvramDividend.Classical.avram_bv_env3_original_compact_ruin_clock_source_signed_HJB_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T14:30:33.825429+00:00
-- url     : https://prove2.me/theorems/9b364d89-2c9f-4674-b009-56c465476d85
-- title:
--   Original BV ruin-clock compact predictable compensated source HJB signed mean
-- statement:
--   On any original bounded-variation ruin-clock compact positive interior band, the actual compensated negative-jump M and physical generator drift B defined using the original X, ν, source marked jumps and predictable stopped band have an integrable sum with nonpositive expectation. Automatically derives true ruin stopping, predictable measurability and bounds from admissibility and local C1 assumptions. Global boundary passage remains separate.
-- source:
--   Composition of Proved original admissible compact localisation eb00e27d and Proved original signed C1 source martingale drift 2afcaa98.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_original_compact_ruin_clock_source_signed_HJB_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (T : ℝ≥0) (a b : ℝ) (ha : 0 < a) (ha2 : a ≤ 2)
    (hab : a ≤ b)
    (hBand : Icc (a / 2) b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let E : Set (ℝ≥0 × Ω) := {p |
      (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b}
    let Upre : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if p.1 ∈ E ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (Upre p.1 + p.2) - w (Upre p.1))
      else 0
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
    let F : ℝ≥0 × Ω → ℝ := fun p =>
      if p ∈ E then
        Real.exp (-(q * (p.1 : ℝ))) *
          (X.drift * deriv w (Upre p) +
            (∫ z in Iio (0 : ℝ), w (Upre p + z) - w (Upre p) ∂X.ν) -
            q * w (Upre p))
      else 0
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let M : Ω → ℝ := fun ω =>
      (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal))
    let B : Ω → ℝ := fun ω =>
      ∫ t, F (t, ω) ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)
    Integrable (fun ω => M ω + B ω) P ∧
      (∫ ω, M ω + B ω ∂P) ≤ 0 := by sorry
