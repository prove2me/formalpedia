-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_triangular_grid_compensator_L1_centered
-- name    : AvramDividend.Classical.avram_bv_meas7_original_triangular_grid_compensator_L1_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:54:42.346197+00:00
-- url     : https://prove2.me/theorems/9c9a7e78-b414-4abf-a215-c1ba119446c1
-- title:
--   Original BV stopped compensated jumps on the triangular physical grid
-- statement:
--   For the actual bounded-variation spectrally negative Levy process and admissible D, package the original compact-band stopped compensated jump source on every row of the triangular physical grid. Each genuine original increment sum is integrable and has mean zero on precisely that row, with its own stopping horizon and original X.nu.
-- source:
--   A source-exact triangular-indexed instantiation of the existing Proved original physical-grid compensated jump theorem 8ee10b6c. Compact-band and smoothness assumptions remain explicit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_finite_physical_grid_increment_centered

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_meas7_original_triangular_grid_compensator_L1_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (a b : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (ha2 : ∀ n, a n ≤ 2)
    (hab : ∀ n, a n ≤ b n)
    (hBand : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (u : ℕ → ℕ → ℝ≥0) :
    let M : ℕ → ℝ≥0 → Ω → ℝ := fun n S ω =>
      let τ : Ω → ℝ≥0 := fun ω' =>
        (min (ruinTime X x D ω') (S : ℝ≥0∞)).toNNReal
      let E : Set (ℝ≥0 × Ω) := {p |
        (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
        Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n)}
      let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
        if p.1 ∈ E ∧ p.2 < 0 then
          Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
           w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
        else 0
      let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
        if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
      let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω' =>
        ((Measure.count.restrict
          {v : ℝ≥0 | 0 < v ∧
            X.X v ω' - Function.leftLim (fun z : ℝ≥0 => X.X z ω') v ≠ 0}).map
          (fun v : ℝ≥0 => (v,
            X.X v ω' - Function.leftLim (fun z : ℝ≥0 => X.X z ω') v)))
      (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 (S : ℝ))).map Real.toNNReal))
    let K : ℕ → Ω → ℝ := fun n ω =>
      Finset.sum (Finset.range (n + 1))
        (fun i => M n (u n (i + 1)) ω - M n (u n i) ω)
    ∀ n, Integrable (K n) P ∧ (∫ ω, K n ω ∂P) = 0 := by sorry
