-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_finite_physical_grid_increment_centered
-- name    : AvramDividend.Classical.avram_bv_meas7_original_finite_physical_grid_increment_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:13:01.639026+00:00
-- url     : https://prove2.me/theorems/8ee10b6c-1705-4d7d-a170-0dba15abd6c6
-- title:
--   Centred genuine original compensated jump sum over a finite physical grid
-- statement:
--   For the original spectrally negative bounded-variation Levy process and admissible actual dividend process, fix one compact localisation index and any finite sequence of nonnegative physical grid clocks. The finite sum of the true stopped compensated negative-jump increments at successive clocks is P-integrable and has exactly zero expectation. All jumps are sourced from the intrinsic original X.X counting measure, compensated by X.nu; there is no proxy or new stochastic centring assumption.
-- source:
--   A genuine original-source finite-grid reduction from the Proved/public clock-increment theorem 0f48f2b4-7448-492d-a72d-733868072f74. The telescoping identity ∑_{i<k}(M(u(i+1))-M(u(i)))=M(u(k))-M(u(0)) identifies the grid sum with an already centred L1 original compensated clock increment. The result can supply the jump-martingale part of the original stopped triple-mesh source, but does not claim identification with its cash/terminal or drift R terms.

import Mathlib
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_compact_stopped_clock_increment_centered

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_meas7_original_finite_physical_grid_increment_centered
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
    (n k : ℕ) (u : ℕ → ℝ≥0) :
    let M : ℝ≥0 → Ω → ℝ := fun S ω =>
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
          {u : ℝ≥0 | 0 < u ∧
            X.X u ω' - Function.leftLim (fun v : ℝ≥0 => X.X v ω') u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω' - Function.leftLim (fun v : ℝ≥0 => X.X v ω') u)))
      (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 (S : ℝ))).map Real.toNNReal))
    Integrable (fun ω => Finset.sum (Finset.range k)
      (fun i => M (u (i + 1)) ω - M (u i) ω)) P ∧
    (∫ ω, (Finset.sum (Finset.range k)
      (fun i => M (u (i + 1)) ω - M (u i) ω)) ∂P) = 0 := by sorry
