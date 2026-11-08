-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_turn13_allcap_predictable_two_scale_grid_L1
-- name    : AvramDividend.Classical.avram_p3_grid4_turn13_allcap_predictable_two_scale_grid_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T11:25:59.024484+00:00
-- url     : https://prove2.me/theorems/aef644be-a008-4612-9e40-bd71952b4a34
-- title:
--   All-cap original BV predictable spatial bands yield centred two-scale stopped grids
-- statement:
--   For every positive dividend cap, construct one sequence of compact predictable pre-reserve bands that exhausts the strict interior, and prove the original Lévy jump compensated increments are integrable and centred on every finite stopped physical row, independently for each compact band index.
-- source:
--   Uses the proved all-cap compact-band exhaustion theorem fc04d4a7 and the proved original stopped-grid compensated jump theorem 8ee10b6c; no extra probabilistic assumptions or surrogate process.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_finite_physical_grid_increment_centered
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_allcap_full_predictable_compact_bands
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_turn13_allcap_predictable_two_scale_grid_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (u : ℕ → ℕ → ℝ≥0) :
    ∃ a b : ℕ → ℝ,
      (∀ k, 0 < a k) ∧
      (∀ k, a k ≤ 2) ∧
      (∀ k, a k ≤ b k) ∧
      (∀ k, Icc (a k / 2) (b k) ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (a k) (b k)) ∧
      (let K : ℕ → ℕ → Ω → ℝ := fun n k ω =>
        let M : ℝ≥0 → Ω → ℝ := fun S ω' =>
          let τ : Ω → ℝ≥0 := fun ω'' =>
            (min (ruinTime X x D ω'') (S : ℝ≥0∞)).toNNReal
          let E : Set (ℝ≥0 × Ω) := {p |
            (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
            Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a k) (b k)}
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
          let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω'' =>
            ((Measure.count.restrict
              {v : ℝ≥0 | 0 < v ∧
                X.X v ω'' - Function.leftLim (fun z : ℝ≥0 => X.X z ω'') v ≠ 0}).map
              (fun v : ℝ≥0 => (v,
                X.X v ω'' - Function.leftLim (fun z : ℝ≥0 => X.X z ω'') v)))
          (∫ p, H ((p.1, ω'), p.2) ∂(NX ω')) -
          (∫ t, ∫ z, H ((t, ω'), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
            ∂(((volume : Measure ℝ).restrict (Icc 0 (S : ℝ))).map Real.toNNReal))
        Finset.sum (Finset.range (n + 1)) (fun i => M (u n (i + 1)) ω - M (u n i) ω)
      ∀ n k, Integrable (K n k) P ∧ (∫ ω, K n k ω ∂P) = 0) := by sorry
