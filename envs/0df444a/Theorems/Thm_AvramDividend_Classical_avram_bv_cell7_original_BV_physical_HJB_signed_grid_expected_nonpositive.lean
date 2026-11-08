-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_physical_HJB_signed_grid_expected_nonpositive
-- name    : AvramDividend.Classical.avram_bv_cell7_original_BV_physical_HJB_signed_grid_expected_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T11:15:55.378012+00:00
-- url     : https://prove2.me/theorems/b86d7e06-a45a-4b61-954c-67f2b90d9579
-- title:
--   Original BV compensated HJB signed expected budget holds for exact stopped physical Lévy jump cells
-- statement:
--   Given actual original spectrally negative Levy X, admissible original dividends D, and a compact interior C1 localisation band, there is a genuine original stopped physical signed negative-jump-cell source J. Almost surely J equals the exact positive-minus-negative sums over the real original Lévy jump times in the clipped half-open physical cells, including final ruin/horizon contact and excluding the origin. Its difference from the exact original Levy rate compensator plus original stopped generator-time source is integrable with nonpositive expectation. This combines the separately Proved original indexed compensated HJB source expectation theorem 6d66798c with the unconditional original H-to-physical-grid pathwise equality a8af58a2. No extra random centring or source identity assumptions are made.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_indexed_compact_bands_signed_budget
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_localised_compensator_H_exact_stopped_grid

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_BV_physical_HJB_signed_grid_expected_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hwC1 : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (T : ℝ≥0) (a b : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (ha2 : ∀ n, a n ≤ 2)
    (hab : ∀ n, a n ≤ b n)
    (hBand : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (n m : ℕ) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
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
    let F : (ℝ≥0 × Ω) → ℝ := fun p =>
      if p ∈ E then Real.exp (-(q * (p.1 : ℝ))) *
        (X.drift * deriv w (Function.leftLim
          (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) +
         (∫ z in Iio (0 : ℝ),
            w (Function.leftLim
              (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1 + z) -
            w (Function.leftLim
              (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) ∂X.ν) -
         q * w (Function.leftLim
          (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1))
      else 0
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict
        {u : ℝ≥0 | 0 < u ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let Comp : Ω → ℝ := fun ω =>
      ∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)
    let B : Ω → ℝ := fun ω =>
      ∫ t, F (t, ω)
        ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)
    ∃ J : Ω → ℝ,
      (∀ᵐ ω ∂P,
        let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        let Eω : Set (ℝ≥0 × ℝ) :=
          {p | p.1 ≤ τ ω ∧ Y p.1 ∈ Icc (a n) (b n) ∧ p.2 < 0}
        let K : ℝ≥0 × ℝ → ℝ := fun p =>
          if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
        let R : ℝ≥0 × ℝ → ℝ := fun p =>
          (1 : ℝ) * Real.exp (-(q * (p.1 : ℝ))) *
            (if p ∈ Eω then K p else 0)
        let Δ : ℝ≥0 → ℝ := fun v =>
          X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
        let u : ℕ → ℝ≥0 := fun i =>
          min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) (τ ω)
        let Fp : ℝ≥0 × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (R p)
        let Fm : ℝ≥0 × ℝ → ℝ≥0∞ := fun p =>
          ENNReal.ofReal ((-1 : ℝ) * Real.exp (-(q * (p.1 : ℝ))) *
            (if p ∈ Eω then K p else 0))
        J ω =
          (∑ i ∈ Finset.range (m + 1),
            ∑' v : ℝ≥0,
              if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc (u i) (u (i + 1)) then
                Fp (v, Δ v) else 0).toReal -
          (∑ i ∈ Finset.range (m + 1),
            ∑' v : ℝ≥0,
              if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc (u i) (u (i + 1)) then
                Fm (v, Δ v) else 0).toReal) ∧
      Integrable (fun ω => J ω - Comp ω + B ω) P ∧
      (∫ ω, J ω - Comp ω + B ω ∂P) ≤ 0 := by sorry
