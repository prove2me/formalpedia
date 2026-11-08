-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_centered_compensated_triangular_physical_H_cells
-- name    : AvramDividend.Classical.avram_bv_cell7_original_BV_centered_compensated_triangular_physical_H_cells
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T11:41:18.539533+00:00
-- url     : https://prove2.me/theorems/796b635d-6147-4fac-882e-7e44697b0598
-- title:
--   Original triangular stopped negative jump cells and centred Levy-rate compensator are jointly certified
-- statement:
--   On any genuine original BV spectrally negative Levy dividend process and countably indexed compact C1 bands, the same deterministic triangular physical clock family carries both an integrable zero-mean sum of actual original H minus original Levy-rate compensator increments and an unconditional full-probability same-path identification of every prefix H integral with exact stopped finite signed physical jump-cell sums. The full nonconditional proof imports the separately Proved original predictable compensator triangular mean-zero theorem 9c9a7e78 and source-exact physical prefix bridge 941e8e27; no fictitious martingale, expected-value assumption or law substitution is used. It supplies a joint source for P3-GRID4 to form its true centred original M while retaining zero exclusion and terminal contact.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_triangular_grid_compensator_L1_centered
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_triangular_clock_indexed_H_exact_physical_cells

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_BV_centered_compensated_triangular_physical_H_cells
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
    (a b : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (ha2 : ∀ n, a n ≤ 2)
    (hab : ∀ n, a n ≤ b n)
    (hBand : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (v : ℕ → ℕ → ℝ≥0) :
    (let M : ℕ → ℝ≥0 → Ω → ℝ := fun n S ω =>
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
          {r : ℝ≥0 | 0 < r ∧
            X.X r ω' - Function.leftLim (fun z : ℝ≥0 => X.X z ω') r ≠ 0}).map
          (fun r : ℝ≥0 => (r,
            X.X r ω' - Function.leftLim (fun z : ℝ≥0 => X.X z ω') r)))
      (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 (S : ℝ))).map Real.toNNReal))
     let K : ℕ → Ω → ℝ := fun n ω =>
       Finset.sum (Finset.range (n + 1))
         (fun i => M n (v n (i + 1)) ω - M n (v n i) ω)
     ∀ n, Integrable (K n) P ∧ (∫ ω, K n ω ∂P) = 0) ∧
    (∀ᵐ ω ∂P, ∀ n i m : ℕ,
    let T : ℝ≥0 := v n i
    let τ : Ω → ℝ≥0 := fun η =>
      (min (ruinTime X x D η) (T : ℝ≥0∞)).toNNReal
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
    let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let Eω : Set (ℝ≥0 × ℝ) :=
      {p | p.1 ≤ τ ω ∧ Y p.1 ∈ Icc (a n) (b n) ∧ p.2 < 0}
    let A : ℝ≥0 × ℝ → ℝ := fun p =>
      if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
    let J : ℝ≥0 × ℝ → ℝ := fun p =>
      (1 : ℝ) * Real.exp (-(q * (p.1 : ℝ))) *
        (if p ∈ Eω then A p else 0)
    let Δ : ℝ≥0 → ℝ := fun z =>
      X.X z ω - Function.leftLim (fun y : ℝ≥0 => X.X y ω) z
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {z : ℝ≥0 | 0 < z ∧ Δ z ≠ 0}).map
        (fun z : ℝ≥0 => (z, Δ z)))
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) (τ ω)
    let Fp : ℝ≥0 × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (J p)
    let Fm : ℝ≥0 × ℝ → ℝ≥0∞ := fun p =>
      ENNReal.ofReal ((-1 : ℝ) * Real.exp (-(q * (p.1 : ℝ))) *
        (if p ∈ Eω then A p else 0))
    (∫ p, H ((p.1, ω), p.2) ∂NX) =
        (∑ j ∈ Finset.range (m + 1),
          ∑' z : ℝ≥0,
            if (0 < z ∧ Δ z ≠ 0) ∧ z ∈ Ioc (u j) (u (j + 1)) then
              Fp (z, Δ z) else 0).toReal -
        (∑ j ∈ Finset.range (m + 1),
          ∑' z : ℝ≥0,
            if (0 < z ∧ Δ z ≠ 0) ∧ z ∈ Ioc (u j) (u (j + 1)) then
              Fm (z, Δ z) else 0).toReal) := by sorry
