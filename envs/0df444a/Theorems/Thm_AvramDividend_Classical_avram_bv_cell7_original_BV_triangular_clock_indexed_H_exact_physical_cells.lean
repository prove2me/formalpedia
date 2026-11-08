-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_triangular_clock_indexed_H_exact_physical_cells
-- name    : AvramDividend.Classical.avram_bv_cell7_original_BV_triangular_clock_indexed_H_exact_physical_cells
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T11:26:43.661684+00:00
-- url     : https://prove2.me/theorems/941e8e27-72fb-46cd-821e-be4ba9962dc3
-- title:
--   Original BV indexed triangular prefix clocks share the exact compensated H stopped finite jump-cell source
-- statement:
--   For every deterministic triangular physical prefix-clock family v(n,i) and countable family of interior C1 localisation bands in the true original BV spectrally negative Levy dividend problem, a single original full-probability sample-path event simultaneously identifies the full H nonlinear negative-jump integral with its actual stopped finite signed physical-cell jump source at every prefix clock, band index and finite cell subdivision. This is the missing pathwise source identification interface for the Proved 9c9a7e78 centred compensated triangular-grid increments, and follows from countable ae_all_iff applied twice to the independently Proved original stopped single-band physical H identity a8af58a2. No random horizon, law substitution or artificial stochastic hypotheses are introduced.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_localised_compensator_H_exact_stopped_grid

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_BV_triangular_clock_indexed_H_exact_physical_cells
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (a b : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (hab : ∀ n, a n ≤ b n)
    (hBand : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (v : ℕ → ℕ → ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ n i m : ℕ,
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
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2)
            p.1.1 + p.2) -
           w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2)
            p.1.1))
      else 0
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
    let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let Eω : Set (ℝ≥0 × ℝ) :=
      {p | p.1 ≤ τ ω ∧ Y p.1 ∈ Icc (a n) (b n) ∧ p.2 < 0}
    let K : ℝ≥0 × ℝ → ℝ := fun p =>
      if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
    let J : ℝ≥0 × ℝ → ℝ := fun p =>
      (1 : ℝ) * Real.exp (-(q * (p.1 : ℝ))) *
        (if p ∈ Eω then K p else 0)
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
        (if p ∈ Eω then K p else 0))
    (∫ p, H ((p.1, ω), p.2) ∂NX) =
        (∑ j ∈ Finset.range (m + 1),
          ∑' z : ℝ≥0,
            if (0 < z ∧ Δ z ≠ 0) ∧ z ∈ Ioc (u j) (u (j + 1)) then
              Fp (z, Δ z) else 0).toReal -
        (∑ j ∈ Finset.range (m + 1),
          ∑' z : ℝ≥0,
            if (0 < z ∧ Δ z ≠ 0) ∧ z ∈ Ioc (u j) (u (j + 1)) then
              Fm (z, Δ z) else 0).toReal := by sorry
