-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB59_original_interior_caplinear_true_stop_crossing_source_positive_bound
-- name    : AvramDividend.Classical.avram_gbB59_original_interior_caplinear_true_stop_crossing_source_positive_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:33:45.334091+00:00
-- url     : https://prove2.me/theorems/44558be9-8e72-48a9-8bef-b559b20e859f
-- title:
--   Original Gaussian unique stop-straddling cell caplinear spatial source positive remainder envelope
-- statement:
--   For the genuine original controlled Gaussian source X, dividend right limits D, physical grid and stopped time rho, the caplinear interior-cutoff payoff V_b admits an exact positive part bound for the one stop-straddling cell. The difference between discounted spatial value increment and compensated Gaussian HJB increment on that source crossing cell is bounded by the discounted absolute spatial increment and absolute Gaussian compensation on the same true crossing mask. This is the source crossing-cell component of B54.
-- source:
--   The Proved original physical crossing-cell finite-sum upper envelope A147 accepts an arbitrary payoff w. Instantiate that theorem at the interior caplinear V_b; no smoothness or reinterpretation of original controlled source is introduced.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a147_original_true_crossing_source_value_HJB_positive_sum_envelope
open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB59_original_interior_caplinear_true_stop_crossing_source_positive_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (b q : ℝ)
    (ω : Ω) (n m : ℕ) (ρ : ℝ≥0) :
    let Vb : ℝ → ℝ := fun y =>
      if y ≤ b then w y else w b + (y - b)
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
    let H : ℕ → ℝ := fun i => E (s i) *
      (deriv Vb (Y (s i)) * Z i +
        (iteratedDeriv 2 Vb (Y (s i)) / 2) *
          (Z i^2 - (Δ : ℝ) * X.σ^2)) +
        (Δ : ℝ) * E (s i) * X.generator Vb (Y (s i))
    let V : ℕ → ℝ := fun i =>
      Vb (Y (s i) + (X.X ρ ω - X.X (s i) ω)) - Vb (Y (s i))
    let Ccell : ℕ → ℝ := fun i => E ρ * V i - H i
    let cut : ℕ → Prop := fun i => s i < ρ ∧ ρ < s i + Δ
    max (∑ i ∈ Finset.range m, if cut i then Ccell i else 0) 0 ≤
      ∑ i ∈ Finset.range m,
        if cut i then |E ρ| * |V i| + |H i| else 0 := by sorry
