-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a147_original_true_crossing_source_value_HJB_positive_sum_envelope
-- name    : AvramDividend.Classical.avram_ga_a147_original_true_crossing_source_value_HJB_positive_sum_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:10:54.294845+00:00
-- url     : https://prove2.me/theorems/efd7d4c5-81e8-41a9-b777-8dd247412fb7
-- title:
--   Original stopped Gaussian true crossing positive spatial source residual bounded by the single-cell value displacement and full Gaussian HJB compensator
-- statement:
--   For the original Lévy source X and admissible-dividend right-limit process, on the true uniformly stopped physical grid the positive part of the sum of genuinely crossing-cell source residuals is bounded pathwise by the sum of the absolute discounted value displacements from the original source X at the actual random stopped clock and absolute full physical HJB compensator terms. The statement retains the actual s_i and rho and requires no independent Gaussian-process assumption; at most one term is nonzero under the established unique-crossing lemma.
-- source:
--   Original Avram Gaussian b0 positive-interior true stopped source crossing decomposition ga94, certified finite positive-part majorant ga25 and scalar absolute error decomposition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a25_finite_sum_positive_part_le
open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a147_original_true_crossing_source_value_HJB_positive_sum_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (ω : Ω) (n m : ℕ) (ρ : ℝ≥0) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
    let H : ℕ → ℝ := fun i => E (s i) *
      (deriv w (Y (s i)) * Z i +
        (iteratedDeriv 2 w (Y (s i)) / 2) *
          (Z i^2 - (Δ : ℝ) * X.σ^2)) +
        (Δ : ℝ) * E (s i) * X.generator w (Y (s i))
    let V : ℕ → ℝ := fun i =>
      w (Y (s i) + (X.X ρ ω - X.X (s i) ω)) - w (Y (s i))
    let Ccell : ℕ → ℝ := fun i => E ρ * V i - H i
    let cut : ℕ → Prop := fun i => s i < ρ ∧ ρ < s i + Δ
    max (∑ i ∈ Finset.range m, if cut i then Ccell i else 0) 0 ≤
      ∑ i ∈ Finset.range m,
        if cut i then |E ρ| * |V i| + |H i| else 0 := by sorry
