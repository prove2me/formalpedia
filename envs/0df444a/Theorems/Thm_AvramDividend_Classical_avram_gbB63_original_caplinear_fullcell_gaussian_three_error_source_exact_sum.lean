-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB63_original_caplinear_fullcell_gaussian_three_error_source_exact_sum
-- name    : AvramDividend.Classical.avram_gbB63_original_caplinear_fullcell_gaussian_three_error_source_exact_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:38:49.226194+00:00
-- url     : https://prove2.me/theorems/6327c161-4b09-44ba-9a91-d05bfd314e6f
-- title:
--   Original interior caplinear finite physical Gaussian full-cell HJB Taylor source exact three-error algebra
-- statement:
--   The true original jump-free Gaussian Lévy source with actual dividend right-limits and physical full stopped grid admits the exact finite sum identity decomposing the caplinear payoff discounted spatial residual minus centred Gaussian first/second-order increments and generator drift into Taylor, variance cross, and discount remainders. This retains genuine physical full cells and the cap-linear interior cutoff b. This is the full-cell algebraic input needed alongside crossing-cell B59, signed dividend B60/B62 and source L1 bounds to close B54.
-- source:
--   Instantiate Proved original physical full mesh exact Taylor three-error sum A130 at V_b(y)=if y≤b then w(y) else w(b)+(y-b). No second derivative at the true cap C is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a130_original_gaussian_physically_full_mesh_three_error_source_exact_sum
open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB63_original_caplinear_fullcell_gaussian_three_error_source_exact_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (b : ℝ)
    (q : ℝ) (ω : Ω) (n m : ℕ) (ρ : ℝ≥0) :
    let Vb : ℝ → ℝ := fun y =>
      if y ≤ b then w y else w b + (y - b)
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℕ → ℝ := fun i => x + X.X (s i) ω - rightLimit D (s i) ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
    let H : ℕ → ℝ := fun i => E (s i) *
      (deriv Vb (Y i) * Z i + (iteratedDeriv 2 Vb (Y i) / 2) *
        (Z i^2 - (Δ : ℝ) * X.σ^2)) +
      (Δ : ℝ) * E (s i) * X.generator Vb (Y i)
    let F : ℕ → ℝ := fun i =>
      E (s i + Δ) * (Vb (Y i + R i) - Vb (Y i)) - H i
    let T : ℕ → ℝ := fun i => E (s i) *
      (Vb (Y i + R i) - Vb (Y i) - deriv Vb (Y i) * R i -
        (iteratedDeriv 2 Vb (Y i) / 2) * R i^2)
    let B : ℕ → ℝ := fun i => E (s i) *
      (iteratedDeriv 2 Vb (Y i) / 2) * (R i^2 - Z i^2)
    let C : ℕ → ℝ := fun i =>
      (E (s i + Δ) - E (s i)) * (Vb (Y i + R i) - Vb (Y i))
    let cut : ℕ → Prop := fun i => s i < ρ ∧ s i + Δ ≤ ρ
    (∑ i ∈ Finset.range m, if cut i then F i else 0) =
      (∑ i ∈ Finset.range m, if cut i then T i else 0) +
      (∑ i ∈ Finset.range m, if cut i then B i else 0) +
      (∑ i ∈ Finset.range m, if cut i then C i else 0) := by sorry
