-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_canonical_ruin_contact_potential_sum_prefix_plus_one_cell
-- name    : AvramDividend.Classical.avram_jump6_B_original_canonical_ruin_contact_potential_sum_prefix_plus_one_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:46:38.53517+00:00
-- url     : https://prove2.me/theorems/65b46381-f041-452f-8936-f3499f80ff14
-- title:
--   Exact original stopped physical potential sum equals precontact prefix plus crossing cell
-- statement:
--   When the exact canonical physical grid first reaches the true stopped clock rho in cell i, all later signed physical potential terms vanish. Hence the original full source-exact discounted sum is precisely the strict prefix sum plus the one genuine crossing cell, with the true Levy sample path and right-limit dividend values.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_original_canonical_ruin_contact_potential_sum_prefix_plus_one_cell
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (w : ℝ → ℝ)
    (n j i : ℕ) (ρ : ℝ≥0) (hρn : ρ ≤ (n : ℝ≥0))
    (hi : i < (n + 1) * (j + 1))
    (hcross : min (((i + 1 : ℕ) : ℝ≥0) /
        ((j + 1 : ℕ) : ℝ≥0)) ρ = ρ) :
    let v : ℕ → ℝ≥0 := fun l =>
      min ((l : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ρ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun l =>
      x + X.X (v (l + 1)) ω - rightLimit D (v l) ω
    (∑ l ∈ Finset.range ((n + 1) * (j + 1)),
      E (v (l + 1)) * (w (Y (v (l + 1))) - w (Z l))) =
      (∑ l ∈ Finset.range i,
        E (v (l + 1)) * (w (Y (v (l + 1))) - w (Z l))) +
      E ρ * (w (Y ρ) - w (Z i)) := by sorry
