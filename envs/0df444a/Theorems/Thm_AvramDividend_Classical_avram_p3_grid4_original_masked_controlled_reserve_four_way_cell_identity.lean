-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_masked_controlled_reserve_four_way_cell_identity
-- name    : AvramDividend.Classical.avram_p3_grid4_original_masked_controlled_reserve_four_way_cell_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T14:22:59.942516+00:00
-- url     : https://prove2.me/theorems/3ee6f60d-3c00-4786-aa70-4b3ee814349c
-- title:
--   Four-way original controlled BV reserve cell decomposition under stopping masks
-- statement:
--   The authentic reserve U(t)=x+X.X(t)-rightLimit(D,t) has the exact cellwise four-way split into original BV deterministic drift, residual R, negative-jump sum J and right-limit dividend control. The equality survives arbitrary real stopping and interior/cap localisation weights. This is the source-exact masked generalisation of accepted original four-way grid identity 2a606877, needed to match the genuine masked B_n and stopped cash/terminal finite-grid inequality in 2bc848f9.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_masked_controlled_reserve_four_way_cell_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (u : ℕ → ℝ≥0) (a : ℕ → ℝ) (n : ℕ) :
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
    let R : ℝ≥0 → ℝ := fun t =>
      ((t : ℝ) * X.drift - X.X t ω) - J t
    let U : ℝ≥0 → ℝ := fun t =>
      x + X.X t ω - rightLimit D t ω
    (∑ i ∈ Finset.range n, a i * (U (u (i + 1)) - U (u i))) =
      (∑ i ∈ Finset.range n, a i *
        (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift)) +
      (∑ i ∈ Finset.range n, a i * (R (u i) - R (u (i + 1)))) -
      (∑ i ∈ Finset.range n, a i * (J (u (i + 1)) - J (u i))) -
      (∑ i ∈ Finset.range n, a i *
        (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) := by sorry
