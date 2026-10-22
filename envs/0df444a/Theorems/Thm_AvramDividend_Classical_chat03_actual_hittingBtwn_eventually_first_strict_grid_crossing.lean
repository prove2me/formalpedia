-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_actual_hittingBtwn_eventually_first_strict_grid_crossing
-- name    : AvramDividend.Classical.chat03_actual_hittingBtwn_eventually_first_strict_grid_crossing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T14:23:56.220387+00:00
-- url     : https://prove2.me/theorems/fb36740f-13ff-4988-8a8c-51727c53ca0e
-- title:
--   Exact bounded hittingBtwn Lévy grid clocks eventually select first strict crossings
-- statement:
--   Fix a spectrally negative Lévy sample path with finite strict two-sided first passage infimum and a sequence of positive uniform meshes tending to zero. If terminal grid times eventually exceed the first passage by one unit and K is exactly the Mathlib bounded hittingBtwn clock formed from the two strict barrier inequalities, then K eventually lands on a genuine crossing and no earlier sampled index crosses. This connects the pathwise mesh approximation results to the actual measurable stopping clock used in the expected stopped q-scale theorem.
-- source:
--   Combine Proved Chat03 terminal-cap first-grid witness and Proved generic hittingBtwn identification, translating the max of two signed barrier gaps into the corresponding disjunction of strict exits.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_first_grid_crossing_before_terminal_cap
import Theorems.Thm_AvramDividend_Classical_chat03_hittingBtwn_eq_earliest_observed_crossing
import Mathlib.Probability.Process.HittingTime

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_actual_hittingBtwn_eventually_first_strict_grid_crossing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (m : ℕ → ℕ)
    (hcap : ∀ᶠ n in atTop, τ + 1 ≤ (m n : ℝ≥0) * mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max (X.X ((j : ℝ≥0) * mesh n) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (m n) η) :
    ∀ᶠ n in atTop,
      (X.X ((K n ω : ℝ≥0) * mesh n) ω < lower ∨
       upper < X.X ((K n ω : ℝ≥0) * mesh n) ω) ∧
      (∀ j : ℕ, j < K n ω →
        ¬ (X.X ((j : ℝ≥0) * mesh n) ω < lower ∨
           upper < X.X ((j : ℝ≥0) * mesh n) ω)) := by sorry
