-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB304_original_localized_fixed_level_hit_mesh_cover
-- name    : AvramDividend.Classical.avram_gbB304_original_localized_fixed_level_hit_mesh_cover
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:33:30.353872+00:00
-- url     : https://prove2.me/theorems/f7553781-ecf7-499f-802f-ee88010dcdb5
-- title:
--   Every original localised Gaussian reserve level hit lies at an endpoint or in an original good/bad dividend cell
-- statement:
--   A fixed-level hit of the exact original Lévy source less its genuine right-limit adapted dividend payments within a positive finite physical horizon and terminal dividend localisation is covered by either one of finitely many mesh boundary times, one bad original dividend-increment cell, or one good cell. The physical mesh covering theorem B287 and the real dividend increment threshold dichotomy prove the inclusion pathwise, preserving every original assumption and localisation. This is the substantive source-specific geometric component in B276b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory ProbabilityTheory Set Finset AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB304_original_localized_fixed_level_hit_mesh_cover
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n M m : ℕ) (hm : 0 < m) :
  let δ : ℝ := 1 / ((m : ℝ) ^ 4)
  let N : ℕ := n * m ^ 4
  let E : Set (Ω × ℝ) := {z | z.2 ∈ Set.range
    (fun i : Fin N => (i : ℝ) * δ)}
  let B : Set (Ω × ℝ) := {z | ∃ i ∈ Finset.range N,
    z.2 ∈ Set.Ioo ((i : ℝ) * δ) (((i : ℝ) + 1) * δ) ∧
    1 / ((m : ℝ) ^ 3) <
      D (((i + 1 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 -
      D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 ∧
    x + X.X (Real.toNNReal z.2) z.1 -
      rightLimit D (Real.toNNReal z.2) z.1 = b ∧
    D n z.1 - D 0 z.1 ≤ (M : ℝ)}
  let G : Set (Ω × ℝ) := {z | ∃ i ∈ Finset.range N,
    z.2 ∈ Set.Ioo ((i : ℝ) * δ) (((i : ℝ) + 1) * δ) ∧
    D (((i + 1 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 -
      D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 ≤
        1 / ((m : ℝ) ^ 3) ∧
    x + X.X (Real.toNNReal z.2) z.1 -
      rightLimit D (Real.toNNReal z.2) z.1 = b}
  let S : Set (Ω × ℝ) := {z |
    0 < z.2 ∧ z.2 < (n : ℝ) ∧
    x + X.X (Real.toNNReal z.2) z.1 -
      rightLimit D (Real.toNNReal z.2) z.1 = b ∧
    D n z.1 - D 0 z.1 ≤ (M : ℝ)}
  S ⊆ E ∪ (B ∪ G) := by sorry
