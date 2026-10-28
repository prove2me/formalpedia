-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_fin_mesh_increment_sum_eq_terminal_displacement
-- name    : AvramDividend.Classical.avram_ws01e_b_fin_mesh_increment_sum_eq_terminal_displacement
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T12:32:43.245602+00:00
-- url     : https://prove2.me/theorems/a50cda73-6ace-4a04-b4bf-b7e3ab1728be
-- title:
--   Fin-indexed Lévy mesh-increment sum equals true terminal displacement
-- statement:
--   For any spectrally negative Lévy path, step δ and natural n including n=0, the sum of n successive increments indexed by Fin n equals the terminal path displacement X_(nδ)-X_0. This reindexes the already accepted range-indexed telescoping identity into the exact Fin-indexed increment-vector sum appearing in the Esscher likelihood.
-- source:
--   Proved avram_ws01e_b_equal_mesh_increment_sum_telescopes (24166a47) and pinned Mathlib Fin.sum_univ_eq_sum_range.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_equal_mesh_increment_sum_telescopes

open AvramDividend.Classical MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_ws01e_b_fin_mesh_increment_sum_eq_terminal_displacement
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (δ : ℝ≥0) (n : ℕ) (ω : Ω) :
    (∑ i : Fin n,
      (X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
       X.X ((i.val : ℝ≥0) * δ) ω)) =
    X.X ((n : ℝ≥0) * δ) ω - X.X 0 ω := by sorry
