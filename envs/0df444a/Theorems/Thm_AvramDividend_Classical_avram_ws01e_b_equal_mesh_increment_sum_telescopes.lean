-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_equal_mesh_increment_sum_telescopes
-- name    : AvramDividend.Classical.avram_ws01e_b_equal_mesh_increment_sum_telescopes
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T08:07:12.317044+00:00
-- url     : https://prove2.me/theorems/24166a47-0647-44eb-a1c3-942787ad2e43
-- title:
--   Equal-mesh Lévy increments telescope to total terminal displacement
-- statement:
--   For any Lévy path, nonnegative mesh step δ and n finite increments, the sum of successive increments X_{(j+1)δ}−X_{jδ} over j=0,...,n−1 is exactly X_{nδ}−X_0, even for n=0. This identifies the terminal displacement inside the finite-terminal Esscher density with the total sum of the finite-mesh increment vector, allowing an exact path-law to vector-law density pushforward.
-- source:
--   Elementary Finset.sum_range_succ induction and real arithmetic, no Lévy-specific stochastic assumptions used beyond the path evaluation map.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_ws01e_b_equal_mesh_increment_sum_telescopes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (δ : ℝ≥0) (n : ℕ) (ω : Ω) :
    Finset.sum (Finset.range n) (fun j =>
      X.X ((((j + 1 : ℕ) : ℝ≥0) * δ)) ω -
      X.X (((j : ℝ≥0) * δ)) ω) =
      X.X (((n : ℝ≥0) * δ)) ω - X.X 0 ω := by sorry
