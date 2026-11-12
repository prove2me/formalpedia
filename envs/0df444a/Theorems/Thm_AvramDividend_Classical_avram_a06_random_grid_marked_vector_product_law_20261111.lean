-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_random_grid_marked_vector_product_law_20261111
-- name    : AvramDividend.Classical.avram_a06_random_grid_marked_vector_product_law_20261111
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:24:45.068519+00:00
-- url     : https://prove2.me/theorems/8baaa263-322f-424d-adf6-9d1c9c21626a
-- title:
--   Exact A06 random-grid marked-vector law is the image of independent count and mark marginals
-- statement:
--   The full vector of randomly indexed marked interval sums has the exact law obtained by applying the deterministic grid transformation to independent count and mark streams. The measurable transformation is already proved, as is the generic independent-image-law identity. This is the measure-level mixing bridge in A06.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_joint_count_mark_grid_transform_measurable_20261111
import Theorems.Thm_AvramDividend_Classical_avram_a06_independent_pair_measurable_image_law_20261111
open MeasureTheory ProbabilityTheory Finset
noncomputable section

theorem AvramDividend.Classical.avram_a06_random_grid_marked_vector_product_law_20261111
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (N : Ω → Fin (n + 1) → ℕ) (Y : Ω → ℕ → ℝ)
    (hN : Measurable N) (hY : Measurable Y)
    (hSeparate : IndepFun N Y P) :
    Measure.map (fun ω => WithLp.toLp 2 (fun i : Fin n =>
      ∑ j ∈ Finset.Ico (N ω i.castSucc) (N ω i.succ), Y ω j)) P =
    Measure.map (fun p : (Fin (n + 1) → ℕ) × (ℕ → ℝ) =>
      WithLp.toLp 2 (fun i : Fin n =>
        ∑ j ∈ Finset.Ico (p.1 i.castSucc) (p.1 i.succ), p.2 j))
      ((Measure.map N P).prod (Measure.map Y P)) := by sorry
