-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB294_prod_vs_swapped_product_one_sided
-- name    : AvramDividend.Classical.avram_gbB294_prod_vs_swapped_product_one_sided
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T11:12:40.121205+00:00
-- url     : https://prove2.me/theorems/41946df8-b438-42fa-ad95-bba17568c314
-- title:
--   One-sided general product measure comparison under coordinate swap
-- statement:
--   Show that the original product measure is dominated by the swapped product measure, without assuming sigma-finiteness of P. This precise general-measure comparison is sufficient together with prod_apply_le to deduce the original fibre envelope.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB294_prod_vs_swapped_product_one_sided
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : Set (Ω × ℝ)) (hS : MeasurableSet S) :
    (P.prod volume) S ≤
      (volume.prod P) (Prod.swap ⁻¹' S) := by sorry
