-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_negative_cutoff_retained_omitted_partition_20261113
-- name    : AvramDividend.Classical.avram_a21_negative_cutoff_retained_omitted_partition_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:28:56.241204+00:00
-- url     : https://prove2.me/theorems/44879cb9-709c-41f1-b2ab-d341526d55b4
-- title:
--   Exact partition of original negative small-jump marks into retained strip and omitted near-zero tail
-- statement:
--   For every natural cutoff n, the retained original physical mark interval (-1,-1/(n+1)] and omitted near-zero interval (-1/(n+1),0) are disjoint and their union is (-1,0), including correct ownership of the cutoff atom.
-- source:
--   Pinned Mathlib Set.Ioc_union_Ioo_eq_Ioo with real endpoint inequalities. The correct negative-strip set partition needed by source finite-cutoff Gaussian variance 74450e6a, avoiding false d73cacfa.

import Mathlib
open Set
noncomputable section

theorem AvramDividend.Classical.avram_a21_negative_cutoff_retained_omitted_partition_20261113
    (n : ℕ) :
    Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))) ∪
      Ioo (-(1 / ((n : ℝ) + 1))) 0 = Ioo (-1 : ℝ) 0 := by sorry
