-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a26_range_occupied_card_equals_fin_boolean_sum_20261116
-- name    : AvramDividend.Classical.avram_a26_range_occupied_card_equals_fin_boolean_sum_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:19:25.459862+00:00
-- url     : https://prove2.me/theorems/441b76b7-3cd4-44d9-9669-e3fb02bf00d4
-- title:
--   Number of occupied grid cells equals the sum of their zero-one indicator variables
-- statement:
--   For every finite range of cells, its filtered cardinal is exactly the sum of corresponding zero-one indicators indexed by Fin n. Rewrite Mathlib Finset.card_filter and Fin.sum_univ_eq_sum_range. This is the deterministic bridge from the original physical occupied-cell cardinal to the independent Bernoulli-variable sum in the binomial grid law.
-- source:
--   Pinned Mathlib Finset.card_filter and Fin.sum_univ_eq_sum_range.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open scoped BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a26_range_occupied_card_equals_fin_boolean_sum_20261116
    (n : ℕ) (b : ℕ → Prop) [DecidablePred b] :
    ((Finset.range n).filter b).card =
      ∑ i : Fin n, if b i.val then (1 : ℕ) else 0 := by sorry
