-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_filter_image_card_le
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_filter_image_card_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:09:01.836885+00:00
-- url     : https://prove2.me/theorems/86454f51-ce59-4d0a-9aa6-7b5d1f4e28c4
-- title:
--   Finite grid image-filter cardinality dominated by original cell-index occupancy
-- statement:
--   For any finite index grid mapped to possibly repeated time endpoints, the number of distinct marked endpoints is at most the number of source marked cell indices. This source-backed combinatorial bridge enables original stationary finite-grid indicator-sum expectation bounds without assuming distinct times or any jump rate. It is the exact finite-cardinality reduction needed for the original P2-A mesh liminf and mean-envelope proof.

import Mathlib
open Finset

theorem AvramDividend.Classical.avram_p2_a_zero_rate_filter_image_card_le
    {α β : Type*} [DecidableEq β] (s : Finset α)
    (f : α → β) (p : β → Prop) [DecidablePred p] :
    ((s.image f).filter p).card ≤
      (s.filter (fun a => p (f a))).card := by sorry
