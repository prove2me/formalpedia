-- Prove2me | Theorems.Thm_Erdos146_booleanWordOnes_card_equiv
-- name    : Erdos146.booleanWordOnes_card_equiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:44:29.842999+00:00
-- url     : https://prove2.me/theorems/32f8f3db-354b-4662-bb47-984396b3cc84
-- title:
--   Counting Boolean words of a given weight
-- statement:
--   The words of $\{0,1\}^m$ of a prescribed weight are in bijection with the subsets of that size, so their number is the corresponding binomial coefficient.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L12534-L12556

import Definitions.Def_erdos146_core2
import Mathlib.Data.Finset.Card

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.booleanWordOnes_card_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (equivalence : ι ≃ κ)
    (word : κ → Bool) :
    (booleanWordOnes (fun index : ι => word (equivalence index))).card =
      (booleanWordOnes word).card := by sorry
