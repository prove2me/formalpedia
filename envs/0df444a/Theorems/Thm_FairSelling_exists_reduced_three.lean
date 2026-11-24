-- Prove2me | Theorems.Thm_FairSelling_exists_reduced_three
-- name    : FairSelling.exists_reduced_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:25:22.670573+00:00
-- url     : https://prove2.me/theorems/db39dbc9-1079-439c-9390-371f4fc62369
-- title:
--   Fair Selling: exists reduced three
-- statement:
--   **Lemma 5, `n = 3`.**  Every valuation has an MMS configuration into three parts that
--   force-sells at most two goods: three pairwise-disjoint kept bundles `A i` and a force-sold set `s`
--   with `s.card ≤ 2`, whose proceeds are split by `q`, covering all goods, with every part worth at
--   least `MMS`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MMSPartition.lean#L110-L114
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MMSPartition.lean#L110-L114

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.exists_reduced_three (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g) :
    ∃ (A : Fin 3 → Finset G) (s : Finset G) (q : Fin 3 → ℝ),
      ConfigN 3 w p (MMS 3 w p) A s q ∧ s.card ≤ 2 := by sorry
